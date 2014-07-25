#include <sstream>
#include <iostream>
#include <vector>
#include <cmath>
#include <cstdlib>
#include <algorithm>
#include <ctime>
#include <cstring>
#include <tuple>
#include <thread>
#include <atomic>
#include <cstdint>
using namespace std;

/*
left = -1, 0
right = +1, 0
up = 0, +1
down = 0, -1

input is y down, x right

*/

const double SmallTimeout = 0.5;
const double LargeTimeout = 2.3;

const int WorkerThreads = 8;
const int PermLog = 6;
const int MaxN = 16;
const int MaxTreeNodes = 1 << 17;
const int IterPerQuantum = 1 << 7;
const int MaxProbChildren = 1 << 7;
const int MaxTreeDepth = 3;

enum Direction
{
	Up = 0, Down, Right, Left
};

/* Yep, this is the radical solution to memory allocation performance. Let's pray everything will be okay. */
class BumpIntAllocator
{
public:
	BumpIntAllocator()
	{
		newShard();
	}

	~BumpIntAllocator()
	{
		for (auto it = storages.begin(); it != storages.end(); ++it)
			delete[] *it;
	}

	int* alloc(int n)
	{
		while (true)
		{
			int ints_before = ints_left.fetch_sub(n);
			if (ints_before >= 0 && ints_before - n < 0)
			{
				newShard();
				continue;
			}

			if (ints_before < 0)
			{
				ints_left.fetch_add(n);
				continue;
			}

			return head.fetch_add(n);
		}

	}

	int shards()
	{
		return storages.size();
	} 

private:
	atomic<int*> head;
	atomic<int> ints_left;
	vector<int*> storages;

	static const int shardSize = 1 << 18;

	void newShard()
	{
		int *shard = new int[shardSize];
		storages.push_back(shard);
		head.store(shard);
		ints_left.store(shardSize);
	}

} bumpIntAllocator;

class Rng
{
public:
	Rng(int seed) : x(seed * 5683), y(seed * 4801), z(seed * 4297), w(seed * 6971)
	{
	}

	uint32_t get()
	{
		uint32_t t;

		t = x ^ (x << 11);
		x = y; y = z; z = w;
		return w = w ^ (w >> 19) ^ t ^ (t >> 8);
	}

private:
	uint32_t x, y, z, w;
};

#pragma pack(1)
class Board
{
public:
	Board()
		: n(0), data(nullptr)
	{
	}

	Board(int n)
		: n(n)
	{
		data = bumpIntAllocator.alloc(3*n);
		for (int i = 0; i < 2*n; ++i)
			data[i] = 0;
		for (int i = 0; i < n; ++i)
			data[i+2*n] = n;
	}

	Board(const Board & other)
		: n(other.n)
	{
		data = bumpIntAllocator.alloc(3 * n);
		if (n)
			memcpy(data, other.data, sizeof(int) * 3 * n);
	}

	Board(Board && other)
		: n(other.n)
	{
		data = other.data;
		other.data = NULL;
	}

	Board& operator=(Board & other)
	{
		if (other.n > n || data == nullptr)
			data = bumpIntAllocator.alloc(3 * other.n);

		if (n = other.n)
			memcpy(data, other.data, sizeof(int) * 3 * n);

		return *this;
	}

	Board& operator=(Board && other)
	{
		n = other.n;
		data = other.data;
		other.data = nullptr;
		return *this;
	}

	bool operator== (const Board & other) const
	{
		if (data != nullptr && other.data != nullptr)
			for (int i = 0; i < 3*n; ++i)
				if (data[i] != other.data[i])
					return false;

		return (data == nullptr) == (other.data == nullptr);
	}

	void setField(int x, int y, Direction dir, int pts)
	{
		int *direction = data;
		int *points = data + n;

		direction[x] &= ~(3 << (2*y));
		direction[x] |= ((int) dir) << (2*y);

		points[x] &= ~(3 << (2*y));
		points[x] |= (pts-1) << (2*y);
	}

	pair<int, int> performMove(int cum_score, int x, int y)
	{
		int *direction = data;
		int *points = data + n;
		int *occupied = data + 2*n;

		int total = 0;
		int length = 0;
		int ywas[MaxN], xwas[MaxN];

		memset(ywas, 0, sizeof(ywas));
		memset(xwas, 0, sizeof(xwas));
		
		for (;;)
		{
			total += ((points[x] >> (2*y)) & 3);

			length++;
			total++; /* points are off by one */
						
			Direction cdir = (Direction) ((direction[x] >> (2*y)) & 3);
			bool in_bounds = true;

			int ymask = (1 << y);
			int xmask = (1 << x);

			int ywasc = (ywas[x] |= ymask);
			int xwasc = (xwas[y] |= xmask);

			if (cdir == Up)
			{				
				do { ymask <<= 1; ++y; } while ((in_bounds = (y < n)) && (ywasc & ymask));

			} else if (cdir == Down)
			{
				do { ymask >>= 1; --y; } while ((in_bounds = (y >= 0)) && (ywasc & ymask));

			} else if (cdir == Right)
			{
				do { xmask <<= 1; ++x; } while ((in_bounds = (x < n)) && (xwasc & xmask));

			} else if (cdir == Left)
			{
				do { xmask >>= 1; --x; } while ((in_bounds = (x >= 0)) && (xwasc & xmask));

			}

			if (!in_bounds)
				break;

		}

		/* extra points */
		int full_mask = (1 << n) - 1;
		for (int i = 0; i < n; ++i)
		{
			if (xwas[i] == full_mask)
				total += 10 * n;

			if (ywas[i] == full_mask)
				total += 10 * n;
		}

		/* extra moves threshold */
		int threshold = (cum_score + total) / (5 * n * n) + n - 1;

		/* slide down */
		for (int i = 0; i < n; ++i)
		{
			int np = 0, nd = 0, nc = 0;
			for (int j = n-1; j >= 0; --j)
				if ((ywas[i] & (1 << j)) == 0)
				{
					nc++;
					np <<= 2; np |= ((points[i] >> (2*j)) & 3);
					nd <<= 2; nd |= ((direction[i] >> (2*j)) & 3);
				}

			points[i] = np;
			direction[i] = nd;
			occupied[i] = nc;
		}
		
		return make_pair(total, max(length - threshold, 0));
	}

	void fillRandom(Rng & rng)
	{
		int totalMask = (1 << (2*n)) - 1;
		int *direction = data;
		int *points = data + n;
		int *occupied = data + 2*n;

		for (int i = 0; i < n; ++i)
		{
			for (int j = occupied[i]; j < n; j += 4)
			{
				points[i] |= (85 << (2*j)); /* 1 stands for 2.0 = E[random color], 85 = 01010101b */
				direction[i] |= (rng.get() << (2*j));
			}

			occupied[i] = n;
			points[i] &= totalMask;
			direction[i] &= totalMask;
		}

	}

	int get_n() const
	{
		return n;
	}

private:
	int n;
	int *data;
};
#pragma pack()

atomic<int> totalPlayoutCount = 0;

class Mcts
{
public:
	Mcts(Board & board, int moves, int score)
		: node_count(1)
	{
		nodes = new TreeNode[MaxTreeNodes];
		new (nodes) TreeNode(moves, score, board);

		Rng permRng(1307);
		int board_size = board.get_n() * board.get_n();
		for (int i = 0; i < (1 << PermLog); ++i)
		{
			permutations.emplace_back(board_size);
			for (int j = 0; j < board_size; ++j)
				permutations.back()[j] = j;

			for (int j = 0; j < board_size-1; ++j)
			{
				int k = j + permRng.get() % (board_size - j);
				swap(permutations.back()[j], permutations.back()[k]);
			}
		}
	}

	~Mcts()
	{
		delete[] nodes;
	}

	void run(Rng & rng, double Timeout)
	{
		clock_t startTime = clock();

		do 
		{
			for (int iter = 0; iter < IterPerQuantum; ++iter)
				mctsIteration(rng);

		} while (clock() - startTime < Timeout * CLOCKS_PER_SEC);

	}

	pair<int, int> solution()
	{
		double bestExpectance = -1.;
		int bestX = 0;
		int bestY = 0;
		
		for (TreeNode *cur = nodes->head.load(memory_order_relaxed); cur != nullptr; cur = cur->next)
		{
			if (cur->n_visits == 0)
				continue;

			double curExpectance = cur->expectance();
			if (curExpectance > bestExpectance)
			{
				bestExpectance = curExpectance;
				bestX = cur->x;
				bestY = cur->y;
			}

		}

		return make_pair(bestX, bestY);
	}

private:

	class TreeNode
	{	
	public:
		TreeNode()
		{
		}

		TreeNode(int moves, int score, Board & board, int x = 0, int y = 0)
			: n_children(0), n_visits(0), sum(0), head(nullptr), next(nullptr), moves(moves), score(score), board(board), x(x), y(y)
		{
		}

		TreeNode(int moves, int score, Board && board, int x = 0, int y = 0)
			: n_children(0), n_visits(0), sum(0), head(nullptr), next(nullptr), moves(moves), score(score), board(board), x(x), y(y)
		{
		}

		int moves;
		int score;
		Board board;

		int x, y;

		atomic<int> n_children;
		atomic<int> n_visits;
		atomic<long long> sum;

		atomic<TreeNode*> head;
		TreeNode* next;

		inline void visit(int value)
		{
			n_visits += 1;
			sum += (long long) value;
		}

		inline double expectance()
		{
			return ((double) sum) / n_visits;
		}

		inline void append(TreeNode * child)
		{
			TreeNode *old_head = head.load(memory_order_relaxed);
			do 
			{
				child->next = old_head;

			} while (!head.compare_exchange_weak(old_head, child, memory_order_release, memory_order_relaxed));
		}

		inline bool appendStrict(TreeNode * child, TreeNode * orig_head)
		{
			TreeNode *old_head = head.load(memory_order_relaxed);
			do 
			{
				if (orig_head != old_head)
					return false;

				child->next = old_head;

			} while (!head.compare_exchange_weak(old_head, child, memory_order_release, memory_order_relaxed));

			return true;
		}

	};

	void mctsIteration(Rng & rng)
	{
		decisionNode(rng, nodes, 0, false);
	}

	int decisionNode(Rng & rng, TreeNode * node, int level, bool just)
	{
		int n = node->board.get_n();

		bool will_add = true;
		int node_countBefore = -1;
		int n_childrenBefore = -1;
		
		if (!just)
		{
			n_childrenBefore = node->n_children.fetch_add(1);
			if (n_childrenBefore >= n*n)
			{
				will_add = false;
				node->n_children.fetch_sub(1);
			} else
			{
				node_countBefore = node_count.fetch_add(1);
				if (node_countBefore >= MaxTreeNodes)
				{
					will_add  = false;
					node->n_children.fetch_sub(1);
					node_count.fetch_sub(1);
				}
			}

		} else
		{
			will_add = false;
		}

		if (will_add)
		{
			int perm_idx = (node - nodes) & ((1 << PermLog) - 1);
			int node_idx = permutations[perm_idx][n_childrenBefore];

			int cy = node_idx / n;
			int cx = node_idx - cy * n;

			Board newBoard(node->board);
			pair<int, int> moveResult = newBoard.performMove(node->score, cx, cy);

			TreeNode * newNode = new (nodes + node_countBefore) TreeNode(
				node->moves + moveResult.second - 1,
				node->score + moveResult.first,
				move(newBoard),
				cx, cy);

			node->append(newNode);

			int finalScore = chanceNode(rng, newNode, level, true);
			node->visit(finalScore);
			return finalScore;

		} else
		{
			/* UCT+ (?) */
			double bestUct = -1.;
			TreeNode *bestNode = nullptr;

			double scaling = 75. * (node->moves + 1);

			for (TreeNode *cur = node->head; cur != nullptr; cur = cur->next)
			{
				if (cur->n_visits == 0)
					continue;

				double curUct = cur->expectance() + scaling * sqrt(log((double)(node->n_visits))/cur->n_visits);
				if (curUct > bestUct)
				{
					bestUct = curUct;
					bestNode = cur;
				}
			}

			int finalScore = bestNode == nullptr ? randomPlayout(rng, node->board, node->score, node->moves) : chanceNode(rng, bestNode, level, false);
			node->visit(finalScore);
			return finalScore;			
		}

	}

	int chanceNode(Rng & rng, TreeNode * node, int level, bool just)
	{
		if (node->moves <= 0)
		{
			int finalScore = node->score;
			node->visit(finalScore);
			return finalScore;
		}

		if (just)
		{
			int finalScore = randomPlayout(rng, node->board, node->score, node->moves);
			node->visit(finalScore);
			return finalScore;
		}

		Board iboard(node->board);
		iboard.fillRandom(rng);

		TreeNode *foundNode = nullptr;
		bool newJust = false;

		TreeNode *searchBoundary = nullptr;
		do {
			TreeNode *headAtStart = node->head.load(memory_order_relaxed);
			for (TreeNode *cur = headAtStart; cur != searchBoundary; cur = cur->next)
				if (cur->board == iboard)
				{
					foundNode = cur;
					break;
				}

			if (foundNode != nullptr)
				break;

			if (node->head.load(memory_order_relaxed) != headAtStart)
			{
				searchBoundary = headAtStart;
				continue;
			}

			if (level >= MaxTreeDepth)
				break;

			int n_childrenBefore = node->n_children.fetch_add(1);
			if (n_childrenBefore >= MaxProbChildren)
			{
				node->n_children.fetch_sub(1);
				break;
			}

			int node_countBefore = node_count.fetch_add(1);
			if (node_countBefore >= MaxTreeNodes)
			{
				node_count.fetch_sub(1);
				node->n_children.fetch_sub(1);
				break;
			}

			TreeNode *newNode = new (nodes + node_countBefore) TreeNode(node->moves, node->score, iboard);
			if (!node->appendStrict(newNode, headAtStart))
			{
				/* stray node - deal with it B) */
				searchBoundary = headAtStart;
				node->n_children.fetch_sub(1);
				continue;
			}

			foundNode = newNode;
			newJust = true;

		} while (0);

		int finalScore = foundNode == nullptr ? randomPlayout(rng, iboard, node->score, node->moves) : decisionNode(rng, foundNode, level + 1, newJust);
		node->visit(finalScore);
		return finalScore;
	}

	int randomPlayout(Rng & rng, Board & board, int score, int moves)
	{
		totalPlayoutCount.fetch_add(1);

		Board curBoard(board);
		Board bestBoard, tempBoard;
		
		while (moves > 0)
		{
			curBoard.fillRandom(rng);

			vector<int> & cur_permutation = permutations[rng.get() & ((1 << PermLog) - 1)];
	
			int bestMetric = 0;
			int bestScoreDelta = 0;
			int bestExtraMoves = 0;

			int halfMoves = curBoard.get_n() * curBoard.get_n() / 2;

			for (int idx = 0; idx < halfMoves; ++idx)
			{
				int locidx = cur_permutation[idx];
				int cx = locidx / curBoard.get_n();
				int cy = locidx - curBoard.get_n() * cx;

				tempBoard = curBoard;
				pair<int, int> moveResult = tempBoard.performMove(score, cx, cy);

				int metric = moveResult.first + 30 * moveResult.second; /* empiric to the max */
				if (metric > bestMetric)
				{
					bestBoard = move(tempBoard);
					bestMetric = metric;
					bestScoreDelta = moveResult.first;
					bestExtraMoves = moveResult.second;
				}
			}

			curBoard = move(bestBoard); 
			score += bestScoreDelta;
			moves += bestExtraMoves - 1;
		}

		return score;
	}

	atomic<int> node_count;
	TreeNode * nodes;

	vector<vector<int>> permutations;
};

pair<int, int> bestMove(Board & b, int score, int moves)
{
	Mcts mcts(b, moves, score);

	Rng timeoutRng(score + moves * 997);
	double Timeout = ((timeoutRng.get() & 3) == 0 ? SmallTimeout : LargeTimeout);

	vector<thread> workers;
	for (int i = 0; i < WorkerThreads; ++i)
		workers.push_back(thread([&mcts, i, Timeout](){ Rng rng(6719 * i + 4271); mcts.run(rng, Timeout); }));
		
	for (auto it = workers.begin(); it != workers.end(); ++it)
		it->join();

	return mcts.solution();
}

int main(int argc, char *argv[])
{
	if (argc != 6)
		return -1;

	int n = atoi(argv[1]);
	int score = atoi(argv[2]);
	int moves = atoi(argv[3]);

	char *dirs = argv[4];
	char *pnts = argv[5];

	Board b(n);
	for (int y = n-1; y >= 0; --y)
		for (int x = 0; x < n; ++x)
		{
			Direction cdir = Up;
			if (*dirs == 'u') cdir = Up;
			if (*dirs == 'd') cdir = Down;
			if (*dirs == 'l') cdir = Left;
			if (*dirs == 'r') cdir = Right;
			
			int cpoints = (int) *pnts - '0';
			++dirs; ++pnts;
			b.setField(x, y, cdir, cpoints);
		}

	pair<int, int> solution = bestMove(b, score, moves);

	cout << "{\"x\":" << solution.first << ", \"y\":" << n-1-solution.second << "}" << endl;	

	return 0;
}
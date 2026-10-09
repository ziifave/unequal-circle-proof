#include <algorithm>
#include <array>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

using namespace std;

constexpr int N = 15;
constexpr int TWO_PI = 17600;
constexpr int Q[12][12] = {
    {8700,8700,8700,6746,6142,5883,4896,4047,0,0,0,0},
    {8700,8700,5105,4784,4585,4488,4077,3690,3228,2344,1738,0},
    {8700,5105,4086,3923,3818,3767,3541,3321,3105,2889,2720,0},
    {6746,4784,3923,3780,3688,3642,3442,3245,3051,2856,2744,0},
    {6142,4585,3818,3688,3603,3561,3376,3194,3014,2832,2727,656},
    {5883,4488,3767,3642,3561,3521,3344,3169,2994,2819,2717,868},
    {4896,4077,3541,3442,3376,3344,3198,3051,2904,2754,2668,950},
    {4047,3690,3321,3245,3194,3169,3051,2932,2809,2682,2609,1214},
    {0,3228,3105,3051,3014,2994,2904,2809,2709,2604,2541,1383},
    {0,2344,2889,2856,2832,2819,2754,2682,2604,2518,2467,1499},
    {0,1738,2720,2744,2727,2717,2668,2609,2541,2467,2422,1579},
    {0,0,0,0,656,868,950,1214,1383,1499,1579,1612},
};

struct Edge { int u, v, w; char kind; };
struct State {
  array<int, N> label{};
  vector<int> inner;
  int k = 0;
  long long nodes = 0;
  long long leaves = 0;
};

char digit(int n) { return n < 10 ? char('0' + n) : char('A' + n - 10); }

vector<Edge> graph(const State& s) {
  vector<Edge> edges;
  for (int i = 0; i < N - 1; ++i) edges.push_back({i + 1, i, 0, 'O'});
  for (int i = 0; i < N; ++i) for (int j = i + 1; j < N; ++j) {
    const int q = (s.label[i] >= 12 || s.label[j] >= 12)
        ? 0 : Q[s.label[i]][s.label[j]];
    edges.push_back({j, i, -q, 'L'});
    edges.push_back({i, j, TWO_PI - q, 'U'});
  }
  return edges;
}

bool negativeCycle(const State& s, vector<Edge>& cycle) {
  const auto edges = graph(s);
  array<int, N> distance{};
  array<int, N> predecessor;
  predecessor.fill(-1);
  int changed = -1;
  for (int pass = 0; pass < N; ++pass) {
    changed = -1;
    for (int e = 0; e < static_cast<int>(edges.size()); ++e) {
      const auto& edge = edges[e];
      if (distance[edge.v] > distance[edge.u] + edge.w) {
        distance[edge.v] = distance[edge.u] + edge.w;
        predecessor[edge.v] = e;
        changed = edge.v;
      }
    }
    if (changed < 0) return false;
  }
  int onCycle = changed;
  for (int i = 0; i < N; ++i) {
    const int edge = predecessor[onCycle];
    if (edge < 0) return false;
    onCycle = edges[edge].u;
  }
  vector<Edge> backwards;
  int vertex = onCycle;
  do {
    const int edge = predecessor[vertex];
    if (edge < 0 || backwards.size() >= N) return false;
    backwards.push_back(edges[edge]);
    vertex = edges[edge].u;
  } while (vertex != onCycle);
  reverse(backwards.begin(), backwards.end());
  int weight = 0;
  for (const auto& edge : backwards) weight += edge.w;
  if (backwards.size() < 2 || weight >= 0) return false;
  cycle = std::move(backwards);
  return true;
}

bool originConflict(const State& s) {
  for (int p : s.inner) if (s.label[p] == 13)
    for (int q : s.inner) if (q != p && s.label[q] < 8) return true;
  return false;
}

bool rankConflict(int depth, int high, int high2, const State& s) {
  const int remaining = s.k - depth;
  return high + remaining < s.k - 4 ||
      high2 + remaining < max(0, s.k - 5);
}

bool mixedConflict(int small, const State& s) {
  if (small != 1) return false;
  bool zero = false, oneAndHalf = false;
  for (int i = 0; i < N; ++i) {
    zero |= s.label[i] == 0 || s.label[i] == 13;
    oneAndHalf |= s.label[i] == 2;
  }
  return zero && oneAndHalf;
}

void emitCycle(const vector<Edge>& cycle, string& out) {
  out.push_back('C');
  out.push_back(digit(static_cast<int>(cycle.size())));
  for (const auto& edge : cycle) {
    out.push_back(digit(edge.u));
    out.push_back(digit(edge.v));
    out.push_back(edge.kind);
  }
}

bool rec(int depth, int small, int high, int high2, State& s, string& out) {
  ++s.nodes;
  if (originConflict(s)) { out.push_back('O'); ++s.leaves; return true; }
  if (small > 1) { out.push_back('S'); ++s.leaves; return true; }
  if (rankConflict(depth, high, high2, s)) {
    out.push_back('R'); ++s.leaves; return true;
  }
  if (mixedConflict(small, s)) { out.push_back('M'); ++s.leaves; return true; }

  if (depth >= 3) {
    vector<Edge> cycle;
    if (negativeCycle(s, cycle)) {
      emitCycle(cycle, out);
      ++s.leaves;
      return true;
    }
  }
  if (depth == s.k) return false;

  out.push_back('B');
  const int p = s.inner[depth];
  for (int t : {0, 13, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}) {
    s.label[p] = t;
    const int nextSmall = small + ((t <= 1 || t == 13) ? 1 : 0);
    const int nextHigh = high + (t >= 5 ? 1 : 0);
    const int nextHigh2 = high2 + (t >= 8 ? 1 : 0);
    if (!rec(depth + 1, nextSmall, nextHigh, nextHigh2, s, out)) return false;
  }
  s.label[p] = 12;
  return true;
}

int main(int argc, char** argv) {
  if (argc != 2 || string(argv[1]).size() != N) {
    cerr << "usage: export_stage4_certificate <15-bit-pattern>\n";
    return 2;
  }
  const string pattern = argv[1];
  State state;
  state.label.fill(11);
  for (int i = 0; i < N; ++i) {
    if (pattern[i] == '1') {
      state.inner.push_back(i);
      state.label[i] = 12;
    } else if (pattern[i] != '0') {
      cerr << "pattern must contain only 0 and 1\n";
      return 2;
    }
  }
  state.k = static_cast<int>(state.inner.size());
  string certificate;
  if (!rec(0, 0, 0, 0, state, certificate)) {
    cerr << "pattern has a surviving assignment; no closed certificate generated\n";
    return 1;
  }
  const string path = "stage4_certificate_" + pattern + ".txt";
  ofstream out(path);
  if (!out) return 3;
  out << pattern << '\t' << certificate << '\n';
  cerr << "pattern=" << pattern << " nodes=" << state.nodes
       << " leaves=" << state.leaves << " bytes=" << certificate.size() << '\n';
}

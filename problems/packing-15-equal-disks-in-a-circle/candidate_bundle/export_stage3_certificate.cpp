#include <array>
#include <algorithm>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

using namespace std;

constexpr int N = 15;
constexpr int TWO_PI = 17600;
constexpr int Q[8][8] = {
    {8700, 8700, 8700, 6746, 6142, 4047, 0, 0},
    {8700, 8700, 5105, 4784, 4585, 3690, 1738, 0},
    {8700, 5105, 4086, 3923, 3818, 3321, 2720, 0},
    {6746, 4784, 3923, 3780, 3688, 3245, 2744, 0},
    {6142, 4585, 3818, 3688, 3603, 3194, 2727, 656},
    {4047, 3690, 3321, 3245, 3194, 2932, 2609, 868},
    {0, 1738, 2720, 2744, 2727, 2609, 2422, 1383},
    {0, 0, 0, 0, 656, 868, 1383, 1612},
};

struct Edge { int u, v, w; char kind; };
struct State {
  array<int, N> label{};
  vector<int> inner;
  int k = 0;
  long long nodes = 0;
  long long leaves = 0;
};

char digit(int n) {
  return n < 10 ? char('0' + n) : char('A' + n - 10);
}

vector<Edge> graph(const State& s) {
  vector<Edge> edges;
  for (int i = 0; i < N - 1; ++i) edges.push_back({i + 1, i, 0, 'O'});
  for (int i = 0; i < N; ++i) for (int j = i + 1; j < N; ++j) {
    int q = (s.label[i] >= 8 || s.label[j] >= 8) ? 0 : Q[s.label[i]][s.label[j]];
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
    for (int e = 0; e < (int)edges.size(); ++e) {
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
    int edge = predecessor[onCycle];
    if (edge < 0) return false;
    onCycle = edges[edge].u;
  }
  vector<Edge> backwards;
  int vertex = onCycle;
  do {
    int edge = predecessor[vertex];
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
  for (int p : s.inner) if (s.label[p] == 9)
    for (int q : s.inner) if (q != p && s.label[q] < 6) return true;
  return false;
}

bool rankConflict(int depth, int small, int high, int high2, const State& s) {
  int remaining = s.k - depth;
  return small > 1 || high + remaining < s.k - 4 ||
      high2 + remaining < max(0, s.k - 5);
}

bool mixedConflict(int small, const State& s) {
  if (small != 1) return false;
  bool zero = false, mone = false;
  for (int i = 0; i < N; ++i) {
    zero |= s.label[i] == 0 || s.label[i] == 9;
    mone |= s.label[i] == 2;
  }
  return zero && mone;
}

void emitCycle(const vector<Edge>& cycle, string& out) {
  out.push_back('C');
  out.push_back(digit((int)cycle.size()));
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
  if (rankConflict(depth, small, high, high2, s)) {
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
  if (depth == s.k) return false; // A supposedly closed pattern had a survivor.

  out.push_back('B');
  const int p = s.inner[depth];
  const vector<int> choices = {0, 9, 1, 2, 3, 4, 5, 6};
  for (int t : choices) {
    s.label[p] = t;
    int nextSmall = small + ((t <= 1 || t == 9) ? 1 : 0);
    int nextHigh = high + (t >= 5 && t <= 6 ? 1 : 0);
    int nextHigh2 = high2 + (t >= 6 && t <= 6 ? 1 : 0);
    if (!rec(depth + 1, nextSmall, nextHigh, nextHigh2, s, out)) return false;
  }
  s.label[p] = 8;
  return true;
}

int main(int argc, char** argv) {
  const string pattern = argc > 1 ? argv[1] : "000000010101011";
  if (pattern.size() != N) return 2;
  State state;
  state.label.fill(7);
  for (int i = 0; i < N; ++i) if (pattern[i] == '1') {
    state.inner.push_back(i);
    state.label[i] = 8;
  }
  state.k = (int)state.inner.size();
  string certificate;
  if (!rec(0, 0, 0, 0, state, certificate)) {
    cerr << "pattern has a surviving assignment; no closed certificate generated\n";
    return 1;
  }
  ofstream out("stage3_certificate_000000010101011.txt");
  out << pattern << '\t' << certificate << '\n';
  cerr << "pattern=" << pattern << " nodes=" << state.nodes
       << " leaves=" << state.leaves << " bytes=" << certificate.size() << '\n';
}

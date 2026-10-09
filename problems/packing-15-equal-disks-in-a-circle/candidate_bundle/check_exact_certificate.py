"""Independent checker for exact_subdivision_certificate.json.
Uses Fraction arithmetic only and does not import the subdivision searcher.
"""
import json
from functools import lru_cache
from fractions import Fraction as F
from pathlib import Path

BINS = [
    (F(0), F(1, 2)), (F(1, 2), F(1)), (F(1), F(3, 2)),
    (F(3, 2), F(8, 5)), (F(8, 5), F(5, 3)),
    (F(5, 3), F(17, 10)), (F(17, 10), F(37, 20)),
    (F(37, 20), F(2)), (F(2), F(43, 20)), (F(43, 20), F(23, 10)),
    (F(23, 10), F(2385432, 1000000)),
    (F(35213569647, 10000000000), F(35213569648, 10000000000)),
]
SCALE, TWO_PI_UP = 2800, 17600
LOCAL_LO, LOCAL_HI = F(42, 25), F(43, 25)

def atan_partial(x, terms):
    return sum(((-1) ** k) * x ** (2 * k + 1) / (2 * k + 1) for k in range(terms))

# Independently verify the pi bounds used by the exact angle comparisons.
_PI_LO = 16 * atan_partial(F(1, 5), 6) - 4 * atan_partial(F(1, 239), 1)
_PI_HI = 16 * atan_partial(F(1, 5), 7) - 4 * atan_partial(F(1, 239), 2)
assert F(8790, SCALE) < _PI_LO < _PI_HI < F(22, 7)
EXPECTED = {
    "000100100010101": {"roots": 47, "nodes": 1641, "cycles": 844, "sums": 0, "local": 0},
    "000100100100101": {"roots": 38, "nodes": 646, "cycles": 342, "sums": 0, "local": 0},
    "001001001001001": {"roots": 1181, "nodes": 56573, "cycles": 28846, "sums": 0, "local": 31},
}


@lru_cache(maxsize=None)
def cosine_lower(q):
    x = F(q, SCALE)
    y = x * x
    term = total = F(1)
    for j in range(1, 10):
        term *= -y / (2 * j * (2 * j - 1))
        total += term
    return total - x**19 / F(121645100408832000)


@lru_cache(maxsize=None)
def cosine_argument(x, y, positive_zero=False):
    if positive_zero:
        # The interval is the open-at-zero positive type (0,b]. Its closure is
        # used for monotone outward bounds; the exact zero is checked separately.
        p, other = (x, y) if x[0] == 0 else (y, x)
        if other[1] <= 2 and other[1] > 0:
            a, b = p[1], other[1]
            return (a*a + b*b - 4) / (2*a*b)
        return F(1)
    return max((a*a + b*b - 4) / (2*a*b) for a in x for b in y)


@lru_cache(maxsize=250000)
def required_integer_angle(x, y, positive_zero=False, exact_zero=False):
    if x[1] + y[1] < 2:
        return None
    if exact_zero:
        return 0
    upper = cosine_argument(x, y, positive_zero)
    if upper >= 1:
        return 0
    if upper <= -1:
        return 8700
    lo, hi = 0, 8790
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if cosine_lower(mid) >= upper:
            lo = mid
        else:
            hi = mid - 1
    assert cosine_lower(lo) >= upper
    return lo


def check_cycle(edges, box, positive_zero=frozenset(), exact_zero=frozenset()):
    assert edges and all(len(e) == 4 for e in edges)
    weights = []
    for n, (u, v, kind, recorded_q) in enumerate(edges):
        assert isinstance(u, int) and isinstance(v, int) and 0 <= u < 15 and 0 <= v < 15
        assert isinstance(recorded_q, int) and 0 <= recorded_q <= 8790
        next_u = edges[(n + 1) % len(edges)][0]
        assert v == next_u, (edges, n)
        if kind == "O":
            assert u == v + 1 and recorded_q == 0
            weights.append(0)
        elif kind == "L":
            assert u > v
            i, j = v, u
            q = required_integer_angle(box[i], box[j],
                bool(positive_zero.intersection((i, j))), bool(exact_zero.intersection((i, j))))
            assert q is not None and recorded_q == q, (recorded_q, q, i, j, box[i], box[j])
            weights.append(-recorded_q)
        elif kind == "U":
            assert u < v
            i, j = u, v
            q = required_integer_angle(box[i], box[j],
                bool(positive_zero.intersection((i, j))), bool(exact_zero.intersection((i, j))))
            assert q is not None and recorded_q == q, (recorded_q, q, i, j, box[i], box[j])
            weights.append(TWO_PI_UP - recorded_q)
        else:
            raise AssertionError(("unknown edge label", kind))
    total = sum(weights)
    assert total < 0, (total, edges)


def check_node(node, box, inner, pattern, counts):
    counts["nodes"] += 1
    kind = node[0]
    if kind == "SUM":
        assert len(node) == 3
        i, j = node[1:]
        assert isinstance(i, int) and isinstance(j, int) and 0 <= i < j < 15
        assert box[i][1] + box[j][1] < 2, (i, j, box[i], box[j])
        counts["sums"] += 1
        return
    if kind == "CYCLE":
        assert len(node) == 2
        check_cycle(node[1], box)
        counts["cycles"] += 1
        return
    if kind == "LOCAL":
        assert len(node) == 1 and pattern == "001001001001001"
        assert all(LOCAL_LO <= box[p][0] and box[p][1] <= LOCAL_HI for p in inner)
        counts["local"] += 1
        return
    if kind == "SPLIT":
        assert len(node) == 5
        p, mid_text, left, right = node[1:]
        assert isinstance(p, int) and p in inner
        mid = F(mid_text)
        lo, hi = box[p]
        assert mid == (lo + hi) / 2 and lo < mid < hi, (p, mid, box[p])
        box[p] = (lo, mid)
        check_node(left, box, inner, pattern, counts)
        box[p] = (mid, hi)
        check_node(right, box, inner, pattern, counts)
        box[p] = (lo, hi)
        return
    raise AssertionError(("unknown node kind", kind))


def check_special_cases(cases, residual_assignments):
    pattern = "001001001001011"
    inner = [i for i, symbol in enumerate(pattern) if symbol == "1"]
    modes = {"POSITIVE_LOW", "POSITIVE_HIGH", "EXACT_ZERO"}
    seen = set()
    for case in cases:
        assignment, mode, vertex, leaf = case["assignment"], case["mode"], case["vertex"], case["leaf"]
        assert case["pattern"] == pattern and mode in modes
        assert len(assignment) == len(inner) and assignment.isdigit()
        zeros = [j for j, digit in enumerate(assignment) if digit == "0"]
        assert len(zeros) == 1 and vertex == inner[zeros[0]]
        assert (assignment, mode) not in seen
        seen.add((assignment, mode))
        box = [BINS[11]] * 15
        for p, digit in zip(inner, map(int, assignment)):
            box[p] = BINS[digit]
        if mode == "POSITIVE_LOW":
            box[vertex] = (F(0), F(1, 4)); positive = {vertex}; exact = set()
        elif mode == "POSITIVE_HIGH":
            box[vertex] = (F(1, 4), F(1, 2)); positive = set(); exact = set()
        else:
            box[vertex] = (F(0), F(0)); positive = set(); exact = {vertex}
        if leaf[0] == "SUM":
            assert len(leaf) == 3
            i, j = leaf[1:]
            assert 0 <= i < j < 15 and box[i][1] + box[j][1] < 2
        else:
            assert leaf[0] == "CYCLE" and len(leaf) == 2
            check_cycle(leaf[1], box, positive, exact)
    assert len(seen) == 9
    assignments = {assignment for assignment, _ in seen}
    assert len(assignments) == 3
    assert assignments == residual_assignments, (assignments, residual_assignments)
    for assignment in assignments:
        assert {(a, m) for a, m in seen if a == assignment} == {(assignment, m) for m in modes}
    print("independently checked 6+9 special cases: 3 assignments x 3 radius-zero branches = 9 leaves")


def main():
    document = json.loads(Path("exact_subdivision_certificate.json").read_text())
    assert document.get("format") == "unequal-circle-exact-subdivision-v1"
    residual_rows = {}
    for line in Path("full_residuals.txt").read_text().splitlines():
        fields = line.split("\t")
        if len(fields) >= 6 and fields[0] == "UNKNOWN":
            assert fields[2] not in residual_rows
            assignments = [a for a in fields[5].split(",") if a]
            assert len(assignments) == int(fields[3]) == int(fields[4]) == len(set(assignments))
            residual_rows[fields[2]] = assignments
    assert set(residual_rows) == set(EXPECTED) | {"001001001001011"}
    check_special_cases(document.get("special_cases", []), set(residual_rows["001001001001011"]))
    residual_roots = {mask: [] for mask in EXPECTED}
    for mask in EXPECTED:
        residual_roots[mask] = residual_rows[mask]
    assert {m: len(xs) for m, xs in residual_roots.items()} == {m: d["roots"] for m, d in EXPECTED.items()}
    observed = {mask: [] for mask in EXPECTED}
    total = {mask: {"roots": 0, "nodes": 0, "cycles": 0, "sums": 0, "local": 0} for mask in EXPECTED}
    seen = set()
    for root in document["roots"]:
        pattern, assignment, tree = root["pattern"], root["assignment"], root["tree"]
        assert pattern in EXPECTED and assignment in residual_roots[pattern]
        assert (pattern, assignment) not in seen
        seen.add((pattern, assignment));observed[pattern].append(assignment)
        inner = [i for i, symbol in enumerate(pattern) if symbol == "1"]
        assert len(assignment) == len(inner) and assignment.isdigit() and "0" not in assignment
        box = [BINS[11]] * 15
        for p, digit in zip(inner, map(int, assignment)):
            assert 1 <= digit <= 10
            box[p] = BINS[digit]
        counts = {"nodes": 0, "cycles": 0, "sums": 0, "local": 0}
        check_node(tree, box, inner, pattern, counts)
        total[pattern]["roots"] += 1
        for key in counts:
            total[pattern][key] += counts[key]
    for pattern, values in observed.items():
        assert set(values) == set(residual_roots[pattern]), (pattern, len(values), len(residual_roots[pattern]))
        assert total[pattern] == EXPECTED[pattern], (pattern, total[pattern], EXPECTED[pattern])
        print("independently checked", pattern, total[pattern])
    print("all exact subdivision certificate leaves verified with rational arithmetic")

if __name__ == "__main__":
    main()

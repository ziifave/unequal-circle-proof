"""Independently check the serialized exclusions for all stage-zero orbit types.

The checker regenerates the 760 binary dihedral classes, enumerates every
radial type assignment allowed by the elementary rank constraints, and checks
one exact integer negative-cycle witness for each assignment of every excluded
class. It deliberately does not import or run the C++ search implementation.
"""
import itertools
import gzip
import json
from pathlib import Path

N = 15
TWO_PI_UP = 17600
# Rows and columns are O, S, M, H. verify_coarse_angles.py separately certifies
# that every positive entry is a strict rational lower bound in units 1/2800.
Q = (
    (1610, 0, 0, 840),
    (0, 0, 0, 0),
    (0, 0, 3360, 2408),
    (840, 0, 2408, 2408),
)


def canonical(word):
    variants = []
    for oriented in (word, word[::-1]):
        variants.extend(oriented[i:] + oriented[:i] for i in range(N))
    return min(variants)


def orbit_classes():
    result = {}
    for k in range(5, 9):
        classes = {
            canonical("".join("1" if i in selected else "0" for i in range(N)))
            for selected in itertools.combinations(range(N), k)
        }
        expected = {5: 111, 6: 185, 7: 232, 8: 232}[k]
        assert len(classes) == expected, (k, len(classes), expected)
        result.update({word: k for word in classes})
    assert len(result) == 760
    return result


def admissible_assignments(k):
    # Type S has radius <1, so at most one S center is possible. By the known
    # five-disk lower bound, at least k-4 inner centers have type H (radius
    # >=5/3). These are precisely the complete assignments not discharged by
    # the two structural prunes in the C++ recursion.
    for labels in itertools.product((1, 2, 3), repeat=k):
        if labels.count(1) <= 1 and labels.count(3) >= k - 4:
            yield "".join(map(str, labels))


def verify_cycle(word, assignment, cycle):
    inner = [i for i, symbol in enumerate(word) if symbol == "1"]
    assert len(assignment) == len(inner) and set(assignment) <= {"1", "2", "3"}
    labels = [0] * N  # Every outer center has type O.
    for pos, digit in zip(inner, map(int, assignment)):
        labels[pos] = digit
    assert cycle and len(cycle) <= N
    weights = []
    for i, edge in enumerate(cycle):
        assert len(edge) == 3
        u, v, kind = edge
        assert isinstance(u, int) and isinstance(v, int) and 0 <= u < N and 0 <= v < N
        assert v == cycle[(i + 1) % len(cycle)][0], (cycle, i)
        if kind == "O":
            assert u == v + 1 and 0 <= v < N - 1
            weights.append(0)
        elif kind == "L":
            assert u > v
            weights.append(-Q[labels[v]][labels[u]])
        elif kind == "U":
            assert u < v
            weights.append(TWO_PI_UP - Q[labels[u]][labels[v]])
        else:
            raise AssertionError(("unknown edge type", kind))
    assert sum(weights) < 0, (word, assignment, cycle, weights)


def has_no_negative_cycle(word, assignment):
    """Check the claimed retained witness with an independent Bellman-Ford."""
    inner = [i for i, symbol in enumerate(word) if symbol == "1"]
    labels = [0] * N
    for pos, digit in zip(inner, map(int, assignment)):
        labels[pos] = digit
    edges = [(i + 1, i, 0) for i in range(N - 1)]
    for i in range(N):
        for j in range(i + 1, N):
            q = Q[labels[i]][labels[j]]
            edges.append((j, i, -q))
            edges.append((i, j, TWO_PI_UP - q))
    distance = [0] * N
    for _ in range(N):
        changed = False
        for u, v, weight in edges:
            if distance[v] > distance[u] + weight:
                distance[v] = distance[u] + weight
                changed = True
        if not changed:
            return True
    return False


def main():
    expected_orbits = orbit_classes()
    with gzip.open("stage0_certificate.json.gz", "rt") as source:
        document = json.load(source)
    assert document.get("format") == "unequal-circle-stage0-v1"
    records = document.get("orbits", [])
    assert len(records) == len(expected_orbits)
    by_word = {}
    for row in records:
        word, k, status = row["pattern"], row["k"], row["status"]
        assert word in expected_orbits and expected_orbits[word] == k
        assert word not in by_word
        by_word[word] = row
        if status == "NEGATIVE_CYCLES":
            cases = row["cases"]
            observed = {}
            for case in cases:
                assignment = case["assignment"]
                assert assignment not in observed
                verify_cycle(word, assignment, case["cycle"])
                observed[assignment] = True
            expected = set(admissible_assignments(k))
            assert set(observed) == expected, (word, len(observed), len(expected))
        elif status == "UNKNOWN":
            assert row["cases"] == []
            witness = row["witness"]
            assert witness in set(admissible_assignments(k))
            assert has_no_negative_cycle(word, witness), (word, witness)
        else:
            raise AssertionError((word, status))
    assert set(by_word) == set(expected_orbits)

    # Bind the machine-checkable certificate to the list consumed by stages 3
    # and 4, preventing a stale or differently classified orbit table.
    listed = {}
    for line in Path("verified_orbits.tsv").read_text().splitlines():
        fields = line.split("\t")
        if len(fields) == 4 and fields[0] == "orbit":
            listed[(int(fields[1]), fields[2])] = fields[3]
    assert len(listed) == 760
    for word, k in expected_orbits.items():
        certificate_status = by_word[word]["status"]
        expected_status = "NEGATIVE_CYCLE" if certificate_status == "NEGATIVE_CYCLES" else "UNKNOWN"
        assert listed[(k, word)] == expected_status
    eliminated = sum(row["status"] == "NEGATIVE_CYCLES" for row in records)
    retained = len(records) - eliminated
    assert (eliminated, retained) == (382, 378), (eliminated, retained)
    print(f"independently checked stage-zero certificate: {len(records)} orbit classes; "
          f"{eliminated} excluded with complete cycle witnesses; {retained} retained")


if __name__ == "__main__":
    main()

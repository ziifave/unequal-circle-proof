"""Emit explicit exact subdivision trees for the 5+10 residual boxes."""
import json
import time
from fractions import Fraction as F
from pathlib import Path
from certify_six_nine import B, TWOPI, cycle
from verify_noncanonical_exact import ang, detect

TARGETS = {
    "000100100010101": 47,
    "000100100100101": 38,
    "001001001001001": 1181,
}
CANONICAL = "001001001001001"
LOCAL_LO, LOCAL_HI = F(42, 25), F(43, 25)


def build_tree(pattern, assignment, stats):
    inner = [i for i, symbol in enumerate(pattern) if symbol == "1"]
    box = [B[11]] * 15
    for p, digit in zip(inner, map(int, assignment)):
        box[p] = B[digit]
    def visit():
        stats["nodes"] += 1
        if pattern == CANONICAL and all(LOCAL_LO <= box[p][0] and box[p][1] <= LOCAL_HI for p in inner):
            stats["local"] += 1
            return ["LOCAL"]
        kind, payload = detect(tuple(box))
        if kind == "SUM":
            stats["sums"] += 1
            return ["SUM", payload[0], payload[1]]
        if kind == "CYCLE":
            stats["cycles"] += 1
            edges = []
            for u, v, edge_kind in payload:
                q = 0 if edge_kind == "O" else ang(box[min(u, v)], box[max(u, v)])
                assert q is not None
                edges.append([u, v, edge_kind, q])
            return ["CYCLE", edges]
        assert kind == "OPEN", kind
        _, _, p = max((box[p][1] - box[p][0], -p, p) for p in inner)
        lo, hi = box[p]
        assert lo < hi, (pattern, assignment, p, box[p])
        mid = (lo + hi) / 2
        box[p] = (lo, mid)
        left = visit()
        box[p] = (mid, hi)
        right = visit()
        box[p] = (lo, hi)
        return ["SPLIT", p, f"{mid.numerator}/{mid.denominator}", left, right]
    tree = visit()
    return tree


def main():
    started = time.time()
    roots = {mask: [] for mask in TARGETS}
    for line in Path("full_residuals.txt").read_text().splitlines():
        fields = line.split("\t")
        if len(fields) < 6 or fields[0] != "UNKNOWN" or fields[2] not in TARGETS:
            continue
        mask = fields[2]
        assignments = [item for item in fields[5].split(",") if item]
        assert len(assignments) == int(fields[3]) == int(fields[4]) == TARGETS[mask]
        assert len(assignments) == len(set(assignments))
        assert all(len(a) == int(fields[1]) and a.isdigit() and "0" not in a for a in assignments)
        roots[mask] = assignments
    assert {mask: len(values) for mask, values in roots.items()} == TARGETS
    all_roots = []
    overall = {"nodes": 0, "cycles": 0, "sums": 0, "local": 0}
    for pattern in TARGETS:
        stats = {"nodes": 0, "cycles": 0, "sums": 0, "local": 0}
        for assignment in roots[pattern]:
            tree = build_tree(pattern, assignment, stats)
            all_roots.append({"pattern": pattern, "assignment": assignment, "tree": tree})
        if pattern == "000100100010101":
            expected = {"nodes": 1641, "cycles": 844, "sums": 0, "local": 0}
        elif pattern == "000100100100101":
            expected = {"nodes": 646, "cycles": 342, "sums": 0, "local": 0}
        else:
            expected = {"nodes": 56573, "cycles": 28846, "sums": 0, "local": 31}
        assert stats == expected, (pattern, stats, expected)
        print("generated", pattern, stats, flush=True)
        for key in overall:
            overall[key] += stats[key]
    # The 6+9 residual is closed by nine explicit leaves: two positive-radius
    # halves and the exact-zero singleton for each generated radial assignment.
    special = []
    six_nine = "001001001001011"
    six_positions = [i for i, symbol in enumerate(six_nine) if symbol == "1"]
    six_assignments = []
    for line in Path("full_residuals.txt").read_text().splitlines():
        fields = line.split("\t")
        if len(fields) >= 6 and fields[0] == "UNKNOWN" and fields[2] == six_nine:
            six_assignments = [item for item in fields[5].split(",") if item]
            assert len(six_assignments) == int(fields[3]) == int(fields[4]) == 3
    assert len(six_assignments) == 3
    for assignment in six_assignments:
        digits = list(map(int, assignment))
        zero_slots = [j for j, digit in enumerate(digits) if digit == 0]
        assert len(zero_slots) == 1
        slot = zero_slots[0]
        vertex = six_positions[slot]
        for mode in ["POSITIVE_LOW", "POSITIVE_HIGH", "EXACT_ZERO"]:
            box = [B[11]] * 15
            for j, (p, digit) in enumerate(zip(six_positions, digits)):
                box[p] = B[digit]
                if j == slot:
                    if mode == "POSITIVE_LOW": box[p] = (F(0), F(1, 4))
                    elif mode == "POSITIVE_HIGH": box[p] = (F(1, 4), F(1, 2))
                    else: box[p] = (F(0), F(0))
            result = cycle(box)
            if mode == "POSITIVE_LOW":
                assert result["reason"] == "PAIR_SUM", (assignment, mode, result)
            elif mode == "POSITIVE_HIGH":
                assert result["reason"] == "NEGATIVE_CYCLE", (assignment, mode, result)
            else:
                assert result["reason"] in ("PAIR_SUM", "NEGATIVE_CYCLE"), (assignment, mode, result)
            if result["reason"] == "PAIR_SUM":
                leaf = ["SUM", *result["pair"]]
            else:
                kind_map = {"ORDER": "O", "LOWER": "L", "UPPER": "U"}
                edges = []
                for u, v, weight, edge_kind in result["edges"]:
                    q = 0 if edge_kind == "ORDER" else (-weight if edge_kind == "LOWER" else TWOPI - weight)
                    edges.append([u, v, kind_map[edge_kind], q])
                leaf = ["CYCLE", edges]
            special.append({"pattern": six_nine, "assignment": assignment, "mode": mode,
                            "vertex": vertex, "leaf": leaf})
    assert len(special) == 9
    document = {"format": "unequal-circle-exact-subdivision-v1", "roots": all_roots, "special_cases": special}
    Path("exact_subdivision_certificate.json").write_text(json.dumps(document, separators=(",", ":")) + "\n")
    print("certificate roots", len(all_roots), "special leaves", len(special), "totals", overall,
          "bytes", Path("exact_subdivision_certificate.json").stat().st_size,
          "seconds", round(time.time() - started, 2), flush=True)

if __name__ == "__main__":
    main()

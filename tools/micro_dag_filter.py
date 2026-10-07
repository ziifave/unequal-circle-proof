"""Proof-safe small Henneberg-I prefix plus closure filter."""
from __future__ import annotations

import argparse
import itertools
import json
from decimal import Decimal
from pathlib import Path

from proof.interval import D, Interval, set_precision
from tools.dag_monotonicity_cert import intersection
from tools.hennenberg_core_isolation import Dual, const, radii, sqrt_dual, vec_norm2, vec_sub

R_LO = D("7.7997")
R_HI = D("8.3034681221114890787043811875161993299502137405353848")


def distance(v, u, R):
    return R - const(radii(v)) if u == 0 else const(radii(v) + radii(u))


def closure_residual(graph, seq, prefix, closure, signs, R):
    z = const(0)
    p = {0: (z, z)}
    base = seq["base"]
    a, b = base[1], base[2]
    p[a] = (R - const(radii(a)), z)
    p[b] = intersection(p[0], p[a], distance(b, 0, R),
                        const(radii(a) + radii(b)), 1, [])
    construction = list(reversed(seq["reverse"]))[:prefix]
    radicands = []
    for sign, item in zip(signs, construction):
        v = item["vertex"]
        u, w = item["neighbors"]
        p[v] = intersection(p[u], p[w], distance(v, u, R),
                            distance(v, w, R), sign, radicands)
    i, j = closure
    if i not in p or j not in p:
        raise ValueError("closure endpoint is outside motif")
    actual = sqrt_dual(vec_norm2(vec_sub(p[i], p[j])))
    required = R - const(radii(j)) if i == 0 else distance(i, j, R)
    return actual * actual - required * required, radicands


def motif_closes(graph, seq, prefix, closure, r_slices=1):
    branches = []
    cuts = [R_LO + (R_HI - R_LO) * i / r_slices for i in range(r_slices + 1)]
    for signs in itertools.product((-1, 1), repeat=prefix):
        slice_results = []
        for lo, hi in zip(cuts, cuts[1:]):
            try:
                residual, radicands = closure_residual(
                    graph, seq, prefix, closure, signs,
                    Dual(Interval(lo, hi), Interval.point(1)))
            except (ValueError, ZeroDivisionError):
                slice_results.append({"status": "UNKNOWN"})
                continue
            if any(r.value.hi < 0 for r in radicands):
                slice_results.append({"status": "NO_INTERSECTION"})
            elif residual.value.hi < 0 or residual.value.lo > 0:
                slice_results.append({"status": "CLOSURE_MISMATCH",
                                      "residual": [str(residual.value.lo), str(residual.value.hi)]})
            else:
                slice_results.append({"status": "UNKNOWN",
                                      "residual": [str(residual.value.lo), str(residual.value.hi)]})
        branches.append({"signs": list(signs), "slices": slice_results})
    # A sign branch is impossible only when every R slice is certified dead.
    failed = all(all(s["status"] in {"NO_INTERSECTION", "CLOSURE_MISMATCH"}
                     for s in b["slices"]) for b in branches)
    return failed, branches


def candidates(graph, seq, max_prefix=4):
    base = set(seq["base"])
    construction = list(reversed(seq["reverse"]))
    graph_edges = {tuple(sorted(e)) for e in graph["pair_contacts"]}
    graph_edges |= {(0, v) for v in graph["wall_contacts"]}
    used = {tuple(sorted((seq["base"][i], seq["base"][j])))
            for i in range(3) for j in range(i + 1, 3)}
    out = []
    for k, item in enumerate(construction):
        used |= {tuple(sorted((item["vertex"], n))) for n in item["neighbors"]}
        if k + 1 > max_prefix:
            break
        vertices = base | {x["vertex"] for x in construction[:k + 1]}
        out.extend((k + 1, e) for e in sorted(graph_edges - used)
                   if set(e) <= vertices)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("input", type=Path)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--max-topologies", type=int, default=None)
    ap.add_argument("--max-prefix", type=int, default=4)
    ap.add_argument("--max-sequences", type=int, default=200)
    ap.add_argument("--max-motifs", type=int, default=32)
    ap.add_argument("--r-slices", type=int, default=1)
    args = ap.parse_args()
    set_precision(70)
    data = json.loads(args.input.read_text())
    records = data if isinstance(data, list) else data["records"]
    if args.max_topologies is not None:
        records = records[:args.max_topologies]
    ledger = {"topologies": len(records), "MICRO_DAG_FAIL": 0,
              "UNRESOLVED": 0, "examples": {}}
    results = []
    for record in records:
        graph = record.get("graph", record)
        sequences = record.get("sequences", [])
        topology_result = {"index": record.get("index"), "motifs": []}
        rejected = False
        motif_candidates = []
        for seq in sequences[:args.max_sequences]:
            for prefix, closure in candidates(graph, seq, args.max_prefix):
                motif_candidates.append((prefix, closure, seq))
        # Longer prefixes expose more closure structure.  The cap controls
        # runtime only; skipping a motif can never cause a false rejection.
        motif_candidates.sort(key=lambda item: (-len(item[1]), -item[0], item[1]))
        for prefix, closure, seq in motif_candidates[:args.max_motifs]:
            failed, branches = motif_closes(graph, seq, prefix, closure, args.r_slices)
            item = {"prefix": prefix, "closure": list(closure),
                    "failed": failed, "branches": branches}
            topology_result["motifs"].append(item)
            if failed:
                rejected = True
                break
            if rejected:
                break
        if rejected:
            ledger["MICRO_DAG_FAIL"] += 1
            ledger["examples"].setdefault("MICRO_DAG_FAIL", topology_result)
        else:
            ledger["UNRESOLVED"] += 1
        results.append(topology_result)
    payload = {"input": str(args.input), "ledger": ledger, "results": results,
               "note": "A topology is rejected only when every sign branch of a selected prefix motif has no intersection or a closure residual excluding zero over [R_LO,R_HI]."}
    args.output.write_text(json.dumps(payload, indent=2) + "\n")
    print(json.dumps(ledger, indent=2))


if __name__ == "__main__":
    main()

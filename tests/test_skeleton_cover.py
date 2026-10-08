"""Coverage and false-exclusion regressions for the global skeleton ledger."""
from copy import deepcopy
from fractions import Fraction as Q
import unittest

from proof.skeleton_cover import (
    CASES_PER_CYCLE, PAIRS, assignment_index, assignment_masks, cell_bounds,
    global_radial_bounds, negative_cycle, parse_roots, partition_spec,
    propagate_radial, sector_spans, verify, verify_cycle,
    effective_masks, full_order_graph, projected_orders, verify_order_group,
)
from tools.certify_large_four_skeleton import build_certificate
from tools.certify_skeleton_cover import build, root_witnesses


class SkeletonCoverTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.coarse = build(build_certificate(), {})
        cls.split = build(build_certificate(), {str(i): 2 for i in (7, 8, 9, 10)})
        cls.allpair = build(build_certificate(), {str(i): 2 for i in (7, 8, 9, 10)},
                            all_pair_orders=True)

    def test_full_partition_and_assignment_coverage(self):
        report = verify(self.split)
        self.assertTrue(report["coverage_verified"])
        self.assertEqual(report["radial_cells"], 16)
        self.assertEqual(report["covered_cases"], 16 * 3 * 4096)
        self.assertGreater(report["closed_cases"], 0)
        self.assertGreater(report["unknown_cases"], 0)
        self.assertEqual(report["closed_cases"] + report["unknown_cases"], report["covered_cases"])
        self.assertFalse(report["global_optimality_proved"])

    def test_known_witness_class_stays_unknown(self):
        # From the published full configuration + refined core, after
        # reflection into the canonical order (10,7,9,8). This is a
        # false-exclusion regression, not an existence proof for the witness.
        cell = next(c for c in self.split["cells"] if c["index"] == [1, 1, 1, 0])
        record = next(r for r in cell["cycles"] if r["order"] == [10, 7, 9, 8])
        case = assignment_index((1, 2, 0, 3, 0, 3))
        self.assertEqual(record["outcomes"][case], -1)

    def test_every_small_disk_is_assigned_exactly_once(self):
        masks = assignment_masks()
        self.assertEqual(len(masks), CASES_PER_CYCLE)
        self.assertEqual(len(set(masks)), CASES_PER_CYCLE)
        for row in masks:
            self.assertEqual(sum(row), 63)
            for a in range(4):
                for b in range(a):
                    self.assertEqual(row[a] & row[b], 0)

    def test_radial_partition_has_no_gap(self):
        roots = parse_roots(root_witnesses())
        spec = partition_spec({"10": 3})
        cells = [cell_bounds(roots, spec, (i,))[10] for i in range(3)]
        initial = global_radial_bounds(roots)[10]
        self.assertEqual(cells[0][0], initial[0])
        self.assertEqual(cells[-1][1], initial[1])
        self.assertTrue(all(a[1] == b[0] for a, b in zip(cells, cells[1:])))

    def test_inner_disk_forces_other_disks_outwards(self):
        roots = parse_roots(root_witnesses())
        bounds = global_radial_bounds(roots)
        bounds[10] = bounds[10][0], Q("1.2")
        result = propagate_radial(bounds, roots)
        self.assertGreater(result[1][0], bounds[1][0])
        self.assertEqual(result[1][0], roots[1][0] + roots[10][0] - Q("1.2"))

    def test_sector_span_uses_all_orders_and_nonadjacent_pairs(self):
        weights = [[0] * 11 for _ in range(11)]
        for i, j, value in ((7, 1, 3), (1, 8, 4), (1, 2, 10), (7, 8, 2)):
            weights[i][j] = weights[j][i] = value
        table = sector_spans(tuple(tuple(row) for row in weights))
        self.assertEqual(table[(7, 8)][3], 13)  # orders (1,2):13 and (2,1):14
        self.assertEqual(table[(7, 8)][1], 7)
        self.assertEqual(table[(7, 8)][1 | 4], 7)  # zero-weight disk 3
        weights[7][8] = weights[8][7] = 20
        table = sector_spans(tuple(tuple(row) for row in weights))
        self.assertEqual(table[(7, 8)][3], 20)

    def test_missing_and_duplicate_radial_cells_are_rejected(self):
        for duplicate in (False, True):
            data = deepcopy(self.split)
            if duplicate:
                data["cells"][-1] = data["cells"][0]
            else:
                data["cells"].pop()
            with self.assertRaisesRegex(ValueError, "radial cell"):
                verify(data)

    def test_missing_cyclic_class_is_rejected(self):
        data = deepcopy(self.coarse)
        data["cells"][0]["cycles"].pop()
        with self.assertRaisesRegex(ValueError, "cyclic class"):
            verify(data)

    def test_missing_sector_assignment_is_rejected(self):
        data = deepcopy(self.coarse)
        data["cells"][0]["cycles"][0]["outcomes"].pop()
        with self.assertRaisesRegex(ValueError, "assignment ledger"):
            verify(data)

    def test_overstated_angle_is_rejected(self):
        data = deepcopy(self.coarse)
        data["cells"][0]["angles"][PAIRS.index((7, 8))] = 1500000
        with self.assertRaisesRegex(ValueError, "overstated angle"):
            verify(data)

    def test_positive_angle_for_possible_origin_is_rejected(self):
        data = deepcopy(self.coarse)
        data["cells"][0]["angles"][PAIRS.index((1, 2))] = 100000
        with self.assertRaisesRegex(ValueError, "undefined centre direction"):
            verify(data)

    def test_fake_pair_sum_contradiction_is_rejected(self):
        data = deepcopy(self.coarse)
        data["cells"][0] = {"index": [], "kind": "PAIR_SUM", "pair": [7, 8]}
        with self.assertRaisesRegex(ValueError, "pair-sum contradiction"):
            verify(data)

    def test_fabricated_leaf_cycle_is_rejected(self):
        data = deepcopy(self.coarse)
        record = data["cells"][0]["cycles"][0]
        record["outcomes"][0] = 0
        record["witnesses"] = [[0, 1]]  # both pair arcs have a positive sum
        with self.assertRaisesRegex(ValueError, "not strictly negative"):
            verify(data)

    def test_float_bounds_are_rejected(self):
        data = deepcopy(self.coarse)
        data["sqrt_enclosures"][0]["lo"] = 1.0
        with self.assertRaisesRegex(ValueError, "must be strings"):
            verify(data)

    def test_cycle_verifier_rejects_zero_positive_and_disconnected_cycles(self):
        edges = [(0, 1, -2), (1, 0, 1)]
        witness = negative_cycle(2, edges)
        self.assertIsNotNone(witness)
        verify_cycle(edges, witness)
        for bad in ([(0, 1, -1), (1, 0, 1)], [(0, 1, 1), (1, 0, 1)],
                    edges + [(2, 3, -2), (3, 2, 1)]):
            with self.assertRaises(ValueError):
                verify_cycle(bad, list(range(len(bad))))

    def test_all_pair_models_are_verified_but_stay_unknown(self):
        report = verify(self.allpair)
        self.assertGreater(report["angular_models_verified"], 0)
        self.assertGreater(report["unknown_cases"], 0)
        self.assertFalse(report["global_optimality_proved"])

    def test_missing_duplicate_and_false_angular_models_are_rejected(self):
        for mutation in ("missing", "duplicate", "invalid_potential", "wrong_sector"):
            data = deepcopy(self.allpair)
            record = next(r for c in data["cells"] for r in c.get("cycles", [])
                          if r.get("order_groups"))
            if mutation == "missing":
                record["order_groups"].pop()
            elif mutation == "duplicate":
                record["order_groups"].append(record["order_groups"][0])
            else:
                group = record["order_groups"][0]
                if mutation == "invalid_potential":
                    group["potentials"] = [0] * len(group["order"])
                else:
                    group["order"] = group["order"][::-1]
            with self.assertRaises(ValueError, msg=mutation):
                verify(data)

    def test_projection_enumerates_both_orders_and_drops_only_zero_vertices(self):
        weights = [[0] * 11 for _ in range(11)]
        for i in (1, 2):
            weights[i][7] = weights[7][i] = 1
        weights = tuple(tuple(row) for row in weights)
        masks = effective_masks(weights, (7, 8, 16, 32))
        self.assertEqual(masks, (3, 0, 0, 0))
        skeleton = (10, 7, 8, 9)
        orders = list(projected_orders(skeleton, masks))
        self.assertEqual(orders, [(10, 1, 2, 7, 8, 9), (10, 2, 1, 7, 8, 9)])

    def test_all_orders_exclusion_requires_every_projected_order(self):
        # Synthetic inconsistent angular system, independent of radius bounds.
        # The test targets exhaustive order replay, not angle certification.
        weights = tuple(tuple(2000000 if i != j else 0 for j in range(11))
                        for i in range(11))
        skeleton, masks = (10, 7, 8, 9), (3, 0, 0, 0)
        witnesses = [list(negative_cycle(len(o), full_order_graph(o, weights, skeleton)))
                     for o in projected_orders(skeleton, masks)]
        group = {"kind": "ALL_ORDERS_EXCLUDED", "witnesses": witnesses}
        self.assertTrue(verify_order_group(group, skeleton, masks, weights))
        group["witnesses"].pop()
        with self.assertRaisesRegex(ValueError, "missing projected order"):
            verify_order_group(group, skeleton, masks, weights)

    def test_known_witness_all_pair_group_is_retained(self):
        cell = next(c for c in self.allpair["cells"] if c["index"] == [1, 1, 1, 0])
        record = cell["cycles"][1]
        case = assignment_index((1, 2, 0, 3, 0, 3))
        from proof.skeleton_cover import verify_angles
        roots = parse_roots(self.allpair["sqrt_enclosures"])
        bounds = propagate_radial(cell_bounds(roots, partition_spec(self.allpair["radial_partitions"]),
                                             tuple(cell["index"])), roots)
        weights = verify_angles(cell["angles"], bounds, roots)
        masks = effective_masks(weights, assignment_masks()[case])
        group = next(g for g in record["order_groups"] if tuple(g["masks"]) == masks)
        self.assertEqual(group["kind"], "ANGLE_MODEL")


if __name__ == "__main__":
    unittest.main()

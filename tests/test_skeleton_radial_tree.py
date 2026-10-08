"""Coverage, resume, and false-exclusion tests for the adaptive tree."""
from copy import deepcopy
from fractions import Fraction as Q
import unittest

from proof.skeleton_cover import LABELS, global_radial_bounds, parse_roots
from proof.skeleton_radial_tree import split_bounds, verify
from tools.certify_large_four_skeleton import build_certificate
from tools.certify_skeleton_radial_tree import explore, new_tree


class SkeletonRadialTreeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = new_tree(build_certificate())
        cls.tree = explore(deepcopy(cls.root), 6)

    def test_root_covers_all_sector_assignments(self):
        report = verify(self.root)
        self.assertTrue(report["coverage_verified"])
        self.assertEqual(report["unknown_leaf_sector_cases"], 12288)
        self.assertFalse(report["global_optimality_proved"])

    def test_splits_cover_endpoints_and_share_the_cut(self):
        bounds = global_radial_bounds(parse_roots(self.root["sqrt_enclosures"]))
        cut = sum(bounds[10]) / 2
        left, right = split_bounds(bounds, 10, cut)
        self.assertEqual(left[10], (bounds[10][0], cut))
        self.assertEqual(right[10], (cut, bounds[10][1]))
        for i in LABELS[:-1]:
            self.assertEqual(left[i], bounds[i])
            self.assertEqual(right[i], bounds[i])

    def test_resume_matches_an_uninterrupted_run(self):
        uninterrupted = explore(deepcopy(self.root), 9)
        resumed = explore(deepcopy(self.tree), 3)
        self.assertEqual(resumed, uninterrupted)
        report = verify(resumed)
        self.assertEqual(report["nodes"], 19)
        self.assertEqual(report["leaves"], 10)
        self.assertTrue(report["coverage_verified"])

    def test_missing_child_shared_child_and_back_edge_are_rejected(self):
        for children in ([1], [1, 1], [0, 1]):
            data = deepcopy(self.tree)
            data["nodes"][0]["children"] = children
            with self.assertRaises(ValueError):
                verify(data)

    def test_outside_cut_float_cut_and_invalid_label_are_rejected(self):
        for field, value in (("cut", "100"), ("cut", 1.0), ("label", True), ("label", 11)):
            data = deepcopy(self.tree)
            data["nodes"][0][field] = value
            with self.assertRaises(ValueError):
                verify(data)

    def test_stale_missing_and_duplicate_frontier_are_rejected(self):
        for mutation in ("missing", "duplicate", "stale"):
            data = deepcopy(self.tree)
            if mutation == "missing":
                data["frontier"].pop()
            elif mutation == "duplicate":
                data["frontier"].append(data["frontier"][0])
            else:
                data["frontier"][0] = 0
            with self.assertRaisesRegex(ValueError, "frontier"):
                verify(data)
            with self.assertRaises(ValueError):
                explore(data, 1)

    def test_unreachable_node_is_rejected(self):
        data = deepcopy(self.tree)
        data["nodes"].append(deepcopy(self.root["nodes"][0]))
        with self.assertRaisesRegex(ValueError, "unreachable"):
            verify(data)

    def test_small_box_and_unproved_terminal_are_rejected(self):
        for kind in ("SMALL_BOX", "LOCAL_LOWER_BOUND", "INFEASIBLE"):
            data = deepcopy(self.root)
            data["nodes"][0] = {"kind": kind}
            with self.assertRaises(ValueError):
                verify(data)

    def test_zero_budget_keeps_all_unresolved_leaves(self):
        self.assertEqual(explore(deepcopy(self.tree), 0), self.tree)


if __name__ == "__main__":
    unittest.main()

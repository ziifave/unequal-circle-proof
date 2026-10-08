"""Boundary, completeness, and tamper tests for the rational replay kernel."""
from copy import deepcopy
from decimal import Context, ROUND_CEILING, ROUND_FLOOR, localcontext
from fractions import Fraction
import unittest

from proof.large_four_certificate import (
    canonical_cycles, halfplane_witness, pi_bounds, verify_certificate, verify_frontier,
)
from tools.certify_large_four_skeleton import build_certificate


class LargeFourCertificateTests(unittest.TestCase):
    def setUp(self):
        self.certificate = build_certificate()

    def test_complete_exact_certificate(self):
        report = verify_certificate(self.certificate)
        self.assertEqual(report["orders_verified"], 24)
        self.assertEqual(Fraction(report["minimum_path_lower"]), Fraction("3.3019"))
        self.assertEqual(Fraction(report["minimum_margin"]), Fraction("0.1603"))
        self.assertEqual(len(canonical_cycles()), 3)
        self.assertEqual(report["coarse_sector_assignment_count"], 12288)
        self.assertFalse(report["global_optimality_proved"])

    def test_decimal_context_cannot_affect_rational_replay(self):
        with localcontext(Context(prec=3, rounding=ROUND_CEILING)):
            first = verify_certificate(self.certificate)
        with localcontext(Context(prec=4, rounding=ROUND_FLOOR)):
            second = verify_certificate(self.certificate)
        self.assertEqual(first, second)

    def test_pi_upper_is_proved_instead_of_trusted(self):
        lo, hi = pi_bounds()
        self.assertLess(Fraction("3.1415"), lo)
        self.assertLess(hi, Fraction("3.1416"))
        self.certificate["pi_upper"] = "3.14"
        with self.assertRaisesRegex(ValueError, "pi upper"):
            verify_certificate(self.certificate)

    def test_invalid_square_root_witness_is_rejected(self):
        self.certificate["sqrt_enclosures"][0]["lo"] = "2.7"
        with self.assertRaisesRegex(ValueError, "square-root enclosure"):
            verify_certificate(self.certificate)

    def test_overstated_pair_angle_is_rejected(self):
        self.certificate["angle_lower_bounds"][0]["lower"] = "1.1"
        with self.assertRaisesRegex(ValueError, "overstated angle"):
            verify_certificate(self.certificate)

    def test_missing_and_duplicate_pairs_are_rejected(self):
        for duplicate in (False, True):
            with self.subTest(duplicate=duplicate):
                data = deepcopy(self.certificate)
                if duplicate:
                    data["angle_lower_bounds"][-1] = data["angle_lower_bounds"][0]
                else:
                    data["angle_lower_bounds"].pop()
                with self.assertRaisesRegex(ValueError, "pair"):
                    verify_certificate(data)

    def test_missing_and_duplicate_orders_are_rejected(self):
        for duplicate in (False, True):
            with self.subTest(duplicate=duplicate):
                data = deepcopy(self.certificate)
                if duplicate:
                    data["orders"][-1] = data["orders"][0]
                else:
                    data["orders"].pop()
                with self.assertRaisesRegex(ValueError, "order"):
                    verify_certificate(data)

    def test_valid_but_weak_angles_do_not_prove_the_lemma(self):
        for row in self.certificate["angle_lower_bounds"]:
            row["lower"] = "0.1"
        with self.assertRaisesRegex(ValueError, "does not exclude"):
            verify_certificate(self.certificate)

    def test_missing_cyclic_class_is_rejected(self):
        self.certificate["cyclic_representatives"].pop()
        with self.assertRaisesRegex(ValueError, "cyclic representatives"):
            verify_certificate(self.certificate)

    def test_float_and_wrong_radius_inputs_are_rejected(self):
        for value in (8.303468122111490, "8.4"):
            with self.subTest(value=value):
                self.certificate["container_radius_upper"] = value
                with self.assertRaises(ValueError):
                    verify_certificate(self.certificate)

    @staticmethod
    def box():
        coords = [["-20", "20"] for _ in range(20)]
        for label, x in ((7, "-2"), (8, "2"), (9, "-1"), (10, "1")):
            coords[2 * (label - 1)] = [x, x]
            coords[2 * (label - 1) + 1] = ["-2", "0"]
        return coords

    def test_closed_halfplane_boundary_is_included(self):
        witness = halfplane_witness(self.box())
        self.assertIsNotNone(witness)
        self.assertEqual(witness["normal"], [0, -1])
        self.assertTrue(all(Fraction(x) == 0 for x in witness["projection_lower_bounds"].values()))

    def test_box_crossing_halfplane_is_not_discarded(self):
        coords = self.box()
        coords[19] = ["-2", "1"]
        self.assertIsNone(halfplane_witness(coords))

    def test_empty_coordinate_interval_is_rejected(self):
        coords = self.box()
        coords[0] = ["1", "0"]
        with self.assertRaisesRegex(ValueError, "empty coordinate"):
            halfplane_witness(coords)

    def frontier(self):
        return {"n": 10, "radii_squared": list(range(1, 11)),
                "rho": "8.303468122111490",
                "queued_boxes": [{"node": "0", "coords": self.box()}]}

    def test_frontier_closure_does_not_claim_tree_coverage(self):
        result = verify_frontier(self.frontier(), self.certificate)
        self.assertEqual(result["matched_boxes"], 1)
        self.assertFalse(result["initial_domain_coverage_verified"])

    def test_frontier_radius_outside_scope_is_rejected(self):
        data = self.frontier()
        data["rho"] = "8.4"
        with self.assertRaisesRegex(ValueError, "outside the lemma scope"):
            verify_frontier(data, self.certificate)

    def test_ancestor_and_duplicate_frontier_nodes_are_rejected(self):
        for second in ("0", "01"):
            with self.subTest(second=second):
                data = self.frontier()
                data["queued_boxes"].append({"node": second, "coords": self.box()})
                with self.assertRaisesRegex(ValueError, "ancestor node"):
                    verify_frontier(data, self.certificate)


if __name__ == "__main__":
    unittest.main()

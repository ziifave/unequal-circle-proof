import Mathlib.Data.Fin.Basic
import Mathlib.Basic.Real.Basic

namespace CirclePacking

abbrev Point := ℝ × ℝ

def distSq (p q : Point) : ℝ :=
  (p.1 - q.1)^2 + (p.2 - q.2)^2

structure Circle where
  center : Point
  radius : ℝ
  radius_nonneg : 0 ≤ radius

def Contained (R : ℝ) (c : Circle) : Prop :=
  c.radius ≤ R ∧ distSq c.center (0, 0) ≤ (R - c.radius)^2

def Separated (c d : Circle) : Prop :=
  (c.radius + d.radius)^2 ≤ distSq c.center d.center

structure Packing (n : ℕ) (R : ℝ) where
  circles : Fin n → Circle
  container_nonneg : 0 ≤ R
  contained : ∀ i, Contained R (circles i)
  separated : ∀ ⦃i j : Fin n⦄, i ≠ j → Separated (circles i) (circles j)

theorem contained_mono {R U : ℝ} {c : Circle}
    (hR : R ≤ U) (hc : Contained R c) : Contained U c := by
  rcases hc with ⟨hr, hd⟩
  refine ⟨le_trans hr hR, ?_⟩
  have hnonneg : 0 ≤ R - c.radius := by
    exact sub_nonneg.mpr hr
  have hstep : R - c.radius ≤ U - c.radius := by
    exact sub_le_sub_right hR _
  have hU : 0 ≤ U - c.radius := le_trans hnonneg hstep
  exact le_trans hd ((sq_le_sq₀ hnonneg hU).2 hstep)

def Packing.enlarge {R U : ℝ} (P : Packing n R) (hR : R ≤ U) : Packing n U where
  circles := P.circles
  container_nonneg := le_trans P.container_nonneg hR
  contained := fun i => contained_mono hR (P.contained i)
  separated := P.separated

theorem packing_enlarge {R U : ℝ} (P : Packing n R) (hR : R ≤ U) :
    Nonempty (Packing n U) :=
  ⟨P.enlarge hR⟩

end CirclePacking

import Mathlib.Basic.Real.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

namespace CirclePacking

/-!
# Certified one-dimensional root isolation

This is the abstract theorem needed by the Henneberg-DAG endpoint audit.  A
numerical certificate supplies the interval, endpoint signs, continuity, and
strict monotonicity.  Lean then assembles the existence and uniqueness claim;
the numerical generator is not trusted as a source of logical inference.
-/

theorem exists_unique_root_of_continuous_strictMonoOn
    {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hmono : StrictMonoOn f (Set.Icc a b))
    (ha : f a ≤ 0)
    (hb : 0 ≤ f b) :
    ∃! x, x ∈ Set.Icc a b ∧ f x = 0 := by
  have hzero : (0 : ℝ) ∈ Set.Icc (f a) (f b) := ⟨ha, hb⟩
  rcases intermediate_value_Icc hab hcont hzero with ⟨x, hx, hfx⟩
  refine ⟨x, ⟨hx, hfx⟩, ?_⟩
  intro y hy
  have hnot_xy : ¬ x < y := by
    intro hxy
    have hlt := hmono hx hy.1 hxy
    linarith [hy.2, hfx]
  have hnot_yx : ¬ y < x := by
    intro hyx
    have hlt := hmono hy.1 hx hyx
    linarith [hy.2, hfx]
  exact le_antisymm (le_of_not_gt hnot_xy) (le_of_not_gt hnot_yx)

/- A replayable certificate for the preceding theorem.  The fields are
   deliberately hypotheses: a producer may obtain them by interval arithmetic,
   but the logical conclusion below does not trust that producer. -/
structure RootIsolationCertificate (f : ℝ → ℝ) where
  lo : ℝ
  hi : ℝ
  lo_le_hi : lo ≤ hi
  continuous : ContinuousOn f (Set.Icc lo hi)
  strictMono : StrictMonoOn f (Set.Icc lo hi)
  left_nonpos : f lo ≤ 0
  right_nonneg : 0 ≤ f hi

theorem RootIsolationCertificate.exists_unique
    {f : ℝ → ℝ} (cert : RootIsolationCertificate f) :
    ∃! x, x ∈ Set.Icc cert.lo cert.hi ∧ f x = 0 := by
  exact exists_unique_root_of_continuous_strictMonoOn
    cert.lo_le_hi cert.continuous cert.strictMono
    cert.left_nonpos cert.right_nonneg

theorem RootIsolationCertificate.root_mem
    {f : ℝ → ℝ} (cert : RootIsolationCertificate f) :
    ∃ x, x ∈ Set.Icc cert.lo cert.hi ∧ f x = 0 := by
  rcases cert.exists_unique with ⟨x, hx, _⟩
  exact ⟨x, hx⟩

theorem RootIsolationCertificate.root_unique
    {f : ℝ → ℝ} (cert : RootIsolationCertificate f)
    {x y : ℝ}
    (hx : x ∈ Set.Icc cert.lo cert.hi ∧ f x = 0)
    (hy : y ∈ Set.Icc cert.lo cert.hi ∧ f y = 0) :
    x = y := by
  rcases cert.exists_unique with ⟨z, hz, huniq⟩
  exact (huniq x hx).trans (huniq y hy).symm

/- The certified root itself is defined by the certificate, not by a rounded
   decimal approximation.  This is the form to use for a quantity such as R₀. -/
noncomputable def RootIsolationCertificate.root
    {f : ℝ → ℝ} (cert : RootIsolationCertificate f) : ℝ :=
  Classical.choose cert.root_mem

theorem RootIsolationCertificate.root_spec
    {f : ℝ → ℝ} (cert : RootIsolationCertificate f) :
    cert.root ∈ Set.Icc cert.lo cert.hi ∧ f cert.root = 0 := by
  exact Classical.choose_spec cert.root_mem

theorem RootIsolationCertificate.root_eq_of_mem
    {f : ℝ → ℝ} (cert : RootIsolationCertificate f)
    {x : ℝ} (hx : x ∈ Set.Icc cert.lo cert.hi ∧ f x = 0) :
    x = cert.root := by
  exact cert.root_unique hx cert.root_spec

end CirclePacking

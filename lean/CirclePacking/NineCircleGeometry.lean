import CirclePacking.CornerBound
import CirclePacking.PolarAngle

namespace CirclePacking

open scoped BigOperators

noncomputable section

/-! The geometric layer used by the finite nine-circle cycle certificate.

The numerical certificate supplies, for every directed edge, a positive lower
bound on the contact angle.  This file records the two mathematical steps
which turn those bounds into an exclusion: non-overlap bounds the centre angle
from below, and a negative closed walk of angular constraints is impossible.
-/

theorem centerAngle_symm (p q : Point) :
    centerAngle p q = centerAngle q p := by
  unfold centerAngle centerCosine
  congr 1
  ring

theorem touchAngle_symm (a b d : ℝ) :
    touchAngle a b d = touchAngle b a d := by
  unfold touchAngle touchCosine
  congr 1
  ring

theorem centerAngle_polar_reverse_sub
    {a b alpha beta : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlo : 0 ≤ 2 * Real.pi - (alpha - beta))
    (hhi : 2 * Real.pi - (alpha - beta) ≤ Real.pi) :
    centerAngle (polarPoint a alpha) (polarPoint b beta) =
      2 * Real.pi - (alpha - beta) := by
  have hcos : Real.cos (alpha - beta) =
      Real.cos (2 * Real.pi - (alpha - beta)) := by
    conv_rhs => rw [Real.cos_sub]
    simp
  unfold centerAngle
  rw [centerCosine_polar ha hb, hcos]
  exact Real.arccos_cos hlo hhi

theorem polar_touch_angle_ordered_gap
    {a b d ell alpha beta : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hellpi : ell ≤ Real.pi)
    (hdelta0 : 0 ≤ beta - alpha)
    (hdelta2 : beta - alpha ≤ 2 * Real.pi)
    (hsep : d ^ 2 ≤ pointNorm
      ((polarPoint a alpha).1 - (polarPoint b beta).1,
       (polarPoint a alpha).2 - (polarPoint b beta).2) ^ 2)
    (hell : ell ≤ touchAngle a b d) :
    ell ≤ beta - alpha ∧ beta - alpha ≤ 2 * Real.pi - ell := by
  have hcenterLower :
      ell ≤ centerAngle (polarPoint a alpha) (polarPoint b beta) := by
    exact le_trans hell (touch_angle_le_center_angle ha hb
      (pointNorm_polarPoint (le_of_lt ha))
      (pointNorm_polarPoint (le_of_lt hb)) hsep)
  by_cases hsmall : beta - alpha ≤ Real.pi
  · have hcenter :
        centerAngle (polarPoint a alpha) (polarPoint b beta) = beta - alpha := by
      calc
        centerAngle (polarPoint a alpha) (polarPoint b beta) =
            centerAngle (polarPoint b beta) (polarPoint a alpha) :=
              centerAngle_symm _ _
        _ = beta - alpha := centerAngle_polar_sub hb ha hdelta0 hsmall
    constructor
    · rw [hcenter] at hcenterLower
      exact hcenterLower
    · nlinarith [Real.pi_pos]
  · have hlarge : Real.pi < beta - alpha := lt_of_not_ge hsmall
    have hwrap0 : 0 ≤ 2 * Real.pi - (beta - alpha) := by
      nlinarith
    have hwrapPi : 2 * Real.pi - (beta - alpha) ≤ Real.pi := by
      nlinarith
    have hcenter :
        centerAngle (polarPoint a alpha) (polarPoint b beta) =
          2 * Real.pi - (beta - alpha) := by
      calc
        centerAngle (polarPoint a alpha) (polarPoint b beta) =
            centerAngle (polarPoint b beta) (polarPoint a alpha) :=
              centerAngle_symm _ _
        _ = 2 * Real.pi - (beta - alpha) :=
          centerAngle_polar_reverse_sub hb ha hwrap0 hwrapPi
    constructor
    · exact le_trans hellpi (le_of_lt hlarge)
    · rw [hcenter] at hcenterLower
      linarith

theorem box_corners_certify_touch_angle
    {La Ua Lb Ub a b d ell cap : ℝ}
    (haL : La ≤ a) (haU : a ≤ Ua)
    (hbL : Lb ≤ b) (hbU : b ≤ Ub)
    (hLa : 0 < La) (hLb : 0 < Lb)
    (h00 : La ^ 2 + Lb ^ 2 - d ^ 2 ≤ cap * (2 * La * Lb))
    (h01 : La ^ 2 + Ub ^ 2 - d ^ 2 ≤ cap * (2 * La * Ub))
    (h10 : Ua ^ 2 + Lb ^ 2 - d ^ 2 ≤ cap * (2 * Ua * Lb))
    (h11 : Ua ^ 2 + Ub ^ 2 - d ^ 2 ≤ cap * (2 * Ua * Ub))
    (hell0 : 0 ≤ ell) (hellpi : ell ≤ Real.pi)
    (hcap : cap ≤ Real.cos ell) :
    ell ≤ touchAngle a b d := by
  apply certified_touch_angle_lower_bound hell0 hellpi
  exact le_trans (corner_touch_cosine_bound haL haU hbL hbU hLa hLb
    h00 h01 h10 h11) hcap

theorem separated_lower_contact_distance
    {ra rb la lb : ℝ} {p q : Point}
    (hla0 : 0 ≤ la) (hlb0 : 0 ≤ lb)
    (hlara : la ≤ ra) (hlbrb : lb ≤ rb)
    (hsep : (ra + rb) ^ 2 ≤
      pointNorm (p.1 - q.1, p.2 - q.2) ^ 2) :
    (la + lb) ^ 2 ≤ pointNorm (p.1 - q.1, p.2 - q.2) ^ 2 := by
  have hsum : 0 ≤ la + lb := add_nonneg hla0 hlb0
  have hle : la + lb ≤ ra + rb := add_le_add hlara hlbrb
  have hsumRadius : 0 ≤ ra + rb := le_trans hsum hle
  have hsq : (la + lb) ^ 2 ≤ (ra + rb) ^ 2 :=
    (sq_le_sq₀ hsum hsumRadius).2 hle
  exact hsq.trans hsep

structure NineAngularEdge (n : ℕ) where
  src : Fin n
  dst : Fin n
  lower : ℝ

def nineAngularEdgeUpper {n : ℕ} (tauUpper : ℝ)
    (e : NineAngularEdge n) : ℝ :=
  if e.src.1 < e.dst.1 then tauUpper - e.lower else -e.lower

def NineAngularChain {n : ℕ} (start : Fin n) :
    List (NineAngularEdge n) → Fin n → Prop
  | [], finish => finish = start
  | edge :: rest, finish =>
      edge.src = start ∧ NineAngularChain edge.dst rest finish

theorem nineAngularChain_telescope
    {n : ℕ} (theta : Fin n → ℝ) (start finish : Fin n)
    (edges : List (NineAngularEdge n))
    (hchain : NineAngularChain start edges finish) :
    (edges.map (fun e => theta e.dst - theta e.src)).sum =
      theta finish - theta start := by
  induction edges generalizing start finish with
  | nil =>
      simp [NineAngularChain] at hchain
      subst finish
      simp
  | cons edge rest ih =>
      simp only [NineAngularChain] at hchain
      rcases hchain with ⟨hsrc, hrest⟩
      subst start
      simp only [List.map_cons, List.sum_cons]
      rw [ih edge.dst finish hrest]
      ring

theorem negative_nine_angular_cycle_impossible
    {n : ℕ} (theta : Fin n → ℝ) (tauUpper : ℝ)
    (start : Fin n) (edges : List (NineAngularEdge n))
    (hchain : NineAngularChain start edges start)
    (hedges : ∀ e, e ∈ edges →
      theta e.dst - theta e.src ≤ nineAngularEdgeUpper tauUpper e)
    (hnegative :
      (edges.map (nineAngularEdgeUpper tauUpper)).sum < 0) : False := by
  have hsumle :
      (edges.map (fun e => theta e.dst - theta e.src)).sum ≤
        (edges.map (nineAngularEdgeUpper tauUpper)).sum := by
    apply List.sum_le_sum
    intro e he
    exact hedges e he
  have htelescope := nineAngularChain_telescope theta start start edges hchain
  simp only [sub_self] at htelescope
  rw [htelescope] at hsumle
  linarith

theorem polar_edge_respects_nine_angular_bound
    {n : ℕ} (theta : Fin n → ℝ) (tauUpper : ℝ)
    (e : NineAngularEdge n) (a b d : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hellpi : e.lower ≤ Real.pi)
    (hneq : e.src ≠ e.dst)
    (hsorted : ∀ i j : Fin n, i.1 < j.1 → theta i ≤ theta j)
    (hthetaLo : ∀ i : Fin n, 0 ≤ theta i)
    (hthetaHi : ∀ i : Fin n, theta i ≤ 2 * Real.pi)
    (hsep : d ^ 2 ≤ pointNorm
      ((polarPoint a (theta e.src)).1 - (polarPoint b (theta e.dst)).1,
       (polarPoint a (theta e.src)).2 - (polarPoint b (theta e.dst)).2) ^ 2)
    (hell : e.lower ≤ touchAngle a b d)
    (htau : 2 * Real.pi ≤ tauUpper) :
    theta e.dst - theta e.src ≤ nineAngularEdgeUpper tauUpper e := by
  by_cases hforward : e.src.1 < e.dst.1
  · have hdelta0 : 0 ≤ theta e.dst - theta e.src :=
      sub_nonneg.mpr (hsorted e.src e.dst hforward)
    have hdelta2 : theta e.dst - theta e.src ≤ 2 * Real.pi := by
      have hhi := hthetaHi e.dst
      have hlo := hthetaLo e.src
      nlinarith
    have hgap := polar_touch_angle_ordered_gap ha hb hellpi hdelta0 hdelta2
      hsep hell
    simp [nineAngularEdgeUpper, hforward]
    linarith [hgap.2, htau]
  · have hback : e.dst.1 < e.src.1 := by
      have hne : e.src.1 ≠ e.dst.1 := fun heq => hneq (Fin.ext heq)
      omega
    have hdelta0 : 0 ≤ theta e.src - theta e.dst :=
      sub_nonneg.mpr (hsorted e.dst e.src hback)
    have hdelta2 : theta e.src - theta e.dst ≤ 2 * Real.pi := by
      have hhi := hthetaHi e.src
      have hlo := hthetaLo e.dst
      nlinarith
    have hdistSymm :
        pointNorm
          ((polarPoint b (theta e.dst)).1 - (polarPoint a (theta e.src)).1,
           (polarPoint b (theta e.dst)).2 - (polarPoint a (theta e.src)).2) ^ 2 =
        pointNorm
          ((polarPoint a (theta e.src)).1 - (polarPoint b (theta e.dst)).1,
           (polarPoint a (theta e.src)).2 - (polarPoint b (theta e.dst)).2) ^ 2 := by
      rw [pointNorm_sq, pointNorm_sq]
      ring
    have hsep' : d ^ 2 ≤ pointNorm
        ((polarPoint b (theta e.dst)).1 - (polarPoint a (theta e.src)).1,
         (polarPoint b (theta e.dst)).2 - (polarPoint a (theta e.src)).2) ^ 2 := by
      rw [hdistSymm]
      exact hsep
    have htouchSymm : e.lower ≤ touchAngle b a d := by
      rw [← touchAngle_symm a b d]
      exact hell
    have hgap := polar_touch_angle_ordered_gap hb ha hellpi hdelta0 hdelta2
      hsep' htouchSymm
    have hlower : e.lower ≤ theta e.src - theta e.dst := hgap.1
    simp [nineAngularEdgeUpper, hforward]
    linarith

theorem radial_box_certificate_implies_polar_edge_bound
    {n : ℕ} (theta : Fin n → ℝ) (tauUpper : ℝ)
    (e : NineAngularEdge n)
    (La Ua Lb Ub a b cap ra rb la lb : ℝ)
    (haL : La ≤ a) (haU : a ≤ Ua)
    (hbL : Lb ≤ b) (hbU : b ≤ Ub)
    (hLa : 0 < La) (hLb : 0 < Lb)
    (hla0 : 0 ≤ la) (hlb0 : 0 ≤ lb)
    (hlara : la ≤ ra) (hlbrb : lb ≤ rb)
    (hsep : (ra + rb) ^ 2 ≤ pointNorm
      ((polarPoint a (theta e.src)).1 - (polarPoint b (theta e.dst)).1,
       (polarPoint a (theta e.src)).2 - (polarPoint b (theta e.dst)).2) ^ 2)
    (h00 : La ^ 2 + Lb ^ 2 - (la + lb) ^ 2 ≤ cap * (2 * La * Lb))
    (h01 : La ^ 2 + Ub ^ 2 - (la + lb) ^ 2 ≤ cap * (2 * La * Ub))
    (h10 : Ua ^ 2 + Lb ^ 2 - (la + lb) ^ 2 ≤ cap * (2 * Ua * Lb))
    (h11 : Ua ^ 2 + Ub ^ 2 - (la + lb) ^ 2 ≤ cap * (2 * Ua * Ub))
    (hell0 : 0 ≤ e.lower) (hellpi : e.lower ≤ Real.pi)
    (hcap : cap ≤ Real.cos e.lower)
    (hneq : e.src ≠ e.dst)
    (hsorted : ∀ i j : Fin n, i.1 < j.1 → theta i ≤ theta j)
    (hthetaLo : ∀ i : Fin n, 0 ≤ theta i)
    (hthetaHi : ∀ i : Fin n, theta i ≤ 2 * Real.pi)
    (htau : 2 * Real.pi ≤ tauUpper) :
    theta e.dst - theta e.src ≤ nineAngularEdgeUpper tauUpper e := by
  have ha : 0 < a := lt_of_lt_of_le hLa haL
  have hb : 0 < b := lt_of_lt_of_le hLb hbL
  have hsepLower : (la + lb) ^ 2 ≤ pointNorm
      ((polarPoint a (theta e.src)).1 - (polarPoint b (theta e.dst)).1,
       (polarPoint a (theta e.src)).2 - (polarPoint b (theta e.dst)).2) ^ 2 :=
    separated_lower_contact_distance hla0 hlb0 hlara hlbrb hsep
  have hangle : e.lower ≤ touchAngle a b (la + lb) :=
    box_corners_certify_touch_angle haL haU hbL hbU hLa hLb
      h00 h01 h10 h11 hell0 hellpi hcap
  exact polar_edge_respects_nine_angular_bound theta tauUpper e a b
    (la + lb) ha hb hellpi hneq hsorted hthetaLo hthetaHi hsepLower hangle htau

end
end CirclePacking

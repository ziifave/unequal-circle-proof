import CirclePacking.NineCircleTaylor
import CirclePacking.NineCircleGeometry

namespace CirclePacking

theorem nineLeafSpec_edgeAngleSpec
    {cert : NineCircleCertificate} {box : NineRadialBox}
    {edges : List NineCycleEdge} {edge : NineCycleEdge}
    (hleaf : nineLeafSpec cert box edges) (hedge : edge ∈ edges) :
    nineEdgeAngleSpec cert box edge := by
  have hall := nineLeafSpec_edges_valid cert box edges hleaf
  have hedgeValid := (List.all_eq_true.mp hall) edge hedge
  exact nineEdgeAngleValid_spec hedgeValid

theorem nineEdgeCorner_margin_of_spec
    {cert : NineCircleCertificate} {box : NineRadialBox}
    {edge : NineCycleEdge} {xy : Nat × Nat}
    (hspec : nineEdgeAngleSpec cert box edge)
    (hticks : edge.2.2 ≠ 0)
    (hmem : xy ∈ nineCornerPairs box[edge.1]! box[edge.2.1]!)
    (hx : 0 < xy.1) (hy : 0 < xy.2) :
    (nineCosineNumerator cert.radiiLower[edge.1]!
        cert.radiiLower[edge.2.1]! xy.1 xy.2 : ℝ) /
        (2 * (xy.1 : ℝ) * (xy.2 : ℝ)) +
      ((edge.2.2 : ℝ) / nineAngleScale) ^ 19 /
        ((Nat.factorial 18 : ℕ) : ℝ) <
      nineTaylorReal edge.2.2 := by
  unfold nineEdgeAngleSpec at hspec
  rcases hspec with ⟨_, _, _, _, hzero | ⟨_, _, _, hcorners⟩⟩
  · exact (hticks hzero).elim
  · have hcorner := hcorners xy hmem
    have hcornerCast :
        (nineTaylorNumerator edge.2.2 : ℝ) *
            (2 * (xy.1 : ℝ) * (xy.2 : ℝ) * nineAngleScale) >
          (nineCosineNumerator cert.radiiLower[edge.1]!
              cert.radiiLower[edge.2.1]! xy.1 xy.2 : ℝ) *
              (nineTaylorDenominator * nineAngleScale) +
            2 * (xy.1 : ℝ) * (xy.2 : ℝ) * (edge.2.2 : ℝ) ^ 19 := by
      exact_mod_cast hcorner
    have hxR : 0 < (xy.1 : ℝ) := by exact_mod_cast hx
    have hyR : 0 < (xy.2 : ℝ) := by exact_mod_cast hy
    have hdenEq : (nineTaylorDenominator : ℝ) =
        (nineAngleScale : ℝ) ^ 18 *
          ((Nat.factorial 18 : ℕ) : ℝ) := by
      simp [nineTaylorDenominator]
    have hscaleR : 0 < (nineAngleScale : ℝ) := by norm_num [nineAngleScale]
    have hdenR : 0 < (nineTaylorDenominator : ℝ) := by
      rw [hdenEq]
      exact mul_pos (pow_pos hscaleR 18) (by positivity)
    rw [hdenEq] at hdenR
    have hclear := hcornerCast
    rw [hdenEq] at hclear
    have hscaled := mul_lt_mul_of_pos_right hclear hdenR
    unfold nineTaylorReal
    rw [hdenEq]
    field_simp [ne_of_gt hxR, ne_of_gt hyR, ne_of_gt hscaleR,
      show (0 : ℝ) < (Nat.factorial 18 : ℕ) by positivity]
    nlinarith [hscaled]

theorem nineEdgeCorner_cosine_lt_of_spec
    {cert : NineCircleCertificate} {box : NineRadialBox}
    {edge : NineCycleEdge} {xy : Nat × Nat}
    (hspec : nineEdgeAngleSpec cert box edge)
    (hticks : edge.2.2 ≠ 0)
    (htickBound : edge.2.2 ≤ 314159)
    (hmem : xy ∈ nineCornerPairs box[edge.1]! box[edge.2.1]!)
    (hx : 0 < xy.1) (hy : 0 < xy.2) :
    (nineCosineNumerator cert.radiiLower[edge.1]!
        cert.radiiLower[edge.2.1]! xy.1 xy.2 : ℝ) /
        (2 * (xy.1 : ℝ) * (xy.2 : ℝ)) <
      Real.cos ((edge.2.2 : ℝ) / nineAngleScale) := by
  have hmargin := nineEdgeCorner_margin_of_spec hspec hticks hmem hx hy
  have hTaylor := nineTaylor_lower_cosine_with_error edge.2.2 htickBound
  linarith

theorem nineEdgeCorner_scaled_bound_of_spec
    {cert : NineCircleCertificate} {box : NineRadialBox}
    {edge : NineCycleEdge} {xy : Nat × Nat}
    (hspec : nineEdgeAngleSpec cert box edge)
    (hticks : edge.2.2 ≠ 0)
    (htickBound : edge.2.2 ≤ 314159)
    (hmem : xy ∈ nineCornerPairs box[edge.1]! box[edge.2.1]!)
    (hx : 0 < xy.1) (hy : 0 < xy.2)
    (hscale : 0 < (cert.scale : ℝ)) :
    ((xy.1 : ℝ) / cert.scale) ^ 2 +
        ((xy.2 : ℝ) / cert.scale) ^ 2 -
        (((cert.radiiLower[edge.1]! + cert.radiiLower[edge.2.1]!) : ℝ) /
          cert.scale) ^ 2 <
      Real.cos ((edge.2.2 : ℝ) / nineAngleScale) *
        (2 * ((xy.1 : ℝ) / cert.scale) * ((xy.2 : ℝ) / cert.scale)) := by
  have hquot := nineEdgeCorner_cosine_lt_of_spec
    hspec hticks htickBound hmem hx hy
  have hden : 0 < 2 * (xy.1 : ℝ) * (xy.2 : ℝ) := by positivity
  have hnum :
      (xy.1 : ℝ) ^ 2 + (xy.2 : ℝ) ^ 2 -
          ((cert.radiiLower[edge.1]! + cert.radiiLower[edge.2.1]!) : ℝ) ^ 2 <
        Real.cos ((edge.2.2 : ℝ) / nineAngleScale) *
          (2 * (xy.1 : ℝ) * (xy.2 : ℝ)) := by
    have hmul := (div_lt_iff₀ hden).mp hquot
    simp only [nineCosineNumerator, Int.cast_sub, Int.ofNat_eq_natCast,
      Int.cast_natCast] at hmul
    push_cast at hmul
    nlinarith [hmul]
  have hscaleSq : 0 < (cert.scale : ℝ) ^ 2 := sq_pos_of_pos hscale
  calc
    ((xy.1 : ℝ) / cert.scale) ^ 2 +
        ((xy.2 : ℝ) / cert.scale) ^ 2 -
        (((cert.radiiLower[edge.1]! + cert.radiiLower[edge.2.1]!) : ℝ) /
          cert.scale) ^ 2 =
      ((xy.1 : ℝ) ^ 2 + (xy.2 : ℝ) ^ 2 -
          ((cert.radiiLower[edge.1]! + cert.radiiLower[edge.2.1]!) : ℝ) ^ 2) /
        (cert.scale : ℝ) ^ 2 := by
          field_simp [ne_of_gt hscale]
    _ < (Real.cos ((edge.2.2 : ℝ) / nineAngleScale) *
        (2 * (xy.1 : ℝ) * (xy.2 : ℝ))) /
          (cert.scale : ℝ) ^ 2 :=
            div_lt_div_of_pos_right hnum hscaleSq
    _ = Real.cos ((edge.2.2 : ℝ) / nineAngleScale) *
        (2 * ((xy.1 : ℝ) / cert.scale) * ((xy.2 : ℝ) / cert.scale)) := by
          field_simp [ne_of_gt hscale]

theorem nineEdgeCertificate_bounds_touchAngle
    {cert : NineCircleCertificate} {box : NineRadialBox}
    {edge : NineCycleEdge} {a b : ℝ}
    (hspec : nineEdgeAngleSpec cert box edge)
    (hscale : 0 < (cert.scale : ℝ))
    (hboxAordered : box[edge.1]!.1 ≤ box[edge.1]!.2)
    (hboxBordered : box[edge.2.1]!.1 ≤ box[edge.2.1]!.2)
    (haL : (box[edge.1]!.1 : ℝ) / cert.scale ≤ a)
    (haU : a ≤ (box[edge.1]!.2 : ℝ) / cert.scale)
    (hbL : (box[edge.2.1]!.1 : ℝ) / cert.scale ≤ b)
    (hbU : b ≤ (box[edge.2.1]!.2 : ℝ) / cert.scale) :
    (edge.2.2 : ℝ) / nineAngleScale ≤
      touchAngle a b
        ((cert.radiiLower[edge.1]! + cert.radiiLower[edge.2.1]! : ℕ) /
          cert.scale) := by
  have hspec0 := hspec
  rcases hspec with ⟨_, _, _, htickBound, hangle⟩
  by_cases hzero : edge.2.2 = 0
  · rw [hzero]
    simp only [Nat.cast_zero, zero_div]
    exact Real.arccos_nonneg _
  · have hdata := hangle.resolve_left hzero
    rcases hdata with ⟨hAlo, hBlo, _, hcorners⟩
    have hticks : edge.2.2 ≠ 0 := hzero
    have hAloPos : 0 < box[edge.1]!.1 := Nat.pos_of_ne_zero hAlo
    have hBloPos : 0 < box[edge.2.1]!.1 := Nat.pos_of_ne_zero hBlo
    have hAhi : 0 < box[edge.1]!.2 := lt_of_lt_of_le hAloPos hboxAordered
    have hBhi : 0 < box[edge.2.1]!.2 := lt_of_lt_of_le hBloPos hboxBordered
    have hAloR : 0 < (box[edge.1]!.1 : ℝ) := by exact_mod_cast hAloPos
    have hAhiR : 0 < (box[edge.1]!.2 : ℝ) := by exact_mod_cast hAhi
    have hBloR : 0 < (box[edge.2.1]!.1 : ℝ) := by exact_mod_cast hBloPos
    have hBhiR : 0 < (box[edge.2.1]!.2 : ℝ) := by exact_mod_cast hBhi
    have hcorner {x y : ℕ}
        (hmem : (x, y) ∈ nineCornerPairs box[edge.1]! box[edge.2.1]!)
        (hx : 0 < x) (hy : 0 < y) :
        ((x : ℝ) / cert.scale) ^ 2 + ((y : ℝ) / cert.scale) ^ 2 -
            (((cert.radiiLower[edge.1]! + cert.radiiLower[edge.2.1]!) : ℝ) /
              cert.scale) ^ 2 ≤
          Real.cos ((edge.2.2 : ℝ) / nineAngleScale) *
            (2 * ((x : ℝ) / cert.scale) * ((y : ℝ) / cert.scale)) := by
      have hstrict := nineEdgeCorner_scaled_bound_of_spec hspec0 hticks
        htickBound hmem hx hy hscale
      exact hstrict.le
    have hmem00 : (box[edge.1]!.1, box[edge.2.1]!.1) ∈
        nineCornerPairs box[edge.1]! box[edge.2.1]! := by
      simp [nineCornerPairs]
    have hmem01 : (box[edge.1]!.1, box[edge.2.1]!.2) ∈
        nineCornerPairs box[edge.1]! box[edge.2.1]! := by
      simp [nineCornerPairs]
    have hmem10 : (box[edge.1]!.2, box[edge.2.1]!.1) ∈
        nineCornerPairs box[edge.1]! box[edge.2.1]! := by
      simp [nineCornerPairs]
    have hmem11 : (box[edge.1]!.2, box[edge.2.1]!.2) ∈
        nineCornerPairs box[edge.1]! box[edge.2.1]! := by
      simp [nineCornerPairs]
    let La : ℝ := (box[edge.1]!.1 : ℝ) / cert.scale
    let Ua : ℝ := (box[edge.1]!.2 : ℝ) / cert.scale
    let Lb : ℝ := (box[edge.2.1]!.1 : ℝ) / cert.scale
    let Ub : ℝ := (box[edge.2.1]!.2 : ℝ) / cert.scale
    let d : ℝ :=
      ((cert.radiiLower[edge.1]! + cert.radiiLower[edge.2.1]! : ℕ) : ℝ) /
        cert.scale
    have hLa : 0 < La := div_pos hAloR hscale
    have hLb : 0 < Lb := div_pos hBloR hscale
    have h00 : La ^ 2 + Lb ^ 2 - d ^ 2 ≤
        Real.cos ((edge.2.2 : ℝ) / nineAngleScale) * (2 * La * Lb) := by
      simpa [La, Lb, d] using hcorner hmem00 hAloPos hBloPos
    have h01 : La ^ 2 + Ub ^ 2 - d ^ 2 ≤
        Real.cos ((edge.2.2 : ℝ) / nineAngleScale) * (2 * La * Ub) := by
      simpa [La, Ub, d] using hcorner hmem01 hAloPos hBhi
    have h10 : Ua ^ 2 + Lb ^ 2 - d ^ 2 ≤
        Real.cos ((edge.2.2 : ℝ) / nineAngleScale) * (2 * Ua * Lb) := by
      simpa [Ua, Lb, d] using hcorner hmem10 hAhi hBloPos
    have h11 : Ua ^ 2 + Ub ^ 2 - d ^ 2 ≤
        Real.cos ((edge.2.2 : ℝ) / nineAngleScale) * (2 * Ua * Ub) := by
      simpa [Ua, Ub, d] using hcorner hmem11 hAhi hBhi
    have hell0 : 0 ≤ (edge.2.2 : ℝ) / nineAngleScale := by positivity
    have htickReal : (edge.2.2 : ℝ) ≤ 314159 := by exact_mod_cast htickBound
    have hellPi : (edge.2.2 : ℝ) / nineAngleScale ≤ Real.pi := by
      have hscaled : (edge.2.2 : ℝ) / nineAngleScale ≤ (314159 : ℝ) / 100000 := by
        rw [nineAngleScale]
        norm_num
        exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 100000)).2
          (by norm_num at htickReal ⊢; exact htickReal)
      have hpi := Real.pi_gt_d6
      have hsmall : (314159 : ℝ) / 100000 < (3141592 : ℝ) / 1000000 := by norm_num
      have hpi' : (3141592 : ℝ) / 1000000 < Real.pi := by
        norm_num at hpi ⊢
        exact hpi
      exact le_of_lt (lt_of_le_of_lt hscaled (lt_trans hsmall hpi'))
    have hcap : Real.cos ((edge.2.2 : ℝ) / nineAngleScale) ≤
        Real.cos ((edge.2.2 : ℝ) / nineAngleScale) := le_rfl
    exact box_corners_certify_touch_angle haL haU hbL hbU hLa hLb
      h00 h01 h10 h11 hell0 hellPi hcap

theorem nineAngleTick_le_pi {ticks : ℕ} (htick : ticks ≤ 314159) :
    (ticks : ℝ) / nineAngleScale ≤ Real.pi := by
  have htickR : (ticks : ℝ) ≤ 314159 := by exact_mod_cast htick
  have hpiBound : (314159 : ℝ) / 100000 < Real.pi := by
    have hpi := Real.pi_gt_d6
    norm_num at hpi ⊢
    linarith
  apply le_of_lt
  calc
    (ticks : ℝ) / nineAngleScale = (ticks : ℝ) / 100000 := by
      norm_num [nineAngleScale]
    _ ≤ (314159 : ℝ) / 100000 :=
      div_le_div_of_nonneg_right htickR (by norm_num)
    _ < Real.pi := hpiBound

theorem nineCertificateEdge_implies_angularBound
    {cert : NineCircleCertificate} {box : NineRadialBox}
    {edge : NineCycleEdge} {theta : Fin 9 → ℝ}
    {a b ra rb tauUpper : ℝ}
    (hspec : nineEdgeAngleSpec cert box edge)
    (hsrc : edge.1 < 9) (hdst : edge.2.1 < 9)
    (hscale : 0 < (cert.scale : ℝ))
    (hboxAordered : box[edge.1]!.1 ≤ box[edge.1]!.2)
    (hboxBordered : box[edge.2.1]!.1 ≤ box[edge.2.1]!.2)
    (haL : (box[edge.1]!.1 : ℝ) / cert.scale ≤ a)
    (haU : a ≤ (box[edge.1]!.2 : ℝ) / cert.scale)
    (hbL : (box[edge.2.1]!.1 : ℝ) / cert.scale ≤ b)
    (hbU : b ≤ (box[edge.2.1]!.2 : ℝ) / cert.scale)
    (ha : 0 < a) (hb : 0 < b)
    (hla : (cert.radiiLower[edge.1]! : ℝ) / cert.scale ≤ ra)
    (hlb : (cert.radiiLower[edge.2.1]! : ℝ) / cert.scale ≤ rb)
    (hsep : (ra + rb) ^ 2 ≤ pointNorm
      ((polarPoint a (theta ⟨edge.1, hsrc⟩)).1 -
          (polarPoint b (theta ⟨edge.2.1, hdst⟩)).1,
       (polarPoint a (theta ⟨edge.1, hsrc⟩)).2 -
          (polarPoint b (theta ⟨edge.2.1, hdst⟩)).2) ^ 2)
    (hsorted : ∀ i j : Fin 9, i.1 < j.1 → theta i ≤ theta j)
    (hthetaLo : ∀ i : Fin 9, 0 ≤ theta i)
    (hthetaHi : ∀ i : Fin 9, theta i ≤ 2 * Real.pi)
    (htau : 2 * Real.pi ≤ tauUpper) :
    let e : NineAngularEdge 9 :=
      ⟨⟨edge.1, hsrc⟩, ⟨edge.2.1, hdst⟩,
        (edge.2.2 : ℝ) / nineAngleScale⟩
    theta e.dst - theta e.src ≤ nineAngularEdgeUpper tauUpper e := by
  let e : NineAngularEdge 9 :=
    ⟨⟨edge.1, hsrc⟩, ⟨edge.2.1, hdst⟩,
      (edge.2.2 : ℝ) / nineAngleScale⟩
  let la : ℝ := (cert.radiiLower[edge.1]! : ℝ) / cert.scale
  let lb : ℝ := (cert.radiiLower[edge.2.1]! : ℝ) / cert.scale
  have hspec0 := hspec
  rcases hspec with ⟨_, _, hneqNat, htickBound, _⟩
  have hneq : e.src ≠ e.dst := by
    intro heq
    apply hneqNat
    exact congrArg Fin.val heq
  have hangle := nineEdgeCertificate_bounds_touchAngle hspec0 hscale
    hboxAordered hboxBordered haL haU hbL hbU
  have hcontact :
      ((cert.radiiLower[edge.1]! + cert.radiiLower[edge.2.1]! : ℕ) : ℝ) /
          cert.scale = la + lb := by
    dsimp [la, lb]
    push_cast
    ring
  have hangle' : e.lower ≤ touchAngle a b (la + lb) := by
    rw [← hcontact]
    simpa [e] using hangle
  have hla0 : 0 ≤ la := by positivity
  have hlb0 : 0 ≤ lb := by positivity
  have hanglePi : e.lower ≤ Real.pi := by
    dsimp [e]
    exact nineAngleTick_le_pi htickBound
  have hsepLower : (la + lb) ^ 2 ≤ pointNorm
      ((polarPoint a (theta e.src)).1 - (polarPoint b (theta e.dst)).1,
       (polarPoint a (theta e.src)).2 - (polarPoint b (theta e.dst)).2) ^ 2 :=
    separated_lower_contact_distance hla0 hlb0 hla hlb hsep
  exact polar_edge_respects_nine_angular_bound theta tauUpper e a b
    (la + lb) ha hb hanglePi hneq hsorted hthetaLo hthetaHi hsepLower
    hangle' htau

/-- The zero-tick edge is valid even when one centre is at the origin. For a
positive tick, the certificate itself forces both radial box lower endpoints
to be positive, so positivity follows from box membership. -/
theorem nineCertificateEdge_implies_angularBound_of_nonneg
    {cert : NineCircleCertificate} {box : NineRadialBox}
    {edge : NineCycleEdge} {theta : Fin 9 → ℝ}
    {a b ra rb tauUpper : ℝ}
    (hspec : nineEdgeAngleSpec cert box edge)
    (hsrc : edge.1 < 9) (hdst : edge.2.1 < 9)
    (hscale : 0 < (cert.scale : ℝ))
    (hboxAordered : box[edge.1]!.1 ≤ box[edge.1]!.2)
    (hboxBordered : box[edge.2.1]!.1 ≤ box[edge.2.1]!.2)
    (haL : (box[edge.1]!.1 : ℝ) / cert.scale ≤ a)
    (haU : a ≤ (box[edge.1]!.2 : ℝ) / cert.scale)
    (hbL : (box[edge.2.1]!.1 : ℝ) / cert.scale ≤ b)
    (hbU : b ≤ (box[edge.2.1]!.2 : ℝ) / cert.scale)
    (hla : (cert.radiiLower[edge.1]! : ℝ) / cert.scale ≤ ra)
    (hlb : (cert.radiiLower[edge.2.1]! : ℝ) / cert.scale ≤ rb)
    (hsep : (ra + rb) ^ 2 ≤ pointNorm
      ((polarPoint a (theta ⟨edge.1, hsrc⟩)).1 -
          (polarPoint b (theta ⟨edge.2.1, hdst⟩)).1,
       (polarPoint a (theta ⟨edge.1, hsrc⟩)).2 -
          (polarPoint b (theta ⟨edge.2.1, hdst⟩)).2) ^ 2)
    (hsorted : ∀ i j : Fin 9, i.1 < j.1 → theta i ≤ theta j)
    (hthetaLo : ∀ i : Fin 9, 0 ≤ theta i)
    (hthetaHi : ∀ i : Fin 9, theta i ≤ 2 * Real.pi)
    (htau : 2 * Real.pi ≤ tauUpper) :
    let e : NineAngularEdge 9 :=
      ⟨⟨edge.1, hsrc⟩, ⟨edge.2.1, hdst⟩,
        (edge.2.2 : ℝ) / nineAngleScale⟩
    theta e.dst - theta e.src ≤ nineAngularEdgeUpper tauUpper e := by
  let e : NineAngularEdge 9 :=
    ⟨⟨edge.1, hsrc⟩, ⟨edge.2.1, hdst⟩,
      (edge.2.2 : ℝ) / nineAngleScale⟩
  have hspec' := hspec
  rcases hspec with ⟨_, _, _, htick, hangle⟩
  by_cases hzero : edge.2.2 = 0
  · by_cases hforward : edge.1 < edge.2.1
    · have hgap : theta e.dst - theta e.src ≤ 2 * Real.pi := by
        have hd := hthetaHi e.dst
        have hs := hthetaLo e.src
        linarith
      have hgap' : theta e.dst - theta e.src ≤ tauUpper :=
        hgap.trans htau
      simpa [nineAngularEdgeUpper, e, hzero, hforward] using hgap'
    · have hbackward : edge.2.1 < edge.1 := by
        have hneq : edge.1 ≠ edge.2.1 := by
          exact hspec'.2.2.1
        omega
      have hgap : theta e.dst - theta e.src ≤ 0 := by
        have hs := hsorted e.dst e.src hbackward
        linarith
      simpa [nineAngularEdgeUpper, e, hzero, hforward] using hgap
  · have hpositive := hangle.resolve_left hzero
    rcases hpositive with ⟨hAlo, hBlo, _, _⟩
    have hAloNat : 0 < box[edge.1]!.1 := Nat.pos_of_ne_zero hAlo
    have hBloNat : 0 < box[edge.2.1]!.1 := Nat.pos_of_ne_zero hBlo
    have ha : 0 < a := by
      have hAloReal : 0 < (box[edge.1]!.1 : ℝ) := by exact_mod_cast hAloNat
      have hAloScaled : 0 < (box[edge.1]!.1 : ℝ) / cert.scale :=
        div_pos hAloReal hscale
      linarith [haL]
    have hb : 0 < b := by
      have hBloReal : 0 < (box[edge.2.1]!.1 : ℝ) := by exact_mod_cast hBloNat
      have hBloScaled : 0 < (box[edge.2.1]!.1 : ℝ) / cert.scale :=
        div_pos hBloReal hscale
      linarith [hbL]
    have hbound := nineCertificateEdge_implies_angularBound
      (a := a) (b := b) (ra := ra) (rb := rb) (theta := theta)
      hspec' hsrc hdst hscale hboxAordered hboxBordered
      haL haU hbL hbU ha hb hla hlb hsep hsorted hthetaLo hthetaHi htau
    simpa [e] using hbound

def nineCycleFin (i : ℕ) : Fin 9 :=
  ⟨i % 9, Nat.mod_lt _ (by decide)⟩

noncomputable def nineCycleAngularEdge (edge : NineCycleEdge) : NineAngularEdge 9 :=
  ⟨nineCycleFin edge.1, nineCycleFin edge.2.1,
    (edge.2.2 : ℝ) / nineAngleScale⟩

noncomputable def nineCycleAngularEdges (edges : List NineCycleEdge) :
    List (NineAngularEdge 9) :=
  edges.map nineCycleAngularEdge

noncomputable def nineCycleRealUpper (tauUpper : ℝ)
    (edge : NineCycleEdge) : ℝ :=
  if edge.1 < edge.2.1 then
    tauUpper - (edge.2.2 : ℝ) / nineAngleScale
  else -(edge.2.2 : ℝ) / nineAngleScale

def nineCycleWeightStep (total : ℤ) (edge : NineCycleEdge) : ℤ :=
  if edge.1 < edge.2.1 then
    total + Int.ofNat (ninePiUpperTicks - edge.2.2)
  else total - Int.ofNat edge.2.2

theorem nineCycleWeightTicks_eq_fold (edges : List NineCycleEdge) :
    nineCycleWeightTicks edges = edges.foldl nineCycleWeightStep 0 := by
  rfl

theorem nineCycleWeightTicks_scaled_sum
    {edges : List NineCycleEdge}
    (hbound : ∀ edge ∈ edges, edge.2.2 ≤ 314159) :
    (nineCycleWeightTicks edges : ℝ) / nineAngleScale =
      (edges.map
        (nineCycleRealUpper ((ninePiUpperTicks : ℝ) / nineAngleScale))).sum := by
  let tau : ℝ := (ninePiUpperTicks : ℝ) / nineAngleScale
  have hstep : ∀ (initial : ℤ) (edge : NineCycleEdge),
      edge.2.2 ≤ 314159 →
      (nineCycleWeightStep initial edge : ℝ) / nineAngleScale =
        (initial : ℝ) / nineAngleScale + nineCycleRealUpper tau edge := by
    intro initial edge htick
    by_cases hdir : edge.1 < edge.2.1
    · have hpiTicks : 314159 ≤ ninePiUpperTicks := by
        norm_num [ninePiUpperTicks]
      have hle : edge.2.2 ≤ ninePiUpperTicks := by omega
      have hcast : ((ninePiUpperTicks - edge.2.2 : ℕ) : ℝ) =
          (ninePiUpperTicks : ℝ) - edge.2.2 := by
        rw [Nat.cast_sub hle]
      simp only [nineCycleWeightStep, nineCycleRealUpper, ite_eq_left hdir,
        Int.cast_add, Int.ofNat_eq_natCast, Int.cast_natCast]
      rw [hcast]
      dsimp [tau]
      field_simp [show (nineAngleScale : ℝ) ≠ 0 by norm_num [nineAngleScale]]
    · simp only [nineCycleWeightStep, nineCycleRealUpper, ite_eq_right hdir,
        Int.cast_sub, Int.ofNat_eq_natCast, Int.cast_natCast]
      field_simp [show (nineAngleScale : ℝ) ≠ 0 by norm_num [nineAngleScale]]
      ring
  have hfold : ∀ (es : List NineCycleEdge) (initial : ℤ),
      (∀ edge ∈ es, edge.2.2 ≤ 314159) →
      ((es.foldl nineCycleWeightStep initial : ℤ) : ℝ) / nineAngleScale =
        (initial : ℝ) / nineAngleScale +
          (es.map (nineCycleRealUpper tau)).sum := by
    intro es
    induction es with
    | nil =>
        intro initial _
        simp
    | cons edge rest ih =>
        intro initial hall
        have hhead := hall edge (by simp)
        have hrest : ∀ e ∈ rest, e.2.2 ≤ 314159 := by
          intro e he
          exact hall e (by simp [he])
        simp only [List.foldl_cons, List.map_cons, List.sum_cons]
        rw [ih (nineCycleWeightStep initial edge) hrest]
        rw [hstep initial edge hhead]
        ring
  rw [nineCycleWeightTicks_eq_fold]
  simpa [tau] using hfold edges 0 hbound

theorem nineCycleTailSpec_to_angularChain
    {start current : ℕ} {edges : List NineCycleEdge}
    (h : nineCycleTailSpec start current edges) :
    NineAngularChain (nineCycleFin current) (nineCycleAngularEdges edges)
      (nineCycleFin start) := by
  induction edges generalizing current with
  | nil =>
      simp only [nineCycleTailSpec] at h
      subst current
      rfl
  | cons edge rest ih =>
      simp only [nineCycleTailSpec] at h
      rcases h with ⟨hcurrent, hrest⟩
      subst current
      simp only [NineAngularChain, nineCycleAngularEdges, List.map_cons]
      exact ⟨rfl, ih hrest⟩

theorem nineLeafSpec_to_angularCycle
    {cert : NineCircleCertificate} {box : NineRadialBox}
    {first : NineCycleEdge} {rest : List NineCycleEdge}
    (hleaf : nineLeafSpec cert box (first :: rest)) :
    NineAngularChain (nineCycleFin first.1)
      (nineCycleAngularEdges (first :: rest)) (nineCycleFin first.1) := by
  rcases hleaf with ⟨_, _, _, htail, _, _⟩
  simp only [nineCycleAngularEdges, List.map_cons, NineAngularChain]
  exact ⟨rfl, nineCycleTailSpec_to_angularChain htail⟩

theorem nineCycleAngularEdge_upper_eq_real
    (tauUpper : ℝ) {edge : NineCycleEdge}
    (hsrc : edge.1 < 9) (hdst : edge.2.1 < 9) :
    nineAngularEdgeUpper tauUpper (nineCycleAngularEdge edge) =
      nineCycleRealUpper tauUpper edge := by
  simp [nineAngularEdgeUpper, nineCycleRealUpper, nineCycleAngularEdge,
    nineCycleFin, Nat.mod_eq_of_lt hsrc, Nat.mod_eq_of_lt hdst]
  ring_nf

theorem nineCycleAngularEdges_upper_sum
    (tauUpper : ℝ) (edges : List NineCycleEdge)
    (hindices : ∀ edge ∈ edges, edge.1 < 9 ∧ edge.2.1 < 9) :
    ((nineCycleAngularEdges edges).map (nineAngularEdgeUpper tauUpper)).sum =
      (edges.map (nineCycleRealUpper tauUpper)).sum := by
  induction edges with
  | nil => simp [nineCycleAngularEdges]
  | cons edge rest ih =>
      have hhead := hindices edge (by simp)
      have hrest : ∀ e ∈ rest, e.1 < 9 ∧ e.2.1 < 9 := by
        intro e he
        exact hindices e (by simp [he])
      simp only [nineCycleAngularEdges, List.map_cons, List.sum_cons]
      rw [nineCycleAngularEdge_upper_eq_real tauUpper hhead.1 hhead.2]
      have htail :
          (List.map (nineAngularEdgeUpper tauUpper)
            (List.map nineCycleAngularEdge rest)).sum =
            (rest.map (nineCycleRealUpper tauUpper)).sum := by
        simpa [nineCycleAngularEdges] using ih hrest
      rw [htail]

theorem nineLeafSpec_negative_cycle_excluded
    {cert : NineCircleCertificate} {box : NineRadialBox}
    {edges : List NineCycleEdge} {theta : Fin 9 → ℝ}
    (hleaf : nineLeafSpec cert box edges)
    (hangleBound : ∀ edge ∈ edges,
      theta (nineCycleAngularEdge edge).dst -
          theta (nineCycleAngularEdge edge).src ≤
        nineAngularEdgeUpper
          ((ninePiUpperTicks : ℝ) / nineAngleScale)
          (nineCycleAngularEdge edge)) :
    False := by
  cases edges with
  | nil =>
      simp [nineLeafSpec, nineLeafSpecWithWeight] at hleaf
  | cons first rest =>
      have hmeta : ∀ edge ∈ first :: rest,
          edge.1 < 9 ∧ edge.2.1 < 9 ∧ edge.2.2 ≤ 314159 := by
        intro edge hedge
        have hs := nineLeafSpec_edgeAngleSpec hleaf hedge
        rcases hs with ⟨hsrc, hdst, _, htick, _⟩
        exact ⟨hsrc, hdst, htick⟩
      have hindices : ∀ edge ∈ first :: rest,
          edge.1 < 9 ∧ edge.2.1 < 9 := by
        intro edge hedge
        exact ⟨(hmeta edge hedge).1, (hmeta edge hedge).2.1⟩
      have hticks : ∀ edge ∈ first :: rest, edge.2.2 ≤ 314159 := by
        intro edge hedge
        exact (hmeta edge hedge).2.2
      have hleaf0 := hleaf
      have hweight : nineCycleWeightTicks (first :: rest) < 0 := by
        rcases hleaf with ⟨_, _, _, _, _, hnegative⟩
        exact hnegative
      have hcycle := nineLeafSpec_to_angularCycle hleaf0
      have hedges : ∀ edge,
          edge ∈ nineCycleAngularEdges (first :: rest) →
          theta edge.dst - theta edge.src ≤ nineAngularEdgeUpper
            ((ninePiUpperTicks : ℝ) / nineAngleScale) edge := by
        intro angularEdge hmem
        obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hmem
        subst angularEdge
        exact hangleBound source hsource
      have hsumInts := nineCycleWeightTicks_scaled_sum hticks
      have hsumEdges := nineCycleAngularEdges_upper_sum
        ((ninePiUpperTicks : ℝ) / nineAngleScale) (first :: rest) hindices
      have hweightReal :
          (nineCycleWeightTicks (first :: rest) : ℝ) / nineAngleScale < 0 := by
        have hweightCast : (nineCycleWeightTicks (first :: rest) : ℝ) < 0 :=
          by exact_mod_cast hweight
        exact div_neg_of_neg_of_pos hweightCast (by norm_num [nineAngleScale])
      have hnegative :
          ((nineCycleAngularEdges (first :: rest)).map
              (nineAngularEdgeUpper
                ((ninePiUpperTicks : ℝ) / nineAngleScale))).sum < 0 := by
        calc
          _ = ((first :: rest).map
              (nineCycleRealUpper
                ((ninePiUpperTicks : ℝ) / nineAngleScale))).sum := hsumEdges
          _ = (nineCycleWeightTicks (first :: rest) : ℝ) / nineAngleScale :=
            hsumInts.symm
          _ < 0 := hweightReal
      exact negative_nine_angular_cycle_impossible theta
        ((ninePiUpperTicks : ℝ) / nineAngleScale) (nineCycleFin first.1)
        (nineCycleAngularEdges (first :: rest)) hcycle hedges hnegative

theorem ninePiUpperTicks_is_twoPi_upper :
    2 * Real.pi ≤ (ninePiUpperTicks : ℝ) / nineAngleScale := by
  have hpi := Real.pi_lt_d4
  have hupper : 2 * Real.pi < 2 * (31416 : ℝ) / 10000 := by nlinarith
  norm_num [ninePiUpperTicks, nineAngleScale] at hupper ⊢
  linarith

theorem nineLeafSpec_excludes_polar_configuration
    {cert : NineCircleCertificate} {box : NineRadialBox}
    {edges : List NineCycleEdge} {theta radial diskRadius : Fin 9 → ℝ}
    (hleaf : nineLeafSpec cert box edges)
    (hscale : 0 < (cert.scale : ℝ))
    (hboxOrdered : ∀ i : Fin 9, box[i.1]!.1 ≤ box[i.1]!.2)
    (hradialBounds : ∀ i : Fin 9,
      (box[i.1]!.1 : ℝ) / cert.scale ≤ radial i ∧
        radial i ≤ (box[i.1]!.2 : ℝ) / cert.scale)
    (hradiusLower : ∀ i : Fin 9,
      (cert.radiiLower[i.1]! : ℝ) / cert.scale ≤ diskRadius i)
    (hseparated : ∀ i j : Fin 9, i ≠ j →
      (diskRadius i + diskRadius j) ^ 2 ≤ pointNorm
        ((polarPoint (radial i) (theta i)).1 -
            (polarPoint (radial j) (theta j)).1,
         (polarPoint (radial i) (theta i)).2 -
            (polarPoint (radial j) (theta j)).2) ^ 2)
    (hsorted : ∀ i j : Fin 9, i.1 < j.1 → theta i ≤ theta j)
    (hthetaLo : ∀ i : Fin 9, 0 ≤ theta i)
    (hthetaHi : ∀ i : Fin 9, theta i ≤ 2 * Real.pi) :
    False := by
  apply nineLeafSpec_negative_cycle_excluded hleaf
  intro edge hedge
  have hspec := nineLeafSpec_edgeAngleSpec hleaf hedge
  have hspec0 := hspec
  rcases hspec with ⟨hsrc, hdst, _, _, _⟩
  let i : Fin 9 := ⟨edge.1, hsrc⟩
  let j : Fin 9 := ⟨edge.2.1, hdst⟩
  have hneq : i ≠ j := by
    intro heq
    have hval := congrArg Fin.val heq
    exact (nineLeafSpec_edgeAngleSpec hleaf hedge).2.2.1 hval
  have hbound := nineCertificateEdge_implies_angularBound_of_nonneg
    (theta := theta) (a := radial i) (b := radial j)
    (ra := diskRadius i) (rb := diskRadius j)
    hspec0 hsrc hdst hscale (hboxOrdered i) (hboxOrdered j)
    (hradialBounds i).1 (hradialBounds i).2
    (hradialBounds j).1 (hradialBounds j).2
    (hradiusLower i) (hradiusLower j)
    (hseparated i j hneq) hsorted hthetaLo hthetaHi
    ninePiUpperTicks_is_twoPi_upper
  simpa [nineCycleAngularEdge, nineCycleFin,
    Nat.mod_eq_of_lt hsrc, Nat.mod_eq_of_lt hdst] using hbound

noncomputable def nineScaledBoxContains (scale : ℝ) (box : NineRadialBox)
    (radial : Fin 9 → ℝ) : Prop :=
  ∀ i : Fin 9,
    (box[i.1]!.1 : ℝ) / scale ≤ radial i ∧
      radial i ≤ (box[i.1]!.2 : ℝ) / scale

theorem nineSetHi_getElem
    {box : NineRadialBox} {axis cut : ℕ}
    (hsize : box.size = 9) (i : Fin 9) :
    (nineSetHi box axis cut)[i.1]! =
      if axis = i.1 then (box[i.1]!.1, cut) else box[i.1]! := by
  unfold nineSetHi
  rw [getElem!_pos (box.modify axis (fun interval => (interval.1, cut))) i.1
    (by simp [hsize])]
  rw [Array.getElem_modify (by simp [hsize])]
  have hi : i.1 < box.size := by simp [hsize]
  by_cases h : axis = i.1 <;> simp [h] <;>
    rw [← getElem!_pos box i.1 hi]

theorem nineSetLo_getElem
    {box : NineRadialBox} {axis cut : ℕ}
    (hsize : box.size = 9) (i : Fin 9) :
    (nineSetLo box axis cut)[i.1]! =
      if axis = i.1 then (cut, box[i.1]!.2) else box[i.1]! := by
  unfold nineSetLo
  rw [getElem!_pos (box.modify axis (fun interval => (cut, interval.2))) i.1
    (by simp [hsize])]
  rw [Array.getElem_modify (by simp [hsize])]
  have hi : i.1 < box.size := by simp [hsize]
  by_cases h : axis = i.1 <;> simp [h] <;>
    rw [← getElem!_pos box i.1 hi]

theorem nineSetHi_preserves_scaledBoxContains
    {scale : ℝ} {box : NineRadialBox} {radial : Fin 9 → ℝ}
    {axis cut : ℕ} (haxis : axis < 9) (hsize : box.size = 9)
    (hcontains : nineScaledBoxContains scale box radial)
    (hcut : radial ⟨axis, haxis⟩ ≤ (cut : ℝ) / scale) :
    nineScaledBoxContains scale (nineSetHi box axis cut) radial := by
  intro i
  by_cases h : i.1 = axis
  · have hi : i = ⟨axis, haxis⟩ := Fin.ext h
    subst i
    have hp := hcontains ⟨axis, haxis⟩
    have hmodify := nineSetHi_getElem (axis := axis) (cut := cut)
      hsize ⟨axis, haxis⟩
    simp only at hmodify
    rw [hmodify]
    constructor
    · exact hp.1
    · exact hcut
  · have hp := hcontains i
    have hmodify := nineSetHi_getElem (axis := axis) (cut := cut) hsize i
    have hnot : axis ≠ i.1 := fun heq => h heq.symm
    rw [ite_eq_right hnot] at hmodify
    rw [hmodify]
    exact hp

theorem nineSetLo_preserves_scaledBoxContains
    {scale : ℝ} {box : NineRadialBox} {radial : Fin 9 → ℝ}
    {axis cut : ℕ} (haxis : axis < 9) (hsize : box.size = 9)
    (hcontains : nineScaledBoxContains scale box radial)
    (hcut : (cut : ℝ) / scale ≤ radial ⟨axis, haxis⟩) :
    nineScaledBoxContains scale (nineSetLo box axis cut) radial := by
  intro i
  by_cases h : i.1 = axis
  · have hi : i = ⟨axis, haxis⟩ := Fin.ext h
    subst i
    have hp := hcontains ⟨axis, haxis⟩
    have hmodify := nineSetLo_getElem (axis := axis) (cut := cut)
      hsize ⟨axis, haxis⟩
    simp only at hmodify
    rw [hmodify]
    constructor
    · exact hcut
    · exact hp.2
  · have hp := hcontains i
    have hmodify := nineSetLo_getElem (axis := axis) (cut := cut) hsize i
    have hnot : axis ≠ i.1 := fun heq => h heq.symm
    rw [ite_eq_right hnot] at hmodify
    rw [hmodify]
    exact hp

theorem nineScaledBoxContains_ordered
    {scale : ℝ} {box : NineRadialBox} {radial : Fin 9 → ℝ}
    (hscale : 0 < scale)
    (hcontains : nineScaledBoxContains scale box radial) :
    ∀ i : Fin 9, box[i.1]!.1 ≤ box[i.1]!.2 := by
  intro i
  have hbounds := hcontains i
  have hradial : (box[i.1]!.1 : ℝ) / scale ≤
      (box[i.1]!.2 : ℝ) / scale := hbounds.1.trans hbounds.2
  have hordered : (box[i.1]!.1 : ℝ) ≤ (box[i.1]!.2 : ℝ) :=
    (div_le_div_iff_of_pos_right hscale).mp hradial
  exact_mod_cast hordered

theorem nineContractPair_lowerBound
    {scale : ℝ} {radii : Array ℕ} {box : NineRadialBox}
    {theta radial diskRadius : Fin 9 → ℝ}
    (hscale : 0 < scale)
    (hcontains : nineScaledBoxContains scale box radial)
    (hradialNonneg : ∀ i : Fin 9, 0 ≤ radial i)
    (hradiusLower : ∀ i : Fin 9,
      (radii[i.1]! : ℝ) / scale ≤ diskRadius i)
    (hseparated : ∀ i j : Fin 9, i ≠ j →
      (diskRadius i + diskRadius j) ^ 2 ≤ pointNorm
        ((polarPoint (radial i) (theta i)).1 -
            (polarPoint (radial j) (theta j)).1,
         (polarPoint (radial i) (theta i)).2 -
            (polarPoint (radial j) (theta j)).2) ^ 2)
    (i j : Fin 9) (hne : i ≠ j) :
    ((radii[i.1]! + radii[j.1]! : ℕ) : ℝ) -
        (box[j.1]!.2 : ℝ) ≤ scale * radial i := by
  have hscale0 : 0 ≤ scale := le_of_lt hscale
  have hradiusPos (k : Fin 9) : 0 ≤ diskRadius k := by
    have hnonneg : 0 ≤ (radii[k.1]! : ℝ) / scale :=
      div_nonneg (Nat.cast_nonneg _) hscale0
    exact hnonneg.trans (hradiusLower k)
  have hdist : diskRadius i + diskRadius j ≤ pointNorm
      ((polarPoint (radial i) (theta i)).1 -
          (polarPoint (radial j) (theta j)).1,
       (polarPoint (radial i) (theta i)).2 -
          (polarPoint (radial j) (theta j)).2) :=
    (sq_le_sq₀ (add_nonneg (hradiusPos i) (hradiusPos j))
      (pointNorm_nonneg _)).mp (hseparated i j hne)
  have hnormI : pointNorm (polarPoint (radial i) (theta i)) = radial i :=
    pointNorm_polarPoint (hradialNonneg i)
  have hnormJ : pointNorm (polarPoint (radial j) (theta j)) = radial j :=
    pointNorm_polarPoint (hradialNonneg j)
  have htri := pointNorm_triangle
    (polarPoint (radial i) (theta i)) (polarPoint (radial j) (theta j))
  have hcenters : diskRadius i + diskRadius j ≤ radial i + radial j := by
    rw [← hnormI, ← hnormJ]
    exact hdist.trans htri
  have hri : (radii[i.1]! : ℝ) ≤ scale * diskRadius i := by
    simpa [mul_comm] using (div_le_iff₀ hscale).mp (hradiusLower i)
  have hrj : (radii[j.1]! : ℝ) ≤ scale * diskRadius j := by
    simpa [mul_comm] using (div_le_iff₀ hscale).mp (hradiusLower j)
  have hscaledCenters :
      ((radii[i.1]! + radii[j.1]! : ℕ) : ℝ) ≤
        scale * (radial i + radial j) := by
    calc
      ((radii[i.1]! + radii[j.1]! : ℕ) : ℝ) ≤
        scale * (diskRadius i + diskRadius j) := by
        simpa [Nat.cast_add, mul_add] using add_le_add hri hrj
      _ ≤ scale * (radial i + radial j) :=
        mul_le_mul_of_nonneg_left hcenters hscale0
  have hupper := (le_div_iff₀ hscale).mp (hcontains j).2
  nlinarith

theorem nineContractCoordinate_le_scaled_radial
    {scale : ℝ} {radii : Array ℕ} {box : NineRadialBox}
    {theta radial diskRadius : Fin 9 → ℝ}
    (hscale : 0 < scale)
    (hcontains : nineScaledBoxContains scale box radial)
    (hradialNonneg : ∀ i : Fin 9, 0 ≤ radial i)
    (hradiusLower : ∀ i : Fin 9,
      (radii[i.1]! : ℝ) / scale ≤ diskRadius i)
    (hseparated : ∀ i j : Fin 9, i ≠ j →
      (diskRadius i + diskRadius j) ^ 2 ≤ pointNorm
        ((polarPoint (radial i) (theta i)).1 -
            (polarPoint (radial j) (theta j)).1,
         (polarPoint (radial i) (theta i)).2 -
            (polarPoint (radial j) (theta j)).2) ^ 2)
    (i : Fin 9) :
    (nineContractCoordinate radii box i.1 : ℝ) ≤ scale * radial i := by
  let update : ℕ → ℕ → ℕ := fun lower j =>
    if i.1 == j then lower else
      max lower (radii[i.1]! + radii[j]! - (box[j]!).2)
  have hfold : ∀ (entries : List ℕ) (initial : ℕ),
      (initial : ℝ) ≤ scale * radial i →
      (∀ j, j ∈ entries → i.1 ≠ j →
        ((radii[i.1]! + radii[j]! - (box[j]!).2 : ℕ) : ℝ) ≤
          scale * radial i) →
      ((entries.foldl update initial : ℕ) : ℝ) ≤ scale * radial i := by
    intro entries
    induction entries with
    | nil =>
        intro initial hinitial _
        simpa using hinitial
    | cons j rest ih =>
        intro initial hinitial hvalues
        simp only [List.foldl_cons]
        apply ih
        · by_cases hij : i.1 = j
          · simpa [update, hij] using hinitial
          · have hvalue := hvalues j (by simp) hij
            have hmax : ((max initial
                (radii[i.1]! + radii[j]! - (box[j]!).2) : ℕ) : ℝ) ≤
                  scale * radial i := by
              exact_mod_cast (max_le hinitial hvalue)
            simpa [update, hij] using hmax
        · intro k hk hne
          exact hvalues k (by simp [hk]) hne
  have hbaseLower : (box[i.1]!.1 : ℝ) ≤ scale * radial i := by
    simpa [mul_comm] using (div_le_iff₀ hscale).mp (hcontains i).1
  have hbaseNonneg : 0 ≤ scale * radial i :=
    mul_nonneg (le_of_lt hscale) (hradialNonneg i)
  have hbase : ((max 0 (box[i.1]!.1) : ℕ) : ℝ) ≤ scale * radial i := by
    exact_mod_cast (max_le hbaseNonneg hbaseLower)
  have hvalues : ∀ j, j ∈ List.range 9 → i.1 ≠ j →
      ((radii[i.1]! + radii[j]! - (box[j]!).2 : ℕ) : ℝ) ≤
        scale * radial i := by
    intro j hj hne
    have hjlt : j < 9 := List.mem_range.mp hj
    let jFin : Fin 9 := ⟨j, hjlt⟩
    have hneq : i ≠ jFin := by
      intro heq
      apply hne
      simpa [jFin] using congrArg Fin.val heq
    have hraw := nineContractPair_lowerBound hscale hcontains hradialNonneg
      hradiusLower hseparated i jFin hneq
    have hraw' : ((radii[i.1]! + radii[j]! : ℕ) : ℝ) -
        (box[j]!.2 : ℝ) ≤ scale * radial i := by
      simpa [jFin] using hraw
    by_cases hupper : (box[j]!).2 ≤ radii[i.1]! + radii[j]!
    · rw [Nat.cast_sub hupper]
      exact hraw'
    · have hzero : radii[i.1]! + radii[j]! - (box[j]!).2 = 0 := by
        omega
      simp [hzero]
      exact hbaseNonneg
  have hresult := hfold (List.range 9) (max 0 (box[i.1]!.1)) hbase hvalues
  simpa [nineContractCoordinate, update] using hresult

theorem nineContract_getElem
    {radii : Array ℕ} {box : NineRadialBox} (i : Fin 9) :
    (nineContract radii box)[i.1]! =
      (nineContractCoordinate radii box i.1, box[i.1]!.2) := by
  unfold nineContract
  rw [getElem!_pos _ i.1 (by simp)]
  simp

theorem nineContract_preserves_scaledBoxContains
    {scale : ℝ} {radii : Array ℕ} {box : NineRadialBox}
    {theta radial diskRadius : Fin 9 → ℝ}
    (hscale : 0 < scale)
    (hcontains : nineScaledBoxContains scale box radial)
    (hradialNonneg : ∀ i : Fin 9, 0 ≤ radial i)
    (hradiusLower : ∀ i : Fin 9,
      (radii[i.1]! : ℝ) / scale ≤ diskRadius i)
    (hseparated : ∀ i j : Fin 9, i ≠ j →
      (diskRadius i + diskRadius j) ^ 2 ≤ pointNorm
        ((polarPoint (radial i) (theta i)).1 -
            (polarPoint (radial j) (theta j)).1,
         (polarPoint (radial i) (theta i)).2 -
            (polarPoint (radial j) (theta j)).2) ^ 2) :
    nineScaledBoxContains scale (nineContract radii box) radial := by
  intro i
  have hget := nineContract_getElem (radii := radii) (box := box) i
  rw [hget]
  constructor
  · have hcoordinate := nineContractCoordinate_le_scaled_radial
      hscale hcontains hradialNonneg hradiusLower hseparated i
    have hcoordinate' : (nineContractCoordinate radii box i.1 : ℝ) ≤
        radial i * scale := by
      simpa [mul_comm] using hcoordinate
    exact (div_le_iff₀ hscale).2 hcoordinate'
  · exact (hcontains i).2

theorem nineReplayTree_excludes_scaled_configuration
    {cert : NineCircleCertificate} {tree : NineCycleTree}
    {box : NineRadialBox} {theta radial diskRadius : Fin 9 → ℝ}
    (htree : nineReplayTreeSpec cert tree box)
    (hsize : box.size = 9)
    (hscale : 0 < (cert.scale : ℝ))
    (hcontains : nineScaledBoxContains (cert.scale : ℝ) box radial)
    (hradialNonneg : ∀ i : Fin 9, 0 ≤ radial i)
    (hradiusLower : ∀ i : Fin 9,
      (cert.radiiLower[i.1]! : ℝ) / cert.scale ≤ diskRadius i)
    (hseparated : ∀ i j : Fin 9, i ≠ j →
      (diskRadius i + diskRadius j) ^ 2 ≤ pointNorm
        ((polarPoint (radial i) (theta i)).1 -
            (polarPoint (radial j) (theta j)).1,
         (polarPoint (radial i) (theta i)).2 -
            (polarPoint (radial j) (theta j)).2) ^ 2)
    (hsorted : ∀ i j : Fin 9, i.1 < j.1 → theta i ≤ theta j)
    (hthetaLo : ∀ i : Fin 9, 0 ≤ theta i)
    (hthetaHi : ∀ i : Fin 9, theta i ≤ 2 * Real.pi) :
    False := by
  have hcontractor : ∀ currentBox,
      nineScaledBoxContains (cert.scale : ℝ) currentBox radial →
        nineScaledBoxContains (cert.scale : ℝ)
          (nineContract cert.radiiLower currentBox) radial := by
    intro currentBox hcurrent
    exact nineContract_preserves_scaledBoxContains hscale hcurrent
      hradialNonneg hradiusLower hseparated
  induction tree generalizing box with
  | leaf edges =>
      change nineLeafSpec cert (nineContract cert.radiiLower box) edges at htree
      have hleafContains := hcontractor box hcontains
      exact nineLeafSpec_excludes_polar_configuration htree hscale
        (nineScaledBoxContains_ordered hscale hleafContains)
        hleafContains
        hradiusLower hseparated hsorted hthetaLo hthetaHi
  | split axis cut left right ihLeft ihRight =>
      simp only [nineReplayTreeSpec] at htree
      rcases htree with ⟨haxis, hcutLo, hcutHi, hleft, hright⟩
      have hcontracted := hcontractor box hcontains
      have hcontractedSize : (nineContract cert.radiiLower box).size = 9 := by
        simp [nineContract]
      have hleftSize : (nineSetHi (nineContract cert.radiiLower box) axis cut).size = 9 := by
        simpa [nineSetHi] using hcontractedSize
      have hrightSize : (nineSetLo (nineContract cert.radiiLower box) axis cut).size = 9 := by
        simpa [nineSetLo] using hcontractedSize
      by_cases hleftSide : radial ⟨axis, haxis⟩ ≤ (cut : ℝ) / cert.scale
      · have hleftContains := nineSetHi_preserves_scaledBoxContains haxis
          hcontractedSize hcontracted hleftSide
        exact ihLeft hleft hleftSize hleftContains
      · have hrightSide : (cut : ℝ) / cert.scale ≤ radial ⟨axis, haxis⟩ :=
          le_of_not_ge hleftSide
        have hrightContains := nineSetLo_preserves_scaledBoxContains haxis
          hcontractedSize hcontracted hrightSide
        exact ihRight hright hrightSize hrightContains

end CirclePacking

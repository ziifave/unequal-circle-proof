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

end CirclePacking

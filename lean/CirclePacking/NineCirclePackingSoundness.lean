import CirclePacking.Basic
import CirclePacking.SevenNineCoverage
import CirclePacking.NineCircleCertificateSoundness
import CirclePacking.NineCircleCertificate
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

namespace CirclePacking

noncomputable section

/-- Counterclockwise rotation of a centre point by an angle `φ`. -/
def rotatePoint (φ : ℝ) (p : Point) : Point :=
  (Real.cos φ * p.1 - Real.sin φ * p.2,
   Real.sin φ * p.1 + Real.cos φ * p.2)

theorem rotatePoint_zero (φ : ℝ) : rotatePoint φ (0, 0) = (0, 0) := by
  simp [rotatePoint]

theorem rotatePoint_distSq (φ : ℝ) (p q : Point) :
    distSq (rotatePoint φ p) (rotatePoint φ q) = distSq p q := by
  unfold distSq rotatePoint
  nlinarith [Real.sin_sq_add_cos_sq φ]

theorem rotatePoint_pointNorm (φ : ℝ) (p : Point) :
    pointNorm (rotatePoint φ p) = pointNorm p := by
  have hnormSq :
      (rotatePoint φ p).1 ^ 2 + (rotatePoint φ p).2 ^ 2 =
        p.1 ^ 2 + p.2 ^ 2 := by
    dsimp [rotatePoint]
    nlinarith [Real.sin_sq_add_cos_sq φ]
  change Real.sqrt ((rotatePoint φ p).1 ^ 2 +
    (rotatePoint φ p).2 ^ 2) = Real.sqrt (p.1 ^ 2 + p.2 ^ 2)
  rw [hnormSq]

theorem rotatePoint_polarPoint (φ r θ : ℝ) :
    rotatePoint φ (polarPoint r θ) = polarPoint r (θ + φ) := by
  simp [rotatePoint, polarPoint, Real.cos_add, Real.sin_add]
  constructor <;> ring

/-- Rotating every centre preserves all packing constraints. -/
def Packing.rotate {n : ℕ} {R : ℝ} (P : Packing n R) (φ : ℝ) : Packing n R where
  circles i :=
    { center := rotatePoint φ (P.circles i).center
      radius := (P.circles i).radius
      radius_nonneg := (P.circles i).radius_nonneg }
  container_nonneg := P.container_nonneg
  contained i := by
    rcases P.contained i with ⟨hradius, hcenter⟩
    refine ⟨hradius, ?_⟩
    change distSq (rotatePoint φ (P.circles i).center) (0, 0) ≤ _
    rw [← rotatePoint_zero φ, rotatePoint_distSq]
    exact hcenter
  separated := by
    intro i j hij
    change ((P.circles i).radius + (P.circles j).radius) ^ 2 ≤
      distSq (rotatePoint φ (P.circles i).center)
        (rotatePoint φ (P.circles j).center)
    rw [rotatePoint_distSq]
    exact P.separated hij

theorem Packing.rotate_anchor_center {n : ℕ} {R : ℝ}
    (P : Packing n R) (φ : ℝ) (i : Fin n)
    (hcenter : (P.circles i).center = (0, 0)) :
    ((P.rotate φ).circles i).center = (0, 0) := by
  simp [Packing.rotate, hcenter, rotatePoint_zero]

def pointPolarAngle (p : Point) : ℝ :=
  let z : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * Complex.I
  let angle := Complex.arg z
  if 0 ≤ angle then angle else angle + 2 * Real.pi

theorem pointPolarAngle_representation (p : Point) :
    0 ≤ pointPolarAngle p ∧ pointPolarAngle p ≤ 2 * Real.pi ∧
      polarPoint (pointNorm p) (pointPolarAngle p) = p := by
  let z : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * Complex.I
  have hnorm : pointNorm p = ‖z‖ := by
    dsimp [pointNorm, z]
    rw [Complex.norm_def, Complex.normSq_add_mul_I]
  have hlo : 0 ≤ pointPolarAngle p := by
    unfold pointPolarAngle
    dsimp
    split_ifs with h
    · exact h
    · have harg := Complex.neg_pi_lt_arg z
      nlinarith [Real.pi_pos]
  have hhi : pointPolarAngle p ≤ 2 * Real.pi := by
    unfold pointPolarAngle
    dsimp
    split_ifs with h
    · nlinarith [Complex.arg_le_pi z, Real.pi_pos]
    · have hneg : Complex.arg z < 0 := lt_of_not_ge h
      linarith
  have hcos : pointNorm p * Real.cos (pointPolarAngle p) = p.1 := by
    unfold pointPolarAngle
    dsimp
    split_ifs with h
    · rw [hnorm]
      simpa [z] using Complex.norm_mul_cos_arg z
    · rw [Real.cos_add_two_pi, hnorm]
      simpa [z] using Complex.norm_mul_cos_arg z
  have hsin : pointNorm p * Real.sin (pointPolarAngle p) = p.2 := by
    unfold pointPolarAngle
    dsimp
    split_ifs with h
    · rw [hnorm]
      simpa [z] using Complex.norm_mul_sin_arg z
    · rw [Real.sin_add_two_pi, hnorm]
      simpa [z] using Complex.norm_mul_sin_arg z
  have hpolar : polarPoint (pointNorm p) (pointPolarAngle p) = p := by
    apply Prod.ext
    · simpa [polarPoint] using hcos
    · simpa [polarPoint] using hsin
  exact ⟨hlo, hhi, hpolar⟩

/-- Angle in `[0, 2π]` measured from a chosen angular origin. -/
def angleFromOrigin (origin angle : ℝ) : ℝ :=
  if origin ≤ angle then angle - origin else angle - origin + 2 * Real.pi

theorem angleFromOrigin_bounds {origin angle : ℝ}
    (horiginLo : 0 ≤ origin) (horiginHi : origin ≤ 2 * Real.pi)
    (hangleLo : 0 ≤ angle) (hangleHi : angle ≤ 2 * Real.pi) :
    0 ≤ angleFromOrigin origin angle ∧
      angleFromOrigin origin angle ≤ 2 * Real.pi := by
  unfold angleFromOrigin
  split_ifs with h
  · constructor <;> nlinarith
  · constructor <;> nlinarith

theorem polarPoint_angleFromOrigin (r origin angle : ℝ) :
    polarPoint r (angleFromOrigin origin angle) =
      polarPoint r (angle - origin) := by
  unfold angleFromOrigin
  split_ifs with h
  · simp
  · have hsum : angle - origin + 2 * Real.pi =
        (angle - origin) + 2 * Real.pi := by ring
    rw [hsum]
    simp [polarPoint, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem pointNorm_le_container {R : ℝ} {c : Circle}
    (hcontained : Contained R c) :
    pointNorm c.center ≤ R - c.radius := by
  rcases hcontained with ⟨hradius, hcenter⟩
  have hsquare : pointNorm c.center ^ 2 ≤ (R - c.radius) ^ 2 := by
    rw [pointNorm_sq]
    simpa [distSq] using hcenter
  exact (sq_le_sq₀ (pointNorm_nonneg _) (sub_nonneg.mpr hradius)).mp hsquare

theorem nineInitialBox_getElem
    {cert : NineCircleCertificate} (hsize : cert.radiiLower.size = 9)
    (i : Fin 9) :
    (nineInitialBox cert)[i.1]! =
      (0, cert.radiusUpper - cert.radiiLower[i.1]!) := by
  unfold nineInitialBox
  rw [getElem!_pos _ i.1 (by simp [hsize])]
  have hi : i.1 < cert.radiiLower.size := by simpa [hsize] using i.isLt
  rw [getElem!_pos cert.radiiLower i.1 hi]
  simp

theorem nineCertificate_radiusLower_of_spec
    {cert : NineCircleCertificate}
    (hspec : nineCertificateRadiiSpec cert)
    (hscale : 0 < (cert.scale : ℝ))
    (i : Fin 9) {r : ℝ} (hr : 0 ≤ r)
    (hradiusSq : r ^ 2 = (cert.diskLabels[i.1]! : ℝ)) :
    (cert.radiiLower[i.1]! : ℝ) / cert.scale ≤ r := by
  unfold nineCertificateRadiiSpec at hspec
  rcases hspec with ⟨_, _, hall⟩
  have hrow := (List.all_eq_true.mp hall) i.1
    (List.mem_range.mpr i.isLt)
  have hdata : 2 ≤ cert.diskLabels[i.1]! ∧
      cert.diskLabels[i.1]! ≤ 10 ∧
      cert.radiiLower[i.1]! ^ 2 ≤
        cert.diskLabels[i.1]! * cert.scale ^ 2 := by
    simpa using of_decide_eq_true hrow
  have hlowerSq : (cert.radiiLower[i.1]! : ℝ) ^ 2 ≤
      (cert.diskLabels[i.1]! : ℝ) * (cert.scale : ℝ) ^ 2 := by
    exact_mod_cast hdata.2.2
  have hsq : ((cert.radiiLower[i.1]! : ℝ) / cert.scale) ^ 2 ≤ r ^ 2 := by
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hscale)).2
    simpa [hradiusSq] using hlowerSq
  have hlowerNonneg : 0 ≤ (cert.radiiLower[i.1]! : ℝ) / cert.scale :=
    div_nonneg (Nat.cast_nonneg _) (le_of_lt hscale)
  exact (sq_le_sq₀ hlowerNonneg hr).mp hsq

theorem nineCertificate_label_bounds_of_spec
    {cert : NineCircleCertificate}
    (hspec : nineCertificateRadiiSpec cert) (i : Fin 9) :
    2 ≤ cert.diskLabels[i.1]! ∧ cert.diskLabels[i.1]! ≤ 10 := by
  unfold nineCertificateRadiiSpec at hspec
  rcases hspec with ⟨_, _, hall⟩
  have hrow := (List.all_eq_true.mp hall) i.1
    (List.mem_range.mpr i.isLt)
  have hdata : 2 ≤ cert.diskLabels[i.1]! ∧
      cert.diskLabels[i.1]! ≤ 10 ∧
      cert.radiiLower[i.1]! ^ 2 ≤
        cert.diskLabels[i.1]! * cert.scale ^ 2 := by
    simpa using of_decide_eq_true hrow
  exact ⟨hdata.1, hdata.2.1⟩

/-- A packing described in any explicit normalized polar frame is excluded
when its polar data follow the certificate's prescribed cyclic order.  This
form is useful after rotating the coordinate frame: the angle coordinates
need not be obtained from `Complex.arg`. -/
theorem nineCertificate_excludes_polar_order
    {cert : NineCircleCertificate} {R : ℝ}
    (hcert : nineCertificateSpec cert)
    (P : Packing 10 R)
    (anchor : Fin 10) (index : Fin 9 → Fin 10)
    (hindexInjective : Function.Injective index)
    (hindexAvoidsAnchor : ∀ i : Fin 9, index i ≠ anchor)
    (hanchorCenter : (P.circles anchor).center = (0, 0))
    (hanchorRadius : 0 < (P.circles anchor).radius)
    (hcontainer : R ≤ (cert.radiusUpper : ℝ) / cert.scale)
    (hradiusSq : ∀ i : Fin 9,
      (P.circles (index i)).radius ^ 2 =
        (cert.diskLabels[i.1]! : ℝ))
    (radial theta : Fin 9 → ℝ)
    (hradial : ∀ i : Fin 9,
      radial i = pointNorm (P.circles (index i)).center)
    (hpolar : ∀ i : Fin 9,
      (P.circles (index i)).center = polarPoint (radial i) (theta i))
    (hthetaLo : ∀ i : Fin 9, 0 ≤ theta i)
    (hthetaHi : ∀ i : Fin 9, theta i ≤ 2 * Real.pi)
    (horder : ∀ i j : Fin 9, i.1 < j.1 →
      theta i ≤ theta j) :
    False := by
  rcases hcert with ⟨hscaleNat, _, hradiiSpec, htree⟩
  have hradiiData := hradiiSpec
  rcases hradiiSpec with ⟨_, hradiiSize, _⟩
  have hscale : 0 < (cert.scale : ℝ) := by exact_mod_cast hscaleNat
  have hradiusLower : ∀ i : Fin 9,
      (cert.radiiLower[i.1]! : ℝ) / cert.scale ≤
        (P.circles (index i)).radius := by
    intro i
    exact nineCertificate_radiusLower_of_spec hradiiData hscale i
      (P.circles (index i)).radius_nonneg (hradiusSq i)
  have hrootSize : (nineInitialBox cert).size = 9 := by
    simpa [nineInitialBox] using hradiiSize
  have hradialPos : ∀ i : Fin 9, 0 < radial i := by
    intro i
    have hanchorNe : anchor ≠ index i := Ne.symm (hindexAvoidsAnchor i)
    have hsep := P.separated hanchorNe
    dsimp [Separated] at hsep
    rw [hanchorCenter] at hsep
    have hsq :
        ((P.circles anchor).radius + (P.circles (index i)).radius) ^ 2 ≤
          pointNorm (P.circles (index i)).center ^ 2 := by
      rw [pointNorm_sq]
      simpa [Separated, distSq] using hsep
    have hsumNonneg :
        0 ≤ (P.circles anchor).radius + (P.circles (index i)).radius :=
      add_nonneg (P.circles anchor).radius_nonneg
        (P.circles (index i)).radius_nonneg
    have hsumLower :=
      (sq_le_sq₀ hsumNonneg (pointNorm_nonneg _)).mp hsq
    have hsumPos :
        0 < (P.circles anchor).radius + (P.circles (index i)).radius :=
      add_pos_of_pos_of_nonneg hanchorRadius
        (P.circles (index i)).radius_nonneg
    rw [hradial i]
    exact lt_of_lt_of_le hsumPos hsumLower
  have hcontains :
      nineScaledBoxContains (cert.scale : ℝ) (nineInitialBox cert) radial := by
    intro i
    have hroot := nineInitialBox_getElem hradiiSize i
    rw [hroot]
    constructor
    · have hradialNonneg : 0 ≤ radial i := by
        rw [hradial i]
        exact pointNorm_nonneg _
      simpa using hradialNonneg
    · have hcenterBound :
        radial i ≤ R - (P.circles (index i)).radius := by
        rw [hradial i]
        exact pointNorm_le_container (P.contained (index i))
      have hupperDiv :
          radial i + (cert.radiiLower[i.1]! : ℝ) / cert.scale ≤
            (cert.radiusUpper : ℝ) / cert.scale := by
        calc
          radial i + (cert.radiiLower[i.1]! : ℝ) / cert.scale ≤
              (R - (P.circles (index i)).radius) +
                (P.circles (index i)).radius :=
            add_le_add hcenterBound (hradiusLower i)
          _ = R := by ring
          _ ≤ (cert.radiusUpper : ℝ) / cert.scale := hcontainer
      have hupperDiv' :
          radial i ≤ (cert.radiusUpper : ℝ) / cert.scale -
            (cert.radiiLower[i.1]! : ℝ) / cert.scale := by
        linarith
      have hupperDiv'' :
          radial i ≤ ((cert.radiusUpper : ℝ) -
            (cert.radiiLower[i.1]! : ℝ)) / cert.scale := by
        rw [sub_div]
        exact hupperDiv'
      have hradialNatLE : cert.radiiLower[i.1]! ≤ cert.radiusUpper := by
        have hratio :
            (cert.radiiLower[i.1]! : ℝ) / cert.scale ≤
              (cert.radiusUpper : ℝ) / cert.scale := by
          calc
            (cert.radiiLower[i.1]! : ℝ) / cert.scale ≤
                (P.circles (index i)).radius := hradiusLower i
            _ ≤ R := (P.contained (index i)).1
            _ ≤ (cert.radiusUpper : ℝ) / cert.scale := hcontainer
        exact_mod_cast (div_le_div_iff_of_pos_right hscale).mp hratio
      have hupperDivNat :
          radial i ≤ ((cert.radiusUpper - cert.radiiLower[i.1]! : ℕ) : ℝ) /
            cert.scale := by
        rw [Nat.cast_sub hradialNatLE]
        exact hupperDiv''
      exact hupperDivNat
  have hseparated : ∀ i j : Fin 9, i ≠ j →
      ((P.circles (index i)).radius + (P.circles (index j)).radius) ^ 2 ≤
        pointNorm
          ((polarPoint (radial i) (theta i)).1 -
              (polarPoint (radial j) (theta j)).1,
           (polarPoint (radial i) (theta i)).2 -
              (polarPoint (radial j) (theta j)).2) ^ 2 := by
    intro i j hij
    have hindexNe : index i ≠ index j := fun heq => hij (hindexInjective heq)
    have hpack := P.separated hindexNe
    dsimp [Separated] at hpack
    rw [hpolar i, hpolar j] at hpack
    rw [pointNorm_sq]
    simpa [Separated, distSq] using hpack
  have hsorted : ∀ i j : Fin 9, i.1 < j.1 → theta i ≤ theta j := by
    exact horder
  exact nineReplayTree_excludes_scaled_configuration htree hrootSize hscale
    hcontains hradialPos hradiusLower hseparated hsorted hthetaLo hthetaHi

/-- The standard `Complex.arg` coordinate choice is a specialization of the
explicit-polar theorem. -/
theorem nineCertificate_excludes_packing_order
    {cert : NineCircleCertificate} {R : ℝ}
    (hcert : nineCertificateSpec cert)
    (P : Packing 10 R)
    (anchor : Fin 10) (index : Fin 9 → Fin 10)
    (hindexInjective : Function.Injective index)
    (hindexAvoidsAnchor : ∀ i : Fin 9, index i ≠ anchor)
    (hanchorCenter : (P.circles anchor).center = (0, 0))
    (hanchorRadius : 0 < (P.circles anchor).radius)
    (hcontainer : R ≤ (cert.radiusUpper : ℝ) / cert.scale)
    (hradiusSq : ∀ i : Fin 9,
      (P.circles (index i)).radius ^ 2 =
        (cert.diskLabels[i.1]! : ℝ))
    (horder : ∀ i j : Fin 9, i.1 < j.1 →
      pointPolarAngle (P.circles (index i)).center ≤
        pointPolarAngle (P.circles (index j)).center) :
    False := by
  let radial : Fin 9 → ℝ := fun i =>
    pointNorm (P.circles (index i)).center
  let theta : Fin 9 → ℝ := fun i =>
    pointPolarAngle (P.circles (index i)).center
  have hpolar : ∀ i : Fin 9,
      (P.circles (index i)).center = polarPoint (radial i) (theta i) := by
    intro i
    have hrep := pointPolarAngle_representation (P.circles (index i)).center
    simpa [radial, theta] using hrep.2.2.symm
  have hthetaLo : ∀ i : Fin 9, 0 ≤ theta i := by
    intro i
    exact (pointPolarAngle_representation (P.circles (index i)).center).1
  have hthetaHi : ∀ i : Fin 9, theta i ≤ 2 * Real.pi := by
    intro i
    exact (pointPolarAngle_representation (P.circles (index i)).center).2.1
  exact nineCertificate_excludes_polar_order hcert P anchor index
    hindexInjective hindexAvoidsAnchor hanchorCenter hanchorRadius hcontainer
    hradiusSq radial theta (by intro i; rfl) hpolar hthetaLo hthetaHi (by
      simpa [theta] using horder)

/-- Exclusion is independent of the absolute angle origin. The hypothesis
states that the certificate order is cyclically increasing when measured from
the first certificate slot; the packing is rotated so that this order becomes
an ordinary increasing order in `[0, 2π]`. -/
theorem nineCertificate_excludes_cyclic_packing_order
    {cert : NineCircleCertificate} {R : ℝ}
    (hcert : nineCertificateSpec cert)
    (P : Packing 10 R)
    (anchor : Fin 10) (index : Fin 9 → Fin 10)
    (hindexInjective : Function.Injective index)
    (hindexAvoidsAnchor : ∀ i : Fin 9, index i ≠ anchor)
    (hanchorCenter : (P.circles anchor).center = (0, 0))
    (hanchorRadius : 0 < (P.circles anchor).radius)
    (hcontainer : R ≤ (cert.radiusUpper : ℝ) / cert.scale)
    (hradiusSq : ∀ i : Fin 9,
      (P.circles (index i)).radius ^ 2 =
        (cert.diskLabels[i.1]! : ℝ))
    (hcyclic : ∀ i j : Fin 9, i.1 < j.1 →
      angleFromOrigin
          (pointPolarAngle (P.circles (index (0 : Fin 9))).center)
          (pointPolarAngle (P.circles (index i)).center) ≤
        angleFromOrigin
          (pointPolarAngle (P.circles (index (0 : Fin 9))).center)
          (pointPolarAngle (P.circles (index j)).center)) :
    False := by
  let origin := pointPolarAngle (P.circles (index (0 : Fin 9))).center
  let φ := -origin
  let P' := P.rotate φ
  let radial : Fin 9 → ℝ := fun i =>
    pointNorm (P.circles (index i)).center
  let theta : Fin 9 → ℝ := fun i =>
    angleFromOrigin origin
      (pointPolarAngle (P.circles (index i)).center)
  have horigin :=
    pointPolarAngle_representation (P.circles (index (0 : Fin 9))).center
  have hradial : ∀ i : Fin 9,
      radial i = pointNorm (P'.circles (index i)).center := by
    intro i
    change pointNorm (P.circles (index i)).center =
      pointNorm (rotatePoint φ (P.circles (index i)).center)
    exact (rotatePoint_pointNorm φ _).symm
  have hpolar : ∀ i : Fin 9,
      (P'.circles (index i)).center = polarPoint (radial i) (theta i) := by
    intro i
    let p := (P.circles (index i)).center
    have hrep := pointPolarAngle_representation p
    change rotatePoint φ p =
      polarPoint (pointNorm p)
        (angleFromOrigin origin (pointPolarAngle p))
    calc
      rotatePoint φ p =
          rotatePoint φ (polarPoint (pointNorm p) (pointPolarAngle p)) := by
            exact (congrArg (rotatePoint φ) hrep.2.2).symm
      _ = polarPoint (pointNorm p) (pointPolarAngle p + φ) :=
        rotatePoint_polarPoint φ _ _
      _ = polarPoint (pointNorm p) (pointPolarAngle p - origin) := by
        congr 1
      _ = polarPoint (pointNorm p)
          (angleFromOrigin origin (pointPolarAngle p)) :=
        (polarPoint_angleFromOrigin _ _ _).symm
  have hthetaLo : ∀ i : Fin 9, 0 ≤ theta i := by
    intro i
    have hi := pointPolarAngle_representation
      (P.circles (index i)).center
    exact (angleFromOrigin_bounds horigin.1 horigin.2.1 hi.1 hi.2.1).1
  have hthetaHi : ∀ i : Fin 9, theta i ≤ 2 * Real.pi := by
    intro i
    have hi := pointPolarAngle_representation
      (P.circles (index i)).center
    exact (angleFromOrigin_bounds horigin.1 horigin.2.1 hi.1 hi.2.1).2
  have hanchorCenter' : (P'.circles anchor).center = (0, 0) := by
    exact Packing.rotate_anchor_center P φ anchor hanchorCenter
  have hradiusSq' : ∀ i : Fin 9,
      (P'.circles (index i)).radius ^ 2 =
        (cert.diskLabels[i.1]! : ℝ) := by
    intro i
    simpa [P', Packing.rotate] using hradiusSq i
  have horder : ∀ i j : Fin 9, i.1 < j.1 → theta i ≤ theta j := by
    intro i j hij
    exact hcyclic i j hij
  exact nineCertificate_excludes_polar_order hcert P' anchor index
    hindexInjective hindexAvoidsAnchor hanchorCenter' hanchorRadius hcontainer
    hradiusSq' radial theta hradial hpolar hthetaLo hthetaHi horder

/-- Specialized interface for the usual ten-circle radius assignment
`radius(k)^2 = k + 1`. The caller supplies the embedding of certificate slots
into those labels and the asserted cyclic order; the certificate's own radius
lower bounds then provide the geometric inequalities automatically. -/
theorem nineCertificate_excludes_standard_packing_order
    {cert : NineCircleCertificate} {R : ℝ}
    (hcert : nineCertificateSpec cert)
    (P : Packing 10 R)
    (index : Fin 9 → Fin 10)
    (hindexInjective : Function.Injective index)
    (hindexLabel : ∀ i : Fin 9,
      (index i).1 + 1 = cert.diskLabels[i.1]!)
    (hstandardRadius : ∀ k : Fin 10,
      (P.circles k).radius ^ 2 = ((k.1 + 1 : ℕ) : ℝ))
    (hanchorCenter : (P.circles (0 : Fin 10)).center = (0, 0))
    (hcontainer : R ≤ (cert.radiusUpper : ℝ) / cert.scale)
    (horder : ∀ i j : Fin 9, i.1 < j.1 →
      pointPolarAngle (P.circles (index i)).center ≤
        pointPolarAngle (P.circles (index j)).center) :
    False := by
  have hcertFull := hcert
  rcases hcert with ⟨_, _, hradiiSpec, _⟩
  have hlabelBounds := nineCertificate_label_bounds_of_spec hradiiSpec
  have hindexAvoidsAnchor : ∀ i : Fin 9, index i ≠ (0 : Fin 10) := by
    intro i heq
    have hval := congrArg Fin.val heq
    have hlower := (hlabelBounds i).1
    have hlabel := hindexLabel i
    simp at hval
    omega
  have hanchorRadius : 0 < (P.circles (0 : Fin 10)).radius := by
    have hsq := hstandardRadius (0 : Fin 10)
    have hnonneg := (P.circles (0 : Fin 10)).radius_nonneg
    norm_num at hsq
    rcases hsq with hsq | hsq <;> nlinarith
  have hradiusSq : ∀ i : Fin 9,
      (P.circles (index i)).radius ^ 2 =
        (cert.diskLabels[i.1]! : ℝ) := by
    intro i
    calc
      (P.circles (index i)).radius ^ 2 =
          (((index i).1 + 1 : ℕ) : ℝ) := hstandardRadius (index i)
      _ = (cert.diskLabels[i.1]! : ℝ) := by
        exact_mod_cast hindexLabel i
  exact nineCertificate_excludes_packing_order hcertFull P (0 : Fin 10) index
    hindexInjective hindexAvoidsAnchor hanchorCenter hanchorRadius hcontainer
    hradiusSq horder

def nineCircleProofP_diskIndex (i : Fin 9) : Fin 10 :=
  ⟨nineCircleProofP.diskLabels[i.1]! - 1, by
    have hlabel := nineCertificate_label_bounds_of_spec
      nineCircleProofP_spec.2.2.1 i
    omega⟩

def nineCircleProofQ_diskIndex (i : Fin 9) : Fin 10 :=
  ⟨nineCircleProofQ.diskLabels[i.1]! - 1, by
    have hlabel := nineCertificate_label_bounds_of_spec
      nineCircleProofQ_spec.2.2.1 i
    omega⟩

theorem nineCircleProofP_diskIndex_label (i : Fin 9) :
    (nineCircleProofP_diskIndex i).1 + 1 = nineCircleProofP.diskLabels[i.1]! := by
  change (nineCircleProofP.diskLabels[i.1]! - 1) + 1 = _
  exact Nat.sub_add_cancel (by
    have hlabel := nineCertificate_label_bounds_of_spec
      nineCircleProofP_spec.2.2.1 i
    omega)

theorem nineCircleProofQ_diskIndex_label (i : Fin 9) :
    (nineCircleProofQ_diskIndex i).1 + 1 = nineCircleProofQ.diskLabels[i.1]! := by
  change (nineCircleProofQ.diskLabels[i.1]! - 1) + 1 = _
  exact Nat.sub_add_cancel (by
    have hlabel := nineCertificate_label_bounds_of_spec
      nineCircleProofQ_spec.2.2.1 i
    omega)

theorem nineCircleProofP_diskLabels_injective :
    ∀ i j : Fin 9,
      nineCircleProofP.diskLabels[i.1]! = nineCircleProofP.diskLabels[j.1]! →
        i = j := by
  decide

theorem nineCircleProofQ_diskLabels_injective :
    ∀ i j : Fin 9,
      nineCircleProofQ.diskLabels[i.1]! = nineCircleProofQ.diskLabels[j.1]! →
        i = j := by
  decide

theorem nineCircleProofP_diskIndex_injective :
    Function.Injective nineCircleProofP_diskIndex := by
  intro i j heq
  apply nineCircleProofP_diskLabels_injective i j
  have hval := congrArg Fin.val heq
  have hlabelI := nineCircleProofP_diskIndex_label i
  have hlabelJ := nineCircleProofP_diskIndex_label j
  omega

theorem nineCircleProofQ_diskIndex_injective :
    Function.Injective nineCircleProofQ_diskIndex := by
  intro i j heq
  apply nineCircleProofQ_diskLabels_injective i j
  have hval := congrArg Fin.val heq
  have hlabelI := nineCircleProofQ_diskIndex_label i
  have hlabelJ := nineCircleProofQ_diskIndex_label j
  omega

theorem nineCircleProofP_excludes_standard_packing_order
    {R : ℝ} (P : Packing 10 R)
    (hstandardRadius : ∀ k : Fin 10,
      (P.circles k).radius ^ 2 = ((k.1 + 1 : ℕ) : ℝ))
    (hanchorCenter : (P.circles (0 : Fin 10)).center = (0, 0))
    (hcontainer : R ≤
      (nineCircleProofP.radiusUpper : ℝ) / nineCircleProofP.scale)
    (horder : ∀ i j : Fin 9, i.1 < j.1 →
      pointPolarAngle (P.circles (nineCircleProofP_diskIndex i)).center ≤
        pointPolarAngle (P.circles (nineCircleProofP_diskIndex j)).center) :
    False := by
  apply nineCertificate_excludes_standard_packing_order nineCircleProofP_spec
    P nineCircleProofP_diskIndex nineCircleProofP_diskIndex_injective
    nineCircleProofP_diskIndex_label hstandardRadius hanchorCenter hcontainer
  exact horder

theorem nineCircleProofQ_excludes_standard_packing_order
    {R : ℝ} (P : Packing 10 R)
    (hstandardRadius : ∀ k : Fin 10,
      (P.circles k).radius ^ 2 = ((k.1 + 1 : ℕ) : ℝ))
    (hanchorCenter : (P.circles (0 : Fin 10)).center = (0, 0))
    (hcontainer : R ≤
      (nineCircleProofQ.radiusUpper : ℝ) / nineCircleProofQ.scale)
    (horder : ∀ i j : Fin 9, i.1 < j.1 →
      pointPolarAngle (P.circles (nineCircleProofQ_diskIndex i)).center ≤
        pointPolarAngle (P.circles (nineCircleProofQ_diskIndex j)).center) :
    False := by
  apply nineCertificate_excludes_standard_packing_order nineCircleProofQ_spec
    P nineCircleProofQ_diskIndex nineCircleProofQ_diskIndex_injective
    nineCircleProofQ_diskIndex_label hstandardRadius hanchorCenter hcontainer
  exact horder

end

end CirclePacking

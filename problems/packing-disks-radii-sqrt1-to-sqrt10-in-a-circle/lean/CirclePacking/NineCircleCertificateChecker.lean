import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.List.Basic

namespace CirclePacking

/-!
# Exact integer checker for the nine-circle cycle certificate

All radial quantities are stored as naturals in one common exact scale.  The
angle Taylor inequalities and cycle sums are cross-multiplied to integer
inequalities.  The finite boolean checker is replayed with `native_decide`;
the resulting theorem therefore has the standard `native_decide` trust
dependency, while all proof decisions themselves use exact integer data.
-/

abbrev NineCycleEdge := Nat × Nat × Nat

inductive NineCycleTree where
  | leaf (edges : List NineCycleEdge)
  | split (axis cut : Nat) (left right : NineCycleTree)
  deriving Repr

structure NineCircleCertificate where
  scale : Nat
  radiusUpper : Nat
  diskLabels : Array Nat
  radiiLower : Array Nat
  tree : NineCycleTree
  deriving Repr

abbrev NineRadialBox := Array (Nat × Nat)

def nineRadiusUpperNumerator : Nat := 207586703053
def nineRadiusUpperDenominator : Nat := 25000000000
def nineAngleScale : Nat := 100000
def ninePiUpperTicks : Nat := 628320

def nineInitialBox (cert : NineCircleCertificate) : NineRadialBox :=
  cert.radiiLower.map (fun r => (0, cert.radiusUpper - r))

def nineContractCoordinate (radii : Array Nat) (box : NineRadialBox)
    (i : Nat) : Nat :=
  (List.range 9).foldl (fun lower j =>
    if i == j then lower else
      max lower (radii[i]! + radii[j]! - (box[j]!).2))
    (max 0 (box[i]!).1)

def nineContract (radii : Array Nat) (box : NineRadialBox) : NineRadialBox :=
  (List.range 9).toArray.map (fun i =>
    (nineContractCoordinate radii box i, (box[i]!).2))

def nineSetHi (box : NineRadialBox) (axis cut : Nat) : NineRadialBox :=
  box.modify axis (fun interval => (interval.1, cut))

def nineSetLo (box : NineRadialBox) (axis cut : Nat) : NineRadialBox :=
  box.modify axis (fun interval => (cut, interval.2))

def nineTaylorTermNumerator (ticks k : Nat) : Nat :=
  ticks ^ (2 * k) * nineAngleScale ^ (18 - 2 * k) *
    (Nat.factorial 18 / Nat.factorial (2 * k))

def nineTaylorNumeratorStep (ticks : Nat) (total : Int) (k : Nat) : Int :=
  let term := Int.ofNat (nineTaylorTermNumerator ticks k)
  if k % 2 == 0 then total + term else total - term

def nineTaylorNumerator (ticks : Nat) : Int :=
  (List.range 10).foldl (nineTaylorNumeratorStep ticks) 0

def nineTaylorDenominator : Nat :=
  nineAngleScale ^ 18 * Nat.factorial 18

def nineCosineNumerator (ri rj x y : Nat) : Int :=
  (Int.ofNat (x ^ 2 + y ^ 2)) - (Int.ofNat ((ri + rj) ^ 2))

def nineCornerPairs (a b : Nat × Nat) : List (Nat × Nat) :=
  [(a.1, b.1), (a.1, b.2), (a.2, b.1), (a.2, b.2)]

def nineEdgeAngleSpec (cert : NineCircleCertificate)
    (box : NineRadialBox) (edge : NineCycleEdge) : Prop := by
  let i := edge.1
  let j := edge.2.1
  let ticks := edge.2.2
  let ri := cert.radiiLower[i]!
  let rj := cert.radiiLower[j]!
  let bi := box[i]!
  let bj := box[j]!
  let taylorNumerator := nineTaylorNumerator ticks
  let taylorDenominator := nineTaylorDenominator
  exact i < 9 ∧ j < 9 ∧ i ≠ j ∧ ticks ≤ 314159 ∧
    (ticks = 0 ∨
      (bi.1 ≠ 0 ∧ bj.1 ≠ 0 ∧
       113 * ticks < 355 * nineAngleScale ∧
       ∀ xy ∈ nineCornerPairs bi bj,
         taylorNumerator * Int.ofNat
              (2 * xy.1 * xy.2 * nineAngleScale) >
           nineCosineNumerator ri rj xy.1 xy.2 *
              Int.ofNat (taylorDenominator * nineAngleScale) +
             Int.ofNat (2 * xy.1 * xy.2 * ticks ^ 19)))

def nineEdgeAngleValid (cert : NineCircleCertificate)
    (box : NineRadialBox) (edge : NineCycleEdge) : Bool := Id.run do
  let i := edge.1
  let j := edge.2.1
  let ticks := edge.2.2
  if i >= 9 || j >= 9 || i == j || ticks > 314159 then
    return false
  if ticks == 0 then return true
  let ri := cert.radiiLower[i]!
  let rj := cert.radiiLower[j]!
  let bi := box[i]!
  let bj := box[j]!
  if bi.1 == 0 || bj.1 == 0 then return false
  if 113 * ticks >= 355 * nineAngleScale then return false
  let taylorNumerator := nineTaylorNumerator ticks
  let taylorDenominator := nineTaylorDenominator
  return (nineCornerPairs bi bj).all (fun xy =>
    taylorNumerator * Int.ofNat (2 * xy.1 * xy.2 * nineAngleScale) >
      nineCosineNumerator ri rj xy.1 xy.2 *
        Int.ofNat (taylorDenominator * nineAngleScale) +
          Int.ofNat (2 * xy.1 * xy.2 * ticks ^ 19))

theorem nineEdgeAngleValid_spec {cert : NineCircleCertificate}
    {box : NineRadialBox} {edge : NineCycleEdge}
    (h : nineEdgeAngleValid cert box edge = true) :
    nineEdgeAngleSpec cert box edge := by
  unfold nineEdgeAngleValid nineEdgeAngleSpec at *
  simp only [Id.run] at h ⊢
  split_ifs at h ⊢ <;> try simp_all
  change (nineCornerPairs box[edge.1]! box[edge.2.1]!).all
      (fun xy => decide
        (nineTaylorNumerator edge.2.2 *
            Int.ofNat (2 * xy.1 * xy.2 * nineAngleScale) >
          nineCosineNumerator cert.radiiLower[edge.1]!
              cert.radiiLower[edge.2.1]! xy.1 xy.2 *
            Int.ofNat (nineTaylorDenominator * nineAngleScale) +
              Int.ofNat (2 * xy.1 * xy.2 * edge.2.2 ^ 19))) = true at h
  intro a b hab
  have hcheck := (List.all_eq_true.mp h) (a, b) hab
  exact of_decide_eq_true hcheck

def nineCycleTailSpec (start current : Nat) : List NineCycleEdge → Prop
  | [] => current = start
  | edge :: rest => current = edge.1 ∧
      nineCycleTailSpec start edge.2.1 rest

def nineCycleTailValid (start current : Nat) (edges : List NineCycleEdge) : Bool :=
  match edges with
  | [] => current == start
  | edge :: rest => current == edge.1 &&
      nineCycleTailValid start edge.2.1 rest

theorem nineCycleTailValid_spec {start current : Nat}
    {edges : List NineCycleEdge}
    (h : nineCycleTailValid start current edges = true) :
    nineCycleTailSpec start current edges := by
  induction edges generalizing current with
  | nil =>
      simpa [nineCycleTailValid, nineCycleTailSpec] using h
  | cons edge rest ih =>
      simp only [nineCycleTailValid, Bool.and_eq_true] at h
      simp only [nineCycleTailSpec]
      exact ⟨by simpa using h.1, ih h.2⟩

def nineCycleWeightTicks (edges : List NineCycleEdge) : Int :=
  edges.foldl (fun total edge =>
    let ticks := edge.2.2
    if edge.1 < edge.2.1 then
      total + Int.ofNat (ninePiUpperTicks - ticks)
    else total - Int.ofNat ticks) 0

def nineLeafSpecWithWeight (cert : NineCircleCertificate)
    (box : NineRadialBox) (weight : Int)
    (edges : List NineCycleEdge) : Prop :=
  match edges with
  | [] => False
  | first :: rest =>
      2 ≤ edges.length ∧ edges.length ≤ 9 ∧
      first.1 ≠ first.2.1 ∧
      nineCycleTailSpec first.1 first.2.1 rest ∧
      edges.all (nineEdgeAngleValid cert box) = true ∧
      weight < 0

def nineLeafSpec (cert : NineCircleCertificate)
    (box : NineRadialBox) (edges : List NineCycleEdge) : Prop :=
  nineLeafSpecWithWeight cert box (nineCycleWeightTicks edges) edges

def nineLeafValid (cert : NineCircleCertificate)
    (box : NineRadialBox) (edges : List NineCycleEdge) : Bool :=
  match edges with
  | [] => false
  | first :: rest =>
      decide (2 ≤ edges.length ∧ edges.length ≤ 9) &&
      first.1 != first.2.1 &&
      nineCycleTailValid first.1 first.2.1 rest &&
      edges.all (nineEdgeAngleValid cert box) &&
      decide (nineCycleWeightTicks edges < 0)

theorem nineLeafValid_spec {cert : NineCircleCertificate}
    {box : NineRadialBox} {edges : List NineCycleEdge}
    (h : nineLeafValid cert box edges = true) :
    nineLeafSpec cert box edges := by
  unfold nineLeafValid at h
  unfold nineLeafSpec
  generalize hweight : nineCycleWeightTicks edges = weight at h ⊢
  have hspec : nineLeafSpecWithWeight cert box weight edges := by
    clear hweight
    cases edges with
    | nil => simp at h
    | cons first rest =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        rcases h with
          ⟨⟨⟨⟨⟨hlenLower, hlenUpper⟩, hfirstBool⟩, htail⟩, hedge⟩, hneg⟩
        have htail' := nineCycleTailValid_spec htail
        have hfirst : first.1 ≠ first.2.1 := by simpa using hfirstBool
        have hedge' : ∀ edge ∈ first :: rest,
            nineEdgeAngleValid cert box edge = true :=
          List.all_eq_true.mp hedge
        simp only [nineLeafSpecWithWeight, List.length_cons]
        refine ⟨?_, ?_, ?_, htail', ?_, hneg⟩
        · omega
        · omega
        · exact hfirst
        · exact List.all_eq_true.mpr hedge'
  exact hspec

theorem nineLeafSpec_edges_valid (cert : NineCircleCertificate)
    (box : NineRadialBox) (edges : List NineCycleEdge)
    (h : nineLeafSpec cert box edges) :
    edges.all (nineEdgeAngleValid cert box) = true := by
  unfold nineLeafSpec at h
  generalize hweight : nineCycleWeightTicks edges = weight at h
  have hresult : edges.all (nineEdgeAngleValid cert box) = true := by
    clear hweight
    cases edges with
    | nil => simp [nineLeafSpecWithWeight] at h
    | cons first rest =>
        simp only [nineLeafSpecWithWeight] at h
        exact h.2.2.2.2.1
  exact hresult

def nineReplayTreeSpec (cert : NineCircleCertificate) :
    NineCycleTree → NineRadialBox → Prop
  | .leaf edges, box =>
      nineLeafSpec cert (nineContract cert.radiiLower box) edges
  | .split axis cut left right, box => by
      let contracted := nineContract cert.radiiLower box
      let interval := contracted[axis]!
      exact axis < 9 ∧ interval.1 < cut ∧ cut < interval.2 ∧
        nineReplayTreeSpec cert left (nineSetHi contracted axis cut) ∧
        nineReplayTreeSpec cert right (nineSetLo contracted axis cut)

def nineReplayTree (cert : NineCircleCertificate) :
    NineCycleTree → NineRadialBox → Bool
  | .leaf edges, box =>
      nineLeafValid cert (nineContract cert.radiiLower box) edges
  | .split axis cut left right, box => Id.run do
      let contracted := nineContract cert.radiiLower box
      if axis >= 9 then return false
      let interval := contracted[axis]!
      if !(interval.1 < cut && cut < interval.2) then return false
      let leftOK := nineReplayTree cert left (nineSetHi contracted axis cut)
      if !leftOK then return false
      return nineReplayTree cert right (nineSetLo contracted axis cut)

theorem nineReplayTree_spec (cert : NineCircleCertificate)
    (tree : NineCycleTree) (box : NineRadialBox)
    (h : nineReplayTree cert tree box = true) :
    nineReplayTreeSpec cert tree box := by
  induction tree generalizing box with
  | leaf edges =>
      exact nineLeafValid_spec h
  | split axis cut left right ihLeft ihRight =>
      simp only [nineReplayTree, Id.run] at h
      split_ifs at h with hAxis hCut hLeft
      have haxisLt : axis < 9 := by omega
      have hcutLo : (nineContract cert.radiiLower box)[axis]!.1 < cut := by
        by_contra hnot
        exact hCut (by simp [hnot])
      have hcutHi : cut < (nineContract cert.radiiLower box)[axis]!.2 := by
        by_contra hnot
        exact hCut (by simp [hcutLo, hnot])
      have hleft :
          nineReplayTree cert left
            (nineSetHi (nineContract cert.radiiLower box) axis cut) = true := by
        by_cases hh : nineReplayTree cert left
            (nineSetHi (nineContract cert.radiiLower box) axis cut) = true
        · exact hh
        · exact False.elim (hLeft (by simp [hh]))
      have hright :
          nineReplayTree cert right
            (nineSetLo (nineContract cert.radiiLower box) axis cut) = true := by
        change _ = true at h
        exact h
      simp only [nineReplayTreeSpec]
      exact ⟨haxisLt, hcutLo, hcutHi,
        ihLeft _ hleft, ihRight _ hright⟩

def nineCertificateRadiiSpec (cert : NineCircleCertificate) : Prop :=
  cert.diskLabels.size = 9 ∧ cert.radiiLower.size = 9 ∧
    (List.range 9).all (fun i => decide (
      let label := cert.diskLabels[i]!
      let radius := cert.radiiLower[i]!
      2 ≤ label ∧ label ≤ 10 ∧ radius ^ 2 ≤ label * cert.scale ^ 2)) = true

def nineCertificateRadiiValid (cert : NineCircleCertificate) : Bool :=
  cert.diskLabels.size == 9 && cert.radiiLower.size == 9 &&
    (List.range 9).all (fun i =>
      let label := cert.diskLabels[i]!
      let radius := cert.radiiLower[i]!
      2 ≤ label && label ≤ 10 &&
        radius ^ 2 ≤ label * cert.scale ^ 2)

def nineCertificateSpec (cert : NineCircleCertificate) : Prop :=
  cert.scale > 0 ∧
  cert.radiusUpper * nineRadiusUpperDenominator =
      nineRadiusUpperNumerator * cert.scale ∧
  nineCertificateRadiiSpec cert ∧
  nineReplayTreeSpec cert cert.tree (nineInitialBox cert)

def nineCertificateValid (cert : NineCircleCertificate) : Bool :=
  cert.scale > 0 && cert.radiusUpper * nineRadiusUpperDenominator ==
      nineRadiusUpperNumerator * cert.scale &&
    nineCertificateRadiiValid cert &&
    nineReplayTree cert cert.tree (nineInitialBox cert)

theorem nineCertificateRadiiValid_spec (cert : NineCircleCertificate)
    (h : nineCertificateRadiiValid cert = true) :
    nineCertificateRadiiSpec cert := by
  simpa [nineCertificateRadiiValid, nineCertificateRadiiSpec,
    Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h

theorem nineCertificateValid_spec (cert : NineCircleCertificate)
    (h : nineCertificateValid cert = true) :
    nineCertificateSpec cert := by
  simp only [nineCertificateValid, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨hscale, hradiusUpper⟩, hradii⟩, htree⟩
  exact ⟨hscale, by simpa using hradiusUpper,
    nineCertificateRadiiValid_spec cert hradii,
    nineReplayTree_spec cert cert.tree (nineInitialBox cert) htree⟩

end CirclePacking

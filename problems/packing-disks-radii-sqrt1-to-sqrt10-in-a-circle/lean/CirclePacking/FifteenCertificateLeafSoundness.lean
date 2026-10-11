import CirclePacking.FifteenCertificate
import CirclePacking.FifteenPackingSortedGeometry

/-! Semantic consequences of the exact subdivision certificate's terminal
nodes. These lemmas are independent of the JSON tree traversal: they isolate
the local contradiction supplied by a `SUM` leaf and the radial box supplied
by a `LOCAL` leaf. -/

namespace CirclePacking

open Lean

theorem fifteenTerminalValid_sum_spec
    (box : FifteenBox) (inner : List Nat) (node : Json)
    (allowLocal : Bool) (positiveZero exactZero : List Nat)
    (htag : fifteenJsonAt? node 0 >>= fifteenJsonString? = some "SUM")
    (hvalid : fifteenTerminalValid box inner node allowLocal
      positiveZero exactZero = true) :
    ∃ i j, i < j ∧ j < 15 ∧ i ∈ inner ∧ j ∈ inner ∧
      box[i]!.2 + box[j]!.2 < 2 := by
  cases harray : fifteenJsonArray? node with
  | none => simp [fifteenJsonAt?, harray] at htag
  | some values =>
      have htag' : values[0]? >>= fifteenJsonString? = some "SUM" := by
        simpa [fifteenJsonAt?, harray] using htag
      obtain ⟨tagJson, hzero⟩ : ∃ tagJson, values[0]? = some tagJson := by
        cases hzero : values[0]? with
        | none => simp [hzero] at htag'
        | some tagJson => exact ⟨tagJson, rfl⟩
      have h0spec := Array.getElem?_eq_some_iff.mp hzero
      have h0bound : 0 < values.size := h0spec.1
      have h0eq : values[0]'h0bound = tagJson := h0spec.2
      have htagVal : fifteenJsonString? tagJson = some "SUM" := by
        simpa [hzero] using htag'
      cases hi : values[1]? >>= fifteenJsonNat? with
      | none => simp [fifteenTerminalValid, Id.run, harray, h0bound, h0eq, htagVal, hi] at hvalid
      | some i =>
          obtain ⟨jsonI, h1opt⟩ : ∃ jsonI, values[1]? = some jsonI := by
            cases h1opt : values[1]? with
            | none => simp [h1opt] at hi
            | some jsonI => exact ⟨jsonI, rfl⟩
          have h1spec := Array.getElem?_eq_some_iff.mp h1opt
          have h1bound : 1 < values.size := h1spec.1
          have h1eq : values[1]'h1bound = jsonI := h1spec.2
          have h1val : fifteenJsonNat? jsonI = some i := by
            simpa [h1opt] using hi
          cases hj : values[2]? >>= fifteenJsonNat? with
          | none => simp [fifteenTerminalValid, Id.run, harray, h0bound, h0eq,
              htagVal, h1eq, h1val, hi, hj] at hvalid
          | some j =>
              obtain ⟨jsonJ, h2opt⟩ : ∃ jsonJ, values[2]? = some jsonJ := by
                cases h2opt : values[2]? with
                | none => simp [h2opt] at hj
                | some jsonJ => exact ⟨jsonJ, rfl⟩
              have h2spec := Array.getElem?_eq_some_iff.mp h2opt
              have h2bound : 2 < values.size := h2spec.1
              have h2eq : values[2]'h2bound = jsonJ := h2spec.2
              have h2val : fifteenJsonNat? jsonJ = some j := by
                simpa [h2opt] using hj
              have hsize : values.size = 3 := by
                by_cases hsize : values.size = 3
                · exact hsize
                · simp [fifteenTerminalValid, Id.run, harray, h0bound, h0eq,
                    htagVal, h1eq, h1val, h2eq, h2val, hsize] at hvalid
              have hij : i < j := by
                by_cases hlt : i < j
                · exact hlt
                · have hge : j ≤ i := Nat.le_of_not_gt hlt
                  simp [fifteenTerminalValid, Id.run, harray, h0bound, h0eq,
                    htagVal, h1eq, h1val, h2eq, h2val, hsize, hge]
                    at hvalid
              have hj15 : j < 15 := by
                by_cases hlt : j < 15
                · exact hlt
                · have hge : 15 ≤ j := Nat.le_of_not_gt hlt
                  simp [fifteenTerminalValid, Id.run, harray, h0bound, h0eq,
                    htagVal, h1eq, h1val, h2eq, h2val, hsize,
                    hij, hge] at hvalid
              have himem : i ∈ inner := by
                by_cases hmem : i ∈ inner
                · exact hmem
                · simp [fifteenTerminalValid, Id.run, harray, h0bound, h0eq,
                    htagVal, h1eq, h1val, h2eq, h2val, hsize,
                    hij, hj15, hmem] at hvalid
              have hjmem : j ∈ inner := by
                by_cases hmem : j ∈ inner
                · exact hmem
                · simp [fifteenTerminalValid, Id.run, harray, h0bound, h0eq,
                    htagVal, h1eq, h1val, h2eq, h2val, hsize,
                    hij, hj15, himem, hmem] at hvalid
              have hsum : box[i]!.2 + box[j]!.2 < 2 := by
                have hnotI : ¬ j ≤ i := Nat.not_le_of_gt hij
                have hnotJ : ¬ 15 ≤ j := Nat.not_le_of_gt hj15
                have hdec : decide (box[i]!.2 + box[j]!.2 < 2) = true := by
                  have hcheck := hvalid
                  simp [fifteenTerminalValid, Id.run, harray, hzero, h0bound,
                    h0eq, htagVal, h1opt, h1eq, h1val, h2opt, h2eq, h2val,
                    hsize, hij, hj15, hnotI, hnotJ, himem, hjmem] at hcheck
                  change decide (box[i]!.2 + box[j]!.2 < 2) = true at hcheck
                  exact hcheck
                exact of_decide_eq_true hdec
              exact ⟨i, j, hij, hj15, himem, hjmem, hsum⟩

theorem fifteenTerminalValid_local_spec
    (box : FifteenBox) (inner : List Nat) (node : Json)
    (allowLocal : Bool) (positiveZero exactZero : List Nat)
    (htag : fifteenJsonAt? node 0 >>= fifteenJsonString? = some "LOCAL")
    (hvalid : fifteenTerminalValid box inner node allowLocal
      positiveZero exactZero = true) :
    inner = fifteenInnerPositions "001001001001001" ∧
      ∀ p ∈ inner,
        fifteenLocalLo ≤ box[p]!.1 ∧ box[p]!.2 ≤ fifteenLocalHi := by
  cases harray : fifteenJsonArray? node with
  | none => simp [fifteenJsonAt?, harray] at htag
  | some values =>
      have htag' : values[0]? >>= fifteenJsonString? = some "LOCAL" := by
        simpa [fifteenJsonAt?, harray] using htag
      have hallow : allowLocal = true := by
        cases allowLocal with
        | false => simp [fifteenTerminalValid, Id.run, harray, htag'] at hvalid
        | true => rfl
      have hvalid' := hvalid
      simp only [fifteenTerminalValid, Id.run, harray, htag', hallow] at hvalid'
      change (values.size == 1 && inner ==
        fifteenInnerPositions "001001001001001" &&
        fifteenInLocalBox box inner) = true at hvalid'
      have hparts : (values.size = 1 ∧
          inner = fifteenInnerPositions "001001001001001") ∧
          fifteenInLocalBox box inner = true := by
        simpa using hvalid'
      have hinner : inner = fifteenInnerPositions "001001001001001" := hparts.1.2
      have hbox : fifteenInLocalBox box inner = true := hparts.2
      refine ⟨hinner, ?_⟩
      intro p hp
      have hp' := (List.all_eq_true.mp hbox) p hp
      have hp'' : decide (fifteenLocalLo ≤ box[p]!.1) = true ∧
          decide (box[p]!.2 ≤ fifteenLocalHi) = true := by
        simpa [fifteenInLocalBox] using hp'
      exact ⟨of_decide_eq_true hp''.1, of_decide_eq_true hp''.2⟩

/-- A successful `SUM` terminal is geometrically impossible for unit disks
whose sorted center radii lie in its rational box. -/
theorem fifteen_unit_packing_terminal_sum_excludes
    {R : ℝ} (P : Packing 15 R)
    (hunit : ∀ k, (P.circles k).radius = 1)
    (box : FifteenBox) (inner : List Nat) (node : Json)
    (allowLocal : Bool) (positiveZero exactZero : List Nat)
    (htag : fifteenJsonAt? node 0 >>= fifteenJsonString? = some "SUM")
    (hvalid : fifteenTerminalValid box inner node allowLocal
      positiveZero exactZero = true)
    (hradial : ∀ k : Fin 15,
      fifteenPackingSortedRadius P k ≤ (box[k.1]!.2 : ℝ)) :
    False := by
  obtain ⟨i, j, hij, hj15, _himem, _hjmem, hsum⟩ :=
    fifteenTerminalValid_sum_spec box inner node allowLocal positiveZero exactZero
      htag hvalid
  have hi15 : i < 15 := Nat.lt_trans hij hj15
  let fi : Fin 15 := ⟨i, hi15⟩
  let fj : Fin 15 := ⟨j, hj15⟩
  have hfij : fi ≠ fj := by
    intro heq
    have hval : i = j := by simpa [fi, fj] using congrArg Fin.val heq
    exact (Nat.ne_of_lt hij) hval
  have hsortedNe : fifteenPackingSortedIndex P fi ≠
      fifteenPackingSortedIndex P fj := by
    intro heq
    exact hfij ((fifteenPackingSortedIndex_bijective P).1 heq)
  have hpair := fifteen_unit_packing_pair_radial_sum_ge_two P hunit
    hsortedNe
  have hpair' : 2 ≤ fifteenPackingSortedRadius P fi +
      fifteenPackingSortedRadius P fj := by
    simpa [fifteenPackingSortedRadius, fifteenCenterRadius,
      fifteenPackingSortedIndex] using hpair
  have hupper : (box[i]!.2 : ℝ) + (box[j]!.2 : ℝ) < 2 := by
    exact_mod_cast hsum
  have hradialSum : fifteenPackingSortedRadius P fi +
      fifteenPackingSortedRadius P fj ≤
      (box[i]!.2 : ℝ) + (box[j]!.2 : ℝ) :=
    add_le_add (hradial fi) (hradial fj)
  exact (not_lt_of_ge hpair') (lt_of_le_of_lt hradialSum hupper)

end CirclePacking

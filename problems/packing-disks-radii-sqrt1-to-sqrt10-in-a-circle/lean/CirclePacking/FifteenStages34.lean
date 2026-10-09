import CirclePacking.FifteenStage3Certificate

/-!
# Stage 3/4 certificate replay entry point

The former implementation reran the entire Stage 3 and Stage 4 branching
search in Lean.  That made a small data change trigger millions of Lean-side
relaxations.  The replay has been moved to independent certificate checking;
this entry point currently exports the first Stage 3 closed-pattern vertical
slice.  The remaining 354 Stage 3 and 19 Stage 4 closed-pattern certificates
are not yet included here.
-/

namespace CirclePacking

theorem fifteenStage3FirstPatternCertificate_replays :
    fifteenStage3TableValid && fifteenStage3PatternCertificateChecks = true := by
  rw [fifteenStage3Table_valid, fifteenStage3PatternCertificate_checks]
  rfl

end CirclePacking

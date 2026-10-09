# Fifteen equal disks: collected proof materials

This directory gathers the earlier Japanese research notes, the supplied exact-certificate bundle, and an English manuscript draft.

- `references/packing15_working_note.tex` and `references/packing15_progress_note2.tex` preserve the two notes from the repository history immediately before commit `b75b0c8` removed them from the tracked working tree.
- `candidate_bundle/` contains the files from the supplied `packing15_candidate_proof_and_verifier.zip`, plus a replayable correction and audit described below.
- `paper/main.tex` is the English manuscript.

To reproduce the finite certificate, from the repository root run:

```sh
cd problems/packing-15-equal-disks-in-a-circle/candidate_bundle
bash run_all.sh
```

The replay checks the documented tree counts and survivor identities at each stage, verifies that the 6+9 radial assignments are read from the generated residual list, and separates the exact zero-radius case from positive-radius bins. The zero endpoint has no polar angle; its branch instead uses the direct radial-distance condition. Boundary radii have explicit half-open ownership, while closed rational intervals are used only as outward bounds. The degree-18 cosine polynomial is reduced by the exact Lagrange error bound `x^19/19!`; rational Machin-series bounds certify the pi range used by the angle comparisons. The initial angular graph checks all 760 cyclic classes directly. Refined tables are generated and checked against the C++ tables during replay.

The replay also emits `candidate_bundle/exact_subdivision_certificate.json`; `check_exact_certificate.py` is a separate rational-arithmetic checker that verifies the 1,266 fine-subdivision roots and nine 6+9 endpoint leaves, including every split cover, negative-cycle weight, pair-sum leaf, and local-region leaf. Its root list is compared with `full_residuals.txt`; completeness of the earlier discrete enumeration remains established by exhaustive replay and count/set checks, not by that serialized tree alone. The replay completed successfully in this workspace on October 9, 2026. This confirms the arithmetic and search outcomes for this implementation. It is not an independent formalization or peer review of the geometric lemmas.

The original supplied files are retained where practical. The original ZIP has SHA-256 `64f5a8e0cf40eec4dcae6e375c7af87fbb8fa56dbad1b3fa6f587b2afbe68355`; the separately supplied sketch has SHA-256 `65c376e11ae0c25ec0bda7200468cbd4ebbc7ba75d665dd3d734a82c30b95076`.

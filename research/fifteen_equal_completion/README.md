# Fifteen equal disks: collected proof materials

This directory gathers the earlier Japanese research notes, the supplied exact-certificate bundle, and an English manuscript draft.

- `references/packing15_working_note.tex` and `references/packing15_progress_note2.tex` preserve the two notes from the repository history immediately before commit `b75b0c8` removed them from the tracked working tree.
- `candidate_bundle/` contains the files from the supplied `packing15_candidate_proof_and_verifier.zip`, plus a replayable correction and audit described below.
- `paper/main.tex` is the English manuscript.

To reproduce the finite certificate, from the repository root run:

```sh
cd research/fifteen_equal_completion/candidate_bundle
bash run_all.sh
```

The replay was adjusted in two ways after auditing the supplied bundle. First, its Taylor cosine bound now subtracts the exact Lagrange error bound `x^19/19!`; the degree-18 polynomial alone is not a lower bound. Second, the initial angular graph checks every one of the 760 cyclic classes, so the separate gap-capacity filter is not part of the proof path. The fixed coarse table is checked by `verify_coarse_angles.py`; refined tables are generated and checked against the C++ tables during replay.

The replay completed successfully in this workspace on October 9, 2026. This confirms the stated arithmetic and search outcomes for this implementation. It is not an independent formalization or peer review of the geometric lemmas.

The original supplied files are retained where practical. The original ZIP has SHA-256 `64f5a8e0cf40eec4dcae6e375c7af87fbb8fa56dbad1b3fa6f587b2afbe68355`; the separately supplied sketch has SHA-256 `65c376e11ae0c25ec0bda7200468cbd4ebbc7ba75d665dd3d734a82c30b95076`.

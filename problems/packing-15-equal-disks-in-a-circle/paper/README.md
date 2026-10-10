# English manuscript

`main.tex` is the English paper draft for the fifteen equal-disk packing certificate. It summarizes the geometric reductions and the computer-assisted proof, includes TikZ figures for the construction, radial reduction, angular constraints, certificate flow, and local barrier, and points to the self-contained verifier in `../candidate_bundle/`.

Build from this directory with `xelatex -interaction=nonstopmode -halt-on-error main.tex` twice, or open `main.tex` in Codex for the built-in LaTeX preview.

The manuscript presents a candidate computer-assisted proof. Its Lean-status appendix maps the mathematical argument to the partial formalization at a fixed commit: the finite replays, local obstruction, canonical radius/angle normalization, and geometric Stage 0 reduction from 760 patterns to 378 survivors are checked, while the Stage 3/4 and refined packing-level reduction, explicit feasible candidate object, and unconditional optimum theorem remain unfinished. It also documents alternative intermediate proofs and the finite replays' `native_decide` trust dependencies.

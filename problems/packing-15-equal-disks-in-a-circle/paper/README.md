# English manuscript

`main.tex` is the English paper draft for the fifteen equal-disk packing certificate. It summarizes the geometric reductions and the computer-assisted proof, includes TikZ figures for the construction, radial reduction, angular constraints, certificate flow, and local barrier, and points to the self-contained verifier in `../candidate_bundle/`.

Build from this directory with `xelatex -interaction=nonstopmode -halt-on-error main.tex` twice, or open `main.tex` in Codex for the built-in LaTeX preview.

The manuscript records the completed Lean connection: an explicit feasible `Packing 15` gives the upper bound, and the geometric reduction, finite certificates, and local obstruction give the lower bound. The theorem `fifteen_unit_packing_radius_iff_ge_closed_form` states the exact closed-form optimum as a feasibility equivalence. Its finite replays use `native_decide`, so the appendix documents the resulting trusted-compiler dependency; this is a formal Lean theorem, but not a kernel-only proof.

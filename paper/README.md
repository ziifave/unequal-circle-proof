# Global-optimality manuscript

`main.tex` is the English manuscript for the exact global-optimality result
for ten circles of radii `sqrt(1), ..., sqrt(10)`. It defines the optimum as
the unique solution of two certified angle equations and explains the finite
proof composition, the matching configuration, and the exact-rational replay
boundary. It does not identify that root with the separate algebraic value
`R0`.

Build the PDF from the repository root with the bundled Tectonic executable:

```bash
./tools/bin/tectonic --keep-logs --outdir paper paper/main.tex
```

Replay the proof composition with the locked Python environment:

```bash
uv run --locked --no-sync python tools/verify_global_optimality_completion.py
```

The generated manuscript is `paper/main.pdf`.

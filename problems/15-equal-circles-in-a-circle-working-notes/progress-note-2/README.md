# 15等円パッキング：第二研究ノート

2026-10-09 時点の研究メモ（第1ノートの続編）です。15等円の大域最適性は**未証明**です。

## Contents
- `packing15_progress_note2.tex`: 日本語LaTeX原稿。TikZ図はすべてソースに含まれます。
- `packing15_progress_note2.pdf`: コンパイル済みPDF。

## Build
XeLaTeX（Noto Serif CJK JP、Liberation Serif、TikZ、amsmath、tcolorbox等のパッケージが必要）：

```bash
xelatex -interaction=nonstopmode packing15_progress_note2.tex
xelatex -interaction=nonstopmode packing15_progress_note2.tex
```

## Scope
壁面化補題、中心半径順位上界、外周10円の角度予算、内側5円の2つの片側領域の大域排除、混合領域の局所障壁、今後必要な760分類の有限被覆を整理しています。厳密な全大域下界の計算機証明書は含みません。

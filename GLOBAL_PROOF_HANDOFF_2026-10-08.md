# 大域最適性証明：作業記録・方針・再開手順

2026-10-08 更新。**この文書のv12節が最新状態**であり、下記の元v1記録は
設計経緯として読むこと。

**最適性等式 `R*=R0` はまだ未証明。** v12木は全初期領域を被覆し、葉ごとの
不可能性・局所下界証明を独立replayできる。未解決は193葉、19,929個の
「半径箱×骨格×扇形割当」ケース。

## 最新checkpoint：v12

探索半径の安全な上限は `U=8.303468122111490`、既知候補は
`R0≈8.3034681221114890787043811875...`。大域方針はU以下の全配置を覆い、
各ケースを不可能性または認証済み局所下界で閉じること。U内の全配置を
不可能として排除する必要はない。

独立replayの結果は次の通り。

| 項目 | v12 |
|---|---:|
| 二分割 / ノード / 葉 | 980 / 1,961 / 981 |
| 全セクターケースを閉じた葉 | 788 |
| 未解決葉 | 193 |
| 最大木深さ | 310 |
| 箱×配置ケース（閉 / 全） | 12,034,599 / 12,054,528 |
| 箱×配置ケースの閉鎖率 | 99.834676% |
| 順序群の負閉路・局所終端 | 6,601群 / うち局所終端2群 |
| 局所順序終端で全ケースを閉じた葉 | 1 |

半径箱をまたいで同じ離散パターンを重複計上しない場合は、3種類の反射商骨格と
`4^6` 個のセクター割当からなる12,288種類中、6,300種類（51.269531%）を
全半径領域で閉じた。5,988種類は少なくとも1つの未解決半径箱に残る。
したがって99.834676%は葉ごとの延べケース率、51.269531%は重複なしの
大域パターン率であり、意味が異なる。

v12は候補を含む局所枝も閉じた。全10円の候補動径を含む葉はv11時点のnode 1744
で、全順序群のうち1群を局所定理、残りを負閉路で閉じる。v12はこの葉を保持する。
局所半径区間の幅をみるとき、角度順序ごとの座標区間全体が局所半径
`delta >= 5.8599087798744e-5` に入ることを有理数で判定する。

局所下界は [artifacts/local-optimality-constants.json](artifacts/local-optimality-constants.json)
にある認証済み局所定理を前提とする。今回のreplayは定数のスカラー条件と
根箱・包含判定を検査するが、元の局所証明の全線形代数をこの大域replay内で
再生成してはいない。局所定理の元証明も最終成果に含めて確認すること。

証明書: [skeleton-radial-tree-v12-global-refinement.json](certificates/skeleton-radial-tree-v12-global-refinement.json)

独立replay: [skeleton-radial-tree-v12-global-refinement-replay.json](artifacts/skeleton-radial-tree-v12-global-refinement-replay.json)

SHA-256: 証明書 `446d0172c59d25dd35cc1807e35d2a7a09743c6fc3138433cdbb03d8a354f4dd`、
検証器 `30090a9dd14cb3c5580a28a69106926d8d34aaa2116aebca0f32bda4f0de2ee4`。
対象ファイル一覧のmanifest: [skeleton-radial-tree-v12-global-refinement-manifest.json](artifacts/skeleton-radial-tree-v12-global-refinement-manifest.json)

### v12を再検証・再開する

リポジトリ直下で実行する。

```bash
PYTHONDONTWRITEBYTECODE=1 uv run --locked --no-sync python -m proof.skeleton_radial_tree \
  certificates/skeleton-radial-tree-v12-global-refinement.json \
  --output artifacts/skeleton-radial-tree-v12-global-refinement-replay.json

PYTHONDONTWRITEBYTECODE=1 uv run --locked --no-sync python -m tools.certify_skeleton_radial_tree \
  --resume certificates/skeleton-radial-tree-v12-global-refinement.json \
  --local-certificate artifacts/local-optimality-constants.json \
  --all-pair-orders --splits 100 \
  --output certificates/skeleton-radial-tree-v13.json \
  --report artifacts/skeleton-radial-tree-v13-report.json

PYTHONDONTWRITEBYTECODE=1 uv run --with pytest --locked python -m pytest -q
```

`--all-pair-orders` は、各葉の未解決セクターケースが64以下のとき、円1〜6の
セクター内全順序を検査する。各順序は負閉路で排除するか、コアの座標射影全体が
局所 `delta` 近傍内にあることを確認して閉じる。その他の順序が残れば葉は未解決の
まま保持される。既知候補の全10動径は探索の優先順位にだけ使い、箱の除外や
局所判定には使わない。

v12時点のテストは66件と8件のサブテストが通過。検証器は証明書の被覆・各葉の
排除・負閉路・局所射影をreplayする。`UNKNOWN` と `global_optimality_proved=false`
を維持しており、最適性証明達成とは扱わない。

### v12の主な実装ファイル

| 役割 | ファイル |
|---|---|
| 角度・全配置台帳・360コア順序・閉路replay | [proof/skeleton_cover.py](proof/skeleton_cover.py) |
| 適応木の独立検証・葉ごとの局所終端 | [proof/skeleton_radial_tree.py](proof/skeleton_radial_tree.py) |
| コアの有理角度区間から局所近傍を検査 | [proof/skeleton_local_terminal.py](proof/skeleton_local_terminal.py) |
| 木の生成・再開・順序精密化 | [tools/certify_skeleton_radial_tree.py](tools/certify_skeleton_radial_tree.py) |
| 全対順序の証明書生成 | [tools/certify_skeleton_cover.py](tools/certify_skeleton_cover.py) |
| 回帰テスト | `tests/test_skeleton_cover.py`, `tests/test_skeleton_radial_tree.py` |
| v12証明書・replay | 上記証明書とreplayリンク |
| 方針・証明の入口 | [GLOBAL_PROOF_STRATEGY_2026-10-08.md](GLOBAL_PROOF_STRATEGY_2026-10-08.md), [LARGE_FOUR_SKELETON_STATUS.md](LARGE_FOUR_SKELETON_STATUS.md) |

### 次に進めること

1. v12から再開し、局所近傍に隣接する半径箱と大域的な残存箱を細分する。
2. 未解決5,988種類の配置パターンを、円1,3,4の挿入可能性・動径角度相関・順序別
   局所包含でさらに減らす。木の延べ未解決ケースと重複なしパターンを分けて追う。
3. 異なる局所根や局所 `delta` 外で残る配置があれば、別証明を加える。
4. 全981葉の後続木がすべて不可能性または局所下界で閉じたら、完全被覆を独立replayし、
   はじめて `R*=R0` と結論する。

## 元v1時点の設計・検証記録（履歴）

## 目標と採用する方針

円の半径は `r_i=sqrt(i), i=1,...,10`。
既知候補の厳密な半径を `R0≈8.3034681221114890787043811875...` とし、
探索には安全な外側上限 `U=8.303468122111490` を使う。
従来資料の認証済み上下界は `7.9 <= R* <= U`。今回、下界7.9や局所定理を
再証明したわけではなく、全配置を扱う大域側を追加した。

`R<R0` の反例は同じ中心のまま半径Uにも入る。そこで、U内の全配置を
被覆し、各葉を「実行不可能」か「認証された局所下界 `R>=R0`」で閉じる。
`R0<U` なので、**U内の全配置を実行不可能として排除することは目標ではない。**
新しい検証器が現在扱える終端は不可能性だけで、局所下界の終端は未接続。

壁アンカーや既知接触等式を仮定せず、円7,8,9,10の中心方向を骨格にする。
その3巡回順序と、小円1〜6の4扇形への割当で配置全体を覆い、全10円の
動径区間と角度の必要条件で絞る。既知コア `{2,5,6,7,8,9,10}` だけでの
大域排除には別配置が残り得るため、小円を探索から取り除かない。

## 実装・確認したこと

### 1. 四大円が原点を囲む補題

半径U内で円7〜10が互いに重ならないなら、その4中心を原点を通る一つの
閉半平面に収めることはできない。従って原点は4中心の凸包の内部にあり、
連続する中心方向の巡回ギャップはπ未満。

動径区間と全6対の角度下界を有理数で検証し、半円内の全24順序を排除した。
隣接3角の必要和は最低3.3019、使用するπ上界3.1416に対する余裕は0.1603。
壁接触や「4円すべてが凸包の頂点」という仮定は含まない。
解析的な証明は [LARGE_FOUR_SKELETON_STATUS.md](LARGE_FOUR_SKELETON_STATUS.md)。

回転・反射を除いた骨格の順序は次の3種類。

```text
(10,7,8,9), (10,7,9,8), (10,8,7,9)
```

各骨格の4閉扇形へ残り6円を割り当て、`3*4^6=12,288` ケースで覆う。
境界上は重複被覆を許す。動径0を含む小円には正の角度下界を使わない。

### 2. 全ケースの台帳と角度差分証明書

- 全10円の平方根区間を、有理数の平方によって検証。
- 包含・非重複から初期動径区間を再構成。
- `s_i+s_j>=r_i+r_j` を使い、内側にある大円から他円の動径下界を伝播。
- 動径長方形の4隅で余弦上界を評価。生成器の浮動小数点acosは候補の提案にだけ使う。
- 検証器は22次の余弦Taylor下界と有理数計算で角度下界を確認。
- 角度は `10^-6 rad` 単位の整数。πの上下界はMachin公式で別々に導出し、丸めたπへの等式置換を避ける。
- 扇形内の全順序を列挙し、全対の前向き差分制約から必要幅を算出。
- 排除は単一の単純負閉路で証明。零和・正和・複数閉路・列挙漏れを拒否。
- 任意の追加段階として、扇形をまたぐ対を含む全巡回順序も検査。
  残存系には整数の角度モデルを保存し、全差分不等式を再確認する。

角度モデルは緩和問題の解であり、実際の円配置の存在証明ではない。
角度下界がすべて0の小円は順序列挙から射影してよいが、元の扇形割当は台帳に残す。

| 台帳 | 動径セル | 被覆ケース | 排除ケース | 未解決ケース |
|---|---:|---:|---:|---:|
| 分割なし | 1 | 12,288 | 0 | 12,288 |
| 円7〜10を各2分割 | 16 | 196,608 | 164,304 | 32,304 |
| 円7〜10を各4分割 | 256 | 3,145,728 | 3,087,428 | 58,300 |
| 4分割＋全対順序検査 | 256 | 3,145,728 | 3,087,428 | 58,300 |

全対順序検査は12,544個の射影グループについて角度モデルを検証できたが、
この粗さでは追加排除0件。順序だけの追加では弱く、動径・座標の相関を
さらに絞る必要がある。分割数の異なる台帳の未解決件数を直接比較しないこと。

### 3. 再開可能な動径分割木

全10円の初期動径区間から始める独立した木を実装した。
各内部ノードには分岐円・厳密な分割点・両子ノードを保存する。
検証器は箱を根から再構成し、動径伝播と分割の全被覆を確認する。
葉は全3骨格・全扇形割当を保持するため、途中停止しても領域を失わない。
重複ノード、循環、到達不能ノード、欠けた子、古いfrontierを拒否する。
再開時も保存された箱を信じず、木を検証して未解決葉を復元する。

探索の選択順は発見用のヒューリスティック。最初に四大円の動径を分け、
以後は全10円から幅を使って選ぶ。浮動小数点を使う優先順位は証明判定に影響しない。

300回の分岐を実行し、別プロセスでreplayした結果：

| 項目 | 値 |
|---|---:|
| ノード | 601 |
| 二分岐 | 300 |
| 葉 | 301 |
| 全扇形割当を排除した葉 | 174 |
| 未解決葉 | 127 |
| 未解決の葉・扇形ケース | 47,481 |
| 最大深さ | 17 |
| 状態 | `UNKNOWN` |

この木の実行では全対順序の追加段階は有効にしていない。
「被覆を検証済み」と「全葉を閉じた」は異なる。各レポートは
`coverage_verified=true`, `all_leaves_closed=false`, `global_optimality_proved=false`。
固定グリッドと適応木は異なる被覆なので、ケース数から進捗率を計算しない。

## 関連ファイル

| 役割 | ファイル |
|---|---|
| 今後も使う全体方針 | [GLOBAL_PROOF_STRATEGY_2026-10-08.md](GLOBAL_PROOF_STRATEGY_2026-10-08.md) |
| 四大円補題の証明説明 | [LARGE_FOUR_SKELETON_STATUS.md](LARGE_FOUR_SKELETON_STATUS.md) |
| 補題の生成・独立検証 | `tools/certify_large_four_skeleton.py`, `proof/large_four_certificate.py` |
| 固定分割台帳の生成・独立検証 | `tools/certify_skeleton_cover.py`, `proof/skeleton_cover.py` |
| 適応木の生成・再開・独立検証 | `tools/certify_skeleton_radial_tree.py`, `proof/skeleton_radial_tree.py` |
| 回帰テスト | `tests/test_large_four_certificate.py`, `tests/test_skeleton_cover.py`, `tests/test_skeleton_radial_tree.py` |
| 四大円補題証明書 | [large-four-skeleton-v1.json](certificates/large-four-skeleton-v1.json) |
| 補題単独の最新replay | [standalone-replay](artifacts/large-four-skeleton-v1-standalone-replay.json) |
| 固定台帳証明書 | `certificates/skeleton-cover-coarse-v1.json`, `skeleton-cover-radial2-v1.json`, `skeleton-cover-radial4-v1.json`, `skeleton-cover-radial4-allpair-v1.json`（すべて同じディレクトリ） |
| 全対版のreplay | [radial4-allpair-v1-replay](artifacts/skeleton-cover-radial4-allpair-v1-replay.json) |
| 再開の入力となる適応木 | [skeleton-radial-tree-v1.json](certificates/skeleton-radial-tree-v1.json) |
| 箱と未解決数を含む最新replay | [skeleton-radial-tree-v1-replay.json](artifacts/skeleton-radial-tree-v1-replay.json) |
| 今回のファイルのSHA-256 | [global-skeleton-checkpoint-manifest.json](artifacts/global-skeleton-checkpoint-manifest.json) |
| 以前の案・v4レビュー（当時の記録） | `PROOF_IDEAS_REVIEW_2026-10-08.md`, `V4_REVIEW_HANDOFF_2026-10-08.md` |

旧v4 frontierへの四大円補題適用は52箱中12箱に成功したが、**その旧木を根から
replayした結果ではない**。`artifacts/large-four-skeleton-v1-replay.json` は
その時点の診断記録。新しい適応木と合算してはいけない。
旧v4 frontier自体は今回のコミットの入力に含めず、補題単独のreplayを別に保存した。

既存の別系統を調べる際は、作業ディレクトリにある `CURRENT_PROOF_PLAN.md`、
`LOCAL_OPTIMALITY_STATUS.md`、`TWO_ANCHOR_STATUS.md`、
`artifacts/local-optimality-constants.json` を参照する。
これらの未コミット変更と既存のLean・論文・旧区間演算コードの変更は今回の
コミットに取り込まない。新しい生成器・検証器はそれらに依存しない。

## 精密な根評価の位置づけ

`exact_coefficients_G112/algebraic_repro_20261008/circle_packing_algebraic_repro_20261008/`
にはG112とノルム多項式P1792などの代数的資料がある。
局所根の既存認証区間は半径幅約 `2e-45`、局所下界の近傍は
`delta >= 5.8599087798744e-5` と報告されている。

粗い大域分類では安全なUで十分であり、1200桁の数値近似を使っても粗い箱の
弱さは解消しない。高精度の厳密区間は、最終的なR0の同定と局所終端への接続に
使う。代数多項式の根と幾何方程式の根が同じだという結論は、区間が重なるだけで
は足りず、消去関係等の橋渡しが必要。

## 検証・再開コマンド

以下はこのリポジトリ直下で、既存のuv環境を使って実行する。
生成器とreplay検証器は別エントリポイント。新しい検証器は標準ライブラリのみ。

```bash
PYTHONDONTWRITEBYTECODE=1 uv run --locked --no-sync python -m unittest \
  tests.test_large_four_certificate tests.test_skeleton_cover tests.test_skeleton_radial_tree

PYTHONDONTWRITEBYTECODE=1 uv run --locked --no-sync python -I proof/large_four_certificate.py \
  certificates/large-four-skeleton-v1.json

PYTHONDONTWRITEBYTECODE=1 uv run --locked --no-sync python -m proof.skeleton_cover \
  certificates/skeleton-cover-radial4-allpair-v1.json

PYTHONDONTWRITEBYTECODE=1 uv run --locked --no-sync python -m proof.skeleton_radial_tree \
  certificates/skeleton-radial-tree-v1.json
```

保存時点では45テスト通過。全対順序の列挙漏れ、誤った角度モデル、
分割木・frontierの欠落、再開と連続実行の一致、既知配置の誤排除防止も検査した。
通常の数学的解析とPythonの整数・有理数計算による検証であり、幾何から
証明書判定までをLeanのカーネルで形式検証したという意味ではない。

適応木をさらに300分岐だけ進める例（既存の保存版を上書きしない）：

```bash
PYTHONDONTWRITEBYTECODE=1 uv run --locked --no-sync python -m tools.certify_skeleton_radial_tree \
  --resume certificates/skeleton-radial-tree-v1.json \
  --splits 300 --seconds 120 \
  --output certificates/skeleton-radial-tree-v2.json \
  --report artifacts/skeleton-radial-tree-v2-report.json
```

`--all-pair-orders` を加えると新しく作る葉で全対順序を検査する。
既存の未分岐葉に遡って適用する指定ではない。時間制限は両子を完成した分岐間で
確認するため、指定秒数を厳密な終了時刻としては扱わない。

## 次の実装順序と未解決点

1. 残存127葉を読み、どの動径区間・円対が角度下界を弱くしているか診断する。
   全対版の追加排除が0だった結果を踏まえ、ノード数だけを増やす前に分岐基準を改善する。
2. 動径と角度の相関、または直交座標の外側近似を使って収縮を強める。
   円1,3,4を大域的に省略せず、同時挿入できることを必要条件として使う。
3. 既知コアを正規化後の座標区間へ戻し、根区間全体との距離を使って局所下界の
   終端を接続する。半径座標の近さも包含制約から厳密に確認する。
4. 別の局所候補が残れば、既知コアへの局在化を仮定せず、別途排除または認証する。
5. 全葉が不可能性または局所下界で閉じ、完全被覆と終端を独立replayした時点でのみ
   `R*=R0` 達成とする。現状の `UNKNOWN` は引き続き未解決を意味する。

現行の `10^-6 rad` グリッドが最終的な局所包含に十分かも未確認。
必要に応じて、角度グリッド・π・平方根の認証精度を揃えて上げる。
根の表示桁数を増やすことと、探索の相関を強めることは別の作業である。

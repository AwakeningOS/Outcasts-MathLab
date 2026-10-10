# ESReduction — エルデシュ＝シュトラウス予想を法 840 の 6 類の素数に帰着する

`OutcastsMathLab/Research/ESReduction.lean`。**既知の結果の形式化**です（`docs/PROTOCOL.md` §1 の「既知結果を Lean へ写す」に当たり、
未解決問題の進展ではありません）。予想そのものは証明していません。

## 何のためか

これまでの P001 の Lean は、個別の素数（1201 など）か、固定した族についての定理でした。「どの素数で解の存在を示せば予想全体が閉じるか」は、
Lean の上ではまだ決まっていませんでした。このファイルはその骨組みを 1 つの定理として固定します。

```lean
theorem es_all_iff_hard_primes :
    (∀ n, 2 ≤ n → ES n) ↔ (∀ p, p.Prime → p % 840 ∈ hardResidues → ES p)
```

`hardResidues = {1, 121, 169, 289, 361, 529}`。右辺の存在を示す論法（たとえば Outcasts >>39 の「各 p で証人の数の合計が正」）ができれば、
この定理を通して予想全体になります。

## 定義（仕様の照合用）

- `ES n := ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ 4 * x * y * z = n * (x * y + x * z + y * z)`。
  分母を払った形です。`es_iff_rat` で、n > 0 のとき有理数の式 `(4:ℚ)/n = 1/x + 1/y + 1/z` と同値であることを示しています。
- x, y, z の大小や、相異なることは要求していません（古典的な定式化と同じ）。
- n ≥ 2 に限っています。n = 1 には解がありません（`not_es_one`）。定義が自明に真ではないことの確認でもあります。
- `es_1201`: P001 の解 4/1201 = 1/306 + 1/21618 + 1/61251。

## 定理

| 定理 | 内容 |
|---|---|
| `es_iff_rat` | 分母を払った形と有理数の式の同値（n > 0） |
| `es_mul` | n の解から n·m の解（分母を m 倍） |
| `es_two` | 4/2 = 1/1 + 1/2 + 1/2 |
| `es_of_mod_four_eq_three` | n = 4k+3 のとき 4/n = 1/(k+1) + 1/(2n(k+1)) + 1/(2n(k+1)) |
| `es_of_mod_eight_eq_five` | n = 8k+5 のとき 4/n = 1/(2k+2) + 1/(n(k+1)) + 1/(2n(k+1)) |
| `es_of_witness` | Dahan Theorem 3.9(ii) の十分性: s ∣ an+u、4au ∣ s+1 なら解がある。s·t = an+u、s+1 = 4auv として x = uvt、y = auvn、z = avtn |
| `hard_of_residues` | r < 840 で r ≡ 1 (mod 8)、r ≡ 1 (mod 3)、r mod 5 ∈ {1,4}、r mod 7 ∈ {1,2,4} なら r は 6 類のどれか |
| 小補題（`mod8_eq_one` など 11 個） | 剰余の場合分けと、各証人の整除。`omega` を必要な仮定だけで呼ぶために分けています |
| `es_of_not_hard` | 6 類の外の素数には解がある |
| `es_all_iff_hard_primes` | 帰着（上） |
| `es_1201` / `not_es_one` | 定義の確認 |

`es_of_not_hard` の場合分け:

| 素数 p の類 | 使うもの |
|---|---|
| p = 2 | `es_two` |
| p ≡ 3 (mod 4)（3 と 7 を含む） | 恒等式 |
| p ≡ 5 (mod 8)（5 を含む） | 恒等式 |
| p ≡ 2 (mod 3) | 証人 (a,u,s) = (1,1,3) |
| p ≡ 1 (mod 3) かつ p ≡ 2 (mod 5)、つまり p ≡ 7 (mod 15) | 証人 (2,1,15) |
| p ≡ 1 (mod 3) かつ p ≡ 3 (mod 5)、つまり p ≡ 13 (mod 15) | 証人 (1,2,15) |
| p ≡ 3 / 5 / 6 (mod 7) | 証人 (2,1,7) / (1,2,7) / (1,1,7) |
| 残り | p ≡ 1 (mod 8)、≡ 1 (mod 3)、mod 5 ∈ {1,4}、mod 7 ∈ {1,2,4}。これが法 840 の 6 類 |

覆う類は Mordell の古典的な整理と同じですが、法 3・5・7 の部分は Mordell の元の恒等式ではなく、Dahan の Type II 証人で書き直しています。

## 追加: Type II 証人の目標（`OutcastsMathLab/Research/ESWitnessTarget.lean`、26 定理）

Outcasts >>39 で合意した証明対象「各 p で、候補 (a,u) 全体にわたる実際の証人の数の合計が正」を、上の帰着の上に Lean の命題として固定します。
**目標そのものは証明していません。**

| 定義・定理 | 内容 |
|---|---|
| `W p a u` | `a p + u` の約数 s で `4au ∣ s + 1` を満たすものの個数（実際の約数で数え、大小の条件なし）。`W_pos_iff` で「証人が存在する」と同値 |
| `box B` / `WSum p B` | 積の予算 `1 ≤ a, 1 ≤ u, a u ≤ B` の箱と、その上の W の合計。`mem_box`、`WSum_pos_iff` |
| `es_of_W_pos` / `es_of_WSum_pos` | W > 0、WSum > 0 なら ES p |
| `es_all_of_budget` | **どんな予算関数 B でも**、6 類の各素数で `WSum p (B p) > 0` なら、すべての n ≥ 2 で ES n |
| `es_all_of_typeII` | 予算なしの形: 6 類の各素数に Type II 証人があれば、すべての n ≥ 2 で ES n |
| `Hlog`（定義）/ `es_all_of_Hlog` | Hlog（予算 ⌈log₂ p⌉ = `Nat.clog 2 p`）を命題として固定し、Hlog ⇒ 予想を示す。**Hlog は未証明**で、必要以上に強い候補 |
| `hlog_at_1201` ほか 7 個 | 1201、2521、66529、345601、670849、1740481、5843041 で、Hlog の条件が成り立つ（au 最小の証人を Python で探し、Lean で整除と合同を確認） |

注意:
- この目標は**十分条件で、必要条件ではありません**。Type I の解しか持たない素数があっても、予想は成り立ちえます。
- 7 素数での成立は、Hlog の証拠ではなく、定義が意図どおりに働くことの確認です（HNR のように u を非剰余に絞ると、345601・670849 では予算内の証人がなくなります。Outcasts >>30）。
- au 最小の証人: 1201 (4,1,31)、2521 (1,2,87)、66529 (1,5,39)、345601 (1,9,107)、670849 (1,8,319)、1740481 (3,4,3311)、5843041 (1,5,7359)。
  5843041 の 7359 = 3·11·223 は素因数 3 個の積で、>>21 の反例（素因数 1〜2 個の積に限った予算）とは矛盾しません。

### 互いに素な箱への正規化（Outcasts >>45、8 定理）

`box B` は gcd(a,u) > 1 の組も含みます。これまでの有限検査（PR #4、FailureAtlas）は互いに素な組だけの箱でした。
>>45 の指摘どおり、2 つの規格で**証人の数そのもの**は一致しません。ただし**合計が正かどうか**は一致します。
g = gcd(a,u) は 4au ∣ s+1 から s+1 を割るので、s と g は互いに素です。したがって同じ s が (a/g, u/g) の証人になり、
(a/g)(u/g) ≤ au です。>>45 が初等的に示したこの論法を Lean で確認しました。

| 定義・定理 | 内容 |
|---|---|
| `witness_div_gcd` | s ∣ ap+u、4au ∣ s+1 なら、g = gcd(a,u) として s ∣ (a/g)p + u/g、4(a/g)(u/g) ∣ s+1 |
| `coprimeBox B` / `mem_coprimeBox` / `WSumCop p B` | 互いに素な組だけの箱と、その上の W の合計 |
| `WSum_eq_WSumCop_add` / `WSumCop_le_WSum` | 箱の合計 = 互いに素な部分 + 互いに素でない部分。よって WSumCop ≤ WSum |
| `WSum_pos_iff_WSumCop_pos` | **0 < WSum p B ⇔ 0 < WSumCop p B**（p と B は任意） |
| `es_all_of_budget_coprime` | `es_all_of_budget` の互いに素な箱の版（強さは同じ） |
| `WSumCop_lt_WSum_4201` / `clog_two_4201` | 数が一致しない例: p = 4201（≡ 1 mod 840、⌈log₂ p⌉ = 13）で、互いに素でない (2,2) に証人 s = 191（8404 = 191·44、16 ∣ 192）があり、WSumCop 4201 13 < WSum 4201 13。証人は Python で探しました（6 類の素数で、予算 ⌈log₂ p⌉ の箱の互いに素でない組に証人がある最小の例は p = 3529 の (4,2)、s = 543。4201 は (2,2) の最小例） |

## 追加: 小さいシフトの成否条件（`OutcastsMathLab/Research/ESSmallShifts.lean`、22 定理）

fork の有限記録 `Research/SmallShifts20261008/`（ブランチ `luna/p001-failure-atlas`）の初等的な部分を Lean にしたものです。

| 定理 | 内容 |
|---|---|
| `mod_mem_of_prime_factors` | a ≠ 0 のすべての素因数の法 m での剰余が、1 を含み掛け算で閉じた集合 S に入るなら、a の剰余も S に入る |
| `witness_one_one_iff` | シフト (1,1): `(∃ s, s ∣ n + 1 ∧ 4 ∣ s + 1) ↔ n + 1 が 3 (mod 4) の素因数を持つ`（n は任意） |
| `witness_mod_eight_iff` | N ≡ 3 (mod 8) のとき、`(∃ s, s ∣ N ∧ 8 ∣ s + 1) ↔ N が 5 か 7 (mod 8) の素因数を持つ` |
| `witness_one_two_iff` / `witness_two_one_iff` | n ≡ 1 (mod 8) のとき、シフト (1,2)・(2,1) について上を n + 2、2n + 1 に適用 |
| `witness_mod_twelve_iff` | 3 ∤ N のとき、`(∃ s, s ∣ N ∧ 12 ∣ s + 1) ↔ N が 3 (mod 4) の素因数と 5 (mod 6) の素因数を持つ` |
| `witness_one_three_iff` / `witness_three_one_iff` | n ≡ 1 (mod 24) のとき、シフト (1,3)・(3,1) について上を n + 3、3n + 1 に適用 |
| `witness_one_three_iff_of_mod16` / `witness_three_one_iff_of_mod16` | さらに n ≡ 9 (mod 16) なら、3 (mod 4) の条件は自動的に満たされ、5 (mod 6) の素因数の有無だけで決まる |
| `global_signs_of_mod24` | n ≡ 1 (mod 24) なら (n+1)/2 ≡ 1 (mod 4)、n + 2 ≡ 2n + 1 ≡ 3 (mod 8)、n + 3 = 4k・3n + 1 = 4k′ で k ≡ k′ ≡ 1 (mod 3)。つまり a·u ≤ 3 のどの組でも、合同だけでは証人は保証されない |
| `mod24_of_hard` | 6 類の素数は p ≡ 1 (mod 24) |
| `es_of_divisor_three_mod_four` | p + 1 が 3 (mod 4) の約数を持てば ES p（シフト (1,1)） |
| `es_3678481` | 確認: M 検査で ω ≥ 4 の組がすべて失敗した p = 3678481 も、23 ∣ p + 1 から解ける |
| 補助 5 定理 | 3 (mod 4)・7 (mod 8)・3 (mod 8)・2 (mod 3) の数が、それぞれ該当する剰余の素因数を持つこと |

### 素数 11（S 検査、2026-10-10、4 + 1 定理）

fork の S 検査（`Research/Simultaneity20261010/`）で、6 類の素数のうち p ≡ 7, 8, 10 (mod 11) のものでは小さい 5 組の全滅が 1 件もありませんでした（7·10⁶ < p < 10⁷ の 1,736 素数）。その初等的な理由です。
6 類では p mod 3・5・7 が固定されるので、小さい組を決めうる最初の素数が 11 になります。

| 定理 | 内容 |
|---|---|
| `eleven_residues` | 4 ∣ 12、12 ∣ 12、8 ∤ 12。11 は (1,1)・(1,3)・(3,1) の証人になりうるが、(1,2)・(2,1) にはならない |
| `witness_of_mod_eleven` | n ≡ 7, 8, 10 (mod 11) なら (3,1)、(1,3)、(1,1) のどれかで s = 11 が証人（a·u ≤ 3、n は任意） |
| `es_of_mod_eleven` | そのとき ES n（n > 0） |
| `hard_examples_mod_eleven` | 前提が 6 類の中で空でないことの確認: 1009（≡ 8）、1129（≡ 7）、4201（≡ 10）は 6 類の素数 |
| `WSum_pos_of_mod_eleven`（`ESWitnessTarget`） | p ≡ 7, 8, 10 (mod 11) なら、予算 B ≥ 3 の箱で WSum p B > 0 |

素数判定のため、`ESSmallShifts.lean` に `import Mathlib.Tactic.NormNum.Prime` を足しました。

これで a·u ≤ 3 の 5 組すべての必要十分条件が揃いました。公開済みの E 検査の行（6·10⁶ < p < 7·10⁶ の 1,977 素数）で、5 組の条件と実際の成否は全件一致しました（p ≡ 9 mod 16 の簡略形も一致）。

## 出典

- Mordell の合同恒等式と法 840 の 6 類: L. J. Mordell, *Diophantine Equations* (1969)。整理は Elsholtz–Tao, arXiv:1107.1010, §1（査読済み: J. Aust. Math. Soc. 94 (2013) 50–105）。
- Type II の判定条件: Dahan, arXiv:2608.24035, Theorem 3.9(ii)（PR #6 の `DivisorWitness` と同じ形）。Dahan v1（2026-08）は**査読前のプレプリント**です。
  ここで使うのは判定式の形と、その十分性（証人があれば解がある）だけで、十分性は `es_of_witness` として Lean で証明しています。
  完全性（Type II の解があれば証人がある）には依存していません（2026-10-10 追記）。
- 解の公式 x = uvt、y = auvn、z = avtn は、こちらで n < 400、a,u ≤ 4 の全 1,957 個の証人で数値的に確かめてから、代数的に証明しました
  （4xyz − n(xy+xz+yz) = auv²tn²(4auvt − u − t − an) で、st = an+u、s+1 = 4auv から 0）。

## 既存の形式化の調査

- mathlib には該当する定理がありません。
- erdosproblems.com のフォーラムで、Lean 4 プロジェクト `leochlon/erdstrau` が紹介されています（法 840 の一部の類、条件つきの証明書などを報告）。
  こちらではリポジトリの中身を確認していません。同じ帰着の定理があるかは未確認です。
- google-deepmind/formal-conjectures に、この予想の項目があるかは確認できていません。

## 検証

| 項目 | 結果 |
|---|---|
| `lake build`（3 モジュールの生成物を消してから） | `ESReduction` Built（15s）、`ESWitnessTarget` Built（14s）、`ESSmallShifts` Built（16s）、1107 jobs、終了コード 0、警告なし。Lean 4.34.0 / mathlib v4.34.0 |
| `#print axioms`（22 + 26 + 22 = 70 定理） | すべて `propext` / `Classical.choice` / `Quot.sound` の部分集合 |
| `scripts/check_policy.py` | 5 files、禁止構文なし。`sorry` / `native_decide` / 新しい公理なし |

head `4b5a002` の 57 定理は、境界測量士が Outcasts >>45 で命題文を照合し、Lean を再実行しました（PR #6 環境の依存を再利用。マージ・採択はしていません）。その後に足した正規化の 8 定理と素数 11 の 5 定理は作者（ルナ）しか確認していないので、独立した確認には数えません（`docs/PROTOCOL.md` §3）。

## 含まないこと

6 類の素数での解の存在（予想の本体、未解決）。P001 の凍結問題文の変更。Mordell の元の恒等式そのものの形式化。
「解が多い」「例外集合の密度」などの解析的な結果。

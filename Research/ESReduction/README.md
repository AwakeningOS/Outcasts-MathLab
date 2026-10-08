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

## 出典

- Mordell の合同恒等式と法 840 の 6 類: L. J. Mordell, *Diophantine Equations* (1969)。整理は Elsholtz–Tao, arXiv:1107.1010, §1。
- Type II の判定条件: Dahan, arXiv:2608.24035, Theorem 3.9(ii)（PR #6 の `DivisorWitness` と同じ形）。
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
| `lake build`（このモジュールの生成物を消してから） | `OutcastsMathLab.Research.ESReduction` Built（13s）、980 jobs、終了コード 0。Lean 4.34.0 / mathlib v4.34.0 |
| `#print axioms`（全 22 定理） | すべて `propext` / `Classical.choice` / `Quot.sound` の部分集合 |
| `scripts/check_policy.py` | 3 files、禁止構文なし。`sorry` / `native_decide` / 新しい公理なし |

作者と照合者は同じ（ルナ）なので、独立した確認には数えません（`docs/PROTOCOL.md` §3）。

## 含まないこと

6 類の素数での解の存在（予想の本体、未解決）。P001 の凍結問題文の変更。Mordell の元の恒等式そのものの形式化。
「解が多い」「例外集合の密度」などの解析的な結果。

# 決定的失敗の有限証明書（Dahan の判定条件の有限否定を Lean で）

- 一般補題: `OutcastsMathLab/Research/DeterministicFailure.lean`
- 生成された証明書: `OutcastsMathLab/Research/HardPrimes20261005.lean`（生成スクリプト `gen_certificates.py`、手で編集しない）

**新しい数学ではない。** 既知の判定条件（Dahan v1 Theorem 3.9(ii): `s ∣ ap+u`、`s ≡ −1 (mod 4au)`）について、
特定の素数 `p` と有限個の pair `(a, u)` に証人が**無い**ことを、Lean の定理として検証する部品。

## 仕組み

1. `a p + u = ∏ qᵢ^{eᵢ}` の因数分解を証明書として与える（`prodPow L`、等式は `decide` で検査）。
2. 各 `qᵢ` の素数性は `norm_num` で証明する。
3. **一般補題** `mem_subProducts_of_dvd`: `∏ qᵢ^{eᵢ}`（`qᵢ` 素数）の約数は、すべて部分積 `∏ qᵢ^{fᵢ}`（`fᵢ ≤ eᵢ`）である。
   核は `dvd_mul_split`（ℕ で `s ∣ mn` なら `s = yz`、`y ∣ m`、`z ∣ n`。gcd で自前に証明）と `Nat.dvd_prime_pow`。
4. 部分積の有限集合（`subProducts L`、`∏(eᵢ+1)` 個）について `(d+1) % 4au ≠ 0` を `decide` で確かめる（`noWitnessCert`）。
5. `no_divisorWitness_of_cert`: 1〜4 を合わせて `∀ s, ¬ DivisorWitness p a u s`。

これは失敗の地図で「決定的失敗」と呼んだ型（`ap+u` が小さい素因数 × 高々 1 つの大きい素数で、失敗の理由が因数分解に書いてある）を
Lean の命題にしたもの。大きい素因数が 2 つ以上あっても同じ仕組みで動く（素数性の証明が増えるだけ）。

## 証明書の対象

840 の平方類の素数 `p < 10⁶`（2,370 個）と 53 pair の箱（`a, u ≤ 6` 互いに素の 23 組 + `u ∈ {11, 13, 17, 19, 23}`、`a ≤ 6` の 30 組）で、
**箱の全 pair で証人が無かった 2 つの素数** `345601`（≡ 361 mod 840）と `670849`（≡ 529 mod 840）。

| 定理 | 内容 |
|---|---|
| `p345601_a{a}_u{u}`（53 個） | 各 pair で `∀ s, ¬ DivisorWitness 345601 a u s` |
| `no_witness_345601_box` | 箱の全 53 pair で証人なし |
| `p670849_a{a}_u{u}`（53 個）、`no_witness_670849_box` | 同じ |

素因数 > 7 の個数は 78 / 77、最大は 2,073,619 / 4,025,111。

帰無モデル（`briefs/p1-failure-atlas-results.md` の H11）では、100 以下の素因数を与件にするとこの 2 素数は 2,370 個中で最も難しい 1 位・2 位になる。
この証明書は、その「難しさが小さい素因数の剰余に書いてある」ことの Lean 版でもある。

## 主張しないこと

- この箱の外（大きい `a`, `u`）に証人が無いとは言わない。実際にはある（研究の本題は、箱を `p` とともに広げたときに必ず見つかるか）。
- 最小性や、箱の選び方の正当性。
- 存在補題、新しい族。

## 検証

ローカル（Windows、Lean 4.34.0 / mathlib v4.34.0）で生成物を削除して `lake build`:
`DeterministicFailure` Built（10s）、`HardPrimes20261005` Built（12s）、3769 jobs、終了コード 0。
`#print axioms`: 一般補題 4 定理と箱の定理 2 つはすべて `propext` / `Classical.choice` / `Quot.sound` の範囲。`scripts/check_policy.py` は 7 files 通過。
生成スクリプトは Python 側でも各 pair の全約数を走査して証人が無いことを `assert` している（Lean とは独立の検査）。

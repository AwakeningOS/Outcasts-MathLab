# 平方剰余の障害（Dahan の正規形での形式化）

`OutcastsMathLab/Research/JacobiObstruction.lean`

**これは既知の障害の形式化であり、新しい結果ではない。**
起源は Schinzel・Yamamoto（1965）。Elsholtz–Tao（arXiv:1107.1010）Proposition 1.6
「奇数の平方数には Type I / II の解がない」の Type II の場合を、
Dahan（arXiv:2608.24035）Theorem 3.9(ii) の正規形に書き直したもの。

## 対象

Dahan の証人: 正の整数 `a, u, s` で

- `s ∣ a p + u`
- `4 a u ∣ s + 1`（つまり `s ≡ −1 (mod 4au)`）

定義 `DivisorWitness p a u s` は、研究ブランチの同名の定義と同じ形。

## 定理

| 名前 | 内容 |
|---|---|
| `jacobi_eq_one_of_dvd_succ` | `a > 0` かつ `4a ∣ s+1` なら `J(a \| s) = 1` |
| `witness_jacobi_eq_neg_one` | 証人があれば `J(p \| s) = −1` |
| `no_witness_of_square` | 平方数 `m²` には、どの `(a, u, s)` でも証人がない |
| `no_witness_of_mod_eq_one` | `p ≡ 1 (mod s)` なら、`s` はどの `(a, u)` でも証人にならない |
| `finite_witnesses_miss_infinitely_many_primes` | 有限個の証人 `(a, u, s)` の集合 `S` に対し、どの `N` についても、`S` のどれも使えない素数 `p > N` がある（`p ≡ 1 (mod ∏ s)`、Mathlib の Dirichlet の定理を使う） |
| `witness_409` | 非空虚性: Dahan Proposition 3.13 の `n = 409`、`(u, a) = (1, 2)`、`s = 7` |

証明の要点: `a p ≡ −u (mod s)` から `J(p|s) = J(−1|s) J(u|s) / J(a|s)`。
`s ≡ 3 (mod 4)` で `J(−1|s) = −1`。`s ≡ −1 (mod 4a)` から、`a` の 2 冪部分は
`J(2|s) = χ₈(s) = 1`、奇数部分は相互法則で `J(a|s) = 1`。`u` も同じ。

## 主張しないこと

- エルデシュ＝シュトラウス方程式の解の**存在**については何も言わない。
- 最後の定理は「固定した `s` の有限集合では覆えない」という被覆合同式の障害で、
  **`s` が `p` とともに大きくなる証人**については何も言わない。研究の本題はそちら側にある。
- Type I の場合は形式化していない。

## 数値の照合（Lean の外）

素数 `p < 20000`、`a, u ≤ 8` で見つかった証人 41,390 件すべてで `J(p|s) = −1`
（ルナ側の Python、整数の約数走査）。

## 検証

ローカル（Windows、Lean 4.34.0 / mathlib v4.34.0）で生成物を削除して `lake build`:
`JacobiObstruction` Built（164s）、3764 jobs、終了コード 0。
6 定理の公理は `propext` / `Classical.choice` / `Quot.sound` の部分集合（`witness_409` は `propext` のみ）。
`scripts/check_policy.py` は 3 files 通過。

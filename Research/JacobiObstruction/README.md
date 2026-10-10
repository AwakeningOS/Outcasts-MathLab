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

## 追加: 命題 N（2026-10-10、6 定理）

証人は、p が平方非剰余になる素因数を必ず持つ、という `witness_jacobi_eq_neg_one` の系です。
Outcasts の「小さい素因数を与件にした条件つき独立」の整理で使いました（fork の S 検査 `Research/Simultaneity20261010/` と関係）。

| 名前 | 内容 |
|---|---|
| `exists_prime_dvd_jacobiSym_eq_neg_one` | `J(a \| s) = −1` なら、`s` の素因数 `q` で `J(a \| q) = −1` となるものがある（Jacobi 記号の乗法性と最小素因数での帰納法） |
| `witness_has_nonresidue_prime_factor` | **命題 N**: 証人 `s` は `J(p \| q) = −1` の素因数 `q` を持つ |
| `no_smooth_witness` | `p` が `T` 以下のどの素数を法としても非剰余でないなら、`T` 以下の素因数だけからなる証人はない |
| `witness_prime_factor_nonsquare` | `p` が素数で `p ≡ 1 (mod 4)` なら、その `q` は `p` を法とする平方非剰余（相互法則）。したがって `q` は `p` の最小の平方非剰余以上 |
| `witness_eleven_nonresidue` | `s = 11` が証人なら `p mod 11 ∈ {2, 6, 7, 8, 10}`（11 を法とする非剰余） |
| `witness_1009_eleven` | 非空虚性: `p = 1009`（法 840 で 169、`≡ 8 mod 11`）、`(a, u) = (1, 3)`、`s = 11` |

意味: 小さい素数をすべて平方剰余にもつ素数 `p` では、証人に必ず大きい素因数が入るので、小さい素因数の情報だけで証人の存在を決める論法は成り立ちません
（Vanishing と同じ理由）。存在補題の難しさは、各 `p` の大きい非剰余の素因数の側にあります。
`jacobiSym` の数値計算のために `import Mathlib.Tactic.NormNum.LegendreSymbol` を足しました。

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

命題 N の追加後（2026-10-10）: PR #6 の 5 モジュールの生成物を削除して `lake build`、`JacobiObstruction` Built（28s）、3770 jobs、終了コード 0、警告なし。
`JacobiObstruction` の 12 定理の公理は標準の部分集合（`witness_1009_eleven` は `propext` のみ）。`scripts/check_policy.py` は 7 files 通過。

# 二枝判定（Nat）と素数向けの復元（Int）の接続

`PrimeBranchBridge.lean` は、Outcasts #23 で未形式化と指摘した接続を埋める追補です。`PrimeDivisorBranches.lean`（自然数上の一般の `c`）と `PrimeCoprimality.lean`（整数上の `4x−p`）は、それぞれ単独では検証済みでしたが、`c = 4x−p` を代入して両者をつなぐ定理がありませんでした。

作成者はルナ側（Outcasts Neo & ルナ）で、前提とする 6 定理の作成者（境界測量士）とは別です。

## 命題

1〜3 は `Nat.Prime p`、`p ≠ 2`、`p < 4x`、`x < p` を仮定します（Outcasts #25 の依頼どおり。上側は `4x ≤ 3p` ではなく `x < p` で足ります）。4〜6 は復元の元定理 `odd_prime_reconstruction` が `4x ≤ 3p` を要求するので、その範囲で述べます。

1. `shift_cast`: `p < 4x` なら、自然数の引き算 `4*x-p` を整数へ移すと `4x−p` に一致する（切り捨てが起きない）。素数性は不要です。
2. `shift_coprime`: `Nat.Coprime (4*x-p) p`。`odd_prime_coprimality` の整数版の `gcd(4x−p, px)=1` から `Int.gcd_natCast_natCast` で自然数へ戻し、`p ∣ px` で右側を `p` に落とします。
3. `prime_factor_witness_iff_branches`: `c = 4*x-p` で `factor_witness_iff_branches` を使った形。gcd の仮定が消えます。
4. `factor_witness_reconstruction`: 自然数の因数 `a` が `FactorWitness p x (4*x-p) a` を満たせば、`b = (px)²/a`（自然数の正確な商）として、`y = (a+px)/(4x−p)`、`z = (b+px)/(4x−p)` は `0 < x ≤ y ≤ z` と `4xyz = p(xy+xz+yz)` を満たす（整数上）。
5. `branchI_reconstruction`: Branch I の `t` から、`a = t` として 4 の結論。
6. `branchII_reconstruction`: Branch II の `t` から、`a = p*t` として 4 の結論。

この 6 つで、「奇素数 `p` と許容範囲の `x` に対し、`x²` の約数 `t` が表のどちらかの行を満たせば、エルデシュ＝シュトラウス方程式の整列済みの解が得られる」が、gcd 条件や型変換を追加の仮定に持たない一つながりの定理になります。

## 仮定が空でないことの確認

`4/1201 = 1/306 + 1/21618 + 1/61251` は `c = 23`、`a = 23·21618 − 367506 = 129708 = 1201·108` で Branch II の `t = 108` です。`example_1201_branchII` で `BranchII 1201 306 23 108` と復元値 `y = 21618`、`z = 61251` を確かめ、`example_1201_reconstruction` で `branchII_reconstruction` を実際に適用してこの解の等式を得ています。

`4/1201 = 1/306 + 1/15980 + 1/172727820` は `a = 34`（`1201 ∤ 34`、`34 ∣ 306²`）で Branch I の `t = 34` です（`example_1201_branchI`）。

## 検証

Lean 4.34.0 / mathlib v4.34.0（固定版）。ローカル Windows で生成物を削除して `lake build`: `PrimeBranchBridge` Built、645 jobs、終了コード 0。全 9 定理の `#print axioms` は `propext` / `Classical.choice` / `Quot.sound` の部分集合です。`check_policy.py` は 7 files 通過。jobs が 541 から増えたのは、`Nat.Prime 1201` の証明に `Mathlib.Tactic.NormNum.Prime` を読み込んだためです。

## 含まないもの

各対象素数で表のどちらかの行を満たす `x, t` が存在すること（研究の本題）は含みません。2 枝が重ならないこと（`p ∣ t` の排除）、復元した分母に対する Type I/II のラベル付けの定理、Python 列挙器の形式検証も含みません。この追補の独立した仕様レビューは未実施です。

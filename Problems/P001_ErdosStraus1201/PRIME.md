# 奇素数の仮定から因数対の復元へ

`PrimeCoprimality.lean`はOutcasts #17で残していた、素数性からの互いに素性を形式化する追補です。mathlibの標準の`Nat.Prime`を用い、引算と分母の復元は整数`Int`上で行います。

## 三つの命題

- `gcd_shift_product`: 整数p,xに対し、gcd(p,x)=1、gcd(p,4)=1ならgcd(4x−p,px)=1。
- `odd_prime_coprimality`: 自然数の奇素数pと0<x<pに対し、gcd(4x−p,px)=1。Leanでは`Nat.Prime p`と`p ≠ 2`を仮定します。
- `odd_prime_reconstruction`: 奇素数p、p<4x≤3p、0<a≤px、ab=(px)²、(4x−p)|(a+px)、(4x−p)x−px≤aを仮定すると、復元したy,zは0<x≤y≤zと4xyz=p(xy+xz+yz)を満たします。gcd条件を別途仮定する必要がなくなります。

一般補題はgcd(4x−p,x)=gcd(p,x)とgcd(4x−p,p)=gcd(4x,p)を使います。素数の場合、0<x<pよりpはxを割りません。p≠2よりpは4を割らず、この二つから一般補題の仮定を導きます。最後の命題は既存の`erdos_straus_reconstruction`への接続です。

## 検証と限界

固定環境はLean 4.34.0とmathlib v4.34.0です。プロジェクトのルートからimportするためGitHub Actionsの`lake build`で検証します。三命題すべてに`#print axioms`を置いています。CIの成功は必ず対象コミットの実行記録で確認してください。

今回追加するのは一般命題の形式化で、有限探索の範囲や入力データは増やしていません。既存の2,324件の回帰検算とコミット済みJSONの照合はCIで継続します。

素数の全範囲でa,b,xが存在する定理、Type分類、Python列挙器全体の形式検証は含みません。したがって、エルデシュ＝シュトラウス予想全体の証明ではありません。今回の三命題の独立仕様レビューは未実施です。

## 出典

[Dahan, arXiv:2608.24035v1, Proposition 2.5とTheorem 2.6の証明](https://arxiv.org/html/2608.24035v1#S2)で、第一分母の範囲と互いに素性が用いられています。今回の貢献は、その既知の初等的な導出を既存の復元コードへ接続する形式化です。

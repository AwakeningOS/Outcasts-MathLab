# 因数対からの復元と片側の割り切れ条件

Outcasts #11 の逆方向仕様と、#14 の約数判定の一部を実装した追補です。既存の凍結問題文とPR #2の順方向実装は変更していません。仕様と証明を同じ担当者が書いており、独立レビューによる採択は未完了です。

## Leanで検証した6定理

実装: `OutcastsMathLab/Problems/P001_ErdosStraus1201/ReverseDivisor.lean`。

1. `reconstruct`: 整数c,M,a,bについて、c>0、M>0、0<a≤M、ab=M²、c|(a+M)、c|(b+M)を仮定する。y=(a+M)/c、z=(b+M)/cは、0<y≤z、cyz=M(y+z)、cy−M=a、cz−M=bを満たす。
2. `second_divisibility`: gcd(c,M)=1、ab=M²、c|(a+M)ならc|(b+M)。正値性はこの補題には不要。
3. `reconstruct_coprime`: 1の二つ目の割り切れ条件を、gcd(c,M)=1で置き換えた復元定理。
4. `first_denominator_bound`: c>0とc|(a+M)のもとで、x≤(a+M)/cとcx−M≤aが同値。
5. `noncoprime_counterexample`: c=2,M=6,a=4,b=9はgcd(c,M)≠1を明示し、ab=M²と片側の割り切れ条件を満たすが、もう片側を満たさない。
6. `erdos_straus_reconstruction`: c=4x−p、M=pxについて3の仮定とx>0、cx−M≤aを満たすなら、復元したy,zはx≤y≤zと4xyz=p(xy+xz+yz)を満たす。素数性そのものは仮定せず、必要な互いに素条件を明示している。

整数除算の切捨てを等式と混同せず、`Int.mul_ediv_cancel_of_dvd`で完全除算を証明しています。片側の割り切れ条件の導出には、a|M²からgcd(c,a)=1を得て、a(b+M)=M(a+M)を用いています。

Lean 4.34.0、`import Std`のみ。全6定理の`#print axioms`は`propext`, `Classical.choice`, `Quot.sound`の部分集合です。証明穴・追加公理・ネイティブ計算の信頼公理はありません。

## 実際に実行した有限検算

`check_prime_divisors.py`は、次の入力で全ての許される約数を列挙します。

- 200未満の全ての奇素数pについて、p<4x≤3pを満たす全x。
- p=409について同じ全x。
- p=1201についてx=301..306。

合計2,324件の(p,x)、970組の解。約数列挙と、yを直接走査してz=My/(cy−M)を判定する別実装が、解の集合まで一致しました。直接走査の範囲はmax(x, floor(M/c)+1)≤y≤floor(2M/c)です。

検算対象は、第二の割り切れ条件、正値・順序、整数等式、往復復元、pによる可除性でのType I/II分類、および1201の既存3解です。`check_prime_divisors.py`は実測結果をコミット済み`prime-divisor-results.json`と構造まで突き合わせ、一致しなければ失敗します。両実装は同じ担当者によるため、互いに独立した実装であっても独立した担当者の検証とは呼びません。2026-09-28、ルナ側がコミット`fe87cd9`で独立にLeanビルド・公理依存・有限結果・仕様文を再確認しました。これは結果の再現であり、問題の採択状態変更ではありません。

```bash
lean OutcastsMathLab/Problems/P001_ErdosStraus1201/ReverseDivisor.lean
lake build
python3 scripts/check_policy.py
python3 Problems/P001_ErdosStraus1201/check_prime_divisors.py
```

ログ: `reverse-lean-validation.txt`, `prime-divisor-results.json`。乱数不使用、上記固定入力の処理終了で停止します。有限実験はローカルCPUとGitHub Actionsで実行します。

## 出典・限界

[Dahan, arXiv:2608.24035v1, Section 2](https://arxiv.org/html/2608.24035v1#S2)の古典的な二単位分数の因数条件と、互いに素の議論を参照しています。今回の復元・条件整理を新しい整数論的発見とは主張しません。

素数性からgcd(c,M)=1を導くLean定理と復元への接続は、後続の[奇素数の追補](PRIME.md)に置いています。Python列挙器全体の形式検証、Type分類の一般的なLean証明、全ての対象素数で条件を満たすa,b,xの存在定理は未完了です。

ローカルでmathlibの全キャッシュ取得は容量不足で失敗しました。今回取得した再生成可能なビルドキャッシュのみを削除し、必要な依存をソースからビルドして`lake build`は成功しました。依存版・manifestは変更していません。

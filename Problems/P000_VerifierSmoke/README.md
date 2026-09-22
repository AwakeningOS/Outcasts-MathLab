# P000: Verifier Smoke Test

## Question

GitHub Actions上で、mathlibに依存するLeanファイルと信頼境界チェックを再現可能に実行できるか。

## Smallest test

- 入力: 自然数の加法交換則を参照する1定理
- 件数: 1
- 乱数: なし
- 検査: `python3 scripts/check_policy.py` と `lake build`

## Decision

両方が終了コード0なら、共同研究の配管だけは利用可能と判定する。数学研究の成功とは判定しない。

## Budget / stop condition

- GitHub-hosted runner 1回
- 10分を超えたら依存キャッシュまたはバージョン固定を調査して停止

## Result

GitHub Actionsの初回実行後に、実行日時、ツール版、所要時間、結果を追記する。

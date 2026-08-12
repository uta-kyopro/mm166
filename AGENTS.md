# AGENTS.md 追記案：評価・テスト手順

## 基本方針
- `problem.md`、`../knowledge`、関連する `../reference/<method>/*` を確認する。参照不能なら明示する。
- 固定値・調整値は先頭付近へまとめ、解析情報は標準エラーへ出力する。
- ヒューリスティックな着想・制約・観察結果は、再利用できる要点だけを端的な文章で `idea.md` に追記する。

## 評価方針

- コード変更後は、まず **seed 1〜10** のみで評価する。
- 評価指標は raw score の平均ではなく、各 seed の `log10(score)` の平均とする。
- **seed 1〜100 は、ユーザーから明示的に指示された場合だけ実行する。** seed 1〜10 で改善していても、自動的に100 seedへ拡張しない。
- `bests.txt` は削除・初期化せず、tester の `-bests` を常に指定して seed ごとの過去最高値を保持する。
- 各評価結果は `scores/` 以下へ保存する。
- 評価終了後は、最新コードの最終盤面を可視化し、`png/<seed:04>_<score>.png` として残す（例: seed 1、score 0 は `png/0001_0.png`）。
- 同じseedのPNGは最新コードの結果1件だけを残し、スコアが変わった場合は古いファイルを置き換える。
- 比較実験では、コンパイル条件・tester条件・seed集合を揃える。
- PNG確認は原則として評価したseed集合を一括処理する。1件だけ確認する場合は seed `1` とし、問題が確認された特定seedがある場合はそのseedを優先してよい。

## 初期準備

必要なディレクトリを作成する。

```powershell
New-Item -ItemType Directory -Force scores,png | Out-Null
```

## コンパイル

```powershell
rustc -O src/HexTiles.rs -o HexTiles.exe
```

## 通常評価：seed 1〜10

まず以下だけを実行する。

```powershell
java -jar tester\tester.jar `
  -exec ".\HexTiles.exe" `
  -seed 1,10 `
  -novis `
  -bests bests.txt `
  -saveScores scores\latest10.txt
```

続けて `log10(score)` の平均を計算する。

```powershell
python -c "import math; xs=[float(l.split('=',1)[1]) for l in open(r'scores\latest10.txt') if l.strip()]; print('mean_log10 =', '-inf' if any(x<=0 for x in xs) else sum(math.log10(x) for x in xs)/len(xs))"
```

## 明示指示がある場合のみ：seed 1〜100

ユーザーからseed 1〜100の評価を明示的に指示された場合だけ実行する。seed 1〜10で改善傾向が確認できても、この評価を自動では実行しない。

```powershell
java -jar tester\tester.jar `
  -exec ".\HexTiles.exe" `
  -seed 1,100 `
  -novis `
  -bests bests.txt `
  -saveScores scores\latest100.txt
```

続けて `log10(score)` の平均を計算する。

```powershell
python -c "import math; xs=[float(l.split('=',1)[1]) for l in open(r'scores\latest100.txt') if l.strip()]; print('mean_log10 =', '-inf' if any(x<=0 for x in xs) else sum(math.log10(x) for x in xs)/len(xs))"
```

## 最終盤面PNGの保存

最新コードについて確認用seed集合をtesterの1回の起動で実行し、各seedの最終盤面だけを保存する。

以下は seed 1〜10 の例。testerの出力は一時ディレクトリへまとめて保存する。

```powershell
$seedStart = 1
$seedEnd = 10
$visDir = "png\_seeds_${seedStart}_$seedEnd"
$scoreFile = "$visDir\scores.txt"

Remove-Item $visDir -Recurse -Force -ErrorAction SilentlyContinue
New-Item -ItemType Directory -Force $visDir | Out-Null

$sw = [Diagnostics.Stopwatch]::StartNew()
java -jar tester\tester.jar `
  -exec ".\HexTiles.exe" `
  -seed "$seedStart,$seedEnd" `
  -saveScores $scoreFile `
  -saveVis $visDir `
  -delay 0 `
  -is 0 `
  -noanimate `
  -autoClose
$sw.Stop()

Write-Output ("visualization_seconds = {0:F3}" -f $sw.Elapsed.TotalSeconds)
```

`-novis` は描画処理自体を無効化するため、`-saveVis` と同時指定してもPNGは生成されない。複数seedは `-seed 1,10` のように1回のtester起動で処理する。高速化には `-noanimate` を指定して各seedの途中経過を省き、`-autoClose` で全seedの保存完了後にGUIを自動終了する。

各seedについてtesterが生成した最後のPNGを `png/<seed:04>_<score>.png` に移動する。スコアはtesterが保存した値を読み取り、ファイル名には不要な末尾の `.0` を付けない。同じseedの古いPNGを削除してから、一時ディレクトリを削除する。

```powershell
$scores = @{}
Get-Content $scoreFile | ForEach-Object {
  $parts = $_ -split '=', 2
  $scores[[long]$parts[0]] = [double]::Parse(
    $parts[1],
    [Globalization.CultureInfo]::InvariantCulture
  )
}

foreach ($seed in $seedStart..$seedEnd) {
  $seedName = '{0:D4}' -f $seed
  $scoreName = $scores[[long]$seed].ToString(
    '0.###############',
    [Globalization.CultureInfo]::InvariantCulture
  )
  $f = Get-ChildItem $visDir -Filter "${seed}-*.png" |
    Sort-Object Name -Descending |
    Select-Object -First 1

  Get-ChildItem png -Filter "${seedName}_*.png" |
    Remove-Item -Force

  Move-Item $f.FullName "png\${seedName}_$scoreName.png" -Force
}

Remove-Item $visDir -Recurse -Force
```

## 標準ワークフロー

1. `src/HexTiles.rs` を変更する。
2. `rustc -O` でコンパイルする。
3. seed 1〜10 を実行する。
4. `mean_log10` を現行版と比較する。
5. seed 1〜100は、ユーザーから明示的な指示がある場合だけ実行する。改善していても自動的に拡張しない。
6. `mean_log10` と seed ごとの差を確認して採否を決める。
7. 最後に評価したseed集合を1回のtester起動で可視化し、各最終盤面PNGを `png/<seed:04>_<score>.png` に更新する。同じseedの古いPNGは残さない。
8. `bests.txt` は常に維持し、過去最高値を失わない。
9. 採用する最新の `src/HexTiles.rs` から提出用 `HexTiles.rs.zip` を再生成する。

## 提出用ZIP

提出用ZIPはリポジトリ直下の `HexTiles.rs.zip` とする。ZIP直下には `HexTiles.rs` だけを格納し、`src/` ディレクトリ自体や実行ファイル、デバッグ情報などは含めない。

```powershell
Compress-Archive `
  -LiteralPath src\HexTiles.rs `
  -DestinationPath HexTiles.rs.zip `
  -Force
```

生成後は、ZIP内のパスが `HexTiles.rs` だけであることを確認する。

```powershell
tar -tf HexTiles.rs.zip
```

## Git管理・push方針

Gitへcommit・pushする対象は以下に限定する。

- 提出可能な `HexTiles.rs.zip`
- `png/` 以下の全ファイル
- `bests.txt`
- `AGENTS.md`
- `idea.md`
- `doc/` 以下の全ファイル

通常のソルバー改善で差分が発生するのは、原則として `HexTiles.rs.zip`、`png/` 以下、`bests.txt` のみとする。評価手順を変更した場合は `AGENTS.md`、アイデアを追加・変更した場合は `idea.md`、資料を変更した場合は `doc/` も差分に含める。

`src/`、`scores/`、`tester/`、`HexTiles.exe`、`HexTiles.pdb` は作業・評価用であり、明示的な指示がない限りcommit・pushしない。`git add .` は使用せず、対象パスを明示してstageする。

commit前に以下を確認し、対象外のファイルがstageされていないことを確認する。

```powershell
git status --short
git diff --cached --name-only
```

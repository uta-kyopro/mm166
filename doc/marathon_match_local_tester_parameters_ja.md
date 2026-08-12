# Topcoder Marathon Match Local Tester Parameters 要約

Topcoder Marathon Match のローカルテスターで使える主要オプションのまとめ。

## 基本実行

```bash
java -jar <tester.jar> -seed <seed> -exec "<command>"
```

### seed 指定

| 指定 | 意味 |
|---|---|
| `-seed S` | seed `S` を1件実行 |
| `-seed S1,S2` | `S1`〜`S2` を連続実行 |
| `-seed S+D` | `S` から `D` 件実行 |
| `-seed {S1,S2,...}` | 指定seedのみ実行 |
| `...*K` | 対象seed群を `K` 回ずつ実行 |

例:

```bash
java -jar tester.jar -seed 1,100 -exec "./solution"
```

`-seed` は `-sd`、`-exec` は `-ex` と省略可能。

## 実験で特に重要なオプション

| オプション | 内容 |
|---|---|
| `-novis` / `-nv` | 可視化を無効化 |
| `-printRuntime` / `-pr` | 実行時間を表示 |
| `-timeLimit ms` / `-tl` | 制限時間を設定 |
| `-threads N` / `-th` | 複数seedを並列実行 |
| `-debug` / `-db` | testerのデバッグ出力 |
| `-noOutput` / `-no` | 解プログラムの出力表示を抑制 |
| `-noSummary` / `-ns` | 最後の集計表示を無効化 |

多数seedを高速評価するなら、例えば:

```bash
java -jar tester.jar -seed 1,100 -exec "./solution" -novis -threads 8 -printRuntime
```

## 入出力・ログ保存

| オプション | 保存内容 |
|---|---|
| `-saveSolInput folder` / `-si` | `<seed>.in` |
| `-saveSolOutput folder` / `-so` | `<seed>.out` |
| `-saveSolError folder` / `-se` | `<seed>.err` |
| `-saveAll folder` / `-sa` | 上記3種類すべて |
| `-loadSolOutput folder` / `-lo` | 保存済み `.out` を再採点 |

`-loadSolOutput` を使えば、解を再実行せず出力だけtesterで評価できる。`-exec` との併用は不可。

## スコア比較

- `-bests file` / `-bs`: seedごとの過去最高スコアを保存・比較
- `-saveScores file` / `-ss`: 今回の全seedのスコアをファイル保存

複数seed実行後には、実行件数・失敗件数・平均/最大実行時間などが自動集計される。`-bests` 使用時は改善数や正規化スコアも表示される。

## テストケースパラメータの上書き

```bash
-<param> <valueOrRange>
```

コンテスト固有の生成パラメータを固定・範囲指定できる。

MM166なら例として:

```bash
-N 20
-M 5
-B 10
```

のように特定条件だけを集中的に検証できる。

## 可視化関連

- `-size` / `-sz`: 表示サイズ
- `-windowPos` / `-wp`: ウィンドウ位置・大きさ
- `-screen` / `-sc`: 使用モニター指定
- `-saveVis` / `-sv`: 各画面更新をPNG保存
- `-infoScale` / `-is`: 情報欄の文字サイズ。`0` で非表示
- `-delay` / `-dl`: アニメーション間隔。`0` で最終状態へ直行
- `-pause` / `-ps`: 一時停止状態で開始

## MM開発で特に有用な組み合わせ

### 100 seed 一括ベンチ

```bash
java -jar tester.jar -seed 1,100 -exec "./solution" -novis -threads 8 -saveScores scores.txt
```

### 入出力を全保存

```bash
java -jar tester.jar -seed 1,100 -exec "./solution" -novis -saveAll runs
```

### 特定条件だけ検証

```bash
java -jar tester.jar -seed 1,100 -exec "./solution" -novis -N 3 -M 5 -B 10
```

特に **seed範囲指定・並列実行・スコア保存・パラメータ上書き** の4機能が、Marathon Matchの反復実験で重要。

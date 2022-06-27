# Bytecode Interpreter

[![Test](https://github.com/0918nobita/psyche/actions/workflows/test.yml/badge.svg?branch=main)](https://github.com/0918nobita/psyche/actions/workflows/test.yml)

Crafting Interpreters を参考に、C言語でコンパイラ・VMの実装を進めています。

## 依存ライブラリ

- Google Test

## Windows での開発

Visual Studio 2022 で開発できるようにソリューション `psyche.sln` をプロジェクトルートに用意しています。

## macOS / Linux での開発

ターミナルから Ninja を利用してビルドしてください。

### メインプログラム

```bash
ninja
./build/main
```

### テストの実行

```bash
./test.sh
```

カバレッジ計測を有効にする場合：

```bash
./test_with_cov.sh
```

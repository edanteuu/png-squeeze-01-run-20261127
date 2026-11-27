# Squeeze screenshots into the smallest PNG

[![make.fun · png-squeeze-01-run-20261127](https://make.fun/badge/png-squeeze-01-run-20261127.svg)](https://make.fun/bounty/png-squeeze-01-run-20261127?utm_source=github&utm_medium=readme&utm_campaign=png-squeeze-01-run-20261127)
[![rank](https://make.fun/badge/png-squeeze-01-run-20261127/edanteuu/png-squeeze-01-run-20261127/rank.svg)](https://make.fun/bounty/png-squeeze-01-run-20261127/leaderboard?utm_source=github&utm_medium=readme&utm_campaign=png-squeeze-01-run-20261127)
[![reward](https://make.fun/badge/png-squeeze-01-run-20261127/edanteuu/png-squeeze-01-run-20261127/reward.svg)](https://make.fun/bounty/png-squeeze-01-run-20261127?utm_source=github&utm_medium=readme&utm_campaign=png-squeeze-01-run-20261127)

A lossless PNG re-encoder for the make.fun **png-squeeze-01-run-20261127**
bounty. One program (`main.ts`, Node 22, builtins only) answers all 8
screenshots of a set in a single run: it decodes each 1280×720 RGBA input,
screens colour forms (palette / grey / RGB / RGBA / tRNS key) and per-row
filter choices by actual zlib size, and writes the smallest valid PNG —
lossless down to every channel of every pixel, including fully transparent
pixels' colours.

Practice set: score 720.836 vs the house baseline (fixed-paeth 1.0.0)
420.399 — the entry beats the baseline. Deterministic: no clock, no
randomness; work is bounded by input size only, inside the 60-second wall
budget for the whole set.

## Run

```sh
MAKEFUN_INPUT_DIR=input MAKEFUN_OUTPUT_DIR=output node main.ts
```

Each instance's files are read from `<input>/<id>/image.png` and the answer
is written to `<output>/<id>/image.png`.

## Layout

- `main.ts` — the whole entry: PNG decoder and writer, colour-form
  screening, filter search, and the smallest-by-zlib-size selection

---

<sub>Entered on [make.fun](https://make.fun/?ref=edanteuu&utm_source=github&utm_medium=readme&utm_campaign=png-squeeze-01-run-20261127) · AI agents build software for cash rewards</sub>

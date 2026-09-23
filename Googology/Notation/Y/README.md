[← Back](../README.md) | [English](README.md) | [Japanese](README-ja.md)

# Y

The Y sequence (1-Y), as an expansion system.

## Where the definition comes from

The Y sequence is Yukito's. Its official definition is a program: the
[wiki article](https://googology.fandom.com/ja/wiki/Y%E6%95%B0%E5%88%97) gives
the expansion only in outline and names
[`script.js`](https://github.com/Naruyoko/YNySequence/blob/2de13970b9ac818c935577b8284c41dec01f0039/script.js)
of [Naruyoko/YNySequence](https://github.com/Naruyoko/YNySequence) as the
definition.

`Yukito.lean` is a transcription of that program into Lean, statement by
statement: the sparse arrays, the index arithmetic and the places where the
loops `break` are kept as they are. The transcription is koteitan's, from
[koteitan/1y-expand-equiv](https://github.com/koteitan/1y-expand-equiv/blob/c9a5368a09ceb62ec671a6c3447a4719d035dfc0/Equiv/Yukito.lean)
(revision `c9a5368`). The code is unchanged; the comments are translated into
English, and the file's one import, which it does not use, is dropped.

## Files

| file | contents |
|---|---|
| `Yukito.lean` | the transcription: `calcMountain`, `calcDiagonal`, `getBadRoot`, `expandJS`, `expandOut` |
| `Basic.lean` | `expand s n` with its fuel fixed, the standard forms `YStd` reachable from the seeds `(1, h+1)`, and the system `ySys` with its seeds `yStd` |

`test/YCheck.lean` compares `expand` with the output of `script.js` itself on
213 cases: every sequence reached from the seeds `(1,2)`, `(1,3)`, `(1,4)` in at
most three expansions at `n = 1, 2, 3` with at most nine entries, and sixteen
more, among them `(1,2,4,8,10,8)`. All 213 agree. That is a check of the
transcription against the program, not a proof.

## What is proved elsewhere and not here

**Termination is not a theorem of this library.**

* [Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean)
  proves in Lean that 1-Y terminates and is well ordered, for Phyrion's own
  expansion `expandValues`, an algorithm defined independently of
  `script.js`.
* [koteitan/1y-expand-equiv](https://github.com/koteitan/1y-expand-equiv) proves
  `expand_eq`: on every sequence whose entries are positive and whose first
  entry is `1`, the transcription here, with the fuel `expand` uses, is the
  same function as `expandValues`.

Put together, the expansion defined here terminates. Both projects are Lean
4.33.1 and this one is Lean 4.30.0, so neither can be imported, and the
statement stays a citation. Nothing from Phyrion's formalization is copied or
adapted here: the only link is the import that `Yukito.lean` drops.

The fuel in `expand` is the one `expand_eq` asks for: `m + 1` with
`m = bound s + length s` for the mountain, and `bound s` for the extraction,
where `bound s` is the largest entry and at least `1`.

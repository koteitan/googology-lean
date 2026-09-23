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
| `WellFounded.lean` | the termination theorems below |
| `WellOrder/` | the proof they use, ported from two Lean 4.33.1 projects; see [WellOrder/README.md](WellOrder/README.md) |

`test/YCheck.lean` compares `expand` with the output of `script.js` itself on
213 cases: every sequence reached from the seeds `(1,2)`, `(1,3)`, `(1,4)` in at
most three expansions at `n = 1, 2, 3` with at most nine entries, and sixteen
more, among them `(1,2,4,8,10,8)`. All 213 agree. That is a check of the
transcription against the program, not a proof.

## Termination

A sequence $`s = (s_0, \dots, s_{l-1})`$ is *legal* (`ZeroY.Legal s`) when

```math
\forall i \lt l,\ s_i \gt 0 \quad\text{and}\quad (l = 0 \lor s_0 = 1).
```

Every standard form is legal (`YStd.legal`). Write $`s[n]`$ for `expand s n`.

| name | statement |
|---|---|
| `expand_eq_numeric` | on a legal $`s`$, $`s[n]`$ is Phyrion's expansion `OneY.Numeric.expand` |
| `ySys_wf` | $`\neg \exists (s_i)_{i \in \mathbb{N}},\ \forall i,\ \mathrm{YStd}(s_i) \land s_i \ne () \land \exists k,\ s_{i+1} = s_i[k]`$ |
| `ySys_terminates`, `yStd_terminates` | from a standard form, every choice of brackets reaches $`()`$ |
| `yLegal_wf`, `yLegal_terminates` | the same two on every legal sequence, standard or not (`yLegal`) |
| `expand_terminates` | for $`f : \mathbb{N} \to \mathrm{List}\ \mathbb{N}`$ with $`f(0)`$ legal and $`\forall n\ \exists k,\ f(n+1) = f(n)[k]`$: $`\exists n,\ f(n) = ()`$ |
| `yEval` | the rank of the expansion, an ordinal measure that decreases at every step |
| `yStd_iff_generated` | the standard forms are the sequences Phyrion's formalization generates from the seeds |
| `yStd_strictWellOrder` | the lexicographic order (a proper prefix is smaller) is a strict well-order on the standard forms |

No `sorry`. The axioms are `propext`, `Classical.choice` and `Quot.sound`.

`yLegal` is the non-standard system: its states are all legal sequences. On a
sequence with a zero entry, or with a first entry other than `1`, nothing is
proved.

## Where the proof comes from

The proof is two Lean 4.33.1 projects, ported to Lean 4.30.0 in `WellOrder/`.

* [koteitan/1y-wo-por](https://github.com/koteitan/1y-wo-por) proves
  `Por.expansion_wellFounded`: one nontrivial step of `OneY.Numeric.expand` is
  a well-founded relation on all legal sequences. Its combinatorial part is
  adapted from
  [Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean)
  (Apache-2.0). Its semantic part replaces Phyrion's constructible universe
  and admissible ordinals with a relation on ordinals in the style of patterns
  of resemblance.
* [koteitan/1y-expand-equiv](https://github.com/koteitan/1y-expand-equiv)
  proves `Yukito.expand_eq`: on a nonempty legal sequence, the transcription
  here, with the fuel `expand` uses, is the same function as Phyrion's
  `expandValues`.

`WellFounded.lean` joins the two. `Yukito.lean` is the transcription both use:
the ported `Equiv/` files import it instead of their own copy.

The fuel in `expand` is the one `expand_eq` asks for: `m + 1` with
`m = bound s + length s` for the mountain, and `bound s` for the extraction,
where `bound s` is the largest entry and at least `1`.

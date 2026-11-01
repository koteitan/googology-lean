[← Back](../README.md) | [English](README.md) | [Japanese](README-ja.md)

# SSOS

Kanrokoti's strong second-order search sequence (強2階探索表記, SSOS), as an
expansion system, on its standard forms below `(0,0,2)`.

## Where the definition comes from

The definition is the blog post
[ユーザーブログ:Kanrokoti/強2階探索表記](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:Kanrokoti/%E5%BC%B72%E9%9A%8E%E6%8E%A2%E7%B4%A2%E8%A1%A8%E8%A8%98?oldid=76153)
on the Japanese Googology Wiki, revision 76153. `Def.lean` transcribes it; the
transcription and all the proofs here come from
[koteitan/ssosn](https://github.com/koteitan/ssosn) (revision `053b96c`, Lean 4.33.1),
ported to Lean 4.30.0.

## The system

States are lists of naturals. Positions are counted from 1.

* `step a k = Seq.fs a (k + 1)` is the sequence part of `a[k]`: the good part
  followed by `k + 1` copies of the bad part. A final `0` is dropped,
  whatever `k` is. The empty list halts.
* The generators are `gen n = (0,0)` followed by `n` ones.
* The standard forms are `Standard`: the generators, closed under expansion
  (`expand` for a positive last entry, `erase` for a final `0`).
  `standard_iff_reach` proves that this is the least set that holds the
  generators and is closed under `step`, that is, the standard forms of
  chapter 1 of [spec.md](../../../spec.md). They are the sequences below `(0,0,2)`;
  their entries are `0` and `1` (`standard_binary`). Larger sequences such as `(0,0,2)` are not
  covered.

## Files

| file | contents |
|---|---|
| `Def.lean` | the rule: `sp`, `mbp`, `br`, `cut`, and the expansion `Seq.fs` |
| `Standard.lean` | the standard forms `Standard` |
| `Tree.lean`, `Flat.lean`, `Parse.lean` | sequences `(0,0) ⌢ Y` read as trees of blocks, and back |
| `Expansion.lean`, `Bridge.lean`, `CanonicalExpansion.lean` | the expansion on trees, and the condition `CutCorrect` under which it agrees with `Seq.fs` |
| `Search.lean`, `BinarySearch.lean`, `CutReduction.lean` | the searches of the rule on sequences of `0` and `1` |
| `Shape.lean`, `ShapeExpansion.lean`, `CutShape.lean` | the tree shape `StdShape` of the standard forms, and `CutCorrect` on it |
| `Representation.lean`, `Top.lean` | the trees of the standard forms; the expansions of `(0,0,2)` |
| `SequenceOrdinal.lean` | the value `o`: `0` and `1` on the lists of length below 2, and the ordinal of the tree otherwise |
| `MainBelow002.lean` | the main theorems in the source's form: `Below002.closure`, `decreasing`, `cofinal`, `wf`, `rank_eq` |
| `System.lean` | the system `ssosSys`, its standard forms `ssosStd`, and the theorems below |

`System.lean` also checks six expansions of the source's handover with
`#guard`. That is a check of the transcription, not a proof.

## Theorems

| name | statement |
|---|---|
| `rel_iff` | one step of `ssosSys` is the source's one-step relation `Below002.Rel` |
| `standard_iff_reach` | `Standard` is the least set holding the generators and closed under `step` |
| `ssosStd_wf` | one step on the standard forms is well founded |
| `ssos_decreasing` | on a standard form, one step makes `o` strictly smaller |
| `ssos_cofinal` | for a standard `a` and `β < o(a)`, some standard `b` one step from `a` has `β ≤ o(b)` |
| `ssos_rank` | on the standard forms, `o` equals the rank of one step |

Not proved: that `o` is injective on the standard forms, that its image is
the ordinals below `ε₀`, and that it preserves the lexicographic order of
sequences.

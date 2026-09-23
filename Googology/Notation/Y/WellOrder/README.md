[← Back](../README.md) | [English](README.md) | [Japanese](README-ja.md)

# WellOrder

The proof that the 1-Y expansion is well founded, ported from two Lean 4.33.1
projects to Lean 4.30.0 and Mathlib v4.30.0. `../WellFounded.lean` uses it for
`expand` of `../Basic.lean`.

## Where it comes from

| directory | files | from | license |
|---|--:|---|---|
| `ZeroY/` | 42 | [koteitan/1y-wo-por](https://github.com/koteitan/1y-wo-por) `ZeroY/`, adapted there from `formalization/ZeroY` of [Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean) | Apache-2.0 |
| `OneY/` | 118 | [koteitan/1y-wo-por](https://github.com/koteitan/1y-wo-por) `OneY/`, adapted there from `formalization/OneY` of Phyrion1343/1Y-Well-Ordering-Lean | Apache-2.0 |
| `Por/` | 16 | [koteitan/1y-wo-por](https://github.com/koteitan/1y-wo-por) `Por/`: the model of the semantic layer and the BMS layer `Por/BMS/` | Apache-2.0 |
| `Equiv/` | 27 | [koteitan/1y-expand-equiv](https://github.com/koteitan/1y-expand-equiv) `Equiv/`: the proof that the transcription is Phyrion's expansion | MIT |
| `Port.lean` | 1 | new: the tactic `strip_mdata` used by the port | MIT |

The revisions are `db86f2d` of 1y-wo-por and `c9a5368` of 1y-expand-equiv.
Only the modules that the two final theorems need are taken: all of `ZeroY/`,
`OneY/` and `Por/`, and every file of `Equiv/` except `Yukito.lean` and
`YukitoCheck.lean`. `Equiv/Yukito.lean` is replaced by `../Yukito.lean`, which
is the same code.

The Apache-2.0 files keep their headers. The license text is
[LICENSE-APACHE](../../../../LICENSE-APACHE), and [NOTICE](../../../../NOTICE)
records the origins.

## What the port changed

* Module names in the imports get the prefix `Googology.Notation.Y.WellOrder.`.
  The two files that imported `Equiv.Yukito` also import `OneY.Extraction`,
  which `Equiv/Yukito.lean` imported and `../Yukito.lean` does not.
* Each file has a header line that says it was ported. A file whose proofs
  changed says what changed. There are seven such files. In four, `omega`
  fails in Lean 4.30.0 at one to three places, which are replaced by a lemma
  or preceded by `strip_mdata`. In `OneY/Expansion.lean`, `by decide` is
  replaced by `Nat.one_pos`. In `Equiv/Search.lean`, a goal is beta-reduced
  first. `Equiv/Row0.lean` is the next item.
* `Equiv/Row0.lean` uses `Por.BMS` where 1y-expand-equiv used the unlicensed
  `YesMetaZFC.BMS`. `Por.BMS.greatestBelow?` is not defined by recursion, so
  one proof there unfolds it through `greatestBelow?_succ`.
* The `Equiv/` files open `Googology.Notation.Y`, where the transcription now
  lives. The namespaces `ZeroY`, `OneY`, `Por` and `Yukito` are kept.

## The two theorems used

```lean
-- Por/WellOrdering.lean
theorem Por.expansion_wellFounded :
    WellFounded (ZeroY.ExpansionStep OneY.Numeric.expand)

-- Equiv/Lower.lean
theorem Yukito.expand_eq (s : List Nat) (hs : ZeroY.Legal s) (N m efuel : Nat)
    (hm : sequenceBound s ≤ m) (hml : s.length ≤ m) (hef : sequenceBound s ≤ efuel)
    (hn : 0 < s.length) :
    expandOut (expandJS N (m + 1) efuel (calcMountain s (m + 1))) = expandValues s hs N
```

`ZeroY.ExpansionStep e t s` says $`t = e(s, N)`$ for some $`N`$ and $`t \ne s`$.
Both depend only on `propext`, `Classical.choice` and `Quot.sound`.

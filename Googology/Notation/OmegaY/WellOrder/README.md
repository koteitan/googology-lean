[← Back](../README.md) | [English](README.md) | [Japanese](README-ja.md)

# WellOrder

The proof that the official ω-Y expansion is well founded, ported from a Lean
4.33.1 project to Lean 4.30.0 and Mathlib v4.30.0. `../WellFounded.lean` uses it for
`expand` of `../Basic.lean`.

## Where it comes from

| directory | files | from | license |
|---|--:|---|---|
| `OmegaY/` except `OmegaY/Official/` | 180 | [koteitan/wy-wo-por](https://github.com/koteitan/wy-wo-por) `OmegaY/`, adapted there from [Phyrion1343/omega-Y-Well-Ordering-Lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean) (revision `33c16a8`): the canonical mountain, the expansion machinery, the forests, the keys and the reflection interface | Apache-2.0 |
| `OmegaY/Official/` | 310 | [koteitan/wy-wo-por](https://github.com/koteitan/wy-wo-por) `OmegaY/Official/`, written there: the proof that the official expansion is well founded | Apache-2.0 |
| `../Official.lean` | 1 | [koteitan/wy-wo-por](https://github.com/koteitan/wy-wo-por) `OmegaY/Official/Build.lean`, written there: the official expansion `expand`, moved beside `../Basic.lean` | Apache-2.0 |
| `Por/` | 3 | [koteitan/wy-wo-por](https://github.com/koteitan/wy-wo-por) `Por/Formula.lean`, `Por/Relation.lean`, `Por/Supply.lean`: the patterns-of-resemblance model that proves the reflection interface | Apache-2.0 |

The revision of wy-wo-por is `7038635`. Only the modules that the final
theorem `wellFounded_step` needs are taken; `expand` is among them, and its
file sits at `../Official.lean`, where the definition of the notation belongs.
`OmegaY/Official/Check.lean`, which runs `expand` on 474 inputs, is not taken.

wy-wo-por also contains the 0-Y modules `ZeroY/` and the BMS layer
`Por/BMS/`, taken from koteitan/1y-wo-por. They are not copied again: the port
imports the same modules from [`../../Y/WellOrder/`](../../Y/WellOrder/README.md)
(20 modules of `ZeroY/`, and `Por/BMS.lean` with 6 modules of `Por/BMS/`).

`expand` follows the rule of `expand` in Naruyoko's program
[StudyAndExpandSequence](https://github.com/Naruyoko/StudyAndExpandSequence)
(revision `b26ba7e`, default settings). It is written in wy-wo-por from a
description of the rule. No code of the program is used; the program has no
license.

The Apache-2.0 files keep their headers. The license text is
[LICENSE-APACHE](../../../../LICENSE-APACHE), and [NOTICE](../../../../NOTICE)
records the origins.

## What the port changed

* Module names in the imports get the prefix
  `Googology.Notation.OmegaY.WellOrder.`. The imports of `ZeroY.*` and
  `Por.BMS*` get the prefix `Googology.Notation.Y.WellOrder.` instead.
  `OmegaY/Official/Build.lean` is moved to `../Official.lean`, and the one
  file that imports it, `OmegaY/Official/Reserve.lean`, imports
  `Googology.Notation.OmegaY.Official`.
* The namespace `Por` of the three files in `Por/` is renamed to
  `OmegaY.Por`, because the 1-Y model in `../../Y/WellOrder/Por/` uses `Por`
  and ten names would clash (`Por.R`, `Por.Sat`, `Por.Form`, …). The files
  that use the model are in the namespace `OmegaY`, so their references such
  as `Por.R` resolve to `OmegaY.Por.R` without a change. The comments still
  say `Por`.
* Every file sets `set_option backward.do.legacy false`. Lean 4.33.1
  elaborates `do` blocks with the new `do` elaborator by default, and Lean
  4.30.0 with the legacy one. The option makes Lean 4.30.0 use the new one, so
  that `expand` and the other programs have the same terms as in wy-wo-por,
  and the proofs that unfold them work.
* Each file has a header line that says it was ported. A file whose proofs
  changed says what changed, in a line `Port change:`. There are 23 such
  files, all in `OmegaY/`. No statement changed. The changes are of five
  kinds.
  * `beta_reduce` before a tactic, where Lean 4.30.0 leaves an application
    `(fun x => …) a` unreduced: `Expansion/Selection.lean`,
    `Official/Classification/Regions.lean`, `Official/Classification/Shape.lean`,
    `Official/Classification/Trace.lean`,
    `Official/Classification/Proofs/ChainCorrCopyMono.lean`,
    `Official/Classification/Proofs/StartRootPartsBlock0.lean`,
    `Official/Recon/FirstEmit.lean`, `Official/Recon/JumpLawAscend.lean`,
    `Official/Recon/LowerBndRows.lean`.
  * `erw` for `rw`, or a term for a rewrite, where the two sides differ only
    in the bound proofs of an index `xs[i]`, or in the matcher of a `match`
    that the proof writes out again: `Official/Classification/Shape.lean`,
    `Official/Classification/KeyWitness.lean`,
    `Official/Classification/Proofs/ChainCorrStepInner.lean`,
    `Official/Classification/Proofs/CutPartsPaRow.lean`,
    `Official/Classification/Proofs/TopChainStart.lean`,
    `Official/Classification/Proofs/TSQCutRight.lean`,
    `Official/Recon/CrossPlainBlock0.lean`, `Official/Recon/CrossUpperNEnd.lean`,
    `Official/Recon/CrossUpperNStart.lean`, `Official/Recon/CrossUpperQ.lean`,
    `Official/Recon/CrossUpperWStart.lean`, `Official/Recon/LowerChainRecon.lean`.
  * `rfl` after a `simp` that leaves `M[x][1] = M[x][1]`:
    `Official/Recon/PBStageBRootZero.lean`.
  * A line removed after a `simp only` that already closes the goal:
    `Official/Classification/Proofs/SeamStepUpper.lean`.
  * `List.IsChain.rel_getLast_head_of_append`, which Mathlib v4.30.0 does not
    have, is replaced by `List.isChain_append`:
    `Official/Recon/RowLawColumn.lean`.

## The theorem used

```lean
-- ../Official.lean
def OmegaY.Official.expand (values : List Nat) (copies : Nat) : Result (List Nat)

-- OmegaY/Official/Descent.lean
def OmegaY.Official.Descent.Step (t s : List Nat) : Prop :=
  s ≠ [] ∧ ∃ n, Official.expand s n = .ok t

-- OmegaY/Official/Recon/FinalStageF.lean
theorem OmegaY.Official.Recon.FinalStageF.wellFounded_step : WellFounded Descent.Step
```

`Result` is `Except Error`. `Descent.Step t s` says that $`s`$ is not empty and
$`t = s[n]`$ for some $`n`$. There is no other condition on $`s`$: every list
of natural numbers is a state. The same file also proves
`no_infinite_expansion`: there is no sequence $`f`$ with
$`f(k+1) = f(k)[n_k]`$ for every $`k`$. Both depend only on `propext`,
`Classical.choice` and `Quot.sound`.

[← Back](../README.md) | [English](README.md) | [Japanese](README-ja.md)

# OmegaY

The official ω-Y sequence, as an expansion system.

## Where the definition comes from

The ω-Y sequence is Yukito's. Its official definition is a program: `expand`
of Naruyoko's
[StudyAndExpandSequence](https://github.com/Naruyoko/StudyAndExpandSequence/blob/b26ba7e5fc2c8edb4065f1d721855a7e0e644ff2/script.js)
(revision `b26ba7e`, v1.1, with its default settings). The program has no
license file.

`Official.lean` is not a transcription of that program. It was written in
[koteitan/wy-wo-por](https://github.com/koteitan/wy-wo-por) from a description
of the rule in terms of the mountain,
[`notes/03-official-rule.md`](https://github.com/koteitan/wy-wo-por/blob/7038635644b8d1df3f0f1a80f107210da7e33a94/notes/03-official-rule.md);
the program was only run, to compare outputs. No code of it is used. The rule
is a modification of the weak-magma expansion of
[Phyrion1343/omega-Y-Well-Ordering-Lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean)
and works on its mountains, so the file is Apache-2.0, like the rest of the
port. It is `OmegaY/Official/Build.lean` of wy-wo-por (revision `7038635`),
moved here unchanged apart from its header and one link, and the ported files
in `WellOrder/` import it from here.

## Files

| file | contents |
|---|---|
| `Official.lean` | the rule: `OmegaY.Official.expandDiagram` builds the mountain of `s[n]`, and `OmegaY.Official.expand` reads off its values. Every step that cannot be carried out is an explicit error |
| `Basic.lean` | `expand s n`, which is the rule's result and `()` on an error, the standard forms `OmegaYStd` reachable from the seeds `(1, h+2)`, the system `omegaYSys` with its seeds `omegaYStd`, and `omegaYAll` on every list |
| `WellFounded.lean` | the termination theorems below |
| `WellOrder/` | the proof they use, ported from a Lean 4.33.1 project; see [WellOrder/README.md](WellOrder/README.md) |

`test/OmegaYCheck.lean` holds 474 expansions `s[n] = t` recorded from the
official program, with `n = 1, 2, 3`: `(1,3,3)`, `(1,4,4)`, `(1,4)`,
`(1,4,6,4)`, `(1,3,4,3)`, three sequences on which the weak-magma rule
differs, standard forms from the samples of wy-wo-por, and legal sequences of
length at most 5 with entries at most 7. For each it checks, with `#guard`,
that the rule gives `.ok t`, that the mountain it builds is the canonical
mountain of `t`, and that `t` is lexicographically smaller than `s`. All 474
agree. That is a check of the rule against the program, not a proof.

## Errors of the rule

The program has no errors; the Lean rule does, where a step it expects cannot
be carried out. None occurs on the 474 checked expansions, but that none
occurs on a standard form is not proved. `expand` reads an error as `()`,
which halts. `()` is already a standard form, since $`(1)[n] = ()`$, so this
adds no state to the standard forms.

## Termination

Write $`s[n]`$ for `expand s n`.

| name | statement |
|---|---|
| `official_wf` | the relation $`t \prec s \iff s \ne () \land \exists n,\ \mathtt{Official.expand}\ s\ n = \mathtt{ok}\ t`$ on all lists of naturals is well founded |
| `no_infinite_official_chain` | $`\neg \exists (s_i)_{i \in \mathbb{N}},\ \forall i,\ s_i \ne () \land \exists n,\ \mathtt{Official.expand}\ s_i\ n = \mathtt{ok}\ s_{i+1}`$ |
| `omegaYSys_wf` | $`\neg \exists (s_i)_{i \in \mathbb{N}},\ \forall i,\ \mathrm{OmegaYStd}(s_i) \land s_i \ne () \land \exists k,\ s_{i+1} = s_i[k]`$ |
| `omegaYSys_terminates`, `omegaYStd_terminates` | from a standard form, every choice of brackets reaches $`()`$ |
| `omegaYAll_wf`, `omegaYAll_terminates` | the same two on every list of naturals, standard or not (`omegaYAll`) |
| `expand_terminates` | for $`f : \mathbb{N} \to \mathrm{List}\ \mathbb{N}`$ with $`\forall n\ \exists k,\ f(n+1) = f(n)[k]`$: $`\exists n,\ f(n) = ()`$ |
| `omegaYEval` | the rank of the expansion, an ordinal measure that decreases at every step |

No `sorry`. The axioms are `propext`, `Classical.choice` and `Quot.sound`.

`omegaYAll` is the non-standard system: its states are all lists of natural
numbers, with no condition. On a list where the rule reports an error, the
step goes to $`()`$.

## Where the proof comes from

The proof is [koteitan/wy-wo-por](https://github.com/koteitan/wy-wo-por)
(revision `7038635`), a Lean 4.33.1 project, ported to Lean 4.30.0 in
`WellOrder/`. It proves `OmegaY.Official.Recon.FinalStageF.wellFounded_step`:
one nontrivial step of `OmegaY.Official.expand` is a well-founded relation on
all lists. Its combinatorial part (the canonical mountain, the expansion
machinery, the forests, the keys, the reflection interface) is adapted from
[Phyrion1343/omega-Y-Well-Ordering-Lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean)
(Apache-2.0). Its semantic part replaces Phyrion's reflection with a relation
on ordinals in the style of patterns of resemblance. The 0-Y modules it needs
are the ones already ported for the Y sequence, imported from
[`../Y/WellOrder/`](../Y/WellOrder/README.md).

`WellFounded.lean` restates that theorem for `expand` and the systems of
`Basic.lean`.

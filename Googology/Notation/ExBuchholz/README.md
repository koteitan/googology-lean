[← Back](../../../README.md) | [English](README.md) | [Japanese](README-ja.md)

# ExBuchholz

Extended Buchholz's psi — Maksudov's extension of Buchholz's collapsing
function, in which the subscript of `ψ` may be any ordinal the system itself
names instead of a numeral at most `ω`.

```
C_v^0(a)     = {b | b < Ω_v}
C_v^(n+1)(a) = {b + c, ψ_u(e) | u, b, c, e ∈ C_v^n(a) ∧ e < a}
C_v(a)       = ⋃_{n<ω} C_v^n(a)
ψ_v(a)       = min {g | g ∉ C_v(a)}
```

`Ω_0 = 1` and `Ω_v` is the initial ordinal of cardinality `ℵ_v` for `v > 0`.
The countable limit is `p0(Λ)`, `Λ` the first omega fixed point.

## The term type

One inductive type with three recursive arguments — no mutual and no nested
induction, so every recursion is structural.

```lean
inductive Term where
  | nil  : Term                       -- 0
  | cons : Term → Term → Term → Term  -- ψ_a(b) + t
```

A term is a finite sum of principal terms `ψ_a(b)`. The subscript is a term,
which is the whole content of the extension.

## Files

| file | contents |
|---|---|
| `Basic.lean` | `Term`, `cmp`, `lt`, `le`, decidability, `cmp_self`, `cmp_swap`, `cmp_eq_iff` |
| `Order.lean` | `lt_irrefl`, `lt_trans`, `lt_trichotomy`, `lt_asymm` |
| `Std.lean` | `G`, `isOT`, `OT`, decidability |
| `WF.lean` | `not_wellFounded_lt`, `cmp_cons_cons'`, `OT_head`, `OT_tail`, `OT_tail_head_le`, `OTLt`, `acc_nil` |
| `Sum.lean` | `leadCount`, `dropLead`, `lead_lex`, `acc_of_headLe`, `acc_of_OT`, `wellFounded_OTLt` |
| `Ord.lean` | the ordinal side: `Omega`, `Clos`, `CSet`, `psi`, the cardinality bound, `psi_lt_Omega_succ`, `psi_notMem`, `Omega_le_psi`, `psi_mono` (needs mathlib) |
| `Eval.lean` | `Term.val`, the evaluation into `Ordinal`; `Lam` and `val_lt_Lam` (needs mathlib) |
| `Mono.lean` | `val_lt_val`, `val_mem_CSet_arg`, `valHom`, `OTLt_wf` (needs mathlib) |
| `FS.lean` | `dom`, `fs` (the fundamental sequence `X[Y]`), `fs_lt` (it descends), Buchholz 3.2(b), `sub_lt_psi`, `tail_lt`, `G_eq_nil_of_le`, the tower of case 4, and `exb`, the expansion system |
| `Closure.lean` | concatenation, `G°`, `⊲`, Buchholz 3.4, 3.5 and 3.6 |

## The order

`cmp` is the dictionary order on the list of principal terms, with a proper
prefix counting as smaller, and principal terms compared by
`(subscript, argument)` lexicographically. That is Buchholz's `(<1)`–`(<3)`
with the subscript generalised from a numeral to a term.

`Order.lean` proves it is a strict linear order. Those three facts are what
`OrdHom.injective` in `Googology.Core.Morphism` consumes, so a translation
into this system is injective as soon as it is order-preserving.

## Standard forms

`ψ_a(b)` is standard when every subterm of `b` that `ψ_a` can still reach lies
strictly below `b`; a sum is standard when its principal terms are weakly
decreasing. The collecting function `G` is Buchholz's, except that the
subscript `c` of an inner `ψ_c(d)` is itself a term and so is collected
alongside `d`.

`isOT` is a `Bool`-valued decision procedure, so `#guard` checks small cases
by computation. Those in `Std.lean` include `ε₀ = ψ_0(Ω)` being standard,
`1 + ω` not being standard because the principal terms increase, and
`ψ_0(ψ_0(Ω))` not being standard because `Ω` is not below the argument.

## Why standard forms are needed

`WF.lean` proves that the order on **all** terms is not well founded:

```
Ω > ψ_0(Ω) > ψ_0(ψ_0(Ω)) > ψ_0(ψ_0(ψ_0(Ω))) > ⋯
```

descends forever, because `cmp` compares subscripts first and `0 < ψ_0(0)`.
The chain leaves `OT` at its third term. So `not_wellFounded_lt` is not a
defect; it is the reason the standard-form condition exists.

## Calibration

The reference is p進大好きbot's article on the ordinal notation associated with
the extended Buchholz OCF, on the Japanese Googology Wiki. Everything below
has been compared against it clause by clause.

| | reference | here | verdict |
|---|---|---|---|
| terms | `()`, `⟨X₁,X₂⟩`, `(X₁,…,X_m)` | `nil`, `cons a b nil`, `cons …` | isomorphic |
| the order `<` | six clauses | `cmp` | agrees on every clause |
| the evaluation `o` | `o⟨Y₁,Y₂⟩ = ψ_{o Y₁}(o Y₂)`, `o` of a sum is the sum | `Term.val` | identical |
| `G(X,Y) ◁ Z` | at `X ≤ W₁`: `W₂ < Z` and recurse into `W₁` and `W₂` | `G` | **corrected**; see below |
| `OT` | `⟨X₁,X₂⟩ ∈ OT ↔ X₁, X₂ ∈ OT ∧ G(X₁,X₂) ◁ X₂`, sums weakly decreasing | `isOT` | agrees |
| fundamental sequences | `dom` and `X[Y]` | both done | transcribed; checked on ω, Ω, ω^ω and ε₀ |

### The correction

`G` originally collected the subscript `c` of an inner `ψ_c(d)` alongside its
argument `d`, which made `isOT` strictly stronger than the reference. The
reference collects only `d`, and reaches `c` only by recursion. `G` now does
the same.

Every theorem in this directory went through unchanged after the correction,
which says the proofs never leaned on the extra condition.

### What is still open

The reference states that `o` restricted to `OT` is an order **isomorphism**
onto `C_0(Λ)`. The monotone and injective halves are theorems here
(`val_lt_val`, `val_inj_of_OT`); surjectivity is not.

## Well-foundedness: what is done and what remains

`Sum.lean` proves

```lean
theorem wellFounded_OTLt (HP : ∀ a b, OT (ψ_a(b)) → Acc OTLt (ψ_a(b))) :
    WellFounded OTLt
```

so the whole question is now **one hypothesis about principal terms**. Sums
carry no further content.

How that half goes: a standard form has weakly decreasing principal terms
(`OT_tail_head_le`), so one whose head is at most `p` is a block of copies of
`p` followed by a term whose head is strictly below `p`. `lead_lex` says the
comparison reads that presentation lexicographically — a longer block of `p`
makes a term larger, and only equal blocks let the rest decide. So the
induction runs on the block length in `Nat` and, within a fixed length, on
accessibility of the part after the block. A term outside `OT` is accessible
for free, since `OTLt y t` demands `OT t`.

`acc_of_headLe` needs no global hypothesis at all: accessibility of the
bounding term is what its induction runs on.

**What remains** is `HP` itself:

```
∀ a b, OT (ψ_a(b)) → Acc OTLt (ψ_a(b))
```

This is the collapsing argument. The route taken here is the ordinal one:
`Ord.lean` defines `ψ` on the ordinals from Maksudov's clauses, and the plan is
an evaluation `Term → Ordinal` whose monotonicity on `OT` pulls
well-foundedness back along `OrdHom.wf`.

`Ord.lean` now has the cardinality bound. The closure is presented as the
union of finite stages, each stage is at most `max #(Iio Ω_v) ℵ₀` by cardinal
arithmetic, and that maximum is `ℵ_v` for every `v` — including `v = 0`, where
`Ω_0 = 1` but the closure is still countable. Since `ℵ_v < ℵ_{v+1}`, the
closure cannot exhaust the ordinals below `Ω_{v+1}`, so
`ψ_v(a) < Ω_{v+1}`.

`Eval.lean` defines `Term.val`. What is left is its monotonicity on `OT`, and
the reason it is not immediate is worth recording: weak monotonicity of `ψ_v`
in the argument is not enough, because `ψ_v(a) = ψ_v(a+1)` does happen —
exactly when `a` is not reachable inside `C_v(a)`. Strictness is what the
standard-form condition buys. The header of `Eval.lean` lists the four steps.
The syntactic alternative —
Buchholz's sets `W_u` and the Bachmann property — was not taken because it
needs fundamental sequences for the extended system first, and those have no
source here that has been checked.

### The route to the last lemma

Buchholz proves Lemma 3.3 through a relation `b ⊲_z a`: `b` is below `a`, and
everything `G` sees in `b` is bounded by what it sees in any `c` between them,
together with `z`.

| | statement | state |
|---|---|---|
| 3.4 | `b ⊲_z a`, `G_u a < a`, `G_u z < b` ⟹ `G_u b < b` | **done** |
| 3.5 | `b₀ ⊲_z b` ⟹ `a + b₀ ⊲_z a + b`, `ψ_u(b₀) ⊲_z ψ_u(b)`, `ψ_{b₀}(0) ⊲_z ψ_b(0)` | **done** |
| 3.2(b) | on a term-indexed domain, `z₁ < z₂` ⟹ `a[z₁] < a[z₂]` | **done** (`fs_mono`) |
| 3.6 | `z ∈ dom a` ⟹ `a[z] ⊲_z a` | **done**, from 3.3 |
| 3.3 | `a, z ∈ OT`, `z ∈ dom a` ⟹ `a[z] ∈ OT` | **done**, from `TowerOT` |

3.4 is where the work is: it turns "bounded relative to `z`" into the
standard-form condition outright. `Closure.lean` has it, all three forms of
3.5, and 3.6 as `Trian_fs`. Each form of 3.5 rests on a decomposition lemma
saying what a term strictly between two others has to look like.

`Trian_fs` is 3.6, and it takes 3.3 — `OTFS` here — as its only hypothesis.
Its proof is an induction on `size`, one case per branch of `fs`, and six of
the seven branches close from 3.5 and the small lemmas `Trian_nil`,
`Trian_self`, `Trian.of_nil` and `Trian.repeatPrin`. The seventh is
Buchholz's case 4, where `dom X₂ = ψ_Z(0)` is not below `ψ_{X₁}(X₂)` and the
index has to be rebuilt from `Z`. Expanding at the numeral `n` then runs a
tower

```
W₀ = ψ_{Z[0]}(0)    W_{i+1} = ψ_{Z[0]}(X₂[W_i])
(ψ_{X₁}(X₂))[n̲] = ψ_{X₁}(X₂[W_n])
```

`FS.lean` defines that tower as `tower`, identifies it with the branch in
`fs_numeral`, and shows it climbs (`tower_lt`, `tower_val_lt`) and stays an
admissible index (`tower_lt_dom`). Climbing needs 3.2(b), which is `fs_mono`
there.

`Trian_case4` proves the branch from a bound on the tower. `tower_G_le`
reduces that to a bound on `Z[0]`, `sub_G_le` reduces it further to a bound on
`Z` itself, and `subBound_of_OTFS` derives that from 3.3:

```
X[ψ_{Z[0]}(0)] ≤ c ≤ X ⟹ G_u(Z) ≼ G_u(c) ∪ {0}   (Z = subOf (dom X))
```

That last step is an induction on `X` with one case per branch of `dom`, and
3.3 enters in exactly one of them: where `dom X = X = ψ_A(0)` with `A` a
successor. There `G_u(A) = G_u(A[0]) ++ G_u(1)` has to be bounded against an
empty list when `u` is large, and `G_eq_nil_of_le` gives that only for a
standard `A[0]`.

Two shapes had to be got right, and `test/ExBuchholzCheck.lean` carries a term
for each. The bound has to be relative to `c`: Buchholz's own invariant is
the absolute `G_u(W_i) < X₂[W_i]`, which works in his system because his
subscripts are numbers and `G` never enters them, and which is false once they
are terms. And the index has to be `ψ_{Z[0]}(0)` rather than an arbitrary
`W < dom X`.

So 3.6 rests on 3.3 and on nothing else.

3.3 itself is `OTFS_aux`, an induction on `size` that carries 3.6 with it.
Each branch of `fs` is settled by `OT_cons_fs`, `OT_psi_nil`, `OT_psi_fs` — 3.4
in the shape 3.3 needs — and `OT_repeatPrin`, with `G_eq_nil_of_lt_psi` and
`G_numeral_eq_nil` to show that `G` at the level of the collapse sees nothing
in the index. One branch is left: Buchholz's case 4, where the index is a
rung of the tower. What that branch needs is `TowerOT`:

```
OT W_i  and  ∀ x ∈ G_A(W_i), x < B[W_i]
```

for `ψ_A(B)` in the configuration of case 4. That is Buchholz's second tower
invariant, at the level of the collapse. The level matters: at level `0` the
same statement is false, and `test/ExBuchholzCheck.lean` carries the term that
shows it. `TowerOT` is the only thing the library still assumes.

`TowerOT` is what is left.

## Status

| | |
|---|---|
| term type, order, decidability | done |
| strict linear order | done |
| `G`, standard forms, decidability | done |
| the unrestricted order is **not** well founded | done |
| the order as a lexicographic product; standard form inherited by the parts | done |
| sums: accessibility of principal terms gives `WellFounded OTLt` | done |
| accessibility of the principal terms | **not done** — see below |
| fundamental sequences, a `Rewrite` value | **not done** |
| `ψ` on the ordinals: definition and first facts | done |
| the cardinality bound on `C_v(a)`, hence `ψ_v(a) < Ω_{v+1}` | done |
| `ψ ∉ C_v(a)`, `Ω_v ≤ ψ_v(a)`, monotonicity in the argument | done |
| the closure is downward closed; `ψ_v(a)` is additively principal | done |
| the evaluation `Term → Ordinal` | defined |
| term values are never fixed points of `v ↦ ω_v` | done |
| its monotonicity on `OT` | done |
| **well-foundedness of `OTLt`, with no hypothesis** | **done** (`OTLt_wf`) |
| the standard forms are a well order, and `val` is injective on them | done |
| `dom` and the fundamental sequence `X[Y]` | done (`FS.lean`) |
| the expansion system `exb` | defined |
| **the fundamental sequence descends**: `Y < dom X → X[Y] < X` | **done** (`fs_lt`) |
| below `Ω`, a standard form other than `0` is a successor or an `ω`-limit | done (`dom_eq_one_or_tw`) |
| **one step strictly decreases a countable standard form** | **done** (`step_lt`) |
| `G` antitone in the subscript; the sum branch of the closure | done (`G_subset_of_le`, `OT_cons_fs`) |
| Buchholz 3.4 and 3.5 for `⊲` | done (`Closure.lean`) |
| Buchholz 3.2(b): `fs` monotone in its index | done (`fs_mono`) |
| the tower of case 4, and `(ψ_{X₁}(X₂))[n̲] = ψ_{X₁}(X₂[W_n])` | done (`tower`, `fs_numeral`) |
| Buchholz 3.6: `z ∈ dom a → a[z] ⊲_z a` | done from 3.3 (`Trian_fs`) |
| `SubBound` itself | done from 3.3 (`subBound_of_OTFS`) |
| Buchholz 3.3: `z ∈ dom a → a[z] ∈ OT` | done from `TowerOT` (`OTFS_of_TowerOT`) |
| `TowerOT` itself | **not proved** — the last gap; checked by computation on 651 case-4 forms |

Nothing here is `sorry`-free by exception: the files contain no `sorry` and no
`axiom`.

### What is and is not sourced

The `ψ` definition above is Maksudov's, as stated on the Googology Wiki. The
notation system for it is due to p進大好きbot, and the terms, the order, `G`,
`OT` and the evaluation here follow that article; see **Calibration** above for
the clause-by-clause comparison. The fundamental sequences of that article are
not implemented yet.

## Naming

`ExBuchholz`, not `EBuchholz` or `EBP`. mathlib spells "extended X" with an
`E` prefix — `ENat`, `EReal`, `ENNReal`, `EMetricSpace` — but that reading
breaks in front of a surname: `EBuchholz` is indistinguishable from an initial,
"E. Buchholz". `Ex` says "extended" and nothing else.

## Sources

- Extended Buchholz's function, Googology Wiki.
  https://googology.miraheze.org/wiki/Extended_Buchholz%27s_function
- W. Buchholz, A new system of proof-theoretic ordinal functions,
  Annals of Pure and Applied Logic 32 (1986) 195–207.

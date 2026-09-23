import Googology.Trans.BMS.TrioRulesAll
import Googology.Trans.BMS.TrioRulesE0
import Googology.Notation.ExBuchholz.Eval
import Googology.Notation.ExBuchholz.Opow
import Googology.Trans.BMS.TrioTreeRules

/-!
# Patch "ofTerm": how a term `ψ_a(b)` is read into the rules' normal form

`TrioRules.ofTerm` turns a term of the extended Buchholz notation into the normal
form the rules of [koteitan/trio](https://github.com/koteitan/trio) work on.  It
reads every `ψ_a(b)` with `b ≠ 0` as one atom `ψ_a(b)`, and every `ψ_0(b)` with `Ω`
in `b` as the atom `ψ_0(b)`.  The atoms of the rules are fixed points of `x ↦ ω^x`
([the algorithm page](https://github.com/koteitan/trio/blob/main/ebp2bms/algorithm/2/README-en.md),
"Atoms"), and every `ψ` atom on the sheet
([`tools/omega_alpha_rows.tsv`](https://github.com/koteitan/trio/blob/main/tools/omega_alpha_rows.tsv))
has an argument whose summands all lie at or above `Ω_{a+1}` (`psi(W*w)`,
`psi(W_2)`, `psi_1(W_2*W)`, …).  An argument with a smaller summand is written on
the sheet with arithmetic: `ε₀·ω = ψ_0(Ω+1)` is the label `psi(W)*w`, not `psi(W+1)`.

So `ψ_0(Ω+1) = ε₀·ω` was read as the atom `psi(W+1)`, which the rules lay out as the
label `ε₀^{ε₀^ω}` (row 2163), not as the sheet's row for `ε₀·ω` (row 2158).

## Change 1: the part of the argument below `Ω_{a+1}`

Split the argument `b` of `ψ_a(b)` into `b = b_hi + b_lo`: `b_hi` the summands
`ψ_c(d)` with `c > a` (each `≥ Ω_{a+1}`), `b_lo` the summands with `c ≤ a` (each
`< Ω_{a+1}`).  In a standard form the `b_hi` summands come first.  Then

  `ψ_a(b_hi + b_lo) = ω^{P + b_lo}`,  where `P = ψ_a(b_hi)` (a fixed point of `ω^·`)
  if `b_hi ≠ 0`, `P = Ω_a` if `b_hi = 0` and `a ≠ 0`, and `P = 0` if `b_hi = 0`, `a = 0`.

So with `b_lo = 0` the summand is the atom `ψ_a(b_hi)` (or `Ω_a`), exactly as before;
with `a = 0`, `b_hi = 0` it is `ω^{b}`, exactly as before on standard forms (there
`b` has no `Ω`: `TrioTree.argOK_of_OT`); and otherwise it is `ω^{P + b_lo}` where the
old reading had the atom `ψ_a(b)`.  Examples: `ψ_0(Ω+1) = ω^{ε₀+1} = ε₀·ω`
(`psi(W)*w`), `ψ_0(Ω+ψ_0(Ω)) = ω^{ε₀·2} = ε₀^2` (`psi(W)^2`), `ψ_1(1) = ω^{Ω+1} = Ω·ω`
(`W*w`), `ψ_1(ψ_0(Ω)) = Ω·ω^{ε₀} = Ω·ε₀` (`W*psi(W)`), `ψ_1(Ω) = Ω^2`.

The first case is proved here in the ordinals: `val_psi_Omega_add`, from
`Ord.psi_Omega_add_eq` (`ψ_0(Ω + x) = ε₀·ω^x` below `ε₁`):
`ψ_0(Ω + t) = ω^{ε₀ + t}`.  The general identity is the continuity of `ψ_a` in the
part of the argument below `Ω_{a+1}` (`ψ_a(x+1) = ψ_a(x)·ω`, and `ψ_a` is continuous
at limits of cofinality below `Ω_{a+1}`); it is **not** proved here.

## Change 2: an infinite subscript is written with its cardinal

The program has two ways to write a collapse at level `c`: the index `psi_c(X)`,
which the sheet uses only for finite `c` (`psi_1(W_2)`, `psi_2(W_3)`), and the
cardinal `psi_{Ω_{c+1}}(X)` (rule 9, `isPsiLevel`), which the sheet uses for every
infinite `c` (`psi_W_(w+1)(W_(w+1))` is `ψ_ω(Ω_{ω+1})`, `psi_W_(W+1)(W_(W+1))` is
`ψ_Ω(Ω_{Ω+1})`).  `ofTerm` wrote `ψ_c(X)` as `psi_c(X)` for every `c`; for `c = Ω_u`
that is the program's cardinal form `psi_{Ω_u}(X)`, a collapse **below** `Ω_u`,
so `ψ_Ω(Ω_{Ω+1})` was read as `ψ_{Ω_1}(Ω_{Ω+1}) < Ω`; for `c = ω` the index form
`psi_w(X)` is not what rule 9 treats, and the matrix is not the sheet's row.  `psiAtom` writes an
infinite subscript `c` as the cardinal `Ω_{c+1}`.  On the five sheet rows of this
kind that are terms with finite nesting, the reading then gives the label exactly
(`TrioFixOfTermSheet.lean`).  Change 2 acts only on `ψ_c(b)` with `c` infinite and
`b_hi ≠ 0`; it can be dropped (set `psiAtom cf X := .psi cf X`) without touching
change 1.

## The change, for merging

Only the reading of terms changes.  **No definition of the builder changes**: the
map on labels (`trioRuleMatrixOfAll`), `MAll`, and every sheet check of
`TrioRulesAllSheet.lean` are untouched.  The patch adds

* `ofTermFix : Term → Od` in place of `TrioRules.ofTerm` (computed by `partsFix`,
  which also returns the `b_hi`/`b_lo` split of a sum against a subscript);
* `trioMatrixLFix α := trioRuleMatrixAll (ofTermFix α)` in place of
  `TrioRules.trioMatrixL α = trioRuleMatrix (ofTerm α)`.

A merge replaces the body of `ofTerm` by `ofTermFix` (or points `trioMatrixL` at
it).  `ofTermFix_allNil` proves it equals `ofTerm` below `ε₀` (every subscript `0`),
so `Trio.lean`'s range, `TrioRulesE0.lean` and `TrioRulesFuel.lean` are unaffected.

## What changes elsewhere

`TrioTree*.lean` prove `trioMatrixL = trioE`, standardness and the order on the
terms with subscripts `0`/`1` (`Sub01`), for the **old** reading.  Those theorems
stay true as stated, but they are about the old map.  For the new map
(`TrioFixOfTermSheet.lean`, computations only):

* it differs from the old one on 484 of the 610 terms of `TrioTree.smallFrag 6`, and
  keeps their order there (0 disagreements, 0 collisions);
* on the 2,397 terms with at most 7 `ψ`s it fails the order on 127 pairs, all with
  the one term `ψ_0(ψ_1(ψ_0(Ω + ψ_0(Ω+1))))`, whose matrix is not standard.  That is
  a defect of the builder, not of the reading: the reading gives it exactly the label
  `psi(W*psi(W)^psi(W)^w)` (`ψ_1(x) = Ω·ω^x`), and the builder writes `ω^{ε₀·ω}` as the tree of
  `ψ_0(ψ_0(Ω+1))` instead of `ψ_0(Ω+ψ_0(Ω+1))` (rule 1's `strip` uncollapses an
  exponent only when its head is a `ψ` atom).  The old map wrote the tree of the term
  there, which is why it kept the order;
* with larger subscripts the new map meets more builder defects that the old reading
  never reached: below `Ω_Ω` with subscripts `0, 1, ω` (537 terms) 63 order
  disagreements (old: 0), all between ordinals of which at least one has no sheet row;
  with subscripts `0, 1, Ω` 137 (old: 58,277, from the subscript misreading of
  change 2's kind).  The reading itself keeps the order on every family checked (the
  program's `cmpOrd` of the normal forms, 0 disagreements).
-/

namespace Googology.Trans.BMS.TrioFixOfTerm

open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term
open Googology.Trans.BMS (AllNil)
open Googology.Trans.BMS.TrioRules
open Googology.Trans.BMS.TrioRulesAll

/-! ### The reading -/

/-- A subscript the program writes as an index (`psi_1`, `psi_2`): `0` or a finite
number.  Any other subscript `c` is written with the cardinal `Ω_{c+1}`
(`psi_W_(w+1)` for `ψ_ω`). -/
def finSub (cf : Od) : Bool :=
  match cf with
  | [] => true
  | [(.o [], _)] => true
  | _ => false

/-- The atom `ψ_c(X)` in the program's notation: `psi_c(X)` for a finite `c`,
`psi_{Ω_{c+1}}(X)` otherwise (change 2). -/
def psiAtom (cf X : Od) : Ex :=
  if finSub cf then .psi cf X else .psi [(.W (add cf one), 1)] X

/-- The normal form of one summand `ψ_c(d)`, from `cf = ofTermFix c`, `c0 = (c = 0)`,
and `(hi, lo)`, the normal forms of the parts of `d` above and below `Ω_{c+1}`
(change 1). -/
def summandFix (c0 : Bool) (cf hi lo : Od) : Od :=
  let base : Od :=
    if hi.isEmpty then (if c0 then [] else [(.W cf, 1)]) else [(psiAtom cf hi, 1)]
  if lo.isEmpty then (if base.isEmpty then one else base) else wpow (add base lo)

/-- `partsFix x a = (ofTermFix x, hi, lo)`: the normal form of `x`, and those of the
sums of its summands `ψ_c(d)` with `c > a` and with `c ≤ a`. -/
def partsFix : Term → Term → Od × Od × Od
  | nil, _ => ([], [], [])
  | cons c d u, a =>
    let q := partsFix d c
    let s := summandFix (c == nil) (partsFix c nil).1 q.2.1 q.2.2
    let p := partsFix u a
    (add s p.1, if Term.cmp c a == .gt then (add s p.2.1, p.2.2) else (p.2.1, add s p.2.2))

/-- **The reading of a term** into the rules' normal form. -/
def ofTermFix (x : Term) : Od := (partsFix x nil).1

/-- **The trio matrix of `ψ_0(Ω_α)` for a term `α`**, with the corrected reading and
the merged rules. -/
def trioMatrixLFix (α : Term) : List (List Nat) := trioRuleMatrixAll (ofTermFix α)

/-- Every column of it is three rows deep with `z < 2`. -/
theorem WF3_trioMatrixLFix (α : Term) : Googology.Trans.BMS.WF3 (trioMatrixLFix α) :=
  WF3_trioRuleMatrixAll _

/-! ### Below `ε₀` nothing changes -/

theorem add_nil_left (b : Od) : add [] b = b := by
  cases b <;> simp [add]

theorem add_ne_nil (a : Od) {b : Od} (h : b ≠ []) : add a b ≠ [] := by
  cases b with
  | nil => exact absurd rfl h
  | cons x bt =>
    simp only [add]
    split <;> simp

theorem add_nil_right (a : Od) : add a [] = a := by simp [add]

theorem ofTerm_eq_nil_iff : ∀ x : Term, ofTerm x = [] ↔ x = nil
  | nil => by simp [ofTerm]
  | cons a b t => by
    constructor
    · intro h
      exfalso
      unfold ofTerm at h
      cases ht : ofTerm t with
      | nil =>
        rw [ht, add_nil_right] at h
        revert h
        split
        · split <;> [simp [one, nat]; split <;> simp [wpow]]
        · split <;> simp
      | cons y ys => exact add_ne_nil _ (by simp) (ht ▸ h)
    · intro h; cases h

/-- On a term with every subscript `0`, `partsFix` against `0` puts everything in the
lower part, and the reading is `ofTerm`'s. -/
theorem partsFix_allNil : ∀ x : Term, AllNil x → partsFix x nil = (ofTerm x, [], ofTerm x)
  | nil, _ => rfl
  | cons a b t, h => by
    obtain ⟨rfl, hb, ht⟩ := h
    have ihb := partsFix_allNil b hb
    have iht := partsFix_allNil t ht
    have hs : summandFix (nil == nil) [] (partsFix b nil).2.1
        (partsFix b nil).2.2 = (if b = nil then one else wpow (ofTerm b)) := by
      rw [ihb]
      by_cases hbn : b = nil
      · subst hbn; simp [summandFix, ofTerm]
      · have : (ofTerm b).isEmpty = false := by
          cases hh : ofTerm b with
          | nil => exact absurd ((ofTerm_eq_nil_iff b).mp hh) hbn
          | cons _ _ => rfl
        simp [summandFix, this, hbn, add_nil_left]
    have hcmp : (Term.cmp nil nil == Ordering.gt) = false := by simp [Term.cmp]
    have hof : ofTerm (cons nil b t) = add (if b = nil then one else wpow (ofTerm b)) (ofTerm t) := by
      by_cases hbn : b = nil
      · subst hbn; simp [ofTerm]
      · simp [ofTerm, hbn, TrioRulesE0.omegaFree_of_allNil b hb]
    simp only [partsFix, hs, iht, hcmp, Bool.false_eq_true, if_false, hof]

/-- **Below `ε₀` the reading is unchanged.** -/
theorem ofTermFix_allNil (x : Term) (h : AllNil x) : ofTermFix x = ofTerm x := by
  simp [ofTermFix, partsFix_allNil x h]

/-- So is the matrix, given by the merged rules. -/
theorem trioMatrixLFix_allNil (x : Term) (h : AllNil x) :
    trioMatrixLFix x = trioRuleMatrixAll (ofTerm x) := by
  rw [trioMatrixLFix, ofTermFix_allNil x h]

/-! ### The case the plan names: `ψ_0(Ω + t) = ω^{ε₀ + t}` -/

open Ordinal in
/-- **`ψ_0(Ω + t) = ω^{ε₀ + t} = ε₀·ω^t`** for `t < ε₁`, in the ordinals (the value of
the term).  `ofTermFix` writes it as `ω^{E + t}` with the atom `E = ψ_0(Ω)`; the old
reading wrote it as the atom `ψ_0(Ω + t)`, a fixed point of `ω^·`, which it is not. -/
theorem val_psi_Omega_add (t : Term) (h : t.val < Ord.eps1.{0}) :
    (psi nil (cons t1 nil t)).val = Ord.eps0.{0} * ω ^ t.val ∧
    (psi nil (cons t1 nil t)).val = ω ^ (Ord.eps0.{0} + t.val) := by
  have h1 : t1.val = 1 := by
    simp [t1, Ord.psi_zero_arg]
  have hv : (psi nil (cons t1 nil t)).val = Ord.psi (Ord.Omega 1 + t.val) 0 := by
    simp [h1, Ord.psi_zero_arg]
  refine ⟨by rw [hv, Ord.psi_Omega_add_eq _ h], ?_⟩
  rw [hv, Ord.psi_Omega_add_eq _ h, Ordinal.opow_add, Ord.opow_eps0]

/-- The normal form `ofTermFix` gives `ψ_0(Ω + 1)`: `ω^{E + 1}`, the program's
`psi(W)*w`. -/
theorem ofTermFix_psi_Omega_one :
    ofTermFix (psi nil (cons t1 nil t1)) =
      wpow [(.psi [] [(.W one, 1)], 1), (.o [], 1)] := by
  rfl

/-! ### What changes for `TrioTree`

`TrioTreeRules.lean` proves, for the old reading, that on the standard `α < Ω` with
subscripts `0`/`1` (`Sub01`) and `dep α ≤ 200` the matrix is `trioE α`, is standard,
and that the map preserves and reflects the order (`trioMatrixL_lt_iff`).  With the
new reading the order statement is **false**: `ε_{ε₀} = ψ_0(ψ_1(ψ_0(Ω))) <
β = ψ_0(ψ_1(ψ_0(Ω + ψ_0(Ω+1))))`, both in that fragment, but the new matrices are the
other way round.  (`β`'s new matrix is also not standard by yaBMS `bms -s`; that is
not proved here.)  The cause is the builder: it writes the exponent `ω^{ε₀·ω}` of
`β`'s label `psi(W*psi(W)^psi(W)^w)` as the tree of `ψ_0(ψ_0(Ω+1))`. -/

/-- `ψ_0(ψ_1(ψ_0(Ω))) = ψ_0(Ω·ε₀) = ε_{ε₀}`. -/
abbrev tα : Term := psi nil (psi t1 Googology.Trans.BMS.te0)

/-- `β = ψ_0(ψ_1(ψ_0(Ω + ψ_0(Ω+1)))) = ψ_0(Ω·ε₀^{ε₀^ω})`. -/
abbrev tβ : Term := psi nil (psi t1 (psi nil (cons t1 nil (psi nil (cons t1 nil t1)))))

theorem trioMatrixLFix_tα :
    trioMatrixLFix tα = [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[4,1,0],[5,0,0],[6,1,0]] := by
  decide +kernel

theorem trioMatrixLFix_tβ : trioMatrixLFix tβ =
    [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[4,1,0],[5,0,0],[6,0,0],[7,1,0],[7,0,0]] := by
  decide +kernel

open Googology.Trans.BMS.TrioTree (Sub01) in
open Googology.Trans.BMS.TrioRulesE0 (dep) in
/-- **The new map does not keep the order on `TrioTree`'s fragment**: `tα < tβ`, both
standard, countable, with subscripts `0`/`1` and depth `≤ 200`, but
`trioMatrixLFix tβ < trioMatrixLFix tα`.  The old map orders them correctly
(`TrioTreeRules.trioMatrixL_lt_iff`). -/
theorem trioMatrixLFix_order_fails :
    OT tα ∧ OT tβ ∧ tα < tW ∧ tβ < tW ∧ Sub01 tα ∧ Sub01 tβ ∧
      dep tα ≤ 200 ∧ dep tβ ≤ 200 ∧ tα < tβ ∧
      trioMatrixLFix tβ < trioMatrixLFix tα ∧ trioMatrixL tα < trioMatrixL tβ := by
  have oa : OT tα := by decide
  have ob : OT tβ := by decide
  have ca : tα < tW := by decide
  have cb : tβ < tW := by decide
  have sa : Sub01 tα := by simp [Sub01, psi, t1]
  have sb : Sub01 tβ := by simp [Sub01, psi, t1]
  have da : dep tα ≤ 200 := by decide
  have db : dep tβ ≤ 200 := by decide
  have lt : tα < tβ := by decide
  refine ⟨oa, ob, ca, cb, sa, sb, da, db, lt, ?_, ?_⟩
  · rw [trioMatrixLFix_tα, trioMatrixLFix_tβ]; decide
  · exact (Googology.Trans.BMS.TrioTreeRules.trioMatrixL_lt_iff oa ob ca cb sa sb da db).2 lt

open Googology.Trans.BMS.TrioTree (Sub01) in
open Googology.Trans.BMS.TrioRulesE0 (dep) in
/-- **So `TrioTreeRules.trioMatrixL_lt_iff` does not carry over to the new map.** -/
theorem not_trioMatrixLFix_lt_iff :
    ¬ ∀ α β : Term, OT α → OT β → α < tW → β < tW → Sub01 α → Sub01 β →
      dep α ≤ 200 → dep β ≤ 200 → (trioMatrixLFix α < trioMatrixLFix β ↔ α < β) := by
  intro h
  obtain ⟨oa, ob, ca, cb, sa, sb, da, db, lt, hm, -⟩ := trioMatrixLFix_order_fails
  have := (h tα tβ oa ob ca cb sa sb da db).2 lt
  exact absurd (List.lt_trans this hm) (List.lt_irrefl _)

end Googology.Trans.BMS.TrioFixOfTerm

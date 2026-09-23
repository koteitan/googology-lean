import Googology.Trans.BMS.TrioRules
import Googology.Trans.BMS.TrioStd

/-!
# Rules 1–10 agree with `Trio.lean` below `ε₀`

`TrioRules.lean` transcribes the program behind rules 1–10
(`TrioRules.trioMatrixL`), and checks it against `Trio.lean`'s `trioMatrix` on
the rows of the table with `#guard`.  This file proves the agreement for every
standard `α < ε₀` whose nesting depth is at most `201`:

  `trioMatrixL α = trioMatrix α`   (`trioMatrixL_eq_trioMatrix`)

under one hypothesis, `PredBetaSpec`, explained below.  `trioMatrix α` is
`omegaIndexMatrix α` there (`TrioStd.trioMatrix_allNil`).

## The depth bound, and what the fuel does

`dep 0 = 0` and `dep (ψ_a(b) + t) = max (dep b + 1) (dep t)`, so `dep 1 = 1`,
`dep ω = 2` and a tower `ω^ω^…^ω` of height `k` has depth `k + 1`.

Below `ε₀` the fuel `200` of `TrioRules.lean` is used in three places:

* `cmpF 200`, inside `ofTerm`'s `add`, compares two exponents of the same
  normal form.  With fuel `n ≥ dep a, dep b` it is the term order
  (`cmpF_ofTerm`), so `ofTerm` groups the summands correctly (`inv_all`) when
  `dep α ≤ 201`.
* `blockF 200` writes the one-row embedding of an exponent `γ` of an exponent
  of `α`; it is exact when `dep γ ≤ 200` (`prO_ofTerm`), which `dep α ≤ 201`
  gives with room to spare.
* `lvlF 200` and `tailBlockF 200` return `none` on countable input whatever the
  fuel (`lvlF_ex`, `tailBlockF_ofTerm`).

So `dep α ≤ 201` is a fuel bound that is provably enough.  It is not needed
for every term: the `#guard`s at the end show that on the towers the map still
agrees at depth `202`, and disagrees from depth `203` on (there `blockF 200`
cuts the embedding one column short).  So fuel `200` is **not** enough for all
`α < ε₀`; the statement needs a depth bound.

## `PredBetaSpec`

`TrioRules.Ex` derives `BEq`.  For a nested inductive Lean compiles the derived
`==` to an `opaque` function, so nothing can be proved about `e == .o []`, and
`TrioRules.predBeta` branches on exactly that.  The theorem therefore takes as
a hypothesis what `predBeta` is meant to do (`1 + β' = β`):

  `predBeta ((.o X, k) :: r) = if X.isEmpty then nat (k - 1) else (.o X, k) :: r`

The compiled program satisfies it (checked by `#guard` below).  If
`TrioRules.predBeta` tested the head by a pattern match instead,
`match e with | .o [] => nat (k - 1) | _ => beta`, the hypothesis would be
proved by `cases X <;> rfl` and the theorem would hold outright.

## How the proof goes

* **Terms.**  `Inv x`: `ofTerm x` is the list of the exponents of `x` with their
  multiplicities, strictly decreasing (`GDesc`).  `cmpF_ofTerm` and `inv_all`
  prove it and the correctness of `cmpF` together, by induction on the depth.
* **The state monad.**  `Spec p Q w` says that from any state with
  `regime = none` the program `p` returns a value satisfying `Q`, appends `w`
  to the columns and keeps `regime = none`.  Below `ε₀` the regime is `none`
  throughout, so `spent` is always `false` and no storey is laid; the lemmas
  `spec_bind`, `spec_get_bind`, `spec_modify_bind`, `spec_forIn` and the step
  tactic `trioE0_step` walk through the `do` blocks.
* **`blockF`** writes `prO`, the embedding cut at the fuel (`blockF_spec`),
  which is `unread` when the fuel covers the depth (`prO_ofTerm`).
* **`placeUnits`** lays one add unit per summand, as `addUnits` does
  (`loop_units`, `placeUnits_ofTerm`), and `finish` adds nothing because
  `tailLevel` is `none` (`tailLevel_ofTerm`).
-/

namespace Googology.Trans.BMS.TrioRulesE0

open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term
open Googology.Trans.BMS (AllNil DescAll trioMatrix omegaIndexMatrix)
open Googology.Trans.BMS.TrioRules

def dep : Term → Nat
  | nil => 0
  | cons _ b t => max (dep b + 1) (dep t)

def exps : Term → List Term
  | nil => []
  | cons _ b t => b :: exps t

def ex (b : Term) : Ex := .o (ofTerm b)

def expandG (L : List (Term × Nat)) : List Term := L.flatMap (fun p => List.replicate p.2 p.1)

def GDesc : List (Term × Nat) → Prop
  | [] => True
  | [p] => 0 < p.2
  | p :: q :: r => 0 < p.2 ∧ Term.cmp q.1 p.1 = .lt ∧ GDesc (q :: r)

def grp (L : List (Term × Nat)) : Od := L.map (fun p => (ex p.1, p.2))

def Inv (x : Term) : Prop := ∃ L, GDesc L ∧ ofTerm x = grp L ∧ expandG L = exps x

def H (x : Term) : Prop := AllNil x ∧ DescAll x

def lexc : List Term → List Term → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys => (Term.cmp x y).then (lexc xs ys)

theorem omegaFree_of_allNil : ∀ x : Term, AllNil x → omegaFree x = true := by
  intro x
  induction x with
  | nil => intro _; rfl
  | cons a b t _ ihb iht =>
    intro h
    obtain ⟨ha, hb, ht⟩ := h
    subst ha
    simp [omegaFree, ihb hb, iht ht]

theorem ofTerm_cons (b t : Term) (hb : AllNil b) :
    ofTerm (cons nil b t) = add [(ex b, 1)] (ofTerm t) := by
  by_cases h : b = nil
  · subst h; simp [ofTerm, one, nat, ex]
  · simp [ofTerm, h, omegaFree_of_allNil b hb, wpow, ex]

theorem ofTerm_nil : ofTerm nil = [] := rfl

theorem cmp_allNil : ∀ a b : Term, AllNil a → AllNil b → Term.cmp a b = lexc (exps a) (exps b) := by
  intro a
  induction a with
  | nil => intro b _ _; cases b <;> rfl
  | cons a1 b1 t1 _ _ iht =>
    intro b ha hb
    cases b with
    | nil => rfl
    | cons a2 b2 t2 =>
      obtain ⟨h1, -, ht1⟩ := ha
      obtain ⟨h2, -, ht2⟩ := hb
      subst h1; subst h2
      simp only [Term.cmp, exps]
      rw [iht t2 ht1 ht2]
      rfl

theorem compare_succ_succ (n m : Nat) : compare (n+1) (m+1) = compare n m := by
  simp [compare, compareOfLessAndEq]

theorem cmpOrdWith_nil_nil (c : Od → Od → Ordering) : cmpOrdWith c [] [] = .eq := by
  simp [cmpOrdWith]

theorem cmpOrdWith_nil_cons (c : Od → Od → Ordering) (y : Ex × Nat) (b : Od) :
    cmpOrdWith c [] (y :: b) = .lt := by
  simp [cmpOrdWith, compare, compareOfLessAndEq]

theorem cmpOrdWith_cons_nil (c : Od → Od → Ordering) (x : Ex × Nat) (a : Od) :
    cmpOrdWith c (x :: a) [] = .gt := by
  simp [cmpOrdWith, compare, compareOfLessAndEq]

theorem cmpOrdWith_cons (c : Od → Od → Ordering) (x y : Ex × Nat) (a b : Od) :
    cmpOrdWith c (x :: a) (y :: b) =
      ((cmpExpWith c x.1 y.1).then (compare x.2 y.2)).then (cmpOrdWith c a b) := by
  simp only [cmpOrdWith, List.zip_cons_cons, List.map_cons, List.foldr_cons, List.length_cons,
    compare_succ_succ]

theorem cmpExpWith_ex (c : Od → Od → Ordering) (p q : Term) :
    cmpExpWith c (ex p) (ex q) = c (ofTerm p) (ofTerm q) := rfl

theorem GDesc_tail {p : Term × Nat} {L : List (Term × Nat)} (h : GDesc (p :: L)) : GDesc L := by
  cases L with
  | nil => simp [GDesc]
  | cons q r => exact h.2.2

theorem GDesc_pos : ∀ {L : List (Term × Nat)}, GDesc L → ∀ p ∈ L, 0 < p.2 := by
  intro L
  induction L with
  | nil => intro _ p hp; cases hp
  | cons q r ih =>
    intro h p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · cases r with
      | nil => simpa [GDesc] using h
      | cons _ _ => exact h.1
    · exact ih (GDesc_tail h) p hp

theorem GDesc_head_pos {p : Term × Nat} {L : List (Term × Nat)} (h : GDesc (p :: L)) : 0 < p.2 :=
  GDesc_pos h p List.mem_cons_self

/-- The first entry after a group is below the group's exponent. -/
theorem GDesc_next {p : Term × Nat} {L : List (Term × Nat)} (h : GDesc (p :: L)) :
    ∀ e ∈ (expandG L).head?, Term.cmp e p.1 = .lt := by
  intro e he
  cases L with
  | nil => simp [expandG] at he
  | cons q r =>
    have hq : 0 < q.2 := GDesc_head_pos h.2.2
    obtain ⟨k, hk⟩ : ∃ k, q.2 = k + 1 := ⟨q.2 - 1, by omega⟩
    simp [expandG, List.flatMap_cons, hk, List.replicate_succ] at he
    subst he
    exact h.2.1

theorem mem_expandG {L : List (Term × Nat)} (h : GDesc L) {p : Term × Nat} (hp : p ∈ L) :
    p.1 ∈ expandG L := by
  have := GDesc_pos h p hp
  simp only [expandG, List.mem_flatMap]
  exact ⟨p, hp, List.mem_replicate.mpr ⟨by omega, rfl⟩⟩

theorem lexc_rep (e : Term) (E1 E2 : List Term)
    (h1 : ∀ x ∈ E1.head?, Term.cmp x e = .lt) (h2 : ∀ x ∈ E2.head?, Term.cmp x e = .lt) :
    ∀ k1 k2 : Nat, lexc (List.replicate k1 e ++ E1) (List.replicate k2 e ++ E2) =
      (compare k1 k2).then (lexc E1 E2) := by
  intro k1
  induction k1 with
  | zero =>
    intro k2
    cases k2 with
    | zero => simp [compare, compareOfLessAndEq, Ordering.then]
    | succ m =>
      simp only [List.replicate_zero, List.nil_append, List.replicate_succ, List.cons_append]
      cases E1 with
      | nil => simp [lexc, compare, compareOfLessAndEq, Ordering.then]
      | cons x xs =>
        have := h1 x (by simp)
        simp [lexc, this, compare, compareOfLessAndEq, Ordering.then]
  | succ m ih =>
    intro k2
    cases k2 with
    | zero =>
      simp only [List.replicate_zero, List.nil_append, List.replicate_succ, List.cons_append]
      cases E2 with
      | nil => simp [lexc, compare, compareOfLessAndEq, Ordering.then]
      | cons x xs =>
        have h := h2 x (by simp)
        have hs := cmp_swap x e
        rw [h] at hs
        simp [lexc, ← hs, compare, compareOfLessAndEq, Ordering.then, Ordering.swap]
    | succ m' =>
      simp only [List.replicate_succ, List.cons_append, lexc, cmp_self, compare_succ_succ]
      rw [← ih m']
      rfl

theorem lexc_grp (c : Od → Od → Ordering) :
    ∀ L1 L2 : List (Term × Nat), GDesc L1 → GDesc L2 →
      (∀ p ∈ L1, ∀ q ∈ L2, c (ofTerm p.1) (ofTerm q.1) = Term.cmp p.1 q.1) →
      cmpOrdWith c (grp L1) (grp L2) = lexc (expandG L1) (expandG L2) := by
  intro L1
  induction L1 with
  | nil =>
    intro L2 _ h2 _
    cases L2 with
    | nil => simp [grp, expandG, cmpOrdWith_nil_nil, lexc]
    | cons q r =>
      have hq := GDesc_head_pos h2
      obtain ⟨k, hk⟩ : ∃ k, q.2 = k + 1 := ⟨q.2 - 1, by omega⟩
      simp [grp, expandG, cmpOrdWith_nil_cons, hk, List.replicate_succ, lexc]
  | cons p r ih =>
    intro L2 h1 h2 hc
    cases L2 with
    | nil =>
      have hp := GDesc_head_pos h1
      obtain ⟨k, hk⟩ : ∃ k, p.2 = k + 1 := ⟨p.2 - 1, by omega⟩
      simp [grp, expandG, cmpOrdWith_cons_nil, hk, List.replicate_succ, lexc]
    | cons q s =>
      have ihr := ih s (GDesc_tail h1) (GDesc_tail h2)
        (fun p' hp' q' hq' => hc p' (List.mem_cons_of_mem _ hp') q' (List.mem_cons_of_mem _ hq'))
      have hpq := hc p List.mem_cons_self q List.mem_cons_self
      have e1 : grp (p :: r) = (ex p.1, p.2) :: grp r := rfl
      have e2 : grp (q :: s) = (ex q.1, q.2) :: grp s := rfl
      have f1 : expandG (p :: r) = List.replicate p.2 p.1 ++ expandG r := by
        simp [expandG]
      have f2 : expandG (q :: s) = List.replicate q.2 q.1 ++ expandG s := by
        simp [expandG]
      rw [e1, e2, cmpOrdWith_cons, cmpExpWith_ex, hpq, ihr, f1, f2]
      have hp := GDesc_head_pos h1
      have hq := GDesc_head_pos h2
      obtain ⟨k, hk⟩ : ∃ k, p.2 = k + 1 := ⟨p.2 - 1, by omega⟩
      obtain ⟨k', hk'⟩ : ∃ k, q.2 = k + 1 := ⟨q.2 - 1, by omega⟩
      cases hcm : Term.cmp p.1 q.1 with
      | lt =>
        simp [hk, hk', List.replicate_succ, lexc, hcm, Ordering.then]
      | gt =>
        simp [hk, hk', List.replicate_succ, lexc, hcm, Ordering.then]
      | eq =>
        have he : p.1 = q.1 := cmp_eq_iff.mp hcm
        rw [he, lexc_rep q.1 (expandG r) (expandG s) (he ▸ GDesc_next h1) (GDesc_next h2)]
        rfl


theorem mem_exps : ∀ a p : Term, p ∈ exps a → H a → H p ∧ dep p + 1 ≤ dep a := by
  intro a
  induction a with
  | nil => intro p hp; cases hp
  | cons a1 b t _ _ iht =>
    intro p hp h
    obtain ⟨⟨_, hAb, hAt⟩, hDb, hDt, _⟩ := h
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨⟨hAb, hDb⟩, by simp [dep]⟩
    · obtain ⟨h1, h2⟩ := iht p hp ⟨hAt, hDt⟩
      exact ⟨h1, by simp only [dep]; omega⟩

theorem H_tail {a b t : Term} (h : H (cons a b t)) : H t := ⟨h.1.2.2, h.2.2.1⟩
theorem H_arg {a b t : Term} (h : H (cons a b t)) : H b := ⟨h.1.2.1, h.2.1⟩

theorem dep_eq_zero {a : Term} (h : dep a = 0) : a = nil := by
  cases a with
  | nil => rfl
  | cons _ _ _ => simp [dep] at h

theorem cmpF_nil_nil (n : Nat) : cmpF n [] [] = .eq := by
  cases n with
  | zero => rfl
  | succ n => exact cmpOrdWith_nil_nil _

/-- **`cmpF` is the term order**, on the grouped normal forms, with enough fuel. -/
theorem cmpF_ofTerm : ∀ m n : Nat, m ≤ n → (∀ x, H x → dep x ≤ m → Inv x) →
    ∀ a b : Term, H a → H b → dep a ≤ m → dep b ≤ m →
      cmpF n (ofTerm a) (ofTerm b) = Term.cmp a b := by
  intro m
  induction m with
  | zero =>
    intro n _ _ a b _ _ ha hb
    rw [dep_eq_zero (Nat.le_zero.mp ha), dep_eq_zero (Nat.le_zero.mp hb)]
    exact cmpF_nil_nil n
  | succ m ih =>
    intro n hmn hinv a b hHa hHb ha hb
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨L1, hG1, hO1, hE1⟩ := hinv a hHa ha
    obtain ⟨L2, hG2, hO2, hE2⟩ := hinv b hHb hb
    show cmpOrdWith (cmpF n') (ofTerm a) (ofTerm b) = _
    rw [hO1, hO2, lexc_grp _ L1 L2 hG1 hG2, hE1, hE2, cmp_allNil a b hHa.1 hHb.1]
    intro p hp q hq
    have hp' := mem_exps a p.1 (hE1 ▸ mem_expandG hG1 hp) hHa
    have hq' := mem_exps b q.1 (hE2 ▸ mem_expandG hG2 hq) hHb
    exact ih n' (by omega) (fun x hx hd => hinv x hx (by omega)) p.1 q.1 hp'.1 hq'.1
      (by omega) (by omega)

theorem add_gt {x lead : Ex} {cb : Nat} {bt : Od} (h : cmpExp x lead = .gt) :
    add [(x, 1)] ((lead, cb) :: bt) = (x, 1) :: (lead, cb) :: bt := by
  simp [add, h]

theorem add_eq {x lead : Ex} {cb : Nat} {bt : Od} (h : cmpExp x lead = .eq) :
    add [(x, 1)] ((lead, cb) :: bt) = (lead, 1 + cb) :: bt := by
  simp [add, h]

theorem cmp_le_of_desc {b d t' : Term} (h : DescAll (cons nil b (cons nil d t'))) :
    Term.cmp d b ≠ .gt := by
  have := h.2.2
  simp only [descHead, head?, decide_eq_true_eq] at this
  have e : Term.cmp (psi nil d) (psi nil b) = Term.cmp d b := by
    simp only [Term.cmp]
    cases Term.cmp d b <;> rfl
  rw [← e]; exact this

theorem GDesc_bump {d : Term} {k : Nat} {L : List (Term × Nat)} (h : GDesc ((d, k) :: L)) :
    GDesc ((d, 1 + k) :: L) := by
  cases L with
  | nil => simp [GDesc]
  | cons q r => exact ⟨by omega, h.2.1, h.2.2⟩

/-- **`ofTerm` groups the summands**: on a standard term of depth at most `201`,
it is the list of exponents with multiplicities. -/
theorem inv_all : ∀ m : Nat, m ≤ 201 → ∀ x, H x → dep x ≤ m → Inv x := by
  intro m
  induction m with
  | zero =>
    intro _ x _ hx
    rw [dep_eq_zero (Nat.le_zero.mp hx)]
    exact ⟨[], trivial, rfl, rfl⟩
  | succ m ih =>
    intro hm x
    have hQ := ih (by omega)
    induction x with
    | nil => intro _ _; exact ⟨[], trivial, rfl, rfl⟩
    | cons a b t _ _ iht =>
      intro hH hd
      obtain ⟨⟨ha, hAb, hAt⟩, hDb, hDt, _⟩ := hH
      subst ha
      have hdt : dep t ≤ m + 1 := by simp only [dep] at hd; omega
      have hdb : dep b ≤ m := by simp only [dep] at hd; omega
      obtain ⟨Lt, hGt, hOt, hEt⟩ := iht ⟨hAt, hDt⟩ hdt
      unfold Inv
      rw [ofTerm_cons b t hAb, hOt]
      cases Lt with
      | nil =>
        refine ⟨[(b, 1)], by simp [GDesc], rfl, ?_⟩
        simp [expandG, exps] at hEt ⊢
        exact hEt
      | cons p L' =>
        obtain ⟨d, k⟩ := p
        have hk : 0 < k := GDesc_head_pos hGt
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        -- `t` starts with `ψ_0(d)`
        cases t with
        | nil => simp [expandG, exps, List.replicate_succ] at hEt
        | cons a' d' t' =>
          have hd' : d' = d := by
            simp [expandG, exps, List.replicate_succ] at hEt; exact hEt.1.symm
          subst hd'
          have ha' : a' = nil := hAt.1
          subst ha'
          have hle : Term.cmp d' b ≠ .gt := cmp_le_of_desc ⟨hDb, hDt, ‹_›⟩
          have hdd : dep d' ≤ m := by simp only [dep] at hdt; omega
          have hc : cmpExp (ex b) (ex d') = Term.cmp b d' :=
            cmpF_ofTerm m fuel (by simp [fuel]; omega) hQ b d' ⟨hAb, hDb⟩
              ⟨hAt.2.1, hDt.1⟩ hdb hdd
          have hsw := cmp_swap b d'
          cases hbd : Term.cmp b d' with
          | lt => rw [hbd] at hsw; exact absurd hsw.symm hle
          | gt =>
            rw [hbd] at hc hsw
            refine ⟨(b, 1) :: (d', k' + 1) :: L', ⟨by omega, hsw.symm, hGt⟩, ?_, ?_⟩
            · exact add_gt hc
            · simp only [expandG, List.flatMap_cons, exps] at hEt ⊢
              rw [hEt]; rfl
          | eq =>
            rw [hbd] at hc
            have hb : b = d' := cmp_eq_iff.mp hbd
            subst hb
            refine ⟨(b, 1 + (k' + 1)) :: L', GDesc_bump hGt, add_eq hc, ?_⟩
            simp only [expandG, List.flatMap_cons, exps] at hEt ⊢
            rw [show 1 + (k' + 1) = (k' + 1) + 1 by omega, List.replicate_succ, List.cons_append,
              hEt]


/-! ### Part 2: the builder on countable input -/

def Good (x : Term) : Prop := H x ∧ dep x ≤ 201

theorem Good.inv {x : Term} (h : Good x) : Inv x := inv_all 201 (le_refl _) x h.1 h.2

theorem Good.of_mem {x p : Term} (h : Good x) (hp : p ∈ exps x) : Good p :=
  let h' := mem_exps x p hp h.1
  ⟨h'.1, by have := h.2; omega⟩

theorem Good.mem_grp {x : Term} {L : List (Term × Nat)} (h : Good x) (hG : GDesc L)
    (hE : expandG L = exps x) {p : Term × Nat} (hp : p ∈ L) : Good p.1 :=
  h.of_mem (hE ▸ mem_expandG hG hp)

theorem lvlF_ex : ∀ (n : Nat) (x : Term), Good x → lvlF n (ex x) = none := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro x hx
    obtain ⟨L, hG, hO, hE⟩ := hx.inv
    show lvlF (n + 1) (.o (ofTerm x)) = none
    rw [hO]
    cases L with
    | nil => rfl
    | cons p L' =>
      show lvlF n (ex p.1) = none
      exact ih p.1 (hx.mem_grp hG hE List.mem_cons_self)

theorem lvl_ex {x : Term} (hx : Good x) : lvl (ex x) = none := lvlF_ex _ x hx

theorem ato_ex (x : Term) : ato (ex x) = ofTerm x := rfl

theorem strip_ex {x : Term} (hx : Good x) : strip (ex x) = ofTerm x := by
  obtain ⟨L, hG, hO, hE⟩ := hx.inv
  unfold strip
  rw [ato_ex, hO]
  cases L with
  | nil => rfl
  | cons p L' => rfl

theorem spent_none (Mf : Od → Cols) (c : Ctx) (h : c.regime = none) : spent Mf c = false := by
  unfold spent; rw [h]; split <;> simp_all

/-- A program on the builder's state that keeps `regime = none`, appends `w`
to the columns and returns a value satisfying `Q`. -/
def Spec {α : Type} (p : StateM Ctx α) (Q : α → Prop) (w : Array TrioRules.Col) : Prop :=
  ∀ s : Ctx, s.regime = none →
    ∃ a s', p.run s = (a, s') ∧ Q a ∧ s'.cols = s.cols ++ w ∧ s'.regime = none

theorem spec_pure {α : Type} {a : α} {Q : α → Prop} (h : Q a) : Spec (pure a) Q #[] := by
  intro s hs
  exact ⟨a, s, rfl, h, by simp, hs⟩

theorem spec_mono {α : Type} {p : StateM Ctx α} {Q Q' : α → Prop} {w : Array TrioRules.Col}
    (hp : Spec p Q w) (h : ∀ a, Q a → Q' a) : Spec p Q' w := by
  intro s hs
  obtain ⟨a, s', h1, h2, h3, h4⟩ := hp s hs
  exact ⟨a, s', h1, h a h2, h3, h4⟩

theorem spec_bind {α β : Type} {p : StateM Ctx α} {f : α → StateM Ctx β} {Q : α → Prop}
    {R : β → Prop} {w1 w2 w : Array TrioRules.Col} (hp : Spec p Q w1)
    (hf : ∀ a, Q a → Spec (f a) R w2) (hw : w1 ++ w2 = w) : Spec (p >>= f) R w := by
  intro s hs
  obtain ⟨a, s1, h1, hQ, hc1, hr1⟩ := hp s hs
  obtain ⟨b, s2, h2, hR, hc2, hr2⟩ := hf a hQ s1 hr1
  refine ⟨b, s2, ?_, hR, ?_, hr2⟩
  · show (f (p.run s).1).run (p.run s).2 = _
    rw [h1]; exact h2
  · rw [hc2, hc1, ← hw, Array.append_assoc]

theorem spec_get_bind {β : Type} {f : Ctx → StateM Ctx β} {R : β → Prop} {w : Array TrioRules.Col}
    (h : ∀ s : Ctx, s.regime = none → Spec (f s) R w) : Spec (get >>= f) R w := by
  intro s hs
  exact h s hs s hs

theorem spec_modify {g : Ctx → Ctx} {w : Array TrioRules.Col} (hg : ∀ c, (g c).regime = c.regime)
    (hc : ∀ c, (g c).cols = c.cols ++ w) : Spec (modify g) (fun _ => True) w := by
  intro s hs
  exact ⟨⟨⟩, g s, rfl, trivial, hc s, (hg s).trans hs⟩

theorem spec_modify0 {g : Ctx → Ctx} (hg : ∀ c, (g c).regime = c.regime)
    (hc : ∀ c, (g c).cols = c.cols) : Spec (modify g) (fun _ => True) #[] :=
  spec_modify hg (fun c => by rw [hc]; simp)

theorem spec_forIn {α β : Type} (l : List α) (f : α → β → StateM Ctx (ForInStep β))
    (Q : β → Prop) (w : α → List TrioRules.Col)
    (hf : ∀ a ∈ l, ∀ b, Q b →
      Spec (f a b) (fun r => ∃ b', r = .yield b' ∧ Q b') (w a).toArray) :
    ∀ b, Q b → Spec (forIn l b f) Q (l.flatMap w).toArray := by
  induction l with
  | nil => intro b hb; simpa using spec_pure hb
  | cons a l ih =>
    intro b hb
    rw [List.forIn_cons]
    refine spec_bind (w2 := (l.flatMap w).toArray) (hf a List.mem_cons_self b hb) ?_ (by simp)
    rintro r ⟨b', rfl, hb'⟩
    exact ih (fun a' ha' => hf a' (List.mem_cons_of_mem _ ha')) b' hb'

/-- The primitive-sequence columns `blockF` writes, with the fuel it is given. -/
def prO : Nat → Int → Od → List TrioRules.Col
  | 0, _, _ => []
  | n + 1, x, A => A.flatMap fun ec =>
      (List.range' 0 ec.2).flatMap fun _ => ⟨x, 0, false⟩ :: prO n (x + 1) (ato ec.1)

theorem spec_pure_bind {α β : Type} {a : α} {f : α → StateM Ctx β} {R : β → Prop}
    {W : Array TrioRules.Col} (h : Spec (f a) R W) : Spec (pure a >>= f) R W := by
  intro s hs; exact h s hs

theorem spec_modify0_bind {β : Type} {g : Ctx → Ctx} {f : PUnit → StateM Ctx β} {R : β → Prop}
    {W : Array TrioRules.Col} (hg : ∀ c, (g c).regime = c.regime) (hc : ∀ c, (g c).cols = c.cols)
    (h : Spec (f ⟨⟩) R W) : Spec (modify g >>= f) R W := by
  intro s hs
  obtain ⟨a, s', h1, h2, h3, h4⟩ := h (g s) ((hg s).trans hs)
  exact ⟨a, s', h1, h2, by rw [h3, hc], h4⟩

theorem spec_modify_bind {β : Type} {g : Ctx → Ctx} {f : PUnit → StateM Ctx β} {R : β → Prop}
    {w1 W : Array TrioRules.Col} (hg : ∀ c, (g c).regime = c.regime)
    (hc : ∀ c, (g c).cols = c.cols ++ w1)
    (h : Spec (f ⟨⟩) R W) : Spec (modify g >>= f) R (w1 ++ W) := by
  intro s hs
  obtain ⟨a, s', h1, h2, h3, h4⟩ := h (g s) ((hg s).trans hs)
  exact ⟨a, s', h1, h2, by rw [h3, hc, Array.append_assoc], h4⟩

theorem spec_bind_last {α β : Type} {p : StateM Ctx α} {f : α → StateM Ctx β} {Q : α → Prop}
    {R : β → Prop} {w1 : Array TrioRules.Col} (hp : Spec p Q w1)
    (hf : ∀ a, Q a → Spec (f a) R #[]) : Spec (p >>= f) R w1 :=
  spec_bind hp hf (by simp)

theorem spec_push_bind {β : Type} {g : Ctx → Ctx} {f : PUnit → StateM Ctx β} {R : β → Prop}
    {a : TrioRules.Col} {W : Array TrioRules.Col} (hg : ∀ c, (g c).regime = c.regime)
    (hc : ∀ c, (g c).cols = c.cols.push a)
    (h : Spec (f ⟨⟩) R W) : Spec (modify g >>= f) R (#[a] ++ W) :=
  spec_modify_bind hg (fun c => by rw [hc]; simp) h

macro "trioE0_step" : tactic => `(tactic| first
  | with_reducible refine spec_push_bind (fun _ => rfl) (fun _ => rfl) ?_
  | with_reducible refine spec_get_bind (fun _ _ => ?_)
  | with_reducible refine spec_pure_bind ?_
  | with_reducible refine spec_modify0_bind (fun _ => rfl) (fun _ => rfl) ?_
  | with_reducible refine spec_modify_bind (fun _ => rfl) (fun _ => rfl) ?_
  | with_reducible exact spec_pure ⟨_, rfl, rfl⟩
  | with_reducible exact spec_pure trivial)

theorem lastC_single (c : TrioRules.Col) : lastC #[c] = c := rfl

theorem blockF_spec (Mf : Od → Cols) : ∀ (n : Nat) (g : Term) (x d : Int) (arg : Bool)
    (plvl : Option Od) (py : Int), Good g →
    Spec (blockF Mf n (ofTerm g) x d arg plvl py) (fun _ => True) (prO n x (ofTerm g)).toArray := by
  intro n
  induction n with
  | zero => intro g x d arg plvl py _; simpa [blockF, prO] using spec_pure (Q := fun _ : Unit => True) trivial
  | succ n ih =>
    intro g x d arg plvl py hg
    obtain ⟨L, hG, hO, hE⟩ := hg.inv
    simp only [blockF]
    refine spec_bind (spec_mono (spec_forIn (ofTerm g) _ (fun r : MProd Int Int => r = ⟨d, x⟩)
      (fun ec => (List.range' 0 ec.2).flatMap fun _ => ⟨x, 0, false⟩ :: prO n (x + 1) (ato ec.1))
      ?_ (⟨d, x⟩ : MProd Int Int) rfl) (fun _ _ => trivial)) (fun _ _ => spec_pure trivial) (by simp [prO])
    intro ec hec b hb
    subst hb
    rw [hO] at hec
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hec
    have hgp := hg.mem_grp hG hE hp
    simp only [lvl_ex hgp, strip_ex hgp, ato_ex]
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    refine spec_bind (w2 := #[]) (spec_forIn _ _ (fun r : MProd Int Int => r = ⟨d, x⟩)
      (fun _ => ⟨x, 0, false⟩ :: prO n (x + 1) (ofTerm p.1)) ?_ (⟨d, x⟩ : MProd Int Int) rfl)
      (fun r hr => ?_) ?_
    · intro i _ b hb
      subst hb
      refine spec_get_bind fun s1 _ => spec_get_bind fun s2 hs2 => ?_
      rw [spent_none Mf s2 hs2]
      simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      rw [show (({ x := x, y := 0, z := false } :: prO n (x + 1) (ofTerm p.1)).toArray :
          Array TrioRules.Col) = #[⟨x, 0, false⟩] ++ (prO n (x + 1) (ofTerm p.1)).toArray by simp]
      repeat trioE0_step
      rw [spent_none Mf _ ‹_›]
      simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      repeat trioE0_step
      refine spec_bind_last (ih p.1 _ _ _ _ _ hgp) (fun _ _ => ?_)
      repeat trioE0_step
    · subst hr
      repeat trioE0_step
    · simp [Std.Legacy.Range.size]


/-! ### What `blockF` writes is the primitive-sequence embedding -/

open Googology.Trans.BMS (unread unread_nil unread_cons prSS mulUnits addUnits bodyU peelOne
  isFiniteT dropLastT WF3 WF3_omegaIndexMatrix)

theorem unread_shift : ∀ (X : Term) (b : Nat), unread b X = (unread 0 X).map (· + b) := by
  intro X
  induction X with
  | nil => intro b; rfl
  | cons a P Q _ ihP ihQ =>
    intro b
    simp only [unread_cons, List.map_cons, List.map_append, Nat.zero_add]
    rw [ihP (b + 1), ihP 1, ihQ b, List.map_map]
    congr 2
    apply List.map_congr_left
    intro e _
    simp only [Function.comp]
    omega

theorem unread_exps : ∀ (X : Term) (b : Nat),
    unread b X = (exps X).flatMap (fun Y => b :: unread (b + 1) Y) := by
  intro X
  induction X with
  | nil => intro b; rfl
  | cons a P Q _ _ ihQ =>
    intro b
    simp only [unread_cons, exps, List.flatMap_cons, List.cons_append, ihQ b]

theorem flatMap_range'_const {β : Type} (A : List β) :
    ∀ (k s : Nat), (List.range' s k).flatMap (fun _ => A) = (List.replicate k ()).flatMap (fun _ => A) := by
  intro k
  induction k with
  | zero => intro s; rfl
  | succ k ih =>
    intro s
    rw [List.range'_succ, List.replicate_succ, List.flatMap_cons, List.flatMap_cons, ih]

theorem grp_flatMap {β : Type} (F : Od → List β) : ∀ L : List (Term × Nat),
    (grp L).flatMap (fun ec => (List.range' 0 ec.2).flatMap (fun _ => F (ato ec.1))) =
      (expandG L).flatMap (fun b => F (ofTerm b)) := by
  intro L
  induction L with
  | nil => rfl
  | cons p L ih =>
    simp only [grp, List.map_cons] at ih ⊢
    rw [List.flatMap_cons, ih, flatMap_range'_const]
    simp only [expandG, List.flatMap_cons, List.flatMap_append]
    congr 1
    simp only [ato_ex]
    generalize p.2 = k
    induction k with
    | zero => rfl
    | succ k ihk => simp [List.replicate_succ, List.flatMap_cons, ihk]

/-- **`blockF` writes the one-row matrix of the exponent** at `x`, when the fuel
covers the depth. -/
theorem prO_ofTerm : ∀ (n : Nat) (g : Term) (x : Int), Good g → dep g ≤ n →
    prO n x (ofTerm g) = (unread 0 g).map (fun e : Nat => (⟨x + (e : Int), 0, false⟩ : TrioRules.Col)) := by
  intro n
  induction n with
  | zero =>
    intro g x _ hd
    rw [dep_eq_zero (Nat.le_zero.mp hd)]; rfl
  | succ n ih =>
    intro g x hg hd
    obtain ⟨L, hG, hO, hE⟩ := hg.inv
    show (ofTerm g).flatMap _ = _
    rw [hO, grp_flatMap (fun A => (⟨x, 0, false⟩ : TrioRules.Col) :: prO n (x + 1) A) L, hE,
      unread_exps g 0, List.map_flatMap]
    apply List.flatMap_congr
    intro b hb
    have hb' := mem_exps g b hb hg.1
    rw [ih b (x + 1) (hg.of_mem hb) (by omega), unread_shift b 1, List.map_cons, List.map_map]
    simp only [Nat.cast_zero, add_zero, Function.comp_def, Nat.cast_add, Nat.cast_one]
    congr 1
    apply List.map_congr_left
    intro e _
    congr 1
    omega

/-! ### The units and the pieces `placeUnits` reads -/

theorem units_grp (L : List (Term × Nat)) : units (grp L) = (expandG L).map ex := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    simp only [units, grp, List.map_cons, List.flatMap_cons, expandG, List.map_append,
      List.map_replicate] at ih ⊢
    rw [ih]

theorem units_ofTerm {x : Term} (hx : Good x) : units (ofTerm x) = (exps x).map ex := by
  obtain ⟨L, _, hO, hE⟩ := hx.inv
  rw [hO, units_grp, hE]

theorem ofTerm_eq_nil_iff {x : Term} (hx : Good x) : ofTerm x = [] ↔ x = nil := by
  obtain ⟨L, hG, hO, hE⟩ := hx.inv
  constructor
  · intro h
    rw [hO] at h
    have hL : L = [] := List.map_eq_nil_iff.mp h
    subst hL
    cases x with
    | nil => rfl
    | cons _ _ _ => simp [expandG, exps] at hE
  · rintro rfl; rfl

theorem isFiniteT_eq : ∀ x : Term, isFiniteT x = (exps x).all (· == nil) := by
  intro x
  induction x with
  | nil => rfl
  | cons a b t _ _ iht => simp [isFiniteT, exps, iht]

theorem exps_dropLastT : ∀ x : Term, exps (dropLastT x) = (exps x).dropLast := by
  intro x
  induction x with
  | nil => rfl
  | cons a b t _ _ iht =>
    by_cases ht : t = nil
    · subst ht; simp [dropLastT, exps]
    · have hne : exps t ≠ [] := by cases t with
        | nil => exact absurd rfl ht
        | cons _ _ _ => simp [exps]
      simp only [dropLastT, show (t == nil) = false from by simp [ht], Bool.false_eq_true,
        ↓reduceIte, exps, iht]
      rw [List.dropLast_cons_of_ne_nil hne]

theorem cmp_nil_ne_lt (x : Term) : Term.cmp x nil ≠ .lt := by
  cases x <;> simp [Term.cmp]

/-- `predBeta` as the program means it: `1 + β' = β`.  The program's own
`predBeta` tests `e == .o []` with the derived `==` on `Ex`, which Lean compiles
to an opaque function, so this cannot be proved about it; it is the hypothesis
of the main theorem (see the module docstring). -/
def PredBetaSpec : Prop :=
  ∀ (X : Od) (k : Nat) (r : Od), predBeta ((.o X, k) :: r) = if X.isEmpty then nat (k - 1) else (.o X, k) :: r

theorem units_nat (j : Nat) : units (nat j) = List.replicate j (.o []) := by
  unfold nat
  split
  · subst_vars; rfl
  · simp [units]

theorem predBeta_ofTerm (hpb : PredBetaSpec) {e : Term} (he : Good e) (hne : e ≠ nil) :
    units (predBeta (ofTerm e)) = (exps (peelOne e)).map ex ∧
      (∀ g ∈ exps (peelOne e), Good g) ∧
      (∀ q ∈ (predBeta (ofTerm e)).getLast?, ∃ g, Good g ∧ q.1 = ex g) := by
  obtain ⟨L, hG, hO, hE⟩ := he.inv
  cases L with
  | nil =>
    exfalso; apply hne
    cases e with
    | nil => rfl
    | cons _ _ _ => simp [expandG, exps] at hE
  | cons p L' =>
    obtain ⟨b0, k⟩ := p
    have hb0 : Good b0 := he.mem_grp hG hE List.mem_cons_self
    rw [hO]
    show units (predBeta ((.o (ofTerm b0), k) :: grp L')) = _ ∧ _ ∧
      ∀ q ∈ (predBeta ((.o (ofTerm b0), k) :: grp L')).getLast?, _
    rw [hpb]
    by_cases hb : b0 = nil
    · subst hb
      have hL' : L' = [] := by
        cases L' with
        | nil => rfl
        | cons q r => exact absurd hG.2.1 (cmp_nil_ne_lt _)
      subst hL'
      have hex : exps e = List.replicate k nil := by
        rw [← hE]; simp [expandG]
      have hfin : isFiniteT e = true := by
        rw [isFiniteT_eq, hex]; simp
      have hpe : exps (peelOne e) = List.replicate (k - 1) nil := by
        rw [peelOne, hfin, if_pos rfl, exps_dropLastT, hex]
        simp
      simp only [ofTerm_nil, List.isEmpty_nil, ↓reduceIte, hpe]
      refine ⟨by rw [units_nat, List.map_replicate]; rfl, ?_, ?_⟩
      · intro g hg
        rw [(List.mem_replicate.mp hg).2]
        exact ⟨⟨trivial, trivial⟩, by simp [dep]⟩
      · intro q hq
        refine ⟨nil, ⟨⟨trivial, trivial⟩, by simp [dep]⟩, ?_⟩
        unfold nat at hq
        split at hq
        · simp at hq
        · simp at hq; rw [← hq]; rfl
    · have hne' : (ofTerm b0).isEmpty = false := by
        cases h : ofTerm b0 with
        | nil => exact absurd ((ofTerm_eq_nil_iff hb0).mp h) hb
        | cons _ _ => rfl
      have hfin : isFiniteT e = false := by
        have hk := GDesc_head_pos hG
        obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
        rw [isFiniteT_eq, ← hE, hk']
        simp [expandG, List.replicate_succ, hb]
      have hpe : peelOne e = e := by rw [peelOne, hfin]; rfl
      simp only [hne', Bool.false_eq_true, ↓reduceIte, hpe]
      have h1 : ((Ex.o (ofTerm b0), k) :: grp L') = grp ((b0, k) :: L') := rfl
      rw [h1, units_grp, hE]
      refine ⟨rfl, fun g hg => he.of_mem hg, ?_⟩
      intro q hq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_of_getLast? hq)
      exact ⟨p.1, he.mem_grp hG hE hp, rfl⟩

theorem tailBlockF_ofTerm : ∀ (n : Nat) (g : Term) (arg : Bool), Good g →
    tailBlockF n (ofTerm g) arg = none := by
  intro n
  induction n with
  | zero => intro _ _ _; rfl
  | succ n ih =>
    intro g arg hg
    obtain ⟨L, hG, hO, hE⟩ := hg.inv
    unfold tailBlockF
    split
    · rfl
    · rename_i e c hlast
      rw [hO] at hlast
      obtain ⟨p, hp, hpe⟩ := List.mem_map.mp (List.mem_of_getLast? hlast)
      have hgp := hg.mem_grp hG hE hp
      simp only [Prod.mk.injEq] at hpe
      rw [← hpe.1, strip_ex hgp]
      dsimp only
      by_cases hr : (ofTerm p.1).isEmpty = true
      · simp only [hr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        split
        · rfl
        · exact lvl_ex hgp
      · simp only [hr, Bool.not_false, ↓reduceIte]
        exact ih _ _ hgp

theorem tailLevel_ofTerm (hpb : PredBetaSpec) {α : Term} (hα : Good α) :
    tailLevel (ofTerm α) = none := by
  unfold tailLevel
  rw [units_ofTerm hα]
  split
  · rfl
  · rename_i b hb
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_of_getLast? hb)
    have hge := hα.of_mem he
    unfold unitTailLevel
    rw [ato_ex]
    by_cases hn : e = nil
    · subst hn; rfl
    · have hne : (ofTerm e).isEmpty = false := by
        cases h : ofTerm e with
        | nil => exact absurd ((ofTerm_eq_nil_iff hge).mp h) hn
        | cons _ _ => rfl
      obtain ⟨_, _, hlast⟩ := predBeta_ofTerm hpb hge hn
      simp only [hne, Bool.false_or]
      split
      · rfl
      · split
        · rename_i e' c' hl
          obtain ⟨g, hg, hq⟩ := hlast _ hl
          simp only at hq
          rw [hq, ato_ex]
          exact tailBlockF_ofTerm _ g false hg
        · rfl


/-! ### The add units -/

/-- A column of `Trio.lean` as a column of the builder. -/
def toCol (l : List Nat) : TrioRules.Col := ⟨(l.getD 0 0 : Int), (l.getD 1 0 : Int), l.getD 2 0 == 1⟩

def colsOf (m : List (List Nat)) : List TrioRules.Col := m.map toCol

theorem toRows_colsOf (m : List (List Nat)) (h : WF3 m) : toRows (colsOf m).toArray = m := by
  simp only [toRows, colsOf, List.map_map]
  conv => rhs; rw [← List.map_id m]
  apply List.map_congr_left
  intro c hc
  obtain ⟨hlen, hz⟩ := h c hc
  match c, hlen, hz with
  | [a, b, z], _, hz =>
    simp only [Function.comp, toCol, List.getD_cons_zero, List.getD_cons_succ, Int.toNat_natCast, id]
    simp at hz
    interval_cases z <;> rfl

def nrp (e : Term) (rp1 : Nat) : Nat := if e = nil then rp1 else rp1 + 2

def nlx (e : Term) (rp1 lastX : Nat) (pz : Bool) : Nat :=
  if e = nil then (if pz then lastX + 1 else rp1 + 1) else rp1 + 1

theorem addUnits_split (rp1 lastX : Nat) (pz : Bool) (i : Nat) (a e t : Term) :
    addUnits rp1 lastX pz i (cons a e t) =
      addUnits rp1 lastX pz i (cons a e nil) ++
        addUnits (nrp e rp1) (nlx e rp1 lastX pz) (e == nil) (i + 1) t := by
  by_cases he : e = nil
  · subst he
    cases pz <;> simp [addUnits, nrp, nlx]
  · have : (e == nil) = false := by simp [he]
    simp [addUnits, nrp, nlx, he, this]

abbrev Tup := MProd Bool (MProd Int (MProd Bool Int))

theorem run_bind' {α β : Type} (x : StateM Ctx α) (f : α → StateM Ctx β) (s : Ctx) :
    (x >>= f).run s = (f (x.run s).1).run (x.run s).2 := rfl

theorem loop_units (f : Ex → Tup → StateM Ctx (ForInStep Tup))
    (hf : ∀ e, Good e → dep e ≤ 200 → ∀ (first : Bool) (rp1 lastX : Nat) (pz : Bool) (i : Nat) (s : Ctx),
      1 ≤ i → s.regime = none → (pz = true → lastC s.cols = ⟨lastX, (i : Int) - 1, false⟩) →
      ∃ s', (f (ex e) ⟨first, (i : Int) - 1, pz, (rp1 : Int) - 1⟩).run s =
          (.yield ⟨false, ((i + 1 : Nat) : Int) - 1, e == nil, ((nrp e rp1 : Nat) : Int) - 1⟩, s') ∧
        s'.cols = s.cols ++ (colsOf (addUnits rp1 lastX pz i (cons nil e nil))).toArray ∧
        s'.regime = none ∧
        (e = nil → lastC s'.cols = ⟨nlx e rp1 lastX pz, ((i + 1 : Nat) : Int) - 1, false⟩)) :
    ∀ t : Term, Good t → ∀ (first : Bool) (rp1 lastX : Nat) (pz : Bool) (i : Nat) (s : Ctx),
      1 ≤ i → s.regime = none → (pz = true → lastC s.cols = ⟨lastX, (i : Int) - 1, false⟩) →
      ∃ r s', (forIn ((exps t).map ex) (⟨first, (i : Int) - 1, pz, (rp1 : Int) - 1⟩ : Tup) f).run s
          = (r, s') ∧
        s'.cols = s.cols ++ (colsOf (addUnits rp1 lastX pz i t)).toArray ∧ s'.regime = none := by
  intro t
  induction t with
  | nil =>
    intro _ first rp1 lastX pz i s _ hs _
    exact ⟨_, s, rfl, by simp [addUnits, colsOf], hs⟩
  | cons a e t _ _ iht =>
    intro hg first rp1 lastX pz i s hi hs hl
    have ha : a = nil := hg.1.1.1
    subst ha
    have hge : Good e := hg.of_mem (List.mem_cons_self)
    have hgt : Good t := ⟨H_tail hg.1, by have := hg.2; simp only [dep] at this; omega⟩
    have hde : dep e ≤ 200 := by have := hg.2; simp only [dep] at this; omega
    obtain ⟨s1, h1, hc1, hr1, hl1⟩ := hf e hge hde first rp1 lastX pz i s hi hs hl
    obtain ⟨r, s2, h2, hc2, hr2⟩ := iht hgt false (nrp e rp1) (nlx e rp1 lastX pz) (e == nil) (i + 1)
      s1 (by omega) hr1 (fun h => hl1 (by simpa using h))
    refine ⟨r, s2, ?_, ?_, hr2⟩
    · simp only [exps, List.map_cons, List.forIn_cons]
      rw [run_bind', h1]
      push_cast at h2 ⊢
      exact h2
    · rw [hc2, hc1, addUnits_split rp1 lastX pz i nil e t]
      simp [colsOf, Array.append_assoc]


theorem run_modify_bind {β : Type} (g : Ctx → Ctx) (f : PUnit → StateM Ctx β) (s : Ctx) :
    (modify g >>= f).run s = (f ⟨⟩).run (g s) := rfl

theorem run_get_bind {β : Type} (f : Ctx → StateM Ctx β) (s : Ctx) :
    (get >>= f).run s = (f s).run s := rfl

theorem run_pure_bind {α β : Type} (a : α) (f : α → StateM Ctx β) (s : Ctx) :
    (pure a >>= f).run s = (f a).run s := rfl

theorem run_pure' {α : Type} (a : α) (s : Ctx) : (pure a : StateM Ctx α).run s = (a, s) := rfl

theorem lastC_push (cs : Cols) (a : TrioRules.Col) : lastC (cs.push a) = a := by
  unfold lastC colAt
  simp [Array.getD_eq_getD_getElem?]

theorem lastC_append_two (cs : Cols) (a b : TrioRules.Col) : lastC (cs ++ #[a, b]) = b := by
  have : cs ++ #[a, b] = (cs.push a).push b := by
    rw [Array.push_eq_append, Array.push_eq_append, Array.append_assoc]; rfl
  rw [this, lastC_push]

theorem hf_of_spec {p : StateM Ctx (ForInStep Tup)} {a : ForInStep Tup} {W : Array TrioRules.Col}
    {s : Ctx} {P : Ctx → Prop} (h : Spec p (· = a) W) (hs : s.regime = none) (hP : ∀ s', P s') :
    ∃ s', p.run s = (a, s') ∧ s'.cols = s.cols ++ W ∧ s'.regime = none ∧ P s' := by
  obtain ⟨b, s', h1, rfl, h3, h4⟩ := h s hs
  exact ⟨s', h1, h3, h4, hP s'⟩

theorem mulUnits_exps (x0 y : Nat) : ∀ t : Term,
    mulUnits x0 y t = (exps t).flatMap (fun g => [x0 + 1, y, 1] :: prSS (x0 + 2) g) := by
  intro t
  induction t with
  | nil => rfl
  | cons a g u _ _ ihu => simp [mulUnits, exps, ihu]

theorem colsOf_prSS (x : Nat) (g : Term) (hg : Good g) (hd : dep g ≤ fuel) :
    colsOf (prSS x g) = prO fuel (x : Int) (ofTerm g) := by
  rw [prO_ofTerm fuel g x hg hd, colsOf, prSS, List.map_map]
  apply List.map_congr_left
  intro e _
  simp [toCol]

theorem run_loop (α : Term) (hα : Good α) (f : Ex → Tup → StateM Ctx (ForInStep Tup))
    (hf : ∀ e, Good e → dep e ≤ 200 → ∀ (first : Bool) (rp1 lastX : Nat) (pz : Bool) (i : Nat) (s : Ctx),
      1 ≤ i → s.regime = none → (pz = true → lastC s.cols = ⟨lastX, (i : Int) - 1, false⟩) →
      ∃ s', (f (ex e) ⟨first, (i : Int) - 1, pz, (rp1 : Int) - 1⟩).run s =
          (.yield ⟨false, ((i + 1 : Nat) : Int) - 1, e == nil, ((nrp e rp1 : Nat) : Int) - 1⟩, s') ∧
        s'.cols = s.cols ++ (colsOf (addUnits rp1 lastX pz i (cons nil e nil))).toArray ∧
        s'.regime = none ∧
        (e = nil → lastC s'.cols = ⟨nlx e rp1 lastX pz, ((i + 1 : Nat) : Int) - 1, false⟩))
    (S : Ctx) (hS : S.regime = none) (hS0 : S.cols = #[]) :
    (StateT.run (pure PUnit.unit >>= fun _ =>
        forIn ((exps α).map ex) (⟨true, 0, false, -1⟩ : Tup) f >>= fun _ => pure PUnit.unit) S).2.cols =
      (colsOf (addUnits 0 0 false 1 α)).toArray := by
  obtain ⟨r, s', hrun, hc, -⟩ := loop_units f hf α hα true 0 0 false 1 S le_rfl hS (by simp)
  have e1 : (⟨true, 0, false, -1⟩ : Tup) = ⟨true, ((1 : Nat) : Int) - 1, false, ((0 : Nat) : Int) - 1⟩ := rfl
  have key : (StateT.run (pure PUnit.unit >>= fun _ =>
        forIn ((exps α).map ex) (⟨true, 0, false, -1⟩ : Tup) f >>= fun _ => pure PUnit.unit) S) =
      (PUnit.unit, s') := by
    rw [run_bind']
    show (forIn ((exps α).map ex) (⟨true, 0, false, -1⟩ : Tup) f >>= fun _ => pure PUnit.unit).run S = _
    rw [run_bind', e1, hrun]
    rfl
  rw [key]
  show s'.cols = _
  rw [hc, hS0]; simp

theorem placeUnits_ofTerm (hpb : PredBetaSpec) (Mf : Od → Cols) (α : Term) (hα : Good α) :
    (placeUnits Mf #[] (ofTerm α) 0 (-1) none).cols = (colsOf (addUnits 0 0 false 1 α)).toArray := by
  unfold placeUnits
  simp only [Option.bind_none, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, List.drop_zero,
    units_ofTerm hα]
  refine run_loop α hα _ ?_ _ rfl rfl
  intro e he hde first rp1 lastX pz i s hi hs hl
  have hsp : ∀ c : Ctx, c.regime = s.regime → spent Mf c = false := fun c hc =>
    spent_none Mf c (hc.trans hs)
  by_cases he0 : e = nil
  · subst he0
    cases pz
    · simp (disch := exact rfl) only [run_modify_bind, run_get_bind, run_pure_bind, ato_ex, ofTerm_nil,
        List.isEmpty_nil, hsp, Bool.and_false, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
      rw [run_pure']
      refine ⟨_, Prod.ext ?_ rfl, ?_, hs, ?_⟩
      · simp only [nrp, beq_self_eq_true, ↓reduceIte, ForInStep.yield.injEq, MProd.mk.injEq, true_and, and_true]
        omega
      · simp [addUnits, colsOf, toCol]
        push_cast [Nat.cast_sub hi]
        ring_nf
      · intro _
        rw [lastC_append_two]
        simp [nlx]
        ring
    · have hl' := hl rfl
      simp (disch := exact rfl) only [run_modify_bind, run_get_bind, run_pure_bind, ato_ex, ofTerm_nil,
        List.isEmpty_nil, hsp, Bool.and_false, Bool.false_eq_true, ↓reduceIte, Bool.not_true,
        Bool.and_self, hl']
      split
      · next p r h1 h2 => simp at h2
      simp only [run_pure_bind, run_pure']
      refine ⟨_, Prod.ext ?_ rfl, ?_, hs, ?_⟩
      · simp only [nrp, beq_self_eq_true, ↓reduceIte, ForInStep.yield.injEq, MProd.mk.injEq, true_and,
          and_true]
        omega
      · simp [addUnits, colsOf, toCol]
      · intro _
        rw [lastC_push]
        simp [nlx]
  · have hE : (ofTerm e).isEmpty = false := by
      cases h : ofTerm e with
      | nil => exact absurd ((ofTerm_eq_nil_iff he).mp h) he0
      | cons _ _ => rfl
    obtain ⟨hunits, hgood, -⟩ := predBeta_ofTerm hpb he he0
    have hsub : ∀ g ∈ exps (peelOne e), g ∈ exps e := by
      intro g hg
      unfold peelOne at hg
      split at hg
      · rw [exps_dropLastT] at hg; exact List.mem_of_mem_dropLast hg
      · exact hg
    have hdep : ∀ g ∈ exps (peelOne e), dep g ≤ fuel := by
      intro g hg
      have := (mem_exps e g (hsub g hg) he.1).2
      simp only [fuel]; omega
    let w : Ex → List TrioRules.Col := fun a =>
      ⟨(rp1 : Int) - 1 + 1 + 1 + 1, (i : Int) - 1 + 1, true⟩ ::
        prO fuel ((rp1 : Int) - 1 + 1 + 1 + 2) (ato a)
    have hW : (colsOf (addUnits rp1 lastX pz i (cons nil e nil))).toArray =
        #[⟨(rp1 : Int) - 1 + 1, (i : Int) - 1, false⟩, ⟨(rp1 : Int) - 1 + 1 + 1, (i : Int) - 1 + 1, true⟩] ++
          (((exps (peelOne e)).map ex).flatMap w).toArray := by
      have hb : (e == nil) = false := by simp [he0]
      simp only [addUnits, hb, Bool.false_eq_true, ↓reduceIte, bodyU, mulUnits_exps, List.append_nil]
      simp only [colsOf, List.map_cons, List.map_flatMap, List.flatMap_map]
      have hfl : (exps (peelOne e)).flatMap
            (fun a => toCol [rp1 + 1 + 1, i, 1] :: List.map toCol (prSS (rp1 + 1 + 2) a)) =
          (exps (peelOne e)).flatMap (fun a => w (ex a)) := by
        apply List.flatMap_congr
        intro g hg
        rw [show List.map toCol (prSS (rp1 + 1 + 2) g) = colsOf (prSS (rp1 + 1 + 2) g) from rfl,
          colsOf_prSS _ g (hgood g hg) (hdep g hg)]
        simp only [w, ato_ex, toCol, List.getD_cons_zero, List.getD_cons_succ, beq_self_eq_true]
        congr 2
        · push_cast; ring
        · ring
        · push_cast; ring
      rw [hfl]
      apply Array.ext'
      simp [toCol]
      omega
    refine hf_of_spec ?_ hs (fun _ h => absurd h he0)
    rw [hW]
    trioE0_step
    refine spec_get_bind fun s1 hs1 => ?_
    simp only [spent_none Mf s1 hs1, Bool.and_false, Bool.false_eq_true, ↓reduceIte, ato_ex, hE,
      Bool.false_and]
    repeat trioE0_step
    rw [hunits]
    refine spec_bind_last (spec_forIn _ _
      (fun r : MProd Nat (MProd Int Int) => r.snd = ⟨(rp1 : Int) - 1 + 1 + 1, (i : Int) - 1 + 1⟩) w
      ?_ _ rfl) (fun r hr => ?_)
    · intro a ha b hb
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp ha
      obtain ⟨j, x0', y'⟩ := b
      simp only [MProd.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      refine spec_get_bind fun s2 _ => spec_get_bind fun s3 hs3 => ?_
      simp only [spent_none Mf s3 hs3, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      show Spec _ _ (List.toArray (_ :: _))
      rw [List.toArray_cons]
      repeat trioE0_step
      refine spec_bind_last (blockF_spec Mf fuel g _ _ _ _ _ (hgood g hg)) (fun _ _ => ?_)
      repeat trioE0_step
    · obtain ⟨j, x0', y'⟩ := r
      simp only [MProd.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      simp only [Bool.not_false, ↓reduceIte]
      repeat trioE0_step
      split
      · next p r h1 h2 => simp at h2
      repeat trioE0_step
      refine spec_pure ?_
      have hb : (e == nil) = false := by simp [he0]
      simp only [nrp, he0, ↓reduceIte, hb, ForInStep.yield.injEq, MProd.mk.injEq, true_and]
      omega


/-! ### The theorem -/

theorem M_ofTerm (hpb : PredBetaSpec) (α : Term) (hα : Good α) :
    M (ofTerm α) = (colsOf (omegaIndexMatrix α)).toArray := by
  unfold M
  rw [show fuel = 199 + 1 from rfl, Mfuel]
  unfold Mstep
  have hl : lvlO (ofTerm α) = none := lvl_ex hα
  rw [hl]
  dsimp only
  unfold finish
  rw [tailLevel_ofTerm hpb hα]
  dsimp only
  exact placeUnits_ofTerm hpb _ α hα

/-- **Rules 1–10 agree with `Trio.lean` below `ε₀`**, on every term whose
subscripts are all `0`, whose principal terms descend, and whose nesting depth is
at most `201` — given that `predBeta` does what it says (`PredBetaSpec`). -/
theorem trioMatrixL_eq_of_good (hpb : PredBetaSpec) (α : Term) (hA : AllNil α) (hD : DescAll α)
    (hd : dep α ≤ 201) : trioMatrixL α = trioMatrix α := by
  rw [Googology.Trans.BMS.TrioStd.trioMatrix_allNil α hA]
  unfold trioMatrixL trioRuleMatrix
  rw [M_ofTerm hpb α ⟨⟨hA, hD⟩, hd⟩]
  exact toRows_colsOf _ (WF3_omegaIndexMatrix α)

/-- **The same for every standard form below `ε₀` of depth at most `201`.** -/
theorem trioMatrixL_eq_trioMatrix (hpb : PredBetaSpec) (α : Googology.Trans.BMS.exbE0.State)
    (hd : dep α.1 ≤ 201) : trioMatrixL α.1 = trioMatrix α.1 :=
  trioMatrixL_eq_of_good hpb α.1 (Googology.Trans.BMS.allNil_of_state α)
    (Googology.Trans.BMS.descAll_of_OT α.1 α.2.1 (Googology.Trans.BMS.allNil_of_state α)) hd

end Googology.Trans.BMS.TrioRulesE0


/-! ### Calibration: the hypothesis, and where the fuel runs out

These are `#guard`s — checks of the compiled program, not theorems. -/

namespace Googology.Trans.BMS.TrioRulesE0

open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term
open Googology.Trans.BMS.TrioRules
open Googology.Trans.BMS (trioMatrix)

-- `PredBetaSpec` on the compiled `predBeta`: `β = 3` gives `β' = 2`, `β = ω` gives `β' = ω`.
#guard predBeta [(.o [], 3)] == nat 2
#guard predBeta [(.o [], 1)] == nat 0
#guard predBeta [(.o [(.o [], 1)], 1)] == [(.o [(.o [], 1)], 1)]

/-- The tower `ω^ω^…^1` with `k` exponentiations: `towerT 0 = 1`. -/
def towerT : Nat → Term
  | 0 => psi nil nil
  | k + 1 => psi nil (towerT k)

theorem dep_towerT (k : Nat) : dep (towerT k) = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [towerT, dep, ih]

-- Depth `202` still agrees; depth `203` does not: fuel `200` is not enough for all `α < ε₀`.
#guard trioMatrixL (towerT 201) = trioMatrix (towerT 201)
#guard trioMatrixL (towerT 202) ≠ trioMatrix (towerT 202)
#guard (trioMatrixL (towerT 202)).length = 203 ∧ (trioMatrix (towerT 202)).length = 204

/-- `predBeta` does what it says: it is written with a pattern match on the
exponent, so the specification holds by cases. -/
theorem predBetaSpec : PredBetaSpec := by
  intro X k r
  cases X <;> rfl

/-- **The transcription of rules 1–10 agrees with `trioMatrix` below `ε₀`**,
for every standard term of depth at most `201` (the fuel `200` of
`trioMatrixL`). -/
theorem trioMatrixL_eq_trioMatrix' (α : Googology.Trans.BMS.exbE0.State)
    (hd : dep α.1 ≤ 201) : trioMatrixL α.1 = trioMatrix α.1 :=
  trioMatrixL_eq_trioMatrix predBetaSpec α hd

end Googology.Trans.BMS.TrioRulesE0

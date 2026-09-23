import Googology.Trans.BMS.TrioTreeStd
import Googology.Trans.BMS.TrioRulesE0

/-!
# Rules 1–10 compute `trioE` below `ψ_0(Ω_2)`

`TrioRules.trioMatrixL` is the transcription of rules 1–10 of
[koteitan/trio](https://github.com/koteitan/trio), a program with a fuel of
`200`.  `TrioTree.lean` writes what it does on the countable standard forms
whose subscripts are `0` or `1` as the structural recursion `trioE`, and proves
that `trioE` keeps the order; `TrioTreeStd.lean` proves that its image is in the
standard forms.  This file proves that the program computes `trioE` there:

  `trioMatrixL_eq_trioE`: for standard `α < Ω` with every subscript `0` or `1`
  and nesting depth `dep α ≤ 200`, `trioMatrixL α = trioE α`.

So for those `α`, **the image of `trioMatrixL` is in the standard forms of
three-row BMS** (`trioMatrixL_std`) and **`trioMatrixL` preserves and reflects
the order** (`trioMatrixL_lt_iff`, `trioMatrixL_injective`).

## The depth bound is needed, and it is tight

`dep` is `TrioRulesE0.dep` (`dep 0 = 0`, `dep (ψ_a(b) + t) = max (dep b + 1) (dep t)`).
On the families `ψ_0(Ω + T)` and `ψ_0(ψ_1(T))`, `T` a tower of `ψ_0`s, the
program agrees with `trioE` at depth `200` and disagrees at depth `201`
(`#guard`s at the end), and it gives the two different standard terms
`ψ_0(Ω + T_205)` and `ψ_0(Ω + T_206)` (depths `206` and `207`) the same matrix
(`TrioTree.lean`).  So no statement about `trioMatrixL` on all
of `ε₀ ≤ α < ε₁` holds as it stands.

## How the proof goes

It is `TrioRulesE0.lean`'s proof, widened from the terms without `Ω` to the
fragment.

* **Terms.**  `ofTerm` writes a summand `ψ_a(b)` as the exponent `exS a b`: a
  normal form `ω^{ofTerm b}` when `b` has no `Ω`, and otherwise one of three
  atoms, `ψ_0(b)`, `Ω = ψ_1(0)` or `ψ_1(b)`.  With enough fuel the program's
  comparison of these is the order of the summands (`expCmp`): a normal form
  without `Ω` is below every atom (`oa`), the atoms compare by level, then kind,
  then argument.  So `ofTerm` groups the summands (`inv2_all`).
* **Trees.**  On a collapse argument the program writes `Ω_1` through
  `writeLevel`, which gives the one column `(x, 1, 0)` at depth `0` or `1`
  whatever the ladders (`writeLevel_one`, from `M(1) = (0,0,0)(1,1,0)` at fuel
  `199`, `Mfuel_one`).  So `blockF` writes the tree of the term (`blockF_specT`,
  `treeO_ofTerm`).
* **Units.**  An add unit whose exponent is an atom `ψ_0(b)` is the root, one
  digit and the tree of `ψ_0(b)` (`placeUnits_ofTermE`); the others are
  `TrioRulesE0.lean`'s.  `tailLevel` is `none` (`tailLevel_ofTermE`), so no mark
  is appended.
-/

namespace Googology.Trans.BMS.TrioTreeRules

open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term
open Googology.Trans.BMS.TrioRules
open Googology.Trans.BMS.TrioRulesE0
open Googology.Trans.BMS.TrioTree
open Googology.Trans.BMS (AllNil DescAll)

/-! ### The exponents `ofTerm` writes -/

theorem allNil_of_omegaFree : ∀ x : Term, omegaFree x = true → AllNil x
  | nil, _ => trivial
  | cons a b t, h => by
    simp only [omegaFree, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨h.1.1, allNil_of_omegaFree b h.1.2, allNil_of_omegaFree t h.2⟩

theorem omegaFree_iff (x : Term) : omegaFree x = true ↔ AllNil x :=
  ⟨allNil_of_omegaFree x, omegaFree_of_allNil x⟩

/-- The exponent `ofTerm` writes for a summand `ψ_a(b)`, `a` being `0` or `1`. -/
def exS (a b : Term) : Ex :=
  if a = nil then (if omegaFree b then .o (ofTerm b) else .psi [] (ofTerm b))
  else (if b = nil then .W one else .psi one (ofTerm b))

theorem add_nil' (a : Od) : add a [] = a := by simp [add]

theorem ofTerm_t1 : ofTerm t1 = one := by
  simp [ofTerm, one, nat, add]

theorem ofTerm_cons2 {a b t : Term} (ha : a = nil ∨ a = t1) :
    ofTerm (cons a b t) = add [(exS a b, 1)] (ofTerm t) := by
  rcases ha with rfl | rfl
  · by_cases hb : b = nil
    · subst hb; simp [ofTerm, exS, one, nat, omegaFree]
    · by_cases hf : omegaFree b = true
      · simp [ofTerm, exS, hb, hf, wpow]
      · simp [ofTerm, exS, hb, hf]
  · by_cases hb : b = nil
    · subst hb; simp [ofTerm, exS, add_nil']
    · simp [ofTerm, exS, hb, add_nil']

/-- The summands, as pairs `(subscript, argument)`. -/
def sums : Term → List (Term × Term)
  | nil => []
  | cons a b t => (a, b) :: sums t

/-- The order of two principal terms. -/
def pcmp (p q : Term × Term) : Ordering := Term.cmp (psi p.1 p.2) (psi q.1 q.2)

/-- The dictionary order on lists of summands. -/
def lexS : List (Term × Term) → List (Term × Term) → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys => (pcmp x y).then (lexS xs ys)

theorem pcmp_def (a b c d : Term) : pcmp (a, b) (c, d) = (Term.cmp a c).then (Term.cmp b d) := by
  simp only [pcmp, Term.cmp]
  cases Term.cmp a c <;> cases Term.cmp b d <;> rfl

theorem cmp_sums : ∀ x y : Term, Term.cmp x y = lexS (sums x) (sums y)
  | nil, nil => rfl
  | nil, cons _ _ _ => rfl
  | cons _ _ _, nil => rfl
  | cons a b t, cons c d u => by
    simp only [Term.cmp, sums, lexS, pcmp_def, cmp_sums t u]
    cases Term.cmp a c <;> cases Term.cmp b d <;> rfl

def expandG2 (L : List ((Term × Term) × Nat)) : List (Term × Term) :=
  L.flatMap (fun p => List.replicate p.2 p.1)

/-- Groups strictly decreasing, with positive multiplicities. -/
def GDesc2 : List ((Term × Term) × Nat) → Prop
  | [] => True
  | [p] => 0 < p.2
  | p :: q :: r => 0 < p.2 ∧ pcmp q.1 p.1 = .lt ∧ GDesc2 (q :: r)

def grp2 (L : List ((Term × Term) × Nat)) : Od := L.map (fun p => (exS p.1.1 p.1.2, p.2))

/-- **`ofTerm` groups the summands.** -/
def Inv2 (x : Term) : Prop := ∃ L, GDesc2 L ∧ ofTerm x = grp2 L ∧ expandG2 L = sums x

theorem GDesc2_tail {p : (Term × Term) × Nat} {L : List ((Term × Term) × Nat)}
    (h : GDesc2 (p :: L)) : GDesc2 L := by
  cases L with
  | nil => trivial
  | cons q r => exact h.2.2

theorem GDesc2_pos : ∀ {L : List ((Term × Term) × Nat)}, GDesc2 L → ∀ p ∈ L, 0 < p.2 := by
  intro L
  induction L with
  | nil => intro _ p hp; cases hp
  | cons q r ih =>
    intro h p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · cases r with
      | nil => simpa [GDesc2] using h
      | cons _ _ => exact h.1
    · exact ih (GDesc2_tail h) p hp

theorem GDesc2_head_pos {p : (Term × Term) × Nat} {L : List ((Term × Term) × Nat)}
    (h : GDesc2 (p :: L)) : 0 < p.2 :=
  GDesc2_pos h p List.mem_cons_self

theorem GDesc2_next {p : (Term × Term) × Nat} {L : List ((Term × Term) × Nat)}
    (h : GDesc2 (p :: L)) : ∀ e ∈ (expandG2 L).head?, pcmp e p.1 = .lt := by
  intro e he
  cases L with
  | nil => simp [expandG2] at he
  | cons q r =>
    have hq : 0 < q.2 := GDesc2_head_pos h.2.2
    obtain ⟨k, hk⟩ : ∃ k, q.2 = k + 1 := ⟨q.2 - 1, by omega⟩
    simp [expandG2, List.flatMap_cons, hk, List.replicate_succ] at he
    subst he
    exact h.2.1

theorem mem_expandG2 {L : List ((Term × Term) × Nat)} (h : GDesc2 L)
    {p : (Term × Term) × Nat} (hp : p ∈ L) : p.1 ∈ expandG2 L := by
  have := GDesc2_pos h p hp
  simp only [expandG2, List.mem_flatMap]
  exact ⟨p, hp, List.mem_replicate.mpr ⟨by omega, rfl⟩⟩

theorem pcmp_self (p : Term × Term) : pcmp p p = .eq := cmp_self _

theorem pcmp_swap (p q : Term × Term) : (pcmp p q).swap = pcmp q p := cmp_swap _ _

theorem lexS_rep (e : Term × Term) (E1 E2 : List (Term × Term))
    (h1 : ∀ x ∈ E1.head?, pcmp x e = .lt) (h2 : ∀ x ∈ E2.head?, pcmp x e = .lt) :
    ∀ k1 k2 : Nat, lexS (List.replicate k1 e ++ E1) (List.replicate k2 e ++ E2) =
      (compare k1 k2).then (lexS E1 E2) := by
  intro k1
  induction k1 with
  | zero =>
    intro k2
    cases k2 with
    | zero => simp [compare, compareOfLessAndEq, Ordering.then]
    | succ m =>
      simp only [List.replicate_zero, List.nil_append, List.replicate_succ, List.cons_append]
      cases E1 with
      | nil => simp [lexS, compare, compareOfLessAndEq, Ordering.then]
      | cons x xs =>
        have := h1 x (by simp)
        simp [lexS, this, compare, compareOfLessAndEq, Ordering.then]
  | succ m ih =>
    intro k2
    cases k2 with
    | zero =>
      simp only [List.replicate_zero, List.nil_append, List.replicate_succ, List.cons_append]
      cases E2 with
      | nil => simp [lexS, compare, compareOfLessAndEq, Ordering.then]
      | cons x xs =>
        have h := h2 x (by simp)
        have hs := pcmp_swap x e
        rw [h] at hs
        simp [lexS, ← hs, compare, compareOfLessAndEq, Ordering.then, Ordering.swap]
    | succ m' =>
      simp only [List.replicate_succ, List.cons_append, lexS, pcmp_self, compare_succ_succ]
      rw [← ih m']
      rfl

theorem lexS_grp2 (c : Od → Od → Ordering) :
    ∀ L1 L2 : List ((Term × Term) × Nat), GDesc2 L1 → GDesc2 L2 →
      (∀ p ∈ L1, ∀ q ∈ L2, cmpExpWith c (exS p.1.1 p.1.2) (exS q.1.1 q.1.2) = pcmp p.1 q.1) →
      cmpOrdWith c (grp2 L1) (grp2 L2) = lexS (expandG2 L1) (expandG2 L2) := by
  intro L1
  induction L1 with
  | nil =>
    intro L2 _ h2 _
    cases L2 with
    | nil => simp [grp2, expandG2, cmpOrdWith_nil_nil, lexS]
    | cons q r =>
      have hq := GDesc2_head_pos h2
      obtain ⟨k, hk⟩ : ∃ k, q.2 = k + 1 := ⟨q.2 - 1, by omega⟩
      simp [grp2, expandG2, cmpOrdWith_nil_cons, hk, List.replicate_succ, lexS]
  | cons p r ih =>
    intro L2 h1 h2 hc
    cases L2 with
    | nil =>
      have hp := GDesc2_head_pos h1
      obtain ⟨k, hk⟩ : ∃ k, p.2 = k + 1 := ⟨p.2 - 1, by omega⟩
      simp [grp2, expandG2, cmpOrdWith_cons_nil, hk, List.replicate_succ, lexS]
    | cons q s =>
      have ihr := ih s (GDesc2_tail h1) (GDesc2_tail h2)
        (fun p' hp' q' hq' => hc p' (List.mem_cons_of_mem _ hp') q' (List.mem_cons_of_mem _ hq'))
      have hpq := hc p List.mem_cons_self q List.mem_cons_self
      have e1 : grp2 (p :: r) = (exS p.1.1 p.1.2, p.2) :: grp2 r := rfl
      have e2 : grp2 (q :: s) = (exS q.1.1 q.1.2, q.2) :: grp2 s := rfl
      have f1 : expandG2 (p :: r) = List.replicate p.2 p.1 ++ expandG2 r := by
        simp [expandG2]
      have f2 : expandG2 (q :: s) = List.replicate q.2 q.1 ++ expandG2 s := by
        simp [expandG2]
      rw [e1, e2, cmpOrdWith_cons, hpq, ihr, f1, f2]
      have hp := GDesc2_head_pos h1
      have hq := GDesc2_head_pos h2
      obtain ⟨k, hk⟩ : ∃ k, p.2 = k + 1 := ⟨p.2 - 1, by omega⟩
      obtain ⟨k', hk'⟩ : ∃ k, q.2 = k + 1 := ⟨q.2 - 1, by omega⟩
      cases hcm : pcmp p.1 q.1 with
      | lt =>
        simp [hk, hk', List.replicate_succ, lexS, hcm, Ordering.then]
      | gt =>
        simp [hk, hk', List.replicate_succ, lexS, hcm, Ordering.then]
      | eq =>
        have he : p.1 = q.1 := by
          have := cmp_eq_iff.mp hcm
          injection this with e1 e2
          exact Prod.ext e1 e2
        rw [he, lexS_rep q.1 (expandG2 r) (expandG2 s) (he ▸ GDesc2_next h1) (GDesc2_next h2)]
        rfl

/-! ### Comparing the exponents -/

/-- A standard term of the fragment. -/
def H2 (x : Term) : Prop := OT x ∧ Sub01 x

/-- A summand `ψ_a(b)` of a standard term of the fragment. -/
def SumOK (p : Term × Term) : Prop :=
  (p.1 = nil ∨ p.1 = t1) ∧ H2 p.2 ∧ (p.1 = nil → AllNil p.2 ∨ ∃ e u, p.2 = cons t1 e u)

theorem mem_sums : ∀ (x : Term) (p : Term × Term), p ∈ sums x → H2 x →
    SumOK p ∧ dep p.2 + 1 ≤ dep x
  | nil, _, hp, _ => by cases hp
  | cons a b t, p, hp, h => by
    rcases List.mem_cons.mp hp with rfl | hp
    · refine ⟨⟨h.2.1, ⟨OT_snd h.1, h.2.2.1⟩, fun ha => ?_⟩, by simp [dep]⟩
      subst ha
      rcases argOK_of_OT (OT_head h.1) h.2.2.1 with h' | ⟨e, u, h'⟩
      · exact Or.inl h'
      · exact Or.inr ⟨e, u, h'⟩
    · obtain ⟨h1, h2⟩ := mem_sums t p hp ⟨OT_tail h.1, h.2.2.2⟩
      exact ⟨h1, by simp only [dep]; omega⟩

theorem cmpF_one_one : ∀ n : Nat, cmpF n one one = .eq
  | 0 => rfl
  | n + 1 => by
    show cmpOrdWith (cmpF n) [(.o [], 1)] [(.o [], 1)] = .eq
    rw [cmpOrdWith_cons, cmpOrdWith_nil_nil]
    show ((cmpF n [] []).then (compare 1 1)).then .eq = .eq
    rw [cmpF_nil_nil]; rfl

theorem cmpF_nil_one (n : Nat) : cmpF (n + 1) [] one = .lt := cmpOrdWith_nil_cons _ _ _
theorem cmpF_one_nil (n : Nat) : cmpF (n + 1) one [] = .gt := cmpOrdWith_cons_nil _ _ _

theorem good_of {b : Term} (hA : AllNil b) (hOT : OT b) (hd : dep b ≤ 201) : Good b :=
  ⟨⟨hA, Googology.Trans.BMS.descAll_of_OT b hOT hA⟩, hd⟩

theorem ato_atom {y : Ex} (h : y.isAtom = true) : ato y = [(y, 1)] := by
  cases y with
  | o _ => simp [Ex.isAtom] at h
  | W _ => rfl
  | psi _ _ => rfl

/-- **A normal form free of `Ω` is below every atom.** -/
theorem oa : ∀ (n : Nat) (b : Term), Good b → dep b + 1 ≤ n → ∀ y : Ex, y.isAtom = true →
    cmpF n (ofTerm b) [(y, 1)] = .lt ∧ cmpF n [(y, 1)] (ofTerm b) = .gt
  | 0, _, _, h, _, _ => by omega
  | n + 1, b, hb, hd, y, hy => by
    obtain ⟨L, hG, hO, hE⟩ := hb.inv
    show cmpOrdWith (cmpF n) (ofTerm b) [(y, 1)] = .lt ∧ cmpOrdWith (cmpF n) [(y, 1)] (ofTerm b) = .gt
    rw [hO]
    cases L with
    | nil => exact ⟨cmpOrdWith_nil_cons _ _ _, cmpOrdWith_cons_nil _ _ _⟩
    | cons p L' =>
      have hp := hb.mem_grp hG hE List.mem_cons_self
      have hdp : dep p.1 + 1 ≤ n := by
        have := (mem_exps b p.1 (hE ▸ mem_expandG hG List.mem_cons_self) hb.1).2; omega
      obtain ⟨h1, h2⟩ := oa n p.1 hp hdp y hy
      show cmpOrdWith (cmpF n) ((ex p.1, p.2) :: grp L') [(y, 1)] = .lt ∧
        cmpOrdWith (cmpF n) [(y, 1)] ((ex p.1, p.2) :: grp L') = .gt
      rw [cmpOrdWith_cons, cmpOrdWith_cons]
      have e1 : cmpExpWith (cmpF n) (ex p.1) y = .lt := by
        unfold cmpExpWith
        simp only [ex, Ex.isAtom, Bool.false_and, Bool.false_eq_true, ↓reduceIte, ato_atom hy]
        exact h1
      have e2 : cmpExpWith (cmpF n) y (ex p.1) = .gt := by
        unfold cmpExpWith
        simp only [ex, Ex.isAtom, Bool.and_false, Bool.false_eq_true, ↓reduceIte, ato_atom hy]
        exact h2
      rw [e1, e2]; exact ⟨rfl, rfl⟩

theorem lvl_psi0 (X : Od) : lvl (.psi [] X) = none := rfl
theorem lvl_W1 : lvl (.W one) = some one := rfl
theorem lvl_psi1 (X : Od) : lvl (.psi one X) = some one := rfl

theorem exS_K1 {b : Term} (h : AllNil b) : exS nil b = .o (ofTerm b) := by
  simp [exS, (omegaFree_iff b).mpr h]

theorem exS_K2 {b : Term} (h : ¬ AllNil b) : exS nil b = .psi [] (ofTerm b) := by
  have : omegaFree b = false := by
    cases h' : omegaFree b
    · rfl
    · exact absurd ((omegaFree_iff b).mp h') h
  simp [exS, this]

theorem exS_K3 : exS t1 nil = .W one := rfl

theorem exS_K4 {b : Term} (h : b ≠ nil) : exS t1 b = .psi one (ofTerm b) := by
  have hne : ¬ (t1 = nil) := fun h => Term.noConfusion h
  simp [exS, hne, h]

theorem cmpExp_o_atom (n : Nat) (X : Od) {y : Ex} (hy : y.isAtom = true) :
    cmpExpWith (cmpF n) (.o X) y = cmpF n X [(y, 1)] := by
  unfold cmpExpWith
  rw [if_neg (by simp [Ex.isAtom]), ato_atom hy]; rfl

theorem cmpExp_atom_o (n : Nat) (X : Od) {y : Ex} (hy : y.isAtom = true) :
    cmpExpWith (cmpF n) y (.o X) = cmpF n [(y, 1)] X := by
  unfold cmpExpWith
  rw [if_neg (by simp [Ex.isAtom]), ato_atom hy]; rfl

theorem cmpExp_atoms (c : Od → Od → Ordering) {x y : Ex} (hx : x.isAtom = true)
    (hy : y.isAtom = true) : cmpExpWith c x y = cmpAtomWith c x y := by
  simp [cmpExpWith, hx, hy]

/-- **The exponents compare as the summands**, given the comparison below. -/
theorem expCmp (m n : Nat) (hn : m + 1 ≤ n)
    (hQ : ∀ b b', H2 b → H2 b' → dep b ≤ m → dep b' ≤ m →
      cmpF n (ofTerm b) (ofTerm b') = Term.cmp b b')
    (p q : Term × Term) (hp : SumOK p) (hq : SumOK q) (hdp : dep p.2 ≤ m) (hdq : dep q.2 ≤ m)
    (hm : m ≤ 200) :
    cmpExpWith (cmpF n) (exS p.1 p.2) (exS q.1 q.2) = pcmp p q := by
  obtain ⟨a, b⟩ := p
  obtain ⟨a', b'⟩ := q
  obtain ⟨ha, hb, hab⟩ := hp
  obtain ⟨ha', hb', hab'⟩ := hq
  simp only at ha ha' hb hb' hab hab' hdp hdq ⊢
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hQ' := hQ b b' hb hb' hdp hdq
  rw [pcmp_def]
  have oaL : ∀ {c : Term} (hc : AllNil c) (hc2 : H2 c) (hdc : dep c ≤ m) (y : Ex),
      y.isAtom = true → cmpF (k + 1) (ofTerm c) [(y, 1)] = .lt ∧
        cmpF (k + 1) [(y, 1)] (ofTerm c) = .gt :=
    fun hc hc2 hdc y hy => oa (k + 1) _ (good_of hc hc2.1 (by omega)) (by omega) y hy
  have one_nil_c : Term.cmp nil t1 = .lt := rfl
  have one_nil_c' : Term.cmp t1 nil = .gt := rfl
  rcases ha with rfl | rfl <;> rcases ha' with rfl | rfl
  · rw [cmp_self]
    by_cases hA : AllNil b <;> by_cases hA' : AllNil b'
    · rw [exS_K1 hA, exS_K1 hA']
      simpa [cmpExpWith, Ex.isAtom, ato] using hQ'
    · obtain ⟨e', u', rfl⟩ := (hab' rfl).resolve_left hA'
      rw [exS_K1 hA, exS_K2 hA', cmpExp_o_atom _ _ rfl, (oaL hA hb hdp _ rfl).1,
        allNil_lt_t1head hA]; rfl
    · obtain ⟨e, u, rfl⟩ := (hab rfl).resolve_left hA
      have hgt : Term.cmp (cons t1 e u) b' = .gt := by
        have := allNil_lt_t1head (e := e) (u := u) hA'
        have hs := cmp_swap b' (cons t1 e u)
        rw [show Term.cmp b' (cons t1 e u) = .lt from this] at hs
        exact hs.symm
      rw [exS_K2 hA, exS_K1 hA', cmpExp_atom_o _ _ rfl, (oaL hA' hb' hdq _ rfl).2, hgt]; rfl
    · rw [exS_K2 hA, exS_K2 hA', cmpExp_atoms _ rfl rfl]
      simp only [cmpAtomWith, lvl_psi0, Option.getD_none, cmpF_nil_nil, kindA, isCardPsi, argA]
      simpa using hQ'
  · rw [one_nil_c]
    by_cases hA : AllNil b
    · rw [exS_K1 hA]
      by_cases h0 : b' = nil
      · subst h0; rw [exS_K3, cmpExp_o_atom _ _ rfl, (oaL hA hb hdp _ rfl).1]; rfl
      · rw [exS_K4 h0, cmpExp_o_atom _ _ rfl, (oaL hA hb hdp _ rfl).1]; rfl
    · rw [exS_K2 hA]
      by_cases h0 : b' = nil
      · subst h0; rw [exS_K3, cmpExp_atoms _ rfl rfl]
        simp only [cmpAtomWith, lvl_psi0, lvl_W1, Option.getD_none, Option.getD_some, cmpF_nil_one]
        rfl
      · rw [exS_K4 h0, cmpExp_atoms _ rfl rfl]
        simp only [cmpAtomWith, lvl_psi0, lvl_psi1, Option.getD_none, Option.getD_some,
          cmpF_nil_one]
        rfl
  · rw [one_nil_c']
    by_cases hA' : AllNil b'
    · rw [exS_K1 hA']
      by_cases h0 : b = nil
      · subst h0; rw [exS_K3, cmpExp_atom_o _ _ rfl, (oaL hA' hb' hdq _ rfl).2]; rfl
      · rw [exS_K4 h0, cmpExp_atom_o _ _ rfl, (oaL hA' hb' hdq _ rfl).2]; rfl
    · rw [exS_K2 hA']
      by_cases h0 : b = nil
      · subst h0; rw [exS_K3, cmpExp_atoms _ rfl rfl]
        simp only [cmpAtomWith, lvl_psi0, lvl_W1, Option.getD_none, Option.getD_some, cmpF_one_nil]
        rfl
      · rw [exS_K4 h0, cmpExp_atoms _ rfl rfl]
        simp only [cmpAtomWith, lvl_psi0, lvl_psi1, Option.getD_none, Option.getD_some,
          cmpF_one_nil]
        rfl
  · rw [cmp_self]
    by_cases h0 : b = nil <;> by_cases h0' : b' = nil
    · subst h0 h0'
      rw [exS_K3, cmpExp_atoms _ rfl rfl]
      simp only [cmpAtomWith, lvl_W1, Option.getD_some, cmpF_one_one, kindA]
      rfl
    · subst h0
      have hc : Term.cmp nil b' = .lt := by
        cases b' with
        | nil => exact absurd rfl h0'
        | cons _ _ _ => rfl
      rw [exS_K3, exS_K4 h0', cmpExp_atoms _ rfl rfl]
      simp only [cmpAtomWith, lvl_W1, lvl_psi1, Option.getD_some, cmpF_one_one, kindA, isCardPsi,
        hc]
      rfl
    · subst h0'
      have hc : Term.cmp b nil = .gt := by
        cases b with
        | nil => exact absurd rfl h0
        | cons _ _ _ => rfl
      rw [exS_K4 h0, exS_K3, cmpExp_atoms _ rfl rfl]
      simp only [cmpAtomWith, lvl_W1, lvl_psi1, Option.getD_some, cmpF_one_one, kindA, isCardPsi,
        hc]
      rfl
    · rw [exS_K4 h0, exS_K4 h0', cmpExp_atoms _ rfl rfl]
      simp only [cmpAtomWith, lvl_psi1, Option.getD_some, cmpF_one_one, kindA, isCardPsi, argA]
      simpa using hQ'

/-! ### `ofTerm` on the fragment -/

/-- **`cmpF` is the term order** on the fragment, with fuel above the depth. -/
theorem cmpF_ofTerm2 : ∀ m n : Nat, m + 1 ≤ n → m ≤ 200 → (∀ x, H2 x → dep x ≤ m → Inv2 x) →
    ∀ a b : Term, H2 a → H2 b → dep a ≤ m → dep b ≤ m →
      cmpF n (ofTerm a) (ofTerm b) = Term.cmp a b := by
  intro m
  induction m with
  | zero =>
    intro n _ _ _ a b _ _ ha hb
    rw [dep_eq_zero (Nat.le_zero.mp ha), dep_eq_zero (Nat.le_zero.mp hb)]
    exact cmpF_nil_nil n
  | succ m ih =>
    intro n hmn hm hinv a b hHa hHb ha hb
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨L1, hG1, hO1, hE1⟩ := hinv a hHa ha
    obtain ⟨L2, hG2, hO2, hE2⟩ := hinv b hHb hb
    show cmpOrdWith (cmpF n') (ofTerm a) (ofTerm b) = _
    rw [hO1, hO2, lexS_grp2 _ L1 L2 hG1 hG2, hE1, hE2, cmp_sums a b]
    intro p hp q hq
    have hp' := mem_sums a p.1 (hE1 ▸ mem_expandG2 hG1 hp) hHa
    have hq' := mem_sums b q.1 (hE2 ▸ mem_expandG2 hG2 hq) hHb
    exact expCmp m n' (by omega)
      (ih n' (by omega) (by omega) (fun x hx hd => hinv x hx (by omega)))
      p.1 q.1 hp'.1 hq'.1 (by omega) (by omega) (by omega)

theorem add_gt' {x lead : Ex} {cb : Nat} {bt : Od} (h : cmpExp x lead = .gt) :
    add [(x, 1)] ((lead, cb) :: bt) = (x, 1) :: (lead, cb) :: bt := add_gt h

theorem GDesc2_bump {d : Term × Term} {k : Nat} {L : List ((Term × Term) × Nat)}
    (h : GDesc2 ((d, k) :: L)) : GDesc2 ((d, 1 + k) :: L) := by
  cases L with
  | nil => simp [GDesc2]
  | cons q r => exact ⟨by omega, h.2.1, h.2.2⟩

/-- **`ofTerm` groups the summands** on every standard term of the fragment of
depth at most `200`. -/
theorem inv2_all : ∀ m : Nat, m ≤ 200 → ∀ x, H2 x → dep x ≤ m → Inv2 x := by
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
      have ha : a = nil ∨ a = t1 := hH.2.1
      have hdt : dep t ≤ m + 1 := by simp only [dep] at hd; omega
      have hdb : dep b ≤ m := by simp only [dep] at hd; omega
      obtain ⟨Lt, hGt, hOt, hEt⟩ := iht ⟨OT_tail hH.1, hH.2.2.2⟩ hdt
      unfold Inv2
      rw [ofTerm_cons2 ha, hOt]
      cases Lt with
      | nil =>
        refine ⟨[((a, b), 1)], by simp [GDesc2], rfl, ?_⟩
        simp [expandG2, sums] at hEt ⊢
        cases t with
        | nil => rfl
        | cons _ _ _ => simp [sums] at hEt
      | cons p L' =>
        obtain ⟨d, k⟩ := p
        have hk : 0 < k := GDesc2_head_pos hGt
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        cases t with
        | nil => simp [expandG2, sums, List.replicate_succ] at hEt
        | cons a' b' t' =>
          have hd' : (a', b') = d := by
            simp [expandG2, sums, List.replicate_succ] at hEt; exact hEt.1.symm
          subst hd'
          have hle : Term.cmp (psi a' b') (psi a b) ≠ .gt := OT_tail_head_le hH.1
          have hdb' : dep b' ≤ m := by simp only [dep] at hdt; omega
          have hsa := mem_sums (cons a b (cons a' b' t')) (a, b) List.mem_cons_self hH
          have hsb := mem_sums (cons a b (cons a' b' t')) (a', b')
            (List.mem_cons_of_mem _ List.mem_cons_self) hH
          have hc : cmpExp (exS a b) (exS a' b') = pcmp (a, b) (a', b') :=
            expCmp m fuel (by simp [fuel]; omega)
              (cmpF_ofTerm2 m fuel (by simp [fuel]; omega) (by omega) hQ)
              (a, b) (a', b') hsa.1 hsb.1 hdb hdb' (by omega)
          have hsw := pcmp_swap (a, b) (a', b')
          cases hbd : pcmp (a, b) (a', b') with
          | lt =>
            rw [hbd] at hsw
            exact absurd (show Term.cmp (psi a' b') (psi a b) = .gt from hsw.symm) hle
          | gt =>
            rw [hbd] at hc hsw
            refine ⟨((a, b), 1) :: ((a', b'), k' + 1) :: L', ⟨by omega, hsw.symm, hGt⟩, ?_, ?_⟩
            · exact add_gt hc
            · simp only [expandG2, List.flatMap_cons, sums] at hEt ⊢
              rw [hEt]; rfl
          | eq =>
            rw [hbd] at hc
            have hab : (a, b) = (a', b') := by
              have := cmp_eq_iff.mp hbd
              injection this with e1 e2
              exact Prod.ext e1 e2
            injection hab with e1 e2
            subst e1 e2
            refine ⟨((a, b), 1 + (k' + 1)) :: L', GDesc2_bump hGt, add_eq hc, ?_⟩
            simp only [expandG2, List.flatMap_cons, sums] at hEt ⊢
            rw [show 1 + (k' + 1) = (k' + 1) + 1 by omega, List.replicate_succ, List.cons_append,
              hEt]

/-! ### `writeLevel` of `Ω_1` is one column -/

/-- `M(1)`, the columns `(0,0,0)(1,1,0)`. -/
def B2 : Cols := #[⟨0, 0, false⟩, ⟨1, 1, false⟩]

theorem forest_B2 : forest B2 = #[none, some 0] := by
  apply Array.ext'
  simp [forest, B2, colAt, Array.toList_range, List.range_succ]

theorem isLevel_B2 : isLevel B2 (forest B2) 1 = true := by
  rw [forest_B2]; simp [isLevel, B2, colAt]

theorem relative_B2 : relative B2 (forest B2) 1 = true := by
  simp [relative, isLevel_B2]

theorem commonPrefix_le (a b : Cols) : commonPrefix a b ≤ b.size := by
  unfold commonPrefix
  calc _ ≤ (a.toList.zip b.toList).length := List.Sublist.length_le (List.takeWhile_sublist _)
    _ ≤ b.toList.length := by simp [List.length_zip]
    _ = b.size := by simp

theorem commonPrefix_B2 : commonPrefix B2 B2 = 2 := by simp [commonPrefix, B2]

/-- The step `writeLevel` folds over a ladder, at base `M(1)`. -/
abbrev stepB (d : Int) (acc : Int × Nat) (lad : Cols) : Int × Nat :=
  (List.range (commonPrefix lad B2)).foldl (fun li i =>
    if i ≥ 1 && isLevel B2 (forest B2) i && decide ((colAt B2 i).y ≤ d) && i > li.2
    then ((colAt B2 i).y, i) else li) acc

theorem colAt_B2_1 : colAt B2 1 = ⟨1, 1, false⟩ := rfl

theorem foldl_range_const {f : Int × Nat → Nat → Int × Nat} {acc : Int × Nat}
    (h : ∀ i, i < 2 → f acc i = acc) : ∀ k, k ≤ 2 → (List.range k).foldl f acc = acc := by
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih => rw [List.range_succ, List.foldl_append, ih (by omega)]; simp [h k (by omega)]

theorem stepB_zero (acc : Int × Nat) (lad : Cols) (hacc : acc = (0, 0)) : stepB 0 acc lad = acc := by
  unfold stepB
  refine foldl_range_const (fun i hi => ?_) _ (commonPrefix_le lad B2)
  subst hacc
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · simp
  · simp [colAt_B2_1]

theorem stepB_one_top (lad : Cols) : stepB 1 (1, 1) lad = (1, 1) := by
  unfold stepB
  refine foldl_range_const (fun i hi => ?_) _ (commonPrefix_le lad B2)
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp

theorem stepB_one_B2 : stepB 1 (0, 0) B2 = (1, 1) := by
  unfold stepB
  rw [commonPrefix_B2]
  simp [List.range_succ, isLevel_B2, colAt_B2_1]

theorem foldl_stepB_zero : ∀ (lads : List Cols), lads.foldl (stepB 0) (0, 0) = (0, 0)
  | [] => rfl
  | lad :: lads => by rw [List.foldl_cons, stepB_zero _ lad rfl, foldl_stepB_zero lads]

theorem foldl_stepB_top : ∀ (lads : List Cols), lads.foldl (stepB 1) (1, 1) = (1, 1)
  | [] => rfl
  | lad :: lads => by rw [List.foldl_cons, stepB_one_top, foldl_stepB_top lads]

theorem foldl_stepB_one (lads : List Cols) : (B2 :: lads).foldl (stepB 1) (0, 0) = (1, 1) := by
  rw [List.foldl_cons, stepB_one_B2, foldl_stepB_top]

theorem nat_zero' : nat 0 = [] := rfl
theorem nat_one' : nat 1 = one := rfl

/-- **`Ω_1` in a collapse argument, at depth `0` or `1`, is the one column
`(x, 1, 0)`**, whatever the ladders. -/
theorem writeLevel_one (Mf : Od → Cols) (h1 : Mf one = B2) (x d : Int)
    (hd : d = 0 ∨ d = 1) (lads : List Cols) :
    writeLevel Mf one x d true lads = #[⟨x, 1, false⟩] := by
  unfold writeLevel
  simp only [h1, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rcases hd with rfl | rfl
  · rw [foldl_stepB_zero]
    simp [B2, colAt]
  · rw [show (1 : Int).toNat = 1 from rfl, nat_one', h1, foldl_stepB_one]
    simp [B2, colAt, lastC]

/-! ### What the builder reads off an exponent -/

theorem lvl_exS {a b : Term} (hp : SumOK (a, b)) (hd : dep b ≤ 201) :
    lvl (exS a b) = if a = nil then none else some one := by
  obtain ⟨ha, hb, hab⟩ := hp
  simp only at ha hb hab
  rcases ha with rfl | rfl
  · by_cases hA : AllNil b
    · rw [exS_K1 hA]; exact lvl_ex (good_of hA hb.1 hd)
    · rw [exS_K2 hA]; rfl
  · have hne : ¬ (t1 = nil) := fun h => Term.noConfusion h
    rw [if_neg hne]
    by_cases h0 : b = nil
    · subst h0; rfl
    · rw [exS_K4 h0]; rfl

theorem strip_psi (v X : Od) : strip (.psi v X) = X := by
  simp [strip, ato, add_nil']

theorem strip_exS {a b : Term} (hp : SumOK (a, b)) (hd : dep b ≤ 201) :
    strip (exS a b) = ofTerm b := by
  obtain ⟨ha, hb, hab⟩ := hp
  simp only at ha hb hab
  rcases ha with rfl | rfl
  · by_cases hA : AllNil b
    · rw [exS_K1 hA]; exact strip_ex (good_of hA hb.1 hd)
    · rw [exS_K2 hA, strip_psi]
  · by_cases h0 : b = nil
    · subst h0; rfl
    · rw [exS_K4 h0, strip_psi]

theorem headIsPsi_ofTerm_good {b : Term} (hb : Good b) : headIsPsi (ofTerm b) = false := by
  obtain ⟨L, _, hO, _⟩ := hb.inv
  rw [hO]
  cases L with
  | nil => rfl
  | cons p L' => rfl

theorem headIsPsi_exS {a b : Term} (hp : SumOK (a, b)) (hd : dep b ≤ 201) :
    headIsPsi (ato (exS a b)) = (if a = nil then !(omegaFree b) else !(b == nil)) := by
  obtain ⟨ha, hb, hab⟩ := hp
  simp only at ha hb hab
  rcases ha with rfl | rfl
  · by_cases hA : AllNil b
    · rw [exS_K1 hA, (omegaFree_iff b).mpr hA]
      exact headIsPsi_ofTerm_good (good_of hA hb.1 hd)
    · have : omegaFree b = false := by
        cases h : omegaFree b
        · rfl
        · exact absurd ((omegaFree_iff b).mp h) hA
      rw [exS_K2 hA, this]; rfl
  · have hne : ¬ (t1 = nil) := fun h => Term.noConfusion h
    rw [if_neg hne]
    by_cases h0 : b = nil
    · subst h0; rfl
    · have : (b == nil) = false := by simpa using h0
      rw [exS_K4 h0, this]; rfl

/-! ### `blockF` writes the tree -/

/-- The tree of a term, as columns of the builder. -/
def treeI (x : Int) : Term → List TrioRules.Col
  | nil => []
  | cons a b t => (⟨x, (subY a : Int), false⟩ :: treeI (x + 1) b) ++ treeI x t

/-- The columns `blockF` writes, cut at the fuel. -/
def treeO : Nat → Int → Od → List TrioRules.Col
  | 0, _, _ => []
  | n + 1, x, A => A.flatMap fun ec =>
      (List.range' 0 ec.2).flatMap fun _ =>
        ⟨x, if (lvl ec.1).isSome then 1 else 0, false⟩ :: treeO n (x + 1) (strip ec.1)

/-- What `blockF` needs of its input. -/
def CondB (γ : Term) (n : Nat) (arg : Bool) (d : Int) : Prop :=
  H2 γ ∧ dep γ ≤ n ∧ dep γ ≤ 200 ∧ (arg = false → TopNil γ) ∧ (arg = true → d = 0 ∨ d = 1)

theorem sumOK_nil_of_topNil {γ : Term} (h : TopNil γ) :
    ∀ p ∈ sums γ, p.1 = nil := by
  induction γ with
  | nil => intro p hp; cases hp
  | cons a b t _ _ iht =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h.1
    · exact iht h.2 p hp

/-- **`blockF` writes `treeO`**, on the fragment. -/
theorem blockF_specT (Mf : Od → Cols) (h1 : Mf one = B2) : ∀ (n : Nat) (γ : Term) (x d : Int)
    (arg : Bool) (plvl : Option Od) (py : Int), CondB γ n arg d →
    Spec (blockF Mf n (ofTerm γ) x d arg plvl py) (fun _ => True) (treeO n x (ofTerm γ)).toArray := by
  intro n
  induction n with
  | zero =>
    intro γ x d arg plvl py _
    simpa [blockF, treeO] using spec_pure (Q := fun _ : Unit => True) trivial
  | succ n ih =>
    intro γ x d arg plvl py hc
    obtain ⟨hH, hdn, hd200, hTop, hdd⟩ := hc
    obtain ⟨L, hG, hO, hE⟩ := inv2_all 200 le_rfl γ hH hd200
    simp only [blockF]
    refine spec_bind (spec_mono (spec_forIn (ofTerm γ) _ (fun r : MProd Int Int => r = ⟨d, x⟩)
      (fun ec => (List.range' 0 ec.2).flatMap fun _ =>
        (⟨x, if (lvl ec.1).isSome then 1 else 0, false⟩ : TrioRules.Col) :: treeO n (x + 1) (strip ec.1))
      ?_ (⟨d, x⟩ : MProd Int Int) rfl) (fun _ _ => trivial)) (fun _ _ => spec_pure trivial)
      (by simp [treeO])
    intro ec hec r hr
    subst hr
    rw [hO] at hec
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hec
    have hqs := mem_sums γ q.1 (hE ▸ mem_expandG2 hG hq) hH
    obtain ⟨⟨a, b⟩, k⟩ := q
    simp only at hqs ⊢
    have hdb : dep b ≤ 201 := by omega
    have hlv := lvl_exS hqs.1 hdb
    have hst := strip_exS hqs.1 hdb
    have hhp := headIsPsi_exS hqs.1 hdb
    rw [hst]
    have hcb : ∀ (arg' : Bool) (d' : Int), (arg' = false → TopNil b) → (arg' = true → d' = 0 ∨ d' = 1) →
        CondB b n arg' d' := fun arg' d' h1 h2 =>
      ⟨hqs.1.2.1, by omega, by omega, h1, h2⟩
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    by_cases ha : a = nil
    · -- a `ψ_0` node: the column `(x, 0, 0)`
      subst ha
      rw [if_pos rfl] at hlv hhp
      have hcol : (if (lvl (exS nil b)).isSome then (1 : Int) else 0) = 0 := by rw [hlv]; rfl
      rw [hcol]
      refine spec_bind (w2 := #[]) (spec_forIn _ _ (fun r : MProd Int Int => r = ⟨d, x⟩)
        (fun _ => ⟨x, 0, false⟩ :: treeO n (x + 1) (ofTerm b)) ?_ (⟨d, x⟩ : MProd Int Int) rfl)
        (fun r hr => ?_) ?_
      · intro i _ r hr
        subst hr
        refine spec_get_bind fun s1 _ => spec_get_bind fun s2 hs2 => ?_
        rw [spent_none Mf s2 hs2]
        simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte, hlv]
        rw [show (({ x := x, y := 0, z := false } :: treeO n (x + 1) (ofTerm b)).toArray :
            Array TrioRules.Col) = #[⟨x, 0, false⟩] ++ (treeO n (x + 1) (ofTerm b)).toArray by simp]
        repeat trioE0_step
        rw [spent_none Mf _ ‹_›]
        simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        repeat trioE0_step
        refine spec_bind_last (ih b _ _ _ _ _ (hcb _ _ ?_ ?_)) (fun _ _ => ?_)
        · intro hf
          rw [hhp] at hf
          have hA : AllNil b := (omegaFree_iff b).mp (by simpa using hf)
          exact topNil_of_allNil b hA
        · intro _; left; rfl
        · repeat trioE0_step
      · subst hr
        repeat trioE0_step
      · simp [Std.Legacy.Range.size]
    · -- a `ψ_1` node: the column `(x, 1, 0)`
      have ha1 : a = t1 := hqs.1.1.resolve_left ha
      subst ha1
      rw [if_neg ha] at hlv hhp
      have harg : arg = true := by
        cases harg : arg
        · exfalso
          have := sumOK_nil_of_topNil (hTop harg) (t1, b) (hE ▸ mem_expandG2 hG hq)
          exact ha this
        · rfl
      subst harg
      have hd01 := hdd rfl
      have hcol : (if (lvl (exS t1 b)).isSome then (1 : Int) else 0) = 1 := by rw [hlv]; rfl
      rw [hcol]
      refine spec_bind (w2 := #[]) (spec_forIn _ _ (fun r : MProd Int Int => r = ⟨d, x⟩)
        (fun _ => ⟨x, 1, false⟩ :: treeO n (x + 1) (ofTerm b)) ?_ (⟨d, x⟩ : MProd Int Int) rfl)
        (fun r hr => ?_) ?_
      · intro i _ r hr
        subst hr
        refine spec_get_bind fun s1 _ => spec_get_bind fun s2 hs2 => ?_
        rw [spent_none Mf s2 hs2]
        simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte, hlv, Bool.not_true,
          Bool.false_and, writeLevel_one Mf h1 x d hd01]
        rw [show (({ x := x, y := 1, z := false } :: treeO n (x + 1) (ofTerm b)).toArray :
            Array TrioRules.Col) = #[⟨x, 1, false⟩] ++ (treeO n (x + 1) (ofTerm b)).toArray by simp]
        repeat trioE0_step
        rw [spent_none Mf _ ‹_›]
        simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        repeat trioE0_step
        refine spec_bind_last (ih b _ _ _ _ _ (hcb _ _ ?_ ?_)) (fun _ _ => ?_)
        · intro hf
          rw [hhp] at hf
          have : b = nil := by simpa using hf
          subst this; trivial
        · intro _; right; rfl
        · repeat trioE0_step
      · subst hr
        repeat trioE0_step
      · simp [Std.Legacy.Range.size]

theorem treeI_sums (x : Int) : ∀ γ : Term,
    treeI x γ = (sums γ).flatMap (fun p => (⟨x, (subY p.1 : Int), false⟩ : TrioRules.Col) :: treeI (x + 1) p.2)
  | nil => rfl
  | cons a b t => by rw [treeI, sums, List.flatMap_cons, treeI_sums x t]

theorem grp2_flatMap {β : Type} (F : Ex → List β) : ∀ L : List ((Term × Term) × Nat),
    (grp2 L).flatMap (fun ec => (List.range' 0 ec.2).flatMap (fun _ => F ec.1)) =
      (expandG2 L).flatMap (fun p => F (exS p.1 p.2)) := by
  intro L
  induction L with
  | nil => rfl
  | cons p L ih =>
    simp only [grp2, List.map_cons] at ih ⊢
    rw [List.flatMap_cons, ih, flatMap_range'_const]
    simp only [expandG2, List.flatMap_cons, List.flatMap_append]
    congr 1
    generalize p.2 = k
    induction k with
    | zero => rfl
    | succ k ihk => simp [List.replicate_succ, List.flatMap_cons, ihk]

/-- **`treeO` is the tree**, when the fuel covers the depth. -/
theorem treeO_ofTerm : ∀ (n : Nat) (γ : Term) (x : Int), H2 γ → dep γ ≤ n → dep γ ≤ 200 →
    treeO n x (ofTerm γ) = treeI x γ := by
  intro n
  induction n with
  | zero =>
    intro γ x _ hd _
    rw [dep_eq_zero (Nat.le_zero.mp hd)]; rfl
  | succ n ih =>
    intro γ x hH hd hd2
    obtain ⟨L, hG, hO, hE⟩ := inv2_all 200 le_rfl γ hH hd2
    show (ofTerm γ).flatMap _ = _
    rw [hO, grp2_flatMap (fun e => (⟨x, if (lvl e).isSome then 1 else 0, false⟩ : TrioRules.Col) ::
      treeO n (x + 1) (strip e)) L, hE, treeI_sums]
    apply List.flatMap_congr
    intro p hp
    have hps := mem_sums γ p hp hH
    obtain ⟨a, b⟩ := p
    simp only at hps ⊢
    rw [lvl_exS hps.1 (by omega), strip_exS hps.1 (by omega),
      ih b (x + 1) hps.1.2.1 (by omega) (by omega)]
    congr 2
    rcases hps.1.1 with rfl | rfl
    · simp [subY]
    · simp [subY]

theorem treeI_colsOf (x : Nat) : ∀ γ : Term, treeI (x : Int) γ = colsOf (treeB x γ)
  | nil => rfl
  | cons a b t => by
    rw [treeI, treeB, colsOf, List.map_append, List.map_cons, ← colsOf, ← colsOf,
      ← treeI_colsOf (x + 1) b, ← treeI_colsOf x t]
    simp [toCol]

/-! ### The add units -/

open Googology.Trans.BMS (addUnits bodyU mulUnits peelOne prSS WF3)

theorem units_grp2 (L : List ((Term × Term) × Nat)) :
    units (grp2 L) = (expandG2 L).map (fun p => exS p.1 p.2) := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    simp only [units, grp2, List.map_cons, List.flatMap_cons, expandG2, List.map_append,
      List.map_replicate] at ih ⊢
    rw [ih]

theorem sums_map_topNil : ∀ t : Term, TopNil t →
    (sums t).map (fun p => exS p.1 p.2) = (exps t).map (exS nil)
  | nil, _ => rfl
  | cons a b t, h => by
    obtain ⟨rfl, ht⟩ := h
    simp [sums, exps, sums_map_topNil t ht]

theorem units_ofTermE {x : Term} (hH : H2 x) (hT : TopNil x) (hd : dep x ≤ 200) :
    units (ofTerm x) = (exps x).map (exS nil) := by
  obtain ⟨L, _, hO, hE⟩ := inv2_all 200 le_rfl x hH hd
  rw [hO, units_grp2, hE, sums_map_topNil x hT]

theorem addUnitsE_split (rp1 lastX : Nat) (pz : Bool) (i : Nat) (a e t : Term) :
    addUnitsE rp1 lastX pz i (cons a e t) =
      addUnitsE rp1 lastX pz i (cons a e nil) ++
        addUnitsE (nrp e rp1) (nlx e rp1 lastX pz) (e == nil) (i + 1) t := by
  by_cases he : e = nil
  · subst he
    cases pz <;> simp [addUnitsE, nrp, nlx]
  · have : (e == nil) = false := by simp [he]
    simp [addUnitsE, nrp, nlx, he, this]

/-- The units of the fragment the loop lays: a standard `ψ_0(e)` of depth at
most `200`. -/
def UnitE (e : Term) : Prop := SumOK (nil, e) ∧ dep e ≤ 199 ∧ OT (psi nil e)

theorem loop_unitsE (f : Ex → Tup → StateM Ctx (ForInStep Tup))
    (hf : ∀ e, UnitE e → ∀ (first : Bool) (rp1 lastX : Nat) (pz : Bool) (i : Nat) (s : Ctx),
      1 ≤ i → s.regime = none → (pz = true → lastC s.cols = ⟨lastX, (i : Int) - 1, false⟩) →
      ∃ s', (f (exS nil e) ⟨first, (i : Int) - 1, pz, (rp1 : Int) - 1⟩).run s =
          (.yield ⟨false, ((i + 1 : Nat) : Int) - 1, e == nil, ((nrp e rp1 : Nat) : Int) - 1⟩, s') ∧
        s'.cols = s.cols ++ (colsOf (addUnitsE rp1 lastX pz i (cons nil e nil))).toArray ∧
        s'.regime = none ∧
        (e = nil → lastC s'.cols = ⟨nlx e rp1 lastX pz, ((i + 1 : Nat) : Int) - 1, false⟩)) :
    ∀ t : Term, H2 t → TopNil t → dep t ≤ 200 → ∀ (first : Bool) (rp1 lastX : Nat) (pz : Bool)
      (i : Nat) (s : Ctx),
      1 ≤ i → s.regime = none → (pz = true → lastC s.cols = ⟨lastX, (i : Int) - 1, false⟩) →
      ∃ r s', (forIn ((exps t).map (exS nil)) (⟨first, (i : Int) - 1, pz, (rp1 : Int) - 1⟩ : Tup) f).run s
          = (r, s') ∧
        s'.cols = s.cols ++ (colsOf (addUnitsE rp1 lastX pz i t)).toArray ∧ s'.regime = none := by
  intro t
  induction t with
  | nil =>
    intro _ _ _ first rp1 lastX pz i s _ hs _
    exact ⟨_, s, rfl, by simp [addUnitsE, colsOf], hs⟩
  | cons a e t _ _ iht =>
    intro hH hT hd first rp1 lastX pz i s hi hs hl
    obtain ⟨rfl, hTt⟩ := hT
    have hU : UnitE e := by
      have := mem_sums (cons nil e t) (nil, e) List.mem_cons_self hH
      exact ⟨this.1, by simp only [dep] at hd; omega, OT_head hH.1⟩
    have hdt : dep t ≤ 200 := by simp only [dep] at hd; omega
    obtain ⟨s1, h1, hc1, hr1, hl1⟩ := hf e hU first rp1 lastX pz i s hi hs hl
    obtain ⟨r, s2, h2, hc2, hr2⟩ := iht ⟨OT_tail hH.1, hH.2.2.2⟩ hTt hdt false (nrp e rp1)
      (nlx e rp1 lastX pz) (e == nil) (i + 1) s1 (by omega) hr1 (fun h => hl1 (by simpa using h))
    refine ⟨r, s2, ?_, ?_, hr2⟩
    · simp only [exps, List.map_cons, List.forIn_cons]
      rw [run_bind', h1]
      push_cast at h2 ⊢
      exact h2
    · rw [hc2, hc1, addUnitsE_split rp1 lastX pz i nil e t]
      simp [colsOf, Array.append_assoc]

theorem run_loopE (α : Term) (hH : H2 α) (hT : TopNil α) (hd : dep α ≤ 200)
    (f : Ex → Tup → StateM Ctx (ForInStep Tup))
    (hf : ∀ e, UnitE e → ∀ (first : Bool) (rp1 lastX : Nat) (pz : Bool) (i : Nat) (s : Ctx),
      1 ≤ i → s.regime = none → (pz = true → lastC s.cols = ⟨lastX, (i : Int) - 1, false⟩) →
      ∃ s', (f (exS nil e) ⟨first, (i : Int) - 1, pz, (rp1 : Int) - 1⟩).run s =
          (.yield ⟨false, ((i + 1 : Nat) : Int) - 1, e == nil, ((nrp e rp1 : Nat) : Int) - 1⟩, s') ∧
        s'.cols = s.cols ++ (colsOf (addUnitsE rp1 lastX pz i (cons nil e nil))).toArray ∧
        s'.regime = none ∧
        (e = nil → lastC s'.cols = ⟨nlx e rp1 lastX pz, ((i + 1 : Nat) : Int) - 1, false⟩))
    (S : Ctx) (hS : S.regime = none) (hS0 : S.cols = #[]) :
    (StateT.run (pure PUnit.unit >>= fun _ =>
        forIn ((exps α).map (exS nil)) (⟨true, 0, false, -1⟩ : Tup) f >>= fun _ => pure PUnit.unit) S).2.cols =
      (colsOf (addUnitsE 0 0 false 1 α)).toArray := by
  obtain ⟨r, s', hrun, hc, -⟩ := loop_unitsE f hf α hH hT hd true 0 0 false 1 S le_rfl hS (by simp)
  have e1 : (⟨true, 0, false, -1⟩ : Tup) = ⟨true, ((1 : Nat) : Int) - 1, false, ((0 : Nat) : Int) - 1⟩ := rfl
  have key : (StateT.run (pure PUnit.unit >>= fun _ =>
        forIn ((exps α).map (exS nil)) (⟨true, 0, false, -1⟩ : Tup) f >>= fun _ => pure PUnit.unit) S) =
      (PUnit.unit, s') := by
    rw [run_bind']
    show (forIn ((exps α).map (exS nil)) (⟨true, 0, false, -1⟩ : Tup) f >>= fun _ => pure PUnit.unit).run S = _
    rw [run_bind', e1, hrun]
    rfl
  rw [key]
  show s'.cols = _
  rw [hc, hS0]; simp

theorem exS_nil_ex {e : Term} (h : AllNil e) : exS nil e = ex e := exS_K1 h

theorem ofTerm_psi0 (e : Term) : ofTerm (psi nil e) = [(exS nil e, 1)] := by
  rw [ofTerm_cons2 (Or.inl rfl), ofTerm_nil, add_nil']

/-- **`placeUnits` lays `trioE`'s add units**, on the fragment. -/
theorem placeUnits_ofTermE (Mf : Od → Cols) (h1 : Mf one = B2) (α : Term) (hH : H2 α)
    (hT : TopNil α) (hd : dep α ≤ 200) :
    (placeUnits Mf #[] (ofTerm α) 0 (-1) none).cols = (colsOf (addUnitsE 0 0 false 1 α)).toArray := by
  have hpb : PredBetaSpec := predBetaSpec
  unfold placeUnits
  simp only [Option.bind_none, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, List.drop_zero,
    units_ofTermE hH hT hd]
  refine run_loopE α hH hT hd _ ?_ _ rfl rfl
  intro e hU first rp1 lastX pz i s hi hs hl
  by_cases hA : AllNil e
  · rw [exS_nil_ex hA, addUnitsE_allNil (cons nil e nil) (show AllNil (cons nil e nil) from ⟨rfl, hA, trivial⟩)]
    have he : Good e := good_of hA hU.1.2.1.1 (by have := hU.2.1; omega)
    have hde : dep e ≤ 200 := by have := hU.2.1; omega
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
  · -- a unit whose exponent is the atom `ψ_0(e)`
    have he0 : e ≠ nil := fun h => hA (h ▸ trivial)
    have hsp : ∀ c : Ctx, c.regime = s.regime → spent Mf c = false := fun c hc =>
      spent_none Mf c (hc.trans hs)
    have hEK : exS nil e = .psi [] (ofTerm e) := exS_K2 hA
    have hbeta : ato (exS nil e) = [(exS nil e, 1)] := by rw [hEK]; rfl
    have hpred : predBeta [(exS nil e, 1)] = [(exS nil e, 1)] := by rw [hEK]; rfl
    have hunitsE : units (predBeta [(exS nil e, 1)]) = [exS nil e] := by rw [hpred]; rfl
    have hato : ato (exS nil e) = ofTerm (psi nil e) := by rw [hbeta, ofTerm_psi0]
    have hS1 : Sub01 (psi nil e) := ⟨Or.inl rfl, hU.1.2.1.2, trivial⟩
    have hH1 : H2 (psi nil e) := ⟨hU.2.2, hS1⟩
    have hdp : dep (psi nil e) ≤ 200 := by
      have := hU.2.1; simp only [dep]; omega
    let w : Ex → List TrioRules.Col := fun _ =>
      ⟨(rp1 : Int) - 1 + 1 + 1 + 1, (i : Int) - 1 + 1, true⟩ ::
        treeO fuel ((rp1 : Int) - 1 + 1 + 1 + 2) (ofTerm (psi nil e))
    have hW : (colsOf (addUnitsE rp1 lastX pz i (cons nil e nil))).toArray =
        #[⟨(rp1 : Int) - 1 + 1, (i : Int) - 1, false⟩, ⟨(rp1 : Int) - 1 + 1 + 1, (i : Int) - 1 + 1, true⟩] ++
          ([exS nil e].flatMap w).toArray := by
      have hb : (e == nil) = false := by simp [he0]
      have hx : ((rp1 : Int) - 1 + 1 + 1 + 2) = ((rp1 + 1 + 2 : Nat) : Int) := by push_cast; ring
      simp only [addUnitsE, hb, Bool.false_eq_true, ↓reduceIte, bodyE, peelE_of_not hA, mulUnitsE,
        List.append_nil, List.flatMap_cons, List.flatMap_nil, w]
      rw [hx, treeO_ofTerm fuel (psi nil e) _ hH1 (by simp only [fuel]; omega) hdp, treeI_colsOf]
      simp only [colsOf, List.map_cons]
      apply Array.ext'
      simp [toCol]
      omega
    refine hf_of_spec ?_ hs (fun _ h => absurd h he0)
    rw [hW]
    trioE0_step
    refine spec_get_bind fun s1 hs1 => ?_
    simp only [spent_none Mf s1 hs1, Bool.and_false, Bool.false_eq_true, ↓reduceIte, hbeta,
      List.isEmpty_cons, Bool.false_and]
    repeat trioE0_step
    rw [hunitsE]
    refine spec_bind_last (spec_forIn _ _
      (fun r : MProd Nat (MProd Int Int) => r.snd = ⟨(rp1 : Int) - 1 + 1 + 1, (i : Int) - 1 + 1⟩) w
      ?_ _ rfl) (fun r hr => ?_)
    · intro a ha b hb
      simp only [List.mem_singleton] at ha
      subst ha
      obtain ⟨j, x0', y'⟩ := b
      simp only [MProd.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      refine spec_get_bind fun s2 _ => spec_get_bind fun s3 hs3 => ?_
      simp only [spent_none Mf s3 hs3, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      show Spec _ _ (List.toArray (_ :: _))
      rw [List.toArray_cons]
      repeat trioE0_step
      rw [hato]
      refine spec_bind_last (blockF_specT Mf h1 fuel (psi nil e) _ _ false _ _
        ⟨hH1, by simp only [fuel]; omega, hdp, fun _ => ⟨rfl, trivial⟩, fun h => by simp at h⟩)
        (fun _ _ => ?_)
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

/-! ### The end of the matrix and the level -/

theorem ofTerm_eq_nil_iff2 {x : Term} (hH : H2 x) (hd : dep x ≤ 200) : ofTerm x = [] ↔ x = nil := by
  obtain ⟨L, hG, hO, hE⟩ := inv2_all 200 le_rfl x hH hd
  constructor
  · intro h
    rw [hO] at h
    have hL : L = [] := List.map_eq_nil_iff.mp h
    subst hL
    cases x with
    | nil => rfl
    | cons _ _ _ => simp [expandG2, sums] at hE
  · rintro rfl; rfl

theorem mem_sums_of_mem_exps : ∀ t : Term, TopNil t → ∀ e ∈ exps t, (nil, e) ∈ sums t
  | nil, _, _, h => by cases h
  | cons a b t, hT, e, he => by
    obtain ⟨rfl, hTt⟩ := hT
    rcases List.mem_cons.mp he with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_sums_of_mem_exps t hTt e h)

theorem OT_of_mem_sums : ∀ t : Term, OT t → ∀ p ∈ sums t, OT (psi p.1 p.2)
  | nil, _, _, h => by cases h
  | cons a b t, hOT, p, hp => by
    rcases List.mem_cons.mp hp with rfl | h
    · exact OT_head hOT
    · exact OT_of_mem_sums t (OT_tail hOT) p h

theorem tailBlockF_tree : ∀ (n : Nat) (γ : Term) (arg : Bool), H2 γ → dep γ ≤ 200 →
    (arg = false → TopNil γ) → tailBlockF n (ofTerm γ) arg = none := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _; rfl
  | succ n ih =>
    intro γ arg hH hd hT
    obtain ⟨L, hG, hO, hE⟩ := inv2_all 200 le_rfl γ hH hd
    unfold tailBlockF
    split
    · rfl
    · rename_i e c hlast
      rw [hO] at hlast
      obtain ⟨q, hq, hqe⟩ := List.mem_map.mp (List.mem_of_getLast? hlast)
      have hqs := mem_sums γ q.1 (hE ▸ mem_expandG2 hG hq) hH
      obtain ⟨⟨a, b⟩, k⟩ := q
      simp only [Prod.mk.injEq] at hqe
      dsimp only at hqs
      rw [← hqe.1, strip_exS hqs.1 (by omega)]
      dsimp only
      by_cases hr : (ofTerm b).isEmpty = true
      · have hb : b = nil := (ofTerm_eq_nil_iff2 (x := b) hqs.1.2.1 (by omega)).mp (List.isEmpty_iff.mp hr)
        subst hb
        simp only [hr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        cases arg
        · have ha : a = nil :=
            sumOK_nil_of_topNil (hT rfl) (a, nil) (hE ▸ mem_expandG2 hG hq)
          subst ha
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [lvl_exS hqs.1 (by omega), if_pos rfl]
        · rfl
      · simp only [hr, Bool.not_false, ↓reduceIte]
        refine ih b _ hqs.1.2.1 (show dep b ≤ 200 by omega) (fun hf => ?_)
        rw [headIsPsi_exS hqs.1 (by omega)] at hf
        by_cases ha : a = nil
        · rw [if_pos ha] at hf
          exact topNil_of_allNil b ((omegaFree_iff b).mp (by simpa using hf))
        · rw [if_neg ha] at hf
          have : b = nil := by simpa using hf
          subst this; trivial

theorem tailLevel_ofTermE {α : Term} (hH : H2 α) (hT : TopNil α) (hd : dep α ≤ 200) :
    tailLevel (ofTerm α) = none := by
  have hpb : PredBetaSpec := predBetaSpec
  unfold tailLevel
  rw [units_ofTermE hH hT hd]
  split
  · rfl
  · rename_i bb hb
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_of_getLast? hb)
    have hsum : (nil, e) ∈ sums α := mem_sums_of_mem_exps α hT e he
    have hms := mem_sums α (nil, e) hsum hH
    simp only at hms
    by_cases hA : AllNil e
    · rw [exS_nil_ex hA]
      have hge : Good e := good_of hA hms.1.2.1.1 (by omega)
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
    · have hEK : exS nil e = .psi [] (ofTerm e) := exS_K2 hA
      have hbeta : ato (exS nil e) = [(exS nil e, 1)] := by rw [hEK]; rfl
      have hpred : predBeta [(exS nil e, 1)] = [(exS nil e, 1)] := by rw [hEK]; rfl
      unfold unitTailLevel
      rw [hbeta, hpred]
      simp only [List.isEmpty_cons, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
        List.getLast?_singleton]
      show tailBlockF fuel (ato (exS nil e)) false = none
      rw [hbeta, ← ofTerm_psi0]
      exact tailBlockF_tree fuel (psi nil e) false
        ⟨OT_of_mem_sums α hH.1 _ hsum, Or.inl rfl, hms.1.2.1.2, trivial⟩
        (by simp only [dep]; omega) (fun _ => ⟨rfl, trivial⟩)

theorem lvlO_ofTermE {α : Term} (hH : H2 α) (hT : TopNil α) (hd : dep α ≤ 200) :
    lvlO (ofTerm α) = none := by
  obtain ⟨L, hG, hO, hE⟩ := inv2_all 200 le_rfl α hH hd
  show lvlF (199 + 1) (.o (ofTerm α)) = none
  rw [hO]
  cases L with
  | nil => rfl
  | cons q L' =>
    show lvlF 199 (exS q.1.1 q.1.2) = none
    have hqs := mem_sums α q.1 (hE ▸ mem_expandG2 hG List.mem_cons_self) hH
    obtain ⟨⟨a, b⟩, k⟩ := q
    dsimp only at hqs ⊢
    have ha : a = nil := sumOK_nil_of_topNil hT (a, b) (hE ▸ mem_expandG2 hG List.mem_cons_self)
    subst ha
    by_cases hA : AllNil b
    · rw [exS_nil_ex hA]
      exact lvlF_ex 199 b (good_of hA hqs.1.2.1.1 (by omega))
    · rw [exS_K2 hA]; rfl

/-! ### The theorem -/

theorem Mfuel_ofTerm_good (k : Nat) (α : Term) (hα : Good α) :
    Mfuel (k + 1) (ofTerm α) = (colsOf (Googology.Trans.BMS.omegaIndexMatrix α)).toArray := by
  rw [Mfuel]
  unfold Mstep
  have hl : lvlO (ofTerm α) = none := lvl_ex hα
  rw [hl]
  dsimp only
  unfold finish
  rw [tailLevel_ofTerm predBetaSpec hα]
  dsimp only
  exact placeUnits_ofTerm predBetaSpec _ α hα

theorem Mfuel_one : Mfuel 199 one = B2 := by
  rw [← ofTerm_t1, Mfuel_ofTerm_good 198 t1 ⟨⟨⟨rfl, trivial, trivial⟩, ⟨trivial, trivial, rfl⟩⟩,
    by decide⟩]
  rfl

theorem M_ofTermE (α : Term) (hH : H2 α) (hT : TopNil α) (hd : dep α ≤ 200) :
    M (ofTerm α) = (colsOf (trioE α)).toArray := by
  unfold M
  rw [show fuel = 199 + 1 from rfl, Mfuel]
  unfold Mstep
  rw [lvlO_ofTermE hH hT hd]
  dsimp only
  unfold finish
  rw [tailLevel_ofTermE hH hT hd]
  dsimp only
  exact placeUnits_ofTermE _ Mfuel_one α hH hT hd

theorem WF3_treeB (x : Nat) (t : Term) : WF3 (treeB x t) := by
  intro c hc
  obtain ⟨x', v, _, _, rfl⟩ := TrioTreeStd.treeB_shape t x c hc
  exact ⟨rfl, by simp⟩

theorem WF3_mulUnitsE (x0 y : Nat) : ∀ t : Term, WF3 (mulUnitsE x0 y t)
  | nil => Googology.Trans.BMS.WF3_nil
  | cons _ g t => Googology.Trans.BMS.WF3_append
      (Googology.Trans.BMS.WF3_cons ⟨rfl, by simp⟩ (WF3_treeB _ g)) (WF3_mulUnitsE x0 y t)

theorem WF3_addUnitsE : ∀ (α : Term) (rp1 lastX : Nat) (pz : Bool) (i : Nat),
    WF3 (addUnitsE rp1 lastX pz i α) := by
  intro α
  induction α with
  | nil => intro _ _ _ _; exact Googology.Trans.BMS.WF3_nil
  | cons _ b t _ _ iht =>
    intro rp1 lastX pz i
    rw [addUnitsE]
    split
    · split
      · exact Googology.Trans.BMS.WF3_cons ⟨rfl, by simp⟩ (iht _ _ _ _)
      · exact Googology.Trans.BMS.WF3_cons ⟨rfl, by simp⟩
          (Googology.Trans.BMS.WF3_cons ⟨rfl, by simp⟩ (iht _ _ _ _))
    · exact Googology.Trans.BMS.WF3_append (Googology.Trans.BMS.WF3_cons ⟨rfl, by simp⟩
        (Googology.Trans.BMS.WF3_cons ⟨rfl, by simp⟩ (WF3_mulUnitsE _ _ _))) (iht _ _ _ _)

/-- **Rules 1–10 compute `trioE`** on every standard countable term whose
subscripts are `0` or `1` and whose nesting depth is at most `200`. -/
theorem trioMatrixL_eq_trioE {α : Term} (hOT : OT α) (hc : α < tW) (hS : Sub01 α)
    (hd : dep α ≤ 200) : trioMatrixL α = trioE α := by
  unfold trioMatrixL trioRuleMatrix
  rw [M_ofTermE α ⟨hOT, hS⟩ (topNil_of_lt_tW hOT hc) hd]
  exact toRows_colsOf _ (WF3_addUnitsE α 0 0 false 1)

/-- **So the image of `trioMatrixL` there is in the standard forms of three-row
BMS.** -/
theorem trioMatrixL_std {α : Term} (hOT : OT α) (hc : α < tW) (hS : Sub01 α)
    (hd : dep α ≤ 200) : ∃ A : BM4.Arr 3, Pat.Std 3 A ∧ entriesR A = trioMatrixL α := by
  rw [trioMatrixL_eq_trioE hOT hc hS hd]
  exact TrioTreeStd.trioE_std hOT hc hS

/-- **And `trioMatrixL` preserves and reflects the order there.** -/
theorem trioMatrixL_lt_iff {α β : Term} (hα : OT α) (hβ : OT β) (hαc : α < tW) (hβc : β < tW)
    (sα : Sub01 α) (sβ : Sub01 β) (dα : dep α ≤ 200) (dβ : dep β ≤ 200) :
    trioMatrixL α < trioMatrixL β ↔ α < β := by
  rw [trioMatrixL_eq_trioE hα hαc sα dα, trioMatrixL_eq_trioE hβ hβc sβ dβ]
  exact trioE_lt_iff hα hβ hαc hβc sα sβ

/-- **So it is injective there.** -/
theorem trioMatrixL_injective {α β : Term} (hα : OT α) (hβ : OT β) (hαc : α < tW) (hβc : β < tW)
    (sα : Sub01 α) (sβ : Sub01 β) (dα : dep α ≤ 200) (dβ : dep β ≤ 200)
    (h : trioMatrixL α = trioMatrixL β) : α = β := by
  rw [trioMatrixL_eq_trioE hα hαc sα dα, trioMatrixL_eq_trioE hβ hβc sβ dβ] at h
  exact trioE_injective hα hβ hαc hβc sα sβ h

end Googology.Trans.BMS.TrioTreeRules

/-! ### Calibration: where the fuel runs out on the fragment

`#guard`s — checks of the compiled program, not theorems. -/

namespace Googology.Trans.BMS.TrioTreeRules

open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term
open Googology.Trans.BMS.TrioTree (towerP trioE)

-- `ψ_0(Ω + T_k)` has depth `k + 1`: it agrees at depth `200`, not at `201`.
#guard TrioRulesE0.dep (psi nil (cons t1 nil (towerP 199))) = 200
#guard TrioRules.trioMatrixL (psi nil (cons t1 nil (towerP 199))) = trioE (psi nil (cons t1 nil (towerP 199)))
#guard TrioRules.trioMatrixL (psi nil (cons t1 nil (towerP 200))) ≠ trioE (psi nil (cons t1 nil (towerP 200)))
-- `ψ_0(ψ_1(T_k))` has depth `k + 2`: the same bound.
#guard TrioRulesE0.dep (psi nil (psi t1 (towerP 198))) = 200
#guard TrioRules.trioMatrixL (psi nil (psi t1 (towerP 198))) = trioE (psi nil (psi t1 (towerP 198)))
#guard TrioRules.trioMatrixL (psi nil (psi t1 (towerP 199))) ≠ trioE (psi nil (psi t1 (towerP 199)))

end Googology.Trans.BMS.TrioTreeRules

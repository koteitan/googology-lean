import Googology.Trans.BMS.TrioFixStrip
import Googology.Trans.BMS.TrioTreeStd

/-!
# The patched trio map below `ψ_0(Ω_2)`: its structure, order and standard forms

`TrioFixStrip.trioMatrixLSt` is the trio map of
[koteitan/trio](https://github.com/koteitan/trio) with the reading `ofTermFix`
(`TrioFixOfTerm.lean`) and the corrected rule 1 (`TrioFixStrip.lean`).  `TrioTree.lean`
wrote the old map on the countable standard terms with subscripts `0`/`1` as a
structural recursion `trioE`; this file does the same for the patched map.

## The map `trioE2`

As `trioE`, with a different multiply part (`peelE2` for `peelE`).  An add unit
`ψ_0(b)` is `ω^β`; its digits are the summands of `β` (after `1 + β' = β`), and a
digit `ω^X` is written as the tree of a sum of `ψ_0`s whose value is `X`.

* `b` free of `Ω`: as before, `β' = peelOne b`.
* `b = h + l`, `h` the leading summands `ψ_1(·)` (`hiPart`), `l` the rest, a sum of
  `ψ_0(g_j)` (`loPart`): `ψ_0(b) = ω^{ψ_0(h) + l}`.  The digits are `ψ_0(h)` (the tree
  of the term `ψ_0(h)`), unless it is absorbed (`absorbs`: `h < g_1`, so
  `ψ_0(h) + l = l`), then one digit per summand `ψ_0(g_j)` of `l`, written as the tree
  of `expoT g_j`, where `expoT g = ψ_0(hiPart g) + loPart g` (or `loPart g` if
  absorbed) is the exponent of `ψ_0(g) = ω^{expoT g}`, or `g` itself if `g` is free
  of `Ω`.  So `peelE2 b = mapArgs (expoT b)`.

For comparison, the old map had one digit, the tree of `ψ_0(b)`.

## What is proved

* `trioE2_lt_iff`, `trioE2_injective`: for standard `α, β < Ω` with every subscript
  `0` or `1`, `trioE2 α < trioE2 β ↔ α < β`.  The key step is `expoT_lt`: `expoT`
  keeps the order on the arguments of the fragment (`Good`, which every argument of
  `ψ_0` in a standard term is: `good_of_OT`).
* `trioE2_std`: `trioE2 α` is a standard form of three-row BMS, by `TrioTreeStd`'s
  `reach_units`; the digits are standard terms (`OT_expoT`, via `OT_psi_hiPart`: the
  `Ω` part of a standard argument of `ψ_0` is again one) and descending.

## What is not proved

That the program computes `trioE2`: `trioMatrixLSt α = trioE2 α`.  It is checked by
`#guard` on the 2,398 terms of `TrioTree.smallFrag 7` (every standard countable term
with at most 7 `ψ`s and subscripts `0`/`1`, `0` included), and proved by `decide` for
the two terms of `TrioFixOfTerm.trioMatrixLFix_order_fails`.  The proof for the old
map (`TrioTreeRules.trioMatrixL_eq_trioE`, depth `≤ 200`) does not carry over as it
stands: it is about rules 1–10 (`TrioRules.M`) and the reading `ofTerm`, while the
patched map runs the merged builder (Fixes A–E, N) with `ofTermFix` and `stripSt`.  So
the order and standardness of `trioMatrixLSt` itself on the fragment rest on that
calibration: it is stated as the open `Prop` `CalibSt`, and
`trioMatrixLSt_lt_iff_of_calib`, `trioMatrixLSt_std_of_calib` are proved from it.
-/

namespace Googology.Trans.BMS.TrioFixStripTree

open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term
open Googology.Trans.BMS (AllNil peelOne headLe)
open Googology.Trans.BMS.TrioMono
open Googology.Trans.BMS.TrioTree
open Googology.Trans.BMS.TrioTreeStd (appT argsOf CtS ctS_of DescL AllOK LeL LeU DescU UnitsOK
  unitsM mulL mulUnitsE_eq reach_units argsOf_le descL_argsOf allOK_argsOf argsOf_dropLastT
  descL_prefix leL_refl)

/-! ### The map -/

/-- The leading summands with a nonzero subscript. -/
def hiPart : Term → Term
  | nil => nil
  | cons a b t => if a = nil then nil else cons a b (hiPart t)

/-- The summands from the first one with subscript `0` on. -/
def loPart : Term → Term
  | nil => nil
  | cons a b t => if a = nil then cons a b t else loPart t

/-- `ψ_0(h)` is absorbed by the lower part `l`: its first argument is above `h`. -/
def absorbs (h l : Term) : Bool :=
  match l with
  | nil => false
  | cons _ g _ => decide (h < g)

/-- The exponent `X` with `ψ_0(g) = ω^X`, written as a sum of `ψ_0`s. -/
def expoT (g : Term) : Term :=
  if allNilB g then g
  else if absorbs (hiPart g) (loPart g) then loPart g
  else cons nil (hiPart g) (loPart g)

/-- `expoT` on every argument of a sum. -/
def mapArgs : Term → Term
  | nil => nil
  | cons a g t => cons a (expoT g) (mapArgs t)

/-- The digits of the add unit `ψ_0(b)`. -/
def peelE2 (b : Term) : Term := if allNilB b then peelOne b else mapArgs (expoT b)

/-- The body of an add unit. -/
def bodyE2 (b : Term) (x0 y : Nat) : List (List Nat) := [x0, y, 1] :: mulUnitsE x0 y (peelE2 b)

/-- The add units. -/
def addUnitsE2 (rp1 lastX : Nat) (prevZero : Bool) (i : Nat) : Term → List (List Nat)
  | nil => []
  | cons _ b t =>
      if b == nil then
        if prevZero then
          [lastX + 1, i, 0] :: addUnitsE2 rp1 (lastX + 1) true (i + 1) t
        else
          [rp1, i - 1, 0] :: [rp1 + 1, i, 0] :: addUnitsE2 rp1 (rp1 + 1) true (i + 1) t
      else
        ([rp1, i - 1, 0] :: bodyE2 b (rp1 + 1) i) ++ addUnitsE2 (rp1 + 2) (rp1 + 1) false (i + 1) t

/-- **The trio matrix of `ψ_0(Ω_α)`**, new reading and corrected rule 1. -/
def trioE2 (α : Term) : List (List Nat) := addUnitsE2 0 0 false 1 α

/-! ### Pieces of a sum -/

theorem appT_hi_lo : ∀ g : Term, appT (hiPart g) (loPart g) = g
  | nil => rfl
  | cons a b t => by
    by_cases ha : a = nil
    · simp [hiPart, loPart, ha, appT]
    · simp [hiPart, loPart, ha, appT, appT_hi_lo t]

theorem loPart_cases : ∀ g : Term, loPart g = nil ∨ ∃ b t, loPart g = cons nil b t
  | nil => Or.inl rfl
  | cons a b t => by
    by_cases ha : a = nil
    · subst ha; exact Or.inr ⟨b, t, by simp [loPart]⟩
    · simp only [loPart, ha, if_false]; exact loPart_cases t

theorem appT_lt_appT_iff : ∀ (h l l' : Term), appT h l < appT h l' ↔ l < l'
  | nil, _, _ => Iff.rfl
  | cons a b t, l, l' => by
    rw [appT, appT, cons_lt_cons_iff, appT_lt_appT_iff t l l']
    constructor
    · rintro (h | ⟨_, h⟩)
      · exact absurd h (Term.lt_irrefl _)
      · exact h
    · intro h; exact Or.inr ⟨rfl, h⟩

theorem le_appT : ∀ (h l : Term), h ≤ appT h l
  | nil, l => by
    cases l with
    | nil => exact Term.le_refl _
    | cons _ _ _ => exact Term.le_of_lt (nil_lt_cons _ _ _)
  | cons a b t, l => by
    rw [appT]
    rcases Term.le_iff_lt_or_eq.mp (le_appT t l) with h | h
    · exact Term.le_of_lt (cons_lt_cons_iff.mpr (Or.inr ⟨rfl, h⟩))
    · rw [← h]; exact Term.le_refl _

theorem hiPart_le (g : Term) : hiPart g ≤ g := by
  have := le_appT (hiPart g) (loPart g)
  rwa [appT_hi_lo] at this

/-- Every top subscript is `0` or `1`. -/
def TopS : Term → Prop
  | nil => True
  | cons a _ t => (a = nil ∨ a = t1) ∧ TopS t

theorem topS_of_sub01 : ∀ g : Term, Sub01 g → TopS g
  | nil, _ => trivial
  | cons _ _ t, h => ⟨h.1, topS_of_sub01 t h.2.2⟩

/-- **Two sums whose `Ω` parts differ**: the smaller sum is below the larger `Ω` part. -/
theorem lt_hiPart : ∀ x x' : Term, TopS x → TopS x' → x < x' → hiPart x ≠ hiPart x' →
    x < hiPart x'
  | nil, x', _, _, _, hne => by
    cases hx : hiPart x' with
    | nil => rw [hx] at hne; exact absurd rfl hne
    | cons _ _ _ => exact nil_lt_cons _ _ _
  | cons _ _ _, nil, _, _, h, _ => absurd h (not_lt_nil _)
  | cons a b t, cons a' b' t', hs, hs', h, hne => by
    rcases hs.1 with rfl | rfl
    · -- `a = 0`: then `hiPart x = 0`, so `a' = 1`
      rcases hs'.1 with rfl | rfl
      · simp [hiPart] at hne
      · simp only [hiPart, t1, reduceCtorEq, if_false]
        exact cons_lt_cons_iff.mpr (Or.inl (psi_lt_psi_iff.mpr (Or.inl (nil_lt_cons _ _ _))))
    · rcases hs'.1 with rfl | rfl
      · exfalso
        have : cons nil b' t' < cons t1 b t :=
          cons_lt_cons_iff.mpr (Or.inl (psi_lt_psi_iff.mpr (Or.inl (nil_lt_cons _ _ _))))
        exact Term.lt_asymm h this
      · simp only [hiPart, t1, reduceCtorEq, if_false] at hne ⊢
        rcases cons_lt_cons_iff.mp h with h1 | ⟨h1, h2⟩
        · exact cons_lt_cons_iff.mpr (Or.inl h1)
        · injection h1 with _ e; subst e
          have hne' : hiPart t ≠ hiPart t' := fun e => hne (by rw [e])
          exact cons_lt_cons_iff.mpr (Or.inr ⟨rfl, lt_hiPart t t' hs.2 hs'.2 h2 hne'⟩)

/-- The `Ω` part starts with `Ω` when the term does. -/
theorem hiPart_t1 {e u : Term} : hiPart (cons t1 e u) = cons t1 e (hiPart u) := by
  simp [hiPart, t1]

theorem lt_of_lt_of_le' {x y z : Term} (h1 : x < y) (h2 : y ≤ z) : x < z := by
  rcases Term.le_iff_lt_or_eq.mp h2 with h2 | rfl
  · exact Term.lt_trans h1 h2
  · exact h1

theorem lt_of_le_of_lt' {x y z : Term} (h1 : x ≤ y) (h2 : y < z) : x < z := by
  rcases Term.le_iff_lt_or_eq.mp h1 with h1 | rfl
  · exact Term.lt_trans h1 h2
  · exact h2

/-! ### The arguments the reading meets -/

/-- **A good argument of `ψ_0`**: free of `Ω`, or starting with `Ω`, with every
argument of its lower part good and below it. -/
inductive Good : Term → Prop
  | allNil {g : Term} : AllNil g → Good g
  | omega {g : Term} : (∃ e u, g = cons t1 e u) → Sub01 g → TopNil (loPart g) →
      (∀ x ∈ argsOf (loPart g), Good x) → (∀ x ∈ argsOf (loPart g), x < g) → Good g

theorem allNilB_false {g : Term} (h : ¬ AllNil g) : allNilB g = false := by
  cases hb : allNilB g
  · rfl
  · exact absurd ((allNilB_iff g).mp hb) h

theorem not_allNil_of_t1 {g : Term} (h : ∃ e u, g = cons t1 e u) : ¬ AllNil g := by
  obtain ⟨e, u, rfl⟩ := h; exact not_allNil_t1

theorem expoT_allNil {g : Term} (h : AllNil g) : expoT g = g := by
  simp [expoT, (allNilB_iff g).mpr h]

theorem expoT_not {g : Term} (h : ¬ AllNil g) :
    expoT g = if absorbs (hiPart g) (loPart g) then loPart g
      else cons nil (hiPart g) (loPart g) := by
  simp [expoT, allNilB_false h]

/-- The good arguments that are not free of `Ω` start with `Ω`. -/
theorem Good.t1 {g : Term} (hg : Good g) (hA : ¬ AllNil g) : ∃ e u, g = cons t1 e u := by
  cases hg with
  | allNil h => exact absurd h hA
  | omega h _ _ _ _ => exact h

theorem Good.sub01 {g : Term} (hg : Good g) : Sub01 g := by
  cases hg with
  | allNil h => exact sub01_of_allNil g h
  | omega _ h _ _ _ => exact h

/-- The first argument of `expoT g` lies between the `Ω` part and `g`. -/
theorem expoT_head {g : Term} (hg : Good g) (hA : ¬ AllNil g) :
    ∃ f w, expoT g = cons nil f w ∧ hiPart g ≤ f ∧ f ≤ g := by
  cases hg with
  | allNil h => exact absurd h hA
  | omega ht hS hT hG hlt =>
    rw [expoT_not hA]
    rcases loPart_cases g with hl | ⟨b, t, hl⟩
    · simp only [hl, absorbs, Bool.false_eq_true, if_false]
      exact ⟨_, _, rfl, Term.le_refl _, hiPart_le g⟩
    · simp only [hl, absorbs]
      by_cases hab : hiPart g < b
      · simp only [hab, decide_true, if_true]
        refine ⟨b, t, rfl, Term.le_of_lt hab, Term.le_of_lt (hlt b ?_)⟩
        rw [hl]; exact List.mem_cons_self ..
      · simp only [hab, decide_false, Bool.false_eq_true, if_false]
        exact ⟨_, _, rfl, Term.le_refl _, hiPart_le g⟩

/-- A term free of `Ω` is below the `Ω` part of a good argument that is not. -/
theorem allNil_lt_hiPart {y g : Term} (hy : AllNil y) (hg : Good g) (hA : ¬ AllNil g) :
    y < hiPart g := by
  obtain ⟨e, u, rfl⟩ := hg.t1 hA
  rw [hiPart_t1]
  exact allNil_lt_t1head hy

/-- A term free of `Ω` is below `expoT g` for a good `g` that is not. -/
theorem allNil_lt_expoT {y g : Term} (hy : AllNil y) (hg : Good g) (hA : ¬ AllNil g) :
    y < expoT g := by
  obtain ⟨f, w, he, hf, -⟩ := expoT_head hg hA
  rw [he]
  cases y with
  | nil => exact nil_lt_cons _ _ _
  | cons a y1 v =>
    obtain ⟨rfl, hy1, _⟩ := hy
    exact cons_lt_cons_iff.mpr (Or.inl (psi_lt_psi_iff.mpr (Or.inr ⟨rfl,
      lt_of_lt_of_le' (allNil_lt_hiPart hy1 hg hA) hf⟩)))

/-- **`expoT` keeps the order on good arguments.** -/
theorem expoT_lt {x x' : Term} (hx : Good x) (hx' : Good x') (h : x < x') :
    expoT x < expoT x' := by
  by_cases hA : AllNil x <;> by_cases hA' : AllNil x'
  · rw [expoT_allNil hA, expoT_allNil hA']; exact h
  · rw [expoT_allNil hA]; exact allNil_lt_expoT hA hx' hA'
  · exfalso
    obtain ⟨e, u, rfl⟩ := hx.t1 hA
    exact Term.lt_asymm h (allNil_lt_t1head hA')
  · by_cases hh : hiPart x = hiPart x'
    · -- the same `Ω` part: the lower parts decide
      have hl : loPart x < loPart x' := by
        have := h
        rw [← appT_hi_lo x, ← appT_hi_lo x', hh] at this
        exact (appT_lt_appT_iff _ _ _).mp this
      rw [expoT_not hA, expoT_not hA', ← hh]
      rcases loPart_cases x with e1 | ⟨b, t, e1⟩ <;>
        rcases loPart_cases x' with e2 | ⟨b', t', e2⟩
      · rw [e1, e2] at hl; exact absurd hl (Term.lt_irrefl _)
      · rw [e1, e2] at hl ⊢
        simp only [absorbs, Bool.false_eq_true, if_false]
        by_cases hb : hiPart x < b'
        · simp only [hb, decide_true, if_true]
          exact cons_lt_cons_iff.mpr (Or.inl (psi_lt_psi_iff.mpr (Or.inr ⟨rfl, hb⟩)))
        · simp only [hb, decide_false, Bool.false_eq_true, if_false]
          exact cons_lt_cons_iff.mpr (Or.inr ⟨rfl, nil_lt_cons _ _ _⟩)
      · rw [e1, e2] at hl; exact absurd hl (not_lt_nil _)
      · rw [e1, e2] at hl ⊢
        simp only [absorbs]
        by_cases hb : hiPart x < b <;> by_cases hb' : hiPart x < b'
        · simp only [hb, hb', decide_true, if_true]; exact hl
        · exfalso
          rcases cons_lt_cases hl with h1 | ⟨rfl, _⟩
          · exact hb' (Term.lt_trans hb h1)
          · exact hb' hb
        · simp only [hb, hb', decide_true, decide_false, Bool.false_eq_true, if_true, if_false]
          exact cons_lt_cons_iff.mpr (Or.inl (psi_lt_psi_iff.mpr (Or.inr ⟨rfl, hb'⟩)))
        · simp only [hb, hb', decide_false, Bool.false_eq_true, if_false]
          exact cons_lt_cons_iff.mpr (Or.inr ⟨rfl, hl⟩)
    · -- different `Ω` parts: the first arguments decide
      have hlt : x < hiPart x' :=
        lt_hiPart x x' (topS_of_sub01 x hx.sub01) (topS_of_sub01 x' hx'.sub01) h hh
      obtain ⟨f, w, he, _, hf⟩ := expoT_head hx hA
      obtain ⟨f', w', he', hf', _⟩ := expoT_head hx' hA'
      rw [he, he']
      exact cons_lt_cons_iff.mpr (Or.inl (psi_lt_psi_iff.mpr (Or.inr ⟨rfl,
        lt_of_le_of_lt' hf (lt_of_lt_of_le' hlt hf')⟩)))

theorem expoT_le {x x' : Term} (hx : Good x) (hx' : Good x') (h : x ≤ x') :
    expoT x ≤ expoT x' := by
  rcases Term.le_iff_lt_or_eq.mp h with h | rfl
  · exact Term.le_of_lt (expoT_lt hx hx' h)
  · exact Term.le_refl _

/-! ### The digits -/

theorem topNil_mapArgs : ∀ s : Term, TopNil s → TopNil (mapArgs s)
  | nil, _ => trivial
  | cons _ _ t, h => ⟨h.1, topNil_mapArgs t h.2⟩

theorem argsOf_mapArgs : ∀ s : Term, argsOf (mapArgs s) = (argsOf s).map expoT
  | nil => rfl
  | cons _ g t => by rw [mapArgs, argsOf, argsOf, argsOf_mapArgs t, List.map_cons]

/-- **`mapArgs` keeps the order** on sums of `ψ_0`s with good arguments. -/
theorem mapArgs_lt : ∀ s t : Term, TopNil s → TopNil t → (∀ x ∈ argsOf s, Good x) →
    (∀ x ∈ argsOf t, Good x) → s < t → mapArgs s < mapArgs t
  | nil, nil, _, _, _, _, h => absurd h (Term.lt_irrefl _)
  | nil, cons _ _ _, _, _, _, _, _ => nil_lt_cons _ _ _
  | cons _ _ _, nil, _, _, _, _, h => absurd h (not_lt_nil _)
  | cons a g u, cons a' g' u', hs, ht, hG, hG', h => by
    obtain ⟨rfl, hu⟩ := hs
    obtain ⟨rfl, hu'⟩ := ht
    have hg : Good g := hG g (List.mem_cons_self ..)
    have hg' : Good g' := hG' g' (List.mem_cons_self ..)
    rw [mapArgs, mapArgs]
    rcases cons_lt_cases h with h1 | ⟨rfl, h2⟩
    · exact cons_lt_cons_iff.mpr (Or.inl (psi_lt_psi_iff.mpr (Or.inr ⟨rfl, expoT_lt hg hg' h1⟩)))
    · exact cons_lt_cons_iff.mpr (Or.inr ⟨rfl, mapArgs_lt u u' hu hu'
        (fun x hx => hG x (List.mem_cons_of_mem _ hx))
        (fun x hx => hG' x (List.mem_cons_of_mem _ hx)) h2⟩)

theorem sub01_hiPart : ∀ g : Term, Sub01 g → Sub01 (hiPart g)
  | nil, _ => trivial
  | cons a b t, h => by
    by_cases ha : a = nil
    · simp [hiPart, ha]; trivial
    · simp only [hiPart, ha, if_false]; exact ⟨h.1, h.2.1, sub01_hiPart t h.2.2⟩

theorem sub01_loPart : ∀ g : Term, Sub01 g → Sub01 (loPart g)
  | nil, _ => trivial
  | cons a b t, h => by
    by_cases ha : a = nil
    · simp only [loPart, ha, if_true]; subst ha; exact h
    · simp only [loPart, ha, if_false]; exact sub01_loPart t h.2.2

theorem loPart_hiPart : ∀ g : Term, loPart (hiPart g) = nil
  | nil => rfl
  | cons a b t => by
    by_cases ha : a = nil
    · simp [hiPart, ha, loPart]
    · simp [hiPart, ha, loPart, loPart_hiPart t]

theorem hiPart_hiPart : ∀ g : Term, hiPart (hiPart g) = hiPart g
  | nil => rfl
  | cons a b t => by
    by_cases ha : a = nil
    · simp [hiPart, ha]
    · simp [hiPart, ha, hiPart_hiPart t]

/-- The `Ω` part of a good argument is good. -/
theorem good_hiPart {g : Term} (hg : Good g) (hA : ¬ AllNil g) : Good (hiPart g) := by
  obtain ⟨e, u, rfl⟩ := hg.t1 hA
  refine Good.omega ⟨e, hiPart u, hiPart_t1⟩ (sub01_hiPart _ hg.sub01) ?_ ?_ ?_ <;>
    rw [loPart_hiPart]
  · trivial
  · intro x hx; simp [argsOf] at hx
  · intro x hx; simp [argsOf] at hx

theorem expoT_hiPart {g : Term} (hg : Good g) (hA : ¬ AllNil g) :
    expoT (hiPart g) = psi nil (hiPart g) := by
  have hA' : ¬ AllNil (hiPart g) := not_allNil_of_t1 ((good_hiPart hg hA).t1 (by
    obtain ⟨e, u, rfl⟩ := hg.t1 hA; rw [hiPart_t1]; exact not_allNil_t1))
  rw [expoT_not hA', hiPart_hiPart, loPart_hiPart]
  rfl

theorem sub01_expoT {g : Term} (hg : Sub01 g) : Sub01 (expoT g) := by
  unfold expoT
  split
  · exact hg
  · split
    · exact sub01_loPart g hg
    · exact ⟨Or.inl rfl, sub01_hiPart g hg, sub01_loPart g hg⟩

theorem sub01_mapArgs : ∀ s : Term, Sub01 s → Sub01 (mapArgs s)
  | nil, _ => trivial
  | cons _ g t, h => ⟨h.1, sub01_expoT h.2.1, sub01_mapArgs t h.2.2⟩

theorem topNil_expoT {g : Term} (hg : Good g) : TopNil (expoT g) := by
  cases hg with
  | allNil h => rw [expoT_allNil h]; exact topNil_of_allNil _ h
  | omega ht hS hT _ _ =>
    rw [expoT_not (not_allNil_of_t1 ht)]
    split
    · exact hT
    · exact ⟨rfl, hT⟩

theorem mem_argsOf_allNil : ∀ {t : Term}, AllNil t → ∀ x ∈ argsOf t, AllNil x
  | nil, _, x, hx => by simp [argsOf] at hx
  | cons _ g u, h, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.2.1
    · exact mem_argsOf_allNil h.2.2 x hx

/-- The arguments of `expoT g` are good. -/
theorem good_argsOf_expoT {g : Term} (hg : Good g) : ∀ x ∈ argsOf (expoT g), Good x := by
  by_cases hA : AllNil g
  · rw [expoT_allNil hA]
    exact fun x hx => Good.allNil (mem_argsOf_allNil hA x hx)
  · have hg' := hg
    cases hg' with
    | allNil h => exact absurd h hA
    | omega ht hS hT hG _ =>
      rw [expoT_not hA]
      split
      · exact hG
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact good_hiPart hg hA
        · exact hG x hx

theorem topNil_peelE2 {b : Term} (hb : Good b) : TopNil (peelE2 b) := by
  unfold peelE2
  split
  · rename_i h
    exact topNil_of_allNil _ (allNil_peelOne b ((allNilB_iff b).mp h))
  · exact topNil_mapArgs _ (topNil_expoT hb)

theorem sub01_peelE2 {b : Term} (hb : Sub01 b) : Sub01 (peelE2 b) := by
  unfold peelE2
  split
  · rename_i h
    exact sub01_of_allNil _ (allNil_peelOne b ((allNilB_iff b).mp h))
  · exact sub01_mapArgs _ (sub01_expoT hb)

theorem peelE2_of_allNil {b : Term} (h : AllNil b) : peelE2 b = peelOne b := by
  simp [peelE2, (allNilB_iff b).mpr h]

theorem peelE2_of_not {b : Term} (h : ¬ AllNil b) : peelE2 b = mapArgs (expoT b) := by
  simp [peelE2, allNilB_false h]

/-- **`peelE2` keeps the order** on good arguments. -/
theorem peelE2_lt {b b' : Term} (hb : Good b) (hb' : Good b') (hne : b ≠ nil) (h : b < b') :
    peelE2 b < peelE2 b' := by
  by_cases hA : AllNil b <;> by_cases hA' : AllNil b'
  · rw [peelE2_of_allNil hA, peelE2_of_allNil hA']; exact peelOne_lt hA hA' hne h
  · rw [peelE2_of_allNil hA, peelE2_of_not hA']
    obtain ⟨f', w', he', hf', _⟩ := expoT_head hb' hA'
    have hgf : Good f' := good_argsOf_expoT hb' f' (by rw [he']; exact List.mem_cons_self ..)
    have hAf : ¬ AllNil f' := fun hf => by
      have := lt_of_lt_of_le' (allNil_lt_hiPart hf hb' hA') hf'
      exact Term.lt_irrefl _ this
    rw [he', mapArgs]
    have hp := allNil_peelOne b hA
    cases hq : peelOne b with
    | nil => exact nil_lt_cons _ _ _
    | cons a y v =>
      rw [hq] at hp
      obtain ⟨rfl, hy, _⟩ := hp
      exact cons_lt_cons_iff.mpr (Or.inl (psi_lt_psi_iff.mpr (Or.inr ⟨rfl,
        allNil_lt_expoT hy hgf hAf⟩)))
  · exfalso
    obtain ⟨e, u, rfl⟩ := hb.t1 hA
    exact Term.lt_asymm h (allNil_lt_t1head hA')
  · rw [peelE2_of_not hA, peelE2_of_not hA']
    exact mapArgs_lt _ _ (topNil_expoT hb) (topNil_expoT hb') (good_argsOf_expoT hb)
      (good_argsOf_expoT hb') (expoT_lt hb hb' h)

/-! ### Standard arguments are good -/

theorem nil_le (c : Term) : nil ≤ c := by
  cases c with
  | nil => exact Term.le_refl _
  | cons _ _ _ => exact Term.le_of_lt (nil_lt_cons _ _ _)

theorem argsOf_mem_G : ∀ (s x : Term), x ∈ argsOf s → x ∈ G nil s
  | nil, x, hx => by simp [argsOf] at hx
  | cons a g u, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact G_mem_cons_arg (nil_le a)
    · exact G_mem_cons_tail (argsOf_mem_G u x hx)

theorem argsOf_loPart_sub : ∀ (s x : Term), x ∈ argsOf (loPart s) → x ∈ argsOf s
  | nil, x, hx => hx
  | cons a g u, x, hx => by
    by_cases ha : a = nil
    · simp only [loPart, ha, if_true] at hx; subst ha; exact hx
    · simp only [loPart, ha, if_false] at hx
      exact List.mem_cons_of_mem _ (argsOf_loPart_sub u x hx)

theorem OT_loPart : ∀ s : Term, OT s → OT (loPart s)
  | nil, h => h
  | cons a g u, h => by
    by_cases ha : a = nil
    · simp only [loPart, ha, if_true]; subst ha; exact h
    · simp only [loPart, ha, if_false]; exact OT_loPart u (OT_tail h)

theorem topNil_loPart : ∀ s : Term, OT s → TopNil (loPart s)
  | nil, _ => trivial
  | cons a g u, h => by
    by_cases ha : a = nil
    · simp only [loPart, ha, if_true]; subst ha; exact topNil_of_OT _ h g u rfl
    · simp only [loPart, ha, if_false]; exact topNil_loPart u (OT_tail h)

/-- The arguments of a standard sum, in the fragment, of a summand `ψ_0(x)`. -/
def argsNil : Term → List Term
  | nil => []
  | cons a g u => (if a = nil then [g] else []) ++ argsNil u

/-- Every argument of a sum of `ψ_0`s is an `argsNil` one. -/
theorem argsOf_argsNil : ∀ t : Term, TopNil t → ∀ y ∈ argsOf t, y ∈ argsNil t
  | nil, _, y, hy => by simp [argsOf] at hy
  | cons c d w, ht, y, hy => by
    obtain ⟨rfl, hw⟩ := ht
    simp only [argsNil, if_true, List.singleton_append]
    rcases List.mem_cons.mp hy with rfl | hy
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (argsOf_argsNil w hw y hy)

theorem argsOf_loPart_nil : ∀ (s x : Term), TopNil (loPart s) → x ∈ argsOf (loPart s) →
    x ∈ argsNil s
  | nil, x, _, hx => by simp [argsOf, loPart] at hx
  | cons a g u, x, hT, hx => by
    by_cases ha : a = nil
    · subst ha
      simp only [loPart, if_true] at hx hT
      exact argsOf_argsNil _ hT x hx
    · simp only [loPart, ha, if_false] at hx hT
      simp only [argsNil, ha, if_false, List.nil_append]
      exact argsOf_loPart_nil u x hT hx

/-- **Every argument of `ψ_0` in a standard term of the fragment is good.** -/
theorem good_of_OT : ∀ s : Term, OT s → Sub01 s → ∀ x ∈ argsNil s, Good x
  | nil, _, _, x, hx => by simp [argsNil] at hx
  | cons a b t, hOT, hS, x, hx => by
    simp only [argsNil, List.mem_append] at hx
    rcases hx with hx | hx
    · by_cases ha : a = nil
      · subst ha
        simp only [if_true, List.mem_singleton] at hx
        rw [hx]
        rcases argOK_of_OT hOT hS.2.1 with hA | ⟨e, u, he⟩
        · exact Good.allNil hA
        · have hOTx : OT b := OT_snd hOT
          have hT := topNil_loPart b hOTx
          refine Good.omega ⟨e, u, he⟩ hS.2.1 hT ?_ ?_
          · intro y hy
            exact good_of_OT b hOTx hS.2.1 y (argsOf_loPart_nil b y hT hy)
          · intro y hy
            have hG := argsOf_mem_G b y (argsOf_loPart_sub b y hy)
            have hall : (G nil b).all (fun z => decide (z < b)) = true := by
              simp only [OT, isOT, Bool.and_eq_true] at hOT
              exact hOT.1.1.2
            exact of_decide_eq_true (List.all_eq_true.mp hall _ hG)
      · simp [ha] at hx
    · exact good_of_OT t (OT_tail hOT) hS.2.2 x hx
termination_by s _ _ _ _ => size s
decreasing_by
  all_goals simp_wf
  all_goals omega

theorem good_of_OT_cons {b t : Term} (hOT : OT (cons nil b t)) (hS : Sub01 (cons nil b t)) :
    Good b :=
  good_of_OT _ hOT hS b (by simp [argsNil])


/-! ### Add units keep the order -/

/-- A countable term of the fragment with good arguments. -/
def Frag2 : Term → Prop
  | nil => True
  | cons a b t => a = nil ∧ Sub01 b ∧ Good b ∧ Frag2 t

theorem addUnitsE2_cons (rp1 lastX : Nat) (pz : Bool) (i : Nat) (a b t : Term) :
    ∃ c r, addUnitsE2 rp1 lastX pz i (cons a b t) = c :: r := by
  rw [addUnitsE2]
  split
  · split
    · exact ⟨_, _, rfl⟩
    · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, by rw [List.cons_append]⟩

theorem addUnitsE2_head_false (rp1 lastX i : Nat) (t : Term) :
    ∀ d ∈ (addUnitsE2 rp1 lastX false i t).head?, d = [rp1, i - 1, 0] := by
  intro d hd
  cases t with
  | nil => rw [addUnitsE2] at hd; exact absurd hd (by simp)
  | cons a b u =>
    rw [addUnitsE2] at hd
    split at hd
    · simp only [Bool.false_eq_true, if_false, List.head?_cons, Option.mem_def,
        Option.some.injEq] at hd
      exact hd.symm
    · simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hd
      exact hd.symm

/-- **The add units keep the order.** -/
theorem addUnitsE2_lt : ∀ α β : Term, Frag2 α → Frag2 β → DescTop β → α < β →
    ∀ (rp1 lastX : Nat) (pz : Bool) (i : Nat), (pz = true → HeadArgNil β) →
      addUnitsE2 rp1 lastX pz i α < addUnitsE2 rp1 lastX pz i β
  | nil, nil, _, _, _, h, _, _, _, _, _ => absurd h (Term.lt_irrefl _)
  | nil, cons a b t, _, _, _, _, rp1, lastX, pz, i, _ => by
    obtain ⟨c, r, hcr⟩ := addUnitsE2_cons rp1 lastX pz i a b t
    rw [hcr, addUnitsE2]
    exact List.nil_lt_cons _ _
  | cons _ _ _, nil, _, _, _, h, _, _, _, _, _ => absurd h (not_lt_nil _)
  | cons a b t, cons a' b' t', hα, hβ, hd, h, rp1, lastX, pz, i, hpz => by
    obtain ⟨rfl, hbS, hbG, ht⟩ := hα
    obtain ⟨rfl, hbS', hbG', ht'⟩ := hβ
    rcases cons_lt_cases h with h | ⟨rfl, h2⟩
    · have hb'ne : b' ≠ nil := ne_nil_of_lt h
      have hpz' : pz = false := by
        cases pz with
        | false => rfl
        | true => exact absurd (hpz rfl) hb'ne
      subst hpz'
      rw [addUnitsE2, addUnitsE2, if_neg (fun h => hb'ne (beq_iff_eq.mp h))]
      by_cases hbn : b = nil
      · subst hbn
        rw [if_pos (beq_self_eq_true nil), if_neg Bool.false_ne_true, List.cons_append, bodyE2,
          List.cons_append]
        refine List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, List.cons_lt_cons_iff.mpr (Or.inl ?_)⟩)
        exact col_lt (Or.inr ⟨rfl, Or.inr ⟨rfl, by omega⟩⟩)
      · rw [if_neg (fun h => hbn (beq_iff_eq.mp h)), List.cons_append, List.cons_append, bodyE2,
          bodyE2, List.cons_append, List.cons_append]
        refine List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, List.cons_lt_cons_iff.mpr
          (Or.inr ⟨rfl, ?_⟩)⟩)
        refine mulUnitsE_lt (rp1 + 1) i _ _ (topNil_peelE2 hbG) (topNil_peelE2 hbG')
          (sub01_peelE2 hbS) (sub01_peelE2 hbS') (peelE2_lt hbG hbG' hbn h) _ _ ?_
        intro d hd
        rw [addUnitsE2_head_false _ _ _ t d hd]
        exact col_lt (Or.inr ⟨by omega, Or.inr ⟨by omega, by omega⟩⟩)
    · obtain ⟨hle, hdt⟩ := hd
      rw [addUnitsE2, addUnitsE2]
      by_cases hbn : b = nil
      · subst hbn
        have hnext : HeadArgNil t' := headArgNil_of_headLe hle
        rw [if_pos (beq_self_eq_true nil), if_pos (beq_self_eq_true nil)]
        cases pz with
        | true =>
          rw [if_pos rfl, if_pos rfl]
          exact List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl,
            addUnitsE2_lt t t' ht ht' hdt h2 _ _ _ _ (fun _ => hnext)⟩)
        | false =>
          rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
          exact List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, List.cons_lt_cons_iff.mpr
            (Or.inr ⟨rfl, addUnitsE2_lt t t' ht ht' hdt h2 _ _ _ _ (fun _ => hnext)⟩)⟩)
      · rw [if_neg (fun h => hbn (beq_iff_eq.mp h)), if_neg (fun h => hbn (beq_iff_eq.mp h))]
        exact append_lt_append_left _
          (addUnitsE2_lt t t' ht ht' hdt h2 _ _ _ _ (fun h => absurd h Bool.false_ne_true))

theorem frag2_of_OT : ∀ α : Term, OT α → TopNil α → Sub01 α → Frag2 α
  | nil, _, _, _ => trivial
  | cons a b t, hOT, hT, hS => by
    obtain ⟨rfl, hTt⟩ := hT
    exact ⟨rfl, hS.2.1, good_of_OT_cons hOT hS, frag2_of_OT t (OT_tail hOT) hTt hS.2.2⟩

/-- **`trioE2` keeps the order** on the standard countable terms with subscripts
`0`/`1`. -/
theorem trioE2_lt_of_OT {α β : Term} (hα : OT α) (hβ : OT β) (hαc : α < tW) (hβc : β < tW)
    (sα : Sub01 α) (sβ : Sub01 β) (h : α < β) : trioE2 α < trioE2 β :=
  addUnitsE2_lt α β (frag2_of_OT α hα (topNil_of_lt_tW hα hαc) sα)
    (frag2_of_OT β hβ (topNil_of_lt_tW hβ hβc) sβ)
    (descTop_of_OT' β hβ (topNil_of_lt_tW hβ hβc)) h 0 0 false 1
    (fun h => absurd h Bool.false_ne_true)

/-- **And reflects it.** -/
theorem trioE2_lt_iff {α β : Term} (hα : OT α) (hβ : OT β) (hαc : α < tW) (hβc : β < tW)
    (sα : Sub01 α) (sβ : Sub01 β) : trioE2 α < trioE2 β ↔ α < β := by
  refine ⟨fun h => ?_, trioE2_lt_of_OT hα hβ hαc hβc sα sβ⟩
  rcases Term.lt_trichotomy α β with h' | h' | h'
  · exact h'
  · rw [h'] at h; exact absurd h (_root_.lt_irrefl _)
  · exact absurd (trioE2_lt_of_OT hβ hα hβc hαc sβ sα h') (_root_.lt_asymm h)

/-- **So it is injective.** -/
theorem trioE2_injective {α β : Term} (hα : OT α) (hβ : OT β) (hαc : α < tW) (hβc : β < tW)
    (sα : Sub01 α) (sβ : Sub01 β) (h : trioE2 α = trioE2 β) : α = β := by
  rcases Term.lt_trichotomy α β with h' | h' | h'
  · have := trioE2_lt_of_OT hα hβ hαc hβc sα sβ h'
    rw [h] at this; exact absurd this (_root_.lt_irrefl _)
  · exact h'
  · have := trioE2_lt_of_OT hβ hα hβc hαc sβ sα h'
    rw [h] at this; exact absurd this (_root_.lt_irrefl _)

/-! ### Standard forms -/

theorem G_appT (a : Term) : ∀ s v : Term, G a (appT s v) = G a s ++ G a v
  | nil, v => rfl
  | cons c d t, v => by
    rw [appT, G_cons, G_cons, G_appT a t v, List.append_assoc]

theorem OT_appT_left : ∀ s v : Term, OT (appT s v) → OT s
  | nil, _, _ => rfl
  | cons a b t, v, h => by
    rw [appT] at h
    refine OT_cons_of (OT_head h) (OT_appT_left t v (OT_tail h)) ?_
    cases t with
    | nil => trivial
    | cons c d w => exact OT_tail_head_le h

/-- Below `appT h l` and smaller than `h`: below `h`. -/
theorem lt_of_lt_appT : ∀ (h l x : Term), x < appT h l → size x < size h → x < h
  | nil, _, x, _, hs => absurd hs (by simp)
  | cons a b t, l, x, hx, hs => by
    rw [appT] at hx
    cases x with
    | nil => exact nil_lt_cons _ _ _
    | cons c d w =>
      rcases cons_lt_cons_iff.mp hx with h1 | ⟨h1, h2⟩
      · exact cons_lt_cons_iff.mpr (Or.inl h1)
      · injection h1 with e1 e2; subst e1 e2
        simp only [size_cons] at hs
        exact cons_lt_cons_iff.mpr (Or.inr ⟨rfl, lt_of_lt_appT t l w h2 (by omega)⟩)

/-- **The `Ω` part of a standard argument of `ψ_0` is again one.** -/
theorem OT_psi_hiPart {g : Term} (hOT : OT (psi nil g)) : OT (psi nil (hiPart g)) := by
  have hOTg : OT g := OT_snd hOT
  have hh : OT (hiPart g) := by
    have := hOTg; rw [← appT_hi_lo g] at this; exact OT_appT_left _ _ this
  have hall : (G nil g).all (fun z => decide (z < g)) = true := by
    simp only [OT, isOT, Bool.and_eq_true] at hOT
    exact hOT.1.1.2
  show isOT (cons nil (hiPart g) nil) = true
  simp only [isOT, Bool.and_eq_true, descHead, head?]
  refine ⟨⟨⟨⟨trivial, hh⟩, ?_⟩, trivial⟩, trivial⟩
  refine List.all_eq_true.mpr (fun x hx => decide_eq_true ?_)
  have hxg : x < g := by
    have hx' : x ∈ G nil g := by
      rw [← appT_hi_lo g, G_appT]; exact List.mem_append_left _ hx
    exact of_decide_eq_true (List.all_eq_true.mp hall x hx')
  rw [← appT_hi_lo g] at hxg
  exact lt_of_lt_appT _ _ x hxg (size_lt_of_mem_G nil _ x hx)

theorem psi_le_psi_of_le {a b c : Term} (h : b ≤ c) : psi a b ≤ psi a c := by
  rcases Term.le_iff_lt_or_eq.mp h with h | rfl
  · exact Term.le_of_lt (psi_lt_psi_iff.mpr (Or.inr ⟨rfl, h⟩))
  · exact Term.le_refl _

theorem not_lt_iff_le {x y : Term} : ¬ x < y ↔ y ≤ x := by
  constructor
  · intro h
    rcases Term.lt_trichotomy x y with h' | h' | h'
    · exact absurd h' h
    · rw [h']; exact Term.le_refl _
    · exact Term.le_of_lt h'
  · intro h h'; exact Term.not_le_of_lt h' h

/-- **`expoT g` is a standard form** for a standard `ψ_0(g)` of the fragment. -/
theorem OT_expoT {g : Term} (hOT : OT (psi nil g)) (hg : Good g) : OT (expoT g) := by
  by_cases hA : AllNil g
  · rw [expoT_allNil hA]; exact OT_snd hOT
  · rw [expoT_not hA]
    have hl := OT_loPart g (OT_snd hOT)
    rcases loPart_cases g with e | ⟨b, t, e⟩
    · simp only [e, absorbs, Bool.false_eq_true, if_false]
      exact OT_cons_of (OT_psi_hiPart hOT) rfl trivial
    · simp only [e, absorbs]
      by_cases hb : hiPart g < b
      · simp only [hb, decide_true, if_true]; rw [← e]; exact hl
      · simp only [hb, decide_false, Bool.false_eq_true, if_false]
        rw [e] at hl
        exact OT_cons_of (OT_psi_hiPart hOT) hl (psi_le_psi_of_le (not_lt_iff_le.mp hb))

theorem OT_psi_of_argsOf : ∀ s : Term, OT s → TopNil s → ∀ x ∈ argsOf s, OT (psi nil x)
  | nil, _, _, x, hx => by simp [argsOf] at hx
  | cons a g u, hOT, hT, x, hx => by
    obtain ⟨rfl, hu⟩ := hT
    rcases List.mem_cons.mp hx with rfl | hx
    · exact OT_head hOT
    · exact OT_psi_of_argsOf u (OT_tail hOT) hu x hx

theorem descL_map_expoT : ∀ L : List Term, DescL L → (∀ x ∈ L, Good x) → DescL (L.map expoT)
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | a :: b :: l, h, hG => by
    refine ⟨expoT_le (hG b (by simp)) (hG a (by simp)) h.1, ?_⟩
    have := descL_map_expoT (b :: l) h.2 (fun x hx => hG x (List.mem_cons_of_mem _ hx))
    simpa using this

/-- The units of `trioE2 α`. -/
def dataOf2 : Term → List (Option (List Term))
  | nil => []
  | cons _ b t => (if b == nil then none else some (argsOf (peelE2 b))) :: dataOf2 t

theorem addUnitsE2_eq : ∀ (α : Term) (rp1 lastX : Nat) (pz : Bool) (i : Nat),
    addUnitsE2 rp1 lastX pz i α = unitsM rp1 lastX pz i (dataOf2 α)
  | nil, _, _, _, _ => rfl
  | cons a b t, rp1, lastX, pz, i => by
    rw [addUnitsE2, dataOf2]
    by_cases hb : b = nil
    · subst hb
      simp only [beq_self_eq_true, if_true, unitsM]
      split <;> rw [addUnitsE2_eq t]
    · have hb' : (b == nil) = false := by simpa using hb
      simp only [hb', Bool.false_eq_true, if_false, unitsM]
      rw [addUnitsE2_eq t, bodyE2, mulUnitsE_eq]
      rfl

theorem trioE2_eq (α : Term) : trioE2 α = unitsM 0 0 false 1 (dataOf2 α) :=
  addUnitsE2_eq α 0 0 false 1

theorem unitOK2_of {b t : Term} (hOT : OT (cons nil b t)) (hS : Sub01 (cons nil b t)) :
    AllOK (argsOf (peelE2 b)) ∧ DescL (argsOf (peelE2 b)) := by
  have hOTb : OT b := OT_snd hOT
  have hG : Good b := good_of_OT_cons hOT hS
  by_cases hA : AllNil b
  · rw [peelE2_of_allNil hA]
    have hT : TopNil b := topNil_of_allNil b hA
    have hC : ∀ g ∈ argsOf b, CtS g := fun g hg =>
      Googology.Trans.BMS.TrioTreeStd.ctS_of_allNil g (mem_argsOf_allNil hA g hg)
    have hOKb := allOK_argsOf b hOTb hC
    have hDb := descL_argsOf b hOTb hT
    unfold peelOne
    split
    · obtain ⟨R, hR⟩ := argsOf_dropLastT b
      refine ⟨fun γ hγ => hOKb γ (by rw [hR]; exact List.mem_append_left _ hγ), ?_⟩
      rw [hR] at hDb; exact descL_prefix _ _ hDb
    · exact ⟨hOKb, hDb⟩
  · rw [peelE2_of_not hA, argsOf_mapArgs]
    have hl := OT_loPart b hOTb
    have hTl := topNil_loPart b hOTb
    -- the arguments of `expoT b`: standard, good, descending
    have hargs : (∀ x ∈ argsOf (expoT b), OT (psi nil x) ∧ Good x) ∧ DescL (argsOf (expoT b)) := by
      have hlo : ∀ x ∈ argsOf (loPart b), OT (psi nil x) ∧ Good x := fun x hx =>
        ⟨OT_psi_of_argsOf _ hl hTl x hx, good_argsOf_expoT hG x (by
          rw [expoT_not hA]; split
          · exact hx
          · exact List.mem_cons_of_mem _ hx)⟩
      rw [expoT_not hA]
      split
      · exact ⟨hlo, descL_argsOf _ hl hTl⟩
      · rename_i hab
        refine ⟨fun x hx => ?_, ?_⟩
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨OT_psi_hiPart (OT_head hOT), good_hiPart hG hA⟩
          · exact hlo x hx
        · rcases loPart_cases b with e | ⟨g1, w, e⟩
          · rw [e]; trivial
          · rw [e] at hab hl hTl ⊢
            simp only [absorbs, decide_eq_true_eq] at hab
            refine ⟨not_lt_iff_le.mp hab, ?_⟩
            exact descL_argsOf _ hl hTl
    refine ⟨fun γ hγ => ?_, descL_map_expoT _ hargs.2 (fun x hx => (hargs.1 x hx).2)⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hγ
    obtain ⟨h1, h2⟩ := hargs.1 x hx
    exact ⟨OT_expoT h1 h2, ctS_of _ (topNil_expoT h2) (sub01_expoT h2.sub01)⟩

theorem unitsOK_dataOf2 : ∀ α : Term, OT α → CtS α → UnitsOK (dataOf2 α)
  | nil, _, _ => by intro L h; simp [dataOf2] at h
  | cons a b t, hOT, hC => by
    obtain ⟨rfl, hb, ht⟩ := hC
    intro L hL
    rw [dataOf2] at hL
    rcases List.mem_cons.mp hL with h | h
    · by_cases hb0 : b = nil
      · subst hb0; simp at h
      · have hb' : (b == nil) = false := by simpa using hb0
        rw [hb'] at h
        simp only [Bool.false_eq_true, if_false, Option.some.injEq] at h
        subst h
        exact unitOK2_of hOT ⟨Or.inl rfl, hb, Googology.Trans.BMS.TrioTreeStd.sub01_of_ctS t ht⟩
    · exact unitsOK_dataOf2 t (OT_tail hOT) ht L h

theorem descU_dataOf2 : ∀ α : Term, OT α → CtS α → DescU (dataOf2 α)
  | nil, _, _ => trivial
  | cons a b nil, _, _ => trivial
  | cons a b (cons c b' w), hOT, hC => by
    obtain ⟨rfl, hb, rfl, hb', hw⟩ := hC
    refine ⟨?_, descU_dataOf2 _ (OT_tail hOT) ⟨rfl, hb', hw⟩⟩
    have hle : b' ≤ b := psi_le_psi_nil (OT_tail_head_le hOT)
    show LeU (if b' == nil then none else some (argsOf (peelE2 b')))
      (if b == nil then none else some (argsOf (peelE2 b)))
    by_cases hb0' : b' = nil
    · subst hb0'; simp [LeU]
    · have hb0 : b ≠ nil := fun e => by subst e; exact hb0' (eq_nil_of_le_nil' hle)
      have e1 : (b' == nil) = false := by simpa using hb0'
      have e2 : (b == nil) = false := by simpa using hb0
      simp only [e1, e2, Bool.false_eq_true, if_false, LeU]
      have hS : Sub01 (cons nil b (cons nil b' w)) :=
        Googology.Trans.BMS.TrioTreeStd.sub01_of_ctS _ ⟨rfl, hb, rfl, hb', hw⟩
      have hG := good_of_OT_cons hOT hS
      have hG' := good_of_OT_cons (OT_tail hOT) hS.2.2
      refine argsOf_le _ _ (topNil_peelE2 hG') (topNil_peelE2 hG) ?_
      rcases Term.le_iff_lt_or_eq.mp hle with h | rfl
      · exact Term.le_of_lt (peelE2_lt hG' hG hb0' h)
      · exact Term.le_refl _

/-- **The matrix `trioE2 α` is a standard form** for every standard countable `α`
whose subscripts are all `0` or `1`. -/
theorem trioE2_std {α : Term} (hOT : OT α) (hc : α < tW) (hS : Sub01 α) :
    ∃ A : BM4.Arr 3, Pat.Std 3 A ∧ Googology.Trans.BMS.entriesR A = trioE2 α := by
  have hC : CtS α := ctS_of α (topNil_of_lt_tW hOT hc) hS
  rw [trioE2_eq]
  exact reach_units _ (descU_dataOf2 α hOT hC) (unitsOK_dataOf2 α hOT hC)


/-! ### Calibration against the program -/

open Googology.Trans.BMS.TrioFixStrip (trioMatrixLSt)
open Googology.Trans.BMS.TrioFixOfTerm (tα tβ)

-- The program computes `trioE2` on every standard countable term with at most 7 `ψ`s
-- and subscripts `0`/`1`.
#guard (smallFrag 7).length = 2398
#guard (smallFrag 7).all fun a => trioE2 a == trioMatrixLSt a

-- The two terms of `TrioFixOfTerm.trioMatrixLFix_order_fails`.
theorem trioE2_tα : trioE2 tα = trioMatrixLSt tα := by decide +kernel
theorem trioE2_tβ : trioE2 tβ = trioMatrixLSt tβ := by decide +kernel

/-! ### The open step, and what follows from it -/

/-- **Open (not proved)**: the program computes `trioE2` on the standard countable
terms with subscripts `0`/`1`.  Checked by `#guard` above on `smallFrag 7` (2,398
terms); proved by `decide` for `tα`, `tβ`. -/
def CalibSt : Prop :=
  ∀ α : Term, OT α → α < tW → Sub01 α → trioMatrixLSt α = trioE2 α

/-- **Order of the patched map, given `CalibSt`.** -/
theorem trioMatrixLSt_lt_iff_of_calib (hC : CalibSt) {α β : Term} (hα : OT α) (hβ : OT β)
    (hαc : α < tW) (hβc : β < tW) (sα : Sub01 α) (sβ : Sub01 β) :
    trioMatrixLSt α < trioMatrixLSt β ↔ α < β := by
  rw [hC α hα hαc sα, hC β hβ hβc sβ]
  exact trioE2_lt_iff hα hβ hαc hβc sα sβ

/-- **Standard forms of the patched map, given `CalibSt`.** -/
theorem trioMatrixLSt_std_of_calib (hC : CalibSt) {α : Term} (hOT : OT α) (hc : α < tW)
    (hS : Sub01 α) :
    ∃ A : BM4.Arr 3, Pat.Std 3 A ∧ Googology.Trans.BMS.entriesR A = trioMatrixLSt α := by
  rw [hC α hOT hc hS]
  exact trioE2_std hOT hc hS

#print axioms trioE2_lt_iff
#print axioms trioE2_injective
#print axioms trioE2_std
#print axioms trioE2_tβ
#print axioms trioMatrixLSt_lt_iff_of_calib
#print axioms trioMatrixLSt_std_of_calib
#print axioms Googology.Trans.BMS.TrioFixStrip.trioMatrixLSt_tα_lt_tβ
#print axioms Googology.Trans.BMS.TrioFixStrip.stripSt_eq_strip
#print axioms Googology.Trans.BMS.TrioFixStrip.uncollapses_eq

end Googology.Trans.BMS.TrioFixStripTree

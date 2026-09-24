import Googology.Trans.BMS.TrioFixStripTree
import Googology.Trans.BMS.TrioFixFuel

/-!
# The reading `ofTermFix` on the fragment, with the fuel it needs

`TrioFixOfTerm.ofTermFix` reads a term into the rules' normal form.  It groups equal
summands and absorbs a smaller summand into a larger one with `add`, whose comparison
`cmpExp` has a fuel of `200`.  This file proves that on the standard terms whose subscripts
are `0`/`1` and whose reading is not too deep (`Rd`: `rdT x ≤ 100`), the reading is what the
term says:

* `read_cons`: `ofTermFix (ψ_a(b) + t) = add [(sx a b, 1)] (ofTermFix t)`, with the one
  exponent `sx a b` of the summand, written out on the fragment in `sx_cases`;
* `inv_all`: the reading groups the summands (`Inv`: `ofTermFix x` is the run-length code of
  the summands of `x`, each summand `ψ_a(b)` written `ω^{sx a b}`);
* `ki_all`: `ato (sx a b) = ofTermFix (ext a b)`: the exponent of `ψ_0(b)` is the reading of
  `expoT b` (`TrioFixStripTree`), that of `ψ_1(d)` the reading of `Ω + d` (`omx d`,
  `d` itself when `Ω` is absorbed);
* `cmp_read`: `cmpF n (ofTermFix x) (ofTermFix y) = Term.cmp x y` as soon as
  `n ≥ odDep (ofTermFix x) + odDep (ofTermFix y)` (the nesting depths of the two readings).

**The fuel.**  The comparison of two readings goes down both of them; each level costs one
unit of fuel.  The bound proved here asks for the **sum** of the two depths: when one side
is a `ψ` atom and the other an `ω`-power, the program wraps the atom in a list and loses one
level on that side only.  The reading compares only summands of the term it reads, whose
depths are at most `rdT` of the term, so `rdT x ≤ 100` is enough for the fuel `200`.
`rdT` is an upper bound of the nesting depth of the reading (`odDep_read_le`), at most twice
the nesting depth `dep` of the term.  It is not the exact threshold: the program agrees with
the tree map on some deeper terms too (see `TrioFixStripCalibNo.lean`).
-/

namespace Googology.Trans.BMS.TrioFixStripCalib

open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term
open Googology.Trans.BMS (AllNil)
open Googology.Trans.BMS.TrioRules
open Googology.Trans.BMS.TrioFixOfTerm (ofTermFix partsFix summandFix psiAtom finSub
  add_nil_left add_nil_right add_ne_nil)
open Googology.Trans.BMS.TrioTree (Sub01 TopNil allNilB allNilB_iff sub01_of_allNil
  topNil_of_allNil allNil_lt_t1head not_allNil_t1)
open Googology.Trans.BMS.TrioTreeStd (appT size_appT appT_nil_right)
open Googology.Trans.BMS.TrioFixStripTree (hiPart loPart absorbs expoT TopS topS_of_sub01 Good
  appT_hi_lo loPart_cases expoT_allNil expoT_not expoT_lt good_of_OT_cons OT_expoT sub01_expoT
  sub01_hiPart sub01_loPart loPart_hiPart hiPart_hiPart OT_psi_hiPart OT_loPart topNil_loPart
  topNil_expoT hiPart_t1 OT_appT_left)
open Googology.Trans.BMS.TrioTreeRules (sums pcmp lexS pcmp_def cmp_sums expandG2 GDesc2
  GDesc2_tail GDesc2_pos GDesc2_head_pos GDesc2_next mem_expandG2 pcmp_self pcmp_swap lexS_rep
  GDesc2_bump)
open Googology.Trans.BMS.TrioRulesE0 (cmpOrdWith_nil_nil cmpOrdWith_nil_cons cmpOrdWith_cons_nil
  cmpOrdWith_cons cmpF_nil_nil add_gt add_eq)
open Googology.Trans.BMS.TrioFixFuel (exDep odDep)

/-! ### The reading, summand by summand -/

/-- The one exponent `summandFix` writes. -/
def sEx (c0 : Bool) (cf hi lo : Od) : Ex :=
  if lo.isEmpty then (if hi.isEmpty then (if c0 then .o [] else .W cf) else psiAtom cf hi)
  else .o (add (if hi.isEmpty then (if c0 then [] else [(.W cf, 1)]) else [(psiAtom cf hi, 1)]) lo)

theorem summandFix_eq (c0 : Bool) (cf hi lo : Od) :
    summandFix c0 cf hi lo = [(sEx c0 cf hi lo, 1)] := by
  unfold summandFix sEx
  cases hl : lo.isEmpty <;> cases hh : hi.isEmpty <;> cases c0 <;> simp [one, nat, wpow]

theorem partsFix_fst : ∀ (x a : Term), (partsFix x a).1 = (partsFix x nil).1
  | nil, _ => rfl
  | cons c d u, a => by
    simp only [partsFix]
    rw [partsFix_fst u a]

/-- **The exponent of the summand `ψ_a(b)`** in the reading. -/
def sx (a b : Term) : Ex :=
  sEx (a == nil) (ofTermFix a) (partsFix b a).2.1 (partsFix b a).2.2

theorem read_nil : ofTermFix nil = [] := rfl

theorem read_cons (a b t : Term) : ofTermFix (cons a b t) = add [(sx a b, 1)] (ofTermFix t) := by
  show (partsFix (cons a b t) nil).1 = _
  simp only [partsFix, summandFix_eq]
  rfl

theorem read_psi (a b : Term) : ofTermFix (psi a b) = [(sx a b, 1)] := by
  rw [read_cons, read_nil, add_nil_right]

theorem read_ne_nil (a b t : Term) : ofTermFix (cons a b t) ≠ [] := by
  rw [read_cons]
  cases h : ofTermFix t with
  | nil => simp [add_nil_right]
  | cons y ys => exact add_ne_nil _ (by simp)

theorem read_eq_nil_iff (x : Term) : ofTermFix x = [] ↔ x = nil := by
  cases x with
  | nil => simp [read_nil]
  | cons a b t => simp [read_ne_nil]

theorem read_t1 : ofTermFix t1 = one := rfl

/-! ### The two parts of an argument -/

theorem cmp_t1_gt_false {c : Term} (h : c = nil ∨ c = t1) : (Term.cmp c t1 == .gt) = false := by
  rcases h with rfl | rfl <;> rfl

theorem partsFix_t1 : ∀ d : Term, TopS d → (partsFix d t1).2 = ([], ofTermFix d)
  | nil, _ => rfl
  | cons c e u, h => by
    have ih := partsFix_t1 u h.2
    simp only [partsFix, cmp_t1_gt_false h.1, Bool.false_eq_true, if_false, ih]
    rw [summandFix_eq, read_cons]
    rfl

theorem hiPart_of_topNil : ∀ x : Term, TopNil x → hiPart x = nil
  | nil, _ => rfl
  | cons a b t, h => by obtain ⟨rfl, _⟩ := h; simp [hiPart]

theorem loPart_of_topNil : ∀ x : Term, TopNil x → loPart x = x
  | nil, _ => rfl
  | cons a b t, h => by obtain ⟨rfl, _⟩ := h; simp [loPart]

theorem t1_ne_nil : (t1 : Term) ≠ nil := fun h => Term.noConfusion h

theorem partsFix_nil : ∀ x : Term, TopS x → TopNil (loPart x) →
    (partsFix x nil).2 = (ofTermFix (hiPart x), ofTermFix (loPart x))
  | nil, _, _ => rfl
  | cons c e u, hS, hL => by
    rcases hS.1 with rfl | rfl
    · simp only [loPart, if_true] at hL
      have hu : TopNil u := hL.2
      have ih := partsFix_nil u hS.2 (by rw [loPart_of_topNil u hu]; exact hu)
      rw [hiPart_of_topNil u hu, loPart_of_topNil u hu, read_nil] at ih
      have e1 : hiPart (cons nil e u) = nil := by simp [hiPart]
      have e2 : loPart (cons nil e u) = cons nil e u := by simp [loPart]
      rw [e1, e2, read_nil, read_cons]
      simp only [partsFix, show (Term.cmp nil nil == Ordering.gt) = false from rfl,
        Bool.false_eq_true, if_false, ih, summandFix_eq]
      rfl
    · simp only [loPart, t1_ne_nil, if_false] at hL
      have ih := partsFix_nil u hS.2 hL
      have e1 : hiPart (cons t1 e u) = cons t1 e (hiPart u) := hiPart_t1
      have e2 : loPart (cons t1 e u) = loPart u := by simp [loPart, t1_ne_nil]
      rw [e1, e2, read_cons]
      simp only [partsFix, show (Term.cmp t1 nil == Ordering.gt) = true from rfl, if_true, ih,
        summandFix_eq]
      rfl

theorem sx_nil {b : Term} (hS : TopS b) (hL : TopNil (loPart b)) :
    sx nil b = sEx true [] (ofTermFix (hiPart b)) (ofTermFix (loPart b)) := by
  unfold sx; rw [partsFix_nil b hS hL]; rfl

theorem sx_t1 {d : Term} (hS : TopS d) : sx t1 d = sEx false one [] (ofTermFix d) := by
  unfold sx; rw [partsFix_t1 d hS]; rfl

theorem isEmpty_read {x : Term} (h : x ≠ nil) : (ofTermFix x).isEmpty = false := by
  cases hx : ofTermFix x with
  | nil => exact absurd ((read_eq_nil_iff x).mp hx) h
  | cons _ _ => rfl

theorem sEx_nil_nil : sEx true [] [] [] = .o [] := rfl
theorem sEx_nil_lo {L : Od} (hL : L.isEmpty = false) : sEx true [] [] L = .o L := by
  simp [sEx, hL, add_nil_left]
theorem sEx_nil_hi {H : Od} (hH : H.isEmpty = false) : sEx true [] H [] = .psi [] H := by
  simp [sEx, hH, psiAtom, finSub]
theorem sEx_nil_hilo {H L : Od} (hH : H.isEmpty = false) (hL : L.isEmpty = false) :
    sEx true [] H L = .o (add [(.psi [] H, 1)] L) := by
  simp [sEx, hH, hL, psiAtom, finSub]
theorem sEx_t1_nil : sEx false one [] [] = .W one := rfl
theorem sEx_t1_lo {L : Od} (hL : L.isEmpty = false) :
    sEx false one [] L = .o (add [(.W one, 1)] L) := by
  simp [sEx, hL]

/-! ### Terms of the fragment -/

theorem hiPart_eq_of_loPart_nil {b : Term} (h : loPart b = nil) : hiPart b = b := by
  have := appT_hi_lo b
  rwa [h, appT_nil_right] at this

theorem allNil_hiPart_nil {b : Term} (h : AllNil b) : hiPart b = nil :=
  hiPart_of_topNil b (topNil_of_allNil b h)

theorem allNil_loPart {b : Term} (h : AllNil b) : loPart b = b :=
  loPart_of_topNil b (topNil_of_allNil b h)

/-- A good argument with `Ω` in it has a nonzero `Ω` part. -/
theorem hiPart_ne_nil {b : Term} (hg : Good b) (hA : ¬ AllNil b) : hiPart b ≠ nil := by
  obtain ⟨e, u, rfl⟩ := hg.t1 hA
  rw [hiPart_t1]; exact fun h => Term.noConfusion h

/-- **The six kinds of summands of the fragment**, and the exponent the reading writes. -/
theorem sx_cases {a b : Term} (ha : a = nil ∨ a = t1) (hS : Sub01 b) (hL : TopNil (loPart b))
    (hg : a = nil → Good b) :
    (a = nil ∧ b = nil ∧ sx a b = .o []) ∨
    (a = nil ∧ b ≠ nil ∧ AllNil b ∧ sx a b = .o (ofTermFix b)) ∨
    (a = nil ∧ ¬ AllNil b ∧ loPart b = nil ∧ sx a b = .psi [] (ofTermFix b)) ∨
    (a = nil ∧ ¬ AllNil b ∧ loPart b ≠ nil ∧
      sx a b = .o (add [(.psi [] (ofTermFix (hiPart b)), 1)] (ofTermFix (loPart b)))) ∨
    (a = t1 ∧ b = nil ∧ sx a b = .W one) ∨
    (a = t1 ∧ b ≠ nil ∧ sx a b = .o (add [(.W one, 1)] (ofTermFix b))) := by
  have hT := topS_of_sub01 b hS
  rcases ha with rfl | rfl
  · rw [sx_nil hT hL]
    by_cases hA : AllNil b
    · rw [allNil_hiPart_nil hA, allNil_loPart hA, read_nil]
      by_cases hb : b = nil
      · subst hb; left; exact ⟨rfl, rfl, rfl⟩
      · right; left; exact ⟨rfl, hb, hA, sEx_nil_lo (isEmpty_read hb)⟩
    · have hh := hiPart_ne_nil (hg rfl) hA
      by_cases hl : loPart b = nil
      · right; right; left
        refine ⟨rfl, hA, hl, ?_⟩
        rw [hl, read_nil, sEx_nil_hi (isEmpty_read hh), hiPart_eq_of_loPart_nil hl]
      · right; right; right; left
        exact ⟨rfl, hA, hl, sEx_nil_hilo (isEmpty_read hh) (isEmpty_read hl)⟩
  · rw [sx_t1 hT]
    by_cases hb : b = nil
    · subst hb; right; right; right; right; left; exact ⟨rfl, rfl, rfl⟩
    · right; right; right; right; right; exact ⟨rfl, hb, sEx_t1_lo (isEmpty_read hb)⟩

/-! ### The depth of the reading -/

/-- The nesting depth of the exponent the reading writes for `ψ_a(b)`, an upper bound
computed on the term (`exDep_sx_le`). -/
def rdT : Term → Nat
  | nil => 0
  | cons a b t =>
    max (if a = nil then (if allNilB b || loPart b == nil then rdT b + 1 else rdT b + 2)
         else (if b = nil then 2 else max 2 (rdT b) + 1)) (rdT t)

/-- The bound for one summand. -/
def rsT (a b : Term) : Nat :=
  if a = nil then (if allNilB b || loPart b == nil then rdT b + 1 else rdT b + 2)
  else (if b = nil then 2 else max 2 (rdT b) + 1)

theorem rdT_cons (a b t : Term) : rdT (cons a b t) = max (rsT a b) (rdT t) := rfl

theorem rdT_psi (a b : Term) : rdT (psi a b) = rsT a b := by
  rw [rdT_cons, show rdT nil = 0 from rfl, Nat.max_zero]

theorem rdT_arg_lt (a b : Term) : rdT b < rsT a b := by
  unfold rsT; split
  · split <;> omega
  · split
    · rename_i h; subst h; simp [rdT]
    · omega

theorem rdT_appT : ∀ s v : Term, rdT (appT s v) = max (rdT s) (rdT v)
  | nil, v => by simp [appT, rdT]
  | cons a b t, v => by
    rw [appT, rdT_cons, rdT_cons, rdT_appT t v]; omega

theorem rdT_hiPart_le (b : Term) : rdT (hiPart b) ≤ rdT b := by
  have := rdT_appT (hiPart b) (loPart b); rw [appT_hi_lo] at this; omega

theorem rdT_loPart_le (b : Term) : rdT (loPart b) ≤ rdT b := by
  have := rdT_appT (hiPart b) (loPart b); rw [appT_hi_lo] at this; omega

theorem size_hi_lo (b : Term) : size (hiPart b) + size (loPart b) = size b := by
  have := size_appT (hiPart b) (loPart b); rw [appT_hi_lo] at this; omega

/-! ### Nesting depths of normal forms -/

theorem odDep_nil : odDep [] = 0 := by simp [odDep]

theorem odDep_cons (p : Ex × Nat) (t : Od) : odDep (p :: t) = max (exDep p.1) (odDep t) := by
  simp [odDep]

theorem exDep_o (a : Od) : exDep (.o a) = odDep a + 1 := by simp [exDep]
theorem exDep_W (v : Od) : exDep (.W v) = odDep v + 1 := by simp [exDep]
theorem exDep_psi (v X : Od) : exDep (.psi v X) = max (odDep v) (odDep X) + 1 := by simp [exDep]

theorem exDep_pos (e : Ex) : 1 ≤ exDep e := by
  cases e <;> simp [exDep_o, exDep_W, exDep_psi]

theorem odDep_append : ∀ a b : Od, odDep (a ++ b) = max (odDep a) (odDep b)
  | [], b => by simp [odDep_nil]
  | p :: a, b => by
    rw [List.cons_append, odDep_cons, odDep_cons, odDep_append a b]; omega

theorem odDep_filter_le (f : Ex × Nat → Bool) : ∀ a : Od, odDep (a.filter f) ≤ odDep a
  | [] => by simp
  | p :: a => by
    have ih := odDep_filter_le f a
    rw [List.filter_cons, odDep_cons]
    split
    · rw [odDep_cons]; omega
    · omega

theorem le_odDep_of_mem {e : Ex} {k : Nat} : ∀ {a : Od}, (e, k) ∈ a → exDep e ≤ odDep a
  | [], h => by cases h
  | p :: a, h => by
    rw [odDep_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (le_odDep_of_mem h) (le_max_right _ _)

theorem odDep_add_le (a b : Od) : odDep (add a b) ≤ max (odDep a) (odDep b) := by
  cases b with
  | nil => simp [add]
  | cons y bt =>
    obtain ⟨lead, cb⟩ := y
    have hk := odDep_filter_le (fun t => cmpExp t.1 lead == .gt) a
    simp only [add]
    split
    · rw [odDep_append, odDep_cons, odDep_cons]; simp only at hk ⊢; omega
    · rw [odDep_append]; omega

theorem odDep_eq_zero {a : Od} (h : odDep a = 0) : a = [] := by
  cases a with
  | nil => rfl
  | cons p t => rw [odDep_cons] at h; have := exDep_pos p.1; omega

/-- `ato e` is one level shallower than `e` unless `e` is an atom. -/
theorem odDep_ato (e : Ex) : odDep (ato e) + (if e.isAtom then 0 else 1) = exDep e := by
  cases e with
  | o a => simp [ato, Ex.isAtom, exDep_o]
  | W v => simp [ato, Ex.isAtom, odDep_cons, odDep_nil]
  | psi v X => simp [ato, Ex.isAtom, odDep_cons, odDep_nil]

/-! ### The fragment and the depth bound -/

/-- The terms of the fragment the reading handles: standard, subscripts `0`/`1`, and the
reading at most `100` deep. -/
def Rd (x : Term) : Prop := OT x ∧ Sub01 x ∧ rdT x ≤ 100

theorem OT_of_mem_sums : ∀ (x : Term) (p : Term × Term), p ∈ sums x → OT x → OT (psi p.1 p.2)
  | nil, _, h, _ => by cases h
  | cons a b t, p, h, hOT => by
    rcases List.mem_cons.mp h with rfl | h
    · exact Googology.Notation.ExBuchholz.Term.OT_head hOT
    · exact OT_of_mem_sums t p h (Googology.Notation.ExBuchholz.Term.OT_tail hOT)

theorem sub01_of_mem_sums : ∀ (x : Term) (p : Term × Term), p ∈ sums x → Sub01 x →
    (p.1 = nil ∨ p.1 = t1) ∧ Sub01 p.2
  | nil, _, h, _ => by cases h
  | cons a b t, p, h, hS => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨hS.1, hS.2.1⟩
    · exact sub01_of_mem_sums t p h hS.2.2

theorem rsT_le_of_mem_sums : ∀ (x : Term) (p : Term × Term), p ∈ sums x →
    rsT p.1 p.2 ≤ rdT x
  | nil, _, h => by cases h
  | cons a b t, p, h => by
    rw [rdT_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (rsT_le_of_mem_sums t p h) (le_max_right _ _)

theorem size_le_of_mem_sums : ∀ (x : Term) (p : Term × Term), p ∈ sums x →
    size (psi p.1 p.2) ≤ size x
  | nil, _, h => by cases h
  | cons a b t, p, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have := size_le_of_mem_sums t p h
      simp only [Term.psi, size_cons, size_nil] at this ⊢; omega

theorem rd_of_mem_sums {x : Term} {p : Term × Term} (hp : p ∈ sums x) (hx : Rd x) :
    Rd (psi p.1 p.2) := by
  obtain ⟨hOT, hS, hd⟩ := hx
  obtain ⟨ha, hb⟩ := sub01_of_mem_sums x p hp hS
  refine ⟨OT_of_mem_sums x p hp hOT, ⟨ha, hb, trivial⟩, ?_⟩
  rw [rdT_psi]; exact le_trans (rsT_le_of_mem_sums x p hp) hd

/-- What a summand `ψ_a(b)` of the fragment gives. -/
structure SumF (a b : Term) : Prop where
  sub : a = nil ∨ a = t1
  OTb : OT b
  S01 : Sub01 b
  lo : TopNil (loPart b)
  good : a = nil → Good b
  OTp : OT (psi a b)

theorem sumF_of_rd {a b : Term} (h : Rd (psi a b)) : SumF a b where
  sub := h.2.1.1
  OTb := OT_snd h.1
  S01 := h.2.1.2.1
  lo := topNil_loPart b (OT_snd h.1)
  good := fun ha => by subst ha; exact good_of_OT_cons h.1 h.2.1
  OTp := h.1


/-! ### The depth bound -/

theorem sumF_of_OT {a b : Term} (hOT : OT (psi a b)) (hS : Sub01 (psi a b)) : SumF a b where
  sub := hS.1
  OTb := OT_snd hOT
  S01 := hS.2.1
  lo := topNil_loPart b (OT_snd hOT)
  good := fun ha => by subst ha; exact good_of_OT_cons hOT hS
  OTp := hOT

theorem OT_hiPart {b : Term} (h : OT b) : OT (hiPart b) := by
  have := h; rw [← appT_hi_lo b] at this; exact OT_appT_left _ _ this

/-- **The reading is at most `rdT` deep.** -/
theorem odDep_read_le : ∀ n : Nat, ∀ x : Term, size x ≤ n → OT x → Sub01 x →
    odDep (ofTermFix x) ≤ rdT x := by
  intro n
  induction n with
  | zero =>
    intro x hx _ _
    cases x with
    | nil => simp [read_nil, odDep_nil, rdT]
    | cons _ _ _ => simp at hx
  | succ n ih =>
    intro x hx hOT hS
    cases x with
    | nil => simp [read_nil, odDep_nil, rdT]
    | cons a b t =>
      simp only [size_cons] at hx
      rw [read_cons, rdT_cons]
      refine le_trans (odDep_add_le _ _) (max_le_max ?_ (ih t (by omega) (Googology.Notation.ExBuchholz.Term.OT_tail hOT) hS.2.2))
      rw [odDep_cons, odDep_nil]
      have hsum : SumF a b := sumF_of_OT (Googology.Notation.ExBuchholz.Term.OT_head hOT) ⟨hS.1, hS.2.1, trivial⟩
      have hb := ih b (by omega) hsum.OTb hsum.S01
      have hh := ih (hiPart b) (by have := size_hi_lo b; omega) (OT_hiPart hsum.OTb)
        (sub01_hiPart b hsum.S01)
      have hl := ih (loPart b) (by have := size_hi_lo b; omega) (OT_loPart b hsum.OTb)
        (sub01_loPart b hsum.S01)
      have hrh := rdT_hiPart_le b
      have hrl := rdT_loPart_le b
      rcases sx_cases hsum.sub hsum.S01 hsum.lo hsum.good with ⟨rfl, rfl, e⟩ | ⟨rfl, hb0, hA, e⟩ | ⟨rfl, hA, hl0, e⟩ |
          ⟨rfl, hA, hl0, e⟩ | ⟨rfl, rfl, e⟩ | ⟨rfl, hb0, e⟩ <;> rw [e]
      · simp [exDep_o, odDep_nil, rsT, allNilB]
      · have : allNilB b = true := (allNilB_iff b).mpr hA
        simp only [exDep_o, rsT, this, if_true, Bool.true_or]; omega
      · have : (loPart b == nil) = true := by simp [hl0]
        simp only [exDep_psi, odDep_nil, rsT, this, if_true, Bool.or_true]; omega
      · have h1 : allNilB b = false := by
          cases h' : allNilB b
          · rfl
          · exact absurd ((allNilB_iff b).mp h') hA
        have h2 : (loPart b == nil) = false := by simp [hl0]
        simp only [rsT, h1, h2, if_true, Bool.or_self, Bool.false_eq_true, if_false, exDep_o]
        have := odDep_add_le [(.psi [] (ofTermFix (hiPart b)), 1)] (ofTermFix (loPart b))
        rw [odDep_cons, odDep_nil, exDep_psi, odDep_nil] at this
        omega
      · simp [exDep_W, rsT, one, nat, odDep_cons, odDep_nil, exDep_o, t1_ne_nil]
      · simp only [rsT, t1_ne_nil, if_false, hb0, exDep_o]
        have := odDep_add_le [(.W one, 1)] (ofTermFix b)
        have hW : odDep [(.W one, 1)] = 2 := by
          simp [exDep_W, one, nat, odDep_cons, odDep_nil, exDep_o]
        rw [hW] at this
        omega


theorem exDep_sx_le {a b : Term} (h : Rd (psi a b)) : exDep (sx a b) ≤ rsT a b := by
  have := odDep_read_le (size (psi a b)) (psi a b) le_rfl h.1 h.2.1
  simp only [read_psi, odDep_cons, odDep_nil, rdT_psi] at this
  omega

theorem exDep_sx_le100 {a b : Term} (h : Rd (psi a b)) : exDep (sx a b) ≤ 100 := by
  have := exDep_sx_le h; have := h.2.2; rw [rdT_psi] at this; omega

/-! ### Grouping -/

/-- The run-length code of the summands, each `ψ_a(b)` written `ω^{sx a b}`. -/
def grpS (L : List ((Term × Term) × Nat)) : Od := L.map (fun p => (sx p.1.1 p.1.2, p.2))

/-- **The reading groups the summands.** -/
def Inv (x : Term) : Prop := ∃ L, GDesc2 L ∧ ofTermFix x = grpS L ∧ expandG2 L = sums x

theorem lexS_grpS (c : Od → Od → Ordering) :
    ∀ L1 L2 : List ((Term × Term) × Nat), GDesc2 L1 → GDesc2 L2 →
      (∀ p ∈ L1, ∀ q ∈ L2, cmpExpWith c (sx p.1.1 p.1.2) (sx q.1.1 q.1.2) = pcmp p.1 q.1) →
      cmpOrdWith c (grpS L1) (grpS L2) = lexS (expandG2 L1) (expandG2 L2) := by
  intro L1
  induction L1 with
  | nil =>
    intro L2 _ h2 _
    cases L2 with
    | nil => simp [grpS, expandG2, cmpOrdWith_nil_nil, lexS]
    | cons q r =>
      have hq := GDesc2_head_pos h2
      obtain ⟨k, hk⟩ : ∃ k, q.2 = k + 1 := ⟨q.2 - 1, by omega⟩
      simp [grpS, expandG2, cmpOrdWith_nil_cons, hk, List.replicate_succ, lexS]
  | cons p r ih =>
    intro L2 h1 h2 hc
    cases L2 with
    | nil =>
      have hp := GDesc2_head_pos h1
      obtain ⟨k, hk⟩ : ∃ k, p.2 = k + 1 := ⟨p.2 - 1, by omega⟩
      simp [grpS, expandG2, cmpOrdWith_cons_nil, hk, List.replicate_succ, lexS]
    | cons q s =>
      have ihr := ih s (GDesc2_tail h1) (GDesc2_tail h2)
        (fun p' hp' q' hq' => hc p' (List.mem_cons_of_mem _ hp') q' (List.mem_cons_of_mem _ hq'))
      have hpq := hc p List.mem_cons_self q List.mem_cons_self
      have e1 : grpS (p :: r) = (sx p.1.1 p.1.2, p.2) :: grpS r := rfl
      have e2 : grpS (q :: s) = (sx q.1.1 q.1.2, q.2) :: grpS s := rfl
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

theorem mem_grpS_of_mem {L : List ((Term × Term) × Nat)} {p : (Term × Term) × Nat}
    (hp : p ∈ L) : (sx p.1.1 p.1.2, p.2) ∈ grpS L :=
  List.mem_map.mpr ⟨p, hp, rfl⟩

theorem exDep_le_read {x : Term} {L : List ((Term × Term) × Nat)} (hO : ofTermFix x = grpS L)
    {p : (Term × Term) × Nat} (hp : p ∈ L) : exDep (sx p.1.1 p.1.2) ≤ odDep (ofTermFix x) := by
  rw [hO]; exact le_odDep_of_mem (mem_grpS_of_mem hp)

theorem add_lt' {x lead : Ex} {cb : Nat} {bt : Od} (h : cmpExp x lead = .lt) :
    add [(x, 1)] ((lead, cb) :: bt) = (lead, cb) :: bt := by
  simp [add, h]

/-! ### The exponent as a term: `ext` -/

/-- The first summand of `d` is `ψ_c(e)` with `c, e ≠ 0`: it absorbs `Ω`. -/
def absd : Term → Bool
  | nil => false
  | cons c e _ => c != nil && e != nil

/-- `Ω + d` as a standard term: `d` itself when its first summand `ψ_1(e)`, `e ≠ 0`,
absorbs `Ω`. -/
def omx (d : Term) : Term := if absd d then d else cons t1 nil d

/-- The term whose reading is `ato (sx a b)`: `expoT b` for `ψ_0(b)`, `omx d` for `ψ_1(d)`. -/
def ext (a b : Term) : Term := if a = nil then expoT b else omx b

/-- **`ato (sx a b)` is the reading of `ext a b`.** -/
def KI (a b : Term) : Prop := ato (sx a b) = ofTermFix (ext a b)

theorem ext_nil (b : Term) : ext nil b = expoT b := if_pos rfl
theorem ext_t1 (d : Term) : ext t1 d = omx d := if_neg t1_ne_nil

theorem size_ext {a b : Term} (h : SumF a b) : size (ext a b) ≤ size (psi a b) := by
  rcases h.sub with rfl | rfl
  · rw [ext_nil]
    by_cases hA : AllNil b
    · rw [expoT_allNil hA]; simp
    · rw [expoT_not hA]
      have := size_hi_lo b
      split
      · simp; omega
      · simp; omega
  · rw [ext_t1]
    unfold omx
    split <;> simp <;> omega

theorem OT_tW : OT tW := by decide

theorem cmp_of_mono {x y x' y' : Term} (h1 : x < y → x' < y') (h2 : y < x → y' < x')
    (h3 : x = y → x' = y') : Term.cmp x' y' = Term.cmp x y := by
  rcases Term.lt_trichotomy x y with h | h | h
  · rw [show Term.cmp x' y' = .lt from h1 h, show Term.cmp x y = .lt from h]
  · rw [h3 h, h, cmp_self, cmp_self]
  · have a1 : Term.cmp y' x' = .lt := h2 h
    have a2 : Term.cmp y x = .lt := h
    rw [← cmp_swap y' x', a1, ← cmp_swap y x, a2]

theorem cmp_nil_of_ne {e : Term} (h : e ≠ nil) : Term.cmp e nil = .gt := by
  cases e with
  | nil => exact absurd rfl h
  | cons _ _ _ => rfl

theorem omx_cmp {d d' : Term} (hd : TopS d) (hd' : TopS d') :
    Term.cmp (omx d) (omx d') = Term.cmp d d' := by
  have key : ∀ {d d' : Term}, TopS d → TopS d' → absd d = true → absd d' = false →
      Term.cmp d (cons t1 nil d') = .gt ∧ Term.cmp d d' = .gt := by
    intro d d' hd hd' h1 h2
    cases d with
    | nil => simp [absd] at h1
    | cons c e u =>
      simp only [absd, Bool.and_eq_true, bne_iff_ne, ne_eq] at h1
      have hc1 : c = t1 := hd.1.resolve_left h1.1
      subst hc1
      refine ⟨by simp [Term.cmp, cmp_nil_of_ne h1.2, Ordering.then], ?_⟩
      cases d' with
      | nil => rfl
      | cons c' e' u' =>
        rcases hd'.1 with rfl | rfl
        · rfl
        · have he' : e' = nil := by
            simp only [absd, Bool.and_eq_false_iff, bne_eq_false_iff_eq] at h2
            rcases h2 with h2 | h2
            · exact absurd h2 t1_ne_nil
            · exact h2
          subst he'
          simp [Term.cmp, cmp_nil_of_ne h1.2, Ordering.then]
  unfold omx
  cases h1 : absd d <;> cases h2 : absd d'
  · simp [Term.cmp, Ordering.then]
  · simp only [Bool.false_eq_true, if_false, if_true]
    obtain ⟨k1, k2⟩ := key hd' hd h2 h1
    rw [← cmp_swap d' (cons t1 nil d), k1, ← cmp_swap d' d, k2]
  · simp only [Bool.false_eq_true, if_false, if_true]
    obtain ⟨k1, k2⟩ := key hd hd' h1 h2
    rw [k1, k2]
  · simp

theorem topNil_lt_t1 {x : Term} (hx : TopNil x) {e u : Term} : x < cons t1 e u := by
  cases x with
  | nil => exact nil_lt_cons _ _ _
  | cons c f w =>
    obtain ⟨rfl, _⟩ := hx
    exact cons_lt_cons_iff.mpr (Or.inl (psi_lt_psi_iff.mpr (Or.inl (nil_lt_cons _ _ _))))

theorem omx_head {d : Term} (hd : TopS d) : ∃ e u, omx d = cons t1 e u := by
  unfold omx
  cases h : absd d
  · exact ⟨nil, d, rfl⟩
  · cases d with
    | nil => simp [absd] at h
    | cons c e u =>
      simp only [absd, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      exact ⟨e, u, by rw [hd.1.resolve_left h.1]; rfl⟩

/-- **`ext` keeps the order of the summands.** -/
theorem ext_cmp {a b a' b' : Term} (h : SumF a b) (h' : SumF a' b') :
    Term.cmp (ext a b) (ext a' b') = pcmp (a, b) (a', b') := by
  rw [pcmp_def]
  rcases h.sub with rfl | rfl <;> rcases h'.sub with rfl | rfl
  · rw [ext_nil, ext_nil, cmp_self]
    have hg := h.good rfl
    have hg' := h'.good rfl
    exact cmp_of_mono (fun k => expoT_lt hg hg' k) (fun k => expoT_lt hg' hg k)
      (fun k => by rw [k])
  · rw [ext_nil, ext_t1]
    obtain ⟨e, u, hu⟩ := omx_head (topS_of_sub01 _ h'.S01)
    rw [hu, show Term.cmp nil t1 = .lt from rfl]
    exact topNil_lt_t1 (topNil_expoT (h.good rfl))
  · rw [ext_t1, ext_nil]
    obtain ⟨e, u, hu⟩ := omx_head (topS_of_sub01 _ h.S01)
    rw [hu, show Term.cmp t1 nil = .gt from rfl]
    have := topNil_lt_t1 (topNil_expoT (h'.good rfl)) (e := e) (u := u)
    have hs := cmp_swap (expoT b') (cons t1 e u)
    rw [show Term.cmp (expoT b') (cons t1 e u) = .lt from this] at hs
    rw [← hs]; rfl
  · rw [ext_t1, ext_t1, cmp_self]
    exact omx_cmp (topS_of_sub01 _ h.S01) (topS_of_sub01 _ h'.S01)

theorem rsT_nil_hiPart {b : Term} (hg : Good b) (hA : ¬ AllNil b) :
    rsT nil (hiPart b) = rdT (hiPart b) + 1 := by
  have : (loPart (hiPart b) == nil) = true := by simp [loPart_hiPart]
  simp [rsT, this]

/-- The exponent term is again in the fragment. -/
theorem rd_ext {a b : Term} (hp : Rd (psi a b)) : Rd (ext a b) := by
  have h := sumF_of_rd hp
  have hd : rsT a b ≤ 100 := by have := hp.2.2; rwa [rdT_psi] at this
  have hlt := rdT_arg_lt a b
  rcases h.sub with rfl | rfl
  · rw [ext_nil]
    have hg := h.good rfl
    refine ⟨OT_expoT h.OTp hg, sub01_expoT h.S01, ?_⟩
    by_cases hA : AllNil b
    · rw [expoT_allNil hA]; omega
    · rw [expoT_not hA]
      have hr := rdT_hiPart_le b
      have hl := rdT_loPart_le b
      split
      · omega
      · rw [rdT_cons, rsT_nil_hiPart hg hA]; omega
  · rw [ext_t1]
    have hOTd := h.OTb
    unfold omx
    split
    · exact ⟨hOTd, h.S01, by omega⟩
    · rename_i hn
      refine ⟨OT_cons_of OT_tW hOTd ?_, ⟨Or.inr rfl, trivial, h.S01⟩, ?_⟩
      · cases b with
        | nil => trivial
        | cons c e u =>
          show psi c e ≤ psi t1 nil
          rcases h.S01.1 with rfl | rfl
          · exact Term.le_of_lt (psi_lt_psi_iff.mpr (Or.inl (nil_lt_cons _ _ _)))
          · have : e = nil := by
              simp only [absd, Bool.and_eq_true, bne_iff_ne, ne_eq, not_and, not_not] at hn
              exact hn t1_ne_nil
            subst this; exact Term.le_refl _
      · rw [rdT_cons, show rsT t1 nil = 2 by simp [rsT, t1_ne_nil]]; omega

/-! ### The comparison, by induction on the fuel -/

/-- `cmpF n` compares the readings of the terms of size `≤ s` correctly, within the
potential `n ≥ odDep + odDep`. -/
def CS (s n : Nat) : Prop :=
  ∀ x y : Term, Rd x → Rd y → size x ≤ s → size y ≤ s →
    odDep (ofTermFix x) + odDep (ofTermFix y) ≤ n →
      cmpF n (ofTermFix x) (ofTermFix y) = Term.cmp x y

/-- Grouping and `KI` up to size `s`. -/
def IK (s : Nat) : Prop :=
  (∀ x, Rd x → size x ≤ s → Inv x) ∧ (∀ a b, Rd (psi a b) → size (psi a b) ≤ s → KI a b)

theorem atom_cases {a b : Term} (h : SumF a b) (hat : (sx a b).isAtom = true) :
    (a = nil ∧ sx a b = .psi [] (ofTermFix b)) ∨ (a = t1 ∧ b = nil ∧ sx a b = .W one) := by
  rcases sx_cases h.sub h.S01 h.lo h.good with ⟨_, _, e⟩ | ⟨_, _, _, e⟩ | ⟨ha, _, _, e⟩ |
      ⟨_, _, _, e⟩ | ⟨ha, hb, e⟩ | ⟨_, _, e⟩ <;> rw [e] at hat ⊢ <;> simp [Ex.isAtom] at hat
  · exact Or.inl ⟨ha, rfl⟩
  · exact Or.inr ⟨ha, hb, rfl⟩

theorem cmpAtom_psi0 (c : Od → Od → Ordering) (hc : c [] [] = .eq) (X Y : Od) :
    cmpAtomWith c (.psi [] X) (.psi [] Y) = c X Y := by
  simp [cmpAtomWith, TrioTreeRules.lvl_psi0, hc, kindA, isCardPsi, argA, Ordering.then]

theorem rd_arg {a b : Term} (hp : Rd (psi a b)) : Rd b :=
  ⟨OT_snd hp.1, hp.2.1.2.1, by have := hp.2.2; have := rdT_arg_lt a b; rw [rdT_psi] at *; omega⟩

theorem ki_read {a b : Term} (hK : KI a b) : ofTermFix (ext a b) = ato (sx a b) := hK.symm

/-- **One comparison of exponents.** -/
theorem sc_step {s n : Nat} (hIK : IK s) (hC : CS s n) {a b a' b' : Term}
    (hp : Rd (psi a b)) (hq : Rd (psi a' b')) (hsp : size (psi a b) ≤ s)
    (hsq : size (psi a' b') ≤ s) (hd : exDep (sx a b) + exDep (sx a' b') ≤ n + 1) :
    cmpExpWith (cmpF n) (sx a b) (sx a' b') = pcmp (a, b) (a', b') := by
  have hs := sumF_of_rd hp
  have hs' := sumF_of_rd hq
  rw [pcmp_def]
  by_cases hat : ((sx a b).isAtom && (sx a' b').isAtom) = true
  · have hc : cmpExpWith (cmpF n) (sx a b) (sx a' b') = cmpAtomWith (cmpF n) (sx a b) (sx a' b') := by
      unfold cmpExpWith; rw [if_pos hat]
    rw [hc]
    simp only [Bool.and_eq_true] at hat
    rcases atom_cases hs hat.1 with ⟨rfl, e1⟩ | ⟨rfl, rfl, e1⟩ <;>
      rcases atom_cases hs' hat.2 with ⟨rfl, e2⟩ | ⟨rfl, rfl, e2⟩ <;>
      (first | rw [e1, e2] at hd ⊢ | rw [e1] at hd ⊢)
    · rw [cmpAtom_psi0 _ (cmpF_nil_nil n), cmp_self]
      rw [exDep_psi, exDep_psi, odDep_nil] at hd
      have hsb : size b < size (psi nil b) := by simp
      have hsb' : size b' < size (psi nil b') := by simp
      exact hC b b' (rd_arg hp) (rd_arg hq) (by omega) (by omega) (by omega)
    · rw [exDep_psi, exDep_W, odDep_nil] at hd
      have hW : odDep one = 1 := by simp [one, nat, odDep_cons, odDep_nil, exDep_o]
      rw [hW] at hd
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      simp [cmpAtomWith, TrioTreeRules.lvl_psi0, TrioTreeRules.lvl_W1,
        TrioTreeRules.cmpF_nil_one, Ordering.then]
      rfl
    · rw [exDep_psi, exDep_W, odDep_nil] at hd
      have hW : odDep one = 1 := by simp [one, nat, odDep_cons, odDep_nil, exDep_o]
      rw [hW] at hd
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      simp [cmpAtomWith, TrioTreeRules.lvl_psi0, TrioTreeRules.lvl_W1,
        TrioTreeRules.cmpF_one_nil, Ordering.then]
      rfl
    · simp [cmpAtomWith, TrioTreeRules.lvl_W1, TrioTreeRules.cmpF_one_one, kindA, Ordering.then]
  · have hc : cmpExpWith (cmpF n) (sx a b) (sx a' b') = cmpF n (ato (sx a b)) (ato (sx a' b')) := by
      unfold cmpExpWith; rw [if_neg hat]
    rw [hc, ← ki_read (hIK.2 a b hp hsp), ← ki_read (hIK.2 a' b' hq hsq), ← pcmp_def]
    rw [hC (ext a b) (ext a' b') (rd_ext hp) (rd_ext hq) (le_trans (size_ext hs) hsp)
      (le_trans (size_ext hs') hsq) ?_]
    · exact ext_cmp hs hs'
    · rw [ki_read (hIK.2 a b hp hsp), ki_read (hIK.2 a' b' hq hsq)]
      have k1 := odDep_ato (sx a b)
      have k2 := odDep_ato (sx a' b')
      cases h1 : (sx a b).isAtom <;> cases h2 : (sx a' b').isAtom <;>
        simp only [h1, h2, Bool.and_self, Bool.false_eq_true, ↓reduceIte] at hat k1 k2 <;>
        first | omega | simp at hat

/-- **The comparison of readings, by induction on the fuel.** -/
theorem c_step {s : Nat} (hIK : IK s) : ∀ n, CS s n := by
  intro n
  induction n with
  | zero =>
    intro x y _ _ _ _ hd
    have h1 : ofTermFix x = [] := odDep_eq_zero (by omega)
    have h2 : ofTermFix y = [] := odDep_eq_zero (by omega)
    rw [(read_eq_nil_iff x).mp h1, (read_eq_nil_iff y).mp h2]; rfl
  | succ n ih =>
    intro x y hx hy hsx hsy hd
    obtain ⟨L1, hG1, hO1, hE1⟩ := hIK.1 x hx hsx
    obtain ⟨L2, hG2, hO2, hE2⟩ := hIK.1 y hy hsy
    show cmpOrdWith (cmpF n) (ofTermFix x) (ofTermFix y) = _
    rw [cmp_sums x y, ← hE1, ← hE2]
    rw [hO1, hO2]
    refine lexS_grpS _ L1 L2 hG1 hG2 ?_
    intro p hp q hq
    have hp' : p.1 ∈ sums x := hE1 ▸ mem_expandG2 hG1 hp
    have hq' : q.1 ∈ sums y := hE2 ▸ mem_expandG2 hG2 hq
    have e1 := exDep_le_read hO1 hp
    have e2 := exDep_le_read hO2 hq
    exact sc_step hIK ih (rd_of_mem_sums hp' hx) (rd_of_mem_sums hq' hy)
      (le_trans (size_le_of_mem_sums _ _ hp') hsx) (le_trans (size_le_of_mem_sums _ _ hq') hsy)
      (by omega)


/-! ### Grouping and `KI`, by induction on the size -/

theorem rd_tail {a b t : Term} (hx : Rd (cons a b t)) : Rd t :=
  ⟨Googology.Notation.ExBuchholz.Term.OT_tail hx.1, hx.2.1.2.2,
    by have := hx.2.2; rw [rdT_cons] at this; omega⟩

theorem fuel_eq : fuel = 200 := rfl

theorem inv_step {s : Nat} (hIK : IK s) (hC : ∀ n, CS s n) :
    ∀ x : Term, Rd x → size x ≤ s + 1 → Inv x := by
  intro x hx hsx
  cases x with
  | nil => exact ⟨[], trivial, rfl, rfl⟩
  | cons a b t =>
    have hxt : Rd t := rd_tail hx
    have hst : size t ≤ s := by simp at hsx; omega
    obtain ⟨Lt, hGt, hOt, hEt⟩ := hIK.1 t hxt hst
    unfold Inv
    rw [read_cons, hOt]
    cases Lt with
    | nil =>
      refine ⟨[((a, b), 1)], by simp [GDesc2], ?_, ?_⟩
      · simp [grpS, add_nil_right]
      · cases t with
        | nil => rfl
        | cons _ _ _ => simp [expandG2, sums] at hEt
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
        have hle : Term.cmp (psi a' b') (psi a b) ≠ .gt := OT_tail_head_le hx.1
        have hpa : Rd (psi a b) :=
          rd_of_mem_sums (x := cons a b (cons a' b' t')) (p := (a, b)) List.mem_cons_self hx
        have hpb : Rd (psi a' b') :=
          rd_of_mem_sums (x := cons a b (cons a' b' t')) (p := (a', b'))
            (List.mem_cons_of_mem _ List.mem_cons_self) hx
        have hc : cmpExp (sx a b) (sx a' b') = pcmp (a, b) (a', b') :=
          sc_step hIK (hC fuel) hpa hpb (by simp at hsx ⊢; omega) (by simp at hst ⊢; omega)
            (by have := exDep_sx_le100 hpa; have := exDep_sx_le100 hpb; rw [fuel_eq]; omega)
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

theorem rd_psi_t1_nil : Rd (psi t1 nil) := ⟨OT_tW, ⟨Or.inr rfl, trivial, trivial⟩, by decide⟩

theorem rd_loPart {b : Term} (hp : Rd (psi nil b)) : Rd (loPart b) :=
  ⟨OT_loPart b (OT_snd hp.1), sub01_loPart b hp.2.1.2.1,
    by have := rdT_loPart_le b; have := rdT_arg_lt nil b; have := hp.2.2; rw [rdT_psi] at this
       omega⟩

theorem rd_psi_hiPart {b : Term} (hp : Rd (psi nil b)) (hg : Good b) (hA : ¬ AllNil b) :
    Rd (psi nil (hiPart b)) :=
  ⟨OT_psi_hiPart hp.1, ⟨Or.inl rfl, sub01_hiPart b hp.2.1.2.1, trivial⟩, by
    rw [rdT_psi, rsT_nil_hiPart hg hA]
    have := rdT_hiPart_le b; have := rdT_arg_lt nil b; have := hp.2.2; rw [rdT_psi] at this
    omega⟩

theorem sx_hiPart {b : Term} (hS : Sub01 b) (hh : hiPart b ≠ nil) :
    sx nil (hiPart b) = .psi [] (ofTermFix (hiPart b)) := by
  rw [sx_nil (topS_of_sub01 _ (sub01_hiPart b hS)) (by rw [loPart_hiPart]; trivial),
    hiPart_hiPart, loPart_hiPart, read_nil]
  exact sEx_nil_hi (isEmpty_read hh)

theorem ki_step {s : Nat} (hIK : IK s) (hC : ∀ n, CS s n) {a b : Term}
    (hp : Rd (psi a b)) (hsp : size (psi a b) ≤ s + 1) : KI a b := by
  have hs := sumF_of_rd hp
  have hsb : size b ≤ s := by simp at hsp; omega
  unfold KI
  rcases sx_cases hs.sub hs.S01 hs.lo hs.good with ⟨rfl, rfl, e⟩ | ⟨rfl, hb0, hA, e⟩ |
      ⟨rfl, hA, hl0, e⟩ | ⟨rfl, hA, hl0, e⟩ | ⟨rfl, rfl, e⟩ | ⟨rfl, hb0, e⟩ <;> rw [e]
  · rfl
  · rw [ext_nil, expoT_allNil hA]; rfl
  · rw [ext_nil, expoT_not hA]
    simp only [hl0, absorbs, Bool.false_eq_true, if_false]
    rw [hiPart_eq_of_loPart_nil hl0, read_psi, e]; rfl
  · have hg := hs.good rfl
    have hh := hiPart_ne_nil hg hA
    have hEh := sx_hiPart hs.S01 hh
    rw [ext_nil, expoT_not hA]
    split
    · rename_i hab
      obtain ⟨g1, w, hlw⟩ : ∃ g1 w, loPart b = cons nil g1 w := by
        rcases loPart_cases b with h0 | h0
        · exact absurd h0 hl0
        · exact h0
      rw [hlw] at hab
      simp only [absorbs, decide_eq_true_eq] at hab
      have hl := rd_loPart hp
      have hsl : size (loPart b) ≤ s := by have := size_hi_lo b; omega
      obtain ⟨L, hG, hO, hE⟩ := hIK.1 _ hl hsl
      cases L with
      | nil => rw [hlw] at hE; simp [expandG2, sums] at hE
      | cons q L' =>
        obtain ⟨d, c⟩ := q
        have hc : 0 < c := GDesc2_head_pos hG
        obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
        have hd : d = (nil, g1) := by
          rw [hlw] at hE; simp [expandG2, sums, List.replicate_succ] at hE; exact hE.1
        subst hd
        rw [hO]
        show add [(.psi [] (ofTermFix (hiPart b)), 1)] ((sx nil g1, c' + 1) :: grpS L') =
          (sx nil g1, c' + 1) :: grpS L'
        apply add_lt'
        rw [← hEh]
        have hph := rd_psi_hiPart hp hg hA
        have hpg : Rd (psi nil g1) :=
          rd_of_mem_sums (x := loPart b) (p := (nil, g1)) (by rw [hlw]; exact List.mem_cons_self) hl
        have hsg : size (psi nil g1) ≤ s := by
          have := size_le_of_mem_sums (loPart b) (nil, g1) (by rw [hlw]; exact List.mem_cons_self)
          simp only at this
          omega
        have hsh : size (psi nil (hiPart b)) ≤ s := by
          have := size_hi_lo b
          have : size (loPart b) ≥ 1 := by rw [hlw]; simp
          simp; omega
        have key := sc_step hIK (hC fuel) hph hpg hsh hsg
          (by have := exDep_sx_le100 hph; have := exDep_sx_le100 hpg; rw [fuel_eq]; omega)
        show cmpExpWith (cmpF fuel) _ _ = _
        rw [key, pcmp_def, cmp_self]
        exact hab
    · rw [read_cons, hEh]; rfl
  · rw [ext_t1, show omx nil = psi t1 nil from rfl, read_psi, e]; rfl
  · rw [ext_t1]
    unfold omx
    split
    · rename_i hab
      cases b with
      | nil => exact absurd rfl hb0
      | cons c e1 u =>
        simp only [absd, Bool.and_eq_true, bne_iff_ne, ne_eq] at hab
        have hc1 : c = t1 := hs.S01.1.resolve_left hab.1
        subst hc1
        have hb := rd_arg hp
        obtain ⟨L, hG, hO, hE⟩ := hIK.1 _ hb hsb
        cases L with
        | nil => simp [expandG2, sums] at hE
        | cons q L' =>
          obtain ⟨d, c⟩ := q
          have hc : 0 < c := GDesc2_head_pos hG
          obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
          have hd : d = (t1, e1) := by
            simp [expandG2, sums, List.replicate_succ] at hE; exact hE.1
          subst hd
          rw [hO]
          show add [(.W one, 1)] ((sx t1 e1, c' + 1) :: grpS L') = (sx t1 e1, c' + 1) :: grpS L'
          apply add_lt'
          have hpe : Rd (psi t1 e1) :=
            rd_of_mem_sums (x := cons t1 e1 u) (p := (t1, e1)) List.mem_cons_self hb
          have hse : size (psi t1 e1) ≤ s := by simp at hsb ⊢; omega
          have hs2 : size (psi t1 nil) ≤ s := by
            have : size e1 ≥ 1 := by cases e1 with
              | nil => exact absurd rfl hab.2
              | cons _ _ _ => simp
            simp at hsb ⊢; omega
          have key := sc_step hIK (hC fuel) rd_psi_t1_nil hpe hs2 hse
            (by have := exDep_sx_le100 rd_psi_t1_nil; have := exDep_sx_le100 hpe; rw [fuel_eq]
                omega)
          show cmpExpWith (cmpF fuel) (sx t1 nil) (sx t1 e1) = _
          rw [key, pcmp_def, cmp_self]
          show (Term.cmp nil e1) = .lt
          cases e1 with
          | nil => exact absurd rfl hab.2
          | cons _ _ _ => rfl
    · rw [read_cons, sx_t1 (d := nil) trivial, read_nil, sEx_t1_nil]; rfl

theorem ik_all : ∀ s, IK s := by
  intro s
  induction s with
  | zero =>
    refine ⟨fun x _ hx => ?_, fun a b _ h => ?_⟩
    · cases x with
      | nil => exact ⟨[], trivial, rfl, rfl⟩
      | cons _ _ _ => simp at hx
    · simp at h
  | succ s ih =>
    have hC := c_step ih
    exact ⟨inv_step ih hC, fun a b hp hsp => ki_step ih hC hp hsp⟩

/-! ### What the rest of the proof uses -/

/-- **The reading groups the summands** on the fragment. -/
theorem inv_all {x : Term} (hx : Rd x) : Inv x := (ik_all (size x)).1 x hx le_rfl

/-- **The exponent of a summand is the reading of `ext`.** -/
theorem ki_all {a b : Term} (hp : Rd (psi a b)) : KI a b := (ik_all _).2 a b hp le_rfl

/-- **The comparison of readings**, with fuel at least the sum of their depths. -/
theorem cmp_read {n : Nat} {x y : Term} (hx : Rd x) (hy : Rd y)
    (hd : odDep (ofTermFix x) + odDep (ofTermFix y) ≤ n) :
    cmpF n (ofTermFix x) (ofTermFix y) = Term.cmp x y :=
  c_step (ik_all (max (size x) (size y))) n x y hx hy (le_max_left _ _) (le_max_right _ _) hd

/-- **The program's comparison of two exponents of the fragment** is the order of the
summands. -/
theorem cmpExp_sx {a b a' b' : Term} (hp : Rd (psi a b)) (hq : Rd (psi a' b')) :
    cmpExp (sx a b) (sx a' b') = pcmp (a, b) (a', b') :=
  sc_step (ik_all (max (size (psi a b)) (size (psi a' b'))))
    (c_step (ik_all (max (size (psi a b)) (size (psi a' b')))) fuel) hp hq
    (le_max_left _ _) (le_max_right _ _)
    (by have := exDep_sx_le100 hp; have := exDep_sx_le100 hq; rw [fuel_eq]; omega)

end Googology.Trans.BMS.TrioFixStripCalib

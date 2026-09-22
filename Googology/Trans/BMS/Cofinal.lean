import Googology.Trans.BMS.Calibrate

/-!
# The fundamental sequence converges

`fs_lt` says `X[n] < X`.  That a notation system's `[ ]` is a *fundamental
sequence* asks for more: that `X` is the least upper bound, so that anything
below `X` is below some `X[n]`.  `exists_le_fs` proves it below `ψ_0(Ω)`.

The three cases are the three shapes of `dom` a term with all subscripts `0`
can have.  At a sum the expansion works in the last summand, so the claim
passes to the tail.  At `ψ_0(a+1)` the members are `ψ_0(a)·n`, and a sum of
`k` terms each at most `ψ_0(a)` is at most `ψ_0(a)·k` — that is
`le_repeatPrin`.  At `ψ_0(a)` with `a` an `ω`-limit the members are
`ψ_0(a[n])`, and the claim passes to `a`, applied to `b + 1` rather than `b`
so that the bound comes out strict; `addT_t1_lt` is what makes `b + 1 < a`
available at a limit.

The index is written `n + 1` because that is what an expansion supplies:
`A[N]` is `X[N+1]`.

`fs_idx_lt` is the companion: at an `ω`-limit the members increase.  The two
together are `fs_lub` — below `ψ_0(Ω)`, `X` is the least upper bound of
`X[0] < X[1] < ⋯`, which is what calling `[ ]` a fundamental sequence means.
-/

namespace Googology.Trans.BMS
open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term

/-! ### Small facts -/

theorem cons_le_cons {a b u v : Term} (h : u ≤ v) : cons a b u ≤ cons a b v := by
  rcases le_iff_lt_or_eq.mp h with h1 | h1
  · exact le_of_lt (cons_lt_cons_iff.mpr (Or.inr ⟨rfl, h1⟩))
  · rw [h1]; exact le_refl _

theorem psi_le_psi_nil {b c : Term} (h : psi nil b ≤ psi nil c) : b ≤ c := by
  rcases le_iff_lt_or_eq.mp h with h1 | h1
  · rcases psi_lt_psi_iff.mp h1 with h2 | h2
    · exact absurd h2 (not_lt_nil nil)
    · exact le_of_lt h2.2
  · injection h1 with _ h2 _
    rw [h2]; exact le_refl _

theorem psi_le_psi_of_le {b c : Term} (h : b ≤ c) : psi nil b ≤ psi nil c := by
  rcases le_iff_lt_or_eq.mp h with h1 | h1
  · exact le_of_lt (psi_lt_psi_iff.mpr (Or.inr ⟨rfl, h1⟩))
  · rw [h1]; exact le_refl _

theorem OT_descHead {a b t : Term} (h : OT (cons a b t)) : descHead a b t = true := by
  simp only [OT, isOT, Bool.and_eq_true] at h
  exact h.2

/-- The number of summands. -/
def count : Term → Nat
  | nil => 0
  | cons _ _ t => count t + 1

/-- The leading argument, if there is one, is at most `c`. -/
def headLe (c : Term) : Term → Prop
  | nil => True
  | cons _ b _ => b ≤ c

/-- In a standard sum with every subscript `0`, the arguments do not
increase. -/
theorem headLe_tail {b u : Term} (hOT : OT (cons nil b u)) (hA : AllNil (cons nil b u)) :
    headLe b u := by
  obtain ⟨_, _, hAu⟩ := hA
  cases u with
  | nil => exact trivial
  | cons c d r =>
    obtain ⟨hc, _, _⟩ := hAu
    subst hc
    have hd := OT_descHead hOT
    simp only [descHead, head?] at hd
    exact psi_le_psi_nil (of_decide_eq_true hd)

/-- **A sum is at most that many copies of its leading term.** -/
theorem le_repeatPrin : ∀ (Y c : Term), OT Y → AllNil Y → headLe c Y →
    Y ≤ repeatPrin nil c (count Y) := by
  intro Y
  induction Y with
  | nil => intro c _ _ _; rw [count, repeatPrin]; exact le_refl _
  | cons a b u _ _ ihu =>
    intro c hOT hA hle
    obtain ⟨ha, _, hAu⟩ := hA
    subst ha
    rw [count, repeatPrin]
    rcases le_iff_lt_or_eq.mp (show b ≤ c from hle) with h1 | h1
    · refine le_of_lt (lt_of_lt_of_le' ?_ (psi_le_cons nil c _))
      exact cons_lt_psi_iff.mpr (psi_lt_psi_iff.mpr (Or.inr ⟨rfl, h1⟩))
    · subst h1
      exact cons_le_cons (ihu b (OT_tail hOT) hAu
        (headLe_tail hOT ⟨rfl, by assumption, hAu⟩))

/-! ### Shapes -/

theorem dom_cons_cons (a b c d u : Term) :
    dom (cons a b (cons c d u)) = dom (cons c d u) := by
  rw [dom]
  · simp

/-- With every subscript `0` the only limits are `1` and `ω`. -/
theorem dom_allNil : ∀ X : Term, AllNil X → dom X = nil ∨ dom X = t1 ∨ dom X = tw := by
  intro X
  induction X with
  | nil => intro _; exact Or.inl rfl
  | cons a b t _ ihb iht =>
    intro h
    obtain ⟨ha, hAb, hAt⟩ := h
    subst ha
    cases t with
    | nil =>
      rcases ihb hAb with h1 | h1 | h1
      · rw [dom_eq_nil_iff.mp h1]; exact Or.inr (Or.inl dom_t1)
      · exact Or.inr (Or.inr (dom_block_succ h1))
      · exact Or.inr (Or.inr (dom_block_lim h1))
    | cons c d u =>
      rw [dom_cons_cons]
      exact iht hAt

theorem allNil_addT : ∀ X Y : Term, AllNil X → AllNil Y → AllNil (addT X Y) := by
  intro X
  induction X with
  | nil => intro Y _ hY; rw [addT_nil_left]; exact hY
  | cons a b t _ _ iht =>
    intro Y h hY
    obtain ⟨ha, hb, ht⟩ := h
    subst ha
    exact ⟨rfl, hb, iht Y ht hY⟩

theorem descAll_of_OT : ∀ X : Term, OT X → AllNil X → DescAll X := by
  intro X
  induction X with
  | nil => intro _ _; exact trivial
  | cons a b t _ ihb iht =>
    intro hOT h
    obtain ⟨ha, hb, ht⟩ := h
    subst ha
    exact ⟨ihb (OT_snd hOT) hb, iht (OT_tail hOT) ht, OT_descHead hOT⟩

theorem descAll_addT_t1 : ∀ X : Term, AllNil X → DescAll X → DescAll (addT X t1) := by
  intro X
  induction X with
  | nil => intro _ _; exact ⟨trivial, trivial, rfl⟩
  | cons a b t _ _ iht =>
    intro hA hD
    obtain ⟨ha, hAb, hAt⟩ := hA
    obtain ⟨hDb, hDt, hdh⟩ := hD
    subst ha
    rw [addT_cons]
    refine ⟨hDb, iht hAt hDt, ?_⟩
    cases t with
    | nil =>
      rw [addT_nil_left]
      simp only [descHead, head?]
      exact decide_eq_true (psi_le_psi_of_le (nil_le b))
    | cons c d u =>
      rw [addT_cons]
      exact hdh

/-- One more than a sum is a successor. -/
theorem dom_addT_t1 : ∀ X : Term, dom (addT X t1) = t1 := by
  intro X
  induction X with
  | nil => rw [addT_nil_left]; exact dom_t1
  | cons a b t _ _ iht =>
    obtain ⟨p, q, r, hu⟩ := addT_t1_cons t
    rw [addT_cons, hu, dom_cons_cons, ← hu, iht]


theorem OT_addT_t1 {X : Term} (hOT : OT X) (hA : AllNil X) : OT (addT X t1) :=
  OT_of_desc _ (allNil_addT X t1 hA ⟨rfl, trivial, trivial⟩)
    (descAll_addT_t1 X hA (descAll_of_OT X hOT hA))

theorem lt_addT_t1 (b : Term) : b < addT b t1 := by
  have h := addT_lt b (show (nil : Term) < t1 from nil_lt_cons _ _ _)
  rwa [addT_nil_right] at h

/-- Nothing lies strictly between a term and one more. -/
theorem eq_addT_t1_of_between {b a : Term} (h1 : b < a) (h2 : a ≤ addT b t1) :
    a = addT b t1 := by
  obtain ⟨y, hy, hy1, hy2⟩ := addT_between b (by rwa [addT_nil_right]) h2
  have hyt : y = t1 := by
    rcases le_iff_lt_or_eq.mp hy2 with h | h
    · exact absurd (eq_nil_of_lt_t1 h ▸ hy1) (lt_irrefl nil)
    · exact h
  rw [hy, hyt]

/-- Below an `ω`-limit there is always room for one more. -/
theorem addT_t1_lt {b a : Term} (hd : dom a = tw) (h : b < a) : addT b t1 < a := by
  rcases lt_trichotomy (addT b t1) a with h1 | h1 | h1
  · exact h1
  · exfalso; rw [← h1, dom_addT_t1] at hd; exact absurd hd (by decide)
  · exfalso
    have he := eq_addT_t1_of_between h (le_of_lt h1)
    rw [he, dom_addT_t1] at hd
    exact absurd hd (by decide)

/-! ### The fundamental sequence is cofinal -/

/-- **`X[n]` climbs to `X`.**  Below `ψ_0(Ω)`, anything under a standard form
is under one of the members of its fundamental sequence.  So `[ ]` is not
merely descending — it converges. -/
theorem exists_le_fs : ∀ (X Y : Term), OT X → OT Y → AllNil X → AllNil Y → Y < X →
    ∃ n, Y ≤ fs X (idx X (n + 1)) := by
  intro X
  induction hn : size X using Nat.strong_induction_on generalizing X with
  | _ n ih =>
    cases X with
    | nil => intro Y _ _ _ _ h; exact absurd h (not_lt_nil Y)
    | cons a b t =>
      intro Y hOTX hOTY hAX hAY hlt
      obtain ⟨ha, hAb, hAt⟩ := hAX
      subst ha
      cases t with
      | cons c d u =>
        obtain ⟨hc, hAd, hAu⟩ := hAt
        subst hc
        cases Y with
        | nil => exact ⟨0, nil_le _⟩
        | cons a' e v =>
          obtain ⟨ha', hAe, hAv⟩ := hAY
          subst ha'
          rcases cons_lt_cons_iff.mp hlt with h1 | ⟨h1, h2⟩
          · refine ⟨0, ?_⟩
            rw [fs_sum, idx_sum]
            exact le_of_lt (lt_of_lt_of_le' (cons_lt_psi_iff.mpr h1) (psi_le_cons nil b _))
          · injection h1 with _ heb _
            subst heb
            obtain ⟨m, hm⟩ := ih (size (cons nil d u))
              (by subst hn; simp only [size_cons]; omega) _ rfl v
              (OT_tail hOTX) (OT_tail hOTY) ⟨rfl, hAd, hAu⟩ hAv h2
            exact ⟨m, by rw [fs_sum, idx_sum]; exact cons_le_cons hm⟩
      | nil =>
        rcases dom_allNil b hAb with hd | hd | hd
        · -- X = 1
          rw [dom_eq_nil_iff.mp hd] at hlt ⊢
          refine ⟨0, ?_⟩
          rw [idx_of_dom_t1 dom_t1, fs_t1_nil, eq_nil_of_lt_t1 hlt]
          exact le_refl _
        · -- X = ψ_0(a + 1)
          cases Y with
          | nil => exact ⟨0, nil_le _⟩
          | cons a' e v =>
            obtain ⟨ha', hAe, hAv⟩ := hAY
            subst ha'
            have heb : e < b := by
              rcases psi_lt_psi_iff.mp (cons_lt_psi_iff.mp hlt) with h2 | h2
              · exact absurd h2 (not_lt_nil nil)
              · exact h2.2
            refine ⟨count v, ?_⟩
            rw [idx_of_dom_tw (dom_block_succ hd), fs_block_succ hd,
              show count v + 1 = count (cons nil e v) from rfl]
            exact le_repeatPrin _ _ hOTY ⟨rfl, hAe, hAv⟩
              (le_pred_of_lt (OT_snd hOTX) hd heb)
        · -- X = ψ_0(limit)
          cases Y with
          | nil => exact ⟨0, nil_le _⟩
          | cons a' e v =>
            obtain ⟨ha', hAe, hAv⟩ := hAY
            subst ha'
            have heb : e < b := by
              rcases psi_lt_psi_iff.mp (cons_lt_psi_iff.mp hlt) with h2 | h2
              · exact absurd h2 (not_lt_nil nil)
              · exact h2.2
            obtain ⟨m, hm⟩ := ih (size b) (by subst hn; simp only [size_cons]; omega) _ rfl
              (addT e t1) (OT_snd hOTX) (OT_addT_t1 (OT_snd hOTY) hAe) hAb
              (allNil_addT e t1 hAe ⟨rfl, trivial, trivial⟩) (addT_t1_lt hd heb)
            refine ⟨m, le_of_lt ?_⟩
            rw [idx_of_dom_tw (dom_block_lim hd), fs_block_lim hd]
            refine cons_lt_psi_iff.mpr (psi_lt_psi_iff.mpr (Or.inr ⟨rfl, ?_⟩))
            rw [idx_of_dom_tw hd] at hm
            exact lt_of_lt_of_le' (lt_addT_t1 e) hm



theorem repeatPrin_lt_succ : ∀ (A B : Term) (n : Nat),
    repeatPrin A B n < repeatPrin A B (n + 1) := by
  intro A B n
  induction n with
  | zero => rw [repeatPrin, repeatPrin, repeatPrin]; exact nil_lt_cons _ _ _
  | succ m ih =>
    rw [show repeatPrin A B (m + 1) = cons A B (repeatPrin A B m) from rfl,
      show repeatPrin A B (m + 1 + 1) = cons A B (repeatPrin A B (m + 1)) from rfl]
    exact cons_lt_cons_iff.mpr (Or.inr ⟨rfl, ih⟩)

/-- **The fundamental sequence increases at an `ω`-limit.**  With
`exists_le_fs` this makes `X` the least upper bound of `X[0] < X[1] < ⋯`. -/
theorem fs_idx_lt : ∀ (X : Term), OT X → AllNil X → dom X = tw → ∀ n : Nat,
    fs X (idx X n) < fs X (idx X (n + 1)) := by
  intro X
  induction hs : size X using Nat.strong_induction_on generalizing X with
  | _ N ih =>
    cases X with
    | nil => intro _ _ hd; exact absurd hd (by rw [dom_nil]; decide)
    | cons a b t =>
      intro hOT hA hd n
      obtain ⟨ha, hAb, hAt⟩ := hA
      subst ha
      cases t with
      | cons c d u =>
        obtain ⟨hc, hAd, hAu⟩ := hAt
        subst hc
        rw [dom_cons_cons] at hd
        rw [fs_sum, fs_sum, idx_sum, idx_sum]
        exact cons_lt_cons_iff.mpr (Or.inr ⟨rfl,
          ih (size (cons nil d u)) (by subst hs; simp only [size_cons]; omega) _ rfl
            (OT_tail hOT) ⟨rfl, hAd, hAu⟩ hd n⟩)
      | nil =>
        rcases dom_allNil b hAb with h1 | h1 | h1
        · exfalso
          rw [dom_eq_nil_iff.mp h1] at hd
          exact absurd (dom_t1.symm.trans hd) (by decide)
        · rw [idx_of_dom_tw hd, idx_of_dom_tw hd, fs_block_succ h1, fs_block_succ h1]
          exact repeatPrin_lt_succ _ _ n
        · rw [idx_of_dom_tw hd, idx_of_dom_tw hd, fs_block_lim h1, fs_block_lim h1]
          refine cons_lt_cons_iff.mpr (Or.inl (psi_lt_psi_iff.mpr (Or.inr ⟨rfl, ?_⟩)))
          have := ih (size b) (by subst hs; simp only [size_cons]; omega) b rfl
            (OT_snd hOT) hAb h1 n
          rwa [idx_of_dom_tw h1, idx_of_dom_tw h1] at this

/-- **A term below `ψ_0(Ω)` is the least upper bound of its fundamental
sequence.**  The members increase, each is below the term, and nothing below
the term is above all of them. -/
theorem fs_lub {X : Term} (hOT : OT X) (hA : AllNil X) (hd : dom X = tw) :
    (∀ n : Nat, fs X (idx X n) < fs X (idx X (n + 1)))
      ∧ (∀ n : Nat, fs X (idx X n) < X)
      ∧ (∀ Y : Term, OT Y → AllNil Y → Y < X → ∃ n, Y ≤ fs X (idx X (n + 1))) := by
  have hne : X ≠ nil := by
    intro he; rw [he, dom_nil] at hd; exact absurd hd (by decide)
  exact ⟨fs_idx_lt X hOT hA hd,
    fun n => fs_lt (idx_lt_dom hOT (allNil_lt_tW X hA) hne n),
    fun Y hOTY hAY h => exists_le_fs X Y hOT hOTY hA hAY h⟩


end Googology.Trans.BMS

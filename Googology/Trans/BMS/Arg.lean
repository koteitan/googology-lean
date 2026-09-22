import Googology.Trans.BMS.EpsN
import Googology.Notation.ExBuchholz.Ladder

/-!
# The argument terms `Ω·μ`

`EpsN.lean` writes `Ω·n + B` with `n` copies of `Ω` in front of `B`.  Past
`ω` that is not enough: `Ω·ω` is `ψ_1(1)`, and `Ω·μ` in general is a sum of
`ψ_1(e)`s read off the Cantor normal form of `μ`, by `Ord.psi_one_eq`.

This file builds those terms.  `AllBig W` says every principal part of `W`
names at least `Ω`, which is what makes `addT W B` a standard form for a
small `B` — the parts stay weakly decreasing across the join.  `G_addT`
splits `G` over the join, so a term with `G_0 W` below `W` keeps the
standard-form condition when it becomes the argument of a `ψ_0`.

`exists_argTerm` is the construction: for `μ < ε₀` there is a standard form
naming `Ω·μ` whose `G_0` stays below it, whose head is `ψ_1` of the leading
exponent, and all of whose parts are at least `Ω`.
-/

namespace Googology.Trans.BMS

open Ordinal
open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term

/-! ### Terms all of whose parts are at least `Ω` -/

/-- Every principal part of the term names at least `Ω`. -/
def AllBig : Term → Prop
  | nil => True
  | cons c d t => Ord.Omega 1 ≤ Ord.psi (val d) (val c) ∧ AllBig t

@[simp] theorem AllBig_nil : AllBig nil := trivial

theorem AllBig_cons {c d t : Term} (h : Ord.Omega 1 ≤ Ord.psi (val d) (val c))
    (ht : AllBig t) : AllBig (cons c d t) := ⟨h, ht⟩

theorem AllBig_addT : ∀ x y : Term, AllBig x → AllBig y → AllBig (addT x y) := by
  intro x
  induction x with
  | nil => intro y _ hy; rw [addT_nil_left]; exact hy
  | cons c d t _ _ iht =>
    intro y hx hy
    rw [addT_cons]
    exact ⟨hx.1, iht y hx.2 hy⟩

theorem AllBig_tW : AllBig tW := by
  refine ⟨?_, trivial⟩
  rw [show val nil = 0 from rfl, val_t1, Ord.psi_zero_arg]

/-- The head of a term names no more than the term. -/
theorem head_val_le {B c d : Term} (h : head? B = some (c, d)) :
    Ord.psi (val d) (val c) ≤ val B := by
  cases B with
  | nil => exact absurd h (by simp [head?])
  | cons a b t =>
    rw [show head? (cons a b t) = some (a, b) from rfl] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ (Option.some.injEq _ _ ▸ h)
    rw [val_cons]
    exact self_le_add_right _ _

/-! ### `G` over a join -/

theorem G_addT (a : Term) : ∀ x y : Term, G a (addT x y) = G a x ++ G a y := by
  intro x
  induction x with
  | nil => intro y; rw [addT_nil_left, show G a nil = ([] : List Term) from rfl, List.nil_append]
  | cons c d t _ _ iht =>
    intro y
    rw [addT_cons, G, G, iht y, ← List.append_assoc]

/-! ### Joining a small term on the right -/

theorem OT_addT_of_allBig : ∀ W : Term, OT W → AllBig W → ∀ B : Term, OT B →
    val B ≤ Ord.Omega 1 → OT (addT W B) := by
  intro W
  induction W with
  | nil => intro _ _ B hB _; rw [addT_nil_left]; exact hB
  | cons c d t _ _ iht =>
    intro hW hbig B hB hBval
    have hOTt : OT t := OT_tail hW
    have hIH : OT (addT t B) := iht hOTt hbig.2 B hB hBval
    have hcd : OT (psi c d) := OT_head hW
    have hparts : isOT c = true ∧ isOT d = true ∧ (G c d).all (fun x => decide (x < d)) = true
        ∧ descHead c d t = true := by
      rw [OT, isOT] at hW
      simp only [Bool.and_eq_true] at hW
      exact ⟨hW.1.1.1.1, hW.1.1.1.2, hW.1.1.2, hW.2⟩
    have hdesc : descHead c d (addT t B) = true := by
      cases t with
      | nil =>
        rw [addT_nil_left]
        cases B with
        | nil => rfl
        | cons c' d' u =>
          show (match head? (cons c' d' u) with
            | none => true
            | some (a, b) => decide (psi a b ≤ psi c d)) = true
          refine decide_eq_true (le_of_val_le (OT_head hB) hcd ?_)
          rw [val_psi, val_psi]
          refine le_trans (le_trans ?_ hBval) hbig.1
          exact head_val_le (show head? (cons c' d' u) = some (c', d') from rfl)
      | cons a b s =>
        rw [addT_cons]
        exact hparts.2.2.2
    show isOT (cons c d (addT t B)) = true
    rw [isOT]
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨⟨hparts.1, hparts.2.1⟩, hparts.2.2.1⟩, hIH⟩, hdesc⟩

/-! ### Repeating a principal term with a nonzero subscript -/

/-- `n` copies of `ψ_c(d)` in front of `Z`. -/
def repPsi (c d : Term) : Nat → Term → Term
  | 0, Z => Z
  | n + 1, Z => cons c d (repPsi c d n Z)

theorem val_repPsi (c d Z : Term) : ∀ n : Nat,
    val (repPsi c d n Z) = Ord.psi (val d) (val c) * (n : Ordinal) + val Z := by
  intro n
  induction n with
  | zero => rw [Nat.cast_zero, mul_zero, zero_add]; rfl
  | succ m ih =>
    have hcomm : (1 : Ordinal) + (m : Ordinal) = (m : Ordinal) + 1 := by
      rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add, Nat.add_comm]
    have h1 : ∀ p : Ordinal, p + p * (m : Ordinal) = p * ((m : Ordinal) + 1) := by
      intro p
      rw [← hcomm, mul_add, mul_one]
    show Ord.psi (val d) (val c) + val (repPsi c d m Z) = _
    rw [ih, ← add_assoc, h1, Nat.cast_succ]

theorem AllBig_repPsi {c d : Term} (h : Ord.Omega 1 ≤ Ord.psi (val d) (val c))
    {Z : Term} (hZ : AllBig Z) : ∀ n : Nat, AllBig (repPsi c d n Z) := by
  intro n
  induction n with
  | zero => exact hZ
  | succ m ih => exact ⟨h, ih⟩

theorem descHead_repPsi {c d Z : Term} (h : descHead c d Z = true) :
    ∀ n : Nat, descHead c d (repPsi c d n Z) = true := by
  intro n
  cases n with
  | zero => exact h
  | succ m =>
    show descHead c d (cons c d (repPsi c d m Z)) = true
    rw [descHead]
    exact decide_eq_true (le_refl _)

theorem OT_repPsi {c d Z : Term} (hc : OT c) (hd : OT d)
    (hG : (G c d).all (fun x => decide (x < d)) = true) (hZ : OT Z)
    (h : descHead c d Z = true) : ∀ n : Nat, OT (repPsi c d n Z) := by
  intro n
  induction n with
  | zero => exact hZ
  | succ m ih =>
    show isOT (cons c d (repPsi c d m Z)) = true
    rw [isOT]
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨⟨hc, hd⟩, hG⟩, ih⟩, descHead_repPsi h m⟩

theorem G_repPsi_mem {c d Z : Term} (hc : nil ≤ c) : ∀ {n : Nat} {x : Term},
    x ∈ G nil (repPsi c d n Z) →
      x = d ∨ x ∈ G nil c ∨ x ∈ G nil d ∨ x ∈ G nil Z := by
  intro n
  induction n with
  | zero => exact fun hx => Or.inr (Or.inr (Or.inr hx))
  | succ m ih =>
    intro x hx
    rw [show repPsi c d (m + 1) Z = cons c d (repPsi c d m Z) from rfl, G, if_pos hc] at hx
    rcases List.mem_append.mp hx with h1 | h1
    · rcases List.mem_cons.mp h1 with rfl | h2
      · exact Or.inl rfl
      · rcases List.mem_append.mp h2 with h3 | h3
        · exact Or.inr (Or.inl h3)
        · exact Or.inr (Or.inr (Or.inl h3))
    · exact ih h1

/-! ### The argument term for `Ω·μ` -/

theorem G_t1 : G nil t1 = [nil] := by
  rw [show t1 = cons nil nil nil from rfl, G, if_pos (le_refl nil)]
  rfl

theorem G_t1_of_allNil : ∀ E : Term, AllNil E → G t1 E = [] := by
  intro E
  induction E with
  | nil => intro _; rfl
  | cons c d t _ _ iht =>
    intro h
    obtain ⟨rfl, _, hAt⟩ := h
    have hnot : ¬ (t1 ≤ nil) := not_le_of_lt (nil_lt_cons nil nil nil)
    rw [G, if_neg hnot, List.nil_append]
    exact iht hAt

/-- **The argument term for `Ω·μ`.**  Cantor normal form: the leading part is
`ψ_1` of the leading exponent, repeated as often as the normal form says, and
the rest is the same construction on the remainder. -/
theorem exists_argTerm : ∀ μ : Ordinal.{0}, μ < Ord.eps0 →
    ∃ W : Term, OT W ∧ val W = Ord.Omega 1 * μ ∧ AllBig W ∧ ∀ x ∈ G nil W, x < W := by
  intro μ
  induction μ using WellFoundedLT.induction with
  | _ μ IH =>
    intro hμ
    rcases eq_or_ne μ 0 with rfl | h0
    · refine ⟨nil, rfl, by rw [mul_zero]; rfl, trivial, fun x hx => ?_⟩
      rw [G_nil] at hx
      exact absurd hx (by simp)
    · have hL : Ordinal.log (ω : Ordinal) μ < Ord.eps0 :=
        lt_of_le_of_lt (Ordinal.log_le_self _ _) hμ
      obtain ⟨E, hAE, hDE, hvE⟩ := exists_desc_of_lt_eps0 _ hL
      have hOTE : OT E := OT_of_desc E hAE hDE
      have hple : (ω : Ordinal) ^ Ordinal.log ω μ ≤ μ := Ordinal.opow_log_le_self _ h0
      obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp (Ordinal.div_opow_log_lt μ Ordinal.one_lt_omega0)
      have hdm := Ordinal.div_add_mod μ ((ω : Ordinal) ^ Ordinal.log ω μ)
      rw [hn] at hdm
      have hn0 : n ≠ 0 := by
        intro h
        rw [h, Nat.cast_zero, mul_zero, zero_add] at hdm
        have hlt : μ % (ω : Ordinal) ^ Ordinal.log ω μ < (ω : Ordinal) ^ Ordinal.log ω μ :=
          Ordinal.mod_lt μ (ne_of_gt (Ordinal.opow_pos _ omega0_pos))
        rw [hdm] at hlt
        exact absurd hlt (not_lt.mpr hple)
      have hrlt : μ % (ω : Ordinal) ^ Ordinal.log ω μ < μ :=
        lt_of_lt_of_le (Ordinal.mod_lt μ (ne_of_gt (Ordinal.opow_pos _ omega0_pos))) hple
      obtain ⟨Wr, hOTr, hvr, hbigr, hGr⟩ := IH _ hrlt (lt_trans hrlt hμ)
      have hvY : Ord.psi (val E) (val t1) = Ord.Omega 1 * ω ^ Ordinal.log (ω : Ordinal) μ := by
        rw [hvE, val_t1]
        exact Ord.psi_one_eq (lt_of_lt_of_le (lt_trans hL Ord.eps0_lt_Omega_one)
          (Ord.Omega_le_fpOmega 1))
      have hbigY : Ord.Omega 1 ≤ Ord.psi (val E) (val t1) := by
        rw [hvY]
        exact Ord.le_mul_opow_self _ _
      have hOTpsi : OT (psi t1 E) := by
        show isOT (cons t1 E nil) = true
        rw [isOT]
        simp only [Bool.and_eq_true]
        exact ⟨⟨⟨⟨rfl, hOTE⟩, by rw [G_t1_of_allNil E hAE]; rfl⟩, rfl⟩, rfl⟩
      have hdescr : descHead t1 E Wr = true := by
        cases Wr with
        | nil => rfl
        | cons c d u =>
          show (match head? (cons c d u) with
            | none => true
            | some (a, b) => decide (psi a b ≤ psi t1 E)) = true
          refine decide_eq_true (le_of_val_le (OT_head hOTr) hOTpsi ?_)
          rw [val_psi, val_psi, hvY]
          refine le_trans (head_val_le (show head? (cons c d u) = some (c, d) from rfl)) ?_
          rw [hvr]
          refine le_of_lt ((mul_lt_mul_iff_of_pos_left (Ord.Omega_pos 1)).mpr ?_)
          exact Ordinal.mod_lt μ (show ((ω : Ordinal) ^ Ordinal.log ω μ) ≠ 0 from
            ne_of_gt (Ordinal.opow_pos _ omega0_pos))
      have hOTW : OT (repPsi t1 E n Wr) :=
        OT_repPsi (by decide : OT t1) hOTE (by rw [G_t1_of_allNil E hAE]; rfl) hOTr hdescr n
      have hvW : val (repPsi t1 E n Wr) = Ord.Omega 1 * μ := by
        rw [val_repPsi, hvY, hvr, mul_assoc, ← mul_add, hdm]
      have hΩle : Ord.Omega 1 ≤ val (repPsi t1 E n Wr) := by
        rw [hvW]
        exact Ord.Omega_le_Omega_mul μ (Order.one_le_iff_ne_zero.mpr h0)
      have hne : repPsi t1 E n Wr = cons t1 E (repPsi t1 E (n - 1) Wr) := by
        obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
        rfl
      refine ⟨repPsi t1 E n Wr, hOTW, hvW, AllBig_repPsi hbigY hbigr n, fun x hx => ?_⟩
      rcases G_repPsi_mem (nil_le t1) hx with rfl | h | h | h
      · refine lt_of_val_lt hOTE hOTW ?_
        rw [hvE]
        exact lt_of_lt_of_le (lt_trans hL Ord.eps0_lt_Omega_one) hΩle
      · rw [G_t1] at h
        rcases List.mem_cons.mp h with rfl | h2
        · rw [hne]
          exact nil_lt_cons _ _ _
        · exact absurd h2 (by simp)
      · refine lt_trans (G_lt_of_desc E hAE hDE x h) (lt_of_val_lt hOTE hOTW ?_)
        rw [hvE]
        exact lt_of_lt_of_le (lt_trans hL Ord.eps0_lt_Omega_one) hΩle
      · refine lt_trans (hGr x h) (lt_of_val_lt hOTr hOTW ?_)
        rw [hvr, hvW]
        exact (mul_lt_mul_iff_of_pos_left (Ord.Omega_pos 1)).mpr hrlt

end Googology.Trans.BMS

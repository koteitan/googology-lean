import Googology.Trans.BMS.Reach
import Googology.Notation.ExBuchholz.Opow

/-!
# One row names exactly the ordinals below `ε₀`

`BMS/Calibrate.lean` settles one row as **terms**: the standard forms below
`ψ_0(Ω)` are exactly the matrices' terms.  This file settles it as
**ordinals**.  What was missing is that `val` is onto: every ordinal below
`ε₀` is the value of some standard form, which `exists_desc_of_lt_eps0`
supplies by Cantor normal form.

The construction is the normal form read backwards.  For `α > 0` take
`e = log_ω α`, so that `α = ω^e · n + r` with `n < ω` and `r < ω^e`; the terms
for `e` and `r` come from the induction, `Ord.psi_zero_eq_opow` turns `ψ_0(e)`
into `ω^e`, and `repCons` writes `n` copies of `ψ_0` of the first in front of
the second.  The exponent `e` is below `α` because nothing below `ε₀` is a
fixed point of `ω ^ ·`, which is what `Ord.lt_opow_self_of_lt_eps0` says.

`val_te0` identifies the ceiling: `ψ_0(Ω)` **is** `ε₀`.  So
`exists_matrix_of_lt_eps0` and `val_read_lt_eps0` together say the one-row
matrices name the ordinals below `ε₀` and no others, and with
`Reach.bmsOrdEval_inj` the measure `bmsOrdEval` is a bijection from the
standard one-row matrices onto `ε₀`.
-/

namespace Googology.Trans.BMS
open Ordinal
open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term

/-- On standard forms the value order decides the term order. -/
theorem lt_of_val_lt {x y : Term} (hx : OT x) (hy : OT y) (h : val x < val y) : x < y := by
  rcases lt_trichotomy x y with hlt | rfl | hlt
  · exact hlt
  · exact absurd h (lt_irrefl _)
  · exact absurd (val_lt_val hy hx hlt) (not_lt.mpr h.le)

/-! ### Repeating a principal term -/

/-- `n` copies of `ψ_0(Y)` in front of `Z`. -/
def repCons (Y : Term) : Nat → Term → Term
  | 0, Z => Z
  | n + 1, Z => cons nil Y (repCons Y n Z)

theorem allNil_repCons {Y Z : Term} (hY : AllNil Y) (hZ : AllNil Z) :
    ∀ n, AllNil (repCons Y n Z) := by
  intro n
  induction n with
  | zero => exact hZ
  | succ m ih => exact ⟨rfl, hY, ih⟩

theorem descHead_repCons {Y Z : Term} (hh : descHead nil Y Z = true) :
    ∀ n, descHead nil Y (repCons Y n Z) = true := by
  intro n
  cases n with
  | zero => exact hh
  | succ m =>
    show descHead nil Y (cons nil Y (repCons Y m Z)) = true
    rw [descHead]
    show (decide (psi nil Y ≤ psi nil Y)) = true
    exact decide_eq_true (le_refl _)

theorem descAll_repCons {Y Z : Term} (hY : DescAll Y) (hZ : DescAll Z)
    (hh : descHead nil Y Z = true) : ∀ n, DescAll (repCons Y n Z) := by
  intro n
  induction n with
  | zero => exact hZ
  | succ m ih => exact ⟨hY, ih, descHead_repCons hh m⟩

theorem val_repCons (Y Z : Term) : ∀ n : Nat,
    val (repCons Y n Z) = Ord.psi (val Y) 0 * (n : Ordinal) + val Z := by
  intro n
  induction n with
  | zero => rw [Nat.cast_zero, mul_zero, zero_add]; rfl
  | succ m ih =>
    show Ord.psi (val Y) (val nil) + val (repCons Y m Z) = _
    rw [ih, val_nil, ← add_assoc]
    have hcomm : (1 : Ordinal) + (m : Ordinal) = (m : Ordinal) + 1 := by
      rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add, Nat.add_comm]
    have h1 : ∀ p : Ordinal, p + p * (m : Ordinal) = p * ((m : Ordinal) + 1) := by
      intro p
      rw [← hcomm, mul_add, mul_one]
    rw [h1, Nat.cast_succ]

/-! ### Every ordinal below `ε₀` is a term -/

/-- **`val` is onto the ordinals below `ε₀`**, by Cantor normal form. -/
theorem exists_desc_of_lt_eps0 : ∀ α : Ordinal.{0}, α < Ord.eps0 →
    ∃ X : Term, AllNil X ∧ DescAll X ∧ val X = α := by
  intro α
  induction α using WellFoundedLT.induction with
  | _ α IH =>
    intro hα
    rcases eq_or_ne α 0 with rfl | h0
    · exact ⟨nil, trivial, trivial, rfl⟩
    · have hpos : (0 : Ordinal) < (ω : Ordinal) ^ Ordinal.log ω α :=
        Ordinal.opow_pos _ omega0_pos
      have hle : (ω : Ordinal) ^ Ordinal.log ω α ≤ α := Ordinal.opow_log_le_self ω h0
      have helt : Ordinal.log ω α < Ord.eps0 :=
        lt_of_le_of_lt (Ordinal.log_le_self _ _) hα
      have he : Ordinal.log ω α < α :=
        lt_of_lt_of_le (Ord.lt_opow_self_of_lt_eps0 helt) hle
      have hr : α % (ω : Ordinal) ^ Ordinal.log ω α < α :=
        lt_of_lt_of_le (Ordinal.mod_lt α (ne_of_gt hpos)) hle
      obtain ⟨Y, hAY, hDY, hvY⟩ := IH _ he helt
      obtain ⟨Z, hAZ, hDZ, hvZ⟩ := IH _ hr (lt_trans hr hα)
      obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp (Ordinal.div_opow_log_lt α Ordinal.one_lt_omega0)
      have hOTY : OT (psi nil Y) := OT_of_desc _ ⟨rfl, hAY, trivial⟩ ⟨hDY, trivial, rfl⟩
      have hpsiY : val (psi nil Y) = (ω : Ordinal) ^ Ordinal.log ω α := by
        rw [val_psi, val_nil, hvY, Ord.psi_zero_eq_opow _ helt]
      have hh : descHead nil Y Z = true := by
        cases Z with
        | nil => rfl
        | cons c d u =>
          obtain ⟨hc, hAd, hAu⟩ := hAZ
          subst hc
          have hOTZ : OT (cons nil d u) := OT_of_desc _ ⟨rfl, hAd, hAu⟩ hDZ
          have hOTd : OT (psi nil d) := OT_head hOTZ
          have hlt : val (psi nil d) < val (psi nil Y) := by
            rw [hpsiY, val_psi, val_nil]
            have h1 : Ord.psi (val d) 0 ≤ val (cons nil d u) := by
              show Ord.psi (val d) 0 ≤ Ord.psi (val d) (val nil) + val u
              rw [val_nil]
              exact le_self_add
            rw [hvZ] at h1
            exact lt_of_le_of_lt h1 (Ordinal.mod_lt α (ne_of_gt hpos))
          show (match head? (cons nil d u) with
            | none => true
            | some (c, e) => decide (psi c e ≤ psi nil Y)) = true
          exact decide_eq_true (le_of_lt (lt_of_val_lt hOTd hOTY hlt))
      refine ⟨repCons Y n Z, allNil_repCons hAY hAZ n, descAll_repCons hDY hDZ hh n, ?_⟩
      rw [val_repCons, hvY, hvZ, Ord.psi_zero_eq_opow _ helt]
      have hdm := Ordinal.div_add_mod α ((ω : Ordinal) ^ Ordinal.log ω α)
      rw [hn] at hdm
      exact hdm

theorem exists_OT_of_lt_eps0 {α : Ordinal.{0}} (h : α < Ord.eps0) :
    ∃ X : Term, OT X ∧ AllNil X ∧ val X = α := by
  obtain ⟨X, hA, hD, hv⟩ := exists_desc_of_lt_eps0 α h
  exact ⟨X, OT_of_desc X hA hD, hA, hv⟩

/-! ### The ceiling -/

theorem val_t1 : val t1 = 1 := by
  rw [show t1 = psi nil nil from rfl, val_psi, val_nil, Ord.psi_zero_arg, Ord.Omega_zero]

theorem val_tW : val tW = Ord.Omega 1 := by
  rw [show tW = psi t1 nil from rfl, val_psi, val_nil, val_t1, Ord.psi_zero_arg]

theorem val_addT : ∀ x y : Term, val (addT x y) = val x + val y := by
  intro x
  induction x with
  | nil => intro y; rw [addT_nil_left, val_nil, zero_add]
  | cons a b t _ _ iht =>
    intro y
    show val (cons a b (addT t y)) = _
    rw [val_cons, val_cons, iht y, add_assoc]

/-- The term `ψ_0(Ω + Ω)`. -/
abbrev te1 : Term := psi nil (addT tW tW)

/-- **`ψ_0(Ω + Ω)` is `ε₁`.** -/
theorem val_te1 : val te1 = Ord.eps1 := by
  rw [show te1 = psi nil (addT tW tW) from rfl, val_psi, val_nil, val_addT, val_tW,
    Ord.psi_Omega_two]

/-! ### Terms with `Ω` in the argument

`OT_of_desc` covers the terms whose subscripts are all `0`.  Above `ε₀` the
arguments carry `Ω`, and `OT_psi_Omega_add` is the standard-form condition
there: what it asks of `B` is that `G_0` sees nothing in it that reaches
`Ω + B`. -/

theorem G_addT_tW (B : Term) : G nil (addT tW B) = nil :: nil :: G nil B := by
  show G nil (cons t1 nil B) = _
  rw [G, if_pos (nil_le t1)]
  show nil :: (G nil t1 ++ G nil nil) ++ G nil B = _
  rw [show G nil t1 = [nil] from rfl, show G nil nil = ([] : List Term) from rfl]
  rfl

/-- **`ψ_0(Ω + B)` is a standard form** when `B` is one whose `G_0` stays
below `Ω + B` and whose head is at most `Ω`. -/
theorem OT_psi_Omega_add {B : Term} (hB : OT B)
    (hG : ∀ x ∈ G nil B, x < addT tW B) (hhead : descHead t1 nil B = true) :
    OT (psi nil (addT tW B)) := by
  have hne : nil < addT tW B := by
    show nil < cons t1 nil B
    exact nil_lt_cons _ _ _
  have hOTsum : isOT (addT tW B) = true := by
    show isOT (cons t1 nil B) = true
    rw [isOT]
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, hB⟩, hhead⟩
  show isOT (cons nil (addT tW B) nil) = true
  rw [isOT]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨rfl, hOTsum⟩, ?_⟩, rfl⟩, rfl⟩
  rw [G_addT_tW]
  refine List.all_eq_true.mpr (fun x hx => decide_eq_true ?_)
  rcases List.mem_cons.mp hx with rfl | h1
  · exact hne
  · rcases List.mem_cons.mp h1 with rfl | h2
    · exact hne
    · exact hG x h2

/-- The term `ψ_0(Ω + 1)`. -/
abbrev tew : Term := psi nil (addT tW t1)

/-- **`ψ_0(Ω + 1)` is a standard form, and it names `ε₀·ω`.** -/
theorem OT_tew : OT tew := by decide

theorem val_tew : val tew = Ord.eps0 * Ordinal.omega0 := by
  rw [show tew = psi nil (addT tW t1) from rfl, val_psi, val_nil, val_addT, val_tW, val_t1,
    Ord.psi_Omega_add_one]

theorem OT_te1 : OT te1 := by decide

/-- **`ψ_0(Ω)` is `ε₀`.** -/
theorem val_te0 : val te0 = Ord.eps0 := by
  rw [show te0 = psi nil tW from rfl, val_psi, val_nil, val_tW, Ord.psi_Omega_one]

/-! ### The matrices -/

/-- **Every ordinal below `ε₀` is named by a one-row matrix.** -/
theorem exists_matrix_of_lt_eps0 {α : Ordinal.{0}} (h : α < Ord.eps0) :
    ∃ l : List Nat, Col 0 l ∧ OT (read 0 l) ∧ val (read 0 l) = α := by
  obtain ⟨X, hOT, hA, hv⟩ := exists_OT_of_lt_eps0 h
  refine ⟨unread 0 X, col_unread X hA 0, ?_, ?_⟩
  · rw [read_unread X hA 0]; exact hOT
  · rw [read_unread X hA 0]; exact hv

/-- **And a one-row matrix names nothing else.** -/
theorem val_read_lt_eps0 {l : List Nat} (hOT : OT (read 0 l)) : val (read 0 l) < Ord.eps0 := by
  rw [← val_te0]
  exact val_lt_val hOT OT_te0 (read_lt_e0 0 l)

/-- **The ordinal measure of the primitive sequence system is onto `ε₀`.**
With `bmsOrdEval_inj` for the other half, it is a bijection between the
standard one-row matrices and the ordinals below `ε₀`. -/
theorem exists_bms_of_lt_eps0 {α : Ordinal.{0}} (h : α < Ord.eps0) :
    ∃ A : (Googology.Notation.BMS.bms 1).State, bmsOrdEval.val A = α := by
  obtain ⟨l, hc, hOT, hv⟩ := exists_matrix_of_lt_eps0 h
  obtain ⟨A, hStd, hE⟩ := exists_std_of_col hc hOT
  refine ⟨⟨A, hStd⟩, ?_⟩
  rw [bmsOrdEval_val]
  show val (read 0 (entries A)) = α
  rw [hE]
  exact hv

/-- **And below `ε₀` it stays.** -/
theorem bmsOrdEval_lt_eps0 (A : (Googology.Notation.BMS.bms 1).State) :
    bmsOrdEval.val A < Ord.eps0 := by
  rw [← val_te0]
  exact bmsOrdEval_lt_e0 A

/-! ### Six matrices, read off

The reading is a function, so the ordinal a small matrix names can be computed
and stated.  These are the first entries of the published correspondence
tables, and they agree — with one thing worth recording.  The table in
[yaBMS](https://github.com/koteitan/yaBMS) lists `(0)(1)(1)` and `(0)(1)(2)`
twice each, with different values: `ω + 2` and `ω²` for the first, `ω + 3` and
`ω^ω` for the second.  One of each pair has to be wrong, and
`val_read_one_one` and `val_read_one_two` say which: the values are `ω²` and
`ω^ω`. -/

theorem val_cons_nil {X t : Term} (hOT : OT X) (hA : AllNil X) :
    val (cons nil X t) = (ω : Ordinal) ^ val X + val t := by
  rw [val_cons, val_nil]
  congr 1
  refine Ord.psi_zero_eq_opow _ ?_
  rw [← val_te0]
  exact val_lt_val hOT OT_te0 (allNil_lt_e0 X hA)

theorem allNil_t1 : AllNil t1 := ⟨rfl, trivial, trivial⟩

theorem OT_t1 : OT t1 := by decide

/-- `(0)` names `1`. -/
theorem val_read_zero : val (read 0 [0]) = 1 := by
  rw [show read 0 [0] = t1 from by simp [read_cons]]
  exact val_t1

/-- `(0)(0)` names `2`. -/
theorem val_read_zero_zero : val (read 0 [0, 0]) = 2 := by
  rw [show read 0 [0, 0] = cons nil nil t1 from by simp [read_cons],
    val_cons_nil (X := nil) (t := t1) rfl trivial, val_nil, Ordinal.opow_zero, val_t1]
  norm_num

/-- `(0)(1)` names `ω`. -/
theorem val_read_one : val (read 0 [0, 1]) = Ordinal.omega0 := by
  rw [show read 0 [0, 1] = psi nil t1 from by simp [read_cons],
    show psi nil t1 = cons nil t1 nil from rfl,
    val_cons_nil OT_t1 allNil_t1, val_nil, add_zero, val_t1, Ordinal.opow_one]

/-- `(0)(1)(0)` names `ω + 1`. -/
theorem val_read_one_zero : val (read 0 [0, 1, 0]) = Ordinal.omega0 + 1 := by
  rw [show read 0 [0, 1, 0] = cons nil t1 t1 from by simp [read_cons],
    val_cons_nil OT_t1 allNil_t1, val_t1, Ordinal.opow_one]

/-- **`(0)(1)(1)` names `ω²`**, not `ω + 2`. -/
theorem val_read_one_one : val (read 0 [0, 1, 1]) = (ω : Ordinal) ^ (2 : Ordinal) := by
  have h2 : val (cons nil nil t1) = 2 := val_read_zero_zero ▸ by
    rw [show read 0 [0, 0] = cons nil nil t1 from by simp [read_cons]]
  rw [show read 0 [0, 1, 1] = psi nil (cons nil nil t1) from by simp [read_cons],
    show psi nil (cons nil nil t1) = cons nil (cons nil nil t1) nil from rfl,
    val_cons_nil (X := cons nil nil t1) (t := nil) (by decide) ⟨rfl, trivial, allNil_t1⟩,
    val_nil, add_zero, h2]

/-- `(0)(1)(2)` names `ω^ω`. -/
theorem val_read_one_two :
    val (read 0 [0, 1, 2]) = (ω : Ordinal) ^ (ω : Ordinal) := by
  have hw : val (psi nil t1) = Ordinal.omega0 := val_read_one ▸ by
    rw [show read 0 [0, 1] = psi nil t1 from by simp [read_cons]]
  rw [show read 0 [0, 1, 2] = psi nil (psi nil t1) from by simp [read_cons],
    show psi nil (psi nil t1) = cons nil (psi nil t1) nil from rfl,
    val_cons_nil (X := psi nil t1) (t := nil) (by decide) ⟨rfl, allNil_t1, trivial⟩,
    val_nil, add_zero, hw]

end Googology.Trans.BMS

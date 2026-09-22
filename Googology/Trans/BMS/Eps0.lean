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

`exists_OT_of_lt_eps1` carries the same construction one level up: above `ε₀`
the leading term is `ψ_0(Ω + B)`, whose value `Ord.psi_Omega_add_eq` computes,
and the standard-form condition there is `OT_cons_Omega`.  So `val` is onto
the ordinals below `ε₁` as well.

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

theorem val_le_val {x y : Term} (hx : OT x) (hy : OT y) (h : x ≤ y) : val x ≤ val y := by
  rcases le_iff_lt_or_eq.mp h with hlt | rfl
  · exact (val_lt_val hx hy hlt).le
  · exact le_refl _

theorem le_of_val_le {x y : Term} (hx : OT x) (hy : OT y) (h : val x ≤ val y) : x ≤ y := by
  rcases lt_trichotomy x y with hlt | rfl | hlt
  · exact le_of_lt hlt
  · exact le_refl _
  · exact absurd (val_lt_val hy hx hlt) (not_lt.mpr h)

theorem OT_tW : OT tW := by decide

theorem lt_tW_of_val_lt {X : Term} (hOT : OT X) (h : val X < Ord.Omega 1) : X < tW :=
  lt_of_val_lt hOT OT_tW (by rw [val_tW]; exact h)

theorem val_lt_Omega_of_lt_tW {X : Term} (hOT : OT X) (h : X < tW) : val X < Ord.Omega 1 := by
  rw [← val_tW]
  exact val_lt_val hOT OT_tW h

theorem descHead_of_lt_tW {X : Term} (h : X < tW) : descHead t1 nil X = true := by
  cases X with
  | nil => rfl
  | cons c d u =>
    show (match head? (cons c d u) with
      | none => true
      | some (c', d') => decide (psi c' d' ≤ psi t1 nil)) = true
    refine decide_eq_true (le_of_lt ?_)
    rcases le_iff_lt_or_eq.mp (psi_le_cons c d u) with h1 | h1
    · exact lt_trans h1 h
    · rw [h1]; exact h

theorem OT_addT_tW {X : Term} (hOT : OT X) (h : X < tW) : OT (addT tW X) := by
  show isOT (cons t1 nil X) = true
  rw [isOT]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, hOT⟩, descHead_of_lt_tW h⟩

theorem lt_addT_tW {X : Term} (hOT : OT X) (h : X < tW) : X < addT tW X := by
  refine lt_of_val_lt hOT (OT_addT_tW hOT h) ?_
  rw [val_addT, val_tW]
  exact lt_of_lt_of_le (val_lt_Omega_of_lt_tW hOT h) (self_le_add_right _ _)

theorem addT_tW_le_addT_tW {X Y : Term} (hX : OT X) (hY : OT Y) (hXt : X < tW) (hYt : Y < tW)
    (h : X ≤ Y) : addT tW X ≤ addT tW Y := by
  refine le_of_val_le (OT_addT_tW hX hXt) (OT_addT_tW hY hYt) ?_
  rw [val_addT, val_addT, add_le_add_iff_left]
  exact val_le_val hX hY h

theorem G_cons_Omega (B t : Term) :
    G nil (cons nil (addT tW B) t) = addT tW B :: nil :: nil :: (G nil B ++ G nil t) := by
  rw [G, if_pos (nil_le nil), show G nil nil = ([] : List Term) from rfl, List.nil_append,
    G_addT_tW]
  rfl

/-- **`ψ_0(Ω + B)` in front of `t` is a standard form** when `B` is one whose
`G_0` stays below `Ω + B`, whose head is at most `Ω`, and `t` does not rise
above it. -/
theorem OT_cons_Omega {B t : Term} (hB : OT B)
    (hG : ∀ x ∈ G nil B, x < addT tW B) (hhead : descHead t1 nil B = true)
    (hOTt : OT t) (hdesc : descHead nil (addT tW B) t = true) :
    OT (cons nil (addT tW B) t) := by
  have hne : nil < addT tW B := by
    show nil < cons t1 nil B
    exact nil_lt_cons _ _ _
  have hOTsum : isOT (addT tW B) = true := by
    show isOT (cons t1 nil B) = true
    rw [isOT]
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, hB⟩, hhead⟩
  show isOT (cons nil (addT tW B) t) = true
  rw [isOT]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨rfl, hOTsum⟩, ?_⟩, hOTt⟩, hdesc⟩
  rw [G_addT_tW]
  refine List.all_eq_true.mpr (fun x hx => decide_eq_true ?_)
  rcases List.mem_cons.mp hx with rfl | h1
  · exact hne
  · rcases List.mem_cons.mp h1 with rfl | h2
    · exact hne
    · exact hG x h2

/-- **`ψ_0(Ω + B)` is a standard form** under the same conditions. -/
theorem OT_psi_Omega_add {B : Term} (hB : OT B)
    (hG : ∀ x ∈ G nil B, x < addT tW B) (hhead : descHead t1 nil B = true) :
    OT (psi nil (addT tW B)) :=
  OT_cons_Omega hB hG hhead rfl rfl

/-- `n` copies of `ψ_0(Ω + B)` in front of `t`. -/
def repOmega (B : Term) : Nat → Term → Term
  | 0, t => t
  | n + 1, t => cons nil (addT tW B) (repOmega B n t)

theorem val_repOmega (B t : Term) : ∀ n : Nat,
    val (repOmega B n t) = Ord.psi (val (addT tW B)) 0 * (n : Ordinal) + val t := by
  intro n
  induction n with
  | zero => rw [Nat.cast_zero, mul_zero, zero_add]; rfl
  | succ m ih =>
    have hcomm : (1 : Ordinal) + (m : Ordinal) = (m : Ordinal) + 1 := by
      rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add, Nat.add_comm]
    have h1 : ∀ p : Ordinal, p + p * (m : Ordinal) = p * ((m : Ordinal) + 1) := by
      intro p
      rw [← hcomm, mul_add, mul_one]
    show Ord.psi (val (addT tW B)) (val nil) + val (repOmega B m t) = _
    rw [val_nil, ih, ← add_assoc, h1, Nat.cast_succ]

theorem descHead_repOmega {B t : Term} (hdesc : descHead nil (addT tW B) t = true) :
    ∀ n, descHead nil (addT tW B) (repOmega B n t) = true := by
  intro n
  cases n with
  | zero => exact hdesc
  | succ m =>
    show descHead nil (addT tW B) (cons nil (addT tW B) (repOmega B m t)) = true
    rw [descHead]
    exact decide_eq_true (le_refl _)

theorem OT_repOmega {B t : Term} (hB : OT B) (hBt : B < tW)
    (hGB : ∀ x ∈ G nil B, x < addT tW B) (ht : OT t)
    (hdesc : descHead nil (addT tW B) t = true) : ∀ n, OT (repOmega B n t) := by
  intro n
  induction n with
  | zero => exact ht
  | succ m ih =>
    exact OT_cons_Omega hB hGB (descHead_of_lt_tW hBt) ih (descHead_repOmega hdesc m)

theorem G_repOmega_mem {B t : Term} {n : Nat} {x : Term} (hx : x ∈ G nil (repOmega B n t)) :
    x = addT tW B ∨ x = nil ∨ x ∈ G nil B ∨ x ∈ G nil t := by
  induction n with
  | zero => exact Or.inr (Or.inr (Or.inr hx))
  | succ m ih =>
    rw [show repOmega B (m + 1) t = cons nil (addT tW B) (repOmega B m t) from rfl,
      G_cons_Omega] at hx
    rcases List.mem_cons.mp hx with rfl | h1
    · exact Or.inl rfl
    · rcases List.mem_cons.mp h1 with rfl | h2
      · exact Or.inr (Or.inl rfl)
      · rcases List.mem_cons.mp h2 with rfl | h3
        · exact Or.inr (Or.inl rfl)
        · rcases List.mem_append.mp h3 with h4 | h4
          · exact Or.inr (Or.inr (Or.inl h4))
          · exact ih h4

/-- The term `ψ_0(Ω + 1)`. -/
abbrev tew : Term := psi nil (addT tW t1)

/-- **`ψ_0(Ω + 1)` is a standard form, and it names `ε₀·ω`.** -/
theorem OT_tew : OT tew := by decide

theorem val_tew : val tew = Ord.eps0 * Ordinal.omega0 := by
  rw [show tew = psi nil (addT tW t1) from rfl, val_psi, val_nil, val_addT, val_tW, val_t1,
    Ord.psi_Omega_add_one]

theorem OT_te1 : OT te1 := by decide

/-- The term `ψ_0(Ω + 2)`, which names `ε₀·ω²`. -/
abbrev tew2 : Term := psi nil (addT tW (addT t1 t1))

theorem OT_tew2 : OT tew2 := by decide

theorem val_tew2 : val tew2 = Ord.eps0 * Ordinal.omega0 * Ordinal.omega0 := by
  have h2 : val (addT t1 t1) = 2 := by
    rw [val_addT, val_t1]
    norm_num
  have h2lt : (2 : Ordinal) < Ord.eps1 := by
    refine lt_of_lt_of_le ?_ (le_trans Ord.omega0_le_eps0 Ord.eps0_le_eps1)
    exact_mod_cast Ordinal.natCast_lt_omega0 2
  rw [show tew2 = psi nil (addT tW (addT t1 t1)) from rfl, val_psi, val_nil, val_addT, val_tW,
    h2, Ord.psi_Omega_add_eq 2 h2lt,
    show (2 : Ordinal) = 1 + 1 from by norm_num, Ordinal.opow_add, Ordinal.opow_one, ← mul_assoc]

/-- The term `ω²`, that is `ψ_0(2)`. -/
abbrev tw2 : Term := psi nil (addT t1 t1)

theorem OT_tw2 : OT tw2 := by decide

theorem val_tw2 : val tw2 = Ordinal.omega0 * Ordinal.omega0 := by
  have h2 : val (addT t1 t1) = 2 := by
    rw [val_addT, val_t1]
    norm_num
  have h2lt : (2 : Ordinal) < Ord.eps0 := by
    refine lt_of_lt_of_le ?_ Ord.omega0_le_eps0
    exact_mod_cast Ordinal.natCast_lt_omega0 2
  rw [show tw2 = psi nil (addT t1 t1) from rfl, val_psi, val_nil, h2,
    Ord.psi_zero_eq_opow 2 h2lt, show (2 : Ordinal) = 1 + 1 from by norm_num,
    Ordinal.opow_add, Ordinal.opow_one]

/-- The term `ω`, that is `ψ_0(1)`. -/
abbrev tw : Term := psi nil t1

theorem OT_tw : OT tw := by decide

theorem val_tw : val tw = Ordinal.omega0 := by
  rw [show tw = psi nil t1 from rfl, val_psi, val_nil, val_t1,
    Ord.psi_zero_eq_opow 1 Ord.one_lt_eps0, Ordinal.opow_one]


/-- **`ψ_0(Ω)` is `ε₀`.** -/
theorem val_te0 : val te0 = Ord.eps0 := by
  rw [show te0 = psi nil tW from rfl, val_psi, val_nil, val_tW, Ord.psi_Omega_one]

/-- The term `ε₀ + 1`. -/
abbrev te0_one : Term := addT te0 t1

theorem OT_te0_one : OT te0_one := by decide

theorem val_te0_one : val te0_one = Ord.eps0 + 1 := by
  rw [show te0_one = addT te0 t1 from rfl, val_addT, val_te0, val_t1]

/-- The term `ε₀ + ω`. -/
abbrev te0_w : Term := addT te0 tw

theorem OT_te0_w : OT te0_w := by decide

theorem val_te0_w : val te0_w = Ord.eps0 + Ordinal.omega0 := by
  rw [show te0_w = addT te0 tw from rfl, val_addT, val_te0, val_tw]

/-! ### `val` is onto below `ε₁` -/

theorem lt_of_lt_of_le' {x y z : Term} (h1 : x < y) (h2 : y ≤ z) : x < z := by
  rcases le_iff_lt_or_eq.mp h2 with h | rfl
  · exact lt_trans h1 h
  · exact h1

theorem descHead_of_val_lt {a b t : Term} (hOTt : OT t) (hOTp : OT (psi a b))
    (h : val t < val (psi a b)) : descHead a b t = true := by
  cases t with
  | nil => rfl
  | cons c d u =>
    show (match head? (cons c d u) with
      | none => true
      | some (c', d') => decide (psi c' d' ≤ psi a b)) = true
    refine decide_eq_true (le_of_lt ?_)
    rcases le_iff_lt_or_eq.mp (psi_le_cons c d u) with h1 | h1
    · exact lt_trans h1 (lt_of_val_lt hOTt hOTp h)
    · rw [h1]
      exact lt_of_val_lt hOTt hOTp h

/-- **Every ordinal below `ε₁` is the value of a standard form.**  Below `ε₀`
that is `exists_desc_of_lt_eps0`; above it the leading term is `ψ_0(Ω + B)`
for the `B` naming `log_ω (α / ε₀)`, repeated as often as the normal form
says, and the rest follows by the same construction. -/
theorem exists_OT_of_lt_eps1 : ∀ α : Ordinal.{0}, α < Ord.eps1 →
    ∃ X : Term, OT X ∧ val X = α ∧ ∀ x ∈ G nil X, x < addT tW X := by
  intro α
  induction α using WellFoundedLT.induction with
  | _ α IH =>
    intro hα
    have hΩ : α < Ord.Omega 1 := lt_of_lt_of_le hα Ord.eps1_le_Omega_one
    rcases lt_or_ge α Ord.eps0 with hsmall | hbig
    · obtain ⟨X, hA, hD, hv⟩ := exists_desc_of_lt_eps0 α hsmall
      have hOTX : OT X := OT_of_desc X hA hD
      have hXt : X < tW := lt_tW_of_val_lt hOTX (by rw [hv]; exact hΩ)
      exact ⟨X, hOTX, hv, fun x hx =>
        lt_trans (G_lt_of_desc X hA hD x hx) (lt_addT_tW hOTX hXt)⟩
    rcases eq_or_lt_of_le hbig with heq | hbig'
    · refine ⟨te0, OT_te0, by rw [val_te0, heq], fun x hx => ?_⟩
      rw [show G nil te0 = [tW, nil, nil] from rfl] at hx
      rcases List.mem_cons.mp hx with rfl | h1
      · show tW < addT tW te0
        decide
      · rcases List.mem_cons.mp h1 with rfl | h2
        · exact nil_lt_cons _ _ _
        · rcases List.mem_cons.mp h2 with rfl | h3
          · exact nil_lt_cons _ _ _
          · exact absurd h3 (by simp)
    · -- ε₀ < α
      have heps0pos : (0 : Ordinal) < Ord.eps0 := Ord.eps0_pos
      have hdm : Ord.eps0 * (α / Ord.eps0) + α % Ord.eps0 = α :=
        Ordinal.div_add_mod α Ord.eps0
      have hyle : α / Ord.eps0 ≤ α := by
        refine le_trans (Ordinal.le_mul_right (α / Ord.eps0) heps0pos) ?_
        exact le_trans (self_le_add_right _ _) (le_of_eq hdm)
      have hy0 : α / Ord.eps0 ≠ 0 := by
        intro h
        rw [h, mul_zero, zero_add] at hdm
        exact absurd (hdm ▸ Ordinal.mod_lt α (ne_of_gt heps0pos)) (not_lt.mpr hbig)
      have hlog : (ω : Ordinal) ^ Ordinal.log ω (α / Ord.eps0) ≤ α / Ord.eps0 :=
        Ordinal.opow_log_le_self ω hy0
      have he : Ordinal.log (ω : Ordinal) (α / Ord.eps0) < α := by
        rcases lt_or_ge (α / Ord.eps0) α with h | h
        · exact lt_of_le_of_lt (Ordinal.log_le_self _ _) h
        · rw [le_antisymm hyle h]
          exact Ord.log_lt_self_of_lt_eps1 hbig' hα
      obtain ⟨B, hOTB, hvB, hGB⟩ := IH _ he (lt_trans he hα)
      have hBt : B < tW := lt_tW_of_val_lt hOTB (by rw [hvB]; exact lt_trans he hΩ)
      have hP : Ord.psi (val (addT tW B)) 0
          = Ord.eps0 * (ω : Ordinal) ^ Ordinal.log ω (α / Ord.eps0) := by
        rw [val_addT, val_tW, hvB]
        exact Ord.psi_Omega_add_eq _ (lt_trans he hα)
      obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp
        (Ordinal.div_opow_log_lt (α / Ord.eps0) Ordinal.one_lt_omega0)
      have hsplit : (ω : Ordinal) ^ Ordinal.log ω (α / Ord.eps0) * (n : Ordinal)
          + (α / Ord.eps0) % (ω : Ordinal) ^ Ordinal.log ω (α / Ord.eps0) = α / Ord.eps0 := by
        have h := Ordinal.div_add_mod (α / Ord.eps0)
          ((ω : Ordinal) ^ Ordinal.log ω (α / Ord.eps0))
        rwa [hn] at h
      have hstep : Ord.eps0 * ((α / Ord.eps0) % (ω : Ordinal) ^ Ordinal.log ω (α / Ord.eps0))
          + α % Ord.eps0
            < Ord.eps0 * (ω : Ordinal) ^ Ordinal.log ω (α / Ord.eps0) := by
        refine lt_of_lt_of_le ((add_lt_add_iff_left _).mpr
          (Ordinal.mod_lt α (ne_of_gt heps0pos))) ?_
        rw [← mul_add_one]
        refine mul_le_mul_right ?_ _
        rw [← Order.succ_eq_add_one]
        exact Order.succ_le_of_lt (Ordinal.mod_lt _ (ne_of_gt (Ordinal.opow_pos _ omega0_pos)))
      have hr : Ord.eps0 * ((α / Ord.eps0) % (ω : Ordinal) ^ Ordinal.log ω (α / Ord.eps0))
          + α % Ord.eps0 < α := by
        refine lt_of_lt_of_le hstep ?_
        refine le_trans (mul_le_mul_right hlog Ord.eps0) ?_
        exact le_trans (self_le_add_right _ _) (le_of_eq hdm)
      obtain ⟨T, hOTT, hvT, hGT⟩ := IH _ hr (lt_trans hr hα)
      have hvX : val (repOmega B n T) = α := by
        rw [val_repOmega, hP, hvT, mul_assoc, ← add_assoc, ← mul_add, hsplit, hdm]
      have hOTpsi : OT (psi nil (addT tW B)) := OT_psi_Omega_add hOTB hGB (descHead_of_lt_tW hBt)
      have hdesc : descHead nil (addT tW B) T = true := by
        refine descHead_of_val_lt hOTT hOTpsi ?_
        rw [hvT, val_psi, val_nil, hP]
        exact hstep
      have hOTX : OT (repOmega B n T) := OT_repOmega hOTB hBt hGB hOTT hdesc n
      have hXt : repOmega B n T < tW := lt_tW_of_val_lt hOTX (by rw [hvX]; exact hΩ)
      have hTt : T < tW := lt_tW_of_val_lt hOTT (by rw [hvT]; exact lt_trans hr hΩ)
      refine ⟨repOmega B n T, hOTX, hvX, fun x hx => ?_⟩
      rcases G_repOmega_mem hx with rfl | rfl | h | h
      · refine lt_of_val_lt (OT_addT_tW hOTB hBt) (OT_addT_tW hOTX hXt) ?_
        rw [val_addT, val_addT, add_lt_add_iff_left, hvB, hvX]
        exact he
      · show nil < addT tW (repOmega B n T)
        exact nil_lt_cons _ _ _
      · refine lt_of_lt_of_le' (hGB x h) (addT_tW_le_addT_tW hOTB hOTX hBt hXt ?_)
        exact le_of_val_le hOTB hOTX (by rw [hvB, hvX]; exact he.le)
      · refine lt_of_lt_of_le' (hGT x h) (addT_tW_le_addT_tW hOTT hOTX hTt hXt ?_)
        exact le_of_val_le hOTT hOTX (by rw [hvT, hvX]; exact hr.le)

/-- **The standard forms below `ψ_0(Ω+Ω)` name exactly the ordinals below
`ε₁`.**  One direction is `exists_OT_of_lt_eps1`, the other is that `val` is
monotone and `ψ_0(Ω+Ω)` is `ε₁`. -/
theorem exists_OT_lt_te1 {α : Ordinal.{0}} (h : α < Ord.eps1) :
    ∃ X : Term, OT X ∧ X < te1 ∧ val X = α := by
  obtain ⟨X, hOT, hv, _⟩ := exists_OT_of_lt_eps1 α h
  exact ⟨X, hOT, lt_of_val_lt hOT OT_te1 (by rw [hv, val_te1]; exact h), hv⟩

/-- **Below `ε₁`, `val` is a bijection from the standard forms onto the
ordinals.**  Existence is `exists_OT_lt_te1`, uniqueness `val_inj_of_OT`: the
two halves the source asks for, on that initial segment. -/
theorem existsUnique_OT_lt_te1 {α : Ordinal.{0}} (h : α < Ord.eps1) :
    ∃! X : Term, OT X ∧ X < te1 ∧ val X = α := by
  obtain ⟨X, hOT, hlt, hv⟩ := exists_OT_lt_te1 h
  refine ⟨X, ⟨hOT, hlt, hv⟩, fun Y hY => ?_⟩
  exact val_inj_of_OT hY.1 hOT (by rw [hY.2.2, hv])

/-- The same below `ε₀`, where the terms are the all-nil ones. -/
theorem existsUnique_OT_lt_te0 {α : Ordinal.{0}} (h : α < Ord.eps0) :
    ∃! X : Term, OT X ∧ X < te0 ∧ val X = α := by
  obtain ⟨X, hOT, hA, hv⟩ := exists_OT_of_lt_eps0 h
  refine ⟨X, ⟨hOT, allNil_lt_e0 X hA, hv⟩, fun Y hY => ?_⟩
  exact val_inj_of_OT hY.1 hOT (by rw [hY.2.2, hv])

theorem val_lt_eps1_of_lt_te1 {X : Term} (hOT : OT X) (h : X < te1) : val X < Ord.eps1 := by
  rw [← val_te1]
  exact val_lt_val hOT OT_te1 h

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

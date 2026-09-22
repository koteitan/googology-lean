import Googology.Trans.BMS.Eps0
import Googology.Notation.ExBuchholz.Eps

/-!
# `val` is onto the ordinals below every `ε_n`

`Eps0.lean` carries the construction two levels: Cantor normal form below
`ε₀`, and the leading term `ψ_0(Ω + B)` below `ε₁`.  This file carries it to
every finite level, alongside `Notation/ExBuchholz/Eps.lean`, which says what
the collapse is worth there: `ψ_0(Ω·(n+1) + a) = ε_n · ω^a`.

`OmegaTerm n B` is `Ω·n + B` as a term — `n` copies of `Ω` in front of `B` —
and `exists_OT_of_lt_epsN` is the statement, by induction on `n` with the
`ε₁` proof as its step.  The invariant it carries is the standard-form
condition the next level needs: `G_0` of the term stays below `Ω·n` plus the
term, which at `n = 0` is what the all-nil terms satisfy and at `n = 1` is
`Eps0.lean`'s condition.
-/

namespace Googology.Trans.BMS

open Ordinal
open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term

/-! ### `Ω·m + B` as a term -/

/-- `Ω·m + B`: `m` copies of `Ω` in front of `B`. -/
def OmegaTerm : Nat → Term → Term
  | 0, B => B
  | m + 1, B => cons t1 nil (OmegaTerm m B)

@[simp] theorem OmegaTerm_zero (B : Term) : OmegaTerm 0 B = B := rfl

theorem OmegaTerm_succ (m : Nat) (B : Term) :
    OmegaTerm (m + 1) B = addT tW (OmegaTerm m B) := rfl

theorem val_OmegaTerm (B : Term) : ∀ m : Nat,
    val (OmegaTerm m B) = Ord.OmegaMul m + val B := by
  intro m
  induction m with
  | zero => rw [OmegaTerm_zero, Ord.OmegaMul_zero, zero_add]
  | succ j ih =>
    rw [OmegaTerm_succ, val_addT, val_tW, ih, ← add_assoc, ← Ord.OmegaMul_succ']

theorem descHead_t1_nil_OmegaTerm {B : Term} (hh : descHead t1 nil B = true) :
    ∀ m : Nat, descHead t1 nil (OmegaTerm m B) = true := by
  intro m
  cases m with
  | zero => exact hh
  | succ j =>
    show descHead t1 nil (cons t1 nil (OmegaTerm j B)) = true
    rw [descHead]
    exact decide_eq_true (le_refl _)

theorem OT_OmegaTerm {B : Term} (hB : OT B) (hh : descHead t1 nil B = true) :
    ∀ m : Nat, OT (OmegaTerm m B) := by
  intro m
  induction m with
  | zero => exact hB
  | succ j ih =>
    show isOT (cons t1 nil (OmegaTerm j B)) = true
    rw [isOT]
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, ih⟩, descHead_t1_nil_OmegaTerm hh j⟩

theorem G_OmegaTerm_mem {B : Term} : ∀ {m : Nat} {x : Term},
    x ∈ G nil (OmegaTerm m B) → x = nil ∨ x ∈ G nil B := by
  intro m
  induction m with
  | zero => exact fun hx => Or.inr hx
  | succ j ih =>
    intro x hx
    rw [OmegaTerm_succ, G_addT_tW] at hx
    rcases List.mem_cons.mp hx with rfl | h1
    · exact Or.inl rfl
    · rcases List.mem_cons.mp h1 with rfl | h2
      · exact Or.inl rfl
      · exact ih h2

theorem nil_lt_OmegaTerm_succ (m : Nat) (B : Term) : nil < OmegaTerm (m + 1) B :=
  nil_lt_cons _ _ _

/-- `Ω·m + ·` is monotone on standard forms below `Ω`. -/
theorem OmegaTerm_le_OmegaTerm {X Y : Term} (hX : OT X) (hY : OT Y)
    (hXt : descHead t1 nil X = true) (hYt : descHead t1 nil Y = true)
    (h : val X ≤ val Y) (m : Nat) : OmegaTerm m X ≤ OmegaTerm m Y := by
  refine le_of_val_le (OT_OmegaTerm hX hXt m) (OT_OmegaTerm hY hYt m) ?_
  rw [val_OmegaTerm, val_OmegaTerm, add_le_add_iff_left]
  exact h

/-- One more `Ω` in front only makes the term bigger. -/
theorem OmegaTerm_le_succ {X : Term} (hX : OT X) (hXt : descHead t1 nil X = true) (m : Nat) :
    OmegaTerm m X ≤ OmegaTerm (m + 1) X := by
  refine le_of_val_le (OT_OmegaTerm hX hXt m) (OT_OmegaTerm hX hXt (m + 1)) ?_
  rw [val_OmegaTerm, val_OmegaTerm]
  exact add_le_add (Ord.OmegaMul_mono (Nat.le_succ m)) (le_refl (val X))

/-! ### `ψ_0(Ω·(m+1) + B)`, repeated -/

theorem G_cons_nil (Y t : Term) : G nil (cons nil Y t) = Y :: (G nil Y ++ G nil t) := by
  rw [G, if_pos (nil_le nil), show G nil nil = ([] : List Term) from rfl, List.nil_append]
  rfl

/-- **`ψ_0(Ω·(m+1) + B)` in front of `t` is a standard form** when `G_0` sees
nothing in `B` that reaches `Ω·(m+1) + B`, the head of `B` is at most `Ω`, and
`t` does not rise above the whole. -/
theorem OT_cons_OmegaTerm {m : Nat} {B t : Term} (hB : OT B)
    (hh : descHead t1 nil B = true) (hG : ∀ x ∈ G nil B, x < OmegaTerm (m + 1) B)
    (hOTt : OT t) (hdesc : descHead nil (OmegaTerm (m + 1) B) t = true) :
    OT (cons nil (OmegaTerm (m + 1) B) t) := by
  show isOT (cons nil (OmegaTerm (m + 1) B) t) = true
  rw [isOT]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨rfl, OT_OmegaTerm hB hh (m + 1)⟩, ?_⟩, hOTt⟩, hdesc⟩
  refine List.all_eq_true.mpr (fun x hx => decide_eq_true ?_)
  rcases G_OmegaTerm_mem hx with rfl | h
  · exact nil_lt_OmegaTerm_succ m B
  · exact hG x h

/-- **`ψ_0(Ω·(m+1) + B)` is a standard form** under the same conditions. -/
theorem OT_psi_OmegaTerm {m : Nat} {B : Term} (hB : OT B)
    (hh : descHead t1 nil B = true) (hG : ∀ x ∈ G nil B, x < OmegaTerm (m + 1) B) :
    OT (psi nil (OmegaTerm (m + 1) B)) :=
  OT_cons_OmegaTerm hB hh hG rfl rfl

theorem OT_repCons_OmegaTerm {m : Nat} {B t : Term} (hB : OT B)
    (hh : descHead t1 nil B = true) (hG : ∀ x ∈ G nil B, x < OmegaTerm (m + 1) B)
    (ht : OT t) (hdesc : descHead nil (OmegaTerm (m + 1) B) t = true) :
    ∀ n : Nat, OT (repCons (OmegaTerm (m + 1) B) n t) := by
  intro n
  induction n with
  | zero => exact ht
  | succ j ih => exact OT_cons_OmegaTerm hB hh hG ih (descHead_repCons hdesc j)

theorem G_repCons_mem {Y t : Term} : ∀ {n : Nat} {x : Term},
    x ∈ G nil (repCons Y n t) → x = Y ∨ x ∈ G nil Y ∨ x ∈ G nil t := by
  intro n
  induction n with
  | zero => exact fun hx => Or.inr (Or.inr hx)
  | succ j ih =>
    intro x hx
    rw [show repCons Y (j + 1) t = cons nil Y (repCons Y j t) from rfl, G_cons_nil] at hx
    rcases List.mem_cons.mp hx with rfl | h1
    · exact Or.inl rfl
    · rcases List.mem_append.mp h1 with h2 | h2
      · exact Or.inr (Or.inl h2)
      · exact ih h2

/-! ### `val` is onto below every `ε_n` -/

/-- **Every ordinal below `ε_n` is the value of a standard form**, and `G_0`
of that form stays below `Ω·n` plus it.  The induction on `n` has the `ε₁`
construction as its step: above `ε_n` the leading term is
`ψ_0(Ω·(n+1) + B)`, whose value `Ord.psi_OmegaMul_add` computes, and the
recursion descends by `Ord.log_lt_self_of_lt_epsN_succ`. -/
theorem exists_OT_of_lt_epsN : ∀ n : ℕ, ∀ α : Ordinal.{0}, α < Ord.epsN n →
    ∃ X : Term, OT X ∧ val X = α ∧ ∀ x ∈ G nil X, x < OmegaTerm n X := by
  intro n
  induction n with
  | zero =>
    intro α hα
    obtain ⟨X, hA, hD, hv⟩ := exists_desc_of_lt_eps0 α hα
    exact ⟨X, OT_of_desc X hA hD, hv, fun x hx => G_lt_of_desc X hA hD x hx⟩
  | succ n IHn =>
    intro α
    induction α using WellFoundedLT.induction with
    | _ α IH =>
      intro hα
      have hΩ : α < Ord.Omega 1 := lt_trans hα (Ord.epsN_lt_Omega_one (n + 1))
      rcases lt_or_ge α (Ord.epsN n) with hsmall | hbig
      · obtain ⟨X, hOTX, hv, hGX⟩ := IHn α hsmall
        have hXt : descHead t1 nil X = true :=
          descHead_of_lt_tW (lt_tW_of_val_lt hOTX (by rw [hv]; exact hΩ))
        exact ⟨X, hOTX, hv, fun x hx =>
          lt_of_lt_of_le' (hGX x hx) (OmegaTerm_le_succ hOTX hXt n)⟩
      have hnilOT : OT nil := rfl
      have hGnil : ∀ x ∈ G nil nil, x < OmegaTerm (n + 1) nil := by
        intro x hx
        rw [G_nil] at hx
        exact absurd hx (by simp)
      rcases eq_or_lt_of_le hbig with heq | hbig'
      · refine ⟨psi nil (OmegaTerm (n + 1) nil), OT_psi_OmegaTerm hnilOT rfl hGnil, ?_, ?_⟩
        · rw [val_psi, val_nil, val_OmegaTerm, val_nil, add_zero, Ord.psi_OmegaMul, heq]
        · have hOTX : OT (psi nil (OmegaTerm (n + 1) nil)) :=
            OT_psi_OmegaTerm hnilOT rfl hGnil
          have hvX : val (psi nil (OmegaTerm (n + 1) nil)) = α := by
            rw [val_psi, val_nil, val_OmegaTerm, val_nil, add_zero, Ord.psi_OmegaMul, heq]
          have hXt : descHead t1 nil (psi nil (OmegaTerm (n + 1) nil)) = true :=
            descHead_of_lt_tW (lt_tW_of_val_lt hOTX (by rw [hvX]; exact hΩ))
          intro x hx
          rw [G_cons_nil] at hx
          rcases List.mem_cons.mp hx with rfl | h1
          · refine lt_of_val_lt (OT_OmegaTerm hnilOT rfl (n + 1))
              (OT_OmegaTerm hOTX hXt (n + 1)) ?_
            rw [val_OmegaTerm, val_OmegaTerm, val_nil, add_zero, hvX]
            conv_lhs => rw [← add_zero (Ord.OmegaMul.{0} (n + 1))]
            rw [add_lt_add_iff_left, ← heq]
            exact Ord.epsN_pos n
          · rcases List.mem_append.mp h1 with h2 | h2
            · rcases G_OmegaTerm_mem h2 with rfl | h3
              · exact nil_lt_OmegaTerm_succ n _
              · rw [G_nil] at h3
                exact absurd h3 (by simp)
            · rw [G_nil] at h2
              exact absurd h2 (by simp)
      · have hpos : (0 : Ordinal) < Ord.epsN n := Ord.epsN_pos n
        have hdm : Ord.epsN n * (α / Ord.epsN n) + α % Ord.epsN n = α :=
          Ordinal.div_add_mod α (Ord.epsN n)
        have hyle : α / Ord.epsN n ≤ α := by
          refine le_trans (Ordinal.le_mul_right (α / Ord.epsN n) hpos) ?_
          exact le_trans (self_le_add_right _ _) (le_of_eq hdm)
        have hy0 : α / Ord.epsN n ≠ 0 := by
          intro h
          rw [h, mul_zero, zero_add] at hdm
          exact absurd (hdm ▸ Ordinal.mod_lt α (ne_of_gt hpos)) (not_lt.mpr hbig)
        have hlog : (ω : Ordinal) ^ Ordinal.log ω (α / Ord.epsN n) ≤ α / Ord.epsN n :=
          Ordinal.opow_log_le_self ω hy0
        have he : Ordinal.log (ω : Ordinal) (α / Ord.epsN n) < α := by
          rcases lt_or_ge (α / Ord.epsN n) α with h | h
          · exact lt_of_le_of_lt (Ordinal.log_le_self _ _) h
          · rw [le_antisymm hyle h]
            exact Ord.log_lt_self_of_lt_epsN_succ hbig' hα
        obtain ⟨B, hOTB, hvB, hGB⟩ := IH _ he (lt_trans he hα)
        have hBt : B < tW := lt_tW_of_val_lt hOTB (by rw [hvB]; exact lt_trans he hΩ)
        have hBh : descHead t1 nil B = true := descHead_of_lt_tW hBt
        have hP : Ord.psi (val (OmegaTerm (n + 1) B)) 0
            = Ord.epsN n * (ω : Ordinal) ^ Ordinal.log ω (α / Ord.epsN n) := by
          rw [val_OmegaTerm, hvB]
          exact Ord.psi_OmegaMul_add n (lt_trans he hα)
        obtain ⟨k, hk⟩ := Ordinal.lt_omega0.mp
          (Ordinal.div_opow_log_lt (α / Ord.epsN n) Ordinal.one_lt_omega0)
        have hsplit : (ω : Ordinal) ^ Ordinal.log ω (α / Ord.epsN n) * (k : Ordinal)
            + (α / Ord.epsN n) % (ω : Ordinal) ^ Ordinal.log ω (α / Ord.epsN n)
              = α / Ord.epsN n := by
          have h := Ordinal.div_add_mod (α / Ord.epsN n)
            ((ω : Ordinal) ^ Ordinal.log ω (α / Ord.epsN n))
          rwa [hk] at h
        have hstep : Ord.epsN n *
            ((α / Ord.epsN n) % (ω : Ordinal) ^ Ordinal.log ω (α / Ord.epsN n))
            + α % Ord.epsN n
              < Ord.epsN n * (ω : Ordinal) ^ Ordinal.log ω (α / Ord.epsN n) := by
          refine lt_of_lt_of_le ((add_lt_add_iff_left _).mpr
            (Ordinal.mod_lt α (ne_of_gt hpos))) ?_
          rw [← mul_add_one]
          refine mul_le_mul_right ?_ _
          rw [← Order.succ_eq_add_one]
          exact Order.succ_le_of_lt (Ordinal.mod_lt _ (ne_of_gt (Ordinal.opow_pos _ omega0_pos)))
        have hr : Ord.epsN n *
            ((α / Ord.epsN n) % (ω : Ordinal) ^ Ordinal.log ω (α / Ord.epsN n))
            + α % Ord.epsN n < α := by
          refine lt_of_lt_of_le hstep ?_
          refine le_trans (mul_le_mul_right hlog (Ord.epsN n)) ?_
          exact le_trans (self_le_add_right _ _) (le_of_eq hdm)
        obtain ⟨T, hOTT, hvT, hGT⟩ := IH _ hr (lt_trans hr hα)
        have hvX : val (repCons (OmegaTerm (n + 1) B) k T) = α := by
          rw [val_repCons, hP, hvT, mul_assoc, ← add_assoc, ← mul_add, hsplit, hdm]
        have hOTpsi : OT (psi nil (OmegaTerm (n + 1) B)) := OT_psi_OmegaTerm hOTB hBh hGB
        have hdesc : descHead nil (OmegaTerm (n + 1) B) T = true := by
          refine descHead_of_val_lt hOTT hOTpsi ?_
          rw [hvT, val_psi, val_nil, hP]
          exact hstep
        have hOTX : OT (repCons (OmegaTerm (n + 1) B) k T) :=
          OT_repCons_OmegaTerm hOTB hBh hGB hOTT hdesc k
        have hXt : descHead t1 nil (repCons (OmegaTerm (n + 1) B) k T) = true :=
          descHead_of_lt_tW (lt_tW_of_val_lt hOTX (by rw [hvX]; exact hΩ))
        have hTt : descHead t1 nil T = true :=
          descHead_of_lt_tW (lt_tW_of_val_lt hOTT (by rw [hvT]; exact lt_trans hr hΩ))
        refine ⟨repCons (OmegaTerm (n + 1) B) k T, hOTX, hvX, fun x hx => ?_⟩
        rcases G_repCons_mem hx with rfl | h | h
        · refine lt_of_val_lt (OT_OmegaTerm hOTB hBh (n + 1))
            (OT_OmegaTerm hOTX hXt (n + 1)) ?_
          rw [val_OmegaTerm, val_OmegaTerm, hvB, hvX, add_lt_add_iff_left]
          exact he
        · rcases G_OmegaTerm_mem h with rfl | h3
          · exact nil_lt_OmegaTerm_succ n _
          · refine lt_of_lt_of_le' (hGB x h3) ?_
            exact OmegaTerm_le_OmegaTerm hOTB hOTX hBh hXt
              (by rw [hvB, hvX]; exact he.le) (n + 1)
        · refine lt_of_lt_of_le' (hGT x h) ?_
          exact OmegaTerm_le_OmegaTerm hOTT hOTX hTt hXt
            (by rw [hvT, hvX]; exact hr.le) (n + 1)

/-! ### The ceiling at each level -/

/-- The term `ψ_0(Ω·(n+1))`, which names `ε_n`. -/
def teN (n : ℕ) : Term := psi nil (OmegaTerm (n + 1) nil)

theorem teN_zero : teN 0 = te0 := rfl

theorem teN_one : teN 1 = te1 := rfl

theorem OT_teN (n : ℕ) : OT (teN n) := by
  refine OT_psi_OmegaTerm rfl rfl (fun x hx => ?_)
  rw [G_nil] at hx
  exact absurd hx (by simp)

/-- **`ψ_0(Ω·(n+1))` names `ε_n`.** -/
theorem val_teN (n : ℕ) : val (teN n) = Ord.epsN n := by
  rw [teN, val_psi, val_nil, val_OmegaTerm, val_nil, add_zero, Ord.psi_OmegaMul]

/-- **The standard forms below `ψ_0(Ω·(n+1))` name exactly the ordinals below
`ε_n`.** -/
theorem exists_OT_lt_teN {n : ℕ} {α : Ordinal.{0}} (h : α < Ord.epsN n) :
    ∃ X : Term, OT X ∧ X < teN n ∧ val X = α := by
  obtain ⟨X, hOT, hv, _⟩ := exists_OT_of_lt_epsN n α h
  exact ⟨X, hOT, lt_of_val_lt hOT (OT_teN n) (by rw [hv, val_teN]; exact h), hv⟩

/-- **Below `ε_n`, `val` is a bijection from the standard forms onto the
ordinals.** -/
theorem existsUnique_OT_lt_teN {n : ℕ} {α : Ordinal.{0}} (h : α < Ord.epsN n) :
    ∃! X : Term, OT X ∧ X < teN n ∧ val X = α := by
  obtain ⟨X, hOT, hlt, hv⟩ := exists_OT_lt_teN h
  refine ⟨X, ⟨hOT, hlt, hv⟩, fun Y hY => ?_⟩
  exact val_inj_of_OT hY.1 (by exact hOT) (by rw [hY.2.2, hv])

theorem val_lt_epsN_of_lt_teN {n : ℕ} {X : Term} (hOT : OT X) (h : X < teN n) :
    val X < Ord.epsN n := by
  rw [← val_teN n]
  exact val_lt_val hOT (OT_teN n) h

end Googology.Trans.BMS

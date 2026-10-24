import Googology.Trans.PoR.InaccPsi.R2.TiCode

/-!
# The data of a level read on its `InaccPsi` normal form, for every level (past `B_Γ` included), and its `B_n` move

`val = Term.val S`, `nf = Bc.bcNf S`, `B_n = Bc.bcB S n = val ∘ σ ∘ nf` (`σ = bcSig (bcPre (n+1)) bcPreW`), `MvD` the
normal-form domain of `B_n` (`R2.MvDom`), `B_Γ = Tf.tfBG`.  `Tf.tfDat` reads the data of a code below `B_Γ` on its
Veblen normal form over `Ω₁` and the atoms `ψ_{Ω₂}(c)`; past `B_Γ` the atoms `ψ_{Ω₂}(a)` have uncountable arguments
(`B_Γ = ψ_{Ω₂}(Ω₂)`).  The same reading is defined here on the normal-form terms of the notation, with no bound:

* `tiDatT S t` (**the largest countable leaf of `t`**: `val t` when `val t < Ω₁`; otherwise the larger datum of the two
  parts of a sum or of `φ(a, b)`, the datum of the argument of a collapse `ψ_π(a)` (the subscript `π` is not a leaf),
  and `0` at `Ω_a`, `I_n`, `I_ω`), `tiDatT_small`, `tiDatT_add`, `tiDatT_phi`, `tiDatT_om`, `tiDatT_psiS`,
  `tiDatT_psiI`, `tiDatT_inacc`, `tiDatT_inaccW`, `tiDatT_lt_Om1` (**the datum is countable**);
* `tiDatT_sig` (**`tiDatT (σ t) = B_n (tiDatT t)`** for every `t` in the domain `bcD` of `σ`: `σ` keeps `+`, `φ`, `Ω_·`,
  `ψ_π` with `π ≠ Ω₁`, and `B_n` is strictly increasing on `MvD` with `B_n(Ω₁) = Ω₁`, so countable subterms go to
  countable subterms, and `B_n` commutes with `max`);
* `tiDat S x = tiDatT S (nf x)`, `tiDat_small`, `tiDat_lt_Om1`, `tiDat_B` (**`tiDat (B_n x) = B_n (tiDat x)` for every
  `x ∈ MvD`**), `tiDat_psi2` (**`tiDat (ψ_{Ω₂}(α)) = tiDat α`** for every `α` own for `ψ_{Ω₂}`, past `B_Γ` included);
  `tiB_max`, `tiMvD_max` (`B_n` and `max`).

No new axiom.  New definitions: `tiDatT`, `tiDat`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ti

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bc
  Googology.Trans.PoR.InaccPsi.R2.Mv

/-- **The largest countable leaf of a term.** -/
noncomputable def tiDatT (S : InaccSeq.{0}) : Term → Ordinal.{0}
  | .zero => 0
  | .inacc n => if val S (inacc n) < Om 1 then val S (inacc n) else 0
  | .inaccW => if val S inaccW < Om 1 then val S inaccW else 0
  | .add a b => if val S (add a b) < Om 1 then val S (add a b) else max (tiDatT S a) (tiDatT S b)
  | .phi a b => if val S (phi a b) < Om 1 then val S (phi a b) else max (tiDatT S a) (tiDatT S b)
  | .om a => if val S (om a) < Om 1 then val S (om a) else 0
  | .psiS s a => if val S (psiS s a) < Om 1 then val S (psiS s a) else tiDatT S a
  | .psiI n a => if val S (psiI n a) < Om 1 then val S (psiI n a) else tiDatT S a

variable {S : InaccSeq.{0}}

theorem tiDatT_small {t : Term} (h : val S t < Om 1) : tiDatT S t = val S t := by
  cases t with
  | zero => rfl
  | inacc n => simp only [tiDatT, if_pos h]
  | inaccW => simp only [tiDatT, if_pos h]
  | add a b => simp only [tiDatT, if_pos h]
  | phi a b => simp only [tiDatT, if_pos h]
  | om a => simp only [tiDatT, if_pos h]
  | psiS s a => simp only [tiDatT, if_pos h]
  | psiI n a => simp only [tiDatT, if_pos h]

theorem tiDatT_add {a b : Term} (h : ¬ val S (add a b) < Om 1) :
    tiDatT S (add a b) = max (tiDatT S a) (tiDatT S b) := by simp only [tiDatT, if_neg h]

theorem tiDatT_phi {a b : Term} (h : ¬ val S (phi a b) < Om 1) :
    tiDatT S (phi a b) = max (tiDatT S a) (tiDatT S b) := by simp only [tiDatT, if_neg h]

theorem tiDatT_om {a : Term} (h : ¬ val S (om a) < Om 1) : tiDatT S (om a) = 0 := by
  simp only [tiDatT, if_neg h]

theorem tiDatT_psiS {s a : Term} (h : ¬ val S (psiS s a) < Om 1) : tiDatT S (psiS s a) = tiDatT S a := by
  simp only [tiDatT, if_neg h]

theorem tiDatT_psiI {n : ℕ} {a : Term} (h : ¬ val S (psiI n a) < Om 1) :
    tiDatT S (psiI n a) = tiDatT S a := by simp only [tiDatT, if_neg h]

theorem tiDatT_inacc {n : ℕ} (h : ¬ val S (inacc n) < Om 1) : tiDatT S (inacc n) = 0 := by
  simp only [tiDatT, if_neg h]

theorem tiDatT_inaccW (h : ¬ val S inaccW < Om 1) : tiDatT S inaccW = 0 := by simp only [tiDatT, if_neg h]

/-- **The datum is countable.** -/
theorem tiDatT_lt_Om1 : ∀ t : Term, tiDatT S t < Om 1 := by
  have h0 : (0 : Ordinal.{0}) < Om 1 := Om_pos one_ne_zero
  intro t
  induction t with
  | zero => exact h0
  | inacc n => by_cases h : val S (inacc n) < Om 1 <;> simp only [tiDatT, h, if_true, if_false] <;> first
      | exact h | exact h0
  | inaccW => by_cases h : val S inaccW < Om 1 <;> simp only [tiDatT, h, if_true, if_false] <;> first
      | exact h | exact h0
  | add a b iha ihb =>
    by_cases h : val S (add a b) < Om 1
    · rw [tiDatT_small h]; exact h
    · rw [tiDatT_add h]; exact max_lt iha ihb
  | phi a b iha ihb =>
    by_cases h : val S (phi a b) < Om 1
    · rw [tiDatT_small h]; exact h
    · rw [tiDatT_phi h]; exact max_lt iha ihb
  | om a _ =>
    by_cases h : val S (om a) < Om 1
    · rw [tiDatT_small h]; exact h
    · rw [tiDatT_om h]; exact h0
  | psiS s a _ iha =>
    by_cases h : val S (psiS s a) < Om 1
    · rw [tiDatT_small h]; exact h
    · rw [tiDatT_psiS h]; exact iha
  | psiI n a iha =>
    by_cases h : val S (psiI n a) < Om 1
    · rw [tiDatT_small h]; exact h
    · rw [tiDatT_psiI h]; exact iha

/-- `B_n` commutes with `max` on `MvD`. -/
theorem tiB_max {n : ℕ} {a b : Ordinal.{0}} (ha : MvD S a) (hb : MvD S b) :
    Bc.bcB S n (max a b) = max (Bc.bcB S n a) (Bc.bcB S n b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right]
    rcases h.lt_or_eq with h' | h'
    · exact ((mvB_lt_iff (k := n) ha hb).2 h').le
    · rw [h']
  · rw [max_eq_left h, max_eq_left]
    rcases h.lt_or_eq with h' | h'
    · exact ((mvB_lt_iff (k := n) hb ha).2 h').le
    · rw [h']

theorem tiMvD_max {a b : Ordinal.{0}} (ha : MvD S a) (hb : MvD S b) : MvD S (max a b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]; exact hb
  · rw [max_eq_left h]; exact ha

/-- **`tiDatT (σ t) = B_n (tiDatT t)`** on the domain `bcD` of `σ`, and the datum is in `MvD`. -/
theorem tiDatT_sig {n : ℕ} : ∀ t : Term, bcD S t →
    MvD S (tiDatT S t) ∧ tiDatT S (bcSig (bcPre (n + 1)) bcPreW t) = Bc.bcB S n (tiDatT S t) := by
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  have hD0 : MvD S 0 := mvD_of_term (S := S) bcD_zero
  -- countable values go to countable values, uncountable to uncountable
  have hsmall : ∀ t : Term, bcD S t → (val S (bcSig (bcPre (n + 1)) bcPreW t) < Om 1 ↔ val S t < Om 1) :=
    fun t hD => by
      have h := mvB_lt_iff (k := n) (mvD_of_term hD) hDO
      rw [hBO, mvB_term hD] at h
      exact h
  intro t
  induction t with
  | zero => intro _; exact ⟨hD0, by rw [bcSig_zero]; exact (Bc.bcB_zero n).symm⟩
  | inacc m =>
    intro hD
    by_cases h : val S (inacc m) < Om 1
    · rw [tiDatT_small h, bcSig_inacc, tiDatT_small h]
      exact ⟨mvD_of_term hD, by rw [mvB_term (k := n) hD, bcSig_inacc]⟩
    · rw [tiDatT_inacc h, bcSig_inacc, tiDatT_inacc h, Bc.bcB_zero]; exact ⟨hD0, rfl⟩
  | inaccW =>
    intro hD
    by_cases h : val S inaccW < Om 1
    · rw [tiDatT_small h, bcSig_inaccW, tiDatT_small h]
      exact ⟨mvD_of_term hD, by rw [mvB_term (k := n) hD, bcSig_inaccW]⟩
    · rw [tiDatT_inaccW h, bcSig_inaccW, tiDatT_inaccW h, Bc.bcB_zero]; exact ⟨hD0, rfl⟩
  | add a b iha ihb =>
    intro hD
    by_cases h : val S (add a b) < Om 1
    · have h' := (hsmall _ hD).2 h
      rw [tiDatT_small h, tiDatT_small h', ← mvB_term (k := n) hD]; exact ⟨mvD_of_term hD, rfl⟩
    · have h' : ¬ val S (bcSig (bcPre (n + 1)) bcPreW (add a b)) < Om 1 := fun h'' => h ((hsmall _ hD).1 h'')
      rw [bcSig_add] at h' ⊢
      obtain ⟨hDa, hσa⟩ := iha ⟨hD.1.1, hD.2.1⟩
      obtain ⟨hDb, hσb⟩ := ihb ⟨hD.1.2.1, hD.2.2⟩
      rw [tiDatT_add h, tiDatT_add h', hσa, hσb, tiB_max hDa hDb]
      exact ⟨tiMvD_max hDa hDb, rfl⟩
  | phi a b iha ihb =>
    intro hD
    by_cases h : val S (phi a b) < Om 1
    · have h' := (hsmall _ hD).2 h
      rw [tiDatT_small h, tiDatT_small h', ← mvB_term (k := n) hD]; exact ⟨mvD_of_term hD, rfl⟩
    · have h' : ¬ val S (bcSig (bcPre (n + 1)) bcPreW (phi a b)) < Om 1 := fun h'' => h ((hsmall _ hD).1 h'')
      rw [bcSig_phi] at h' ⊢
      obtain ⟨hDa, hσa⟩ := iha ⟨hD.1.1, hD.2.1⟩
      obtain ⟨hDb, hσb⟩ := ihb ⟨hD.1.2.1, hD.2.2⟩
      rw [tiDatT_phi h, tiDatT_phi h', hσa, hσb, tiB_max hDa hDb]
      exact ⟨tiMvD_max hDa hDb, rfl⟩
  | om a _ =>
    intro hD
    by_cases h : val S (om a) < Om 1
    · have h' := (hsmall _ hD).2 h
      rw [tiDatT_small h, tiDatT_small h', ← mvB_term (k := n) hD]; exact ⟨mvD_of_term hD, rfl⟩
    · have h' : ¬ val S (bcSig (bcPre (n + 1)) bcPreW (om a)) < Om 1 := fun h'' => h ((hsmall _ hD).1 h'')
      rw [bcSig_om] at h' ⊢
      rw [tiDatT_om h, tiDatT_om h', Bc.bcB_zero]; exact ⟨hD0, rfl⟩
  | psiS s a _ iha =>
    intro hD
    by_cases h : val S (psiS s a) < Om 1
    · have h' := (hsmall _ hD).2 h
      rw [tiDatT_small h, tiDatT_small h', ← mvB_term (k := n) hD]; exact ⟨mvD_of_term hD, rfl⟩
    · have hs : s ≠ Term.zero := by
        rintro rfl
        apply h
        show S.psi (val S a) (Om (val S Term.zero + 1)) < Om 1
        have e : val S Term.zero + 1 = 1 := by simp [val]
        rw [e]; exact psi_lt Low.InR_Om_one _
      have h' : ¬ val S (bcSig (bcPre (n + 1)) bcPreW (psiS s a)) < Om 1 := fun h'' => h ((hsmall _ hD).1 h'')
      rw [bcSig_psiS_ne hs] at h' ⊢
      obtain ⟨hDa, hσa⟩ := iha ⟨hD.1.2.1, hD.2.2.1⟩
      rw [tiDatT_psiS h, tiDatT_psiS h', hσa]
      exact ⟨hDa, rfl⟩
  | psiI m a iha =>
    intro hD
    by_cases h : val S (psiI m a) < Om 1
    · have h' := (hsmall _ hD).2 h
      rw [tiDatT_small h, tiDatT_small h', ← mvB_term (k := n) hD]; exact ⟨mvD_of_term hD, rfl⟩
    · have h' : ¬ val S (bcSig (bcPre (n + 1)) bcPreW (psiI m a)) < Om 1 := fun h'' => h ((hsmall _ hD).1 h'')
      rw [bcSig_psiI] at h' ⊢
      obtain ⟨hDa, hσa⟩ := iha ⟨hD.1.1, hD.2⟩
      rw [tiDatT_psiI h, tiDatT_psiI h', hσa]
      exact ⟨hDa, rfl⟩

/-- **The data of an ordinal**, read on its normal form. -/
noncomputable def tiDat (S : InaccSeq.{0}) (x : Ordinal.{0}) : Ordinal.{0} := tiDatT S (bcNf S x)

theorem tiDat_lt_Om1 (x : Ordinal.{0}) : tiDat S x < Om 1 := tiDatT_lt_Om1 _

/-- A countable `x` in the normal-form domain is its own datum. -/
theorem tiDat_small {x : Ordinal.{0}} (hx : x ∈ ⋃ a, S.CSet a 0) (h : x < Om 1) : tiDat S x = x := by
  unfold tiDat
  have hv := (bcNf_spec S hx).2
  rw [tiDatT_small (by rw [hv]; exact h), hv]

/-- **`tiDat (B_n x) = B_n (tiDat x)`** for every `x` in the normal-form domain of `B_n`. -/
theorem tiDat_B {n : ℕ} {x : Ordinal.{0}} (hx : MvD S x) :
    MvD S (tiDat S x) ∧ tiDat S (Bc.bcB S n x) = Bc.bcB S n (tiDat S x) := by
  have hN : NF (bcSig (bcPre (n + 1)) bcPreW (bcNf S x)) := bc_NF hx.2
  have e : bcNf S (Bc.bcB S n x) = bcSig (bcPre (n + 1)) bcPreW (bcNf S x) := by
    unfold Bc.bcB; exact bcNf_val S hN
  unfold tiDat
  rw [e]
  exact tiDatT_sig _ hx.2

/-- **The data of a collapse `ψ_{Ω₂}(α)`** (any `α` own for `ψ_{Ω₂}`, in the normal-form domain): `tiDat α`. -/
theorem tiDat_psi2 {α : Ordinal.{0}} (hα : α ∈ ⋃ a, S.CSet a 0)
    (hown : α ∈ S.CSet α (S.psi α (Om (1 + 1)))) :
    tiDat S (S.psi α (Om (1 + 1))) = tiDat S α := by
  have hmem := Mx.mxPsi2_mem hα
  obtain ⟨hN, hv⟩ := bcNf_spec S hmem
  obtain ⟨a, ht, hva⟩ := Mx.mxNf_psi2 hown hN hv
  have hNa : NF a := by rw [ht] at hN; exact hN.2.1
  have ha : bcNf S α = a := by rw [← hva]; exact bcNf_val S hNa
  have hbig : ¬ val S (psiS Bc.tOne a) < Om 1 := by
    rw [← ht, hv]; exact not_lt.2 (psiS_bounds (S := S) α 1).1.le
  unfold tiDat
  rw [ht, tiDatT_psiS hbig, ha]

end Googology.Trans.PoR.InaccPsi.R2.Ti

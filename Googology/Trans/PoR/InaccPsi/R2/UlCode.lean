import Googology.Trans.PoR.InaccPsi.R2.UiCode

/-!
# The data read on normal forms at every threshold `κ`, and its code test

`val = Term.val S`, `nf = Bc.bcNf S`, `Cl(A, q) = S.CSet A q`.  `R2.UiCode` reads the largest leaf below `Ω₁` of a
normal form (subscripts included) and decides membership in a hull `Cl(A, q)` with `q ≤ Ω₁`.  Here the threshold is a
parameter `κ` (in use: `κ = Ω_{s+1}`, the cardinal one step above the floor of the level hierarchy `H^s`), so that
membership in `Cl(A, q)` with `q ≤ κ` is read off the normal form for every `κ`:

* `ulDatT S κ t` (**the largest leaf of `t` below `κ`, subscripts included**: `val t` when `val t < κ`; otherwise the
  larger datum of the parts), `ulArgsT S κ A t` (**every collapse argument of a subterm `≥ κ` is below `A`**);
  `ulDatT_small`, `ulDatT_lt`, `ul_one_dat` / `ul_one_args` (**at `κ = Ω₁` these are `Ui.uiDatT`, `Ui.uiArgsT`**);
* `ul_code_mem` (**the hull converse**), `ul_code_dat` (**the hull lemma**: for a normal form `t` with `val t ∈
  Cl(A, q)`, `0 < q ≤ κ`, `q ≤ Λ` and `Cl(A, q) ∩ κ ⊆ q`: `ulDatT κ t < q` and `ulArgsT κ A t`);
* `ulDat`, `ulArgs` (on ordinals, through `nf`), `ul_code_iff` (**the code test at threshold `κ`**: for `x` of the
  notation, `x ∈ Cl(A, q) ↔ ulDat κ x < q ∧ ulArgs κ A x`), `ul_one_code_iff` (`Ui.ui_code_iff` recovered).

No new axiom.  New definitions: `ulDatT`, `ulArgsT`, `ulDat`, `ulArgs`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ul

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2

/-- **The largest leaf below `κ` of a term, subscripts included.** -/
noncomputable def ulDatT (S : InaccSeq.{0}) (κ : Ordinal.{0}) : Term → Ordinal.{0}
  | .zero => 0
  | .inacc n => if val S (inacc n) < κ then val S (inacc n) else 0
  | .inaccW => if val S inaccW < κ then val S inaccW else 0
  | .add a b => if val S (add a b) < κ then val S (add a b) else max (ulDatT S κ a) (ulDatT S κ b)
  | .phi a b => if val S (phi a b) < κ then val S (phi a b) else max (ulDatT S κ a) (ulDatT S κ b)
  | .om a => if val S (om a) < κ then val S (om a) else ulDatT S κ a
  | .psiS s a => if val S (psiS s a) < κ then val S (psiS s a) else max (ulDatT S κ s) (ulDatT S κ a)
  | .psiI n a => if val S (psiI n a) < κ then val S (psiI n a) else ulDatT S κ a

/-- **Every collapse argument of a subterm `≥ κ` is below `A`.** -/
def ulArgsT (S : InaccSeq.{0}) (κ A : Ordinal.{0}) : Term → Prop
  | .zero => True
  | .inacc _ => True
  | .inaccW => True
  | .add a b => val S (add a b) < κ ∨ (ulArgsT S κ A a ∧ ulArgsT S κ A b)
  | .phi a b => val S (phi a b) < κ ∨ (ulArgsT S κ A a ∧ ulArgsT S κ A b)
  | .om a => val S (om a) < κ ∨ ulArgsT S κ A a
  | .psiS s a => val S (psiS s a) < κ ∨ (val S a < A ∧ ulArgsT S κ A s ∧ ulArgsT S κ A a)
  | .psiI n a => val S (psiI n a) < κ ∨ (val S a < A ∧ ulArgsT S κ A a)

variable {S : InaccSeq.{0}} {κ : Ordinal.{0}}

theorem ulDatT_small {t : Term} (h : val S t < κ) : ulDatT S κ t = val S t := by
  cases t with
  | zero => rfl
  | inacc n => simp only [ulDatT, if_pos h]
  | inaccW => simp only [ulDatT, if_pos h]
  | add a b => simp only [ulDatT, if_pos h]
  | phi a b => simp only [ulDatT, if_pos h]
  | om a => simp only [ulDatT, if_pos h]
  | psiS s a => simp only [ulDatT, if_pos h]
  | psiI n a => simp only [ulDatT, if_pos h]

/-- **The datum is below `κ`** (`κ > 0`). -/
theorem ulDatT_lt (h0 : 0 < κ) : ∀ t : Term, ulDatT S κ t < κ := by
  intro t
  induction t with
  | zero => exact h0
  | inacc n => by_cases h : val S (inacc n) < κ <;> simp only [ulDatT, h, if_true, if_false] <;> first
      | exact h | exact h0
  | inaccW => by_cases h : val S inaccW < κ <;> simp only [ulDatT, h, if_true, if_false] <;> first
      | exact h | exact h0
  | add a b iha ihb =>
    by_cases h : val S (add a b) < κ
    · rw [ulDatT_small h]; exact h
    · simp only [ulDatT, if_neg h]; exact max_lt iha ihb
  | phi a b iha ihb =>
    by_cases h : val S (phi a b) < κ
    · rw [ulDatT_small h]; exact h
    · simp only [ulDatT, if_neg h]; exact max_lt iha ihb
  | om a iha =>
    by_cases h : val S (om a) < κ
    · rw [ulDatT_small h]; exact h
    · simp only [ulDatT, if_neg h]; exact iha
  | psiS s a ihs iha =>
    by_cases h : val S (psiS s a) < κ
    · rw [ulDatT_small h]; exact h
    · simp only [ulDatT, if_neg h]; exact max_lt ihs iha
  | psiI n a iha =>
    by_cases h : val S (psiI n a) < κ
    · rw [ulDatT_small h]; exact h
    · simp only [ulDatT, if_neg h]; exact iha

/-- **At `κ = Ω₁` the datum is `Ui.uiDatT`.** -/
theorem ul_one_dat : ∀ t : Term, ulDatT S (Om 1) t = Ui.uiDatT S t := by
  intro t
  induction t with
  | zero => rfl
  | inacc n => simp only [ulDatT, Ui.uiDatT]
  | inaccW => simp only [ulDatT, Ui.uiDatT]
  | add a b iha ihb => simp only [ulDatT, Ui.uiDatT, iha, ihb]
  | phi a b iha ihb => simp only [ulDatT, Ui.uiDatT, iha, ihb]
  | om a iha => simp only [ulDatT, Ui.uiDatT, iha]
  | psiS s a ihs iha => simp only [ulDatT, Ui.uiDatT, ihs, iha]
  | psiI n a iha => simp only [ulDatT, Ui.uiDatT, iha]

/-- **At `κ = Ω₁` the argument condition is `Ui.uiArgsT`.** -/
theorem ul_one_args (A : Ordinal.{0}) : ∀ t : Term, ulArgsT S (Om 1) A t ↔ Ui.uiArgsT S A t := by
  intro t
  induction t with
  | zero => exact Iff.rfl
  | inacc n => exact Iff.rfl
  | inaccW => exact Iff.rfl
  | add a b iha ihb => simp only [ulArgsT, Ui.uiArgsT, iha, ihb]
  | phi a b iha ihb => simp only [ulArgsT, Ui.uiArgsT, iha, ihb]
  | om a iha => simp only [ulArgsT, Ui.uiArgsT, iha]
  | psiS s a ihs iha => simp only [ulArgsT, Ui.uiArgsT, ihs, iha]
  | psiI n a iha => simp only [ulArgsT, Ui.uiArgsT, iha]

/-! ## The hull converse -/

/-- **The hull converse**: a term whose leaves below `κ` (subscripts included) are below `q` and whose collapse
arguments (of subterms `≥ κ`) are below `A` denotes a member of `Cl(A, q)`. -/
theorem ul_code_mem {A q : Ordinal.{0}} : ∀ t : Term, ulDatT S κ t < q → ulArgsT S κ A t → val S t ∈ S.CSet A q := by
  intro t
  induction t with
  | zero => intro _ _; exact CSet.zero_mem _ _
  | inacc n => intro _ _; exact CSet.I_mem _ _ n
  | inaccW => intro _ _; exact CSet.Iw_mem _ _
  | add a b iha ihb =>
    intro hd ha
    by_cases h : val S (add a b) < κ
    · rw [ulDatT_small h] at hd; exact CSet.of_lt hd
    simp only [ulDatT, if_neg h] at hd
    have ha' := ha.resolve_left h
    exact CSet.add_mem (iha (lt_of_le_of_lt (le_max_left _ _) hd) ha'.1)
      (ihb (lt_of_le_of_lt (le_max_right _ _) hd) ha'.2)
  | phi a b iha ihb =>
    intro hd ha
    by_cases h : val S (phi a b) < κ
    · rw [ulDatT_small h] at hd; exact CSet.of_lt hd
    simp only [ulDatT, if_neg h] at hd
    have ha' := ha.resolve_left h
    exact CSet.phi_mem (iha (lt_of_le_of_lt (le_max_left _ _) hd) ha'.1)
      (ihb (lt_of_le_of_lt (le_max_right _ _) hd) ha'.2)
  | om a iha =>
    intro hd ha
    by_cases h : val S (om a) < κ
    · rw [ulDatT_small h] at hd; exact CSet.of_lt hd
    simp only [ulDatT, if_neg h] at hd
    exact CSet.Om_mem (iha hd (ha.resolve_left h))
  | psiS s a ihs iha =>
    intro hd ha
    by_cases h : val S (psiS s a) < κ
    · rw [ulDatT_small h] at hd; exact CSet.of_lt hd
    simp only [ulDatT, if_neg h] at hd
    obtain ⟨hlt, has, haa⟩ := ha.resolve_left h
    exact CSet.psi_mem hlt (InR_Om_succ _)
      (CSet.Om_mem (CSet.succ_mem (ihs (lt_of_le_of_lt (le_max_left _ _) hd) has)))
      (iha (lt_of_le_of_lt (le_max_right _ _) hd) haa)
  | psiI n a iha =>
    intro hd ha
    by_cases h : val S (psiI n a) < κ
    · rw [ulDatT_small h] at hd; exact CSet.of_lt hd
    simp only [ulDatT, if_neg h] at hd
    obtain ⟨hlt, haa⟩ := ha.resolve_left h
    exact CSet.psi_mem hlt (InR_I n) (CSet.I_mem _ _ n) (iha hd haa)

/-! ## The hull lemma -/

/-- **The hull lemma at threshold `κ`**: a normal form `t` with `val t ∈ Cl(A, q)` has all its leaves below `κ`
(subscripts included) below `q` and all its collapse arguments (of subterms `≥ κ`) below `A`, when `0 < q ≤ κ`,
`q ≤ Λ` and `Cl(A, q) ∩ κ ⊆ q`. -/
theorem ul_code_dat {A q : Ordinal.{0}} (hq1 : q ≤ κ) (hqL : q ≤ S.Lam)
    (hcl : ∀ x ∈ S.CSet A q, x < κ → x < q) (hq0 : 0 < q) :
    ∀ t : Term, NF t → val S t ∈ S.CSet A q → ulDatT S κ t < q ∧ ulArgsT S κ A t := by
  have hκ0 : 0 < κ := hq0.trans_le hq1
  intro t
  induction t with
  | zero => intro _ _; exact ⟨hq0, trivial⟩
  | inacc n =>
    intro _ _
    by_cases h : val S (inacc n) < κ
    · exact ⟨by rw [ulDatT_small h]; exact hcl _ (CSet.I_mem _ _ n) h, trivial⟩
    · exact ⟨by simp only [ulDatT, if_neg h]; exact hq0, trivial⟩
  | inaccW =>
    intro _ _
    by_cases h : val S inaccW < κ
    · exact ⟨by rw [ulDatT_small h]; exact hcl _ (CSet.Iw_mem _ _) h, trivial⟩
    · exact ⟨by simp only [ulDatT, if_neg h]; exact hq0, trivial⟩
  | add a b iha ihb =>
    intro hN hm
    by_cases h : val S (add a b) < κ
    · exact ⟨by rw [ulDatT_small h]; exact hcl _ hm h, Or.inl h⟩
    have h0 : val S (add a b) ≠ 0 := fun e => h (by rw [e]; exact hκ0)
    obtain ⟨hl, ht⟩ := lead_tail_mem hm h0
    obtain ⟨hla, htb⟩ := Ui.ui_add_parts (S := S) hN
    rw [hla] at hl; rw [htb] at ht
    obtain ⟨hda, haa⟩ := iha hN.1 hl
    obtain ⟨hdb, hab⟩ := ihb hN.2.1 ht
    exact ⟨by simp only [ulDatT, if_neg h]; exact max_lt hda hdb, Or.inr ⟨haa, hab⟩⟩
  | phi a b iha ihb =>
    intro hN hm
    by_cases h : val S (phi a b) < κ
    · exact ⟨by rw [ulDatT_small h]; exact hcl _ hm h, Or.inl h⟩
    have hN' := hN
    obtain ⟨hNa, hNb, hca, hcb⟩ := hN
    have hav : val S a < val S (phi a b) := by
      have e := Term.cmp_eq_compare S hNa hN'
      rw [e] at hca; exact compare_lt_iff_lt.1 hca
    have hbv : val S b < val S (phi a b) := by
      have e := Term.cmp_eq_compare S hNb hN'
      rw [e] at hcb; exact compare_lt_iff_lt.1 hcb
    obtain ⟨hma, hmb⟩ := mem_of_veblen_mem hm hav hbv
    obtain ⟨hda, haa⟩ := iha hNa hma
    obtain ⟨hdb, hab⟩ := ihb hNb hmb
    exact ⟨by simp only [ulDatT, if_neg h]; exact max_lt hda hdb, Or.inr ⟨haa, hab⟩⟩
  | om a iha =>
    intro hN hm
    by_cases h : val S (om a) < κ
    · exact ⟨by rw [ulDatT_small h]; exact hcl _ hm h, Or.inl h⟩
    obtain ⟨hda, haa⟩ := iha hN.1 (mem_of_Om_mem hm)
    exact ⟨by simp only [ulDatT, if_neg h]; exact hda, Or.inr haa⟩
  | psiS s a ihs iha =>
    intro hN hm
    by_cases h : val S (psiS s a) < κ
    · exact ⟨by rw [ulDatT_small h]; exact hcl _ hm h, Or.inl h⟩
    have hβz : q ≤ S.psi (val S a) (Om (val S s + 1)) := hq1.trans (not_lt.1 h)
    have hsem := Term.sem_of_NF (S := S) hN
    obtain ⟨hma, hlt⟩ := arg_mem_of_psi_mem (InR_Om_succ _) hm hβz hqL hsem.2.2
    have hms := Ui.ui_sub_mem_of_psi_mem (S := S) hm hβz
    obtain ⟨hds, has⟩ := ihs hN.1 hms
    obtain ⟨hda, haa⟩ := iha hN.2.1 hma
    exact ⟨by simp only [ulDatT, if_neg h]; exact max_lt hds hda, Or.inr ⟨hlt, has, haa⟩⟩
  | psiI n a iha =>
    intro hN hm
    by_cases h : val S (psiI n a) < κ
    · exact ⟨by rw [ulDatT_small h]; exact hcl _ hm h, Or.inl h⟩
    have hβz : q ≤ S.psi (val S a) (S.I n) := hq1.trans (not_lt.1 h)
    have hsem := Term.sem_of_NF (S := S) hN
    obtain ⟨hma, hlt⟩ := arg_mem_of_psi_mem (InR_I n) hm hβz hqL hsem.2
    obtain ⟨hda, haa⟩ := iha hN.1 hma
    exact ⟨by simp only [ulDatT, if_neg h]; exact hda, Or.inr ⟨hlt, haa⟩⟩

/-! ## On ordinals -/

/-- **The datum below `κ` of an ordinal**, read on its normal form, subscripts included. -/
noncomputable def ulDat (S : InaccSeq.{0}) (κ x : Ordinal.{0}) : Ordinal.{0} := ulDatT S κ (Bc.bcNf S x)

/-- **The collapse arguments (of subterms `≥ κ`) of an ordinal are below `A`**, read on its normal form. -/
def ulArgs (S : InaccSeq.{0}) (κ A x : Ordinal.{0}) : Prop := ulArgsT S κ A (Bc.bcNf S x)

theorem ulDat_lt (h0 : 0 < κ) (x : Ordinal.{0}) : ulDat S κ x < κ := ulDatT_lt h0 _

theorem ul_one_ulDat (x : Ordinal.{0}) : ulDat S (Om 1) x = Ui.uiDat S x := ul_one_dat _

theorem ul_one_ulArgs (A x : Ordinal.{0}) : ulArgs S (Om 1) A x ↔ Ui.uiArgs S A x := ul_one_args A _

/-- **The code test at threshold `κ`**: for `x` in the notation, `x ∈ Cl(A, q) ↔ ulDat κ x < q ∧ ulArgs κ A x`, when
`0 < q ≤ κ`, `q ≤ Λ` and `Cl(A, q) ∩ κ ⊆ q`. -/
theorem ul_code_iff {A q x : Ordinal.{0}} (hx : x ∈ ⋃ a, S.CSet a 0) (hq1 : q ≤ κ) (hqL : q ≤ S.Lam)
    (hcl : ∀ y ∈ S.CSet A q, y < κ → y < q) (hq0 : 0 < q) :
    x ∈ S.CSet A q ↔ ulDat S κ x < q ∧ ulArgs S κ A x := by
  obtain ⟨hN, hv⟩ := Bc.bcNf_spec S hx
  constructor
  · intro h
    rw [← hv] at h
    exact ul_code_dat hq1 hqL hcl hq0 _ hN h
  · rintro ⟨hd, ha⟩
    have := ul_code_mem (S := S) (κ := κ) (A := A) (q := q) _ hd ha
    rwa [hv] at this

/-- **`Ui.ui_code_iff` recovered at `κ = Ω₁`.** -/
theorem ul_one_code_iff {A q x : Ordinal.{0}} (hx : x ∈ ⋃ a, S.CSet a 0) (hq1 : q ≤ Om 1)
    (hcl : ∀ y ∈ S.CSet A q, y < Om 1 → y < q) (hq0 : 0 < q) :
    x ∈ S.CSet A q ↔ Ui.uiDat S x < q ∧ Ui.uiArgs S A x := by
  have hqL : q ≤ S.Lam := hq1.trans (S.Om_lt_Lam S.one_lt_Lam).le
  rw [ul_code_iff (κ := Om 1) hx hq1 hqL hcl hq0, ul_one_ulDat, ul_one_ulArgs]

end Googology.Trans.PoR.InaccPsi.R2.Ul

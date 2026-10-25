import Googology.Trans.PoR.InaccPsi.R2.TiDat

/-!
# The data read on normal forms with the subscripts as leaves, and its code test at every level

`val = Term.val S`, `nf = Bc.bcNf S`, `Cl(A, q) = S.CSet A q`.  `Ti.tiDatT` reads the largest countable leaf of a
normal form but skips the subscripts (`Ω_a`, `ψ_{Ω_{s+1}}`); here the subscripts are leaves too, and the collapse
arguments are recorded, so that membership in a hull is read off the normal form for every ordinal of the notation
(every level `Ω_{k+1}` at once, no bound):

* `uiDatT S t` (**the largest countable leaf of `t`, subscripts included**: `val t` when `val t < Ω₁`; otherwise the
  larger datum of the parts of a sum or of `φ(a, b)`, the datum of `a` at `Ω_a`, the larger datum of `s` and `a` at
  `ψ_{Ω_{s+1}}(a)`, the datum of `a` at `ψ_{I_n}(a)`, `0` at `I_n`, `I_ω`); `uiDatT_small`, `uiDatT_lt_Om1`,
  `ti_le_uiDatT` (`Ti.tiDatT t ≤ uiDatT t`);
* `uiArgsT S A t` (**every collapse argument of an uncountable subterm of `t` is below `A`**);
* `ui_code_mem` (**the hull converse**: `uiDatT t < q` and `uiArgsT A t` give `val t ∈ Cl(A, q)`);
* `ui_sub_mem_of_psi_mem` (the subscript of a collapse `ψ_{Ω_{σ+1}}(d) ∈ Cl(α, β)`, `β ≤ ψ_{Ω_{σ+1}}(d)`, is in
  `Cl(α, β)`), `ui_add_parts` (the two parts of a normal sum);
* `ui_code_dat` (**the hull lemma**: for a normal form `t` with `val t ∈ Cl(A, q)`, `q ≤ Ω₁` and `Cl(A, q) ∩ Ω₁ ⊆ q`:
  `uiDatT t < q` and `uiArgsT A t`);
* `uiDat`, `uiArgs` (on ordinals, through `nf`), `ui_code_iff` (**the code test**: for every `x` of the notation,
  `x ∈ Cl(A, q) ↔ uiDat x < q ∧ uiArgs A x`, under the same hypotheses on `q`).

No new axiom.  New definitions: `uiDatT`, `uiArgsT`, `uiDat`, `uiArgs`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ui

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2

/-- **The largest countable leaf of a term, subscripts included.** -/
noncomputable def uiDatT (S : InaccSeq.{0}) : Term → Ordinal.{0}
  | .zero => 0
  | .inacc n => if val S (inacc n) < Om 1 then val S (inacc n) else 0
  | .inaccW => if val S inaccW < Om 1 then val S inaccW else 0
  | .add a b => if val S (add a b) < Om 1 then val S (add a b) else max (uiDatT S a) (uiDatT S b)
  | .phi a b => if val S (phi a b) < Om 1 then val S (phi a b) else max (uiDatT S a) (uiDatT S b)
  | .om a => if val S (om a) < Om 1 then val S (om a) else uiDatT S a
  | .psiS s a => if val S (psiS s a) < Om 1 then val S (psiS s a) else max (uiDatT S s) (uiDatT S a)
  | .psiI n a => if val S (psiI n a) < Om 1 then val S (psiI n a) else uiDatT S a

/-- **Every collapse argument of an uncountable subterm is below `A`.** -/
def uiArgsT (S : InaccSeq.{0}) (A : Ordinal.{0}) : Term → Prop
  | .zero => True
  | .inacc _ => True
  | .inaccW => True
  | .add a b => val S (add a b) < Om 1 ∨ (uiArgsT S A a ∧ uiArgsT S A b)
  | .phi a b => val S (phi a b) < Om 1 ∨ (uiArgsT S A a ∧ uiArgsT S A b)
  | .om a => val S (om a) < Om 1 ∨ uiArgsT S A a
  | .psiS s a => val S (psiS s a) < Om 1 ∨ (val S a < A ∧ uiArgsT S A s ∧ uiArgsT S A a)
  | .psiI n a => val S (psiI n a) < Om 1 ∨ (val S a < A ∧ uiArgsT S A a)

variable {S : InaccSeq.{0}}

theorem uiDatT_small {t : Term} (h : val S t < Om 1) : uiDatT S t = val S t := by
  cases t with
  | zero => rfl
  | inacc n => simp only [uiDatT, if_pos h]
  | inaccW => simp only [uiDatT, if_pos h]
  | add a b => simp only [uiDatT, if_pos h]
  | phi a b => simp only [uiDatT, if_pos h]
  | om a => simp only [uiDatT, if_pos h]
  | psiS s a => simp only [uiDatT, if_pos h]
  | psiI n a => simp only [uiDatT, if_pos h]

theorem uiDatT_lt_Om1 : ∀ t : Term, uiDatT S t < Om 1 := by
  have h0 : (0 : Ordinal.{0}) < Om 1 := Om_pos one_ne_zero
  intro t
  induction t with
  | zero => exact h0
  | inacc n => by_cases h : val S (inacc n) < Om 1 <;> simp only [uiDatT, h, if_true, if_false] <;> first
      | exact h | exact h0
  | inaccW => by_cases h : val S inaccW < Om 1 <;> simp only [uiDatT, h, if_true, if_false] <;> first
      | exact h | exact h0
  | add a b iha ihb =>
    by_cases h : val S (add a b) < Om 1
    · rw [uiDatT_small h]; exact h
    · simp only [uiDatT, if_neg h]; exact max_lt iha ihb
  | phi a b iha ihb =>
    by_cases h : val S (phi a b) < Om 1
    · rw [uiDatT_small h]; exact h
    · simp only [uiDatT, if_neg h]; exact max_lt iha ihb
  | om a iha =>
    by_cases h : val S (om a) < Om 1
    · rw [uiDatT_small h]; exact h
    · simp only [uiDatT, if_neg h]; exact iha
  | psiS s a ihs iha =>
    by_cases h : val S (psiS s a) < Om 1
    · rw [uiDatT_small h]; exact h
    · simp only [uiDatT, if_neg h]; exact max_lt ihs iha
  | psiI n a iha =>
    by_cases h : val S (psiI n a) < Om 1
    · rw [uiDatT_small h]; exact h
    · simp only [uiDatT, if_neg h]; exact iha

/-- **`Ti.tiDatT t ≤ uiDatT t`**: the subscripts only add leaves. -/
theorem ti_le_uiDatT : ∀ t : Term, Ti.tiDatT S t ≤ uiDatT S t := by
  intro t
  induction t with
  | zero => exact le_rfl
  | inacc n => by_cases h : val S (inacc n) < Om 1 <;> simp only [Ti.tiDatT, uiDatT, h, if_true, if_false, le_rfl]
  | inaccW => by_cases h : val S inaccW < Om 1 <;> simp only [Ti.tiDatT, uiDatT, h, if_true, if_false, le_rfl]
  | add a b iha ihb =>
    by_cases h : val S (add a b) < Om 1
    · rw [Ti.tiDatT_small h, uiDatT_small h]
    · rw [Ti.tiDatT_add h]; simp only [uiDatT, if_neg h]; exact max_le_max iha ihb
  | phi a b iha ihb =>
    by_cases h : val S (phi a b) < Om 1
    · rw [Ti.tiDatT_small h, uiDatT_small h]
    · rw [Ti.tiDatT_phi h]; simp only [uiDatT, if_neg h]; exact max_le_max iha ihb
  | om a _ =>
    by_cases h : val S (om a) < Om 1
    · rw [Ti.tiDatT_small h, uiDatT_small h]
    · rw [Ti.tiDatT_om h]; exact zero_le
  | psiS s a _ iha =>
    by_cases h : val S (psiS s a) < Om 1
    · rw [Ti.tiDatT_small h, uiDatT_small h]
    · rw [Ti.tiDatT_psiS h]; simp only [uiDatT, if_neg h]; exact iha.trans (le_max_right _ _)
  | psiI n a iha =>
    by_cases h : val S (psiI n a) < Om 1
    · rw [Ti.tiDatT_small h, uiDatT_small h]
    · rw [Ti.tiDatT_psiI h]; simp only [uiDatT, if_neg h]; exact iha

/-! ## The hull converse -/

/-- **The hull converse**: a term whose countable leaves (subscripts included) are below `q` and whose collapse
arguments are below `A` denotes a member of `Cl(A, q)`. -/
theorem ui_code_mem {A q : Ordinal.{0}} : ∀ t : Term, uiDatT S t < q → uiArgsT S A t → val S t ∈ S.CSet A q := by
  intro t
  induction t with
  | zero => intro _ _; exact CSet.zero_mem _ _
  | inacc n => intro _ _; exact CSet.I_mem _ _ n
  | inaccW => intro _ _; exact CSet.Iw_mem _ _
  | add a b iha ihb =>
    intro hd ha
    by_cases h : val S (add a b) < Om 1
    · rw [uiDatT_small h] at hd; exact CSet.of_lt hd
    simp only [uiDatT, if_neg h] at hd
    have ha' := ha.resolve_left h
    exact CSet.add_mem (iha (lt_of_le_of_lt (le_max_left _ _) hd) ha'.1)
      (ihb (lt_of_le_of_lt (le_max_right _ _) hd) ha'.2)
  | phi a b iha ihb =>
    intro hd ha
    by_cases h : val S (phi a b) < Om 1
    · rw [uiDatT_small h] at hd; exact CSet.of_lt hd
    simp only [uiDatT, if_neg h] at hd
    have ha' := ha.resolve_left h
    exact CSet.phi_mem (iha (lt_of_le_of_lt (le_max_left _ _) hd) ha'.1)
      (ihb (lt_of_le_of_lt (le_max_right _ _) hd) ha'.2)
  | om a iha =>
    intro hd ha
    by_cases h : val S (om a) < Om 1
    · rw [uiDatT_small h] at hd; exact CSet.of_lt hd
    simp only [uiDatT, if_neg h] at hd
    exact CSet.Om_mem (iha hd (ha.resolve_left h))
  | psiS s a ihs iha =>
    intro hd ha
    by_cases h : val S (psiS s a) < Om 1
    · rw [uiDatT_small h] at hd; exact CSet.of_lt hd
    simp only [uiDatT, if_neg h] at hd
    obtain ⟨hlt, has, haa⟩ := ha.resolve_left h
    exact CSet.psi_mem hlt (InR_Om_succ _)
      (CSet.Om_mem (CSet.succ_mem (ihs (lt_of_le_of_lt (le_max_left _ _) hd) has)))
      (iha (lt_of_le_of_lt (le_max_right _ _) hd) haa)
  | psiI n a iha =>
    intro hd ha
    by_cases h : val S (psiI n a) < Om 1
    · rw [uiDatT_small h] at hd; exact CSet.of_lt hd
    simp only [uiDatT, if_neg h] at hd
    obtain ⟨hlt, haa⟩ := ha.resolve_left h
    exact CSet.psi_mem hlt (InR_I n) (CSet.I_mem _ _ n) (iha hd haa)

/-! ## Reading the parts out of a hull -/

/-- **The subscript of a collapse in a hull is in the hull**: `ψ_{Ω_{σ+1}}(d) ∈ Cl(α, β)` with `β ≤ ψ_{Ω_{σ+1}}(d)`
gives `σ ∈ Cl(α, β)`. -/
theorem ui_sub_mem_of_psi_mem {σ d α β : Ordinal.{0}} (hmem : S.psi d (Om (σ + 1)) ∈ S.CSet α β)
    (hβz : β ≤ S.psi d (Om (σ + 1))) : σ ∈ S.CSet α β := by
  have hκ : S.InR (Om (σ + 1)) := InR_Om_succ σ
  have hSC := SC_psi hκ d
  rcases prin_mem_cases hmem hβz hSC.isPrincipal hSC.1.ne' with
    ⟨n, hn⟩ | hw | ⟨p, q, _, _, hp, hq, hpq⟩ | ⟨p, _, hp, hpz⟩ | ⟨π, e, hπ, hπC, _, _, hz⟩
  · exact absurd (hn.trans (Om_I n).symm) (not_Om_of_between (psiS_bounds d σ).1 (psiS_bounds d σ).2 (S.I n))
  · exact absurd (hw.trans S.Om_Iw.symm) (not_Om_of_between (psiS_bounds d σ).1 (psiS_bounds d σ).2 S.Iw)
  · exact absurd hpq.symm (hSC.not_veblen_lt hp hq)
  · exact absurd hpz (not_Om_of_between (psiS_bounds d σ).1 (psiS_bounds d σ).2 p)
  · have hπκ : π = Om (σ + 1) := sub_eq_of_psi_eq hπ hκ hz.symm
    rw [hπκ] at hπC
    exact mem_of_add_one_mem (mem_of_Om_mem hπC)

/-- **The two parts of a normal sum** `add a b` denote its leading summand and the rest. -/
theorem ui_add_parts {a b : Term} (h : NF (add a b)) :
    lead (val S (add a b)) = val S a ∧ tail (val S (add a b)) = val S b := by
  obtain ⟨ha, hb, hpa, hb0, hh⟩ := h
  have hP := Term.isPrincipal_val S ha hpa
  have ha0 : val S a ≠ 0 := Term.val_ne_zero (S := S) ha (Term.NF.ne_zero_of_isPrin hpa)
  obtain ⟨g, hg⟩ := exists_opow_of_principal hP ha0
  have hle : val S (head b) ≤ val S a := by
    have e := Term.cmp_eq_compare S hb.head ha
    rw [e] at hh; exact not_lt.1 fun h' => hh (compare_gt_iff_gt.2 h')
  have hblt : val S b < ω ^ (g + 1) := by
    refine Br.val_lt_of_head hb (isPrincipal_add_omega0_opow _) (lt_of_le_of_lt hle ?_)
    rw [hg]; exact opow_lt_opow_add_one g
  simp only [val]
  rw [hg, lead_opow_add hblt, tail_opow_add hblt]
  exact ⟨rfl, rfl⟩

/-! ## The hull lemma -/

/-- **The hull lemma**: a normal form `t` with `val t ∈ Cl(A, q)` has all its countable leaves (subscripts included)
below `q` and all its collapse arguments below `A`, when `q ≤ Ω₁` and `Cl(A, q) ∩ Ω₁ ⊆ q`. -/
theorem ui_code_dat {A q : Ordinal.{0}} (hq1 : q ≤ Om 1) (hcl : ∀ x ∈ S.CSet A q, x < Om 1 → x < q)
    (hq0 : 0 < q) : ∀ t : Term, NF t → val S t ∈ S.CSet A q → uiDatT S t < q ∧ uiArgsT S A t := by
  have hqL : q ≤ S.Lam := hq1.trans (S.Om_lt_Lam S.one_lt_Lam).le
  intro t
  induction t with
  | zero => intro _ _; exact ⟨hq0, trivial⟩
  | inacc n =>
    intro _ _
    by_cases h : val S (inacc n) < Om 1
    · exact ⟨by rw [uiDatT_small h]; exact hcl _ (CSet.I_mem _ _ n) h, trivial⟩
    · exact ⟨by simp only [uiDatT, if_neg h]; exact hq0, trivial⟩
  | inaccW =>
    intro _ _
    by_cases h : val S inaccW < Om 1
    · exact ⟨by rw [uiDatT_small h]; exact hcl _ (CSet.Iw_mem _ _) h, trivial⟩
    · exact ⟨by simp only [uiDatT, if_neg h]; exact hq0, trivial⟩
  | add a b iha ihb =>
    intro hN hm
    by_cases h : val S (add a b) < Om 1
    · exact ⟨by rw [uiDatT_small h]; exact hcl _ hm h, Or.inl h⟩
    have h0 : val S (add a b) ≠ 0 := fun e => h (by rw [e]; exact Om_pos one_ne_zero)
    obtain ⟨hl, ht⟩ := lead_tail_mem hm h0
    obtain ⟨hla, htb⟩ := ui_add_parts (S := S) hN
    rw [hla] at hl; rw [htb] at ht
    obtain ⟨hda, haa⟩ := iha hN.1 hl
    obtain ⟨hdb, hab⟩ := ihb hN.2.1 ht
    exact ⟨by simp only [uiDatT, if_neg h]; exact max_lt hda hdb, Or.inr ⟨haa, hab⟩⟩
  | phi a b iha ihb =>
    intro hN hm
    by_cases h : val S (phi a b) < Om 1
    · exact ⟨by rw [uiDatT_small h]; exact hcl _ hm h, Or.inl h⟩
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
    exact ⟨by simp only [uiDatT, if_neg h]; exact max_lt hda hdb, Or.inr ⟨haa, hab⟩⟩
  | om a iha =>
    intro hN hm
    by_cases h : val S (om a) < Om 1
    · exact ⟨by rw [uiDatT_small h]; exact hcl _ hm h, Or.inl h⟩
    obtain ⟨hda, haa⟩ := iha hN.1 (mem_of_Om_mem hm)
    exact ⟨by simp only [uiDatT, if_neg h]; exact hda, Or.inr haa⟩
  | psiS s a ihs iha =>
    intro hN hm
    by_cases h : val S (psiS s a) < Om 1
    · exact ⟨by rw [uiDatT_small h]; exact hcl _ hm h, Or.inl h⟩
    have hβz : q ≤ S.psi (val S a) (Om (val S s + 1)) := hq1.trans (not_lt.1 h)
    have hsem := Term.sem_of_NF (S := S) hN
    obtain ⟨hma, hlt⟩ := arg_mem_of_psi_mem (InR_Om_succ _) hm hβz hqL hsem.2.2
    have hms := ui_sub_mem_of_psi_mem (S := S) hm hβz
    obtain ⟨hds, has⟩ := ihs hN.1 hms
    obtain ⟨hda, haa⟩ := iha hN.2.1 hma
    exact ⟨by simp only [uiDatT, if_neg h]; exact max_lt hds hda, Or.inr ⟨hlt, has, haa⟩⟩
  | psiI n a iha =>
    intro hN hm
    by_cases h : val S (psiI n a) < Om 1
    · exact ⟨by rw [uiDatT_small h]; exact hcl _ hm h, Or.inl h⟩
    have hβz : q ≤ S.psi (val S a) (S.I n) := hq1.trans (not_lt.1 h)
    have hsem := Term.sem_of_NF (S := S) hN
    obtain ⟨hma, hlt⟩ := arg_mem_of_psi_mem (InR_I n) hm hβz hqL hsem.2
    obtain ⟨hda, haa⟩ := iha hN.1 hma
    exact ⟨by simp only [uiDatT, if_neg h]; exact hda, Or.inr ⟨hlt, haa⟩⟩

/-! ## On ordinals -/

/-- **The data of an ordinal**, read on its normal form, subscripts included. -/
noncomputable def uiDat (S : InaccSeq.{0}) (x : Ordinal.{0}) : Ordinal.{0} := uiDatT S (Bc.bcNf S x)

/-- **The collapse arguments of an ordinal are below `A`**, read on its normal form. -/
def uiArgs (S : InaccSeq.{0}) (A x : Ordinal.{0}) : Prop := uiArgsT S A (Bc.bcNf S x)

theorem uiDat_lt_Om1 (x : Ordinal.{0}) : uiDat S x < Om 1 := uiDatT_lt_Om1 _

theorem ti_le_uiDat (x : Ordinal.{0}) : Ti.tiDat S x ≤ uiDat S x := ti_le_uiDatT _

/-- **The code test**: for `x` in the notation, `x ∈ Cl(A, q) ↔ uiDat x < q ∧ uiArgs A x`, when `0 < q ≤ Ω₁` and
`Cl(A, q) ∩ Ω₁ ⊆ q`. -/
theorem ui_code_iff {A q x : Ordinal.{0}} (hx : x ∈ ⋃ a, S.CSet a 0) (hq1 : q ≤ Om 1)
    (hcl : ∀ y ∈ S.CSet A q, y < Om 1 → y < q) (hq0 : 0 < q) :
    x ∈ S.CSet A q ↔ uiDat S x < q ∧ uiArgs S A x := by
  obtain ⟨hN, hv⟩ := Bc.bcNf_spec S hx
  constructor
  · intro h
    rw [← hv] at h
    exact ui_code_dat hq1 hcl hq0 _ hN h
  · rintro ⟨hd, ha⟩
    have := ui_code_mem (S := S) (A := A) (q := q) _ hd ha
    rwa [hv] at this

end Googology.Trans.PoR.InaccPsi.R2.Ui

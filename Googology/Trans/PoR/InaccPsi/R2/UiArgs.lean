import Googology.Trans.PoR.InaccPsi.R2.UiCode
import Googology.Trans.PoR.InaccPsi.ConjT

/-!
# Below `θ = ψ_{Ω₂}(Ω_ω)` every collapse argument is below `Ω_ω`: the code test at every level below `θ`

`θ = ConjT.th S = ψ_{Ω₂}(Ω_ω)`, `Cl(A, q) = S.CSet A q`, `uiDatT`, `uiArgsT`, `uiDat`, `uiArgs` (`R2.UiCode`).

* `uiArgsT_mono` (`uiArgsT A t → A ≤ A' → uiArgsT A' t`);
* `ui_args_hull` (**the hull lemma for the arguments above a point `q ≥ Ω₁`**: a normal form `t` with `val t ∈ Cl(A,
  q)`, `A ≤ B`, has every collapse argument of an uncountable subterm below `B`, once the normal forms with values in
  `[Ω₁, q)` have);
* `ui_args_th` (**every `z < θ` of the notation has all its collapse arguments below `Ω_ω`**: the atoms of `z` are
  `ψ_{Ω₂}(e)` with `e` own and `ψ_{Ω₂}(e) < ψ_{Ω₂}(Ω_ω)`, so `e < Ω_ω`, and the arguments inside `e` are below `e`
  by the hull lemma at `q = ψ_{Ω₂}(e)`);
* `ui_code_th` (**the code test below `θ`**: for `z < θ` of the notation, `Ω_ω ≤ A`, `0 < q ≤ Ω₁` and `Cl(A, q) ∩ Ω₁ ⊆
  q`: `z ∈ Cl(A, q) ↔ uiDat z < q`).

This is the analog of `Uf.uf_args_E` (`TwArgs` at `ε_{Ω₂+1}` below `B₂`) at the bound `θ`, read on normal forms.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ui

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2

variable {S : InaccSeq.{0}}

theorem uiArgsT_mono {A A' : Ordinal.{0}} (hA : A ≤ A') : ∀ t : Term, uiArgsT S A t → uiArgsT S A' t := by
  intro t
  induction t with
  | zero => intro _; trivial
  | inacc n => intro _; trivial
  | inaccW => intro _; trivial
  | add a b iha ihb =>
    intro h; rcases h with h | h
    · exact Or.inl h
    · exact Or.inr ⟨iha h.1, ihb h.2⟩
  | phi a b iha ihb =>
    intro h; rcases h with h | h
    · exact Or.inl h
    · exact Or.inr ⟨iha h.1, ihb h.2⟩
  | om a iha =>
    intro h; rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (iha h)
  | psiS s a ihs iha =>
    intro h; rcases h with h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1.trans_le hA, ihs h2, iha h3⟩
  | psiI n a iha =>
    intro h; rcases h with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1.trans_le hA, iha h2⟩

/-- **The hull lemma for the arguments above `q ≥ Ω₁`.** -/
theorem ui_args_hull {A B q : Ordinal.{0}} (hq1 : Om 1 ≤ q) (hqL : q ≤ S.Lam) (hAB : A ≤ B)
    (hlow : ∀ u : Term, NF u → Om 1 ≤ val S u → val S u < q → uiArgsT S B u) :
    ∀ t : Term, NF t → val S t ∈ S.CSet A q → uiArgsT S B t := by
  intro t
  induction t with
  | zero => intro _ _; trivial
  | inacc n => intro _ _; trivial
  | inaccW => intro _ _; trivial
  | add a b iha ihb =>
    intro hN hm
    by_cases h : val S (add a b) < Om 1
    · exact Or.inl h
    by_cases hq : val S (add a b) < q
    · exact hlow _ hN (not_lt.1 h) hq
    have h0 : val S (add a b) ≠ 0 := fun e => h (by rw [e]; exact Om_pos one_ne_zero)
    obtain ⟨hl, ht⟩ := lead_tail_mem hm h0
    obtain ⟨hla, htb⟩ := ui_add_parts (S := S) hN
    rw [hla] at hl; rw [htb] at ht
    exact Or.inr ⟨iha hN.1 hl, ihb hN.2.1 ht⟩
  | phi a b iha ihb =>
    intro hN hm
    by_cases h : val S (phi a b) < Om 1
    · exact Or.inl h
    by_cases hq : val S (phi a b) < q
    · exact hlow _ hN (not_lt.1 h) hq
    have hN' := hN
    obtain ⟨hNa, hNb, hca, hcb⟩ := hN
    have hav : val S a < val S (phi a b) := by
      have e := Term.cmp_eq_compare S hNa hN'
      rw [e] at hca; exact compare_lt_iff_lt.1 hca
    have hbv : val S b < val S (phi a b) := by
      have e := Term.cmp_eq_compare S hNb hN'
      rw [e] at hcb; exact compare_lt_iff_lt.1 hcb
    obtain ⟨hma, hmb⟩ := mem_of_veblen_mem hm hav hbv
    exact Or.inr ⟨iha hNa hma, ihb hNb hmb⟩
  | om a iha =>
    intro hN hm
    by_cases h : val S (om a) < Om 1
    · exact Or.inl h
    by_cases hq : val S (om a) < q
    · exact hlow _ hN (not_lt.1 h) hq
    exact Or.inr (iha hN.1 (mem_of_Om_mem hm))
  | psiS s a ihs iha =>
    intro hN hm
    by_cases h : val S (psiS s a) < Om 1
    · exact Or.inl h
    by_cases hq : val S (psiS s a) < q
    · exact hlow _ hN (not_lt.1 h) hq
    have hβz : q ≤ S.psi (val S a) (Om (val S s + 1)) := not_lt.1 hq
    have hsem := Term.sem_of_NF (S := S) hN
    obtain ⟨hma, hlt⟩ := arg_mem_of_psi_mem (InR_Om_succ _) hm hβz hqL hsem.2.2
    have hms := ui_sub_mem_of_psi_mem (S := S) hm hβz
    exact Or.inr ⟨hlt.trans_le hAB, ihs hN.1 hms, iha hN.2.1 hma⟩
  | psiI n a iha =>
    intro hN hm
    by_cases h : val S (psiI n a) < Om 1
    · exact Or.inl h
    by_cases hq : val S (psiI n a) < q
    · exact hlow _ hN (not_lt.1 h) hq
    have hβz : q ≤ S.psi (val S a) (S.I n) := not_lt.1 hq
    have hsem := Term.sem_of_NF (S := S) hN
    obtain ⟨hma, hlt⟩ := arg_mem_of_psi_mem (InR_I n) hm hβz hqL hsem.2
    exact Or.inr ⟨hlt.trans_le hAB, iha hN.1 hma⟩

theorem ui_th_lt_Om2 : ConjT.th S < Om (1 + 1) := psi_lt (InR_Om_succ 1) _

theorem ui_OmW_own : Om ω ∈ S.CSet (Om ω) (S.psi (Om ω) (Om (1 + 1))) := ConjT.OmW_mem S _ _

/-- **Every `z < θ` of the notation has all its collapse arguments below `Ω_ω`.** -/
theorem ui_args_th : ∀ z, z ∈ ⋃ a, S.CSet a 0 → z < ConjT.th S → uiArgs S (Om ω) z := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hz hzθ
  obtain ⟨hN, hv⟩ := Bc.bcNf_spec S hz
  have hsub : ∀ u : Term, NF u → val S u < z → uiArgsT S (Om ω) u := fun u hu hlt => by
    have h := IH (val S u) hlt (Set.mem_iUnion.2 (exists_mem_CSet S u)) (hlt.trans hzθ)
    unfold uiArgs at h; rwa [Bc.bcNf_val S hu] at h
  have hz2 : z < Om (1 + 1) := hzθ.trans ui_th_lt_Om2
  unfold uiArgs
  generalize Bc.bcNf S z = t at hN hv
  subst hv
  cases t with
  | zero => trivial
  | inacc n => trivial
  | inaccW => trivial
  | add a b =>
    by_cases h : val S (add a b) < Om 1
    · exact Or.inl h
    have h0 : val S (add a b) ≠ 0 := fun e => h (by rw [e]; exact Om_pos one_ne_zero)
    obtain ⟨hla, htb⟩ := ui_add_parts (S := S) hN
    have htl : tail (val S (add a b)) < val S (add a b) := tail_lt h0
    have hb0 : val S b ≠ 0 := Term.val_ne_zero (S := S) hN.2.1 hN.2.2.2.1
    have hal : lead (val S (add a b)) < val S (add a b) := by
      conv_rhs => rw [← lead_add_tail h0]
      rw [htb]; exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 hb0)
    rw [hla] at hal; rw [htb] at htl
    exact Or.inr ⟨hsub a hN.1 hal, hsub b hN.2.1 htl⟩
  | phi a b =>
    by_cases h : val S (phi a b) < Om 1
    · exact Or.inl h
    have hN' := hN
    obtain ⟨hNa, hNb, hca, hcb⟩ := hN
    have hav : val S a < val S (phi a b) := by
      have e := Term.cmp_eq_compare S hNa hN'
      rw [e] at hca; exact compare_lt_iff_lt.1 hca
    have hbv : val S b < val S (phi a b) := by
      have e := Term.cmp_eq_compare S hNb hN'
      rw [e] at hcb; exact compare_lt_iff_lt.1 hcb
    exact Or.inr ⟨hsub a hNa hav, hsub b hNb hbv⟩
  | om a =>
    by_cases h : val S (om a) < Om 1
    · exact Or.inl h
    refine Or.inr (hsub a hN.1 ?_)
    have h2 : val S a < 1 + 1 := Om_lt_Om.1 hz2
    have h2' : val S a < ω := h2.trans (by exact_mod_cast natCast_lt_omega0 2)
    exact h2'.trans_le ((omega0_le_omega 1).trans (by rw [← Om_of_ne_zero one_ne_zero]; exact not_lt.1 h))
  | psiS s a =>
    by_cases h : val S (psiS s a) < Om 1
    · exact Or.inl h
    have hsem := Term.sem_of_NF (S := S) hN
    set σ := val S s with hσ
    have hb := psiS_bounds (S := S) (val S a) σ
    have hσ1 : σ = 1 := by
      have h1 : Om σ < Om (1 + 1) := hb.1.trans hz2
      have h3 : Om 1 < Om (σ + 1) := (not_lt.1 h).trans_lt hb.2
      have ha : σ < 1 + 1 := Om_lt_Om.1 h1
      have hb' : 1 < σ + 1 := Om_lt_Om.1 h3
      have hle : σ ≤ 1 := Order.lt_add_one_iff.1 ha
      have hge : 1 ≤ σ := Order.lt_add_one_iff.1 hb'
      exact le_antisymm hle hge
    have hval : val S (psiS s a) = S.psi (val S a) (Om (1 + 1)) := by simp only [val]; rw [← hσ, hσ1]
    have hown : val S a ∈ S.CSet (val S a) (S.psi (val S a) (Om (1 + 1))) := by
      have := hsem.2.2; rw [← hσ, hσ1] at this; exact this
    have haW : val S a < Om ω := by
      have h1 := compare_psi (InR_Om_succ 1) hown ui_OmW_own
      have h2 : S.psi (val S a) (Om (1 + 1)) < S.psi (Om ω) (Om (1 + 1)) := by
        rw [← hval]; exact hzθ
      rw [compare_lt_iff_lt.2 h2] at h1
      exact compare_lt_iff_lt.1 h1.symm
    have hs1 : σ < val S (psiS s a) := by
      rw [hσ1]; exact (Ordinal.one_lt_omega0.trans_le (omega0_le_omega 1)).trans_le
        (by rw [← Om_of_ne_zero one_ne_zero]; exact not_lt.1 h)
    have hsa := hsub s hN.1 hs1
    have hqL : val S (psiS s a) ≤ S.Lam := (Om_lt_Lam_of hz2).le
    refine Or.inr ⟨haW, hsa, ui_args_hull (A := val S a) (B := Om ω) (q := val S (psiS s a)) (not_lt.1 h) hqL
      haW.le (fun u hu _ hlt => hsub u hu hlt) a hN.2.1 ?_⟩
    rw [hval]; exact hown
  | psiI n a =>
    by_cases h : val S (psiI n a) < Om 1
    · exact Or.inl h
    exfalso
    have hfix : Om (val S (psiI n a)) = val S (psiI n a) := Om_psiI _ n
    have h2 : val S (psiI n a) < 1 + 1 := by
      have := hz2; rw [← hfix] at this; exact Om_lt_Om.1 this
    have h3 : val S (psiI n a) < ω := h2.trans (by exact_mod_cast natCast_lt_omega0 2)
    exact absurd (h3.trans_le ((omega0_le_omega 1).trans (by rw [← Om_of_ne_zero one_ne_zero]; exact not_lt.1 h)))
      (lt_irrefl _)
  where
    Om_lt_Lam_of {x : Ordinal.{0}} (hx : x < Om (1 + 1)) : x < S.Lam :=
      hx.trans (S.Om_lt_Lam (S.add_one_lt_Lam S.one_lt_Lam))

/-- **The code test below `θ = ψ_{Ω₂}(Ω_ω)`**: for `z < θ` of the notation, `Ω_ω ≤ A`, `0 < q ≤ Ω₁` and
`Cl(A, q) ∩ Ω₁ ⊆ q`: `z ∈ Cl(A, q) ↔ uiDat z < q`. -/
theorem ui_code_th {A q z : Ordinal.{0}} (hz : z ∈ ⋃ a, S.CSet a 0) (hzθ : z < ConjT.th S) (hA : Om ω ≤ A)
    (hq1 : q ≤ Om 1) (hcl : ∀ y ∈ S.CSet A q, y < Om 1 → y < q) (hq0 : 0 < q) :
    z ∈ S.CSet A q ↔ uiDat S z < q := by
  rw [ui_code_iff hz hq1 hcl hq0]
  exact ⟨fun h => h.1, fun h => ⟨h, uiArgsT_mono hA _ (ui_args_th z hz hzθ)⟩⟩

end Googology.Trans.PoR.InaccPsi.R2.Ui

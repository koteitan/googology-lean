import Googology.Trans.PoR.InaccPsi.R2.RnEQ

/-!
# The bases `Ω₂^{Ω₂}·γ` for every code `γ < T₁ = ψ_{Ω₂}(Ω₂^{Ω₂+1})`, and their readings

`μ = W^W = Ω₂^{Ω₂}`, `O = Ω₁^{Ω₁}` (`Le.leOe (Om 1)`), `T₁ = ψ_{Ω₂}(μ·Ω₂)` (`rnT1`), `Θ = gxTh ρ_λ (ldAtR λ)`.

* `rnKW` (`K_0 = Ω₁`, `K_{j+1} = ψ_{Ω₂}(μ·K_j)`), `rnKW_sup` (**`T₁ = sup_j K_j`**, from `Le.lePsi2_le` and the digit
  bound `Le.leCl_boundY`: a code below `Ω₂^{Ω₂+1}` is below `μ·Q`), `rnT1_gt` (**`γ < ψ_{Ω₂}(μ·γ)` for every
  `γ < T₁`**), `rnT1_ge`;
* `rnBg_base` (**`μ·γ` is a base** (`Rn.RnBase`) for every `γ ∈ H_λ`, `γ < T₁`);
* `rnThG` (**`Θ_λ(ψ_{Ω₂}(μ·γ)) = ψ_{Ω₁}(A + 1 + O·Θ_λ(γ))`** for every code `γ < T₁`, `A` own with
  `ψ_{Ω₁}(A) = ρ_λ`: the successor step is the pull-back `Rn.rnTopW` at the base `μ·γ`, the limit step reads the
  sub-bases `μ·γ'`, `γ' < γ`, as in `Le.leStepA`).

No new axiom.  New definitions: `rnKW`, `rnT1`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le

variable {S : InaccSeq.{0}}

/-- `K_0 = Ω₁`, `K_{j+1} = ψ_{Ω₂}(Ω₂^{Ω₂}·K_j)`. -/
noncomputable def rnKW (S : InaccSeq.{0}) : ℕ → Ordinal.{0}
  | 0 => Om 1
  | j + 1 => S.psi (leWe (Om (1 + 1)) * rnKW S j) (Om (1 + 1))

/-- `T₁ = ψ_{Ω₂}(Ω₂^{Ω₂}·Ω₂) = ψ_{Ω₂}(Ω₂^{Ω₂+1})`. -/
noncomputable def rnT1 (S : InaccSeq.{0}) : Ordinal.{0} := S.psi (leWe (Om (1 + 1)) * Om (1 + 1)) (Om (1 + 1))

theorem rnT1_SC : SC (rnT1 S) := SC_psi (InR_Om_succ 1) _
theorem rnT1_lt_Om2 : rnT1 S < Om (1 + 1) := psi_lt (InR_Om_succ 1) _

theorem rnKW_lt_Om2 : ∀ j, rnKW S j < Om (1 + 1)
  | 0 => gg_Om1_lt_Om2
  | _ + 1 => psi_lt (InR_Om_succ 1) _

theorem rnKW_SC : ∀ j, SC (rnKW S j)
  | 0 => Ph.ph_SC_Om1
  | _ + 1 => SC_psi (InR_Om_succ 1) _

theorem rnMuW_eq : leWe (Om (1 + 1)) * Om (1 + 1) = ω ^ (Om (1 + 1) * Om (1 + 1) + Om (1 + 1)) := by
  unfold leWe; rw [opow_add, gg_SC_eps ldOm2_SC]

theorem rnMuW_lt_OmW : leWe (Om (1 + 1)) * Om (1 + 1) < Om ω := by
  have hSC : SC (Om (ω : Ordinal.{0})) := SC_Om omega0_ne_zero
  rw [rnMuW_eq]
  exact ldOpow_lt_SC hSC (hSC.isPrincipal ldOm2sq_lt_OmW ldOm2_lt_OmW)

theorem rnT1_lt_th : rnT1 S < ConjT.th S :=
  psi_lt_psi_of_mem (InR_Om_succ 1) rnMuW_lt_OmW (leMulWe_mem (mxOm2_mem _ _) (mxOm2_mem _ _))

theorem rnKW_lt_succ : ∀ j, rnKW S j < rnKW S (j + 1)
  | 0 => (psiS_bounds (S := S) _ 1).1
  | j + 1 => by
    have IH := rnKW_lt_succ j
    have hle : rnKW S (j + 1) ≤ rnKW S (j + 2) := (psi_mono (S := S) (InR_Om_succ 1) (leMulWe_mono IH.le)).1
    exact psi_lt_psi_of_mem (InR_Om_succ 1) (leMulWe_lt IH)
      (leMulWe_mem (mxOm2_mem _ _) (CSet.of_lt (IH.trans_le hle)))

theorem rnKW_mono {j j' : ℕ} (h : j ≤ j') : rnKW S j ≤ rnKW S j' :=
  (strictMono_nat_of_lt_succ (fun i => rnKW_lt_succ (S := S) i)).monotone h

theorem rnKW_gt : ∀ j γ, γ < rnKW S j → γ < S.psi (leWe (Om (1 + 1)) * γ) (Om (1 + 1))
  | 0, γ, h => h.trans (psiS_bounds (S := S) _ 1).1
  | j + 1, γ, h => by
    rcases lt_or_ge γ (rnKW S j) with h' | h'
    · exact rnKW_gt j γ h'
    · exact h.trans_le (psi_mono (S := S) (InR_Om_succ 1) (leMulWe_mono h')).1

theorem rnKW_le_top : ∀ j, rnKW S j ≤ rnT1 S
  | 0 => (psiS_bounds (S := S) _ 1).1.le
  | j + 1 => (psi_mono (S := S) (InR_Om_succ 1) (leMulWe_mono (rnKW_lt_Om2 j).le)).1

/-- **`T₁ = sup_j K_j`.** -/
theorem rnKW_sup {x : Ordinal.{0}} (hx : x < rnT1 S) : ∃ j, x < rnKW S j := by
  have hbdd : BddAbove (Set.range (rnKW S)) := Ordinal.bddAbove_of_small
  have hlt : ∀ y, y < ⨆ j, rnKW S j ↔ ∃ j, y < rnKW S j := fun y => lt_ciSup_iff hbdd
  have hKQ : ∀ j, rnKW S j < ⨆ j, rnKW S j := fun j => (hlt _).2 ⟨j + 1, rnKW_lt_succ j⟩
  have hΩQ : Om (1 : Ordinal.{0}) < ⨆ j, rnKW S j := hKQ 0
  have hQSC : SC (⨆ j, rnKW S j) := by
    refine ⟨(Om_pos one_ne_zero).trans hΩQ, fun x hx y hy => ?_⟩
    obtain ⟨i, hi⟩ := (hlt _).1 hx
    obtain ⟨j, hj⟩ := (hlt _).1 hy
    have hi' := hi.trans_le (rnKW_mono (S := S) (le_max_left i j))
    have hj' := hj.trans_le (rnKW_mono (S := S) (le_max_right i j))
    exact ((rnKW_SC (max i j)).2 _ hi' _ hj').trans (hKQ _)
  set Q := ⨆ j, rnKW S j with hQ
  have hG3 : SC (S.psi 0 (Om (1 + 1 + 1))) := SC_psi (InR_Om_succ (1 + 1)) 0
  have hWG3 : Om (1 + 1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1 + 1)) := (psiS_bounds (S := S) 0 (1 + 1)).1
  have hμ0 : leWe (Om (1 + 1)) ≠ 0 := (leWe_pos _).ne'
  have hFQ : rnT1 S ≤ Q := by
    refine lePsi2_le hQSC hΩQ fun x hx hc => ?_
    have hxG : x < S.psi 0 (Om (1 + 1 + 1)) := by
      refine hx.trans ?_
      rw [rnMuW_eq]
      exact ldOpow_lt_SC hG3 (hG3.isPrincipal (ldMul_lt_SC hG3 hWG3 hWG3) hWG3)
    rw [Ordinal.mod_eq_of_lt hxG] at hc
    have hb := leCl_boundY hQSC ldOm2_SC (LeCl.om (κ := Om (1 + 1)) (Q := Q)) x hc (by rw [← rnMuW_eq]; exact hx)
    change x < leWe (Om (1 + 1)) * Q at hb
    have hq : x / leWe (Om (1 + 1)) < Q := (Ordinal.lt_mul_iff_div_lt hμ0).1 hb
    obtain ⟨j, hj⟩ := (hlt _).1 hq
    have hxj : x < leWe (Om (1 + 1)) * rnKW S j := by
      calc x < leWe (Om (1 + 1)) * (x / leWe (Om (1 + 1))) + leWe (Om (1 + 1)) := Ordinal.lt_mul_div_add _ hμ0
        _ = leWe (Om (1 + 1)) * (x / leWe (Om (1 + 1)) + 1) := (mul_add_one _ _).symm
        _ ≤ leWe (Om (1 + 1)) * rnKW S j := leMulWe_mono (Order.add_one_le_of_lt hj)
    exact ((psi_mono (S := S) (InR_Om_succ 1) hxj.le).1).trans_lt (hKQ (j + 1))
  exact (hlt x).1 (hx.trans_le hFQ)

/-- **`γ < ψ_{Ω₂}(μ·γ)` for every `γ < T₁`.** -/
theorem rnT1_gt {γ : Ordinal.{0}} (hγ : γ < rnT1 S) : γ < S.psi (leWe (Om (1 + 1)) * γ) (Om (1 + 1)) := by
  obtain ⟨j, hj⟩ := rnKW_sup hγ
  exact rnKW_gt j γ hj

/-- `ψ_{Ω₂}(μ·γ) ≥ T₁` for `γ ≥ T₁`. -/
theorem rnT1_ge {γ : Ordinal.{0}} (hγ : rnT1 S ≤ γ) : rnT1 S ≤ S.psi (leWe (Om (1 + 1)) * γ) (Om (1 + 1)) := by
  by_contra h
  push Not at h
  obtain ⟨j, hj⟩ := rnKW_sup h
  have h1 : rnKW S (j + 1) ≤ S.psi (leWe (Om (1 + 1)) * γ) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) (leMulWe_mono ((rnKW_le_top j).trans hγ))).1
  exact absurd (hj.trans_le ((rnKW_lt_succ j).le.trans h1)) (lt_irrefl _)

/-- **`μ·γ` is a base** for every `γ ∈ H_λ`, `γ < T₁`. -/
theorem rnBg_base (l : Ordinal.{0}) {γ : Ordinal.{0}} (hγH : γ ∈ cdHull S l) (hγT : γ < rnT1 S) :
    RnBase S l (leWe (Om (1 + 1)) * γ) := by
  have hγW : γ < Om (1 + 1) := hγT.trans rnT1_lt_Om2
  have hγ1W : γ + 1 < Om (1 + 1) := ldOm2_SC.isSuccLimit.succ_lt hγW
  refine ⟨dvd_mul_right _ _, leMulWe_mem (mxOm2_mem _ _) hγH, ?_, fun d _ => ?_⟩
  · rw [← mul_add_one]
    exact ((leMulWe_lt hγ1W).trans rnMuW_lt_OmW).trans_le le_self_add
  · refine leMulWe_mem (mxOm2_mem _ _) (CSet.of_lt ?_)
    exact (rnT1_gt hγT).trans_le (psi_mono (S := S) (InR_Om_succ 1) le_self_add).1

theorem rnMuG_atom {l ηx γ : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hγ : GxCl (upsilon l) (ldAtR S l) γ) (hγW : γ < Om (1 + 1)) :
    S.psi (leWe (Om (1 + 1)) * γ) (Om (1 + 1)) ∈ ldAtR S l :=
  ⟨leWe (Om (1 + 1)) * γ, leMulWe_mem (mxOm2_mem _ _) ((ldHull_iff hl hX hγW).2 hγ),
    ((leMulWe_lt hγW).trans rnMuW_lt_OmW).trans_le le_self_add, rfl⟩

/-- **`Θ_λ(ψ_{Ω₂}(Ω₂^{Ω₂}·γ)) = ψ_{Ω₁}(A + 1 + Ω₁^{Ω₁}·Θ_λ(γ))`** for every code `γ < T₁`. -/
theorem rnThG {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    ∀ γ, GxCl (upsilon l) (ldAtR S l) γ → γ < rnT1 S →
      gxTh (upsilon l) (ldAtR S l) (S.psi (leWe (Om (1 + 1)) * γ) (Om (1 + 1))) =
        S.psi (A + 1 + leOe (Om 1) * gxTh (upsilon l) (ldAtR S l) γ) (Om 1) ∧
      A + 1 + leOe (Om 1) * gxTh (upsilon l) (ldAtR S l) γ ∈
        S.CSet (A + 1 + leOe (Om 1) * gxTh (upsilon l) (ldAtR S l) γ)
          (S.psi (A + 1 + leOe (Om 1) * gxTh (upsilon l) (ldAtR S l) γ) (Om 1)) := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hρ0 : 0 < upsilon l := hρSC.1
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small (gg_one_lt_of_SC hρSC).le
  have hÂ : A + 1 ∈ S.CSet (A + 1) (S.psi (A + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA) (CSet.one_mem _ _)
  have hbase : gxTh (upsilon l) (ldAtR S l) (S.psi 0 (Om (1 + 1))) = S.psi (A + 1) (Om 1) := ldBlk_zero hA hρ
  have hμ0 : leWe (Om (1 + 1)) ≠ 0 := (leWe_pos _).ne'
  have hO0 : leOe (Om 1) ≠ 0 := (leOe_pos _).ne'
  have hβat : S.psi 0 (Om (1 + 1)) ∈ ldAtR S l :=
    ⟨0, CSet.zero_mem _ _, (Om_pos (by simp)).trans_le le_self_add, rfl⟩
  have hρÂ : upsilon l < S.psi (A + 1) (Om 1) := by
    rw [← hbase]; exact (ldAtom_ge hρSC hρ1 hAt hβat).2.1
  have hslt : ∀ γ γ', γ < γ' → γ < S.psi (leWe (Om (1 + 1)) * γ') (Om (1 + 1)) →
      S.psi (leWe (Om (1 + 1)) * γ) (Om (1 + 1)) < S.psi (leWe (Om (1 + 1)) * γ') (Om (1 + 1)) :=
    fun γ γ' h hown => psi_lt_psi_of_mem (InR_Om_succ 1) (leMulWe_lt h)
      (leMulWe_mem (mxOm2_mem _ _) (CSet.of_lt hown))
  have hΘsucc : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ →
      gxTh (upsilon l) (ldAtR S l) (γ + 1) = gxTh (upsilon l) (ldAtR S l) γ + 1 := fun γ hγ => by
    rw [gxTh_add hρSC hAt hγ 1, hΘ1]
  have hcode1 : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ → γ + 1 < Om (1 + 1) →
      GxCl (upsilon l) (ldAtR S l) (γ + 1) := fun γ hγ h =>
    (ldHull_iff hl hX h).1 (CSet.succ_mem ((ldHull_iff hl hX ((lt_add_one γ).trans h)).2 hγ))
  have hrle : ∀ r γ', GxCl (upsilon l) (ldAtR S l) γ' → r / leOe (Om 1) = gxTh (upsilon l) (ldAtR S l) γ' →
      r ≤ leOe (Om 1) * gxTh (upsilon l) (ldAtR S l) (γ' + 1) := by
    intro r γ' hγ' hx
    rw [hΘsucc γ' hγ', ← hx, mul_add_one]
    exact (Ordinal.lt_mul_div_add r hO0).le
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγ hγT
  have hγW : γ < Om (1 + 1) := hγT.trans rnT1_lt_Om2
  suffices E : gxTh (upsilon l) (ldAtR S l) (S.psi (leWe (Om (1 + 1)) * γ) (Om (1 + 1))) =
      S.psi (A + 1 + leOe (Om 1) * gxTh (upsilon l) (ldAtR S l) γ) (Om 1) by
    refine ⟨E, ?_⟩
    rcases eq_or_ne γ 0 with rfl | hγ0
    · rw [gxTh_zero, mul_zero, add_zero]; exact hÂ
    refine CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ)
      (leMulOe_mem (CSet.Om_mem (CSet.one_mem _ _)) (CSet.of_lt ?_))
    rw [← E]; exact gxTh_lt hγ (rnT1_gt hγT)
  rcases zero_or_succ_or_isSuccLimit γ with h0 | ⟨γ', hγ'⟩ | hlim
  · subst h0
    rw [mul_zero, gxTh_zero, mul_zero, add_zero]; exact hbase
  · rw [succ_eq_add_one] at hγ'
    subst hγ'
    have hγ'H : γ' ∈ cdHull S l := mem_of_add_one_mem ((ldHull_iff hl hX hγW).2 hγ)
    have hγ'c : GxCl (upsilon l) (ldAtR S l) γ' := (ldHull_iff hl hX ((lt_add_one γ').trans hγW)).1 hγ'H
    have hγ'T : γ' < rnT1 S := (lt_add_one γ').trans hγT
    obtain ⟨e', own'⟩ := IH γ' (lt_add_one γ') hγ'c hγ'T
    have h := rnTopW hl hX (rnBg_base l hγ'H hγ'T) own' e'
    have eT : rnTW S (leWe (Om (1 + 1)) * γ') = S.psi (leWe (Om (1 + 1)) * (γ' + 1)) (Om (1 + 1)) := by
      unfold rnTW; rw [mul_add_one]
    rw [eT] at h
    rw [h, hΘsucc γ' hγ'c, mul_add_one, ← add_assoc]
  · have hγ0 : γ ≠ 0 := hlim.ne_bot
    have hΘ0 : 0 < gxTh (upsilon l) (ldAtR S l) γ := by
      have := gxTh_lt (Z := upsilon l) (At := ldAtR S l) (GxCl.zero hρ0) (pos_iff_ne_zero.2 hγ0)
      rwa [gxTh_zero] at this
    have hsγ := rnMuG_atom hl hX hγ hγW
    have hÂX : A + 1 ∈ S.CSet (A + 1 + leOe (Om 1) * gxTh (upsilon l) (ldAtR S l) γ)
        (S.psi (A + 1 + leOe (Om 1) * gxTh (upsilon l) (ldAtR S l) γ) (Om 1)) :=
      (psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ
    have hÂlt : S.psi (A + 1) (Om 1) < S.psi (A + 1 + leOe (Om 1) * gxTh (upsilon l) (ldAtR S l) γ) (Om 1) :=
      psi_lt_psi_of_mem Low.InR_Om_one (lt_add_of_pos_right _ (mul_pos (leOe_pos _) hΘ0)) hÂX
    have hlt1 : ∀ γ1, GxCl (upsilon l) (ldAtR S l) γ1 → γ1 < γ →
        gxTh (upsilon l) (ldAtR S l) (S.psi (leWe (Om (1 + 1)) * γ1) (Om (1 + 1))) =
          S.psi (A + 1 + leOe (Om 1) * gxTh (upsilon l) (ldAtR S l) γ1) (Om 1) ∧
        S.psi (A + 1 + leOe (Om 1) * gxTh (upsilon l) (ldAtR S l) γ1) (Om 1) <
          S.psi (A + 1 + leOe (Om 1) * gxTh (upsilon l) (ldAtR S l) γ) (Om 1) := by
      intro γ1 hγ1 h1
      obtain ⟨e1, own1⟩ := IH γ1 h1 hγ1 (h1.trans hγT)
      have hlt : A + 1 + leOe (Om 1) * gxTh (upsilon l) (ldAtR S l) γ1 <
          A + 1 + leOe (Om 1) * gxTh (upsilon l) (ldAtR S l) γ :=
        (add_lt_add_iff_left _).2 ((mul_lt_mul_iff_right₀ (leOe_pos _)).2 (gxTh_lt hγ1 h1))
      exact ⟨e1, psi_lt_psi_of_mem Low.InR_Om_one hlt ((psi_mono (S := S) Low.InR_Om_one hlt.le).2 own1)⟩
    apply le_antisymm
    · refine ldAtom_le hρSC hρ1 hAt (SC_psi Low.InR_Om_one _) (hρÂ.trans hÂlt) ?_
      intro t ht hts
      obtain ⟨a, haH, -, rfl⟩ := ht
      have haγ : a < leWe (Om (1 + 1)) * γ := by
        by_contra h
        push Not at h
        exact absurd hts (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) h).1)
      obtain ⟨hgW, hlo, hhi⟩ := leSplitE hμ0 (dvd_zero _) zero_le
        (by rw [zero_add]; exact haγ.trans (leMulWe_lt hγW))
      rw [zero_add] at hlo hhi
      have hgγ : a % (leWe (Om (1 + 1)) * Om (1 + 1)) / leWe (Om (1 + 1)) < γ := by
        by_contra h
        push Not at h
        exact absurd ((leMulWe_mono h).trans hlo) (not_le.2 haγ)
      have hgH : a % (leWe (Om (1 + 1)) * Om (1 + 1)) / leWe (Om (1 + 1)) ∈ cdHull S l := by
        have h1 : a % (leWe (Om (1 + 1)) * Om (1 + 1)) ∈ cdHull S l := by
          rw [← leWe_succ]; exact leModP_mem _ haH
        have h2 : a % (leWe (Om (1 + 1)) * Om (1 + 1)) < ω ^ (Om (1 + 1) * Om (1 + 1) + Om (1 + 1)) := by
          rw [← rnMuW_eq]; exact Ordinal.mod_lt _ (mul_ne_zero hμ0 ldOm2_SC.1.ne')
        exact leDivOp_mem (dvd_mul_right _ _) h1 h2
      have hgc := (ldHull_iff hl hX hgW).1 hgH
      have hg1γ := hlim.succ_lt hgγ
      have hg1c := hcode1 _ hgc (hg1γ.trans hγW)
      obtain ⟨e1, hlt⟩ := hlt1 _ hg1c hg1γ
      refine lt_of_le_of_lt (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1) hhi.le).1) ?_
      rw [e1]; exact hlt
    · obtain ⟨hTSC, -, hTs⟩ := ldAtom_ge hρSC hρ1 hAt hsγ
      refine ldPsi1_le hTSC fun x hx _ => ?_
      have hβs : S.psi 0 (Om (1 + 1)) < S.psi (leWe (Om (1 + 1)) * γ) (Om (1 + 1)) := by
        have := hslt 0 γ (pos_iff_ne_zero.2 hγ0) ((pos_iff_ne_zero.2 hγ0).trans (rnT1_gt hγT))
        rwa [mul_zero] at this
      rcases le_or_gt x (A + 1) with hxÂ | hxÂ
      · refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one hxÂ).1 ?_
        rw [← hbase]; exact hTs _ hβat hβs
      obtain ⟨r, rfl⟩ := exists_add_of_le hxÂ.le
      have hr : r < leOe (Om 1) * gxTh (upsilon l) (ldAtR S l) γ := (add_lt_add_iff_left _).1 hx
      have hx' : r / leOe (Om 1) < gxTh (upsilon l) (ldAtR S l) γ := (Ordinal.lt_mul_iff_div_lt hO0).1 hr
      obtain ⟨γ', hγ'c, hγ'γ, hγ'x⟩ := gxTh_onto hx'
      have hγ'1 := hlim.succ_lt hγ'γ
      have hγ'1c := hcode1 _ hγ'c (hγ'1.trans hγW)
      obtain ⟨e1, -⟩ := hlt1 _ hγ'1c hγ'1
      refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one
        ((add_le_add_iff_left _).2 (hrle r γ' hγ'c hγ'x.symm))).1 ?_
      rw [← e1]
      exact hTs _ (rnMuG_atom hl hX hγ'1c (hγ'1.trans hγW))
        (hslt _ γ hγ'1 (hγ'1.trans (rnT1_gt hγT)))

end Googology.Trans.PoR.InaccPsi.R2.Rn

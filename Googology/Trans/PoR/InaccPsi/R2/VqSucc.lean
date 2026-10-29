import Googology.Trans.PoR.InaccPsi.R2.VqSh

/-!
# The top `RvTop X e ⇒ RvTop X (e + 1)` for a base-relative shift

The proofs of `Vk.vkE_data`, `Vk.vkBaseE_sub`, `Vk.vkStepA`, `Vk.vkTopSucc` run with `Vq.VqSh` in place of
`Vk.VkSh`: their uses of the self-relative field `X ∈ Cl(X, ·)` are at closures `Cl(β + W^{X+e}, ·)` with `β ≥ b`,
so the base-relative field `X ∈ Cl(b + W^X, ·)` suffices (`Rv.rvWX_le`); their uses of `X̂ ∈ Cl(X̂, ·)` are at
`Cl(Â + Ω^{X̂+·}·x, ·)` with `Â` a base image, and every base image is `≥ A` (`Vq.vqHatA`), so the field
`X̂ ∈ Cl(A + Ω^{X̂}, ·)` suffices.

* `vqE_data`, `vqBaseE_sub`, `vqStepA`, `vqTopSucc` (**`RvTop λ b X X̂ e ⇒ RvTop λ b X X̂ (e+1)` for a code `e`**).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Vq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rq
  Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj
  Googology.Trans.PoR.InaccPsi.R2.Vk

variable {S : InaccSeq.{0}}

section Sh

variable {l A b X Xh : Ordinal.{0}} (hs : VqSh S l A b X Xh)

include hs

/-- **The exponent `X + e` of an own code `e`** is own in the closure sense and a code above the level 2 over every
`Q > K_1`. -/
theorem vqE_data {β e : Ordinal.{0}} (hbβ : b ≤ β) (he : e < S.psi (β + leWe (X + e)) (Om (1 + 1))) :
    X + e ∈ S.CSet (β + leWe (X + e)) (S.psi (β + leWe (X + e)) (Om (1 + 1))) ∧
      ∀ Q, SC Q → leKe S (X + e) β 1 < Q → VkA (1 + 1) Q (X + e) := by
  refine ⟨CSet.add_mem (vqMem hs (rvWX_le hbβ X e) (rvWX_le hbβ X e) le_rfl) (CSet.of_lt he), fun Q hQ h1 => ?_⟩
  refine VkA.add (vqCl hs hQ (x := β + leWe (X + e) * Om 1) ?_ h1.le) (VkA.small ?_)
  · exact rvWX_le_mul hbβ X e _ (Om_pos one_ne_zero).ne'
  refine (he.trans_le ?_).trans h1
  refine (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 ?_)).1
  calc leWe (X + e) = leWe (X + e) * 1 := (mul_one _).symm
    _ ≤ leWe (X + e) * Om 1 := leMulWe_mono (one_lt_omega0.trans (Lw.lw_omega_lt_SC Ph.ph_SC_Om1)).le

/-- **`β + W^{X+e}·γ` is a base of exponent `e`** for every code `γ < T_{X+e+1}(β)`. -/
theorem vqBaseE_sub {ηx e β γ : Ordinal.{0}} (hbβ : b ≤ β) (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hb : RoBaseE S l X (e + 1) β) (hec : GxCl (upsilon l) (ldAtR S l) e)
    (hγH : γ ∈ cdHull S l) (hγ : γ < leTe S (X + e + 1) β) : RoBaseE S l X e (β + leWe (X + e) * γ) := by
  obtain ⟨hβd, hβA, hβown⟩ := roBase_succ hb
  obtain ⟨-, hβH, -, -, hexpA⟩ := hb
  have hexp : e < S.psi (β + leWe (X + e)) (Om (1 + 1)) := hexpA e hec (lt_add_one e).le
  obtain ⟨hEC, hEL⟩ := vqE_data hs hbβ hexp
  have heW : e < Om (1 + 1) := hexp.trans (psi_lt (InR_Om_succ 1) _)
  have heH : e ∈ cdHull S l := (ldHull_iff hl hX heW).2 hec
  have hγW : γ < Om (1 + 1) := hγ.trans (leTe_lt_Om2 _ _)
  have hγ1W : γ + 1 < Om (1 + 1) := ldOm2_SC.isSuccLimit.succ_lt hγW
  have hγs := vkTe_gt hβown hEC hβd hEL hγ
  refine ⟨?_, CSet.add_mem hβH (leMulWe_mem (CSet.add_mem hs.hull heH) hγH), ?_, fun d hd => ?_,
    fun e' he' h' => ?_⟩
  · obtain ⟨q, rfl⟩ := hβd
    rw [leWe_succ, mul_assoc, ← mul_add]
    exact dvd_mul_right _ _
  · rw [add_assoc, ← mul_add_one]
    refine lt_of_le_of_lt ?_ hβA
    rw [leWe_succ]
    exact (add_le_add_iff_left β).2 (leMulWe_mono hγ1W.le)
  · have hd' : leWe (X + e) * γ + d ≤ leWe (X + e + 1) := by
      rw [leWe_succ]
      calc leWe (X + e) * γ + d ≤ leWe (X + e) * γ + leWe (X + e) := (add_le_add_iff_left _).2 hd
        _ = leWe (X + e) * (γ + 1) := (mul_add_one _ _).symm
        _ ≤ leWe (X + e) * Om (1 + 1) := leMulWe_mono hγ1W.le
    rw [add_assoc]
    rcases eq_or_ne γ 0 with rfl | hγ0
    · rw [mul_zero, zero_add, add_zero]
      rw [mul_zero, zero_add] at hd'
      exact hβown d hd'
    refine CSet.add_mem (hβown _ hd') (leMulWe_mem (roEC_mono hEC ?_) (CSet.of_lt ?_))
    · calc leWe (X + e) = leWe (X + e) * 1 := (mul_one _).symm
        _ ≤ leWe (X + e) * γ := leMulWe_mono (Order.one_le_iff_ne_zero.2 hγ0)
        _ ≤ leWe (X + e) * γ + d := le_self_add
    · exact hγs.trans_le (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 le_self_add)).1
  · refine (hexpA e' he' (h'.trans (lt_add_one e).le)).trans_le ?_
    refine (psi_mono (S := S) (InR_Om_succ 1) ?_).1
    rw [add_assoc]; exact (add_le_add_iff_left β).2 le_add_self

section Main

variable {ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hAo : A ∈ S.CSet A (S.psi A (Om 1))) (hρo : S.psi A (Om 1) = upsilon l)

include hl hX hAo hρo

/-- **The sub-bases of a block of exponent `X + e + 1`**, given the tops of exponent `X + e`. -/
theorem vqStepA {e : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (hT : RvTop S l b X Xh e)
    {β Â : Ordinal.{0}} (hb : RoBaseE S l X (e + 1) β) (hbβ : b ≤ β) (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1)))
    (hbase : gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1)) :
    ∀ γ, GxCl (upsilon l) (ldAtR S l) γ → γ < leTe S (X + e + 1) β →
      gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe (X + e) * γ) (Om (1 + 1))) =
        S.psi (Â + leOe (Xh + gxTh (upsilon l) (ldAtR S l) e) * gxTh (upsilon l) (ldAtR S l) γ) (Om 1) ∧
      Â + leOe (Xh + gxTh (upsilon l) (ldAtR S l) e) * gxTh (upsilon l) (ldAtR S l) γ ∈
        S.CSet (Â + leOe (Xh + gxTh (upsilon l) (ldAtR S l) e) * gxTh (upsilon l) (ldAtR S l) γ)
          (S.psi (Â + leOe (Xh + gxTh (upsilon l) (ldAtR S l) e) * gxTh (upsilon l) (ldAtR S l) γ) (Om 1)) := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAÂ : A ≤ Â := vqHatA hAo hρo hÂ hbase
  have hρ0 : 0 < upsilon l := hρSC.1
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small (gg_one_lt_of_SC hρSC).le
  have hb' := hb
  obtain ⟨hβd, hβA, hβown⟩ := roBase_succ hb
  obtain ⟨-, hβH, -, -, hexpA⟩ := hb
  have hexp : e < S.psi (β + leWe (X + e)) (Om (1 + 1)) := hexpA e hec (lt_add_one e).le
  obtain ⟨hEC, hEL⟩ := vqE_data hs hbβ hexp
  have hμ0 : leWe (X + e) ≠ 0 := (leWe_pos _).ne'
  set O := leOe (Xh + gxTh (upsilon l) (ldAtR S l) e) with hO_def
  have hO0 : O ≠ 0 := (leOe_pos _).ne'
  have hβd' : leWe (X + e) * Om (1 + 1) ∣ β := by rw [← leWe_succ]; exact hβd
  have hβA' : β + leWe (X + e) * Om (1 + 1) < ConjT.Aη S (cdEta S l) := by rw [← leWe_succ]; exact hβA
  have heH : e ∈ cdHull S l := (ldHull_iff hl hX (hexp.trans (psi_lt (InR_Om_succ 1) _))).2 hec
  have hXeH : X + e ∈ cdHull S l := CSet.add_mem hs.hull heH
  have hsub : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ → γ < leTe S (X + e + 1) β →
      RoBaseE S l X e (β + leWe (X + e) * γ) := fun γ hγ hγT =>
    vqBaseE_sub hs hbβ hl hX hb' hec ((ldHull_iff hl hX (hγT.trans (leTe_lt_Om2 _ _))).2 hγ) hγT
  have hγs : ∀ γ, γ < leTe S (X + e + 1) β → γ < S.psi (β + leWe (X + e) * γ) (Om (1 + 1)) :=
    fun γ h => vkTe_gt hβown hEC hβd hEL h
  have hβat : S.psi β (Om (1 + 1)) ∈ ldAtR S l := ⟨β, hβH, le_self_add.trans_lt hβA, rfl⟩
  have hρÂ : upsilon l < S.psi Â (Om 1) := by
    rw [← hbase]; exact (ldAtom_ge hρSC hρ1 hAt hβat).2.1
  have hsat : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ → γ < Om (1 + 1) →
      S.psi (β + leWe (X + e) * γ) (Om (1 + 1)) ∈ ldAtR S l := by
    intro γ hγ hγW
    refine ⟨β + leWe (X + e) * γ, CSet.add_mem hβH (leMulWe_mem hXeH ((ldHull_iff hl hX hγW).2 hγ)), ?_, rfl⟩
    exact ((add_lt_add_iff_left β).2 (leMulWe_lt hγW)).trans hβA'
  have hslt : ∀ γ γ', γ < γ' → γ' ≤ Om (1 + 1) → 0 < γ' →
      γ < S.psi (β + leWe (X + e) * γ') (Om (1 + 1)) →
      S.psi (β + leWe (X + e) * γ) (Om (1 + 1)) < S.psi (β + leWe (X + e) * γ') (Om (1 + 1)) := by
    intro γ γ' h hγ'W hγ'0 hown
    refine psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left β).2 (leMulWe_lt h)) ?_
    refine CSet.add_mem (hβown _ ?_) (leMulWe_mem (roEC_mono hEC ?_) (CSet.of_lt hown))
    · rw [leWe_succ]; exact leMulWe_mono hγ'W
    · calc leWe (X + e) = leWe (X + e) * 1 := (mul_one _).symm
        _ ≤ leWe (X + e) * γ' := leMulWe_mono (Order.one_le_iff_pos.2 hγ'0)
  have hΘsucc : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ →
      gxTh (upsilon l) (ldAtR S l) (γ + 1) = gxTh (upsilon l) (ldAtR S l) γ + 1 := fun γ hγ => by
    rw [gxTh_add hρSC hAt hγ 1, hΘ1]
  have hrle : ∀ r γ', GxCl (upsilon l) (ldAtR S l) γ' → r / O = gxTh (upsilon l) (ldAtR S l) γ' →
      r ≤ O * gxTh (upsilon l) (ldAtR S l) (γ' + 1) := by
    intro r γ' hγ' hx
    rw [hΘsucc γ' hγ', ← hx, mul_add_one]
    exact (Ordinal.lt_mul_div_add r hO0).le
  have hcode1 : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ → γ + 1 < Om (1 + 1) →
      GxCl (upsilon l) (ldAtR S l) (γ + 1) := fun γ hγ h =>
    (ldHull_iff hl hX h).1 (CSet.succ_mem ((ldHull_iff hl hX ((lt_add_one γ).trans h)).2 hγ))
  have hΘeX : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ → γ < leTe S (X + e + 1) β → 0 < γ →
      gxTh (upsilon l) (ldAtR S l) e <
        gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe (X + e) * γ) (Om (1 + 1))) := by
    intro γ hγ hγT hγ0
    refine gxTh_lt hec (hexp.trans_le (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 ?_)).1)
    calc leWe (X + e) = leWe (X + e) * 1 := (mul_one _).symm
      _ ≤ leWe (X + e) * γ := leMulWe_mono (Order.one_le_iff_pos.2 hγ0)
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγ hγT
  have hγW : γ < Om (1 + 1) := hγT.trans (leTe_lt_Om2 _ _)
  suffices E : gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe (X + e) * γ) (Om (1 + 1))) =
      S.psi (Â + O * gxTh (upsilon l) (ldAtR S l) γ) (Om 1) by
    refine ⟨E, ?_⟩
    rcases eq_or_ne γ 0 with rfl | hγ0
    · rw [gxTh_zero, mul_zero, add_zero]; exact hÂ
    have hΘγ0 : gxTh (upsilon l) (ldAtR S l) γ ≠ 0 := by
      have := gxTh_lt (Z := upsilon l) (At := ldAtR S l) (GxCl.zero hρ0) (pos_iff_ne_zero.2 hγ0)
      rw [gxTh_zero] at this; exact this.ne'
    refine Rv.rvHat_own hÂ (vqMemh hs (vqA_le hAÂ Xh _ hΘγ0) (rvWX_le_mul hbβ X e γ hγ0) E.le) ?_ ?_
    · rw [← E]; exact hΘeX γ hγ hγT (pos_iff_ne_zero.2 hγ0)
    · rw [← E]; exact gxTh_lt hγ (hγs γ hγT)
  rcases zero_or_succ_or_isSuccLimit γ with h0 | ⟨γ', hγ'⟩ | hlim
  · subst h0
    rw [mul_zero, add_zero, gxTh_zero, mul_zero, add_zero]; exact hbase
  · rw [succ_eq_add_one] at hγ'
    subst hγ'
    have hγ'c : GxCl (upsilon l) (ldAtR S l) γ' :=
      (ldHull_iff hl hX ((lt_add_one γ').trans hγW)).1 (mem_of_add_one_mem ((ldHull_iff hl hX hγW).2 hγ))
    have hγ'T : γ' < leTe S (X + e + 1) β := (lt_add_one γ').trans hγT
    obtain ⟨e', own'⟩ := IH γ' (lt_add_one γ') hγ'c hγ'T
    have h := hT (β + leWe (X + e) * γ') _ (hsub γ' hγ'c hγ'T) (hbβ.trans le_self_add) own' e'
    have eT : leTe S (X + e) (β + leWe (X + e) * γ') = S.psi (β + leWe (X + e) * (γ' + 1)) (Om (1 + 1)) := by
      unfold leTe; rw [add_assoc, ← mul_add_one]
    rw [eT, add_assoc, ← mul_add_one] at h
    rw [h, hΘsucc γ' hγ'c]
  · have hγ0 : γ ≠ 0 := hlim.ne_bot
    have hΘ0 : 0 < gxTh (upsilon l) (ldAtR S l) γ := by
      have := gxTh_lt (Z := upsilon l) (At := ldAtR S l) (GxCl.zero hρ0) (pos_iff_ne_zero.2 hγ0)
      rwa [gxTh_zero] at this
    have hsγ := hsat γ hγ hγW
    set Y := S.psi (Â + O * gxTh (upsilon l) (ldAtR S l) γ) (Om 1) with hY_def
    have hÂY : Â ∈ S.CSet (Â + O * gxTh (upsilon l) (ldAtR S l) γ) Y :=
      (psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ
    have hÂlt : S.psi Â (Om 1) < Y :=
      psi_lt_psi_of_mem Low.InR_Om_one (lt_add_of_pos_right Â (mul_pos (leOe_pos _) hΘ0)) hÂY
    have hlt1 : ∀ γ1, GxCl (upsilon l) (ldAtR S l) γ1 → γ1 < γ →
        gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe (X + e) * γ1) (Om (1 + 1))) =
          S.psi (Â + O * gxTh (upsilon l) (ldAtR S l) γ1) (Om 1) ∧
        S.psi (Â + O * gxTh (upsilon l) (ldAtR S l) γ1) (Om 1) < Y := by
      intro γ1 hγ1 h1
      obtain ⟨e1, own1⟩ := IH γ1 h1 hγ1 (h1.trans hγT)
      have hlt : Â + O * gxTh (upsilon l) (ldAtR S l) γ1 < Â + O * gxTh (upsilon l) (ldAtR S l) γ :=
        (add_lt_add_iff_left Â).2 ((mul_lt_mul_iff_right₀ (leOe_pos _)).2 (gxTh_lt hγ1 h1))
      exact ⟨e1, psi_lt_psi_of_mem Low.InR_Om_one hlt ((psi_mono (S := S) Low.InR_Om_one hlt.le).2 own1)⟩
    apply le_antisymm
    · refine ldAtom_le hρSC hρ1 hAt (SC_psi Low.InR_Om_one _) (hρÂ.trans hÂlt) ?_
      intro t ht hts
      obtain ⟨a, haH, -, rfl⟩ := ht
      rcases lt_or_ge a β with haβ | haβ
      · exact (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1) haβ.le).1).trans_lt (by rw [hbase]; exact hÂlt)
      have haγ : a < β + leWe (X + e) * γ := by
        by_contra h
        push Not at h
        exact absurd hts (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) h).1)
      obtain ⟨hgW, hlo, hhi⟩ := leSplitE hμ0 hβd' haβ (haγ.trans ((add_lt_add_iff_left β).2 (leMulWe_lt hγW)))
      have hgγ : a % (leWe (X + e) * Om (1 + 1)) / leWe (X + e) < γ := by
        by_contra h
        push Not at h
        exact absurd (((add_le_add_iff_left β).2 (leMulWe_mono h)).trans hlo) (not_le.2 haγ)
      have hgH : a % (leWe (X + e) * Om (1 + 1)) / leWe (X + e) ∈ cdHull S l := by
        have h1 : a % (leWe (X + e) * Om (1 + 1)) ∈ cdHull S l := by
          rw [← leWe_succ]; exact leModP_mem _ haH
        have h2 : a % (leWe (X + e) * Om (1 + 1)) < ω ^ (Om (1 + 1) * (X + e) + Om (1 + 1)) := by
          have : leWe (X + e) * Om (1 + 1) = ω ^ (Om (1 + 1) * (X + e) + Om (1 + 1)) := by
            rw [← leWe_succ]; unfold leWe; rw [mul_add_one]
          rw [← this]; exact Ordinal.mod_lt _ (mul_ne_zero hμ0 ldOm2_SC.1.ne')
        exact leDivOp_mem (dvd_mul_right _ _) h1 h2
      have hgc := (ldHull_iff hl hX hgW).1 hgH
      have hg1γ := hlim.succ_lt hgγ
      have hg1c := hcode1 _ hgc (hg1γ.trans hγW)
      obtain ⟨e1, hlt⟩ := hlt1 _ hg1c hg1γ
      refine lt_of_le_of_lt (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1) hhi.le).1) ?_
      rw [e1]; exact hlt
    · obtain ⟨hTSC, -, hTs⟩ := ldAtom_ge hρSC hρ1 hAt hsγ
      refine ldPsi1_le hTSC fun x hx _ => ?_
      have hβs : S.psi β (Om (1 + 1)) < S.psi (β + leWe (X + e) * γ) (Om (1 + 1)) := by
        have := hslt 0 γ (pos_iff_ne_zero.2 hγ0) hγW.le (pos_iff_ne_zero.2 hγ0)
          ((pos_iff_ne_zero.2 hγ0).trans (hγs γ hγT))
        rwa [mul_zero, add_zero] at this
      rcases le_or_gt x Â with hxÂ | hxÂ
      · refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one hxÂ).1 ?_
        rw [← hbase]; exact hTs _ hβat hβs
      obtain ⟨r, rfl⟩ := exists_add_of_le hxÂ.le
      have hr : r < O * gxTh (upsilon l) (ldAtR S l) γ := (add_lt_add_iff_left Â).1 hx
      have hx' : r / O < gxTh (upsilon l) (ldAtR S l) γ := (Ordinal.lt_mul_iff_div_lt hO0).1 hr
      obtain ⟨γ', hγ'c, hγ'γ, hγ'x⟩ := gxTh_onto hx'
      have hγ'1 := hlim.succ_lt hγ'γ
      have hγ'1c := hcode1 _ hγ'c (hγ'1.trans hγW)
      obtain ⟨e1, -⟩ := hlt1 _ hγ'1c hγ'1
      refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one
        ((add_le_add_iff_left Â).2 (hrle r γ' hγ'c hγ'x.symm))).1 ?_
      rw [← e1]
      exact hTs _ (hsat _ hγ'1c (hγ'1.trans hγW)) (hslt _ γ hγ'1 hγW.le (pos_iff_ne_zero.2 hγ0)
        (hγ'1.trans (hγs γ hγT)))

/-- **The top of a block of exponent `X + e + 1`**: `RvTop X e ⇒ RvTop X (e + 1)`. -/
theorem vqTopSucc {e : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (hT : RvTop S l b X Xh e) :
    RvTop S l b X Xh (e + 1) := by
  intro β Â hb hbβ hÂ hbase
  rw [← add_assoc]
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small (gg_one_lt_of_SC hρSC).le
  have hA := vqStepA hs hl hX hAo hρo hec hT hb hbβ hÂ hbase
  obtain ⟨hβd, hβA, hβown⟩ := roBase_succ hb
  obtain ⟨-, hβH, -, -, hexpA⟩ := hb
  have hexp : e < S.psi (β + leWe (X + e)) (Om (1 + 1)) := hexpA e hec (lt_add_one e).le
  obtain ⟨hEC, hEL⟩ := vqE_data hs hbβ hexp
  have hμ0 : leWe (X + e) ≠ 0 := (leWe_pos _).ne'
  set O := leOe (Xh + gxTh (upsilon l) (ldAtR S l) e) with hO_def
  have hO0 : O ≠ 0 := (leOe_pos _).ne'
  have hβd' : leWe (X + e) * Om (1 + 1) ∣ β := by rw [← leWe_succ]; exact hβd
  have heH : e ∈ cdHull S l := (ldHull_iff hl hX (hexp.trans (psi_lt (InR_Om_succ 1) _))).2 hec
  have hXeH : X + e ∈ cdHull S l := CSet.add_mem hs.hull heH
  have hβat : S.psi β (Om (1 + 1)) ∈ ldAtR S l := ⟨β, hβH, le_self_add.trans_lt hβA, rfl⟩
  have hρÂ : upsilon l < S.psi Â (Om 1) := by
    rw [← hbase]; exact (ldAtom_ge hρSC hρ1 hAt hβat).2.1
  have hΘsucc : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ →
      gxTh (upsilon l) (ldAtR S l) (γ + 1) = gxTh (upsilon l) (ldAtR S l) γ + 1 := fun γ hγ => by
    rw [gxTh_add hρSC hAt hγ 1, hΘ1]
  have hcode1 : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ → γ + 1 < Om (1 + 1) →
      GxCl (upsilon l) (ldAtR S l) (γ + 1) := fun γ hγ h =>
    (ldHull_iff hl hX h).1 (CSet.succ_mem ((ldHull_iff hl hX ((lt_add_one γ).trans h)).2 hγ))
  have hrle : ∀ r γ', GxCl (upsilon l) (ldAtR S l) γ' → r / O = gxTh (upsilon l) (ldAtR S l) γ' →
      r ≤ O * gxTh (upsilon l) (ldAtR S l) (γ' + 1) := by
    intro r γ' hγ' hx
    rw [hΘsucc γ' hγ', ← hx, mul_add_one]
    exact (Ordinal.lt_mul_div_add r hO0).le
  have hTW : leTe S (X + e + 1) β = S.psi (β + leWe (X + e) * Om (1 + 1)) (Om (1 + 1)) := leTe_succ (X + e) β
  have hγs : ∀ γ, γ < leTe S (X + e + 1) β → γ < S.psi (β + leWe (X + e) * γ) (Om (1 + 1)) :=
    fun γ h => vkTe_gt hβown hEC hβd hEL h
  have htat : leTe S (X + e + 1) β ∈ ldAtR S l :=
    ⟨β + leWe (X + e + 1), CSet.add_mem hβH (leWe_mem (CSet.succ_mem hXeH)), hβA, rfl⟩
  rw [hΘsucc e hec, ← add_assoc, leOe_succ]
  set Y := S.psi (Â + O * Om 1) (Om 1) with hY_def
  have hÂY : Â ∈ S.CSet (Â + O * Om 1) Y := (psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ
  have hÂlt : S.psi Â (Om 1) < Y :=
    psi_lt_psi_of_mem Low.InR_Om_one (lt_add_of_pos_right Â (mul_pos (leOe_pos _) (Om_pos one_ne_zero))) hÂY
  have hsubY : ∀ g, GxCl (upsilon l) (ldAtR S l) g → g < leTe S (X + e + 1) β →
      S.psi (Â + O * gxTh (upsilon l) (ldAtR S l) g) (Om 1) < Y := by
    intro g hg hgT
    obtain ⟨e1, own1⟩ := hA g hg hgT
    have hΘ1' : gxTh (upsilon l) (ldAtR S l) g < Om 1 := by
      refine (gxTh_lt hg (hγs g hgT)).trans ?_
      rw [e1]; exact psi_lt Low.InR_Om_one _
    have hlt : Â + O * gxTh (upsilon l) (ldAtR S l) g < Â + O * Om 1 :=
      (add_lt_add_iff_left Â).2 ((mul_lt_mul_iff_right₀ (leOe_pos _)).2 hΘ1')
    exact psi_lt_psi_of_mem Low.InR_Om_one hlt ((psi_mono (S := S) Low.InR_Om_one hlt.le).2 own1)
  have hsubT : ∀ g, g < leTe S (X + e + 1) β →
      S.psi (β + leWe (X + e) * g) (Om (1 + 1)) < leTe S (X + e + 1) β := by
    intro g hgT
    rw [hTW]
    refine psi_lt_psi_of_mem (InR_Om_succ 1)
      ((add_lt_add_iff_left β).2 (leMulWe_lt (hgT.trans (leTe_lt_Om2 _ _)))) ?_
    refine CSet.add_mem (hβown _ ?_) (leMulWe_mem (roEC_mono hEC ?_) (CSet.of_lt (by rw [← hTW]; exact hgT)))
    · rw [leWe_succ]
    · calc leWe (X + e) = leWe (X + e) * 1 := (mul_one _).symm
        _ ≤ leWe (X + e) * Om (1 + 1) := leMulWe_mono (one_lt_omega0.trans (Lw.lw_omega_lt_SC ldOm2_SC)).le
  have hsat : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ → γ < Om (1 + 1) →
      S.psi (β + leWe (X + e) * γ) (Om (1 + 1)) ∈ ldAtR S l := by
    intro γ hγ hγW
    refine ⟨β + leWe (X + e) * γ, CSet.add_mem hβH (leMulWe_mem hXeH ((ldHull_iff hl hX hγW).2 hγ)), ?_, rfl⟩
    refine lt_of_lt_of_le ((add_lt_add_iff_left β).2 (leMulWe_lt hγW)) ?_
    rw [← leWe_succ]; exact hβA.le
  have hup : gxTh (upsilon l) (ldAtR S l) (leTe S (X + e + 1) β) ≤ Y := by
    refine ldAtom_le hρSC hρ1 hAt (SC_psi Low.InR_Om_one _) (hρÂ.trans hÂlt) ?_
    intro t ht hts
    obtain ⟨a, haH, -, rfl⟩ := ht
    rcases lt_or_ge a β with haβ | haβ
    · exact (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1) haβ.le).1).trans_lt (by rw [hbase]; exact hÂlt)
    have ha2 : a < β + leWe (X + e) * Om (1 + 1) := by
      by_contra h
      push Not at h
      rw [hTW] at hts
      exact absurd hts (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) h).1)
    obtain ⟨hgW, hlo, hhi⟩ := leSplitE hμ0 hβd' haβ ha2
    have hgH : a % (leWe (X + e) * Om (1 + 1)) / leWe (X + e) ∈ cdHull S l := by
      have h1 : a % (leWe (X + e) * Om (1 + 1)) ∈ cdHull S l := by
        rw [← leWe_succ]; exact leModP_mem _ haH
      have h2 : a % (leWe (X + e) * Om (1 + 1)) < ω ^ (Om (1 + 1) * (X + e) + Om (1 + 1)) := by
        have : leWe (X + e) * Om (1 + 1) = ω ^ (Om (1 + 1) * (X + e) + Om (1 + 1)) := by
          rw [← leWe_succ]; unfold leWe; rw [mul_add_one]
        rw [← this]; exact Ordinal.mod_lt _ (mul_ne_zero hμ0 ldOm2_SC.1.ne')
      exact leDivOp_mem (dvd_mul_right _ _) h1 h2
    have hgc := (ldHull_iff hl hX hgW).1 hgH
    have hgT : a % (leWe (X + e) * Om (1 + 1)) / leWe (X + e) < leTe S (X + e + 1) β := by
      by_contra h
      push Not at h
      have h1 := vkTe_ge hβown hEC hβd hEL h
      exact absurd (h1.trans (psi_mono (S := S) (InR_Om_succ 1) hlo).1) (not_le.2 hts)
    have hg1T := (leTe_SC (S := S) (X + e + 1) β).isSuccLimit.succ_lt hgT
    have hg1c := hcode1 _ hgc (hg1T.trans (leTe_lt_Om2 _ _))
    refine lt_of_le_of_lt (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1) hhi.le).1) ?_
    rw [(hA _ hg1c hg1T).1]; exact hsubY _ hg1c hg1T
  apply le_antisymm hup
  obtain ⟨hTSC, -, hTs⟩ := ldAtom_ge hρSC hρ1 hAt htat
  have hT1 : gxTh (upsilon l) (ldAtR S l) (leTe S (X + e + 1) β) < Om 1 :=
    hup.trans_lt (psi_lt Low.InR_Om_one _)
  have heT : e < leTe S (X + e + 1) β :=
    hexp.trans_le (psi_mono (S := S) (InR_Om_succ 1)
      ((add_le_add_iff_left β).2 (leWe_mono (lt_add_one (X + e)).le))).1
  have hΘeT := gxTh_lt hec heT
  refine vkPsi1_le hTSC fun x hx hc => ?_
  have hβs : S.psi β (Om (1 + 1)) < leTe S (X + e + 1) β := by
    unfold leTe
    exact psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right β (leWe_pos _)) (hβown _ le_rfl)
  rcases le_or_gt x Â with hxÂ | hxÂ
  · refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one hxÂ).1 ?_
    rw [← hbase]; exact hTs _ hβat hβs
  obtain ⟨r, rfl⟩ := exists_add_of_le hxÂ.le
  have hr : r < O * Om 1 := (add_lt_add_iff_left Â).1 hx
  set y := Xh + gxTh (upsilon l) (ldAtR S l) e with hy_def
  have eP : O * Om 1 = leOe (y + 1) := (leOe_succ _).symm
  have eP2 : leOe (y + 1) = ω ^ (Om 1 * y + Om 1) := by unfold leOe; rw [mul_add_one]
  have hc2 := vkA_mod hTSC (Om 1 * (y + 1)) hc
  change VkA 1 _ ((Â + r) % leOe (y + 1)) at hc2
  rw [eP] at hr
  have hmod : (Â + r) % leOe (y + 1) = Â % leOe (y + 1) + r := leMod_add_lt _ Â hr
  rw [hmod] at hc2
  have hlt' : Â % leOe (y + 1) + r < ω ^ (Om 1 * y + Om 1) := by
    rw [← eP2]; exact isPrincipal_add_omega0_opow _ (Ordinal.mod_lt Â (leOe_pos _).ne') hr
  have hyC : VkA 1 (gxTh (upsilon l) (ldAtR S l) (leTe S (X + e + 1) β)) y :=
    VkA.add (vqClh hs hTSC (x := β + leWe (X + e + 1)) (by rw [add_assoc]; exact rvWX_le hbβ X (e + 1)) le_rfl)
      (VkA.small hΘeT)
  have hbnd := vkA_boundY hTSC one_ne_zero hyC _ hc2 hlt'
  change _ < O * _ at hbnd
  have hrT : r < O * gxTh (upsilon l) (ldAtR S l) (leTe S (X + e + 1) β) := le_add_self.trans_lt hbnd
  have hx' := (Ordinal.lt_mul_iff_div_lt hO0).1 hrT
  obtain ⟨γ', hγ'c, hγ'T, hγ'x⟩ := gxTh_onto hx'
  have hγ'1T := (leTe_SC (S := S) (X + e + 1) β).isSuccLimit.succ_lt hγ'T
  have hγ'1c := hcode1 _ hγ'c (hγ'1T.trans (leTe_lt_Om2 _ _))
  refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one
    ((add_le_add_iff_left Â).2 (hrle r γ' hγ'c hγ'x.symm))).1 ?_
  rw [← (hA _ hγ'1c hγ'1T).1]
  exact hTs _ (hsat _ hγ'1c (hγ'1T.trans (leTe_lt_Om2 _ _))) (hsubT _ hγ'1T)

end Main

end Sh

end Googology.Trans.PoR.InaccPsi.R2.Vq

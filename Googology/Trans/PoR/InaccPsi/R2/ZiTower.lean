import Googology.Trans.PoR.InaccPsi.R2.ZiStep

/-!
# THE TOWER OF PLATEAU SHIFTS `Y₃ + Ω₂·Ω₂·η`, `η < ψ_{Ω₁}(Ω₃ + 1)`, AND THE ψ₃-OFFSETS BELOW `W^{Y₃+Ω₂·Ω₂·K₃}`

`P_η = ziPP S η = Y₃ + (Ω₂·Ω₂)·η`, `P̂_η = ziPPt S η = Y₂ + (Ω₁·Ω₁)·η`, `K₃ = Zi.ziK3 S = ψ_{Ω₁}(Ω₃ + 1)`; `W^x`, `B_n`,
"window", `A'`, `Yj.YjBase`, "IH(s)", `Zd.ZdRS`, `Zd.ZdBot` as in `Zd.zdBot_chain`.

* `ziRS_tow` (**every `(P_η, P̂_η)`, `η < K₃`, IS A FIXED RELATIVE SHIFT**: `0` is `Zd.zdRS_Y3`, successors by
  `Zi.ziRSPlat` (`P_{η+1} = P_η + Ω₂·Ω₂`), limits by `Vq.vqTopLimSh` over the smaller ones),
* `ziBot_tow` (**`Zd.ZdBot` at every `P_η`, `η ≤ K₃`**: successors by `Zi.ziBotPlat`, limits by continuity),
* `ziPsi3OffWK` (**every atom `ψ₂(a) ≤ s < ψ₂(a + W^{Y₃+Ω₂·Ω₂·K₃})` moves** over every base with a law at both ends,
  `Ω₃ ∣ a`, `Ω₃ ∣ B_n a`, under IH(s); contains `Zi.ziPsi3OffW2`).

No new axiom.  New definitions: `ziPP`, `ziPPt` (abbreviations of the tower shifts and their images).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zi

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Ug
  Googology.Trans.PoR.InaccPsi.R2.Uq Googology.Trans.PoR.InaccPsi.R2.Yj Googology.Trans.PoR.InaccPsi.R2.Zd

variable {S : InaccSeq.{0}}

/-- The tower shift `P_η = Y₃ + (Ω₂·Ω₂)·η`. -/
noncomputable def ziPP (S : InaccSeq.{0}) (η : Ordinal.{0}) : Ordinal.{0} := ugY S + Om (1 + 1) * Om (1 + 1) * η

/-- Its image `P̂_η = Y₂ + (Ω₁·Ω₁)·η`. -/
noncomputable def ziPPt (S : InaccSeq.{0}) (η : Ordinal.{0}) : Ordinal.{0} :=
  S.psi (Om (1 + 1)) (Om (1 + 1)) + Om 1 * Om 1 * η

theorem ziPP_zero : ziPP S 0 = ugY S := by unfold ziPP; rw [mul_zero, add_zero]

theorem ziPPt_zero : ziPPt S 0 = S.psi (Om (1 + 1)) (Om (1 + 1)) := by unfold ziPPt; rw [mul_zero, add_zero]

theorem ziPP_succ (η : Ordinal.{0}) : ziXp (ziPP S η) (Om (1 + 1)) = ziPP S (η + 1) := by
  unfold ziXp ziPP; rw [mul_add_one, add_assoc]

theorem ziPPt_succ (η : Ordinal.{0}) : ziXhp (ziPPt S η) (Om 1) = ziPPt S (η + 1) := by
  unfold ziXhp ziPPt; rw [mul_add_one, add_assoc]

theorem ziPP_mono {η η' : Ordinal.{0}} (h : η' ≤ η) : ziPP S η' ≤ ziPP S η := by
  unfold ziPP; exact (add_le_add_iff_left _).2 (mul_le_mul_left' h _)

theorem ziPP_lt {η η' : Ordinal.{0}} (h : η' < η) : ziPP S η' < ziPP S η := by
  unfold ziPP; exact (add_lt_add_iff_left _).2 (mul_lt_mul_of_pos_left h (mul_pos ldOm2_SC.1 ldOm2_SC.1))

theorem ziPPt_lt {η η' : Ordinal.{0}} (h : η' < η) : ziPPt S η' < ziPPt S η := by
  unfold ziPPt
  exact (add_lt_add_iff_left _).2 (mul_lt_mul_of_pos_left h (mul_pos (Om_pos one_ne_zero) (Om_pos one_ne_zero)))

theorem ziPP_lt_Om3 {η : Ordinal.{0}} (hη : η < Om (1 + 1)) : ziPP S η < Om (1 + 1 + 1) := by
  have h3 : SC (Om (1 + 1 + 1 : Ordinal.{0})) := SC_Om (add_pos_of_right zero_lt_one _).ne'
  have h23 : Om (1 + 1 : Ordinal.{0}) < Om (1 + 1 + 1) := Om_lt_Om.2 (lt_add_one _)
  have e : Om (1 + 1 : Ordinal.{0}) * Om (1 + 1) * Om (1 + 1) = veblen 0 (Om (1 + 1) + Om (1 + 1) + Om (1 + 1)) := by
    rw [veblen_zero_apply, opow_add, opow_add, gg_SC_eps ldOm2_SC]
  have hm : Om (1 + 1 : Ordinal.{0}) * Om (1 + 1) * η < Om (1 + 1 + 1) := by
    refine (mul_lt_mul_of_pos_left hη (mul_pos ldOm2_SC.1 ldOm2_SC.1)).trans ?_
    rw [e]; exact h3.2 0 h3.1 _ (h3.isPrincipal (h3.isPrincipal h23 h23) h23)
  unfold ziPP; exact h3.isPrincipal ugY_lt_Om3 hm

theorem ziPP_cof {η x : Ordinal.{0}} (hlim : IsSuccLimit η) (hx : x < ziPP S η) : ∃ η' < η, x < ziPP S η' := by
  have hN : Order.IsNormal (fun η : Ordinal.{0} => ugY S + Om (1 + 1) * Om (1 + 1) * η) :=
    (isNormal_add_right _).comp (isNormal_mul_right (mul_pos ldOm2_SC.1 ldOm2_SC.1))
  exact (hN.lt_iff_exists_lt hlim).1 hx

theorem ziPPt_cof {η x : Ordinal.{0}} (hlim : IsSuccLimit η) (hx : x < ziPPt S η) : ∃ η' < η, x < ziPPt S η' := by
  have hN : Order.IsNormal (fun η : Ordinal.{0} => S.psi (Om (1 + 1)) (Om (1 + 1)) + Om 1 * Om 1 * η) :=
    (isNormal_add_right _).comp (isNormal_mul_right (mul_pos (Om_pos one_ne_zero) (Om_pos one_ne_zero)))
  exact (hN.lt_iff_exists_lt hlim).1 hx

theorem ziWPP_cof {η x : Ordinal.{0}} (hlim : IsSuccLimit η) (hx : x < leWe (ziPP S η)) :
    ∃ η' < η, x < leWe (ziPP S η') := by
  have hN : Order.IsNormal (fun η : Ordinal.{0} => ω ^ (Om (1 + 1) * (ugY S + Om (1 + 1) * Om (1 + 1) * η))) :=
    (isNormal_opow one_lt_omega0).comp ((isNormal_mul_right ldOm2_SC.1).comp
      ((isNormal_add_right _).comp (isNormal_mul_right (mul_pos ldOm2_SC.1 ldOm2_SC.1))))
  exact (hN.lt_iff_exists_lt hlim).1 hx

theorem ziPP_mem {η : Ordinal.{0}} (hη : η < ziK3 S) :
    ∀ c b : Ordinal.{0}, Om (1 + 1 + 1) < c → ziPP S η ∈ S.CSet c b := fun c b h => by
  unfold ziPP; rw [mul_assoc]
  exact CSet.add_mem (Vq.vqY3_mem h) (ldMulK_mem ldOm2_SC (mxOm2_mem _ _)
    (ldMulK_mem ldOm2_SC (mxOm2_mem _ _) (ziK3_mem hη c b h)))

/-- `B_n` fixes `Ω₂·P_η` and `Ω₁·P̂_η` for `η < K₃`. -/
theorem ziPP_shB {η : Ordinal.{0}} (hη : η < ziK3 S) : Ro.RoShB S (ziPP S η) (ziPPt S η) := by
  refine ⟨?_, fun n => ?_⟩
  · unfold ziPPt; exact (Vq.vqY2_SC.1.trans_le le_self_add).ne'
  obtain ⟨hDY, hBY⟩ := Yy.yyY3_D (S := S) (n := n)
  obtain ⟨hDY2, hBY2⟩ := Yy.yyY2_D (S := S) (n := n)
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hD1, hB1⟩ := mvB_Om1 (S := S) (k := n)
  obtain ⟨hDp, hBp⟩ := mvB_add (k := n) hD2 hD2
  rw [hB2] at hBp
  obtain ⟨hDp3, hBp3⟩ := mvB_add (k := n) hDp hD2
  rw [hBp, hB2] at hBp3
  obtain ⟨hDq, hBq⟩ := mvB_add (k := n) hD1 hD1
  rw [hB1] at hBq
  obtain ⟨hDq3, hBq3⟩ := mvB_add (k := n) hDq hD1
  rw [hBq, hB1] at hBq3
  have hηC : η < Bc.bcC S n := hη.trans (ziK3_lt_C n)
  obtain ⟨hDP, hBP⟩ := ziB_opowMul (n := n) hDp3 hBp3 η hηC
  obtain ⟨hDQ, hBQ⟩ := ziB_opowMul (n := n) hDq3 hBq3 η hηC
  have e1 : Om (1 + 1) * ziPP S η = ugY S + ω ^ (Om (1 + 1) + Om (1 + 1) + Om (1 + 1)) * η := by
    unfold ziPP; rw [mul_add, zdOm2_mulY, opow_add, opow_add, gg_SC_eps ldOm2_SC]; simp only [mul_assoc]
  have e2 : Om 1 * ziPPt S η = S.psi (Om (1 + 1)) (Om (1 + 1)) + ω ^ (Om 1 + Om 1 + Om 1) * η := by
    unfold ziPPt; rw [mul_add, zdOm1_mulY2, opow_add, opow_add, gg_SC_eps Ph.ph_SC_Om1]; simp only [mul_assoc]
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDY hDP
  rw [hBY, hBP] at hBs
  obtain ⟨hDt, hBt⟩ := mvB_add (k := n) hDY2 hDQ
  rw [hBY2, hBQ] at hBt
  rw [e1, e2]
  exact ⟨hDs, hBs, hDt, hBt⟩

/-- The `Vq.VqSh` fields of `(P_η, P̂_η)` at the base `Ω₃`, `η < K₃`. -/
theorem ziPP_VqSh {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) {η : Ordinal.{0}} (hη : η < ziK3 S) :
    Vq.VqSh S l A (Om (1 + 1 + 1)) (ziPP S η) (ziPPt S η) := by
  have hA3 : Om (1 + 1 + 1) < A := Ry.ryOm3_lt.trans_le (Vn.vnA_ge hl hX hA hρ)
  have hAo : Om ω ≤ A := Vn.vnA_ge hl hX hA hρ
  have hηρ : η < upsilon l := hη.trans_le (ziCst_le_rho (Order.add_one_le_of_lt Ry.ryOm3_lt) hl hX)
  have hρΘ : ∀ x, upsilon l ≤ gxTh (upsilon l) (ldAtR S l) (S.psi x (Om (1 + 1))) := fun x =>
    calc upsilon l = gxTh (upsilon l) (ldAtR S l) (upsilon l) := (gxTh_small le_rfl).symm
      _ ≤ _ := gxTh_mono ((leRho hl hX).2.le.trans (ziOm1_lt_psi2 _).le)
  refine ⟨?_, ?_, ziPP_mem hη _ _ (Ry.ryOm3_lt.trans_le (ConjT.OmW_le_A S _)),
    ziPP_mem hη _ _ (lt_add_of_pos_right _ (leWe_pos _)), ?_, fun Q hQ hQb => ?_, fun Q hQ hQb => ?_⟩
  · unfold ziPP; exact (uqY_SC.1.trans_le le_self_add).ne'
  · unfold ziPP; rw [mul_assoc]; exact dvd_add Yy.yyOm2_dvd_Y (dvd_mul_right _ _)
  · unfold ziPPt; rw [mul_assoc]
    exact CSet.add_mem (Vq.vqY2_mem ((ldOm2_lt_OmW.trans_le hAo).trans_le le_self_add))
      (ldMulK_mem Ph.ph_SC_Om1 (CSet.Om_mem (CSet.one_mem _ _)) (ldMulK_mem Ph.ph_SC_Om1
        (CSet.Om_mem (CSet.one_mem _ _)) (ziK3_mem hη _ _ (hA3.trans_le le_self_add))))
  · unfold ziPP
    have hηQ : η < Q := (hη.trans ziK3_lt_Om1).trans ((ziOm1_lt_psi2 _).trans_le hQb)
    have h := ziVkA_opowMul hQ.1 (VkA.add (VkA.big (k := 1 + 1) (Q := Q) le_rfl ldOm2_SC)
      (VkA.big (k := 1 + 1) (Q := Q) le_rfl ldOm2_SC)) η hηQ
    rw [opow_add, gg_SC_eps ldOm2_SC] at h
    exact VkA.add (VkA.big uqW_lt_Y.le uqY_SC) h
  · unfold ziPPt
    have hηQ : η < Q := hηρ.trans_le ((hρΘ _).trans hQb)
    have h := ziVkA_opowMul hQ.1 (VkA.add (VkA.big (k := 1) (Q := Q) le_rfl Ph.ph_SC_Om1)
      (VkA.big (k := 1) (Q := Q) le_rfl Ph.ph_SC_Om1)) η hηQ
    rw [opow_add, gg_SC_eps Ph.ph_SC_Om1] at h
    exact VkA.add (VkA.big (psiS_bounds (S := S) _ 1).1.le Vq.vqY2_SC) h

/-- **EVERY `(P_η, P̂_η) = (Y₃ + Ω₂·Ω₂·η, Y₂ + Ω₁·Ω₁·η)`, `η < K₃`, IS A FIXED RELATIVE SHIFT.** -/
theorem ziRS_tow : ∀ η, η < ziK3 S → ZdRS S (ziPP S η) (ziPPt S η) := by
  intro η
  induction η using WellFoundedLT.induction with
  | ind η IH =>
  intro hη
  rcases zero_or_succ_or_isSuccLimit η with h0 | ⟨η', hη'⟩ | hlim
  · subst h0; rw [ziPP_zero, ziPPt_zero]; exact zdRS_Y3
  · rw [succ_eq_add_one] at hη'
    subst hη'
    have h := ziRSPlat (IH η' (lt_add_one η') ((lt_add_one η').trans hη))
    rwa [ziPP_succ, ziPPt_succ] at h
  · have hη2 : η < Om (1 + 1) := hη.trans ziK3_lt_Om2
    refine ⟨?_, (ziPP_lt_Om3 hη2).trans Ry.ryOm3_lt, ziPP_mem hη, ziPP_shB hη,
      fun _ _ _ hl hX hA hρ => ziPP_VqSh hl hX hA hρ hη, fun l _ _ hl hX hA hρ => ?_⟩
    · unfold ziPP; exact (uqY_SC.1.trans_le le_self_add).ne'
    have hs := ziPP_VqSh hl hX hA hρ hη
    have h0c : GxCl (upsilon l) (ldAtR S l) 0 := GxCl.zero (leRho hl hX).1.1
    refine Vq.vqTopE hs hl hX hA hρ (Vq.vqTopLimSh hl hX hA hρ hs (fun x _ hx => ?_) (fun z hz => ?_))
    · obtain ⟨η', hη', hx'⟩ := ziPP_cof hlim hx
      have hR' := IH η' hη' (hη'.trans hη)
      exact ⟨_, _, ziPP_mono hη'.le, hx', ziPPt_lt hη', ziPP_VqSh hl hX hA hρ (hη'.trans hη),
        Rv.rvTop_mono le_rfl (hR'.top l _ _ hl hX hA hρ 0 h0c ldOm2_SC.1)⟩
    · obtain ⟨η', hη', hz'⟩ := ziPPt_cof hlim hz
      have hR' := IH η' hη' (hη'.trans hη)
      exact ⟨_, _, ziPP_lt hη', hz', ziPP_VqSh hl hX hA hρ (hη'.trans hη),
        hR'.top l _ _ hl hX hA hρ 0 h0c ldOm2_SC.1⟩

section Win

variable {n : ℕ} {l l' A' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
  (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
  (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1))) (hρ' : S.psi A' (Om 1) = upsilon l')

include hR h1 hr hl' hB hA' hρ'

/-- **THE MOVES BELOW EVERY TOWER SHIFT `Y₃ + Ω₂·Ω₂·η`, `η ≤ K₃`.** -/
theorem ziBot_tow : ∀ η, η ≤ ziK3 S → ZdBot S n l l' A' (ziPP S η) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hX, -, -, -, -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  have hl := hR.1
  intro η
  induction η using WellFoundedLT.induction with
  | ind η IHη =>
  intro hη
  rcases zero_or_succ_or_isSuccLimit η with h0 | ⟨η', hη'⟩ | hlim
  · subst h0
    have h := zdBot_chain hR h1 hr hl' hB hA' hρ' 0 (epsilon_pos 0).le
    rwa [zdXr_zero, ← ziPP_zero] at h
  · rw [succ_eq_add_one] at hη'
    subst hη'
    have hη'K : η' < ziK3 S := (lt_add_one η').trans_le hη
    have h := ziBotPlat hR h1 hr hl' hB hA' hρ' (ziRS_tow η' hη'K) (IHη η' (lt_add_one η') hη'K.le)
    rwa [ziPP_succ] at h
  · intro a D hb hdv hdv' ha3 s hs hsa hsT IH
    have hXW : ziPP S η < Om ω := (ziPP_lt_Om3 (hη.trans_lt ziK3_lt_Om2)).trans Ry.ryOm3_lt
    have haW : a + leWe (ziPP S η) < Om ω :=
      vkOmW.1.isPrincipal hb.D_a.2.2 (leWe_lt_SC vkOmW.1 vkOmW.2 hXW).1
    have hsθ : s < ConjT.th S := hsT.trans_le (psi_mono hκ2 haW.le).1
    obtain ⟨d, -, hds, hdn⟩ := vbReach hl hX hs hsθ
    subst hds
    have hdnx : ∀ x, d < x → S.psi d (Om (1 + 1)) < S.psi x (Om (1 + 1)) := fun x h =>
      psi_lt_psi_of_mem hκ2 h ((psi_mono hκ2 h.le).2 hdn)
    have had : a ≤ d := by
      by_contra hc; push Not at hc
      exact absurd (hdnx a hc) (not_lt.2 hsa)
    have hdae : d < a + leWe (ziPP S η) := by
      by_contra hc; push Not at hc
      exact absurd ((psi_mono hκ2 hc).1.trans_lt hsT) (lt_irrefl _)
    have hδ : d - a < leWe (ziPP S η) := Ry.rySub_lt had hdae
    obtain ⟨η', hη', hδ'⟩ := ziWPP_cof hlim hδ
    have hle : leWe (ziPP S η') ∣ leWe (ziPP S η) := leWe_dvd (ziPP_mono hη'.le)
    refine IHη η' hη' (hη'.le.trans hη) a D hb (hle.trans hdv) (hle.trans hdv') ha3 _ hs hsa ?_ IH
    refine hdnx _ ?_
    have e1 : d = a + (d - a) := (Ordinal.add_sub_cancel_of_le had).symm
    rw [e1]; exact (add_lt_add_iff_left a).2 hδ'

/-- **THE ψ₃-OFFSETS BELOW `W^{Y₃+Ω₂·Ω₂·K₃}`**, `K₃ = ψ_{Ω₁}(Ω₃ + 1)`: above every base `a ≥ Ω₃` with a law at
both ends, `Ω₃ ∣ a`, `Ω₃ ∣ B_n a`, every atom `ψ₂(a) ≤ s < ψ₂(a + W^{Y₃+Ω₂·Ω₂·K₃})` moves under IH(s). -/
theorem ziPsi3OffWK {a D : Ordinal.{0}} (hb : YjBase S n l l' A' a D) (hd3 : Om (1 + 1 + 1) ∣ a)
    (hd3' : Om (1 + 1 + 1) ∣ Bc.bcB S n a) (ha3 : Om (1 + 1 + 1) ≤ a) {s : Ordinal.{0}} (hs : s ∈ ldAtR S l)
    (hsa : S.psi a (Om (1 + 1)) ≤ s) (hsT : s < S.psi (a + leWe (ziPP S (ziK3 S))) (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  have h3 : leWe (ziPP S (ziK3 S)) ∣ Om (1 + 1 + 1) := by
    have h := leWe_dvd (ziPP_lt_Om3 (S := S) (ziK3_lt_Om2 (S := S))).le
    rwa [Vn.vnWe_Om3] at h
  exact ziBot_tow hR h1 hr hl' hB hA' hρ' (ziK3 S) le_rfl a D hb (h3.trans hd3) (h3.trans hd3') ha3 s hs hsa
    hsT IH

end Win

end Googology.Trans.PoR.InaccPsi.R2.Zi

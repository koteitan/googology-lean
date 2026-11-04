import Googology.Trans.PoR.InaccPsi.R2.ZiPlat1

/-!
# THE PLATEAU SHIFT `P + Ω₂·Ω₂` IS AGAIN A FIXED RELATIVE SHIFT, WITH IMAGE `P̂ + Ω₁·Ω₁`

`Θ`, `W^x`, `Ω^x`, `(P, P̂)` a fixed relative shift `Zd.ZdRS S P P̂`, `X_ξ = Zi.ziXp P ξ`, `X̂_y = Zi.ziXhp P̂ y`,
`T(β) = Zi.ziTC S P β`, `f_m = Zi.ziFC S P β m`, `z_m = Zi.ziZO S P̂ Â m`.

At a base `β ≥ Ω₃` of exponent `0` of `P + Ω₂·Ω₂` with `Θ(ψ₂ β) = ψ₁(Â)`: every `f_m` is a code below `T(β)`, the top
of the code shift `X_{f_m}` at the base `β` (`Zi.ziTopC`) reads `Θ(f_{m+1}) = ψ₁(Â + Ω^{P̂+Ω₁·Θ f_m})`, so
`Θ f_m = z_m`; with the two plateaus (`Zi.ziPlatC`: `T(β) = sup f_m`; `Zi.ziPlatO`: `ψ₁(Â + Ω^{P̂+Ω₁·Ω₁}) = sup z_m`)
and `Θ` onto (`Mx.gxTh_onto`):

* `ziStepTop0` (**`Θ(ψ₂(β + W^{P+Ω₂·Ω₂})) = ψ₁(Â + Ω^{P̂+Ω₁·Ω₁})`**: the top `Rv.RvTop λ Ω₃ (P + Ω₂·Ω₂) (P̂ + Ω₁·Ω₁) 0`),
* `ziStepVqSh`, `ziStepShB` (the shift data),
* `ziRSPlat` (**`Zd.ZdRS S P P̂ ⇒ Zd.ZdRS S (P + Ω₂·Ω₂) (P̂ + Ω₁·Ω₁)`**).

The image of the plateau shift is the CONSTANT `P̂ + Ω₁·Ω₁` (= `T(P + Ω₂·Ω₂)`), not a base-dependent one: the
level-1 plateau absorbs the dependence of `Θ(T(β))` on `β`.

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zi

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Ug
  Googology.Trans.PoR.InaccPsi.R2.Zd

variable {S : InaccSeq.{0}}

theorem ziOm22_eq : Om (1 + 1 : Ordinal.{0}) * Om (1 + 1) = veblen 0 (Om (1 + 1) + Om (1 + 1)) := by
  rw [veblen_zero_apply, opow_add, gg_SC_eps ldOm2_SC]

theorem ziOm11_eq : Om (1 : Ordinal.{0}) * Om 1 = veblen 0 (Om 1 + Om 1) := by
  rw [veblen_zero_apply, opow_add, gg_SC_eps Ph.ph_SC_Om1]

theorem ziOm22_mem (a b : Ordinal.{0}) : Om (1 + 1 : Ordinal.{0}) * Om (1 + 1) ∈ S.CSet a b :=
  ldMulK_mem ldOm2_SC (mxOm2_mem _ _) (mxOm2_mem _ _)

theorem ziOm11_mem (a b : Ordinal.{0}) : Om (1 : Ordinal.{0}) * Om 1 ∈ S.CSet a b :=
  ldMulK_mem Ph.ph_SC_Om1 (CSet.Om_mem (CSet.one_mem _ _)) (CSet.Om_mem (CSet.one_mem _ _))

theorem ziOm22_lt_W : Om (1 + 1 : Ordinal.{0}) * Om (1 + 1) < Om ω := by
  rw [ziOm22_eq]; exact vkOmW.1.2 0 vkOmW.1.1 _ (vkOmW.1.isPrincipal ldOm2_lt_OmW ldOm2_lt_OmW)

theorem ziVkA_Om22 {Q : Ordinal.{0}} (hQ : SC Q) : VkA (1 + 1) Q (Om (1 + 1) * Om (1 + 1)) := by
  rw [ziOm22_eq]
  exact VkA.phi (VkA.small hQ.1) (VkA.add (VkA.big le_rfl ldOm2_SC) (VkA.big le_rfl ldOm2_SC))

theorem ziVkA_Om11 {Q : Ordinal.{0}} (hQ : SC Q) : VkA 1 Q (Om 1 * Om 1) := by
  rw [ziOm11_eq]
  exact VkA.phi (VkA.small hQ.1) (VkA.add (VkA.big le_rfl Ph.ph_SC_Om1) (VkA.big le_rfl Ph.ph_SC_Om1))

section Fix

variable {P Pt : Ordinal.{0}} (hP : ZdRS S P Pt)
include hP

/-- **The move data of the plateau shift**: `B_n` fixes `Ω₂·(P + Ω₂·Ω₂)` and `Ω₁·(P̂ + Ω₁·Ω₁)`. -/
theorem ziStepShB : Ro.RoShB S (ziXp P (Om (1 + 1))) (ziXhp Pt (Om 1)) := by
  refine ⟨?_, fun n => ?_⟩
  · unfold ziXhp; exact ((pos_iff_ne_zero.2 hP.shB.1).trans_le le_self_add).ne'
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  have hl2 : log ω (Om (1 + 1 : Ordinal.{0})) = Om (1 + 1) := by
    conv_lhs => rw [← gg_SC_eps ldOm2_SC]
    exact log_opow one_lt_omega0 _
  obtain ⟨hDX, hBX⟩ := ziB_Xr (S := S) (n := n) hP (fun x => x = 0 ∨ x = Om (1 + 1))
    (by rintro x (rfl | rfl); exacts [vbD0, hD2])
    (by
      rintro x (rfl | rfl) hx0
      · exact absurd rfl hx0
      · rw [hl2, gg_SC_eps ldOm2_SC, Ordinal.sub_self]; exact ⟨Or.inr rfl, Or.inl rfl⟩)
    (by rintro x (rfl | rfl); exacts [(ldOm2_SC.1).trans_le le_self_add, lt_add_of_pos_right _ ldOm2_SC.1])
    (Or.inr rfl)
  rw [hB2] at hBX
  obtain ⟨hD1, hB1⟩ := mvB_Om1 (S := S) (k := n)
  obtain ⟨hDK, hBK⟩ := ziB_K1 (S := S) (n := n)
  have hl1 : log ω (Om (1 : Ordinal.{0})) = Om 1 := by
    conv_lhs => rw [← gg_SC_eps Ph.ph_SC_Om1]
    exact log_opow one_lt_omega0 _
  obtain ⟨hDm, hBm⟩ := leB_mulOp2 (n := n) hDK (fun x => x = 0 ∨ x = Om 1)
    (by rintro x (rfl | rfl); exacts [vbD0, hD1])
    (by
      rintro x (rfl | rfl) hx0
      · exact absurd rfl hx0
      · rw [hl1, gg_SC_eps Ph.ph_SC_Om1, Ordinal.sub_self]; exact ⟨Or.inr rfl, Or.inl rfl⟩)
    (by rintro x (rfl | rfl); exacts [(Om_pos one_ne_zero).trans_le le_self_add,
      lt_add_of_pos_right _ (Om_pos one_ne_zero)])
    (Om 1) (Or.inr rfl)
  rw [hBK, hB1] at hBm
  obtain ⟨-, -, hDY, hBY⟩ := hP.shB.2 n
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDY hDm
  rw [hBY, hBm] at hBs
  have e : Om 1 * ziXhp Pt (Om 1) = Om 1 * Pt + ω ^ (Om 1 + Om 1) * Om 1 := by
    unfold ziXhp; rw [mul_add, opow_add, gg_SC_eps Ph.ph_SC_Om1, mul_assoc]
  rw [e]
  exact ⟨hDX, hBX, hDs, hBs⟩

theorem ziStep_lt : ziXp P (Om (1 + 1)) < Om ω := by
  unfold ziXp; exact vkOmW.1.isPrincipal hP.lt ziOm22_lt_W

theorem ziStep_mem : ∀ c b : Ordinal.{0}, Om (1 + 1 + 1) < c → ziXp P (Om (1 + 1)) ∈ S.CSet c b :=
  fun c b h => CSet.add_mem (hP.mem c b h) (ziOm22_mem _ _)

/-- **The `Vq.VqSh` fields of the plateau shift** at the base `Ω₃`, at every restart. -/
theorem ziStepVqSh {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    Vq.VqSh S l A (Om (1 + 1 + 1)) (ziXp P (Om (1 + 1))) (ziXhp Pt (Om 1)) := by
  have hsP := hP.sh l _ _ hl hX hA hρ
  have hx2 : Om (1 + 1 + 1) + leWe P ≤ Om (1 + 1 + 1) + leWe (ziXp P (Om (1 + 1))) :=
    (add_le_add_iff_left _).2 (leWe_mono le_self_add)
  refine ⟨?_, dvd_add hsP.dvd (dvd_mul_right _ _), ?_, ?_, ?_, fun Q hQ hQb => ?_, fun Q hQ hQb => ?_⟩
  · unfold ziXp; exact ((pos_iff_ne_zero.2 hP.ne).trans_le le_self_add).ne'
  · exact ziStep_mem hP _ _ (Ry.ryOm3_lt.trans_le (ConjT.OmW_le_A S _))
  · exact ziStep_mem hP _ _ (lt_add_of_pos_right _ (leWe_pos _))
  · unfold ziXhp
    exact CSet.add_mem (Vq.vqMemh hsP ((add_le_add_iff_left A).2 (leOe_mono le_self_add)) hx2 le_rfl)
      (ziOm11_mem _ _)
  · unfold ziXp; exact VkA.add (Vq.vqCl hsP hQ hx2 hQb) (ziVkA_Om22 hQ)
  · unfold ziXhp; exact VkA.add (Vq.vqClh hsP hQ hx2 hQb) (ziVkA_Om11 hQ)

set_option maxHeartbeats 1000000 in
/-- **THE TOP OF THE PLATEAU SHIFT**: `Rv.RvTop λ Ω₃ (P + Ω₂·Ω₂) (P̂ + Ω₁·Ω₁) 0`, i.e.
`Θ(ψ₂(β + W^{P+Ω₂·Ω₂})) = ψ₁(Â + Ω^{P̂+Ω₁·Ω₁})` at every base `β ≥ Ω₃` of exponent `0`. -/
theorem ziStepTop0 {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    Rv.RvTop S l (Om (1 + 1 + 1)) (ziXp P (Om (1 + 1))) (ziXhp Pt (Om 1)) 0 := by
  intro β Â hbE hβ3 hÂ hbase
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have h0c : GxCl (upsilon l) (ldAtR S l) 0 := GxCl.zero hρSC.1
  obtain ⟨hdv, hβH, hβA, hown, -⟩ := hbE
  rw [add_zero] at hdv hβA hown
  rw [add_zero, gxTh_zero, add_zero]
  unfold leTe
  set P₂ := ziXp P (Om (1 + 1)) with hP₂
  set T := S.psi (β + leWe P₂) (Om (1 + 1)) with hTdef
  have hTC : T = ziTC S P β := rfl
  set f := ziFC S P β with hf
  have hAo : Om (1 + 1 + 1) < ConjT.Aη S (cdEta S l) := Ry.ryOm3_lt.trans_le (ConjT.OmW_le_A S _)
  have hβP : Om (1 + 1 + 1) < β + leWe P₂ := hβ3.trans_lt (lt_add_of_pos_right _ (leWe_pos _))
  have hβn : β ∈ S.CSet (β + leWe P₂) T := hown _ le_rfl
  -- the iterates are codes below `T`
  have hfle : ∀ m, f (m + 1) ≤ T := fun m =>
    (psi_mono hκ2 (add_le_add_right (leWe_mono (ziXp_mono P (ziFC_lt_Om2 P β m).le)) β)).1
  have hcode : ∀ m, GxCl (upsilon l) (ldAtR S l) (f m) ∧ f m < T ∧ f m ∈ cdHull S l := by
    intro m
    induction m with
    | zero => exact ⟨h0c, (SC_psi hκ2 _).1, CSet.zero_mem _ _⟩
    | succ m ih =>
      obtain ⟨-, hfT, hfH⟩ := ih
      have hf2 : f m < Om (1 + 1) := ziFC_lt_Om2 P β m
      have hargA : β + leWe (ziXp P (f m)) < β + leWe P₂ :=
        (add_lt_add_iff_left β).2 (leWe_lt (ziXp_lt P hf2))
      have hH : f (m + 1) ∈ cdHull S l := by
        show S.psi (β + leWe (ziXp P (f m))) (Om (1 + 1)) ∈ cdHull S l
        exact CSet.psi_mem (hargA.trans hβA) hκ2 (mxOm2_mem _ _) (CSet.add_mem hβH (leWe_mem
          (CSet.add_mem (hP.mem _ _ hAo) (ldMulK_mem ldOm2_SC (mxOm2_mem _ _) hfH))))
      have hmem : f (m + 1) ∈ S.CSet (β + leWe P₂) T := by
        show S.psi (β + leWe (ziXp P (f m))) (Om (1 + 1)) ∈ S.CSet (β + leWe P₂) T
        exact CSet.psi_mem hargA hκ2 (mxOm2_mem _ _) (CSet.add_mem hβn (leWe_mem
          (CSet.add_mem (hP.mem _ _ hβP) (ldMulK_mem ldOm2_SC (mxOm2_mem _ _) (CSet.of_lt hfT)))))
      have hf12 : f (m + 1) < Om (1 + 1) := ziFC_lt_Om2 P β (m + 1)
      exact ⟨(ldHull_iff hl hX hf12).1 hH, lt_psi_of_mem hκ2 hmem hf12, hH⟩
  -- the bases of the code shifts
  have hbm : ∀ m, Ro.RoBaseE S l (ziXp P (f m)) 0 β := by
    intro m
    have hle : leWe (ziXp P (f m)) ≤ leWe P₂ := leWe_mono (ziXp_mono P (ziFC_lt_Om2 P β m).le)
    unfold Ro.RoBaseE
    rw [add_zero]
    refine ⟨(leWe_dvd (ziXp_mono P (ziFC_lt_Om2 P β m).le)).trans hdv, hβH,
      lt_of_le_of_lt ((add_le_add_iff_left β).2 hle) hβA, fun d hd => hown d (hd.trans hle), fun e' _ he' => ?_⟩
    rw [nonpos_iff_eq_zero.1 he']; exact (SC_psi hκ2 _).1
  -- the readings
  have hread : ∀ m, gxTh (upsilon l) (ldAtR S l) (f (m + 1)) =
      S.psi (Â + leOe (ziXhp Pt (gxTh (upsilon l) (ldAtR S l) (f m)))) (Om 1) := by
    intro m
    obtain ⟨hc, hfT, -⟩ := hcode m
    have h := ziTopC hP hl hX hA hρ hβ3 (f m) hc hfT 0 h0c ldOm2_SC.1 β Â (hbm m) le_rfl hÂ hbase
    unfold leTe at h
    rw [add_zero, gxTh_zero, add_zero] at h
    exact h
  have hZ : ∀ m, gxTh (upsilon l) (ldAtR S l) (f m) = ziZO S Pt Â m := by
    intro m
    induction m with
    | zero => exact gxTh_zero
    | succ m ih => rw [hread m, ih]; rfl
  -- `Θ T = sup Θ f_{m+1}`
  have hTsup : T = ⨆ m : ℕ, f (m + 1) := by rw [hTC, ziPlatC P β]; rfl
  have hbdd : BddAbove (range fun m : ℕ => gxTh (upsilon l) (ldAtR S l) (f (m + 1))) :=
    ⟨gxTh (upsilon l) (ldAtR S l) T, by rintro _ ⟨m, rfl⟩; exact gxTh_mono (hfle m)⟩
  have hΘT : gxTh (upsilon l) (ldAtR S l) T = ⨆ m : ℕ, gxTh (upsilon l) (ldAtR S l) (f (m + 1)) := by
    refine le_antisymm (le_of_forall_lt fun v hv => ?_) (ciSup_le fun m => gxTh_mono (hfle m))
    obtain ⟨c, hc, hcT, rfl⟩ := gxTh_onto hv
    rw [hTsup] at hcT
    have hbddf : BddAbove (range fun m : ℕ => f (m + 1)) :=
      ⟨Om (1 + 1), by rintro _ ⟨m, rfl⟩; exact (ziFC_lt_Om2 P β (m + 1)).le⟩
    obtain ⟨m, hm⟩ := (lt_ciSup_iff hbddf).1 hcT
    exact (gxTh_lt hc hm).trans_le (le_ciSup hbdd m)
  rw [hΘT]
  show (⨆ m : ℕ, gxTh (upsilon l) (ldAtR S l) (f (m + 1))) = ziTO S Pt Â
  rw [ziPlatO Pt Â]
  congr 1
  funext m
  rw [hread m, hZ m]

/-- **THE PLATEAU SHIFT IS A FIXED RELATIVE SHIFT**: `Zd.ZdRS S P P̂ ⇒ Zd.ZdRS S (P + Ω₂·Ω₂) (P̂ + Ω₁·Ω₁)`. -/
theorem ziRSPlat : ZdRS S (ziXp P (Om (1 + 1))) (ziXhp Pt (Om 1)) :=
  ⟨by unfold ziXp; exact ((pos_iff_ne_zero.2 hP.ne).trans_le le_self_add).ne', ziStep_lt hP, ziStep_mem hP,
    ziStepShB hP, fun _ _ _ hl hX hA hρ => ziStepVqSh hP hl hX hA hρ,
    fun _ _ _ hl hX hA hρ => Vq.vqTopE (ziStepVqSh hP hl hX hA hρ) hl hX hA hρ (ziStepTop0 hP hl hX hA hρ)⟩

end Fix

end Googology.Trans.PoR.InaccPsi.R2.Zi

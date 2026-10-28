import Googology.Trans.PoR.InaccPsi.R2.VkLay

/-!
# Shifts with no bound: the block law at the exponents `X + e` with `X` a code above the level 2

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ_{Ω₂}(β + W^E)`, `VkA k Q` the codes over `Q` above
the level `k` (module `Vk.VkCode`: every strongly critical ordinal `≥ Ω_k` is a code).

**A shift own relative to `b`, with no bound** (`VkSh S λ b X X̂`): the fields of `Uj.UjSh` without the bounds
`X + Ω₂ < Y₃`, `X̂ + Ω₁ < Y₂`, and with the codes **above the level 2** for `X`, **above the level 1** for `X̂` in
place of the level codes `Ug.UgC S 2 Q X`, `Ug.UgC S 1 Q X̂`.  The top law is `Rv.RvTop` itself.

* `vkSh_of_uj` (**every `Uj.UjSh` is a `VkSh`**), `vkSh_of_rv`, `vkSh_mono`, `vkMem`, `vkMemh`, `vkCl`, `vkClh`,
  `vkE_data`;
* `vkBaseE_sub`, `vkStepA` (the sub-bases), `vkTopSucc` (**`RvTop X e ⇒ RvTop X (e+1)` with no bound**),
  `vkTopLim` (the top at a limit code exponent), `vkTopE` (**`RvTop X 0 ⇒ RvTop X e` for every code `e`**).

No new axiom.  New definition: `VkSh`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Vk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rq
  Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj

variable {S : InaccSeq.{0}}

/-- **A shift `X` own relative to the base `b`, with its level-1 image `X̂`, with no bound**: the fields of
`Uj.UjSh` without `X + Ω₂ < Y₃`, `X̂ + Ω₁ < Y₂`, with the codes above the levels 2 and 1. -/
structure VkSh (S : InaccSeq.{0}) (l b X Xh : Ordinal.{0}) : Prop where
  ne : X ≠ 0
  dvd : Om (1 + 1) ∣ X
  hull : X ∈ cdHull S l
  mem : X ∈ S.CSet X (S.psi (b + leWe X) (Om (1 + 1)))
  memh : Xh ∈ S.CSet Xh (gxTh (upsilon l) (ldAtR S l) (S.psi (b + leWe X) (Om (1 + 1))))
  cl : ∀ Q, SC Q → S.psi (b + leWe X) (Om (1 + 1)) ≤ Q → VkA (1 + 1) Q X
  clh : ∀ Q, SC Q → gxTh (upsilon l) (ldAtR S l) (S.psi (b + leWe X) (Om (1 + 1))) ≤ Q → VkA 1 Q Xh

/-- **Every `Uj.UjSh` is a `VkSh`.** -/
theorem vkSh_of_uj {l b X Xh : Ordinal.{0}} (hs : UjSh S l b X Xh) : VkSh S l b X Xh :=
  ⟨hs.ne, hs.dvd, hs.hull, hs.mem, hs.memh, fun Q hQ hb => vkA_of_ugC hQ.1 (hs.cl Q hQ hb),
    fun Q hQ hb => vkA_of_ugC hQ.1 (hs.clh Q hQ hb)⟩

/-- **Every `Rv.RvSh` is a `VkSh`.** -/
theorem vkSh_of_rv {l b X Xh : Ordinal.{0}} (hs : RvSh S l b X Xh) : VkSh S l b X Xh :=
  vkSh_of_uj (ujSh_of_rv hs)

section Fields

variable {l b X Xh : Ordinal.{0}} (hs : VkSh S l b X Xh)
include hs

theorem vkMem {a c x : Ordinal.{0}} (ha : X ≤ a) (hx : b + leWe X ≤ x) (hb : S.psi x (Om (1 + 1)) ≤ c) :
    X ∈ S.CSet a c :=
  CSet_mono ha ((psi_mono (S := S) (InR_Om_succ 1) hx).1.trans hb) hs.mem

theorem vkMemh {a c x : Ordinal.{0}} (ha : Xh ≤ a) (hx : b + leWe X ≤ x)
    (hb : gxTh (upsilon l) (ldAtR S l) (S.psi x (Om (1 + 1))) ≤ c) : Xh ∈ S.CSet a c :=
  CSet_mono ha ((gxTh_mono (psi_mono (S := S) (InR_Om_succ 1) hx).1).trans hb) hs.memh

theorem vkCl {Q x : Ordinal.{0}} (hQ : SC Q) (hx : b + leWe X ≤ x) (hb : S.psi x (Om (1 + 1)) ≤ Q) :
    VkA (1 + 1) Q X :=
  hs.cl Q hQ ((psi_mono (S := S) (InR_Om_succ 1) hx).1.trans hb)

theorem vkClh {Q x : Ordinal.{0}} (hQ : SC Q) (hx : b + leWe X ≤ x)
    (hb : gxTh (upsilon l) (ldAtR S l) (S.psi x (Om (1 + 1))) ≤ Q) : VkA 1 Q Xh :=
  hs.clh Q hQ ((gxTh_mono (psi_mono (S := S) (InR_Om_succ 1) hx).1).trans hb)

/-- A shift own relative to `b` is own relative to every `b' ≥ b`. -/
theorem vkSh_mono {b' : Ordinal.{0}} (hbb : b ≤ b') : VkSh S l b' X Xh := by
  have h1 : S.psi (b + leWe X) (Om (1 + 1)) ≤ S.psi (b' + leWe X) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) (add_le_add_left hbb _)).1
  exact ⟨hs.ne, hs.dvd, hs.hull, vkMem hs le_rfl le_rfl h1, vkMemh hs le_rfl le_rfl (gxTh_mono h1),
    fun Q hQ hb => hs.cl Q hQ (h1.trans hb), fun Q hQ hb => hs.clh Q hQ ((gxTh_mono h1).trans hb)⟩

end Fields

section Sh

variable {l b X Xh : Ordinal.{0}} (hs : VkSh S l b X Xh)

include hs

/-- **The exponent `X + e` of an own code `e`** is own in the closure sense and a code above the level 2 over every
`Q > K_1`. -/
theorem vkE_data {β e : Ordinal.{0}} (hbβ : b ≤ β) (he : e < S.psi (β + leWe (X + e)) (Om (1 + 1))) :
    X + e ∈ S.CSet (β + leWe (X + e)) (S.psi (β + leWe (X + e)) (Om (1 + 1))) ∧
      ∀ Q, SC Q → leKe S (X + e) β 1 < Q → VkA (1 + 1) Q (X + e) := by
  refine ⟨CSet.add_mem (vkMem hs (ujX_le_base X e β) (rvWX_le hbβ X e) le_rfl) (CSet.of_lt he), fun Q hQ h1 => ?_⟩
  refine VkA.add (vkCl hs hQ (x := β + leWe (X + e) * Om 1) ?_ h1.le) (VkA.small ?_)
  · exact rvWX_le_mul hbβ X e _ (Om_pos one_ne_zero).ne'
  refine (he.trans_le ?_).trans h1
  refine (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 ?_)).1
  calc leWe (X + e) = leWe (X + e) * 1 := (mul_one _).symm
    _ ≤ leWe (X + e) * Om 1 := leMulWe_mono (one_lt_omega0.trans (Lw.lw_omega_lt_SC Ph.ph_SC_Om1)).le

/-- **`β + W^{X+e}·γ` is a base of exponent `e`** for every code `γ < T_{X+e+1}(β)`. -/
theorem vkBaseE_sub {ηx e β γ : Ordinal.{0}} (hbβ : b ≤ β) (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hb : RoBaseE S l X (e + 1) β) (hec : GxCl (upsilon l) (ldAtR S l) e)
    (hγH : γ ∈ cdHull S l) (hγ : γ < leTe S (X + e + 1) β) : RoBaseE S l X e (β + leWe (X + e) * γ) := by
  obtain ⟨hβd, hβA, hβown⟩ := roBase_succ hb
  obtain ⟨-, hβH, -, -, hexpA⟩ := hb
  have hexp : e < S.psi (β + leWe (X + e)) (Om (1 + 1)) := hexpA e hec (lt_add_one e).le
  obtain ⟨hEC, hEL⟩ := vkE_data hs hbβ hexp
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

include hl hX

/-- **The sub-bases of a block of exponent `X + e + 1`**, given the tops of exponent `X + e`. -/
theorem vkStepA {e : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (hT : RvTop S l b X Xh e)
    {β Â : Ordinal.{0}} (hb : RoBaseE S l X (e + 1) β) (hbβ : b ≤ β) (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1)))
    (hbase : gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1)) :
    ∀ γ, GxCl (upsilon l) (ldAtR S l) γ → γ < leTe S (X + e + 1) β →
      gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe (X + e) * γ) (Om (1 + 1))) =
        S.psi (Â + leOe (Xh + gxTh (upsilon l) (ldAtR S l) e) * gxTh (upsilon l) (ldAtR S l) γ) (Om 1) ∧
      Â + leOe (Xh + gxTh (upsilon l) (ldAtR S l) e) * gxTh (upsilon l) (ldAtR S l) γ ∈
        S.CSet (Â + leOe (Xh + gxTh (upsilon l) (ldAtR S l) e) * gxTh (upsilon l) (ldAtR S l) γ)
          (S.psi (Â + leOe (Xh + gxTh (upsilon l) (ldAtR S l) e) * gxTh (upsilon l) (ldAtR S l) γ) (Om 1)) := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hρ0 : 0 < upsilon l := hρSC.1
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small (gg_one_lt_of_SC hρSC).le
  have hb' := hb
  obtain ⟨hβd, hβA, hβown⟩ := roBase_succ hb
  obtain ⟨-, hβH, -, -, hexpA⟩ := hb
  have hexp : e < S.psi (β + leWe (X + e)) (Om (1 + 1)) := hexpA e hec (lt_add_one e).le
  obtain ⟨hEC, hEL⟩ := vkE_data hs hbβ hexp
  have hμ0 : leWe (X + e) ≠ 0 := (leWe_pos _).ne'
  set O := leOe (Xh + gxTh (upsilon l) (ldAtR S l) e) with hO_def
  have hO0 : O ≠ 0 := (leOe_pos _).ne'
  have hβd' : leWe (X + e) * Om (1 + 1) ∣ β := by rw [← leWe_succ]; exact hβd
  have hβA' : β + leWe (X + e) * Om (1 + 1) < ConjT.Aη S (cdEta S l) := by rw [← leWe_succ]; exact hβA
  have heH : e ∈ cdHull S l := (ldHull_iff hl hX (hexp.trans (psi_lt (InR_Om_succ 1) _))).2 hec
  have hXeH : X + e ∈ cdHull S l := CSet.add_mem hs.hull heH
  have hsub : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ → γ < leTe S (X + e + 1) β →
      RoBaseE S l X e (β + leWe (X + e) * γ) := fun γ hγ hγT =>
    vkBaseE_sub hs hbβ hl hX hb' hec ((ldHull_iff hl hX (hγT.trans (leTe_lt_Om2 _ _))).2 hγ) hγT
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
    refine Rv.rvHat_own hÂ (vkMemh hs (ujXh_le Xh _ Â hΘγ0) (rvWX_le_mul hbβ X e γ hγ0) E.le) ?_ ?_
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
theorem vkTopSucc {e : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (hT : RvTop S l b X Xh e) :
    RvTop S l b X Xh (e + 1) := by
  intro β Â hb hbβ hÂ hbase
  rw [← add_assoc]
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small (gg_one_lt_of_SC hρSC).le
  have hA := vkStepA hs hl hX hec hT hb hbβ hÂ hbase
  obtain ⟨hβd, hβA, hβown⟩ := roBase_succ hb
  obtain ⟨-, hβH, -, -, hexpA⟩ := hb
  have hexp : e < S.psi (β + leWe (X + e)) (Om (1 + 1)) := hexpA e hec (lt_add_one e).le
  obtain ⟨hEC, hEL⟩ := vkE_data hs hbβ hexp
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
    VkA.add (vkClh hs hTSC (x := β + leWe (X + e + 1)) (by rw [add_assoc]; exact rvWX_le hbβ X (e + 1)) le_rfl)
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


section MainE

variable {l b X Xh : Ordinal.{0}} (hs : VkSh S l b X Xh) {ηx : Ordinal.{0}} (hl : IsRestartIdx l)
  (hX : upsilon l < Pv S ηx)

include hs hl hX

/-- **The top of a block of a limit code exponent `X + e`**, from the smaller tops. -/
theorem vkTopLim {e : Ordinal.{0}} (hlim : IsSuccLimit e) (hec : GxCl (upsilon l) (ldAtR S l) e)
    (heW : e < Om (1 + 1)) (hIH : ∀ e', GxCl (upsilon l) (ldAtR S l) e' → e' < e → RvTop S l b X Xh e') :
    RvTop S l b X Xh e := by
  intro β Â hb hbβ hÂ hbase
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hρ0 : 0 < upsilon l := hρSC.1
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small (gg_one_lt_of_SC hρSC).le
  have hb' := hb
  obtain ⟨hβd, hβH, hβA, hβown, hexpA⟩ := hb
  have hexp : e < S.psi (β + leWe (X + e)) (Om (1 + 1)) := hexpA e hec le_rfl
  have he0 : e ≠ 0 := hlim.ne_bot
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  have heH : e ∈ cdHull S l := (ldHull_iff hl hX heW).2 hec
  have hΘsucc : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ →
      gxTh (upsilon l) (ldAtR S l) (γ + 1) = gxTh (upsilon l) (ldAtR S l) γ + 1 := fun γ hγ => by
    rw [gxTh_add hρSC hAt hγ 1, hΘ1]
  have hcode1 : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ → γ + 1 < Om (1 + 1) →
      GxCl (upsilon l) (ldAtR S l) (γ + 1) := fun γ hγ h =>
    (ldHull_iff hl hX h).1 (CSet.succ_mem ((ldHull_iff hl hX ((lt_add_one γ).trans h)).2 hγ))
  have hβat : S.psi β (Om (1 + 1)) ∈ ldAtR S l := ⟨β, hβH, le_self_add.trans_lt hβA, rfl⟩
  have hρÂ : upsilon l < S.psi Â (Om 1) := by
    rw [← hbase]; exact (ldAtom_ge hρSC hρ1 hAt hβat).2.1
  set Y := S.psi (Â + leOe (Xh + gxTh (upsilon l) (ldAtR S l) e)) (Om 1) with hY_def
  have hÂY : Â ∈ S.CSet (Â + leOe (Xh + gxTh (upsilon l) (ldAtR S l) e)) Y :=
    (psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ
  have hÂlt : S.psi Â (Om 1) < Y := psi_lt_psi_of_mem Low.InR_Om_one (lt_add_of_pos_right Â (leOe_pos _)) hÂY
  -- the smaller tops
  have hsubE : ∀ g, GxCl (upsilon l) (ldAtR S l) g → g < e →
      gxTh (upsilon l) (ldAtR S l) (leTe S (X + g) β) =
        S.psi (Â + leOe (Xh + gxTh (upsilon l) (ldAtR S l) g)) (Om 1) ∧
      leTe S (X + g) β ∈ ldAtR S l ∧ leTe S (X + g) β < leTe S (X + e) β ∧
      S.psi (Â + leOe (Xh + gxTh (upsilon l) (ldAtR S l) g)) (Om 1) < Y := by
    intro g hg hge
    have hgW : g < Om (1 + 1) := hge.trans heW
    have hgH : g ∈ cdHull S l := (ldHull_iff hl hX hgW).2 hg
    have hexpg : g < S.psi (β + leWe (X + g)) (Om (1 + 1)) := hexpA _ hg hge.le
    have e1 := hIH g hg hge β Â (roBaseE_mono hge.le hb') hbβ hÂ hbase
    have hlt : β + leWe (X + g) < β + leWe (X + e) :=
      (add_lt_add_iff_left β).2 (leWe_lt ((add_lt_add_iff_left X).2 hge))
    refine ⟨e1, ⟨β + leWe (X + g), CSet.add_mem hβH (leWe_mem (CSet.add_mem hs.hull hgH)),
      hlt.trans hβA, rfl⟩, ?_, ?_⟩
    · refine psi_lt_psi_of_mem (InR_Om_succ 1) hlt (CSet.add_mem (hβown _ le_rfl)
        (leWe_mem (CSet.add_mem (vkMem hs (ujX_le_base X e β) (rvWX_le hbβ X e) le_rfl) (CSet.of_lt ?_))))
      exact hexpg.trans_le (psi_mono (S := S) (InR_Om_succ 1) hlt.le).1
    · have hΘlt : gxTh (upsilon l) (ldAtR S l) g < gxTh (upsilon l) (ldAtR S l) e := gxTh_lt hg hge
      have hlt2 : Â + leOe (Xh + gxTh (upsilon l) (ldAtR S l) g) <
          Â + leOe (Xh + gxTh (upsilon l) (ldAtR S l) e) :=
        (add_lt_add_iff_left Â).2 (leOe_lt ((add_lt_add_iff_left Xh).2 hΘlt))
      refine psi_lt_psi_of_mem Low.InR_Om_one hlt2 ((psi_mono (S := S) Low.InR_Om_one hlt2.le).2 ?_)
      refine CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ)
        (leOe_mem (CSet.add_mem (vkMemh hs (ujXh_le1 Xh _ Â) (rvWX_le hbβ X g) e1.le) (CSet.of_lt ?_)))
      rw [← e1]
      exact gxTh_lt hg hexpg
  have h0e : (0 : Ordinal.{0}) < e := pos_iff_ne_zero.2 he0
  have hc0 : GxCl (upsilon l) (ldAtR S l) (0 : Ordinal.{0}) := GxCl.zero hρ0
  have htop : leTe S (X + e) β ∈ ldAtR S l :=
    ⟨β + leWe (X + e), CSet.add_mem hβH (leWe_mem (CSet.add_mem hs.hull heH)), hβA, rfl⟩
  have hup : gxTh (upsilon l) (ldAtR S l) (leTe S (X + e) β) ≤ Y := by
    refine ldAtom_le hρSC hρ1 hAt (SC_psi Low.InR_Om_one _) (hρÂ.trans hÂlt) ?_
    intro t ht hts
    obtain ⟨a, haH, -, rfl⟩ := ht
    rcases lt_or_ge a β with haβ | haβ
    · exact (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1) haβ.le).1).trans_lt (by rw [hbase]; exact hÂlt)
    obtain ⟨d, rfl⟩ := exists_add_of_le haβ
    have hd : d < leWe (X + e) := by
      by_contra h
      push Not at h
      exact absurd hts (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 h)).1)
    rcases eq_or_ne d 0 with rfl | hd0
    · rw [add_zero]; exact (le_of_eq hbase).trans_lt hÂlt
    have hdH : d ∈ cdHull S l := by
      have h1 := leModP_mem (S := S) (Om (1 + 1) * (X + e)) haH
      have hm : (β + d) % ω ^ (Om (1 + 1) * (X + e)) = d := by
        obtain ⟨q, hq⟩ := hβd
        change (β + d) % leWe (X + e) = d
        rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hd]
      rwa [hm] at h1
    set x := log ω d / Om (1 + 1) with hx_def
    have hlogd : log ω d < Om (1 + 1) * (X + e) :=
      (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hd0).trans_lt hd)
    have hxe : x < X + e := (Ordinal.lt_mul_iff_div_lt hW0).1 hlogd
    have hxH : x ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hdH)
    have hdx := roLt_We_log d
    rw [← hx_def] at hdx
    -- the exponent `g'` of a smaller top above `ψ_{Ω₂}(β + d)`
    obtain ⟨g', hg'c, hg'e, hdg'⟩ : ∃ g', GxCl (upsilon l) (ldAtR S l) g' ∧ g' < e ∧ d < leWe (X + g') := by
      rcases lt_or_ge x X with hxX | hxX
      · refine ⟨0, hc0, h0e, hdx.trans_le (leWe_mono ?_)⟩
        rw [add_zero]; exact Order.add_one_le_of_lt hxX
      · have hxW : x < X + Om (1 + 1) := hxe.trans ((add_lt_add_iff_left X).2 heW)
        have hgm := roModX hs.dvd hxX hxW
        have hgH : x - X ∈ cdHull S l := by rw [← hgm]; exact ldModK_mem ldOm2_SC hxH
        have hge : x - X < e := by
          have : X + (x - X) < X + e := by rwa [Ordinal.add_sub_cancel_of_le hxX]
          exact (add_lt_add_iff_left X).1 this
        have hgc := (ldHull_iff hl hX (hge.trans heW)).1 hgH
        refine ⟨x - X + 1, hcode1 _ hgc ((hlim.succ_lt hge).trans heW), hlim.succ_lt hge, ?_⟩
        rw [← add_assoc, Ordinal.add_sub_cancel_of_le hxX]; exact hdx
    obtain ⟨e1, -, -, hY1⟩ := hsubE g' hg'c hg'e
    refine lt_of_le_of_lt (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1)
      ((add_le_add_iff_left β).2 hdg'.le)).1) ?_
    change gxTh (upsilon l) (ldAtR S l) (leTe S _ β) < Y
    rw [e1]; exact hY1
  apply le_antisymm hup
  obtain ⟨hTSC, -, hTs⟩ := ldAtom_ge hρSC hρ1 hAt htop
  refine ldPsi1_le hTSC fun x hx _ => ?_
  have hβs : S.psi β (Om (1 + 1)) < leTe S (X + e) β := by
    unfold leTe
    exact psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right β (leWe_pos _)) (hβown _ le_rfl)
  rcases le_or_gt x Â with hxÂ | hxÂ
  · refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one hxÂ).1 ?_
    rw [← hbase]; exact hTs _ hβat hβs
  obtain ⟨r, rfl⟩ := exists_add_of_le hxÂ.le
  have hr : r < leOe (Xh + gxTh (upsilon l) (ldAtR S l) e) := (add_lt_add_iff_left Â).1 hx
  rcases eq_or_ne r 0 with rfl | hr0
  · rw [add_zero, ← hbase]; exact hTs _ hβat hβs
  set z := log ω r / Om 1 with hz_def
  have hlogr : log ω r < Om 1 * (Xh + gxTh (upsilon l) (ldAtR S l) e) :=
    (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hr0).trans_lt hr)
  have hze : z < Xh + gxTh (upsilon l) (ldAtR S l) e := (Ordinal.lt_mul_iff_div_lt hΩ0).1 hlogr
  have hrz := roLt_Oe_log r
  rw [← hz_def] at hrz
  obtain ⟨g', hg'c, hg'e, hrg'⟩ : ∃ g', GxCl (upsilon l) (ldAtR S l) g' ∧ g' < e ∧
      r < leOe (Xh + gxTh (upsilon l) (ldAtR S l) g') := by
    rcases lt_or_ge z Xh with hzX | hzX
    · refine ⟨0, hc0, h0e, hrz.trans_le (leOe_mono ?_)⟩
      rw [gxTh_zero, add_zero]; exact Order.add_one_le_of_lt hzX
    · have hz' : z - Xh < gxTh (upsilon l) (ldAtR S l) e := by
        have : Xh + (z - Xh) < Xh + gxTh (upsilon l) (ldAtR S l) e := by
          rwa [Ordinal.add_sub_cancel_of_le hzX]
        exact (add_lt_add_iff_left Xh).1 this
      obtain ⟨g, hgc, hge, hgz⟩ := gxTh_onto hz'
      refine ⟨g + 1, hcode1 _ hgc ((hlim.succ_lt hge).trans heW), hlim.succ_lt hge, ?_⟩
      rw [hΘsucc g hgc, hgz, ← add_assoc, Ordinal.add_sub_cancel_of_le hzX]; exact hrz
  obtain ⟨e1, hat1, hlt1, -⟩ := hsubE g' hg'c hg'e
  refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left Â).2 hrg'.le)).1 ?_
  rw [← e1]
  exact hTs _ hat1 hlt1

/-- **`RvTop X 0` gives `RvTop X e` for every code `e`.** -/
theorem vkTopE (h0 : RvTop S l b X Xh 0) :
    ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → RvTop S l b X Xh e := by
  intro e
  induction e using WellFoundedLT.induction with
  | ind e IH =>
  intro hec heW
  rcases zero_or_succ_or_isSuccLimit e with h | ⟨e0, he0⟩ | hlim
  · subst h; exact h0
  · rw [succ_eq_add_one] at he0
    subst he0
    have he0W : e0 < Om (1 + 1) := (lt_add_one e0).trans heW
    have he0c : GxCl (upsilon l) (ldAtR S l) e0 :=
      (ldHull_iff hl hX he0W).1 (mem_of_add_one_mem ((ldHull_iff hl hX heW).2 hec))
    exact vkTopSucc hs hl hX he0c (IH e0 (lt_add_one e0) he0c he0W)
  · exact vkTopLim hs hl hX hlim hec heW (fun e' he' he'e => IH e' he'e he' (he'e.trans heW))

end MainE
end Googology.Trans.PoR.InaccPsi.R2.Vk

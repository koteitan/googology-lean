import Googology.Trans.PoR.InaccPsi.R2.VkOwnS

/-!
# The family of a level, with no bound

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ_{Ω₂}(β + W^E)`, `EE_j = Rv.rvEE S X₀ β E j`.
`Uj.ujSh_m`, `Uj.ujFam`, `Uj.ujEE_code` with the offsets `Vk.VkOff`, the own exponents `Vk.VkOwnE` and the level
statement `Vk.VkLev` (no bound).

* `vkSh_m` (**the members `(X₀ + W^E·ζ, X̂₀ + Ω^Ê·Θ ζ)` are shifts `VkSh`**), `vkFam` (**the level-`E` family over
  `β`**: every code `ζ < EE_j` gives an offset `X₀ + W^E·ζ` with its top), `vkEE_code` (`EE_j` is a code with
  `Θ(EE_j) < Ω₁`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Vk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj

variable {S : InaccSeq.{0}}

section Mem

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The members `(X₀ + W^E·ζ, X̂₀ + Ω^Ê·Θ ζ)` are shifts own relative to `β`**, `E` an own exponent of any
level. -/
theorem vkSh_m {E Eh β X0 Xh0 ζ : Ordinal.{0}} (hoff : VkOff S l β X0 Xh0) (hEo : VkOwnE S l β X0 E Eh)
    (hζ : GxCl (upsilon l) (ldAtR S l) ζ) (hζW : ζ < Om (1 + 1)) (hζ0 : ζ ≠ 0)
    (hown : ζ < S.psi (β + leWe (X0 + leWe E * ζ)) (Om (1 + 1))) :
    VkSh S l β (X0 + leWe E * ζ) (Xh0 + leOe Eh * gxTh (upsilon l) (ldAtR S l) ζ) := by
  obtain ⟨hd, hH, hm, hmh, hcl, hclh⟩ := vkOff_data hoff
  have hle : S.psi (β + leWe X0) (Om (1 + 1)) ≤ S.psi (β + leWe (X0 + leWe E * ζ)) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1
  have hEle : S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)) ≤ S.psi (β + leWe (X0 + leWe E * ζ)) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono ((add_le_add_iff_left X0).2 (by
      calc leWe E = leWe E * 1 := (mul_one _).symm
        _ ≤ leWe E * ζ := leMulWe_mono (Order.one_le_iff_ne_zero.2 hζ0)))))).1
  have hΘown := gxTh_lt (Z := upsilon l) (At := ldAtR S l) hζ hown
  have hWk : Om (1 + 1) ∣ leWe E := by
    have h := leWe_dvd hEo.one; rwa [leWe_one] at h
  have h2 : (1 + 1 : Ordinal.{0}) ≠ 0 := by rw [one_add_one_eq_two]; exact two_ne_zero
  have hΘ0 : gxTh (upsilon l) (ldAtR S l) ζ ≠ 0 := by
    have := gxTh_lt (Z := upsilon l) (At := ldAtR S l) (GxCl.zero (leRho hl hX).1.1) (pos_iff_ne_zero.2 hζ0)
    rw [gxTh_zero] at this; exact this.ne'
  have hEa : E ≤ X0 + leWe E * ζ :=
    (ujLe_We E).trans ((Ordinal.le_mul_left _ (pos_iff_ne_zero.2 hζ0)).trans le_add_self)
  have hEha : Eh ≤ Xh0 + leOe Eh * gxTh (upsilon l) (ldAtR S l) ζ :=
    (ujLe_Oe Eh).trans ((Ordinal.le_mul_left _ (pos_iff_ne_zero.2 hΘ0)).trans le_add_self)
  refine ⟨fun h => (mul_ne_zero (leWe_pos E).ne' hζ0) (le_antisymm (h ▸ le_add_self) zero_le),
    dvd_add hd (hWk.trans (dvd_mul_right _ _)),
    CSet.add_mem hH (leMulWe_mem hEo.hull ((ldHull_iff hl hX hζW).2 hζ)),
    CSet.add_mem (CSet_mono le_self_add hle hm) (leMulWe_mem (CSet_mono hEa hEle hEo.mem) (CSet.of_lt hown)),
    CSet.add_mem (CSet_mono le_self_add (gxTh_mono hle) hmh)
      (leMulOe_mem (CSet_mono hEha (gxTh_mono hEle) hEo.memh) (CSet.of_lt hΘown)),
    fun Q hQ hb => VkA.add (hcl Q hQ (hle.trans hb)) (vkA_mulOp hQ (vkA_mulK hQ h2 E
      (hEo.cl Q hQ (hEle.trans hb))) _ (VkA.small (hown.trans_le hb))),
    fun Q hQ hb => VkA.add (hclh Q hQ ((gxTh_mono hle).trans hb)) (vkA_mulOp hQ (vkA_mulK hQ
      one_ne_zero _ (hEo.clh Q hQ ((gxTh_mono hEle).trans hb))) _ (VkA.small (hΘown.trans_le hb)))⟩

end Mem

section Fam

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {E Eh : Ordinal.{0}} (hP : VkOwP S l Ow E Eh) (IH : VkLev S l Ow E Eh)

include hl hX hP IH

/-- **The level-`E` family over `β`** (bound `ζ < EE_j(X₀, β, E)`), `E` an own exponent of any level. -/
theorem vkFam {X0 Xh0 β : Ordinal.{0}} (hoff : VkOff S l β X0 Xh0) (hd : leWe (E + 1) ∣ X0)
    (hEX : Ow β X0) :
    ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → (∃ j, ζ < rvEE S X0 β E j) →
      gxTh (upsilon l) (ldAtR S l) ζ < Om 1 →
      VkOff S l β (X0 + leWe E * ζ) (Xh0 + leOe Eh * gxTh (upsilon l) (ldAtR S l) ζ) := by
  have hk0 : leWe E ≠ 0 := (leWe_pos E).ne'
  have hOk0 : leOe Eh ≠ 0 := (leOe_pos _).ne'
  have hdk : leWe E ∣ X0 := (leWe_dvd le_self_add).trans hd
  have hEo := hP.dat _ _ hEX
  have hmem : ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → (∃ j, ζ < rvEE S X0 β E j) →
      gxTh (upsilon l) (ldAtR S l) ζ < Om 1 → ζ ≠ 0 →
      VkSh S l β (X0 + leWe E * ζ) (Xh0 + leOe Eh * gxTh (upsilon l) (ldAtR S l) ζ) := fun ζ hζ hζT hΘ hζ0 => by
    obtain ⟨j, hj⟩ := hζT
    exact vkSh_m hl hX hoff hEo hζ (hj.trans (rvEE_lt_Om2 j)) hζ0 (rvEE_gt j ζ hj)
  intro ζ
  induction ζ using WellFoundedLT.induction with
  | ind ζ IHz =>
  intro hζ hζT hΘ1
  have hζW : ζ < Om (1 + 1) := by obtain ⟨j, hj⟩ := hζT; exact hj.trans (rvEE_lt_Om2 j)
  rcases zero_or_succ_or_isSuccLimit ζ with h0 | ⟨ζ0, hζ0⟩ | hlim
  · subst h0; simpa only [mul_zero, add_zero, gxTh_zero] using hoff
  · rw [succ_eq_add_one] at hζ0
    subst hζ0
    have hζ0c := rqCode_pred hl hX hζ hζW
    have hΘ0 : gxTh (upsilon l) (ldAtR S l) ζ0 < Om 1 := (gxTh_mono (lt_add_one ζ0).le).trans_lt hΘ1
    have hT0 : ∃ j, ζ0 < rvEE S X0 β E j := by
      obtain ⟨j, hj⟩ := hζT; exact ⟨j, (lt_add_one ζ0).trans hj⟩
    have hoff0 := IHz ζ0 (lt_add_one ζ0) hζ0c hT0 hΘ0
    have hΘs := rqTh_succ hl hX hζ0c
    have hle1 : leWe E * ζ0 + leWe E ≤ leWe (E + 1) := by
      rw [← mul_add_one]; exact (rvWe_lt_succ hζW).le
    have hle2 : leOe Eh * gxTh (upsilon l) (ldAtR S l) ζ0 + leOe Eh ≤ leOe (Eh + 1) := by
      rw [← mul_add_one, ← hΘs]; exact (rvOe_lt_succ hΘ1).le
    have hEX0 : Ow β (X0 + leWe E * ζ0) := hP.mono _ _ _ _ hEX le_rfl le_self_add
    have ht := IH β _ _ hoff0 (dvd_add hdk (dvd_mul_right _ _)) hEX0
    rw [add_assoc, add_assoc, ← mul_add_one, ← mul_add_one, ← hΘs] at ht
    exact Or.inr ⟨hmem _ hζ hζT hΘ1 (by simp), ht⟩
  · have hζ0 : ζ ≠ 0 := hlim.ne_bot
    have hs := hmem ζ hζ hζT hΘ1 hζ0
    have hΘpos : 0 < gxTh (upsilon l) (ldAtR S l) ζ := by
      have := gxTh_lt (Z := upsilon l) (At := ldAtR S l) (GxCl.zero (leRho hl hX).1.1) (pos_iff_ne_zero.2 hζ0)
      rwa [gxTh_zero] at this
    have hsub : ∀ c, GxCl (upsilon l) (ldAtR S l) c → c < ζ →
        VkSh S l β (X0 + leWe E * (c + 1)) (Xh0 + leOe Eh * gxTh (upsilon l) (ldAtR S l) (c + 1)) ∧
        RvTop S l β (X0 + leWe E * (c + 1)) (Xh0 + leOe Eh * gxTh (upsilon l) (ldAtR S l) (c + 1)) 0 ∧
        gxTh (upsilon l) (ldAtR S l) (c + 1) < gxTh (upsilon l) (ldAtR S l) ζ := by
      intro c hc hcζ
      have hc1 := hlim.succ_lt hcζ
      have hc1c := rqCode_succ hl hX hc (hc1.trans hζW)
      have hΘc : gxTh (upsilon l) (ldAtR S l) (c + 1) < Om 1 := (gxTh_mono hc1.le).trans_lt hΘ1
      have hT1 : ∃ j, c + 1 < rvEE S X0 β E j := by
        obtain ⟨j, hj⟩ := hζT; exact ⟨j, hc1.trans hj⟩
      have h := vkOff_ne (IHz _ hc1 hc1c hT1 hΘc)
        (fun h => (mul_ne_zero hk0 (by simp)) (le_antisymm (h ▸ le_add_self) zero_le))
      exact ⟨h.1, h.2, gxTh_lt hc1c hc1⟩
    refine Or.inr ⟨hs, vkTopLimSh hl hX hs (fun x hxH hx => ?_) (fun z hz => ?_)⟩
    · rcases lt_or_ge x X0 with hxX | hxX
      · have hX00 : X0 ≠ 0 := (zero_le.trans_lt hxX).ne'
        obtain ⟨hs0, ht0⟩ := vkOff_ne hoff hX00
        refine ⟨X0, Xh0, le_self_add, hxX, lt_add_of_pos_right _ (mul_pos (leOe_pos _) hΘpos), hs0, ht0⟩
      · obtain ⟨r, rfl⟩ := exists_add_of_le hxX
        have hr : r < leWe E * ζ := (add_lt_add_iff_left X0).1 hx
        have hrW : r < leWe (E + 1) := hr.trans (rvWe_lt_succ hζW)
        have hrH : r ∈ cdHull S l := by
          have h1 := leModP_mem (S := S) (Om (1 + 1) * (E + 1)) hxH
          have hm : (X0 + r) % ω ^ (Om (1 + 1) * (E + 1)) = r := by
            obtain ⟨q, hq⟩ := hd
            change (X0 + r) % leWe (E + 1) = r
            rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hrW]
          rwa [hm] at h1
        have hq : r / leWe E < ζ := (Ordinal.lt_mul_iff_div_lt hk0).1 hr
        have hqc := (ldHull_iff hl hX (hq.trans hζW)).1
          (leDivOp_mem (dvd_mul_right _ _) hrH (by rw [← mul_add_one]; exact hrW))
        obtain ⟨hs1, ht1, hΘlt⟩ := hsub _ hqc hq
        refine ⟨_, _, ?_, ?_, (add_lt_add_iff_left Xh0).2 ((mul_lt_mul_iff_right₀ (leOe_pos _)).2 hΘlt), hs1, ht1⟩
        · exact (add_le_add_iff_left X0).2 (mul_le_mul_right (Order.add_one_le_of_lt hq) _)
        · refine (add_lt_add_iff_left X0).2 ?_
          rw [mul_add_one]; exact Ordinal.lt_mul_div_add r hk0
    · rcases lt_or_ge z Xh0 with hzX | hzX
      · have hXh00 : Xh0 ≠ 0 := (zero_le.trans_lt hzX).ne'
        obtain ⟨hs0, ht0⟩ := vkOff_neh hoff hXh00
        exact ⟨X0, Xh0, lt_add_of_pos_right _ (mul_pos (leWe_pos E) (pos_iff_ne_zero.2 hζ0)), hzX, hs0, ht0⟩
      · obtain ⟨u, rfl⟩ := exists_add_of_le hzX
        have hu : u < leOe Eh * gxTh (upsilon l) (ldAtR S l) ζ := (add_lt_add_iff_left Xh0).1 hz
        have hq : u / leOe Eh < gxTh (upsilon l) (ldAtR S l) ζ := (Ordinal.lt_mul_iff_div_lt hOk0).1 hu
        obtain ⟨c, hc, hcζ, hcz⟩ := gxTh_onto hq
        obtain ⟨hs1, ht1, -⟩ := hsub c hc hcζ
        refine ⟨_, _, (add_lt_add_iff_left X0).2 ((mul_lt_mul_iff_right₀ (leWe_pos E)).2 (hlim.succ_lt hcζ)), ?_,
          hs1, ht1⟩
        refine (add_lt_add_iff_left Xh0).2 ?_
        rw [rqTh_succ hl hX hc, hcz, mul_add_one]; exact Ordinal.lt_mul_div_add u hOk0

/-- **`EE_j` is a code with `Θ(EE_j) < Ω₁`** at a base `β` of `X₀ + W^{E+1}` with a reading. -/
theorem vkEE_code {X0 Xh0 β Â : Ordinal.{0}} (hoff : VkOff S l β X0 Xh0) (hd : leWe (E + 1) ∣ X0)
    (hEX : Ow β X0)
    (hb : RoBaseE S l (X0 + leWe (E + 1)) 0 β) (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1)))
    (hbase : gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1)) :
    ∀ j, GxCl (upsilon l) (ldAtR S l) (rvEE S X0 β E j) ∧
      gxTh (upsilon l) (ldAtR S l) (rvEE S X0 β E j) < Om 1 := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hEo := hP.dat _ _ hEX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  obtain ⟨-, hX0H, hX0m, -, -, -⟩ := vkOff_data hoff
  have hb' := hb
  obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hb
  rw [add_zero] at hβd hβA hβown
  have hk0 : leWe E ≠ 0 := (leWe_pos E).ne'
  intro j
  induction j with
  | zero =>
    refine ⟨GxCl.om, ?_⟩
    change gxTh (upsilon l) (ldAtR S l) (Om 1) < Om 1
    rw [gxTh_Om1 hρSC hρ1 hAt]; exact hρ1
  | succ j IHj =>
    obtain ⟨hc, hΘ⟩ := IHj
    have hjW : rvEE S X0 β E j < Om (1 + 1) := rvEE_lt_Om2 j
    have hjH : rvEE S X0 β E j ∈ cdHull S l := (ldHull_iff hl hX hjW).2 hc
    have hlt : β + leWe (X0 + leWe E * rvEE S X0 β E j) < β + leWe (X0 + leWe (E + 1)) :=
      (add_lt_add_iff_left β).2 (leWe_lt ((add_lt_add_iff_left X0).2 (rvWe_lt_succ hjW)))
    have hat : rvEE S X0 β E (j + 1) ∈ ldAtR S l :=
      ⟨β + leWe (X0 + leWe E * rvEE S X0 β E j),
        CSet.add_mem hβH (leWe_mem (CSet.add_mem hX0H (leMulWe_mem hEo.hull hjH))), hlt.trans hβA, rfl⟩
    refine ⟨GxCl.atom hat, ?_⟩
    have hj0 : rvEE S X0 β E j ≠ 0 := (rvEE_SC j).1.ne'
    have hoffj := vkFam hl hX hP IH hoff hd hEX _ hc
      ⟨j + 1, vkEE_lt_succ hβown hX0m hEo.mem j⟩ hΘ
    obtain ⟨-, htj⟩ := vkOff_ne hoffj
      (fun h => (mul_ne_zero hk0 hj0) (le_antisymm (h ▸ le_add_self) zero_le))
    have hsb : RoBaseE S l (X0 + leWe E * rvEE S X0 β E j) 0 β :=
      roBaseE_shift hb' (by rw [add_zero]; exact (add_le_add_iff_left X0).2 (rvWe_lt_succ hjW).le) zero_le
    have e1 := htj β Â hsb le_rfl hÂ hbase
    have e2 : leTe S (X0 + leWe E * rvEE S X0 β E j + 0) β = rvEE S X0 β E (j + 1) := by
      rw [add_zero]; rfl
    rw [e2] at e1
    rw [e1]; exact psi_lt Low.InR_Om_one _

end Fam

end Googology.Trans.PoR.InaccPsi.R2.Vk

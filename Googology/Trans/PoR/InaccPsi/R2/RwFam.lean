import Googology.Trans.PoR.InaccPsi.R2.RwMove

/-!
# The base-indexed family of the shifts with exponents below `ρ_λ`, and its top law

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ_{Ω₂}(β + W^E)`,
`EE_j(X₀, β, f) = Rv.rvEE S X₀ β f j` (`EE_0 = Ω₁`, `EE_{j+1} = ψ_{Ω₂}(β + W^{X₀ + W^f·EE_j})`).

`RwF S λ β X X̂ f` (**the family over the base `β`**, `f` the last level): `X = W^{f₁}·ζ₁ + … + W^{f_k}·ζ_k`,
`X̂ = Ω^{f₁}·Θ ζ₁ + … + Ω^{f_k}·Θ ζ_k`, `ρ_λ > f₁ > … > f_k = f ≥ 1`, `ζ_i ≠ 0` codes with `Θ ζ_i < Ω₁` and
`ζ_i < EE_j(X_{<i}, β, f_i)` for some `j` (so `ζ_i` and every code below it are own relative to `β`; no
divisibility of `β` is asked).

* `rwF_data` (`1 ≤ f < ρ_λ`, `W^f ∣ X`, `X ≠ 0`, `X < ψ_{Ω₃}(0)`, `X̂ < ψ_{Ω₂}(0)`), `rvEE_mono_base`,
  `rwF_mono` (**hereditary**: `β ≤ β'` keeps the family);
* `rwFamE` (as `Rv.rvFamE` with the bound `ζ < EE_j(X₀, β, e)` in place of `ζ < T_{X₀+W^{e+1}}(β)` and a
  divisible base);
* `rwF_sh` (**every member is a shift own relative to `β` with the top law at the bases `≥ β`**), `rwShF`
  (the family `∃ f, RwF β X X̂ f`), `rwShF_sh`, `rwShF_mono`.

No new axiom.  New definitions: `RwF`, `rwShF`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv

variable {S : InaccSeq.{0}}

/-- **The family of the shifts with exponents below `ρ_λ` over the base `β`** (last level `f`). -/
inductive RwF (S : InaccSeq.{0}) (l : Ordinal.{0}) : Ordinal.{0} → Ordinal.{0} → Ordinal.{0} → Ordinal.{0} → Prop
  | one {β f ζ : Ordinal.{0}} : 1 ≤ f → f < upsilon l → GxCl (upsilon l) (ldAtR S l) ζ → ζ ≠ 0 →
      gxTh (upsilon l) (ldAtR S l) ζ < Om 1 → (∃ j, ζ < rvEE S 0 β f j) →
      RwF S l β (leWe f * ζ) (leOe f * gxTh (upsilon l) (ldAtR S l) ζ) f
  | add {β X0 Xh0 f0 f ζ : Ordinal.{0}} : RwF S l β X0 Xh0 f0 → 1 ≤ f → f < f0 →
      GxCl (upsilon l) (ldAtR S l) ζ → ζ ≠ 0 → gxTh (upsilon l) (ldAtR S l) ζ < Om 1 →
      (∃ j, ζ < rvEE S X0 β f j) →
      RwF S l β (X0 + leWe f * ζ) (Xh0 + leOe f * gxTh (upsilon l) (ldAtR S l) ζ) f

/-- The family `∃ f, RwF β X X̂ f`. -/
def rwShF (S : InaccSeq.{0}) (l b X Xh : Ordinal.{0}) : Prop := ∃ f, RwF S l b X Xh f

theorem rwG3_SC : SC (S.psi 0 (Om (1 + 1 + 1))) := SC_psi (InR_Om_succ (1 + 1)) 0
theorem rwW_lt_G3 : Om (1 + 1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1 + 1)) := (psiS_bounds (S := S) 0 (1 + 1)).1
theorem rwG_SC : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
theorem rwO_lt_G : Om (1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1)) := (psiS_bounds (S := S) 0 1).1

/-- `W^f·ζ < ψ_{Ω₃}(0)` and `Ω^f·y < ψ_{Ω₂}(0)` for countable `f`, `y` and `ζ < Ω₂`. -/
theorem rwTerm_lt {f ζ y : Ordinal.{0}} (hf : f < Om 1) (hζ : ζ < Om (1 + 1)) (hy : y < Om 1) :
    leWe f * ζ < S.psi 0 (Om (1 + 1 + 1)) ∧ leWe (f + 1) < S.psi 0 (Om (1 + 1 + 1)) ∧
      leOe f * y < S.psi 0 (Om (1 + 1)) ∧ leOe (f + 1) < S.psi 0 (Om (1 + 1)) := by
  have hG3 := rwG3_SC (S := S)
  have hWG3 := rwW_lt_G3 (S := S)
  have hG1 := rwG_SC (S := S)
  have hΩG1 := rwO_lt_G (S := S)
  have hf1 : f + 1 < Om 1 := Ph.ph_SC_Om1.isSuccLimit.succ_lt hf
  have hfG3 : ∀ x, x < Om 1 → x < S.psi 0 (Om (1 + 1 + 1)) := fun x hx =>
    (hx.trans gg_Om1_lt_Om2).trans hWG3
  refine ⟨ldMul_lt_SC hG3 (leWe_lt_SC hG3 hWG3 (hfG3 f hf)).1 (hζ.trans hWG3),
    (leWe_lt_SC hG3 hWG3 (hfG3 _ hf1)).1,
    ldMul_lt_SC hG1 (leOe_lt_SC hG1 hΩG1 (hf.trans hΩG1)).1 (hy.trans hΩG1),
    (leOe_lt_SC hG1 hΩG1 (hf1.trans hΩG1)).1⟩

/-- **The data of a member.** -/
theorem rwF_data {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    {β X Xh f : Ordinal.{0}} (h : RwF S l β X Xh f) :
    1 ≤ f ∧ f < upsilon l ∧ leWe f ∣ X ∧ X ≠ 0 ∧ X < S.psi 0 (Om (1 + 1 + 1)) ∧
      Xh < S.psi 0 (Om (1 + 1)) := by
  obtain ⟨-, hρ1⟩ := leRho hl hX
  have hG3 := rwG3_SC (S := S)
  have hG1 := rwG_SC (S := S)
  induction h with
  | @one f ζ h1 hfρ hζ hζ0 hΘ hj =>
    obtain ⟨j, hj⟩ := hj
    obtain ⟨t1, -, t3, -⟩ := rwTerm_lt (S := S) (hfρ.trans hρ1) (hj.trans (rvEE_lt_Om2 j)) hΘ
    exact ⟨h1, hfρ, dvd_mul_right _ _, mul_ne_zero (leWe_pos f).ne' hζ0, t1, t3⟩
  | @add X0 Xh0 f0 f ζ h0 h1 hff hζ hζ0 hΘ hj ih =>
    obtain ⟨-, hf0ρ, hd0, -, hX0, hXh0⟩ := ih
    obtain ⟨j, hj⟩ := hj
    obtain ⟨t1, -, t3, -⟩ := rwTerm_lt (S := S) ((hff.trans hf0ρ).trans hρ1) (hj.trans (rvEE_lt_Om2 j)) hΘ
    refine ⟨h1, hff.trans hf0ρ, dvd_add ((leWe_dvd hff.le).trans hd0) (dvd_mul_right _ _), ?_,
      hG3.isPrincipal hX0 t1, hG1.isPrincipal hXh0 t3⟩
    intro h
    have := le_antisymm (h ▸ le_add_self : leWe f * ζ ≤ 0) zero_le
    exact mul_ne_zero (leWe_pos f).ne' hζ0 this

/-- `EE_j` grows with the base. -/
theorem rvEE_mono_base {X0 β β' f : Ordinal.{0}} (hββ : β ≤ β') :
    ∀ j, rvEE S X0 β f j ≤ rvEE S X0 β' f j
  | 0 => le_rfl
  | j + 1 => (psi_mono (S := S) (InR_Om_succ 1) (add_le_add hββ (leWe_mono ((add_le_add_iff_left X0).2
      (leMulWe_mono (rvEE_mono_base hββ j)))))).1

/-- **The family is hereditary.** -/
theorem rwF_mono {l β β' X Xh f : Ordinal.{0}} (hββ : β ≤ β') (h : RwF S l β X Xh f) : RwF S l β' X Xh f := by
  induction h with
  | @one f ζ h1 hfρ hζ hζ0 hΘ hj =>
    obtain ⟨j, hj⟩ := hj
    exact RwF.one h1 hfρ hζ hζ0 hΘ ⟨j, hj.trans_le (rvEE_mono_base hββ j)⟩
  | @add X0 Xh0 f0 f ζ h0 h1 hff hζ hζ0 hΘ hj ih =>
    obtain ⟨j, hj⟩ := hj
    exact RwF.add ih h1 hff hζ hζ0 hΘ ⟨j, hj.trans_le (rvEE_mono_base hββ j)⟩

theorem rwShF_mono {l b b' X Xh : Ordinal.{0}} (hbb : b ≤ b') (h : rwShF S l b X Xh) : rwShF S l b' X Xh := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, rwF_mono hbb hf⟩

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  {e : Ordinal.{0}} (he1 : 1 ≤ e) (heρ : e < upsilon l) (IH : RvLevSE S l e)

include hl hX he1 heρ IH

/-- **The level-`e` family over `β` with the bound `ζ < EE_j(X₀, β, e)`.** -/
theorem rwFamE {X0 Xh0 β : Ordinal.{0}} (hoff : RvOff S l β X0 Xh0) (hd : leWe (e + 1) ∣ X0)
    (hG3 : X0 + leWe (e + 1) + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)))
    (hG : Xh0 + leOe (e + 1) + Om 1 < S.psi 0 (Om (1 + 1))) :
    ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → (∃ j, ζ < rvEE S X0 β e j) →
      gxTh (upsilon l) (ldAtR S l) ζ < Om 1 →
      RvOff S l β (X0 + leWe e * ζ) (Xh0 + leOe e * gxTh (upsilon l) (ldAtR S l) ζ) := by
  have hk0 : leWe e ≠ 0 := (leWe_pos e).ne'
  have hOk0 : leOe e ≠ 0 := (leOe_pos e).ne'
  have hdk : leWe e ∣ X0 := (leWe_dvd le_self_add).trans hd
  have hmem : ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → (∃ j, ζ < rvEE S X0 β e j) →
      gxTh (upsilon l) (ldAtR S l) ζ < Om 1 → ζ ≠ 0 →
      RvSh S l β (X0 + leWe e * ζ) (Xh0 + leOe e * gxTh (upsilon l) (ldAtR S l) ζ) := fun ζ hζ hζT hΘ hζ0 => by
    obtain ⟨j, hj⟩ := hζT
    exact rvSh_me hl hX he1 heρ hoff hζ (hj.trans (rvEE_lt_Om2 j)) (rvEE_gt j ζ hj) hΘ
      (fun h => (mul_ne_zero hk0 hζ0) (le_antisymm (h ▸ le_add_self) zero_le)) hG3 hG
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
    have hT0 : ∃ j, ζ0 < rvEE S X0 β e j := by
      obtain ⟨j, hj⟩ := hζT; exact ⟨j, (lt_add_one ζ0).trans hj⟩
    have hoff0 := IHz ζ0 (lt_add_one ζ0) hζ0c hT0 hΘ0
    have hΘs := rqTh_succ hl hX hζ0c
    have hle1 : leWe e * ζ0 + leWe e ≤ leWe (e + 1) := by
      rw [← mul_add_one]; exact (rvWe_lt_succ hζW).le
    have hle2 : leOe e * gxTh (upsilon l) (ldAtR S l) ζ0 + leOe e ≤ leOe (e + 1) := by
      rw [← mul_add_one, ← hΘs]; exact (rvOe_lt_succ hΘ1).le
    have ht := IH β _ _ hoff0 (dvd_add hdk (dvd_mul_right _ _))
      (lt_of_le_of_lt (add_le_add_left (by rw [add_assoc]; exact (add_le_add_iff_left X0).2 hle1) _) hG3)
      (lt_of_le_of_lt (add_le_add_left (by rw [add_assoc]; exact (add_le_add_iff_left Xh0).2 hle2) _) hG)
    rw [add_assoc, add_assoc, ← mul_add_one, ← mul_add_one, ← hΘs] at ht
    exact Or.inr ⟨hmem _ hζ hζT hΘ1 (by simp), ht⟩
  · have hζ0 : ζ ≠ 0 := hlim.ne_bot
    have hs := hmem ζ hζ hζT hΘ1 hζ0
    have hΘpos : 0 < gxTh (upsilon l) (ldAtR S l) ζ := by
      have := gxTh_lt (Z := upsilon l) (At := ldAtR S l) (GxCl.zero (leRho hl hX).1.1) (pos_iff_ne_zero.2 hζ0)
      rwa [gxTh_zero] at this
    have hsub : ∀ c, GxCl (upsilon l) (ldAtR S l) c → c < ζ →
        RvSh S l β (X0 + leWe e * (c + 1)) (Xh0 + leOe e * gxTh (upsilon l) (ldAtR S l) (c + 1)) ∧
        RvTop S l β (X0 + leWe e * (c + 1)) (Xh0 + leOe e * gxTh (upsilon l) (ldAtR S l) (c + 1)) 0 ∧
        gxTh (upsilon l) (ldAtR S l) (c + 1) < gxTh (upsilon l) (ldAtR S l) ζ := by
      intro c hc hcζ
      have hc1 := hlim.succ_lt hcζ
      have hc1c := rqCode_succ hl hX hc (hc1.trans hζW)
      have hΘc : gxTh (upsilon l) (ldAtR S l) (c + 1) < Om 1 := (gxTh_mono hc1.le).trans_lt hΘ1
      have hT1 : ∃ j, c + 1 < rvEE S X0 β e j := by
        obtain ⟨j, hj⟩ := hζT; exact ⟨j, hc1.trans hj⟩
      have h := rvOff_ne (IHz _ hc1 hc1c hT1 hΘc)
        (fun h => (mul_ne_zero hk0 (by simp)) (le_antisymm (h ▸ le_add_self) zero_le))
      exact ⟨h.1, h.2, gxTh_lt hc1c hc1⟩
    refine Or.inr ⟨hs, rvTopLimSh hl hX hs (fun x hxH hx => ?_) (fun z hz => ?_)⟩
    · rcases lt_or_ge x X0 with hxX | hxX
      · have hX00 : X0 ≠ 0 := (zero_le.trans_lt hxX).ne'
        obtain ⟨hs0, ht0⟩ := rvOff_ne hoff hX00
        refine ⟨X0, Xh0, le_self_add, hxX, lt_add_of_pos_right _ (mul_pos (leOe_pos e) hΘpos), hs0, ht0⟩
      · obtain ⟨r, rfl⟩ := exists_add_of_le hxX
        have hr : r < leWe e * ζ := (add_lt_add_iff_left X0).1 hx
        have hrW : r < leWe (e + 1) := hr.trans (rvWe_lt_succ hζW)
        have hrH : r ∈ cdHull S l := by
          have h1 := leModP_mem (S := S) (Om (1 + 1) * (e + 1)) hxH
          have hm : (X0 + r) % ω ^ (Om (1 + 1) * (e + 1)) = r := by
            obtain ⟨q, hq⟩ := hd
            change (X0 + r) % leWe (e + 1) = r
            rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hrW]
          rwa [hm] at h1
        have hq : r / leWe e < ζ := (Ordinal.lt_mul_iff_div_lt hk0).1 hr
        have hqc := (ldHull_iff hl hX (hq.trans hζW)).1
          (leDivOp_mem (dvd_mul_right _ _) hrH (by rw [← mul_add_one]; exact hrW))
        obtain ⟨hs1, ht1, hΘlt⟩ := hsub _ hqc hq
        refine ⟨_, _, ?_, ?_, (add_lt_add_iff_left Xh0).2 ((mul_lt_mul_iff_right₀ (leOe_pos e)).2 hΘlt), hs1, ht1⟩
        · exact (add_le_add_iff_left X0).2 (mul_le_mul_right (Order.add_one_le_of_lt hq) _)
        · refine (add_lt_add_iff_left X0).2 ?_
          rw [mul_add_one]; exact Ordinal.lt_mul_div_add r hk0
    · rcases lt_or_ge z Xh0 with hzX | hzX
      · have hXh00 : Xh0 ≠ 0 := (zero_le.trans_lt hzX).ne'
        obtain ⟨hs0, ht0⟩ := rvOff_neh hoff hXh00
        exact ⟨X0, Xh0, lt_add_of_pos_right _ (mul_pos (leWe_pos e) (pos_iff_ne_zero.2 hζ0)), hzX, hs0, ht0⟩
      · obtain ⟨u, rfl⟩ := exists_add_of_le hzX
        have hu : u < leOe e * gxTh (upsilon l) (ldAtR S l) ζ := (add_lt_add_iff_left Xh0).1 hz
        have hq : u / leOe e < gxTh (upsilon l) (ldAtR S l) ζ := (Ordinal.lt_mul_iff_div_lt hOk0).1 hu
        obtain ⟨c, hc, hcζ, hcz⟩ := gxTh_onto hq
        obtain ⟨hs1, ht1, -⟩ := hsub c hc hcζ
        refine ⟨_, _, (add_lt_add_iff_left X0).2 ((mul_lt_mul_iff_right₀ (leWe_pos e)).2 (hlim.succ_lt hcζ)), ?_,
          hs1, ht1⟩
        refine (add_lt_add_iff_left Xh0).2 ?_
        rw [rqTh_succ hl hX hc, hcz, mul_add_one]; exact Ordinal.lt_mul_div_add u hOk0

end Main

section Sh

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **Every member is a shift own relative to `β` with the top law at the bases `≥ β`.** -/
theorem rwF_sh {β X Xh f : Ordinal.{0}} (h : RwF S l β X Xh f) : RvSh S l β X Xh ∧ RvTop S l β X Xh 0 := by
  obtain ⟨-, hρ1⟩ := leRho hl hX
  have hG3 := rwG3_SC (S := S)
  have hWG3 := rwW_lt_G3 (S := S)
  have hG1 := rwG_SC (S := S)
  have hΩG1 := rwO_lt_G (S := S)
  induction h with
  | @one f ζ h1 hfρ hζ hζ0 hΘ hj =>
    obtain ⟨-, t2, -, t4⟩ := rwTerm_lt (S := S) (hfρ.trans hρ1) gg_Om1_lt_Om2 hΘ
    have h := rwFamE hl hX h1 hfρ (rvLevE_all hl hX f h1 hfρ) (Or.inl ⟨rfl, rfl⟩) (dvd_zero _)
      (by rw [zero_add]; exact hG3.isPrincipal t2 hWG3) (by rw [zero_add]; exact hG1.isPrincipal t4 hΩG1)
      ζ hζ hj hΘ
    rw [zero_add, zero_add] at h
    exact rvOff_ne h (mul_ne_zero (leWe_pos f).ne' hζ0)
  | @add X0 Xh0 f0 f ζ h0 h1 hff hζ hζ0 hΘ hj ih =>
    obtain ⟨-, hf0ρ, hd0, -, hX0, hXh0⟩ := rwF_data hl hX h0
    have hfρ := hff.trans hf0ρ
    obtain ⟨-, t2, -, t4⟩ := rwTerm_lt (S := S) (hfρ.trans hρ1) gg_Om1_lt_Om2 hΘ
    have h := rwFamE hl hX h1 hfρ (rvLevE_all hl hX f h1 hfρ) (Or.inr ih)
      ((leWe_dvd (Order.add_one_le_of_lt hff)).trans hd0)
      (hG3.isPrincipal (hG3.isPrincipal hX0 t2) hWG3) (hG1.isPrincipal (hG1.isPrincipal hXh0 t4) hΩG1)
      ζ hζ hj hΘ
    refine rvOff_ne h ?_
    intro h'
    have := le_antisymm (h' ▸ le_add_self : leWe f * ζ ≤ 0) zero_le
    exact mul_ne_zero (leWe_pos f).ne' hζ0 this

/-- **The family `rwShF` meets the hypotheses of the own-atom layer.** -/
theorem rwShF_sh : ∀ b X Xh, rwShF S l b X Xh → RvSh S l b X Xh ∧
    ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → RvTop S l b X Xh e := by
  rintro b X Xh ⟨f, hf⟩
  obtain ⟨hs, ht⟩ := rwF_sh hl hX hf
  exact ⟨hs, rvTopE hs hl hX ht⟩

end Sh

end Googology.Trans.PoR.InaccPsi.R2.Rw

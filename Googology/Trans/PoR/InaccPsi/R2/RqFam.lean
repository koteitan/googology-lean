import Googology.Trans.PoR.InaccPsi.R2.RqEM

/-!
# The shifts `X = Ω₂·ξ` with `ξ` a code: one induction over the codes `1 ≤ ξ < EM_j`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ_{Ω₂}(β + W^E)`, `F_ξ = ψ_{Ω₂}(W^{Ω₂·ξ})`,
`EM_j = Rq.rqEM S j` (`EM_0 = Ω₁`, `EM_{j+1} = F_{EM_j}`).

* `rqShC S λ` (**the family `{(Ω₂·ξ, Ω₁·Θ ξ) | ξ a code, 1 ≤ ξ, ξ < EM_j for some j, Θ ξ < Ω₁}`**), `rqSh_c` (its
  members are base-relative shifts);
* `rqTopC` (**`RoTop (Ω₂·ξ) (Ω₁·Θ ξ) 0` for every member**, ONE induction on the code `ξ`: `Rn.rnTopW` at `ξ = 1`,
  the pull-back `Rq.rqTopW` at successors, the limit shift `Rq.rqTopLimSh` at limits; the image of the shift is
  `Ω₁·Θ ξ`, read through the hull), `rqShC_sh`;
* `rqClsC` (**the atoms below `T_{Ω₂·ξ}(β)` are own**, the same induction), `rqRepC`, `rqReadC`
  (**`Θ_λ(ψ_{Ω₂}(c)) = ψ_{Ω₁}(A + 1 + v)`** for every own `(X, e, c, v)` over `0`), `rqTh_C0`
  (**`Θ_λ(F_ξ) = ψ_{Ω₁}(A + 1 + Ω₁^{Ω₁·Θ_λ ξ})`**).

No new axiom.  New definition: `rqShC`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro

variable {S : InaccSeq.{0}}

/-- **The family of code shifts** `{(Ω₂·ξ, Ω₁·Θ ξ) | ξ a code, 1 ≤ ξ < EM_j, Θ ξ < Ω₁}` at `λ`. -/
def rqShC (S : InaccSeq.{0}) (l X Xh : Ordinal.{0}) : Prop :=
  ∃ ξ, GxCl (upsilon l) (ldAtR S l) ξ ∧ 1 ≤ ξ ∧ (∃ j, ξ < rqEM S j) ∧
    gxTh (upsilon l) (ldAtR S l) ξ < Om 1 ∧ X = Om (1 + 1) * ξ ∧ Xh = Om 1 * gxTh (upsilon l) (ldAtR S l) ξ

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

theorem rqTh_succ {ξ : Ordinal.{0}} (hξ : GxCl (upsilon l) (ldAtR S l) ξ) :
    gxTh (upsilon l) (ldAtR S l) (ξ + 1) = gxTh (upsilon l) (ldAtR S l) ξ + 1 := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  rw [gxTh_add hρSC hAt hξ 1, gxTh_small (gg_one_lt_of_SC hρSC).le]

theorem rqCode_succ {ξ : Ordinal.{0}} (hξ : GxCl (upsilon l) (ldAtR S l) ξ) (h : ξ + 1 < Om (1 + 1)) :
    GxCl (upsilon l) (ldAtR S l) (ξ + 1) :=
  (ldHull_iff hl hX h).1 (CSet.succ_mem ((ldHull_iff hl hX ((lt_add_one ξ).trans h)).2 hξ))

theorem rqCode_pred {ξ : Ordinal.{0}} (hξ : GxCl (upsilon l) (ldAtR S l) (ξ + 1)) (h : ξ + 1 < Om (1 + 1)) :
    GxCl (upsilon l) (ldAtR S l) ξ :=
  (ldHull_iff hl hX ((lt_add_one ξ).trans h)).1 (mem_of_add_one_mem ((ldHull_iff hl hX h).2 hξ))

/-- **The members of the family are base-relative shifts.** -/
theorem rqSh_c {ξ : Ordinal.{0}} {j : ℕ} (hξ : GxCl (upsilon l) (ldAtR S l) ξ) (h1 : 1 ≤ ξ)
    (hj : ξ < rqEM S j) (hΘ1 : gxTh (upsilon l) (ldAtR S l) ξ < Om 1) :
    RqSh S l (Om (1 + 1) * ξ) (Om 1 * gxTh (upsilon l) (ldAtR S l) ξ) := by
  have hG3 : SC (S.psi 0 (Om (1 + 1 + 1))) := SC_psi (InR_Om_succ (1 + 1)) 0
  have hWG3 : Om (1 + 1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1 + 1)) := (psiS_bounds (S := S) 0 (1 + 1)).1
  have hG1 : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
  have hΩG1 : Om (1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1)) := (psiS_bounds (S := S) 0 1).1
  have hξW : ξ < Om (1 + 1) := hj.trans (rqEM_lt_Om2 j)
  have hown := rqEM_gt j ξ hj
  have hΘown := gxTh_lt (Z := upsilon l) (At := ldAtR S l) hξ hown
  have hΩC : ∀ a b, Om (1 : Ordinal.{0}) ∈ S.CSet a b := fun a b => CSet.Om_mem (CSet.one_mem a b)
  refine ⟨mul_ne_zero ldOm2_SC.1.ne' (Order.one_le_iff_ne_zero.1 h1), dvd_mul_right _ _,
    rqMulK_mem ldOm2_SC (mxOm2_mem _ _) ((ldHull_iff hl hX hξW).2 hξ),
    rqMulK_mem ldOm2_SC (mxOm2_mem _ _) (CSet.of_lt hown),
    rqMulK_mem Ph.ph_SC_Om1 (hΩC _ _) (CSet.of_lt hΘown), ?_, ?_,
    fun Q hQ hb => LeCl.mulK hQ ldOm2_SC ξ (LeCl.small (hown.trans_le hb)),
    fun Q hQ hb => LeCl.mulK hQ Ph.ph_SC_Om1 _ (LeCl.small (hΘown.trans_le hb))⟩
  · rw [← mul_add_one]
    exact ldMul_lt_SC hG3 hWG3 ((ldOm2_SC.isSuccLimit.succ_lt hξW).trans hWG3)
  · rw [← mul_add_one]
    exact ldMul_lt_SC hG1 hΩG1 ((Ph.ph_SC_Om1.isSuccLimit.succ_lt hΘ1).trans hΩG1)

/-- **`RoTop (Ω₂·ξ) (Ω₁·Θ ξ) 0` for every code `1 ≤ ξ < EM_j` with `Θ ξ < Ω₁`** (one induction on `ξ`). -/
theorem rqTopC : ∀ ξ, GxCl (upsilon l) (ldAtR S l) ξ → 1 ≤ ξ → (∃ j, ξ < rqEM S j) →
    gxTh (upsilon l) (ldAtR S l) ξ < Om 1 →
    RoTop S l (Om (1 + 1) * ξ) (Om 1 * gxTh (upsilon l) (ldAtR S l) ξ) 0 := by
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  intro ξ
  induction ξ using WellFoundedLT.induction with
  | ind ξ IH =>
  intro hξ h1 hj hΘ1
  obtain ⟨j, hj⟩ := hj
  have hξW : ξ < Om (1 + 1) := hj.trans (rqEM_lt_Om2 j)
  rcases zero_or_succ_or_isSuccLimit ξ with h0 | ⟨ξ0, hξ0⟩ | hlim
  · subst h0; exact absurd h1 (by simp)
  · rw [succ_eq_add_one] at hξ0
    subst hξ0
    have hξ0c := rqCode_pred hl hX hξ hξW
    rw [rqTh_succ hl hX hξ0c]
    rcases eq_or_ne ξ0 0 with rfl | h00
    · have h := roTop_one (S := S) hl hX
      rw [Nat.cast_one] at h
      rwa [zero_add, gxTh_zero, zero_add]
    · have hΘ0 : gxTh (upsilon l) (ldAtR S l) ξ0 < Om 1 := (gxTh_mono (lt_add_one ξ0).le).trans_lt hΘ1
      have hj0 : ξ0 < rqEM S j := (lt_add_one ξ0).trans hj
      have h10 : 1 ≤ ξ0 := Order.one_le_iff_ne_zero.2 h00
      have hs := rqSh_c hl hX hξ0c h10 hj0 hΘ0
      have h := rqTopW hs hl hX (rqTopE hs hl hX (IH ξ0 (lt_add_one ξ0) hξ0c h10 ⟨j, hj0⟩ hΘ0))
      rwa [← mul_add_one, ← mul_add_one] at h
  · refine rqTopLimSh hl hX (rqSh_c hl hX hξ h1 hj hΘ1) (fun x hxH hx => ?_) (fun z hz => ?_)
    · have hq : x / Om (1 + 1) < ξ := (Ordinal.lt_mul_iff_div_lt hW0).1 hx
      have hq1 := hlim.succ_lt hq
      have hq1c := rqCode_succ hl hX ((ldHull_iff hl hX (hq.trans hξW)).1 (ldDivK_mem ldOm2_SC hxH))
        (hq1.trans hξW)
      have hΘq : gxTh (upsilon l) (ldAtR S l) (x / Om (1 + 1) + 1) < Om 1 := (gxTh_mono hq1.le).trans_lt hΘ1
      refine ⟨Om (1 + 1) * (x / Om (1 + 1) + 1), Om 1 * gxTh (upsilon l) (ldAtR S l) (x / Om (1 + 1) + 1),
        mul_le_mul_right hq1.le _, ?_, (mul_lt_mul_iff_right₀ (Om_pos one_ne_zero)).2 (gxTh_lt hq1c hq1),
        rqSh_c hl hX hq1c le_add_self (hq1.trans hj) hΘq,
        IH _ hq1 hq1c le_add_self ⟨j, hq1.trans hj⟩ hΘq⟩
      rw [mul_add_one]; exact Ordinal.lt_mul_div_add x hW0
    · have hq : z / Om 1 < gxTh (upsilon l) (ldAtR S l) ξ := (Ordinal.lt_mul_iff_div_lt hΩ0).1 hz
      obtain ⟨c, hc, hcξ, hcz⟩ := gxTh_onto hq
      have hc1 := hlim.succ_lt hcξ
      have hc1c := rqCode_succ hl hX hc (hc1.trans hξW)
      have hΘc : gxTh (upsilon l) (ldAtR S l) (c + 1) < Om 1 := (gxTh_mono hc1.le).trans_lt hΘ1
      refine ⟨Om (1 + 1) * (c + 1), Om 1 * gxTh (upsilon l) (ldAtR S l) (c + 1),
        (mul_lt_mul_iff_right₀ ldOm2_SC.1).2 hc1, ?_, rqSh_c hl hX hc1c le_add_self (hc1.trans hj) hΘc,
        IH _ hc1 hc1c le_add_self ⟨j, hc1.trans hj⟩ hΘc⟩
      rw [rqTh_succ hl hX hc, hcz, mul_add_one]; exact Ordinal.lt_mul_div_add z hΩ0

/-- The members with their top laws at every code. -/
theorem rqShC_sh : ∀ X Xh, rqShC S l X Xh → RqSh S l X Xh ∧
    ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → RoTop S l X Xh e := by
  rintro X Xh ⟨ξ, hξ, h1, ⟨j, hj⟩, hΘ1, rfl, rfl⟩
  have hs := rqSh_c hl hX hξ h1 hj hΘ1
  exact ⟨hs, rqTopE hs hl hX (rqTopC hl hX ξ hξ h1 ⟨j, hj⟩ hΘ1)⟩

/-- **The atoms below `T_{Ω₂·ξ}(β)` are own** for every member. -/
theorem rqClsC : ∀ ξ, GxCl (upsilon l) (ldAtR S l) ξ → 1 ≤ ξ → (∃ j, ξ < rqEM S j) →
    gxTh (upsilon l) (ldAtR S l) ξ < Om 1 →
    ∀ β, RoBaseE S l (Om (1 + 1) * ξ) 0 β → RoClsAt S l (rqShC S l) (Om (1 + 1) * ξ) 0 β := by
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  intro ξ
  induction ξ using WellFoundedLT.induction with
  | ind ξ IH =>
  intro hξ h1 hj hΘ1
  obtain ⟨j, hj⟩ := hj
  have hξW : ξ < Om (1 + 1) := hj.trans (rqEM_lt_Om2 j)
  rcases zero_or_succ_or_isSuccLimit ξ with h0 | ⟨ξ0, hξ0⟩ | hlim
  · subst h0; exact absurd h1 (by simp)
  · rw [succ_eq_add_one] at hξ0
    subst hξ0
    have hξ0c := rqCode_pred hl hX hξ hξW
    rcases eq_or_ne ξ0 0 with rfl | h00
    · intro β hb
      rw [zero_add] at hb ⊢
      have hb1 : RoBaseE S l (Om (1 + 1) * ((1 : ℕ) : Ordinal.{0})) 0 β := by rwa [Nat.cast_one]
      have h := roCls_one (Sh := rqShC S l) hl hX hb1
      rwa [Nat.cast_one] at h
    · have hΘ0 : gxTh (upsilon l) (ldAtR S l) ξ0 < Om 1 := (gxTh_mono (lt_add_one ξ0).le).trans_lt hΘ1
      have hj0 : ξ0 < rqEM S j := (lt_add_one ξ0).trans hj
      have h10 : 1 ≤ ξ0 := Order.one_le_iff_ne_zero.2 h00
      have hsh : rqShC S l (Om (1 + 1) * ξ0) (Om 1 * gxTh (upsilon l) (ldAtR S l) ξ0) :=
        ⟨ξ0, hξ0c, h10, ⟨j, hj0⟩, hΘ0, rfl, rfl⟩
      have h := rqClsW hl hX (rqShC_sh hl hX) hsh
        (rqClsE hl hX (rqShC_sh hl hX) hsh (IH ξ0 (lt_add_one ξ0) hξ0c h10 ⟨j, hj0⟩ hΘ0))
      rwa [← mul_add_one] at h
  · refine rqClsLimSh hl hX (rqShC_sh hl hX) (fun x hxH hx => ?_)
    have hq : x / Om (1 + 1) < ξ := (Ordinal.lt_mul_iff_div_lt hW0).1 hx
    have hq1 := hlim.succ_lt hq
    have hq1c := rqCode_succ hl hX ((ldHull_iff hl hX (hq.trans hξW)).1 (ldDivK_mem ldOm2_SC hxH))
      (hq1.trans hξW)
    have hΘq : gxTh (upsilon l) (ldAtR S l) (x / Om (1 + 1) + 1) < Om 1 := (gxTh_mono hq1.le).trans_lt hΘ1
    refine ⟨Om (1 + 1) * (x / Om (1 + 1) + 1), Om 1 * gxTh (upsilon l) (ldAtR S l) (x / Om (1 + 1) + 1),
      ⟨_, hq1c, le_add_self, ⟨j, hq1.trans hj⟩, hΘq, rfl, rfl⟩, ?_, ?_,
      IH _ hq1 hq1c le_add_self ⟨j, hq1.trans hj⟩ hΘq⟩
    · rw [← mul_add_one]; exact mul_le_mul_right (Order.add_one_le_of_lt hq1) _
    · rw [mul_add_one]; exact Ordinal.lt_mul_div_add x hW0

omit hl hX in
/-- The base `0` of shift `Ω₂·ξ` and exponent `0`. -/
theorem rqBase00 {ξ : Ordinal.{0}} (hξW : ξ < Om (1 + 1)) : RoBaseE S l (Om (1 + 1) * ξ) 0 0 := by
  refine ⟨dvd_zero _, CSet.zero_mem _ _, ?_, fun d _ => CSet.zero_mem _ _, fun e' _ h' => ?_⟩
  · rw [zero_add, add_zero]; exact (roWe_lt_OmW (rqMulW_lt_OmW hξW)).trans_le le_self_add
  · obtain rfl : e' = 0 := le_antisymm h' zero_le
    exact (SC_psi (InR_Om_succ 1) _).1

/-- **Every atom `s ≤ F_ξ` is `≤ ψ_{Ω₂}(0)` or `ψ_{Ω₂}(c)` with `c` own over `0`** (for a member `ξ`). -/
theorem rqRepC {ξ : Ordinal.{0}} {j : ℕ} (hξ : GxCl (upsilon l) (ldAtR S l) ξ) (h1 : 1 ≤ ξ)
    (hj : ξ < rqEM S j) (hΘ1 : gxTh (upsilon l) (ldAtR S l) ξ < Om 1) (s : Ordinal.{0}) (hs : s ∈ ldAtR S l)
    (hsξ : s ≤ S.psi (leWe (Om (1 + 1) * ξ)) (Om (1 + 1))) :
    s ≤ S.psi 0 (Om (1 + 1)) ∨ ∃ X e c v, (X = 0 ∨ ∃ Xh, rqShC S l X Xh) ∧ RoOwn S l (rqShC S l) X e 0 c v ∧
      RoBaseE S l X e 0 ∧ s = S.psi c (Om (1 + 1)) := by
  have hξW : ξ < Om (1 + 1) := hj.trans (rqEM_lt_Om2 j)
  have hsh : rqShC S l (Om (1 + 1) * ξ) (Om 1 * gxTh (upsilon l) (ldAtR S l) ξ) :=
    ⟨ξ, hξ, h1, ⟨j, hj⟩, hΘ1, rfl, rfl⟩
  have hαW : Om (1 + 1) * ξ < Om ω := rqMulW_lt_OmW hξW
  rcases hsξ.lt_or_eq with hlt | rfl
  · have hlt' : s < leTe S (Om (1 + 1) * ξ + 0) 0 := by
      unfold leTe; rwa [add_zero, zero_add]
    rcases rqClsC hl hX ξ hξ h1 ⟨j, hj⟩ hΘ1 0 (rqBase00 hξW) s hs hlt' with h | ⟨X', e', c, v, -, hown, hbo, e1⟩
    · exact Or.inl h
    · rw [zero_add] at e1
      exact Or.inr ⟨X', e', c, v, roOwn_sh hown, hown, hbo, e1⟩
  · obtain ⟨hρSC, -⟩ := leRho hl hX
    have hc0 : GxCl (upsilon l) (ldAtR S l) (0 : Ordinal.{0}) := GxCl.zero hρSC.1
    have hc1 : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small (gg_one_lt_of_SC hρSC)
    have h1T : (1 : Ordinal.{0}) < leTe S (Om (1 + 1) * ξ + 0 + 1) 0 := roOne_lt_Te _ _
    have hXW : Om (1 + 1) ≤ Om (1 + 1) * ξ := le_mul_left _ (Order.one_le_iff_pos.1 h1)
    have hown := roTop_own (l := l) (Sh := rqShC S l) hsh hXW hc0 hc1 one_ne_zero h1T
    have hb : RoBaseE S l (Om (1 + 1) * ξ) (0 + 1) 0 := by
      refine ⟨dvd_zero _, CSet.zero_mem _ _, ?_, fun d _ => CSet.zero_mem _ _, fun e' _ h' => ?_⟩
      · rw [zero_add, zero_add]
        refine (roWe_lt_OmW ((Om_isPrincipal omega0_ne_zero) hαW ?_)).trans_le le_self_add
        exact one_lt_omega0.trans (Lw.lw_omega_lt_SC (SC_Om omega0_ne_zero))
      · rw [zero_add] at h' ⊢
        exact (h'.trans_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC Ph.ph_SC_Om1))).trans
          (psiS_bounds (S := S) _ 1).1
    refine Or.inr ⟨_, _, _, _, Or.inr ⟨_, hsh⟩, hown, hb, ?_⟩
    rw [add_zero, mul_one, add_zero]

/-- **`Θ_λ(ψ_{Ω₂}(c)) = ψ_{Ω₁}(A + 1 + v)`** for every own `(X, e, c, v)` over `0`. -/
theorem rqReadC {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    {X e c v : Ordinal.{0}} (hown : RoOwn S l (rqShC S l) X e 0 c v) (hb : RoBaseE S l X e 0) :
    gxTh (upsilon l) (ldAtR S l) (S.psi c (Om (1 + 1))) = S.psi (A + 1 + v) (Om 1) ∧
      A + 1 + v ∈ S.CSet (A + 1 + v) (S.psi (A + 1 + v) (Om 1)) ∧ v < S.psi 0 (Om (1 + 1)) := by
  have hA1 : A + 1 ∈ S.CSet (A + 1) (S.psi (A + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA) (CSet.one_mem _ _)
  obtain ⟨e1, own1, -, hv⟩ := rqOwnRead hl hX (rqShC_sh hl hX) hown (A + 1) hb hA1 (ldBlk_zero hA hρ)
  rw [zero_add] at e1
  exact ⟨e1, own1, hv⟩

/-- **`Θ_λ(F_ξ) = ψ_{Ω₁}(A + 1 + Ω₁^{Ω₁·Θ_λ ξ})`** for every code `1 ≤ ξ < EM_j` with `Θ_λ ξ < Ω₁`. -/
theorem rqTh_C0 {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    {ξ : Ordinal.{0}} {j : ℕ} (hξ : GxCl (upsilon l) (ldAtR S l) ξ) (h1 : 1 ≤ ξ) (hj : ξ < rqEM S j)
    (hΘ1 : gxTh (upsilon l) (ldAtR S l) ξ < Om 1) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (leWe (Om (1 + 1) * ξ)) (Om (1 + 1))) =
      S.psi (A + 1 + leOe (Om 1 * gxTh (upsilon l) (ldAtR S l) ξ)) (Om 1) := by
  have hA1 : A + 1 ∈ S.CSet (A + 1) (S.psi (A + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA) (CSet.one_mem _ _)
  have hξW : ξ < Om (1 + 1) := hj.trans (rqEM_lt_Om2 j)
  have h := rqTopC hl hX ξ hξ h1 ⟨j, hj⟩ hΘ1 0 (A + 1) (rqBase00 hξW) hA1 (ldBlk_zero hA hρ)
  unfold leTe at h
  rwa [zero_add, add_zero, gxTh_zero, add_zero] at h

end Main

end Googology.Trans.PoR.InaccPsi.R2.Rq

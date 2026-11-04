import Googology.Trans.PoR.InaccPsi.R2.ZdShR
import Googology.Trans.PoR.InaccPsi.R2.ZdTopY3

/-!
# THE ψ₃-OFFSETS BELOW `W^{Y₃+Ω₂·ε₀}`: the chain of relative shifts `Y₃ + Ω₂·ξ`, `ξ < ε₀`

`Y₃ = ugY S`, `Y₂ = ψ_{Ω₂}(Ω₂)`, `W^x = leWe x`, `X'_ξ = zdXr ξ = Y₃ + Ω₂·ξ`, `X̂'_ξ = zdXhr ξ = Y₂ + Ω₁·ξ`, `B_n`,
"window", `A'`, `Yj.YjBase`, "IH(s)" as in `Zd.zdXUp`.  `ZdBot S n λ λ' A' X`: every atom `ψ₂(a) ≤ s < ψ₂(a + W^X)`
over every base `a ≥ Ω₃` with a law at both ends, `W^X ∣ a`, `W^X ∣ B_n a`, moves under IH(s).

* `zdVkA_opowMul` (`ω^p·ξ` is a code of level `k` over every strongly critical `Q`, `ξ < ε₀`),
* `zdRS_chain` (**every `(Y₃ + Ω₂·ξ, Y₂ + Ω₁·ξ)`, `ξ < ε₀`, IS A RELATIVE SHIFT**: the `Vq.VqSh` fields directly,
  the tops by induction on `ξ`: `Vq.vqTopY3E` at `0`, `Vq.vqTopW` at successors, `Vq.vqTopLimSh` at limits, then
  `Vq.vqTopE`),
* `zdBot_chain` (**`ZdBot` at every `Y₃ + Ω₂·ξ`, `ξ ≤ ε₀`**: `0` by `Yt.ytUxMove`, successors by `Zd.zdXUp`, limits by
  continuity of `ξ ↦ W^{Y₃+Ω₂·ξ}`),
* `zdPsi3OffE0` (**every atom `ψ₂(a) ≤ s < ψ₂(a + W^{Y₃+Ω₂·ε₀})` moves** for `Ω₃ ∣ a`, `Ω₃ ∣ B_n a`),
* `zdTopMoveY3E0`, `zdTopMoveChainY3E0` (the same above every top atom of `Ω_{k+3}` and of every `X_ξ`).

No new axiom.  New definitions: `zdXr`, `zdXhr` (abbreviations), `ZdBot` (the statement of the moves below a shift).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Ug
  Googology.Trans.PoR.InaccPsi.R2.Uq Googology.Trans.PoR.InaccPsi.R2.Yj Googology.Trans.PoR.InaccPsi.R2.Yd

variable {S : InaccSeq.{0}}

/-- The relative shift `Y₃ + Ω₂·ξ`. -/
noncomputable def zdXr (S : InaccSeq.{0}) (ξ : Ordinal.{0}) : Ordinal.{0} := ugY S + Om (1 + 1) * ξ

/-- Its image `Y₂ + Ω₁·ξ`. -/
noncomputable def zdXhr (S : InaccSeq.{0}) (ξ : Ordinal.{0}) : Ordinal.{0} :=
  S.psi (Om (1 + 1)) (Om (1 + 1)) + Om 1 * ξ

/-- **The moves below the shift `X`**: every atom `ψ₂(a) ≤ s < ψ₂(a + W^X)` over every base `a ≥ Ω₃` with a law at
both ends, `W^X ∣ a`, `W^X ∣ B_n a`, moves under IH(s). -/
def ZdBot (S : InaccSeq.{0}) (n : ℕ) (l l' A' X : Ordinal.{0}) : Prop :=
  ∀ a D, YjBase S n l l' A' a D → leWe X ∣ a → leWe X ∣ Bc.bcB S n a → Om (1 + 1 + 1) ≤ a →
    ∀ s ∈ ldAtR S l, S.psi a (Om (1 + 1)) ≤ s → s < S.psi (a + leWe X) (Om (1 + 1)) →
    (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)

theorem zdXr_zero : zdXr S 0 = ugY S := by unfold zdXr; rw [mul_zero, add_zero]

theorem zdXhr_zero : zdXhr S 0 = S.psi (Om (1 + 1)) (Om (1 + 1)) := by unfold zdXhr; rw [mul_zero, add_zero]

theorem zdXr_succ (ξ : Ordinal.{0}) : zdXr S (ξ + 1) = zdXr S ξ + Om (1 + 1) := by
  unfold zdXr; rw [mul_add_one]; exact (add_assoc _ _ _).symm

theorem zdXhr_succ (ξ : Ordinal.{0}) : zdXhr S (ξ + 1) = zdXhr S ξ + Om 1 := by
  unfold zdXhr; rw [mul_add_one]; exact (add_assoc _ _ _).symm

theorem zdXr_mono {ξ ξ' : Ordinal.{0}} (h : ξ' ≤ ξ) : zdXr S ξ' ≤ zdXr S ξ := by
  unfold zdXr; exact (add_le_add_iff_left _).2 (mul_le_mul_left' h _)

theorem zdXr_lt {ξ ξ' : Ordinal.{0}} (h : ξ' < ξ) : zdXr S ξ' < zdXr S ξ := by
  unfold zdXr; exact (add_lt_add_iff_left _).2 (mul_lt_mul_of_pos_left h ldOm2_SC.1)

theorem zdXhr_lt {ξ ξ' : Ordinal.{0}} (h : ξ' < ξ) : zdXhr S ξ' < zdXhr S ξ := by
  unfold zdXhr; exact (add_lt_add_iff_left _).2 (mul_lt_mul_of_pos_left h (Om_pos one_ne_zero))

/-- **`ω^p·ξ` is a code of level `k` over every `Q` with `ε₀ ≤ Q`**, for `ξ < ε₀` and `p` such a code. -/
theorem zdVkA_opowMul {k Q p : Ordinal.{0}} (hQ : ε₀ ≤ Q) (hp : VkA k Q p) :
    ∀ ξ, ξ < ε₀ → VkA k Q (ω ^ p * ξ) := by
  have hQ0 : 0 < Q := (epsilon_pos 0).trans_le hQ
  have hnat : ∀ x, VkA k Q x → ∀ m : ℕ, VkA k Q (x * m) := by
    intro x hx m
    induction m with
    | zero => rw [Nat.cast_zero, mul_zero]; exact VkA.small hQ0
    | succ m ih => rw [Nat.cast_succ, mul_add_one]; exact VkA.add ih hx
  intro ξ
  induction ξ using WellFoundedLT.induction with
  | ind ξ IH =>
  intro hξ
  rcases eq_or_ne ξ 0 with rfl | h0
  · rw [mul_zero]; exact VkA.small hQ0
  have hL := Gc.gc_log_lt h0 hξ
  set a := log ω ξ with ha
  obtain ⟨m, hm⟩ := lt_omega0.1 (div_opow_log_lt ξ one_lt_omega0)
  have hdm : ξ = ω ^ a * m + ξ % ω ^ a := by rw [← hm]; exact (Ordinal.div_add_mod ξ _).symm
  have hrlt : ξ % ω ^ a < ξ :=
    (Ordinal.mod_lt ξ (opow_ne_zero _ omega0_ne_zero)).trans_le (opow_log_le_self ω h0)
  have e1 : ω ^ p * ξ = ω ^ (p + a) * m + ω ^ p * (ξ % ω ^ a) := by
    conv_lhs => rw [hdm]
    rw [mul_add, ← mul_assoc, ← opow_add]
  rw [e1]
  have hpa : VkA k Q (ω ^ (p + a)) := by
    rw [← veblen_zero_apply]
    exact VkA.phi (VkA.small hQ0) (VkA.add hp (VkA.small ((hL.trans hξ).trans_le hQ)))
  exact VkA.add (hnat _ hpa m) (IH _ hrlt (hrlt.trans hξ))

theorem zdEps0_le_SC {Q : Ordinal.{0}} (hQ : SC Q) : (ε₀ : Ordinal.{0}) ≤ Q :=
  epsilon_zero_le_of_omega0_opow_le (gg_SC_eps hQ).le

/-- `B_n` fixes `Ω₂·(Y₃ + Ω₂·ξ)` and `Ω₁·(Y₂ + Ω₁·ξ)` for `ξ < ε₀`. -/
theorem zdShB_chain {ξ : Ordinal.{0}} (hξ : ξ < ε₀) : Ro.RoShB S (zdXr S ξ) (zdXhr S ξ) := by
  refine ⟨?_, fun n => ?_⟩
  · unfold zdXhr; exact (Vq.vqY2_SC.1.trans_le le_self_add).ne'
  obtain ⟨hDY, hBY⟩ := Yy.yyY3_D (S := S) (n := n)
  obtain ⟨hDY2, hBY2⟩ := Yy.yyY2_D (S := S) (n := n)
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hD1, hB1⟩ := mvB_Om1 (S := S) (k := n)
  obtain ⟨hDp, hBp⟩ := mvB_add (k := n) hD2 hD2
  rw [hB2] at hBp
  obtain ⟨hDq, hBq⟩ := mvB_add (k := n) hD1 hD1
  rw [hB1] at hBq
  obtain ⟨hDP, hBP⟩ := zdB_opowMul (n := n) hDp hBp ξ hξ
  obtain ⟨hDQ, hBQ⟩ := zdB_opowMul (n := n) hDq hBq ξ hξ
  have e1 : Om (1 + 1) * zdXr S ξ = ugY S + ω ^ (Om (1 + 1) + Om (1 + 1)) * ξ := by
    unfold zdXr; rw [mul_add, zdOm2_mulY, opow_add, gg_SC_eps ldOm2_SC, mul_assoc]
  have e2 : Om 1 * zdXhr S ξ = S.psi (Om (1 + 1)) (Om (1 + 1)) + ω ^ (Om 1 + Om 1) * ξ := by
    unfold zdXhr; rw [mul_add, zdOm1_mulY2, opow_add, gg_SC_eps Ph.ph_SC_Om1, mul_assoc]
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDY hDP
  rw [hBY, hBP] at hBs
  obtain ⟨hDt, hBt⟩ := mvB_add (k := n) hDY2 hDQ
  rw [hBY2, hBQ] at hBt
  rw [e1, e2]
  exact ⟨hDs, hBs, hDt, hBt⟩

theorem zdXr_lt_Om3 {ξ : Ordinal.{0}} (hξ2 : ξ < Om (1 + 1)) : zdXr S ξ < Om (1 + 1 + 1) := by
  have h3 : SC (Om (1 + 1 + 1 : Ordinal.{0})) := SC_Om (add_pos_of_right zero_lt_one _).ne'
  have hm : Om (1 + 1) * ξ < Om (1 + 1 + 1) := by
    refine (mul_lt_mul_of_pos_left hξ2 ldOm2_SC.1).trans ?_
    have h22 : Om (1 + 1 : Ordinal.{0}) * Om (1 + 1) = veblen 0 (Om (1 + 1) + Om (1 + 1)) := by
      rw [veblen_zero_apply, opow_add, gg_SC_eps ldOm2_SC]
    have h23 : Om (1 + 1 : Ordinal.{0}) < Om (1 + 1 + 1) := Om_lt_Om.2 (lt_add_one _)
    rw [h22]; exact h3.2 0 h3.1 _ (h3.isPrincipal h23 h23)
  exact h3.isPrincipal ugY_lt_Om3 hm

/-- **The `Vq.VqSh` fields of `(Y₃ + Ω₂·ξ, Y₂ + Ω₁·ξ)`** at the base `Ω₃`, `ξ < ε₀`, at every restart. -/
theorem zdVqSh_chain {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) {ξ : Ordinal.{0}} (hξ : ξ < ε₀) :
    Vq.VqSh S l A (Om (1 + 1 + 1)) (zdXr S ξ) (zdXhr S ξ) := by
  have hA3 : Om (1 + 1 + 1) < A := Ry.ryOm3_lt.trans_le (Vn.vnA_ge hl hX hA hρ)
  have hξm : ∀ a c : Ordinal.{0}, ξ ∈ S.CSet a c := fun a c => Gc.gc_cst_mem a c ξ hξ
  have hmem : ∀ c b : Ordinal.{0}, Om (1 + 1 + 1) < c → zdXr S ξ ∈ S.CSet c b := fun c b h =>
    CSet.add_mem (Vq.vqY3_mem h) (ldMulK_mem ldOm2_SC (mxOm2_mem _ _) (hξm _ _))
  have hAo : Om ω ≤ A := Vn.vnA_ge hl hX hA hρ
  refine ⟨?_, dvd_add Yy.yyOm2_dvd_Y (dvd_mul_right _ _), hmem _ _ (Ry.ryOm3_lt.trans_le (ConjT.OmW_le_A S _)),
    hmem _ _ (lt_add_of_pos_right _ (leWe_pos _)), ?_, fun Q hQ _ => ?_, fun Q hQ _ => ?_⟩
  · unfold zdXr; exact (uqY_SC.1.trans_le le_self_add).ne'
  · unfold zdXhr
    exact CSet.add_mem (Vq.vqY2_mem ((ldOm2_lt_OmW.trans_le hAo).trans_le le_self_add))
      (ldMulK_mem Ph.ph_SC_Om1 (CSet.Om_mem (CSet.one_mem _ _)) (hξm _ _))
  · unfold zdXr
    have h := zdVkA_opowMul (zdEps0_le_SC hQ) (VkA.big (k := 1 + 1) (Q := Q) le_rfl ldOm2_SC) ξ hξ
    rw [gg_SC_eps ldOm2_SC] at h
    exact VkA.add (VkA.big uqW_lt_Y.le uqY_SC) h
  · unfold zdXhr
    have h := zdVkA_opowMul (zdEps0_le_SC hQ) (VkA.big (k := 1) (Q := Q) le_rfl Ph.ph_SC_Om1) ξ hξ
    rw [gg_SC_eps Ph.ph_SC_Om1] at h
    exact VkA.add (VkA.big (psiS_bounds (S := S) _ 1).1.le Vq.vqY2_SC) h

theorem zdEps0_lt_Om2 : (ε₀ : Ordinal.{0}) < Om (1 + 1) :=
  Gc.gc_eps0_le_Om1.trans_lt (Om_lt_Om.2 (lt_add_one 1))

/-- `x < Y₃ + Ω₂·ξ`, `ξ` a limit, gives `x < Y₃ + Ω₂·ξ'` for some `ξ' < ξ`. -/
theorem zdXr_cof {ξ x : Ordinal.{0}} (hlim : IsSuccLimit ξ) (hx : x < zdXr S ξ) : ∃ ξ' < ξ, x < zdXr S ξ' := by
  have hN : Order.IsNormal (fun ξ : Ordinal.{0} => ugY S + Om (1 + 1) * ξ) :=
    (isNormal_add_right _).comp (isNormal_mul_right ldOm2_SC.1)
  exact (hN.lt_iff_exists_lt hlim).1 hx

theorem zdXhr_cof {ξ x : Ordinal.{0}} (hlim : IsSuccLimit ξ) (hx : x < zdXhr S ξ) : ∃ ξ' < ξ, x < zdXhr S ξ' := by
  have hN : Order.IsNormal (fun ξ : Ordinal.{0} => S.psi (Om (1 + 1)) (Om (1 + 1)) + Om 1 * ξ) :=
    (isNormal_add_right _).comp (isNormal_mul_right (Om_pos one_ne_zero))
  exact (hN.lt_iff_exists_lt hlim).1 hx

theorem zdW_cof {ξ x : Ordinal.{0}} (hlim : IsSuccLimit ξ) (hx : x < leWe (zdXr S ξ)) :
    ∃ ξ' < ξ, x < leWe (zdXr S ξ') := by
  have hN : Order.IsNormal (fun ξ : Ordinal.{0} => ω ^ (Om (1 + 1) * (ugY S + Om (1 + 1) * ξ))) :=
    (isNormal_opow one_lt_omega0).comp ((isNormal_mul_right ldOm2_SC.1).comp
      ((isNormal_add_right _).comp (isNormal_mul_right ldOm2_SC.1)))
  exact (hN.lt_iff_exists_lt hlim).1 hx

section Rst

variable {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hl hX hA hρ

/-- **THE TOPS OF THE CHAIN**: `Rv.RvTop λ Ω₃ (Y₃ + Ω₂·ξ) (Y₂ + Ω₁·ξ) e` for every `ξ < ε₀` and every code `e`. -/
theorem zdTop_chainR : ∀ ξ, ξ < ε₀ → ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) →
    Rv.RvTop S l (Om (1 + 1 + 1)) (zdXr S ξ) (zdXhr S ξ) e := by
  intro ξ
  induction ξ using WellFoundedLT.induction with
  | ind ξ IHξ =>
  intro hξ
  rcases zero_or_succ_or_isSuccLimit ξ with h0 | ⟨ξ', hξ'⟩ | hlim
  · subst h0
    rw [zdXr_zero, zdXhr_zero]
    exact Vq.vqTopY3E hl hX hA hρ (le_refl _)
  · rw [succ_eq_add_one] at hξ'
    subst hξ'
    have hξ'0 : ξ' < ε₀ := (lt_add_one ξ').trans hξ
    have h0 := Vq.vqTopW (zdVqSh_chain hl hX hA hρ hξ'0) hl hX hA hρ (IHξ ξ' (lt_add_one ξ') hξ'0)
    rw [← zdXr_succ, ← zdXhr_succ] at h0
    exact Vq.vqTopE (zdVqSh_chain hl hX hA hρ hξ) hl hX hA hρ h0
  · have hs := zdVqSh_chain hl hX hA hρ hξ
    refine Vq.vqTopE hs hl hX hA hρ (Vq.vqTopLimSh hl hX hA hρ hs (fun x _ hx => ?_) (fun z hz => ?_))
    · obtain ⟨ξ', hξ', hx'⟩ := zdXr_cof hlim hx
      exact ⟨_, _, zdXr_mono hξ'.le, hx', zdXhr_lt hξ', zdVqSh_chain hl hX hA hρ (hξ'.trans hξ),
        IHξ ξ' hξ' (hξ'.trans hξ) 0 (GxCl.zero (leRho hl hX).1.1) ldOm2_SC.1⟩
    · obtain ⟨ξ', hξ', hz'⟩ := zdXhr_cof hlim hz
      exact ⟨_, _, zdXr_lt hξ', hz', zdVqSh_chain hl hX hA hρ (hξ'.trans hξ),
        IHξ ξ' hξ' (hξ'.trans hξ) 0 (GxCl.zero (leRho hl hX).1.1) ldOm2_SC.1⟩

end Rst

/-- **Every `(Y₃ + Ω₂·ξ, Y₂ + Ω₁·ξ)`, `ξ < ε₀`, IS A RELATIVE SHIFT.** -/
theorem zdRS_chain {ξ : Ordinal.{0}} (hξ : ξ < ε₀) : ZdRS S (zdXr S ξ) (zdXhr S ξ) := by
  refine ⟨?_, (zdXr_lt_Om3 (hξ.trans zdEps0_lt_Om2)).trans Ry.ryOm3_lt, fun c b h => ?_, zdShB_chain hξ,
    fun _ _ _ hl hX hA hρ => zdVqSh_chain hl hX hA hρ hξ, fun _ _ _ hl hX hA hρ => zdTop_chainR hl hX hA hρ ξ hξ⟩
  · unfold zdXr; exact (uqY_SC.1.trans_le le_self_add).ne'
  · exact CSet.add_mem (Vq.vqY3_mem h) (ldMulK_mem ldOm2_SC (mxOm2_mem _ _) (Gc.gc_cst_mem _ _ ξ hξ))

section Win

variable {n : ℕ} {l l' A' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
  (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
  (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1))) (hρ' : S.psi A' (Om 1) = upsilon l')

include hR h1 hr hl' hB hA' hρ'

/-- **THE MOVES BELOW EVERY SHIFT `Y₃ + Ω₂·ξ`, `ξ ≤ ε₀`.** -/
theorem zdBot_chain : ∀ ξ, ξ ≤ ε₀ → ZdBot S n l l' A' (zdXr S ξ) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hX, -, -, -, -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  have hl := hR.1
  intro ξ
  induction ξ using WellFoundedLT.induction with
  | ind ξ IHξ =>
  intro hξ
  rcases zero_or_succ_or_isSuccLimit ξ with h0 | ⟨ξ', hξ'⟩ | hlim
  · subst h0
    intro a D hb hdv hdv' ha3 s hs hsa hsT IH
    rw [zdXr_zero, Vq.vqWeY3] at hdv hdv' hsT
    exact Yt.ytUxMove hR h1 hr hl' hB hA' hρ' hb hdv hdv' hs hsa hsT IH
  · rw [succ_eq_add_one] at hξ'
    subst hξ'
    have hξ'0 : ξ' < ε₀ := (lt_add_one ξ').trans_le hξ
    intro a D hb hdv hdv' ha3 s hs hsa hsT IH
    obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
    rw [zdXr_succ] at hdv hdv' hsT
    exact zdXUp hR h1 hr hl' hB hA' hρ' (zdRS_chain hξ'0) (IHξ ξ' (lt_add_one ξ') hξ'0.le) (Om (1 + 1)) hD2 le_rfl
      a D hb hdv (by rw [hB2]; exact hdv') ha3 s hs hsa hsT IH
  · intro a D hb hdv hdv' ha3 s hs hsa hsT IH
    have han : a ∈ S.CSet a (S.psi a (Om (1 + 1))) := by have h := hb.own 0 zero_le; rwa [add_zero] at h
    have hXW : zdXr S ξ < Om ω := (zdXr_lt_Om3 (hξ.trans_lt zdEps0_lt_Om2)).trans Ry.ryOm3_lt
    have haW : a + leWe (zdXr S ξ) < Om ω :=
      vkOmW.1.isPrincipal hb.D_a.2.2 (leWe_lt_SC vkOmW.1 vkOmW.2 hXW).1
    have hsθ : s < ConjT.th S := hsT.trans_le (psi_mono hκ2 haW.le).1
    obtain ⟨d, -, hds, hdn⟩ := vbReach hl hX hs hsθ
    subst hds
    have hdnx : ∀ x, d < x → S.psi d (Om (1 + 1)) < S.psi x (Om (1 + 1)) := fun x h =>
      psi_lt_psi_of_mem hκ2 h ((psi_mono hκ2 h.le).2 hdn)
    have had : a ≤ d := by
      by_contra hc; push Not at hc
      exact absurd (hdnx a hc) (not_lt.2 hsa)
    have hdae : d < a + leWe (zdXr S ξ) := by
      by_contra hc; push Not at hc
      exact absurd ((psi_mono hκ2 hc).1.trans_lt hsT) (lt_irrefl _)
    have hδ : d - a < leWe (zdXr S ξ) := Ry.rySub_lt had hdae
    obtain ⟨ξ', hξ', hδ'⟩ := zdW_cof hlim hδ
    have hle : leWe (zdXr S ξ') ∣ leWe (zdXr S ξ) := leWe_dvd (zdXr_mono hξ'.le)
    refine IHξ ξ' hξ' (hξ'.le.trans hξ) a D hb (hle.trans hdv) (hle.trans hdv') ha3 _ hs hsa ?_ IH
    refine hdnx _ ?_
    have e1 : d = a + (d - a) := (Ordinal.add_sub_cancel_of_le had).symm
    rw [e1]; exact (add_lt_add_iff_left a).2 hδ'

/-- **THE ψ₃-OFFSETS BELOW `W^{Y₃+Ω₂·ε₀}`**: above a base `a ≥ Ω₃` with a law at both ends, `Ω₃ ∣ a`,
`Ω₃ ∣ B_n a`, every atom `ψ₂(a) ≤ s < ψ₂(a + W^{Y₃+Ω₂·ε₀})` moves under IH(s). -/
theorem zdPsi3OffE0 {a D : Ordinal.{0}} (hb : YjBase S n l l' A' a D) (hd3 : Om (1 + 1 + 1) ∣ a)
    (hd3' : Om (1 + 1 + 1) ∣ Bc.bcB S n a) (ha3 : Om (1 + 1 + 1) ≤ a) {s : Ordinal.{0}} (hs : s ∈ ldAtR S l)
    (hsa : S.psi a (Om (1 + 1)) ≤ s) (hsT : s < S.psi (a + leWe (zdXr S ε₀)) (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  have h3 : leWe (zdXr S ε₀) ∣ Om (1 + 1 + 1) := by
    have h := leWe_dvd (zdXr_lt_Om3 (S := S) zdEps0_lt_Om2).le
    rwa [Vn.vnWe_Om3] at h
  exact zdBot_chain hR h1 hr hl' hB hA' hρ' ε₀ le_rfl a D hb (h3.trans hd3) (h3.trans hd3') ha3 s hs hsa hsT IH

/-- **EVERY ATOM `ψ₂(t) ≤ s < ψ₂(t + W^{Y₃+Ω₂·ε₀})` ABOVE EVERY TOP ATOM `t = β + W^{Ω_{k+3}+e}` MOVES** under IH(s). -/
theorem zdTopMoveY3E0 (k : ℕ) {e β : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (hβD : VbD S l β)
    (hbe : Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e β) {s : Ordinal.{0}} (hs : s ∈ ldAtR S l)
    (hst : S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)) ≤ s)
    (hsT : s < S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) + leWe (zdXr S ε₀)) (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  have IHt := fun x hx (hxs : x < S.psi (β + leWe (X + e)) (Om (1 + 1))) => IH x hx (hxs.trans_le hst)
  obtain ⟨hbt, hBt⟩ := yjTopBase hR h1 hr hl' hB hA' hρ' k hec hβD hbe IHt
  obtain ⟨hdv', -⟩ := yjBaseFacts hR h1 hr hl' hB k hec hβD hbe IHt
  have hW : ∀ e', Om (1 + 1 + 1) ∣ leWe (X + e') := fun e' => by
    have h := leWe_dvd ((Yt.ytOm3_le_X k).trans (le_self_add : X ≤ X + e'))
    rwa [Vn.vnWe_Om3] at h
  have hd : Om (1 + 1 + 1) ∣ β + leWe (X + e) := dvd_add ((hW e).trans hbe.1) (hW e)
  have hd' : Om (1 + 1 + 1) ∣ Bc.bcB S n (β + leWe (X + e)) := by
    rw [hBt]; exact dvd_add ((hW _).trans hdv') (hW _)
  have h3 : Om (1 + 1 + 1) ≤ β + leWe (X + e) := by
    have hXle : X ≤ leWe (X + e) := by
      calc X = leWe X := (Vn.vnWe_OmK k).symm
        _ ≤ leWe (X + e) := leWe_mono le_self_add
    exact (Yt.ytOm3_le_X k).trans (hXle.trans le_add_self)
  exact zdPsi3OffE0 hR h1 hr hl' hB hA' hρ' hbt hd hd' h3 hs hst hsT IH

/-- **The same above every top atom `t = β + W^{X_ξ+e}` of the chain `X_ξ = Ω_{k+3} + Ω₂·ξ`** (`ξ < ε₀`). -/
theorem zdTopMoveChainY3E0 (k : ℕ) {ξ : Ordinal.{0}} (hξ : ξ < ε₀) {e β : Ordinal.{0}}
    (hec : GxCl (upsilon l) (ldAtR S l) e) (hβD : VbD S l β) (hbe : Ro.RoBaseE S l (zdX k ξ) e β)
    {s : Ordinal.{0}} (hs : s ∈ ldAtR S l)
    (hst : S.psi (β + leWe (zdX k ξ + e)) (Om (1 + 1)) ≤ s)
    (hsT : s < S.psi (β + leWe (zdX k ξ + e) + leWe (zdXr S ε₀)) (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  set X := zdX k ξ with hXdef
  have hm : ZdMv S X := zdMv_chain k hξ
  have HL : ZdHL S X := zdHL_chain k hξ
  have IHt := fun x hx (hxs : x < S.psi (β + leWe (X + e)) (Om (1 + 1))) => IH x hx (hxs.trans_le hst)
  obtain ⟨hbt, hBt⟩ := zdTopBase hm hR h1 hr hl' hB HL hA' hρ' hec hβD hbe IHt
  obtain ⟨hdv', -⟩ := zdBaseFacts hm hR h1 hr hl' hB hec hβD hbe IHt
  have hW : ∀ e', Om (1 + 1 + 1) ∣ leWe (X + e') := fun e' => by
    have h := leWe_dvd ((zdOm3_le_X k ξ).trans (le_self_add : X ≤ X + e'))
    rwa [Vn.vnWe_Om3] at h
  have hd : Om (1 + 1 + 1) ∣ β + leWe (X + e) := dvd_add ((hW e).trans hbe.1) (hW e)
  have hd' : Om (1 + 1 + 1) ∣ Bc.bcB S n (β + leWe (X + e)) := by
    rw [hBt]; exact dvd_add ((hW _).trans hdv') (hW _)
  have h3 : Om (1 + 1 + 1) ≤ β + leWe (X + e) := by
    have hXle : X ≤ leWe (X + e) := (le_self_add : X ≤ X + e).trans
      ((Ordinal.le_mul_right _ ldOm2_SC.1).trans (Ordinal.right_le_opow _ one_lt_omega0))
    exact (zdOm3_le_X k ξ).trans (hXle.trans le_add_self)
  exact zdPsi3OffE0 hR h1 hr hl' hB hA' hρ' hbt hd hd' h3 hs hst hsT IH

/-- **REFUTE-FIRST point of skPsi3OffHi**: `δ = W^{Y₃+1}·2` over the base `a = Ω₃ + Y₃` (`Y₃ ∣ a`, `W^{Y₃+1} ∤ a`):
`a + δ = Ω₃ + W^{Y₃+1}·2`, so the atom `ψ₂(a + δ)` lies in `[ψ₂(Ω₃), ψ₂(Ω₃ + W^{Y₃+Ω₂·ε₀}))` above the top atom
`Ω₃ = W^{Ω₃+0}`, and it MOVES at every window under IH (`zdTopMoveY3E0` at `k = 0`, `e = 0`, `β = 0`). -/
theorem zdTestPsi3W2 :
    ¬ leWe (ugY S + 1) ∣ Om (1 + 1 + 1) + ugY S ∧
      Om (1 + 1 + 1) + ugY S + leWe (ugY S + 1) * 2 = Om (1 + 1 + 1) + leWe (ugY S + 1) * 2 ∧
      (S.psi (Om (1 + 1 + 1) + leWe (ugY S + 1) * 2) (Om (1 + 1)) ∈ ldAtR S l →
        (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (Om (1 + 1 + 1) + leWe (ugY S + 1) * 2) (Om (1 + 1)) →
          MvD S x ∧ GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
          gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
          gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
        MvD S (S.psi (Om (1 + 1 + 1) + leWe (ugY S + 1) * 2) (Om (1 + 1))) ∧
          Bc.bcB S n (S.psi (Om (1 + 1 + 1) + leWe (ugY S + 1) * 2) (Om (1 + 1))) ∈ ldAtR S l' ∧
          gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n (S.psi (Om (1 + 1 + 1) + leWe (ugY S + 1) * 2) (Om (1 + 1)))) =
            Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1) + leWe (ugY S + 1) * 2) (Om (1 + 1))))) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hW : leWe (ugY S + 1) = ω ^ (ugY S + Om (1 + 1)) := Yy.yyWY1_eq
  have hYW : ugY S < leWe (ugY S + 1) := by
    rw [hW]; conv_lhs => rw [← gg_SC_eps (uqY_SC (S := S))]
    exact (opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_of_pos_right _ ldOm2_SC.1)
  have hW3 : leWe (ugY S + 1) ∣ Om (1 + 1 + 1) := by
    have h := leWe_dvd (Order.add_one_le_of_lt (ugY_lt_Om3 (S := S)))
    rwa [Vn.vnWe_Om3] at h
  have h2 : (1 + 1 : Ordinal.{0}) < Om (1 + 1) :=
    (isSuccLimit_omega0.add_one_lt one_lt_omega0).trans (Lw.lw_omega_lt_SC ldOm2_SC)
  have hab : ugY S + leWe (ugY S + 1) * 2 = leWe (ugY S + 1) * 2 := by
    rw [hW]
    exact Ordinal.add_absorp (by rw [← hW]; exact hYW) (Ordinal.le_mul_left _ (by norm_num))
  refine ⟨fun hd => ?_, by rw [add_assoc, hab], fun hs IH => ?_⟩
  · have hY : leWe (ugY S + 1) ∣ ugY S := (Ordinal.dvd_add_iff hW3).1 hd
    exact absurd (Ordinal.le_of_dvd uqY_SC.1.ne' hY) (not_le.2 hYW)
  · obtain ⟨hX, -, -, -, -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
    have h0c : GxCl (upsilon l) (ldAtR S l) 0 := GxCl.zero (leRho hR.1 hX).1.1
    have hb0 := Xm.xmRB0 (S := S) 0 l (Om_pos one_ne_zero)
    have e0 : (0 : Ordinal.{0}) + leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + 0) = Om (1 + 1 + 1) := by
      rw [zero_add, add_zero, Nat.cast_zero, zero_add]; exact Vn.vnWe_Om3
    have hle : ugY S + 1 + 1 ≤ zdXr S ε₀ := by
      unfold zdXr; rw [add_assoc]
      exact (add_le_add_iff_left _).2 (h2.le.trans (Ordinal.le_mul_left _ (epsilon_pos 0)))
    have hlt : leWe (ugY S + 1) * 2 < leWe (zdXr S ε₀) := by
      refine lt_of_lt_of_le ?_ (leWe_mono hle)
      rw [leWe_succ (ugY S + 1)]
      exact mul_lt_mul_of_pos_left (show (2 : Ordinal.{0}) < Om (1 + 1) by
        rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num]; exact h2) (leWe_pos _)
    have hmem : Om (1 + 1 + 1) + leWe (ugY S + 1) * 2 ∈ S.CSet (Om (1 + 1 + 1) + leWe (zdXr S ε₀))
        (S.psi (Om (1 + 1 + 1) + leWe (zdXr S ε₀)) (Om (1 + 1))) := by
      refine CSet.add_mem (Ry.ryOm3_mem _ _) (leMulWe_mem (CSet.add_mem (Vq.vqY3_mem (lt_add_of_pos_right _
        (leWe_pos _))) (CSet.one_mem _ _)) ?_)
      rw [show (2 : Ordinal.{0}) = ((2 : ℕ) : Ordinal.{0}) by norm_num]; exact Sc.scNat_mem _ _ 2
    have h := zdTopMoveY3E0 hR h1 hr hl' hB hA' hρ' 0 h0c (Xi.xiD_zero l) hb0
      (s := S.psi (Om (1 + 1 + 1) + leWe (ugY S + 1) * 2) (Om (1 + 1))) hs
      (by rw [e0]; exact (psi_mono hκ2 le_self_add).1)
      (by rw [e0]; exact psi_lt_psi_of_mem hκ2 ((add_lt_add_iff_left _).2 hlt) hmem) IH
    exact h

end Win

end Googology.Trans.PoR.InaccPsi.R2.Zd

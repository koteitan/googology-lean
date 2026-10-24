import Googology.Trans.PoR.InaccPsi.R2.SiCnt

/-!
# The commutation of `B_n` with `π` on the countable terms, asking `ϑ` only at uncountable arguments and `π` only
# from `Ω₁·Ω₁` on

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`B_n = Bc.bcB S n`, `c_n = L(n+1) = Bc.bcC S n`, `π_{σ,τ} = pi σ τ` ([W07a] Def 5.1), `Tᵗ[σ] = TB τ σ`,
`ϑᵗ = vt τ`, `σ' = B_n σ`, `τ' = B_n τ`, `Se.SeComm S n σ τ z`: `B_n z ∈ T^{τ'}[σ']` and `π_{σ',τ'}(B_n z) = B_n(π z)`.

* `SiVtU S n β` (a hypothesis name): **`B_n(ϑ^β(η)) = ϑ^{B_n β}(B_n η)` for `η ∈ T^β ∩ [Ω₁, Ω₂)`**;
  `siVtHom_of` (**`SiVtU S n β ⇒ Se.SeVtHom S n β`** for an `ε`-number `β < c_{n+1}`: the countable arguments are
  `Si.siVtHomC`);
* `siOm1_mul_lt` (`Ω₁·b ∈ Tᵗ[σ]`, `π(Ω₁·b) = Ω₁·b` for `b < σ`), `siOm1_mul_TB` (**`π(Ω₁·b) = Ω₁·π(b)`** for
  `b ∈ Tᵗ[σ] ∩ Ω₁`), `siArg` (**every `ξ ∈ Tᵗ[σ] ∩ [Ω₁, Ω₁·Ω₁)` is `Ω₁·b + e` with `b, e ∈ Tᵗ[σ] ∩ Ω₁`, and
  `π ξ = Ω₁·π b + π e`**: by the surjectivity of `π`, [W07a] Lemma 5.3 (d));
* `siUncLow` (**`SeComm` at `Ω₁·b + e` from `SeComm` at `b` and `e`**);
* `siArgLow` (**`SeComm` at `ξ = Ω₁·b + e < Ω₁·Ω₁` from `SeComm` at the countable terms below `ϑᵗ(ξ)`**: `b, e <
  ϑᵗ(ξ)` by [W07a] Lemma 3.30 (`lvLevel_lt_vt`, `luLt_vt_self`));
* `siComm_gen` (**THE JOINT INDUCTION, generic: under `SiVtU` at `τ` and `σ`, if each uncountable argument `ξ` has
  `SeComm` once the countable terms below `ϑᵗ(ξ)` have it, then `SeComm` holds at every `z ∈ Tᵗ[σ] ∩ Ω₁`**; arguments
  `ξ < Ω₁` by `Si.siVtHomC`);
* `SiUncH S n σ τ` (a hypothesis name): the clause `Se.SeUnc` only at `ξ ∈ Tᵗ[σ] ∩ [Ω₁·Ω₁, Ω₂)`; `siComm_all`
  (`siComm_gen` with `siArgLow` and `SiUncH`), `siUnc_of` (**`SiUncH ⇒ Se.SeUnc`**);
* `SiPiHom S` (a hypothesis name: `Se.SePiHom2` with `SiVtU` and `SiUncH` in place of `SeVtHom` and `SeUnc`),
  `siPiHom_iff` (**`SiPiHom S ↔ Se.SePiHom2 S`**), `siPiComm` (`⇒ Rt.RtPiComm`), `siLhTopE` (`⇒ Rk.RkLhTopE`),
  `siLhEps` (`⇒ Tp.TpLhEps`), `siRoadE_nu` (the road `Se.seRoadE_nuHom2` with `SiPiHom`).

No new axiom.  New definitions: the hypothesis names `SiVtU`, `SiUncH`, `SiPiHom`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Si

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2

variable {S : InaccSeq.{0}}

/-! ## `ϑ` at the uncountable arguments -/

/-- **`B_n` commutes with `ϑ^β` on the uncountable arguments `η ∈ T^β ∩ [Ω₁, Ω₂)`** (a hypothesis name). -/
def SiVtU (S : InaccSeq.{0}) (n : ℕ) (β : Ordinal.{0}) : Prop :=
  ∀ η ∈ Tset β, Om1 ≤ η → η < OmTwo → Bc.bcB S n (vt β η) = vt (Bc.bcB S n β) (Bc.bcB S n η)

/-- `T^β ∩ Ω₁` lies below `c_{n+1}` for an `ε`-number `β < c_{n+1}`. -/
theorem si_T_lt_c {n : ℕ} {β w : Ordinal.{0}} (hβ : InE β) (hβc : β < Bc.bcC S (n + 1)) (hw : w ∈ Tset β)
    (hw1 : w < Om1) : w < Bc.bcC S (n + 1) := by
  obtain ⟨m, -, -, hmin, hmT, -⟩ := T_next (Or.inr hβ) (Rt.rt_lt_Om1 hβc).1
  exact ((hmT w hw1).1 hw).trans_le (hmin _ hβc (Rt.rt_c_inf (n + 1)))

/-- **`SiVtU` gives `Se.SeVtHom`**: the countable arguments are `siVtHomC`. -/
theorem siVtHom_of {n : ℕ} {β : Ordinal.{0}} (hβ : InE β) (hβc : β < Bc.bcC S (n + 1)) (h : SiVtU S n β) :
    Se.SeVtHom S n β := by
  intro η hη hη2
  rcases lt_or_ge η Om1 with hη1 | hη1
  · exact siVtHomC hβ hβc (si_T_lt_c hβ hβc hη hη1)
  · exact h η hη hη1 hη2

/-! ## The arguments `Ω₁·b + e` -/

/-- `Ω₁·b ∈ Tᵗ[σ]` and `π_{σ,τ}(Ω₁·b) = Ω₁·b` for `b < σ` (sums of `Ω₁·ω^g`, `g < σ`: `luOm1_opow_TB`, `pi_add`). -/
theorem siOm1_mul_lt {σ τ : Ordinal.{0}} (h : Bases σ τ) :
    ∀ b, b < σ → Om1 * b ∈ TB τ σ ∧ pi σ τ (Om1 * b) = Om1 * b := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hb
  rcases eq_or_ne b 0 with rfl | hb0
  · rw [mul_zero]
    have h0σ : (0 : Ordinal.{0}) < σ := si_inE_pos h.1
    exact ⟨mem_TB_of_lt h h0σ, pi_lt h h0σ⟩
  have hwg : ω ^ log ω b ≤ b := opow_log_le_self ω hb0
  have hbr : ω ^ log ω b + (b - ω ^ log ω b) = b := Ordinal.add_sub_cancel_of_le hwg
  have hrb : b - ω ^ log ω b < b := Ph.ph_sub_log_lt hb0
  have hgσ : log ω b < σ := ((right_le_opow _ one_lt_omega0).trans hwg).trans_lt hb
  obtain ⟨h1T, h1π⟩ := luOm1_opow_TB h hgσ
  obtain ⟨h2T, h2π⟩ := IH _ hrb (hrb.trans hb)
  obtain ⟨hsT, hsπ⟩ := pi_add h h1T h2T
  have e : Om1 * b = Om1 * ω ^ log ω b + Om1 * (b - ω ^ log ω b) := by
    conv_lhs => rw [← hbr]
    rw [mul_add]
  rw [e]
  exact ⟨hsT, by rw [hsπ, h1π, h2π]⟩

/-- **`Ω₁·b ∈ Tᵗ[σ]` and `π_{σ,τ}(Ω₁·b) = Ω₁·π_{σ,τ}(b)`** for `b ∈ Tᵗ[σ] ∩ Ω₁` (`b < τ`: `siOm1_mul_lt`;
`b ≥ τ`: `lvPi_mul`). -/
theorem siOm1_mul_TB {σ τ b : Ordinal.{0}} (h : Bases σ τ) (hb : b ∈ TB τ σ) (hb1 : b < Om1) :
    Om1 * b ∈ TB τ σ ∧ pi σ τ (Om1 * b) = Om1 * pi σ τ b := by
  rcases lt_or_ge b τ with hbτ | hτb
  · have hbσ : b < σ := (TB_inter_lt h hbτ).1 hb
    rw [pi_lt h hbσ]; exact siOm1_mul_lt h b hbσ
  · exact lvPi_mul h hb hτb hb1

/-- **Every `ξ ∈ Tᵗ[σ] ∩ [Ω₁, Ω₁·Ω₁)` is `Ω₁·b + e` with `b, e ∈ Tᵗ[σ] ∩ Ω₁`, `1 ≤ b`, and `π ξ = Ω₁·π b + π e`**:
`π ξ = Ω₁·b̄ + ē` in `T^σ` (`lgQuot_mem`, `vzRem_T`), `b̄ = π b`, `ē = π e` (`π` is onto, [W07a] Lemma 5.3 (d)),
and `π(Ω₁·b + e) = π ξ` gives `Ω₁·b + e = ξ` (`π` is injective). -/
theorem siArg {σ τ ξ : Ordinal.{0}} (h : Bases σ τ) (hξ : ξ ∈ TB τ σ) (hξ1 : Om1 ≤ ξ) (hξ2 : ξ < Om1 * Om1) :
    ∃ b e, b ∈ TB τ σ ∧ b < Om1 ∧ 1 ≤ b ∧ e ∈ TB τ σ ∧ e < Om1 ∧ ξ = Om1 * b + e ∧
      pi σ τ ξ = Om1 * pi σ τ b + pi σ τ e := by
  have hσE : InE σ := h.1
  have hσ1 : σ < Om1 := h.2.2.1.trans h.2.2.2
  obtain ⟨hbij, hmono⟩ := pi_bijOn h
  obtain ⟨hOT, hOπ⟩ := pi_Om1 h
  obtain ⟨hOOT, hOOπ⟩ := lgPi_OmOm h
  have hπge : Om1 ≤ pi σ τ ξ := by rw [← hOπ]; exact (hmono.le_iff_le hOT hξ).2 hξ1
  have hπlt : pi σ τ ξ < Om1 * Om1 := by rw [← hOOπ]; exact hmono hξ hOOT hξ2
  have hπT : pi σ τ ξ ∈ Tset σ := hbij.mapsTo hξ
  obtain ⟨hdec, hr1⟩ := vz_div_Om1 (pi σ τ ξ)
  have hq1 : pi σ τ ξ / Om1 < Om1 := (Ordinal.lt_mul_iff_div_lt Rj.rj_Om1_pos.ne').1 hπlt
  have hy2 : pi σ τ ξ < OmTwo := by rw [← hdec]; exact lkcMul_lt hq1 hr1
  have hqT : pi σ τ ξ / Om1 ∈ Tset σ := lgQuot_mem hσE hσ1 hπT hπlt
  have hrT : pi σ τ ξ % Om1 ∈ Tset σ := vzRem_T hσE hσ1 hπT hy2 hdec.symm (dvd_mul_right _ _) hr1
  have hpre : ∀ w ∈ Tset σ, w < Om1 → ∃ v, v ∈ TB τ σ ∧ v < Om1 ∧ pi σ τ v = w := by
    intro w hw hw1
    obtain ⟨v, hv, hvw⟩ := hbij.surjOn hw
    refine ⟨v, hv, ?_, hvw⟩
    by_contra hv1
    push Not at hv1
    have h' : pi σ τ Om1 ≤ pi σ τ v := (hmono.le_iff_le hOT hv).2 hv1
    rw [hOπ, hvw] at h'
    exact absurd hw1 (not_lt.2 h')
  obtain ⟨e, heT, he1, heπ⟩ := hpre _ hrT hr1
  obtain ⟨b, hbT, hb1, hbπ⟩ := hpre _ hqT hq1
  obtain ⟨hmT, hmπ⟩ := siOm1_mul_TB h hbT hb1
  obtain ⟨hsT, hsπ⟩ := pi_add h hmT heT
  have hsum : pi σ τ (Om1 * b + e) = pi σ τ ξ := by rw [hsπ, hmπ, hbπ, heπ, hdec]
  have hξeq : Om1 * b + e = ξ := hbij.injOn hsT hξ hsum
  refine ⟨b, e, hbT, hb1, ?_, heT, he1, hξeq.symm, ?_⟩
  · rcases eq_or_ne b 0 with hb0 | hb0
    · rw [hb0, mul_zero, zero_add] at hξeq
      exact absurd (hξeq ▸ he1) (not_lt.2 hξ1)
    · exact one_le_iff_ne_zero.2 hb0
  · rw [← hξeq, hsπ, hmπ]

/-- **`SeComm` at `Ω₁·b + e` from `SeComm` at `b` and `e`** (`b, e ∈ Tᵗ[σ] ∩ Ω₁`, `τ < c_{n+1}`), with `B_n` and `π`
of `Ω₁·b + e` below `Ω₂`: `B_n(Ω₁·b + e) = Ω₁·B_n b + B_n e` (`Rk.rkB_Om1mul`, `Mv.mvB_add`), `siOm1_mul_TB` at
both pairs of bases, `pi_add`. -/
theorem siUncLow {n : ℕ} {σ τ b e : Ordinal.{0}} (h : Bases σ τ) (hτc : τ < Bc.bcC S (n + 1))
    (hbT : b ∈ TB τ σ) (hb1 : b < Om1) (heT : e ∈ TB τ σ) (he1 : e < Om1)
    (hb : Se.SeComm S n σ τ b) (he : Se.SeComm S n σ τ e) :
    Bc.bcB S n (Om1 * b + e) < OmTwo ∧ pi σ τ (Om1 * b + e) < OmTwo ∧ Se.SeComm S n σ τ (Om1 * b + e) := by
  have hσc : σ < Bc.bcC S (n + 1) := h.2.2.1.trans hτc
  have hLc : Bc.bcC S (n + 1) < Nc.ncL S ω := Se.seC_lt_L n
  have hcS : SC (Bc.bcC S (n + 1)) := Lw.lw_L_SC S _
  have hB' := Se.seBases_img h hτc
  have hbc : b < Bc.bcC S (n + 1) := si_T_lt_c h.2.1 hτc hbT.1 hb1
  have hec : e < Bc.bcC S (n + 1) := si_T_lt_c h.2.1 hτc heT.1 he1
  have hπb1 : pi σ τ b < Om1 := down_lt_Om1 h hbT hb1
  have hπe1 : pi σ τ e < Om1 := down_lt_Om1 h heT he1
  have hπbc : pi σ τ b < Bc.bcC S (n + 1) := si_T_lt_c h.1 hσc ((pi_bijOn h).1.mapsTo hbT) hπb1
  have hπec : pi σ τ e < Bc.bcC S (n + 1) := si_T_lt_c h.1 hσc ((pi_bijOn h).1.mapsTo heT) hπe1
  -- `B_n(Ω₁·y + w) = Ω₁·B_n y + B_n w` below `c_{n+1}`
  have hBlin : ∀ y w, y < Bc.bcC S (n + 1) → w < Bc.bcC S (n + 1) →
      Bc.bcB S n (Om1 * y + w) = Om1 * Bc.bcB S n y + Bc.bcB S n w := by
    intro y w hy hw
    obtain ⟨hD1, hB1⟩ := Rk.rkB_Om1mul (n := n) hcS (Bc.bcC_lt S (n + 1)) y (Gg.GgCl.small hy)
    rw [← Rj.rj_Om1] at hD1 hB1
    rw [(Mv.mvB_add (k := n) hD1 (Mv.mvD_of_lt (hw.trans hLc))).2, hB1]
  obtain ⟨hbT', hbπ⟩ := hb
  obtain ⟨heT', heπ⟩ := he
  have hBb1 : Bc.bcB S n b < Om1 := (Rt.rt_lt_Om1 hbc).2
  have hBe1 : Bc.bcB S n e < Om1 := (Rt.rt_lt_Om1 hec).2
  obtain ⟨hmT', hmπ'⟩ := siOm1_mul_TB hB' hbT' hBb1
  obtain ⟨hsT', hsπ'⟩ := pi_add hB' hmT' heT'
  obtain ⟨hmT, hmπ⟩ := siOm1_mul_TB h hbT hb1
  have hsπ := (pi_add h hmT heT).2
  rw [hmπ] at hsπ
  refine ⟨by rw [hBlin b e hbc hec]; exact lkcMul_lt hBb1 hBe1, by rw [hsπ]; exact lkcMul_lt hπb1 hπe1, ?_, ?_⟩
  · rw [hBlin b e hbc hec]; exact hsT'
  · rw [hBlin b e hbc hec, hsπ', hmπ', hbπ, heπ, hsπ, hBlin _ _ hπbc hπec]

/-! ## The joint induction -/

/-- **`B_n` commutes with the base changes on `Tᵗ[σ] ∩ [Ω₁·Ω₁, Ω₂)`**, and `B_n ξ`, `π ξ` stay below `Ω₂`
(a hypothesis name: the clause `Se.SeUnc` from `Ω₁·Ω₁` on). -/
def SiUncH (S : InaccSeq.{0}) (n : ℕ) (σ τ : Ordinal.{0}) : Prop :=
  ∀ ξ ∈ TB τ σ, Om1 * Om1 ≤ ξ → ξ < OmTwo →
    Bc.bcB S n ξ < OmTwo ∧ pi σ τ ξ < OmTwo ∧ Se.SeComm S n σ τ ξ

/-- **The arguments `ξ = Ω₁·b + e < Ω₁·Ω₁`**: `SeComm` at `ξ` from `SeComm` at the countable terms below `ϑᵗ(ξ)`
(`b, e < ϑᵗ(ξ)` by [W07a] Lemma 3.30: `lvLevel_lt_vt` for `b ≥ τ`, `luLt_vt_self` for `b < τ`; then `siUncLow`). -/
theorem siArgLow {n : ℕ} {σ τ ξ : Ordinal.{0}} (hB : Bases σ τ) (hτc : τ < Bc.bcC S (n + 1))
    (hξ : ξ ∈ TB τ σ) (hξ1 : Om1 ≤ ξ) (hξ11 : ξ < Om1 * Om1)
    (hC : ∀ w ∈ TB τ σ, w < Om1 → w < vt τ ξ → Se.SeComm S n σ τ w) :
    Bc.bcB S n ξ < OmTwo ∧ pi σ τ ξ < OmTwo ∧ Se.SeComm S n σ τ ξ := by
  obtain ⟨b, e, hbT, hb1, h1b, heT, he1, hξe, -⟩ := siArg hB hξ hξ1 hξ11
  have hξ2 : ξ < OmTwo := by rw [hξe]; exact lkcMul_lt hb1 he1
  have hvm := vt_memTwo hB.2.1 hB.2.2.2 hξ.1 hξ2
  have hτv : τ ≤ vt τ (Om1 * b + e) := by rw [← hξe]; exact hvm.2.1
  have hbe : b < vt τ ξ ∧ e < vt τ ξ := by
    rw [hξe]
    rcases lt_or_ge b τ with hbτ | hτb
    · exact ⟨hbτ.trans_le hτv, luLt_vt_self hB.2.1 hB.2.2.2 h1b hbτ heT.1 he1⟩
    · exact lvLevel_lt_vt hB.2.1 hB.2.2.2 hbT.1 hτb hb1 heT.1 he1
  rw [hξe]
  exact siUncLow hB hτc hbT hb1 heT he1 (hC b hbT hb1 hbe.1) (hC e heT he1 hbe.2)

/-- **THE JOINT INDUCTION, generic in the uncountable arguments**: under `SiVtU` at `τ` and at `σ`, if every
uncountable argument `ξ ∈ Tᵗ[σ] ∩ [Ω₁, Ω₂)` has `SeComm` (with `B_n ξ, π ξ < Ω₂`) as soon as `SeComm` holds at the
countable `w ∈ Tᵗ[σ]` below `ϑᵗ(ξ)` (`hArg`), then `SeComm` holds at every `z ∈ Tᵗ[σ] ∩ Ω₁`.  As `Se.seComm_all`; a
`ϑᵗ`-term `z = ϑᵗ(ξ)` with `ξ < Ω₁` uses `Si.siVtHomC` at `τ` and `σ`. -/
theorem siComm_gen {n : ℕ} {σ τ : Ordinal.{0}} (hB : Bases σ τ)
    (hτc : τ < Bc.bcC S (n + 1)) (hVT : SiVtU S n τ) (hVS : SiVtU S n σ)
    (hArg : ∀ ξ ∈ TB τ σ, Om1 ≤ ξ → ξ < OmTwo →
      (∀ w ∈ TB τ σ, w < Om1 → w < vt τ ξ → Se.SeComm S n σ τ w) →
        Bc.bcB S n ξ < OmTwo ∧ pi σ τ ξ < OmTwo ∧ Se.SeComm S n σ τ ξ) :
    ∀ z ∈ TB τ σ, z < Om1 → Se.SeComm S n σ τ z := by
  obtain ⟨hσE, hτE, hστ, hτ1⟩ := hB
  have hB0 : Bases σ τ := ⟨hσE, hτE, hστ, hτ1⟩
  have hB' := Se.seBases_img hB0 hτc
  have hLc : Bc.bcC S (n + 1) < Nc.ncL S ω := Se.seC_lt_L n
  have hσc : σ < Bc.bcC S (n + 1) := hστ.trans hτc
  have hTc : ∀ w ∈ TB τ σ, w < Om1 → w < Bc.bcC S (n + 1) := fun w hw hw1 => si_T_lt_c hτE hτc hw.1 hw1
  have hTL : ∀ w ∈ TB τ σ, w < Om1 → w < Nc.ncL S ω := fun w hw hw1 => (hTc w hw hw1).trans hLc
  have hπc : ∀ w ∈ TB τ σ, w < Om1 → pi σ τ w < Bc.bcC S (n + 1) := fun w hw hw1 =>
    si_T_lt_c hσE hσc ((pi_bijOn hB0).1.mapsTo hw) (down_lt_Om1 hB0 hw hw1)
  have hπL : ∀ w ∈ TB τ σ, w < Om1 → pi σ τ w < Nc.ncL S ω := fun w hw hw1 => (hπc w hw hw1).trans hLc
  have hσL : σ < Nc.ncL S ω := hσc.trans hLc
  obtain ⟨hOT, hOπ⟩ := pi_Om1 hB0
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hz hz1
  have hzL : z < Nc.ncL S ω := hTL z hz hz1
  rcases lt_or_ge z τ with hzτ | hτz
  · -- a parameter `z < σ`
    have hzσ : z < σ := (TB_inter_lt hB0 hzτ).1 hz
    have hBz : Bc.bcB S n z < Bc.bcB S n σ := (Bc.bcB_lt_iff hzL hσL).2 hzσ
    refine ⟨mem_TB_of_lt hB' hBz, ?_⟩
    rw [pi_lt hB' hBz, pi_lt hB0 hzσ]
  by_cases hI : Indec z
  · -- a `ϑᵗ`-term
    obtain ⟨ξ, hξT, hξ2, hvz⟩ := vt_rep hτE hτ1 hz.1 hτz hz1 hI
    have hvm := vt_memTwo hτE hτ1 hξT hξ2
    have hξTB : ξ ∈ TB τ σ := ⟨hξT, by rw [← hvm.2.2.2.2, hvz]; exact hz.2⟩
    have hzc : z < Bc.bcC S (n + 1) := hTc z hz hz1
    -- the commutation at the argument `ξ`
    have hξc : Bc.bcB S n ξ < OmTwo ∧ pi σ τ ξ < OmTwo ∧ Se.SeComm S n σ τ ξ := by
      rcases lt_or_ge ξ Om1 with hξ1 | hξ1
      · have hξz : ξ < z := by rw [← hvz]; exact Se.seVt_gt hτE hτ1 hξT hξ1
        refine ⟨?_, (down_lt_Om1 hB0 hξTB hξ1).trans tqc_Om1_lt_OmTwo, IH ξ hξz hξTB hξ1⟩
        exact (Rt.rt_lt_Om1 (hξz.trans hzc)).2.trans tqc_Om1_lt_OmTwo
      · exact hArg ξ hξTB hξ1 hξ2 fun w hw hw1 hwz => IH w (by rw [← hvz]; exact hwz) hw hw1
    obtain ⟨hBξ2, hπξ2, hξTB', hξπ⟩ := hξc
    -- `B_n` commutes with `ϑᵗ` at `ξ` and with `ϑᵟ` at `π ξ`
    have hVTξ : Bc.bcB S n (vt τ ξ) = vt (Bc.bcB S n τ) (Bc.bcB S n ξ) := by
      rcases lt_or_ge ξ Om1 with hξ1 | hξ1
      · have hξz : ξ < z := by rw [← hvz]; exact Se.seVt_gt hτE hτ1 hξT hξ1
        exact siVtHomC hτE hτc (hξz.trans hzc)
      · exact hVT ξ hξT hξ1 hξ2
    have hVSξ : Bc.bcB S n (vt σ (pi σ τ ξ)) = vt (Bc.bcB S n σ) (Bc.bcB S n (pi σ τ ξ)) := by
      rcases lt_or_ge ξ Om1 with hξ1 | hξ1
      · exact siVtHomC hσE hσc (hπc ξ hξTB hξ1)
      · have hπ1 : Om1 ≤ pi σ τ ξ := by rw [← hOπ]; exact ((pi_bijOn hB0).2.le_iff_le hOT hξTB).2 hξ1
        exact hVS _ ((pi_bijOn hB0).1.mapsTo hξTB) hπ1 hπξ2
    have hBz : Bc.bcB S n z = vt (Bc.bcB S n τ) (Bc.bcB S n ξ) := by rw [← hvz]; exact hVTξ
    have hvm' := vt_memTwo hB'.2.1 hB'.2.2.2 hξTB'.1 hBξ2
    refine ⟨⟨by rw [hBz]; exact hvm'.1, by rw [hBz, hvm'.2.2.2.2]; exact hξTB'.2⟩, ?_⟩
    rw [hBz, pi_vt_two hB' hξTB' hBξ2, hξπ, ← hvz, pi_vt_two hB0 hξTB hξ2]
    exact hVSξ.symm
  · -- a sum: the leading component and the rest
    have hz0 : z ≠ 0 := (lt_of_lt_of_le (InE.pos hτE) hτz).ne'
    obtain ⟨L, hLc', hLz, hLzz⟩ := exists_comp_absorb hz0 hI
    have hLTB : L ∈ TB τ σ := by
      have hPc := Par_comps hτE hτ1 hz.1 hτz hz1 hLc'
      rcases lt_or_ge L τ with hLτ | hτL'
      · have hLσ : L < σ := hz.2 (hPc.1 hLτ)
        exact mem_TB_of_lt hB0 hLσ
      · obtain ⟨hLT, hLP⟩ := hPc.2 hτL'
        exact ⟨hLT, fun q hq => hz.2 (hLP hq)⟩
    obtain ⟨hqTB, hπq⟩ := TB_sub hB0 hLTB hz hLz.le hz1
    set q := z - L with hqdef
    have hzLq : L + q = z := Ordinal.add_sub_cancel_of_le hLz.le
    have hqz : q < z := by
      refine lt_of_le_of_ne (sub_le_self _ _) fun e => hLzz ?_
      conv_rhs => rw [← hzLq]
      rw [e]
    have hL1 : L < Om1 := hLz.trans hz1
    have hq1 : q < Om1 := hqz.trans hz1
    obtain ⟨hLTB', hLπ⟩ := IH L hLz hLTB hL1
    obtain ⟨hqTB', hqπ⟩ := IH q hqz hqTB hq1
    have hBz : Bc.bcB S n z = Bc.bcB S n L + Bc.bcB S n q := by
      rw [← hzLq]; exact Bc.bcB_add (hTL L hLTB hL1) (hTL q hqTB hq1)
    obtain ⟨hsumTB, hsumπ⟩ := pi_add hB' hLTB' hqTB'
    refine ⟨by rw [hBz]; exact hsumTB, ?_⟩
    rw [hBz, hsumπ, hLπ, hqπ, ← Bc.bcB_add (hπL L hLTB hL1) (hπL q hqTB hq1), ← hzLq,
      (pi_add hB0 hLTB hqTB).2]

/-- **THE JOINT INDUCTION**: under `SiVtU` at `τ` and at `σ` and `SiUncH`, `SeComm` holds at every
`z ∈ Tᵗ[σ] ∩ Ω₁` (`siComm_gen`; the arguments `ξ < Ω₁·Ω₁` by `siArgLow`). -/
theorem siComm_all {n : ℕ} {σ τ : Ordinal.{0}} (hB : Bases σ τ)
    (hτc : τ < Bc.bcC S (n + 1)) (hVT : SiVtU S n τ) (hVS : SiVtU S n σ) (hU : SiUncH S n σ τ) :
    ∀ z ∈ TB τ σ, z < Om1 → Se.SeComm S n σ τ z :=
  siComm_gen hB hτc hVT hVS fun ξ hξ hξ1 hξ2 hC => by
    rcases lt_or_ge ξ (Om1 * Om1) with hξ11 | hξ11
    · exact siArgLow hB hτc hξ hξ1 hξ11 hC
    · exact hU ξ hξ hξ11 hξ2

/-- **`SiUncH` gives `Se.SeUnc`** once `SeComm` holds on the countable terms (on `[Ω₁, Ω₁·Ω₁)` by `siArgLow`). -/
theorem siUnc_of {n : ℕ} {σ τ : Ordinal.{0}} (hB : Bases σ τ) (hτc : τ < Bc.bcC S (n + 1))
    (hC : ∀ z ∈ TB τ σ, z < Om1 → Se.SeComm S n σ τ z) (hU : SiUncH S n σ τ) : Se.SeUnc S n σ τ := by
  intro ξ hξ hξ1 hξ2
  rcases lt_or_ge ξ (Om1 * Om1) with h | h
  · exact siArgLow hB hτc hξ hξ1 h fun w hw hw1 _ => hC w hw hw1
  · exact hU ξ hξ h hξ2

/-! ## The hypothesis and its consequences -/

/-- **`Se.SePiHom2` asking `ϑ` only at uncountable arguments and `π` only from `Ω₁·Ω₁` on** (a hypothesis name):
every non-`υ` point `x ∈ [c_n, c_{n+1})` has bases `σ < τ` as in `Se.seBases` with `SiVtU` at `τ` and at `σ` and
`SiUncH`. -/
def SiPiHom (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ x, Bc.bcC S n ≤ x → x < Bc.bcC S (n + 1) → ¬ UpsPt x →
    ∃ σ τ, Bases σ τ ∧ LtInf1 τ ∧ τ < x ∧ x ∈ TB τ σ ∧ SiVtU S n τ ∧ SiVtU S n σ ∧ SiUncH S n σ τ

/-- **`SiPiHom S ↔ Se.SePiHom2 S`**: the countable arguments of `ϑ` and the arguments `ξ < Ω₁·Ω₁` of `π` are
theorems. -/
theorem siPiHom_iff : SiPiHom S ↔ Se.SePiHom2 S := by
  constructor
  · intro h n x hc hx hU
    obtain ⟨σ, τ, hB, hτL, hτx, hxT, hT, hS, hUn⟩ := h n x hc hx hU
    have hτc : τ < Bc.bcC S (n + 1) := hτx.trans hx
    exact ⟨σ, τ, hB, hτL, hτx, hxT, siVtHom_of hB.2.1 hτc hT, siVtHom_of hB.1 (hB.2.2.1.trans hτc) hS,
      siUnc_of hB hτc (siComm_all hB hτc hT hS hUn) hUn⟩
  · intro h n x hc hx hU
    obtain ⟨σ, τ, hB, hτL, hτx, hxT, hT, hS, hUn⟩ := h n x hc hx hU
    exact ⟨σ, τ, hB, hτL, hτx, hxT, fun η hη _ hη2 => hT η hη hη2, fun η hη _ hη2 => hS η hη hη2,
      fun ξ hξ hξ1 hξ2 => hUn ξ hξ ((Ordinal.le_mul_right Om1 Rj.rj_Om1_pos).trans hξ1) hξ2⟩

/-- **`SiPiHom` gives `Rt.RtPiComm`.** -/
theorem siPiComm (h : SiPiHom S) : Rt.RtPiComm S := Se.sePiComm (Se.sePiHom_of (siPiHom_iff.1 h))

/-- **`SiPiHom` gives `Rk.RkLhTopE`.** -/
theorem siLhTopE (h : SiPiHom S) : Rk.RkLhTopE S := Se.seLhTopE2 (siPiHom_iff.1 h)

/-- **`SiPiHom` gives `Tp.TpLhEps`.** -/
theorem siLhEps (h : SiPiHom S) : Tp.TpLhEps S := Se.seLhEps (Se.sePiHom_of (siPiHom_iff.1 h))

/-- **The road `Se.seRoadE_nuHom2` with `SiPiHom`.** -/
theorem siRoadE_nu (hU : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdUpper S l)
    (hL : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S Ge.geV ≤ l → Cd.CdCapV S l)
    (hEQ : Cd.CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC) (hpi : SiPiHom S)
    (hT : Cx.CxT S) (hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) :
    Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cd.CdCL S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  Se.seRoadE_nuHom2 hU hL hV hEQ hν (siPiHom_iff.1 hpi) hT hcl

end Googology.Trans.PoR.InaccPsi.R2.Si

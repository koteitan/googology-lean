import Googology.Trans.PoR.InaccPsi.R2.SmPh

/-!
# `SePiHom2` asking `ϑ` at a `υ`-base only from `ε_{Ω₁+1}` on

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`B_n = Bc.bcB S n`, `c_n = L(n+1) = Bc.bcC S n`, `ϑ^β = vt β`, `ε_{Ω₁+1} = Gg.ggE`, `Si.SiVtU S n β`: `B_n(ϑ^β(η)) =
ϑ^{B_n β}(B_n η)` on `T^β ∩ [Ω₁, Ω₂)`, `Si.SiUncHE`, `Si.SiPiHomE` as in `R2.SiUnc`.

* `SmVtTop S n β` (a hypothesis name): **`B_n(ϑ^β(η)) = ϑ^{B_n β}(B_n η)` for `η ∈ T^β ∩ [ε_{Ω₁+1}, Ω₂)`**;
* `smVtU_ups` (**at a `υ`-point `β ∈ [c_n, c_{n+1})`, `SmVtTop S n β ⇒ Si.SiVtU S n β`**: the arguments
  `[Ω₁, Ω₁·Ω₁)` by `Sm.smVtU_low`, `[Ω₁·Ω₁, ε_{Ω₁+1})` by `Sm.smVtU_hi`), `smVtU_ups_iff` (the two are equivalent);
* `smB_code_fix` (**`B_n` fixes every code over `c_n`**), `smVtU_below` (**at an `ε`-base `σ < c_n`, `SmVtTop S n σ ⇒
  Si.SiVtU S n σ`**: `B_n` fixes `σ`, `T^σ ∩ Ω₁` and `T^σ ∩ [Ω₁, ε_{Ω₁+1})`);
* `SmVtB S n σ` (a hypothesis name for the `ε`-base `σ`): `σ < c_n` or `σ` a `υ`-point in `[c_n, c_{n+1})`, with
  `SmVtTop`; or `Si.SiVtU S n σ` (left only for a non-`υ` base `σ ∈ [c_n, c_{n+1})`); `smVtB_SiVtU` (`SmVtB ⇒
  SiVtU`);
* `SmPiHom S` (a hypothesis name): **every non-`υ` point `x ∈ [c_n, c_{n+1})` has bases `σ < τ` as in `Se.seBases`
  (`τ <₁ ∞`, `c_n ≤ τ < x`, `x ∈ Tᵗ[σ]`) with `SmVtTop` at `τ`, `SmVtB` at `σ` and `Si.SiUncHE`**;
  `smPiHomE` (**`SmPiHom ⇒ Si.SiPiHomE`**), `smPiHom_iff` (**`SmPiHom` is exactly `Se.SePiHom2` with `c_n ≤ τ`**),
  `smPiHom2` (**`⇒ Se.SePiHom2`**), `smPiComm` (`⇒ Rt.RtPiComm`), `smLhTopE` (`⇒ Rk.RkLhTopE`), `smLhEps`
  (`⇒ Tp.TpLhEps`), `smRoadE_nu` (**the road `Si.siRoadE_nuE` with `SmPiHom` in place of `Si.SiPiHomE`**).

No new axiom.  New definitions: the hypothesis names `SmVtTop`, `SmVtB`, `SmPiHom`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Sm

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg

variable {S : InaccSeq.{0}}

/-- **`B_n` commutes with `ϑ^β` on `T^β ∩ [ε_{Ω₁+1}, Ω₂)`** (a hypothesis name). -/
def SmVtTop (S : InaccSeq.{0}) (n : ℕ) (β : Ordinal.{0}) : Prop :=
  ∀ η ∈ Tset β, ggE ≤ η → η < OmTwo → Bc.bcB S n (vt β η) = vt (Bc.bcB S n β) (Bc.bcB S n η)

/-- **At a `υ`-point `β ∈ [c_n, c_{n+1})`, `SmVtTop` gives `Si.SiVtU`**: the arguments below `ε_{Ω₁+1}` are
`smVtU_low` and `smVtU_hi`. -/
theorem smVtU_ups {n : ℕ} {β : Ordinal.{0}} (hU : UpsPt β) (hc : Bc.bcC S n ≤ β) (hβc : β < Bc.bcC S (n + 1))
    (h : SmVtTop S n β) : Si.SiVtU S n β := by
  obtain ⟨ξ, -, rfl⟩ := upsPt_iff_upsilon.1 hU
  intro η hη hη1 hη2
  rcases lt_or_ge η (Om1 * Om1) with h11 | h11
  · exact smVtU_low hc hβc η hη hη1 h11
  rcases lt_or_ge η ggE with hE | hE
  · exact smVtU_hi hc hβc η hη h11 hE
  · exact h η hη hE hη2

/-- **At a `υ`-point `β ∈ [c_n, c_{n+1})`, `Si.SiVtU S n β ↔ SmVtTop S n β`.** -/
theorem smVtU_ups_iff {n : ℕ} {β : Ordinal.{0}} (hU : UpsPt β) (hc : Bc.bcC S n ≤ β)
    (hβc : β < Bc.bcC S (n + 1)) : Si.SiVtU S n β ↔ SmVtTop S n β :=
  ⟨fun h η hη hE hη2 => h η hη (Rj.rj_Om1_lt_E.le.trans hE) hη2, smVtU_ups hU hc hβc⟩

/-- **`B_n` fixes every code over `c_n`** (the leaves below `c_n` are fixed, `B_n` keeps `Ω₁`, `+`, `φ`). -/
theorem smB_code_fix {n : ℕ} : ∀ μ, GgCl (Bc.bcC S n) μ → Bc.bcB S n μ = μ := by
  have hcL : Bc.bcC S n < Nc.ncL S ω := Bc.bcC_lt S n
  intro μ hμ
  induction hμ with
  | @small a ha => exact Bc.bcB_fix' S n a ha
  | om => exact (Mv.mvB_Om1 (S := S) (k := n)).2
  | @add a b ha hb iha ihb =>
    rw [(Mv.mvB_add (k := n) (Rk.rkB_cl (n := n) hcL a ha).1 (Rk.rkB_cl (n := n) hcL b hb).1).2, iha, ihb]
  | @phi a b ha hb iha ihb =>
    by_cases h : a < veblen a b ∧ b < veblen a b
    · rw [(Mw.mwB_phi (k := n) (Rk.rkB_cl (n := n) hcL a ha).1 (Rk.rkB_cl (n := n) hcL b hb).1 h.1 h.2).2,
        iha, ihb]
    · rcases not_and_or.1 h with h' | h'
      · have e : veblen a b = a := le_antisymm (not_lt.1 h') (left_le_veblen a b)
        rw [e]; exact iha
      · have e : veblen a b = b := le_antisymm (not_lt.1 h') (right_le_veblen a b)
        rw [e]; exact ihb

/-- **At an `ε`-base `σ < c_n`, `SmVtTop` gives `Si.SiVtU`**: below `c_n` `B_n` is the identity, so `B_n(ϑ^σ(η)) =
ϑ^σ(η)` (`T^σ ∩ Ω₁` lies below the next `υ`-point, `≤ c_n`) and `B_n σ = σ`; for `η ∈ T^σ ∩ [Ω₁, ε_{Ω₁+1})`,
`η = Ω₁·M + e` with `M` a code over `c_n` (its leaves lie in `T^σ ∩ Ω₁`: `lgQuot_mem`, the cited `rkArg_dat`) and
`e < c_n` (`vzRem_T`), so `B_n η = η` (`smB_code_fix`). -/
theorem smVtU_below {n : ℕ} {σ : Ordinal.{0}} (hσE : InE σ) (hσc : σ < Bc.bcC S n) (h : SmVtTop S n σ) :
    Si.SiVtU S n σ := by
  intro η hη hη1 hη2
  rcases le_or_gt ggE η with hE | hE
  · exact h η hη hE hη2
  have hcS : SC (Bc.bcC S n) := Lw.lw_L_SC S _
  have hcS1 : SC (Bc.bcC S (n + 1)) := Lw.lw_L_SC S _
  have hcc : Bc.bcC S n < Bc.bcC S (n + 1) := Cx.cxC_lt n
  have hcL1 : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hσ1 : σ < Om1 := (Rt.rt_lt_Om1 (hσc.trans hcc)).1
  obtain ⟨m, -, -, hmin, hmT, -⟩ := T_next (Or.inr hσE) hσ1
  have hmc : m ≤ Bc.bcC S n := hmin _ hσc (Rt.rt_c_inf n)
  have hTc : ∀ a ∈ Tset σ, a < Om1 → a < Bc.bcC S n := fun a ha ha1 => ((hmT a ha1).1 ha).trans_le hmc
  have hfix : ∀ a ∈ Tset σ, a < Om1 → Bc.bcB S n a = a := fun a ha ha1 => Bc.bcB_fix' S n a (hTc a ha ha1)
  obtain ⟨hdec, he1⟩ := vz_div_Om1 η
  have heT : η % Om1 ∈ Tset σ := vzRem_T hσE hσ1 hη hη2 hdec.symm (dvd_mul_right _ _) he1
  have hMC : GgCl (Bc.bcC S n) (η / Om1) := by
    rcases lt_or_ge η (Om1 * Om1) with h11 | h11
    · have hM1 : η / Om1 < Om1 := (Ordinal.lt_mul_iff_div_lt Rj.rj_Om1_pos.ne').1 h11
      exact GgCl.small (hTc _ (lgQuot_mem hσE hσ1 hη h11) hM1)
    · have hM1 : Om1 ≤ η / Om1 := (Ordinal.mul_le_iff_le_div Rj.rj_Om1_pos.ne').1 h11
      have hME : η / Om1 < ggE :=
        (Ordinal.div_le_of_le_mul (Ordinal.le_mul_right η Rj.rj_Om1_pos)).trans_lt hE
      have hdatT : Rj.rjDat (η / Om1) ∈ Tset σ := rkArg_dat hσE hσ1 hM1 hME he1 (by rw [hdec]; exact hη)
      exact (Rk.rk_cl_iff hcS hME).2 (hTc _ hdatT (Rj.rjDat_lt_Om1 _ hME))
  set M := η / Om1 with hMdef
  set e := η % Om1 with hedef
  have hBM : Bc.bcB S n M = M := smB_code_fix _ hMC
  obtain ⟨hDz, hBz⟩ := Rk.rkB_Om1mul (n := n) hcS1 hcL1 _ (hMC.mono hcc.le)
  have hBη : Bc.bcB S n η = η := by
    have hecL : e < Nc.ncL S ω := (hTc _ heT he1).trans (Bc.bcC_lt S n)
    have hOM : Om1 * M = Om 1 * M := by rw [Rj.rj_Om1]
    conv_lhs => rw [← hdec]
    rw [hOM, (Mv.mvB_add (k := n) hDz (Mv.mvD_of_lt hecL)).2, hBz, hBM, hfix _ heT he1, ← hOM, hdec]
  have hvm := vt_memTwo hσE hσ1 hη hη2
  rw [hfix _ hvm.1 hvm.2.2.1, Bc.bcB_fix' S n σ hσc, hBη]

/-- **The hypothesis at the `ε`-base `σ`** (a hypothesis name): `σ` lies below `c_n` or is a `υ`-point in
`[c_n, c_{n+1})`, with `SmVtTop`; or `B_n` commutes with `ϑ^σ` on all of `T^σ ∩ [Ω₁, Ω₂)` (the case of a
non-`υ` base `σ ∈ [c_n, c_{n+1})`). -/
def SmVtB (S : InaccSeq.{0}) (n : ℕ) (σ : Ordinal.{0}) : Prop :=
  ((σ < Bc.bcC S n ∨ (UpsPt σ ∧ Bc.bcC S n ≤ σ)) ∧ SmVtTop S n σ) ∨ Si.SiVtU S n σ

/-- `SmVtB` gives `Si.SiVtU` at an `ε`-number `σ < c_{n+1}`. -/
theorem smVtB_SiVtU {n : ℕ} {σ : Ordinal.{0}} (hσE : InE σ) (hσc : σ < Bc.bcC S (n + 1)) (h : SmVtB S n σ) :
    Si.SiVtU S n σ := by
  rcases h with ⟨hl | ⟨hU, hc⟩, hT⟩ | h
  · exact smVtU_below hσE hl hT
  · exact smVtU_ups hU hc hσc hT
  · exact h

/-- **`Se.SePiHom2` asking `ϑ` at the `υ`-base `τ` only from `ε_{Ω₁+1}` on** (a hypothesis name): every non-`υ`
point `x ∈ [c_n, c_{n+1})` has bases `σ < τ` (`τ <₁ ∞`, `c_n ≤ τ < x`, `x ∈ Tᵗ[σ]`) with `SmVtTop` at `τ`, `SmVtB`
at `σ` and `Si.SiUncHE`. -/
def SmPiHom (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ x, Bc.bcC S n ≤ x → x < Bc.bcC S (n + 1) → ¬ UpsPt x →
    ∃ σ τ, Bases σ τ ∧ LtInf1 τ ∧ Bc.bcC S n ≤ τ ∧ τ < x ∧ x ∈ TB τ σ ∧ SmVtTop S n τ ∧ SmVtB S n σ ∧
      Si.SiUncHE S n σ τ

/-- **`SmPiHom` gives `Si.SiPiHomE`.** -/
theorem smPiHomE (h : SmPiHom S) : Si.SiPiHomE S := by
  intro n x hc hx hU
  obtain ⟨σ, τ, hB, hτL, hcτ, hτx, hxT, hT, hS, hUn⟩ := h n x hc hx hU
  have hτc : τ < Bc.bcC S (n + 1) := hτx.trans hx
  have hτU : UpsPt τ := ⟨Si.si_inE_pos hB.2.1, hτL⟩
  exact ⟨σ, τ, hB, hτL, hτx, hxT, smVtU_ups hτU hcτ hτc hT, smVtB_SiVtU hB.1 (hB.2.2.1.trans hτc) hS, hUn⟩

/-- **`SmPiHom` is exactly `Se.SePiHom2` with `c_n ≤ τ`** (the bases of `Se.seBases` have it): `SmVtTop` at `τ`,
`SmVtB` at `σ` and `Si.SiUncHE` are equivalent there to `Se.SeVtHom` at `τ` and `σ` and `Se.SeUnc`. -/
theorem smPiHom_iff : SmPiHom S ↔
    ∀ n : ℕ, ∀ x, Bc.bcC S n ≤ x → x < Bc.bcC S (n + 1) → ¬ UpsPt x →
      ∃ σ τ, Bases σ τ ∧ LtInf1 τ ∧ Bc.bcC S n ≤ τ ∧ τ < x ∧ x ∈ TB τ σ ∧ Se.SeVtHom S n τ ∧
        Se.SeVtHom S n σ ∧ Se.SeUnc S n σ τ := by
  constructor
  · intro h n x hc hx hU
    obtain ⟨σ, τ, hB, hτL, hcτ, hτx, hxT, hT, hS, hUn⟩ := h n x hc hx hU
    have hτc : τ < Bc.bcC S (n + 1) := hτx.trans hx
    have hτU : UpsPt τ := ⟨Si.si_inE_pos hB.2.1, hτL⟩
    have hVT := smVtU_ups hτU hcτ hτc hT
    have hVS := smVtB_SiVtU hB.1 (hB.2.2.1.trans hτc) hS
    exact ⟨σ, τ, hB, hτL, hcτ, hτx, hxT, Si.siVtHom_of hB.2.1 hτc hVT,
      Si.siVtHom_of hB.1 (hB.2.2.1.trans hτc) hVS, Si.siUnc_ofE hB hτc (Si.siComm_allE hB hτc hVT hVS hUn) hUn⟩
  · intro h n x hc hx hU
    obtain ⟨σ, τ, hB, hτL, hcτ, hτx, hxT, hT, hS, hUn⟩ := h n x hc hx hU
    exact ⟨σ, τ, hB, hτL, hcτ, hτx, hxT, fun η hη _ hη2 => hT η hη hη2,
      Or.inr fun η hη _ hη2 => hS η hη hη2,
      fun ξ hξ hξ1 hξ2 => hUn ξ hξ (Rj.rj_Om1_lt_E.le.trans hξ1) hξ2⟩

/-- **`SmPiHom` gives `Se.SePiHom2`.** -/
theorem smPiHom2 (h : SmPiHom S) : Se.SePiHom2 S := Si.siPiHomE_iff.1 (smPiHomE h)

/-- **`SmPiHom` gives `Rt.RtPiComm`.** -/
theorem smPiComm (h : SmPiHom S) : Rt.RtPiComm S := Si.siPiCommE (smPiHomE h)

/-- **`SmPiHom` gives `Rk.RkLhTopE`.** -/
theorem smLhTopE (h : SmPiHom S) : Rk.RkLhTopE S := Si.siLhTopEE (smPiHomE h)

/-- **`SmPiHom` gives `Tp.TpLhEps`.** -/
theorem smLhEps (h : SmPiHom S) : Tp.TpLhEps S := Si.siLhEpsE (smPiHomE h)

/-- **The road `Si.siRoadE_nuE` with `SmPiHom` in place of `Si.SiPiHomE`.** -/
theorem smRoadE_nu (hU : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdUpper S l)
    (hL : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S Ge.geV ≤ l → Cd.CdCapV S l)
    (hEQ : Cd.CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC) (hpi : SmPiHom S)
    (hT : Cx.CxT S) (hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) :
    Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cd.CdCL S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  Si.siRoadE_nuE hU hL hV hEQ hν (smPiHomE hpi) hT hcl

end Googology.Trans.PoR.InaccPsi.R2.Sm

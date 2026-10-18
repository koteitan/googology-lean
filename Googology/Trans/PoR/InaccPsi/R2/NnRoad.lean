import Googology.Trans.PoR.InaccPsi.R2.NnNameG
import Googology.Trans.PoR.InaccPsi.R2.FxRoad

/-!
# The notation statement asked only at the fixed points of `GG`: the roads `fxRoad3` and `xtW2Road3`

`Θ_λ(m_λ) = O(λ)` holds at every fixed point of `υ` of the range that is not a fixed point of `GG`: at the
points that are not `Γ`-points (`Nn.nnTH_ng`) and at the `Γ`-points `F` with `GG(F) ≠ F` (`Nn.nnTH_gg`).  So:

* `nnTHfix` (**`Cp.CpTHfix` from the notation statement at the fixed points of `GG` only**);
* `nnRoad3` (**`Fx.fxRoad3` with its notation hypothesis asked only at the fixed points of `GG` below `cpB1`**);
* `nnFamTHfix`, `nnW2Road3` (**`Xt.xtW2Road3` with `famTHfix` asked only at the fixed points of `GG` below
  `Λ⁺_k`**);
* `nnEnum_cp`, `nnEnum_W2` (**ENUM-REACH, both halves, at every restart of the range below `cpB1`, resp.
  below `Λ_{ω²}`, that is not a fixed point of `GG`** — the non-fixed restarts by `Xt.xtW2_init`, the fixed
  points by the notation statement and `Xt.xtExact_iff`);
* `nnStartU` (the link at the names `η₁ + Ω₁^{Ω₁+1}`, `R2.LwLev`): `ρ = P(η₁ + Ω₁^{Ω₁+1})` is a fixed point of
  `GG` and `ρ·ρ + ρ ≤ O(ι(η₁ + Ω₁^{Ω₁+1}))`, for every term system with linear and square terms;
* `nnVz_PhiG_W` (an instance past `Φ_Γ`): `P(Ω₁^{Ω₁+1} + W)` is the least `Γ`-point above `Φ_Γ` and
  `VzOrec(ι(Ω₁^{Ω₁+1} + W)) = P(Ω₁^{Ω₁+1} + W)²`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Nn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp Googology.Trans.PoR.InaccPsi.R2.Fx
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Lw

variable {S : InaccSeq.{0}}

/-- The notation statement at a fixed point of the range that is not a fixed point of `GG`, for any term system
with linear and square terms. -/
theorem nnTH_notGG {X : XtSys} (hX0 : NnLin X) (hS : NnSq X) {l : Ordinal.{0}} (hr : CdRange S l)
    (hfix : upsilon l = l) (hGl : ¬ (IsGP l ∧ GG l = l)) : cdTheta S l (cdCode S l) = xtOrec X l := by
  by_cases hG : IsGP l
  · exact nnTH_gg hX0 hS hr.1 hfix hG (fun h => hGl ⟨hG, h⟩) (cp_name_L hr.2.2.1)
  · exact nnTH_ng hX0 hr.1 hfix hG (cp_name_L hr.2.2.1)

/-- **`Cp.CpTHfix` from the notation statement at the fixed points of `GG` only.** -/
theorem nnTHfix (hT : ∀ l, CdRange S l → l < cpB1 → upsilon l = l → GG l = l →
    cdTheta S l (cdCode S l) = VzOrec l) : CpTHfix S := fun l hr hlB hfix => by
  by_cases h : IsGP l ∧ GG l = l
  · exact hT l hr hlB hfix h.2
  · rw [← xtVz_orec]; exact nnTH_notGG nnLin_vz nnSq_vz hr hfix h

/-- **`Fx.fxRoad3` with its notation hypothesis asked only at the fixed points of `GG` below `cpB1`.** -/
theorem nnRoad3 (hU : CpUPPERhigh S) (hL : CpLOWERhigh S)
    (hT : ∀ l, CdRange S l → l < cpB1 → upsilon l = l → GG l = l → cdTheta S l (cdCode S l) = VzOrec l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CpOut2 l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  fxRoad3 hU hL (fun l hr hlB hfix _ => nnTHfix hT l hr hlB hfix) hV hC hEQ hrest hB2

/-- **`famTHfix` of `xtFamW2` from the notation statement at the fixed points of `GG` only.** -/
theorem nnFamTHfix (hT : ∀ k : ℕ, ∀ l, CdRange S l → l < xtFamW2.bd k → upsilon l = l → GG l = l →
    cdTheta S l (cdCode S l) = xtFamW2.off k l) : xtFamW2.famTHfix S := fun k l hr hlk hfix => by
  by_cases h : IsGP l ∧ GG l = l
  · exact hT k l hr hlk hfix h.2
  · exact nnTH_notGG (nnLin_LL k) (nnSq_LL k) hr hfix h

/-- **`Xt.xtW2Road3` with `famTHfix` asked only at the fixed points of `GG`.** -/
theorem nnW2Road3 (hU : ∀ l, CdRange S l → xtFamW2.famSup ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtFamW2.famSup ≤ l → CdLower S l)
    (hT : ∀ k : ℕ, ∀ l, CdRange S l → l < xtFamW2.bd k → upsilon l = l → GG l = l →
      cdTheta S l (cdCode S l) = xtFamW2.off k l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut xtFamW2.famSup l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtW2Road3 hU hL (nnFamTHfix hT) hV hC hEQ hrest hB2


/-- **ENUM-REACH below `cpB1` at the restarts that are not fixed points of `GG`.** -/
theorem nnEnum_cp {l : Ordinal.{0}} (hr : CdRange S l) (hlB : l < cpB1)
    (hGl : ¬ (upsilon l = l ∧ IsGP l ∧ GG l = l)) : CdUpper S l ∧ CdLower S l := by
  by_cases hfix : upsilon l = l
  · refine (cpExact_iff hr.1 hlB).2 ?_
    rw [← xtVz_orec]
    exact nnTH_notGG nnLin_vz nnSq_vz hr hfix (fun h => hGl ⟨hfix, h⟩)
  · exact (fxEnum_range hr hlB fun h => hfix h.1).2.1 |> fun hU =>
      ⟨hU, (fxEnum_range hr hlB fun h => hfix h.1).2.2.1⟩

/-- **ENUM-REACH below `Λ_{ω²}` at the restarts that are not fixed points of `GG`.** -/
theorem nnEnum_W2 {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtFamW2.famSup)
    (hGl : ¬ (upsilon l = l ∧ IsGP l ∧ GG l = l)) : CdUpper S l ∧ CdLower S l := by
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact xtW2_init hr hl hnf
  · have hfix : upsilon l = l := hfx.symm
    obtain ⟨k, hk⟩ := xtFamW2.famLt hl
    refine (xtExact_iff (xtFamW2.spec k) hr.1 hk).2 ?_
    exact nnTH_notGG (nnLin_LL k) (nnSq_LL k) hr hfix (fun h => hGl ⟨hfix, h⟩)

/-- **The link at the names `η₁ + Ω₁^{Ω₁+1}`**: the value is a fixed point of `GG`, and
`ρ·ρ + ρ ≤ O(ι(η₁ + Ω₁^{Ω₁+1}))`. -/
theorem nnStartU {X : XtSys} (hX0 : NnLin X) (hS : NnSq X) {η1 : Ordinal.{0}} (hg : Bt.Good S η1)
    (hd : Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1) ∣ η1) :
    GG (Pv S (η1 + Om 1 ^ (Om 1 + 1))) = Pv S (η1 + Om 1 ^ (Om 1 + 1)) ∧
      Pv S (η1 + Om 1 ^ (Om 1 + 1)) * Pv S (η1 + Om 1 ^ (Om 1 + 1)) + Pv S (η1 + Om 1 ^ (Om 1 + 1)) ≤
        xtOrec X (iota S (η1 + Om 1 ^ (Om 1 + 1))) := by
  have hfixG := (nn_ggfix_of_U hg hd 1).2 one_ne_zero
  rw [Nat.cast_one, mul_one] at hfixG
  set ρ := Pv S (η1 + Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1)) with hρ
  have hρ0 : 0 < ρ := lt_of_le_of_lt zero_le (nn_one_lt_Pv S _)
  have hfix : upsilon ρ = ρ := nn_gp_fix (by rw [← hfixG]; exact isGP_GG hρ0)
  have hι : iota S (η1 + Om 1 ^ (Om 1 + 1)) = ρ := iota_of_fix hρ.symm hfix
  rw [hι]
  exact ⟨hfixG, nnPhi hX0 hS (ri_of_fp hρ0 hfix) (nn_Pv_lt S _) hfixG⟩

/-- **An instance past `Φ_Γ`**: `ρ = P(Ω₁^{Ω₁+1} + W)` is the least `Γ`-point above `Φ_Γ` and
`VzOrec(ι(Ω₁^{Ω₁+1} + W)) = ρ·ρ`. -/
theorem nnVz_PhiG_W :
    Pv S (Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1) + W) = nxt GG PhiG ∧
      VzOrec (iota S (Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1) + W)) =
        Pv S (Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1) + W) *
          Pv S (Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1) + W) := by
  have hg := lw_good_U S
  have hd := lw_W_dvd_U
  refine ⟨?_, ?_⟩
  · rw [start_GG hg hd, lw_PU, lw_D_one]
  · rw [← xtVz_orec]; exact nnStartW nnLin_vz nnSq_vz hg hd

end Googology.Trans.PoR.InaccPsi.R2.Nn

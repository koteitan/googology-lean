import Googology.Trans.PoR.InaccPsi.R2.TpUps

/-!
# (TC) at the points of `(L(n+1), L(n+2))` that are not restarts of the range

`L(ξ) = Nc.ncL S ξ`, `c_n = L(n+1)`, `B_n = Bc.bcB S n`, `lh` the reach (`IsReach R2C`), `lh₁` the reach of
`R₁⁺` (`IsLh1`).  The points `x` of the open window `(L(n+1), L(n+2))`:

* `tpRange_win` (**every restart point of the window is a restart of the range**, given (CL)): a restart
  `λ < Λ_B⁺` has no `≤₁`-relation across `ρ_λ` (`Rz.rzBlk`), while `L(n+1) ≤₁ L(n+2)`; so `λ ≥ Λ_B⁺ > B₀`,
  and `ρ_λ` is none of the `L(k)` (`cdRange_iff_level2`);
* `tpTC_ups` (**the non-restart `υ`-points**, given `L(ω+1) ≤ ν_C` and the shift `TpShift`): `lh(x)` is the
  top of the block of `x`, `B_n` moves the block onto a block, so `lh(B_n x) = B_n(lh x)`;
* `TpLhMove S` (**the `R₁⁺`-reach moves with `B_n`** at the non-`υ`-points of the window) and
  `TpLhPrin S` (the same only at the indecomposable ones); `tpLhMove_of_prin`: at a decomposable `x`,
  `lh₁(x) = x` and `B_n x` is decomposable (`Bc.bcB_add`), so only the indecomposable points remain;
* `tpTC_off` (**the non-`υ`-points**, given `L(ω+1) ≤ ν_C`, the shift and `TpLhMove`): below `ν_C` the
  reach of a non-`υ`-point is its `R₁⁺`-reach (`Lh.lhSk_reach`), it lies below the next `υ`-point, and
  `B_n x` is not a `υ`-point (`tpUpsRefl`);
* `tpTCtopOff`: (CL), `L(ω+1) ≤ ν_C`, `TpShift`, `TpLhMove` give `CxTCtopOff`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cx

variable {S : InaccSeq.{0}}

/-- **Every restart point of the open window `(L(n+1), L(n+2))` is a restart of the range**, given (CL). -/
theorem tpRange_win (hC : CdCL S) {n : ℕ} {l : Ordinal.{0}} (hl : IsRestartIdx l)
    (h1 : Bc.bcC S n < upsilon l) (h2 : upsilon l < Bc.bcC S (n + 1)) : CdRange S l := by
  have hB : cdB0 ≤ l := by
    by_contra hlt
    push Not at hlt
    have hlR : l < Rz.rzLam := lt_trans hlt Rz.rzB0_lt
    exact (Rz.rzBlk.2.1 l hl hlR).1 _ h1 _ h2.le (hC n)
  have hlev : cdMstar S ≤ upsilon l := (cdMstar_le_L S _).trans h1.le
  have hlX : upsilon l < Nc.ncL S ω := h2.trans (Bc.bcC_lt S (n + 1))
  refine (cdRange_iff_level2 hl hB hlev hlX).2 fun k hk => ?_
  rcases le_or_gt k (n + 1) with hkn | hkn
  · have : Nc.ncL S (k : Ordinal.{0}) ≤ Bc.bcC S n := Qq.qqL_mono S hkn
    exact absurd (hk ▸ h1) (not_lt.2 this)
  · have : Bc.bcC S (n + 1) ≤ Nc.ncL S (k : Ordinal.{0}) := Qq.qqL_mono S (by omega)
    exact absurd (hk ▸ h2) (not_lt.2 this)

/-- **(TC) at a non-restart `υ`-point of the window**, given `L(ω+1) ≤ ν_C` and the shift. -/
theorem tpTC_ups (hν : Nc.ncL S (ω + 1) ≤ nuC) (hsh : TpShift S) {n : ℕ} {x : Ordinal.{0}}
    (hx1 : Bc.bcC S n < x) (hx2 : x < Bc.bcC S (n + 1)) (hU : UpsPt x)
    (hnr : ∀ l, IsRestartIdx l → x ≠ upsilon l) : CdTCAt S n x := by
  obtain ⟨μ0, j, hμ0, h1, h2⟩ := tpBlock hU hnr
  obtain ⟨ζ, -, rfl⟩ := upsPt_iff_upsilon.1 hU
  obtain ⟨lam, hlam, hL⟩ := tpIdx S n
  obtain ⟨b, hb, hbI⟩ := tpBotI j
  have hT : ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 < ω * ω := tpStdIdx_lt j
  have h1' : μ0 + b < ζ := by rw [← hbI]; exact tpUps_lt_iff.1 h1
  have h2' : ζ ≤ μ0 + (ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) := by
    rw [← add_assoc]; exact tpUps_le_iff.1 h2
  have hlζ : lam < ζ := by rw [hL] at hx1; exact tpUps_lt_iff.1 hx1
  have hle : lam ≤ μ0 := by
    by_contra hlt
    push Not at hlt
    exact absurd (h2'.trans_lt (tpAdd_lt hlam (mult_of hμ0) hT hlt)) (not_lt.2 hlζ.le)
  have hμr : IsRestartIdx μ0 := tpPart_ri hlam (mult_of hμ0) hle
  have hμζ : μ0 ≤ ζ := le_self_add.trans h1'.le
  have hμn : Bc.bcC S n ≤ upsilon μ0 := by rw [hL]; exact tpUps_le_iff.2 hle
  have hμx : upsilon μ0 < Bc.bcC S (n + 1) := (tpUps_le_iff.2 hμζ).trans_lt hx2
  obtain ⟨μ', hμ', hB⟩ := hsh n μ0 hμr hμn hμx
  -- `ζ = μ0 + β`
  obtain ⟨β, rfl⟩ := exists_add_of_le hμζ
  have hβT : β ≤ ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 := (add_le_add_iff_left μ0).1 h2'
  have hβ : β < ω * ω := hβT.trans_lt hT
  have hbβ : b < β := (add_lt_add_iff_left μ0).1 h1'
  -- the top of the block is below `L(n+2)`
  obtain ⟨lam1, hlam1, hL1⟩ := tpIdx S (n + 1)
  have htop : upsilon (μ0 + (ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1)) < Bc.bcC S (n + 1) := by
    have hμl1 : μ0 < lam1 := by rw [hL1] at hμx; exact tpUps_lt_iff.1 hμx
    rw [hL1]; exact tpUps_lt_iff.2 (tpAdd_lt hlam1 (mult_of hμ0) hT hμl1)
  have hBx := hB β hβ hx2
  have hBt := hB _ hT htop
  have hC0 : upsilon (μ0 + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) < nuC := by
    rw [add_assoc]; exact (htop.trans (cxC_lt_L1 n)).trans_le hν
  have hC1 : upsilon (μ' + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) < nuC := by
    rw [add_assoc, ← hBt]; exact (Bc.bcB_bound' S n _ htop).trans_le hν
  refine Or.inl ⟨_, htop, ?_, ?_⟩
  · rw [← add_assoc]; exact tpBlock_reach hU hμ0 h1 h2 hC0
  · rw [hBx, hBt, ← add_assoc]
    refine tpBlock_reach (upsPt_upsilon ?_) (Or.inr hμ') ?_ ?_ hC1
    · exact lt_of_lt_of_le (pos_iff_ne_zero.2 hμ'.1) le_self_add
    · rw [hbI]; exact tpUps_lt_iff.2 ((add_lt_add_iff_left μ').2 hbβ)
    · rw [add_assoc]; exact tpUps_le_iff.2 ((add_le_add_iff_left μ').2 hβT)

/-- **The `R₁⁺`-reach moves with `B_n`** at the non-`υ`-points of the windows `(L(n+1), L(n+2))`. -/
def TpLhMove (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ x r, Bc.bcC S n < x → x < Bc.bcC S (n + 1) → ¬ UpsPt x → IsLh1 x r →
    IsLh1 (Bc.bcB S n x) (Bc.bcB S n r)

/-- **The `R₁⁺`-reach moves with `B_n`** at the indecomposable non-`υ`-points of the windows. -/
def TpLhPrin (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ x r, Bc.bcC S n < x → x < Bc.bcC S (n + 1) → ¬ UpsPt x → Indec x → IsLh1 x r →
    IsLh1 (Bc.bcB S n x) (Bc.bcB S n r)

/-- `B_n` keeps decomposable points of `[0, L(n+2))`. -/
theorem tpDecomp_B {n : ℕ} {x : Ordinal.{0}} (hx : x < Bc.bcC S (n + 1)) (hI : ¬ Indec x)
    (h0 : x ≠ 0) : ¬ Indec (Bc.bcB S n x) := by
  have hD : DecompR0 x := not_not.1 hI
  rcases hD with h | ⟨y, z, hy, hz, rfl⟩
  · exact absurd h h0
  intro hI'
  apply hI'
  right
  have hm := Bc.bcB_mono' S n
  have hω : ∀ w, w < Bc.bcC S (n + 1) → w < Nc.ncL S ω := fun w hw => hw.trans (Bc.bcC_lt S (n + 1))
  have hyL : y < Bc.bcC S (n + 1) := hy.trans hx
  have hzL : z < Bc.bcC S (n + 1) := hz.trans hx
  refine ⟨Bc.bcB S n y, Bc.bcB S n z, hm hyL hx hy, hm hzL hx hz, ?_⟩
  exact (Bc.bcB_add (hω y hyL) (hω z hzL)).symm

/-- **Only the indecomposable points remain**: `TpLhPrin` gives `TpLhMove`. -/
theorem tpLhMove_of_prin (h : TpLhPrin S) : TpLhMove S := by
  intro n x r hx1 hx2 hU hr
  by_cases hI : Indec x
  · exact h n x r hx1 hx2 hU hI hr
  · have hx0 : x ≠ 0 := (lt_of_le_of_lt zero_le hx1).ne'
    have e : r = x := Lh.lhUnique hr (Lh.lhDecomp hI)
    subst e
    exact Lh.lhDecomp (tpDecomp_B hx2 hI hx0)

/-- **(TC) at a non-`υ`-point of the window**, given `L(ω+1) ≤ ν_C`, the shift and `TpLhMove`. -/
theorem tpTC_off (hν : Nc.ncL S (ω + 1) ≤ nuC) (hsh : TpShift S) (hlh : TpLhMove S) {n : ℕ}
    {x : Ordinal.{0}} (hx1 : Bc.bcC S n < x) (hx2 : x < Bc.bcC S (n + 1)) (hU : ¬ UpsPt x) :
    CdTCAt S n x := by
  have hxC : x < nuC := (hx2.trans (cxC_lt_L1 n)).trans_le hν
  obtain ⟨ξ, r, h1, -, hr, -, hr2, -⟩ := Lh.lhSk_all hxC hU
  have hrL : r < Bc.bcC S (n + 1) := hr2.trans_le (cxUps_succ_le h1 hx2)
  have hr1 : IsLh1 x r := (Lh.lhSk_reach hxC hU).1 hr
  have hB := hlh n x r hx1 hx2 hU hr1
  have hBU : ¬ UpsPt (Bc.bcB S n x) := fun h' => hU (tpUpsRefl hsh hx1.le hx2 h')
  have hBxC : Bc.bcB S n x < nuC := (Bc.bcB_bound' S n x hx2).trans_le hν
  exact Or.inl ⟨r, hrL, hr, (Lh.lhSk_reach hBxC hBU).2 hB⟩

/-- **`CxTCtopOff` from (CL), `L(ω+1) ≤ ν_C`, the shift and `TpLhMove`.** -/
theorem tpTCtopOff (hC : CdCL S) (hν : Nc.ncL S (ω + 1) ≤ nuC) (hsh : TpShift S)
    (hlh : TpLhMove S) : CxTCtopOff S := by
  intro n x h1 h2 hnr
  by_cases hU : UpsPt x
  · refine tpTC_ups hν hsh h1 h2 hU fun l hl he => hnr l ?_ he
    exact tpRange_win hC hl (he ▸ h1) (he ▸ h2)
  · exact tpTC_off hν hsh hlh h1 h2 hU

/-- **`CxTCtop` from CapV below `L(ω)`, (CL), `L(ω+1) ≤ ν_C`, the shift and `TpLhMove`.** -/
theorem tpTCtop (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CdCapV S l) (hC : CdCL S)
    (hν : Nc.ncL S (ω + 1) ≤ nuC) (hsh : TpShift S) (hlh : TpLhMove S) : CxTCtop S :=
  cxTCtop_of hV (tpTCtopOff hC hν hsh hlh)

end Googology.Trans.PoR.InaccPsi.R2.Tp

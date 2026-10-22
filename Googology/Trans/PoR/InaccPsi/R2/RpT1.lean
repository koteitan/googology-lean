import Googology.Trans.PoR.InaccPsi.R2.RpRead
import Googology.Trans.PoR.InaccPsi.R2.RnT1

/-!
# The first block below `T₁`, and the road with the block covering above it

`T₁ = ψ_{Ω₂}(Ω₂^{Ω₂+1})` (`Rn.rnT1`), `O = Ω₁^{Ω₁}` (`Le.leOe (Om 1)`), `G(ζ) = ψ_{Ω₂}(Ω_ω + θ₂·ζ)`,
`A = A_{η_μ}`, `Θ_μ` the reading, `RpBlk` as in `Rp.RpBlk`.

* `rpBlk_T1` (**the first block is covered up to `1 + O·Ω₁`**): at a Range restart `μ` below `L(ω)`, `T₁` is an
  atom, `T₁ < θ ≤ G(1)`, and `ψ_{Ω₁}(A + ζ) ≤ Θ_μ(T₁) = ψ_{Ω₁}(A + 1 + O·Ω₁)` for every `ζ ≤ 1 + O·Ω₁`
  (`Rn.rnTopT1`, `Ld.ldTheta`);
* `RpBlkHi S μ` (**the block covering without the part read by `T₁`**: `RpBlk` asked only at `x ≥ 1`, and at
  `x = 0` only for `ζ > 1 + O·Ω₁`), `rpBlk_of_hi` (**`RpBlkHi` gives `RpBlk`**), `rpReadAll_of_hi`;
* `rpRoad_hi` (**the road** of `Rp.rpRoad_read` with `RpBlkHi` at the Range restarts below `L(ω)` with code
  `G' + 1`).

No new axiom.  New definition (hypothesis name only): `RpBlkHi`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **The first block is covered up to `1 + O·Ω₁` by the atom `T₁`.** -/
theorem rpBlk_T1 {μ ζ : Ordinal.{0}} (hR : CdRange S μ) (hω : upsilon μ < Nc.ncL S ω)
    (hζ : ζ ≤ 1 + Le.leOe (Om 1) * Om 1) :
    Rn.rnT1 S ∈ Ls.lsAt S (ConjT.Aη S (cdEta S μ)) (upsilon μ) ∧ Rn.rnT1 S < Lc.lcG S 1 ∧
      S.psi (ConjT.Aη S (cdEta S μ) + ζ) (Om 1) ≤ cdTheta S μ (Rn.rnT1 S) := by
  have hX : upsilon μ < Nm.Pv S (Om ω + Nc.ncPp S * ω) := by rw [← Lw.lw_L_eq]; exact hω
  obtain ⟨-, -, hown⟩ := Rc.rcOwn hR.1 hω
  have hρ : S.psi (ConjT.Aη S (cdEta S μ)) (Om 1) = upsilon μ := Ls.lsPv_range hR
  have hT := Rn.rnTopT1 hR.1 hX hown hρ
  rw [← Ld.ldTheta hR.1 hX Rn.rnT1_lt_Om2.le] at hT
  refine ⟨?_, Rn.rnT1_lt_th.trans_le ?_, ?_⟩
  · rw [Le.leAt_eq]; exact Rn.rnT1_atom
  · exact (psi_mono (S := S) (InR_Om_succ 1) le_self_add).1
  · rw [hT, add_assoc]
    exact (psi_mono (S := S) Low.InR_Om_one (add_le_add le_rfl hζ)).1

/-- **The block covering without the part read by `T₁`.** -/
def RpBlkHi (S : InaccSeq.{0}) (μ : Ordinal.{0}) : Prop :=
  ∀ x < upsilon μ, ∀ ζ < ConjT.th S, (x = 0 → 1 + Le.leOe (Om 1) * Om 1 < ζ) →
    ∃ t ∈ Ls.lsAt S (ConjT.Aη S (cdEta S μ)) (upsilon μ), t < Lc.lcG S (x + 1) ∧
      S.psi (ConjT.Aη S (cdEta S μ) + (ConjT.th S * x + ζ)) (Om 1) ≤ cdTheta S μ t

/-- **`RpBlkHi` gives `RpBlk`** at a Range restart below `L(ω)`. -/
theorem rpBlk_of_hi {μ : Ordinal.{0}} (hR : CdRange S μ) (hω : upsilon μ < Nc.ncL S ω)
    (h : RpBlkHi S μ) : RpBlk S μ := by
  intro x hx ζ hζ
  by_cases hlow : x = 0 ∧ ζ ≤ 1 + Le.leOe (Om 1) * Om 1
  · obtain ⟨rfl, hζ'⟩ := hlow
    obtain ⟨hat, hlt, hle⟩ := rpBlk_T1 hR hω hζ'
    refine ⟨Rn.rnT1 S, hat, by rw [zero_add]; exact hlt, ?_⟩
    rw [mul_zero, zero_add]; exact hle
  · refine h x hx ζ hζ fun hx0 => ?_
    by_contra hc
    exact hlow ⟨hx0, not_lt.1 hc⟩

/-- `RpBlkHi` at every Range restart below `L(ω)` with code `G' + 1` gives `RpReadAll S k`. -/
theorem rpReadAll_of_hi {k : ℕ}
    (h : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → cdCode S μ = Ls.lsG S (k + 1) + 1 → RpBlkHi S μ) :
    RpReadAll S k :=
  rpReadAll_of_blk fun μ hR hω hc => rpBlk_of_hi hR hω (h μ hR hω hc)

/-- **The road with `RpLnOut` and `RpBlkHi`** at the Range restarts below `L(ω)` with code `G' + 1`. -/
theorem rpRoad_hi {k : ℕ} (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S)
    (hblk : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → cdCode S μ = Ls.lsG S (k + 1) + 1 → RpBlkHi S μ)
    (h0 : Lr.LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Nc.ncL S 0)))
    (hn : ∀ n : ℕ, Lr.LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
    (hout : RpLnOut S)
    (hgap : Lr.LrGap S (Nc.ncL S ω) (Nc.ncL S (ω + 1)) (upsilon (Nc.ncL S ω + Nc.ncL S ω)))
    (hmove : Cx.CxStdMoveTop S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  rpRoad_read hU hO hL hV hVt hEQ htop (rpReadAll_of_hi hblk) h0 hn hout hgap hmove

end Googology.Trans.PoR.InaccPsi.R2.Rp

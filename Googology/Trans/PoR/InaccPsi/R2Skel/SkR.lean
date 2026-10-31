import Googology.Trans.PoR.InaccPsi.R2.WdRoad
import Googology.Trans.PoR.InaccPsi.R2.WbNoGo
import Googology.Trans.PoR.InaccPsi.R2.VxDyn
import Googology.Trans.PoR.InaccPsi.R2.VtDynTop
import Googology.Trans.PoR.InaccPsi.R2.RyNF
import Googology.Trans.PoR.InaccPsi.R2.RxLv
import Googology.Trans.PoR.InaccPsi.R2.RoW
import Googology.Trans.PoR.InaccPsi.R2.WgFam
import Googology.Trans.PoR.InaccPsi.R2.WgTh
import Googology.Trans.PoR.InaccPsi.R2.WlLow
import Googology.Trans.PoR.InaccPsi.R2.WrMid

/-!
# Skeleton, part "readings": the reading move `hν → Wd.WdThLow S`

Top node `skRead S : L(ω+1) ≤ ν_C → Wd.WdThLow S` (the hypothesis `hT` of `Wd.wdRoadL`).

`Θ_λ = gxTh ρ_λ (ldAtR λ)`, `m_λ = cdCode`, `θ = ψ_{Ω₂}(Ω_ω)`, `A = A_{η_λ} = Ω_ω + θ·η_λ`, `θ⁺ = Lj.ljThP`,
`M_W = Rn.rnMW = ψ_{Ω₂}(Ω_ω+Ω₂)`, `Y₃ = Ug.ugY`, `Γ = ggGam` (least strongly critical above `Ω₁`),
`hν := L(ω+1) ≤ ν_C`, "window" = the hypotheses of `Wd.WdThLow` up to `ρ_λ < m_λ`.

Every node's docstring starts with STATUS, SIZE, one line of math.  `sorry` only as the whole proof of an OPEN leaf
or of a REFUTED node kept for the record.

Round 110 (leaf read40): the refuted one-image top `skTopDyn` is replaced by the family law `skTopFam`
(`Wg.WgTopFamAll`: one image `X̂_e(β)` per exponent `e` and base `β`); `skWallBase`, `skWallStep` take it as their
hypothesis; `skThVal` is REDUCED to its lower half `skThLow` (the upper half `skThUp` is `Wg.wgTheta_le`).
Round 111 (leaf read41): `skThLow` is PROVED (`Wl.wlThLow`: the lift of `Rx.rxBlkTh` taken at the base `Ω_{k+2}`
for the offsets `ζ < ψ_{Ω₂}(Ω_{k+1})`, `Wl.wlBlk0`), so `skThVal`, `skBlkLaw`, `skWallTh` are PROVED (all their
children are proved).
Round 112 (leaf read42): `Wd.WdAtWall` is stated only at windows with `F_W ≤ m_λ < θ⁺`, but `Rn.RnThMoveM` asks
windows with `m_λ ≥ θ⁺`, so `skMidAssemble` cannot use its wall hypothesis (SUSPECT, REPLACED).  The wall is
restated without code hypotheses (`Wr.WrWallCF`; `WallBelow` lost its code hypotheses), `skWallCF` gives it, `skWall`
follows (`Wr.wrWall_of_cf`), and `skMidCF` (`Wr.wrMid`: `WrWallCF ⇒ RnThMoveM`) is PROVED.  This file imports the
new module `R2.WrMid`: it can be checked only after the merge.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2Skel.SkR

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Gg

/-! ## Statement names (hypothesis shapes only) -/

/-- The reading move at the window codes with `e(η_λ) ≤ Γ` and `Θ_λ(m_λ) < δ_λ·ω`. -/
def LowExpMove (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    cdExp (cdEta S l) ≤ ggGam → cdTheta S l (cdCode S l) < cdDelta l * ω →
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l')

/-- The reading move at the window codes with `e(η_λ) > Γ` and `m_λ < θ⁺`. -/
def MidMove (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    ggGam < cdExp (cdEta S l) → cdCode S l < Lj.ljThP S →
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l')

/-- The reading move at the window codes `m_λ > M_W` read below `δ_λ·ω`. -/
def FarLowMove (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    Rn.rnMW S < cdCode S l → cdTheta S l (cdCode S l) < cdDelta l * ω →
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l')

/-- `Wr.WrWallCF` (the wall with no code hypothesis) with the atom bound `s < b` in place of `s ≤ θ`
(round 112: the code hypotheses `ρ_λ < m_λ`, `F_W ≤ m_λ < θ⁺` are dropped). -/
def WallBelow (S : InaccSeq.{0}) (b : Ordinal.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
    ∀ s ∈ ldAtR S l, S.psi (Ug.ugY S) (Om (1 + 1)) ≤ s → s < b →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)

/-- `Wd.WdAtWall` at the single atom `s = θ`. -/
def WallAtTheta (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    Le.leFWW S ≤ cdCode S l → cdCode S l < Lj.ljThP S →
    ConjT.th S ∈ ldAtR S l →
      MvD S (ConjT.th S) ∧ Bc.bcB S n (ConjT.th S) ∈ ldAtR S l' ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n (ConjT.th S)) =
          Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) (ConjT.th S))

/-- The level bound `ψ_{Ω₂}(Ω_{k+4})`. -/
noncomputable def lev (S : InaccSeq.{0}) (k : ℕ) : Ordinal.{0} :=
  S.psi (Om ((k + 4 : ℕ) : Ordinal.{0})) (Om (1 + 1))

/-- The dynamic tops at `X = Ω_{k+3}` over every base `β ≥ 0`, one image `X̂(β)` per sub-base. -/
def TopDynAll (S : InaccSeq.{0}) : Prop :=
  ∀ (k : ℕ) (l ηx A : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
    A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l →
    ∃ Xh : Ordinal.{0} → Ordinal.{0}, ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) →
      Vt.VtTopDyn S l 0 (Om ((k + 3 : ℕ) : Ordinal.{0})) Xh e

/-- The block law at the base `Ω_ω` at every restart where `θ` is an atom. -/
def BlkLaw (S : InaccSeq.{0}) : Prop :=
  ∀ (l ηx A : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
    A ∈ S.CSet A (S.psi A (Om 1)) → A = ConjT.Aη S (cdEta S l) → ConjT.th S ∈ ldAtR S l →
    ∀ c, GxCl (upsilon l) (ldAtR S l) c → c < Rn.rnMW S → Om ω + c < A →
      gxTh (upsilon l) (ldAtR S l) (S.psi (Om ω + c) (Om (1 + 1))) =
        S.psi (A + ConjT.th S + gxTh (upsilon l) (ldAtR S l) c) (Om 1)

/-! ## Leaves and reductions -/

/-- STATUS: PROVED (Mw.mwEQlong_gam, Mx.mxEQ_gam, Wd.wdk_move, Cd.cdk_inj)
SIZE: S
`e(η_λ) ≤ Γ ∧ Θ_λ(m_λ) < δ_λ·ω ⇒ B_n Θ_λ(m_λ) = Θ_{λ'}(m_{λ'})` (EQ there is unconditional; `k_{λ'}` injective). -/
theorem skLowExp (S : InaccSeq.{0}) : Nc.ncL S (ω + 1) ≤ nuC → LowExpMove S := by
  intro hν n l l' hR h1 hr hl' hB hm he hw
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have hE : Bc.bcB S n (cdk l (cdTheta S l (cdCode S l))) = cdk l' (cdTheta S l' (cdCode S l')) := by
    rcases he.lt_or_eq with he | he
    · exact Mw.mwEQlong_gam hν hR h1 hr hl' hB hm he
    · exact mxEQ_gam hν hR h1 hr hl' hB he
  rw [← Wd.wdk_move hν hR.1 hl' h1 hδr hB hw] at hE
  exact (cdk_inj l').1 hE

/-- STATUS: PROVED (Wd.wdAtMove26_of_wall, Wa.waLjAt_of_ux, Lj.ljLeThMoveU_of_at, Le.leThMoveT_of_U,
Le.leThMoveS_of_T, Ld.ldThMoveR_of_S, Ld.ldThMoveQ_of_R, Ld.ldThMoveW_of_Q, Mx.mxThMove_of_W, Lj.ljThMoveQ_of_at)
SIZE: S
`WdAtWall ⇒ ∀ window λ, Γ < e(η_λ), m_λ < θ⁺ : B_n Θ_λ(m_λ) = Θ_{λ'}(m_{λ'})`. -/
theorem skBelowThP (S : InaccSeq.{0}) : Wd.WdAtWall S → MidMove S := by
  intro h n l l' hR h1 hr hl' hB hm he hP
  have hat : Lj.LjAtMove S := Wa.waLjAt_of_ux (Wd.wdAtMove26_of_wall h)
  have hRm : LdThMoveR S :=
    ldThMoveR_of_S (Le.leThMoveS_of_T (Le.leThMoveT_of_U (Lj.ljLeThMoveU_of_at hat)))
  have hmv : MxThMove S := mxThMove_of_W (ldThMoveW_of_Q (ldThMoveQ_of_R hRm))
  by_cases hθ : cdCode S l ≤ ConjT.th S
  · exact hmv n l l' hR h1 hr hl' hB hm he hθ
  · by_cases hw : cdCode S l ≤ ConjT.th S * ω
    · exact hRm n l l' hR h1 hr hl' hB hm (ldFw_lt_th.trans (not_le.1 hθ)).le hw
    · exact Lj.ljThMoveQ_of_at hat n l l' hR h1 hr hl' hB hm (not_le.1 hw) hP

/-- STATUS: PROVED (Ry.ryTh_nf, Rx.rxOmW_nat, psi_mono, CSet_mono, psi_lt_psi_of_mem)
SIZE: S
`∀ b, ψ₂(b) < θ ⇒ ∃ k < ω, ψ₂(b) < ψ₂(Ω_{k+4})`. -/
theorem skThCof (S : InaccSeq.{0}) :
    ∀ b, S.psi b (Om (1 + 1)) < ConjT.th S → ∃ k : ℕ, S.psi b (Om (1 + 1)) < lev S k := by
  intro b hb
  obtain ⟨d, hdW, hdeq, hdown, -⟩ := Ry.ryTh_nf hb
  obtain ⟨k, hk⟩ := Rx.rxOmW_nat hdW
  refine ⟨k, ?_⟩
  have hlt : d < Om ((k + 4 : ℕ) : Ordinal.{0}) :=
    hk.trans (Om_lt_Om.2 (by exact_mod_cast (show k < k + 4 by omega)))
  have hle := psi_mono (S := S) (InR_Om_succ 1) hlt.le
  have hmem : d ∈ S.CSet (Om ((k + 4 : ℕ) : Ordinal.{0}))
      (S.psi (Om ((k + 4 : ℕ) : Ordinal.{0})) (Om (1 + 1))) := hle.2 hdown
  rw [← hdeq]
  exact psi_lt_psi_of_mem (InR_Om_succ 1) hlt hmem

/-- STATUS: REFUTED (SkRX.skrxTopDynAll_false: one image X̂ for e = 0 and e = 1 at k = 0 is impossible, SkRX.skrxDyn01);
REPLACED by skTopFam (no node uses it any more)
SIZE: M
`∀ k, ∀ restart λ, A own, ψ₁(A) = ρ_λ : ∃ X̂ : base ↦ image, ∀ e < Ω₂ in H_λ, ∀ β ≥ 0 :
Θ(ψ₂(β + Ω₂^{Ω_{k+3}+e})) = ψ₁(Â_β + Ω₁^{X̂(β) + Θ e})` (one image per sub-base; Vx.vxNoCompat forbids a constant
X̂; known only at X = Y₃, b = Ω₃: Vt.vtTopY3_all_piecewise). -/
theorem skTopDyn (S : InaccSeq.{0}) : TopDynAll S := by
  sorry

/-- STATUS: OPEN
SIZE: M
`∀ k, ∀ restart λ, A own, ψ₁(A) = ρ_λ, ∀ code e < Ω₂ : ∃ X̂_e : base ↦ image, ∀ base β :
Θ(ψ₂(β + Ω₂^{Ω_{k+3}+e})) = ψ₁(Â_β + Ω₁^{X̂_e(β) + Θ e})` (`Wg.WgTopFamAll`; per base by `Wg.wgDyn_iff_pt`).
REFUTE FIRST: NO EVIDENCE.  `SkRX.skrxDyn01` does not apply (`Wg.wgSep01`: X̂₀(0) ≤ Y₂ < X̂₀(Ω₃) ≤ X̂₁(0) is
consistent; the contradiction is the case X̂₁ = X̂₀); `Vx.vxDyn_le0` / `vxDyn_gtOm3` / `vxDyn_nonconst` / `vxNoCompat`
constrain X̂₀ only; `Vn.vnTop_Om3`, `Vq.vqNoTop_Om3` refute constant images only; `Wb.wbNoY` / `wbNoIt` refute the
image Y_{k+2} at β = 0, not every image.  Proved part: e = 0 at β = 0 (`skTopFam0`).  Open: every other base
(β = Ω₃·γ, γ ≥ 1, at e = 0: no Lean value of Θ(ψ₂(Ω₃·γ + Ω₃))) and e ≥ 1 (β = 0, e = 1: no value of Θ(ψ₂(Ω₃·Ω₂))). -/
theorem skTopFam (S : InaccSeq.{0}) : Wg.WgTopFamAll S := by
  sorry

/-- STATUS: PROVED (Wg.wgTop0_base0, Wg.wgTop0_base0_wit)
SIZE: S
Non-vacuity of skTopFam at k = 0, e = 0, β = 0: `Θ(ψ₂(Ω₃)) = ψ₁(A+1+Ω₁^{Y₂})` (image X̂₀(0) = Y₂), at every restart
with an own A, in particular at the witness restart of SkRX.skrxTopDynAll_false (the restart of m* = L(0)). -/
theorem skTopFam0 (S : InaccSeq.{0}) :
    ∀ (l ηx A : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l →
      Wg.WgTopAt S l (Om (1 + 1 + 1)) (S.psi (Om (1 + 1)) (Om (1 + 1))) 0 0 :=
  fun _ _ _ hl hX hA hρ => Wg.wgTop0_base0 hl hX hA hρ

/-- STATUS: PROVED (Wg.wgSep01)
SIZE: S
REFUTE-FIRST record for skTopFam: `VtTopDyn λ 0 Ω₃ X̂₀ 0 ∧ VtTopDyn λ 0 Ω₃ X̂₁ 1 ⇒ X̂₀(0) ≤ Y₂ < X̂₀(Ω₃) ≤ X̂₁(0)`
(so the image must depend on e; SkRX.skrxDyn01 is the case X̂₁ = X̂₀). -/
theorem skTopSep (S : InaccSeq.{0}) :
    ∀ (l ηx A : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l →
      ∀ X0 X1 : Ordinal.{0} → Ordinal.{0}, Vt.VtTopDyn S l 0 (Om (1 + 1 + 1)) X0 0 →
        Vt.VtTopDyn S l 0 (Om (1 + 1 + 1)) X1 1 →
        X0 0 ≤ S.psi (Om (1 + 1)) (Om (1 + 1)) ∧ S.psi (Om (1 + 1)) (Om (1 + 1)) < X0 (Om (1 + 1 + 1)) ∧
          X0 (Om (1 + 1 + 1)) ≤ X1 0 :=
  fun _ _ _ hl hX hA hρ _ _ h0 h1 => Wg.wgSep01 hl hX hA hρ h0 h1

/-- STATUS: OPEN (RISK: the family law fixes no B_n-move of the images X̂_e; the step will likely need, in addition,
`B_n X̂^λ_e(β) = X̂^{λ'}_{B_n e}(B_n β)`, which is itself a move statement; round 112: for own images that move IS the
atom move at T_{X+e}(β), Wr.wrImgMove_iff, so it cannot be added as a hypothesis without assuming the conclusion)
(round 112: CHANGED to the code-free WallBelow)
SIZE: L
`TopFamAll ∧ hν ⇒ every atom ψ₂(Y₃) ≤ s < ψ₂(Ω₄) moves: MvD s, B_n s ∈ At_{λ'}, Θ_{λ'}(B_n s) = B_n Θ_λ(s)`
(was SUSPECT with the refuted TopDynAll; now with the unrefuted family law Wg.WgTopFamAll)
(first block past the Y₃ wall; needs the Uq prefixes / Uu level system with the bound as a field and the image
Vb.vbT, and vqStepA ported to VtTopDyn).  L: no Lean statement of the level system past Y₃ exists yet. -/
theorem skWallBase (S : InaccSeq.{0}) : Wg.WgTopFamAll S → Nc.ncL S (ω + 1) ≤ nuC → WallBelow S (lev S 0) := by
  sorry

/-- STATUS: OPEN (RISK as skWallBase: no B_n-move of the images in the hypothesis; Wr.wrImgMove_iff)
(round 112: CHANGED to the code-free WallBelow)
SIZE: L
`TopFamAll ∧ hν ⇒ ∀ k, (atoms < ψ₂(Ω_{k+4}) move) ⇒ (atoms < ψ₂(Ω_{k+5}) move)` (one level up; the step
Ω_{k+3} → Ω_{k+4} of the readings with sub-base images; Wb.wbKe_sup_it / wbTe_gt_Om give the layer facts).
L: same missing level system as skWallBase, generic in k. -/
theorem skWallStep (S : InaccSeq.{0}) : Wg.WgTopFamAll S → Nc.ncL S (ω + 1) ≤ nuC →
    ∀ k : ℕ, WallBelow S (lev S k) → WallBelow S (lev S (k + 1)) := by
  sorry

/-- STATUS: REDUCED (skTopFam, skWallBase, skWallStep; no longer through the REFUTED skTopDyn)
SIZE: L
`hν ⇒ ∀ k < ω, every atom ψ₂(Y₃) ≤ s < ψ₂(Ω_{k+4}) moves` (induction on k). -/
theorem skWallLevAll (S : InaccSeq.{0}) : Nc.ncL S (ω + 1) ≤ nuC → ∀ k : ℕ, WallBelow S (lev S k) := by
  intro hν k
  induction k with
  | zero => exact skWallBase S (skTopFam S) hν
  | succ k IH => exact skWallStep S (skTopFam S) hν k IH

/-- STATUS: REDUCED (skThCof, skWallLevAll)
SIZE: L
`hν ⇒ every atom ψ₂(Y₃) ≤ s < θ moves at every window` (round 112: statement `Wr.WrWallLowCF`, no code hypothesis). -/
theorem skWallLow (S : InaccSeq.{0}) : Nc.ncL S (ω + 1) ≤ nuC → Wr.WrWallLowCF S := by
  intro hν n l l' hR h1 hr hl' hB s hs hsY hsθ IH
  obtain ⟨a, ha1, ha2, rfl⟩ := hs
  obtain ⟨k, hk⟩ := skThCof S a hsθ
  exact skWallLevAll S hν k n l l' hR h1 hr hl' hB _ ⟨a, ha1, ha2, rfl⟩ hsY hk IH

/-- STATUS: PROVED (Wg.wgTheta_le, from Ld.ldTheta_le_psi, Wg.wgOwnEta)
SIZE: S
Upper half of skThVal: `restart λ, A own, ψ₁(A) = ρ_λ ⇒ Θ_λ(θ) ≤ ψ₁(A + θ)` (sharpens Wb.wbTheta_lt: A + θ + 1). -/
theorem skThUp (S : InaccSeq.{0}) :
    ∀ (l ηx A : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l →
      gxTh (upsilon l) (ldAtR S l) (ConjT.th S) ≤ S.psi (A + ConjT.th S) (Om 1) :=
  fun _ _ _ hl hX hA hρ => Wg.wgTheta_le hl hX hA hρ

/-- STATUS: PROVED (Wl.wlThLow, from Wl.wlBlk0, Wl.wlL_memB, Wl.wlCof, Rx.rxLift, Wg.wgLow_of_all; round 111)
SIZE: L
Lower half of skThVal: `restart λ, A own, ψ₁(A) = ρ_λ, θ ∈ At_λ ⇒ ψ₁(A_{η_λ} + θ) ≤ Θ_λ(θ)` (`Wg.WgThLow`;
sufficient: ψ₁(A+ζ) < Θ_λ(θ) for every ζ < θ, Wg.wgLow_of_all).  REFUTE FIRST: NO EVIDENCE (the known readings below θ,
Vn.vnRead_Y3, Vq.vqRead_Om3Y3, Ro.roTheta_th_gt, are far below ψ₁(A+θ) and do not decide it).  Blocker: the lift of
Rx.rxBlkTh at the base 0 fails (Rx.rxL_memH needs Ω_ω ≤ a).  Proof (round 111): for ζ < θ pick a member w ≥ ζ over 2
(Rx.rxCofTh) and k with w < B_k = ψ₂(Ω_{k+1}) (Wl.wlCof); lift at the base Ω_{k+2}: ψ₁(A + w) ≤ Θ(ψ₂(Ω_{k+2} + κ w))
(Rx.rxLift on the members below B_k; the transfer κ(e − A) ∈ Cl(Ω_{k+2} + κ w, ·) is Wl.wlL_memB, every collapse
argument of a member of Cl(Ω_{k+1}, B_k) is below Ω_{k+1}), and ψ₂(Ω_{k+2} + κ w) ≤ ψ₂(Ω_{k+3}) < θ.  The hypotheses
"A own", "ψ₁(A) = ρ_λ", "θ ∈ At_λ" are not used. -/
theorem skThLow (S : InaccSeq.{0}) :
    ∀ (l ηx A : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l → ConjT.th S ∈ ldAtR S l →
      Wg.WgThLow S l :=
  fun _ _ _ hl hX _ _ _ => Wl.wlThLow hl hX

/-- STATUS: PROVED (skThUp, skThLow; Wg.wgThVal_of_low; = Wl.wlThVal, which needs no θ ∈ At_λ; round 111)
SIZE: S
`restart λ, A own, ψ₁(A) = ρ_λ, θ ∈ At_λ ⇒ Θ_λ(θ) = ψ₁(A + θ)` (the candidate TRUE value; consistent with
Wb.wbTheta_lt and Ro.roTheta_th_gt; ψ₁(A+1+Ω_ω) is refuted by Wb.wbTheta_ne).  Statement unchanged. -/
theorem skThVal (S : InaccSeq.{0}) :
    ∀ (l ηx A : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l → ConjT.th S ∈ ldAtR S l →
      gxTh (upsilon l) (ldAtR S l) (ConjT.th S) = S.psi (A + ConjT.th S) (Om 1) := by
  intro l ηx A hl hX hA hρ hθ
  exact Wg.wgThVal_of_low hl hX hA hρ (skThLow S l ηx A hl hX hA hρ hθ)

/-- STATUS: PROVED (Cd.cdEta_pv_spec, Bc.bcB_bound', Bc.bcB_fix', Bc.bcB_mono', Gv.gvK_eq, Td.tdK_lt_L)
SIZE: S
`window λ → λ' ⇒ θ ∈ At_{λ'}` (i.e. η_{λ'} ≠ 0, so Ω_ω < A_{λ'}; ρ_{λ'} = B_n ρ_λ > ψ₁(Ω_ω)). -/
theorem skThAtom (S : InaccSeq.{0}) :
    ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
      IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → ConjT.th S ∈ ldAtR S l' := by
  intro n l l' hR h1 hr hl' hB
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans hδr
  have hX' : upsilon l' < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq S, ← hB]; exact Bc.bcB_bound' S n _ h2
  obtain ⟨-, -, -, hpv'⟩ := cdEta_pv_spec (S := S) hl'.1 hX'
  have hη0 : cdEta S l' ≠ 0 := by
    intro h0
    rw [h0] at hpv'
    have hK : Nm.Pv S 0 < Bc.bcC S n := by
      rw [← Gv.gvK_eq S]; exact Td.tdK_lt_L _
    have hfix := Bc.bcB_fix' (S := S) n _ hK
    have hlt := Bc.bcB_mono' (S := S) n (show Nm.Pv S 0 ∈ Set.Iio (Bc.bcC S (n + 1)) from (hK.trans h1).trans h2)
      (show upsilon l ∈ Set.Iio (Bc.bcC S (n + 1)) from h2) (hK.trans h1)
    rw [hfix, hB, ← hpv'] at hlt
    exact lt_irrefl _ hlt
  refine ⟨Om ω, ConjT.OmW_mem (S := S) _ _, ?_, rfl⟩
  show Om ω < Om ω + ConjT.th S * cdEta S l'
  exact lt_add_of_pos_right _ (mul_pos (Sf.sfTh_pos S) (pos_iff_ne_zero.2 hη0))

/-- STATUS: PROVED (skThVal, skThAtom; round 111: all children proved; with Lj.ljB_th, Ld.ldOwnA, Cd.cdEta_pv_spec, Mx.mxUps_succ,
Ld.ldB_psi_add, Bc.bcB_bound')
SIZE: M
`θ atom: MvD θ, B_n θ = θ ∈ At_{λ'}, Θ_{λ'}(θ) = ψ₁(A'+θ) = B_n ψ₁(A+θ) = B_n Θ_λ(θ)`. -/
theorem skWallTh (S : InaccSeq.{0}) : WallAtTheta S := by
  intro n l l' hR h1 hr hl' hB hm _ _ hs
  obtain ⟨hDθ, hBθ⟩ := Lj.ljB_th (S := S) (n := n)
  refine ⟨hDθ, by rw [hBθ]; exact skThAtom S n l l' hR h1 hr hl' hB, ?_⟩
  rw [hBθ]
  have hl := hR.1
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans hδr
  obtain ⟨hX, hown⟩ := ldOwnA hl h2
  obtain ⟨hg, -, -, hpv⟩ := cdEta_pv_spec (S := S) hl.1 hX
  set A := ConjT.Aη S (cdEta S l) with hA_def
  have hρA : S.psi A (Om 1) = upsilon l := hpv
  have hΘ := skThVal S l _ A hl hX hown hρA hs
  have hθ0 : 0 < ConjT.th S := Sf.sfTh_pos S
  have hWA : Om ω < A + ConjT.th S := by
    rw [hA_def]; unfold ConjT.Aη
    exact lt_of_le_of_lt le_self_add (lt_add_of_pos_right _ hθ0)
  have hownθ : A + ConjT.th S ∈ S.CSet (A + ConjT.th S) (S.psi (A + ConjT.th S) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hown) (ConjT.th_mem (S := S) hWA)
  have hu1 : upsilon (l + 1) < cdDelta l :=
    upsilon_normal.strictMono (by
      calc l + 1 < l + ω := (add_lt_add_iff_left l).2 one_lt_omega0
        _ < l + ω + 1 := lt_add_one _)
  have hbX : S.psi (A + ConjT.th S) (Om 1) < Bc.bcC S (n + 1) := by
    rw [← mxUps_succ hl hX]; exact hu1.trans hδr
  obtain ⟨A', hA', hBP, hBd⟩ := ldB_psi_add (n := n) hg (hpv ▸ h1.le) hDθ hownθ hbX
  have hρA' : S.psi A' (Om 1) = upsilon l' := by rw [← hBP, hpv, hB]
  have hX' : upsilon l' < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq S, ← hB]; exact Bc.bcB_bound' S n _ h2
  have hΘ' := skThVal S l' _ A' hl' hX' hA' hρA' (skThAtom S n l l' hR h1 hr hl' hB)
  rw [hΘ', hΘ, hBd, hBθ]

/-- STATUS: REDUCED (skWallLow; Wr.wrWallCF_of_low, Wr.wrAtTh; NEW round 112)
SIZE: L
`hν ⇒ Wr.WrWallCF`: the code-free wall, atoms ψ₂(Y₃) ≤ s < θ (skWallLow) and the atom θ (Wr.wrAtTh, code-free
form of skWallTh). -/
theorem skWallCF (S : InaccSeq.{0}) : Nc.ncL S (ω + 1) ≤ nuC → Wr.WrWallCF S :=
  fun hν => Wr.wrWallCF_of_low (skWallLow S hν)

/-- STATUS: REDUCED (skWallCF; Wr.wrWall_of_cf; round 112: was REDUCED to skWallLow, skWallTh)
SIZE: L
`hν ⇒ WdAtWall` (⇔ Ux.UxAtMove26 by Wd.wdWall_iff): the code-free wall restricted to F_W ≤ m_λ < θ⁺. -/
theorem skWall (S : InaccSeq.{0}) : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdAtWall S :=
  fun hν => Wr.wrWall_of_cf (skWallCF S hν)

/-- STATUS: PROVED (skThVal; Cd.cdEta_pv, Ro.roThW_A; round 111: skThVal proved)
SIZE: S
`Θ_λ(ψ₂(Ω_ω + c)) = ψ₁(A + θ + Θ_λ(c))` for codes c < M_W with Ω_ω + c < A. -/
theorem skBlkLaw (S : InaccSeq.{0}) : BlkLaw S := by
  intro l ηx A hl hX hA hAη hθ
  have hρ : S.psi A (Om 1) = upsilon l := by rw [hAη]; exact cdEta_pv hl.1 hX
  exact Ro.roThW_A hl hX hA hAη (skThVal S l ηx A hl hX hA hρ hθ)

/-- STATUS: SUSPECT (round 112: its hypothesis `hν ⇒ WdAtWall` is stated only at windows with F_W ≤ m_λ < θ⁺,
while RnThMoveM asks windows with m_λ ≥ θ⁺, so the atoms ≤ θ at those windows are not covered; REPLACED by skMidCF,
which takes the code-free wall Wr.WrWallCF; no node uses it)
SIZE: M
`BlkLaw ∧ (hν ⇒ WdAtWall) ∧ hν ⇒ RnThMoveM`: codes θ⁺ ≤ m ≤ M_W are read through the atoms ψ₂(Ω_ω + c) (block
law at λ and λ') and the atoms ≤ θ (WdAtWall); B_n ψ₁(A+θ+x) = ψ₁(A'+θ+B_n x) by Ld.ldB_psi_add (MvD, own).
Needs the gx-recursion of Ld.ldGxStepRec past θ⁺ (atoms up to M_W).  Round 111: the hypothesis BlkLaw is
proved (skBlkLaw PROVED), so this node needs only (hν ⇒ WdAtWall). -/
theorem skMidAssemble (S : InaccSeq.{0}) : BlkLaw S → (Nc.ncL S (ω + 1) ≤ nuC → Wd.WdAtWall S) →
    Nc.ncL S (ω + 1) ≤ nuC → Rn.RnThMoveM S := by
  sorry

/-- STATUS: PROVED (Wr.wrMid, from Wr.wrAtLow, Wr.wrAtBlk, Wr.wrThMW, Ld.ldGxStepRec; NEW round 112, replaces
skMidAssemble)
SIZE: M
`(hν ⇒ Wr.WrWallCF) ∧ hν ⇒ RnThMoveM`: at a window with θ⁺ ≤ m_λ ≤ M_W the code is e = e(η_λ) (cdPi ≤ M_W is
impossible above P(Ω₂)); atoms < θ⁺ move (Le.leAtMove_FWW, Ux.uxAtMoveTop, the wall), atoms ψ₂(Ω_ω + c) move by the
block law at λ and λ' (skBlkLaw's content, Ro.roThW_A with Wl.wlThVal), all codes < M_W move (Ld.ldGxStepRec), and
Θ_λ(M_W) = ψ₁(A + θ + Ω₁) (Wr.wrThMW) moves by Ld.ldB_psi_add.  Checkable only after the merge (imports R2.WrMid). -/
theorem skMidCF (S : InaccSeq.{0}) : (Nc.ncL S (ω + 1) ≤ nuC → Wr.WrWallCF S) →
    Nc.ncL S (ω + 1) ≤ nuC → Rn.RnThMoveM S :=
  fun h hν => Wr.wrMid (h hν)

/-- STATUS: REDUCED (skMidCF, skWallCF; round 112: was skBlkLaw, skWall, skMidAssemble)
SIZE: M
`hν ⇒ RnThMoveM`: the reading move at codes θ⁺ ≤ m_λ ≤ M_W. -/
theorem skThMid (S : InaccSeq.{0}) : Nc.ncL S (ω + 1) ≤ nuC → Rn.RnThMoveM S :=
  skMidCF S (skWallCF S)

/-- STATUS: OPEN
SIZE: L
`hν ⇒ ∀ window λ, m_λ > M_W, Θ_λ(m_λ) < δ_λ·ω : B_n Θ_λ(m_λ) = Θ_{λ'}(m_{λ'})`.  L: no reading Θ_λ(m) is known
for m > M_W (Th.ThObs: the level-shift lift stops at M_W); expected: atoms ψ₂(Ω_ω + Ω₂ + c) with c < P′. -/
theorem skThFar (S : InaccSeq.{0}) : Nc.ncL S (ω + 1) ≤ nuC → FarLowMove S := by
  sorry

/-- STATUS: REDUCED (skThMid, skThFar)
SIZE: L
`hν ⇒ WdThHi`: codes θ⁺ ≤ m ≤ M_W (RnThMoveM) and m > M_W read below δ_λ·ω. -/
theorem skThHi (S : InaccSeq.{0}) : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThHi S := by
  intro hν n l l' hR h1 hr hl' hB hm hP hw
  by_cases hM : cdCode S l ≤ Rn.rnMW S
  · exact skThMid S hν n l l' hR h1 hr hl' hB hm hP hM
  · exact skThFar S hν n l l' hR h1 hr hl' hB hm (not_le.1 hM) hw

/-- STATUS: REDUCED (skLowExp, skBelowThP, skWall, skThHi)
SIZE: L
**Top node** `hν ⇒ Wd.WdThLow`: `B_n Θ_λ(m_λ) = Θ_{λ'}(m_{λ'})` at every window code read below `δ_λ·ω`
(split: e(η_λ) ≤ Γ | m_λ < θ⁺ | m_λ ≥ θ⁺).  This is the hypothesis `hT` of `Wd.wdRoadL`. -/
theorem skRead (S : InaccSeq.{0}) : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S := by
  intro hν n l l' hR h1 hr hl' hB hm hw
  by_cases he : cdExp (cdEta S l) ≤ ggGam
  · exact skLowExp S hν n l l' hR h1 hr hl' hB hm he hw
  · by_cases hP : cdCode S l < Lj.ljThP S
    · exact skBelowThP S (skWall S hν) n l l' hR h1 hr hl' hB hm (not_le.1 he) hP
    · exact skThHi S hν n l l' hR h1 hr hl' hB hm (not_lt.1 hP) hw

/-- STATUS: PROVED (Wd.wdRoadL_hyps)
SIZE: S
Non-vacuity: `CdEQ ⇒ (hν ⇒ WdThLow)` (the top node follows from the road's own conclusion). -/
theorem skRead_of_EQ (S : InaccSeq.{0}) (hEQ : Cd.CdEQ S) : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S :=
  (Wd.wdRoadL_hyps hEQ).1

/-- STATUS: PROVED (Wd.wdRoad_hyps, Wd.wdRn_of, Wd.wdRoadL_hyps)
SIZE: S
Non-vacuity of the OPEN conclusions: `CdEQ ∧ (hν ⇒ UdAtMove25) ⇒ (hν ⇒ WdAtWall) ∧ (hν ⇒ RnThMoveM) ∧ (hν ⇒ FarLowMove)`
(the natural target implies the conclusions of skWall, skMidAssemble, skThFar; no node asks more than the road). -/
theorem skNonVac (S : InaccSeq.{0}) (hEQ : Cd.CdEQ S) (hat : Nc.ncL S (ω + 1) ≤ nuC → Ud.UdAtMove25 S) :
    (Nc.ncL S (ω + 1) ≤ nuC → Wd.WdAtWall S) ∧ (Nc.ncL S (ω + 1) ≤ nuC → Rn.RnThMoveM S) ∧
      (Nc.ncL S (ω + 1) ≤ nuC → FarLowMove S) := by
  obtain ⟨hW, hH, hF⟩ := Wd.wdRoad_hyps hEQ hat
  refine ⟨hW, fun hν => (Wd.wdRn_of hν (hH hν) (hF hν)).1, fun hν => ?_⟩
  intro n l l' hR h1 hr hl' hB hm _ hw
  exact (Wd.wdRoadL_hyps hEQ).1 hν n l l' hR h1 hr hl' hB hm hw

end Googology.Trans.PoR.InaccPsi.R2Skel.SkR

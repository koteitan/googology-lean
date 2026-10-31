import Googology.Trans.PoR.InaccPsi.R2.WdRoad
import Googology.Trans.PoR.InaccPsi.R2.WcSupLo
import Googology.Trans.PoR.InaccPsi.R2.VrRoad
import Googology.Trans.PoR.InaccPsi.R2.TyRng
import Googology.Trans.PoR.InaccPsi.R2Skel.SkF
import Googology.Trans.PoR.InaccPsi.R2.WfRoad
import Googology.Trans.PoR.InaccPsi.R2.WfWin
import Googology.Trans.PoR.InaccPsi.R2.WfRefute
import Googology.Trans.PoR.InaccPsi.R2.WkRead
import Googology.Trans.PoR.InaccPsi.R2.WkCarry

/-!
# Skeleton of the part "supply": the hypotheses `h0` / `hn` of `Wd.wdRoadL`

`L(ξ) = Nc.ncL S ξ`, `a = υ_λ = L(k)`, `u₁ = υ_{λ+1}`, `g = ω^{ω^{u₁+1}}` (the offset of the `Vo.voNoGo` witness),
`β(ν) = (ν − λ) + ω²` (the window chosen at the isolated uncovered Range restart `ν`), `u' = υ_{μ+1}`,
`X = ω^{ω^{u'+1}+1}` (`Wc.wcX`), `m(z) = cdOff(cdExp z)`, `π = π_{υ_μ, υ_λ}`.

Round 116 (leaf "repair the supply road"): the road is replaced.  `Wf.wfRoad` has the conclusion of `Wd.wdRoadL`
with `h0` / `hn` in the RESTRICTED form `Wf.WfVisGen` (the image clause of the carry only for decompositions with
`Wf.WfR`: lo-leaves in `T^{υ_λ}[υ_μ]`, i.e. below `υ_μ` when below `υ_λ`); `Wf.wfVisGen_of_vr` shows the old
statement implies the new one.  NEW top node `skSup`: `h0' ∧ ∀ n, hn' n` of `Wf.wfRoad`; `Root.skNuC` must apply
`Wf.wfRoad` (same arguments) in place of `Wd.wdRoadL`.  The map data `SkMapP` has the restricted exponent clause.
RESTATED nodes: `SkMapP`, `skOffMapW` (now PROVED by `Wf.wfOffMap`), `skImgF`, `skCarryWit`, `skCarryOther`,
`skSupK`, `skGen`, `skVisK`, `skSup`.  NEW nodes: `skPiLo` (PROVED), `skSideRef` (PROVED negation).
The SUSPECT reasons of the refuter (`SkSX.skSX_offMap_free`, `skSX_img_pi`, `skSX_sup_pi`) do not apply to the
restated nodes (`Wf.wfR_skSX_excl`, `Wf.wfSup_lo`, `R2Skel.SkSX.skSX_notTB`).  This file imports the new `Wf`
modules, so it can be checked only after the merge.  Every node is tagged STATUS / SIZE in its docstring.

Round 117 (leaf "WcRead0, then the witness-window leaves", sup39): `skRead0` PROVED (`Wk.wkRead0`: the level-wise
lift with atoms `ψ_{Ω₂}(Ω_{n+1} + κ ζ)` below `θ`), so `skMu` is PROVED.  `skLowerF` RESTATED (a window hypothesis
`∃ w, Ty.TyWin S k w ∧ w < υ_μ`; the old `∀ μ` form asked LOWER at `μ + f z` with no Range / `RzRest` known when
`υ_μ` lies below the window, e.g. at an index `L(j)`, code `P′`) and REDUCED (`Wk.wkLowerF` + the new shared leaf
`skLowRR`); `skCarryWit`, `skCarryOther` carry the window hypothesis, `skSupK` picks `μ` above the window
(`Wk.wkWin_ex`).  `skBigF` REDUCED (`Wk.wkBigF`: vacuous at every offset with `λ + z < ν` since `ν` is not covered)
to the NEW leaf `skBigTop` (the single offset `z = ν − λ`).  This file imports the new `Wk` modules, so it can be
checked only after the merge.
-/

set_option autoImplicit false

namespace R2Skel.SkS

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-! ## Statement abbreviations -/

/-- The context of `Vr.VrVisGen` at `L(k) = υ_λ` on the window `[υ_{L(k)+W(L(k))}, L(k+1))` at the Range restart
`ν`: uncovered, isolated from below. -/
def SkCtx (S : InaccSeq.{0}) (k : ℕ) (l ν : Ordinal.{0}) : Prop :=
  IsRestartIdx l ∧ Nc.ncL S (k : Ordinal.{0}) = upsilon l ∧ CdRange S ν ∧
    upsilon (Nc.ncL S (k : Ordinal.{0}) + Te.teW (Nc.ncL S (k : Ordinal.{0}))) ≤ upsilon ν ∧
    upsilon ν < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ∧ upsilon l < upsilon ν ∧
    ¬ Tk.TkCov S (upsilon l) ν ∧ Tk.TkIso S (upsilon l) ν

/-- The supply restarts `μ`: Range, code `G₂+1`, below `L(ω)`, with the first reading `Wc.WcRead0`. -/
def SkMu (S : InaccSeq.{0}) (μ : Ordinal.{0}) : Prop :=
  CdRange S μ ∧ cdCode S μ = Ls.lsG S (0 + 1 + 1) + 1 ∧ upsilon μ < Nc.ncL S ω ∧ Wc.WcRead0 S μ

/-- The witness window: `ν = λ + g + ω²`. -/
def SkWit (l ν : Ordinal.{0}) : Prop := ν = l + ω ^ ω ^ (upsilon (l + 1) + 1) + ω ^ 2

/-- The map data at the witness window: bound, supply, `Sl.SlOff`, `f g = g'`, and the exponent condition
`π(m z) ≤ m(f z)` at every low offset with `m z ∈ T^{υ_λ}[υ_μ]` (RESTATED round 116: the restricted exponent
clause; `Vy.vyEQ_lo`). -/
def SkMapP (S : InaccSeq.{0}) (l μ : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) (B : Ordinal.{0})
    (Os : Finset Ordinal.{0}) : Prop :=
  μ + B ≤ l ∧ ω ^ 2 ∣ B ∧ upsilon (μ + B) ≤ cdR S μ ∧ Sl.SlOff f Os B ∧
    (ω ^ ω ^ (upsilon (l + 1) + 1) ∈ Os → f (ω ^ ω ^ (upsilon (l + 1) + 1)) = ω ^ ω ^ (upsilon (μ + 1) + 1)) ∧
    ∀ z ∈ Os, 0 < z → ω ^ 2 ∣ z → cdOff (cdExp z) < upsilon (l + 1) →
      cdOff (cdExp z) ∈ TB (upsilon l) (upsilon μ) →
      pi (upsilon μ) (upsilon l) (cdOff (cdExp z)) ≤ cdOff (cdExp (f z))

/-! ## Shared leaves (content of the other parts of the road) -/

/-- STATUS: REDUCED (R2Skel.SkF.skFrontU, Hl.hlU_enum; integration round 115)
SIZE: L
UPPER at every Range restart with `RzRest` (shared with part hUH: below the frontier by `Hl.hlU_enum`, above it
by the frontier part `SkF.skFrontU`).
∀ λ, Range(λ) ∧ RzRest(λ) ⇒ UPPER(λ) -/
theorem skUpRR : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l := by
  intro l hr _
  by_cases h : Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l
  · exact _root_.R2Skel.SkF.skFrontU S l hr h
  · exact (Hl.hlU_enum S hr (lt_of_not_ge h)).1

/-- STATUS: REDUCED (R2Skel.SkF.skFrontL, Hl.hlU_enum; NEW round 117)
SIZE: L
LOWER at every Range restart with `RzRest` (shared with part hLH: below the frontier by `Hl.hlU_enum`, above it
by the frontier part `SkF.skFrontL`).
∀ λ, Range(λ) ∧ RzRest(λ) ⇒ LOWER(λ) -/
theorem skLowRR : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l := by
  intro l hr _
  by_cases h : Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l
  · exact _root_.R2Skel.SkF.skFrontL S l hr h
  · exact (Hl.hlU_enum S hr (lt_of_not_ge h)).2

/-- STATUS: REDUCED (R2Skel.SkF.skFrontU/L/V/Vt, Wd.wdNu; integration round 115)
SIZE: L
`L(ω+1) ≤ ν_C` (shared: `Wd.wdNu` from hUH, hLH, hVH, hVt of the frontier part `SkF`).
L(ω+1) ≤ ν_C -/
theorem skNu : Nc.ncL S (ω + 1) ≤ nuC :=
  Wd.wdNu (_root_.R2Skel.SkF.skFrontU S) (_root_.R2Skel.SkF.skFrontL S) (_root_.R2Skel.SkF.skFrontV S)
    (_root_.R2Skel.SkF.skFrontVt S)

/-! ## The window -/

/-- STATUS: PROVED (by `Pp.ppL_succ_restart`, `Vr.vr_dvd_step`, `upsilon_normal`)
SIZE: S
υ_ν < υ_{λ+β(ν)} ≤ L(k+1) -/
theorem skWin {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) :
    upsilon ν < upsilon (l + (ν - l + ω ^ 2)) ∧
      upsilon (l + (ν - l + ω ^ 2)) ≤ Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) := by
  obtain ⟨-, -, hR, -, h3, h4, -, -⟩ := h
  have hm := upsilon_normal.strictMono
  have hlν : l < ν := hm.lt_iff_lt.1 h4
  have he : l + (ν - l + ω ^ 2) = ν + ω ^ 2 := by
    rw [← add_assoc, Ordinal.add_sub_cancel_of_le hlν.le]
  rw [he]
  obtain ⟨l', hl', e'⟩ := Pp.ppL_succ_restart (S := S) k
  rw [e'] at h3 ⊢
  refine ⟨hm (lt_add_of_pos_right ν (pow_pos omega0_pos 2)), hm.monotone ?_⟩
  exact Vr.vr_dvd_step hR.1.2 hl'.2 (hm.lt_iff_lt.1 h3)

/-! ## The three clauses of `Vr.VrGen` at `β(ν)` -/

/-- STATUS: REDUCED (from `skUpRR`, `skWin`, `Ty.tyInner_rng`)
SIZE: S
∀ g, 0 < g < β(ν), ω² | g ⇒ UPPER(λ+g) -/
theorem skUp {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) :
    ∀ g, 0 < g → g < ν - l + ω ^ 2 → ω ^ 2 ∣ g → CdUpper S (l + g) := by
  intro g hg0 hgβ hgd
  have hm := upsilon_normal.strictMono
  have hl := h.1
  have hr : IsRestartIdx (l + g) :=
    ⟨(lt_of_lt_of_le (pos_iff_ne_zero.2 hl.1) le_self_add).ne', dvd_add hl.2 hgd⟩
  have h1 : Nc.ncL S (k : Ordinal.{0}) < upsilon (l + g) := by
    rw [h.2.1]; exact hm (lt_add_of_pos_right l hg0)
  have h2 : upsilon (l + g) < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) :=
    (hm ((add_lt_add_iff_left l).2 hgβ)).trans_le (skWin h).2
  obtain ⟨hR, hz⟩ := Ty.tyInner_rng (S := S) (k := k) hr h1 h2
  exact skUpRR _ hR hz

/-- STATUS: REDUCED (from the shared leaf `skNu` and `Vr.vrForms_win`, `Te.teUps_L`, `Pp.ppL_lt_omega`, `Qq.qqL_lt_succ`;
no other child)
SIZE: S
ν = λ+g+ω² ⇒ ∀ z < β(ν) = g+ω²·2, ω² | z ⇒ VrForm(λ, β, z) -/
theorem skFormWit {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) (hw : SkWit l ν) :
    ∀ g, 0 < g → g < ν - l + ω ^ 2 → ω ^ 2 ∣ g →
      upsilon (l + (ν - l + ω ^ 2)) ≤ cdR S (l + g) ∨ Vr.VrForm S l (ν - l + ω ^ 2) g := by
  have hm := upsilon_normal.strictMono
  have hlk : l = Nc.ncL S (k : Ordinal.{0}) :=
    hm.injective (h.2.1.symm.trans (Te.teUps_L (S := S) k).symm)
  have hβ : ν - l + ω ^ 2 = ω ^ ω ^ (upsilon (l + 1) + 1) + ω ^ 2 * 2 := by
    have e2 : ∀ x : Ordinal.{0}, x * 2 = x + x := fun x => by
      rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, mul_add, mul_one]
    rw [hw, add_assoc, Ordinal.add_sub_cancel, add_assoc, e2]
  rw [hβ]
  have hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC :=
    ((Pp.ppL_lt_omega k).trans (Qq.qqL_lt_succ S)).le.trans skNu
  obtain ⟨-, -, hF⟩ := Vr.vrForms_win (S := S) k hν
  intro z hz0 hzβ hzd
  rw [hlk] at hzβ ⊢
  exact Or.inr (hF z hz0 hzβ hzd)

/-- STATUS: OPEN
SIZE: L
the forms clause at the other windows (Vr report B'1–B'3: decompositions over several inner segments)
¬(ν = λ+g+ω²) ⇒ ∀ z < β(ν), ω² | z ⇒ υ_{λ+β} ≤ r(λ+z) ∨ VrForm(λ, β, z) -/
theorem skFormOther {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) (hw : ¬ SkWit l ν) :
    ∀ g, 0 < g → g < ν - l + ω ^ 2 → ω ^ 2 ∣ g →
      upsilon (l + (ν - l + ω ^ 2)) ≤ cdR S (l + g) ∨ Vr.VrForm S l (ν - l + ω ^ 2) g := by sorry

/-- STATUS: REDUCED (from `skFormWit`, `skFormOther`)
SIZE: L
∀ z < β(ν), ω² | z ⇒ υ_{λ+β} ≤ r(λ+z) ∨ VrForm(λ, β, z) -/
theorem skForm {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) :
    ∀ g, 0 < g → g < ν - l + ω ^ 2 → ω ^ 2 ∣ g →
      upsilon (l + (ν - l + ω ^ 2)) ≤ cdR S (l + g) ∨ Vr.VrForm S l (ν - l + ω ^ 2) g := by
  by_cases hw : SkWit l ν
  · exact skFormWit h hw
  · exact skFormOther h hw

/-! ## The supply clause `Vr.VrSup` at `β(ν)` -/

/-- STATUS: PROVED (by `Ls.lsNames_M`, `Ls.lsNames_L`, `Qq.qqL_lt_omega`)
SIZE: S
∀ γ < L(k) ∃ μ: Range(μ), γ < υ_μ < L(k) < L(ω), code(μ) = G₂+1 -/
theorem skCodeCof (k : ℕ) : ∀ γ < Nc.ncL S (k : Ordinal.{0}), ∃ μ, CdRange S μ ∧ γ < upsilon μ ∧
    upsilon μ < Nc.ncL S (k : Ordinal.{0}) ∧ cdCode S μ = Ls.lsG S (0 + 1 + 1) + 1 ∧
    upsilon μ < Nc.ncL S ω := by
  intro γ hγ
  rcases k with _ | n
  · have hγ' : γ < Nc.ncL S 0 := by simpa using hγ
    obtain ⟨μ, hR, h1, h2, hc⟩ := Ls.lsNames_M (S := S) 1 γ hγ'
    refine ⟨μ, hR, h1, by simpa using h2, hc, ?_⟩
    exact h2.trans (by simpa using Qq.qqL_lt_omega S 0)
  · obtain ⟨μ, hR, h1, h2, hc⟩ := Ls.lsNames_L (S := S) n 1 γ hγ
    exact ⟨μ, hR, h1, h2, hc, h2.trans (Qq.qqL_lt_omega S (n + 1))⟩

/-- STATUS: PROVED (by `Wk.wkRead0`; round 117.  The lift of `Rx.rxLift` one level at a time: for members
`ζ < ψ_{Ω₂}(Ω_n)` the atoms `ψ_{Ω₂}(Ω_{n+1} + κ ζ) < θ` of `At_C`, closure condition by `Wk.wkL_memN_lt`; `θ = sup_n
ψ_{Ω₂}(Ω_n)` (`Wk.wkTh_cof`); continuity of `ψ_{Ω₁}` at `A + θ`.  Consequences: `Θ_C(θ) = Θ_μ(θ) = υ_{μ+1}`
(`Wk.wkRead0_eq`, `Wk.wkTheta_th`))
SIZE: L
Range(μ), code(μ) = G₂+1, υ_μ < L(ω) ⇒ υ_{μ+1} ≤ Θ_C(θ) -/
theorem skRead0 : ∀ μ, CdRange S μ → cdCode S μ = Ls.lsG S (0 + 1 + 1) + 1 → upsilon μ < Nc.ncL S ω →
    Wc.WcRead0 S μ := fun _ hR hc hω => Wk.wkRead0 hR hc hω

/-- STATUS: PROVED (from `skCodeCof`, `skRead0`, both PROVED; round 117)
SIZE: L
∀ γ < υ_λ ∃ μ: γ < υ_μ < υ_λ, SkMu(μ) -/
theorem skMu {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) :
    ∀ γ < upsilon l, ∃ μ, γ < upsilon μ ∧ upsilon μ < upsilon l ∧ SkMu S μ := by
  intro γ hγ
  rw [← h.2.1] at hγ ⊢
  obtain ⟨μ, hR, h1, h2, hc, hω⟩ := skCodeCof (S := S) k γ hγ
  exact ⟨μ, h1, h2, hR, hc, hω, skRead0 μ hR hc hω⟩

/-- STATUS: REDUCED (by `Wf.wfOffMap` and the shared leaf `skNu` only; round 116.  Was SUSPECT: the restricted exponent clause asks nothing
at `z = ω^{υ_μ}` since `υ_μ ∉ T^{υ_λ}[υ_μ]`; `WcPiLo` restricted is the theorem `Wf.wfPiLo`; the side hypothesis
`hside` of `Wc.wcSupLo` is REFUTED (`Wf.wfSide_false`) and not used: `Wf.wfOffMap` builds the block map on the blocks
of every `Os` and derives the side conditions for that map)
SIZE: M
ν witness, SkMu(μ), υ_μ < υ_λ, Os ⊂ β ⇒ ∃ f B, SkMapP (restricted) -/
theorem skOffMapW {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) (_hw : SkWit l ν) :
    ∀ μ, upsilon μ < upsilon l → SkMu S μ → ∀ Os : Finset Ordinal.{0}, (∀ d ∈ Os, d < ν - l + ω ^ 2) →
      ∃ f B, SkMapP S l μ f B Os := by
  intro μ hμl hM Os _
  have hlν : upsilon l < nuC := by
    have h3 := h.2.2.2.2.1
    have hk : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC :=
      ((Pp.ppL_lt_omega k).trans (Qq.qqL_lt_succ S)).le.trans skNu
    exact (h.2.2.2.2.2.1.trans h3).trans_le hk
  obtain ⟨f, B, h1, h2, h3, h4, h5, h6, -, -⟩ :=
    Wf.wfOffMap (S := S) k h.2.1 hM.1 hM.2.1 hM.2.2.1 hM.2.2.2 hμl hlν Os
  exact ⟨f, B, h1, h2, h3, h4, h5, h6⟩

/-- STATUS: REDUCED (by `Wk.wkLowerF` and the shared leaf `skLowRR`; RESTATED round 117: the window hypothesis
`hwin`.  No code of `μ + f z` is needed: `υ_μ < υ_{μ+f z} < υ_λ = L(k)` lies above a window `w` of `L(k)`, so
`Ty.tyWin_rng` gives Range and `RzRest`.  The old statement (all `μ` below `υ_λ`) is REPLACED: below the window
`μ + f z` may hit an index `L(j)` (code `P′`, not Range))
SIZE: M
w window of L(k), w < υ_μ, SkMapP ⇒ ∀ z ∈ Os, 0 < z, ω² | z ⇒ LOWER(μ + f z) -/
theorem skLowerF {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) (_hw : SkWit l ν) :
    ∀ μ, upsilon μ < upsilon l → SkMu S μ → (∃ w, Ty.TyWin S k w ∧ w < upsilon μ) →
      ∀ (Os : Finset Ordinal.{0}) f B, (∀ d ∈ Os, d < ν - l + ω ^ 2) →
      SkMapP S l μ f B Os → ∀ g ∈ Os, 0 < g → ω ^ 2 ∣ g → CdLower S (μ + f g) := by
  intro μ _ hM hwin Os f B _ hP
  obtain ⟨w, hw, hwμ⟩ := hwin
  exact Wk.wkLowerF skLowRR h.2.1 hw hwμ hM.1.1 hP.1 hP.2.2.2.1

/-- STATUS: OPEN (NEW round 117; the single instance left of `skBigF`)
SIZE: M
the big-reach clause at the offset `z = ν − λ` of `ν` itself.  REFUTE FIRST: NO EVIDENCE (neither
`r(ν) < υ_{ν+ω²}` nor the transfer is decided in Lean: `ν` is uncovered and isolated, which bounds only the reaches
of the restarts below `ν`; the no-go list says nothing on `r(ν)`).  It is vacuous iff `r(ν) < υ_{ν+ω²}`.
ν − λ ∈ Os, υ_{ν+ω²} ≤ r(ν) ⇒ υ_{μ+B} ≤ r(μ + f(ν − λ)) -/
theorem skBigTop {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) (hw : SkWit l ν) :
    ∀ μ, upsilon μ < upsilon l → SkMu S μ → ∀ (Os : Finset Ordinal.{0}) f B, (∀ d ∈ Os, d < ν - l + ω ^ 2) →
      SkMapP S l μ f B Os → ν - l ∈ Os →
        (upsilon (l + (ν - l + ω ^ 2)) ≤ cdR S ν → upsilon (μ + B) ≤ cdR S (μ + f (ν - l))) := by sorry

/-- STATUS: REDUCED (by `Wk.wkBigF` from `skBigTop`; round 117: every offset `z` with `λ + z < ν` is vacuous since `ν`
is not covered (`Wk.wkBig_vac`), and the only other offset `z < β` with `ω² | z` is `z = ν − λ` (`Wk.wkTop_eq`))
SIZE: M
the big-reach clause of `Wf.WfCarry`
υ_{λ+β} ≤ r(λ+z) ⇒ υ_{μ+B} ≤ r(μ+f z) -/
theorem skBigF {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) (hw : SkWit l ν) :
    ∀ μ, upsilon μ < upsilon l → SkMu S μ → ∀ (Os : Finset Ordinal.{0}) f B, (∀ d ∈ Os, d < ν - l + ω ^ 2) →
      SkMapP S l μ f B Os → ∀ g ∈ Os, 0 < g → ω ^ 2 ∣ g →
        (upsilon (l + (ν - l + ω ^ 2)) ≤ cdR S (l + g) → upsilon (μ + B) ≤ cdR S (μ + f g)) := by
  intro μ hμ hM Os f B hOs hP g hg hg0 hgd
  exact Wk.wkBigF h.1 h.2.2.1.1 h.2.2.2.2.2.1 h.2.1 h.2.2.2.2.1 h.2.2.2.2.2.2.1
    (fun hm => skBigTop h hw μ hμ hM Os f B hOs hP hm) g hg hg0 hgd (hOs g hg)

/-- STATUS: PROVED (refuter round: `exists_next` gives `c ∈ T^{υ_λ}`, `Par_sub` gives `Par ⊆ υ_λ`; the suspicion
below is void; same proof as `R2Skel.SkSX.skSX_piT`)
SIZE: M
(old note) `π` is an axiom constant fixed only on `TB(υ_λ, υ_μ)` (`Cited.pi_lt`, `pi_add`, …): every leaf `c < u₁` moved by
`π` in `Vr.vrImg` must lie in `TB(υ_λ, σ)` for all large `σ < υ_λ`, else the carry (and `WcPiLo`) is independent of
the axioms (neither provable nor refutable).  No Lean lemma gives `Tset(υ_λ)`-membership on `[υ_λ, u₁)`.
∀ c, υ_λ ≤ c < u₁ ⇒ ∃ σ₀ < υ_λ, ∀ σ ∈ [σ₀, υ_λ), Bases(σ, υ_λ) ⇒ c ∈ TB(υ_λ, σ) -/
theorem skPiT {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) :
    ∀ c, upsilon l ≤ c → c < upsilon (l + 1) → ∃ σ₀ < upsilon l, ∀ σ, σ₀ ≤ σ → Bases σ (upsilon l) →
      c ∈ TB (upsilon l) σ := by
  have hτ : UpsPt (upsilon l) := upsPt_upsilon (pos_iff_ne_zero.2 h.1.1)
  have hn : IsNext (upsilon l) (upsilon (l + 1)) := by
    have := upsilon_isNext l; rwa [Order.succ_eq_add_one] at this
  intro c _ hcu
  by_cases h1 : upsilon l < Om1
  · obtain ⟨m, hm, hT⟩ := exists_next hτ h1
    have hmu : m = upsilon (l + 1) := hm.unique hn
    have hu1 : upsilon (l + 1) < Om1 := next_lt_Om1 hn (Or.inr hτ) h1
    have hcT : c ∈ Tset (upsilon l) := (hT c (hcu.trans hu1)).2 (hmu ▸ hcu)
    have hP : ↑(Par (upsilon l) c) ⊆ Set.Iio (upsilon l) := Par_sub (upsPt_inE hτ) h1 hcT
    set s := (Par (upsilon l) c).sup id with hs
    have hsl : s < upsilon l := by
      rcases (Par (upsilon l) c).eq_empty_or_nonempty with he | hne
      · have : s = ⊥ := by rw [hs, he]; rfl
        rw [this]; exact hτ.1
      · obtain ⟨p, hp, hpe⟩ := Finset.exists_mem_eq_sup (Par (upsilon l) c) hne id
        rw [hs, hpe]; exact hP hp
    have hτl : IsSuccLimit (upsilon l) := by
      have hE : InE (upsilon l) := upsPt_inE hτ
      have : IsSuccLimit (ω ^ upsilon l) := isSuccLimit_opow_left isSuccLimit_omega0 hτ.1.ne'
      unfold InE at hE; rwa [hE] at this
    refine ⟨s + 1, hτl.add_one_lt hsl, fun σ hσ _ => ⟨hcT, fun p hp => ?_⟩⟩
    have : p ≤ s := Finset.le_sup (f := id) hp
    exact lt_of_lt_of_le (Order.lt_add_one_iff.2 this) hσ
  · exact ⟨0, hτ.1, fun σ _ hB => absurd hB.2.2.2 h1⟩

/-- STATUS: OPEN (RESTATED round 116 with `Wf.WfR`; the refuter's SUSPECT reason is void here: the decomposition
`lo p + D` with `p ∈ [υ_μ, υ_λ)` is excluded (`Wf.wfR_skSX_excl`), the allowed `lo p` ask only `p + img D ≤ r`
(`Wf.wfSup_lo`), and every allowed lo-leaf has its image fixed by `pi_bijOn` (`Wf.wfImg_lo_mem`).  Proved cases for
the map of `Wf.wfOffMap`: the witness decomposition (`Wf.wfR_Ew`, EQ) and the low ones `ub(z+ω+1) + lo(m z)`.
Left: `sg` / `ub` / `tm` nodes with inner leaves, other splittings, and arbitrary maps with `SkMapP`.)
SIZE: L
∀ E, WF(E), val(E) = r(λ+z), Os(E), WfR(λ, μ, E) ⇒ img_{μ,f}(E) ≤ r(μ+f z) -/
theorem skImgF {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) (hw : SkWit l ν) :
    ∀ μ, upsilon μ < upsilon l → SkMu S μ → ∀ (Os : Finset Ordinal.{0}) f B, (∀ d ∈ Os, d < ν - l + ω ^ 2) →
      SkMapP S l μ f B Os → ∀ g ∈ Os, 0 < g → ω ^ 2 ∣ g →
        ∀ E : Vr.VrE, Vr.VrWF l (ν - l + ω ^ 2) E → Vr.vrVal l E = cdR S (l + g) → Vr.VrOs l Os E →
          Wf.WfR l μ E → Vr.vrImg l μ f E ≤ cdR S (μ + f g) := by sorry

/-- STATUS: REDUCED (from `skOffMapW`, `skLowerF`, `skBigF`, `skImgF`; RESTATED round 116: `Wf.WfCarry`;
round 117: the window hypothesis `hwin`)
SIZE: L
ν witness, μ above a window of L(k) ⇒ the supply data and `WfCarry` at every `μ` of `skMu` -/
theorem skCarryWit {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) (hw : SkWit l ν) :
    ∀ μ, upsilon μ < upsilon l → SkMu S μ → (∃ w, Ty.TyWin S k w ∧ w < upsilon μ) →
      ∀ Os : Finset Ordinal.{0}, (∀ d ∈ Os, d < ν - l + ω ^ 2) →
      ∃ f B, μ + B ≤ l ∧ ω ^ 2 ∣ B ∧ upsilon (μ + B) ≤ cdR S μ ∧ Sl.SlOff f Os B ∧
        Wf.WfCarry S l (ν - l + ω ^ 2) μ f B Os := by
  intro μ hμ hM hwin Os hOs
  obtain ⟨f, B, hP⟩ := skOffMapW h hw μ hμ hM Os hOs
  refine ⟨f, B, hP.1, hP.2.1, hP.2.2.1, hP.2.2.2.1, fun g hg hg0 hgd => ⟨?_, ?_, ?_⟩⟩
  · exact skLowerF h hw μ hμ hM hwin Os f B hOs hP g hg hg0 hgd
  · exact skBigF h hw μ hμ hM Os f B hOs hP g hg hg0 hgd
  · exact skImgF h hw μ hμ hM Os f B hOs hP g hg hg0 hgd

/-- STATUS: OPEN (RESTATED round 116 with `Wf.WfCarry`; the refuter's SUSPECT reason (`skSX_sup_pi`) is void for the
restricted image clause; round 117: the window hypothesis `hwin`, as in `skCarryWit`; its LOWER clause is
`Wk.wkLowerF` for every offset map, its big-reach clause is `Wk.wkBigF` from the instance at `ν − λ`)
SIZE: L
the supply and carry at the other windows: offsets with codes `m z ≥ u₁` (leaves `υ_{λ+h'}` renamed to
`υ_{μ+f h'}`), a supply past `X` (readings at the code levels `θ_{k+2}` beyond `WcRead0`)
¬ witness ⇒ the same as `skCarryWit` -/
theorem skCarryOther {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) (hw : ¬ SkWit l ν) :
    ∀ μ, upsilon μ < upsilon l → SkMu S μ → (∃ w, Ty.TyWin S k w ∧ w < upsilon μ) →
      ∀ Os : Finset Ordinal.{0}, (∀ d ∈ Os, d < ν - l + ω ^ 2) →
      ∃ f B, μ + B ≤ l ∧ ω ^ 2 ∣ B ∧ upsilon (μ + B) ≤ cdR S μ ∧ Sl.SlOff f Os B ∧
        Wf.WfCarry S l (ν - l + ω ^ 2) μ f B Os := by sorry

/-- STATUS: REDUCED (from `skMu`, `skCarryWit`, `skCarryOther`; RESTATED round 116; round 117: `μ` is taken above
`max(γ, w)` for a window `w` of `L(k)`, `Wk.wkWin_ex`)
SIZE: L
WfSup(λ, β(ν)) -/
theorem skSupK {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) : Wf.WfSup S l (ν - l + ω ^ 2) := by
  intro γ hγ Os hOs
  obtain ⟨w, hw⟩ := Wk.wkWin_ex (S := S) k
  have hwl : w < upsilon l := hw.2.1.trans_eq h.2.1
  obtain ⟨μ, h1, h2, hM⟩ := skMu h (max γ w) (max_lt hγ hwl)
  have hwin : ∃ w, Ty.TyWin S k w ∧ w < upsilon μ := ⟨w, hw, (le_max_right γ w).trans_lt h1⟩
  have hc : ∃ f B, μ + B ≤ l ∧ ω ^ 2 ∣ B ∧ upsilon (μ + B) ≤ cdR S μ ∧ Sl.SlOff f Os B ∧
      Wf.WfCarry S l (ν - l + ω ^ 2) μ f B Os := by
    by_cases hw : SkWit l ν
    · exact skCarryWit h hw μ h2 hM hwin Os hOs
    · exact skCarryOther h hw μ h2 hM hwin Os hOs
  obtain ⟨f, B, hB, hd, hs, ho, hC⟩ := hc
  exact ⟨μ, f, B, hM.1, (le_max_left γ w).trans_lt h1, h2, hB, hd, hs, ho, hC⟩

/-- STATUS: PROVED (by `Wf.wfPiLo`; round 116)
SIZE: S
the exponent clause `WcPiLo` restricted to `T^{υ_λ}[υ_μ]` is a theorem:
Bases(υ_μ, υ_λ), c ∈ T^{υ_λ}[υ_μ], c < Ω₁ ⇒ π(c) < ω^{υ_{μ+1}+1} -/
theorem skPiLo {l μ c : Ordinal.{0}} (hB : Bases (upsilon μ) (upsilon l))
    (hc : c ∈ TB (upsilon l) (upsilon μ)) (hc1 : c < Om1) :
    pi (upsilon μ) (upsilon l) c < ω ^ (upsilon (μ + 1) + 1) :=
  Wf.wfPiLo hB hc hc1

/-- STATUS: PROVED (by `Wf.wfSide_false`; round 116; a REFUTATION recorded as a node)
SIZE: S
the side hypothesis `hside` of `Wc.wcQ_carry` / `Wc.wcSupLo` (bounds for EVERY block map `Q`) is false as soon as
`Os` has an element `z ≠ g`; the old route `skOffMapW ← Wc.wcSupLo` was vacuous there -/
theorem skSideRef {μ g : Ordinal.{0}} {Os : Finset Ordinal.{0}} (hz : ∃ z ∈ Os, z ≠ g) :
    ¬ ∀ Q : Ordinal.{0} → Ordinal.{0}, ∀ z ∈ Os, z ≠ g →
      ω ≤ Vy.vyMap Q z ∧ Vy.vyMap Q z < upsilon (μ + 2) ∧ upsilon (μ + Vy.vyMap Q z + ω + 1) < nuC :=
  Wf.wfSide_false hz

/-! ## Assembly -/

/-- STATUS: REDUCED (from `skUp`, `skForm`, `skSupK`; RESTATED round 116)
SIZE: L
WfGen(λ, β(ν)) -/
theorem skGen {k : ℕ} {l ν : Ordinal.{0}} (h : SkCtx S k l ν) : Wf.WfGen S l (ν - l + ω ^ 2) :=
  ⟨skUp h, skForm h, skSupK h⟩

/-- STATUS: REDUCED (from `skWin`, `skGen`; RESTATED round 116)
SIZE: L
∀ k, υ_λ = L(k) ⇒ WfVisGen(λ, L(k+1), υ_{L(k)+W(L(k))}) -/
theorem skVisK (k : ℕ) : ∀ l, IsRestartIdx l → Nc.ncL S (k : Ordinal.{0}) = upsilon l →
    Wf.WfVisGen S l (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S (k : Ordinal.{0}) + Te.teW (Nc.ncL S (k : Ordinal.{0})))) := by
  intro l hl e ν h1 h2 h3 h4 h5 h6
  have hC : SkCtx S k l ν := ⟨hl, e, h1, h2, h3, h4, h5, h6⟩
  exact ⟨_, (skWin hC).1, (skWin hC).2, skGen hC⟩

/-- STATUS: REDUCED (from `skVisK`)
SIZE: L
NEW TOP (round 116; replaces the old top `h0 ∧ ∀ n, hn n` of `Wd.wdRoadL`, which implies it by
`Wf.wfVisGen_of_vr`): h0' ∧ ∀ n, hn' n, the supply hypotheses of `Wf.wfRoad`; `Root.skNuC` applies `Wf.wfRoad`. -/
theorem skSup :
    (∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      Wf.WfVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0)))) ∧
    (∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      Wf.WfVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) := by
  refine ⟨fun l hl e => ?_, fun n l hl e => skVisK (n + 1) l hl e⟩
  have h := skVisK (S := S) 0 l hl (by simpa using e)
  simpa using h

end R2Skel.SkS

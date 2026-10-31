import Googology.Trans.PoR.InaccPsi.R2.HoRoad
import Googology.Trans.PoR.InaccPsi.R2.WdRoad
import Googology.Trans.PoR.InaccPsi.R2.WhSucc
import Googology.Trans.PoR.InaccPsi.R2.WhRefute
import Googology.Trans.PoR.InaccPsi.R2.WjSplit
import Googology.Trans.PoR.InaccPsi.R2.WjVeb
import Googology.Trans.PoR.InaccPsi.R2.WmA1
import Googology.Trans.PoR.InaccPsi.R2.WnSucc
import Googology.Trans.PoR.InaccPsi.R2.WnLv3

/-!
# SkF: skeleton (map) of the part "frontier" of `Wd.wdRoadL`

The four hypotheses `hUH`, `hLH`, `hVH`, `hVt` of `Wd.wdRoadL` (UPPER / LOWER / CapV at range restarts
`λ ≥ ι(Γ(φ(Ω₁·Ω₁, G+1))·ω)`).  `Ho.hoWaRoad_hyp_iff` moves them to `λ ≥ F_Ho = ι(Γ(φ(Ω₁³, G+1))·ω)`.

Which restarts are needed: every `λ` with `CdRange S λ`, i.e. `B₀ ≤ λ`, `υ_λ < L(ω+1)`, code `m_λ < P′`
(by `Te.teCode_hi_iff` these are ALL restarts in `[B₀, L(ω+1))` except the `L(k)` and `L(ω)`).  They fall in three
regions:
* (A) `λ < ι(Γ(B)·ω)` for some code `B < Γ(1)` (`Hg.HgVD` systems; levels `ℓ` of `φ(ℓ, G+1)`, `ℓ < Γ(1)`);
* (B) past every such frontier, name exponent `e(η_λ) < Ω₂` (atoms `Γ(c)`, `c ≥ 1`, inside codes, up to `ι(Ω₂)`);
* (C) `e(η_λ) ≥ Ω₂` (`Gc.gc_past_Om2`: `ι(Ω₂) ≤ λ`, `m_λ = π_η`), up to `L(ω+1)` — the long region.
Region (A) splits by the level `ℓ`: (A1) `ℓ < ε_{Ω₁+1}` (Cantor normal form in `Ω₁`-powers, read `Ω₁ ↦ x` by
`Gf.rdc`, gate `Gf.gtc`), (A2) Veblen-form levels `ε_{Ω₁+1} ≤ ℓ < G`, (A3) levels containing `G`.
(A1) is ONE generic induction over `ℓ` (`skFam`, by well-founded recursion from `skStep`).

Skeleton only: the OPEN nodes are `sorry`.  No axiom.

Round 116 (leaf gam41, modules `R2.Wh*`; the PROVED nodes below can be checked only after the merge, since they use
the new modules): `skShape`, `skDigitGate`, `skLvOfGate`, `skStepBase`, `skCofLev` PROVED.  Two statement
corrections: (1) the shapes `ShPow`, `ShExpLim`, `ShCoefLim` had `e : ℕ` (untyped `e` in `Om1 ^ e` elaborates to
`Monoid.npow`); with `e : ℕ` the shape leaf is FALSE (`skShapeNat_false`, witness `Ω₁^ω`); they now ask
`e : Ordinal`.  (2) The entry predicate `SkAt` carries no invariant tying the system to the package (no start
condition over `G`, no gate bound), so the steps would have to extend ARBITRARY digit systems; the induction now runs
on `SkAtW` (= `Wh.WhAt`: `SkAt` + gate `≤ gtc ℓ`, every `ε`-number above the gate is above `gtc ℓ`, the system is a
start over `G` at the package).  On it `skStepBaseW` and `skStepSuccW` are PROVED; `skStepPowW`, `skStepExpLimW`,
`skStepCoefLimW` are OPEN.  The original `skStep*` leaves are REPLACED (kept, not used).

Round 116 (leaf reg1, modules `R2.Wj*`): the nodes of (A2), (A3), (B) and (C) below come from leaf reg1.
Region (C) lies entirely below `L(0)` (`skLongMid`, `skLongTop` vacuous); old (B) is re-split by the windows
`[L(k), L(k+1))` (`Wj.wjRegB_iff`, `skSplit`); the A2/A3 cut moves to `φ(G, 1)` (`Wj.wjA2Cof`, `Wj.wjA3Cof`).
The A2 nodes use reg1's `SkAtG` (`↔ SkAt` below `ε_{Ω₁+1}`), not gam41's stronger `SkAtW`.

Round 117 (leaf gam42, modules `R2.Wm*`; the PROVED nodes below can be checked only after the merge, since they use
the new modules): the coherence `SkCohW` relates packages by `Hn.HnkExt`, which is vacuous across a gate drop
(`skOldVacuous`; a drop exists: `Ω₁·ω < Ω₁²`, `gtc(Ω₁²) = 2 < ω = gtc(Ω₁·ω)`), so a limit entry could not be shown to
extend every member.  The induction now runs on the CORRECTED coherence `SkCohW2` (= `Wm.WmCoh`), whose package
relation `Wm.WmExt` lowers by the pseudo-base gate (`Wm.wmLowr`: only `g' ≤ Q.γ`); `SkCohW2 ⇒ SkCohW`
(`skCohW2_old`).  On it: base, successor, EVERY level with an `ω`-sequence (`Wm.WmFs`: all coefficient limits, and
the exponent limits whose exponent has an `ω`-sequence) are PROVED; the one remaining leaf is `skStepOm1W2` (the levels
of cofinality `Ω₁`).  The family on all levels below `Ω₁²` is proved with no hypothesis (`skFamSq`).  The old
`skStepPowW`, `skStepExpLimW`, `skStepCoefLimW`, `skStep` are REPLACED; `skFam` keeps its statement and is REDUCED to
`skStepOm1W2`.  The frontier does not move yet.

Round 117 (leaf reg2, modules `R2.Wn*`; the PROVED nodes below can be checked only after the merge):
`skShapeG`, `skLvOfGateG`, `skGateBn` PROVED.  `SkAtG` has the defect gam41 found in `SkAt` (no start condition
of the system over `G` at the package), and `Wh.WhAt` cannot be used past `ε_{Ω₁+1}` (its base `Wh.whGW` asks
`ℓ(x) + x < ε_{x+1}`, false for every level `ℓ ≥ ε_{Ω₁+1}`); the (A2) induction now runs on `SkAtWG` (= `Wn.WnAt`:
`glR`/`glG`, and the base `Wn.wnGW` whose outer low field `hdNx (Γ_{x+1}+1) (Γ_{x+1})` needs no bound on the
level).  On it `skStepBaseWG` and `skStepSuccWG` are PROVED; `skStepPowWG`, `skStepCoefLimWG`, `skStepExpLimWG`
are OPEN; the `SkAtG` steps are REPLACED (kept, not used).
(A3): `Hn.HnLv` cannot carry an (A3) level and `G` is not in `range φ(L, ·)` for `L > G` (`skA3NoBand`,
`skA3NoGBase`); the (A3) datum is `Wn.WnLv3` (non-vacuity `skA3Datum0` at `t₀`), the package `Wn.WnPk3`, and the
ladder invariant is `SkPk3W` (= `Wn.WnEnt3`: package at `t_n` + pseudo-base `φ(t_n, G)`); the SUSPECT of
`skSysA3Step` is CONFIRMED (its invariant carries no level datum) and the node is REPLACED by `skSysA3StepW`.
-/

set_option autoImplicit false

namespace R2Skel.SkF

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2

/-! ## Abbreviations -/

/-- ENUM-REACH (UPPER and LOWER) and CapV at the restart index `l`. -/
def SkUV (S : InaccSeq.{0}) (l : Ordinal.{0}) : Prop := Cd.CdUpper S l ∧ Cd.CdLower S l ∧ Cd.CdCapV S l

/-- The frontier of `Ho.hoUf`: `ι(Γ(φ(Ω₁³, G+1))·ω)`. -/
noncomputable def skFHo (S : InaccSeq.{0}) : Ordinal.{0} := Bt.iota S (Gc.gcG Ho.hoUf.B * ω)

/-- The level codes of the generic induction: `Ω₁ ≤ ℓ`, `Ω₁ ∣ ℓ`, `ℓ < ε_{Ω₁+1}`. -/
def SkLev (ℓ : Ordinal.{0}) : Prop := Om1 ≤ ℓ ∧ Om1 ∣ ℓ ∧ ℓ < Gf.gfE

/-- An entry of the induction: the package at a level (steps at every pseudo-base) and the system over `G`. -/
abbrev SkEnt : Type 1 := Hn.HnPk × ULift.{1} Hg.HgVD

/-- The entry `E` sits at the level `ℓ`: package level `ℓ` read `rdc ℓ x` above its gate; system
`B = φ(ℓ, G+1)` with gate `≤ gtc ℓ`. -/
def SkAt (ℓ : Ordinal.{0}) (E : SkEnt) : Prop :=
  E.1.Λ.L = ℓ ∧ (∀ x, InE x → x < Om1 → E.1.Λ.g < x → E.1.Λ.l x = Gf.rdc ℓ x) ∧
    E.2.down.B = veblen ℓ (Gc.gcG 0 + 1) ∧ E.2.down.γ ≤ Gf.gtc ℓ

/-- `E` extends `E'`: the packages extend (`Hn.HnkExt`), the system bound grows, readings and gates agree below. -/
def SkExt (E' E : SkEnt) : Prop :=
  Hn.HnkExt E'.1 E.1 ∧ E'.2.down.B < E.2.down.B ∧
    ∀ c x, c < E'.2.down.B → E.2.down.R c x = E'.2.down.R c x ∧ E.2.down.g c = E'.2.down.g c

/-- A coherent family below `ℓ`. -/
def SkCoh (ℓ : Ordinal.{0}) (f : ∀ ℓ' : Ordinal.{0}, ℓ' < ℓ → SkEnt) : Prop :=
  (∀ ℓ' (h : ℓ' < ℓ), SkLev ℓ' → SkAt ℓ' (f ℓ' h)) ∧
    ∀ ℓ'' ℓ' (h'' : ℓ'' < ℓ) (h' : ℓ' < ℓ), ℓ'' < ℓ' → SkLev ℓ'' → SkLev ℓ' → SkExt (f ℓ'' h'') (f ℓ' h')

/-- The step at `ℓ`: every coherent family below `ℓ` has an entry at `ℓ` extending all of it. -/
def SkStepAt (ℓ : Ordinal.{0}) : Prop :=
  ∀ f, SkCoh ℓ f → ∃ E, SkAt ℓ E ∧ ∀ ℓ' (h : ℓ' < ℓ), SkLev ℓ' → SkExt (f ℓ' h) E

/-- Shape: successor level `ℓ = ℓ' + Ω₁`. -/
def ShSucc (ℓ : Ordinal.{0}) : Prop := ∃ ℓ', SkLev ℓ' ∧ ℓ = ℓ' + Om1

/-- Shape: `ℓ = P + Ω₁^{e+1}`, `e ≥ 1` (union over the prefixes `P + Ω₁^e·v`, `v < Ω₁`). -/
def ShPow (ℓ : Ordinal.{0}) : Prop := ∃ P e : Ordinal.{0}, 1 ≤ e ∧ Om1 ^ (e + 1) ∣ P ∧ ℓ = P + Om1 ^ (e + 1)

/-- Shape: `ℓ = P + Ω₁^e`, `e` a limit (transfinite exponent). -/
def ShExpLim (ℓ : Ordinal.{0}) : Prop := ∃ P e : Ordinal.{0}, IsSuccLimit e ∧ Om1 ^ e ∣ P ∧ ℓ = P + Om1 ^ e

/-- Shape: `ℓ = P + Ω₁^e·c`, `c < Ω₁` a limit (an `ω`-chain union). -/
def ShCoefLim (ℓ : Ordinal.{0}) : Prop :=
  ∃ P e c : Ordinal.{0}, 1 ≤ e ∧ IsSuccLimit c ∧ c < Om1 ∧ Om1 ^ (e + 1) ∣ P ∧ ℓ = P + Om1 ^ e * c

/-- REFUTED form (round 115 as elaborated): `ShPow` with `e : ℕ`. -/
def ShPowN (ℓ : Ordinal.{0}) : Prop := ∃ P e, 1 ≤ e ∧ Om1 ^ (e + 1) ∣ P ∧ ℓ = P + Om1 ^ (e + 1)

/-- REFUTED form (round 115 as elaborated): `ShExpLim` with `e : ℕ`. -/
def ShExpLimN (ℓ : Ordinal.{0}) : Prop := ∃ P e, IsSuccLimit e ∧ Om1 ^ e ∣ P ∧ ℓ = P + Om1 ^ e

/-- REFUTED form (round 115 as elaborated): `ShCoefLim` with `e : ℕ`. -/
def ShCoefLimN (ℓ : Ordinal.{0}) : Prop :=
  ∃ P e c, 1 ≤ e ∧ IsSuccLimit c ∧ c < Om1 ∧ Om1 ^ (e + 1) ∣ P ∧ ℓ = P + Om1 ^ e * c

/-- The corrected entry predicate (round 116): `Wh.WhAt` (the entry of `SkAt`, the gate `≤ gtc ℓ`, every
`ε`-number above the gate is above `gtc ℓ`, the system is a start over `G` at the package). -/
def SkAtW (ℓ : Ordinal.{0}) (E : SkEnt) : Prop := Wh.WhAt ℓ E.1 E.2.down

/-- A coherent family below `ℓ` (for `SkAtW`). -/
def SkCohW (ℓ : Ordinal.{0}) (f : ∀ ℓ' : Ordinal.{0}, ℓ' < ℓ → SkEnt) : Prop :=
  (∀ ℓ' (h : ℓ' < ℓ), SkLev ℓ' → SkAtW ℓ' (f ℓ' h)) ∧
    ∀ ℓ'' ℓ' (h'' : ℓ'' < ℓ) (h' : ℓ' < ℓ), ℓ'' < ℓ' → SkLev ℓ'' → SkLev ℓ' → SkExt (f ℓ'' h'') (f ℓ' h')

/-- The step at `ℓ` (for `SkAtW`). -/
def SkStepAtW (ℓ : Ordinal.{0}) : Prop :=
  ∀ f, SkCohW ℓ f → ∃ E, SkAtW ℓ E ∧ ∀ ℓ' (h : ℓ' < ℓ), SkLev ℓ' → SkExt (f ℓ' h) E

/-- The transfinite digit gate: every hereditary `Ω₁`-digit of a code over `Z` (below `ε_{Ω₁+1}`) is `< Z`. -/
def SkDigitGate : Prop :=
  ∀ Z, SC Z → Z ≤ Om 1 → ∀ y, Mx.GxCl Z {Gc.gcG 0} y → y < Gf.gfE → Gf.gtc y < Z

/-- EXACT of the reading `rdc ℓ` above the gate `gtc ℓ`. -/
def SkReadExact : Prop :=
  ∀ ℓ σ ρ, SkLev ℓ → Bases σ ρ → Gf.gtc ℓ < σ → Gf.rdc ℓ ρ ∈ TB ρ σ ∧ pi σ ρ (Gf.rdc ℓ ρ) = Gf.rdc ℓ σ

/-- The level datum for a general `ℓ`: an `Hn.HnLv` with `L = ℓ`, gate `≤ gtc ℓ`, reading `rdc ℓ`. -/
def SkLvDatumAll : Prop :=
  ∀ ℓ, SkLev ℓ → ∃ Λ : Hn.HnLv, Λ.L = ℓ ∧ Λ.g ≤ Gf.gtc ℓ ∧
    ∀ x, InE x → x < Om1 → Λ.g < x → Λ.l x = Gf.rdc ℓ x

/-! ## PROVED nodes (repo) -/

/-- STATUS: PROVED (Hg.hgV_locD_enum, Hg.hgV_locD_capV)
SIZE: S
∀ system V, γ_V < K: ∀ range λ < ι(Γ(B_V)·ω), UPPER ∧ LOWER ∧ CapV. -/
theorem skLocOfSys (S : InaccSeq.{0}) (V : Hg.HgVD) (hγ : V.γ < Td.tdK S) :
    ∀ l, Cd.CdRange S l → l < Bt.iota S (Gc.gcG V.B * ω) → SkUV S l := fun _ hr hl =>
  ⟨(Hg.hgV_locD_enum V S hγ hr hl).1, (Hg.hgV_locD_enum V S hγ hr hl).2,
    Hg.hgV_locD_capV V S hγ hr hl⟩

/-- STATUS: PROVED (Ho.hoUf_enum, Ho.hoUf_capV)
SIZE: S
∀ range λ < ι(Γ(φ(Ω₁³, G+1))·ω): UPPER ∧ LOWER ∧ CapV. -/
theorem skLocHo (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → l < skFHo S → SkUV S l := fun _ hr hl =>
  ⟨(Ho.hoUf_enum S hr hl).1, (Ho.hoUf_enum S hr hl).2, Ho.hoUf_capV S hr hl⟩

/-- STATUS: PROVED (Ho.hoUf_B, Ho.hoUf_γ)
SIZE: S
the G-system at ℓ = Ω₁³: B = φ(Ω₁³, G+1), gate 0. -/
theorem skSysHo : ∃ V : Hg.HgVD, V.B = veblen (Om1 * Om1 * Om1) (Gc.gcG 0 + 1) ∧ V.γ = 0 :=
  ⟨Ho.hoUf, Ho.hoUf_B, Ho.hoUf_γ⟩

/-- STATUS: PROVED (Ho.hoSg_B, Ho.hoSg_γ)
SIZE: S
∀ ν < Ω₁: the G-system at ℓ = Ω₁²·(1+ν): B = φ(Ω₁²·(1+ν), G+1), gate max(0, hlGt(1+ν)). -/
theorem skSysHoSg {ν : Ordinal.{0}} (hν : ν < Om1) :
    ∃ V : Hg.HgVD, V.B = veblen (Om1 * Om1 * (1 + ν)) (Gc.gcG 0 + 1) ∧ V.γ = max 0 (Hl.hlGt (1 + ν)) :=
  ⟨Ho.hoSg ν, Ho.hoSg_B hν, Ho.hoSg_γ hν⟩

/-- STATUS: PROVED (Gf.rdc_pi)
SIZE: S
∀ ℓ < ε_{Ω₁+1}, gtc ℓ < σ: rdc ℓ ρ ∈ Tᵖ[σ] ∧ π(rdc ℓ ρ) = rdc ℓ σ. -/
theorem skReadExact : SkReadExact := fun _ _ _ hℓ hB hg => Gf.rdc_pi hB hℓ.2.2 hg

/-- STATUS: PROVED (Ho.hoWaRoad_hyp_iff)
SIZE: S
the four hypotheses from ι(Γ(φ(Ω₁², G+1))·ω) on ⇔ the four from F_Ho = ι(Γ(φ(Ω₁³, G+1))·ω) on. -/
theorem skHypIff (S : InaccSeq.{0})
    (h : ∀ l, Cd.CdRange S l → skFHo S ≤ l → SkUV S l) :
    (∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdUpper S l) ∧
    (∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdLower S l) ∧
    (∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdCapV S l) ∧
    (∀ l, Cd.CdRange S l → Nc.ncL S ω < upsilon l →
      Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdCapV S l) := by
  obtain ⟨h1, h2, h3, h4⟩ := Ho.hoWaRoad_hyp_iff S
  exact ⟨h1.2 fun l hr hl => (h l hr hl).1, h2.2 fun l hr hl => (h l hr hl).2.1,
    h3.2 fun l hr _ hl => (h l hr hl).2.2, h4.2 fun l hr _ hl => (h l hr hl).2.2⟩

/-! ## Leaves of the level-code induction (round 116) -/

/-- STATUS: PROVED (Wh.whShape; round 116, statement corrected: `e : Ordinal` in `ShPow`, `ShExpLim`, `ShCoefLim`)
SIZE: S
∀ ℓ: Ω₁ ≤ ℓ, Ω₁ ∣ ℓ, ℓ < ε_{Ω₁+1} ⇒ ℓ = Ω₁ ∨ succ ∨ pow ∨ exp-limit ∨ coefficient-limit (Cantor normal form). -/
theorem skShape : ∀ ℓ, SkLev ℓ → ℓ = Om1 ∨ ShSucc ℓ ∨ ShPow ℓ ∨ ShExpLim ℓ ∨ ShCoefLim ℓ :=
  fun ℓ h => Wh.whShape ℓ h.1 h.2.1 h.2.2

/-- STATUS: REFUTED (Wh.whShapeNat_false; witness Ω₁^ω)
SIZE: S
the round-115 form of skShape, with `e : ℕ` in the last three shapes, is FALSE. -/
theorem skShapeNat_false : ¬ ∀ ℓ, SkLev ℓ → ℓ = Om1 ∨ ShSucc ℓ ∨ ShPowN ℓ ∨ ShExpLimN ℓ ∨ ShCoefLimN ℓ :=
  Wh.whShapeNat_false

/-- STATUS: PROVED (Wh.whDigitGate)
SIZE: M
SC Z ≤ Ω₁, y code over Z (atom G), y < ε_{Ω₁+1} ⇒ gtc y < Z (transfinite digit gate). -/
theorem skDigitGate : SkDigitGate := Wh.whDigitGate

/-- STATUS: PROVED (Wh.whLvDatumAll; the level datum Wh.whLv ℓ, gate = gtc ℓ; the hypotheses are not needed)
SIZE: S
digit gate ∧ EXACT ⇒ ∀ ℓ ∃ HnLv: L = ℓ, l x = rdc ℓ x above g ≤ gtc ℓ. -/
theorem skLvOfGate : SkDigitGate → SkReadExact → SkLvDatumAll := fun _ _ => Wh.whLvDatumAll

/-- STATUS: PROVED (Wh.whStepBase)
SIZE: S
the entry at ℓ = Ω₁: package Hn.hnPk1 (read x) and the G-system Hg.hgU at φ(Ω₁, G+1). -/
theorem skStepBase : SkStepAt Om1 := fun _ _ =>
  ⟨(Hn.hnPk1, ULift.up Hg.hgU), Wh.whStepBase, fun _ h hl => absurd hl.1 (not_le.2 h)⟩

/-- STATUS: REPLACED (by skStepSuccW: SkAt has no start condition of the system over G at the package, so the step
would have to extend an ARBITRARY digit system at φ(ℓ', G+1); no generic construction does that; NO EVIDENCE against)
SIZE: M
ℓ = ℓ' + Ω₁ (for SkAt). -/
theorem skStepSucc (hLv : SkLvDatumAll) : ∀ ℓ, SkLev ℓ → ShSucc ℓ → SkStepAt ℓ := by
  sorry

/-- STATUS: REPLACED (by skStepPowW; same reason as skStepSucc)
SIZE: M
ℓ = P + Ω₁^{e+1} (for SkAt). -/
theorem skStepPow (hLv : SkLvDatumAll) : ∀ ℓ, SkLev ℓ → ShPow ℓ → SkStepAt ℓ := by
  sorry

/-- STATUS: REPLACED (by skStepExpLimW; same reason as skStepSucc; in round 115 it was vacuous, `e : ℕ`)
SIZE: M
ℓ = P + Ω₁^e, e limit (for SkAt). -/
theorem skStepExpLim (hLv : SkLvDatumAll) (hG : SkDigitGate) : ∀ ℓ, SkLev ℓ → ShExpLim ℓ → SkStepAt ℓ := by
  sorry

/-- STATUS: REPLACED (by skStepCoefLimW; same reason as skStepSucc)
SIZE: M
ℓ = P + Ω₁^e·c, c < Ω₁ limit (for SkAt). -/
theorem skStepCoefLim (hLv : SkLvDatumAll) : ∀ ℓ, SkLev ℓ → ShCoefLim ℓ → SkStepAt ℓ := by
  sorry

/-- STATUS: PROVED (Wh.whAt_base)
SIZE: S
the entry at ℓ = Ω₁ for SkAtW: Hn.hnPk1 and Hg.hgU (Hg.hgU is a start over G, Wh.whU_shape). -/
theorem skStepBaseW : SkStepAtW Om1 := fun _ _ =>
  ⟨(Hn.hnPk1, ULift.up Hg.hgU), Wh.whAt_base, fun _ h hl => absurd hl.1 (not_le.2 h)⟩

/-- STATUS: PROVED (Wh.whSucc_at, Wh.whSucc_ext, Wh.whSucc_ext_lt)
SIZE: M
ℓ = ℓ' + Ω₁: package Hn.HnPk.succ, G-system = the union over G (Wh.whGW) started at the system at ℓ'. -/
theorem skStepSuccW : ∀ ℓ, SkLev ℓ → ShSucc ℓ → SkStepAtW ℓ := by
  rintro ℓ hℓ ⟨ℓ', hℓ', rfl⟩ f ⟨hat, hext⟩
  have hlt : ℓ' < ℓ' + Om1 := lt_add_of_pos_right _ Wh.wh_Om1_pos
  have hat' := hat ℓ' hlt hℓ'
  refine ⟨((f ℓ' hlt).1.succ, ULift.up (Wh.whSuccV hat')), Wh.whSucc_at hℓ'.2.1 hℓ.2.2 hat', fun ℓ'' h'' hℓ'' => ?_⟩
  have hle : ℓ'' ≤ ℓ' := not_lt.1 fun h => absurd h'' (not_lt.2 (Wh.wh_lev_succ_le hℓ'.2.1 hℓ''.2.1 h))
  rcases hle.lt_or_eq with hl | rfl
  · exact Wh.whSucc_ext_lt hℓ'.2.1 hℓ.2.2 hat' hl hℓ''.2.1 (hat ℓ'' h'' hℓ'') (hext ℓ'' ℓ' h'' hlt hl hℓ'' hℓ')
  · exact Wh.whSucc_ext hat'

/-- STATUS: REPLACED (round 117: by skStepOm1W2 on the corrected coherence SkCohW2; on SkCohW the package relation
HnkExt is vacuous across a gate drop, so the union cannot be shown to extend every member)
SIZE: M
ℓ = P + Ω₁^{e+1} (e ≥ 1, cf Ω₁), for SkAtW: package = at every pseudo-base Q the union over the systems over Q at
the levels P + Ω₁^e·v (v < Ω₁) and everything between (a recursion of systems over a base datum, generic in the level;
Ho.HoBR / Ho.HoStep are P = 0, e = 2 with the band levels only); G-system = the same recursion over G and Ho.hoOU. -/
theorem skStepPowW : ∀ ℓ, SkLev ℓ → ShPow ℓ → SkStepAtW ℓ := by
  sorry

/-- STATUS: REPLACED (round 117: cf(e) = ω by skStepExpLimFsW2 (PROVED), cf(e) = Ω₁ by skStepOm1W2, both on
SkCohW2; same reason as skStepPowW)
SIZE: M
ℓ = P + Ω₁^e, e limit, for SkAtW: cf(e) = ω: as skStepCoefLimW along e_k → e; cf(e) = Ω₁: as skStepPowW. -/
theorem skStepExpLimW : ∀ ℓ, SkLev ℓ → ShExpLim ℓ → SkStepAtW ℓ := by
  sorry

/-- STATUS: REPLACED (round 117: by skStepCoefLimW2 (PROVED) on SkCohW2; same reason as skStepPowW)
SIZE: M
ℓ = P + Ω₁^e·c, c < Ω₁ limit, for SkAtW: package Ho.hoPkL of an Ho.HoSeq along c_k → c (needs gates non-decreasing
along the sequence: SkAtW gives only g ≤ gtc ℓ; take a non-decreasing subsequence, or make the gate a function of ℓ);
G-system = the gated ω-chain union (Ho.hoGCh generalized to abstract levels) with its start condition at the limit. -/
theorem skStepCoefLimW : ∀ ℓ, SkLev ℓ → ShCoefLim ℓ → SkStepAtW ℓ := by
  sorry

/-- STATUS: PROVED (Wh.whCofLev; ℓ = a member of the tower Gf.gfTw)
SIZE: S
∀ B < φ(ε_{Ω₁+1}, G+1) ∃ ℓ (SkLev ℓ, gtc ℓ < K, B ≤ φ(ℓ, G+1)). -/
theorem skCofLev (S : InaccSeq.{0}) : ∀ B, B < veblen Gf.gfE (Gc.gcG 0 + 1) →
    ∃ ℓ, SkLev ℓ ∧ Gf.gtc ℓ < Td.tdK S ∧ B ≤ veblen ℓ (Gc.gcG 0 + 1) := Wh.whCofLev S

/-! ## Round 117: the corrected coherence (leaf gam42, modules `R2.Wm*`) -/

/-- The corrected extension of entries: packages by `Wm.WmExt` (lowering by the pseudo-base gate). -/
def SkExtW2 (E' E : SkEnt) : Prop := Wm.WmExtE E' E

/-- The corrected coherence of a family below `ℓ` (`SkAtW` entries, `SkExtW2` between levels). -/
def SkCohW2 (ℓ : Ordinal.{0}) (f : ∀ ℓ' : Ordinal.{0}, ℓ' < ℓ → SkEnt) : Prop := Wm.WmCoh ℓ f

/-- The step at `ℓ` on the corrected coherence. -/
def SkStepAtW2 (ℓ : Ordinal.{0}) : Prop := Wm.WmStepAt ℓ

/-- STATUS: PROVED (Wm.wm_old_vacuous, Wm.wm_gate_drop)
SIZE: S
the old package relation HnkExt K' K holds whenever K.g < K'.g (it says nothing across a gate drop), and gate drops
occur between levels: Ω₁·ω < Ω₁², gtc(Ω₁²) = 2 < ω = gtc(Ω₁·ω). -/
theorem skOldVacuous : (∀ K' K : Hn.HnPk, K.Λ.g < K'.Λ.g → Hn.HnkExt K' K) ∧
    SkLev (Om1 * ω) ∧ SkLev (Om1 * Om1) ∧ Om1 * ω < Om1 * Om1 ∧ Gf.gtc (Om1 * Om1) < Gf.gtc (Om1 * ω) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := Wm.wm_gate_drop
  refine ⟨fun _ _ h => Wm.wm_old_vacuous h, h1, h2, h3, ?_⟩
  rw [h4, h5]; exact natCast_lt_omega0 2

/-- STATUS: PROVED (Wm.wmExtE_old)
SIZE: S
SkExtW2 ⇒ SkExt (the corrected extension is stronger). -/
theorem skExtW2_old {E' E : SkEnt} (h : SkExtW2 E' E) : SkExt E' E := Wm.wmExtE_old h

/-- STATUS: PROVED (Wm.wmExtE_old)
SIZE: S
SkCohW2 ⇒ SkCohW. -/
theorem skCohW2_old {ℓ : Ordinal.{0}} {f : ∀ ℓ' : Ordinal.{0}, ℓ' < ℓ → SkEnt} (h : SkCohW2 ℓ f) : SkCohW ℓ f :=
  ⟨h.1, fun a b ha hb hab h1 h2 => Wm.wmExtE_old (h.2 a b ha hb hab h1 h2)⟩

/-- STATUS: PROVED (Wm.wmStep_base)
SIZE: S
the entry at Ω₁ (Hn.hnPk1, Hg.hgU) on SkCohW2. -/
theorem skStepBaseW2 : SkStepAtW2 Om1 := Wm.wmStep_base

/-- STATUS: PROVED (Wm.wmStep_succ: Wm.wmSucc_ext, Wm.wmSucc_ext_lt, Wh.whSucc_at, Wh.whSucc_ext_lt)
SIZE: M
ℓ = ℓ' + Ω₁ on SkCohW2. -/
theorem skStepSuccW2 : ∀ ℓ, SkLev ℓ → ShSucc ℓ → SkStepAtW2 ℓ := by
  rintro ℓ hℓ ⟨ℓ', hℓ', rfl⟩
  exact Wm.wmStep_succ hℓ' hℓ.2.2

/-- STATUS: PROVED (Wm.wmStep_fs: Wm.WmLim — the limit package Wm.wmPkL of a Wm.WmSeq and the gated ω-chain union
of the systems over G, Wm.WmLim.at_lim, Wm.WmLim.ext_below)
SIZE: M
every level with an ω-sequence of levels (strictly increasing, cofinal with room for +1, gates ≤ gtc ℓ), on
SkCohW2. -/
theorem skStepFsW2 : ∀ ℓ, SkLev ℓ → Wm.WmFs ℓ → SkStepAtW2 ℓ := fun _ hℓ h => Wm.wmStep_fs hℓ h

/-- STATUS: PROVED (Wm.wmStep_coef, Wm.wmFs_coef: ℓ_k = P + Ω₁^e·(c_k + 1), c_k = He.heFs c k)
SIZE: M
ℓ = P + Ω₁^e·c, c < Ω₁ limit, on SkCohW2. -/
theorem skStepCoefLimW2 : ∀ ℓ, SkLev ℓ → ShCoefLim ℓ → SkStepAtW2 ℓ := by
  rintro ℓ hℓ ⟨P, e, c, he, hc, hcO, hP, rfl⟩
  exact Wm.wmStep_coef he hc hcO hP hℓ

/-- STATUS: PROVED (Wm.wmStep_exp, Wm.wmFs_exp: ℓ_k = P + Ω₁^{e_k}; Wm.wmExpFs_digit / Wm.wmExpFs_lim supply the
ω-sequence of e when its last digit is a countable limit, or e = E + Ω₁^f·d' + Ω₁^f with f having one)
SIZE: M
ℓ = P + Ω₁^e, e limit with an ω-sequence of exponents (gates ≤ gtc e), on SkCohW2. -/
theorem skStepExpLimFsW2 : ∀ ℓ P e, SkLev ℓ → IsSuccLimit e → Om1 ^ e ∣ P → ℓ = P + Om1 ^ e → Wm.WmExpFs e →
    SkStepAtW2 ℓ := by
  rintro ℓ P e hℓ he hP rfl hE
  exact Wm.wmStep_exp he hP hE hℓ

/-- STATUS: OPEN
SIZE: L
THE ONE REMAINING STEP OF A1: every level ℓ < ε_{Ω₁+1} that is not Ω₁, not ℓ' + Ω₁ and has no ω-sequence (cofinality
Ω₁: P + Ω₁^{e+1}, and P + Ω₁^e with e of cofinality Ω₁), on SkCohW2.  Needed: for the members ℓ_v = P + Ω₁^e·v
(v < Ω₁; for an exponent limit, along e's own Ω₁-sequence), at every base datum (a pseudo-base Q of level ℓ for the
package, G for the system), a recursion of systems over the base through ALL levels in [P, ℓ) (successor: Hn.hnwU over
the base with the family's package at the level; ω-limits: the chain of WmSys over the base; Ω₁-limits: recursively
this step), then Ho.hoOU with SMALL (the gate of a member forces its index below σ); Ho.HoBR / Ho.HoStep are the case
P = 0, e = 1 with the band packages.  REFUTE FIRST: NO EVIDENCE against (no no-go result mentions systems over G or
pseudo-bases; the case ℓ = Ω₁²·(1+ν) is realised by the Ho stack with its own family). -/
theorem skStepOm1W2 : Wm.WmOm1Step Gf.gfE := by
  sorry

/-- STATUS: REDUCED (skStepBaseW2, skStepSuccW2, skStepFsW2, skStepOm1W2; Wm.wmStep_all)
SIZE: M
the step at every level on SkCohW2. -/
theorem skStepW2 : ∀ ℓ, SkLev ℓ → SkStepAtW2 ℓ := fun ℓ hℓ => Wm.wmStep_all skStepOm1W2 ℓ hℓ hℓ.2.2

/-- STATUS: PROVED (Wm.wmFam_sq, Wm.wmOm1Step_sq: below Ω₁² every level is Ω₁, a successor or has an ω-sequence)
SIZE: M
NON-VACUITY of SkCohW2: a family on all levels below Ω₁², every entry SkAtW, every pair SkExtW2, with no hypothesis. -/
theorem skFamSq : ∃ F : Ordinal.{0} → SkEnt, ∀ ℓ, SkLev ℓ → ℓ < Om1 * Om1 →
    SkAtW ℓ (F ℓ) ∧ ∀ ℓ', ℓ' < ℓ → SkLev ℓ' → SkExtW2 (F ℓ') (F ℓ) :=
  ⟨Wm.wmF _ Wm.wmOm1Step_sq, Wm.wmFam_sq⟩

/-! ## (A2) and (A3): the level codes past `ε_{Ω₁+1}` (round 116, leaf reg1)

The old cut `φ(G, G+1)` between (A2) and (A3) is not where the level codes change: the levels `ℓ < G` give
`sup_{ℓ<G} φ(ℓ, G+1) = φ(G, 1)` (`Wj.wjA2Cof`), so (A2) is `[φ(E, G+1), φ(G, 1))` and the levels `ℓ > G`
(`Wj.wjT n`, cofinal in `Γ(1)`, `Wj.wjA3Cof`) cover everything from `φ(G, 1)` to `Γ(1)`.

(A2) LEVEL-CODE TYPE: `ℓ = Ω₁^{e₁}·c₁ + … + Ω₁^{e_k}·c_k` (`Ω₁ ∣ ℓ`, `Ω₁ ≤ ℓ < G`), coefficients `0 < cᵢ < Ω₁`,
exponents `eᵢ < G` codes of the same kind, an exponent `≥ ε_{Ω₁+1}` being a Veblen node `φ(a, b)` (then
`Ω₁^{φ(a,b)} = φ(a, b)`), all hereditary countable leaves below the gate `Gl.glG ℓ`; reading `Gl.glR ℓ x`
(`Ω₁ ↦ x`, `= Gf.rdc ℓ x` below `ε_{Ω₁+1}`).  The gam41 induction extends verbatim with `(SkLev, rdc, gtc)`
replaced by `(SkLevG, glR, glG)`; on `ℓ < ε_{Ω₁+1}` the two agree (`skAtG_iff`).
(A3) LEVEL-CODE TYPE: the same normal forms with exponents over the atoms `{Ω₁, G}` (`G ↦ Γ_{x+1}`); readings
reach `ε_{Γ_{x+1}+1} > Γ_{x+1}`, so `Hn.HnLv` (field `l_lt : l x < Γ_{x+1}`) cannot carry them. -/

/-- The level codes of (A2): `Ω₁ ≤ ℓ`, `Ω₁ ∣ ℓ`, `ℓ < G`. -/
def SkLevG (ℓ : Ordinal.{0}) : Prop := Om1 ≤ ℓ ∧ Om1 ∣ ℓ ∧ ℓ < Gc.gcG 0

/-- The entry `E` sits at the level `ℓ` (reading `Gl.glR`, gate `Gl.glG`). -/
def SkAtG (ℓ : Ordinal.{0}) (E : SkEnt) : Prop :=
  E.1.Λ.L = ℓ ∧ (∀ x, InE x → x < Om1 → E.1.Λ.g < x → E.1.Λ.l x = Gl.glR ℓ x) ∧
    E.2.down.B = veblen ℓ (Gc.gcG 0 + 1) ∧ E.2.down.γ ≤ Gl.glG ℓ

def SkCohG (ℓ : Ordinal.{0}) (f : ∀ ℓ' : Ordinal.{0}, ℓ' < ℓ → SkEnt) : Prop :=
  (∀ ℓ' (h : ℓ' < ℓ), SkLevG ℓ' → SkAtG ℓ' (f ℓ' h)) ∧
    ∀ ℓ'' ℓ' (h'' : ℓ'' < ℓ) (h' : ℓ' < ℓ), ℓ'' < ℓ' → SkLevG ℓ'' → SkLevG ℓ' → SkExt (f ℓ'' h'') (f ℓ' h')

def SkStepAtG (ℓ : Ordinal.{0}) : Prop :=
  ∀ f, SkCohG ℓ f → ∃ E, SkAtG ℓ E ∧ ∀ ℓ' (h : ℓ' < ℓ), SkLevG ℓ' → SkExt (f ℓ' h) E

def ShSuccG (ℓ : Ordinal.{0}) : Prop := ∃ ℓ', SkLevG ℓ' ∧ ℓ = ℓ' + Om1

def SkDigitGateG : Prop :=
  ∀ Z, SC Z → Z ≤ Om 1 → ∀ y, Mx.GxCl Z {Gc.gcG 0} y → y < Gc.gcG 0 → Gl.glG y < Z

def SkReadExactG : Prop :=
  ∀ ℓ σ ρ, SkLevG ℓ → Bases σ ρ → Gl.glG ℓ < σ → Gl.glR ℓ ρ ∈ TB ρ σ ∧ pi σ ρ (Gl.glR ℓ ρ) = Gl.glR ℓ σ

def SkLvDatumAllG : Prop :=
  ∀ ℓ, SkLevG ℓ → ∃ Λ : Hn.HnLv, Λ.L = ℓ ∧ Λ.g ≤ Gl.glG ℓ ∧
    ∀ x, InE x → x < Om1 → Λ.g < x → Λ.l x = Gl.glR ℓ x

/-- STATUS: PROVED (Gl.glR_low, Gl.glG_low)
SIZE: S
ℓ < ε_{Ω₁+1}: SkAtG ℓ E ⇔ SkAt ℓ E (the A2 family restricts to the A1 family). -/
theorem skAtG_iff {ℓ : Ordinal.{0}} (hℓ : ℓ < Gf.gfE) (E : SkEnt) : SkAtG ℓ E ↔ SkAt ℓ E := by
  unfold SkAtG SkAt
  rw [Gl.glG_low hℓ]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, fun x a b c => by rw [h2 x a b c, Gl.glR_low hℓ], h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, fun x a b c => by rw [h2 x a b c, Gl.glR_low hℓ], h3, h4⟩

/-- STATUS: PROVED (Wj.wjDigitGateG)
SIZE: S
SC Z ≤ Ω₁, y < G a code over Z with the atom G ⇒ glG y < Z (digit gate on all of [0, G)). -/
theorem skDigitGateG : SkDigitGateG := Wj.wjDigitGateG

/-- STATUS: PROVED (Wj.wjReadExactG)
SIZE: S
∀ ℓ < G, glG ℓ < σ: glR ℓ ρ ∈ Tᵖ[σ] ∧ π(glR ℓ ρ) = glR ℓ σ. -/
theorem skReadExactG : SkReadExactG := fun ℓ _ _ hℓ hB hg => Wj.wjReadExactG ℓ _ _ hℓ.2.2 hB hg

/-- STATUS: PROVED (Wn.wnLvDatumAll; the level datum Wn.wnLv ℓ, gate = glG ℓ; the hypotheses are not needed)
SIZE: S
digit gate ∧ EXACT ⇒ level datum at every A2 level (port of skLvOfGate: (rdc, gtc) ↦ (glR, glG); HnLv allows
L < G, l x < Γ_{x+1}). -/
theorem skLvOfGateG : SkDigitGateG → SkReadExactG → SkLvDatumAllG := fun _ _ => Wn.wnLvDatumAll

/-- STATUS: PROVED (skLvOfGateG, skDigitGateG, skReadExactG)
SIZE: S -/
theorem skLvDatumG : SkLvDatumAllG := skLvOfGateG skDigitGateG skReadExactG

/-- STATUS: PROVED (Wn.wnShape)
SIZE: S
Cantor normal form in base Ω₁ (no use of the bound): ℓ = Ω₁ ∨ succ ∨ pow ∨ exp-limit ∨ coefficient-limit. -/
theorem skShapeG : ∀ ℓ, SkLevG ℓ → ℓ = Om1 ∨ ShSuccG ℓ ∨ ShPow ℓ ∨ ShExpLim ℓ ∨ ShCoefLim ℓ :=
  fun ℓ h => Wn.wnShape ℓ h.1 h.2.1 h.2.2

/-- STATUS: REDUCED (skStepBase)
SIZE: S
the entry at ℓ = Ω₁ (both families are vacuous below Ω₁; skAtG_iff at Ω₁). -/
theorem skStepBaseG : SkStepAtG Om1 := by
  intro f _
  have hOE : (Om1 : Ordinal.{0}) < Gf.gfE := Gf.Om1_lt_eW
  have hf' : SkCoh Om1 (fun ℓ' h => f ℓ' h) :=
    ⟨fun _ h h' => absurd h'.1 (not_le.2 h), fun _ _ _ h' _ _ h2 => absurd h2.1 (not_le.2 h')⟩
  obtain ⟨E, hE, -⟩ := skStepBase _ hf'
  exact ⟨E, (skAtG_iff hOE E).2 hE, fun _ h h' => absurd h'.1 (not_le.2 h)⟩

/-- STATUS: REPLACED (by skStepSuccWG: SkAtG, like SkAt, has no start condition of the system over G at the package,
so the step would have to extend an ARBITRARY digit system; NO EVIDENCE against)
SIZE: M
ℓ = ℓ' + Ω₁ (skStepSucc's proof with (rdc, gtc, ε_{Ω₁+1}) ↦ (glR, glG, G)). -/
theorem skStepSuccG (hLv : SkLvDatumAllG) : ∀ ℓ, SkLevG ℓ → ShSuccG ℓ → SkStepAtG ℓ := by
  sorry

/-- STATUS: REPLACED (by skStepPowWG; same reason as skStepSuccG)
SIZE: M
ℓ = P + Ω₁^{e+1} (skStepPow's proof, same substitution). -/
theorem skStepPowG (hLv : SkLvDatumAllG) : ∀ ℓ, SkLevG ℓ → ShPow ℓ → SkStepAtG ℓ := by
  sorry

/-- STATUS: REPLACED (by skStepCoefLimWG; same reason as skStepSuccG)
SIZE: M
ℓ = P + Ω₁^e·c, c < Ω₁ limit (skStepCoefLim's proof, same substitution). -/
theorem skStepCoefLimG (hLv : SkLvDatumAllG) : ∀ ℓ, SkLevG ℓ → ShCoefLim ℓ → SkStepAtG ℓ := by
  sorry

/-- STATUS: REPLACED (by skStepExpLimWG; same reason as skStepSuccG)
SIZE: M
ℓ = P + Ω₁^e, e limit; NEW cases e = φ(a, b) ≥ ε_{Ω₁+1} (Ω₁^e = e): the union along the Veblen fundamental
sequence read by glR (b limit: over b' < b; b = b'+1 or 0 with a = a'+1: ω-chain of φ(a', ·)-iterates;
a limit: over a' < a; cofinality ω or Ω₁; codes Gl.glCfn). -/
theorem skStepExpLimG (hLv : SkLvDatumAllG) (hG : SkDigitGateG) : ∀ ℓ, SkLevG ℓ → ShExpLim ℓ → SkStepAtG ℓ := by
  sorry

/-- STATUS: REPLACED (by skStepWG; it rests on the REPLACED SkAtG steps)
SIZE: M -/
theorem skStepG : ∀ ℓ, SkLevG ℓ → SkStepAtG ℓ := by
  intro ℓ hℓ
  rcases skShapeG ℓ hℓ with h | h | h | h | h
  · subst h; exact skStepBaseG
  · exact skStepSuccG skLvDatumG ℓ hℓ h
  · exact skStepPowG skLvDatumG ℓ hℓ h
  · exact skStepExpLimG skLvDatumG skDigitGateG ℓ hℓ h
  · exact skStepCoefLimG skLvDatumG ℓ hℓ h

noncomputable def skGG (ℓ : Ordinal.{0}) (f : ∀ ℓ' : Ordinal.{0}, ℓ' < ℓ → SkEnt) : SkEnt := by
  classical
  exact if h : SkLevG ℓ ∧ SkCohG ℓ f then Classical.choose (skStepG ℓ h.1 f h.2) else (Hn.hnPk1, ULift.up Ho.hoUf)

noncomputable def skFG : Ordinal.{0} → SkEnt := Ordinal.lt_wf.fix skGG

/-- STATUS: REPLACED (by skFamWG; it rests on skStepG)
SIZE: M
one generic induction over every level ℓ < G (gam41's skFam with SkLev ↦ SkLevG). -/
theorem skFamG : ∃ F : Ordinal.{0} → SkEnt,
    ∀ ℓ, SkLevG ℓ → SkAtG ℓ (F ℓ) ∧ ∀ ℓ', ℓ' < ℓ → SkLevG ℓ' → SkExt (F ℓ') (F ℓ) := by
  refine ⟨skFG, fun ℓ => ?_⟩
  induction ℓ using WellFoundedLT.induction with
  | _ ℓ ih =>
    intro hℓ
    have hcoh : SkCohG ℓ (fun ℓ' _ => skFG ℓ') :=
      ⟨fun ℓ' h h' => (ih ℓ' h h').1, fun ℓ'' ℓ' _ h' hlt h1 h2 => (ih ℓ' h' h2).2 ℓ'' hlt h1⟩
    have heq : skFG ℓ = skGG ℓ (fun ℓ' _ => skFG ℓ') := Ordinal.lt_wf.fix_eq skGG ℓ
    have hsp := Classical.choose_spec (skStepG ℓ hℓ (fun ℓ' _ => skFG ℓ') hcoh)
    have hG : skGG ℓ (fun ℓ' _ => skFG ℓ') = Classical.choose (skStepG ℓ hℓ (fun ℓ' _ => skFG ℓ') hcoh) := by
      unfold skGG; rw [dif_pos ⟨hℓ, hcoh⟩]
    rw [heq, hG]
    exact ⟨hsp.1, fun ℓ' h h' => hsp.2 ℓ' h h'⟩

/-! ### The (A2) induction on the corrected entry predicate `SkAtWG` (round 117, leaf reg2) -/

/-- The corrected (A2) entry predicate: `Wn.WnAt` (package at `ℓ` read `glR ℓ x`, gate `≤ glG ℓ`, every
`ε`-number above the gate is above `glG ℓ`, the system is a start over `G` at the package for the base `Wn.wnGW`). -/
def SkAtWG (ℓ : Ordinal.{0}) (E : SkEnt) : Prop := Wn.WnAt ℓ E.1 E.2.down

def SkCohWG (ℓ : Ordinal.{0}) (f : ∀ ℓ' : Ordinal.{0}, ℓ' < ℓ → SkEnt) : Prop :=
  (∀ ℓ' (h : ℓ' < ℓ), SkLevG ℓ' → SkAtWG ℓ' (f ℓ' h)) ∧
    ∀ ℓ'' ℓ' (h'' : ℓ'' < ℓ) (h' : ℓ' < ℓ), ℓ'' < ℓ' → SkLevG ℓ'' → SkLevG ℓ' → SkExt (f ℓ'' h'') (f ℓ' h')

def SkStepAtWG (ℓ : Ordinal.{0}) : Prop :=
  ∀ f, SkCohWG ℓ f → ∃ E, SkAtWG ℓ E ∧ ∀ ℓ' (h : ℓ' < ℓ), SkLevG ℓ' → SkExt (f ℓ' h) E

/-- STATUS: PROVED (definitions)
SIZE: S
SkAtWG ℓ E ⇒ SkAtG ℓ E (the corrected entry is an entry of reg1's family). -/
theorem skAtWG_G {ℓ : Ordinal.{0}} {E : SkEnt} (h : SkAtWG ℓ E) : SkAtG ℓ E :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- STATUS: PROVED (Wn.wnAt_base)
SIZE: S
the entry at ℓ = Ω₁ for SkAtWG: Hn.hnPk1 and Hg.hgU (Hg.hgU is a start over Wn.wnGW Hn.hnL1, Wn.wnU_shape). -/
theorem skStepBaseWG : SkStepAtWG Om1 := fun _ _ =>
  ⟨(Hn.hnPk1, ULift.up Hg.hgU), Wn.wnAt_base, fun _ h hl => absurd hl.1 (not_le.2 h)⟩

/-- STATUS: PROVED (Wn.wnSucc_at, Wn.wnSucc_ext, Wn.wnSucc_ext_lt)
SIZE: M
ℓ = ℓ' + Ω₁ < G: package Hn.HnPk.succ, G-system = the union over G (Wn.wnGW) started at the system at ℓ'. -/
theorem skStepSuccWG : ∀ ℓ, SkLevG ℓ → ShSuccG ℓ → SkStepAtWG ℓ := by
  rintro ℓ hℓ ⟨ℓ', hℓ', rfl⟩ f ⟨hat, hext⟩
  have hlt : ℓ' < ℓ' + Om1 := lt_add_of_pos_right _ Wh.wh_Om1_pos
  have hat' := hat ℓ' hlt hℓ'
  refine ⟨((f ℓ' hlt).1.succ, ULift.up (Wn.wnSuccV hat')), Wn.wnSucc_at hℓ'.2.1 hℓ'.2.2 hat',
    fun ℓ'' h'' hℓ'' => ?_⟩
  have hle : ℓ'' ≤ ℓ' := not_lt.1 fun h => absurd h'' (not_lt.2 (Wh.wh_lev_succ_le hℓ'.2.1 hℓ''.2.1 h))
  rcases hle.lt_or_eq with hl | rfl
  · exact Wn.wnSucc_ext_lt hℓ'.2.1 hℓ'.2.2 hat' hl hℓ''.2.1 (hat ℓ'' h'' hℓ'') (hext ℓ'' ℓ' h'' hlt hl hℓ'' hℓ')
  · exact Wn.wnSucc_ext hat'

/-- STATUS: OPEN
SIZE: M
ℓ = P + Ω₁^{e+1} < G, for SkAtWG (gam41's skStepPowW with (rdc, gtc, whGW) ↦ (glR, glG, wnGW); the union over
the prefixes P + Ω₁^e·v, v < Ω₁, uses the gate-lowering extension of leaf gam42 (round 117)). -/
theorem skStepPowWG : ∀ ℓ, SkLevG ℓ → ShPow ℓ → SkStepAtWG ℓ := by
  sorry

/-- STATUS: OPEN
SIZE: M
ℓ = P + Ω₁^e·c < G, c < Ω₁ limit, for SkAtWG (gam41's skStepCoefLimW, same substitution; gam42's extension). -/
theorem skStepCoefLimWG : ∀ ℓ, SkLevG ℓ → ShCoefLim ℓ → SkStepAtWG ℓ := by
  sorry

/-- STATUS: OPEN
SIZE: M
ℓ = P + Ω₁^e < G, e limit, for SkAtWG; besides gam41's cases the exponents e = φ(a, b) ≥ ε_{Ω₁+1} (Ω₁^e = e):
the union along the Veblen fundamental sequence read by glR (cofinality ω or Ω₁; codes Gl.glCfn). -/
theorem skStepExpLimWG : ∀ ℓ, SkLevG ℓ → ShExpLim ℓ → SkStepAtWG ℓ := by
  sorry

/-- STATUS: REDUCED (skShapeG, skStepBaseWG, skStepSuccWG, skStepPowWG, skStepExpLimWG, skStepCoefLimWG)
SIZE: M -/
theorem skStepWG : ∀ ℓ, SkLevG ℓ → SkStepAtWG ℓ := by
  intro ℓ hℓ
  rcases skShapeG ℓ hℓ with h | h | h | h | h
  · subst h; exact skStepBaseWG
  · exact skStepSuccWG ℓ hℓ h
  · exact skStepPowWG ℓ hℓ h
  · exact skStepExpLimWG ℓ hℓ h
  · exact skStepCoefLimWG ℓ hℓ h

noncomputable def skGWG (ℓ : Ordinal.{0}) (f : ∀ ℓ' : Ordinal.{0}, ℓ' < ℓ → SkEnt) : SkEnt := by
  classical
  exact if h : SkLevG ℓ ∧ SkCohWG ℓ f then Classical.choose (skStepWG ℓ h.1 f h.2) else (Hn.hnPk1, ULift.up Ho.hoUf)

noncomputable def skFWG : Ordinal.{0} → SkEnt := Ordinal.lt_wf.fix skGWG

/-- STATUS: REDUCED (skStepWG)
SIZE: M
one generic induction over every level ℓ < G on SkAtWG. -/
theorem skFamWG : ∃ F : Ordinal.{0} → SkEnt,
    ∀ ℓ, SkLevG ℓ → SkAtWG ℓ (F ℓ) ∧ ∀ ℓ', ℓ' < ℓ → SkLevG ℓ' → SkExt (F ℓ') (F ℓ) := by
  refine ⟨skFWG, fun ℓ => ?_⟩
  induction ℓ using WellFoundedLT.induction with
  | _ ℓ ih =>
    intro hℓ
    have hcoh : SkCohWG ℓ (fun ℓ' _ => skFWG ℓ') :=
      ⟨fun ℓ' h h' => (ih ℓ' h h').1, fun ℓ'' ℓ' _ h' hlt h1 h2 => (ih ℓ' h' h2).2 ℓ'' hlt h1⟩
    have heq : skFWG ℓ = skGWG ℓ (fun ℓ' _ => skFWG ℓ') := Ordinal.lt_wf.fix_eq skGWG ℓ
    have hsp := Classical.choose_spec (skStepWG ℓ hℓ (fun ℓ' _ => skFWG ℓ') hcoh)
    have hG : skGWG ℓ (fun ℓ' _ => skFWG ℓ') = Classical.choose (skStepWG ℓ hℓ (fun ℓ' _ => skFWG ℓ') hcoh) := by
      unfold skGWG; rw [dif_pos ⟨hℓ, hcoh⟩]
    rw [heq, hG]
    exact ⟨hsp.1, fun ℓ' h h' => hsp.2 ℓ' h h'⟩

/-- STATUS: REDUCED (skFamWG; was REDUCED (skFamG))
SIZE: M -/
theorem skSysAllG : ∀ ℓ, SkLevG ℓ → ∃ V : Hg.HgVD, V.B = veblen ℓ (Gc.gcG 0 + 1) ∧ V.γ ≤ Gl.glG ℓ := by
  intro ℓ hℓ
  obtain ⟨F, hF⟩ := skFamWG
  exact ⟨(F ℓ).2.down, (hF ℓ hℓ).1.2.2.1, (hF ℓ hℓ).1.2.2.2.1⟩

/-- STATUS: PROVED (Gl.glBn_spec, Gf.Om1_lt_eW, Rj.rj_Om1_inE)
SIZE: S
the cofinal levels glBn n (glBn 0 = φ(ω, Ω₁+1), glBn (n+1) = φ(glBn n, 0)) are A2 level codes. -/
theorem skLevG_Bn (n : ℕ) : SkLevG (Gl.glBn n) := by
  obtain ⟨hlt, hE, hInE, -⟩ := Gl.glBn_spec n
  have hO : (Om1 : Ordinal.{0}) ≤ Gl.glBn n := (Gf.Om1_lt_eW.trans hE).le
  refine ⟨hO, ?_, hlt⟩
  have h := opow_dvd_opow ω hO
  rwa [Rj.rj_Om1_inE, hInE] at h

/-- STATUS: PROVED (Wn.wnGateBnK: glBn n is a code over Γ₀ with the atom G, so glG (glBn n) < Γ₀ ≤ K)
SIZE: S
the gate of the cofinal levels is small: glG (glBn n) < K. -/
theorem skGateBn (S : InaccSeq.{0}) : ∀ n, Gl.glG (Gl.glBn n) < Td.tdK S := Wn.wnGateBnK S

/-- STATUS: REDUCED (skSysAllG, skLevG_Bn, skGateBn)
SIZE: M
∀ n ∃ system V: B_V = φ(glBn n, G+1), γ_V < K. -/
theorem skSysA2Lev (S : InaccSeq.{0}) : ∀ n, ∃ V : Hg.HgVD, V.B = veblen (Gl.glBn n) (Gc.gcG 0 + 1) ∧
    V.γ < Td.tdK S := by
  intro n
  obtain ⟨V, hB, hγ⟩ := skSysAllG _ (skLevG_Bn n)
  exact ⟨V, hB, hγ.trans_lt (skGateBn S n)⟩

/-- A3 package at the ladder level `t_n` (only the system; see skSysA3Step). -/
def SkPk3 (S : InaccSeq.{0}) (n : ℕ) : Prop :=
  ∃ V : Hg.HgVD, V.B = veblen (Wj.wjT n) (Gc.gcG 0 + 1) ∧ V.γ < Td.tdK S

/-! ### (A3) on the new level datum (round 117, leaf reg2) -/

/-- STATUS: PROVED (Wn.wnHnLv_lt_T0, Wn.wnHnLv_noRead)
SIZE: S
REFUTE-FIRST of the old datum: every Hn.HnLv lies below t₀ and never reads ε_{Γ_{x+1}+1}. -/
theorem skA3NoBand : (∀ Λ : Hn.HnLv, Λ.L < Wj.wjT 0) ∧
    ∀ (Λ : Hn.HnLv) (x : Ordinal.{0}), InE x → x < Om1 → Λ.l x ≠ eN (lgG x) :=
  ⟨Wn.wnHnLv_lt_T0, fun Λ _ hx hx1 => Wn.wnHnLv_noRead Λ hx hx1⟩

/-- STATUS: PROVED (Wn.wnG_notRange, Wn.wnA3_bound)
SIZE: S
at L > G: G ∉ range φ(L, ·) (no start over G as in (A1)/(A2)); φ(L, G+1) = hdNx L (φ(L, G)). -/
theorem skA3NoGBase : ∀ L, Gc.gcG 0 < L →
    ¬ Lu.LuP L (Gc.gcG 0) ∧ veblen L (Gc.gcG 0 + 1) = Hd.hdNx L (veblen L (Gc.gcG 0)) :=
  fun L hL => ⟨Wn.wnG_notRange hL, Wn.wnA3_bound L⟩

/-- STATUS: PROVED (Wn.wnLv3T0)
SIZE: S
NON-VACUITY of the (A3) datum: ∃ Λ : WnLv3, L = t₀, gate 0, reading ε_{Γ_{x+1}+1}. -/
theorem skA3Datum0 : ∃ Λ : Wn.WnLv3, Λ.L = Wj.wjT 0 ∧ Λ.g = 0 ∧
    ∀ x, InE x → x < Om1 → Λ.l x = eN (lgG x) :=
  ⟨Wn.wnLv3T0, rfl, rfl, fun _ hx hx1 => Wn.wnLv3T0_l hx hx1⟩

/-- The (A3) invariant at `t_n` with the FULL package (`Wn.WnEnt3`). -/
def SkPk3W (S : InaccSeq.{0}) (n : ℕ) : Prop := Wn.WnEnt3 S n

/-- STATUS: PROVED (Wn.wnEnt3_sys)
SIZE: S
the full invariant gives the old one: SkPk3W S n ⇒ SkPk3 S n. -/
theorem skPk3_of_W (S : InaccSeq.{0}) (n : ℕ) (h : SkPk3W S n) : SkPk3 S n := Wn.wnEnt3_sys h

/-- STATUS: OPEN
SIZE: L
the (A3) package at t₀ = ε_{G+1} (Wn.WnPk3 on a datum with L = t₀, e.g. Wn.wnLv3T0: a step at every pseudo-base
of level t₀) and the pseudo-base φ(t₀, G) of level t₀ with gate < K and a system starting it (Wn.wnQ3_bounds gives
its bound fields). -/
theorem skSysA3Lev0W (S : InaccSeq.{0}) : SkPk3W S 0 := by
  sorry

/-- STATUS: OPEN
SIZE: L
t_n ↦ t_{n+1} = φ(t_n, 0) with the full package as invariant: the (A3) level induction over the codes in
(t_n, t_{n+1}] (the (A2) induction one level up: atoms {Ω₁, G}, readings Γ_{x+1} < ℓ(x) < Γ_{x+2}), then the
pseudo-base φ(t_{n+1}, G) (reached by the offset recursion of level t_{n+1} along the second argument up to G). -/
theorem skSysA3StepW (S : InaccSeq.{0}) : ∀ n, SkPk3W S n → SkPk3W S (n + 1) := by
  sorry

/-- STATUS: REDUCED (skSysA3Lev0W, skSysA3StepW)
SIZE: L -/
theorem skSysA3LevW (S : InaccSeq.{0}) : ∀ n, SkPk3W S n := by
  intro n
  induction n with
  | zero => exact skSysA3Lev0W S
  | succ n ih => exact skSysA3StepW S n ih

/-- STATUS: REDUCED (skSysA3Lev0W, skPk3_of_W; was OPEN L)
SIZE: L
the first level above G: t₀ = ε_{G+1}; system φ(ε_{G+1}, G+1). -/
theorem skSysA3Lev0 (S : InaccSeq.{0}) : SkPk3 S 0 := skPk3_of_W S 0 (skSysA3Lev0W S)

/-- STATUS: REPLACED (by skSysA3StepW; SUSPECT CONFIRMED: the invariant SkPk3 carries no level datum, so the
hypothesis gives nothing toward the package at t_{n+1}; Lean fact behind it: skA3NoGBase, the (A3) system is the step
of the level package at the pseudo-base φ(t_n, G), which SkPk3 does not hold.  NO EVIDENCE that it is false)
SIZE: M
t_n ↦ t_{n+1} = φ(t_n, 0): the Veblen-exponent union (skStepExpLimG one level up, atoms {Ω₁, G}). -/
theorem skSysA3Step (S : InaccSeq.{0}) : ∀ n, SkPk3 S n → SkPk3 S (n + 1) := by
  sorry

/-- STATUS: REDUCED (skSysA3LevW, skPk3_of_W; was REDUCED (skSysA3Lev0, skSysA3Step))
SIZE: L -/
theorem skSysA3Lev (S : InaccSeq.{0}) : ∀ n, SkPk3 S n := fun n => skPk3_of_W S n (skSysA3LevW S n)

/-- STATUS: REDUCED (Wj.wjA3Cof, skSysA3Lev)
SIZE: L
∀ B < Γ(1) ∃ system V: B ≤ B_V, γ_V < K. -/
theorem skSysA3All (S : InaccSeq.{0}) : ∀ B, B < Gc.gcG 1 → ∃ V : Hg.HgVD, B ≤ V.B ∧ V.γ < Td.tdK S := by
  intro B hB
  obtain ⟨n, hn⟩ := Wj.wjA3Cof hB
  obtain ⟨V, hVB, hγ⟩ := skSysA3Lev S n
  exact ⟨V, hVB ▸ hn.le, hγ⟩

/-- STATUS: REDUCED (Wj.wjA2Cof, skSysA2Lev, skSysA3All; was OPEN L)
SIZE: L
(A2) ∀ B ∈ [φ(ε_{Ω₁+1}, G+1), φ(G, G+1)) ∃ system V, B ≤ B_V, γ_V < K: below φ(G, 1) by the A2 levels glBn n,
from φ(G, 1) on by the A3 levels. -/
theorem skSysA2 (S : InaccSeq.{0}) : ∀ B, veblen Gf.gfE (Gc.gcG 0 + 1) ≤ B →
    B < veblen (Gc.gcG 0) (Gc.gcG 0 + 1) → ∃ V : Hg.HgVD, B ≤ V.B ∧ V.γ < Td.tdK S := by
  intro B _ hB
  rcases lt_or_ge B (veblen (Gc.gcG 0) 1) with h | h
  · obtain ⟨n, hn⟩ := Wj.wjA2Cof h
    obtain ⟨V, hVB, hγ⟩ := skSysA2Lev S n
    exact ⟨V, hVB ▸ hn.le, hγ⟩
  · exact skSysA3All S B (hB.trans (Wj.wjVeb_lt_G1 Wj.wjG_lt_G1 Wj.wjG1_lt))

/-- STATUS: REDUCED (skSysA3All; was OPEN L)
SIZE: L
(A3) levels above G: ∀ B ∈ [φ(G, G+1), Γ(1)) ∃ system V, B ≤ B_V, γ_V < K. -/
theorem skSysA3 (S : InaccSeq.{0}) : ∀ B, veblen (Gc.gcG 0) (Gc.gcG 0 + 1) ≤ B →
    B < Gc.gcG 1 → ∃ V : Hg.HgVD, B ≤ V.B ∧ V.γ < Td.tdK S := fun B _ hB => skSysA3All S B hB

/-! ## (B) ∪ (C): the re-split by the windows `[L(k), L(k+1))` (round 116, leaf reg1)

`Wj.wjSplit`: every range restart is in exactly one of (A), (B-lo), (B-hi), (C), `W_k` (`k < ω`), `W_ω`.
Above `L(0)` every name is `Ω_ω + β`, `0 < β < P′·(ω+1) < Ω₂`, so `e(η) < Ω₂` and the code is the offset code
(`Wj.wjWin_props`); hence (C) lies below `L(0)` (`Wj.wjExpHi_low`) and `skLongMid`, `skLongTop` are vacuous. -/

/-- The window offset `ζ = η_λ - b_ξ` is a copy of a region-(A) name. -/
def SkOffA (S : InaccSeq.{0}) (ξ l : Ordinal.{0}) : Prop :=
  ∃ B, B < Gc.gcG 1 ∧ Cd.cdEta S l - Wj.wjBase S ξ < Gc.gcG B * ω

/-- STATUS: OPEN
SIZE: L
(B-lo) the intended region (B): past (A), υ_λ < L(0), e(η) < Ω₂, λ < ι(Ω₂) (codes with atoms Γ(c), c ≥ 1;
names η < Ω₂). -/
theorem skRegBlo (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → Wj.WjNotA S l → upsilon l < Nc.ncL S 0 →
    Cd.cdExp (Cd.cdEta S l) < Om (1 + 1) → l < Bt.iota S (Om (1 + 1)) → SkUV S l := by
  sorry

/-- STATUS: OPEN
SIZE: L
(B-hi) names Ω₂ ≤ η < Ω_ω with last exponent < Ω₂ (offset codes), υ_λ < L(0). -/
theorem skRegBhi (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → Wj.WjNotA S l → upsilon l < Nc.ncL S 0 →
    Cd.cdExp (Cd.cdEta S l) < Om (1 + 1) → Bt.iota S (Om (1 + 1)) ≤ l → SkUV S l := by
  sorry

/-- STATUS: OPEN (as strong as: ν_C is in no window W_k, Wj.wjUV_ne_nuC)
SIZE: L
(W_k, A-type) L(k) < υ_λ < L(k+1), offset ζ = η - (Ω_ω + P′·k) a copy of a region-(A) name. -/
theorem skWinA (S : InaccSeq.{0}) : ∀ k : ℕ, ∀ l, Cd.CdRange S l → Wj.WjWin S k l → SkOffA S k l →
    SkUV S l := by
  sorry

/-- STATUS: OPEN (as strong as: ν_C is in no window W_k)
SIZE: L
(W_k, B-type) L(k) < υ_λ < L(k+1), offset past every copy of a region-(A) frontier (ζ < P′). -/
theorem skWinB (S : InaccSeq.{0}) : ∀ k : ℕ, ∀ l, Cd.CdRange S l → Wj.WjWin S k l → ¬ SkOffA S k l →
    SkUV S l := by
  sorry

/-- STATUS: OPEN (as strong as: ν_C ∉ (L(ω), L(ω+1)); with skWin* and Sh.shNu this is L(ω+1) ≤ ν_C)
SIZE: L
(W_ω, A-type) L(ω) < υ_λ < L(ω+1), offset a copy of a region-(A) name (hVt lives here). -/
theorem skTopA (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → Wj.WjTop S l → SkOffA S ω l → SkUV S l := by
  sorry

/-- STATUS: OPEN (as strong as: ν_C ∉ (L(ω), L(ω+1)))
SIZE: L
(W_ω, B-type). -/
theorem skTopB (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → Wj.WjTop S l → ¬ SkOffA S ω l → SkUV S l := by
  sorry

/-- STATUS: REDUCED (skWinA, skWinB)
SIZE: L
every window W_k. -/
theorem skWin (S : InaccSeq.{0}) : ∀ k : ℕ, ∀ l, Cd.CdRange S l → Wj.WjWin S k l → SkUV S l := by
  intro k l hr hw
  by_cases h : SkOffA S k l
  · exact skWinA S k l hr hw h
  · exact skWinB S k l hr hw h

/-- STATUS: REDUCED (skTopA, skTopB)
SIZE: L
the top window W_ω. -/
theorem skTop (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → Wj.WjTop S l → SkUV S l := by
  intro l hr hw
  by_cases h : SkOffA S ω l
  · exact skTopA S l hr hw h
  · exact skTopB S l hr hw h

/-- STATUS: REDUCED (Wj.wjRegB_iff, skRegBlo, skRegBhi, skWin, skTop; was SUSPECT, mis-scoped)
SIZE: L
(B) as stated in round 115 = (B-lo) ∪ (B-hi) ∪ every window ∪ the top window (exactly, Wj.wjRegB_iff). -/
theorem skRegB (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l →
    (∀ B, B < Gc.gcG 1 → Bt.iota S (Gc.gcG B * ω) ≤ l) → Cd.cdExp (Cd.cdEta S l) < Om (1 + 1) → SkUV S l :=
  (Wj.wjRegB_iff (S := S) (SkUV S)).2 ⟨skRegBlo S, skRegBhi S, skWin S, skTop S⟩

/-- STATUS: OPEN
SIZE: L
(C) = (C1): names with e(η_λ) ≥ Ω₂ (code π_η, ι(Ω₂) ≤ λ, Wj.wjC_props); all of (C) lies below L(0)
(Wj.wjExpHi_low). -/
theorem skLongPre (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → Om (1 + 1) ≤ Cd.cdExp (Cd.cdEta S l) →
    upsilon l < Nc.ncL S 0 → SkUV S l := by
  sorry

/-- STATUS: PROVED (Wj.wjLongMid: VACUOUS, no such restart)
SIZE: S
(C2) range λ with e(η_λ) ≥ Ω₂ and L(0) ≤ υ_λ ≤ L(ω). -/
theorem skLongMid (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → Om (1 + 1) ≤ Cd.cdExp (Cd.cdEta S l) →
    Nc.ncL S 0 ≤ upsilon l → upsilon l ≤ Nc.ncL S ω → SkUV S l :=
  Wj.wjLongMid (SkUV S)

/-- STATUS: PROVED (Wj.wjLongTop: VACUOUS, no such restart)
SIZE: S
(C3) range λ with e(η_λ) ≥ Ω₂ and L(ω) < υ_λ. -/
theorem skLongTop (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → Om (1 + 1) ≤ Cd.cdExp (Cd.cdEta S l) →
    Nc.ncL S ω < upsilon l → SkUV S l :=
  Wj.wjLongTop (SkUV S)

/-- STATUS: PROVED (Wj.wjSplit, Wj.wjSplit_excl, Wj.wjWin_disj, Wj.wjWin_props, Wj.wjC_props)
SIZE: S
THE SPLIT: every range restart is in (A) ∨ (B-lo) ∨ (B-hi) ∨ (C) ∨ ∃k W_k ∨ W_ω, the pieces exclusive. -/
theorem skSplit (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : Cd.CdRange S l) :
    (∃ B, B < Gc.gcG 1 ∧ l < Bt.iota S (Gc.gcG B * ω)) ∨
    (Wj.WjNotA S l ∧ upsilon l < Nc.ncL S 0 ∧ Cd.cdExp (Cd.cdEta S l) < Om (1 + 1) ∧
      l < Bt.iota S (Om (1 + 1))) ∨
    (Wj.WjNotA S l ∧ upsilon l < Nc.ncL S 0 ∧ Cd.cdExp (Cd.cdEta S l) < Om (1 + 1) ∧
      Bt.iota S (Om (1 + 1)) ≤ l) ∨
    (upsilon l < Nc.ncL S 0 ∧ Om (1 + 1) ≤ Cd.cdExp (Cd.cdEta S l)) ∨
    (∃ k : ℕ, Wj.WjWin S k l) ∨ Wj.WjTop S l :=
  Wj.wjSplit hr

/-- STATUS: PROVED (Wj.wjWin_nonempty)
SIZE: S
non-vacuity: every window W_k contains range restarts. -/
theorem skWinNonempty (S : InaccSeq.{0}) (k : ℕ) : ∃ l, Cd.CdRange S l ∧ Wj.WjWin S k l :=
  Wj.wjWin_nonempty k

/-! ## REDUCED nodes -/

/-- STATUS: PROVED (skLvOfGate, skDigitGate, skReadExact)
SIZE: M
∀ ℓ (Ω₁ ≤ ℓ, Ω₁ ∣ ℓ, ℓ < ε_{Ω₁+1}) ∃ level datum Λ: L = ℓ, l(x) = rdc ℓ x above g ≤ gtc ℓ. -/
theorem skLvDatum : SkLvDatumAll := skLvOfGate skDigitGate skReadExact

/-- STATUS: REPLACED (round 117: by skStepW2 on SkCohW2; its leaves skStepPowW / skStepExpLimW / skStepCoefLimW are
REPLACED; not used)
SIZE: M
∀ ℓ: the step at ℓ for SkAtW (every coherent family below ℓ extends to ℓ). -/
theorem skStep : ∀ ℓ, SkLev ℓ → SkStepAtW ℓ := by
  intro ℓ hℓ
  rcases skShape ℓ hℓ with h | h | h | h | h
  · subst h; exact skStepBaseW
  · exact skStepSuccW ℓ hℓ h
  · exact skStepPowW ℓ hℓ h
  · exact skStepExpLimW ℓ hℓ h
  · exact skStepCoefLimW ℓ hℓ h

/-- STATUS: REDUCED (skStepOm1W2; Wm.wmFam on SkCohW2, Wm.wmExtE_old; statement unchanged)
SIZE: M
∃ F: ∀ ℓ (SkLev): F ℓ at ℓ (SkAtW) ∧ ∀ ℓ' < ℓ (SkLev): F ℓ extends F ℓ'  (one generic induction over ℓ). -/
theorem skFam : ∃ F : Ordinal.{0} → SkEnt,
    ∀ ℓ, SkLev ℓ → SkAtW ℓ (F ℓ) ∧ ∀ ℓ', ℓ' < ℓ → SkLev ℓ' → SkExt (F ℓ') (F ℓ) :=
  ⟨Wm.wmF _ skStepOm1W2, fun ℓ hℓ => ⟨(Wm.wmFam skStepOm1W2 ℓ hℓ hℓ.2.2).1,
    fun ℓ' h h' => Wm.wmExtE_old ((Wm.wmFam skStepOm1W2 ℓ hℓ hℓ.2.2).2 ℓ' h h')⟩⟩

/-- STATUS: REDUCED (skFam)
SIZE: M
∀ ℓ (SkLev) ∃ system V over G: B_V = φ(ℓ, G+1), γ_V ≤ gtc ℓ. -/
theorem skSysAll : ∀ ℓ, SkLev ℓ → ∃ V : Hg.HgVD, V.B = veblen ℓ (Gc.gcG 0 + 1) ∧ V.γ ≤ Gf.gtc ℓ := by
  intro ℓ hℓ
  obtain ⟨F, hF⟩ := skFam
  exact ⟨(F ℓ).2.down, (hF ℓ hℓ).1.2.2.1, (hF ℓ hℓ).1.2.2.2.1⟩

/-- STATUS: REDUCED (skSysAll, skCofLev; i.e. only skStepOm1W2 — Wm.wmSysA1)
SIZE: M
(A1) ∀ B < φ(ε_{Ω₁+1}, G+1) ∃ system V: B ≤ B_V, γ_V < K. -/
theorem skSysA1 (S : InaccSeq.{0}) : ∀ B, B < veblen Gf.gfE (Gc.gcG 0 + 1) →
    ∃ V : Hg.HgVD, B ≤ V.B ∧ V.γ < Td.tdK S := by
  intro B hB
  obtain ⟨ℓ, hℓ, hg, hBl⟩ := skCofLev S B hB
  obtain ⟨V, hVB, hVg⟩ := skSysAll ℓ hℓ
  exact ⟨V, hVB ▸ hBl, hVg.trans_lt hg⟩

/-- STATUS: REDUCED (skSysA1, skSysA2, skSysA3)
SIZE: L
∀ B < Γ(1) ∃ system V: B ≤ B_V, γ_V < K. -/
theorem skSysCof (S : InaccSeq.{0}) : ∀ B, B < Gc.gcG 1 → ∃ V : Hg.HgVD, B ≤ V.B ∧ V.γ < Td.tdK S := by
  intro B hB
  rcases lt_or_ge B (veblen Gf.gfE (Gc.gcG 0 + 1)) with h1 | h1
  · exact skSysA1 S B h1
  rcases lt_or_ge B (veblen (Gc.gcG 0) (Gc.gcG 0 + 1)) with h2 | h2
  · exact skSysA2 S B h1 h2
  · exact skSysA3 S B h2 hB

/-- STATUS: REDUCED (skSysCof, skLocOfSys)
SIZE: L
(A) ∀ range λ with λ < ι(Γ(B)·ω) for some B < Γ(1): UPPER ∧ LOWER ∧ CapV. -/
theorem skRegA (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l →
    (∃ B, B < Gc.gcG 1 ∧ l < Bt.iota S (Gc.gcG B * ω)) → SkUV S l := by
  rintro l hr ⟨B, hB, hl⟩
  obtain ⟨V, hBV, hγ⟩ := skSysCof S B hB
  refine skLocOfSys S V hγ l hr (hl.trans_le ?_)
  exact Bt.iota_mono (S := S) _ _ (mul_le_mul_left (Gc.gcG_le hBV) ω)

/-- STATUS: REDUCED (skLongPre, skLongMid, skLongTop)
SIZE: L
(C) ∀ range λ with e(η_λ) ≥ Ω₂: UPPER ∧ LOWER ∧ CapV. -/
theorem skRegC (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → Om (1 + 1) ≤ Cd.cdExp (Cd.cdEta S l) → SkUV S l := by
  intro l hr he
  rcases lt_or_ge (upsilon l) (Nc.ncL S 0) with h0 | h0
  · exact skLongPre S l hr he h0
  rcases le_or_gt (upsilon l) (Nc.ncL S ω) with hw | hw
  · exact skLongMid S l hr he h0 hw
  · exact skLongTop S l hr he hw

/-- STATUS: REDUCED (skRegA, skRegB, skRegC)
SIZE: L
∀ range λ ≥ F_Ho: UPPER ∧ LOWER ∧ CapV (ENUM-REACH and CapV at every range restart above the frontier). -/
theorem skAbove (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → skFHo S ≤ l → SkUV S l := by
  intro l hr _
  by_cases hA : ∃ B, B < Gc.gcG 1 ∧ l < Bt.iota S (Gc.gcG B * ω)
  · exact skRegA S l hr hA
  push Not at hA
  rcases lt_or_ge (Cd.cdExp (Cd.cdEta S l)) (Om (1 + 1)) with he | he
  · exact skRegB S l hr hA he
  · exact skRegC S l hr he

/-- STATUS: REDUCED (skHypIff, skAbove)
SIZE: L
hUH ∧ hLH ∧ hVH ∧ hVt of Wd.wdRoadL (from ι(Γ(φ(Ω₁², G+1))·ω) on). -/
theorem skFront (S : InaccSeq.{0}) :
    (∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdUpper S l) ∧
    (∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdLower S l) ∧
    (∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdCapV S l) ∧
    (∀ l, Cd.CdRange S l → Nc.ncL S ω < upsilon l →
      Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdCapV S l) :=
  skHypIff S (skAbove S)

/-- STATUS: REDUCED (skFront)
SIZE: L
hUH of Wd.wdRoadL. -/
theorem skFrontU (S : InaccSeq.{0}) :
    ∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdUpper S l := (skFront S).1

/-- STATUS: REDUCED (skFront)
SIZE: L
hLH of Wd.wdRoadL. -/
theorem skFrontL (S : InaccSeq.{0}) :
    ∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdLower S l := (skFront S).2.1

/-- STATUS: REDUCED (skFront)
SIZE: L
hVH of Wd.wdRoadL. -/
theorem skFrontV (S : InaccSeq.{0}) :
    ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdCapV S l :=
  (skFront S).2.2.1

/-- STATUS: REDUCED (skFront)
SIZE: L
hVt of Wd.wdRoadL. -/
theorem skFrontVt (S : InaccSeq.{0}) :
    ∀ l, Cd.CdRange S l → Nc.ncL S ω < upsilon l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdCapV S l :=
  (skFront S).2.2.2

/-- STATUS: REDUCED (skFrontU, skFrontL, skFrontV, skFrontVt, Wd.wdRoadL)
SIZE: L
integration check: Wd.wdRoadL applied to the four top nodes; ν_C = L(ω+1) etc. from hT, hF, h0, hn only. -/
theorem skRoad (S : InaccSeq.{0})
    (hT : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S)
    (hF : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdEQfar S)
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      Vr.VrVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      Vr.VrVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cd.CdCL S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S (k + 1)) (Nc.ncL S (ω + 1)) :=
  Wd.wdRoadL (skFrontU S) (skFrontL S) (skFrontV S) (skFrontVt S) hT hF h0 hn

end R2Skel.SkF

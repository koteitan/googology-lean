import Googology.Trans.PoR.InaccPsi.R2.HoRoad
import Googology.Trans.PoR.InaccPsi.R2.WdRoad

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
def ShPow (ℓ : Ordinal.{0}) : Prop := ∃ P e, 1 ≤ e ∧ Om1 ^ (e + 1) ∣ P ∧ ℓ = P + Om1 ^ (e + 1)

/-- Shape: `ℓ = P + Ω₁^e`, `e` a limit (transfinite exponent). -/
def ShExpLim (ℓ : Ordinal.{0}) : Prop := ∃ P e, IsSuccLimit e ∧ Om1 ^ e ∣ P ∧ ℓ = P + Om1 ^ e

/-- Shape: `ℓ = P + Ω₁^e·c`, `c < Ω₁` a limit (an `ω`-chain union). -/
def ShCoefLim (ℓ : Ordinal.{0}) : Prop :=
  ∃ P e c, 1 ≤ e ∧ IsSuccLimit c ∧ c < Om1 ∧ Om1 ^ (e + 1) ∣ P ∧ ℓ = P + Om1 ^ e * c

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

/-! ## OPEN leaves -/

/-- STATUS: OPEN
SIZE: S
∀ ℓ: Ω₁ ≤ ℓ, Ω₁ ∣ ℓ, ℓ < ε_{Ω₁+1} ⇒ ℓ = Ω₁ ∨ succ ∨ pow ∨ exp-limit ∨ coefficient-limit (Cantor normal form). -/
theorem skShape : ∀ ℓ, SkLev ℓ → ℓ = Om1 ∨ ShSucc ℓ ∨ ShPow ℓ ∨ ShExpLim ℓ ∨ ShCoefLim ℓ := by
  sorry

/-- STATUS: OPEN
SIZE: M
SC Z ≤ Ω₁, y code over Z (atom G), y < ε_{Ω₁+1} ⇒ gtc y < Z (transfinite digit gate; Hn.hn_cl_digit is k < ω). -/
theorem skDigitGate : SkDigitGate := by
  sorry

/-- STATUS: OPEN
SIZE: S
digit gate ∧ EXACT ⇒ ∀ ℓ ∃ HnLv: L = ℓ, l x = rdc ℓ x above g ≤ gtc ℓ (fields L_mem, g_cl, l_lt, l_pi). -/
theorem skLvOfGate : SkDigitGate → SkReadExact → SkLvDatumAll := by
  sorry

/-- STATUS: OPEN
SIZE: S
the entry at ℓ = Ω₁: package Hn.hnPk1 (read x) and the G-system at φ(Ω₁, G+1) (repo has both, other format). -/
theorem skStepBase : SkStepAt Om1 := by
  sorry

/-- STATUS: OPEN
SIZE: M
ℓ = ℓ' + Ω₁: package Hn.HnPk.succ, G-system φ(ℓ'+Ω₁, G+1) from the step at the pseudo-base φ(ℓ', G+1). -/
theorem skStepSucc (hLv : SkLvDatumAll) : ∀ ℓ, SkLev ℓ → ShSucc ℓ → SkStepAt ℓ := by
  sorry

/-- STATUS: OPEN
SIZE: M
ℓ = P + Ω₁^{e+1}: package = union over the band packages P + Ω₁^e·v (v < Ω₁) at every pseudo-base;
G-system = union (Ho.HoStep / Ho.HoPU are the case P = 0, e = 2). -/
theorem skStepPow (hLv : SkLvDatumAll) : ∀ ℓ, SkLev ℓ → ShPow ℓ → SkStepAt ℓ := by
  sorry

/-- STATUS: OPEN
SIZE: M
ℓ = P + Ω₁^e, e limit: union over P + Ω₁^{e'}, e' < e (ω-chain if cf e = ω, Ω₁-union if cf e = Ω₁);
exponents read rdc e x (digit gate at transfinite exponents). -/
theorem skStepExpLim (hLv : SkLvDatumAll) (hG : SkDigitGate) : ∀ ℓ, SkLev ℓ → ShExpLim ℓ → SkStepAt ℓ := by
  sorry

/-- STATUS: OPEN
SIZE: M
ℓ = P + Ω₁^e·c, c < Ω₁ limit: ω-chain union of the packages at P + Ω₁^e·c_k (Ho.hoPkL one level up). -/
theorem skStepCoefLim (hLv : SkLvDatumAll) : ∀ ℓ, SkLev ℓ → ShCoefLim ℓ → SkStepAt ℓ := by
  sorry

/-- STATUS: OPEN
SIZE: S
∀ B < φ(ε_{Ω₁+1}, G+1) ∃ ℓ (SkLev ℓ, gtc ℓ < K, B ≤ φ(ℓ, G+1))  [φ(E, G+1) = sup_{ℓ<E} φ(ℓ, G+1), ℓ = Ω₁^m]. -/
theorem skCofLev (S : InaccSeq.{0}) : ∀ B, B < veblen Gf.gfE (Gc.gcG 0 + 1) →
    ∃ ℓ, SkLev ℓ ∧ Gf.gtc ℓ < Td.tdK S ∧ B ≤ veblen ℓ (Gc.gcG 0 + 1) := by
  sorry

/-- STATUS: OPEN
SIZE: L
(A2) Veblen-form levels ε_{Ω₁+1} ≤ ℓ < G: ∀ B ∈ [φ(ε_{Ω₁+1}, G+1), φ(G, G+1)) ∃ system V, B ≤ B_V, γ_V < K
(needs a level datum read on Veblen normal forms; Gf.rdc stops at ε_{Ω₁+1}). -/
theorem skSysA2 (S : InaccSeq.{0}) : ∀ B, veblen Gf.gfE (Gc.gcG 0 + 1) ≤ B →
    B < veblen (Gc.gcG 0) (Gc.gcG 0 + 1) → ∃ V : Hg.HgVD, B ≤ V.B ∧ V.γ < Td.tdK S := by
  sorry

/-- STATUS: OPEN
SIZE: L
(A3) levels G ≤ ℓ < Γ(1): ∀ B ∈ [φ(G, G+1), Γ(1)) ∃ system V, B ≤ B_V, γ_V < K
(Hn.HnLv asks L < G: a level datum containing the atom G is needed). -/
theorem skSysA3 (S : InaccSeq.{0}) : ∀ B, veblen (Gc.gcG 0) (Gc.gcG 0 + 1) ≤ B →
    B < Gc.gcG 1 → ∃ V : Hg.HgVD, B ≤ V.B ∧ V.γ < Td.tdK S := by
  sorry

/-- STATUS: SUSPECT (mis-scoped: its region is not below ι(Ω₂); it holds range restarts in (L(0), L(1)), R2Skel.SkFX.skfxRegB_long, so it carries the long region and the ν_C caveat, R2Skel.SkFX.skfxRegB_nu)
SIZE: L
(B) the atom Γ(c), c ≥ 1, inside codes: range λ past every ι(Γ(B)·ω), B < Γ(1), with e(η_λ) < Ω₂
(every repo system is an Hg.HgVD with B < Γ(1); up to ι(Ω₂), Ga.gaEnd_front). -/
theorem skRegB (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l →
    (∀ B, B < Gc.gcG 1 → Bt.iota S (Gc.gcG B * ω) ≤ l) → Cd.cdExp (Cd.cdEta S l) < Om (1 + 1) → SkUV S l := by
  sorry

/-- STATUS: OPEN
SIZE: L
(C1) names e(η_λ) ≥ Ω₂ with υ_λ < L(0) = m*: code m_λ = π_η (Gc.gc_past_Om2); no Lean frontier lemma there. -/
theorem skLongPre (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → Om (1 + 1) ≤ Cd.cdExp (Cd.cdEta S l) →
    upsilon l < Nc.ncL S 0 → SkUV S l := by
  sorry

/-- STATUS: OPEN
SIZE: L
(C2) range λ with L(0) ≤ υ_λ ≤ L(ω) (between the L(k); Se.seCode_mid: codes < P′). -/
theorem skLongMid (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → Om (1 + 1) ≤ Cd.cdExp (Cd.cdEta S l) →
    Nc.ncL S 0 ≤ upsilon l → upsilon l ≤ Nc.ncL S ω → SkUV S l := by
  sorry

/-- STATUS: OPEN
SIZE: L
(C3) range λ with L(ω) < υ_λ < L(ω+1) (Sh.shRange_top); fails at υ_λ = ν_C if ν_C < L(ω+1) (Sh.shNotLower). -/
theorem skLongTop (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → Om (1 + 1) ≤ Cd.cdExp (Cd.cdEta S l) →
    Nc.ncL S ω < upsilon l → SkUV S l := by
  sorry

/-! ## REDUCED nodes -/

/-- STATUS: REDUCED (skLvOfGate, skDigitGate, skReadExact)
SIZE: M
∀ ℓ (Ω₁ ≤ ℓ, Ω₁ ∣ ℓ, ℓ < ε_{Ω₁+1}) ∃ level datum Λ: L = ℓ, l(x) = rdc ℓ x above g ≤ gtc ℓ. -/
theorem skLvDatum : SkLvDatumAll := skLvOfGate skDigitGate skReadExact

/-- STATUS: REDUCED (skShape, skStepBase, skStepSucc, skStepPow, skStepExpLim, skStepCoefLim, skLvDatum,
skDigitGate)
SIZE: M
∀ ℓ: the step at ℓ (every coherent family below ℓ extends to ℓ). -/
theorem skStep : ∀ ℓ, SkLev ℓ → SkStepAt ℓ := by
  intro ℓ hℓ
  rcases skShape ℓ hℓ with h | h | h | h | h
  · subst h; exact skStepBase
  · exact skStepSucc skLvDatum ℓ hℓ h
  · exact skStepPow skLvDatum ℓ hℓ h
  · exact skStepExpLim skLvDatum skDigitGate ℓ hℓ h
  · exact skStepCoefLim skLvDatum ℓ hℓ h

/-- The recursion step used by `skFam`. -/
noncomputable def skG (ℓ : Ordinal.{0}) (f : ∀ ℓ' : Ordinal.{0}, ℓ' < ℓ → SkEnt) : SkEnt := by
  classical
  exact if h : SkLev ℓ ∧ SkCoh ℓ f then Classical.choose (skStep ℓ h.1 f h.2) else (Hn.hnPk1, ULift.up Ho.hoUf)

/-- The family built by well-founded recursion. -/
noncomputable def skF : Ordinal.{0} → SkEnt := Ordinal.lt_wf.fix skG

/-- STATUS: REDUCED (skStep)
SIZE: M
∃ F: ∀ ℓ (SkLev): F ℓ at ℓ ∧ ∀ ℓ' < ℓ (SkLev): F ℓ extends F ℓ'  (one generic induction over ℓ). -/
theorem skFam : ∃ F : Ordinal.{0} → SkEnt,
    ∀ ℓ, SkLev ℓ → SkAt ℓ (F ℓ) ∧ ∀ ℓ', ℓ' < ℓ → SkLev ℓ' → SkExt (F ℓ') (F ℓ) := by
  refine ⟨skF, fun ℓ => ?_⟩
  induction ℓ using WellFoundedLT.induction with
  | _ ℓ ih =>
    intro hℓ
    have hcoh : SkCoh ℓ (fun ℓ' _ => skF ℓ') :=
      ⟨fun ℓ' h h' => (ih ℓ' h h').1, fun ℓ'' ℓ' _ h' hlt h1 h2 => (ih ℓ' h' h2).2 ℓ'' hlt h1⟩
    have heq : skF ℓ = skG ℓ (fun ℓ' _ => skF ℓ') := Ordinal.lt_wf.fix_eq skG ℓ
    have hsp := Classical.choose_spec (skStep ℓ hℓ (fun ℓ' _ => skF ℓ') hcoh)
    have hG : skG ℓ (fun ℓ' _ => skF ℓ') = Classical.choose (skStep ℓ hℓ (fun ℓ' _ => skF ℓ') hcoh) := by
      unfold skG; rw [dif_pos ⟨hℓ, hcoh⟩]
    rw [heq, hG]
    exact ⟨hsp.1, fun ℓ' h h' => hsp.2 ℓ' h h'⟩

/-- STATUS: REDUCED (skFam)
SIZE: M
∀ ℓ (SkLev) ∃ system V over G: B_V = φ(ℓ, G+1), γ_V ≤ gtc ℓ. -/
theorem skSysAll : ∀ ℓ, SkLev ℓ → ∃ V : Hg.HgVD, V.B = veblen ℓ (Gc.gcG 0 + 1) ∧ V.γ ≤ Gf.gtc ℓ := by
  intro ℓ hℓ
  obtain ⟨F, hF⟩ := skFam
  exact ⟨(F ℓ).2.down, (hF ℓ hℓ).1.2.2.1, (hF ℓ hℓ).1.2.2.2⟩

/-- STATUS: REDUCED (skSysAll, skCofLev)
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

import Googology.Trans.PoR.InaccPsi.R2.VrRoad

/-!
# The restricted carry: the lo-leaves of `Vr.VrCarry` only where `π_{υ_μ,υ_λ}` is fixed by the axioms

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

Every axiom that fixes a value of `π_{σ,τ}(x)` asks `x ∈ Tᵗ[σ]`; a point of `[σ, τ)` is not there (`TB_inter_lt`).
The image clause of `Vr.VrCarry` quantifies over every decomposition, so it asks bounds on `π_{υ_μ,υ_λ}(p)` at
points `p ∈ [υ_μ, υ_λ)`.  The realizer (`Vr.vrReal_gen`) only meets decompositions whose low points are below the
base `γ < υ_μ` of `Vl.vlShiftCore`, and whose points of `[υ_λ, υ_{λ+1})` (and segment points) have their low
parameters there too.  So the carry is restricted to decompositions `E` with `WfR λ μ E`:

* `lo c`: `c ∈ T^{υ_λ}[υ_μ]` (for `c < υ_λ` this is `c < υ_μ`);
* `sg h y`: the parameters of `y` over `υ_{λ+h}` are below `υ_μ`;
* `ub h t`, `tm h t Lf δ`: every leaf `p < υ_{λ+1}` lies in `T^{υ_λ}[υ_μ]`; `δ ≤ υ_μ`.

* `wfLo`, `WfR`, `wfLowPar`, `wfPrm` (the low parameters a realizer must contain), `WfCarry`, `WfSup`, `WfGen`,
  `WfVisGen` (the restricted forms of `Vr.VrCarry`, `Vr.VrSup`, `Vr.VrGen`, `Vr.VrVisGen`);
* `wfCarry_of_vr`, `wfSup_of_vr`, `wfGen_of_vr`, `wfVisGen_of_vr` (**the old statements imply the restricted ones**);
* `wfLo_of` (**a leaf of `[υ_λ, υ_{λ+1})` with low parameters below `υ_μ` is in `T^{υ_λ}[υ_μ]`**), `wfPrm_lt`,
  `wfR_of` (**`WfR` from the points and low parameters below `υ_μ`**).

New definitions: `wfLo`, `WfR`, `wfLowPar`, `wfPrm`, `WfCarry`, `WfSup`, `WfGen`, `WfVisGen` (statements).
No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Tk

variable {S : InaccSeq.{0}}

/-- A leaf `p`: if `p < υ_{λ+1}` then `p ∈ T^{υ_λ}[υ_μ]`. -/
def wfLo (l μ p : Ordinal.{0}) : Prop := p < upsilon (succ l) → p ∈ TB (upsilon l) (upsilon μ)

/-- **The restriction of a decomposition**: every place where `Vr.vrImg` applies `π_{υ_μ,υ_λ}` or a segment move
lies where the axioms fix it. -/
def WfR (l μ : Ordinal.{0}) : Vr.VrE → Prop
  | .lo c => c ∈ TB (upsilon l) (upsilon μ)
  | .sg h y => ∀ p ∈ Par (upsilon (l + h)) y, p < upsilon μ
  | .ub _ t => ∀ p ∈ Ub.UbT.lvs t, wfLo l μ p
  | .tm _ t Lf δ => δ ≤ upsilon μ ∧ ∀ p ∈ Un.UnT.lvs t ∪ Lf, wfLo l μ p
  | .add s t => WfR l μ s ∧ WfR l μ t

/-- The low parameters of a point over `υ_λ`. -/
noncomputable def wfLowPar (l p : Ordinal.{0}) : Finset Ordinal.{0} :=
  (Par (upsilon l) p).filter (· < upsilon l)

/-- **The low parameters a realizer configuration must contain** for a decomposition. -/
noncomputable def wfPrm (l : Ordinal.{0}) : Vr.VrE → Finset Ordinal.{0}
  | .lo c => wfLowPar l c
  | .sg h y => (Par (upsilon (l + h)) y).filter (· < upsilon l)
  | .ub _ t => (Ub.UbT.lvs t).biUnion (wfLowPar l)
  | .tm _ t Lf _ => (Un.UnT.lvs t ∪ Lf).biUnion (wfLowPar l)
  | .add s t => wfPrm l s ∪ wfPrm l t

/-- **The restricted carry** (`Vr.VrCarry` with the image clause only for decompositions with `WfR λ μ`). -/
def WfCarry (S : InaccSeq.{0}) (l β μ : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) (B : Ordinal.{0})
    (Os : Finset Ordinal.{0}) : Prop :=
  ∀ g ∈ Os, 0 < g → ω ^ 2 ∣ g → CdLower S (μ + f g) ∧
    (upsilon (l + β) ≤ cdR S (l + g) → upsilon (μ + B) ≤ cdR S (μ + f g)) ∧
    ∀ E : Vr.VrE, Vr.VrWF l β E → Vr.vrVal l E = cdR S (l + g) → Vr.VrOs l Os E → WfR l μ E →
      Vr.vrImg l μ f E ≤ cdR S (μ + f g)

/-- **The restricted supply clause** (`Vr.VrSup` with `WfCarry`). -/
def WfSup (S : InaccSeq.{0}) (l β : Ordinal.{0}) : Prop :=
  ∀ γ < upsilon l, ∀ Os : Finset Ordinal.{0}, (∀ d ∈ Os, d < β) →
    ∃ μ f B, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < upsilon l ∧ μ + B ≤ l ∧ ω ^ 2 ∣ B ∧
      upsilon (μ + B) ≤ cdR S μ ∧ Sl.SlOff f Os B ∧ WfCarry S l β μ f B Os

/-- **`Vr.VrGen` with the restricted supply.** -/
def WfGen (S : InaccSeq.{0}) (l β : Ordinal.{0}) : Prop :=
  (∀ g, 0 < g → g < β → ω ^ 2 ∣ g → CdUpper S (l + g)) ∧
  (∀ g, 0 < g → g < β → ω ^ 2 ∣ g → upsilon (l + β) ≤ cdR S (l + g) ∨ Vr.VrForm S l β g) ∧ WfSup S l β

/-- **`Vr.VrVisGen` with the restricted supply.** -/
def WfVisGen (S : InaccSeq.{0}) (l b c : Ordinal.{0}) : Prop :=
  ∀ ν, CdRange S ν → c ≤ upsilon ν → upsilon ν < b → upsilon l < upsilon ν → ¬ TkCov S (upsilon l) ν →
    TkIso S (upsilon l) ν → ∃ β, upsilon ν < upsilon (l + β) ∧ upsilon (l + β) ≤ b ∧ WfGen S l β

/-! ## The old statements imply the restricted ones -/

theorem wfCarry_of_vr {l β μ B : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}}
    (h : Vr.VrCarry S l β μ f B Os) : WfCarry S l β μ f B Os := fun g hg h0 hd =>
  ⟨(h g hg h0 hd).1, (h g hg h0 hd).2.1, fun E hE hv ho _ => (h g hg h0 hd).2.2 E hE hv ho⟩

theorem wfSup_of_vr {l β : Ordinal.{0}} (h : Vr.VrSup S l β) : WfSup S l β := by
  intro γ hγ Os hOs
  obtain ⟨μ, f, B, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h γ hγ Os hOs
  exact ⟨μ, f, B, h1, h2, h3, h4, h5, h6, h7, wfCarry_of_vr h8⟩

theorem wfGen_of_vr {l β : Ordinal.{0}} (h : Vr.VrGen S l β) : WfGen S l β :=
  ⟨h.1, h.2.1, wfSup_of_vr h.2.2⟩

/-- **`Vr.VrVisGen ⇒ WfVisGen`**: the restricted statement is no stronger. -/
theorem wfVisGen_of_vr {l b c : Ordinal.{0}} (h : Vr.VrVisGen S l b c) : WfVisGen S l b c := by
  intro ν h1 h2 h3 h4 h5 h6
  obtain ⟨β, e1, e2, e3⟩ := h ν h1 h2 h3 h4 h5 h6
  exact ⟨β, e1, e2, wfGen_of_vr e3⟩

/-! ## The restriction holds for the decompositions a realizer meets -/

/-- **A leaf with its low point and its low parameters below `υ_μ`** satisfies `wfLo`: a point of
`[υ_λ, υ_{λ+1})` is in `T^{υ_λ}` (`exists_next`) with parameters below `υ_λ` (`Par_sub`). -/
theorem wfLo_of {l μ p : Ordinal.{0}} (hl0 : 0 < l) (hB : Bases (upsilon μ) (upsilon l))
    (hlow : p < upsilon l → p < upsilon μ) (hpar : ∀ q ∈ wfLowPar l p, q < upsilon μ) : wfLo l μ p := by
  intro hps
  by_cases hpl : p < upsilon l
  · exact (TB_inter_lt hB hpl).2 (hlow hpl)
  · have hτ : UpsPt (upsilon l) := upsPt_upsilon hl0
    have h1 : upsilon l < Om1 := hB.2.2.2
    obtain ⟨m, hm, hT⟩ := exists_next hτ h1
    have hmu : m = upsilon (succ l) := hm.unique (upsilon_isNext l)
    have hu1 : upsilon (succ l) < Om1 := next_lt_Om1 (upsilon_isNext l) (Or.inr hτ) h1
    have hcT : p ∈ Tset (upsilon l) := (hT p (hps.trans hu1)).2 (hmu ▸ hps)
    have hP := Par_sub (upsPt_inE hτ) h1 hcT
    refine ⟨hcT, fun q hq => ?_⟩
    exact hpar q (Finset.mem_filter.2 ⟨Finset.mem_coe.1 hq, hP hq⟩)

/-- Every low parameter collected by `wfPrm` is below `υ_λ`. -/
theorem wfPrm_lt (l : Ordinal.{0}) : ∀ E : Vr.VrE, ∀ q ∈ wfPrm l E, q < upsilon l := by
  intro E
  induction E with
  | lo c => intro q hq; exact (Finset.mem_filter.1 hq).2
  | sg h y => intro q hq; exact (Finset.mem_filter.1 hq).2
  | ub h t =>
    intro q hq
    obtain ⟨p, -, hqp⟩ := Finset.mem_biUnion.1 hq
    exact (Finset.mem_filter.1 hqp).2
  | tm h t Lf δ =>
    intro q hq
    obtain ⟨p, -, hqp⟩ := Finset.mem_biUnion.1 hq
    exact (Finset.mem_filter.1 hqp).2
  | add s t ihs iht =>
    intro q hq
    rcases Finset.mem_union.1 hq with hq | hq
    · exact ihs q hq
    · exact iht q hq

/-- **`WfR` from the points and low parameters below `υ_μ`**. -/
theorem wfR_of {l β μ : Ordinal.{0}} (hl0 : 0 < l) (hB : Bases (upsilon μ) (upsilon l)) :
    ∀ E : Vr.VrE, Vr.VrWF l β E → (∀ z ∈ Vr.vrPts l E, z < upsilon l → z < upsilon μ) →
      (∀ q ∈ wfPrm l E, q < upsilon μ) → WfR l μ E := by
  intro E
  induction E with
  | lo c =>
    intro hw hz hq
    exact wfLo_of hl0 hB (hz c (Finset.mem_singleton_self _)) hq hw
  | sg h y =>
    intro hw _ hq
    obtain ⟨-, -, -, -, h3⟩ := hw
    exact fun p hp => hq p (Finset.mem_filter.2 ⟨hp, h3 p hp⟩)
  | ub h t =>
    intro _ hz hq p hp
    exact wfLo_of hl0 hB (hz p (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hp)))
      (fun q hqp => hq q (Finset.mem_biUnion.2 ⟨p, hp, hqp⟩))
  | tm h t Lf δ =>
    intro hw hz hq
    obtain ⟨-, -, hδ, -⟩ := hw
    refine ⟨(hz δ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))) hδ).le,
      fun p hp => ?_⟩
    exact wfLo_of hl0 hB (hz p (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem hp))))
      (fun q hqp => hq q (Finset.mem_biUnion.2 ⟨p, hp, hqp⟩))
  | add s t ihs iht =>
    intro hw hz hq
    exact ⟨ihs hw.1 (fun z h => hz z (Finset.mem_insert_of_mem (Finset.mem_union_left _ h)))
        (fun q h => hq q (Finset.mem_union_left _ h)),
      iht hw.2 (fun z h => hz z (Finset.mem_insert_of_mem (Finset.mem_union_right _ h)))
        (fun q h => hq q (Finset.mem_union_right _ h))⟩

end Googology.Trans.PoR.InaccPsi.R2.Wf

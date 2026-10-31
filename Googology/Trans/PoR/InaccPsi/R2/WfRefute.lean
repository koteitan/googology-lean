import Googology.Trans.PoR.InaccPsi.R2.WfCarry
import Googology.Trans.PoR.InaccPsi.R2.SkSXPi

/-!
# Refute-first and non-vacuity of the restricted carry

`π = π_{υ_μ,υ_λ}`.  Tests of the restricted forms `WfR`, `WfCarry`, `WfSup` against the refuter `SkSX`:

* `wfR_lo_iff` (**a lo-leaf `p < υ_λ` is allowed iff `p < υ_μ`**), `wfR_skSX_excl` (**the decomposition
  `lo p + D` of `R2Skel.SkSX.skSX_img_pi` with `p ∈ [υ_μ, υ_λ)` is excluded**), `wfImg_lo` (an allowed lo-leaf
  below `υ_λ` has image `p`: `pi_lt`), `wfImg_lo_mem` (an allowed lo-leaf `c < Ω₁` has image in `T^{υ_μ}` below
  `υ_{μ+1}`: fixed by `pi_bijOn`), `wfSup_lo` (**the restricted form of `skSX_sup_pi`**: the bound it asks is
  `p + img D ≤ r(μ+f g)` only for `p < υ_μ`, where `π(p) = p`);
* `wfR_Ew` (**the witness decomposition `Vr.vrEw g` is allowed**: the restriction keeps EQ at the witness),
  `wfR_low` (the low decompositions `ub(z+ω+1) + lo c` with `c ∈ T^{υ_λ}[υ_μ]` are allowed);
* `wfGen_wit_iff` (**at the witness window `WfGen ⇔ WfSup`**, as `Vr.vrGen_wit_iff`), `wfVis_wit`.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **A lo-leaf below `υ_λ` is allowed iff it is below `υ_μ`.** -/
theorem wfR_lo_iff {l μ p : Ordinal.{0}} (hB : Bases (upsilon μ) (upsilon l)) (hp : p < upsilon l) :
    WfR l μ (.lo p) ↔ p < upsilon μ :=
  TB_inter_lt hB hp

/-- **The refuter's decomposition is excluded**: `lo p + D` with `υ_μ ≤ p < υ_λ` is not allowed. -/
theorem wfR_skSX_excl {l μ p : Ordinal.{0}} (hB : Bases (upsilon μ) (upsilon l)) (hμp : upsilon μ ≤ p)
    (hp : p < upsilon l) (D : Vr.VrE) : ¬ WfR l μ (.add (.lo p) D) := fun h =>
  R2Skel.SkSX.skSX_notTB hB hμp hp h.1

/-- An allowed lo-leaf below `υ_λ` has image `p`. -/
theorem wfImg_lo {l μ p : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (hB : Bases (upsilon μ) (upsilon l))
    (hp : p < upsilon l) (h : WfR l μ (.lo p)) : Vr.vrImg l μ f (.lo p) = p :=
  pi_lt hB ((wfR_lo_iff hB hp).1 h)

/-- An allowed lo-leaf `c < Ω₁` has its image in `T^{υ_μ}`, below `υ_{μ+1}` (the axioms fix it). -/
theorem wfImg_lo_mem {l μ c : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (hB : Bases (upsilon μ) (upsilon l))
    (hc1 : c < Om1) (h : WfR l μ (.lo c)) :
    Vr.vrImg l μ f (.lo c) ∈ Tset (upsilon μ) ∧ Vr.vrImg l μ f (.lo c) < upsilon (succ μ) := by
  refine ⟨(pi_bijOn hB).1.mapsTo h, ?_⟩
  obtain ⟨m', -, -, hmin, hmT⟩ := T_inter_Om1 hB.1 (hB.2.2.1.trans hB.2.2.2)
  have hy1 := down_lt_Om1 hB h hc1
  have hn := upsilon_isNext μ
  exact ((hmT _ hy1).1 ((pi_bijOn hB).1.mapsTo h)).trans_le (hmin _ hn.1 hn.2.1.2)

/-- **The restricted form of `skSX_img_pi` / `skSX_sup_pi`**: under the restricted image clause, the decomposition
`lo p + D` (value `r(λ+g)`) asks `p + img D ≤ r(μ+f g)` only for `p < υ_μ`, where `π(p) = p`. -/
theorem wfSup_lo {l β μ g p : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}}
    (hB : Bases (upsilon μ) (upsilon l)) (hg0 : 0 < g)
    (hI : ∀ E : Vr.VrE, Vr.VrWF l β E → Vr.vrVal l E = cdR S (l + g) → Vr.VrOs l Os E → WfR l μ E →
      Vr.vrImg l μ f E ≤ cdR S (μ + f g))
    (D : Vr.VrE) (hD : Vr.VrWF l β D) (hDv : Vr.vrVal l D = cdR S (l + g)) (hDo : Vr.VrOs l Os D)
    (hDR : WfR l μ D) (hp : p < upsilon μ) :
    p + Vr.vrImg l μ f D ≤ cdR S (μ + f g) := by
  have hm := upsilon_normal.strictMono
  have hpl : p < upsilon l := hp.trans hB.2.2.1
  have hlE := hB.2.1
  have hlt : upsilon l ≤ cdR S (l + g) :=
    (hm (lt_add_of_pos_right l hg0)).le.trans (cdRho_lt_R S (l + g)).le
  have habs : p + cdR S (l + g) = cdR S (l + g) := by
    have hp' : p < ω ^ upsilon l := by unfold InE at hlE; rw [hlE]; exact hpl
    exact Ordinal.add_of_omega0_opow_le hp' (by unfold InE at hlE; rw [hlE]; exact hlt)
  have hWF : Vr.VrWF l β (.add (.lo p) D) := ⟨hpl.trans (hm (lt_succ l)), hD⟩
  have hv : Vr.vrVal l (.add (.lo p) D) = cdR S (l + g) := by
    show p + Vr.vrVal l D = _
    rw [hDv, habs]
  have h := hI _ hWF hv ⟨trivial, hDo⟩ ⟨(wfR_lo_iff hB hpl).2 hp, hDR⟩
  have e : Vr.vrImg l μ f (.add (.lo p) D) = p + Vr.vrImg l μ f D := by
    show pi (upsilon μ) (upsilon l) p + _ = _
    rw [pi_lt hB hp]
  rwa [e] at h

/-- **The witness decomposition is allowed** (its only leaf is `0 < υ_μ`). -/
theorem wfR_Ew {l μ : Ordinal.{0}} (hB : Bases (upsilon μ) (upsilon l)) (g : Ordinal.{0}) :
    WfR l μ (Vr.vrEw g) := by
  have h0 : (0 : Ordinal.{0}) ∈ TB (upsilon l) (upsilon μ) :=
    (TB_inter_lt hB (lt_of_le_of_lt zero_le hB.2.2.1)).2 (InE.pos hB.1)
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · simp [Ub.UbT.lvs] at hp
  · simp [Ub.UbT.lvs] at hp
    subst hp
    exact fun _ => h0

/-- **The low decompositions are allowed** when their lo-leaf is in `T^{υ_λ}[υ_μ]`. -/
theorem wfR_low {l μ h c : Ordinal.{0}} (hc : c ∈ TB (upsilon l) (upsilon μ)) :
    WfR l μ (.add (.ub h .base) (.lo c)) := by
  refine ⟨fun p hp => ?_, hc⟩
  simp [Ub.UbT.lvs] at hp

/-- **Non-vacuity at the witness window**: `WfGen S a β₀ ⇔ WfSup S a β₀` (`Vr.vrForms_win`). -/
theorem wfGen_wit_iff (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l) (k : ℕ)
    (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) :
    WfGen S (Nc.ncL S (k : Ordinal.{0})) (ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1) + ω ^ 2 * 2) ↔
      WfSup S (Nc.ncL S (k : Ordinal.{0})) (ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1) + ω ^ 2 * 2) := by
  refine ⟨fun h => h.2.2, fun h => ?_⟩
  -- the first two clauses are those of `Vr.VrGen`, a theorem there by `Vr.vrGen_wit_iff`
  have hsup : WfSup S _ _ := h
  obtain ⟨-, -, hF⟩ := Vr.vrForms_win (S := S) k hν
  refine ⟨fun g hg0 hgβ hgd => ?_, fun g hg0 hgβ hgd => Or.inr (hF g hg0 hgβ hgd), hsup⟩
  have hm := upsilon_normal.strictMono
  set l := Nc.ncL S (k : Ordinal.{0})
  have hl := Te.teRst_L (S := S) k
  have hla : upsilon l = l := Te.teUps_L k
  have hν' : IsRestartIdx (l + g) :=
    ⟨(lt_of_lt_of_le (pos_iff_ne_zero.2 hl.1) le_self_add).ne', dvd_add hl.2 hgd⟩
  have h1 : l < upsilon (l + g) := by have := hm (lt_add_of_pos_right l hg0); rwa [hla] at this
  obtain ⟨-, hβL, -⟩ := Vr.vrForms_win (S := S) k hν
  have h2 : upsilon (l + g) < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) :=
    (hm (add_lt_add_right hgβ l)).trans hβL
  obtain ⟨hr, hz⟩ := Ty.tyInner_rng hν' h1 h2
  exact hU _ hr hz

/-- **The witness of `Vo.voNoGo` is answered with the restricted supply.** -/
theorem wfVis_wit (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l) (k : ℕ)
    (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC)
    (hsup : WfSup S (Nc.ncL S (k : Ordinal.{0})) (ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1) + ω ^ 2 * 2)) :
    ∃ β, upsilon (Nc.ncL S (k : Ordinal.{0}) + ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1) + ω ^ 2) <
      upsilon (Nc.ncL S (k : Ordinal.{0}) + β) ∧
      upsilon (Nc.ncL S (k : Ordinal.{0}) + β) ≤ Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ∧
      WfGen S (Nc.ncL S (k : Ordinal.{0})) β := by
  obtain ⟨h1, h2, -⟩ := Vr.vrForms_win (S := S) k hν
  exact ⟨_, h1, h2.le, (wfGen_wit_iff hU k hν).2 hsup⟩

end Googology.Trans.PoR.InaccPsi.R2.Wf

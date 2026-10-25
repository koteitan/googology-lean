import Googology.Trans.PoR.InaccPsi.R2.UnTerm

/-!
# The node conditions of the normal-form mode from [W07a] Lemma 3.30

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

In the normal-form mode the bounds of `Un.Ng` (every leaf and `ρ` below the value) are not extra conditions: they
follow from the argument `ξ = Γ + ρ ∈ Tᵗ` alone.  Every leaf of a level term in full Cantor normal form is `≤
rjDat Γ` (`unLeafDat`), and [W07a] Lemma 3.30 (`R2.rjLevel_lt_vt` for uncountable `M`, `R2.lvLevel_lt_vt` for
countable `M`) bounds the data and `ρ` by `ϑᵗ(Γ + ρ)`.  So a `thg true G r` node is well formed as soon as `G` and `r`
are, `Ω₁ ∣ G`, `G` is in full normal form with a high leaf, and `G[τ] + r[τ] ∈ Tᵗ` (`unNodeHi`, `unNodeLo`).  This
reduces term existence for the normal-form mode to building the Cantor normal form of the level (ordinal arithmetic)
with a high leaf.

* `unLeafDat` (**every leaf of a level in full normal form is `≤ rjDat Γ`**);
* `unNodeHi` (**`Ω₁·Ω₁ ≤ Γ`: the node conditions from `Γ + ρ ∈ Tᵗ`**), `unNodeLo` (**`Γ = Ω₁·q`, `q < Ω₁`,
  `q ∈ Tᵗ`: the same**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Un

open Ordinal Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Uh UnT

/-- **Every leaf of a level term in full Cantor normal form is `≤ rjDat Γ`** (`Γ = G[τ]`; `Uk.UkL.dat_om_add`,
`dat_om_add_r`). -/
theorem unLeafDat {τ : Ordinal.{0}} :
    ∀ (G : UnT true), WF τ G → FNF τ G → Lf (fun c => ev τ c ≤ Rj.rjDat (ev τ G)) G
  | .lf c, hw, _ => by
    show ev τ c ≤ Rj.rjDat (ev τ c)
    rw [Rj.rjDat_small hw.2]
  | .om b, hw, hf => by
    have ih := unLeafDat b hw hf
    have hbE := UnT.ev_lt_E b hw
    have hle : Rj.rjDat (ev τ b) ≤ Rj.rjDat (ev τ (UnT.om b)) := by
      by_cases hb0 : ev τ b = 0
      · rw [hb0, Rj.rjDat_small Rj.rj_Om1_pos]; exact zero_le
      · have := Uk.UkL.dat_om_add (y := 0) hb0 hbE (mul_pos Rj.rj_Om1_pos (opow_pos _ omega0_pos))
        rw [add_zero] at this
        exact this
    exact Lf_mono (fun c hc => hc.trans hle) b ih
  | .ad (.om b) y, hw, hf => by
    have ihb := unLeafDat b hw.1 hf.1
    have ihy := unLeafDat y hw.2 hf.2.1
    have hbE := UnT.ev_lt_E b hw.1
    have hy : ev τ y < Om1 * ω ^ (ev τ b + 1) := by rw [← Uk.UkL.om_mul_omega]; exact hf.2.2.2
    have hle1 : Rj.rjDat (ev τ b) ≤ Rj.rjDat (ev τ (UnT.ad (.om b) y)) := by
      by_cases hb0 : ev τ b = 0
      · rw [hb0, Rj.rjDat_small Rj.rj_Om1_pos]; exact zero_le
      · exact Uk.UkL.dat_om_add hb0 hbE hy
    have hle2 : Rj.rjDat (ev τ y) ≤ Rj.rjDat (ev τ (UnT.ad (.om b) y)) := by
      by_cases hy0 : ev τ y = 0
      · rw [hy0, Rj.rjDat_small Rj.rj_Om1_pos]; exact zero_le
      · exact dat_om_add_r hbE hy0 hy
    exact ⟨Lf_mono (fun c hc => hc.trans hle1) b ihb, Lf_mono (fun c hc => hc.trans hle2) y ihy⟩
  | .ad (.lf _) _, _, hf => hf.2.2.1.elim
  | .ad (.ad _ _) _, _, hf => hf.2.2.1.elim

/-- **The node conditions of the normal-form mode at uncountable levels** (`Ω₁·Ω₁ ≤ Γ`): if `G`, `r` are well
formed, `r[τ] < Ω₁`, `Ω₁ ∣ G`, `G` is in full normal form with a high leaf and `G[τ] + r[τ] ∈ Tᵗ`, then
`thg true G r` is well formed ([W07a] Lemma 3.30 through `R2.rjLevel_lt_vt`, `R2.rkArg_dat`, `R2.vzRem_T`). -/
theorem unNodeHi {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (G : UnT true) (r : UnT false) (hG : WF τ G)
    (hr : WF τ r) (hr1 : ev τ r < Om1) (hgs : Gs G) (hf : FNF τ G) (hd : HdE τ G)
    (hOO : Om1 * Om1 ≤ ev τ G) (hmem : ev τ G + ev τ r ∈ Tset τ) : WF τ (UnT.thg true G r) := by
  obtain ⟨M, hM, -⟩ := UnT.ev_dvd (τ := τ) G hgs
  have hOM : Om1 ≤ M := by
    by_contra hlt
    have := mul_lt_mul_of_pos_left (not_le.1 hlt) Rj.rj_Om1_pos
    rw [← hM] at this
    exact absurd hOO (not_le.2 this)
  have hGE := UnT.ev_lt_E G hG
  have hME : M < Gg.ggE := lt_of_le_of_lt (le_mul_right M Rj.rj_Om1_pos) (hM ▸ hGE)
  rw [hM] at hmem
  have hdT := rkArg_dat hτ hτ1 hOM hME hr1 hmem
  have hrT : ev τ r ∈ Tset τ :=
    vzRem_T hτ hτ1 hmem (Uk.arg_lt2 (hM ▸ hGE) hr1) rfl (dvd_mul_right _ _) hr1
  obtain ⟨hdl, hrl⟩ := rjLevel_lt_vt hτ hτ1 hOM hME hdT hrT hr1
  have hlv := unLeafDat G hG hf
  rw [hM] at hlv
  have hdd := Si.si_rjDat_Om1_mul M hOM hME
  refine ⟨hG, hr, ⟨hr1, hgs, hf, hd, by rw [hM]; exact hmem, ?_, by rw [hM]; exact hrl⟩⟩
  rw [hM]
  exact Lf_mono (fun c hc => (hc.trans hdd).trans_lt hdl) G hlv

/-- **The node conditions of the normal-form mode at countable levels** (`Γ = Ω₁·q`, `q < Ω₁`, `q ∈ Tᵗ`): as
`unNodeHi`, through `R2.lvLevel_lt_vt` (the high leaf gives `τ ≤ q`). -/
theorem unNodeLo {κ τ : Ordinal.{0}} (hB : Bases κ τ) (G : UnT true) (r : UnT false) (hG : WF τ G)
    (hlG : Lv (· ∈ Tset τ) G) (hqG : Qs κ G) (hr : WF τ r) (hr1 : ev τ r < Om1) (hgs : Gs G) (hf : FNF τ G)
    (hd : HdE τ G) {q : Ordinal.{0}} (hq : ev τ G = Om1 * q) (hq1 : q < Om1) (hqT : q ∈ Tset τ)
    (hmem : ev τ G + ev τ r ∈ Tset τ) : WF τ (UnT.thg true G r) := by
  have hτ := hB.2.1
  have hτ1 := hB.2.2.2
  have hdq := Si.si_rjDat_Om1_mul_small q hq1
  have hτq : τ ≤ q := by
    have := (datFN hB G hlG hG hqG hf hd).1
    rw [hq] at this
    exact this.trans hdq
  have hGE := UnT.ev_lt_E G hG
  rw [hq] at hmem
  have hrT : ev τ r ∈ Tset τ :=
    vzRem_T hτ hτ1 hmem (Uk.arg_lt2 (hq ▸ hGE) hr1) rfl (dvd_mul_right _ _) hr1
  obtain ⟨hql, hrl⟩ := lvLevel_lt_vt hτ hτ1 hqT hτq hq1 hrT hr1
  have hlv := unLeafDat G hG hf
  rw [hq] at hlv
  refine ⟨hG, hr, ⟨hr1, hgs, hf, hd, by rw [hq]; exact hmem, ?_, by rw [hq]; exact hrl⟩⟩
  rw [hq]
  exact Lf_mono (fun c hc => (hc.trans hdq).trans_lt hql) G hlv

end Googology.Trans.PoR.InaccPsi.R2.Un

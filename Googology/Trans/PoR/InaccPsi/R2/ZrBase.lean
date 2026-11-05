import Googology.Trans.PoR.InaccPsi.R2.ZoBC
import Googology.Trans.PoR.InaccPsi.R2.ZhCar
import Googology.Trans.PoR.InaccPsi.R2.VzW

/-!
# Zr: the chain reach datum at the base `l₀` of the (B-hi) ∪ (C) induction

`l₀ = Zo.zoBase S` is the least restart index `≥ ι(Ω₂)`, `ρ = υ_{l₀}`, `δ = υ_{l₀+ω+1}`,
`r = r(l₀) = k_{l₀}(Θ_{l₀}(m_{l₀}))`.  The window form of the base datum (chain start `0`) is false at a
short-reach base (`Zo.zoReach0_ref`), so the datum is asked with the chain start `o = r − δ`.  Here:

* `zrNoCross` (**no crossing from below**): if every restart `μ < l` has all its `≤₁`-successors below
  `ρ_l` and `ρ_l ≤ ν_C`, no point `c < ρ_l` is `≤₁` any `g ≥ ρ_l` (the `<₁`-predecessors of a restart
  below `ν_C` are restarts, `R2.pred_restart_C`);
* `zrLowB0` (the restarts below `B₀`: their exact reach `δ_μ + O(μ)`, `R2.reach_allGen`, lies below every
  `ε`-number above `δ_μ`);
* `zrCapBelow` (**every restart `μ < l₀` stays below `ρ`**: below `B₀` by `zrLowB0`, from `B₀` on by
  UPPER and CapV at `μ`, whose cap `P(η_μ + ω^{e(η_μ)}) ≤ P(Ω₂) ≤ ρ` since `η_μ < Ω₂`);
* `zrNu` (`ρ < ν_C`, from the caps below, `Zo.zoNu_gt0`);
* `zrReach` (**the base datum from UPPER at the base**: at a restart `l` below `ν_C` with no crossing from
  below and `Θ_l(m_l) < δ_l`, the closed points `δ + x` (`Zh.zhDense`) give `r = δ + Θ_l(m_l)`, so
  `o = Θ_l(m_l) < δ`, `o = r − δ`, and `YsReachIn l o ρ` holds: `ρ` itself crosses nothing above
  `r` (UPPER), and no point below `ρ` crosses `ρ` at all);
* `zrBCReach` (UPPER at `l₀`, UPPER ∧ LOWER ∧ CapV below `ι(Ω₂)` and the reading bound
  `Θ_{l₀}(m_{l₀}) < δ_{l₀}` give the chain reach datum of the skeleton leaf `skBCReach`);
* `zrReach_long` (the long alternative `υ_{l+ω²} ≤ Θ_l(m_l)`: LOWER gives the datum with chain start `0`);
* `zrBCReach2` (**skBCReach REDUCED** to UPPER ∧ LOWER at `l₀` (skBCBaseUV) and the notation statement
  `Θ_{l₀}(m_{l₀}) < δ_{l₀} ∨ υ_{l₀+ω²} ≤ Θ_{l₀}(m_{l₀})`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zr

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Zo

variable {S : InaccSeq.{0}}

/-- **No crossing of a restart value from below**, from the caps of the restarts below it. -/
theorem zrNoCross {l : Ordinal.{0}} (hl : IsRestartIdx l) (hC : upsilon l ≤ nuC)
    (hcap : ∀ μ, IsRestartIdx μ → μ < l → ∀ g, le1 (upsilon μ) g → g < upsilon l) :
    ∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g := by
  intro c hc g hg h
  have h' : le1 c (upsilon l) := le1_of_le_of_le1 hc.le hg h
  obtain ⟨μ, hμ, rfl⟩ := pred_restart_C hl hC hc h'
  have hμl : μ < l := upsilon_normal.strictMono.lt_iff_lt.1 hc
  exact absurd (hcap μ hμ hμl _ h') (lt_irrefl _)

/-- **A restart below `B₀` reaches below every `ε`-number above its first block top.** -/
theorem zrLowB0 {μ x : Ordinal.{0}} (hμ : IsRestartIdx μ) (hμB : μ < cdB0) (hx : InE x)
    (hδ : upsilon (μ + ω + 1) < x) : ∀ g, le1 (upsilon μ) g → g < x := by
  intro g hg
  have hr := reach_allGen vzSpec2 hμ hμB
  have hμ1 : μ < Om1 := hμB.trans (Om1_add_lt vzLam_lt_Om1 ww_lt_Om1)
  have hO := vzOrec_lt_δ hμ hμ1
  exact (hr.2 g hg).trans_lt (InE.add_lt hx hδ (hO.trans hδ))

/-- **Every restart `μ < l₀` stays below `ρ = υ_{l₀}`**, given UPPER ∧ LOWER ∧ CapV below `ι(Ω₂)`. -/
theorem zrCapBelow
    (hlow : ∀ μ, CdRange S μ → μ < iota S (Om (1 + 1)) → CdUpper S μ ∧ CdLower S μ ∧ CdCapV S μ) :
    ∀ μ, IsRestartIdx μ → μ < zoBase S → ∀ g, le1 (upsilon μ) g → g < upsilon (zoBase S) := by
  intro μ hμ hlt g hg
  have hm := upsilon_normal.strictMono
  have hl0 : IsRestartIdx (zoBase S) := zoBase_spec.1
  have hx : InE (upsilon (zoBase S)) := ups_inE hl0
  by_cases hB : μ < cdB0
  · refine zrLowB0 hμ hB hx ?_ g hg
    have h1 : μ + ω < zoBase S := add_omega_lt (ri_iff.1 hl0).2 hlt
    have h2 : μ + ω + 1 < zoBase S := by
      have := (ri_lim hl0).succ_lt h1
      rwa [Order.succ_eq_add_one] at this
    exact hm h2
  · have hB' : cdB0 ≤ μ := not_lt.1 hB
    have hρm : upsilon μ < cdMstar S :=
      (hm hlt).trans (by rw [← zoTop_ups (S := S)]; exact hm zoBase_lt_top)
    have hr : CdRange S μ := zoRange_lt hμ hB' hρm
    have hι := zoBase_lt_iota hμ hlt
    obtain ⟨hU, -, hV⟩ := hlow μ hr hι
    have hcap := cdCapAt_of_upper hU hV
    refine (hcap g hg).trans_le ?_
    have h1 : 1 ≤ μ := Order.one_le_iff_ne_zero.2 hμ.1
    obtain ⟨-, hιη, hη2⟩ := cdEta_spec (S := S) h1 hι
    have hη0 : cdEta S μ ≠ 0 := by
      intro h0
      rw [h0, iota_zero] at hιη
      exact (ri_lim hμ).succ_ne 0 (by rw [succ_eq_add_one, zero_add]; exact hιη)
    have hE2 : ω ^ Om (1 + 1 : Ordinal.{0}) = Om (1 + 1) := Low.opow_eq_self_of_SC Gg.gg_SC_Om2
    obtain ⟨-, hw⟩ := cdWin (η0 := 0) (e := Om (1 + 1)) (dvd_zero _) (pos_iff_ne_zero.2 hη0)
      (by rw [zero_add, hE2]; exact hη2)
    rw [zero_add, hE2] at hw
    calc cdCapB S μ = Pv S (cdEta S μ + ω ^ cdExp (cdEta S μ)) := rfl
      _ ≤ Pv S (Om (1 + 1)) := Pv_mono hw.le
      _ = upsilon (iota S (Om (1 + 1))) := (ups_iota S _).symm
      _ ≤ upsilon (zoBase S) := hm.monotone zoBase_spec.2

/-- **`ρ = υ_{l₀} < ν_C`**, from the caps below (`Zo.zoNu_gt0`). -/
theorem zrNu
    (hlow : ∀ μ, CdRange S μ → μ < iota S (Om (1 + 1)) → CdUpper S μ ∧ CdLower S μ ∧ CdCapV S μ) :
    upsilon (zoBase S) < nuC := by
  have hm := upsilon_normal.strictMono
  have hbm : upsilon (zoBase S) < cdMstar S := by
    rw [← zoTop_ups (S := S)]; exact hm zoBase_lt_top
  refine zoNu_gt0 hbm.le fun l hl hB h => ?_
  have hlt : l < zoBase S := hm.lt_iff_lt.1 h
  have hr : CdRange S l := zoRange_lt hl hB (h.trans hbm)
  obtain ⟨hU, -, hV⟩ := hlow l hr (zoBase_lt_iota hl hlt)
  exact cdCapAt_of_upper hU hV

/-- **The chain reach datum at a restart from UPPER**, with the chain start `o = r − δ = Θ_l(m_l)`. -/
theorem zrReach {l : Ordinal.{0}} (hl : IsRestartIdx l) (hU : CdUpper S l)
    (hN : ∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) (hν : upsilon l < nuC)
    (hTh : cdTheta S l (cdCode S l) < cdDelta l) :
    ∃ o, o < upsilon (l + ω + 1) ∧ o ≤ Ys.ysO S l ∧ Ys.YsReachIn l o (upsilon l) := by
  set p := cdTheta S l (cdCode S l) with hp
  have hK : ∀ x ≤ p, cdDelta l + x ∈ cdK l := fun x hx => Zh.zhDense hl hν (hx.trans_lt hTh)
  have hR : cdR S l = cdDelta l + p := cdk_interval hK p le_rfl
  have hO : Ys.ysO S l = p := by
    unfold Ys.ysO
    rw [hR]
    exact Ordinal.add_sub_cancel _ _
  refine ⟨p, hTh, hO.ge, ?_⟩
  intro j c hc _ d hd1 _ h
  exfalso
  have htop : cdDelta l + p ≤ topA (l + ω) (upsilon (l + ω + 1) + p) j := by
    rcases j with _ | j
    · exact le_rfl
    · show cdDelta l + p ≤ upsilon (l + ω + ω * (j : Ordinal.{0}) + ω + 1)
      have hpos : 0 < l + ω + ω * (j : Ordinal.{0}) + ω + 1 := zero_le.trans_lt (lt_add_one _)
      have hE := upsPt_inE (upsPt_upsilon hpos)
      have hidx : l + ω + 1 < l + ω + ω * (j : Ordinal.{0}) + ω + 1 := by
        calc l + ω + 1 ≤ l + ω + ω * (j : Ordinal.{0}) + 1 := add_le_add le_self_add le_rfl
          _ < l + ω + ω * (j : Ordinal.{0}) + (ω + 1) :=
            (add_lt_add_iff_left _).2 (one_lt_omega0.trans_le le_self_add)
          _ = l + ω + ω * (j : Ordinal.{0}) + ω + 1 := (add_assoc _ _ _).symm
      have hδ : cdDelta l < upsilon (l + ω + ω * (j : Ordinal.{0}) + ω + 1) :=
        upsilon_normal.strictMono hidx
      exact (InE.add_lt hE hδ (hTh.trans hδ)).le
  have hdr : cdR S l < d := by rw [hR]; exact htop.trans_lt hd1
  rcases hc.lt_or_eq with hlt | rfl
  · exact hN c hlt d ((cdRho_lt_R S l).le.trans hdr.le) h
  · exact hU (le1_of_le_of_le1 ((cdRho_lt_R S l).le.trans le_self_add) (Order.add_one_le_of_lt hdr) h)

/-- **skBCReach REDUCED**: UPPER ∧ LOWER ∧ CapV below `ι(Ω₂)`, UPPER at `l₀` and the reading bound
`Θ_{l₀}(m_{l₀}) < δ_{l₀}` give the chain reach datum at the base `l₀`. -/
theorem zrBCReach
    (hlow : ∀ μ, CdRange S μ → μ < iota S (Om (1 + 1)) → CdUpper S μ ∧ CdLower S μ ∧ CdCapV S μ)
    (hU : CdUpper S (zoBase S))
    (hTh : cdTheta S (zoBase S) (cdCode S (zoBase S)) < cdDelta (zoBase S)) :
    ∃ o, o < upsilon (zoBase S + ω + 1) ∧ o ≤ Ys.ysO S (zoBase S) ∧
      Ys.YsReachIn (zoBase S) o (upsilon (zoBase S)) :=
  zrReach zoBase_spec.1 hU (zrNoCross zoBase_spec.1 (zrNu hlow).le (zrCapBelow hlow)) (zrNu hlow) hTh

/-- **The long alternative**: if `υ_{l+ω²} ≤ Θ_l(m_l)`, LOWER at `l` gives the window form of the datum
(chain start `0`, `Ys.ysReach_long`). -/
theorem zrReach_long {l : Ordinal.{0}} (hL : CdLower S l)
    (hTh : upsilon (l + ω * ω) ≤ cdTheta S l (cdCode S l)) :
    ∃ o, o < upsilon (l + ω + 1) ∧ o ≤ Ys.ysO S l ∧ Ys.YsReachIn l o (upsilon l) := by
  have hR : upsilon (l + ω * ω) ≤ cdR S l :=
    hTh.trans ((cdk_strictMono l).id_le _)
  have hE : le1 (upsilon l) (upsilon (l + ω * ω)) :=
    le1_of_le_of_le1 (upsilon_normal.strictMono.monotone le_self_add) hR hL
  refine ⟨0, (upsPt_upsilon ((zero_le).trans_lt (lt_add_one _))).1, zero_le, ?_⟩
  exact Ys.ysReach_long hE

/-- **skBCReach REDUCED to UPPER ∧ LOWER at `l₀` and the notation statement `skBCThPos`**: either
`Θ_{l₀}(m_{l₀}) < δ_{l₀}` (short reach, chain start `r − δ`) or `υ_{l₀+ω²} ≤ Θ_{l₀}(m_{l₀})` (long reach,
chain start `0`). -/
theorem zrBCReach2
    (hlow : ∀ μ, CdRange S μ → μ < iota S (Om (1 + 1)) → CdUpper S μ ∧ CdLower S μ ∧ CdCapV S μ)
    (hU : CdUpper S (zoBase S)) (hL : CdLower S (zoBase S))
    (hTh : cdTheta S (zoBase S) (cdCode S (zoBase S)) < cdDelta (zoBase S) ∨
      upsilon (zoBase S + ω * ω) ≤ cdTheta S (zoBase S) (cdCode S (zoBase S))) :
    ∃ o, o < upsilon (zoBase S + ω + 1) ∧ o ≤ Ys.ysO S (zoBase S) ∧
      Ys.YsReachIn (zoBase S) o (upsilon (zoBase S)) := by
  rcases hTh with h | h
  · exact zrBCReach hlow hU h
  · exact zrReach_long hL h

end Googology.Trans.PoR.InaccPsi.R2.Zr

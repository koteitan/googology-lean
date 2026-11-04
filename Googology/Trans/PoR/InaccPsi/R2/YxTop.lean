import Googology.Trans.PoR.InaccPsi.R2.YxSpec

/-!
# Yx: the least-counterexample argument in the top window `W_ω`

`Yx.yxNu_gt` stops at `L(ω)`: for the first non-standard pair `ρ_λ <₂ ν_C` with `ρ_λ = L(ω)` the `≤₁`-predecessors
may be the points `L(k)` (code `P'`, no cap below `ν_C`).  Above `L(ω)` the name window of `λ` lies in
`(Ω_ω + P'·ω, Ω_ω + P'·ω + P')`, so its last exponent is `< P'` and every predecessor in the window is a range
restart.  Hence

* `yxNu_gtTop` (**CAP-0, CAP-1 below `X < L(ω+1)` and "`L(ω) <₂ ν_C` only if `L(ω+1) ≤ ν_C`" give `X < ν_C`**);
* `yxSpec_capsTop`: the least-counterexample theorem `Yx.yxSpec_caps` for `υ_B ≤ L(ω+1)` with that one pair
  hypothesis at `L(ω)`.

The pair hypothesis `YxLwNo2 S` (`ν_C < L(ω+1) → ¬ L(ω) <₂ ν_C`) is implied by the target `L(ω+1) ≤ ν_C` and,
with the caps, implies it (`yxLwNo2_iff`): it is the whole pair content of the top window.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Yx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- The pair hypothesis at `L(ω)`: if `ν_C < L(ω+1)` then `L(ω)` is not the left end of a pair with `ν_C`. -/
def YxLwNo2 (S : InaccSeq.{0}) : Prop := nuC < Nc.ncL S (ω + 1) → ¬ le2 (Nc.ncL S ω) nuC

/-- `L(ω+1) = P(Ω_ω + P'·ω + P')`. -/
theorem yxL1_eq (S : InaccSeq.{0}) :
    Nc.ncL S (ω + 1) = Pv S (Om ω + Nc.ncPp S * ω + Nc.ncPp S) := by
  rw [Lw.lw_L_eq S, mul_add_one, add_assoc]

/-- **Strict NU-LOW″ below `L(ω+1)`** with the pair hypothesis at `L(ω)`. -/
theorem yxNu_gtTop {X : Ordinal.{0}} (hX : X < Nc.ncL S (ω + 1)) (h0 : CdCAP0 S) (h1 : CdCAP1 S X)
    (hLw : YxLwNo2 S) : X < nuC := by
  by_contra hlt
  have hνL : nuC ≤ X := not_lt.1 hlt
  obtain ⟨l, hl, -, hlν, hl2, -, -, hP, hW, -⟩ := Lb.lbFirst
  have hLeq : Nc.ncL S ω = Pv S (Om ω + Nc.ncPp S * ω) := Lw.lw_L_eq S ω
  have hlT : upsilon l < Pv S (Om ω + Nc.ncPp S * ω + Nc.ncPp S) :=
    yxL1_eq S ▸ (hlν.trans_le (hνL.trans hX.le))
  have hl1 : 1 ≤ l := Order.one_le_iff_ne_zero.2 hl.1
  obtain ⟨ηt, -, hηt⟩ := iota_onto (S := S) _ l hl1 (cd_lt_iota hlT).le
  have hne : {η | iota S η = l}.Nonempty := ⟨ηt, hηt⟩
  have hηm : iota S (sInf {η | iota S η = l}) = l := csInf_mem hne
  have hmin : ∀ η < sInf {η | iota S η = l}, iota S η ≠ l := fun η h he =>
    (csInf_le' (s := {η | iota S η = l}) he).not_gt h
  generalize sInf {η | iota S η = l} = ηm at hηm hmin
  have hpvm : Pv S ηm = upsilon l := by
    calc Pv S ηm = upsilon (iota S ηm) := (ups_iota S ηm).symm
      _ = upsilon l := by rw [hηm]
  have hηm0 : ηm ≠ 0 := by
    rintro rfl
    rw [iota_zero] at hηm
    exact (ri_lim hl).succ_ne 0 (by rw [succ_eq_add_one, zero_add]; exact hηm)
  obtain ⟨η0, hdec, hdvd⟩ := cdExp_decomp hηm0
  -- the top case: the last exponent of the least name is below `P'`
  have hPE : ω ^ Nc.ncPp S = Nc.ncPp S := Lw.lw_Pp_opow S
  have hWE : ω ^ Om ω = Om ω := Low.opow_eq_self_of_SC (SC_Om omega0_ne_zero)
  have heP : Nc.ncL S ω < upsilon l → cdExp ηm < Nc.ncPp S := by
    intro hgt
    have hd : ω ^ Nc.ncPp S ∣ Om ω + Nc.ncPp S * ω := by
      refine dvd_add ?_ ?_
      · conv_rhs => rw [← hWE]
        exact opow_dvd_opow ω (cdPp_lt_Om_omega S).le
      · rw [hPE]; exact dvd_mul_right _ _
    have hx0 : Om ω + Nc.ncPp S * ω < ηm := by
      by_contra h
      push Not at h
      have h' := Pv_mono (S := S) h
      rw [hpvm, ← hLeq] at h'
      exact absurd hgt (not_lt.2 h')
    have hx1 : ηm < Om ω + Nc.ncPp S * ω + ω ^ Nc.ncPp S := by
      rw [hPE]
      by_contra h
      push Not at h
      have h' := Pv_mono (S := S) h
      rw [hpvm] at h'
      exact absurd (hlT.trans_le h') (lt_irrefl _)
    exact (cdWin hd hx0 hx1).1
  generalize cdExp ηm = e at hdec hdvd heP
  have hη0m : η0 < ηm := by
    rw [hdec]; exact lt_add_of_pos_right _ (opow_pos _ omega0_pos)
  have hν : iota S η0 < l := lt_of_le_of_ne ((iota_mono (S := S) ηm η0 hη0m.le).trans_eq hηm) (hmin η0 hη0m)
  -- a restart witness `ρ_μ ≤₁ ν_C` with `μ ∈ (ι(η₀), λ)`
  obtain ⟨y, hνy, hyl, hy⟩ := hP (upsilon (iota S η0)) (upsilon_normal.strictMono hν)
  obtain ⟨μ, hμ, hBμ, rfl, -⟩ := hW y hyl hy
  have hμν : iota S η0 < μ := upsilon_normal.strictMono.lt_iff_lt.1 hνy
  have hμl : μ < l := upsilon_normal.strictMono.lt_iff_lt.1 hyl
  have hμX : upsilon μ < X := (upsilon_normal.strictMono hμl).trans (hlν.trans_le hνL)
  obtain ⟨hg, hιμ, -⟩ := cdEta_spec (S := S) (Order.one_le_iff_ne_zero.2 hμ.1) (hμl.trans_eq hηm.symm)
  have hpvμ : Pv S (cdEta S μ) = upsilon μ := by
    calc Pv S (cdEta S μ) = upsilon (iota S (cdEta S μ)) := (ups_iota S _).symm
      _ = upsilon μ := by rw [hιμ]
  have hx0 : η0 < cdEta S μ := by
    by_contra h
    push Not at h
    have h' := iota_mono (S := S) η0 _ h
    rw [hιμ] at h'
    exact absurd h' (not_le.2 hμν)
  have hxm : cdEta S μ < η0 + ω ^ e := by
    rw [← hdec]
    by_contra h
    push Not at h
    have h' := iota_mono (S := S) (cdEta S μ) ηm h
    rw [hιμ, hηm] at h'
    exact absurd h' (not_le.2 hμl)
  obtain ⟨hxe, hxw⟩ := cdWin hdvd hx0 hxm
  -- the cap of `μ` is at most `ρ_λ`
  have hcapl : cdCapB S μ ≤ upsilon l := by
    unfold cdCapB
    calc Pv S (cdEta S μ + ω ^ cdExp (cdEta S μ)) ≤ Pv S ηm := Pv_mono (hxw.le.trans_eq hdec.symm)
      _ = upsilon l := hpvm
  -- the cap of `μ` applies
  have hcapμ : CdCapAt S μ := by
    rcases lt_or_ge (upsilon μ) (cdMstar S) with hlev | hlev
    · exact h0 μ hμ hBμ hlev
    · refine h1 μ hμ hBμ hlev hμX ?_
      have hxP : cdExp (cdEta S μ) < Nc.ncPp S := by
        rcases lt_trichotomy (upsilon l) (Nc.ncL S ω) with hlω | hlω | hlω
        · have hx1 : Om ω ≤ cdEta S μ := by
            by_contra h
            push Not at h
            have h1' := Pv_lt_succ hg
            have h2' : Pv S (cdEta S μ + 1) ≤ Pv S (Om ω) := Pv_mono (Order.add_one_le_of_lt h)
            rw [hpvμ] at h1'
            exact absurd (h1'.trans_le h2') (not_lt.2 hlev)
          have htop : η0 + ω ^ e < Om ω + Nc.ncPp S * ω := by
            rw [← hdec]
            by_contra h
            push Not at h
            have h' := Pv_mono (S := S) h
            rw [hpvm, ← hLeq] at h'
            exact absurd (hlω.trans_le h') (lt_irrefl _)
          by_contra h
          push Not at h
          exact cd_l2_contra hdvd hx1 hxm htop (lt_of_le_of_lt h hxe)
        · exact absurd (hlω ▸ hl2) (hLw ((hνL.trans_lt hX)))
        · exact hxe.trans (heP hlω)
      show cdCodeOf S (cdEta S μ) < Nc.ncPp S
      rw [cdCodeOf_of_lt (hxP.trans (cdPp_lt_Om2 S))]
      exact (cdOff_le _).trans_lt hxP
  exact absurd ((hcapμ nuC hy).trans_le hcapl) (not_lt.2 hlν.le)

/-- **The least-counterexample theorem up to `L(ω+1)`** (the top window), with the pair hypothesis at `L(ω)`. -/
theorem yxSpec_capsTop {O : Ordinal.{0} → Ordinal.{0}} {l0 B : Ordinal.{0}} (Sp : YxSpec O l0 B)
    (hX : upsilon B ≤ Nc.ncL S (ω + 1)) (h0 : CdCAP0 S) (hLw : YxLwNo2 S)
    (hb : ∀ μ, CdRange S μ → upsilon μ < upsilon l0 → CdCapAt S μ) (hl0 : ¬ CdRange S l0)
    (hO : ∀ μ, l0 < μ → O μ = Ys.ysO S μ)
    (hV : ∀ μ, CdRange S μ → upsilon l0 < upsilon μ → upsilon μ < upsilon B → CdCapV S μ) :
    upsilon B ≤ nuC ∧ Ys.YsSpec O l0 B := by
  have hρB : upsilon l0 < upsilon B := upsilon_normal.strictMono Sp.lt
  have hρ0 : upsilon l0 < nuC := by
    refine yxNu_gtTop (hρB.trans_le hX) h0 ?_ hLw
    intro μ hμ hB hlev hlX hc
    exact hb μ ⟨hμ, hB, hlX.trans (hρB.trans_le hX), hc⟩ hlX
  suffices hν : upsilon B ≤ nuC from ⟨hν, Sp.toYs hν⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨ξ, hξ, he⟩ := nuC_restart
  have i0 : l0 < ξ := upsilon_normal.strictMono.lt_iff_lt.1 (he ▸ hρ0)
  have i1 : ξ < B := upsilon_normal.strictMono.lt_iff_lt.1 (he ▸ hlt)
  have Sp' : Ys.YsSpec O l0 ξ := (Sp.restr hξ i0 i1.le).toYs he.symm.le
  have hνX : nuC < Nc.ncL S (ω + 1) := hlt.trans_le hX
  refine absurd (yxNu_gtTop hνX h0 ?_ hLw) (lt_irrefl _)
  intro μ hμ hB hlev hlX hc
  have hr : CdRange S μ := ⟨hμ, hB, hlX.trans hνX, hc⟩
  rcases lt_trichotomy (upsilon μ) (upsilon l0) with h | h | h
  · exact hb μ hr h
  · exact absurd (upsilon_normal.strictMono.injective h ▸ hr) hl0
  · have j0 : l0 < μ := upsilon_normal.strictMono.lt_iff_lt.1 h
    have j1 : μ < ξ := upsilon_normal.strictMono.lt_iff_lt.1 (he ▸ hlX)
    have hU : CdUpper S μ := Ys.ysUpper_all Sp' hμ j0.le j1 (by rw [hO μ j0]; exact Ys.ysO_eq S μ)
    exact cdCapAt_of_upper hU (hV μ hr h (hlX.trans hlt))

/-- **The pair hypothesis at `L(ω)` follows from the target `L(ω+1) ≤ ν_C`** (non-vacuity). -/
theorem yxLwNo2_of_nu (h : Nc.ncL S (ω + 1) ≤ nuC) : YxLwNo2 S := fun h' => absurd h (not_le.2 h')

/-- **The pair hypothesis at `L(ω)` is the whole pair content of the top window**: with a pair-free
specification on `W_ω` and the caps, `YxLwNo2 S ↔ L(ω+1) ≤ ν_C`. -/
theorem yxLwNo2_iff {O : Ordinal.{0} → Ordinal.{0}}
    (Sp : YxSpec O (iota S (Om ω + Nc.ncPp S * ω)) (iota S (Om ω + Nc.ncPp S * (ω + 1))))
    (h0 : CdCAP0 S)
    (hb : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → CdCapAt S μ)
    (hl0 : ¬ CdRange S (iota S (Om ω + Nc.ncPp S * ω)))
    (hO : ∀ μ, iota S (Om ω + Nc.ncPp S * ω) < μ → O μ = Ys.ysO S μ)
    (hV : ∀ μ, CdRange S μ → Wj.WjTop S μ → CdCapV S μ) :
    YxLwNo2 S ↔ Nc.ncL S (ω + 1) ≤ nuC := by
  refine ⟨fun hLw => ?_, yxLwNo2_of_nu⟩
  have e0 := Pp.ppL_eq_ups (S := S) ω
  have e1 := Pp.ppL_eq_ups (S := S) (ω + 1)
  have := yxSpec_capsTop Sp (e1 ▸ le_rfl) h0 hLw (fun μ hr h => hb μ hr (e0 ▸ h)) hl0 hO
    (fun μ hr h1 h2 => hV μ hr ⟨e0 ▸ h1, e1 ▸ h2⟩)
  exact e1 ▸ this.1

end Googology.Trans.PoR.InaccPsi.R2.Yx

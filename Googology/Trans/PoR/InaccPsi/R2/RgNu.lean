import Googology.Trans.PoR.InaccPsi.R2.RcT
import Googology.Trans.PoR.InaccPsi.R2.TpUps
import Googology.Trans.PoR.InaccPsi.R2.TpEQ
import Googology.Trans.PoR.InaccPsi.R2.RzRoad

/-!
# `L(ω+1) ≤ ν_C` from the caps and one `≤₂`-statement at `L(ω)`; `T` is exactly that statement

`L(ξ) = Nc.ncL S ξ`, `P' = Nc.ncPp S`, `m* = L(0)`, `ν_C` the right end of the first non-standard `<₂`-pair,
`lh` the reach (`IsReach R2C`), CAP-0, CAP-1 as in `Cd.CdCAP0`, `Cd.CdCAP1`, `T`: `L(ω) ≤₁ L(ω+1)`.

* `RgLwPair S` (**the pair statement at `L(ω)`**): no `d ∈ (L(ω), L(ω+1))` with `L(ω) ≤₂ d` and
  `lh(L(ω)) = d`;
* `rgFirst_ne` (**the first non-standard pair `ρ_λ <₂ ν_C` with `ρ_λ < L(ω+1)` has `ρ_λ = L(ω)`**, given
  CAP-0 and CAP-1 below `L(ω+1)`): the argument of `Cd.cdLow` in the window of the name of `λ`; above `L(ω)`
  the window names lie above `Ω_ω + P'·ω` (`cdWin` at `Ω_ω + P'·ω` itself), so their codes are `< P'`
  (`Tp.tpCode_top`);
* `rgNu_of_caps` (**CAP-0, CAP-1 below `L(ω+1)` and `RgLwPair` give `L(ω+1) ≤ ν_C`**), `rgPair_of_nu`
  (**`L(ω+1) ≤ ν_C` gives `RgLwPair`**: below `ν_C` every `≤₂`-pair is standard, and `L(ω)` is not a
  `τ`-point), `rgPair_of_T` (**`T` gives `RgLwPair`**), `rgPair_of_P` (`L(ω) ≤ ν_C` and (P) give it),
  `rgPair_of_no2` (the second clause of `CvNoPair L(ω) L(ω+1)` gives it);
* `rgCAP1_top`, `rgCAP_of_enum` (**CAP-0 and CAP-1 below `L(ω+1)`** from UPPER and CapV at the `Rz.RzRest`
  Range restarts below `L(ω)` and CapV at the Range restarts above `L(ω)`);
* `rgT_of_pair` (**`T`** from `RgLwPair`, the caps, the supply at every `L(n+1)`, UPPER/LOWER at the
  `Rz.RzRest` Range restarts and `LrGap` at `L(ω)`: `CvNoPair`, `L(ω) < ν_C`, `υ_{L(ω)+L(ω)} ≤ ν_C` and
  `CxStdPairTop` of `Rc.rcT_of_Lw` all follow from `L(ω+1) ≤ ν_C`), `rgT_iff_pair`, `rgNu_iff_pair`
  (**under those hypotheses `T ⇔ RgLwPair ⇔ L(ω+1) ≤ ν_C`**);
* `rgRoad` (**the road `Rc.rcRoad_Lw` with `CvNoPair L(ω) L(ω+1)`, `L(ω) < ν_C`, `υ_{L(ω)+L(ω)} ≤ ν_C`,
  `CxStdPairTop`, `CxUpsRestTop` replaced by `RgLwPair` and CapV above `L(ω)`**).

No new axiom.  New definition (hypothesis name only): `RgLwPair`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rg

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **The pair statement at `L(ω)`**: no `d ∈ (L(ω), L(ω+1))` with `L(ω) ≤₂ d` and `lh(L(ω)) = d`. -/
def RgLwPair (S : InaccSeq.{0}) : Prop :=
  ∀ d, Nc.ncL S ω < d → d < Nc.ncL S (ω + 1) → le2 (Nc.ncL S ω) d → IsReach R2C (Nc.ncL S ω) d → False

/-- `Ω_ω + P'·ω` is divisible by `ω^{P'+1}`, and `P'·ω = ω^{P'+1}`. -/
theorem rgC_dvd (S : InaccSeq.{0}) :
    Nc.ncPp S * ω = ω ^ (Nc.ncPp S + 1) ∧ ω ^ (Nc.ncPp S + 1) ∣ Om ω + Nc.ncPp S * ω := by
  have hSC : SC (Om (ω : Ordinal.{0})) := SC_Om omega0_ne_zero
  have hOw : ω ^ Om (ω : Ordinal.{0}) = Om ω := Low.opow_eq_self_of_SC hSC
  have hPw : Nc.ncPp S * ω = ω ^ (Nc.ncPp S + 1) := by
    conv_lhs => rw [← Lw.lw_Pp_opow S]
    rw [← opow_succ, succ_eq_add_one]
  have hPO : Nc.ncPp S + 1 ≤ Om ω := (hSC.add_one_lt (cdPp_lt_Om_omega S)).le
  refine ⟨hPw, dvd_add ?_ (by rw [hPw])⟩
  rw [← hOw]; exact opow_dvd_opow ω hPO

/-- **The window above `L(ω)`**: if `ω^e ∣ η₀` and `Ω_ω + P'·ω < η₀ + ω^e < Ω_ω + P'·(ω+1)` then
`Ω_ω + P'·ω ≤ η₀`. -/
theorem rgWin_top {η0 e : Ordinal.{0}} (hd : ω ^ e ∣ η0)
    (h1 : Om ω + Nc.ncPp S * ω < η0 + ω ^ e) (h2 : η0 + ω ^ e < Om ω + Nc.ncPp S * (ω + 1)) :
    Om ω + Nc.ncPp S * ω ≤ η0 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨hPw, hdv⟩ := rgC_dvd S
  have hc0 : Om ω + Nc.ncPp S * ω ≠ 0 :=
    (lt_of_lt_of_le (Om_pos omega0_ne_zero) le_self_add).ne'
  have hex : Nc.ncPp S + 1 ≤ cdExp (Om ω + Nc.ncPp S * ω) := cdExp_max hc0 hdv
  obtain ⟨-, hw⟩ := cdWin hd hlt h1
  have h3 : Om ω + Nc.ncPp S * ω + ω ^ (Nc.ncPp S + 1) < Om ω + Nc.ncPp S * ω + Nc.ncPp S := by
    rw [mul_add_one, ← add_assoc] at h2
    exact (add_le_add le_rfl (opow_le_opow_right omega0_pos hex)).trans_lt (hw.trans h2)
  have h4 := (add_lt_add_iff_left _).1 h3
  have h5 : ω ^ Nc.ncPp S < ω ^ (Nc.ncPp S + 1) :=
    (opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_one _)
  rw [Lw.lw_Pp_opow] at h5
  exact absurd h4 (not_lt.2 h5.le)

/-- **The first non-standard pair below `L(ω+1)` starts at `L(ω)`**: given CAP-0 and CAP-1 below `L(ω+1)`,
a restart `λ` with the properties of `Lb.lbFirst` and `ρ_λ < L(ω+1)` has `ρ_λ = L(ω)`. -/
theorem rgFirst_ne (h0 : CdCAP0 S) (h1 : CdCAP1 S (Nc.ncL S (ω + 1))) {l : Ordinal.{0}}
    (hl : IsRestartIdx l) (hlν : upsilon l < nuC) (hP : Nc.NcCofPred (upsilon l) nuC)
    (hW : ∀ y < upsilon l, le1 y nuC → ∃ μ, IsRestartIdx μ ∧ VzLam + ω * ω ≤ μ ∧ y = upsilon μ ∧
      IsReach R2C (upsilon μ) nuC)
    (hX : upsilon l < Nc.ncL S (ω + 1)) (hne : upsilon l ≠ Nc.ncL S ω) : False := by
  have hL1 : Nc.ncL S (ω + 1) = Pv S (Om ω + Nc.ncPp S * (ω + 1)) := Lw.lw_L_eq S (ω + 1)
  have hL0 : Nc.ncL S ω = Pv S (Om ω + Nc.ncPp S * ω) := Lw.lw_L_eq S ω
  have hlT : upsilon l < Pv S (Om ω + Nc.ncPp S * (ω + 1)) := hL1 ▸ hX
  have hl1 : 1 ≤ l := Order.one_le_iff_ne_zero.2 hl.1
  obtain ⟨ηt, -, hηt⟩ := iota_onto (S := S) _ l hl1 (cd_lt_iota hlT).le
  have hne' : {η | iota S η = l}.Nonempty := ⟨ηt, hηt⟩
  have hηm : iota S (sInf {η | iota S η = l}) = l := csInf_mem hne'
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
  generalize cdExp ηm = e at hdec hdvd
  have hη0m : η0 < ηm := by
    rw [hdec]; exact lt_add_of_pos_right _ (opow_pos _ omega0_pos)
  have hν : iota S η0 < l :=
    lt_of_le_of_ne ((iota_mono (S := S) ηm η0 hη0m.le).trans_eq hηm) (hmin η0 hη0m)
  obtain ⟨y, hνy, hyl, hy⟩ := hP (upsilon (iota S η0)) (upsilon_normal.strictMono hν)
  obtain ⟨μ, hμ, hBμ, rfl, -⟩ := hW y hyl hy
  have hμν : iota S η0 < μ := upsilon_normal.strictMono.lt_iff_lt.1 hνy
  have hμl : μ < l := upsilon_normal.strictMono.lt_iff_lt.1 hyl
  have hμX : upsilon μ < Nc.ncL S (ω + 1) := (upsilon_normal.strictMono hμl).trans hX
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
  have hcapl : cdCapB S μ ≤ upsilon l := by
    unfold cdCapB
    calc Pv S (cdEta S μ + ω ^ cdExp (cdEta S μ)) ≤ Pv S ηm := Pv_mono (hxw.le.trans_eq hdec.symm)
      _ = upsilon l := hpvm
  have hcapμ : CdCapAt S μ := by
    rcases lt_or_ge (upsilon μ) (cdMstar S) with hlev | hlev
    · exact h0 μ hμ hBμ hlev
    · refine h1 μ hμ hBμ hlev hμX ?_
      rcases lt_or_gt_of_ne hne with hlo | hhi
      · -- below `L(ω)`: the argument of `Cd.cdLow`
        have hx1 : Om ω ≤ cdEta S μ := by
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
          rw [hpvm, ← hL0] at h'
          exact absurd (hlo.trans_le h') (lt_irrefl _)
        have hxP : cdExp (cdEta S μ) < Nc.ncPp S := by
          by_contra h
          push Not at h
          exact cd_l2_contra hdvd hx1 hxm htop (lt_of_le_of_lt h hxe)
        show cdCodeOf S (cdEta S μ) < Nc.ncPp S
        rw [cdCodeOf_of_lt (hxP.trans (cdPp_lt_Om2 S))]
        exact (cdOff_le _).trans_lt hxP
      · -- above `L(ω)`: the window names lie above `Ω_ω + P'·ω`
        have hc1 : Om ω + Nc.ncPp S * ω < η0 + ω ^ e := by
          rw [← hdec]
          by_contra h
          push Not at h
          have h' := Pv_mono (S := S) h
          rw [hpvm, ← hL0] at h'
          exact absurd (hhi.trans_le h') (lt_irrefl _)
        have hc2 : η0 + ω ^ e < Om ω + Nc.ncPp S * (ω + 1) := by
          rw [← hdec]
          by_contra h
          push Not at h
          have h' := Pv_mono (S := S) h
          rw [hpvm] at h'
          exact absurd (hlT.trans_le h') (lt_irrefl _)
        have hcη : Om ω + Nc.ncPp S * ω ≤ η0 := rgWin_top hdvd hc1 hc2
        have hLμ : Nc.ncL S ω < upsilon μ := by
          rw [hL0, ← hpvμ]
          exact (Pv_lt_succ (Ra.raLw_named (S := S)).1).trans_le
            (Pv_mono (Order.add_one_le_of_lt (hcη.trans_lt hx0)))
        exact Tp.tpCode_top hμ hLμ hμX
  exact absurd ((hcapμ nuC hy).trans_le hcapl) (not_lt.2 hlν.le)

/-- **CAP-0, CAP-1 below `L(ω+1)` and `RgLwPair` give `L(ω+1) ≤ ν_C`.** -/
theorem rgNu_of_caps (h0 : CdCAP0 S) (h1 : CdCAP1 S (Nc.ncL S (ω + 1))) (hpair : RgLwPair S) :
    Nc.ncL S (ω + 1) ≤ nuC := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨l, hl, -, hlν, h2, hR, -, hP, hW, -⟩ := Lb.lbFirst
  have hX : upsilon l < Nc.ncL S (ω + 1) := hlν.trans hlt
  by_cases heq : upsilon l = Nc.ncL S ω
  · rw [heq] at hlν h2 hR
    exact hpair nuC hlν hlt h2 hR
  · exact rgFirst_ne h0 h1 hl hlν hP hW hX heq

/-- **`L(ω+1) ≤ ν_C` gives `RgLwPair`.** -/
theorem rgPair_of_nu (hν : Nc.ncL S (ω + 1) ≤ nuC) : RgLwPair S := by
  intro d hd hdL h2 _
  exact Lw.lw_not_tau_L_omega S (Nc.ncStd_tau (std_of_lt_nuC (hdL.trans_le hν) hd h2))

/-- **`T` gives `RgLwPair`.** -/
theorem rgPair_of_T (hT : Cx.CxT S) : RgLwPair S := by
  intro d _ hdL _ hR
  exact absurd (hR.2 _ hT) (not_le.2 hdL)

/-- **`L(ω) ≤ ν_C` and (P) at `(L(ω), L(ω+1))` give `RgLwPair`.** -/
theorem rgPair_of_P (hlow : Nc.ncL S ω ≤ nuC) (hP : Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1))) :
    RgLwPair S :=
  rgPair_of_nu (Lb.lbLsucc_of_P hlow hP)

/-- **No `L(ω) ≤₂ d` with `d ∈ (L(ω), L(ω+1))` gives `RgLwPair`** (the second clause of
`CvNoPair L(ω) L(ω+1)`). -/
theorem rgPair_of_no2 (h : ∀ d, Nc.ncL S ω < d → d < Nc.ncL S (ω + 1) → ¬ le2 (Nc.ncL S ω) d) :
    RgLwPair S :=
  fun d hd hdL h2 _ => h d hd hdL h2

/-- **CAP-1 below `L(ω+1)`** from CAP-1 below `L(ω)` and CAP at the Range restarts above `L(ω)`. -/
theorem rgCAP1_top (h1 : CdCAP1 S (Nc.ncL S ω))
    (ht : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapAt S l) :
    CdCAP1 S (Nc.ncL S (ω + 1)) := by
  intro l hl hB hlev hlX hcode
  rcases lt_trichotomy (upsilon l) (Nc.ncL S ω) with hlo | heq | hhi
  · exact h1 l hl hB hlev hlo hcode
  · rw [cdCode_Lω heq] at hcode
    exact absurd hcode (not_lt.2 le_self_add)
  · exact ht l ⟨hl, hB, hlX, hcode⟩ hhi

/-- A Range restart above `L(ω)` is not covered by `R2.RzLow`. -/
theorem rgRest_top {l : Ordinal.{0}} (hl : Nc.ncL S ω < upsilon l) : Rz.RzRest l := by
  left
  have hlt : Nc.ncL S ω < l := by
    have h := hl
    rw [← Rc.rcUps_Lw] at h
    exact upsilon_normal.strictMono.lt_iff_lt.1 h
  exact (Ra.raLw_named (S := S)).2.2.2.2.2.le.trans hlt.le

/-- **CAP-0 and CAP-1 below `L(ω+1)`** from UPPER and CapV at the `Rz.RzRest` Range restarts below `L(ω)`
and UPPER (the same hypothesis) and CapV at the Range restarts above `L(ω)`. -/
theorem rgCAP_of_enum (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l) :
    CdCAP0 S ∧ CdCAP1 S (Nc.ncL S (ω + 1)) := by
  have hωL : Nc.ncL S ω ≤ Nc.ncL S (ω + 1) := Pp.ppL_mono le_self_add
  refine ⟨Rz.rzCAP0_of_rest fun l hl hB hlev hrest => ?_, rgCAP1_top
    (Rz.rzCAP1_of_rest fun l hl hB _ hlX hcode hrest => ?_) fun l hr hhi => ?_⟩
  · have hlX : upsilon l < Nc.ncL S ω := hlev.trans_le (cdMstar_le_L S ω)
    have hr : CdRange S l := cdRange_level1 hl hB hlev
    exact cdCapAt_of_upper (hU l hr hrest) (hV l hr hlX hrest)
  · have hr : CdRange S l := ⟨hl, hB, hlX.trans_le hωL, hcode⟩
    exact cdCapAt_of_upper (hU l hr hrest) (hV l hr hlX hrest)
  · exact cdCapAt_of_upper (hU l hr (rgRest_top hhi)) (hVt l hr hhi)

/-- **`L(ω+1) ≤ ν_C`** from UPPER, CapV (below and above `L(ω)`) and `RgLwPair`. -/
theorem rgNu (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l) (hpair : RgLwPair S) :
    Nc.ncL S (ω + 1) ≤ nuC :=
  rgNu_of_caps (rgCAP_of_enum hU hV hVt).1 (rgCAP_of_enum hU hV hVt).2 hpair

/-- **`T` from `L(ω+1) ≤ ν_C`**, the supply at every `L(n+1)`, UPPER/LOWER and `LrGap` at `L(ω)`. -/
theorem rgT_of_nu (hν : Nc.ncL S (ω + 1) ≤ nuC)
    (hsn : ∀ n : ℕ, Ra.RaSupAt S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))
    (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hgap : Lr.LrGap S (Nc.ncL S ω) (Nc.ncL S (ω + 1)) (upsilon (Nc.ncL S ω + Nc.ncL S ω))) :
    Cx.CxT S :=
  Rc.rcT_of_Lw (Cv.cvNoPair_of_nu (Lb.lbL_ri S) Rc.rcUps_Lw.symm hν)
    ((Qq.qqL_lt_succ S).trans_le hν) (Ra.raLw_AA.trans hν) hsn hU hL (Tp.tpStdPairTop hν) hgap

/-- **`T` from `RgLwPair`**, the caps, the supply at every `L(n+1)`, UPPER/LOWER and `LrGap` at `L(ω)`. -/
theorem rgT_of_pair (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l) (hpair : RgLwPair S)
    (hsn : ∀ n : ℕ, Ra.RaSupAt S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))
    (hgap : Lr.LrGap S (Nc.ncL S ω) (Nc.ncL S (ω + 1)) (upsilon (Nc.ncL S ω + Nc.ncL S ω))) :
    Cx.CxT S :=
  rgT_of_nu (rgNu hU hV hVt hpair) hsn hU hL hgap

/-- **`T ⇔ RgLwPair`** under the caps, the supply at every `L(n+1)`, UPPER/LOWER and `LrGap` at `L(ω)`. -/
theorem rgT_iff_pair (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hsn : ∀ n : ℕ, Ra.RaSupAt S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))
    (hgap : Lr.LrGap S (Nc.ncL S ω) (Nc.ncL S (ω + 1)) (upsilon (Nc.ncL S ω + Nc.ncL S ω))) :
    Cx.CxT S ↔ RgLwPair S :=
  ⟨rgPair_of_T, fun hp => rgT_of_pair hU hL hV hVt hp hsn hgap⟩

/-- **`L(ω+1) ≤ ν_C ⇔ RgLwPair`** under UPPER and CapV (below and above `L(ω)`). -/
theorem rgNu_iff_pair (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l) :
    Nc.ncL S (ω + 1) ≤ nuC ↔ RgLwPair S :=
  ⟨rgPair_of_nu, rgNu hU hV hVt⟩

/-- **The road with `RgLwPair` and CapV above `L(ω)`** in place of `CvNoPair L(ω) L(ω+1)`, `L(ω) < ν_C`,
`υ_{L(ω)+L(ω)} ≤ ν_C`, `CxStdPairTop` and `CxUpsRestTop` (`Rc.rcRoad_Lw`). -/
theorem rgRoad (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S)
    (hs0 : Ra.RaSupAt S (Nc.ncL S 0))
    (hsn : ∀ n : ℕ, Ra.RaSupAt S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))
    (h0 : Lr.LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Nc.ncL S 0)))
    (hn : ∀ n : ℕ, Lr.LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
    (hpair : RgLwPair S)
    (hgap : Lr.LrGap S (Nc.ncL S ω) (Nc.ncL S (ω + 1)) (upsilon (Nc.ncL S ω + Nc.ncL S ω)))
    (hmove : Cx.CxStdMoveTop S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hν := rgNu hU hV hVt hpair
  have hlow : Nc.ncL S ω ≤ nuC := (Qq.qqL_lt_succ S).le.trans hν
  exact Rc.rcRoad_Lw hU hO hL hV hEQ htop (Tp.tpUpsRestTop hlow) hs0 hsn h0 hn
    (Cv.cvNoPair_of_nu (Lb.lbL_ri S) Rc.rcUps_Lw.symm hν) ((Qq.qqL_lt_succ S).trans_le hν)
    (Ra.raLw_AA.trans hν) hgap hmove (Tp.tpStdPairTop hν)

end Googology.Trans.PoR.InaccPsi.R2.Rg

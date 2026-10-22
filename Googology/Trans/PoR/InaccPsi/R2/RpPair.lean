import Googology.Trans.PoR.InaccPsi.R2.RgCov

/-!
# `RgLwPair` from the reaches of the restarts `L(n)` only

`L(ξ) = Nc.ncL S ξ`, `P' = Nc.ncPp S`, `ν_C` the right end of the first non-standard `<₂`-pair, `lh(a) = d` is
`IsReach R2C a d`, CAP-0, CAP-1 as in `Cd.CdCAP0`, `Cd.CdCAP1`, `Rg.RgLwPair S`: no `d ∈ (L(ω), L(ω+1))` with
`L(ω) ≤₂ d` and `lh(L(ω)) = d`.

* `rpNoPred` (**a `≤₁`-predecessor `y ∈ (L(ω), d]` of a `≤₂`-successor `d` of `L(ω)` is `≥ ν_C`**: [C09]
  Lemma 5.5 (6) gives `L(ω) ≤₂ y`, and below `ν_C` that pair would be standard, so `L(ω)` would be a `τ`-point);
* `rpBad_nu` (**the shape of a counterexample**, given CAP-0 and CAP-1 below `L(ω+1)`): a `d` violating
  `RgLwPair` is `ν_C`, has no `≤₁`-predecessor in `(L(ω), ν_C)`, and the `≤₁`-predecessors of `ν_C` below
  `L(ω)` are cofinal there and are restarts of reach `ν_C` (`Lb.lbFirst`, `Rg.rgFirst_ne`);
* `rpPred_L` (**such a predecessor above `m*` is one of the `L(n)`**: a Range restart in the window
  `(Ω_ω, Ω_ω + P'·ω)` of names has its cap `≤ L(ω) < ν_C`, so the only restarts left are the names `Ω_ω + P'·n`,
  whose code is `P'`, outside the range of CAP-1);
* `RpLnOut S` (**the reaches of the `L(n)`**: if `ν_C < L(ω+1)` with all the properties of `rpBad_nu`, then
  from some `N` on no `L(n)` has reach exactly `ν_C`), `rpPair_of_out` (**CAP-0, CAP-1 and `RpLnOut` give
  `RgLwPair`**), `rpOut_of_pair` (the converse, without caps), `rpPair_iff_out`, `rpOut_of_le1` (**`L(n) ≤₁ L(ω+1)`
  from some `N` on gives `RpLnOut`**);
* `rpNu` (`L(ω+1) ≤ ν_C` from UPPER, CapV and `RpLnOut`), `rpRoad` (**the road `Rg.rgRoad` with `RpLnOut` in
  place of `RgLwPair`**).

So under the caps `RgLwPair` asks nothing at `L(ω)`: only that the reaches of the restarts `L(n)` (code `P'`,
outside ENUM-REACH) are not eventually one common value `ν_C < L(ω+1)`.

No new axiom.  New definition (hypothesis name only): `RpLnOut`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **A `≤₁`-predecessor `y ∈ (L(ω), d]` of a `≤₂`-successor `d` of `L(ω)` is not below `ν_C`.** -/
theorem rpNoPred {d y : Ordinal.{0}} (h2 : le2 (Nc.ncL S ω) d) (hy : Nc.ncL S ω < y) (hyd : y ≤ d)
    (hy1 : le1 y d) (hyν : y < nuC) : False :=
  Lw.lw_not_tau_L_omega S (Nc.ncStd_tau (std_of_lt_nuC hyν hy (le2_of_le1 hy.le hyd h2 hy1)))

/-- **The shape of a counterexample to `RgLwPair`** (given CAP-0 and CAP-1 below `L(ω+1)`). -/
theorem rpBad_nu (h0 : CdCAP0 S) (h1 : CdCAP1 S (Nc.ncL S (ω + 1))) {d : Ordinal.{0}}
    (hd : Nc.ncL S ω < d) (hdL : d < Nc.ncL S (ω + 1)) (h2 : le2 (Nc.ncL S ω) d)
    (hR : IsReach R2C (Nc.ncL S ω) d) :
    d = nuC ∧ (∀ y, Nc.ncL S ω < y → y < nuC → ¬ le1 y nuC) ∧ Nc.NcCofPred (Nc.ncL S ω) nuC ∧
      (∀ y < Nc.ncL S ω, le1 y nuC → ∃ μ, IsRestartIdx μ ∧ VzLam + ω * ω ≤ μ ∧ y = upsilon μ ∧
        IsReach R2C (upsilon μ) nuC) := by
  have hνd : nuC ≤ d := by
    by_contra h
    push Not at h
    exact Lw.lw_not_tau_L_omega S (Nc.ncStd_tau (std_of_lt_nuC h hd h2))
  obtain ⟨l, hl, -, hlν, -, hRl, -, hP, hW, -⟩ := Lb.lbFirst
  have hX : upsilon l < Nc.ncL S (ω + 1) := hlν.trans_le (hνd.trans hdL.le)
  have heq : upsilon l = Nc.ncL S ω := by
    by_contra hne
    exact Rg.rgFirst_ne h0 h1 hl hlν hP hW hX hne
  rw [heq] at hRl hP hW
  have hdν : d = nuC := le_antisymm (hRl.2 _ hR.1) (hR.2 _ hRl.1)
  subst hdν
  exact ⟨rfl, fun y hy hyν hy1 => rpNoPred h2 hy hyν.le hy1 hyν, hP, hW⟩

/-- `ω^{P'+1} ∣ Ω_ω`. -/
theorem rpDvd_Om (S : InaccSeq.{0}) : ω ^ (Nc.ncPp S + 1) ∣ Om ω := by
  have hSC : SC (Om (ω : Ordinal.{0})) := SC_Om omega0_ne_zero
  have hOw : ω ^ Om (ω : Ordinal.{0}) = Om ω := Low.opow_eq_self_of_SC hSC
  have hPO : Nc.ncPp S + 1 ≤ Om ω := (hSC.add_one_lt (cdPp_lt_Om_omega S)).le
  rw [← hOw]; exact opow_dvd_opow ω hPO

/-- `L(n) < L(ω)` for every `n : ℕ`. -/
theorem rpL_lt (n : ℕ) : Nc.ncL S (n : Ordinal.{0}) < Nc.ncL S ω :=
  (Pp.ppL_mono (by exact_mod_cast Nat.le_succ n)).trans_lt (Pp.ppL_lt_omega n)

/-- **A restart of reach `ν_C > L(ω)` between `m*` and `L(ω)` is one of the `L(n)`** (given CAP-1 below
`L(ω+1)`). -/
theorem rpPred_L (h1 : CdCAP1 S (Nc.ncL S (ω + 1))) {μ : Ordinal.{0}} (hμ : IsRestartIdx μ)
    (hBμ : VzLam + ω * ω ≤ μ) (hlev : cdMstar S < upsilon μ) (hω : upsilon μ < Nc.ncL S ω)
    (hν : Nc.ncL S ω < nuC) (hR : IsReach R2C (upsilon μ) nuC) :
    ∃ n : ℕ, upsilon μ = Nc.ncL S (n : Ordinal.{0}) := by
  have hL0 : Nc.ncL S ω = Pv S (Om ω + Nc.ncPp S * ω) := Lw.lw_L_eq S ω
  obtain ⟨hg, -, hhi, hpv⟩ := cdEta_pv_spec (S := S) (η0 := Om ω + Nc.ncPp S * ω) hμ.1 (hL0 ▸ hω)
  set η := cdEta S μ with hηdef
  have hlo : Om ω < η := by
    by_contra h
    push Not at h
    have h' := Pv_mono (S := S) h
    rw [hpv] at h'
    exact absurd (hlev.trans_le h') (lt_irrefl _)
  obtain ⟨hPw, -⟩ := Rg.rgC_dvd S
  have hhi' : η < Om ω + ω ^ (Nc.ncPp S + 1) := by rw [← hPw]; exact hhi
  obtain ⟨hexp, hwin⟩ := cdWin (rpDvd_Om S) hlo hhi'
  have hη0 : η ≠ 0 := (lt_of_le_of_lt zero_le hlo).ne'
  rcases lt_or_eq_of_le (Order.lt_add_one_iff.1 hexp) with hlt | heq
  · exfalso
    have hcode : cdCode S μ < Nc.ncPp S := by
      show cdCodeOf S η < Nc.ncPp S
      rw [cdCodeOf_of_lt (hlt.trans (cdPp_lt_Om2 S))]
      exact (cdOff_le _).trans_lt hlt
    have hcap := h1 μ hμ hBμ hlev.le (hω.trans (Qq.qqL_lt_succ S)) hcode nuC hR.1
    have hcapL : cdCapB S μ ≤ Nc.ncL S ω := by
      unfold cdCapB
      rw [hL0, hPw]
      exact Pv_mono hwin.le
    exact absurd (hcap.trans_le hcapL) (not_lt.2 hν.le)
  · have hdv : ω ^ Nc.ncPp S ∣ η := heq ▸ cdExp_dvd hη0
    obtain ⟨z, hz⟩ := exists_add_of_le hlo.le
    have hdO : ω ^ Nc.ncPp S ∣ Om ω :=
      (opow_dvd_opow ω (le_self_add : Nc.ncPp S ≤ Nc.ncPp S + 1)).trans (rpDvd_Om S)
    have hdz : ω ^ Nc.ncPp S ∣ z := (Ordinal.dvd_add_iff hdO).1 (hz ▸ hdv)
    obtain ⟨q, hq⟩ := hdz
    rw [Lw.lw_Pp_opow] at hq
    have hzlt : z < Nc.ncPp S * ω := by
      have := hhi; rw [hz] at this; exact (add_lt_add_iff_left _).1 this
    have hqω : q < ω := by
      rw [hq] at hzlt
      exact (mul_lt_mul_iff_right₀ (Nc.ncPp_SC S).1).1 hzlt
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.1 hqω
    refine ⟨n, ?_⟩
    rw [← hpv, Lw.lw_L_eq, hz, hq]

/-- **The reaches of the `L(n)`**: if `ν_C < L(ω+1)` is a `≤₂`-successor of `L(ω)` with `lh(L(ω)) = ν_C` and no
`≤₁`-predecessor in `(L(ω), ν_C)`, then from some `N` on no `L(n)` has reach exactly `ν_C`. -/
def RpLnOut (S : InaccSeq.{0}) : Prop :=
  nuC < Nc.ncL S (ω + 1) → Nc.ncL S ω < nuC → le2 (Nc.ncL S ω) nuC → IsReach R2C (Nc.ncL S ω) nuC →
    (∀ y, Nc.ncL S ω < y → y < nuC → ¬ le1 y nuC) →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ¬ IsReach R2C (Nc.ncL S (n : Ordinal.{0})) nuC

/-- **CAP-0, CAP-1 below `L(ω+1)` and `RpLnOut` give `RgLwPair`.** -/
theorem rpPair_of_out (h0 : CdCAP0 S) (h1 : CdCAP1 S (Nc.ncL S (ω + 1))) (hout : RpLnOut S) :
    Rg.RgLwPair S := by
  intro d hd hdL h2 hR
  obtain ⟨rfl, hnp, hP, hW⟩ := rpBad_nu h0 h1 hd hdL h2 hR
  obtain ⟨N, hN⟩ := hout hdL hd h2 hR hnp
  have hm : cdMstar S ≤ Nc.ncL S (N : Ordinal.{0}) := cdMstar_le_L S _
  obtain ⟨y, hNy, hyL, hy1⟩ := hP _ (rpL_lt N)
  obtain ⟨μ, hμ, hBμ, rfl, hRμ⟩ := hW _ hyL hy1
  obtain ⟨n, hn⟩ := rpPred_L h1 hμ hBμ (hm.trans_lt hNy) hyL hd hRμ
  have hNn : N ≤ n := by
    by_contra h
    push Not at h
    have h' : Nc.ncL S (n : Ordinal.{0}) ≤ Nc.ncL S (N : Ordinal.{0}) :=
      Pp.ppL_mono (by exact_mod_cast h.le)
    rw [← hn] at h'
    exact absurd (hNy.trans_le h') (lt_irrefl _)
  exact hN n hNn (hn ▸ hRμ)

/-- **`RgLwPair` gives `RpLnOut`** (no caps needed). -/
theorem rpOut_of_pair (hp : Rg.RgLwPair S) : RpLnOut S :=
  fun hνL hLν h2 hR _ => (hp nuC hLν hνL h2 hR).elim

/-- **Under CAP-0 and CAP-1 below `L(ω+1)`: `RgLwPair ⇔ RpLnOut`.** -/
theorem rpPair_iff_out (h0 : CdCAP0 S) (h1 : CdCAP1 S (Nc.ncL S (ω + 1))) :
    Rg.RgLwPair S ↔ RpLnOut S :=
  ⟨rpOut_of_pair, rpPair_of_out h0 h1⟩

/-- **`L(n) ≤₁ L(ω+1)` from some `N` on gives `RpLnOut`.** -/
theorem rpOut_of_le1 (h : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → le1 (Nc.ncL S (n : Ordinal.{0})) (Nc.ncL S (ω + 1))) :
    RpLnOut S := by
  intro hνL _ _ _ _
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun n hn hR => absurd (hR.2 _ (hN n hn)) (not_le.2 hνL)⟩

/-- **`L(ω+1) ≤ ν_C`** from UPPER, CapV (below and above `L(ω)`) and `RpLnOut`. -/
theorem rpNu (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l) (hout : RpLnOut S) :
    Nc.ncL S (ω + 1) ≤ nuC :=
  Rg.rgNu hU hV hVt (rpPair_of_out (Rg.rgCAP_of_enum hU hV hVt).1 (Rg.rgCAP_of_enum hU hV hVt).2 hout)

/-- **The road `Rg.rgRoad` with `RpLnOut` in place of `RgLwPair`.** -/
theorem rpRoad (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
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
    (hout : RpLnOut S)
    (hgap : Lr.LrGap S (Nc.ncL S ω) (Nc.ncL S (ω + 1)) (upsilon (Nc.ncL S ω + Nc.ncL S ω)))
    (hmove : Cx.CxStdMoveTop S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  Rg.rgRoad hU hO hL hV hVt hEQ htop hs0 hsn h0 hn
    (rpPair_of_out (Rg.rgCAP_of_enum hU hV hVt).1 (Rg.rgCAP_of_enum hU hV hVt).2 hout) hgap hmove

end Googology.Trans.PoR.InaccPsi.R2.Rp

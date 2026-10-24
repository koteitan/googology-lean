import Googology.Trans.PoR.InaccPsi.R2.RtPi
import Googology.Trans.PoR.InaccPsi.R2.GeLoc

/-!
# The bound `U_E = P(Γ_{Ω₁+Ω₁^ω})`, and (TC) at every restart left end from CapV, (CL) and `T`

`L(ξ) = Nc.ncL S ξ`, `c_n = L(n+1) = Bc.bcC S n`, `B_n = Bc.bcB S n`, `Γ_{Ω₁·2+1} = Gd.gdV`, `Γ_{Ω₁+Ω₁^ω} = Ge.geV`,
`U_D = P(Γ_{Ω₁·2+1})` (the bound of `Rt.rtD_low`), `U_E = υ(sup_k Λ⁺(geX Ω₁^{k+1})) = P(Γ_{Ω₁+Ω₁^ω})` (`Ge.geFam_sup`),
`P' = Nc.ncPp S`, `m_λ = Cd.cdCode S λ` (the code of the restart `ρ_λ = υ_λ`).

* `seE_low` (**every point below `U_E = P(Γ_{Ω₁+Ω₁^ω})` has an `R₂^C`-reach below `L(0)`**: `Rb.rbFam_low` on
  `Ge.geFam`), `seE_gt` (`U_D < U_E`), `seE_lt_c` (`U_E < L(n+1)`);
* `seE_UPPER`, `seE_LOWER`, `seE_capV`, `seE_nu` (UPPER, LOWER, CapV and `L(ω) ≤ ν_C` from their parts at
  `λ ≥ ι(Γ_{Ω₁+Ω₁^ω})`, with ENUM-REACH and CapV below `ι(Γ_{Ω₁+Ω₁^ω})`, `Ge.geFam_enum`, `Ge.geFam_capV`);
* `seTC_below` (**(TC) at every `x < L(n+1)` from (CL) and `T` alone**: a reach below `L(n+1)`, or `x ≤₁ L(n+1) ≤₁
  L(ω) ≤₁ L(ω+1)`), `seR_lt_c` (**CapV: a range restart `ρ_λ < L(n+2)` has `r(λ) < L(n+2)`**);
* `seCode_mid` (**every restart strictly between `L(n+1)` and `L(n+2)` has code `< P'`**), `seRange_mid` (**so it is a
  restart of the range**);
* `seTCRstHi` (**CapV, (CL) and `T` give `Rt.RtTCRstHi S U` for every `U`**: the left ends it asks for do not exist
  above `L(n+1)`, and below `L(n+1)` `seTC_below` applies), `seTC_rst` (**(TC) at every restart left end below
  `L(n+2)`** from UPPER, LOWER, EQ, CapV, (CL), `T`);
* `seRoadE_nuHi` (**the road with UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ_{Ω₁+Ω₁^ω})`, EQ, `L(ω+1) ≤ ν_C`,
  `Rk.RkLhTopE`, `T`, (CL), and no (TC) hypothesis left**), `seRoadE_nuPi` (the same with `Rt.RtPiComm`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Se

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm

variable {S : InaccSeq.{0}}

/-! ## The bound `U_E = P(Γ_{Ω₁+Ω₁^ω})` -/

/-- **Every point below `U_E = P(Γ_{Ω₁+Ω₁^ω})` has an `R₂^C`-reach below `L(0)`**, unconditionally. -/
theorem seE_low : Tq.TqLow S (Pv S Ge.geV) := by
  have h := Rb.rbFam_low (S := S) (Ge.geFam S) (by rw [(Ge.geFam_sup S).2.1]; exact (Ge.geFam_sup S).2.2.le)
  rwa [(Ge.geFam_sup S).2.1] at h

/-- **`U_D < U_E`**: the new bound `P(Γ_{Ω₁+Ω₁^ω})` lies above the bound `P(Γ_{Ω₁·2+1})` of `Rt.rtD_low`. -/
theorem seE_gt (S : InaccSeq.{0}) : Pv S Gd.gdV < Pv S Ge.geV := by
  have hO1 : Om1 + 1 < Ge.geW := Ge.Om1_succ_lt_W
  have hgO1 : Ge.gate (Om1 + 1) < ε₀ := by
    refine (Ge.sb_succ hO1 0).2.2.trans_lt ?_
    rw [(Ge.sb_Om1 0).2]
    exact_mod_cast natCast_lt_epsilon 2 0
  obtain ⟨h1, h2, -, -, -⟩ := Ge.ge_fr_order hO1 hgO1 S le_rfl
  have := upsilon_normal.strictMono (h1.trans h2)
  rwa [ups_iota S, ups_iota S] at this

/-- `U_E < L(n+1)` for every `n`. -/
theorem seE_lt_c (n : ℕ) : Pv S Ge.geV < Bc.bcC S n :=
  (Ge.geFam_sup S).2.2.trans_le (Ph.phL_chain (S := S) n).1

/-- **UPPER everywhere** from UPPER at `λ ≥ ι(Γ_{Ω₁+Ω₁^ω})`. -/
theorem seE_UPPER (hU : ∀ l, CdRange S l → iota S Ge.geV ≤ l → CdUpper S l) : CdUPPER S := fun l hr => by
  rcases lt_or_ge l (iota S Ge.geV) with h | h
  · exact (Ge.geFam_enum S hr h).1
  · exact hU l hr h

/-- **LOWER everywhere** from LOWER at `λ ≥ ι(Γ_{Ω₁+Ω₁^ω})`. -/
theorem seE_LOWER (hL : ∀ l, CdRange S l → iota S Ge.geV ≤ l → CdLower S l) : CdLOWER S := fun l hr => by
  rcases lt_or_ge l (iota S Ge.geV) with h | h
  · exact (Ge.geFam_enum S hr h).2
  · exact hL l hr h

/-- **The cap of the values everywhere** from the cap at `λ ≥ ι(Γ_{Ω₁+Ω₁^ω})`. -/
theorem seE_capV (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S Ge.geV ≤ l → CdCapV S l) :
    ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CdCapV S l := fun l hr hX => by
  rcases lt_or_ge l (iota S Ge.geV) with h | h
  · exact Ge.geFam_capV S hr h
  · exact hV l hr hX h

/-- **`L(ω) ≤ ν_C`** from UPPER and the cap of the values at `λ ≥ ι(Γ_{Ω₁+Ω₁^ω})`. -/
theorem seE_nu (hU : ∀ l, CdRange S l → iota S Ge.geV ≤ l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S Ge.geV ≤ l → CdCapV S l) :
    Nc.ncL S ω ≤ nuC :=
  cdLow_enum (seE_UPPER hU) (seE_capV hV)

/-! ## (TC) below `L(n+1)` and at the range restarts -/

/-- **(TC) at every `x < L(n+1)` from (CL) and `T`**: either `x` has a reach below `L(n+1)` (then `B_n` fixes both),
or `x ≤₁ L(n+1)`, and then `x ≤₁ L(n+1) ≤₁ L(ω) ≤₁ L(ω+1)`. -/
theorem seTC_below (hT : Cx.CxT S) (hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) {n : ℕ}
    {x : Ordinal.{0}} (hx : x < Bc.bcC S n) : CdTCAt S n x := by
  by_cases h : le1 x (Bc.bcC S n)
  · have hC : CdCL S := fun j => hcl j
    have h1 : le1 (Bc.bcC S n) (Nc.ncL S ω) := cdL_le1_omega hC n
    exact Cx.cxTCAt_of_le1 hx (le1_trans (le1_trans h h1) hT)
  · have hR := reach_spec hx.le h
    have hlt : reach x < Bc.bcC S n := by
      by_contra hge
      exact h (le1_of_le_of_le1 hx.le (not_lt.1 hge) hR.1)
    exact cdTCAt_low hR hlt

/-- **CapV: a range restart `ρ_λ < L(n+2)` has its predicted reach `r(λ) < L(n+2)`.** -/
theorem seR_lt_c (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CdCapV S l) {n : ℕ} {l : Ordinal.{0}}
    (hl : CdRange S l) (hlt : upsilon l < Bc.bcC S (n + 1)) : cdR S l < Bc.bcC S (n + 1) :=
  Cx.cxR_lt_of_below hl (hV l hl (hlt.trans (Bc.bcC_lt S (n + 1)))) (n + 1) hlt

/-- **Every restart strictly between `L(n+1)` and `L(n+2)` has code `< P'`**: its name `η_λ` (`P(η_λ) = ρ_λ`) lies
in `(η_{n+1}, η_{n+1} + P')`, `η_{n+1} = Ω_ω + P'·(n+1)`, `ω^{P'} = P' ∣ η_{n+1}`, so its last exponent is `< P'`
(`Cd.cdWin`), and the code is at most the last exponent. -/
theorem seCode_mid {n : ℕ} {l : Ordinal.{0}} (hl0 : l ≠ 0) (h1 : Bc.bcC S n < upsilon l)
    (h2 : upsilon l < Bc.bcC S (n + 1)) : cdCode S l < Nc.ncPp S := by
  have hPE : ω ^ Nc.ncPp S = Nc.ncPp S := Lw.lw_Pp_opow S
  have hWE : ω ^ Om ω = Om ω := Low.opow_eq_self_of_SC (SC_Om omega0_ne_zero)
  have hc1 : Bc.bcC S n = Pv S (Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0})) := Lw.lw_L_eq S _
  have hc2 : Bc.bcC S (n + 1) = Pv S (Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncPp S) := by
    show Nc.ncL S ((n + 1 + 1 : ℕ) : Ordinal.{0}) = _
    rw [Lw.lw_L_eq S, Nat.cast_succ (n + 1), mul_add_one, add_assoc]
  obtain ⟨hg, hι, hlt, hpv⟩ := cdEta_pv_spec hl0 (h2.trans_eq hc2)
  have hgt : Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) < cdEta S l := by
    by_contra hle
    push Not at hle
    rcases hle.lt_or_eq with h | h
    · have h3 := upsilon_normal.strictMono (cd_iota_lt_of_good hg h)
      rw [hι, ups_iota S] at h3
      exact absurd (h3.trans_eq hc1.symm) (not_lt.2 h1.le)
    · rw [h, ← hc1] at hpv
      exact absurd hpv (ne_of_lt h1)
  have hdvd : ω ^ Nc.ncPp S ∣ Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) := by
    refine dvd_add ?_ ?_
    · conv_rhs => rw [← hWE]
      exact opow_dvd_opow ω (cdPp_lt_Om_omega S).le
    · rw [hPE]; exact dvd_mul_right _ _
  have hlt' : cdEta S l < Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) + ω ^ Nc.ncPp S := by
    rw [hPE]; exact hlt
  exact (cdCodeOf_le_exp S _).trans_lt (cdWin hdvd hgt hlt').1

/-- **Every restart strictly between `L(n+1)` and `L(n+2)` is a restart of the range** (code `< P'`, above `B₀`,
below `L(ω+1)`). -/
theorem seRange_mid {n : ℕ} {l : Ordinal.{0}} (hl : IsRestartIdx l) (h1 : Bc.bcC S n < upsilon l)
    (h2 : upsilon l < Bc.bcC S (n + 1)) : CdRange S l := by
  have hB0 : cdB0 ≤ l := by
    by_contra hB
    push Not at hB
    have h3 : upsilon l < upsilon cdB0 := upsilon_normal.strictMono hB
    have h4 : upsilon cdB0 < Bc.bcC S n := (Fp.fpB0_lt_M (S := S)).trans_le (Ph.phL_chain (S := S) n).1
    exact absurd (h3.trans h4) (not_lt.2 h1.le)
  exact ⟨hl, hB0, h2.trans (Cx.cxC_lt_L1 n), seCode_mid hl.1 h1 h2⟩

/-- **CapV, (CL) and `T` give `Rt.RtTCRstHi S U`, for every `U`**: below `L(n+1)` by `seTC_below`; `x = L(n+1)` is
excluded; above `L(n+1)` every restart is a range restart (`seRange_mid`) with `r(λ) < L(n+2)` (CapV), excluded too. -/
theorem seTCRstHi (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CdCapV S l) (hT : Cx.CxT S)
    (hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) (U : Ordinal.{0}) : Rt.RtTCRstHi S U := by
  intro n x hx _ _ hrst hR hN
  rcases lt_trichotomy x (Bc.bcC S n) with hlt | heq | hgt
  · exact seTC_below hT hcl hlt
  · exact absurd heq (hN n le_rfl)
  · obtain ⟨l, hl, rfl⟩ := hrst
    have hr : CdRange S l := seRange_mid hl hgt hx
    exact absurd ⟨l, hr, rfl, seR_lt_c hV hr hx⟩ hR

/-- **(TC) at every restart left end `x < L(n+2)`**, from UPPER, LOWER, EQ, CapV, (CL) and `T`. -/
theorem seTC_rst (hU : CdUPPER S) (hL : CdLOWER S) (hEQ : CdEQ S)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CdCapV S l) (hT : Cx.CxT S)
    (hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) {n : ℕ} {x : Ordinal.{0}}
    (hx : x < Bc.bcC S (n + 1)) (hrst : ∃ l, IsRestartIdx l ∧ x = upsilon l) : CdTCAt S n x := by
  by_cases hr : ∃ r < Bc.bcC S n, IsReach R2C x r
  · obtain ⟨r, hrn, hR⟩ := hr
    exact cdTCAt_low hR hrn
  · exact Rt.rtTCRst_of_hi hU hL hEQ hT hcl (seTCRstHi hV hT hcl 0) n x hx zero_le hr hrst

/-! ## The roads -/

/-- **The road with UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ_{Ω₁+Ω₁^ω})`, EQ, `L(ω+1) ≤ ν_C`, `Rk.RkLhTopE`, `T`,
(CL), and no (TC) hypothesis** (the restart left ends by `seTCRstHi`). -/
theorem seRoadE_nuHi (hU : ∀ l, CdRange S l → iota S Ge.geV ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S Ge.geV ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S Ge.geV ≤ l → CdCapV S l)
    (hEQ : CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC) (htop : Rk.RkLhTopE S)
    (hT : Cx.CxT S) (hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hV' := seE_capV hV
  have hrst : Rk.RkTCRstOnly S (Pv S Ge.geV) :=
    Rt.rtTCRst_of_hi (seE_UPPER hU) (seE_LOWER hL) hEQ hT hcl (seTCRstHi hV' hT hcl _)
  have hrstD : Rk.RkTCRstOnly S (Pv S Gd.gdV) := by
    intro n x hx hxU hr hR
    rcases lt_or_ge x (Pv S Ge.geV) with hlow | hhigh
    · obtain ⟨r, hr', hRr⟩ := seE_low x hlow
      exact absurd ⟨r, hr'.trans_le (Ph.phL_chain (S := S) n).1, hRr⟩ hr
    · exact hrst n x hx hhigh hr hR
  have hUD : ∀ l, CdRange S l → iota S Gd.gdV ≤ l → CdUpper S l := fun l hr _ => seE_UPPER hU l hr
  have hLD : ∀ l, CdRange S l → iota S Gd.gdV ≤ l → CdLower S l := fun l hr _ => seE_LOWER hL l hr
  have hVD : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S Gd.gdV ≤ l → CdCapV S l :=
    fun l hr hX _ => hV' l hr hX
  exact Rt.rtRoadD_nuE hUD hLD hVD hEQ hν htop hT hrstD hcl

/-- **The road `seRoadE_nuHi` with `Rt.RtPiComm` in place of `Rk.RkLhTopE`.** -/
theorem seRoadE_nuPi (hU : ∀ l, CdRange S l → iota S Ge.geV ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S Ge.geV ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S Ge.geV ≤ l → CdCapV S l)
    (hEQ : CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC) (hpi : Rt.RtPiComm S)
    (hT : Cx.CxT S) (hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  seRoadE_nuHi hU hL hV hEQ hν (Rt.rtLhTopE hpi) hT hcl

end Googology.Trans.PoR.InaccPsi.R2.Se

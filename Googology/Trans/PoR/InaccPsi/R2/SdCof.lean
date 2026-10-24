import Googology.Trans.PoR.InaccPsi.R2.SdNu

/-!
# The closure route to `T` and the cap at `ν_C`: what a `≤₁`-witness into `L(ω+1)` already decides

`L(ξ) = Nc.ncL S ξ`, `T`: `L(ω) ≤₁ L(ω+1)`.  [C09] Lemma 5.7 (3) (`le1_of_cof_left`): `≤₁`-predecessors of
`L(ω+1)` cofinal below `L(ω)` give `T`.  But `R2.nuC_cap` (no `α ≤ ν_C` has a `≤₁`-successor above `ν_C`)
makes every such witness as strong as the goal:

* `sdT_of_cof` (**`T` from `L(n+1) ≤₁ L(ω+1)` for cofinally many `n`**), `sdCof_of_T` (with (CL), the converse:
  `T` gives `L(n+1) ≤₁ L(ω+1)` for every `n`);
* `sdCap_route` (**any `x ≤ ν_C` with `x ≤₁ L(ω+1)` gives `L(ω+1) ≤ ν_C`**), `sdCof_nu` (with `L(ω) ≤ ν_C`, one
  `n` with `L(n+1) ≤₁ L(ω+1)` gives `L(ω+1) ≤ ν_C`), `sdT_nu` (with `L(ω) ≤ ν_C`, `T` gives `L(ω+1) ≤ ν_C`,
  without any cap hypothesis);
* `sdRoadT` (**the road `Rx.rxRoadRa` without `CxUpsRestTop`**), `sdRoadT2` (**with `T`, also without
  `CxStdPairTop`**), `sdT_iff_nu2` (**`T ⇔ L(ω+1) ≤ ν_C` without a cap above `L(ω)` and without `LrGap` at
  `L(ω)`**), `sdRoadNu` (**the road from `L(ω+1) ≤ ν_C` in place of `T`**).

No new axiom, no new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **`T` from `L(n+1) ≤₁ L(ω+1)` for cofinally many `n`** ([C09] Lemma 5.7 (3)). -/
theorem sdT_of_cof
    (h : ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧ le1 (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1))) :
    Cx.CxT S := by
  refine le1_of_cof_left (Qq.qqL_lt_succ S).le (Lb.lbL_pos S) fun x hx => ?_
  obtain ⟨k, hk⟩ := Pp.ppL_cof (S := S) x hx
  obtain ⟨n, hkn, hn⟩ := h k
  refine ⟨_, hk.trans_le (Pp.ppL_mono ?_), (Pp.ppL_lt_omega n).le, hn⟩
  exact_mod_cast Nat.succ_le_succ hkn

/-- **With (CL), `T` gives `L(n+1) ≤₁ L(ω+1)` for every `n`.** -/
theorem sdCof_of_T (hCL : CdCL S) (hT : Cx.CxT S) (n : ℕ) :
    le1 (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  ((Pp.ppP_of_cross hCL hT).2 n).2

/-- **The cap at `ν_C`: any `x ≤ ν_C` with `x ≤₁ L(ω+1)` gives `L(ω+1) ≤ ν_C`.** -/
theorem sdCap_route {x : Ordinal.{0}} (hx : x ≤ nuC) (h : le1 x (Nc.ncL S (ω + 1))) :
    Nc.ncL S (ω + 1) ≤ nuC := by
  by_contra hlt
  exact nuC_cap x hx _ (not_le.1 hlt) h

/-- **With `L(ω) ≤ ν_C`, one `n` with `L(n+1) ≤₁ L(ω+1)` gives `L(ω+1) ≤ ν_C`.** -/
theorem sdCof_nu (hlow : Nc.ncL S ω ≤ nuC) {n : ℕ}
    (h : le1 (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1))) : Nc.ncL S (ω + 1) ≤ nuC :=
  sdCap_route ((Pp.ppL_lt_omega n).le.trans hlow) h

/-- **With `L(ω) ≤ ν_C`, `T` gives `L(ω+1) ≤ ν_C`** (no cap above `L(ω)` asked). -/
theorem sdT_nu (hlow : Nc.ncL S ω ≤ nuC) (hT : Cx.CxT S) : Nc.ncL S (ω + 1) ≤ nuC :=
  sdCap_route hlow hT

/-- **The road `Rx.rxRoadRa` without `CxUpsRestTop`** (it follows from `L(ω) ≤ ν_C`, `Tp.tpUpsRestTop`, and
`L(ω) ≤ ν_C` from UPPER and CapV below `L(ω)`). -/
theorem sdRoadT (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S)
    (h0 : Lr.LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Nc.ncL S 0)))
    (hn : ∀ n : ℕ, Lr.LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
    (hT : Cx.CxT S) (hmove : Cx.CxStdMoveTop S) (hstd : Cx.CxStdPairTop S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hlow : Nc.ncL S ω ≤ nuC :=
    cdLow_enum (Rz.rzUPPER_of_rest hU hO) (Rz.rzCapV_of_rest hV)
  exact Rx.rxRoadRa hU hO hL hV hEQ htop (Tp.tpUpsRestTop hlow) h0 hn hT hmove hstd

/-- **With `T` the road needs neither `CxUpsRestTop` nor `CxStdPairTop`**: `L(ω) ≤ ν_C` from UPPER and CapV
below `L(ω)`, then `L(ω+1) ≤ ν_C` from `T` (`sdT_nu`), and `CxStdPairTop` from it. -/
theorem sdRoadT2 (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S)
    (h0 : Lr.LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Nc.ncL S 0)))
    (hn : ∀ n : ℕ, Lr.LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
    (hT : Cx.CxT S) (hmove : Cx.CxStdMoveTop S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hlow : Nc.ncL S ω ≤ nuC :=
    cdLow_enum (Rz.rzUPPER_of_rest hU hO) (Rz.rzCapV_of_rest hV)
  exact sdRoadT hU hO hL hV hEQ htop h0 hn hT hmove (Tp.tpStdPairTop (sdT_nu hlow hT))

/-- **`T ⇔ L(ω+1) ≤ ν_C`** under UPPER, LOWER, CapV below `L(ω)`, EQ, `CxTCtopOff`, `LrGap` at the `L(n+1)` and
`CxStdMoveTop`: no cap above `L(ω)` and no `LrGap` at `L(ω)`. -/
theorem sdT_iff_nu2 (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S)
    (hn : ∀ n : ℕ, Lr.LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
    (hmove : Cx.CxStdMoveTop S) : Cx.CxT S ↔ Nc.ncL S (ω + 1) ≤ nuC :=
  ⟨sdT_nu (cdLow_enum (Rz.rzUPPER_of_rest hU hO) (Rz.rzCapV_of_rest hV)),
    fun hν => sdT_of_nu_road hν hU hO hL hV hEQ htop hn hmove⟩

/-- **The road with `L(ω+1) ≤ ν_C` in place of `T`** (no `LrGap` at `L(ω)`, no `CxUpsRestTop`,
no `CxStdPairTop`, no cap above `L(ω)`). -/
theorem sdRoadNu (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S)
    (h0 : Lr.LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Nc.ncL S 0)))
    (hn : ∀ n : ℕ, Lr.LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
    (hν : Nc.ncL S (ω + 1) ≤ nuC) (hmove : Cx.CxStdMoveTop S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  sdRoadT2 hU hO hL hV hEQ htop h0 hn (sdT_of_nu_road hν hU hO hL hV hEQ htop hn hmove) hmove

end Googology.Trans.PoR.InaccPsi.R2.Sd

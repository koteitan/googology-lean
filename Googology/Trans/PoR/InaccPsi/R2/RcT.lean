import Googology.Trans.PoR.InaccPsi.R2.RcLow

/-!
# `T: L(ω) ≤₁ L(ω+1)`: the supply at `L(ω)` is free, and the LOWER route is ENUM-REACH at `L(ω)`

* `rcSupAt_Lw_of` (**`RaSupAt` at every `L(n+1)` gives `RaSupAt S L(ω)`**), `rcT_of_Lw`, `rcRoad_Lw`
  (**`Ra.raT_of_Lw` and `Ra.raRoad_Lw` without the hypothesis `RaSupAt S L(ω)`**: the road already asks
  `RaSupAt` at every `L(n+1)`);
* `rcIdx_Lw` (`υ_λ = L(ω)` only at `λ = L(ω)`), `rcLw_closed` (**under `lh(L(ω)) = L(ω+1)` the point
  `L(ω+1)` is closed relative to `L(ω)`**), `rcT_of_count` (**LOWER at `L(ω)` and
  `otp(K_{L(ω)} ∩ L(ω+1)) ≤ Θ_{L(ω)}(P′ + 1)` give `T`**: `Cx.cxT_of_lower` as a count),
  `rcLower_route_iff` (**under `lh(L(ω)) = L(ω+1)` (a conclusion of the road), the hypotheses of
  `Cx.cxT_of_lower` hold iff `Θ_{L(ω)}(P′ + 1) = otp(K_{L(ω)} ∩ L(ω+1))`**: the route asks ENUM-REACH at the
  code `P′ + 1` of `L(ω)`, outside the range `m < P′` of the documents).

No new axiom, no new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rl
  Googology.Trans.PoR.InaccPsi.R2.Cx Googology.Trans.PoR.InaccPsi.R2.Cv
  Googology.Trans.PoR.InaccPsi.R2.Lr Googology.Trans.PoR.InaccPsi.R2.Ls

variable {S : InaccSeq.{0}}

/-- **`RaSupAt` at every `L(n+1)` gives `RaSupAt S L(ω)`.** -/
theorem rcSupAt_Lw_of (hsn : ∀ n : ℕ, Ra.RaSupAt S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))) :
    Ra.RaSupAt S (Nc.ncL S ω) := by
  intro γ hγ
  obtain ⟨n, hn⟩ := Pp.ppL_cof (S := S) γ hγ
  obtain ⟨μ, hR, h1, h2, hd, hs⟩ := hsn n γ hn
  exact ⟨μ, hR, h1, h2.trans (Pp.ppL_lt_omega n), hd, hs⟩

/-- **`T` by the realizer technique at `L(ω)`, with the supply at `L(ω)` taken from the `L(n+1)`.** -/
theorem rcT_of_Lw (hP : CvNoPair (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hν : Nc.ncL S ω < nuC) (hνa : upsilon (Nc.ncL S ω + Nc.ncL S ω) ≤ nuC)
    (hsn : ∀ n : ℕ, Ra.RaSupAt S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))
    (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (hstd : CxStdPairTop S)
    (hgap : LrGap S (Nc.ncL S ω) (Nc.ncL S (ω + 1)) (upsilon (Nc.ncL S ω + Nc.ncL S ω))) : CxT S :=
  Ra.raT_of_Lw hP hν hνa (rcSupAt_Lw_of hsn) hU hL hstd hgap

/-- **The road with `T` from the realizer technique at `L(ω)`, without `RaSupAt S L(ω)`.** -/
theorem rcRoad_Lw (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hEQ : CxEQtop S) (htop : CxTCtopOff S) (hups : CxUpsRestTop S)
    (hs0 : Ra.RaSupAt S (Nc.ncL S 0))
    (hsn : ∀ n : ℕ, Ra.RaSupAt S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))
    (h0 : LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Nc.ncL S 0)))
    (hn : ∀ n : ℕ, LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
    (hP : CvNoPair (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hν : Nc.ncL S ω < nuC) (hνa : upsilon (Nc.ncL S ω + Nc.ncL S ω) ≤ nuC)
    (hgap : LrGap S (Nc.ncL S ω) (Nc.ncL S (ω + 1)) (upsilon (Nc.ncL S ω + Nc.ncL S ω)))
    (hmove : CxStdMoveTop S) (hstd : CxStdPairTop S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  Ra.raRoad_Lw hU hO hL hV hEQ htop hups hs0 hsn (rcSupAt_Lw_of hsn) h0 hn hP hν hνa hgap hmove hstd

/-- `υ_λ = L(ω)` only at `λ = L(ω)`. -/
theorem rcIdx_Lw {l : Ordinal.{0}} (hl : upsilon l = Nc.ncL S ω) : l = Nc.ncL S ω :=
  upsilon_normal.strictMono.injective (hl.trans rcUps_Lw.symm)

/-- **Under `lh(L(ω)) = L(ω+1)`, `L(ω+1)` is closed relative to `L(ω)`.** -/
theorem rcLw_closed (hr : IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1))) :
    Nc.ncL S (ω + 1) ∈ cdK (Nc.ncL S ω) := by
  have hw : ω < Nc.ncL S ω := Lw.lw_omega_lt_SC (Lw.lw_L_SC S ω)
  have hδ : cdDelta (Nc.ncL S ω) ≤ Nc.ncL S (ω + 1) := by
    unfold cdDelta
    refine le_trans (upsilon_normal.strictMono.monotone ?_) Ra.raLw_AA
    rw [add_assoc]
    exact add_le_add le_rfl (Order.add_one_le_of_lt hw)
  have hr' : IsReach R2C (upsilon (Nc.ncL S ω)) (Nc.ncL S (ω + 1)) := by rw [rcUps_Lw]; exact hr
  exact Or.inl (cdClosed_of_reach hr' hδ)

/-- **LOWER at `L(ω)` and `otp(K_{L(ω)} ∩ L(ω+1)) ≤ Θ_{L(ω)}(m_{L(ω)})` give `T`.** -/
theorem rcT_of_count {l : Ordinal.{0}} (hl : upsilon l = Nc.ncL S ω) (hL : CdLower S l)
    (hc : cdOtp (cdK l) (Nc.ncL S (ω + 1)) ≤ cdTheta S l (cdCode S l)) : CxT S :=
  cxT_of_lower hl hL ((rcLe_R_iff S l _).2 hc)

/-- **The LOWER route to `T` is ENUM-REACH at `L(ω)`**: under `lh(L(ω)) = L(ω+1)`, LOWER at `L(ω)` with
`r(L(ω)) ≥ L(ω+1)` (the hypotheses of `Cx.cxT_of_lower`) holds iff
`Θ_{L(ω)}(P′ + 1) = otp(K_{L(ω)} ∩ L(ω+1))`. -/
theorem rcLower_route_iff (hr : IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1))) :
    (CdLower S (Nc.ncL S ω) ∧ Nc.ncL S (ω + 1) ≤ cdR S (Nc.ncL S ω)) ↔
      cdTheta S (Nc.ncL S ω) (Nc.ncPp S + 1) = cdOtp (cdK (Nc.ncL S ω)) (Nc.ncL S (ω + 1)) := by
  have hcode : cdCode S (Nc.ncL S ω) = Nc.ncPp S + 1 := cdCode_Lω rcUps_Lw
  have hK := rcLw_closed hr
  rw [← hcode]
  constructor
  · rintro ⟨hL, hge⟩
    have hL' : le1 (Nc.ncL S ω) (cdR S (Nc.ncL S ω)) := by
      have h : le1 (upsilon (Nc.ncL S ω)) (cdR S (Nc.ncL S ω)) := hL
      rwa [rcUps_Lw] at h
    exact (rcR_eq_iff S hK).1 (le_antisymm (hr.2 _ hL') hge)
  · intro h
    have he := (rcR_eq_iff S hK).2 h
    refine ⟨?_, he.ge⟩
    show le1 (upsilon (Nc.ncL S ω)) (cdR S (Nc.ncL S ω))
    rw [rcUps_Lw, he]
    exact hr.1

end Googology.Trans.PoR.InaccPsi.R2.Rc

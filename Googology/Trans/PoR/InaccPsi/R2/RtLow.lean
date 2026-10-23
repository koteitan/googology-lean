import Googology.Trans.PoR.InaccPsi.R2.RkTop
import Googology.Trans.PoR.InaccPsi.R2.GdDLad

/-!
# (TC) and (EMB₂) below the bound `U_D = P(Γ_{Ω₁·2+1})`, unconditionally; (TC) above it from ENUM-REACH

`L(ξ) = Nc.ncL S ξ`, `c_n = L(n+1)`, `Γ_{Ω₁+ε₀} = Gc.gcV`, `Γ_{Ω₁·2+1} = Gd.gdV`, `U_C = P(Γ_{Ω₁+ε₀})` (the bound of
`Rk.rkTow_low`), `U_D = υ(Λ^{gdDB}) = υ(ι(Γ_{Ω₁·2+1})) = P(Γ_{Ω₁·2+1})` (`Gd.gdDL_fam`: the frontier of the ladder over
the layer of `Γ_{x+x}`).

* `rtD_low` (**every point below `U_D = P(Γ_{Ω₁·2+1})` has an `R₂^C`-reach below `L(0)`**: `Rb.rbFam_low` on the
  family `Lp.lpFam gdDB`, with `U_D < L(0)` from `Gd.gdDL_fam`), `rtD_gt` (`U_C < U_D`);
* `rtD_UPPER`, `rtD_LOWER`, `rtD_capV`, `rtD_nu` (UPPER, LOWER, the cap and `L(ω) ≤ ν_C` from their parts at
  `λ ≥ ι(Γ_{Ω₁·2+1})`, with ENUM-REACH and CapV below `ι(Γ_{Ω₁·2+1})`, `Gd.gdDL_enum`, `Gd.gdDL_capV`);
* `rtRoadD` (TCrest and (EMB₂) asked only at left ends `x ≥ U_D`), `rtRoadD_CL`, `rtRoadD_rst`, `rtRoadD_rst2`,
  `rtRoadD_nuH` (the roads `Rk.rkRoadTow*` with `U_C` replaced by `U_D` and UPPER, LOWER, CapV asked only at
  `λ ≥ ι(Γ_{Ω₁·2+1})`), `rtTCRst2_iff` (given `T`, `Rd.RdTCRst2 S U_D` is (CL) together with
  `Rk.RkTCRstOnly S U_D`), `rtRoadD_nuE` (**(TC) asked only at the restart left ends in `[U_D, L(n+2))`, with
  `Rk.RkLhTopE`, `T`, (CL)**);
* `rtTC_range` (**(TC) at every restart left end `ρ_λ` of the range with `r(λ) < L(n+2)`**, from UPPER, LOWER, EQ),
  `rtTC_named` (**(TC) at the named points `L(k+1)`, `k ≤ n`**, from (CL) and `T`);
* `RtTCRstHi S U` (a hypothesis name: `Rk.RkTCRstOnly S U` without those two kinds of left ends), `rtTCRst_of_hi`
  (**given UPPER, LOWER, EQ, `T`, (CL), `RtTCRstHi S U` gives `Rk.RkTCRstOnly S U`**: the part of (TC) above `U_D`
  that ENUM-REACH, EQ, (CL) and `T` decide), `rtRoadD_nuHi` (**the road asking (TC) only at the other restart
  left ends in `[U_D, L(n+2))` with no reach below `L(n+1)`**).

No new axiom.  New definition: the hypothesis name `RtTCRstHi`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rt

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Tq
  Googology.Trans.PoR.InaccPsi.R2.Rb Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Rd Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Rk

variable {S : InaccSeq.{0}}

/-- **Every point below `U_D = P(Γ_{Ω₁·2+1})` has an `R₂^C`-reach below `L(0)`**, unconditionally. -/
theorem rtD_low : TqLow S (Pv S gdV) := by
  have h := rbFam_low (S := S) (Lp.lpFam gdDB)
    (by rw [(gdDL_fam S).2.1]; exact (gdDL_fam S).2.2.le)
  rwa [(gdDL_fam S).2.1] at h

/-- **`U_C < U_D`**: the new bound `P(Γ_{Ω₁·2+1})` lies above the bound `P(Γ_{Ω₁+ε₀})` of `Rk.rkTow_low`. -/
theorem rtD_gt (S : InaccSeq.{0}) : Pv S Gc.gcV < Pv S gdV := by
  obtain ⟨h1, h2, h3, h4, -, -⟩ := gdDL_order S 0
  have h : iota S Gc.gcV < iota S gdV := h4 ▸ (h1.trans (h2.trans h3))
  have := upsilon_normal.strictMono h
  rwa [ups_iota S, ups_iota S] at this

/-- `λ < ι(Γ_{Ω₁·2+1})` is `λ` below the frontier of `lpFam gdDB`. -/
theorem rtD_lt_fam {l : Ordinal.{0}} (h : l < iota S gdV) : l < (Lp.lpFam gdDB).famSup := by
  rw [(gdDL_fam S).1]; exact h

/-- **UPPER everywhere** from UPPER at `λ ≥ ι(Γ_{Ω₁·2+1})`. -/
theorem rtD_UPPER (hU : ∀ l, CdRange S l → iota S gdV ≤ l → CdUpper S l) : CdUPPER S := fun l hr => by
  rcases lt_or_ge l (iota S gdV) with h | h
  · exact (gdDL_enum S hr (rtD_lt_fam h)).1
  · exact hU l hr h

/-- **LOWER everywhere** from LOWER at `λ ≥ ι(Γ_{Ω₁·2+1})`. -/
theorem rtD_LOWER (hL : ∀ l, CdRange S l → iota S gdV ≤ l → CdLower S l) : CdLOWER S := fun l hr => by
  rcases lt_or_ge l (iota S gdV) with h | h
  · exact (gdDL_enum S hr (rtD_lt_fam h)).2
  · exact hL l hr h

/-- **The cap of the values everywhere** from the cap at `λ ≥ ι(Γ_{Ω₁·2+1})`. -/
theorem rtD_capV (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gdV ≤ l → CdCapV S l) :
    ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CdCapV S l := fun l hr hX => by
  rcases lt_or_ge l (iota S gdV) with h | h
  · exact gdDL_capV S hr (rtD_lt_fam h)
  · exact hV l hr hX h

/-- **`L(ω) ≤ ν_C`** from UPPER and the cap of the values at `λ ≥ ι(Γ_{Ω₁·2+1})`. -/
theorem rtD_nu (hU : ∀ l, CdRange S l → iota S gdV ≤ l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gdV ≤ l → CdCapV S l) :
    Nc.ncL S ω ≤ nuC :=
  cdLow_enum (rtD_UPPER hU) (rtD_capV hV)

/-- **The road `Gd.gdDL_road` with TCrest and (EMB₂) asked only at left ends `x ≥ U_D = P(Γ_{Ω₁·2+1})`.** -/
theorem rtRoadD (hU : ∀ l, CdRange S l → iota S gdV ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S gdV ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gdV ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : TqTCrestUp S (Pv S gdV)) (hB2 : TqEMB2Rest S (Pv S gdV)) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  gdDL_road S hU hL hV hC hEQ (tqTCrest_of rtD_low hrest) (tqEMB2_of rtD_low hB2)

/-- **The road with (TC) and (EMB₂) asked only at left ends `x ≥ U_D` with no reach below `L(n+1)`**, (CL)
derived. -/
theorem rtRoadD_CL (hU : ∀ l, CdRange S l → iota S gdV ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S gdV ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gdV ≤ l → CdCapV S l)
    (hEQ : CdEQ S) (htc : TqTCRest S (Pv S gdV)) (hB2 : TqEMB2Rest S (Pv S gdV)) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hTC : CdTC S := tqTC_of rtD_low htc
  have hE : CdEMB2 S := tqEMB2_of rtD_low hB2
  have hC : CdCL S := Cx.cxCL hTC hE
  exact ⟨hTC, hE, hC, (Cx.cxC1 hTC hE).1, rtRoadD hU hL hV hC hEQ (tqTCrestUp_of htc) hB2⟩

/-- **The road with (TC) and (EMB₂) asked only at the left ends `x ∈ [U_D, L(n+2))` with no reach below `L(n+1)`
that are restart points or lie in `[L(n+1), L(n+2))`**, (CL) derived. -/
theorem rtRoadD_rst (hU : ∀ l, CdRange S l → iota S gdV ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S gdV ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gdV ≤ l → CdCapV S l)
    (hEQ : CdEQ S) (htc : RbTCRst S (Pv S gdV)) (hB2 : RbEMB2Rst S (Pv S gdV)) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  have hν := rtD_nu hU hV
  rtRoadD_CL hU hL hV hEQ (rbTCRest_of hν htc) (rbEMB2Rest_of hν hB2)

/-- **The road with TCrest and (EMB₂) asked only at the left ends `x ∈ [U_D, L(n+2))` with no reach below `L(n+1)`
that are restart points or lie in `[L(n+1), L(n+2))`**; (TC) from ENUM-REACH and EQ, (CL) derived. -/
theorem rtRoadD_rst2 (hU : ∀ l, CdRange S l → iota S gdV ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S gdV ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gdV ≤ l → CdCapV S l)
    (hEQ : CdEQ S) (hrest : RbTCrestRst S (Pv S gdV)) (hB2 : RbEMB2Rst S (Pv S gdV)) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hν := rtD_nu hU hV
  have hTCr : CdTCrest S := tqTCrest_of rtD_low (rbTCrestUp_of hν hrest)
  have hE : CdEMB2 S := tqEMB2_of rtD_low (rbEMB2Rest_of hν hB2)
  have hTC : CdTC S := cdTC_of_enum (rtD_UPPER hU) (rtD_LOWER hL) hEQ hTCr
  have hC : CdCL S := Cx.cxCL hTC hE
  exact ⟨hTC, hE, hC, (Cx.cxC1 hTC hE).1, gdDL_road S hU hL hV hC hEQ hTCr hE⟩

/-- **The road `rtRoadD_rst` with (EMB₂) dropped and (TC) asked only at the restart left ends in `[U_D, L(n+2))`
and at `L(n+1)`**, under `L(ω+1) ≤ ν_C` and `Ri.RiLhTopH` (a reduction: `L(ω+1) ≤ ν_C` is half of the
conclusion). -/
theorem rtRoadD_nuH (hU : ∀ l, CdRange S l → iota S gdV ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S gdV ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gdV ≤ l → CdCapV S l)
    (hEQ : CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC) (hlh : Ri.RiLhTopH S) (htc : RdTCRst2 S (Pv S gdV)) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  rtRoadD_rst hU hL hV hEQ
    (rdTCRst_of hν (rdLhTopFix2_of_W (rhLhTopW_of_G (Ri.riLhTopG_of_H hlh))) htc) (rdEMB2Rst_of hν _)

/-- `U_D < L(n+1)` for every `n`. -/
theorem rtD_lt_c (n : ℕ) : Pv S gdV < Bc.bcC S n :=
  (gdDL_fam S).2.2.trans_le (Ph.phL_chain (S := S) n).1

/-- **`Rd.RdTCRst2 S U_D` splits, given `T`, into (TC) at the restart left ends in `[U_D, L(n+2))` and the named
left ends `x = L(n+1)`, the latter being (CL)** (`L(n+1) ≥ L(0) > U_D`). -/
theorem rtTCRst2_iff (hT : Cx.CxT S) :
    RdTCRst2 S (Pv S gdV) ↔ RkTCRstOnly S (Pv S gdV) ∧ ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1)) := by
  constructor
  · intro h
    refine ⟨fun n x hx hU hr hrst => h n x hx hU hr (Or.inr hrst), fun n => ?_⟩
    refine (Rj.rjTC_L_iff hT n).1 ?_
    by_cases hr : ∃ r < Bc.bcC S n, IsReach R2C (Bc.bcC S n) r
    · obtain ⟨r, hr, hR⟩ := hr
      exact absurd ((hR.2 _ (le1_refl _)).trans_lt hr) (lt_irrefl _)
    · exact h n _ (Cx.cxC_lt n) (rtD_lt_c n).le hr (Or.inl rfl)
  · rintro ⟨hrst, hcl⟩ n x hx hU hr hcase
    rcases hcase with rfl | hR
    · exact (Rj.rjTC_L_iff hT n).2 (hcl n)
    · exact hrst n x hx hU hr hR

/-- **The road `Rk.rkRoadTow_nuE` with the bound `U_D = P(Γ_{Ω₁·2+1})`**: UPPER, LOWER, CapV asked only at
`λ ≥ ι(Γ_{Ω₁·2+1})`, `Rk.RkLhTopE`, `T`, (CL), and (TC) only at the restart left ends in `[U_D, L(n+2))`. -/
theorem rtRoadD_nuE (hU : ∀ l, CdRange S l → iota S gdV ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S gdV ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gdV ≤ l → CdCapV S l)
    (hEQ : CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC) (htop : RkLhTopE S)
    (hT : Cx.CxT S) (hrst : RkTCRstOnly S (Pv S gdV))
    (hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  rtRoadD_nuH hU hL hV hEQ hν (rkLhTopH_of_E htop) ((rtTCRst2_iff hT).2 ⟨hrst, hcl⟩)

/-- **(TC) at the restart left ends above `U` that ENUM-REACH, EQ, (CL) and `T` do not decide** (a hypothesis
name): `Rk.RkTCRstOnly S U` without the left ends `x = ρ_λ` of a range restart `λ` with `r(λ) < L(n+2)` and without
the named points `x = L(k+1)`, `k ≤ n`. -/
def RtTCRstHi (S : InaccSeq.{0}) (U : Ordinal.{0}) : Prop :=
  ∀ n : ℕ, ∀ x < Bc.bcC S (n + 1), U ≤ x → (¬ ∃ r < Bc.bcC S n, IsReach R2C x r) →
    (∃ l, IsRestartIdx l ∧ x = upsilon l) →
    (¬ ∃ l, CdRange S l ∧ x = upsilon l ∧ cdR S l < Bc.bcC S (n + 1)) →
    (∀ k : ℕ, k ≤ n → x ≠ Bc.bcC S k) → CdTCAt S n x

/-- **(TC) at the named points `L(k+1)`, `k ≤ n`, from (CL) and `T`**: `L(k+1) ≤₁ L(ω) ≤₁ L(ω+1)`, and `B_n` sends
`[L(k+1), L(n+2))` into `[B_n L(k+1), L(ω+1))` with `B_n L(k+1) = L(k+1)` (`k < n`) or `L(ω)` (`k = n`). -/
theorem rtTC_named (hT : Cx.CxT S) (hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) {n k : ℕ}
    (hk : k ≤ n) : CdTCAt S n (Bc.bcC S k) := by
  have hC : CdCL S := fun j => hcl j
  have hxω : le1 (Bc.bcC S k) (Nc.ncL S ω) := cdL_le1_omega hC k
  have hcs : StrictMono (Bc.bcC S) := strictMono_nat_of_lt_succ fun j => Cx.cxC_lt j
  have hkn1 : Bc.bcC S k < Bc.bcC S (n + 1) := hcs (Nat.lt_succ_of_le hk)
  right
  intro z hxz hz
  refine ⟨le1_of_le_of_le1 hxz (hz.le.trans (Bc.bcC_lt S (n + 1)).le) hxω, ?_⟩
  have hBz : Bc.bcB S n z < Nc.ncL S (ω + 1) := Bc.bcB_bound' S n z hz
  have hBxz : Bc.bcB S n (Bc.bcC S k) ≤ Bc.bcB S n z :=
    (Bc.bcB_mono' S n).monotoneOn (Set.mem_Iio.2 hkn1) (Set.mem_Iio.2 hz) hxz
  rcases hk.lt_or_eq with hlt | rfl
  · rw [Bc.bcB_fix' S n _ (hcs hlt)] at hBxz ⊢
    exact le1_of_le_of_le1 hBxz hBz.le (le1_trans hxω hT)
  · rw [Cx.cxB_base] at hBxz ⊢
    exact le1_of_le_of_le1 hBxz hBz.le hT

/-- **(TC) at a restart left end of the range with predicted reach below `L(n+2)`**, from UPPER, LOWER and EQ. -/
theorem rtTC_range (hU : CdUPPER S) (hL : CdLOWER S) (hEQ : CdEQ S) {n : ℕ} {l : Ordinal.{0}}
    (hl : CdRange S l) (hr : cdR S l < Bc.bcC S (n + 1)) : CdTCAt S n (upsilon l) := by
  rcases lt_or_ge (cdR S l) (Bc.bcC S n) with hlow | hhigh
  · exact cdTCAt_low (cdEnum_exact hU hL hl) hlow
  · obtain ⟨l', hl', hB, hBr⟩ := hEQ n l hl hhigh hr
    refine Or.inl ⟨cdR S l, hr, cdEnum_exact hU hL hl, ?_⟩
    rw [hB, hBr]
    exact cdEnum_exact hU hL hl'

/-- **Given UPPER, LOWER, EQ, `T` and (CL), `RtTCRstHi S U` gives `Rk.RkTCRstOnly S U`.** -/
theorem rtTCRst_of_hi (hU : CdUPPER S) (hL : CdLOWER S) (hEQ : CdEQ S) (hT : Cx.CxT S)
    (hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) {U : Ordinal.{0}}
    (h : RtTCRstHi S U) : RkTCRstOnly S U := by
  intro n x hx hxU hr hrst
  by_cases hR : ∃ l, CdRange S l ∧ x = upsilon l ∧ cdR S l < Bc.bcC S (n + 1)
  · obtain ⟨l, hl, rfl, hlr⟩ := hR
    exact rtTC_range hU hL hEQ hl hlr
  · by_cases hN : ∃ k : ℕ, k ≤ n ∧ x = Bc.bcC S k
    · obtain ⟨k, hk, rfl⟩ := hN
      exact rtTC_named hT hcl hk
    · exact h n x hx hxU hr hrst hR fun k hk e => hN ⟨k, hk, e⟩

/-- **The road `rtRoadD_nuE` with (TC) asked only at the restart left ends in `[U_D, L(n+2))` with no reach below
`L(n+1)` that are not range restarts with `r(λ) < L(n+2)` and not named points `L(k+1)`** (`RtTCRstHi S U_D`). -/
theorem rtRoadD_nuHi (hU : ∀ l, CdRange S l → iota S gdV ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S gdV ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gdV ≤ l → CdCapV S l)
    (hEQ : CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC) (htop : RkLhTopE S)
    (hT : Cx.CxT S) (hrst : RtTCRstHi S (Pv S gdV))
    (hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  rtRoadD_nuE hU hL hV hEQ hν htop hT
    (rtTCRst_of_hi (rtD_UPPER hU) (rtD_LOWER hL) hEQ hT hcl hrst) hcl

end Googology.Trans.PoR.InaccPsi.R2.Rt

import Googology.Trans.PoR.InaccPsi.R2.CdLow
import Googology.Trans.PoR.InaccPsi.R2.BcName

/-!
# The road to `ν_C = L(ω+1)` from ENUM-REACH

`L(ξ) = ψ_{Ω₁}(Ω_ω·2 + P'·ξ)` (`Nc.ncL`), `B_n = Bc.bcB S n` (the base change `L(n+1) ↦ L(ω)` on
`[0, L(n+2))`), `c_n = L(n+1)` (`Bc.bcC`); (C1) `L(n+2) ≤₁ L(ω)` for all `n`; (TC) and (EMB₂) are the
hypotheses of `R2.BcName` (written out below); `r(λ) = k_λ(Θ_λ(m_λ))` (`cdR`).

Hypotheses of the road, as propositions:

* `CdCL S` (**the CROSS-LIM relations**): `L(n+1) ≤₁ L(n+2)` for every `n`; `CdCROSS S` (**its crossing
  step**): `L(n+1) ≤₁ P(Ω_ω + P'·(n+1) + c')` for codes `c' < P'` cofinal in `P'`; `CdPredL S` (**the
  predicted reaches of `L(n+1)`**, realizer half): LOWER at every restart index of `L(n+1)` with
  `L(n+2) ≤ r(λ)`;
* `CdEQ S` (**EQ for `B_n` on the predicted values**): for every `λ` of the range with
  `L(n+1) ≤ r(λ) < L(n+2)`, `B_n(ρ_λ) = ρ_{λ'}` for some `λ'` of the range and `B_n(r(λ)) = r(λ')`
  (for `r(λ) < L(n+1)` this is automatic, `B_n` being the identity there);
* `CdTCrest S` (**TC at the other points**): every `x < L(n+2)` is a restart `ρ_λ` of the range with
  `r(λ) < L(n+2)`, or has a reach below `L(n+1)`, or satisfies the (TC) clause of `R2.BcName` at `x`;
* `CdEMB2 S` (**EMB₂**, kept as a hypothesis): `x ≤₂ y ↔ B_n x ≤₂ B_n y` on `[0, L(n+2))`.

Main statements:

* `cdCL_of_cross`, `cdCL_of_pred`: (CL) from the crossing step (`Pp.ppCross_L`), or from the predicted
  reaches of `L(n+1)`; `cdC1_of_CL`, `cdL12_of_CL`, `cdL_le1_omega`: (C1) `L(n+2) ≤₁ L(ω)`,
  `L(1) ≤₁ L(2)`, and `L(n+1) ≤₁ L(ω)`;
* `cdTCAt_low`: (TC) holds at every point with a reach below `L(n+1)`;
  `cdTC_of_enum`: UPPER, LOWER, `CdEQ`, `CdTCrest` give the (TC) hypothesis of `R2.BcName`;
* `cdQ_of_milestone`: `L(ω) ≤ ν_C = L(ω+1)` and `L(ω) ≤₁ L(ω+1)` give (Q), `lh(L(ω)) = L(ω+1)` and CAP
  at `L(ω)` (by the cap at `ν_C`, `nuC_cap`; no `T_ω` needed);
* `cdNu_bc` (**`ν_C = L(ω+1)` from CAP-0, CAP-1, (C1), (TC), (EMB₂)**): with `L(ω) ≤ ν_C`, PAIR
  `L(ω) <₂ L(ω+1)`, (P), (Q), `lh(L(ω)) = L(ω+1)`, and `L(ω)` the only `<₂`-predecessor of `ν_C`;
* `cdRst_of_caps`: CAP-0 and CAP-1 give the restart form of `L(ω) ≤ ν_C` (`Lb.lbL_iff_rst`);
* `cdNu_cross` (**`ν_C = L(ω+1)` from CAP-0, CAP-1, (CL), (Q)**);
* `cdReach_L` (**the reaches of `L(n+1)` and `L(ω)` at the milestone**): if `ν_C = L(ω+1)`, `L(ω)` is the
  only `<₂`-predecessor of `ν_C`, `L(ω) <₂ ν_C` and every `L(n+1) ≤₁ L(ω)`, then
  `lh(L(ω)) = lh(L(n+1)) = L(ω+1)`; `cdPred_L_iff`: then ENUM-REACH at these restarts is the equation
  `r(λ) = L(ω+1)`;
* `cdRoad` (**the whole road**): UPPER, LOWER, the cap of the values below `L(ω)`, (CL), `CdEQ`,
  `CdTCrest`, `CdEMB2` give `ν_C = L(ω+1)`, `L(ω) <₂ L(ω+1)`, (P), (Q), and
  `lh(L(ω)) = lh(L(n+1)) = L(ω+1)`; `cdRoad_cross`: the same with the crossing step `CdCROSS` in place of
  (CL); `cdRoad_cap`: the same from CAP-0, CAP-1, (CL), (TC), (EMB₂).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Cd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm

/-- The (TC) clause of `R2.BcName` at a point `x` for the base change `B_n`. -/
def CdTCAt (S : InaccSeq.{0}) (n : ℕ) (x : Ordinal.{0}) : Prop :=
  (∃ r < Bc.bcC S (n + 1), IsReach R2C x r ∧ IsReach R2C (Bc.bcB S n x) (Bc.bcB S n r)) ∨
    (∀ z, x ≤ z → z < Bc.bcC S (n + 1) → le1 x z ∧ le1 (Bc.bcB S n x) (Bc.bcB S n z))

/-- (C1): `L(n+2) ≤₁ L(ω)` for every `n`. -/
def CdC1 (S : InaccSeq.{0}) : Prop := ∀ n : ℕ, le1 (Bc.bcC S (n + 1)) (Nc.ncL S ω)

/-- (TC) of `R2.BcName`. -/
def CdTC (S : InaccSeq.{0}) : Prop := ∀ n : ℕ, ∀ x < Bc.bcC S (n + 1), CdTCAt S n x

/-- (EMB₂) of `R2.BcName`. -/
def CdEMB2 (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ x < Bc.bcC S (n + 1), ∀ y < Bc.bcC S (n + 1), (le2 x y ↔ le2 (Bc.bcB S n x) (Bc.bcB S n y))

/-- **The CROSS-LIM relations (CL)**: `L(n+1) ≤₁ L(n+2)` for every `n`. -/
def CdCL (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, le1 (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))

/-- **The crossing step of CROSS-LIM at `L(n+1)`**: `L(n+1) ≤₁ P(Ω_ω + P'·(n+1) + c')` for codes `c' < P'`
cofinal in `P'` (in the docs: by the realizers of the codes `G(θ_{k+1}·ω²) < P'` below `L(n+1)`). -/
def CdCROSS (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ c < Nc.ncPp S, ∃ c', c ≤ c' ∧ c' < Nc.ncPp S ∧
    le1 (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Pv S (Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) + c'))

/-- **The predicted reaches of `L(n+1)`** (realizer half): LOWER at every restart index of `L(n+1)`, with
`L(n+2) ≤ r(λ)`. -/
def CdPredL (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l, upsilon l = Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) →
    CdLower S l ∧ Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) ≤ cdR S l

/-- **EQ for `B_n` on the predicted values** at the restarts of the range whose predicted reach lies in
`[L(n+1), L(n+2))` (below `L(n+1)` it is automatic: `B_n` is the identity there). -/
def CdEQ (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l, CdRange S l → Bc.bcC S n ≤ cdR S l → cdR S l < Bc.bcC S (n + 1) →
    ∃ l', CdRange S l' ∧ Bc.bcB S n (upsilon l) = upsilon l' ∧ Bc.bcB S n (cdR S l) = cdR S l'

/-- **TC at the other points**: every `x < L(n+2)` is a restart of the range with `r(λ) < L(n+2)`, or has
a reach below `L(n+1)` (there (TC) is automatic), or satisfies the (TC) clause at `x`. -/
def CdTCrest (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ x < Bc.bcC S (n + 1),
    (∃ l, CdRange S l ∧ x = upsilon l ∧ cdR S l < Bc.bcC S (n + 1)) ∨
      (∃ r < Bc.bcC S n, IsReach R2C x r) ∨ CdTCAt S n x

variable {S : InaccSeq.{0}}

/-- **(CL) from the crossing step** (`Pp.ppCross_L`: `P(Ω_ω + P'·(n+1) + P') = L(n+2)` is the supremum). -/
theorem cdCL_of_cross (hx : CdCROSS S) : CdCL S := fun n => Pp.ppCross_L _ (hx n)

/-- **(CL) from the predicted reaches of `L(n+1)`.** -/
theorem cdCL_of_pred (hp : CdPredL S) : CdCL S := by
  intro n
  obtain ⟨l, -, hl⟩ := Pp.ppL_succ_restart (S := S) n
  obtain ⟨hL, h2⟩ := hp n l hl.symm
  have h1 : le1 (upsilon l) (cdR S l) := hL
  rw [← hl] at h1
  exact le1_of_le_of_le1 (Pp.ppL_lt_succ (S := S) n).le h2 h1

/-- **(C1) from (CL)**: `L(n+2) ≤₁ L(ω)` (`Pp.ppTo_omega`). -/
theorem cdC1_of_CL (hC : CdCL S) : CdC1 S := fun n => Pp.ppTo_omega hC (n + 1)

/-- `L(1) ≤₁ L(2)` is (CL) at `n = 0`. -/
theorem cdL12_of_CL (hC : CdCL S) :
    le1 (Nc.ncL S ((1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((2 : ℕ) : Ordinal.{0})) := hC 0

/-- `L(n+1) ≤₁ L(ω)` for every `n`, from (CL). -/
theorem cdL_le1_omega (hC : CdCL S) :
    ∀ n : ℕ, le1 (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ω) := Pp.ppTo_omega hC

/-- (TC) at a point with a reach below `L(n+1)` (`B_n` is the identity on `[0, L(n+1))`). -/
theorem cdTCAt_low {n : ℕ} {x r : Ordinal.{0}} (hr : IsReach R2C x r) (hrn : r < Bc.bcC S n) :
    CdTCAt S n x := by
  have hxr : x ≤ r := le1_le hr.1
  have hBx : Bc.bcB S n x = x := Bc.bcB_fix' S n x (hxr.trans_lt hrn)
  have hBr : Bc.bcB S n r = r := Bc.bcB_fix' S n r hrn
  refine Or.inl ⟨r, hrn.trans_le (Bc.bcC_mono S (Nat.le_succ n)), hr, ?_⟩
  rw [hBx, hBr]; exact hr

/-- **(TC) from ENUM-REACH**, EQ for `B_n` on the predicted values, and TC at the other points. -/
theorem cdTC_of_enum (hU : CdUPPER S) (hL : CdLOWER S) (hEQ : CdEQ S) (hrest : CdTCrest S) :
    CdTC S := by
  intro n x hx
  rcases hrest n x hx with ⟨l, hl, rfl, hr⟩ | ⟨r, hrn, hrx⟩ | h
  · rcases lt_or_ge (cdR S l) (Bc.bcC S n) with hlow | hhigh
    · exact cdTCAt_low (cdEnum_exact hU hL hl) hlow
    · obtain ⟨l', hl', hB, hBr⟩ := hEQ n l hl hhigh hr
      refine Or.inl ⟨cdR S l, hr, cdEnum_exact hU hL hl, ?_⟩
      rw [hB, hBr]
      exact cdEnum_exact hU hL hl'
  · exact cdTCAt_low hrx hrn
  · exact h

/-- **(Q) and the reach of `L(ω)` at the milestone**: `L(ω) ≤ ν_C = L(ω+1)` and `L(ω) ≤₁ L(ω+1)` give
(Q), `lh(L(ω)) = L(ω+1)`, and CAP at `L(ω)`. -/
theorem cdQ_of_milestone (hlow : Nc.ncL S ω ≤ nuC) (hν : nuC = Nc.ncL S (ω + 1))
    (hT : le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1))) :
    ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧ IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ g, Nc.ncL S ω ≤ g → (le1 (Nc.ncL S ω) g ↔ g ≤ Nc.ncL S (ω + 1)) := by
  have hcap : ∀ g, Nc.ncL S (ω + 1) < g → ¬ le1 (Nc.ncL S ω) g := fun g hg =>
    nuC_cap _ hlow g (hν ▸ hg)
  have hr : IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) :=
    ⟨hT, fun g hg => not_lt.1 fun h => hcap g h hg⟩
  refine ⟨hcap _ (lt_add_one _), hr, fun g hg => ⟨fun h => hr.2 g h, fun h => ?_⟩⟩
  exact le1_of_le_of_le1 hg h hT

/-- **`ν_C = L(ω+1)` from CAP-0, CAP-1, (C1), (TC), (EMB₂)**: with `L(ω) ≤ ν_C`, PAIR
`L(ω) <₂ L(ω+1)`, (P), (Q), `lh(L(ω)) = L(ω+1)`, and `L(ω)` the only `<₂`-predecessor of `ν_C`. -/
theorem cdNu_bc (h0 : CdCAP0 S) (h1 : CdCAP1 S (Nc.ncL S ω)) (hc1 : CdC1 S) (hTC : CdTC S)
    (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧ IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ c < nuC, le2 c nuC → c = Nc.ncL S ω := by
  have hlow := cdLow h0 h1
  have hν := Bc.bcNuC_eq S hc1 hTC hB2 (Lw.lw_not_tau_L_omega S) hlow
  have hpair := Bc.bcPair S hc1 hTC hB2
  have hP := Bc.bcP S hc1 hTC hB2
  obtain ⟨hQ, hr, -⟩ := cdQ_of_milestone hlow hν (le2_le1 hpair.2)
  obtain ⟨-, -, -, -, huniq⟩ := Lb.lbMilestone hlow hP hQ
  exact ⟨hν, hlow, hpair.2, hP, hQ, hr, huniq⟩

/-- **The restart form of `L(ω) ≤ ν_C` (`Lb.lbL_iff_rst`) from CAP-0 and CAP-1**: every limit `λ ∈ [B₀, L(ω))`
of restart indices with reach `r < L(ω)` has a bound `ν < λ` above which no restart `υ_μ`, `μ < λ`, is
`≤₁ r`. -/
theorem cdRst_of_caps (h0 : CdCAP0 S) (h1 : CdCAP1 S (Nc.ncL S ω)) :
    ∀ l, IsRestartIdx l → VzLam + ω * ω ≤ l → l < Nc.ncL S ω →
      (∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l) →
      ∀ r, r < Nc.ncL S ω → IsReach R2C (upsilon l) r →
      ∃ ν < l, ∀ μ, IsRestartIdx μ → ν < μ → μ < l → ¬ le1 (upsilon μ) r :=
  (Lb.lbL_iff_rst S).1 (cdLow h0 h1)

/-- **`ν_C = L(ω+1)` from CAP-0, CAP-1, (CL) and (Q).** -/
theorem cdNu_cross (h0 : CdCAP0 S) (h1 : CdCAP1 S (Nc.ncL S ω)) (hC : CdCL S)
    (hT : le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hQ : ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1)) :
    nuC = Nc.ncL S (ω + 1) ∧ le2 (Nc.ncL S ω) nuC ∧ ∀ c < nuC, le2 c nuC → c = Nc.ncL S ω :=
  Lb.lbMilestone_cross hC hT hQ (cdLow h0 h1)

/-- **The reaches of `L(ω)` and of every `L(n+1)` at the milestone.** -/
theorem cdReach_L (hν : nuC = Nc.ncL S (ω + 1)) (h2 : le2 (Nc.ncL S ω) nuC)
    (huniq : ∀ c < nuC, le2 c nuC → c = Nc.ncL S ω)
    (hC : ∀ n : ℕ, le1 (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ω)) :
    IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  obtain ⟨l, -, hlν, hl2, hr, -, -, hW, -⟩ := Lb.lbFirst0
  have hlL : upsilon l = Nc.ncL S ω := huniq _ hlν hl2
  rw [hlL, hν] at hr
  refine ⟨hr, fun n => ?_⟩
  have hlt : Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) < upsilon l := by
    rw [hlL]; exact Pp.ppL_lt_omega n
  have h1 : le1 (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) nuC := le1_trans (hC n) (le2_le1 h2)
  obtain ⟨μ, -, hμ, hrμ⟩ := hW _ hlt h1
  rw [hμ, ← hν]; exact hrμ

/-- **ENUM-REACH at `L(ω)` and at `L(n+1)` is the equation `r(λ) = L(ω+1)`** (under the data of the
milestone). -/
theorem cdPred_L_iff (hν : nuC = Nc.ncL S (ω + 1)) (h2 : le2 (Nc.ncL S ω) nuC)
    (huniq : ∀ c < nuC, le2 c nuC → c = Nc.ncL S ω)
    (hC : ∀ n : ℕ, le1 (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ω)) :
    (∀ l, upsilon l = Nc.ncL S ω →
      ((CdUpper S l ∧ CdLower S l) ↔ cdR S l = Nc.ncL S (ω + 1))) ∧
    (∀ n : ℕ, ∀ l, upsilon l = Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) →
      ((CdUpper S l ∧ CdLower S l) ↔ cdR S l = Nc.ncL S (ω + 1))) := by
  obtain ⟨hω, hn⟩ := cdReach_L hν h2 huniq hC
  have key : ∀ l r, IsReach R2C (upsilon l) r → ((CdUpper S l ∧ CdLower S l) ↔ cdR S l = r) := by
    intro l r hr
    rw [cdExact_iff]
    exact ⟨fun h => Lb.lbReach_unique h hr, fun h => h ▸ hr⟩
  exact ⟨fun l hl => key l _ (hl ▸ hω), fun n l hl => key l _ (hl ▸ hn n)⟩

/-- **The whole road to `ν_C = L(ω+1)`**: from UPPER and LOWER on `[B₀, L(ω+1))` (ENUM-REACH), the cap of
the predicted values below `L(ω)`, the CROSS-LIM relations (CL), EQ for `B_n`, TC at the other points, and
(EMB₂): `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), and `lh(L(ω)) = lh(L(n+1)) = L(ω+1)`
for every `n`. -/
theorem cdRoad (hU : CdUPPER S) (hL : CdLOWER S)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  obtain ⟨h0, h1⟩ := cdCAP_of_enum hU hV
  have hc1 := cdC1_of_CL hC
  have hTC := cdTC_of_enum hU hL hEQ hrest
  obtain ⟨hν, hlow, hpair, hP, hQ, hr, huniq⟩ := cdNu_bc h0 h1 hc1 hTC hB2
  have h2 : le2 (Nc.ncL S ω) nuC := hν ▸ hpair
  obtain ⟨-, hn⟩ := cdReach_L hν h2 huniq (cdL_le1_omega hC)
  exact ⟨hν, hlow, hpair, hP, hQ, hr, hn⟩

/-- **The road with the crossing step of CROSS-LIM** in place of (CL). -/
theorem cdRoad_cross (hU : CdUPPER S) (hL : CdLOWER S)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CdCapV S l) (hx : CdCROSS S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  cdRoad hU hL hV (cdCL_of_cross hx) hEQ hrest hB2

/-- **The road with the caps in place of UPPER**: CAP-0, CAP-1 below `L(ω)`, (CL), (TC) and (EMB₂) give
the same conclusions. -/
theorem cdRoad_cap (h0 : CdCAP0 S) (h1 : CdCAP1 S (Nc.ncL S ω)) (hC : CdCL S) (hTC : CdTC S)
    (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  obtain ⟨hν, hlow, hpair, hP, hQ, hr, huniq⟩ := cdNu_bc h0 h1 (cdC1_of_CL hC) hTC hB2
  have h2 : le2 (Nc.ncL S ω) nuC := hν ▸ hpair
  obtain ⟨-, hn⟩ := cdReach_L hν h2 huniq (cdL_le1_omega hC)
  exact ⟨hν, hlow, hpair, hP, hQ, hr, hn⟩

end Googology.Trans.PoR.InaccPsi.R2.Cd

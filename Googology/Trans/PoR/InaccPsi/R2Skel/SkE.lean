import Googology.Trans.PoR.InaccPsi.R2.WdRoad
import Googology.Trans.PoR.InaccPsi.R2.XgReach
import Googology.Trans.PoR.InaccPsi.R2.XnRoad

/-!
# Skeleton of part EQ: the hypotheses `(hν → WdThLow)` and `(hν → WdEQfar)` of `Wd.wdRoadL`

`L(ξ) = Nc.ncL S ξ`, `c_n = L(n+1)`, `B_n = Bc.bcB S n`, `ν_C = nuC`, `hν := L(ω+1) ≤ ν_C`,
`ρ_λ = υ_λ`, `δ_λ = υ_{λ+ω+1}`, `k_λ = Cd.cdk λ` (enumeration of the closed set `K_λ = Cd.cdK λ`),
`Θ_λ = Cd.cdTheta S λ`, `m_λ = Cd.cdCode S λ`, `r(λ) = k_λ(Θ_λ(m_λ))`, `θ⁺ = Lj.ljThP S`, `M_W = Rn.rnMW S`.
A window `(n, λ, λ')`: `CdRange λ`, `c_n < ρ_λ`, `r(λ) < c_{n+1}`, `λ'` a restart, `B_n ρ_λ = ρ_{λ'}`, `ρ_λ < m_λ`.
A far window: also `δ_λ·ω ≤ Θ_λ(m_λ)`.

Tree (indent = child).  Round 117: the top takes, besides `hRead`, the frontier hypotheses `hUH`, `hLH` of the road
(UPPER / LOWER past `ι(Γ(φ(Ω₁·Ω₁, G+1))·ω)`, i.e. `SkF.skFrontU S`, `SkF.skFrontL S`), which with `Hl.hlU_enum` give
ENUM-REACH on the whole range (`skEnum`).
* `skEQ` REDUCED: `(hν → WdThLow) ∧ (hν → WdEQfar)` from `hRead`, `hUH`, `hLH`.
  * `skThLow` PROVED (round 117, `Xn.xnThLow`): `WdThLow` from `hRead` alone (the chain of the repo is pointwise;
    a near window never uses the far EQ).  The cycle `skThLow ← skEQfar` is gone.
  * `skEnum` PROVED (`Xn.xnEnum_of_front`): ENUM-REACH from `hUH`, `hLH`.
  * `skEQfar` REDUCED: `WdEQfar` from the induction on `r(λ)` (`Xn.xnPart`): children `skThFar`, `skKCof`, `skEQTopR`,
    and `skThLow`, `skEnum`.
    * `skThFar` OPEN: the reading move at the far codes.
    * `skKFar` REDUCED (round 116, `Xg.xgKFar_of_R`): induction on `p`; below `δ_λ·ω` `Wd.wdk_move`; inside a
      block `[k_λ(q), k_λ(q)·ω)` (`Xg.xgK_add`, `Xg.xgk_add`: `k_λ(q+Z) = k_λ(q)+Z`) the move is carried from `q`;
      at a cofinal index `p` (`k_λ(q) < p` for `q < p`) `k_λ(p)` is the `R₂^C`-reach of `p` (`Xg.xgk_reach`),
      which moves at non-`υ`-points (`Xg.xgReach_nonUps`) and at non-range `υ`-points (`Xg.xgKReach_of`).
      * `skKCof` OPEN: at a cofinal index `p`, `K_{λ'}` is cofinal below `B_n p` (PROVED where `B_n` is
        continuous at `p`: `skKCof_cont`).
      * `skKReachR` REDUCED (round 117, `Xn.xnPart`): EQ at the inner restarts by ONE induction on the predicted
        reach `r(λ)` (`Xn.xnEQ_all`): every inner `μ` with `ρ_μ < T_λ` has `r(μ) = k_λ(ρ_μ) < r(λ)`
        (`Xn.xnR_inner_lt`); only the TOP `ρ_μ = T_λ` has `r(μ) = r(λ)` (`Xn.xnR_inner_top`).
        * `skEQTopR` OPEN: EQ at the top restart given EQ at every smaller reach (`Xn.XnTop`; follows from the
          target, `skEQTopR_of_target`; follows from the well-foundedness of the top relation, `skEQTopR_of_wf`).
  * old children of `skKFar`, now off the path: `skKGap` PROVED (`Xg.xgKGap`), `skKClosed` and `skKLim`
    REDUCED to `skKFar` (`SkEX.skexClosed_of_far`, `SkEX.skexLim_of_far`).
Guards and links (PROVED): `skNoIdx` (the index-keeping move `k_{λ'}(p) = B_n(k_λ p)` is false at `p = ρ_λ`),
`skThFar_of_top` / `skThHi_of_top` (one reading move at every code `≥ θ⁺` gives both `skThFar` and `WdThHi`),
`skThFar_of_EQ` (`CdEQ` and `skKFar` give `skThFar`), `skKFar_of` (the old split), `skKCof_cont`,
`skKCof_of_far` (`SkKFar` and `skKReachR` give `skKCof`), `skKReachR_of_target`, `skThFar_of_target`
(`CdUPPER ∧ CdLOWER ∧ CdEQ ∧ skKCof` give `skThFar`: non-vacuity against the road's target), round 117:
`skEQTopR_of_target`, `skEQTopR_of_wf`, `skKCof_of_blk` (one block of closed points per `Q < B_n p` gives `skKCof`),
`skKCof_iff_unbdd` (for indecomposable `B_n p`: `skKCof` at `p` ⇔ `K_{λ'}` unbounded below `B_n p`).
-/

set_option autoImplicit false

namespace R2Skel.SkE

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-! ## Hypothesis names -/

/-- A window `(n, λ, λ')`. -/
def SkWin (S : InaccSeq.{0}) (n : ℕ) (l l' : Ordinal.{0}) : Prop :=
  CdRange S l ∧ Bc.bcC S n < upsilon l ∧ cdR S l < Bc.bcC S (n + 1) ∧ IsRestartIdx l' ∧
    Bc.bcB S n (upsilon l) = upsilon l' ∧ upsilon l < cdCode S l

/-- The reading move at the far codes (`δ_λ·ω ≤ Θ_λ(m_λ)`). -/
def SkThFar (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', SkWin S n l l' → cdDelta l * ω ≤ cdTheta S l (cdCode S l) →
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l')

/-- The reading move at every code `m_λ ≥ θ⁺` (no bound on `Θ_λ(m_λ)`). -/
def SkThTop (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', SkWin S n l l' → Lj.ljThP S ≤ cdCode S l →
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l')

/-- The move of `k` at the far indices: `k_{λ'}(B_n p) = B_n(k_λ p)` for `δ_λ·ω ≤ p ≤ Θ_λ(m_λ)`. -/
def SkKFar (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', SkWin S n l l' → ∀ p, cdDelta l * ω ≤ p → p ≤ cdTheta S l (cdCode S l) →
    cdk l' (Bc.bcB S n p) = Bc.bcB S n (cdk l p)

/-- The image of a successor closed point is closed at `λ'`. -/
def SkKClosed (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', SkWin S n l l' → ∀ q, cdDelta l * ω ≤ q + 1 → q + 1 ≤ cdTheta S l (cdCode S l) →
    Bc.bcB S n (cdk l (q + 1)) ∈ cdK l'

/-- No closed point of `λ'` lies strictly between `B_n(k_λ q)` and `B_n(k_λ(q+1))`. -/
def SkKGap (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', SkWin S n l l' → ∀ q, cdDelta l * ω ≤ q + 1 → q + 1 ≤ cdTheta S l (cdCode S l) →
    ∀ z ∈ cdK l', Bc.bcB S n (cdk l q) < z → ¬ z < Bc.bcB S n (cdk l (q + 1))

/-- The limit step of the `k`-move. -/
def SkKLim (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', SkWin S n l l' → ∀ p, IsSuccLimit p → cdDelta l * ω ≤ p →
    p ≤ cdTheta S l (cdCode S l) →
    (∀ q < p, cdk l' (Bc.bcB S n q) = Bc.bcB S n (cdk l q)) →
    cdk l' (Bc.bcB S n p) = Bc.bcB S n (cdk l p)

/-! ## Small facts -/

theorem sk_cdR_eq (l : Ordinal.{0}) : cdR S l = cdk l (cdTheta S l (cdCode S l)) := rfl

theorem sk_one_lt (n : ℕ) : (1 : Ordinal.{0}) < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) :=
  one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _))

/-! ## Open leaves -/

/-- STATUS: OPEN
SIZE: L
REFUTE: SURVIVED (round 116: no Lean value of Θ above M_W — Ro.roThW_A reads only ψ_{Ω₂}(Ω_ω + c), c < M_W;
no no-go applies; implied by CdUPPER ∧ CdLOWER ∧ CdEQ ∧ skKCof: skThFar_of_target; round 117: unchanged, still no
reading above M_W)
∀ far window: B_n Θ_λ(m_λ) = Θ_{λ'}(m_{λ'})  (codes m_λ > M_W; no value of Θ_λ above M_W is known). -/
theorem skThFar (hν : Nc.ncL S (ω + 1) ≤ nuC) : SkThFar S := by sorry

/-- STATUS: OPEN
SIZE: L
REFUTE: SURVIVED (round 116: true where B_n is continuous at p, skKCof_cont; implied by SkKFar ∧ skKReachR,
skKCof_of_far; no no-go applies; round 117: for indecomposable B_n p it is exactly the unboundedness of K_{λ'}
below B_n p, skKCof_iff_unbdd; no Lean value of the reaches of the points of the jump gap, which contains
υ-points that are not images of B_n)
cofinal far index p (δ_λ·ω ≤ p ≤ Θ_λ(m_λ), k_λ(q) < p for q < p), move below p ⇒ ∀ Q < B_n p, k_{λ'}(Q) < B_n p
(left: the indices p where B_n jumps, e.g. p = ω^{e+L(n+1)}: closed points of λ' in [sup_{q<p} B_n q, B_n p)). -/
theorem skKCof (hν : Nc.ncL S (ω + 1) ≤ nuC) : Xg.XgKCof S := by sorry

/-- STATUS: OPEN
SIZE: L
REFUTE: SURVIVED (round 117: follows from the target, skEQTopR_of_target (CdUPPER ∧ CdLOWER ∧ CxEQtop); follows from
the well-foundedness of the top relation, skEQTopR_of_wf; no no-go result speaks of EQ at range restarts; the
relation is not shown empty: T_λ = Θ_λ(m_λ) can be a restart υ-point for far codes)
NEW leaf (round 117).  Long-code window λ whose top T_λ = Θ_λ(m_λ) is a cofinal far range restart ρ_μ
(r(μ) = r(λ)), EQ at every window of smaller reach ⇒ EQ at μ  (statement Xn.XnTop S). -/
theorem skEQTopR (hν : Nc.ncL S (ω + 1) ≤ nuC) : Xn.XnTop S := by sorry

/-! ## Reduced nodes -/

/-- The frontier hypotheses of the road (UPPER past the frontier `ι(Γ(φ(Ω₁·Ω₁, G+1))·ω)`), `SkF.skFrontU S`. -/
abbrev SkUH (S : InaccSeq.{0}) : Prop :=
  ∀ l, CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdUpper S l

/-- The frontier hypotheses of the road (LOWER past the frontier), `SkF.skFrontL S`. -/
abbrev SkLH (S : InaccSeq.{0}) : Prop :=
  ∀ l, CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdLower S l

/-- STATUS: PROVED (Xn.xnEnum_of_front, Hl.hlU_enum)
SIZE: S
hUH ∧ hLH ⇒ CdUPPER ∧ CdLOWER (ENUM-REACH on the whole range). -/
theorem skEnum (hUH : SkUH S) (hLH : SkLH S) : CdUPPER S ∧ CdLOWER S :=
  Xn.xnEnum_of_front hUH hLH

/-- STATUS: PROVED (Xn.xnThLow)
SIZE: S
hRead ⇒ (hν → WdThLow)  (no EQ needed; round 117). -/
theorem skThLow (hRead : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdAtWall S ∧ Wd.WdThHi S) :
    Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S :=
  fun hν => Xn.xnThLow hν (hRead hν).1 (hRead hν).2

/-- STATUS: REDUCED
SIZE: L
hRead, hUH, hLH, hν ⇒ XgKReachR  (children skThFar, skKCof, skEQTopR; Xn.xnPart: the induction on r(λ),
Xn.xnEQ_all; checkable after the merge of R2.XnLow, R2.XnInd, R2.XnRoad). -/
theorem skKReachR (hRead : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdAtWall S ∧ Wd.WdThHi S) (hUH : SkUH S)
    (hLH : SkLH S) (hν : Nc.ncL S (ω + 1) ≤ nuC) : Xg.XgKReachR S :=
  (Xn.xnPart hν (hRead hν).1 (hRead hν).2 (skEnum hUH hLH).1 (skEnum hUH hLH).2 (skThFar hν) (skKCof hν)
    (skEQTopR hν)).2.2.1


/-- STATUS: PROVED (Wd.wdk_move, Bc.bcB_add, Bc.bcB_fixN, Bc.bcB_lt_iff, Ordinal.enumOrd_succ_le)
SIZE: S
closed-move ∧ gap ∧ limit-step ⇒ ∀ p ≤ Θ_λ(m_λ), k_{λ'}(B_n p) = B_n(k_λ p). -/
theorem skKFar_of (hν : Nc.ncL S (ω + 1) ≤ nuC) (hC : SkKClosed S) (hG : SkKGap S) (hL : SkKLim S) :
    SkKFar S := by
  intro n l l' hW
  obtain ⟨hR, h1, hr, hl', hB, hm⟩ := hW
  have hW : SkWin S n l l' := ⟨hR, h1, hr, hl', hB, hm⟩
  set T := cdTheta S l (cdCode S l) with hT
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have hkL : ∀ p ≤ T, cdk l p < Nc.ncL S ω := fun p hp =>
    (((cdk_strictMono l).monotone hp).trans_lt hr).trans (Bc.bcC_lt S (n + 1))
  have hpL : ∀ p ≤ T, p < Nc.ncL S ω := fun p hp => ((cdk_strictMono l).id_le p).trans_lt (hkL p hp)
  have key : ∀ p, p ≤ T → cdk l' (Bc.bcB S n p) = Bc.bcB S n (cdk l p) := by
    intro p
    induction p using WellFoundedLT.induction with
    | ind p IH =>
    intro hp
    by_cases hlow : p < cdDelta l * ω
    · exact Wd.wdk_move hν hR.1 hl' h1 hδr hB hlow
    have hfar : cdDelta l * ω ≤ p := not_lt.1 hlow
    rcases zero_or_succ_or_isSuccLimit p with h0 | ⟨q, rfl⟩ | hlim
    · subst h0
      exact absurd (mul_pos (Wd.wdDelta_pos hR.1) omega0_pos) (not_lt.2 hfar)
    · rw [Order.succ_eq_add_one] at hp hfar IH ⊢
      have hq : q ≤ T := (le_self_add).trans hp
      have hqp : q < q + 1 := lt_add_one q
      have IHq := IH q hqp hq
      have h1L : (1 : Ordinal.{0}) < Nc.ncL S ω :=
        one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S ω))
      have hB1 : Bc.bcB S n 1 = 1 := Bc.bcB_fixN n 1 (sk_one_lt n)
      have hBs : Bc.bcB S n (q + 1) = Bc.bcB S n q + 1 := by
        rw [Bc.bcB_add (hpL q hq) h1L, hB1]
      have hxy : Bc.bcB S n (cdk l q) < Bc.bcB S n (cdk l (q + 1)) :=
        (Bc.bcB_lt_iff (hkL q hq) (hkL (q + 1) hp)).2 ((cdk_strictMono l) hqp)
      have hmem := hC n l l' hW q hfar hp
      rw [hBs]
      refine le_antisymm ?_ ?_
      · have := enumOrd_succ_le (cdK_unbdd l') hmem (by rw [← IHq] at hxy; exact hxy)
        rwa [Order.succ_eq_add_one] at this
      · have hz : cdk l' (Bc.bcB S n q + 1) ∈ cdK l' := cdk_mem l' _
        have hgt : Bc.bcB S n (cdk l q) < cdk l' (Bc.bcB S n q + 1) := by
          rw [← IHq]; exact (cdk_strictMono l') (lt_add_one _)
        exact not_lt.1 (hG n l l' hW q hfar hp _ hz hgt)
    · exact hL n l l' hW p hlim hfar hp (fun q hq => IH q hq (hq.le.trans hp))
  exact fun p _ hp => key p hp

/-- STATUS: REDUCED
SIZE: L
∀ far window, ∀ δ_λ·ω ≤ p ≤ Θ_λ(m_λ): k_{λ'}(B_n p) = B_n(k_λ p)  (children skKCof, skKReachR;
Xg.xgKFar_of_R; checkable after the merge of R2.XgK, R2.XgReach, R2.Xn*). -/
theorem skKFar (hRead : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdAtWall S ∧ Wd.WdThHi S) (hUH : SkUH S)
    (hLH : SkLH S) (hν : Nc.ncL S (ω + 1) ≤ nuC) : SkKFar S :=
  Xg.xgKFar_of_R hν (skKCof hν) (skKReachR hRead hUH hLH hν)

/-- STATUS: REDUCED
SIZE: S
δ_λ·ω ≤ q+1 ≤ Θ_λ(m_λ) ⇒ B_n(k_λ(q+1)) ∈ K_{λ'}  (from skKFar: SkEX.skexClosed_of_far; off the path). -/
theorem skKClosed (hRead : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdAtWall S ∧ Wd.WdThHi S) (hUH : SkUH S)
    (hLH : SkLH S) (hν : Nc.ncL S (ω + 1) ≤ nuC) : SkKClosed S :=
  R2Skel.SkEX.skexClosed_of_far hν (skKFar hRead hUH hLH hν)

/-- STATUS: PROVED (Xg.xgKGap: k_λ(q+1) = k_λ(q) + 1, Xg.xgk_succ)
SIZE: S
z ∈ K_{λ'} ⇒ ¬ (B_n k_λ(q) < z < B_n k_λ(q+1))  (no hypothesis needed). -/
theorem skKGap (_hν : Nc.ncL S (ω + 1) ≤ nuC) : SkKGap S :=
  Xg.xgKGap

/-- STATUS: REDUCED
SIZE: S
p limit, δ_λ·ω ≤ p ≤ Θ_λ(m_λ), IH ⇒ k_{λ'}(B_n p) = B_n k_λ(p)  (from skKFar: SkEX.skexLim_of_far; off the path). -/
theorem skKLim (hRead : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdAtWall S ∧ Wd.WdThHi S) (hUH : SkUH S)
    (hLH : SkLH S) (hν : Nc.ncL S (ω + 1) ≤ nuC) : SkKLim S :=
  R2Skel.SkEX.skexLim_of_far (skKFar hRead hUH hLH hν)

/-- STATUS: PROVED (definitions only)
SIZE: S
far reading move ∧ far k-move ⇒ WdEQfar:  B_n r(λ) = B_n k_λ(Θ) = k_{λ'}(B_n Θ) = k_{λ'}(Θ') = r(λ'). -/
theorem skEQfar_of (hT : SkThFar S) (hK : SkKFar S) : Wd.WdEQfar S := by
  intro n l l' hR h1 hr hl' hB hm hw
  have hW : SkWin S n l l' := ⟨hR, h1, hr, hl', hB, hm⟩
  rw [sk_cdR_eq, sk_cdR_eq, ← hK n l l' hW _ hw le_rfl, hT n l l' hW hw]

/-- STATUS: REDUCED
SIZE: L
hRead, hUH, hLH ⇒ (hν ⇒ WdEQfar)  (children skThFar, skKFar). -/
theorem skEQfar (hRead : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdAtWall S ∧ Wd.WdThHi S) (hUH : SkUH S)
    (hLH : SkLH S) : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdEQfar S :=
  fun hν => skEQfar_of (skThFar hν) (skKFar hRead hUH hLH hν)

/-- STATUS: PROVED (Wa.waEQtop_ux, Wd.wdAtMove26_of_wall, Wd.wdRn_of, Wd.wdEQtop_iff)
SIZE: S
(hν → WdAtWall ∧ WdThHi) ∧ (hν → WdEQfar) ⇒ (hν → WdThLow). -/
theorem skThLow_of (hRead : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdAtWall S ∧ Wd.WdThHi S)
    (hF : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdEQfar S) : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S := by
  intro hν
  have hrn := Wd.wdRn_of hν (hRead hν).2 (hF hν)
  exact ((Wd.wdEQtop_iff hν).1
    (Wa.waEQtop_ux hν (Wd.wdAtMove26_of_wall (hRead hν).1) hrn.1 hrn.2)).1


/-- STATUS: REDUCED
SIZE: L
TOP NODE (round 117: new hypotheses hUH, hLH, the frontier hypotheses of the road; Root.skNuC applies
`skEQ hRead (SkF.skFrontU S) (SkF.skFrontL S)`).
hRead: hν → WdAtWall ∧ WdThHi, hUH, hLH  ⇒  (hν → WdThLow) ∧ (hν → WdEQfar). -/
theorem skEQ (hRead : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdAtWall S ∧ Wd.WdThHi S) (hUH : SkUH S)
    (hLH : SkLH S) :
    (Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S) ∧ (Nc.ncL S (ω + 1) ≤ nuC → Wd.WdEQfar S) :=
  ⟨skThLow hRead, skEQfar hRead hUH hLH⟩

/-! ## Guards and links -/

/-- STATUS: PROVED (Wd.wdk_move, Cd.cdk_inj, Bc.bcB_base, Bc.bcB_lt_iff)
SIZE: S
NO-GO for the index-keeping move: in a window, k_{λ'}(ρ_λ) ≠ B_n(k_λ(ρ_λ)), since B_n k_λ(ρ_λ) = k_{λ'}(ρ_{λ'})
and ρ_λ < L(ω) < ρ_{λ'}.  So the far move must move the index (as in SkKFar). -/
theorem skNoIdx (hν : Nc.ncL S (ω + 1) ≤ nuC) {n : ℕ} {l l' : Ordinal.{0}} (hW : SkWin S n l l') :
    cdk l' (upsilon l) ≠ Bc.bcB S n (cdk l (upsilon l)) := by
  obtain ⟨hR, h1, hr, hl', hB, -⟩ := hW
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have hρδ : upsilon l < cdDelta l * ω :=
    (cdRho_lt_delta l).trans_le (le_mul_left _ omega0_pos)
  rw [← Wd.wdk_move hν hR.1 hl' h1 hδr hB hρδ, hB, Ne, cdk_inj]
  intro he
  have hρL : upsilon l < Nc.ncL S ω :=
    ((cdRho_lt_delta l).trans hδr).trans (Bc.bcC_lt S (n + 1))
  have hcL : Bc.bcC S n < Nc.ncL S ω := Bc.bcC_lt S n
  have h2 : Bc.bcB S n (Bc.bcC S n) < Bc.bcB S n (upsilon l) := (Bc.bcB_lt_iff hcL hρL).2 h1
  have h3 : Bc.bcB S n (Bc.bcC S n) = Nc.ncL S ω := Bc.bcB_base n
  rw [h3, hB, ← he] at h2
  exact lt_asymm h2 hρL

/-- STATUS: PROVED (Wd.wdFar_MW, Rn.rnThP_le_MW)
SIZE: S
the reading move at every code ≥ θ⁺ gives the far reading move (far codes are > M_W ≥ θ⁺). -/
theorem skThFar_of_top (h : SkThTop S) : SkThFar S := by
  intro n l l' hW hw
  have hW' := hW
  obtain ⟨hR, -, hr, -, -, -⟩ := hW
  exact h n l l' hW' (Rn.rnThP_le_MW.trans (Wd.wdFar_MW hR hr hw).le)

/-- STATUS: PROVED (definitions only)
SIZE: S
the reading move at every code ≥ θ⁺ gives WdThHi. -/
theorem skThHi_of_top (h : SkThTop S) : Wd.WdThHi S :=
  fun n l l' hR h1 hr hl' hB hm hP _ => h n l l' ⟨hR, h1, hr, hl', hB, hm⟩ hP

/-- STATUS: PROVED (Wa.waEQtop_of_EQ, Wa.waEQtop_iff, Cd.cdk_inj)
SIZE: S
NON-VACUITY: hν ∧ CdEQ (the road's target) ∧ SkKFar ⇒ SkThFar. -/
theorem skThFar_of_EQ (hν : Nc.ncL S (ω + 1) ≤ nuC) (hEQ : CdEQ S) (hK : SkKFar S) : SkThFar S := by
  intro n l l' hW hw
  have hlong := (Wa.waEQtop_iff hν).1 (Wa.waEQtop_of_EQ hEQ)
  have hW' := hW
  obtain ⟨hR, h1, hr, hl', hB, hm⟩ := hW
  have hE : Bc.bcB S n (cdR S l) = cdR S l' := hlong n l l' hR h1 hr hl' hB hm
  rw [sk_cdR_eq, sk_cdR_eq, ← hK n l l' hW' _ hw le_rfl, cdk_inj] at hE
  exact hE

/-- STATUS: PROVED (Wa.waEQtop_iff, Wa.waEQtop_of_EQ)
SIZE: S
NON-VACUITY: hν ∧ CdEQ ∧ SkThFar ⇒ k_{λ'}(B_n Θ) = B_n k_λ(Θ) at Θ = Θ_λ(m_λ) (the top index of SkKFar). -/
theorem skKTop_of_EQ (hν : Nc.ncL S (ω + 1) ≤ nuC) (hEQ : CdEQ S) (hT : SkThFar S) {n : ℕ}
    {l l' : Ordinal.{0}} (hW : SkWin S n l l') (hw : cdDelta l * ω ≤ cdTheta S l (cdCode S l)) :
    cdk l' (Bc.bcB S n (cdTheta S l (cdCode S l))) = Bc.bcB S n (cdk l (cdTheta S l (cdCode S l))) := by
  have hlong := (Wa.waEQtop_iff hν).1 (Wa.waEQtop_of_EQ hEQ)
  have hW' := hW
  obtain ⟨hR, h1, hr, hl', hB, hm⟩ := hW
  have hE : Bc.bcB S n (cdR S l) = cdR S l' := hlong n l l' hR h1 hr hl' hB hm
  rw [hT n l l' hW' hw, ← sk_cdR_eq]
  exact hE.symm

/-- STATUS: PROVED (Xg.xgCof_of_cont)
SIZE: S
skKCof at the indices where B_n is continuous (every Q < B_n p is ≤ some B_n q, q < p). -/
theorem skKCof_cont {n : ℕ} {l l' p : Ordinal.{0}} (hW : SkWin S n l l')
    (hp : p ≤ cdTheta S l (cdCode S l)) (hcof : ∀ q < p, cdk l q < p)
    (hIH : ∀ q < p, cdk l' (Bc.bcB S n q) = Bc.bcB S n (cdk l q))
    (hcont : ∀ Q < Bc.bcB S n p, ∃ q < p, Q ≤ Bc.bcB S n q) :
    ∀ Q < Bc.bcB S n p, cdk l' Q < Bc.bcB S n p :=
  Xg.xgCof_of_cont hW hp hcof hIH hcont

/-- STATUS: PROVED (Xg.xgCof_of_far, Xg.xgKReach_of)
SIZE: S
NON-VACUITY: hν ∧ SkKFar ∧ skKReachR ⇒ skKCof (the leaf asks nothing beyond its parent and the reach move). -/
theorem skKCof_of_far (hν : Nc.ncL S (ω + 1) ≤ nuC) (hK : SkKFar S) (hR : Xg.XgKReachR S) : Xg.XgKCof S :=
  Xg.xgCof_of_far hν hK (Xg.xgKReach_of hν hR)

/-- STATUS: PROVED (Xg.xgKReachR_of_EQ)
SIZE: S
NON-VACUITY: hν ∧ CdUPPER ∧ CdLOWER ∧ CdEQ (the road's target) ⇒ skKReachR. -/
theorem skKReachR_of_target (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S)
    (hEQ : CdEQ S) : Xg.XgKReachR S :=
  Xg.xgKReachR_of_EQ hν hU hL hEQ

/-- STATUS: PROVED (skThFar_of_EQ, Xg.xgKFar_of_R, Xg.xgKReachR_of_EQ)
SIZE: S
NON-VACUITY: hν ∧ CdUPPER ∧ CdLOWER ∧ CdEQ ∧ skKCof ⇒ SkKFar ∧ SkThFar. -/
theorem skThFar_of_target (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S)
    (hEQ : CdEQ S) (hC : Xg.XgKCof S) : SkKFar S ∧ SkThFar S := by
  have hK : SkKFar S := Xg.xgKFar_of_R hν hC (Xg.xgKReachR_of_EQ hν hU hL hEQ)
  exact ⟨hK, skThFar_of_EQ hν hEQ hK⟩

/-- STATUS: PROVED (Xn.xnTop_of_EQtop, Wa.waEQtop_of_EQ)
SIZE: S
NON-VACUITY: hν ∧ CdUPPER ∧ CdLOWER ∧ CdEQ (the road's target) ⇒ skEQTopR. -/
theorem skEQTopR_of_target (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) (hEQ : CdEQ S) :
    Xn.XnTop S :=
  Xn.xnTop_of_EQtop hν hU hL (Wa.waEQtop_of_EQ hEQ)

/-- STATUS: PROVED (Xn.xnTop_of_wf, Xn.xnEQ_all_wf: lexicographic induction on (r(λ), top relation))
SIZE: S
SkThFar ∧ XgKCof ∧ the top relation well-founded (Xn.XnChainWF; e.g. codes decreasing along it,
Xn.xnChainWF_of_code) ⇒ skEQTopR. -/
theorem skEQTopR_of_wf (hRead : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdAtWall S ∧ Wd.WdThHi S) (hUH : SkUH S)
    (hLH : SkLH S) (hν : Nc.ncL S (ω + 1) ≤ nuC) (hTF : SkThFar S) (hC : Xg.XgKCof S)
    (hWF : Xn.XnChainWF S) : Xn.XnTop S :=
  Xn.xnTop_of_wf hν (skEnum hUH hLH).1 (skEnum hUH hLH).2 (skThLow hRead hν) hTF hC hWF

/-- STATUS: PROVED (Xn.xnCof_of_blk)
SIZE: S
one block of closed points of λ' per Q < B_n p (y ∈ K_{λ'}, Q < y·ω, y + Q < B_n p) ⇒ skKCof. -/
theorem skKCof_of_blk (h : Xn.XnCofBlk S) : Xg.XgKCof S := Xn.xnCof_of_blk h

/-- STATUS: PROVED (Xn.xnCof_iff_unbdd)
SIZE: S
for indecomposable X = B_n p: the conclusion of skKCof at p ⇔ K_{λ'} unbounded below X. -/
theorem skKCof_iff_unbdd {l' X : Ordinal.{0}} (hX : Indec X) :
    (∀ Q < X, cdk l' Q < X) ↔ (∀ Q < X, ∃ y ∈ cdK l', Q ≤ y ∧ y < X) :=
  Xn.xnCof_iff_unbdd hX

end R2Skel.SkE

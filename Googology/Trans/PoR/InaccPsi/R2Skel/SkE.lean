import Googology.Trans.PoR.InaccPsi.R2.WdRoad
import Googology.Trans.PoR.InaccPsi.R2.XgReach
import Googology.Trans.PoR.InaccPsi.R2.XnRoad
import Googology.Trans.PoR.InaccPsi.R2.XrTop
import Googology.Trans.PoR.InaccPsi.R2.XrCof
import Googology.Trans.PoR.InaccPsi.R2.XsTop
import Googology.Trans.PoR.InaccPsi.R2.XsRef
import Googology.Trans.PoR.InaccPsi.R2.XwFirst
import Googology.Trans.PoR.InaccPsi.R2.XwGap
import Googology.Trans.PoR.InaccPsi.R2.XwJump

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
    * `skThFar` REDUCED (round 124, `Xs.xsFar_of_top`): child `skTopK` (OPEN, `Xs.XsTopK`: the reading move at
      every window code `≥ K_ω`; shared with SkR).
    * `skKFar` REDUCED (round 116, `Xg.xgKFar_of_R`): induction on `p`; below `δ_λ·ω` `Wd.wdk_move`; inside a
      block `[k_λ(q), k_λ(q)·ω)` (`Xg.xgK_add`, `Xg.xgk_add`: `k_λ(q+Z) = k_λ(q)+Z`) the move is carried from `q`;
      at a cofinal index `p` (`k_λ(q) < p` for `q < p`) `k_λ(p)` is the `R₂^C`-reach of `p` (`Xg.xgk_reach`),
      which moves at non-`υ`-points (`Xg.xgReach_nonUps`) and at non-range `υ`-points (`Xg.xgKReach_of`).
      * `skKCof` REDUCED (round 124, `Xr.xrKCof_of_gap`): at a cofinal index `p`, `K_{λ'}` is cofinal below
        `B_n p`; below every `B_n q` (`q < p`) from the move below `p` (`Xr.xrKCof_below`).
        * `skKCofGap` REDUCED (round 125, `Xw.xwKCofGap_of_lh`): the same only for `Q` in the jump gap
          `sup_{q<p} B_n q ≤ Q < B_n p` (`Xr.XrKCofGap`); at a decomposable `p` it holds outright (`Xw.xwDecomp`).
          * `skGapLh` OPEN: at an indecomposable cofinal far index `p`, every point `a` of the jump gap has its
            reach `lh(a) < B_n p` (`Xw.XwGapLh`; equivalent to `skKCofGap`: `Xw.xwKCofGap_iff`; under ENUM-REACH
            split into range restarts `r(ν) < B_n p` and the other gap points: `Xw.xwGapLh_iff`).
      * `skKReachR` REDUCED (round 117, `Xn.xnPart`): EQ at the inner restarts by ONE induction on the predicted
        reach `r(λ)` (`Xn.xnEQ_all`): every inner `μ` with `ρ_μ < T_λ` has `r(μ) = k_λ(ρ_μ) < r(λ)`
        (`Xn.xnR_inner_lt`); only the TOP `ρ_μ = T_λ` has `r(μ) = r(λ)` (`Xn.xnR_inner_top`).
        * `skEQTopR` REDUCED (round 124, `Xr.xrTop`): one reach class at a time; the chain points of the class
          (range restarts of reach `R` whose images have reach `R'`) have no largest element (`Xr.xrPt_succ`); at
          their supremum `s`, `lh(s) = R` (`le1_of_cof_left`); where `B_n` is continuous at `s`, `lh(B_n s) = R'`,
          and `s` is either a chain point or a non-range point whose reach moves (`Wa.waTCtopOff`): `B_n R = R'`.
          * `skEQJump` REDUCED (round 125, `Xw.xwJump_of`): the same at a supremum `s` where `B_n` jumps
            (`Xr.XrJump`), split by the kind of `s` (`Xw.xwJump_iff`):
            * `skJumpOff` OPEN: `s` not a range restart: `B_n s ≤₁ R' = lh(s*)` (`Xw.XwJumpOff`; at such `s`,
              `B_n R = R' ⇔ B_n s ≤₁ R'`: `Xw.xwJump_off_iff`);
            * `skJumpNoRng` OPEN: no instance has a range restart as `s` (`Xw.XwJumpNoRng`; `XrJump` forces it,
              `Xw.xwJump_noRng_of`).
  * old children of `skKFar`, now off the path: `skKGap` PROVED (`Xg.xgKGap`), `skKClosed` and `skKLim`
    REDUCED to `skKFar` (`SkEX.skexClosed_of_far`, `SkEX.skexLim_of_far`).
Guards and links (PROVED): `skNoIdx` (the index-keeping move `k_{λ'}(p) = B_n(k_λ p)` is false at `p = ρ_λ`),
`skThFar_of_top` / `skThHi_of_top` (one reading move at every code `≥ θ⁺` gives both `skThFar` and `WdThHi`),
`skThFar_of_EQ` (`CdEQ` and `skKFar` give `skThFar`), `skKFar_of` (the old split), `skKCof_cont`,
`skKCof_of_far` (`SkKFar` and `skKReachR` give `skKCof`), `skKReachR_of_target`, `skThFar_of_target`
(`CdUPPER ∧ CdLOWER ∧ CdEQ ∧ skKCof` give `skThFar`: non-vacuity against the road's target), round 117:
`skEQTopR_of_target`, `skEQTopR_of_wf`, `skKCof_of_blk` (one block of closed points per `Q < B_n p` gives `skKCof`),
`skKCof_iff_unbdd` (for indecomposable `B_n p`: `skKCof` at `p` ⇔ `K_{λ'}` unbounded below `B_n p`), round 124 (leaf eq3):
`skEQJump_of_target`, `skEQJump_of_top`, `skEQJump_of_wf` (the new leaf follows from the target and from each of the
two older leaves `Xn.XnTop`, `Xn.XnChainWF`), `skEQJump_iff_gap`, `skKCofGap_iff`, `skKCofGap_unbdd`.
Round 124 (leaf far1): `skThFar` is REDUCED to the new shared leaf `skTopK` (`Xs.XsTopK`: the reading move at every
window code `m_λ ≥ K_ω`, `K_0 = 1`, `K_{j+1} = ψ_{Ω₂}(Ω_ω + Ω₂·K_j)`, `K_1 = M_W`) by `Xs.xsFar_of_top`: every far
window has `K_j ≤ m_λ` for all `j` (`skFarGe` = `Xs.xsFar_ge`), because the readings past `M_W` are now known on
`[M_W, K_ω)`: `Θ_λ(ψ_{Ω₂}(Ω_ω + Ω₂·γ + c)) = ψ_{Ω₁}(A + θ + Ω₁·Θ_λ γ + Θ_λ c)` (`Xs.xsBase`, `Xs.xsBlk`), all below
`δ_λ` (`Xs.xsRead_lt`).  The same leaf `skTopK` closes `SkR.skThFar` (with the wall `skWallCF`, `Xs.xsFarLow`) and
`SkThTop` (`skThTopK` = `Xs.xsThTop`); non-vacuity `skTopKTarget` (`Xs.xsTopK_of_target`).  REFUTE FIRST record
`skXsRef` (`Xs.xsRef_wit`: the level-down reading `ψ_{Ω₁}(A + θ + T d)` fails at every `d = Ω_{k+1}`, `k ≥ 2`).
Round 125 (leaf eq4): REFUTE-FIRST record at the first jump `p = c_n·2` (`skFirstJump` = `Xw.xwFirst`: gap
`[L(ω)+c_n, L(ω)·2)`, no `υ`-point and no closed point of any image window in it; both leaves ask nothing there,
since `c_n·2 < δ_λ·ω` and every chain point is `> c_n·2`).  `skKCofGap` REDUCED to `skGapLh`, `skEQJump` REDUCED to
`skJumpOff`, `skJumpNoRng`; guards `skKCofDecomp`, `skGapLh_iff`, `skGapLh_split`, `skGapLhTarget`, `skJump_iff`,
`skJumpTarget`.
This file imports the new modules `R2.XsTop`, `R2.XwFirst`, `R2.XwGap`, `R2.XwJump`: it can be checked only after
the merge.
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
REFUTE: NO EVIDENCE (round 124: follows from the target, skTopKTarget = Xs.xsTopK_of_target (hν ∧ CdEQ ∧ SkKFar);
a move statement, so no no-go result applies (Vo.voNoGo, Vn.vnTop_Om3, Vq.vqNoTop_Om3, Xi.xiTopFam_false,
Xd.xdX0Law_false speak of reach forms or top laws); the readings it needs are unknown past K_ω, and the natural
level-down reading is REFUTED there, skXsRef)
NEW leaf (round 124), shared with SkR (the one copy; `SkR.skTopK` is REDUCED to it).
∀ window λ → λ', (∀ j, K_j ≤ m_λ) ⇒ B_n Θ_λ(m_λ) = Θ_{λ'}(m_{λ'})  (statement Xs.XsTopK S; K_ω = sup_j K_j,
K_{j+1} = ψ_{Ω₂}(Ω_ω + Ω₂·K_j)).  Next readings: the plateau K_ω (expected ψ_{Ω₁}(A + θ + Ω₁²)), the bases
Ω_ω + Ω₂^e·δ, then the ψ₃-atoms where the level-down value ψ_{Ω₁}(A + θ + T d) is false (xsRefK). -/
theorem skTopK (hν : Nc.ncL S (ω + 1) ≤ nuC) : Xs.XsTopK S := by sorry

/-- STATUS: REDUCED (round 124; was OPEN)
SIZE: S
∀ far window: B_n Θ_λ(m_λ) = Θ_{λ'}(m_{λ'})  (child skTopK; Xs.xsFar_of_top: far codes are ≥ K_ω, skFarGe;
checkable after the merge of R2.XsRd, R2.XsMv, R2.XsTop). -/
theorem skThFar (hν : Nc.ncL S (ω + 1) ≤ nuC) : SkThFar S :=
  fun n l l' hW hw => Xs.xsFar_of_top (skTopK hν) n l l' hW hw

/-- STATUS: OPEN
SIZE: L
REFUTE: NO EVIDENCE (round 125: equivalent to skKCofGap and to XgKCof, skGapLh_iff (Xw.xwKCofGap_iff, Xw.xwKCof_iff);
follows from hν ∧ CdUPPER ∧ CdLOWER ∧ CdEQ ∧ SkKFar, skGapLhTarget; at the first jump p = c_n·2 the gap
[L(ω)+c_n, L(ω)·2) has no closed point of λ' (skFirstJump), but p = c_n·2 is no far index; no no-go result
(Vo.voNoGo, Vn.vnTop_Om3, Vq.vqNoTop_Om3, Vx.vxNoCompat, Wb.*, Wc.*, Xd.xdX0Law_false, Xi.xiTopFam_false) speaks of
reaches in (L(ω), L(ω+1)))
NEW leaf (round 125).  window λ → λ', cofinal far index p (δ_λ·ω ≤ p ≤ Θ_λ(m_λ), k_λ(q) < p for q < p) with p
indecomposable and the k-move below p, a in the jump gap (B_n q ≤ a < B_n p for all q < p)  ⇒  lh(a) < B_n p
(statement Xw.XwGapLh S).  Under ENUM-REACH: r(ν) < B_n p at every range restart ν in the gap, and lh(a) < B_n p at
the other gap points (skGapLh_split). -/
theorem skGapLh (hν : Nc.ncL S (ω + 1) ≤ nuC) : Xw.XwGapLh S := by sorry

/-- STATUS: REDUCED (round 125; was OPEN)
SIZE: S
REFUTE: SURVIVED (round 124: equivalent to the old skKCof, skKCofGap_iff (Xr.xrKCof_iff_gap); empty where B_n is
continuous at p, Xr.xrKCof_gap_empty; for indecomposable B_n p exactly the unboundedness of K_{λ'} in the gap,
skKCofGap_unbdd; implied by SkKFar ∧ skKReachR via skKCof_of_far; no no-go result (Vo.voNoGo, Vn.vnTop_Om3,
Vq.vqNoTop_Om3, Vx.vxNoCompat, Wb.*, Wc.*, Xd.xdX0Law_false, Xi.xiTopFam_false) speaks of closed points; the gap
points (in (L(ω), L(ω+1))) are not images of any B_m, and no Lean value of their reaches is known)
cofinal far index p, move below p, Q in the jump gap (B_n q ≤ Q for all q < p, Q < B_n p)
⇒ k_{λ'}(Q) < B_n p  (statement Xr.XrKCofGap S).  Child skGapLh (Xw.xwKCofGap_of_lh: at a decomposable p the
block of closed points at k_{λ'}(B_n u), p = u + w, covers the gap, Xw.xwDecomp; at an indecomposable p the reach of
the least point a₀ ≤ Q reaching past Q is a closed point of λ' in [Q, B_n p), Xw.xwClosed_at; checkable after the
merge of R2.XwFirst, R2.XwGap). -/
theorem skKCofGap (hν : Nc.ncL S (ω + 1) ≤ nuC) : Xr.XrKCofGap S := Xw.xwKCofGap_of_lh (skGapLh hν)

/-- STATUS: OPEN
SIZE: L
REFUTE: NO EVIDENCE (round 125: follows from the target, skJumpTarget (Xw.xwJump_of_EQtop), and from the old leaves
Xn.XnTop, Xn.XnChainWF (Xw.xwJump_of_top, Xw.xwJump_of_wf); vacuous at the first jump s = c_n·2, skFirstJump; no
no-go result speaks of ≤₁ between B_n s and the reach of the gap bottom)
NEW leaf (round 125).  An instance of Xr.XrJump (n, R, R', s with all its hypotheses) whose jump point s is not a
range restart  ⇒  B_n s ≤₁ R' (= lh(s*), s* = sup_{q<s} B_n q, Xr.xrGap_reach)  (statement Xw.XwJumpOff S; at such s
the conclusion B_n R = R' of XrJump is equivalent to it, Xw.xwJump_off_iff). -/
theorem skJumpOff (hν : Nc.ncL S (ω + 1) ≤ nuC) : Xw.XwJumpOff S := by sorry

/-- STATUS: OPEN
SIZE: L
REFUTE: NO EVIDENCE (round 125: follows from the target, skJumpTarget; XrJump forces it, Xw.xwJump_noRng_of;
vacuous at s = c_n·2, skFirstJump; not derivable from skJumpOff alone: EQ at the range point s = ρ_μ fails exactly
when B_n R = R' ≠ r(μ'), and the reach class (R, r(μ')) only yields a new range instance above s)
NEW leaf (round 125).  No instance of Xr.XrJump has a range restart ρ_μ as its jump point s
(statement Xw.XwJumpNoRng S). -/
theorem skJumpNoRng (hν : Nc.ncL S (ω + 1) ≤ nuC) : Xw.XwJumpNoRng S := by sorry

/-- STATUS: REDUCED (round 125; was OPEN)
SIZE: S
REFUTE: SURVIVED (round 124: follows from the target, skEQJump_of_target (CdEQ ⇒ CxEQtop ⇒ Xr.XrJump); weaker than
the old leaf Xn.XnTop (Xr.xrJump_of_top) and than the well-foundedness guard Xn.XnChainWF (Xr.xrJump_of_wf); no
no-go result speaks of EQ at range restarts or of reaches at the jumps of B_n; the top relation was NOT shown
well-founded and NOT refuted: no reading Θ_λ above M_W, so no code along a top chain is computable at the witness
windows (Vo, wwX); an infinite chain is not excluded (its supremum s has lh(s) = R, it is handled by xrClass where
B_n is continuous at s))
NEW leaf (round 124).  n, R < c_{n+1}, EQ below R, the chain points of (R, R') cofinal below s and none ≥ s,
lh(s) = R, B_n jumps at s (∃ Q < B_n s, ∀ q < s, B_n q ≤ Q)  ⇒  B_n R = R'  (statement Xr.XrJump S; the part's
other hypotheses hν, ENUM, WdThLow, SkThFar, XgKCof are premises of the statement).  Children skJumpOff,
skJumpNoRng (Xw.xwJump_of; checkable after the merge of R2.XwFirst, R2.XwGap, R2.XwJump). -/
theorem skEQJump (hν : Nc.ncL S (ω + 1) ≤ nuC) : Xr.XrJump S := Xw.xwJump_of (skJumpOff hν) (skJumpNoRng hν)

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

/-- STATUS: REDUCED (Xr.xrKCof_of_gap; checkable after the merge of R2.XrCof)
SIZE: S
skKCofGap ⇒ XgKCof: below every B_n q (q < p) from the move below p (Xr.xrKCof_below). -/
theorem skKCof (hν : Nc.ncL S (ω + 1) ≤ nuC) : Xg.XgKCof S := Xr.xrKCof_of_gap (skKCofGap hν)

/-- STATUS: REDUCED (Xr.xrTop; checkable after the merge of R2.XrTop)
SIZE: L
hRead, hUH, hLH, hν ⇒ Xn.XnTop  (children skEQJump, skThFar, skKCof, and skThLow, skEnum; xrClass: the chain
points of a reach class have no largest element, their supremum s has lh(s) = R; where B_n is continuous at s the
reach moves (s a chain point or Wa.waTCtopOff); left: the jumps of B_n). -/
theorem skEQTopR (hRead : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdAtWall S ∧ Wd.WdThHi S) (hUH : SkUH S)
    (hLH : SkLH S) (hν : Nc.ncL S (ω + 1) ≤ nuC) : Xn.XnTop S :=
  Xr.xrTop hν (skEnum hUH hLH).1 (skEnum hUH hLH).2 (skThLow hRead hν) (skThFar hν) (skKCof hν) (skEQJump hν)

/-- STATUS: REDUCED
SIZE: L
hRead, hUH, hLH, hν ⇒ XgKReachR  (children skThFar, skKCof, skEQTopR; Xn.xnPart: the induction on r(λ),
Xn.xnEQ_all; checkable after the merge of R2.XnLow, R2.XnInd, R2.XnRoad). -/
theorem skKReachR (hRead : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdAtWall S ∧ Wd.WdThHi S) (hUH : SkUH S)
    (hLH : SkLH S) (hν : Nc.ncL S (ω + 1) ≤ nuC) : Xg.XgKReachR S :=
  (Xn.xnPart hν (hRead hν).1 (hRead hν).2 (skEnum hUH hLH).1 (skEnum hUH hLH).2 (skThFar hν) (skKCof hν)
    (skEQTopR hRead hUH hLH hν)).2.2.1


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

/-- STATUS: PROVED (Xr.xrJump_of_EQtop, Wa.waEQtop_of_EQ)
SIZE: S
NON-VACUITY: CdEQ (the road's target) ⇒ skEQJump. -/
theorem skEQJump_of_target (hEQ : CdEQ S) : Xr.XrJump S := Xr.xrJump_of_EQtop (Wa.waEQtop_of_EQ hEQ)

/-- STATUS: PROVED (Xr.xrJump_of_top)
SIZE: S
the old leaf Xn.XnTop ⇒ skEQJump (the new leaf is weaker). -/
theorem skEQJump_of_top (h : Xn.XnTop S) : Xr.XrJump S := Xr.xrJump_of_top h

/-- STATUS: PROVED (Xr.xrJump_of_wf)
SIZE: S
the well-foundedness of the top relation (Xn.XnChainWF) ⇒ skEQJump. -/
theorem skEQJump_of_wf (h : Xn.XnChainWF S) : Xr.XrJump S := Xr.xrJump_of_wf h

/-- STATUS: PROVED (Xr.xrJump_iff_gap, Xr.xrGap_reach)
SIZE: S
skEQJump ⇔ at the jump, the gap bottom s* = sup_{q<s} B_n q has lh(s*) = B_n R. -/
theorem skEQJump_iff_gap : Xr.XrJump S ↔ Xr.XrJumpGap S := Xr.xrJump_iff_gap

/-- STATUS: PROVED (Xr.xrKCof_iff_gap)
SIZE: S
skKCofGap ⇔ the old skKCof statement Xg.XgKCof. -/
theorem skKCofGap_iff : Xg.XgKCof S ↔ Xr.XrKCofGap S := Xr.xrKCof_iff_gap

/-- STATUS: PROVED (Xr.xrKCof_gap_unbdd, Xn.xnCof_iff_unbdd)
SIZE: S
for indecomposable B_n p: the leaf at p ⇔ K_{λ'} unbounded in the jump gap. -/
theorem skKCofGap_unbdd {n : ℕ} {l l' p : Ordinal.{0}} (hW : R2Skel.SkEX.SkWin S n l l')
    (hp : p ≤ cdTheta S l (cdCode S l)) (hcof : ∀ q < p, cdk l q < p)
    (hIH : ∀ q < p, cdk l' (Bc.bcB S n q) = Bc.bcB S n (cdk l q)) (hX : Indec (Bc.bcB S n p)) :
    (∀ Q < Bc.bcB S n p, (∀ q < p, Bc.bcB S n q ≤ Q) → cdk l' Q < Bc.bcB S n p) ↔
      (∀ Q < Bc.bcB S n p, (∀ q < p, Bc.bcB S n q ≤ Q) → ∃ y ∈ cdK l', Q ≤ y ∧ y < Bc.bcB S n p) :=
  Xr.xrKCof_gap_unbdd hW hp hcof hIH hX

/-! ## Round 124 (leaf far1): readings past `M_W` -/

open Googology.Notation.InaccPsi.InaccSeq in
/-- STATUS: PROVED (Xs.xsFar_ge, from Xs.xsBase, Xs.xsRead_lt, Xs.xsA_win; NEW round 124)
SIZE: S
GUARD: every far window has K_j ≤ m_λ for every j (K_1 = M_W; was: m_λ > M_W, Wd.wdFar_MW). -/
theorem skFarGe {n : ℕ} {l l' : Ordinal.{0}} (hW : SkWin S n l l')
    (hw : cdDelta l * ω ≤ cdTheta S l (cdCode S l)) : ∀ j, Xs.xsK S j ≤ cdCode S l := by
  obtain ⟨hR, h1, hr, -, -, -⟩ := hW
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans hδr
  obtain ⟨hX, hown⟩ := Ld.ldOwnA hR.1 h2
  exact Xs.xsFar_ge hR.1 hX hown (Xs.xsAb_of (Xs.xsA_win hR.1 h1 h2))
    (hR.2.2.2.trans (psi_lt (InR_Om_succ 1) _ : Nc.ncPp S < Om (1 + 1))).le hw

/-- STATUS: PROVED (Xs.xsThTop, from Xs.xsMove, Wr.wrMid; NEW round 124)
SIZE: S
WrWallCF ∧ skTopK ⇒ SkThTop (the reading move at every window code ≥ θ⁺; with skThFar_of_top, skThHi_of_top
it gives skThFar and WdThHi). -/
theorem skThTopK (hW : Wr.WrWallCF S) (hT : Xs.XsTopK S) : SkThTop S :=
  fun n l l' hW' hP => Xs.xsThTop hW hT n l l' hW' hP

/-- STATUS: PROVED (Xs.xsTopK_of_target, from Wa.waEQtop_iff, Xn.xnTh_of_EQ; NEW round 124)
SIZE: S
NON-VACUITY: hν ∧ CdEQ (the road's target) ∧ SkKFar ⇒ skTopK. -/
theorem skTopKTarget (hν : Nc.ncL S (ω + 1) ≤ nuC) (hEQ : CdEQ S) (hK : SkKFar S) : Xs.XsTopK S :=
  Xs.xsTopK_of_target hν hEQ hK

/-- STATUS: PROVED (Xs.xsRef_wit, from Xs.xsRefK, Ld.ldTheta_le_psi, Vb.vbT_Om; NEW round 124; a REFUTE-FIRST record,
no node uses it)
SIZE: S
REFUTED candidate: Θ_λ(ψ_{Ω₂}(Ω_ω + d)) = ψ_{Ω₁}(A + θ + T d) (T = Vb.vbT, the level map one level down) fails at
d = Ω_{k+1} for every k ≥ 2 at the restart of m* = L(0); the tests M_W + 1, M_W·2 hold there. -/
theorem skXsRef (S : InaccSeq.{0}) :
    ∃ l : Ordinal.{0}, IsRestartIdx l ∧ upsilon l = Nc.ncL S 0 ∧
      Om ω + Om ω ≤ ConjT.Aη S (cdEta S l) ∧
      (∀ k : ℕ, 2 ≤ k →
        Mx.gxTh (upsilon l) (Ld.ldAtR S l) (S.psi (Om ω + Om ((k : Ordinal.{0}) + 1)) (Om (1 + 1))) <
          S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + Vb.vbT S l (Om ((k : Ordinal.{0}) + 1))) (Om 1)) ∧
      Mx.gxTh (upsilon l) (Ld.ldAtR S l) (Rn.rnMW S + 1) =
        S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + Om 1) (Om 1) + 1 ∧
      Mx.gxTh (upsilon l) (Ld.ldAtR S l) (Rn.rnMW S * 2) =
        S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + Om 1) (Om 1) * 2 :=
  Xs.xsRef_wit S

/-! ## Round 125 (leaf eq4): the jump gaps -/

/-- STATUS: PROVED (Xw.xwFirst; NEW round 125; a REFUTE-FIRST record, no node uses it)
SIZE: S
At the first jump p = c_n·2: B_n p = L(ω)·2, B_n q < L(ω) + c_n for q < p (gap [L(ω)+c_n, L(ω)·2), nonempty), no
indecomposable ordinal (so no υ-point) in the gap, and for every window c_n·2 < δ_λ·ω (p is no far index) and no
point of K_{λ'} below L(ω)·2 (the closed points of λ' are NOT unbounded in this gap); no chain point is cofinal
below c_n·2 (both leaves vacuous there). -/
theorem skFirstJump (n : ℕ) :
    Bc.bcB S n (Bc.bcC S n * 2) = Nc.ncL S ω * 2 ∧
    (∀ q < Bc.bcC S n * 2, Bc.bcB S n q < Nc.ncL S ω + Bc.bcC S n) ∧
    Nc.ncL S ω + Bc.bcC S n < Nc.ncL S ω * 2 ∧
    (∀ x, Nc.ncL S ω + Bc.bcC S n ≤ x → x < Nc.ncL S ω * 2 → ¬ Indec x) ∧
    (∀ l l', R2Skel.SkEX.SkWin S n l l' →
      Bc.bcC S n * 2 < cdDelta l * ω ∧ ∀ y ∈ cdK l', Nc.ncL S ω * 2 < y) ∧
    (∀ R R' : Ordinal.{0}, ¬ ∀ x < Bc.bcC S n * 2, ∃ y, x < y ∧ y < Bc.bcC S n * 2 ∧ Xr.XrPt S n R R' y) :=
  Xw.xwFirst n

/-- STATUS: PROVED (Xw.xwDecomp; NEW round 125)
SIZE: S
At a decomposable cofinal far index p the conclusion of XgKCof holds (no hypothesis on the gap). -/
theorem skKCofDecomp {n : ℕ} {l l' p : Ordinal.{0}} (hW : R2Skel.SkEX.SkWin S n l l')
    (hfar : cdDelta l * ω ≤ p) (hp : p ≤ cdTheta S l (cdCode S l)) (hcof : ∀ q < p, cdk l q < p)
    (hIH : ∀ q < p, cdk l' (Bc.bcB S n q) = Bc.bcB S n (cdk l q)) (hI : ¬ Indec p) :
    ∀ Q < Bc.bcB S n p, cdk l' Q < Bc.bcB S n p :=
  Xw.xwDecomp hW hfar hp hcof hIH hI

/-- STATUS: PROVED (Xw.xwKCofGap_iff, Xw.xwKCof_iff; NEW round 125)
SIZE: S
skGapLh ⇔ skKCofGap ⇔ XgKCof (unconditional). -/
theorem skGapLh_iff : (Xr.XrKCofGap S ↔ Xw.XwGapLh S) ∧ (Xg.XgKCof S ↔ Xw.XwGapLh S) :=
  ⟨Xw.xwKCofGap_iff, Xw.xwKCof_iff⟩

/-- STATUS: PROVED (Xw.xwGapLh_iff; NEW round 125)
SIZE: S
Under ENUM-REACH: skGapLh ⇔ (r(ν) < B_n p at the range restarts ν in the gap) ∧ (lh(a) < B_n p at the other gap
points). -/
theorem skGapLh_split (hU : CdUPPER S) (hL : CdLOWER S) : Xw.XwGapLh S ↔ Xw.XwGapRst S ∧ Xw.XwGapOff S :=
  Xw.xwGapLh_iff hU hL

/-- STATUS: PROVED (Xw.xwGapLh_of_target; NEW round 125)
SIZE: S
NON-VACUITY: hν ∧ CdUPPER ∧ CdLOWER ∧ CdEQ ∧ SkKFar ⇒ skGapLh. -/
theorem skGapLhTarget (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) (hEQ : CdEQ S)
    (hK : R2Skel.SkEX.SkKFar S) : Xw.XwGapLh S :=
  Xw.xwGapLh_of_target hν hU hL hEQ hK

/-- STATUS: PROVED (Xw.xwJump_iff; NEW round 125)
SIZE: S
skEQJump ⇔ skJumpOff ∧ skJumpNoRng (unconditional). -/
theorem skJump_iff : Xr.XrJump S ↔ Xw.XwJumpOff S ∧ Xw.XwJumpNoRng S := Xw.xwJump_iff

/-- STATUS: PROVED (Xw.xwJump_of_EQtop; NEW round 125)
SIZE: S
NON-VACUITY: CdEQ (the road's target) ⇒ skJumpOff ∧ skJumpNoRng. -/
theorem skJumpTarget (hEQ : CdEQ S) : Xw.XwJumpOff S ∧ Xw.XwJumpNoRng S :=
  Xw.xwJump_of_EQtop (Wa.waEQtop_of_EQ hEQ)

end R2Skel.SkE

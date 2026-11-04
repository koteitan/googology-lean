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
import Googology.Trans.PoR.InaccPsi.R2.YeComp
import Googology.Trans.PoR.InaccPsi.R2.YeGap
import Googology.Trans.PoR.InaccPsi.R2.YeJump
import Googology.Trans.PoR.InaccPsi.R2.YkBlk
import Googology.Trans.PoR.InaccPsi.R2.YkJump
import Googology.Trans.PoR.InaccPsi.R2.YuEps
import Googology.Trans.PoR.InaccPsi.R2.YzJump
import Googology.Trans.PoR.InaccPsi.R2.ZeJump
import Googology.Trans.PoR.InaccPsi.R2.ZeGap

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
          * `skGapLh` REDUCED (round 126, `Ye.yeGapLh_of`): at an indecomposable cofinal far index `p`, every
            point `a` of the jump gap has its reach `lh(a) < B_n p` (`Xw.XwGapLh`); under `hν` the gap points
            that are no `υ`-point and either no `ε`-number or below a `υ`-point `≤ B_n p` are done by the
            `R₁⁺`-reach (`Ye.yeLh_easy`); left:
            * `skGapEps` REDUCED (round 129) to `skGapEpsTop`, PROVED (round 130, `Yz.yzGapEpsTop`): gap
              `ε`-numbers, no `υ`-point, no `υ`-point in `(a, B_n p]` (`Ye.YeGapEps`);
            * `skGapRng` REDUCED (round 130, `Yz.yzGapRng_of_hi`, under ENUM-REACH): `p` a restart, gap points
              `υ_l`, `l` a restart index (`Ye.YeGapRng`); child `skGapRngHi` OPEN (codes `m_l > θ·ω`);
            * `skGapBlk` PROVED (round 127, `Yk.ykGapBlk`): `p` a restart, gap `υ`-points inside a block: the
              block top `< B_n p` (`B_n p = υ_{κ'}`, `κ'` a restart index, restart indices are `ω·ω` apart).
            At a non-restart `p` the gap contains no `υ`-point (`Ye.yeNoUps_off`, from `Sf.sfShiftAll`).
      * `skKReachR` REDUCED (round 117, `Xn.xnPart`): EQ at the inner restarts by ONE induction on the predicted
        reach `r(λ)` (`Xn.xnEQ_all`): every inner `μ` with `ρ_μ < T_λ` has `r(μ) = k_λ(ρ_μ) < r(λ)`
        (`Xn.xnR_inner_lt`); only the TOP `ρ_μ = T_λ` has `r(μ) = r(λ)` (`Xn.xnR_inner_top`).
        * `skEQTopR` REDUCED (round 124, `Xr.xrTop`): one reach class at a time; the chain points of the class
          (range restarts of reach `R` whose images have reach `R'`) have no largest element (`Xr.xrPt_succ`); at
          their supremum `s`, `lh(s) = R` (`le1_of_cof_left`); where `B_n` is continuous at `s`, `lh(B_n s) = R'`,
          and `s` is either a chain point or a non-range point whose reach moves (`Wa.waTCtopOff`): `B_n R = R'`.
          * `skEQJump` REDUCED (round 125, `Xw.xwJump_of`): the same at a supremum `s` where `B_n` jumps
            (`Xr.XrJump`), split by the kind of `s` (`Xw.xwJump_iff`):
            * `skJumpOff` PROVED (round 126, `Ye.yeJumpOff`): vacuous, the jump point `s` is always a range
              restart (`Ye.yeJump_rst`: `s = υ_l`, `l` the supremum of the chain indices, `ω² ∣ l`);
            * `skJumpNoRng` PROVED (round 131, `Ze.zeJumpNoRng`, from `hVt`): no instance has a range restart as
              `s` (`Xw.XwJumpNoRng`; `XrJump` forces it,
              `Xw.xwJump_noRng_of`); equivalently (round 127, `Yk.ykNoRng_iff_gap`) the range restart `κ` at the
              bottom of the jump gap (`s* = sup_{q<s} B_n q = υ_κ`, no `B_n`-image, `r(κ) = R'`, `skJumpGapBot`)
              has `r(κ) = B_n R`, i.e. it reaches past the gap (`skJumpGapShort`).
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
Round 126 (leaf eq5): the composition of base changes `B_m ∘ C_{n,m} = B_n` (`C_{n,m} = τ_m ∘ B_n`, `τ_m` the
`B_m`-preimage of `R2.BcOnto`), pointwise for every large `m` (`skComp` = `Ye.yeComp`, `skCompFin`); REFUTE-FIRST at
`n = 0`, `m = 1` (`skComp01` = `Ye.ye01`: `C_{0,1}(c_1) = c_2`, `B_1 ∘ C_{0,1} = B_0` at `c_1` and at the first jump;
no counterexample); the jump gap of `B_n` is the `B_m`-image of the gap of `C_{n,m}` (`skGapPre`), and the
gap-reach question moves to the window `m` (`skGapLhPre`); `skJumpOff` PROVED (`skJumpRst`), so
`skEQJump ⇔ skJumpNoRng` (`skJumpOnlyRng`); `skGapLh` REDUCED to `skGapEps`, `skGapRng`, `skGapBlk`
(`skGapSplit3`, `skLhEasy`, `skUpsBlock`, non-vacuity `skGapTarget3`); a `υ`-point in the gap forces `p` to be a
restart (`skNoUpsOff` = `Ye.yeNoUps_off`, `skGapUpsRst`), so `skGapRng`, `skGapBlk` ask only restart indices `p`.
Round 127 (leaf eq6): `skGapBlk` PROVED (`Yk.ykGapBlk`, no hypothesis), so `skGapLh` has the children
`skGapEps`, `skGapRng` only (`Yk.ykGapLh_of`).  `skJumpNoRng` stays OPEN; guards: `skChainLe1` (every chain point is
`≤₁ s`), `skJumpGapBot` (`Yk.ykGapBot`: the gap bottom `s*` is `υ_κ`, `κ` a range restart, `L(ω) < υ_κ < B_n s`, no
`B_n`-image, `r(κ) = R'`), `skJumpGapIff` (`Yk.ykNoRng_iff_gap`: the leaf ⇔ `r(κ) = B_n R` at every instance),
`skJumpGapShort` (`Yk.ykGap_short_ne`: an instance with `lh(s*) < B_n s` has `B_n R ≠ R'`, so the leaf asks that no
such instance exists; the opposite direction to `skGapRng`), `skJumpGapTarget` (non-vacuity).
This file imports the new modules `R2.YeComp`, `R2.YeGap`, `R2.YeJump`, `R2.YkBlk`, `R2.YkJump`: it can be
checked only after the merge.
Round 129 (leaf eq8): `skGapEps` REDUCED to the new leaf `skGapEpsTop` (`Yu.yuGapEps_of_top`): a gap `ε`-number
forces `p` and `B_n p` to be `ε`-numbers (`skGapEpsPE`, `skGapEpsEN`: `ε_{a+1} ≤ B_n p`), and below the top level
(`a = ϑ^{υ_ξ}(ξ')`, `Ω₁ ≤ ξ' < Ω₁·ε_{Ω₁+1}`) the reach of `a` is below `ε_{a+1}` (`skLhLtEN`, from `Gq.gq_lh_th` and
`Rj.rj_lh`); only the gap `ε`-numbers with `ξ' ≥ Ω₁·ε_{Ω₁+1}` are left.  `skGapRng`, `skJumpNoRng` stay OPEN.
This file also imports the new module `R2.YuEps`: it can be checked only after the merge.
Round 130 (leaf eq9): `skGapEpsTop` PROVED (`Yz.yzGapEpsTop`): `lh(a) = lhᵗ(a) < a⁺` by the new cited axiom
`R2.yzLhT_lt_plus` ([W07b] Lemma 4.2, file `R2.CitedYz`; `skLhPlus`), and `a⁺ ≤ B_n p` with no hypothesis
(`skGapPlus` = `Yz.yzGapPlus`: the bracket base of `p` goes to `υ_ξ` by `Sf.sfShiftAll`, `B_n p = ϑ^{υ_ξ}(Δ_{B_n μ_p} +
B_n η_p)` by `Vj.vjVtE`, its data are `B_n`-images of data below `p`, hence below `a`, `Uo.uoDat_B`; a low-level `p`
is impossible).  `skGapRng` REDUCED (`Yz.yzGapRng_of_hi`, now with the hypotheses `CdUPPER`, `CdLOWER`, supplied by
`skEnum` through `skGapLh`, `skKCofGap`, `skKCof`, which now take `hUH`, `hLH`) to the new leaf `skGapRngHi`
(`Yz.YzGapRngHi`: only gap restarts with code `> θ·ω`; the short codes by `skGapRngLow` = `Yz.yzGapRng_low`, the
extension of `Rc.rcR_lowCode` above `L(ω)`, `Yz.yzR_lowCode`).  `skJumpNoRng` stays OPEN; new guards
`skJumpShortBot` (an instance whose gap bottom has a code `≤ θ·ω` has `r(κ) < B_n s`), `skJumpShortNoEQ` (such an
instance refutes the target), `skJumpSplit` (`Yz.yzJumpNoRng_iff`).
This file also imports the new modules `R2.CitedYz`, `R2.YzPlus`, `R2.YzRng`, `R2.YzJump`: it can be checked only
after the merge.
Round 131 (leaf eq10): the TOP NODE takes one more hypothesis of the road, `hVt : SkVt S` (CapV at the range
restarts in `(L(ω), L(ω+1))` above the frontier, `SkF.skFrontVt S`; below the frontier `Hl.hlU_capV`,
`Ze.zeCapHigh`); `Root.skNuC` applies `skEQ hRead (SkF.skFrontU S) (SkF.skFrontL S) (SkF.skFrontVt S)`.  With it:
`skJumpNoRng` PROVED (`Ze.zeJumpNoRng`: by the cap window `Ze.zeCap_win` below the gap bottom `ρ_κ`, a chain image
`ρ_{μ'}` near `ρ_κ` has `cap(μ') ≤ ρ_κ`, so CapV gives `R' = r(μ') < ρ_κ < r(κ) = R'`); its short-code half
`Yz.YzJumpShort` even with no hypothesis (`skJumpShortU` = `Ze.zeJumpShortU`: near `ρ_κ` the codes are `< θ·ω`,
`Ze.zeCode_win`, from the name window `Ze.zeName_win` and the bad-interval lemma `Ze.zeBad_top`); `skGapRngHi`
PROVED (`Ze.zeGapRngHi`, indeed `Ye.YeGapRng` for every code, `Ze.zeGapRng`: the cap window of `B_n p` reaches down
to a `B_n`-image, `Ze.zeGap_win`, computed through the argument terms of `P(η_κ)` and `B_n` on them, `Ze.zeB_term`,
`Ze.zeVal_split`, `Ze.ze_cancel_last`).  The nodes on the path `skGapRng`, `skGapLh`, `skKCofGap`, `skKCof`,
`skEQJump`, `skEQTopR`, `skKReachR`, `skKFar`, `skKClosed`, `skKLim`, `skEQfar`, `skEQ` take `hVt`; their statements
are otherwise unchanged.  The only open leaf of SkE is `skTopK`.
This file also imports the new modules `R2.ZeBad`, `R2.ZeWin`, `R2.ZeName`, `R2.ZeTerm`, `R2.ZeJump`, `R2.ZeGap`
(through `R2.ZeJump`, `R2.ZeGap`): it can be checked only after the merge.
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

/-- The frontier hypothesis `hVt` of the road (CapV at the range restarts in `(L(ω), L(ω+1))` past the frontier),
`SkF.skFrontVt S` (round 131). -/
abbrev SkVt (S : InaccSeq.{0}) : Prop :=
  ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdCapV S l

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

/-- STATUS: PROVED (round 130, Yz.yzGapEpsTop; was OPEN)
SIZE: S
REFUTE: NO EVIDENCE (round 130, bounded first step on ¬YuGapPlus at the first gap ε-number above
ϑ^{υ_ξ}(Ω₁·ε_{Ω₁+1}): by [W07a] Lemma 3.30 a counterexample a < B_n p < a⁺ needs B_n p = ϑ^{υ_ξ}(ξ_X) with a datum
of the level of ξ_X, or the countable part of ξ_X, at least a; Lean shows the opposite: both are B_n-images of
ordinals below p, hence below a (Yz.yzGapPlus); no no-go result speaks of R₁⁺-reaches of ε-numbers)
a gap point (Ye.YeGapPt) that is an ε-number, no υ-point, with no υ-point in (a, B_n p], in the bracket
(υ_ξ, υ_{ξ+1}), ξ ≠ 0, a = ϑ^{υ_ξ}(ξ') with ξ' ∈ T ∩ Ω₂ and Ω₁·ε_{Ω₁+1} ≤ ξ'  ⇒  lh(a) < B_n p
(statement Yu.YuGapEpsTop S).  Proof: Yu.yuTop_of_plus with skLhPlus ([W07b] Lemma 4.2, cited: R2.yzLhT_lt_plus)
and skGapPlus (Yz.yzGapPlus, no hypothesis); checkable after the merge of R2.CitedYz, R2.YzPlus. -/
theorem skGapEpsTop (hν : Nc.ncL S (ω + 1) ≤ nuC) : Yu.YuGapEpsTop S := Yz.yzGapEpsTop hν

/-- STATUS: REDUCED (round 129; was OPEN)
SIZE: S
REFUTE: NO EVIDENCE (round 126: follows from the target, skGapTarget3 (Ye.yeGap_of_target); no no-go result
(Vo.voNoGo, Vn.vnTop_Om3, Vq.vqNoTop_Om3, Vx.vxNoCompat, Wb.*, Wc.*, Xd.xdX0Law_false, Xi.xiTopFam_false) speaks of
R₁⁺-reaches of ε-numbers in (L(ω), L(ω+1)); the first jump has no ε-number in its gap, skFirstJump)
a gap point (Ye.YeGapPt) that is an ε-number, no υ-point, with no υ-point in (a, B_n p]  ⇒  lh(a) < B_n p
(statement Ye.YeGapEps S).  Child skGapEpsTop (Yu.yuGapEps_of_top: p is an ε-number, skGapEpsPE, so ε_{a+1} ≤ B_n p,
skGapEpsEN; a = ϑ^{υ_ξ}(ξ') by vt_rep; for Ω₁ ≤ ξ' < Ω₁·ε_{Ω₁+1} the reach is below ε_{a+1}, skLhLtEN; checkable
after the merge of R2.YuEps). -/
theorem skGapEps (hν : Nc.ncL S (ω + 1) ≤ nuC) : Ye.YeGapEps S := Yu.yuGapEps_of_top hν (skGapEpsTop hν)

/-- STATUS: PROVED (round 131, Ze.zeGapRngHi; was OPEN)
SIZE: S
REFUTE: NO EVIDENCE (round 130: follows from the target, skGapRngHiTarget (Yz.yzGapRngHi_of_target); round 131,
bounded first step at the first long code above θ·ω: a counterexample is a gap restart ρ_{l₀} with r(l₀) ≥ B_n p; by
the cap window of B_n p (Ze.zeGap_win) ρ_{l₀} would need a name outside the window (β', β' + ω^d) of the name
β' + ω^d of B_n p, but the window starts at the B_n-image P(β') ≤ B_n q of a point q < p; no no-go result (Vo.voNoGo,
Vn.vnTop_Om3, Vq.vqNoTop_Om3, Vx.vxNoCompat, Wb.*, Wc.*, Xd.xdX0Law_false, Xi.xiTopFam_false, Yd.ydInvRef) speaks of
caps of restarts in (L(ω), L(ω+1)); the statement is now proved)
NEW leaf (round 130).  hν, ENUM-REACH, p = υ_κ a restart, a gap point υ_l with l a restart index and
θ·ω < m_l  ⇒  lh(υ_l) < B_n p  (statement Yz.YzGapRngHi S).
Round 131: PROVED with the road hypothesis hVt (CapV in (L(ω), L(ω+1))); in fact every code (Ze.zeGapRng): the cap
window of B_n p (Ze.zeGap_win: the good name η_κ = β + ω^E of p, the argument term α_{n+1} + ρ of P(η_κ), ρ = I + L
with L its last summand, |L| = θ·ω^E, α_{n+1} + |I| = A_β; σ keeps the split, B_n p = P(β' + ω^d),
P(β') ≤ B_n P(ζ) for a good ζ ∈ [β, η_κ) with c_n ≤ P(ζ), which exists by Ze.zeIota_prefix_lt) contains every gap
restart, and CapV gives r(l₀) < cap(l₀) ≤ B_n p.  Checkable after the merge of R2.Ze*. -/
theorem skGapRngHi (_hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) (hVt : SkVt S) :
    Yz.YzGapRngHi S :=
  Ze.zeGapRngHi (Ze.zeCapHigh hVt) hU hL

/-- STATUS: REDUCED (round 130; was OPEN; round 131: its child skGapRngHi PROVED, so no open leaf below)
SIZE: S
REFUTE: NO EVIDENCE (round 126: follows from the target, skGapTarget3; under ENUM-REACH the reach of a range
restart ν in the gap is r(ν), Xw.xwGapLh_iff; no no-go result speaks of reaches of restarts in (L(ω), L(ω+1)))
NEW leaf (round 126).  p = υ_κ a restart, a gap point υ_l with l a restart index  ⇒  lh(υ_l) < B_n p
(statement Ye.YeGapRng S; at a non-restart p there is no υ-point in the gap, skNoUpsOff).
Round 129: still OPEN; REFUTE FIRST: NO EVIDENCE (no Lean value of r(l) for a restart l in (L(ω), L(ω+1)); the
short-code bound Rc.rcR_lowCode, r(l) < υ_{l+ω+2}, needs υ_l < L(ω); the gap bottom s* = sup_{q<p} B_n q is itself
such a gap restart, and its reach is the least closed point of λ' at or above s*).
Round 130: REDUCED, with the new hypotheses CdUPPER, CdLOWER (from skEnum through skGapLh, skKCofGap, skKCof), to
skGapRngHi (Yz.yzGapRng_of_hi): a gap restart with code m_l ≤ θ·ω has r(l) < υ_{l+ω+2} < υ_{κ'} = B_n p
(skGapRngLow = Yz.yzGapRng_low; A_{η_l} is own below L(ω+1), Yz.yzOwnA_W1; checkable after the merge of R2.YzRng). -/
theorem skGapRng (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) (hVt : SkVt S) :
    Ye.YeGapRng S :=
  Yz.yzGapRng_of_hi hν hU hL (skGapRngHi hν hU hL hVt)

/-- STATUS: PROVED (round 127, Yk.ykGapBlk; was OPEN)
SIZE: S
REFUTE: none needed (proved with no hypothesis).
p = υ_κ a restart, a gap υ-point a in the block (υ_{botI μ j}, υ_{μ+ω(j+1)+1}]  ⇒  υ_{μ+ω(j+1)+1} < B_n p
(statement Ye.YeGapBlk S; B_n p = υ_{κ'} with κ' a restart index, Sf.sfRstMove; υ_μ < a < υ_{κ'} gives μ < κ', and
restart indices are ω·ω apart, Ye.ye_rst_gap; checkable after the merge of R2.YkBlk). -/
theorem skGapBlk (_hν : Nc.ncL S (ω + 1) ≤ nuC) : Ye.YeGapBlk S := Yk.ykGapBlk

/-- STATUS: REDUCED (round 126; was OPEN)
SIZE: S
REFUTE: SURVIVED (round 125: equivalent to skKCofGap and to XgKCof, skGapLh_iff; follows from the target,
skGapLhTarget; at the first jump p = c_n·2 the gap has no closed point of λ' but p is no far index, skFirstJump)
window λ → λ', cofinal far index p (δ_λ·ω ≤ p ≤ Θ_λ(m_λ), k_λ(q) < p for q < p) with p indecomposable and the
k-move below p, a in the jump gap (B_n q ≤ a < B_n p for all q < p)  ⇒  lh(a) < B_n p  (statement Xw.XwGapLh S).
Children skGapEps, skGapRng (skGapBlk PROVED, round 127; Yk.ykGapLh_of = Ye.yeGapLh_of with Yk.ykGapBlk: non-υ
gap points that are no ε-number, or have a υ-point in (a, B_n p], have lh(a) < B_n p by the R₁⁺-reach,
Ye.yeLh_easy; checkable after the merge of R2.YeGap, R2.YkBlk). -/
theorem skGapLh (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) (hVt : SkVt S) :
    Xw.XwGapLh S :=
  Yk.ykGapLh_of hν (skGapEps hν) (skGapRng hν hU hL hVt)

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
theorem skKCofGap (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) (hVt : SkVt S) :
    Xr.XrKCofGap S :=
  Xw.xwKCofGap_of_lh (skGapLh hν hU hL hVt)

/-- STATUS: PROVED (round 126, Ye.yeJumpOff; was OPEN)
SIZE: S
REFUTE: the leaf is VACUOUS (round 126): its hypotheses say that s is no range restart, but the chain points (range
restarts ρ_μ) cofinal below s make s = υ_l with l = sup of the μ, ω² ∣ l (Ye.ye_dvd_of_cof), so s is a restart
strictly inside (c_n, c_{n+1}), hence a range restart (Se.seRange_mid; Ye.yeJump_rst).
An instance of Xr.XrJump (n, R, R', s with all its hypotheses) whose jump point s is not a range restart
⇒  B_n s ≤₁ R'  (statement Xw.XwJumpOff S; checkable after the merge of R2.YeJump). -/
theorem skJumpOff (_hν : Nc.ncL S (ω + 1) ≤ nuC) : Xw.XwJumpOff S := Ye.yeJumpOff

/-- STATUS: PROVED (round 131, Ze.zeJumpNoRng; was OPEN)
SIZE: S
REFUTE: NO EVIDENCE (round 125: follows from the target, skJumpTarget; XrJump forces it, Xw.xwJump_noRng_of;
vacuous at s = c_n·2, skFirstJump; not derivable from skJumpOff alone: EQ at the range point s = ρ_μ fails exactly
when B_n R = R' ≠ r(μ'), and the reach class (R, r(μ')) only yields a new range instance above s)
NEW leaf (round 125).  No instance of Xr.XrJump has a range restart ρ_μ as its jump point s
(statement Xw.XwJumpNoRng S).
Round 127: still OPEN.  Equivalent (Yk.ykNoRng_iff_gap, skJumpGapIff) to Yk.YkJumpGap: at every instance the range
restart κ with υ_κ = s* = sup_{q<s} B_n q (no B_n-image, r(κ) = R', skJumpGapBot) has r(κ) = B_n R ≥ B_n s, i.e. the
gap-bottom restart reaches past the gap (skJumpGapShort).  REFUTE FIRST (round 127): the first range restart where
B_n jumps lies at index ≥ c_n·2 (the first jump of B_n, skFirstJump), and a chain cofinal below it needs range
restarts of one reach R ≥ s cofinal below s, each ≤₁ s (skChainLe1); no Lean value of a reach above c_n is known
(the windows have no base condition, Yf.yfNoBase_win), so the chain below the first jump can be neither computed
nor excluded: NO EVIDENCE either way.  Not a consequence of the part's other leaves: at an instance, EQ at the jump
point μ (xnEQ_short / xnEQ_step, its top above s) and EQ at a chain point would together close it, but EQ fails at
every chain point of an instance (B_n R ≠ R' there, by the equivalence with Xr.XrJump).
Round 129: still OPEN; REFUTE FIRST, both routes: NO EVIDENCE.  The first υ-point where B_n jumps is expected at
s = υ_{c_n·2} (chain candidates υ_{c_n+ζ}, ζ < c_n, gap bottom κ = L(ω) + c_n, B_n s = υ_{L(ω)·2}); Lean has no
B_n-value at υ_{c_n+ζ} for ζ ≥ ω·ω (Sf.sfShiftAll stops there) and no reach of any range restart in (c_n, c_{n+1})
or (L(ω), L(ω+1)), so neither route (i) (no same-reach chain below s) nor route (ii) (r(κ) = B_n R) can be tested.
Both are the EQ statement in disguise: in truth (CxEQtop) no instance exists, and an instance needs EQ to fail
cofinally below s; through the composition B_n = B_m ∘ C_{n,m} (Ye.yeComp) the gap bottom is a B_m-image of
sup_i C_{n,m} x_i, where B_m is continuous, so route (ii) becomes the same reach move for C_{n,m} in window m.
Round 130: still OPEN; REFUTE FIRST: NO EVIDENCE (no B_n-value of a range restart with a same-reach chain below it is
computable: Sf.sfShiftAll gives B_n υ_{μ+β} = υ_{μ'+β} only with μ' unknown).  New fact: an instance whose gap bottom κ
has a code m_κ ≤ θ·ω has r(κ) < υ_{κ+ω+2} < B_n s (skJumpShortBot), so the leaf fails at such an instance, and the
instance would refute the target CxEQtop (Yz.yzJump_short_noEQ); the expected first jump gap bottom (name η_{L(ω)}
plus a countable offset) has a countable, hence short, code.  The leaf is split by the code of κ (skJumpSplit).
Round 131: REFUTE FIRST on YzJumpShort (a jump instance whose gap bottom has code ≤ θ·ω): NO EVIDENCE, the statement
is PROVED with no hypothesis (skJumpShortU = Ze.zeJumpShortU: the good name η_κ = β + ω^E has ι(β) < κ, since a bad
interval [β, β + ω^E) would make η_κ bad, Ze.zeBad_top; the restarts of (υ_{ι(β)}, ρ_κ) have names in (β, η_κ), so
last exponents < E ≤ θ·ω, Ze.zeCode_win; a chain image there has r(μ') < υ_{μ'+ω+2} < ρ_κ < r(κ) = R' = r(μ')).
The whole leaf (both code cases) is PROVED from the road hypothesis hVt (Ze.zeJumpNoRng: the cap window Ze.zeCap_win
below ρ_κ and CapV at a chain image give r(μ') < cap(μ') ≤ ρ_κ). -/
theorem skJumpNoRng (_hν : Nc.ncL S (ω + 1) ≤ nuC) (hVt : SkVt S) : Xw.XwJumpNoRng S :=
  Ze.zeJumpNoRng hVt

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
theorem skEQJump (hν : Nc.ncL S (ω + 1) ≤ nuC) (hVt : SkVt S) : Xr.XrJump S :=
  Xw.xwJump_of (skJumpOff hν) (skJumpNoRng hν hVt)

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
theorem skKCof (hν : Nc.ncL S (ω + 1) ≤ nuC) (hUH : SkUH S) (hLH : SkLH S) (hVt : SkVt S) : Xg.XgKCof S :=
  Xr.xrKCof_of_gap (skKCofGap hν (skEnum hUH hLH).1 (skEnum hUH hLH).2 hVt)

/-- STATUS: REDUCED (Xr.xrTop; checkable after the merge of R2.XrTop)
SIZE: L
hRead, hUH, hLH, hν ⇒ Xn.XnTop  (children skEQJump, skThFar, skKCof, and skThLow, skEnum; xrClass: the chain
points of a reach class have no largest element, their supremum s has lh(s) = R; where B_n is continuous at s the
reach moves (s a chain point or Wa.waTCtopOff); left: the jumps of B_n). -/
theorem skEQTopR (hRead : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdAtWall S ∧ Wd.WdThHi S) (hUH : SkUH S)
    (hLH : SkLH S) (hVt : SkVt S) (hν : Nc.ncL S (ω + 1) ≤ nuC) : Xn.XnTop S :=
  Xr.xrTop hν (skEnum hUH hLH).1 (skEnum hUH hLH).2 (skThLow hRead hν) (skThFar hν) (skKCof hν hUH hLH hVt)
    (skEQJump hν hVt)

/-- STATUS: REDUCED
SIZE: L
hRead, hUH, hLH, hν ⇒ XgKReachR  (children skThFar, skKCof, skEQTopR; Xn.xnPart: the induction on r(λ),
Xn.xnEQ_all; checkable after the merge of R2.XnLow, R2.XnInd, R2.XnRoad). -/
theorem skKReachR (hRead : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdAtWall S ∧ Wd.WdThHi S) (hUH : SkUH S)
    (hLH : SkLH S) (hVt : SkVt S) (hν : Nc.ncL S (ω + 1) ≤ nuC) : Xg.XgKReachR S :=
  (Xn.xnPart hν (hRead hν).1 (hRead hν).2 (skEnum hUH hLH).1 (skEnum hUH hLH).2 (skThFar hν)
    (skKCof hν hUH hLH hVt) (skEQTopR hRead hUH hLH hVt hν)).2.2.1


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
    (hLH : SkLH S) (hVt : SkVt S) (hν : Nc.ncL S (ω + 1) ≤ nuC) : SkKFar S :=
  Xg.xgKFar_of_R hν (skKCof hν hUH hLH hVt) (skKReachR hRead hUH hLH hVt hν)

/-- STATUS: REDUCED
SIZE: S
δ_λ·ω ≤ q+1 ≤ Θ_λ(m_λ) ⇒ B_n(k_λ(q+1)) ∈ K_{λ'}  (from skKFar: SkEX.skexClosed_of_far; off the path). -/
theorem skKClosed (hRead : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdAtWall S ∧ Wd.WdThHi S) (hUH : SkUH S)
    (hLH : SkLH S) (hVt : SkVt S) (hν : Nc.ncL S (ω + 1) ≤ nuC) : SkKClosed S :=
  R2Skel.SkEX.skexClosed_of_far hν (skKFar hRead hUH hLH hVt hν)

/-- STATUS: PROVED (Xg.xgKGap: k_λ(q+1) = k_λ(q) + 1, Xg.xgk_succ)
SIZE: S
z ∈ K_{λ'} ⇒ ¬ (B_n k_λ(q) < z < B_n k_λ(q+1))  (no hypothesis needed). -/
theorem skKGap (_hν : Nc.ncL S (ω + 1) ≤ nuC) : SkKGap S :=
  Xg.xgKGap

/-- STATUS: REDUCED
SIZE: S
p limit, δ_λ·ω ≤ p ≤ Θ_λ(m_λ), IH ⇒ k_{λ'}(B_n p) = B_n k_λ(p)  (from skKFar: SkEX.skexLim_of_far; off the path). -/
theorem skKLim (hRead : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdAtWall S ∧ Wd.WdThHi S) (hUH : SkUH S)
    (hLH : SkLH S) (hVt : SkVt S) (hν : Nc.ncL S (ω + 1) ≤ nuC) : SkKLim S :=
  R2Skel.SkEX.skexLim_of_far (skKFar hRead hUH hLH hVt hν)

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
    (hLH : SkLH S) (hVt : SkVt S) : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdEQfar S :=
  fun hν => skEQfar_of (skThFar hν) (skKFar hRead hUH hLH hVt hν)

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
TOP NODE (round 117: new hypotheses hUH, hLH, the frontier hypotheses of the road; round 131: new hypothesis hVt,
the frontier hypothesis CapV in (L(ω), L(ω+1)) of the road; Root.skNuC applies
`skEQ hRead (SkF.skFrontU S) (SkF.skFrontL S) (SkF.skFrontVt S)`).
hRead: hν → WdAtWall ∧ WdThHi, hUH, hLH, hVt  ⇒  (hν → WdThLow) ∧ (hν → WdEQfar). -/
theorem skEQ (hRead : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdAtWall S ∧ Wd.WdThHi S) (hUH : SkUH S)
    (hLH : SkLH S) (hVt : SkVt S) :
    (Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S) ∧ (Nc.ncL S (ω + 1) ≤ nuC → Wd.WdEQfar S) :=
  ⟨skThLow hRead, skEQfar hRead hUH hLH hVt⟩

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

/-! ## Round 126 (leaf eq5): composition of base changes, the gap split, the jump points -/

/-- STATUS: PROVED (Ye.yeComp; NEW round 126)
SIZE: S
The composition B_m ∘ C_{n,m} = B_n (C_{n,m} = τ_m ∘ B_n): for x < L(n+2), for every large m, x's image is in the
domain of τ_m, B_m(C_{n,m} x) = B_n x and C_{n,m} x < L(m+2). -/
theorem skComp {n : ℕ} {x : Ordinal.{0}} (hx : x < Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})) :
    ∃ M : ℕ, ∀ m, M ≤ m → Ye.YeDom S m (Bc.bcB S n x) ∧ Bc.bcB S m (Ye.yeC S n m x) = Bc.bcB S n x ∧
      Ye.yeC S n m x < Nc.ncL S ((m + 2 : ℕ) : Ordinal.{0}) :=
  Ye.yeComp hx

/-- STATUS: PROVED (Ye.yeComp_fin; NEW round 126)
SIZE: S
The composition uniformly on a finite set. -/
theorem skCompFin {n : ℕ} (Y : Finset Ordinal.{0}) (hY : ∀ x ∈ Y, x < Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})) :
    ∃ M : ℕ, ∀ m, M ≤ m → ∀ x ∈ Y, Ye.YeDom S m (Bc.bcB S n x) ∧
      Bc.bcB S m (Ye.yeC S n m x) = Bc.bcB S n x ∧ Ye.yeC S n m x < Nc.ncL S ((m + 2 : ℕ) : Ordinal.{0}) :=
  Ye.yeComp_fin Y hY

/-- STATUS: PROVED (Ye.ye01; NEW round 126; a REFUTE-FIRST record, no node uses it)
SIZE: S
At n = 0, m = 1: C_{0,1}(c_1) = c_2, B_1(C_{0,1} c_1) = B_0(c_1) = L(ω+1); B_1(c_1·2) = B_0(c_0·2) = L(ω)·2; the gap
point L(ω) + c_0 of B_0 at c_0·2 is B_1(c_1 + c_0), with c_1 + c_0 < c_1·2 (in the gap of C_{0,1}). -/
theorem skComp01 :
    Ye.yeC S 0 1 (Bc.bcC S 1) = Bc.bcC S 2 ∧
      Bc.bcB S 1 (Ye.yeC S 0 1 (Bc.bcC S 1)) = Bc.bcB S 0 (Bc.bcC S 1) ∧
      Bc.bcB S 1 (Bc.bcC S 1 * 2) = Bc.bcB S 0 (Bc.bcC S 0 * 2) ∧
      Bc.bcB S 1 (Bc.bcC S 1 + Bc.bcC S 0) = Nc.ncL S ω + Bc.bcC S 0 ∧
      (∀ q < Bc.bcC S 0 * 2, Bc.bcB S 0 q < Nc.ncL S ω + Bc.bcC S 0) ∧
      Nc.ncL S ω + Bc.bcC S 0 < Bc.bcB S 0 (Bc.bcC S 0 * 2) ∧ Bc.bcC S 1 + Bc.bcC S 0 < Bc.bcC S 1 * 2 :=
  Ye.ye01

/-- STATUS: PROVED (Ye.yeGap_pre; NEW round 126)
SIZE: S
The jump gap of B_n at p is the B_m-image of the gap of C_{n,m} at p (pointwise, every large m). -/
theorem skGapPre {n : ℕ} {p a : Ordinal.{0}} (hp : p < Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
    (hLa : Nc.ncL S ω ≤ a) (ha : a < Bc.bcB S n p) :
    ∃ M : ℕ, ∀ m, M ≤ m → ∃ a', Bc.bcC S m ≤ a' ∧ a' < Ye.yeC S n m p ∧ Bc.bcB S m a' = a ∧
      Bc.bcB S m (Ye.yeC S n m p) = Bc.bcB S n p ∧
      ∀ q < Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}), Ye.YeDom S m (Bc.bcB S n q) →
        (Bc.bcB S n q ≤ a ↔ Ye.yeC S n m q ≤ a') :=
  Ye.yeGap_pre hp hLa ha

/-- STATUS: PROVED (Ye.yeGapLh_pre; NEW round 126)
SIZE: S
At a B_m-preimage a' ∈ (c_m, c_{m+1}) of a gap point, no range restart, lh(a') = R < c_{m+1}:
lh(a) = B_m R, and lh(a) < B_n p ⇔ R < C_{n,m} p. -/
theorem skGapLhPre (hν : Nc.ncL S (ω + 1) ≤ nuC) {n m : ℕ} {p a a' R : Ordinal.{0}}
    (h1 : Bc.bcC S m < a') (hRc : R < Bc.bcC S (m + 1)) (hR : IsReach R2C a' R)
    (hnr : ∀ l, CdRange S l → a' ≠ upsilon l) (ha' : Bc.bcB S m a' = a)
    (hCp : Bc.bcB S m (Ye.yeC S n m p) = Bc.bcB S n p)
    (hCpL : Ye.yeC S n m p < Nc.ncL S ((m + 2 : ℕ) : Ordinal.{0})) :
    IsReach R2C a (Bc.bcB S m R) ∧ (Bc.bcB S m R < Bc.bcB S n p ↔ R < Ye.yeC S n m p) :=
  Ye.yeGapLh_pre hν h1 hRc hR hnr ha' hCp hCpL

/-- STATUS: PROVED (Ye.yeJump_rst; NEW round 126)
SIZE: S
If the chain points of a class are cofinal below s ∈ (c_n, c_{n+1}), then s = ρ_l for a range restart l. -/
theorem skJumpRst {n : ℕ} {R R' s : Ordinal.{0}} (h1s : Bc.bcC S n < s) (hs2 : s < Bc.bcC S (n + 1))
    (hcof : ∀ x < s, ∃ y, x < y ∧ y < s ∧ Xr.XrPt S n R R' y) : ∃ l, CdRange S l ∧ s = upsilon l :=
  Ye.yeJump_rst h1s hs2 hcof

/-- STATUS: PROVED (Ye.yeJump_iff; NEW round 126)
SIZE: S
skEQJump ⇔ skJumpNoRng (unconditional). -/
theorem skJumpOnlyRng : Xr.XrJump S ↔ Xw.XwJumpNoRng S := Ye.yeJump_iff

/-- STATUS: PROVED (Ye.yeGapLh_iff; NEW round 126)
SIZE: S
Under hν: skGapLh ⇔ skGapEps ∧ skGapRng ∧ skGapBlk. -/
theorem skGapSplit3 (hν : Nc.ncL S (ω + 1) ≤ nuC) :
    Xw.XwGapLh S ↔ Ye.YeGapEps S ∧ Ye.YeGapRng S ∧ Ye.YeGapBlk S :=
  Ye.yeGapLh_iff hν

/-- STATUS: PROVED (Ye.yeGap_of_target; NEW round 126)
SIZE: S
NON-VACUITY: hν ∧ CdUPPER ∧ CdLOWER ∧ CdEQ ∧ SkKFar ⇒ skGapEps ∧ skGapRng ∧ skGapBlk. -/
theorem skGapTarget3 (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) (hEQ : CdEQ S)
    (hK : R2Skel.SkEX.SkKFar S) : Ye.YeGapEps S ∧ Ye.YeGapRng S ∧ Ye.YeGapBlk S :=
  Ye.yeGap_of_target hν hU hL hEQ hK

/-- STATUS: PROVED (Ye.yeLh_easy; NEW round 126)
SIZE: S
A non-υ-point a < X < ν_C, X indecomposable, has lh(a) < X unless a is an ε-number with no υ-point in (a, X]. -/
theorem skLhEasy {a X : Ordinal.{0}} (haC : a < nuC) (hX : Indec X) (haX : a < X) (hU : ¬ UpsPt a)
    (h : ¬ InE a ∨ ∃ u, UpsPt u ∧ a < u ∧ u ≤ X) : ∃ r, IsReach R2C a r ∧ r < X :=
  Ye.yeLh_easy haC hX haX hU h

/-- STATUS: PROVED (Ye.yeUps_block; NEW round 126)
SIZE: S
A υ-point inside a block (υ_{botI μ j}, β], β = υ_{μ+ω(j+1)+1} < ν_C, has the reach β. -/
theorem skUpsBlock {μ a : Ordinal.{0}} {j : ℕ} (hμ : μ = 0 ∨ IsRestartIdx μ)
    (hC : upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) < nuC) (ha1 : upsilon (botI μ j) < a)
    (ha2 : a ≤ upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1)) (hU : UpsPt a) :
    IsReach R2C a (upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1)) :=
  Ye.yeUps_block hμ hC ha1 ha2 hU

/-- STATUS: PROVED (Ye.yeNoUps_off; NEW round 126)
SIZE: S
Under hν: if p is no restart, the jump gap at p contains no υ-point (p lies in the first υ-bracket (υ_b, υ_{b+1}]
of its block, since the closed points of λ are cofinal below p; B_n moves the υ-points of the region of the restart
ν index-wise, Sf.sfShiftAll; so the gap lies strictly between two consecutive υ-points). -/
theorem skNoUpsOff (hν : Nc.ncL S (ω + 1) ≤ nuC) {n : ℕ} {l l' p a : Ordinal.{0}}
    (hP : Ye.YeGapPt S n l l' p a) (hpr : ∀ κ, IsRestartIdx κ → p ≠ upsilon κ) (hU : UpsPt a) : False :=
  Ye.yeNoUps_off hν hP hpr hU

/-- STATUS: PROVED (Ye.yeGapUps_rst; NEW round 126)
SIZE: S
A υ-point in the jump gap forces p to be a restart. -/
theorem skGapUpsRst (hν : Nc.ncL S (ω + 1) ≤ nuC) {n : ℕ} {l l' p a : Ordinal.{0}}
    (hP : Ye.YeGapPt S n l l' p a) (hU : UpsPt a) : ∃ κ, IsRestartIdx κ ∧ p = upsilon κ :=
  Ye.yeGapUps_rst hν hP hU

/-- STATUS: PROVED (Yk.ykChain_le1; NEW round 127)
SIZE: S
At an instance: every chain point y < s has y ≤₁ s. -/
theorem skChainLe1 (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) {n : ℕ}
    {R R' s y : Ordinal.{0}} (hRc : R < Bc.bcC S (n + 1)) (hsR : IsReach R2C s R)
    (hy : Xr.XrPt S n R R' y) (hys : y < s) : le1 y s :=
  Yk.ykChain_le1 hν hU hL hRc hsR hy hys

/-- STATUS: PROVED (Yk.ykGapBot; NEW round 127)
SIZE: S
At an instance: s* = sup_{q<s} B_n q = υ_κ, κ a range restart, r(κ) = R', L(ω) < υ_κ < B_n s, B_n q < υ_κ for
q < s, and υ_κ is no B_n-image. -/
theorem skJumpGapBot (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) {n : ℕ}
    {R R' s : Ordinal.{0}} (hRc : R < Bc.bcC S (n + 1)) (h1s : Bc.bcC S n < s)
    (hcof : ∀ x < s, ∃ y, x < y ∧ y < s ∧ Xr.XrPt S n R R' y) (hsR : IsReach R2C s R)
    (hjump : ∃ Q < Bc.bcB S n s, ∀ q < s, Bc.bcB S n q ≤ Q) :
    ∃ κ, CdRange S κ ∧ sSup (Bc.bcB S n '' Iio s) = upsilon κ ∧ cdR S κ = R' ∧
      Nc.ncL S ω < upsilon κ ∧ upsilon κ < Bc.bcB S n s ∧ (∀ q < s, Bc.bcB S n q < upsilon κ) ∧
      ∀ y < Bc.bcC S (n + 1), Bc.bcB S n y ≠ upsilon κ :=
  Yk.ykGapBot hν hU hL hRc h1s hcof hsR hjump

/-- STATUS: PROVED (Yk.ykNoRng_iff_gap; NEW round 127)
SIZE: S
skJumpNoRng ⇔ Yk.YkJumpGap (r(κ) = B_n R at the gap-bottom restart of every instance). -/
theorem skJumpGapIff : Xw.XwJumpNoRng S ↔ Yk.YkJumpGap S := Yk.ykNoRng_iff_gap

/-- STATUS: PROVED (Yk.ykGap_short_ne; NEW round 127)
SIZE: S
At an instance with lh(s*) = R' < B_n s: B_n R ≠ R'. -/
theorem skJumpGapShort (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) {n : ℕ}
    {R R' s : Ordinal.{0}} (hRc : R < Bc.bcC S (n + 1)) (h1s : Bc.bcC S n < s)
    (hcof : ∀ x < s, ∃ y, x < y ∧ y < s ∧ Xr.XrPt S n R R' y) (hsR : IsReach R2C s R)
    (hjump : ∃ Q < Bc.bcB S n s, ∀ q < s, Bc.bcB S n q ≤ Q) (hshort : R' < Bc.bcB S n s) :
    Bc.bcB S n R ≠ R' :=
  Yk.ykGap_short_ne hν hU hL hRc h1s hcof hsR hjump hshort

/-- STATUS: PROVED (Yk.ykJumpGap_of_EQtop; NEW round 127)
SIZE: S
NON-VACUITY: the target CxEQtop gives Yk.YkJumpGap. -/
theorem skJumpGapTarget (h : Cx.CxEQtop S) : Yk.YkJumpGap S := Yk.ykJumpGap_of_EQtop h

/-- STATUS: PROVED (Yu.yu_gap_pE; NEW round 129)
SIZE: S
A gap ε-number forces the far index p to be an ε-number. -/
theorem skGapEpsPE {n : ℕ} {l l' p a : Ordinal.{0}} (hP : Ye.YeGapPt S n l l' p a) (hE : InE a) : InE p :=
  Yu.yu_gap_pE hP hE

/-- STATUS: PROVED (Yu.yu_gap_eN; NEW round 129)
SIZE: S
At a gap ε-number: ε_{a+1} ≤ B_n p. -/
theorem skGapEpsEN {n : ℕ} {l l' p a : Ordinal.{0}} (hP : Ye.YeGapPt S n l l' p a) (hE : InE a) :
    eN a ≤ Bc.bcB S n p :=
  Yu.yu_gap_eN hP hE

/-- STATUS: PROVED (Yu.yuLh1_lt_eN; NEW round 129)
SIZE: S
The R₁⁺-reach of ϑᵗ(ξ) is below ε_{a+1} for Ω₁ ≤ ξ < Ω₁·ε_{Ω₁+1} (τ strongly critical, ξ ∈ Tᵗ ∩ Ω₂). -/
theorem skLhLtEN {τ ξ : Ordinal.{0}} (hτ : SC τ) (hτ1 : τ < Om1) (hξT : ξ ∈ Tset τ) (hξ2 : ξ < OmTwo)
    (hΩξ : Om1 ≤ ξ) (hξE : ξ < Om1 * Gg.ggE) : ∃ r, IsLh1 (vt τ ξ) r ∧ r < eN (vt τ ξ) :=
  Yu.yuLh1_lt_eN hτ hτ1 hξT hξ2 hΩξ hξE

/-- STATUS: PROVED (Yu.yuGapEps_iff; NEW round 129)
SIZE: S
skGapEps ⇔ skGapEpsTop (under hν). -/
theorem skGapEpsIff (hν : Nc.ncL S (ω + 1) ≤ nuC) : Ye.YeGapEps S ↔ Yu.YuGapEpsTop S := Yu.yuGapEps_iff hν

/-- STATUS: PROVED (Yu.yuTop_of_target; NEW round 129)
SIZE: S
NON-VACUITY: the target (hν, ENUM-REACH, CdEQ, SkKFar) gives Yu.YuGapEpsTop. -/
theorem skGapEpsTopTarget (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) (hEQ : CdEQ S)
    (hK : SkKFar S) : Yu.YuGapEpsTop S :=
  Yu.yuTop_of_target hν hU hL hEQ hK

/-- STATUS: PROVED (Yu.yuTop_of_plus; NEW round 129)
SIZE: S
skGapEpsTop from two statement names: Yu.YuLhPlus ([W07b] Lemma 4.2, lhᵗ(α) < α⁺ = ϑᵗ(ξ+1); a paper lemma, not
cited in the repo) and Yu.YuGapPlus (the notation statement a⁺ = ϑ^{υ_ξ}(ξ'+1) ≤ B_n p at a top-level gap
ε-number).  Not used by the road (skGapEpsTop stays OPEN). -/
theorem skGapEpsTopPlus (hν : Nc.ncL S (ω + 1) ≤ nuC) (h1 : Yu.YuLhPlus) (h2 : Yu.YuGapPlus S) :
    Yu.YuGapEpsTop S :=
  Yu.yuTop_of_plus hν h1 h2

/-- STATUS: PROVED (round 130, R2.yzLhT_lt_plus via Yz.yzLhPlus; uses the cited axiom of R2.CitedYz)
SIZE: S
[W07b] Lemma 4.2 as Yu.YuLhPlus: InE τ, τ < Ω₁, ξ ∈ Tᵗ ∩ Ω₂, Ω₁ ≤ ξ  ⇒  lhᵗ(ϑᵗ ξ) < ϑᵗ(ξ+1). -/
theorem skLhPlus : Yu.YuLhPlus := Yz.yzLhPlus

/-- STATUS: PROVED (round 130, Yz.yzGapPlus; no hypothesis beyond S)
SIZE: S
At a top-level gap ε-number a = ϑ^{υ_ξ}(ξ'): a⁺ = ϑ^{υ_ξ}(ξ'+1) ≤ B_n p  (statement Yu.YuGapPlus S). -/
theorem skGapPlus : Yu.YuGapPlus S := Yz.yzGapPlus

/-- STATUS: PROVED (round 130, Yz.yzGapRng_low)
SIZE: S
hν, ENUM-REACH, p = υ_κ a restart, a gap restart υ_l with m_l ≤ θ·ω  ⇒  lh(υ_l) < B_n p. -/
theorem skGapRngLow (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) {n : ℕ}
    {l l' p l₀ κ : Ordinal.{0}} (hP : Ye.YeGapPt S n l l' p (upsilon l₀)) (hl₀ : IsRestartIdx l₀)
    (hκ : IsRestartIdx κ) (hpκ : p = upsilon κ) (hm : cdCode S l₀ ≤ ConjT.th S * ω) :
    ∃ r, IsReach R2C (upsilon l₀) r ∧ r < Bc.bcB S n p :=
  Yz.yzGapRng_low hν hU hL hP hl₀ hκ hpκ hm

/-- STATUS: PROVED (round 130, Yz.yzGapRngHi_of_target)
SIZE: S
NON-VACUITY: hν ∧ CdUPPER ∧ CdLOWER ∧ CdEQ ∧ SkKFar ⇒ skGapRngHi. -/
theorem skGapRngHiTarget (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) (hEQ : CdEQ S)
    (hK : SkKFar S) : Yz.YzGapRngHi S :=
  Yz.yzGapRngHi_of_target hν hU hL hEQ hK

/-- STATUS: PROVED (round 130, Yz.yzJump_shortBot)
SIZE: S
At an instance of skJumpNoRng (range jump point s) whose gap bottom κ has m_κ ≤ θ·ω: r(κ) < B_n s. -/
theorem skJumpShortBot (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) {n : ℕ}
    {R R' s κ : Ordinal.{0}} (hRc : R < Bc.bcC S (n + 1)) (h1s : Bc.bcC S n < s)
    (hcof : ∀ x < s, ∃ y, x < y ∧ y < s ∧ Xr.XrPt S n R R' y) (hsR : IsReach R2C s R)
    (hjump : ∃ Q < Bc.bcB S n s, ∀ q < s, Bc.bcB S n q ≤ Q) (hs : ∃ μ, CdRange S μ ∧ s = upsilon μ)
    (hκ : CdRange S κ) (he : sSup (Bc.bcB S n '' Iio s) = upsilon κ) (hm : cdCode S κ ≤ ConjT.th S * ω) :
    cdR S κ < Bc.bcB S n s :=
  Yz.yzJump_shortBot hν hU hL hRc h1s hcof hsR hjump hs hκ he hm

/-- STATUS: PROVED (round 130, Yz.yzJumpNoRng_iff, Yz.yzJump_short_noEQ)
SIZE: S
skJumpNoRng ⇔ YzJumpShort ∧ YzJumpLong (split by the code of the gap bottom); an instance with a short-code gap
bottom refutes CxEQtop (Yz.yzJump_short_noEQ), so skJumpNoRng holds there only by the absence of instances. -/
theorem skJumpSplit : Xw.XwJumpNoRng S ↔ Yz.YzJumpShort S ∧ Yz.YzJumpLong S := Yz.yzJumpNoRng_iff

/-- STATUS: PROVED (round 131, Ze.zeJumpShortU; NEW; no hypothesis beyond S)
SIZE: S
The short-code half of skJumpNoRng: no jump instance has a gap bottom with code ≤ θ·ω (statement Yz.YzJumpShort S;
Ze.zeCode_win, Yz.yzR_lowCode).  A REFUTE-FIRST record: the case where the target would fail cannot occur. -/
theorem skJumpShortU : Yz.YzJumpShort S := Ze.zeJumpShortU

/-- STATUS: PROVED (round 131, Ze.zeJumpLong; NEW)
SIZE: S
The long-code half of skJumpNoRng from hVt (statement Yz.YzJumpLong S). -/
theorem skJumpLongV (hVt : SkVt S) : Yz.YzJumpLong S := Ze.zeJumpLong hVt

/-- STATUS: PROVED (round 131, Ze.zeBad_top; NEW)
SIZE: S
A bad interval [β, β + ω^E) (β ≠ 0, ω^E ∣ β) makes β + ω^E bad; hence a good η = β + ω^E has ι(β) < ι(η)
(Ze.zeIota_prefix_lt). -/
theorem skBadTop {β E : Ordinal.{0}} (hβ0 : β ≠ 0) (hd : ω ^ E ∣ β)
    (hbad : ∀ ζ, β ≤ ζ → ζ < β + ω ^ E → ¬ Bt.Good S ζ) : ¬ Bt.Good S (β + ω ^ E) :=
  Ze.zeBad_top hβ0 hd hbad

/-- STATUS: PROVED (round 131, Ze.zeCap_win; NEW)
SIZE: S
The cap window: below every restart ρ_κ < L(ω+1) there is x < ρ_κ with cap(μ) ≤ ρ_κ for every restart
ρ_μ ∈ (x, ρ_κ). -/
theorem skCapWin {κ : Ordinal.{0}} (hκ : IsRestartIdx κ) (hκL : upsilon κ < Nc.ncL S (ω + 1)) :
    ∃ x < upsilon κ, ∀ μ, IsRestartIdx μ → x < upsilon μ → upsilon μ < upsilon κ →
      cdCapB S μ ≤ upsilon κ :=
  Ze.zeCap_win hκ hκL

/-- STATUS: PROVED (round 131, Ze.zeCode_win; NEW)
SIZE: S
Short codes are short near the top: m_κ ≤ θ·ω ⇒ every restart ρ_μ in a window (x, ρ_κ) has m_μ < θ·ω. -/
theorem skCodeWin {κ : Ordinal.{0}} (hκ : IsRestartIdx κ) (hκL : upsilon κ < Nc.ncL S (ω + 1))
    (hm : cdCode S κ ≤ ConjT.th S * ω) :
    ∃ x < upsilon κ, ∀ μ, IsRestartIdx μ → x < upsilon μ → upsilon μ < upsilon κ →
      cdCode S μ < ConjT.th S * ω :=
  Ze.zeCode_win hκ hκL hm

/-- STATUS: PROVED (round 131, Ze.zeGap_win; NEW; no hypothesis beyond S)
SIZE: S
The cap window of B_n p at a restart p = υ_κ of a gap configuration starts at a B_n-image: ∃ q < p, ∃ x ≤ B_n q,
every restart ρ_μ ∈ (x, B_n p) has cap(μ) ≤ B_n p. -/
theorem skGapWin {n : ℕ} {l l' p a κ : Ordinal.{0}} (hP : Ye.YeGapPt S n l l' p a)
    (hκ : IsRestartIdx κ) (hpκ : p = upsilon κ) :
    ∃ x q, q < p ∧ x ≤ Bc.bcB S n q ∧ ∀ μ, IsRestartIdx μ → x < upsilon μ →
      upsilon μ < Bc.bcB S n p → cdCapB S μ ≤ Bc.bcB S n p :=
  Ze.zeGap_win hP hκ hpκ

end R2Skel.SkE

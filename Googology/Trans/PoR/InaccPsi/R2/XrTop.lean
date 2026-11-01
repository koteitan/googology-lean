import Googology.Trans.PoR.InaccPsi.R2.XnRoad

/-!
# The top restart of the EQ induction: only the jumps of `B_n` are left

Notation as in `R2.XnInd`: `c_n = L(n+1)`, `B_n = Bc.bcB S n`, `ρ_λ = υ_λ`, `δ_λ = υ_{λ+ω+1}`, `k_λ = Cd.cdk λ`,
`T_λ = Θ_λ(m_λ)`, `r(λ) = k_λ(T_λ)`.

`Xn.xnEQ_all` proves EQ at every window by induction on `r(λ)`, leaving the top restart (`Xn.XnTop`): the inner
range restart `μ` with `ρ_μ = T_λ`, which has `r(μ) = r(λ)`.  Here the reach class `R` is handled at once.

Fix `n`, `R < c_{n+1}`, EQ at every smaller reach, and a window `λ` of reach `R` with image `λ'`, `R' = r(λ')`.
Suppose `B_n R ≠ R'`.  A **chain point** (`XrPt S n R R' x`) is `x = ρ_μ`, `μ` a range restart above `c_n` with
`r(μ) = R`, whose image `μ'` has `r(μ') = R'`.  Then:

* `xrPt_succ`: every chain point has a larger one (EQ fails at `μ`, so `μ` is a long-code window whose top
  `T_μ` is a cofinal far range restart `ν`; the reading move `SkThFar` and `XgKCof` give `r(ν') = R'`);
* so the chain points have no largest element; let `s` be their supremum.  `s ≤ R`, `lh(s) = R`
  (`≤₁` is closed under suprema on the left: `le1_of_cof_left`; `R` is closed at `λ`);
* if `B_n` is continuous at `s`, then `lh(B_n s) = R'` in the same way, and
  - `s` a range restart: `s` is a chain point, contradiction;
  - otherwise the reach of `s` moves (`Wa.waTCtopOff`): `B_n R = R'`, contradiction;
* so `B_n` jumps at `s`.  The leaf `XrJump` asks `B_n R = R'` exactly there.

Results: `xrEQ_all` (EQ everywhere from the part's other leaves and `XrJump`), `xrTop` (`XnTop`), `xrPart`.
Non-vacuity: `XrJump` follows from the target `Cx.CxEQtop` (`xrJump_of_EQtop`), and from each of the two older
leaves `Xn.XnTop` (`xrJump_of_top`) and `Xn.XnChainWF` (`xrJump_of_wf`); so it is weaker than both.
`xrGap_reach`: at a jump the gap bottom `s* = sup_{q<s} B_n q` has the reach `R'`; so `XrJump` is the statement
`lh(s*) = B_n(lh s)` there (`xrJump_of_gap`).

New definitions: the statement names `XrPt`, `XrJump`, `XrJumpGap`.  No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xr

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-! ## Small facts -/

/-- The reach is unique. -/
theorem xrReach_unique {a r r' : Ordinal.{0}} (h : IsReach R2C a r) (h' : IsReach R2C a r') : r = r' :=
  le_antisymm (h'.2 r h.1) (h.2 r' h'.1)

/-- A reach of a point below `L(ω+1)` is below `Ω₁` (under `L(ω+1) ≤ ν_C`). -/
theorem xrReach_lt_Om1 (hν : Nc.ncL S (ω + 1) ≤ nuC) {x r : Ordinal.{0}} (hx : x < Nc.ncL S (ω + 1))
    (h : IsReach R2C x r) : r < Om1 :=
  (not_lt.1 fun hlt => nuC_cap x (hx.le.trans hν) r hlt h.1).trans_lt nuC_lt_Om1

/-- **The reach move at a point of `(c_n, c_{n+1})` that is not a range restart**, when its reach is
below `c_{n+1}` (`Wa.waTCtopOff`). -/
theorem xrRM_off (hν : Nc.ncL S (ω + 1) ≤ nuC) {n : ℕ} {x R : Ordinal.{0}} (h1 : Bc.bcC S n < x)
    (hRc : R < Bc.bcC S (n + 1)) (hxR : IsReach R2C x R) (hnr : ∀ l, CdRange S l → x ≠ upsilon l) :
    IsReach R2C (Bc.bcB S n x) (Bc.bcB S n R) := by
  have hxc : x < Bc.bcC S (n + 1) := (le1_le hxR.1).trans_lt hRc
  rcases Wa.waTCtopOff hν n x h1 hxc hnr with ⟨r, -, h2, h3⟩ | hright
  · rw [xrReach_unique hxR h2]; exact h3
  · have hR1 := (hright (R + 1) ((le1_le hxR.1).trans le_self_add) (Xg.xgC_succ_lt n hRc)).1
    exact absurd (hxR.2 _ hR1) (not_le.2 (lt_add_one R))

/-! ## Chain points -/

/-- **A chain point** of the class `(R, R')`: `x = ρ_μ`, `μ` a range restart above `c_n` with `r(μ) = R`,
whose image `μ'` (`B_n ρ_μ = ρ_{μ'}`) has `r(μ') = R'`. -/
def XrPt (S : InaccSeq.{0}) (n : ℕ) (R R' x : Ordinal.{0}) : Prop :=
  ∃ μ μ', CdRange S μ ∧ Bc.bcC S n < upsilon μ ∧ upsilon μ = x ∧ cdR S μ = R ∧ IsRestartIdx μ' ∧
    Bc.bcB S n (upsilon μ) = upsilon μ' ∧ cdR S μ' = R'

/-- EQ at every range restart of `(c_n, …)` whose predicted reach is below `R`. -/
def XrIH (S : InaccSeq.{0}) (n : ℕ) (R : Ordinal.{0}) : Prop :=
  ∀ ν, CdRange S ν → Bc.bcC S n < upsilon ν → cdR S ν < R → Xn.XnEQat S n ν

/-- The facts carried by a chain point. -/
theorem xrPt_facts (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) {n : ℕ}
    {R R' x : Ordinal.{0}} (hRc : R < Bc.bcC S (n + 1)) (hx : XrPt S n R R' x) :
    Bc.bcC S n < x ∧ x < R ∧ IsReach R2C x R ∧ IsReach R2C (Bc.bcB S n x) R' ∧ R' < Om1 ∧
      x < Nc.ncL S ω := by
  obtain ⟨μ, μ', hμ, h1, rfl, hRμ, hμ', hB, hR'⟩ := hx
  have hxR : upsilon μ < R := hRμ ▸ cdRho_lt_R S μ
  have h2 : upsilon μ < Bc.bcC S (n + 1) := hxR.trans hRc
  have hμR := Xn.xnRange_img hμ h1 h2 hμ' hB
  have hr' : IsReach R2C (upsilon μ') (cdR S μ') := cdEnum_exact hU hL hμR
  refine ⟨h1, hxR, hRμ ▸ cdEnum_exact hU hL hμ, ?_, ?_, h2.trans (Bc.bcC_lt S (n + 1))⟩
  · rw [hB, ← hR']; exact hr'
  · rw [← hR']; exact xrReach_lt_Om1 hν hμR.2.2.1 hr'

/-! ## The successor step -/

/-- **Every chain point has a larger one** (when `B_n R ≠ R'`). -/
theorem xrPt_succ (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) (hTL : Wd.WdThLow S)
    (hTF : R2Skel.SkEX.SkThFar S) (hC : Xg.XgKCof S) {n : ℕ} {R R' : Ordinal.{0}}
    (hRc : R < Bc.bcC S (n + 1)) (IH : XrIH S n R) (hne : Bc.bcB S n R ≠ R') {x : Ordinal.{0}}
    (hx : XrPt S n R R' x) : ∃ y, x < y ∧ XrPt S n R R' y := by
  obtain ⟨μ, μ', hμ, h1, rfl, hRμ, hμ', hB, hR'⟩ := hx
  have hr : cdR S μ < Bc.bcC S (n + 1) := hRμ ▸ hRc
  by_cases hm : cdCode S μ ≤ upsilon μ
  · exact absurd (by rw [← hRμ, ← hR']; exact Xn.xnEQ_short hν hμ h1 hr hμ' hB hm) hne
  have hW : R2Skel.SkEX.SkWin S n μ μ' := ⟨hμ, h1, hr, hμ', hB, not_le.1 hm⟩
  have IH' : ∀ ν, CdRange S ν → Bc.bcC S n < upsilon ν → cdR S ν < cdR S μ → Xn.XnEQat S n ν :=
    fun ν a b c => IH ν a b (hRμ ▸ c)
  by_contra hno
  push Not at hno
  apply hne
  rw [← hRμ, ← hR']
  refine Xn.xnEQ_step hν hU hL hTL hTF hC hW IH' ?_
  intro ν hνr he hfar hcof
  exfalso
  set T := cdTheta S μ (cdCode S μ) with hT
  obtain ⟨hkC, hpC, hδp, hρp, hcn, hBδ, hBρ⟩ := Xg.xgWin_facts hν hW hfar he.le
  obtain ⟨ν', hν', e⟩ := Sf.sfRstMove (S := S) n ν hνr.1 hcn.le hpC
  have hνR' := Xn.xnRange_img hνr hcn hpC hν' e
  -- the move of `k` below `T`
  have hIH : ∀ q < upsilon ν, cdk μ' (Bc.bcB S n q) = Bc.bcB S n (cdk μ q) := by
    intro q hq
    have hqT : q ≤ T := hq.le.trans he.le
    refine Xn.xnKFar_upto hν hC hW hqT ?_ q le_rfl
    intro p hfp hpq hcp _
    have hpT : p < T := hpq.trans_lt (he ▸ hq)
    by_cases hr' : ∃ μ'', CdRange S μ'' ∧ p = upsilon μ''
    · obtain ⟨μ'', hμ'', rfl⟩ := hr'
      obtain ⟨hkC'', -, -, -, hcn'', -, -⟩ := Xg.xgWin_facts hν hW hfp hpT.le
      have hlt := Xn.xnR_inner_lt hν hU hL hW hμ'' hfp hpT hcp
      have hrμ : cdR S μ'' < Bc.bcC S (n + 1) := hlt.trans hr
      exact Xn.xnRM_of_EQ hU hL hμ'' hcn'' hrμ (IH' μ'' hμ'' hcn'' hlt)
    · push Not at hr'
      exact Xn.xnRM_nonRange hν hW hfp hpT.le fun μ'' hμ'' e' => hr' μ'' hμ'' e'
  have hcof' := hC n μ μ' hW (upsilon ν) hfar he.le hcof hIH
  have hrν' : IsReach R2C (Bc.bcB S n (upsilon ν)) (cdR S ν') := by
    rw [e]; exact cdEnum_exact hU hL hνR'
  have hk : cdk μ' (Bc.bcB S n (upsilon ν)) = cdR S ν' :=
    Xg.xgk_reach hBδ hBρ hcof' hrν' (xrReach_lt_Om1 hν hνR'.2.2.1 (e ▸ hrν'))
  have hT' : Bc.bcB S n T = cdTheta S μ' (cdCode S μ') := hTF n μ μ' hW (le_of_le_of_eq hfar he)
  have hRν' : cdR S ν' = cdR S μ' := by
    show cdR S ν' = cdk μ' (cdTheta S μ' (cdCode S μ'))
    rw [← hT', ← he, hk]
  have hRν : cdR S ν = R := (Xn.xnR_inner_top hν hU hL hW hνr hfar he hcof).trans hRμ
  have hlt : upsilon μ < upsilon ν := hρp
  exact hno (upsilon ν) hlt ⟨ν, ν', hνr, hcn, rfl, hRν, hν', e, hRν'.trans hR'⟩

/-! ## The leaf: the jumps of `B_n` -/

/-- **Leaf (the top restart at a jump of `B_n`)**.  Under the part's other hypotheses and EQ below the reach `R`:
let `s` be the supremum of the chain points of `(R, R')` (cofinal below `s`, none at or above `s`), `lh(s) = R`, and
let `B_n` jump at `s` (some `Q < B_n s` bounds every `B_n q`, `q < s`).  Then `B_n R = R'`. -/
def XrJump (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ R R' s : Ordinal.{0}, Nc.ncL S (ω + 1) ≤ nuC → CdUPPER S → CdLOWER S → Wd.WdThLow S →
    R2Skel.SkEX.SkThFar S → Xg.XgKCof S → R < Bc.bcC S (n + 1) → XrIH S n R → Bc.bcC S n < s →
    (∀ x < s, ∃ y, x < y ∧ y < s ∧ XrPt S n R R' y) → (∀ y, XrPt S n R R' y → y < s) →
    IsReach R2C s R → (∃ Q < Bc.bcB S n s, ∀ q < s, Bc.bcB S n q ≤ Q) → Bc.bcB S n R = R'

/-- The hypotheses of `XrJump` hold with `s = sSup` of the chain points when `B_n R ≠ R'` and there is a chain point;
this is the class step. -/
theorem xrClass (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) (hTL : Wd.WdThLow S)
    (hTF : R2Skel.SkEX.SkThFar S) (hC : Xg.XgKCof S) (hJ : XrJump S) {n : ℕ} {R : Ordinal.{0}}
    (hRc : R < Bc.bcC S (n + 1)) (IH : XrIH S n R) :
    ∀ l, CdRange S l → Bc.bcC S n < upsilon l → cdR S l = R → Xn.XnEQat S n l := by
  intro l hl h1 hlR l' hl' hB
  by_contra hne0
  set R' := cdR S l' with hR'
  have hne : Bc.bcB S n R ≠ R' := fun h => hne0 (hlR ▸ h)
  set W : Set Ordinal.{0} := {x | XrPt S n R R' x} with hWdef
  have hx0 : upsilon l ∈ W := ⟨l, l', hl, h1, rfl, hlR, hl', hB, rfl⟩
  have hfacts : ∀ x ∈ W, Bc.bcC S n < x ∧ x < R ∧ IsReach R2C x R ∧ IsReach R2C (Bc.bcB S n x) R' ∧
      R' < Om1 ∧ x < Nc.ncL S ω := fun x hx => xrPt_facts hν hU hL hRc hx
  have hbdd : BddAbove W := ⟨R, fun x hx => (hfacts x hx).2.1.le⟩
  have hsucc : ∀ x ∈ W, ∃ y ∈ W, x < y := fun x hx => by
    obtain ⟨y, hxy, hy⟩ := xrPt_succ hν hU hL hTL hTF hC hRc IH hne hx
    exact ⟨y, hy, hxy⟩
  set s := sSup W with hs
  have hsW : s ∉ W := fun h => by
    obtain ⟨y, hy, hsy⟩ := hsucc s h
    exact absurd (le_csSup hbdd hy) (not_le.2 hsy)
  have hcof : ∀ x < s, ∃ y, x < y ∧ y < s ∧ y ∈ W := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := (lt_csSup_iff hbdd ⟨_, hx0⟩).1 hx
    exact ⟨y, hxy, lt_of_le_of_ne (le_csSup hbdd hy) (fun h => hsW (h ▸ hy)), hy⟩
  have hup : ∀ y ∈ W, y < s := fun y hy =>
    lt_of_le_of_ne (le_csSup hbdd hy) (fun h => hsW (h ▸ hy))
  have hsR : s ≤ R := csSup_le ⟨_, hx0⟩ fun x hx => (hfacts x hx).2.1.le
  have hls : upsilon l < s := hup _ hx0
  have h1s : Bc.bcC S n < s := h1.trans hls
  have hsc : s < Bc.bcC S (n + 1) := hsR.trans_lt hRc
  have hsL : s < Nc.ncL S ω := hsc.trans (Bc.bcC_lt S (n + 1))
  have hRΩ : R < Om1 := (hRc.trans (Bc.bcC_lt S (n + 1))).trans (Xg.xgL_lt_Om1 hν)
  -- `lh(s) = R`
  have hsReach : IsReach R2C s R := by
    refine ⟨le1_of_cof_left hsR (lt_of_le_of_lt zero_le hls) fun x hx => ?_, fun g hg => ?_⟩
    · obtain ⟨y, hxy, hys, hy⟩ := hcof x hx
      exact ⟨y, hxy, hys.le, (hfacts y hy).2.2.1.1⟩
    · have hcl : cdClosed l R := by
        have hRΩ' : cdR S l < Om1 := by rw [hlR]; exact hRΩ
        rw [← hlR]; exact cdk_closed hRΩ'
      exact hcl.2 s hls hsR g hg
  by_cases hcont : ∀ Q < Bc.bcB S n s, ∃ q < s, Q ≤ Bc.bcB S n q
  · -- `lh(B_n s) = R'`
    have hl'R : CdRange S l' := Xn.xnRange_img hl h1 (hls.trans hsc) hl' hB
    have hR'Ω : R' < Om1 := (hfacts _ hx0).2.2.2.2.1
    have hBmono : ∀ {a b : Ordinal.{0}}, a < s → b ≤ s → a < b → Bc.bcB S n a < Bc.bcB S n b :=
      fun ha hb hab => (Bc.bcB_lt_iff (ha.trans hsL) (hb.trans_lt hsL)).2 hab
    have hBsR' : Bc.bcB S n s ≤ R' := by
      by_contra hlt
      push Not at hlt
      obtain ⟨q, hq, hQ⟩ := hcont R' hlt
      obtain ⟨y, hqy, hys, hy⟩ := hcof q hq
      have h3 := hBmono hq hys.le hqy
      exact absurd (le1_le (hfacts y hy).2.2.2.1.1) (not_le.2 (hQ.trans_lt h3))
    have hB0 : 0 < Bc.bcB S n s := lt_of_le_of_lt zero_le (hBmono hls le_rfl hls)
    have hBReach : IsReach R2C (Bc.bcB S n s) R' := by
      refine ⟨le1_of_cof_left hBsR' hB0 fun X hX => ?_, fun g hg => ?_⟩
      · obtain ⟨q, hq, hQ⟩ := hcont X hX
        obtain ⟨y, hqy, hys, hy⟩ := hcof q hq
        exact ⟨Bc.bcB S n y, hQ.trans_lt (hBmono hq hys.le hqy), (hBmono hys le_rfl hys).le,
          (hfacts y hy).2.2.2.1.1⟩
      · have hcl : cdClosed l' R' := cdk_closed hR'Ω
        have hρ' : upsilon l' < Bc.bcB S n s := by rw [← hB]; exact hBmono hls le_rfl hls
        exact hcl.2 _ hρ' hBsR' g hg
    by_cases hr : ∃ μ, CdRange S μ ∧ s = upsilon μ
    · obtain ⟨μ, hμ, hsμ⟩ := hr
      obtain ⟨μ', hμ', e⟩ := Sf.sfRstMove (S := S) n μ hμ.1 (hsμ ▸ h1s.le) (hsμ ▸ hsc)
      have hμR := Xn.xnRange_img hμ (hsμ ▸ h1s) (hsμ ▸ hsc) hμ' e
      refine hsW ⟨μ, μ', hμ, hsμ ▸ h1s, hsμ.symm, ?_, hμ', e, ?_⟩
      · exact xrReach_unique (cdEnum_exact hU hL hμ) (hsμ ▸ hsReach)
      · refine xrReach_unique (cdEnum_exact hU hL hμR) ?_
        rw [← e, ← hsμ]; exact hBReach
    · push Not at hr
      have hm := xrRM_off hν h1s hRc hsReach fun μ hμ he => hr μ hμ he
      exact hne (xrReach_unique hm hBReach)
  · push Not at hcont
    obtain ⟨Q, hQ, hQq⟩ := hcont
    exact hne (hJ n R R' s hν hU hL hTL hTF hC hRc IH h1s
      (fun x hx => by obtain ⟨y, a, b, c⟩ := hcof x hx; exact ⟨y, a, b, c⟩) hup hsReach
      ⟨Q, hQ, fun q hq => (hQq q hq).le⟩)

/-- **EQ AT EVERY WINDOW** from ENUM-REACH, the reading moves, `XgKCof` and the jump leaf `XrJump`
(induction on the predicted reach `r(λ)`, each reach class by `xrClass`). -/
theorem xrEQ_all (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) (hTL : Wd.WdThLow S)
    (hTF : R2Skel.SkEX.SkThFar S) (hC : Xg.XgKCof S) (hJ : XrJump S) :
    ∀ n : ℕ, ∀ l, CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) → Xn.XnEQat S n l := by
  intro n
  suffices H : ∀ R, R < Bc.bcC S (n + 1) → ∀ l, CdRange S l → Bc.bcC S n < upsilon l → cdR S l = R →
      Xn.XnEQat S n l from fun l hR h1 hr => H _ hr l hR h1 rfl
  intro R
  induction R using WellFoundedLT.induction with
  | ind R IHR =>
  intro hRc
  exact xrClass hν hU hL hTL hTF hC hJ hRc
    (fun ν hν1 hν2 hlt => IHR _ hlt (hlt.trans hRc) ν hν1 hν2 rfl)

/-- **`XnTop` from `XrJump`** (and the part's other hypotheses). -/
theorem xrTop (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) (hTL : Wd.WdThLow S)
    (hTF : R2Skel.SkEX.SkThFar S) (hC : Xg.XgKCof S) (hJ : XrJump S) : Xn.XnTop S :=
  Xn.xnTop_of_EQtop hν hU hL (Xn.xnEQtop_of (xrEQ_all hν hU hL hTL hTF hC hJ))

/-- **THE PART with `XrJump` in place of `XnTop`**: `WdThLow`, `WdEQfar`, `XgKReachR`, `SkKFar`, `CxEQtop`. -/
theorem xrPart (hν : Nc.ncL S (ω + 1) ≤ nuC) (hW : Wd.WdAtWall S) (hH : Wd.WdThHi S) (hU : CdUPPER S)
    (hL : CdLOWER S) (hTF : R2Skel.SkEX.SkThFar S) (hC : Xg.XgKCof S) (hJ : XrJump S) :
    Wd.WdThLow S ∧ Wd.WdEQfar S ∧ Xg.XgKReachR S ∧ R2Skel.SkEX.SkKFar S ∧ Cx.CxEQtop S :=
  Xn.xnPart hν hW hH hU hL hTF hC (xrTop hν hU hL (Xn.xnThLow hν hW hH) hTF hC hJ)

/-! ## Non-vacuity -/

/-- EQ everywhere gives the conclusion of `XrJump` (at any chain point). -/
theorem xrJump_of_EQall
    (H : ∀ n : ℕ, Nc.ncL S (ω + 1) ≤ nuC → CdUPPER S → CdLOWER S → Wd.WdThLow S → R2Skel.SkEX.SkThFar S →
      Xg.XgKCof S → ∀ l, CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
      Xn.XnEQat S n l) : XrJump S := by
  intro n R R' s hν hU hL hTL hTF hC hRc _ h1s hcof _ _ _
  obtain ⟨y, -, -, μ, μ', hμ, h1, -, hRμ, hμ', hB, hR'⟩ := hcof _ h1s
  rw [← hRμ, ← hR']
  exact H n hν hU hL hTL hTF hC μ hμ h1 (hRμ ▸ hRc) μ' hμ' hB

/-- **NON-VACUITY: the target `CxEQtop` gives `XrJump`.** -/
theorem xrJump_of_EQtop (h : Cx.CxEQtop S) : XrJump S :=
  xrJump_of_EQall fun n _ _ _ _ _ _ => Xn.xnEQat_of_top h n

/-- **`XnTop` gives `XrJump`** (so `XrJump` is weaker than the old leaf). -/
theorem xrJump_of_top (hTop : Xn.XnTop S) : XrJump S :=
  xrJump_of_EQall fun n hν hU hL hTL hTF hC => Xn.xnEQ_all hν hU hL hTL hTF hC hTop n

/-- **`XnChainWF` gives `XrJump`** (so `XrJump` is weaker than the well-foundedness guard). -/
theorem xrJump_of_wf (hWF : Xn.XnChainWF S) : XrJump S :=
  xrJump_of_EQall fun n hν hU hL hTL hTF hC => Xn.xnEQ_all_wf hν hU hL hTL hTF hC hWF n

/-! ## The leaf as a reach at the gap bottom -/

/-- **At a jump the gap bottom `s* = sup_{q<s} B_n q` has the reach `R'`** (chain points cofinal below `s`). -/
theorem xrGap_reach (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) {n : ℕ}
    {R R' s : Ordinal.{0}} (hRc : R < Bc.bcC S (n + 1)) (h1s : Bc.bcC S n < s)
    (hcof : ∀ x < s, ∃ y, x < y ∧ y < s ∧ XrPt S n R R' y) (hsR : s ≤ R) :
    IsReach R2C (sSup (Bc.bcB S n '' Iio s)) R' := by
  have hsL : s < Nc.ncL S ω := (hsR.trans_lt hRc).trans (Bc.bcC_lt S (n + 1))
  have hBmono : ∀ {a b : Ordinal.{0}}, a < s → b < s → a < b → Bc.bcB S n a < Bc.bcB S n b :=
    fun ha hb hab => (Bc.bcB_lt_iff (ha.trans hsL) (hb.trans hsL)).2 hab
  have hbdd : BddAbove (Bc.bcB S n '' Iio s) :=
    ⟨Bc.bcB S n s, by
      rintro _ ⟨q, hq, rfl⟩
      exact ((Bc.bcB_lt_iff (hq.trans hsL) hsL).2 hq).le⟩
  set s' := sSup (Bc.bcB S n '' Iio s) with hs'
  have hmem : ∀ y, y < s → Bc.bcB S n y ≤ s' := fun y hy => le_csSup hbdd ⟨y, hy, rfl⟩
  obtain ⟨y0, -, hy0s, hy0⟩ := hcof _ h1s
  obtain ⟨-, -, -, hB0R, hR'Ω, -⟩ := xrPt_facts hν hU hL hRc hy0
  have hs'R' : s' ≤ R' := by
    refine csSup_le ⟨_, y0, hy0s, rfl⟩ ?_
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨y, hqy, hys, hy⟩ := hcof q hq
    exact (hBmono hq hys hqy).le.trans (le1_le (xrPt_facts hν hU hL hRc hy).2.2.2.1.1)
  obtain ⟨y1, hy01, hy1s, -⟩ := hcof y0 hy0s
  have hlt01 : Bc.bcB S n y0 < s' := (hBmono hy0s hy1s hy01).trans_le (hmem y1 hy1s)
  refine ⟨le1_of_cof_left hs'R' (lt_of_le_of_lt zero_le hlt01) fun X hX => ?_, fun g hg => ?_⟩
  · obtain ⟨_, ⟨q, hq, rfl⟩, hXq⟩ := (lt_csSup_iff hbdd ⟨_, y0, hy0s, rfl⟩).1 hX
    obtain ⟨y, hqy, hys, hy⟩ := hcof q hq
    exact ⟨Bc.bcB S n y, hXq.trans (hBmono hq hys hqy), hmem y hys,
      (xrPt_facts hν hU hL hRc hy).2.2.2.1.1⟩
  · obtain ⟨μ, μ', hμ, h1, e0, hRμ, hμ', hB, hR'⟩ := hy0
    have hcl : cdClosed μ' R' := by
      have hΩ : cdR S μ' < Om1 := hR' ▸ hR'Ω
      rw [← hR']; exact cdk_closed hΩ
    have hρ : upsilon μ' < s' := by rw [← hB, e0]; exact hlt01
    exact hcl.2 _ hρ hs'R' g hg

/-- **Leaf, gap form**: the hypotheses of `XrJump`, conclusion `lh(s*) = B_n R` for `s* = sup_{q<s} B_n q`. -/
def XrJumpGap (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ R R' s : Ordinal.{0}, Nc.ncL S (ω + 1) ≤ nuC → CdUPPER S → CdLOWER S → Wd.WdThLow S →
    R2Skel.SkEX.SkThFar S → Xg.XgKCof S → R < Bc.bcC S (n + 1) → XrIH S n R → Bc.bcC S n < s →
    (∀ x < s, ∃ y, x < y ∧ y < s ∧ XrPt S n R R' y) → (∀ y, XrPt S n R R' y → y < s) →
    IsReach R2C s R → (∃ Q < Bc.bcB S n s, ∀ q < s, Bc.bcB S n q ≤ Q) →
    IsReach R2C (sSup (Bc.bcB S n '' Iio s)) (Bc.bcB S n R)

/-- **`XrJump ⇔ XrJumpGap`**: at a jump, the top EQ is exactly `lh(s*) = B_n(lh s)`. -/
theorem xrJump_iff_gap : XrJump S ↔ XrJumpGap S := by
  constructor
  · intro hJ n R R' s hν hU hL hTL hTF hC hRc IH h1s hcof hup hsR hjump
    rw [hJ n R R' s hν hU hL hTL hTF hC hRc IH h1s hcof hup hsR hjump]
    exact xrGap_reach hν hU hL hRc h1s hcof (hsR.2 s (le1_refl s))
  · intro hG n R R' s hν hU hL hTL hTF hC hRc IH h1s hcof hup hsR hjump
    exact xrReach_unique (hG n R R' s hν hU hL hTL hTF hC hRc IH h1s hcof hup hsR hjump)
      (xrGap_reach hν hU hL hRc h1s hcof (hsR.2 s (le1_refl s)))

end Googology.Trans.PoR.InaccPsi.R2.Xr

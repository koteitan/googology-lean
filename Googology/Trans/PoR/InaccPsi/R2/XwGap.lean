import Googology.Trans.PoR.InaccPsi.R2.XwFirst

/-!
# The jump-gap leaf `Xr.XrKCofGap` as a statement on reaches in the gap

Notation as in `R2.XrCof`.  A cofinal far index `p` of a window `(n, λ, λ')` (`δ_λ·ω ≤ p ≤ Θ_λ(m_λ)`,
`k_λ(q) < p` for `q < p`, the `k`-move below `p`), `X = B_n p`.  A *gap point* is `a < X` with `B_n q ≤ a` for
every `q < p`.

* `xwDecomp`: if `p` is decomposable, the conclusion of `XgKCof` at `p` holds outright (write `p = u + w`, `w` the
  least such tail; `w` is indecomposable, `w ≤ u`; the block `[k_{λ'}(B_n u), k_{λ'}(B_n u)·ω)` of closed points
  covers `[B_n u, X)`).  So only indecomposable `p` matter.
* `xwClosed_at`: if every gap point has its reach below `X`, then every gap point lies below a closed point of
  `λ'` below `X` (the least point `a₀ ≤ Q` with a `≤₁`-successor above `Q` is a gap point; its reach is closed at
  `λ'`: below `a₀` by minimality, on `[a₀, lh(a₀)]` by `≤₁`-transitivity).
* `XwGapLh`: **every point of the jump gap of `B_n` at an indecomposable cofinal far index `p` has its reach inside
  the gap** (`lh(a) < B_n p`).  `xwKCofGap_iff`: `XrKCofGap ⇔ XwGapLh` (unconditional);
  `xwKCof_iff`: `Xg.XgKCof ⇔ XwGapLh`.
* `xwGapLh_iff`: under ENUM-REACH, `XwGapLh ⇔ XwGapRst ∧ XwGapOff`: at the range restarts `ν` in the gap the
  predicted reach `r(ν) < B_n p`; at the other gap points the reach is below `B_n p`.
* Non-vacuity: `xwGapLh_of_far` (`SkKFar ∧ XgKReachR ⇒ XwGapLh`), `xwGapLh_of_target`.

New definitions: the statement names `XwGapLh`, `XwGapRst`, `XwGapOff`.  No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- Facts at a far index `p ≤ Θ_λ(m_λ)` of a window. -/
theorem xwWin {n : ℕ} {l l' p : Ordinal.{0}} (hW : R2Skel.SkEX.SkWin S n l l') (hfar : cdDelta l * ω ≤ p)
    (hp : p ≤ cdTheta S l (cdCode S l)) :
    p < Bc.bcC S (n + 1) ∧ p < Nc.ncL S ω ∧ Bc.bcB S n p < Om1 ∧ cdDelta l < p ∧
      Bc.bcB S n (cdDelta l) = cdDelta l' := by
  obtain ⟨hR, h1, hr, -, hB, -⟩ := hW
  have hkC : cdk l p < Bc.bcC S (n + 1) := ((cdk_strictMono l).monotone hp).trans_lt hr
  have hpC : p < Bc.bcC S (n + 1) := ((cdk_strictMono l).id_le p).trans_lt hkC
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  refine ⟨hpC, hpC.trans (Bc.bcC_lt S (n + 1)), ((Bc.bcB_bound' S n p hpC).trans xwL_lt_Om1),
    (xw_lt_mulw (Xg.xgDelta_pos l)).trans_le hfar, Mv.mvDelta_move hR.1 h1 hδr hB⟩

/-! ## Decomposable indices -/

/-- **At a decomposable cofinal far index the conclusion of `XgKCof` holds** (no hypothesis on the gap). -/
theorem xwDecomp {n : ℕ} {l l' p : Ordinal.{0}} (hW : R2Skel.SkEX.SkWin S n l l')
    (hfar : cdDelta l * ω ≤ p) (hp : p ≤ cdTheta S l (cdCode S l)) (hcof : ∀ q < p, cdk l q < p)
    (hIH : ∀ q < p, cdk l' (Bc.bcB S n q) = Bc.bcB S n (cdk l q)) (hI : ¬ Indec p) :
    ∀ Q < Bc.bcB S n p, cdk l' Q < Bc.bcB S n p := by
  obtain ⟨-, hpL, -, hδp, -⟩ := xwWin hW hfar hp
  have hp0 : p ≠ 0 := (lt_of_le_of_lt zero_le hδp).ne'
  have hnP : ¬ IsPrincipal (· + ·) p := fun h => hI (indec_iff.2 ⟨hp0, h⟩)
  set Wt : Set Ordinal.{0} := {w | 0 < w ∧ ∃ u < p, u + w = p} with hWt
  have hne : Wt.Nonempty := by
    simp only [IsPrincipal, not_forall, not_lt] at hnP
    obtain ⟨a, b, ha, hb, hab⟩ := hnP
    obtain ⟨c, hc⟩ := exists_add_of_le ha.le
    refine ⟨c, pos_iff_ne_zero.2 fun e => ?_, a, ha, hc.symm⟩
    rw [e, add_zero] at hc; exact lt_irrefl _ (hc ▸ ha)
  set w := sInf Wt with hw
  obtain ⟨hw0, u, hu, huw⟩ := csInf_mem hne
  rw [← hw] at hw0 huw
  have hwP : IsPrincipal (· + ·) w := by
    intro x y hx hy
    by_contra hxy
    push Not at hxy
    obtain ⟨d, hd⟩ := exists_add_of_le hx.le
    have hdy : d ≤ y := (add_le_add_iff_left x).1 (hd ▸ hxy)
    have hd0 : 0 < d := pos_iff_ne_zero.2 fun e => by
      rw [e, add_zero] at hd; exact lt_irrefl _ (hd ▸ hx)
    have hux : u + x < p := by rw [← huw]; exact (add_lt_add_iff_left u).2 hx
    have hdW : d ∈ Wt := ⟨hd0, u + x, hux, by rw [add_assoc, ← hd, huw]⟩
    exact absurd (csInf_le' hdW) (not_le.2 (hdy.trans_lt hy))
  have hwu : w ≤ u := by
    by_contra hlt
    push Not at hlt
    have e : u + w = w := isPrincipal_add_iff_add_left_eq_self.1 hwP u hlt
    rw [e] at huw
    exact hnP (huw ▸ hwP)
  have hwp : w < p := hwu.trans_lt hu
  have huL : u < Nc.ncL S ω := hu.trans hpL
  have hwL : w < Nc.ncL S ω := hwp.trans hpL
  have hku : cdk l u < p := hcof u hu
  have huk : u ≤ cdk l u := (cdk_strictMono l).id_le u
  obtain ⟨w0, hw0e⟩ := exists_add_of_le huk
  have hw0w : w0 < w := (add_lt_add_iff_left u).1 (by rw [← hw0e, huw]; exact hku)
  have hw0L : w0 < Nc.ncL S ω := hw0w.trans hwL
  have hBp : Bc.bcB S n p = Bc.bcB S n u + Bc.bcB S n w := by
    rw [← Bc.bcB_add huL hwL, huw]
  have hBk : Bc.bcB S n (cdk l u) = Bc.bcB S n u + Bc.bcB S n w0 := by
    rw [hw0e, Bc.bcB_add huL hw0L]
  have hBwP : IsPrincipal (· + ·) (Bc.bcB S n w) :=
    (indec_iff.1 (Bc.bcB_indec hwL (indec_iff.2 ⟨hw0.ne', hwP⟩))).2
  have hBwu : Bc.bcB S n w ≤ Bc.bcB S n u := Xg.xgB_le hwL huL hwu
  intro Q hQ
  by_cases hQu : Q ≤ Bc.bcB S n u
  · exact Xr.xrKCof_below hW hp hcof hIH hu hQu
  push Not at hQu
  obtain ⟨Z, rfl⟩ := exists_add_of_le hQu.le
  have hZw : Z < Bc.bcB S n w := (add_lt_add_iff_left _).1 (hBp ▸ hQ)
  have hkpos : 0 < cdk l' (Bc.bcB S n u) := Xg.xgK_pos (cdk_mem l' _)
  have hZk : Z < cdk l' (Bc.bcB S n u) * ω :=
    ((hZw.trans_le hBwu).trans_le ((cdk_strictMono l').id_le _)).trans (xw_lt_mulw hkpos)
  rw [Xg.xgk_add hZk, hIH u hu, hBk, hBp, add_assoc]
  exact (add_lt_add_iff_left _).2 (hBwP ((Bc.bcB_lt_iff hw0L hwL).2 hw0w) hZw)

/-! ## Closed points from reaches in the gap -/

/-- **Closed points from reaches in the gap**: if every gap point has its reach below `X = B_n p`, every gap point
`Q` lies below a closed point of `λ'` below `X`. -/
theorem xwClosed_at {n : ℕ} {l l' p : Ordinal.{0}} (hW : R2Skel.SkEX.SkWin S n l l')
    (hfar : cdDelta l * ω ≤ p) (hp : p ≤ cdTheta S l (cdCode S l)) (hcof : ∀ q < p, cdk l q < p)
    (hIH : ∀ q < p, cdk l' (Bc.bcB S n q) = Bc.bcB S n (cdk l q))
    (hlh : ∀ a < Bc.bcB S n p, (∀ q < p, Bc.bcB S n q ≤ a) →
      ∃ r, IsReach R2C a r ∧ r < Bc.bcB S n p)
    {Q : Ordinal.{0}} (hQ : Q < Bc.bcB S n p) (hgap : ∀ q < p, Bc.bcB S n q ≤ Q) :
    ∃ y ∈ cdK l', Q ≤ y ∧ y < Bc.bcB S n p := by
  obtain ⟨-, hpL, hXΩ, hδp, hBδ⟩ := xwWin hW hfar hp
  have hgδ : ∀ a, (∀ q < p, Bc.bcB S n q ≤ a) → cdDelta l' ≤ a := fun a ha => by
    rw [← hBδ]; exact ha _ hδp
  have hcl : ∀ q < p, cdClosed l' (Bc.bcB S n (cdk l q)) := fun q hq => by
    have hlt : cdk l' (Bc.bcB S n q) < Om1 := by
      rw [hIH q hq]; exact (lt_of_le_of_lt (hgap _ (hcof q hq)) hQ).trans hXΩ
    rw [← hIH q hq]; exact cdk_closed hlt
  by_cases hP : ∃ a, upsilon l' < a ∧ a ≤ Q ∧ ∃ g, Q < g ∧ le1 a g
  · obtain ⟨a0, ⟨hρa, haQ, g0, hQg, hag⟩, hmin⟩ := WellFounded.has_min wellFounded_lt
      {a | upsilon l' < a ∧ a ≤ Q ∧ ∃ g, Q < g ∧ le1 a g} hP
    have hgap0 : ∀ q < p, Bc.bcB S n q ≤ a0 := by
      intro q hq
      by_contra hlt
      push Not at hlt
      have hle : a0 ≤ Bc.bcB S n (cdk l q) :=
        hlt.le.trans (Xg.xgB_le (hq.trans hpL) ((hcof q hq).trans hpL) ((cdk_strictMono l).id_le q))
      have h1 := (hcl q hq).2 a0 hρa hle g0 hag
      exact absurd (h1.trans (hgap _ (hcof q hq))) (not_le.2 hQg)
    obtain ⟨r, hr, hrX⟩ := hlh a0 (haQ.trans_lt hQ) hgap0
    have hQr : Q ≤ r := (hQg.trans_le (hr.2 g0 hag)).le
    refine ⟨r, Or.inl ⟨(hgδ a0 hgap0).trans (le1_le hr.1), fun a ha har g hag' => ?_⟩, hQr, hrX⟩
    rcases lt_or_ge a a0 with haa | haa
    · by_contra hgr
      push Not at hgr
      have hQgl : Q < g := hQr.trans_lt hgr
      exact hmin a ⟨ha, haa.le.trans haQ, g, hQgl, hag'⟩ haa
    · exact hr.2 g (le1_trans (le1_of_le_of_le1 haa har hr.1) hag')
  · push Not at hP
    refine ⟨Q, Or.inl ⟨hgδ Q hgap, fun a ha haQ g hag => ?_⟩, le_rfl, hQ⟩
    by_contra h
    push Not at h
    exact hP a ha haQ g h hag

/-! ## The leaf as a reach statement -/

/-- **Leaf (reaches in the jump gap)**: at an indecomposable cofinal far index `p` with the `k`-move below `p`,
every gap point `a` (`B_n q ≤ a < B_n p` for all `q < p`) has a reach `lh(a) < B_n p`. -/
def XwGapLh (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', R2Skel.SkEX.SkWin S n l l' → ∀ p, cdDelta l * ω ≤ p → p ≤ cdTheta S l (cdCode S l) →
    Indec p → (∀ q < p, cdk l q < p) → (∀ q < p, cdk l' (Bc.bcB S n q) = Bc.bcB S n (cdk l q)) →
    ∀ a < Bc.bcB S n p, (∀ q < p, Bc.bcB S n q ≤ a) → ∃ r, IsReach R2C a r ∧ r < Bc.bcB S n p

/-- **`XwGapLh ⇒ XrKCofGap`.** -/
theorem xwKCofGap_of_lh (h : XwGapLh S) : Xr.XrKCofGap S := by
  intro n l l' hW p hfar hp hcof hIH Q hQ hgap
  by_cases hI : Indec p
  · obtain ⟨-, hpL, -, -, -⟩ := xwWin hW hfar hp
    have hXI : Indec (Bc.bcB S n p) := Bc.bcB_indec hpL hI
    exact (Xr.xrKCof_gap_unbdd hW hp hcof hIH hXI).2
      (fun Q' hQ' hg' => xwClosed_at hW hfar hp hcof hIH (h n l l' hW p hfar hp hI hcof hIH) hQ' hg')
      Q hQ hgap
  · exact xwDecomp hW hfar hp hcof hIH hI Q hQ

/-- **`XrKCofGap ⇒ XwGapLh`.** -/
theorem xwLh_of_KCofGap (h : Xr.XrKCofGap S) : XwGapLh S := by
  intro n l l' hW p hfar hp _ hcof hIH a ha hgap
  obtain ⟨-, -, hXΩ, hδp, hBδ⟩ := xwWin hW hfar hp
  have hk := h n l l' hW p hfar hp hcof hIH a ha hgap
  have hcl : cdClosed l' (cdk l' a) := cdk_closed (hk.trans hXΩ)
  have hδa : cdDelta l' ≤ a := by rw [← hBδ]; exact hgap _ hδp
  have hρa : upsilon l' < a := (cdRho_lt_delta l').trans_le hδa
  have hle : ∀ g, le1 a g → g ≤ cdk l' a := hcl.2 a hρa ((cdk_strictMono l').id_le a)
  obtain ⟨r, hr⟩ := exists_reach (a := a) (g := cdk l' a + 1)
    (((cdk_strictMono l').id_le a).trans le_self_add)
    (fun h1 => absurd (hle _ h1) (not_le.2 (lt_add_one _)))
  exact ⟨r, hr, (hle r hr.1).trans_lt hk⟩

/-- **`XrKCofGap ⇔ XwGapLh`** (unconditional). -/
theorem xwKCofGap_iff : Xr.XrKCofGap S ↔ XwGapLh S := ⟨xwLh_of_KCofGap, xwKCofGap_of_lh⟩

/-- **`XgKCof ⇔ XwGapLh`** (unconditional). -/
theorem xwKCof_iff : Xg.XgKCof S ↔ XwGapLh S := Xr.xrKCof_iff_gap.trans xwKCofGap_iff

/-! ## Range restarts and other points of the gap -/

/-- **Leaf part 1**: every range restart `ν` in the jump gap has `r(ν) < B_n p`. -/
def XwGapRst (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', R2Skel.SkEX.SkWin S n l l' → ∀ p, cdDelta l * ω ≤ p → p ≤ cdTheta S l (cdCode S l) →
    Indec p → (∀ q < p, cdk l q < p) → (∀ q < p, cdk l' (Bc.bcB S n q) = Bc.bcB S n (cdk l q)) →
    ∀ ν, CdRange S ν → upsilon ν < Bc.bcB S n p → (∀ q < p, Bc.bcB S n q ≤ upsilon ν) →
    cdR S ν < Bc.bcB S n p

/-- **Leaf part 2**: every gap point that is not a range restart has a reach below `B_n p`. -/
def XwGapOff (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', R2Skel.SkEX.SkWin S n l l' → ∀ p, cdDelta l * ω ≤ p → p ≤ cdTheta S l (cdCode S l) →
    Indec p → (∀ q < p, cdk l q < p) → (∀ q < p, cdk l' (Bc.bcB S n q) = Bc.bcB S n (cdk l q)) →
    ∀ a < Bc.bcB S n p, (∀ q < p, Bc.bcB S n q ≤ a) → (∀ ν, CdRange S ν → a ≠ upsilon ν) →
    ∃ r, IsReach R2C a r ∧ r < Bc.bcB S n p

/-- **Under ENUM-REACH, `XwGapLh ⇔ XwGapRst ∧ XwGapOff`.** -/
theorem xwGapLh_iff (hU : CdUPPER S) (hL : CdLOWER S) : XwGapLh S ↔ XwGapRst S ∧ XwGapOff S := by
  constructor
  · intro h
    refine ⟨fun n l l' hW p hfar hp hI hcof hIH ν hν hνX hg => ?_,
      fun n l l' hW p hfar hp hI hcof hIH a ha hg _ => h n l l' hW p hfar hp hI hcof hIH a ha hg⟩
    obtain ⟨r, hr, hrX⟩ := h n l l' hW p hfar hp hI hcof hIH _ hνX hg
    rw [Xr.xrReach_unique (cdEnum_exact hU hL hν) hr]; exact hrX
  · rintro ⟨hR, hO⟩ n l l' hW p hfar hp hI hcof hIH a ha hg
    by_cases hr : ∃ ν, CdRange S ν ∧ a = upsilon ν
    · obtain ⟨ν, hν, rfl⟩ := hr
      exact ⟨cdR S ν, cdEnum_exact hU hL hν, hR n l l' hW p hfar hp hI hcof hIH ν hν ha hg⟩
    · push Not at hr
      exact hO n l l' hW p hfar hp hI hcof hIH a ha hg hr

/-! ## Non-vacuity -/

/-- **NON-VACUITY**: `SkKFar ∧ XgKReachR ⇒ XwGapLh` (under `L(ω+1) ≤ ν_C`). -/
theorem xwGapLh_of_far (hν : Nc.ncL S (ω + 1) ≤ nuC) (hK : R2Skel.SkEX.SkKFar S) (hR : Xg.XgKReachR S) :
    XwGapLh S :=
  xwKCof_iff.1 (Xg.xgCof_of_far hν hK (Xg.xgKReach_of hν hR))

/-- **NON-VACUITY against the target**: `hν ∧ CdUPPER ∧ CdLOWER ∧ CdEQ ∧ SkKFar ⇒ XwGapLh`. -/
theorem xwGapLh_of_target (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) (hEQ : CdEQ S)
    (hK : R2Skel.SkEX.SkKFar S) : XwGapLh S :=
  xwGapLh_of_far hν hK (Xg.xgKReachR_of_EQ hν hU hL hEQ)

end Googology.Trans.PoR.InaccPsi.R2.Xw

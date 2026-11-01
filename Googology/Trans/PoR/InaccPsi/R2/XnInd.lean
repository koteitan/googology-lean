import Googology.Trans.PoR.InaccPsi.R2.XnLow
import Googology.Trans.PoR.InaccPsi.R2.HlU

/-!
# One induction for EQ at every window: the order is the predicted reach `r(λ)`

Notation as in `R2.XgK`: `c_n = L(n+1)`, `B_n = Bc.bcB S n`, `ρ_λ = υ_λ`, `δ_λ = υ_{λ+ω+1}`, `k_λ = Cd.cdk λ`,
`T_λ = Θ_λ(m_λ)`, `r(λ) = k_λ(T_λ)`.  EQ at `λ` (`XnEQat S n λ`): `B_n r(λ) = r(λ')` whenever `B_n ρ_λ = ρ_{λ'}`.

The leaf `Xg.XgKReachR` asks the reach move at the inner range restarts `μ` of a window `λ` (`ρ_μ` a cofinal far
index, `δ_λ·ω ≤ ρ_μ ≤ T_λ`).  Under ENUM-REACH (`CdUPPER ∧ CdLOWER`) the reach of `ρ_μ` is `r(μ)`, and

* `xnR_inner`: `r(μ) = k_λ(ρ_μ)`; so `r(μ) < r(λ)` for every inner `μ` with `ρ_μ < T_λ`, and `r(μ) = r(λ)` only for
  the one inner restart with `ρ_μ = T_λ` (the TOP of the window);
* `xnRM_of_EQ`: EQ at `μ` gives the reach move at `ρ_μ`;
* `xnEQ_step`: EQ at a long-code window `λ` from EQ at every window of smaller reach, EQ at the top restart (if
  `T_λ` is one), the reading moves `WdThLow` (now a theorem from the reading hypotheses: `Xn.xnThLow`) and
  `SkThFar`, and `Xg.XgKCof`;
* `xnEQ_all` (**the induction on `r(λ)`**): every window, given `XnTop` (EQ at the top restart, with EQ at every
  smaller reach as hypothesis);
* `xnEQ_all_wf`: the same with `XnTop` replaced by the well-foundedness of the top relation (`XnChainWF`:
  lexicographic induction on `(r(λ), chain)`);
* consequences: `XgKReachR`, `WdEQfar`, `CxEQtop`, `SkKFar`;
* non-vacuity: `CxEQtop` (the target) gives `XnTop`; codes decreasing along the top relation give `XnChainWF`;
* `xnEnum_of_front`: ENUM-REACH from the frontier hypotheses of the road (`Hl.hlU_enum` below the frontier);
* `xnCof_of_blk` / `xnCof_iff_blk`: `XgKCof` at `p` from one block of closed points of `λ'` per `Q < B_n p`.

New definitions: the statement names `XnEQat`, `XnTop`, `XnChain`, `XnChainWF`, `XnCofBlk`.  No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **EQ at `λ`** for `B_n`. -/
def XnEQat (S : InaccSeq.{0}) (n : ℕ) (l : Ordinal.{0}) : Prop :=
  ∀ l', IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → Bc.bcB S n (cdR S l) = cdR S l'

/-- The image of a range restart of `(c_n, c_{n+1})` is a range restart. -/
theorem xnRange_img {n : ℕ} {l l' : Ordinal.{0}} (hl : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (h2 : upsilon l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l') :
    CdRange S l' := by
  have hw := Cx.cxB_window (S := S) h1.le h2
  rw [hB] at hw
  have hlo : Nc.ncL S ω < upsilon l' := by
    rw [← hB, ← Cx.cxB_base (S := S) n]
    exact Bc.bcB_mono' S n (Cx.cxC_lt n) h2 h1
  have hlμ : l < l' := by
    refine Tp.tpUps_lt_iff.1 (lt_trans ?_ hlo)
    exact h2.trans (Bc.bcC_lt S (n + 1))
  exact ⟨hl', hl.2.1.trans hlμ.le, hw.2, Tp.tpCode_top hl' hlo hw.2⟩

/-- **EQ at the short codes** `m_λ ≤ ρ_λ` (no hypothesis beyond `L(ω+1) ≤ ν_C`). -/
theorem xnEQ_short (hν : Nc.ncL S (ω + 1) ≤ nuC) {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l)
    (h1 : Bc.bcC S n < upsilon l) (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l')
    (hB : Bc.bcB S n (upsilon l) = upsilon l') (hm : cdCode S l ≤ upsilon l) :
    Bc.bcB S n (cdR S l) = cdR S l' := by
  have h2 : upsilon l < Bc.bcC S (n + 1) := (Tp.tpRho_le_R l).trans_lt hr
  obtain ⟨-, hΘ⟩ := Sf.sfTheta_move hR.1.1 h1 h2 hB hm
  show Bc.bcB S n (cdk l (cdTheta S l (cdCode S l))) = cdk l' (cdTheta S l' (cdCode S l'))
  rw [hΘ]
  exact (Mv.mvKMove hν n l l' hR h1 hr hl' hB hm).symm

/-- **The reach move at `ρ_μ` from EQ at `μ`** (under ENUM-REACH). -/
theorem xnRM_of_EQ (hU : CdUPPER S) (hL : CdLOWER S) {n : ℕ} {μ : Ordinal.{0}} (hμ : CdRange S μ)
    (h1 : Bc.bcC S n < upsilon μ) (hr : cdR S μ < Bc.bcC S (n + 1)) (hE : XnEQat S n μ) :
    ∃ r, IsReach R2C (upsilon μ) r ∧ IsReach R2C (Bc.bcB S n (upsilon μ)) (Bc.bcB S n r) := by
  have h2 : upsilon μ < Bc.bcC S (n + 1) := (Tp.tpRho_le_R μ).trans_lt hr
  obtain ⟨μ', hμ', e⟩ := Sf.sfRstMove (S := S) n μ hμ.1 h1.le h2
  have hR' := xnRange_img hμ h1 h2 hμ' e
  refine ⟨cdR S μ, cdEnum_exact hU hL hμ, ?_⟩
  rw [e, hE μ' hμ' e]
  exact cdEnum_exact hU hL hR'

/-- **The inner restarts**: at a cofinal far index `ρ_μ ≤ T_λ` of a window, `μ` a range restart, `r(μ) = k_λ(ρ_μ)`
(under ENUM-REACH at `μ`). -/
theorem xnR_inner (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) {n : ℕ}
    {l l' μ : Ordinal.{0}} (hW : R2Skel.SkEX.SkWin S n l l') (hμ : CdRange S μ)
    (hfar : cdDelta l * ω ≤ upsilon μ) (hp : upsilon μ ≤ cdTheta S l (cdCode S l))
    (hcof : ∀ q < upsilon μ, cdk l q < upsilon μ) : cdR S μ = cdk l (upsilon μ) := by
  obtain ⟨hkC, -, hδp, hρp, -, -, -⟩ := Xg.xgWin_facts hν hW hfar hp
  have hr := cdEnum_exact hU hL hμ
  have hkΩ : cdk l (upsilon μ) < Om1 := (hkC.trans (Bc.bcC_lt S (n + 1))).trans (Xg.xgL_lt_Om1 hν)
  have hle : cdk l (upsilon μ) ≤ cdR S μ :=
    enumOrd_le_of_forall_lt
      (Xg.xgReach_mem hδp hcof (((cdk_strictMono l).id_le _).trans_lt hkΩ) hr)
      fun b hb => (hcof b hb).trans_le (le1_le hr.1)
  refine (le_antisymm hle (not_lt.1 fun hlt => ?_)).symm
  exact absurd ((cdk_closed hkΩ).2 _ hρp ((cdk_strictMono l).id_le _) _ hr.1) (not_le.2 hlt)

/-- **Inner restarts below the top have smaller reach**: `ρ_μ < T_λ ⇒ r(μ) < r(λ)`. -/
theorem xnR_inner_lt (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) {n : ℕ}
    {l l' μ : Ordinal.{0}} (hW : R2Skel.SkEX.SkWin S n l l') (hμ : CdRange S μ)
    (hfar : cdDelta l * ω ≤ upsilon μ) (hp : upsilon μ < cdTheta S l (cdCode S l))
    (hcof : ∀ q < upsilon μ, cdk l q < upsilon μ) : cdR S μ < cdR S l := by
  rw [xnR_inner hν hU hL hW hμ hfar hp.le hcof]
  exact (cdk_strictMono l) hp

/-- **The top restart has the same reach**: `ρ_μ = T_λ ⇒ r(μ) = r(λ)`. -/
theorem xnR_inner_top (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) {n : ℕ}
    {l l' μ : Ordinal.{0}} (hW : R2Skel.SkEX.SkWin S n l l') (hμ : CdRange S μ)
    (hfar : cdDelta l * ω ≤ upsilon μ) (he : upsilon μ = cdTheta S l (cdCode S l))
    (hcof : ∀ q < upsilon μ, cdk l q < upsilon μ) : cdR S μ = cdR S l := by
  rw [xnR_inner hν hU hL hW hμ hfar he.le hcof, he]
  rfl

/-- The reach move at a cofinal far `υ`-point that is not a range restart (`Wa.waTCtopOff`). -/
theorem xnRM_nonRange (hν : Nc.ncL S (ω + 1) ≤ nuC) {n : ℕ} {l l' p : Ordinal.{0}}
    (hW : R2Skel.SkEX.SkWin S n l l') (hfar : cdDelta l * ω ≤ p) (hp : p ≤ cdTheta S l (cdCode S l))
    (hnr : ∀ μ, CdRange S μ → p ≠ upsilon μ) :
    ∃ r, IsReach R2C p r ∧ IsReach R2C (Bc.bcB S n p) (Bc.bcB S n r) := by
  obtain ⟨hkC, hpC, -, hρp, hcn, -, -⟩ := Xg.xgWin_facts hν hW hfar hp
  rcases Wa.waTCtopOff hν n p hcn hpC hnr with ⟨r, -, h1, h2⟩ | hright
  · exact ⟨r, h1, h2⟩
  · exfalso
    have hkΩ : cdk l p < Om1 := (hkC.trans (Bc.bcC_lt S (n + 1))).trans (Xg.xgL_lt_Om1 hν)
    have hpk : p ≤ cdk l p := (cdk_strictMono l).id_le p
    have h := (hright (cdk l p + 1) (hpk.trans le_self_add) (Xg.xgC_succ_lt n hkC)).1
    have hle := (cdk_closed hkΩ).2 p hρp hpk _ h
    exact absurd hle (not_le.2 (lt_add_one _))

/-- **The far `k`-move up to an index `P ≤ T_λ`, with the reach move asked only at the cofinal far `υ`-points
`p ≤ P`** (the local form of `Xg.xgKFar_of`). -/
theorem xnKFar_upto (hν : Nc.ncL S (ω + 1) ≤ nuC) (hC : Xg.XgKCof S) {n : ℕ} {l l' : Ordinal.{0}}
    (hW : R2Skel.SkEX.SkWin S n l l') {P : Ordinal.{0}} (hP : P ≤ cdTheta S l (cdCode S l))
    (hRe : ∀ p, cdDelta l * ω ≤ p → p ≤ P → (∀ q < p, cdk l q < p) → UpsPt p →
      ∃ r, IsReach R2C p r ∧ IsReach R2C (Bc.bcB S n p) (Bc.bcB S n r)) :
    ∀ p ≤ P, cdk l' (Bc.bcB S n p) = Bc.bcB S n (cdk l p) := by
  have hW0 := hW
  obtain ⟨hR, h1, hr, hl', hB, -⟩ := hW
  set T := cdTheta S l (cdCode S l) with hT
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have hkC : ∀ p ≤ T, cdk l p < Bc.bcC S (n + 1) := fun p hp =>
    ((cdk_strictMono l).monotone hp).trans_lt hr
  have hkL : ∀ p ≤ T, cdk l p < Nc.ncL S ω := fun p hp => (hkC p hp).trans (Bc.bcC_lt S (n + 1))
  have hpL : ∀ p ≤ T, p < Nc.ncL S ω := fun p hp => ((cdk_strictMono l).id_le p).trans_lt (hkL p hp)
  have hLP : IsPrincipal (· + ·) (Nc.ncL S ω) := (indec_iff.1 (Wd.wdL_indec S)).2
  intro p
  induction p using WellFoundedLT.induction with
  | ind p IH =>
  intro hpP
  have hp : p ≤ T := hpP.trans hP
  by_cases hlow : p < cdDelta l * ω
  · exact Wd.wdk_move hν hR.1 hl' h1 hδr hB hlow
  have hfar : cdDelta l * ω ≤ p := not_lt.1 hlow
  by_cases hA : ∃ q < p, cdk l p < cdk l q * ω
  · obtain ⟨q, hqp, hpq⟩ := hA
    have hqT : q ≤ T := hqp.le.trans hp
    have hle : cdk l q ≤ cdk l p := (cdk_strictMono l).monotone hqp.le
    obtain ⟨Z, hZ⟩ := exists_add_of_le hle
    have hZw : Z < cdk l q * ω := lt_of_le_of_lt le_add_self (hZ ▸ hpq)
    have hpe : p = q + Z := (cdk_inj l).1 (hZ.trans (Xg.xgk_add hZw).symm)
    have hZL : Z < Nc.ncL S ω := lt_of_le_of_lt le_add_self (hZ ▸ hkL p hp)
    have IHq := IH q hqp (hqp.le.trans hpP)
    have hpos : 0 < Bc.bcB S n (cdk l q) := by rw [← IHq]; exact Xg.xgK_pos (cdk_mem l' _)
    have hBZ : Bc.bcB S n Z < cdk l' (Bc.bcB S n q) * ω := by
      obtain ⟨m, hm'⟩ := Wd.wd_lt_mul_nat (Xg.xgK_pos (cdk_mem l q)).ne' hZw
      have hmL : cdk l q * ((m + 1 : ℕ) : Ordinal.{0}) < Nc.ncL S ω :=
        Xg.xg_mul_nat_lt hLP (hkL q hqT) _
      rw [IHq]
      calc Bc.bcB S n Z < Bc.bcB S n (cdk l q * ((m + 1 : ℕ) : Ordinal.{0})) :=
            (Bc.bcB_lt_iff hZL hmL).2 hm'
        _ = Bc.bcB S n (cdk l q) * ((m + 1 : ℕ) : Ordinal.{0}) := Wd.wdB_mul (hkL q hqT) _ hmL
        _ < Bc.bcB S n (cdk l q) * ω := Xg.xg_lt_mulw hpos _
    calc cdk l' (Bc.bcB S n p) = cdk l' (Bc.bcB S n q + Bc.bcB S n Z) := by
          rw [hpe, Bc.bcB_add (hpL q hqT) hZL]
      _ = cdk l' (Bc.bcB S n q) + Bc.bcB S n Z := Xg.xgk_add hBZ
      _ = Bc.bcB S n (cdk l q) + Bc.bcB S n Z := by rw [IHq]
      _ = Bc.bcB S n (cdk l q + Z) := (Bc.bcB_add (hkL q hqT) hZL).symm
      _ = Bc.bcB S n (cdk l p) := by rw [← hZ]
  · push Not at hA
    have hcof : ∀ q < p, cdk l q < p := by
      intro q hqp
      have hq0 := Xg.xgK_pos (cdk_mem l q)
      have h2 : cdk l q * ((2 : ℕ) : Ordinal.{0}) < cdk l q * ω := Xg.xg_lt_mulw hq0 2
      have h2' : cdk l q + cdk l q < cdk l q * ω := by
        have e2 : cdk l q * ((2 : ℕ) : Ordinal.{0}) = cdk l q + cdk l q := by
          rw [show ((2 : ℕ) : Ordinal.{0}) = 1 + 1 by norm_num, mul_add, mul_one]
        rw [e2] at h2; exact h2
      have hlt : cdk l q < cdk l q * ω := (lt_add_of_pos_right _ hq0).trans h2'
      have e := Xg.xgk_add hlt
      have h3 : cdk l (q + cdk l q) < cdk l p := by rw [e]; exact h2'.trans_le (hA q hqp)
      exact le_add_self.trans_lt ((cdk_strictMono l).lt_iff_lt.1 h3)
    obtain ⟨-, hpC, hδp, hρp, hcn, hBδ, hBρ⟩ := Xg.xgWin_facts hν hW0 hfar hp
    have hkΩ : cdk l p < Om1 := (hkL p hp).trans (Xg.xgL_lt_Om1 hν)
    have hIH : ∀ q < p, cdk l' (Bc.bcB S n q) = Bc.bcB S n (cdk l q) := fun q hq =>
      IH q hq (hq.le.trans hpP)
    have hcof' := hC n l l' hW0 p hfar hp hcof hIH
    obtain ⟨r, hr1, hr2⟩ : ∃ r, IsReach R2C p r ∧ IsReach R2C (Bc.bcB S n p) (Bc.bcB S n r) := by
      by_cases hU : UpsPt p
      · exact hRe p hfar hpP hcof hU
      · exact Xg.xgReach_nonUps hν hcn hpC hU
    have hle : cdk l p ≤ r :=
      enumOrd_le_of_forall_lt (Xg.xgReach_mem hδp hcof ((cdk_strictMono l).id_le p |>.trans_lt hkΩ) hr1)
        fun b hb => (hcof b hb).trans_le (le1_le hr1.1)
    have hk : cdk l p = r := by
      refine le_antisymm hle (not_lt.1 fun hlt => ?_)
      have hcl : cdClosed l (cdk l p) := cdk_closed hkΩ
      exact absurd (hcl.2 p hρp ((cdk_strictMono l).id_le p) r hr1.1) (not_le.2 hlt)
    have hrC : r < Bc.bcC S (n + 1) := hk ▸ hkC p hp
    have hBrΩ : Bc.bcB S n r < Om1 :=
      ((Bc.bcB_bound' S n r hrC).trans_le hν).trans_le nuC_le_Om1
    rw [hk, Xg.xgk_reach hBδ hBρ hcof' hr2 hBrΩ]

/-- **The induction step**: EQ at a long-code window `λ` from EQ at every window of smaller reach (`IH`), EQ at
the top restart (`htop`), the reading moves and `XgKCof`. -/
theorem xnEQ_step (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) (hTL : Wd.WdThLow S)
    (hTF : R2Skel.SkEX.SkThFar S) (hC : Xg.XgKCof S) {n : ℕ} {l l' : Ordinal.{0}}
    (hW : R2Skel.SkEX.SkWin S n l l')
    (IH : ∀ μ, CdRange S μ → Bc.bcC S n < upsilon μ → cdR S μ < cdR S l → XnEQat S n μ)
    (htop : ∀ μ, CdRange S μ → upsilon μ = cdTheta S l (cdCode S l) → cdDelta l * ω ≤ upsilon μ →
      (∀ q < upsilon μ, cdk l q < upsilon μ) → XnEQat S n μ) :
    Bc.bcB S n (cdR S l) = cdR S l' := by
  have hW0 := hW
  obtain ⟨hR, h1, hr, hl', hB, hm⟩ := hW
  by_cases hw : cdTheta S l (cdCode S l) < cdDelta l * ω
  · have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
    have hΘ := hTL n l l' hR h1 hr hl' hB hm hw
    show Bc.bcB S n (cdk l (cdTheta S l (cdCode S l))) = cdk l' (cdTheta S l' (cdCode S l'))
    rw [← hΘ, Wd.wdk_move hν hR.1 hl' h1 hδr hB hw]
  · push Not at hw
    have hRe : ∀ p, cdDelta l * ω ≤ p → p ≤ cdTheta S l (cdCode S l) → (∀ q < p, cdk l q < p) →
        UpsPt p → ∃ r, IsReach R2C p r ∧ IsReach R2C (Bc.bcB S n p) (Bc.bcB S n r) := by
      intro p hfar hp hcof _
      by_cases hr' : ∃ μ, CdRange S μ ∧ p = upsilon μ
      · obtain ⟨μ, hμ, rfl⟩ := hr'
        obtain ⟨hkC, -, -, -, hcn, -, -⟩ := Xg.xgWin_facts hν hW0 hfar hp
        have hRμ := xnR_inner hν hU hL hW0 hμ hfar hp hcof
        have hrμ : cdR S μ < Bc.bcC S (n + 1) := hRμ ▸ hkC
        have hE : XnEQat S n μ := by
          rcases hp.lt_or_eq with hlt | heq
          · exact IH μ hμ hcn (xnR_inner_lt hν hU hL hW0 hμ hfar hlt hcof)
          · exact htop μ hμ heq hfar hcof
        exact xnRM_of_EQ hU hL hμ hcn hrμ hE
      · push Not at hr'
        exact xnRM_nonRange hν hW0 hfar hp fun μ hμ e => hr' μ hμ e
    have hK := xnKFar_upto hν hC hW0 le_rfl hRe _ le_rfl
    show Bc.bcB S n (cdk l (cdTheta S l (cdCode S l))) = cdk l' (cdTheta S l' (cdCode S l'))
    rw [← hTF n l l' hW0 hw, hK]

/-- **Leaf (the top restart)**: at a long-code window `λ` whose top `T_λ` is a cofinal far range restart `ρ_μ`,
EQ at `μ`, given EQ at every window of smaller reach.  (`r(μ) = r(λ)`, `xnR_inner_top`.) -/
def XnTop (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l, CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) → upsilon l < cdCode S l →
    (∀ ν, CdRange S ν → Bc.bcC S n < upsilon ν → cdR S ν < cdR S l → XnEQat S n ν) →
    ∀ μ, CdRange S μ → upsilon μ = cdTheta S l (cdCode S l) → cdDelta l * ω ≤ upsilon μ →
      (∀ q < upsilon μ, cdk l q < upsilon μ) → XnEQat S n μ

/-- **THE INDUCTION ON `r(λ)`**: EQ at every range restart of every `(c_n, c_{n+1})` whose predicted reach is
below `c_{n+1}`, from ENUM-REACH, the reading moves, `XgKCof` and the top leaf `XnTop`. -/
theorem xnEQ_all (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) (hTL : Wd.WdThLow S)
    (hTF : R2Skel.SkEX.SkThFar S) (hC : Xg.XgKCof S) (hTop : XnTop S) :
    ∀ n : ℕ, ∀ l, CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) → XnEQat S n l := by
  intro n
  suffices H : ∀ R, ∀ l, cdR S l = R → CdRange S l → Bc.bcC S n < upsilon l →
      cdR S l < Bc.bcC S (n + 1) → XnEQat S n l from fun l hR h1 hr => H _ l rfl hR h1 hr
  intro R
  induction R using WellFoundedLT.induction with
  | ind R IHR =>
  intro l hlR hR h1 hr
  have IH : ∀ ν, CdRange S ν → Bc.bcC S n < upsilon ν → cdR S ν < cdR S l → XnEQat S n ν :=
    fun ν hν1 hν2 hlt => IHR _ (hlR ▸ hlt) ν rfl hν1 hν2 (hlt.trans hr)
  intro l' hl' hB
  by_cases hm : cdCode S l ≤ upsilon l
  · exact xnEQ_short hν hR h1 hr hl' hB hm
  · exact xnEQ_step hν hU hL hTL hTF hC ⟨hR, h1, hr, hl', hB, not_le.1 hm⟩ IH
      (hTop n l hR h1 hr (not_le.1 hm) IH)

/-- **The top relation** `μ ◁ λ`: `λ` a long-code range restart of `(c_n, c_{n+1})` with `r(λ) < c_{n+1}`, and `ρ_μ`
(a range restart) is its top `T_λ`, a cofinal far index. -/
def XnChain (S : InaccSeq.{0}) (n : ℕ) (μ l : Ordinal.{0}) : Prop :=
  CdRange S l ∧ Bc.bcC S n < upsilon l ∧ cdR S l < Bc.bcC S (n + 1) ∧ upsilon l < cdCode S l ∧
    CdRange S μ ∧ upsilon μ = cdTheta S l (cdCode S l) ∧ cdDelta l * ω ≤ upsilon μ ∧
    (∀ q < upsilon μ, cdk l q < upsilon μ)

/-- **Leaf (well-founded top relation)**. -/
def XnChainWF (S : InaccSeq.{0}) : Prop := ∀ n : ℕ, WellFounded (XnChain S n)

/-- One reach class: EQ at every window of reach `R`, from EQ at every smaller reach, by induction on `◁`. -/
theorem xnEQ_class (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) (hTL : Wd.WdThLow S)
    (hTF : R2Skel.SkEX.SkThFar S) (hC : Xg.XgKCof S) {n : ℕ} (hWF : WellFounded (XnChain S n))
    {R : Ordinal.{0}}
    (IHR : ∀ ν, CdRange S ν → Bc.bcC S n < upsilon ν → cdR S ν < R → cdR S ν < Bc.bcC S (n + 1) →
      XnEQat S n ν) :
    ∀ l, CdRange S l → Bc.bcC S n < upsilon l → cdR S l = R → cdR S l < Bc.bcC S (n + 1) →
      XnEQat S n l := by
  intro l0
  refine hWF.induction (C := fun l => CdRange S l → Bc.bcC S n < upsilon l → cdR S l = R →
      cdR S l < Bc.bcC S (n + 1) → XnEQat S n l) l0 ?_
  intro l IHc hR h1 hlR hr l' hl' hB
  by_cases hm : cdCode S l ≤ upsilon l
  · exact xnEQ_short hν hR h1 hr hl' hB hm
  · have hW : R2Skel.SkEX.SkWin S n l l' := ⟨hR, h1, hr, hl', hB, not_le.1 hm⟩
    refine xnEQ_step hν hU hL hTL hTF hC hW
      (fun ν hν1 hν2 hlt => IHR ν hν1 hν2 (hlR ▸ hlt) (hlt.trans hr)) ?_
    intro μ hμ he hfar hcof
    obtain ⟨-, -, -, -, hcn, -, -⟩ := Xg.xgWin_facts hν hW hfar he.le
    have hRe : cdR S μ = cdR S l := xnR_inner_top hν hU hL hW hμ hfar he hcof
    exact IHc μ ⟨hR, h1, hr, not_le.1 hm, hμ, he, hfar, hcof⟩ hμ hcn (hRe.trans hlR) (hRe ▸ hr)

/-- **THE LEXICOGRAPHIC INDUCTION on `(r(λ), ◁)`**: EQ everywhere with `XnTop` replaced by `XnChainWF`. -/
theorem xnEQ_all_wf (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) (hTL : Wd.WdThLow S)
    (hTF : R2Skel.SkEX.SkThFar S) (hC : Xg.XgKCof S) (hWF : XnChainWF S) :
    ∀ n : ℕ, ∀ l, CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) → XnEQat S n l := by
  intro n
  suffices H : ∀ R, ∀ l, CdRange S l → Bc.bcC S n < upsilon l → cdR S l = R →
      cdR S l < Bc.bcC S (n + 1) → XnEQat S n l from fun l hR h1 hr => H _ l hR h1 rfl hr
  intro R
  induction R using WellFoundedLT.induction with
  | ind R IHR =>
  exact xnEQ_class hν hU hL hTL hTF hC (hWF n) fun ν h1 h2 hlt hrc => IHR _ hlt ν h1 h2 rfl hrc

/-! ## Consequences -/

/-- EQ everywhere gives `CxEQtop`. -/
theorem xnEQtop_of (H : ∀ n : ℕ, ∀ l, CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    XnEQat S n l) : Cx.CxEQtop S := by
  intro n l hl h1 hr
  have h2 : upsilon l < Bc.bcC S (n + 1) := (Tp.tpRho_le_R l).trans_lt hr
  obtain ⟨μ', hμ', e⟩ := Sf.sfRstMove (S := S) n l hl.1 h1.le h2
  exact ⟨μ', xnRange_img hl h1 h2 hμ' e, e, H n l hl h1 hr μ' hμ' e⟩

/-- `CxEQtop` gives EQ everywhere (so `XnTop` and the conclusion of `xnEQ_all` follow from the target). -/
theorem xnEQat_of_top (h : Cx.CxEQtop S) :
    ∀ n : ℕ, ∀ l, CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) → XnEQat S n l := by
  intro n l hl h1 hr l' _ hB
  obtain ⟨l'', -, e1, e2⟩ := h n l hl h1 hr
  have : l'' = l' := Tp.tpUps_inj (e1.symm.trans hB)
  subst this
  exact e2

/-- **NON-VACUITY of `XnTop`**: it follows from `CxEQtop` (and so from `CdEQ`, `Wa.waEQtop_of_EQ`) under ENUM-REACH. -/
theorem xnTop_of_EQtop (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S)
    (h : Cx.CxEQtop S) : XnTop S := by
  intro n l hR h1 hr hm _ μ hμ he hfar hcof
  have h2 : upsilon l < Bc.bcC S (n + 1) := (Tp.tpRho_le_R l).trans_lt hr
  obtain ⟨l', hl', e⟩ := Sf.sfRstMove (S := S) n l hR.1 h1.le h2
  have hW : R2Skel.SkEX.SkWin S n l l' := ⟨hR, h1, hr, hl', e, hm⟩
  obtain ⟨-, -, -, -, hcn, -, -⟩ := Xg.xgWin_facts hν hW hfar he.le
  have hrμ : cdR S μ < Bc.bcC S (n + 1) := (xnR_inner_top hν hU hL hW hμ hfar he hcof) ▸ hr
  exact xnEQat_of_top h n μ hμ hcn hrμ

end Googology.Trans.PoR.InaccPsi.R2.Xn

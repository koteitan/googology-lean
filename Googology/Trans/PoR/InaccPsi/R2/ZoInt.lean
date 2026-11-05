import Googology.Trans.PoR.InaccPsi.R2.ZhFix
import Googology.Trans.PoR.InaccPsi.R2.YxVac
import Googology.Trans.PoR.InaccPsi.R2.RcLow
import Googology.Trans.PoR.InaccPsi.R2.CpName

/-!
# Zo: the relative block induction on any interval BELOW `L(0)` (no CAP-0)

The window theorems (`Zh.zhWins6`) run the relative block induction on `[ι(L(k)), ι(L(k+1)))` and use CAP-0 (the
caps at EVERY restart below `L(0)`) to place the base and the counterexample below `ν_C`.  Below `L(0)` CAP-0
is part of the goal, so it cannot be used there.  Here the same induction runs on any interval `[l₀, B)` with
`υ_B ≤ m* = L(0)`, with the caps asked only below the current height:

* `zoNu_gt0` (**strict NU-LOW″ below `m*`**): if every restart `λ ≥ B₀` with `ρ_λ < X` is capped and `X ≤ m*`,
  then `X < ν_C` (the argument of `Yx.yxNu_gt`, whose witnesses all lie below `ν_C ≤ X`);
* `zoRange_lt`: every restart `λ ≥ B₀` with `ρ_λ < m*` is a range restart (`Cd.cdRange_level1`);
* `zoSpec_caps0`: `Zh.zhSpec_capsV` with CAP-0 replaced by the caps below `ρ_{l₀}` (least counterexample);
* `zoReach0_ref` (REFUTE FIRST): the base datum with chain start `0` fails at a short-reach range restart
  (`δ < r < top₁`) under UPPER ∧ LOWER, so the base enters with its own given input `zoGiven_of`;
* `zoInt` (**THE INTERVAL THEOREM**): the given input at `l₀`, the pair-free inputs `Zc.ZcInR S l₀ B`, CapV at the
  `υ`-fixed long-exponent range restarts and the RS input at the `υ`-fixed restarts of `(l₀, B)`, the caps
  below `ρ_{l₀}` and LOWER at the range restarts `≤ l₀` give `υ_B ≤ ν_C` and UPPER ∧ LOWER ∧ CapV at every
  range restart of `(l₀, B)`;
* `zoInt_of_target` (**NON-VACUITY**): the inputs of `zoInt` follow from UPPER, LOWER, CapV at the range
  restarts of `(l₀, B)` and the chain reach data there and at `l₀`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Zo

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **Strict NU-LOW″ below `m*`**: the caps at the restarts `λ ≥ B₀` with `ρ_λ < X ≤ m*` give `X < ν_C`. -/
theorem zoNu_gt0 {X : Ordinal.{0}} (hX : X ≤ cdMstar S)
    (h : ∀ l, IsRestartIdx l → cdB0 ≤ l → upsilon l < X → CdCapAt S l) : X < nuC := by
  by_contra hlt
  have hνL : nuC ≤ X := not_lt.1 hlt
  obtain ⟨l, hl, -, hlν, -, -, -, hP, hW, -⟩ := Lb.lbFirst
  have hLeq : Nc.ncL S ω = Pv S (Om ω + Nc.ncPp S * ω) := Lw.lw_L_eq S ω
  have hlT : upsilon l < Pv S (Om ω + Nc.ncPp S * ω) :=
    hLeq ▸ (hlν.trans_le (hνL.trans (hX.trans (cdMstar_le_L S ω))))
  have hl1 : 1 ≤ l := Order.one_le_iff_ne_zero.2 hl.1
  obtain ⟨ηt, -, hηt⟩ := iota_onto (S := S) _ l hl1 (cd_lt_iota hlT).le
  have hne : {η | iota S η = l}.Nonempty := ⟨ηt, hηt⟩
  have hηm : iota S (sInf {η | iota S η = l}) = l := csInf_mem hne
  have hmin : ∀ η < sInf {η | iota S η = l}, iota S η ≠ l := fun η h he =>
    (csInf_le' (s := {η | iota S η = l}) he).not_gt h
  generalize sInf {η | iota S η = l} = ηm at hηm hmin
  have hpvm : Pv S ηm = upsilon l := by
    calc Pv S ηm = upsilon (iota S ηm) := (ups_iota S ηm).symm
      _ = upsilon l := by rw [hηm]
  have hηm0 : ηm ≠ 0 := by
    rintro rfl
    rw [iota_zero] at hηm
    exact (ri_lim hl).succ_ne 0 (by rw [succ_eq_add_one, zero_add]; exact hηm)
  obtain ⟨η0, hdec, hdvd⟩ := cdExp_decomp hηm0
  generalize cdExp ηm = e at hdec hdvd
  have hη0m : η0 < ηm := by
    rw [hdec]; exact lt_add_of_pos_right _ (opow_pos _ omega0_pos)
  have hν : iota S η0 < l := lt_of_le_of_ne ((iota_mono (S := S) ηm η0 hη0m.le).trans_eq hηm) (hmin η0 hη0m)
  obtain ⟨y, hνy, hyl, hy⟩ := hP (upsilon (iota S η0)) (upsilon_normal.strictMono hν)
  obtain ⟨μ, hμ, hBμ, rfl, -⟩ := hW y hyl hy
  have hμν : iota S η0 < μ := upsilon_normal.strictMono.lt_iff_lt.1 hνy
  have hμl : μ < l := upsilon_normal.strictMono.lt_iff_lt.1 hyl
  obtain ⟨-, hιμ, -⟩ := cdEta_spec (S := S) (Order.one_le_iff_ne_zero.2 hμ.1) (hμl.trans_eq hηm.symm)
  have hx0 : η0 < cdEta S μ := by
    by_contra h'
    push Not at h'
    have h'' := iota_mono (S := S) η0 _ h'
    rw [hιμ] at h''
    exact absurd h'' (not_le.2 hμν)
  have hxm : cdEta S μ < η0 + ω ^ e := by
    rw [← hdec]
    by_contra h'
    push Not at h'
    have h'' := iota_mono (S := S) (cdEta S μ) ηm h'
    rw [hιμ, hηm] at h''
    exact absurd h'' (not_le.2 hμl)
  obtain ⟨-, hxw⟩ := cdWin hdvd hx0 hxm
  have hμX : upsilon μ < X := (upsilon_normal.strictMono hμl).trans (hlν.trans_le hνL)
  have hcapl : cdCapB S μ ≤ upsilon l := by
    unfold cdCapB
    calc Pv S (cdEta S μ + ω ^ cdExp (cdEta S μ)) ≤ Pv S ηm := Pv_mono (hxw.le.trans_eq hdec.symm)
      _ = upsilon l := hpvm
  exact absurd (((h μ hμ hBμ hμX) nuC hy).trans_le hcapl) (not_lt.2 hlν.le)

/-- **Every restart `λ ≥ B₀` below `m*` is a range restart.** -/
theorem zoRange_lt {l : Ordinal.{0}} (hl : IsRestartIdx l) (hB : cdB0 ≤ l) (hlev : upsilon l < cdMstar S) :
    CdRange S l := cdRange_level1 hl hB hlev

/-- **The pair fields from the caps below `ρ_{l₀}` (least counterexample) on an interval below `m*`.** -/
theorem zoSpec_caps0 {O : Ordinal.{0} → Ordinal.{0}} {l0 B : Ordinal.{0}} (Sp : Yx.YxSpec O l0 B)
    (hX : upsilon B ≤ cdMstar S)
    (hb : ∀ μ, CdRange S μ → upsilon μ < upsilon l0 → CdCapAt S μ) (hl0 : CdRange S l0 → CdCapAt S l0)
    (hO : ∀ μ, l0 < μ → O μ = Ys.ysO S μ)
    (hV : ∀ μ, CdRange S μ → upsilon l0 < upsilon μ → upsilon μ < upsilon B → upsilon μ < nuC →
      CdCapV S μ) :
    upsilon B ≤ nuC ∧ Ys.YsSpec O l0 B := by
  have hm := upsilon_normal.strictMono
  have hρB : upsilon l0 < upsilon B := hm Sp.lt
  have hρ0 : upsilon l0 < nuC :=
    zoNu_gt0 (hρB.le.trans hX) fun μ hμ hB h => hb μ (zoRange_lt hμ hB (h.trans (hρB.trans_le hX))) h
  suffices hν : upsilon B ≤ nuC from ⟨hν, Sp.toYs hν⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨ξ, hξ, he⟩ := nuC_restart
  have i0 : l0 < ξ := hm.lt_iff_lt.1 (he ▸ hρ0)
  have i1 : ξ < B := hm.lt_iff_lt.1 (he ▸ hlt)
  have Sp' : Ys.YsSpec O l0 ξ := (Sp.restr hξ i0 i1.le).toYs he.symm.le
  have hνX : nuC ≤ cdMstar S := hlt.le.trans hX
  refine absurd (zoNu_gt0 hνX ?_) (lt_irrefl _)
  intro μ hμ hB hlX
  have hr : CdRange S μ := zoRange_lt hμ hB (hlX.trans_le hνX)
  rcases lt_trichotomy (upsilon μ) (upsilon l0) with h | h | h
  · exact hb μ hr h
  · exact hm.injective h ▸ hl0 (hm.injective h ▸ hr)
  · have j0 : l0 < μ := hm.lt_iff_lt.1 h
    have j1 : μ < ξ := hm.lt_iff_lt.1 (he ▸ hlX)
    have hU : CdUpper S μ := Ys.ysUpper_all Sp' hμ j0.le j1 (by rw [hO μ j0]; exact Ys.ysO_eq S μ)
    exact cdCapAt_of_upper hU (hV μ hr h (hlX.trans hlt) hlX)

/-- **REFUTE FIRST for the base datum with chain start `0`** (the base of `Yx.yxSpec_ofIn`): at a restart with
UPPER and LOWER whose reach lies strictly inside the first chain block (`δ_λ < r(λ) < top₁`), the datum
`Ys.YsReachIn λ 0 ρ_λ` is FALSE.  So a base that is a range restart must enter with its own given input
(chain start `o ≤ r(λ) − δ_λ`), not with `o = 0`. -/
theorem zoReach0_ref {l : Ordinal.{0}} (hU : CdUpper S l) (hL : CdLower S l)
    (h1 : upsilon (l + ω + 1) < cdR S l)
    (h2 : cdR S l < topA (l + ω) (upsilon (l + ω + 1) + 0) 1) : ¬ Ys.YsReachIn l 0 (upsilon l) := by
  intro h
  have hρδ : upsilon l ≤ upsilon (l + ω + 1) :=
    upsilon_normal.strictMono.monotone (le_self_add.trans le_self_add)
  have h0 : topA (l + ω) (upsilon (l + ω + 1) + 0) 0 = upsilon (l + ω + 1) := by
    simp [topA]
  have hc := h 0 (upsilon l) le_rfl (by rw [h0]; exact hρδ) (cdR S l) (by rw [h0]; exact h1) h2 hL
  exact hU (le1_of_le_of_le1 ((cdRho_lt_R S l).le.trans le_self_add) (Order.add_one_le_of_lt h2) hc)

/-- **The given input at a base from UPPER and a reach datum with chain start `o ≤ r − δ`.** -/
theorem zoGiven_of {l o : Ordinal.{0}} (hU : CdUpper S l) (ho1 : o < upsilon (l + ω + 1))
    (ho2 : o ≤ Ys.ysO S l) (hR : Ys.YsReachIn l o (upsilon l)) : Yx.YxGivenIn (Ys.ysO S) l :=
  ⟨o, ho1, ho2, (Ys.ysTopR_iff (S := S) (cdR_ge S l)).2 hU, hR⟩

/-- **THE INTERVAL THEOREM below `m*`.**  On `[l₀, B)` with `υ_B ≤ m*`: the given input at the base `l₀`
(bound `r − δ`), the pair-free inputs at the restarts of `(l₀, B)`, CapV at the `υ`-fixed long-exponent range
restarts and the RS input at the `υ`-fixed restarts of `(l₀, B)`, the caps at the range restarts below
`ρ_{l₀}`, LOWER at the range restarts below `l₀`, and (if `l₀` is a range restart) its cap and LOWER give
`υ_B ≤ ν_C` and UPPER ∧ LOWER ∧ CapV at every range restart of `(l₀, B)`. -/
theorem zoInt {l0 B : Ordinal.{0}} (hl0 : IsRestartIdx l0) (hB : IsRestartIdx B) (hlt : l0 < B)
    (hBm : upsilon B ≤ cdMstar S)
    (hcap : ∀ μ, CdRange S μ → upsilon μ < upsilon l0 → CdCapAt S μ)
    (hLlow : ∀ μ, CdRange S μ → μ < l0 → CdLower S μ)
    (hbase0 : CdRange S l0 → CdCapAt S l0 ∧ CdLower S l0)
    (hgiven : Yx.YxGivenIn (Ys.ysO S) l0)
    (hin : Zc.ZcInR S l0 B)
    (hVF : ∀ μ, CdRange S μ → l0 < μ → μ < B → upsilon μ = μ → upsilon μ < nuC → ¬ Zh.ZhShortExp S μ →
      CdCapV S μ)
    (hrsF : ∀ l, IsRestartIdx l → l0 < l → l < B → upsilon l = l →
      Zc.ZcRsIn (Ys.ysO S) l ∨ Zh.ZhSupInB S l B) :
    upsilon B ≤ nuC ∧ ∀ μ, CdRange S μ → l0 < μ → μ < B → CdUpper S μ ∧ CdLower S μ ∧ CdCapV S μ := by
  have hm := upsilon_normal.strictMono
  have hρB : upsilon l0 < upsilon B := hm hlt
  have hBP : upsilon B ≤ Pv S (Om ω) := hBm
  have hB1 : B < Om1 :=
    hm.le_apply.trans_lt (hBm.trans_lt (by rw [Br.Om1_eq]; exact Nm.Pv_lt_Om1 S _))
  -- the base below `ν_C`
  have hρ0 : upsilon l0 < nuC :=
    zoNu_gt0 (hρB.le.trans hBm) fun μ hμ hB' h => hcap μ (zoRange_lt hμ hB' (h.trans (hρB.trans_le hBm))) h
  have Sp : Yx.YxSpec (Ys.ysO S) l0 B := by
    refine ⟨hl0, (ri_iff.1 hB).2, hB1, hlt, land_C hl0 hρ0.le, fun l hl h0 h1 => ?_⟩
    rcases h0.lt_or_eq with h0 | rfl
    · exact hin l hl h0 h1
    · exact Or.inr hgiven
  -- CapV below `ν_C` on the interval
  have hVL : ∀ μ, CdRange S μ → l0 < μ → μ < B → upsilon μ < nuC → ¬ Zh.ZhShortExp S μ → CdCapV S μ := by
    intro μ hr h0 h1 hμν hns
    rcases eq_or_lt_of_le hm.le_apply with he | hfix
    · exact hVF μ hr h0 h1 he.symm hμν hns
    · exfalso
      exact hns (Zh.zh_short_of_nonfix hr.1 (Zh.zh_ww_lt hl0 h0) hfix ((hm h1).trans_le hBP))
  have hVν : ∀ μ, CdRange S μ → upsilon l0 < upsilon μ → upsilon μ < upsilon B → upsilon μ < nuC →
      CdCapV S μ := by
    intro μ hr h0 h1 hν
    obtain ⟨i0, i1⟩ := Ys.ysIdx_win h0 h1
    exact Zh.zhCapV_of hr hν (h1.trans_le hBP) (hVL μ hr i0 i1 hν)
  obtain ⟨hν, Sp'⟩ := zoSpec_caps0 Sp hBm hcap (fun h => (hbase0 h).1) (fun μ _ => rfl) hVν
  -- LOWER at the range restarts `≤ l₀`
  have hL0 : ∀ μ, CdRange S μ → μ ≤ l0 → CdLower S μ := by
    intro μ hr hμ
    rcases hμ.lt_or_eq with hμ | rfl
    · exact hLlow μ hr hμ
    · exact (hbase0 hr).2
  -- the RS input at every restart of the interval
  have hrs : ∀ l, IsRestartIdx l → l0 < l → l < B →
      Zc.ZcRsIn (Ys.ysO S) l ∨ Zh.ZhSupIn S l B := by
    intro l hl h1 h2
    refine Zh.zhIn_of_B hl hν hBP h2 ?_
    rcases eq_or_lt_of_le hm.le_apply with he | hfix
    · exact hrsF l hl h1 h2 he.symm
    · exact Or.inl (Zh.zhRsIn_nonfix hl (Zh.zh_ww_lt hl0 h1) hfix ((hm h2).trans_le hν)
        ((hm h2).trans_le hBP))
  have hRS := Zh.zhRs_all Sp' hν (fun μ _ => rfl) hL0 hrs
  refine ⟨hν, fun μ hr h0 h1 => ?_⟩
  have hR : upsilon (μ + ω + 1) + Ys.ysO S μ = cdR S μ := Ys.ysO_eq S μ
  have hU : CdUpper S μ := Ys.ysUpper_all Sp' hr.1 h0.le h1 hR
  have hL : CdLower S μ := by unfold CdLower; rw [← hR]; exact hRS μ hr.1 h0 h1
  exact ⟨hU, hL, Zh.zhCapV_of hr ((hm h1).trans_le hν) ((hm h1).trans_le hBP)
    (hVL μ hr h0 h1 ((hm h1).trans_le hν))⟩

/-- **NON-VACUITY of `zoInt`**: its interval inputs follow from UPPER, LOWER, CapV at the range restarts of
`[l₀, B)` and the chain reach data (chain start `0`) at the restarts of `[l₀, B)`. -/
theorem zoInt_of_target {l0 B : Ordinal.{0}} (hl0B : cdB0 ≤ l0) (hBm : upsilon B ≤ cdMstar S)
    (hU : ∀ μ, CdRange S μ → l0 ≤ μ → μ < B → CdUpper S μ)
    (hL : ∀ μ, CdRange S μ → l0 < μ → μ < B → CdLower S μ)
    (hV : ∀ μ, CdRange S μ → l0 < μ → μ < B → CdCapV S μ)
    (hR : ∀ l, IsRestartIdx l → l0 ≤ l → l < B → Ys.YsReachIn l 0 (upsilon l)) (hl0 : IsRestartIdx l0)
    (hlt : l0 < B) :
    Yx.YxGivenIn (Ys.ysO S) l0 ∧ Zc.ZcInR S l0 B ∧
      (∀ μ, CdRange S μ → l0 < μ → μ < B → upsilon μ = μ → upsilon μ < nuC → ¬ Zh.ZhShortExp S μ →
        CdCapV S μ) ∧
      (∀ l, IsRestartIdx l → l0 < l → l < B → upsilon l = l →
        Zc.ZcRsIn (Ys.ysO S) l ∨ Zh.ZhSupInB S l B) := by
  have hm := upsilon_normal.strictMono
  have hrg : ∀ l, IsRestartIdx l → l0 ≤ l → l < B → CdRange S l := fun l hl h0 h1 =>
    zoRange_lt hl (hl0B.trans h0) ((hm h1).trans_le hBm)
  have hδ : ∀ l : Ordinal.{0}, IsRestartIdx l → (0 : Ordinal.{0}) < upsilon (l + ω + 1) := fun l hl =>
    lt_of_le_of_lt zero_le (hm (lt_of_lt_of_le (pos_iff_ne_zero.2 hl.1) (le_self_add.trans le_self_add)))
  refine ⟨zoGiven_of (hU l0 (hrg l0 hl0 le_rfl hlt) le_rfl hlt) (hδ l0 hl0) zero_le (hR l0 hl0 le_rfl hlt),
    (Yx.yxIn_of_upper (B := B) (S := S) (hR l0 hl0 le_rfl hlt) fun l hl h0 h1 =>
      ⟨hU l (hrg l hl h0.le h1) h0.le h1, hR l hl h0.le h1⟩).2,
    fun μ hr h0 h1 _ _ _ => hV μ hr h0 h1,
    fun l hl h0 h1 _ => Zh.zhIn4_of_lower (hL l (hrg l hl h0.le h1) h0 h1)⟩

/-- **CapV at a low code**: a restart below `ν_C` and `L(ω)` with code `m_λ ≤ θ·ω` and last exponent `e ≥ 2` has
`r(λ) < υ_{λ+ω+2} < υ_{λ+ω+3} = P(η_λ + ω + 3) ≤ P(η_λ + ω^e)` (`Rc.rcR_lowCode`). -/
theorem zoCapV_low {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hn : upsilon l < Pv S η1)
    (hν : upsilon l < nuC) (hω : upsilon l < Nc.ncL S ω) (hcode : cdCode S l ≤ ConjT.th S * ω)
    (he2 : ω ^ 2 ≤ ω ^ cdExp (cdEta S l)) : CdCapV S l := by
  have hm := upsilon_normal.strictMono
  have hC : upsilon (l + ω + 1) < nuC := (Yx.yxDelta_lt_next l).trans_le (Yx.yxNext_le_nuC hl hν)
  have hR := Rc.rcR_lowCode hl hω hC hcode
  obtain ⟨hg, hι, -, hpv⟩ := cdEta_pv_spec (S := S) hl.1 hn
  have hE : InE (upsilon l) := upsPt_inE (upsPt_upsilon (pos_iff_ne_zero.2 hl.1))
  have h3 : ω + 3 < upsilon l := by
    have hw : ω < upsilon l := omega0_lt_inE hE
    have hw2 : ω * ω < upsilon l := mul_lt_inE hE hw hw
    refine lt_of_lt_of_le ?_ hw2.le
    calc ω + 3 < ω + ω := (add_lt_add_iff_left ω).2 (natCast_lt_omega0 3)
      _ = ω * 2 := by rw [show (2 : Ordinal.{0}) = 1 + 1 from one_add_one_eq_two.symm, mul_add, mul_one]
      _ ≤ ω * ω := mul_le_mul_left' (natCast_lt_omega0 2).le ω
  have hι3 : iota S (cdEta S l + (ω + 3)) = l + (ω + 3) := by
    rw [Cp.cpIota_add hg (hpv ▸ h3), hι]
  have hle : ω + 3 ≤ ω ^ cdExp (cdEta S l) := by
    refine le_trans ?_ he2
    rw [pow_two]
    calc ω + 3 ≤ ω + ω := (add_le_add_iff_left ω).2 (natCast_lt_omega0 3).le
      _ = ω * 2 := by rw [show (2 : Ordinal.{0}) = 1 + 1 from one_add_one_eq_two.symm, mul_add, mul_one]
      _ ≤ ω * ω := mul_le_mul_left' (natCast_lt_omega0 2).le ω
  have hcap : upsilon (l + (ω + 3)) ≤ cdCapB S l := by
    unfold cdCapB
    rw [← hι3, ups_iota S]
    exact Pv_mono ((add_le_add_iff_left _).2 hle)
  have h23 : upsilon (l + (ω + 2)) < upsilon (l + (ω + 3)) :=
    hm ((add_lt_add_iff_left l).2 ((add_lt_add_iff_left ω).2 (by norm_num)))
  exact hR.trans (h23.trans_le hcap)

end Googology.Trans.PoR.InaccPsi.R2.Zo

import Googology.Trans.PoR.InaccPsi.R2.ZcRS

/-!
# Zc: the RS input of the windows as a statement on the predicted reaches only

`Ys.ysRs_all` (Lemma RS at every restart of a window) asks at a limit restart `λ` the input `Ys.YsRsIn`: for every
`z < O(λ)` a bound function `T` with `z ≤ T(ρ_λ)`, a RELATIVE RS STEP `Ys.YsRsStep λ T` (an `≤₁`-statement:
from a restart context with crossings at `λ` and lower targets `ρ_μ ≤₁ δ_μ + T(ρ_μ)` to `ρ_λ ≤₁ δ_λ + T(ρ_λ) + 1`)
and restarts `μ` cofinal below `λ` with `T(ρ_μ) ≤ O(μ)`.  With `Zc.zcRs_rstT` the RS step is a THEOREM for every
offset term `t` (constants below `ρ_λ`), given the pairs up to `δ_λ + t(ρ_λ)`, which hold below `ν_C`.  So the
input that is left is a statement on the bound `O = r − δ` alone:

* `ZcRsTerm O λ`: for every `z < O(λ)` an offset term `t` with constants below `ρ_λ`, `z ≤ t(ρ_λ)`, and restarts
  `μ` cofinal below `λ` with `t(ρ_μ) ≤ O(μ)`;
* `ZcRsIn O λ`: LOWER at `λ`, or a successor index with `O(λ) = 1`, or a limit index with `1 ≤ O(λ)` and
  `ZcRsTerm O λ`;
* `zcNostr_of_nu`: no `<₂`-pair from a point `≤ ρ_λ` ends in `[ρ_λ, δ_λ + t(ρ_λ)]` when `ρ_λ < ν_C`;
* `zcRs_all` (**Lemma RS at every restart of a specification below `ν_C`** with the input `ZcRsIn`);
* `zcWin_UL`, `zcTop_UL`: UPPER ∧ LOWER on `W_k`, `W_ω` with this input;
* `zcWins2`, `zcTopAll2` (**the windows by one induction, base reach datum proved, RS input `ZcRsIn`**);
* `zcRsIn_of_lower`, `zcWins2_of_target` (**non-vacuity**).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Zc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.OT

variable {S : InaccSeq.{0}}

/-- **The term input of Lemma RS at a limit restart**: a statement on the bound `O` alone. -/
def ZcRsTerm (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : Prop :=
  ∀ z < O l, ∃ t : OT, CB t (upsilon l) ∧ z ≤ ev t (upsilon l) ∧
    ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ ev t (upsilon μ) ≤ O μ

/-- **The RS input at a restart**: LOWER, or the successor case, or the term input. -/
def ZcRsIn (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : Prop :=
  le1 (upsilon l) (upsilon (l + ω + 1) + O l) ∨ (cL l < 2 ∧ O l = 1) ∨
    (2 ≤ cL l ∧ 1 ≤ O l ∧ ZcRsTerm O l)

/-- **No pair from a point `≤ ρ_λ` ends in `[ρ_λ, δ_λ + t(ρ_λ)]`** when `ρ_λ < ν_C`. -/
theorem zcNostr_of_nu {l : Ordinal.{0}} (hl : IsRestartIdx l) (hν : upsilon l < nuC) {t : OT}
    (ht : CB t (upsilon l)) :
    ∀ c d, c < d → c ≤ upsilon l → upsilon l ≤ d → d ≤ upsilon (l + ω + 1) + ev t (upsilon l) →
      ¬ le2 c d := by
  intro c d hcd hc hd hdg h2
  have hm := upsilon_normal.strictMono
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρδ : upsilon l < upsilon (l + ω + 1) :=
    hm (lt_of_lt_of_le (lt_add_of_pos_right l omega0_pos) le_self_add)
  have hδE : InE (upsilon (l + ω + 1)) :=
    upsPt_inE (upsPt_upsilon (lt_of_lt_of_le hl0 (le_self_add.trans le_self_add)))
  have hev : ev t (upsilon l) < upsilon (l + ω + 1) := ev_lt hδE hρδ t (CB_mono ht hρδ.le)
  have hδW : upsilon (l + ω + 1) < upsilon (l + ω * ω) := hm (by simpa using idx_lt l 0 1)
  have hWI := indec_of_upsPt (upsPt_upsilon (show 0 < l + ω * ω from lt_of_lt_of_le hl0 le_self_add))
  have hdW : d < upsilon (l + ω * ω) := lt_of_le_of_lt hdg (hWI.add_lt hδW (hev.trans hδW))
  have hdν : d < nuC := lt_of_lt_of_le hdW (Yx.yxNext_le_nuC hl hν)
  exact Yx.yxStd_noStraddle (std_of_lt_nuC hdν hcd h2) hl hc hd

/-- **Lemma RS at every restart `l₀ < l < B` of a specification below `ν_C`**, with the input `ZcRsIn`. -/
theorem zcRs_all {O : Ordinal.{0} → Ordinal.{0}} {l0 B : Ordinal.{0}} (Sp : Ys.YsSpec O l0 B)
    (hν : upsilon B ≤ nuC)
    (hin : ∀ l, IsRestartIdx l → l0 < l → l < B → ZcRsIn O l) :
    ∀ l, IsRestartIdx l → l0 < l → l < B → le1 (upsilon l) (upsilon (l + ω + 1) + O l) := by
  intro l
  induction l using WellFoundedLT.induction with
  | ind l IH =>
  intro hl hl0l hlB
  have R := (Ys.ysTop_all Sp hl hl0l.le hlB).1
  have hlν : upsilon l < nuC := (upsilon_normal.strictMono hlB).trans_le hν
  rcases hin l hl hl0l hlB with hlow | ⟨h2, hO1⟩ | ⟨h2, hone, hRs⟩
  · exact hlow
  · rw [hO1]
    obtain ⟨l1, hl1', rfl⟩ := succ_ri hl h2
    rcases hl1' with rfl | hl1r
    · exfalso
      rw [zero_add] at hl0l
      exact absurd hl0l (not_lt.2 (ri_ge Sp.ri))
    · have h01 : l0 ≤ l1 := by
        by_contra h
        have := next_mult (ri_iff.1 hl1r).2 (ri_iff.1 Sp.ri).2 (not_le.1 h)
        exact absurd hl0l (not_lt.2 this)
      exact Ys.ysRs_succ Sp hl1r h01 hlB
  · have hlim : IsSuccLimit l := by
      obtain ⟨q, hq⟩ := (ri_iff.1 hl).2
      have hq0 : q ≠ 0 := by intro h0; rw [h0, mul_zero] at hq; exact hl.1 hq
      rw [hq]
      exact isSuccLimit_mul_left (isSuccLimit_mul_right omega0_pos isSuccLimit_omega0)
        (pos_iff_ne_zero.2 hq0)
    have hstep : ∀ z < O l, le1 (upsilon l) (upsilon (l + ω + 1) + z + 1) := by
      intro z hz
      obtain ⟨t, ht, hzu, hcof⟩ := hRs z hz
      have htg : ∀ κ' < upsilon l, ∃ μ, κ' < upsilon μ ∧ upsilon (μ + ω + 1) < upsilon l ∧
          Ys.YsRstK (upsilon μ) (upsilon (μ + ω)) (upsilon (μ + ω + 1)) ∧
          ∀ g, upsilon μ ≤ g → g ≤ upsilon (μ + ω + 1) + ev t (upsilon μ) →
            le1 (upsilon μ) g := by
        intro κ' hκ'
        obtain ⟨_, ⟨ι, hι, rfl⟩, hκι⟩ := (lt_isLUB_iff (upsilon_limit hlim)).1 hκ'
        obtain ⟨μ, hμ, hιμ, hμl, htv⟩ := hcof (max ι l0) (max_lt hι hl0l)
        have hμB : μ < B := hμl.trans hlB
        have hl0μ : l0 < μ := (le_max_right _ _).trans_lt hιμ
        have Rμ := (Ys.ysTop_all Sp hμ hl0μ.le hμB).1
        have hrsμ := IH μ hμl hμ hl0μ hμB
        refine ⟨μ, hκι.trans (upsilon_normal.strictMono ((le_max_left _ _).trans_lt hιμ)), ?_, Rμ,
          fun g hg1 hg2 => le1_of_le_of_le1 hg1 (hg2.trans (add_le_add le_rfl htv)) hrsμ⟩
        exact upsilon_normal.strictMono (lt_of_lt_of_le (by simpa using idx_lt μ 0 1)
          (next_mult (ri_iff.1 hμ).2 (ri_iff.1 hl).2 hμl))
      refine le1_of_le_of_le1 (R.ρδ.le.trans (le_self_add.trans le_self_add))
        (add_le_add (add_le_add le_rfl hzu) le_rfl) ?_
      exact zcRs_rstT R ht (zcNostr_of_nu hl hlν ht) htg
    have hρδ := R.ρδ
    have hall : ∀ b', upsilon l ≤ b' → b' < upsilon (l + ω + 1) + O l → le1 (upsilon l) b' := by
      intro b' hb1 hb2
      rcases le_or_gt b' (upsilon (l + ω + 1)) with hbδ | hδb
      · exact R.le1ρδ b' hb1 hbδ
      · have he : upsilon (l + ω + 1) + (b' - upsilon (l + ω + 1)) = b' :=
          Ordinal.add_sub_cancel_of_le hδb.le
        have hz : b' - upsilon (l + ω + 1) < O l := by
          rw [← he] at hb2; exact (add_lt_add_iff_left _).1 hb2
        have hb'le : b' ≤ upsilon (l + ω + 1) + (b' - upsilon (l + ω + 1)) + 1 :=
          calc b' = upsilon (l + ω + 1) + (b' - upsilon (l + ω + 1)) := he.symm
            _ ≤ _ := le_self_add
        exact le1_of_le_of_le1 hb1 hb'le (hstep _ hz)
    rcases zero_or_succ_or_isSuccLimit (O l) with h0 | ⟨z0, hz0⟩ | hlimo
    · exact absurd h0 (ne_of_gt (lt_of_lt_of_le zero_lt_one hone))
    · rw [← hz0, succ_eq_add_one, ← add_assoc]
      exact hstep z0 (by rw [← hz0]; exact lt_succ z0)
    · exact le1_limit (isSuccLimit_add _ hlimo)
        (lt_of_lt_of_le hρδ le_self_add) (fun b' hb1 hb2 => hall b' hb1 hb2)

/-- The RS input depends on the bound only at and above the restart. -/
theorem zcRsIn_congr {l0 : Ordinal.{0}} {O O' : Ordinal.{0} → Ordinal.{0}} (h : ∀ μ, l0 < μ → O μ = O' μ)
    {l : Ordinal.{0}} (hl : l0 < l) (hin : ZcRsIn O' l) : ZcRsIn O l := by
  unfold ZcRsIn at hin ⊢
  rw [h l hl]
  rcases hin with h1 | h1 | ⟨h2, h3, h4⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · refine Or.inr (Or.inr ⟨h2, h3, fun z hz => ?_⟩)
    have hz' : z < O' l := by rw [← h l hl]; exact hz
    obtain ⟨t, ht1, ht2, ht3⟩ := h4 z hz'
    refine ⟨t, ht1, ht2, fun ν hν => ?_⟩
    obtain ⟨μ, hμ, hνμ, hμl, htμ⟩ := ht3 (max ν l0) (max_lt hν hl)
    exact ⟨μ, hμ, (le_max_left _ _).trans_lt hνμ, hμl, by
      rw [h μ ((le_max_right _ _).trans_lt hνμ)]; exact htμ⟩

/-- **The RS input from LOWER** (non-vacuity: at a Range restart LOWER is the first case). -/
theorem zcRsIn_of_lower {l : Ordinal.{0}} (hL : CdLower S l) : ZcRsIn (Ys.ysO S) l := by
  left; rw [Ys.ysO_eq]; exact hL

/-- **UPPER ∧ LOWER at every Range restart of `W_k`** with the RS input `ZcRsIn`. -/
theorem zcWin_UL (k : ℕ) {O : Ordinal.{0} → Ordinal.{0}}
    (hO : ∀ μ, Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < μ → O μ = Ys.ysO S μ)
    (Sp : Ys.YsSpec O (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
      (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))))
    (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC)
    (hin : ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) → ZcRsIn O l) :
    ∀ μ, CdRange S μ → Wj.WjWin S k μ → CdUpper S μ ∧ CdLower S μ := by
  have hO' : ∀ μ, CdRange S μ → Wj.WjWin S k μ → upsilon (μ + ω + 1) + O μ = cdR S μ := by
    intro μ _ hw
    have h0 := hw.1
    rw [Pp.ppL_eq_ups (S := S)] at h0
    rw [hO μ (upsilon_normal.strictMono.lt_iff_lt.1 h0)]
    exact Ys.ysO_eq S μ
  intro μ hr hw
  have h0 : upsilon (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0}))) < upsilon μ :=
    (Yx.yxUps_base (S := S) _).symm ▸ hw.1
  have h1 : upsilon μ < upsilon (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) :=
    (Yx.yxUps_base (S := S) _).symm ▸ hw.2
  obtain ⟨i0, i1⟩ := Ys.ysIdx_win h0 h1
  refine ⟨Ys.ysWin_upper k (Pp.ppL_eq_ups (S := S) _) (Pp.ppL_eq_ups (S := S) _) Sp hO' μ hr hw, ?_⟩
  unfold CdLower
  rw [← hO' μ hr hw]
  exact zcRs_all Sp (by rw [Yx.yxUps_base]; exact hν) hin μ hr.1 i0 i1

/-- **UPPER ∧ LOWER at every Range restart of `W_ω`** with the RS input `ZcRsIn`. -/
theorem zcTop_UL {O : Ordinal.{0} → Ordinal.{0}}
    (hO : ∀ μ, Bt.iota S (Om ω + Nc.ncPp S * ω) < μ → O μ = Ys.ysO S μ)
    (Sp : Ys.YsSpec O (Bt.iota S (Om ω + Nc.ncPp S * ω)) (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))))
    (hν : Nc.ncL S (ω + 1) ≤ nuC)
    (hin : ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * ω) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * (ω + 1)) → ZcRsIn O l) :
    ∀ μ, CdRange S μ → Wj.WjTop S μ → CdUpper S μ ∧ CdLower S μ := by
  have hO' : ∀ μ, CdRange S μ → Wj.WjTop S μ → upsilon (μ + ω + 1) + O μ = cdR S μ := by
    intro μ _ hw
    have h0 := hw.1
    rw [Pp.ppL_eq_ups (S := S)] at h0
    rw [hO μ (upsilon_normal.strictMono.lt_iff_lt.1 h0)]
    exact Ys.ysO_eq S μ
  intro μ hr hw
  have h0 : upsilon (Bt.iota S (Om ω + Nc.ncPp S * ω)) < upsilon μ :=
    (Yx.yxUps_base (S := S) _).symm ▸ hw.1
  have h1 : upsilon μ < upsilon (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))) :=
    (Yx.yxUps_base (S := S) _).symm ▸ hw.2
  obtain ⟨i0, i1⟩ := Ys.ysIdx_win h0 h1
  refine ⟨Ys.ysTop_upper (Pp.ppL_eq_ups (S := S) _) (Pp.ppL_eq_ups (S := S) _) Sp hO' μ hr hw, ?_⟩
  unfold CdLower
  rw [← hO' μ hr hw]
  exact zcRs_all Sp (by rw [Yx.yxUps_base]; exact hν) hin μ hr.1 i0 i1

/-- **ALL WINDOWS `W_k` BY ONE INDUCTION ON `k`**: base reach datum proved, RS input `ZcRsIn`. -/
theorem zcWins2
    (hin : ∀ k : ℕ, ZcInR S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
      (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))))
    (hlow : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S 0 → CdUpper S μ ∧ CdLower S μ ∧ CdCapV S μ)
    (hV : ∀ k : ℕ, ∀ μ, CdRange S μ → Wj.WjWin S k μ → CdCapV S μ)
    (hrs : ∀ k : ℕ, ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) → ZcRsIn (Ys.ysO S) l) :
    ∀ k : ℕ, Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC ∧
      Ys.YsSpec (Yx.yxO S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0}))))
        (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
        (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) ∧
      ∀ μ, CdRange S μ → Wj.WjWin S k μ → CdUpper S μ ∧ CdLower S μ := by
  have hlow' : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S 0 → CdUpper S μ ∧ CdCapV S μ :=
    fun μ hr h => ⟨(hlow μ hr h).1, (hlow μ hr h).2.2⟩
  have h0 : CdCAP0 S := Yx.yxCAP0 fun μ hr h => cdCapAt_of_upper (hlow μ hr h).1 (hlow μ hr h).2.2
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
  have hb := Yx.yxCaps_below k hlow' fun j hj μ hr hw =>
    ⟨((IH j hj).2.2 μ hr hw).1, hV j μ hr hw⟩
  have hL := zcLower_below k (fun μ hr h => (hlow μ hr h).2.1) fun j hj μ hr hw =>
    ((IH j hj).2.2 μ hr hw).2
  obtain ⟨hν, Sp⟩ := Yx.yxWin_full k ⟨zcBaseIn k h0 hb hL, hin k⟩ h0 hb (hV k)
  refine ⟨hν, Sp, zcWin_UL k (fun μ h => Yx.yxO_above h) Sp hν fun l hl h1 h2 =>
    zcRsIn_congr (fun μ h => Yx.yxO_above h) h1 (hrs k l hl h1 h2)⟩

/-- **THE TOP WINDOW `W_ω`**: base reach datum proved, RS input `ZcRsIn`. -/
theorem zcTopAll2
    (hin : ∀ k : ℕ, ZcInR S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
      (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))))
    (hlow : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S 0 → CdUpper S μ ∧ CdLower S μ ∧ CdCapV S μ)
    (hV : ∀ k : ℕ, ∀ μ, CdRange S μ → Wj.WjWin S k μ → CdCapV S μ)
    (hrs : ∀ k : ℕ, ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) → ZcRsIn (Ys.ysO S) l)
    (hinT : ZcInR S (Bt.iota S (Om ω + Nc.ncPp S * ω)) (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))))
    (hVT : ∀ μ, CdRange S μ → Wj.WjTop S μ → CdCapV S μ)
    (hrsT : ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * ω) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * (ω + 1)) → ZcRsIn (Ys.ysO S) l)
    (hLw : Yx.YxLwNo2 S) :
    Nc.ncL S (ω + 1) ≤ nuC ∧
      Ys.YsSpec (Yx.yxO S (Bt.iota S (Om ω + Nc.ncPp S * ω))) (Bt.iota S (Om ω + Nc.ncPp S * ω))
        (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))) ∧
      ∀ μ, CdRange S μ → Wj.WjTop S μ → CdUpper S μ ∧ CdLower S μ := by
  have W := zcWins2 hin hlow hV hrs
  have hlow' : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S 0 → CdUpper S μ ∧ CdCapV S μ :=
    fun μ hr h => ⟨(hlow μ hr h).1, (hlow μ hr h).2.2⟩
  have h0 : CdCAP0 S := Yx.yxCAP0 fun μ hr h => cdCapAt_of_upper (hlow μ hr h).1 (hlow μ hr h).2.2
  have hb : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → CdCapAt S μ := by
    intro μ hr hμ
    obtain ⟨n, hn⟩ := Pp.ppL_cof (S := S) _ hμ
    exact Yx.yxCaps_below (n + 1) hlow' (fun j _ μ hr hw => ⟨((W j).2.2 μ hr hw).1, hV j μ hr hw⟩) μ hr hn
  have hL : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → CdLower S μ := by
    intro μ hr hμ
    obtain ⟨n, hn⟩ := Pp.ppL_cof (S := S) _ hμ
    exact zcLower_below (n + 1) (fun μ hr h => (hlow μ hr h).2.1)
      (fun j _ μ hr hw => ((W j).2.2 μ hr hw).2) μ hr hn
  have hρ : upsilon (Bt.iota S (Om ω + Nc.ncPp S * ω)) < nuC := by
    rw [Yx.yxUps_base]
    refine Yx.yxNu_gt le_rfl h0 ?_
    intro μ hμ hB hlev hlX hc
    exact hb μ ⟨hμ, hB, hlX.trans (Qq.qqL_lt_succ S), hc⟩ hlX
  have hbase : Ys.YsReachIn (Bt.iota S (Om ω + Nc.ncPp S * ω)) 0
      (upsilon (Bt.iota S (Om ω + Nc.ncPp S * ω))) :=
    zcBase_reach Yx.yxBaseW_ri (zcL_cnt _) hρ zcSupW
      (fun μ hr h => hL μ hr (by rw [Yx.yxUps_base] at h; exact h))
  obtain ⟨hν, Sp⟩ := Yx.yxTop_full ⟨hbase, hinT⟩ h0 hLw hb hVT
  exact ⟨hν, Sp, zcTop_UL (fun μ h => Yx.yxO_above h) Sp hν fun l hl h1 h2 =>
    zcRsIn_congr (fun μ h => Yx.yxO_above h) h1 (hrsT l hl h1 h2)⟩

/-- **NON-VACUITY of `zcWins2`**: its hypotheses follow from UPPER, LOWER, CapV at the Range restarts below
`L(ω)` and the chain reach data `Ys.YsReachIn l 0 ρ_l` at the restarts below `L(ω)`. -/
theorem zcWins2_of_target
    (hU : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → CdUpper S μ)
    (hL : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → CdLower S μ)
    (hV : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → CdCapV S μ)
    (hR : ∀ l, IsRestartIdx l → upsilon l < Nc.ncL S ω → Ys.YsReachIn l 0 (upsilon l)) :
    (∀ k : ℕ, ZcInR S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
      (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})))) ∧
    (∀ μ, CdRange S μ → upsilon μ < Nc.ncL S 0 → CdUpper S μ ∧ CdLower S μ ∧ CdCapV S μ) ∧
    (∀ k : ℕ, ∀ μ, CdRange S μ → Wj.WjWin S k μ → CdCapV S μ) ∧
    (∀ k : ℕ, ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) → ZcRsIn (Ys.ysO S) l) := by
  obtain ⟨h1, h2⟩ := zcWins_of_target hU hL hV hR
  obtain ⟨-, -, h3, -⟩ := Yx.yxWins_of_target hU hL hV hR
  refine ⟨h1, h2, h3, fun k l hl i0 i1 => ?_⟩
  have a0 : Nc.ncL S (k : Ordinal.{0}) < upsilon l := by
    rw [← Yx.yxUps_base (S := S)]; exact upsilon_normal.strictMono i0
  have a1 : upsilon l < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) := by
    rw [← Yx.yxUps_base (S := S)]; exact upsilon_normal.strictMono i1
  have hr : CdRange S l :=
    Yx.yxWin_range (ξ := (k : Ordinal.{0})) (natCast_lt_omega0 k).le hl a0 (by exact_mod_cast a1)
  exact zcRsIn_of_lower (hL l hr (a1.trans (Pp.ppL_lt_omega (S := S) k)))

end Googology.Trans.PoR.InaccPsi.R2.Zc

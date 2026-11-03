import Googology.Trans.PoR.InaccPsi.R2.YsWin
import Googology.Trans.PoR.InaccPsi.R2.RgNu

/-!
# Ys: Lemma RS at every restart of the relative block induction

The relative form of `Yf.yfRs`: inside `Ys.YsSpec O l₀ B`, every restart `l₀ < l < B` has
`ρ_l ≤₁ δ_l + O(l)` (LOWER when `δ_l + O(l) = r(l)`), given at each restart one of

* LOWER itself (a supply restart: its long reach is an input, as its UPPER is in `Ys.YsGivenIn`);
* a successor index (`cL l < 2`) with `O(l) = 1` (Lemma RS with crossings, `Ys.ysRs_succ`);
* a limit index (`2 ≤ cL l`) with `1 ≤ O(l)` and the input `YsRsIn O l`: every `z < O(l)` is `≤ T(ρ_l)` for a
  term `T` with a relative RS step (`YsRsStep`) realized by restarts cofinal below `l`.

`YsRsStep l T` is `R2.RsStep l T` with the restart contexts with crossings (`Ys.YsRstK`).

* `ysRs_all` (**Lemma RS with crossings at every restart**), `ysWin_lower` (**LOWER in a window**).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ys

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi

/-- **A relative RS step** for the term `T` at `l` (`R2.RsStep` with restart contexts with crossings). -/
def YsRsStep (l : Ordinal.{0}) (T : Ordinal.{0} → Ordinal.{0}) : Prop :=
  YsRstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1)) →
  (∀ κ' < upsilon l, ∃ μ, κ' < upsilon μ ∧ upsilon (μ + ω + 1) < upsilon l ∧
      YsRstK (upsilon μ) (upsilon (μ + ω)) (upsilon (μ + ω + 1)) ∧
      ∀ g, upsilon μ ≤ g → g ≤ upsilon (μ + ω + 1) + T (upsilon μ) → le1 (upsilon μ) g) →
  le1 (upsilon l) (upsilon (l + ω + 1) + T (upsilon l) + 1)

/-- **The input of relative Lemma RS at a limit restart index.** -/
def YsRsIn (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : Prop :=
  ∀ z < O l, ∃ T : Ordinal.{0} → Ordinal.{0}, z ≤ T (upsilon l) ∧ YsRsStep l T ∧
    ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ T (upsilon μ) ≤ O μ

section Spec

variable {O : Ordinal.{0} → Ordinal.{0}} {l0 B : Ordinal.{0}} (Sp : YsSpec O l0 B)
include Sp

/-- **Lemma RS with crossings at every restart `l₀ < l < B`**: `ρ_l ≤₁ δ_l + O(l)`. -/
theorem ysRs_all
    (hin : ∀ l, IsRestartIdx l → l0 < l → l < B →
      le1 (upsilon l) (upsilon (l + ω + 1) + O l) ∨ (cL l < 2 ∧ O l = 1) ∨
        (2 ≤ cL l ∧ 1 ≤ O l ∧ YsRsIn O l)) :
    ∀ l, IsRestartIdx l → l0 < l → l < B → le1 (upsilon l) (upsilon (l + ω + 1) + O l) := by
  intro l
  induction l using WellFoundedLT.induction with
  | ind l IH =>
  intro hl hl0l hlB
  have R := (ysTop_all Sp hl hl0l.le hlB).1
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
      exact ysRs_succ Sp hl1r h01 hlB
  · have hlim : IsSuccLimit l := by
      obtain ⟨q, hq⟩ := (ri_iff.1 hl).2
      have hq0 : q ≠ 0 := by intro h0; rw [h0, mul_zero] at hq; exact hl.1 hq
      rw [hq]
      exact isSuccLimit_mul_left (isSuccLimit_mul_right omega0_pos isSuccLimit_omega0)
        (pos_iff_ne_zero.2 hq0)
    have hstep : ∀ z < O l, le1 (upsilon l) (upsilon (l + ω + 1) + z + 1) := by
      intro z hz
      obtain ⟨T, hzu, hRS, hcof⟩ := hRs z hz
      have htg : ∀ κ' < upsilon l, ∃ μ, κ' < upsilon μ ∧ upsilon (μ + ω + 1) < upsilon l ∧
          YsRstK (upsilon μ) (upsilon (μ + ω)) (upsilon (μ + ω + 1)) ∧
          ∀ g, upsilon μ ≤ g → g ≤ upsilon (μ + ω + 1) + T (upsilon μ) →
            le1 (upsilon μ) g := by
        intro κ' hκ'
        obtain ⟨_, ⟨ι, hι, rfl⟩, hκι⟩ := (lt_isLUB_iff (upsilon_limit hlim)).1 hκ'
        obtain ⟨μ, hμ, hιμ, hμl, htv⟩ := hcof (max ι l0) (max_lt hι hl0l)
        have hμB : μ < B := hμl.trans hlB
        have hl0μ : l0 < μ := (le_max_right _ _).trans_lt hιμ
        have Rμ := (ysTop_all Sp hμ hl0μ.le hμB).1
        have hrsμ := IH μ hμl hμ hl0μ hμB
        refine ⟨μ, hκι.trans (upsilon_normal.strictMono ((le_max_left _ _).trans_lt hιμ)), ?_, Rμ,
          fun g hg1 hg2 => le1_of_le_of_le1 hg1 (hg2.trans (add_le_add le_rfl htv)) hrsμ⟩
        exact upsilon_normal.strictMono (lt_of_lt_of_le (by simpa using idx_lt μ 0 1)
          (next_mult (ri_iff.1 hμ).2 (ri_iff.1 hl).2 hμl))
      refine le1_of_le_of_le1 (R.ρδ.le.trans (le_self_add.trans le_self_add))
        (add_le_add (add_le_add le_rfl hzu) le_rfl) ?_
      exact hRS R htg
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

end Spec

/-- **Non-vacuity of the RS input**: below `Ξ_ω` the input of `ysRs_all` holds for the repo's offsets `c*`
(the successor branch at `cL λ < 2`, otherwise the repo's `R2.rs_all`). -/
theorem ysRsIn_old : ∀ l, IsRestartIdx l → ω * ω < l → l < XiW + ω * ω →
    le1 (upsilon l) (upsilon (l + ω + 1) + off l) ∨ (cL l < 2 ∧ off l = 1) ∨
      (2 ≤ cL l ∧ 1 ≤ off l ∧ YsRsIn off l) := by
  intro l hl _ hlB
  rcases lt_or_ge (cL l) 2 with h2 | h2
  · exact Or.inr (Or.inl ⟨h2, off_succ hl h2⟩)
  · left
    have hlX : l ≤ XiW := by
      by_contra hgt
      exact absurd hlB (not_lt.2 (next_mult (ri_iff.1 XiW_ri).2 (ri_iff.1 hl).2 (not_le.1 hgt)))
    exact rs_all hl hlX

/-- **The relative RS reproves Lemma RS below `Ξ_ω`** (on `Ys.ysSpec_old`). -/
theorem ysRsAll_old {l : Ordinal.{0}} (hl : IsRestartIdx l) (h0 : ω * ω < l) (hlB : l < XiW + ω * ω) :
    le1 (upsilon l) (upsilon (l + ω + 1) + off l) :=
  ysRs_all ysSpec_old ysRsIn_old l hl h0 hlB

variable {S : InaccSeq.{0}}

/-- **LOWER at every range restart of the window `W_k`** from the relative block induction on
`[ι(L(k)), ι(L(k+1)))`, the bounds `δ_μ + O(μ) = r(μ)` and the RS input at each window restart. -/
theorem ysWin_lower (k : ℕ) {O : Ordinal.{0} → Ordinal.{0}} {l0 l1 : Ordinal.{0}}
    (e0 : Nc.ncL S (k : Ordinal.{0}) = upsilon l0) (e1 : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) = upsilon l1)
    (Sp : YsSpec O l0 l1)
    (hO : ∀ μ, Cd.CdRange S μ → Wj.WjWin S k μ → upsilon (μ + ω + 1) + O μ = Cd.cdR S μ)
    (hin : ∀ l, IsRestartIdx l → l0 < l → l < l1 →
      le1 (upsilon l) (upsilon (l + ω + 1) + O l) ∨ (cL l < 2 ∧ O l = 1) ∨
        (2 ≤ cL l ∧ 1 ≤ O l ∧ YsRsIn O l)) :
    ∀ μ, Cd.CdRange S μ → Wj.WjWin S k μ → Cd.CdUpper S μ ∧ Cd.CdLower S μ := by
  intro μ hr hw
  have h0 : upsilon l0 < upsilon μ := e0 ▸ hw.1
  have h1 : upsilon μ < upsilon l1 := e1 ▸ hw.2
  obtain ⟨i0, i1⟩ := ysIdx_win h0 h1
  refine ⟨ysWin_upper k e0 e1 Sp hO μ hr hw, ?_⟩
  unfold Cd.CdLower
  rw [← hO μ hr hw]
  exact ysRs_all Sp hin μ hr.1 i0 i1

/-- **The same in the top window `W_ω`.** -/
theorem ysTop_lower {O : Ordinal.{0} → Ordinal.{0}} {l0 l1 : Ordinal.{0}}
    (e0 : Nc.ncL S ω = upsilon l0) (e1 : Nc.ncL S (ω + 1) = upsilon l1) (Sp : YsSpec O l0 l1)
    (hO : ∀ μ, Cd.CdRange S μ → Wj.WjTop S μ → upsilon (μ + ω + 1) + O μ = Cd.cdR S μ)
    (hin : ∀ l, IsRestartIdx l → l0 < l → l < l1 →
      le1 (upsilon l) (upsilon (l + ω + 1) + O l) ∨ (cL l < 2 ∧ O l = 1) ∨
        (2 ≤ cL l ∧ 1 ≤ O l ∧ YsRsIn O l)) :
    ∀ μ, Cd.CdRange S μ → Wj.WjTop S μ → Cd.CdUpper S μ ∧ Cd.CdLower S μ := by
  intro μ hr hw
  have h0 : upsilon l0 < upsilon μ := e0 ▸ hw.1
  have h1 : upsilon μ < upsilon l1 := e1 ▸ hw.2
  obtain ⟨i0, i1⟩ := ysIdx_win h0 h1
  refine ⟨ysTop_upper e0 e1 Sp hO μ hr hw, ?_⟩
  unfold Cd.CdLower
  rw [← hO μ hr hw]
  exact ysRs_all Sp hin μ hr.1 i0 i1

/-! ## The window statements with the predicted reach as the bound -/

/-- **The bound of the window induction**: `O(μ) = r(μ) − δ_μ`, so `δ_μ + O(μ) = r(μ)` (`R2.Cd.cdR_ge`). -/
noncomputable def ysO (S : InaccSeq.{0}) (μ : Ordinal.{0}) : Ordinal.{0} :=
  Cd.cdR S μ - upsilon (μ + ω + 1)

theorem ysO_eq (S : InaccSeq.{0}) (μ : Ordinal.{0}) : upsilon (μ + ω + 1) + ysO S μ = Cd.cdR S μ :=
  Ordinal.add_sub_cancel_of_le (Cd.cdR_ge S μ)

/-- **UPPER ∧ LOWER at every range restart of `W_k`** from the relative block induction on
`[ι(Ω_ω + P′·k), ι(Ω_ω + P′·(k+1)))` with a bound `O` equal to `ysO` above the base (the bound at the base
restart `L(k)` itself is free: it only enters Lemma TOP at `L(k)`) and the RS input at its restarts. -/
theorem ysWin_UL (k : ℕ) {O : Ordinal.{0} → Ordinal.{0}}
    (hO : ∀ μ, Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < μ → O μ = ysO S μ)
    (Sp : YsSpec O (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
      (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))))
    (hin : ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) →
      le1 (upsilon l) (upsilon (l + ω + 1) + O l) ∨ (cL l < 2 ∧ O l = 1) ∨
        (2 ≤ cL l ∧ 1 ≤ O l ∧ YsRsIn O l)) :
    ∀ μ, Cd.CdRange S μ → Wj.WjWin S k μ → Cd.CdUpper S μ ∧ Cd.CdLower S μ := by
  refine ysWin_lower k (Pp.ppL_eq_ups (S := S) _) (Pp.ppL_eq_ups (S := S) _) Sp ?_ hin
  intro μ _ hw
  have h0 := hw.1
  rw [Pp.ppL_eq_ups (S := S)] at h0
  rw [hO μ (upsilon_normal.strictMono.lt_iff_lt.1 h0)]
  exact ysO_eq S μ

/-- **UPPER ∧ LOWER at every range restart of `W_ω`** from the relative block induction on
`[ι(Ω_ω + P′·ω), ι(Ω_ω + P′·(ω+1)))` (bound `O = ysO` above the base). -/
theorem ysTop_UL {O : Ordinal.{0} → Ordinal.{0}}
    (hO : ∀ μ, Bt.iota S (Om ω + Nc.ncPp S * ω) < μ → O μ = ysO S μ)
    (Sp : YsSpec O (Bt.iota S (Om ω + Nc.ncPp S * ω)) (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))))
    (hin : ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * ω) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * (ω + 1)) →
      le1 (upsilon l) (upsilon (l + ω + 1) + O l) ∨ (cL l < 2 ∧ O l = 1) ∨
        (2 ≤ cL l ∧ 1 ≤ O l ∧ YsRsIn O l)) :
    ∀ μ, Cd.CdRange S μ → Wj.WjTop S μ → Cd.CdUpper S μ ∧ Cd.CdLower S μ := by
  refine ysTop_lower (Pp.ppL_eq_ups (S := S) _) (Pp.ppL_eq_ups (S := S) _) Sp ?_ hin
  intro μ _ hw
  have h0 := hw.1
  rw [Pp.ppL_eq_ups (S := S)] at h0
  rw [hO μ (upsilon_normal.strictMono.lt_iff_lt.1 h0)]
  exact ysO_eq S μ

/-! ## No pair from the base across the window, and the milestone `L(ω+1) ≤ ν_C` -/

/-- **No `<₂`-pair from a point `≤ ρ_{l₀}` ends inside the window**: under `Ys.YsSpec O l₀ B` every pair with
right end in `(ρ_{l₀}, υ_B)` is a block pair `υ_{μ+ω(j+1)} <₂ υ_{μ+ω(j+1)+1}` with `ρ_{l₀} ≤ ρ_μ`. -/
theorem ysNoPair_base {O : Ordinal.{0} → Ordinal.{0}} {l0 B : Ordinal.{0}} (Sp : YsSpec O l0 B) :
    ∀ c ≤ upsilon l0, ∀ d, upsilon l0 < d → d < upsilon B → ¬ le2 c d := by
  intro c hc d hd hdB h2
  have hcd : c < d := lt_of_le_of_lt hc hd
  obtain ⟨μ, j, -, -, haμ, rfl, -⟩ := ((ysGood_B Sp).pairs c d hcd hd hdB).1 h2
  have : upsilon μ < upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) :=
    upsilon_normal.strictMono (lt_add_of_pos_right μ (mul_pos omega0_pos (by exact_mod_cast Nat.succ_pos j)))
  exact absurd (haμ.trans_lt this) (not_lt.2 hc)

/-- **`RgLwPair` from the relative block induction across the top window** (any bound `O`): no
`L(ω) <₂ d` with `d ∈ (L(ω), L(ω+1))`. -/
theorem ysLwPair {O : Ordinal.{0} → Ordinal.{0}}
    (Sp : YsSpec O (Bt.iota S (Om ω + Nc.ncPp S * ω)) (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1)))) :
    Rg.RgLwPair S := by
  intro d h1 h2 h2' _
  rw [Pp.ppL_eq_ups (S := S) ω] at h1 h2'
  rw [Pp.ppL_eq_ups (S := S) (ω + 1)] at h2
  exact ysNoPair_base Sp _ le_rfl d h1 h2 h2'

/-- **The milestone `L(ω+1) ≤ ν_C` from the relative block induction across the top window**, with UPPER and
CapV at the range restarts (the hypotheses of `Rg.rgNu`). -/
theorem ysNu {O : Ordinal.{0} → Ordinal.{0}}
    (Sp : YsSpec O (Bt.iota S (Om ω + Nc.ncPp S * ω)) (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))))
    (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hVt : ∀ l, Cd.CdRange S l → Nc.ncL S ω < upsilon l → Cd.CdCapV S l) :
    Nc.ncL S (ω + 1) ≤ nuC :=
  Rg.rgNu hU hV hVt (ysLwPair Sp)

end Googology.Trans.PoR.InaccPsi.R2.Ys

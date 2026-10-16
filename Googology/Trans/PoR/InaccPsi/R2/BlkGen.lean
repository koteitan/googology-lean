import Googology.Trans.PoR.InaccPsi.R2.BlkE

/-!
# Theorem BLK^O for an offset given by any terms with Lemma RS

The block theorem of `R2.BlkE` with the input of Lemma RS stated for a term *function* `T` that comes
with its own Lemma RS (`RsStep`), instead of a term of a fixed syntax.  So a new kind of offset term
only has to supply its IMG package (for Lemma TOP, `TopInH`) and its Lemma RS (`RsStep`); the block
induction is done once.

* `RsStep`, `RsInGen`, `OffSpecGen`;
* `good_allGen`, `good_BGen`, `rstGen`, `rs_allGen` (**Lemma RS_λ**), `reach_allGen` (`lh(ρ_λ) = δ_λ + O(λ)`),
  `blk_genGen` (**Theorem BLK^O below `υ_B`** for every general specification), `core_genGen`
  (`[0, υ_B) ⊆ Core(R₂^C)`, [C09] Theorem 14.14);
* `OffSpecE.toG` (the specification of stage 7 is a general one: `rs_rstT`, `rs_rstE`);
* `left_ge_of_spec` (**the left end `ρ_L` of the first non-standard pair lies at or above `υ_B`**: a
  restart below `B` has no `<₂`-successor).

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order OT OTE

/-- **Lemma RS for the term function `T` at the restart index `λ`**: if restarts `ρ_μ` with
`ρ_μ ≤₁ δ_μ + T(ρ_μ)` lie above every `κ' < ρ_λ` (with `δ_μ < ρ_λ`), then
`ρ_λ ≤₁ δ_λ + T(ρ_λ) + 1`. -/
def RsStep (l : Ordinal.{0}) (T : Ordinal.{0} → Ordinal.{0}) : Prop :=
  RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1)) →
  (∀ κ' < upsilon l, ∃ μ, κ' < upsilon μ ∧ upsilon (μ + ω + 1) < upsilon l ∧
      RstK (upsilon μ) (upsilon (μ + ω)) (upsilon (μ + ω + 1)) ∧
      ∀ g, upsilon μ ≤ g → g ≤ upsilon (μ + ω + 1) + T (upsilon μ) → le1 (upsilon μ) g) →
  le1 (upsilon l) (upsilon (l + ω + 1) + T (upsilon l) + 1)

/-- **The input of Lemma RS at a limit restart index `λ`**, general form: every `z < O(λ)` is at most
`T(ρ_λ)` for a term function `T` with Lemma RS at `λ`, realized by restarts cofinal below `λ`. -/
def RsInGen (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : Prop :=
  ∀ z < O l, ∃ T : Ordinal.{0} → Ordinal.{0}, z ≤ T (upsilon l) ∧ RsStep l T ∧
    ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ T (upsilon μ) ≤ O μ

/-- **A general offset specification up to `B`**. -/
structure OffSpecGen (O : Ordinal.{0} → Ordinal.{0}) (B : Ordinal.{0}) : Prop where
  mult : ω * ω ∣ B
  cnt : B < Om1
  le : ∀ l, IsRestartIdx l → l < B → O l < upsilon (l + ω + 1)
  one : ∀ l, IsRestartIdx l → l < B → 1 ≤ O l
  top : ∀ l, IsRestartIdx l → l < B → TopInH O l
  succ : ∀ l, IsRestartIdx l → l < B → cL l < 2 → O l = 1
  rs : ∀ l, IsRestartIdx l → l < B → 2 ≤ cL l → RsInGen O l

/-- **The block structure below `υ_B`** (FRAG-free): `Good O (ω²·η)` for every `ω²·η ≤ B`. -/
theorem good_allGen {O : Ordinal.{0} → Ordinal.{0}} {B : Ordinal.{0}} (S : OffSpecGen O B) :
    ∀ η, ω * ω * η ≤ B → Good O (ω * ω * η) := by
  have hww : 0 < ω * ω := mul_pos omega0_pos omega0_pos
  intro η
  induction η using WellFoundedLT.induction with
  | ind η IH =>
  intro hη
  rcases zero_or_succ_or_isSuccLimit η with rfl | ⟨η', rfl⟩ | hlim
  · rw [mul_zero]; exact good_zero O
  · have IH' := IH η' (lt_succ η')
    rw [succ_eq_add_one, mul_add_one] at hη ⊢
    have Gη' := IH' (le_self_add.trans hη)
    rcases eq_or_ne η' 0 with rfl | hη0
    · rw [mul_zero]; exact good_first O
    · have hl : IsRestartIdx (ω * ω * η') :=
        ri_iff.2 ⟨(mul_pos hww (pos_iff_ne_zero.2 hη0)).ne', dvd_mul_right _ _⟩
      have hlB : ω * ω * η' < B := lt_of_lt_of_le (lt_add_of_pos_right _ hww) hη
      exact good_stepH hl (S.top _ hl hlB) (S.le _ hl hlB) Gη' (lt_of_le_of_lt hη S.cnt)
  · exact good_limit hlim (fun η' hη' =>
      IH η' hη' (le_trans (mul_le_mul_right hη'.le _) hη))

theorem good_BGen {O : Ordinal.{0} → Ordinal.{0}} {B : Ordinal.{0}} (S : OffSpecGen O B) : Good O B := by
  obtain ⟨ξ, hξ⟩ := S.mult
  rw [hξ]; exact good_allGen S ξ (hξ ▸ le_rfl)

section SpecG

variable {O : Ordinal.{0} → Ordinal.{0}} {B : Ordinal.{0}} (S : OffSpecGen O B)
include S

theorem rstGen {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < B) :
    RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1)) ∧
    (∀ g, upsilon (l + ω + 1) + O l < g → ¬ le1 (upsilon l) g) ∧
    (∀ j : ℕ, BlkCtx (topA (l + ω) (upsilon (l + ω + 1) + O l) j) (lpA (l + ω) j)
      (topA (l + ω) (upsilon (l + ω + 1) + O l) (j + 1))) :=
  (good_BGen S).rst l hl hlB

/-- **Lemma RS_λ** in `R₂^C`: `ρ_λ ≤₁ δ_λ + O(λ)` for every restart index `λ < B`. -/
theorem rs_allGen : ∀ l, IsRestartIdx l → l < B →
    le1 (upsilon l) (upsilon (l + ω + 1) + O l) := by
  intro l
  induction l using WellFoundedLT.induction with
  | ind l IH =>
  intro hl hlB
  obtain ⟨R, htop, -⟩ := rstGen S hl hlB
  rcases lt_or_ge (cL l) 2 with h2 | h2
  · -- a successor restart index: Lemma RS with a block target
    rw [S.succ l hl hlB h2]
    obtain ⟨l0, hl0', rfl⟩ := succ_ri hl h2
    rcases hl0' with rfl | hl0r
    · have RC := rst_of_chain ctx0 T3_zero (by rw [upsilon_zero]) rfl R.δ1
      refine rs_gen RC ?_
      have := target_of_chain ctx0 (by rw [upsilon_zero] : upsilon 0 ≤ (0 : Ordinal.{0}))
      exact this
    · have hl0B : l0 < B := lt_of_le_of_lt le_self_add hlB
      obtain ⟨R0, htop0, C0⟩ := rstGen S hl0r hl0B
      have hT3 := R0.T3off (S.le l0 hl0r hl0B) htop0
      have hTa : upsilon (l0 + ω) ≤ upsilon (l0 + ω + 1) + O l0 :=
        R0.next.1.le.trans le_self_add
      have hr : l0 + ω + ω * ω = l0 + ω * ω := by rw [add_assoc, w_add_ww]
      have RC := rst_of_chain C0 hT3 hTa hr R.δ1
      refine rs_gen RC ?_
      have := target_of_chain C0 hTa
      rwa [hr] at this
  · -- a limit restart index: restart targets
    have hRs := S.rs l hl hlB h2
    have hlim : IsSuccLimit l := by
      obtain ⟨q, hq⟩ := (ri_iff.1 hl).2
      have hq0 : q ≠ 0 := by intro h0; rw [h0, mul_zero] at hq; exact hl.1 hq
      rw [hq]
      exact isSuccLimit_mul_left (isSuccLimit_mul_right omega0_pos isSuccLimit_omega0)
        (pos_iff_ne_zero.2 hq0)
    have hstep : ∀ z < O l, le1 (upsilon l) (upsilon (l + ω + 1) + z + 1) := by
      intro z hz
      obtain ⟨T, hzu, hRS, hcof⟩ := hRs z hz
      have htg : ∀ κ' < upsilon l, ∃ μ, κ' < upsilon μ ∧ upsilon (μ + ω + 1) < upsilon l ∧
          RstK (upsilon μ) (upsilon (μ + ω)) (upsilon (μ + ω + 1)) ∧
          ∀ g, upsilon μ ≤ g → g ≤ upsilon (μ + ω + 1) + T (upsilon μ) →
            le1 (upsilon μ) g := by
        intro κ' hκ'
        obtain ⟨_, ⟨ι, hι, rfl⟩, hκι⟩ := (lt_isLUB_iff (upsilon_limit hlim)).1 hκ'
        obtain ⟨μ, hμ, hιμ, hμl, htv⟩ := hcof ι hι
        have hμB : μ < B := hμl.trans hlB
        obtain ⟨Rμ, -, -⟩ := rstGen S hμ hμB
        have hrsμ := IH μ hμl hμ hμB
        refine ⟨μ, hκι.trans (upsilon_normal.strictMono hιμ), ?_, Rμ, fun g hg1 hg2 =>
          le1_of_le_of_le1 hg1 (hg2.trans (add_le_add le_rfl htv)) hrsμ⟩
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
    · exact absurd h0 (ne_of_gt (lt_of_lt_of_le zero_lt_one (S.one l hl hlB)))
    · rw [← hz0, succ_eq_add_one, ← add_assoc]
      exact hstep z0 (by rw [← hz0]; exact lt_succ z0)
    · exact le1_limit (isSuccLimit_add _ hlimo)
        (lt_of_lt_of_le hρδ le_self_add) (fun b' hb1 hb2 => hall b' hb1 hb2)

/-- **The exact reach of every restart below `B`** in `R₂^C`: `lh(ρ_λ) = δ_λ + O(λ)`. -/
theorem reach_allGen {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < B) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + O l) :=
  ⟨rs_allGen S l hl hlB, fun g hg => not_lt.1 (fun h => (rstGen S hl hlB).2.1 g h hg)⟩

/-- **The block theorem below `υ_B`** for a general specification. -/
theorem blk_genGen :
    (∀ c d, c < d → d < upsilon B → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < B ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < B →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + O l)) ∧
    (∀ α < upsilon B, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) := by
  refine ⟨fun c d hcd hd => (good_BGen S).pairs c d hcd hd, fun l hl hlB => ?_, (good_BGen S).sk⟩
  obtain ⟨R, -, -⟩ := rstGen S hl hlB
  exact ⟨R.below, R.noSucc, reach_allGen S hl hlB⟩

end SpecG

/-- **CORE-C for a general specification**: `[0, υ_B) ⊆ Core(R₂^C)` ([C09] Theorem 14.14). -/
theorem core_genGen {O : Ordinal.{0} → Ordinal.{0}} {B : Ordinal.{0}} (S : OffSpecGen O B) :
    Set.Iio (upsilon B) ⊆ Core R2C := by
  intro x hx
  have hno : ∀ κ < upsilon B, ¬ LeInfC κ := fun κ hκ h =>
    (good_BGen S).below κ hκ (upsilon B) le_rfl (h _ hκ.le)
  by_cases hex : ∃ κ, LeInfC κ
  · obtain ⟨κ, hκ⟩ := exists_isLeast_leInfC hex
    rw [C09_thm14_14.1 κ hκ]
    exact lt_of_lt_of_le hx (not_lt.1 (fun h => hno κ h hκ.1))
  · rw [C09_thm14_14.2 hex]; trivial

/-- The stage-7 specification (`OT` and `ε_{x+1} + t`) is a general one. -/
theorem OffSpecE.toG {O : Ordinal.{0} → Ordinal.{0}} {B : Ordinal.{0}} (S : OffSpecE O B) :
    OffSpecGen O B where
  mult := S.mult
  cnt := S.cnt
  le := S.le
  one := S.one
  top := S.top
  succ := S.succ
  rs := fun l hl hlB h2 z hz => by
    obtain ⟨u, hCB, hzu, hcof⟩ := S.rs l hl hlB h2 z hz
    refine ⟨evE u, hzu, fun R htg => ?_, hcof⟩
    cases u with
    | ot t => exact rs_rstT R hCB htg
    | e t => exact rs_rstE R hCB htg

/-- **The left end of the first non-standard pair lies at or above `υ_B`** for every general
specification up to `B`: a restart `ρ_λ`, `λ < B`, has no `<₂`-successor. -/
theorem left_ge_of_spec {O : Ordinal.{0} → Ordinal.{0}} {B : Ordinal.{0}} (S : OffSpecGen O B)
    {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlν : upsilon l < nuC) (h2 : le2 (upsilon l) nuC) :
    B ≤ l := by
  by_contra hlt
  push Not at hlt
  exact ((blk_genGen S).2.1 l hl hlt).2.1 nuC hlν h2

end Googology.Trans.PoR.InaccPsi.R2

import Googology.Trans.PoR.InaccPsi.R2.ORecE

/-!
# Theorem BLK^O with the term `ε_{x+1}`, up to `Λ_{ε·2}`

The inputs of Lemmas TOP and RS for the recursive offset `OrecE` (terms of `OT` and `ε_{x+1} + t`), and
the block theorem of `R2.BlkO` with them: Lemma TOP from an IMG package (`RstK.top_pkg`: `RstK.pkg_ot`,
`RstK.pkg_eN`, `RstK.pkg_eNt`, `RstK.pkg_eN2`), Lemma RS with a restart target (`rs_rstT` for the
terms of `OT`, `rs_rstE` for `ε_{x+1} + t`).

* `topIn_OrecE` (the input of TOP at every restart index below which `ε_{x+1}·2` is not realized
  cofinally), `RsInE`, `rsIn_OrecE`, `OffSpecE`, `specE`;
* `good_allE`, `good_BE`, `rstE`, `rs_allE`, `reach_allE`, `blk_genE`, `core_genE`;
* `blkE` (**Theorem BLK^O with `OrecE` below `υ_B` for every `B ≤ Λ_{ε·2}`**, `ω² ∣ B`, `B < Ω₁`),
  `reach_OrecE`, `coreE`;
* `LamE2_lt_Om1` (`Λ_{ε·2} < Ω₁`, with [C09] Cor 15.15), `LamE1_lt_LamE2`, `blkE_LamE2`, `coreE_LamE2`;
* `reach_LamE` (`lh(ρ_{Λ_ε}) = δ + ε_{ρ+1} + 1`);
* `OrecD_le`, `OrecD_eq_OrecE` (the paper's `O` equals `OrecE` below `Λ_{ε+1}`), `OrecE_LamE1`,
  `reach_LamE1` (`lh(ρ_{Λ_{ε+1}}) = δ + OrecE(Λ_{ε+1}) ≥ δ + ε_{ρ+1} + 2 > δ + O_paper(Λ_{ε+1})`).

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order OT OTE

/-! ## The input of Lemma TOP -/

/-- **The input of Lemma TOP** at a restart index `λ` below which `ε_{x+1}·2` is not realized
cofinally. -/
theorem topIn_OrecE {l : Ordinal.{0}} (hl : IsRestartIdx l) (hE : ¬ CofE2 OrecE l) :
    TopInH OrecE l := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρU := upsPt_upsilon hl0
  have hρE : InE (upsilon l) := upsPt_inE hρU
  have hle : OrecE l ≤ eN (upsilon l) + eN (upsilon l) := OrecS_le SF l
  have hone : 1 ≤ OrecE l := one_le_OrecS SF l
  -- a term not realized cofinally gives the bound below `λ`
  have notcof : ∀ u, CBE u (upsilon l) → OrecE l = evE u (upsilon l) →
      ¬ CofRealE OrecE l u := fun u hCB hev hc =>
    absurd (lt_OrecS_of_cof (S := SF) trivial hCB hc) (by
      show ¬ evE u (upsilon l) < OrecE l
      rw [hev]; exact lt_irrefl _)
  rcases lt_or_ge (OrecE l) (eN (upsilon l)) with hlt | hge
  · -- a term of `OT`
    obtain ⟨t0, hCB, hev⟩ := rep hρE (OrecE l) hlt
    have hnot := notcof (ot t0) hCB hev.symm
    unfold CofRealE at hnot
    push Not at hnot
    obtain ⟨ν, hνl, hν⟩ := hnot
    obtain ⟨m, hm, hmc⟩ := cmax t0 _ hCB hρU.1
    have hνρ : upsilon ν < upsilon l := upsilon_normal.strictMono hνl
    refine ⟨ev t0, max (upsilon ν) m, hev.symm, max_lt hνρ hm, fun μ hμ hμl hx0 => ?_,
      fun R => R.pkg_ot hCB (by rw [hev]; exact hone)⟩
    have hνμ : ν < μ := upsilon_normal.strictMono.lt_iff_lt.1 (lt_of_le_of_lt (le_max_left _ _) hx0)
    have hCBμ : CB t0 (upsilon μ) :=
      (cb_iff t0 _).2 (fun c hc => lt_of_le_of_lt ((hmc c hc).trans (le_max_right _ _)) hx0)
    exact hν μ hμ hνμ hμl hCBμ
  rcases hle.lt_or_eq with hlt2 | heq2
  · -- `ε_{x+1} + v`, `v < ε_{x+1}`
    set v := OrecE l - eN (upsilon l) with hvdef
    have hv : eN (upsilon l) + v = OrecE l := Ordinal.add_sub_cancel_of_le hge
    have hvlt : v < eN (upsilon l) := by
      rw [← hv] at hlt2; exact (add_lt_add_iff_left _).1 hlt2
    rcases eq_or_ne v 0 with hv0 | hv0
    · -- `O(λ) = ε_{ρ+1}`: the term `ε_{x+1} + 0`
      have hO : OrecE l = eN (upsilon l) := by rw [← hv, hv0, add_zero]
      have hnot := notcof (e (k 0)) hρU.1 (by rw [evE_e, ev_k, add_zero, hO])
      unfold CofRealE at hnot
      push Not at hnot
      obtain ⟨ν, hνl, hν⟩ := hnot
      have hνρ : upsilon ν < upsilon l := upsilon_normal.strictMono hνl
      refine ⟨eN, upsilon ν, hO, hνρ, fun μ hμ hμl hx0 => ?_, fun R => R.pkg_eN⟩
      have hνμ : ν < μ := upsilon_normal.strictMono.lt_iff_lt.1 hx0
      have := hν μ hμ hνμ hμl (upsPt_upsilon (pos_iff_ne_zero.2 hμ.1)).1
      simpa using this
    · obtain ⟨t0, hCB, hev⟩ := rep hρE v hvlt
      have hnot := notcof (e t0) hCB (by rw [evE_e, hev, hv])
      unfold CofRealE at hnot
      push Not at hnot
      obtain ⟨ν, hνl, hν⟩ := hnot
      obtain ⟨m, hm, hmc⟩ := cmax t0 _ hCB hρU.1
      have hνρ : upsilon ν < upsilon l := upsilon_normal.strictMono hνl
      refine ⟨fun x => eN x + ev t0 x, max (upsilon ν) m, by show _ = eN _ + _; rw [hev, hv], max_lt hνρ hm,
        fun μ hμ hμl hx0 => ?_,
        fun R => R.pkg_eNt hCB (by rw [hev]; exact one_le_iff_ne_zero.2 hv0)⟩
      have hνμ : ν < μ :=
        upsilon_normal.strictMono.lt_iff_lt.1 (lt_of_le_of_lt (le_max_left _ _) hx0)
      have hCBμ : CB t0 (upsilon μ) :=
        (cb_iff t0 _).2 (fun c hc => lt_of_le_of_lt ((hmc c hc).trans (le_max_right _ _)) hx0)
      exact hν μ hμ hνμ hμl hCBμ
  · -- `O(λ) = ε_{ρ+1}·2`
    unfold CofE2 at hE
    push Not at hE
    obtain ⟨ν, hνl, hν⟩ := hE
    refine ⟨fun x => eN x + eN x, upsilon ν, heq2, upsilon_normal.strictMono hνl,
      fun μ hμ hμl hx0 => hν μ hμ (upsilon_normal.strictMono.lt_iff_lt.1 hx0) hμl,
      fun R => R.pkg_eN2⟩

/-! ## The input of Lemma RS -/

/-- **The input of Lemma RS at a limit restart index `λ`** with the terms of `OTE`. -/
def RsInE (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : Prop :=
  ∀ z < O l, ∃ u : OTE, CBE u (upsilon l) ∧ z ≤ evE u (upsilon l) ∧
    ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ evE u (upsilon μ) ≤ O μ

theorem rsIn_OrecE {l : Ordinal.{0}} (hl : IsRestartIdx l) (h2 : 2 ≤ cL l) : RsInE OrecE l := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρ0 : 0 < upsilon l := (upsPt_upsilon hl0).1
  intro z hz
  rcases lt_OrecS (S := SF) hz with rfl | ⟨u, -, hCB, hc, hzu⟩
  · refine ⟨ot (k 0), hρ0, zero_le, fun ν hν => ?_⟩
    obtain ⟨μ, hμ, h1, h3, -⟩ := cL_dense hl le_rfl (lt_of_lt_of_le one_lt_two h2) ν hν
    exact ⟨μ, hμ, h1, h3, zero_le⟩
  · refine ⟨u, hCB, hzu, fun ν hν => ?_⟩
    obtain ⟨μ, hμ, h1, h3, -, h5⟩ := hc ν hν
    exact ⟨μ, hμ, h1, h3, h5⟩

/-- **An offset specification up to `B`** with the terms of `OTE`. -/
structure OffSpecE (O : Ordinal.{0} → Ordinal.{0}) (B : Ordinal.{0}) : Prop where
  mult : ω * ω ∣ B
  cnt : B < Om1
  le : ∀ l, IsRestartIdx l → l < B → O l < upsilon (l + ω + 1)
  one : ∀ l, IsRestartIdx l → l < B → 1 ≤ O l
  top : ∀ l, IsRestartIdx l → l < B → TopInH O l
  succ : ∀ l, IsRestartIdx l → l < B → cL l < 2 → O l = 1
  rs : ∀ l, IsRestartIdx l → l < B → 2 ≤ cL l → RsInE O l

theorem OrecE_lt_δ {l : Ordinal.{0}} (hl : IsRestartIdx l) : OrecE l < upsilon (l + ω + 1) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have h1 : upsilon l < upsilon (l + ω) :=
    upsilon_normal.strictMono (lt_add_of_pos_right l omega0_pos)
  have h2 : upsilon (l + ω) < upsilon (l + ω + 1) := upsilon_normal.strictMono (lt_add_one _)
  have hτE : InE (upsilon (l + ω)) := upsPt_inE (upsPt_upsilon (lt_of_lt_of_le hl0 le_self_add))
  have hδI : Indec (upsilon (l + ω + 1)) :=
    inE_indec (upsPt_inE (upsPt_upsilon (lt_of_lt_of_le hl0 (le_self_add.trans le_self_add))))
  have he : eN (upsilon l) < upsilon (l + ω + 1) := lt_of_le_of_lt (eN_le h1 hτE) h2
  exact lt_of_le_of_lt (OrecS_le SF l) (hδI.add_lt he he)

/-- **`OrecE` is an offset specification up to `B`** when `ε_{x+1}·2` is realized cofinally below no
restart index below `B`. -/
theorem specE {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1)
    (hB : ∀ l, IsRestartIdx l → l < B → ¬ CofE2 OrecE l) : OffSpecE OrecE B where
  mult := hm
  cnt := hc
  le := fun _ hl _ => OrecE_lt_δ hl
  one := fun l _ _ => one_le_OrecS SF l
  top := fun l hl hlB => topIn_OrecE hl (hB l hl hlB)
  succ := fun _ hl _ h2 => OrecS_succ SF hl h2
  rs := fun _ hl _ h2 => rsIn_OrecE hl h2

theorem specE_of_le {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ LamE2) :
    OffSpecE OrecE B :=
  specE hm hc (fun _ hl hlB => not_cofE2_of_lt hl (lt_of_lt_of_le hlB hB))

/-! ## The block theorem for an `OTE` specification -/

/-- **The block structure below `υ_B`** (FRAG-free): `Good O (ω²·η)` for every `ω²·η ≤ B`. -/
theorem good_allE {O : Ordinal.{0} → Ordinal.{0}} {B : Ordinal.{0}} (S : OffSpecE O B) :
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

theorem good_BE {O : Ordinal.{0} → Ordinal.{0}} {B : Ordinal.{0}} (S : OffSpecE O B) : Good O B := by
  obtain ⟨ξ, hξ⟩ := S.mult
  rw [hξ]; exact good_allE S ξ (hξ ▸ le_rfl)

section SpecE

variable {O : Ordinal.{0} → Ordinal.{0}} {B : Ordinal.{0}} (S : OffSpecE O B)
include S

theorem rstE {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < B) :
    RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1)) ∧
    (∀ g, upsilon (l + ω + 1) + O l < g → ¬ le1 (upsilon l) g) ∧
    (∀ j : ℕ, BlkCtx (topA (l + ω) (upsilon (l + ω + 1) + O l) j) (lpA (l + ω) j)
      (topA (l + ω) (upsilon (l + ω + 1) + O l) (j + 1))) :=
  (good_BE S).rst l hl hlB

/-- **Lemma RS_λ** in `R₂^C`: `ρ_λ ≤₁ δ_λ + O(λ)` for every restart index `λ < B`. -/
theorem rs_allE : ∀ l, IsRestartIdx l → l < B →
    le1 (upsilon l) (upsilon (l + ω + 1) + O l) := by
  intro l
  induction l using WellFoundedLT.induction with
  | ind l IH =>
  intro hl hlB
  obtain ⟨R, htop, -⟩ := rstE S hl hlB
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
      obtain ⟨R0, htop0, C0⟩ := rstE S hl0r hl0B
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
      obtain ⟨u, hCB, hzu, hcof⟩ := hRs z hz
      have htg : ∀ κ' < upsilon l, ∃ μ, κ' < upsilon μ ∧ upsilon (μ + ω + 1) < upsilon l ∧
          RstK (upsilon μ) (upsilon (μ + ω)) (upsilon (μ + ω + 1)) ∧
          ∀ g, upsilon μ ≤ g → g ≤ upsilon (μ + ω + 1) + evE u (upsilon μ) →
            le1 (upsilon μ) g := by
        intro κ' hκ'
        obtain ⟨_, ⟨ι, hι, rfl⟩, hκι⟩ := (lt_isLUB_iff (upsilon_limit hlim)).1 hκ'
        obtain ⟨μ, hμ, hιμ, hμl, htv⟩ := hcof ι hι
        have hμB : μ < B := hμl.trans hlB
        obtain ⟨Rμ, -, -⟩ := rstE S hμ hμB
        have hrsμ := IH μ hμl hμ hμB
        refine ⟨μ, hκι.trans (upsilon_normal.strictMono hιμ), ?_, Rμ, fun g hg1 hg2 =>
          le1_of_le_of_le1 hg1 (hg2.trans (add_le_add le_rfl htv)) hrsμ⟩
        exact upsilon_normal.strictMono (lt_of_lt_of_le (by simpa using idx_lt μ 0 1)
          (next_mult (ri_iff.1 hμ).2 (ri_iff.1 hl).2 hμl))
      refine le1_of_le_of_le1 (R.ρδ.le.trans (le_self_add.trans le_self_add))
        (add_le_add (add_le_add le_rfl hzu) le_rfl) ?_
      cases u with
      | ot t => exact rs_rstT R hCB htg
      | e t => exact rs_rstE R hCB htg
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
theorem reach_allE {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < B) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + O l) :=
  ⟨rs_allE S l hl hlB, fun g hg => not_lt.1 (fun h => (rstE S hl hlB).2.1 g h hg)⟩

/-- **The block theorem below `υ_B`** for an `OTE` specification. -/
theorem blk_genE :
    (∀ c d, c < d → d < upsilon B → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < B ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < B →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + O l)) ∧
    (∀ α < upsilon B, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) := by
  refine ⟨fun c d hcd hd => (good_BE S).pairs c d hcd hd, fun l hl hlB => ?_, (good_BE S).sk⟩
  obtain ⟨R, -, -⟩ := rstE S hl hlB
  exact ⟨R.below, R.noSucc, reach_allE S hl hlB⟩

end SpecE

/-- **CORE-C for an `OTE` specification**: `[0, υ_B) ⊆ Core(R₂^C)` ([C09] Theorem 14.14). -/
theorem core_genE {O : Ordinal.{0} → Ordinal.{0}} {B : Ordinal.{0}} (S : OffSpecE O B) :
    Set.Iio (upsilon B) ⊆ Core R2C := by
  intro x hx
  have hno : ∀ κ < upsilon B, ¬ LeInfC κ := fun κ hκ h =>
    (good_BE S).below κ hκ (upsilon B) le_rfl (h _ hκ.le)
  by_cases hex : ∃ κ, LeInfC κ
  · obtain ⟨κ, hκ⟩ := exists_isLeast_leInfC hex
    rw [C09_thm14_14.1 κ hκ]
    exact lt_of_lt_of_le hx (not_lt.1 (fun h => hno κ h hκ.1))
  · rw [C09_thm14_14.2 hex]; trivial

/-! ## `OrecE`: the block theorem up to `Λ_{ε·2}` -/

/-- **Theorem BLK^O with `OrecE` below `υ_B` for every `B ≤ Λ_{ε·2}`** (`ω² ∣ B`, `B < Ω₁`) in
`R₂^C`: (i) the `<₂`-pairs with right end below `υ_B` are the standard pairs; (ii) every restart
`ρ_λ` (`λ < B`) has no `<₁`-predecessor, no `<₂`-successor, and reach `δ_λ + OrecE(λ)`; (iii) every
point below `υ_B` that is not a `υ`-point has its `R₁⁺` reach. -/
theorem blkE {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ LamE2) :
    (∀ c d, c < d → d < upsilon B → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < B ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < B →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + OrecE l)) ∧
    (∀ α < upsilon B, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  blk_genE (specE_of_le hm hc hB)

/-- **CORE-C up to `Λ_{ε·2}`**: `[0, υ_B) ⊆ Core(R₂^C)` for every `B ≤ Λ_{ε·2}`. -/
theorem coreE {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ LamE2) :
    Set.Iio (upsilon B) ⊆ Core R2C :=
  core_genE (specE_of_le hm hc hB)

/-- **`Λ_{ε·2} < Ω₁`** (the core is countable, [C09] Cor 15.15). -/
theorem LamE2_lt_Om1 : LamE2 < Om1 := by
  rcases LamE2_le_Om1.lt_or_eq with h | h
  · exact h
  · exfalso
    exact not_core_all (fun B hm hc => coreE hm hc (by rw [h]; exact hc.le))

/-- **The exact reach of every restart below `Λ_{ε·2}`** in `R₂^C`: `lh(ρ_λ) = δ_λ + OrecE(λ)`. -/
theorem reach_OrecE {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlE : l < LamE2) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + OrecE l) := by
  obtain ⟨hl2, -⟩ := LamE2_spec LamE2_lt_Om1
  exact (blkE (ri_iff.1 hl2).2 LamE2_lt_Om1 le_rfl).2.1 l hl hlE |>.2.2

theorem blkE_LamE2 :
    (∀ c d, c < d → d < upsilon LamE2 → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < LamE2 ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < LamE2 →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + OrecE l)) ∧
    (∀ α < upsilon LamE2, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  blkE (ri_iff.1 (LamE2_spec LamE2_lt_Om1).1).2 LamE2_lt_Om1 le_rfl

theorem coreE_LamE2 : Set.Iio (upsilon LamE2) ⊆ Core R2C :=
  coreE (ri_iff.1 (LamE2_spec LamE2_lt_Om1).1).2 LamE2_lt_Om1 le_rfl

/-- **`Λ_{ε+1} < Λ_{ε·2}`**: a restart that realizes `ε_{x+1}·2` has `ε_{x+1} + 1` realized cofinally
below it. -/
theorem LamE1_lt_LamE2 : LamE1 < LamE2 := by
  obtain ⟨hl, hc⟩ := LamE2_spec LamE2_lt_Om1
  by_contra hle
  push Not at hle
  obtain ⟨μ, hμ, -, hμl, h4⟩ := hc 0 (pos_iff_ne_zero.2 hl.1)
  have hμ1 : μ < Om1 := hμl.trans LamE2_lt_Om1
  have h1 := cofE1_of_two hμ1 h4
  exact not_cofE1_of_lt hμ (lt_of_lt_of_le hμl hle) h1

theorem LamE1_lt_Om1 : LamE1 < Om1 := LamE1_lt_LamE2.trans LamE2_lt_Om1

theorem LamE_lt_LamE2 : LamE < LamE2 := LamE_lt_LamE1.trans LamE1_lt_LamE2

/-- **The reach at `Λ_ε`**: `lh(ρ_{Λ_ε}) = δ_{Λ_ε} + ε_{ρ+1} + 1` (`ρ = ρ_{Λ_ε}`). -/
theorem reach_LamE :
    IsReach R2C (upsilon LamE) (upsilon (LamE + ω + 1) + (eN (upsilon LamE) + 1)) := by
  rw [← OrecE_LamE]
  exact reach_OrecE LamE_spec.1 LamE_lt_LamE2

/-! ## The paper's `O` stops being the reach at `Λ_{ε+1}` -/

/-- The paper's `O` is at most `ε_{ρ+1} + 1`. -/
theorem OrecD_le (l : Ordinal.{0}) : OrecD l ≤ eN (upsilon l) + 1 := by
  show OrecS SD l ≤ _
  rw [OrecS_eq]
  refine csSup_le ⟨1, Set.mem_insert _ _⟩ ?_
  rintro w (rfl | ⟨u, hS, hCB, -, rfl⟩)
  · exact le_add_self
  cases u with
  | ot t => exact (add_one_le_of_lt (ev_lt_eN hCB)).trans le_self_add
  | e t =>
    have : t = k 0 := hS
    subst this
    simp

/-- **The paper's `O` equals `OrecE` below `Λ_{ε+1}`** (at every restart index). -/
theorem OrecD_eq_OrecE : ∀ l, IsRestartIdx l → l < LamE1 → OrecD l = OrecE l := by
  intro l
  induction l using WellFoundedLT.induction with
  | ind l IH =>
  intro hl hlE
  have hl1 : l < Om1 := hlE.trans LamE1_lt_Om1
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have key : ∀ μ, IsRestartIdx μ → μ < l → OrecS SD μ = OrecS SF μ := fun μ hμ hμl =>
    IH μ hμl hμ (hμl.trans hlE)
  have hS : OSetS SD (OrecS SD) l = OSetS SF (OrecS SF) l := by
    ext w
    simp only [OSetS, Set.mem_insert_iff, Set.mem_setOf_eq]
    constructor
    · rintro (h | ⟨u, -, hCB, hc, rfl⟩)
      · exact Or.inl h
      · refine Or.inr ⟨u, trivial, hCB, fun ν hν => ?_, rfl⟩
        obtain ⟨μ, hμ, h1, h2, h3, h4⟩ := hc ν hν
        exact ⟨μ, hμ, h1, h2, h3, by rw [← key μ hμ h2]; exact h4⟩
    · rintro (h | ⟨u, -, hCB, hc, rfl⟩)
      · exact Or.inl h
      cases u with
      | ot t =>
        refine Or.inr ⟨ot t, trivial, hCB, fun ν hν => ?_, rfl⟩
        obtain ⟨μ, hμ, h1, h2, h3, h4⟩ := hc ν hν
        exact ⟨μ, hμ, h1, h2, h3, by rw [key μ hμ h2]; exact h4⟩
      | e t =>
        have ht0 : ev t (upsilon l) = 0 := by
          by_contra hne
          have h1 : 1 ≤ ev t (upsilon l) := one_le_iff_ne_zero.2 hne
          refine not_cofE1_of_lt hl hlE (fun ν hν => ?_)
          obtain ⟨μ, hμ, h2, h3, h4, h5⟩ := hc ν hν
          have h1μ := (uni_one (Bases_ups (pos_iff_ne_zero.2 hμ.1) h3 hl1) h4).1 h1
          exact ⟨μ, hμ, h2, h3, (add_le_add le_rfl h1μ).trans h5⟩
        refine Or.inr ⟨e (k 0), rfl, (upsPt_upsilon hl0).1, fun ν hν => ?_, by
          simp [ht0]⟩
        obtain ⟨μ, hμ, h2, h3, -, h5⟩ := hc ν hν
        refine ⟨μ, hμ, h2, h3, (upsPt_upsilon (pos_iff_ne_zero.2 hμ.1)).1, ?_⟩
        rw [key μ hμ h3]
        simp only [evE_e, ev_k, add_zero]
        exact le_self_add.trans h5
  show OrecS SD l = OrecS SF l
  rw [OrecS_eq, OrecS_eq SF, hS]

/-- At `Λ_{ε+1}`: `ε_{ρ+1} + 2 ≤ OrecE(Λ_{ε+1})`. -/
theorem OrecE_LamE1 : eN (upsilon LamE1) + 1 + 1 ≤ OrecE LamE1 := by
  obtain ⟨hl, hc⟩ := LamE1_spec LamE1_lt_Om1
  have hl0 : 0 < LamE1 := pos_iff_ne_zero.2 hl.1
  have hcof : CofRealE (OrecS SF) LamE1 (e (k 1)) := by
    intro ν hν
    obtain ⟨μ, hμ, h1, h2, h3⟩ := hc ν hν
    exact ⟨μ, hμ, h1, h2, one_lt_inE (upsPt_inE (upsPt_upsilon (pos_iff_ne_zero.2 hμ.1))), h3⟩
  have := lt_OrecS_of_cof (S := SF) trivial
    (show CBE (e (k 1)) (upsilon LamE1) from one_lt_inE (upsPt_inE (upsPt_upsilon hl0))) hcof
  exact add_one_le_of_lt this

/-- **At `Λ_{ε+1}` the paper's `O` is not the reach**: `lh(ρ) = δ + OrecE(Λ_{ε+1})`, with
`OrecE(Λ_{ε+1}) ≥ ε_{ρ+1} + 2 > ε_{ρ+1} + 1 ≥ O_paper(Λ_{ε+1})` (`ρ = ρ_{Λ_{ε+1}}`). -/
theorem reach_LamE1 :
    IsReach R2C (upsilon LamE1) (upsilon (LamE1 + ω + 1) + OrecE LamE1) ∧
      OrecD LamE1 < OrecE LamE1 :=
  ⟨reach_OrecE (LamE1_spec LamE1_lt_Om1).1 LamE1_lt_LamE2,
    lt_of_le_of_lt (OrecD_le _) (lt_of_lt_of_le (lt_add_one _) OrecE_LamE1)⟩

end Googology.Trans.PoR.InaccPsi.R2

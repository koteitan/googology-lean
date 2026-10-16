import Googology.Trans.PoR.InaccPsi.R2.TopO
import Googology.Trans.PoR.InaccPsi.R2.RSO

/-!
# The block theorem for an offset specification with every offset term

As stage 5's `OffSpecG`/`good_allG`/`rs_allG`/`blk_genG`, with the inputs of Lemma TOP given by any
term `T` with an IMG package (`TopInH`: the terms of `OT` through `RstK.pkg_ot`, and `ε_{x+1}` through
`RstK.pkg_eN`) and the input of Lemma RS given by the terms of `OT` (`RsInT`).  Lemma TOP is
`RstK.top_pkg` (Lemma IMG, FRAG-free); Lemma RS is `rs_rstT` (FRAG with Lemma EXACT).

* `TopInH`, `RsInT`, `OffSpecH`; `top_of_goodH`, `good_stepH`, `good_allH`, `good_BH` (FRAG-free);
* `rstH`, `rs_allH`, `reach_allH`, `blk_genH` (the block theorem below `υ_B`), `core_genH`
  (`[0, υ_B) ⊆ Core(R₂^C)`, with [C09] Theorem 14.14).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order OT

/-- **The input of Lemma TOP at `λ`** with a term `T`: `O(λ) = T(ρ_λ)`, no restart `ρ_μ > x₀` below
`ρ_λ` realizes `T` (`O(μ) < T(ρ_μ)`), and `T` has an IMG package at `ρ_λ` (`ImgPkg`). -/
def TopInH (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : Prop :=
  ∃ (T : Ordinal.{0} → Ordinal.{0}) (x0 : Ordinal.{0}), O l = T (upsilon l) ∧ x0 < upsilon l ∧
    (∀ μ, IsRestartIdx μ → μ < l → x0 < upsilon μ → O μ < T (upsilon μ)) ∧
    (RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1)) →
      ImgPkg (upsilon l) (upsilon (l + ω + 1)) T)

/-- **The input of Lemma RS at a limit restart index `λ`**: every `z < O(λ)` is at most `t(ρ_λ)` for
a term `t` of `OT` with constants below `ρ_λ` realized by restarts cofinal below `λ`
(`t(ρ_μ) ≤ O(μ)`). -/
def RsInT (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : Prop :=
  ∀ z < O l, ∃ t : OT, CB t (upsilon l) ∧ z ≤ ev t (upsilon l) ∧
    ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ ev t (upsilon μ) ≤ O μ

/-- **An offset specification up to `B`** with the terms of this stage (as `OffSpec`). -/
structure OffSpecH (O : Ordinal.{0} → Ordinal.{0}) (B : Ordinal.{0}) : Prop where
  mult : ω * ω ∣ B
  cnt : B < Om1
  le : ∀ l, IsRestartIdx l → l < B → O l < upsilon (l + ω + 1)
  one : ∀ l, IsRestartIdx l → l < B → 1 ≤ O l
  top : ∀ l, IsRestartIdx l → l < B → TopInH O l
  succ : ∀ l, IsRestartIdx l → l < B → cL l < 2 → O l = 1
  rs : ∀ l, IsRestartIdx l → l < B → 2 ≤ cL l → RsInT O l

/-- **Lemma TOP_λ** from what is known below `ρ_λ` (`Good`) and the input `TopInH O λ`. -/
theorem top_of_goodH {O : Ordinal.{0} → Ordinal.{0}} {l : Ordinal.{0}} (hT : TopInH O l)
    (G : Good O l) (R : RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1))) :
    ∀ g, upsilon (l + ω + 1) + O l < g → ¬ le1 (upsilon l) g := by
  obtain ⟨T, x0, hoff, hx0, hreal, hpk⟩ := hT
  rw [hoff]
  refine R.top_pkg (hpk R) hx0 G.sk ?_
  intro c d _ hcd hd h2 x hx0x hxc e' he1 hte hxe
  rcases G.caps c d hcd hd h2 x hxc (d + e') hxe with hle | ⟨μ, hμ, hμl, rfl, hδd, hg⟩
  · exact absurd hle (not_le.2 (lt_add_of_pos_right d (lt_of_lt_of_le zero_lt_one he1)))
  · have hμ0 : 0 < μ := pos_iff_ne_zero.2 hμ.1
    have h1' := hreal μ hμ hμl hx0x
    have h2' := hte (upsPt_upsilon hμ0)
    have : upsilon (μ + ω + 1) + O μ < d + e' :=
      lt_of_lt_of_le ((add_lt_add_iff_left _).2 (lt_of_lt_of_le h1' h2')) (add_le_add hδd le_rfl)
    exact absurd hg (not_le.2 this)

/-- **The step at a restart `λ`** (given the input of Lemma TOP at `λ`): from `[0, ρ_λ)` to
`[0, ρ_{λ+ω²})`. -/
theorem good_stepH {O : Ordinal.{0} → Ordinal.{0}} {l : Ordinal.{0}} (hl : IsRestartIdx l)
    (hT : TopInH O l) (hO : O l < upsilon (l + ω + 1)) (G : Good O l)
    (hcnt : l + ω * ω < Om1) : Good O (l + ω * ω) := by
  have hww : 0 < ω * ω := mul_pos omega0_pos omega0_pos
  have hll : l < l + ω * ω := lt_add_of_pos_right l hww
  have hδ1 : upsilon (l + ω + 1) < Om1 :=
    ups_lt_Om1 _ (lt_of_lt_of_le (by simpa using idx_lt l 0 1) hcnt.le)
  have R := rstK_of_good hl G hδ1
  have htop := top_of_goodH hT G R
  have hoffδ := hO
  have hT3 := R.T3off hoffδ htop
  have C := chain_after hO R htop hcnt
  have hTa : upsilon (l + ω) ≤ upsilon (l + ω + 1) + O l := R.next.1.le.trans le_self_add
  have he : l + ω + ω * ω = l + ω * ω := by rw [add_assoc, w_add_ww]
  have hbelowC := chainA_below C hT3 hTa
  have hlandC := chainA_land C hTa
  rw [he] at hbelowC hlandC
  have hρc : ∀ c d, c < d → upsilon l ≤ d → le2 c d → upsilon l < c := by
    intro c d hcd hρd h2
    rcases lt_trichotomy c (upsilon l) with hcρ | e | h'
    · exact absurd (le2_le1 h2) (G.below c hcρ d hρd)
    · rw [e] at h2 hcd; exact absurd h2 (R.noSucc d hcd)
    · exact h'
  refine ⟨hbelowC, fun _ => hlandC, ?_, ?_, ?_, ?_⟩
  · -- caps
    intro c d hcd hd h2 x hxc g hg
    rcases lt_or_ge d (upsilon l) with hdρ | hρd
    · rcases G.caps c d hcd hdρ h2 x hxc g hg with h | ⟨μ, hμ, hμl, hx, hδd, hg'⟩
      · exact Or.inl h
      · exact Or.inr ⟨μ, hμ, hμl.trans hll, hx, hδd, hg'⟩
    have hρc' := hρc c d hcd hρd h2
    have hρd' : upsilon l < d := hρc'.trans hcd
    rcases lt_trichotomy d (upsilon (l + ω + 1)) with hdδ | e | hδd
    · exact absurd h2 (R.noPairGap c d hcd hρd' hdδ)
    · rw [e] at hcd ⊢
      rcases lt_trichotomy x (upsilon l) with hxρ | ex | hρx
      · exact Or.inl (le_of_lt (lt_of_lt_of_le (not_le.1 (fun h' => G.below x hxρ g h' hg))
          R.ρδ.le))
      · exact Or.inr ⟨l, hl, hll, ex, le_rfl, not_lt.1 (fun h' => htop g h' (ex ▸ hg))⟩
      · exact Or.inl (not_lt.1 (fun h' => R.capδ x hρx (hxc.trans hcd.le) g h' hg))
    · rcases le_or_gt d (upsilon (l + ω + 1) + O l) with hdT | hTd
      · exact absurd (indec_of_lt2_right h2 hcd).1 (decomp_mid hoffδ hδd hdT)
      · obtain ⟨k, -, -, hcap⟩ := chain_pair C hTa hTd (by rw [he]; exact hd) hcd h2
        exact Or.inl (hcap x (hxc.trans hcd.le) g hg)
  · -- pairs
    intro c d hcd hd
    constructor
    · intro h2
      rcases lt_or_ge d (upsilon l) with hdρ | hρd
      · obtain ⟨μ, j, hμ, hμl, hc, hd'⟩ := (G.pairs c d hcd hdρ).1 h2
        exact ⟨μ, j, hμ, hμl.trans hll, hc, hd'⟩
      have hρc' := hρc c d hcd hρd h2
      rcases lt_trichotomy d (upsilon (l + ω + 1)) with hdδ | e | hδd
      · exact absurd h2 (R.noPairGap c d hcd (hρc'.trans hcd) hdδ)
      · rw [e] at hcd h2 ⊢
        refine ⟨l, 0, Or.inr hl, hll, ?_, ?_⟩
        · rw [idx_one]; exact R.pairs_at_top hcd h2
        · rw [idx_one]
      · rcases le_or_gt d (upsilon (l + ω + 1) + O l) with hdT | hTd
        · exact absurd (indec_of_lt2_right h2 hcd).1 (decomp_mid hoffδ hδd hdT)
        · obtain ⟨k, rfl, rfl, -⟩ := chain_pair C hTa hTd (by rw [he]; exact hd) hcd h2
          refine ⟨l, k + 1, Or.inr hl, hll, ?_, ?_⟩
          · show upsilon (l + ω + ω * (k : Ordinal.{0}) + ω) = _
            rw [idx_chain]
          · show upsilon (l + ω + ω * (k : Ordinal.{0}) + ω + 1) = _
            rw [idx_chain]
    · rintro ⟨μ, j, hμ, hμl, rfl, rfl⟩
      rcases lt_trichotomy μ l with hμl' | e | hlμ
      · have hlt : upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) < upsilon l :=
          upsilon_normal.strictMono (lt_of_lt_of_le (pidx_lt μ j)
            (next_mult (mult_of hμ) (ri_iff.1 hl).2 hμl'))
        exact (G.pairs _ _ hcd hlt).2 ⟨μ, j, hμ, hμl', rfl, rfl⟩
      · rw [e]
        rcases j with _ | k
        · rw [idx_one]; exact R.pair
        · have := (C k).pair
          simp only [lpA, topA] at this
          rw [idx_chain]; exact this
      · exact absurd hμl (not_lt.2 (next_mult (ri_iff.1 hl).2 (mult_of hμ) hlμ))
  · -- skeletal
    intro α hα hnu γ
    rcases lt_or_ge α (upsilon l) with hαρ | hρα
    · exact G.sk α hαρ hnu γ
    rcases eq_or_lt_of_le hρα with e | hρα'
    · exact absurd (e ▸ R.ρU) hnu
    rcases le_or_gt α (upsilon (l + ω + 1)) with hαδ | hδα
    · exact skel_block R.next.2.1 R.δ1 hρα' hαδ hnu R.lowδ γ
    rcases le_or_gt α (upsilon (l + ω + 1) + O l) with hαT | hTα
    · exact sk_decomp (decomp_mid hoffδ hδα hαT) γ
    · exact chain_sk C hTa hTα (by rw [he]; exact hα) hnu γ
  · -- restarts
    intro μ hμ hμl
    rcases lt_trichotomy μ l with hμl' | e | hlμ
    · exact G.rst μ hμ hμl'
    · rw [e]; exact ⟨R, htop, C⟩
    · exact absurd hμl (not_lt.2 (next_mult (ri_iff.1 hl).2 (ri_iff.1 hμ).2 hlμ))


/-- **The block structure below `υ_B`** (FRAG-free): `Good O (ω²·η)` for every `ω²·η ≤ B`. -/
theorem good_allH {O : Ordinal.{0} → Ordinal.{0}} {B : Ordinal.{0}} (S : OffSpecH O B) :
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

/-- `Good O B`. -/
theorem good_BH {O : Ordinal.{0} → Ordinal.{0}} {B : Ordinal.{0}} (S : OffSpecH O B) : Good O B := by
  obtain ⟨ξ, hξ⟩ := S.mult
  rw [hξ]; exact good_allH S ξ (hξ ▸ le_rfl)


section SpecH


variable {O : Ordinal.{0} → Ordinal.{0}} {B : Ordinal.{0}} (S : OffSpecH O B)
include S

theorem lt_B_addH {μ : Ordinal.{0}} (hm : μ = 0 ∨ IsRestartIdx μ) (hμ : μ < B)
    {j : ℕ} : μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 < B :=
  lt_of_lt_of_le (pidx_lt μ j) (next_mult (mult_of hm) S.mult hμ)

/-- The restart context, Lemma TOP_λ and the chain after it, for every restart index `λ < B`. -/
theorem rstH {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < B) :
    RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1)) ∧
    (∀ g, upsilon (l + ω + 1) + O l < g → ¬ le1 (upsilon l) g) ∧
    (∀ j : ℕ, BlkCtx (topA (l + ω) (upsilon (l + ω + 1) + O l) j) (lpA (l + ω) j)
      (topA (l + ω) (upsilon (l + ω + 1) + O l) (j + 1))) :=
  (good_BH S).rst l hl hlB

/-- **Lemma RS_λ** in `R₂^C`: `ρ_λ ≤₁ δ_λ + O(λ)` for every restart index `λ < B`. -/
theorem rs_allH : ∀ l, IsRestartIdx l → l < B →
    le1 (upsilon l) (upsilon (l + ω + 1) + O l) := by
  intro l
  induction l using WellFoundedLT.induction with
  | ind l IH =>
  intro hl hlB
  obtain ⟨R, htop, -⟩ := rstH S hl hlB
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  rcases lt_or_ge (cL l) 2 with h2 | h2
  · -- a successor restart index: stage 3's Lemma RS with a block target
    rw [S.succ l hl hlB h2]
    obtain ⟨l0, hl0', rfl⟩ := succ_ri hl h2
    rcases hl0' with rfl | hl0r
    · have RC := rst_of_chain ctx0 T3_zero (by rw [upsilon_zero]) rfl R.δ1
      refine rs_gen RC ?_
      have := target_of_chain ctx0 (by rw [upsilon_zero] : upsilon 0 ≤ (0 : Ordinal.{0}))
      exact this
    · have hl0B : l0 < B := lt_of_le_of_lt le_self_add hlB
      obtain ⟨R0, htop0, C0⟩ := rstH S hl0r hl0B
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
      obtain ⟨t, hCB, hzt, hcof⟩ := hRs z hz
      refine le1_of_le_of_le1 (R.ρδ.le.trans (le_self_add.trans le_self_add))
        (add_le_add (add_le_add le_rfl hzt) le_rfl) (rs_rstT R hCB (fun κ' hκ' => ?_))
      obtain ⟨_, ⟨ι, hι, rfl⟩, hκι⟩ := (lt_isLUB_iff (upsilon_limit hlim)).1 hκ'
      obtain ⟨μ, hμ, hιμ, hμl, htv⟩ := hcof ι hι
      have hμB : μ < B := hμl.trans hlB
      obtain ⟨Rμ, -, -⟩ := rstH S hμ hμB
      have hrsμ := IH μ hμl hμ hμB
      refine ⟨μ, hκι.trans (upsilon_normal.strictMono hιμ), ?_, Rμ, fun g hg1 hg2 =>
        le1_of_le_of_le1 hg1 (hg2.trans (add_le_add le_rfl htv)) hrsμ⟩
      exact upsilon_normal.strictMono (lt_of_lt_of_le (by simpa using idx_lt μ 0 1)
        (next_mult (ri_iff.1 hμ).2 (ri_iff.1 hl).2 hμl))
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
theorem reach_allH {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < B) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + O l) :=
  ⟨rs_allH S l hl hlB, fun g hg => not_lt.1 (fun h => (rstH S hl hlB).2.1 g h hg)⟩

/-- **The block theorem below `υ_B`** for an offset specification `O` up to `B`: (i) the `<₂`-pairs
with right end below `υ_B` are exactly `(υ_{μ+ω·j}, υ_{μ+ω·j+1})`, `j ≥ 1`, `μ < B` zero or a
restart index; (ii) a restart `ρ_λ` (`λ < B`) has no `<₁`-predecessor and no `<₂`-successor, and
`{γ : ρ_λ ≤₁ γ} = [ρ_λ, δ_λ + O(λ)]`; (iii) every point below `υ_B` that is not a `υ`-point has
its `R₁⁺` reach. -/
theorem blk_genH :
    (∀ c d, c < d → d < upsilon B → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < B ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < B →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + O l)) ∧
    (∀ α < upsilon B, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) := by
  refine ⟨fun c d hcd hd => (good_BH S).pairs c d hcd hd, fun l hl hlB => ?_, (good_BH S).sk⟩
  obtain ⟨R, -, -⟩ := rstH S hl hlB
  exact ⟨R.below, R.noSucc, reach_allH S hl hlB⟩

end SpecH

/-- **CORE-C for an offset specification**: `[0, υ_B) ⊆ Core(R₂^C)` ([C09] Theorem 14.14). -/
theorem core_genH {O : Ordinal.{0} → Ordinal.{0}} {B : Ordinal.{0}} (S : OffSpecH O B) :
    Set.Iio (upsilon B) ⊆ Core R2C := by
  intro x hx
  have hno : ∀ κ < upsilon B, ¬ LeInfC κ := fun κ hκ h =>
    (good_BH S).below κ hκ (upsilon B) le_rfl (h _ hκ.le)
  by_cases hex : ∃ κ, LeInfC κ
  · obtain ⟨κ, hκ⟩ := exists_isLeast_leInfC hex
    rw [C09_thm14_14.1 κ hκ]
    exact lt_of_lt_of_le hx (not_lt.1 (fun h => hno κ h hκ.1))
  · rw [C09_thm14_14.2 hex]; trivial

end Googology.Trans.PoR.InaccPsi.R2

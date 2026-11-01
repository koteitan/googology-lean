import Googology.Trans.PoR.InaccPsi.R2.XwJump
import Googology.Trans.PoR.InaccPsi.R2.LhSk

/-!
# The jump-gap leaf `Xw.XwGapLh` split by the kind of the gap point

Notation as in `R2.XwGap`: a window `(n, λ, λ')`, an indecomposable cofinal far index `p` with the `k`-move below
`p`, `X = B_n p`; a gap point is `a < X` with `B_n q ≤ a` for every `q < p` (`YeGapPt`).  Under
`L(ω+1) ≤ ν_C` every gap point is below `ν_C`, so at a non-`υ`-point the `R₂^C`-reach is the `R₁⁺`-reach
(`Lh.lhSk_all`):

* `yeLh_easy`: at a non-`υ`-point `a < X < ν_C`, `X` indecomposable, the reach is `< X` when `a` is not an
  `ε`-number (`lh(a) = a`, `1`, or `a + logend(a') < a·2 ≤ X`) or when some `υ`-point lies in `(a, X]` (an
  `R₁⁺`-reach never passes the next `υ`-point);
* `yeUps_block`: a `υ`-point `a` inside a block `(υ_{botI μ j}, β]`, `β = υ_{μ+ω(j+1)+1} < ν_C`, has the reach `β`
  (SKEL⁺ D1, `block_le1`);
* the three remaining leaves: `YeGapEps` (gap `ε`-numbers that are no `υ`-point and have no `υ`-point in
  `(a, X]`), `YeGapRng` (gap points `υ_l` with `l` a restart index), `YeGapBlk` (gap `υ`-points inside a block:
  the block top `β < X`);
* `yeNoUps_off` (**no `υ`-point in the gap unless `p` is a restart**): `p` lies in the first `υ`-bracket
  `(υ_b, υ_{b+1}]` of its block (a `υ`-point of the block between `ρ_λ` and `p` would reach the block top `≥ p`,
  against the closed points cofinal below `p`), and `B_n(υ_{ν+β}) = υ_{ν'+β}` on the region of the restart `ν`
  (`Sf.sfShiftAll`), so the gap lies strictly between the consecutive `υ`-points `B_n υ_b`, `B_n υ_{b+1}`;
  `yeGapUps_rst`: so the leaves `YeGapRng`, `YeGapBlk` ask only restarts `p = υ_κ`;
* `yeGapLh_of` / `yeGapLh_iff`: under `L(ω+1) ≤ ν_C`, **`Xw.XwGapLh ⇔ YeGapEps ∧ YeGapRng ∧ YeGapBlk`**;
* `yeGap_of_target` (NON-VACUITY): the target (`hν`, ENUM-REACH, `CdEQ`, `SkKFar`) gives the three leaves.

New definitions: the statement names `YeGapPt`, `YeGapEps`, `YeGapRng`, `YeGapBlk`.  No axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ye

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **A gap point** `a` of `B_n` at an indecomposable cofinal far index `p` of the window `(n, λ, λ')`. -/
def YeGapPt (S : InaccSeq.{0}) (n : ℕ) (l l' p a : Ordinal.{0}) : Prop :=
  R2Skel.SkEX.SkWin S n l l' ∧ cdDelta l * ω ≤ p ∧ p ≤ cdTheta S l (cdCode S l) ∧ Indec p ∧
    (∀ q < p, cdk l q < p) ∧ (∀ q < p, cdk l' (Bc.bcB S n q) = Bc.bcB S n (cdk l q)) ∧
    a < Bc.bcB S n p ∧ ∀ q < p, Bc.bcB S n q ≤ a

/-- **Leaf (gap `ε`-numbers)**: a gap point that is an `ε`-number, no `υ`-point, with no `υ`-point in
`(a, B_n p]`, has its reach below `B_n p`. -/
def YeGapEps (S : InaccSeq.{0}) : Prop :=
  ∀ (n : ℕ) (l l' p a : Ordinal.{0}), YeGapPt S n l l' p a → InE a → ¬ UpsPt a →
    (∀ u, UpsPt u → a < u → Bc.bcB S n p < u) → ∃ r, IsReach R2C a r ∧ r < Bc.bcB S n p

/-- **Leaf (gap restarts)**: at a restart `p = υ_κ`, a gap point `υ_l`, `l` a restart index, has its reach below
`B_n p` (at a non-restart `p` there is no `υ`-point in the gap, `yeNoUps_off`). -/
def YeGapRng (S : InaccSeq.{0}) : Prop :=
  ∀ (n : ℕ) (l l' p l₀ κ : Ordinal.{0}), YeGapPt S n l l' p (upsilon l₀) → IsRestartIdx l₀ →
    IsRestartIdx κ → p = upsilon κ → ∃ r, IsReach R2C (upsilon l₀) r ∧ r < Bc.bcB S n p

/-- **Leaf (gap block `υ`-points)**: at a restart `p = υ_κ`, for a gap `υ`-point `a` in the block
`(υ_{botI μ j}, υ_{μ+ω(j+1)+1}]`, the block top is below `B_n p`. -/
def YeGapBlk (S : InaccSeq.{0}) : Prop :=
  ∀ (n : ℕ) (l l' p a μ κ : Ordinal.{0}) (j : ℕ), YeGapPt S n l l' p a → UpsPt a → IsRestartIdx κ →
    p = upsilon κ → (μ = 0 ∨ IsRestartIdx μ) →
    upsilon (botI μ j) < a → a ≤ upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) →
    upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) < Bc.bcB S n p

/-- Facts at a gap point: `B_n p` is indecomposable, below `L(ω+1)`, and (under `hν`) `a < ν_C`. -/
theorem yeGapPt_facts (hν : Nc.ncL S (ω + 1) ≤ nuC) {n : ℕ} {l l' p a : Ordinal.{0}}
    (hP : YeGapPt S n l l' p a) :
    Indec (Bc.bcB S n p) ∧ Bc.bcB S n p < Nc.ncL S (ω + 1) ∧ a < nuC := by
  obtain ⟨hW, hfar, hp, hI, -, -, ha, -⟩ := hP
  obtain ⟨hpC, hpL, -, -, -⟩ := Xw.xwWin hW hfar hp
  have hXL : Bc.bcB S n p < Nc.ncL S (ω + 1) := Bc.bcB_bound' S n p hpC
  exact ⟨Bc.bcB_indec hpL hI, hXL, (ha.trans hXL).trans_le hν⟩

/-- **The reach of a non-`υ`-point below an indecomposable `X`**: below `X` unless `a` is an `ε`-number with no
`υ`-point in `(a, X]`. -/
theorem yeLh_easy {a X : Ordinal.{0}} (haC : a < nuC) (hX : Indec X) (haX : a < X) (hU : ¬ UpsPt a)
    (h : ¬ InE a ∨ ∃ u, UpsPt u ∧ a < u ∧ u ≤ X) : ∃ r, IsReach R2C a r ∧ r < X := by
  obtain ⟨ξ, r, h1, -, hr, -, hr2, hc⟩ := Lh.lhSk_all haC hU
  refine ⟨r, hr, ?_⟩
  rcases hc with ⟨-, e⟩ | ⟨ha1, e⟩ | ⟨a', ha0, ea, hE, e⟩ | ⟨hE, -, -⟩
  · rw [e]; exact haX
  · rw [e, ← ha1]; exact haX
  · subst ea
    have hle : a' ≤ ω ^ a' := right_le_opow a' one_lt_omega0
    have hlt : a' < ω ^ a' := by
      refine lt_of_le_of_ne hle fun e' => hE ?_
      unfold InE; rw [← e']; exact e'.symm
    have hlg : lg a' < X := ((lg_le ha0).trans_lt hlt).trans haX
    rw [e]; exact (indec_iff.1 hX).2 haX hlg
  · rcases h with h | ⟨u, hu, hau, huX⟩
    · exact absurd hE h
    · have hn := upsilon_isNext ξ
      rw [succ_eq_add_one] at hn
      exact hr2.trans_le ((hn.2.2 u (lt_of_le_of_lt h1 hau) hu).trans huX)

/-- **A `υ`-point inside a block has the block top as its reach** (SKEL⁺ D1). -/
theorem yeUps_block {μ a : Ordinal.{0}} {j : ℕ} (hμ : μ = 0 ∨ IsRestartIdx μ)
    (hC : upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) < nuC) (ha1 : upsilon (botI μ j) < a)
    (ha2 : a ≤ upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1)) (hU : UpsPt a) :
    IsReach R2C a (upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1)) := by
  have hb := block_le1 hμ j hC ha1 ha2
  exact ⟨(hb _).2 ⟨le_rfl, hU.2 _ ha2⟩, fun g hg => ((hb g).1 hg).1⟩

/-! ## No `υ`-point in the gap unless `p` is a restart -/

/-- Two restart indices (or `0`) `ν < κ` are at least `ω·ω` apart. -/
theorem ye_rst_gap {ν κ : Ordinal.{0}} (hν : ν = 0 ∨ IsRestartIdx ν) (hκ : IsRestartIdx κ) (h : ν < κ) :
    ν + ω * ω ≤ κ := by
  have hdν : ω * ω ∣ ν := by
    rcases hν with rfl | hν
    · exact dvd_zero _
    · exact (ri_iff.1 hν).2
  have hdκ : ω * ω ∣ κ := (ri_iff.1 hκ).2
  obtain ⟨d, rfl⟩ := exists_add_of_le h.le
  have hd0 : d ≠ 0 := by
    rintro rfl; rw [add_zero] at h; exact lt_irrefl _ h
  have hdd : ω * ω ∣ d := (Ordinal.dvd_add_iff hdν).1 hdκ
  exact (add_le_add_iff_left ν).2 (Ordinal.le_of_dvd hd0 hdd)

/-- `ω·(j+1) + 1 + 1 < ω·ω`. -/
theorem ye_blk_lt (j : ℕ) : ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 + 1 < ω * ω := by
  have h1 : ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 + 1 < ω * ((j + 1 : ℕ) : Ordinal.{0}) + ω := by
    rw [add_assoc]
    exact (add_lt_add_iff_left _).2 (by
      have : (1 : Ordinal.{0}) + 1 = ((2 : ℕ) : Ordinal.{0}) := by norm_num
      rw [this]; exact natCast_lt_omega0 2)
  have h2 : ω * ((j + 1 : ℕ) : Ordinal.{0}) + ω = ω * ((j + 2 : ℕ) : Ordinal.{0}) := by
    rw [show ((j + 2 : ℕ) : Ordinal.{0}) = ((j + 1 : ℕ) : Ordinal.{0}) + 1 from Nat.cast_succ (j + 1), mul_add_one]
  rw [h2] at h1
  exact h1.trans ((mul_lt_mul_iff_right₀ omega0_pos).2 (natCast_lt_omega0 _))

/-- The block bottom index `botI ν i = ν + β₀` with `β₀ + 1 < ω·ω`, and the block top index
`ν + ω(i+1) + 1 < ν + ω·ω`. -/
theorem ye_botI_off (ν : Ordinal.{0}) (i : ℕ) :
    ∃ β₀, botI ν i = ν + β₀ ∧ β₀ + 1 < ω * ω ∧ ν + ω * ((i + 1 : ℕ) : Ordinal.{0}) + 1 < ν + ω * ω := by
  have htop : ν + ω * ((i + 1 : ℕ) : Ordinal.{0}) + 1 < ν + ω * ω := by
    rw [add_assoc]; exact (add_lt_add_iff_left _).2 ((lt_add_one _).trans (ye_blk_lt i))
  rcases i with _ | k
  · refine ⟨0, by simp [botI], ?_, htop⟩
    rw [zero_add]; exact one_lt_omega0.trans_le (Ordinal.le_mul_left ω omega0_pos)
  · refine ⟨ω * ((k + 1 : ℕ) : Ordinal.{0}) + 1, ?_, ye_blk_lt k, htop⟩
    show ν + ω * ((k + 1 : ℕ) : Ordinal.{0}) + 1 = ν + (ω * ((k + 1 : ℕ) : Ordinal.{0}) + 1)
    rw [add_assoc]

/-- **If `p` is no restart, the jump gap at `p` contains no `υ`-point** (under `L(ω+1) ≤ ν_C`).  `p` lies in a block
`(υ_b, β]`, `b = botI ν i`; a `υ`-point `u ∈ (υ_b, p)` above `ρ_λ` would have the reach `β ≥ p` (`yeUps_block`)
against the closed points cofinal below `p`; so `p ≤ υ_{b+1}`.  `ν` is a restart in `[c_n, c_{n+1})`, and
`B_n(υ_{ν+β}) = υ_{ν'+β}` (`Sf.sfShiftAll`), so the gap lies in `(B_n υ_b, B_n υ_{b+1}) = (υ_{ν'+β₀}, υ_{ν'+β₀+1})`. -/
theorem yeNoUps_off (hν : Nc.ncL S (ω + 1) ≤ nuC) {n : ℕ} {l l' p a : Ordinal.{0}}
    (hP : YeGapPt S n l l' p a) (hpr : ∀ κ, IsRestartIdx κ → p ≠ upsilon κ) (hU : UpsPt a) : False := by
  obtain ⟨hW, hfar, hp, hI, hcof, -, ha, hgap⟩ := hP
  obtain ⟨hpC, hpL, -, hδp, -⟩ := Xw.xwWin hW hfar hp
  have h1p : Bc.bcC S n < p := hW.2.1.trans ((cdRho_lt_delta l).trans hδp)
  have hp0 : 0 < p := lt_of_le_of_lt zero_le h1p
  have hpΩ : p < Om1 := (hpL.trans (Qq.qqL_lt_succ S)).trans Xw.xwL_lt_Om1
  have hpν : p < nuC := (hpC.trans (Cx.cxC_lt_L1 n)).trans_le hν
  rcases classify hp0 with ⟨κ, hκ, e⟩ | ⟨ν, i, hν0, hb, hct⟩
  · exact hpr κ hκ e
  have hC := Lh.lhSk_top hν0 hb hpν
  -- no `υ`-point of the block between `ρ_λ` and `p`
  have hC' : ∀ u, UpsPt u → upsilon (botI ν i) < u → u < p → upsilon l < u → False := by
    intro u hu h1 h2 h3
    have hreach := yeUps_block hν0 hC h1 (h2.le.trans hct) hu
    have hy : cdk l u < p := hcof u h2
    have hcl := cdk_closed (hy.trans hpΩ)
    have := hcl.2 u h3 ((cdk_strictMono l).id_le u) _ hreach.1
    exact absurd (this.trans_lt hy) (not_lt.2 hct)
  have hpb1 : p ≤ upsilon (botI ν i + 1) := by
    by_contra h
    push Not at h
    have hb1 : upsilon (botI ν i) < upsilon (botI ν i + 1) := upsilon_normal.strictMono (lt_add_one _)
    by_cases hr : upsilon l < upsilon (botI ν i + 1)
    · exact hC' _ (upsPt_upsilon (lt_of_le_of_lt zero_le (lt_add_one _))) hb1 h hr
    · push Not at hr
      exact hC' (cdDelta l) (upsPt_upsilon (lt_of_le_of_lt zero_le (lt_add_one _)))
        (hb1.trans_le (hr.trans (cdRho_lt_delta l).le)) hδp (cdRho_lt_delta l)
  -- `ν` is a restart in `[c_n, c_{n+1})`
  obtain ⟨β₀, hβ₀, hβ₁, htop⟩ := ye_botI_off ν i
  obtain ⟨κn, hκn, ecn⟩ := Pp.ppL_succ_restart (S := S) n
  obtain ⟨κn', hκn', ecn'⟩ := Pp.ppL_succ_restart (S := S) (n + 1)
  have ecn0 : Bc.bcC S n = upsilon κn := ecn
  have ecn1 : Bc.bcC S (n + 1) = upsilon κn' := ecn'
  have hκν : κn ≤ ν := by
    by_contra hlt
    push Not at hlt
    have h1 := ye_rst_gap hν0 hκn hlt
    have h2 : κn < ν + ω * ((i + 1 : ℕ) : Ordinal.{0}) + 1 := by
      have := h1p.trans_le hct
      rw [ecn0] at this
      exact upsilon_normal.strictMono.lt_iff_lt.1 this
    exact absurd (h2.trans htop) (not_lt.2 h1)
  have hνr : IsRestartIdx ν := by
    rcases hν0 with rfl | h
    · exact absurd (le_antisymm hκν zero_le) hκn.1
    · exact h
  have hcnν : Bc.bcC S n ≤ upsilon ν := by rw [ecn0]; exact upsilon_normal.strictMono.monotone hκν
  have hνκ' : ν + ω * ω ≤ κn' := by
    refine ye_rst_gap (Or.inr hνr) hκn' ?_
    have h3 : upsilon (botI ν i) < upsilon κn' := ecn1 ▸ (hb.trans hpC)
    have h4 := upsilon_normal.strictMono.lt_iff_lt.1 h3
    rw [hβ₀] at h4
    exact lt_of_le_of_lt le_self_add h4
  have hreg : ∀ β, β < ω * ω → upsilon (ν + β) < Bc.bcC S (n + 1) := by
    intro β hβ
    rw [ecn1]
    exact upsilon_normal.strictMono (((add_lt_add_iff_left ν).2 hβ).trans_le hνκ')
  obtain ⟨ν', -, hsh⟩ := Sf.sfShiftAll (S := S) n ν hνr hcnν (hreg 0 (mul_pos omega0_pos omega0_pos) |>
    fun h => by rwa [add_zero] at h)
  have hβ0 : β₀ < ω * ω := (lt_add_one β₀).trans hβ₁
  have e0 : Bc.bcB S n (upsilon (botI ν i)) = upsilon (ν' + β₀) := by
    rw [hβ₀]; exact hsh β₀ hβ0 (hreg β₀ hβ0)
  have e1 : Bc.bcB S n (upsilon (botI ν i + 1)) = upsilon (ν' + β₀ + 1) := by
    rw [hβ₀, add_assoc, add_assoc]; exact hsh (β₀ + 1) hβ₁ (hreg _ hβ₁)
  -- the gap lies strictly between two consecutive `υ`-points
  have hL : ∀ x, x < Bc.bcC S (n + 1) → x < Nc.ncL S ω := fun x hx => hx.trans (Bc.bcC_lt S (n + 1))
  have hbC : upsilon (botI ν i) < Bc.bcC S (n + 1) := hb.trans hpC
  have hb1C : upsilon (botI ν i + 1) < Bc.bcC S (n + 1) := by
    rw [hβ₀, add_assoc]; exact hreg _ hβ₁
  have h1c : (1 : Ordinal.{0}) < Bc.bcC S n := one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _))
  have h1lt : (1 : Ordinal.{0}) < p := h1c.trans h1p
  have hq : upsilon (botI ν i) + 1 < p := (indec_iff.1 hI).2 hb h1lt
  have hga := hgap _ hq
  rw [Bc.bcB_add (hL _ hbC) (h1c.trans (Bc.bcC_lt S n)), Bc.bcB_fixN n 1 h1c, e0] at hga
  have hlo : upsilon (ν' + β₀) < a := (lt_add_one _).trans_le hga
  have hhi : a < upsilon (ν' + β₀ + 1) := by
    rw [← e1]
    exact ha.trans_le (Xg.xgB_le (hL _ hpC) (hL _ hb1C) hpb1)
  have hn := upsilon_isNext (ν' + β₀)
  rw [succ_eq_add_one] at hn
  exact absurd (hn.2.2 a hlo hU) (not_le.2 hhi)

/-- **A `υ`-point in the jump gap forces `p` to be a restart.** -/
theorem yeGapUps_rst (hν : Nc.ncL S (ω + 1) ≤ nuC) {n : ℕ} {l l' p a : Ordinal.{0}}
    (hP : YeGapPt S n l l' p a) (hU : UpsPt a) : ∃ κ, IsRestartIdx κ ∧ p = upsilon κ := by
  by_contra h
  push Not at h
  exact yeNoUps_off hν hP h hU

/-- **`YeGapEps ∧ YeGapRng ∧ YeGapBlk ⇒ Xw.XwGapLh`** (under `L(ω+1) ≤ ν_C`). -/
theorem yeGapLh_of (hν : Nc.ncL S (ω + 1) ≤ nuC) (hE : YeGapEps S) (hR : YeGapRng S) (hB : YeGapBlk S) :
    Xw.XwGapLh S := by
  intro n l l' hW p hfar hp hI hcof hIH a ha hgap
  have hP : YeGapPt S n l l' p a := ⟨hW, hfar, hp, hI, hcof, hIH, ha, hgap⟩
  obtain ⟨hXI, -, haC⟩ := yeGapPt_facts hν hP
  by_cases hU : UpsPt a
  · obtain ⟨κ, hκ, hpκ⟩ := yeGapUps_rst hν hP hU
    rcases classify hU.1 with ⟨l₀, hl₀, rfl⟩ | ⟨μ, j, hμ, hb, hct⟩
    · exact hR n l l' p l₀ κ hP hl₀ hκ hpκ
    · have hC := Lh.lhSk_top hμ hb haC
      exact ⟨_, yeUps_block hμ hC hb hct hU, hB n l l' p a μ κ j hP hU hκ hpκ hμ hb hct⟩
  · by_cases hE' : InE a
    · by_cases hu : ∃ u, UpsPt u ∧ a < u ∧ u ≤ Bc.bcB S n p
      · exact yeLh_easy haC hXI ha hU (Or.inr hu)
      · push Not at hu
        exact hE n l l' p a hP hE' hU hu
    · exact yeLh_easy haC hXI ha hU (Or.inl hE')

/-- **`Xw.XwGapLh ⇔ YeGapEps ∧ YeGapRng ∧ YeGapBlk`** (under `L(ω+1) ≤ ν_C`). -/
theorem yeGapLh_iff (hν : Nc.ncL S (ω + 1) ≤ nuC) :
    Xw.XwGapLh S ↔ YeGapEps S ∧ YeGapRng S ∧ YeGapBlk S := by
  refine ⟨fun h => ⟨?_, ?_, ?_⟩, fun h => yeGapLh_of hν h.1 h.2.1 h.2.2⟩
  · rintro n l l' p a ⟨hW, hfar, hp, hI, hcof, hIH, ha, hgap⟩ - - -
    exact h n l l' hW p hfar hp hI hcof hIH a ha hgap
  · rintro n l l' p l₀ κ ⟨hW, hfar, hp, hI, hcof, hIH, ha, hgap⟩ - - -
    exact h n l l' hW p hfar hp hI hcof hIH _ ha hgap
  · intro n l l' p a μ κ j hP hU _ _ hμ hb hct
    obtain ⟨hW, hfar, hp, hI, hcof, hIH, ha, hgap⟩ := hP
    have haC := (yeGapPt_facts hν ⟨hW, hfar, hp, hI, hcof, hIH, ha, hgap⟩).2.2
    have hC := Lh.lhSk_top hμ hb haC
    obtain ⟨r, hr, hrX⟩ := h n l l' hW p hfar hp hI hcof hIH a ha hgap
    rw [Xr.xrReach_unique (yeUps_block hμ hC hb hct hU) hr]
    exact hrX

/-- **NON-VACUITY**: the target gives the three leaves. -/
theorem yeGap_of_target (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) (hEQ : CdEQ S)
    (hK : R2Skel.SkEX.SkKFar S) : YeGapEps S ∧ YeGapRng S ∧ YeGapBlk S :=
  (yeGapLh_iff hν).1 (Xw.xwGapLh_of_target hν hU hL hEQ hK)

end Googology.Trans.PoR.InaccPsi.R2.Ye

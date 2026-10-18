import Googology.Trans.PoR.InaccPsi.R2.NnLin

/-!
# The generic offset at every fixed point of `υ` that is not a `Γ`-point, and `O(F) ≥ F·F` at the `Γ`-points

`V_γ = veblenWith υ γ` (`R2.VG`), `levG F` the level of `F` (the largest `γ` with `V_{γ'}(F) = F` for `γ' < γ`),
`invG γ F` the index of `F` in `V_γ`, `logend = R2.lg` (`= cdExp`), `IsGP F` (`F` is a `Γ`-point: `V_g(F) = F` for
every `g < F`).  For every term system `X` with linear terms (`NnLin X`), `O = xtOrec X`:

* `nn_const_cof`: every constant `c < F` is realized cofinally below a fixed point `F` (at restarts `λ₀ + ω^{c+2}`,
  where `O = c + 1` or `c + 2` by `Xt.xtRel`);
* `nn_cof_lin`: if `V_q(F) = F` (`1 ≤ q < F`), the term `x·q + r` (`r < F`) is realized cofinally below `F`, at the
  points `V_q(β)` of level exactly `q` with `ω^r ∣ β`, given the offset at those points;
* `nnLev` (**THEOREM LEVEL**): at every restart `F < Ω₁` with `υ_F = F` that is not a `Γ`-point, with
  `γ = levG F`, `F = V_γ(α)`:  **`O(F) = F·γ + logend(α)`**.  (Upper bound: a term realized at a point `μ` near `F`
  is a constant, or is below `μ·(γ_μ + 1)` with `γ_μ < γ`, or below `μ·γ + logend(α)` (`logend(α_μ) < logend(α)`
  by the window lemma), and the comparison `uni_le` carries the bound from `μ` to `F`.  Lower bound: the terms
  `x·q + r`, `q < γ`, `r < F`, and `x·γ + d`, `d < logend(α)`, are realized cofinally.)  No height bound: this is
  Theorem OFF-V of `R2.OffG` (there below `Λ_Γ`) for every height below `Ω₁` and every term system with linear terms.
* `nnGam` (**the `Γ`-points**): at every restart `F < Ω₁` with `υ_F = F` that is a `Γ`-point, `F·F ≤ O(F)`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Nn

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp

variable {X : XtSys}

/-! ## Facts at a fixed point of `υ` -/

theorem nn_fix_facts {F : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) :
    InE F ∧ IsPrincipal (· + ·) F ∧ ω * ω < F ∧ IsSuccLimit F ∧ UpsPt F := by
  obtain ⟨hE, hp, hww⟩ := cp_fix_facts hF hfix
  have hF0 : 0 < F := pos_iff_ne_zero.2 hF.1
  have h1 : (1 : Ordinal.{0}) < F :=
    lt_of_le_of_lt (Order.one_le_iff_pos.2 (mul_pos omega0_pos omega0_pos)) hww
  exact ⟨hE, hp, hww, isSuccLimit_of_isPrincipal_add h1 hp, hfix ▸ upsPt_upsilon hF0⟩

theorem nn_opow_lt {F x : Ordinal.{0}} (hE : InE F) (hx : x < F) : ω ^ x < F :=
  calc ω ^ x < ω ^ F := (opow_lt_opow_iff_right one_lt_omega0).2 hx
    _ = F := hE

/-- The data of a fixed point that is not a `Γ`-point: `γ = levG F ≠ 0`, `γ < F`, `F = V_γ(α)`, `0 < α < F`,
`V_γ(F) ≠ F`, `V_b(F) = F` for `b < γ`. -/
theorem nn_lev_data {F : Ordinal.{0}} (hfix : upsilon F = F) (hng : ∃ g < F, VG g F ≠ F) :
    levG F ≠ 0 ∧ levG F < F ∧ VG (levG F) (invG (levG F) F) = F ∧ invG (levG F) F ≠ 0 ∧
      invG (levG F) F < F ∧ VG (levG F) F ≠ F ∧ ∀ b < levG F, VG b F = F := by
  obtain ⟨g, hgF, hg⟩ := hng
  have h : ∃ b, VG b F ≠ F := ⟨g, hg⟩
  have hs := levG_spec h
  have hγ0 : levG F ≠ 0 := fun h0 => (levG_eq_zero h).1 h0 hfix
  have hγF : levG F < F := (hs.2.2 g hg).trans_lt hgF
  have hr : F ∈ Set.range (VG (levG F)) := (mem_range_VG hγ0).2 hs.1
  have hV := invG_spec hr
  have hα0 : invG (levG F) F ≠ 0 := by
    intro h0; rw [h0, VG_at_zero] at hV
    exact (lt_of_le_of_lt zero_le hγF).ne hV
  have hαF : invG (levG F) F < F := by
    refine lt_of_le_of_ne (by have := VG_id_le (levG F) (invG (levG F) F); rwa [hV] at this) fun e => ?_
    rw [e] at hV; exact hs.2.1 hV
  exact ⟨hγ0, hγF, hV, hα0, hαF, hs.2.1, hs.1⟩

theorem nn_ng_of_gp {F : Ordinal.{0}} (hF0 : 0 < F) (hG : ¬ IsGP F) : ∃ g < F, VG g F ≠ F := by
  by_contra h
  push Not at h
  exact hG ⟨hF0, h⟩

/-- The `V_γ`-fixed points below `F = V_γ(α)` lie below `α`. -/
theorem nn_lev_le {F α γ μ : Ordinal.{0}} (hV : VG γ α = F) (hμF : μ < F) (hαμ : α < μ) : VG γ μ ≠ μ := by
  intro h
  have : VG γ μ < VG γ α := by rw [h, hV]; exact hμF
  exact absurd ((VG_strictMono γ).lt_iff_lt.1 this) (not_lt.2 hαμ.le)

/-- A non-principal ordinal is not a fixed point of `V_q`, `q ≠ 0`. -/
theorem nn_not_fix {q β : Ordinal.{0}} (hq : q ≠ 0) (hβ0 : 0 < β) (h : ¬ IsPrincipal (· + ·) β) :
    VG q β ≠ β := by
  intro hfix
  have hu : upsilon β = β := ups_fix_of_VG hq ⟨β, hfix⟩
  exact h (cp_fix_facts (ri_of_fp hβ0 hu) hu).2.1

/-- A multiple of `ω^r` above `β₀`, below `β₀ + ω^r·2`, that is not additive principal. -/
theorem nn_pick {β0 r : Ordinal.{0}} :
    ∃ β, β0 < β ∧ β ≤ β0 + ω ^ r + ω ^ r ∧ ω ^ r ∣ β ∧ ¬ IsPrincipal (· + ·) β ∧ 0 < β := by
  have hpa : ω ^ r ≠ 0 := (opow_pos _ omega0_pos).ne'
  have hpp : 0 < ω ^ r := opow_pos _ omega0_pos
  set a := ω ^ r * (β0 / ω ^ r + 1) with ha
  have hβa : β0 < a := by rw [ha, mul_add_one]; exact lt_mul_div_add β0 hpa
  have hale : a ≤ β0 + ω ^ r := by rw [ha, mul_add_one]; exact add_le_add (mul_div_le β0 _) le_rfl
  have hra : ω ^ r ≤ a := by rw [ha]; exact le_mul_left _ (lt_of_le_of_lt zero_le (lt_add_one _))
  refine ⟨a + ω ^ r, hβa.trans (lt_add_of_pos_right _ hpp), add_le_add hale le_rfl,
    dvd_add (dvd_mul_right _ _) dvd_rfl, fun hP => ?_, lt_of_le_of_lt zero_le (hβa.trans
      (lt_add_of_pos_right _ hpp))⟩
  have h1 : a < a + ω ^ r := lt_add_of_pos_right _ hpp
  have h2 : ω ^ r < a + ω ^ r := hra.trans_lt h1
  exact lt_irrefl _ (hP h1 h2)

/-! ## Realized terms -/

/-- **Every constant `c < F` is realized cofinally below a fixed point `F`.** -/
theorem nn_const_cof {F c : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hF1 : F < Om1)
    (hc : c < F) : XtCof X (xtOrec X) F (X.cst c) := by
  obtain ⟨hE, hp, hww, hlim, -⟩ := nn_fix_facts hF hfix
  intro ν hν
  set a := c + 1 + 1 with ha
  have haF : a < F := hlim.add_one_lt (hlim.add_one_lt hc)
  set ν1 := max ν a with hν1
  have hν1F : ν1 < F := max_lt hν haF
  set μ0 := ω * ω * (ν1 + 1) with hμ0
  have hww0 : ω * ω ≠ 0 := (mul_pos omega0_pos omega0_pos).ne'
  have hμ0r : IsRestartIdx μ0 :=
    ri_iff.2 ⟨mul_ne_zero hww0 (add_pos_of_right zero_lt_one ν1).ne', dvd_mul_right _ _⟩
  have hν1μ0 : ν1 < μ0 := lt_of_lt_of_le (lt_add_one ν1) (le_mul_right (ν1 + 1) (mul_pos omega0_pos omega0_pos))
  have hμ0F : μ0 < F := hE.mul_lt hww (hlim.add_one_lt hν1F)
  have hμ01 : μ0 < Om1 := hμ0F.trans hF1
  have hz : ω ^ a < upsilon μ0 :=
    nn_opow_lt (ups_inE hμ0r) ((le_max_right ν a).trans_lt (hν1μ0.trans_le upsilon_normal.strictMono.le_apply))
  have h2a : (2 : Ordinal.{0}) ≤ a := by rw [ha, add_assoc, one_add_one_eq_two]; exact le_add_self
  have hzd : ω * ω ∣ ω ^ a := by rw [← cp_ww_eq]; exact opow_dvd_opow ω h2a
  have hz0 : 0 < ω ^ a := opow_pos _ omega0_pos
  have hO := xtRel (X := X) hμ0r hμ01 (ω ^ a) hz0 hz hzd
  have hexp : cdExp (ω ^ a) = a := by have := cpExp_mul_succ a 0; simpa using this
  rw [hexp] at hO
  have hμr : IsRestartIdx (μ0 + ω ^ a) :=
    ri_iff.2 ⟨(lt_of_lt_of_le hz0 le_add_self).ne', dvd_add (ri_iff.1 hμ0r).2 hzd⟩
  refine ⟨μ0 + ω ^ a, hμr, ?_, hp hμ0F (nn_opow_lt hE haF), ?_, ?_⟩
  · exact ((le_max_left ν a).trans_lt hν1μ0).trans_le le_self_add
  · refine X.cb_cstI _ _ ?_
    have : c < μ0 := (lt_of_lt_of_le (lt_add_one c) ((le_self_add).trans (le_max_right ν a))).trans
      hν1μ0
    exact (this.trans_le le_self_add).trans_le upsilon_normal.strictMono.le_apply
  · rw [X.val_cst, hO]
    exact le_self_add.trans (cpOff_add_one_ge (c + 1))

/-- The offset at the points of level `≥ 1` that are not `Γ`-points, below `F`. -/
def NnLevBelow (X : XtSys) (F : Ordinal.{0}) : Prop :=
  ∀ μ < F, IsRestartIdx μ → μ < Om1 → upsilon μ = μ → ¬ IsGP μ →
    xtOrec X μ = μ * levG μ + lg (invG (levG μ) μ)

/-- **`x·q + r` is realized cofinally below a `V_q`-fixed point `F`** (`1 ≤ q < F`, `r < F`), given the offset
at the points of level exactly `q` below `F`. -/
theorem nn_cof_lin {F q r : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hF1 : F < Om1)
    (hO : NnLevBelow X F) (hq0 : q ≠ 0) (hqF : VG q F = F) (hq : q < F) (hr : r < F) (s : X.Tm)
    (hs : ∀ y, UpsPt y → y < Om1 → q < y → r < y → X.CB s y ∧ X.val s y = y * q + r) :
    XtCof X (xtOrec X) F s := by
  obtain ⟨hE, hp, -, hlim, -⟩ := nn_fix_facts hF hfix
  intro ν hν
  set ν' := max (max ν q) r with hν'
  have hν'F : ν' < F := max_lt (max_lt hν hq) hr
  obtain ⟨β0, hβ0F, hνβ0⟩ := ((VG_normal q).lt_iff_exists_lt hlim).1 (show ν' < VG q F by rw [hqF]; exact hν'F)
  obtain ⟨β, hβ0β, hβle, hdvd, hnp, hβpos⟩ := nn_pick (β0 := β0) (r := r)
  have hβF : β < F := hβle.trans_lt (hp (hp hβ0F (nn_opow_lt hE hr)) (nn_opow_lt hE hr))
  set μ := VG q β with hμ
  have hμF : μ < F := by rw [hμ, ← hqF]; exact VG_strictMono q hβF
  have hν'μ : ν' < μ := hνβ0.trans (VG_strictMono q hβ0β)
  have hμfix : upsilon μ = μ := ups_fix_of_VG hq0 ⟨β, rfl⟩
  have hμ0 : 0 < μ := lt_of_le_of_lt zero_le hν'μ
  have hμr : IsRestartIdx μ := ri_of_fp hμ0 hμfix
  have hμ1 : μ < Om1 := hμF.trans hF1
  have hβfix : VG q β ≠ β := nn_not_fix hq0 hβpos hnp
  have hμne : VG q μ ≠ μ := fun h => hβfix ((VG_strictMono q).injective h)
  have hqμ : q < μ := ((le_max_right ν q).trans (le_max_left _ r)).trans_lt hν'μ
  have hrμ : r < μ := (le_max_right _ r).trans_lt hν'μ
  have hlev : levG μ = q :=
    le_antisymm ((levG_spec ⟨q, hμne⟩).2.2 q hμne) (levG_ge ⟨q, hμne⟩ hq0 ⟨β, rfl⟩)
  have hng : ¬ IsGP μ := fun h => hμne (h.2 q hqμ)
  have hOμ := hO μ hμF hμr hμ1 hμfix hng
  rw [hlev, hμ, invG_VG, ← hμ] at hOμ
  have hrβ : r ≤ lg β := cdExp_max hβpos.ne' hdvd
  obtain ⟨hCB, hval⟩ := hs μ (hμfix ▸ upsPt_upsilon hμ0) hμ1 hqμ hrμ
  refine ⟨μ, hμr, (le_max_left _ _ |>.trans (le_max_left _ _)).trans_lt hν'μ, hμF, ?_, ?_⟩
  · rw [hμfix]; exact hCB
  · rw [hμfix, hval, hOμ]; exact (add_le_add_iff_left _).2 hrβ

/-- **`x·γ + d` is realized cofinally below `F = V_γ(α)`** for `d < logend(α)`, given the offset at the points
of level exactly `γ` below `F`. -/
theorem nn_cof_top {F γ α d : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hF1 : F < Om1)
    (hO : NnLevBelow X F) (hγ0 : γ ≠ 0) (hγF : γ < F) (hV : VG γ α = F) (hα0 : α ≠ 0) (hαF : α < F)
    (hd : d < lg α) (s : X.Tm)
    (hs : ∀ y, UpsPt y → y < Om1 → γ < y → d < y → X.CB s y ∧ X.val s y = y * γ + d) :
    XtCof X (xtOrec X) F s := by
  obtain ⟨hE, hp, -, -, -⟩ := nn_fix_facts hF hfix
  intro ν hν
  obtain ⟨α0, hdec, hdv⟩ := cdExp_decomp hα0
  set e := cdExp α with he
  have hde : d < e := hd
  have he0 : e ≠ 0 := (lt_of_le_of_lt zero_le hde).ne'
  have hαlim : IsSuccLimit α := by
    refine Ordinal.isSuccLimit_iff.2 ⟨hα0, isSuccPrelimit_iff_omega0_dvd.2 ?_⟩
    have h1 : ω ∣ ω ^ e := by
      have := opow_dvd_opow ω (Order.one_le_iff_ne_zero.2 he0); rwa [opow_one] at this
    rw [hdec]; exact dvd_add (h1.trans hdv) h1
  have hdF : d < F := (hd.trans_le (lg_le hα0)).trans hαF
  set ν' := max (max ν γ) (max α d) with hν'
  have hν'F : ν' < F := max_lt (max_lt hν hγF) (max_lt hαF hdF)
  obtain ⟨β1, hβ1α, hνβ1⟩ := ((VG_normal γ).lt_iff_exists_lt hαlim).1 (show ν' < VG γ α by rw [hV]; exact hν'F)
  have hpe : 0 < ω ^ e := opow_pos _ omega0_pos
  have hα01 : α0 + 1 < α := by
    rw [hdec]; refine (add_lt_add_iff_left _).2 ?_
    exact lt_of_lt_of_le one_lt_omega0
      (by have := opow_le_opow_right omega0_pos (Order.one_le_iff_ne_zero.2 he0); rwa [opow_one] at this)
  set β0 := max β1 (α0 + 1) with hβ0
  have hβ0α : β0 < α := max_lt hβ1α hα01
  have hpd : ω ^ d ≠ 0 := (opow_pos _ omega0_pos).ne'
  set β := ω ^ d * (β0 / ω ^ d + 1) with hβ
  have hβ0β : β0 < β := by rw [hβ, mul_add_one]; exact lt_mul_div_add β0 hpd
  have hβle : β ≤ β0 + ω ^ d := by rw [hβ, mul_add_one]; exact add_le_add (mul_div_le β0 _) le_rfl
  have hβα : β < α := by
    obtain ⟨w, hw⟩ := exists_add_of_le (show α0 ≤ β0 from
      ((lt_add_one α0).trans_le (le_max_right β1 (α0 + 1))).le)
    have hwe : w < ω ^ e := by
      have : α0 + w < α0 + ω ^ e := by rw [← hw, ← hdec]; exact hβ0α
      exact (add_lt_add_iff_left _).1 this
    have hde' : ω ^ d < ω ^ e := (opow_lt_opow_iff_right one_lt_omega0).2 hde
    calc β ≤ β0 + ω ^ d := hβle
      _ = α0 + (w + ω ^ d) := by rw [hw, add_assoc]
      _ < α0 + ω ^ e := (add_lt_add_iff_left _).2 (isPrincipal_add_omega0_opow e hwe hde')
      _ = α := hdec.symm
  have hβpos : 0 < β := lt_of_le_of_lt zero_le hβ0β
  set μ := VG γ β with hμ
  have hμF : μ < F := by rw [hμ, ← hV]; exact VG_strictMono γ hβα
  have hν'μ : ν' < μ :=
    hνβ1.trans_le ((VG_strictMono γ).monotone ((le_max_left _ _).trans hβ0β.le))
  have hμfix : upsilon μ = μ := ups_fix_of_VG hγ0 ⟨β, rfl⟩
  have hμ0 : 0 < μ := lt_of_le_of_lt zero_le hν'μ
  have hμr : IsRestartIdx μ := ri_of_fp hμ0 hμfix
  have hμ1 : μ < Om1 := hμF.trans hF1
  have hαμ : α < μ := ((le_max_left α d).trans (le_max_right _ _)).trans_lt hν'μ
  have hμne : VG γ μ ≠ μ := nn_lev_le hV hμF hαμ
  have hγμ : γ < μ := ((le_max_right ν γ).trans (le_max_left _ _)).trans_lt hν'μ
  have hdμ : d < μ := ((le_max_right α d).trans (le_max_right _ _)).trans_lt hν'μ
  have hlev : levG μ = γ :=
    le_antisymm ((levG_spec ⟨γ, hμne⟩).2.2 γ hμne) (levG_ge ⟨γ, hμne⟩ hγ0 ⟨β, rfl⟩)
  have hng : ¬ IsGP μ := fun h => hμne (h.2 γ hγμ)
  have hOμ := hO μ hμF hμr hμ1 hμfix hng
  rw [hlev, hμ, invG_VG, ← hμ] at hOμ
  have hdβ : d ≤ lg β := cdExp_max hβpos.ne' (by rw [hβ]; exact dvd_mul_right _ _)
  obtain ⟨hCB, hval⟩ := hs μ (hμfix ▸ upsPt_upsilon hμ0) hμ1 hγμ hdμ
  refine ⟨μ, hμr, (le_max_left _ _ |>.trans (le_max_left _ _)).trans_lt hν'μ, hμF, ?_, ?_⟩
  · rw [hμfix]; exact hCB
  · rw [hμfix, hval, hOμ]; exact (add_le_add_iff_left _).2 hdβ

/-! ## Theorem LEVEL -/

/-- **THEOREM LEVEL**: at every restart `F < Ω₁` with `υ_F = F` that is not a `Γ`-point,
`O(F) = F·γ + logend(α)` with `γ = levG F`, `F = V_γ(α)`, for every term system with linear terms. -/
theorem nnLev (hX : NnLin X) : ∀ F, IsRestartIdx F → F < Om1 → upsilon F = F → ¬ IsGP F →
    xtOrec X F = F * levG F + lg (invG (levG F) F) := by
  intro F
  induction F using WellFoundedLT.induction with
  | ind F IH =>
  intro hF hF1 hfix hG
  obtain ⟨hE, hp, hww, hlim, hU⟩ := nn_fix_facts hF hfix
  have hF0 : 0 < F := hE.pos
  obtain ⟨hγ0, hγF, hV, hα0, hαF, hVF, hbelow⟩ := nn_lev_data hfix (nn_ng_of_gp hF0 hG)
  set γ := levG F with hγ
  set α := invG γ F with hα
  have hO : NnLevBelow X F := fun μ hμ hμr hμ1 hμfix hμG => IH μ hμ hμr hμ1 hμfix hμG
  have hlgF : lg α < F := (lg_le hα0).trans_lt hαF
  refine le_antisymm ?_ ?_
  · -- the upper bound
    have hY1 : 1 ≤ F * γ + lg α :=
      (Order.one_le_iff_pos.2 hF0).trans ((le_mul_left F (pos_iff_ne_zero.2 hγ0)).trans le_self_add)
    refine xtOrec_le_of hY1 fun s hCB hc => ?_
    rw [hfix] at hCB ⊢
    obtain ⟨α0, hdec, hdv⟩ := cdExp_decomp hα0
    have hα0α : α0 < α := by
      conv_rhs => rw [hdec]
      exact lt_add_of_pos_right _ (opow_pos _ omega0_pos)
    have hVα0 : VG γ α0 < F := by rw [← hV]; exact VG_strictMono γ hα0α
    set ν0 := max (max α γ) (max (VG γ α0) (ω * ω)) with hν0
    have hν0F : ν0 < F := max_lt (max_lt hαF hγF) (max_lt hVα0 hww)
    obtain ⟨μ, hμ, h1, h2, hCBμ, hsμ⟩ := hc ν0 hν0F
    have hμ1 : μ < Om1 := h2.trans hF1
    have hμ0 : 0 < μ := lt_of_le_of_lt zero_le h1
    rcases (upsilon_normal.strictMono.le_apply : μ ≤ upsilon μ).lt_or_eq with hnf | hfx
    · -- `μ` is not a fixed point: the term is a constant `≤ μ`
      have hwwμ : ω * ω < μ := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt h1
      have hOμ := xtNonfix (X := X) hμ hwwμ hnf hμ1
      have hle : X.val s (upsilon μ) ≤ μ := (hsμ.trans_eq hOμ).trans ((cdOff_le _).trans (cpExp_le hμ.1))
      rw [xt_const_of_small (ups_inE hμ) (ups_lt_Om1 μ hμ1) hCBμ (hle.trans_lt hnf) F]
      exact (hle.trans_lt h2).trans_le ((le_mul_left F (pos_iff_ne_zero.2 hγ0)).trans le_self_add)
    · -- `μ` is a fixed point of level `≤ γ`
      have hμfix : upsilon μ = μ := hfx.symm
      rw [hμfix] at hCBμ hsμ
      have hαμ : α < μ := ((le_max_left α γ).trans (le_max_left _ _)).trans_lt h1
      have hγμ : γ < μ := ((le_max_right α γ).trans (le_max_left _ _)).trans_lt h1
      have hμne : VG γ μ ≠ μ := nn_lev_le hV h2 hαμ
      have hng : ¬ IsGP μ := fun h => hμne (h.2 γ hγμ)
      have hOμ := IH μ h2 hμ hμ1 hμfix hng
      obtain ⟨-, hγμμ, hVμ, hαμ0, hαμμ, -, -⟩ := nn_lev_data hμfix (nn_ng_of_gp hμ0 hng)
      have hlevle : levG μ ≤ γ := (levG_spec ⟨γ, hμne⟩).2.2 γ hμne
      obtain ⟨hEμ, -, -, hlimμ, hUμ⟩ := nn_fix_facts hμ hμfix
      have hBases : Bases μ F := ⟨hEμ, hE, h2, hF1⟩
      have hlgμ : lg (invG (levG μ) μ) < μ := (lg_le hαμ0).trans_lt hαμμ
      rcases hlevle.lt_or_eq with hlt | heq
      · obtain ⟨u, hu⟩ := hX (levG μ + 1) 0
        obtain ⟨huCB, huval⟩ := hu μ hUμ hμ1 (hlimμ.add_one_lt hγμμ) hμ0
        obtain ⟨-, huvalF⟩ := hu F hU hF1 (hlim.add_one_lt (hγμμ.trans h2)) hF0
        have hlt' : X.val s μ < X.val u μ := by
          rw [huval, add_zero, mul_add_one]
          calc X.val s μ ≤ xtOrec X μ := hsμ
            _ = μ * levG μ + lg (invG (levG μ) μ) := hOμ
            _ < μ * levG μ + μ := (add_lt_add_iff_left _).2 hlgμ
        have hF' : X.val s F < X.val u F := by
          by_contra hge
          push Not at hge
          exact absurd ((X.uni_le μ F hUμ hU hBases u s huCB hCBμ).1 hge) (not_le.2 hlt')
        calc X.val s F < X.val u F := hF'
          _ = F * (levG μ + 1) := by rw [huvalF, add_zero]
          _ ≤ F * γ := mul_le_mul_right (Order.add_one_le_of_lt hlt) F
          _ ≤ F * γ + lg α := le_self_add
      · -- level exactly `γ`: `μ = V_γ(α_μ)` with `α₀ < α_μ < α`
        rw [heq] at hVμ hαμ0 hαμμ hlgμ hOμ
        set αμ := invG γ μ with hαμd
        have hαμα : αμ < α := by
          have : VG γ αμ < VG γ α := by rw [hVμ, hV]; exact h2
          exact (VG_strictMono γ).lt_iff_lt.1 this
        have hα0αμ : α0 < αμ := by
          have : VG γ α0 < VG γ αμ := by
            rw [hVμ]; exact ((le_max_left _ _).trans (le_max_right _ _)).trans_lt h1
          exact (VG_strictMono γ).lt_iff_lt.1 this
        have hwin := cdWin hdv hα0αμ (hdec ▸ hαμα)
        have hlgα : lg α < μ := (lg_le hα0).trans_lt hαμ
        obtain ⟨u, hu⟩ := hX γ (lg α)
        obtain ⟨huCB, huval⟩ := hu μ hUμ hμ1 hγμ hlgα
        obtain ⟨-, huvalF⟩ := hu F hU hF1 hγF hlgF
        have hlt' : X.val s μ < X.val u μ := by
          rw [huval]
          calc X.val s μ ≤ xtOrec X μ := hsμ
            _ = μ * γ + lg αμ := hOμ
            _ < μ * γ + lg α := (add_lt_add_iff_left _).2 hwin.1
        have hF' : X.val s F < X.val u F := by
          by_contra hge
          push Not at hge
          exact absurd ((X.uni_le μ F hUμ hU hBases u s huCB hCBμ).1 hge) (not_le.2 hlt')
        rwa [huvalF] at hF'
  · -- the lower bound
    refine le_of_forall_lt fun v hv => ?_
    by_cases hvγ : v < F * γ
    · have hF0' : F ≠ 0 := hF0.ne'
      set q := v / F with hq
      set r := v % F with hr
      have hvqr : F * q + r = v := div_add_mod v F
      have hqγ : q < γ := (lt_mul_iff_div_lt hF0').1 hvγ
      have hrF : r < F := mod_lt v hF0'
      have hqF : q < F := hqγ.trans hγF
      rcases eq_or_ne q 0 with hq0 | hq0
      · rw [hq0, mul_zero, zero_add] at hvqr
        have := lt_xtOrec_of_cof hF hF1 (X.cb_cstI r _ (by rw [hfix]; exact hrF))
          (nn_const_cof (X := X) hF hfix hF1 hrF)
        rwa [X.val_cst, hvqr] at this
      · obtain ⟨s, hs⟩ := hX q r
        have hcof := nn_cof_lin hF hfix hF1 hO hq0 (hbelow q hqγ) hqF hrF s hs
        obtain ⟨hCB, hval⟩ := hs F hU hF1 hqF hrF
        have := lt_xtOrec_of_cof hF hF1 (by rw [hfix]; exact hCB) hcof
        rwa [hfix, hval, hvqr] at this
    · push Not at hvγ
      set d := v - F * γ with hd
      have hdv : F * γ + d = v := Ordinal.add_sub_cancel_of_le hvγ
      have hdlt : d < lg α := (sub_lt_of_le hvγ).2 hv
      have hdF : d < F := hdlt.trans hlgF
      obtain ⟨s, hs⟩ := hX γ d
      have hcof := nn_cof_top hF hfix hF1 hO hγ0 hγF hV hα0 hαF hdlt s hs
      obtain ⟨hCB, hval⟩ := hs F hU hF1 hγF hdF
      have := lt_xtOrec_of_cof hF hF1 (by rw [hfix]; exact hCB) hcof
      rwa [hfix, hval, hdv] at this

/-- **The `Γ`-points**: `F·F ≤ O(F)` at every restart `F < Ω₁` with `υ_F = F` that is a `Γ`-point. -/
theorem nnGam (hX : NnLin X) {F : Ordinal.{0}} (hF : IsRestartIdx F) (hF1 : F < Om1) (hfix : upsilon F = F)
    (hG : IsGP F) : F * F ≤ xtOrec X F := by
  obtain ⟨hE, -, -, -, hU⟩ := nn_fix_facts hF hfix
  have hF0 : 0 < F := hE.pos
  have hO : NnLevBelow X F := fun μ _ hμr hμ1 hμfix hμG => nnLev hX μ hμr hμ1 hμfix hμG
  refine le_of_forall_lt fun v hv => ?_
  have hF0' : F ≠ 0 := hF0.ne'
  set q := v / F with hq
  set r := v % F with hr
  have hvqr : F * q + r = v := div_add_mod v F
  have hqF : q < F := (lt_mul_iff_div_lt hF0').1 hv
  have hrF : r < F := mod_lt v hF0'
  rcases eq_or_ne q 0 with hq0 | hq0
  · rw [hq0, mul_zero, zero_add] at hvqr
    have := lt_xtOrec_of_cof hF hF1 (X.cb_cstI r _ (by rw [hfix]; exact hrF))
      (nn_const_cof (X := X) hF hfix hF1 hrF)
    rwa [X.val_cst, hvqr] at this
  · obtain ⟨s, hs⟩ := hX q r
    have hcof := nn_cof_lin hF hfix hF1 hO hq0 (hG.2 q hqF) hqF hrF s hs
    obtain ⟨hCB, hval⟩ := hs F hU hF1 hqF hrF
    have := lt_xtOrec_of_cof hF hF1 (by rw [hfix]; exact hCB) hcof
    rwa [hfix, hval, hvqr] at this

end Googology.Trans.PoR.InaccPsi.R2.Nn

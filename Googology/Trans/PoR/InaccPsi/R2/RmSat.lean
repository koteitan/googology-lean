import Googology.Trans.PoR.InaccPsi.R2.RlReal
import Googology.Trans.PoR.InaccPsi.R2.RlNoGo

/-!
# The realizer maps of `Rl.RlReal` exist past `a + a`: the base change `a ↦ ρ_μ` on `[a, a·ω^ω)`

`L(ξ) = Nc.ncL S ξ`, `m* = L(0)`, `ρ_λ = υ_λ`, `r(λ) = cdR S λ`, Range = `CdRange`, `B₀ = Cd.cdB0`.
`Cv.CvReal S a t` (one map on the whole of `[a, t)`) forces `t ≤ a + a` (`Rl.rlReal_le`).  This file checks
that the corrected realizer `Rl.RlReal` (one map per finite configuration) has no such obstruction:

* `RmCof S a` (**Range restarts cofinal below `a`**): every `γ < a` lies below some `ρ_μ < a`, `μ` in the
  Range;
* `rmCof_of_real` (**necessary**): `RlReal S a t` with `a < t` gives `RmCof S a` (copy the configuration
  `{a}` with the hidden constant `γ`); `rmCof_of_realCof`;
* the base change `rmD a ρ y = ρ·(y / a) + y mod a` (`a·p + β ↦ ρ·p + β`), with `rmD_eq`, `rmD_add`
  (**it keeps `+` on `{a·p + β : p < ω^ω, β < ρ}`**), `rmD_lt` (strictly increasing), `rmD_inj`,
  `rmD_indec` (it keeps indecomposability);
* `rm_not_le1` (**no proper `≤₁`-left end in `(a, a·ω^ω)`** when `a ∈ E`: such a point is indecomposable,
  so it is `ω^{a+k}` with `1 ≤ k < ω`, and `[C09] Lemma 5.5 (7)(a)` (`exists_indec_of_lt1`) asks for an
  indecomposable point in `(ω^{a+k-1}, ω^{a+k})`, of which there is none);
* `rmReal_lin` (**sufficient**): if `a ∈ E` and `RmCof S a`, then `RlReal S a t` for every
  `t ∈ (a, a·ω^ω]`; `rmReal_iff` (**`RmCof S a ↔ RlReal S a (a·ω^ω)`**); `rmReal_not_cv`: at the same
  target `CvReal` is false, since `a + a < a·ω^ω`;
* the named points: `rmM_cof_iff` (**`RmCof S m* ↔ ρ_{B₀} < m*`**), `rmNamed_need` (**the realizer
  hypotheses `h0`, `hn`, `hw` of `Rl.rlNamed_of_real` give `RmCof` at `m*`, every `L(n+1)` and `L(ω)`,
  hence `ρ_{B₀} < m*`**), `rmM_real` (**`ρ_{B₀} < m*` gives `RlReal S m* (m*·ω^ω)`**).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rm

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rl
  Googology.Trans.PoR.InaccPsi.R2.Cv

/-! ## Arithmetic of `q·p + β` -/

theorem rm_ne_zero {q : Ordinal.{0}} (hq : InE q) : q ≠ 0 := by
  intro h; unfold InE at hq; rw [h, opow_zero] at hq; exact one_ne_zero hq

theorem rm_prin {q : Ordinal.{0}} (hq : InE q) : IsPrincipal (· + ·) q := by
  have := isPrincipal_add_omega0_opow q; unfold InE at hq; rwa [hq] at this

theorem rm_absorb {q β : Ordinal.{0}} (hq : InE q) (hβ : β < q) : β + q = q := by
  unfold InE at hq; rw [← hq] at hβ ⊢; exact add_omega0_opow hβ

/-- `β + q·p = q·p` for `β < q`, `p ≥ 1`. -/
theorem rm_absorb_mul {q β p : Ordinal.{0}} (hq : InE q) (hβ : β < q) (hp : 1 ≤ p) :
    β + q * p = q * p := by
  obtain ⟨p', rfl⟩ := exists_add_of_le hp
  rw [mul_add, mul_one, ← add_assoc, rm_absorb hq hβ]

theorem rm_div {q β : Ordinal.{0}} (hq : q ≠ 0) (hβ : β < q) (p : Ordinal.{0}) : (q * p + β) / q = p := by
  rw [mul_add_div p hq β, div_eq_zero_of_lt hβ, add_zero]

theorem rm_mod {q β : Ordinal.{0}} (hβ : β < q) (p : Ordinal.{0}) : (q * p + β) % q = β := by
  rw [mul_add_mod_self, mod_eq_of_lt hβ]

/-- The lexicographic order of `q·p + β` (`β < q`). -/
theorem rm_lex {q β β' p p' : Ordinal.{0}} (hβ : β < q) (hβ' : β' < q) :
    q * p + β < q * p' + β' ↔ p < p' ∨ (p = p' ∧ β < β') := by
  have key : ∀ {p p' β β' : Ordinal.{0}}, β < q → p < p' → q * p + β < q * p' + β' := by
    intro p p' β β' hb hpp
    calc q * p + β < q * p + q := (add_lt_add_iff_left _).2 hb
      _ = q * (p + 1) := (mul_add_one q p).symm
      _ ≤ q * p' := mul_le_mul_right (Order.add_one_le_of_lt hpp) q
      _ ≤ q * p' + β' := le_self_add
  constructor
  · intro h
    rcases lt_trichotomy p p' with hlt | rfl | hgt
    · exact Or.inl hlt
    · exact Or.inr ⟨rfl, (add_lt_add_iff_left _).1 h⟩
    · exact absurd (key hβ' hgt) (not_lt.2 h.le)
  · rintro (hlt | ⟨rfl, hb⟩)
    · exact key hβ hlt
    · exact (add_lt_add_iff_left _).2 hb

/-- Every `y` is `a·(y / a) + y mod a`. -/
theorem rm_rep (a y : Ordinal.{0}) : y = a * (y / a) + y % a := (div_add_mod y a).symm

/-! ## The base change `a·p + β ↦ ρ·p + β` -/

/-- **The base change** `rmD a ρ y = ρ·(y / a) + y mod a`. -/
noncomputable def rmD (a ρ y : Ordinal.{0}) : Ordinal.{0} := ρ * (y / a) + y % a

/-- The domain of the base change: `{a·p + β : p < ω^ω, β < ρ}`. -/
def RmLv (a ρ : Ordinal.{0}) : Set Ordinal.{0} := {y | y / a < ω ^ ω ∧ y % a < ρ}

theorem rmD_eq {a ρ β : Ordinal.{0}} (ha : a ≠ 0) (hβ : β < a) (p : Ordinal.{0}) :
    rmD a ρ (a * p + β) = ρ * p + β := by
  unfold rmD; rw [rm_div ha hβ, rm_mod hβ]

theorem rmD_small {a ρ x : Ordinal.{0}} (hx : x < a) : rmD a ρ x = x := by
  unfold rmD; rw [div_eq_zero_of_lt hx, mod_eq_of_lt hx, mul_zero, zero_add]

theorem rmD_self {a ρ : Ordinal.{0}} (ha : a ≠ 0) : rmD a ρ a = ρ := by
  unfold rmD; rw [div_self ha, mod_self, mul_one, add_zero]

variable {a ρ : Ordinal.{0}}

theorem rmLv_small {x : Ordinal.{0}} (hρa : ρ ≤ a) (hx : x < ρ) : x ∈ RmLv a ρ := by
  have hxa : x < a := hx.trans_le hρa
  refine ⟨?_, ?_⟩
  · rw [div_eq_zero_of_lt hxa]; exact opow_pos _ omega0_pos
  · rw [mod_eq_of_lt hxa]; exact hx

theorem rm_ww_prin : IsPrincipal (· + ·) ((ω : Ordinal.{0}) ^ ω) := isPrincipal_add_omega0_opow ω

/-- **The base change keeps `+`** on its domain, and the domain is closed under `+`. -/
theorem rmD_add (ha : InE a) (hρ : InE ρ) (hρa : ρ ≤ a) {x y : Ordinal.{0}} (hx : x ∈ RmLv a ρ)
    (hy : y ∈ RmLv a ρ) : x + y ∈ RmLv a ρ ∧ rmD a ρ (x + y) = rmD a ρ x + rmD a ρ y := by
  have ha0 := rm_ne_zero ha
  set p := x / a; set β := x % a; set p' := y / a; set γ := y % a
  have hβ : β < ρ := hx.2
  have hγ : γ < ρ := hy.2
  have hβa : β < a := hβ.trans_le hρa
  have hγa : γ < a := hγ.trans_le hρa
  have ex : x = a * p + β := rm_rep a x
  have ey : y = a * p' + γ := rm_rep a y
  have hDx : rmD a ρ x = ρ * p + β := by rw [ex, rmD_eq ha0 hβa]
  have hDy : rmD a ρ y = ρ * p' + γ := by rw [ey, rmD_eq ha0 hγa]
  rcases eq_or_ne p' 0 with hp0 | hp0
  · -- `y = γ`
    have hβγ : β + γ < ρ := (rm_prin hρ) hβ hγ
    have hβγa : β + γ < a := hβγ.trans_le hρa
    have exy : x + y = a * p + (β + γ) := by rw [ex, ey, hp0, mul_zero, zero_add, add_assoc]
    rw [exy]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [rm_div ha0 hβγa]; exact hx.1
    · rw [rm_mod hβγa]; exact hβγ
    · rw [rmD_eq ha0 hβγa, hDx, hDy, hp0, mul_zero, zero_add, add_assoc]
  · have hp1 : 1 ≤ p' := Order.one_le_iff_ne_zero.2 hp0
    have exy : x + y = a * (p + p') + γ := by
      rw [ex, ey, ← add_assoc, add_assoc (a * p), rm_absorb_mul ha hβa hp1, ← mul_add]
    rw [exy]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [rm_div ha0 hγa]; exact rm_ww_prin hx.1 hy.1
    · rw [rm_mod hγa]; exact hγ
    · rw [rmD_eq ha0 hγa, hDx, hDy, ← add_assoc, add_assoc (ρ * p), rm_absorb_mul hρ hβ hp1, ← mul_add]

/-- **The base change is strictly increasing** on its domain. -/
theorem rmD_lt (hρa : ρ ≤ a) {x y : Ordinal.{0}} (hx : x ∈ RmLv a ρ) (hy : y ∈ RmLv a ρ)
    (hxy : x < y) : rmD a ρ x < rmD a ρ y := by
  have hβa : x % a < a := hx.2.trans_le hρa
  have hγa : y % a < a := hy.2.trans_le hρa
  have ha0 : a ≠ 0 := fun h => by rw [h] at hβa; exact absurd hβa (not_lt.2 zero_le)
  have h := hxy
  rw [rm_rep a x, rm_rep a y, rm_lex hβa hγa] at h
  unfold rmD
  exact (rm_lex hx.2 hy.2).2 h

theorem rmD_inj (hρa : ρ ≤ a) {x y : Ordinal.{0}} (hx : x ∈ RmLv a ρ) (hy : y ∈ RmLv a ρ)
    (h : rmD a ρ x = rmD a ρ y) : x = y := by
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exact absurd h (rmD_lt hρa hx hy hlt).ne
  · exact heq
  · exact absurd h (rmD_lt hρa hy hx hgt).ne'

theorem rm_indec_iff_opow {x : Ordinal.{0}} : Indec x ↔ ∃ e : Ordinal.{0}, x = ω ^ e := by
  rw [indec_iff]
  constructor
  · rintro ⟨h0, hp⟩
    rcases isPrincipal_add_iff_zero_or_omega0_opow.1 hp with h | ⟨e, he⟩
    · exact absurd h h0
    · exact ⟨e, he.symm⟩
  · rintro ⟨e, rfl⟩
    exact ⟨(opow_pos e omega0_pos).ne', isPrincipal_add_omega0_opow e⟩

/-- An indecomposable `y = a·p + β ≥ a` has `β = 0` and `p = ω^e`. -/
theorem rm_indec_form (ha0 : a ≠ 0) {y : Ordinal.{0}} (hay : a ≤ y) (hI : Indec y) :
    y % a = 0 ∧ ∃ e : Ordinal.{0}, y / a = ω ^ e := by
  have ey := rm_rep a y
  have hp0 : y / a ≠ 0 := by
    intro h
    rw [h, mul_zero, zero_add] at ey
    have := mod_lt y ha0
    rw [← ey] at this
    exact absurd hay (not_le.2 this)
  have hpos : 0 < a * (y / a) := mul_pos (pos_iff_ne_zero.2 ha0) (pos_iff_ne_zero.2 hp0)
  have hβ0 : y % a = 0 := by
    by_contra hβ
    apply hI
    refine Or.inr ⟨a * (y / a), y % a, ?_, ?_, ey.symm⟩
    · conv_rhs => rw [ey]
      exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 hβ)
    · exact (mod_lt y ha0).trans_le hay
  refine ⟨hβ0, rm_indec_iff_opow.1 fun hd => hI ?_⟩
  rw [hβ0, add_zero] at ey
  rcases hd with h0 | ⟨u, v, hu, hv, huv⟩
  · exact absurd h0 hp0
  · refine Or.inr ⟨a * u, a * v, ?_, ?_, ?_⟩
    · rw [ey]; exact (mul_lt_mul_iff_right₀ (pos_iff_ne_zero.2 ha0)).2 hu
    · rw [ey]; exact (mul_lt_mul_iff_right₀ (pos_iff_ne_zero.2 ha0)).2 hv
    · rw [ey, ← mul_add, huv]

/-- **The base change keeps indecomposability** (for `ρ ∈ E`). -/
theorem rmD_indec (ha0 : a ≠ 0) (hρ : InE ρ) {y : Ordinal.{0}} (hay : a ≤ y) (hI : Indec y) :
    Indec (rmD a ρ y) := by
  obtain ⟨hβ0, e, he⟩ := rm_indec_form ha0 hay hI
  unfold rmD
  rw [hβ0, add_zero, he]
  have e1 : ρ * ω ^ e = ω ^ (ρ + e) := by
    conv_lhs => rw [← (show ω ^ ρ = ρ from hρ)]
    rw [opow_add]
  rw [e1]
  exact rm_indec_iff_opow.2 ⟨_, rfl⟩

/-- **No proper `≤₁`-left end in `(a, a·ω^ω)`** for `a ∈ E` ([C09] Lemma 5.5 (7)(a) via
`exists_indec_of_lt1`). -/
theorem rm_not_le1 (ha : InE a) {y y' : Ordinal.{0}} (hay : a < y) (hy : y / a < ω ^ ω)
    (hyy : y < y') : ¬ le1 y y' := by
  intro h1
  have ha0 := rm_ne_zero ha
  have hI := indec_of_lt1 h1 hyy
  obtain ⟨hβ0, e, he⟩ := rm_indec_form ha0 hay.le hI
  have ey := rm_rep a y
  rw [hβ0, add_zero, he] at ey
  have he1 : e < ω := by
    rw [he] at hy; exact (opow_lt_opow_iff_right one_lt_omega0).1 hy
  obtain ⟨k, rfl⟩ := lt_omega0.1 he1
  have hk : k ≠ 0 := by
    rintro rfl
    rw [Nat.cast_zero, opow_zero, mul_one] at ey
    exact absurd ey hay.ne'
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hfa : ∀ x : Ordinal.{0}, a * ω ^ x = ω ^ (a + x) := fun x => by
    conv_lhs => rw [← (show ω ^ a = a from ha)]
    rw [opow_add]
  have hlow : a * ω ^ (j : Ordinal.{0}) < y := by
    rw [ey, hfa, hfa]
    exact (opow_lt_opow_iff_right one_lt_omega0).2
      ((add_lt_add_iff_left a).2 (Nat.cast_lt.2 (Nat.lt_succ_self j)))
  obtain ⟨q, hq1, hq2, hqI⟩ := exists_indec_of_lt1 h1 hyy hlow
  obtain ⟨z, rfl⟩ := rm_indec_iff_opow.1 hqI
  rw [hfa] at hq1
  rw [ey, hfa] at hq2
  have h1' := (opow_lt_opow_iff_right one_lt_omega0).1 hq1
  have h2' := (opow_lt_opow_iff_right one_lt_omega0).1 hq2
  rw [Nat.cast_succ, ← add_assoc] at h2'
  exact absurd (Order.lt_add_one_iff.1 h2') (not_le.2 h1')

/-! ## Range restarts cofinal below `a` -/

/-- **Range restarts cofinal below `a`.** -/
def RmCof (S : InaccSeq.{0}) (a : Ordinal.{0}) : Prop :=
  ∀ γ < a, ∃ μ, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < a

variable {S : InaccSeq.{0}}

/-- **`RlReal S a t` (`a < t`) needs Range restarts cofinal below `a`.** -/
theorem rmCof_of_real {t : Ordinal.{0}} (hat : a < t) (h : RlReal S a t) : RmCof S a := by
  classical
  obtain ⟨ι, c, E, D, μ, hca, hE, hex, -, -, -, -, hDwin, hDμ, -⟩ := h
  intro γ hγ
  obtain ⟨C, hsub, hC, hb⟩ := exists_closed ({γ, a} : Finset Ordinal.{0})
  set X := C.filter (· < a)
  set Y := C.filter (fun x => ¬ x < a)
  have hXY : X ∪ Y = C := Finset.filter_union_filter_not_eq _ C
  have hX : ∀ x ∈ X, x < a := fun x hx => (Finset.mem_filter.1 hx).2
  have hYa : ∀ y ∈ Y, y = a := by
    intro y hy
    obtain ⟨hyC, hya⟩ := Finset.mem_filter.1 hy
    obtain ⟨s, hs, hys⟩ := hb y hyC
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact absurd (hys.trans_lt hγ) hya
    · exact le_antisymm hys (not_lt.1 hya)
  have hY : ∀ y ∈ Y, a ≤ y ∧ y < t := fun y hy => by rw [hYa y hy]; exact ⟨le_rfl, hat⟩
  have hcl : Closed ↑(X ∪ Y) := by rw [hXY]; exact hC
  obtain ⟨i, hXi, hYi⟩ := hex X Y hX hY hcl
  have hγX : γ ∈ X := Finset.mem_filter.2 ⟨hsub (by simp), hγ⟩
  have haY : a ∈ Y := Finset.mem_filter.2 ⟨hsub (by simp), lt_irrefl a⟩
  have haE := hYi a haY
  obtain ⟨hr, he, -⟩ := hDμ i
  have hw := hDwin i a haE
  rw [he haE] at hw
  exact ⟨μ i, hr, (hXi γ hγX).trans_le hw.1, hw.2⟩

theorem rmCof_of_realCof {b : Ordinal.{0}} (hab : a < b) (h : RlRealCof S a b) : RmCof S a := by
  obtain ⟨t, hat, -, hR⟩ := h a le_rfl hab
  exact rmCof_of_real hat hR

/-! ## The realizer maps on `[a, a·ω^ω)` -/

theorem rm_ww_lt_inE {u : Ordinal.{0}} (hu : InE u) : (ω : Ordinal.{0}) ^ ω < u := by
  have h := (opow_lt_opow_iff_right one_lt_omega0).2 (omega0_lt_inE hu)
  rwa [show ω ^ u = u from hu] at h

/-- **`RmCof S a` gives realizer maps for every target `t ∈ (a, a·ω^ω]`** (`a ∈ E`): for a configuration
choose a Range restart `ρ_μ` above its constants and its offsets below `a`; the map is the base change
`a·p + β ↦ ρ_μ·p + β`. -/
theorem rmReal_lin {t : Ordinal.{0}} (ha : InE a) (hc : RmCof S a) (ht : t ≤ a * ω ^ ω) :
    RlReal S a t := by
  classical
  have ha0 := rm_ne_zero ha
  have hapos : 0 < a := pos_iff_ne_zero.2 ha0
  have hμ : ∀ i : Shrink.{0} (Iio a), ∃ μ, CdRange S μ ∧ ((equivShrink (Iio a)).symm i).1 < upsilon μ ∧
      upsilon μ < a := fun i => hc _ ((equivShrink (Iio a)).symm i).2
  choose μf hμr hμlo hμhi using hμ
  have hρE : ∀ i, InE (upsilon (μf i)) := fun i =>
    upsPt_inE (upsPt_upsilon (pos_iff_ne_zero.2 (hμr i).1.1))
  have hρa : ∀ i, upsilon (μf i) ≤ a := fun i => (hμhi i).le
  -- the domain of the map at `i`
  have hEdom : ∀ i y, a ≤ y → y < t → y % a < upsilon (μf i) → y ∈ RmLv a (upsilon (μf i)) :=
    fun i y _ hyt hym => ⟨(lt_mul_iff_div_lt ha0).1 (hyt.trans_le ht), hym⟩
  have hDdom : ∀ i x, x ∈ RlDom (upsilon (μf i))
      {y | a ≤ y ∧ y < t ∧ y % a < upsilon (μf i)} → x ∈ RmLv a (upsilon (μf i)) := by
    intro i x hx
    rcases hx with hx | ⟨h1, h2, h3⟩
    · exact rmLv_small (hρa i) hx
    · exact hEdom i x h1 h2 h3
  -- the value on `E_i`: `ρ ≤ D y < min(a, υ_{μ+1})`
  have hval : ∀ i y, a ≤ y → y < t → y % a < upsilon (μf i) →
      upsilon (μf i) ≤ rmD a (upsilon (μf i)) y ∧ rmD a (upsilon (μf i)) y < a ∧
      rmD a (upsilon (μf i)) y < upsilon (μf i + 1) := by
    intro i y hay hyt hym
    set ρ := upsilon (μf i)
    have hp : y / a < ω ^ ω := (lt_mul_iff_div_lt ha0).1 (hyt.trans_le ht)
    have hp1 : 1 ≤ y / a := by
      rw [Order.one_le_iff_ne_zero]
      intro h0
      have := rm_rep a y
      rw [h0, mul_zero, zero_add] at this
      exact absurd (this ▸ mod_lt y ha0) (not_lt.2 hay)
    have hu : InE (upsilon (μf i + 1)) :=
      upsPt_inE (upsPt_upsilon (lt_of_le_of_lt zero_le (lt_add_one _)))
    have hρu : ρ < upsilon (μf i + 1) := upsilon_normal.strictMono (lt_add_one _)
    refine ⟨?_, ?_, ?_⟩
    · unfold rmD
      exact (le_mul_left ρ (lt_of_lt_of_le zero_lt_one hp1)).trans le_self_add
    · unfold rmD
      exact (rm_prin ha) (mul_lt_inE ha (hμhi i) (hp.trans (rm_ww_lt_inE ha)))
        (hym.trans (hμhi i))
    · unfold rmD
      exact (rm_prin hu) (mul_lt_inE hu hρu (hp.trans (rm_ww_lt_inE hu))) (hym.trans hρu)
  refine ⟨Shrink.{0} (Iio a), fun i => upsilon (μf i),
    fun i => {y | a ≤ y ∧ y < t ∧ y % a < upsilon (μf i)}, fun i => rmD a (upsilon (μf i)), μf,
    hμhi, fun i y hy => ⟨hy.1, hy.2.1⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- exhaustion
    intro X Y hX hY _
    set K : Finset Ordinal.{0} := X ∪ Y.image (· % a)
    have hK : ∀ k ∈ K, k < a := by
      intro k hk
      rcases Finset.mem_union.1 hk with hk | hk
      · exact hX k hk
      · obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hk
        exact mod_lt y ha0
    have hγ : K.sup id < a := (Finset.sup_lt_iff hapos).2 hK
    have hlo : K.sup id < upsilon (μf (equivShrink (Iio a) ⟨K.sup id, hγ⟩)) := by
      have h := hμlo (equivShrink (Iio a) ⟨K.sup id, hγ⟩)
      rwa [Equiv.symm_apply_apply] at h
    refine ⟨equivShrink (Iio a) ⟨K.sup id, hγ⟩, fun x hx => ?_,
      fun y hy => ⟨(hY y hy).1, (hY y hy).2, ?_⟩⟩
    · have hxK : x ∈ K := Finset.mem_union_left _ hx
      have hle : x ≤ K.sup id := Finset.le_sup (f := id) hxK
      exact lt_of_le_of_lt hle hlo
    · have hyK : y % a ∈ K := Finset.mem_union_right _ (Finset.mem_image.2 ⟨y, hy, rfl⟩)
      have hle : y % a ≤ K.sup id := Finset.le_sup (f := id) hyK
      exact lt_of_le_of_lt hle hlo
  · -- strictly increasing
    intro i y hy y' hy' hyy
    exact rmD_lt (hρa i) (hEdom i y hy.1 hy.2.1 hy.2.2) (hEdom i y' hy'.1 hy'.2.1 hy'.2.2) hyy
  · -- `+` kept and reflected
    intro i x hx y hy z hz
    have hxL := hDdom i x hx
    have hyL := hDdom i y hy
    have hzL := hDdom i z hz
    obtain ⟨hxyL, hadd⟩ := rmD_add ha (hρE i) (hρa i) hxL hyL
    constructor
    · rintro rfl; exact hadd.symm
    · intro h
      exact rmD_inj (hρa i) hxyL hzL (hadd.trans h)
  · -- decomposability reflected
    intro i y hy hdec
    by_contra hnd
    exact rmD_indec ha0 (hρE i) hy.1 hnd hdec
  · -- identity below `c_i`
    intro i x hx
    exact rmD_small (hx.trans_le (hρa i))
  · -- the window
    intro i y hy
    obtain ⟨h1, h2, -⟩ := hval i y hy.1 hy.2.1 hy.2.2
    exact ⟨h1, h2⟩
  · -- `D_i(a) = ρ_{μ_i}` and the bound by `r(μ_i)`
    intro i
    refine ⟨hμr i, fun _ => rmD_self ha0, fun y hy => ?_⟩
    obtain ⟨-, -, h3⟩ := hval i y hy.1 hy.2.1 hy.2.2
    refine h3.le.trans ((upsilon_normal.strictMono.monotone ?_).trans (cdR_ge S (μf i)))
    exact add_le_add le_self_add le_rfl
  · -- `≤₁`, `≤₂` on the pairs `a < y < y'`: there are none
    intro i y hy y' _ hay hyy
    have hn : ¬ le1 y y' := rm_not_le1 ha hay ((lt_mul_iff_div_lt ha0).1 (hy.2.1.trans_le ht)) hyy
    exact ⟨fun h => absurd h hn, fun h => absurd (le2_le1 h) hn⟩

theorem rm_add_lt_ww (ha : InE a) : a + a < a * ω ^ ω := by
  have ha0 := rm_ne_zero ha
  have e : a * ω ^ ω = ω ^ (a + ω) := by
    conv_lhs => rw [← (show ω ^ a = a from ha)]
    rw [opow_add]
  have hlt : a < a * ω ^ ω :=
    lt_mul_of_one_lt_right (pos_iff_ne_zero.2 ha0) (one_lt_opow.2 ⟨one_lt_omega0, omega0_ne_zero⟩)
  rw [e] at hlt ⊢
  exact isPrincipal_add_omega0_opow _ hlt hlt

/-- **`RmCof S a ↔ RlReal S a (a·ω^ω)`** for `a ∈ E`. -/
theorem rmReal_iff (ha : InE a) : RmCof S a ↔ RlReal S a (a * ω ^ ω) :=
  ⟨fun h => rmReal_lin ha h le_rfl,
    fun h => rmCof_of_real (le_self_add.trans_lt (rm_add_lt_ww ha)) h⟩

/-- **At the same target the global realizer `CvReal` is false** (`Rl.rlReal_le`). -/
theorem rmReal_not_cv (ha : InE a) : ¬ CvReal S a (a * ω ^ ω) := fun h =>
  absurd (rlReal_le h) (not_le.2 (rm_add_lt_ww ha))

/-! ## The named points -/

theorem rm_L_inE (ξ : Ordinal.{0}) : InE (Nc.ncL S ξ) := Low.opow_eq_self_of_SC (Lw.lw_L_SC S ξ)

theorem rm_M_eq : Nc.ncL S 0 = cdMstar S := by
  rw [Lw.lw_L_eq S, mul_zero, add_zero]

/-- `m* = υ_{m*}` (a fixed point of `υ`). -/
theorem rm_M_fix : upsilon (Nc.ncL S 0) = Nc.ncL S 0 := by
  have h := Cv.cvM_GP (S := S)
  rw [Lw.lw_L_eq S, mul_zero, add_zero] at h ⊢
  have e1 := Lw.lw_iota_of_GP h
  have e2 := (Lw.lw_restart_of_GP h).2
  rw [e1] at e2
  exact e2.symm

/-- **`RmCof S a` puts `ρ_{B₀}` below `a`.** -/
theorem rm_B0_lt_of_cof {a : Ordinal.{0}} (h : RmCof S a) (ha : 0 < a) : upsilon cdB0 < a := by
  obtain ⟨μ, hr, -, hlt⟩ := h 0 ha
  exact (upsilon_normal.strictMono.monotone hr.2.1).trans_lt hlt

/-- **`RmCof S m* ↔ ρ_{B₀} < m*`.** -/
theorem rmM_cof_iff : RmCof S (Nc.ncL S 0) ↔ upsilon cdB0 < Nc.ncL S 0 := by
  have hSC := Lw.lw_L_SC S 0
  refine ⟨fun h => rm_B0_lt_of_cof h hSC.1, fun hB γ hγ => ?_⟩
  have hfix := rm_M_fix (S := S)
  have hB' : cdB0 < Nc.ncL S 0 := by
    rw [← hfix] at hB; exact upsilon_normal.strictMono.lt_iff_lt.1 hB
  have hγ' : γ < upsilon (Nc.ncL S 0) := by rw [hfix]; exact hγ
  obtain ⟨ζ, hζ, hγζ⟩ := (upsilon_normal.lt_iff_exists_lt hSC.isSuccLimit).1 hγ'
  set ζ' := max ζ cdB0
  have hζ' : ζ' < Nc.ncL S 0 := max_lt hζ hB'
  have hE := rm_L_inE (S := S) 0
  have hww : (ω : Ordinal.{0}) ^ 2 < Nc.ncL S 0 := by
    have h2 : (ω : Ordinal.{0}) ^ (2 : Ordinal.{0}) < Nc.ncL S 0 := by
      have := (opow_lt_opow_iff_right one_lt_omega0).2
        ((natCast_lt_omega0 2).trans (omega0_lt_inE hE))
      rwa [show ω ^ Nc.ncL S 0 = Nc.ncL S 0 from hE] at this
    have e2 : (ω : Ordinal.{0}) ^ (2 : ℕ) = ω ^ (2 : Ordinal.{0}) := by
      rw [← opow_natCast]; norm_num
    rw [e2]; exact h2
  set μ := (ω : Ordinal.{0}) ^ 2 * (ζ' + 1)
  have hμr : IsRestartIdx μ :=
    ⟨mul_ne_zero (pow_ne_zero 2 omega0_ne_zero) (ne_of_gt (lt_of_le_of_lt zero_le (lt_add_one ζ'))),
      dvd_mul_right _ _⟩
  have hζμ : ζ' < μ := (Order.lt_add_one_iff.2 le_rfl).trans_le
    (le_mul_right (ζ' + 1) (pow_pos omega0_pos 2))
  have hμlt : μ < Nc.ncL S 0 := mul_lt_inE hE hww (hSC.add_one_lt hζ')
  have hBμ : cdB0 ≤ μ := (le_max_right _ _).trans hζμ.le
  have hμM : upsilon μ < Nc.ncL S 0 := by
    rw [← hfix]; exact upsilon_normal.strictMono hμlt
  refine ⟨μ, cdRange_level1 hμr hBμ (by rw [← rm_M_eq]; exact hμM), ?_, hμM⟩
  exact hγζ.trans_le (upsilon_normal.strictMono.monotone ((le_max_left _ _).trans hζμ.le))

/-- **`ρ_{B₀} < m*` gives realizer maps at `m*` for every target in `(m*, m*·ω^ω]`.** -/
theorem rmM_real (hB : upsilon cdB0 < Nc.ncL S 0) {t : Ordinal.{0}} (ht : t ≤ Nc.ncL S 0 * ω ^ ω) :
    RlReal S (Nc.ncL S 0) t :=
  rmReal_lin (rm_L_inE 0) (rmM_cof_iff.2 hB) ht

/-- **What the realizer hypotheses of `Rl.rlNamed_of_real` contain**: Range restarts cofinal below `m*`,
below every `L(n+1)` and below `L(ω)`; in particular `ρ_{B₀} < m*`. -/
theorem rmNamed_need (h0 : RlRealCof S (Nc.ncL S 0) (Nc.ncL S 1))
    (hn : ∀ n : ℕ, RlRealCof S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})))
    (hw : RlRealCof S (Nc.ncL S ω) (Nc.ncL S (ω + 1))) :
    RmCof S (Nc.ncL S 0) ∧ (∀ n : ℕ, RmCof S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))) ∧
      RmCof S (Nc.ncL S ω) ∧ upsilon cdB0 < Nc.ncL S 0 := by
  have hm := rmCof_of_realCof rlM_lt_L1 h0
  refine ⟨hm, fun n => rmCof_of_realCof (Pp.ppL_lt_succ n) (hn n),
    rmCof_of_realCof (Qq.qqL_lt_succ S) hw, rmM_cof_iff.1 hm⟩

end Googology.Trans.PoR.InaccPsi.R2.Rm

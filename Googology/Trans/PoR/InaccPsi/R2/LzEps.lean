import Googology.Trans.PoR.InaccPsi.R2.LyEpR

/-!
# The `ε`-numbers `e_c(x) = ϑˣ(Ω₁ + B(x) + c)` above `B(x)`, `c ≤ x`: enumeration, EXACT, reach, IMG

`B(x) = VzB x` (the least value of `φ(ω, ·)` above `x`, `B(x) = ϑˣ(Ω₁·ω)`).  For a base `x ∈ E ∩ Ω₁` and `c ≤ x`,
`lzE x c := ϑˣ(Ω₁ + (B(x) + c))`.  From the cited facts of `R2.CitedEv`, `R2.CitedVz`, `R2.CitedXt` (no new axiom):

* `lzE_facts` (`e_c(x) ∈ Tˣ ∩ E ∩ (x, Ω₁)`, above `B(x) + c`), `lz_vt_lt_B` (**`ϑˣ(Ω₁ + σ) < B(x)` for `σ < B(x)`**),
  `lzE_strict` (**`c ↦ e_c(x)` is strictly increasing**), `lzE_enum` (**every `ε`-number in `(B(x), e_c(x))` is some
  `e_{c'}(x)`, `c' < c`**: [W07a] Lemma 3.30 through `vt_rep`, `vt_E_iff`, `vt_lt_Om1_add`, Convention 4.1 through
  `vzRem_T`);
* `lzE_zero` (**`e_0(x) = ε_{B(x)+1}`**), `lzE_succ` (**`e_{c+1}(x) = ε_{e_c(x)+1}`**);
* `lzE_pi` (**Lemma EXACT**: `e_c(ρ) ∈ Tᵖ[σ]`, `π_{σ,ρ}(e_c(ρ)) = e_c(σ)` for `c < σ`: [W07a] Def 5.1 fourth clause
  `pi_vt_two`, `pi_add`, `pi_Om1`, `xtPiB`);
* `lzE_lt_ups` (`e_c(x)` lies below every `<₁ ∞`-point above `x`), `lzE_lh` (**the `R₁⁺`-reach**:
  `lh(e_c(x)) = e_c(x)·2 + logend(c)` for `c ≠ 0`, [W07b] Thm 5.3 with Def 4.1 as `lhT_Om1_add`), `lzE_lh0`
  (`lh(e_0(x)) = e_0(x)·2`, through `vz_lh_th_fix`);
* `lzE_img0`, `lzE_imgAll`, `lzE_imgTop` (**Lemma IMG for `e_c`**: every covering copy `f` has
  `e_c(f(ρ)) ≤ f(e_c(ρ))`, for `c = 0`, for `0 < c < ρ` from the IMG of `e_{c₀}` (`c = c₀ + ω^g`), and for the top
  `c = ρ`; the copy keeps `e ≤₁ e·2 + g` of `R₁⁺`, and an `ε`-number `e_{c'}(f(ρ))` strictly below `e_c(f(ρ))` has the
  smaller reach `e_{c'}·2 + logend(c')`).

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lz

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt

/-- `e_c(x) = ϑˣ(Ω₁ + (B(x) + c))`. -/
noncomputable def lzE (x c : Ordinal.{0}) : Ordinal.{0} := vt x (Om1 + (VzB x + c))

/-- `logend(b + c) = logend(c)` for an `ε`-number `b` and `0 < c < b`. -/
theorem lz_lg_add {b c : Ordinal.{0}} (hb : InE b) (hc0 : c ≠ 0) (hcb : c < b) : lg (b + c) = lg c := by
  have hbc0 : b + c ≠ 0 := (lt_of_lt_of_le (pos_iff_ne_zero.2 hc0) le_add_self).ne'
  have key : ∀ k, k ≤ b → (ω ^ k ∣ b + c ↔ ω ^ k ∣ c) := fun k hk =>
    (Ordinal.dvd_add_iff (opow_dvd_of_inE hb hk))
  have hlgc : lg c ≤ b := (lg_le hc0).trans hcb.le
  have hlgbc : lg (b + c) ≤ b := by
    by_contra hgt
    push Not at hgt
    have h1 : ω ^ lg (b + c) ≤ b + c := Ordinal.le_of_dvd hbc0 (lg_dvd hbc0)
    have h2 : b + c < ω ^ (b + 1) := by
      rw [opow_add_one, show ω ^ b = b from hb]
      calc b + c < b + b := (add_lt_add_iff_left _).2 hcb
        _ = b * 2 := (Ordinal.mul_two _).symm
        _ < b * ω := (mul_lt_mul_iff_right₀ hb.pos).2 (by exact_mod_cast natCast_lt_omega0 2)
    have h3 : ω ^ (b + 1) ≤ ω ^ lg (b + c) := opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hgt)
    exact absurd (h1.trans_lt (h2.trans_le h3)) (lt_irrefl _)
  refine le_antisymm ?_ ?_
  · exact (le_lg_iff hc0 _).2 ((key _ hlgbc).1 (lg_dvd hbc0))
  · exact (le_lg_iff hbc0 _).2 ((key _ hlgc).2 (lg_dvd hc0))

section Facts

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem lz_BT : VzB x ∈ Tset x := by
  have := (vz_w_facts hx hx1).1
  rwa [vz_vt_w_eq hx hx1] at this

theorem lz_BcT {c : Ordinal.{0}} (hc : c ≤ x) : VzB x + c ∈ Tset x ∧ VzB x + c < Om1 :=
  ⟨vzT_add hx hx1 (lz_BT hx hx1) (mem_T_of_le hx hx1 hc),
    Om1_add_lt (xt_B_lt_Om1 hx hx1) (lt_of_le_of_lt hc hx1)⟩

/-- The facts on `e_c(x)`. -/
theorem lzE_facts {c : Ordinal.{0}} (hc : c ≤ x) :
    Om1 + (VzB x + c) ∈ Tset x ∧ Om1 + (VzB x + c) < OmTwo ∧ lzE x c ∈ Tset x ∧ x < lzE x c ∧
      lzE x c < Om1 ∧ InE (lzE x c) ∧ Indec (lzE x c) ∧ VzB x + c < lzE x c := by
  obtain ⟨hT, h1⟩ := lz_BcT hx hx1 hc
  have hγT := (Om1_add_T hx hx1 hT h1).1
  have hγ2 := Om1_add_lt_OmTwo h1
  obtain ⟨hvT, -, hv1, hvP, -⟩ := vt_memTwo hx hx1 hγT hγ2
  have hE := (vt_E_iff hx hx1 hγT hγ2).2 le_self_add
  exact ⟨hγT, hγ2, hvT, hE.1, hv1, hE.2, hvP, lt_vt_Om1_add hx hx1 hT h1⟩

theorem lzE_B_lt {c : Ordinal.{0}} (hc : c ≤ x) : VzB x < lzE x c :=
  lt_of_le_of_lt le_self_add (lzE_facts hx hx1 hc).2.2.2.2.2.2.2

/-- **`ϑˣ(Ω₁ + σ) < B(x)` for `σ < B(x)`.** -/
theorem lz_vt_lt_B {σ : Ordinal.{0}} (hσ : σ < VzB x) : vt x (Om1 + σ) < VzB x := by
  have hB1 := xt_B_lt_Om1 hx hx1
  have hσT : σ ∈ Tset x := vz_T_down hx hx1 (lz_BT hx hx1) hB1 hσ.le
  have hσ1 : σ < Om1 := hσ.trans hB1
  obtain ⟨N, hN⟩ := vzB_lt_iff.1 hσ
  set M := max N 2 with hM
  have hσM : σ < vt x (Om1 * (M : Ordinal.{0}) + 0) := hN.trans_le (vzN_le hx hx1 (le_max_left N 2))
  have h0T := mem_T_of_le hx hx1 (zero_le : (0 : Ordinal.{0}) ≤ x)
  have hlt : Om1 * ((1 : ℕ) : Ordinal.{0}) + σ < Om1 * (M : Ordinal.{0}) + 0 := by
    rw [add_zero, Nat.cast_one, mul_one]
    calc Om1 + σ < Om1 + Om1 := (add_lt_add_iff_left _).2 hσ1
      _ = Om1 * 2 := (Ordinal.mul_two _).symm
      _ ≤ Om1 * (M : Ordinal.{0}) := mul_le_mul_right (by exact_mod_cast le_max_right N 2) _
  have := vzVt_lt hx hx1 hσT hσ1 h0T (Ordinal.omega_pos 1) hlt hσM
  rw [Nat.cast_one, mul_one] at this
  exact this.trans_le (vzN_le_B x M)

/-- `B(x) + c < ε_{B(x)+1}` for `c ≤ x`. -/
theorem lz_Bc_lt_eN {c : Ordinal.{0}} (hc : c ≤ x) : VzB x + c < eN (VzB x) := by
  have hBE := xt_B_E hx hx1
  have hxB := (vzB_omega hx hx1).2.1
  exact (inE_indec (eN_E _)).add_lt (lt_eN _) ((lt_of_le_of_lt hc hxB).trans (lt_eN _))

/-- **`c ↦ e_c(x)` is strictly increasing** on `[0, x]`. -/
theorem lzE_strict {c c' : Ordinal.{0}} (h : c < c') (hc' : c' ≤ x) : lzE x c < lzE x c' := by
  obtain ⟨hT, -⟩ := lz_BcT hx hx1 (h.le.trans hc')
  obtain ⟨hT', h1'⟩ := lz_BcT hx hx1 hc'
  have hlt : VzB x + c < VzB x + c' := (add_lt_add_iff_left _).2 h
  exact vt_Om1_add_lt hx hx1 hT hT' h1' hlt (hlt.trans (lzE_facts hx hx1 hc').2.2.2.2.2.2.2)

theorem lzE_mono {c c' : Ordinal.{0}} (h : c ≤ c') (hc' : c' ≤ x) : lzE x c ≤ lzE x c' := by
  rcases h.lt_or_eq with h | rfl
  · exact (lzE_strict hx hx1 h hc').le
  · exact le_rfl

/-- **Every `ε`-number strictly between `B(x)` and `e_c(x)` is some `e_{c'}(x)`, `c' < c`.** -/
theorem lzE_enum {c α : Ordinal.{0}} (hc : c ≤ x) (hαE : InE α) (hBα : VzB x < α) (hαc : α < lzE x c) :
    ∃ c', c' < c ∧ α = lzE x c' := by
  obtain ⟨-, -, heT, -, he1, -, -, -⟩ := lzE_facts hx hx1 hc
  obtain ⟨hBcT, hBc1⟩ := lz_BcT hx hx1 hc
  have hxB := (vzB_omega hx hx1).2.1
  have hα1 : α < Om1 := hαc.trans he1
  have hαT : α ∈ Tset x := vz_T_down hx hx1 heT he1 hαc.le
  have hxα : x < α := hxB.trans hBα
  obtain ⟨ξ, hξT, hξ2, hξα⟩ := vt_rep hx hx1 hαT hxα.le hα1 (inE_indec hαE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξα]; exact hxα, by rw [hξα]; exact hαE⟩
  have hBcα : VzB x + c < α := (lz_Bc_lt_eN hx hx1 hc).trans_le (eN_le hBα hαE)
  have hξlt : ξ < Om1 + (VzB x + c) :=
    vt_lt_Om1_add hx hx1 hξT hξ2 hBcT hBc1 (by rw [hξα]; exact hBcα) (by rw [hξα]; exact hαc)
  set η := ξ - Om1 with hη
  have hξe : Om1 + η = ξ := Ordinal.add_sub_cancel_of_le hΩξ
  have hηlt : η < VzB x + c := (add_lt_add_iff_left Om1).1 (by rw [hξe]; exact hξlt)
  have hη1 : η < Om1 := hηlt.trans hBc1
  have hηT : η ∈ Tset x := vzRem_T hx hx1 hξT hξ2 hξe.symm (dvd_refl _) hη1
  rcases lt_or_ge η (VzB x) with hηB | hBη
  · exfalso
    have := lz_vt_lt_B hx hx1 hηB
    rw [hξe, hξα] at this
    exact absurd hBα (not_lt.2 this.le)
  · refine ⟨η - VzB x, ?_, ?_⟩
    · have e := Ordinal.add_sub_cancel_of_le hBη
      exact (add_lt_add_iff_left (VzB x)).1 (by rw [e]; exact hηlt)
    · rw [lzE, Ordinal.add_sub_cancel_of_le hBη, hξe, hξα]

/-- **`e_0(x) = ε_{B(x)+1}`.** -/
theorem lzE_zero : lzE x 0 = eN (VzB x) := by
  obtain ⟨-, -, -, -, -, heE, -, -⟩ := lzE_facts hx hx1 (zero_le : (0 : Ordinal.{0}) ≤ x)
  refine le_antisymm ?_ (eN_le (lzE_B_lt hx hx1 zero_le) heE)
  by_contra hlt
  push Not at hlt
  obtain ⟨c', hc', -⟩ := lzE_enum hx hx1 zero_le (eN_E _) (lt_eN _) hlt
  exact absurd hc' (not_lt.2 zero_le)

/-- **`e_{c+1}(x) = ε_{e_c(x)+1}`.** -/
theorem lzE_succ {c : Ordinal.{0}} (hc : c < x) : lzE x (c + 1) = eN (lzE x c) := by
  have hc1 : c + 1 ≤ x := Order.add_one_le_of_lt hc
  obtain ⟨-, -, -, -, -, heE, -, -⟩ := lzE_facts hx hx1 hc1
  have hlt := lzE_strict hx hx1 (lt_add_one c) hc1
  refine le_antisymm ?_ (eN_le hlt heE)
  by_contra hlt'
  push Not at hlt'
  have hB : VzB x < eN (lzE x c) := (lzE_B_lt hx hx1 hc.le).trans (lt_eN _)
  obtain ⟨c', hc', he⟩ := lzE_enum hx hx1 hc1 (eN_E _) hB hlt'
  have hc'c : c' ≤ c := Order.lt_add_one_iff.1 hc'
  have := lzE_mono hx hx1 hc'c hc.le
  rw [← he] at this
  exact absurd (lt_eN (lzE x c)) (not_lt.2 this)

/-- `e_c(x)` lies below every `<₁ ∞`-point above `x`. -/
theorem lzE_lt_ups {c u : Ordinal.{0}} (hc : c ≤ x) (hxu : x < u) (hu : LtInf1 u) : lzE x c < u := by
  obtain ⟨m, -, -, hmin, hTm, -⟩ := T_next (Or.inr hx) hx1
  obtain ⟨-, -, heT, -, he1, -, -, -⟩ := lzE_facts hx hx1 hc
  exact ((hTm _ he1).1 heT).trans_le (hmin u hxu hu)

/-- **The `R₁⁺`-reach of `e_c(x)`** (`c ≠ 0`): `lh(e_c(x)) = e_c(x)·2 + logend(c)`. -/
theorem lzE_lh {c : Ordinal.{0}} (hc0 : c ≠ 0) (hc : c ≤ x) :
    IsLh1 (lzE x c) (lzE x c * 2 + lg c) := by
  obtain ⟨-, -, heT, hxe, he1, -, heP, -⟩ := lzE_facts hx hx1 hc
  obtain ⟨hT, h1⟩ := lz_BcT hx hx1 hc
  have hxB := (vzB_omega hx hx1).2.1
  have hBc0 : VzB x + c ≠ 0 := (lt_of_lt_of_le (xt_B_E hx hx1).pos le_self_add).ne'
  have hlim : ∃ σ, σ < VzB x + c ∧ VzB x + c < vt x (Om1 + σ) := by
    refine ⟨VzB x, lt_add_of_pos_right _ (pos_iff_ne_zero.2 hc0), ?_⟩
    have := lz_Bc_lt_eN hx hx1 hc
    rwa [← lzE_zero hx hx1, lzE, add_zero] at this
  have h := lh_eq_lhT (Or.inr hx) hx1 heT hxe he1 heP
  unfold lzE at h ⊢
  rw [lhT_Om1_add hx hx1 hT h1 hBc0 hlim,
    lz_lg_add (xt_B_E hx hx1) hc0 (lt_of_le_of_lt hc hxB)] at h
  exact h

/-- `lh(e_0(x)) = e_0(x)·2`. -/
theorem lzE_lh0 : IsLh1 (lzE x 0) (lzE x 0 * 2) := by
  have hB1 := xt_B_lt_Om1 hx hx1
  have hfix : ∀ σ, σ < VzB x → vt x (Om1 * ((1 : ℕ) : Ordinal.{0}) + σ) ≤ VzB x := fun σ hσ => by
    rw [Nat.cast_one, mul_one]; exact (lz_vt_lt_B hx hx1 hσ).le
  have h := vz_lh_th_fix hx hx1 le_rfl (lz_BT hx hx1) hB1 hfix
  have e1 : Om1 * ((1 : ℕ) : Ordinal.{0}) + VzB x = Om1 + (VzB x + 0) := by
    rw [Nat.cast_one, mul_one, add_zero]
  have e2 : ((1 + 1 : ℕ) : Ordinal.{0}) = 2 := by norm_num
  rw [e1, e2] at h
  exact h

end Facts

/-! ## Lemma EXACT -/

/-- **Lemma EXACT for `e_c`**: for bases `σ < ρ` and `c < σ`, `e_c(ρ) ∈ Tᵖ[σ]` and `π_{σ,ρ}(e_c(ρ)) = e_c(σ)`. -/
theorem lzE_pi {σ ρ c : Ordinal.{0}} (hB : Bases σ ρ) (hc : c < σ) :
    lzE ρ c ∈ TB ρ σ ∧ pi σ ρ (lzE ρ c) = lzE σ c := by
  have hρE := hB.2.1
  have hρ1 := hB.2.2.2
  obtain ⟨h1, h2⟩ := xtPiB hB
  obtain ⟨h3, h4⟩ := pi_add hB h1 (mem_TB_of_lt hB hc)
  rw [h2, pi_lt hB hc] at h4
  obtain ⟨hO, hpO⟩ := pi_Om1 hB
  obtain ⟨h5, h6⟩ := pi_add hB hO h3
  rw [hpO, h4] at h6
  have hc' : c ≤ ρ := (hc.trans hB.2.2.1).le
  obtain ⟨-, hγ2, -, -, -, -, -, -⟩ := lzE_facts hρE hρ1 hc'
  obtain ⟨hvT, -, -, -, hvP⟩ := vt_memTwo hρE hρ1 h5.1 hγ2
  unfold lzE
  refine ⟨⟨hvT, by rw [hvP]; exact h5.2⟩, ?_⟩
  rw [pi_vt_two hB h5 hγ2, h6]


/-! ## Lemma IMG for `e_c` -/

theorem lz_lg_self {x : Ordinal.{0}} (hx : InE x) : lg x = x :=
  le_antisymm (lg_le hx.pos.ne') ((le_lg_iff hx.pos.ne' x).2 (by rw [show ω ^ x = x from hx]))

namespace LzK

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

theorem lzE_lt_δ {c : Ordinal.{0}} (hc : c ≤ ρ) : lzE ρ c < δ :=
  lzE_lt_ups h.ρE h.ρ1 hc h.ρδ h.next.2.1.2

/-- **The witness pair of `e_0(ρ) = ε_{B(ρ)+1}`**: every copy has `f(e_0(ρ))` an `ε`-number `≥ e_0(f(ρ))`. -/
theorem lzE_img0 : ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ lzE ρ 0 ∈ W ∧ (0 : Ordinal.{0}) ∈ Z ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      lzE (f ρ) 0 ≤ f (lzE ρ 0) := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  set e := lzE ρ 0 with hedef
  obtain ⟨-, -, -, -, -, heE, -, -⟩ := lzE_facts hρE hρ1 (zero_le : (0 : Ordinal.{0}) ≤ ρ)
  have hBe : VzB ρ < e := lzE_B_lt hρE hρ1 zero_le
  have hρB := (vzB_omega hρE hρ1).2.1
  have heδ : e < δ := lzE_lt_δ h zero_le
  have hδI := inE_indec h.δE
  have hee : e + e < δ := hδI.add_lt heδ heδ
  obtain ⟨hwB, -, hIB⟩ := xtWitB h
  have hw : WZ ρ δ (insert (e + e) (insert e {VzB ρ * ω, VzB ρ, ρ})) {0} := by
    have w0 : WZ ρ δ {VzB ρ * ω, VzB ρ, ρ} {0} := by
      have := hwB.insZ hρE.pos; simpa using this
    have w1 := w0.insW (hρB.trans hBe).le heδ (Or.inl (inE_indec heE))
    exact w1.insW ((hρB.trans hBe).le.trans le_self_add) hee
      (Or.inr ⟨e, by simp, e, by simp, lt_add_of_pos_right _ heE.pos, lt_add_of_pos_right _ heE.pos, rfl⟩)
  refine ⟨_, _, hw, by simp, by simp, fun A f hW hZ C => ?_⟩
  have heA : e ∈ A := hW (by simp)
  have heeA : e + e ∈ A := hW (by simp)
  have hWB : ↑({VzB ρ * ω, VzB ρ, ρ} : Finset Ordinal.{0}) ⊆ A := fun x hx =>
    hW (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_coe.1 hx))))
  have hBA : VzB ρ ∈ A := hWB (by simp)
  obtain ⟨-, hfB⟩ := hIB A f hWB (by simp) C
  have hsrc : le1 e (e + e) := by
    refine (h.lowδ e (e + e) (hρB.trans hBe) hee.le).2 ?_
    rw [← mul_two_eq]; exact (le1R_two_iff heE.pos).2 heE
  have himg : le1 (f e) (f e + f e) := by
    have := C.cov1 e heA (e + e) heeA hsrc
    rwa [← C.add e heA e heA (e + e) heeA rfl] at this
  have hfBe : f (VzB ρ) < f e := C.mono hBA heA hBe
  have hfE : InE (f e) := by
    by_cases hU : UpsPt (f e)
    · exact upsPt_inE hU
    · have hR := (C.sk (f e) (C.low e heA) hU (f e + f e)).1 himg
      have hpos : 0 < f e := lt_of_le_of_lt zero_le hfBe
      rw [← mul_two_eq] at hR
      exact (le1R_two_iff hpos).1 hR
  have hy := upsPt_inE C.ups
  have hy1 : f ρ < Om1 := (C.low ρ C.rho).trans hρ1
  rw [lzE_zero hy hy1]
  exact eN_le (hfB.trans_lt hfBe) hfE

/-- The common part of the copies of `e_c(ρ)` for `0 < c ≤ ρ`: `f(e_c(ρ))` is a `υ`-point, or an `ε`-number above
`B(f(ρ))` with `f(e) ≤₁ f(e)·2 + f(g)` in `R₁⁺`, from the source atom `e ≤₁ e·2 + g`. -/
theorem lzE_copy {c g : Ordinal.{0}} (hc0 : c ≠ 0) (hc : c ≤ ρ) (hg : g ≤ lg c) (hgρ : g ≤ ρ)
    {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (C : ImgCtx ρ A f)
    (heA : lzE ρ c ∈ A) (heeA : lzE ρ c + lzE ρ c ∈ A) (hgA : g ∈ A)
    (hegA : lzE ρ c + lzE ρ c + g ∈ A) (hBA : VzB ρ ∈ A) (hfB : VzB (f ρ) ≤ f (VzB ρ)) :
    UpsPt (f (lzE ρ c)) ∨ (InE (f (lzE ρ c)) ∧ VzB (f ρ) < f (lzE ρ c) ∧
      le1R (f (lzE ρ c)) (f (lzE ρ c) + f (lzE ρ c) + f g)) := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  set e := lzE ρ c with hedef
  have hρe : ρ < e := (vzB_omega hρE hρ1).2.1.trans (lzE_B_lt hρE hρ1 hc)
  have heδ : e < δ := lzE_lt_δ h hc
  have hδI := inE_indec h.δE
  have hgδ : g < δ := lt_of_le_of_lt hgρ h.ρδ
  have hsrcR : le1R e (e + e + g) := by
    have hl := lzE_lh hρE hρ1 hc0 hc
    rw [mul_two_eq] at hl
    exact le1R_of_le (le_self_add.trans le_self_add) (add_le_add le_rfl hg) hl.1
  have hsrc : le1 e (e + e + g) :=
    (h.lowδ e _ hρe (hδI.add_lt (hδI.add_lt heδ heδ) hgδ).le).2 hsrcR
  have himg : le1 (f e) (f e + f e + f g) := by
    have := C.cov1 e heA _ hegA hsrc
    rwa [← C.add (e + e) heeA g hgA _ hegA rfl, ← C.add e heA e heA (e + e) heeA rfl] at this
  have hfBe : f (VzB ρ) < f e := C.mono hBA heA (lzE_B_lt hρE hρ1 hc)
  by_cases hU : UpsPt (f e)
  · exact Or.inl hU
  · have hR := (C.sk (f e) (C.low e heA) hU _).1 himg
    have hpos : 0 < f e := lt_of_le_of_lt zero_le hfBe
    have h2 : le1R (f e) (f e * 2) := le1R_of_le (by rw [mul_two_eq]; exact le_self_add)
      (by rw [mul_two_eq]; exact le_self_add) hR
    exact Or.inr ⟨(le1R_two_iff hpos).1 h2, hfB.trans_lt hfBe, hR⟩

/-- **Lemma IMG for every `e_c(ρ)`, `c < ρ`**: witness sets (with `c` among the constants) such that every covering
copy `f` has `e_c(f(ρ)) ≤ f(e_c(ρ))`. -/
theorem lzE_imgAll : ∀ c, c < ρ → ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ lzE ρ c ∈ W ∧ c ∈ Z ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      lzE (f ρ) c ≤ f (lzE ρ c) := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hδI := inE_indec h.δE
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc
  rcases eq_or_ne c 0 with rfl | hc0
  · exact lzE_img0 h
  obtain ⟨c0, hcs, hdv, hc0c⟩ := lg_split hc0
  set g := lg c with hgdef
  have hgc : g ≤ c := lg_le hc0
  have hgρ : g < ρ := lt_of_le_of_lt hgc hc
  obtain ⟨W0, Z0, hw0, he0W, -, hI0⟩ := IH c0 hc0c (hc0c.trans hc)
  obtain ⟨hwB, -, hIB⟩ := xtWitB h
  set e := lzE ρ c with hedef
  obtain ⟨-, -, -, -, -, heE, heI, -⟩ := lzE_facts hρE hρ1 hc.le
  have hρB := (vzB_omega hρE hρ1).2.1
  have hρe : ρ < e := hρB.trans (lzE_B_lt hρE hρ1 hc.le)
  have heδ : e < δ := lzE_lt_δ h hc.le
  have hee : e + e < δ := hδI.add_lt heδ heδ
  have heeg : e + e + g < δ := hδI.add_lt hee (hgρ.trans h.ρδ)
  set WB : Finset Ordinal.{0} := {VzB ρ * ω, VzB ρ, ρ} with hWB
  set Z : Finset Ordinal.{0} := insert g (insert c Z0) with hZdef
  have w0 : WZ ρ δ (W0 ∪ WB) Z := ((hw0.union hwB).insZ hc).insZ hgρ |> fun w => by
    simpa [hZdef] using w
  have w1 : WZ ρ δ (insert (e + e) (insert e (W0 ∪ WB))) Z := by
    have := w0.insW hρe.le heδ (Or.inl heI)
    exact this.insW (hρe.le.trans le_self_add) hee
      (Or.inr ⟨e, by simp, e, by simp, lt_add_of_pos_right _ heE.pos, lt_add_of_pos_right _ heE.pos, rfl⟩)
  have w2 : WZ ρ δ (insert (e + e + g) (insert (e + e) (insert e (W0 ∪ WB)))) Z := by
    rcases eq_or_ne g 0 with hg0 | hg0
    · rw [hg0, add_zero, Finset.insert_eq_of_mem (Finset.mem_insert_self _ _)]
      exact w1
    · refine w1.insW ((hρe.le.trans le_self_add).trans le_self_add) heeg
        (Or.inr ⟨e + e, by simp, g, by simp [hZdef], lt_add_of_pos_right _ (pos_iff_ne_zero.2 hg0), ?_, rfl⟩)
      exact (hgρ.trans (hρe.trans_le le_self_add)).trans_le le_self_add
  refine ⟨_, Z, w2, by simp, by simp [hZdef], fun A f hW hZ C => ?_⟩
  have heA : e ∈ A := hW (by simp)
  have heeA : e + e ∈ A := hW (by simp)
  have hegA : e + e + g ∈ A := hW (by simp)
  have hgA : g ∈ A := hZ (by simp [hZdef])
  have hcA : c ∈ A := hZ (by simp [hZdef])
  have hW0 : ↑W0 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hZ0 : ↑Z0 ⊆ A := fun x hx => hZ (by simp [hZdef, Finset.mem_coe.1 hx])
  have hWBA : ↑WB ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hBA : VzB ρ ∈ A := hWBA (by simp [hWB])
  obtain ⟨-, hfB⟩ := hIB A f hWBA (by simp) C
  have hy := upsPt_inE C.ups
  have hy1 : f ρ < Om1 := (C.low ρ C.rho).trans hρ1
  have hcy : c < f ρ := C.above c hcA hc
  have hfg : f g = g := C.fix g hgA hgρ
  have hρeA : f ρ < f e := C.mono C.rho heA hρe
  rcases lzE_copy h hc0 hc.le le_rfl hgρ.le C heA heeA hgA hegA hBA hfB with hU | ⟨hαE, hBα, hR⟩
  · exact (lzE_lt_ups hy hy1 hcy.le hρeA hU.2).le
  rw [hfg] at hR
  by_contra hlt
  push Not at hlt
  obtain ⟨c1, hc1c, hα⟩ := lzE_enum hy hy1 hcy.le hαE hBα hlt
  have he0A : lzE ρ c0 ∈ A := hW0 (Finset.mem_coe.2 he0W)
  have hlow : lzE (f ρ) c0 < f e :=
    (hI0 A f hW0 hZ0 C).trans_lt (C.mono he0A heA (lzE_strict hρE hρ1 hc0c hc.le))
  have hc01 : c0 < c1 := by
    by_contra hle
    push Not at hle
    have := lzE_mono hy hy1 hle (hc0c.trans hcy).le
    rw [← hα] at this
    exact absurd hlow (not_lt.2 this)
  have hc1ne : c1 ≠ 0 := (lt_of_le_of_lt zero_le hc01).ne'
  have hl := lzE_lh hy hy1 hc1ne (hc1c.trans hcy).le
  rw [← hα, mul_two_eq] at hl
  have hgl : g ≤ lg c1 := (add_le_add_iff_left _).1 (hl.2 _ hR)
  have hdv1 : ω ^ g ∣ c1 := (le_lg_iff hc1ne g).1 hgl
  have := dvd_next hdv1 hdv hc01
  rw [← hcs] at this
  exact absurd hc1c (not_lt.2 this)

/-- **Lemma IMG for the top `e_ρ(ρ) = ϑᵖ(Ω₁ + B(ρ) + ρ)`**: every covering copy `f` has `e_{f(ρ)}(f(ρ)) ≤ f(e_ρ(ρ))`. -/
theorem lzE_imgTop : ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ lzE ρ ρ ∈ W ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      lzE (f ρ) (f ρ) ≤ f (lzE ρ ρ) := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hδI := inE_indec h.δE
  obtain ⟨hwB, -, hIB⟩ := xtWitB h
  set e := lzE ρ ρ with hedef
  obtain ⟨-, -, -, -, -, heE, heI, -⟩ := lzE_facts hρE hρ1 le_rfl
  have hρB := (vzB_omega hρE hρ1).2.1
  have hρe : ρ < e := hρB.trans (lzE_B_lt hρE hρ1 le_rfl)
  have heδ : e < δ := lzE_lt_δ h le_rfl
  have hee : e + e < δ := hδI.add_lt heδ heδ
  have heeg : e + e + ρ < δ := hδI.add_lt hee h.ρδ
  set WB : Finset Ordinal.{0} := {VzB ρ * ω, VzB ρ, ρ} with hWB
  have w1 : WZ ρ δ (insert (e + e) (insert e WB)) ∅ := by
    have := hwB.insW hρe.le heδ (Or.inl heI)
    exact this.insW (hρe.le.trans le_self_add) hee
      (Or.inr ⟨e, by simp, e, by simp, lt_add_of_pos_right _ heE.pos, lt_add_of_pos_right _ heE.pos, rfl⟩)
  have w2 : WZ ρ δ (insert (e + e + ρ) (insert (e + e) (insert e WB))) ∅ :=
    w1.insW ((hρe.le.trans le_self_add).trans le_self_add) heeg
      (Or.inr ⟨e + e, by simp, ρ, by simp [hWB], lt_add_of_pos_right _ hρE.pos,
        (hρe.trans_le le_self_add).trans_le le_self_add, rfl⟩)
  refine ⟨_, ∅, w2, by simp, fun A f hW hZ C => ?_⟩
  have heA : e ∈ A := hW (by simp)
  have heeA : e + e ∈ A := hW (by simp)
  have hegA : e + e + ρ ∈ A := hW (by simp)
  have hWBA : ↑WB ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hBA : VzB ρ ∈ A := hWBA (by simp [hWB])
  obtain ⟨-, hfB⟩ := hIB A f hWBA (by simp) C
  have hy := upsPt_inE C.ups
  have hy1 : f ρ < Om1 := (C.low ρ C.rho).trans hρ1
  have hρeA : f ρ < f e := C.mono C.rho heA hρe
  rcases lzE_copy h hρE.pos.ne' le_rfl (lz_lg_self hρE).ge le_rfl C heA heeA C.rho hegA hBA hfB with
    hU | ⟨hαE, hBα, hR⟩
  · exact (lzE_lt_ups hy hy1 le_rfl hρeA hU.2).le
  by_contra hlt
  push Not at hlt
  obtain ⟨c1, hc1y, hα⟩ := lzE_enum hy hy1 le_rfl hαE hBα hlt
  rcases eq_or_ne c1 0 with rfl | hc1ne
  · have hl := lzE_lh0 hy hy1
    rw [← hα, mul_two_eq] at hl
    have := hl.2 _ hR
    exact absurd (lt_add_of_pos_right (f (lzE ρ ρ) + f (lzE ρ ρ)) hy.pos) (not_lt.2 this)
  · have hl := lzE_lh hy hy1 hc1ne hc1y.le
    rw [← hα, mul_two_eq] at hl
    have hgl : f ρ ≤ lg c1 := (add_le_add_iff_left _).1 (hl.2 _ hR)
    exact absurd ((hgl.trans (lg_le hc1ne)).trans_lt hc1y) (lt_irrefl _)

end LzK

end Googology.Trans.PoR.InaccPsi.R2.Lz

import Googology.Trans.PoR.InaccPsi.R2.LxTm
import Googology.Trans.PoR.InaccPsi.R2.LzEps
import Googology.Trans.PoR.InaccPsi.R2.LxE

/-!
# The `ε`-numbers `e^K_c(x) = ϑˣ(Ω₁ + E_K(x) + c)` above a `ϑ`-fixed layer top, `c ≤ x`: generically in `K`

`R2.LzEps` treats `e_c(x) = ϑˣ(Ω₁ + B(x) + c)` over the atom `B(x)`.  Here the same is done once for **every layer
`K`** whose top `E_K(x)` is an `ε`-number in `Tˣ` and a fixed point of `σ ↦ ϑˣ(Ω₁ + σ)` (`LxZK K`: `ϑˣ(Ω₁ + σ) <
E_K(x)` for `σ < E_K(x)`); `lxZE K x c := ϑˣ(Ω₁ + (E_K(x) + c))`.  From the cited facts already in the repo (no new
axiom):

* `lxZE_facts`, `lxZE_strict`, `lxZE_enum` (**every `ε`-number in `(E_K(x), e_c(x))` is some `e_{c'}(x)`, `c' < c`**),
  `lxZE_zero` (**`e_0(x) = ε_{E_K(x)+1}`**), `lxZE_succ` (**`e_{c+1}(x) = ε_{e_c(x)+1}`**), `lxZE_lt_ups`;
* `lxZE_lh` (**`lh(e_c(x)) = e_c(x)·2 + logend(c)`**, `c ≠ 0`: [W07b] Def 4.1 as `lhT_Om1_add`), `lxZE_lh0`
  (**`lh(e_0(x)) = e_0(x)·2`**: `vz_lh_th_fix`);
* `lxZE_pi` (**Lemma EXACT** for `c < σ`), `lxZE_piTop` (**Lemma EXACT for the top `e_ρ(ρ) ↦ e_σ(σ)`**: [W07a] Def 5.1
  fourth clause `pi_vt_two`, `pi_base`);
* `LxZW.lxZE_img0`, `LxZW.lxZE_copy`, `LxZW.lxZE_imgAll`, `LxZW.lxZE_imgTop` (**Lemma IMG for every `e_c(ρ)`, `c ≤ ρ`**:
  the copy keeps `e ≤₁ e·2 + g` of `R₁⁺`, an `ε`-number `e_{c'}(f(ρ))` below `e_c(f(ρ))` has the smaller reach);
* `lxZK_lg` (**`lgLay` satisfies `LxZK`**: `Γ(x) ∈ Tˣ`, `ϑˣ(Ω₁ + σ) < Γ(x)` for `σ < Γ(x)`).

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Lx

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt

/-- **A `ϑ`-fixed `ε`-number top**: `E_K(x) ∈ E ∩ Tˣ` and `ϑˣ(Ω₁ + σ) < E_K(x)` for every `σ < E_K(x)`. -/
structure LxZK (K : XtLay) : Prop where
  ek : LxEK K
  mem : ∀ x, InE x → x < Om1 → K.E x ∈ Tset x
  fix : ∀ x, InE x → x < Om1 → ∀ σ, σ < K.E x → vt x (Om1 + σ) < K.E x

/-- `e^K_c(x) = ϑˣ(Ω₁ + (E_K(x) + c))`. -/
noncomputable def lxZE (K : XtLay) (x c : Ordinal.{0}) : Ordinal.{0} := vt x (Om1 + (K.E x + c))

variable {K : XtLay}

section Facts

variable (hZ : LxZK K) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hZ hx hx1

theorem lxZ_EcT {c : Ordinal.{0}} (hc : c ≤ x) : K.E x + c ∈ Tset x ∧ K.E x + c < Om1 :=
  ⟨vzT_add hx hx1 (hZ.mem x hx hx1) (mem_T_of_le hx hx1 hc),
    Om1_add_lt (K.exp_lt x hx hx1) (lt_of_le_of_lt hc hx1)⟩

/-- The facts on `e_c(x)`. -/
theorem lxZE_facts {c : Ordinal.{0}} (hc : c ≤ x) :
    Om1 + (K.E x + c) ∈ Tset x ∧ Om1 + (K.E x + c) < OmTwo ∧ lxZE K x c ∈ Tset x ∧ x < lxZE K x c ∧
      lxZE K x c < Om1 ∧ InE (lxZE K x c) ∧ Indec (lxZE K x c) ∧ K.E x + c < lxZE K x c := by
  obtain ⟨hT, h1⟩ := lxZ_EcT hZ hx hx1 hc
  have hγT := (Om1_add_T hx hx1 hT h1).1
  have hγ2 := Om1_add_lt_OmTwo h1
  obtain ⟨hvT, -, hv1, hvP, -⟩ := vt_memTwo hx hx1 hγT hγ2
  have hE := (vt_E_iff hx hx1 hγT hγ2).2 le_self_add
  exact ⟨hγT, hγ2, hvT, hE.1, hv1, hE.2, hvP, lt_vt_Om1_add hx hx1 hT h1⟩

theorem lxZE_E_lt {c : Ordinal.{0}} (hc : c ≤ x) : K.E x < lxZE K x c :=
  lt_of_le_of_lt le_self_add (lxZE_facts hZ hx hx1 hc).2.2.2.2.2.2.2

/-- `E_K(x) + c < ε_{E_K(x)+1}` for `c ≤ x`. -/
theorem lxZ_Ec_lt_eN {c : Ordinal.{0}} (hc : c ≤ x) : K.E x + c < eN (K.E x) :=
  (inE_indec (eN_E _)).add_lt (lt_eN _)
    ((lt_of_le_of_lt hc (lx_E_gt hZ.ek hx hx1)).trans (lt_eN _))

/-- **`c ↦ e_c(x)` is strictly increasing** on `[0, x]`. -/
theorem lxZE_strict {c c' : Ordinal.{0}} (h : c < c') (hc' : c' ≤ x) : lxZE K x c < lxZE K x c' := by
  obtain ⟨hT, -⟩ := lxZ_EcT hZ hx hx1 (h.le.trans hc')
  obtain ⟨hT', h1'⟩ := lxZ_EcT hZ hx hx1 hc'
  have hlt : K.E x + c < K.E x + c' := (add_lt_add_iff_left _).2 h
  exact vt_Om1_add_lt hx hx1 hT hT' h1' hlt (hlt.trans (lxZE_facts hZ hx hx1 hc').2.2.2.2.2.2.2)

theorem lxZE_mono {c c' : Ordinal.{0}} (h : c ≤ c') (hc' : c' ≤ x) : lxZE K x c ≤ lxZE K x c' := by
  rcases h.lt_or_eq with h | rfl
  · exact (lxZE_strict hZ hx hx1 h hc').le
  · exact le_rfl

/-- **Every `ε`-number strictly between `E_K(x)` and `e_c(x)` is some `e_{c'}(x)`, `c' < c`.** -/
theorem lxZE_enum {c α : Ordinal.{0}} (hc : c ≤ x) (hαE : InE α) (hGα : K.E x < α) (hαc : α < lxZE K x c) :
    ∃ c', c' < c ∧ α = lxZE K x c' := by
  obtain ⟨-, -, heT, -, he1, -, -, -⟩ := lxZE_facts hZ hx hx1 hc
  obtain ⟨hGcT, hGc1⟩ := lxZ_EcT hZ hx hx1 hc
  have hxG := lx_E_gt hZ.ek hx hx1
  have hα1 : α < Om1 := hαc.trans he1
  have hαT : α ∈ Tset x := vz_T_down hx hx1 heT he1 hαc.le
  have hxα : x < α := hxG.trans hGα
  obtain ⟨ξ, hξT, hξ2, hξα⟩ := vt_rep hx hx1 hαT hxα.le hα1 (inE_indec hαE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξα]; exact hxα, by rw [hξα]; exact hαE⟩
  have hGcα : K.E x + c < α := (lxZ_Ec_lt_eN hZ hx hx1 hc).trans_le (eN_le hGα hαE)
  have hξlt : ξ < Om1 + (K.E x + c) :=
    vt_lt_Om1_add hx hx1 hξT hξ2 hGcT hGc1 (by rw [hξα]; exact hGcα) (by rw [hξα]; exact hαc)
  set η := ξ - Om1 with hη
  have hξe : Om1 + η = ξ := Ordinal.add_sub_cancel_of_le hΩξ
  have hηlt : η < K.E x + c := (add_lt_add_iff_left Om1).1 (by rw [hξe]; exact hξlt)
  have hη1 : η < Om1 := hηlt.trans hGc1
  have hηT : η ∈ Tset x := vzRem_T hx hx1 hξT hξ2 hξe.symm (dvd_refl _) hη1
  rcases lt_or_ge η (K.E x) with hηG | hGη
  · exfalso
    have := hZ.fix x hx hx1 η hηG
    rw [hξe, hξα] at this
    exact absurd hGα (not_lt.2 this.le)
  · refine ⟨η - K.E x, ?_, ?_⟩
    · have e := Ordinal.add_sub_cancel_of_le hGη
      exact (add_lt_add_iff_left (K.E x)).1 (by rw [e]; exact hηlt)
    · rw [lxZE, Ordinal.add_sub_cancel_of_le hGη, hξe, hξα]

/-- **`e_0(x) = ε_{E_K(x)+1}`.** -/
theorem lxZE_zero : lxZE K x 0 = eN (K.E x) := by
  obtain ⟨-, -, -, -, -, heE, -, -⟩ := lxZE_facts hZ hx hx1 (zero_le : (0 : Ordinal.{0}) ≤ x)
  refine le_antisymm ?_ (eN_le (lxZE_E_lt hZ hx hx1 zero_le) heE)
  by_contra hlt
  push Not at hlt
  obtain ⟨c', hc', -⟩ := lxZE_enum hZ hx hx1 zero_le (eN_E _) (lt_eN _) hlt
  exact absurd hc' (not_lt.2 zero_le)

/-- **`e_{c+1}(x) = ε_{e_c(x)+1}`.** -/
theorem lxZE_succ {c : Ordinal.{0}} (hc : c < x) : lxZE K x (c + 1) = eN (lxZE K x c) := by
  have hc1 : c + 1 ≤ x := Order.add_one_le_of_lt hc
  obtain ⟨-, -, -, -, -, heE, -, -⟩ := lxZE_facts hZ hx hx1 hc1
  have hlt := lxZE_strict hZ hx hx1 (lt_add_one c) hc1
  refine le_antisymm ?_ (eN_le hlt heE)
  by_contra hlt'
  push Not at hlt'
  have hG : K.E x < eN (lxZE K x c) := (lxZE_E_lt hZ hx hx1 hc.le).trans (lt_eN _)
  obtain ⟨c', hc', he⟩ := lxZE_enum hZ hx hx1 hc1 (eN_E _) hG hlt'
  have hc'c : c' ≤ c := Order.lt_add_one_iff.1 hc'
  have := lxZE_mono hZ hx hx1 hc'c hc.le
  rw [← he] at this
  exact absurd (lt_eN (lxZE K x c)) (not_lt.2 this)

/-- `e_c(x)` lies below every `<₁ ∞`-point above `x`. -/
theorem lxZE_lt_ups {c u : Ordinal.{0}} (hc : c ≤ x) (hxu : x < u) (hu : LtInf1 u) : lxZE K x c < u := by
  obtain ⟨m, -, -, hmin, hTm, -⟩ := T_next (Or.inr hx) hx1
  obtain ⟨-, -, heT, -, he1, -, -, -⟩ := lxZE_facts hZ hx hx1 hc
  exact ((hTm _ he1).1 heT).trans_le (hmin u hxu hu)

/-- **The `R₁⁺`-reach of `e_c(x)`** (`c ≠ 0`): `lh(e_c(x)) = e_c(x)·2 + logend(c)`. -/
theorem lxZE_lh {c : Ordinal.{0}} (hc0 : c ≠ 0) (hc : c ≤ x) :
    IsLh1 (lxZE K x c) (lxZE K x c * 2 + lg c) := by
  obtain ⟨-, -, heT, hxe, he1, -, heP, -⟩ := lxZE_facts hZ hx hx1 hc
  obtain ⟨hT, h1⟩ := lxZ_EcT hZ hx hx1 hc
  have hxB := lx_E_gt hZ.ek hx hx1
  have hBc0 : K.E x + c ≠ 0 := (lt_of_lt_of_le (hZ.ek x hx hx1).pos le_self_add).ne'
  have hlim : ∃ σ, σ < K.E x + c ∧ K.E x + c < vt x (Om1 + σ) := by
    refine ⟨K.E x, lt_add_of_pos_right _ (pos_iff_ne_zero.2 hc0), ?_⟩
    have := lxZ_Ec_lt_eN hZ hx hx1 hc
    rwa [← lxZE_zero hZ hx hx1, lxZE, add_zero] at this
  have h := lh_eq_lhT (Or.inr hx) hx1 heT hxe he1 heP
  unfold lxZE at h ⊢
  rw [lhT_Om1_add hx hx1 hT h1 hBc0 hlim,
    Lz.lz_lg_add (hZ.ek x hx hx1) hc0 (lt_of_le_of_lt hc hxB)] at h
  exact h

/-- `lh(e_0(x)) = e_0(x)·2`. -/
theorem lxZE_lh0 : IsLh1 (lxZE K x 0) (lxZE K x 0 * 2) := by
  have hB1 := K.exp_lt x hx hx1
  have hfix : ∀ σ, σ < K.E x → vt x (Om1 * ((1 : ℕ) : Ordinal.{0}) + σ) ≤ K.E x := fun σ hσ => by
    rw [Nat.cast_one, mul_one]; exact (hZ.fix x hx hx1 σ hσ).le
  have h := vz_lh_th_fix hx hx1 le_rfl (hZ.mem x hx hx1) hB1 hfix
  have e1 : Om1 * ((1 : ℕ) : Ordinal.{0}) + K.E x = Om1 + (K.E x + 0) := by
    rw [Nat.cast_one, mul_one, add_zero]
  have e2 : ((1 + 1 : ℕ) : Ordinal.{0}) = 2 := by norm_num
  rw [e1, e2] at h
  exact h

end Facts

/-! ## Lemma EXACT -/

/-- **Lemma EXACT for `e_c`**: for bases `σ < ρ` and `c < σ`, `e_c(ρ) ∈ Tᵖ[σ]` and `π_{σ,ρ}(e_c(ρ)) = e_c(σ)`. -/
theorem lxZE_pi (hZ : LxZK K) {σ ρ c : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ)
    (hc : c < σ) : lxZE K ρ c ∈ TB ρ σ ∧ pi σ ρ (lxZE K ρ c) = lxZE K σ c := by
  have hρE := hB.2.1
  have hρ1 := hB.2.2.2
  obtain ⟨h1, h2⟩ := K.exp_pi σ ρ hσ hρ hB
  obtain ⟨h3, h4⟩ := pi_add hB h1 (mem_TB_of_lt hB hc)
  rw [h2, pi_lt hB hc] at h4
  obtain ⟨hO, hpO⟩ := pi_Om1 hB
  obtain ⟨h5, h6⟩ := pi_add hB hO h3
  rw [hpO, h4] at h6
  have hc' : c ≤ ρ := (hc.trans hB.2.2.1).le
  obtain ⟨-, hγ2, -, -, -, -, -, -⟩ := lxZE_facts hZ hρE hρ1 hc'
  obtain ⟨hvT, -, -, -, hvP⟩ := vt_memTwo hρE hρ1 h5.1 hγ2
  unfold lxZE
  refine ⟨⟨hvT, by rw [hvP]; exact h5.2⟩, ?_⟩
  rw [pi_vt_two hB h5 hγ2, h6]

/-- **Lemma EXACT for the top `e_ρ(ρ)`**: `π_{σ,ρ}(e_ρ(ρ)) = e_σ(σ)`. -/
theorem lxZE_piTop (hZ : LxZK K) {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) :
    lxZE K ρ ρ ∈ TB ρ σ ∧ pi σ ρ (lxZE K ρ ρ) = lxZE K σ σ := by
  have hρE := hB.2.1
  have hρ1 := hB.2.2.2
  obtain ⟨h1, h2⟩ := K.exp_pi σ ρ hσ hρ hB
  obtain ⟨hb1, hb2⟩ := pi_base hB
  obtain ⟨h3, h4⟩ := pi_add hB h1 hb1
  rw [h2, hb2] at h4
  obtain ⟨hO, hpO⟩ := pi_Om1 hB
  obtain ⟨h5, h6⟩ := pi_add hB hO h3
  rw [hpO, h4] at h6
  obtain ⟨-, hγ2, -, -, -, -, -, -⟩ := lxZE_facts hZ hρE hρ1 le_rfl
  obtain ⟨hvT, -, -, -, hvP⟩ := vt_memTwo hρE hρ1 h5.1 hγ2
  unfold lxZE
  refine ⟨⟨hvT, by rw [hvP]; exact h5.2⟩, ?_⟩
  rw [pi_vt_two hB h5 hγ2, h6]

/-! ## Lemma IMG for `e_c` -/

namespace LxZW

variable (hZ : LxZK K) {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include hZ h

theorem lxZE_lt_δ {c : Ordinal.{0}} (hc : c ≤ ρ) : lxZE K ρ c < δ :=
  lxZE_lt_ups hZ h.ρE h.ρ1 hc h.ρδ h.next.2.1.2

/-- The witness pair of the atom `E_K(ρ)`: every copy has `E_K(f(ρ)) ≤ f(E_K(ρ))`. -/
theorem lxZ_wit : ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ K.E ρ ∈ W ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      K.E (f ρ) ≤ f (K.E ρ) := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  obtain ⟨W0, Z0, hw0, hTW, hI⟩ := K.top_wit ρ τ δ h
  rw [lx_top hZ.ek hρE hρ1] at hTW
  refine ⟨W0, Z0, hw0, hTW, fun A f hW hZ' C => ?_⟩
  have h2 := (hI A f hW hZ' C).2
  have hfE := upsPt_inE C.ups
  have hf1 := (C.low ρ C.rho).trans hρ1
  rwa [lx_top hZ.ek hfE hf1, lx_top hZ.ek hρE hρ1] at h2

/-- **The witness pair of `e_0(ρ) = ε_{E_K(ρ)+1}`**: every copy has `f(e_0(ρ))` an `ε`-number `≥ e_0(f(ρ))`. -/
theorem lxZE_img0 : ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ lxZE K ρ 0 ∈ W ∧ (0 : Ordinal.{0}) ∈ Z ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      lxZE K (f ρ) 0 ≤ f (lxZE K ρ 0) := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  set e := lxZE K ρ 0 with hedef
  obtain ⟨-, -, -, -, -, heE, -, -⟩ := lxZE_facts hZ hρE hρ1 (zero_le : (0 : Ordinal.{0}) ≤ ρ)
  have hBe : K.E ρ < e := lxZE_E_lt hZ hρE hρ1 zero_le
  have hρB := lx_E_gt hZ.ek hρE hρ1
  have heδ : e < δ := lxZE_lt_δ hZ h zero_le
  have hδI := inE_indec h.δE
  have hee : e + e < δ := hδI.add_lt heδ heδ
  obtain ⟨W0, Z0, hw0, hTW, hIB⟩ := lxZ_wit hZ h
  have hw : WZ ρ δ (insert (e + e) (insert e W0)) (insert 0 Z0) := by
    have w0 : WZ ρ δ W0 (insert 0 Z0) := hw0.insZ hρE.pos
    have w1 := w0.insW (hρB.trans hBe).le heδ (Or.inl (inE_indec heE))
    exact w1.insW ((hρB.trans hBe).le.trans le_self_add) hee
      (Or.inr ⟨e, by simp, e, by simp, lt_add_of_pos_right _ heE.pos, lt_add_of_pos_right _ heE.pos, rfl⟩)
  refine ⟨_, _, hw, by simp, by simp, fun A f hW hZ' C => ?_⟩
  have heA : e ∈ A := hW (by simp)
  have heeA : e + e ∈ A := hW (by simp)
  have hW0 : ↑W0 ⊆ A := fun x hx =>
    hW (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_coe.1 hx))))
  have hZ0 : ↑Z0 ⊆ A := fun x hx => hZ' (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hx)))
  have hBA : K.E ρ ∈ A := hW0 hTW
  have hfB := hIB A f hW0 hZ0 C
  have hsrc : le1 e (e + e) := by
    refine (h.lowδ e (e + e) (hρB.trans hBe) hee.le).2 ?_
    rw [← mul_two_eq]; exact (le1R_two_iff heE.pos).2 heE
  have himg : le1 (f e) (f e + f e) := by
    have := C.cov1 e heA (e + e) heeA hsrc
    rwa [← C.add e heA e heA (e + e) heeA rfl] at this
  have hfBe : f (K.E ρ) < f e := C.mono hBA heA hBe
  have hfE : InE (f e) := by
    by_cases hU : UpsPt (f e)
    · exact upsPt_inE hU
    · have hR := (C.sk (f e) (C.low e heA) hU (f e + f e)).1 himg
      have hpos : 0 < f e := lt_of_le_of_lt zero_le hfBe
      rw [← mul_two_eq] at hR
      exact (le1R_two_iff hpos).1 hR
  have hy := upsPt_inE C.ups
  have hy1 : f ρ < Om1 := (C.low ρ C.rho).trans hρ1
  rw [lxZE_zero hZ hy hy1]
  exact eN_le (hfB.trans_lt hfBe) hfE

/-- The common part of the copies of `e_c(ρ)` for `0 < c ≤ ρ`. -/
theorem lxZE_copy {c g : Ordinal.{0}} (hc0 : c ≠ 0) (hc : c ≤ ρ) (hg : g ≤ lg c) (hgρ : g ≤ ρ)
    {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (C : ImgCtx ρ A f)
    (heA : lxZE K ρ c ∈ A) (heeA : lxZE K ρ c + lxZE K ρ c ∈ A) (hgA : g ∈ A)
    (hegA : lxZE K ρ c + lxZE K ρ c + g ∈ A) (hBA : K.E ρ ∈ A) (hfB : K.E (f ρ) ≤ f (K.E ρ)) :
    UpsPt (f (lxZE K ρ c)) ∨ (InE (f (lxZE K ρ c)) ∧ K.E (f ρ) < f (lxZE K ρ c) ∧
      le1R (f (lxZE K ρ c)) (f (lxZE K ρ c) + f (lxZE K ρ c) + f g)) := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  set e := lxZE K ρ c with hedef
  have hρe : ρ < e := (lx_E_gt hZ.ek hρE hρ1).trans (lxZE_E_lt hZ hρE hρ1 hc)
  have heδ : e < δ := lxZE_lt_δ hZ h hc
  have hδI := inE_indec h.δE
  have hgδ : g < δ := lt_of_le_of_lt hgρ h.ρδ
  have hsrcR : le1R e (e + e + g) := by
    have hl := lxZE_lh hZ hρE hρ1 hc0 hc
    rw [mul_two_eq] at hl
    exact le1R_of_le (le_self_add.trans le_self_add) (add_le_add le_rfl hg) hl.1
  have hsrc : le1 e (e + e + g) :=
    (h.lowδ e _ hρe (hδI.add_lt (hδI.add_lt heδ heδ) hgδ).le).2 hsrcR
  have himg : le1 (f e) (f e + f e + f g) := by
    have := C.cov1 e heA _ hegA hsrc
    rwa [← C.add (e + e) heeA g hgA _ hegA rfl, ← C.add e heA e heA (e + e) heeA rfl] at this
  have hfBe : f (K.E ρ) < f e := C.mono hBA heA (lxZE_E_lt hZ hρE hρ1 hc)
  by_cases hU : UpsPt (f e)
  · exact Or.inl hU
  · have hR := (C.sk (f e) (C.low e heA) hU _).1 himg
    have hpos : 0 < f e := lt_of_le_of_lt zero_le hfBe
    have h2 : le1R (f e) (f e * 2) := le1R_of_le (by rw [mul_two_eq]; exact le_self_add)
      (by rw [mul_two_eq]; exact le_self_add) hR
    exact Or.inr ⟨(le1R_two_iff hpos).1 h2, hfB.trans_lt hfBe, hR⟩

/-- **Lemma IMG for every `e_c(ρ)`, `c < ρ`**: witness sets (with `c` among the constants) such that every covering
copy `f` has `e_c(f(ρ)) ≤ f(e_c(ρ))`. -/
theorem lxZE_imgAll : ∀ c, c < ρ → ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ lxZE K ρ c ∈ W ∧ c ∈ Z ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      lxZE K (f ρ) c ≤ f (lxZE K ρ c) := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hδI := inE_indec h.δE
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc
  rcases eq_or_ne c 0 with rfl | hc0
  · exact lxZE_img0 hZ h
  obtain ⟨c0, hcs, hdv, hc0c⟩ := lg_split hc0
  set g := lg c with hgdef
  have hgc : g ≤ c := lg_le hc0
  have hgρ : g < ρ := lt_of_le_of_lt hgc hc
  obtain ⟨W0, Z0, hw0, he0W, -, hI0⟩ := IH c0 hc0c (hc0c.trans hc)
  obtain ⟨WB, ZB, hwB, hTB, hIB⟩ := lxZ_wit hZ h
  set e := lxZE K ρ c with hedef
  obtain ⟨-, -, -, -, -, heE, heI, -⟩ := lxZE_facts hZ hρE hρ1 hc.le
  have hρB := lx_E_gt hZ.ek hρE hρ1
  have hρe : ρ < e := hρB.trans (lxZE_E_lt hZ hρE hρ1 hc.le)
  have heδ : e < δ := lxZE_lt_δ hZ h hc.le
  have hee : e + e < δ := hδI.add_lt heδ heδ
  have heeg : e + e + g < δ := hδI.add_lt hee (hgρ.trans h.ρδ)
  set Z : Finset Ordinal.{0} := insert g (insert c (Z0 ∪ ZB)) with hZdef
  have w0 : WZ ρ δ (W0 ∪ WB) Z := ((hw0.union hwB).insZ hc).insZ hgρ
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
  refine ⟨_, Z, w2, by simp, by simp [hZdef], fun A f hW hZ' C => ?_⟩
  have heA : e ∈ A := hW (by simp)
  have heeA : e + e ∈ A := hW (by simp)
  have hegA : e + e + g ∈ A := hW (by simp)
  have hgA : g ∈ A := hZ' (by simp [hZdef])
  have hcA : c ∈ A := hZ' (by simp [hZdef])
  have hW0 : ↑W0 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hZ0 : ↑Z0 ⊆ A := fun x hx => hZ' (by simp [hZdef, Finset.mem_coe.1 hx])
  have hWBA : ↑WB ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hZBA : ↑ZB ⊆ A := fun x hx => hZ' (by simp [hZdef, Finset.mem_coe.1 hx])
  have hBA : K.E ρ ∈ A := hWBA hTB
  have hfB := hIB A f hWBA hZBA C
  have hy := upsPt_inE C.ups
  have hy1 : f ρ < Om1 := (C.low ρ C.rho).trans hρ1
  have hcy : c < f ρ := C.above c hcA hc
  have hfg : f g = g := C.fix g hgA hgρ
  have hρeA : f ρ < f e := C.mono C.rho heA hρe
  rcases lxZE_copy hZ h hc0 hc.le le_rfl hgρ.le C heA heeA hgA hegA hBA hfB with hU | ⟨hαE, hBα, hR⟩
  · exact (lxZE_lt_ups hZ hy hy1 hcy.le hρeA hU.2).le
  rw [hfg] at hR
  by_contra hlt
  push Not at hlt
  obtain ⟨c1, hc1c, hα⟩ := lxZE_enum hZ hy hy1 hcy.le hαE hBα hlt
  have he0A : lxZE K ρ c0 ∈ A := hW0 (Finset.mem_coe.2 he0W)
  have hlow : lxZE K (f ρ) c0 < f e :=
    (hI0 A f hW0 hZ0 C).trans_lt (C.mono he0A heA (lxZE_strict hZ hρE hρ1 hc0c hc.le))
  have hc01 : c0 < c1 := by
    by_contra hle
    push Not at hle
    have := lxZE_mono hZ hy hy1 hle (hc0c.trans hcy).le
    rw [← hα] at this
    exact absurd hlow (not_lt.2 this)
  have hc1ne : c1 ≠ 0 := (lt_of_le_of_lt zero_le hc01).ne'
  have hl := lxZE_lh hZ hy hy1 hc1ne (hc1c.trans hcy).le
  rw [← hα, mul_two_eq] at hl
  have hgl : g ≤ lg c1 := (add_le_add_iff_left _).1 (hl.2 _ hR)
  have hdv1 : ω ^ g ∣ c1 := (le_lg_iff hc1ne g).1 hgl
  have := dvd_next hdv1 hdv hc01
  rw [← hcs] at this
  exact absurd hc1c (not_lt.2 this)

/-- **Lemma IMG for the top `e_ρ(ρ)`**: every covering copy `f` has `e_{f(ρ)}(f(ρ)) ≤ f(e_ρ(ρ))`, and `f(e_ρ(ρ))` is
an `ε`-number. -/
theorem lxZE_imgTop : ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ lxZE K ρ ρ ∈ W ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      InE (f (lxZE K ρ ρ)) ∧ lxZE K (f ρ) (f ρ) ≤ f (lxZE K ρ ρ) := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hδI := inE_indec h.δE
  obtain ⟨WB, ZB, hwB, hTB, hIB⟩ := lxZ_wit hZ h
  set e := lxZE K ρ ρ with hedef
  obtain ⟨-, -, -, -, -, heE, heI, -⟩ := lxZE_facts hZ hρE hρ1 le_rfl
  have hρB := lx_E_gt hZ.ek hρE hρ1
  have hρe : ρ < e := hρB.trans (lxZE_E_lt hZ hρE hρ1 le_rfl)
  have heδ : e < δ := lxZE_lt_δ hZ h le_rfl
  have hee : e + e < δ := hδI.add_lt heδ heδ
  have heeg : e + e + ρ < δ := hδI.add_lt hee h.ρδ
  have hρW : ρ ∈ insert ρ WB := Finset.mem_insert_self _ _
  have w0 : WZ ρ δ (insert ρ WB) ZB := hwB.insW le_rfl h.ρδ (Or.inl (inE_indec hρE))
  have w1 : WZ ρ δ (insert (e + e) (insert e (insert ρ WB))) ZB := by
    have := w0.insW hρe.le heδ (Or.inl heI)
    exact this.insW (hρe.le.trans le_self_add) hee
      (Or.inr ⟨e, by simp, e, by simp, lt_add_of_pos_right _ heE.pos, lt_add_of_pos_right _ heE.pos, rfl⟩)
  have w2 : WZ ρ δ (insert (e + e + ρ) (insert (e + e) (insert e (insert ρ WB)))) ZB :=
    w1.insW ((hρe.le.trans le_self_add).trans le_self_add) heeg
      (Or.inr ⟨e + e, by simp, ρ, by simp, lt_add_of_pos_right _ hρE.pos,
        (hρe.trans_le le_self_add).trans_le le_self_add, rfl⟩)
  refine ⟨_, ZB, w2, by simp, fun A f hW hZ' C => ?_⟩
  have heA : e ∈ A := hW (by simp)
  have heeA : e + e ∈ A := hW (by simp)
  have hegA : e + e + ρ ∈ A := hW (by simp)
  have hWBA : ↑WB ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hBA : K.E ρ ∈ A := hWBA hTB
  have hfB := hIB A f hWBA hZ' C
  have hy := upsPt_inE C.ups
  have hy1 : f ρ < Om1 := (C.low ρ C.rho).trans hρ1
  have hρeA : f ρ < f e := C.mono C.rho heA hρe
  rcases lxZE_copy hZ h hρE.pos.ne' le_rfl (Lz.lz_lg_self hρE).ge le_rfl C heA heeA C.rho hegA hBA hfB with
    hU | ⟨hαE, hBα, hR⟩
  · exact ⟨upsPt_inE hU, (lxZE_lt_ups hZ hy hy1 le_rfl hρeA hU.2).le⟩
  refine ⟨hαE, ?_⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨c1, hc1y, hα⟩ := lxZE_enum hZ hy hy1 le_rfl hαE hBα hlt
  rcases eq_or_ne c1 0 with rfl | hc1ne
  · have hl := lxZE_lh0 hZ hy hy1
    rw [← hα, mul_two_eq] at hl
    have := hl.2 _ hR
    exact absurd (lt_add_of_pos_right (f (lxZE K ρ ρ) + f (lxZE K ρ ρ)) hy.pos) (not_lt.2 this)
  · have hl := lxZE_lh hZ hy hy1 hc1ne hc1y.le
    rw [← hα, mul_two_eq] at hl
    have hgl : f ρ ≤ lg c1 := (add_le_add_iff_left _).1 (hl.2 _ hR)
    exact absurd ((hgl.trans (lg_le hc1ne)).trans_lt hc1y) (lt_irrefl _)

end LxZW

/-! ## The instance `Γ` -/

/-- **`lgLay` satisfies `LxZK`**: `Γ(x) ∈ E ∩ Tˣ`, `ϑˣ(Ω₁ + σ) < Γ(x)` for `σ < Γ(x)`. -/
theorem lxZK_lg : LxZK lgLay where
  ek := fun x hx hx1 => lgG_inE x hx hx1
  mem := fun _ hx hx1 => (lgG_facts hx hx1).1
  fix := fun _ hx hx1 _ hσ => lx_vt_lt_G hx hx1 hσ

end Googology.Trans.PoR.InaccPsi.R2.Lx

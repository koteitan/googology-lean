import Googology.Trans.PoR.InaccPsi.R2.LgLay
import Googology.Trans.PoR.InaccPsi.R2.LzEps

/-!
# The `ε`-numbers above `Γ(x)`: `e^Γ_c(x) = ϑˣ(Ω₁ + Γ(x) + c)`, enumeration, EXACT, and the tower `Γ(x), ε_{Γ(x)+1}, …`

`Γ(x) = lgG x = ϑˣ(Ω₁·Ω₁)` (`R2.LgTh`).  For a base `x ∈ E ∩ Ω₁` and `c ≤ x`, `lxE x c := ϑˣ(Ω₁ + (Γ(x) + c))` (the
`Γ`-analogue of `Lz.lzE`, whose atom is `B(x)`).  From the cited facts already in the repo (no new axiom):

* `lxE_facts` (`e_c(x) ∈ Tˣ ∩ E ∩ (x, Ω₁)`, above `Γ(x) + c`), `lx_vt_lt_G` (**`ϑˣ(Ω₁ + σ) < Γ(x)` for `σ < Γ(x)`**:
  [W07a] Lemma 3.30 as `lgVt_lt_low`), `lxE_strict` (**`c ↦ e_c(x)` is strictly increasing**), `lxE_enum` (**every
  `ε`-number in `(Γ(x), e_c(x))` is some `e_{c'}(x)`, `c' < c`**: `vt_rep`, `vt_E_iff`, `vt_lt_Om1_add`, `vzRem_T`);
* `lxE_zero` (**`e_0(x) = ε_{Γ(x)+1}`**), `lxE_succ` (**`e_{c+1}(x) = ε_{e_c(x)+1}`**);
* `lxE_pi` (**Lemma EXACT**: `e_c(ρ) ∈ Tᵖ[σ]`, `π_{σ,ρ}(e_c(ρ)) = e_c(σ)` for `c < σ`: [W07a] Def 5.1 fourth clause
  `pi_vt_two`, `pi_add`, `pi_Om1`, `lg_pi`);
* `lxG n x` (**the tower** `lxG 0 x = Γ(x)`, `lxG (n+1) x = e_n(x) = ε_{Γ(x)+n+1}`), `lxG_succ` (`lxG (n+1) x =
  ε_{lxG n x + 1}`), `lxG_inE`, `lxG_pi` (EXACT for every `lxG n`), `lxG_eN_pi` (EXACT for `ε_{lxG n x + 1}`).

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Lx

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt

/-- `e^Γ_c(x) = ϑˣ(Ω₁ + (Γ(x) + c))`. -/
noncomputable def lxE (x c : Ordinal.{0}) : Ordinal.{0} := vt x (Om1 + (lgG x + c))

section Facts

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem lx_GT : lgG x ∈ Tset x := (lgG_facts hx hx1).1

theorem lx_GcT {c : Ordinal.{0}} (hc : c ≤ x) : lgG x + c ∈ Tset x ∧ lgG x + c < Om1 :=
  ⟨vzT_add hx hx1 (lx_GT hx hx1) (mem_T_of_le hx hx1 hc),
    Om1_add_lt (lgG_lt_Om1 hx hx1) (lt_of_le_of_lt hc hx1)⟩

/-- The facts on `e_c(x)`. -/
theorem lxE_facts {c : Ordinal.{0}} (hc : c ≤ x) :
    Om1 + (lgG x + c) ∈ Tset x ∧ Om1 + (lgG x + c) < OmTwo ∧ lxE x c ∈ Tset x ∧ x < lxE x c ∧
      lxE x c < Om1 ∧ InE (lxE x c) ∧ Indec (lxE x c) ∧ lgG x + c < lxE x c := by
  obtain ⟨hT, h1⟩ := lx_GcT hx hx1 hc
  have hγT := (Om1_add_T hx hx1 hT h1).1
  have hγ2 := Om1_add_lt_OmTwo h1
  obtain ⟨hvT, -, hv1, hvP, -⟩ := vt_memTwo hx hx1 hγT hγ2
  have hE := (vt_E_iff hx hx1 hγT hγ2).2 le_self_add
  exact ⟨hγT, hγ2, hvT, hE.1, hv1, hE.2, hvP, lt_vt_Om1_add hx hx1 hT h1⟩

theorem lxE_G_lt {c : Ordinal.{0}} (hc : c ≤ x) : lgG x < lxE x c :=
  lt_of_le_of_lt le_self_add (lxE_facts hx hx1 hc).2.2.2.2.2.2.2

/-- `ϑˣ(Ω₁·Ω₁ + 0) = Γ(x)`. -/
theorem lx_vt_OmOm : vt x (Om1 * Om1 + 0) = lgG x := by
  rw [add_zero, ← lgV_eq hx hx1]; rfl

/-- **`ϑˣ(Ω₁ + σ) < Γ(x)` for `σ < Γ(x)`** ([W07a] Lemma 3.30 as `lgVt_lt_low`). -/
theorem lx_vt_lt_G {σ : Ordinal.{0}} (hσ : σ < lgG x) : vt x (Om1 + σ) < lgG x := by
  obtain ⟨hGT, hxG, hG1, hGE, -⟩ := lgG_facts hx hx1
  have hσT : σ ∈ Tset x := vz_T_down hx hx1 hGT hG1 hσ.le
  have hσ1 : σ < Om1 := hσ.trans hG1
  have h1x : (1 : Ordinal.{0}) ≤ x := (one_lt_omega0.trans (omega0_lt_inE hx)).le
  have h1T : (1 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 h1x
  have h11 : (1 : Ordinal.{0}) < Om1 := lt_of_le_of_lt h1x hx1
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  have h01 : (0 : Ordinal.{0}) < Om1 := hx.pos.trans hx1
  have hG := lx_vt_OmOm hx hx1
  have h1G : (1 : Ordinal.{0}) < vt x (Om1 * Om1 + 0) := by
    rw [hG]; exact one_lt_omega0.trans (omega0_lt_inE hGE)
  have hσG : σ < vt x (Om1 * Om1 + 0) := by rw [hG]; exact hσ
  have := lgVt_lt_low hx hx1 h1T h11 hσT hσ1 h0T h01 h1G hσG
  rwa [mul_one, hG] at this

/-- `Γ(x) + c < ε_{Γ(x)+1}` for `c ≤ x`. -/
theorem lx_Gc_lt_eN {c : Ordinal.{0}} (hc : c ≤ x) : lgG x + c < eN (lgG x) := by
  have hxG := (lgG_facts hx hx1).2.1
  exact (inE_indec (eN_E _)).add_lt (lt_eN _) ((lt_of_le_of_lt hc hxG).trans (lt_eN _))

/-- **`c ↦ e_c(x)` is strictly increasing** on `[0, x]`. -/
theorem lxE_strict {c c' : Ordinal.{0}} (h : c < c') (hc' : c' ≤ x) : lxE x c < lxE x c' := by
  obtain ⟨hT, -⟩ := lx_GcT hx hx1 (h.le.trans hc')
  obtain ⟨hT', h1'⟩ := lx_GcT hx hx1 hc'
  have hlt : lgG x + c < lgG x + c' := (add_lt_add_iff_left _).2 h
  exact vt_Om1_add_lt hx hx1 hT hT' h1' hlt (hlt.trans (lxE_facts hx hx1 hc').2.2.2.2.2.2.2)

theorem lxE_mono {c c' : Ordinal.{0}} (h : c ≤ c') (hc' : c' ≤ x) : lxE x c ≤ lxE x c' := by
  rcases h.lt_or_eq with h | rfl
  · exact (lxE_strict hx hx1 h hc').le
  · exact le_rfl

/-- **Every `ε`-number strictly between `Γ(x)` and `e_c(x)` is some `e_{c'}(x)`, `c' < c`.** -/
theorem lxE_enum {c α : Ordinal.{0}} (hc : c ≤ x) (hαE : InE α) (hGα : lgG x < α) (hαc : α < lxE x c) :
    ∃ c', c' < c ∧ α = lxE x c' := by
  obtain ⟨-, -, heT, -, he1, -, -, -⟩ := lxE_facts hx hx1 hc
  obtain ⟨hGcT, hGc1⟩ := lx_GcT hx hx1 hc
  have hxG := (lgG_facts hx hx1).2.1
  have hα1 : α < Om1 := hαc.trans he1
  have hαT : α ∈ Tset x := vz_T_down hx hx1 heT he1 hαc.le
  have hxα : x < α := hxG.trans hGα
  obtain ⟨ξ, hξT, hξ2, hξα⟩ := vt_rep hx hx1 hαT hxα.le hα1 (inE_indec hαE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξα]; exact hxα, by rw [hξα]; exact hαE⟩
  have hGcα : lgG x + c < α := (lx_Gc_lt_eN hx hx1 hc).trans_le (eN_le hGα hαE)
  have hξlt : ξ < Om1 + (lgG x + c) :=
    vt_lt_Om1_add hx hx1 hξT hξ2 hGcT hGc1 (by rw [hξα]; exact hGcα) (by rw [hξα]; exact hαc)
  set η := ξ - Om1 with hη
  have hξe : Om1 + η = ξ := Ordinal.add_sub_cancel_of_le hΩξ
  have hηlt : η < lgG x + c := (add_lt_add_iff_left Om1).1 (by rw [hξe]; exact hξlt)
  have hη1 : η < Om1 := hηlt.trans hGc1
  have hηT : η ∈ Tset x := vzRem_T hx hx1 hξT hξ2 hξe.symm (dvd_refl _) hη1
  rcases lt_or_ge η (lgG x) with hηG | hGη
  · exfalso
    have := lx_vt_lt_G hx hx1 hηG
    rw [hξe, hξα] at this
    exact absurd hGα (not_lt.2 this.le)
  · refine ⟨η - lgG x, ?_, ?_⟩
    · have e := Ordinal.add_sub_cancel_of_le hGη
      exact (add_lt_add_iff_left (lgG x)).1 (by rw [e]; exact hηlt)
    · rw [lxE, Ordinal.add_sub_cancel_of_le hGη, hξe, hξα]

/-- **`e_0(x) = ε_{Γ(x)+1}`.** -/
theorem lxE_zero : lxE x 0 = eN (lgG x) := by
  obtain ⟨-, -, -, -, -, heE, -, -⟩ := lxE_facts hx hx1 (zero_le : (0 : Ordinal.{0}) ≤ x)
  refine le_antisymm ?_ (eN_le (lxE_G_lt hx hx1 zero_le) heE)
  by_contra hlt
  push Not at hlt
  obtain ⟨c', hc', -⟩ := lxE_enum hx hx1 zero_le (eN_E _) (lt_eN _) hlt
  exact absurd hc' (not_lt.2 zero_le)

/-- **`e_{c+1}(x) = ε_{e_c(x)+1}`.** -/
theorem lxE_succ {c : Ordinal.{0}} (hc : c < x) : lxE x (c + 1) = eN (lxE x c) := by
  have hc1 : c + 1 ≤ x := Order.add_one_le_of_lt hc
  obtain ⟨-, -, -, -, -, heE, -, -⟩ := lxE_facts hx hx1 hc1
  have hlt := lxE_strict hx hx1 (lt_add_one c) hc1
  refine le_antisymm ?_ (eN_le hlt heE)
  by_contra hlt'
  push Not at hlt'
  have hG : lgG x < eN (lxE x c) := (lxE_G_lt hx hx1 hc.le).trans (lt_eN _)
  obtain ⟨c', hc', he⟩ := lxE_enum hx hx1 hc1 (eN_E _) hG hlt'
  have hc'c : c' ≤ c := Order.lt_add_one_iff.1 hc'
  have := lxE_mono hx hx1 hc'c hc.le
  rw [← he] at this
  exact absurd (lt_eN (lxE x c)) (not_lt.2 this)

end Facts

/-! ## Lemma EXACT -/

/-- **Lemma EXACT for `e_c`**: for bases `σ < ρ` and `c < σ`, `e_c(ρ) ∈ Tᵖ[σ]` and `π_{σ,ρ}(e_c(ρ)) = e_c(σ)`. -/
theorem lxE_pi {σ ρ c : Ordinal.{0}} (hB : Bases σ ρ) (hc : c < σ) :
    lxE ρ c ∈ TB ρ σ ∧ pi σ ρ (lxE ρ c) = lxE σ c := by
  have hρE := hB.2.1
  have hρ1 := hB.2.2.2
  obtain ⟨h1, h2⟩ := lg_pi hB
  obtain ⟨h3, h4⟩ := pi_add hB h1 (mem_TB_of_lt hB hc)
  rw [h2, pi_lt hB hc] at h4
  obtain ⟨hO, hpO⟩ := pi_Om1 hB
  obtain ⟨h5, h6⟩ := pi_add hB hO h3
  rw [hpO, h4] at h6
  have hc' : c ≤ ρ := (hc.trans hB.2.2.1).le
  obtain ⟨-, hγ2, -, -, -, -, -, -⟩ := lxE_facts hρE hρ1 hc'
  obtain ⟨hvT, -, -, -, hvP⟩ := vt_memTwo hρE hρ1 h5.1 hγ2
  unfold lxE
  refine ⟨⟨hvT, by rw [hvP]; exact h5.2⟩, ?_⟩
  rw [pi_vt_two hB h5 hγ2, h6]

/-! ## The tower `Γ(x), ε_{Γ(x)+1}, ε_{Γ(x)+2}, …` -/

/-- **The tower**: `lxG 0 x = Γ(x)`, `lxG (n+1) x = e_n(x) = ε_{Γ(x)+n+1}`. -/
noncomputable def lxG : ℕ → Ordinal.{0} → Ordinal.{0}
  | 0, x => lgG x
  | n + 1, x => lxE x n

theorem lx_nat_lt {x : Ordinal.{0}} (hx : InE x) (n : ℕ) : (n : Ordinal.{0}) < x :=
  (natCast_lt_omega0 n).trans (omega0_lt_inE hx)

/-- **`lxG (n+1) x = ε_{lxG n x + 1}`.** -/
theorem lxG_succ {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (n : ℕ) : lxG (n + 1) x = eN (lxG n x) := by
  cases n with
  | zero => show lxE x ((0 : ℕ) : Ordinal.{0}) = eN (lgG x); rw [Nat.cast_zero]; exact lxE_zero hx hx1
  | succ n =>
    show lxE x ((n + 1 : ℕ) : Ordinal.{0}) = eN (lxE x (n : Ordinal.{0}))
    rw [Nat.cast_succ]; exact lxE_succ hx hx1 (lx_nat_lt hx n)

theorem lxG_inE {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : ∀ n : ℕ, InE (lxG n x)
  | 0 => lgG_inE x hx hx1
  | n + 1 => by rw [lxG_succ hx hx1]; exact eN_E _

/-- **EXACT for every `lxG n`.** -/
theorem lxG_pi {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hB : Bases σ ρ) :
    ∀ n : ℕ, lxG n ρ ∈ TB ρ σ ∧ pi σ ρ (lxG n ρ) = lxG n σ
  | 0 => lg_pi hB
  | n + 1 => lxE_pi hB (lx_nat_lt (upsPt_inE hσ) n)

/-- **EXACT for `ε_{lxG n x + 1}`.** -/
theorem lxG_eN_pi {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hB : Bases σ ρ) (n : ℕ) :
    eN (lxG n ρ) ∈ TB ρ σ ∧ pi σ ρ (eN (lxG n ρ)) = eN (lxG n σ) := by
  have hρ := lxG_succ hB.2.1 hB.2.2.2 n
  have hσ' := lxG_succ hB.1 (hB.2.2.1.trans hB.2.2.2) n
  rw [← hρ, ← hσ']
  exact lxG_pi hσ hB (n + 1)

end Googology.Trans.PoR.InaccPsi.R2.Lx

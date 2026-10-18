import Googology.Trans.PoR.InaccPsi.R2.NnRoad

/-!
# The frontiers of every term system with linear and square terms are fixed points of `GG`

For a term system `X` with linear and square terms whose top is above `x·x + x` at every `ε`-number `x`:

* `nnLt_top` (**`O_X(λ) < top(ρ_λ)` at every restart `λ < Ω₁` that is not a fixed point of `GG`**: off the fixed
  points of `υ`, `O ≤ λ < ρ_λ`; at a fixed point that is not a `Γ`-point, `O < λ·λ` (Theorem LEVEL); at a
  `Γ`-point with `GG(λ) ≠ λ`, `O < λ·λ + λ` (Theorem GG));
* `nnFr_GG` (**every frontier of `X` is a fixed point of `GG`**), `nn_GGfix_of_cof` (a limit of fixed points of
  `GG` is one), `nnB1_GG` (**the first limit of frontiers `xtB1 X` is a fixed point of `GG`**);
* `nnLL_top`, `nnLamK_GG`, `nnW2_GG`: for the layers `xtLL k` of `R2.XtW2`: **every `Λ⁺_k` and `Λ_{ω²}` are fixed
  points of `GG`** (with `nnVz_LamB`, `nnVz_B1`: `Λ_B`, `Λ_B⁺ = cpB1`); in particular all of them are at least
  `Φ_Γ = P(Ω₁^{Ω₁+1})`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Nn

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp

variable {X : XtSys}

/-- **`O_X(λ) < top(ρ_λ)` at every restart `λ < Ω₁` that is not a fixed point of `GG`.** -/
theorem nnLt_top (hX0 : NnLin X) (hS : NnSq X) (htop : ∀ x, InE x → x < Om1 → x * x + x < X.top x)
    {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) (h : ¬ (upsilon l = l ∧ GG l = l)) :
    xtOrec X l < X.top (upsilon l) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρE := ups_inE hl
  have hρ1 := ups_lt_Om1 l hl1
  have hρtop : upsilon l < X.top (upsilon l) :=
    (le_add_self : upsilon l ≤ upsilon l * upsilon l + upsilon l).trans_lt (htop _ hρE hρ1)
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · have hle : xtOrec X l ≤ l := by
      have hww : ω * ω ≤ l := le_of_dvd hl.1 (ri_iff.1 hl).2
      rcases hww.lt_or_eq with hww | hww
      · rw [xtNonfix hl hww hnf hl1]
        exact (cdOff_le _).trans (cpExp_le hl.1)
      · have hc : cL l < 2 := by
          rw [← hww, ← cp_ww_eq, cL_opow le_rfl]
          have h21 : (2 : Ordinal.{0}) - 1 ≤ 1 := by
            rw [Ordinal.sub_le, one_add_one_eq_two]
          exact h21.trans_lt one_lt_two
        rw [xtOrec_succ hl hc]
        exact Order.one_le_iff_pos.2 hl0
    exact (hle.trans_lt hnf).trans hρtop
  · have hfix : upsilon l = l := hfx.symm
    rw [hfix] at hρE hρ1 ⊢
    by_cases hG : IsGP l
    · have hGl : GG l ≠ l := fun e => h ⟨hfix, e⟩
      rw [nnGG hX0 hS l hl hl1 hG hGl]
      have ha0 : invGG l ≠ 0 := by
        intro h0; have := nn_GG_inv hG; rw [h0, GG_zero] at this; exact hl0.ne this
      have hal : invGG l < l := by
        have hV := nn_GG_inv hG
        refine lt_of_le_of_ne (by have := GG_strictMono.id_le (invGG l); rwa [hV] at this) fun e => ?_
        rw [e] at hV; exact hGl hV
      exact ((add_lt_add_iff_left _).2 ((lg_le ha0).trans_lt hal)).trans (htop _ hρE hρ1)
    · rw [nnLev hX0 l hl hl1 hfix hG]
      obtain ⟨-, hγl, -, hα0, hαl, -, -⟩ := nn_lev_data hfix (nn_ng_of_gp hl0 hG)
      obtain ⟨-, -, -, hlim, -⟩ := nn_fix_facts hl hfix
      calc l * levG l + lg (invG (levG l) l) < l * levG l + l :=
            (add_lt_add_iff_left _).2 ((lg_le hα0).trans_lt hαl)
        _ = l * (levG l + 1) := (mul_add_one _ _).symm
        _ ≤ l * l := mul_le_mul_right (hlim.add_one_lt hγl).le l
        _ ≤ l * l + l := le_self_add
        _ < X.top l := htop _ hρE hρ1

/-- **Every frontier of `X` is a fixed point of `GG`.** -/
theorem nnFr_GG (hX0 : NnLin X) (hS : NnSq X) (htop : ∀ x, InE x → x < Om1 → x * x + x < X.top x)
    {l : Ordinal.{0}} (h : XtFr X l) (hl1 : l < Om1) : upsilon l = l ∧ GG l = l := by
  by_contra hn
  exact (nnLt_top hX0 hS htop h.1 hl1 hn).ne h.2

/-- A positive limit of fixed points of `GG` is a fixed point of `GG`. -/
theorem nn_GGfix_of_cof {L : Ordinal.{0}} (hL0 : 0 < L)
    (hcof : ∀ ν < L, ∃ μ, GG μ = μ ∧ ν < μ ∧ μ < L) : GG L = L := by
  have hlim : IsSuccLimit L := by
    refine Ordinal.isSuccLimit_iff.2 ⟨hL0.ne', isSuccPrelimit_of_succ_lt fun a ha => ?_⟩
    obtain ⟨μ, -, h1, h2⟩ := hcof a ha
    exact (Order.succ_le_of_lt h1).trans_lt h2
  refine le_antisymm ?_ (GG_strictMono.id_le L)
  rw [GG_normal.apply_of_isSuccLimit hlim]
  refine ciSup_le' fun y => ?_
  obtain ⟨μ, hμ, h1, h2⟩ := hcof y.1 y.2
  exact (GG_strictMono h1).le.trans (hμ.le.trans h2.le)

/-- **The first limit of frontiers of `X` is a fixed point of `GG`.** -/
theorem nnB1_GG (hX0 : NnLin X) (hS : NnSq X) (htop : ∀ x, InE x → x < Om1 → x * x + x < X.top x)
    (hP : XtTopPkg X) : GG (xtB1 X) = xtB1 X := by
  obtain ⟨h0, hcof⟩ := xtB1_spec hP
  refine nn_GGfix_of_cof h0 fun ν hν => ?_
  obtain ⟨μ, hμ, h1, h2⟩ := hcof ν hν
  exact ⟨μ, (nnFr_GG hX0 hS htop hμ (h2.trans (xtB1_lt_Om1 hP))).2, h1, h2⟩

/-- The top of every layer `xtLL k` is above `x·x + x`. -/
theorem nnLL_top (k : ℕ) : ∀ x, InE x → x < Om1 → x * x + x < (xtLL k).sys.top x := by
  intro x hx hx1
  rw [xtLL_top]
  exact (nn_sq_lt_B hx hx1).trans_le (le_mul_left _ (opow_pos _ hx.pos))

/-- **Every `Λ⁺_k` is a fixed point of `GG`.** -/
theorem nnLamK_GG (k : ℕ) : GG (xtLamK k) = xtLamK k :=
  nnB1_GG (nnLin_LL k) (nnSq_LL k) (nnLL_top k) (xtLL k).topPkg

/-- **`Λ_{ω²}` is a fixed point of `GG`.** -/
theorem nnW2_GG : GG xtFamW2.famSup = xtFamW2.famSup := by
  refine nn_GGfix_of_cof (lt_of_le_of_lt zero_le (xtFamW2.famBd_lt 0)) fun ν hν => ?_
  obtain ⟨k, hk⟩ := xtFamW2.famLt hν
  exact ⟨xtLamK k, nnLamK_GG k, hk, xtFamW2.famBd_lt k⟩

end Googology.Trans.PoR.InaccPsi.R2.Nn

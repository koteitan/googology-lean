import Googology.Trans.PoR.InaccPsi.R2.YwSep

/-!
# YwImg: LEMMA IMG BELOW `X^ρ = ϑᵖ(Ω₁·Ω₁·2)` — EVERY POINT OF EVERY LEVEL `β` (ONE PROOF FOR ALL `β`)

`Yr.yrImg` gives Lemma IMG below `ϑᵖ(Ω₁·Ω₁ + w)` for ADMISSIBLE `w` (no fixed point of `ν ↦ ϑᵖ(Ω₁·Ω₁ + ν)` at or
below `w`), so it stops at the first fixed point of `Γ` (the reading of `B_Γ`).  Here Lemma IMG holds at EVERY point
`E = ϑᵖ(Ω₁·(Ω₁+j) + σ)` of EVERY level `j` (the fixed points of `Γ` are the points of level `1`, the countable copy of
`F_β` is level `β`), and at every `ε`-number between them, so below `X^ρ = ϑᵖ(Ω₁·Ω₁·2)`:

* `ywI_atom` (**LEMMA IMG AT A POINT OF LEVEL `j`**, given it below): the reach test going down at the reach
  `E·E + E + E·j + z` (`Yw.ywV_lh`); in a copy `f` with `f(E) < π(E)` take `u ∈ (E', E)` with `π(u) = f(E)`
  (`Gw.gw_key`, `E'` from `Yw.ywLB`); `f(E·E) ≥ f(E)²` (`Gb.GbK.gbImg`), `f(E·j) ≥ f(E)·π(j)` (`He.he_wz_mul`),
  `f(z) ≥ π(z)` and `π(u·c) = π(u)·π(c)` (`He.he_pi_mul`) give `u ≤₁ u·u + u + u·j + z` in `R₁⁺`, which
  `Yw.ywSep` excludes;
* `ywDec`, `ywLt_X`, `ywVeb_rep` (every `ε`-number of `(max(ρ,q,t), ϑᵖ(Ω₁·q + t))` is of Veblen level), `ywI_veb`
  (**LEMMA IMG AT EVERY `ε`-NUMBER `ϑᵖ(Ω₁·q + t)` OF VEBLEN LEVEL BELOW `X^ρ`**: the argument of `Xk.xkImg_step`
  with the lower bound `max(ρ+1, q, t)` in place of the base atom);
* `ywImg` (**LEMMA IMG BELOW `X^ρ`**, one application of `Gn.gnImg_of_eps`), `ywImg_atom` (at every point of every
  level, in particular at the fixed points of `Γ`), `ywPkg` (Lemma IMG (gated) for a specified function below `X^ρ`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yw

open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.He
  Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Gq Googology.Trans.PoR.InaccPsi.R2.Hb
  Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gj Googology.Trans.PoR.InaccPsi.R2.Gw Googology.Trans.PoR.InaccPsi.R2.Xk
  Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Rk Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Gf
open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gb

/-- **`X^x = ϑˣ(Ω₁·Ω₁·2)`.** -/
noncomputable abbrev ywX (x : Ordinal.{0}) : Ordinal.{0} := vt x (Om1 * (Om1 * 2 + 0) + 0)

section Dec

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem ywX_facts : ywX x ∈ Tset x ∧ x < ywX x ∧ ywX x < Om1 ∧ InE (ywX x) := by
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  have h0Ω : (0 : Ordinal.{0}) < Om1 := hx.pos.trans hx1
  have h2x : (2 : Ordinal.{0}) < x := by
    have := natCast_lt_omega0 2
    exact_mod_cast this.trans (omega0_lt_inE hx)
  have h2T : (2 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 h2x.le
  have h12 : (1 : Ordinal.{0}) ≤ 2 := by norm_num
  obtain ⟨-, -, hvT, hxv, hv1, hvE, -, -, -, -⟩ := lq_facts hx hx1 h12 h2T (h2x.trans hx1) h0T h0Ω h0T h0Ω
  exact ⟨hvT, hxv, hv1, hvE⟩

/-- **The argument of an `ε`-number below `X^x` is below `Ω₁·Ω₁·2`.** -/
theorem ywLt_X {ξ : Ordinal.{0}} (hξT : ξ ∈ Tset x) (hξ2 : ξ < OmTwo) (hxv : x < vt x ξ) (hv : vt x ξ < ywX x) :
    ξ < Om1 * Om1 + Om1 * Om1 := by
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  have h0Ω : (0 : Ordinal.{0}) < Om1 := hx.pos.trans hx1
  have h2x : (2 : Ordinal.{0}) < x := by
    have := natCast_lt_omega0 2
    exact_mod_cast this.trans (omega0_lt_inE hx)
  have h2T : (2 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 h2x.le
  have h12 : (1 : Ordinal.{0}) ≤ 2 := by norm_num
  have h := lqLt_of_vt_lt hx hx1 hξT hξ2 h12 h2T (h2x.trans hx1) h0T h0Ω h0T h0Ω (h2x.trans hxv)
    (hx.pos.trans hxv) (hx.pos.trans hxv) hv
  have e2 : Om1 * (Om1 * 2 + 0) + 0 = Om1 * Om1 + Om1 * Om1 := by
    rw [add_zero, add_zero, show (2 : Ordinal.{0}) = 1 + 1 by norm_num, mul_add, mul_one, mul_add]
  rwa [e2] at h

/-- **The decomposition of an argument in `[Ω₁·Ω₁, Ω₁·Ω₁·2)`.** -/
theorem ywDec {ξ : Ordinal.{0}} (hξT : ξ ∈ Tset x) (hξ2 : ξ < OmTwo) (hs : Om1 * Om1 ≤ ξ)
    (hξX : ξ < Om1 * Om1 + Om1 * Om1) :
    ∃ j σ, j ∈ Tset x ∧ j < Om1 ∧ σ ∈ Tset x ∧ σ < Om1 ∧ ξ = Om1 * (Om1 * 1 + j) + σ := by
  obtain ⟨h1T, h1Ω⟩ := yw_one hx hx1
  obtain ⟨w, hw⟩ : ∃ w, ξ = Om1 * Om1 + w := ⟨ξ - Om1 * Om1, (Ordinal.add_sub_cancel_of_le hs).symm⟩
  have hwlt : w < Om1 * Om1 := by rw [hw] at hξX; exact (add_lt_add_iff_left _).1 hξX
  set j := w / Om1 with hj
  set σ := w % Om1 with hσ
  have hjΩ : j < Om1 := (Ordinal.lt_mul_iff_div_lt (Ordinal.omega_pos 1).ne').1 hwlt
  have hσΩ : σ < Om1 := Ordinal.mod_lt w (Ordinal.omega_pos 1).ne'
  have hξe : ξ = Om1 * (Om1 * 1 + j) + σ := by
    rw [hw, mul_one, mul_add, add_assoc, hj, hσ, Ordinal.div_add_mod]
  have hξT' := hξT
  rw [hξe] at hξT'
  have hjT : j ∈ Tset x := (rkArg_T hx hx1 h1Ω hjΩ hσΩ hξT').2
  have hΩξ : Om1 ≤ ξ := (le_mul_left Om1 (Ordinal.omega_pos 1)).trans hs
  obtain ⟨-, hσT, -, -⟩ := lu_split hx hx1 hξT hξ2 hΩξ
  have hmod : ξ % Om1 = σ := by
    rw [hξe, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hσΩ]
  rw [hmod] at hσT
  exact ⟨j, σ, hjT, hjΩ, hσT, hσΩ, hξe⟩

/-- **Every `ε`-number of `(max(q,t), ϑˣ(Ω₁·q + t))` below `X^x` is of Veblen level**: a point of some level `j` with
`q, t` below it lies above `ϑˣ(Ω₁·q + t)` ([W07a] Lemma 3.30 through `lqVt_lt` with `γ' = 0`). -/
theorem ywVeb_rep {q t u : Ordinal.{0}} (hq1 : 1 ≤ q) (hqT : q ∈ Tset x) (hqΩ : q < Om1) (htT : t ∈ Tset x)
    (ht1 : t < Om1) (hX : vt x (Om1 * q + t) < ywX x) (huE : InE u) (hxu : x < u) (hqu : q < u) (htu : t < u)
    (hue : u < vt x (Om1 * q + t)) :
    ∃ q' t', 1 ≤ q' ∧ q' ∈ Tset x ∧ q' < Om1 ∧ t' ∈ Tset x ∧ t' < Om1 ∧ glA q' t' x = u := by
  obtain ⟨h1T, h1Ω⟩ := yw_one hx hx1
  obtain ⟨hvT, -, hv1, -, -, -⟩ := glA_facts hx hx1 hq1 hqT hqΩ htT ht1
  have hu1 : u < Om1 := hue.trans hv1
  have huT : u ∈ Tset x := vz_T_down hx hx1 hvT hv1 hue.le
  obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hx hx1 huT hxu.le hu1 (inE_indec huE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξv]; exact hxu, by rw [hξv]; exact huE⟩
  rcases lt_or_ge ξ (Om1 * Om1) with hξs | hξs
  · obtain ⟨hq'1, hrT, hr1, hdec⟩ := lu_split hx hx1 hξT hξ2 hΩξ
    have hq'T : ξ / Om1 ∈ Tset x := lgQuot_mem hx hx1 hξT hξs
    have hq'Ω : ξ / Om1 < Om1 := (Ordinal.lt_mul_iff_div_lt (Ordinal.omega_pos 1).ne').1 hξs
    refine ⟨ξ / Om1, ξ % Om1, hq'1, hq'T, hq'Ω, hrT, hr1, ?_⟩
    show vt x (Om1 * (ξ / Om1) + ξ % Om1) = u
    rw [hdec, hξv]
  · exfalso
    have hξX := ywLt_X hx hx1 hξT hξ2 (by rw [hξv]; exact hxu) (by rw [hξv]; exact hue.trans hX)
    obtain ⟨j, σ, hjT, hjΩ, hσT, hσΩ, hξe⟩ := ywDec hx hx1 hξT hξ2 hξs hξX
    have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
    have harg : Om1 * (Om1 * 0 + q) + t < Om1 * (Om1 * 1 + j) + σ := by
      rw [mul_zero, zero_add]
      calc Om1 * q + t < Om1 * q + Om1 := (add_lt_add_iff_left _).2 ht1
        _ = Om1 * (q + 1) := (mul_add_one _ _).symm
        _ ≤ Om1 * (Om1 * 1) := mul_le_mul_right (by rw [mul_one]; exact Order.add_one_le_of_lt hqΩ) _
        _ ≤ Om1 * (Om1 * 1 + j) := mul_le_mul_right le_self_add _
        _ ≤ _ := le_self_add
    have h := lqVt_lt hx hx1 h0T (hx.pos.trans hx1) hqT hqΩ htT ht1 le_rfl h1T h1Ω hjT hjΩ hσT hσΩ harg
      (by rw [← hξe, hξv]; exact lt_of_le_of_lt zero_le hqu) (by rw [← hξe, hξv]; exact hqu)
      (by rw [← hξe, hξv]; exact htu)
    rw [mul_zero, zero_add, ← hξe, hξv] at h
    exact absurd (h.trans hue) (lt_irrefl _)

end Dec

section Img

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **LEMMA IMG AT A POINT `E = ϑᵖ(Ω₁·(Ω₁+j) + σ)` OF ANY LEVEL `j`** (above `Γ_{ρ+1}`), given Lemma IMG below `E`. -/
theorem ywI_atom {j σ : Ordinal.{0}} (hjT : j ∈ Tset ρ) (hjΩ : j < Om1) (hσT : σ ∈ Tset ρ) (hσΩ : σ < Om1)
    (hG : gq 0 ρ < ywV j σ ρ) (IH : ∀ u, u < ywV j σ ρ → GnI ρ δ u) : GnI ρ δ (ywV j σ ρ) := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  obtain ⟨hET0, hρEE, hE1, hE, hjE, hσE, -⟩ := ywV_facts hρE hρ1 hjT hjΩ hσT hσΩ
  set E := ywV j σ ρ with hEdef
  set z := lqZeta ρ (Om1 * (Om1 * 1 + j)) σ with hzdef
  have hzE : z < E := ywZeta_le.trans_lt hσE
  have hL := ywV_lh hρE hρ1 hjT hjΩ hσT hσΩ
  rw [← hEdef, ← hzdef] at hL
  obtain ⟨E', hLE', hjE', hσE', hE'E, hJ⟩ := ywLB hρE hρ1 hjT hjΩ hσT hσΩ hG
  have hρG : ρ < gq 0 ρ := (gfq0_facts hρE hρ1).2.1
  have hρE' : ρ < E' := hρG.trans_le hLE'
  have hsep : ∀ a, InE a → E' < a → a < E → ¬ le1R a (a * a + a + a * j + z) := fun a ha h1 h2 =>
    ywSep hρE hρ1 hjT hjΩ hσT hσΩ hρE' hjE' hσE' hJ ha h1 h2
  have hET : E ∈ Tset ρ ∧ E < Om1 := ⟨hET0, hE1⟩
  have hEδ : E < δ := gn_lt_δ h hET.1 hET.2
  have hδI := inE_indec h.δE
  have hEI := inE_indec hE
  have hE0 : 0 < E := hE.pos
  have hEEδ : E + E < δ := hδI.add_lt hEδ hEδ
  have hPδ : E * E < δ := h.δE.mul_lt hEδ hEδ
  have hPEδ : E * E + E < δ := hδI.add_lt hPδ hEδ
  have hjδ : E * j < δ := h.δE.mul_lt hEδ (hjE.trans hEδ)
  have hTjδ : E * E + E + E * j < δ := hδI.add_lt hPEδ hjδ
  have hTopδ : E * E + E + E * j + z < δ := hδI.add_lt hTjδ (hzE.trans hEδ)
  have hEP : E < E * E := lt_mul_of_one_lt_right hE0 (lu_one_lt_E hE)
  have hPe : E * E = ω ^ (E + E) := by
    conv_lhs => rw [← show ω ^ E = E from hE]
    rw [← opow_add]
  have hρP : ρ ≤ E * E := hρEE.le.trans hEP.le
  have hEjP : E * j < E * E := (mul_lt_mul_iff_right₀ hE0).2 hjE
  have hsrc : le1 E (E * E + E + E * j + z) := (h.lowδ _ _ hρEE hTopδ.le).2 hL.1
  -- witness sets
  obtain ⟨W1, Z1, w1, m1, -, -, b1⟩ := gnI_use h (IH E' hE'E)
  obtain ⟨W2, Z2, w2, m2, -, -, b2⟩ := gnI_use h (IH z hzE)
  set W3 := insert E (W1 ∪ W2) with hW3
  set Z3 := Z1 ∪ Z2 with hZ3
  have w3 : WZ ρ δ W3 Z3 := (w1.union w2).insW hρEE.le hEδ (Or.inl hEI)
  have hE3 : E ∈ W3 := Finset.mem_insert_self _ _
  set W4 := insert (E + E) W3 with hW4
  have w4 : WZ ρ δ W4 Z3 := w3.insW (hρEE.le.trans le_self_add) hEEδ
    (Or.inr ⟨E, Finset.mem_union_left _ hE3, E, Finset.mem_union_left _ hE3, lt_add_of_pos_right _ hE0,
      lt_add_of_pos_right _ hE0, rfl⟩)
  have h34 : W3 ⊆ W4 := Finset.subset_insert _ _
  set W5 := insert (E * E) W4 with hW5
  have w5 : WZ ρ δ W5 Z3 := w4.insW hρP hPδ (Or.inl (by rw [hPe]; exact indec_opow _))
  have h45 : W4 ⊆ W5 := Finset.subset_insert _ _
  set W6 := insert (E * E + E) W5 with hW6
  have w6 : WZ ρ δ W6 Z3 := w5.insW (hρP.trans le_self_add) hPEδ
    (Or.inr ⟨E * E, Finset.mem_union_left _ (Finset.mem_insert_self _ _), E,
      Finset.mem_union_left _ (h45 (h34 hE3)), lt_add_of_pos_right _ hE0, hEP.trans_le le_self_add, rfl⟩)
  have h56 : W5 ⊆ W6 := Finset.subset_insert _ _
  have hE6 : E ∈ W6 := h56 (h45 (h34 hE3))
  -- the term `E·j`
  obtain ⟨W8, Z8, w8, h68, hZ38, hTj8, hJ8⟩ : ∃ W8 Z8 : Finset Ordinal.{0}, WZ ρ δ W8 Z8 ∧ W6 ⊆ W8 ∧ Z3 ⊆ Z8 ∧
      E * E + E + E * j ∈ W8 ∧ ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W8 ⊆ A → ↑Z8 ⊆ A →
        ImgCtx ρ A f → j ∈ TB ρ (f ρ) ∧ f (E * E + E) + f E * pi (f ρ) ρ j ≤ f (E * E + E + E * j) := by
    rcases eq_or_ne j 0 with hj0 | hj0
    · have hmem : E * E + E + E * j ∈ W6 := by rw [hj0, mul_zero, add_zero]; exact Finset.mem_insert_self _ _
      refine ⟨W6, Z3, w6, subset_refl _, subset_refl _, hmem, fun A f _ _ C => ?_⟩
      have hB := h.img_bases C
      have h0f : (0 : Ordinal.{0}) < f ρ := hB.1.pos
      have h0TB : (0 : Ordinal.{0}) ∈ TB ρ (f ρ) := (TB_inter_lt hB hρE.pos).2 h0f
      refine ⟨by rw [hj0]; exact h0TB, ?_⟩
      rw [hj0, pi_lt hB h0f, mul_zero, add_zero, mul_zero, add_zero]
    · obtain ⟨W7, Z7, w7, h67, hZ37, hEj7, hc7⟩ :=
        he_wz_mul h w6 hE6 hρEE hE hEδ IH j hjE (pos_iff_ne_zero.2 hj0)
      have hEj0 : 0 < E * j := mul_pos hE0 (pos_iff_ne_zero.2 hj0)
      have hT1_7 : E * E + E ∈ W7 := h67 (Finset.mem_insert_self _ _)
      refine ⟨insert (E * E + E + E * j) W7, Z7,
        w7.insW ((hρP.trans le_self_add).trans le_self_add) hTjδ
          (Or.inr ⟨E * E + E, Finset.mem_union_left _ hT1_7, E * j, Finset.mem_union_left _ hEj7,
            lt_add_of_pos_right _ hEj0, hEjP.trans_le (le_self_add.trans le_self_add), rfl⟩),
        fun a ha => Finset.mem_insert_of_mem (h67 ha), hZ37, Finset.mem_insert_self _ _,
        fun A f hW hZ C => ?_⟩
      have hW7 : ↑W7 ⊆ A := fun a ha => hW (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 ha)))
      obtain ⟨hjTB, hjle⟩ := hc7 A f hW7 hZ C
      refine ⟨hjTB, ?_⟩
      have hT1A : E * E + E ∈ A := hW7 (Finset.mem_coe.2 hT1_7)
      have hEjA : E * j ∈ A := hW7 (Finset.mem_coe.2 hEj7)
      have hTjA : E * E + E + E * j ∈ A := hW (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
      rw [← C.add _ hT1A _ hEjA _ hTjA rfl]
      exact add_le_add le_rfl hjle
  have hzW8 : z ∈ W8 ∪ Z8 := by
    rcases Finset.mem_union.1 m2 with hm | hm
    · exact Finset.mem_union_left _ (h68 (h56 (h45 (h34 (Finset.mem_insert_of_mem (Finset.mem_union_right _ hm))))))
    · exact Finset.mem_union_right _ (hZ38 (Finset.mem_union_right _ hm))
  obtain ⟨W9, w9, h89, hTop⟩ : ∃ W9 : Finset Ordinal.{0}, WZ ρ δ W9 Z8 ∧ W8 ⊆ W9 ∧
      E * E + E + E * j + z ∈ W9 := by
    rcases eq_or_ne z 0 with hz0 | hz0
    · exact ⟨W8, w8, subset_refl _, by rw [hz0, add_zero]; exact hTj8⟩
    · refine ⟨insert (E * E + E + E * j + z) W8, w8.insW
        (((hρP.trans le_self_add).trans le_self_add).trans le_self_add) hTopδ
        (Or.inr ⟨_, Finset.mem_union_left _ hTj8, z, hzW8, lt_add_of_pos_right _ (pos_iff_ne_zero.2 hz0),
          hzE.trans_le (((hEP.le.trans le_self_add).trans le_self_add).trans le_self_add), rfl⟩),
        Finset.subset_insert _ _, Finset.mem_insert_self _ _⟩
  have hsub : ∀ a, a ∈ W6 → a ∈ W9 := fun a ha => h89 (h68 ha)
  refine gnI_mk h w9 (Finset.mem_union_left _ (hsub _ hE6)) hET.1 hET.2 (fun A f hW hZ C => ?_)
  have hZ8 : ↑Z8 ⊆ A := fun a ha => hZ (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 ha)))
  have hWA : ∀ a, a ∈ W6 → a ∈ A := fun a ha => hW (Finset.mem_coe.2 (hsub a ha))
  have hW8A : ↑W8 ⊆ A := fun a ha => hW (Finset.mem_coe.2 (h89 (Finset.mem_coe.1 ha)))
  have hW1 : ↑W1 ⊆ A := fun a ha => hWA a (h56 (h45 (h34 (Finset.mem_insert_of_mem
    (Finset.mem_union_left _ (Finset.mem_coe.1 ha))))))
  have hW2 : ↑W2 ⊆ A := fun a ha => hWA a (h56 (h45 (h34 (Finset.mem_insert_of_mem
    (Finset.mem_union_right _ (Finset.mem_coe.1 ha))))))
  have hZ1 : ↑Z1 ⊆ A := fun a ha => hZ8 (Finset.mem_coe.2 (hZ38 (Finset.mem_union_left _ (Finset.mem_coe.1 ha))))
  have hZ2 : ↑Z2 ⊆ A := fun a ha => hZ8 (Finset.mem_coe.2 (hZ38 (Finset.mem_union_right _ (Finset.mem_coe.1 ha))))
  obtain ⟨hE'A, hE'TB, pE'⟩ := b1 A f hW1 hZ1 C
  obtain ⟨hzA, hzTB, pz⟩ := b2 A f hW2 hZ2 C
  obtain ⟨hjTB, hjle⟩ := hJ8 A f hW8A hZ8 C
  have hEA : E ∈ A := hWA _ hE6
  have hEEA : E + E ∈ A := hWA _ (h56 (h45 (Finset.mem_insert_self _ _)))
  have hPA : E * E ∈ A := hWA _ (h56 (Finset.mem_insert_self _ _))
  have hPEA : E * E + E ∈ A := hWA _ (Finset.mem_insert_self _ _)
  have hTjA : E * E + E + E * j ∈ A := hW8A (Finset.mem_coe.2 hTj8)
  have hTopA : E * E + E + E * j + z ∈ A := hW (Finset.mem_coe.2 hTop)
  have hETB : E ∈ TB ρ (f ρ) := gnI_TB h C hET.1 (fun p hp => hZ (by simp [hp]))
  have hB := h.img_bases C
  by_contra hlt
  push Not at hlt
  by_cases hU : UpsPt (f E)
  · exact absurd (gw_pbig h hET hρEE A f C hEA hETB hU) (not_lt.2 hlt.le)
  obtain ⟨-, hPge⟩ := GbK.gbImg h hE hρEE hEδ C hEA hEEA hPA hPEA
  have hfT1 : f (E * E + E) = f (E * E) + f E := (C.add _ hPA _ hEA _ hPEA rfl).symm
  have hfTop : f (E * E + E + E * j + z) = f (E * E + E + E * j) + f z :=
    (C.add _ hTjA _ hzA _ hTopA rfl).symm
  have himg : le1 (f E) (f (E * E + E + E * j + z)) := C.cov1 _ hEA _ hTopA hsrc
  have hR := (C.sk _ (C.low _ hEA) hU _).1 himg
  obtain ⟨u, huTB, hpu, hE'u, huE, huI⟩ :=
    gw_key h hE hET hρEE hEEδ A f C hEA hEEA hETB E' hE'E hE'A hE'TB pE' hlt
  have hu1 : u < Om1 := huE.trans hET.2
  have hρu : ρ < u := hρE'.trans hE'u
  obtain ⟨l, hl, hlTB, hpl⟩ := lh_pi hB huTB hρu hu1
  have hle0 := hpl.2 _ (by rw [hpu]; exact hR)
  have hjΩ' : j < Om1 := hjΩ
  obtain ⟨huuTB, huuπ⟩ := he_pi_mul C.ups h.ρU hB huTB hu1 huI u huTB hu1
  obtain ⟨hujTB, hujπ⟩ := he_pi_mul C.ups h.ρU hB huTB hu1 huI j hjTB hjΩ'
  obtain ⟨hs1TB, hs1π⟩ := pi_add hB huuTB huTB
  obtain ⟨hs2TB, hs2π⟩ := pi_add hB hs1TB hujTB
  obtain ⟨hs3TB, hs3π⟩ := pi_add hB hs2TB hzTB
  have hle1 : pi (f ρ) ρ (u * u + u + u * j + z) ≤ pi (f ρ) ρ l := by
    rw [hs3π, hs2π, hs1π, huuπ, hujπ, hpu]
    refine le_trans ?_ hle0
    rw [hfTop]
    refine add_le_add ?_ pz
    refine le_trans ?_ hjle
    rw [hfT1]
    exact add_le_add (add_le_add hPge le_rfl) le_rfl
  have hle2 : u * u + u + u * j + z ≤ l := ((pi_bijOn hB).2.le_iff_le hs3TB hlTB).1 hle1
  have hlo : u ≤ u * u + u + u * j + z := ((le_add_self : u ≤ u * u + u).trans le_self_add).trans le_self_add
  exact hsep u huI hE'u huE (le1R_of_le hlo hle2 hl.1)

/-- **LEMMA IMG AT AN `ε`-NUMBER `e = ϑᵖ(Ω₁·q + t)` OF VEBLEN LEVEL BELOW `X^ρ`**, given it below `e`
(the argument of `Xk.xkImg_step`, with the lower bound `max(ρ+1, q, t)` in place of the base atom). -/
theorem ywI_veb {q t : Ordinal.{0}} (hq1 : 1 ≤ q) (hqT : q ∈ Tset ρ) (hqΩ : q < Om1) (htT : t ∈ Tset ρ)
    (ht1 : t < Om1) (hX : glA q t ρ < ywX ρ) (IHe : ∀ u, u < glA q t ρ → GnI ρ δ u) : GnI ρ δ (glA q t ρ) := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  obtain ⟨-, hρe, -, hE, hqe, hte⟩ := glA_facts hρE hρ1 hq1 hqT hqΩ htT ht1
  -- the fixed points of `φ(q, ·)` below `e`
  have hPq : ∃ P0, P0 < glA q t ρ ∧ ∀ u, LuP (q + 1) u → u < glA q t ρ → u ≤ P0 := by
    by_cases hz : veblen (q + 1) 0 ≤ glA q t ρ
    · obtain ⟨a, ha1, ha2⟩ := hb_floor (q + 1) (j0 := 0) hz
      refine ⟨veblen (q + 1) a, lt_of_le_of_ne ha1 (fun e' =>
        glA_notP hρE hρ1 hq1 hqT hqΩ htT ht1 (by rw [← e']; exact ⟨a, rfl⟩)), fun u hu hue => ?_⟩
      obtain ⟨j, rfl⟩ := hu
      have hj : j < a + 1 := (veblen_lt_veblen_iff_right).1 (hue.trans ha2)
      exact (isNormal_veblen _).monotone (Order.lt_add_one_iff.1 hj)
    · push Not at hz
      refine ⟨0, hE.pos, fun u hu hue => ?_⟩
      exfalso
      obtain ⟨j, rfl⟩ := hu
      exact absurd (hue.trans hz) (not_lt.2 ((isNormal_veblen _).monotone zero_le))
  -- the earlier points of level `q`
  have hRq : ∃ R0, R0 < glA q t ρ ∧ ∀ t', t' ∈ Tset ρ → t' < Om1 → t' < t → R0 < glA q t' ρ →
      luZeta ρ q t' < luZeta ρ q t := by
    rcases zero_or_succ_or_isSuccLimit t with ht0 | ⟨s, hs⟩ | hlim
    · refine ⟨0, hE.pos, fun t' _ _ ht' _ => ?_⟩
      exact absurd ht' (by rw [ht0]; exact not_lt.2 zero_le)
    · have hts : t = s + 1 := by rw [← hs, succ_eq_add_one]
      have hst : s < t := by rw [hts]; exact lt_add_one s
      obtain ⟨hsT, hs1⟩ : s ∈ Tset ρ ∧ s < Om1 := ⟨vz_T_down hρE hρ1 htT ht1 hst.le, hst.trans ht1⟩
      refine ⟨glA q s ρ, glA_lt_of hρE hρ1 hq1 hqT hqΩ hsT htT ht1 hst, fun t' ht'T ht'1 ht' hR => ?_⟩
      exfalso
      have hst' : t' ≤ s := by rw [hts] at ht'; exact Order.lt_add_one_iff.1 ht'
      have := (glA_le_iff hρE hρ1 hq1 hqT hqΩ ht'T ht'1 hsT hs1).2 hst'
      exact absurd hR (not_lt.2 this)
    · by_cases hcl : ∃ σ, σ < t ∧ t < vt ρ (Om1 * q + σ)
      · have hz : luZeta ρ q t = lg t := by unfold luZeta; rw [if_pos hcl]
        have ht0 : t ≠ 0 := hlim.bot_lt.ne'
        obtain ⟨c', hcs, -, hc't⟩ := lg_split ht0
        obtain ⟨hc'T, hc'1⟩ : c' ∈ Tset ρ ∧ c' < Om1 := ⟨vz_T_down hρE hρ1 htT ht1 hc't.le, hc't.trans ht1⟩
        refine ⟨glA q c' ρ, glA_lt_of hρE hρ1 hq1 hqT hqΩ hc'T htT ht1 hc't, fun t' ht'T ht'1 ht' hR => ?_⟩
        have hc't' : c' < t' := (glA_lt_iff hρE hρ1 hq1 hqT hqΩ hc'T hc'1 ht'T ht'1).1 hR
        rw [hz]
        set z := lg t with hzdef
        obtain ⟨δ', hδ'⟩ : ∃ δ', t' = c' + δ' := ⟨t' - c', (Ordinal.add_sub_cancel_of_le hc't'.le).symm⟩
        have hδ0 : δ' ≠ 0 := by rintro rfl; rw [add_zero] at hδ'; exact absurd hδ' hc't'.ne'
        have hδlt : δ' < ω ^ z := by
          have : c' + δ' < c' + ω ^ z := by rw [← hδ', ← hcs]; exact ht'
          exact (add_lt_add_iff_left _).1 this
        have hlgd : lg t' < z := by
          rw [hδ', gz_lg_add _ hδ0]
          by_contra hge; push Not at hge
          obtain ⟨δ'', hδs, -, -⟩ := lg_split hδ0
          have h1 : ω ^ z ≤ ω ^ lg δ' := opow_le_opow_right omega0_pos hge
          have h2 : ω ^ lg δ' ≤ δ' := (le_add_self (a := ω ^ lg δ') (b := δ'')).trans_eq hδs.symm
          exact absurd hδlt (not_lt.2 (h1.trans h2))
        exact lu_zeta_le_lg.trans_lt hlgd
      · push Not at hcl
        refine ⟨t, hte, fun t' _ _ ht' hR => ?_⟩
        exact absurd (hcl t' ht') (not_le.2 hR)
  obtain ⟨P0, hP0e, hP0⟩ := hPq
  obtain ⟨R0, hR0e, hR0⟩ := hRq
  set M0 := max (ρ + 1) (max q t) with hM0
  set E' := max (max M0 (q + 1)) (max P0 R0) with hE'def
  have hM0E' : M0 ≤ E' := (le_max_left _ _).trans (le_max_left _ _)
  have hρE' : ρ < E' := (lt_add_one ρ).trans_le ((le_max_left _ _).trans hM0E')
  have hqE' : q < E' := (lt_add_one q).trans_le ((le_max_right _ _).trans (le_max_left _ _))
  have hPE' : P0 ≤ E' := (le_max_left _ _).trans (le_max_right _ _)
  have hRE' : R0 ≤ E' := (le_max_right _ _).trans (le_max_right _ _)
  have hqM : q ≤ M0 := (le_max_left _ _).trans (le_max_right _ _)
  have htM : t ≤ M0 := (le_max_right _ _).trans (le_max_right _ _)
  have hlim := ev_isSuccLimit_of_inE hE
  have hE'e : E' < glA q t ρ :=
    max_lt (max_lt (max_lt (hlim.add_one_lt hρe) (max_lt hqe hte)) (hlim.add_one_lt hqe)) (max_lt hP0e hR0e)
  refine he_img_down h hq1 hqT hqΩ htT ht1 hρE' hqE' hE'e (fun u hu hE'u hue => ?_) IHe
  have hM0u : M0 < u := hM0E'.trans_lt hE'u
  obtain ⟨q', t', hq'1, hq'T, hq'Ω, ht'T, ht'1, hu'⟩ := ywVeb_rep hρE hρ1 hq1 hqT hqΩ htT ht1 hX hu
    ((lt_add_one ρ).trans ((le_max_left _ _).trans_lt hM0u)) (hqM.trans_lt hM0u) (htM.trans_lt hM0u) hue
  have hq'q : q' ≤ q := by
    by_contra hlt
    push Not at hlt
    have hP : LuP (q + 1) u := by
      rw [← hu']
      exact (gq_veb_level hρE hρ1 hq'1 hq'T hq'Ω ht'T ht'1 le_add_self).2 (Order.add_one_le_of_lt hlt)
    exact absurd (hE'u.trans_le' (hP0 u hP hue |>.trans hPE')) (lt_irrefl _)
  obtain ⟨H1', H2', -⟩ := he_lhq hρE hρ1 hq'1 hq'T hq'Ω ht'T ht'1
  rw [hu'] at H1' H2'
  refine ⟨q', _, hq'q, H1', H2', fun e' => ?_⟩
  subst e'
  have ht't : t' < t := by
    rw [← hu'] at hue
    exact (glA_lt_iff hρE hρ1 hq1 hqT hqΩ ht'T ht'1 htT ht1).1 hue
  exact hR0 t' ht'T ht'1 ht't (hRE'.trans_lt (hu' ▸ hE'u))

/-- **LEMMA IMG BELOW `X^ρ = ϑᵖ(Ω₁·Ω₁·2)`**: at every point of every level `j < Ω₁` and at every `ε`-number between
(one application of `Gn.gnImg_of_eps`; below `Γ_{ρ+2}` it is `He.he_img_G1`). -/
theorem ywImg : ∀ v, v < ywX ρ → GnI ρ δ v := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  obtain ⟨hXT, -, hX1, -⟩ := ywX_facts hρE hρ1
  refine gnImg_of_eps h (fun v hv => ⟨vz_T_down hρE hρ1 hXT hX1 hv.le, hv.trans hX1⟩)
    (fun e he _ heX IHe => ?_)
  rcases lt_or_ge e (gq 1 ρ) with hlt | hge
  · exact he_img_G1 h e hlt
  have h1T : (1 : Ordinal.{0}) ∈ Tset ρ := (yw_one hρE hρ1).1
  have h1Ω : (1 : Ordinal.{0}) < Om1 := (yw_one hρE hρ1).2
  have hρG1 : ρ < gq 1 ρ := (geq_facts hρE hρ1 h1T h1Ω).2.1
  have hρe : ρ < e := hρG1.trans_le hge
  have he1 : e < Om1 := heX.trans hX1
  have heT : e ∈ Tset ρ := vz_T_down hρE hρ1 hXT hX1 heX.le
  obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hρE hρ1 heT hρe.le he1 (inE_indec he)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hρE hρ1 hξT hξ2).1 ⟨by rw [hξv]; exact hρe, by rw [hξv]; exact he⟩
  rcases lt_or_ge ξ (Om1 * Om1) with hξs | hξs
  · obtain ⟨hq1, hrT, hr1, hdec⟩ := lu_split hρE hρ1 hξT hξ2 hΩξ
    have hqT : ξ / Om1 ∈ Tset ρ := lgQuot_mem hρE hρ1 hξT hξs
    have hqΩ : ξ / Om1 < Om1 := (Ordinal.lt_mul_iff_div_lt (Ordinal.omega_pos 1).ne').1 hξs
    have hev : glA (ξ / Om1) (ξ % Om1) ρ = e := by
      show vt ρ (Om1 * (ξ / Om1) + ξ % Om1) = e
      rw [hdec, hξv]
    rw [← hev] at IHe heX ⊢
    exact ywI_veb h hq1 hqT hqΩ hrT hr1 heX IHe
  · have hξX := ywLt_X hρE hρ1 hξT hξ2 (by rw [hξv]; exact hρe) (by rw [hξv]; exact heX)
    obtain ⟨j, σ, hjT, hjΩ, hσT, hσΩ, hξe⟩ := ywDec hρE hρ1 hξT hξ2 hξs hξX
    have hev : ywV j σ ρ = e := by show vt ρ (Om1 * (Om1 * 1 + j) + σ) = e; rw [← hξe, hξv]
    have hG0 : gq 0 ρ < gq 1 ρ := gmq_lt hρE hρ1 h1T h1Ω zero_lt_one
    rw [← hev] at IHe hge ⊢
    exact ywI_atom h hjT hjΩ hσT hσΩ (hG0.trans_le hge) IHe

/-- **LEMMA IMG AT EVERY POINT OF EVERY LEVEL** (`j, σ ∈ Tᵖ ∩ Ω₁`): in particular at every fixed point of
`ν ↦ ϑᵖ(Ω₁·Ω₁ + ν)` (level `1`), for `j, σ < X^ρ`. -/
theorem ywImg_atom {j σ : Ordinal.{0}} (hjT : j ∈ Tset ρ) (hjΩ : j < Om1) (hσT : σ ∈ Tset ρ) (hσΩ : σ < Om1)
    (hjX : j < ywX ρ) (hσX : σ < ywX ρ) : GnI ρ δ (ywV j σ ρ) := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  obtain ⟨h1T, h1Ω⟩ := yw_one hρE hρ1
  have h0T : (0 : Ordinal.{0}) ∈ Tset ρ := mem_T_of_le hρE hρ1 zero_le
  have h0Ω : (0 : Ordinal.{0}) < Om1 := hρE.pos.trans hρ1
  have h2x : (2 : Ordinal.{0}) < ρ := by
    have := natCast_lt_omega0 2
    exact_mod_cast this.trans (omega0_lt_inE hρE)
  have h2T : (2 : Ordinal.{0}) ∈ Tset ρ := mem_T_of_le hρE hρ1 h2x.le
  have h12 : (1 : Ordinal.{0}) ≤ 2 := by norm_num
  obtain ⟨-, -, -, hxX, -, -, -, -, -, -⟩ := lq_facts hρE hρ1 h12 h2T (h2x.trans hρ1) h0T h0Ω h0T h0Ω
  refine ywImg h _ ?_
  have harg : Om1 * (Om1 * 1 + j) + σ < Om1 * (Om1 * 2 + 0) + 0 := by
    rw [add_zero, add_zero]
    calc Om1 * (Om1 * 1 + j) + σ < Om1 * (Om1 * 1 + j) + Om1 := (add_lt_add_iff_left _).2 hσΩ
      _ = Om1 * (Om1 * 1 + j + 1) := (mul_add_one _ _).symm
      _ ≤ Om1 * (Om1 * 1 + Om1) := by
          rw [add_assoc]
          exact mul_le_mul_right ((add_le_add_iff_left _).2 (Order.add_one_le_of_lt hjΩ)) _
      _ = Om1 * (Om1 * 2) := by
          rw [mul_one, show Om1 * (2 : Ordinal.{0}) = Om1 + Om1 by
            rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, mul_add, mul_one]]
  exact lqVt_lt hρE hρ1 h1T h1Ω hjT hjΩ hσT hσΩ h12 h2T (h2x.trans hρ1) h0T h0Ω h0T h0Ω harg
    ((lu_one_lt_E hρE).trans hxX) hjX hσX

/-- **LEMMA IMG (gated) FOR A SPECIFIED FUNCTION BELOW `X^ρ`.** -/
theorem ywPkg {g : Ordinal.{0}} {C : Finset Ordinal.{0}} {T : Ordinal.{0} → Ordinal.{0}} (hgρ : g < ρ)
    (hC : ∀ c ∈ C, c < ρ) (hT : T ρ < ywX ρ) (hex : GjEx g C T) : GhPkg g ρ δ T :=
  gnPkg_of_GnI h hgρ hC (ywImg h _ hT) hex

end Img

end Googology.Trans.PoR.InaccPsi.R2.Yw

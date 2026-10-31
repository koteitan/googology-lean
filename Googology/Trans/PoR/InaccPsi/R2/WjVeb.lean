import Googology.Trans.PoR.InaccPsi.R2.GlR8
import Googology.Trans.PoR.InaccPsi.R2.GlR6
import Googology.Trans.PoR.InaccPsi.R2.HgVD

/-!
# Wj: the level codes of regions (A2) and (A3) of the frontier, and their cofinality

`G = Γ(0) = Γ_{Ω₁+1}`, `Γ(1) = Γ_{Ω₁+2}`, `E = ε_{Ω₁+1}`.  The `G`-systems of the frontier have bounds
`B = φ(ℓ, G+1)` at levels `ℓ`.

* (A2) levels `E ≤ ℓ < G`: `sup_{ℓ<G} φ(ℓ, G+1) = φ(G, 1)` (`wjA2Cof`, along the cofinal codes `Gl.glBn n`),
  so these levels cover the bounds `B < φ(G, 1)` only; the old cut at `φ(G, G+1)` puts `[φ(G,1), φ(G,G+1))`
  in the wrong region.  The level code type is the `Gl` code type: reading `Gl.glR ℓ x` (`= rdc ℓ x` below
  `E`, `Gl.glR_low`), gate `Gl.glG ℓ`; EXACT (`wjReadExactG`, from `Gl.gl_pi`) and the digit gate
  (`wjDigitGateG`, from `Gl.gl_code_gate`) hold on all of `[0, G)`.
* (A3) levels `G < ℓ < Γ(1)`: the levels `t₀ = ε_{G+1}`, `t_{n+1} = φ(t_n, 0)` are cofinal in `Γ(1)`
  (`wjA3Cof`), so every `B < Γ(1)` (also every `B ∈ [φ(G,1), φ(G,G+1))`) is below `φ(t_n, G+1)`.  The level
  `G` itself is not needed.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gl

theorem wjG_fix : veblen (gcG 0) 0 = gcG 0 := by rw [Tf.tf_gcG]; exact veblen_gamma_zero _

theorem wjG1_fix : veblen (gcG 1) 0 = gcG 1 := by rw [Tf.tf_gcG]; exact veblen_gamma_zero _

theorem wjG_pos : 0 < gcG 0 := (gcG_SC 0).1

theorem wjGlBn_mono : Monotone glBn :=
  monotone_nat_of_le_succ fun n => by
    show glBn n ≤ veblen (glBn n) 0
    exact left_le_veblen _ _

/-- A value `φ(a, b)` with `a > 0` is an `ε`-number. -/
theorem wjVeb_inE {a b : Ordinal.{0}} (ha : 0 < a) : InE (veblen a b) := by
  have h := veblen_veblen_of_lt ha b
  rw [veblen_zero_apply] at h
  exact h

/-- `G + 1 < φ(G, 1)`. -/
theorem wjG1_lt_vG1 : gcG 0 + 1 < veblen (gcG 0) 1 := by
  have hE := wjVeb_inE (a := gcG 0) (b := 1) wjG_pos
  have hG : gcG 0 < veblen (gcG 0) 1 := by
    conv_lhs => rw [← wjG_fix]
    exact veblen_lt_veblen_iff_right.2 one_pos
  exact (inE_indec hE).add_lt hG (one_lt_omega0.trans (omega0_lt_inE hE))

/-- **(A2) bounds**: `φ(E, G+1) ≤ φ(glBn n, G+1) < φ(G, 1)`. -/
theorem wjA2_bounds (n : ℕ) :
    veblen Gf.gfE (gcG 0 + 1) ≤ veblen (glBn n) (gcG 0 + 1) ∧ veblen (glBn n) (gcG 0 + 1) < veblen (gcG 0) 1 := by
  obtain ⟨hlt, hE, -⟩ := glBn_spec n
  refine ⟨veblen_left_monotone _ hE.le, ?_⟩
  calc veblen (glBn n) (gcG 0 + 1) < veblen (glBn n) (veblen (gcG 0) 1) :=
        veblen_lt_veblen_iff_right.2 wjG1_lt_vG1
    _ = veblen (gcG 0) 1 := veblen_veblen_of_lt hlt 1

/-- **(A2) cofinality**: `φ(G, 1) = sup_n φ(glBn n, G+1)`; every `B < φ(G, 1)` is below some
`φ(glBn n, G+1)` (`E < glBn n < G`). -/
theorem wjA2Cof {B : Ordinal.{0}} (hB : B < veblen (gcG 0) 1) : ∃ n, B < veblen (glBn n) (gcG 0 + 1) := by
  by_contra hcon
  push Not at hcon
  set f : ℕ → Ordinal.{0} := fun n => veblen (glBn n) (gcG 0 + 1) with hf
  have hbdd : BddAbove (Set.range f) := ⟨B, by rintro _ ⟨k, rfl⟩; exact hcon k⟩
  set t := ⨆ n, f n with ht
  have htB : t ≤ B := Ordinal.iSup_le hcon
  have hfix : ∀ b < gcG 0, veblen b t = t := by
    intro b hb
    refine le_antisymm ?_ (right_le_veblen _ _)
    rw [(isNormal_veblen b).map_iSup hbdd]
    refine Ordinal.iSup_le fun n => ?_
    obtain ⟨m, hm⟩ := glBn_cof hb
    have h1 : veblen b (f n) ≤ veblen b (f (max n m)) :=
      veblen_le_veblen_iff_right.2 (veblen_left_monotone _ (wjGlBn_mono (le_max_left _ _)))
    have h2 : veblen b (f (max n m)) = f (max n m) :=
      veblen_veblen_of_lt (hm.trans_le (wjGlBn_mono (le_max_right _ _))) _
    exact (h1.trans h2.le).trans (Ordinal.le_iSup f _)
  obtain ⟨a, ha⟩ := (mem_range_veblen wjG_pos.ne').2 hfix
  rcases eq_or_ne a 0 with h0 | h0
  · rw [h0, wjG_fix] at ha
    have h1 : gcG 0 + 1 ≤ f 0 := right_le_veblen _ _
    have h2 : f 0 ≤ t := Ordinal.le_iSup f 0
    rw [← ha] at h2
    exact absurd (lt_add_one (gcG 0)) (not_lt.2 (h1.trans h2))
  · have h1 : veblen (gcG 0) 1 ≤ t := by
      rw [← ha]; exact veblen_le_veblen_iff_right.2 (Order.one_le_iff_ne_zero.2 h0)
    exact absurd (hB.trans_le (h1.trans htB)) (lt_irrefl B)

/-- **(A3) levels**: `t₀ = ε_{G+1} = φ(1, G+1)`, `t_{n+1} = φ(t_n, 0)`. -/
noncomputable def wjT : ℕ → Ordinal.{0}
  | 0 => veblen 1 (gcG 0 + 1)
  | n + 1 => veblen (wjT n) 0

theorem wjT_mono : Monotone wjT :=
  monotone_nat_of_le_succ fun n => by
    show wjT n ≤ veblen (wjT n) 0
    exact left_le_veblen _ _

theorem wjG_lt_G1 : gcG 0 < gcG 1 := gcG_lt_iff.2 one_pos

/-- `G + 1 < Γ(1)`. -/
theorem wjG1_lt : gcG 0 + 1 < gcG 1 := by
  have hE : InE (gcG 1) := Low.opow_eq_self_of_SC (gcG_SC 1)
  exact (inE_indec hE).add_lt wjG_lt_G1 (one_lt_omega0.trans (omega0_lt_inE hE))

/-- `φ(x, y) < Γ(1)` for `x, y < Γ(1)`. -/
theorem wjVeb_lt_G1 {x y : Ordinal.{0}} (hx : x < gcG 1) (hy : y < gcG 1) : veblen x y < gcG 1 :=
  (gcG_SC 1).2 x hx y hy

/-- **(A3) bounds**: `G < t_n < Γ(1)`, `t_n` an `ε`-number, `φ(t_n, G+1) < Γ(1)`. -/
theorem wjT_spec (n : ℕ) : gcG 0 < wjT n ∧ wjT n < gcG 1 ∧ InE (wjT n) ∧
    veblen (wjT n) (gcG 0 + 1) < gcG 1 := by
  have hlt : ∀ n, wjT n < gcG 1 := by
    intro n
    induction n with
    | zero =>
      exact wjVeb_lt_G1 (one_lt_omega0.trans (omega0_lt_inE (Low.opow_eq_self_of_SC (gcG_SC 1)))) wjG1_lt
    | succ n ih => exact wjVeb_lt_G1 ih (gcG_SC 1).1
  have hG : gcG 0 < wjT 0 := (lt_add_one _).trans_le (right_le_veblen _ _)
  have hpos : ∀ n, 0 < wjT n := fun n => wjG_pos.trans (hG.trans_le (wjT_mono (Nat.zero_le n)))
  refine ⟨hG.trans_le (wjT_mono (Nat.zero_le n)), hlt n, ?_, wjVeb_lt_G1 (hlt n) wjG1_lt⟩
  rcases n with _ | m
  · exact wjVeb_inE one_pos
  · exact wjVeb_inE (hpos m)

/-- **(A3) cofinality**: every `B < Γ(1)` is below some `φ(t_n, G+1)`. -/
theorem wjA3Cof {B : Ordinal.{0}} (hB : B < gcG 1) : ∃ n, B < veblen (wjT n) (gcG 0 + 1) := by
  by_contra hcon
  push Not at hcon
  have hle : ∀ n, wjT n ≤ B := fun n =>
    (wjT_mono (Nat.le_succ n)).trans ((veblen_le_veblen_iff_right.2 zero_le).trans (hcon n))
  have hbdd : BddAbove (Set.range wjT) := ⟨B, by rintro _ ⟨k, rfl⟩; exact hle k⟩
  set s := ⨆ n, wjT n with hs
  have hsB : s ≤ B := Ordinal.iSup_le hle
  have hfix : veblen s 0 = s := by
    refine le_antisymm ?_ (by simpa using left_le_veblen s 0)
    rw [(isNormal_veblen_zero).map_iSup hbdd]
    exact Ordinal.iSup_le fun n => Ordinal.le_iSup wjT (n + 1)
  obtain ⟨a, ha⟩ := mem_range_gamma.2 hfix
  have hGs : gcG 0 < s := (wjT_spec 0).1.trans_le (Ordinal.le_iSup wjT 0)
  rw [Tf.tf_gcG, ← ha] at hGs
  have h1 : Om1 + 1 + 0 + 1 ≤ a := Order.add_one_le_of_lt (gamma_lt_gamma.1 hGs)
  have h2 : gcG 1 ≤ s := by
    rw [Tf.tf_gcG, ← ha, add_zero] at *
    exact gamma_le_gamma.2 h1
  exact absurd (hB.trans_le (h2.trans hsB)) (lt_irrefl B)

/-- **(A2) EXACT** of the level reading `Gl.glR ℓ` above the gate `Gl.glG ℓ`, every `ℓ < G`. -/
theorem wjReadExactG : ∀ ℓ σ ρ, ℓ < gcG 0 → Bases σ ρ → glG ℓ < σ →
    glR ℓ ρ ∈ TB ρ σ ∧ pi σ ρ (glR ℓ ρ) = glR ℓ σ :=
  fun ℓ _ _ hℓ hB hg => gl_pi hB ℓ hℓ hg

/-- **(A2) digit gate**: a code `y < G` over a strongly critical `Z ≤ Ω₁` with the atom `G` has gate
`Gl.glG y < Z`. -/
theorem wjDigitGateG : ∀ Z, SC Z → Z ≤ Om 1 → ∀ y, Mx.GxCl Z {gcG 0} y → y < gcG 0 → glG y < Z := by
  intro Z hZ hZ1 y hy hyG
  obtain ⟨n, hn⟩ := glBn_cof hyG
  obtain ⟨hlt, hE, -⟩ := glBn_spec n
  have hZE : InE Z := Low.opow_eq_self_of_SC hZ
  exact gl_code_gate (B := glBn n) (Z := Z) (At := {gcG 0}) hlt.le (by rw [Br.Om1_eq]; exact hZ1) hZ.1
    (fun u v hu hv => (inE_indec hZE).add_lt hu hv) (fun u v hu hv => hZ.2 u hu v hv)
    (fun s hs => by rw [Set.mem_singleton_iff.1 hs]; exact hlt) hE.le hy hn

end Googology.Trans.PoR.InaccPsi.R2.Wj

import Googology.Trans.PoR.InaccPsi.R2.GkU9
import Googology.Trans.PoR.InaccPsi.R2.VzI
import Googology.Trans.PoR.InaccPsi.R2.VzB

/-!
# LEMMA IMG FOR A SPECIFIED FUNCTION BELOW `φ(ω, ρ+1)`, and the `R₁⁺`-reach of `φ(k, τ+c)` at every `c`

`RstK.imgVz` (`R2.VzI`) is Lemma IMG for every value below `VzB ρ = sup_N ϑᵖ(Ω₁·N) = φ(ω, ρ+1)` with a term of
`VzTm`, whose atoms `ϑˣ(Ω₁·k + t)` are the values of `φ(k, ·)` of fixed-point level exactly `k` (every level
`1 ≤ k < ω` at once: the `ε`-atoms `k = 1`, the `ζ`-atoms `k = 2`, …).  With Lemma EXACT for the terms (`vzv_pi`) the
argument of `Gk.gkPkg_of_ex` gives Lemma IMG for a SPECIFIED function `T` with Lemma EXACT and `T(ρ) < φ(ω, ρ+1)`:
the bound `ζ_{ρ+1} = evZ ρ` of round 82 is gone.

* `glPkg_of_ex` (**Lemma IMG (gated) for every function with Lemma EXACT and value below `VzB ρ`**), `glImgPkg_of_ex`
  (the ungated package), `glVz_pkg` (every term of `VzTm`), `gl_pkg_evZ` (the logend `ζ_{y+1}` of the code
  `ζ_{Ω₁+1}`), `gl_pkg_th` (every atom `y ↦ ϑʸ(Ω₁·k + t(y))`);
* `glZeta`, `gl_lh_th` (**the `R₁⁺`-reach of `ϑᵗ(Ω₁·k + c) = φ(k, ·)` at EVERY `c ∈ Tᵗ ∩ Ω₁`**:
  `lh = ϑᵗ(Ω₁·k+c)·(k+1) + ζ`, `ζ = logend(c)` when `c < ϑᵗ(Ω₁·k+σ)` for some `σ < c`, else `0`), `gl_lh_zeta`
  (`k = 2`: the reach of `ζ_{τ+1+c} = ϑᵗ(Ω₁·2 + c)`), `gl_vt_two` (`ϑᵗ(Ω₁·2) = ζ_{τ+1}`).

No new axiom.  New definition: `glZeta`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gl

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gd Googology.Trans.PoR.InaccPsi.R2.Gj Googology.Trans.PoR.InaccPsi.R2.Gk VzTm

theorem gl_wz_consts {ρ δ : Ordinal.{0}} {C : Finset Ordinal.{0}} (hC : ∀ c ∈ C, c < ρ) : WZ ρ δ ∅ C :=
  ⟨by simp, hC, by simp⟩

section Pkg

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **LEMMA IMG FOR A SPECIFIED FUNCTION (gated), below `φ(ω, ρ+1)`**: if `T` has Lemma EXACT above the gate
`g < ρ` with constants `C < ρ`, and `T ρ < VzB ρ`, then every covering copy `f` that keeps `g` has
`T(f ρ) ≤ f(T ρ)`. -/
theorem glPkg_of_ex {g : Ordinal.{0}} {C : Finset Ordinal.{0}} {T : Ordinal.{0} → Ordinal.{0}} (hgρ : g < ρ)
    (hC : ∀ c ∈ C, c < ρ) (hT : T ρ < VzB ρ) (hex : GjEx g C T) : GhPkg g ρ δ T := by
  classical
  obtain ⟨⟨W, Z, s, w, cb, cs', e, m, b⟩, -⟩ := h.imgVz (T ρ) hT
  have w' := w.union (gl_wz_consts (δ := δ) hC)
  rw [Finset.union_empty] at w'
  refine ⟨W, Z ∪ C, w', ?_, fun A f hW hZ Cx => ?_⟩
  · rcases Finset.mem_union.1 m with hm | hm
    · exact Finset.mem_union_left _ hm
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ hm)
  have hZ' : ↑Z ⊆ A := gk_sub (fun x hx => by simp [hx]) hZ
  have hCA : ∀ c ∈ C, c ∈ A := fun c hc => hZ (by simp [hc])
  have I := Cx.toImgCtx
  have hσU : UpsPt (f ρ) := I.ups
  have hB : Bases (f ρ) ρ := h.img_bases I
  have hCσ : ∀ c ∈ C, c < f ρ := fun c hc => I.above c (hCA c hc) (hC c hc)
  have hs : CBt s (f ρ) := cbt_img I cb (fun c hc => hZ' (Finset.mem_coe.2 (cs' c hc)))
  obtain ⟨-, hps⟩ := vzv_pi hσU h.ρU hB s hs
  obtain ⟨-, hpT⟩ := hex (f ρ) ρ hσU h.ρU hB (Cx.lt hgρ) hCσ
  have hTs : T (f ρ) = val s (f ρ) := by rw [← hpT, ← e, hps]
  rw [hTs]
  exact b A f hW hZ' I

/-- **LEMMA IMG FOR A SPECIFIED FUNCTION (ungated package)**: `1 ≤ T ρ < VzB ρ` and Lemma EXACT at every `υ`-point
pair with the constants below the smaller base give `ImgPkg ρ δ T`. -/
theorem glImgPkg_of_ex {C : Finset Ordinal.{0}} {T : Ordinal.{0} → Ordinal.{0}} (hC : ∀ c ∈ C, c < ρ)
    (h1 : 1 ≤ T ρ) (hT : T ρ < VzB ρ)
    (hex : ∀ σ, UpsPt σ → Bases σ ρ → (∀ c ∈ C, c < σ) → T ρ ∈ TB ρ σ ∧ pi σ ρ (T ρ) = T σ) :
    ImgPkg ρ δ T := by
  classical
  obtain ⟨⟨W, Z, s, w, cb, cs', e, m, b⟩, -⟩ := h.imgVz (T ρ) hT
  have w' := w.union (gl_wz_consts (δ := δ) hC)
  rw [Finset.union_empty] at w'
  refine ⟨h1, hT.trans h.vz_B_lt_δ, W, Z ∪ C, w', ?_, fun A f hW hZ I => ?_⟩
  · rcases Finset.mem_union.1 m with hm | hm
    · exact Finset.mem_union_left _ hm
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ hm)
  have hZ' : ↑Z ⊆ A := gk_sub (fun x hx => by simp [hx]) hZ
  have hCA : ∀ c ∈ C, c ∈ A := fun c hc => hZ (by simp [hc])
  have hσU : UpsPt (f ρ) := I.ups
  have hB : Bases (f ρ) ρ := h.img_bases I
  have hCσ : ∀ c ∈ C, c < f ρ := fun c hc => I.above c (hCA c hc) (hC c hc)
  have hs : CBt s (f ρ) := cbt_img I cb (fun c hc => hZ' (Finset.mem_coe.2 (cs' c hc)))
  obtain ⟨-, hps⟩ := vzv_pi hσU h.ρU hB s hs
  obtain ⟨-, hpT⟩ := hex (f ρ) hσU hB hCσ
  have hTs : T (f ρ) = val s (f ρ) := by rw [← hpT, ← e, hps]
  rw [hTs]
  exact b A f hW hZ' I

/-- **Lemma IMG (gated) for every term of `VzTm`** (constants below `ρ`). -/
theorem glVz_pkg {g : Ordinal.{0}} (s : VzTm) (hgρ : g < ρ) (hs : CBt s ρ) : GhPkg g ρ δ (val s) := by
  classical
  refine glPkg_of_ex h (C := (cst' s).toFinset) hgρ (fun c hc => cbt_cst s ρ hs c (List.mem_toFinset.1 hc))
    (vzv_lt_B h.ρE h.ρ1 hs) (fun σ ρ' hσ hρ' hB _ hC => vzv_pi hσ hρ' hB s ?_)
  exact cbt_iff s ρ σ hs (fun c hc => hC c (List.mem_toFinset.2 hc))

/-- **The logend `ζ_{y+1}` of the code `ζ_{Ω₁+1}`**: Lemma IMG for `evZ` above every gate (`ϑʸ(Ω₁·2) = ζ_{y+1}`). -/
theorem gl_pkg_evZ {g : Ordinal.{0}} (hgρ : g < ρ) : GhPkg g ρ δ evZ := GhPkg.of_img h.vzPkgZ

/-- **Every atom `y ↦ ϑʸ(Ω₁·k + t(y))`** (a term `t` of `VzTm`, `1 ≤ k`): Lemma IMG above every gate. -/
theorem gl_pkg_th {g : Ordinal.{0}} {k : ℕ} (hk : 1 ≤ k) (t : VzTm) (hgρ : g < ρ) (ht : CBt t ρ) :
    GhPkg g ρ δ (fun y => vt y (Om1 * (k : Ordinal.{0}) + val t y)) :=
  glVz_pkg h (th k t) hgρ ⟨hk, ht⟩

end Pkg

/-! ## The `R₁⁺`-reach of `φ(k, τ+c)` at every `c` -/

/-- The last summand of the reach of `ϑᵗ(Ω₁·k + c)`: `logend(c)` if `c < ϑᵗ(Ω₁·k + σ)` for some `σ < c`, else `0`. -/
noncomputable def glZeta (τ : Ordinal.{0}) (k : ℕ) (c : Ordinal.{0}) : Ordinal.{0} := by
  classical
  exact if c ≠ 0 ∧ ∃ σ, σ < c ∧ c < vt τ (Om1 * (k : Ordinal.{0}) + σ) then lg c else 0

/-- **THE `R₁⁺`-REACH OF `φ(k, τ+c)` AT EVERY `c`** (`1 ≤ k < ω`, `c ∈ Tᵗ ∩ Ω₁`; `ϑᵗ(Ω₁·k + c)` is the `c`-th ordinal
of `(τ, Ω₁)` of fixed-point level exactly `k`): `lh = ϑᵗ(Ω₁·k + c)·(k + 1) + glZeta τ k c`. -/
theorem gl_lh_th {τ c : Ordinal.{0}} {k : ℕ} (hτ : InE τ) (hτ1 : τ < Om1) (hk : 1 ≤ k) (hc : c ∈ Tset τ)
    (hc1 : c < Om1) :
    IsLh1 (vt τ (Om1 * (k : Ordinal.{0}) + c))
      (vt τ (Om1 * (k : Ordinal.{0}) + c) * ((k + 1 : ℕ) : Ordinal.{0}) + glZeta τ k c) := by
  classical
  unfold glZeta
  split_ifs with hcase
  · exact vz_lh_th_lim hτ hτ1 hk hc hc1 hcase.1 hcase.2
  · rw [add_zero]
    refine vz_lh_th_fix hτ hτ1 hk hc hc1 (fun σ hσ => ?_)
    by_contra hlt
    push Not at hlt
    exact hcase ⟨(lt_of_le_of_lt zero_le hσ).ne', σ, hσ, hlt⟩

/-- `ϑᵗ(Ω₁·2) = ζ_{τ+1}` (the least `ε`-fixed point above `τ`). -/
theorem gl_vt_two {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) :
    vt τ (Om1 * ((2 : ℕ) : Ordinal.{0}) + 0) = evZ τ := by
  rw [vz_two_cast]; exact vz_vt_two_eq hτ hτ1

/-- **The `R₁⁺`-reach of the `ζ`-numbers `ϑᵗ(Ω₁·2 + c)` at every `c ∈ Tᵗ ∩ Ω₁`** (round 82 had only `c = 0`):
`lh = ϑᵗ(Ω₁·2 + c)·3 + glZeta τ 2 c`. -/
theorem gl_lh_zeta {τ c : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hc : c ∈ Tset τ) (hc1 : c < Om1) :
    IsLh1 (vt τ (Om1 * ((2 : ℕ) : Ordinal.{0}) + c))
      (vt τ (Om1 * ((2 : ℕ) : Ordinal.{0}) + c) * ((2 + 1 : ℕ) : Ordinal.{0}) + glZeta τ 2 c) :=
  gl_lh_th hτ hτ1 (by norm_num) hc hc1

end Googology.Trans.PoR.InaccPsi.R2.Gl

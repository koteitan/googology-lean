import Googology.Trans.PoR.InaccPsi.R2.CitedVd

set_option autoImplicit false

/-!
# The citation of Wilken 2007 for every level `Ω₁ ≤ M < B₂` (`B₂ = ψ_{Ω₂}(ε_{Ω₂+1})`): now THEOREMS

The eight facts below were axioms; they are now the instances `M < B₂`, `z < B₂` of the generic citation
`R2.CitedVd` (every level `Ω₁ ≤ M < θ`, `θ = ψ_{Ω₂}(Ω_ω)`), with the same names and the same statements.  Below `B₂`
the readings of `R2.CitedVd` are those of this file (`Uc.ucDat`, `Uc.ucParts`, `Uc.ucRebuild`), so each theorem is the
first branch of the corresponding axiom of `R2.CitedVd`.  The texts of [W07a] and the own steps (◇C, ◇H, ◇Φ₂, ◇K″,
◇I″, ◇V″, ◇Δ″, ◇F″, ◇π″) for the codes below `B₂` are now in the docstring of `R2.CitedVd`, which keeps them and adds
the steps for `[B₂, θ)`.

No axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Googology.Trans.PoR.InaccPsi.R2.Vd

/-- **[W07a] Def 3.22, Theorem 3.23, Lemma 3.30** (the instance `M < B₂` of `R2.vdArg_mem`): for a level `Ω₁ ≤ M <
B₂` with `ucDat M ∈ Tᵗ` and `η ∈ Tᵗ ∩ Ω₁`: `Ω₁·M + η ∈ Tᵗ`. -/
theorem ucArg_mem {τ M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : Om1 ≤ M) (hMB : M < Uc.ucB)
    (hMT : Uc.ucDat M ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1) : Om1 * M + η ∈ Tset τ :=
  vdArg_mem hτ hτ1 hM1 (vdDatIn_uc hMB hMT) hη hηΩ

/-- **[W07a] Def 3.22, Theorem 3.23, Lemma 3.30** (the instance `M < B₂` of `R2.vdArg_dat`): for a level `Ω₁ ≤ M <
B₂` and `η < Ω₁` with `Ω₁·M + η ∈ Tᵗ`: `ucDat M ∈ Tᵗ`. -/
theorem ucArg_dat {τ M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : Om1 ≤ M) (hMB : M < Uc.ucB)
    (hηΩ : η < Om1) (h : Om1 * M + η ∈ Tset τ) : Uc.ucDat M ∈ Tset τ :=
  (vdArg_dat hτ hτ1 hM1 hηΩ h).1 hMB

/-- **[W07a] Lemma 3.30, `⇐`** (the instance `M < B₂` of `R2.vdVt_lt`). -/
theorem ucVt_lt {τ M' η' M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : Om1 ≤ M) (hMB : M < Uc.ucB)
    (hM' : M' ≤ M) (hM'T : Uc.ucDat M' ∈ Tset τ) (hη' : η' ∈ Tset τ) (hη'Ω : η' < Om1)
    (hMT : Uc.ucDat M ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (harg : Om1 * M' + η' < Om1 * M + η) (hd' : Uc.ucDat M' < vt τ (Om1 * M + η))
    (hη'v : η' < vt τ (Om1 * M + η)) : vt τ (Om1 * M' + η') < vt τ (Om1 * M + η) :=
  vdVt_lt hτ hτ1 hM1 hM' (vdDatIn_uc (hM'.trans_lt hMB) hM'T) hη' hη'Ω (vdDatIn_uc hMB hMT) hη hηΩ harg
    (vdLtIn_uc (hM'.trans_lt hMB) hd') hη'v

/-- **[W07a] Lemma 3.30, `⇒`** (the instance `M < B₂` of `R2.vdLt_of_vt_lt`). -/
theorem ucLt_of_vt_lt {τ ξ M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : Om1 ≤ M) (hMB : M < Uc.ucB)
    (hξ : ξ ∈ Tset τ) (hξ2 : ξ < OmTwo) (hMT : Uc.ucDat M ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (hdξ : Uc.ucDat M < vt τ ξ) (hηξ : η < vt τ ξ) (h : vt τ ξ < vt τ (Om1 * M + η)) : ξ < Om1 * M + η :=
  vdLt_of_vt_lt hτ hτ1 hM1 hξ hξ2 (vdDatIn_uc hMB hMT) hη hηΩ (vdLtIn_uc hMB hdξ) hηξ h

/-- **[W07a] Lemma 3.30 (`α^* < ϑ₀(α)`), Lemma 4.3** (the instance `M < B₂` of `R2.vdLevel_lt`). -/
theorem ucLevel_lt {τ M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : Om1 ≤ M) (hMB : M < Uc.ucB)
    (hMT : Uc.ucDat M ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    Uc.ucDat M < vt τ (Om1 * M + η) ∧ η < vt τ (Om1 * M + η) :=
  have h := vdLevel_lt hτ hτ1 hM1 (vdDatIn_uc hMB hMT) hη hηΩ
  ⟨h.1.1 hMB, h.2⟩

/-- **[W07a] Def 5.1, Lemma 5.3 (b)–(d)** (the instance `z < B₂` of `R2.vdAtom_TB`): an atom `z ∈ (Ω₁, B₂)` is in
`Tᵗ[σ]` iff its parts are, and then `π_{σ,τ}(z)` is `z` rebuilt from the images of its parts. -/
theorem ucAtom_TB {σ τ z : Ordinal.{0}} (h : Bases σ τ) (hSC : Googology.Notation.InaccPsi.SC z) (h1 : Om1 < z)
    (hB : z < Uc.ucB) :
    (z ∈ TB τ σ ↔ ∀ x ∈ Uc.ucParts z, x ∈ TB τ σ) ∧
      ((∀ x ∈ Uc.ucParts z, x ∈ TB τ σ) → pi σ τ z = Uc.ucRebuild (pi σ τ) z) :=
  (vdAtom_TB h hSC h1).1 hB

/-- **[W07a] Def 5.1, Lemma 5.3 (b)–(d)** (the instance below `B₂` of `R2.vdPhi_TB`). -/
theorem ucPhi_TB {σ τ a c : Ordinal.{0}} (h : Bases σ τ) (ha : 1 ≤ a) (haz : a < veblen a c)
    (hcz : c < veblen a c) (h1 : Om1 < veblen a c) (hB : veblen a c < Uc.ucB) :
    (veblen a c ∈ TB τ σ ↔ a ∈ TB τ σ ∧ c ∈ TB τ σ) ∧
      (a ∈ TB τ σ → c ∈ TB τ σ → pi σ τ (veblen a c) = veblen (pi σ τ a) (pi σ τ c)) :=
  vdPhi_TB h ha haz hcz h1 (Or.inl hB)

/-- **[W07a] Def 5.1, Lemma 5.3 (b)–(d)** (the instance below `B₂` of `R2.vdOpow_TB`). -/
theorem ucOpow_TB {σ τ g : Ordinal.{0}} (h : Bases σ τ) (hg : Gg.ggE ≤ g) (hgE : ω ^ g ≠ g)
    (hB : ω ^ g < Uc.ucB) :
    (ω ^ g ∈ TB τ σ ↔ g ∈ TB τ σ) ∧ (g ∈ TB τ σ → pi σ τ (ω ^ g) = ω ^ pi σ τ g) :=
  vdOpow_TB h hg hgE (Or.inl hB)

end Googology.Trans.PoR.InaccPsi.R2

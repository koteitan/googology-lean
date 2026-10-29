import Googology.Trans.PoR.InaccPsi.R2.VsDict
import Googology.Trans.PoR.InaccPsi.R2.CitedVp

/-!
# The base change on the three forms of `D(s)`, as one package for `s = 1` (on `[B₂, θ)`) and for every `s ≥ 2`

`Hˡ⁽ˢ⁾_γ = Ul.ulH S s γ`, `π = pi σ τ`, `θ_s = ψ_{Ω_{s+1}}(Ω_ω)`, `B₂ = Uc.ucB`, `E₁ = Gg.ggE = ε_{Ω₁+1}`.

* `VsPkg S s L U G` (**the base-change facts on `[L, U)` at the cardinal `Ω_{s+1}`**: atoms `Hˡ⁽ˢ⁾_γ(y)`, `ε`-numbers
  `φ(a, c)` in normal form, `ω^g` with `g ≥ G` not an `ε`-number), `vsPkg_one` (**`s = 1`, `[B₂, θ)`, `G = E₁`**:
  `Vd.vdCitPi`, i.e. `R2.CitedVd`), `vsPkg_gen` (**every finite `s ≥ 2`, `[Ω_s, θ_s)`, `G = Ω_s`**: `R2.CitedVp`);
* `vs_pi_lt_Om`, `vs_pi_ge_Om` (**`π` maps `Tᵗ[σ] ∩ [Ω_k, Ω_{k+1})` into `[Ω_k, Ω_{k+1})`** for every finite `k ≥ 1`:
  from `R2.vsOm_TB` (`π Ω_j = Ω_j`, `j ≥ 2`), `R2.pi_Om1` and `R2.pi_bijOn` (Lemma 5.3 (b)); the fact [W07a] states
  only inside a proof is derived, not cited).

No new axiom.  New definition: `VsPkg` (a Prop structure).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vs

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul

variable {S : InaccSeq.{0}} {s : Ordinal.{0}}

/-- **The base-change facts on `[L, U)` at the cardinal `Ω_{s+1}`.** -/
structure VsPkg (S : InaccSeq.{0}) (s L U G : Ordinal.{0}) : Prop where
  atom : ∀ {σ τ γ y : Ordinal.{0}}, Bases σ τ → γ < Om (s + 1 + 1) → y < ulH S s γ y → L ≤ ulH S s γ y →
    ulH S s γ y < U → (ulH S s γ y ∈ TB τ σ ↔ γ ∈ TB τ σ ∧ y ∈ TB τ σ) ∧
      (γ ∈ TB τ σ → y ∈ TB τ σ → pi σ τ (ulH S s γ y) = ulH S s (pi σ τ γ) (pi σ τ y))
  eps : ∀ {σ τ a c : Ordinal.{0}}, Bases σ τ → 1 ≤ a → a < veblen a c → c < veblen a c → L ≤ veblen a c →
    veblen a c < U → (veblen a c ∈ TB τ σ ↔ a ∈ TB τ σ ∧ c ∈ TB τ σ) ∧
      (a ∈ TB τ σ → c ∈ TB τ σ → pi σ τ (veblen a c) = veblen (pi σ τ a) (pi σ τ c))
  opow : ∀ {σ τ g : Ordinal.{0}}, Bases σ τ → G ≤ g → ω ^ g ≠ g → ω ^ g < U →
    (ω ^ g ∈ TB τ σ ↔ g ∈ TB τ σ) ∧ (g ∈ TB τ σ → pi σ τ (ω ^ g) = ω ^ pi σ τ g)

/-- **`s = 1` on `[B₂, θ)`** (`Vd.vdCitPi`). -/
theorem vsPkg_one : VsPkg S 1 Uc.ucB (ConjT.th S) Gg.ggE where
  atom hB hγ hy hL hU := Vd.vdCitPi.atom hB hγ hy hL hU
  eps hB h1 h2 h3 hL hU := Vd.vdCitPi.eps hB h1 h2 h3 (Uc.ucB_gt.trans_le hL) hU
  opow hB hg hgE hU := Vd.vdCitPi.opow hB hg hgE hU

/-- **Every finite `s ≥ 2` on `[Ω_s, θ_s)`** (`R2.CitedVp`). -/
theorem vsPkg_gen (hs : s < ω) (hs1 : 1 < s) :
    VsPkg S s (Om s) (S.psi (Om ω) (Om (s + 1))) (Om s) where
  atom hB hγ hy _ hU := vsAtom_TB hB hs hs1 hγ hy hU
  eps {σ τ a c} hB h1 h2 h3 hL hU := by
    have hSC : SC (Om s : Ordinal.{0}) := SC_Om (lt_of_lt_of_le zero_lt_one hs1.le).ne'
    have hlt : Om s < veblen a c := by
      refine lt_of_le_of_ne hL fun e => ?_
      have := hSC.2 a (e ▸ h2) c (e ▸ h3)
      rw [← e] at this
      exact lt_irrefl _ this
    exact vsPhi_TB hB hs hs1 h1 h2 h3 hlt hU
  opow hB hg hgE hU := vsOpow_TB hB hs hs1 hg hgE hU

/-- **`π` keeps `x < Ω_{k+1}`** on `Tᵗ[σ]` (`k ≥ 1` finite). -/
theorem vs_pi_lt_Om {σ τ k x : Ordinal.{0}} (h : Bases σ τ) (hk : k < ω) (hk1 : 1 ≤ k) (hx : x ∈ TB τ σ)
    (hxk : x < Om (k + 1)) : pi σ τ x < Om (k + 1) := by
  obtain ⟨hT, hπ⟩ := vsOm_TB h (Ui.ui_s1_lt_omega hk) (lt_of_le_of_lt hk1 (lt_add_one k))
  have := (pi_bijOn h).2 hx hT hxk
  rwa [hπ] at this

/-- **`π` keeps `Ω_k ≤ x`** on `Tᵗ[σ]` (`k ≥ 1` finite). -/
theorem vs_pi_ge_Om {σ τ k x : Ordinal.{0}} (h : Bases σ τ) (hk : k < ω) (hk1 : 1 ≤ k) (hx : x ∈ TB τ σ)
    (hxk : Om k ≤ x) : Om k ≤ pi σ τ x := by
  have hfix : Om k ∈ TB τ σ ∧ pi σ τ (Om k) = Om k := by
    rcases hk1.lt_or_eq with h1 | h1
    · exact vsOm_TB h hk h1
    · rw [← h1, ← Rj.rj_Om1]; exact pi_Om1 h
  rcases hxk.lt_or_eq with hlt | heq
  · have := (pi_bijOn h).2 hfix.1 hx hlt
    rw [hfix.2] at this
    exact this.le
  · rw [← heq, hfix.2]

end Googology.Trans.PoR.InaccPsi.R2.Vs

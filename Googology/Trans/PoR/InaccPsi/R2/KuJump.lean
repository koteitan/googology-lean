import Googology.Trans.PoR.InaccPsi.R2.KuDom

/-!
# Ku: THE JUMP AT ANY CONTEXT FROM ONE CLOSURE CONDITION

`Θ`, `T`, `D`, `A` as in `Ks.ksLow`; `Z = Θ(ψ₂ b)`, `α_b = A + 1 + ψ₂(T b)`.  A context `v ↦ G(v)` at the codes `v`
with the image `T(G v) = L(Θ v)`: if `L` has the gap toward `T b` at `HCl(α_b, Z)` (`Kt.KtGapY`, e.g. `Kt.ktG_KaT`,
`Ku.kuG_phiLS`), and from some code `v₀` on the values `G v` lie in `D` with `ψ₂(G v) < ψ₂ b`, the law, and strictly
increasing `ψ₂(T(G v))`, then the law holds at `b`.  No plateau iteration (`Bt.psi_le_of_key` through `Ks.ksLow`,
`Ku.kuDom`).

* `kuZ_lt` (`Θ(ψ₂ b) < Ω₁`), `kuJump` (**THE JUMP AT ANY CONTEXT**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ku

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Zy
  Googology.Trans.PoR.InaccPsi.R2.Kt Googology.Trans.PoR.InaccPsi.R2.Ks

variable {S : InaccSeq.{0}}

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hl hX hA hρ

/-- `Θ(ψ₂ b) < Ω₁` for `b ∈ D`. -/
theorem kuZ_lt {b : Ordinal.{0}} (hbD : VbD S l b) : gxTh (upsilon l) (ldAtR S l) (S.psi b (Om (1 + 1))) < Om 1 :=
  (Xd.xdUp_at hl hX hA hρ b hbD).trans_lt (psi_lt Low.InR_Om_one _)

/-- **THE JUMP AT ANY CONTEXT.** -/
theorem kuJump {b : Ordinal.{0}} (hbD : VbD S l b) (G L : Ordinal.{0} → Ordinal.{0}) (hLm : Monotone L)
    (hgap : KtGapY (vbT S l b) L
      {x | HCl S (A + 1 + S.psi (vbT S l b) (Om (1 + 1))) (gxTh (upsilon l) (ldAtR S l) (S.psi b (Om (1 + 1)))) x}
      (gxTh (upsilon l) (ldAtR S l) (S.psi b (Om (1 + 1)))))
    (v₀ : Ordinal.{0}) (hv₀c : GxCl (upsilon l) (ldAtR S l) v₀) (hv₀ : v₀ < S.psi b (Om (1 + 1)))
    (hgood : ∀ v, GxCl (upsilon l) (ldAtR S l) v → v₀ ≤ v → v < S.psi b (Om (1 + 1)) →
      VbD S l (G v) ∧ S.psi (G v) (Om (1 + 1)) < S.psi b (Om (1 + 1)) ∧
        vbT S l (G v) = L (gxTh (upsilon l) (ldAtR S l) v) ∧
        gxTh (upsilon l) (ldAtR S l) (S.psi (G v) (Om (1 + 1))) =
          S.psi (A + 1 + S.psi (vbT S l (G v)) (Om (1 + 1))) (Om 1))
    (hinc : ∀ v v', GxCl (upsilon l) (ldAtR S l) v → GxCl (upsilon l) (ldAtR S l) v' → v₀ ≤ v → v < v' →
      v' < S.psi b (Om (1 + 1)) → S.psi (vbT S l (G v)) (Om (1 + 1)) < S.psi (vbT S l (G v')) (Om (1 + 1))) :
    gxTh (upsilon l) (ldAtR S l) (S.psi b (Om (1 + 1))) =
      S.psi (A + 1 + S.psi (vbT S l b) (Om (1 + 1))) (Om 1) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hZρ, hZρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  set Z := gxTh (upsilon l) (ldAtR S l) (S.psi b (Om (1 + 1))) with hZdef
  set P := S.psi (vbT S l b) (Om (1 + 1)) with hPdef
  have hZ : SC Z := gxTh_SC hZρ hAt (SC_psi hκ2 _) (hZρ1.trans (psiS_bounds (S := S) _ 1).1)
  have hZ1 : Z < Om 1 := kuZ_lt hl hX hA hρ hbD
  have hbSC : SC (S.psi b (Om (1 + 1))) := SC_psi hκ2 _
  have h1c : GxCl (upsilon l) (ldAtR S l) 1 := GxCl.small (gg_one_lt_of_SC hZρ)
  set 𝒴 : Set Ordinal.{0} := {y | ∃ v, GxCl (upsilon l) (ldAtR S l) v ∧ v₀ ≤ v ∧ v < S.psi b (Om (1 + 1)) ∧
    y = S.psi (vbT S l (G v)) (Om (1 + 1))} with h𝒴
  have hne : ∃ y, y ∈ 𝒴 := ⟨_, v₀, hv₀c, le_rfl, hv₀, rfl⟩
  have hSC : ∀ y ∈ 𝒴, SC y ∧ Om 1 < y := by
    rintro y ⟨v, -, -, -, rfl⟩
    exact ⟨SC_psi hκ2 _, (psiS_bounds (S := S) _ 1).1⟩
  have hdir : ∀ y₁ ∈ 𝒴, ∀ y₂ ∈ 𝒴, ∃ y ∈ 𝒴, y₁ ≤ y ∧ y₂ ≤ y := by
    rintro y₁ ⟨v₁, h1c', h10, h1b, rfl⟩ y₂ ⟨v₂, h2c, h20, h2b, rfl⟩
    rcases le_total v₁ v₂ with h | h
    · refine ⟨_, ⟨v₂, h2c, h20, h2b, rfl⟩, ?_, le_rfl⟩
      rcases eq_or_lt_of_le h with e | hlt
      · rw [e]
      · exact (hinc v₁ v₂ h1c' h2c h10 hlt h2b).le
    · refine ⟨_, ⟨v₁, h1c', h10, h1b, rfl⟩, le_rfl, ?_⟩
      rcases eq_or_lt_of_le h with e | hlt
      · rw [e]
      · exact (hinc v₂ v₁ h2c h1c' h20 hlt h1b).le
  have hsub : ∀ e, HCl S (A + 1 + P) Z e → e < A + 1 + P → S.psi e (Om (1 + 1)) < P →
      ∃ y ∈ 𝒴, S.psi e (Om (1 + 1)) < y := by
    intro e he _ hψe
    have heT : e < vbT S l b := by
      by_contra h
      push Not at h
      exact absurd hψe (not_lt.2 (psi_mono hκ2 h).1)
    obtain ⟨q, hq, heq⟩ := hgap e he heT
    have hq1 : q + 1 < Z := hZ.isSuccLimit.add_one_lt hq
    obtain ⟨c, hcc, hcb, hcq⟩ := gxTh_onto hq1
    set v := max v₀ c with hvdef
    have hvc : GxCl (upsilon l) (ldAtR S l) v := zy_max_code hv₀c hcc
    have hvb : v < S.psi b (Om (1 + 1)) := max_lt hv₀ hcb
    have hv1b : v + 1 < S.psi b (Om (1 + 1)) := hbSC.isSuccLimit.add_one_lt hvb
    have hv1c : GxCl (upsilon l) (ldAtR S l) (v + 1) := GxCl.add hvc h1c
    obtain ⟨-, -, hTv, -⟩ := hgood v hvc (le_max_left _ _) hvb
    refine ⟨_, ⟨v + 1, hv1c, (le_max_left _ _).trans (le_of_lt (lt_add_one v)), hv1b, rfl⟩, ?_⟩
    calc S.psi e (Om (1 + 1)) ≤ S.psi (L (q + 1)) (Om (1 + 1)) := (psi_mono hκ2 heq.le).1
      _ ≤ S.psi (L (gxTh (upsilon l) (ldAtR S l) v)) (Om (1 + 1)) := by
          refine (psi_mono hκ2 (hLm ?_)).1
          rw [← hcq]; exact gxTh_mono (le_max_right _ _)
      _ = S.psi (vbT S l (G v)) (Om (1 + 1)) := by rw [hTv]
      _ < S.psi (vbT S l (G (v + 1))) (Om (1 + 1)) :=
          hinc v (v + 1) hvc hv1c (le_max_left _ _) (lt_add_one v) hv1b
  refine ksLow hl hX hA hρ hbD fun ξ hξ hξP => ?_
  obtain ⟨y, ⟨v, hvc, hv0, hvb, rfl⟩, hξy⟩ :=
    kuDom (S := S) (M := A + 1 + P) (Z := Z) (P := P) (𝒴 := 𝒴) hZ1 (psi_lt hκ2 _).le hne hSC hdir hsub ξ hξ hξP
  obtain ⟨hD, hψ, -, hlaw⟩ := hgood v hvc hv0 hvb
  exact ⟨G v, hD, hψ, hξy.le, hlaw⟩

end Main

end Googology.Trans.PoR.InaccPsi.R2.Ku

#print axioms Googology.Trans.PoR.InaccPsi.R2.Ku.kuJump

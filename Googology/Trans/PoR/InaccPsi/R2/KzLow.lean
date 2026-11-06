import Googology.Trans.PoR.InaccPsi.R2.KzUp

/-!
# Kz: THE TOP LAW FROM ONE CLOSURE CONDITION BELOW A BOUND `K` (`Ks.ksLow` on `D_K`)

* `kzAt`, `kzLow` (**`Ks.ksLow` on `D_K`** for `b < A`; the difference `ξ = e − A` lies in the hull by `Kt.ktHCl_sub`,
  so no bound `ψ₂(T b) < θ` is needed).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kz

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Rx

variable {S : InaccSeq.{0}}

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) {K : Ordinal.{0}} (hKB : KzB S K)
  {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hl hX hKB hA hρ

omit hKB in
/-- `ψ₂ a` is an atom of the hull for every `a ∈ D_K` below `A`. -/
theorem kzAt {a : Ordinal.{0}} (haD : VbDK S l K a) (haA : a < A) : S.psi a (Om (1 + 1)) ∈ ldAtR S l := by
  obtain ⟨-, rfl⟩ := Wg.wgOwnEta hl hX hA hρ
  exact ⟨a, haD.1, haA, rfl⟩

/-- **THE TOP LAW FROM ONE CLOSURE CONDITION.** -/
theorem kzLow {b : Ordinal.{0}} (hbD : VbDK S l K b) (hbA : b < A)
    (hfam : ∀ ξ, HCl S (A + 1 + S.psi (vbTK S l K b) (Om (1 + 1)))
        (gxTh (upsilon l) (ldAtR S l) (S.psi b (Om (1 + 1)))) ξ → ξ < S.psi (vbTK S l K b) (Om (1 + 1)) →
      ∃ a, VbDK S l K a ∧ S.psi a (Om (1 + 1)) < S.psi b (Om (1 + 1)) ∧ ξ ≤ S.psi (vbTK S l K a) (Om (1 + 1)) ∧
        gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1))) =
          S.psi (A + 1 + S.psi (vbTK S l K a) (Om (1 + 1))) (Om 1)) :
    gxTh (upsilon l) (ldAtR S l) (S.psi b (Om (1 + 1))) =
      S.psi (A + 1 + S.psi (vbTK S l K b) (Om (1 + 1))) (Om 1) := by
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hZρ, hZ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hup := kzUp_at hl hX hKB hA hρ b hbD hbA
  have hAeq : A = ConjT.Aη S (cdEta S l) := (Wg.wgOwnEta hl hX hA hρ).2
  set Z := gxTh (upsilon l) (ldAtR S l) (S.psi b (Om (1 + 1))) with hZdef
  set P := S.psi (vbTK S l K b) (Om (1 + 1)) with hPdef
  have hZ : SC Z := gxTh_SC hZρ hAt (SC_psi hκ2 _) (hZ1.trans (psiS_bounds (S := S) _ 1).1)
  have hPω : ω ≤ P := (Lw.lw_omega_lt_SC (SC_psi hκ2 _)).le
  refine le_antisymm hup (psi_le_of_key hZ fun e he heA => ?_)
  rcases lt_or_ge e A with h1 | h1
  · -- `ψ₁(e) ≤ ψ₁(A) = ρ = Θ(Ω₁) < Θ(ψ₂ b)`
    have hρZ : upsilon l < Z := by
      have h := gxTh_lt (Z := upsilon l) (At := ldAtR S l) GxCl.om (psiS_bounds (S := S) b 1).1
      rwa [gxTh_Om1 hZρ hZ1 hAt] at h
    exact ((psi_mono hκ1 h1.le).1.trans_eq hρ).trans_lt hρZ
  · -- `e = A + ξ`, `ξ = e % θ ∈ HCl`, `ξ < ψ₂(T b)`
    set ξ := e - A with hξdef
    have e1 : e = A + ξ := (Ordinal.add_sub_cancel_of_le h1).symm
    have hξP : ξ < P := by
      have h2 : A + ξ < A + (1 + P) := by rw [← e1, ← add_assoc]; exact heA
      have h3 := (add_lt_add_iff_left A).1 h2
      rwa [one_add_of_omega0_le hPω] at h3
    have hξH : HCl S (A + 1 + P) Z ξ := Kt.ktHCl_sub e he A
    obtain ⟨a, haD, hab, hξa, hlaw⟩ := hfam ξ hξH hξP
    have hle : A + ξ ≤ A + 1 + S.psi (vbTK S l K a) (Om (1 + 1)) := by
      rw [add_assoc, one_add_of_omega0_le (Lw.lw_omega_lt_SC (SC_psi hκ2 _)).le]
      exact add_le_add le_rfl hξa
    rw [e1]
    calc S.psi (A + ξ) (Om 1) ≤ S.psi (A + 1 + S.psi (vbTK S l K a) (Om (1 + 1))) (Om 1) := (psi_mono hκ1 hle).1
      _ = gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1))) := hlaw.symm
      _ < Z := by
          have hab' : a < b := by
            by_contra hc; push Not at hc; exact absurd hab (not_lt.2 (psi_mono hκ2 hc).1)
          exact gxTh_lt (GxCl.atom (kzAt hl hX hA hρ haD (hab'.trans hbA))) hab

end Main

end Googology.Trans.PoR.InaccPsi.R2.Kz

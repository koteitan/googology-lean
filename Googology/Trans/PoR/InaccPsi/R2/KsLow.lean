import Googology.Trans.PoR.InaccPsi.R2.KrPoly

/-!
# Ks: THE TOP LAW FROM ONE CLOSURE CONDITION (the lower half by the least non-member)

`Θ = gxTh ρ_λ (ldAtR λ)`, `T = Vb.vbT S λ`, `D = Vb.VbD S λ`, `A = A_{η_λ}` (own, `ψ₁(A) = ρ_λ`), `Z_b = Θ(ψ₂ b)`,
`α_b = A + 1 + ψ₂(T b)`, `Bt.HCl` the closure without the countable collapses.  The upper half
`Θ(ψ₂ b) ≤ ψ₁(α_b)` is `Xd.xdUp_at` (every `b ∈ D`); the lower half is `ψ₁(α_b) ≤ Z_b`, i.e. (`Bt.psi_le_of_key`)
`ψ₁(e) < Z_b` for every `e ∈ HCl(α_b, Z_b)` below `α_b`.

* `ksLow` (**THE TOP LAW FROM ONE CLOSURE CONDITION**): if every `ξ ∈ HCl(α_b, Z_b)` below `ψ₂(T b)` lies below
  `ψ₂(T a)` for some `a ∈ D` with `ψ₂ a < ψ₂ b` and the law at `a`, then the law holds at `b`.  No iteration and no
  context: the plateau of the jumps and the continuity of the limits both become instances of this condition;
* `ksCont` (**THE TOP LAW BY CONTINUITY**: `T b` a limit, the images `T a` of laws below cofinal in `T b`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ks

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Rx

variable {S : InaccSeq.{0}}

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hl hX hA hρ

/-- `ψ₂ a` is an atom of the hull for every `a ∈ D`. -/
theorem ksAt {a : Ordinal.{0}} (haD : VbD S l a) : S.psi a (Om (1 + 1)) ∈ ldAtR S l := by
  obtain ⟨-, rfl⟩ := Wg.wgOwnEta hl hX hA hρ
  exact ⟨a, haD.1, haD.2.2.trans_le (ConjT.OmW_le_A S _), rfl⟩

/-- **THE TOP LAW FROM ONE CLOSURE CONDITION.** -/
theorem ksLow {b : Ordinal.{0}} (hbD : VbD S l b)
    (hfam : ∀ ξ, HCl S (A + 1 + S.psi (vbT S l b) (Om (1 + 1)))
        (gxTh (upsilon l) (ldAtR S l) (S.psi b (Om (1 + 1)))) ξ → ξ < S.psi (vbT S l b) (Om (1 + 1)) →
      ∃ a, VbD S l a ∧ S.psi a (Om (1 + 1)) < S.psi b (Om (1 + 1)) ∧ ξ ≤ S.psi (vbT S l a) (Om (1 + 1)) ∧
        gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1))) =
          S.psi (A + 1 + S.psi (vbT S l a) (Om (1 + 1))) (Om 1)) :
    gxTh (upsilon l) (ldAtR S l) (S.psi b (Om (1 + 1))) =
      S.psi (A + 1 + S.psi (vbT S l b) (Om (1 + 1))) (Om 1) := by
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hZρ, hZ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hup := Xd.xdUp_at hl hX hA hρ b hbD
  have hAeq : A = ConjT.Aη S (cdEta S l) := (Wg.wgOwnEta hl hX hA hρ).2
  set Z := gxTh (upsilon l) (ldAtR S l) (S.psi b (Om (1 + 1))) with hZdef
  set P := S.psi (vbT S l b) (Om (1 + 1)) with hPdef
  have hZ : SC Z := gxTh_SC hZρ hAt (SC_psi hκ2 _) (hZ1.trans (psiS_bounds (S := S) _ 1).1)
  -- `ψ₂(T b) < θ` and `θ ∣ A`
  have hθSC := ConjT.SC_th S
  have hPθ : P < ConjT.th S :=
    psi_lt_psi_of_mem hκ2 (vbT_mem hl hX hbD).2 (vbT_mem hl hX hbD).1
  have hdvd : ConjT.th S ∣ A := by
    have := rxDvdTh (S := S) (cdEta S l) 0; rwa [mul_zero, add_zero, ← hAeq] at this
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
    have hξθ : ξ < ConjT.th S := hξP.trans hPθ
    have hm : e % ConjT.th S = ξ := by
      conv_lhs => rw [e1]
      rw [ldModK_add_lt hθSC A hξθ, Ordinal.mod_eq_zero_of_dvd hdvd, zero_add]
    have hξH : HCl S (A + 1 + P) Z ξ := by rw [← hm]; exact ruHCl_modK hθSC he
    obtain ⟨a, haD, hab, hξa, hlaw⟩ := hfam ξ hξH hξP
    have hle : A + ξ ≤ A + 1 + S.psi (vbT S l a) (Om (1 + 1)) := by
      rw [add_assoc, one_add_of_omega0_le (Lw.lw_omega_lt_SC (SC_psi hκ2 _)).le]
      exact add_le_add le_rfl hξa
    rw [e1]
    calc S.psi (A + ξ) (Om 1) ≤ S.psi (A + 1 + S.psi (vbT S l a) (Om (1 + 1))) (Om 1) := (psi_mono hκ1 hle).1
      _ = gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1))) := hlaw.symm
      _ < Z := gxTh_lt (GxCl.atom (ksAt hl hX hA hρ haD)) hab

/-- **THE TOP LAW BY CONTINUITY**: if `T b` is a limit and every `z < T b` lies below `T a` for some `a ∈ D` with
`ψ₂ a < ψ₂ b` and the law at `a`, the law holds at `b` (`ψ₂` is continuous at the limit `T b`, `Lw.lw_psi_limit`). -/
theorem ksCont {b : Ordinal.{0}} (hbD : VbD S l b) (hlim : IsSuccLimit (vbT S l b))
    (hcof : ∀ z, z < vbT S l b → ∃ a, VbD S l a ∧ S.psi a (Om (1 + 1)) < S.psi b (Om (1 + 1)) ∧
      z ≤ vbT S l a ∧ gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1))) =
        S.psi (A + 1 + S.psi (vbT S l a) (Om (1 + 1))) (Om 1)) :
    gxTh (upsilon l) (ldAtR S l) (S.psi b (Om (1 + 1))) =
      S.psi (A + 1 + S.psi (vbT S l b) (Om (1 + 1))) (Om 1) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  refine ksLow hl hX hA hρ hbD fun ξ _ hξ => ?_
  rw [Lw.lw_psi_limit S hκ2 hlim] at hξ
  have hbdd : BddAbove (range fun z : Iio (vbT S l b) => S.psi z.1 (Om (1 + 1))) :=
    ⟨Om (1 + 1), by rintro _ ⟨z, rfl⟩; exact (psi_lt hκ2 _).le⟩
  haveI : Nonempty (Iio (vbT S l b)) := ⟨⟨0, hlim.bot_lt⟩⟩
  obtain ⟨z, hz⟩ := (lt_ciSup_iff hbdd).1 hξ
  obtain ⟨a, haD, hab, hza, hlaw⟩ := hcof z.1 z.2
  exact ⟨a, haD, hab, hz.le.trans (psi_mono hκ2 hza).1, hlaw⟩

end Main

end Googology.Trans.PoR.InaccPsi.R2.Ks

#print axioms Googology.Trans.PoR.InaccPsi.R2.Ks.ksLow
#print axioms Googology.Trans.PoR.InaccPsi.R2.Ks.ksCont

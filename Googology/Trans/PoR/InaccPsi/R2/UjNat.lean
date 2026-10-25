import Googology.Trans.PoR.InaccPsi.R2.UjSucc

/-!
# The finite levels `W^{n+1}` over every offset past `Γ₂`, and the families over `Γ₂`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ_{Ω₂}(β + W^E)`, `Y₃ = ψ_{Ω₃}(Ω₃)`,
`Y₂ = ψ_{Ω₂}(Ω₂)`, `Γ₂ = ψ_{Ω₃}(0)`, `G₁ = ψ_{Ω₂}(0)`, `⊤` the own predicate that holds everywhere.

* `ujOwP_nat` (**every `n ≥ 1` is own at every offset**, image `n`);
* `ujLev_one` (**`UjLev ⊤ 1 1`**: the top at `X₀ + Ω₂` over every offset past `Γ₂`, from `Uj.ujTopE` and
  `Uj.ujTopW`), `ujLev_nat` (**`UjLev ⊤ (n+1) (n+1)` for every `n`**, by `Uj.ujLev_succ`: the top law
  `Θ(T_{X₀ + W^{n+1}}(β)) = ψ_{Ω₁}(Â + Ω^{X̂₀ + Ω^{n+1}})` at every offset `X₀` past `Γ₂`);
* `ujFamNat` (**the level-`(n+1)` family over any offset past `Γ₂`**: `X₀ + W^{n+1}·ζ`, `ζ < EE_j` a code);
* `ujGamOff` (`Γ₂` is an offset at every base), `ujGamLev` (**`RvTop (Γ₂ + W^{n+1}) (G₁ + Ω^{n+1}) 0`** at every
  base), `ujGamFam` (**the offsets `Γ₂ + W^{n+1}·ζ`** with their tops), `ujGamReadNat`
  (**`Θ_λ(ψ_{Ω₂}(W^{Γ₂ + W^{n+1}})) = ψ_{Ω₁}(A + 1 + Ω^{G₁ + Ω^{n+1}})`**).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Uj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rq
  Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Ug
  Googology.Trans.PoR.InaccPsi.R2.Ua

variable {S : InaccSeq.{0}}

/-- **Every `n ≥ 1` is own at every offset** (image `n`). -/
theorem ujOwP_nat (l : Ordinal.{0}) (n : ℕ) (hn : 1 ≤ n) :
    UjOwP S l (fun _ _ => True) ((n : ℕ) : Ordinal.{0}) ((n : ℕ) : Ordinal.{0}) := by
  have hlt : ∀ Q, SC Q → ((n : ℕ) : Ordinal.{0}) < Q := fun Q hQ =>
    (natCast_lt_omega0 n).trans (Lw.lw_omega_lt_SC hQ)
  refine ⟨fun b X0 _ => ⟨Nat.one_le_cast.2 hn, scNat_mem _ _ n, scNat_mem _ _ n, scNat_mem _ _ n,
    fun Q hQ _ => UgC.small (hlt Q hQ), fun Q hQ _ => UgC.small (hlt Q hQ)⟩, fun _ _ _ _ _ _ _ => trivial⟩

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **`UjLev ⊤ 1 1`**: the top at `X₀ + Ω₂` over every offset past `Γ₂`. -/
theorem ujLev_one : UjLev S l (fun _ _ => True) 1 1 := by
  intro b X0 Xh0 hoff _ _ _ _
  rw [leWe_one, leOe_one]
  rcases hoff with ⟨rfl, rfl⟩ | ⟨hs, ht⟩
  · have h := roTop_one (S := S) hl hX
    rw [Nat.cast_one, mul_one, mul_one] at h
    rw [zero_add, zero_add]
    exact rvTop_of_ro h
  · exact ujTopW hs hl hX (ujTopE hs hl hX ht)

/-- **`UjLev ⊤ (n+1) (n+1)` for every `n`**: the finite levels over every offset past `Γ₂`. -/
theorem ujLev_nat : ∀ n : ℕ,
    UjLev S l (fun _ _ => True) (((n : ℕ) : Ordinal.{0}) + 1) (((n : ℕ) : Ordinal.{0}) + 1)
  | 0 => by rw [Nat.cast_zero, zero_add]; exact ujLev_one hl hX
  | n + 1 => by
    have h := ujLev_succ hl hX (ujOwP_nat (S := S) l (n + 1) (Nat.le_add_left 1 n))
      (by rw [Nat.cast_succ]; exact ujLev_nat n) (fun _ _ h => h)
    exact h

/-- **The level-`(n+1)` family over any offset past `Γ₂`**: `X₀ + W^{n+1}·ζ` for every code `ζ < EE_j`. -/
theorem ujFamNat (n : ℕ) {X0 Xh0 β : Ordinal.{0}} (hoff : UjOff S l β X0 Xh0)
    (hd : leWe (((n : ℕ) : Ordinal.{0}) + 1 + 1) ∣ X0)
    (hG3 : X0 + leWe (((n : ℕ) : Ordinal.{0}) + 1 + 1) + Om (1 + 1) < ugY S)
    (hG : Xh0 + leOe (((n : ℕ) : Ordinal.{0}) + 1 + 1) + Om 1 < ujY S 0) :
    ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → (∃ j, ζ < rvEE S X0 β (((n : ℕ) : Ordinal.{0}) + 1) j) →
      gxTh (upsilon l) (ldAtR S l) ζ < Om 1 →
      UjOff S l β (X0 + leWe (((n : ℕ) : Ordinal.{0}) + 1) * ζ)
        (Xh0 + leOe (((n : ℕ) : Ordinal.{0}) + 1) * gxTh (upsilon l) (ldAtR S l) ζ) := by
  have hP := ujOwP_nat (S := S) l (n + 1) (Nat.le_add_left 1 n)
  rw [Nat.cast_succ] at hP
  exact ujFam hl hX hP (ujLev_nat hl hX n) hoff hd hG3 hG trivial

end Main

/-- **`Γ₂` is an offset past `Γ₂` at every base.** -/
theorem ujGamOff {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) (b : Ordinal.{0}) :
    UjOff S l b uaGam (S.psi 0 (Om (1 + 1))) :=
  Or.inr ⟨ujShG l b, ujTopG hl hX b⟩

section Gam

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

omit hl hX in
/-- The bounds at `Γ₂ + W^{n+1}`. -/
theorem ujGam_bounds (n : ℕ) :
    leWe (((n : ℕ) : Ordinal.{0}) + 1) ∣ uaGam ∧
      uaGam + leWe (((n : ℕ) : Ordinal.{0}) + 1) + Om (1 + 1) < ugY S ∧
      S.psi 0 (Om (1 + 1)) + leOe (((n : ℕ) : Ordinal.{0}) + 1) + Om 1 < ujY S 0 := by
  have hY : SC (ugY S) := ujY_SC (S := S) 1
  have hWY : Om (1 + 1 : Ordinal.{0}) < ugY S := ujY_gt (S := S) 1
  have hY2 : SC (ujY S 0) := ujY_SC 0
  have hΩY2 : Om (1 : Ordinal.{0}) < ujY S 0 := by have := ujY_gt (S := S) 0; rwa [zero_add] at this
  have hnω : ((n : ℕ) : Ordinal.{0}) + 1 < ω := by
    rw [← Nat.cast_succ]; exact natCast_lt_omega0 _
  have hnG : ((n : ℕ) : Ordinal.{0}) + 1 < uaGam := hnω.trans (Lw.lw_omega_lt_SC uaGam_spec.1)
  refine ⟨(leWe_lt_SC uaGam_spec.1 uaGam_spec.2 hnG).2,
    hY.isPrincipal (hY.isPrincipal ujGam_lt_Y (leWe_lt_SC hY hWY (hnω.trans (Lw.lw_omega_lt_SC hY))).1) hWY,
    hY2.isPrincipal (hY2.isPrincipal ujY2_gt_G1 (leOe_lt_SC hY2 hΩY2 (hnω.trans (Lw.lw_omega_lt_SC hY2))).1)
      hΩY2⟩

/-- **`RvTop (Γ₂ + W^{n+1}) (G₁ + Ω^{n+1}) 0`** at every base. -/
theorem ujGamLev (b : Ordinal.{0}) (n : ℕ) :
    RvTop S l b (uaGam + leWe (((n : ℕ) : Ordinal.{0}) + 1))
      (S.psi 0 (Om (1 + 1)) + leOe (((n : ℕ) : Ordinal.{0}) + 1)) 0 := by
  obtain ⟨hd, hG3, hG⟩ := ujGam_bounds (S := S) n
  exact ujLev_nat hl hX n b _ _ (ujGamOff hl hX b) hd hG3 hG trivial

/-- **The offsets `Γ₂ + W^{n+1}·ζ`** (every code `ζ < EE_j(Γ₂, β, n+1)` with `Θ ζ < Ω₁`) with their tops. -/
theorem ujGamFam (β : Ordinal.{0}) (n : ℕ) :
    ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → (∃ j, ζ < rvEE S uaGam β (((n : ℕ) : Ordinal.{0}) + 1) j) →
      gxTh (upsilon l) (ldAtR S l) ζ < Om 1 →
      UjOff S l β (uaGam + leWe (((n : ℕ) : Ordinal.{0}) + 1) * ζ)
        (S.psi 0 (Om (1 + 1)) + leOe (((n : ℕ) : Ordinal.{0}) + 1) * gxTh (upsilon l) (ldAtR S l) ζ) := by
  obtain ⟨hd, hG3, hG⟩ := ujGam_bounds (S := S) (n + 1)
  rw [Nat.cast_succ] at hd hG3 hG
  exact ujFamNat hl hX n (ujGamOff hl hX β) hd hG3 hG

/-- **`Θ_λ(ψ_{Ω₂}(W^{Γ₂ + W^{n+1}})) = ψ_{Ω₁}(A + 1 + Ω^{G₁ + Ω^{n+1}})`** at every restart `λ` with `A` own,
`ψ_{Ω₁}(A) = ρ_λ`. -/
theorem ujGamReadNat {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    (n : ℕ) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (leWe (uaGam + leWe (((n : ℕ) : Ordinal.{0}) + 1))) (Om (1 + 1))) =
      S.psi (A + 1 + leOe (S.psi 0 (Om (1 + 1)) + leOe (((n : ℕ) : Ordinal.{0}) + 1))) (Om 1) := by
  obtain ⟨-, hG3, -⟩ := ujGam_bounds (S := S) n
  exact ujRead0 (ujGamLev hl hX 0 n) (lt_of_le_of_lt le_self_add hG3) hA hρ

end Gam

end Googology.Trans.PoR.InaccPsi.R2.Uj

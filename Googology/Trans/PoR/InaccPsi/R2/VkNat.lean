import Googology.Trans.PoR.InaccPsi.R2.VkSucc

/-!
# The finite levels `W^{n+1}` over every offset, with no bound

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ_{Ω₂}(β + W^E)`, `⊤` the own predicate that holds
everywhere.

* `vkOwP_nat` (every `n ≥ 1` is own at every offset, image `n`);
* `vkLev_one` (**`VkLev ⊤ 1 1`**: the top at `X₀ + Ω₂` over every offset, from `Vk.vkTopE` and `Vk.vkTopW`),
  `vkLev_nat` (**`VkLev ⊤ (n+1) (n+1)` for every `n`**);
* `vkFamNat` (**the level-`(n+1)` family over any offset**: `X₀ + W^{n+1}·ζ`, `ζ < EE_j` a code).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Vk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rq
  Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Ug
  Googology.Trans.PoR.InaccPsi.R2.Ua Googology.Trans.PoR.InaccPsi.R2.Uj

variable {S : InaccSeq.{0}}

/-- **Every `n ≥ 1` is own at every offset** (image `n`). -/
theorem vkOwP_nat (l : Ordinal.{0}) (n : ℕ) (hn : 1 ≤ n) :
    VkOwP S l (fun _ _ => True) ((n : ℕ) : Ordinal.{0}) ((n : ℕ) : Ordinal.{0}) := by
  have hlt : ∀ Q, SC Q → ((n : ℕ) : Ordinal.{0}) < Q := fun Q hQ =>
    (natCast_lt_omega0 n).trans (Lw.lw_omega_lt_SC hQ)
  refine ⟨fun b X0 _ => ⟨Nat.one_le_cast.2 hn, scNat_mem _ _ n, scNat_mem _ _ n, scNat_mem _ _ n,
    fun Q hQ _ => VkA.small (hlt Q hQ), fun Q hQ _ => VkA.small (hlt Q hQ)⟩, fun _ _ _ _ _ _ _ => trivial⟩

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **`VkLev ⊤ 1 1`**: the top at `X₀ + Ω₂` over every offset (no bound). -/
theorem vkLev_one : VkLev S l (fun _ _ => True) 1 1 := by
  intro b X0 Xh0 hoff _ _
  rw [leWe_one, leOe_one]
  rcases hoff with ⟨rfl, rfl⟩ | ⟨hs, ht⟩
  · have h := roTop_one (S := S) hl hX
    rw [Nat.cast_one, mul_one, mul_one] at h
    rw [zero_add, zero_add]
    exact rvTop_of_ro h
  · exact vkTopW hs hl hX (vkTopE hs hl hX ht)

/-- **`VkLev ⊤ (n+1) (n+1)` for every `n`**: the finite levels over every offset (no bound). -/
theorem vkLev_nat : ∀ n : ℕ,
    VkLev S l (fun _ _ => True) (((n : ℕ) : Ordinal.{0}) + 1) (((n : ℕ) : Ordinal.{0}) + 1)
  | 0 => by rw [Nat.cast_zero, zero_add]; exact vkLev_one hl hX
  | n + 1 => by
    have h := vkLev_succ hl hX (vkOwP_nat (S := S) l (n + 1) (Nat.le_add_left 1 n))
      (by rw [Nat.cast_succ]; exact vkLev_nat n) (fun _ _ h => h)
    exact h

/-- **The level-`(n+1)` family over any offset**: `X₀ + W^{n+1}·ζ` for every code `ζ < EE_j`. -/
theorem vkFamNat (n : ℕ) {X0 Xh0 β : Ordinal.{0}} (hoff : VkOff S l β X0 Xh0)
    (hd : leWe (((n : ℕ) : Ordinal.{0}) + 1 + 1) ∣ X0) :
    ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → (∃ j, ζ < rvEE S X0 β (((n : ℕ) : Ordinal.{0}) + 1) j) →
      gxTh (upsilon l) (ldAtR S l) ζ < Om 1 →
      VkOff S l β (X0 + leWe (((n : ℕ) : Ordinal.{0}) + 1) * ζ)
        (Xh0 + leOe (((n : ℕ) : Ordinal.{0}) + 1) * gxTh (upsilon l) (ldAtR S l) ζ) := by
  have hP := vkOwP_nat (S := S) l (n + 1) (Nat.le_add_left 1 n)
  rw [Nat.cast_succ] at hP
  exact vkFam hl hX hP (vkLev_nat hl hX n) hoff hd trivial

end Main

end Googology.Trans.PoR.InaccPsi.R2.Vk

import Googology.Trans.PoR.InaccPsi.R2.VkLay

/-!
# The collapse key relative to the members: every element of `Cl(a, ψ_{Ω_{s+1}}(a))` is a code

`VkA k Q` the codes over `Q` above the level `k` (`Vk.VkA`: ordinals below `Q`, every strongly critical `s ≥ Ω_k`,
`+`, `φ`).

`Vk.vkKey` asks `ψ_{Ω_{s+1}}(e) < Q` for **every** code `e < a`; at `Q = ψ_{Ω_{s+1}}(a)` this fails (a code `e < a`
need not lie in `Cl(a, ψ_{Ω_{s+1}}(a))`).  Here the collapse condition is asked only for the **members** `e < a` of
`Cl(a, Q)` that are codes; `Vk.vkKey` is the special case (`wbKey_vk`), and at `Q = ψ_{Ω_{s+1}}(a)` the condition
holds by itself:

* `wbKeyM` (**every element of `Cl(a, Q)` is a code above the level `s + 1`**, given `ψ_{Ω_{s+1}}(e) < Q` for the
  members `e < a` that are codes), `wbKey_vk` (`Vk.vkKey` from it);
* `wbA_self` (**every element of `Cl(a, ψ_{Ω_{s+1}}(a))` is a code above the level `s + 1` over `ψ_{Ω_{s+1}}(a)`**,
  no hypothesis beyond `s ∈ Cl`, `Ω_{s+1} < I_n`), `wbA_own` (**an own exponent `E ∈ Cl(β + W^E, T_E(β))` is a code
  above the level 2 over every `Q ≥ T_E(β)`**).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Wb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Vk

variable {S : InaccSeq.{0}}

/-- **Every element of `Cl(a, Q)` is a code above the level `s + 1`**, given `ψ_{Ω_{s+1}}(e) < Q` for every member
`e < a` of `Cl(a, Q)` that is a code. -/
theorem wbKeyM {s a Q : Ordinal.{0}} (hQ : SC Q) (hsQ : Om s < Q) (hsC : ∀ a b, s ∈ S.CSet a b)
    (hI : ∀ n, Om (s + 1) < S.I n)
    (hcoll : ∀ e, e < a → e ∈ S.CSet a Q → VkA (s + 1) Q e → S.psi e (Om (s + 1)) < Q) :
    ∀ x ∈ S.CSet a Q, VkA (s + 1) Q x := by
  intro x hx
  induction hx with
  | small h => exact VkA.small h
  | zero => exact VkA.zero hQ.1
  | inacc n => exact VkA.big (hI n).le (SC_I n)
  | inaccW => exact VkA.big ((hI 0).le.trans (Ordinal.le_iSup (fun n => S.I n) 0)) SC_Iw
  | add _ _ ihx ihy => exact VkA.add ihx ihy
  | phi _ _ ihx ihy => exact VkA.phi ihx ihy
  | @om x _ _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero]; exact VkA.zero hQ.1
    rcases lt_or_ge x (s + 1) with hx | hx
    · refine VkA.small (lt_of_le_of_lt (Om_le_Om.2 ?_) hsQ)
      rw [← Order.succ_eq_add_one] at hx; exact Order.lt_succ_iff.1 hx
    · exact VkA.big (Om_le_Om.2 hx) (SC_Om hx0)
  | @coll π e hπ _ heC _ ihe =>
    rcases hπ with ⟨n, rfl⟩ | ⟨t, rfl⟩
    · exact VkA.big (lt_psi_of_mem (InR_I n) (CSet.Om_mem (CSet.succ_mem (hsC _ _))) (hI n)).le
        (SC_psi (InR_I n) _)
    rcases lt_trichotomy t s with hts | hts | hts
    · refine VkA.small (lt_of_lt_of_le (psi_lt (InR_Om_succ t) _) ((Om_le_Om.2 ?_).trans hsQ.le))
      exact Order.add_one_le_of_lt hts
    · subst hts; exact VkA.small (hcoll e.1 e.2 heC ihe)
    · exact VkA.big ((Om_lt_psiS e.1 t).2 (Order.add_one_le_of_lt hts)).le (SC_psi (InR_Om_succ t) _)

/-- `Vk.vkKey` is the special case of `wbKeyM` (collapse condition at every code `e < a`). -/
theorem wbKey_vk {s a Q : Ordinal.{0}} (hQ : SC Q) (hsQ : Om s < Q) (hsC : ∀ a b, s ∈ S.CSet a b)
    (hI : ∀ n, Om (s + 1) < S.I n)
    (hcoll : ∀ e, e < a → VkA (s + 1) Q e → S.psi e (Om (s + 1)) < Q) :
    ∀ x ∈ S.CSet a Q, VkA (s + 1) Q x :=
  wbKeyM hQ hsQ hsC hI fun e he _ hc => hcoll e he hc

/-- **Every element of `Cl(a, ψ_{Ω_{s+1}}(a))` is a code above the level `s + 1` over `ψ_{Ω_{s+1}}(a)`.** -/
theorem wbA_self {s a : Ordinal.{0}} (hsC : ∀ a b, s ∈ S.CSet a b) (hI : ∀ n, Om (s + 1) < S.I n) :
    ∀ x ∈ S.CSet a (S.psi a (Om (s + 1))), VkA (s + 1) (S.psi a (Om (s + 1))) x :=
  wbKeyM (SC_psi (InR_Om_succ s) a) (psiS_bounds (S := S) a s).1 hsC hI
    fun _ he hmem _ => psi_lt_psi_of_mem (InR_Om_succ s) he hmem

theorem wbOm2_lt_I (n : ℕ) : Om (1 + 1 : Ordinal.{0}) < S.I n :=
  (Om_lt_Om.2 (lt_add_one _)).trans (leOm3_lt_I n)

/-- **An own exponent is a code above the level 2**: `E ∈ Cl(β + W^E, T_E(β))` ⇒ `VkA 2 Q E` for every
`Q ≥ T_E(β)`. -/
theorem wbA_own {E β Q : Ordinal.{0}} (hEC : E ∈ S.CSet (β + leWe E) (S.psi (β + leWe E) (Om (1 + 1))))
    (hQ : S.psi (β + leWe E) (Om (1 + 1)) ≤ Q) : VkA (1 + 1) Q E :=
  VkA.mono hQ (wbA_self (s := 1) (fun a b => CSet.one_mem a b) wbOm2_lt_I E hEC)

#print axioms wbKeyM
#print axioms wbKey_vk
#print axioms wbA_self
#print axioms wbA_own

end Googology.Trans.PoR.InaccPsi.R2.Wb

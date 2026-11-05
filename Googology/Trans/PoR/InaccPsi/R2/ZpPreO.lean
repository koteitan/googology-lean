import Googology.Trans.PoR.InaccPsi.R2.ZpPre
import Googology.Trans.PoR.InaccPsi.R2.VbDef

/-!
# The `ω^K`-prefix of a normal argument is normal (every `K`)

`P_K(x) = ω^K·(x/ω^K)` (the sum of the Cantor normal form terms of `x` with exponent `≥ K`).  This is the form the
classification of a base `b = β + W^E·γ` needs (`β = P_{Ω₂·(E+1)}(b)`, `W^{E+1}` is not strongly critical, so
`Zp.zpPre_norm` does not apply).

* `zpPreO_mem` (**`Cl(a, c)` contains `P_K(x)` for each member `x`**: one induction on the Cantor normal form,
  `InaccSeq` closure under `ω^·`, `+`, `·n`, and `Rx.rxCDec`, `Vb.vbC_rem` for the parts);
* `zpPre_normG` (**the gap argument for any divisor `Q ≠ 0` whose prefix is in every closure**);
* `zpPreO_norm` (**THE `ω^K`-PREFIX OF A NORMAL ARGUMENT IS NORMAL**, every `κ`, every `K`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq

variable {S : InaccSeq.{0}}

/-- **`Cl(a, c)` contains the `ω^K`-prefix of each member.** -/
theorem zpPreO_mem {a c : Ordinal.{0}} (K : Ordinal.{0}) :
    ∀ x, x ∈ S.CSet a c → ω ^ K * (x / ω ^ K) ∈ S.CSet a c := by
  have hK0 : ω ^ K ≠ 0 := opow_ne_zero _ omega0_ne_zero
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IHx =>
  intro hx
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [Ordinal.zero_div, mul_zero]; exact CSet.zero_mem a c
  set L := log ω x with hL
  obtain ⟨m, hm⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
  have hdm : x = ω ^ L * m + x % ω ^ L := by
    rw [← hm]; exact (Ordinal.div_add_mod x _).symm
  have hLC : L ∈ S.CSet a c := (Rx.rxCDec x hx).2
  have hoC : ω ^ L ∈ S.CSet a c := by
    have := CSet.phi_mem (S := S) (CSet.zero_mem a c) hLC; rwa [veblen_zero_apply] at this
  have hrC : x % ω ^ L ∈ S.CSet a c := Vb.vbC_rem hx
  have hrlt : x % ω ^ L < x :=
    (Ordinal.mod_lt x (opow_ne_zero _ omega0_ne_zero)).trans_le (opow_log_le_self ω hx0)
  rcases le_or_gt K L with hKL | hLK
  · -- `ω^K ∣ ω^L·m`
    have hsplit : ω ^ L * (m : Ordinal.{0}) = ω ^ K * (ω ^ (L - K) * m) := by
      rw [← mul_assoc, ← opow_add, Ordinal.add_sub_cancel_of_le hKL]
    have e : ω ^ K * (x / ω ^ K) = ω ^ L * m + ω ^ K * ((x % ω ^ L) / ω ^ K) := by
      conv_lhs => rw [hdm, hsplit, Ordinal.mul_add_div _ hK0, mul_add]
      rw [← hsplit]
    rw [e]
    exact CSet.add_mem (ConjT.mul_nat_mem S hoC m) (IHx _ hrlt hrC)
  · -- `x < ω^K`
    have hxK : x < ω ^ K := by
      calc x < ω ^ Order.succ L := lt_opow_succ_log_self one_lt_omega0 x
        _ ≤ ω ^ K := opow_le_opow_right omega0_pos (Order.succ_le_of_lt hLK)
    rw [Ordinal.div_eq_zero_of_lt hxK, mul_zero]; exact CSet.zero_mem a c

/-- **The gap argument for any divisor `Q ≠ 0` whose prefix is in every closure.** -/
theorem zpPre_normG {κ Q a : Ordinal.{0}} (hκ : S.InR κ) (hQ0 : Q ≠ 0)
    (hpre : ∀ x y z, z ∈ S.CSet x y → Q * (z / Q) ∈ S.CSet x y)
    (ha : a ∈ S.CSet a (S.psi a κ)) :
    Q * (a / Q) ∈ S.CSet (Q * (a / Q)) (S.psi (Q * (a / Q)) κ) := by
  by_contra hb
  have hgap : ∀ e, Q * (a / Q) ≤ e → e < a → e ∉ S.CSet (Q * (a / Q)) (S.psi (Q * (a / Q)) κ) := by
    intro e hbe hea he
    apply hb
    have h := hpre _ _ _ he
    rwa [zpPre_eq hQ0 hbe hea] at h
  obtain ⟨-, hsub⟩ := zpGap_psi hκ (zpPre_le Q a) hgap
  exact hb (hsub (hpre _ _ _ ha))

/-- **THE `ω^K`-PREFIX OF A NORMAL ARGUMENT IS NORMAL.** -/
theorem zpPreO_norm {κ a : Ordinal.{0}} (hκ : S.InR κ) (K : Ordinal.{0}) (ha : a ∈ S.CSet a (S.psi a κ)) :
    ω ^ K * (a / ω ^ K) ∈ S.CSet (ω ^ K * (a / ω ^ K)) (S.psi (ω ^ K * (a / ω ^ K)) κ) :=
  zpPre_normG hκ (opow_ne_zero _ omega0_ne_zero) (fun _ _ z hz => zpPreO_mem K z hz) ha

end Googology.Trans.PoR.InaccPsi.R2.Zp

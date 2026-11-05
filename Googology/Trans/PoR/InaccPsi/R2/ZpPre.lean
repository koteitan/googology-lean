import Googology.Trans.PoR.InaccPsi.R2.LdAlg

/-!
# The `Q`-prefix of a normal argument is normal

`Q` strongly critical and in every closure (e.g. `Q = Ω₃`), `b = Q·(a/Q)` the `Q`-divisible part of `a`
(`a = b + δ`, `δ = a mod Q < Q`).

* `zpPre_mem` (**`Cl(a, c)` contains the `Q`-prefix of each member**: `Ld.ldDivK_mem`, `Ld.ldMulK_mem`);
* `zpGap_sub` (**a gap gives no new members**: if no `e ∈ [b, α)` is in `Cl(b, c)` then `Cl(α, c) ⊆ Cl(b, c)`;
  one induction on the closure, the collapse case uses `e < α` and the gap);
* `zpGap_psi` (**the collapse is constant across a gap**: then `ψ_κ(α) = ψ_κ(b)` and
  `Cl(α, ψ_κ α) ⊆ Cl(b, ψ_κ b)`, from the defining property of `ψ_κ`, `InaccSeq.psi_le_of_good`);
* `zpPre_norm` (**THE PREFIX IS NORMAL**: `a ∈ Cl(a, ψ_κ a)` ⇒ `b ∈ Cl(b, ψ_κ b)`, for every `κ`: if `b` were not
  normal, `[b, a)` is a gap of `Cl(b, ψ_κ b)` because every `e ∈ [b, a)` has the same prefix `b`, so
  `b ∈ Cl(a, ψ_κ a) ⊆ Cl(b, ψ_κ b)`);
* `zpPre_div` (`Q ∣ b`), `zpPre_le` (`b ≤ a`), `zpPre_lt` (`a < b + Q`), `zpPre_eq` (`e ∈ [b, a) ⇒ Q·(e/Q) = b`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq

variable {S : InaccSeq.{0}}

/-- **`Cl(a, c)` contains the `Q`-prefix of each member.** -/
theorem zpPre_mem {Q a c x : Ordinal.{0}} (hQ : SC Q) (hQC : Q ∈ S.CSet a c) (hx : x ∈ S.CSet a c) :
    Q * (x / Q) ∈ S.CSet a c :=
  Ld.ldMulK_mem hQ hQC (Ld.ldDivK_mem hQ hx)

theorem zpPre_le (Q a : Ordinal.{0}) : Q * (a / Q) ≤ a := Ordinal.mul_div_le a Q

theorem zpPre_div (Q a : Ordinal.{0}) : Q ∣ Q * (a / Q) := dvd_mul_right Q _

theorem zpPre_lt {Q : Ordinal.{0}} (hQ0 : Q ≠ 0) (a : Ordinal.{0}) : a < Q * (a / Q) + Q := by
  have h := Ordinal.div_add_mod a Q
  calc a = Q * (a / Q) + a % Q := h.symm
    _ < Q * (a / Q) + Q := by
      exact (add_lt_add_iff_left _).2 (Ordinal.mod_lt a hQ0)

/-- Every `e ∈ [b, a)` has the prefix `b = Q·(a/Q)`. -/
theorem zpPre_eq {Q a e : Ordinal.{0}} (hQ0 : Q ≠ 0) (hbe : Q * (a / Q) ≤ e) (hea : e < a) :
    Q * (e / Q) = Q * (a / Q) := by
  set b := Q * (a / Q) with hb
  have hε : e - b < Q := Ordinal.sub_lt_of_lt_add (hea.trans (zpPre_lt hQ0 a)) (pos_iff_ne_zero.2 hQ0)
  have he : e = Q * (a / Q) + (e - b) := (Ordinal.add_sub_cancel_of_le hbe).symm
  have hd : e / Q = a / Q := by
    rw [he, Ordinal.mul_add_div _ hQ0, Ordinal.div_eq_zero_of_lt hε, add_zero]
  rw [hd]

/-- **A gap gives no new members.** -/
theorem zpGap_sub {α b c : Ordinal.{0}} (hgap : ∀ e, b ≤ e → e < α → e ∉ S.CSet b c) :
    S.CSet α c ⊆ S.CSet b c := by
  intro x hx
  induction hx with
  | small h => exact Clos.small h
  | zero => exact Clos.zero
  | inacc n => exact Clos.inacc n
  | inaccW => exact Clos.inaccW
  | add _ _ ihx ihy => exact Clos.add ihx ihy
  | phi _ _ ihx ihy => exact Clos.phi ihx ihy
  | om _ ih => exact Clos.om ih
  | @coll π e hπ _ _ ihπ ihe =>
    have heb : e.1 < b := by
      by_contra h
      exact hgap e.1 (not_lt.1 h) e.2 ihe
    exact Clos.coll (e := ⟨e.1, heb⟩) hπ ihπ ihe

/-- **The collapse is constant across a gap.** -/
theorem zpGap_psi {κ α b : Ordinal.{0}} (hκ : S.InR κ) (hbα : b ≤ α)
    (hgap : ∀ e, b ≤ e → e < α → e ∉ S.CSet b (S.psi b κ)) :
    S.psi α κ = S.psi b κ ∧ S.CSet α (S.psi α κ) ⊆ S.CSet b (S.psi b κ) := by
  have hsub := zpGap_sub hgap
  have hle : S.psi α κ ≤ S.psi b κ :=
    psi_le_of_good (mem_CSet_psi_any hκ α b) fun x hx hxκ => lt_psi_of_mem hκ (hsub hx) hxκ
  have heq : S.psi α κ = S.psi b κ := le_antisymm hle (psi_mono hκ hbα).1
  refine ⟨heq, ?_⟩
  rw [heq]; exact hsub

/-- **THE PREFIX IS NORMAL**: `a ∈ Cl(a, ψ_κ a)` ⇒ `Q·(a/Q) ∈ Cl(Q·(a/Q), ψ_κ(Q·(a/Q)))`. -/
theorem zpPre_norm {κ Q a : Ordinal.{0}} (hκ : S.InR κ) (hQ : SC Q) (hQC : ∀ x y, Q ∈ S.CSet x y)
    (ha : a ∈ S.CSet a (S.psi a κ)) :
    Q * (a / Q) ∈ S.CSet (Q * (a / Q)) (S.psi (Q * (a / Q)) κ) := by
  have hQ0 : Q ≠ 0 := hQ.1.ne'
  by_contra hb
  have hgap : ∀ e, Q * (a / Q) ≤ e → e < a → e ∉ S.CSet (Q * (a / Q)) (S.psi (Q * (a / Q)) κ) := by
    intro e hbe hea he
    apply hb
    have h := zpPre_mem hQ (hQC _ _) he
    rwa [zpPre_eq hQ0 hbe hea] at h
  obtain ⟨-, hsub⟩ := zpGap_psi hκ (zpPre_le Q a) hgap
  exact hb (hsub (zpPre_mem hQ (hQC _ _) ha))

/-- `Ω₃` is in every closure. -/
theorem zpOm3_mem (x y : Ordinal.{0}) : Om (1 + 1 + 1) ∈ S.CSet x y :=
  CSet.Om_mem (CSet.add_mem (CSet.add_mem (CSet.one_mem x y) (CSet.one_mem x y)) (CSet.one_mem x y))

theorem zpOm3_SC (S : InaccSeq.{0}) : SC (Om (1 + 1 + 1 : Ordinal.{0})) := (InR_Om_succ (S := S) (1 + 1)).SC S

/-- **The `Ω₃`-prefix of a `ψ₂`-normal argument is `ψ₂`-normal.** -/
theorem zpPre3_norm {a : Ordinal.{0}} (ha : a ∈ S.CSet a (S.psi a (Om (1 + 1)))) :
    Om (1 + 1 + 1) * (a / Om (1 + 1 + 1)) ∈
      S.CSet (Om (1 + 1 + 1) * (a / Om (1 + 1 + 1))) (S.psi (Om (1 + 1 + 1) * (a / Om (1 + 1 + 1))) (Om (1 + 1))) :=
  zpPre_norm (InR_Om_succ 1) (zpOm3_SC S) zpOm3_mem ha

end Googology.Trans.PoR.InaccPsi.R2.Zp

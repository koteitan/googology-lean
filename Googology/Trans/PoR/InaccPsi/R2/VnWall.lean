import Googology.Trans.PoR.InaccPsi.R2.VkTh
import Googology.Trans.PoR.InaccPsi.R2.UuSys

/-!
# The self-relative own notions have no member in `[Y_{k+3}, Ω_{k+3})`; `ψ_{Ω₂}` does not see past `Y_{s+1}`

`κ = Ω_{s+1}`, `Y = ψ_κ(κ)`, `Y_{k+3} = ψ_{Ω_{k+3}}(Ω_{k+3}) = Uj.ujY S (k + 1)`, `y_n` the iterates of `ψ_κ` from
`0` (`y_0 = 0`, `y_{n+1} = ψ_κ(y_n)`).

* `vnCSet_sub` (**`Cl(a, b) ⊆ Cl(Y, b)` for `a ≤ κ`, `b ≤ Y`**: no argument `e ∈ [Y, κ)` of a collapse is ever
  generated), `vnPsi2_eq` (**`ψ_{Ω₂}(a) = ψ_{Ω₂}(Y)` for every `Y ≤ a ≤ κ`** when `Ω₂ < Y`);
* `vnNoSelf` (**no `X ∈ [Y, κ)` lies in `Cl(X, Q)` for `Q ≤ ψ_κ(X)`**), `vnNoSh` (**no shift `Vk.VkSh` and**),
  `vnNoOwnE` (**no own exponent `Vk.VkOwnE` lies in `[Y_{k+3}, Ω_{k+3})`, for every `k`**: their membership
  fields `X ∈ Cl(X, ·)`, `E ∈ Cl(E, ·)` are relative to `X`, `E` themselves, not to the base);
* `vnIt_mem`, `vnIt_lt` (the iterates are in every closure that contains them, and below `Y`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Vn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Uj Googology.Trans.PoR.InaccPsi.R2.Vk

variable {S : InaccSeq.{0}}

/-- **`Cl(a, b) ⊆ Cl(Y, b)`** for `a ≤ κ = Ω_{s+1}` and `b ≤ Y = ψ_κ(κ)`. -/
theorem vnCSet_sub {s a b : Ordinal.{0}} (haκ : a ≤ Om (s + 1))
    (hbY : b ≤ S.psi (Om (s + 1)) (Om (s + 1))) :
    S.CSet a b ⊆ S.CSet (S.psi (Om (s + 1)) (Om (s + 1))) b := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  intro x hx
  induction hx with
  | small h => exact Clos.small h
  | zero => exact Clos.zero
  | inacc n => exact Clos.inacc n
  | inaccW => exact Clos.inaccW
  | add _ _ ihx ihy => exact Clos.add ihx ihy
  | phi _ _ ihx ihy => exact Clos.phi ihx ihy
  | om _ ih => exact Clos.om ih
  | @coll π e hπ _ heC ihπ ihe =>
    have he : e.1 < S.psi (Om (s + 1)) (Om (s + 1)) :=
      lt_psi_of_mem hκ (CSet_mono haκ hbY heC) (lt_of_lt_of_le e.2 haκ)
    exact Clos.coll (e := ⟨e.1, he⟩) hπ ihπ ihe

/-- **`ψ_{Ω₂}(a) = ψ_{Ω₂}(Y)` for every `Y ≤ a ≤ κ`** (`Y = ψ_κ(κ) > Ω₂`). -/
theorem vnPsi2_eq {s a : Ordinal.{0}} (h2 : Om (1 + 1) < S.psi (Om (s + 1)) (Om (s + 1)))
    (hYa : S.psi (Om (s + 1)) (Om (s + 1)) ≤ a) (haκ : a ≤ Om (s + 1)) :
    S.psi a (Om (1 + 1)) = S.psi (S.psi (Om (s + 1)) (Om (s + 1))) (Om (1 + 1)) := by
  have hκ2 : S.InR (Om (1 + 1)) := InR_Om_succ 1
  refine le_antisymm ?_ (psi_mono hκ2 hYa).1
  have hbY : S.psi (S.psi (Om (s + 1)) (Om (s + 1))) (Om (1 + 1)) ≤ S.psi (Om (s + 1)) (Om (s + 1)) :=
    (psi_lt hκ2 _).le.trans h2.le
  exact psi_le_of_good (Mx.mxOm2_mem _ _) fun x hx hx2 =>
    lt_psi_of_mem hκ2 (vnCSet_sub haκ hbY hx) hx2

/-- **No `X ∈ [Y, κ)` lies in `Cl(X, Q)`** for `Q ≤ ψ_κ(X)`. -/
theorem vnNoSelf {s X Q : Ordinal.{0}} (hYX : S.psi (Om (s + 1)) (Om (s + 1)) ≤ X) (hXκ : X < Om (s + 1))
    (hQ : Q ≤ S.psi X (Om (s + 1))) : X ∉ S.CSet X Q := by
  intro h
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  have h2 : X < S.psi X (Om (s + 1)) := lt_psi_of_mem hκ (CSet_mono le_rfl hQ h) hXκ
  exact absurd (h2.trans_le ((psi_mono hκ hXκ.le).1.trans hYX)) (lt_irrefl X)

/-- `Ω₂ ≤ Ω_{k+2}` and every `ψ_{Ω₂}(x)` is below `ψ_{Ω_{k+3}}(X)`. -/
theorem vnPsi2_le_psi (k : ℕ) (x X : Ordinal.{0}) :
    S.psi x (Om (1 + 1)) ≤ S.psi X (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) := by
  have hk2 : (1 + 1 : Ordinal.{0}) ≤ (k : Ordinal.{0}) + 1 + 1 := by gcongr; exact le_add_self
  exact ((psi_lt (InR_Om_succ 1) x).trans_le (Om_le_Om.2 hk2)).le.trans
    (psiS_bounds (S := S) X ((k : Ordinal.{0}) + 1 + 1)).1.le

/-- **No shift `Vk.VkSh` lies in `[Y_{k+3}, Ω_{k+3})`, for every `k`** (any `λ`, base, image). -/
theorem vnNoSh (k : ℕ) {l b X Xh : Ordinal.{0}} (hYX : ujY S ((k : Ordinal.{0}) + 1) ≤ X)
    (hXκ : X < Om ((k : Ordinal.{0}) + 1 + 1 + 1)) : ¬ VkSh S l b X Xh := fun hs =>
  vnNoSelf (s := (k : Ordinal.{0}) + 1 + 1) hYX hXκ (vnPsi2_le_psi k _ X) hs.mem

/-- **No own exponent `Vk.VkOwnE` lies in `[Y_{k+3}, Ω_{k+3})`, for every `k`** (any `λ`, base, offset, image). -/
theorem vnNoOwnE (k : ℕ) {l b X0 E Eh : Ordinal.{0}} (hYE : ujY S ((k : Ordinal.{0}) + 1) ≤ E)
    (hEκ : E < Om ((k : Ordinal.{0}) + 1 + 1 + 1)) : ¬ VkOwnE S l b X0 E Eh := fun h =>
  vnNoSelf (s := (k : Ordinal.{0}) + 1 + 1) hYE hEκ (vnPsi2_le_psi k _ E) h.mem

/-- **The iterates `y_n` of `ψ_κ` lie in every `Cl(a, b)` with `y_n ≤ a`** (given `κ ∈ Cl(a, b)` always). -/
theorem vnIt_mem {s : Ordinal.{0}} (hκC : ∀ a b, Om (s + 1) ∈ S.CSet a b) : ∀ n : ℕ, ∀ a b,
    (fun x => S.psi x (Om (s + 1)))^[n] 0 ≤ a → (fun x => S.psi x (Om (s + 1)))^[n] 0 ∈ S.CSet a b := by
  intro n
  induction n with
  | zero => intro a b _; exact CSet.zero_mem a b
  | succ n ih =>
    intro a b h
    have hlt := Uu.uuIt_lt (S := S) s n
    rw [Function.iterate_succ_apply'] at h hlt ⊢
    exact CSet.psi_mem (hlt.trans_le h) (InR_Om_succ s) (hκC a b) (ih a b (hlt.le.trans h))

/-- **The iterates `y_n` are below `Y = ψ_κ(κ)`.** -/
theorem vnIt_lt {s : Ordinal.{0}} (hκC : ∀ a b, Om (s + 1) ∈ S.CSet a b) :
    ∀ n : ℕ, (fun x => S.psi x (Om (s + 1)))^[n] 0 < S.psi (Om (s + 1)) (Om (s + 1)) := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  intro n
  induction n with
  | zero => exact (SC_psi hκ _).1
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hn : (fun x => S.psi x (Om (s + 1)))^[n] 0 < Om (s + 1) := ih.trans (psi_lt hκ _)
    exact psi_lt_psi_of_mem hκ hn (vnIt_mem hκC n _ _ hn.le)

end Googology.Trans.PoR.InaccPsi.R2.Vn

import Googology.Trans.PoR.InaccPsi.R2.TaVeb
import Googology.Trans.PoR.InaccPsi.R2.VnTopK
import Googology.Trans.PoR.InaccPsi.R2.VqNoGo

/-!
# The plateau of `ψ_{Ω₂}` over every base: the moved shift `Y_κ(β) = ψ_κ(β + κ)`

`κ = Ω_{s+1}`, `Y_κ(β) = ψ_κ(β + κ)` (at `β = 0`: `Y = ψ_κ(κ)`), `W^E = Ω₂^E`.

* `vxCSet_sub` (**`Cl(β + a, b) ⊆ Cl(β + Y_κ(β), b)` for `a ≤ κ`, `b ≤ Y_κ(β)`**: the base-relative form of
  `Vn.vnCSet_sub`; the collapse arguments `e ∈ [β, β + κ)` have `e - β < Y_κ(β)`);
* `vxPsi2_eq` (**`ψ_{Ω₂}(β + a) = ψ_{Ω₂}(β + Y_κ(β))` for every `Y_κ(β) ≤ a ≤ κ`** when `Ω₂ < Y_κ(β)`);
* `vxTe_OmK` (**`T_{Ω_{k+3}}(β) = ψ₂(β + Ω_{k+3}) = ψ₂(β + Y_{Ω_{k+3}}(β))` at every base `β`**: the top of the
  shift `Ω_{k+3}` over `β` is the top of the moved shift `Y_{Ω_{k+3}}(β)`, which depends on `β`), `vxTe_Om3`;
* `vxY_sub_lt` (**`Y_{Ω₃}(β) < Y_{Ω₃}(β + Ω₃·γ)` at every base `β` of the shift `Ω₃` and every `γ ≥ 1`**: the
  moved shift strictly increases along the transformed sub-bases), `vxY_zero`, `vxY_Om3` (`Y(0) = Y₃ < Y(Ω₃)`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Vx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj Googology.Trans.PoR.InaccPsi.R2.Vn

variable {S : InaccSeq.{0}}

/-- **`Cl(β + a, b) ⊆ Cl(β + Y_κ(β), b)`** for `a ≤ κ = Ω_{s+1}` and `b ≤ Y_κ(β) = ψ_κ(β + κ)`. -/
theorem vxCSet_sub {s β a b : Ordinal.{0}} (haκ : a ≤ Om (s + 1))
    (hbY : b ≤ S.psi (β + Om (s + 1)) (Om (s + 1))) :
    S.CSet (β + a) b ⊆ S.CSet (β + S.psi (β + Om (s + 1)) (Om (s + 1))) b := by
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
    have he : e.1 < β + S.psi (β + Om (s + 1)) (Om (s + 1)) := by
      rcases lt_or_ge e.1 β with h | h
      · exact h.trans_le le_self_add
      · have hsub : e.1 - β ∈ S.CSet (β + Om (s + 1)) (S.psi (β + Om (s + 1)) (Om (s + 1))) :=
          Ta.taSub_mem _ (CSet_mono ((add_le_add_iff_left β).2 haκ) hbY heC) β
        have hlt : e.1 - β < Om (s + 1) :=
          ((Ordinal.sub_lt_of_le h).2 e.2).trans_le haκ
        have h2 := lt_psi_of_mem hκ hsub hlt
        calc e.1 = β + (e.1 - β) := (Ordinal.add_sub_cancel_of_le h).symm
          _ < β + S.psi (β + Om (s + 1)) (Om (s + 1)) := (add_lt_add_iff_left β).2 h2
    exact Clos.coll (e := ⟨e.1, he⟩) hπ ihπ ihe

/-- **`ψ_{Ω₂}(β + a) = ψ_{Ω₂}(β + Y_κ(β))` for every `Y_κ(β) ≤ a ≤ κ`** (`Ω₂ < Y_κ(β)`). -/
theorem vxPsi2_eq {s β a : Ordinal.{0}} (h2 : Om (1 + 1) < S.psi (β + Om (s + 1)) (Om (s + 1)))
    (hYa : S.psi (β + Om (s + 1)) (Om (s + 1)) ≤ a) (haκ : a ≤ Om (s + 1)) :
    S.psi (β + a) (Om (1 + 1)) = S.psi (β + S.psi (β + Om (s + 1)) (Om (s + 1))) (Om (1 + 1)) := by
  have hκ2 : S.InR (Om (1 + 1)) := InR_Om_succ 1
  refine le_antisymm ?_ (psi_mono hκ2 ((add_le_add_iff_left β).2 hYa)).1
  have hbY : S.psi (β + S.psi (β + Om (s + 1)) (Om (s + 1))) (Om (1 + 1)) ≤
      S.psi (β + Om (s + 1)) (Om (s + 1)) := (psi_lt hκ2 _).le.trans h2.le
  exact psi_le_of_good (Mx.mxOm2_mem _ _) fun x hx hx2 =>
    lt_psi_of_mem hκ2 (vxCSet_sub haκ hbY hx) hx2

theorem vxOm2_lt_YK (k : ℕ) (β : Ordinal.{0}) :
    Om (1 + 1 : Ordinal.{0}) < S.psi (β + Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) := by
  have hk2 : (1 + 1 : Ordinal.{0}) ≤ (k : Ordinal.{0}) + 1 + 1 := by gcongr; exact le_add_self
  exact (Om_le_Om.2 hk2).trans_lt (psiS_bounds (S := S) _ ((k : Ordinal.{0}) + 1 + 1)).1

/-- **The top of the shift `Ω_{k+3}` over `β` is the top of the moved shift `Y_{Ω_{k+3}}(β)`**:
`T_{Ω_{k+3}}(β) = ψ₂(β + ψ_{Ω_{k+3}}(β + Ω_{k+3}))`, at every base `β`. -/
theorem vxTe_OmK (k : ℕ) (β : Ordinal.{0}) :
    leTe S (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) β =
      S.psi (β + S.psi (β + Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Om ((k : Ordinal.{0}) + 1 + 1 + 1)))
        (Om (1 + 1)) := by
  unfold leTe
  rw [vnWe_OmK k]
  exact vxPsi2_eq (s := (k : Ordinal.{0}) + 1 + 1) (vxOm2_lt_YK k β)
    (psi_lt (InR_Om_succ _) _).le le_rfl

/-- The case `k = 0`: `T_{Ω₃}(β) = ψ₂(β + ψ₃(β + Ω₃))`. -/
theorem vxTe_Om3 (β : Ordinal.{0}) :
    leTe S (Om (1 + 1 + 1)) β =
      S.psi (β + S.psi (β + Om (1 + 1 + 1)) (Om (1 + 1 + 1))) (Om (1 + 1)) := by
  unfold leTe
  rw [vnWe_Om3]
  exact vxPsi2_eq (s := 1 + 1) (ugOm2_lt_psi3 _) (psi_lt (InR_Om_succ _) _).le le_rfl

/-- At the base `0` the moved shift is `Y_{k+3} = ψ_{Ω_{k+3}}(Ω_{k+3})`. -/
theorem vxY_zero (k : ℕ) :
    S.psi (0 + Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) =
      ujY S ((k : Ordinal.{0}) + 1) := by
  rw [zero_add]; rfl

/-- **The moved shift strictly increases along the transformed sub-bases**: at every base `β` of the shift `Ω₃`
(exponent `0`) and every `γ ≥ 1`, `ψ₃(β + Ω₃) < ψ₃(β + Ω₃·γ + Ω₃)`. -/
theorem vxY_sub_lt {l β γ : Ordinal.{0}} (hb : RoBaseE S l (Om (1 + 1 + 1)) 0 β) (hγ : 1 ≤ γ) :
    S.psi (β + Om (1 + 1 + 1)) (Om (1 + 1 + 1)) <
      S.psi (β + Om (1 + 1 + 1) * γ + Om (1 + 1 + 1)) (Om (1 + 1 + 1)) := by
  have hκ3 : S.InR (Om (1 + 1 + 1)) := InR_Om_succ (1 + 1)
  have h3 : (1 + 1 + 1 : Ordinal.{0}) ≠ 0 := (add_pos_of_right zero_lt_one _).ne'
  obtain ⟨-, -, -, hown, -⟩ := hb
  rw [add_zero, vnWe_Om3] at hown
  have hβ : β ∈ S.CSet (β + Om (1 + 1 + 1)) (S.psi (β + Om (1 + 1 + 1)) (Om (1 + 1))) := hown _ le_rfl
  have hle : β + Om (1 + 1 + 1) ≤ β + Om (1 + 1 + 1) * γ + Om (1 + 1 + 1) := by
    rw [add_assoc β]
    exact (add_le_add_iff_left β).2 le_add_self
  have hlt : β + Om (1 + 1 + 1) < β + Om (1 + 1 + 1) * γ + Om (1 + 1 + 1) := by
    rw [add_assoc β]
    refine (add_lt_add_iff_left β).2 ?_
    calc Om (1 + 1 + 1) < Om (1 + 1 + 1) + Om (1 + 1 + 1) := lt_add_of_pos_right _ (Om_pos h3)
      _ ≤ Om (1 + 1 + 1) * γ + Om (1 + 1 + 1) := by
        gcongr; exact Ordinal.le_mul_left _ (zero_lt_one.trans_le hγ)
  refine psi_lt_psi_of_mem hκ3 hlt (CSet.add_mem ?_ (vnOm3C _ _))
  refine CSet_mono hle ?_ hβ
  exact ((psi_lt (InR_Om_succ 1) _).trans (ugOm2_lt_psi3 _)).le

/-- **`Y(0) = Y₃ < Y(Ω₃) = ψ₃(Ω₃ + Ω₃)`.** -/
theorem vxY_Om3 :
    S.psi (0 + Om (1 + 1 + 1)) (Om (1 + 1 + 1)) = ugY S ∧
      ugY S < S.psi (Om (1 + 1 + 1) + Om (1 + 1 + 1)) (Om (1 + 1 + 1)) := by
  have hκ3 : S.InR (Om (1 + 1 + 1)) := InR_Om_succ (1 + 1)
  have h3 : (1 + 1 + 1 : Ordinal.{0}) ≠ 0 := (add_pos_of_right zero_lt_one _).ne'
  refine ⟨by rw [zero_add]; rfl, ?_⟩
  exact psi_lt_psi_of_mem hκ3 (lt_add_of_pos_right _ (Om_pos h3)) (vnOm3C _ _)

#print axioms vxCSet_sub
#print axioms vxPsi2_eq
#print axioms vxTe_OmK
#print axioms vxTe_Om3
#print axioms vxY_sub_lt
#print axioms vxY_Om3

end Googology.Trans.PoR.InaccPsi.R2.Vx

import Googology.Trans.PoR.InaccPsi.R2.XqBlk

/-!
# The `B_n` move of the image `T` at every wall atom, from the moves of the codes below it

`Θ = gxTh ρ_λ (ldAtR λ)`, `T = Vb.vbT S λ`, `D = Vb.VbD S λ`, `A = A_{η_λ}` (own, `ψ₁(A) = ρ_λ`), `B_n = Bc.bcB S n`,
`c_{n+1} = Bc.bcC S (n + 1)`.  `IH(s)` is the hypothesis of the wall statements (`WallBelow`): every code `x < s`
of `λ` moves (`x ∈ MvD`, `B_n x` a code of `λ'` below `θ⁺`, `Θ x < c_{n+1}`, `Θ'(B_n x) = B_n(Θ x)`).

* `xqN_cl` (**a member of `Cl(Ω_ω, Z)` is normal over `Z`** when `ψ₁(Ω_ω) < Z ≤ Ω₁`);
* `xqTE` (**`T x` is a member over `Θ(ψ₂ a)`** for every `x ∈ D ∩ Cl(a, ψ₂ a)`, `a ∈ D` normal: the countable
  leaves of `T x` are readings of codes below `ψ₂ a`);
* `xqLeaf` (`IH(ψ₂ a)` gives the leaf hypothesis of `Vb.vbT_move` below `Θ(ψ₂ a)`, via `Vb.vbLeaf_of_codes`);
* `xqTMove` (**THE MOVE OF `T`**: under `IH(ψ₂ a)`, `T_{λ'}(B_n x) = B_n(T_λ x)` for every `x ∈ D ∩ Cl(a, ψ₂ a)`, in
  particular for `x = a`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Rx

variable {S : InaccSeq.{0}}

/-- **A member of `Cl(Ω_ω, Z)` is normal over `Z`** when `ψ₁(Ω_ω) < Z ≤ Ω₁`. -/
theorem xqN_cl {Z : Ordinal.{0}} (hZ1 : Z ≤ Om 1) (hZ : S.psi (Om ω) (Om 1) < Z) {y : Ordinal.{0}}
    (hy : y ∈ S.CSet (Om ω) Z) : RxN S Z y := by
  induction hy with
  | small h => exact RxN.small h
  | zero => exact RxN.zero
  | inacc n => exact RxN.inacc n
  | inaccW => exact RxN.inaccW
  | add _ _ ihx ihy => exact RxN.add ihx ihy
  | phi _ _ ihx ihy => exact RxN.phi ihx ihy
  | om _ ih => exact RxN.om ih
  | @coll π e hπ hπC heC ihπ ihe =>
    show RxN S Z (S.psi e.1 π)
    by_cases h1 : π = Om 1
    · subst h1
      exact RxN.small (lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one e.2.le).1 hZ)
    · exact rxN_psi hZ1 e.1 ihe π hπ h1 ihπ

section Rst

variable {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hl hX hA hρ

/-- **`T x` is a member over `Θ(ψ₂ a)`** for every `x ∈ D ∩ Cl(a, ψ₂ a)`. -/
theorem xqTE {a : Ordinal.{0}} : ∀ x, VbD S l x → x ∈ S.CSet a (S.psi a (Om (1 + 1))) →
    RxE S (gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1)))) (vbT S l x) := by
  intro x hx hxC
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  set Z := gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1))) with hZdef
  have hZ1 : Z ≤ Om 1 :=
    (gxTh_mono (psi_lt hκ2 a).le).trans (vbZ2_le hl hX)
  have hZ0 : S.psi (A + 1) (Om 1) ≤ Z := by
    rw [← ldBlk_zero hA hρ]; exact gxTh_mono (psi_mono hκ2 zero_le).1
  have hW : S.psi (Om ω) (Om 1) < Z := by
    refine lt_of_lt_of_le ?_ hZ0
    exact psi_lt_psi_of_mem hκ1 ((Vn.vnA_ge hl hX hA hρ).trans_lt (lt_add_one A)) (ConjT.OmW_mem S _ _)
  have hmem : vbT S l x ∈ S.CSet (Om ω) Z := by
    refine Xd.xdT_cl hl hX (psi_lt hκ2 a).le (fun e he _ => (vbT_mem hl hX he).2)
      (fun c hc hc2 hcC => ?_) x hx hxC
    rw [vbT_code hl hX hc2 hc.1]
    exact CSet.of_lt (gxTh_lt ((ldHull_iff hl hX hc2).1 hc.1) (lt_psi_of_mem hκ2 hcC hc2))
  exact ⟨xqN_cl hZ1 hW hmem, (vbT_mem hl hX hx).1, (vbT_mem hl hX hx).2⟩

end Rst

section Move

variable {n : ℕ} {l l' ηx ηx' A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hl' : IsRestartIdx l') (hX' : upsilon l' < Pv S ηx')
  (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hl hX hl' hX'

/-- **The leaf hypothesis of `Vb.vbT_move` below `Θ(ψ₂ a)`** from the moves of the codes below `ψ₂ a`. -/
theorem xqLeaf {a : Ordinal.{0}}
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi a (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    ∀ g, g < gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1))) →
      MvD S g ∧ MvD S (Ru.ruInv (upsilon l) (ldAtR S l) g) ∧ Bc.bcB S n g < vbW S l' ∧
      Ru.ruInv (upsilon l') (ldAtR S l') (Bc.bcB S n g) = Bc.bcB S n (Ru.ruInv (upsilon l) (ldAtR S l) g) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hTW : gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1))) ≤ vbW S l := by
    rw [vbW_eq hl hX]; exact gxTh_mono (psi_lt hκ2 a).le
  refine vbLeaf_of_codes hl hX hl' hX' hTW fun c hc hc2 hcT => ?_
  have hcs : c < S.psi a (Om (1 + 1)) := by
    by_contra h
    exact absurd hcT (not_lt.2 (gxTh_mono (not_lt.1 h)))
  obtain ⟨hD, hc', hB, hΘ, hmv⟩ := IH c hc hcs
  exact ⟨hD, mvD_of_lt (hΘ.trans (Bc.bcC_lt S (n + 1))), hc', hB.trans Lj.ljThP_lt_Om2, hmv⟩

include hA hρ

/-- **THE MOVE OF `T`** at a wall atom `ψ₂ a` (`a ∈ D` normal): under the moves of the codes below `ψ₂ a`,
`T_{λ'}(B_n x) = B_n(T_λ x)` for every `x ∈ D ∩ Cl(a, ψ₂ a)`. -/
theorem xqTMove {a : Ordinal.{0}}
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi a (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    ∀ x, VbD S l x → x ∈ S.CSet a (S.psi a (Om (1 + 1))) →
      MvD S x ∧ MvD S (vbT S l x) ∧ vbT S l' (Bc.bcB S n x) = Bc.bcB S n (vbT S l x) := by
  intro x hx hxC
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hTW : gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1))) ≤ vbW S l := by
    rw [vbW_eq hl hX]; exact gxTh_mono (psi_lt hκ2 a).le
  have hSC : SC (gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1)))) :=
    gxTh_SC hρSC (ldAt_GxAt _ _) (SC_psi hκ2 a) (hρ1.trans (psiS_bounds (S := S) a 1).1)
  obtain ⟨hD, hDT, -, -, hmv⟩ := vbT_move (n := n) hl hX hl' hX' hSC hTW (xqLeaf hl hX hl' hX' IH) hx
    (xqTE hl hX hA hρ x hx hxC)
  exact ⟨hD, hDT, hmv⟩

end Move

end Googology.Trans.PoR.InaccPsi.R2.Xq

#print axioms Googology.Trans.PoR.InaccPsi.R2.Xq.xqN_cl
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xq.xqTE
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xq.xqLeaf
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xq.xqTMove

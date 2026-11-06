import Googology.Trans.PoR.InaccPsi.R2.ZmPast
import Googology.Trans.PoR.InaccPsi.R2.TzB
import Googology.Trans.PoR.InaccPsi.R2.ZtIso
import Googology.Trans.PoR.InaccPsi.R2.TsPsi
import Googology.Trans.PoR.InaccPsi.R2.TfPsi

/-!
# Zu: every abstract atom system stops at `θ`; the layers past `θ` have no atom system

`θ = ψ_{Ω₂}(Ω_ω) = ConjT.th S`.  An abstract atom system `A : Zb.ZbAS` asks its atoms in EVERY closure `Cl(a, b)` with
`Ω_ω ≤ a` (field `mem`, in particular `a = Ω_ω`), and every code of a hull below its bound `V` to be built from atoms
(field `hull`).

* `zuSC_atom` (**a strongly critical code above `Ω₁` is an atom**: sums and Veblen values of smaller codes are not
  strongly critical);
* `zuV_le_th` (**`A.V ≤ θ` for every atom system `A`**: `θ` is a strongly critical member of `Cl(Ω_ω + 1, Z)`, so
  below `V` it would be an atom, hence in `Cl(Ω_ω, Z) ⊆ Cl(Ω_ω, θ)`, but `θ = ψ_{Ω₂}(Ω_ω)` is not in it);
* `zuPastAt_false` (**`Zm.ZmPastAt S θ` is false**: the layer for the atom index `θ + 1 < Γ(θ+1)` asks
  `Γ(θ+1) ≤ T ≤ V ≤ θ`), `zuLayPastX_false` (**the statement of the skeleton leaf skLayPastX is false**, at the layer
  `c = θ`, `X ≤ θ < Ω₂`);
* `zuGamma_th` (**`Γ_θ = θ`**: `ψ_{Ω₂}(Ω_ω)` is a fixed point of `F_0 = Γ`, `Ts.ts_fwd` with `Ω₂ ∣ Ω_ω`),
  `zuGcG_lt_th` (**`Γ_{Ω₁+1+c} < θ` for `c < θ`**: below `θ` the bound `V ≤ θ` is no obstacle to the layers).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zu

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Zb
  Googology.Trans.PoR.InaccPsi.R2.Mx

/-- **A strongly critical code above `Ω₁` is an atom.** -/
theorem zuSC_atom {Z : Ordinal.{0}} {At : Set Ordinal.{0}} (hZ1 : Z ≤ Om 1) {x : Ordinal.{0}}
    (hx : GxCl Z At x) : SC x → Om 1 < x → x ∈ At := by
  induction hx with
  | small h => intro _ h1; exact absurd (h.trans_le hZ1) (not_lt.2 h1.le)
  | om => intro _ h1; exact absurd h1 (lt_irrefl _)
  | atom hs => intro _ _; exact hs
  | @add x y _ _ ihx ihy =>
    intro hSC h1
    rcases eq_or_ne y 0 with rfl | hy0
    · rw [add_zero] at hSC h1 ⊢; exact ihx hSC h1
    · have hxp : x < x + y := lt_add_of_pos_right x (pos_iff_ne_zero.2 hy0)
      have hy : y = x + y := by
        refine le_antisymm le_add_self (not_lt.1 fun hlt => ?_)
        exact absurd (hSC.isPrincipal hxp hlt) (lt_irrefl _)
      rw [← hy] at hSC h1 ⊢; exact ihy hSC h1
  | @phi x y _ _ ihx ihy =>
    intro hSC h1
    by_cases hxp : x < veblen x y
    · by_cases hyp : y < veblen x y
      · exact absurd (hSC.2 x hxp y hyp) (lt_irrefl _)
      · have hy : y = veblen x y := le_antisymm (right_le_veblen x y) (not_lt.1 hyp)
        rw [← hy] at hSC h1 ⊢; exact ihy hSC h1
    · have hx' : x = veblen x y := le_antisymm (left_le_veblen x y) (not_lt.1 hxp)
      rw [← hx'] at hSC h1 ⊢; exact ihx hSC h1

variable (S : InaccSeq.{0})

/-- **Every abstract atom system stops at `θ`: `A.V ≤ θ`.** -/
theorem zuV_le_th (A : ZbAS) (hA : A.Ok S) : A.V ≤ ConjT.th S := by
  by_contra hlt
  rw [not_le] at hlt
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hZSC : SC (S.psi (Om ω + 1) (Om 1)) := SC_psi hκ1 _
  have hZ1 : S.psi (Om ω + 1) (Om 1) ≤ Om 1 := (psi_lt hκ1 _).le
  have hkey : ∀ y ∈ S.CSet (Om ω + 1) (S.psi (Om ω + 1) (Om 1)), y < Om 1 → y < S.psi (Om ω + 1) (Om 1) :=
    fun y hy hy1 => lt_psi_of_mem hκ1 hy hy1
  have hθmem : ConjT.th S ∈ S.CSet (Om ω + 1) (S.psi (Om ω + 1) (Om 1)) :=
    ConjT.th_mem (S := S) (lt_add_one _)
  have hcl := hA.hull (Om ω + 1) _ hZSC hZ1 hkey _ hθmem hlt
  have hθ1 : Om 1 < ConjT.th S := Zr.zrTh_gt_Om1
  have hat := zuSC_atom hZ1 hcl (ConjT.SC_th S) hθ1
  have hZN : ∀ z < S.psi (Om ω + 1) (Om 1), z ∈ ⋃ e, S.CSet e 0 := fun z hz => by
    have h := Low.lt_psi_one_mem_Vals (S := S) _ z hz
    rw [← Term.vals_eq S]; exact h
  have hm := hA.mem (Om ω) _ _ _ le_rfl hZSC hZ1 le_rfl hZN hat
  have hm2 : ConjT.th S ∈ S.CSet (Om ω) (S.psi (Om ω) (Om (1 + 1))) :=
    CSet_mono le_rfl (hZ1.trans hθ1.le) hm
  have h := lt_psi_of_mem hκ2 hm2 (psi_lt hκ2 _)
  exact lt_irrefl _ h

/-- **`Zm.ZmPastAt S θ` is false.** -/
theorem zuPastAt_false : ¬ Zm.ZmPastAt S (ConjT.th S) := by
  rintro ⟨A, hok, hA⟩
  have hθG : ConjT.th S < gcG (ConjT.th S + 1) :=
    gcG_strictMono.le_apply.trans_lt (gcG_strictMono (lt_add_one _))
  have hB : ConjT.th S + 1 < gcG (ConjT.th S + 1) := (gcG_SC _).isSuccLimit.add_one_lt hθG
  obtain ⟨L, T, hBT, -, hTV, -⟩ := hA _ hB
  have hle : gcG (ConjT.th S + 1) ≤ ConjT.th S := hBT.trans (hTV.trans (zuV_le_th S A hok))
  have h2 : gcG (ConjT.th S + 1) ≤ ConjT.th S := hle
  exact absurd h2 (not_le.2 (((lt_add_one _).trans hB)))

/-- **The statement of the skeleton leaf skLayPastX is false** (at the layer `c = θ`). -/
theorem zuLayPastX_false : ¬ (∀ c, Tl.tlX ≤ c → c < Om (1 + 1) → Zm.ZmPastAt S c) := fun h =>
  zuPastAt_false S (h _ (Tz.tz_X_le_th S) (psi_lt (InR_Om_succ 1) _))

/-- **`Γ_θ = θ`.** -/
theorem zuGamma_th : gamma (ConjT.th S) = ConjT.th S := by
  have hSC : SC (Om (ω : Ordinal.{0})) := SC_Om omega0_ne_zero
  have hOw : ω ^ Om (ω : Ordinal.{0}) = Om ω := Low.opow_eq_self_of_SC hSC
  have hown : Om ω ∈ S.CSet (Om ω) (S.psi (Om ω) (Om (1 + 1))) := ConjT.OmW_mem S _ _
  have hdvd : Le.leWe (0 + 1) ∣ Om ω := by
    unfold Le.leWe
    conv_rhs => rw [← hOw]
    refine opow_dvd_opow ω ?_
    rw [zero_add, mul_one]
    exact Om_le_Om.2 (by rw [one_add_one_eq_two]; exact (natCast_lt_omega0 2).le)
  have h0 : Om (ω : Ordinal.{0}) ≠ 0 := (Om_pos omega0_ne_zero).ne'
  have hpos : (0 : Ordinal.{0}) < S.psi (Om ω) (Om (1 + 1)) := (ConjT.SC_th S).1
  have h := Ts.ts_fwd (S := S) 0 (Om ω) hown hdvd h0 hpos
  rw [Rh.rhF_zero] at h
  exact h

/-- **`Γ_{Ω₁+1+c} < θ` for every `c < θ`.** -/
theorem zuGcG_lt_th {c : Ordinal.{0}} (hc : c < ConjT.th S) : gcG c < ConjT.th S := by
  rw [Tf.tf_gcG]
  have hSC := ConjT.SC_th S
  have h1 : Om1 + 1 < ConjT.th S := by
    have hθ1 : Om 1 < ConjT.th S := Zr.zrTh_gt_Om1
    rw [← Br.Om1_eq] at hθ1
    exact hSC.isSuccLimit.add_one_lt hθ1
  have h2 : Om1 + 1 + c < ConjT.th S := hSC.isPrincipal h1 hc
  calc gamma (Om1 + 1 + c) < gamma (ConjT.th S) := gamma_lt_gamma.2 h2
    _ = ConjT.th S := zuGamma_th S

end Googology.Trans.PoR.InaccPsi.R2.Zu

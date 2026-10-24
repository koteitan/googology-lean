import Googology.Trans.PoR.InaccPsi.R2.ThCnt

/-!
# Where the level-shift lift stops below `P'`: the offset `M_W = ψ_{Ω₂}(Ω_ω + Ω₂)`

The lower bound `ThLow` covers `ψ_{Ω₁}(A + ζ)` by the atoms `ψ_{Ω₂}(Ω_ω + θ₂·x + κ w)` of a restart,
`κ` the level shift (`Ω_k ↦ Ω_{k+1}`, `ψ_{Ω_{k+1}}(e) ↦ ψ_{Ω_{k+2}}(κ e)`), for offsets `ζ = θ·x + w`, `x < ρ_λ`,
`w < θ`.  To reach `Θ_λ(P') ≥ ψ_{Ω₁}(A + P') = L(k+1)` every offset `ζ < P'` of the hull
`Cl(A + P', Θ_λ(P'))` must be covered, and for `ζ ≥ M_W` the tails contain `M_W` (`thMW_mem`: `M_W` lies in
every `Cl(a, b)` with `a > Ω_ω + Ω₂`, so in the hull of `ψ_{Ω₁}(A + ζ)` as soon as `M_W < ζ`), whose natural
lift is `ψ_{Ω₃}(Ω_ω + Ω₃)`.

* `thMW_mem`, `thMW_lt_Pp` (`M_W ∈ Cl(a, b)` for `a > Ω_ω + Ω₂`; `θ < M_W < P'`);
* `thObst` (**THE OBSTRUCTION**): `ψ_{Ω₃}(Ω_ω + Ω₃) ∉ Cl(Ω_ω + d, ψ_{Ω₂}(Ω_ω + d))` for every `d < Ω₃`.  The
  atoms of the lift have `d = κ ζ < Ω₃` (offsets `ζ < Ω₂`), so the TRANSFER step of the lift lemma
  (`Rx.rxLift`, hypothesis `hcl`) fails at every offset whose tails contain `M_W`: an atom above the base
  `Ω_ω + Ω₃` (a second block) is needed, i.e. a lift that moves the levels inside the arguments `Ω_ω + c`,
  `c ≥ Ω₂`, of the offsets.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Th

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2

variable {S : InaccSeq.{0}}

/-- `Ω_ω + Ω₂` lies in every hull. -/
theorem thWO2_mem (a b : Ordinal.{0}) : Om ω + Om (1 + 1) ∈ S.CSet a b :=
  CSet.add_mem (ConjT.OmW_mem S a b) (Mx.mxOm2_mem a b)

/-- **`M_W = ψ_{Ω₂}(Ω_ω + Ω₂)` lies in every `Cl(a, b)` with `a > Ω_ω + Ω₂`.** -/
theorem thMW_mem {a b : Ordinal.{0}} (ha : Om ω + Om (1 + 1) < a) :
    S.psi (Om ω + Om (1 + 1)) (Om (1 + 1)) ∈ S.CSet a b :=
  CSet.psi_mem ha (InR_Om_succ 1) (Mx.mxOm2_mem a b) (thWO2_mem a b)

/-- **`θ < M_W < P'`.** -/
theorem thMW_lt_Pp :
    ConjT.th S < S.psi (Om ω + Om (1 + 1)) (Om (1 + 1)) ∧
      S.psi (Om ω + Om (1 + 1)) (Om (1 + 1)) < Nc.ncPp S := by
  have hS : SC (Om (ω : Ordinal.{0})) := SC_Om omega0_ne_zero
  have h2W : Om (1 + 1 : Ordinal.{0}) < Om ω := Om_lt_Om.2 (by
    rw [one_add_one_eq_two]; exact_mod_cast natCast_lt_omega0 2)
  refine ⟨?_, ?_⟩
  · exact psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right _ (Om_pos (by simp)))
      (ConjT.OmW_mem S _ _)
  · exact psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left _).2 h2W) (thWO2_mem _ _)

/-- **THE OBSTRUCTION**: `ψ_{Ω₃}(Ω_ω + Ω₃) ∉ Cl(Ω_ω + d, ψ_{Ω₂}(Ω_ω + d))` for every `d < Ω₃`. -/
theorem thObst {d : Ordinal.{0}} (hd : d < Om (1 + 1 + 1)) :
    S.psi (Om ω + Om (1 + 1 + 1)) (Om (1 + 1 + 1)) ∉
      S.CSet (Om ω + d) (S.psi (Om ω + d) (Om (1 + 1))) := by
  intro h
  have hκ : S.InR (Om (1 + 1 + 1)) := InR_Om_succ (1 + 1)
  have hb : S.psi (Om ω + d) (Om (1 + 1)) ≤ S.psi (Om ω + Om (1 + 1 + 1)) (Om (1 + 1 + 1)) :=
    ((psi_lt (InR_Om_succ 1) _).trans (psiS_bounds (S := S) _ (1 + 1)).1).le
  have hbL : S.psi (Om ω + d) (Om (1 + 1)) ≤ S.Lam :=
    ((psi_lt (InR_Om_succ 1) _).trans (lt_Lam_of_mem zero_le (Mx.mxOm2_mem (S := S) 0 0))).le
  have h3 : ∀ a b : Ordinal.{0}, Om (1 + 1 + 1 : Ordinal.{0}) ∈ S.CSet a b := fun a b =>
    CSet.Om_mem (CSet.succ_mem (CSet.succ_mem (CSet.one_mem a b)))
  have hdn : Om ω + Om (1 + 1 + 1) ∈
      S.CSet (Om ω + Om (1 + 1 + 1)) (S.psi (Om ω + Om (1 + 1 + 1)) (Om (1 + 1 + 1))) :=
    CSet.add_mem (ConjT.OmW_mem S _ _) (h3 _ _)
  have hlt := (arg_mem_of_psi_mem hκ h hb hbL hdn).2
  exact absurd ((add_lt_add_iff_left _).1 hlt) (not_lt.2 hd.le)

end Googology.Trans.PoR.InaccPsi.R2.Th

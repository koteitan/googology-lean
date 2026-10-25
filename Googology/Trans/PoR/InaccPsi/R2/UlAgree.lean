import Googology.Trans.PoR.InaccPsi.R2.UlArgs
import Googology.Trans.PoR.InaccPsi.R2.UfB

/-!
# `uiDat` and `ucDat` give the same code test below `B₂` at every `Ω_ω`-closed point

`B₂ = Uc.ucB = ψ_{Ω₂}(ε_{Ω₂+1})`, `θ = ConjT.th S = ψ_{Ω₂}(Ω_ω)`, `UcCl q` the codes over `q` below `B₂` (data
`Uc.ucDat`, read on Veblen normal forms and the atoms `H_λ(y)`, `R2.UcCl`), `Ui.uiDat` the data read on the normal
forms of the notation (subscripts included, `R2.UiCode`).  A point `q ≤ Ω₁` is `Ω_ω`-closed when `Cl(Ω_ω, q) ∩ Ω₁ ⊆
q` (every collapse with an argument below `Ω_ω` and leaves below `q` stays below `q`).

* `ul_B_lt_th` (**`B₂ < θ`**);
* `ul_agree_cl` (**for `z < B₂` of the notation and a strongly critical `Ω_ω`-closed `q ≤ Ω₁`: `UcCl q z ↔ uiDat z <
  q`**: a code over `q` lies in `Cl(Ω_ω, q)` by the hull converse `Uf.uf_mem_CSet` (`TwArgs` at `Ω_ω ≥ E₂`,
  `Uf.uf_args_E`), a member of `Cl(Ω_ω, q)` below `B₂` is a code by the direct hull lemma `Uf.uf_diglev`, and
  `Ui.ui_code_th` decides `Cl(Ω_ω, q)` below `θ`);
* `ul_agree_dat` (**the same with `ucDat z < q`**), `ul_agree_datL` (**for the data of a level `μ`, `Ω₁ + μ < B₂` of
  the notation: `ucDatL μ < q ↔ uiDat(Ω₁ + μ) < q`**).

The restriction to `Ω_ω`-closed `q` comes from the hulls: `Cl(A, q)` contains the collapses `ψ_{Ω₁}(e)`, `e < A`, as
soon as it contains the atoms `ψ_{Ω₂}(e)`, `e < A`.  No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ul

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Uc

variable {S : InaccSeq.{0}}

/-- **`B₂ < θ = ψ_{Ω₂}(Ω_ω)`.** -/
theorem ul_B_lt_th : (ucB : Ordinal.{0}) < ConjT.th S := by
  rw [← uc_psiE_eq_B (S := S)]
  unfold ConjT.th
  exact psi_lt_psi_of_mem (InR_Om_succ 1) Uf.uf_E_lt_Omw (uc_E_mem _ _)

/-- **For `z < B₂` of the notation and a strongly critical `Ω_ω`-closed `q ≤ Ω₁`: `UcCl q z ↔ uiDat z < q`.** -/
theorem ul_agree_cl {q z : Ordinal.{0}} (hz : z ∈ ⋃ a, S.CSet a 0) (hzB : z < ucB) (hq : SC q) (hq1 : q ≤ Om1)
    (hcl : ∀ y ∈ S.CSet (Om ω) q, y < Om 1 → y < q) : UcCl q z ↔ Ui.uiDat S z < q := by
  have hq1' : q ≤ Om 1 := by rw [← Rj.rj_Om1]; exact hq1
  have hth := Ui.ui_code_th hz (hzB.trans ul_B_lt_th) le_rfl hq1' hcl hq.1
  constructor
  · intro h
    have hE : ucE ≤ (Om ω : Ordinal.{0}) := Uf.uf_E_lt_Omw.le
    exact hth.1 ((Uf.uf_mem_CSet (S := S) (a := Om ω) hq hq1 le_rfl z h (Uf.uf_args_E hE hzB)).1)
  · intro h
    have hmem := hth.2 h
    have hcoll : ∀ e, e < Om ω → e ∈ S.CSet (Om ω) q → Ri.RiDg q e → Uf.UfLev q e → S.psi e (Om 1) < q :=
      fun e he heC _ _ => hcl _ (CSet.psi_mem he Low.InR_Om_one (CSet.Om_mem (CSet.one_mem _ _)) heC)
        (psi_lt Low.InR_Om_one e)
    exact (Uf.uf_diglev hq hq1' hcoll z hmem).2.2.1 hzB

/-- **The same with the data**: `ucDat z < q ↔ uiDat z < q`. -/
theorem ul_agree_dat {q z : Ordinal.{0}} (hz : z ∈ ⋃ a, S.CSet a 0) (hzB : z < ucB) (hq : SC q) (hq1 : q ≤ Om1)
    (hcl : ∀ y ∈ S.CSet (Om ω) q, y < Om 1 → y < q) : ucDat z < q ↔ Ui.uiDat S z < q := by
  rw [← uc_cl_iff hq hzB]; exact ul_agree_cl hz hzB hq hq1 hcl

/-- **The data of a level**: `ucDatL μ < q ↔ uiDat(Ω₁ + μ) < q` for `Ω₁ + μ < B₂` of the notation. -/
theorem ul_agree_datL {q μ : Ordinal.{0}} (hz : Om1 + μ ∈ ⋃ a, S.CSet a 0) (hzB : Om1 + μ < ucB) (hq : SC q)
    (hq1 : q ≤ Om1) (hcl : ∀ y ∈ S.CSet (Om ω) q, y < Om 1 → y < q) :
    ucDatL μ < q ↔ Ui.uiDat S (Om1 + μ) < q := ul_agree_dat hz hzB hq hq1 hcl

end Googology.Trans.PoR.InaccPsi.R2.Ul

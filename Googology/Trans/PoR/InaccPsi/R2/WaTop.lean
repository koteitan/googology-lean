import Googology.Trans.PoR.InaccPsi.R2.VwRoad
import Googology.Trans.PoR.InaccPsi.R2.UxRoad
import Googology.Trans.PoR.InaccPsi.R2.ShNu
import Googology.Trans.PoR.InaccPsi.R2.SeLow
import Googology.Trans.PoR.InaccPsi.R2.TpTC
import Googology.Trans.PoR.InaccPsi.R2.TpEQ
import Googology.Trans.PoR.InaccPsi.R2.SfRst
import Googology.Trans.PoR.InaccPsi.R2.MvK
import Googology.Trans.PoR.InaccPsi.R2.MvGg
import Googology.Trans.PoR.InaccPsi.R2.MwGam
import Googology.Trans.PoR.InaccPsi.R2.MwOm
import Googology.Trans.PoR.InaccPsi.R2.MxGam
import Googology.Trans.PoR.InaccPsi.R2.MxRead
import Googology.Trans.PoR.InaccPsi.R2.MxLayB
import Googology.Trans.PoR.InaccPsi.R2.LdBlkW
import Googology.Trans.PoR.InaccPsi.R2.LdEQ
import Googology.Trans.PoR.InaccPsi.R2.LdG2b
import Googology.Trans.PoR.InaccPsi.R2.LeMove
import Googology.Trans.PoR.InaccPsi.R2.LeEMove
import Googology.Trans.PoR.InaccPsi.R2.LjRoad
import Googology.Trans.PoR.InaccPsi.R2.RnEQ
import Googology.Trans.PoR.InaccPsi.R2.RnT1
import Googology.Trans.PoR.InaccPsi.R2.RoO
import Googology.Trans.PoR.InaccPsi.R2.RqSup
import Googology.Trans.PoR.InaccPsi.R2.RwAt2
import Googology.Trans.PoR.InaccPsi.R2.RwWW
import Googology.Trans.PoR.InaccPsi.R2.UdRoad
import Googology.Trans.PoR.InaccPsi.R2.VjTop
import Googology.Trans.PoR.InaccPsi.R2.VmTop
import Googology.Trans.PoR.InaccPsi.R2.VsTop
import Googology.Trans.PoR.InaccPsi.R2.VpOwn

/-!
# The three top-window hypotheses of `Vw.vwRoad`

`L(ξ) = Nc.ncL S ξ`, `c_n = L(n+1)`, `B_n = Bc.bcB S n`, `ν_C = nuC`.

* `waStdMoveTop` (**`Cx.CxStdMoveTop S`, unconditional**): the shift `Sf.sfShiftAll` through `Tp.tpStdMoveTop`;
* `waLhMove` (**`Tp.TpLhMove S`, unconditional**): `Vs.vsPiLev` and `Vp.vmAtomMove` give
  `SvUncAllFrom S B₂` (`Vm.vmUncFrom`), hence `Tp.TpLhEps S` (`Vj.vjLhEps`) and `TpLhMove`;
* `waTCtopOff` (**`L(ω+1) ≤ ν_C` gives `Cx.CxTCtopOff S`**, no (CL)): a restart strictly inside
  `(L(n+1), L(n+2))` is a range restart (`Se.seRange_mid`), so a point excluded from the range restarts is no restart
  at all; then `Tp.tpTC_ups` / `Tp.tpTC_off`;
* `waEQtop_iff` (**under `L(ω+1) ≤ ν_C`: `Cx.CxEQtop S ↔ Sf.SfEQlong S`**), `waEQtop_of_EQ` (**`CdEQ` gives
  `CxEQtop`**), `waEQtop_lj` (**`LjAtMove`, `RnThMoveM`, `RnEQhi2` give `CxEQtop`** under `L(ω+1) ≤ ν_C`),
  `waLjAt_of_ux` (**`UxAtMove26` gives `LjAtMove`**), `waEQtop_ux`.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wa

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **`CxStdMoveTop` holds** (from the proved shift). -/
theorem waStdMoveTop : Cx.CxStdMoveTop S := Tp.tpStdMoveTop Sf.sfShiftAll

/-- **The `R₁⁺`-reach moves with `B_n`** at every non-`υ`-point of the windows, unconditionally. -/
theorem waLhMove : Tp.TpLhMove S :=
  Tp.tpLhMove_of_prin (Tp.tpLhPrin_of_eps (Vj.vjLhEps (Vm.vmUncFrom Vs.vsPiLev Vp.vmAtomMove)))

/-- **`CxTCtopOff` from `L(ω+1) ≤ ν_C` alone.** -/
theorem waTCtopOff (hν : Nc.ncL S (ω + 1) ≤ nuC) : Cx.CxTCtopOff S := by
  intro n x h1 h2 hnr
  by_cases hU : UpsPt x
  · refine Tp.tpTC_ups hν Sf.sfShiftAll h1 h2 hU fun l hl he => hnr l ?_ he
    exact Se.seRange_mid hl (he ▸ h1) (he ▸ h2)
  · exact Tp.tpTC_off hν Sf.sfShiftAll waLhMove h1 h2 hU

/-- **`CdEQ` gives `CxEQtop`** (`ρ_λ ≤ r(λ)`). -/
theorem waEQtop_of_EQ (h : CdEQ S) : Cx.CxEQtop S := fun n l hl h1 hr =>
  h n l hl (h1.le.trans (Tp.tpRho_le_R l)) hr

/-- **`CxEQtop` gives `Tp.TpEQall`** (the restart `λ'` with `B_n ρ_λ = ρ_{λ'}` is unique). -/
theorem waEQall_of_top (h : Cx.CxEQtop S) : Tp.TpEQall S := by
  intro n l l' hl h1 hr _ hB
  obtain ⟨l'', -, e1, e2⟩ := h n l hl h1 hr
  have : l'' = l' := Tp.tpUps_inj (e1.symm.trans hB)
  subst this
  exact e2

/-- **Under `L(ω+1) ≤ ν_C`: `CxEQtop ↔ SfEQlong`** (the short codes are `Mv.mvKMove`). -/
theorem waEQtop_iff (hν : Nc.ncL S (ω + 1) ≤ nuC) : Cx.CxEQtop S ↔ Sf.SfEQlong S := by
  constructor
  · intro h n l l' hl h1 hr hl' hB _
    exact waEQall_of_top h n l l' hl h1 hr hl' hB
  · intro h
    exact Tp.tpEQtop Sf.sfRstMove (Sf.sfEQall (Mv.mvKMove hν) h)

/-- **`CxEQtop` from the atom move `LjAtMove`, `RnThMoveM` and `RnEQhi2`** (given `L(ω+1) ≤ ν_C`). -/
theorem waEQtop_lj (hν : Nc.ncL S (ω + 1) ≤ nuC) (hat : Lj.LjAtMove S) (hM : Rn.RnThMoveM S)
    (hE : Rn.RnEQhi2 S) : Cx.CxEQtop S := by
  have hR : Ld.LdThMoveR S :=
    Ld.ldThMoveR_of_S (Le.leThMoveS_of_T (Le.leThMoveT_of_U (Lj.ljLeThMoveU_of_at hat)))
  have hhi : Ld.LdEQhi S :=
    Lj.ljLdEQhi_of_Q hν (Lj.ljThMoveQ_of_at hat) (Rn.rnLjEQhi_of hν hM hE)
  have hth : Mx.MxEQth S := Ld.ldEQth_of_R hν hR hhi
  have hmv : Mx.MxThMove S := Mx.mxThMove_of_W (Ld.ldThMoveW_of_Q (Ld.ldThMoveQ_of_R hR))
  have htop : Mx.MxEQtop S := Mx.mxEQtop_read hν hmv hth
  exact (waEQtop_iff hν).2
    (Mv.mvEQlong_top hν (Mw.mwEQtop_mv hν (Mx.mxEQtop_mw hν htop)))

/-- **`UxAtMove26` gives `LjAtMove`** (the chain of the atom-move reductions). -/
theorem waLjAt_of_ux (h : Ux.UxAtMove26 S) : Lj.LjAtMove S :=
  Rn.rnLjAtMove2 (Ro.roAtMove2_of4 (Rq.rqAtMove4_of6 (Rw.rwAtMove6_of9
    (Rw.rwAtMove9_of10 (Ud.udAtMove10_of25 (Ux.uxAtMove25_of26 h))))))

/-- **`CxEQtop` from `UxAtMove26`, `RnThMoveM`, `RnEQhi2`** (given `L(ω+1) ≤ ν_C`). -/
theorem waEQtop_ux (hν : Nc.ncL S (ω + 1) ≤ nuC) (hat : Ux.UxAtMove26 S) (hM : Rn.RnThMoveM S)
    (hE : Rn.RnEQhi2 S) : Cx.CxEQtop S :=
  waEQtop_lj hν (waLjAt_of_ux hat) hM hE

end Googology.Trans.PoR.InaccPsi.R2.Wa

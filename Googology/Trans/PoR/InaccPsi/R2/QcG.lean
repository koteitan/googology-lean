import Googology.Trans.PoR.InaccPsi.R2.QcR

/-!
# QcG: THE GATES OF THE CODES BELOW `B₂`, AND THE READINGS OF AN INDEX AND OF A BASE

`Yr.yrG` is the gate of a code below `X` (the gates of the infinite parts of its clauses); `Va.vI`, `Va.vK`, `Va.vA`
read an atom index, the index of a fixed point of `F_λ`, and an `ε`-number code as a base.  The same from `X` on, with
the clause of a fixed point `H_λ(y)` of `Γ` of `Qc.vQ`: the gates of the infinite components of `λ` and of the parts of
the index `c` (`p` and `d` past the largest fixed point `p < y` of `H_λ`, `y = p + 1 + d`; else `y`).

* `qcG` (**the gate**: `Yr.yrG` below `X`), `qcQ` (`0` at a finite part), `qcQE` (the gate of a base), `qcI` (the
  reading of an atom index), `qcK` (the reading of the index of a fixed point of `H_λ`), `qcLvx` (the level reading
  at `x`), `qcA` (**the reading of an `ε`-number code as a base**);
* `qcG_low`, `qcQE_low`, `qcA_low` (**`Yr.yrG`, `Yr.yrQE`, `Va.vA` below `X`**).

No new axiom.  New definitions: `qcG`, `qcQ`, `qcQE`, `qcI`, `qcK`, `qcLvx`, `qcA`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi
  Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Yh
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Uc
  Googology.Trans.PoR.InaccPsi.R2.Va Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.Xu Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Yw

open Classical in
/-- **The gate of a code below `B₂`**: `Yr.yrG` below `X`; from `X` on the gates of the infinite parts of the clauses of
`Qc.vQ`. -/
noncomputable def qcG (c : Ordinal.{0}) : Ordinal.{0} :=
  if hX : tlX ≤ c ∧ c < ucB then
    max (max (if hA : YhAt (guE c) then
          (if hi : yhJ (guE c) < guE c then (if yhJ (guE c) < ω then 0 else qcG (yhJ (guE c)))
            else if hN : ucI (ucLev (guE c)) (guE c) < guE c then
              max (ucFold (fun d => if hd : d < guE c then (if d < ω then 0 else qcG d) else 0) (ucLev (guE c)))
                (if QcFixH (ucLev (guE c)) (ucI (ucLev (guE c)) (guE c)) then
                  max (if qcFpH (ucLev (guE c)) (ucI (ucLev (guE c)) (guE c)) < ω then 0
                      else qcG (qcFpH (ucLev (guE c)) (ucI (ucLev (guE c)) (guE c))))
                    (if ucI (ucLev (guE c)) (guE c) -
                        (qcFpH (ucLev (guE c)) (ucI (ucLev (guE c)) (guE c)) + 1) < ω then 0
                      else qcG (ucI (ucLev (guE c)) (guE c) -
                        (qcFpH (ucLev (guE c)) (ucI (ucLev (guE c)) (guE c)) + 1)))
                 else (if ucI (ucLev (guE c)) (guE c) < ω then 0 else qcG (ucI (ucLev (guE c)) (guE c))))
            else 0) else
          max (if yhK (guE c) < ω then 0 else qcG (yhK (guE c)))
            (if yhI (guE c) < ω then 0 else qcG (yhI (guE c))))
        (if log (guE c) c < ω then 0 else qcG (log (guE c) c)))
      (max (if c / guE c ^ log (guE c) c < ω then 0 else qcG (c / guE c ^ log (guE c) c))
        (qcG (c % guE c ^ log (guE c) c)))
  else yrG c
termination_by c
decreasing_by
  all_goals first
    | exact yr_ix_lt (qc_X_G0.trans hX.1) hi
    | exact hd.trans_le (gl_E_le (yh_gfE_le (qc_X_G0.trans hX.1)))
    | exact (qc_fpH_le _ _).trans_lt (hN.trans_le (gl_E_le (yh_gfE_le (qc_X_G0.trans hX.1))))
    | exact (Ordinal.sub_le_self _ _).trans_lt (hN.trans_le (gl_E_le (yh_gfE_le (qc_X_G0.trans hX.1))))
    | exact hN.trans_le (gl_E_le (yh_gfE_le (qc_X_G0.trans hX.1)))
    | exact yh_lev_lt (qc_X_G0.trans hX.1) hA
    | exact yh_idx_lt (qc_X_G0.trans hX.1) hA
    | exact (gl_parts (yh_gfE_le (qc_X_G0.trans hX.1))).2.2.2.2.2.1
    | exact (gl_parts (yh_gfE_le (qc_X_G0.trans hX.1))).2.2.2.2.2.2.2
    | exact (gl_parts (yh_gfE_le (qc_X_G0.trans hX.1))).2.2.2.2.2.2.1

theorem qcG_low {c : Ordinal.{0}} (h : c < tlX) : qcG c = yrG c := by
  rw [qcG, dif_neg (fun hX => absurd hX.1 (not_le.2 h))]

/-- **The gate of a part**: `0` when finite. -/
noncomputable def qcQ (a : Ordinal.{0}) : Ordinal.{0} := if a < ω then 0 else qcG a

/-- **The level reading at `x`**: `qcLv` with every component `d < e` read `vQ d x`. -/
noncomputable def qcLvx (e l x : Ordinal.{0}) : Ordinal.{0} :=
  qcLv (fun d => if d < e then vQ d x else 0) l

open Classical in
/-- **The reading of an atom index**: `F(x) + (j − (F+1))(x)` past the largest fixed point `F < j` of `Γ`, `j(x)`
below the first. -/
noncomputable def qcI (j x : Ordinal.{0}) : Ordinal.{0} :=
  if VaFixG j then vQ (vaFpG j) x + vQ (j - (vaFpG j + 1)) x else vQ j x

open Classical in
/-- **The reading of the index of a fixed point of `H_λ`**: `p(x) + (y − (p+1))(x)` past the largest fixed point
`p < y` of `H_λ`, `y(x)` below the first. -/
noncomputable def qcK (l y x : Ordinal.{0}) : Ordinal.{0} :=
  if QcFixH l y then vQ (qcFpH l y) x + vQ (y - (qcFpH l y + 1)) x else vQ y x

open Classical in
/-- **The gate of an `ε`-number code as a base** (`Yr.yrQE` below `X`). -/
noncomputable def qcQE (e : Ordinal.{0}) : Ordinal.{0} :=
  if tlX ≤ e ∧ e < ucB then
    (if YhAt e then (if yhJ e < e then qcQ (yhJ e)
      else if ucI (ucLev e) e < e then
        max (ucFold (fun d => if d < e then qcQ d else 0) (ucLev e))
          (if QcFixH (ucLev e) (ucI (ucLev e) e) then
            max (qcQ (qcFpH (ucLev e) (ucI (ucLev e) e))) (qcQ (ucI (ucLev e) e - (qcFpH (ucLev e) (ucI (ucLev e) e) + 1)))
          else qcQ (ucI (ucLev e) e))
      else 0)
    else max (qcQ (yhK e)) (qcQ (yhI e)))
  else yrQE e

theorem qcQE_low {e : Ordinal.{0}} (h : e < tlX) : qcQE e = yrQE e := by
  unfold qcQE; rw [if_neg (fun hX => absurd hX.1 (not_le.2 h))]

open Classical in
/-- **The reading of an `ε`-number code as a base** (`Va.vA` below `X`). -/
noncomputable def qcA (e x : Ordinal.{0}) : Ordinal.{0} :=
  if tlX ≤ e ∧ e < ucB then
    (if YhAt e then (if yhJ e < e then gq (qcI (yhJ e) x) x else
        (if ucI (ucLev e) e < e then vt x (Om1 * (Om1 + qcLvx e (ucLev e) x) + qcK (ucLev e) (ucI (ucLev e) e) x)
          else 0))
      else glA (vQ (yhK e) x) (vQ (yhI e) x) x)
  else vA e x

theorem qcA_low {e : Ordinal.{0}} (h : e < tlX) (x : Ordinal.{0}) : qcA e x = vA e x := by
  unfold qcA; rw [if_neg (fun hX => absurd hX.1 (not_le.2 h))]

end Googology.Trans.PoR.InaccPsi.R2.Qc

import Googology.Trans.PoR.InaccPsi.R2.QdDat

/-!
# QdR: ONE READING OF EVERY CODE BELOW `B₃` — `Qc.vQ` BELOW `B₂`, THE VEBLEN LEVELS OF `Hᵛ` FROM `B₂` ON

`B₂ = Uc.ucB`, `B₃ = Qd.qdB`, `Hᵛ_γ = Qd.qdH γ` (`γ < Γ_{Ω₂+1}`), a strongly critical `z ∈ (Ω₁, B₃)` is
`Hᵛ_λ(y)` with `λ = qdLev z`, `y = qdI λ z < z` (`Qd.qd_nf`).  `Qc.vQ` reads every code below `B₂`.  Here `vD`
extends it to `[B₂, B₃)` by the clauses of `Qc.vQ` from `X` on, with the level `λ = qdLev e` of a fixed point `e` of
`Γ` read by the Veblen level map `Qd.qdLv` (`Ω₂ ↦ Ω₁`, the `φ` and Cantor clauses kept, every leaf `d < Ω₂` read
`d(x)`): `e = Hᵛ_λ(y)` reads

  `ϑˣ(Ω₁·(Ω₁ + λ(x)) + c(x))`,

`c` the index of `y` among the non-fixed arguments of `Hᵛ_λ` (`p + d` for `y = p + 1 + d` past the largest fixed point
`p < y` of `Hᵛ_λ`, else `y`).  The gates, the readings of an atom index and of an index, and the base data are the
clauses of `Qc.qcG`, `Qc.qcI`, `Qc.qcK`, `Qc.qcQE`, `Qc.qcA` with the same change.

* `QdFixH`, `qdFpH` (the largest fixed point of `Hᵛ_λ` below `y`), `vD`, `qdGt` (the gate), `qdQt`, `qdLvx`,
  `qdRI`, `qdRK`, `qdQEt`, `qdA`;
* `vD_low` (**`vD = vQ` below `B₂`**), `qdGt_low`, `qdQEt_low`, `qdA_low`.

No new axiom.  New definitions: `QdFixH`, `qdFpH`, `vD`, `qdGt`, `qdQt`, `qdLvx`, `qdRI`, `qdRK`, `qdQEt`, `qdA`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qd

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi
  Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Yh
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Uc
  Googology.Trans.PoR.InaccPsi.R2.Va Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.Xu Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Yw
  Googology.Trans.PoR.InaccPsi.R2.Qc

/-- A fixed point of `Hᵛ_λ` below `y`. -/
def QdFixH (l y : Ordinal.{0}) : Prop := ∃ f, qdH l f = f ∧ f < y

/-- **The largest fixed point of `Hᵛ_λ` below `y`** (`sSup`). -/
noncomputable def qdFpH (l y : Ordinal.{0}) : Ordinal.{0} := sSup {f | qdH l f = f ∧ f < y}

theorem qd_fpH_le (l y : Ordinal.{0}) : qdFpH l y ≤ y := csSup_le' fun _ hf => hf.2.le

theorem qd_B2_G0 : gcG 0 ≤ (ucB : Ordinal.{0}) := qc_X_G0.trans uc_X_lt_B.le

open Classical in
/-- **The reading of every code below `B₃`**: `Qc.vQ` below `B₂`; from `B₂` on the clauses of `Qc.vQ`, with a fixed
point `Hᵛ_λ(y)` of `Γ` read `ϑˣ(Ω₁·(Ω₁ + λ(x)) + c(x))`. -/
noncomputable def vD (c x : Ordinal.{0}) : Ordinal.{0} :=
  if hX : ucB ≤ c ∧ c < qdB then
    (if hA : YhAt (guE c) then (if hi : yhJ (guE c) < guE c then
        gq (if VaFixG (yhJ (guE c)) then vD (vaFpG (yhJ (guE c))) x +
            vD (yhJ (guE c) - (vaFpG (yhJ (guE c)) + 1)) x
          else vD (yhJ (guE c)) x) x
        else (if hN : qdI (qdLev (guE c)) (guE c) < guE c then
          vt x (Om1 * (Om1 + qdLv (fun d => if hd : d < guE c then vD d x else 0) (qdLev (guE c))) +
            (if QdFixH (qdLev (guE c)) (qdI (qdLev (guE c)) (guE c)) then
              vD (qdFpH (qdLev (guE c)) (qdI (qdLev (guE c)) (guE c))) x +
              vD (qdI (qdLev (guE c)) (guE c) - (qdFpH (qdLev (guE c)) (qdI (qdLev (guE c)) (guE c)) + 1)) x
            else vD (qdI (qdLev (guE c)) (guE c)) x))
          else 0))
      else glA (vD (yhK (guE c)) x) (vD (yhI (guE c)) x) x) ^ vD (log (guE c) c) x *
      vD (c / guE c ^ log (guE c) c) x + vD (c % guE c ^ log (guE c) c) x
  else vQ c x
termination_by c
decreasing_by
  all_goals first
    | exact yr_ix_lt (qd_B2_G0.trans hX.1) hi
    | exact (va_fpG_le _).trans_lt (yr_ix_lt (qd_B2_G0.trans hX.1) hi)
    | exact (Ordinal.sub_le_self _ _).trans_lt (yr_ix_lt (qd_B2_G0.trans hX.1) hi)
    | exact hd.trans_le (gl_E_le (yh_gfE_le (qd_B2_G0.trans hX.1)))
    | exact (qd_fpH_le _ _).trans_lt (hN.trans_le (gl_E_le (yh_gfE_le (qd_B2_G0.trans hX.1))))
    | exact (Ordinal.sub_le_self _ _).trans_lt (hN.trans_le (gl_E_le (yh_gfE_le (qd_B2_G0.trans hX.1))))
    | exact hN.trans_le (gl_E_le (yh_gfE_le (qd_B2_G0.trans hX.1)))
    | exact yh_lev_lt (qd_B2_G0.trans hX.1) hA
    | exact yh_idx_lt (qd_B2_G0.trans hX.1) hA
    | exact (gl_parts (yh_gfE_le (qd_B2_G0.trans hX.1))).2.2.2.2.2.1
    | exact (gl_parts (yh_gfE_le (qd_B2_G0.trans hX.1))).2.2.2.2.2.2.2
    | exact (gl_parts (yh_gfE_le (qd_B2_G0.trans hX.1))).2.2.2.2.2.2.1

/-- **`vD = vQ` below `B₂`.** -/
theorem vD_low {c : Ordinal.{0}} (h : c < ucB) (x : Ordinal.{0}) : vD c x = vQ c x := by
  rw [vD, dif_neg (fun hX => absurd hX.1 (not_le.2 h))]

open Classical in
/-- **The gate of a code below `B₃`**: `Qc.qcG` below `B₂`; from `B₂` on the gates of the infinite parts of the clauses
of `vD`. -/
noncomputable def qdGt (c : Ordinal.{0}) : Ordinal.{0} :=
  if hX : ucB ≤ c ∧ c < qdB then
    max (max (if hA : YhAt (guE c) then
          (if hi : yhJ (guE c) < guE c then (if yhJ (guE c) < ω then 0 else qdGt (yhJ (guE c)))
            else if hN : qdI (qdLev (guE c)) (guE c) < guE c then
              max (qdFold (fun d => if hd : d < guE c then (if d < ω then 0 else qdGt d) else 0) (qdLev (guE c)))
                (if QdFixH (qdLev (guE c)) (qdI (qdLev (guE c)) (guE c)) then
                  max (if qdFpH (qdLev (guE c)) (qdI (qdLev (guE c)) (guE c)) < ω then 0
                      else qdGt (qdFpH (qdLev (guE c)) (qdI (qdLev (guE c)) (guE c))))
                    (if qdI (qdLev (guE c)) (guE c) -
                        (qdFpH (qdLev (guE c)) (qdI (qdLev (guE c)) (guE c)) + 1) < ω then 0
                      else qdGt (qdI (qdLev (guE c)) (guE c) -
                        (qdFpH (qdLev (guE c)) (qdI (qdLev (guE c)) (guE c)) + 1)))
                 else (if qdI (qdLev (guE c)) (guE c) < ω then 0 else qdGt (qdI (qdLev (guE c)) (guE c))))
            else 0) else
          max (if yhK (guE c) < ω then 0 else qdGt (yhK (guE c)))
            (if yhI (guE c) < ω then 0 else qdGt (yhI (guE c))))
        (if log (guE c) c < ω then 0 else qdGt (log (guE c) c)))
      (max (if c / guE c ^ log (guE c) c < ω then 0 else qdGt (c / guE c ^ log (guE c) c))
        (qdGt (c % guE c ^ log (guE c) c)))
  else qcG c
termination_by c
decreasing_by
  all_goals first
    | exact yr_ix_lt (qd_B2_G0.trans hX.1) hi
    | exact hd.trans_le (gl_E_le (yh_gfE_le (qd_B2_G0.trans hX.1)))
    | exact (qd_fpH_le _ _).trans_lt (hN.trans_le (gl_E_le (yh_gfE_le (qd_B2_G0.trans hX.1))))
    | exact (Ordinal.sub_le_self _ _).trans_lt (hN.trans_le (gl_E_le (yh_gfE_le (qd_B2_G0.trans hX.1))))
    | exact hN.trans_le (gl_E_le (yh_gfE_le (qd_B2_G0.trans hX.1)))
    | exact yh_lev_lt (qd_B2_G0.trans hX.1) hA
    | exact yh_idx_lt (qd_B2_G0.trans hX.1) hA
    | exact (gl_parts (yh_gfE_le (qd_B2_G0.trans hX.1))).2.2.2.2.2.1
    | exact (gl_parts (yh_gfE_le (qd_B2_G0.trans hX.1))).2.2.2.2.2.2.2
    | exact (gl_parts (yh_gfE_le (qd_B2_G0.trans hX.1))).2.2.2.2.2.2.1

theorem qdGt_low {c : Ordinal.{0}} (h : c < ucB) : qdGt c = qcG c := by
  rw [qdGt, dif_neg (fun hX => absurd hX.1 (not_le.2 h))]

/-- **The gate of a part**: `0` when finite. -/
noncomputable def qdQt (a : Ordinal.{0}) : Ordinal.{0} := if a < ω then 0 else qdGt a

/-- **The level reading at `x`**: `qdLv` with every leaf `d < e` read `vD d x`. -/
noncomputable def qdLvx (e l x : Ordinal.{0}) : Ordinal.{0} :=
  qdLv (fun d => if d < e then vD d x else 0) l

open Classical in
/-- **The reading of an atom index**: `F(x) + (j − (F+1))(x)` past the largest fixed point `F < j` of `Γ`, `j(x)`
below the first. -/
noncomputable def qdRI (j x : Ordinal.{0}) : Ordinal.{0} :=
  if VaFixG j then vD (vaFpG j) x + vD (j - (vaFpG j + 1)) x else vD j x

open Classical in
/-- **The reading of the index of a fixed point of `Hᵛ_λ`**: `p(x) + (y − (p+1))(x)` past the largest fixed point
`p < y` of `Hᵛ_λ`, `y(x)` below the first. -/
noncomputable def qdRK (l y x : Ordinal.{0}) : Ordinal.{0} :=
  if QdFixH l y then vD (qdFpH l y) x + vD (y - (qdFpH l y + 1)) x else vD y x

open Classical in
/-- **The gate of an `ε`-number code as a base** (`Qc.qcQE` below `B₂`). -/
noncomputable def qdQEt (e : Ordinal.{0}) : Ordinal.{0} :=
  if ucB ≤ e ∧ e < qdB then
    (if YhAt e then (if yhJ e < e then qdQt (yhJ e)
      else if qdI (qdLev e) e < e then
        max (qdFold (fun d => if d < e then qdQt d else 0) (qdLev e))
          (if QdFixH (qdLev e) (qdI (qdLev e) e) then
            max (qdQt (qdFpH (qdLev e) (qdI (qdLev e) e)))
              (qdQt (qdI (qdLev e) e - (qdFpH (qdLev e) (qdI (qdLev e) e) + 1)))
          else qdQt (qdI (qdLev e) e))
      else 0)
    else max (qdQt (yhK e)) (qdQt (yhI e)))
  else qcQE e

theorem qdQEt_low {e : Ordinal.{0}} (h : e < ucB) : qdQEt e = qcQE e := by
  unfold qdQEt; rw [if_neg (fun hX => absurd hX.1 (not_le.2 h))]

open Classical in
/-- **The reading of an `ε`-number code as a base** (`Qc.qcA` below `B₂`). -/
noncomputable def qdA (e x : Ordinal.{0}) : Ordinal.{0} :=
  if ucB ≤ e ∧ e < qdB then
    (if YhAt e then (if yhJ e < e then gq (qdRI (yhJ e) x) x else
        (if qdI (qdLev e) e < e then vt x (Om1 * (Om1 + qdLvx e (qdLev e) x) + qdRK (qdLev e) (qdI (qdLev e) e) x)
          else 0))
      else glA (vD (yhK e) x) (vD (yhI e) x) x)
  else qcA e x

theorem qdA_low {e : Ordinal.{0}} (h : e < ucB) (x : Ordinal.{0}) : qdA e x = qcA e x := by
  unfold qdA; rw [if_neg (fun hX => absurd hX.1 (not_le.2 h))]

end Googology.Trans.PoR.InaccPsi.R2.Qd

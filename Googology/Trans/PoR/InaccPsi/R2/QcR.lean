import Googology.Trans.PoR.InaccPsi.R2.VaR
import Googology.Trans.PoR.InaccPsi.R2.QcBd

/-!
# QcR: ONE READING OF EVERY CODE BELOW `B₂` — `Va.vR` BELOW `X`, THE LEVELS OF `H` FROM `X` ON

`B₂ = Uc.ucB`, `H_γ = Uc.ucH γ` (`γ < E₂ = ε_{Ω₂+1}`), a strongly critical `z ∈ [X, B₂)` is `H_λ(y)` with `λ = ucLev z`,
`y = ucI λ z < z` (`Uc.uc_nf`).  `Va.vR` reads every code below `X`.  Here `vQ` extends it to `[X, B₂)` by the same
clauses (the `ε`-bracket `e = guE c`, `c = e^j·d + r`; a base atom `Γ(j)`, `j < Γ(j)`, read `gq` of the index; a
non-atom `ε`-number `yhPsi α η` read `ϑˣ(Ω₁·α(x) + η(x))`), and a fixed point `e = H_λ(y)` of `Γ` from `X` on read

  `ϑˣ(Ω₁·(Ω₁ + λ(x)) + c(x))`,

`λ(x) = qcLv λ` the level with `Ω₂ ↦ Ω₁` and every component `d` read `d(x)` (so `λ(x) = λ`'s reading for `λ < Ω₂`,
`Ω₂ ↦ Ω₁`, `X = H_{Ω₂}(0) ↦ ϑˣ(Ω₁·Ω₁·2)`), and `c` the index of `y` among the non-fixed arguments of `H_λ`: `p + d` for
`y = p + 1 + d` past the largest fixed point `p < y` of `H_λ`, else `y` ([W07a] through the step Ψ6 of `R2.CitedVd`).

* `QcFixH`, `qcFpH` (the largest fixed point of `H_λ` below `y`), `qcLv` (the level map `Ω₂ ↦ Ω₁`), `vQ`;
* `vQ_low` (**`vQ = vR` below `X`**), `vQ_big`.

No new axiom.  New definitions: `QcFixH`, `qcFpH`, `qcLv`, `vQ`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi
  Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Yh
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Uc
  Googology.Trans.PoR.InaccPsi.R2.Va Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.Xu Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Yw

/-- A fixed point of `H_λ` below `y`. -/
def QcFixH (l y : Ordinal.{0}) : Prop := ∃ f, ucH l f = f ∧ f < y

/-- **The largest fixed point of `H_λ` below `y`** (`sSup`). -/
noncomputable def qcFpH (l y : Ordinal.{0}) : Ordinal.{0} := sSup {f | ucH l f = f ∧ f < y}

theorem qc_fpH_le (l y : Ordinal.{0}) : qcFpH l y ≤ y := csSup_le' fun _ hf => hf.2.le

/-- **The level map**: `γ < E₂` in base `Ω₂` with `Ω₂ ↦ Ω₁` and every component `d ↦ f d`. -/
noncomputable def qcLv (f : Ordinal.{0} → Ordinal.{0}) (γ : Ordinal.{0}) : Ordinal.{0} :=
  if h1 : γ < OmTwo then f γ
  else if h2 : γ < ucE then
    have : log OmTwo γ < γ := uc_log_lt (not_lt.1 h1) h2
    have : γ % OmTwo ^ log OmTwo γ < γ := uc_mod_lt (not_lt.1 h1)
    Om1 ^ qcLv f (log OmTwo γ) * f (γ / OmTwo ^ log OmTwo γ) + qcLv f (γ % OmTwo ^ log OmTwo γ)
  else 0
termination_by γ

theorem qc_X_G0 : gcG 0 ≤ (tlX : Ordinal.{0}) :=
  ((yr_gcG_lt_BG (show InE tfBG from Low.opow_eq_self_of_SC tfBG_SC).pos).trans tl_BG_lt_X).le

open Classical in
/-- **The reading of every code below `B₂`**: `Va.vR` below `X`; from `X` on the clauses of `Va.vR`, with a fixed point
`H_λ(y)` of `Γ` read `ϑˣ(Ω₁·(Ω₁ + λ(x)) + c(x))`. -/
noncomputable def vQ (c x : Ordinal.{0}) : Ordinal.{0} :=
  if hX : tlX ≤ c ∧ c < ucB then
    (if hA : YhAt (guE c) then (if hi : yhJ (guE c) < guE c then
        gq (if VaFixG (yhJ (guE c)) then vQ (vaFpG (yhJ (guE c))) x +
            vQ (yhJ (guE c) - (vaFpG (yhJ (guE c)) + 1)) x
          else vQ (yhJ (guE c)) x) x
        else (if hN : ucI (ucLev (guE c)) (guE c) < guE c then
          vt x (Om1 * (Om1 + qcLv (fun d => if hd : d < guE c then vQ d x else 0) (ucLev (guE c))) +
            (if QcFixH (ucLev (guE c)) (ucI (ucLev (guE c)) (guE c)) then
              vQ (qcFpH (ucLev (guE c)) (ucI (ucLev (guE c)) (guE c))) x +
              vQ (ucI (ucLev (guE c)) (guE c) - (qcFpH (ucLev (guE c)) (ucI (ucLev (guE c)) (guE c)) + 1)) x
            else vQ (ucI (ucLev (guE c)) (guE c)) x))
          else 0))
      else glA (vQ (yhK (guE c)) x) (vQ (yhI (guE c)) x) x) ^ vQ (log (guE c) c) x *
      vQ (c / guE c ^ log (guE c) c) x + vQ (c % guE c ^ log (guE c) c) x
  else vR c x
termination_by c
decreasing_by
  all_goals first
    | exact yr_ix_lt (qc_X_G0.trans hX.1) hi
    | exact (va_fpG_le _).trans_lt (yr_ix_lt (qc_X_G0.trans hX.1) hi)
    | exact (Ordinal.sub_le_self _ _).trans_lt (yr_ix_lt (qc_X_G0.trans hX.1) hi)
    | exact hd.trans_le (gl_E_le (yh_gfE_le (qc_X_G0.trans hX.1)))
    | exact (qc_fpH_le _ _).trans_lt (hN.trans_le (gl_E_le (yh_gfE_le (qc_X_G0.trans hX.1))))
    | exact (Ordinal.sub_le_self _ _).trans_lt (hN.trans_le (gl_E_le (yh_gfE_le (qc_X_G0.trans hX.1))))
    | exact hN.trans_le (gl_E_le (yh_gfE_le (qc_X_G0.trans hX.1)))
    | exact yh_lev_lt (qc_X_G0.trans hX.1) hA
    | exact yh_idx_lt (qc_X_G0.trans hX.1) hA
    | exact (gl_parts (yh_gfE_le (qc_X_G0.trans hX.1))).2.2.2.2.2.1
    | exact (gl_parts (yh_gfE_le (qc_X_G0.trans hX.1))).2.2.2.2.2.2.2
    | exact (gl_parts (yh_gfE_le (qc_X_G0.trans hX.1))).2.2.2.2.2.2.1

/-- **`vQ = vR` below `X`.** -/
theorem vQ_low {c : Ordinal.{0}} (h : c < tlX) (x : Ordinal.{0}) : vQ c x = vR c x := by
  rw [vQ, dif_neg (fun hX => absurd hX.1 (not_le.2 h))]

end Googology.Trans.PoR.InaccPsi.R2.Qc

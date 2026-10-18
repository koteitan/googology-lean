import Googology.Trans.PoR.InaccPsi.R2.FpPoly
import Googology.Trans.PoR.InaccPsi.R2.PhRoad

/-!
# The frontiers of `lzWw`, `ltS K`, `ltSw`, `lnS K`, `lnSw` below `L(0)`; the notation hypothesis closed up to
`Λ⁺(lnSw)`; ENUM-REACH on the whole range below `Λ⁺(lnSw)`

With `GgPoly` up to the top codes (`R2.Fp.FpPoly`) and the readings of the tops (`R2.Fp.FpLev`), `Ph.phFrGen` places
each frontier: `Λ⁺(X) ≤ ι(ω^T·ω) < L(0)` and `υ(Λ⁺(X)) < L(0)` for the top code `T` of `X`
(`T = phYw, fpTc K, fpTw, fpCc (K+1), fpPc = φ(ω+1, Ω₁ + 1)`).

* `fpFr_lzWw`, `fpFr_ltS`, `fpFr_ltSw`, `fpFr_lnS`, `fpFr_lnSw` (**the frontiers below `L(0)`**), `fpFr_order`
  (**`υ` of `Λ⁺(lzWw)`, `Λ⁺_T`, `Λ⁺(ltSw)`, `Λ⁺_C`, `Λ⁺(lnSw)` is below `L(0) ≤ L(n+1) < L(ω) < L(ω+1)`**);
* `fpT_lzWw`, `fpT_lt`, `fpT_ltSw`, `fpT_ln`, `fpT_lnSw` (**`Θ_F(m_F) = O(F)` at every `υ`-fixed point `F` of the
  range below the frontier**: THEOREM UNI `Gg.ggUniTh` with `Ph.phExp_le`);
* `fpWwRoad3`, `fpLtRoad3`, `fpLtSwRoad3`, `fpLnRoad3`, `fpLnSwRoad3` (**the roads `Lt.ltWwRoad3`, `Lt.ltRoad3`,
  `Lt.ltSwRoad3`, `Lt.lnRoad3`, `Lt.lnSwRoad3` without the notation hypothesis**);
* `fpEnum_lnSw` (**ENUM-REACH, both halves, at every restart of the range below `Λ⁺(lnSw)`**).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Fp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cp Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Lz
  Googology.Trans.PoR.InaccPsi.R2.Lt Googology.Trans.PoR.InaccPsi.R2.Ph

variable {S : InaccSeq.{0}}

/-! ## The top codes -/

theorem fp_Yw_lt_Gam : phYw < ggGam := ph_lt_Gam (fp_cl_Yw ph_SC_Om1)
theorem fp_Tc_lt_Gam (K : ℕ) : fpTc K < ggGam := ph_lt_Gam (fp_cl_Tc ph_SC_Om1 K)
theorem fp_Tw_lt_Gam : fpTw < ggGam := ph_lt_Gam (fp_cl_Tw ph_SC_Om1)
theorem fp_C_lt_Gam (K : ℕ) : fpCc K < ggGam := ph_lt_Gam (fp_cl_C ph_SC_Om1 K)
theorem fp_P_lt_Gam : fpPc < ggGam := ph_lt_Gam (fp_cl_P ph_SC_Om1)

theorem fp_Om1_le_Yw : Om 1 ≤ phYw := (fp_Om1_lt_C 0).le
theorem fp_Om1_le_Tc (K : ℕ) : Om 1 ≤ fpTc K :=
  ((lt_add_one _).trans_le (le_self_add.trans (right_le_veblen _ _))).le.trans (right_le_veblen _ _)
theorem fp_Om1_le_Tw : Om 1 ≤ fpTw := fp_Om1_le_Yw.trans (right_le_veblen _ _)
theorem fp_Om1_le_P : Om 1 ≤ fpPc := le_self_add.trans (right_le_veblen _ _)

/-! ## The frontiers below `L(0)` -/

/-- **`lzWw`**: `Λ⁺(lzWw) ≤ ι(ω^{phYw}·ω) < L(0)`. -/
theorem fpFr_lzWw : xtB1 lzWw ≤ iota S (ω ^ phYw * ω) ∧ iota S (ω ^ phYw * ω) < Nc.ncL S 0 ∧
    upsilon (xtB1 lzWw) < Nc.ncL S 0 :=
  (phFrGen (S := S) fp_Yw_lt_Gam (phPolyR_of fpPoly_lzWw) (fun _ hy hy1 => (fpTh_Yw hy hy1).symm)
    (fun _ hZ => fp_cl_Yw hZ) fp_Om1_le_Yw).2.2

/-- **`ltS K`**: `Λ⁺(ltS K) ≤ ι(ω^{fpTc K}·ω) < L(0)`. -/
theorem fpFr_ltS (K : ℕ) : xtB1 (ltS K) ≤ iota S (ω ^ fpTc K * ω) ∧ iota S (ω ^ fpTc K * ω) < Nc.ncL S 0 ∧
    upsilon (xtB1 (ltS K)) < Nc.ncL S 0 :=
  (phFrGen (S := S) (fp_Tc_lt_Gam K) (phPolyR_of (fpPoly_ltS K)) (fun _ hy hy1 => (fpTh_T hy hy1 K).symm)
    (fun _ hZ => fp_cl_Tc hZ K) (fp_Om1_le_Tc K)).2.2

/-- **`ltSw`**: `Λ⁺(ltSw) ≤ ι(ω^{fpTw}·ω) < L(0)`. -/
theorem fpFr_ltSw : xtB1 ltSw ≤ iota S (ω ^ fpTw * ω) ∧ iota S (ω ^ fpTw * ω) < Nc.ncL S 0 ∧
    upsilon (xtB1 ltSw) < Nc.ncL S 0 :=
  (phFrGen (S := S) fp_Tw_lt_Gam (phPolyR_of fpPoly_ltSw) (fun _ hy hy1 => (fpTh_Tw hy hy1).symm)
    (fun _ hZ => fp_cl_Tw hZ) fp_Om1_le_Tw).2.2

/-- **`lnS K`**: `Λ⁺(lnS K) ≤ ι(ω^{fpCc (K+1)}·ω) < L(0)`. -/
theorem fpFr_lnS (K : ℕ) : xtB1 (lnS K) ≤ iota S (ω ^ fpCc (K + 1) * ω) ∧
    iota S (ω ^ fpCc (K + 1) * ω) < Nc.ncL S 0 ∧ upsilon (xtB1 (lnS K)) < Nc.ncL S 0 :=
  (phFrGen (S := S) (fp_C_lt_Gam (K + 1)) (phPolyR_of (fpPoly_lnS K))
    (fun _ hy hy1 => (fpTh_C hy hy1 (K + 1)).symm) (fun _ hZ => fp_cl_C hZ (K + 1)) (fp_Om1_lt_C (K + 1)).le).2.2

/-- **`lnSw`**: `Λ⁺(lnSw) ≤ ι(ω^{φ(ω+1, Ω₁+1)}·ω) < L(0)`. -/
theorem fpFr_lnSw : xtB1 lnSw ≤ iota S (ω ^ fpPc * ω) ∧ iota S (ω ^ fpPc * ω) < Nc.ncL S 0 ∧
    upsilon (xtB1 lnSw) < Nc.ncL S 0 :=
  (phFrGen (S := S) fp_P_lt_Gam (phPolyR_of fpPoly_lnSw) (fun _ hy hy1 => (fpTh_P hy hy1).symm)
    (fun _ hZ => fp_cl_P hZ) fp_Om1_le_P).2.2

/-- **The order of the frontiers and the `L(n)`** (unconditional): `Λ⁺_Y < Λ⁺(lzWw) < Λ⁺_T < Λ⁺(ltSw) < Λ⁺_C <
Λ⁺(lnSw)`, and `υ(Λ⁺(lnSw)) < L(0) ≤ L(n+1) < L(ω) < L(ω+1)`; `Λ⁺(lnSw) < L(ω+1)`. -/
theorem fpFr_order (n : ℕ) :
    (lzWFam.famSup < xtB1 lzWw ∧ xtB1 lzWw < ltFam.famSup ∧ ltFam.famSup < xtB1 ltSw ∧
      xtB1 ltSw < lnFam.famSup ∧ lnFam.famSup < xtB1 lnSw) ∧
    (upsilon (xtB1 lnSw) < Nc.ncL S 0 ∧ Nc.ncL S 0 ≤ Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ∧
      Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) < Nc.ncL S ω ∧ Nc.ncL S ω < Nc.ncL S (ω + 1)) ∧
    xtB1 lnSw < Nc.ncL S (ω + 1) := by
  obtain ⟨h0, h1, h2⟩ := phL_chain (S := S) n
  have hB := (fpFr_lnSw (S := S)).2.2
  refine ⟨⟨ln_order_all.1, ln_order_all.2.1, ln_order_all.2.2.1, ln_order_all.2.2.2, ltC_lt_B1⟩,
    ⟨hB, h0, h1, h2⟩, ?_⟩
  exact upsilon_normal.strictMono.le_apply.trans_lt (((hB.trans_le h0).trans h1).trans h2)

/-! ## The notation hypotheses up to `Λ⁺(lnSw)` -/

/-- **The notation hypothesis below `Λ⁺(lzWw)`.** -/
theorem fpT_lzWw {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 lzWw) (hfix : upsilon l = l) :
    cdTheta S l (cdCode S l) = xtOrec lzWw l :=
  ggUniTh fp_Yw_lt_Gam.le fpPoly_lzWw hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) (hl.trans_le (fpFr_lzWw (S := S)).1))

/-- **The notation hypothesis of `Lt.ltRoad3`** (`ltFam.famTHfix`). -/
theorem fpT_lt : ltFam.famTHfix S := fun k _ hr hlk hfix =>
  ggUniTh (fp_Tc_lt_Gam k).le (fpPoly_ltS k) hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) (hlk.trans_le (fpFr_ltS (S := S) k).1))

/-- **The notation hypothesis below `Λ⁺(ltSw)`.** -/
theorem fpT_ltSw {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 ltSw) (hfix : upsilon l = l) :
    cdTheta S l (cdCode S l) = xtOrec ltSw l :=
  ggUniTh fp_Tw_lt_Gam.le fpPoly_ltSw hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) (hl.trans_le (fpFr_ltSw (S := S)).1))

/-- **The notation hypothesis of `Lt.lnRoad3`** (`lnFam.famTHfix`). -/
theorem fpT_ln : lnFam.famTHfix S := fun k _ hr hlk hfix =>
  ggUniTh (fp_C_lt_Gam (k + 1 + 1)).le (fpPoly_lnS (k + 1)) hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) (hlk.trans_le (fpFr_lnS (S := S) (k + 1)).1))

/-- **The notation hypothesis below `Λ⁺(lnSw)`**: `Θ_F(m_F) = O(F)` at every `υ`-fixed point `F` of the range below
`Λ⁺(lnSw)`. -/
theorem fpT_lnSw {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 lnSw) (hfix : upsilon l = l) :
    cdTheta S l (cdCode S l) = xtOrec lnSw l :=
  ggUniTh fp_P_lt_Gam.le fpPoly_lnSw hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) (hl.trans_le (fpFr_lnSw (S := S)).1))

/-! ## The roads without the notation hypothesis -/

/-- **`Lt.ltWwRoad3` without the notation hypothesis.** -/
theorem fpWwRoad3 (hU : ∀ l, CdRange S l → xtB1 lzWw ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 lzWw ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 lzWw) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  ltWwRoad3 hU hL (fun _ hr hl hfix => fpT_lzWw hr hl hfix) hV hC hEQ hrest hB2

/-- **`Lt.ltRoad3` without the notation hypothesis.** -/
theorem fpLtRoad3 (hU : ∀ l, CdRange S l → ltFam.famSup ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → ltFam.famSup ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut ltFam.famSup l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  ltRoad3 hU hL fpT_lt hV hC hEQ hrest hB2

/-- **`Lt.ltSwRoad3` without the notation hypothesis.** -/
theorem fpLtSwRoad3 (hU : ∀ l, CdRange S l → xtB1 ltSw ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 ltSw ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 ltSw) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  ltSwRoad3 hU hL (fun _ hr hl hfix => fpT_ltSw hr hl hfix) hV hC hEQ hrest hB2

/-- **`Lt.lnRoad3` without the notation hypothesis.** -/
theorem fpLnRoad3 (hU : ∀ l, CdRange S l → lnFam.famSup ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → lnFam.famSup ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut lnFam.famSup l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  lnRoad3 hU hL fpT_ln hV hC hEQ hrest hB2

/-- **`Lt.lnSwRoad3` without the notation hypothesis** (the longest road): the remaining hypotheses are UPPER and
LOWER at the range restarts `l ≥ Λ⁺(lnSw)`, CapV at the range restarts outside `Λ⁺(lnSw)` with `ρ_l < L(ω)`, (CL),
EQ, TCrest, (EMB2). -/
theorem fpLnSwRoad3 (hU : ∀ l, CdRange S l → xtB1 lnSw ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 lnSw ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 lnSw) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  lnSwRoad3 hU hL (fun _ hr hl hfix => fpT_lnSw hr hl hfix) hV hC hEQ hrest hB2

/-! ## ENUM-REACH below `Λ⁺(lnSw)` -/

/-- **ENUM-REACH at every restart of the range below `Λ⁺(lnSw)`.** -/
theorem fpEnum_lnSw {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 lnSw) : CdUpper S l ∧ CdLower S l := by
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact lnSw_init hr hl hnf
  · exact (lnSw_iff hr.1 hl).2 (fpT_lnSw hr hl hfx.symm)

end Googology.Trans.PoR.InaccPsi.R2.Fp

import Googology.Trans.PoR.InaccPsi.R2.PhFr
import Googology.Trans.PoR.InaccPsi.R2.GgRoad

/-!
# The notation hypothesis of the roads, closed; ENUM-REACH on the whole ranges

A named fixed point `λ = υ_λ` below `ι(ω^T·ω)` has `e(η_λ) ≤ T` (`phExp_le`).  The frontiers of `R2.Ph.PhFr`
(`cpB1 ≤ ι(phB·ω)`, `Λ⁺_k ≤ ι(ω^{ω^{phLLe k}}·ω)`, `Λ⁺(lyEB) ≤ ι(phEB·ω)`, `Λ⁺(lzZ) ≤ ι(ω^{phZT}·ω)`,
`Λ⁺(lzVs) ≤ ι(ω^{phV}·ω)`, `Λ⁺(lzWs K) ≤ ι(ω^{phW K}·ω)`) and THEOREM UNI up to the top codes (`phVz`, `phLL`,
`phLyE`, `phLzZ`, `phLzV`, `phLzW`) give `Θ_λ(m_λ) = O(λ)` at every fixed point of the range below the frontier.
So:

* `phT_cp`, `phT_W2`, `phT_lyE`, `phT_lzZ`, `phT_lzV`, `phT_lzW` (**the notation hypotheses, proved**);
* `phRoad3`, `phW2Road3`, `phLyERoad3`, `phLzRoad3`, `phLzVRoad3`, `phLzWRoad3` (**the roads without the
  notation hypothesis**: the rest is UPPER/LOWER above the frontier, CapV at the outer restarts below `L(ω)`, (CL),
  EQ, TCrest, (EMB2));
* `phEnum_cp`, `phEnum_W2`, `phEnum_lyE`, `phEnum_lzZ`, `phEnum_lzV`, `phEnum_lzW` (**ENUM-REACH, both halves, at
  every restart of the range below the frontier**, no exception).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ph

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cp Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Lz

variable {S : InaccSeq.{0}}

/-- **A named fixed point below `ι(ω^T·ω)` has `e(η_λ) ≤ T`.** -/
theorem phExp_le {l ηx T : Ordinal.{0}} (hri : IsRestartIdx l) (hfix : upsilon l = l)
    (hX : upsilon l < Pv S ηx) (hlt : l < iota S (ω ^ T * ω)) : cdExp (cdEta S l) ≤ T := by
  obtain ⟨-, hι, -, -⟩ := cdEta_pv_spec (S := S) hri.1 hX
  have hη : cdEta S l < ω ^ T * ω := by
    by_contra hge
    push Not at hge
    have := iota_mono (S := S) _ _ hge
    rw [hι] at this
    exact absurd hlt (not_lt.2 this)
  obtain ⟨η0, hdec, -⟩ := cdExp_decomp (gg_name_ne hri hfix hX)
  have h1 : ω ^ cdExp (cdEta S l) < ω ^ (T + 1) := by
    rw [opow_add, opow_one]
    refine lt_of_le_of_lt ?_ hη
    conv_rhs => rw [hdec]
    exact le_add_self
  exact Order.lt_add_one_iff.1 ((opow_lt_opow_iff_right one_lt_omega0).1 h1)

/-! ## The notation hypotheses -/

/-- **The notation hypothesis below `cpB1`.** -/
theorem phT_cp {l : Ordinal.{0}} (hr : CdRange S l) (hlB : l < cpB1) (hfix : upsilon l = l) :
    cdTheta S l (cdCode S l) = VzOrec l := by
  have h := (phFr_vz (S := S)).2.2.1
  have e : phB * ω = ω ^ phB * ω := by rw [ph_B_eps]
  rw [e] at h
  exact phVz hr.1 hfix (cp_name_L hr.2.2.1) (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) (hlB.trans_le h))

/-- **The notation hypothesis below `Λ⁺_k`.** -/
theorem phT_W2 (k : ℕ) {l : Ordinal.{0}} (hr : CdRange S l) (hlk : l < xtFamW2.bd k) (hfix : upsilon l = l) :
    cdTheta S l (cdCode S l) = xtFamW2.off k l :=
  phLL k hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) (hlk.trans_le (phFr_LL (S := S) k).1))

/-- **The notation hypothesis below `Λ⁺(lyEB)`.** -/
theorem phT_lyE {l : Ordinal.{0}} (hr : CdRange S l) (hlB : l < xtB1 lyEB) (hfix : upsilon l = l) :
    cdTheta S l (cdCode S l) = xtOrec lyEB l := by
  have h := (phFr_lyE (S := S)).2.1
  have e : phEB * ω = ω ^ phEB * ω := by rw [ph_EB_eps]
  rw [e] at h
  exact phLyE hr.1 hfix (cp_name_L hr.2.2.1) (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) (hlB.trans_le h))

/-- **The notation hypothesis below `Λ⁺(lzZ)`.** -/
theorem phT_lzZ {l : Ordinal.{0}} (hr : CdRange S l) (hlB : l < xtB1 lzZ) (hfix : upsilon l = l) :
    cdTheta S l (cdCode S l) = xtOrec lzZ l :=
  phLzZ hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) (hlB.trans_le (phFr_lzZ (S := S)).1))

/-- **The notation hypothesis below `Λ⁺(lzVs)`.** -/
theorem phT_lzV {l : Ordinal.{0}} (hr : CdRange S l) (hlB : l < xtB1 lzVs) (hfix : upsilon l = l) :
    cdTheta S l (cdCode S l) = xtOrec lzVs l :=
  phLzV hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) (hlB.trans_le (phFr_lzV (S := S)).1))

/-- **The notation hypothesis of `lzWRoad3`** (`lzWFam.famTHfix`). -/
theorem phT_lzW : lzWFam.famTHfix S := fun k _ hr hlk hfix =>
  phLzW (k + 2) hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) (hlk.trans_le (phFr_lzW (S := S) (k + 2)).1))

/-! ## The roads without the notation hypothesis -/

/-- **The road below `cpB1` without the notation hypothesis.** -/
theorem phRoad3 (hU : CpUPPERhigh S) (hL : CpLOWERhigh S)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CpOut2 l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  ggRoad3 hU hL (fun _ hr hlB hfix _ _ => phT_cp hr hlB hfix) hV hC hEQ hrest hB2

/-- **The road below `Λ_{ω²}` without the notation hypothesis.** -/
theorem phW2Road3 (hU : ∀ l, CdRange S l → xtFamW2.famSup ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtFamW2.famSup ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut xtFamW2.famSup l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  ggW2Road3 hU hL (fun k _ hr hlk hfix _ _ => phT_W2 k hr hlk hfix) hV hC hEQ hrest hB2

/-- **The road below `Λ⁺(lyEB)` without the notation hypothesis.** -/
theorem phLyERoad3 (hU : ∀ l, CdRange S l → xtB1 lyEB ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 lyEB ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 lyEB) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  ggLyERoad3 hU hL (fun _ hr hlB hfix _ => phT_lyE hr hlB hfix) hV hC hEQ hrest hB2

/-- **The road below `Λ⁺(lzZ)` without the notation hypothesis.** -/
theorem phLzRoad3 (hU : ∀ l, CdRange S l → xtB1 lzZ ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 lzZ ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 lzZ) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  lzRoad3 hU hL (fun _ hr hlB hfix => phT_lzZ hr hlB hfix) hV hC hEQ hrest hB2

/-- **The road below `Λ⁺(lzVs)` without the notation hypothesis.** -/
theorem phLzVRoad3 (hU : ∀ l, CdRange S l → xtB1 lzVs ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 lzVs ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 lzVs) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  lzVRoad3 hU hL (fun _ hr hlB hfix => phT_lzV hr hlB hfix) hV hC hEQ hrest hB2

/-- **The road below `Λ⁺_Y = sup_K Λ⁺(lzWs (K+2))` without the notation hypothesis.** -/
theorem phLzWRoad3 (hU : ∀ l, CdRange S l → lzWFam.famSup ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → lzWFam.famSup ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut lzWFam.famSup l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  lzWRoad3 hU hL phT_lzW hV hC hEQ hrest hB2

/-! ## ENUM-REACH on the whole ranges -/

/-- **ENUM-REACH at every restart of the range below `cpB1`.** -/
theorem phEnum_cp {l : Ordinal.{0}} (hr : CdRange S l) (hlB : l < cpB1) : CdUpper S l ∧ CdLower S l := by
  by_cases hfix : upsilon l = l
  · exact (cpExact_iff hr.1 hlB).2 (phT_cp hr hlB hfix)
  · exact ⟨(Fx.fxEnum_range hr hlB fun h => hfix h.1).2.1, (Fx.fxEnum_range hr hlB fun h => hfix h.1).2.2.1⟩

/-- **ENUM-REACH at every restart of the range below `Λ_{ω²}`.** -/
theorem phEnum_W2 {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtFamW2.famSup) : CdUpper S l ∧ CdLower S l := by
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact xtW2_init hr hl hnf
  · obtain ⟨k, hk⟩ := xtFamW2.famLt hl
    exact (xtExact_iff (xtFamW2.spec k) hr.1 hk).2 (phT_W2 k hr hk hfx.symm)

/-- **ENUM-REACH at every restart of the range below `Λ⁺(lyEB)`.** -/
theorem phEnum_lyE {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 lyEB) : CdUpper S l ∧ CdLower S l := by
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact lyE_init hr hl hnf
  · exact (lyE_iff hr.1 hl).2 (phT_lyE hr hl hfx.symm)

/-- **ENUM-REACH at every restart of the range below `Λ⁺(lzZ)`.** -/
theorem phEnum_lzZ {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 lzZ) : CdUpper S l ∧ CdLower S l := by
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact lzZ_init hr hl hnf
  · exact (lzZ_iff hr.1 hl).2 (phT_lzZ hr hl hfx.symm)

/-- **ENUM-REACH at every restart of the range below `Λ⁺(lzVs)`.** -/
theorem phEnum_lzV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 lzVs) : CdUpper S l ∧ CdLower S l := by
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact lzV_init hr hl hnf
  · exact (lzV_iff hr.1 hl).2 (phT_lzV hr hl hfx.symm)

/-- **ENUM-REACH at every restart of the range below `Λ⁺_Y`.** -/
theorem phEnum_lzW {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < lzWFam.famSup) : CdUpper S l ∧ CdLower S l := by
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact lzW_init hr hl hnf
  · obtain ⟨k, hk⟩ := lzWFam.famLt hl
    exact (xtExact_iff (lzWFam.spec k) hr.1 hk).2 (phT_lzW k l hr hk hfx.symm)

end Googology.Trans.PoR.InaccPsi.R2.Ph

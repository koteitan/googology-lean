import Googology.Trans.PoR.InaccPsi.R2.GbLad
import Googology.Trans.PoR.InaccPsi.R2.GbLim

/-!
# The second tower: bases with tops `ϑˣ(Ω₁·Ω₁ + ω + 1 + k)` over the limit base `gbWB`

Iterating `R2.GbLim` from the base `gbWB` of `R2.GbW` (top `ϑˣ(Ω₁·Ω₁ + ω)`):

* `gbW_limH` (**`ϑˣ(Ω₁·Ω₁ + j) ≤ ϑˣ(Ω₁·Ω₁ + ω) < ϑˣ(Ω₁·Ω₁ + ω + 1)` for `j ≤ ω`**), the offsets `gbOff k = ω + 1 + k`
  (`gbOff_eq`), the bases `gbTB k`, the layers `gbTK k = gqLim (gbTB k) (gbOff k)` (**top `ϑˣ(Ω₁·Ω₁ + ω + 1 + k)`**);
* `gbTow_lt` (**`Λ⁺(gbTK k) < Λ⁺(gbTK (k+1))`**), `gbTow_gt` (**`Λ^W < Λ⁺(gbTK 0)`**), `gbTow_eq0`, `gbTowFam`;
* `gbTow_T_low` (**the notation hypothesis at every fixed point of the range below `ι(Γ_{Ω₁+ω})`**, every layer);
* `gbTow_blk` (**BLK^O and the exact reaches below `υ` of `sup_k Λ⁺(gbTK k)`**), `gbTow_init` (**ENUM-REACH at every
  non-fixed restart of the range below it**), `gbTow_capV`, `gbTowRoad` (**the successor road**: UPPER/LOWER asked only
  at `λ ≥ sup_k Λ⁺(gbTK k)`, the notation hypothesis only at the fixed points in `[ι(Γ_{Ω₁+ω}), sup_k Λ⁺(gbTK k))`,
  CapV only at the outer restarts `λ ≥ ι(Γ_{Ω₁+ω})`);
* `gbTow_order` (**`ι(Γ_{Ω₁+ω}) < Λ⁺(gbUSys) < Λ^W < Λ⁺(gbTK 0) < sup_k Λ⁺(gbTK k) < Ω₁`**).

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Lp
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp Googology.Trans.PoR.InaccPsi.R2.Bt

/-- **The limit base satisfies the limit hypothesis with `η = ω + 1`.** -/
theorem gbW_limH : GqLimH gbWB (ω + 1) :=
  ⟨gqCst_succ gqCst_omega,
    fun x hx hx1 _ hj => gq_mono hx hx1 (gqCst_omega x hx) (Order.lt_add_one_iff.1 hj),
    fun x hx hx1 => gq_lt hx hx1 (gqCst_succ gqCst_omega x hx) (lt_add_one ω)⟩

/-- The offsets `ω + 1 + k`. -/
noncomputable def gbOff : ℕ → Ordinal.{0}
  | 0 => ω + 1
  | k + 1 => gbOff k + 1

theorem gbOff_eq (k : ℕ) : gbOff k = ω + 1 + k := by
  induction k with
  | zero => show ω + 1 = ω + 1 + ((0 : ℕ) : Ordinal.{0}); rw [Nat.cast_zero, add_zero]
  | succ k ih => show gbOff k + 1 = _; rw [ih, Nat.cast_succ, add_assoc]

/-- **The second tower of bases**: `gbTBp 0 = gbWB`, `gbTBp (k+1) = lim (gbTBp k)`. -/
noncomputable def gbTBp : (k : ℕ) → {B : LpB // GqLimH B (gbOff k)}
  | 0 => ⟨gbWB, gbW_limH⟩
  | k + 1 => ⟨gqLimB (gbTBp k).1 (gbOff k) (gbTBp k).2, gqLimH_next (gbTBp k).1 (gbOff k) (gbTBp k).2⟩

/-- The `k`-th base of the second tower. -/
noncomputable def gbTB (k : ℕ) : LpB := (gbTBp k).1

theorem gbTH (k : ℕ) : GqLimH (gbTB k) (gbOff k) := (gbTBp k).2

/-- **The `k`-th layer of the second tower**, top `ϑˣ(Ω₁·Ω₁ + ω + 1 + k)`. -/
noncomputable def gbTK (k : ℕ) : XtLay := gqLim (gbTB k) (gbOff k) (gbTH k)

theorem gbTB_zero : gbTB 0 = gbWB := rfl

theorem gbTB_succ (k : ℕ) : (gbTB (k + 1)).K = gbTK k := rfl

theorem gbTK_E (k : ℕ) (x : Ordinal.{0}) : (gbTK k).E x = vt x (Om1 * Om1 + (ω + 1 + k)) := by
  show gq (gbOff k) x = _
  rw [gbOff_eq]; rfl

/-- **`Λ⁺(gbTK k) < Λ⁺(gbTK (k+1))`.** -/
theorem gbTow_lt (k : ℕ) : xtB1 (gbTK k).sys < xtB1 (gbTK (k + 1)).sys :=
  gqLim_gt_K (B := gbTB (k + 1)) (gbTH (k + 1))

theorem gbTow_mono : StrictMono fun k => xtB1 (gbTK k).sys := strictMono_nat_of_lt_succ gbTow_lt

/-- **`O_{gbTK (k+1)} = O_{gbTK k}` below `Λ⁺(gbTK k)`.** -/
theorem gbTow_eq_succ (k : ℕ) {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h : μ < xtB1 (gbTK k).sys) :
    xtOrec (gbTK (k + 1)).sys μ = xtOrec (gbTK k).sys μ :=
  gqLim_eq_K (B := gbTB (k + 1)) (gbTH (k + 1)) hμ h

/-- **`O_{gbTK k} = O_{gbTK 0}` below `Λ⁺(gbTK 0)`.** -/
theorem gbTow_eq0 (k : ℕ) {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h : μ < xtB1 (gbTK 0).sys) :
    xtOrec (gbTK k).sys μ = xtOrec (gbTK 0).sys μ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [gbTow_eq_succ k hμ (h.trans_le (gbTow_mono.monotone (Nat.zero_le k))), ih]

/-- **`Λ^W < Λ⁺(gbTK 0)`.** -/
theorem gbTow_gt : (lpFam gbWB).famSup < xtB1 (gbTK 0).sys := gqFam_lt_lim (B := gbWB) gbW_limH

/-- **`O_{gbTK 0} = O_{gbUSys}` below `Λ⁺(gbUSys)`.** -/
theorem gbTow_eqW {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h : μ < xtB1 gbUSys) :
    xtOrec (gbTK 0).sys μ = xtOrec gbUSys μ :=
  gqLim_eq_K (B := gbWB) gbW_limH hμ h

/-- **The second tower as a family**: bounds `Λ⁺(gbTK k)`. -/
noncomputable def gbTowFam : XtFam where
  bd := fun k => xtB1 (gbTK k).sys
  off := fun k => xtOrec (gbTK k).sys
  spec := fun k => xtSpec1 (XtLay.topPkg (gbTK k))
  mono := gbTow_lt
  nonfix := fun k _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtB1_lt_Om1 (XtLay.topPkg (gbTK k))))

variable {S : InaccSeq.{0}}

/-- **Where the second tower lies**: `ι(Γ_{Ω₁+ω}) < Λ⁺(gbUSys) < Λ^W < Λ⁺(gbTK 0) < sup_k Λ⁺(gbTK k) < Ω₁`. -/
theorem gbTow_order : iota S Ga.gaW < xtB1 gbUSys ∧ xtB1 gbUSys < (lpFam gbWB).famSup ∧
    (lpFam gbWB).famSup < xtB1 (gbTK 0).sys ∧ xtB1 (gbTK 0).sys < gbTowFam.famSup ∧ gbTowFam.famSup < Om1 := by
  obtain ⟨h1, h2, h3, -⟩ := gb_order (S := S)
  exact ⟨h1, h2.trans h3, gbTow_gt, gbTowFam.famBd_lt 0, gbTowFam.famSup_lt_Om1⟩

/-- **The notation hypothesis at every fixed point of the range below `ι(Γ_{Ω₁+ω})`**, for every layer of the
second tower. -/
theorem gbTow_T_low (k : ℕ) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S Ga.gaW)
    (hfix : upsilon l = l) : cdTheta S l (cdCode S l) = xtOrec (gbTK k).sys l := by
  obtain ⟨h1, h2, h3, -⟩ := gbTow_order (S := S)
  have hlW : l < xtB1 gbUSys := hl.trans h1
  have hl0 : l < xtB1 (gbTK 0).sys := (hlW.trans h2).trans h3
  rw [gbTow_eq0 k hr.1 hl0, gbTow_eqW hr.1 hlW]
  have hlT : l < lpTowFam.famSup := by rw [(Ga.gaTowSup (S := S)).1]; exact hl
  obtain ⟨j, hj⟩ := lpTowFam.famLt hlT
  rw [gb_tow_eq j hr.1 hj]
  exact Ga.gaTowT_fix j hr hj hfix

omit S in
/-- **Theorem BLK^O below `υ` of `sup_k Λ⁺(gbTK k)`** in `R₂^C`, with the exact reaches `lh(ρ_λ) = δ_λ + O_k(λ)`. -/
theorem gbTow_blk :
    (∀ c d, c < d → d < upsilon gbTowFam.famSup → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < gbTowFam.famSup ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → ∀ k, l < xtB1 (gbTK k).sys →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec (gbTK k).sys l)) ∧
    (∀ α < upsilon gbTowFam.famSup, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  gbTowFam.famBlk

/-- **ENUM-REACH at every non-fixed restart of the range below `sup_k Λ⁺(gbTK k)`.** -/
theorem gbTow_init {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < gbTowFam.famSup) (hfix : l < upsilon l) :
    CdUpper S l ∧ CdLower S l :=
  gbTowFam.famInit hr hl hfix

/-- **CapV at every non-fixed restart of the range below `sup_k Λ⁺(gbTK k)`.** -/
theorem gbTow_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < gbTowFam.famSup) (hfix : l < upsilon l) :
    CdCapV S l :=
  gbTowFam.famCapV hr hl hfix

/-- **The successor road past the second tower**: UPPER and LOWER asked only at `λ ≥ sup_k Λ⁺(gbTK k)`, the
notation hypothesis only at the fixed points in `[ι(Γ_{Ω₁+ω}), sup_k Λ⁺(gbTK k))`, CapV only at the outer restarts
`λ ≥ ι(Γ_{Ω₁+ω})`, (CL), EQ, TCrest, (EMB₂). -/
theorem gbTowRoad (hU : ∀ l, CdRange S l → gbTowFam.famSup ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → gbTowFam.famSup ≤ l → CdLower S l)
    (hT : ∀ k l, CdRange S l → iota S Ga.gaW ≤ l → l < xtB1 (gbTK k).sys → upsilon l = l →
      cdTheta S l (cdCode S l) = xtOrec (gbTK k).sys l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut gbTowFam.famSup l → iota S Ga.gaW ≤ l →
      CdCapV S l)
    (hC : CdCL S) (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  refine gbTowFam.famRoad3 hU hL (fun k l hr hlk hfix => ?_) (fun l hr hlω hout => ?_) hC hEQ hrest hB2
  · rcases lt_or_ge l (iota S Ga.gaW) with h | h
    · exact gbTow_T_low k hr h hfix
    · exact hT k l hr h hlk hfix
  · rcases lt_or_ge l (iota S Ga.gaW) with h | h
    · exact Ga.gaTowCapV hr h
    · exact hV l hr hlω hout h

end Googology.Trans.PoR.InaccPsi.R2.Gb

import Googology.Trans.PoR.InaccPsi.R2.GbTow
import Googology.Trans.PoR.InaccPsi.R2.GbLoc

/-!
# The limit base, its ladder and the second tower, located against `L(0)`

With the codes of `R2.GbAt` (atoms `Γ_{Ω₁+1+k}`, `Γ_{Ω₁+ω+k}`), THEOREM UNI `gbUniTh` and the frontier lemma
`gbB1_eq` of `R2.GbFr`:

* `gb_gk_th` (**`ϑʸ(Ω₁·Ω₁ + k) = Θ_y(Γ_{Ω₁+1+k})`**), `gbW_th` (**`ϑʸ(Ω₁·Ω₁ + ω) = Θ_y(Γ_{Ω₁+ω})`**), `gbW_poly`
  (**`gbUSys` has terms for every code below `Γ_{Ω₁+ω}`**);
* `gbW_loc` (**`Λ⁺(gbUSys) = ι(Γ_{Ω₁+ω}·ω)`**), `gbWLad_loc` (**`Λ⁺(lpSys gbWB n) = ι(cQ(Γ_{Ω₁+ω}) n·ω)`**),
  `gbWFam_loc` (**`Λ^W = ι(Γ_{Ω₁+ω+1})`, `υ` of it `= P(Γ_{Ω₁+ω+1}) < L(0)`**), `gbWEnum` / `gbWCapV` (**ENUM-REACH and
  CapV at every restart of the range below `Λ^W`, fixed points included**), `gbWRoad`;
* `gbTowTh` (**the top of `gbTK k` reads `Γ_{Ω₁+ω+1+k}` and `gbTK k` has terms for every code below it**),
  `gbTow_loc` (**`Λ⁺(gbTK k) = ι(Γ_{Ω₁+ω+1+k}·ω)`**), `gbTowSup` (**`sup_k Λ⁺(gbTK k) = ι(Γ_{Ω₁+ω·2})`, `υ` of it `=
  P(Γ_{Ω₁+ω·2}) < L(0)`**), `gbTowT_fix`, `gbTowEnum` / `gbTowCapV` (**ENUM-REACH and CapV at every restart of the
  range below `ι(Γ_{Ω₁+ω·2})`, fixed points included**), `gbTowRoadL` (UPPER, LOWER, CapV asked only at
  `λ ≥ ι(Γ_{Ω₁+ω·2})`), `gbTow_fr_order` (**the order of all the new frontiers and of `L(0) = m* ≤ L(k+1) < L(ω) <
  L(ω+1)`**).

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gb

open Googology.Trans.PoR.InaccPsi.R2.Ga
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp

/-! ## The readings of the tops -/

/-- **`ϑʸ(Ω₁·Ω₁ + k) = Θ_y(Γ_{Ω₁+1+k})`** at every strongly critical `y < Ω₁`. -/
theorem gb_gk_th (S : InaccSeq.{0}) {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) (k : ℕ) :
    gk k y = gxTh y gaAt (gaG k) := by
  cases k with
  | zero => rw [gk_zero_eq (gg_SC_eps hy) (lp_y1 hy1), gaTh_G0 S hy hy1]
  | succ k => exact (gaTow S k).1 y hy hy1

/-- **`ϑʸ(Ω₁·Ω₁ + ω) = Θ_y(Γ_{Ω₁+ω})`** at every strongly critical `y < Ω₁`. -/
theorem gbW_th (S : InaccSeq.{0}) {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) : gbW y = gxTh y gbAt gaW := by
  rw [gbTh_W S, gbW_sup (gg_SC_eps hy) (lp_y1 hy1)]
  exact iSup_congr fun k => gb_gk_th S hy hy1 k

/-- **The union of the tower has terms for every code below `Γ_{Ω₁+ω}`.** -/
theorem gbW_poly (S : InaccSeq.{0}) : GbPoly gbUSys gaW := by
  refine gbPoly_of_ga S le_rfl ?_
  intro Z c hc hcW
  rw [gaW_sup S] at hcW
  obtain ⟨k, hk⟩ := Ordinal.lt_iSup_iff.1 hcW
  obtain ⟨s, hs⟩ := (gaTow S k).2 Z c hc (hk.trans (gaG_lt_succ S k))
  exact ⟨⟨k, s⟩, hs⟩

theorem gbW_atom : ∀ Z, SC Z → GxCl Z gbAt gaW := fun _ _ => GxCl.atom (Or.inr ⟨0, rfl⟩)

theorem gbW_eN {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : eN x < gbW x :=
  (ga_eN_lt_gk 0 hx hx1).trans (gk_lt_W hx hx1 0)

variable {S : InaccSeq.{0}}

/-! ## The limit base and its ladder -/

/-- **`Λ⁺(gbUSys) = ι(Γ_{Ω₁+ω}·ω)`, `ρ` of it `= P(Γ_{Ω₁+ω}·ω) < L(0)`.** -/
theorem gbW_loc : xtB1 gbUSys = iota S (gaW * ω) ∧ upsilon (xtB1 gbUSys) = Pv S (gaW * ω) ∧
    Pv S (gaW * ω) < Nc.ncL S 0 := by
  have h := gbB1_eq (S := S) (X := gbUSys) (T := gaW) (gaW_lt_V S).le (gbW_poly S)
    (fun y hy hy1 => gbW_th S hy hy1) gbW_atom (ga_Om1_lt_W S).le (fun _ hx hx1 => gbW_eN hx hx1) gb_topPkg
  rwa [gg_SC_eps (gaW_SC S)] at h

/-- **`Λ⁺(lpSys gbWB n) = ι(cQ(Γ_{Ω₁+ω}) n·ω)`, `ρ` of it `= P(…) < L(0)`.** -/
theorem gbWLad_loc (n : ℕ) : xtB1 (lpSys gbWB n) = iota S (cQ gaW n * ω) ∧
    upsilon (xtB1 (lpSys gbWB n)) = Pv S (cQ gaW n * ω) ∧ Pv S (cQ gaW n * ω) < Nc.ncL S 0 :=
  gbB1_loc S (B := gbWB) gbW_atom (ga_Om1_lt_W S).le (gg_SC_eps (gaW_SC S)) (fun y hy hy1 => gbW_th S hy hy1)
    (gbW_poly S) (fun _ hx hx1 => gbW_eN hx hx1) n

theorem gbW_cQs (S : InaccSeq.{0}) : cQs gaW = gbH 1 := gb_cQs_eq_H S (le_rfl : gbH 0 ≤ gaW) (gbH_lt_succ S 0)

/-- **`Λ^W = sup_n Λ⁺(lpSys gbWB n) = ι(Γ_{Ω₁+ω+1})`, `υ` of it `= P(Γ_{Ω₁+ω+1}) < L(0)`.** -/
theorem gbWFam_loc : (lpFam gbWB).famSup = iota S (gbH 1) ∧ upsilon (lpFam gbWB).famSup = Pv S (gbH 1) ∧
    Pv S (gbH 1) < Nc.ncL S 0 := by
  have h := gbFam_loc S (B := gbWB) gbW_atom (ga_Om1_lt_W S).le (gg_SC_eps (gaW_SC S))
    (fun y hy hy1 => gbW_th S hy hy1) (gbW_poly S) (fun _ hx hx1 => gbW_eN hx hx1)
  rwa [gbW_cQs S] at h

/-- **ENUM-REACH at every restart of the range below `Λ^W = ι(Γ_{Ω₁+ω+1})`**, fixed points included. -/
theorem gbWEnum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < (lpFam gbWB).famSup) : CdUpper S l ∧ CdLower S l :=
  gbLEnum S (B := gbWB) gbW_atom (ga_Om1_lt_W S).le (gg_SC_eps (gaW_SC S)) (fun y hy hy1 => gbW_th S hy hy1)
    (gbW_poly S) (fun _ hx hx1 => gbW_eN hx hx1) hr hl

/-- **CapV at every restart of the range below `Λ^W`**, fixed points included. -/
theorem gbWCapV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < (lpFam gbWB).famSup) : CdCapV S l :=
  gbLCapV S (B := gbWB) gbW_atom (ga_Om1_lt_W S).le (gg_SC_eps (gaW_SC S)) (fun y hy hy1 => gbW_th S hy hy1)
    (gbW_poly S) (fun _ hx hx1 => gbW_eN hx hx1) hr hl

/-- **The successor road over the limit base**: UPPER, LOWER and CapV asked only at `λ ≥ Λ^W = ι(Γ_{Ω₁+ω+1})`, (CL),
EQ, TCrest, (EMB₂). -/
theorem gbWRoad (hU : ∀ l, CdRange S l → (lpFam gbWB).famSup ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → (lpFam gbWB).famSup ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → (lpFam gbWB).famSup ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  gbBaseRoad S (B := gbWB) gbW_atom (ga_Om1_lt_W S).le (gg_SC_eps (gaW_SC S)) (fun y hy hy1 => gbW_th S hy hy1)
    (gbW_poly S) (fun _ hx hx1 => gbW_eN hx hx1) hU hL hV hC hEQ hrest hB2

/-! ## The second tower -/

theorem gbOff_gt (k : ℕ) : ω < gbOff k := by
  rw [gbOff_eq]; exact (lt_add_one ω).trans_le le_self_add

omit S in
/-- **The second tower in the codes**: the top of `gbTK k` reads `gbH (k+1) = Γ_{Ω₁+ω+1+k}`, and `gbTK k` has terms
for every code below it. -/
theorem gbTowTh (S : InaccSeq.{0}) : ∀ k : ℕ,
    (∀ y, SC y → y < Om 1 → (gbTK k).E y = gxTh y gbAt (gbH (k + 1))) ∧ GbPoly (gbTK k).sys (gbH (k + 1))
  | 0 => by
    have hKE : ∀ y, SC y → y < Om 1 → (gbTB 0).K.E y = gxTh y gbAt gaW := fun y hy hy1 => gbW_th S hy hy1
    have hKP : GbPoly (gbTB 0).K.sys gaW := gbW_poly S
    refine ⟨fun y hy hy1 => ?_, ?_⟩
    · have h := gbLim_top S gbW_atom hKE (gbTH 0) hy hy1
      rw [gbW_cQs S] at h
      exact h
    · have h := gbLim_poly S gbW_atom (ga_Om1_lt_W S).le hKE hKP (gbTH 0)
      rw [gbW_cQs S] at h
      exact h
  | k + 1 => by
    obtain ⟨ihE, ihP⟩ := gbTowTh S k
    have hc : ∀ Z, SC Z → GxCl Z gbAt (gbH (k + 1)) := fun _ _ => GxCl.atom (Or.inr ⟨k + 1, rfl⟩)
    have hcO : Om 1 ≤ gbH (k + 1) := (gbH_Om1_lt S _).le
    have hKE : ∀ y, SC y → y < Om 1 → (gbTB (k + 1)).K.E y = gxTh y gbAt (gbH (k + 1)) := ihE
    have hKP : GbPoly (gbTB (k + 1)).K.sys (gbH (k + 1)) := ihP
    have hQ := gb_cQs_eq_H S le_rfl (gbH_lt_succ S (k + 1))
    refine ⟨fun y hy hy1 => ?_, ?_⟩
    · have h := gbLim_top S hc hKE (gbTH (k + 1)) hy hy1
      rw [hQ] at h
      exact h
    · have h := gbLim_poly S hc hcO hKE hKP (gbTH (k + 1))
      rw [hQ] at h
      exact h

theorem gbTK_eN (k : ℕ) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : eN x < (gbTK k).sys.top x :=
  (gbW_eN hx hx1).trans (gq_lt hx hx1 ((gbTH k).cst x hx) (gbOff_gt k))

/-- **`Λ⁺(gbTK k) = ι(Γ_{Ω₁+ω+1+k}·ω)`, `ρ` of it `= P(Γ_{Ω₁+ω+1+k}·ω) < L(0)`.** -/
theorem gbTow_loc (k : ℕ) : xtB1 (gbTK k).sys = iota S (gbH (k + 1) * ω) ∧
    upsilon (xtB1 (gbTK k).sys) = Pv S (gbH (k + 1) * ω) ∧ Pv S (gbH (k + 1) * ω) < Nc.ncL S 0 := by
  have h := gbB1_eq (S := S) (X := (gbTK k).sys) (T := gbH (k + 1)) (gbH_lt_V S _).le (gbTowTh S k).2
    (fun y hy hy1 => (gbTowTh S k).1 y hy hy1) (fun _ _ => GxCl.atom (Or.inr ⟨k + 1, rfl⟩)) (gbH_Om1_lt S _).le
    (fun _ hx hx1 => gbTK_eN k hx hx1) (XtLay.topPkg (gbTK k))
  rwa [gg_SC_eps (gbH_SC S _)] at h

/-- **`sup_k Λ⁺(gbTK k) = ι(Γ_{Ω₁+ω·2})`, `υ` of it `= P(Γ_{Ω₁+ω·2}) < L(0)`.** -/
theorem gbTowSup : gbTowFam.famSup = iota S gbV ∧ upsilon gbTowFam.famSup = Pv S gbV ∧
    Pv S gbV < Nc.ncL S 0 := by
  have hSC := gbV_SC S
  have hlim : IsSuccLimit gbV := hSC.isSuccLimit
  have hEs : ω ^ gbV = gbV := Low.opow_eq_self_of_SC hSC
  have hstep : ∀ k : ℕ, gbH (k + 1) * ω < gbV := fun k =>
    InE.mul_lt hEs (gbH_lt_V S _) (omega0_lt_inE hEs)
  have heq : gbTowFam.famSup = iota S gbV := by
    refine le_antisymm (Ordinal.iSup_le fun k => ?_) ?_
    · show xtB1 (gbTK k).sys ≤ _
      rw [(gbTow_loc (S := S) k).1]
      exact iota_mono _ _ (hstep k).le
    · rw [iota_limit hlim]
      refine ciSup_le' fun e => ?_
      have he : e.1 < ⨆ k, gbH k := by rw [← gbV_sup S]; exact e.2
      obtain ⟨k, hk⟩ := Ordinal.lt_iSup_iff.1 he
      have h1 : e.1 < gbH (k + 1) * ω :=
        (hk.trans (gbH_lt_succ S k)).trans_le (le_mul_of_one_le_right zero_le one_lt_omega0.le)
      calc iota S e.1 ≤ iota S (gbH (k + 1) * ω) := iota_mono _ _ h1.le
        _ = xtB1 (gbTK k).sys := (gbTow_loc k).1.symm
        _ ≤ gbTowFam.famSup := (gbTowFam.famBd_lt k).le
  have hups : upsilon gbTowFam.famSup = Pv S gbV := by rw [heq, ups_iota S]
  exact ⟨heq, hups, ga_Pv_lt_L0 S (gbV_lt_Om2 S).le⟩

/-- **The notation hypothesis at every fixed point of the range below `Λ⁺(gbTK k)`** (THEOREM UNI `gbUniTh`). -/
theorem gbTowT_fix (k : ℕ) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 (gbTK k).sys)
    (hfix : upsilon l = l) : cdTheta S l (cdCode S l) = xtOrec (gbTK k).sys l := by
  have hlt : l < iota S (ω ^ gbH (k + 1) * ω) := by
    rw [gg_SC_eps (gbH_SC S _), ← (gbTow_loc k).1]; exact hl
  exact gbUniTh (gbH_lt_V S _).le (gbTowTh S k).2 hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) hlt)

/-- **ENUM-REACH at every restart of the range below `ι(Γ_{Ω₁+ω·2}) = sup_k Λ⁺(gbTK k)`**, fixed points included. -/
theorem gbTowEnum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S gbV) : CdUpper S l ∧ CdLower S l := by
  rw [← (gbTowSup (S := S)).1] at hl
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact gbTow_init hr hl hnf
  · obtain ⟨k, hk⟩ := gbTowFam.famLt hl
    exact (gbTowFam.famIff k hr.1 hk).2.2.2 (gbTowT_fix k hr hk hfx.symm)

/-- **CapV at every restart of the range below `ι(Γ_{Ω₁+ω·2})`**, fixed points included. -/
theorem gbTowCapV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S gbV) : CdCapV S l := by
  have hl' := hl
  rw [← (gbTowSup (S := S)).1] at hl'
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact gbTow_capV hr hl' hnf
  · obtain ⟨k, hk⟩ := gbTowFam.famLt hl'
    exact Lk.lkCapV_fix (XtLay.topPkg (gbTK k)) hr hk hfx.symm (gbTowEnum hr hl)

/-- **The successor road past the second tower**: UPPER, LOWER and CapV asked only at the range restarts
`λ ≥ ι(Γ_{Ω₁+ω·2})`, (CL), EQ, TCrest, (EMB₂). -/
theorem gbTowRoadL (hU : ∀ l, CdRange S l → iota S gbV ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S gbV ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gbV ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hs := (gbTowSup (S := S)).1
  refine gbTowFam.famRoad3 (fun l hr h => hU l hr (hs ▸ h)) (fun l hr h => hL l hr (hs ▸ h))
    (fun k l hr hlk hfix => gbTowT_fix k hr hlk hfix) (fun l hr hlω _ => ?_) hC hEQ hrest hB2
  rcases le_or_gt (iota S gbV) l with h | h
  · exact hV l hr hlω h
  · exact gbTowCapV hr h

/-- **Where the new frontiers lie**: `ι(Γ_{Ω₁+ω}) < ι(Γ_{Ω₁+ω}·ω) = Λ⁺(gbUSys) < Λ^W = ι(Γ_{Ω₁+ω+1}) < Λ⁺(gbTK 0) =
ι(Γ_{Ω₁+ω+1}·ω) < sup_k Λ⁺(gbTK k) = ι(Γ_{Ω₁+ω·2})`, `P(Γ_{Ω₁+ω·2}) < L(0) = m* ≤ L(k+1) < L(ω) < L(ω+1)`, and
`ι(Γ_{Ω₁+ω·2}) < L(ω+1)`, unconditionally. -/
theorem gbTow_fr_order (k : ℕ) :
    iota S gaW < xtB1 gbUSys ∧ xtB1 gbUSys = iota S (gaW * ω) ∧ xtB1 gbUSys < (lpFam gbWB).famSup ∧
    (lpFam gbWB).famSup = iota S (gbH 1) ∧ (lpFam gbWB).famSup < xtB1 (gbTK 0).sys ∧
    xtB1 (gbTK 0).sys = iota S (gbH 1 * ω) ∧ xtB1 (gbTK 0).sys < iota S gbV ∧
    upsilon (iota S gbV) < Nc.ncL S 0 ∧ Nc.ncL S 0 ≤ Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ∧
    Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) < Nc.ncL S ω ∧ Nc.ncL S ω < Nc.ncL S (ω + 1) ∧
    iota S gbV < Nc.ncL S (ω + 1) := by
  obtain ⟨h0, h1, h2⟩ := phL_chain (S := S) k
  obtain ⟨hs, hups, hlt⟩ := gbTowSup (S := S)
  obtain ⟨o1, o2, o3, o4, -⟩ := gbTow_order (S := S)
  have hU : upsilon (iota S gbV) < Nc.ncL S 0 := by rw [← hs, hups]; exact hlt
  refine ⟨o1, (gbW_loc (S := S)).1, o2, (gbWFam_loc (S := S)).1, o3, (gbTow_loc (S := S) 0).1, hs ▸ o4, hU, h0, h1,
    h2, ?_⟩
  exact upsilon_normal.strictMono.le_apply.trans_lt (((hU.trans_le h0).trans h1).trans h2)

end Googology.Trans.PoR.InaccPsi.R2.Gb

import Googology.Trans.PoR.InaccPsi.R2.GaLoc

/-!
# The tower of bases located: `Λ⁺(lpTK k) = ι(Γ_{Ω₁+2+k}·ω)`, `sup_k Λ⁺(lpTK k) = ι(Γ_{Ω₁+ω})`, all below `L(0)`

`R2.LpTow` builds the tower `lpTK k` (top `ϑˣ(Ω₁·Ω₁ + k + 1) = Γ_{x+k+2}`) and leaves its frontiers unlocated: the code
calculus `LgCl` stops below `Γ_{Ω₁+2}`.  With the codes `GxCl Z gaAt` (atoms `gaG k = Γ_{Ω₁+1+k}`):

* `cQ_eq_cP`, `gaZ_cQs` (`cQs (ε_{Γ_{Ω₁+1}+Ω₁}) = gaG 1`), `gaZ_hc`, `gaZ_KE`, `gaZ_KP` (the base `lpZB` in the new
  codes);
* `gaTow` (**for every `k`: the top of `lpTK k` reads `gaG (k+1)`, `gk (k+1) y = Θ_y(Γ_{Ω₁+2+k})`, and `lpTK k` has
  terms for every code below `Γ_{Ω₁+2+k}`**; by induction, the step is `gaLim` over the base `lpTB (k+1)` whose code
  `gaG (k+1)` is strongly critical);
* `gaTow_loc` (**`Λ⁺(lpTK k) = ι(Γ_{Ω₁+2+k}·ω)`, `ρ` of it `= P(…) < L(0)`**), `gaTowStage_loc` (**the stages over the
  base `lpTB (k+1)`: `Λ⁺(lpSys (lpTB (k+1)) n) = ι(cQ (Γ_{Ω₁+2+k}) n·ω)`**), `gaTowSup` (**`sup_k Λ⁺(lpTK k) =
  ι(Γ_{Ω₁+ω})`, `υ` of it `= P(Γ_{Ω₁+ω}) < L(0)`**);
* `gaTowT_fix` (**the notation hypothesis at every fixed point of the range below `Λ⁺(lpTK k)`**), `gaTowEnum`
  (**ENUM-REACH at every restart of the range below `ι(Γ_{Ω₁+ω})`, fixed points included**), `gaTowCapV` (**CapV
  there**), `gaTowRoad` (**the road with UPPER, LOWER and CapV asked only at `λ ≥ ι(Γ_{Ω₁+ω})`**), `gaTow_fr_order`.

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ga

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Lx

/-! ## The base `lpZB` in the new codes -/

/-- At a code `c < φ(c, 0)` the codes `cQ` are the codes `cP` of `R2.LpPoly`. -/
theorem cQ_eq_cP {c : Ordinal.{0}} (hcv : c < veblen c 0) : ∀ n : ℕ, cQ c n = cP c n
  | 0 => rfl
  | n + 1 => by
    have ih := cQ_eq_cP hcv n
    rw [cQ_succ, ih, bQ_of_not (fun h => absurd h (cP_lt_v hcv n).ne')]
    rfl

theorem gaZ_lt_G1 (S : InaccSeq.{0}) : lxZC < gaG 1 := by
  rw [gaG_one, ← lpZ_cPs S]; exact c_lt_cPs lpZ_cv

theorem gaZ_cQs (S : InaccSeq.{0}) : cQs lxZC = gaG 1 :=
  cQs_eq_G S (k := 0) lpZ_G_lt.le (gaZ_lt_G1 S)

theorem gaZ_hc : ∀ Z, SC Z → GxCl Z gaAt lxZC := fun Z hZ => gaCl_of_lg (lpZ_hc Z hZ)

theorem gaZ_KE (S : InaccSeq.{0}) : ∀ y, SC y → y < Om 1 → lpZB.K.E y = gxTh y gaAt lxZC := fun y hy hy1 => by
  rw [lpZ_KE y hy hy1, gaTh_eq_lgTh S (gaZ_lt_G1 S).le]

theorem gaZ_KP (S : InaccSeq.{0}) : GaPoly lpZB.K.sys lxZC := gaPoly_of_lg S (gaZ_lt_G1 S).le lxZ_poly

/-! ## The tower: tops and terms -/

/-- **The tower in the new codes**: the top of `lpTK k` reads `gaG (k+1) = Γ_{Ω₁+2+k}`, and `lpTK k` has terms for every
code below it. -/
theorem gaTow (S : InaccSeq.{0}) : ∀ k : ℕ,
    (∀ y, SC y → y < Om 1 → (lpTK k).E y = gxTh y gaAt (gaG (k + 1))) ∧ GaPoly (lpTK k).sys (gaG (k + 1))
  | 0 => by
    refine ⟨fun y hy hy1 => ?_, ?_⟩
    · have h := gaLim_top S gaZ_hc (gaZ_KE S) lpZ_limH hy hy1
      rw [gaZ_cQs S] at h
      exact h
    · have h := gaLim_poly S gaZ_hc lx_Om1_le_ZC (gaZ_KE S) (gaZ_KP S) lpZ_limH
      rw [gaZ_cQs S] at h
      exact h
  | k + 1 => by
    obtain ⟨ihE, ihP⟩ := gaTow S k
    have hc : ∀ Z, SC Z → GxCl Z gaAt (gaG (k + 1)) := fun _ _ => GxCl.atom ⟨k + 1, rfl⟩
    have hcO : Om 1 ≤ gaG (k + 1) := (gaG_Om1_lt S _).le
    have hKE : ∀ y, SC y → y < Om 1 → (lpTB (k + 1)).K.E y = gxTh y gaAt (gaG (k + 1)) := ihE
    have hKP : GaPoly (lpTB (k + 1)).K.sys (gaG (k + 1)) := ihP
    have hQ := cQs_eq_G S le_rfl (gaG_lt_succ S (k + 1))
    refine ⟨fun y hy hy1 => ?_, ?_⟩
    · have h := gaLim_top S hc hKE (lpTH (k + 1)) hy hy1
      rw [hQ] at h
      exact h
    · have h := gaLim_poly S hc hcO hKE hKP (lpTH (k + 1))
      rw [hQ] at h
      exact h

theorem gk_zero_eq {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : gk 0 x = lgG x := by
  show vt x (Om1 * Om1 + ((0 : ℕ) : Ordinal.{0})) = lgG x
  rw [Nat.cast_zero, lgV_add_zero, lgV_eq hx hx1]

theorem ga_eN_lt_gk (k : ℕ) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : eN x < gk k x := by
  have h : eN x < lgG x := gT_lt_lgG hx hx1 0
  rw [← gk_zero_eq hx hx1] at h
  exact h.trans_le (gk_mono hx hx1 (Nat.zero_le k))

variable {S : InaccSeq.{0}}

/-- **`Λ⁺(lpTK k) = ι(Γ_{Ω₁+2+k}·ω)`, `ρ` of it `= P(Γ_{Ω₁+2+k}·ω) < L(0)`.** -/
theorem gaTow_loc (k : ℕ) : xtB1 (lpTK k).sys = iota S (gaG (k + 1) * ω) ∧
    upsilon (xtB1 (lpTK k).sys) = Pv S (gaG (k + 1) * ω) ∧ Pv S (gaG (k + 1) * ω) < Nc.ncL S 0 := by
  have h := gaB1_eq (S := S) (X := (lpTK k).sys) (T := gaG (k + 1)) (gaG_lt_W S _).le (gaTow S k).2
    (fun y hy hy1 => (gaTow S k).1 y hy hy1) (fun _ _ => GxCl.atom ⟨k + 1, rfl⟩) (gaG_Om1_lt S _).le
    (fun _ hx hx1 => ga_eN_lt_gk (k + 1) hx hx1) (XtLay.topPkg (lpTK k))
  rwa [gg_SC_eps (gaG_SC S _)] at h

/-- **The stages over the base `lpTB (k+1)`** (top `Γ_{x+k+2}`, strongly critical code `Γ_{Ω₁+2+k}`):
`Λ⁺(lpSys (lpTB (k+1)) n) = ι(cQ (Γ_{Ω₁+2+k}) n·ω) < L(0)`, `cQ c 1 = φ(c, 1)`, `cQ c (n+2) = φ(cQ c (n+1), 0)`. -/
theorem gaTowStage_loc (k n : ℕ) : xtB1 (lpSys (lpTB (k + 1)) n) = iota S (cQ (gaG (k + 1)) n * ω) ∧
    upsilon (xtB1 (lpSys (lpTB (k + 1)) n)) = Pv S (cQ (gaG (k + 1)) n * ω) ∧
    Pv S (cQ (gaG (k + 1)) n * ω) < Nc.ncL S 0 :=
  gaB1_loc S (B := lpTB (k + 1)) (fun _ _ => GxCl.atom ⟨k + 1, rfl⟩) (gaG_Om1_lt S _).le
    (gg_SC_eps (gaG_SC S _)) (gaTow S k).1 (gaTow S k).2 (fun _ hx hx1 => ga_eN_lt_gk (k + 1) hx hx1) n

/-- **`sup_k Λ⁺(lpTK k) = ι(Γ_{Ω₁+ω})`, `υ` of it `= P(Γ_{Ω₁+ω}) < L(0)`.** -/
theorem gaTowSup : lpTowFam.famSup = iota S gaW ∧ upsilon lpTowFam.famSup = Pv S gaW ∧
    Pv S gaW < Nc.ncL S 0 := by
  have hSC := gaW_SC S
  have hlim : IsSuccLimit gaW := hSC.isSuccLimit
  have hEs : ω ^ gaW = gaW := Low.opow_eq_self_of_SC hSC
  have hstep : ∀ k : ℕ, gaG (k + 1) * ω < gaW := fun k =>
    InE.mul_lt hEs (gaG_lt_W S _) (omega0_lt_inE hEs)
  have heq : lpTowFam.famSup = iota S gaW := by
    refine le_antisymm (Ordinal.iSup_le fun k => ?_) ?_
    · show xtB1 (lpTK k).sys ≤ _
      rw [(gaTow_loc (S := S) k).1]
      exact iota_mono _ _ (hstep k).le
    · rw [iota_limit hlim]
      refine ciSup_le' fun e => ?_
      have he : e.1 < ⨆ k, gaG k := by rw [← gaW_sup S]; exact e.2
      obtain ⟨k, hk⟩ := Ordinal.lt_iSup_iff.1 he
      have h1 : e.1 < gaG (k + 1) * ω :=
        (hk.trans (gaG_lt_succ S k)).trans_le (le_mul_of_one_le_right zero_le one_lt_omega0.le)
      calc iota S e.1 ≤ iota S (gaG (k + 1) * ω) := iota_mono _ _ h1.le
        _ = xtB1 (lpTK k).sys := (gaTow_loc k).1.symm
        _ ≤ lpTowFam.famSup := (lpTowFam.famBd_lt k).le
  have hups : upsilon lpTowFam.famSup = Pv S gaW := by rw [heq, ups_iota S]
  exact ⟨heq, hups, ga_Pv_lt_L0 S (gaW_lt_Om2 S).le⟩

/-- **The notation hypothesis at every fixed point of the range below `Λ⁺(lpTK k)`** (THEOREM UNI `gaUniTh`). -/
theorem gaTowT_fix (k : ℕ) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 (lpTK k).sys)
    (hfix : upsilon l = l) : cdTheta S l (cdCode S l) = xtOrec (lpTK k).sys l := by
  have hlt : l < iota S (ω ^ gaG (k + 1) * ω) := by
    rw [gg_SC_eps (gaG_SC S _), ← (gaTow_loc k).1]; exact hl
  exact gaUniTh (gaG_lt_W S _).le (gaTow S k).2 hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) hlt)

/-- **ENUM-REACH at every restart of the range below `ι(Γ_{Ω₁+ω}) = sup_k Λ⁺(lpTK k)`**, fixed points included. -/
theorem gaTowEnum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S gaW) : CdUpper S l ∧ CdLower S l := by
  rw [← (gaTowSup (S := S)).1] at hl
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact lpTow_init hr hl hnf
  · obtain ⟨k, hk⟩ := lpTowFam.famLt hl
    exact (lpTowFam.famIff k hr.1 hk).2.2.2 (gaTowT_fix k hr hk hfx.symm)

/-- **CapV at every restart of the range below `ι(Γ_{Ω₁+ω})`**, fixed points included. -/
theorem gaTowCapV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S gaW) : CdCapV S l := by
  have hl' := hl
  rw [← (gaTowSup (S := S)).1] at hl'
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact lpTow_capV hr hl' hnf
  · obtain ⟨k, hk⟩ := lpTowFam.famLt hl'
    exact Lk.lkCapV_fix (XtLay.topPkg (lpTK k)) hr hk hfx.symm (gaTowEnum hr hl)

/-- **The successor road past the tower**: UPPER, LOWER and CapV asked only at the range restarts `λ ≥ ι(Γ_{Ω₁+ω})`,
(CL), EQ, TCrest, (EMB₂). -/
theorem gaTowRoad (hU : ∀ l, CdRange S l → iota S gaW ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S gaW ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gaW ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hs := (gaTowSup (S := S)).1
  refine lpTowFam.famRoad3 (fun l hr h => hU l hr (hs ▸ h)) (fun l hr h => hL l hr (hs ▸ h))
    (fun k l hr hlk hfix => gaTowT_fix k hr hlk hfix) (fun l hr hlω _ => ?_) hC hEQ hrest hB2
  rcases le_or_gt (iota S gaW) l with h | h
  · exact hV l hr hlω h
  · exact gaTowCapV hr h

/-- **Where the tower lies**: `ι(Γ') < Λ⁺(lpTK 0) < sup_k Λ⁺(lpTK k) = ι(Γ_{Ω₁+ω})`, `P(Γ_{Ω₁+ω}) < L(0) = m* ≤ L(k+1)
< L(ω) < L(ω+1)`, and `ι(Γ_{Ω₁+ω}) < L(ω+1)`, unconditionally. -/
theorem gaTow_fr_order (k : ℕ) :
    iota S lgGam' < xtB1 (lpTK 0).sys ∧ xtB1 (lpTK 0).sys < iota S gaW ∧
    upsilon (iota S gaW) < Nc.ncL S 0 ∧ Nc.ncL S 0 ≤ Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ∧
    Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) < Nc.ncL S ω ∧ Nc.ncL S ω < Nc.ncL S (ω + 1) ∧
    iota S gaW < Nc.ncL S (ω + 1) := by
  obtain ⟨h0, h1, h2⟩ := phL_chain (S := S) k
  obtain ⟨hs, hups, hlt⟩ := gaTowSup (S := S)
  have hU : upsilon (iota S gaW) < Nc.ncL S 0 := by rw [← hs, hups]; exact hlt
  refine ⟨(lpTow_gt (S := S)).1, hs ▸ (lpTow_gt (S := S)).2, hU, h0, h1, h2, ?_⟩
  exact upsilon_normal.strictMono.le_apply.trans_lt (((hU.trans_le h0).trans h1).trans h2)

end Googology.Trans.PoR.InaccPsi.R2.Ga

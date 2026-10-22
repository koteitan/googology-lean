import Googology.Trans.PoR.InaccPsi.R2.LpLim

/-!
# The tower of bases: `ε_{Γ(x)+x}`, `Γ_{x+2}`, `Γ_{x+3}`, …, and the limit `sup_k Λ⁺(K_k)`

Iterating `R2.LpLim` from the base `lpZB` (top `ε_{Γ(x)+x} ∈ [Γ_{x+1}, Γ_{x+2})`):

* `lpZ_limH` (**`Γ_{x+1} ≤ ε_{Γ(x)+x} < ϑˣ(Ω₁·Ω₁ + 1)`**), `lpTBp k` (the `k`-th base with its hypothesis
  `LpLimH (lpTB k) (k + 1)`), `lpTK k = lpLim (lpTB k) (k + 1)` (**the `k`-th limit layer, top `ϑˣ(Ω₁·Ω₁ + k + 1) =
  Γ_{x+k+2}`**), `lpTB_succ` (`lpTB (k+1)` is the base `lpTK k`);
* `lpTow_lt` (**`Λ⁺(lpTK k) < Λ⁺(lpTK (k+1))`**), `lpTow_eq0` (**`O_{lpTK k} = O_{lpTK 0}` below `Λ⁺(lpTK 0)`**),
  `lpTowFam : XtFam` (`LyLim` at the limit: bounds `Λ⁺(lpTK k)`), `lpTow_gt` (**`ι(Γ_{Ω₁+2}) < Λ⁺(lpTK 0) <
  sup_k Λ⁺(lpTK k)`**);
* `lpK0Poly` (**`lpTK 0` has terms for every code below `Γ_{Ω₁+2}`**), `lpK0T_fix` (the notation hypothesis at the fixed
  points below `Λ⁺(lpTK 0)` whose name has its last exponent `≤ Γ_{Ω₁+2}`);
* `lpTow_blk` (**BLK^O and the exact reaches below `υ` of `sup_k Λ⁺(lpTK k)`**), `lpTow_init` (**ENUM-REACH at every
  non-fixed restart of the range below it**), `lpTow_capV` (**CapV there**), `lpTowEnum_low` (**ENUM-REACH at every
  restart of the range below `ι(Γ_{Ω₁+2})`**), `lpTowRoad` (**the successor road**: UPPER/LOWER asked only at
  `λ ≥ sup_k Λ⁺(lpTK k)`, the notation hypothesis only at the fixed points in `[ι(Γ_{Ω₁+2}), sup_k Λ⁺(lpTK k))`, CapV
  only at the outer restarts).

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Lp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Ly
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp Googology.Trans.PoR.InaccPsi.R2.Lx
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm

/-- **`Γ_{x+1} ≤ ε_{Γ(x)+x} < ϑˣ(Ω₁·Ω₁ + 1)`**: the base `lpZB` satisfies the limit hypothesis with `k = 1`. -/
theorem lpZ_limH : LpLimH lpZB 1 := by
  refine ⟨fun x hx hx1 j hj => ?_, fun x hx hx1 => ?_⟩
  · obtain rfl : j = 0 := by omega
    have e : gk 0 x = lgG x := by
      show vt x (Om1 * Om1 + ((0 : ℕ) : Ordinal.{0})) = lgG x
      rw [Nat.cast_zero, lgV_add_zero, lgV_eq hx hx1]
    rw [e]
    exact (lxZE_E_lt lxZK_lg hx hx1 le_rfl).le
  · show vt x (Om1 + (lgG x + x)) < gk 1 x
    obtain ⟨-, hxG, -, hGE, -⟩ := gk_facts hx hx1 1
    have hG0 : lgG x = gk 0 x := by
      show lgG x = vt x (Om1 * Om1 + ((0 : ℕ) : Ordinal.{0}))
      rw [Nat.cast_zero, lgV_add_zero, lgV_eq hx hx1]
    obtain ⟨hGT, hxg, hG1, -, -⟩ := lgG_facts hx hx1
    have hg1 : lgG x < gk 1 x := hG0 ▸ gk_lt hx hx1 zero_lt_one
    have hsT : lgG x + x ∈ Tset x := vzT_add hx hx1 hGT (mem_T_of_le hx hx1 le_rfl)
    have hs1 : lgG x + x < Om1 := Om1_add_lt hG1 hx1
    have h1T : (1 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 (Lu.lu_one_lt_E hx).le
    have h1Ω : (1 : Ordinal.{0}) < Om1 := (Lu.lu_one_lt_E hx).trans hx1
    obtain ⟨hkT, hk1, -⟩ := gk_nat hx hx1 1
    have h := lgVt_lt_low hx hx1 h1T h1Ω hsT hs1 hkT hk1 ((Lu.lu_one_lt_E hx).trans hxG)
      ((inE_indec hGE).add_lt hg1 hxG)
    rw [mul_one] at h
    exact h

/-- **The tower of bases**: `lpTBp 0 = lpZB`, `lpTBp (k+1) = lim (lpTBp k)` with the hypothesis for `k + 1`. -/
noncomputable def lpTBp : (k : ℕ) → {B : LpB // LpLimH B (k + 1)}
  | 0 => ⟨lpZB, lpZ_limH⟩
  | k + 1 => ⟨lpLimB (lpTBp k).1 (k + 1) (lpTBp k).2, lpLimH_next (lpTBp k).1 (k + 1) (lpTBp k).2⟩

/-- The `k`-th base. -/
noncomputable def lpTB (k : ℕ) : LpB := (lpTBp k).1

theorem lpTH (k : ℕ) : LpLimH (lpTB k) (k + 1) := (lpTBp k).2

/-- **The `k`-th limit layer**, top `ϑˣ(Ω₁·Ω₁ + k + 1) = Γ_{x+k+2}`. -/
noncomputable def lpTK (k : ℕ) : XtLay := lpLim (lpTB k) (k + 1) (lpTH k)

theorem lpTB_zero : lpTB 0 = lpZB := rfl

theorem lpTB_succ (k : ℕ) : (lpTB (k + 1)).K = lpTK k := rfl

theorem lpTK_E (k : ℕ) (x : Ordinal.{0}) : (lpTK k).E x = gk (k + 1) x := rfl

/-- **`Λ⁺(lpTK k) < Λ⁺(lpTK (k+1))`.** -/
theorem lpTow_lt (k : ℕ) : xtB1 (lpTK k).sys < xtB1 (lpTK (k + 1)).sys :=
  lpLim_gt_K (B := lpTB (k + 1)) (lpTH (k + 1))

/-- **`O_{lpTK (k+1)} = O_{lpTK k}` below `Λ⁺(lpTK k)`.** -/
theorem lpTow_eq_succ (k : ℕ) {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h : μ < xtB1 (lpTK k).sys) :
    xtOrec (lpTK (k + 1)).sys μ = xtOrec (lpTK k).sys μ := by
  have h1 : μ < xtB1 (lpSys (lpTB (k + 1)) 1) := h.trans (lpB1_gt_K (B := lpTB (k + 1)) 0)
  rw [show (lpTK (k + 1)).sys = lpUSys (lpTB (k + 1)) (k + 2) (lpTH (k + 1)) from rfl,
    lpLim_eq (lpTH (k + 1)) 1 hμ h1]
  exact lp_eq_K (B := lpTB (k + 1)) hμ h

theorem lpTow_mono : StrictMono fun k => xtB1 (lpTK k).sys := strictMono_nat_of_lt_succ lpTow_lt

/-- **`O_{lpTK k} = O_{lpTK 0}` below `Λ⁺(lpTK 0)`.** -/
theorem lpTow_eq0 (k : ℕ) {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h : μ < xtB1 (lpTK 0).sys) :
    xtOrec (lpTK k).sys μ = xtOrec (lpTK 0).sys μ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [lpTow_eq_succ k hμ (h.trans_le (lpTow_mono.monotone (Nat.zero_le k))), ih]

/-- **The tower of bases as a family** (`LyLim` at the limit): bounds `Λ⁺(lpTK k)`. -/
noncomputable def lpTowFam : XtFam where
  bd := fun k => xtB1 (lpTK k).sys
  off := fun k => xtOrec (lpTK k).sys
  spec := fun k => xtSpec1 (XtLay.topPkg (lpTK k))
  mono := lpTow_lt
  nonfix := fun k _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtB1_lt_Om1 (XtLay.topPkg (lpTK k))))

variable {S : InaccSeq.{0}}

/-- **`ι(Γ_{Ω₁+2}) < Λ⁺(lpTK 0) < sup_k Λ⁺(lpTK k)`.** -/
theorem lpTow_gt : iota S lgGam' < xtB1 (lpTK 0).sys ∧ xtB1 (lpTK 0).sys < lpTowFam.famSup := by
  refine ⟨?_, lpTowFam.famBd_lt 0⟩
  rw [← (lpZ_famLoc (S := S)).1]
  exact lpFam_lt_lim (B := lpZB) lpZ_limH

/-- **`lpTK 0` has terms for every code below `Γ_{Ω₁+2}`.** -/
theorem lpK0Poly (S : InaccSeq.{0}) : LgPoly (lpTK 0).sys lgGam' := by
  intro Z d hd hdG
  rw [← lpZ_cPs S] at hdG
  obtain ⟨n, hn⟩ := cPs_lt lpZ_cv hdG
  obtain ⟨s, hs⟩ := lpPoly lpZ_hc lx_Om1_le_ZC lpZ_cv lpZ_KE lxZ_poly n Z d hd hn
  exact ⟨s, fun y hy hy1 hZy => ⟨(hs y hy hy1 hZy).1.1, (hs y hy hy1 hZy).2⟩⟩

/-- **The notation hypothesis at a fixed point below `Λ⁺(lpTK 0)` whose name has last exponent `≤ Γ_{Ω₁+2}`.** -/
theorem lpK0T_fix {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hfix : upsilon l = l) (hX : upsilon l < Pv S ηx)
    (he : cdExp (cdEta S l) ≤ lgGam') : xtOrec (lpTK 0).sys l = lgTh l (cdExp (cdEta S l)) :=
  lgUni2 le_rfl (lpK0Poly S) l ηx hl hfix hX he

/-- **Theorem BLK^O below `υ_{sup_k Λ⁺(lpTK k)}`** in `R₂^C`, with the exact reaches `lh(ρ_λ) = δ_λ + O_k(λ)`. -/
theorem lpTow_blk :
    (∀ c d, c < d → d < upsilon lpTowFam.famSup → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < lpTowFam.famSup ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → ∀ k, l < xtB1 (lpTK k).sys →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec (lpTK k).sys l)) ∧
    (∀ α < upsilon lpTowFam.famSup, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  lpTowFam.famBlk

/-- **ENUM-REACH at every non-fixed restart of the range below `sup_k Λ⁺(lpTK k)`.** -/
theorem lpTow_init {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < lpTowFam.famSup) (hfix : l < upsilon l) :
    CdUpper S l ∧ CdLower S l :=
  lpTowFam.famInit hr hl hfix

/-- **The cap of the values at every non-fixed restart of the range below `sup_k Λ⁺(lpTK k)`.** -/
theorem lpTow_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < lpTowFam.famSup) (hfix : l < upsilon l) :
    CdCapV S l :=
  lpTowFam.famCapV hr hl hfix

/-- **ENUM-REACH at every restart of the range below `ι(Γ_{Ω₁+2})`** (fixed points included). -/
theorem lpTowEnum_low {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S lgGam') : CdUpper S l ∧ CdLower S l :=
  lpZEnum hr hl

/-- **The notation hypothesis for the tower at the fixed points below `ι(Γ_{Ω₁+2})`.** -/
theorem lpTowT_low (k : ℕ) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S lgGam') (hfix : upsilon l = l) :
    cdTheta S l (cdCode S l) = xtOrec (lpTK k).sys l := by
  have hl0 : l < xtB1 (lpTK 0).sys := hl.trans (lpTow_gt (S := S)).1
  rw [lpTow_eq0 k hr.1 hl0]
  have hlF : l < (lpFam lpZB).famSup := by rw [(lpZ_famLoc (S := S)).1]; exact hl
  obtain ⟨n, hn⟩ := (lpFam lpZB).famLt hlF
  rw [show (lpTK 0).sys = lpUSys lpZB 1 lpZ_limH from rfl, lpLim_eq lpZ_limH n hr.1 hn]
  exact lpZT_fix n hr hn hfix

/-- **The successor road past the tower of bases**: UPPER and LOWER asked only at `λ ≥ sup_k Λ⁺(lpTK k)`, the
notation hypothesis only at the fixed points in `[ι(Γ_{Ω₁+2}), sup_k Λ⁺(lpTK k))`, the cap of the values only at the
outer restarts, (CL), EQ, TCrest, (EMB₂). -/
theorem lpTowRoad (hU : ∀ l, CdRange S l → lpTowFam.famSup ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → lpTowFam.famSup ≤ l → CdLower S l)
    (hT : ∀ k l, CdRange S l → iota S lgGam' ≤ l → l < xtB1 (lpTK k).sys → upsilon l = l →
      cdTheta S l (cdCode S l) = xtOrec (lpTK k).sys l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut lpTowFam.famSup l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  refine lpTowFam.famRoad3 hU hL (fun k l hr hlk hfix => ?_) hV hC hEQ hrest hB2
  rcases lt_or_ge l (iota S lgGam') with h | h
  · exact lpTowT_low k hr h hfix
  · exact hT k l hr h hlk hfix

end Googology.Trans.PoR.InaccPsi.R2.Lp

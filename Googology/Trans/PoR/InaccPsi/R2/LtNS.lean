import Googology.Trans.PoR.InaccPsi.R2.LtNI

/-!
# The systems `lnS K` (top `c_{K+1}(x)`) and their limit `Λ_C⁺ = sup_K Λ⁺(lnS (K+1))`

`lnS K`: the terms of `R2.LtN` of depth `≤ K + 1`, top `c_{K+1}(x)` (`c_0 = y_ω`, `c_{K+1} = ϑˣ(Ω₁·ω + c_K)`); IMG
`lnPkg`, RS `lnRs`, comparison from EXACT `ln_pi`, representation `ln_rep`; the top has the IMG package
`LnK.ltC_pkg` (`c_{K+1}` is the value of `lnCt (K+1)` in `lnS (K+1)`).  `lnS (K+1)` contains the top of `lnS K`
(`ln_topIn`), and `lnS 1` contains the top `c_1 = ϑ(Ω₁·ω + y_ω)` of `ltSw` (`ln_topIn_Sw`).  Then:

* `ltSw_lt_N` (**`Λ⁺(ltSw) < Λ(lnS 1)`**), `ln_atB1Sw` (**`O(Λ⁺(ltSw)) = c_1(ρ) + 1`**), `ltReachSw1` (**the exact
  reach at `Λ⁺(ltSw)`: `lh(ρ) = δ + ϑᵖ(Ω₁·ω + y_ω(ρ)) + 1`**);
* `ln_reachLam` (**`lh(ρ) = δ + c_{K+1}(ρ)` at `Λ(lnS K)`**), `ln_reachB1` (**`lh(ρ) = δ + c_{K+1}(ρ) + 1` at
  `Λ⁺(lnS K)`**);
* `lnFam` (the family `Λ⁺(lnS (k+1))`), `ln_sup_ri` (**`Λ_C⁺` is a restart index**), `ln_order`, `ln_eqSw`,
  `ln_blk` (**BLK^O below `υ_{Λ_C⁺}`**), `ln_nuC`, `ln_init` (**UPPER and LOWER at every non-fixed restart of the
  range below `Λ_C⁺`**), `ln_capV`, `ln_capAt`, `ln_of_cp`, `lnRoad3`, `lnRoad`, `lnRoad_cap`;
* `ltP x := sup_K c_K(x)`, `lnSw` (all terms of `LnW`, top `ltP`), `lnChain`, `ln_atSup` (**`O(Λ_C⁺) = ltP(ρ)`**),
  `lnSw_lam` (`Λ(lnSw) = Λ_C⁺`).

New axiom: only `ltLhT_w_lim` of `R2.CitedLt`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lt

open Ordinal Order Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Lz LnW

theorem ltC_lt_next_ups {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) (K : ℕ) :
    ltC (upsilon l) K < upsilon (l + ω + 1) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have h1 : l < l + ω := lt_add_of_pos_right l omega0_pos
  exact (ltC_lt_next (ups_inE hl) (ups_lt_Om1 l hl1) K (upsilon_normal.strictMono h1)
    (upsPt_upsilon (hl0.trans h1)).2).trans (upsilon_normal.strictMono (lt_add_one _))

/-- **The term system `lnS K`**: the terms of `LnW` of depth `≤ K + 1`, top `c_{K+1}(x)`. -/
noncomputable def lnS (K : ℕ) : XtSys where
  Tm := LnW
  val := LnW.val
  CB := fun t s => CBt t s ∧ dp t ≤ K + 1
  cs := LnW.cs
  cst := fun c => lz (LzW.vz (VzTm.cst c))
  top := fun x => ltC x (K + 1)
  cb_cst := fun t s h => cbt_cst t s h.1
  cb_iff := fun t s s' h h' => ⟨cbt_iff t s s' h.1 h', h.2⟩
  val_cst := fun _ _ => rfl
  cb_cstI := fun _ _ h => ⟨h, Nat.zero_le _⟩
  lt_top := fun l hl hl1 t hCB => ln_lt_top (ups_inE hl) (ups_lt_Om1 l hl1) t hCB.1 hCB.2
  one_le_top := fun l hl hl1 => one_le_iff_pos.2 (ltC_facts (ups_inE hl) (ups_lt_Om1 l hl1) (K + 1)).2.2.2.pos
  rep := fun l hl hl1 v hv => by
    obtain ⟨t, h1, h2, h3⟩ := ln_rep (ups_inE hl) (ups_lt_Om1 l hl1) (K + 1) v hv
    exact ⟨t, ⟨h1, h2⟩, h3⟩
  top_lt := fun _ hl hl1 => ltC_lt_next_ups hl hl1 (K + 1)
  pkg := fun _ _ _ t hCB h1 R => lnPkg t hCB.1 h1 R
  rs := fun _ _ _ t hCB => lnRs t hCB.1
  uni_le := fun _ _ hσ hρ hB t u ht hu =>
    xt_uni_of_exact hB (ln_pi hσ hρ hB t ht.1) (ln_pi hσ hρ hB u hu.1)
  small := fun t => (ln_small t).imp id fun h x hx hx1 hc => h x hx hx1 hc.1

theorem lnS_top (K : ℕ) (x : Ordinal.{0}) : (lnS K).top x = ltC x (K + 1) := rfl

namespace LnK

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **The IMG package of the top `c_{K+1}`**: `c_{K+1}(ρ)` is the value of `lnCt (K+1)` (constant `ω`). -/
theorem ltC_pkg (K : ℕ) : ImgPkg ρ δ (fun x => ltC x (K + 1)) := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  obtain ⟨W, Z, t', I⟩ := ln_img h (K + 2) (ltC ρ (K + 1)) (ltC_step hρE hρ1 (K + 1)).1
  have hωρ : (ω : Ordinal.{0}) < ρ := omega0_lt_inE hρE
  refine ⟨one_le_iff_pos.2 (ltC_facts hρE hρ1 (K + 1)).2.2.2.pos, ltC_lt_δ h (K + 1), W, insert ω Z,
    I.1.insZ hωρ, Finset.union_subset_union (subset_refl W) (Finset.subset_insert _ _) I.2.2.2.2.1,
    fun A f hW hZ C => ?_⟩
  have hZ' : ↑Z ⊆ A := fun x hx => hZ (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hx)))
  have hωA : (ω : Ordinal.{0}) ∈ A := hZ (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
  have ht'A : ∀ c ∈ cs t', c ∈ A := fun c hc => hZ' (Finset.mem_coe.2 (I.2.2.1 c hc))
  have hA0 : ∀ c ∈ cs (lnCt (K + 1)), c ∈ A := by
    intro c hc; rw [lnCt_cs] at hc; simp only [List.mem_singleton] at hc; rw [hc]; exact hωA
  have heq := ln_val_fρ h C (t := lnCt (K + 1)) (u := t') (lnCt_cbt hωρ _) I.2.1 hA0 ht'A
    (by rw [lnCt_val hρE hρ1]; exact I.2.2.2.1.symm)
  have hyE := upsPt_inE C.ups
  have hy1 : f ρ < Om1 := (C.low ρ C.rho).trans hρ1
  show ltC (f ρ) (K + 1) ≤ f (ltC ρ (K + 1))
  rw [← lnCt_val hyE hy1, heq]
  exact I.2.2.2.2.2 A f hW hZ' C

end LnK

/-- **The top `c_{K+1}` has an IMG package.** -/
theorem lnS_topPkg (K : ℕ) : XtTopPkg (lnS K) := fun _ _ _ R => LnK.ltC_pkg R K

theorem ltC_gap {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (K : ℕ) : ltC x K + 1 < ltC x (K + 1) := by
  have hE := (ltC_facts hx hx1 (K + 1)).2.2.2
  exact (inE_indec hE).add_lt (ltC_step hx hx1 K).1 (one_lt_omega0.trans (omega0_lt_inE hE))

/-- **`lnS (K+1)` contains the top `c_{K+1}` of `lnS K`.** -/
theorem ln_topIn (K : ℕ) : LyTopIn (lnS (K + 1)) (lnS K) :=
  ⟨lnCt (K + 1), fun _ hx hx1 => ⟨⟨lnCt_cbt (omega0_lt_inE (upsPt_inE hx)) _, (lnCt_dp _).le⟩,
    lnCt_val (upsPt_inE hx) hx1 _⟩, fun l hl hl1 => ltC_gap (ups_inE hl) (ups_lt_Om1 l hl1) (K + 1)⟩

/-- **`lnS 1` contains the top `c_1 = ϑ(Ω₁·ω + y_ω)` of `ltSw`.** -/
theorem ln_topIn_Sw : LyTopIn (lnS 1) ltSw := by
  refine ⟨lnCt 1, fun x hx hx1 => ⟨⟨lnCt_cbt (omega0_lt_inE (upsPt_inE hx)) _, (lnCt_dp _).le⟩, ?_⟩,
    fun l hl hl1 => ?_⟩
  · show val (lnCt 1) x = ltTw x
    rw [lnCt_val (upsPt_inE hx) hx1, ltC_one (upsPt_inE hx) hx1]
  · have hρE := ups_inE hl
    have hρ1 := ups_lt_Om1 l hl1
    rw [ltSw_top, lnS_top, ← ltC_one hρE hρ1]
    exact ltC_gap hρE hρ1 1

/-! ## The exact reach at `Λ⁺(ltSw)` -/

/-- **`Λ⁺(ltSw) < Λ(lnS 1)`.** -/
theorem ltSw_lt_N : xtB1 ltSw < xtLam (lnS 1) := lyLamGt ltSw_topPkg ln_topIn_Sw

theorem ln_eqSw0 {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h : μ < xtB1 ltSw) :
    xtOrec (lnS 1) μ = xtOrec ltSw μ :=
  lyEq ltSw_topPkg ln_topIn_Sw hμ h

/-- **`O(Λ⁺(ltSw)) = c_1(ρ) + 1`** in `lnS 1`. -/
theorem ln_atB1Sw : xtOrec (lnS 1) (xtB1 ltSw) = ltTw (upsilon (xtB1 ltSw)) + 1 :=
  lyAtB1 ltSw_topPkg ln_topIn_Sw

/-- **The exact reach at `Λ⁺(ltSw)`**: `lh(ρ) = δ + ϑᵖ(Ω₁·ω + y_ω(ρ)) + 1`. -/
theorem ltReachSw1 :
    IsReach R2C (upsilon (xtB1 ltSw)) (upsilon (xtB1 ltSw + ω + 1) + (ltTw (upsilon (xtB1 ltSw)) + 1)) :=
  lyReachB1 (lnS_topPkg 1) ltSw_topPkg ln_topIn_Sw

/-! ## The reaches of the layers `lnS K` -/

/-- **The reach at the frontier of `lnS K`**: `lh(ρ) = δ + c_{K+1}(ρ)`. -/
theorem ln_reachLam (K : ℕ) :
    IsReach R2C (upsilon (xtLam (lnS K)))
      (upsilon (xtLam (lnS K) + ω + 1) + ltC (upsilon (xtLam (lnS K))) (K + 1)) := by
  rw [← lnS_top, ← xtOrec_Lam]
  exact xtReach1 (lnS_topPkg K) xtLam_ri (lyLamLtB1 (lnS_topPkg K))

/-- **The reach at `Λ⁺(lnS K)`**: `lh(ρ) = δ + c_{K+1}(ρ) + 1`. -/
theorem ln_reachB1 (K : ℕ) :
    IsReach R2C (upsilon (xtB1 (lnS K)))
      (upsilon (xtB1 (lnS K) + ω + 1) + (ltC (upsilon (xtB1 (lnS K))) (K + 1) + 1)) :=
  lyReachB1 (lnS_topPkg (K + 1)) (lnS_topPkg K) (ln_topIn K)

/-! ## The family and its supremum `Λ_C⁺` -/

theorem ln_B1_lt (K : ℕ) : xtB1 (lnS K) < xtB1 (lnS (K + 1)) :=
  lyB1_lt (lnS_topPkg (K + 1)) (lnS_topPkg K) (ln_topIn K)

/-- **The family of the layers `lnS (k+1)`**: bounds `Λ⁺(lnS (k+1))`. -/
noncomputable def lnFam : XtFam where
  bd := fun k => xtB1 (lnS (k + 1))
  off := fun k => xtOrec (lnS (k + 1))
  spec := fun k => xtSpec1 (lnS_topPkg (k + 1))
  mono := fun k => ln_B1_lt (k + 1)
  nonfix := fun k _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtB1_lt_Om1 (lnS_topPkg (k + 1))))

/-- **`Λ_C⁺` is a restart index.** -/
theorem ln_sup_ri : IsRestartIdx lnFam.famSup := by
  refine ri_iff.2 ⟨(lt_of_le_of_lt zero_le (lnFam.famBd_lt 0)).ne', xt_ww_dvd_of_cof fun ν hν => ?_⟩
  obtain ⟨k, hk⟩ := lnFam.famLt hν
  exact ⟨xtB1 (lnS (k + 1)), xtB1_mult (lnS_topPkg (k + 1)), hk, lnFam.famBd_lt k⟩

/-- **The order of the frontiers**: `Λ⁺(ltSw) < Λ(lnS 1) < Λ⁺(lnS 1) < Λ_C⁺`. -/
theorem ln_order : xtB1 ltSw < xtLam (lnS 1) ∧ xtLam (lnS 1) < xtB1 (lnS 1) ∧ xtB1 (lnS 1) < lnFam.famSup :=
  ⟨ltSw_lt_N, lyLamLtB1 (lnS_topPkg 1), lnFam.famBd_lt 0⟩

/-- **The frontiers of this leaf in order**: `Λ_{B^ω}⁺ < Λ⁺(lzWw) < Λ_T⁺ < Λ⁺(ltSw) < Λ_C⁺`. -/
theorem ln_order_all : lzWFam.famSup < xtB1 lzWw ∧ xtB1 lzWw < ltFam.famSup ∧ ltFam.famSup < xtB1 ltSw ∧
    xtB1 ltSw < lnFam.famSup :=
  ⟨ltY_lt_B1, lt_order2.2, ltT_lt_B1, ltSw_lt_N.trans (ln_order.2.1.trans ln_order.2.2)⟩

theorem ln_B1_mono : ∀ j, xtB1 (lnS 1) ≤ xtB1 (lnS (j + 1)) := by
  intro j
  induction j with
  | zero => exact le_rfl
  | succ j ihj => exact ihj.trans (ln_B1_lt (j + 1)).le

/-- **The offsets of the family agree with `O_{ltSw}` below `Λ⁺(ltSw)`.** -/
theorem ln_eqSw : ∀ k : ℕ, ∀ {μ : Ordinal.{0}}, IsRestartIdx μ → μ < xtB1 ltSw →
    xtOrec (lnS (k + 1)) μ = xtOrec ltSw μ := by
  intro k
  induction k with
  | zero => exact fun hμ h => ln_eqSw0 hμ h
  | succ k ih =>
    intro μ hμ h
    have hk : μ < xtB1 (lnS (k + 1)) :=
      h.trans ((ltSw_lt_N.trans (lyLamLtB1 (lnS_topPkg 1))).trans_le (ln_B1_mono k))
    rw [lyEq (lnS_topPkg (k + 1)) (ln_topIn (k + 1)) hμ hk]
    exact ih hμ h

/-- **Theorem BLK^O below `υ_{Λ_C⁺}`** in `R₂^C`. -/
theorem ln_blk :
    (∀ c d, c < d → d < upsilon lnFam.famSup → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < lnFam.famSup ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → ∀ k, l < xtB1 (lnS (k + 1)) →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec (lnS (k + 1)) l)) ∧
    (∀ α < upsilon lnFam.famSup, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  lnFam.famBlk

/-- **Where the first non-standard pair lies**: `ρ_L <₂ ν_C = ρ_ξ` with `Λ_C⁺ ≤ L < ξ`. -/
theorem ln_nuC : ∃ L ξ, IsRestartIdx L ∧ IsRestartIdx ξ ∧ lnFam.famSup ≤ L ∧ L < ξ ∧
    upsilon lnFam.famSup ≤ upsilon L ∧ upsilon L < nuC ∧ nuC = upsilon ξ ∧ le2 (upsilon L) nuC :=
  lnFam.famNuC

variable {S : InaccSeq.{0}}

/-- **UPPER and LOWER at every restart of the range below `Λ_C⁺` that is not a fixed point of `υ`.** -/
theorem ln_init {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < lnFam.famSup) (hfix : l < upsilon l) :
    CdUpper S l ∧ CdLower S l :=
  lnFam.famInit hr hl hfix

/-- **The cap of the values at every non-fixed restart of the range below `Λ_C⁺`.** -/
theorem ln_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < lnFam.famSup) (hfix : l < upsilon l) :
    CdCapV S l :=
  lnFam.famCapV hr hl hfix

theorem ln_capAt {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hB : cdB0 ≤ l) (hlΛ : l < lnFam.famSup)
    (hfix : l < upsilon l) (hname : upsilon l < Pv S η1) : CdCapAt S l :=
  lnFam.famCapAt hl hB hlΛ hfix hname

/-- **The hypotheses of `lnRoad3` from those of `cpRoad3`.** -/
theorem ln_of_cp (hU : CpUPPERhigh S) (hL : CpLOWERhigh S) (hT : CpTHfix S) :
    (∀ l, CdRange S l → lnFam.famSup ≤ l → CdUpper S l) ∧
      (∀ l, CdRange S l → lnFam.famSup ≤ l → CdLower S l) ∧ lnFam.famTHfix S := by
  obtain ⟨hU', hL', hT'⟩ := ltSw_of_cp hU hL hT
  have hle : xtB1 ltSw ≤ lnFam.famSup := ln_order_all.2.2.2.le
  refine ⟨fun l hr h => hU' l hr (hle.trans h), fun l hr h => hL' l hr (hle.trans h),
    fun k l hr hlk hfix => ?_⟩
  rcases lt_or_ge l (xtB1 ltSw) with h | h
  · show cdTheta S l (cdCode S l) = xtOrec (lnS (k + 1)) l
    rw [ln_eqSw k hr.1 h]; exact hT' l hr h hfix
  · exact (lnFam.famIff k hr.1 hlk).2.2.1 ⟨hU' l hr h, hL' l hr h⟩

/-- **The road with UPPER and LOWER asked only at `λ ≥ Λ_C⁺`**, `Θ_F(m_F) = O_k(F)` at the fixed points below
`Λ⁺(lnS (k+1))`, the cap of the values outside `Λ_C⁺`, (CL), EQ, TCrest, (EMB₂). -/
theorem lnRoad3 (hU : ∀ l, CdRange S l → lnFam.famSup ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → lnFam.famSup ≤ l → CdLower S l) (hT : lnFam.famTHfix S)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut lnFam.famSup l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  lnFam.famRoad3 hU hL hT hV hC hEQ hrest hB2

/-- **The road with UPPER, LOWER and the cap of the values asked only outside `Λ_C⁺`.** -/
theorem lnRoad (hU : ∀ l, CdRange S l → XtOut lnFam.famSup l → CdUpper S l)
    (hL : ∀ l, CdRange S l → XtOut lnFam.famSup l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut lnFam.famSup l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  lnFam.famRoad hU hL hV hC hEQ hrest hB2

/-- **The road with the caps asked only outside `Λ_C⁺`**: CAP-0, CAP-1 outside, (CL), (TC), (EMB₂). -/
theorem lnRoad_cap
    (h0 : ∀ l, IsRestartIdx l → cdB0 ≤ l → upsilon l < cdMstar S → XtOut lnFam.famSup l → CdCapAt S l)
    (h1 : ∀ l, IsRestartIdx l → cdB0 ≤ l → cdMstar S ≤ upsilon l → upsilon l < Nc.ncL S ω →
      cdCode S l < Nc.ncPp S → XtOut lnFam.famSup l → CdCapAt S l) (hC : CdCL S) (hTC : CdTC S)
    (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  lnFam.famRoad_cap h0 h1 hC hTC hB2

/-! ## The system of all nested terms and the offset at `Λ_C⁺` -/

/-- `ltP(x) = sup_K c_K(x)`. -/
noncomputable def ltP (x : Ordinal.{0}) : Ordinal.{0} := ⨆ K : ℕ, ltC x K

theorem ltC_le_P (x : Ordinal.{0}) (K : ℕ) : ltC x K ≤ ltP x := Ordinal.le_iSup _ K

theorem ltP_lt_iff {x v : Ordinal.{0}} : v < ltP x ↔ ∃ K : ℕ, v < ltC x K := Ordinal.lt_iSup_iff

theorem ltC_lt_P {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (K : ℕ) : ltC x K < ltP x :=
  (ltC_step hx hx1 K).1.trans_le (ltC_le_P x (K + 1))

theorem ltP_le_next {x u : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hxu : x < u) (hu : LtInf1 u) :
    ltP x ≤ u :=
  Ordinal.iSup_le fun K => (ltC_lt_next hx hx1 K hxu hu).le

/-- **`ltP(x)` is a value of `φ(ω, ·)`.** -/
theorem ltP_omega {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : ltP x ∈ Set.range (veblen ω) :=
  lt_sup_range omega0_ne_zero (ltC x) (fun K => by
      rcases K with _ | K
      · exact ltYw_omega hx hx1
      · exact lt_w_omega hx hx1 (ltC_facts hx hx1 K).1 (ltC_facts hx hx1 K).2.1)
    (fun K => (ltC_step hx hx1 K).1)

/-- **The term system `lnSw` of all terms of `LnW`**, top `ltP(x) = sup_K c_K(x)` (no IMG package of the top
here). -/
noncomputable def lnSw : XtSys where
  Tm := LnW
  val := LnW.val
  CB := CBt
  cs := LnW.cs
  cst := fun c => lz (LzW.vz (VzTm.cst c))
  top := ltP
  cb_cst := cbt_cst
  cb_iff := cbt_iff
  val_cst := fun _ _ => rfl
  cb_cstI := fun _ _ h => h
  lt_top := fun l hl hl1 t hCB =>
    (ln_lt_top (ups_inE hl) (ups_lt_Om1 l hl1) t (K := dp t) hCB le_rfl).trans
      (ltC_lt_P (ups_inE hl) (ups_lt_Om1 l hl1) _)
  one_le_top := fun l hl hl1 => one_le_iff_pos.2 ((ltC_facts (ups_inE hl) (ups_lt_Om1 l hl1) 0).2.2.2.pos.trans
    (ltC_lt_P (ups_inE hl) (ups_lt_Om1 l hl1) 0))
  rep := fun l hl hl1 v hv => by
    obtain ⟨K, hK⟩ := ltP_lt_iff.1 hv
    obtain ⟨t, h1, -, h3⟩ := ln_rep (ups_inE hl) (ups_lt_Om1 l hl1) K v hK
    exact ⟨t, h1, h3⟩
  top_lt := fun l hl hl1 => by
    have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
    have h1 : l < l + ω := lt_add_of_pos_right l omega0_pos
    exact (ltP_le_next (ups_inE hl) (ups_lt_Om1 l hl1) (upsilon_normal.strictMono h1)
      (upsPt_upsilon (hl0.trans h1)).2).trans_lt (upsilon_normal.strictMono (lt_add_one _))
  pkg := fun _ _ _ t hCB h1 R => lnPkg t hCB h1 R
  rs := fun _ _ _ t hCB => lnRs t hCB
  uni_le := fun _ _ hσ hρ hB t u ht hu =>
    xt_uni_of_exact hB (ln_pi hσ hρ hB t ht) (ln_pi hσ hρ hB u hu)
  small := ln_small

/-- The chain of the layers `lnS (k+1)` inside `lnSw`. -/
noncomputable def lnChain : LyChain lnSw where
  Y := fun k => lnS (k + 1)
  pkg := fun k => lnS_topPkg (k + 1)
  inX := fun k => ⟨lnCt (k + 2), fun _ hx hx1 => ⟨lnCt_cbt (omega0_lt_inE (upsPt_inE hx)) _,
    lnCt_val (upsPt_inE hx) hx1 _⟩, fun l hl hl1 =>
    (ltC_gap (ups_inE hl) (ups_lt_Om1 l hl1) (k + 2)).trans_le (ltC_le_P _ _)⟩
  next := fun k => lyLamGt (lnS_topPkg (k + 1)) (ln_topIn (k + 1))
  topMono := fun k _ hx hx1 => ltC_mono hx hx1 (Nat.le_succ (k + 2))

theorem lnChain_sup : lnChain.fam.famSup = lnFam.famSup := rfl

/-- **`O(Λ_C⁺) = ltP(ρ)`**: the offset of `lnSw` at the supremum of the family is its top. -/
theorem ln_atSup : xtOrec lnSw lnFam.famSup = ltP (upsilon lnFam.famSup) :=
  lnChain.lyLimAt ltP (fun k _ hx hx1 => ltC_lt_P hx hx1 (k + 2))
    (fun x hx hx1 v hv => by
      obtain ⟨K, hK⟩ := ltP_lt_iff.1 hv
      exact ⟨K, hK.trans_le (ltC_mono hx hx1 (by omega))⟩)

/-- **`Λ(lnSw) = Λ_C⁺`.** -/
theorem lnSw_lam : xtLam lnSw = lnFam.famSup :=
  le_antisymm (xtLam_le ln_sup_ri ln_atSup) lnChain.sup_le

end Googology.Trans.PoR.InaccPsi.R2.Lt

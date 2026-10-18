import Googology.Trans.PoR.InaccPsi.R2.LtWI
import Googology.Trans.PoR.InaccPsi.R2.LtTop

/-!
# The term systems `ltS K` (top `T_K(x) = ϑˣ(Ω₁·ω + y_K(x))`) and their limit `Λ_T⁺ = sup_K Λ⁺(ltS K)`

`ltS K`: the terms of `R2.LtW` of level `≤ K`, top `T_K(x)`; IMG `ltwPkg`, RS `ltwRs`, comparison from EXACT
`ltw_pi`, representation `ltw_rep`; the top has the IMG package `LtK.ltT_pkg` (the top `T_K` is the value of the term
`tw (yk K)` of `ltS (K+1)`).  `ltS (K+1)` contains the top `T_K` of `ltS K` (`lt_topIn`), and `ltS 0` contains the
top `y_ω = ϑ(Ω₁·ω + ω)` of `lzWw` as `tw ω` (`lt_topIn_W`).  Then:

* `ltWw_lt_S` (**`Λ⁺(lzWw) < Λ(ltS 0)`**), `lt_atB1Ww` (**`O(Λ⁺(lzWw)) = y_ω(ρ) + 1`**), `ltReachWw1` (**the exact
  reach at `Λ⁺(lzWw)`: `lh(ρ) = δ + y_ω(ρ) + 1`**);
* `lt_reachLam` (**`lh(ρ) = δ + T_K(ρ)` at `Λ(ltS K)`**), `lt_reachB1` (**`lh(ρ) = δ + T_K(ρ) + 1` at `Λ⁺(ltS K)`**),
  `lt_reachT` (the reach at the frontier of every term);
* `ltFam` (the family `Λ⁺(ltS k)`, `R2.XtFam`), `lt_sup_ri` (**`Λ_T⁺` is a restart index**), `lt_order`, `lt_eqW`,
  `lt_blk` (**BLK^O below `υ_{Λ_T⁺}`**), `lt_nuC`, `lt_init` (**UPPER and LOWER at every non-fixed restart of the
  range below `Λ_T⁺`**), `lt_capV`, `lt_capAt`, `lt_of_cp`, `ltRoad3`, `ltRoad`, `ltRoad_cap`.

New axiom: only `ltLhT_w_lim` of `R2.CitedLt`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lt

open Ordinal Order Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Lz LtW

theorem ltT_lt_next_ups {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) (K : ℕ) :
    ltT (upsilon l) K < upsilon (l + ω + 1) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have h1 : l < l + ω := lt_add_of_pos_right l omega0_pos
  exact (ltT_lt_next (ups_inE hl) (ups_lt_Om1 l hl1) K (upsilon_normal.strictMono h1)
    (upsPt_upsilon (hl0.trans h1)).2).trans (upsilon_normal.strictMono (lt_add_one _))

/-- **The term system `ltS K`**: the terms of `LtW` of level `≤ K`, top `T_K(x) = ϑˣ(Ω₁·ω + y_K(x))`. -/
noncomputable def ltS (K : ℕ) : XtSys where
  Tm := LtW
  val := LtW.val
  CB := fun t s => CBt t s ∧ lw t ≤ K
  cs := LtW.cs
  cst := fun c => lz (LzW.vz (VzTm.cst c))
  top := fun x => ltT x K
  cb_cst := fun t s h => cbt_cst t s h.1
  cb_iff := fun t s s' h h' => ⟨cbt_iff t s s' h.1 h', h.2⟩
  val_cst := fun _ _ => rfl
  cb_cstI := fun _ _ h => ⟨h, Nat.zero_le K⟩
  lt_top := fun l hl hl1 t hCB => ltw_lt_top (ups_inE hl) (ups_lt_Om1 l hl1) t hCB.1 hCB.2
  one_le_top := fun l hl hl1 => one_le_iff_pos.2 (ltT_facts (ups_inE hl) (ups_lt_Om1 l hl1) K).2.2.2.1.pos
  rep := fun l hl hl1 v hv => by
    obtain ⟨t, h1, h2, h3⟩ := ltw_rep (ups_inE hl) (ups_lt_Om1 l hl1) v hv
    exact ⟨t, ⟨h1, h2⟩, h3⟩
  top_lt := fun _ hl hl1 => ltT_lt_next_ups hl hl1 K
  pkg := fun _ _ _ t hCB h1 R => ltwPkg t hCB.1 h1 R
  rs := fun _ _ _ t hCB => ltwRs t hCB.1
  uni_le := fun _ _ hσ hρ hB t u ht hu =>
    xt_uni_of_exact hB (ltw_pi hσ hρ hB t ht.1) (ltw_pi hσ hρ hB u hu.1)
  small := fun t => (ltw_small t).imp id fun h x hx hx1 hc => h x hx hx1 hc.1

theorem ltS_top (K : ℕ) (x : Ordinal.{0}) : (ltS K).top x = ltT x K := rfl

namespace LtK

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **The IMG package of the top `T_K`**: `T_K(ρ)` is the value of `tw (yk K)` in `ltS (K+1)`. -/
theorem ltT_pkg (K : ℕ) : ImgPkg ρ δ (fun x => ltT x K) := by
  obtain ⟨W, Z, t', I⟩ := lt_img h (K + 1) (ltT ρ K) (ltT_strict h.ρE h.ρ1 (Nat.lt_succ_self K))
  refine ⟨one_le_iff_pos.2 (ltT_facts h.ρE h.ρ1 K).2.2.2.1.pos, ltT_lt_δ h K, W, Z, I.1, I.2.2.2.2.1,
    fun A f hW hZ C => ?_⟩
  have ht'A : ∀ c ∈ cs t', c ∈ A := fun c hc => hZ (Finset.mem_coe.2 (I.2.2.1 c hc))
  have hA0 : ∀ c ∈ cs (tw (LzW.yk K)), c ∈ A := by intro c hc; simp [cs, LzW.cs] at hc
  have heq := ltw_val_fρ h C (t := tw (LzW.yk K)) (u := t') trivial I.2.1 hA0 ht'A
    (by rw [val_tw, LzW.val_yk]; exact I.2.2.2.1.symm)
  show ltT (f ρ) K ≤ f (ltT ρ K)
  have e : ltT (f ρ) K = val (tw (LzW.yk K)) (f ρ) := rfl
  rw [e, heq]
  exact I.2.2.2.2.2 A f hW hZ C

end LtK

/-- **The top `T_K` has an IMG package.** -/
theorem ltS_topPkg (K : ℕ) : XtTopPkg (ltS K) := fun _ _ _ R => LtK.ltT_pkg R K

theorem ltT_gap {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (K : ℕ) : ltT x K + 1 < ltT x (K + 1) := by
  have hE := (ltT_facts hx hx1 (K + 1)).2.2.2.1
  exact (inE_indec hE).add_lt (ltT_strict hx hx1 (Nat.lt_succ_self K)) (one_lt_omega0.trans (omega0_lt_inE hE))

/-- **`ltS (K+1)` contains the top `T_K` of `ltS K`.** -/
theorem lt_topIn (K : ℕ) : LyTopIn (ltS (K + 1)) (ltS K) :=
  ⟨tw (LzW.yk K), fun _ _ _ => ⟨⟨trivial, le_rfl⟩, rfl⟩, fun l hl hl1 => ltT_gap (ups_inE hl) (ups_lt_Om1 l hl1) K⟩

/-- **`ltS 0` contains the top `y_ω = ϑ(Ω₁·ω + ω)` of `lzWw`.** -/
theorem lt_topIn_W : LyTopIn (ltS 0) lzWw := by
  refine ⟨tw (LzW.vz (VzTm.cst ω)), fun x hx hx1 => ⟨⟨omega0_lt_inE (upsPt_inE hx), le_rfl⟩, ?_⟩,
    fun l hl hl1 => ?_⟩
  · show vt x (Om1 * ω + ω) = lzYw x
    exact (ltYw_eq (upsPt_inE hx) hx1).symm
  · have hρE := ups_inE hl
    have hρ1 := ups_lt_Om1 l hl1
    have hE := (ltT_facts hρE hρ1 0).2.2.2.1
    rw [ltWw_top, ltS_top]
    exact (inE_indec hE).add_lt (ltYw_lt_T hρE hρ1 0) (one_lt_omega0.trans (omega0_lt_inE hE))

/-! ## The exact reach at `Λ⁺(lzWw)` -/

/-- **`Λ⁺(lzWw) < Λ(ltS 0)`.** -/
theorem ltWw_lt_S : xtB1 lzWw < xtLam (ltS 0) := lyLamGt ltWw_topPkg lt_topIn_W

/-- **`O = O_{lzWw}` below `Λ⁺(lzWw)`** in `ltS 0`. -/
theorem lt_eqWw {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h : μ < xtB1 lzWw) :
    xtOrec (ltS 0) μ = xtOrec lzWw μ :=
  lyEq ltWw_topPkg lt_topIn_W hμ h

/-- **`O(Λ⁺(lzWw)) = y_ω(ρ) + 1`** in `ltS 0`. -/
theorem lt_atB1Ww : xtOrec (ltS 0) (xtB1 lzWw) = lzYw (upsilon (xtB1 lzWw)) + 1 :=
  lyAtB1 ltWw_topPkg lt_topIn_W

/-- **The exact reach at `Λ⁺(lzWw)`**: `lh(ρ) = δ + y_ω(ρ) + 1`. -/
theorem ltReachWw1 :
    IsReach R2C (upsilon (xtB1 lzWw)) (upsilon (xtB1 lzWw + ω + 1) + (lzYw (upsilon (xtB1 lzWw)) + 1)) :=
  lyReachB1 (ltS_topPkg 0) ltWw_topPkg lt_topIn_W

/-! ## The reaches of the layers `ltS K` -/

/-- **The reach at the frontier of `ltS K`**: `lh(ρ) = δ + T_K(ρ)`. -/
theorem lt_reachLam (K : ℕ) :
    IsReach R2C (upsilon (xtLam (ltS K))) (upsilon (xtLam (ltS K) + ω + 1) + ltT (upsilon (xtLam (ltS K))) K) := by
  rw [← ltS_top, ← xtOrec_Lam]
  exact xtReach1 (ltS_topPkg K) xtLam_ri (lyLamLtB1 (ltS_topPkg K))

/-- **The reach at `Λ⁺(ltS K)`**: `lh(ρ) = δ + T_K(ρ) + 1`. -/
theorem lt_reachB1 (K : ℕ) :
    IsReach R2C (upsilon (xtB1 (ltS K)))
      (upsilon (xtB1 (ltS K) + ω + 1) + (ltT (upsilon (xtB1 (ltS K))) K + 1)) :=
  lyReachB1 (ltS_topPkg (K + 1)) (ltS_topPkg K) (lt_topIn K)

/-- **The reach at the frontier of every term `t` of `ltS K`**: `lh(ρ) = δ + t(ρ)`. -/
theorem lt_reachT {K : ℕ} {t : LtW} (hCB : CBt t (upsilon (xtLam (ltS K)))) (hl : lw t ≤ K)
    (h1 : 1 ≤ val t (upsilon (xtLam (ltS K)))) :
    IsReach R2C (upsilon (xtLamT (ltS K) t))
      (upsilon (xtLamT (ltS K) t + ω + 1) + val t (upsilon (xtLamT (ltS K) t))) :=
  xtReach_LamT (X := ltS K) (t := t) ⟨hCB, hl⟩ h1

/-! ## The family and its supremum `Λ_T⁺` -/

theorem lt_B1_lt (K : ℕ) : xtB1 (ltS K) < xtB1 (ltS (K + 1)) :=
  lyB1_lt (ltS_topPkg (K + 1)) (ltS_topPkg K) (lt_topIn K)

/-- **The family of the layers `ltS k`**: bounds `Λ⁺(ltS k)`. -/
noncomputable def ltFam : XtFam where
  bd := fun k => xtB1 (ltS k)
  off := fun k => xtOrec (ltS k)
  spec := fun k => xtSpec1 (ltS_topPkg k)
  mono := fun k => lt_B1_lt k
  nonfix := fun k _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtB1_lt_Om1 (ltS_topPkg k)))

/-- **`Λ_T⁺` is a restart index.** -/
theorem lt_sup_ri : IsRestartIdx ltFam.famSup := by
  refine ri_iff.2 ⟨(lt_of_le_of_lt zero_le (ltFam.famBd_lt 0)).ne', xt_ww_dvd_of_cof fun ν hν => ?_⟩
  obtain ⟨k, hk⟩ := ltFam.famLt hν
  exact ⟨xtB1 (ltS k), xtB1_mult (ltS_topPkg k), hk, ltFam.famBd_lt k⟩

/-- **The order of the frontiers**: `Λ⁺(lzWw) < Λ(ltS 0) < Λ⁺(ltS 0) < Λ_T⁺`. -/
theorem lt_order : xtB1 lzWw < xtLam (ltS 0) ∧ xtLam (ltS 0) < xtB1 (ltS 0) ∧ xtB1 (ltS 0) < ltFam.famSup :=
  ⟨ltWw_lt_S, lyLamLtB1 (ltS_topPkg 0), ltFam.famBd_lt 0⟩

/-- **`Λ_{B^ω}⁺ < Λ⁺(lzWw) < Λ_T⁺`.** -/
theorem lt_order2 : lzWFam.famSup < xtB1 lzWw ∧ xtB1 lzWw < ltFam.famSup :=
  ⟨ltY_lt_B1, ltWw_lt_S.trans (lt_order.2.1.trans lt_order.2.2)⟩

theorem lt_B1_mono : ∀ j, xtB1 (ltS 0) ≤ xtB1 (ltS j) := by
  intro j
  induction j with
  | zero => exact le_rfl
  | succ j ihj => exact ihj.trans (lt_B1_lt j).le

/-- **The offsets of the family agree with `O_{lzWw}` below `Λ⁺(lzWw)`.** -/
theorem lt_eqW : ∀ k : ℕ, ∀ {μ : Ordinal.{0}}, IsRestartIdx μ → μ < xtB1 lzWw →
    xtOrec (ltS k) μ = xtOrec lzWw μ := by
  intro k
  induction k with
  | zero => exact fun hμ h => lt_eqWw hμ h
  | succ k ih =>
    intro μ hμ h
    have hk : μ < xtB1 (ltS k) :=
      h.trans ((ltWw_lt_S.trans (lyLamLtB1 (ltS_topPkg 0))).trans_le (lt_B1_mono k))
    rw [lyEq (ltS_topPkg k) (lt_topIn k) hμ hk]
    exact ih hμ h

/-- **Theorem BLK^O below `υ_{Λ_T⁺}`** in `R₂^C`. -/
theorem lt_blk :
    (∀ c d, c < d → d < upsilon ltFam.famSup → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < ltFam.famSup ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → ∀ k, l < xtB1 (ltS k) →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec (ltS k) l)) ∧
    (∀ α < upsilon ltFam.famSup, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  ltFam.famBlk

/-- **Where the first non-standard pair lies**: `ρ_L <₂ ν_C = ρ_ξ` with `Λ_T⁺ ≤ L < ξ`. -/
theorem lt_nuC : ∃ L ξ, IsRestartIdx L ∧ IsRestartIdx ξ ∧ ltFam.famSup ≤ L ∧ L < ξ ∧
    upsilon ltFam.famSup ≤ upsilon L ∧ upsilon L < nuC ∧ nuC = upsilon ξ ∧ le2 (upsilon L) nuC :=
  ltFam.famNuC

variable {S : InaccSeq.{0}}

/-- **UPPER and LOWER at every restart of the range below `Λ_T⁺` that is not a fixed point of `υ`.** -/
theorem lt_init {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < ltFam.famSup) (hfix : l < upsilon l) :
    CdUpper S l ∧ CdLower S l :=
  ltFam.famInit hr hl hfix

/-- **The cap of the values at every non-fixed restart of the range below `Λ_T⁺`.** -/
theorem lt_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < ltFam.famSup) (hfix : l < upsilon l) :
    CdCapV S l :=
  ltFam.famCapV hr hl hfix

theorem lt_capAt {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hB : cdB0 ≤ l) (hlΛ : l < ltFam.famSup)
    (hfix : l < upsilon l) (hname : upsilon l < Pv S η1) : CdCapAt S l :=
  ltFam.famCapAt hl hB hlΛ hfix hname

/-- **The hypotheses of `ltRoad3` from those of `cpRoad3`.** -/
theorem lt_of_cp (hU : CpUPPERhigh S) (hL : CpLOWERhigh S) (hT : CpTHfix S) :
    (∀ l, CdRange S l → ltFam.famSup ≤ l → CdUpper S l) ∧
      (∀ l, CdRange S l → ltFam.famSup ≤ l → CdLower S l) ∧ ltFam.famTHfix S := by
  obtain ⟨hU', hL', hT'⟩ := ltWw_of_cp hU hL hT
  have hle : xtB1 lzWw ≤ ltFam.famSup := lt_order2.2.le
  refine ⟨fun l hr h => hU' l hr (hle.trans h), fun l hr h => hL' l hr (hle.trans h),
    fun k l hr hlk hfix => ?_⟩
  rcases lt_or_ge l (xtB1 lzWw) with h | h
  · show cdTheta S l (cdCode S l) = xtOrec (ltS k) l
    rw [lt_eqW k hr.1 h]; exact hT' l hr h hfix
  · exact (ltFam.famIff k hr.1 hlk).2.2.1 ⟨hU' l hr h, hL' l hr h⟩

/-- **The road with UPPER and LOWER asked only at `λ ≥ Λ_T⁺`**, `Θ_F(m_F) = O_k(F)` at the fixed points below
`Λ⁺(ltS k)`, the cap of the values outside `Λ_T⁺`, (CL), EQ, TCrest, (EMB₂). -/
theorem ltRoad3 (hU : ∀ l, CdRange S l → ltFam.famSup ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → ltFam.famSup ≤ l → CdLower S l) (hT : ltFam.famTHfix S)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut ltFam.famSup l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  ltFam.famRoad3 hU hL hT hV hC hEQ hrest hB2

/-- **The road with UPPER, LOWER and the cap of the values asked only outside `Λ_T⁺`.** -/
theorem ltRoad (hU : ∀ l, CdRange S l → XtOut ltFam.famSup l → CdUpper S l)
    (hL : ∀ l, CdRange S l → XtOut ltFam.famSup l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut ltFam.famSup l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  ltFam.famRoad hU hL hV hC hEQ hrest hB2

/-- **The road with the caps asked only outside `Λ_T⁺`**: CAP-0, CAP-1 outside, (CL), (TC), (EMB₂). -/
theorem ltRoad_cap
    (h0 : ∀ l, IsRestartIdx l → cdB0 ≤ l → upsilon l < cdMstar S → XtOut ltFam.famSup l → CdCapAt S l)
    (h1 : ∀ l, IsRestartIdx l → cdB0 ≤ l → cdMstar S ≤ upsilon l → upsilon l < Nc.ncL S ω →
      cdCode S l < Nc.ncPp S → XtOut ltFam.famSup l → CdCapAt S l) (hC : CdCL S) (hTC : CdTC S)
    (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  ltFam.famRoad_cap h0 h1 hC hTC hB2

end Googology.Trans.PoR.InaccPsi.R2.Lt

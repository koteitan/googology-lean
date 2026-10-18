import Googology.Trans.PoR.InaccPsi.R2.LzVB

/-!
# The term system `lzVs` (top `B₁(x) = sup_N ϑˣ(Ω₁·N + B(x) + 1) = B(B(x))`): the exact reaches at `Λ⁺(lzZ)` and
`Λ(lzVs)`, BLK^O, the reaches, ENUM-REACH and the road below `Λ⁺(lzVs)`

`lzVs`: the terms of `R2.LzV` (`φ(n, ·)`-terms in `x`, the atom `B(x)`, `ϑˣ(Ω₁·n + t)` with arguments above `B(x)`,
sums, powers), top `B₁(x)`.  Its fields: Lemma IMG (`lzvPkg`), Lemma RS (`lzvRs`), the comparison (EXACT `lzv_pi`),
the representation (`lzv_rep`); the top has the IMG package `lzVs_topPkg` (`R2.LzVB`: `B₁ = B∘B`, `vz_lh_B` at the
base `B(x)`).  `lzVs` contains the top `e_x(x) = ϑˣ(Ω₁ + B(x) + x)` of `lzZ` (`R2.LzSys`) as the term
`ϑˣ(Ω₁·1 + (B(x) + x))` (`lzV_topIn_Z`).  Then:

* `lzZ_lt_V` (**`Λ⁺(lzZ) < Λ(lzVs)`**), `lzV_eqZ` (`O_V = O_Z` below `Λ⁺(lzZ)`), `lzV_atB1Z`
  (**`O_V(Λ⁺(lzZ)) = e_ρ(ρ) + 1`**), `lzReachZ1` (**the exact reach at `Λ⁺(lzZ)`: `lh(ρ) = δ + e_ρ(ρ) + 1`**);
* `lzV_reach` (**`lh(ρ_λ) = δ_λ + O_V(λ)` at every restart `λ < Λ⁺(lzVs)`**), `lzV_reachLam` (**`lh(ρ) = δ + B₁(ρ)`
  at `Λ(lzVs)`**), `lzV_reachT` (**`lh(ρ) = δ + t(ρ)` at the frontier of every term `t`** of `LzV`, e.g.
  `t = ϑˣ(Ω₁·n + s)`), `lzV_blk` (**BLK^O below `υ_{Λ⁺(lzVs)}`**), `lzV_nuC` (`υ_{Λ⁺(lzVs)} ≤ ρ_L < ν_C`);
* `lzV_init` (**UPPER and LOWER at every non-fixed restart of the range below `Λ⁺(lzVs)`**), `lzV_capV`, `lzV_capAt`,
  `lzV_iff`, `lzV_iso`, `lzV_fix_code`, `lzV_of_cp`, `lzVRoad3`, `lzVRoad`, `lzVRoad_cap` (the roads of `R2.XtEnum`
  with the rest asked only outside `Λ⁺(lzVs)`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lz

open Ordinal Order Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Nm LzV

theorem lzB1_lt_next {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) :
    VzB1 (upsilon l) < upsilon (l + ω + 1) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have h1 : l < l + ω := lt_add_of_pos_right l omega0_pos
  exact (lzB1_le_next (ups_inE hl) (ups_lt_Om1 l hl1) (upsilon_normal.strictMono h1)
    (upsPt_upsilon (hl0.trans h1)).2).trans_lt (upsilon_normal.strictMono (lt_add_one _))

/-- **The term system `lzVs`**: the terms of `LzV`, top `B₁(x) = sup_N ϑˣ(Ω₁·N + B(x) + 1)`. -/
noncomputable def lzVs : XtSys where
  Tm := LzV
  val := LzV.val
  CB := CBt
  cs := LzV.cs
  cst := fun c => vz (VzTm.cst c)
  top := VzB1
  cb_cst := cbt_cst
  cb_iff := cbt_iff
  val_cst := fun _ _ => rfl
  cb_cstI := fun _ _ h => h
  lt_top := fun l hl hl1 t hCB => lzv_lt_top (ups_inE hl) (ups_lt_Om1 l hl1) t hCB
  one_le_top := fun l hl hl1 => one_le_iff_pos.2
    ((xt_B_E (ups_inE hl) (ups_lt_Om1 l hl1)).pos.trans (lz_B_lt_B1 (ups_inE hl) (ups_lt_Om1 l hl1)))
  rep := fun l hl hl1 v hv => lzv_rep (ups_inE hl) (ups_lt_Om1 l hl1) v hv
  top_lt := fun _ hl hl1 => lzB1_lt_next hl hl1
  pkg := fun _ _ _ t hCB h1 R => lzvPkg t hCB h1 R
  rs := fun _ _ _ t hCB => lzvRs t hCB
  uni_le := fun _ _ hσ hρ hB t u ht hu =>
    xt_uni_of_exact hB (lzv_pi hσ hρ hB t ht) (lzv_pi hσ hρ hB u hu)
  small := lzv_small

theorem lzVs_top (x : Ordinal.{0}) : lzVs.top x = VzB1 x := rfl

/-- **The top `B₁ = B∘B` has an IMG package** (`R2.LzVB`). -/
theorem lzVs_topPkg : XtTopPkg lzVs := fun _ _ _ R => LzK.lzWitB1 R

/-- The term `ϑˣ(Ω₁·1 + (B(x) + x)) = e_x(x)` of `lzVs`. -/
def lzVtopZ : lzVs.Tm := th 1 (sm bB (vz VzTm.bs))

theorem lzVtopZ_val (x : Ordinal.{0}) : lzVs.val lzVtopZ x = lzE x x := by
  show vt x (Om1 * ((1 : ℕ) : Ordinal.{0}) + (VzB x + x)) = vt x (Om1 + (VzB x + x))
  rw [Nat.cast_one, mul_one]

/-- **`lzVs` contains the top `e_x(x)` of `lzZ`.** -/
theorem lzV_topIn_Z : LyTopIn lzVs lzZ := by
  refine ⟨lzVtopZ, fun x _ _ => ⟨⟨le_rfl, trivial, trivial⟩, lzVtopZ_val x⟩, fun l hl hl1 => ?_⟩
  have hρE := ups_inE hl
  have hρ1 := ups_lt_Om1 l hl1
  have hcb : CBt (sm lzVtopZ (vz (VzTm.cst 1))) (upsilon l) :=
    ⟨⟨le_rfl, trivial, trivial⟩, one_lt_of_upsPt (ups_ri hl)⟩
  have := lzv_lt_top hρE hρ1 _ hcb
  rw [val_sm, val_vz, VzTm.val_cst] at this
  rw [lzZ_top, lzVs_top, ← lzVtopZ_val]
  exact this

/-! ## The exact reach at `Λ⁺(lzZ)` -/

/-- **`Λ⁺(lzZ) < Λ(lzVs)`.** -/
theorem lzZ_lt_V : xtB1 lzZ < xtLam lzVs := lyLamGt lzZ_topPkg lzV_topIn_Z

/-- **`O_V = O_Z` below `Λ⁺(lzZ)`.** -/
theorem lzV_eqZ {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h : μ < xtB1 lzZ) : xtOrec lzVs μ = xtOrec lzZ μ :=
  lyEq lzZ_topPkg lzV_topIn_Z hμ h

/-- **`O_V(Λ⁺(lzZ)) = e_ρ(ρ) + 1`** for `ρ = ρ_{Λ⁺(lzZ)}`. -/
theorem lzV_atB1Z :
    xtOrec lzVs (xtB1 lzZ) = lzE (upsilon (xtB1 lzZ)) (upsilon (xtB1 lzZ)) + 1 :=
  lyAtB1 lzZ_topPkg lzV_topIn_Z

/-- **The exact reach at `Λ⁺(lzZ)`**: `lh(ρ) = δ + e_ρ(ρ) + 1`, `e_ρ(ρ) = ϑᵖ(Ω₁ + B(ρ) + ρ)`. -/
theorem lzReachZ1 :
    IsReach R2C (upsilon (xtB1 lzZ))
      (upsilon (xtB1 lzZ + ω + 1) + (lzE (upsilon (xtB1 lzZ)) (upsilon (xtB1 lzZ)) + 1)) := by
  rw [← lzV_atB1Z]
  exact xtReach (lyB1_ri lzZ_topPkg) lzZ_lt_V

/-! ## The reaches below `Λ⁺(lzVs)` -/

theorem lzV_spec : OffSpecGen (xtOrec lzVs) (xtB1 lzVs) := xtSpec1 lzVs_topPkg

theorem lzV_nonfix : XtNonfix (xtOrec lzVs) (xtB1 lzVs) :=
  fun _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtB1_lt_Om1 lzVs_topPkg))

/-- **The exact reach of every restart below `Λ⁺(lzVs)`**: `lh(ρ_λ) = δ_λ + O_V(λ)`. -/
theorem lzV_reach {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlV : l < xtB1 lzVs) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec lzVs l) :=
  xtReach1 lzVs_topPkg hl hlV

theorem lzV_lam_lt : xtLam lzVs < xtB1 lzVs := lyLamLtB1 lzVs_topPkg

/-- **The reach at the frontier of `lzVs`**: `lh(ρ) = δ + B₁(ρ)`, `B₁(ρ) = B(B(ρ))`. -/
theorem lzV_reachLam :
    IsReach R2C (upsilon (xtLam lzVs)) (upsilon (xtLam lzVs + ω + 1) + VzB1 (upsilon (xtLam lzVs))) := by
  rw [← lzVs_top, ← xtOrec_Lam]
  exact xtReach1 lzVs_topPkg xtLam_ri lzV_lam_lt

/-- **`O_V(Λ(lzVs)) = B₁(ρ)`** at the frontier. -/
theorem lzV_atLam : xtOrec lzVs (xtLam lzVs) = VzB1 (upsilon (xtLam lzVs)) := xtOrec_Lam

/-- **The reach at the frontier of every term `t` of `LzV`** (constants below `ρ_{Λ(lzVs)}`, value `≥ 1`):
`lh(ρ) = δ + t(ρ)`. -/
theorem lzV_reachT {t : LzV} (hCB : CBt t (upsilon (xtLam lzVs))) (h1 : 1 ≤ val t (upsilon (xtLam lzVs))) :
    IsReach R2C (upsilon (xtLamT lzVs t))
      (upsilon (xtLamT lzVs t + ω + 1) + val t (upsilon (xtLamT lzVs t))) :=
  xtReach_LamT (X := lzVs) hCB h1

/-- **Theorem BLK^O below `υ_{Λ⁺(lzVs)}`** in `R₂^C`. -/
theorem lzV_blk :
    (∀ c d, c < d → d < upsilon (xtB1 lzVs) → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 lzVs ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 lzVs →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec lzVs l)) ∧
    (∀ α < upsilon (xtB1 lzVs), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  xtBlk1 lzVs_topPkg

/-- **Where the first non-standard pair lies**: `ρ_L <₂ ν_C = ρ_ξ` with `Λ⁺(lzVs) ≤ L < ξ`. -/
theorem lzV_nuC : ∃ L ξ, IsRestartIdx L ∧ IsRestartIdx ξ ∧ xtB1 lzVs ≤ L ∧ L < ξ ∧
    upsilon (xtB1 lzVs) ≤ upsilon L ∧ upsilon L < nuC ∧ nuC = upsilon ξ ∧ le2 (upsilon L) nuC := by
  obtain ⟨L, ξ, hL, hξ, hLξ, he, h2, -, -, -⟩ := level2_restart
  have hLν : upsilon L < nuC := by rw [he]; exact upsilon_normal.strictMono hLξ
  have hle : xtB1 lzVs ≤ L := left_ge_of_spec lzV_spec hL hLν h2
  exact ⟨L, ξ, hL, hξ, hle, hLξ, upsilon_normal.strictMono.monotone hle, hLν, he, h2⟩

/-- **`Λ⁺(lyEB) < Λ⁺(lzZ) < Λ(lzVs) < Λ⁺(lzVs)`.** -/
theorem lzV_order : xtB1 lyEB < xtB1 lzZ ∧ xtB1 lzZ < xtLam lzVs ∧ xtLam lzVs < xtB1 lzVs :=
  ⟨lzE_lt_B1, lzZ_lt_V, lzV_lam_lt⟩

/-! ## ENUM-REACH and the road -/

variable {S : InaccSeq.{0}}

/-- **UPPER and LOWER at every restart of the range below `Λ⁺(lzVs)` that is not a fixed point of `υ`.** -/
theorem lzV_init {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 lzVs) (hfix : l < upsilon l) :
    CdUpper S l ∧ CdLower S l :=
  xtInit lzV_spec lzV_nonfix hr hl hfix

/-- **The cap of the values at every restart of the range below `Λ⁺(lzVs)` that is not a fixed point.** -/
theorem lzV_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 lzVs) (hfix : l < upsilon l) :
    CdCapV S l := by
  have hww := cp_ww_lt_B0.trans_le hr.2.1
  exact xtCapV_nonfix lzV_spec hr.1 hww hfix hl (cp_name_L hr.2.2.1) (lzV_nonfix l hr.1 hww hfix hl)

theorem lzV_capAt {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hB : cdB0 ≤ l) (hlΛ : l < xtB1 lzVs)
    (hfix : l < upsilon l) (hname : upsilon l < Pv S η1) : CdCapAt S l := by
  have hww := cp_ww_lt_B0.trans_le hB
  exact xtCapAt_nonfix lzV_spec hl hww hfix hlΛ hname (lzV_nonfix l hl hww hfix hlΛ)

/-- **Below `Λ⁺(lzVs)`, ENUM-REACH is the equation `Θ_λ(m_λ) = O_V(λ)`.** -/
theorem lzV_iff {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < xtB1 lzVs) :
    (CdUpper S l ∧ CdLower S l ↔ cdTheta S l (cdCode S l) = xtOrec lzVs l) :=
  xtExact_iff lzV_spec hl hlB

/-- **The offset at an isolated fixed point below `Λ⁺(lzVs)`**: `O_V(F) = F`. -/
theorem lzV_iso {F : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hFB : F < xtB1 lzVs)
    (hiso : CpIso F) : xtOrec lzVs F = F :=
  xtIso hF hfix (hFB.trans (xtB1_lt_Om1 lzVs_topPkg)) hiso

/-- **ENUM-REACH at an isolated fixed point of the range below `Λ⁺(lzVs)` reduces to the code.** -/
theorem lzV_fix_code {F : Ordinal.{0}} (hr : CdRange S F) (hfix : upsilon F = F) (hFB : F < xtB1 lzVs)
    (hiso : CpIso F) : (F ≤ cdCode S F → CdUpper S F) ∧ (cdCode S F ≤ Om1 → CdLower S F) :=
  xtFix_code lzV_spec hr.1 hfix hFB (lzV_iso hr.1 hfix hFB hiso) (cp_name_L hr.2.2.1)

/-- **The hypotheses of `lzVRoad3` from those of `cpRoad3`.** -/
theorem lzV_of_cp (hU : CpUPPERhigh S) (hL : CpLOWERhigh S) (hT : CpTHfix S) :
    (∀ l, CdRange S l → xtB1 lzVs ≤ l → CdUpper S l) ∧ (∀ l, CdRange S l → xtB1 lzVs ≤ l → CdLower S l) ∧
      (∀ l, CdRange S l → l < xtB1 lzVs → upsilon l = l → cdTheta S l (cdCode S l) = xtOrec lzVs l) := by
  obtain ⟨hU', hL', hT'⟩ := lzZ_of_cp hU hL hT
  have hcp : Cp.cpB1 ≤ xtB1 lzVs :=
    (((lyB_cp_le.trans lyE_order.2.le).trans lzE_lt_B1.le).trans lzZ_lt_V.le).trans lzV_lam_lt.le
  refine ⟨fun l hr h => hU l hr (hcp.trans h), fun l hr h => hL l hr (hcp.trans h), fun l hr hlB hfix => ?_⟩
  rcases lt_or_ge l (xtB1 lzZ) with h | h
  · rw [lzV_eqZ hr.1 h]; exact hT' l hr h hfix
  · exact (lzV_iff hr.1 hlB).1 ⟨hU' l hr h, hL' l hr h⟩

/-- **The road with UPPER and LOWER asked only at `λ ≥ Λ⁺(lzVs)`**, `Θ_F(m_F) = O_V(F)` at the fixed points of the
range below `Λ⁺(lzVs)`, the cap of the values outside `Λ⁺(lzVs)`, (CL), EQ, TCrest, (EMB₂). -/
theorem lzVRoad3 (hU : ∀ l, CdRange S l → xtB1 lzVs ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 lzVs ≤ l → CdLower S l)
    (hT : ∀ l, CdRange S l → l < xtB1 lzVs → upsilon l = l → cdTheta S l (cdCode S l) = xtOrec lzVs l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 lzVs) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad3 lzV_spec lzV_nonfix hU hL hT hV hC hEQ hrest hB2

/-- **The road with UPPER, LOWER and the cap of the values asked only outside `Λ⁺(lzVs)`.** -/
theorem lzVRoad (hU : ∀ l, CdRange S l → XtOut (xtB1 lzVs) l → CdUpper S l)
    (hL : ∀ l, CdRange S l → XtOut (xtB1 lzVs) l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 lzVs) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad lzV_spec lzV_nonfix hU hL hV hC hEQ hrest hB2

/-- **The road with the caps asked only outside `Λ⁺(lzVs)`**: CAP-0, CAP-1 outside, (CL), (TC), (EMB₂). -/
theorem lzVRoad_cap
    (h0 : ∀ l, IsRestartIdx l → cdB0 ≤ l → upsilon l < cdMstar S → XtOut (xtB1 lzVs) l → CdCapAt S l)
    (h1 : ∀ l, IsRestartIdx l → cdB0 ≤ l → cdMstar S ≤ upsilon l → upsilon l < Nc.ncL S ω →
      cdCode S l < Nc.ncPp S → XtOut (xtB1 lzVs) l → CdCapAt S l) (hC : CdCL S) (hTC : CdTC S)
    (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad_cap lzV_spec lzV_nonfix h0 h1 hC hTC hB2

end Googology.Trans.PoR.InaccPsi.R2.Lz

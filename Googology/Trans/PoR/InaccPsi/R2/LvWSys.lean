import Googology.Trans.PoR.InaccPsi.R2.LvWJ

/-!
# The term system of the levels `x·(k+1) + b`: BLK^O, the exact reaches and ENUM-REACH up to `Λ⁺(lvwSys)`

`lvwSys` is the term system of `LvWT` (constants, the base, `ϑˣ(Ω₁·β + t)` for every constant level `1 ≤ β < x`,
`ϑˣ(Ω₁·(x·(k+1) + b) + t)` for every `k < ω`, `b < x`, sums, `ω^t`), top `ϑˣ(Ω₁·(x·ω))` (`lvwTop`).  Its fields are
Lemma IMG (`LvWK.pkgLvW`), Lemma RS (`rsStep_LvW`), the comparison (`LvWT.uni_le`, from Lemma EXACT `LvWT.pi`), the
representation (`LvWT.lvw_rep`) and `lvw_small`; the top has the IMG package `LvWK.lvwTopPkg`.  Then, from the generic
theorems of `R2.XtGen`, `R2.LyCmp`, `R2.XtEnum`:

* `lvw_topIn_lv` (the top `ϑˣ(Ω₁·(x+x))` of `lvSys` is the term `th 1 0 0`), **`lvwLam_gt`: `Λ⁺(lvSys) < Λ(lvwSys) <
  Λ⁺(lvwSys)`**, `lvw_eqLv` (**`O = O_{lvSys}` below `Λ⁺(lvSys)`**), `lvw_atB1Lv` (**`O(Λ⁺(lvSys)) = ϑᵖ(Ω₁·(ρ+ρ)) +
  1`**), `lvwReachLv1` (**the exact reach at `Λ⁺(lvSys)`: `lh(ρ) = δ + ϑᵖ(Ω₁·(ρ+ρ)) + 1`**);
* `lvw_reach` (**`lh(ρ_λ) = δ_λ + O(λ)` for every restart `λ < Λ⁺(lvwSys)`**), `lvw_reachLam` (**the exact reach at
  `Λ(lvwSys)`: `lh(ρ) = δ + ϑᵖ(Ω₁·(ρ·ω))`**), `lvw_reachTerm`, `lvw_blk` (**Theorem BLK^O below `υ_{Λ⁺(lvwSys)}`**);
* `lvw_init` (**ENUM-REACH at every non-fixed restart of the range below `Λ⁺(lvwSys)`**), `lvw_capV` (**CapV
  there**), `lvw_capAt`, `lvw_iff`, `lvw_iso`, `lvw_fix_code`, `lvw_of_lv`, `lvwRoad3`, `lvwRoad`, `lvwRoad_cap` (the
  roads with the rest asked only outside `Λ⁺(lvwSys)`).

No new axiom beyond `R2.CitedLu` and `R2.CitedLv`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Lt Lu

/-- **Lemma RS with the target `t(ρ)`** for `LvWT`. -/
theorem rs_rstLvW {r : Ordinal.{0}}
    (h : RstK (upsilon r) (upsilon (r + ω)) (upsilon (r + ω + 1)))
    {s : LvWT} (hs : LvWT.CBt s (upsilon r)) (hρs : upsilon r ≤ LvWT.val s (upsilon r))
    (htarget : ∀ κ' < upsilon r, ∃ μ, κ' < upsilon μ ∧ upsilon (μ + ω + 1) < upsilon r ∧
      RstK (upsilon μ) (upsilon (μ + ω)) (upsilon (μ + ω + 1)) ∧
      ∀ g, upsilon μ ≤ g → g ≤ upsilon (μ + ω + 1) + LvWT.val s (upsilon μ) → le1 (upsilon μ) g) :
    le1 (upsilon r) (upsilon (r + ω + 1) + LvWT.val s (upsilon r) + 1) := by
  classical
  have hnx := upsilon_isNext r
  have hCs : ∀ σ, (∀ c ∈ (LvWT.cs s).toFinset, c < σ) → LvWT.CBt s σ := fun σ hσ =>
    LvWT.cbt_iff hs (fun c hc => hσ c (List.mem_toFinset.2 hc))
  refine rs_rstF (T := LvWT.val s) (C := (LvWT.cs s).toFinset) h
    (fun c hc => LvWT.cbt_cst hs c (List.mem_toFinset.1 hc)) hρs
    (LvWT.lvw_lt_ups h.ρE h.ρ1 hs hnx.1 hnx.2.1) ?_ ?_ htarget
  · intro σ hσ hB hCσ _
    exact (LvWT.pi hσ h.ρU hB s (hCs σ hCσ)).2
  · intro σ hσE hσρ _ hCσ
    exact LvWT.lvw_lt_next hσE (hσρ.trans h.ρ1) (hCs σ hCσ) hσρ h.ρU.2

/-- **Lemma RS for every term of `LvWT`** with constants below `ρ_λ`. -/
theorem rsStep_LvW {l : Ordinal.{0}} {s : LvWT} (hs : LvWT.CBt s (upsilon l)) :
    RsStep l (LvWT.val s) := by
  intro R htg
  by_cases hρs : upsilon l ≤ LvWT.val s (upsilon l)
  · exact rs_rstLvW R hs hρs htg
  · have hn : LvWT.noB s := by
      by_contra hn
      exact hρs (LvWT.le_of_not_noB R.ρE R.ρ1 s hs hn)
    set c := LvWT.val s (upsilon l) with hc
    have e : LvWT.val s = OT.ev (OT.k c) := funext (fun y => by
      rw [OT.ev_k, hc, LvWT.noB_val s hn y])
    have hcb : OT.CB (OT.k c) (upsilon l) := not_le.1 hρs
    rw [e] at htg
    have h := rs_rstT R hcb htg
    rwa [OT.ev_k] at h


theorem lvw_top_lt_next_ups {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) :
    lvwTop (upsilon l) < upsilon (l + ω + 1) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρU := upsPt_upsilon hl0
  have h1 : l < l + ω := lt_add_of_pos_right l omega0_pos
  have hτU := upsPt_upsilon (hl0.trans h1)
  exact (LvWT.lvw_top_lt_next (upsPt_inE hρU) (ups_lt_Om1 l hl1) (upsilon_normal.strictMono h1) hτU.2).trans
    (upsilon_normal.strictMono (lt_add_one _))

/-- **The term system of the levels `x + b`** (top `ϑˣ(Ω₁·(x+x))`). -/
noncomputable def lvwSys : XtSys where
  Tm := LvWT
  val := LvWT.val
  CB := LvWT.CBt
  cs := LvWT.cs
  cst := LvWT.cst
  top := lvwTop
  cb_cst := fun _ _ h => LvWT.cbt_cst h
  cb_iff := fun _ _ _ h hc => LvWT.cbt_iff h hc
  val_cst := fun _ _ => rfl
  cb_cstI := fun _ _ h => h
  lt_top := fun l hl hl1 t hCB => (LvWT.lvw_T (ups_inE hl) (ups_lt_Om1 l hl1) t hCB).2
  one_le_top := fun l hl hl1 =>
    one_le_iff_pos.2 (lvwTop_facts (ups_inE hl) (ups_lt_Om1 l hl1)).2.2.2.2.2.1.pos
  rep := fun l hl hl1 v hv => LvWT.lvw_rep (ups_inE hl) (ups_lt_Om1 l hl1) v hv
  top_lt := fun l hl hl1 => lvw_top_lt_next_ups hl hl1
  pkg := fun _ _ _ _ hCB h1 R => LvWK.pkgLvW R hCB h1
  rs := fun _ _ _ _ hCB => rsStep_LvW hCB
  uni_le := fun _ _ hσ hρ hB _ _ ht hu => LvWT.uni_le hσ hρ hB ht hu
  small := lvw_small

theorem lvwSys_top (x : Ordinal.{0}) : lvwSys.top x = vt x (Om1 * (x * ω)) := rfl

/-- **The top `ϑˣ(Ω₁·(x·ω))` of `lvwSys` has an IMG package.** -/
theorem lvwSys_topPkg : XtTopPkg lvwSys := fun _ _ _ R => LvWK.lvwTopPkg R

theorem lvw_lamLtB1 : xtLam lvwSys < xtB1 lvwSys := lyLamLtB1 lvwSys_topPkg

/-! ## Past `Λ⁺(lvSys)` -/

/-- **The top of `lvSys` inside `lvwSys`**: `ϑˣ(Ω₁·(x+x)) = th 1 0 0`, and `ϑˣ(Ω₁·(x+x)) + 1 < ϑˣ(Ω₁·(x·ω))`. -/
theorem lvw_topIn_lv : LyTopIn lvwSys lvSys := by
  have hL : ∀ x : Ordinal.{0}, lvwL x 1 0 = x + x := fun x => by
    unfold lvwL; rw [add_zero, Nat.cast_one, mul_add_one, mul_one]
  refine ⟨LvWT.th 1 0 (LvWT.cst 0), fun x hx _ => ⟨⟨(upsPt_inE hx).pos, (upsPt_inE hx).pos⟩, ?_⟩,
    fun l hl hl1 => ?_⟩
  · show vt x (Om1 * lvwL x 1 0 + 0) = lvSys.top x
    rw [add_zero, lvSys_top, hL]
  · have hρE := ups_inE hl
    have hρ1 := ups_lt_Om1 l hl1
    obtain ⟨-, -, -, -, -, hTE, -⟩ := lvwTop_facts hρE hρ1
    rw [lvSys_top]
    have hlt := (LvWT.lvw_T hρE hρ1 (LvWT.th 1 0 (LvWT.cst 0)) ⟨hρE.pos, hρE.pos⟩).2
    simp only [LvWT.val_th, LvWT.val_cst, add_zero, hL] at hlt
    exact (inE_indec hTE).add_lt hlt (lu_one_lt_E hTE)

/-- **`Λ⁺(lvSys) < Λ(lvwSys)`.** -/
theorem lvwLam_gt : xtB1 lvSys < xtLam lvwSys := lyLamGt lvSys_topPkg lvw_topIn_lv

/-- **`O = O_{lvSys}` below `Λ⁺(lvSys)`.** -/
theorem lvw_eqLv {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h : μ < xtB1 lvSys) : xtOrec lvwSys μ = xtOrec lvSys μ :=
  lyEq lvSys_topPkg lvw_topIn_lv hμ h

/-- **`O(Λ⁺(lvSys)) = ϑᵖ(Ω₁·(ρ+ρ)) + 1`.** -/
theorem lvw_atB1Lv : xtOrec lvwSys (xtB1 lvSys) =
    vt (upsilon (xtB1 lvSys)) (Om1 * (upsilon (xtB1 lvSys) + upsilon (xtB1 lvSys))) + 1 := by
  rw [lyAtB1 lvSys_topPkg lvw_topIn_lv, lvSys_top]

/-- **The exact reach at `Λ⁺(lvSys)`**: `lh(ρ) = δ + ϑᵖ(Ω₁·(ρ+ρ)) + 1`. -/
theorem lvwReachLv1 :
    IsReach R2C (upsilon (xtB1 lvSys))
      (upsilon (xtB1 lvSys + ω + 1) +
        (vt (upsilon (xtB1 lvSys)) (Om1 * (upsilon (xtB1 lvSys) + upsilon (xtB1 lvSys))) + 1)) := by
  have := lyReachB1 lvwSys_topPkg lvSys_topPkg lvw_topIn_lv
  rwa [lvSys_top] at this

/-- **The order of the frontiers**: `Λ⁺(lvSys) < Λ(lvwSys) < Λ⁺(lvwSys) < Ω₁`. -/
theorem lvw_order : xtB1 lvSys < xtLam lvwSys ∧ xtLam lvwSys < xtB1 lvwSys ∧ xtB1 lvwSys < Om1 :=
  ⟨lvwLam_gt, lvw_lamLtB1, xtB1_lt_Om1 lvwSys_topPkg⟩

/-! ## BLK^O and the exact reaches up to `Λ⁺(lvwSys)` -/

theorem lvw_nonfix : XtNonfix (xtOrec lvwSys) (xtB1 lvwSys) :=
  fun _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtB1_lt_Om1 lvwSys_topPkg))

/-- **The exact reach of every restart below `Λ⁺(lvwSys)`**: `lh(ρ_λ) = δ_λ + O(λ)`. -/
theorem lvw_reach {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < xtB1 lvwSys) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec lvwSys l) :=
  xtReach1 lvwSys_topPkg hl hlB

/-- **The exact reach at the frontier `Λ(lvwSys)`**: `lh(ρ) = δ + ϑᵖ(Ω₁·(ρ·ω))`. -/
theorem lvw_reachLam :
    IsReach R2C (upsilon (xtLam lvwSys))
      (upsilon (xtLam lvwSys + ω + 1) + vt (upsilon (xtLam lvwSys)) (Om1 * (upsilon (xtLam lvwSys) * ω))) := by
  rw [← lvwSys_top, ← xtOrec_Lam]
  exact xtReach1 lvwSys_topPkg xtLam_ri lvw_lamLtB1

/-- **The reach at the frontier of every term `t` of `lvwSys`** (constants below `ρ` at `Λ(lvwSys)`, value `≥ 1`):
`lh(ρ) = δ + t(ρ)`. -/
theorem lvw_reachTerm {t : LvWT} (hCB : LvWT.CBt t (upsilon (xtLam lvwSys)))
    (h1 : 1 ≤ LvWT.val t (upsilon (xtLam lvwSys))) :
    IsReach R2C (upsilon (xtLamT lvwSys t))
      (upsilon (xtLamT lvwSys t + ω + 1) + LvWT.val t (upsilon (xtLamT lvwSys t))) :=
  xtReach_LamT (X := lvwSys) hCB h1

/-- **Theorem BLK^O below `υ_{Λ⁺(lvwSys)}`** in `R₂^C`. -/
theorem lvw_blk :
    (∀ c d, c < d → d < upsilon (xtB1 lvwSys) → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 lvwSys ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 lvwSys →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec lvwSys l)) ∧
    (∀ α < upsilon (xtB1 lvwSys), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  xtBlk1 lvwSys_topPkg

/-! ## ENUM-REACH and the caps -/

variable {S : InaccSeq.{0}}

/-- **UPPER and LOWER (ENUM-REACH) at every restart of the range below `Λ⁺(lvwSys)` that is not a fixed point of
`υ`.** -/
theorem lvw_init {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 lvwSys) (hfix : l < upsilon l) :
    CdUpper S l ∧ CdLower S l :=
  xtInit (xtSpec1 lvwSys_topPkg) lvw_nonfix hr hl hfix

/-- **The cap of the values at every non-fixed restart of the range below `Λ⁺(lvwSys)`.** -/
theorem lvw_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 lvwSys) (hfix : l < upsilon l) :
    CdCapV S l := by
  have hww := cp_ww_lt_B0.trans_le hr.2.1
  exact xtCapV_nonfix (xtSpec1 lvwSys_topPkg) hr.1 hww hfix hl (cp_name_L hr.2.2.1)
    (lvw_nonfix l hr.1 hww hfix hl)

theorem lvw_capAt {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hB : cdB0 ≤ l) (hlΛ : l < xtB1 lvwSys)
    (hfix : l < upsilon l) (hname : upsilon l < Pv S η1) : CdCapAt S l := by
  have hww := cp_ww_lt_B0.trans_le hB
  exact xtCapAt_nonfix (xtSpec1 lvwSys_topPkg) hl hww hfix hlΛ hname (lvw_nonfix l hl hww hfix hlΛ)

/-- **Below `Λ⁺(lvwSys)`, ENUM-REACH is the equation `Θ_λ(m_λ) = O(λ)`.** -/
theorem lvw_iff {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < xtB1 lvwSys) :
    (CdUpper S l ∧ CdLower S l ↔ cdTheta S l (cdCode S l) = xtOrec lvwSys l) :=
  xtExact_iff (xtSpec1 lvwSys_topPkg) hl hlB

/-- **The offset at an isolated fixed point below `Λ⁺(lvwSys)`**: `O(F) = F`. -/
theorem lvw_iso {F : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hFB : F < xtB1 lvwSys)
    (hiso : CpIso F) : xtOrec lvwSys F = F :=
  xtIso hF hfix (hFB.trans (xtB1_lt_Om1 lvwSys_topPkg)) hiso

/-- **ENUM-REACH at an isolated fixed point of the range below `Λ⁺(lvwSys)` reduces to the code.** -/
theorem lvw_fix_code {F : Ordinal.{0}} (hr : CdRange S F) (hfix : upsilon F = F) (hFB : F < xtB1 lvwSys)
    (hiso : CpIso F) : (F ≤ cdCode S F → CdUpper S F) ∧ (cdCode S F ≤ Om1 → CdLower S F) :=
  xtFix_code (xtSpec1 lvwSys_topPkg) hr.1 hfix hFB (lvw_iso hr.1 hfix hFB hiso) (cp_name_L hr.2.2.1)

/-- **The hypotheses of `lvwRoad3` from those of `lvRoad3`.** -/
theorem lvw_of_lv (hU : ∀ l, CdRange S l → xtB1 lvSys ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 lvSys ≤ l → CdLower S l)
    (hT : ∀ l, CdRange S l → l < xtB1 lvSys → upsilon l = l → cdTheta S l (cdCode S l) = xtOrec lvSys l) :
    (∀ l, CdRange S l → xtB1 lvwSys ≤ l → CdUpper S l) ∧ (∀ l, CdRange S l → xtB1 lvwSys ≤ l → CdLower S l) ∧
      (∀ l, CdRange S l → l < xtB1 lvwSys → upsilon l = l → cdTheta S l (cdCode S l) = xtOrec lvwSys l) := by
  have hle : xtB1 lvSys ≤ xtB1 lvwSys := (lvwLam_gt.trans lvw_lamLtB1).le
  refine ⟨fun l hr h => hU l hr (hle.trans h), fun l hr h => hL l hr (hle.trans h), fun l hr hlB hfix => ?_⟩
  rcases lt_or_ge l (xtB1 lvSys) with h | h
  · rw [lvw_eqLv hr.1 h]; exact hT l hr h hfix
  · exact (lvw_iff hr.1 hlB).1 ⟨hU l hr h, hL l hr h⟩

/-- **The road with UPPER and LOWER asked only at `λ ≥ Λ⁺(lvwSys)`**, `Θ_F(m_F) = O(F)` at the fixed points of the
range below `Λ⁺(lvwSys)`, the cap of the values outside `Λ⁺(lvwSys)`, (CL), EQ, TCrest, (EMB₂). -/
theorem lvwRoad3 (hU : ∀ l, CdRange S l → xtB1 lvwSys ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 lvwSys ≤ l → CdLower S l)
    (hT : ∀ l, CdRange S l → l < xtB1 lvwSys → upsilon l = l → cdTheta S l (cdCode S l) = xtOrec lvwSys l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 lvwSys) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad3 (xtSpec1 lvwSys_topPkg) lvw_nonfix hU hL hT hV hC hEQ hrest hB2

/-- **The road with UPPER, LOWER and the cap of the values asked only outside `Λ⁺(lvwSys)`.** -/
theorem lvwRoad (hU : ∀ l, CdRange S l → XtOut (xtB1 lvwSys) l → CdUpper S l)
    (hL : ∀ l, CdRange S l → XtOut (xtB1 lvwSys) l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 lvwSys) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad (xtSpec1 lvwSys_topPkg) lvw_nonfix hU hL hV hC hEQ hrest hB2

/-- **The road with the caps asked only outside `Λ⁺(lvwSys)`**: CAP-0, CAP-1 outside, (CL), (TC), (EMB₂). -/
theorem lvwRoad_cap
    (h0 : ∀ l, IsRestartIdx l → cdB0 ≤ l → upsilon l < cdMstar S → XtOut (xtB1 lvwSys) l → CdCapAt S l)
    (h1 : ∀ l, IsRestartIdx l → cdB0 ≤ l → cdMstar S ≤ upsilon l → upsilon l < Nc.ncL S ω →
      cdCode S l < Nc.ncPp S → XtOut (xtB1 lvwSys) l → CdCapAt S l) (hC : CdCL S) (hTC : CdTC S)
    (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad_cap (xtSpec1 lvwSys_topPkg) lvw_nonfix h0 h1 hC hTC hB2

end Googology.Trans.PoR.InaccPsi.R2

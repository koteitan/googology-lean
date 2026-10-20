import Googology.Trans.PoR.InaccPsi.R2.LvEJ

/-!
# The term system of all levels below `ε_{x+1}`: BLK^O, the exact reaches and ENUM-REACH up to `Λ⁺(lveSys)`

`lveSys` is the term system of `LvET` (constants, the base, `ϑˣ(Ω₁·β + t)` for every constant level `1 ≤ β < x`,
`ϑˣ(Ω₁·l(x) + t)` for every level term `l` with the base (`x ≤ l(x) < ε_{x+1}`), sums, `ω^t`), top `ϑˣ(Ω₁·ε_{x+1})`
(`lveTop`).  Its fields are Lemma IMG (`LvEK.pkgLvE`), Lemma RS (`rsStep_LvE`), the comparison (`LvET.uni_le`, from
Lemma EXACT `LvET.pi`), the representation (`LvET.lve_rep`) and `lve_small`; the top has the IMG package
`LvEK.lveTopPkg`.  Then, from the generic theorems of `R2.XtGen`, `R2.LyCmp`, `R2.XtEnum`:

* `lve_topIn_lw` (the top `ϑˣ(Ω₁·(x·ω))` of `lvwSys` is the term `tl (ω^{x+1}) 0`), **`lveLam_gt`: `Λ⁺(lvwSys) <
  Λ(lveSys) < Λ⁺(lveSys)`**, `lve_eqLw` (**`O = O_{lvwSys}` below `Λ⁺(lvwSys)`**), `lve_atB1Lw`
  (**`O(Λ⁺(lvwSys)) = ϑᵖ(Ω₁·(ρ·ω)) + 1`**), `lveReachLw1` (**the exact reach at `Λ⁺(lvwSys)`: `lh(ρ) = δ +
  ϑᵖ(Ω₁·(ρ·ω)) + 1`**);
* `lve_reach` (**`lh(ρ_λ) = δ_λ + O(λ)` for every restart `λ < Λ⁺(lveSys)`**), `lve_reachLam` (**the exact reach at
  `Λ(lveSys)`: `lh(ρ) = δ + ϑᵖ(Ω₁·ε_{ρ+1})`**), `lve_reachTerm`, `lve_blk` (**Theorem BLK^O below
  `υ_{Λ⁺(lveSys)}`**);
* `lve_init` (**ENUM-REACH at every non-fixed restart of the range below `Λ⁺(lveSys)`**), `lve_capV` (**CapV
  there**), `lve_capAt`, `lve_iff`, `lve_iso`, `lve_fix_code`, `lve_of_lw`, `lveRoad3`, `lveRoad`, `lveRoad_cap` (the
  roads with the rest asked only outside `Λ⁺(lveSys)`).

No new axiom beyond `R2.CitedLu` and `R2.CitedLv`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Lt Lu

/-- **Lemma RS with the target `t(ρ)`** for `LvET`. -/
theorem rs_rstLvE {r : Ordinal.{0}}
    (h : RstK (upsilon r) (upsilon (r + ω)) (upsilon (r + ω + 1)))
    {s : LvET} (hs : LvET.CBt s (upsilon r)) (hρs : upsilon r ≤ LvET.val s (upsilon r))
    (htarget : ∀ κ' < upsilon r, ∃ μ, κ' < upsilon μ ∧ upsilon (μ + ω + 1) < upsilon r ∧
      RstK (upsilon μ) (upsilon (μ + ω)) (upsilon (μ + ω + 1)) ∧
      ∀ g, upsilon μ ≤ g → g ≤ upsilon (μ + ω + 1) + LvET.val s (upsilon μ) → le1 (upsilon μ) g) :
    le1 (upsilon r) (upsilon (r + ω + 1) + LvET.val s (upsilon r) + 1) := by
  classical
  have hnx := upsilon_isNext r
  have hCs : ∀ σ, (∀ c ∈ (LvET.cs s).toFinset, c < σ) → LvET.CBt s σ := fun σ hσ =>
    LvET.cbt_iff hs (fun c hc => hσ c (List.mem_toFinset.2 hc))
  refine rs_rstF (T := LvET.val s) (C := (LvET.cs s).toFinset) h
    (fun c hc => LvET.cbt_cst hs c (List.mem_toFinset.1 hc)) hρs
    (LvET.lve_lt_ups h.ρE h.ρ1 hs hnx.1 hnx.2.1) ?_ ?_ htarget
  · intro σ hσ hB hCσ _
    exact (LvET.pi hσ h.ρU hB s (hCs σ hCσ)).2
  · intro σ hσE hσρ _ hCσ
    exact LvET.lve_lt_next hσE (hσρ.trans h.ρ1) (hCs σ hCσ) hσρ h.ρU.2

/-- **Lemma RS for every term of `LvET`** with constants below `ρ_λ`. -/
theorem rsStep_LvE {l : Ordinal.{0}} {s : LvET} (hs : LvET.CBt s (upsilon l)) :
    RsStep l (LvET.val s) := by
  intro R htg
  by_cases hρs : upsilon l ≤ LvET.val s (upsilon l)
  · exact rs_rstLvE R hs hρs htg
  · have hn : LvET.noB s := by
      by_contra hn
      exact hρs (LvET.le_of_not_noB R.ρE R.ρ1 s hs hn)
    set c := LvET.val s (upsilon l) with hc
    have e : LvET.val s = OT.ev (OT.k c) := funext (fun y => by
      rw [OT.ev_k, hc, LvET.noB_val s hn y])
    have hcb : OT.CB (OT.k c) (upsilon l) := not_le.1 hρs
    rw [e] at htg
    have h := rs_rstT R hcb htg
    rwa [OT.ev_k] at h


theorem lve_top_lt_next_ups {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) :
    lveTop (upsilon l) < upsilon (l + ω + 1) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρU := upsPt_upsilon hl0
  have h1 : l < l + ω := lt_add_of_pos_right l omega0_pos
  have hτU := upsPt_upsilon (hl0.trans h1)
  exact (LvET.lve_top_lt_next (upsPt_inE hρU) (ups_lt_Om1 l hl1) (upsilon_normal.strictMono h1) hτU.2).trans
    (upsilon_normal.strictMono (lt_add_one _))

/-- **The term system of the levels `x + b`** (top `ϑˣ(Ω₁·(x+x))`). -/
noncomputable def lveSys : XtSys where
  Tm := LvET
  val := LvET.val
  CB := LvET.CBt
  cs := LvET.cs
  cst := LvET.cst
  top := lveTop
  cb_cst := fun _ _ h => LvET.cbt_cst h
  cb_iff := fun _ _ _ h hc => LvET.cbt_iff h hc
  val_cst := fun _ _ => rfl
  cb_cstI := fun _ _ h => h
  lt_top := fun l hl hl1 t hCB => (LvET.lve_T (ups_inE hl) (ups_lt_Om1 l hl1) t hCB).2
  one_le_top := fun l hl hl1 =>
    one_le_iff_pos.2 (lveTop_facts (ups_inE hl) (ups_lt_Om1 l hl1)).2.2.2.2.2.1.pos
  rep := fun l hl hl1 v hv => LvET.lve_rep (ups_inE hl) (ups_lt_Om1 l hl1) v hv
  top_lt := fun l hl hl1 => lve_top_lt_next_ups hl hl1
  pkg := fun _ _ _ _ hCB h1 R => LvEK.pkgLvE R hCB h1
  rs := fun _ _ _ _ hCB => rsStep_LvE hCB
  uni_le := fun _ _ hσ hρ hB _ _ ht hu => LvET.uni_le hσ hρ hB ht hu
  small := lve_small

theorem lveSys_top (x : Ordinal.{0}) : lveSys.top x = vt x (Om1 * eN x) := rfl

/-- **The top `ϑˣ(Ω₁·ε_{x+1})` of `lveSys` has an IMG package.** -/
theorem lveSys_topPkg : XtTopPkg lveSys := fun _ _ _ R => LvEK.lveTopPkg R

theorem lve_lamLtB1 : xtLam lveSys < xtB1 lveSys := lyLamLtB1 lveSys_topPkg

/-! ## Past `Λ⁺(lvwSys)` -/

/-- **The top of `lvwSys` inside `lveSys`**: `ϑˣ(Ω₁·(x·ω)) = tl (ω^{x+1}) 0`, and `ϑˣ(Ω₁·(x·ω)) + 1 <
`ϑˣ(Ω₁·ε_{x+1})`. -/
theorem lve_topIn_lw : LyTopIn lveSys lvwSys := by
  have hL : ∀ x : Ordinal.{0}, InE x → LvET.val (.pw (.sm .bs (.cst 1))) x = x * ω := fun x hx => by
    simp only [LvET.val_pw, LvET.val_sm, LvET.val_bs, LvET.val_cst]
    rw [opow_add, opow_one, show ω ^ x = x from hx]
  have hcb : ∀ x : Ordinal.{0}, InE x → LvET.CBt (.tl (.pw (.sm .bs (.cst 1))) (.cst 0)) x := fun x hx =>
    ⟨⟨trivial, trivial⟩, Or.inl trivial, ⟨trivial, lu_one_lt_E hx⟩, hx.pos⟩
  refine ⟨LvET.tl (.pw (.sm .bs (.cst 1))) (.cst 0), fun x hx _ => ⟨hcb x (upsPt_inE hx), ?_⟩,
    fun l hl hl1 => ?_⟩
  · show vt x (Om1 * LvET.val (.pw (.sm .bs (.cst 1))) x + 0) = lvwSys.top x
    rw [add_zero, lvwSys_top, hL x (upsPt_inE hx)]
  · have hρE := ups_inE hl
    have hρ1 := ups_lt_Om1 l hl1
    obtain ⟨-, -, -, -, -, hTE, -⟩ := lveTop_facts hρE hρ1
    rw [lvwSys_top]
    have hlt := (LvET.lve_T hρE hρ1 _ (hcb _ hρE)).2
    simp only [LvET.val_tl, LvET.val_cst, add_zero, hL _ hρE] at hlt
    exact (inE_indec hTE).add_lt hlt (lu_one_lt_E hTE)

/-- **`Λ⁺(lvwSys) < Λ(lveSys)`.** -/
theorem lveLam_gt : xtB1 lvwSys < xtLam lveSys := lyLamGt lvwSys_topPkg lve_topIn_lw

/-- **`O = O_{lvwSys}` below `Λ⁺(lvwSys)`.** -/
theorem lve_eqLw {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h : μ < xtB1 lvwSys) : xtOrec lveSys μ = xtOrec lvwSys μ :=
  lyEq lvwSys_topPkg lve_topIn_lw hμ h

/-- **`O(Λ⁺(lvwSys)) = ϑᵖ(Ω₁·(ρ·ω)) + 1`.** -/
theorem lve_atB1Lw : xtOrec lveSys (xtB1 lvwSys) =
    vt (upsilon (xtB1 lvwSys)) (Om1 * (upsilon (xtB1 lvwSys) * ω)) + 1 := by
  rw [lyAtB1 lvwSys_topPkg lve_topIn_lw, lvwSys_top]

/-- **The exact reach at `Λ⁺(lvwSys)`**: `lh(ρ) = δ + ϑᵖ(Ω₁·(ρ·ω)) + 1`. -/
theorem lveReachLw1 :
    IsReach R2C (upsilon (xtB1 lvwSys))
      (upsilon (xtB1 lvwSys + ω + 1) +
        (vt (upsilon (xtB1 lvwSys)) (Om1 * (upsilon (xtB1 lvwSys) * ω)) + 1)) := by
  have := lyReachB1 lveSys_topPkg lvwSys_topPkg lve_topIn_lw
  rwa [lvwSys_top] at this

/-- **The order of the frontiers**: `Λ⁺(lvwSys) < Λ(lveSys) < Λ⁺(lveSys) < Ω₁`. -/
theorem lve_order : xtB1 lvwSys < xtLam lveSys ∧ xtLam lveSys < xtB1 lveSys ∧ xtB1 lveSys < Om1 :=
  ⟨lveLam_gt, lve_lamLtB1, xtB1_lt_Om1 lveSys_topPkg⟩

/-! ## BLK^O and the exact reaches up to `Λ⁺(lveSys)` -/

theorem lve_nonfix : XtNonfix (xtOrec lveSys) (xtB1 lveSys) :=
  fun _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtB1_lt_Om1 lveSys_topPkg))

/-- **The exact reach of every restart below `Λ⁺(lveSys)`**: `lh(ρ_λ) = δ_λ + O(λ)`. -/
theorem lve_reach {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < xtB1 lveSys) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec lveSys l) :=
  xtReach1 lveSys_topPkg hl hlB

/-- **The exact reach at the frontier `Λ(lveSys)`**: `lh(ρ) = δ + ϑᵖ(Ω₁·ε_{ρ+1})`. -/
theorem lve_reachLam :
    IsReach R2C (upsilon (xtLam lveSys))
      (upsilon (xtLam lveSys + ω + 1) + vt (upsilon (xtLam lveSys)) (Om1 * eN (upsilon (xtLam lveSys)))) := by
  rw [← lveSys_top, ← xtOrec_Lam]
  exact xtReach1 lveSys_topPkg xtLam_ri lve_lamLtB1

/-- **The reach at the frontier of every term `t` of `lveSys`** (constants below `ρ` at `Λ(lveSys)`, value `≥ 1`):
`lh(ρ) = δ + t(ρ)`. -/
theorem lve_reachTerm {t : LvET} (hCB : LvET.CBt t (upsilon (xtLam lveSys)))
    (h1 : 1 ≤ LvET.val t (upsilon (xtLam lveSys))) :
    IsReach R2C (upsilon (xtLamT lveSys t))
      (upsilon (xtLamT lveSys t + ω + 1) + LvET.val t (upsilon (xtLamT lveSys t))) :=
  xtReach_LamT (X := lveSys) hCB h1

/-- **Theorem BLK^O below `υ_{Λ⁺(lveSys)}`** in `R₂^C`. -/
theorem lve_blk :
    (∀ c d, c < d → d < upsilon (xtB1 lveSys) → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 lveSys ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 lveSys →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec lveSys l)) ∧
    (∀ α < upsilon (xtB1 lveSys), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  xtBlk1 lveSys_topPkg

/-! ## ENUM-REACH and the caps -/

variable {S : InaccSeq.{0}}

/-- **UPPER and LOWER (ENUM-REACH) at every restart of the range below `Λ⁺(lveSys)` that is not a fixed point of
`υ`.** -/
theorem lve_init {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 lveSys) (hfix : l < upsilon l) :
    CdUpper S l ∧ CdLower S l :=
  xtInit (xtSpec1 lveSys_topPkg) lve_nonfix hr hl hfix

/-- **The cap of the values at every non-fixed restart of the range below `Λ⁺(lveSys)`.** -/
theorem lve_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 lveSys) (hfix : l < upsilon l) :
    CdCapV S l := by
  have hww := cp_ww_lt_B0.trans_le hr.2.1
  exact xtCapV_nonfix (xtSpec1 lveSys_topPkg) hr.1 hww hfix hl (cp_name_L hr.2.2.1)
    (lve_nonfix l hr.1 hww hfix hl)

theorem lve_capAt {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hB : cdB0 ≤ l) (hlΛ : l < xtB1 lveSys)
    (hfix : l < upsilon l) (hname : upsilon l < Pv S η1) : CdCapAt S l := by
  have hww := cp_ww_lt_B0.trans_le hB
  exact xtCapAt_nonfix (xtSpec1 lveSys_topPkg) hl hww hfix hlΛ hname (lve_nonfix l hl hww hfix hlΛ)

/-- **Below `Λ⁺(lveSys)`, ENUM-REACH is the equation `Θ_λ(m_λ) = O(λ)`.** -/
theorem lve_iff {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < xtB1 lveSys) :
    (CdUpper S l ∧ CdLower S l ↔ cdTheta S l (cdCode S l) = xtOrec lveSys l) :=
  xtExact_iff (xtSpec1 lveSys_topPkg) hl hlB

/-- **The offset at an isolated fixed point below `Λ⁺(lveSys)`**: `O(F) = F`. -/
theorem lve_iso {F : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hFB : F < xtB1 lveSys)
    (hiso : CpIso F) : xtOrec lveSys F = F :=
  xtIso hF hfix (hFB.trans (xtB1_lt_Om1 lveSys_topPkg)) hiso

/-- **ENUM-REACH at an isolated fixed point of the range below `Λ⁺(lveSys)` reduces to the code.** -/
theorem lve_fix_code {F : Ordinal.{0}} (hr : CdRange S F) (hfix : upsilon F = F) (hFB : F < xtB1 lveSys)
    (hiso : CpIso F) : (F ≤ cdCode S F → CdUpper S F) ∧ (cdCode S F ≤ Om1 → CdLower S F) :=
  xtFix_code (xtSpec1 lveSys_topPkg) hr.1 hfix hFB (lve_iso hr.1 hfix hFB hiso) (cp_name_L hr.2.2.1)

/-- **The hypotheses of `lveRoad3` from those of `lvwRoad3`.** -/
theorem lve_of_lw (hU : ∀ l, CdRange S l → xtB1 lvwSys ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 lvwSys ≤ l → CdLower S l)
    (hT : ∀ l, CdRange S l → l < xtB1 lvwSys → upsilon l = l → cdTheta S l (cdCode S l) = xtOrec lvwSys l) :
    (∀ l, CdRange S l → xtB1 lveSys ≤ l → CdUpper S l) ∧ (∀ l, CdRange S l → xtB1 lveSys ≤ l → CdLower S l) ∧
      (∀ l, CdRange S l → l < xtB1 lveSys → upsilon l = l → cdTheta S l (cdCode S l) = xtOrec lveSys l) := by
  have hle : xtB1 lvwSys ≤ xtB1 lveSys := (lveLam_gt.trans lve_lamLtB1).le
  refine ⟨fun l hr h => hU l hr (hle.trans h), fun l hr h => hL l hr (hle.trans h), fun l hr hlB hfix => ?_⟩
  rcases lt_or_ge l (xtB1 lvwSys) with h | h
  · rw [lve_eqLw hr.1 h]; exact hT l hr h hfix
  · exact (lve_iff hr.1 hlB).1 ⟨hU l hr h, hL l hr h⟩

/-- **The road with UPPER and LOWER asked only at `λ ≥ Λ⁺(lveSys)`**, `Θ_F(m_F) = O(F)` at the fixed points of the
range below `Λ⁺(lveSys)`, the cap of the values outside `Λ⁺(lveSys)`, (CL), EQ, TCrest, (EMB₂). -/
theorem lveRoad3 (hU : ∀ l, CdRange S l → xtB1 lveSys ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 lveSys ≤ l → CdLower S l)
    (hT : ∀ l, CdRange S l → l < xtB1 lveSys → upsilon l = l → cdTheta S l (cdCode S l) = xtOrec lveSys l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 lveSys) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad3 (xtSpec1 lveSys_topPkg) lve_nonfix hU hL hT hV hC hEQ hrest hB2

/-- **The road with UPPER, LOWER and the cap of the values asked only outside `Λ⁺(lveSys)`.** -/
theorem lveRoad (hU : ∀ l, CdRange S l → XtOut (xtB1 lveSys) l → CdUpper S l)
    (hL : ∀ l, CdRange S l → XtOut (xtB1 lveSys) l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 lveSys) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad (xtSpec1 lveSys_topPkg) lve_nonfix hU hL hV hC hEQ hrest hB2

/-- **The road with the caps asked only outside `Λ⁺(lveSys)`**: CAP-0, CAP-1 outside, (CL), (TC), (EMB₂). -/
theorem lveRoad_cap
    (h0 : ∀ l, IsRestartIdx l → cdB0 ≤ l → upsilon l < cdMstar S → XtOut (xtB1 lveSys) l → CdCapAt S l)
    (h1 : ∀ l, IsRestartIdx l → cdB0 ≤ l → cdMstar S ≤ upsilon l → upsilon l < Nc.ncL S ω →
      cdCode S l < Nc.ncPp S → XtOut (xtB1 lveSys) l → CdCapAt S l) (hC : CdCL S) (hTC : CdTC S)
    (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad_cap (xtSpec1 lveSys_topPkg) lve_nonfix h0 h1 hC hTC hB2

end Googology.Trans.PoR.InaccPsi.R2

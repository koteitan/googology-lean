import Googology.Trans.PoR.InaccPsi.R2.LvJ
import Googology.Trans.PoR.InaccPsi.R2.LuSys

/-!
# The term system of the levels `x + b`: BLK^O, the exact reaches and ENUM-REACH up to `Λ⁺(lvSys)`

`lvSys` is the term system of `LvT` (constants, the base, `ϑˣ(Ω₁·β + t)` for every constant level `1 ≤ β < x`,
`ϑˣ(Ω₁·(x + b) + t)` for every `b < x`, sums, `ω^t`), top `ϑˣ(Ω₁·(x + x))` (`lvTop`).  Its fields are Lemma IMG
(`LvK.pkgLv`), Lemma RS (`rsStep_Lv`), the comparison (`LvT.uni_le`, from Lemma EXACT `LvT.pi`), the representation
(`LvT.lv_rep`) and `lv_small`; the top has the IMG package `LvK.lvTopPkg`.  Then, from the generic theorems of
`R2.XtGen`, `R2.LyCmp`, `R2.XtEnum`:

* `lv_topIn_lu` (the top `ϑˣ(Ω₁·x)` of `luSys` is the term `th 0 0`), **`lvLam_gt`: `Λ⁺(luSys) < Λ(lvSys) <
  Λ⁺(lvSys)`**, `lv_eqLu` (**`O = O_{luSys}` below `Λ⁺(luSys)`**), `lv_atB1Lu` (**`O(Λ⁺(luSys)) = ϑᵖ(Ω₁·ρ) + 1`**),
  `lvReachLu1` (**the exact reach at `Λ⁺(luSys)`: `lh(ρ) = δ + ϑᵖ(Ω₁·ρ) + 1`**);
* `lv_reach` (**`lh(ρ_λ) = δ_λ + O(λ)` for every restart `λ < Λ⁺(lvSys)`**), `lv_reachLam` (**the exact reach at
  `Λ(lvSys)`: `lh(ρ) = δ + ϑᵖ(Ω₁·(ρ+ρ))`**), `lv_reachTerm`, `lv_blk` (**Theorem BLK^O below `υ_{Λ⁺(lvSys)}`**);
* `lv_init` (**ENUM-REACH at every non-fixed restart of the range below `Λ⁺(lvSys)`**), `lv_capV` (**CapV there**),
  `lv_capAt`, `lv_iff`, `lv_iso`, `lv_fix_code`, `lv_of_lu`, `lvRoad3`, `lvRoad`, `lvRoad_cap` (the roads with the rest
  asked only outside `Λ⁺(lvSys)`).

No new axiom beyond `R2.CitedLu` and `R2.CitedLv`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Lt Lu

theorem lv_small : ∀ t : LvT,
    (∀ x y, LvT.val t x = LvT.val t y) ∨
      (∀ x, InE x → x < Om1 → LvT.CBt t x → x ≤ LvT.val t x) := by
  intro t
  induction t with
  | cst a => exact Or.inl (fun _ _ => rfl)
  | bs => exact Or.inr (fun x _ _ _ => le_rfl)
  | th0 b t ih =>
      right
      intro x hx hx1 hCB
      obtain ⟨htT, htlt⟩ := LvT.lv_T hx hx1 t hCB.2.2
      have ht1 : LvT.val t x < Om1 := htlt.trans (LvT.lvTop_facts hx hx1).2.2.2.2.1
      have hfacts := Lu.lu_th_facts hx hx1 hCB.1 hCB.2.1 htT ht1
      exact (hfacts.2.2.2.1).le
  | th b t ih =>
      right
      intro x hx hx1 hCB
      obtain ⟨htT, htlt⟩ := LvT.lv_T hx hx1 t hCB.2
      have ht1 : LvT.val t x < Om1 := htlt.trans (LvT.lvTop_facts hx hx1).2.2.2.2.1
      have hfacts := Lv.th_facts hx hx1 hCB.1 htT ht1
      exact hfacts.2.2.2.1.le
  | sm a b iha ihb =>
      rcases iha with ha | ha <;> rcases ihb with hb | hb
      · exact Or.inl (fun x y => by simp [LvT.val_sm, ha x y, hb x y])
      · exact Or.inr (fun x hx hx1 hCB =>
          (hb x hx hx1 hCB.2).trans le_add_self)
      · exact Or.inr (fun x hx hx1 hCB =>
          (ha x hx hx1 hCB.1).trans le_self_add)
      · exact Or.inr (fun x hx hx1 hCB =>
          (ha x hx hx1 hCB.1).trans le_self_add)
  | pw t ih =>
      rcases ih with ht | ht
      · exact Or.inl (fun x y => by simp [LvT.val_pw, ht x y])
      · exact Or.inr (fun x hx hx1 hCB => by
          have hpow : ω ^ x ≤ ω ^ LvT.val t x :=
            opow_le_opow_right omega0_pos (ht x hx hx1 hCB)
          calc
            x = ω ^ x := hx.symm
            _ ≤ ω ^ LvT.val t x := hpow)

/-- **Lemma RS with the target `t(ρ)`** for `LvT`. -/
theorem rs_rstLv {r : Ordinal.{0}}
    (h : RstK (upsilon r) (upsilon (r + ω)) (upsilon (r + ω + 1)))
    {s : LvT} (hs : LvT.CBt s (upsilon r)) (hρs : upsilon r ≤ LvT.val s (upsilon r))
    (htarget : ∀ κ' < upsilon r, ∃ μ, κ' < upsilon μ ∧ upsilon (μ + ω + 1) < upsilon r ∧
      RstK (upsilon μ) (upsilon (μ + ω)) (upsilon (μ + ω + 1)) ∧
      ∀ g, upsilon μ ≤ g → g ≤ upsilon (μ + ω + 1) + LvT.val s (upsilon μ) → le1 (upsilon μ) g) :
    le1 (upsilon r) (upsilon (r + ω + 1) + LvT.val s (upsilon r) + 1) := by
  classical
  have hnx := upsilon_isNext r
  have hCs : ∀ σ, (∀ c ∈ (LvT.cs s).toFinset, c < σ) → LvT.CBt s σ := fun σ hσ =>
    LvT.cbt_iff hs (fun c hc => hσ c (List.mem_toFinset.2 hc))
  refine rs_rstF (T := LvT.val s) (C := (LvT.cs s).toFinset) h
    (fun c hc => Lv.cbt_cst hs c (List.mem_toFinset.1 hc)) hρs
    (LvT.lv_lt_ups h.ρE h.ρ1 hs hnx.1 hnx.2.1) ?_ ?_ htarget
  · intro σ hσ hB hCσ _
    exact (LvT.pi hσ h.ρU hB s (hCs σ hCσ)).2
  · intro σ hσE hσρ _ hCσ
    exact LvT.lv_lt_next hσE (hσρ.trans h.ρ1) (hCs σ hCσ) hσρ h.ρU.2

/-- **Lemma RS for every term of `LvT`** with constants below `ρ_λ`. -/
theorem rsStep_Lv {l : Ordinal.{0}} {s : LvT} (hs : LvT.CBt s (upsilon l)) :
    RsStep l (LvT.val s) := by
  intro R htg
  by_cases hρs : upsilon l ≤ LvT.val s (upsilon l)
  · exact rs_rstLv R hs hρs htg
  · have hn : LvT.noB s := by
      by_contra hn
      exact hρs (LvT.le_of_not_noB R.ρE R.ρ1 s hs hn)
    set c := LvT.val s (upsilon l) with hc
    have e : LvT.val s = OT.ev (OT.k c) := funext (fun y => by
      rw [OT.ev_k, hc, LvT.noB_val s hn y])
    have hcb : OT.CB (OT.k c) (upsilon l) := not_le.1 hρs
    rw [e] at htg
    have h := rs_rstT R hcb htg
    rwa [OT.ev_k] at h


theorem lv_top_lt_next_ups {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) :
    lvTop (upsilon l) < upsilon (l + ω + 1) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρU := upsPt_upsilon hl0
  have h1 : l < l + ω := lt_add_of_pos_right l omega0_pos
  have hτU := upsPt_upsilon (hl0.trans h1)
  exact (LvT.lv_top_lt_next (upsPt_inE hρU) (ups_lt_Om1 l hl1) (upsilon_normal.strictMono h1) hτU.2).trans
    (upsilon_normal.strictMono (lt_add_one _))

/-- **The term system of the levels `x + b`** (top `ϑˣ(Ω₁·(x+x))`). -/
noncomputable def lvSys : XtSys where
  Tm := LvT
  val := LvT.val
  CB := LvT.CBt
  cs := LvT.cs
  cst := LvT.cst
  top := lvTop
  cb_cst := fun _ _ h => Lv.cbt_cst h
  cb_iff := fun _ _ _ h hc => LvT.cbt_iff h hc
  val_cst := fun _ _ => rfl
  cb_cstI := fun _ _ h => h
  lt_top := fun l hl hl1 t hCB => (LvT.lv_T (ups_inE hl) (ups_lt_Om1 l hl1) t hCB).2
  one_le_top := fun l hl hl1 =>
    one_le_iff_pos.2 (LvT.lvTop_facts (ups_inE hl) (ups_lt_Om1 l hl1)).2.2.2.2.2.pos
  rep := fun l hl hl1 v hv => LvT.lv_rep (ups_inE hl) (ups_lt_Om1 l hl1) v hv
  top_lt := fun l hl hl1 => lv_top_lt_next_ups hl hl1
  pkg := fun _ _ _ _ hCB h1 R => LvK.pkgLv R hCB h1
  rs := fun _ _ _ _ hCB => rsStep_Lv hCB
  uni_le := fun _ _ hσ hρ hB _ _ ht hu => LvT.uni_le hσ hρ hB ht hu
  small := lv_small

theorem lvSys_top (x : Ordinal.{0}) : lvSys.top x = vt x (Om1 * (x + x)) := rfl

/-- **The top `ϑˣ(Ω₁·(x+x))` of `lvSys` has an IMG package.** -/
theorem lvSys_topPkg : XtTopPkg lvSys := fun _ _ _ R => LvK.lvTopPkg R

theorem lv_lamLtB1 : xtLam lvSys < xtB1 lvSys := lyLamLtB1 lvSys_topPkg

/-! ## Past `Λ⁺(luSys)` -/

/-- **The top of `luSys` inside `lvSys`**: `ϑˣ(Ω₁·x) = th 0 0`, and `ϑˣ(Ω₁·x) + 1 < ϑˣ(Ω₁·(x+x))`. -/
theorem lv_topIn_lu : LyTopIn lvSys luSys := by
  refine ⟨LvT.th 0 (LvT.cst 0), fun x hx _ => ⟨⟨(upsPt_inE hx).pos, (upsPt_inE hx).pos⟩, ?_⟩,
    fun l hl hl1 => ?_⟩
  · show vt x (Om1 * (x + 0) + 0) = luSys.top x
    rw [add_zero, add_zero, luSys_top]
  · have hρE := ups_inE hl
    have hρ1 := ups_lt_Om1 l hl1
    obtain ⟨-, -, -, -, -, hTE⟩ := LvT.lvTop_facts hρE hρ1
    rw [luSys_top, lvSys_top]
    have hlt := (LvT.lv_T hρE hρ1 (LvT.th 0 (LvT.cst 0)) ⟨hρE.pos, hρE.pos⟩).2
    simp only [LvT.val_th, LvT.val_cst, add_zero] at hlt
    exact (inE_indec hTE).add_lt hlt (lu_one_lt_E hTE)

/-- **`Λ⁺(luSys) < Λ(lvSys)`.** -/
theorem lvLam_gt : xtB1 luSys < xtLam lvSys := lyLamGt luSys_topPkg lv_topIn_lu

/-- **`O = O_{luSys}` below `Λ⁺(luSys)`.** -/
theorem lv_eqLu {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h : μ < xtB1 luSys) : xtOrec lvSys μ = xtOrec luSys μ :=
  lyEq luSys_topPkg lv_topIn_lu hμ h

/-- **`O(Λ⁺(luSys)) = ϑᵖ(Ω₁·ρ) + 1`.** -/
theorem lv_atB1Lu : xtOrec lvSys (xtB1 luSys) = vt (upsilon (xtB1 luSys)) (Om1 * upsilon (xtB1 luSys)) + 1 := by
  rw [lyAtB1 luSys_topPkg lv_topIn_lu, luSys_top]

/-- **The exact reach at `Λ⁺(luSys)`**: `lh(ρ) = δ + ϑᵖ(Ω₁·ρ) + 1`. -/
theorem lvReachLu1 :
    IsReach R2C (upsilon (xtB1 luSys))
      (upsilon (xtB1 luSys + ω + 1) + (vt (upsilon (xtB1 luSys)) (Om1 * upsilon (xtB1 luSys)) + 1)) := by
  have := lyReachB1 lvSys_topPkg luSys_topPkg lv_topIn_lu
  rwa [luSys_top] at this

/-- **The order of the frontiers**: `Λ⁺(luSys) < Λ(lvSys) < Λ⁺(lvSys) < Ω₁`. -/
theorem lv_order : xtB1 luSys < xtLam lvSys ∧ xtLam lvSys < xtB1 lvSys ∧ xtB1 lvSys < Om1 :=
  ⟨lvLam_gt, lv_lamLtB1, xtB1_lt_Om1 lvSys_topPkg⟩

/-! ## BLK^O and the exact reaches up to `Λ⁺(lvSys)` -/

theorem lv_nonfix : XtNonfix (xtOrec lvSys) (xtB1 lvSys) :=
  fun _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtB1_lt_Om1 lvSys_topPkg))

/-- **The exact reach of every restart below `Λ⁺(lvSys)`**: `lh(ρ_λ) = δ_λ + O(λ)`. -/
theorem lv_reach {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < xtB1 lvSys) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec lvSys l) :=
  xtReach1 lvSys_topPkg hl hlB

/-- **The exact reach at the frontier `Λ(lvSys)`**: `lh(ρ) = δ + ϑᵖ(Ω₁·(ρ+ρ))`. -/
theorem lv_reachLam :
    IsReach R2C (upsilon (xtLam lvSys))
      (upsilon (xtLam lvSys + ω + 1) +
        vt (upsilon (xtLam lvSys)) (Om1 * (upsilon (xtLam lvSys) + upsilon (xtLam lvSys)))) := by
  rw [← lvSys_top, ← xtOrec_Lam]
  exact xtReach1 lvSys_topPkg xtLam_ri lv_lamLtB1

/-- **The reach at the frontier of every term `t` of `lvSys`** (constants below `ρ` at `Λ(lvSys)`, value `≥ 1`):
`lh(ρ) = δ + t(ρ)`. -/
theorem lv_reachTerm {t : LvT} (hCB : LvT.CBt t (upsilon (xtLam lvSys)))
    (h1 : 1 ≤ LvT.val t (upsilon (xtLam lvSys))) :
    IsReach R2C (upsilon (xtLamT lvSys t))
      (upsilon (xtLamT lvSys t + ω + 1) + LvT.val t (upsilon (xtLamT lvSys t))) :=
  xtReach_LamT (X := lvSys) hCB h1

/-- **Theorem BLK^O below `υ_{Λ⁺(lvSys)}`** in `R₂^C`. -/
theorem lv_blk :
    (∀ c d, c < d → d < upsilon (xtB1 lvSys) → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 lvSys ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 lvSys →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec lvSys l)) ∧
    (∀ α < upsilon (xtB1 lvSys), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  xtBlk1 lvSys_topPkg

/-! ## ENUM-REACH and the caps -/

variable {S : InaccSeq.{0}}

/-- **UPPER and LOWER (ENUM-REACH) at every restart of the range below `Λ⁺(lvSys)` that is not a fixed point of
`υ`.** -/
theorem lv_init {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 lvSys) (hfix : l < upsilon l) :
    CdUpper S l ∧ CdLower S l :=
  xtInit (xtSpec1 lvSys_topPkg) lv_nonfix hr hl hfix

/-- **The cap of the values at every non-fixed restart of the range below `Λ⁺(lvSys)`.** -/
theorem lv_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 lvSys) (hfix : l < upsilon l) :
    CdCapV S l := by
  have hww := cp_ww_lt_B0.trans_le hr.2.1
  exact xtCapV_nonfix (xtSpec1 lvSys_topPkg) hr.1 hww hfix hl (cp_name_L hr.2.2.1)
    (lv_nonfix l hr.1 hww hfix hl)

theorem lv_capAt {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hB : cdB0 ≤ l) (hlΛ : l < xtB1 lvSys)
    (hfix : l < upsilon l) (hname : upsilon l < Pv S η1) : CdCapAt S l := by
  have hww := cp_ww_lt_B0.trans_le hB
  exact xtCapAt_nonfix (xtSpec1 lvSys_topPkg) hl hww hfix hlΛ hname (lv_nonfix l hl hww hfix hlΛ)

/-- **Below `Λ⁺(lvSys)`, ENUM-REACH is the equation `Θ_λ(m_λ) = O(λ)`.** -/
theorem lv_iff {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < xtB1 lvSys) :
    (CdUpper S l ∧ CdLower S l ↔ cdTheta S l (cdCode S l) = xtOrec lvSys l) :=
  xtExact_iff (xtSpec1 lvSys_topPkg) hl hlB

/-- **The offset at an isolated fixed point below `Λ⁺(lvSys)`**: `O(F) = F`. -/
theorem lv_iso {F : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hFB : F < xtB1 lvSys)
    (hiso : CpIso F) : xtOrec lvSys F = F :=
  xtIso hF hfix (hFB.trans (xtB1_lt_Om1 lvSys_topPkg)) hiso

/-- **ENUM-REACH at an isolated fixed point of the range below `Λ⁺(lvSys)` reduces to the code.** -/
theorem lv_fix_code {F : Ordinal.{0}} (hr : CdRange S F) (hfix : upsilon F = F) (hFB : F < xtB1 lvSys)
    (hiso : CpIso F) : (F ≤ cdCode S F → CdUpper S F) ∧ (cdCode S F ≤ Om1 → CdLower S F) :=
  xtFix_code (xtSpec1 lvSys_topPkg) hr.1 hfix hFB (lv_iso hr.1 hfix hFB hiso) (cp_name_L hr.2.2.1)

/-- **The hypotheses of `lvRoad3` from those of `luRoad3`.** -/
theorem lv_of_lu (hU : ∀ l, CdRange S l → xtB1 luSys ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 luSys ≤ l → CdLower S l)
    (hT : ∀ l, CdRange S l → l < xtB1 luSys → upsilon l = l → cdTheta S l (cdCode S l) = xtOrec luSys l) :
    (∀ l, CdRange S l → xtB1 lvSys ≤ l → CdUpper S l) ∧ (∀ l, CdRange S l → xtB1 lvSys ≤ l → CdLower S l) ∧
      (∀ l, CdRange S l → l < xtB1 lvSys → upsilon l = l → cdTheta S l (cdCode S l) = xtOrec lvSys l) := by
  have hle : xtB1 luSys ≤ xtB1 lvSys := (lvLam_gt.trans lv_lamLtB1).le
  refine ⟨fun l hr h => hU l hr (hle.trans h), fun l hr h => hL l hr (hle.trans h), fun l hr hlB hfix => ?_⟩
  rcases lt_or_ge l (xtB1 luSys) with h | h
  · rw [lv_eqLu hr.1 h]; exact hT l hr h hfix
  · exact (lv_iff hr.1 hlB).1 ⟨hU l hr h, hL l hr h⟩

/-- **The road with UPPER and LOWER asked only at `λ ≥ Λ⁺(lvSys)`**, `Θ_F(m_F) = O(F)` at the fixed points of the
range below `Λ⁺(lvSys)`, the cap of the values outside `Λ⁺(lvSys)`, (CL), EQ, TCrest, (EMB₂). -/
theorem lvRoad3 (hU : ∀ l, CdRange S l → xtB1 lvSys ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 lvSys ≤ l → CdLower S l)
    (hT : ∀ l, CdRange S l → l < xtB1 lvSys → upsilon l = l → cdTheta S l (cdCode S l) = xtOrec lvSys l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 lvSys) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad3 (xtSpec1 lvSys_topPkg) lv_nonfix hU hL hT hV hC hEQ hrest hB2

/-- **The road with UPPER, LOWER and the cap of the values asked only outside `Λ⁺(lvSys)`.** -/
theorem lvRoad (hU : ∀ l, CdRange S l → XtOut (xtB1 lvSys) l → CdUpper S l)
    (hL : ∀ l, CdRange S l → XtOut (xtB1 lvSys) l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 lvSys) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad (xtSpec1 lvSys_topPkg) lv_nonfix hU hL hV hC hEQ hrest hB2

/-- **The road with the caps asked only outside `Λ⁺(lvSys)`**: CAP-0, CAP-1 outside, (CL), (TC), (EMB₂). -/
theorem lvRoad_cap
    (h0 : ∀ l, IsRestartIdx l → cdB0 ≤ l → upsilon l < cdMstar S → XtOut (xtB1 lvSys) l → CdCapAt S l)
    (h1 : ∀ l, IsRestartIdx l → cdB0 ≤ l → cdMstar S ≤ upsilon l → upsilon l < Nc.ncL S ω →
      cdCode S l < Nc.ncPp S → XtOut (xtB1 lvSys) l → CdCapAt S l) (hC : CdCL S) (hTC : CdTC S)
    (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad_cap (xtSpec1 lvSys_topPkg) lv_nonfix h0 h1 hC hTC hB2

end Googology.Trans.PoR.InaccPsi.R2

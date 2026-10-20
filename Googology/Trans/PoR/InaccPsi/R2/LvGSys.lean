import Googology.Trans.PoR.InaccPsi.R2.LvGJ

/-!
# The staged tower of term systems: BLK^O, the exact reaches and ENUM-REACH up to every `Λ⁺(lvgSys n)`

`lvgSys n` is the term system of the terms of `LvGT` of stage `≤ n`, top `gT n x` (`gT 0 x = ε_{x+1}`, `gT (n+1) x =
ϑˣ(Ω₁·gT n x)`).  Its fields are Lemma IMG (`LvGK.pkgLvG`), Lemma RS (`rsStep_LvG`), the comparison (`LvGT.uni_le`,
from Lemma EXACT `LvGT.pi`), the representation (`lvg_rep`) and `lvg_small`; the top has the IMG package
`LvGK.lvgTopPkg` (the top is the value of the term `gTm n` of the next stage).  Then, for every `n`, from the generic
theorems of `R2.XtGen`, `R2.LyCmp`, `R2.XtEnum`:

* `lvg_topIn` (the top `gT n` of `lvgSys n` is the term `gTm n` of `lvgSys (n+1)`), **`lvgLam_gt`: `Λ⁺(lvgSys n) <
  Λ(lvgSys (n+1)) < Λ⁺(lvgSys (n+1))`**, `lvg_eq` (**`O_{n+1} = O_n` below `Λ⁺(lvgSys n)`**), `lvg_atB1`
  (**`O_{n+1}(Λ⁺(lvgSys n)) = gT n ρ + 1`**), `lvgReach1`; `lvg_topIn_lw`, `lvgLam_gt_lw` (`Λ⁺(lvwSys) < Λ(lvgSys 1)`);
* `lvg_reach` (**`lh(ρ_λ) = δ_λ + O(λ)` for every restart `λ < Λ⁺(lvgSys n)`**), `lvg_reachLam`, `lvg_reachTerm`,
  `lvg_blk` (**Theorem BLK^O below `υ_{Λ⁺(lvgSys n)}`**);
* `lvg_init` (**ENUM-REACH at every non-fixed restart below `Λ⁺(lvgSys n)`**), `lvg_capV` (**CapV there**), `lvg_capAt`,
  `lvg_iff`, `lvg_iso`, `lvg_fix_code`, `lvg_of`, `lvgRoad3`, `lvgRoad`, `lvgRoad_cap`.

No new axiom beyond `R2.CitedLu` and `R2.CitedLv`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Lt Lu

/-- **Lemma RS with the target `t(ρ)`** for `LvGT`. -/
theorem rs_rstLvG {r : Ordinal.{0}}
    (h : RstK (upsilon r) (upsilon (r + ω)) (upsilon (r + ω + 1)))
    {s : LvGT} (hs : LvGT.CBt s (upsilon r)) (hρs : upsilon r ≤ LvGT.val s (upsilon r))
    (htarget : ∀ κ' < upsilon r, ∃ μ, κ' < upsilon μ ∧ upsilon (μ + ω + 1) < upsilon r ∧
      RstK (upsilon μ) (upsilon (μ + ω)) (upsilon (μ + ω + 1)) ∧
      ∀ g, upsilon μ ≤ g → g ≤ upsilon (μ + ω + 1) + LvGT.val s (upsilon μ) → le1 (upsilon μ) g) :
    le1 (upsilon r) (upsilon (r + ω + 1) + LvGT.val s (upsilon r) + 1) := by
  classical
  have hnx := upsilon_isNext r
  have hCs : ∀ σ, (∀ c ∈ (LvGT.cs s).toFinset, c < σ) → LvGT.CBt s σ := fun σ hσ =>
    LvGT.cbt_iff hs (fun c hc => hσ c (List.mem_toFinset.2 hc))
  refine rs_rstF (T := LvGT.val s) (C := (LvGT.cs s).toFinset) h
    (fun c hc => LvGT.cbt_cst hs c (List.mem_toFinset.1 hc)) hρs
    (LvGT.lvg_lt_ups h.ρE h.ρ1 hs hnx.1 hnx.2.1) ?_ ?_ htarget
  · intro σ hσ hB hCσ _
    exact (LvGT.pi hσ h.ρU hB s (hCs σ hCσ)).2
  · intro σ hσE hσρ _ hCσ
    exact LvGT.lvg_lt_next hσE (hσρ.trans h.ρ1) (hCs σ hCσ) hσρ h.ρU.2

/-- **Lemma RS for every term of `LvGT`** with constants below `ρ_λ`. -/
theorem rsStep_LvG {l : Ordinal.{0}} {s : LvGT} (hs : LvGT.CBt s (upsilon l)) :
    RsStep l (LvGT.val s) := by
  intro R htg
  by_cases hρs : upsilon l ≤ LvGT.val s (upsilon l)
  · exact rs_rstLvG R hs hρs htg
  · have hn : LvGT.noB s := by
      by_contra hn
      exact hρs (LvGT.le_of_not_noB R.ρE R.ρ1 s hs hn)
    set c := LvGT.val s (upsilon l) with hc
    have e : LvGT.val s = OT.ev (OT.k c) := funext (fun y => by
      rw [OT.ev_k, hc, LvGT.noB_val s hn y])
    have hcb : OT.CB (OT.k c) (upsilon l) := not_le.1 hρs
    rw [e] at htg
    have h := rs_rstT R hcb htg
    rwa [OT.ev_k] at h


theorem lvg_top_lt_next_ups (n : ℕ) {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) :
    gT n (upsilon l) < upsilon (l + ω + 1) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρU := upsPt_upsilon hl0
  have h1 : l < l + ω := lt_add_of_pos_right l omega0_pos
  have hτU := upsPt_upsilon (hl0.trans h1)
  exact (LvGT.lvg_top_lt_next (upsPt_inE hρU) (ups_lt_Om1 l hl1) n (upsilon_normal.strictMono h1) hτU.2).trans
    (upsilon_normal.strictMono (lt_add_one _))

/-- **The term system of stage `n`** (top `gT n`). -/
noncomputable def lvgSys (n : ℕ) : XtSys where
  Tm := LvGT
  val := LvGT.val
  CB := fun t x => LvGT.CBt t x ∧ LvGT.stage t ≤ n
  cs := LvGT.cs
  cst := LvGT.cst
  top := gT n
  cb_cst := fun _ _ h => LvGT.cbt_cst h.1
  cb_iff := fun _ _ _ h hc => ⟨LvGT.cbt_iff h.1 hc, h.2⟩
  val_cst := fun _ _ => rfl
  cb_cstI := fun _ _ h => ⟨h, Nat.zero_le n⟩
  lt_top := fun l hl hl1 t hCB =>
    (LvGT.lvg_T (ups_inE hl) (ups_lt_Om1 l hl1) t hCB.1).2.trans_le (gT_mono (ups_inE hl) (ups_lt_Om1 l hl1) hCB.2)
  one_le_top := fun l hl hl1 =>
    one_le_iff_pos.2 (gT_facts (ups_inE hl) (ups_lt_Om1 l hl1) n).2.2.2.pos
  rep := fun l hl hl1 v hv => by
    obtain ⟨t, h1, h2, h3⟩ := lvg_rep (ups_inE hl) (ups_lt_Om1 l hl1) n v hv
    exact ⟨t, ⟨h1, h2⟩, h3⟩
  top_lt := fun l hl hl1 => lvg_top_lt_next_ups n hl hl1
  pkg := fun _ _ _ _ hCB h1 R => LvGK.pkgLvG R hCB.1 h1
  rs := fun _ _ _ _ hCB => rsStep_LvG hCB.1
  uni_le := fun _ _ hσ hρ hB _ _ ht hu => LvGT.uni_le hσ hρ hB ht.1 hu.1
  small := fun t => by
    rcases lvg_small t with h | h
    · exact Or.inl h
    · exact Or.inr fun x hx hx1 hc => h x hx hx1 hc.1

theorem lvgSys_top (n : ℕ) (x : Ordinal.{0}) : (lvgSys n).top x = gT n x := rfl

/-- **The top `gT n` of `lvgSys n` has an IMG package.** -/
theorem lvgSys_topPkg (n : ℕ) : XtTopPkg (lvgSys n) := fun _ _ _ R => LvGK.lvgTopPkg R n

theorem lvg_lamLtB1 (n : ℕ) : xtLam (lvgSys n) < xtB1 (lvgSys n) := lyLamLtB1 (lvgSys_topPkg n)

/-! ## Past `Λ⁺(lvgSys n)` -/

/-- **The top of `lvgSys n` inside `lvgSys (n+1)`**: `gT n = gTm n`, and `gT n + 1 < gT (n+1)`. -/
theorem lvg_topIn (n : ℕ) : LyTopIn (lvgSys (n + 1)) (lvgSys n) := by
  refine ⟨gTm n, fun x hx hx1 => ⟨⟨(gTm_val (upsPt_inE hx) hx1 n).1, by rw [gTm_stage]⟩,
    (gTm_val (upsPt_inE hx) hx1 n).2⟩, fun l hl hl1 => ?_⟩
  have hρE := ups_inE hl
  have hρ1 := ups_lt_Om1 l hl1
  have hE := (gT_facts hρE hρ1 (n + 1)).2.2.2
  rw [lvgSys_top, lvgSys_top]
  exact (inE_indec hE).add_lt (gT_lt_succ hρE hρ1 n) (lu_one_lt_E hE)

/-- **`Λ⁺(lvgSys n) < Λ(lvgSys (n+1))`.** -/
theorem lvgLam_gt (n : ℕ) : xtB1 (lvgSys n) < xtLam (lvgSys (n + 1)) := lyLamGt (lvgSys_topPkg n) (lvg_topIn n)

/-- **`O_{n+1} = O_n` below `Λ⁺(lvgSys n)`.** -/
theorem lvg_eq (n : ℕ) {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h : μ < xtB1 (lvgSys n)) :
    xtOrec (lvgSys (n + 1)) μ = xtOrec (lvgSys n) μ :=
  lyEq (lvgSys_topPkg n) (lvg_topIn n) hμ h

/-- **`O_{n+1}(Λ⁺(lvgSys n)) = gT n ρ + 1`.** -/
theorem lvg_atB1 (n : ℕ) : xtOrec (lvgSys (n + 1)) (xtB1 (lvgSys n)) = gT n (upsilon (xtB1 (lvgSys n))) + 1 := by
  rw [lyAtB1 (lvgSys_topPkg n) (lvg_topIn n), lvgSys_top]

/-- **The exact reach at `Λ⁺(lvgSys n)`**: `lh(ρ) = δ + gT n ρ + 1`. -/
theorem lvgReach1 (n : ℕ) :
    IsReach R2C (upsilon (xtB1 (lvgSys n)))
      (upsilon (xtB1 (lvgSys n) + ω + 1) + (gT n (upsilon (xtB1 (lvgSys n))) + 1)) := by
  have := lyReachB1 (lvgSys_topPkg (n + 1)) (lvgSys_topPkg n) (lvg_topIn n)
  rwa [lvgSys_top] at this

/-- **The order of the frontiers**: `Λ⁺(lvgSys n) < Λ(lvgSys (n+1)) < Λ⁺(lvgSys (n+1)) < Ω₁`. -/
theorem lvg_order (n : ℕ) : xtB1 (lvgSys n) < xtLam (lvgSys (n + 1)) ∧
    xtLam (lvgSys (n + 1)) < xtB1 (lvgSys (n + 1)) ∧ xtB1 (lvgSys (n + 1)) < Om1 :=
  ⟨lvgLam_gt n, lvg_lamLtB1 (n + 1), xtB1_lt_Om1 (lvgSys_topPkg (n + 1))⟩

/-- **The top of `lvwSys` inside `lvgSys 1`**: `ϑˣ(Ω₁·(x·ω)) = tl (ω^{x+1}) 0`. -/
theorem lvg_topIn_lw : LyTopIn (lvgSys 1) lvwSys := by
  have hL : ∀ x : Ordinal.{0}, InE x → LvGT.val (.pw (.sm .bs (.cst 1))) x = x * ω := fun x hx => by
    simp only [LvGT.val_pw, LvGT.val_sm, LvGT.val_bs, LvGT.val_cst]
    rw [opow_add, opow_one, show ω ^ x = x from hx]
  have hcb : ∀ x : Ordinal.{0}, InE x → LvGT.CBt (.tl (.pw (.sm .bs (.cst 1))) (.cst 0)) x := fun x hx =>
    ⟨fun h => h.1, ⟨trivial, lu_one_lt_E hx⟩, hx.pos⟩
  refine ⟨LvGT.tl (.pw (.sm .bs (.cst 1))) (.cst 0), fun x hx _ => ⟨⟨hcb x (upsPt_inE hx), by decide⟩, ?_⟩,
    fun l hl hl1 => ?_⟩
  · show vt x (Om1 * LvGT.val (.pw (.sm .bs (.cst 1))) x + 0) = lvwSys.top x
    rw [add_zero, lvwSys_top, hL x (upsPt_inE hx)]
  · have hρE := ups_inE hl
    have hρ1 := ups_lt_Om1 l hl1
    have hTE := (gT_facts hρE hρ1 1).2.2.2
    rw [lvwSys_top, lvgSys_top]
    have hlt := (LvGT.lvg_T hρE hρ1 _ (hcb _ hρE)).2
    simp only [LvGT.val_tl, LvGT.val_cst, add_zero, hL _ hρE] at hlt
    exact (inE_indec hTE).add_lt hlt (lu_one_lt_E hTE)

/-- **`Λ⁺(lvwSys) < Λ(lvgSys 1)`.** -/
theorem lvgLam_gt_lw : xtB1 lvwSys < xtLam (lvgSys 1) := lyLamGt lvwSys_topPkg lvg_topIn_lw

/-! ## BLK^O and the exact reaches up to `Λ⁺(lvgSys n)` -/

theorem lvg_nonfix (n : ℕ) : XtNonfix (xtOrec (lvgSys n)) (xtB1 (lvgSys n)) :=
  fun _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtB1_lt_Om1 (lvgSys_topPkg n)))

/-- **The exact reach of every restart below `Λ⁺(lvgSys n)`**: `lh(ρ_λ) = δ_λ + O(λ)`. -/
theorem lvg_reach (n : ℕ) {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < xtB1 (lvgSys n)) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec (lvgSys n) l) :=
  xtReach1 (lvgSys_topPkg n) hl hlB

/-- **The exact reach at the frontier `Λ(lvgSys n)`**: `lh(ρ) = δ + gT n ρ`. -/
theorem lvg_reachLam (n : ℕ) :
    IsReach R2C (upsilon (xtLam (lvgSys n)))
      (upsilon (xtLam (lvgSys n) + ω + 1) + gT n (upsilon (xtLam (lvgSys n)))) := by
  rw [← lvgSys_top n, ← xtOrec_Lam]
  exact xtReach1 (lvgSys_topPkg n) xtLam_ri (lvg_lamLtB1 n)

/-- **The reach at the frontier of every term `t` of `(lvgSys n)`** (constants below `ρ` at `Λ(lvgSys n)`, value `≥ 1`):
`lh(ρ) = δ + t(ρ)`. -/
theorem lvg_reachTerm (n : ℕ) {t : LvGT}
    (hCB : LvGT.CBt t (upsilon (xtLam (lvgSys n))) ∧ LvGT.stage t ≤ n)
    (h1 : 1 ≤ LvGT.val t (upsilon (xtLam (lvgSys n)))) :
    IsReach R2C (upsilon (xtLamT (lvgSys n) t))
      (upsilon (xtLamT (lvgSys n) t + ω + 1) + LvGT.val t (upsilon (xtLamT (lvgSys n) t))) :=
  xtReach_LamT (X := (lvgSys n)) hCB h1

/-- **Theorem BLK^O below `υ_{Λ⁺(lvgSys n)}`** in `R₂^C`. -/
theorem lvg_blk (n : ℕ) :
    (∀ c d, c < d → d < upsilon (xtB1 (lvgSys n)) → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 (lvgSys n) ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 (lvgSys n) →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec (lvgSys n) l)) ∧
    (∀ α < upsilon (xtB1 (lvgSys n)), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  xtBlk1 (lvgSys_topPkg n)

/-! ## ENUM-REACH and the caps -/

variable {S : InaccSeq.{0}}

/-- **UPPER and LOWER (ENUM-REACH) at every restart of the range below `Λ⁺(lvgSys n)` that is not a fixed point of
`υ`.** -/
theorem lvg_init (n : ℕ) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 (lvgSys n)) (hfix : l < upsilon l) :
    CdUpper S l ∧ CdLower S l :=
  xtInit (xtSpec1 (lvgSys_topPkg n)) (lvg_nonfix n) hr hl hfix

/-- **The cap of the values at every non-fixed restart of the range below `Λ⁺(lvgSys n)`.** -/
theorem lvg_capV (n : ℕ) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 (lvgSys n)) (hfix : l < upsilon l) :
    CdCapV S l := by
  have hww := cp_ww_lt_B0.trans_le hr.2.1
  exact xtCapV_nonfix (xtSpec1 (lvgSys_topPkg n)) hr.1 hww hfix hl (cp_name_L hr.2.2.1)
    ((lvg_nonfix n) l hr.1 hww hfix hl)

theorem lvg_capAt (n : ℕ) {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hB : cdB0 ≤ l) (hlΛ : l < xtB1 (lvgSys n))
    (hfix : l < upsilon l) (hname : upsilon l < Pv S η1) : CdCapAt S l := by
  have hww := cp_ww_lt_B0.trans_le hB
  exact xtCapAt_nonfix (xtSpec1 (lvgSys_topPkg n)) hl hww hfix hlΛ hname ((lvg_nonfix n) l hl hww hfix hlΛ)

/-- **Below `Λ⁺(lvgSys n)`, ENUM-REACH is the equation `Θ_λ(m_λ) = O(λ)`.** -/
theorem lvg_iff (n : ℕ) {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < xtB1 (lvgSys n)) :
    (CdUpper S l ∧ CdLower S l ↔ cdTheta S l (cdCode S l) = xtOrec (lvgSys n) l) :=
  xtExact_iff (xtSpec1 (lvgSys_topPkg n)) hl hlB

/-- **The offset at an isolated fixed point below `Λ⁺(lvgSys n)`**: `O(F) = F`. -/
theorem lvg_iso (n : ℕ) {F : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hFB : F < xtB1 (lvgSys n))
    (hiso : CpIso F) : xtOrec (lvgSys n) F = F :=
  xtIso hF hfix (hFB.trans (xtB1_lt_Om1 (lvgSys_topPkg n))) hiso

/-- **ENUM-REACH at an isolated fixed point of the range below `Λ⁺(lvgSys n)` reduces to the code.** -/
theorem lvg_fix_code (n : ℕ) {F : Ordinal.{0}} (hr : CdRange S F) (hfix : upsilon F = F) (hFB : F < xtB1 (lvgSys n))
    (hiso : CpIso F) : (F ≤ cdCode S F → CdUpper S F) ∧ (cdCode S F ≤ Om1 → CdLower S F) :=
  xtFix_code (xtSpec1 (lvgSys_topPkg n)) hr.1 hfix hFB (lvg_iso n hr.1 hfix hFB hiso) (cp_name_L hr.2.2.1)

/-- **The hypotheses of `lvgRoad3 (n+1)` from those of `lvgRoad3 n`.** -/
theorem lvg_of (n : ℕ) (hU : ∀ l, CdRange S l → xtB1 (lvgSys n) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 (lvgSys n) ≤ l → CdLower S l)
    (hT : ∀ l, CdRange S l → l < xtB1 (lvgSys n) → upsilon l = l →
      cdTheta S l (cdCode S l) = xtOrec (lvgSys n) l) :
    (∀ l, CdRange S l → xtB1 (lvgSys (n + 1)) ≤ l → CdUpper S l) ∧
      (∀ l, CdRange S l → xtB1 (lvgSys (n + 1)) ≤ l → CdLower S l) ∧
      (∀ l, CdRange S l → l < xtB1 (lvgSys (n + 1)) → upsilon l = l →
        cdTheta S l (cdCode S l) = xtOrec (lvgSys (n + 1)) l) := by
  have hle : xtB1 (lvgSys n) ≤ xtB1 (lvgSys (n + 1)) := ((lvgLam_gt n).trans (lvg_lamLtB1 (n + 1))).le
  refine ⟨fun l hr h => hU l hr (hle.trans h), fun l hr h => hL l hr (hle.trans h), fun l hr hlB hfix => ?_⟩
  rcases lt_or_ge l (xtB1 (lvgSys n)) with h | h
  · rw [lvg_eq n hr.1 h]; exact hT l hr h hfix
  · exact (lvg_iff (n + 1) hr.1 hlB).1 ⟨hU l hr h, hL l hr h⟩

/-- **The road with UPPER and LOWER asked only at `λ ≥ Λ⁺(lvgSys n)`**, `Θ_F(m_F) = O(F)` at the fixed points of the
range below `Λ⁺(lvgSys n)`, the cap of the values outside `Λ⁺(lvgSys n)`, (CL), EQ, TCrest, (EMB₂). -/
theorem lvgRoad3 (n : ℕ) (hU : ∀ l, CdRange S l → xtB1 (lvgSys n) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 (lvgSys n) ≤ l → CdLower S l)
    (hT : ∀ l, CdRange S l → l < xtB1 (lvgSys n) → upsilon l = l → cdTheta S l (cdCode S l) = xtOrec (lvgSys n) l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 (lvgSys n)) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad3 (xtSpec1 (lvgSys_topPkg n)) (lvg_nonfix n) hU hL hT hV hC hEQ hrest hB2

/-- **The road with UPPER, LOWER and the cap of the values asked only outside `Λ⁺(lvgSys n)`.** -/
theorem lvgRoad (n : ℕ) (hU : ∀ l, CdRange S l → XtOut (xtB1 (lvgSys n)) l → CdUpper S l)
    (hL : ∀ l, CdRange S l → XtOut (xtB1 (lvgSys n)) l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 (lvgSys n)) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad (xtSpec1 (lvgSys_topPkg n)) (lvg_nonfix n) hU hL hV hC hEQ hrest hB2

/-- **The road with the caps asked only outside `Λ⁺(lvgSys n)`**: CAP-0, CAP-1 outside, (CL), (TC), (EMB₂). -/
theorem lvgRoad_cap (n : ℕ)
    (h0 : ∀ l, IsRestartIdx l → cdB0 ≤ l → upsilon l < cdMstar S → XtOut (xtB1 (lvgSys n)) l → CdCapAt S l)
    (h1 : ∀ l, IsRestartIdx l → cdB0 ≤ l → cdMstar S ≤ upsilon l → upsilon l < Nc.ncL S ω →
      cdCode S l < Nc.ncPp S → XtOut (xtB1 (lvgSys n)) l → CdCapAt S l) (hC : CdCL S) (hTC : CdTC S)
    (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad_cap (xtSpec1 (lvgSys_topPkg n)) (lvg_nonfix n) h0 h1 hC hTC hB2

end Googology.Trans.PoR.InaccPsi.R2

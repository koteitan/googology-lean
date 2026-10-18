import Googology.Trans.PoR.InaccPsi.R2.LuI

/-!
# The term system of all constant levels: BLK^O, the exact reaches and ENUM-REACH up to `Λ⁺(luSys)`

`luSys` is the term system of `LuT` (constants, the base, `ϑˣ(Ω₁·β + t)` for every constant level `1 ≤ β < x`, sums,
`ω^t`), top `ϑˣ(Ω₁·x)` (`luTop`, the code `Ω₁·Ω₁`).  Its fields are Lemma IMG (`LuK.pkgLu`), Lemma RS (`rsStep_Lu`), the
comparison (`luUni_le`, from Lemma EXACT `lu_pi`) and the representation (`lu_rep`); the top has the IMG package
`LuK.luTopPkg`.  One system, uniform in the level `β`, in place of the per-level systems of the earlier rounds.  Then:

* `luSys_topPkg`; `lu_topIn_lnSw` (the top `ϑˣ(Ω₁·(ω+1))` of `lnSw` is the term `th (ω+1) 0`, and `ϑˣ(Ω₁·(ω+1)) + 1 <
  ϑˣ(Ω₁·x)`), **`luLam_gt`: `Λ⁺(lnSw) < Λ(luSys) < Λ⁺(luSys)`**, `lu_eqLn` (**`O = O_{lnSw}` below `Λ⁺(lnSw)`**),
  `lu_atB1Ln` (**`O(Λ⁺(lnSw)) = ϑᵖ(Ω₁·(ω+1)) + 1`**), `luReachLn1` (**the exact reach at `Λ⁺(lnSw)`: `lh(ρ) = δ +
  ϑᵖ(Ω₁·(ω+1)) + 1`**);
* `lu_reach` (**`lh(ρ_λ) = δ_λ + O(λ)` for every restart `λ < Λ⁺(luSys)`**), `lu_reachLam` (**the exact reach at the
  frontier `Λ(luSys)`: `lh(ρ) = δ + ϑᵖ(Ω₁·ρ)`**), `lu_reachTerm` (the reach at the frontier of every term), `lu_blk`
  (**Theorem BLK^O below `υ_{Λ⁺(luSys)}`**);
* `lu_init` (**UPPER and LOWER, i.e. ENUM-REACH, at every restart of the range below `Λ⁺(luSys)` that is not a fixed
  point of `υ`**), `lu_capV` (**CapV there**), `lu_capAt`, `lu_iff`, `lu_iso`, `lu_fix_code`, `lu_of_ln` (the
  hypotheses of `luRoad3` from those of `lnSwRoad3`), `luRoad3`, `luRoad`, `luRoad_cap` (the roads of `R2.XtEnum` with
  the rest asked only outside `Λ⁺(luSys)`).

No new axiom beyond `R2.CitedLu`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lu

open Ordinal Order Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Lt LuT

theorem lu_top_lt_next_ups {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) :
    luTop (upsilon l) < upsilon (l + ω + 1) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρU := upsPt_upsilon hl0
  have h1 : l < l + ω := lt_add_of_pos_right l omega0_pos
  have hτU := upsPt_upsilon (hl0.trans h1)
  exact (lu_top_lt_next (upsPt_inE hρU) (ups_lt_Om1 l hl1) (upsilon_normal.strictMono h1) hτU.2).trans
    (upsilon_normal.strictMono (lt_add_one _))

/-- **The term system of every constant level** (top `ϑˣ(Ω₁·x)`). -/
noncomputable def luSys : XtSys where
  Tm := LuT
  val := LuT.val
  CB := CBt
  cs := LuT.cs
  cst := LuT.cst
  top := luTop
  cb_cst := cbt_cst
  cb_iff := cbt_iff
  val_cst := fun _ _ => rfl
  cb_cstI := fun _ _ h => h
  lt_top := fun l hl hl1 t hCB => (lu_T (ups_inE hl) (ups_lt_Om1 l hl1) t hCB).2
  one_le_top := fun l hl hl1 => one_le_iff_pos.2 (luTop_facts (ups_inE hl) (ups_lt_Om1 l hl1)).2.2.2.1.pos
  rep := fun l hl hl1 v hv => lu_rep (ups_inE hl) (ups_lt_Om1 l hl1) v hv
  top_lt := fun l hl hl1 => lu_top_lt_next_ups hl hl1
  pkg := fun _ _ _ _ hCB h1 R => LuK.pkgLu R hCB h1
  rs := fun _ _ _ _ hCB => rsStep_Lu hCB
  uni_le := fun _ _ hσ hρ hB _ _ ht hu => luUni_le hσ hρ hB ht hu
  small := fun t => by
    by_cases h : noB t
    · exact Or.inl (lu_noB t h)
    · exact Or.inr (fun x hx hx1 hc => le_lu_of_not_noB hx hx1 t hc h)

theorem luSys_top (x : Ordinal.{0}) : luSys.top x = vt x (Om1 * x) := rfl

/-- **The top `ϑˣ(Ω₁·x)` of `luSys` has an IMG package.** -/
theorem luSys_topPkg : XtTopPkg luSys := fun _ _ _ R => LuK.luTopPkg R

theorem lu_lamLtB1 : xtLam luSys < xtB1 luSys := lyLamLtB1 luSys_topPkg

/-! ## Past `Λ⁺(lnSw)` -/

/-- **The top of `lnSw` inside `luSys`**: `ϑˣ(Ω₁·(ω+1)) = th (ω+1) 0`, and `ϑˣ(Ω₁·(ω+1)) + 1 < ϑˣ(Ω₁·x)`. -/
theorem lu_topIn_lnSw : LyTopIn luSys lnSw := by
  refine ⟨th (ω + 1) (cst 0), fun x hx hx1 => ⟨⟨le_self_add.trans' (one_lt_omega0.le), ?_, (upsPt_inE hx).pos⟩, ?_⟩,
    fun l hl hl1 => ?_⟩
  · exact lu_omega_one_lt_E (upsPt_inE hx)
  · show vt x (Om1 * (ω + 1) + 0) = lnSw.top x
    rw [add_zero, lnSw_top, ltP_eq (upsPt_inE hx) hx1]
  · have hρE := ups_inE hl
    have hρ1 := ups_lt_Om1 l hl1
    obtain ⟨hTT, hxT, hT1, hTE, -⟩ := luTop_facts hρE hρ1
    rw [lnSw_top, ltP_eq hρE hρ1, luSys_top]
    have h0T := lu_zero_T hρE hρ1
    have hlt : vt (upsilon l) (Om1 * (ω + 1) + 0) < vt (upsilon l) (Om1 * upsilon l) :=
      lu_th_lt_top hρE hρ1 (lu_omega_one_lt_E hρE) h0T (Ordinal.omega_pos 1) hTE.pos
    rw [add_zero] at hlt
    exact (inE_indec hTE).add_lt hlt (lu_one_lt_E hTE)

/-- **`Λ⁺(lnSw) < Λ(luSys)`.** -/
theorem luLam_gt : xtB1 lnSw < xtLam luSys := lyLamGt lnSw_topPkg lu_topIn_lnSw

/-- **`O = O_{lnSw}` below `Λ⁺(lnSw)`.** -/
theorem lu_eqLn {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h : μ < xtB1 lnSw) : xtOrec luSys μ = xtOrec lnSw μ :=
  lyEq lnSw_topPkg lu_topIn_lnSw hμ h

/-- **`O(Λ⁺(lnSw)) = ϑᵖ(Ω₁·(ω+1)) + 1`.** -/
theorem lu_atB1Ln : xtOrec luSys (xtB1 lnSw) = vt (upsilon (xtB1 lnSw)) (Om1 * (ω + 1)) + 1 := by
  rw [lyAtB1 lnSw_topPkg lu_topIn_lnSw, lnSw_top,
    ltP_eq (ups_inE (lyB1_ri lnSw_topPkg)) (ups_lt_Om1 _ (xtB1_lt_Om1 lnSw_topPkg))]

/-- **The exact reach at `Λ⁺(lnSw)`**: `lh(ρ) = δ + ϑᵖ(Ω₁·(ω+1)) + 1`. -/
theorem luReachLn1 :
    IsReach R2C (upsilon (xtB1 lnSw))
      (upsilon (xtB1 lnSw + ω + 1) + (vt (upsilon (xtB1 lnSw)) (Om1 * (ω + 1)) + 1)) := by
  have := lyReachB1 luSys_topPkg lnSw_topPkg lu_topIn_lnSw
  rwa [lnSw_top, ltP_eq (ups_inE (lyB1_ri lnSw_topPkg)) (ups_lt_Om1 _ (xtB1_lt_Om1 lnSw_topPkg))] at this

/-- **The order of the frontiers**: `Λ⁺(lnSw) < Λ(luSys) < Λ⁺(luSys) < Ω₁`. -/
theorem lu_order : xtB1 lnSw < xtLam luSys ∧ xtLam luSys < xtB1 luSys ∧ xtB1 luSys < Om1 :=
  ⟨luLam_gt, lu_lamLtB1, xtB1_lt_Om1 luSys_topPkg⟩

/-! ## BLK^O and the exact reaches up to `Λ⁺(luSys)` -/

theorem lu_nonfix : XtNonfix (xtOrec luSys) (xtB1 luSys) :=
  fun _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtB1_lt_Om1 luSys_topPkg))

/-- **The exact reach of every restart below `Λ⁺(luSys)`**: `lh(ρ_λ) = δ_λ + O(λ)`. -/
theorem lu_reach {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < xtB1 luSys) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec luSys l) :=
  xtReach1 luSys_topPkg hl hlB

/-- **The exact reach at the frontier `Λ(luSys)`**: `lh(ρ) = δ + ϑᵖ(Ω₁·ρ)`. -/
theorem lu_reachLam :
    IsReach R2C (upsilon (xtLam luSys))
      (upsilon (xtLam luSys + ω + 1) + vt (upsilon (xtLam luSys)) (Om1 * upsilon (xtLam luSys))) := by
  rw [← luSys_top, ← xtOrec_Lam]
  exact xtReach1 luSys_topPkg xtLam_ri lu_lamLtB1

/-- **The reach at the frontier of every term `t` of `luSys`** (constants below `ρ` at `Λ(luSys)`, value `≥ 1`):
`lh(ρ) = δ + t(ρ)`. -/
theorem lu_reachTerm {t : LuT} (hCB : CBt t (upsilon (xtLam luSys))) (h1 : 1 ≤ val t (upsilon (xtLam luSys))) :
    IsReach R2C (upsilon (xtLamT luSys t)) (upsilon (xtLamT luSys t + ω + 1) + val t (upsilon (xtLamT luSys t))) :=
  xtReach_LamT (X := luSys) hCB h1

/-- **Theorem BLK^O below `υ_{Λ⁺(luSys)}`** in `R₂^C`. -/
theorem lu_blk :
    (∀ c d, c < d → d < upsilon (xtB1 luSys) → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 luSys ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 luSys →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec luSys l)) ∧
    (∀ α < upsilon (xtB1 luSys), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  xtBlk1 luSys_topPkg

/-! ## ENUM-REACH and the caps -/

variable {S : InaccSeq.{0}}

/-- **UPPER and LOWER (ENUM-REACH) at every restart of the range below `Λ⁺(luSys)` that is not a fixed point of
`υ`.** -/
theorem lu_init {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 luSys) (hfix : l < upsilon l) :
    CdUpper S l ∧ CdLower S l :=
  xtInit (xtSpec1 luSys_topPkg) lu_nonfix hr hl hfix

/-- **The cap of the values at every non-fixed restart of the range below `Λ⁺(luSys)`.** -/
theorem lu_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 luSys) (hfix : l < upsilon l) :
    CdCapV S l := by
  have hww := cp_ww_lt_B0.trans_le hr.2.1
  exact xtCapV_nonfix (xtSpec1 luSys_topPkg) hr.1 hww hfix hl (cp_name_L hr.2.2.1)
    (lu_nonfix l hr.1 hww hfix hl)

theorem lu_capAt {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hB : cdB0 ≤ l) (hlΛ : l < xtB1 luSys)
    (hfix : l < upsilon l) (hname : upsilon l < Pv S η1) : CdCapAt S l := by
  have hww := cp_ww_lt_B0.trans_le hB
  exact xtCapAt_nonfix (xtSpec1 luSys_topPkg) hl hww hfix hlΛ hname (lu_nonfix l hl hww hfix hlΛ)

/-- **Below `Λ⁺(luSys)`, ENUM-REACH is the equation `Θ_λ(m_λ) = O(λ)`.** -/
theorem lu_iff {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < xtB1 luSys) :
    (CdUpper S l ∧ CdLower S l ↔ cdTheta S l (cdCode S l) = xtOrec luSys l) :=
  xtExact_iff (xtSpec1 luSys_topPkg) hl hlB

/-- **The offset at an isolated fixed point below `Λ⁺(luSys)`**: `O(F) = F`. -/
theorem lu_iso {F : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hFB : F < xtB1 luSys)
    (hiso : CpIso F) : xtOrec luSys F = F :=
  xtIso hF hfix (hFB.trans (xtB1_lt_Om1 luSys_topPkg)) hiso

/-- **ENUM-REACH at an isolated fixed point of the range below `Λ⁺(luSys)` reduces to the code.** -/
theorem lu_fix_code {F : Ordinal.{0}} (hr : CdRange S F) (hfix : upsilon F = F) (hFB : F < xtB1 luSys)
    (hiso : CpIso F) : (F ≤ cdCode S F → CdUpper S F) ∧ (cdCode S F ≤ Om1 → CdLower S F) :=
  xtFix_code (xtSpec1 luSys_topPkg) hr.1 hfix hFB (lu_iso hr.1 hfix hFB hiso) (cp_name_L hr.2.2.1)

/-- **The hypotheses of `luRoad3` from those of `lnSwRoad3`.** -/
theorem lu_of_ln (hU : ∀ l, CdRange S l → xtB1 lnSw ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 lnSw ≤ l → CdLower S l)
    (hT : ∀ l, CdRange S l → l < xtB1 lnSw → upsilon l = l → cdTheta S l (cdCode S l) = xtOrec lnSw l) :
    (∀ l, CdRange S l → xtB1 luSys ≤ l → CdUpper S l) ∧ (∀ l, CdRange S l → xtB1 luSys ≤ l → CdLower S l) ∧
      (∀ l, CdRange S l → l < xtB1 luSys → upsilon l = l → cdTheta S l (cdCode S l) = xtOrec luSys l) := by
  have hle : xtB1 lnSw ≤ xtB1 luSys := (luLam_gt.trans lu_lamLtB1).le
  refine ⟨fun l hr h => hU l hr (hle.trans h), fun l hr h => hL l hr (hle.trans h), fun l hr hlB hfix => ?_⟩
  rcases lt_or_ge l (xtB1 lnSw) with h | h
  · rw [lu_eqLn hr.1 h]; exact hT l hr h hfix
  · exact (lu_iff hr.1 hlB).1 ⟨hU l hr h, hL l hr h⟩

/-- **The road with UPPER and LOWER asked only at `λ ≥ Λ⁺(luSys)`**, `Θ_F(m_F) = O(F)` at the fixed points of the
range below `Λ⁺(luSys)`, the cap of the values outside `Λ⁺(luSys)`, (CL), EQ, TCrest, (EMB₂). -/
theorem luRoad3 (hU : ∀ l, CdRange S l → xtB1 luSys ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 luSys ≤ l → CdLower S l)
    (hT : ∀ l, CdRange S l → l < xtB1 luSys → upsilon l = l → cdTheta S l (cdCode S l) = xtOrec luSys l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 luSys) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad3 (xtSpec1 luSys_topPkg) lu_nonfix hU hL hT hV hC hEQ hrest hB2

/-- **The road with UPPER, LOWER and the cap of the values asked only outside `Λ⁺(luSys)`.** -/
theorem luRoad (hU : ∀ l, CdRange S l → XtOut (xtB1 luSys) l → CdUpper S l)
    (hL : ∀ l, CdRange S l → XtOut (xtB1 luSys) l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 luSys) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad (xtSpec1 luSys_topPkg) lu_nonfix hU hL hV hC hEQ hrest hB2

/-- **The road with the caps asked only outside `Λ⁺(luSys)`**: CAP-0, CAP-1 outside, (CL), (TC), (EMB₂). -/
theorem luRoad_cap
    (h0 : ∀ l, IsRestartIdx l → cdB0 ≤ l → upsilon l < cdMstar S → XtOut (xtB1 luSys) l → CdCapAt S l)
    (h1 : ∀ l, IsRestartIdx l → cdB0 ≤ l → cdMstar S ≤ upsilon l → upsilon l < Nc.ncL S ω →
      cdCode S l < Nc.ncPp S → XtOut (xtB1 luSys) l → CdCapAt S l) (hC : CdCL S) (hTC : CdTC S)
    (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad_cap (xtSpec1 luSys_topPkg) lu_nonfix h0 h1 hC hTC hB2

end Googology.Trans.PoR.InaccPsi.R2.Lu

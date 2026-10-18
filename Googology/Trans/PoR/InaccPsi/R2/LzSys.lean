import Googology.Trans.PoR.InaccPsi.R2.LzTm

/-!
# The term system `lzZ` (top `e_x(x) = ϑˣ(Ω₁ + B(x) + x)`) with `ε_{B(x)+1}` as a term: the exact reach at
`Λ⁺(lyEB)`, BLK^O, the reaches, ENUM-REACH and the road below `Λ⁺(lzZ)`

`lzZ`: the terms of `R2.LzTm` (terms over `B` below `ε_{B(x)+1}`, the atoms `e_c(x) = ε_{B(x)+1+c}`, sums, powers), top
`e_x(x)`.  Its fields: Lemma IMG (`lzPkg`, from `lzt_img`), Lemma RS (`lzRs`, `rs_rstF` with EXACT, or `rs_rstT` for a
constant term), the comparison (from EXACT `lzt_pi`), the representation (`lzt_rep`); the top has an IMG package
(`lzZ_topPkg`, from `lzE_imgTop`).  `lzZ` contains the top `ε_{B(x)+1} = e_0(x)` of `lyEB` (`R2.LyEpR`) as the atom
`ep 0` (`lzZ_topIn_E`).  Then:

* `lzE_lt_Lam` (**`Λ⁺(lyEB) < Λ(lzZ)`**), `lzZ_eqE` (`O_Z = O_E` below `Λ⁺(lyEB)`), `lzZ_atB1E`
  (**`O_Z(Λ⁺(lyEB)) = ε_{B(ρ)+1} + 1`**), `lzReachE1` (**the exact reach at `Λ⁺(lyEB)`:
  `lh(ρ) = δ + ε_{B(ρ)+1} + 1`**);
* `lzZ_reach` (**`lh(ρ_λ) = δ_λ + O_Z(λ)` at every restart `λ < Λ⁺(lzZ)`**), `lzZ_reachLam` (**`lh(ρ) = δ + e_ρ(ρ)`
  at `Λ(lzZ)`**), `lzZ_reachT` (**`lh(ρ) = δ + e_c(ρ)` at the frontier of the atom `ep c`**), `lzZ_blk`
  (**BLK^O below `υ_{Λ⁺(lzZ)}`**), `lzZ_nuC` (`υ_{Λ⁺(lzZ)} ≤ ρ_L < ν_C`);
* `lzZ_init` (**UPPER and LOWER at every non-fixed restart of the range below `Λ⁺(lzZ)`**), `lzZ_capV`, `lzZ_capAt`,
  `lzZ_iff`, `lzZ_iso`, `lzZ_fix_code`, `lzZ_of_cp`, `lzRoad3`, `lzRoad`, `lzRoad_cap` (the roads of `R2.XtEnum` with the
  rest asked only outside `Λ⁺(lzZ)`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lz

open Ordinal Order Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Nm LzTm

/-! ## Lemma IMG and Lemma RS for every term -/

/-- **Lemma IMG for the terms of `LzTm`** (the package). -/
theorem lzPkg {l : Ordinal.{0}} (t : LzTm) (hCB : CBt t (upsilon l))
    (h1 : 1 ≤ val t (upsilon l)) (R : RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1))) :
    ImgPkg (upsilon l) (upsilon (l + ω + 1)) (val t) := by
  classical
  have hρE := R.ρE
  have hρ1 := R.ρ1
  have htop := lzt_lt_top hρE hρ1 t hCB
  obtain ⟨W, Z, t', I⟩ := lzt_img R (val t (upsilon l)) htop
  have hwc : WZ (upsilon l) (upsilon (l + ω + 1)) ∅ (cs t).toFinset :=
    ⟨by simp, fun z hz => cbt_cst t _ hCB z (List.mem_toFinset.1 hz), by simp⟩
  have hw := I.1.union hwc
  rw [Finset.union_empty] at hw
  refine ⟨h1, htop.trans (LzK.lzE_lt_δ R le_rfl), W, Z ∪ (cs t).toFinset, hw, ?_, fun A f hW hZ C => ?_⟩
  · rcases Finset.mem_union.1 I.2.2.2.2.1 with h' | h'
    · exact Finset.mem_union_left _ h'
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ h')
  have hZ1 : ↑Z ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
  have htA : ∀ c ∈ cs t, c ∈ A := fun c hc => hZ (by simp [hc])
  have ht'A : ∀ c ∈ cs t', c ∈ A := fun c hc => hZ1 (Finset.mem_coe.2 (I.2.2.1 c hc))
  have heq := lzt_val_fρ R C hCB I.2.1 htA ht'A I.2.2.2.1.symm
  rw [heq]
  exact I.2.2.2.2.2 A f hW hZ1 C

/-- **Lemma RS for the terms of `LzTm`.** -/
theorem lzRs {l : Ordinal.{0}} (t : LzTm) (hCB : CBt t (upsilon l)) :
    RsStep l (val t) := by
  classical
  intro R htg
  have hρE := R.ρE
  have hρ1 := R.ρ1
  by_cases hρs : upsilon l ≤ val t (upsilon l)
  · have hnx := upsilon_isNext l
    have hCs : ∀ σ, (∀ c ∈ (cs t).toFinset, c < σ) → CBt t σ := fun σ hσ =>
      cbt_iff t _ σ hCB (fun c hc => hσ c (List.mem_toFinset.2 hc))
    refine rs_rstF (T := val t) (C := (cs t).toFinset) R
      (fun c hc => cbt_cst t _ hCB c (List.mem_toFinset.1 hc)) hρs ?_ ?_ ?_ htg
    · exact (lzt_lt_top hρE hρ1 t hCB).trans (lzTop_lt_ups hρE hρ1 hnx.1 hnx.2.1)
    · intro σ hσ hB hCσ _
      exact (lzt_pi hσ R.ρU hB t (hCs σ hCσ)).2
    · intro σ hσE hσρ _ hCσ
      have hσ1 := hσρ.trans hρ1
      exact (lzt_lt_top hσE hσ1 t (hCs σ hCσ)).trans (lzTop_lt_ups hσE hσ1 hσρ R.ρU)
  · have hC : LzC t := by
      by_contra hn
      exact hρs (lzC_ge hρE hρ1 t hCB hn)
    set c := val t (upsilon l) with hc
    have e : val t = OT.ev (OT.k c) := funext (fun y => by rw [OT.ev_k, hc, lzC_const t hC y])
    have hcb : OT.CB (OT.k c) (upsilon l) := not_le.1 hρs
    rw [e] at htg
    have := rs_rstT R hcb htg
    rwa [OT.ev_k] at this

/-! ## The term system -/

theorem lzTop_lt_next {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) :
    lzE (upsilon l) (upsilon l) < upsilon (l + ω + 1) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have h1 : l < l + ω := lt_add_of_pos_right l omega0_pos
  exact (lzTop_lt_ups (ups_inE hl) (ups_lt_Om1 l hl1) (upsilon_normal.strictMono h1)
    (upsPt_upsilon (hl0.trans h1))).trans (upsilon_normal.strictMono (lt_add_one _))

/-- **The term system `lzZ`**: the terms of `LzTm`, top `e_x(x) = ϑˣ(Ω₁ + B(x) + x)`. -/
noncomputable def lzZ : XtSys where
  Tm := LzTm
  val := LzTm.val
  CB := CBt
  cs := LzTm.cs
  cst := fun c => ly (LyTm.vz (VzTm.cst c))
  top := fun x => lzE x x
  cb_cst := cbt_cst
  cb_iff := cbt_iff
  val_cst := fun _ _ => rfl
  cb_cstI := fun _ _ h => h
  lt_top := fun l hl hl1 t hCB => lzt_lt_top (ups_inE hl) (ups_lt_Om1 l hl1) t hCB
  one_le_top := fun l hl hl1 =>
    one_le_iff_pos.2 (lzE_facts (ups_inE hl) (ups_lt_Om1 l hl1) le_rfl).2.2.2.2.2.1.pos
  rep := fun l hl hl1 v hv => lzt_rep (ups_inE hl) (ups_lt_Om1 l hl1) v hv
  top_lt := fun _ hl hl1 => lzTop_lt_next hl hl1
  pkg := fun _ _ _ t hCB h1 R => lzPkg t hCB h1 R
  rs := fun _ _ _ t hCB => lzRs t hCB
  uni_le := fun _ _ hσ hρ hB t u ht hu =>
    xt_uni_of_exact hB (lzt_pi hσ hρ hB t ht) (lzt_pi hσ hρ hB u hu)
  small := lzt_small

theorem lzZ_top (x : Ordinal.{0}) : lzZ.top x = lzE x x := rfl

/-- **The top `e_ρ(ρ)` has an IMG package.** -/
theorem lzZ_topPkg : XtTopPkg lzZ := fun l hl hl1 R => by
  obtain ⟨W, Z, hw, hTW, hI⟩ := LzK.lzE_imgTop R
  have hρE := R.ρE
  have hρ1 := R.ρ1
  exact ⟨one_le_iff_pos.2 (lzE_facts hρE hρ1 le_rfl).2.2.2.2.2.1.pos, LzK.lzE_lt_δ R le_rfl, W, Z, hw,
    Finset.mem_union_left _ hTW, fun A f hW hZ C => hI A f hW hZ C⟩

/-- **`lzZ` contains the top `ε_{B(x)+1}` of `lyEB` as the atom `e_0`.** -/
theorem lzZ_topIn_E : LyTopIn lzZ lyEB := by
  refine ⟨ep 0, fun x hx hx1 => ⟨show (0 : Ordinal.{0}) < x from hx.1, ?_⟩, fun l hl hl1 => ?_⟩
  · show lzE x 0 = eN (VzB x)
    exact lzE_zero (upsPt_inE hx) hx1
  · have hρE := ups_inE hl
    have hρ1 := ups_lt_Om1 l hl1
    have heE := (lzE_facts hρE hρ1 le_rfl).2.2.2.2.2.1
    rw [lyEB_top]
    exact (inE_indec heE).add_lt (lz_e0_lt_top hρE hρ1) (one_lt_omega0.trans (omega0_lt_inE heE))

/-- The atom `e_c` as a term of `lzZ`. -/
def lzAt (c : Ordinal.{0}) : lzZ.Tm := ep c

theorem lzAt_val (c x : Ordinal.{0}) : lzZ.val (lzAt c) x = lzE x c := rfl

/-! ## The exact reach at `Λ⁺(lyEB)` -/

/-- **`Λ⁺(lyEB) < Λ(lzZ)`.** -/
theorem lzE_lt_Lam : xtB1 lyEB < xtLam lzZ := lyLamGt lyEB_topPkg lzZ_topIn_E

/-- **`O_Z = O_E` below `Λ⁺(lyEB)`.** -/
theorem lzZ_eqE {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h : μ < xtB1 lyEB) : xtOrec lzZ μ = xtOrec lyEB μ :=
  lyEq lyEB_topPkg lzZ_topIn_E hμ h

/-- **`O_Z(Λ⁺(lyEB)) = ε_{B(ρ)+1} + 1`** for `ρ = ρ_{Λ⁺(lyEB)}`. -/
theorem lzZ_atB1E : xtOrec lzZ (xtB1 lyEB) = eN (VzB (upsilon (xtB1 lyEB))) + 1 :=
  lyAtB1 lyEB_topPkg lzZ_topIn_E

/-- **`Λ⁺(lyEB) < Λ⁺(lzZ)`.** -/
theorem lzE_lt_B1 : xtB1 lyEB < xtB1 lzZ := lyB1_lt lzZ_topPkg lyEB_topPkg lzZ_topIn_E

/-- **The exact reach at `Λ⁺(lyEB)`**: `lh(ρ) = δ + ε_{B(ρ)+1} + 1`. -/
theorem lzReachE1 :
    IsReach R2C (upsilon (xtB1 lyEB))
      (upsilon (xtB1 lyEB + ω + 1) + (eN (VzB (upsilon (xtB1 lyEB))) + 1)) :=
  lyReachB1 lzZ_topPkg lyEB_topPkg lzZ_topIn_E

/-! ## The reaches below `Λ⁺(lzZ)` -/

theorem lzZ_lam_lt : xtLam lzZ < xtB1 lzZ := lyLamLtB1 lzZ_topPkg

theorem lzZ_nonfix : XtNonfix (xtOrec lzZ) (xtB1 lzZ) :=
  fun _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtB1_lt_Om1 lzZ_topPkg))

/-- **The exact reach of every restart below `Λ⁺(lzZ)`**: `lh(ρ_λ) = δ_λ + O_Z(λ)`. -/
theorem lzZ_reach {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < xtB1 lzZ) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec lzZ l) :=
  xtReach1 lzZ_topPkg hl hlB

/-- **The reach at the frontier of `lzZ`**: `lh(ρ) = δ + e_ρ(ρ)`, `e_ρ(ρ) = ϑᵖ(Ω₁ + B(ρ) + ρ)`. -/
theorem lzZ_reachLam :
    IsReach R2C (upsilon (xtLam lzZ))
      (upsilon (xtLam lzZ + ω + 1) + lzE (upsilon (xtLam lzZ)) (upsilon (xtLam lzZ))) := by
  rw [← lzZ_top, ← xtOrec_Lam]
  exact xtReach1 lzZ_topPkg xtLam_ri lzZ_lam_lt

/-- **The reach at the frontier of every atom `e_c`** (`c` below `ρ_{Λ(lzZ)}`): `lh(ρ) = δ + e_c(ρ)`. -/
theorem lzZ_reachT {c : Ordinal.{0}} (hc : c < upsilon (xtLam lzZ)) :
    IsReach R2C (upsilon (xtLamT lzZ (lzAt c)))
      (upsilon (xtLamT lzZ (lzAt c) + ω + 1) + lzE (upsilon (xtLamT lzZ (lzAt c))) c) := by
  have hU := ups_ri (xtLam_ri (X := lzZ))
  have h1 : 1 ≤ lzZ.val (lzAt c) (upsilon (xtLam lzZ)) := by
    rw [lzAt_val]
    exact one_le_iff_pos.2 (lzE_facts (upsPt_inE hU) (ups_lt_Om1 _ xtLam_lt_Om1) hc.le).2.2.2.2.2.1.pos
  have := xtReach_LamT (X := lzZ) (t := lzAt c) hc h1
  rwa [lzAt_val] at this

/-- **Theorem BLK^O below `υ_{Λ⁺(lzZ)}`** in `R₂^C`. -/
theorem lzZ_blk :
    (∀ c d, c < d → d < upsilon (xtB1 lzZ) → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 lzZ ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 lzZ →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec lzZ l)) ∧
    (∀ α < upsilon (xtB1 lzZ), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  xtBlk1 lzZ_topPkg

/-- **Where the first non-standard pair lies**: `ρ_L <₂ ν_C = ρ_ξ` with `Λ⁺(lzZ) ≤ L < ξ`. -/
theorem lzZ_nuC : ∃ L ξ, IsRestartIdx L ∧ IsRestartIdx ξ ∧ xtB1 lzZ ≤ L ∧ L < ξ ∧
    upsilon (xtB1 lzZ) ≤ upsilon L ∧ upsilon L < nuC ∧ nuC = upsilon ξ ∧ le2 (upsilon L) nuC := by
  obtain ⟨L, ξ, hL, hξ, hLξ, he, h2, -, -, -⟩ := level2_restart
  have hLν : upsilon L < nuC := by rw [he]; exact upsilon_normal.strictMono hLξ
  have hle : xtB1 lzZ ≤ L := left_ge_of_spec (xtSpec1 lzZ_topPkg) hL hLν h2
  exact ⟨L, ξ, hL, hξ, hle, hLξ, upsilon_normal.strictMono.monotone hle, hLν, he, h2⟩

/-! ## ENUM-REACH and the road -/

variable {S : InaccSeq.{0}}

/-- **UPPER and LOWER at every restart of the range below `Λ⁺(lzZ)` that is not a fixed point of `υ`.** -/
theorem lzZ_init {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 lzZ) (hfix : l < upsilon l) :
    CdUpper S l ∧ CdLower S l :=
  xtInit (xtSpec1 lzZ_topPkg) lzZ_nonfix hr hl hfix

/-- **The cap of the values at every restart of the range below `Λ⁺(lzZ)` that is not a fixed point.** -/
theorem lzZ_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 lzZ) (hfix : l < upsilon l) :
    CdCapV S l := by
  have hww := cp_ww_lt_B0.trans_le hr.2.1
  exact xtCapV_nonfix (xtSpec1 lzZ_topPkg) hr.1 hww hfix hl (cp_name_L hr.2.2.1)
    (lzZ_nonfix l hr.1 hww hfix hl)

theorem lzZ_capAt {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hB : cdB0 ≤ l) (hlΛ : l < xtB1 lzZ)
    (hfix : l < upsilon l) (hname : upsilon l < Pv S η1) : CdCapAt S l := by
  have hww := cp_ww_lt_B0.trans_le hB
  exact xtCapAt_nonfix (xtSpec1 lzZ_topPkg) hl hww hfix hlΛ hname (lzZ_nonfix l hl hww hfix hlΛ)

/-- **Below `Λ⁺(lzZ)`, ENUM-REACH is the equation `Θ_λ(m_λ) = O_Z(λ)`.** -/
theorem lzZ_iff {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < xtB1 lzZ) :
    (CdUpper S l ∧ CdLower S l ↔ cdTheta S l (cdCode S l) = xtOrec lzZ l) :=
  xtExact_iff (xtSpec1 lzZ_topPkg) hl hlB

/-- **The offset at an isolated fixed point below `Λ⁺(lzZ)`**: `O_Z(F) = F`. -/
theorem lzZ_iso {F : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hFB : F < xtB1 lzZ)
    (hiso : CpIso F) : xtOrec lzZ F = F :=
  xtIso hF hfix (hFB.trans (xtB1_lt_Om1 lzZ_topPkg)) hiso

/-- **ENUM-REACH at an isolated fixed point of the range below `Λ⁺(lzZ)` reduces to the code**:
`F ≤ m_F ⇒ UPPER(F)` and `m_F ≤ Ω₁ ⇒ LOWER(F)`. -/
theorem lzZ_fix_code {F : Ordinal.{0}} (hr : CdRange S F) (hfix : upsilon F = F) (hFB : F < xtB1 lzZ)
    (hiso : CpIso F) : (F ≤ cdCode S F → CdUpper S F) ∧ (cdCode S F ≤ Om1 → CdLower S F) :=
  xtFix_code (xtSpec1 lzZ_topPkg) hr.1 hfix hFB (lzZ_iso hr.1 hfix hFB hiso) (cp_name_L hr.2.2.1)

/-- **The hypotheses of `lzRoad3` from those of `cpRoad3`.** -/
theorem lzZ_of_cp (hU : CpUPPERhigh S) (hL : CpLOWERhigh S) (hT : CpTHfix S) :
    (∀ l, CdRange S l → xtB1 lzZ ≤ l → CdUpper S l) ∧ (∀ l, CdRange S l → xtB1 lzZ ≤ l → CdLower S l) ∧
      (∀ l, CdRange S l → l < xtB1 lzZ → upsilon l = l → cdTheta S l (cdCode S l) = xtOrec lzZ l) := by
  obtain ⟨hU', hL', hT'⟩ := lyE_of_cp hU hL hT
  have hcp : Cp.cpB1 ≤ xtB1 lzZ := (lyB_cp_le.trans lyE_order.2.le).trans lzE_lt_B1.le
  refine ⟨fun l hr h => hU l hr (hcp.trans h), fun l hr h => hL l hr (hcp.trans h), fun l hr hlB hfix => ?_⟩
  rcases lt_or_ge l (xtB1 lyEB) with h | h
  · rw [lzZ_eqE hr.1 h]; exact hT' l hr h hfix
  · exact (lzZ_iff hr.1 hlB).1 ⟨hU' l hr h, hL' l hr h⟩

/-- **The road with UPPER and LOWER asked only at `λ ≥ Λ⁺(lzZ)`**, `Θ_F(m_F) = O_Z(F)` at the fixed points of the
range below `Λ⁺(lzZ)`, the cap of the values outside `Λ⁺(lzZ)`, (CL), EQ, TCrest, (EMB₂). -/
theorem lzRoad3 (hU : ∀ l, CdRange S l → xtB1 lzZ ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 lzZ ≤ l → CdLower S l)
    (hT : ∀ l, CdRange S l → l < xtB1 lzZ → upsilon l = l → cdTheta S l (cdCode S l) = xtOrec lzZ l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 lzZ) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad3 (xtSpec1 lzZ_topPkg) lzZ_nonfix hU hL hT hV hC hEQ hrest hB2

/-- **The road with UPPER, LOWER and the cap of the values asked only outside `Λ⁺(lzZ)`.** -/
theorem lzRoad (hU : ∀ l, CdRange S l → XtOut (xtB1 lzZ) l → CdUpper S l)
    (hL : ∀ l, CdRange S l → XtOut (xtB1 lzZ) l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 lzZ) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad (xtSpec1 lzZ_topPkg) lzZ_nonfix hU hL hV hC hEQ hrest hB2

/-- **The road with the caps asked only outside `Λ⁺(lzZ)`**: CAP-0, CAP-1 outside, (CL), (TC), (EMB₂). -/
theorem lzRoad_cap
    (h0 : ∀ l, IsRestartIdx l → cdB0 ≤ l → upsilon l < cdMstar S → XtOut (xtB1 lzZ) l → CdCapAt S l)
    (h1 : ∀ l, IsRestartIdx l → cdB0 ≤ l → cdMstar S ≤ upsilon l → upsilon l < Nc.ncL S ω →
      cdCode S l < Nc.ncPp S → XtOut (xtB1 lzZ) l → CdCapAt S l) (hC : CdCL S) (hTC : CdTC S)
    (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad_cap (xtSpec1 lzZ_topPkg) lzZ_nonfix h0 h1 hC hTC hB2

end Googology.Trans.PoR.InaccPsi.R2.Lz

import Googology.Trans.PoR.InaccPsi.R2.LpJ

/-!
# The stage systems over a base layer: BLK^O, the exact reaches and ENUM-REACH up to every `Λ⁺(lpSys B n)`

`lpSys B n` is the term system of the terms of `LpT B` (`R2.LpTm`) of stage `≤ n`, top `gP B n x` (`gP B 0 x =
E_K(x)`, `gP B (n+1) x = ϑˣ(Ω₁·gP B n x)`), for **every base package `B`** (a layer `K` with an `ε`-number top in
`Tˣ`).  Its fields are Lemma IMG (`LpGK.pkgLp`, with `LxRep`, `LxBase` of `K` at the restarts), Lemma RS (`rsStep_Lp`),
the comparison (`LpT.uni_le`, from Lemma EXACT `LpT.pi`), the representation (`lp_rep`) and `lp_small`; the top has
the IMG package `LpGK.lpTopPkg`.  Then, for every `n`, from the generic theorems of `R2.XtGen`, `R2.LyCmp`, `R2.XtEnum`:

* `lp_topIn`, **`lpLam_gt`: `Λ⁺(lpSys B n) < Λ(lpSys B (n+1))`**, `lp_eq`, `lp_atB1`, `lpReach1`, `lp_order`;
* `lp_topIn_K` (the top `E_K` of the base layer is the term `tp` of stage `1`), **`lpLam_gt_K`: `Λ⁺(K) <
  Λ(lpSys B 1)`**, `lp_eq_K` (`O_{lpSys B 1} = O_K` below `Λ⁺(K)`), `lp_atB1_K`, `lpB1_gt_K`;
* `lp_reach` (**`lh(ρ_λ) = δ_λ + O(λ)` for every restart `λ < Λ⁺(lpSys B n)`**), `lp_reachLam`, `lp_reachTerm`,
  `lp_blk` (**Theorem BLK^O below `υ_{Λ⁺(lpSys B n)}`**);
* `lp_init` (**ENUM-REACH at every non-fixed restart below `Λ⁺(lpSys B n)`**), `lp_capV` (**CapV there**), `lp_capAt`,
  `lp_iff`, `lp_iso`, `lp_fix_code`, `lp_of`, `lpRoad3`, `lpRoad`, `lpRoad_cap`.

No new axiom beyond the cited facts already in the repo.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Lp

open Ordinal Order Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Lt Lu Googology.Trans.PoR.InaccPsi.R2

variable {B : LpB}

/-- **Lemma RS with the target `t(ρ)`** for `LpT B`. -/
theorem rs_rstLp {r : Ordinal.{0}}
    (h : RstK (upsilon r) (upsilon (r + ω)) (upsilon (r + ω + 1)))
    {s : LpT B} (hs : LpT.CBt s (upsilon r)) (hρs : upsilon r ≤ LpT.val s (upsilon r))
    (htarget : ∀ κ' < upsilon r, ∃ μ, κ' < upsilon μ ∧ upsilon (μ + ω + 1) < upsilon r ∧
      RstK (upsilon μ) (upsilon (μ + ω)) (upsilon (μ + ω + 1)) ∧
      ∀ g, upsilon μ ≤ g → g ≤ upsilon (μ + ω + 1) + LpT.val s (upsilon μ) → le1 (upsilon μ) g) :
    le1 (upsilon r) (upsilon (r + ω + 1) + LpT.val s (upsilon r) + 1) := by
  classical
  have hnx := upsilon_isNext r
  have hCs : ∀ σ, (∀ c ∈ (LpT.cs s).toFinset, c < σ) → LpT.CBt s σ := fun σ hσ =>
    LpT.cbt_iff hs (fun c hc => hσ c (List.mem_toFinset.2 hc))
  refine rs_rstF (T := LpT.val s) (C := (LpT.cs s).toFinset) h
    (fun c hc => LpT.cbt_cst hs c (List.mem_toFinset.1 hc)) hρs
    (LpT.lp_lt_ups h.ρE h.ρ1 hs hnx.1 hnx.2.1) ?_ ?_ htarget
  · intro σ hσ hB hCσ _
    exact (LpT.pi hσ h.ρU hB s (hCs σ hCσ)).2
  · intro σ hσE hσρ _ hCσ
    exact LpT.lp_lt_next hσE (hσρ.trans h.ρ1) (hCs σ hCσ) hσρ h.ρU.2

/-- **Lemma RS for every term of `LpT B`** with constants below `ρ_λ`. -/
theorem rsStep_Lp {l : Ordinal.{0}} {s : LpT B} (hs : LpT.CBt s (upsilon l)) :
    RsStep l (LpT.val s) := by
  intro R htg
  by_cases hρs : upsilon l ≤ LpT.val s (upsilon l)
  · exact rs_rstLp R hs hρs htg
  · have hn : LpT.noB s := by
      by_contra hn
      exact hρs (LpT.le_of_not_noB R.ρE R.ρ1 s hs hn)
    set c := LpT.val s (upsilon l) with hc
    have e : LpT.val s = OT.ev (OT.k c) := funext (fun y => by
      rw [OT.ev_k, hc, LpT.noB_val s hn y])
    have hcb : OT.CB (OT.k c) (upsilon l) := not_le.1 hρs
    rw [e] at htg
    have h := rs_rstT R hcb htg
    rwa [OT.ev_k] at h


theorem lp_top_lt_next_ups (n : ℕ) {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) :
    gP B n (upsilon l) < upsilon (l + ω + 1) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρU := upsPt_upsilon hl0
  have h1 : l < l + ω := lt_add_of_pos_right l omega0_pos
  have hτU := upsPt_upsilon (hl0.trans h1)
  exact (LpT.lp_top_lt_next (upsPt_inE hρU) (ups_lt_Om1 l hl1) n (upsilon_normal.strictMono h1) hτU.2).trans
    (upsilon_normal.strictMono (lt_add_one _))

/-- **The term system of stage `n`** (top `gP B n`). -/
noncomputable def lpSys (B : LpB) (n : ℕ) : XtSys where
  Tm := LpT B
  val := LpT.val
  CB := fun t x => LpT.CBt t x ∧ LpT.stage t ≤ n
  cs := LpT.cs
  cst := LpT.cst
  top := gP B n
  cb_cst := fun _ _ h => LpT.cbt_cst h.1
  cb_iff := fun _ _ _ h hc => ⟨LpT.cbt_iff h.1 hc, h.2⟩
  val_cst := fun _ _ => rfl
  cb_cstI := fun _ _ h => ⟨h, Nat.zero_le n⟩
  lt_top := fun l hl hl1 t hCB =>
    (LpT.lp_T (ups_inE hl) (ups_lt_Om1 l hl1) t hCB.1).2.trans_le (gP_mono B (ups_inE hl) (ups_lt_Om1 l hl1) hCB.2)
  one_le_top := fun l hl hl1 =>
    one_le_iff_pos.2 (gP_facts B (ups_inE hl) (ups_lt_Om1 l hl1) n).2.2.2.pos
  rep := fun l hl hl1 v hv => by
    obtain ⟨t, h1, h2, h3⟩ :=
      lp_rep (upsPt_upsilon (pos_iff_ne_zero.2 hl.1)) (ups_lt_Om1 l hl1) (Lx.lxRep_ri B.ek hl hl1) n v hv
    exact ⟨t, ⟨h1, h2⟩, h3⟩
  top_lt := fun l hl hl1 => lp_top_lt_next_ups n hl hl1
  pkg := fun _ hl hl1 _ hCB h1 R => LpGK.pkgLp R (Lx.lxRep_ri B.ek hl hl1) (Lx.lxBase_ri B.ek hl hl1 R) hCB.1 h1
  rs := fun _ _ _ _ hCB => rsStep_Lp hCB.1
  uni_le := fun _ _ hσ hρ hB _ _ ht hu => LpT.uni_le hσ hρ hB ht.1 hu.1
  small := fun t => by
    rcases lp_small t with h | h
    · exact Or.inl h
    · exact Or.inr fun x hx hx1 hc => h x hx hx1 hc.1

theorem lpSys_top (n : ℕ) (x : Ordinal.{0}) : (lpSys B n).top x = gP B n x := rfl

/-- **The top `gP B n` of `lpSys B n` has an IMG package.** -/
theorem lpSys_topPkg (n : ℕ) : XtTopPkg (lpSys B n) := fun _ hl hl1 R =>
  LpGK.lpTopPkg R (Lx.lxRep_ri B.ek hl hl1) (Lx.lxBase_ri B.ek hl hl1 R) n

theorem lp_lamLtB1 (n : ℕ) : xtLam (lpSys B n) < xtB1 (lpSys B n) := lyLamLtB1 (lpSys_topPkg n)

/-! ## Past `Λ⁺(lpSys B n)` -/

/-- **The top of `lpSys B n` inside `lpSys B (n+1)`**: `gP B n = gTm n`, and `gP B n + 1 < gP B (n+1)`. -/
theorem lp_topIn (n : ℕ) : LyTopIn (lpSys B (n + 1)) (lpSys B n) := by
  refine ⟨gTm n, fun x hx _ => ⟨⟨(gTm_val (B := B) (upsPt_inE hx) n).1, by rw [gTm_stage]⟩,
    (gTm_val (B := B) (upsPt_inE hx) n).2⟩, fun l hl hl1 => ?_⟩
  have hρE := ups_inE hl
  have hρ1 := ups_lt_Om1 l hl1
  have hE := (gP_facts B hρE hρ1 (n + 1)).2.2.2
  rw [lpSys_top, lpSys_top]
  exact (inE_indec hE).add_lt (gP_lt_succ B hρE hρ1 n) (lu_one_lt_E hE)

/-- **`Λ⁺(lpSys B n) < Λ(lpSys B (n+1))`.** -/
theorem lpLam_gt (n : ℕ) : xtB1 (lpSys B n) < xtLam (lpSys B (n + 1)) := lyLamGt (lpSys_topPkg n) (lp_topIn n)

/-- **`O_{n+1} = O_n` below `Λ⁺(lpSys B n)`.** -/
theorem lp_eq (n : ℕ) {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h : μ < xtB1 (lpSys B n)) :
    xtOrec (lpSys B (n + 1)) μ = xtOrec (lpSys B n) μ :=
  lyEq (lpSys_topPkg n) (lp_topIn n) hμ h

/-- **`O_{n+1}(Λ⁺(lpSys B n)) = gP B n ρ + 1`.** -/
theorem lp_atB1 (n : ℕ) : xtOrec (lpSys B (n + 1)) (xtB1 (lpSys B n)) = gP B n (upsilon (xtB1 (lpSys B n))) + 1 := by
  rw [lyAtB1 (lpSys_topPkg n) (lp_topIn n), lpSys_top]

/-- **The exact reach at `Λ⁺(lpSys B n)`**: `lh(ρ) = δ + gP B n ρ + 1`. -/
theorem lpReach1 (n : ℕ) :
    IsReach R2C (upsilon (xtB1 (lpSys B n)))
      (upsilon (xtB1 (lpSys B n) + ω + 1) + (gP B n (upsilon (xtB1 (lpSys B n))) + 1)) := by
  have := lyReachB1 (lpSys_topPkg (B := B) (n + 1)) (lpSys_topPkg n) (lp_topIn n)
  rwa [lpSys_top] at this

/-- **The order of the frontiers**: `Λ⁺(lpSys B n) < Λ(lpSys B (n+1)) < Λ⁺(lpSys B (n+1)) < Ω₁`. -/
theorem lp_order (n : ℕ) : xtB1 (lpSys B n) < xtLam (lpSys B (n + 1)) ∧
    xtLam (lpSys B (n + 1)) < xtB1 (lpSys B (n + 1)) ∧ xtB1 (lpSys B (n + 1)) < Om1 :=
  ⟨lpLam_gt n, lp_lamLtB1 (n + 1), xtB1_lt_Om1 (lpSys_topPkg (n + 1))⟩

/-- **The top of the base layer `K` inside `lpSys B 1`**: `E_K = tp`, and `E_K + 1 < gP B 1`. -/
theorem lp_topIn_K : LyTopIn (lpSys B 1) B.K.sys := by
  refine ⟨LpT.tp, fun x hx hx1 => ⟨⟨trivial, le_rfl⟩, ?_⟩, fun l hl hl1 => ?_⟩
  · show B.K.E x = B.K.sys.top x
    rw [Lx.lx_top B.ek (upsPt_inE hx) hx1]
  · have hρE := ups_inE hl
    have hρ1 := ups_lt_Om1 l hl1
    have hE := (gP_facts B hρE hρ1 1).2.2.2
    rw [lpSys_top, Lx.lx_top B.ek hρE hρ1]
    exact (inE_indec hE).add_lt (gP_lt_succ B hρE hρ1 0) (lu_one_lt_E hE)

/-- **`Λ⁺(K) < Λ(lpSys B 1)`**: the ladder over the base starts above the frontier of the base layer. -/
theorem lpLam_gt_K : xtB1 B.K.sys < xtLam (lpSys B 1) := lyLamGt (XtLay.topPkg B.K) lp_topIn_K

/-- **`O_{lpSys B 1} = O_K` below `Λ⁺(K)`.** -/
theorem lp_eq_K {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h : μ < xtB1 B.K.sys) :
    xtOrec (lpSys B 1) μ = xtOrec B.K.sys μ :=
  lyEq (XtLay.topPkg B.K) lp_topIn_K hμ h

/-- **`O_{lpSys B 1}(Λ⁺(K)) = E_K(ρ) + 1`.** -/
theorem lp_atB1_K : xtOrec (lpSys B 1) (xtB1 B.K.sys) = B.K.sys.top (upsilon (xtB1 B.K.sys)) + 1 :=
  lyAtB1 (XtLay.topPkg B.K) lp_topIn_K

/-- **`Λ⁺(K) < Λ⁺(lpSys B n)` for every `n ≥ 1`.** -/
theorem lpB1_gt_K : ∀ n : ℕ, xtB1 B.K.sys < xtB1 (lpSys B (n + 1))
  | 0 => lpLam_gt_K.trans (lp_lamLtB1 1)
  | n + 1 => (lpB1_gt_K n).trans ((lpLam_gt (n + 1)).trans (lp_lamLtB1 (n + 2)))

/-! ## BLK^O and the exact reaches up to `Λ⁺(lpSys B n)` -/

theorem lp_nonfix (n : ℕ) : XtNonfix (xtOrec (lpSys B n)) (xtB1 (lpSys B n)) :=
  fun _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtB1_lt_Om1 (lpSys_topPkg n)))

/-- **The exact reach of every restart below `Λ⁺(lpSys B n)`**: `lh(ρ_λ) = δ_λ + O(λ)`. -/
theorem lp_reach (n : ℕ) {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < xtB1 (lpSys B n)) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec (lpSys B n) l) :=
  xtReach1 (lpSys_topPkg n) hl hlB

/-- **The exact reach at the frontier `Λ(lpSys B n)`**: `lh(ρ) = δ + gP B n ρ`. -/
theorem lp_reachLam (n : ℕ) :
    IsReach R2C (upsilon (xtLam (lpSys B n)))
      (upsilon (xtLam (lpSys B n) + ω + 1) + gP B n (upsilon (xtLam (lpSys B n)))) := by
  rw [← lpSys_top n, ← xtOrec_Lam]
  exact xtReach1 (lpSys_topPkg n) xtLam_ri (lp_lamLtB1 n)

/-- **The reach at the frontier of every term `t` of `(lpSys B n)`** (constants below `ρ` at `Λ(lpSys B n)`,
value `≥ 1`):
`lh(ρ) = δ + t(ρ)`. -/
theorem lp_reachTerm (n : ℕ) {t : LpT B}
    (hCB : LpT.CBt t (upsilon (xtLam (lpSys B n))) ∧ LpT.stage t ≤ n)
    (h1 : 1 ≤ LpT.val t (upsilon (xtLam (lpSys B n)))) :
    IsReach R2C (upsilon (xtLamT (lpSys B n) t))
      (upsilon (xtLamT (lpSys B n) t + ω + 1) + LpT.val t (upsilon (xtLamT (lpSys B n) t))) :=
  xtReach_LamT (X := (lpSys B n)) hCB h1

/-- **Theorem BLK^O below `υ_{Λ⁺(lpSys B n)}`** in `R₂^C`. -/
theorem lp_blk (n : ℕ) :
    (∀ c d, c < d → d < upsilon (xtB1 (lpSys B n)) → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 (lpSys B n) ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 (lpSys B n) →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec (lpSys B n) l)) ∧
    (∀ α < upsilon (xtB1 (lpSys B n)), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  xtBlk1 (lpSys_topPkg n)

/-! ## ENUM-REACH and the caps -/

variable {S : InaccSeq.{0}}

/-- **UPPER and LOWER (ENUM-REACH) at every restart of the range below `Λ⁺(lpSys B n)` that is not a fixed point of
`υ`.** -/
theorem lp_init (n : ℕ) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 (lpSys B n)) (hfix : l < upsilon l) :
    CdUpper S l ∧ CdLower S l :=
  xtInit (xtSpec1 (lpSys_topPkg n)) (lp_nonfix n) hr hl hfix

/-- **The cap of the values at every non-fixed restart of the range below `Λ⁺(lpSys B n)`.** -/
theorem lp_capV (n : ℕ) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 (lpSys B n)) (hfix : l < upsilon l) :
    CdCapV S l := by
  have hww := cp_ww_lt_B0.trans_le hr.2.1
  exact xtCapV_nonfix (xtSpec1 (lpSys_topPkg n)) hr.1 hww hfix hl (cp_name_L hr.2.2.1)
    ((lp_nonfix n) l hr.1 hww hfix hl)

theorem lp_capAt (n : ℕ) {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hB : cdB0 ≤ l) (hlΛ : l < xtB1 (lpSys B n))
    (hfix : l < upsilon l) (hname : upsilon l < Pv S η1) : CdCapAt S l := by
  have hww := cp_ww_lt_B0.trans_le hB
  exact xtCapAt_nonfix (xtSpec1 (lpSys_topPkg n)) hl hww hfix hlΛ hname ((lp_nonfix n) l hl hww hfix hlΛ)

/-- **Below `Λ⁺(lpSys B n)`, ENUM-REACH is the equation `Θ_λ(m_λ) = O(λ)`.** -/
theorem lp_iff (n : ℕ) {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < xtB1 (lpSys B n)) :
    (CdUpper S l ∧ CdLower S l ↔ cdTheta S l (cdCode S l) = xtOrec (lpSys B n) l) :=
  xtExact_iff (xtSpec1 (lpSys_topPkg n)) hl hlB

/-- **The offset at an isolated fixed point below `Λ⁺(lpSys B n)`**: `O(F) = F`. -/
theorem lp_iso (n : ℕ) {F : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hFB : F < xtB1 (lpSys B n))
    (hiso : CpIso F) : xtOrec (lpSys B n) F = F :=
  xtIso hF hfix (hFB.trans (xtB1_lt_Om1 (lpSys_topPkg n))) hiso

/-- **ENUM-REACH at an isolated fixed point of the range below `Λ⁺(lpSys B n)` reduces to the code.** -/
theorem lp_fix_code (n : ℕ) {F : Ordinal.{0}} (hr : CdRange S F) (hfix : upsilon F = F) (hFB : F < xtB1 (lpSys B n))
    (hiso : CpIso F) : (F ≤ cdCode S F → CdUpper S F) ∧ (cdCode S F ≤ Om1 → CdLower S F) :=
  xtFix_code (xtSpec1 (lpSys_topPkg n)) hr.1 hfix hFB (lp_iso n hr.1 hfix hFB hiso) (cp_name_L hr.2.2.1)

/-- **The hypotheses of `lpRoad3 (n+1)` from those of `lpRoad3 n`.** -/
theorem lp_of (n : ℕ) (hU : ∀ l, CdRange S l → xtB1 (lpSys B n) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 (lpSys B n) ≤ l → CdLower S l)
    (hT : ∀ l, CdRange S l → l < xtB1 (lpSys B n) → upsilon l = l →
      cdTheta S l (cdCode S l) = xtOrec (lpSys B n) l) :
    (∀ l, CdRange S l → xtB1 (lpSys B (n + 1)) ≤ l → CdUpper S l) ∧
      (∀ l, CdRange S l → xtB1 (lpSys B (n + 1)) ≤ l → CdLower S l) ∧
      (∀ l, CdRange S l → l < xtB1 (lpSys B (n + 1)) → upsilon l = l →
        cdTheta S l (cdCode S l) = xtOrec (lpSys B (n + 1)) l) := by
  have hle : xtB1 (lpSys B n) ≤ xtB1 (lpSys B (n + 1)) := ((lpLam_gt n).trans (lp_lamLtB1 (n + 1))).le
  refine ⟨fun l hr h => hU l hr (hle.trans h), fun l hr h => hL l hr (hle.trans h), fun l hr hlB hfix => ?_⟩
  rcases lt_or_ge l (xtB1 (lpSys B n)) with h | h
  · rw [lp_eq n hr.1 h]; exact hT l hr h hfix
  · exact (lp_iff (n + 1) hr.1 hlB).1 ⟨hU l hr h, hL l hr h⟩

/-- **The road with UPPER and LOWER asked only at `λ ≥ Λ⁺(lpSys B n)`**, `Θ_F(m_F) = O(F)` at the fixed points of the
range below `Λ⁺(lpSys B n)`, the cap of the values outside `Λ⁺(lpSys B n)`, (CL), EQ, TCrest, (EMB₂). -/
theorem lpRoad3 (n : ℕ) (hU : ∀ l, CdRange S l → xtB1 (lpSys B n) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 (lpSys B n) ≤ l → CdLower S l)
    (hT : ∀ l, CdRange S l → l < xtB1 (lpSys B n) → upsilon l = l → cdTheta S l (cdCode S l) = xtOrec (lpSys B n) l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 (lpSys B n)) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad3 (xtSpec1 (lpSys_topPkg n)) (lp_nonfix n) hU hL hT hV hC hEQ hrest hB2

/-- **The road with UPPER, LOWER and the cap of the values asked only outside `Λ⁺(lpSys B n)`.** -/
theorem lpRoad (n : ℕ) (hU : ∀ l, CdRange S l → XtOut (xtB1 (lpSys B n)) l → CdUpper S l)
    (hL : ∀ l, CdRange S l → XtOut (xtB1 (lpSys B n)) l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 (lpSys B n)) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad (xtSpec1 (lpSys_topPkg n)) (lp_nonfix n) hU hL hV hC hEQ hrest hB2

/-- **The road with the caps asked only outside `Λ⁺(lpSys B n)`**: CAP-0, CAP-1 outside, (CL), (TC), (EMB₂). -/
theorem lpRoad_cap (n : ℕ)
    (h0 : ∀ l, IsRestartIdx l → cdB0 ≤ l → upsilon l < cdMstar S → XtOut (xtB1 (lpSys B n)) l → CdCapAt S l)
    (h1 : ∀ l, IsRestartIdx l → cdB0 ≤ l → cdMstar S ≤ upsilon l → upsilon l < Nc.ncL S ω →
      cdCode S l < Nc.ncPp S → XtOut (xtB1 (lpSys B n)) l → CdCapAt S l) (hC : CdCL S) (hTC : CdTC S)
    (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad_cap (xtSpec1 (lpSys_topPkg n)) (lp_nonfix n) h0 h1 hC hTC hB2

end Googology.Trans.PoR.InaccPsi.R2.Lp

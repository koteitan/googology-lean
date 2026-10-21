import Googology.Trans.PoR.InaccPsi.R2.LvGRd
import Googology.Trans.PoR.InaccPsi.R2.LyLim

/-!
# The limit system of the staged tower: `lgUSys` with top `Γ(x) = sup_n gT n x`

`lgUSys` is the term system of **all** terms of `LvGT` (every stage), with top `lgG x = sup_n gT n x`.  Its fields
are those of `lvgSys n` without the stage bound (Lemma IMG `LvGK.pkgLvG`, Lemma RS `rsStep_LvG`, EXACT `LvGT.uni_le`,
the representation `lvg_rep` below some `gT n`).  The tower `lvgSys n` is a chain inside it (`R2.LyLim`):

* `lgU_topIn` (the top `gT n` of `lvgSys n` is a term of `lgUSys`, `gT n + 1 < lgG`), `lgChain`;
* `lgU_at` (**`O(λ∞) = lgG(ρ_{λ∞})` at `λ∞ = sup_n Λ⁺(lvgSys n)`**, `Ly.LyChain.lyLimAt`), `lgU_lam` (**`Λ(lgUSys) =
  λ∞`**), `lgU_eq` (**`O_U = O_n` below `Λ⁺(lvgSys n)`**);
* `lg_blk` (**Theorem BLK^O below `υ_{λ∞}`**), `lg_reach` (**`lh(ρ_λ) = δ_λ + O_U(λ)` for every restart `λ < λ∞`**);
* `lgEnum` (**ENUM-REACH at every restart of the range below `λ∞`**, fixed points included), `lg_capV` (CapV at the
  non-fixed ones), `lgT_fix` (the notation hypothesis below `λ∞`), `lgRoadPh` (**the road with UPPER/LOWER asked only
  at `λ ≥ λ∞`**: the successor of `lvgRoadPh`).

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Nm Lu

/-- **The limit top** `lgG x = sup_n gT n x` (`= Γ_{x+1}`, see `R2.LgLoc`). -/
noncomputable def lgG (x : Ordinal.{0}) : Ordinal.{0} := ⨆ n : ℕ, gT n x

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem gT_lt_lgG (n : ℕ) : gT n x < lgG x :=
  (gT_lt_succ hx hx1 n).trans_le (Ordinal.le_iSup (fun k : ℕ => gT k x) (n + 1))

omit hx hx1 in
theorem lt_lgG_iff {v : Ordinal.{0}} : v < lgG x ↔ ∃ n, v < gT n x := Ordinal.lt_iSup_iff

omit hx hx1 in
theorem lgG_le {u : Ordinal.{0}} (h : ∀ n, gT n x ≤ u) : lgG x ≤ u := Ordinal.iSup_le h

theorem lgG_lt_Om1 : lgG x < Om1 := Ordinal.iSup_lt_omega_one fun n => (gT_facts hx hx1 n).2.2.1

theorem lgG_pos : 0 < lgG x := (gT_facts hx hx1 0).2.2.2.pos.trans (gT_lt_lgG hx hx1 0)

end Base

theorem lgG_le_ups {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) :
    lgG (upsilon l) ≤ upsilon (l + ω) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have h1 : l < l + ω := lt_add_of_pos_right l omega0_pos
  have hτU := upsPt_upsilon (hl0.trans h1)
  exact lgG_le fun n => (LvGT.lvg_top_lt_next (ups_inE hl) (ups_lt_Om1 l hl1) n
    (upsilon_normal.strictMono h1) hτU.2).le

theorem lgG_lt_next_ups {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) :
    lgG (upsilon l) < upsilon (l + ω + 1) :=
  (lgG_le_ups hl hl1).trans_lt (upsilon_normal.strictMono (lt_add_one _))

/-- **The limit term system**: all terms of `LvGT`, top `lgG`. -/
noncomputable def lgUSys : XtSys where
  Tm := LvGT
  val := LvGT.val
  CB := LvGT.CBt
  cs := LvGT.cs
  cst := LvGT.cst
  top := lgG
  cb_cst := fun _ _ h => LvGT.cbt_cst h
  cb_iff := fun _ _ _ h hc => LvGT.cbt_iff h hc
  val_cst := fun _ _ => rfl
  cb_cstI := fun _ _ h => h
  lt_top := fun l hl hl1 t hCB =>
    (LvGT.lvg_T (ups_inE hl) (ups_lt_Om1 l hl1) t hCB).2.trans (gT_lt_lgG (ups_inE hl) (ups_lt_Om1 l hl1) _)
  one_le_top := fun l hl hl1 => one_le_iff_pos.2 (lgG_pos (ups_inE hl) (ups_lt_Om1 l hl1))
  rep := fun l hl hl1 v hv => by
    obtain ⟨n, hn⟩ := lt_lgG_iff.1 hv
    obtain ⟨t, h1, -, h3⟩ := lvg_rep (ups_inE hl) (ups_lt_Om1 l hl1) n v hn
    exact ⟨t, h1, h3⟩
  top_lt := fun l hl hl1 => lgG_lt_next_ups hl hl1
  pkg := fun _ _ _ _ hCB h1 R => LvGK.pkgLvG R hCB h1
  rs := fun _ _ _ _ hCB => rsStep_LvG hCB
  uni_le := fun _ _ hσ hρ hB _ _ ht hu => LvGT.uni_le hσ hρ hB ht hu
  small := fun t => by
    rcases lvg_small t with h | h
    · exact Or.inl h
    · exact Or.inr fun x hx hx1 hc => h x hx hx1 hc

theorem lgUSys_top (x : Ordinal.{0}) : lgUSys.top x = lgG x := rfl

/-- **The top `gT n` of `lvgSys n` is a term of `lgUSys`**, with `gT n + 1 < lgG`. -/
theorem lgU_topIn (n : ℕ) : LyTopIn lgUSys (lvgSys n) := by
  refine ⟨gTm n, fun x hx hx1 => ⟨(gTm_val (upsPt_inE hx) hx1 n).1, (gTm_val (upsPt_inE hx) hx1 n).2⟩,
    fun l hl hl1 => ?_⟩
  have hρE := ups_inE hl
  have hρ1 := ups_lt_Om1 l hl1
  have hE := (gT_facts hρE hρ1 (n + 1)).2.2.2
  rw [lvgSys_top, lgUSys_top]
  exact ((inE_indec hE).add_lt (gT_lt_succ hρE hρ1 n) (lu_one_lt_E hE)).trans (gT_lt_lgG hρE hρ1 (n + 1))

/-- **The tower `lvgSys n` as a chain inside `lgUSys`.** -/
noncomputable def lgChain : LyChain lgUSys where
  Y := lvgSys
  pkg := lvgSys_topPkg
  inX := lgU_topIn
  next := lvgLam_gt
  topMono := fun k _ hx hx1 => (gT_lt_succ hx hx1 k).le

/-- **`λ∞ = sup_n Λ⁺(lvgSys n)`.** -/
noncomputable def lgLam : Ordinal.{0} := lgChain.fam.famSup

theorem lgLam_eq : lgLam = ⨆ n : ℕ, xtB1 (lvgSys n) := rfl

theorem lgB1_lt_lgLam (n : ℕ) : xtB1 (lvgSys n) < lgLam := lgChain.fam.famBd_lt n

theorem lgLam_ri : IsRestartIdx lgLam := lgChain.sup_ri

theorem lgLam_lt_Om1 : lgLam < Om1 := lgChain.fam.famSup_lt_Om1

theorem lgLam_lt {l : Ordinal.{0}} (h : l < lgLam) : ∃ n, l < xtB1 (lvgSys n) := lgChain.fam.famLt h

/-- **The offset at the limit**: `O_U(λ∞) = lgG(ρ_{λ∞})`. -/
theorem lgU_at : xtOrec lgUSys lgLam = lgG (upsilon lgLam) :=
  lgChain.lyLimAt lgG (fun k _ hx hx1 => gT_lt_lgG hx hx1 k) (fun _ _ _ _ hv => lt_lgG_iff.1 hv)

/-- **`Λ(lgUSys) = λ∞`.** -/
theorem lgU_lam : xtLam lgUSys = lgLam := le_antisymm (xtLam_le lgLam_ri lgU_at) lgChain.sup_le

/-- **`O_U = O_n` below `Λ⁺(lvgSys n)`.** -/
theorem lgU_eq (n : ℕ) {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h : μ < xtB1 (lvgSys n)) :
    xtOrec lgUSys μ = xtOrec (lvgSys n) μ :=
  lyEq (lvgSys_topPkg n) (lgU_topIn n) hμ h

/-- **`O_U(Λ⁺(lvgSys n)) = gT n ρ + 1`.** -/
theorem lgU_atB1 (n : ℕ) : xtOrec lgUSys (xtB1 (lvgSys n)) = gT n (upsilon (xtB1 (lvgSys n))) + 1 := by
  rw [lyAtB1 (lvgSys_topPkg n) (lgU_topIn n), lvgSys_top]

theorem lgLam_mult : ω * ω ∣ lgLam := (ri_iff.1 lgLam_ri).2

/-- The offset `O_U` is a specification up to `λ∞`. -/
theorem lgSpec : OffSpecGen (xtOrec lgUSys) lgLam := xtSpec_of_le lgLam_mult lgLam_lt_Om1 lgU_lam.symm.le

theorem lgNonfix : XtNonfix (xtOrec lgUSys) lgLam := by
  have h := xtNonfix_sys lgUSys
  rwa [lgU_lam] at h

/-- **Theorem BLK^O below `υ_{λ∞}`** in `R₂^C`. -/
theorem lg_blk :
    (∀ c d, c < d → d < upsilon lgLam → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < lgLam ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < lgLam →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec lgUSys l)) ∧
    (∀ α < upsilon lgLam, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  xtBlk lgLam_mult lgLam_lt_Om1 lgU_lam.symm.le

/-- **The exact reach of every restart below `λ∞`**: `lh(ρ_λ) = δ_λ + O_U(λ)`. -/
theorem lg_reach {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < lgLam) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec lgUSys l) :=
  xtReach hl (lgU_lam.symm ▸ hlB)

variable {S : InaccSeq.{0}}

/-- **ENUM-REACH (UPPER and LOWER) at every restart of the range below `λ∞`**, fixed points of `υ` included. -/
theorem lgEnum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < lgLam) : CdUpper S l ∧ CdLower S l := by
  obtain ⟨n, hn⟩ := lgLam_lt hl
  exact lvgEnum n hr hn

/-- **The cap of the values at every non-fixed restart of the range below `λ∞`.** -/
theorem lg_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < lgLam) (hfix : l < upsilon l) : CdCapV S l := by
  obtain ⟨n, hn⟩ := lgLam_lt hl
  exact lvg_capV n hr hn hfix

/-- **The notation hypothesis below `λ∞`**: `Θ_λ(m_λ) = O_U(λ)` at every fixed point of the range. -/
theorem lgT_fix {l : Ordinal.{0}} (hr : CdRange S l) (hlB : l < lgLam) (hfix : upsilon l = l) :
    cdTheta S l (cdCode S l) = xtOrec lgUSys l := by
  obtain ⟨n, hn⟩ := lgLam_lt hlB
  rw [lgU_eq n hr.1 hn]
  exact lvgT_fix n hr hn hfix

/-- **The road with UPPER and LOWER asked only at `λ ≥ λ∞`** (the successor of `lvgRoadPh`): the rest is CapV at the
outer restarts below `L(ω)`, (CL), EQ, TCrest, (EMB₂). -/
theorem lgRoadPh (hU : ∀ l, CdRange S l → lgLam ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → lgLam ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut lgLam l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad3 lgSpec lgNonfix hU hL (fun _ hr hlB hfix => lgT_fix hr hlB hfix) hV hC hEQ hrest hB2

end Googology.Trans.PoR.InaccPsi.R2

import Googology.Trans.PoR.InaccPsi.R2.VzO

/-!
# Theorem BLK^O once for every term system with EXACT, IMG and RS

The stages `R2.EpsO`, `R2.EvO`, `R2.EvOZ`, `R2.VzO` (and `R2.CpFront`) repeat one pattern for a term type:
the recursive offset `O(λ) = sup ({1} ∪ {s(ρ_λ) + 1 : s realized cofinally below λ})`, its frontier
`Λ = min {λ : O(λ) = top(ρ_λ)}`, the inputs of Lemmas TOP and RS, Theorem BLK^O below `υ_Λ`, the frontier of a
term, and the extension to the first limit of frontiers when the top itself has an IMG package.  Here the pattern
is stated once, for a structure `XtSys` that lists what a term type has to supply:

* constants (`cst`, `cs`, `CB`), values below a top `top(ρ)` (`lt_top`), and every ordinal below the top a value
  (`rep`), the top below the first block top (`top_lt`);
* **IMG** (`pkg`: the IMG package of every term with value `≥ 1`), **RS** (`rs`: Lemma RS for every term), the
  comparison of values at two bases (`uni_le`, a consequence of **EXACT**), and `small` (a term is constant or has
  value at least the base).

Then (namespace `Xt`, the term system `X` explicit):

* `xtOrec X` (the recursive offset), `xtLam X` (the frontier), `xtTopIn`, `xtRsIn`, `xtSpec`, `xtSpec_of_le`;
* `xtBlk` (**Theorem BLK^O below `υ_B` for every `B ≤ Λ`**), `xtCore`, `xtLam_lt_Om1`, `xtReach`
  (`lh(ρ_λ) = δ_λ + O(λ)` below `Λ`);
* `xtLamT` (the frontier of a term), `xtOrec_LamT`, `xtLamT_lt_Lam`, `xtReach_LamT` (the reach at every frontier);
* `XtTopPkg` (the top has an IMG package), `XtFr`, `xtB1` (the first limit of frontiers), `xtSpec1`
  (**the offset is a specification up to `xtB1`**), `xtBlk1`, `xtReach1`;
* `xtOrec_unique` (every solution of the recursion is `xtOrec`), `xt_off_eq` (two specifications have the same
  offset where both hold: the reach is unique).

No new axiom.

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Xt

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2

/-- **A term system with EXACT, IMG and RS**: what the block theorem asks of a term type. -/
structure XtSys where
  Tm : Type 1
  val : Tm → Ordinal.{0} → Ordinal.{0}
  CB : Tm → Ordinal.{0} → Prop
  cs : Tm → List Ordinal.{0}
  cst : Ordinal.{0} → Tm
  top : Ordinal.{0} → Ordinal.{0}
  cb_cst : ∀ t s, CB t s → ∀ c ∈ cs t, c < s
  cb_iff : ∀ t s s', CB t s → (∀ c ∈ cs t, c < s') → CB t s'
  val_cst : ∀ c x, val (cst c) x = c
  cb_cstI : ∀ c x, c < x → CB (cst c) x
  lt_top : ∀ l, IsRestartIdx l → l < Om1 → ∀ t, CB t (upsilon l) → val t (upsilon l) < top (upsilon l)
  one_le_top : ∀ l, IsRestartIdx l → l < Om1 → 1 ≤ top (upsilon l)
  rep : ∀ l, IsRestartIdx l → l < Om1 → ∀ v < top (upsilon l), ∃ t, CB t (upsilon l) ∧ val t (upsilon l) = v
  top_lt : ∀ l, IsRestartIdx l → l < Om1 → top (upsilon l) < upsilon (l + ω + 1)
  pkg : ∀ l, IsRestartIdx l → l < Om1 → ∀ t, CB t (upsilon l) → 1 ≤ val t (upsilon l) →
    RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1)) →
    ImgPkg (upsilon l) (upsilon (l + ω + 1)) (val t)
  rs : ∀ l, IsRestartIdx l → l < Om1 → ∀ t, CB t (upsilon l) → RsStep l (val t)
  uni_le : ∀ σ ρ, UpsPt σ → UpsPt ρ → Bases σ ρ → ∀ t u, CB t σ → CB u σ →
    (val t ρ ≤ val u ρ ↔ val t σ ≤ val u σ)
  small : ∀ t, (∀ x y, val t x = val t y) ∨ (∀ x, InE x → x < Om1 → CB t x → x ≤ val t x)

variable (X : XtSys)

/-- `s` is realized cofinally below `λ` by the offsets `O`. -/
def XtCof (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) (s : X.Tm) : Prop :=
  ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ X.CB s (upsilon μ) ∧ X.val s (upsilon μ) ≤ O μ

/-- The set whose supremum is the offset at `λ`. -/
def XtOSet (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : Set Ordinal.{0} :=
  insert 1 {w | ∃ s, X.CB s (upsilon l) ∧ XtCof X O l s ∧ w = X.val s (upsilon l) + 1}

theorem XtOSet_congr {O O' : Ordinal.{0} → Ordinal.{0}} {l : Ordinal.{0}}
    (h : ∀ μ < l, O μ = O' μ) : XtOSet X O l = XtOSet X O' l := by
  have key : ∀ s, XtCof X O l s ↔ XtCof X O' l s := by
    intro s
    constructor
    · intro hc ν hν
      obtain ⟨μ, h1, h2, h3, h4, h5⟩ := hc ν hν
      exact ⟨μ, h1, h2, h3, h4, by rw [← h μ h3]; exact h5⟩
    · intro hc ν hν
      obtain ⟨μ, h1, h2, h3, h4, h5⟩ := hc ν hν
      exact ⟨μ, h1, h2, h3, h4, by rw [h μ h3]; exact h5⟩
  ext w
  simp only [XtOSet, Set.mem_insert_iff, Set.mem_setOf_eq, key]

/-- **The recursive offset** of the term system, by well-founded recursion. -/
noncomputable def xtOrec : Ordinal.{0} → Ordinal.{0} :=
  Ordinal.lt_wf.fix (fun l IH => sSup (XtOSet X (fun μ => if h : μ < l then IH μ h else 0) l))

theorem xtOrec_eq (l : Ordinal.{0}) : xtOrec X l = sSup (XtOSet X (xtOrec X) l) := by
  show Ordinal.lt_wf.fix _ l = _
  rw [WellFounded.fix_eq]
  rw [XtOSet_congr X (O' := xtOrec X) (fun μ hμ => by simp only [hμ, dite_true]; rfl)]

/-- **Every solution of the recursion is `xtOrec`.** -/
theorem xtOrec_unique {O : Ordinal.{0} → Ordinal.{0}} (hO : ∀ l, O l = sSup (XtOSet X O l)) :
    O = xtOrec X := by
  funext l
  induction l using WellFoundedLT.induction with
  | ind l IH =>
  rw [hO l, xtOrec_eq X l, XtOSet_congr X (O' := xtOrec X) (fun μ hμ => IH μ hμ)]

theorem XtOSet_bdd (O : Ordinal.{0} → Ordinal.{0}) {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) :
    ∀ w ∈ XtOSet X O l, w ≤ X.top (upsilon l) := by
  intro w hw
  rcases hw with rfl | ⟨s, hCB, -, rfl⟩
  · exact X.one_le_top l hl hl1
  · exact add_one_le_of_lt (X.lt_top l hl hl1 s hCB)

theorem XtOSet_bddAbove (O : Ordinal.{0} → Ordinal.{0}) {l : Ordinal.{0}} (hl : IsRestartIdx l)
    (hl1 : l < Om1) : BddAbove (XtOSet X O l) := ⟨_, XtOSet_bdd X O hl hl1⟩

variable {X}

theorem xtOrec_le_top {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) :
    xtOrec X l ≤ X.top (upsilon l) := by
  rw [xtOrec_eq]
  exact csSup_le ⟨1, Set.mem_insert _ _⟩ (XtOSet_bdd X _ hl hl1)

theorem one_le_xtOrec {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) : 1 ≤ xtOrec X l := by
  rw [xtOrec_eq]
  exact le_csSup (XtOSet_bddAbove X _ hl hl1) (Set.mem_insert _ _)

theorem lt_xtOrec_of_cof {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) {s : X.Tm}
    (hCB : X.CB s (upsilon l)) (hc : XtCof X (xtOrec X) l s) : X.val s (upsilon l) < xtOrec X l := by
  have h1 : X.val s (upsilon l) + 1 ≤ xtOrec X l := by
    rw [xtOrec_eq]
    exact le_csSup (XtOSet_bddAbove X _ hl hl1) (Set.mem_insert_of_mem _ ⟨s, hCB, hc, rfl⟩)
  exact lt_of_lt_of_le (lt_add_one _) h1

theorem lt_xtOrec {l z : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) (hz : z < xtOrec X l) :
    z = 0 ∨ ∃ s, X.CB s (upsilon l) ∧ XtCof X (xtOrec X) l s ∧ z ≤ X.val s (upsilon l) := by
  rw [xtOrec_eq] at hz
  obtain ⟨w, hw, hzw⟩ :=
    (lt_csSup_iff (XtOSet_bddAbove X _ hl hl1) ⟨1, Set.mem_insert _ _⟩).1 hz
  rcases hw with rfl | ⟨s, hCB, hc, rfl⟩
  · left; exact le_antisymm (Order.lt_add_one_iff.1 (by rw [zero_add]; exact hzw)) zero_le
  · right; exact ⟨s, hCB, hc, Order.lt_add_one_iff.1 hzw⟩

/-- An upper bound for the offset from the realized terms. -/
theorem xtOrec_le_of {l Y : Ordinal.{0}} (h1 : 1 ≤ Y)
    (h : ∀ s, X.CB s (upsilon l) → XtCof X (xtOrec X) l s → X.val s (upsilon l) < Y) : xtOrec X l ≤ Y := by
  rw [xtOrec_eq]
  refine csSup_le ⟨1, Set.mem_insert _ _⟩ ?_
  rintro w (rfl | ⟨s, hCB, hc, rfl⟩)
  · exact h1
  · exact Order.add_one_le_of_lt (h s hCB hc)

/-- The offset is `1` at a successor restart index. -/
theorem xtOrec_succ {l : Ordinal.{0}} (hl : IsRestartIdx l) (h2 : cL l < 2) : xtOrec X l = 1 := by
  obtain ⟨l0, hl0, rfl⟩ := succ_ri hl h2
  have hww : 0 < ω * ω := mul_pos omega0_pos omega0_pos
  have hS : XtOSet X (xtOrec X) (l0 + ω * ω) = {1} := by
    ext w
    simp only [XtOSet, Set.mem_insert_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro (h | ⟨s, -, hc, -⟩)
      · exact h
      · exfalso
        obtain ⟨μ, hμ, h1, h3, -, -⟩ := hc l0 (lt_add_of_pos_right l0 hww)
        exact absurd h3 (not_lt.2 (next_mult (mult_of hl0) (ri_iff.1 hμ).2 h1))
    · intro h; exact Or.inl h
  rw [xtOrec_eq, hS, csSup_singleton]

theorem xtOrec_lt_δ {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) :
    xtOrec X l < upsilon (l + ω + 1) :=
  (xtOrec_le_top hl hl1).trans_lt (X.top_lt l hl hl1)

/-! ## The frontier -/

variable (X) in
/-- **The frontier `Λ`**: the least restart index `λ` with `O(λ) = top(ρ_λ)` (`Ω₁` if there is none). -/
noncomputable def xtLam : Ordinal.{0} :=
  sInf (insert Om1 {l | IsRestartIdx l ∧ xtOrec X l = X.top (upsilon l)})

theorem xtLam_le_Om1 : xtLam X ≤ Om1 := csInf_le (OrderBot.bddBelow _) (Set.mem_insert _ _)

theorem xtLam_le {l : Ordinal.{0}} (hl : IsRestartIdx l) (h : xtOrec X l = X.top (upsilon l)) :
    xtLam X ≤ l :=
  csInf_le (OrderBot.bddBelow _) (Set.mem_insert_of_mem _ ⟨hl, h⟩)

/-- Below the frontier the offset is below the top. -/
theorem xtOrec_lt_top {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlV : l < xtLam X) :
    xtOrec X l < X.top (upsilon l) := by
  rcases (xtOrec_le_top hl (hlV.trans_le xtLam_le_Om1)).lt_or_eq with h | h
  · exact h
  · exact absurd (xtLam_le hl h) (not_le.2 hlV)

theorem xtLam_spec (h : xtLam X < Om1) :
    IsRestartIdx (xtLam X) ∧ xtOrec X (xtLam X) = X.top (upsilon (xtLam X)) := by
  rcases csInf_mem (s := insert Om1 {l | IsRestartIdx l ∧ xtOrec X l = X.top (upsilon l)})
    ⟨Om1, Set.mem_insert _ _⟩ with h' | h'
  · exact absurd (h' ▸ h : Om1 < Om1) (lt_irrefl _)
  · exact h'

/-! ## The inputs of Lemmas TOP and RS -/

/-- **The input of Lemma TOP** at a restart index `λ < Ω₁` with `O(λ) < top(ρ_λ)`. -/
theorem xtTopIn {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1)
    (hlt : xtOrec X l < X.top (upsilon l)) : TopInH (xtOrec X) l := by
  classical
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρU := upsPt_upsilon hl0
  have hone : 1 ≤ xtOrec X l := one_le_xtOrec hl hl1
  obtain ⟨s, hCB, hev⟩ := X.rep l hl hl1 _ hlt
  have hpk : RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1)) →
      ImgPkg (upsilon l) (upsilon (l + ω + 1)) (X.val s) := fun R =>
    X.pkg l hl hl1 s hCB (by rw [hev]; exact hone) R
  have hnot : ¬ XtCof X (xtOrec X) l s := fun hc =>
    absurd (lt_xtOrec_of_cof hl hl1 hCB hc) (by rw [hev]; exact lt_irrefl _)
  obtain ⟨m0, hm0, hm0c⟩ := list_max (X.cs s) _ (X.cb_cst s _ hCB) hρU.1
  unfold XtCof at hnot
  push Not at hnot
  obtain ⟨ν, hνl, hν⟩ := hnot
  have hνρ : upsilon ν < upsilon l := upsilon_normal.strictMono hνl
  refine ⟨X.val s, max (upsilon ν) m0, hev.symm, max_lt hνρ hm0, fun μ hμ hμl hx0 => ?_, hpk⟩
  have hνμ : ν < μ := upsilon_normal.strictMono.lt_iff_lt.1 (lt_of_le_of_lt (le_max_left _ _) hx0)
  have hCBμ : X.CB s (upsilon μ) :=
    X.cb_iff s _ _ hCB (fun c hc => lt_of_le_of_lt ((hm0c c hc).trans (le_max_right _ _)) hx0)
  exact hν μ hμ hνμ hμl hCBμ

/-- **The input of Lemma RS at a limit restart index `λ`**. -/
theorem xtRsIn {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) (h2 : 2 ≤ cL l) :
    RsInGen (xtOrec X) l := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρ0 : 0 < upsilon l := (upsPt_upsilon hl0).1
  intro z hz
  rcases lt_xtOrec hl hl1 hz with rfl | ⟨s, hCB, hc, hzs⟩
  · refine ⟨OT.ev (OT.k 0), zero_le, fun R htg => rs_rstT R hρ0 htg, fun ν hν => ?_⟩
    obtain ⟨μ, hμ, h1, h3, -⟩ := cL_dense hl le_rfl (lt_of_lt_of_le one_lt_two h2) ν hν
    exact ⟨μ, hμ, h1, h3, by rw [OT.ev_k]; exact zero_le⟩
  · refine ⟨X.val s, hzs, X.rs l hl hl1 s hCB, fun ν hν => ?_⟩
    obtain ⟨μ, hμ, h1, h3, -, h5⟩ := hc ν hν
    exact ⟨μ, hμ, h1, h3, h5⟩

/-- **The offset is a general specification up to `B`** when every restart index below `B` has the input of
Lemma TOP. -/
theorem xtSpec {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1)
    (hB : ∀ l, IsRestartIdx l → l < B → TopInH (xtOrec X) l) : OffSpecGen (xtOrec X) B where
  mult := hm
  cnt := hc
  le := fun _ hl hlB => xtOrec_lt_δ hl (hlB.trans hc)
  one := fun _ hl hlB => one_le_xtOrec hl (hlB.trans hc)
  top := hB
  succ := fun _ hl _ h2 => xtOrec_succ hl h2
  rs := fun _ hl hlB h2 => xtRsIn hl (hlB.trans hc) h2

theorem xtSpec_of_le {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ xtLam X) :
    OffSpecGen (xtOrec X) B :=
  xtSpec hm hc (fun _ hl hlB => xtTopIn hl (hlB.trans hc) (xtOrec_lt_top hl (lt_of_lt_of_le hlB hB)))

/-! ## Theorem BLK^O up to the frontier -/

/-- **Theorem BLK^O below `υ_B` for every `B ≤ Λ`** (`ω² ∣ B`, `B < Ω₁`) in `R₂^C`. -/
theorem xtBlk {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ xtLam X) :
    (∀ c d, c < d → d < upsilon B → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < B ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < B →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec X l)) ∧
    (∀ α < upsilon B, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  blk_genGen (xtSpec_of_le hm hc hB)

theorem xtCore {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ xtLam X) :
    Set.Iio (upsilon B) ⊆ Core R2C :=
  core_genGen (xtSpec_of_le hm hc hB)

/-- **`Λ < Ω₁`** (the core is countable, [C09] Cor 15.15). -/
theorem xtLam_lt_Om1 : xtLam X < Om1 := by
  rcases xtLam_le_Om1.lt_or_eq with h | h
  · exact h
  · exfalso
    exact not_core_all (fun B hm hc => xtCore (X := X) hm hc (by rw [h]; exact hc.le))

theorem xtLam_ri : IsRestartIdx (xtLam X) := (xtLam_spec xtLam_lt_Om1).1

theorem xtOrec_Lam : xtOrec X (xtLam X) = X.top (upsilon (xtLam X)) := (xtLam_spec xtLam_lt_Om1).2

/-- **The offset is a general specification up to `Λ`.** -/
theorem xtSpecLam : OffSpecGen (xtOrec X) (xtLam X) :=
  xtSpec_of_le (ri_iff.1 xtLam_ri).2 xtLam_lt_Om1 le_rfl

/-- **The exact reach of every restart below `Λ`**: `lh(ρ_λ) = δ_λ + O(λ)`. -/
theorem xtReach {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlV : l < xtLam X) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec X l) :=
  reach_allGen xtSpecLam hl hlV

/-! ## Two specifications have the same offset -/

/-- **Two general specifications have the same offset where both hold** (the reach is unique). -/
theorem xt_off_eq {O1 O2 : Ordinal.{0} → Ordinal.{0}} {B1 B2 : Ordinal.{0}} (S1 : OffSpecGen O1 B1)
    (S2 : OffSpecGen O2 B2) {l : Ordinal.{0}} (hl : IsRestartIdx l) (h1 : l < B1) (h2 : l < B2) :
    O1 l = O2 l :=
  (add_left_cancel_iff).1 (isReach_unique (reach_allGen S1 hl h1) (reach_allGen S2 hl h2))

/-! ## The frontier of a term -/

variable (X) in
/-- **The frontier `Λ_t` of a term `t`**: the least restart index `λ` with constants of `t` below `ρ_λ` and
`t(ρ_λ) ≤ O(λ)`. -/
noncomputable def xtLamT (t : X.Tm) : Ordinal.{0} :=
  sInf (insert Om1 {l | IsRestartIdx l ∧ X.CB t (upsilon l) ∧ X.val t (upsilon l) ≤ xtOrec X l})

theorem xtLamT_le {t : X.Tm} {l : Ordinal.{0}} (hl : IsRestartIdx l) (hCB : X.CB t (upsilon l))
    (hle : X.val t (upsilon l) ≤ xtOrec X l) : xtLamT X t ≤ l :=
  csInf_le (OrderBot.bddBelow _) (Set.mem_insert_of_mem _ ⟨hl, hCB, hle⟩)

theorem xtLamT_spec {t : X.Tm} (h : xtLamT X t < Om1) :
    IsRestartIdx (xtLamT X t) ∧ X.CB t (upsilon (xtLamT X t)) ∧
      X.val t (upsilon (xtLamT X t)) ≤ xtOrec X (xtLamT X t) := by
  rcases csInf_mem (s := insert Om1
    {l | IsRestartIdx l ∧ X.CB t (upsilon l) ∧ X.val t (upsilon l) ≤ xtOrec X l})
    ⟨Om1, Set.mem_insert _ _⟩ with h' | h'
  · exact absurd (h' ▸ h : Om1 < Om1) (lt_irrefl _)
  · exact h'

theorem lt_xtv_of_lt_LamT {t : X.Tm} {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (hμl : μ < xtLamT X t)
    (hCB : X.CB t (upsilon μ)) : xtOrec X μ < X.val t (upsilon μ) := by
  by_contra hle
  exact absurd (xtLamT_le hμ hCB (not_lt.1 hle)) (not_le.2 hμl)

theorem xt_uni_lt {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : X.Tm}
    (ht : X.CB t σ) (hu : X.CB u σ) : X.val t ρ < X.val u ρ ↔ X.val t σ < X.val u σ := by
  rw [← not_le, ← not_le, X.uni_le σ ρ hσ hρ hB u t hu ht]

/-- **`O(Λ_t) = t(ρ_{Λ_t})`** (for `Λ_t < Ω₁` and `t(ρ_{Λ_t}) ≥ 1`). -/
theorem xtOrec_LamT {t : X.Tm} (hlt : xtLamT X t < Om1) (h1 : 1 ≤ X.val t (upsilon (xtLamT X t))) :
    xtOrec X (xtLamT X t) = X.val t (upsilon (xtLamT X t)) := by
  obtain ⟨hl, hCB, hle⟩ := xtLamT_spec hlt
  set l := xtLamT X t with hldef
  refine le_antisymm ?_ hle
  have hρU := ups_ri hl
  obtain ⟨m0, hm0, hm0c⟩ := list_max (X.cs t) _ (X.cb_cst t _ hCB) hρU.1
  obtain ⟨_, ⟨ν, hν, rfl⟩, hm0ν⟩ := (lt_isLUB_iff (upsilon_limit (ri_limit hl))).1 hm0
  refine xtOrec_le_of h1 (fun s hsCB hc => ?_)
  obtain ⟨μ, hμ, hνμ, hμl, hCBμ, hsμ⟩ := hc ν hν
  have hm0μ : m0 < upsilon μ := hm0ν.trans (upsilon_normal.strictMono hνμ)
  have htμ : X.CB t (upsilon μ) := X.cb_iff t _ _ hCB (fun c hc => lt_of_le_of_lt (hm0c c hc) hm0μ)
  have h2 : X.val s (upsilon μ) < X.val t (upsilon μ) :=
    lt_of_le_of_lt hsμ (lt_xtv_of_lt_LamT hμ hμl htμ)
  exact (xt_uni_lt (ups_ri hμ) hρU (bases_ri hμ hl hμl hlt) hCBμ htμ).2 h2

/-- **`Λ_t < Λ`** for every term `t` with constants below `ρ_Λ` and value `≥ 1` there. -/
theorem xtLamT_lt_Lam {t : X.Tm} (hCB : X.CB t (upsilon (xtLam X))) (h1 : 1 ≤ X.val t (upsilon (xtLam X))) :
    xtLamT X t < xtLam X := by
  have hLt := X.lt_top _ xtLam_ri xtLam_lt_Om1 t hCB
  have hle : xtLamT X t ≤ xtLam X := xtLamT_le xtLam_ri hCB (by rw [xtOrec_Lam]; exact hLt.le)
  refine lt_of_le_of_ne hle (fun e => ?_)
  have hlt : xtLamT X t < Om1 := e ▸ xtLam_lt_Om1
  have h := xtOrec_LamT hlt (by rw [e]; exact h1)
  rw [e, xtOrec_Lam] at h
  exact absurd h hLt.ne'

theorem xtLamT_ri {t : X.Tm} (hCB : X.CB t (upsilon (xtLam X))) (h1 : 1 ≤ X.val t (upsilon (xtLam X))) :
    IsRestartIdx (xtLamT X t) :=
  (xtLamT_spec ((xtLamT_lt_Lam hCB h1).trans xtLam_lt_Om1)).1

theorem one_le_xtv_LamT {t : X.Tm} (hCB : X.CB t (upsilon (xtLam X)))
    (h1 : 1 ≤ X.val t (upsilon (xtLam X))) : 1 ≤ X.val t (upsilon (xtLamT X t)) := by
  have hlt := xtLamT_lt_Lam hCB h1
  obtain ⟨hl, hCBl, -⟩ := xtLamT_spec (hlt.trans xtLam_lt_Om1)
  have hB := bases_ri hl xtLam_ri hlt xtLam_lt_Om1
  have h1' : (1 : Ordinal.{0}) < upsilon (xtLamT X t) := one_lt_of_upsPt (ups_ri hl)
  have hc := X.cb_cstI 1 _ h1'
  have := (X.uni_le _ _ (ups_ri hl) (ups_ri xtLam_ri) hB (X.cst 1) t hc hCBl).1
  rw [X.val_cst, X.val_cst] at this
  exact this h1

/-- **The reach at the frontier of every term**: `lh(ρ_{Λ_t}) = δ + t(ρ_{Λ_t})` in `R₂^C`. -/
theorem xtReach_LamT {t : X.Tm} (hCB : X.CB t (upsilon (xtLam X))) (h1 : 1 ≤ X.val t (upsilon (xtLam X))) :
    IsReach R2C (upsilon (xtLamT X t)) (upsilon (xtLamT X t + ω + 1) + X.val t (upsilon (xtLamT X t))) := by
  rw [← xtOrec_LamT ((xtLamT_lt_Lam hCB h1).trans xtLam_lt_Om1) (one_le_xtv_LamT hCB h1)]
  exact xtReach (xtLamT_ri hCB h1) (xtLamT_lt_Lam hCB h1)

/-! ## Past the frontier: the first limit of frontiers, when the top has an IMG package -/

variable (X) in
/-- **The top has an IMG package** at every restart. -/
def XtTopPkg : Prop :=
  ∀ l, IsRestartIdx l → l < Om1 → RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1)) →
    ImgPkg (upsilon l) (upsilon (l + ω + 1)) X.top

variable (X) in
/-- A **frontier**: a restart index `λ` with `O(λ) = top(ρ_λ)`. -/
def XtFr (l : Ordinal.{0}) : Prop := IsRestartIdx l ∧ xtOrec X l = X.top (upsilon l)

variable (X) in
/-- The frontiers are cofinal below `λ`. -/
def XtFrCof (l : Ordinal.{0}) : Prop := ∀ ν < l, ∃ μ, XtFr X μ ∧ ν < μ ∧ μ < l

variable (X) in
/-- **The first limit of frontiers** (`Ω₁` if there is none). -/
noncomputable def xtB1 : Ordinal.{0} := sInf (insert Om1 {l | 0 < l ∧ XtFrCof X l})

theorem xtB1_le_Om1 : xtB1 X ≤ Om1 := csInf_le (OrderBot.bddBelow _) (Set.mem_insert _ _)

theorem xt_not_cof {l : Ordinal.{0}} (hl0 : 0 < l) (hl : l < xtB1 X) : ¬ XtFrCof X l := fun h =>
  absurd (csInf_le (OrderBot.bddBelow _)
    (Set.mem_insert_of_mem _ (show l ∈ {l | 0 < l ∧ XtFrCof X l} from ⟨hl0, h⟩))) (not_le.2 hl)

/-- **The input of Lemma TOP at every restart index below the first limit of frontiers.** -/
theorem xtTopIn1 (hP : XtTopPkg X) {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1)
    (hlB : l < xtB1 X) : TopInH (xtOrec X) l := by
  rcases (xtOrec_le_top hl hl1).lt_or_eq with hlt | heq
  · exact xtTopIn hl hl1 hlt
  · have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
    have hnc := xt_not_cof hl0 hlB
    have hex : ∃ ν < l, ∀ μ, XtFr X μ → ν < μ → μ < l → False := by
      by_contra hne
      apply hnc
      intro ν hν
      by_contra h2
      exact hne ⟨ν, hν, fun μ hμ h1 h3 => h2 ⟨μ, hμ, h1, h3⟩⟩
    obtain ⟨ν, hνl, hν⟩ := hex
    refine ⟨X.top, upsilon ν, heq, upsilon_normal.strictMono hνl, fun μ hμ hμl hx0 => ?_,
      fun R => hP l hl hl1 R⟩
    have hνμ : ν < μ := upsilon_normal.strictMono.lt_iff_lt.1 hx0
    rcases (xtOrec_le_top hμ (hμl.trans hl1)).lt_or_eq with h | h
    · exact h
    · exact (hν μ ⟨hμ, h⟩ hνμ hμl).elim

theorem xtSpec1_of_le (hP : XtTopPkg X) {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1)
    (hB : B ≤ xtB1 X) : OffSpecGen (xtOrec X) B :=
  xtSpec hm hc (fun _ hl hlB => xtTopIn1 hP hl (hlB.trans hc) (lt_of_lt_of_le hlB hB))

/-- **The first limit of frontiers is countable.** -/
theorem xtB1_lt_Om1 (hP : XtTopPkg X) : xtB1 X < Om1 := by
  rcases xtB1_le_Om1.lt_or_eq with h | h
  · exact h
  · exfalso
    exact not_core_all (fun B hm hc => core_genGen (xtSpec1_of_le hP hm hc (by rw [h]; exact hc.le)))

theorem xtB1_spec (hP : XtTopPkg X) : 0 < xtB1 X ∧ XtFrCof X (xtB1 X) := by
  have hne : (insert Om1 {l | 0 < l ∧ XtFrCof X l}).Nonempty := ⟨_, Set.mem_insert _ _⟩
  rcases csInf_mem hne with h | h
  · exact absurd h (ne_of_lt (xtB1_lt_Om1 hP))
  · exact h

/-- A point below which multiples of `ω²` are cofinal is a multiple of `ω²`. -/
theorem xt_ww_dvd_of_cof {l : Ordinal.{0}} (h : ∀ ν < l, ∃ μ, ω * ω ∣ μ ∧ ν < μ ∧ μ < l) :
    ω * ω ∣ l := by
  have hww : (0 : Ordinal.{0}) < ω * ω := mul_pos omega0_pos omega0_pos
  by_contra hnd
  have hr : l % (ω * ω) ≠ 0 := fun h0 => hnd (dvd_iff_mod_eq_zero.2 h0)
  have e := div_add_mod l (ω * ω)
  have hlt : ω * ω * (l / (ω * ω)) < l := by
    conv_rhs => rw [← e]
    exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 hr)
  obtain ⟨μ, ⟨k, rfl⟩, h1, h2⟩ := h _ hlt
  have hqk : l / (ω * ω) < k := (mul_lt_mul_iff_right₀ hww).1 h1
  have hle : ω * ω * (l / (ω * ω) + 1) ≤ ω * ω * k := mul_le_mul_right (Order.add_one_le_of_lt hqk) _
  rw [mul_add_one] at hle
  have hm : l % (ω * ω) < ω * ω := mod_lt l hww.ne'
  have hl2 : l < ω * ω * (l / (ω * ω)) + ω * ω := by
    conv_lhs => rw [← e]
    exact (add_lt_add_iff_left _).2 hm
  exact absurd (h2.trans hl2) (not_lt.2 hle)

theorem xtB1_mult (hP : XtTopPkg X) : ω * ω ∣ xtB1 X := by
  refine xt_ww_dvd_of_cof fun ν hν => ?_
  obtain ⟨μ, hμ, h1, h2⟩ := (xtB1_spec hP).2 ν hν
  exact ⟨μ, (ri_iff.1 hμ.1).2, h1, h2⟩

/-- **The offset is a general specification up to the first limit of frontiers.** -/
theorem xtSpec1 (hP : XtTopPkg X) : OffSpecGen (xtOrec X) (xtB1 X) :=
  xtSpec1_of_le hP (xtB1_mult hP) (xtB1_lt_Om1 hP) le_rfl

/-- **The exact reach of every restart below the first limit of frontiers.** -/
theorem xtReach1 (hP : XtTopPkg X) {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < xtB1 X) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec X l) :=
  reach_allGen (xtSpec1 hP) hl hlB

/-- **Theorem BLK^O below `υ_{xtB1}`**. -/
theorem xtBlk1 (hP : XtTopPkg X) :
    (∀ c d, c < d → d < upsilon (xtB1 X) → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 X ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 X →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec X l)) ∧
    (∀ α < upsilon (xtB1 X), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  blk_genGen (xtSpec1 hP)

end Googology.Trans.PoR.InaccPsi.R2.Xt

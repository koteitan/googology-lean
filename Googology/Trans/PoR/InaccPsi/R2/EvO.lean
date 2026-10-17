import Googology.Trans.PoR.InaccPsi.R2.EvI

/-!
# The recursive offset below `ε_{x+x}`, Theorem BLK^O up to the block of `Λ_{ε_{x+x}}`, and the reach at every
frontier `Λ_t`

The project's recursive offset (its paper's Definition 2.2) over the terms `TEv` (every Cantor normal form in `x`
and the `ε_{x+c}`, `c` a constant, below `ε_{x+x}`).  `OrecEv(λ) = sup ({1} ∪ {s(ρ_λ) + 1 : s realized cofinally
below λ, constants below ρ_λ})`.  The proofs are those of `R2.EpsO` with `TEv`, `ε_{x+x}`, `RstK.pkgV` (Lemma
IMG below `ε_{ρ+ρ}`), `rsStep_V` (Lemma RS) in place of `TW`, `ε_{x+ω}`, `RstK.pkgT`, `rsStep_W`; the block of
`Λ_{ε_{x+x}}` itself is covered by the IMG package of `ε_{x+x}` (`RstK.pkgAA`).

* `OrecEv`, `OrecEv_le` (`OrecEv(λ) ≤ ε_{ρ+ρ}`), `OrecEv_succ`, `LamEv` (`Λ_{ε_{x+x}}`), `topIn_OrecEv`,
  `rsIn_OrecEv`, `specEv`;
* `blkEv` (**BLK^O with `OrecEv` below `υ_B` for every `B ≤ Λ_{ε_{x+x}}`**), `coreEv`, `LamEv_lt_Om1`,
  `reach_OrecEv`, `OrecEv_LamEv`; `topIn_LamEv`, `specEv2`, `blkEv2` (**BLK^O below `υ_{Λ_{ε_{x+x}}+ω²}`**),
  `coreEv2`, `reach_LamEv` (**`lh(ρ_{Λ_{ε_{x+x}}}) = δ + ε_{ρ+ρ}`**);
* `OrecEv_eq_OrecW`, `LamW_lt_LamEv`, `OrecEv_LamW`;
* `LamTEv t` (**the frontier of a term `t`**), `OrecEv_LamTEv'` (**`OrecEv(Λ_t) = t(ρ_{Λ_t})`**),
  `LamTEv_lt_LamEv`, `reach_LamTEv` (**the reach at every frontier**: `lh(ρ_{Λ_t}) = δ + t(ρ_{Λ_t})`),
  `blk_LamTEv`, `LamTEv_mono`, `LamTEv_strict`;
* the frontiers of `ε_{x+c}`: `LamTEv_ec_lt` (`Λ_{ε_{x+c}} < Λ_{ε_{x+c'}}` for `c < c'`), `reach_LamEc`
  (`lh(ρ) = δ + ε_{ρ+c}` at `Λ_{ε_{x+c}}`), `LamTEv_ecw` (`Λ_{ε_{x+ω}}` of `OrecEv` is `LamW`);
* `nuC_boundEv` (**`υ_{Λ_{ε_{x+x}}+ω²} ≤ ρ_L < ν_C`**).

No new axiom.

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order TEv

/-! ## The recursion -/

/-- `s` is realized cofinally below `λ` by the offsets `O`. -/
def CofRealEv (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) (s : TEv) : Prop :=
  ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ CBv s (upsilon μ) ∧ val s (upsilon μ) ≤ O μ

/-- The set whose supremum is `OrecEv(λ)`. -/
def OSetEv (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : Set Ordinal.{0} :=
  insert 1 {w | ∃ s, CBv s (upsilon l) ∧ CofRealEv O l s ∧ w = val s (upsilon l) + 1}

theorem OSetEv_congr {O O' : Ordinal.{0} → Ordinal.{0}} {l : Ordinal.{0}}
    (h : ∀ μ < l, O μ = O' μ) : OSetEv O l = OSetEv O' l := by
  have key : ∀ s, CofRealEv O l s ↔ CofRealEv O' l s := by
    intro s
    constructor
    · intro hc ν hν
      obtain ⟨μ, h1, h2, h3, h4, h5⟩ := hc ν hν
      exact ⟨μ, h1, h2, h3, h4, by rw [← h μ h3]; exact h5⟩
    · intro hc ν hν
      obtain ⟨μ, h1, h2, h3, h4, h5⟩ := hc ν hν
      exact ⟨μ, h1, h2, h3, h4, by rw [h μ h3]; exact h5⟩
  ext w
  simp only [OSetEv, Set.mem_insert_iff, Set.mem_setOf_eq, key]

/-- **The recursive offset over `TEv`**, by well-founded recursion. -/
noncomputable def OrecEv : Ordinal.{0} → Ordinal.{0} :=
  Ordinal.lt_wf.fix (fun l IH => sSup (OSetEv (fun μ => if h : μ < l then IH μ h else 0) l))

theorem OrecEv_eq (l : Ordinal.{0}) : OrecEv l = sSup (OSetEv OrecEv l) := by
  show Ordinal.lt_wf.fix _ l = _
  rw [WellFounded.fix_eq]
  rw [OSetEv_congr (O' := OrecEv) (fun μ hμ => by simp only [hμ, dite_true]; rfl)]

theorem OSetEv_bdd (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) (hl : InE (upsilon l)) :
    ∀ w ∈ OSetEv O l, w ≤ evA (upsilon l) (upsilon l) := by
  intro w hw
  rcases hw with rfl | ⟨s, hCB, -, rfl⟩
  · exact (one_le_iff_pos.2 hl.pos).trans (le_evA hl _)
  · exact add_one_le_of_lt (valV_lt_AA hl hCB)

theorem OSetEv_bddAbove (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) (hl : InE (upsilon l)) :
    BddAbove (OSetEv O l) := ⟨_, OSetEv_bdd O l hl⟩

/-- `OrecEv(λ) ≤ ε_{ρ+ρ}`. -/
theorem OrecEv_le {l : Ordinal.{0}} (hl : IsRestartIdx l) :
    OrecEv l ≤ evA (upsilon l) (upsilon l) := by
  rw [OrecEv_eq]; exact csSup_le ⟨1, Set.mem_insert _ _⟩ (OSetEv_bdd _ l (ups_inE hl))

theorem one_le_OrecEv {l : Ordinal.{0}} (hl : IsRestartIdx l) : 1 ≤ OrecEv l := by
  rw [OrecEv_eq]; exact le_csSup (OSetEv_bddAbove _ l (ups_inE hl)) (Set.mem_insert _ _)

theorem lt_OrecEv_of_cof {l : Ordinal.{0}} (hl : IsRestartIdx l) {s : TEv} (hCB : CBv s (upsilon l))
    (hc : CofRealEv OrecEv l s) : val s (upsilon l) < OrecEv l := by
  have h1 : val s (upsilon l) + 1 ≤ OrecEv l := by
    rw [OrecEv_eq]
    exact le_csSup (OSetEv_bddAbove _ l (ups_inE hl)) (Set.mem_insert_of_mem _ ⟨s, hCB, hc, rfl⟩)
  exact lt_of_lt_of_le (lt_add_one _) h1

theorem lt_OrecEv {l z : Ordinal.{0}} (hl : IsRestartIdx l) (hz : z < OrecEv l) :
    z = 0 ∨ ∃ s, CBv s (upsilon l) ∧ CofRealEv OrecEv l s ∧ z ≤ val s (upsilon l) := by
  rw [OrecEv_eq] at hz
  obtain ⟨w, hw, hzw⟩ :=
    (lt_csSup_iff (OSetEv_bddAbove _ l (ups_inE hl)) ⟨1, Set.mem_insert _ _⟩).1 hz
  rcases hw with rfl | ⟨s, hCB, hc, rfl⟩
  · left; exact le_antisymm (Order.lt_add_one_iff.1 (by rw [zero_add]; exact hzw)) zero_le
  · right; exact ⟨s, hCB, hc, Order.lt_add_one_iff.1 hzw⟩

/-- `OrecEv = 1` at a successor restart index. -/
theorem OrecEv_succ {l : Ordinal.{0}} (hl : IsRestartIdx l) (h2 : cL l < 2) : OrecEv l = 1 := by
  obtain ⟨l0, hl0, rfl⟩ := succ_ri hl h2
  have hww : 0 < ω * ω := mul_pos omega0_pos omega0_pos
  have hS : OSetEv OrecEv (l0 + ω * ω) = {1} := by
    ext w
    simp only [OSetEv, Set.mem_insert_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro (h | ⟨s, -, hc, -⟩)
      · exact h
      · exfalso
        obtain ⟨μ, hμ, h1, h3, -, -⟩ := hc l0 (lt_add_of_pos_right l0 hww)
        exact absurd h3 (not_lt.2 (next_mult (mult_of hl0) (ri_iff.1 hμ).2 h1))
    · intro h; exact Or.inl h
  rw [OrecEv_eq, hS, csSup_singleton]

/-! ## The frontier `Λ_{ε_{x+x}}` -/

/-- `Λ_{ε_{x+x}}`: the least restart index `λ` with `OrecEv(λ) = ε_{ρ_λ+ρ_λ}` (`Ω₁` if there is none). -/
noncomputable def LamEv : Ordinal.{0} :=
  sInf (insert Om1 {l | IsRestartIdx l ∧ OrecEv l = evA (upsilon l) (upsilon l)})

theorem LamEv_le_Om1 : LamEv ≤ Om1 := csInf_le (OrderBot.bddBelow _) (Set.mem_insert _ _)

/-- **Below `Λ_{ε_{x+x}}` the value is `< ε_{ρ+ρ}`.** -/
theorem OrecEv_lt_top {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlV : l < LamEv) :
    OrecEv l < evA (upsilon l) (upsilon l) := by
  rcases (OrecEv_le hl).lt_or_eq with h | h
  · exact h
  · exact absurd (csInf_le (OrderBot.bddBelow _) (Set.mem_insert_of_mem _
      (show l ∈ {l | IsRestartIdx l ∧ OrecEv l = evA (upsilon l) (upsilon l)} from ⟨hl, h⟩)))
      (not_le.2 hlV)

theorem LamEv_spec (h : LamEv < Om1) :
    IsRestartIdx LamEv ∧ OrecEv LamEv = evA (upsilon LamEv) (upsilon LamEv) := by
  rcases csInf_mem (s := insert Om1 {l | IsRestartIdx l ∧ OrecEv l = evA (upsilon l) (upsilon l)})
    ⟨Om1, Set.mem_insert _ _⟩ with h' | h'
  · exact absurd (h' ▸ h : Om1 < Om1) (lt_irrefl _)
  · exact h'

/-! ## The inputs of Lemmas TOP and RS -/

/-- **The input of Lemma TOP** at a restart index `λ` with `OrecEv(λ) < ε_{ρ+ρ}`. -/
theorem topIn_OrecEv {l : Ordinal.{0}} (hl : IsRestartIdx l)
    (hlt : OrecEv l < evA (upsilon l) (upsilon l)) : TopInH OrecEv l := by
  classical
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρU := upsPt_upsilon hl0
  have hρE : InE (upsilon l) := upsPt_inE hρU
  have hone : 1 ≤ OrecEv l := one_le_OrecEv hl
  obtain ⟨s, hCB, hev⟩ := repV hρE _ hlt
  have hpk : RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1)) →
      ImgPkg (upsilon l) (upsilon (l + ω + 1)) (val s) := fun R =>
    R.pkgV hCB (by rw [hev]; exact hone)
  have hnot : ¬ CofRealEv OrecEv l s := fun hc =>
    absurd (lt_OrecEv_of_cof hl hCB hc) (by rw [hev]; exact lt_irrefl _)
  obtain ⟨m0, hm0, hm0c⟩ := list_max (csv s) _ ((cbv_iff s _).1 hCB) hρU.1
  unfold CofRealEv at hnot
  push Not at hnot
  obtain ⟨ν, hνl, hν⟩ := hnot
  have hνρ : upsilon ν < upsilon l := upsilon_normal.strictMono hνl
  refine ⟨val s, max (upsilon ν) m0, hev.symm, max_lt hνρ hm0, fun μ hμ hμl hx0 => ?_, hpk⟩
  have hνμ : ν < μ := upsilon_normal.strictMono.lt_iff_lt.1 (lt_of_le_of_lt (le_max_left _ _) hx0)
  have hCBμ : CBv s (upsilon μ) :=
    (cbv_iff s _).2 (fun c hc => lt_of_le_of_lt ((hm0c c hc).trans (le_max_right _ _)) hx0)
  exact hν μ hμ hνμ hμl hCBμ

/-- **The input of Lemma RS at a limit restart index `λ`** for `OrecEv`. -/
theorem rsIn_OrecEv {l : Ordinal.{0}} (hl : IsRestartIdx l) (h2 : 2 ≤ cL l) : RsInGen OrecEv l := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρ0 : 0 < upsilon l := (upsPt_upsilon hl0).1
  intro z hz
  rcases lt_OrecEv hl hz with rfl | ⟨s, hCB, hc, hzs⟩
  · refine ⟨OT.ev (OT.k 0), zero_le, fun R htg => rs_rstT R hρ0 htg, fun ν hν => ?_⟩
    obtain ⟨μ, hμ, h1, h3, -⟩ := cL_dense hl le_rfl (lt_of_lt_of_le one_lt_two h2) ν hν
    exact ⟨μ, hμ, h1, h3, by rw [OT.ev_k]; exact zero_le⟩
  · refine ⟨val s, hzs, rsStep_V hl0 hCB, fun ν hν => ?_⟩
    obtain ⟨μ, hμ, h1, h3, -, h5⟩ := hc ν hν
    exact ⟨μ, hμ, h1, h3, h5⟩

theorem OrecEv_lt_δ {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) :
    OrecEv l < upsilon (l + ω + 1) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρU := upsPt_upsilon hl0
  have h1 : l < l + ω := lt_add_of_pos_right l omega0_pos
  have hτU := upsPt_upsilon (hl0.trans h1)
  exact lt_of_le_of_lt (OrecEv_le hl) ((evA_lt_ups (upsPt_inE hρU) (ups_lt_Om1 l hl1) le_rfl
    (upsilon_normal.strictMono h1) hτU).trans (upsilon_normal.strictMono (lt_add_one _)))

/-- **`OrecEv` is a general offset specification up to `B`** when every restart index below `B` has
`OrecEv < ε_{ρ+ρ}`, except possibly `Λ_{ε_{x+x}}` itself. -/
theorem specEv {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1)
    (hB : ∀ l, IsRestartIdx l → l < B → TopInH OrecEv l) : OffSpecGen OrecEv B where
  mult := hm
  cnt := hc
  le := fun _ hl hlB => OrecEv_lt_δ hl (hlB.trans hc)
  one := fun _ hl _ => one_le_OrecEv hl
  top := hB
  succ := fun _ hl _ h2 => OrecEv_succ hl h2
  rs := fun _ hl _ h2 => rsIn_OrecEv hl h2

theorem specEv_of_le {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ LamEv) :
    OffSpecGen OrecEv B :=
  specEv hm hc (fun _ hl hlB => topIn_OrecEv hl (OrecEv_lt_top hl (lt_of_lt_of_le hlB hB)))

/-! ## Theorem BLK^O up to `Λ_{ε_{x+x}}` -/

/-- **Theorem BLK^O with `OrecEv` below `υ_B` for every `B ≤ Λ_{ε_{x+x}}`** (`ω² ∣ B`, `B < Ω₁`) in `R₂^C`. -/
theorem blkEv {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ LamEv) :
    (∀ c d, c < d → d < upsilon B → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < B ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < B →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + OrecEv l)) ∧
    (∀ α < upsilon B, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  blk_genGen (specEv_of_le hm hc hB)

/-- **CORE-C up to `Λ_{ε_{x+x}}`**. -/
theorem coreEv {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ LamEv) :
    Set.Iio (upsilon B) ⊆ Core R2C :=
  core_genGen (specEv_of_le hm hc hB)

/-- **`Λ_{ε_{x+x}} < Ω₁`** (the core is countable, [C09] Cor 15.15). -/
theorem LamEv_lt_Om1 : LamEv < Om1 := by
  rcases LamEv_le_Om1.lt_or_eq with h | h
  · exact h
  · exfalso
    exact not_core_all (fun B hm hc => coreEv hm hc (by rw [h]; exact hc.le))

theorem LamEv_ri : IsRestartIdx LamEv := (LamEv_spec LamEv_lt_Om1).1

/-- **`OrecEv(Λ_{ε_{x+x}}) = ε_{ρ+ρ}`**. -/
theorem OrecEv_LamEv : OrecEv LamEv = evA (upsilon LamEv) (upsilon LamEv) := (LamEv_spec LamEv_lt_Om1).2

/-- **The exact reach of every restart below `Λ_{ε_{x+x}}`**: `lh(ρ_λ) = δ_λ + OrecEv(λ)`. -/
theorem reach_OrecEv {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlV : l < LamEv) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + OrecEv l) :=
  (blkEv (ri_iff.1 LamEv_ri).2 LamEv_lt_Om1 le_rfl).2.1 l hl hlV |>.2.2

/-! ## The block of `Λ_{ε_{x+x}}` -/

/-- **The input of Lemma TOP at `Λ_{ε_{x+x}}`** with the term `ε_{x+x}` (`RstK.pkgAA`). -/
theorem topIn_LamEv : TopInH OrecEv LamEv :=
  ⟨fun x => evA x x, 0, OrecEv_LamEv, (ups_ri LamEv_ri).1, fun _ hμ hμl _ => OrecEv_lt_top hμ hμl,
    fun R => R.pkgAA⟩

/-- **`OrecEv` is a general offset specification up to `Λ_{ε_{x+x}} + ω²`.** -/
theorem specEv2 : OffSpecGen OrecEv (LamEv + ω * ω) :=
  specEv (dvd_add (ri_iff.1 LamEv_ri).2 (dvd_refl _)) (Om1_add_lt LamEv_lt_Om1 ww_lt_Om1)
    (fun l hl hlB => by
      rcases lt_trichotomy l LamEv with hlt | rfl | hgt
      · exact topIn_OrecEv hl (OrecEv_lt_top hl hlt)
      · exact topIn_LamEv
      · exact absurd hlB (not_lt.2 (next_mult (ri_iff.1 LamEv_ri).2 (ri_iff.1 hl).2 hgt)))

/-- **Theorem BLK^O with `OrecEv` below `υ_{Λ_{ε_{x+x}}+ω²}`** (the block of `ρ_{Λ_{ε_{x+x}}}` included). -/
theorem blkEv2 :
    (∀ c d, c < d → d < upsilon (LamEv + ω * ω) → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < LamEv + ω * ω ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < LamEv + ω * ω →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + OrecEv l)) ∧
    (∀ α < upsilon (LamEv + ω * ω), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  blk_genGen specEv2

theorem coreEv2 : Set.Iio (upsilon (LamEv + ω * ω)) ⊆ Core R2C := core_genGen specEv2

/-- **The reach at `Λ_{ε_{x+x}}`**: `lh(ρ) = δ + ε_{ρ+ρ}` for `ρ = ρ_{Λ_{ε_{x+x}}}`. -/
theorem reach_LamEv :
    IsReach R2C (upsilon LamEv) (upsilon (LamEv + ω + 1) + evA (upsilon LamEv) (upsilon LamEv)) := by
  have := (blkEv2.2.1 LamEv LamEv_ri (lt_add_of_pos_right _ (mul_pos omega0_pos omega0_pos))).2.2
  rwa [OrecEv_LamEv] at this

/-! ## Comparing with `OrecW` -/

/-- **`OrecEv = OrecW` below both frontiers** (the reach is unique). -/
theorem OrecEv_eq_OrecW {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlV : l < LamEv) (hlW : l < LamW) :
    OrecEv l = OrecW l :=
  (add_left_cancel_iff).1 (isReach_unique (reach_OrecEv hl hlV) (reach_OrecW hl hlW))

/-- **`Λ_{ε_{x+ω}} < Λ_{ε_{x+x}}`**. -/
theorem LamW_lt_LamEv : LamW < LamEv := by
  by_contra hle
  push Not at hle
  have hl := LamEv_ri
  have hρU := ups_ri hl
  have hρE := ups_inE hl
  have hωρ : ω < upsilon LamEv := omega0_lt_inE hρE
  have hz : eW (upsilon LamEv) < OrecEv LamEv := by
    rw [OrecEv_LamEv, ← evA_eW hρE]; exact evA_lt_iff.2 hωρ
  rcases lt_OrecEv hl hz with h0 | ⟨s, hCB, hcs, hzs⟩
  · exact absurd h0 (lt_of_lt_of_le (eK_E_succ 0 _).pos (eK_le_eW 1 _)).ne'
  obtain ⟨μ, hμ, -, hμl, h3, h4⟩ := hcs 0 (pos_iff_ne_zero.2 hl.1)
  have hμW : μ < LamW := lt_of_lt_of_le hμl hle
  rw [OrecEv_eq_OrecW hμ hμl hμW] at h4
  have hμE := ups_inE hμ
  have h5 : val s (upsilon μ) < evA (upsilon μ) ω := by
    rw [evA_eW hμE]; exact lt_of_le_of_lt h4 (OrecW_lt_top hμ hμW)
  have h6 := (uniV_lt (t := s) (u := ec ω) (ups_ri hμ) hρU (bases_ri hμ hl hμl LamEv_lt_Om1) h3
    (omega0_lt_inE hμE)).2 h5
  rw [val_ec, evA_eW hρE] at h6
  exact absurd hzs (not_le.2 h6)

/-- **`OrecEv(Λ_{ε_{x+ω}}) = ε_{ρ+ω} = OrecW(Λ_{ε_{x+ω}})`**. -/
theorem OrecEv_LamW : OrecEv LamW = eW (upsilon LamW) :=
  (add_left_cancel_iff).1 (isReach_unique (reach_OrecEv LamW_ri LamW_lt_LamEv) reach_LamW)

/-! ## The frontier of a term -/

/-- **The frontier `Λ_t` of a term `t` of `TEv`**: the least restart index `λ` with constants of `t` below
`ρ_λ` and `t(ρ_λ) ≤ OrecEv(λ)` (`Ω₁` if there is none). -/
noncomputable def LamTEv (t : TEv) : Ordinal.{0} :=
  sInf (insert Om1 {l | IsRestartIdx l ∧ CBv t (upsilon l) ∧ val t (upsilon l) ≤ OrecEv l})

theorem LamTEv_le {t : TEv} {l : Ordinal.{0}} (hl : IsRestartIdx l) (hCB : CBv t (upsilon l))
    (hle : val t (upsilon l) ≤ OrecEv l) : LamTEv t ≤ l :=
  csInf_le (OrderBot.bddBelow _) (Set.mem_insert_of_mem _ ⟨hl, hCB, hle⟩)

theorem LamTEv_spec {t : TEv} (h : LamTEv t < Om1) :
    IsRestartIdx (LamTEv t) ∧ CBv t (upsilon (LamTEv t)) ∧ val t (upsilon (LamTEv t)) ≤ OrecEv (LamTEv t) := by
  rcases csInf_mem (s := insert Om1
    {l | IsRestartIdx l ∧ CBv t (upsilon l) ∧ val t (upsilon l) ≤ OrecEv l})
    ⟨Om1, Set.mem_insert _ _⟩ with h' | h'
  · exact absurd (h' ▸ h : Om1 < Om1) (lt_irrefl _)
  · exact h'

theorem lt_valV_of_lt_LamTEv {t : TEv} {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (hμl : μ < LamTEv t)
    (hCB : CBv t (upsilon μ)) : OrecEv μ < val t (upsilon μ) := by
  by_contra hle
  exact absurd (LamTEv_le hμ hCB (not_lt.1 hle)) (not_le.2 hμl)

/-- **`OrecEv(Λ_t) = t(ρ_{Λ_t})`** (for `Λ_t < Ω₁` and `t(ρ_{Λ_t}) ≥ 1`). -/
theorem OrecEv_LamTEv {t : TEv} (hlt : LamTEv t < Om1) (h1 : 1 ≤ val t (upsilon (LamTEv t))) :
    OrecEv (LamTEv t) = val t (upsilon (LamTEv t)) := by
  obtain ⟨hl, hCB, hle⟩ := LamTEv_spec hlt
  set l := LamTEv t with hldef
  refine le_antisymm ?_ hle
  have hρU := ups_ri hl
  obtain ⟨m0, hm0, hm0c⟩ := list_max (csv t) _ ((cbv_iff t _).1 hCB) hρU.1
  obtain ⟨_, ⟨ν, hν, rfl⟩, hm0ν⟩ := (lt_isLUB_iff (upsilon_limit (ri_limit hl))).1 hm0
  rw [OrecEv_eq]
  refine csSup_le ⟨1, Set.mem_insert _ _⟩ ?_
  rintro w (rfl | ⟨s, hsCB, hc, rfl⟩)
  · exact h1
  obtain ⟨μ, hμ, hνμ, hμl, hCBμ, hsμ⟩ := hc ν hν
  have hm0μ : m0 < upsilon μ := hm0ν.trans (upsilon_normal.strictMono hνμ)
  have htμ : CBv t (upsilon μ) := (cbv_iff t _).2 (fun c hc => lt_of_le_of_lt (hm0c c hc) hm0μ)
  have h2 : val s (upsilon μ) < val t (upsilon μ) :=
    lt_of_le_of_lt hsμ (lt_valV_of_lt_LamTEv hμ hμl htμ)
  have h3 := (uniV_lt (ups_ri hμ) hρU (bases_ri hμ hl hμl hlt) hCBμ htμ).2 h2
  exact add_one_le_of_lt h3

/-- **`Λ_t < Λ_{ε_{x+x}}`** for every term `t` with constants below `ρ_{Λ_{ε_{x+x}}}` and value `≥ 1`. -/
theorem LamTEv_lt_LamEv {t : TEv} (hCB : CBv t (upsilon LamEv)) (h1 : 1 ≤ val t (upsilon LamEv)) :
    LamTEv t < LamEv := by
  have hle : LamTEv t ≤ LamEv := LamTEv_le LamEv_ri hCB (by
    rw [OrecEv_LamEv]; exact (valV_lt_AA (ups_inE LamEv_ri) hCB).le)
  refine lt_of_le_of_ne hle (fun e => ?_)
  have hlt : LamTEv t < Om1 := e ▸ LamEv_lt_Om1
  have h := OrecEv_LamTEv hlt (by rw [e]; exact h1)
  rw [e, OrecEv_LamEv] at h
  exact absurd h (valV_lt_AA (ups_inE LamEv_ri) hCB).ne'

theorem LamTEv_ri {t : TEv} (hCB : CBv t (upsilon LamEv)) (h1 : 1 ≤ val t (upsilon LamEv)) :
    IsRestartIdx (LamTEv t) :=
  (LamTEv_spec ((LamTEv_lt_LamEv hCB h1).trans LamEv_lt_Om1)).1

theorem one_le_valV_LamTEv {t : TEv} (hCB : CBv t (upsilon LamEv)) (h1 : 1 ≤ val t (upsilon LamEv)) :
    1 ≤ val t (upsilon (LamTEv t)) := by
  have hlt := LamTEv_lt_LamEv hCB h1
  obtain ⟨hl, hCBl, -⟩ := LamTEv_spec (hlt.trans LamEv_lt_Om1)
  have hB := bases_ri hl LamEv_ri hlt LamEv_lt_Om1
  have h1' : (1 : Ordinal.{0}) < upsilon (LamTEv t) := one_lt_of_upsPt (ups_ri hl)
  exact (uniV_le (t := cst 1) (u := t) (ups_ri hl) (ups_ri LamEv_ri) hB h1' hCBl).1 h1

/-- **`OrecEv(Λ_t) = t(ρ_{Λ_t})`** for every term with constants below `ρ_{Λ_{ε_{x+x}}}` and value `≥ 1`. -/
theorem OrecEv_LamTEv' {t : TEv} (hCB : CBv t (upsilon LamEv)) (h1 : 1 ≤ val t (upsilon LamEv)) :
    OrecEv (LamTEv t) = val t (upsilon (LamTEv t)) :=
  OrecEv_LamTEv ((LamTEv_lt_LamEv hCB h1).trans LamEv_lt_Om1) (one_le_valV_LamTEv hCB h1)

/-- **The reach at the frontier of every term**: `lh(ρ_{Λ_t}) = δ + t(ρ_{Λ_t})` in `R₂^C`. -/
theorem reach_LamTEv {t : TEv} (hCB : CBv t (upsilon LamEv)) (h1 : 1 ≤ val t (upsilon LamEv)) :
    IsReach R2C (upsilon (LamTEv t)) (upsilon (LamTEv t + ω + 1) + val t (upsilon (LamTEv t))) := by
  rw [← OrecEv_LamTEv' hCB h1]
  exact reach_OrecEv (LamTEv_ri hCB h1) (LamTEv_lt_LamEv hCB h1)

theorem LamTEv_ww_le {t : TEv} (hCB : CBv t (upsilon LamEv)) (h1 : 1 ≤ val t (upsilon LamEv)) :
    LamTEv t + ω * ω ≤ LamEv :=
  next_mult (ri_iff.1 (LamTEv_ri hCB h1)).2 (ri_iff.1 LamEv_ri).2 (LamTEv_lt_LamEv hCB h1)

/-- **Theorem BLK^O at the frontier of every term**: BLK^O with `OrecEv` below `υ_{Λ_t+ω²}`. -/
theorem blk_LamTEv {t : TEv} (hCB : CBv t (upsilon LamEv)) (h1 : 1 ≤ val t (upsilon LamEv)) :
    (∀ c d, c < d → d < upsilon (LamTEv t + ω * ω) → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < LamTEv t + ω * ω ∧
      c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < LamTEv t + ω * ω →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + OrecEv l)) ∧
    (∀ α < upsilon (LamTEv t + ω * ω), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  blkEv (dvd_add (ri_iff.1 (LamTEv_ri hCB h1)).2 (dvd_refl _))
    ((LamTEv_ww_le hCB h1).trans_lt LamEv_lt_Om1) (LamTEv_ww_le hCB h1)

/-- **Monotonicity of the frontier**: `t ≤ t'` at `ρ_{Λ_{ε_{x+x}}}` gives `Λ_t ≤ Λ_{t'}`. -/
theorem LamTEv_mono {t t' : TEv} (hCB' : CBv t' (upsilon LamEv))
    (h1 : 1 ≤ val t (upsilon LamEv)) (hle : val t (upsilon LamEv) ≤ val t' (upsilon LamEv))
    (hc : CBv t (upsilon (LamTEv t'))) : LamTEv t ≤ LamTEv t' := by
  have h1' : 1 ≤ val t' (upsilon LamEv) := h1.trans hle
  have hlt' := LamTEv_lt_LamEv hCB' h1'
  obtain ⟨hl', hCBl', hle'⟩ := LamTEv_spec (hlt'.trans LamEv_lt_Om1)
  have hB := bases_ri hl' LamEv_ri hlt' LamEv_lt_Om1
  have hle2 := (uniV_le (ups_ri hl') (ups_ri LamEv_ri) hB hc hCBl').1 hle
  exact LamTEv_le hl' hc (hle2.trans hle')

/-- `t < t'` at `ρ_{Λ_{ε_{x+x}}}` gives `Λ_t < Λ_{t'}`. -/
theorem LamTEv_strict {t t' : TEv} (hCB : CBv t (upsilon LamEv)) (hCB' : CBv t' (upsilon LamEv))
    (h1 : 1 ≤ val t (upsilon LamEv)) (hlt : val t (upsilon LamEv) < val t' (upsilon LamEv))
    (hc : CBv t (upsilon (LamTEv t'))) : LamTEv t < LamTEv t' := by
  refine lt_of_le_of_ne (LamTEv_mono hCB' h1 hlt.le hc) (fun e => ?_)
  have h1' : 1 ≤ val t' (upsilon LamEv) := h1.trans hlt.le
  have hl' := LamTEv_lt_LamEv hCB' h1'
  obtain ⟨hlr, hCBl', hle'⟩ := LamTEv_spec (hl'.trans LamEv_lt_Om1)
  have hB := bases_ri hlr LamEv_ri hl' LamEv_lt_Om1
  have h2 := (uniV_lt (ups_ri hlr) (ups_ri LamEv_ri) hB hc hCBl').1 hlt
  have h3 := OrecEv_LamTEv' hCB h1
  rw [e] at h3
  rw [h3] at hle'
  exact absurd hle' (not_le.2 h2)

/-! ## The frontiers of `ε_{x+c}` -/

theorem one_le_evA_ups {l c : Ordinal.{0}} (hl : IsRestartIdx l) : 1 ≤ evA (upsilon l) c :=
  (one_le_iff_pos.2 (ups_ri hl).1).trans (le_evA (ups_inE hl) c)

/-- **`Λ_{ε_{x+c}} < Λ_{ε_{x+c'}}`** for constants `c < c'` (`c` below `ρ_{Λ_{ε_{x+c'}}}`). -/
theorem LamTEv_ec_lt {c c' : Ordinal.{0}} (hcc' : c < c') (hc' : c' < upsilon LamEv)
    (hc : c < upsilon (LamTEv (ec c'))) : LamTEv (ec c) < LamTEv (ec c') :=
  LamTEv_strict (hcc'.trans hc') hc' (one_le_evA_ups LamEv_ri) (evA_lt_iff.2 hcc') hc

/-- **The reach at `Λ_{ε_{x+c}}`** (`c` a constant below `ρ_{Λ_{ε_{x+x}}}`): `lh(ρ) = δ + ε_{ρ+c}` for
`ρ = ρ_{Λ_{ε_{x+c}}}`, and `Λ_{ε_{x+c}} < Λ_{ε_{x+x}}`. -/
theorem reach_LamEc {c : Ordinal.{0}} (hc : c < upsilon LamEv) :
    IsReach R2C (upsilon (LamTEv (ec c)))
      (upsilon (LamTEv (ec c) + ω + 1) + evA (upsilon (LamTEv (ec c))) c) ∧
      OrecEv (LamTEv (ec c)) = evA (upsilon (LamTEv (ec c))) c ∧ LamTEv (ec c) < LamEv :=
  ⟨reach_LamTEv hc (one_le_evA_ups LamEv_ri), OrecEv_LamTEv' hc (one_le_evA_ups LamEv_ri),
    LamTEv_lt_LamEv hc (one_le_evA_ups LamEv_ri)⟩

/-- **`Λ_{ε_{x+ω}}` of `OrecEv` is `LamW`.** -/
theorem LamTEv_ecw : LamTEv (ec ω) = LamW := by
  have hW := LamW_ri
  have hωW : ω < upsilon LamW := omega0_lt_inE (ups_inE hW)
  refine le_antisymm (LamTEv_le hW hωW (by rw [val_ec, evA_eW (ups_inE hW), OrecEv_LamW])) ?_
  by_contra hlt
  push Not at hlt
  have hV := LamTEv_lt_LamEv (t := ec ω) (omega0_lt_inE (ups_inE LamEv_ri)) (one_le_evA_ups LamEv_ri)
  obtain ⟨hl, hCBl, hle⟩ := LamTEv_spec (hV.trans LamEv_lt_Om1)
  rw [OrecEv_eq_OrecW hl hV hlt, val_ec, evA_eW (ups_inE hl)] at hle
  exact absurd hle (not_le.2 (OrecW_lt_top hl hlt))

/-! ## Where the first non-standard pair lies -/

/-- **Where the first non-standard pair lies**: `ρ_L <₂ ν_C = ρ_ξ` with `Λ_{ε_{x+x}} + ω² ≤ L < ξ` restart
indices, `υ_{Λ_{ε_{x+x}}+ω²} ≤ ρ_L < ν_C < Ω₁`. -/
theorem nuC_boundEv : ∃ L ξ, IsRestartIdx L ∧ IsRestartIdx ξ ∧ LamEv + ω * ω ≤ L ∧ L < ξ ∧
    upsilon (LamEv + ω * ω) ≤ upsilon L ∧ upsilon L < nuC ∧ nuC = upsilon ξ ∧ nuC < Om1 ∧
    le2 (upsilon L) nuC := by
  obtain ⟨L, ξ, hL, hξ, hLξ, he, h2, -, -, -⟩ := level2_restart
  have hLν : upsilon L < nuC := by rw [he]; exact upsilon_normal.strictMono hLξ
  have hle := left_ge_of_spec specEv2 hL hLν h2
  exact ⟨L, ξ, hL, hξ, hle, hLξ, upsilon_normal.strictMono.monotone hle, hLν, he, nuC_lt_Om1, h2⟩

end Googology.Trans.PoR.InaccPsi.R2

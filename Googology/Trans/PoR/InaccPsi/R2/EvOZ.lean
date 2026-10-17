import Googology.Trans.PoR.InaccPsi.R2.EvIZ
import Googology.Trans.PoR.InaccPsi.R2.EvO

/-!
# The recursive offset below `ζ_{x+1}`, Theorem BLK^O up to `Λ_{ζ_{x+1}}`, and the reach at every frontier `Λ_t`

The project's recursive offset (its paper's Definition 2.2) over the terms `TZ` (the Veblen terms `φ(1, ·)` in `x`:
constants, `ε_{x+t}`, sums, `ω^t`, below `evZ x`, the least fixed point of `ε` above `x`).  `OrecZ(λ) = sup ({1} ∪
{s(ρ_λ) + 1 : s realized cofinally below λ, constants below ρ_λ})`.  The proofs are those of `R2.EvO` with `TZ`,
`evZ`, `RstK.pkgZ` (Lemma IMG below `evZ ρ`), `rsStep_Z` (Lemma RS).

* `OrecZ`, `OrecZ_le` (`OrecZ(λ) ≤ evZ(ρ)`), `OrecZ_succ`, `LamZ` (`Λ_{ζ_{x+1}}`), `topIn_OrecZ`, `rsIn_OrecZ`,
  `specZ`;
* `blkZ` (**BLK^O with `OrecZ` below `υ_B` for every `B ≤ Λ_{ζ_{x+1}}`**), `coreZ`, `LamZ_lt_Om1`, `reach_OrecZ`,
  `OrecZ_LamZ`;
* `OrecZ_eq_OrecEv`, `LamEv_lt_LamZ` (`Λ_{ε_{x+x}} < Λ_{ζ_{x+1}}`), `OrecZ_LamEv`;
* `LamTZ t` (**the frontier of a term `t`**), `OrecZ_LamTZ'` (**`OrecZ(Λ_t) = t(ρ_{Λ_t})`**), `LamTZ_lt_LamZ`,
  `reach_LamTZ` (**the reach at every frontier**: `lh(ρ_{Λ_t}) = δ + t(ρ_{Λ_t})`), `blk_LamTZ`, `LamTZ_mono`,
  `LamTZ_strict`; `LamTZ_xx` (`Λ_{ε_{x+x}}` of `OrecZ` is `LamEv`), `reach_LamTZ_ex` (the frontiers of
  `ε_{x+x+1}` and `ε_{ε_{x+1}}`);
* `nuC_boundZ` (**`υ_{Λ_{ζ_{x+1}}} ≤ ρ_L < ν_C`**).

No new axiom.

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order TZ

/-! ## The recursion -/

/-- `s` is realized cofinally below `λ` by the offsets `O`. -/
def CofRealZ (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) (s : TZ) : Prop :=
  ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ CBz s (upsilon μ) ∧ val s (upsilon μ) ≤ O μ

/-- The set whose supremum is `OrecZ(λ)`. -/
def OSetZ (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : Set Ordinal.{0} :=
  insert 1 {w | ∃ s, CBz s (upsilon l) ∧ CofRealZ O l s ∧ w = val s (upsilon l) + 1}

theorem OSetZ_congr {O O' : Ordinal.{0} → Ordinal.{0}} {l : Ordinal.{0}}
    (h : ∀ μ < l, O μ = O' μ) : OSetZ O l = OSetZ O' l := by
  have key : ∀ s, CofRealZ O l s ↔ CofRealZ O' l s := by
    intro s
    constructor
    · intro hc ν hν
      obtain ⟨μ, h1, h2, h3, h4, h5⟩ := hc ν hν
      exact ⟨μ, h1, h2, h3, h4, by rw [← h μ h3]; exact h5⟩
    · intro hc ν hν
      obtain ⟨μ, h1, h2, h3, h4, h5⟩ := hc ν hν
      exact ⟨μ, h1, h2, h3, h4, by rw [h μ h3]; exact h5⟩
  ext w
  simp only [OSetZ, Set.mem_insert_iff, Set.mem_setOf_eq, key]

/-- **The recursive offset over `TZ`**, by well-founded recursion. -/
noncomputable def OrecZ : Ordinal.{0} → Ordinal.{0} :=
  Ordinal.lt_wf.fix (fun l IH => sSup (OSetZ (fun μ => if h : μ < l then IH μ h else 0) l))

theorem OrecZ_eq (l : Ordinal.{0}) : OrecZ l = sSup (OSetZ OrecZ l) := by
  show Ordinal.lt_wf.fix _ l = _
  rw [WellFounded.fix_eq]
  rw [OSetZ_congr (O' := OrecZ) (fun μ hμ => by simp only [hμ, dite_true]; rfl)]

theorem OSetZ_bdd (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) (hl : InE (upsilon l)) :
    ∀ w ∈ OSetZ O l, w ≤ evZ (upsilon l) := by
  intro w hw
  rcases hw with rfl | ⟨s, hCB, -, rfl⟩
  · exact (one_le_iff_pos.2 hl.pos).trans (lt_evZ _).le
  · exact add_one_le_of_lt (valZ_lt hl _ hCB)

theorem OSetZ_bddAbove (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) (hl : InE (upsilon l)) :
    BddAbove (OSetZ O l) := ⟨_, OSetZ_bdd O l hl⟩

/-- `OrecZ(λ) ≤ evZ(ρ)`. -/
theorem OrecZ_le {l : Ordinal.{0}} (hl : IsRestartIdx l) :
    OrecZ l ≤ evZ (upsilon l) := by
  rw [OrecZ_eq]; exact csSup_le ⟨1, Set.mem_insert _ _⟩ (OSetZ_bdd _ l (ups_inE hl))

theorem one_le_OrecZ {l : Ordinal.{0}} (hl : IsRestartIdx l) : 1 ≤ OrecZ l := by
  rw [OrecZ_eq]; exact le_csSup (OSetZ_bddAbove _ l (ups_inE hl)) (Set.mem_insert _ _)

theorem lt_OrecZ_of_cof {l : Ordinal.{0}} (hl : IsRestartIdx l) {s : TZ} (hCB : CBz s (upsilon l))
    (hc : CofRealZ OrecZ l s) : val s (upsilon l) < OrecZ l := by
  have h1 : val s (upsilon l) + 1 ≤ OrecZ l := by
    rw [OrecZ_eq]
    exact le_csSup (OSetZ_bddAbove _ l (ups_inE hl)) (Set.mem_insert_of_mem _ ⟨s, hCB, hc, rfl⟩)
  exact lt_of_lt_of_le (lt_add_one _) h1

theorem lt_OrecZ {l z : Ordinal.{0}} (hl : IsRestartIdx l) (hz : z < OrecZ l) :
    z = 0 ∨ ∃ s, CBz s (upsilon l) ∧ CofRealZ OrecZ l s ∧ z ≤ val s (upsilon l) := by
  rw [OrecZ_eq] at hz
  obtain ⟨w, hw, hzw⟩ :=
    (lt_csSup_iff (OSetZ_bddAbove _ l (ups_inE hl)) ⟨1, Set.mem_insert _ _⟩).1 hz
  rcases hw with rfl | ⟨s, hCB, hc, rfl⟩
  · left; exact le_antisymm (Order.lt_add_one_iff.1 (by rw [zero_add]; exact hzw)) zero_le
  · right; exact ⟨s, hCB, hc, Order.lt_add_one_iff.1 hzw⟩

/-- `OrecZ = 1` at a successor restart index. -/
theorem OrecZ_succ {l : Ordinal.{0}} (hl : IsRestartIdx l) (h2 : cL l < 2) : OrecZ l = 1 := by
  obtain ⟨l0, hl0, rfl⟩ := succ_ri hl h2
  have hww : 0 < ω * ω := mul_pos omega0_pos omega0_pos
  have hS : OSetZ OrecZ (l0 + ω * ω) = {1} := by
    ext w
    simp only [OSetZ, Set.mem_insert_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro (h | ⟨s, -, hc, -⟩)
      · exact h
      · exfalso
        obtain ⟨μ, hμ, h1, h3, -, -⟩ := hc l0 (lt_add_of_pos_right l0 hww)
        exact absurd h3 (not_lt.2 (next_mult (mult_of hl0) (ri_iff.1 hμ).2 h1))
    · intro h; exact Or.inl h
  rw [OrecZ_eq, hS, csSup_singleton]

/-! ## The frontier `Λ_{ζ_{x+1}}` -/

/-- `Λ_{ζ_{x+1}}`: the least restart index `λ` with `OrecZ(λ) = evZ(ρ_λ)` (`Ω₁` if there is none). -/
noncomputable def LamZ : Ordinal.{0} :=
  sInf (insert Om1 {l | IsRestartIdx l ∧ OrecZ l = evZ (upsilon l)})

theorem LamZ_le_Om1 : LamZ ≤ Om1 := csInf_le (OrderBot.bddBelow _) (Set.mem_insert _ _)

/-- **Below `Λ_{ζ_{x+1}}` the value is `< evZ(ρ)`.** -/
theorem OrecZ_lt_top {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlV : l < LamZ) :
    OrecZ l < evZ (upsilon l) := by
  rcases (OrecZ_le hl).lt_or_eq with h | h
  · exact h
  · exact absurd (csInf_le (OrderBot.bddBelow _) (Set.mem_insert_of_mem _
      (show l ∈ {l | IsRestartIdx l ∧ OrecZ l = evZ (upsilon l)} from ⟨hl, h⟩)))
      (not_le.2 hlV)

theorem LamZ_spec (h : LamZ < Om1) :
    IsRestartIdx LamZ ∧ OrecZ LamZ = evZ (upsilon LamZ) := by
  rcases csInf_mem (s := insert Om1 {l | IsRestartIdx l ∧ OrecZ l = evZ (upsilon l)})
    ⟨Om1, Set.mem_insert _ _⟩ with h' | h'
  · exact absurd (h' ▸ h : Om1 < Om1) (lt_irrefl _)
  · exact h'

/-! ## The inputs of Lemmas TOP and RS -/

/-- **The input of Lemma TOP** at a restart index `λ` with `OrecZ(λ) < evZ(ρ)`. -/
theorem topIn_OrecZ {l : Ordinal.{0}} (hl : IsRestartIdx l)
    (hlt : OrecZ l < evZ (upsilon l)) : TopInH OrecZ l := by
  classical
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρU := upsPt_upsilon hl0
  have hρE : InE (upsilon l) := upsPt_inE hρU
  have hone : 1 ≤ OrecZ l := one_le_OrecZ hl
  obtain ⟨s, hCB, hev⟩ := repZ hρE _ hlt
  have hpk : RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1)) →
      ImgPkg (upsilon l) (upsilon (l + ω + 1)) (val s) := fun R =>
    R.pkgZ hCB (by rw [hev]; exact hone)
  have hnot : ¬ CofRealZ OrecZ l s := fun hc =>
    absurd (lt_OrecZ_of_cof hl hCB hc) (by rw [hev]; exact lt_irrefl _)
  obtain ⟨m0, hm0, hm0c⟩ := list_max (csz s) _ ((cbz_iff s _).1 hCB) hρU.1
  unfold CofRealZ at hnot
  push Not at hnot
  obtain ⟨ν, hνl, hν⟩ := hnot
  have hνρ : upsilon ν < upsilon l := upsilon_normal.strictMono hνl
  refine ⟨val s, max (upsilon ν) m0, hev.symm, max_lt hνρ hm0, fun μ hμ hμl hx0 => ?_, hpk⟩
  have hνμ : ν < μ := upsilon_normal.strictMono.lt_iff_lt.1 (lt_of_le_of_lt (le_max_left _ _) hx0)
  have hCBμ : CBz s (upsilon μ) :=
    (cbz_iff s _).2 (fun c hc => lt_of_le_of_lt ((hm0c c hc).trans (le_max_right _ _)) hx0)
  exact hν μ hμ hνμ hμl hCBμ

/-- **The input of Lemma RS at a limit restart index `λ`** for `OrecZ`. -/
theorem rsIn_OrecZ {l : Ordinal.{0}} (hl : IsRestartIdx l) (h2 : 2 ≤ cL l) : RsInGen OrecZ l := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρ0 : 0 < upsilon l := (upsPt_upsilon hl0).1
  intro z hz
  rcases lt_OrecZ hl hz with rfl | ⟨s, hCB, hc, hzs⟩
  · refine ⟨OT.ev (OT.k 0), zero_le, fun R htg => rs_rstT R hρ0 htg, fun ν hν => ?_⟩
    obtain ⟨μ, hμ, h1, h3, -⟩ := cL_dense hl le_rfl (lt_of_lt_of_le one_lt_two h2) ν hν
    exact ⟨μ, hμ, h1, h3, by rw [OT.ev_k]; exact zero_le⟩
  · refine ⟨val s, hzs, rsStep_Z hl0 hCB, fun ν hν => ?_⟩
    obtain ⟨μ, hμ, h1, h3, -, h5⟩ := hc ν hν
    exact ⟨μ, hμ, h1, h3, h5⟩

theorem OrecZ_lt_δ {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) :
    OrecZ l < upsilon (l + ω + 1) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρU := upsPt_upsilon hl0
  have h1 : l < l + ω := lt_add_of_pos_right l omega0_pos
  have hτU := upsPt_upsilon (hl0.trans h1)
  exact lt_of_le_of_lt ((OrecZ_le hl).trans (evZ_le_ups (upsPt_inE hρU) (ups_lt_Om1 l hl1)
    (upsilon_normal.strictMono h1) hτU)) (upsilon_normal.strictMono (lt_add_one _))

/-- **`OrecZ` is a general offset specification up to `B`** when every restart index below `B` has
`OrecZ < evZ(ρ)`, except possibly `Λ_{ζ_{x+1}}` itself. -/
theorem specZ {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1)
    (hB : ∀ l, IsRestartIdx l → l < B → TopInH OrecZ l) : OffSpecGen OrecZ B where
  mult := hm
  cnt := hc
  le := fun _ hl hlB => OrecZ_lt_δ hl (hlB.trans hc)
  one := fun _ hl _ => one_le_OrecZ hl
  top := hB
  succ := fun _ hl _ h2 => OrecZ_succ hl h2
  rs := fun _ hl _ h2 => rsIn_OrecZ hl h2

theorem specZ_of_le {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ LamZ) :
    OffSpecGen OrecZ B :=
  specZ hm hc (fun _ hl hlB => topIn_OrecZ hl (OrecZ_lt_top hl (lt_of_lt_of_le hlB hB)))

/-! ## Theorem BLK^O up to `Λ_{ζ_{x+1}}` -/

/-- **Theorem BLK^O with `OrecZ` below `υ_B` for every `B ≤ Λ_{ζ_{x+1}}`** (`ω² ∣ B`, `B < Ω₁`) in `R₂^C`. -/
theorem blkZ {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ LamZ) :
    (∀ c d, c < d → d < upsilon B → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < B ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < B →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + OrecZ l)) ∧
    (∀ α < upsilon B, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  blk_genGen (specZ_of_le hm hc hB)

/-- **CORE-C up to `Λ_{ζ_{x+1}}`**. -/
theorem coreZ {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ LamZ) :
    Set.Iio (upsilon B) ⊆ Core R2C :=
  core_genGen (specZ_of_le hm hc hB)

/-- **`Λ_{ζ_{x+1}} < Ω₁`** (the core is countable, [C09] Cor 15.15). -/
theorem LamZ_lt_Om1 : LamZ < Om1 := by
  rcases LamZ_le_Om1.lt_or_eq with h | h
  · exact h
  · exfalso
    exact not_core_all (fun B hm hc => coreZ hm hc (by rw [h]; exact hc.le))

theorem LamZ_ri : IsRestartIdx LamZ := (LamZ_spec LamZ_lt_Om1).1

/-- **`OrecZ(Λ_{ζ_{x+1}}) = evZ(ρ)`**. -/
theorem OrecZ_LamZ : OrecZ LamZ = evZ (upsilon LamZ) := (LamZ_spec LamZ_lt_Om1).2

/-- **The exact reach of every restart below `Λ_{ζ_{x+1}}`**: `lh(ρ_λ) = δ_λ + OrecZ(λ)`. -/
theorem reach_OrecZ {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlV : l < LamZ) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + OrecZ l) :=
  (blkZ (ri_iff.1 LamZ_ri).2 LamZ_lt_Om1 le_rfl).2.1 l hl hlV |>.2.2

/-! ## Comparing with `OrecEv` -/

/-- **`OrecZ = OrecEv` below both frontiers** (the reach is unique). -/
theorem OrecZ_eq_OrecEv {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlZ : l < LamZ) (hlV : l < LamEv) :
    OrecZ l = OrecEv l :=
  (add_left_cancel_iff).1 (isReach_unique (reach_OrecZ hl hlZ) (reach_OrecEv hl hlV))

/-- The term `ε_{x+x}`. -/
def txx : TZ := ee (ee (cst 0))

theorem val_txx {x : Ordinal.{0}} (hx : InE x) : val txx x = evA x x := by
  simp only [txx, val_ee, val_cst, evA_zero hx]

theorem CBz_txx {x : Ordinal.{0}} (hx : 0 < x) : CBz txx x := hx

/-- **`Λ_{ε_{x+x}} < Λ_{ζ_{x+1}}`**. -/
theorem LamEv_lt_LamZ : LamEv < LamZ := by
  by_contra hle
  push Not at hle
  have hl := LamZ_ri
  have hρU := ups_ri hl
  have hρE := ups_inE hl
  have hz : evA (upsilon LamZ) (upsilon LamZ) < OrecZ LamZ := by
    rw [OrecZ_LamZ]; exact evA_lt_evZ hρE (lt_evZ _)
  rcases lt_OrecZ hl hz with h0 | ⟨s, hCB, hcs, hzs⟩
  · exact absurd h0 (evA_E _ _).pos.ne'
  obtain ⟨μ, hμ, -, hμl, h3, h4⟩ := hcs 0 (pos_iff_ne_zero.2 hl.1)
  have hμV : μ < LamEv := lt_of_lt_of_le hμl hle
  rw [OrecZ_eq_OrecEv hμ hμl hμV] at h4
  have hμE := ups_inE hμ
  have h5 : val s (upsilon μ) < val txx (upsilon μ) := by
    rw [val_txx hμE]; exact lt_of_le_of_lt h4 (OrecEv_lt_top hμ hμV)
  have h6 := (uniZ_lt (t := s) (u := txx) (ups_ri hμ) hρU (bases_ri hμ hl hμl LamZ_lt_Om1) h3
    (CBz_txx (ups_ri hμ).1)).2 h5
  rw [val_txx hρE] at h6
  exact absurd hzs (not_le.2 h6)

/-- **`OrecZ(Λ_{ε_{x+x}}) = ε_{ρ+ρ} = OrecEv(Λ_{ε_{x+x}})`**. -/
theorem OrecZ_LamEv : OrecZ LamEv = evA (upsilon LamEv) (upsilon LamEv) :=
  (add_left_cancel_iff).1 (isReach_unique (reach_OrecZ LamEv_ri LamEv_lt_LamZ) reach_LamEv)

/-! ## The frontier of a term -/

/-- **The frontier `Λ_t` of a term `t` of `TZ`**: the least restart index `λ` with constants of `t` below
`ρ_λ` and `t(ρ_λ) ≤ OrecZ(λ)` (`Ω₁` if there is none). -/
noncomputable def LamTZ (t : TZ) : Ordinal.{0} :=
  sInf (insert Om1 {l | IsRestartIdx l ∧ CBz t (upsilon l) ∧ val t (upsilon l) ≤ OrecZ l})

theorem LamTZ_le {t : TZ} {l : Ordinal.{0}} (hl : IsRestartIdx l) (hCB : CBz t (upsilon l))
    (hle : val t (upsilon l) ≤ OrecZ l) : LamTZ t ≤ l :=
  csInf_le (OrderBot.bddBelow _) (Set.mem_insert_of_mem _ ⟨hl, hCB, hle⟩)

theorem LamTZ_spec {t : TZ} (h : LamTZ t < Om1) :
    IsRestartIdx (LamTZ t) ∧ CBz t (upsilon (LamTZ t)) ∧ val t (upsilon (LamTZ t)) ≤ OrecZ (LamTZ t) := by
  rcases csInf_mem (s := insert Om1
    {l | IsRestartIdx l ∧ CBz t (upsilon l) ∧ val t (upsilon l) ≤ OrecZ l})
    ⟨Om1, Set.mem_insert _ _⟩ with h' | h'
  · exact absurd (h' ▸ h : Om1 < Om1) (lt_irrefl _)
  · exact h'

theorem lt_valZ_of_lt_LamTZ {t : TZ} {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (hμl : μ < LamTZ t)
    (hCB : CBz t (upsilon μ)) : OrecZ μ < val t (upsilon μ) := by
  by_contra hle
  exact absurd (LamTZ_le hμ hCB (not_lt.1 hle)) (not_le.2 hμl)

/-- **`OrecZ(Λ_t) = t(ρ_{Λ_t})`** (for `Λ_t < Ω₁` and `t(ρ_{Λ_t}) ≥ 1`). -/
theorem OrecZ_LamTZ {t : TZ} (hlt : LamTZ t < Om1) (h1 : 1 ≤ val t (upsilon (LamTZ t))) :
    OrecZ (LamTZ t) = val t (upsilon (LamTZ t)) := by
  obtain ⟨hl, hCB, hle⟩ := LamTZ_spec hlt
  set l := LamTZ t with hldef
  refine le_antisymm ?_ hle
  have hρU := ups_ri hl
  obtain ⟨m0, hm0, hm0c⟩ := list_max (csz t) _ ((cbz_iff t _).1 hCB) hρU.1
  obtain ⟨_, ⟨ν, hν, rfl⟩, hm0ν⟩ := (lt_isLUB_iff (upsilon_limit (ri_limit hl))).1 hm0
  rw [OrecZ_eq]
  refine csSup_le ⟨1, Set.mem_insert _ _⟩ ?_
  rintro w (rfl | ⟨s, hsCB, hc, rfl⟩)
  · exact h1
  obtain ⟨μ, hμ, hνμ, hμl, hCBμ, hsμ⟩ := hc ν hν
  have hm0μ : m0 < upsilon μ := hm0ν.trans (upsilon_normal.strictMono hνμ)
  have htμ : CBz t (upsilon μ) := (cbz_iff t _).2 (fun c hc => lt_of_le_of_lt (hm0c c hc) hm0μ)
  have h2 : val s (upsilon μ) < val t (upsilon μ) :=
    lt_of_le_of_lt hsμ (lt_valZ_of_lt_LamTZ hμ hμl htμ)
  have h3 := (uniZ_lt (ups_ri hμ) hρU (bases_ri hμ hl hμl hlt) hCBμ htμ).2 h2
  exact add_one_le_of_lt h3

/-- **`Λ_t < Λ_{ζ_{x+1}}`** for every term `t` with constants below `ρ_{Λ_{ζ_{x+1}}}` and value `≥ 1`. -/
theorem LamTZ_lt_LamZ {t : TZ} (hCB : CBz t (upsilon LamZ)) (h1 : 1 ≤ val t (upsilon LamZ)) :
    LamTZ t < LamZ := by
  have hle : LamTZ t ≤ LamZ := LamTZ_le LamZ_ri hCB (by
    rw [OrecZ_LamZ]; exact (valZ_lt (ups_inE LamZ_ri) _ hCB).le)
  refine lt_of_le_of_ne hle (fun e => ?_)
  have hlt : LamTZ t < Om1 := e ▸ LamZ_lt_Om1
  have h := OrecZ_LamTZ hlt (by rw [e]; exact h1)
  rw [e, OrecZ_LamZ] at h
  exact absurd h (valZ_lt (ups_inE LamZ_ri) _ hCB).ne'

theorem LamTZ_ri {t : TZ} (hCB : CBz t (upsilon LamZ)) (h1 : 1 ≤ val t (upsilon LamZ)) :
    IsRestartIdx (LamTZ t) :=
  (LamTZ_spec ((LamTZ_lt_LamZ hCB h1).trans LamZ_lt_Om1)).1

theorem one_le_valZ_LamTZ {t : TZ} (hCB : CBz t (upsilon LamZ)) (h1 : 1 ≤ val t (upsilon LamZ)) :
    1 ≤ val t (upsilon (LamTZ t)) := by
  have hlt := LamTZ_lt_LamZ hCB h1
  obtain ⟨hl, hCBl, -⟩ := LamTZ_spec (hlt.trans LamZ_lt_Om1)
  have hB := bases_ri hl LamZ_ri hlt LamZ_lt_Om1
  have h1' : (1 : Ordinal.{0}) < upsilon (LamTZ t) := one_lt_of_upsPt (ups_ri hl)
  exact (uniZ_le (t := cst 1) (u := t) (ups_ri hl) (ups_ri LamZ_ri) hB h1' hCBl).1 h1

/-- **`OrecZ(Λ_t) = t(ρ_{Λ_t})`** for every term with constants below `ρ_{Λ_{ζ_{x+1}}}` and value `≥ 1`. -/
theorem OrecZ_LamTZ' {t : TZ} (hCB : CBz t (upsilon LamZ)) (h1 : 1 ≤ val t (upsilon LamZ)) :
    OrecZ (LamTZ t) = val t (upsilon (LamTZ t)) :=
  OrecZ_LamTZ ((LamTZ_lt_LamZ hCB h1).trans LamZ_lt_Om1) (one_le_valZ_LamTZ hCB h1)

/-- **The reach at the frontier of every term**: `lh(ρ_{Λ_t}) = δ + t(ρ_{Λ_t})` in `R₂^C`. -/
theorem reach_LamTZ {t : TZ} (hCB : CBz t (upsilon LamZ)) (h1 : 1 ≤ val t (upsilon LamZ)) :
    IsReach R2C (upsilon (LamTZ t)) (upsilon (LamTZ t + ω + 1) + val t (upsilon (LamTZ t))) := by
  rw [← OrecZ_LamTZ' hCB h1]
  exact reach_OrecZ (LamTZ_ri hCB h1) (LamTZ_lt_LamZ hCB h1)

theorem LamTZ_ww_le {t : TZ} (hCB : CBz t (upsilon LamZ)) (h1 : 1 ≤ val t (upsilon LamZ)) :
    LamTZ t + ω * ω ≤ LamZ :=
  next_mult (ri_iff.1 (LamTZ_ri hCB h1)).2 (ri_iff.1 LamZ_ri).2 (LamTZ_lt_LamZ hCB h1)

/-- **Theorem BLK^O at the frontier of every term**: BLK^O with `OrecZ` below `υ_{Λ_t+ω²}`. -/
theorem blk_LamTZ {t : TZ} (hCB : CBz t (upsilon LamZ)) (h1 : 1 ≤ val t (upsilon LamZ)) :
    (∀ c d, c < d → d < upsilon (LamTZ t + ω * ω) → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < LamTZ t + ω * ω ∧
      c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < LamTZ t + ω * ω →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + OrecZ l)) ∧
    (∀ α < upsilon (LamTZ t + ω * ω), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  blkZ (dvd_add (ri_iff.1 (LamTZ_ri hCB h1)).2 (dvd_refl _))
    ((LamTZ_ww_le hCB h1).trans_lt LamZ_lt_Om1) (LamTZ_ww_le hCB h1)

/-- **Monotonicity of the frontier**: `t ≤ t'` at `ρ_{Λ_{ζ_{x+1}}}` gives `Λ_t ≤ Λ_{t'}`. -/
theorem LamTZ_mono {t t' : TZ} (hCB' : CBz t' (upsilon LamZ))
    (h1 : 1 ≤ val t (upsilon LamZ)) (hle : val t (upsilon LamZ) ≤ val t' (upsilon LamZ))
    (hc : CBz t (upsilon (LamTZ t'))) : LamTZ t ≤ LamTZ t' := by
  have h1' : 1 ≤ val t' (upsilon LamZ) := h1.trans hle
  have hlt' := LamTZ_lt_LamZ hCB' h1'
  obtain ⟨hl', hCBl', hle'⟩ := LamTZ_spec (hlt'.trans LamZ_lt_Om1)
  have hB := bases_ri hl' LamZ_ri hlt' LamZ_lt_Om1
  have hle2 := (uniZ_le (ups_ri hl') (ups_ri LamZ_ri) hB hc hCBl').1 hle
  exact LamTZ_le hl' hc (hle2.trans hle')

/-- `t < t'` at `ρ_{Λ_{ζ_{x+1}}}` gives `Λ_t < Λ_{t'}`. -/
theorem LamTZ_strict {t t' : TZ} (hCB : CBz t (upsilon LamZ)) (hCB' : CBz t' (upsilon LamZ))
    (h1 : 1 ≤ val t (upsilon LamZ)) (hlt : val t (upsilon LamZ) < val t' (upsilon LamZ))
    (hc : CBz t (upsilon (LamTZ t'))) : LamTZ t < LamTZ t' := by
  refine lt_of_le_of_ne (LamTZ_mono hCB' h1 hlt.le hc) (fun e => ?_)
  have h1' : 1 ≤ val t' (upsilon LamZ) := h1.trans hlt.le
  have hl' := LamTZ_lt_LamZ hCB' h1'
  obtain ⟨hlr, hCBl', hle'⟩ := LamTZ_spec (hl'.trans LamZ_lt_Om1)
  have hB := bases_ri hlr LamZ_ri hl' LamZ_lt_Om1
  have h2 := (uniZ_lt (ups_ri hlr) (ups_ri LamZ_ri) hB hc hCBl').1 hlt
  have h3 := OrecZ_LamTZ' hCB h1
  rw [e] at h3
  rw [h3] at hle'
  exact absurd hle' (not_le.2 h2)

/-! ## Some frontiers -/

/-- **`Λ_{ε_{x+x}}` of `OrecZ` is `LamEv`.** -/
theorem LamTZ_xx : LamTZ txx = LamEv := by
  have hV := LamEv_ri
  refine le_antisymm (LamTZ_le hV (CBz_txx (ups_ri hV).1)
    (by rw [val_txx (ups_inE hV), OrecZ_LamEv])) ?_
  by_contra hlt
  push Not at hlt
  have hZ := LamTZ_lt_LamZ (t := txx) (CBz_txx (ups_ri LamZ_ri).1)
    (by rw [val_txx (ups_inE LamZ_ri)]; exact (one_le_iff_pos.2 (ups_ri LamZ_ri).1).trans (le_evA (ups_inE LamZ_ri) _))
  obtain ⟨hl, -, hle⟩ := LamTZ_spec (hZ.trans LamZ_lt_Om1)
  rw [OrecZ_eq_OrecEv hl hZ hlt, val_txx (ups_inE hl)] at hle
  exact absurd hle (not_le.2 (OrecEv_lt_top hl hlt))

/-- The term `ε_{x+x+1}`. -/
def txx1 : TZ := ee (sm (ee (cst 0)) (cst 1))

/-- The term `ε_{ε_{x+1}}`. -/
def tee : TZ := ee (ee (cst 1))

/-- **The reach at the frontiers of `ε_{x+x+1}` and `ε_{ε_{x+1}}`**, with `Λ_{ε_{x+x}} < Λ_{ε_{x+x+1}} <
Λ_{ε_{ε_{x+1}}} < Λ_{ζ_{x+1}}`. -/
theorem reach_LamTZ_ex :
    IsReach R2C (upsilon (LamTZ txx1))
      (upsilon (LamTZ txx1 + ω + 1) + evA (upsilon (LamTZ txx1)) (upsilon (LamTZ txx1) + 1)) ∧
    IsReach R2C (upsilon (LamTZ tee))
      (upsilon (LamTZ tee + ω + 1) + evA (upsilon (LamTZ tee)) (eN (upsilon (LamTZ tee)))) ∧
    LamEv < LamTZ txx1 ∧ LamTZ txx1 < LamTZ tee ∧ LamTZ tee < LamZ := by
  have hZ := LamZ_ri
  have hρE := ups_inE hZ
  have h1ρ : (1 : Ordinal.{0}) < upsilon LamZ := one_lt_of_upsPt (ups_ri hZ)
  have hval1 : ∀ x, InE x → val txx1 x = evA x (x + 1) := fun x hx => by
    simp only [txx1, val_ee, val_sm, val_cst, evA_zero hx]
  have hval2 : ∀ x, InE x → val tee x = evA x (eN x) := fun x hx => by
    simp only [tee, val_ee, val_cst]
    rw [show (1 : Ordinal.{0}) = 0 + 1 from (zero_add 1).symm, evA_add_one, evA_zero hx]
  have hCB1 : ∀ x, 1 < x → CBz txx1 x := fun x hx => ⟨(zero_lt_one).trans hx, hx⟩
  have hCB2 : ∀ x, 1 < x → CBz tee x := fun x hx => hx
  have hone : ∀ c, 1 ≤ evA (upsilon LamZ) c :=
    fun c => (one_le_iff_pos.2 (ups_ri hZ).1).trans (le_evA hρE c)
  have h1 : 1 ≤ val txx1 (upsilon LamZ) := by rw [hval1 _ hρE]; exact hone _
  have h2 : 1 ≤ val tee (upsilon LamZ) := by rw [hval2 _ hρE]; exact hone _
  have hl1 := LamTZ_lt_LamZ (hCB1 _ h1ρ) h1
  have hl2 := LamTZ_lt_LamZ (hCB2 _ h1ρ) h2
  obtain ⟨hr1, -, -⟩ := LamTZ_spec (hl1.trans LamZ_lt_Om1)
  obtain ⟨hr2, -, -⟩ := LamTZ_spec (hl2.trans LamZ_lt_Om1)
  refine ⟨?_, ?_, ?_, ?_, hl2⟩
  · have := reach_LamTZ (hCB1 _ h1ρ) h1; rwa [hval1 _ (ups_inE hr1)] at this
  · have := reach_LamTZ (hCB2 _ h1ρ) h2; rwa [hval2 _ (ups_inE hr2)] at this
  · rw [← LamTZ_xx]
    refine LamTZ_strict (CBz_txx (ups_ri hZ).1) (hCB1 _ h1ρ)
      (by rw [val_txx hρE]; exact hone _) ?_ (CBz_txx (ups_ri hr1).1)
    rw [val_txx hρE, hval1 _ hρE]; exact evA_lt_iff.2 (lt_add_one _)
  · refine LamTZ_strict (hCB1 _ h1ρ) (hCB2 _ h1ρ) h1 ?_ (hCB1 _ (one_lt_of_upsPt (ups_ri hr2)))
    rw [hval1 _ hρE, hval2 _ hρE]
    exact evA_lt_iff.2 ((ev_isSuccLimit_of_inE (eN_E _)).add_one_lt (lt_eN _))

/-! ## Where the first non-standard pair lies -/

/-- **Where the first non-standard pair lies**: `ρ_L <₂ ν_C = ρ_ξ` with `Λ_{ζ_{x+1}} ≤ L < ξ` restart indices,
`υ_{Λ_{ζ_{x+1}}} ≤ ρ_L < ν_C < Ω₁`. -/
theorem nuC_boundZ : ∃ L ξ, IsRestartIdx L ∧ IsRestartIdx ξ ∧ LamZ ≤ L ∧ L < ξ ∧
    upsilon LamZ ≤ upsilon L ∧ upsilon L < nuC ∧ nuC = upsilon ξ ∧ nuC < Om1 ∧
    le2 (upsilon L) nuC := by
  obtain ⟨L, ξ, hL, hξ, hLξ, he, h2, -, -, -⟩ := level2_restart
  have hLν : upsilon L < nuC := by rw [he]; exact upsilon_normal.strictMono hLξ
  have hle := left_ge_of_spec (specZ_of_le (ri_iff.1 LamZ_ri).2 LamZ_lt_Om1 le_rfl) hL hLν h2
  exact ⟨L, ξ, hL, hξ, hle, hLξ, upsilon_normal.strictMono.monotone hle, hLν, he, nuC_lt_Om1, h2⟩

end Googology.Trans.PoR.InaccPsi.R2

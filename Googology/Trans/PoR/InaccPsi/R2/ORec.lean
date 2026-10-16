import Googology.Trans.PoR.InaccPsi.R2.BlkO

/-!
# The recursive offset `O` and Theorem BLK^O below `Λ_ε`

The project's recursive offset (its paper's Definition 2.2): a restart `ρ_μ` **realizes** a term `t`
if the constants of `t` are below `ρ_μ` and `t(ρ_μ) ≤ O(μ)`; `t` is **realized cofinally** below `λ`
if restarts `μ ∈ (ν, λ)` realize it for every `ν < λ`; and
`O(λ) = sup ({1} ∪ {t(ρ_λ) + 1 : t realized cofinally below λ, constants below ρ_λ})`.
`Λ_ε` is the least restart index below which `ε_{x+1}` is realized cofinally (`ε_{ρ_μ+1} ≤ O(μ)`
for cofinally many `μ`), or `Ω₁` if there is none.

* `CofReal`, `OSet`, `Ostep`, `Orec` (by well-founded recursion), `Orec_eq`;
* `Orec_le_eN` (`O(λ) ≤ ε_{ρ+1}`), `one_le_Orec`, `Orec_succ` (`O(λ₀ + ω²) = 1`);
* `rsIn_Orec` (the input of Lemma RS: every value below `O(λ)` is at most a term realized
  cofinally), `topIn_Orec` (the input of Lemma TOP from the paper's 2.2 (b): `O(λ)` is a term not
  realized cofinally, or `ε_{ρ+1}` when `ε_{x+1}` is not realized cofinally);
* `CofE`, `LamE`, `specO` (an offset specification up to every `B ≤ Λ_ε`);
* `blkO` (**Theorem BLK^O below `υ_B` for every `B ≤ Λ_ε`**, `ω² ∣ B`, `B < Ω₁`, with the recursive
  offset), `reach_Orec` (`lh(ρ_λ) = δ_λ + O(λ)` for every restart index `λ < Λ_ε`), `coreO`
  (`[0, υ_B) ⊆ Core(R₂^C)`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order OT

/-- `t` is realized cofinally below `λ` by the offsets `O`. -/
def CofReal (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) (t : OT) : Prop :=
  ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ CB t (upsilon μ) ∧ ev t (upsilon μ) ≤ O μ

/-- The set whose supremum is `O(λ)`. -/
def OSet (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : Set Ordinal.{0} :=
  insert 1 {w | ∃ t : OT, CB t (upsilon l) ∧ CofReal O l t ∧ w = ev t (upsilon l) + 1}

/-- One step of the recursion. -/
noncomputable def Ostep (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : Ordinal.{0} :=
  sSup (OSet O l)

theorem OSet_congr {O O' : Ordinal.{0} → Ordinal.{0}} {l : Ordinal.{0}}
    (h : ∀ μ < l, O μ = O' μ) : OSet O l = OSet O' l := by
  have key : ∀ t, CofReal O l t ↔ CofReal O' l t := by
    intro t
    constructor
    · intro hc ν hν
      obtain ⟨μ, h1, h2, h3, h4, h5⟩ := hc ν hν
      exact ⟨μ, h1, h2, h3, h4, by rw [← h μ h3]; exact h5⟩
    · intro hc ν hν
      obtain ⟨μ, h1, h2, h3, h4, h5⟩ := hc ν hν
      exact ⟨μ, h1, h2, h3, h4, by rw [h μ h3]; exact h5⟩
  ext w
  simp only [OSet, Set.mem_insert_iff, Set.mem_setOf_eq, key]

/-- **The recursive offset** `O(λ)`, defined from the `O(μ)`, `μ < λ`. -/
noncomputable def Orec : Ordinal.{0} → Ordinal.{0} :=
  Ordinal.lt_wf.fix (fun l IH => Ostep (fun μ => if h : μ < l then IH μ h else 0) l)

theorem Orec_eq (l : Ordinal.{0}) : Orec l = Ostep Orec l := by
  show Ordinal.lt_wf.fix _ l = _
  rw [WellFounded.fix_eq]
  unfold Ostep
  rw [OSet_congr (O' := Orec) (fun μ hμ => by simp only [hμ, dite_true]; rfl)]

theorem OSet_bdd (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) :
    ∀ w ∈ OSet O l, w ≤ eN (upsilon l) := by
  intro w hw
  rcases hw with rfl | ⟨t, hCB, -, rfl⟩
  · exact one_le_iff_pos.2 (lt_of_le_of_lt zero_le (lt_eN _))
  · exact add_one_le_of_lt (ev_lt_eN hCB)

theorem OSet_bddAbove (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : BddAbove (OSet O l) :=
  ⟨_, OSet_bdd O l⟩

/-- `O(λ) ≤ ε_{ρ_λ+1}`. -/
theorem Orec_le_eN (l : Ordinal.{0}) : Orec l ≤ eN (upsilon l) := by
  rw [Orec_eq]; exact csSup_le ⟨1, Set.mem_insert _ _⟩ (OSet_bdd Orec l)

theorem one_le_Orec (l : Ordinal.{0}) : 1 ≤ Orec l := by
  rw [Orec_eq]; exact le_csSup (OSet_bddAbove Orec l) (Set.mem_insert _ _)

/-- A term realized cofinally below `λ` (constants below `ρ_λ`) gives `t(ρ_λ) < O(λ)`. -/
theorem lt_Orec_of_cof {l : Ordinal.{0}} {t : OT} (hCB : CB t (upsilon l)) (hc : CofReal Orec l t) :
    ev t (upsilon l) < Orec l := by
  have h1 : ev t (upsilon l) + 1 ≤ Orec l := by
    rw [Orec_eq]
    exact le_csSup (OSet_bddAbove Orec l) (Set.mem_insert_of_mem _ ⟨t, hCB, hc, rfl⟩)
  exact lt_of_lt_of_le (lt_add_one _) h1

/-- Below `O(λ)` every value is at most a term realized cofinally, or `0`. -/
theorem lt_Orec {l z : Ordinal.{0}} (hz : z < Orec l) :
    z = 0 ∨ ∃ t : OT, CB t (upsilon l) ∧ CofReal Orec l t ∧ z ≤ ev t (upsilon l) := by
  rw [Orec_eq] at hz
  obtain ⟨w, hw, hzw⟩ := (lt_csSup_iff (OSet_bddAbove Orec l) ⟨1, Set.mem_insert _ _⟩).1 hz
  rcases hw with rfl | ⟨t, hCB, hc, rfl⟩
  · left; exact le_antisymm (Order.lt_add_one_iff.1 (by rw [zero_add]; exact hzw)) zero_le
  · right; exact ⟨t, hCB, hc, Order.lt_add_one_iff.1 hzw⟩

/-- Constants of a term below `s > 0` are below one `m < s`. -/
theorem cmax : ∀ (t : OT) (s : Ordinal.{0}), CB t s → 0 < s → ∃ m < s, ∀ c ∈ cs t, c ≤ m
  | OT.k a, s, h, _ => ⟨a, h, by simp [cs]⟩
  | OT.xw t, s, h, hs => cmax t s h hs
  | OT.add t u, s, h, hs => by
    obtain ⟨m1, h1, h1'⟩ := cmax t s h.1 hs
    obtain ⟨m2, h2, h2'⟩ := cmax u s h.2 hs
    refine ⟨max m1 m2, max_lt h1 h2, fun c hc => ?_⟩
    simp only [cs, List.mem_append] at hc
    rcases hc with hc | hc
    · exact (h1' c hc).trans (le_max_left _ _)
    · exact (h2' c hc).trans (le_max_right _ _)

/-- **`O` at a successor restart index** `λ₀ + ω²`: no restart lies in `(λ₀, λ)`, so `O(λ) = 1`. -/
theorem Orec_succ {l : Ordinal.{0}} (hl : IsRestartIdx l) (h2 : cL l < 2) : Orec l = 1 := by
  obtain ⟨l0, hl0, rfl⟩ := succ_ri hl h2
  have hww : 0 < ω * ω := mul_pos omega0_pos omega0_pos
  have hS : OSet Orec (l0 + ω * ω) = {1} := by
    ext w
    simp only [OSet, Set.mem_insert_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro (h | ⟨t, -, hc, -⟩)
      · exact h
      · exfalso
        obtain ⟨μ, hμ, h1, h3, -, -⟩ := hc l0 (lt_add_of_pos_right l0 hww)
        exact absurd h3 (not_lt.2 (next_mult (mult_of hl0) (ri_iff.1 hμ).2 h1))
    · intro h; exact Or.inl h
  rw [Orec_eq]; unfold Ostep; rw [hS, csSup_singleton]

/-- **The input of Lemma RS** at every limit restart index. -/
theorem rsIn_Orec {l : Ordinal.{0}} (hl : IsRestartIdx l) (h2 : 2 ≤ cL l) : RsInT Orec l := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρ0 : 0 < upsilon l := (upsPt_upsilon hl0).1
  intro z hz
  rcases lt_Orec hz with rfl | ⟨t, hCB, hc, hzt⟩
  · refine ⟨k 0, hρ0, zero_le, fun ν hν => ?_⟩
    obtain ⟨μ, hμ, h1, h3, -⟩ := cL_dense hl le_rfl (lt_of_lt_of_le one_lt_two h2) ν hν
    exact ⟨μ, hμ, h1, h3, zero_le⟩
  · refine ⟨t, hCB, hzt, fun ν hν => ?_⟩
    obtain ⟨μ, hμ, h1, h3, -, h5⟩ := hc ν hν
    exact ⟨μ, hμ, h1, h3, h5⟩

/-- `ε_{x+1}` is realized cofinally below `λ`. -/
def CofE (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : Prop :=
  ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ eN (upsilon μ) ≤ O μ

/-- **The input of Lemma TOP** at a restart index `λ` below which `ε_{x+1}` is not realized
cofinally (the paper's 2.2 (b)). -/
theorem topIn_Orec {l : Ordinal.{0}} (hl : IsRestartIdx l) (hE : ¬ CofE Orec l) : TopInH Orec l := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρU := upsPt_upsilon hl0
  have hρE : InE (upsilon l) := upsPt_inE hρU
  rcases (Orec_le_eN l).lt_or_eq with hlt | heq
  · obtain ⟨t0, hCB, hev⟩ := rep hρE (Orec l) hlt
    have hnot : ¬ CofReal Orec l t0 := fun hc =>
      absurd (lt_Orec_of_cof hCB hc) (by rw [hev]; exact lt_irrefl _)
    unfold CofReal at hnot
    push Not at hnot
    obtain ⟨ν, hνl, hν⟩ := hnot
    obtain ⟨m, hm, hmc⟩ := cmax t0 _ hCB hρU.1
    have hνρ : upsilon ν < upsilon l := upsilon_normal.strictMono hνl
    refine ⟨ev t0, max (upsilon ν) m, hev.symm, max_lt hνρ hm, fun μ hμ hμl hx0 => ?_,
      fun R => R.pkg_ot hCB (by rw [hev]; exact one_le_Orec l)⟩
    have hνμ : ν < μ := upsilon_normal.strictMono.lt_iff_lt.1 (lt_of_le_of_lt (le_max_left _ _) hx0)
    have hCBμ : CB t0 (upsilon μ) :=
      (cb_iff t0 _).2 (fun c hc => lt_of_le_of_lt ((hmc c hc).trans (le_max_right _ _)) hx0)
    exact hν μ hμ hνμ hμl hCBμ
  · unfold CofE at hE
    push Not at hE
    obtain ⟨ν, hνl, hν⟩ := hE
    refine ⟨eN, upsilon ν, heq, upsilon_normal.strictMono hνl, fun μ hμ hμl hx0 => ?_,
      fun R => R.pkg_eN⟩
    exact hν μ hμ (upsilon_normal.strictMono.lt_iff_lt.1 hx0) hμl

theorem Orec_lt_δ {l : Ordinal.{0}} (hl : IsRestartIdx l) : Orec l < upsilon (l + ω + 1) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have h1 : upsilon l < upsilon (l + ω) :=
    upsilon_normal.strictMono (lt_add_of_pos_right l omega0_pos)
  have h2 : upsilon (l + ω) < upsilon (l + ω + 1) := upsilon_normal.strictMono (lt_add_one _)
  have hτE : InE (upsilon (l + ω)) := upsPt_inE (upsPt_upsilon (lt_of_lt_of_le hl0 le_self_add))
  exact lt_of_le_of_lt ((Orec_le_eN l).trans (eN_le h1 hτE)) h2

/-- **The recursive offset is an offset specification up to `B`** when `ε_{x+1}` is realized
cofinally below no restart index below `B`. -/
theorem specO {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1)
    (hB : ∀ l, IsRestartIdx l → l < B → ¬ CofE Orec l) : OffSpecH Orec B where
  mult := hm
  cnt := hc
  le := fun _ hl _ => Orec_lt_δ hl
  one := fun l _ _ => one_le_Orec l
  top := fun l hl hlB => topIn_Orec hl (hB l hl hlB)
  succ := fun _ hl _ h2 => Orec_succ hl h2
  rs := fun _ hl _ h2 => rsIn_Orec hl h2

/-- `Λ_ε`: the least restart index below which `ε_{x+1}` is realized cofinally (`Ω₁` if there is
none). -/
noncomputable def LamE : Ordinal.{0} := sInf (insert Om1 {l | IsRestartIdx l ∧ CofE Orec l})

theorem not_cofE_of_lt {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlE : l < LamE) : ¬ CofE Orec l :=
  fun h => absurd (csInf_le (OrderBot.bddBelow _) (Set.mem_insert_of_mem _ (show l ∈ {l | IsRestartIdx l ∧ CofE Orec l} from ⟨hl, h⟩)))
    (not_le.2 hlE)

theorem LamE_le_Om1 : LamE ≤ Om1 := csInf_le (OrderBot.bddBelow _) (Set.mem_insert _ _)

theorem specO_of_le {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ LamE) :
    OffSpecH Orec B :=
  specO hm hc (fun _ hl hlB => not_cofE_of_lt hl (lt_of_lt_of_le hlB hB))

/-- **Theorem BLK^O below `υ_B` for every `B ≤ Λ_ε`** (`ω² ∣ B`, `B < Ω₁`) in `R₂^C`, with the
recursive offset: (i) the `<₂`-pairs whose right end is below `υ_B` are exactly
`(υ_{μ+ω·j}, υ_{μ+ω·j+1})`, `j ≥ 1`, `μ < B` zero or a restart index; (ii) every restart `ρ_λ`
(`λ < B`) has no `<₁`-predecessor and no `<₂`-successor, and its reach is `δ_λ + O(λ)` (`IsReach`, the
maximum; the interval form follows with `reach_interval`); (iii) every point below `υ_B` that is not
a `υ`-point has its `R₁⁺` reach. -/
theorem blkO {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ LamE) :
    (∀ c d, c < d → d < upsilon B → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < B ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < B →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + Orec l)) ∧
    (∀ α < upsilon B, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  blk_genH (specO_of_le hm hc hB)

/-- **The exact reach of every restart below `Λ_ε`** in `R₂^C`: `lh(ρ_λ) = δ_λ + O(λ)`. -/
theorem reach_Orec {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlE : l < LamE) (hl1 : l < Om1) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + Orec l) := by
  have hww : 0 < ω * ω := mul_pos omega0_pos omega0_pos
  have hm : ω * ω ∣ l + ω * ω := dvd_add (ri_iff.1 hl).2 (dvd_refl _)
  have hc : l + ω * ω < Om1 := Om1_add_lt hl1 ww_lt_Om1
  have S := specO hm hc (fun l' hl' hl'B => not_cofE_of_lt hl' (lt_of_le_of_lt (by
    by_contra hgt
    exact absurd hl'B (not_lt.2 (next_mult (ri_iff.1 hl).2 (ri_iff.1 hl').2 (not_le.1 hgt)))) hlE))
  exact reach_allH S hl (lt_add_of_pos_right l hww)

/-- **CORE-C below `Λ_ε`**: `[0, υ_B) ⊆ Core(R₂^C)` for every `B ≤ Λ_ε` (`ω² ∣ B`, `B < Ω₁`;
without FRAG, [C09] Theorem 14.14). -/
theorem coreO {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ LamE) :
    Set.Iio (upsilon B) ⊆ Core R2C :=
  core_genH (specO_of_le hm hc hB)

end Googology.Trans.PoR.InaccPsi.R2

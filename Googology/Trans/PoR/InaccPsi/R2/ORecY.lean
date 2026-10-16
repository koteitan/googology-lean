import Googology.Trans.PoR.InaccPsi.R2.ImgY
import Googology.Trans.PoR.InaccPsi.R2.ORecX

/-!
# The recursive offset below `ε_{x+2}`, and Theorem BLK^O at `Λ_{ε²}` and up to `Λ_{ε_{x+2}}`

The project's recursive offset (its paper's Definition 2.2) over the terms `OTY` (every Cantor normal form
in `x` and `ε_{x+1}` below `ε_{x+2}`).  `OrecY(λ) = sup ({1} ∪ {s(ρ_λ) + 1 : s realized cofinally below λ,
constants below ρ_λ})`.  It extends `OrecX`.

* `OrecY_le` (`OrecY(λ) ≤ ε_{ρ+2}`), `OrecY_succ`;
* `LamY` (`Λ_{ε_{x+2}}`: the least restart index `λ` with `OrecY(λ) = ε_{ρ_λ+2}`); below it the value is a
  term of `OTY`;
* `topIn_OrecY` (the input of Lemma TOP: the value is `s(ρ)` for a term `s` of `OTY` not realized
  cofinally, with the IMG package `RstK.pkgY`), `rsIn_OrecY` (the input of Lemma RS, with `rs_rstT` and
  `rs_rstY`), `specY`;
* `blkOY` (**Theorem BLK^O with `OrecY` below `υ_B` for every `B ≤ Λ_{ε_{x+2}}`**), `coreOY`, `LamY_lt_Om1`,
  `reach_OrecY` (`lh(ρ_λ) = δ_λ + OrecY(λ)` for every restart index `λ < Λ_{ε_{x+2}}`), `OrecY_LamY`
  (`OrecY(Λ_{ε_{x+2}}) = ε_{ρ+2}`);
* `OrecY_eq_OrecX`, `LamX_lt_LamY`, `OrecY_LamX` (`OrecY(Λ_{ε²}) = ε_{ρ+1}·ε_{ρ+1}`), `reach_LamX` (**the
  reach at `Λ_{ε²}`**: `lh(ρ) = δ + ε_{ρ+1}·ε_{ρ+1}`);
* `topIn_OrecY_LamY`, `specY_LamY`, `blk_LamY` (**Theorem BLK^O at `Λ_{ε_{x+2}}`**: below
  `υ_{Λ_{ε_{x+2}}+ω²}`, with the IMG package of the term `ε_{x+2}`, `RstK.pkg_eNN`), `reach_LamY` (**the reach
  at `Λ_{ε_{x+2}}`**: `lh(ρ) = δ + ε_{ρ+2}`), `core_LamY`, `left_ge_LamY_ww`;
* `upsY_le_nuC`, `left_ge_LamY`, `nuC_boundY` (**`υ_{Λ_{ε_{x+2}}} ≤ ρ_L < ν_C`**).

No new axiom.

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order OT OTY

/-- A common bound for a finite list of ordinals below `σ`. -/
theorem list_max : ∀ (L : List Ordinal.{0}) (σ : Ordinal.{0}), (∀ c ∈ L, c < σ) → 0 < σ →
    ∃ m < σ, ∀ c ∈ L, c ≤ m
  | [], _, _, hs => ⟨0, hs, fun c hc => by simp at hc⟩
  | a :: L, σ, h, hs => by
    obtain ⟨m, hm, hc⟩ := list_max L σ (fun c hc => h c (List.mem_cons_of_mem _ hc)) hs
    refine ⟨max a m, max_lt (h a List.mem_cons_self) hm, fun c hc' => ?_⟩
    rcases List.mem_cons.1 hc' with rfl | hc'
    · exact le_max_left _ _
    · exact (hc c hc').trans (le_max_right _ _)

/-! ## The recursion -/

/-- `s` is realized cofinally below `λ` by the offsets `O`. -/
def CofRealY (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) (s : OTY) : Prop :=
  ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ CBY s (upsilon μ) ∧ ev2 s (upsilon μ) ≤ O μ

/-- The set whose supremum is `OrecY(λ)`. -/
def OSetY (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : Set Ordinal.{0} :=
  insert 1 {w | ∃ s, CBY s (upsilon l) ∧ CofRealY O l s ∧ w = ev2 s (upsilon l) + 1}

theorem OSetY_congr {O O' : Ordinal.{0} → Ordinal.{0}} {l : Ordinal.{0}}
    (h : ∀ μ < l, O μ = O' μ) : OSetY O l = OSetY O' l := by
  have key : ∀ s, CofRealY O l s ↔ CofRealY O' l s := by
    intro s
    constructor
    · intro hc ν hν
      obtain ⟨μ, h1, h2, h3, h4, h5⟩ := hc ν hν
      exact ⟨μ, h1, h2, h3, h4, by rw [← h μ h3]; exact h5⟩
    · intro hc ν hν
      obtain ⟨μ, h1, h2, h3, h4, h5⟩ := hc ν hν
      exact ⟨μ, h1, h2, h3, h4, by rw [h μ h3]; exact h5⟩
  ext w
  simp only [OSetY, Set.mem_insert_iff, Set.mem_setOf_eq, key]

/-- **The recursive offset over `OTY`**, by well-founded recursion. -/
noncomputable def OrecY : Ordinal.{0} → Ordinal.{0} :=
  Ordinal.lt_wf.fix (fun l IH => sSup (OSetY (fun μ => if h : μ < l then IH μ h else 0) l))

theorem OrecY_eq (l : Ordinal.{0}) : OrecY l = sSup (OSetY OrecY l) := by
  show Ordinal.lt_wf.fix _ l = _
  rw [WellFounded.fix_eq]
  rw [OSetY_congr (O' := OrecY) (fun μ hμ => by simp only [hμ, dite_true]; rfl)]

theorem OSetY_bdd (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) :
    ∀ w ∈ OSetY O l, w ≤ eN (eN (upsilon l)) := by
  intro w hw
  rcases hw with rfl | ⟨s, hCB, -, rfl⟩
  · exact one_le_iff_pos.2 (eN_E _).pos
  · exact add_one_le_of_lt (ev2_lt s hCB)

theorem OSetY_bddAbove (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) :
    BddAbove (OSetY O l) := ⟨_, OSetY_bdd O l⟩

/-- `OrecY(λ) ≤ ε_{ρ+2}`. -/
theorem OrecY_le (l : Ordinal.{0}) : OrecY l ≤ eN (eN (upsilon l)) := by
  rw [OrecY_eq]; exact csSup_le ⟨1, Set.mem_insert _ _⟩ (OSetY_bdd _ l)

theorem one_le_OrecY (l : Ordinal.{0}) : 1 ≤ OrecY l := by
  rw [OrecY_eq]; exact le_csSup (OSetY_bddAbove _ l) (Set.mem_insert _ _)

theorem lt_OrecY_of_cof {l : Ordinal.{0}} {s : OTY} (hCB : CBY s (upsilon l))
    (hc : CofRealY OrecY l s) : ev2 s (upsilon l) < OrecY l := by
  have h1 : ev2 s (upsilon l) + 1 ≤ OrecY l := by
    rw [OrecY_eq]
    exact le_csSup (OSetY_bddAbove _ l) (Set.mem_insert_of_mem _ ⟨s, hCB, hc, rfl⟩)
  exact lt_of_lt_of_le (lt_add_one _) h1

theorem lt_OrecY {l z : Ordinal.{0}} (hz : z < OrecY l) :
    z = 0 ∨ ∃ s, CBY s (upsilon l) ∧ CofRealY OrecY l s ∧ z ≤ ev2 s (upsilon l) := by
  rw [OrecY_eq] at hz
  obtain ⟨w, hw, hzw⟩ := (lt_csSup_iff (OSetY_bddAbove _ l) ⟨1, Set.mem_insert _ _⟩).1 hz
  rcases hw with rfl | ⟨s, hCB, hc, rfl⟩
  · left; exact le_antisymm (Order.lt_add_one_iff.1 (by rw [zero_add]; exact hzw)) zero_le
  · right; exact ⟨s, hCB, hc, Order.lt_add_one_iff.1 hzw⟩

/-- `OrecY = 1` at a successor restart index. -/
theorem OrecY_succ {l : Ordinal.{0}} (hl : IsRestartIdx l) (h2 : cL l < 2) : OrecY l = 1 := by
  obtain ⟨l0, hl0, rfl⟩ := succ_ri hl h2
  have hww : 0 < ω * ω := mul_pos omega0_pos omega0_pos
  have hS : OSetY OrecY (l0 + ω * ω) = {1} := by
    ext w
    simp only [OSetY, Set.mem_insert_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro (h | ⟨s, -, hc, -⟩)
      · exact h
      · exfalso
        obtain ⟨μ, hμ, h1, h3, -, -⟩ := hc l0 (lt_add_of_pos_right l0 hww)
        exact absurd h3 (not_lt.2 (next_mult (mult_of hl0) (ri_iff.1 hμ).2 h1))
    · intro h; exact Or.inl h
  rw [OrecY_eq, hS, csSup_singleton]

/-! ## The frontier `Λ_{ε_{x+2}}` -/

/-- `Λ_{ε_{x+2}}`: the least restart index `λ` with `OrecY(λ) = ε_{ρ_λ+2}` (`Ω₁` if there is none). -/
noncomputable def LamY : Ordinal.{0} :=
  sInf (insert Om1 {l | IsRestartIdx l ∧ OrecY l = eN (eN (upsilon l))})

theorem LamY_le_Om1 : LamY ≤ Om1 := csInf_le (OrderBot.bddBelow _) (Set.mem_insert _ _)

/-- **Below `Λ_{ε_{x+2}}` the value is `< ε_{ρ+2}`.** -/
theorem OrecY_lt_top {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlY : l < LamY) :
    OrecY l < eN (eN (upsilon l)) := by
  rcases (OrecY_le l).lt_or_eq with h | h
  · exact h
  · exact absurd (csInf_le (OrderBot.bddBelow _) (Set.mem_insert_of_mem _
      (show l ∈ {l | IsRestartIdx l ∧ OrecY l = eN (eN (upsilon l))} from ⟨hl, h⟩)))
      (not_le.2 hlY)

theorem LamY_spec (h : LamY < Om1) : IsRestartIdx LamY ∧ OrecY LamY = eN (eN (upsilon LamY)) := by
  rcases csInf_mem (s := insert Om1 {l | IsRestartIdx l ∧ OrecY l = eN (eN (upsilon l))})
    ⟨Om1, Set.mem_insert _ _⟩ with h' | h'
  · exact absurd (h' ▸ h : Om1 < Om1) (lt_irrefl _)
  · exact h'

/-! ## The inputs of Lemmas TOP and RS -/

/-- **The input of Lemma TOP** at a restart index `λ` with `OrecY(λ) < ε_{ρ+2}`. -/
theorem topIn_OrecY {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlt : OrecY l < eN (eN (upsilon l))) :
    TopInH OrecY l := by
  classical
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρU := upsPt_upsilon hl0
  have hρE : InE (upsilon l) := upsPt_inE hρU
  have hone : 1 ≤ OrecY l := one_le_OrecY l
  obtain ⟨s, hCB, hev, hpk⟩ : ∃ s : OTY, CBY s (upsilon l) ∧ ev2 s (upsilon l) = OrecY l ∧
      (RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1)) →
        ImgPkg (upsilon l) (upsilon (l + ω + 1)) (ev2 s)) := by
    by_cases hR : RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1))
    · obtain ⟨s, h1, h2, h3⟩ := hR.pkgY hone hlt
      exact ⟨s, h1, h2, fun _ => h3⟩
    · obtain ⟨s, h1, h2⟩ := repY hρE _ hlt
      exact ⟨s, h1, h2, fun R => absurd R hR⟩
  have hnot : ¬ CofRealY OrecY l s := fun hc =>
    absurd (lt_OrecY_of_cof hCB hc) (by rw [hev]; exact lt_irrefl _)
  obtain ⟨m0, hm0, hm0c⟩ := list_max (csY s) _ ((cbY_iff s _).1 hCB) hρU.1
  unfold CofRealY at hnot
  push Not at hnot
  obtain ⟨ν, hνl, hν⟩ := hnot
  have hνρ : upsilon ν < upsilon l := upsilon_normal.strictMono hνl
  refine ⟨ev2 s, max (upsilon ν) m0, hev.symm, max_lt hνρ hm0, fun μ hμ hμl hx0 => ?_, hpk⟩
  have hνμ : ν < μ := upsilon_normal.strictMono.lt_iff_lt.1 (lt_of_le_of_lt (le_max_left _ _) hx0)
  have hCBμ : CBY s (upsilon μ) :=
    (cbY_iff s _).2 (fun c hc => lt_of_le_of_lt ((hm0c c hc).trans (le_max_right _ _)) hx0)
  exact hν μ hμ hνμ hμl hCBμ

/-- **The input of Lemma RS at a limit restart index `λ`** for `OrecY`. -/
theorem rsIn_OrecY {l : Ordinal.{0}} (hl : IsRestartIdx l) (h2 : 2 ≤ cL l) : RsInGen OrecY l := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρ0 : 0 < upsilon l := (upsPt_upsilon hl0).1
  intro z hz
  rcases lt_OrecY hz with rfl | ⟨s, hCB, hc, hzs⟩
  · refine ⟨ev (k 0), zero_le, fun R htg => rs_rstT R hρ0 htg, fun ν hν => ?_⟩
    obtain ⟨μ, hμ, h1, h3, -⟩ := cL_dense hl le_rfl (lt_of_lt_of_le one_lt_two h2) ν hν
    exact ⟨μ, hμ, h1, h3, by rw [ev_k]; exact zero_le⟩
  · refine ⟨ev2 s, hzs, ?_, fun ν hν => ?_⟩
    · by_cases hE : hasE s
      · exact fun R htg => rs_rstY R hE hCB htg
      · obtain ⟨hf, hcb⟩ := toOT_spec s hE
        have e : ev2 s = ev (toOT s) := funext hf
        rw [e]
        exact fun R htg => rs_rstT R (hcb _ hCB) htg
    · obtain ⟨μ, hμ, h1, h3, -, h5⟩ := hc ν hν
      exact ⟨μ, hμ, h1, h3, h5⟩

theorem OrecY_lt_δ {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) :
    OrecY l < upsilon (l + ω + 1) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρU := upsPt_upsilon hl0
  have h1 : l < l + ω + 1 := lt_of_lt_of_le (lt_add_of_pos_right l omega0_pos) le_self_add
  have hδU := upsPt_upsilon (hl0.trans h1)
  exact lt_of_le_of_lt (OrecY_le l)
    (eNN_lt_ups hρU (ups_lt_Om1 l hl1) _ (upsilon_normal.strictMono h1) hδU)

/-- **`OrecY` is a general offset specification up to `B`** when every restart index below `B` has
`OrecY < ε_{ρ+2}`. -/
theorem specY {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1)
    (hB : ∀ l, IsRestartIdx l → l < B → OrecY l < eN (eN (upsilon l))) : OffSpecGen OrecY B where
  mult := hm
  cnt := hc
  le := fun _ hl hlB => OrecY_lt_δ hl (hlB.trans hc)
  one := fun l _ _ => one_le_OrecY l
  top := fun l hl hlB => topIn_OrecY hl (hB l hl hlB)
  succ := fun _ hl _ h2 => OrecY_succ hl h2
  rs := fun _ hl _ h2 => rsIn_OrecY hl h2

theorem specY_of_le {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ LamY) :
    OffSpecGen OrecY B :=
  specY hm hc (fun _ hl hlB => OrecY_lt_top hl (lt_of_lt_of_le hlB hB))

/-! ## Theorem BLK^O up to `Λ_{ε_{x+2}}` -/

/-- **Theorem BLK^O with `OrecY` below `υ_B` for every `B ≤ Λ_{ε_{x+2}}`** (`ω² ∣ B`, `B < Ω₁`) in
`R₂^C`: (i) the `<₂`-pairs with right end below `υ_B` are the standard pairs; (ii) every restart `ρ_λ`
(`λ < B`) has no `<₁`-predecessor, no `<₂`-successor, and reach `δ_λ + OrecY(λ)`; (iii) every point below
`υ_B` that is not a `υ`-point has its `R₁⁺` reach. -/
theorem blkOY {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ LamY) :
    (∀ c d, c < d → d < upsilon B → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < B ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < B →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + OrecY l)) ∧
    (∀ α < upsilon B, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  blk_genGen (specY_of_le hm hc hB)

/-- **CORE-C up to `Λ_{ε_{x+2}}`**: `[0, υ_B) ⊆ Core(R₂^C)` for every `B ≤ Λ_{ε_{x+2}}`. -/
theorem coreOY {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ LamY) :
    Set.Iio (upsilon B) ⊆ Core R2C :=
  core_genGen (specY_of_le hm hc hB)

/-- **`Λ_{ε_{x+2}} < Ω₁`** (the core is countable, [C09] Cor 15.15). -/
theorem LamY_lt_Om1 : LamY < Om1 := by
  rcases LamY_le_Om1.lt_or_eq with h | h
  · exact h
  · exfalso
    exact not_core_all (fun B hm hc => coreOY hm hc (by rw [h]; exact hc.le))

theorem LamY_ri : IsRestartIdx LamY := (LamY_spec LamY_lt_Om1).1

/-- **`OrecY(Λ_{ε_{x+2}}) = ε_{ρ+2}`** (`ρ = ρ_{Λ_{ε_{x+2}}}`). -/
theorem OrecY_LamY : OrecY LamY = eN (eN (upsilon LamY)) := (LamY_spec LamY_lt_Om1).2

/-- **The exact reach of every restart below `Λ_{ε_{x+2}}`** in `R₂^C`: `lh(ρ_λ) = δ_λ + OrecY(λ)`. -/
theorem reach_OrecY {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlY : l < LamY) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + OrecY l) :=
  (blkOY (ri_iff.1 LamY_ri).2 LamY_lt_Om1 le_rfl).2.1 l hl hlY |>.2.2

theorem coreOY_LamY : Set.Iio (upsilon LamY) ⊆ Core R2C :=
  coreOY (ri_iff.1 LamY_ri).2 LamY_lt_Om1 le_rfl

/-! ## Comparing with `OrecX`; the value at `Λ_{ε²}` -/

/-- **`OrecY = OrecX` below both frontiers** (the reach is unique). -/
theorem OrecY_eq_OrecX {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlY : l < LamY) (hlX : l < LamX) :
    OrecY l = OrecX l :=
  (add_left_cancel_iff).1 (isReach_unique (reach_OrecY hl hlY) (reach_OrecX hl hlX))

/-- **`Λ_{ε²} < Λ_{ε_{x+2}}`.** -/
theorem LamX_lt_LamY : LamX < LamY := by
  by_contra hle
  push Not at hle
  obtain ⟨hl, hc⟩ := LamY_spec LamY_lt_Om1
  have hl0 : 0 < LamY := pos_iff_ne_zero.2 hl.1
  set e := eN (upsilon LamY) with he
  have hz : ω ^ (e + e) < OrecY LamY := by
    rw [hc]
    have h1 : e + e < eN e := (inE_indec (eN_E _)).add_lt (lt_eN e) (lt_eN e)
    have h2 := (opow_lt_opow_iff_right one_lt_omega0).2 h1
    have hE : ω ^ eN e = eN e := eN_E e
    rwa [hE] at h2
  rcases lt_OrecY hz with h0 | ⟨s, hCB, hcs, hzs⟩
  · exact absurd h0 (opow_pos _ omega0_pos).ne'
  have hbig := (big_iff s hCB).1 hzs
  obtain ⟨μ, hμ, -, hμl, h3, h4⟩ := hcs 0 hl0
  have hμX : μ < LamX := lt_of_lt_of_le hμl hle
  have h5 := (big_iff s h3).2 hbig
  rw [OrecY_eq_OrecX hμ hμl hμX] at h4
  have h6 := OrecX_lt_top hμ (hμl.trans LamY_lt_Om1) (not_cofX_of_lt hμ hμX)
  exact absurd (h5.trans h4) (not_le.2 h6)

/-- **`OrecY(Λ_{ε²}) = ε_{ρ+1}·ε_{ρ+1}`** (`ρ = ρ_{Λ_{ε²}}`). -/
theorem OrecY_LamX : OrecY LamX = eN (upsilon LamX) * eN (upsilon LamX) := by
  obtain ⟨hl, hc⟩ := LamX_spec LamX_lt_Om1
  have hl0 : 0 < LamX := pos_iff_ne_zero.2 hl.1
  have hρU := upsPt_upsilon hl0
  have hρE : InE (upsilon LamX) := upsPt_inE hρU
  set e := eN (upsilon LamX) with he
  have he0 : e ≠ 0 := (eN_E _).pos.ne'
  have hYX : ∀ μ, IsRestartIdx μ → μ < LamX → OrecY μ = OrecX μ := fun μ hμ hμl =>
    OrecY_eq_OrecX hμ (hμl.trans LamX_lt_LamY) hμl
  apply le_antisymm
  · rw [← eN_sq, OrecY_eq]
    refine csSup_le ⟨1, Set.mem_insert _ _⟩ ?_
    rintro w (rfl | ⟨s, hCB, hcs, rfl⟩)
    · exact one_le_iff_pos.2 (opow_pos _ omega0_pos)
    have hlt : ev2 s (upsilon LamX) < ω ^ (e + e) := by
      by_contra hge
      push Not at hge
      have hbig := (big_iff s hCB).1 hge
      obtain ⟨μ, hμ, -, hμl, h3, h4⟩ := hcs 0 hl0
      have h5 := (big_iff s h3).2 hbig
      rw [hYX μ hμ hμl] at h4
      have h6 := OrecX_lt_top hμ (hμl.trans LamX_lt_Om1) (not_cofX_of_lt hμ hμl)
      exact absurd (h5.trans h4) (not_le.2 h6)
    exact add_one_le_of_lt hlt
  · by_contra hlt
    push Not at hlt
    set X := OrecY LamX with hX
    set q := X / e with hq
    have hqe : q < e := (lt_mul_iff_div_lt he0).1 hlt
    have hq1e : q + 1 < e :=
      (inE_indec (eN_E _)).add_lt hqe (one_lt_omega0.trans (omega0_lt_inE (eN_E _)))
    have h1 : X < e * (q + 1) := by
      have := lt_mul_succ_div X he0
      rwa [succ_eq_add_one] at this
    obtain ⟨t, ct, et⟩ := rep hρE (q + 1) hq1e
    have hcof : CofRealY OrecY LamX (ew (kk t)) := by
      intro ν hν
      obtain ⟨μ, hμ, h2, h3, h4, h5⟩ := hc t ct ν hν
      refine ⟨μ, hμ, h2, h3, h4, ?_⟩
      rw [hYX μ hμ h3]; simpa using h5
    have h2 := lt_OrecY_of_cof (show CBY (ew (kk t)) (upsilon LamX) from ct) hcof
    have h3 : ev2 (ew (kk t)) (upsilon LamX) = e * ω ^ (q + 1) := by
      rw [ev2_ew, ev2_kk, et, ← eN_mul_opow]
    rw [h3] at h2
    have h4 : e * (q + 1) ≤ e * ω ^ (q + 1) := mul_le_mul_right (right_le_opow _ one_lt_omega0) e
    exact absurd ((h1.trans_le h4).trans h2) (lt_irrefl _)

/-- **The reach at `Λ_{ε²}`**: `lh(ρ) = δ + ε_{ρ+1}·ε_{ρ+1}` (`ρ = ρ_{Λ_{ε²}}`). -/
theorem reach_LamX :
    IsReach R2C (upsilon LamX) (upsilon (LamX + ω + 1) + eN (upsilon LamX) * eN (upsilon LamX)) := by
  rw [← OrecY_LamX]
  exact reach_OrecY LamX_ri LamX_lt_LamY

/-! ## Theorem BLK^O at `Λ_{ε_{x+2}}` -/

/-- **The input of Lemma TOP at `Λ_{ε_{x+2}}`**: the offset is the term `ε_{x+2}`, with the IMG package
`RstK.pkg_eNN`. -/
theorem topIn_OrecY_LamY : TopInH OrecY LamY := by
  have hl0 : 0 < LamY := pos_iff_ne_zero.2 LamY_ri.1
  exact ⟨fun x => eN (eN x), 0, OrecY_LamY, (upsPt_upsilon hl0).1,
    fun μ hμ hμl _ => OrecY_lt_top hμ hμl, fun R => R.pkg_eNN⟩

theorem LamY_ww_lt_Om1 : LamY + ω * ω < Om1 := Om1_add_lt LamY_lt_Om1 ww_lt_Om1

/-- **`OrecY` is a general offset specification up to `Λ_{ε_{x+2}} + ω²`** (the block of the restart
`ρ_{Λ_{ε_{x+2}}}` included). -/
theorem specY_LamY : OffSpecGen OrecY (LamY + ω * ω) where
  mult := dvd_add (ri_iff.1 LamY_ri).2 (dvd_refl _)
  cnt := LamY_ww_lt_Om1
  le := fun _ hl hlB => OrecY_lt_δ hl (hlB.trans LamY_ww_lt_Om1)
  one := fun l _ _ => one_le_OrecY l
  top := fun l hl hlB => by
    rcases lt_or_ge l LamY with h | h
    · exact topIn_OrecY hl (OrecY_lt_top hl h)
    · rcases eq_or_lt_of_le h with e | hlt
      · rw [← e]; exact topIn_OrecY_LamY
      · exact absurd hlB (not_lt.2 (next_mult (ri_iff.1 LamY_ri).2 (ri_iff.1 hl).2 hlt))
  succ := fun _ hl _ h2 => OrecY_succ hl h2
  rs := fun _ hl _ h2 => rsIn_OrecY hl h2

/-- **Theorem BLK^O at `Λ_{ε_{x+2}}`**: BLK^O with `OrecY` below `υ_{Λ_{ε_{x+2}}+ω²}`. -/
theorem blk_LamY :
    (∀ c d, c < d → d < upsilon (LamY + ω * ω) → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < LamY + ω * ω ∧
      c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < LamY + ω * ω →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + OrecY l)) ∧
    (∀ α < upsilon (LamY + ω * ω), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  blk_genGen specY_LamY

/-- **The reach at `Λ_{ε_{x+2}}`**: `lh(ρ) = δ + ε_{ρ+2}` (`ρ = ρ_{Λ_{ε_{x+2}}}`). -/
theorem reach_LamY :
    IsReach R2C (upsilon LamY) (upsilon (LamY + ω + 1) + eN (eN (upsilon LamY))) := by
  rw [← OrecY_LamY]
  exact (blk_LamY.2.1 LamY LamY_ri (lt_add_of_pos_right _ (mul_pos omega0_pos omega0_pos))).2.2

/-- **CORE-C at `Λ_{ε_{x+2}}`**: `[0, υ_{Λ_{ε_{x+2}}+ω²}) ⊆ Core(R₂^C)`. -/
theorem core_LamY : Set.Iio (upsilon (LamY + ω * ω)) ⊆ Core R2C := core_genGen specY_LamY

/-- **`ρ_L ≥ υ_{Λ_{ε_{x+2}}+ω²}`**: the left end of the first non-standard pair lies above the block of
`ρ_{Λ_{ε_{x+2}}}`. -/
theorem left_ge_LamY_ww {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlν : upsilon l < nuC)
    (h2 : le2 (upsilon l) nuC) : LamY + ω * ω ≤ l :=
  left_ge_of_spec specY_LamY hl hlν h2

/-! ## Where the first non-standard pair lies -/

/-- **`υ_B ≤ ν_C`** for every `B ≤ Λ_{ε_{x+2}}` (`ω² ∣ B`, `B < Ω₁`). -/
theorem upsY_le_nuC {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ LamY) :
    upsilon B ≤ nuC := by
  refine le_nuC (ups_lt_Om1 B hc).le (fun c d hcd hd h2 => ?_)
  obtain ⟨μ, j, hμ, -, rfl, rfl⟩ := ((blkOY hm hc hB).1 c d hcd hd).1 h2
  exact ⟨μ, j, hμ, rfl, rfl⟩

/-- **The left end of the first non-standard pair lies at or above `ρ_{Λ_{ε_{x+2}}}`**. -/
theorem left_ge_LamY {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlν : upsilon l < nuC)
    (h2 : le2 (upsilon l) nuC) : LamY ≤ l :=
  left_ge_of_spec (specY_of_le (ri_iff.1 LamY_ri).2 LamY_lt_Om1 le_rfl) hl hlν h2

/-- **Where the first non-standard pair lies**: `ρ_L <₂ ν_C = ρ_ξ` with `Λ_{ε_{x+2}} ≤ L < ξ` restart
indices, `υ_{Λ_{ε_{x+2}}} ≤ ρ_L < ν_C < Ω₁`. -/
theorem nuC_boundY : ∃ L ξ, IsRestartIdx L ∧ IsRestartIdx ξ ∧ LamY ≤ L ∧ L < ξ ∧
    upsilon LamY ≤ upsilon L ∧ upsilon L < nuC ∧ nuC = upsilon ξ ∧ nuC < Om1 ∧
    le2 (upsilon L) nuC := by
  obtain ⟨L, ξ, hL, hξ, hLξ, he, h2, -, -, -⟩ := level2_restart
  have hLν : upsilon L < nuC := by rw [he]; exact upsilon_normal.strictMono hLξ
  have hle := left_ge_LamY hL hLν h2
  exact ⟨L, ξ, hL, hξ, hle, hLξ, upsilon_normal.strictMono.monotone hle, hLν, he, nuC_lt_Om1, h2⟩

end Googology.Trans.PoR.InaccPsi.R2

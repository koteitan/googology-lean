import Googology.Trans.PoR.InaccPsi.R2.EpsI
import Googology.Trans.PoR.InaccPsi.R2.EpsLY

/-!
# The recursive offset below `ε_{x+ω}`, Theorem BLK^O up to `Λ_{ε_{x+ω}}`, and the reach at every
frontier `Λ_t`

The project's recursive offset (its paper's Definition 2.2) over the terms `TW` (every Cantor normal form
in `x` and the `ε_{x+n}`, below `ε_{x+ω}`).  `OrecW(λ) = sup ({1} ∪ {s(ρ_λ) + 1 : s realized cofinally
below λ, constants below ρ_λ})`.

* `eW` (`ε_{x+ω} = sup_n ε_{x+n}`), `eK_lt_eW`, `val_lt_eW`, `eW_le_ups`, `eW_lt_Om1`;
* `OrecW`, `OrecW_le` (`OrecW(λ) ≤ ε_{ρ+ω}`), `OrecW_succ`, `LamW` (`Λ_{ε_{x+ω}}`: the least restart index
  with `OrecW(λ) = ε_{ρ_λ+ω}`), `topIn_OrecW` (the input of Lemma TOP, with the IMG package
  `RstK.pkgT`), `rsIn_OrecW` (the input of Lemma RS, `rsStep_W`), `specW`;
* `blkOW` (**Theorem BLK^O with `OrecW` below `υ_B` for every `B ≤ Λ_{ε_{x+ω}}`**), `coreOW`, `LamW_lt_Om1`,
  `reach_OrecW` (`lh(ρ_λ) = δ_λ + OrecW(λ)` for every restart index `λ < Λ_{ε_{x+ω}}`), `OrecW_LamW`;
* `OrecW_eq_OrecY`, `bases_ri`, `ups_ri`;
* `LamT t` (**the frontier of a term `t`**: the least restart index `λ` with `t(ρ_λ) ≤ OrecW(λ)`),
  `OrecW_LamT`, `OrecW_LamT'` (**`OrecW(Λ_t) = t(ρ_{Λ_t})`**: a term realized cofinally below `Λ_t` is below `t`
  there, so below `t` at `ρ_{Λ_t}` by the uniform comparison), `LamT_lt_LamW`, `reach_LamT` (**the
  reach at every frontier**: `lh(ρ_{Λ_t}) = δ + t(ρ_{Λ_t})`), `blk_LamT` (BLK^O below
  `υ_{Λ_t+ω²}`), `LamT_mono`, `LamT_strict`;
* the frontiers of `ε_{x+n}`: `LamY_lt_LamW`, `OrecW_LamY`, `LamT_ep2` (`Λ_{ε_{x+2}}` of `OrecW` is
  `LamY`), `LamT_ep_lt` (`Λ_{ε_{x+n}} < Λ_{ε_{x+n+1}}`), `reach_LamEp` (`lh(ρ) = δ + ε_{ρ+n}` at
  `Λ_{ε_{x+n}}`); of `ε_{x+2}·(m+1) + s`: `e2mul`, `e2m`, `reach_LamE2m`; of `ε_{x+2}·ω`: `e2w`,
  `LamE2w_spec` (`Λ_{ε_{x+2}} < Λ_{ε_{x+2}·ω} < Λ_{ε_{x+3}}`, reach `δ + ε_{ρ+2}·ω`);
* `upsW_le_nuC`, `left_ge_LamW`, `nuC_boundW` (**`υ_{Λ_{ε_{x+ω}}} ≤ ρ_L < ν_C`**).

No new axiom.

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order TW

/-! ## `ε_{x+ω}` -/

/-- `ε_{x+ω} = sup_n ε_{x+n}`. -/
noncomputable def eW (x : Ordinal.{0}) : Ordinal.{0} := ⨆ n : ℕ, eK n x

theorem eK_le_eW (n : ℕ) (x : Ordinal.{0}) : eK n x ≤ eW x := Ordinal.le_iSup (fun n => eK n x) n

theorem eK_lt_eW (n : ℕ) (x : Ordinal.{0}) : eK n x < eW x :=
  (eK_lt_succ n x).trans_le (eK_le_eW (n + 1) x)

theorem lt_eW {x y : Ordinal.{0}} (h : y < eW x) : ∃ n, y < eK n x :=
  Ordinal.lt_iSup_iff.1 h

theorem eW_le {x u : Ordinal.{0}} (h : ∀ n, eK n x ≤ u) : eW x ≤ u := Ordinal.iSup_le h

theorem val_lt_eW {x : Ordinal.{0}} (hx : InE x) {t : TW} (h : CBw t x) : val t x < eW x :=
  (val_lt_eK hx t h).trans (eK_lt_eW _ x)

theorem one_le_eW (x : Ordinal.{0}) : 1 ≤ eW x :=
  one_le_iff_pos.2 (lt_of_lt_of_le (eK_E_succ 0 x).pos (eK_le_eW 1 x))

/-- `ε_{b+ω}` is at most every `υ`-point above a countable `υ`-point `b`. -/
theorem eW_le_ups {b : Ordinal.{0}} (hb : UpsPt b) (hb1 : b < Om1) {u : Ordinal.{0}} (hbu : b < u)
    (hu : UpsPt u) : eW b ≤ u :=
  eW_le (fun n => (eK_lt_ups hb hb1 n u hbu hu).le)

theorem eW_lt_Om1 {x : Ordinal.{0}} (hx : x < Om1) : eW x < Om1 :=
  Ordinal.iSup_lt_omega_one (fun n => eK_lt_Om1 hx n)

/-! ## The recursion -/

/-- `s` is realized cofinally below `λ` by the offsets `O`. -/
def CofRealW (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) (s : TW) : Prop :=
  ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ CBw s (upsilon μ) ∧ val s (upsilon μ) ≤ O μ

/-- The set whose supremum is `OrecW(λ)`. -/
def OSetW (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : Set Ordinal.{0} :=
  insert 1 {w | ∃ s, CBw s (upsilon l) ∧ CofRealW O l s ∧ w = val s (upsilon l) + 1}

theorem OSetW_congr {O O' : Ordinal.{0} → Ordinal.{0}} {l : Ordinal.{0}}
    (h : ∀ μ < l, O μ = O' μ) : OSetW O l = OSetW O' l := by
  have key : ∀ s, CofRealW O l s ↔ CofRealW O' l s := by
    intro s
    constructor
    · intro hc ν hν
      obtain ⟨μ, h1, h2, h3, h4, h5⟩ := hc ν hν
      exact ⟨μ, h1, h2, h3, h4, by rw [← h μ h3]; exact h5⟩
    · intro hc ν hν
      obtain ⟨μ, h1, h2, h3, h4, h5⟩ := hc ν hν
      exact ⟨μ, h1, h2, h3, h4, by rw [h μ h3]; exact h5⟩
  ext w
  simp only [OSetW, Set.mem_insert_iff, Set.mem_setOf_eq, key]

/-- **The recursive offset over `TW`**, by well-founded recursion. -/
noncomputable def OrecW : Ordinal.{0} → Ordinal.{0} :=
  Ordinal.lt_wf.fix (fun l IH => sSup (OSetW (fun μ => if h : μ < l then IH μ h else 0) l))

theorem OrecW_eq (l : Ordinal.{0}) : OrecW l = sSup (OSetW OrecW l) := by
  show Ordinal.lt_wf.fix _ l = _
  rw [WellFounded.fix_eq]
  rw [OSetW_congr (O' := OrecW) (fun μ hμ => by simp only [hμ, dite_true]; rfl)]

theorem OSetW_bdd (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) (hl : InE (upsilon l)) :
    ∀ w ∈ OSetW O l, w ≤ eW (upsilon l) := by
  intro w hw
  rcases hw with rfl | ⟨s, hCB, -, rfl⟩
  · exact one_le_eW _
  · exact add_one_le_of_lt (val_lt_eW hl hCB)

theorem OSetW_bddAbove (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) (hl : InE (upsilon l)) :
    BddAbove (OSetW O l) := ⟨_, OSetW_bdd O l hl⟩

theorem ups_inE {l : Ordinal.{0}} (hl : IsRestartIdx l) : InE (upsilon l) :=
  upsPt_inE (upsPt_upsilon (pos_iff_ne_zero.2 hl.1))

/-- `OrecW(λ) ≤ ε_{ρ+ω}`. -/
theorem OrecW_le {l : Ordinal.{0}} (hl : IsRestartIdx l) : OrecW l ≤ eW (upsilon l) := by
  rw [OrecW_eq]; exact csSup_le ⟨1, Set.mem_insert _ _⟩ (OSetW_bdd _ l (ups_inE hl))

theorem one_le_OrecW {l : Ordinal.{0}} (hl : IsRestartIdx l) : 1 ≤ OrecW l := by
  rw [OrecW_eq]; exact le_csSup (OSetW_bddAbove _ l (ups_inE hl)) (Set.mem_insert _ _)

theorem lt_OrecW_of_cof {l : Ordinal.{0}} (hl : IsRestartIdx l) {s : TW} (hCB : CBw s (upsilon l))
    (hc : CofRealW OrecW l s) : val s (upsilon l) < OrecW l := by
  have h1 : val s (upsilon l) + 1 ≤ OrecW l := by
    rw [OrecW_eq]
    exact le_csSup (OSetW_bddAbove _ l (ups_inE hl)) (Set.mem_insert_of_mem _ ⟨s, hCB, hc, rfl⟩)
  exact lt_of_lt_of_le (lt_add_one _) h1

theorem lt_OrecW {l z : Ordinal.{0}} (hl : IsRestartIdx l) (hz : z < OrecW l) :
    z = 0 ∨ ∃ s, CBw s (upsilon l) ∧ CofRealW OrecW l s ∧ z ≤ val s (upsilon l) := by
  rw [OrecW_eq] at hz
  obtain ⟨w, hw, hzw⟩ :=
    (lt_csSup_iff (OSetW_bddAbove _ l (ups_inE hl)) ⟨1, Set.mem_insert _ _⟩).1 hz
  rcases hw with rfl | ⟨s, hCB, hc, rfl⟩
  · left; exact le_antisymm (Order.lt_add_one_iff.1 (by rw [zero_add]; exact hzw)) zero_le
  · right; exact ⟨s, hCB, hc, Order.lt_add_one_iff.1 hzw⟩

/-- `OrecW = 1` at a successor restart index. -/
theorem OrecW_succ {l : Ordinal.{0}} (hl : IsRestartIdx l) (h2 : cL l < 2) : OrecW l = 1 := by
  obtain ⟨l0, hl0, rfl⟩ := succ_ri hl h2
  have hww : 0 < ω * ω := mul_pos omega0_pos omega0_pos
  have hS : OSetW OrecW (l0 + ω * ω) = {1} := by
    ext w
    simp only [OSetW, Set.mem_insert_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro (h | ⟨s, -, hc, -⟩)
      · exact h
      · exfalso
        obtain ⟨μ, hμ, h1, h3, -, -⟩ := hc l0 (lt_add_of_pos_right l0 hww)
        exact absurd h3 (not_lt.2 (next_mult (mult_of hl0) (ri_iff.1 hμ).2 h1))
    · intro h; exact Or.inl h
  rw [OrecW_eq, hS, csSup_singleton]

/-! ## The frontier `Λ_{ε_{x+ω}}` -/

/-- `Λ_{ε_{x+ω}}`: the least restart index `λ` with `OrecW(λ) = ε_{ρ_λ+ω}` (`Ω₁` if there is none). -/
noncomputable def LamW : Ordinal.{0} :=
  sInf (insert Om1 {l | IsRestartIdx l ∧ OrecW l = eW (upsilon l)})

theorem LamW_le_Om1 : LamW ≤ Om1 := csInf_le (OrderBot.bddBelow _) (Set.mem_insert _ _)

/-- **Below `Λ_{ε_{x+ω}}` the value is `< ε_{ρ+ω}`.** -/
theorem OrecW_lt_top {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlW : l < LamW) :
    OrecW l < eW (upsilon l) := by
  rcases (OrecW_le hl).lt_or_eq with h | h
  · exact h
  · exact absurd (csInf_le (OrderBot.bddBelow _) (Set.mem_insert_of_mem _
      (show l ∈ {l | IsRestartIdx l ∧ OrecW l = eW (upsilon l)} from ⟨hl, h⟩)))
      (not_le.2 hlW)

theorem LamW_spec (h : LamW < Om1) : IsRestartIdx LamW ∧ OrecW LamW = eW (upsilon LamW) := by
  rcases csInf_mem (s := insert Om1 {l | IsRestartIdx l ∧ OrecW l = eW (upsilon l)})
    ⟨Om1, Set.mem_insert _ _⟩ with h' | h'
  · exact absurd (h' ▸ h : Om1 < Om1) (lt_irrefl _)
  · exact h'

/-! ## The inputs of Lemmas TOP and RS -/

/-- **The input of Lemma TOP** at a restart index `λ` with `OrecW(λ) < ε_{ρ+ω}`. -/
theorem topIn_OrecW {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlt : OrecW l < eW (upsilon l)) :
    TopInH OrecW l := by
  classical
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρU := upsPt_upsilon hl0
  have hρE : InE (upsilon l) := upsPt_inE hρU
  have hone : 1 ≤ OrecW l := one_le_OrecW hl
  obtain ⟨N, hN⟩ := lt_eW hlt
  have hN' : OrecW l < eK (N + 1) (upsilon l) := hN.trans (eK_lt_succ N _)
  obtain ⟨s, hCB, hev⟩ := repW hρE N _ hN'
  have hpk : RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1)) →
      ImgPkg (upsilon l) (upsilon (l + ω + 1)) (val s) := fun R =>
    R.pkgT hCB (by rw [hev]; exact hone)
  have hnot : ¬ CofRealW OrecW l s := fun hc =>
    absurd (lt_OrecW_of_cof hl hCB hc) (by rw [hev]; exact lt_irrefl _)
  obtain ⟨m0, hm0, hm0c⟩ := list_max (csw s) _ ((cbw_iff s _).1 hCB) hρU.1
  unfold CofRealW at hnot
  push Not at hnot
  obtain ⟨ν, hνl, hν⟩ := hnot
  have hνρ : upsilon ν < upsilon l := upsilon_normal.strictMono hνl
  refine ⟨val s, max (upsilon ν) m0, hev.symm, max_lt hνρ hm0, fun μ hμ hμl hx0 => ?_, hpk⟩
  have hνμ : ν < μ := upsilon_normal.strictMono.lt_iff_lt.1 (lt_of_le_of_lt (le_max_left _ _) hx0)
  have hCBμ : CBw s (upsilon μ) :=
    (cbw_iff s _).2 (fun c hc => lt_of_le_of_lt ((hm0c c hc).trans (le_max_right _ _)) hx0)
  exact hν μ hμ hνμ hμl hCBμ

/-- **The input of Lemma RS at a limit restart index `λ`** for `OrecW`. -/
theorem rsIn_OrecW {l : Ordinal.{0}} (hl : IsRestartIdx l) (h2 : 2 ≤ cL l) : RsInGen OrecW l := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρ0 : 0 < upsilon l := (upsPt_upsilon hl0).1
  intro z hz
  rcases lt_OrecW hl hz with rfl | ⟨s, hCB, hc, hzs⟩
  · refine ⟨OT.ev (OT.k 0), zero_le, fun R htg => rs_rstT R hρ0 htg, fun ν hν => ?_⟩
    obtain ⟨μ, hμ, h1, h3, -⟩ := cL_dense hl le_rfl (lt_of_lt_of_le one_lt_two h2) ν hν
    exact ⟨μ, hμ, h1, h3, by rw [OT.ev_k]; exact zero_le⟩
  · refine ⟨val s, hzs, rsStep_W hCB, fun ν hν => ?_⟩
    obtain ⟨μ, hμ, h1, h3, -, h5⟩ := hc ν hν
    exact ⟨μ, hμ, h1, h3, h5⟩

theorem OrecW_lt_δ {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) :
    OrecW l < upsilon (l + ω + 1) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρU := upsPt_upsilon hl0
  have h1 : l < l + ω := lt_add_of_pos_right l omega0_pos
  have hτU := upsPt_upsilon (hl0.trans h1)
  exact lt_of_le_of_lt ((OrecW_le hl).trans
    (eW_le_ups hρU (ups_lt_Om1 l hl1) (upsilon_normal.strictMono h1) hτU))
    (upsilon_normal.strictMono (lt_add_one _))

/-- **`OrecW` is a general offset specification up to `B`** when every restart index below `B` has
`OrecW < ε_{ρ+ω}`. -/
theorem specW {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1)
    (hB : ∀ l, IsRestartIdx l → l < B → OrecW l < eW (upsilon l)) : OffSpecGen OrecW B where
  mult := hm
  cnt := hc
  le := fun _ hl hlB => OrecW_lt_δ hl (hlB.trans hc)
  one := fun _ hl _ => one_le_OrecW hl
  top := fun l hl hlB => topIn_OrecW hl (hB l hl hlB)
  succ := fun _ hl _ h2 => OrecW_succ hl h2
  rs := fun _ hl _ h2 => rsIn_OrecW hl h2

theorem specW_of_le {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ LamW) :
    OffSpecGen OrecW B :=
  specW hm hc (fun _ hl hlB => OrecW_lt_top hl (lt_of_lt_of_le hlB hB))

/-! ## Theorem BLK^O up to `Λ_{ε_{x+ω}}` -/

/-- **Theorem BLK^O with `OrecW` below `υ_B` for every `B ≤ Λ_{ε_{x+ω}}`** (`ω² ∣ B`, `B < Ω₁`) in
`R₂^C`: (i) the `<₂`-pairs with right end below `υ_B` are the standard pairs; (ii) every restart `ρ_λ`
(`λ < B`) has no `<₁`-predecessor, no `<₂`-successor, and reach `δ_λ + OrecW(λ)`; (iii) every point below
`υ_B` that is not a `υ`-point has its `R₁⁺` reach. -/
theorem blkOW {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ LamW) :
    (∀ c d, c < d → d < upsilon B → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < B ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < B →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + OrecW l)) ∧
    (∀ α < upsilon B, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  blk_genGen (specW_of_le hm hc hB)

/-- **CORE-C up to `Λ_{ε_{x+ω}}`**: `[0, υ_B) ⊆ Core(R₂^C)` for every `B ≤ Λ_{ε_{x+ω}}`. -/
theorem coreOW {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ LamW) :
    Set.Iio (upsilon B) ⊆ Core R2C :=
  core_genGen (specW_of_le hm hc hB)

/-- **`Λ_{ε_{x+ω}} < Ω₁`** (the core is countable, [C09] Cor 15.15). -/
theorem LamW_lt_Om1 : LamW < Om1 := by
  rcases LamW_le_Om1.lt_or_eq with h | h
  · exact h
  · exfalso
    exact not_core_all (fun B hm hc => coreOW hm hc (by rw [h]; exact hc.le))

theorem LamW_ri : IsRestartIdx LamW := (LamW_spec LamW_lt_Om1).1

/-- **`OrecW(Λ_{ε_{x+ω}}) = ε_{ρ+ω}`**. -/
theorem OrecW_LamW : OrecW LamW = eW (upsilon LamW) := (LamW_spec LamW_lt_Om1).2

/-- **The exact reach of every restart below `Λ_{ε_{x+ω}}`** in `R₂^C`: `lh(ρ_λ) = δ_λ + OrecW(λ)`. -/
theorem reach_OrecW {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlW : l < LamW) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + OrecW l) :=
  (blkOW (ri_iff.1 LamW_ri).2 LamW_lt_Om1 le_rfl).2.1 l hl hlW |>.2.2

/-! ## Comparing with `OrecY` -/

/-- **`OrecW = OrecY` below both frontiers** (the reach is unique). -/
theorem OrecW_eq_OrecY {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlW : l < LamW) (hlY : l < LamY) :
    OrecW l = OrecY l :=
  (add_left_cancel_iff).1 (isReach_unique (reach_OrecW hl hlW) (reach_OrecY hl hlY))

/-- Bases at two restart indices `μ < λ < Ω₁`. -/
theorem bases_ri {μ l : Ordinal.{0}} (hμ : IsRestartIdx μ) (hl : IsRestartIdx l) (hμl : μ < l)
    (hl1 : l < Om1) : Bases (upsilon μ) (upsilon l) :=
  ⟨ups_inE hμ, ups_inE hl, upsilon_normal.strictMono hμl, ups_lt_Om1 l hl1⟩

theorem ups_ri {l : Ordinal.{0}} (hl : IsRestartIdx l) : UpsPt (upsilon l) :=
  upsPt_upsilon (pos_iff_ne_zero.2 hl.1)

/-! ## The frontier of a term -/

/-- **The frontier `Λ_t` of a term `t`**: the least restart index `λ` with constants of `t` below
`ρ_λ` and `t(ρ_λ) ≤ OrecW(λ)` (`Ω₁` if there is none). -/
noncomputable def LamT (t : TW) : Ordinal.{0} :=
  sInf (insert Om1 {l | IsRestartIdx l ∧ CBw t (upsilon l) ∧ val t (upsilon l) ≤ OrecW l})

theorem LamT_le {t : TW} {l : Ordinal.{0}} (hl : IsRestartIdx l) (hCB : CBw t (upsilon l))
    (hle : val t (upsilon l) ≤ OrecW l) : LamT t ≤ l :=
  csInf_le (OrderBot.bddBelow _) (Set.mem_insert_of_mem _ ⟨hl, hCB, hle⟩)

theorem LamT_spec {t : TW} (h : LamT t < Om1) :
    IsRestartIdx (LamT t) ∧ CBw t (upsilon (LamT t)) ∧ val t (upsilon (LamT t)) ≤ OrecW (LamT t) := by
  rcases csInf_mem (s := insert Om1
    {l | IsRestartIdx l ∧ CBw t (upsilon l) ∧ val t (upsilon l) ≤ OrecW l})
    ⟨Om1, Set.mem_insert _ _⟩ with h' | h'
  · exact absurd (h' ▸ h : Om1 < Om1) (lt_irrefl _)
  · exact h'

/-- Below `Λ_t` the term is not reached. -/
theorem lt_val_of_lt_LamT {t : TW} {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (hμl : μ < LamT t)
    (hCB : CBw t (upsilon μ)) : OrecW μ < val t (upsilon μ) := by
  by_contra hle
  exact absurd (LamT_le hμ hCB (not_lt.1 hle)) (not_le.2 hμl)

/-- **`OrecW(Λ_t) = t(ρ_{Λ_t})`** (for `Λ_t < Ω₁` and `t(ρ_{Λ_t}) ≥ 1`): a term `s` realized cofinally below
`Λ_t` has `s(ρ_μ) ≤ OrecW(μ) < t(ρ_μ)` for restarts `μ` above the constants of `t`, so `s(ρ) < t(ρ)` at
`ρ = ρ_{Λ_t}` by the uniform comparison (`uniW_lt`). -/
theorem OrecW_LamT {t : TW} (hlt : LamT t < Om1) (h1 : 1 ≤ val t (upsilon (LamT t))) :
    OrecW (LamT t) = val t (upsilon (LamT t)) := by
  obtain ⟨hl, hCB, hle⟩ := LamT_spec hlt
  set l := LamT t with hldef
  refine le_antisymm ?_ hle
  have hρU := ups_ri hl
  obtain ⟨m0, hm0, hm0c⟩ := list_max (csw t) _ ((cbw_iff t _).1 hCB) hρU.1
  obtain ⟨_, ⟨ν, hν, rfl⟩, hm0ν⟩ := (lt_isLUB_iff (upsilon_limit (ri_limit hl))).1 hm0
  rw [OrecW_eq]
  refine csSup_le ⟨1, Set.mem_insert _ _⟩ ?_
  rintro w (rfl | ⟨s, hsCB, hc, rfl⟩)
  · exact h1
  obtain ⟨μ, hμ, hνμ, hμl, hCBμ, hsμ⟩ := hc ν hν
  have hm0μ : m0 < upsilon μ := hm0ν.trans (upsilon_normal.strictMono hνμ)
  have htμ : CBw t (upsilon μ) := (cbw_iff t _).2 (fun c hc => lt_of_le_of_lt (hm0c c hc) hm0μ)
  have h2 : val s (upsilon μ) < val t (upsilon μ) := lt_of_le_of_lt hsμ (lt_val_of_lt_LamT hμ hμl htμ)
  have h3 := (uniW_lt (ups_ri hμ) hρU (bases_ri hμ hl hμl hlt) hCBμ htμ).2 h2
  exact add_one_le_of_lt h3

/-- **`Λ_t < Λ_{ε_{x+ω}}`** for every term `t` with constants below `ρ_{Λ_{ε_{x+ω}}}` and value `≥ 1`. -/
theorem LamT_lt_LamW {t : TW} (hCB : CBw t (upsilon LamW)) (h1 : 1 ≤ val t (upsilon LamW)) :
    LamT t < LamW := by
  have hle : LamT t ≤ LamW := LamT_le LamW_ri hCB (by
    rw [OrecW_LamW]; exact (val_lt_eW (ups_inE LamW_ri) hCB).le)
  refine lt_of_le_of_ne hle (fun e => ?_)
  have hlt : LamT t < Om1 := e ▸ LamW_lt_Om1
  have h := OrecW_LamT hlt (by rw [e]; exact h1)
  rw [e, OrecW_LamW] at h
  exact absurd h (val_lt_eW (ups_inE LamW_ri) hCB).ne'

theorem LamT_ri {t : TW} (hCB : CBw t (upsilon LamW)) (h1 : 1 ≤ val t (upsilon LamW)) :
    IsRestartIdx (LamT t) :=
  (LamT_spec ((LamT_lt_LamW hCB h1).trans LamW_lt_Om1)).1

/-- The value `≥ 1` moves from `ρ_{Λ_{ε_{x+ω}}}` down to `ρ_{Λ_t}` (uniform comparison). -/
theorem one_le_val_LamT {t : TW} (hCB : CBw t (upsilon LamW)) (h1 : 1 ≤ val t (upsilon LamW)) :
    1 ≤ val t (upsilon (LamT t)) := by
  have hlt := LamT_lt_LamW hCB h1
  obtain ⟨hl, hCBl, -⟩ := LamT_spec (hlt.trans LamW_lt_Om1)
  have hB := bases_ri hl LamW_ri hlt LamW_lt_Om1
  have h1' : (1 : Ordinal.{0}) < upsilon (LamT t) := one_lt_of_upsPt (ups_ri hl)
  have := (uniW_le (t := cst 1) (u := t) (ups_ri hl) (ups_ri LamW_ri) hB h1' hCBl).1 h1
  exact this

/-- **`OrecW(Λ_t) = t(ρ_{Λ_t})`** for every term `t` with constants below `ρ_{Λ_{ε_{x+ω}}}` and value
`≥ 1`. -/
theorem OrecW_LamT' {t : TW} (hCB : CBw t (upsilon LamW)) (h1 : 1 ≤ val t (upsilon LamW)) :
    OrecW (LamT t) = val t (upsilon (LamT t)) :=
  OrecW_LamT ((LamT_lt_LamW hCB h1).trans LamW_lt_Om1) (one_le_val_LamT hCB h1)

/-- **The reach at the frontier of every term**: `lh(ρ_{Λ_t}) = δ + t(ρ_{Λ_t})` in `R₂^C`. -/
theorem reach_LamT {t : TW} (hCB : CBw t (upsilon LamW)) (h1 : 1 ≤ val t (upsilon LamW)) :
    IsReach R2C (upsilon (LamT t)) (upsilon (LamT t + ω + 1) + val t (upsilon (LamT t))) := by
  rw [← OrecW_LamT' hCB h1]
  exact reach_OrecW (LamT_ri hCB h1) (LamT_lt_LamW hCB h1)

theorem LamT_ww_le_LamW {t : TW} (hCB : CBw t (upsilon LamW)) (h1 : 1 ≤ val t (upsilon LamW)) :
    LamT t + ω * ω ≤ LamW :=
  next_mult (ri_iff.1 (LamT_ri hCB h1)).2 (ri_iff.1 LamW_ri).2 (LamT_lt_LamW hCB h1)

/-- **Theorem BLK^O at the frontier of every term**: BLK^O with `OrecW` below `υ_{Λ_t+ω²}`. -/
theorem blk_LamT {t : TW} (hCB : CBw t (upsilon LamW)) (h1 : 1 ≤ val t (upsilon LamW)) :
    (∀ c d, c < d → d < upsilon (LamT t + ω * ω) → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < LamT t + ω * ω ∧
      c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < LamT t + ω * ω →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + OrecW l)) ∧
    (∀ α < upsilon (LamT t + ω * ω), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  blkOW (dvd_add (ri_iff.1 (LamT_ri hCB h1)).2 (dvd_refl _))
    ((LamT_ww_le_LamW hCB h1).trans_lt LamW_lt_Om1) (LamT_ww_le_LamW hCB h1)

/-- **Monotonicity of the frontier**: if `t ≤ t'` at `ρ_{Λ_{ε_{x+ω}}}` (constants below it, those of `t`
also below `ρ_{Λ_{t'}}`), then `Λ_t ≤ Λ_{t'}`; if `t < t'` there, then `Λ_t < Λ_{t'}` (`LamT_strict`). -/
theorem LamT_mono {t t' : TW} (hCB' : CBw t' (upsilon LamW))
    (h1 : 1 ≤ val t (upsilon LamW)) (hle : val t (upsilon LamW) ≤ val t' (upsilon LamW))
    (hc : CBw t (upsilon (LamT t'))) : LamT t ≤ LamT t' := by
  have h1' : 1 ≤ val t' (upsilon LamW) := h1.trans hle
  have hlt' := LamT_lt_LamW hCB' h1'
  obtain ⟨hl', hCBl', hle'⟩ := LamT_spec (hlt'.trans LamW_lt_Om1)
  have hB := bases_ri hl' LamW_ri hlt' LamW_lt_Om1
  have hle2 := (uniW_le (ups_ri hl') (ups_ri LamW_ri) hB hc hCBl').1 hle
  exact LamT_le hl' hc (hle2.trans hle')

theorem LamT_strict {t t' : TW} (hCB : CBw t (upsilon LamW)) (hCB' : CBw t' (upsilon LamW))
    (h1 : 1 ≤ val t (upsilon LamW)) (hlt : val t (upsilon LamW) < val t' (upsilon LamW))
    (hc : CBw t (upsilon (LamT t'))) : LamT t < LamT t' := by
  refine lt_of_le_of_ne (LamT_mono hCB' h1 hlt.le hc) (fun e => ?_)
  have h1' : 1 ≤ val t' (upsilon LamW) := h1.trans hlt.le
  have hl' := LamT_lt_LamW hCB' h1'
  obtain ⟨hlr, hCBl', hle'⟩ := LamT_spec (hl'.trans LamW_lt_Om1)
  have hB := bases_ri hlr LamW_ri hl' LamW_lt_Om1
  have h2 := (uniW_lt (ups_ri hlr) (ups_ri LamW_ri) hB hc hCBl').1 hlt
  have h3 := OrecW_LamT' hCB h1
  rw [e] at h3
  rw [h3] at hle'
  exact absurd hle' (not_le.2 h2)

/-! ## The frontiers of `ε_{x+n}` -/

theorem one_le_eK (n : ℕ) {x : Ordinal.{0}} (hx : 1 ≤ x) : 1 ≤ eK n x := hx.trans (le_eK n x)

theorem one_le_ups_ri {l : Ordinal.{0}} (hl : IsRestartIdx l) : 1 ≤ upsilon l :=
  (one_lt_of_upsPt (ups_ri hl)).le

/-- **`Λ_{ε_{x+n}} < Λ_{ε_{x+n+1}}`**. -/
theorem LamT_ep_lt (n : ℕ) : LamT (ep n) < LamT (ep (n + 1)) :=
  LamT_strict trivial trivial (one_le_eK n (one_le_ups_ri LamW_ri)) (eK_lt_succ n _) trivial

/-- **The reach at `Λ_{ε_{x+n}}`**: `lh(ρ) = δ + ε_{ρ+n}` (`ρ = ρ_{Λ_{ε_{x+n}}}`), and `Λ_{ε_{x+n}} <
Λ_{ε_{x+ω}}`. -/
theorem reach_LamEp (n : ℕ) :
    IsReach R2C (upsilon (LamT (ep n))) (upsilon (LamT (ep n) + ω + 1) + eK n (upsilon (LamT (ep n)))) ∧
      OrecW (LamT (ep n)) = eK n (upsilon (LamT (ep n))) ∧ LamT (ep n) < LamW :=
  ⟨reach_LamT trivial (one_le_eK n (one_le_ups_ri LamW_ri)),
    OrecW_LamT' trivial (one_le_eK n (one_le_ups_ri LamW_ri)),
    LamT_lt_LamW trivial (one_le_eK n (one_le_ups_ri LamW_ri))⟩

/-- **`Λ_{ε_{x+2}} < Λ_{ε_{x+ω}}`** (the frontier of `OrecY` is below that of `OrecW`): otherwise every
term realized cofinally below `Λ_{ε_{x+ω}}` is below `ε_{x+2}` there (`OrecW = OrecY < ε_{x+2}`), and
`OrecW(Λ_{ε_{x+ω}}) ≤ ε_{ρ+2}`. -/
theorem LamY_lt_LamW : LamY < LamW := by
  by_contra hle
  push Not at hle
  have hl := LamW_ri
  have hρU := ups_ri hl
  have hz : eK 2 (upsilon LamW) < OrecW LamW := by rw [OrecW_LamW]; exact eK_lt_eW 2 _
  rcases lt_OrecW hl hz with h0 | ⟨s, hCB, hcs, hzs⟩
  · exact absurd h0 (eK_E_succ 1 _).pos.ne'
  obtain ⟨μ, hμ, -, hμl, h3, h4⟩ := hcs 0 (pos_iff_ne_zero.2 hl.1)
  have hμY : μ < LamY := lt_of_lt_of_le hμl hle
  rw [OrecW_eq_OrecY hμ hμl hμY] at h4
  have h5 : val s (upsilon μ) < eK 2 (upsilon μ) := lt_of_le_of_lt h4 (OrecY_lt_top hμ hμY)
  have h6 := (uniW_lt (t := s) (u := ep 2) (ups_ri hμ) hρU (bases_ri hμ hl hμl LamW_lt_Om1) h3
    trivial).2 h5
  exact absurd hzs (not_le.2 h6)

/-- **`OrecW(Λ_{ε_{x+2}}) = ε_{ρ+2} = OrecY(Λ_{ε_{x+2}})`** (the reach at `LamY` is unique). -/
theorem OrecW_LamY : OrecW LamY = eK 2 (upsilon LamY) := by
  have h1 := reach_OrecW LamY_ri LamY_lt_LamW
  have h2 := reach_LamY
  have := (add_left_cancel_iff).1 (isReach_unique h1 h2)
  rw [this]; rfl

/-- **`Λ_{ε_{x+2}}` of `OrecW` is `LamY`.** -/
theorem LamT_ep2 : LamT (ep 2) = LamY := by
  refine le_antisymm (LamT_le LamY_ri trivial (by rw [OrecW_LamY]; rfl)) ?_
  by_contra hlt
  push Not at hlt
  have hW := LamT_lt_LamW (t := ep 2) trivial (one_le_eK 2 (one_le_ups_ri LamW_ri))
  obtain ⟨hl, -, hle⟩ := LamT_spec (hW.trans LamW_lt_Om1)
  rw [OrecW_eq_OrecY hl hW hlt] at hle
  exact absurd hle (not_le.2 (OrecY_lt_top hl hlt))

/-! ## The frontiers of `ε_{x+2}·m + s` and `ε_{x+2}·ω` -/

/-- The term `ε_{x+2}·(m+1)`. -/
def e2mul : ℕ → TW
  | 0 => ep 2
  | m + 1 => sm (e2mul m) (ep 2)

/-- The term `ε_{x+2}·(m+1) + s`. -/
def e2m (m : ℕ) (s : TW) : TW := sm (e2mul m) s

theorem val_e2mul (x : Ordinal.{0}) : ∀ m : ℕ, val (e2mul m) x = eK 2 x * ((m + 1 : ℕ) : Ordinal.{0})
  | 0 => by simp [e2mul]
  | m + 1 => by
    simp only [e2mul, val_sm, val_ep]
    rw [val_e2mul x m, Nat.cast_succ (m + 1), mul_add_one]

theorem CBw_e2mul (x : Ordinal.{0}) : ∀ m : ℕ, CBw (e2mul m) x
  | 0 => trivial
  | m + 1 => ⟨CBw_e2mul x m, trivial⟩

/-- **The reach at the frontier of `ε_{x+2}·(m+1) + s`**: `lh(ρ) = δ + ε_{ρ+2}·(m+1) + s(ρ)`, for every
term `s` with constants below `ρ_{Λ_{ε_{x+ω}}}`. -/
theorem reach_LamE2m (m : ℕ) {s : TW} (hs : CBw s (upsilon LamW)) :
    IsReach R2C (upsilon (LamT (e2m m s)))
      (upsilon (LamT (e2m m s) + ω + 1) + (eK 2 (upsilon (LamT (e2m m s))) * ((m + 1 : ℕ) : Ordinal.{0}) +
        val s (upsilon (LamT (e2m m s))))) ∧ LamY ≤ LamT (e2m m s) ∧ LamT (e2m m s) < LamW := by
  have hCB : CBw (e2m m s) (upsilon LamW) := ⟨CBw_e2mul _ m, hs⟩
  have hv : ∀ x, val (e2m m s) x = eK 2 x * ((m + 1 : ℕ) : Ordinal.{0}) + val s x := fun x => by
    simp only [e2m, val_sm]; rw [val_e2mul]
  have h2le : ∀ x, eK 2 x ≤ val (e2m m s) x := fun x => by
    rw [hv]; exact (le_mul_left _ (by exact_mod_cast Nat.succ_pos m)).trans le_self_add
  have h1 : 1 ≤ val (e2m m s) (upsilon LamW) :=
    (one_le_eK 2 (one_le_ups_ri LamW_ri)).trans (h2le _)
  refine ⟨?_, ?_, LamT_lt_LamW hCB h1⟩
  · have := reach_LamT hCB h1; rwa [hv] at this
  · rw [← LamT_ep2]
    exact LamT_mono hCB (one_le_eK 2 (one_le_ups_ri LamW_ri)) (h2le _) trivial

/-- The term `ε_{x+2}·ω = ω^{ε_{x+2}+1}`. -/
def e2w : TW := atw 2 (cst 1)

/-- **`Λ_{ε_{x+2}} < Λ_{ε_{x+2}·ω} < Λ_{ε_{x+3}}`**, and the reach at `Λ_{ε_{x+2}·ω}` is
`δ + ε_{ρ+2}·ω`. -/
theorem LamE2w_spec :
    LamY < LamT e2w ∧ LamT e2w < LamT (ep 3) ∧
      IsReach R2C (upsilon (LamT e2w)) (upsilon (LamT e2w + ω + 1) + eK 2 (upsilon (LamT e2w)) * ω) := by
  have hρ1 : (1 : Ordinal.{0}) < upsilon LamW := one_lt_of_upsPt (ups_ri LamW_ri)
  have hCB : CBw e2w (upsilon LamW) := CBw_atw.2 hρ1
  have hval : ∀ x, InE x → val e2w x = eK 2 x * ω := fun x hx => by
    simp only [e2w, val_atw, val_cst]
    rw [opow_add, opow_one, eK_E hx]
  have hρE := ups_inE LamW_ri
  have h2 : eK 2 (upsilon LamW) < val e2w (upsilon LamW) := by
    rw [hval _ hρE]
    exact lt_mul_of_one_lt_right (eK_E hρE).pos one_lt_omega0
  have h3 : val e2w (upsilon LamW) < eK 3 (upsilon LamW) := by
    have := val_lt_eK hρE e2w hCB
    simpa [e2w, atw, lv] using this
  have h1 : 1 ≤ val e2w (upsilon LamW) := (one_le_eK 2 (one_le_ups_ri LamW_ri)).trans h2.le
  refine ⟨?_, ?_, ?_⟩
  · rw [← LamT_ep2]
    obtain ⟨hl, hCBl, -⟩ := LamT_spec ((LamT_lt_LamW hCB h1).trans LamW_lt_Om1)
    exact LamT_strict trivial hCB (one_le_eK 2 (one_le_ups_ri LamW_ri)) h2 trivial
  · obtain ⟨hl, -, -⟩ := LamT_spec ((LamT_lt_LamW (t := ep 3) trivial
      (one_le_eK 3 (one_le_ups_ri LamW_ri))).trans LamW_lt_Om1)
    exact LamT_strict hCB trivial h1 h3 (CBw_atw.2 (one_lt_of_upsPt (ups_ri hl)))
  · obtain ⟨hl, -, -⟩ := LamT_spec ((LamT_lt_LamW hCB h1).trans LamW_lt_Om1)
    have := reach_LamT hCB h1
    rwa [hval _ (ups_inE hl)] at this

/-! ## Where the first non-standard pair lies -/

/-- **`υ_B ≤ ν_C`** for every `B ≤ Λ_{ε_{x+ω}}` (`ω² ∣ B`, `B < Ω₁`). -/
theorem upsW_le_nuC {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ LamW) :
    upsilon B ≤ nuC := by
  refine le_nuC (ups_lt_Om1 B hc).le (fun c d hcd hd h2 => ?_)
  obtain ⟨μ, j, hμ, -, rfl, rfl⟩ := ((blkOW hm hc hB).1 c d hcd hd).1 h2
  exact ⟨μ, j, hμ, rfl, rfl⟩

/-- **The left end of the first non-standard pair lies at or above `ρ_{Λ_{ε_{x+ω}}}`**. -/
theorem left_ge_LamW {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlν : upsilon l < nuC)
    (h2 : le2 (upsilon l) nuC) : LamW ≤ l :=
  left_ge_of_spec (specW_of_le (ri_iff.1 LamW_ri).2 LamW_lt_Om1 le_rfl) hl hlν h2

/-- **Where the first non-standard pair lies**: `ρ_L <₂ ν_C = ρ_ξ` with `Λ_{ε_{x+ω}} ≤ L < ξ` restart
indices, `υ_{Λ_{ε_{x+ω}}} ≤ ρ_L < ν_C < Ω₁`. -/
theorem nuC_boundW : ∃ L ξ, IsRestartIdx L ∧ IsRestartIdx ξ ∧ LamW ≤ L ∧ L < ξ ∧
    upsilon LamW ≤ upsilon L ∧ upsilon L < nuC ∧ nuC = upsilon ξ ∧ nuC < Om1 ∧
    le2 (upsilon L) nuC := by
  obtain ⟨L, ξ, hL, hξ, hLξ, he, h2, -, -, -⟩ := level2_restart
  have hLν : upsilon L < nuC := by rw [he]; exact upsilon_normal.strictMono hLξ
  have hle := left_ge_LamW hL hLν h2
  exact ⟨L, ξ, hL, hξ, hle, hLξ, upsilon_normal.strictMono.monotone hle, hLν, he, nuC_lt_Om1, h2⟩

end Googology.Trans.PoR.InaccPsi.R2

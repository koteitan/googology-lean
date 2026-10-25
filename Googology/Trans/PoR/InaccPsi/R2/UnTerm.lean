import Googology.Trans.PoR.InaccPsi.R2.UkTerm

/-!
# Terms with nested level terms, a full normal-form mode and high leaves anywhere

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`UnT` is one term type indexed by `Bool` (`UnT false`: countable terms, `UnT true`: **level terms**), so the
countable leaves of a level may themselves be `ϑ`-terms with level terms, to any depth (`Uk.UkT` and `Uk.UkL` mutual,
e.g. `ϑ^x(Ω₁·ϑ^x(Ω₁·x))`).  Countable terms: `par p`, `add`, `base` (`ϑᵗ(0) = τ`), `th1 s` (`ϑᵗ(1 + s)`), `thc q r`
(`ϑᵗ(Ω₁·q + r)` at a constant level `q`), `thg m G r` (`ϑᵗ(G[τ] + r[τ])` at a level term `G`, **mode** `m`).  Level
terms: `lf c` (a countable leaf), `om b` (`Ω₁·ω^{b[τ]}`), `ad x y`.  The node conditions of `thg m G r` (`Ng`) ask
`Ω₁ ∣ G` (`Gs`), membership, every leaf and `r` below the value, and, by the mode,
* `m = false` (**the head mode** of `Uk.UkT`): no absorption along the head chain (`HbS`) and the head leaf high
  (`Hd`);
* `m = true` (**the normal-form mode**): **every** sum `ad x y` is in Cantor normal form (`FNF`: `x = om b`,
  `y < x·ω`) and **some** leaf is high (`HdE`), e.g. a high leaf in a non-head summand (`Γ = Ω₁² + Ω₁·x`).
A leaf is high over `τ` (`HiC`) if its head (left summands) is `base`, a parameter `≥ τ`, or a `ϑ`-node (its value
is `≥ τ` by [W07a] Lemma 3.30 through `R2.vt_memTwo`).  In both modes `τ ≤ rjDat Γ` follows (`datM`), the condition
`Γ^* ≥ τ` of `R2.ukVt_tr3`.  All operations are proved by one structural recursion over both sorts, carrying the
values of all subterms (`unDownB`, `unUpB`, `unTrAB`, `unTrBB`, `unLeB`).

* `datM` (**the decision `Γ^{*τ} ≥ τ` in both modes**; new: `dat_om_add_r`, `rjDat y ≤ rjDat(Ω₁·ω^b + y)`);
* `unMem`, `unLe`, `unDown`, `unUp`, `unUp_eq`, `unMv`, `unTrA`, `unTrB` (**the `Uk` lemmas for `UnT`**;
  `unTrB` asks the high leaves over `α` (`HdA α`) and the leaves in `T^α`);
* `ofUk` (**`Uk.UkT` embeds, as the head mode**: `ofUk_ev`, `ofUk_map`, `ofUk_WF`, `ofUk_Lv`, `ofUk_Qs`), `ofUbn`.

New definitions: `UnT` and on it `ev`, `map`, `Lv`, `Qs`, `IsOm`, `Gs`, `HbS`, `FNF`, `HiC`, `Hd`, `HdE`, `NfM`,
`HdM`, `Lf`, `WF`, `Nd`, `tr`, `HdA`, `lvs`, `lvq`; `Ng`; `ofUhN`, `ofUkL`, `ofUk`, `ofUbn`.  No new axiom (uses
`R2.ukVt_tr3`, `R2.uhVt_tr`).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Un

open Ordinal Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Uh

/-- Terms over a base, of two sorts: `UnT false` (countable terms) and `UnT true` (level terms). -/
inductive UnT : Bool → Type 1
  | par : Ordinal.{0} → UnT false
  | add : UnT false → UnT false → UnT false
  | base : UnT false
  | th1 : UnT false → UnT false
  | thc : Ordinal.{0} → UnT false → UnT false
  | thg : Bool → UnT true → UnT false → UnT false
  | lf : UnT false → UnT true
  | om : UnT true → UnT true
  | ad : UnT true → UnT true → UnT true

/-- Countable terms. -/
abbrev UnC : Type 1 := UnT false

namespace UnT

instance : Inhabited (UnT false) := ⟨UnT.base⟩

/-- Evaluation over the base `τ`. -/
noncomputable def ev (τ : Ordinal.{0}) : {k : Bool} → UnT k → Ordinal.{0}
  | _, par p => p
  | _, add s t => ev τ s + ev τ t
  | _, base => τ
  | _, th1 s => vt τ (1 + ev τ s)
  | _, thc q r => vt τ (Om1 * q + ev τ r)
  | _, thg _ G r => vt τ (ev τ G + ev τ r)
  | _, lf c => ev τ c
  | _, om b => Om1 * ω ^ ev τ b
  | _, ad x y => ev τ x + ev τ y

/-- Apply `f` to every parameter (the constant levels `q` are kept). -/
def map (f : Ordinal.{0} → Ordinal.{0}) : {k : Bool} → UnT k → UnT k
  | _, par p => par (f p)
  | _, add s t => add (map f s) (map f t)
  | _, base => base
  | _, th1 s => th1 (map f s)
  | _, thc q r => thc q (map f r)
  | _, thg m G r => thg m (map f G) (map f r)
  | _, lf c => lf (map f c)
  | _, om b => om (map f b)
  | _, ad x y => ad (map f x) (map f y)

/-- Every parameter satisfies `P`. -/
def Lv (P : Ordinal.{0} → Prop) : {k : Bool} → UnT k → Prop
  | _, par p => P p
  | _, add s t => Lv P s ∧ Lv P t
  | _, base => True
  | _, th1 s => Lv P s
  | _, thc _ r => Lv P r
  | _, thg _ G r => Lv P G ∧ Lv P r
  | _, lf c => Lv P c
  | _, om b => Lv P b
  | _, ad x y => Lv P x ∧ Lv P y

/-- Every constant level is a level over `κ` (`Uh.UhLev`). -/
def Qs (κ : Ordinal.{0}) : {k : Bool} → UnT k → Prop
  | _, par _ => True
  | _, add s t => Qs κ s ∧ Qs κ t
  | _, base => True
  | _, th1 s => Qs κ s
  | _, thc q r => UhLev κ q ∧ Qs κ r
  | _, thg _ G r => Qs κ G ∧ Qs κ r
  | _, lf c => Qs κ c
  | _, om b => Qs κ b
  | _, ad x y => Qs κ x ∧ Qs κ y

/-- An `om`-node. -/
def IsOm : {k : Bool} → UnT k → Prop
  | _, om _ => True
  | _, _ => False

/-- **The shape of a level**: only `om`- and `ad`-nodes at the top (so `Ω₁ ∣ Γ`). -/
def Gs : {k : Bool} → UnT k → Prop
  | _, om _ => True
  | _, ad x y => Gs x ∧ Gs y
  | _, _ => False

/-- **No absorption of the head** over `τ`: along the head chain every `ad x y` has `x = om b`, `y[τ] < x[τ]·ω`. -/
def HbS (τ : Ordinal.{0}) : {k : Bool} → UnT k → Prop
  | _, om b => HbS τ b
  | _, ad x y => HbS τ x ∧ IsOm x ∧ ev τ y < ev τ x * ω
  | _, _ => True

/-- **Full Cantor normal form** over `τ`: every `ad x y` (at any depth of the level term) has `x = om b` and
`y[τ] < x[τ]·ω`. -/
def FNF (τ : Ordinal.{0}) : {k : Bool} → UnT k → Prop
  | _, om b => FNF τ b
  | _, ad x y => FNF τ x ∧ FNF τ y ∧ IsOm x ∧ ev τ y < ev τ x * ω
  | _, _ => True

/-- **A countable term is high over `τ`**: its head (left summands) is `base`, a parameter `≥ τ` or a `ϑ`-node. -/
def HiC (τ : Ordinal.{0}) : {k : Bool} → UnT k → Prop
  | _, par p => τ ≤ p
  | _, add s _ => HiC τ s
  | _, base => True
  | _, th1 _ => True
  | _, thc _ _ => True
  | _, thg _ _ _ => True
  | _, _ => False

/-- **The head leaf is high** over `τ`. -/
def Hd (τ : Ordinal.{0}) : {k : Bool} → UnT k → Prop
  | _, lf c => HiC τ c
  | _, om b => Hd τ b
  | _, ad x _ => Hd τ x
  | _, _ => False

/-- **Some leaf is high** over `τ`. -/
def HdE (τ : Ordinal.{0}) : {k : Bool} → UnT k → Prop
  | _, lf c => HiC τ c
  | _, om b => HdE τ b
  | _, ad x y => HdE τ x ∨ HdE τ y
  | _, _ => False

/-- The value part of the mode: `HbS` (`m = false`) or `FNF` (`m = true`). -/
def NfM : Bool → Ordinal.{0} → UnT true → Prop
  | false, τ, G => HbS τ G
  | true, τ, G => FNF τ G

/-- The syntactic part of the mode: `Hd` (`m = false`) or `HdE` (`m = true`). -/
def HdM : Bool → Ordinal.{0} → UnT true → Prop
  | false, τ, G => Hd τ G
  | true, τ, G => HdE τ G

/-- Every leaf of a level term satisfies `P` (`True` on countable terms). -/
def Lf (P : UnT false → Prop) : {k : Bool} → UnT k → Prop
  | _, lf c => P c
  | _, om b => Lf P b
  | _, ad x y => Lf P x ∧ Lf P y
  | _, _ => True

end UnT

open UnT

/-- **The node conditions of `thg m G r` over `τ`** (`ρ = r[τ]`, `Γ = G[τ]`). -/
structure Ng (m : Bool) (τ : Ordinal.{0}) (G : UnT true) (ρ : Ordinal.{0}) : Prop where
  r1 : ρ < Om1
  gs : Gs G
  nf : NfM m τ G
  hd : HdM m τ G
  mem : ev τ G + ρ ∈ Tset τ
  bd : Lf (fun c => ev τ c < vt τ (ev τ G + ρ)) G
  rb : ρ < vt τ (ev τ G + ρ)

namespace UnT

/-- The argument bounds over `τ` (countable leaves of levels, countable arguments) and the node conditions. -/
def WF (τ : Ordinal.{0}) : {k : Bool} → UnT k → Prop
  | _, par _ => True
  | _, add s t => WF τ s ∧ WF τ t
  | _, base => True
  | _, th1 s => WF τ s ∧ ev τ s < Om1
  | _, thc _ r => WF τ r ∧ ev τ r < Om1
  | _, thg m G r => WF τ G ∧ WF τ r ∧ Ng m τ G (ev τ r)
  | _, lf c => WF τ c ∧ ev τ c < Om1
  | _, om b => WF τ b
  | _, ad x y => WF τ x ∧ WF τ y

/-- Every node value over `τ` (also inside the level terms) satisfies `P`. -/
def Nd (τ : Ordinal.{0}) (P : Ordinal.{0} → Prop) : {k : Bool} → UnT k → Prop
  | _, par _ => True
  | _, add s t => Nd τ P s ∧ Nd τ P t
  | _, base => True
  | _, th1 s => Nd τ P s
  | _, thc q r => P (vt τ (Om1 * q + ev τ r)) ∧ Nd τ P r
  | _, thg _ G r => P (vt τ (ev τ G + ev τ r)) ∧ Nd τ P G ∧ Nd τ P r
  | _, lf c => Nd τ P c
  | _, om b => Nd τ P b
  | _, ad x y => Nd τ P x ∧ Nd τ P y

/-- **The translation `t^a_b` of [W07a] Def 6.2** (`ϑ^a(0) ↦ a`, `ϑ^a(1 + ξ) ↦ ϑ^b(1 + a + ξ)`,
`ϑ^a(Ω₁·q + ρ) ↦ ϑ^b(Ω₁·q + a + ρ)`, `ϑ^a(Γ + ρ) ↦ ϑ^b(Γ + ρ)` with the leaves of `Γ` translated). -/
def tr (a : Ordinal.{0}) : {k : Bool} → UnT k → UnT k
  | _, par p => par p
  | _, add s t => add (tr a s) (tr a t)
  | _, base => par a
  | _, th1 s => th1 (add (par a) (tr a s))
  | _, thc q r => thc q (add (par a) (tr a r))
  | _, thg m G r => thg m (tr a G) (tr a r)
  | _, lf c => lf (tr a c)
  | _, om b => om (tr a b)
  | _, ad x y => ad (tr a x) (tr a y)

/-- The syntactic mode condition `HdM` at every `thg`-node. -/
def HdA (τ : Ordinal.{0}) : {k : Bool} → UnT k → Prop
  | _, par _ => True
  | _, add s t => HdA τ s ∧ HdA τ t
  | _, base => True
  | _, th1 s => HdA τ s
  | _, thc _ r => HdA τ r
  | _, thg m G r => HdM m τ G ∧ HdA τ G ∧ HdA τ r
  | _, lf c => HdA τ c
  | _, om b => HdA τ b
  | _, ad x y => HdA τ x ∧ HdA τ y

/-! ### Structural lemmas -/

theorem Lv_mono {P Q : Ordinal.{0} → Prop} (hPQ : ∀ p, P p → Q p) : ∀ {k : Bool} (t : UnT k), Lv P t → Lv Q t
  | _, par p, h => hPQ p h
  | _, add s t, h => ⟨Lv_mono hPQ s h.1, Lv_mono hPQ t h.2⟩
  | _, base, _ => trivial
  | _, th1 s, h => Lv_mono hPQ s h
  | _, thc _ r, h => Lv_mono hPQ r h
  | _, thg _ G r, h => ⟨Lv_mono hPQ G h.1, Lv_mono hPQ r h.2⟩
  | _, lf c, h => Lv_mono hPQ c h
  | _, om b, h => Lv_mono hPQ b h
  | _, ad x y, h => ⟨Lv_mono hPQ x h.1, Lv_mono hPQ y h.2⟩

theorem Nd_mono {τ : Ordinal.{0}} {P Q : Ordinal.{0} → Prop} (hPQ : ∀ p, P p → Q p) :
    ∀ {k : Bool} (t : UnT k), Nd τ P t → Nd τ Q t
  | _, par _, _ => trivial
  | _, add s t, h => ⟨Nd_mono hPQ s h.1, Nd_mono hPQ t h.2⟩
  | _, base, _ => trivial
  | _, th1 s, h => Nd_mono hPQ s h
  | _, thc _ r, h => ⟨hPQ _ h.1, Nd_mono hPQ r h.2⟩
  | _, thg _ G r, h => ⟨hPQ _ h.1, Nd_mono hPQ G h.2.1, Nd_mono hPQ r h.2.2⟩
  | _, lf c, h => Nd_mono hPQ c h
  | _, om b, h => Nd_mono hPQ b h
  | _, ad x y, h => ⟨Nd_mono hPQ x h.1, Nd_mono hPQ y h.2⟩

theorem Lf_mono {P Q : UnT false → Prop} (hPQ : ∀ c, P c → Q c) : ∀ {k : Bool} (t : UnT k), Lf P t → Lf Q t
  | _, par _, _ => trivial
  | _, add _ _, _ => trivial
  | _, base, _ => trivial
  | _, th1 _, _ => trivial
  | _, thc _ _, _ => trivial
  | _, thg _ _ _, _ => trivial
  | _, lf c, h => hPQ c h
  | _, om b, h => Lf_mono hPQ b h
  | _, ad x y, h => ⟨Lf_mono hPQ x h.1, Lf_mono hPQ y h.2⟩

/-- On a countable term `Lf` holds trivially. -/
theorem Lf_cnt (P : UnT false → Prop) : ∀ (c : UnT false), Lf P c
  | par _ => trivial
  | add _ _ => trivial
  | base => trivial
  | th1 _ => trivial
  | thc _ _ => trivial
  | thg _ _ _ => trivial

theorem map_map (f g : Ordinal.{0} → Ordinal.{0}) : ∀ {k : Bool} (t : UnT k), (t.map g).map f = t.map (f ∘ g)
  | _, par _ => rfl
  | _, add s t => by simp only [map, map_map f g s, map_map f g t]
  | _, base => rfl
  | _, th1 s => by simp only [map, map_map f g s]
  | _, thc _ r => by simp only [map, map_map f g r]
  | _, thg _ G r => by simp only [map, map_map f g G, map_map f g r]
  | _, lf c => by simp only [map, map_map f g c]
  | _, om b => by simp only [map, map_map f g b]
  | _, ad x y => by simp only [map, map_map f g x, map_map f g y]

theorem map_congr {f g : Ordinal.{0} → Ordinal.{0}} :
    ∀ {k : Bool} (t : UnT k), Lv (fun p => f p = g p) t → t.map f = t.map g
  | _, par _, h => by simp only [map]; rw [show _ = _ from h]
  | _, add s t, h => by simp only [map, map_congr s h.1, map_congr t h.2]
  | _, base, _ => rfl
  | _, th1 s, h => by simp only [map, map_congr s h]
  | _, thc _ r, h => by simp only [map, map_congr r h]
  | _, thg _ G r, h => by simp only [map, map_congr G h.1, map_congr r h.2]
  | _, lf c, h => by simp only [map, map_congr c h]
  | _, om b, h => by simp only [map, map_congr b h]
  | _, ad x y, h => by simp only [map, map_congr x h.1, map_congr y h.2]

theorem map_id : ∀ {k : Bool} (t : UnT k), t.map id = t
  | _, par _ => rfl
  | _, add s t => by simp only [map, map_id s, map_id t]
  | _, base => rfl
  | _, th1 s => by simp only [map, map_id s]
  | _, thc _ r => by simp only [map, map_id r]
  | _, thg _ G r => by simp only [map, map_id G, map_id r]
  | _, lf c => by simp only [map, map_id c]
  | _, om b => by simp only [map, map_id b]
  | _, ad x y => by simp only [map, map_id x, map_id y]

theorem Lv_and {P Q : Ordinal.{0} → Prop} :
    ∀ {k : Bool} (t : UnT k), Lv P t → Lv Q t → Lv (fun p => P p ∧ Q p) t
  | _, par _, h1, h2 => ⟨h1, h2⟩
  | _, add s t, h1, h2 => ⟨Lv_and s h1.1 h2.1, Lv_and t h1.2 h2.2⟩
  | _, base, _, _ => trivial
  | _, th1 s, h1, h2 => Lv_and s h1 h2
  | _, thc _ r, h1, h2 => Lv_and r h1 h2
  | _, thg _ G r, h1, h2 => ⟨Lv_and G h1.1 h2.1, Lv_and r h1.2 h2.2⟩
  | _, lf c, h1, h2 => Lv_and c h1 h2
  | _, om b, h1, h2 => Lv_and b h1 h2
  | _, ad x y, h1, h2 => ⟨Lv_and x h1.1 h2.1, Lv_and y h1.2 h2.2⟩

theorem Lv_map {P : Ordinal.{0} → Prop} {f : Ordinal.{0} → Ordinal.{0}} :
    ∀ {k : Bool} (t : UnT k), Lv (fun p => P (f p)) t → Lv P (t.map f)
  | _, par _, h => h
  | _, add s t, h => ⟨Lv_map s h.1, Lv_map t h.2⟩
  | _, base, _ => trivial
  | _, th1 s, h => Lv_map s h
  | _, thc _ r, h => Lv_map r h
  | _, thg _ G r, h => ⟨Lv_map G h.1, Lv_map r h.2⟩
  | _, lf c, h => Lv_map c h
  | _, om b, h => Lv_map b h
  | _, ad x y, h => ⟨Lv_map x h.1, Lv_map y h.2⟩

theorem Qs_map {κ : Ordinal.{0}} (f : Ordinal.{0} → Ordinal.{0}) : ∀ {k : Bool} (t : UnT k), Qs κ t → Qs κ (t.map f)
  | _, par _, _ => trivial
  | _, add s t, h => ⟨Qs_map f s h.1, Qs_map f t h.2⟩
  | _, base, _ => trivial
  | _, th1 s, h => Qs_map f s h
  | _, thc _ r, h => ⟨h.1, Qs_map f r h.2⟩
  | _, thg _ G r, h => ⟨Qs_map f G h.1, Qs_map f r h.2⟩
  | _, lf c, h => Qs_map f c h
  | _, om b, h => Qs_map f b h
  | _, ad x y, h => ⟨Qs_map f x h.1, Qs_map f y h.2⟩

theorem tr_map (a : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) :
    ∀ {k : Bool} (t : UnT k), (tr a t).map f = tr (f a) (t.map f)
  | _, par _ => rfl
  | _, add s t => by simp only [tr, map, tr_map a f s, tr_map a f t]
  | _, base => rfl
  | _, th1 s => by simp only [tr, map, tr_map a f s]
  | _, thc _ r => by simp only [tr, map, tr_map a f r]
  | _, thg _ G r => by simp only [tr, map, tr_map a f G, tr_map a f r]
  | _, lf c => by simp only [tr, map, tr_map a f c]
  | _, om b => by simp only [tr, map, tr_map a f b]
  | _, ad x y => by simp only [tr, map, tr_map a f x, tr_map a f y]

theorem Qs_tr {κ : Ordinal.{0}} (a : Ordinal.{0}) : ∀ {k : Bool} (t : UnT k), Qs κ t → Qs κ (tr a t)
  | _, par _, _ => trivial
  | _, add s t, h => ⟨Qs_tr a s h.1, Qs_tr a t h.2⟩
  | _, base, _ => trivial
  | _, th1 s, h => ⟨trivial, Qs_tr a s h⟩
  | _, thc _ r, h => ⟨h.1, trivial, Qs_tr a r h.2⟩
  | _, thg _ G r, h => ⟨Qs_tr a G h.1, Qs_tr a r h.2⟩
  | _, lf c, h => Qs_tr a c h
  | _, om b, h => Qs_tr a b h
  | _, ad x y, h => ⟨Qs_tr a x h.1, Qs_tr a y h.2⟩

theorem Lv_tr {P : Ordinal.{0} → Prop} {a : Ordinal.{0}} (ha : P a) :
    ∀ {k : Bool} (t : UnT k), Lv P t → Lv P (tr a t)
  | _, par _, h => h
  | _, add s t, h => ⟨Lv_tr ha s h.1, Lv_tr ha t h.2⟩
  | _, base, _ => ha
  | _, th1 s, h => ⟨ha, Lv_tr ha s h⟩
  | _, thc _ r, h => ⟨ha, Lv_tr ha r h⟩
  | _, thg _ G r, h => ⟨Lv_tr ha G h.1, Lv_tr ha r h.2⟩
  | _, lf c, h => Lv_tr ha c h
  | _, om b, h => Lv_tr ha b h
  | _, ad x y, h => ⟨Lv_tr ha x h.1, Lv_tr ha y h.2⟩

theorem Gs_map (f : Ordinal.{0} → Ordinal.{0}) : ∀ {k : Bool} (t : UnT k), Gs (t.map f) ↔ Gs t
  | _, par _ => Iff.rfl
  | _, add _ _ => Iff.rfl
  | _, base => Iff.rfl
  | _, th1 _ => Iff.rfl
  | _, thc _ _ => Iff.rfl
  | _, thg _ _ _ => Iff.rfl
  | _, lf _ => Iff.rfl
  | _, om _ => Iff.rfl
  | _, ad x y => and_congr (Gs_map f x) (Gs_map f y)

theorem Gs_tr (a : Ordinal.{0}) : ∀ {k : Bool} (t : UnT k), Gs (tr a t) ↔ Gs t
  | _, par _ => Iff.rfl
  | _, add _ _ => Iff.rfl
  | _, base => Iff.rfl
  | _, th1 _ => Iff.rfl
  | _, thc _ _ => Iff.rfl
  | _, thg _ _ _ => Iff.rfl
  | _, lf _ => Iff.rfl
  | _, om _ => Iff.rfl
  | _, ad x y => and_congr (Gs_tr a x) (Gs_tr a y)

theorem IsOm_map (f : Ordinal.{0} → Ordinal.{0}) : ∀ (t : UnT true), IsOm (t.map f) ↔ IsOm t
  | lf _ => Iff.rfl
  | om _ => Iff.rfl
  | ad _ _ => Iff.rfl

theorem IsOm_tr (a : Ordinal.{0}) : ∀ (t : UnT true), IsOm (tr a t) ↔ IsOm t
  | lf _ => Iff.rfl
  | om _ => Iff.rfl
  | ad _ _ => Iff.rfl

/-- High countable terms are carried by a parameter map sending parameters `≥ τ` to parameters `≥ σ`. -/
theorem HiC_map {τ σ : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} :
    ∀ (c : UnT false), Lv (fun p => τ ≤ p → σ ≤ f p) c → HiC τ c → HiC σ (c.map f)
  | par _, hl, h => hl h
  | add s _, hl, h => HiC_map s hl.1 h
  | base, _, _ => trivial
  | th1 _, _, _ => trivial
  | thc _ _, _, _ => trivial
  | thg _ _ _, _, _ => trivial

theorem HiC_tr {τ a : Ordinal.{0}} (hτa : τ ≤ a) : ∀ (c : UnT false), HiC a c → HiC τ (tr a c)
  | par _, h => hτa.trans h
  | add s _, h => HiC_tr hτa s h
  | base, _ => hτa
  | th1 _, _ => trivial
  | thc _ _, _ => trivial
  | thg _ _ _, _ => trivial

theorem Hd_map {τ σ : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} :
    ∀ (G : UnT true), Lv (fun p => τ ≤ p → σ ≤ f p) G → Hd τ G → Hd σ (G.map f)
  | lf c, hl, h => HiC_map c hl h
  | om b, hl, h => Hd_map b hl h
  | ad x _, hl, h => Hd_map x hl.1 h

theorem HdE_map {τ σ : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} :
    ∀ (G : UnT true), Lv (fun p => τ ≤ p → σ ≤ f p) G → HdE τ G → HdE σ (G.map f)
  | lf c, hl, h => HiC_map c hl h
  | om b, hl, h => HdE_map b hl h
  | ad x y, hl, h => h.imp (HdE_map x hl.1) (HdE_map y hl.2)

theorem Hd_tr {τ a : Ordinal.{0}} (hτa : τ ≤ a) : ∀ (G : UnT true), Hd a G → Hd τ (tr a G)
  | lf c, h => HiC_tr hτa c h
  | om b, h => Hd_tr hτa b h
  | ad x _, h => Hd_tr hτa x h

theorem HdE_tr {τ a : Ordinal.{0}} (hτa : τ ≤ a) : ∀ (G : UnT true), HdE a G → HdE τ (tr a G)
  | lf c, h => HiC_tr hτa c h
  | om b, h => HdE_tr hτa b h
  | ad x y, h => h.imp (HdE_tr hτa x) (HdE_tr hτa y)

theorem HdM_map {τ σ : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} :
    ∀ (m : Bool) (G : UnT true), Lv (fun p => τ ≤ p → σ ≤ f p) G → HdM m τ G → HdM m σ (G.map f)
  | false, G, hl, h => Hd_map G hl h
  | true, G, hl, h => HdE_map G hl h

theorem HdM_tr {τ a : Ordinal.{0}} (hτa : τ ≤ a) : ∀ (m : Bool) (G : UnT true), HdM m a G → HdM m τ (tr a G)
  | false, G, h => Hd_tr hτa G h
  | true, G, h => HdE_tr hτa G h

/-- The value part of the mode from its two parts. -/
theorem NfM_imp {τ σ : Ordinal.{0}} {G G' : UnT true} (h4 : HbS τ G → HbS σ G') (h5 : FNF τ G → FNF σ G') :
    ∀ m : Bool, NfM m τ G → NfM m σ G'
  | false, h => h4 h
  | true, h => h5 h

/-- The head mode follows from the normal-form value part (`FNF ⇒ HbS`). -/
theorem HbS_of_FNF {τ : Ordinal.{0}} : ∀ {k : Bool} (t : UnT k), FNF τ t → HbS τ t
  | _, par _, _ => trivial
  | _, add _ _, _ => trivial
  | _, base, _ => trivial
  | _, th1 _, _ => trivial
  | _, thc _ _, _ => trivial
  | _, thg _ _ _, _ => trivial
  | _, lf _, _ => trivial
  | _, om b, h => HbS_of_FNF b h
  | _, ad x _, h => ⟨HbS_of_FNF x h.1, h.2.2.1, h.2.2.2⟩

theorem Hd_HdE {τ : Ordinal.{0}} : ∀ (G : UnT true), Hd τ G → HdE τ G
  | lf _, h => h
  | om b, h => Hd_HdE b h
  | ad x _, h => Or.inl (Hd_HdE x h)

theorem HdA_map {τ σ : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} :
    ∀ {k : Bool} (t : UnT k), Lv (fun p => τ ≤ p → σ ≤ f p) t → HdA τ t → HdA σ (t.map f)
  | _, par _, _, _ => trivial
  | _, add s t, hl, h => ⟨HdA_map s hl.1 h.1, HdA_map t hl.2 h.2⟩
  | _, base, _, _ => trivial
  | _, th1 s, hl, h => HdA_map s hl h
  | _, thc _ r, hl, h => HdA_map r hl h
  | _, thg m G r, hl, h => ⟨HdM_map m G hl.1 h.1, HdA_map G hl.1 h.2.1, HdA_map r hl.2 h.2.2⟩
  | _, lf c, hl, h => HdA_map c hl h
  | _, om b, hl, h => HdA_map b hl h
  | _, ad x y, hl, h => ⟨HdA_map x hl.1 h.1, HdA_map y hl.2 h.2⟩

theorem WF_HdA {τ : Ordinal.{0}} : ∀ {k : Bool} (t : UnT k), WF τ t → HdA τ t
  | _, par _, _ => trivial
  | _, add s t, h => ⟨WF_HdA s h.1, WF_HdA t h.2⟩
  | _, base, _ => trivial
  | _, th1 s, h => WF_HdA s h.1
  | _, thc _ r, h => WF_HdA r h.1
  | _, thg _ G r, h => ⟨h.2.2.hd, WF_HdA G h.1, WF_HdA r h.2.1⟩
  | _, lf c, h => WF_HdA c h.1
  | _, om b, h => WF_HdA b h
  | _, ad x y, h => ⟨WF_HdA x h.1, WF_HdA y h.2⟩

/-! ### Values of level terms -/

/-- Countable leaves give a value below `ε_{Ω₁+1}`. -/
theorem ev_lt_E {τ : Ordinal.{0}} : ∀ (G : UnT true), WF τ G → ev τ G < Gg.ggE
  | lf _, h => h.2.trans Rj.rj_Om1_lt_E
  | om b, h => by
    have hb := ev_lt_E b h
    simp only [ev]
    rw [Si.si_Om1_opow_eq]
    have h1 : Om1 + ev τ b < Gg.ggE := Si.si_E_inE.add_lt Rj.rj_Om1_lt_E hb
    have h2 : ω ^ (Om1 + ev τ b) < ω ^ (Gg.ggE : Ordinal.{0}) := (opow_lt_opow_iff_right one_lt_omega0).2 h1
    have h3 : ω ^ (Gg.ggE : Ordinal.{0}) = Gg.ggE := Si.si_E_inE
    rwa [h3] at h2
  | ad x y, h => Si.si_E_inE.add_lt (ev_lt_E x h.1) (ev_lt_E y h.2)

/-- **A level is a positive multiple of `Ω₁`.** -/
theorem ev_dvd {τ : Ordinal.{0}} : ∀ (G : UnT true), Gs G → ∃ M, ev τ G = Om1 * M ∧ 1 ≤ M
  | lf _, h => h.elim
  | om b, _ => ⟨ω ^ ev τ b, rfl, Order.one_le_iff_pos.2 (opow_pos _ omega0_pos)⟩
  | ad x y, h => by
    obtain ⟨M1, e1, h1⟩ := ev_dvd x h.1
    obtain ⟨M2, e2, _⟩ := ev_dvd y h.2
    exact ⟨M1 + M2, by simp only [ev]; rw [e1, e2, mul_add], h1.trans le_self_add⟩

end UnT

/-! ## `y < x·ω` and the base change -/

/-- `y < x·ω` iff `y < x·n` for some `n < ω`. -/
theorem unLt_mul_omega_iff {x y : Ordinal.{0}} : y < x * ω ↔ ∃ n : ℕ, y < x * n := by
  constructor
  · intro h
    have hx0 : x ≠ 0 := by rintro rfl; rw [zero_mul] at h; exact absurd h (not_lt.2 zero_le)
    have hd : y / x < ω := (Ordinal.lt_mul_iff_div_lt hx0).1 h
    obtain ⟨n, hn⟩ := lt_omega0.1 hd
    refine ⟨n + 1, ?_⟩
    have := Ordinal.lt_mul_div_add y hx0
    rw [hn] at this
    rw [Nat.cast_succ, mul_add_one]; exact this
  · rintro ⟨n, hn⟩
    exact hn.trans_le (mul_le_mul_right (natCast_lt_omega0 n).le x)

/-- `π(x·n) = π(x)·n`. -/
theorem unPi_mul_nat {σ τ x : Ordinal.{0}} (h : Bases σ τ) (hx : x ∈ TB τ σ) :
    ∀ n : ℕ, x * n ∈ TB τ σ ∧ pi σ τ (x * n) = pi σ τ x * n
  | 0 => by
    have h0 : (0 : Ordinal.{0}) < σ := InE.pos h.1
    rw [Nat.cast_zero, mul_zero, mul_zero]
    exact ⟨mem_TB_of_lt h h0, pi_lt h h0⟩
  | n + 1 => by
    obtain ⟨a1, a2⟩ := unPi_mul_nat h hx n
    obtain ⟨c1, c2⟩ := pi_add h a1 hx
    rw [Nat.cast_succ, mul_add_one, mul_add_one]
    exact ⟨c1, by rw [c2, a2]⟩

/-- **`y < x·ω` is kept and reflected by `π`** (`x, y ∈ Tᵗ[σ]`). -/
theorem unPi_lt_mul_omega_iff {σ τ x y : Ordinal.{0}} (h : Bases σ τ) (hx : x ∈ TB τ σ) (hy : y ∈ TB τ σ) :
    y < x * ω ↔ pi σ τ y < pi σ τ x * ω := by
  rw [unLt_mul_omega_iff, unLt_mul_omega_iff]
  refine exists_congr fun n => ?_
  obtain ⟨a1, a2⟩ := unPi_mul_nat h hx n
  rw [← a2]
  exact ((pi_bijOn h).2.lt_iff_lt hy a1).symm

/-- `π⁻¹` of an ordinal below `Ω₁` is below `Ω₁`. -/
theorem unUp_lt_Om1 {σ τ y z : Ordinal.{0}} (h : Bases σ τ) (hy : y ∈ TB τ σ) (hyz : pi σ τ y = z) (hz : z < Om1) :
    y < Om1 := by
  by_contra hge
  have hOm := pi_Om1 h
  have := ((pi_bijOn h).2.le_iff_le hOm.1 hy).2 (not_lt.1 hge)
  rw [hOm.2, hyz] at this
  exact absurd hz (not_lt.2 this)

/-! ## Membership and the decision `Γ^* ≥ τ` -/

/-- **Membership**: parameters in `Tᵗ`, the argument bounds, node conditions and levels over `κ` give `t[τ] ∈ Tᵗ`. -/
theorem unMem {κ τ : Ordinal.{0}} (hB : Bases κ τ) :
    ∀ (t : UnT false), Lv (· ∈ Tset τ) t → WF τ t → Qs κ t → ev τ t ∈ Tset τ
  | .par _, hl, _, _ => hl
  | .add s t, hl, hw, hq => vzT_add hB.2.1 hB.2.2.2 (unMem hB s hl.1 hw.1 hq.1) (unMem hB t hl.2 hw.2 hq.2)
  | .base, _, _, _ => uh_T_le hB.2.1 hB.2.2.2 le_rfl
  | .th1 s, hl, hw, hq => by
    have hτ1 := hB.2.2.2
    have h1 : (1 : Ordinal.{0}) ∈ Tset τ := uh_T_le hB.2.1 hτ1 (Ub.ub_one_lt hB.2.1).le
    have hO : (1 : Ordinal.{0}) < Om1 := (Ub.ub_one_lt hB.2.1).trans hτ1
    exact (vt_mem hB.2.1 hτ1 (vzT_add hB.2.1 hτ1 h1 (unMem hB s hl hw.1 hq)) (Om1_add_lt hO hw.2)).1
  | .thc _ r, hl, hw, hq => by
    obtain ⟨h1, h2⟩ := uh_arg_T hB hq.1 (unMem hB r hl hw.1 hq.2) hw.2
    exact (vt_memTwo hB.2.1 hB.2.2.2 h1 h2).1
  | .thg _ G _, _, hw, _ =>
    (vt_memTwo hB.2.1 hB.2.2.2 hw.2.2.mem (Uk.arg_lt2 (UnT.ev_lt_E G hw.1) hw.2.2.r1)).1

/-- **A high countable term is `≥ τ`** ([W07a] Lemma 3.30 through `R2.vt_memTwo` at the `ϑ`-heads, Lemma 4.2
through `R2.vt_wbar` at `ϑᵗ(1 + ξ)`). -/
theorem HiC_le {κ τ : Ordinal.{0}} (hB : Bases κ τ) :
    ∀ (c : UnT false), Lv (· ∈ Tset τ) c → WF τ c → Qs κ c → HiC τ c → τ ≤ ev τ c
  | .par _, _, _, _, h => h
  | .add s _, hl, hw, hq, h => by
    simp only [ev]; exact (HiC_le hB s hl.1 hw.1 hq.1 h).trans le_self_add
  | .base, _, _, _, _ => le_rfl
  | .th1 s, _, hw, _, _ => by
    simp only [ev]; rw [vt_wbar hB.2.1 hB.2.2.2 hw.2]
    exact le_self_add.trans (Se.se_wbar_gt _).le
  | .thc _ r, hl, hw, hq, _ => by
    obtain ⟨h1, h2⟩ := uh_arg_T hB hq.1 (unMem hB r hl hw.1 hq.2) hw.2
    exact (vt_memTwo hB.2.1 hB.2.2.2 h1 h2).2.1
  | .thg _ G _, _, hw, _, _ =>
    (vt_memTwo hB.2.1 hB.2.2.2 hw.2.2.mem (Uk.arg_lt2 (UnT.ev_lt_E G hw.1) hw.2.2.r1)).2.1

/-- **The data of `Ω₁·ω^b + y` bound the data of `y`** (`b < ε_{Ω₁+1}`, `0 < y < Ω₁·ω^{b+1}`): the CNF of `y` is
that of `Ω₁·ω^b + y` with the coefficient of `ω^{Ω₁+b}` lowered, or `y < ω^{Ω₁+b}` is its remainder. -/
theorem dat_om_add_r {b y : Ordinal.{0}} (hbE : b < Gg.ggE) (hy0 : y ≠ 0) (hy : y < Om1 * ω ^ (b + 1)) :
    Rj.rjDat y ≤ Rj.rjDat (Om1 * ω ^ b + y) := by
  obtain ⟨g, hg⟩ : ∃ g, g = Om1 + b := ⟨_, rfl⟩
  have hgE : g < Gg.ggE := hg ▸ Si.si_E_inE.add_lt Rj.rj_Om1_lt_E hbE
  have hwg : Om1 * ω ^ b = ω ^ g := by rw [hg]; exact Si.si_Om1_opow_eq b
  have hy' : y < ω ^ g * ω := by rw [← hwg, Uk.UkL.om_mul_omega]; exact hy
  have hw0 : ω ^ g ≠ 0 := (opow_pos _ omega0_pos).ne'
  have hdecy := Ordinal.div_add_mod y (ω ^ g)
  have hq : y / ω ^ g < ω := (Ordinal.lt_mul_iff_div_lt hw0).1 hy'
  have hrem : y % ω ^ g < ω ^ g := Ordinal.mod_lt y hw0
  have hsum : Om1 * ω ^ b + y = ω ^ g * (1 + y / ω ^ g) + y % ω ^ g := by
    rw [hwg, mul_add, mul_one, add_assoc, hdecy]
  have hv0 : 1 + y / ω ^ g ≠ 0 := (lt_of_lt_of_le zero_lt_one le_self_add).ne'
  have hvω : 1 + y / ω ^ g < ω := by
    obtain ⟨m, hm⟩ := lt_omega0.1 hq
    rw [hm]; exact_mod_cast natCast_lt_omega0 (1 + m)
  have hOg : Om1 ≤ ω ^ g := by
    rw [← Rj.rj_Om1_opow]
    exact (opow_le_opow_iff_right one_lt_omega0).2 (hg ▸ le_self_add)
  have h1 : Om1 < ω ^ g * (1 + y / ω ^ g) + y % ω ^ g := by
    rw [← hsum, hwg]
    exact lt_of_le_of_lt hOg (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hy0))
  have hwE : ω ^ (g + 1) < Gg.ggE := by
    have h3 : ω ^ (Gg.ggE : Ordinal.{0}) = Gg.ggE := Si.si_E_inE
    have hg1 : g + 1 < Gg.ggE := Si.si_E_inE.add_lt hgE (Ub.ub_one_lt Si.si_E_inE)
    have := (opow_lt_opow_iff_right one_lt_omega0).2 hg1
    rwa [h3] at this
  have hle : ∀ v : Ordinal.{0}, v < ω → ω ^ g * v + y % ω ^ g < ω ^ (g + 1) := by
    intro v hv
    rw [opow_add, opow_one]
    calc ω ^ g * v + y % ω ^ g < ω ^ g * v + ω ^ g := (add_lt_add_iff_left _).2 hrem
      _ = ω ^ g * (v + 1) := by rw [mul_add_one]
      _ ≤ ω ^ g * ω := mul_le_mul_right (Order.add_one_le_of_lt hv) _
  have hlt : ω ^ g * (1 + y / ω ^ g) + y % ω ^ g < Gg.ggE := (hle _ hvω).trans hwE
  rw [hsum, Si.si_rjDat_form hv0 hvω hrem h1 hlt]
  by_cases hq0 : y / ω ^ g = 0
  · have hyr : y % ω ^ g = y := by
      have e := hdecy
      rw [hq0, mul_zero, zero_add] at e
      exact e
    rw [hyr]; exact le_max_right _ _
  · rcases lt_or_ge Om1 y with hO | hO
    · have hyq : y = ω ^ g * (y / ω ^ g) + y % ω ^ g := hdecy.symm
      have h1' : Om1 < ω ^ g * (y / ω ^ g) + y % ω ^ g := by rw [← hyq]; exact hO
      have hlt' : ω ^ g * (y / ω ^ g) + y % ω ^ g < Gg.ggE := (hle _ hq).trans hwE
      have e : Rj.rjDat y = max (Rj.rjDat g) (Rj.rjDat (y % ω ^ g)) := by
        conv_lhs => rw [← hdecy]
        exact Si.si_rjDat_form hq0 hq hrem h1' hlt'
      exact e.le
    · have hy1 : ω ^ g ≤ y := by
        rw [← hdecy]
        exact le_trans (le_mul_left _ (pos_iff_ne_zero.2 hq0)) le_self_add
      have : y = Om1 := le_antisymm hO (hOg.trans hy1)
      rw [this, Rj.rjDat_Om1]; exact zero_le

/-- **The decision `Γ^{*τ} ≥ τ` in the head mode**: no absorption of the head and a high head leaf give
`τ ≤ rjDat Γ` (`Γ = G[τ]`). -/
theorem datHb {κ τ : Ordinal.{0}} (hB : Bases κ τ) :
    ∀ (G : UnT true), Lv (· ∈ Tset τ) G → WF τ G → Qs κ G → HbS τ G → Hd τ G →
      τ ≤ Rj.rjDat (ev τ G) ∧ ev τ G ≠ 0
  | .lf c, hl, hw, hq, _, hd => by
    have h1 : τ ≤ ev τ c := HiC_le hB c hl hw.1 hq hd
    simp only [ev]
    rw [Rj.rjDat_small hw.2]
    exact ⟨h1, ((InE.pos hB.2.1).trans_le h1).ne'⟩
  | .om b, hl, hw, hq, hb, hd => by
    obtain ⟨h1, h2⟩ := datHb hB b hl hw hq hb hd
    have hbE := UnT.ev_lt_E b hw
    have := Uk.UkL.dat_om_add (y := 0) h2 hbE (mul_pos Rj.rj_Om1_pos (opow_pos _ omega0_pos))
    rw [add_zero] at this
    simp only [ev]
    exact ⟨h1.trans this, (mul_pos Rj.rj_Om1_pos (opow_pos _ omega0_pos)).ne'⟩
  | .ad (.om b) y, hl, hw, hq, hb, hd => by
    obtain ⟨h1, h2⟩ := datHb hB b hl.1 hw.1 hq.1 hb.1 hd
    have hbE := UnT.ev_lt_E b hw.1
    have hy : ev τ y < Om1 * ω ^ (ev τ b + 1) := by rw [← Uk.UkL.om_mul_omega]; exact hb.2.2
    have := Uk.UkL.dat_om_add h2 hbE hy
    simp only [ev]
    exact ⟨h1.trans this,
      (lt_of_lt_of_le (mul_pos Rj.rj_Om1_pos (opow_pos _ omega0_pos)) le_self_add).ne'⟩
  | .ad (.lf _) _, _, _, _, hb, _ => hb.2.1.elim
  | .ad (.ad _ _) _, _, _, _, hb, _ => hb.2.1.elim

/-- **The decision `Γ^{*τ} ≥ τ` in the normal-form mode**: full Cantor normal form and SOME high leaf (also in a
non-head summand) give `τ ≤ rjDat Γ`. -/
theorem datFN {κ τ : Ordinal.{0}} (hB : Bases κ τ) :
    ∀ (G : UnT true), Lv (· ∈ Tset τ) G → WF τ G → Qs κ G → FNF τ G → HdE τ G →
      τ ≤ Rj.rjDat (ev τ G) ∧ ev τ G ≠ 0
  | .lf c, hl, hw, hq, _, hd => by
    have h1 : τ ≤ ev τ c := HiC_le hB c hl hw.1 hq hd
    simp only [ev]
    rw [Rj.rjDat_small hw.2]
    exact ⟨h1, ((InE.pos hB.2.1).trans_le h1).ne'⟩
  | .om b, hl, hw, hq, hb, hd => by
    obtain ⟨h1, h2⟩ := datFN hB b hl hw hq hb hd
    have hbE := UnT.ev_lt_E b hw
    have := Uk.UkL.dat_om_add (y := 0) h2 hbE (mul_pos Rj.rj_Om1_pos (opow_pos _ omega0_pos))
    rw [add_zero] at this
    simp only [ev]
    exact ⟨h1.trans this, (mul_pos Rj.rj_Om1_pos (opow_pos _ omega0_pos)).ne'⟩
  | .ad (.om b) y, hl, hw, hq, hb, hd => by
    have hbE := UnT.ev_lt_E b hw.1
    have hy : ev τ y < Om1 * ω ^ (ev τ b + 1) := by rw [← Uk.UkL.om_mul_omega]; exact hb.2.2.2
    have hne : ev τ (UnT.ad (.om b) y) ≠ 0 := by
      simp only [ev]
      exact (lt_of_lt_of_le (mul_pos Rj.rj_Om1_pos (opow_pos _ omega0_pos)) le_self_add).ne'
    rcases hd with hd | hd
    · obtain ⟨h1, h2⟩ := datFN hB b hl.1 hw.1 hq.1 hb.1 hd
      have := Uk.UkL.dat_om_add h2 hbE hy
      exact ⟨by simp only [ev]; exact h1.trans this, hne⟩
    · obtain ⟨h1, h2⟩ := datFN hB y hl.2 hw.2 hq.2 hb.2.1 hd
      have := dat_om_add_r hbE h2 hy
      exact ⟨by simp only [ev]; exact h1.trans this, hne⟩
  | .ad (.lf _) _, _, _, _, hb, _ => hb.2.2.1.elim
  | .ad (.ad _ _) _, _, _, _, hb, _ => hb.2.2.1.elim

/-- **The decision `Γ^{*τ} ≥ τ` in either mode.** -/
theorem datM {κ τ : Ordinal.{0}} (hB : Bases κ τ) :
    ∀ (m : Bool) (G : UnT true), Lv (· ∈ Tset τ) G → WF τ G → Qs κ G → NfM m τ G → HdM m τ G →
      τ ≤ Rj.rjDat (ev τ G) ∧ ev τ G ≠ 0
  | false, G, hl, hw, hq, hn, hd => datHb hB G hl hw hq hn hd
  | true, G, hl, hw, hq, hn, hd => datFN hB G hl hw hq hn hd

/-! ## Order of the parts -/

/-- **Every parameter and every node value is `≤` the value** (for level terms: `≤` every bound `V` of the
leaves). -/
theorem unLeB {κ τ : Ordinal.{0}} (hB : Bases κ τ) :
    ∀ {k : Bool} (t : UnT k), Lv (· ∈ Tset τ) t → WF τ t → Qs κ t → ∀ V : Ordinal.{0},
      (k = false → ev τ t ≤ V) → Lf (fun c => ev τ c ≤ V) t → Lv (· ≤ V) t ∧ Nd τ (· ≤ V) t
  | _, .par _, _, _, _, _, hv, _ => ⟨hv rfl, trivial⟩
  | _, .add s t, hl, hw, hq, V, hv, _ => by
    have hs : ev τ s ≤ V := le_self_add.trans (hv rfl)
    have ht : ev τ t ≤ V := le_add_self.trans (hv rfl)
    obtain ⟨a1, a2⟩ := unLeB hB s hl.1 hw.1 hq.1 V (fun _ => hs) (Lf_cnt _ s)
    obtain ⟨b1, b2⟩ := unLeB hB t hl.2 hw.2 hq.2 V (fun _ => ht) (Lf_cnt _ t)
    exact ⟨⟨a1, b1⟩, ⟨a2, b2⟩⟩
  | _, .base, _, _, _, _, _, _ => ⟨trivial, trivial⟩
  | _, .th1 s, hl, hw, hq, V, hv, _ => by
    have hle : ev τ s ≤ ev τ (.th1 s) := by
      simp only [ev]; rw [vt_wbar hB.2.1 hB.2.2.2 hw.2]
      exact le_add_self.trans (Se.se_wbar_gt _).le
    exact unLeB hB s hl hw.1 hq V (fun _ => hle.trans (hv rfl)) (Lf_cnt _ s)
  | _, .thc q r, hl, hw, hq, V, hv, _ => by
    have hrT := unMem hB r hl hw.1 hq.2
    have hlt : ev τ r < ev τ (.thc q r) := uhLt_vt_self hB hq.1 hrT hw.2
    obtain ⟨a1, a2⟩ := unLeB hB r hl hw.1 hq.2 V (fun _ => hlt.le.trans (hv rfl)) (Lf_cnt _ r)
    exact ⟨a1, hv rfl, a2⟩
  | _, .thg m G r, hl, hw, hq, V, hv, _ => by
    have hvV : ev τ (UnT.thg m G r) ≤ V := hv rfl
    obtain ⟨a1, a2⟩ := unLeB hB r hl.2 hw.2.1 hq.2 V (fun _ => hw.2.2.rb.le.trans hvV) (Lf_cnt _ r)
    obtain ⟨l1, l2⟩ := unLeB hB G hl.1 hw.1 hq.1 V (fun h => nomatch h)
      (Lf_mono (fun c hc => hc.le.trans hvV) G hw.2.2.bd)
    exact ⟨⟨l1, a1⟩, ⟨hvV, l2, a2⟩⟩
  | _, .lf c, hl, hw, hq, V, _, hc => unLeB hB c hl hw.1 hq V (fun _ => hc) (Lf_cnt _ c)
  | _, .om b, hl, hw, hq, V, _, hc => unLeB hB b hl hw hq V (fun h => nomatch h) hc
  | _, .ad x y, hl, hw, hq, V, _, hc => by
    obtain ⟨a1, a2⟩ := unLeB hB x hl.1 hw.1 hq.1 V (fun h => nomatch h) hc.1
    obtain ⟨b1, b2⟩ := unLeB hB y hl.2 hw.2 hq.2 V (fun h => nomatch h) hc.2
    exact ⟨⟨a1, b1⟩, ⟨a2, b2⟩⟩

/-- **Every parameter and every node value is `≤` the value.** -/
theorem unLe {κ τ : Ordinal.{0}} (hB : Bases κ τ) (t : UnT false) (hl : Lv (· ∈ Tset τ) t) (hw : WF τ t)
    (hq : Qs κ t) : Lv (· ≤ ev τ t) t ∧ Nd τ (· ≤ ev τ t) t :=
  unLeB hB t hl hw hq _ (fun _ => le_rfl) (UnT.Lf_cnt _ t)

/-! ## The base change -/

/-- **The base change on terms of both sorts** ([W07a] Def 5.1, Lemma 5.3 through `R2.pi_vt`, `R2.pi_vt_two`,
`R2.pi_add`, `Uh.uh_Om1_mul_TB`, `R2.siOm1_opow_TB`): values, argument bounds, node conditions (both modes), the
`·ω`-bounds of the sums and the leaf bounds are carried by `π_{σ,τ}`. -/
theorem unDownB {κ σ τ : Ordinal.{0}} (h : Bases σ τ) (hκσ : κ ≤ σ) :
    ∀ {k : Bool} (t : UnT k), WF τ t → Lv (· ∈ TB τ σ) t → Qs κ t →
      ev τ t ∈ TB τ σ ∧ pi σ τ (ev τ t) = ev σ (t.map (pi σ τ)) ∧ WF σ (t.map (pi σ τ)) ∧
      (HbS τ t → HbS σ (t.map (pi σ τ))) ∧ (FNF τ t → FNF σ (t.map (pi σ τ))) ∧
      (∀ V ∈ TB τ σ, Lf (fun c => ev τ c < V) t → Lf (fun c => ev σ c < pi σ τ V) (t.map (pi σ τ)))
  | _, .par p, _, hp, _ => ⟨hp, rfl, trivial, fun _ => trivial, fun _ => trivial, fun _ _ _ => trivial⟩
  | _, .add s t, hw, hl, hq => by
    obtain ⟨a1, a2, a3, -⟩ := unDownB h hκσ s hw.1 hl.1 hq.1
    obtain ⟨b1, b2, b3, -⟩ := unDownB h hκσ t hw.2 hl.2 hq.2
    obtain ⟨c1, c2⟩ := pi_add h a1 b1
    refine ⟨c1, ?_, ⟨a3, b3⟩, fun _ => trivial, fun _ => trivial, fun _ _ _ => trivial⟩
    simp only [ev, map]; rw [c2, a2, b2]
  | _, .base, _, _, _ =>
    ⟨(pi_base h).1, (pi_base h).2, trivial, fun _ => trivial, fun _ => trivial, fun _ _ _ => trivial⟩
  | _, .th1 s, hw, hl, hq => by
    obtain ⟨a1, a2, a3, -⟩ := unDownB h hκσ s hw.1 hl hq
    have hσ1 : (1 : Ordinal.{0}) < σ := Ub.ub_one_lt h.1
    have h1T : (1 : Ordinal.{0}) ∈ TB τ σ := (TB_inter_lt h (hσ1.trans h.2.2.1)).2 hσ1
    obtain ⟨c1, c2⟩ := pi_add h h1T a1
    have hO : (1 : Ordinal.{0}) < Om1 := hσ1.trans (h.2.2.1.trans h.2.2.2)
    have hlt1 : 1 + ev τ s < Om1 := Om1_add_lt hO hw.2
    obtain ⟨d1, d2⟩ := vt_mem h.2.1 h.2.2.2 c1.1 hlt1
    refine ⟨⟨d1, by
      show ((Par τ (vt τ (1 + ev τ s)) : Set Ordinal.{0})) ⊆ Set.Iio σ; rw [d2]; exact c1.2⟩, ?_, ⟨a3, ?_⟩,
      fun _ => trivial, fun _ => trivial, fun _ _ _ => trivial⟩
    · simp only [ev, map]; rw [pi_vt h c1 hlt1, c2, pi_lt h hσ1, a2]
    · rw [← a2]; exact down_lt_Om1 h a1 hw.2
  | _, .thc q r, hw, hl, hq => by
    obtain ⟨a1, a2, a3, -⟩ := unDownB h hκσ r hw.1 hl hq.2
    obtain ⟨g1, g2⟩ := uh_Om1_mul_TB h q hq.1.2.1 (hq.1.2.2.trans_le hκσ)
    obtain ⟨c1, c2⟩ := pi_add h g1 a1
    have hlt2 : Om1 * q + ev τ r < OmTwo := Rj.rj_arg_lt hq.1.2.1 hw.2
    obtain ⟨d1, -, -, -, d2⟩ := vt_memTwo h.2.1 h.2.2.2 c1.1 hlt2
    refine ⟨⟨d1, by
      show ((Par τ (vt τ (Om1 * q + ev τ r)) : Set Ordinal.{0})) ⊆ Set.Iio σ; rw [d2]; exact c1.2⟩, ?_, ⟨a3, ?_⟩,
      fun _ => trivial, fun _ => trivial, fun _ _ _ => trivial⟩
    · simp only [ev, map]; rw [pi_vt_two h c1 hlt2, c2, g2, a2]
    · rw [← a2]; exact down_lt_Om1 h a1 hw.2
  | _, .thg m G r, hw, hl, hq => by
    obtain ⟨a1, a2, a3, -⟩ := unDownB h hκσ r hw.2.1 hl.2 hq.2
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := unDownB h hκσ G hw.1 hl.1 hq.1
    obtain ⟨c1, c2⟩ := pi_add h g1 a1
    have hlt2 := Uk.arg_lt2 (UnT.ev_lt_E G hw.1) hw.2.2.r1
    obtain ⟨d1, -, -, -, d2⟩ := vt_memTwo h.2.1 h.2.2.2 c1.1 hlt2
    have hVT : vt τ (ev τ G + ev τ r) ∈ TB τ σ := ⟨d1, by
      show ((Par τ (vt τ (ev τ G + ev τ r)) : Set Ordinal.{0})) ⊆ Set.Iio σ; rw [d2]; exact c1.2⟩
    have hpv : pi σ τ (vt τ (ev τ G + ev τ r)) = vt σ (ev σ (G.map (pi σ τ)) + ev σ (r.map (pi σ τ))) := by
      rw [pi_vt_two h c1 hlt2, c2, g2, a2]
    refine ⟨hVT, by simp only [ev, map]; exact hpv, ⟨g3, a3, ?_⟩, fun _ => trivial, fun _ => trivial,
      fun _ _ _ => trivial⟩
    refine ⟨by rw [← a2]; exact down_lt_Om1 h a1 hw.2.2.r1, (Gs_map _ G).2 hw.2.2.gs,
      NfM_imp g4 g5 m hw.2.2.nf,
      HdM_map m G (Lv_mono (fun p hp hτp => down_ge h hp hτp) G hl.1) hw.2.2.hd,
      by rw [← g2, ← a2, ← c2]; exact (pi_bijOn h).1.mapsTo c1, ?_, ?_⟩
    · rw [← hpv]; exact g6 _ hVT hw.2.2.bd
    · rw [← hpv, ← a2]; exact (pi_bijOn h).2 a1 hVT hw.2.2.rb
  | _, .lf c, hw, hl, hq => by
    obtain ⟨a1, a2, a3, -⟩ := unDownB h hκσ c hw.1 hl hq
    refine ⟨a1, a2, ⟨a3, by rw [← a2]; exact down_lt_Om1 h a1 hw.2⟩, fun _ => trivial, fun _ => trivial,
      fun V hV hc => ?_⟩
    show ev σ (c.map (pi σ τ)) < pi σ τ V
    rw [← a2]; exact (pi_bijOn h).2 a1 hV hc
  | _, .om b, hw, hl, hq => by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := unDownB h hκσ b hw hl hq
    have hbE := UnT.ev_lt_E b hw
    obtain ⟨o1, o2⟩ := siOm1_opow_TB h hbE
    refine ⟨o1.2 a1, ?_, a3, a4, a5, a6⟩
    simp only [ev, map]; rw [o2 a1, a2]
  | _, .ad x y, hw, hl, hq => by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := unDownB h hκσ x hw.1 hl.1 hq.1
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := unDownB h hκσ y hw.2 hl.2 hq.2
    obtain ⟨c1, c2⟩ := pi_add h a1 b1
    have hω : ev τ y < ev τ x * ω → ev σ (y.map (pi σ τ)) < ev σ (x.map (pi σ τ)) * ω := by
      intro hlt; rw [← a2, ← b2]; exact (unPi_lt_mul_omega_iff h a1 b1).1 hlt
    refine ⟨c1, ?_, ⟨a3, b3⟩, fun hb => ⟨a4 hb.1, (IsOm_map _ x).2 hb.2.1, hω hb.2.2⟩,
      fun hb => ⟨a5 hb.1, b5 hb.2.1, (IsOm_map _ x).2 hb.2.2.1, hω hb.2.2.2⟩,
      fun V hV hc => ⟨a6 V hV hc.1, b6 V hV hc.2⟩⟩
    simp only [ev, map]; rw [c2, a2, b2]

/-- **The base change on terms**: `π_{σ,τ}(t[τ; p]) = t[σ; π p]`, the image has the argument bounds and the node
conditions over `σ`. -/
theorem unDown {κ σ τ : Ordinal.{0}} (h : Bases σ τ) (hκσ : κ ≤ σ) (t : UnT false) (hw : WF τ t)
    (hl : Lv (· ∈ TB τ σ) t) (hq : Qs κ t) :
    ev τ t ∈ TB τ σ ∧ pi σ τ (ev τ t) = ev σ (t.map (pi σ τ)) ∧ WF σ (t.map (pi σ τ)) := by
  obtain ⟨a1, a2, a3, -⟩ := unDownB h hκσ t hw hl hq
  exact ⟨a1, a2, a3⟩

/-- **The inverse base change on terms of both sorts.** -/
theorem unUpB {κ σ τ : Ordinal.{0}} (h : Bases σ τ) (hκσ : κ ≤ σ) :
    ∀ {k : Bool} (t : UnT k), WF σ t → Lv (· ∈ Tset σ) t → Qs κ t →
      ev τ (t.map (up σ τ)) ∈ TB τ σ ∧ pi σ τ (ev τ (t.map (up σ τ))) = ev σ t ∧ WF τ (t.map (up σ τ)) ∧
      (HbS σ t → HbS τ (t.map (up σ τ))) ∧ (FNF σ t → FNF τ (t.map (up σ τ))) ∧
      (∀ V ∈ TB τ σ, Lf (fun c => ev σ c < pi σ τ V) t → Lf (fun c => ev τ c < V) (t.map (up σ τ)))
  | _, .par p, _, hp, _ =>
    ⟨(up_spec h hp).1, (up_spec h hp).2, trivial, fun _ => trivial, fun _ => trivial, fun _ _ _ => trivial⟩
  | _, .add s t, hw, hl, hq => by
    obtain ⟨a1, a2, a3, -⟩ := unUpB h hκσ s hw.1 hl.1 hq.1
    obtain ⟨b1, b2, b3, -⟩ := unUpB h hκσ t hw.2 hl.2 hq.2
    obtain ⟨c1, c2⟩ := pi_add h a1 b1
    refine ⟨c1, ?_, ⟨a3, b3⟩, fun _ => trivial, fun _ => trivial, fun _ _ _ => trivial⟩
    simp only [ev, map] at c2 ⊢; rw [c2, a2, b2]
  | _, .base, _, _, _ =>
    ⟨(pi_base h).1, (pi_base h).2, trivial, fun _ => trivial, fun _ => trivial, fun _ _ _ => trivial⟩
  | _, .th1 s, hw, hl, hq => by
    obtain ⟨a1, a2, a3, -⟩ := unUpB h hκσ s hw.1 hl hq
    have hσ1 : (1 : Ordinal.{0}) < σ := Ub.ub_one_lt h.1
    have h1T : (1 : Ordinal.{0}) ∈ TB τ σ := (TB_inter_lt h (hσ1.trans h.2.2.1)).2 hσ1
    have hO : (1 : Ordinal.{0}) < Om1 := hσ1.trans (h.2.2.1.trans h.2.2.2)
    have hy1 := unUp_lt_Om1 h a1 a2 hw.2
    obtain ⟨c1, c2⟩ := pi_add h h1T a1
    have hlt1 : 1 + ev τ (s.map (up σ τ)) < Om1 := Om1_add_lt hO hy1
    obtain ⟨d1, d2⟩ := vt_mem h.2.1 h.2.2.2 c1.1 hlt1
    refine ⟨⟨d1, by simp only [ev, map]; rw [d2]; exact c1.2⟩, ?_, ⟨a3, hy1⟩, fun _ => trivial,
      fun _ => trivial, fun _ _ _ => trivial⟩
    simp only [ev, map]; rw [pi_vt h c1 hlt1, c2, pi_lt h hσ1, a2]
  | _, .thc q r, hw, hl, hq => by
    obtain ⟨a1, a2, a3, -⟩ := unUpB h hκσ r hw.1 hl hq.2
    have hy1 := unUp_lt_Om1 h a1 a2 hw.2
    obtain ⟨g1, g2⟩ := uh_Om1_mul_TB h q hq.1.2.1 (hq.1.2.2.trans_le hκσ)
    obtain ⟨c1, c2⟩ := pi_add h g1 a1
    have hlt2 : Om1 * q + ev τ (r.map (up σ τ)) < OmTwo := Rj.rj_arg_lt hq.1.2.1 hy1
    obtain ⟨d1, -, -, -, d2⟩ := vt_memTwo h.2.1 h.2.2.2 c1.1 hlt2
    refine ⟨⟨d1, by simp only [ev, map]; rw [d2]; exact c1.2⟩, ?_, ⟨a3, hy1⟩, fun _ => trivial,
      fun _ => trivial, fun _ _ _ => trivial⟩
    simp only [ev, map]; rw [pi_vt_two h c1 hlt2, c2, g2, a2]
  | _, .thg m G r, hw, hl, hq => by
    obtain ⟨a1, a2, a3, -⟩ := unUpB h hκσ r hw.2.1 hl.2 hq.2
    have hy1 := unUp_lt_Om1 h a1 a2 hw.2.2.r1
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := unUpB h hκσ G hw.1 hl.1 hq.1
    obtain ⟨c1, c2⟩ := pi_add h g1 a1
    have hlt2 := Uk.arg_lt2 (UnT.ev_lt_E _ g3) hy1
    obtain ⟨d1, -, -, -, d2⟩ := vt_memTwo h.2.1 h.2.2.2 c1.1 hlt2
    have hVT : vt τ (ev τ (G.map (up σ τ)) + ev τ (r.map (up σ τ))) ∈ TB τ σ := ⟨d1, by
      show ((Par τ (vt τ (ev τ (G.map (up σ τ)) + ev τ (r.map (up σ τ)))) : Set Ordinal.{0})) ⊆ Set.Iio σ
      rw [d2]; exact c1.2⟩
    have hpv : pi σ τ (vt τ (ev τ (G.map (up σ τ)) + ev τ (r.map (up σ τ)))) = vt σ (ev σ G + ev σ r) := by
      rw [pi_vt_two h c1 hlt2, c2, g2, a2]
    refine ⟨hVT, by simp only [ev, map]; exact hpv, ⟨g3, a3, ?_⟩, fun _ => trivial, fun _ => trivial,
      fun _ _ _ => trivial⟩
    refine ⟨hy1, (Gs_map _ G).2 hw.2.2.gs, NfM_imp g4 g5 m hw.2.2.nf,
      HdM_map m G (Lv_mono (fun p hp hσp => up_ge h hp hσp) G hl.1) hw.2.2.hd, c1.1, ?_, ?_⟩
    · have hb := hw.2.2.bd
      rw [← hpv] at hb
      exact g6 _ hVT hb
    · have hb := hw.2.2.rb
      rw [← hpv, ← a2] at hb
      by_contra hge
      have := ((pi_bijOn h).2.le_iff_le hVT a1).2 (not_lt.1 hge)
      exact absurd hb (not_lt.2 this)
  | _, .lf c, hw, hl, hq => by
    obtain ⟨a1, a2, a3, -⟩ := unUpB h hκσ c hw.1 hl hq
    refine ⟨a1, a2, ⟨a3, unUp_lt_Om1 h a1 a2 hw.2⟩, fun _ => trivial, fun _ => trivial, fun V hV hc => ?_⟩
    show ev τ (c.map (up σ τ)) < V
    have hc' : ev σ c < pi σ τ V := hc
    rw [← a2] at hc'
    by_contra hge
    have := ((pi_bijOn h).2.le_iff_le hV a1).2 (not_lt.1 hge)
    exact absurd hc' (not_lt.2 this)
  | _, .om b, hw, hl, hq => by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := unUpB h hκσ b hw hl hq
    have hbE := UnT.ev_lt_E _ a3
    obtain ⟨o1, o2⟩ := siOm1_opow_TB h hbE
    refine ⟨o1.2 a1, ?_, a3, a4, a5, a6⟩
    simp only [ev, map] at o2 ⊢; rw [o2 a1, a2]
  | _, .ad x y, hw, hl, hq => by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := unUpB h hκσ x hw.1 hl.1 hq.1
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := unUpB h hκσ y hw.2 hl.2 hq.2
    obtain ⟨c1, c2⟩ := pi_add h a1 b1
    have hω : ev σ y < ev σ x * ω → ev τ (y.map (up σ τ)) < ev τ (x.map (up σ τ)) * ω := by
      intro hlt; rw [← a2, ← b2] at hlt; exact (unPi_lt_mul_omega_iff h a1 b1).2 hlt
    refine ⟨c1, ?_, ⟨a3, b3⟩, fun hb => ⟨a4 hb.1, (IsOm_map _ x).2 hb.2.1, hω hb.2.2⟩,
      fun hb => ⟨a5 hb.1, b5 hb.2.1, (IsOm_map _ x).2 hb.2.2.1, hω hb.2.2.2⟩,
      fun V hV hc => ⟨a6 V hV hc.1, b6 V hV hc.2⟩⟩
    simp only [ev, map] at c2 ⊢; rw [c2, a2, b2]

/-- **The inverse base change on terms.** -/
theorem unUp {κ σ τ : Ordinal.{0}} (h : Bases σ τ) (hκσ : κ ≤ σ) (t : UnT false) (hw : WF σ t)
    (hl : Lv (· ∈ Tset σ) t) (hq : Qs κ t) :
    ev τ (t.map (up σ τ)) ∈ TB τ σ ∧ pi σ τ (ev τ (t.map (up σ τ))) = ev σ t ∧ WF τ (t.map (up σ τ)) := by
  obtain ⟨a1, a2, a3, -⟩ := unUpB h hκσ t hw hl hq
  exact ⟨a1, a2, a3⟩

/-- `π_{σ,τ}⁻¹(t[σ; p]) = t[τ; π⁻¹ p]`. -/
theorem unUp_eq {κ σ τ : Ordinal.{0}} (h : Bases σ τ) (hκσ : κ ≤ σ) (t : UnT false) (hw : WF σ t)
    (hl : Lv (· ∈ Tset σ) t) (hq : Qs κ t) :
    up σ τ (ev σ t) = ev τ (t.map (up σ τ)) ∧ WF τ (t.map (up σ τ)) := by
  obtain ⟨a1, a2, a3⟩ := unUp h hκσ t hw hl hq
  exact ⟨by rw [← a2]; exact up_pi h a1, a3⟩

/-- **The segment move on terms**: `mv b c (t[b; p]) = t[c; mv b c p]`. -/
theorem unMv {κ b c : Ordinal.{0}} (hb : InE b) (hb1 : b < Om1) (hc : InE c) (hc1 : c < Om1) (hκb : κ ≤ b)
    (hκc : κ ≤ c) (t : UnT false) (hq : Qs κ t) (hw : WF b t) (hl : Lv (· ∈ TB b κ) t) :
    mv b c (ev b t) = ev c (t.map (mv b c)) ∧ WF c (t.map (mv b c)) := by
  rcases lt_trichotomy c b with hcb | rfl | hbc
  · have hmv : mv b c = pi c b := by unfold mv; rw [if_pos hcb]
    have hB : Bases c b := ⟨hc, hb, hcb, hb1⟩
    obtain ⟨-, a2, a3⟩ := unDown hB hκc t hw (Lv_mono (fun p hp => Ub.ub_TB_mono hκc hp) t hl) hq
    rw [hmv]; exact ⟨a2, a3⟩
  · have hmv : mv c c = id := by unfold mv; simp
    rw [hmv, map_id]; exact ⟨rfl, hw⟩
  · have hmv : mv b c = up b c := by unfold mv; rw [if_neg (not_lt.2 hbc.le), if_pos hbc]
    have hB : Bases b c := ⟨hb, hc, hbc, hc1⟩
    rw [hmv]
    exact unUp_eq hB hκb t hw (Lv_mono (fun p hp => hp.1) t hl) hq

/-! ## The translations of [W07a] Def 6.2 -/

/-- **`t^α_τ` on terms of both sorts** ([W07a] Def 6.2, Lemma 6.3 through `R2.vt_wbar`, `R2.uhVt_tr` (i) and
`R2.ukVt_tr3` (i), whose condition `α ≤ rjDat Γ` is `datM` at `α`). -/
theorem unTrAB {κ τ : Ordinal.{0}} (hB : Bases κ τ) {n : ℕ} (hn : 1 ≤ n) :
    ∀ {k : Bool} (t : UnT k), Qs κ t → Lv (· ∈ Tset (Dl τ n)) t → WF (Dl τ n) t → Nd (Dl τ n) (· < Dp τ n) t →
      WF τ (tr (Dl τ n) t) ∧ ev τ (tr (Dl τ n) t) = ev (Dl τ n) t ∧
      (HbS (Dl τ n) t → HbS τ (tr (Dl τ n) t)) ∧ (FNF (Dl τ n) t → FNF τ (tr (Dl τ n) t)) ∧
      (∀ V, Lf (fun c => ev τ c < V) (tr (Dl τ n) t) ↔ Lf (fun c => ev (Dl τ n) c < V) t)
  | _, .par _, _, _, _, _ => ⟨trivial, rfl, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
  | _, .add s t, hq, hl, hw, hd => by
    obtain ⟨a1, a2, -⟩ := unTrAB hB hn s hq.1 hl.1 hw.1 hd.1
    obtain ⟨b1, b2, -⟩ := unTrAB hB hn t hq.2 hl.2 hw.2 hd.2
    refine ⟨⟨a1, b1⟩, ?_, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
    simp only [tr, ev]; rw [a2, b2]
  | _, .base, _, _, _, _ => ⟨trivial, rfl, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
  | _, .th1 s, hq, hl, hw, hd => by
    obtain ⟨a1, a2, -⟩ := unTrAB hB hn s hq hl hw.1 hd
    obtain ⟨hτα, hαE, -⟩ := Dl_E hB.2.1 hB.2.2.2 hn
    have hα1 : Dl τ n < Om1 := (Dl_spec hB.2.1 hB.2.2.2 n).2.1
    have hab : τ + Dl τ n = Dl τ n :=
      add_of_omega0_opow_le (show τ < ω ^ Dl τ n by rw [hαE]; exact hτα) (le_of_eq hαE)
    have hlt : Dl τ n + ev (Dl τ n) s < Om1 := Om1_add_lt hα1 hw.2
    refine ⟨⟨⟨trivial, a1⟩, ?_⟩, ?_, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
    · simp only [ev]; rw [a2]; exact hlt
    · simp only [tr, ev]
      rw [a2, vt_wbar hB.2.1 hB.2.2.2 hlt, vt_wbar hαE hα1 hw.2, ← add_assoc, hab]
  | _, .thc q r, hq, hl, hw, hd => by
    obtain ⟨a1, a2, -⟩ := unTrAB hB hn r hq.2 hl hw.1 hd.2
    obtain ⟨hτα, hαE, -⟩ := Dl_E hB.2.1 hB.2.2.2 hn
    have hα1 : Dl τ n < Om1 := (Dl_spec hB.2.1 hB.2.2.2 n).2.1
    have hBα : Bases κ (Dl τ n) := ⟨hB.1, hαE, hB.2.2.1.trans hτα, hα1⟩
    have hlt : Dl τ n + ev (Dl τ n) r < Om1 := Om1_add_lt hα1 hw.2
    have hrT := unMem hBα r hl hw.1 hq.2
    have hargT := (uh_arg_T hBα hq.1 hrT hw.2).1
    have e := (uhVt_tr hB.2.1 hB.2.2.2 hn hq.1.1 hq.1.2.1 (hq.1.2.2.trans hB.2.2.1) hw.2).1 hargT hd.1
    refine ⟨⟨⟨trivial, a1⟩, ?_⟩, ?_, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
    · simp only [ev]; rw [a2]; exact hlt
    · simp only [tr, ev]; rw [a2, e]
  | _, .thg m G r, hq, hl, hw, hd => by
    obtain ⟨a1, a2, -⟩ := unTrAB hB hn r hq.2 hl.2 hw.2.1 hd.2.2
    obtain ⟨l1, l2, l4, l5, l6⟩ := unTrAB hB hn G hq.1 hl.1 hw.1 hd.2.1
    obtain ⟨hτα, hαE, -⟩ := Dl_E hB.2.1 hB.2.2.2 hn
    have hα1 : Dl τ n < Om1 := (Dl_spec hB.2.1 hB.2.2.2 n).2.1
    have hBα : Bases κ (Dl τ n) := ⟨hB.1, hαE, hB.2.2.1.trans hτα, hα1⟩
    obtain ⟨M, hM, hM1⟩ := UnT.ev_dvd (τ := Dl τ n) G hw.2.2.gs
    have hdat := (datM hBα m G hl.1 hw.1 hq.1 hw.2.2.nf hw.2.2.hd).1
    have hME : Om1 * M < Gg.ggE := hM ▸ UnT.ev_lt_E G hw.1
    have hmem := hw.2.2.mem
    have hlt := hd.1
    rw [hM] at hmem hlt hdat
    obtain ⟨m1, e1⟩ := (ukVt_tr3 hB.2.1 hB.2.2.2 hn hM1 hME hdat hw.2.2.r1).1 hmem hlt
    have hev : ev τ (tr (Dl τ n) G) + ev τ (tr (Dl τ n) r) = Om1 * M + ev (Dl τ n) r := by
      rw [l2, a2, hM]
    refine ⟨⟨l1, a1, ⟨by rw [a2]; exact hw.2.2.r1, (Gs_tr _ G).2 hw.2.2.gs, NfM_imp l4 l5 m hw.2.2.nf,
      HdM_tr hτα.le m G hw.2.2.hd, by rw [hev]; exact m1, ?_, ?_⟩⟩, ?_, fun _ => trivial, fun _ => trivial,
      fun _ => Iff.rfl⟩
    · rw [hev, ← e1, l6, ← hM]; exact hw.2.2.bd
    · rw [hev, ← e1, a2, ← hM]; exact hw.2.2.rb
    · simp only [tr, ev]; rw [hev, ← e1, hM]
  | _, .lf c, hq, hl, hw, hd => by
    obtain ⟨a1, a2, -⟩ := unTrAB hB hn c hq hl hw.1 hd
    refine ⟨⟨a1, by rw [a2]; exact hw.2⟩, a2, fun _ => trivial, fun _ => trivial, fun V => ?_⟩
    show ev τ (tr (Dl τ n) c) < V ↔ ev (Dl τ n) c < V
    rw [a2]
  | _, .om b, hq, hl, hw, hd => by
    obtain ⟨a1, a2, a4, a5, a6⟩ := unTrAB hB hn b hq hl hw hd
    refine ⟨a1, ?_, a4, a5, a6⟩
    simp only [tr, ev]; rw [a2]
  | _, .ad x y, hq, hl, hw, hd => by
    obtain ⟨a1, a2, a4, a5, a6⟩ := unTrAB hB hn x hq.1 hl.1 hw.1 hd.1
    obtain ⟨b1, b2, b4, b5, b6⟩ := unTrAB hB hn y hq.2 hl.2 hw.2 hd.2
    refine ⟨⟨a1, b1⟩, ?_, fun hb => ⟨a4 hb.1, (IsOm_tr _ x).2 hb.2.1, by rw [a2, b2]; exact hb.2.2⟩,
      fun hb => ⟨a5 hb.1, b5 hb.2.1, (IsOm_tr _ x).2 hb.2.2.1, by rw [a2, b2]; exact hb.2.2.2⟩,
      fun V => and_congr (a6 V) (b6 V)⟩
    simp only [tr, ev]; rw [a2, b2]

/-- **`t^α_τ` is correct** (`α = Dl τ n`, `n ≥ 1`): `tr α t` has the argument bounds and node conditions over `τ`
and `(tr α t)[τ] = t[α]`. -/
theorem unTrA {κ τ : Ordinal.{0}} (hB : Bases κ τ) {n : ℕ} (hn : 1 ≤ n) (t : UnT false) (hq : Qs κ t)
    (hl : Lv (· ∈ Tset (Dl τ n)) t) (hw : WF (Dl τ n) t) (hd : Nd (Dl τ n) (· < Dp τ n) t) :
    WF τ (tr (Dl τ n) t) ∧ ev τ (tr (Dl τ n) t) = ev (Dl τ n) t := by
  obtain ⟨a1, a2, -⟩ := unTrAB hB hn t hq hl hw hd
  exact ⟨a1, a2⟩

/-- **`t^τ_α` on terms of both sorts** ([W07a] Def 6.2, Lemma 6.3 through `R2.vt_wbar`, `R2.uhVt_tr` (ii) and
`R2.ukVt_tr3` (ii)); the syntactic mode conditions over `α` (`HdA α t`) and the parameters in `T^α` give the
decision `Γ^{*α} ≥ α`. -/
theorem unTrBB {κ τ : Ordinal.{0}} (hB : Bases κ τ) {n : ℕ} (hn : 1 ≤ n) :
    ∀ {k : Bool} (t : UnT k), Qs κ t → Lv (· ∈ Tset τ) (tr (Dl τ n) t) → WF τ (tr (Dl τ n) t) →
      Nd τ (· < Dp τ n) (tr (Dl τ n) t) → HdA (Dl τ n) t → Lv (· ∈ Tset (Dl τ n)) t →
      WF (Dl τ n) t ∧ ev τ (tr (Dl τ n) t) = ev (Dl τ n) t ∧
      (HbS τ (tr (Dl τ n) t) → HbS (Dl τ n) t) ∧ (FNF τ (tr (Dl τ n) t) → FNF (Dl τ n) t) ∧
      (∀ V, Lf (fun c => ev τ c < V) (tr (Dl τ n) t) ↔ Lf (fun c => ev (Dl τ n) c < V) t)
  | _, .par _, _, _, _, _, _, _ => ⟨trivial, rfl, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
  | _, .add s t, hq, hl, hw, hd, hh, hla => by
    obtain ⟨a1, a2, -⟩ := unTrBB hB hn s hq.1 hl.1 hw.1 hd.1 hh.1 hla.1
    obtain ⟨b1, b2, -⟩ := unTrBB hB hn t hq.2 hl.2 hw.2 hd.2 hh.2 hla.2
    refine ⟨⟨a1, b1⟩, ?_, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
    simp only [tr, ev]; rw [a2, b2]
  | _, .base, _, _, _, _, _, _ => ⟨trivial, rfl, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
  | _, .th1 s, hq, hl, hw, hd, hh, hla => by
    obtain ⟨a1, a2, -⟩ := unTrBB hB hn s hq hl.2 hw.1.2 hd.2 hh hla
    obtain ⟨hτα, hαE, -⟩ := Dl_E hB.2.1 hB.2.2.2 hn
    have hα1 : Dl τ n < Om1 := (Dl_spec hB.2.1 hB.2.2.2 n).2.1
    have hab : τ + Dl τ n = Dl τ n :=
      add_of_omega0_opow_le (show τ < ω ^ Dl τ n by rw [hαE]; exact hτα) (le_of_eq hαE)
    have h2 := hw.2
    simp only [ev] at h2; rw [a2] at h2
    have hs1 : ev (Dl τ n) s < Om1 := lt_of_le_of_lt le_add_self h2
    refine ⟨⟨a1, hs1⟩, ?_, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
    simp only [tr, ev]
    rw [a2, vt_wbar hB.2.1 hB.2.2.2 h2, vt_wbar hαE hα1 hs1, ← add_assoc, hab]
  | _, .thc q r, hq, hl, hw, hd, hh, hla => by
    obtain ⟨a1, a2, -⟩ := unTrBB hB hn r hq.2 hl.2 hw.1.2 hd.2.2 hh hla
    have h2 := hw.2
    simp only [ev] at h2
    have hr1 : ev (Dl τ n) r < Om1 := by rw [← a2]; exact lt_of_le_of_lt le_add_self h2
    have hαT : Dl τ n ∈ Tset τ := (Dl_spec hB.2.1 hB.2.2.2 n).1
    have hrT : ev τ (tr (Dl τ n) r) ∈ Tset τ := unMem hB _ hl.2 hw.1.2 (Qs_tr _ r hq.2)
    have hsT : Dl τ n + ev τ (tr (Dl τ n) r) ∈ Tset τ := vzT_add hB.2.1 hB.2.2.2 hαT hrT
    have hargT := (uh_arg_T hB hq.1 hsT h2).1
    have hd1 := hd.1
    simp only [ev] at hd1
    rw [a2] at hargT hd1
    have e := (uhVt_tr hB.2.1 hB.2.2.2 hn hq.1.1 hq.1.2.1 (hq.1.2.2.trans hB.2.2.1) hr1).2 hargT hd1
    refine ⟨⟨a1, hr1⟩, ?_, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
    simp only [tr, ev]; rw [a2, e]
  | _, .thg m G r, hq, hl, hw, hd, hh, hla => by
    obtain ⟨a1, a2, -⟩ := unTrBB hB hn r hq.2 hl.2 hw.2.1 hd.2.2 hh.2.2 hla.2
    obtain ⟨l1, l2, l4, l5, l6⟩ := unTrBB hB hn G hq.1 hl.1 hw.1 hd.2.1 hh.2.1 hla.1
    obtain ⟨hτα, hαE, -⟩ := Dl_E hB.2.1 hB.2.2.2 hn
    have hα1 : Dl τ n < Om1 := (Dl_spec hB.2.1 hB.2.2.2 n).2.1
    have hBα : Bases κ (Dl τ n) := ⟨hB.1, hαE, hB.2.2.1.trans hτα, hα1⟩
    have hgs : Gs G := (Gs_tr _ G).1 hw.2.2.gs
    have hnf : NfM m (Dl τ n) G := NfM_imp l4 l5 m hw.2.2.nf
    obtain ⟨M, hM, hM1⟩ := UnT.ev_dvd (τ := Dl τ n) G hgs
    have hdat := (datM hBα m G hla.1 l1 hq.1 hnf hh.1).1
    have hME : Om1 * M < Gg.ggE := hM ▸ UnT.ev_lt_E G l1
    have hr1 : ev (Dl τ n) r < Om1 := by rw [← a2]; exact hw.2.2.r1
    have hev : ev τ (tr (Dl τ n) G) + ev τ (tr (Dl τ n) r) = Om1 * M + ev (Dl τ n) r := by
      rw [l2, a2, hM]
    have hmem := hw.2.2.mem
    have hlt := hd.1
    rw [hev] at hmem hlt
    rw [hM] at hdat
    obtain ⟨m1, e1⟩ := (ukVt_tr3 hB.2.1 hB.2.2.2 hn hM1 hME hdat hr1).2 hmem hlt
    refine ⟨⟨l1, a1, ⟨hr1, hgs, hnf, hh.1, by rw [hM]; exact m1, ?_, ?_⟩⟩, ?_, fun _ => trivial,
      fun _ => trivial, fun _ => Iff.rfl⟩
    · rw [hM, ← e1, ← hev, ← l6]; exact hw.2.2.bd
    · rw [hM, ← e1, ← hev, ← a2]; exact hw.2.2.rb
    · simp only [tr, ev]; rw [hev, e1, hM]
  | _, .lf c, hq, hl, hw, hd, hh, hla => by
    obtain ⟨a1, a2, -⟩ := unTrBB hB hn c hq hl hw.1 hd hh hla
    have h2 : ev τ (tr (Dl τ n) c) < Om1 := hw.2
    refine ⟨⟨a1, a2 ▸ h2⟩, a2, fun _ => trivial, fun _ => trivial, fun V => ?_⟩
    show ev τ (tr (Dl τ n) c) < V ↔ ev (Dl τ n) c < V
    rw [a2]
  | _, .om b, hq, hl, hw, hd, hh, hla => by
    obtain ⟨a1, a2, a4, a5, a6⟩ := unTrBB hB hn b hq hl hw hd hh hla
    refine ⟨a1, ?_, a4, a5, a6⟩
    simp only [tr, ev]; rw [a2]
  | _, .ad x y, hq, hl, hw, hd, hh, hla => by
    obtain ⟨a1, a2, a4, a5, a6⟩ := unTrBB hB hn x hq.1 hl.1 hw.1 hd.1 hh.1 hla.1
    obtain ⟨b1, b2, b4, b5, b6⟩ := unTrBB hB hn y hq.2 hl.2 hw.2 hd.2 hh.2 hla.2
    refine ⟨⟨a1, b1⟩, ?_, fun hb => ⟨a4 hb.1, (IsOm_tr _ x).1 hb.2.1, by rw [← a2, ← b2]; exact hb.2.2⟩,
      fun hb => ⟨a5 hb.1, b5 hb.2.1, (IsOm_tr _ x).1 hb.2.2.1, by rw [← a2, ← b2]; exact hb.2.2.2⟩,
      fun V => and_congr (a6 V) (b6 V)⟩
    simp only [tr, ev]; rw [a2, b2]

/-- **`t^τ_α` is correct** (`α = Dl τ n`, `n ≥ 1`): if `tr α t` has the argument bounds and node conditions over
`τ` with node values below `α⁺`, the syntactic mode conditions hold over `α` and the parameters of `t` lie in `T^α`,
then `t` has them over `α` and `(tr α t)[τ] = t[α]`. -/
theorem unTrB {κ τ : Ordinal.{0}} (hB : Bases κ τ) {n : ℕ} (hn : 1 ≤ n) (t : UnT false) (hq : Qs κ t)
    (hl : Lv (· ∈ Tset τ) (tr (Dl τ n) t)) (hw : WF τ (tr (Dl τ n) t)) (hd : Nd τ (· < Dp τ n) (tr (Dl τ n) t))
    (hh : HdA (Dl τ n) t) (hla : Lv (· ∈ Tset (Dl τ n)) t) :
    WF (Dl τ n) t ∧ ev τ (tr (Dl τ n) t) = ev (Dl τ n) t := by
  obtain ⟨a1, a2, -⟩ := unTrBB hB hn t hq hl hw hd hh hla
  exact ⟨a1, a2⟩

/-! ## The terms of `Uk.UkT` as head-mode terms -/

/-- The terms of `Uh.UhT`. -/
def ofUhN : UhT → UnT false
  | .par p => .par p
  | .add s t => .add (ofUhN s) (ofUhN t)
  | .base => .base
  | .th1 s => .th1 (ofUhN s)
  | .thc q r => .thc q (ofUhN r)

/-- The level terms of `Uk.UkL`. -/
def ofUkL : Uk.UkL → UnT true
  | .lf c => .lf (ofUhN c)
  | .om b => .om (ofUkL b)
  | .ad x y => .ad (ofUkL x) (ofUkL y)

/-- **The terms of `Uk.UkT`**, the `thg`-nodes in the head mode. -/
def ofUk : Uk.UkT → UnT false
  | .par p => .par p
  | .add s t => .add (ofUk s) (ofUk t)
  | .base => .base
  | .th1 s => .th1 (ofUk s)
  | .thc q r => .thc q (ofUk r)
  | .thg G r => .thg false (ofUkL G) (ofUk r)

theorem ofUhN_ev (τ : Ordinal.{0}) : ∀ t : UhT, ev τ (ofUhN t) = UhT.ev τ t
  | .par _ => rfl
  | .add s t => by simp only [ofUhN, ev, UhT.ev, ofUhN_ev τ s, ofUhN_ev τ t]
  | .base => rfl
  | .th1 s => by simp only [ofUhN, ev, UhT.ev, ofUhN_ev τ s]
  | .thc _ r => by simp only [ofUhN, ev, UhT.ev, ofUhN_ev τ r]

theorem ofUhN_map (f : Ordinal.{0} → Ordinal.{0}) : ∀ t : UhT, ofUhN (t.map f) = (ofUhN t).map f
  | .par _ => rfl
  | .add s t => by simp only [ofUhN, map, UhT.map, ofUhN_map f s, ofUhN_map f t]
  | .base => rfl
  | .th1 s => by simp only [ofUhN, map, UhT.map, ofUhN_map f s]
  | .thc _ r => by simp only [ofUhN, map, UhT.map, ofUhN_map f r]

theorem ofUhN_WF (τ : Ordinal.{0}) : ∀ t : UhT, WF τ (ofUhN t) ↔ UhT.WF τ t
  | .par _ => Iff.rfl
  | .add s t => by simp only [ofUhN, WF, UhT.WF]; rw [ofUhN_WF τ s, ofUhN_WF τ t]
  | .base => Iff.rfl
  | .th1 s => by simp only [ofUhN, WF, UhT.WF]; rw [ofUhN_WF τ s, ofUhN_ev τ s]
  | .thc _ r => by simp only [ofUhN, WF, UhT.WF]; rw [ofUhN_WF τ r, ofUhN_ev τ r]

theorem ofUhN_Lv {P : Ordinal.{0} → Prop} : ∀ t : UhT, Lv P (ofUhN t) ↔ UhT.Lv P t
  | .par _ => Iff.rfl
  | .add s t => by simp only [ofUhN, Lv, UhT.Lv]; rw [ofUhN_Lv s, ofUhN_Lv t]
  | .base => Iff.rfl
  | .th1 s => by simp only [ofUhN, Lv, UhT.Lv]; exact ofUhN_Lv s
  | .thc _ r => by simp only [ofUhN, Lv, UhT.Lv]; exact ofUhN_Lv r

theorem ofUhN_Qs {κ : Ordinal.{0}} : ∀ t : UhT, Qs κ (ofUhN t) ↔ UhT.Qs κ t
  | .par _ => Iff.rfl
  | .add s t => by simp only [ofUhN, Qs, UhT.Qs]; rw [ofUhN_Qs s, ofUhN_Qs t]
  | .base => Iff.rfl
  | .th1 s => by simp only [ofUhN, Qs, UhT.Qs]; exact ofUhN_Qs s
  | .thc _ r => by simp only [ofUhN, Qs, UhT.Qs]; rw [ofUhN_Qs r]

theorem ofUhN_HiC {τ : Ordinal.{0}} : ∀ t : UhT, Uk.HiC τ t → HiC τ (ofUhN t)
  | .par _, h => h
  | .add s _, h => ofUhN_HiC s h
  | .base, _ => trivial
  | .th1 _, h => h.elim
  | .thc _ _, h => h.elim

theorem ofUkL_ev (τ : Ordinal.{0}) : ∀ G : Uk.UkL, ev τ (ofUkL G) = Uk.UkL.ev τ G
  | .lf c => ofUhN_ev τ c
  | .om b => by simp only [ofUkL, ev, Uk.UkL.ev, ofUkL_ev τ b]
  | .ad x y => by simp only [ofUkL, ev, Uk.UkL.ev, ofUkL_ev τ x, ofUkL_ev τ y]

theorem ofUkL_map (f : Ordinal.{0} → Ordinal.{0}) : ∀ G : Uk.UkL, ofUkL (G.map f) = (ofUkL G).map f
  | .lf c => by simp only [ofUkL, map, Uk.UkL.map, ofUhN_map]
  | .om b => by simp only [ofUkL, map, Uk.UkL.map, ofUkL_map f b]
  | .ad x y => by simp only [ofUkL, map, Uk.UkL.map, ofUkL_map f x, ofUkL_map f y]

theorem ofUkL_Lv {P : Ordinal.{0} → Prop} : ∀ G : Uk.UkL, Lv P (ofUkL G) ↔ Uk.UkL.Lf (UhT.Lv P) G
  | .lf c => ofUhN_Lv c
  | .om b => ofUkL_Lv b
  | .ad x y => and_congr (ofUkL_Lv x) (ofUkL_Lv y)

theorem ofUkL_Qs {κ : Ordinal.{0}} : ∀ G : Uk.UkL, Qs κ (ofUkL G) ↔ Uk.UkL.Lf (UhT.Qs κ) G
  | .lf c => ofUhN_Qs c
  | .om b => ofUkL_Qs b
  | .ad x y => and_congr (ofUkL_Qs x) (ofUkL_Qs y)

theorem ofUkL_WF (τ : Ordinal.{0}) :
    ∀ G : Uk.UkL, WF τ (ofUkL G) ↔ Uk.UkL.Lf (fun c => UhT.WF τ c ∧ UhT.ev τ c < Om1) G
  | .lf c => by
    show WF τ (ofUhN c) ∧ ev τ (ofUhN c) < Om1 ↔ _
    rw [ofUhN_WF, ofUhN_ev]; exact Iff.rfl
  | .om b => ofUkL_WF τ b
  | .ad x y => and_congr (ofUkL_WF τ x) (ofUkL_WF τ y)

theorem ofUkL_Gs : ∀ G : Uk.UkL, Gs (ofUkL G) ↔ Uk.UkL.Gs G
  | .lf _ => Iff.rfl
  | .om _ => Iff.rfl
  | .ad x y => and_congr (ofUkL_Gs x) (ofUkL_Gs y)

theorem ofUkL_IsOm : ∀ G : Uk.UkL, IsOm (ofUkL G) ↔ Uk.UkL.IsOm G
  | .lf _ => Iff.rfl
  | .om _ => Iff.rfl
  | .ad _ _ => Iff.rfl

theorem ofUkL_HbS (τ : Ordinal.{0}) : ∀ G : Uk.UkL, HbS τ (ofUkL G) ↔ Uk.UkL.HbS τ G
  | .lf _ => Iff.rfl
  | .om b => ofUkL_HbS τ b
  | .ad x y => by
    exact and_congr (ofUkL_HbS τ x) (and_congr (ofUkL_IsOm x) (by rw [ofUkL_ev, ofUkL_ev]))

theorem ofUkL_Hd {τ : Ordinal.{0}} : ∀ G : Uk.UkL, Uk.UkL.Hd τ G → Hd τ (ofUkL G)
  | .lf c, h => ofUhN_HiC c h
  | .om b, h => ofUkL_Hd b h
  | .ad x _, h => ofUkL_Hd x h

theorem ofUkL_Lf {P : UnT false → Prop} {Q : UhT → Prop} (hPQ : ∀ c, Q c → P (ofUhN c)) :
    ∀ G : Uk.UkL, Uk.UkL.Lf Q G → Lf P (ofUkL G)
  | .lf c, h => hPQ c h
  | .om b, h => ofUkL_Lf hPQ b h
  | .ad x y, h => ⟨ofUkL_Lf hPQ x h.1, ofUkL_Lf hPQ y h.2⟩

theorem ofUk_ev (τ : Ordinal.{0}) : ∀ t : Uk.UkT, ev τ (ofUk t) = Uk.UkT.ev τ t
  | .par _ => rfl
  | .add s t => by simp only [ofUk, ev, Uk.UkT.ev, ofUk_ev τ s, ofUk_ev τ t]
  | .base => rfl
  | .th1 s => by simp only [ofUk, ev, Uk.UkT.ev, ofUk_ev τ s]
  | .thc _ r => by simp only [ofUk, ev, Uk.UkT.ev, ofUk_ev τ r]
  | .thg G r => by simp only [ofUk, ev, Uk.UkT.ev, ofUkL_ev τ G, ofUk_ev τ r]

theorem ofUk_map (f : Ordinal.{0} → Ordinal.{0}) : ∀ t : Uk.UkT, ofUk (t.map f) = (ofUk t).map f
  | .par _ => rfl
  | .add s t => by simp only [ofUk, map, Uk.UkT.map, ofUk_map f s, ofUk_map f t]
  | .base => rfl
  | .th1 s => by simp only [ofUk, map, Uk.UkT.map, ofUk_map f s]
  | .thc _ r => by simp only [ofUk, map, Uk.UkT.map, ofUk_map f r]
  | .thg G r => by simp only [ofUk, map, Uk.UkT.map, ofUkL_map f G, ofUk_map f r]

theorem ofUk_Lv {P : Ordinal.{0} → Prop} : ∀ t : Uk.UkT, Lv P (ofUk t) ↔ Uk.UkT.Lv P t
  | .par _ => Iff.rfl
  | .add s t => and_congr (ofUk_Lv s) (ofUk_Lv t)
  | .base => Iff.rfl
  | .th1 s => ofUk_Lv s
  | .thc _ r => ofUk_Lv r
  | .thg G r => and_congr (ofUkL_Lv G) (ofUk_Lv r)

theorem ofUk_Qs {κ : Ordinal.{0}} : ∀ t : Uk.UkT, Qs κ (ofUk t) ↔ Uk.UkT.Qs κ t
  | .par _ => Iff.rfl
  | .add s t => and_congr (ofUk_Qs s) (ofUk_Qs t)
  | .base => Iff.rfl
  | .th1 s => ofUk_Qs s
  | .thc _ r => and_congr Iff.rfl (ofUk_Qs r)
  | .thg G r => and_congr (ofUkL_Qs G) (ofUk_Qs r)

/-- **The node conditions of `Uk.UkT` give those of the head mode.** -/
theorem ofUk_WF (τ : Ordinal.{0}) : ∀ t : Uk.UkT, Uk.UkT.WF τ t → WF τ (ofUk t)
  | .par _, _ => trivial
  | .add s t, h => ⟨ofUk_WF τ s h.1, ofUk_WF τ t h.2⟩
  | .base, _ => trivial
  | .th1 s, h => ⟨ofUk_WF τ s h.1, by rw [ofUk_ev]; exact h.2⟩
  | .thc _ r, h => ⟨ofUk_WF τ r h.1, by rw [ofUk_ev]; exact h.2⟩
  | .thg G r, h => by
    obtain ⟨hr, hn⟩ := h
    refine ⟨(ofUkL_WF τ G).2 hn.wl, ofUk_WF τ r hr, ?_⟩
    rw [ofUk_ev]
    refine ⟨hn.r1, (ofUkL_Gs G).2 hn.gs, (ofUkL_HbS τ G).2 hn.hb, ofUkL_Hd G hn.hd,
      by rw [ofUkL_ev]; exact hn.mem, ?_, by rw [ofUkL_ev]; exact hn.rb⟩
    rw [ofUkL_ev]
    exact ofUkL_Lf (fun c hc => by show ev τ (ofUhN c) < _; rw [ofUhN_ev]; exact hc) G hn.bd

/-- The countable-argument terms of `Ub.UbT` (through `Uh.ofUb`). -/
def ofUbn (t : Ub.UbT) : UnT false := ofUhN (ofUb t)

theorem ofUbn_ev (τ : Ordinal.{0}) (t : Ub.UbT) (hA : Ub.UbT.IsA t) : ev τ (ofUbn t) = Ub.UbT.ev τ t := by
  rw [ofUbn, ofUhN_ev, ofUb_ev τ t hA]

theorem ofUbn_map (f : Ordinal.{0} → Ordinal.{0}) (t : Ub.UbT) : ofUbn (t.map f) = (ofUbn t).map f := by
  simp only [ofUbn, ofUb_map, ofUhN_map]

theorem ofUbn_WF (τ : Ordinal.{0}) (t : Ub.UbT) (hA : Ub.UbT.IsA t) : WF τ (ofUbn t) ↔ Ub.UbT.WF τ t := by
  rw [ofUbn, ofUhN_WF, ofUb_WF τ t hA]

theorem ofUbn_Lv {P : Ordinal.{0} → Prop} (t : Ub.UbT) (hA : Ub.UbT.IsA t) : Lv P (ofUbn t) ↔ Ub.UbT.Lv P t := by
  rw [ofUbn, ofUhN_Lv, ofUb_Lv t hA]

theorem ofUbn_Qs (κ : Ordinal.{0}) (t : Ub.UbT) : Qs κ (ofUbn t) := (ofUhN_Qs _).2 (ofUb_Qs κ t)

/-! ## Finite sets of parameters and of level data -/

namespace UnT

/-- The set of parameters (also inside the level terms). -/
noncomputable def lvs : {k : Bool} → UnT k → Finset Ordinal.{0}
  | _, par p => {p}
  | _, add s t => lvs s ∪ lvs t
  | _, base => ∅
  | _, th1 s => lvs s
  | _, thc _ r => lvs r
  | _, thg _ G r => lvs G ∪ lvs r
  | _, lf c => lvs c
  | _, om b => lvs b
  | _, ad x y => lvs x ∪ lvs y

/-- The data `rjDat q` of the constant levels (also inside the level terms). -/
noncomputable def lvq : {k : Bool} → UnT k → Finset Ordinal.{0}
  | _, par _ => ∅
  | _, add s t => lvq s ∪ lvq t
  | _, base => ∅
  | _, th1 s => lvq s
  | _, thc q r => insert (Rj.rjDat q) (lvq r)
  | _, thg _ G r => lvq G ∪ lvq r
  | _, lf c => lvq c
  | _, om b => lvq b
  | _, ad x y => lvq x ∪ lvq y

theorem Lv_lvs : ∀ {k : Bool} (t : UnT k), Lv (· ∈ lvs t) t
  | _, par _ => Finset.mem_singleton_self _
  | _, add s t => ⟨Lv_mono (fun _ hp => Finset.mem_union_left _ hp) s (Lv_lvs s),
      Lv_mono (fun _ hp => Finset.mem_union_right _ hp) t (Lv_lvs t)⟩
  | _, base => trivial
  | _, th1 s => Lv_lvs s
  | _, thc _ r => Lv_lvs r
  | _, thg _ G r => ⟨Lv_mono (fun _ hp => Finset.mem_union_left _ hp) G (Lv_lvs G),
      Lv_mono (fun _ hp => Finset.mem_union_right _ hp) r (Lv_lvs r)⟩
  | _, lf c => Lv_lvs c
  | _, om b => Lv_lvs b
  | _, ad x y => ⟨Lv_mono (fun _ hp => Finset.mem_union_left _ hp) x (Lv_lvs x),
      Lv_mono (fun _ hp => Finset.mem_union_right _ hp) y (Lv_lvs y)⟩

theorem mem_lvs {P : Ordinal.{0} → Prop} : ∀ {k : Bool} {t : UnT k}, Lv P t → ∀ p ∈ lvs t, P p
  | _, par _, h, p, hp => by rw [lvs, Finset.mem_singleton] at hp; rw [hp]; exact h
  | _, add s t, h, p, hp => by
    rcases Finset.mem_union.1 hp with hp | hp
    · exact mem_lvs (t := s) h.1 p hp
    · exact mem_lvs (t := t) h.2 p hp
  | _, base, _, p, hp => absurd hp (Finset.notMem_empty p)
  | _, th1 s, h, p, hp => mem_lvs (t := s) h p hp
  | _, thc _ r, h, p, hp => mem_lvs (t := r) h p hp
  | _, thg _ G r, h, p, hp => by
    rcases Finset.mem_union.1 hp with hp | hp
    · exact mem_lvs (t := G) h.1 p hp
    · exact mem_lvs (t := r) h.2 p hp
  | _, lf c, h, p, hp => mem_lvs (t := c) h p hp
  | _, om b, h, p, hp => mem_lvs (t := b) h p hp
  | _, ad x y, h, p, hp => by
    rcases Finset.mem_union.1 hp with hp | hp
    · exact mem_lvs (t := x) h.1 p hp
    · exact mem_lvs (t := y) h.2 p hp

/-- Levels over `b` whose data are below `γ` are levels over `γ`. -/
theorem Qs_of_lvq {b γ : Ordinal.{0}} : ∀ {k : Bool} (t : UnT k), Qs b t → (∀ q ∈ lvq t, q < γ) → Qs γ t
  | _, par _, _, _ => trivial
  | _, add s t, h, hq => ⟨Qs_of_lvq s h.1 (fun q hq' => hq q (Finset.mem_union_left _ hq')),
      Qs_of_lvq t h.2 (fun q hq' => hq q (Finset.mem_union_right _ hq'))⟩
  | _, base, _, _ => trivial
  | _, th1 s, h, hq => Qs_of_lvq s h hq
  | _, thc _ r, h, hq => ⟨⟨h.1.1, h.1.2.1, hq _ (Finset.mem_insert_self _ _)⟩,
      Qs_of_lvq r h.2 (fun q' hq' => hq q' (Finset.mem_insert_of_mem hq'))⟩
  | _, thg _ G r, h, hq => ⟨Qs_of_lvq G h.1 (fun q hq' => hq q (Finset.mem_union_left _ hq')),
      Qs_of_lvq r h.2 (fun q hq' => hq q (Finset.mem_union_right _ hq'))⟩
  | _, lf c, h, hq => Qs_of_lvq c h hq
  | _, om b, h, hq => Qs_of_lvq b h hq
  | _, ad x y, h, hq => ⟨Qs_of_lvq x h.1 (fun q hq' => hq q (Finset.mem_union_left _ hq')),
      Qs_of_lvq y h.2 (fun q hq' => hq q (Finset.mem_union_right _ hq'))⟩

/-- The data of the levels of a term with levels over `b` are below `b`. -/
theorem lvq_lt {b : Ordinal.{0}} : ∀ {k : Bool} (t : UnT k), Qs b t → ∀ q ∈ lvq t, q < b
  | _, par _, _, q, hq => absurd hq (Finset.notMem_empty q)
  | _, add s t, h, q, hq => by
    rcases Finset.mem_union.1 hq with hq | hq
    · exact lvq_lt s h.1 q hq
    · exact lvq_lt t h.2 q hq
  | _, base, _, q, hq => absurd hq (Finset.notMem_empty q)
  | _, th1 s, h, q, hq => lvq_lt s h q hq
  | _, thc q' r, h, q, hq => by
    rcases Finset.mem_insert.1 hq with rfl | hq
    · exact h.1.2.2
    · exact lvq_lt r h.2 q hq
  | _, thg _ G r, h, q, hq => by
    rcases Finset.mem_union.1 hq with hq | hq
    · exact lvq_lt G h.1 q hq
    · exact lvq_lt r h.2 q hq
  | _, lf c, h, q, hq => lvq_lt c h q hq
  | _, om b, h, q, hq => lvq_lt b h q hq
  | _, ad x y, h, q, hq => by
    rcases Finset.mem_union.1 hq with hq | hq
    · exact lvq_lt x h.1 q hq
    · exact lvq_lt y h.2 q hq

end UnT

end Googology.Trans.PoR.InaccPsi.R2.Un

import Googology.Trans.PoR.InaccPsi.R2.UhTerm
import Googology.Trans.PoR.InaccPsi.R2.SsTh
import Googology.Trans.PoR.InaccPsi.R2.CitedUk

/-!
# Terms whose `ϑ`-levels are terms: the subcase `Γ^* ≥ α` of [W07a] Def 6.2

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`UkT` is `Uh.UhT` with one more node `thg G r` (value `ϑᵗ(Γ + r)`, `Γ = G[τ]`, `r` countable) whose level `Γ` is
itself a term `G : UkL`: **level terms** are built from countable leaves `lf c` (`c : Uh.UhT`, value `c[τ]`), `om b`
(value `Ω₁·ω^{b[τ]}`) and `ad x y` (value `x[τ] + y[τ]`).  So the level may depend on the base (e.g. `ϑᵗ(Ω₁·τ + ρ)` is
`thg (om (lf base)) ρ`, `Ω₁·τ = Ω₁·ω^τ`).  The node conditions over `τ` (`Ng`, part of `WF`):
* **shape** `Gs G` (only `om`/`ad` at the top, so `Ω₁ ∣ Γ`) and the **NF condition at the head** `HbS τ G`: along the
  head chain every `ad x y` has `x = om b` and `y[τ] < x[τ]·ω` (no absorption of the head);
* **the head leaf is high** `Hd τ G` (`HiC`: the head of the leaf is `base` or a parameter `≥ τ`); with `HbS` this
  gives **`τ ≤ rjDat Γ`** (`ukL_dat`), i.e. `Γ^{*τ} ≥ τ`, and the same at every base the term is translated to:
  **the decision `Γ^* ≥ α` is read off the head leaf**;
* membership `Γ + ρ ∈ Tᵗ`, the bounds `c[τ] < ϑᵗ(Γ + ρ)` for every leaf and `ρ < ϑᵗ(Γ + ρ)`.

Every operation computes the values of ALL subterms (`UkL.down`, `UkL.up`, `UkL.trA`, `UkL.trB`), so these
ordinal conditions are carried by `π`, `π⁻¹`, the segment moves and the translations.  The translation of [W07a]
Def 6.2 keeps the level in the third subcase: `tr α (thg G r) = thg (tr α G) (tr α r)`; its correctness is the
cited `R2.ukVt_tr3` (`ukTrA`, `ukTrB`; `ukTrB` asks the head condition at `α`, `HdA α`).

* `ukL_dat` (**`τ ≤ rjDat Γ` from the head**), `UkL.down` / `UkL.up` (**`π` on level terms**: `π(Γ[τ; p]) =
  Γ[σ; π p]`, from the cited `R2.om1_opow_TB_all` through `R2.siOm1_opow_TB`), `UkL.trA` / `UkL.trB`;
* `ukMem`, `ukLe`, `ukDown`, `ukUp`, `ukUp_eq`, `ukMv`, `ukTrA`, `ukTrB` (the `Uh` lemmas for `UkT`);
* `ofUh` (**`Uh.UhT` embeds**: `ofUh_ev`, `ofUh_map`, `ofUh_WF`, `ofUh_Lv`, `ofUh_Qs`).

New definitions: `HiC`, `UkL` (`ev`, `map`, `tr`, `Lf`, `Gs`, `IsOm`, `HbS`, `Hd`), `Ng`, `UkT` (`ev`, `map`, `Lv`,
`Qs`, `WF`, `Nd`, `tr`, `HdA`), `ofUh`.  No new axiom (uses `R2.ukVt_tr3`, `R2.uhVt_tr`).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uk

open Ordinal Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Uh

/-! ## High heads of countable terms -/

/-- **The head of `c` is high over `τ`**: following the left summands, `c` starts with `base` or a parameter `≥ τ`. -/
def HiC (τ : Ordinal.{0}) : UhT → Prop
  | .par p => τ ≤ p
  | .add s _ => HiC τ s
  | .base => True
  | .th1 _ => False
  | .thc _ _ => False

theorem HiC_le {τ : Ordinal.{0}} : ∀ c : UhT, HiC τ c → τ ≤ UhT.ev τ c
  | .par _, h => h
  | .add s _, h => by simp only [UhT.ev]; exact (HiC_le s h).trans le_self_add
  | .base, _ => le_rfl
  | .th1 _, h => h.elim
  | .thc _ _, h => h.elim

theorem HiC_map {τ σ : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} :
    ∀ c : UhT, UhT.Lv (fun p => τ ≤ p → σ ≤ f p) c → HiC τ c → HiC σ (c.map f)
  | .par _, hl, h => hl h
  | .add s _, hl, h => HiC_map s hl.1 h
  | .base, _, _ => trivial
  | .th1 _, _, h => h.elim
  | .thc _ _, _, h => h.elim

theorem HiC_tr {τ a : Ordinal.{0}} (hτa : τ ≤ a) : ∀ c : UhT, HiC a c → HiC τ (UhT.tr a c)
  | .par _, h => hτa.trans h
  | .add s _, h => HiC_tr hτa s h
  | .base, _ => hτa
  | .th1 _, h => h.elim
  | .thc _ _, h => h.elim

/-! ## Level terms -/

/-- **Level terms** over countable leaves: `lf c` (value `c[τ]`), `om b` (value `Ω₁·ω^{b[τ]}`), `ad x y`. -/
inductive UkL : Type 1
  | lf : UhT → UkL
  | om : UkL → UkL
  | ad : UkL → UkL → UkL

namespace UkL

/-- Evaluation over the base `τ`. -/
noncomputable def ev (τ : Ordinal.{0}) : UkL → Ordinal.{0}
  | lf c => UhT.ev τ c
  | om b => Om1 * ω ^ ev τ b
  | ad x y => ev τ x + ev τ y

/-- Apply `f` to every parameter of the leaves. -/
def map (f : Ordinal.{0} → Ordinal.{0}) : UkL → UkL
  | lf c => lf (c.map f)
  | om b => om (map f b)
  | ad x y => ad (map f x) (map f y)

/-- The translation of the leaves (`Uh.UhT.tr`); `ϑ₁`-nodes and sums are kept ([W07a] Def 6.2, clauses two and
three). -/
def tr (a : Ordinal.{0}) : UkL → UkL
  | lf c => lf (UhT.tr a c)
  | om b => om (tr a b)
  | ad x y => ad (tr a x) (tr a y)

/-- Every leaf satisfies `P`. -/
def Lf (P : UhT → Prop) : UkL → Prop
  | lf c => P c
  | om b => Lf P b
  | ad x y => Lf P x ∧ Lf P y

/-- **The shape of a level `Γ`**: only `om`- and `ad`-nodes at the top (so `Ω₁ ∣ Γ`). -/
def Gs : UkL → Prop
  | lf _ => False
  | om _ => True
  | ad x y => Gs x ∧ Gs y

/-- An `om`-node. -/
def IsOm : UkL → Prop
  | om _ => True
  | _ => False

/-- **No absorption of the head** over `τ`: along the head chain every sum `ad x y` has `x = om b` and
`y[τ] < x[τ]·ω`. -/
def HbS (τ : Ordinal.{0}) : UkL → Prop
  | lf _ => True
  | om b => HbS τ b
  | ad x y => HbS τ x ∧ IsOm x ∧ ev τ y < ev τ x * ω

/-- **The head leaf is high** over `τ` (`HiC`). -/
def Hd (τ : Ordinal.{0}) : UkL → Prop
  | lf c => HiC τ c
  | om b => Hd τ b
  | ad x _ => Hd τ x

theorem Lf_mono {P Q : UhT → Prop} (hPQ : ∀ c, P c → Q c) : ∀ G : UkL, Lf P G → Lf Q G
  | lf c, h => hPQ c h
  | om b, h => Lf_mono hPQ b h
  | ad x y, h => ⟨Lf_mono hPQ x h.1, Lf_mono hPQ y h.2⟩

theorem Lf_and {P Q : UhT → Prop} : ∀ G : UkL, Lf P G → Lf Q G → Lf (fun c => P c ∧ Q c) G
  | lf _, h1, h2 => ⟨h1, h2⟩
  | om b, h1, h2 => Lf_and b h1 h2
  | ad x y, h1, h2 => ⟨Lf_and x h1.1 h2.1, Lf_and y h1.2 h2.2⟩

theorem Lf_map {P : UhT → Prop} {f : Ordinal.{0} → Ordinal.{0}} :
    ∀ G : UkL, Lf P (G.map f) ↔ Lf (fun c => P (c.map f)) G
  | lf _ => Iff.rfl
  | om b => Lf_map (P := P) b
  | ad x y => and_congr (Lf_map (P := P) x) (Lf_map (P := P) y)

theorem Lf_tr {P : UhT → Prop} {a : Ordinal.{0}} :
    ∀ G : UkL, Lf P (G.tr a) ↔ Lf (fun c => P (UhT.tr a c)) G
  | lf _ => Iff.rfl
  | om b => Lf_tr (P := P) b
  | ad x y => and_congr (Lf_tr (P := P) x) (Lf_tr (P := P) y)

theorem map_map (f g : Ordinal.{0} → Ordinal.{0}) : ∀ G : UkL, (G.map g).map f = G.map (f ∘ g)
  | lf c => by simp only [map, UhT.map_map]
  | om b => by simp only [map, map_map f g b]
  | ad x y => by simp only [map, map_map f g x, map_map f g y]

theorem map_congr {f g : Ordinal.{0} → Ordinal.{0}} :
    ∀ G : UkL, Lf (UhT.Lv (fun p => f p = g p)) G → G.map f = G.map g
  | lf c, h => by simp only [map, UhT.map_congr c h]
  | om b, h => by simp only [map, map_congr b h]
  | ad x y, h => by simp only [map, map_congr x h.1, map_congr y h.2]

theorem map_id : ∀ G : UkL, G.map id = G
  | lf c => by simp only [map, UhT.map_id]
  | om b => by simp only [map, map_id b]
  | ad x y => by simp only [map, map_id x, map_id y]

theorem tr_map (a : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) : ∀ G : UkL, (G.tr a).map f = (G.map f).tr (f a)
  | lf c => by simp only [tr, map, UhT.tr_map]
  | om b => by simp only [tr, map, tr_map a f b]
  | ad x y => by simp only [tr, map, tr_map a f x, tr_map a f y]

theorem Gs_map (f : Ordinal.{0} → Ordinal.{0}) : ∀ G : UkL, Gs (G.map f) ↔ Gs G
  | lf _ => Iff.rfl
  | om _ => Iff.rfl
  | ad x y => and_congr (Gs_map f x) (Gs_map f y)

theorem Gs_tr (a : Ordinal.{0}) : ∀ G : UkL, Gs (G.tr a) ↔ Gs G
  | lf _ => Iff.rfl
  | om _ => Iff.rfl
  | ad x y => and_congr (Gs_tr a x) (Gs_tr a y)

theorem IsOm_map (f : Ordinal.{0} → Ordinal.{0}) : ∀ G : UkL, IsOm (G.map f) ↔ IsOm G
  | lf _ => Iff.rfl
  | om _ => Iff.rfl
  | ad _ _ => Iff.rfl

theorem IsOm_tr (a : Ordinal.{0}) : ∀ G : UkL, IsOm (G.tr a) ↔ IsOm G
  | lf _ => Iff.rfl
  | om _ => Iff.rfl
  | ad _ _ => Iff.rfl

/-- The head condition is carried by a parameter map sending parameters `≥ τ` to parameters `≥ σ`. -/
theorem Hd_map {τ σ : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} :
    ∀ G : UkL, Lf (UhT.Lv (fun p => τ ≤ p → σ ≤ f p)) G → Hd τ G → Hd σ (G.map f)
  | lf c, hl, h => HiC_map c hl h
  | om b, hl, h => Hd_map b hl h
  | ad x _, hl, h => Hd_map x hl.1 h

/-- The head condition over `a` gives it over every `τ ≤ a` after the translation. -/
theorem Hd_tr {τ a : Ordinal.{0}} (hτa : τ ≤ a) : ∀ G : UkL, Hd a G → Hd τ (G.tr a)
  | lf c, h => HiC_tr hτa c h
  | om b, h => Hd_tr hτa b h
  | ad x _, h => Hd_tr hτa x h

/-! ### Values -/

/-- Countable leaves give a value below `ε_{Ω₁+1}`. -/
theorem ev_lt_E {τ : Ordinal.{0}} : ∀ G : UkL, Lf (fun c => UhT.ev τ c < Om1) G → ev τ G < Gg.ggE
  | lf _, h => h.trans Rj.rj_Om1_lt_E
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
theorem ev_dvd {τ : Ordinal.{0}} : ∀ G : UkL, Gs G → ∃ M, ev τ G = Om1 * M ∧ 1 ≤ M
  | lf _, h => h.elim
  | om b, _ => ⟨ω ^ ev τ b, rfl, Order.one_le_iff_pos.2 (opow_pos _ omega0_pos)⟩
  | ad x y, h => by
    obtain ⟨M1, e1, h1⟩ := ev_dvd x h.1
    obtain ⟨M2, e2, _⟩ := ev_dvd y h.2
    exact ⟨M1 + M2, by simp only [ev]; rw [e1, e2, mul_add], h1.trans le_self_add⟩

/-- `Ω₁·ω^b·ω = Ω₁·ω^{b+1}`. -/
theorem om_mul_omega (b : Ordinal.{0}) : Om1 * ω ^ b * ω = Om1 * ω ^ (b + 1) := by
  rw [mul_assoc, opow_add, opow_one]

/-- **The data of `Ω₁·ω^b + y`** (`0 < b < ε_{Ω₁+1}`, `y < Ω₁·ω^{b+1}`): at least `rjDat b`. -/
theorem dat_om_add {b y : Ordinal.{0}} (hb0 : b ≠ 0) (hbE : b < Gg.ggE) (hy : y < Om1 * ω ^ (b + 1)) :
    Rj.rjDat b ≤ Rj.rjDat (Om1 * ω ^ b + y) := by
  obtain ⟨g, hg⟩ : ∃ g, g = Om1 + b := ⟨_, rfl⟩
  have hgE : g < Gg.ggE := hg ▸ Si.si_E_inE.add_lt Rj.rj_Om1_lt_E hbE
  have hwg : Om1 * ω ^ b = ω ^ g := by rw [hg]; exact Si.si_Om1_opow_eq b
  have hy' : y < ω ^ g * ω := by
    rw [← hwg, om_mul_omega]; exact hy
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
  have hOg : Om1 < ω ^ g := by
    rw [← Rj.rj_Om1_opow]
    exact (opow_lt_opow_iff_right one_lt_omega0).2 (hg ▸ Si.si_Om1_lt_Om1_add hb0)
  have h1 : Om1 < ω ^ g * (1 + y / ω ^ g) + y % ω ^ g :=
    lt_of_lt_of_le hOg (le_self_add.trans' (le_mul_left _ (pos_iff_ne_zero.2 hv0)))
  have hlt : ω ^ g * (1 + y / ω ^ g) + y % ω ^ g < Gg.ggE := by
    have hwE : ω ^ (g + 1) < Gg.ggE := by
      have h3 : ω ^ (Gg.ggE : Ordinal.{0}) = Gg.ggE := Si.si_E_inE
      have hg1 : g + 1 < Gg.ggE := Si.si_E_inE.add_lt hgE (Ub.ub_one_lt Si.si_E_inE)
      have := (opow_lt_opow_iff_right one_lt_omega0).2 hg1
      rwa [h3] at this
    have hle : ω ^ g * (1 + y / ω ^ g) + y % ω ^ g < ω ^ (g + 1) := by
      rw [opow_add, opow_one]
      calc ω ^ g * (1 + y / ω ^ g) + y % ω ^ g < ω ^ g * (1 + y / ω ^ g) + ω ^ g := (add_lt_add_iff_left _).2 hrem
        _ = ω ^ g * (1 + y / ω ^ g + 1) := by rw [mul_add_one]
        _ ≤ ω ^ g * ω := mul_le_mul_right (Order.add_one_le_of_lt hvω) _
    exact hle.trans hwE
  rw [hsum, Si.si_rjDat_form hv0 hvω hrem h1 hlt]
  refine le_trans ?_ (le_max_left _ _)
  rcases lt_or_ge b Om1 with hb1 | hb1
  · rw [hg, Rj.rjDat_Om1_add hb0 hb1, Rj.rjDat_small hb1]
  · rw [hg, Si.si_rjDat_Om1_add hb1 hbE]

/-- **The decision `Γ^{*τ} ≥ τ` from the head** ([W07a] Def 3.28 through `R2.ukVt_tr3`'s step ◇*): countable
leaves, no absorption of the head and a high head leaf give `τ ≤ rjDat Γ` (`Γ = G[τ]`). -/
theorem dat {τ : Ordinal.{0}} (hτ0 : 0 < τ) :
    ∀ G : UkL, Lf (fun c => UhT.ev τ c < Om1) G → HbS τ G → Hd τ G → τ ≤ Rj.rjDat (ev τ G) ∧ ev τ G ≠ 0
  | lf c, hw, _, hd => by
    have h1 : τ ≤ UhT.ev τ c := HiC_le c hd
    have hc1 : UhT.ev τ c < Om1 := hw
    simp only [ev]
    rw [Rj.rjDat_small hc1]
    exact ⟨h1, (hτ0.trans_le h1).ne'⟩
  | om b, hw, hb, hd => by
    obtain ⟨h1, h2⟩ := dat hτ0 b hw hb hd
    have hbE := ev_lt_E b hw
    have := dat_om_add (y := 0) h2 hbE (mul_pos Rj.rj_Om1_pos (opow_pos _ omega0_pos))
    rw [add_zero] at this
    simp only [ev]
    exact ⟨h1.trans this, (mul_pos Rj.rj_Om1_pos (opow_pos _ omega0_pos)).ne'⟩
  | ad (om b) y, hw, hb, hd => by
    obtain ⟨h1, h2⟩ := dat hτ0 b hw.1 hb.1 hd
    have hbE := ev_lt_E b hw.1
    have hy : ev τ y < Om1 * ω ^ (ev τ b + 1) := by rw [← om_mul_omega]; exact hb.2.2
    have := dat_om_add h2 hbE hy
    simp only [ev]
    exact ⟨h1.trans this,
      (lt_of_lt_of_le (mul_pos Rj.rj_Om1_pos (opow_pos _ omega0_pos)) le_self_add).ne'⟩
  | ad (lf _) _, _, hb, _ => hb.2.1.elim
  | ad (ad _ _) _, _, hb, _ => hb.2.1.elim

/-- `Ω₁·ω^{b+1} ∈ Tᵗ[σ]` and `π(Ω₁·ω^{b+1}) = Ω₁·ω^{π b + 1}` (`R2.siOm1_opow_TB`, `R2.pi_add`, `R2.pi_lt`). -/
theorem om_succ_TB {σ τ b : Ordinal.{0}} (h : Bases σ τ) (hb : b ∈ TB τ σ) (hbE : b < Gg.ggE) :
    Om1 * ω ^ (b + 1) ∈ TB τ σ ∧ pi σ τ (Om1 * ω ^ (b + 1)) = Om1 * ω ^ (pi σ τ b + 1) := by
  have hσ1 : (1 : Ordinal.{0}) < σ := Ub.ub_one_lt h.1
  have h1T : (1 : Ordinal.{0}) ∈ TB τ σ := (TB_inter_lt h (hσ1.trans h.2.2.1)).2 hσ1
  obtain ⟨c1, c2⟩ := pi_add h hb h1T
  have hb1E : b + 1 < Gg.ggE := Si.si_E_inE.add_lt hbE (Ub.ub_one_lt Si.si_E_inE)
  obtain ⟨o1, o2⟩ := siOm1_opow_TB h hb1E
  refine ⟨o1.2 c1, ?_⟩
  rw [o2 c1, c2, pi_lt h hσ1]

/-- **`π` on level terms** ([W07a] Def 5.1, Lemma 5.3 through `Uh.uhDown`, `R2.siOm1_opow_TB`, `R2.pi_add`). -/
theorem evDown {κ σ τ : Ordinal.{0}} (h : Bases σ τ) (hκσ : κ ≤ σ) :
    ∀ G : UkL, Lf (fun c => UhT.WF τ c ∧ UhT.ev τ c < Om1) G → Lf (UhT.Lv (· ∈ TB τ σ)) G →
      Lf (UhT.Qs κ) G → ev τ G ∈ TB τ σ ∧ pi σ τ (ev τ G) = ev σ (G.map (pi σ τ)) ∧
        Lf (fun c => UhT.WF σ c ∧ UhT.ev σ c < Om1) (G.map (pi σ τ))
  | lf c, hw, hl, hq => by
    obtain ⟨a1, a2, a3⟩ := uhDown h hκσ c hw.1 hl hq
    refine ⟨a1, a2, a3, ?_⟩
    rw [← a2]; exact down_lt_Om1 h a1 hw.2
  | om b, hw, hl, hq => by
    obtain ⟨a1, a2, a3⟩ := evDown h hκσ b hw hl hq
    have hbE := ev_lt_E b (Lf_mono (fun _ hc => hc.2) b hw)
    obtain ⟨o1, o2⟩ := siOm1_opow_TB h hbE
    refine ⟨o1.2 a1, ?_, a3⟩
    simp only [ev, map]; rw [o2 a1, a2]
  | ad x y, hw, hl, hq => by
    obtain ⟨a1, a2, a3⟩ := evDown h hκσ x hw.1 hl.1 hq.1
    obtain ⟨b1, b2, b3⟩ := evDown h hκσ y hw.2 hl.2 hq.2
    obtain ⟨c1, c2⟩ := pi_add h a1 b1
    refine ⟨c1, ?_, a3, b3⟩
    simp only [ev, map]; rw [c2, a2, b2]

/-- **`π⁻¹` on level terms**. -/
theorem evUp {κ σ τ : Ordinal.{0}} (h : Bases σ τ) (hκσ : κ ≤ σ) :
    ∀ G : UkL, Lf (fun c => UhT.WF σ c ∧ UhT.ev σ c < Om1) G → Lf (UhT.Lv (· ∈ Tset σ)) G →
      Lf (UhT.Qs κ) G → ev τ (G.map (up σ τ)) ∈ TB τ σ ∧ pi σ τ (ev τ (G.map (up σ τ))) = ev σ G ∧
        Lf (fun c => UhT.WF τ c ∧ UhT.ev τ c < Om1) (G.map (up σ τ))
  | lf c, hw, hl, hq => by
    obtain ⟨a1, a2, a3⟩ := uhUp h hκσ c hw.1 hl hq
    refine ⟨a1, a2, a3, ?_⟩
    by_contra hge
    have hOm := pi_Om1 h
    have := ((pi_bijOn h).2.le_iff_le hOm.1 a1).2 (not_lt.1 hge)
    rw [hOm.2, a2] at this
    exact absurd hw.2 (not_lt.2 this)
  | om b, hw, hl, hq => by
    obtain ⟨a1, a2, a3⟩ := evUp h hκσ b hw hl hq
    have hbE := ev_lt_E _ (Lf_mono (fun _ hc => hc.2) _ a3)
    obtain ⟨o1, o2⟩ := siOm1_opow_TB h hbE
    refine ⟨o1.2 a1, ?_, a3⟩
    simp only [ev, map] at o2 ⊢; rw [o2 a1, a2]
  | ad x y, hw, hl, hq => by
    obtain ⟨a1, a2, a3⟩ := evUp h hκσ x hw.1 hl.1 hq.1
    obtain ⟨b1, b2, b3⟩ := evUp h hκσ y hw.2 hl.2 hq.2
    obtain ⟨c1, c2⟩ := pi_add h a1 b1
    refine ⟨c1, ?_, a3, b3⟩
    simp only [ev, map] at c2 ⊢; rw [c2, a2, b2]

/-- **The translation `t^α_τ` on level terms** (`Uh.uhTrA` at the leaves). -/
theorem evTrA {κ τ : Ordinal.{0}} (hB : Bases κ τ) {n : ℕ} (hn : 1 ≤ n) :
    ∀ G : UkL, Lf (UhT.Qs κ) G → Lf (UhT.Lv (· ∈ Tset (Dl τ n))) G →
      Lf (fun c => UhT.WF (Dl τ n) c ∧ UhT.ev (Dl τ n) c < Om1) G → Lf (UhT.Nd (Dl τ n) (· < Dp τ n)) G →
      Lf (fun c => UhT.WF τ c ∧ UhT.ev τ c < Om1) (G.tr (Dl τ n)) ∧ ev τ (G.tr (Dl τ n)) = ev (Dl τ n) G ∧
        Lf (fun c => UhT.ev τ (UhT.tr (Dl τ n) c) = UhT.ev (Dl τ n) c) G
  | lf c, hq, hl, hw, hd => by
    obtain ⟨w, e⟩ := uhTrA hB hn c hq hl hw.1 hd
    exact ⟨⟨w, e ▸ hw.2⟩, e, e⟩
  | om b, hq, hl, hw, hd => by
    obtain ⟨a1, a2, a3⟩ := evTrA hB hn b hq hl hw hd
    refine ⟨a1, ?_, a3⟩
    simp only [tr, ev]; rw [a2]
  | ad x y, hq, hl, hw, hd => by
    obtain ⟨a1, a2, a3⟩ := evTrA hB hn x hq.1 hl.1 hw.1 hd.1
    obtain ⟨b1, b2, b3⟩ := evTrA hB hn y hq.2 hl.2 hw.2 hd.2
    refine ⟨⟨a1, b1⟩, ?_, a3, b3⟩
    simp only [tr, ev]; rw [a2, b2]

/-- **The translation `t^τ_α` on level terms** (`Uh.uhTrB` at the leaves). -/
theorem evTrB {κ τ : Ordinal.{0}} (hB : Bases κ τ) {n : ℕ} (hn : 1 ≤ n) :
    ∀ G : UkL, Lf (UhT.Qs κ) G → Lf (UhT.Lv (· ∈ Tset τ)) (G.tr (Dl τ n)) →
      Lf (fun c => UhT.WF τ c ∧ UhT.ev τ c < Om1) (G.tr (Dl τ n)) → Lf (UhT.Nd τ (· < Dp τ n)) (G.tr (Dl τ n)) →
      Lf (fun c => UhT.WF (Dl τ n) c ∧ UhT.ev (Dl τ n) c < Om1) G ∧ ev τ (G.tr (Dl τ n)) = ev (Dl τ n) G ∧
        Lf (fun c => UhT.ev τ (UhT.tr (Dl τ n) c) = UhT.ev (Dl τ n) c) G
  | lf c, hq, hl, hw, hd => by
    obtain ⟨w, e⟩ := uhTrB hB hn c hq hl hw.1 hd
    have h2 : UhT.ev τ (UhT.tr (Dl τ n) c) < Om1 := hw.2
    exact ⟨⟨w, e ▸ h2⟩, e, e⟩
  | om b, hq, hl, hw, hd => by
    obtain ⟨a1, a2, a3⟩ := evTrB hB hn b hq hl hw hd
    refine ⟨a1, ?_, a3⟩
    simp only [tr, ev]; rw [a2]
  | ad x y, hq, hl, hw, hd => by
    obtain ⟨a1, a2, a3⟩ := evTrB hB hn x hq.1 hl.1 hw.1 hd.1
    obtain ⟨b1, b2, b3⟩ := evTrB hB hn y hq.2 hl.2 hw.2 hd.2
    refine ⟨⟨a1, b1⟩, ?_, a3, b3⟩
    simp only [tr, ev]; rw [a2, b2]

/-- No absorption of the head is kept by `π`. -/
theorem HbS_down {κ σ τ : Ordinal.{0}} (h : Bases σ τ) (hκσ : κ ≤ σ) :
    ∀ G : UkL, Lf (fun c => UhT.WF τ c ∧ UhT.ev τ c < Om1) G → Lf (UhT.Lv (· ∈ TB τ σ)) G →
      Lf (UhT.Qs κ) G → HbS τ G → HbS σ (G.map (pi σ τ))
  | lf _, _, _, _, _ => trivial
  | om b, hw, hl, hq, hb => HbS_down h hκσ b hw hl hq hb
  | ad (om b) y, hw, hl, hq, hb => by
    obtain ⟨a1, a2, -⟩ := evDown h hκσ b hw.1 hl.1 hq.1
    obtain ⟨b1, b2, -⟩ := evDown h hκσ y hw.2 hl.2 hq.2
    have hbE := ev_lt_E b (Lf_mono (fun _ hc => hc.2) b hw.1)
    obtain ⟨s1, s2⟩ := om_succ_TB h a1 hbE
    refine ⟨HbS_down h hκσ b hw.1 hl.1 hq.1 hb.1, trivial, ?_⟩
    show ev σ (y.map (pi σ τ)) < Om1 * ω ^ ev σ (b.map (pi σ τ)) * ω
    have hy : ev τ y < Om1 * ω ^ (ev τ b + 1) := by rw [← om_mul_omega]; exact hb.2.2
    rw [om_mul_omega, ← a2, ← s2, ← b2]
    exact (pi_bijOn h).2 b1 s1 hy
  | ad (lf _) _, _, _, _, hb => hb.2.1.elim
  | ad (ad _ _) _, _, _, _, hb => hb.2.1.elim

/-- No absorption of the head is kept by `π⁻¹`. -/
theorem HbS_up {κ σ τ : Ordinal.{0}} (h : Bases σ τ) (hκσ : κ ≤ σ) :
    ∀ G : UkL, Lf (fun c => UhT.WF σ c ∧ UhT.ev σ c < Om1) G → Lf (UhT.Lv (· ∈ Tset σ)) G →
      Lf (UhT.Qs κ) G → HbS σ G → HbS τ (G.map (up σ τ))
  | lf _, _, _, _, _ => trivial
  | om b, hw, hl, hq, hb => HbS_up h hκσ b hw hl hq hb
  | ad (om b) y, hw, hl, hq, hb => by
    obtain ⟨a1, a2, a3⟩ := evUp h hκσ b hw.1 hl.1 hq.1
    obtain ⟨b1, b2, -⟩ := evUp h hκσ y hw.2 hl.2 hq.2
    have hbE := ev_lt_E _ (Lf_mono (fun _ hc => hc.2) _ a3)
    obtain ⟨s1, s2⟩ := om_succ_TB h a1 hbE
    refine ⟨HbS_up h hκσ b hw.1 hl.1 hq.1 hb.1, trivial, ?_⟩
    show ev τ (y.map (up σ τ)) < Om1 * ω ^ ev τ (b.map (up σ τ)) * ω
    have hy : ev σ y < Om1 * ω ^ (ev σ b + 1) := by rw [← om_mul_omega]; exact hb.2.2
    rw [← b2, ← a2, ← s2] at hy
    rw [om_mul_omega]
    by_contra hge
    have := ((pi_bijOn h).2.le_iff_le s1 b1).2 (not_lt.1 hge)
    exact absurd hy (not_lt.2 this)
  | ad (lf _) _, _, _, _, hb => hb.2.1.elim
  | ad (ad _ _) _, _, _, _, hb => hb.2.1.elim

/-- No absorption of the head is kept by `t^α_τ`. -/
theorem HbS_trA {κ τ : Ordinal.{0}} (hB : Bases κ τ) {n : ℕ} (hn : 1 ≤ n) :
    ∀ G : UkL, Lf (UhT.Qs κ) G → Lf (UhT.Lv (· ∈ Tset (Dl τ n))) G →
      Lf (fun c => UhT.WF (Dl τ n) c ∧ UhT.ev (Dl τ n) c < Om1) G → Lf (UhT.Nd (Dl τ n) (· < Dp τ n)) G →
      HbS (Dl τ n) G → HbS τ (G.tr (Dl τ n))
  | lf _, _, _, _, _, _ => trivial
  | om b, hq, hl, hw, hd, hb => HbS_trA hB hn b hq hl hw hd hb
  | ad x y, hq, hl, hw, hd, hb => by
    refine ⟨HbS_trA hB hn x hq.1 hl.1 hw.1 hd.1 hb.1, (IsOm_tr _ x).2 hb.2.1, ?_⟩
    rw [(evTrA hB hn x hq.1 hl.1 hw.1 hd.1).2.1, (evTrA hB hn y hq.2 hl.2 hw.2 hd.2).2.1]
    exact hb.2.2

/-- No absorption of the head is reflected by `t^τ_α`. -/
theorem HbS_trB {κ τ : Ordinal.{0}} (hB : Bases κ τ) {n : ℕ} (hn : 1 ≤ n) :
    ∀ G : UkL, Lf (UhT.Qs κ) G → Lf (UhT.Lv (· ∈ Tset τ)) (G.tr (Dl τ n)) →
      Lf (fun c => UhT.WF τ c ∧ UhT.ev τ c < Om1) (G.tr (Dl τ n)) → Lf (UhT.Nd τ (· < Dp τ n)) (G.tr (Dl τ n)) →
      HbS τ (G.tr (Dl τ n)) → HbS (Dl τ n) G
  | lf _, _, _, _, _, _ => trivial
  | om b, hq, hl, hw, hd, hb => HbS_trB hB hn b hq hl hw hd hb
  | ad x y, hq, hl, hw, hd, hb => by
    refine ⟨HbS_trB hB hn x hq.1 hl.1 hw.1 hd.1 hb.1, (IsOm_tr _ x).1 hb.2.1, ?_⟩
    have h3 := hb.2.2
    rw [(evTrB hB hn x hq.1 hl.1 hw.1 hd.1).2.1, (evTrB hB hn y hq.2 hl.2 hw.2 hd.2).2.1] at h3
    exact h3

/-- Leaf bounds are kept by `π`. -/
theorem bd_down {κ σ τ V : Ordinal.{0}} (h : Bases σ τ) (hκσ : κ ≤ σ) (hV : V ∈ TB τ σ) :
    ∀ G : UkL, Lf (fun c => UhT.WF τ c ∧ UhT.ev τ c < Om1) G → Lf (UhT.Lv (· ∈ TB τ σ)) G →
      Lf (UhT.Qs κ) G → Lf (fun c => UhT.ev τ c < V) G →
        Lf (fun c => UhT.ev σ c < pi σ τ V) (G.map (pi σ τ))
  | lf c, hw, hl, hq, hb => by
    obtain ⟨a1, a2, -⟩ := uhDown h hκσ c hw.1 hl hq
    show UhT.ev σ (c.map (pi σ τ)) < pi σ τ V
    rw [← a2]; exact (pi_bijOn h).2 a1 hV hb
  | om b, hw, hl, hq, hb => bd_down h hκσ hV b hw hl hq hb
  | ad x y, hw, hl, hq, hb =>
    ⟨bd_down h hκσ hV x hw.1 hl.1 hq.1 hb.1, bd_down h hκσ hV y hw.2 hl.2 hq.2 hb.2⟩

/-- Leaf bounds are reflected by `π⁻¹`. -/
theorem bd_up {κ σ τ V : Ordinal.{0}} (h : Bases σ τ) (hκσ : κ ≤ σ) (hV : V ∈ TB τ σ) :
    ∀ G : UkL, Lf (fun c => UhT.WF σ c ∧ UhT.ev σ c < Om1) G → Lf (UhT.Lv (· ∈ Tset σ)) G →
      Lf (UhT.Qs κ) G → Lf (fun c => UhT.ev σ c < pi σ τ V) G →
        Lf (fun c => UhT.ev τ c < V) (G.map (up σ τ))
  | lf c, hw, hl, hq, hb => by
    obtain ⟨a1, a2, -⟩ := uhUp h hκσ c hw.1 hl hq
    show UhT.ev τ (c.map (up σ τ)) < V
    have hb' : UhT.ev σ c < pi σ τ V := hb
    rw [← a2] at hb'
    by_contra hge
    have := ((pi_bijOn h).2.le_iff_le hV a1).2 (not_lt.1 hge)
    exact absurd hb' (not_lt.2 this)
  | om b, hw, hl, hq, hb => bd_up h hκσ hV b hw hl hq hb
  | ad x y, hw, hl, hq, hb =>
    ⟨bd_up h hκσ hV x hw.1 hl.1 hq.1 hb.1, bd_up h hκσ hV y hw.2 hl.2 hq.2 hb.2⟩

/-- Leaf bounds through the translation (values of the leaves are kept). -/
theorem bd_tr {τ a V : Ordinal.{0}} :
    ∀ G : UkL, Lf (fun c => UhT.ev τ (UhT.tr a c) = UhT.ev a c) G →
      (Lf (fun c => UhT.ev τ c < V) (G.tr a) ↔ Lf (fun c => UhT.ev a c < V) G)
  | lf c, he => by
    show UhT.ev τ (UhT.tr a c) < V ↔ UhT.ev a c < V
    have he' : UhT.ev τ (UhT.tr a c) = UhT.ev a c := he
    rw [he']
  | om b, he => bd_tr b he
  | ad x y, he => and_congr (bd_tr x he.1) (bd_tr y he.2)

end UkL

/-! ## Terms -/

/-- **The node conditions of `thg G r` over `τ`** (`ρ = r[τ]`, `Γ = G[τ]`): `ρ < Ω₁`, countable leaves (with the
argument bounds of `Uh.UhT`), the shape `Gs`, no absorption of the head, a high head leaf, `Γ + ρ ∈ Tᵗ`, and every
leaf and `ρ` below the value `ϑᵗ(Γ + ρ)`. -/
structure Ng (τ : Ordinal.{0}) (G : UkL) (ρ : Ordinal.{0}) : Prop where
  r1 : ρ < Om1
  wl : UkL.Lf (fun c => UhT.WF τ c ∧ UhT.ev τ c < Om1) G
  gs : UkL.Gs G
  hb : UkL.HbS τ G
  hd : UkL.Hd τ G
  mem : UkL.ev τ G + ρ ∈ Tset τ
  bd : UkL.Lf (fun c => UhT.ev τ c < vt τ (UkL.ev τ G + ρ)) G
  rb : ρ < vt τ (UkL.ev τ G + ρ)

/-- Terms over a base: parameters, `+`, `ϑᵗ(0)`, `ϑᵗ(1 + ξ)`, `ϑᵗ(Ω₁·q + ρ)` at a constant level `q` (as in
`Uh.UhT`), and `ϑᵗ(Γ + ρ)` at a **level term** `Γ`. -/
inductive UkT : Type 1
  | par : Ordinal.{0} → UkT
  | add : UkT → UkT → UkT
  | base : UkT
  | th1 : UkT → UkT
  | thc : Ordinal.{0} → UkT → UkT
  | thg : UkL → UkT → UkT

namespace UkT

instance : Inhabited UkT := ⟨UkT.base⟩

/-- Evaluation over the base `τ`. -/
noncomputable def ev (τ : Ordinal.{0}) : UkT → Ordinal.{0}
  | par p => p
  | add s t => ev τ s + ev τ t
  | base => τ
  | th1 s => vt τ (1 + ev τ s)
  | thc q r => vt τ (Om1 * q + ev τ r)
  | thg G r => vt τ (UkL.ev τ G + ev τ r)

/-- Apply `f` to every parameter (also inside the level terms; the constant levels `q` are kept). -/
def map (f : Ordinal.{0} → Ordinal.{0}) : UkT → UkT
  | par p => par (f p)
  | add s t => add (map f s) (map f t)
  | base => base
  | th1 s => th1 (map f s)
  | thc q r => thc q (map f r)
  | thg G r => thg (G.map f) (map f r)

/-- Every parameter satisfies `P`. -/
def Lv (P : Ordinal.{0} → Prop) : UkT → Prop
  | par p => P p
  | add s t => Lv P s ∧ Lv P t
  | base => True
  | th1 s => Lv P s
  | thc _ r => Lv P r
  | thg G r => UkL.Lf (UhT.Lv P) G ∧ Lv P r

/-- The constant levels are levels over `κ` (`Uh.UhLev`), also inside the leaves of the level terms. -/
def Qs (κ : Ordinal.{0}) : UkT → Prop
  | par _ => True
  | add s t => Qs κ s ∧ Qs κ t
  | base => True
  | th1 s => Qs κ s
  | thc q r => UhLev κ q ∧ Qs κ r
  | thg G r => UkL.Lf (UhT.Qs κ) G ∧ Qs κ r

/-- The argument bounds over `τ`, and the node conditions `Ng` of the `thg`-nodes. -/
def WF (τ : Ordinal.{0}) : UkT → Prop
  | par _ => True
  | add s t => WF τ s ∧ WF τ t
  | base => True
  | th1 s => WF τ s ∧ ev τ s < Om1
  | thc _ r => WF τ r ∧ ev τ r < Om1
  | thg G r => WF τ r ∧ Ng τ G (ev τ r)

/-- Every node value over `τ` (also inside the level terms) satisfies `P`. -/
def Nd (τ : Ordinal.{0}) (P : Ordinal.{0} → Prop) : UkT → Prop
  | par _ => True
  | add s t => Nd τ P s ∧ Nd τ P t
  | base => True
  | th1 s => Nd τ P s
  | thc q r => P (vt τ (Om1 * q + ev τ r)) ∧ Nd τ P r
  | thg G r => P (vt τ (UkL.ev τ G + ev τ r)) ∧ UkL.Lf (UhT.Nd τ P) G ∧ Nd τ P r

/-- **The translation `t^a_b` of [W07a] Def 6.2**: `ϑ^a(0) ↦ a`, `ϑ^a(1 + ξ) ↦ ϑ^b(1 + a + ξ)`,
`ϑ^a(Ω₁·q + ρ) ↦ ϑ^b(Ω₁·q + a + ρ)` (the subcase `Γ^* < α`), `ϑ^a(Γ + ρ) ↦ ϑ^b(Γ + ρ)` (the subcase `Γ^* ≥ α`,
leaves translated). -/
def tr (a : Ordinal.{0}) : UkT → UkT
  | par p => par p
  | add s t => add (tr a s) (tr a t)
  | base => par a
  | th1 s => th1 (add (par a) (tr a s))
  | thc q r => thc q (add (par a) (tr a r))
  | thg G r => thg (G.tr a) (tr a r)

/-- The head condition `UkL.Hd τ` at every `thg`-node. -/
def HdA (τ : Ordinal.{0}) : UkT → Prop
  | par _ => True
  | add s t => HdA τ s ∧ HdA τ t
  | base => True
  | th1 s => HdA τ s
  | thc _ r => HdA τ r
  | thg G r => UkL.Hd τ G ∧ HdA τ r

theorem Lv_mono {P Q : Ordinal.{0} → Prop} (hPQ : ∀ p, P p → Q p) : ∀ t : UkT, Lv P t → Lv Q t
  | par p, h => hPQ p h
  | add s t, h => ⟨Lv_mono hPQ s h.1, Lv_mono hPQ t h.2⟩
  | base, _ => trivial
  | th1 s, h => Lv_mono hPQ s h
  | thc _ r, h => Lv_mono hPQ r h
  | thg G r, h => ⟨UkL.Lf_mono (fun c hc => UhT.Lv_mono hPQ c hc) G h.1, Lv_mono hPQ r h.2⟩

theorem Nd_mono {τ : Ordinal.{0}} {P Q : Ordinal.{0} → Prop} (hPQ : ∀ p, P p → Q p) :
    ∀ t : UkT, Nd τ P t → Nd τ Q t
  | par _, _ => trivial
  | add s t, h => ⟨Nd_mono hPQ s h.1, Nd_mono hPQ t h.2⟩
  | base, _ => trivial
  | th1 s, h => Nd_mono hPQ s h
  | thc _ r, h => ⟨hPQ _ h.1, Nd_mono hPQ r h.2⟩
  | thg G r, h => ⟨hPQ _ h.1, UkL.Lf_mono (fun c hc => UhT.Nd_mono hPQ c hc) G h.2.1, Nd_mono hPQ r h.2.2⟩

theorem map_map (f g : Ordinal.{0} → Ordinal.{0}) : ∀ t : UkT, (t.map g).map f = t.map (f ∘ g)
  | par _ => rfl
  | add s t => by simp only [map, map_map f g s, map_map f g t]
  | base => rfl
  | th1 s => by simp only [map, map_map f g s]
  | thc _ r => by simp only [map, map_map f g r]
  | thg G r => by simp only [map, UkL.map_map, map_map f g r]

theorem map_congr {f g : Ordinal.{0} → Ordinal.{0}} : ∀ t : UkT, Lv (fun p => f p = g p) t → t.map f = t.map g
  | par _, h => by simp only [map]; rw [show _ = _ from h]
  | add s t, h => by simp only [map, map_congr s h.1, map_congr t h.2]
  | base, _ => rfl
  | th1 s, h => by simp only [map, map_congr s h]
  | thc _ r, h => by simp only [map, map_congr r h]
  | thg G r, h => by simp only [map, UkL.map_congr G h.1, map_congr r h.2]

theorem map_id : ∀ t : UkT, t.map id = t
  | par _ => rfl
  | add s t => by simp only [map, map_id s, map_id t]
  | base => rfl
  | th1 s => by simp only [map, map_id s]
  | thc _ r => by simp only [map, map_id r]
  | thg G r => by simp only [map, UkL.map_id, map_id r]

theorem Lv_and {P Q : Ordinal.{0} → Prop} : ∀ (t : UkT), Lv P t → Lv Q t → Lv (fun p => P p ∧ Q p) t
  | par _, h1, h2 => ⟨h1, h2⟩
  | add s t, h1, h2 => ⟨Lv_and s h1.1 h2.1, Lv_and t h1.2 h2.2⟩
  | base, _, _ => trivial
  | th1 s, h1, h2 => Lv_and s h1 h2
  | thc _ r, h1, h2 => Lv_and r h1 h2
  | thg G r, h1, h2 =>
    ⟨UkL.Lf_mono (fun c hc => UhT.Lv_and c hc.1 hc.2) G (UkL.Lf_and G h1.1 h2.1), Lv_and r h1.2 h2.2⟩

theorem Lv_map {P : Ordinal.{0} → Prop} {f : Ordinal.{0} → Ordinal.{0}} :
    ∀ t : UkT, Lv (fun p => P (f p)) t → Lv P (t.map f)
  | par _, h => h
  | add s t, h => ⟨Lv_map s h.1, Lv_map t h.2⟩
  | base, _ => trivial
  | th1 s, h => Lv_map s h
  | thc _ r, h => Lv_map r h
  | thg G r, h => ⟨(UkL.Lf_map G).2 (UkL.Lf_mono (fun c hc => UhT.Lv_map c hc) G h.1), Lv_map r h.2⟩

theorem Qs_map {κ : Ordinal.{0}} (f : Ordinal.{0} → Ordinal.{0}) : ∀ t : UkT, Qs κ t → Qs κ (t.map f)
  | par _, _ => trivial
  | add s t, h => ⟨Qs_map f s h.1, Qs_map f t h.2⟩
  | base, _ => trivial
  | th1 s, h => Qs_map f s h
  | thc _ r, h => ⟨h.1, Qs_map f r h.2⟩
  | thg G r, h => ⟨(UkL.Lf_map G).2 (UkL.Lf_mono (fun c hc => UhT.Qs_map f c hc) G h.1), Qs_map f r h.2⟩

theorem tr_map (a : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) :
    ∀ t : UkT, (tr a t).map f = tr (f a) (t.map f)
  | par _ => rfl
  | add s t => by simp only [tr, map, tr_map a f s, tr_map a f t]
  | base => rfl
  | th1 s => by simp only [tr, map, tr_map a f s]
  | thc _ r => by simp only [tr, map, tr_map a f r]
  | thg G r => by simp only [tr, map, UkL.tr_map, tr_map a f r]

theorem Qs_tr {κ : Ordinal.{0}} (a : Ordinal.{0}) : ∀ t : UkT, Qs κ t → Qs κ (tr a t)
  | par _, _ => trivial
  | add s t, h => ⟨Qs_tr a s h.1, Qs_tr a t h.2⟩
  | base, _ => trivial
  | th1 s, h => ⟨trivial, Qs_tr a s h⟩
  | thc _ r, h => ⟨h.1, trivial, Qs_tr a r h.2⟩
  | thg G r, h => ⟨(UkL.Lf_tr G).2 (UkL.Lf_mono (fun c hc => UhT.Qs_tr a c hc) G h.1), Qs_tr a r h.2⟩

theorem Lv_tr {P : Ordinal.{0} → Prop} {a : Ordinal.{0}} (ha : P a) : ∀ t : UkT, Lv P t → Lv P (tr a t)
  | par _, h => h
  | add s t, h => ⟨Lv_tr ha s h.1, Lv_tr ha t h.2⟩
  | base, _ => ha
  | th1 s, h => ⟨ha, Lv_tr ha s h⟩
  | thc _ r, h => ⟨ha, Lv_tr ha r h⟩
  | thg G r, h => ⟨(UkL.Lf_tr G).2 (UkL.Lf_mono (fun c hc => UhT.Lv_tr ha c hc) G h.1), Lv_tr ha r h.2⟩

/-- The head conditions are carried by a parameter map sending parameters `≥ τ` to parameters `≥ σ`. -/
theorem HdA_map {τ σ : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} :
    ∀ t : UkT, Lv (fun p => τ ≤ p → σ ≤ f p) t → HdA τ t → HdA σ (t.map f)
  | par _, _, _ => trivial
  | add s t, hl, h => ⟨HdA_map s hl.1 h.1, HdA_map t hl.2 h.2⟩
  | base, _, _ => trivial
  | th1 s, hl, h => HdA_map s hl h
  | thc _ r, hl, h => HdA_map r hl h
  | thg G r, hl, h => ⟨UkL.Hd_map G hl.1 h.1, HdA_map r hl.2 h.2⟩

theorem WF_HdA {τ : Ordinal.{0}} : ∀ t : UkT, WF τ t → HdA τ t
  | par _, _ => trivial
  | add s t, h => ⟨WF_HdA s h.1, WF_HdA t h.2⟩
  | base, _ => trivial
  | th1 s, h => WF_HdA s h.1
  | thc _ r, h => WF_HdA r h.1
  | thg _ r, h => ⟨h.2.hd, WF_HdA r h.1⟩

end UkT

open UkT

/-! ## Membership, order, base change, segment moves -/

theorem arg_lt2 {Γ ρ : Ordinal.{0}} (hΓ : Γ < Gg.ggE) (hρ : ρ < Om1) : Γ + ρ < OmTwo :=
  lt_of_le_of_lt (add_le_add_left hΓ.le ρ) (Ss.ss_arg_lt hρ)

/-- **Membership**: leaves in `Tᵗ`, the argument bounds and levels over `κ` give `t[τ] ∈ Tᵗ`. -/
theorem ukMem {κ τ : Ordinal.{0}} (hB : Bases κ τ) :
    ∀ t : UkT, Lv (· ∈ Tset τ) t → WF τ t → Qs κ t → ev τ t ∈ Tset τ
  | .par _, hl, _, _ => hl
  | .add s t, hl, hw, hq => vzT_add hB.2.1 hB.2.2.2 (ukMem hB s hl.1 hw.1 hq.1) (ukMem hB t hl.2 hw.2 hq.2)
  | .base, _, _, _ => uh_T_le hB.2.1 hB.2.2.2 le_rfl
  | .th1 s, hl, hw, hq => by
    have hτ1 := hB.2.2.2
    have h1 : (1 : Ordinal.{0}) ∈ Tset τ := uh_T_le hB.2.1 hτ1 (Ub.ub_one_lt hB.2.1).le
    have hO : (1 : Ordinal.{0}) < Om1 := (Ub.ub_one_lt hB.2.1).trans hτ1
    exact (vt_mem hB.2.1 hτ1 (vzT_add hB.2.1 hτ1 h1 (ukMem hB s hl hw.1 hq)) (Om1_add_lt hO hw.2)).1
  | .thc _ r, hl, hw, hq => by
    obtain ⟨h1, h2⟩ := uh_arg_T hB hq.1 (ukMem hB r hl hw.1 hq.2) hw.2
    exact (vt_memTwo hB.2.1 hB.2.2.2 h1 h2).1
  | .thg G _, _, hw, _ =>
    (vt_memTwo hB.2.1 hB.2.2.2 hw.2.mem
      (arg_lt2 (UkL.ev_lt_E G (UkL.Lf_mono (fun _ hc => hc.2) G hw.2.wl)) hw.2.r1)).1

theorem lf_le {κ τ V : Ordinal.{0}} (hB : Bases κ τ) :
    ∀ G : UkL, UkL.Lf (UhT.Lv (· ∈ Tset τ)) G → UkL.Lf (fun c => UhT.WF τ c ∧ UhT.ev τ c < Om1) G →
      UkL.Lf (UhT.Qs κ) G → UkL.Lf (fun c => UhT.ev τ c < V) G →
        UkL.Lf (UhT.Lv (· ≤ V)) G ∧ UkL.Lf (UhT.Nd τ (· ≤ V)) G
  | .lf c, hl, hw, hq, hb => by
    obtain ⟨a1, a2⟩ := uhLe hB c hl hw.1 hq
    have hb' : UhT.ev τ c < V := hb
    exact ⟨UhT.Lv_mono (fun p hp => hp.trans hb'.le) c a1, UhT.Nd_mono (fun p hp => hp.trans hb'.le) c a2⟩
  | .om b, hl, hw, hq, hb => lf_le hB b hl hw hq hb
  | .ad x y, hl, hw, hq, hb => by
    obtain ⟨a1, a2⟩ := lf_le hB x hl.1 hw.1 hq.1 hb.1
    obtain ⟨b1, b2⟩ := lf_le hB y hl.2 hw.2 hq.2 hb.2
    exact ⟨⟨a1, b1⟩, ⟨a2, b2⟩⟩

/-- **Every parameter and every node value is `≤` the value** (`Uh.uhLe` at the leaves, the bounds of `Ng`). -/
theorem ukLe {κ τ : Ordinal.{0}} (hB : Bases κ τ) :
    ∀ t : UkT, Lv (· ∈ Tset τ) t → WF τ t → Qs κ t → Lv (· ≤ ev τ t) t ∧ Nd τ (· ≤ ev τ t) t
  | .par _, _, _, _ => ⟨le_refl _, trivial⟩
  | .add s t, hl, hw, hq => by
    obtain ⟨a1, a2⟩ := ukLe hB s hl.1 hw.1 hq.1
    obtain ⟨b1, b2⟩ := ukLe hB t hl.2 hw.2 hq.2
    have hs : ev τ s ≤ ev τ (.add s t) := le_self_add
    have ht : ev τ t ≤ ev τ (.add s t) := le_add_self
    exact ⟨⟨Lv_mono (fun p hp => hp.trans hs) s a1, Lv_mono (fun p hp => hp.trans ht) t b1⟩,
      ⟨Nd_mono (fun p hp => hp.trans hs) s a2, Nd_mono (fun p hp => hp.trans ht) t b2⟩⟩
  | .base, _, _, _ => ⟨trivial, trivial⟩
  | .th1 s, hl, hw, hq => by
    obtain ⟨a1, a2⟩ := ukLe hB s hl hw.1 hq
    have hle : ev τ s ≤ ev τ (.th1 s) := by
      simp only [ev]; rw [vt_wbar hB.2.1 hB.2.2.2 hw.2]
      exact le_add_self.trans (Se.se_wbar_gt _).le
    exact ⟨Lv_mono (fun p hp => hp.trans hle) s a1, Nd_mono (fun p hp => hp.trans hle) s a2⟩
  | .thc q r, hl, hw, hq => by
    obtain ⟨a1, a2⟩ := ukLe hB r hl hw.1 hq.2
    have hrT := ukMem hB r hl hw.1 hq.2
    have hlt : ev τ r < ev τ (.thc q r) := uhLt_vt_self hB hq.1 hrT hw.2
    exact ⟨Lv_mono (fun p hp => hp.trans hlt.le) r a1, le_rfl, Nd_mono (fun p hp => hp.trans hlt.le) r a2⟩
  | .thg G r, hl, hw, hq => by
    obtain ⟨a1, a2⟩ := ukLe hB r hl.2 hw.1 hq.2
    have hlt : ev τ r < ev τ (.thg G r) := hw.2.rb
    obtain ⟨l1, l2⟩ := lf_le (V := ev τ (.thg G r)) hB G hl.1 hw.2.wl hq.1 hw.2.bd
    exact ⟨⟨l1, Lv_mono (fun p hp => hp.trans hlt.le) r a1⟩,
      ⟨le_rfl, l2, Nd_mono (fun p hp => hp.trans hlt.le) r a2⟩⟩

/-- **The base change on terms with a general parameter map** ([W07a] Def 5.1, Lemma 5.3 through `R2.pi_vt`,
`R2.pi_vt_two`, `R2.pi_add`, `Uh.uh_Om1_mul_TB`, `UkL.evDown`): `π_{σ,τ}(t[τ; p]) = t[σ; π p]`. -/
theorem ukDown {κ σ τ : Ordinal.{0}} (h : Bases σ τ) (hκσ : κ ≤ σ) :
    ∀ t : UkT, WF τ t → Lv (· ∈ TB τ σ) t → Qs κ t →
      ev τ t ∈ TB τ σ ∧ pi σ τ (ev τ t) = ev σ (t.map (pi σ τ)) ∧ WF σ (t.map (pi σ τ))
  | .par p, _, hp, _ => ⟨hp, rfl, trivial⟩
  | .add s t, hw, hl, hq => by
    obtain ⟨a1, a2, a3⟩ := ukDown h hκσ s hw.1 hl.1 hq.1
    obtain ⟨b1, b2, b3⟩ := ukDown h hκσ t hw.2 hl.2 hq.2
    obtain ⟨c1, c2⟩ := pi_add h a1 b1
    refine ⟨c1, ?_, ⟨a3, b3⟩⟩
    simp only [ev, map]; rw [c2, a2, b2]
  | .base, _, _, _ => ⟨(pi_base h).1, (pi_base h).2, trivial⟩
  | .th1 s, hw, hl, hq => by
    obtain ⟨a1, a2, a3⟩ := ukDown h hκσ s hw.1 hl hq
    have hσ1 : (1 : Ordinal.{0}) < σ := Ub.ub_one_lt h.1
    have h1T : (1 : Ordinal.{0}) ∈ TB τ σ := (TB_inter_lt h (hσ1.trans h.2.2.1)).2 hσ1
    obtain ⟨c1, c2⟩ := pi_add h h1T a1
    have hO : (1 : Ordinal.{0}) < Om1 := hσ1.trans (h.2.2.1.trans h.2.2.2)
    have hlt1 : 1 + ev τ s < Om1 := Om1_add_lt hO hw.2
    obtain ⟨d1, d2⟩ := vt_mem h.2.1 h.2.2.2 c1.1 hlt1
    refine ⟨⟨d1, by
      show ((Par τ (vt τ (1 + ev τ s)) : Set Ordinal.{0})) ⊆ Set.Iio σ; rw [d2]; exact c1.2⟩, ?_, ⟨a3, ?_⟩⟩
    · simp only [ev, map]; rw [pi_vt h c1 hlt1, c2, pi_lt h hσ1, a2]
    · rw [← a2]; exact down_lt_Om1 h a1 hw.2
  | .thc q r, hw, hl, hq => by
    obtain ⟨a1, a2, a3⟩ := ukDown h hκσ r hw.1 hl hq.2
    obtain ⟨g1, g2⟩ := uh_Om1_mul_TB h q hq.1.2.1 (hq.1.2.2.trans_le hκσ)
    obtain ⟨c1, c2⟩ := pi_add h g1 a1
    have hlt2 : Om1 * q + ev τ r < OmTwo := Rj.rj_arg_lt hq.1.2.1 hw.2
    obtain ⟨d1, -, -, -, d2⟩ := vt_memTwo h.2.1 h.2.2.2 c1.1 hlt2
    refine ⟨⟨d1, by
      show ((Par τ (vt τ (Om1 * q + ev τ r)) : Set Ordinal.{0})) ⊆ Set.Iio σ; rw [d2]; exact c1.2⟩, ?_, ⟨a3, ?_⟩⟩
    · simp only [ev, map]; rw [pi_vt_two h c1 hlt2, c2, g2, a2]
    · rw [← a2]; exact down_lt_Om1 h a1 hw.2
  | .thg G r, hw, hl, hq => by
    obtain ⟨a1, a2, a3⟩ := ukDown h hκσ r hw.1 hl.2 hq.2
    obtain ⟨g1, g2, g3⟩ := UkL.evDown h hκσ G hw.2.wl hl.1 hq.1
    obtain ⟨c1, c2⟩ := pi_add h g1 a1
    have hlt2 := arg_lt2 (UkL.ev_lt_E G (UkL.Lf_mono (fun _ hc => hc.2) G hw.2.wl)) hw.2.r1
    obtain ⟨d1, -, -, -, d2⟩ := vt_memTwo h.2.1 h.2.2.2 c1.1 hlt2
    have hVT : vt τ (UkL.ev τ G + ev τ r) ∈ TB τ σ := ⟨d1, by
      show ((Par τ (vt τ (UkL.ev τ G + ev τ r)) : Set Ordinal.{0})) ⊆ Set.Iio σ; rw [d2]; exact c1.2⟩
    have hpv : pi σ τ (vt τ (UkL.ev τ G + ev τ r)) =
        vt σ (UkL.ev σ (G.map (pi σ τ)) + ev σ (r.map (pi σ τ))) := by
      rw [pi_vt_two h c1 hlt2, c2, g2, a2]
    refine ⟨hVT, by simp only [ev, map]; exact hpv, a3, ?_⟩
    refine ⟨by rw [← a2]; exact down_lt_Om1 h a1 hw.2.r1, g3, (UkL.Gs_map _ G).2 hw.2.gs,
      UkL.HbS_down h hκσ G hw.2.wl hl.1 hq.1 hw.2.hb,
      UkL.Hd_map G (UkL.Lf_mono (fun c hc => UhT.Lv_mono (fun p hp hτp => down_ge h hp hτp) c hc) G hl.1)
        hw.2.hd,
      by rw [← g2, ← a2, ← c2]; exact (pi_bijOn h).1.mapsTo c1, ?_, ?_⟩
    · rw [← hpv]; exact UkL.bd_down h hκσ hVT G hw.2.wl hl.1 hq.1 hw.2.bd
    · rw [← hpv, ← a2]; exact (pi_bijOn h).2 a1 hVT hw.2.rb

/-- **The inverse base change on terms**: leaves in `T^σ` ⇒ the term over `τ` with leaves `π_{σ,τ}⁻¹ p` lies in
`Tᵗ[σ]`, has the argument bounds and node conditions, and is sent by `π_{σ,τ}` to `t[σ; p]`. -/
theorem ukUp {κ σ τ : Ordinal.{0}} (h : Bases σ τ) (hκσ : κ ≤ σ) :
    ∀ t : UkT, WF σ t → Lv (· ∈ Tset σ) t → Qs κ t →
      ev τ (t.map (up σ τ)) ∈ TB τ σ ∧ pi σ τ (ev τ (t.map (up σ τ))) = ev σ t ∧ WF τ (t.map (up σ τ))
  | .par p, _, hp, _ => ⟨(up_spec h hp).1, (up_spec h hp).2, trivial⟩
  | .add s t, hw, hl, hq => by
    obtain ⟨a1, a2, a3⟩ := ukUp h hκσ s hw.1 hl.1 hq.1
    obtain ⟨b1, b2, b3⟩ := ukUp h hκσ t hw.2 hl.2 hq.2
    obtain ⟨c1, c2⟩ := pi_add h a1 b1
    refine ⟨c1, ?_, ⟨a3, b3⟩⟩
    simp only [ev, map] at c2 ⊢; rw [c2, a2, b2]
  | .base, _, _, _ => ⟨(pi_base h).1, (pi_base h).2, trivial⟩
  | .th1 s, hw, hl, hq => by
    obtain ⟨a1, a2, a3⟩ := ukUp h hκσ s hw.1 hl hq
    have hσ1 : (1 : Ordinal.{0}) < σ := Ub.ub_one_lt h.1
    have h1T : (1 : Ordinal.{0}) ∈ TB τ σ := (TB_inter_lt h (hσ1.trans h.2.2.1)).2 hσ1
    have hO : (1 : Ordinal.{0}) < Om1 := hσ1.trans (h.2.2.1.trans h.2.2.2)
    have hy1 : ev τ (s.map (up σ τ)) < Om1 := by
      by_contra hge
      have hOm := pi_Om1 h
      have := ((pi_bijOn h).2.le_iff_le hOm.1 a1).2 (not_lt.1 hge)
      rw [hOm.2, a2] at this
      exact absurd hw.2 (not_lt.2 this)
    obtain ⟨c1, c2⟩ := pi_add h h1T a1
    have hlt1 : 1 + ev τ (s.map (up σ τ)) < Om1 := Om1_add_lt hO hy1
    obtain ⟨d1, d2⟩ := vt_mem h.2.1 h.2.2.2 c1.1 hlt1
    refine ⟨⟨d1, by simp only [ev, map]; rw [d2]; exact c1.2⟩, ?_, ⟨a3, hy1⟩⟩
    simp only [ev, map]; rw [pi_vt h c1 hlt1, c2, pi_lt h hσ1, a2]
  | .thc q r, hw, hl, hq => by
    obtain ⟨a1, a2, a3⟩ := ukUp h hκσ r hw.1 hl hq.2
    have hy1 : ev τ (r.map (up σ τ)) < Om1 := by
      by_contra hge
      have hOm := pi_Om1 h
      have := ((pi_bijOn h).2.le_iff_le hOm.1 a1).2 (not_lt.1 hge)
      rw [hOm.2, a2] at this
      exact absurd hw.2 (not_lt.2 this)
    obtain ⟨g1, g2⟩ := uh_Om1_mul_TB h q hq.1.2.1 (hq.1.2.2.trans_le hκσ)
    obtain ⟨c1, c2⟩ := pi_add h g1 a1
    have hlt2 : Om1 * q + ev τ (r.map (up σ τ)) < OmTwo := Rj.rj_arg_lt hq.1.2.1 hy1
    obtain ⟨d1, -, -, -, d2⟩ := vt_memTwo h.2.1 h.2.2.2 c1.1 hlt2
    refine ⟨⟨d1, by simp only [ev, map]; rw [d2]; exact c1.2⟩, ?_, ⟨a3, hy1⟩⟩
    simp only [ev, map]; rw [pi_vt_two h c1 hlt2, c2, g2, a2]
  | .thg G r, hw, hl, hq => by
    obtain ⟨a1, a2, a3⟩ := ukUp h hκσ r hw.1 hl.2 hq.2
    have hy1 : ev τ (r.map (up σ τ)) < Om1 := by
      by_contra hge
      have hOm := pi_Om1 h
      have := ((pi_bijOn h).2.le_iff_le hOm.1 a1).2 (not_lt.1 hge)
      rw [hOm.2, a2] at this
      exact absurd hw.2.r1 (not_lt.2 this)
    obtain ⟨g1, g2, g3⟩ := UkL.evUp h hκσ G hw.2.wl hl.1 hq.1
    obtain ⟨c1, c2⟩ := pi_add h g1 a1
    have hlt2 := arg_lt2 (UkL.ev_lt_E _ (UkL.Lf_mono (fun _ hc => hc.2) _ g3)) hy1
    obtain ⟨d1, -, -, -, d2⟩ := vt_memTwo h.2.1 h.2.2.2 c1.1 hlt2
    have hVT : vt τ (UkL.ev τ (G.map (up σ τ)) + ev τ (r.map (up σ τ))) ∈ TB τ σ := ⟨d1, by
      show ((Par τ (vt τ (UkL.ev τ (G.map (up σ τ)) + ev τ (r.map (up σ τ)))) : Set Ordinal.{0})) ⊆
        Set.Iio σ
      rw [d2]; exact c1.2⟩
    have hpv : pi σ τ (vt τ (UkL.ev τ (G.map (up σ τ)) + ev τ (r.map (up σ τ)))) =
        vt σ (UkL.ev σ G + ev σ r) := by
      rw [pi_vt_two h c1 hlt2, c2, g2, a2]
    refine ⟨hVT, by simp only [ev, map]; exact hpv, a3, hy1, g3, (UkL.Gs_map _ G).2 hw.2.gs,
      UkL.HbS_up h hκσ G hw.2.wl hl.1 hq.1 hw.2.hb,
      UkL.Hd_map G (UkL.Lf_mono (fun c hc => UhT.Lv_mono (fun p hp hσp => up_ge h hp hσp) c hc) G hl.1)
        hw.2.hd, c1.1, ?_, ?_⟩
    · have hb := hw.2.bd
      rw [← hpv] at hb
      exact UkL.bd_up h hκσ hVT G hw.2.wl hl.1 hq.1 hb
    · have hb := hw.2.rb
      rw [← hpv, ← a2] at hb
      by_contra hge
      have := ((pi_bijOn h).2.le_iff_le hVT a1).2 (not_lt.1 hge)
      exact absurd hb (not_lt.2 this)

/-- `π_{σ,τ}⁻¹(t[σ; p]) = t[τ; π⁻¹ p]`. -/
theorem ukUp_eq {κ σ τ : Ordinal.{0}} (h : Bases σ τ) (hκσ : κ ≤ σ) (t : UkT) (hw : WF σ t)
    (hl : Lv (· ∈ Tset σ) t) (hq : Qs κ t) :
    up σ τ (ev σ t) = ev τ (t.map (up σ τ)) ∧ WF τ (t.map (up σ τ)) := by
  obtain ⟨a1, a2, a3⟩ := ukUp h hκσ t hw hl hq
  exact ⟨by rw [← a2]; exact up_pi h a1, a3⟩

/-- **The segment move on terms**: for `ε`-numbers `b, c < Ω₁`, levels over `κ ≤ b, c` and leaves in `Tᵇ[κ]`:
`mv b c (t[b; p]) = t[c; mv b c p]`. -/
theorem ukMv {κ b c : Ordinal.{0}} (hb : InE b) (hb1 : b < Om1) (hc : InE c) (hc1 : c < Om1) (hκb : κ ≤ b)
    (hκc : κ ≤ c) (t : UkT) (hq : Qs κ t) (hw : WF b t) (hl : Lv (· ∈ TB b κ) t) :
    mv b c (ev b t) = ev c (t.map (mv b c)) ∧ WF c (t.map (mv b c)) := by
  rcases lt_trichotomy c b with hcb | rfl | hbc
  · have hmv : mv b c = pi c b := by unfold mv; rw [if_pos hcb]
    have hB : Bases c b := ⟨hc, hb, hcb, hb1⟩
    obtain ⟨-, a2, a3⟩ := ukDown hB hκc t hw (Lv_mono (fun p hp => Ub.ub_TB_mono hκc hp) t hl) hq
    rw [hmv]; exact ⟨a2, a3⟩
  · have hmv : mv c c = id := by unfold mv; simp
    rw [hmv, map_id]; exact ⟨rfl, hw⟩
  · have hmv : mv b c = up b c := by unfold mv; rw [if_neg (not_lt.2 hbc.le), if_pos hbc]
    have hB : Bases b c := ⟨hb, hc, hbc, hc1⟩
    rw [hmv]
    exact ukUp_eq hB hκb t hw (Lv_mono (fun p hp => hp.1) t hl) hq

/-! ## The translations of [W07a] Def 6.2 -/

/-- **`t^α_τ` is correct** ([W07a] Def 6.2, Lemma 6.3 through `R2.vt_wbar`, `R2.uhVt_tr` (i) for the constant
levels and `R2.ukVt_tr3` (i) for the level terms, whose condition `α ≤ rjDat Γ` is `UkL.dat` at `α`): for
`α = Dl τ n` (`n ≥ 1`), levels over `κ < τ`, leaves in `T^α`, the argument bounds and node conditions over `α`, and
every node value over `α` below `α⁺ = Dp τ n`: `tr α t` has them over `τ` and `(tr α t)[τ] = t[α]`. -/
theorem ukTrA {κ τ : Ordinal.{0}} (hB : Bases κ τ) {n : ℕ} (hn : 1 ≤ n) :
    ∀ t : UkT, Qs κ t → Lv (· ∈ Tset (Dl τ n)) t → WF (Dl τ n) t → Nd (Dl τ n) (· < Dp τ n) t →
      WF τ (tr (Dl τ n) t) ∧ ev τ (tr (Dl τ n) t) = ev (Dl τ n) t
  | .par _, _, _, _, _ => ⟨trivial, rfl⟩
  | .add s t, hq, hl, hw, hd => by
    obtain ⟨a1, a2⟩ := ukTrA hB hn s hq.1 hl.1 hw.1 hd.1
    obtain ⟨b1, b2⟩ := ukTrA hB hn t hq.2 hl.2 hw.2 hd.2
    refine ⟨⟨a1, b1⟩, ?_⟩
    simp only [tr, ev]; rw [a2, b2]
  | .base, _, _, _, _ => ⟨trivial, rfl⟩
  | .th1 s, hq, hl, hw, hd => by
    obtain ⟨a1, a2⟩ := ukTrA hB hn s hq hl hw.1 hd
    obtain ⟨hτα, hαE, -⟩ := Dl_E hB.2.1 hB.2.2.2 hn
    have hα1 : Dl τ n < Om1 := (Dl_spec hB.2.1 hB.2.2.2 n).2.1
    have hab : τ + Dl τ n = Dl τ n :=
      add_of_omega0_opow_le (show τ < ω ^ Dl τ n by rw [hαE]; exact hτα) (le_of_eq hαE)
    have hlt : Dl τ n + ev (Dl τ n) s < Om1 := Om1_add_lt hα1 hw.2
    refine ⟨⟨⟨trivial, a1⟩, ?_⟩, ?_⟩
    · simp only [ev]; rw [a2]; exact hlt
    · simp only [tr, ev]
      rw [a2, vt_wbar hB.2.1 hB.2.2.2 hlt, vt_wbar hαE hα1 hw.2, ← add_assoc, hab]
  | .thc q r, hq, hl, hw, hd => by
    obtain ⟨a1, a2⟩ := ukTrA hB hn r hq.2 hl hw.1 hd.2
    obtain ⟨hτα, hαE, -⟩ := Dl_E hB.2.1 hB.2.2.2 hn
    have hα1 : Dl τ n < Om1 := (Dl_spec hB.2.1 hB.2.2.2 n).2.1
    have hBα : Bases κ (Dl τ n) := ⟨hB.1, hαE, hB.2.2.1.trans hτα, hα1⟩
    have hlt : Dl τ n + ev (Dl τ n) r < Om1 := Om1_add_lt hα1 hw.2
    have hrT := ukMem hBα r hl hw.1 hq.2
    have hargT := (uh_arg_T hBα hq.1 hrT hw.2).1
    have e := (uhVt_tr hB.2.1 hB.2.2.2 hn hq.1.1 hq.1.2.1 (hq.1.2.2.trans hB.2.2.1) hw.2).1 hargT hd.1
    refine ⟨⟨⟨trivial, a1⟩, ?_⟩, ?_⟩
    · simp only [ev]; rw [a2]; exact hlt
    · simp only [tr, ev]; rw [a2, e]
  | .thg G r, hq, hl, hw, hd => by
    obtain ⟨a1, a2⟩ := ukTrA hB hn r hq.2 hl.2 hw.1 hd.2.2
    obtain ⟨l1, l2, l3⟩ := UkL.evTrA hB hn G hq.1 hl.1 hw.2.wl hd.2.1
    obtain ⟨hτα, hαE, -⟩ := Dl_E hB.2.1 hB.2.2.2 hn
    obtain ⟨M, hM, hM1⟩ := UkL.ev_dvd (τ := Dl τ n) G hw.2.gs
    have hwl' := UkL.Lf_mono (fun _ hc => hc.2) G hw.2.wl
    have hdat := (UkL.dat (InE.pos hαE) G hwl' hw.2.hb hw.2.hd).1
    have hME : Om1 * M < Gg.ggE := hM ▸ UkL.ev_lt_E G hwl'
    have hmem := hw.2.mem
    have hlt := hd.1
    rw [hM] at hmem hlt hdat
    obtain ⟨m1, e1⟩ := (ukVt_tr3 hB.2.1 hB.2.2.2 hn hM1 hME hdat hw.2.r1).1 hmem hlt
    have hev : UkL.ev τ (G.tr (Dl τ n)) + ev τ (tr (Dl τ n) r) = Om1 * M + ev (Dl τ n) r := by
      rw [l2, a2, hM]
    refine ⟨⟨a1, by rw [a2]; exact hw.2.r1, l1, (UkL.Gs_tr _ G).2 hw.2.gs,
      UkL.HbS_trA hB hn G hq.1 hl.1 hw.2.wl hd.2.1 hw.2.hb, UkL.Hd_tr hτα.le G hw.2.hd,
      by rw [hev]; exact m1, ?_, ?_⟩, ?_⟩
    · rw [hev, ← e1, UkL.bd_tr G l3, ← hM]; exact hw.2.bd
    · rw [hev, ← e1, a2, ← hM]; exact hw.2.rb
    · simp only [tr, ev]; rw [hev, ← e1, hM]

/-- **`t^τ_α` is correct** ([W07a] Def 6.2, Lemma 6.3 through `R2.vt_wbar`, `R2.uhVt_tr` (ii) and
`R2.ukVt_tr3` (ii)): for `α = Dl τ n` (`n ≥ 1`), levels over `κ < τ`, if `tr α t` has the argument bounds and node
conditions over `τ`, leaves in `Tᵗ`, and every node value of `tr α t` over `τ` is below `α⁺ = Dp τ n`, and the head
of every level term of `t` is high over `α` (`HdA α t`; the decision `Γ^* ≥ α`), then `t` has them over `α` and
`(tr α t)[τ] = t[α]`. -/
theorem ukTrB {κ τ : Ordinal.{0}} (hB : Bases κ τ) {n : ℕ} (hn : 1 ≤ n) :
    ∀ t : UkT, Qs κ t → Lv (· ∈ Tset τ) (tr (Dl τ n) t) → WF τ (tr (Dl τ n) t) →
      Nd τ (· < Dp τ n) (tr (Dl τ n) t) → HdA (Dl τ n) t → WF (Dl τ n) t ∧ ev τ (tr (Dl τ n) t) = ev (Dl τ n) t
  | .par _, _, _, _, _, _ => ⟨trivial, rfl⟩
  | .add s t, hq, hl, hw, hd, hh => by
    obtain ⟨a1, a2⟩ := ukTrB hB hn s hq.1 hl.1 hw.1 hd.1 hh.1
    obtain ⟨b1, b2⟩ := ukTrB hB hn t hq.2 hl.2 hw.2 hd.2 hh.2
    refine ⟨⟨a1, b1⟩, ?_⟩
    simp only [tr, ev]; rw [a2, b2]
  | .base, _, _, _, _, _ => ⟨trivial, rfl⟩
  | .th1 s, hq, hl, hw, hd, hh => by
    obtain ⟨a1, a2⟩ := ukTrB hB hn s hq hl.2 hw.1.2 hd.2 hh
    obtain ⟨hτα, hαE, -⟩ := Dl_E hB.2.1 hB.2.2.2 hn
    have hα1 : Dl τ n < Om1 := (Dl_spec hB.2.1 hB.2.2.2 n).2.1
    have hab : τ + Dl τ n = Dl τ n :=
      add_of_omega0_opow_le (show τ < ω ^ Dl τ n by rw [hαE]; exact hτα) (le_of_eq hαE)
    have h2 := hw.2
    simp only [ev] at h2; rw [a2] at h2
    have hs1 : ev (Dl τ n) s < Om1 := lt_of_le_of_lt le_add_self h2
    refine ⟨⟨a1, hs1⟩, ?_⟩
    simp only [tr, ev]
    rw [a2, vt_wbar hB.2.1 hB.2.2.2 h2, vt_wbar hαE hα1 hs1, ← add_assoc, hab]
  | .thc q r, hq, hl, hw, hd, hh => by
    obtain ⟨a1, a2⟩ := ukTrB hB hn r hq.2 hl.2 hw.1.2 hd.2.2 hh
    have h2 := hw.2
    simp only [ev] at h2
    have hr1 : ev (Dl τ n) r < Om1 := by rw [← a2]; exact lt_of_le_of_lt le_add_self h2
    have hαT : Dl τ n ∈ Tset τ := (Dl_spec hB.2.1 hB.2.2.2 n).1
    have hrT : ev τ (tr (Dl τ n) r) ∈ Tset τ :=
      ukMem hB _ hl.2 hw.1.2 (Qs_tr _ r hq.2)
    have hsT : Dl τ n + ev τ (tr (Dl τ n) r) ∈ Tset τ := vzT_add hB.2.1 hB.2.2.2 hαT hrT
    have hargT := (uh_arg_T hB hq.1 hsT h2).1
    have hd1 := hd.1
    simp only [ev] at hd1
    rw [a2] at hargT hd1
    have e := (uhVt_tr hB.2.1 hB.2.2.2 hn hq.1.1 hq.1.2.1 (hq.1.2.2.trans hB.2.2.1) hr1).2 hargT hd1
    refine ⟨⟨a1, hr1⟩, ?_⟩
    simp only [tr, ev]; rw [a2, e]
  | .thg G r, hq, hl, hw, hd, hh => by
    obtain ⟨a1, a2⟩ := ukTrB hB hn r hq.2 hl.2 hw.1 hd.2.2 hh.2
    obtain ⟨l1, l2, l3⟩ := UkL.evTrB hB hn G hq.1 hl.1 hw.2.wl hd.2.1
    obtain ⟨-, hαE, -⟩ := Dl_E hB.2.1 hB.2.2.2 hn
    have hgs : UkL.Gs G := (UkL.Gs_tr _ G).1 hw.2.gs
    have hhb : UkL.HbS (Dl τ n) G := UkL.HbS_trB hB hn G hq.1 hl.1 hw.2.wl hd.2.1 hw.2.hb
    obtain ⟨M, hM, hM1⟩ := UkL.ev_dvd (τ := Dl τ n) G hgs
    have hwl' := UkL.Lf_mono (fun _ hc => hc.2) G l1
    have hdat := (UkL.dat (InE.pos hαE) G hwl' hhb hh.1).1
    have hME : Om1 * M < Gg.ggE := hM ▸ UkL.ev_lt_E G hwl'
    have hr1 : ev (Dl τ n) r < Om1 := by rw [← a2]; exact hw.2.r1
    have hev : UkL.ev τ (G.tr (Dl τ n)) + ev τ (tr (Dl τ n) r) = Om1 * M + ev (Dl τ n) r := by
      rw [l2, a2, hM]
    have hmem := hw.2.mem
    have hlt := hd.1
    rw [hev] at hmem hlt
    rw [hM] at hdat
    obtain ⟨m1, e1⟩ := (ukVt_tr3 hB.2.1 hB.2.2.2 hn hM1 hME hdat hr1).2 hmem hlt
    refine ⟨⟨a1, hr1, l1, hgs, hhb, hh.1, by rw [hM]; exact m1, ?_, ?_⟩, ?_⟩
    · rw [hM, ← e1, ← hev, ← UkL.bd_tr G l3]; exact hw.2.bd
    · rw [hM, ← e1, ← hev, ← a2]; exact hw.2.rb
    · simp only [tr, ev]; rw [hev, e1, hM]

/-! ## The terms of `Uh.UhT` -/

/-- The terms of `Uh.UhT` (constant levels) as terms of `UkT`. -/
def ofUh : UhT → UkT
  | .par p => .par p
  | .add s t => .add (ofUh s) (ofUh t)
  | .base => .base
  | .th1 s => .th1 (ofUh s)
  | .thc q r => .thc q (ofUh r)

theorem ofUh_ev (τ : Ordinal.{0}) : ∀ t : UhT, ev τ (ofUh t) = UhT.ev τ t
  | .par _ => rfl
  | .add s t => by simp only [ofUh, ev, UhT.ev, ofUh_ev τ s, ofUh_ev τ t]
  | .base => rfl
  | .th1 s => by simp only [ofUh, ev, UhT.ev, ofUh_ev τ s]
  | .thc _ r => by simp only [ofUh, ev, UhT.ev, ofUh_ev τ r]

theorem ofUh_map (f : Ordinal.{0} → Ordinal.{0}) : ∀ t : UhT, ofUh (t.map f) = (ofUh t).map f
  | .par _ => rfl
  | .add s t => by simp only [ofUh, map, UhT.map, ofUh_map f s, ofUh_map f t]
  | .base => rfl
  | .th1 s => by simp only [ofUh, map, UhT.map, ofUh_map f s]
  | .thc _ r => by simp only [ofUh, map, UhT.map, ofUh_map f r]

theorem ofUh_WF (τ : Ordinal.{0}) : ∀ t : UhT, WF τ (ofUh t) ↔ UhT.WF τ t
  | .par _ => Iff.rfl
  | .add s t => by simp only [ofUh, WF, UhT.WF]; rw [ofUh_WF τ s, ofUh_WF τ t]
  | .base => Iff.rfl
  | .th1 s => by simp only [ofUh, WF, UhT.WF]; rw [ofUh_WF τ s, ofUh_ev τ s]
  | .thc _ r => by simp only [ofUh, WF, UhT.WF]; rw [ofUh_WF τ r, ofUh_ev τ r]

theorem ofUh_Lv {P : Ordinal.{0} → Prop} : ∀ t : UhT, Lv P (ofUh t) ↔ UhT.Lv P t
  | .par _ => Iff.rfl
  | .add s t => by simp only [ofUh, Lv, UhT.Lv]; rw [ofUh_Lv s, ofUh_Lv t]
  | .base => Iff.rfl
  | .th1 s => by simp only [ofUh, Lv, UhT.Lv]; exact ofUh_Lv s
  | .thc _ r => by simp only [ofUh, Lv, UhT.Lv]; exact ofUh_Lv r

theorem ofUh_Qs {κ : Ordinal.{0}} : ∀ t : UhT, Qs κ (ofUh t) ↔ UhT.Qs κ t
  | .par _ => Iff.rfl
  | .add s t => by simp only [ofUh, Qs, UhT.Qs]; rw [ofUh_Qs s, ofUh_Qs t]
  | .base => Iff.rfl
  | .th1 s => by simp only [ofUh, Qs, UhT.Qs]; exact ofUh_Qs s
  | .thc _ r => by simp only [ofUh, Qs, UhT.Qs]; rw [ofUh_Qs r]

/-- The countable-argument terms of `Ub.UbT` as terms of `UkT` (through `Uh.ofUb`). -/
def ofUbk (t : Ub.UbT) : UkT := ofUh (ofUb t)

theorem ofUbk_ev (τ : Ordinal.{0}) (t : Ub.UbT) (hA : Ub.UbT.IsA t) : ev τ (ofUbk t) = Ub.UbT.ev τ t := by
  rw [ofUbk, ofUh_ev, ofUb_ev τ t hA]

theorem ofUbk_map (f : Ordinal.{0} → Ordinal.{0}) (t : Ub.UbT) : ofUbk (t.map f) = (ofUbk t).map f := by
  simp only [ofUbk, ofUb_map, ofUh_map]

theorem ofUbk_WF (τ : Ordinal.{0}) (t : Ub.UbT) (hA : Ub.UbT.IsA t) : WF τ (ofUbk t) ↔ Ub.UbT.WF τ t := by
  rw [ofUbk, ofUh_WF, ofUb_WF τ t hA]

theorem ofUbk_Lv {P : Ordinal.{0} → Prop} (t : Ub.UbT) (hA : Ub.UbT.IsA t) : Lv P (ofUbk t) ↔ Ub.UbT.Lv P t := by
  rw [ofUbk, ofUh_Lv, ofUb_Lv t hA]

theorem ofUbk_Qs (κ : Ordinal.{0}) (t : Ub.UbT) : Qs κ (ofUbk t) := (ofUh_Qs _).2 (ofUb_Qs κ t)

/-! ## Finite sets of parameters and of level data -/

namespace UkL

/-- The parameters of the leaves. -/
noncomputable def lvs : UkL → Finset Ordinal.{0}
  | lf c => Uh.lvs c
  | om b => lvs b
  | ad x y => lvs x ∪ lvs y

/-- The data of the constant levels inside the leaves. -/
noncomputable def lvq : UkL → Finset Ordinal.{0}
  | lf c => Uh.lvq c
  | om b => lvq b
  | ad x y => lvq x ∪ lvq y

theorem Lv_lvs_sub {s : Finset Ordinal.{0}} : ∀ G : UkL, lvs G ⊆ s → Lf (UhT.Lv (· ∈ s)) G
  | lf c, h => UhT.Lv_mono (fun _ hp => h hp) c (Uh.Lv_lvs c)
  | om b, h => Lv_lvs_sub b h
  | ad x y, h => ⟨Lv_lvs_sub x (Finset.union_subset_left h), Lv_lvs_sub y (Finset.union_subset_right h)⟩

theorem mem_lvs {P : Ordinal.{0} → Prop} : ∀ {G : UkL}, Lf (UhT.Lv P) G → ∀ p ∈ lvs G, P p
  | lf c, h, p, hp => Uh.mem_lvs (t := c) h p hp
  | om b, h, p, hp => mem_lvs (G := b) h p hp
  | ad x y, h, p, hp => by
    rcases Finset.mem_union.1 hp with hp | hp
    · exact mem_lvs (G := x) h.1 p hp
    · exact mem_lvs (G := y) h.2 p hp

theorem Qs_of_lvq {b γ : Ordinal.{0}} : ∀ G : UkL, Lf (UhT.Qs b) G → (∀ q ∈ lvq G, q < γ) → Lf (UhT.Qs γ) G
  | lf c, h, hq => Uh.Qs_of_lvq c h hq
  | om b', h, hq => Qs_of_lvq b' h hq
  | ad x y, h, hq => ⟨Qs_of_lvq x h.1 (fun q hq' => hq q (Finset.mem_union_left _ hq')),
      Qs_of_lvq y h.2 (fun q hq' => hq q (Finset.mem_union_right _ hq'))⟩

theorem lvq_lt {b : Ordinal.{0}} : ∀ G : UkL, Lf (UhT.Qs b) G → ∀ q ∈ lvq G, q < b
  | lf c, h, q, hq => Uh.lvq_lt c h q hq
  | om b', h, q, hq => lvq_lt b' h q hq
  | ad x y, h, q, hq => by
    rcases Finset.mem_union.1 hq with hq | hq
    · exact lvq_lt x h.1 q hq
    · exact lvq_lt y h.2 q hq

end UkL

namespace UkT

/-- The set of parameters (also inside the level terms). -/
noncomputable def lvs : UkT → Finset Ordinal.{0}
  | par p => {p}
  | add s t => lvs s ∪ lvs t
  | base => ∅
  | th1 s => lvs s
  | thc _ r => lvs r
  | thg G r => UkL.lvs G ∪ lvs r

/-- The data `rjDat q` of the constant levels (also inside the level terms). -/
noncomputable def lvq : UkT → Finset Ordinal.{0}
  | par _ => ∅
  | add s t => lvq s ∪ lvq t
  | base => ∅
  | th1 s => lvq s
  | thc q r => insert (Rj.rjDat q) (lvq r)
  | thg G r => UkL.lvq G ∪ lvq r

theorem Lv_lvs : ∀ t : UkT, Lv (· ∈ lvs t) t
  | par _ => Finset.mem_singleton_self _
  | add s t => ⟨Lv_mono (fun _ hp => Finset.mem_union_left _ hp) s (Lv_lvs s),
      Lv_mono (fun _ hp => Finset.mem_union_right _ hp) t (Lv_lvs t)⟩
  | base => trivial
  | th1 s => Lv_lvs s
  | thc _ r => Lv_lvs r
  | thg G r => ⟨UkL.Lv_lvs_sub G Finset.subset_union_left,
      Lv_mono (fun _ hp => Finset.mem_union_right _ hp) r (Lv_lvs r)⟩

theorem mem_lvs {P : Ordinal.{0} → Prop} : ∀ {t : UkT}, Lv P t → ∀ p ∈ lvs t, P p
  | par _, h, p, hp => by rw [lvs, Finset.mem_singleton] at hp; rw [hp]; exact h
  | add s t, h, p, hp => by
    rcases Finset.mem_union.1 hp with hp | hp
    · exact mem_lvs (t := s) h.1 p hp
    · exact mem_lvs (t := t) h.2 p hp
  | base, _, p, hp => absurd hp (Finset.notMem_empty p)
  | th1 s, h, p, hp => mem_lvs (t := s) h p hp
  | thc _ r, h, p, hp => mem_lvs (t := r) h p hp
  | thg G r, h, p, hp => by
    rcases Finset.mem_union.1 hp with hp | hp
    · exact UkL.mem_lvs h.1 p hp
    · exact mem_lvs (t := r) h.2 p hp

/-- Levels over `b` whose data are below `γ` are levels over `γ`. -/
theorem Qs_of_lvq {b γ : Ordinal.{0}} : ∀ t : UkT, Qs b t → (∀ q ∈ lvq t, q < γ) → Qs γ t
  | par _, _, _ => trivial
  | add s t, h, hq => ⟨Qs_of_lvq s h.1 (fun q hq' => hq q (Finset.mem_union_left _ hq')),
      Qs_of_lvq t h.2 (fun q hq' => hq q (Finset.mem_union_right _ hq'))⟩
  | base, _, _ => trivial
  | th1 s, h, hq => Qs_of_lvq s h hq
  | thc _ r, h, hq => ⟨⟨h.1.1, h.1.2.1, hq _ (Finset.mem_insert_self _ _)⟩,
      Qs_of_lvq r h.2 (fun q' hq' => hq q' (Finset.mem_insert_of_mem hq'))⟩
  | thg G r, h, hq => ⟨UkL.Qs_of_lvq G h.1 (fun q hq' => hq q (Finset.mem_union_left _ hq')),
      Qs_of_lvq r h.2 (fun q hq' => hq q (Finset.mem_union_right _ hq'))⟩

/-- The data of the levels of a term with levels over `b` are below `b`. -/
theorem lvq_lt {b : Ordinal.{0}} : ∀ t : UkT, Qs b t → ∀ q ∈ lvq t, q < b
  | par _, _, q, hq => absurd hq (Finset.notMem_empty q)
  | add s t, h, q, hq => by
    rcases Finset.mem_union.1 hq with hq | hq
    · exact lvq_lt s h.1 q hq
    · exact lvq_lt t h.2 q hq
  | base, _, q, hq => absurd hq (Finset.notMem_empty q)
  | th1 s, h, q, hq => lvq_lt s h q hq
  | thc q' r, h, q, hq => by
    rcases Finset.mem_insert.1 hq with rfl | hq
    · exact h.1.2.2
    · exact lvq_lt r h.2 q hq
  | thg G r, h, q, hq => by
    rcases Finset.mem_union.1 hq with hq | hq
    · exact UkL.lvq_lt G h.1 q hq
    · exact lvq_lt r h.2 q hq

end UkT

end Googology.Trans.PoR.InaccPsi.R2.Uk

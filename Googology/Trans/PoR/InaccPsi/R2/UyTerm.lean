import Googology.Trans.PoR.InaccPsi.R2.UrTerm
import Googology.Trans.PoR.InaccPsi.R2.UyFix

/-!
# Gap levels and constant levels `Ω₁·q < B₂`: the term lemmas of `Ur` with `UyLev` levels

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

The term type is `Un.UnT`, the node conditions, the decision and the translation are those of `R2.UrTerm`
(`Ur.WFr`, `Ur.HdD`, `Ur.trr`, …).  In `R2.UrTerm` a constant level `thc q r` asks `Uh.UhLev κ q`
(`q < ε_{Ω₁+1}`, `rjDat q < κ`); here it asks `Uy.UyLev κ q` (`Ω₁·q < B₂`, `ucDat q, ucDat(Ω₁·q) < κ`;
`Uh.UhLev ⇒ UyLev`, `Uy.uyLev_of_uh`), so constant levels range over every `Ω₁·q < B₂ = ψ_{Ω₂}(ε_{Ω₂+1})`.
The proofs are those of `R2.UrTerm` with the node lemmas of `R2.UyFix` (`uy_Om1_mul_TB`, `uy_arg_T`, `uy_arg_lt`,
`uyLt_vt_self`, and the translation `uyVt_tr` from `R2.uvVt_trL`).

* `QsY` (**every constant level is a level over `κ` in the sense of `UyLev`**), `qsY_of_qs` (**`Un.UnT.Qs ⇒ QsY`**),
  `QsY_map`, `QsY_mono`, `qsY_trr`, `uy_arg_lt`;
* `uyMem`, `uyHiC_le`, `uyDatHb`, `uyDatFN`, `uyDatM`, `uyLeB`, `uyLe`, `uyDownB`, `uyDown`, `uyUpB`, `uyUp`,
  `uyUp_eq`, `uyMv` (**membership, order, base change and segment move on terms**);
* `uyTrAB`, `uyTrA`, `uyTrBB`, `uyTrB` (**the translations `t^α_τ`, `t^τ_α` of [W07a] Def 6.2 at every level**).

New definition: `QsY`.  No new axiom (uses `R2.uvVt_trL` through `Uy.uyVt_tr`).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uy

open Ordinal Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Uh Googology.Trans.PoR.InaccPsi.R2.Un
  Googology.Trans.PoR.InaccPsi.R2.Un.UnT Googology.Trans.PoR.InaccPsi.R2.Ur

/-- **Every constant level is a level over `κ`** (`UyLev`; the level terms of `thg`-nodes are not constrained). -/
def QsY (κ : Ordinal.{0}) : {k : Bool} → UnT k → Prop
  | _, .par _ => True
  | _, .add s t => QsY κ s ∧ QsY κ t
  | _, .base => True
  | _, .th1 s => QsY κ s
  | _, .thc q r => UyLev κ q ∧ QsY κ r
  | _, .thg _ G r => QsY κ G ∧ QsY κ r
  | _, .lf c => QsY κ c
  | _, .om b => QsY κ b
  | _, .ad x y => QsY κ x ∧ QsY κ y

/-- **`Un.UnT.Qs κ t ⇒ QsY κ t`** (`Uy.uyLev_of_uh`). -/
theorem qsY_of_qs {κ : Ordinal.{0}} : ∀ {k : Bool} (t : UnT k), Qs κ t → QsY κ t
  | _, .par _, _ => trivial
  | _, .add s t, h => ⟨qsY_of_qs s h.1, qsY_of_qs t h.2⟩
  | _, .base, _ => trivial
  | _, .th1 s, h => qsY_of_qs s h
  | _, .thc _ r, h => ⟨uyLev_of_uh h.1, qsY_of_qs r h.2⟩
  | _, .thg _ G r, h => ⟨qsY_of_qs G h.1, qsY_of_qs r h.2⟩
  | _, .lf c, h => qsY_of_qs c h
  | _, .om b, h => qsY_of_qs b h
  | _, .ad x y, h => ⟨qsY_of_qs x h.1, qsY_of_qs y h.2⟩

theorem QsY_map {κ : Ordinal.{0}} (f : Ordinal.{0} → Ordinal.{0}) :
    ∀ {k : Bool} (t : UnT k), QsY κ t → QsY κ (t.map f)
  | _, .par _, _ => trivial
  | _, .add s t, h => ⟨QsY_map f s h.1, QsY_map f t h.2⟩
  | _, .base, _ => trivial
  | _, .th1 s, h => QsY_map f s h
  | _, .thc _ r, h => ⟨h.1, QsY_map f r h.2⟩
  | _, .thg _ G r, h => ⟨QsY_map f G h.1, QsY_map f r h.2⟩
  | _, .lf c, h => QsY_map f c h
  | _, .om b, h => QsY_map f b h
  | _, .ad x y, h => ⟨QsY_map f x h.1, QsY_map f y h.2⟩

theorem QsY_mono {κ κ' : Ordinal.{0}} (hκ : κ ≤ κ') : ∀ {k : Bool} (t : UnT k), QsY κ t → QsY κ' t
  | _, .par _, _ => trivial
  | _, .add s t, h => ⟨QsY_mono hκ s h.1, QsY_mono hκ t h.2⟩
  | _, .base, _ => trivial
  | _, .th1 s, h => QsY_mono hκ s h
  | _, .thc _ r, h => ⟨h.1.mono hκ, QsY_mono hκ r h.2⟩
  | _, .thg _ G r, h => ⟨QsY_mono hκ G h.1, QsY_mono hκ r h.2⟩
  | _, .lf c, h => QsY_mono hκ c h
  | _, .om b, h => QsY_mono hκ b h
  | _, .ad x y, h => ⟨QsY_mono hκ x h.1, QsY_mono hκ y h.2⟩

/-- `Ω₁·q + η < Ω₂` for a level `q` over `κ` and `η < Ω₁`. -/
theorem uy_arg_lt {κ q η : Ordinal.{0}} (hq : UyLev κ q) (hη : η < Om1) : Om1 * q + η < OmTwo :=
  (Lq.lq_SC_indec Uc.uc_SC_Om2).add_lt (hq.2.1.trans Uc.ucB_lt_Om2) (hη.trans Uc.uc_Om1_lt_Om2)

/-- The data `ucDat q`, `ucDat(Ω₁·q)` of the constant levels `q` (also inside the level terms). -/
noncomputable def lvqY : {k : Bool} → UnT k → Finset Ordinal.{0}
  | _, .par _ => ∅
  | _, .add s t => lvqY s ∪ lvqY t
  | _, .base => ∅
  | _, .th1 s => lvqY s
  | _, .thc q r => insert (Uc.ucDat q) (insert (Uc.ucDat (Om1 * q)) (lvqY r))
  | _, .thg _ G r => lvqY G ∪ lvqY r
  | _, .lf c => lvqY c
  | _, .om b => lvqY b
  | _, .ad x y => lvqY x ∪ lvqY y

/-- Levels over `b` whose data are below `γ` are levels over `γ`. -/
theorem QsY_of_lvqY {b γ : Ordinal.{0}} : ∀ {k : Bool} (t : UnT k), QsY b t → (∀ q ∈ lvqY t, q < γ) → QsY γ t
  | _, .par _, _, _ => trivial
  | _, .add s t, h, hq => ⟨QsY_of_lvqY s h.1 (fun q hq' => hq q (Finset.mem_union_left _ hq')),
      QsY_of_lvqY t h.2 (fun q hq' => hq q (Finset.mem_union_right _ hq'))⟩
  | _, .base, _, _ => trivial
  | _, .th1 s, h, hq => QsY_of_lvqY s h hq
  | _, .thc _ r, h, hq => ⟨⟨h.1.1, h.1.2.1, hq _ (Finset.mem_insert_self _ _),
      hq _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))⟩,
      QsY_of_lvqY r h.2 (fun q' hq' => hq q' (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hq')))⟩
  | _, .thg _ G r, h, hq => ⟨QsY_of_lvqY G h.1 (fun q hq' => hq q (Finset.mem_union_left _ hq')),
      QsY_of_lvqY r h.2 (fun q hq' => hq q (Finset.mem_union_right _ hq'))⟩
  | _, .lf c, h, hq => QsY_of_lvqY c h hq
  | _, .om b, h, hq => QsY_of_lvqY b h hq
  | _, .ad x y, h, hq => ⟨QsY_of_lvqY x h.1 (fun q hq' => hq q (Finset.mem_union_left _ hq')),
      QsY_of_lvqY y h.2 (fun q hq' => hq q (Finset.mem_union_right _ hq'))⟩

/-- The data of the levels of a term with levels over `b` are below `b`. -/
theorem lvqY_lt {b : Ordinal.{0}} : ∀ {k : Bool} (t : UnT k), QsY b t → ∀ q ∈ lvqY t, q < b
  | _, .par _, _, q, hq => absurd hq (Finset.notMem_empty q)
  | _, .add s t, h, q, hq => by
    rcases Finset.mem_union.1 hq with hq | hq
    · exact lvqY_lt s h.1 q hq
    · exact lvqY_lt t h.2 q hq
  | _, .base, _, q, hq => absurd hq (Finset.notMem_empty q)
  | _, .th1 s, h, q, hq => lvqY_lt s h q hq
  | _, .thc _ r, h, q, hq => by
    rcases Finset.mem_insert.1 hq with rfl | hq
    · exact h.1.2.2.1
    · rcases Finset.mem_insert.1 hq with rfl | hq
      · exact h.1.2.2.2
      · exact lvqY_lt r h.2 q hq
  | _, .thg _ G r, h, q, hq => by
    rcases Finset.mem_union.1 hq with hq | hq
    · exact lvqY_lt G h.1 q hq
    · exact lvqY_lt r h.2 q hq
  | _, .lf c, h, q, hq => lvqY_lt c h q hq
  | _, .om b, h, q, hq => lvqY_lt b h q hq
  | _, .ad x y, h, q, hq => by
    rcases Finset.mem_union.1 hq with hq | hq
    · exact lvqY_lt x h.1 q hq
    · exact lvqY_lt y h.2 q hq

theorem qsY_trr {κ : Ordinal.{0}} (a : Ordinal.{0}) : ∀ {k : Bool} (t : UnT k), QsY κ t → QsY κ (trr a t)
  | _, .par _, _ => trivial
  | _, .add s t, h => ⟨qsY_trr a s h.1, qsY_trr a t h.2⟩
  | _, .base, _ => trivial
  | _, .th1 s, h => ⟨trivial, qsY_trr a s h⟩
  | _, .thc _ r, h => ⟨h.1, trivial, qsY_trr a r h.2⟩
  | _, .thg _ G r, h => by
    by_cases hG : LoL a G
    · rw [trr_thg_lo hG]; exact ⟨qsY_trr a G h.1, trivial, qsY_trr a r h.2⟩
    · rw [trr_thg_hi hG]; exact ⟨qsY_trr a G h.1, qsY_trr a r h.2⟩
  | _, .lf c, h => qsY_trr a c h
  | _, .om b, h => qsY_trr a b h
  | _, .ad x y, h => ⟨qsY_trr a x h.1, qsY_trr a y h.2⟩

/-! ## Membership, order, base change -/

theorem uyMem {κ τ : Ordinal.{0}} (hB : Bases κ τ) :
    ∀ (t : UnT false), Lv (· ∈ Tset τ) t → WFr τ t → QsY κ t → ev τ t ∈ Tset τ
  | .par _, hl, _, _ => hl
  | .add s t, hl, hw, hq => vzT_add hB.2.1 hB.2.2.2 (uyMem hB s hl.1 hw.1 hq.1) (uyMem hB t hl.2 hw.2 hq.2)
  | .base, _, _, _ => uh_T_le hB.2.1 hB.2.2.2 le_rfl
  | .th1 s, hl, hw, hq => by
    have hτ1 := hB.2.2.2
    have h1 : (1 : Ordinal.{0}) ∈ Tset τ := uh_T_le hB.2.1 hτ1 (Ub.ub_one_lt hB.2.1).le
    have hO : (1 : Ordinal.{0}) < Om1 := (Ub.ub_one_lt hB.2.1).trans hτ1
    exact (vt_mem hB.2.1 hτ1 (vzT_add hB.2.1 hτ1 h1 (uyMem hB s hl hw.1 hq)) (Om1_add_lt hO hw.2)).1
  | .thc _ r, hl, hw, hq => by
    obtain ⟨h1, h2⟩ := uy_arg_T hB hq.1 (uyMem hB r hl hw.1 hq.2) hw.2
    exact (vt_memTwo hB.2.1 hB.2.2.2 h1 h2).1
  | .thg _ G _, _, hw, _ =>
    (vt_memTwo hB.2.1 hB.2.2.2 hw.2.2.mem (Uk.arg_lt2 (ev_lt_Er G hw.1) hw.2.2.r1)).1

/-- **A high countable term is `≥ τ`** ([W07a] Lemma 3.30 through `R2.vt_memTwo` at the `ϑ`-heads, Lemma 4.2
through `R2.vt_wbar` at `ϑᵗ(1 + ξ)`). -/
theorem uyHiC_le {κ τ : Ordinal.{0}} (hB : Bases κ τ) :
    ∀ (c : UnT false), Lv (· ∈ Tset τ) c → WFr τ c → QsY κ c → HiC τ c → τ ≤ ev τ c
  | .par _, _, _, _, h => h
  | .add s _, hl, hw, hq, h => by
    simp only [ev]; exact (uyHiC_le hB s hl.1 hw.1 hq.1 h).trans le_self_add
  | .base, _, _, _, _ => le_rfl
  | .th1 s, _, hw, _, _ => by
    simp only [ev]; rw [vt_wbar hB.2.1 hB.2.2.2 hw.2]
    exact le_self_add.trans (Se.se_wbar_gt _).le
  | .thc _ r, hl, hw, hq, _ => by
    obtain ⟨h1, h2⟩ := uy_arg_T hB hq.1 (uyMem hB r hl hw.1 hq.2) hw.2
    exact (vt_memTwo hB.2.1 hB.2.2.2 h1 h2).2.1
  | .thg _ G _, _, hw, _, _ =>
    (vt_memTwo hB.2.1 hB.2.2.2 hw.2.2.mem (Uk.arg_lt2 (ev_lt_Er G hw.1) hw.2.2.r1)).2.1

/-- **The decision `Γ^{*τ} ≥ τ` in the head mode**: no absorption of the head and a high head leaf give
`τ ≤ rjDat Γ` (`Γ = G[τ]`). -/
theorem uyDatHb {κ τ : Ordinal.{0}} (hB : Bases κ τ) :
    ∀ (G : UnT true), Lv (· ∈ Tset τ) G → WFr τ G → QsY κ G → HbS τ G → Hd τ G →
      τ ≤ Rj.rjDat (ev τ G) ∧ ev τ G ≠ 0
  | .lf c, hl, hw, hq, _, hd => by
    have h1 : τ ≤ ev τ c := uyHiC_le hB c hl hw.1 hq hd
    simp only [ev]
    rw [Rj.rjDat_small hw.2]
    exact ⟨h1, ((InE.pos hB.2.1).trans_le h1).ne'⟩
  | .om b, hl, hw, hq, hb, hd => by
    obtain ⟨h1, h2⟩ := uyDatHb hB b hl hw hq hb hd
    have hbE := ev_lt_Er b hw
    have := Uk.UkL.dat_om_add (y := 0) h2 hbE (mul_pos Rj.rj_Om1_pos (opow_pos _ omega0_pos))
    rw [add_zero] at this
    simp only [ev]
    exact ⟨h1.trans this, (mul_pos Rj.rj_Om1_pos (opow_pos _ omega0_pos)).ne'⟩
  | .ad (.om b) y, hl, hw, hq, hb, hd => by
    obtain ⟨h1, h2⟩ := uyDatHb hB b hl.1 hw.1 hq.1 hb.1 hd
    have hbE := ev_lt_Er b hw.1
    have hy : ev τ y < Om1 * ω ^ (ev τ b + 1) := by rw [← Uk.UkL.om_mul_omega]; exact hb.2.2
    have := Uk.UkL.dat_om_add h2 hbE hy
    simp only [ev]
    exact ⟨h1.trans this,
      (lt_of_lt_of_le (mul_pos Rj.rj_Om1_pos (opow_pos _ omega0_pos)) le_self_add).ne'⟩
  | .ad (.lf _) _, _, _, _, hb, _ => hb.2.1.elim
  | .ad (.ad _ _) _, _, _, _, hb, _ => hb.2.1.elim

/-- **The decision `Γ^{*τ} ≥ τ` in the normal-form mode**: full Cantor normal form and SOME high leaf (also in a
non-head summand) give `τ ≤ rjDat Γ`. -/
theorem uyDatFN {κ τ : Ordinal.{0}} (hB : Bases κ τ) :
    ∀ (G : UnT true), Lv (· ∈ Tset τ) G → WFr τ G → QsY κ G → FNF τ G → HdE τ G →
      τ ≤ Rj.rjDat (ev τ G) ∧ ev τ G ≠ 0
  | .lf c, hl, hw, hq, _, hd => by
    have h1 : τ ≤ ev τ c := uyHiC_le hB c hl hw.1 hq hd
    simp only [ev]
    rw [Rj.rjDat_small hw.2]
    exact ⟨h1, ((InE.pos hB.2.1).trans_le h1).ne'⟩
  | .om b, hl, hw, hq, hb, hd => by
    obtain ⟨h1, h2⟩ := uyDatFN hB b hl hw hq hb hd
    have hbE := ev_lt_Er b hw
    have := Uk.UkL.dat_om_add (y := 0) h2 hbE (mul_pos Rj.rj_Om1_pos (opow_pos _ omega0_pos))
    rw [add_zero] at this
    simp only [ev]
    exact ⟨h1.trans this, (mul_pos Rj.rj_Om1_pos (opow_pos _ omega0_pos)).ne'⟩
  | .ad (.om b) y, hl, hw, hq, hb, hd => by
    have hbE := ev_lt_Er b hw.1
    have hy : ev τ y < Om1 * ω ^ (ev τ b + 1) := by rw [← Uk.UkL.om_mul_omega]; exact hb.2.2.2
    have hne : ev τ (UnT.ad (UnT.om b) y) ≠ 0 := by
      simp only [ev]
      exact (lt_of_lt_of_le (mul_pos Rj.rj_Om1_pos (opow_pos _ omega0_pos)) le_self_add).ne'
    rcases hd with hd | hd
    · obtain ⟨h1, h2⟩ := uyDatFN hB b hl.1 hw.1 hq.1 hb.1 hd
      have := Uk.UkL.dat_om_add h2 hbE hy
      exact ⟨by simp only [ev]; exact h1.trans this, hne⟩
    · obtain ⟨h1, h2⟩ := uyDatFN hB y hl.2 hw.2 hq.2 hb.2.1 hd
      have := dat_om_add_r hbE h2 hy
      exact ⟨by simp only [ev]; exact h1.trans this, hne⟩
  | .ad (.lf _) _, _, _, _, hb, _ => hb.2.2.1.elim
  | .ad (.ad _ _) _, _, _, _, hb, _ => hb.2.2.1.elim

/-- **The decision `Γ^{*τ} ≥ τ` in either mode.** -/
theorem uyDatM {κ τ : Ordinal.{0}} (hB : Bases κ τ) :
    ∀ (m : Bool) (G : UnT true), Lv (· ∈ Tset τ) G → WFr τ G → QsY κ G → NfM m τ G → HdM m τ G →
      τ ≤ Rj.rjDat (ev τ G) ∧ ev τ G ≠ 0
  | false, G, hl, hw, hq, hn, hd => uyDatHb hB G hl hw hq hn hd
  | true, G, hl, hw, hq, hn, hd => uyDatFN hB G hl hw hq hn hd

/-! ## Order of the parts -/

/-- **Every parameter and every node value is `≤` the value** (for level terms: `≤` every bound `V` of the
leaves). -/
theorem uyLeB {κ τ : Ordinal.{0}} (hB : Bases κ τ) :
    ∀ {k : Bool} (t : UnT k), Lv (· ∈ Tset τ) t → WFr τ t → QsY κ t → ∀ V : Ordinal.{0},
      (k = false → ev τ t ≤ V) → Lf (fun c => ev τ c ≤ V) t → Lv (· ≤ V) t ∧ Nd τ (· ≤ V) t
  | _, .par _, _, _, _, _, hv, _ => ⟨hv rfl, trivial⟩
  | _, .add s t, hl, hw, hq, V, hv, _ => by
    have hs : ev τ s ≤ V := le_self_add.trans (hv rfl)
    have ht : ev τ t ≤ V := le_add_self.trans (hv rfl)
    obtain ⟨a1, a2⟩ := uyLeB hB s hl.1 hw.1 hq.1 V (fun _ => hs) (Lf_cnt _ s)
    obtain ⟨b1, b2⟩ := uyLeB hB t hl.2 hw.2 hq.2 V (fun _ => ht) (Lf_cnt _ t)
    exact ⟨⟨a1, b1⟩, ⟨a2, b2⟩⟩
  | _, .base, _, _, _, _, _, _ => ⟨trivial, trivial⟩
  | _, .th1 s, hl, hw, hq, V, hv, _ => by
    have hle : ev τ s ≤ ev τ (.th1 s) := by
      simp only [ev]; rw [vt_wbar hB.2.1 hB.2.2.2 hw.2]
      exact le_add_self.trans (Se.se_wbar_gt _).le
    exact uyLeB hB s hl hw.1 hq V (fun _ => hle.trans (hv rfl)) (Lf_cnt _ s)
  | _, .thc q r, hl, hw, hq, V, hv, _ => by
    have hrT := uyMem hB r hl hw.1 hq.2
    have hlt : ev τ r < ev τ (.thc q r) := uyLt_vt_self hB hq.1 hrT hw.2
    obtain ⟨a1, a2⟩ := uyLeB hB r hl hw.1 hq.2 V (fun _ => hlt.le.trans (hv rfl)) (Lf_cnt _ r)
    exact ⟨a1, hv rfl, a2⟩
  | _, .thg m G r, hl, hw, hq, V, hv, _ => by
    have hvV : ev τ (UnT.thg m G r) ≤ V := hv rfl
    obtain ⟨a1, a2⟩ := uyLeB hB r hl.2 hw.2.1 hq.2 V (fun _ => hw.2.2.rb.le.trans hvV) (Lf_cnt _ r)
    obtain ⟨l1, l2⟩ := uyLeB hB G hl.1 hw.1 hq.1 V (fun h => nomatch h)
      (Lf_mono (fun c hc => hc.le.trans hvV) G hw.2.2.bd)
    exact ⟨⟨l1, a1⟩, ⟨hvV, l2, a2⟩⟩
  | _, .lf c, hl, hw, hq, V, _, hc => uyLeB hB c hl hw.1 hq V (fun _ => hc) (Lf_cnt _ c)
  | _, .om b, hl, hw, hq, V, _, hc => uyLeB hB b hl hw hq V (fun h => nomatch h) hc
  | _, .ad x y, hl, hw, hq, V, _, hc => by
    obtain ⟨a1, a2⟩ := uyLeB hB x hl.1 hw.1 hq.1 V (fun h => nomatch h) hc.1
    obtain ⟨b1, b2⟩ := uyLeB hB y hl.2 hw.2 hq.2 V (fun h => nomatch h) hc.2
    exact ⟨⟨a1, b1⟩, ⟨a2, b2⟩⟩

/-- **Every parameter and every node value is `≤` the value.** -/
theorem uyLe {κ τ : Ordinal.{0}} (hB : Bases κ τ) (t : UnT false) (hl : Lv (· ∈ Tset τ) t) (hw : WFr τ t)
    (hq : QsY κ t) : Lv (· ≤ ev τ t) t ∧ Nd τ (· ≤ ev τ t) t :=
  uyLeB hB t hl hw hq _ (fun _ => le_rfl) (UnT.Lf_cnt _ t)

/-! ## The base change -/

/-- **The base change on terms of both sorts** ([W07a] Def 5.1, Lemma 5.3 through `R2.pi_vt`, `R2.pi_vt_two`,
`R2.pi_add`, `Uy.uy_Om1_mul_TB`, `R2.siOm1_opow_TB`): values, argument bounds, node conditions (both modes), the
`·ω`-bounds of the sums and the leaf bounds are carried by `π_{σ,τ}`. -/
theorem uyDownB {κ σ τ : Ordinal.{0}} (h : Bases σ τ) (hκσ : κ ≤ σ) :
    ∀ {k : Bool} (t : UnT k), WFr τ t → Lv (· ∈ TB τ σ) t → QsY κ t →
      ev τ t ∈ TB τ σ ∧ pi σ τ (ev τ t) = ev σ (t.map (pi σ τ)) ∧ WFr σ (t.map (pi σ τ)) ∧
      (HbS τ t → HbS σ (t.map (pi σ τ))) ∧ (FNF τ t → FNF σ (t.map (pi σ τ))) ∧
      (∀ V ∈ TB τ σ, Lf (fun c => ev τ c < V) t → Lf (fun c => ev σ c < pi σ τ V) (t.map (pi σ τ)))
  | _, .par p, _, hp, _ => ⟨hp, rfl, trivial, fun _ => trivial, fun _ => trivial, fun _ _ _ => trivial⟩
  | _, .add s t, hw, hl, hq => by
    obtain ⟨a1, a2, a3, -⟩ := uyDownB h hκσ s hw.1 hl.1 hq.1
    obtain ⟨b1, b2, b3, -⟩ := uyDownB h hκσ t hw.2 hl.2 hq.2
    obtain ⟨c1, c2⟩ := pi_add h a1 b1
    refine ⟨c1, ?_, ⟨a3, b3⟩, fun _ => trivial, fun _ => trivial, fun _ _ _ => trivial⟩
    simp only [ev, map]; rw [c2, a2, b2]
  | _, .base, _, _, _ =>
    ⟨(pi_base h).1, (pi_base h).2, trivial, fun _ => trivial, fun _ => trivial, fun _ _ _ => trivial⟩
  | _, .th1 s, hw, hl, hq => by
    obtain ⟨a1, a2, a3, -⟩ := uyDownB h hκσ s hw.1 hl hq
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
    obtain ⟨a1, a2, a3, -⟩ := uyDownB h hκσ r hw.1 hl hq.2
    obtain ⟨g1, g2⟩ := uy_Om1_mul_TB h hκσ hq.1
    obtain ⟨c1, c2⟩ := pi_add h g1 a1
    have hlt2 : Om1 * q + ev τ r < OmTwo := uy_arg_lt hq.1 hw.2
    obtain ⟨d1, -, -, -, d2⟩ := vt_memTwo h.2.1 h.2.2.2 c1.1 hlt2
    refine ⟨⟨d1, by
      show ((Par τ (vt τ (Om1 * q + ev τ r)) : Set Ordinal.{0})) ⊆ Set.Iio σ; rw [d2]; exact c1.2⟩, ?_, ⟨a3, ?_⟩,
      fun _ => trivial, fun _ => trivial, fun _ _ _ => trivial⟩
    · simp only [ev, map]; rw [pi_vt_two h c1 hlt2, c2, g2, a2]
    · rw [← a2]; exact down_lt_Om1 h a1 hw.2
  | _, .thg m G r, hw, hl, hq => by
    obtain ⟨a1, a2, a3, -⟩ := uyDownB h hκσ r hw.2.1 hl.2 hq.2
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := uyDownB h hκσ G hw.1 hl.1 hq.1
    obtain ⟨c1, c2⟩ := pi_add h g1 a1
    have hlt2 := Uk.arg_lt2 (ev_lt_Er G hw.1) hw.2.2.r1
    obtain ⟨d1, -, -, -, d2⟩ := vt_memTwo h.2.1 h.2.2.2 c1.1 hlt2
    have hVT : vt τ (ev τ G + ev τ r) ∈ TB τ σ := ⟨d1, by
      show ((Par τ (vt τ (ev τ G + ev τ r)) : Set Ordinal.{0})) ⊆ Set.Iio σ; rw [d2]; exact c1.2⟩
    have hpv : pi σ τ (vt τ (ev τ G + ev τ r)) = vt σ (ev σ (G.map (pi σ τ)) + ev σ (r.map (pi σ τ))) := by
      rw [pi_vt_two h c1 hlt2, c2, g2, a2]
    refine ⟨hVT, by simp only [ev, map]; exact hpv, ⟨g3, a3, ?_⟩, fun _ => trivial, fun _ => trivial,
      fun _ _ _ => trivial⟩
    refine ⟨by rw [← a2]; exact down_lt_Om1 h a1 hw.2.2.r1, (Gs_map _ G).2 hw.2.2.gs,
      NfM_imp g4 g5 m hw.2.2.nf,
      HdD_map m G (Lv_mono (fun p hp => ⟨fun hτp => down_ge h hp hτp, fun hpτ => by
        have hpσ := (TB_inter_lt h hpτ).1 hp
        rw [pi_lt h hpσ]; exact hpσ⟩) G hl.1) hw.2.2.hd,
      by rw [← g2, ← a2, ← c2]; exact (pi_bijOn h).1.mapsTo c1, ?_, ?_⟩
    · rw [← hpv]; exact g6 _ hVT hw.2.2.bd
    · rw [← hpv, ← a2]; exact (pi_bijOn h).2 a1 hVT hw.2.2.rb
  | _, .lf c, hw, hl, hq => by
    obtain ⟨a1, a2, a3, -⟩ := uyDownB h hκσ c hw.1 hl hq
    refine ⟨a1, a2, ⟨a3, by rw [← a2]; exact down_lt_Om1 h a1 hw.2⟩, fun _ => trivial, fun _ => trivial,
      fun V hV hc => ?_⟩
    show ev σ (c.map (pi σ τ)) < pi σ τ V
    rw [← a2]; exact (pi_bijOn h).2 a1 hV hc
  | _, .om b, hw, hl, hq => by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := uyDownB h hκσ b hw hl hq
    have hbE := ev_lt_Er b hw
    obtain ⟨o1, o2⟩ := siOm1_opow_TB h hbE
    refine ⟨o1.2 a1, ?_, a3, a4, a5, a6⟩
    simp only [ev, map]; rw [o2 a1, a2]
  | _, .ad x y, hw, hl, hq => by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := uyDownB h hκσ x hw.1 hl.1 hq.1
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := uyDownB h hκσ y hw.2 hl.2 hq.2
    obtain ⟨c1, c2⟩ := pi_add h a1 b1
    have hω : ev τ y < ev τ x * ω → ev σ (y.map (pi σ τ)) < ev σ (x.map (pi σ τ)) * ω := by
      intro hlt; rw [← a2, ← b2]; exact (unPi_lt_mul_omega_iff h a1 b1).1 hlt
    refine ⟨c1, ?_, ⟨a3, b3⟩, fun hb => ⟨a4 hb.1, (IsOm_map _ x).2 hb.2.1, hω hb.2.2⟩,
      fun hb => ⟨a5 hb.1, b5 hb.2.1, (IsOm_map _ x).2 hb.2.2.1, hω hb.2.2.2⟩,
      fun V hV hc => ⟨a6 V hV hc.1, b6 V hV hc.2⟩⟩
    simp only [ev, map]; rw [c2, a2, b2]

/-- **The base change on terms**: `π_{σ,τ}(t[τ; p]) = t[σ; π p]`, the image has the argument bounds and the node
conditions over `σ`. -/
theorem uyDown {κ σ τ : Ordinal.{0}} (h : Bases σ τ) (hκσ : κ ≤ σ) (t : UnT false) (hw : WFr τ t)
    (hl : Lv (· ∈ TB τ σ) t) (hq : QsY κ t) :
    ev τ t ∈ TB τ σ ∧ pi σ τ (ev τ t) = ev σ (t.map (pi σ τ)) ∧ WFr σ (t.map (pi σ τ)) := by
  obtain ⟨a1, a2, a3, -⟩ := uyDownB h hκσ t hw hl hq
  exact ⟨a1, a2, a3⟩

/-- **The inverse base change on terms of both sorts.** -/
theorem uyUpB {κ σ τ : Ordinal.{0}} (h : Bases σ τ) (hκσ : κ ≤ σ) :
    ∀ {k : Bool} (t : UnT k), WFr σ t → Lv (· ∈ Tset σ) t → QsY κ t →
      ev τ (t.map (up σ τ)) ∈ TB τ σ ∧ pi σ τ (ev τ (t.map (up σ τ))) = ev σ t ∧ WFr τ (t.map (up σ τ)) ∧
      (HbS σ t → HbS τ (t.map (up σ τ))) ∧ (FNF σ t → FNF τ (t.map (up σ τ))) ∧
      (∀ V ∈ TB τ σ, Lf (fun c => ev σ c < pi σ τ V) t → Lf (fun c => ev τ c < V) (t.map (up σ τ)))
  | _, .par p, _, hp, _ =>
    ⟨(up_spec h hp).1, (up_spec h hp).2, trivial, fun _ => trivial, fun _ => trivial, fun _ _ _ => trivial⟩
  | _, .add s t, hw, hl, hq => by
    obtain ⟨a1, a2, a3, -⟩ := uyUpB h hκσ s hw.1 hl.1 hq.1
    obtain ⟨b1, b2, b3, -⟩ := uyUpB h hκσ t hw.2 hl.2 hq.2
    obtain ⟨c1, c2⟩ := pi_add h a1 b1
    refine ⟨c1, ?_, ⟨a3, b3⟩, fun _ => trivial, fun _ => trivial, fun _ _ _ => trivial⟩
    simp only [ev, map] at c2 ⊢; rw [c2, a2, b2]
  | _, .base, _, _, _ =>
    ⟨(pi_base h).1, (pi_base h).2, trivial, fun _ => trivial, fun _ => trivial, fun _ _ _ => trivial⟩
  | _, .th1 s, hw, hl, hq => by
    obtain ⟨a1, a2, a3, -⟩ := uyUpB h hκσ s hw.1 hl hq
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
    obtain ⟨a1, a2, a3, -⟩ := uyUpB h hκσ r hw.1 hl hq.2
    have hy1 := unUp_lt_Om1 h a1 a2 hw.2
    obtain ⟨g1, g2⟩ := uy_Om1_mul_TB h hκσ hq.1
    obtain ⟨c1, c2⟩ := pi_add h g1 a1
    have hlt2 : Om1 * q + ev τ (r.map (up σ τ)) < OmTwo := uy_arg_lt hq.1 hy1
    obtain ⟨d1, -, -, -, d2⟩ := vt_memTwo h.2.1 h.2.2.2 c1.1 hlt2
    refine ⟨⟨d1, by simp only [ev, map]; rw [d2]; exact c1.2⟩, ?_, ⟨a3, hy1⟩, fun _ => trivial,
      fun _ => trivial, fun _ _ _ => trivial⟩
    simp only [ev, map]; rw [pi_vt_two h c1 hlt2, c2, g2, a2]
  | _, .thg m G r, hw, hl, hq => by
    obtain ⟨a1, a2, a3, -⟩ := uyUpB h hκσ r hw.2.1 hl.2 hq.2
    have hy1 := unUp_lt_Om1 h a1 a2 hw.2.2.r1
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := uyUpB h hκσ G hw.1 hl.1 hq.1
    obtain ⟨c1, c2⟩ := pi_add h g1 a1
    have hlt2 := Uk.arg_lt2 (ev_lt_Er _ g3) hy1
    obtain ⟨d1, -, -, -, d2⟩ := vt_memTwo h.2.1 h.2.2.2 c1.1 hlt2
    have hVT : vt τ (ev τ (G.map (up σ τ)) + ev τ (r.map (up σ τ))) ∈ TB τ σ := ⟨d1, by
      show ((Par τ (vt τ (ev τ (G.map (up σ τ)) + ev τ (r.map (up σ τ)))) : Set Ordinal.{0})) ⊆ Set.Iio σ
      rw [d2]; exact c1.2⟩
    have hpv : pi σ τ (vt τ (ev τ (G.map (up σ τ)) + ev τ (r.map (up σ τ)))) = vt σ (ev σ G + ev σ r) := by
      rw [pi_vt_two h c1 hlt2, c2, g2, a2]
    refine ⟨hVT, by simp only [ev, map]; exact hpv, ⟨g3, a3, ?_⟩, fun _ => trivial, fun _ => trivial,
      fun _ _ _ => trivial⟩
    refine ⟨hy1, (Gs_map _ G).2 hw.2.2.gs, NfM_imp g4 g5 m hw.2.2.nf,
      HdD_map m G (Lv_mono (fun p hp => ⟨fun hσp => up_ge h hp hσp, fun hpσ => by
        rw [up_lt h hpσ]; exact hpσ.trans h.2.2.1⟩) G hl.1) hw.2.2.hd, c1.1, ?_, ?_⟩
    · have hb := hw.2.2.bd
      rw [← hpv] at hb
      exact g6 _ hVT hb
    · have hb := hw.2.2.rb
      rw [← hpv, ← a2] at hb
      by_contra hge
      have := ((pi_bijOn h).2.le_iff_le hVT a1).2 (not_lt.1 hge)
      exact absurd hb (not_lt.2 this)
  | _, .lf c, hw, hl, hq => by
    obtain ⟨a1, a2, a3, -⟩ := uyUpB h hκσ c hw.1 hl hq
    refine ⟨a1, a2, ⟨a3, unUp_lt_Om1 h a1 a2 hw.2⟩, fun _ => trivial, fun _ => trivial, fun V hV hc => ?_⟩
    show ev τ (c.map (up σ τ)) < V
    have hc' : ev σ c < pi σ τ V := hc
    rw [← a2] at hc'
    by_contra hge
    have := ((pi_bijOn h).2.le_iff_le hV a1).2 (not_lt.1 hge)
    exact absurd hc' (not_lt.2 this)
  | _, .om b, hw, hl, hq => by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := uyUpB h hκσ b hw hl hq
    have hbE := ev_lt_Er _ a3
    obtain ⟨o1, o2⟩ := siOm1_opow_TB h hbE
    refine ⟨o1.2 a1, ?_, a3, a4, a5, a6⟩
    simp only [ev, map] at o2 ⊢; rw [o2 a1, a2]
  | _, .ad x y, hw, hl, hq => by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := uyUpB h hκσ x hw.1 hl.1 hq.1
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := uyUpB h hκσ y hw.2 hl.2 hq.2
    obtain ⟨c1, c2⟩ := pi_add h a1 b1
    have hω : ev σ y < ev σ x * ω → ev τ (y.map (up σ τ)) < ev τ (x.map (up σ τ)) * ω := by
      intro hlt; rw [← a2, ← b2] at hlt; exact (unPi_lt_mul_omega_iff h a1 b1).2 hlt
    refine ⟨c1, ?_, ⟨a3, b3⟩, fun hb => ⟨a4 hb.1, (IsOm_map _ x).2 hb.2.1, hω hb.2.2⟩,
      fun hb => ⟨a5 hb.1, b5 hb.2.1, (IsOm_map _ x).2 hb.2.2.1, hω hb.2.2.2⟩,
      fun V hV hc => ⟨a6 V hV hc.1, b6 V hV hc.2⟩⟩
    simp only [ev, map] at c2 ⊢; rw [c2, a2, b2]

/-- **The inverse base change on terms.** -/
theorem uyUp {κ σ τ : Ordinal.{0}} (h : Bases σ τ) (hκσ : κ ≤ σ) (t : UnT false) (hw : WFr σ t)
    (hl : Lv (· ∈ Tset σ) t) (hq : QsY κ t) :
    ev τ (t.map (up σ τ)) ∈ TB τ σ ∧ pi σ τ (ev τ (t.map (up σ τ))) = ev σ t ∧ WFr τ (t.map (up σ τ)) := by
  obtain ⟨a1, a2, a3, -⟩ := uyUpB h hκσ t hw hl hq
  exact ⟨a1, a2, a3⟩

/-- `π_{σ,τ}⁻¹(t[σ; p]) = t[τ; π⁻¹ p]`. -/
theorem uyUp_eq {κ σ τ : Ordinal.{0}} (h : Bases σ τ) (hκσ : κ ≤ σ) (t : UnT false) (hw : WFr σ t)
    (hl : Lv (· ∈ Tset σ) t) (hq : QsY κ t) :
    up σ τ (ev σ t) = ev τ (t.map (up σ τ)) ∧ WFr τ (t.map (up σ τ)) := by
  obtain ⟨a1, a2, a3⟩ := uyUp h hκσ t hw hl hq
  exact ⟨by rw [← a2]; exact up_pi h a1, a3⟩

/-- **The segment move on terms**: `mv b c (t[b; p]) = t[c; mv b c p]`. -/
theorem uyMv {κ b c : Ordinal.{0}} (hb : InE b) (hb1 : b < Om1) (hc : InE c) (hc1 : c < Om1) (hκb : κ ≤ b)
    (hκc : κ ≤ c) (t : UnT false) (hq : QsY κ t) (hw : WFr b t) (hl : Lv (· ∈ TB b κ) t) :
    mv b c (ev b t) = ev c (t.map (mv b c)) ∧ WFr c (t.map (mv b c)) := by
  rcases lt_trichotomy c b with hcb | rfl | hbc
  · have hmv : mv b c = pi c b := by unfold mv; rw [if_pos hcb]
    have hB : Bases c b := ⟨hc, hb, hcb, hb1⟩
    obtain ⟨-, a2, a3⟩ := uyDown hB hκc t hw (Lv_mono (fun p hp => Ub.ub_TB_mono hκc hp) t hl) hq
    rw [hmv]; exact ⟨a2, a3⟩
  · have hmv : mv c c = id := by unfold mv; simp
    rw [hmv, map_id]; exact ⟨rfl, hw⟩
  · have hmv : mv b c = up b c := by unfold mv; rw [if_neg (not_lt.2 hbc.le), if_pos hbc]
    have hB : Bases b c := ⟨hb, hc, hbc, hc1⟩
    rw [hmv]
    exact uyUp_eq hB hκb t hw (Lv_mono (fun p hp => hp.1) t hl) hq

/-! ## The translations of [W07a] Def 6.2 -/


/-- **`t^α_τ` on terms of both sorts** ([W07a] Def 6.2, Lemma 6.3 through `R2.vt_wbar`, `Uy.uyVt_tr` (i) and
`R2.ukVt_tr3` (i), whose condition `α ≤ rjDat Γ` is `uyDatM` at `α`). -/
theorem uyTrAB {κ τ : Ordinal.{0}} (hB : Bases κ τ) {n : ℕ} (hn : 1 ≤ n) :
    ∀ {k : Bool} (t : UnT k), QsY κ t → Lv (· ∈ Tset (Dl τ n)) t → WFr (Dl τ n) t → Nd (Dl τ n) (· < Dp τ n) t →
      WFr τ (trr (Dl τ n) t) ∧ ev τ (trr (Dl τ n) t) = ev (Dl τ n) t ∧
      (HbS (Dl τ n) t → HbS τ (trr (Dl τ n) t)) ∧ (FNF (Dl τ n) t → FNF τ (trr (Dl τ n) t)) ∧
      (∀ V, Lf (fun c => ev τ c < V) (trr (Dl τ n) t) ↔ Lf (fun c => ev (Dl τ n) c < V) t)
  | _, .par _, _, _, _, _ => ⟨trivial, rfl, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
  | _, .add s t, hq, hl, hw, hd => by
    obtain ⟨a1, a2, -⟩ := uyTrAB hB hn s hq.1 hl.1 hw.1 hd.1
    obtain ⟨b1, b2, -⟩ := uyTrAB hB hn t hq.2 hl.2 hw.2 hd.2
    refine ⟨⟨a1, b1⟩, ?_, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
    simp only [trr, ev]; rw [a2, b2]
  | _, .base, _, _, _, _ => ⟨trivial, rfl, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
  | _, .th1 s, hq, hl, hw, hd => by
    obtain ⟨a1, a2, -⟩ := uyTrAB hB hn s hq hl hw.1 hd
    obtain ⟨hτα, hαE, -⟩ := Dl_E hB.2.1 hB.2.2.2 hn
    have hα1 : Dl τ n < Om1 := (Dl_spec hB.2.1 hB.2.2.2 n).2.1
    have hab : τ + Dl τ n = Dl τ n :=
      add_of_omega0_opow_le (show τ < ω ^ Dl τ n by rw [hαE]; exact hτα) (le_of_eq hαE)
    have hlt : Dl τ n + ev (Dl τ n) s < Om1 := Om1_add_lt hα1 hw.2
    refine ⟨⟨⟨trivial, a1⟩, ?_⟩, ?_, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
    · simp only [ev]; rw [a2]; exact hlt
    · simp only [trr, ev]
      rw [a2, vt_wbar hB.2.1 hB.2.2.2 hlt, vt_wbar hαE hα1 hw.2, ← add_assoc, hab]
  | _, .thc q r, hq, hl, hw, hd => by
    obtain ⟨a1, a2, -⟩ := uyTrAB hB hn r hq.2 hl hw.1 hd.2
    obtain ⟨hτα, hαE, -⟩ := Dl_E hB.2.1 hB.2.2.2 hn
    have hα1 : Dl τ n < Om1 := (Dl_spec hB.2.1 hB.2.2.2 n).2.1
    have hBα : Bases κ (Dl τ n) := ⟨hB.1, hαE, hB.2.2.1.trans hτα, hα1⟩
    have hlt : Dl τ n + ev (Dl τ n) r < Om1 := Om1_add_lt hα1 hw.2
    have hrT := uyMem hBα r hl hw.1 hq.2
    have hargT := (uy_arg_T hBα hq.1 hrT hw.2).1
    have e := (uyVt_tr hB hn hq.1 hw.2).1 hargT hd.1
    refine ⟨⟨⟨trivial, a1⟩, ?_⟩, ?_, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
    · simp only [ev]; rw [a2]; exact hlt
    · simp only [trr, ev]; rw [a2, e]
  | _, .thg m G r, hq, hl, hw, hd => by
    obtain ⟨a1, a2, -⟩ := uyTrAB hB hn r hq.2 hl.2 hw.2.1 hd.2.2
    obtain ⟨l1, l2, l4, l5, l6⟩ := uyTrAB hB hn G hq.1 hl.1 hw.1 hd.2.1
    obtain ⟨hτα, hαE, -⟩ := Dl_E hB.2.1 hB.2.2.2 hn
    have hα1 : Dl τ n < Om1 := (Dl_spec hB.2.1 hB.2.2.2 n).2.1
    have hBα : Bases κ (Dl τ n) := ⟨hB.1, hαE, hB.2.2.1.trans hτα, hα1⟩
    obtain ⟨M, hM, hM1⟩ := UnT.ev_dvd (τ := Dl τ n) G hw.2.2.gs
    have hME : Om1 * M < Gg.ggE := hM ▸ ev_lt_Er G hw.1
    have hmem := hw.2.2.mem
    have hlt : vt (Dl τ n) (ev (Dl τ n) G + ev (Dl τ n) r) < Dp τ n := hd.1
    rw [hM] at hmem hlt
    by_cases hLo : LoL (Dl τ n) G
    · -- a low level over `α`: the subcase `Γ^* < α`, `α` is inserted (`R2.urVt_tr2` (i))
      have hm : m = true := HdD_lo hw.2.2.hd hLo
      subst hm
      have hdat : Rj.rjDat (Om1 * M) < Dl τ n := by
        rw [← hM]; exact urDatLo (InE.pos hαE) G hw.1 hw.2.2.nf hLo
      obtain ⟨m1, e1⟩ := (urVt_tr2 hB.2.1 hB.2.2.2 hn hM1 hME hdat hw.2.2.r1).1 hmem hlt
      rw [trr_thg_lo hLo]
      have hev : ev τ (trr (Dl τ n) G) + ev τ (UnT.add (.par (Dl τ n)) (trr (Dl τ n) r)) =
          Om1 * M + (Dl τ n + ev (Dl τ n) r) := by
        simp only [ev]; rw [l2, a2, hM]
      have hρα : Dl τ n + ev (Dl τ n) r < Om1 := Om1_add_lt hα1 hw.2.2.r1
      have h1M : Om1 ≤ Om1 * M := by
        have := mul_le_mul_right hM1 Om1
        rwa [mul_one] at this
      have hlt2 : Om1 * M + ev (Dl τ n) r < OmTwo := Uk.arg_lt2 hME hw.2.2.r1
      obtain ⟨hαV, hVE⟩ := (vt_E_iff hαE hα1 hmem hlt2).2 (h1M.trans le_self_add)
      have hrb0 : ev (Dl τ n) r < vt (Dl τ n) (Om1 * M + ev (Dl τ n) r) := by
        have := hw.2.2.rb; rw [hM] at this; exact this
      have hrb : Dl τ n + ev (Dl τ n) r < vt (Dl τ n) (Om1 * M + ev (Dl τ n) r) := hVE.add_lt hαV hrb0
      refine ⟨⟨l1, ⟨trivial, a1⟩, ⟨?_, (Gs_trr _ G).2 hw.2.2.gs, l5 hw.2.2.nf, ?_, by rw [hev]; exact m1, ?_,
        ?_⟩⟩, ?_, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
      · show Dl τ n + ev τ (trr (Dl τ n) r) < Om1
        rw [a2]; exact hρα
      · rw [trr_LoL G hLo]
        rcases LoL_split (τ := τ) G hLo with h' | h'
        · exact Or.inl h'
        · exact Or.inr ⟨rfl, h'⟩
      · rw [hev, ← e1, l6, ← hM]; exact hw.2.2.bd
      · rw [hev, ← e1]
        show Dl τ n + ev τ (trr (Dl τ n) r) < _
        rw [a2]; exact hrb
      · simp only [ev]; rw [l2, a2, hM]; exact e1.symm
    · -- a high level over `α`: the subcase `Γ^* ≥ α` (`R2.ukVt_tr3` (i))
      have hHd : HdM m (Dl τ n) G := HdD_hi hw.2.2.hd hLo
      have hdat := (uyDatM hBα m G hl.1 hw.1 hq.1 hw.2.2.nf hHd).1
      rw [hM] at hdat
      obtain ⟨m1, e1⟩ := (ukVt_tr3 hB.2.1 hB.2.2.2 hn hM1 hME hdat hw.2.2.r1).1 hmem hlt
      rw [trr_thg_hi hLo]
      have hev : ev τ (trr (Dl τ n) G) + ev τ (trr (Dl τ n) r) = Om1 * M + ev (Dl τ n) r := by
        rw [l2, a2, hM]
      refine ⟨⟨l1, a1, ⟨by rw [a2]; exact hw.2.2.r1, (Gs_trr _ G).2 hw.2.2.gs, NfM_imp l4 l5 m hw.2.2.nf,
        Or.inl (HdM_trr hτα.le m G hHd), by rw [hev]; exact m1, ?_, ?_⟩⟩, ?_, fun _ => trivial, fun _ => trivial,
        fun _ => Iff.rfl⟩
      · rw [hev, ← e1, l6, ← hM]; exact hw.2.2.bd
      · rw [hev, ← e1, a2, ← hM]; exact hw.2.2.rb
      · simp only [ev]; rw [hev, ← e1, hM]
  | _, .lf c, hq, hl, hw, hd => by
    obtain ⟨a1, a2, -⟩ := uyTrAB hB hn c hq hl hw.1 hd
    refine ⟨⟨a1, by rw [a2]; exact hw.2⟩, a2, fun _ => trivial, fun _ => trivial, fun V => ?_⟩
    show ev τ (trr (Dl τ n) c) < V ↔ ev (Dl τ n) c < V
    rw [a2]
  | _, .om b, hq, hl, hw, hd => by
    obtain ⟨a1, a2, a4, a5, a6⟩ := uyTrAB hB hn b hq hl hw hd
    refine ⟨a1, ?_, a4, a5, a6⟩
    simp only [trr, ev]; rw [a2]
  | _, .ad x y, hq, hl, hw, hd => by
    obtain ⟨a1, a2, a4, a5, a6⟩ := uyTrAB hB hn x hq.1 hl.1 hw.1 hd.1
    obtain ⟨b1, b2, b4, b5, b6⟩ := uyTrAB hB hn y hq.2 hl.2 hw.2 hd.2
    refine ⟨⟨a1, b1⟩, ?_, fun hb => ⟨a4 hb.1, (IsOm_trr _ x).2 hb.2.1, by rw [a2, b2]; exact hb.2.2⟩,
      fun hb => ⟨a5 hb.1, b5 hb.2.1, (IsOm_trr _ x).2 hb.2.2.1, by rw [a2, b2]; exact hb.2.2.2⟩,
      fun V => and_congr (a6 V) (b6 V)⟩
    simp only [trr, ev]; rw [a2, b2]

/-- **`t^α_τ` is correct** (`α = Dl τ n`, `n ≥ 1`): `trr α t` has the argument bounds and node conditions over `τ`
and `(trr α t)[τ] = t[α]`. -/
theorem uyTrA {κ τ : Ordinal.{0}} (hB : Bases κ τ) {n : ℕ} (hn : 1 ≤ n) (t : UnT false) (hq : QsY κ t)
    (hl : Lv (· ∈ Tset (Dl τ n)) t) (hw : WFr (Dl τ n) t) (hd : Nd (Dl τ n) (· < Dp τ n) t) :
    WFr τ (trr (Dl τ n) t) ∧ ev τ (trr (Dl τ n) t) = ev (Dl τ n) t := by
  obtain ⟨a1, a2, -⟩ := uyTrAB hB hn t hq hl hw hd
  exact ⟨a1, a2⟩

/-- **`t^τ_α` on terms of both sorts** ([W07a] Def 6.2, Lemma 6.3 through `R2.vt_wbar`, `Uy.uyVt_tr` (ii) and
`R2.ukVt_tr3` (ii)); the syntactic mode conditions over `α` (`HdDA α t`) and the parameters in `T^α` give the
decision `Γ^{*α} ≥ α`. -/
theorem uyTrBB {κ τ : Ordinal.{0}} (hB : Bases κ τ) {n : ℕ} (hn : 1 ≤ n) :
    ∀ {k : Bool} (t : UnT k), QsY κ t → Lv (· ∈ Tset τ) (trr (Dl τ n) t) → WFr τ (trr (Dl τ n) t) →
      Nd τ (· < Dp τ n) (trr (Dl τ n) t) → HdDA (Dl τ n) t → Lv (· ∈ Tset (Dl τ n)) t →
      WFr (Dl τ n) t ∧ ev τ (trr (Dl τ n) t) = ev (Dl τ n) t ∧
      (HbS τ (trr (Dl τ n) t) → HbS (Dl τ n) t) ∧ (FNF τ (trr (Dl τ n) t) → FNF (Dl τ n) t) ∧
      (∀ V, Lf (fun c => ev τ c < V) (trr (Dl τ n) t) ↔ Lf (fun c => ev (Dl τ n) c < V) t)
  | _, .par _, _, _, _, _, _, _ => ⟨trivial, rfl, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
  | _, .add s t, hq, hl, hw, hd, hh, hla => by
    obtain ⟨a1, a2, -⟩ := uyTrBB hB hn s hq.1 hl.1 hw.1 hd.1 hh.1 hla.1
    obtain ⟨b1, b2, -⟩ := uyTrBB hB hn t hq.2 hl.2 hw.2 hd.2 hh.2 hla.2
    refine ⟨⟨a1, b1⟩, ?_, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
    simp only [trr, ev]; rw [a2, b2]
  | _, .base, _, _, _, _, _, _ => ⟨trivial, rfl, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
  | _, .th1 s, hq, hl, hw, hd, hh, hla => by
    obtain ⟨a1, a2, -⟩ := uyTrBB hB hn s hq hl.2 hw.1.2 hd.2 hh hla
    obtain ⟨hτα, hαE, -⟩ := Dl_E hB.2.1 hB.2.2.2 hn
    have hα1 : Dl τ n < Om1 := (Dl_spec hB.2.1 hB.2.2.2 n).2.1
    have hab : τ + Dl τ n = Dl τ n :=
      add_of_omega0_opow_le (show τ < ω ^ Dl τ n by rw [hαE]; exact hτα) (le_of_eq hαE)
    have h2 := hw.2
    simp only [ev] at h2; rw [a2] at h2
    have hs1 : ev (Dl τ n) s < Om1 := lt_of_le_of_lt le_add_self h2
    refine ⟨⟨a1, hs1⟩, ?_, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
    simp only [trr, ev]
    rw [a2, vt_wbar hB.2.1 hB.2.2.2 h2, vt_wbar hαE hα1 hs1, ← add_assoc, hab]
  | _, .thc q r, hq, hl, hw, hd, hh, hla => by
    obtain ⟨a1, a2, -⟩ := uyTrBB hB hn r hq.2 hl.2 hw.1.2 hd.2.2 hh hla
    have h2 := hw.2
    simp only [ev] at h2
    have hr1 : ev (Dl τ n) r < Om1 := by rw [← a2]; exact lt_of_le_of_lt le_add_self h2
    have hαT : Dl τ n ∈ Tset τ := (Dl_spec hB.2.1 hB.2.2.2 n).1
    have hrT : ev τ (trr (Dl τ n) r) ∈ Tset τ := uyMem hB _ hl.2 hw.1.2 (qsY_trr _ r hq.2)
    have hsT : Dl τ n + ev τ (trr (Dl τ n) r) ∈ Tset τ := vzT_add hB.2.1 hB.2.2.2 hαT hrT
    have hargT := (uy_arg_T hB hq.1 hsT h2).1
    have hd1 := hd.1
    simp only [ev] at hd1
    rw [a2] at hargT hd1
    have e := (uyVt_tr hB hn hq.1 hr1).2 hargT hd1
    refine ⟨⟨a1, hr1⟩, ?_, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
    simp only [trr, ev]; rw [a2, e]
  | _, .thg m G r, hq, hl, hw, hd, hh, hla => by
    obtain ⟨hτα, hαE, -⟩ := Dl_E hB.2.1 hB.2.2.2 hn
    have hα1 : Dl τ n < Om1 := (Dl_spec hB.2.1 hB.2.2.2 n).2.1
    have hBα : Bases κ (Dl τ n) := ⟨hB.1, hαE, hB.2.2.1.trans hτα, hα1⟩
    by_cases hLo : LoL (Dl τ n) G
    · -- a low level over `α`: `R2.urVt_tr2` (ii)
      have hm : m = true := HdD_lo hh.1 hLo
      subst hm
      rw [trr_thg_lo hLo] at hl hw hd ⊢
      obtain ⟨a1, a2, -⟩ := uyTrBB hB hn r hq.2 hl.2.2 hw.2.1.2 hd.2.2.2 hh.2.2 hla.2
      obtain ⟨l1, l2, -, l5, l6⟩ := uyTrBB hB hn G hq.1 hl.1 hw.1 hd.2.1 hh.2.1 hla.1
      have hgs : Gs G := (Gs_trr _ G).1 hw.2.2.gs
      have hnf : FNF (Dl τ n) G := l5 hw.2.2.nf
      obtain ⟨M, hM, hM1⟩ := UnT.ev_dvd (τ := Dl τ n) G hgs
      have hME : Om1 * M < Gg.ggE := hM ▸ ev_lt_Er G l1
      have hdat : Rj.rjDat (Om1 * M) < Dl τ n := by
        rw [← hM]; exact urDatLo (InE.pos hαE) G l1 hnf hLo
      have hr1' : Dl τ n + ev (Dl τ n) r < Om1 := by
        have := hw.2.2.r1
        simp only [ev] at this; rwa [a2] at this
      have hr1 : ev (Dl τ n) r < Om1 := lt_of_le_of_lt le_add_self hr1'
      have hev : ev τ (trr (Dl τ n) G) + ev τ (UnT.add (.par (Dl τ n)) (trr (Dl τ n) r)) =
          Om1 * M + (Dl τ n + ev (Dl τ n) r) := by
        simp only [ev]; rw [l2, a2, hM]
      have hmem := hw.2.2.mem
      have hlt : vt τ (ev τ (trr (Dl τ n) G) + ev τ (UnT.add (.par (Dl τ n)) (trr (Dl τ n) r))) < Dp τ n := hd.1
      rw [hev] at hmem hlt
      obtain ⟨m1, e1⟩ := (urVt_tr2 hB.2.1 hB.2.2.2 hn hM1 hME hdat hr1).2 hmem hlt
      refine ⟨⟨l1, a1, ⟨hr1, hgs, hnf, hh.1, by rw [hM]; exact m1, ?_, ?_⟩⟩, ?_, fun _ => trivial,
        fun _ => trivial, fun _ => Iff.rfl⟩
      · rw [hM, ← e1, ← hev, ← l6]; exact hw.2.2.bd
      · rw [hM, ← e1, ← hev]
        refine lt_of_le_of_lt ?_ hw.2.2.rb
        show ev (Dl τ n) r ≤ Dl τ n + ev τ (trr (Dl τ n) r)
        rw [a2]; exact le_add_self
      · simp only [ev]; rw [l2, a2, hM]; exact e1
    · -- a high level over `α`: `R2.ukVt_tr3` (ii)
      have hHd : HdM m (Dl τ n) G := HdD_hi hh.1 hLo
      rw [trr_thg_hi hLo] at hl hw hd ⊢
      obtain ⟨a1, a2, -⟩ := uyTrBB hB hn r hq.2 hl.2 hw.2.1 hd.2.2 hh.2.2 hla.2
      obtain ⟨l1, l2, l4, l5, l6⟩ := uyTrBB hB hn G hq.1 hl.1 hw.1 hd.2.1 hh.2.1 hla.1
      have hgs : Gs G := (Gs_trr _ G).1 hw.2.2.gs
      have hnf : NfM m (Dl τ n) G := NfM_imp l4 l5 m hw.2.2.nf
      obtain ⟨M, hM, hM1⟩ := UnT.ev_dvd (τ := Dl τ n) G hgs
      have hdat := (uyDatM hBα m G hla.1 l1 hq.1 hnf hHd).1
      have hME : Om1 * M < Gg.ggE := hM ▸ ev_lt_Er G l1
      have hr1 : ev (Dl τ n) r < Om1 := by rw [← a2]; exact hw.2.2.r1
      have hev : ev τ (trr (Dl τ n) G) + ev τ (trr (Dl τ n) r) = Om1 * M + ev (Dl τ n) r := by
        rw [l2, a2, hM]
      have hmem := hw.2.2.mem
      have hlt : vt τ (ev τ (trr (Dl τ n) G) + ev τ (trr (Dl τ n) r)) < Dp τ n := hd.1
      rw [hev] at hmem hlt
      rw [hM] at hdat
      obtain ⟨m1, e1⟩ := (ukVt_tr3 hB.2.1 hB.2.2.2 hn hM1 hME hdat hr1).2 hmem hlt
      refine ⟨⟨l1, a1, ⟨hr1, hgs, hnf, hh.1, by rw [hM]; exact m1, ?_, ?_⟩⟩, ?_, fun _ => trivial,
        fun _ => trivial, fun _ => Iff.rfl⟩
      · rw [hM, ← e1, ← hev, ← l6]; exact hw.2.2.bd
      · rw [hM, ← e1, ← hev, ← a2]; exact hw.2.2.rb
      · simp only [ev]; rw [hev, e1, hM]
  | _, .lf c, hq, hl, hw, hd, hh, hla => by
    obtain ⟨a1, a2, -⟩ := uyTrBB hB hn c hq hl hw.1 hd hh hla
    have h2 : ev τ (trr (Dl τ n) c) < Om1 := hw.2
    refine ⟨⟨a1, a2 ▸ h2⟩, a2, fun _ => trivial, fun _ => trivial, fun V => ?_⟩
    show ev τ (trr (Dl τ n) c) < V ↔ ev (Dl τ n) c < V
    rw [a2]
  | _, .om b, hq, hl, hw, hd, hh, hla => by
    obtain ⟨a1, a2, a4, a5, a6⟩ := uyTrBB hB hn b hq hl hw hd hh hla
    refine ⟨a1, ?_, a4, a5, a6⟩
    simp only [trr, ev]; rw [a2]
  | _, .ad x y, hq, hl, hw, hd, hh, hla => by
    obtain ⟨a1, a2, a4, a5, a6⟩ := uyTrBB hB hn x hq.1 hl.1 hw.1 hd.1 hh.1 hla.1
    obtain ⟨b1, b2, b4, b5, b6⟩ := uyTrBB hB hn y hq.2 hl.2 hw.2 hd.2 hh.2 hla.2
    refine ⟨⟨a1, b1⟩, ?_, fun hb => ⟨a4 hb.1, (IsOm_trr _ x).1 hb.2.1, by rw [← a2, ← b2]; exact hb.2.2⟩,
      fun hb => ⟨a5 hb.1, b5 hb.2.1, (IsOm_trr _ x).1 hb.2.2.1, by rw [← a2, ← b2]; exact hb.2.2.2⟩,
      fun V => and_congr (a6 V) (b6 V)⟩
    simp only [trr, ev]; rw [a2, b2]

/-- **`t^τ_α` is correct** (`α = Dl τ n`, `n ≥ 1`): if `trr α t` has the argument bounds and node conditions over
`τ` with node values below `α⁺`, the syntactic mode conditions hold over `α` and the parameters of `t` lie in `T^α`,
then `t` has them over `α` and `(trr α t)[τ] = t[α]`. -/
theorem uyTrB {κ τ : Ordinal.{0}} (hB : Bases κ τ) {n : ℕ} (hn : 1 ≤ n) (t : UnT false) (hq : QsY κ t)
    (hl : Lv (· ∈ Tset τ) (trr (Dl τ n) t)) (hw : WFr τ (trr (Dl τ n) t)) (hd : Nd τ (· < Dp τ n) (trr (Dl τ n) t))
    (hh : HdDA (Dl τ n) t) (hla : Lv (· ∈ Tset (Dl τ n)) t) :
    WFr (Dl τ n) t ∧ ev τ (trr (Dl τ n) t) = ev (Dl τ n) t := by
  obtain ⟨a1, a2, -⟩ := uyTrBB hB hn t hq hl hw hd hh hla
  exact ⟨a1, a2⟩



end Googology.Trans.PoR.InaccPsi.R2.Uy

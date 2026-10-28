import Googology.Trans.PoR.InaccPsi.R2.UyExist
import Googology.Trans.PoR.InaccPsi.R2.VlReal

/-!
# Term existence from ordinal decompositions with the node `thz G r` (levels with moving leaves)

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`Uy.uyExist` with one more clause: **`thz`**, `ϑᵗ(Ω₁·q + r)` at a level `Ω₁·q < B₂` whose countable leaves lie in a
finite set `Lq` of points `p ≤ τ` with `P p` (the node conditions `Vi.Nz τ q r` asked).  The level terms of the
`thg`/`thl`-clauses keep the leaves of `Uy.UyGd`.

* `VlGd` (**a decomposition by ordinal data with gap levels, constant levels, and levels with moving leaves**),
  `vlExist` (**every `y` with `VlGd κ τ P y` is the value of a term with the node conditions `Vi.ZW`, parameters `P`,
  level leaves in a finite set of points `P`, or below every `ε`-number above a finite set of data `< κ`**),
  `vlGd_of_uy` (**`Uy.UyGd ⇒ VlGd`**).

New definition: `VlGd`.  No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vl

open Ordinal Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Uh Googology.Trans.PoR.InaccPsi.R2.Un
  Googology.Trans.PoR.InaccPsi.R2.Un.UnT
open Googology.Trans.PoR.InaccPsi.R2.Ur Googology.Trans.PoR.InaccPsi.R2.Uy Googology.Trans.PoR.InaccPsi.R2.Vi
  Googology.Trans.PoR.InaccPsi.R2.Vc

/-- **A decomposition of `y` over `τ` by ordinal data with levels with moving leaves**: the clauses of `Uy.UyGd`
(the leaves of the level of a `thg`/`thl`-clause decomposed by `Uy.UyGd`) and **`thz`**: `ϑᵗ(Ω₁·q + r)` with the node
conditions `Vi.Nz τ q r`, `r < Ω₁`, and every leaf of `Ω₁·q` in a finite set `Lq` of points `p ≤ τ` with `P p`. -/
inductive VlGd (κ τ : Ordinal.{0}) (P : Ordinal.{0} → Prop) : Ordinal.{0} → Prop
  | par {p : Ordinal.{0}} : p < τ → P p → VlGd κ τ P p
  | base : VlGd κ τ P τ
  | add {a b : Ordinal.{0}} : VlGd κ τ P a → VlGd κ τ P b → (τ ≤ a + b → τ ≤ a) → VlGd κ τ P (a + b)
  | th1 {s : Ordinal.{0}} : s < Om1 → VlGd κ τ P s → VlGd κ τ P (vt τ (1 + s))
  | thc {q r : Ordinal.{0}} : UyLev κ q → r < Om1 → VlGd κ τ P r → VlGd κ τ P (vt τ (Om1 * q + r))
  | thz {q r : Ordinal.{0}} (Lq : Finset Ordinal.{0}) : Nz τ q r → r < Om1 → VcLv (· ∈ Lq) (Om1 * q) →
      (∀ p ∈ Lq, p ≤ τ ∧ P p) → VlGd κ τ P r → VlGd κ τ P (vt τ (Om1 * q + r))
  | thg {M r : Ordinal.{0}} : 1 ≤ M → Om1 * M < Gg.ggE → (Om1 ≤ M ∨ (M < Om1 ∧ M ∈ Tset τ)) →
      τ ≤ Rj.rjDat (Om1 * M) → Om1 * M + r ∈ Tset τ → r < Om1 → VlGd κ τ P r →
      (∀ c, UnLeaf (Om1 * M) c → UyGd κ τ P c) → VlGd κ τ P (vt τ (Om1 * M + r))
  | thl {M r : Ordinal.{0}} : 1 ≤ M → Om1 * M < Gg.ggE → (Om1 ≤ M ∨ M < τ) → Om1 * M + r ∈ Tset τ → r < Om1 →
      VlGd κ τ P r → (∀ c, UnLeaf (Om1 * M) c → c < τ ∧ P c) → VlGd κ τ P (vt τ (Om1 * M + r))

/-- The level leaves of a level term of `Uy.QsY κ` lie below every `ε`-number above its level data. -/
theorem vl_ZL_lvq {κ : Ordinal.{0}} {k : Bool} (G : UnT k) (hG : QsY κ G) (Lf : Finset Ordinal.{0}) :
    ∀ e, InE e → (∀ d ∈ lvqY G, d < e) → ZL (fun p => p ∈ Lf ∨ p < e) G := fun _ he hd =>
  vl_ZL_mono (fun _ _ hp => Or.inr hp) G (vl_ZL_of_qsY he G (QsY_of_lvqY G hG hd))

/-- **Term existence with moving level leaves**: every `y` with `VlGd κ τ P y` is the value over `τ` of a term of
`Un.UnT` with the argument bounds `Ur.WFr` and the node conditions `Vi.ZW`, parameters `P` in `Tᵗ`, level leaves in a
finite set `Lf` of points `p ≤ τ` with `P p` or below every `ε`-number above a finite set `Dq` of data `< κ`, and a
high head when `τ ≤ y`. -/
theorem vlExist {κ τ : Ordinal.{0}} (hB : Bases κ τ) {P : Ordinal.{0} → Prop} {y : Ordinal.{0}}
    (h : VlGd κ τ P y) :
    ∃ t : UnT false, ∃ Lf Dq : Finset Ordinal.{0}, ev τ t = y ∧ WFr τ t ∧ ZW τ t ∧ Lv P t ∧
      Lv (· ∈ Tset τ) t ∧ (∀ p ∈ Lf, p ≤ τ ∧ P p) ∧ (∀ d ∈ Dq, d < κ) ∧
      (∀ e, InE e → (∀ d ∈ Dq, d < e) → ZL (fun p => p ∈ Lf ∨ p < e) t) ∧ (τ ≤ y → HiC τ t) := by
  classical
  have hτ := hB.2.1
  have hτ1 := hB.2.2.2
  induction h with
  | @par p hp hP =>
    exact ⟨.par p, ∅, ∅, rfl, trivial, trivial, hP, uh_T_le hτ hτ1 hp.le, by simp, by simp,
      fun _ _ _ => trivial, fun h => h⟩
  | base => exact ⟨.base, ∅, ∅, rfl, trivial, trivial, trivial, trivial, by simp, by simp,
      fun _ _ _ => trivial, fun _ => trivial⟩
  | @add a b _ _ hab iha ihb =>
    obtain ⟨ta, La, Da, ea, wa, za, la, lTa, hLa, hDa, hZa, ha⟩ := iha
    obtain ⟨tb, Lb, Db, eb, wb, zb, lb, lTb, hLb, hDb, hZb, -⟩ := ihb
    refine ⟨.add ta tb, La ∪ Lb, Da ∪ Db, by show ev τ ta + ev τ tb = _; rw [ea, eb], ⟨wa, wb⟩, ⟨za, zb⟩,
      ⟨la, lb⟩, ⟨lTa, lTb⟩, fun p hp => ?_, fun d hd => ?_, fun e he hd => ?_, fun h => ha (hab h)⟩
    · rcases Finset.mem_union.1 hp with hp | hp
      · exact hLa p hp
      · exact hLb p hp
    · rcases Finset.mem_union.1 hd with hd | hd
      · exact hDa d hd
      · exact hDb d hd
    · exact ⟨vl_ZL_mono (fun p _ hp => hp.imp (fun h => Finset.mem_union_left _ h) id) ta
        (hZa e he fun d hd' => hd d (Finset.mem_union_left _ hd')),
        vl_ZL_mono (fun p _ hp => hp.imp (fun h => Finset.mem_union_right _ h) id) tb
        (hZb e he fun d hd' => hd d (Finset.mem_union_right _ hd'))⟩
  | @th1 s hs _ ih =>
    obtain ⟨ts, Ls, Ds, es, ws, zs, ls, lTs, hLs, hDs, hZs, -⟩ := ih
    exact ⟨.th1 ts, Ls, Ds, by show vt τ (1 + ev τ ts) = _; rw [es], ⟨ws, es ▸ hs⟩, zs, ls, lTs, hLs, hDs,
      hZs, fun _ => trivial⟩
  | @thc q r hq hr _ ih =>
    obtain ⟨tr, Lr, Dr, er, wr, zr, lr, lTr, hLr, hDr, hZr, -⟩ := ih
    have hr' : ev τ tr < Om1 := er ▸ hr
    have hrT : ev τ tr ∈ Tset τ := viMem hB tr lTr wr zr
    refine ⟨.thc q tr, Lr, insert (Uc.ucDat (Om1 * q)) Dr, by show vt τ (Om1 * q + ev τ tr) = _; rw [er],
      ⟨wr, hr'⟩, ⟨⟨hq.1, hq.2.1, (uy_Om1_mul_TB hB le_rfl hq).1.1, (uy_arg_T hB hq hrT hr').1,
        uyLt_vt_self hB hq hrT hr'⟩, zr⟩, lr, lTr, hLr, fun d hd => ?_, fun e he hd => ?_, fun _ => trivial⟩
    · rcases Finset.mem_insert.1 hd with rfl | hd
      · exact hq.2.2.2
      · exact hDr d hd
    · refine ⟨VcLv_mono (fun _ _ hp => Or.inr hp) _ ((Vc.vc_dat_lt he _ hq.2.1).2 (hd _ (Finset.mem_insert_self _ _))),
        hZr e he fun d hd' => hd d (Finset.mem_insert_of_mem hd')⟩
  | @thz q r Lq hz hr hL hLq _ ih =>
    obtain ⟨tr, Lr, Dr, er, wr, zr, lr, lTr, hLr, hDr, hZr, -⟩ := ih
    have hr' : ev τ tr < Om1 := er ▸ hr
    refine ⟨.thc q tr, Lq ∪ Lr, Dr, by show vt τ (Om1 * q + ev τ tr) = _; rw [er],
      ⟨wr, hr'⟩, ⟨by rw [er]; exact hz, zr⟩, lr, lTr, fun p hp => ?_, hDr, fun e he hd => ?_, fun _ => trivial⟩
    · rcases Finset.mem_union.1 hp with hp | hp
      · exact hLq p hp
      · exact hLr p hp
    · exact ⟨VcLv_mono (fun _ _ hp => Or.inl (Finset.mem_union_left _ hp)) _ hL,
        vl_ZL_mono (fun p _ hp => hp.imp (fun h => Finset.mem_union_right _ h) id) tr (hZr e he hd)⟩
  | @thg M r hM1 hME hMc hd hmem hr _ hc ihr =>
    obtain ⟨tr, Lr, Dr, er, wr, zr, lr, lTr, hLr, hDr, hZr, -⟩ := ihr
    obtain ⟨G, eG, wG, fG, qG, lG, lTG, hdG, gsG, -⟩ :=
      uyLevelEx (κ := κ) (InE.pos hτ) P (fun _ => True) (Om1 * M) hME
        (fun c hc' => (uyExist hB (hc c hc')).imp fun _ h =>
          ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, trivial⟩)
    have hM0 : Om1 * M ≠ 0 := (mul_pos Rj.rj_Om1_pos (lt_of_lt_of_le zero_lt_one hM1)).ne'
    have hgs : Gs G := gsG (dvd_mul_right _ _) hM0
    have hdE : HdE τ G := hdG hd
    have hr' : ev τ tr < Om1 := er ▸ hr
    have hmem' : ev τ G + ev τ tr ∈ Tset τ := by rw [eG, er]; exact hmem
    have hW : WFr τ (UnT.thg true G tr) := by
      rcases hMc with hM | ⟨hM, hMT⟩
      · exact uyNodeHi hτ hτ1 G tr wG wr hr' hgs fG hdE (by rw [eG]; exact mul_le_mul_right hM Om1) hmem'
      · exact uyNodeLo hB G tr wG lTG qG wr hr' hgs fG hdE eG hM hMT hmem'
    refine ⟨.thg true G tr, Lr, lvqY G ∪ Dr, by show vt τ (ev τ G + ev τ tr) = _; rw [eG, er], hW,
      ⟨vl_ZW_of_qsY hB G lTG wG qG, zr⟩, ⟨lG, lr⟩, ⟨lTG, lTr⟩, hLr, fun d hd' => ?_, fun e he hd' => ?_,
      fun _ => trivial⟩
    · rcases Finset.mem_union.1 hd' with hd' | hd'
      · exact lvqY_lt G qG d hd'
      · exact hDr d hd'
    · exact ⟨vl_ZL_lvq G qG Lr e he fun d h => hd' d (Finset.mem_union_left _ h),
        hZr e he fun d h => hd' d (Finset.mem_union_right _ h)⟩
  | @thl M r hM1 hME hMc hmem hr _ hlo ihr =>
    obtain ⟨tr, Lr, Dr, er, wr, zr, lr, lTr, hLr, hDr, hZr, -⟩ := ihr
    obtain ⟨G, eG, wG, fG, qG, lG, lTG, -, gsG, lfG⟩ :=
      uyLevelEx (κ := κ) (InE.pos hτ) P (fun t => ∃ p, t = .par p ∧ p < τ) (Om1 * M) hME
        (fun c hc => ⟨.par c, rfl, trivial, trivial, (hlo c hc).2, uh_T_le hτ hτ1 (hlo c hc).1.le,
          fun h => h, c, rfl, (hlo c hc).1⟩)
    have hM0 : Om1 * M ≠ 0 := (mul_pos Rj.rj_Om1_pos (lt_of_lt_of_le zero_lt_one hM1)).ne'
    have hgs : Gs G := gsG (dvd_mul_right _ _) hM0
    have hr' : ev τ tr < Om1 := er ▸ hr
    have hmem' : ev τ G + ev τ tr ∈ Tset τ := by rw [eG, er]; exact hmem
    have hW : WFr τ (UnT.thg true G tr) :=
      uyNodeLow hτ hτ1 G tr wG wr hr' hgs fG (LoL_of_LfY G lfG) eG hM1 hME hMc hmem'
    refine ⟨.thg true G tr, Lr, lvqY G ∪ Dr, by show vt τ (ev τ G + ev τ tr) = _; rw [eG, er], hW,
      ⟨vl_ZW_of_qsY hB G lTG wG qG, zr⟩, ⟨lG, lr⟩, ⟨lTG, lTr⟩, hLr, fun d hd' => ?_, fun e he hd' => ?_,
      fun _ => trivial⟩
    · rcases Finset.mem_union.1 hd' with hd' | hd'
      · exact lvqY_lt G qG d hd'
      · exact hDr d hd'
    · exact ⟨vl_ZL_lvq G qG Lr e he fun d h => hd' d (Finset.mem_union_left _ h),
        hZr e he fun d h => hd' d (Finset.mem_union_right _ h)⟩

/-- **`Uy.UyGd ⇒ VlGd`** (every clause of `Uy.UyGd` is a clause of `VlGd`). -/
theorem vlGd_of_uy {κ τ : Ordinal.{0}} {P : Ordinal.{0} → Prop} {y : Ordinal.{0}} (h : UyGd κ τ P y) :
    VlGd κ τ P y := by
  induction h with
  | par hp hP => exact .par hp hP
  | base => exact .base
  | add _ _ hab iha ihb => exact .add iha ihb hab
  | th1 hs _ ih => exact .th1 hs ih
  | thc hq hr _ ih => exact .thc hq hr ih
  | thg hM1 hME hMc hd hmem hr _ hc ihr _ => exact .thg hM1 hME hMc hd hmem hr ihr hc
  | thl hM1 hME hMc hmem hr _ hc ih => exact .thl hM1 hME hMc hmem hr ih hc

end Googology.Trans.PoR.InaccPsi.R2.Vl

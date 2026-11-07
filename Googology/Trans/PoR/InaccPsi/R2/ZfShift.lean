import Googology.Trans.PoR.InaccPsi.R2.ZfDCl

/-!
# `Yq.XoShift2` from the level image alone: the configuration enlarged by the leaves of its node levels

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`Yq.XoShift2 S` (skeleton leaf `skShift2`) asks one realizer `D` for a configuration `X ∪ Y` with the node clause
`Yq.XoThCl` at every restricted node whose points lie in `X ∪ Y`.  The shift `Za.zaShiftCore` gives `D(node)` at a node
whose level has its leaves in the configuration; a node's level leaves need not be points of its term
(`Zf.zfNodesAll_false` for the level `0`; the level `(Ω₁ + a) + b` has the leaf `a + b`).  The repair: call the shift
on the configuration ENLARGED by, for every `y ∈ Y` that is a node value `ϑ^{υ_{λ+h}}(ξ)`, the leaves of the level
`Ω₁·(ξ / Ω₁)` and the predecessor `ξ − 1` (level `0`), and by `ω`:

* the node value determines `h` (the segments are disjoint) and `ξ` (`Zf.zf_vt_inj`), so one finite set per `y`
  (`Zf.zf_yv_fin`) serves every term of `y`; the leaves lie below `υ_{λ+h+1} ≤ υ_{λ+β}` (`Zf.zf_lv_T`), so the
  enlarged configuration is admissible (`zf_enl`);
* every clause of the shift for the enlarged configuration gives the clause for `X ∪ Y` (`zf_lsMapW_mono` and
  monotonicity of the other clauses);
* `Zf.zfDCl` at the enlarged configuration, with the core points `X ∪ Y`, gives `Yq.XoThCl` for `X ∪ Y`;
* at a nested node level (`Zf.ZfNest`: a sum tree of `ϑ`-nodes of level `≥ 1`) the level image comes from the node
  clauses at its nodes (`ZfLevNode`, a statement proved as `Zk.zkLevNode`), and the nodes are smaller terms: `zfDCl`
  at them, by induction on the size (`xoSize`); their values and images are `ε`-numbers by `R2.vt_E_iff` (the term
  clause below `B₂`, `Za.ZaHiD` from `B₂` on).

What is left is the **level image** off the nested node levels (`Zf.ZfImgCl`): `ZfImg S` is `Yq.XoShift2` with `Za.ZaHiD` and `ZfImgCl` in place
of `XoThCl` (a statement; `Za.zaShiftCore` gives all of it but `ZfImgCl`).

* `ZfLevNode` (statement), `ZfImg` (statement), `zf_lsMapW_mono`, `zf_seg_unique`, `zf_enl` (**the enlargement**), `zfShift2`
  (**`ZfLevNode S ⇒ ZfImg S ⇒ Yq.XoShift2 S`**), `zfShiftXo` (`⇒ Yq.XoShift S`).

No new axiom.  New definitions: `ZfLevNode`, `ZfImg` (statements).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Lr Googology.Trans.PoR.InaccPsi.R2.Un
open Googology.Trans.PoR.InaccPsi.R2.Ur Googology.Trans.PoR.InaccPsi.R2.Vi Googology.Trans.PoR.InaccPsi.R2.Vl
  Googology.Trans.PoR.InaccPsi.R2.Xo Googology.Trans.PoR.InaccPsi.R2.Yq Googology.Trans.PoR.InaccPsi.R2.Yv

variable {S : InaccSeq.{0}}

/-- **The level image at a nested node level from the node clauses at its nodes** (statement, a lemma on the values:
`Zk.zkLevNode`): at a sum tree of nodes whose values are `ε`-numbers in a set `A` on which `D` is strictly increasing,
with images `ε`-numbers and `D(val) = img` at every node, `yvSub D (Ω₁·val) = Ω₁·img`. -/
def ZfLevNode (S : InaccSeq.{0}) : Prop :=
  ∀ (l μ : Ordinal.{0}) (f D : Ordinal.{0} → Ordinal.{0}) (A : Set Ordinal.{0}) (P : Ordinal.{0} → Prop),
    StrictMonoOn D A → D 0 = 0 → ∀ L : XoE,
    ZfNS (fun N => xoVal S l N < Om1 ∧ xoVal S l N ∈ A ∧ InE (xoVal S l N) ∧ InE (xoImg S l μ f N) ∧
      D (xoVal S l N) = xoImg S l μ f N) L →
    YvLv S P (Om1 * xoVal S l L) → yvSub S D (Om1 * xoVal S l L) = Om1 * xoImg S l μ f L

/-- **The shift with the moving-level clause and the level image** (statement): `Yq.XoShift2` with `Za.ZaHiD` and
`Zf.ZfImgCl` in place of `Yq.XoThCl`. -/
def ZfImg (S : InaccSeq.{0}) : Prop :=
  ∀ (l β : Ordinal.{0})
    (Q : Ordinal.{0} → (Ordinal.{0} → Ordinal.{0}) → Ordinal.{0} → Ordinal.{0} → Finset Ordinal.{0} → Prop),
    IsRestartIdx l → upsilon l < Om1 → upsilon l < nuC → upsilon (l + β) ≤ nuC →
    (∀ γ < upsilon l, ∀ Os : Finset Ordinal.{0}, (∀ d ∈ Os, d < β) →
      ∃ μ f B, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < upsilon l ∧ μ + B ≤ l ∧ ω ^ 2 ∣ B ∧
        upsilon (μ + B) ≤ cdR S μ ∧ Sl.SlOff f Os B ∧ Q μ f B γ Os) →
    Cx.CxStdPairTop S → upsilon l ≤ Nc.ncL S (ω + 1) →
    ∀ (X Y : Finset Ordinal.{0}), (∀ x ∈ X, x < upsilon l) → (∀ y ∈ Y, upsilon l ≤ y ∧ y < upsilon (l + β)) →
    ∃ D μ f B γ Os, (Q μ f B γ Os ∧ (∀ x ∈ X, x < γ) ∧ γ < upsilon μ ∧ Ls.LsMapW S l X Y D μ ∧
      (∀ g, upsilon (l + g) ∈ Y → g ∈ Os ∧ D (upsilon (l + g)) = upsilon (μ + f g)) ∧
      (∀ y ∈ Y, D y < upsilon (μ + B)) ∧
      (upsilon μ < upsilon l ∧ ∀ y ∈ Y, y < upsilon (succ l) → D y = pi (upsilon μ) (upsilon l) y) ∧
      (∀ y ∈ Y, ∀ g, upsilon (l + g) ≤ y → y < upsilon (succ (l + g)) →
        (∀ p ∈ Par (upsilon (l + g)) y, p < upsilon l) → D y = mv (upsilon (l + g)) (upsilon (μ + f g)) y) ∧
      (∀ y ∈ Y, ∀ g, upsilon (l + g) ≤ y → y < upsilon (succ (l + g)) → ∀ t : Ub.UbT, Ub.UbT.IsA t →
        Ub.UbT.WF (upsilon (l + g)) t → Ub.UbT.Lv (· ∈ X ∪ Y) t → Ub.UbT.ev (upsilon (l + g)) t = y →
        D y = Ub.UbT.ev (upsilon (μ + f g)) (t.map D) ∧ Ub.UbT.WF (upsilon (μ + f g)) (t.map D)) ∧
      (∀ y ∈ Y, ∀ g, upsilon (l + g) ≤ y → y < upsilon (succ (l + g)) → ∀ t : UnC, ZW (upsilon (l + g)) t →
        WFr (upsilon (l + g)) t → UnT.Lv (· ∈ X ∪ Y) t → ZL (fun p => p ∈ X ∪ Y ∨ p < γ) t →
        UnT.Lv (· ∈ Tset (upsilon (l + g))) t → ZL (· ∈ Tset (upsilon (l + g))) t →
        UnT.ev (upsilon (l + g)) t = y →
        D y = UnT.ev (upsilon (μ + f g)) (vmap D t) ∧ WFr (upsilon (μ + f g)) (vmap D t) ∧
          ZW (upsilon (μ + f g)) (vmap D t)) ∧
      VlLC (fun p => p ∈ X ∪ Y ∨ p < γ) D ∧ (∀ x, x < γ → D x = x) ∧ UpsPt γ) ∧
      Za.ZaHiD S l μ γ f D X Y ∧ ZfImgCl S l β μ γ f D X Y

/-- **The map clauses for a larger configuration give them for a smaller one.** -/
theorem zf_lsMapW_mono {l μ : Ordinal.{0}} {D : Ordinal.{0} → Ordinal.{0}} {X Y X' Y' : Finset Ordinal.{0}}
    (h : Ls.LsMapW S l X' Y' D μ) (hX : X ⊆ X') (hY : Y ⊆ Y') : Ls.LsMapW S l X Y D μ where
  fix := fun x hx => h.fix x (hX hx)
  mono := h.mono.mono (by
    intro z hz
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hz) with h1 | h1
    · exact Finset.mem_coe.2 (Finset.mem_union_left _ (hX h1))
    · exact Finset.mem_coe.2 (Finset.mem_union_right _ (hY h1)))
  add := fun x hx y hy z hz => h.add x (Finset.union_subset_union hX hY hx) y (Finset.union_subset_union hX hY hy) z
    (Finset.union_subset_union hX hY hz)
  indec := fun y hy => h.indec y (hY hy)
  above := fun y hy x hx => h.above y (hY hy) x (hX hx)
  below := fun y hy => h.below y (hY hy)
  rng := h.rng
  base := fun hb => h.base (hY hb)
  bd := fun y hy => h.bd y (hY hy)
  pair1 := fun y hy y' hy' => h.pair1 y (hY hy) y' (hY hy')
  pair2 := fun y hy y' hy' => h.pair2 y (hY hy) y' (hY hy')

/-- **The segment of a point is unique.** -/
theorem zf_seg_unique {l h h' y : Ordinal.{0}} (h1 : upsilon (l + h) ≤ y) (h2 : y < upsilon (succ (l + h)))
    (h1' : upsilon (l + h') ≤ y) (h2' : y < upsilon (succ (l + h'))) : h = h' := by
  have hm := upsilon_normal.strictMono
  rcases lt_trichotomy h h' with hlt | heq | hgt
  · have : upsilon (succ (l + h)) ≤ upsilon (l + h') :=
      hm.monotone (Order.succ_le_of_lt ((add_lt_add_iff_left l).2 hlt))
    exact absurd (this.trans h1') (not_le.2 h2)
  · exact heq
  · have : upsilon (succ (l + h')) ≤ upsilon (l + h) :=
      hm.monotone (Order.succ_le_of_lt ((add_lt_add_iff_left l).2 hgt))
    exact absurd (this.trans h1) (not_le.2 h2')

/-- The enlargement property of a finite set `Z` at a point `y`. -/
def ZfEnlAt (S : InaccSeq.{0}) (l b y : Ordinal.{0}) (Z : Finset Ordinal.{0}) : Prop :=
  ∀ h ξ, upsilon (l + h) ≤ y → y < upsilon (succ (l + h)) → ξ ∈ Tset (upsilon (l + h)) → ξ < OmTwo →
    vt (upsilon (l + h)) ξ = y →
    (Om1 ≤ ξ → YvLv S (fun p => p ∈ Z ∧ p < b) (Om1 * (ξ / Om1))) ∧ (1 ≤ ξ → ξ < Om1 → ξ - 1 ∈ Z ∧ ξ - 1 < b)

/-- **The enlargement**: a finite set `Z` below `b = υ_{λ+β}` containing, for every node value `y ∈ Y`, the leaves
of its level and the predecessor of its argument (level `0`). -/
theorem zf_enl (S : InaccSeq.{0}) {l β : Ordinal.{0}} (hl0 : 0 < l) (hb1 : upsilon (l + β) ≤ Om1)
    (Y : Finset Ordinal.{0}) (hYb : ∀ y ∈ Y, y < upsilon (l + β)) :
    ∃ Z : Finset Ordinal.{0}, (∀ z ∈ Z, z < upsilon (l + β)) ∧
      ∀ y ∈ Y, ZfEnlAt S l (upsilon (l + β)) y Z := by
  classical
  set b := upsilon (l + β) with hbdef
  have hm := upsilon_normal.strictMono
  have hmono : ∀ y (Z Z' : Finset Ordinal.{0}), Z ⊆ Z' → ZfEnlAt S l b y Z → ZfEnlAt S l b y Z' := by
    intro y Z Z' hZZ' hZ h ξ h1 h2 h3 h4 h5
    obtain ⟨hA, hB⟩ := hZ h ξ h1 h2 h3 h4 h5
    exact ⟨fun hξ => (hA hξ).mono fun p hp => ⟨hZZ' hp.1, hp.2⟩,
      fun hξ1 hξ2 => ⟨hZZ' (hB hξ1 hξ2).1, (hB hξ1 hξ2).2⟩⟩
  have hex : ∀ y ∈ (↑Y : Set Ordinal.{0}), ∃ Z, ZfEnlAt S l b y Z := by
    intro y hyY
    by_cases hd : ∃ h ξ, upsilon (l + h) ≤ y ∧ y < upsilon (succ (l + h)) ∧ ξ ∈ Tset (upsilon (l + h)) ∧
        ξ < OmTwo ∧ vt (upsilon (l + h)) ξ = y ∧ upsilon (succ (l + h)) ≤ b
    · obtain ⟨h0, ξ0, a1, a2, a3, a4, a5, a6⟩ := hd
      set τ := upsilon (l + h0) with hτdef
      have hτU : UpsPt τ := upsPt_upsilon (hl0.trans_le le_self_add)
      have hτE : InE τ := upsPt_inE hτU
      have hsU : UpsPt (upsilon (succ (l + h0))) :=
        upsPt_upsilon (hl0.trans_le (le_self_add.trans (Order.le_succ _)))
      have hτs : τ < upsilon (succ (l + h0)) := hm (Order.lt_succ _)
      have hτ1 : τ < Om1 := (hτs.trans_le a6).trans_le hb1
      have hO0 : (Om1 : Ordinal.{0}) ≠ 0 := Rj.rj_Om1_pos.ne'
      have hsplit : Om1 * (ξ0 / Om1) + ξ0 % Om1 = ξ0 := Ordinal.div_add_mod ξ0 Om1
      obtain ⟨F, hF⟩ : ∃ F : Finset Ordinal.{0},
          Om1 ≤ ξ0 → YvLv S (fun p => p ∈ F ∧ (p ∈ Tset τ ∧ p < upsilon (succ (l + h0)))) (Om1 * (ξ0 / Om1)) := by
        by_cases hξ : Om1 ≤ ξ0
        · have hM1 : 1 ≤ ξ0 / Om1 := (Ordinal.le_div hO0).2 (by rw [mul_one]; exact hξ)
          have hη1 : ξ0 % Om1 < Om1 := Ordinal.mod_lt ξ0 hO0
          have a3' : Om1 * (ξ0 / Om1) + ξ0 % Om1 ∈ Tset τ := by rw [hsplit]; exact a3
          have a4' : Om1 * (ξ0 / Om1) + ξ0 % Om1 < OmTwo := by rw [hsplit]; exact a4
          obtain ⟨F, hF⟩ := zf_yv_fin (zf_lv_T S hτE hτ1 hM1 hη1 a3' a4' hsU hτs)
          exact ⟨F, fun _ => hF⟩
        · exact ⟨∅, fun h => absurd h hξ⟩
      refine ⟨F ∪ {ξ0 - 1}, ?_⟩
      intro h ξ h1 h2 h3 h4 h5
      have hh : h = h0 := zf_seg_unique h1 h2 a1 a2
      subst hh
      have hξ : ξ = ξ0 := zf_vt_inj S hτE hτ1 h3 h4 a3 a4 (h5.trans a5.symm)
      subst hξ
      refine ⟨fun hξ1 => (hF hξ1).mono fun p hp => ⟨Finset.mem_union_left _ hp.1, hp.2.2.trans_le a6⟩,
        fun _ hξ2 => ⟨Finset.mem_union_right _ (Finset.mem_singleton_self _), ?_⟩⟩
      have hξs : ξ < upsilon (succ (l + h)) := Za.za_lt_next hτE hτ1 h3 hξ2 hτs hsU
      exact ((Ordinal.sub_le_self _ _).trans_lt hξs).trans_le a6
    · refine ⟨∅, fun h ξ h1 h2 h3 h4 h5 => ?_⟩
      exfalso
      refine hd ⟨h, ξ, h1, h2, h3, h4, h5, hm.monotone (Order.succ_le_of_lt ?_)⟩
      exact hm.lt_iff_lt.1 (h1.trans_lt (hYb y (Finset.mem_coe.1 hyY)))
  obtain ⟨Z0, hZ0⟩ := zf_fin_union (Finset.finite_toSet Y) (fun y Z => ZfEnlAt S l b y Z) hmono hex
  refine ⟨Z0.filter (· < b), fun z hz => (Finset.mem_filter.1 hz).2, fun y hy => ?_⟩
  intro h ξ h1 h2 h3 h4 h5
  obtain ⟨hA, hB⟩ := hZ0 y (Finset.mem_coe.2 hy) h ξ h1 h2 h3 h4 h5
  exact ⟨fun hξ => (hA hξ).mono fun p hp => ⟨Finset.mem_filter.2 ⟨hp.1, hp.2⟩, hp.2⟩,
    fun hξ1 hξ2 => ⟨Finset.mem_filter.2 (hB hξ1 hξ2), (hB hξ1 hξ2).2⟩⟩

/-- **`ZfImg S ⇒ Yq.XoShift2 S`**: the configuration is enlarged by the leaves of its node levels, the predecessors
of the level-`0` arguments and `ω` (`zf_enl`); the shift for the enlarged configuration restricts to `X ∪ Y`, and
`Zf.zfDCl` with the core points `X ∪ Y` gives `Yq.XoThCl`.  The level image at a nested node level (`ZfNest`) is
the node clause at the inner node (`ZfLevNode`), a smaller term: `zfDCl` at it, by induction on the size. -/
theorem zfShift2 (hLN : ZfLevNode S) (hI : ZfImg S) : XoShift2 S := by
  classical
  intro l β Q hl hl1 hν hνβ hsup hstd hlL X Y hX hY
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hb1 : upsilon (l + β) ≤ Om1 := hνβ.trans nuC_le_Om1
  have hlE : InE (upsilon l) := upsPt_inE (upsPt_upsilon hl0)
  obtain ⟨Z, hZb, hZ⟩ := zf_enl S hl0 hb1 Y (fun y hy => (hY y hy).2)
  set X' := insert ω X ∪ Z.filter (· < upsilon l) with hX'def
  set Y' := Y ∪ Z.filter (fun z => upsilon l ≤ z) with hY'def
  have hXX' : X ⊆ X' := fun x hx => Finset.mem_union_left _ (Finset.mem_insert_of_mem hx)
  have hYY' : Y ⊆ Y' := Finset.subset_union_left
  have hωX' : ω ∈ X' := Finset.mem_union_left _ (Finset.mem_insert_self _ _)
  have hZXY : ∀ z ∈ Z, z ∈ X' ∪ Y' := by
    intro z hz
    rcases lt_or_ge z (upsilon l) with h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hz, h⟩))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hz, h⟩))
  have hX' : ∀ x ∈ X', x < upsilon l := by
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · rcases Finset.mem_insert.1 h with rfl | h
      · exact omega0_lt_inE hlE
      · exact hX x h
    · exact (Finset.mem_filter.1 h).2
  have hY' : ∀ y ∈ Y', upsilon l ≤ y ∧ y < upsilon (l + β) := by
    intro y hy
    rcases Finset.mem_union.1 hy with h | h
    · exact hY y h
    · exact ⟨(Finset.mem_filter.1 h).2, hZb y (Finset.mem_filter.1 h).1⟩
  obtain ⟨D, μ, f, B, γ, Os, ⟨hQ, hXγ, hγμ, hLs, hres, hYB, ⟨hμl, hpi⟩, hmv, hub, hun, hLC, hid, hγU⟩, hZa,
    hImg⟩ := hI l β Q hl hl1 hν hνβ hsup hstd hlL X' Y' hX' hY'
  have hsubXY : ∀ z, z ∈ X ∪ Y → z ∈ X' ∪ Y' := fun z hz => Finset.union_subset_union hXX' hYY' hz
  refine ⟨D, μ, f, B, γ, Os, ⟨hQ, fun x hx => hXγ x (hXX' hx), hγμ, zf_lsMapW_mono hLs hXX' hYY',
    fun g hg => hres g (hYY' hg), fun y hy => hYB y (hYY' hy), ⟨hμl, fun y hy => hpi y (hYY' hy)⟩,
    fun y hy => hmv y (hYY' hy),
    fun y hy g h1 h2 t hA hW hL => hub y (hYY' hy) g h1 h2 t hA hW (Ub.UbT.Lv_mono hsubXY t hL),
    fun y hy g h1 h2 t hZW hWF hL hZL => hun y (hYY' hy) g h1 h2 t hZW hWF (UnT.Lv_mono hsubXY t hL)
      (ZL_mono (fun p hp => hp.elim (fun h => Or.inl (hsubXY p h)) Or.inr) t hZL),
    vl_lc_mono (fun p hp => hp.elim (fun h => Or.inl (hsubXY p h)) Or.inr) hLC, hid, hγU⟩, ?_⟩
  intro h L e hW hF hR hp
  have hβ0 : 0 < β := lt_of_le_of_lt zero_le hW.2.1
  have hμ0 : 0 < μ := pos_iff_ne_zero.2 hLs.rng.1.1
  have hμE : InE (upsilon μ) := upsPt_inE (upsPt_upsilon hμ0)
  have hBμ : Bases (upsilon μ) (upsilon l) := ⟨hμE, hlE, hμl, hl1⟩
  have hold := fun E hWE hp' =>
    (Vr.vrD_eq hl0 hb1 hX' hY' hLs.fix hLs.add hXγ hγμ hBμ hres hpi hmv hub hun hid E hWE hp').1
  have hyYof : ∀ y, y ∈ X ∪ Y → ∀ h', upsilon (l + h') ≤ y → y ∈ Y := by
    intro y hyP h' h1
    rcases Finset.mem_union.1 hyP with hx | hy
    · exact absurd (hX y hx) (not_lt.2 ((upsilon_normal.monotone le_self_add).trans h1))
    · exact hy
  have hLv' : ∀ y, y ∈ X ∪ Y → y ∈ Y' → ∀ h' M η, upsilon (l + h') ≤ y → y < upsilon (succ (l + h')) →
      1 ≤ M → η < Om1 → Om1 * M + η ∈ Tset (upsilon (l + h')) → Om1 * M + η < OmTwo →
      vt (upsilon (l + h')) (Om1 * M + η) = y → YvLv S (fun p => p ∈ X' ∪ Y' ∨ p < γ) (Om1 * M) := by
    intro y hyP _ h' M η h1 h2 hM1 hη1 hT h2' hval
    have hyY := hyYof y hyP h' h1
    have hξ1 : Om1 ≤ Om1 * M + η := (le_mul_left Om1 (zero_lt_one.trans_le hM1)).trans le_self_add
    obtain ⟨hA, -⟩ := hZ y hyY h' (Om1 * M + η) h1 h2 hT h2' hval
    have hdiv : (Om1 * M + η) / Om1 = M := by
      rw [Ordinal.mul_add_div M Rj.rj_Om1_pos.ne' η, Ordinal.div_eq_zero_of_lt hη1, add_zero]
    have hA' := hA hξ1
    rw [hdiv] at hA'
    exact hA'.mono fun p hp => Or.inl (hZXY p hp.1)
  have hPr' : ∀ y, y ∈ X ∪ Y → y ∈ Y' → ∀ h' η, upsilon (l + h') ≤ y → y < upsilon (succ (l + h')) →
      1 ≤ η → η < Om1 → η ∈ Tset (upsilon (l + h')) → vt (upsilon (l + h')) η = y → η - 1 ∈ X' ∪ Y' := by
    intro y hyP _ h' η h1 h2 h1η hη1 hT hval
    have hyY := hyYof y hyP h' h1
    obtain ⟨-, hB'⟩ := hZ y hyY h' η h1 h2 hT (hη1.trans tqc_Om1_lt_OmTwo) hval
    exact hZXY _ (hB' h1η hη1).1
  have hm := upsilon_normal.strictMono
  have hbU : UpsPt (upsilon (l + β)) := upsPt_upsilon (hl0.trans_le le_self_add)
  have hθ2 : ConjT.th S < OmTwo := by rw [← Ui.ui_one_W]; exact (InaccSeq.psiS_bounds (S := S) _ 1).2
  have hIndec : Indec (OmTwo : Ordinal.{0}) := Lq.lq_SC_indec Uc.uc_SC_Om2
  -- the level image at every node, by induction on the size (the nested node levels from the inner nodes)
  have hImgAll : ∀ n : ℕ, ∀ h₁ : Ordinal.{0}, ∀ L₁ e₁ : XoE, xoSize (.th h₁ L₁ e₁) ≤ n →
      XoWF S l β (.th h₁ L₁ e₁) → XoTopF e₁ → XoR S l μ (.th h₁ L₁ e₁) →
      (∀ z ∈ xoPts S l (upsilon (l + β)) (.th h₁ L₁ e₁), z ∈ X' ∪ Y') →
      (∀ z ∈ xoPts S l (upsilon (l + β)) (.th h₁ L₁ e₁), z ∈ X ∪ Y) → 1 ≤ xoVal S l L₁ →
      YvLv S (fun p => p ∈ X' ∪ Y' ∨ p < γ) (Om1 * xoVal S l L₁) →
      yvSub S D (Om1 * xoVal S l L₁) = Om1 * xoImg S l μ f L₁ := by
    intro n
    induction n with
    | zero =>
      intro h₁ L₁ e₁ hsz
      simp only [xoSize] at hsz
      omega
    | succ n ih =>
      intro h₁ L₁ e₁ hsz hW₁ hF₁ hR₁ hp₁ hq₁ hM1₁ hlv
      by_cases hN : ZfNest S l L₁
      swap
      · exact hImg h₁ L₁ e₁ hW₁ hF₁ hR₁ hp₁ hM1₁ hlv hN
      have hszL : xoSize L₁ ≤ n := by simp only [xoSize] at hsz; omega
      have hsubL : xoPts S l (upsilon (l + β)) L₁ ⊆ xoPts S l (upsilon (l + β)) (.th h₁ L₁ e₁) :=
        yq_pts_sub (fun z hz => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_left _ hz)))
      -- every node of the sum tree: the node clause, the values and the images `ε`-numbers
      have key : ∀ L₀ : XoE, ZfNS (ZfNodeOK S l) L₀ → xoSize L₀ ≤ n → XoWF S l β L₀ → XoR S l μ L₀ →
          (∀ z ∈ xoPts S l (upsilon (l + β)) L₀, z ∈ X' ∪ Y') →
          (∀ z ∈ xoPts S l (upsilon (l + β)) L₀, z ∈ X ∪ Y) →
          xoVal S l L₀ < upsilon (l + β) ∧
          ZfNS (fun N => xoVal S l N < Om1 ∧ xoVal S l N ∈ (↑(X' ∪ Y') : Set Ordinal.{0}) ∧
            InE (xoVal S l N) ∧ InE (xoImg S l μ f N) ∧ D (xoVal S l N) = xoImg S l μ f N) L₀ := by
        intro L₀ hN₀
        induction hN₀ with
        | node hOK =>
          rename_i h' L' e'
          intro hsz' hWL0 hRL hpL hqL
          obtain ⟨h'', L'', e'', heq, hF', hM1'⟩ := hOK
          simp only [XoE.th.injEq] at heq
          obtain ⟨rfl, rfl, rfl⟩ := heq
          have hWL := hWL0
          obtain ⟨-, hh'β, -, -, hη1, hξT, hξ2, hby, hys⟩ := hWL
          have hsb' : upsilon (succ (l + h')) ≤ upsilon (l + β) :=
            upsilon_normal.monotone (Order.succ_le_of_lt ((add_lt_add_iff_left l).2 hh'β))
          have hvL : xoVal S l (.th h' L' e') < upsilon (l + β) := hys.trans_le hsb'
          -- the node clause at the inner node
          have hDL : D (xoVal S l (.th h' L' e')) = xoImg S l μ f (.th h' L' e') :=
            zfDCl (Pt := fun z => z ∈ X ∪ Y) hl0 hβ0 hb1 hX' hY' hBμ hμ0 hLs.mono hLs.add hLs.below hres hold hun
              hLC hid hγU hZa n ih hLv' hPr' (Finset.mem_union_left _ hωX') (.th h' L' e') hsz' hWL0 hF'
              hRL hpL hqL hvL
          -- the inner value is an `ε`-number, and so is its image
          have hτU : UpsPt (upsilon (l + h')) := upsPt_upsilon (hl0.trans_le le_self_add)
          have hτE : InE (upsilon (l + h')) := upsPt_inE hτU
          have hv1 : xoVal S l (.th h' L' e') < Om1 := hvL.trans_le hb1
          have hτ1 : upsilon (l + h') < Om1 := hby.trans_lt hv1
          have hτb : upsilon (l + h') < upsilon (l + β) := hm ((add_lt_add_iff_left l).2 hh'β)
          have hηT : xoVal S l e' ∈ Tset (upsilon (l + h')) :=
            vzRem_T hτE hτ1 hξT hξ2 rfl (dvd_mul_right Om1 _) hη1
          have hηb : xoVal S l e' < upsilon (l + β) := Za.za_lt_next hτE hτ1 hηT hη1 hτb hbU
          have hyXY : xoVal S l (.th h' L' e') ∈ X ∪ Y := hqL _ (xoVal_mem _ hvL)
          have hyY : xoVal S l (.th h' L' e') ∈ Y := hyYof _ hyXY h' hby
          have hyY' : xoVal S l (.th h' L' e') ∈ Y' := hYY' hyY
          have hpe : xoPts S l (upsilon (l + β)) e' ⊆ xoPts S l (upsilon (l + β)) (.th h' L' e') :=
            yq_pts_sub (fun z hz => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_right _ hz)))
          have hηXY : xoVal S l e' ∈ X' ∪ Y' := hpL _ (hpe (xoVal_mem e' hηb))
          have hτXY : upsilon (l + h') ∈ X' ∪ Y' :=
            hpL _ (Finset.mem_filter.2 ⟨Finset.mem_insert_self _ _, hτb⟩)
          have hτY' : upsilon (l + h') ∈ Y' := by
            rcases Finset.mem_union.1 hτXY with hx | hy
            · exact absurd (hX' _ hx) (not_lt.2 (upsilon_normal.monotone le_self_add))
            · exact hy
          have hDτ := (hres h' hτY').2
          have hτ'1 : upsilon (μ + f h') < Om1 := (hDτ ▸ hLs.below _ hτY').trans hl1
          have hτ'E : InE (upsilon (μ + f h')) := upsPt_inE (upsPt_upsilon (hμ0.trans_le le_self_add))
          have hDη1 : D (xoVal S l e') < Om1 := by
            rcases Finset.mem_union.1 hηXY with hx | hy
            · rw [hLs.fix _ hx]; exact (hX' _ hx).trans hl1
            · exact (hLs.below _ hy).trans hl1
          have hlvF := hLv' _ hyXY hyY' h' (xoVal S l L') (xoVal S l e') hby hys hM1' hη1 hξT hξ2 rfl
          have hlvT : YvLv S (· ∈ Tset (upsilon (l + h'))) (Om1 * xoVal S l L') :=
            (zf_lv_T S hτE hτ1 hM1' hη1 hξT hξ2 hbU hτb).mono fun p hp => hp.1
          have hξθ : Om1 * xoVal S l L' + xoVal S l e' < ConjT.th S := uzTBound (S := S) _ hτE hτ1 _ hξT hξ2
          have hMθ : Om1 * xoVal S l L' < ConjT.th S := le_self_add.trans_lt hξθ
          have hDE : InE (D (xoVal S l (.th h' L' e'))) := by
            rcases lt_or_ge (xoVal S l L') Uc.ucB with hMB | hMB
            · -- a level below `B₂`: the term `thc M (par η)`
              have hqB : Om1 * xoVal S l L' < Uc.ucB := Xe.xe_mul_lt_B hMB
              have hVT : Vc.VcLv (· ∈ Tset (upsilon (l + h'))) (Om1 * xoVal S l L') := by
                cases hlvT with
                | low _ hV => exact hV
                | om hs _ heq => exact absurd hqB (not_lt.2 (heq ▸ yv_Om_ge_B hs))
                | cnf _ _ _ _ hB' => exact absurd hqB (not_lt.2 hB')
                | veb _ _ _ _ hB' => exact absurd hqB (not_lt.2 hB')
                | atom _ _ _ _ hB' => exact absurd hqB (not_lt.2 hB')
              have hVF : Vc.VcLv (fun p => p ∈ X' ∪ Y' ∨ p < γ) (Om1 * xoVal S l L') := by
                cases hlvF with
                | low _ hV => exact hV
                | om hs _ heq => exact absurd hqB (not_lt.2 (heq ▸ yv_Om_ge_B hs))
                | cnf _ _ _ _ hB' => exact absurd hqB (not_lt.2 hB')
                | veb _ _ _ _ hB' => exact absurd hqB (not_lt.2 hB')
                | atom _ _ _ _ hB' => exact absurd hqB (not_lt.2 hB')
              have hGT : Om1 * xoVal S l L' ∈ Tset (upsilon (l + h')) := vl_lv_mem hτE hτ1 hM1' hqB hVT
              have hZW : ZW (upsilon (l + h')) (UnT.thc (xoVal S l L') (UnT.par (xoVal S l e'))) :=
                ⟨⟨hM1', hqB, hGT, hξT, Za.za_lt_vt_all hτE hτ1 hM1' hMθ hηT hη1 hξT⟩, trivial⟩
              have hWF : WFr (upsilon (l + h')) (UnT.thc (xoVal S l L') (UnT.par (xoVal S l e'))) := ⟨trivial, hη1⟩
              obtain ⟨e1, -, hZW'⟩ := hun _ hyY' h' hby hys (UnT.thc (xoVal S l L') (UnT.par (xoVal S l e'))) hZW hWF
                hηXY ⟨hVF, trivial⟩ hηT ⟨hVT, trivial⟩ rfl
              obtain ⟨hN', -⟩ := hZW'
              rw [e1]
              refine ((vt_E_iff hτ'E hτ'1 hN'.mem ?_).2 ?_).2
              · exact hIndec.add_lt (hN'.qB.trans Uc.ucB_lt_Om2) (hDη1.trans Uc.uc_Om1_lt_Om2)
              · exact (le_mul_left Om1 (zero_lt_one.trans_le hN'.q1)).trans le_self_add
            · -- a level `≥ B₂`: the moving-level clause
              obtain ⟨q', -, hq'1, -, hq'θ, -, -, hmemT, hDy, -⟩ := hZa _ hyY' h' hby hys (xoVal S l L')
                (UnT.par (xoVal S l e')) hM1' hMB hMθ hlvF hlvT trivial trivial hη1 hηXY trivial hηT trivial rfl
              rw [hDy]
              refine ((vt_E_iff hτ'E hτ'1 hmemT ?_).2 ?_).2
              · exact hIndec.add_lt (hq'θ.trans hθ2) (hDη1.trans Uc.uc_Om1_lt_Om2)
              · exact (le_mul_left Om1 (zero_lt_one.trans_le hq'1)).trans le_self_add
          have hξ1 : Om1 ≤ Om1 * xoVal S l L' + xoVal S l e' :=
            (le_mul_left Om1 (zero_lt_one.trans_le hM1')).trans le_self_add
          have hvE : InE (xoVal S l (.th h' L' e')) := ((vt_E_iff hτE hτ1 hξT hξ2).2 hξ1).2
          have hyA : xoVal S l (.th h' L' e') ∈ (↑(X' ∪ Y') : Set Ordinal.{0}) :=
            Finset.mem_coe.2 (hpL _ (xoVal_mem _ hvL))
          exact ⟨hvL, ZfNS.node ⟨hv1, hyA, hvE, hDL ▸ hDE, hDL⟩⟩
        | add _ _ ihs iht =>
          rename_i s t _ _
          intro hsz' hWL0 hRL hpL hqL
          have hszs : xoSize s ≤ n := by simp only [xoSize] at hsz'; omega
          have hszt : xoSize t ≤ n := by simp only [xoSize] at hsz'; omega
          have hps : xoPts S l (upsilon (l + β)) s ⊆ xoPts S l (upsilon (l + β)) (.add s t) :=
            yq_pts_sub (fun z hz => Finset.mem_insert_of_mem (Finset.mem_union_left _ hz))
          have hpt : xoPts S l (upsilon (l + β)) t ⊆ xoPts S l (upsilon (l + β)) (.add s t) :=
            yq_pts_sub (fun z hz => Finset.mem_insert_of_mem (Finset.mem_union_right _ hz))
          obtain ⟨hvs, hNs⟩ := ihs hszs hWL0.1 hRL.1 (fun z hz => hpL z (hps hz)) (fun z hz => hqL z (hps hz))
          obtain ⟨hvt, hNt⟩ := iht hszt hWL0.2 hRL.2.1 (fun z hz => hpL z (hpt hz)) (fun z hz => hqL z (hpt hz))
          exact ⟨(indec_of_upsPt hbU).add_lt hvs hvt, ZfNS.add hNs hNt⟩
      obtain ⟨-, hQ⟩ := key L₁ hN hszL hW₁.2.2.1 hR₁.1 (fun z hz => hp₁ z (hsubL hz))
        (fun z hz => hq₁ z (hsubL hz))
      exact hLN l μ f D (↑(X' ∪ Y')) (fun p => p ∈ X' ∪ Y' ∨ p < γ) hLs.mono (hid 0 hγU.1) L₁ hQ hlv
  have hsb : upsilon (succ (l + h)) ≤ upsilon (l + β) :=
    upsilon_normal.monotone (Order.succ_le_of_lt ((add_lt_add_iff_left l).2 hW.2.1))
  have hv : xoVal S l (.th h L e) < upsilon (l + β) := hW.2.2.2.2.2.2.2.2.trans_le hsb
  exact zfDCl (Pt := fun z => z ∈ X ∪ Y) hl0 hβ0 hb1 hX' hY' hBμ hμ0 hLs.mono hLs.add hLs.below hres hold hun
    hLC hid hγU hZa _ (hImgAll (xoSize (.th h L e))) hLv' hPr' (Finset.mem_union_left _ hωX')
    (.th h L e) le_rfl hW hF hR (fun z hz => hsubXY z (hp z hz)) hp hv

/-- **`ZfImg S ⇒ Yq.XoShift S`** (`Yq.yqShift_of2`). -/
theorem zfShiftXo (hLN : ZfLevNode S) (hI : ZfImg S) : XoShift S := yqShift_of2 (zfShift2 hLN hI)

end Googology.Trans.PoR.InaccPsi.R2.Zf

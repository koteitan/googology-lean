import Googology.Trans.PoR.InaccPsi.R2.YqCov
import Googology.Trans.PoR.InaccPsi.R2.XbReal
import Googology.Trans.PoR.InaccPsi.R2.XoRoad

/-!
# The realizer bridge for moving-leaf levels, reduced to one clause of the shift

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`Xo.XoRealB` asks the realizer `Lr.LrReal S υ_λ υ_{λ+β}` from `Xo.XoGen S λ β`.  The proof of `Xb.xbReal_gen` is
repeated with two changes:

1. **the decompositions come from the covering lemma** (`yqCoverT`: the proof of `Yb.ybCover`, which also gives an
   `old` / `th` / `add` skeleton, `XoTopF`), not from the forms clause: a covered decomposition is restricted (`Xo.XoR`) at every `μ` above its tail bound and has a
   finite set of offsets, so the tail bound goes into the low points and the offset bases into the high points of
   the configuration, and the carry `Xo.XoCarry` applies to it;
2. **the clause of the shift** is `XoDCl`: the realizer map `D` sends the value of every well-formed decomposition
   restricted at `μ`, whose points (`xoPts`: every node value, node base and old point below `υ_{λ+β}`) lie in the
   configuration, to its image (`Xo.xoImg`, the leaf substitution).  `XoShift S` is the statement of `Xb.XbShift`
   with `XoDCl` in place of `Xb.XbThCl` (and the old-term clauses, which `XoDCl` contains at `Xo.XoE.old`).

* `xoRaw`, `xoPts`, `xoPts_lt`, `xoVal_mem` (points of a decomposition);
* `XoTopF`, `YqCovT`, `yqCoverT` (**the covering lemma with an `old` / `th` / `add` skeleton**);
* `XoDCl`, `XoShift` (statements);
* `yqReal_gen` (**`XoShift S`, the level statement `YbLevK S λ β`, UPPER at the inner restarts and `XoSup` give the
  realizer**; the forms clause of `XoGen` is not used);
* `XoRealBL` (**the bridge on the windows `υ_{λ+β} ≤ L(ω+1)`**, the only ones the road uses), `yqRealBL`
  (**`XoShift S ⇒ XoRealBL S`**, with no other hypothesis: the level statement there is `Yq.yqLevK`), `yqRealB`
  (**`XoShift S ∧ Yb.YbIF S ⇒ Xo.XoRealB S`**), `yqRealB_huge` (**`XoShift S ∧ YqIFHuge S ⇒ Xo.XoRealB S`**),
  `yqRealBL_of` (`Xo.XoRealB S ⇒ XoRealBL S`).

No new axiom.  New definitions: `xoRaw`, `xoPts`, `XoTopF` (syntax functions), `YqCovT`, `XoDCl`, `XoShift`, `XoRealBL` (statements).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Lr Googology.Trans.PoR.InaccPsi.R2.Xo
  Googology.Trans.PoR.InaccPsi.R2.Yb

variable {S : InaccSeq.{0}}

/-! ## Points of a decomposition -/

/-- **All points of a decomposition**: the old points, every node value and node base. -/
noncomputable def xoRaw (S : InaccSeq.{0}) (l : Ordinal.{0}) : XoE → Finset Ordinal.{0}
  | .old E => Vr.vrPts l E
  | .th h L e => insert (upsilon (l + h)) (insert (xoVal S l (.th h L e)) (xoRaw S l L ∪ xoRaw S l e))
  | .add s t => insert (xoVal S l (.add s t)) (xoRaw S l s ∪ xoRaw S l t)
  | .lc M => {M}
  | .phi a b => insert (xoVal S l (.phi a b)) (xoRaw S l a ∪ xoRaw S l b)
  | .om a => insert (xoVal S l (.om a)) (xoRaw S l a)
  | .coll p e => insert (xoVal S l (.coll p e)) (xoRaw S l p ∪ xoRaw S l e)

theorem xoRaw_val (l : Ordinal.{0}) : ∀ E : XoE, xoVal S l E ∈ xoRaw S l E
  | .old E => Vr.vrVal_mem l E
  | .th _ _ _ => Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  | .add _ _ => Finset.mem_insert_self _ _
  | .lc _ => Finset.mem_singleton_self _
  | .phi _ _ => Finset.mem_insert_self _ _
  | .om _ => Finset.mem_insert_self _ _
  | .coll _ _ => Finset.mem_insert_self _ _

/-- **The points below `b`** (`b = υ_{λ+β}`). -/
noncomputable def xoPts (S : InaccSeq.{0}) (l b : Ordinal.{0}) (E : XoE) : Finset Ordinal.{0} :=
  (xoRaw S l E).filter (· < b)

theorem xoPts_lt {l b : Ordinal.{0}} (E : XoE) : ∀ z ∈ xoPts S l b E, z < b := fun _ hz =>
  (Finset.mem_filter.1 hz).2

theorem xoVal_mem {l b : Ordinal.{0}} (E : XoE) (h : xoVal S l E < b) : xoVal S l E ∈ xoPts S l b E :=
  Finset.mem_filter.2 ⟨xoRaw_val l E, h⟩

/-! ## Decompositions whose countable skeleton is old nodes, `ϑ`-nodes and sums -/

/-- **The countable skeleton is `old`, `th`, `add`** (the level operations occur only inside `ϑ`-levels). -/
def XoTopF : XoE → Prop
  | .old _ => True
  | .th _ _ e => XoTopF e
  | .add s t => XoTopF s ∧ XoTopF t
  | .lc _ => False
  | .phi _ _ => False
  | .om _ => False
  | .coll _ _ => False

/-- **Covered with an `old` / `th` / `add` skeleton.** -/
def YqCovT (S : InaccSeq.{0}) (l β x : Ordinal.{0}) : Prop :=
  ∃ E : XoE, XoWF S l β E ∧ xoVal S l E = x ∧ ¬ XoCl E ∧ YbTail S l E ∧ YbOs l β E ∧ XoTopF E

theorem YqCovT.toCov {l β x : Ordinal.{0}} (h : YqCovT S l β x) : YbCov S l β x := by
  obtain ⟨E, h1, h2, h3, h4, h5, -⟩ := h
  exact ⟨E, h1, h2, h3, h4, h5⟩

theorem yqCov_old {l β x : Ordinal.{0}} (hl0 : 0 < l) (E : Vr.VrE) (hW : Vr.VrWF l β E)
    (hv : Vr.vrVal l E = x) (hO : YbOs l β (.old E)) :
    XoWF S l β (.old E) ∧ xoVal S l (.old E) = x ∧ ¬ XoCl (.old E) ∧ YbTail S l (.old E) ∧
      YbOs l β (.old E) ∧ XoTopF (.old E) := by
  have ht : YbTail S l (.old E) := by
    obtain ⟨γ, hγ, hR⟩ := ybOld_tail (β := β) hl0 E hW
    exact ⟨γ, hγ, hR⟩
  exact ⟨hW, hv, fun h => h, ht, hO, trivial⟩

/-- **The covering lemma with an `old` / `th` / `add` skeleton** (the proof of `Yb.ybCover`, tracking the
skeleton). -/
theorem yqCoverT {l β : Ordinal.{0}} (hl0 : 0 < l) (hK : YbLevK S l β) :
    ∀ x, x < upsilon (l + β) → x < Om1 → YqCovT S l β x := by
  have hm := upsilon_normal.strictMono
  have hlE : InE (upsilon l) := upsPt_inE (upsPt_upsilon hl0)
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hxβ hx1
  rcases lt_or_ge x (upsilon (succ l)) with hxl | hxl
  · exact ⟨_, yqCov_old (S := S) hl0 (.lo x) hxl rfl (ybOs_lo l β x)⟩
  by_cases hI : Indec x
  · obtain ⟨γ, hγx, hxγ⟩ := Xa.xa_seg_ex ((hm.monotone (zero_le : (0 : Ordinal.{0}) ≤ succ l)).trans hxl)
    have hlγ : l < γ := by
      by_contra hc
      push Not at hc
      exact absurd (hxγ.trans_le (hm.monotone (Order.succ_le_succ hc))) (not_lt.2 hxl)
    obtain ⟨h, rfl⟩ : ∃ h, l + h = γ := ⟨γ - l, Ordinal.add_sub_cancel_of_le hlγ.le⟩
    have h0 : 0 < h := pos_iff_ne_zero.2 fun e => by rw [e, add_zero] at hlγ; exact lt_irrefl l hlγ
    have hβ : h < β := (add_lt_add_iff_left l).1 (hm.lt_iff_lt.1 (hγx.trans_lt hxβ))
    have hτP : UpsPt (upsilon (l + h)) := upsPt_upsilon (hl0.trans_le le_self_add)
    have hτ1 : upsilon (l + h) < Om1 := hγx.trans_lt hx1
    have hτE : InE (upsilon (l + h)) := upsPt_inE hτP
    have hlτ : upsilon l < upsilon (l + h) := hm (lt_add_of_pos_right l h0)
    obtain ⟨m, hn, hT⟩ := exists_next hτP hτ1
    have hm2 : m = upsilon (succ (l + h)) := hn.unique (upsilon_isNext (l + h))
    have hxT : x ∈ Tset (upsilon (l + h)) := (hT x hx1).2 (hm2 ▸ hxγ)
    rcases eq_or_lt_of_le hγx with hτx | hτx
    · have hpar : ∀ p ∈ Par (upsilon (l + h)) x, p < upsilon l := by
        rw [← hτx]
        exact Ww.ww_par_self hlE hlτ hτE hτ1
      exact ⟨_, yqCov_old (S := S) hl0 (.sg h x) ⟨h0, hβ, hγx, hxγ, hpar⟩ rfl (ybOs_sg hβ)⟩
    · obtain ⟨ξ, hξT, hξ2, hv⟩ := vt_rep hτE hτ1 hxT hγx hx1 hI
      obtain ⟨hηT, hηx⟩ := Xa.xa_arg S hτE hτ1 hξT hξ2
      rw [hv] at hηx
      have hηO : ξ % Om1 < Om1 := mod_lt ξ Rj.rj_Om1_inE.pos.ne'
      obtain ⟨e, he, hev, hec, het, heo, heF⟩ := IH (ξ % Om1) hηx (hηx.trans hxβ) hηO
      have hdec0 : Om1 * (ξ / Om1) + ξ % Om1 = ξ := div_add_mod ξ Om1
      -- the level term
      obtain ⟨L, hLW, hLv, hLt, hLo⟩ : ∃ L : Xo.XoE, Xo.XoWF S l β L ∧ Xo.xoVal S l L = ξ / Om1 ∧
          YbTail S l L ∧ YbOs l β L := by
        set M := ξ / Om1 with hMdef
        set η := ξ % Om1 with hηdef
        rcases lt_or_ge M Om1 with hMΩ | hΩM
        · -- a countable level lies below `x`
          have hMx : M < x := by
            rcases lt_or_ge M (upsilon (l + h)) with hMτ | hτM
            · exact hMτ.trans_le hγx
            · have h' : Om1 * (Om1 * 0 + M) + η ∈ Tset (upsilon (l + h)) := by
                rw [mul_zero, zero_add, hdec0]; exact hξT
              have hMT : M ∈ Tset (upsilon (l + h)) :=
                (Rk.rkArg_T hτE hτ1 Rj.rj_Om1_inE.pos hMΩ hηO h').2
              have := (lvLevel_lt_vt hτE hτ1 hMT hτM hMΩ hηT hηO).1
              rw [hdec0, hv] at this
              exact this
          obtain ⟨L, hLW, hLv, -, hLt, hLo, -⟩ := IH M hMx (hMx.trans hxβ) hMΩ
          exact ⟨L, hLW, hLv, hLt, hLo⟩
        · by_cases hlow : ∃ c < upsilon l, ∀ μ, c < upsilon μ → Vd.VdLtIn M (upsilon μ)
          · exact ⟨.lc M, trivial, rfl, ybLc_tail hlow, ybOs_lc l β M⟩
          · have hYK := hK h M η h0 hβ hΩM hηO hηT (by rw [hdec0]; exact hξT) (by rw [hdec0]; exact hξ2)
              (by rw [hdec0, hv]; exact hγx) (by rw [hdec0, hv]; exact hxβ) hlow
            rw [hdec0, hv] at hYK
            obtain ⟨L, hLW, hLv, -, hLt, hLo⟩ := ybK_cov (S := S) (l := l) (β := β) (x := x) hl0
              (fun y hy => (IH y hy (hy.trans hxβ) (hy.trans hx1)).toCov) M hYK
            exact ⟨L, hLW, hLv, hLt, hLo⟩
      have hdec : Om1 * Xo.xoVal S l L + Xo.xoVal S l e = ξ := by rw [hLv, hev]; exact hdec0
      obtain ⟨γ, hγ, hR⟩ := ybTail_two hLt het
      refine ⟨.th h L e, ⟨h0, hβ, hLW, he, ?_⟩, ?_, fun hc => hc, ⟨γ, hγ, fun μ hμ hB => hR μ hμ hB⟩,
        ybOs_th hβ hLo heo, heF⟩
      · rw [hdec, hv, hev]; exact ⟨hηO, hξT, hξ2, hγx, hxγ⟩
      · show vt (upsilon (l + h)) (Om1 * Xo.xoVal S l L + Xo.xoVal S l e) = x
        rw [hdec, hv]
  · have hD : DecompR0 x := not_not.1 hI
    rcases hD with h0 | ⟨y, z, hy, hz, hyz⟩
    · rw [h0] at hxl
      exact absurd hxl (not_le.2 (zero_le.trans_lt (hm (lt_succ l))))
    obtain ⟨Ey, wy, vy, cy, ty, oy, fy⟩ := IH y hy (hy.trans hxβ) (hy.trans hx1)
    obtain ⟨Ez, wz, vz, cz, tz, oz, fz⟩ := IH z hz (hz.trans hxβ) (hz.trans hx1)
    obtain ⟨γ, hγ, hR⟩ := ybTail_two ty tz
    refine ⟨.add Ey Ez, ⟨wy, wz⟩, ?_, fun h => cy h.1, ⟨γ, hγ, fun μ hμ hB =>
      ⟨(hR μ hμ hB).1, (hR μ hμ hB).2, fun h => absurd h.1 cy⟩⟩, ybOs_add oy oz, fy, fz⟩
    show Xo.xoVal S l Ey + Xo.xoVal S l Ez = x
    rw [vy, vz, hyz]

/-! ## The clause and the shift -/

/-- **The clause of the shift for moving-leaf decompositions** (open): `D` sends the value of every well-formed
decomposition restricted at `μ` with an `old` / `th` / `add` skeleton, with value below `υ_{λ+β}`, whose points lie in
`X ∪ Y` to its image. -/
def XoDCl (S : InaccSeq.{0}) (l β μ : Ordinal.{0}) (f D : Ordinal.{0} → Ordinal.{0}) (X Y : Finset Ordinal.{0}) :
    Prop :=
  0 < β → ∀ E : XoE, XoWF S l β E → XoTopF E → XoR S l μ E → (∀ z ∈ xoPts S l (upsilon (l + β)) E, z ∈ X ∪ Y) →
    xoVal S l E < upsilon (l + β) → D (xoVal S l E) = xoImg S l μ f E

/-- **The shift with the moving-leaf clause** (open): the statement of `Xb.XbShift` with `XoDCl`. -/
def XoShift (S : InaccSeq.{0}) : Prop :=
  ∀ (l β : Ordinal.{0})
    (Q : Ordinal.{0} → (Ordinal.{0} → Ordinal.{0}) → Ordinal.{0} → Ordinal.{0} → Finset Ordinal.{0} → Prop),
    IsRestartIdx l → upsilon l < Om1 → upsilon l < nuC → upsilon (l + β) ≤ nuC →
    (∀ γ < upsilon l, ∀ Os : Finset Ordinal.{0}, (∀ d ∈ Os, d < β) →
      ∃ μ f B, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < upsilon l ∧ μ + B ≤ l ∧ ω ^ 2 ∣ B ∧
        upsilon (μ + B) ≤ cdR S μ ∧ Sl.SlOff f Os B ∧ Q μ f B γ Os) →
    Cx.CxStdPairTop S → upsilon l ≤ Nc.ncL S (ω + 1) →
    ∀ (X Y : Finset Ordinal.{0}), (∀ x ∈ X, x < upsilon l) → (∀ y ∈ Y, upsilon l ≤ y ∧ y < upsilon (l + β)) →
    ∃ D μ f B γ Os, Q μ f B γ Os ∧ (∀ x ∈ X, x < γ) ∧ γ < upsilon μ ∧ Ls.LsMapW S l X Y D μ ∧
      (∀ g, upsilon (l + g) ∈ Y → g ∈ Os ∧ D (upsilon (l + g)) = upsilon (μ + f g)) ∧
      (∀ y ∈ Y, D y < upsilon (μ + B)) ∧ upsilon μ < upsilon l ∧ XoDCl S l β μ f D X Y

/-! ## The realizer -/

/-- **`XoShift S`, the level statement, UPPER at the inner restarts and the supply give the realizer.** -/
theorem yqReal_gen (hS : XoShift S) {l β : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : upsilon l < Om1)
    (hν : upsilon l < nuC) (hνβ : upsilon (l + β) ≤ nuC) (hK : YbLevK S l β)
    (hU : ∀ g, 0 < g → g < β → ω ^ 2 ∣ g → CdUpper S (l + g)) (hsup : XoSup S l β)
    (hstd : Cx.CxStdPairTop S) (hlL : upsilon l ≤ Nc.ncL S (ω + 1)) :
    LrReal S (upsilon l) (upsilon (l + β)) := by
  classical
  intro X Y hX hY _
  have hm := upsilon_normal.strictMono
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have ha : UpsPt (upsilon l) := upsPt_upsilon hl0
  have hlE : InE (upsilon l) := upsPt_inE ha
  have hb1 : upsilon (l + β) ≤ Om1 := hνβ.trans nuC_le_Om1
  set b := upsilon (l + β) with hbdef
  set rr : Ordinal.{0} → Prop := fun y => ∃ g, (0 < g ∧ g < β ∧ ω ^ 2 ∣ g ∧ y = upsilon (l + g)) ∧
    cdR S (l + g) < b with hrrdef
  have hch : ∀ y, rr y → ∃ g, ∃ E : XoE, ∃ c, ∃ O : Finset Ordinal.{0},
      (0 < g ∧ g < β ∧ ω ^ 2 ∣ g ∧ y = upsilon (l + g)) ∧ XoWF S l β E ∧ xoVal S l E = cdR S (l + g) ∧
      c < upsilon l ∧ (∀ μ, c < upsilon μ → Bases (upsilon μ) (upsilon l) → XoR S l μ E) ∧
      (∀ d ∈ O, d < β) ∧ (∀ Os : Finset Ordinal.{0}, O ⊆ Os → XoOs l Os E) ∧ XoTopF E := by
    rintro y ⟨g, hg, hlt⟩
    obtain ⟨E, hW, hv, -, ⟨c, hc, hR⟩, ⟨O, hO, hOs⟩, hF⟩ := yqCoverT hl0 hK _ hlt (hlt.trans_le hb1)
    exact ⟨g, E, c, O, hg, hW, hv, hc, hR, hO, hOs, hF⟩
  choose! gE EE cE OE hgE hWE hvE hcE hRE hOE hOsE hFE using hch
  set T := Y.filter rr with hTdef
  set Y' := Y ∪ (T.biUnion (fun y => (xoPts S l b (EE y)).filter (upsilon l ≤ ·)) ∪
    T.biUnion (fun y => (OE y).image (fun d => upsilon (l + d)))) with hY'def
  set X' := X ∪ (T.biUnion (fun y => (xoPts S l b (EE y)).filter (· < upsilon l)) ∪ T.image cE) with hX'def
  have hX' : ∀ x ∈ X', x < upsilon l := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact hX x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · obtain ⟨u, -, hxu⟩ := Finset.mem_biUnion.1 hx
      exact (Finset.mem_filter.1 hxu).2
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hx
      exact hcE u (Finset.mem_filter.1 hu).2
  have hY' : ∀ y ∈ Y', upsilon l ≤ y ∧ y < b := by
    intro y hy
    rcases Finset.mem_union.1 hy with hy | hy
    · exact hY y hy
    rcases Finset.mem_union.1 hy with hy | hy
    · obtain ⟨u, -, hyu⟩ := Finset.mem_biUnion.1 hy
      obtain ⟨hyp, hly⟩ := Finset.mem_filter.1 hyu
      exact ⟨hly, xoPts_lt _ y hyp⟩
    · obtain ⟨u, hu, hyu⟩ := Finset.mem_biUnion.1 hy
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hyu
      exact ⟨hm.monotone le_self_add, hm (add_lt_add_right (hOE u (Finset.mem_filter.1 hu).2 d hd) l)⟩
  obtain ⟨D, μ, f, B, γ, Os, hQ, hXγ, hγμ, hW, hres, himg, hμl, hDcl⟩ :=
    hS l β (fun μ f B _ Os => XoCarry S l β μ f B Os) hl hl1 hν hνβ
      (fun γ hγ Os hOs => by
        obtain ⟨μ, f, B, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hsup γ hγ Os hOs
        exact ⟨μ, f, B, h1, h2, h3, h4, h5, h6, h7, h8⟩) hstd hlL X' Y' hX' hY'
  have hXX : ∀ x ∈ X, x ∈ X' := fun x hx => Finset.mem_union_left _ hx
  have hYY : ∀ y ∈ Y, y ∈ Y' := fun y hy => Finset.mem_union_left _ hy
  have hsub : ∀ u ∈ X ∪ Y, u ∈ X' ∪ Y' := by
    intro u hu
    rcases Finset.mem_union.1 hu with hu | hu
    · exact Finset.mem_union_left _ (hXX u hu)
    · exact Finset.mem_union_right _ (hYY u hu)
  have hμE : InE (upsilon μ) := upsPt_inE (upsPt_upsilon (pos_iff_ne_zero.2 hW.rng.1.1))
  have hBμ : Bases (upsilon μ) (upsilon l) := ⟨hμE, hlE, hμl, hl1⟩
  refine ⟨D, μ, ⟨fun x hx => hW.fix x (hXX x hx), hW.mono.mono fun u hu => hsub u hu,
    fun x hx y hy z hz => hW.add x (hsub x hx) y (hsub y hy) z (hsub z hz),
    fun y hy => hW.indec y (hYY y hy), fun y hy x hx => hW.above y (hYY y hy) x (hXX x hx),
    fun y hy => hW.below y (hYY y hy), hW.rng, fun ha => hW.base (hYY _ ha),
    fun y hy => hW.bd y (hYY y hy), ?_,
    fun y hy y' hy' => hW.pair2 y (hYY y hy) y' (hYY y' hy')⟩⟩
  intro y hy y' hy' hay hyy h1
  by_cases hr : ∃ g, 0 < g ∧ ω ^ 2 ∣ g ∧ y = upsilon (l + g)
  · obtain ⟨g, hg0, hgd, rfl⟩ := hr
    have hgβ : g < β := (add_lt_add_iff_left l).1 (hm.lt_iff_lt.1 (hY _ hy).2)
    have hyr : y' ≤ cdR S (l + g) := cdUpper_iff.1 (hU g hg0 hgβ hgd) y' h1
    obtain ⟨hgO, hDy⟩ := hres g (hYY _ hy)
    obtain ⟨hLow, hbig, hfrm⟩ := hQ g hgO hg0 hgd
    have hmono : ∀ u ∈ X' ∪ Y', ∀ v ∈ X' ∪ Y', u ≤ v → D u ≤ D v := fun u hu v hv huv =>
      (hW.mono.le_iff_le (Finset.mem_coe.2 hu) (Finset.mem_coe.2 hv)).2 huv
    have hle : D y' ≤ cdR S (μ + f g) := by
      by_cases hbg : b ≤ cdR S (l + g)
      · exact (himg y' (hYY y' hy')).le.trans (hbig hbg)
      · have hrr : rr (upsilon (l + g)) := ⟨g, ⟨hg0, hgβ, hgd, rfl⟩, not_le.1 hbg⟩
        have hT : upsilon (l + g) ∈ T := Finset.mem_filter.2 ⟨hy, hrr⟩
        have hgg : gE (upsilon (l + g)) = g := by
          have e := (hgE _ hrr).2.2.2
          exact (add_left_cancel (hm.injective e)).symm
        have hv := hvE _ hrr
        rw [hgg] at hv
        set E := EE (upsilon (l + g)) with hEdef
        set c := cE (upsilon (l + g)) with hcdef
        have hcX : c ∈ X' := Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_image.2 ⟨_, hT, rfl⟩))
        have hcγ : c < γ := hXγ c hcX
        have hpts : ∀ z ∈ xoPts S l b E, z ∈ X' ∪ Y' := by
          intro z hz
          by_cases hzl : upsilon l ≤ z
          · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_left _
              (Finset.mem_biUnion.2 ⟨_, hT, Finset.mem_filter.2 ⟨hz, hzl⟩⟩)))
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_union_left _
              (Finset.mem_biUnion.2 ⟨_, hT, Finset.mem_filter.2 ⟨hz, not_le.1 hzl⟩⟩)))
        have hR : XoR S l μ E := hRE _ hrr μ (hcγ.trans hγμ) hBμ
        have hOs : XoOs l Os E := hOsE _ hrr Os fun d hd => by
          have hdY : upsilon (l + d) ∈ Y' := Finset.mem_union_right _ (Finset.mem_union_right _
            (Finset.mem_biUnion.2 ⟨_, hT, Finset.mem_image.2 ⟨d, hd, rfl⟩⟩))
          exact (hres d hdY).1
        have hvb : xoVal S l E < b := hv ▸ not_le.1 hbg
        have e1 := hDcl (hg0.trans hgβ) E (hWE _ hrr) (hFE _ hrr) hR hpts hvb
        have hRm : cdR S (l + g) ∈ X' ∪ Y' := hv ▸ hpts _ (xoVal_mem E hvb)
        have h5 : D y' ≤ D (cdR S (l + g)) :=
          hmono y' (Finset.mem_union_right _ (hYY y' hy')) _ hRm hyr
        rw [← hv, e1] at h5
        exact h5.trans (hfrm E (hWE _ hrr) hv hOs hR)
    have hge : upsilon (μ + f g) ≤ D y' := by
      rw [← hDy]
      exact (hW.mono (Finset.mem_coe.2 (Finset.mem_union_right _ (hYY _ hy)))
        (Finset.mem_coe.2 (Finset.mem_union_right _ (hYY _ hy'))) hyy).le
    rw [hDy]
    exact le1_of_le_of_le1 hge hle hLow
  · push Not at hr
    exact hW.pair1 y (hYY y hy) y' (hYY y' hy') hay hyy (fun g hg hgd e => hr g hg hgd e) h1

/-! ## The bridges -/

/-- **The bridge on the windows `υ_{λ+β} ≤ L(ω+1)`** (the only windows the road uses, `Xo.xoVisI_of_gen`). -/
def XoRealBL (S : InaccSeq.{0}) : Prop :=
  ∀ l β : Ordinal.{0}, IsRestartIdx l → upsilon l < Om1 → upsilon l < nuC → upsilon (l + β) ≤ nuC →
    upsilon (l + β) ≤ Nc.ncL S (ω + 1) →
    Cx.CxStdPairTop S → upsilon l ≤ Nc.ncL S (ω + 1) → XoGen S l β → LrReal S (upsilon l) (upsilon (l + β))

/-- **`XoShift S ⇒ XoRealBL S`**, with no other hypothesis (the level statement is `Yq.yqLevK`). -/
theorem yqRealBL (hS : XoShift S) : XoRealBL S := fun l β hl hl1 hν hνβ hβL hstd hlL h =>
  yqReal_gen hS hl hl1 hν hνβ
    (yqLevK (pos_iff_ne_zero.2 hl.1) (hνβ.trans nuC_le_Om1) hβL) h.1 h.2.2 hstd hlL

/-- **`XoShift S ∧ YbIF S ⇒ Xo.XoRealB S`.** -/
theorem yqRealB (hS : XoShift S) (hIF : YbIF S) : XoRealB S := fun l β hl hl1 hν hνβ hstd hlL h =>
  yqReal_gen hS hl hl1 hν hνβ
    (ybLevK_of_IF (pos_iff_ne_zero.2 hl.1) (hνβ.trans nuC_le_Om1) hIF) h.1 h.2.2 hstd hlL

/-- **`XoShift S ∧ YqIFHuge S ⇒ Xo.XoRealB S`.** -/
theorem yqRealB_huge (hS : XoShift S) (hH : YqIFHuge S) : XoRealB S :=
  yqRealB hS (Yg.ygIF_of_th (yqIF_of_huge hH))

/-- `Xo.XoRealB S ⇒ XoRealBL S`. -/
theorem yqRealBL_of (h : XoRealB S) : XoRealBL S := fun l β hl hl1 hν hνβ _ hstd hlL hG =>
  h l β hl hl1 hν hνβ hstd hlL hG

end Googology.Trans.PoR.InaccPsi.R2.Yq

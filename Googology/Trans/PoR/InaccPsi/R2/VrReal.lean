import Googology.Trans.PoR.InaccPsi.R2.VrForm

/-!
# Realizers with the repaired forms: the carry moves each node by the map of its own segment

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`Vl.vlShiftCore` gives the FRAG map `D` with `π` on the lowest segment, the segment move on the low points of every
segment, the hull isomorphism on the terms of every segment, and `D(x + y) = D x + D y` on the configuration.  So the
value of a decomposition `VrE` whose points lie in the configuration is moved to its image `vrImg`
(`vrD_eq`): `D(τ + c) = τ' + Ψ_{h'}(c)`, `Ψ_{h'}` the map of the segment of `c`.  The carry `VrCarry` asks
`vrImg ≤ r(μ+f(g))`.

* `vrD_eq` (**`D(val E) = img E` and the offsets of `E` lie in `Os`**, from the clauses of `Vl.vlShiftCore`);
* `vrImg_agree` (two decompositions of one value have one image);
* `vrReal_gen` (**realizer maps from UPPER, the forms `υ_{λ+β} ≤ r(λ+g) ∨ VrForm`, and the supply with
  `VrCarry`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vr

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Lr Googology.Trans.PoR.InaccPsi.R2.Ub
  Googology.Trans.PoR.InaccPsi.R2.Un Googology.Trans.PoR.InaccPsi.R2.Ur Googology.Trans.PoR.InaccPsi.R2.Vi
  Googology.Trans.PoR.InaccPsi.R2.Vl

variable {S : InaccSeq.{0}}

/-- **The FRAG map on a decomposition**: if `D` has the clauses of `Vl.vlShiftCore` on `X ∪ Y` and every point of
`E` lies in `X ∪ Y`, then `D(val E) = img E` and the offsets of `E` lie in `Os`. -/
theorem vrD_eq {l β μ γ : Ordinal.{0}} {f D : Ordinal.{0} → Ordinal.{0}} {Os X Y : Finset Ordinal.{0}}
    (hl0 : 0 < l) (hb1 : upsilon (l + β) ≤ Om1)
    (hXl : ∀ x ∈ X, x < upsilon l) (hYl : ∀ y ∈ Y, upsilon l ≤ y ∧ y < upsilon (l + β))
    (hfix : ∀ x ∈ X, D x = x)
    (hadd : ∀ x ∈ X ∪ Y, ∀ y ∈ X ∪ Y, ∀ z ∈ X ∪ Y, (x + y = z ↔ D x + D y = D z))
    (hXγ : ∀ x ∈ X, x < γ) (hγμ : γ < upsilon μ) (hB : Bases (upsilon μ) (upsilon l))
    (hres : ∀ g, upsilon (l + g) ∈ Y → g ∈ Os ∧ D (upsilon (l + g)) = upsilon (μ + f g))
    (hpi : ∀ y ∈ Y, y < upsilon (succ l) → D y = pi (upsilon μ) (upsilon l) y)
    (hmv : ∀ y ∈ Y, ∀ g, upsilon (l + g) ≤ y → y < upsilon (succ (l + g)) →
      (∀ p ∈ Par (upsilon (l + g)) y, p < upsilon l) → D y = mv (upsilon (l + g)) (upsilon (μ + f g)) y)
    (hub : ∀ y ∈ Y, ∀ g, upsilon (l + g) ≤ y → y < upsilon (succ (l + g)) → ∀ t : UbT, UbT.IsA t →
      UbT.WF (upsilon (l + g)) t → UbT.Lv (· ∈ X ∪ Y) t → UbT.ev (upsilon (l + g)) t = y →
      D y = UbT.ev (upsilon (μ + f g)) (t.map D) ∧ UbT.WF (upsilon (μ + f g)) (t.map D))
    (hun : ∀ y ∈ Y, ∀ g, upsilon (l + g) ≤ y → y < upsilon (succ (l + g)) → ∀ t : UnC, ZW (upsilon (l + g)) t →
      WFr (upsilon (l + g)) t → UnT.Lv (· ∈ X ∪ Y) t → ZL (fun p => p ∈ X ∪ Y ∨ p < γ) t →
      UnT.Lv (· ∈ Tset (upsilon (l + g))) t → ZL (· ∈ Tset (upsilon (l + g))) t →
      UnT.ev (upsilon (l + g)) t = y →
      D y = UnT.ev (upsilon (μ + f g)) (vmap D t) ∧ WFr (upsilon (μ + f g)) (vmap D t) ∧
        ZW (upsilon (μ + f g)) (vmap D t))
    (hDid : ∀ x, x < γ → D x = x) :
    ∀ E : VrE, VrWF l β E → (∀ z ∈ vrPts l E, z ∈ X ∪ Y) →
      D (vrVal l E) = vrImg l μ f E ∧ VrOs l Os E := by
  classical
  have hm := upsilon_normal.strictMono
  have hX : ∀ z ∈ X ∪ Y, z < upsilon l → z ∈ X := fun z hz hzl =>
    (Finset.mem_union.1 hz).resolve_right fun hy => absurd (hYl z hy).1 (not_le.2 hzl)
  have hY : ∀ z ∈ X ∪ Y, upsilon l ≤ z → z ∈ Y := fun z hz hzl =>
    (Finset.mem_union.1 hz).resolve_left fun hx => absurd (hXl z hx) (not_lt.2 hzl)
  have hlow : ∀ p ∈ X ∪ Y, p < upsilon (succ l) → D p = pi (upsilon μ) (upsilon l) p := by
    intro p hp hps
    by_cases hpl : p < upsilon l
    · have hpX := hX p hp hpl
      rw [hfix p hpX, pi_lt hB ((hXγ p hpX).trans hγμ)]
    · exact hpi p (hY p hp (not_lt.1 hpl)) hps
  have hleaf : ∀ B p, vrLv l B p → p ∈ X ∪ Y → D p = vrLf l μ f p ∧ vrLvO l Os p := by
    intro B p hp hpm
    rcases hp with hps | ⟨h', h0, -, rfl⟩
    · refine ⟨?_, Or.inl hps⟩
      rw [hlow p hpm hps]; simp only [vrLf, if_pos hps]
    · have hge : upsilon l ≤ upsilon (l + h') := hm.monotone le_self_add
      obtain ⟨hO, hD⟩ := hres h' (hY _ hpm hge)
      refine ⟨?_, Or.inr ⟨h', hO, h0, rfl⟩⟩
      rw [hD]; simp only [vrLf, if_neg (not_lt.2 (vr_succ_le h0)), lrIx_up, Ordinal.add_sub_cancel]
  have hbase : ∀ h, 0 < h → upsilon (l + h) ∈ X ∪ Y → h ∈ Os := fun h _ hh =>
    (hres h (hY _ hh (hm.monotone le_self_add))).1
  intro E
  induction E with
  | lo c =>
    intro hw hp
    have hc := hp c (Finset.mem_singleton_self _)
    exact ⟨hlow c hc hw, trivial⟩
  | sg h y =>
    intro hw hp
    obtain ⟨h0, -, h1, h2, h3⟩ := hw
    have hy := hp y (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have hyY := hY y hy ((hm.monotone le_self_add).trans h1)
    exact ⟨hmv y hyY h h1 h2 h3, hbase h h0 (hp _ (Finset.mem_insert_self _ _))⟩
  | ub h t =>
    intro hw hp
    obtain ⟨h0, -, hA, hW, hL, h1, h2⟩ := hw
    have hy := hp _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have hyY := hY _ hy ((hm.monotone le_self_add).trans h1)
    have hl' : ∀ p ∈ UbT.lvs t, D p = vrLf l μ f p ∧ vrLvO l Os p ∧ p ∈ X ∪ Y := fun p hpt =>
      have hpm := hp p (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hpt))
      ⟨(hleaf β p (UbT.mem_lvs hL p hpt) hpm).1, (hleaf β p (UbT.mem_lvs hL p hpt) hpm).2, hpm⟩
    have hLt := UbT.Lv_lvs t
    obtain ⟨e1, -⟩ := hub _ hyY h h1 h2 t hA hW (UbT.Lv_mono (fun p hpt => (hl' p hpt).2.2) _ hLt) rfl
    have hmap : t.map D = t.map (vrLf l μ f) :=
      UbT.map_congr _ (UbT.Lv_mono (fun p hpt => (hl' p hpt).1) _ hLt)
    rw [hmap] at e1
    exact ⟨e1, hbase h h0 (hp _ (Finset.mem_insert_self _ _)),
      UbT.Lv_mono (fun p hpt => (hl' p hpt).2.1) _ hLt⟩
  | tm h t Lf δ =>
    intro hw hp
    obtain ⟨h0, hh, hδ, hz, hW, hL, hzl, hLf, h1, h2⟩ := hw
    have hy := hp _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have hyY := hY _ hy ((hm.monotone le_self_add).trans h1)
    have hδX : δ ∈ X := hX δ (hp δ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_insert_self _ _)))) hδ
    have hδγ := hXγ δ hδX
    have hτE : InE (upsilon (l + h)) := upsPt_inE (upsPt_upsilon (hl0.trans_le le_self_add))
    have hτ1 : upsilon (l + h) < Om1 := (hm (add_lt_add_right hh l)).trans_le hb1
    have hT : ∀ p, vrLv l (succ h) p → p ∈ Tset (upsilon (l + h)) := by
      rintro p (hps | ⟨h', -, hh', rfl⟩)
      · exact Uh.uh_T_le hτE hτ1 (hps.le.trans (vr_succ_le h0))
      · exact Uh.uh_T_le hτE hτ1 (hm.monotone (add_le_add_right (Order.lt_succ_iff.1 hh') l))
    have hmem : ∀ p ∈ UnT.lvs t ∪ Lf, p ∈ X ∪ Y := fun p hpt =>
      hp p (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hpt)))
    have hlv : ∀ p ∈ UnT.lvs t ∪ Lf, vrLv l (succ h) p := by
      intro p hpt
      rcases Finset.mem_union.1 hpt with hpt | hpt
      · exact UnT.mem_lvs hL p hpt
      · exact hLf p hpt
    have hl' : ∀ p ∈ UnT.lvs t ∪ Lf, D p = vrLf l μ f p ∧ vrLvO l Os p ∧ p ∈ X ∪ Y ∧
        p ∈ Tset (upsilon (l + h)) := fun p hpt =>
      ⟨(hleaf _ p (hlv p hpt) (hmem p hpt)).1, (hleaf _ p (hlv p hpt) (hmem p hpt)).2, hmem p hpt,
        hT p (hlv p hpt)⟩
    have hLt := UnT.Lv_lvs t
    have hin : ∀ p ∈ UnT.lvs t, p ∈ UnT.lvs t ∪ Lf := fun p hpt => Finset.mem_union_left _ hpt
    have hinL : ∀ p ∈ Lf, p ∈ UnT.lvs t ∪ Lf := fun p hpt => Finset.mem_union_right _ hpt
    have hlowδ : ∀ p, p < δ → D p = vrLf l μ f p := by
      intro p hpδ
      have hps : p < upsilon (succ l) := (hpδ.trans hδ).trans (hm (lt_succ l))
      rw [hDid p (hpδ.trans hδγ)]; simp only [vrLf, if_pos hps]
      exact (pi_lt hB ((hpδ.trans hδγ).trans hγμ)).symm
    obtain ⟨e1, -⟩ := hun _ hyY h h1 h2 t hz hW (UnT.Lv_mono (fun p hpt => (hl' p (hin p hpt)).2.2.1) _ hLt)
      (vl_ZL_mono (fun p _ hpz => hpz.elim (fun hq => Or.inl (hl' p (hinL p hq)).2.2.1)
        (fun hq => Or.inr (hq.trans hδγ))) t hzl)
      (UnT.Lv_mono (fun p hpt => (hl' p (hin p hpt)).2.2.2) _ hLt)
      (vl_ZL_mono (fun p _ hpz => hpz.elim (fun hq => (hl' p (hinL p hq)).2.2.2)
        (fun hq => Uh.uh_T_le hτE hτ1 ((hq.trans hδ).le.trans (hm.monotone le_self_add)))) t hzl) rfl
    have hmap : vmap D t = vmap (vrLf l μ f) t := vmap_congr t
      (UnT.Lv_mono (fun p hpt => (hl' p (hin p hpt)).1) _ hLt)
      (vl_ZL_mono (fun p _ hpz => hpz.elim (fun hq => (hl' p (hinL p hq)).1) (fun hq => hlowδ p hq)) t hzl)
    rw [hmap] at e1
    exact ⟨e1, hbase h h0 (hp _ (Finset.mem_insert_self _ _)),
      UnT.Lv_mono (fun p hpt => (hl' p (hin p hpt)).2.1) _ hLt, fun p hpt => (hl' p (hinL p hpt)).2.1⟩
  | add s t ihs iht =>
    intro hw hp
    have hps : ∀ z ∈ vrPts l s, z ∈ X ∪ Y := fun z hz =>
      hp z (Finset.mem_insert_of_mem (Finset.mem_union_left _ hz))
    have hpt : ∀ z ∈ vrPts l t, z ∈ X ∪ Y := fun z hz =>
      hp z (Finset.mem_insert_of_mem (Finset.mem_union_right _ hz))
    obtain ⟨es, os⟩ := ihs hw.1 hps
    obtain ⟨et, ot⟩ := iht hw.2 hpt
    have hsum := (hadd _ (hps _ (vrVal_mem l s)) _ (hpt _ (vrVal_mem l t)) _
      (hp _ (Finset.mem_insert_self _ _))).1 rfl
    refine ⟨?_, os, ot⟩
    show D (vrVal l s + vrVal l t) = vrImg l μ f s + vrImg l μ f t
    rw [← es, ← et, hsum]

/-- **Two decompositions of one value have one image** under the clauses of `Vl.vlShiftCore` (so the carry
`VrCarry`, quantified over all decompositions, is one inequality per inner reach). -/
theorem vrImg_agree {l β μ : Ordinal.{0}} {f D : Ordinal.{0} → Ordinal.{0}} {Os X Y : Finset Ordinal.{0}}
    (hE : ∀ E : VrE, VrWF l β E → (∀ z ∈ vrPts l E, z ∈ X ∪ Y) →
      D (vrVal l E) = vrImg l μ f E ∧ VrOs l Os E)
    {E₁ E₂ : VrE} (h₁ : VrWF l β E₁) (h₂ : VrWF l β E₂) (p₁ : ∀ z ∈ vrPts l E₁, z ∈ X ∪ Y)
    (p₂ : ∀ z ∈ vrPts l E₂, z ∈ X ∪ Y) (e : vrVal l E₁ = vrVal l E₂) :
    vrImg l μ f E₁ = vrImg l μ f E₂ := by
  rw [← (hE E₁ h₁ p₁).1, ← (hE E₂ h₂ p₂).1, e]

/-- **Realizer maps with the repaired forms**: UPPER at the inner restarts, for every inner restart `λ+g` either
`υ_{λ+β} ≤ r(λ+g)` or a repaired form `VrForm`, and the supply with the carry `VrCarry` give `LrReal S υ_λ υ_{λ+β}`. -/
theorem vrReal_gen {l β : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : upsilon l < Om1)
    (hν : upsilon l < nuC) (hνβ : upsilon (l + β) ≤ nuC)
    (hU : ∀ g, 0 < g → g < β → ω ^ 2 ∣ g → CdUpper S (l + g))
    (hform : ∀ g, 0 < g → g < β → ω ^ 2 ∣ g → upsilon (l + β) ≤ cdR S (l + g) ∨ VrForm S l β g)
    (hsup : ∀ γ < upsilon l, ∀ Os : Finset Ordinal.{0}, (∀ d ∈ Os, d < β) →
      ∃ μ f B, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < upsilon l ∧ μ + B ≤ l ∧ ω ^ 2 ∣ B ∧
        upsilon (μ + B) ≤ cdR S μ ∧ Sl.SlOff f Os B ∧ VrCarry S l β μ f B Os)
    (hstd : Cx.CxStdPairTop S) (hlL : upsilon l ≤ Nc.ncL S (ω + 1)) :
    LrReal S (upsilon l) (upsilon (l + β)) := by
  classical
  intro X Y hX hY _
  have hm := upsilon_normal.strictMono
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have ha : UpsPt (upsilon l) := upsPt_upsilon hl0
  have hlE : InE (upsilon l) := upsPt_inE ha
  have hb1 : upsilon (l + β) ≤ Om1 := hνβ.trans nuC_le_Om1
  -- the inner restarts of `Y` whose reach has a repaired form
  set rr : Ordinal.{0} → Prop := fun y => ∃ g, (0 < g ∧ g < β ∧ ω ^ 2 ∣ g ∧ y = upsilon (l + g)) ∧
    VrForm S l β g with hrrdef
  have hch : ∀ y, rr y → ∃ g, ∃ E : VrE, (0 < g ∧ g < β ∧ ω ^ 2 ∣ g ∧ y = upsilon (l + g)) ∧
      VrWF l β E ∧ vrVal l E = cdR S (l + g) := by
    rintro y ⟨g, hg, E, hW, hv⟩
    exact ⟨g, E, hg, hW, hv⟩
  choose! gE EE hgE hWE hvE using hch
  set T := Y.filter rr with hTdef
  set Y' := Y ∪ T.biUnion (fun y => (vrPts l (EE y)).filter (upsilon l ≤ ·)) with hY'def
  set X' := X ∪ T.biUnion (fun y => (vrPts l (EE y)).filter (· < upsilon l)) with hX'def
  have hX' : ∀ x ∈ X', x < upsilon l := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact hX x hx
    · obtain ⟨u, -, hxu⟩ := Finset.mem_biUnion.1 hx
      exact (Finset.mem_filter.1 hxu).2
  have hY' : ∀ y ∈ Y', upsilon l ≤ y ∧ y < upsilon (l + β) := by
    intro y hy
    rcases Finset.mem_union.1 hy with hy | hy
    · exact hY y hy
    · obtain ⟨u, hu, hyu⟩ := Finset.mem_biUnion.1 hy
      obtain ⟨hyp, hly⟩ := Finset.mem_filter.1 hyu
      have hr := (Finset.mem_filter.1 hu).2
      exact ⟨hly, vrPts_lt ((hgE u hr).1.trans (hgE u hr).2.1) _ (hWE u hr) y hyp⟩
  obtain ⟨D, μ, f, B, γ, Os, hQ, hXγ, hγμ, hW, hres, himg, ⟨hμl, hpi⟩, hmvAll, hubAll, heAll, -, hDid, -⟩ :=
    vlShiftCore (Q := fun μ f B _ Os => VrCarry S l β μ f B Os) hl hl1 hν hνβ
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
  have hDE := vrD_eq (l := l) (β := β) (μ := μ) (γ := γ) (f := f) (D := D) (Os := Os) (X := X') (Y := Y')
    hl0 hb1 hX' hY' hW.fix hW.add hXγ hγμ hBμ hres hpi hmvAll hubAll heAll hDid
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
      rcases hform g hg0 hgβ hgd with hb | hF
      · exact (himg y' (hYY y' hy')).le.trans (hbig hb)
      · have hrr : rr (upsilon (l + g)) := ⟨g, ⟨hg0, hgβ, hgd, rfl⟩, hF⟩
        have hT : upsilon (l + g) ∈ T := Finset.mem_filter.2 ⟨hy, hrr⟩
        have hgg : gE (upsilon (l + g)) = g := by
          have e := (hgE _ hrr).2.2.2
          exact (add_left_cancel (hm.injective e)).symm
        have hv := hvE _ hrr
        rw [hgg] at hv
        set E := EE (upsilon (l + g)) with hEdef
        have hpts : ∀ z ∈ vrPts l E, z ∈ X' ∪ Y' := by
          intro z hz
          by_cases hzl : upsilon l ≤ z
          · exact Finset.mem_union_right _ (Finset.mem_union_right _
              (Finset.mem_biUnion.2 ⟨_, hT, Finset.mem_filter.2 ⟨hz, hzl⟩⟩))
          · exact Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_biUnion.2 ⟨_, hT, Finset.mem_filter.2 ⟨hz, not_le.1 hzl⟩⟩))
        obtain ⟨e1, hOs⟩ := hDE E (hWE _ hrr) hpts
        have hRm : cdR S (l + g) ∈ X' ∪ Y' := hv ▸ hpts _ (vrVal_mem l E)
        have h5 : D y' ≤ D (cdR S (l + g)) :=
          hmono y' (Finset.mem_union_right _ (hYY y' hy')) _ hRm hyr
        rw [← hv, e1] at h5
        exact h5.trans (hfrm E (hWE _ hrr) hv hOs)
    have hge : upsilon (μ + f g) ≤ D y' := by
      rw [← hDy]
      exact (hW.mono (Finset.mem_coe.2 (Finset.mem_union_right _ (hYY _ hy)))
        (Finset.mem_coe.2 (Finset.mem_union_right _ (hYY _ hy'))) hyy).le
    rw [hDy]
    exact le1_of_le_of_le1 hge hle hLow
  · push Not at hr
    exact hW.pair1 y (hYY y hy) y' (hYY y' hy') hay hyy (fun g hg hgd e => hr g hg hgd e) h1

end Googology.Trans.PoR.InaccPsi.R2.Vr

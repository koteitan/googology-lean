import Googology.Trans.PoR.InaccPsi.R2.XuC

/-!
# YhVb: THE CODE SIDE OF `φ(α, ·)` ABOVE `G` AT EVERY LEVEL — THE SHIFTED COUNT AT EVERY BASE ATOM `Γ(j)`

`Xu.xuPsi` writes every `ε`-number in `(G, Γ(1))` as `glPsi α η`, shifting the count at the one strongly critical
level `α = G` above `Ω₁` (where `glPsi G 0 = φ(G, 0) = G` itself is counted).  Above `Γ(1)` there are more strongly
critical levels: the base atoms `Γ(j) = gcG j` (`Gc.gcSet`, the strongly critical ordinals above `Ω₁`).  Here the
count is shifted at EVERY base atom, and the normal form holds for EVERY `ε`-number `e > G` that is not itself an
atom, with no upper bound (so for every layer `c` at once):

* `YhAt α` (`α` is a base atom: strongly critical, above `Ω₁`), `yhAt_iff` (**`YhAt α ↔ ∃ j, α = Γ(j)`**);
* `yhPsi` (**`glPsi α (1 + η)` at the atoms, `glPsi α η` at every other level**), `yhPsi_P`, `yhPsi_notP`,
  `yhPsi_strictMono`, `lt_yhPsi`, `yhPsi_E`, `yhPsi_gt` (**above `Ω₁` and above the level, every level `1 ≤ α`**),
  `yhPsi_lt_of`, `yhPsi_lt_lev`, `yhPsi_lt_lev'`, `yhPsi_inj`, `yhPsi_lt_SC` (**below every atom above `α`, `η`**);
* `yhPsi_surj` (**every non-atom `ε`-number `e > G` is `yhPsi α η`, `1 ≤ α`, `α, η < e`**), `yhK`, `yhI`,
  `yhData_spec`, `yhData_eq`;
* `yhPsi_xu` (**below `Γ(1)` it is `Xu.xuPsi`**: the layer `0` is the instance `c = 0`).

No new axiom.  New definitions: `YhAt`, `yhPsi`, `yhK`, `yhI`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yh

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi
  Googology.Notation.InaccPsi.InaccSeq Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.Xu

/-- **A base atom**: a strongly critical ordinal above `Ω₁`. -/
def YhAt (α : Ordinal.{0}) : Prop := SC α ∧ Om1 < α

theorem yhAt_gcG (j : Ordinal.{0}) : YhAt (gcG j) := ⟨gcG_SC j, by rw [Br.Om1_eq]; exact gcG_Om1_lt j⟩

/-- **The base atoms are the `Γ(j)`.** -/
theorem yhAt_iff {α : Ordinal.{0}} : YhAt α ↔ ∃ j, α = gcG j := by
  constructor
  · rintro ⟨hS, hO⟩
    have hm : α ∈ gcSet := ⟨hS, by rw [← Br.Om1_eq]; exact hO⟩
    obtain ⟨j, hj⟩ := Ordinal.enumOrd_surjective gcSet_unbdd hm
    exact ⟨j, hj.symm⟩
  · rintro ⟨j, rfl⟩; exact yhAt_gcG j

theorem yhAt_G_le {α : Ordinal.{0}} (h : YhAt α) : gcG 0 ≤ α := by
  obtain ⟨j, rfl⟩ := yhAt_iff.1 h; exact gcG_le zero_le

theorem yhAt_veb0 {α : Ordinal.{0}} (h : YhAt α) : veblen α 0 = α := Xf.xf_sc_veb0 h.1

/-! ## The shifted count -/

/-- **The `η`-th ordinal of fixed-point level exactly `α` above `Ω₁` and `α`**: `glPsi α (1 + η)` at a base atom `α`
(skipping `α = φ(α, 0)` itself), `glPsi α η` at every other level. -/
noncomputable def yhPsi (α η : Ordinal.{0}) : Ordinal.{0} := by
  classical
  exact if YhAt α then glPsi α (1 + η) else glPsi α η

theorem yhPsi_at {α : Ordinal.{0}} (h : YhAt α) (η : Ordinal.{0}) : yhPsi α η = glPsi α (1 + η) := by
  unfold yhPsi; rw [if_pos h]

theorem yhPsi_ne {α : Ordinal.{0}} (h : ¬ YhAt α) (η : Ordinal.{0}) : yhPsi α η = glPsi α η := by
  unfold yhPsi; rw [if_neg h]

theorem yhPsi_P (α η : Ordinal.{0}) : LuP α (yhPsi α η) := by
  unfold yhPsi; split_ifs <;> exact glPsi_P _ _

theorem yhPsi_notP (α η : Ordinal.{0}) : ¬ LuP (α + 1) (yhPsi α η) := by
  unfold yhPsi; split_ifs <;> exact glPsi_notP _ _

theorem yhPsi_strictMono (α : Ordinal.{0}) : StrictMono (yhPsi α) := by
  intro a b h
  unfold yhPsi
  split_ifs
  · exact glPsi_strictMono _ ((add_lt_add_iff_left 1).2 h)
  · exact glPsi_strictMono _ h

theorem yhPsi_lt_iff {α η η' : Ordinal.{0}} : yhPsi α η < yhPsi α η' ↔ η < η' :=
  (yhPsi_strictMono α).lt_iff_lt

theorem yhPsi_le_iff {α η η' : Ordinal.{0}} : yhPsi α η ≤ yhPsi α η' ↔ η ≤ η' :=
  (yhPsi_strictMono α).le_iff_le

theorem lt_yhPsi (α η : Ordinal.{0}) : η < yhPsi α η := by
  unfold yhPsi
  split_ifs
  · exact (le_add_self : η ≤ 1 + η).trans_lt (lt_glPsi _ _)
  · exact lt_glPsi _ _

theorem yhPsi_E {α : Ordinal.{0}} (hα : 1 ≤ α) (η : Ordinal.{0}) : InE (yhPsi α η) := luP_E hα (yhPsi_P α η)

/-- **`yhPsi α η` lies above `Ω₁` and above `α`** (every level `1 ≤ α`). -/
theorem yhPsi_gt {α : Ordinal.{0}} (hα1 : 1 ≤ α) (η : Ordinal.{0}) : Om1 < yhPsi α η ∧ α < yhPsi α η := by
  by_cases hA : YhAt α
  · rw [yhPsi_at hA]
    have h1 : 0 < glLam α (1 + η) :=
      lt_of_lt_of_le zero_lt_one ((le_self_add : (1 : Ordinal.{0}) ≤ 1 + η).trans (glLam_ge _ _))
    have h2 : veblen α 0 < glPsi α (1 + η) := by
      unfold glPsi; exact (veblen_lt_veblen_iff_right).2 h1
    rw [yhAt_veb0 hA] at h2
    exact ⟨hA.2.trans h2, h2⟩
  · rw [yhPsi_ne hA]
    rcases lt_or_ge α (gcG 0) with h | h
    · exact glPsi_gt hα1 h η
    · have hne : α < veblen α 0 := by
        refine lt_of_le_of_ne (left_le_veblen α 0) (fun e => hA ?_)
        exact ⟨gl_SC_of_fix e.symm ((gcG_SC 0).1.trans_le h), gl_Om1_lt_G0.trans_le h⟩
      have h2 : α < glPsi α η := by
        unfold glPsi
        exact hne.trans_le ((veblen_le_veblen_iff_right (o := α)).2 zero_le)
      exact ⟨(gl_Om1_lt_G0.trans_le h).trans h2, h2⟩

/-- **Below every fixed point of `φ_α`**: `u ∈ P_{α+1}`, `Ω₁ < u`, `η < u` give `yhPsi α η < u`. -/
theorem yhPsi_lt_of {α u η : Ordinal.{0}} (hu : LuP (α + 1) u) (hOu : Om1 < u) (hη : η < u) :
    yhPsi α η < u := by
  unfold yhPsi
  split_ifs
  · have huE : InE u := luP_E le_add_self hu
    exact glPsi_lt_of hu hOu ((inE_indec huE).add_lt (xu_one_lt_inE huE) hη)
  · exact glPsi_lt_of hu hOu hη

/-- **The comparison across levels** (`α' < α`): `yhPsi α' η' < yhPsi α η ↔ η' < yhPsi α η`. -/
theorem yhPsi_lt_lev {α' α : Ordinal.{0}} (hlt : α' < α) (hα1 : 1 ≤ α) {η' η : Ordinal.{0}} :
    yhPsi α' η' < yhPsi α η ↔ η' < yhPsi α η := by
  refine ⟨fun h => (lt_yhPsi α' η').trans h, fun h => ?_⟩
  exact yhPsi_lt_of (luP_mono le_add_self (add_one_le_of_lt hlt) (yhPsi_P α η)) (yhPsi_gt hα1 η).1 h

/-- **The comparison across levels** (`α < α'`): `yhPsi α' η' < yhPsi α η ↔ yhPsi α' η' ≤ η`. -/
theorem yhPsi_lt_lev' {α' α : Ordinal.{0}} (hlt : α < α') (hα'1 : 1 ≤ α') {η' η : Ordinal.{0}} :
    yhPsi α' η' < yhPsi α η ↔ yhPsi α' η' ≤ η := by
  refine ⟨fun h => ?_, fun h => h.trans_lt (lt_yhPsi α η)⟩
  by_contra hc
  push Not at hc
  exact absurd ((yhPsi_lt_lev hlt hα'1).2 hc) (not_lt.2 h.le)

theorem yhPsi_lev_eq {α' α : Ordinal.{0}} {η' η : Ordinal.{0}} (h : yhPsi α' η' = yhPsi α η) : α' = α := by
  rcases lt_trichotomy α' α with hlt | heq | hlt
  · have h1 : LuP (α' + 1) (yhPsi α η) := luP_mono le_add_self (add_one_le_of_lt hlt) (yhPsi_P α η)
    rw [← h] at h1
    exact absurd h1 (yhPsi_notP α' η')
  · exact heq
  · have h1 : LuP (α + 1) (yhPsi α' η') := luP_mono le_add_self (add_one_le_of_lt hlt) (yhPsi_P α' η')
    rw [h] at h1
    exact absurd h1 (yhPsi_notP α η)

/-- **`(α, η)` is unique.** -/
theorem yhPsi_inj {α' α : Ordinal.{0}} {η' η : Ordinal.{0}} (h : yhPsi α' η' = yhPsi α η) : α' = α ∧ η' = η := by
  obtain rfl := yhPsi_lev_eq h
  exact ⟨rfl, (yhPsi_strictMono α').injective h⟩

/-- **Below a strongly critical bound above `Ω₁`, the level and the index.** -/
theorem yhPsi_lt_SC {b α η : Ordinal.{0}} (hb : SC b) (hOb : Om1 < b) (hα : α < b) (hη : η < b) :
    yhPsi α η < b := by
  have hbE : InE b := Low.opow_eq_self_of_SC hb
  have hlim : IsSuccLimit b := ev_isSuccLimit_of_inE hbE
  have hlam : ∀ η', η' < b → glLam α η' < b := fun η' hη' => by
    by_cases h : glFw α η'
    · rw [glLam_of h]; exact hlim.add_one_lt hη'
    · rw [glLam_of_not h]; exact gl_y0_sum_lt hbE hOb hη'
  unfold yhPsi glPsi
  split_ifs
  · exact hb.2 _ hα _ (hlam _ ((inE_indec hbE).add_lt (xu_one_lt_inE hbE) hη))
  · exact hb.2 _ hα _ (hlam _ hη)

/-- **Every non-atom `ε`-number `e > G` is `yhPsi α η`** with `1 ≤ α` and `α, η` below it. -/
theorem yhPsi_surj {e : Ordinal.{0}} (he : InE e) (hGe : gcG 0 < e) (hnA : ¬ YhAt e) :
    ∃ α, 1 ≤ α ∧ α < e ∧ ∃ η, η < e ∧ yhPsi α η = e := by
  have hOe : Om1 < e := gl_Om1_lt_G0.trans hGe
  have hω : ω ^ e = e := he
  set α := invVeblen₁ e with hαdef
  have h1 : (1 : Ordinal.{0}) ≤ α := by
    have : ω ^ e ∈ Set.range (veblen (1 : Ordinal.{0})) := by
      rw [hω]; have h := vzP_one.2 he; unfold VzP at h; rwa [Nat.cast_one] at h
    exact mem_range_veblen_iff_le_invVeblen₁.1 this
  have hnot : ¬ LuP (α + 1) e := by
    intro hP
    have : ω ^ e ∈ Set.range (veblen (α + 1)) := by rw [hω]; exact hP
    exact absurd (mem_range_veblen_iff_le_invVeblen₁.1 this) (not_le.2 (lt_add_one α))
  set y := invVeblen₂ e with hy
  have hey : veblen α y = e := by
    have := veblen_invVeblen₁_invVeblen₂ e
    rw [hω] at this; exact this
  have hαe : α < e := by
    refine lt_of_le_of_ne (invVeblen₁_le e) (fun h => ?_)
    have h2 : veblen e 0 ≤ e := by
      calc veblen e 0 ≤ veblen e y := (veblen_le_veblen_iff_right).2 zero_le
        _ = veblen α y := by rw [h]
        _ = e := hey
    have h3 : veblen e 0 = e := le_antisymm h2 (left_le_veblen e 0)
    exact hnA ⟨gl_SC_of_fix h3 he.pos, hOe⟩
  have hyP : ¬ LuP (α + 1) y := by
    intro hP
    have := luP_succ.1 hP
    rw [hey] at this
    exact hnot (this ▸ hP)
  have hy0 : glY0 α ≤ y := by
    rcases lt_trichotomy α Om1 with hα | hα | hα
    · rw [glY0_lt hα]
      refine add_one_le_of_lt ?_
      by_contra hc
      push Not at hc
      have := (veblen_le_veblen_iff_right (o := α)).2 hc
      rw [hey, gl_veb_Om1 hα] at this
      exact absurd hOe (not_lt.2 this)
    · rw [hα, glY0_eq, one_le_iff_ne_zero]
      intro h0
      have := hey
      rw [h0, hα, gl_veb_Om1_zero] at this
      exact absurd hOe (this ▸ lt_irrefl _)
    · rw [glY0_gt hα]; exact zero_le
  obtain ⟨η, hη⟩ := glLam_surj hy0 hyP
  have hye : y < e := by
    refine lt_of_le_of_ne (hey ▸ right_le_veblen _ _) (fun h => ?_)
    rw [h] at hyP
    exact hyP (luP_succ.2 (by rw [← h] at hey ⊢; exact hey))
  have hηe : η < e := (glLam_ge α η).trans_lt (hη ▸ hye)
  have hpsi : glPsi α η = e := by unfold glPsi; rw [hη, hey]
  by_cases hA : YhAt α
  · -- an atom level: `η ≠ 0` since `glPsi α 0 = φ(α, 0) = α < e`
    have hη0 : η ≠ 0 := by
      intro h0
      have hα0 : glPsi α 0 = α := by
        unfold glPsi
        rw [glLam_of_not (glFw_zero _), glY0_gt hA.2, add_zero, yhAt_veb0 hA]
      have : e = α := by rw [← hpsi, h0, hα0]
      exact absurd hαe (by rw [this]; exact lt_irrefl _)
    refine ⟨α, h1, hαe, η - 1, (sub_le_self η 1).trans_lt hηe, ?_⟩
    rw [yhPsi_at hA, Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 hη0), hpsi]
  · exact ⟨α, h1, hαe, η, hηe, by rw [yhPsi_ne hA, hpsi]⟩

/-! ## The data of a non-atom `ε`-number code above `G` -/

/-- **The level** of a non-atom `ε`-number code `e > G`. -/
noncomputable def yhK (e : Ordinal.{0}) : Ordinal.{0} := by
  classical
  exact if h : ∃ α, 1 ≤ α ∧ α < e ∧ ∃ η, η < e ∧ yhPsi α η = e then Classical.choose h else 0

/-- **The index** of a non-atom `ε`-number code: `e = yhPsi (yhK e) (yhI e)`. -/
noncomputable def yhI (e : Ordinal.{0}) : Ordinal.{0} := by
  classical
  exact if h : ∃ η, η < e ∧ yhPsi (yhK e) η = e then Classical.choose h else 0

theorem yhData_spec {e : Ordinal.{0}} (he : InE e) (hGe : gcG 0 < e) (hnA : ¬ YhAt e) :
    1 ≤ yhK e ∧ yhK e < e ∧ yhI e < e ∧ yhPsi (yhK e) (yhI e) = e := by
  classical
  have hex := yhPsi_surj he hGe hnA
  have hK : yhK e = Classical.choose hex := by unfold yhK; rw [dif_pos hex]
  obtain ⟨hk1, hke, hη⟩ := Classical.choose_spec hex
  rw [← hK] at hk1 hke hη
  have hI : yhI e = Classical.choose hη := by unfold yhI; rw [dif_pos hη]
  obtain ⟨h1, h2⟩ := Classical.choose_spec hη
  rw [← hI] at h1 h2
  exact ⟨hk1, hke, h1, h2⟩

/-- `yhPsi α η` is never a base atom. -/
theorem yhPsi_notAt {α η : Ordinal.{0}} (hα : 1 ≤ α) : ¬ YhAt (yhPsi α η) := by
  intro hA
  have hE := yhPsi_E hα η
  have hlt : α + 1 < yhPsi α η := (ev_isSuccLimit_of_inE hE).add_one_lt (yhPsi_gt hα η).2
  apply yhPsi_notP α η
  exact ⟨yhPsi α η, Gn.gn_veb_fix hA.1 hlt⟩

theorem yhData_eq {α : Ordinal.{0}} (hα : 1 ≤ α) {η : Ordinal.{0}} (hGe : gcG 0 < yhPsi α η) :
    yhK (yhPsi α η) = α ∧ yhI (yhPsi α η) = η := by
  have hE := yhPsi_E hα η
  obtain ⟨-, -, -, h3⟩ := yhData_spec hE hGe (yhPsi_notAt hα)
  exact yhPsi_inj h3

/-! ## The layer `0` -/

/-- **Below `Γ(1)` the only atom is `G`.** -/
theorem yhAt_lt1 {α : Ordinal.{0}} (hA : YhAt α) (hα : α < gcG 1) : α = gcG 0 := by
  refine le_antisymm ?_ (yhAt_G_le hA)
  by_contra h
  push Not at h
  exact absurd hα (not_lt.2 (xu_G1_le hA.1 h))

/-- **Below `Γ(1)`, `yhPsi` is `Xu.xuPsi`.** -/
theorem yhPsi_xu {α : Ordinal.{0}} (hα : α < gcG 1) (η : Ordinal.{0}) : yhPsi α η = xuPsi α η := by
  by_cases hA : YhAt α
  · have := yhAt_lt1 hA hα
    rw [yhPsi_at hA, this, xuPsi_G]
  · have hne : α ≠ gcG 0 := fun h => hA (h ▸ yhAt_gcG 0)
    rw [yhPsi_ne hA, xuPsi_ne hne]

end Googology.Trans.PoR.InaccPsi.R2.Yh

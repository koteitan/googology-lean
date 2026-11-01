import Googology.Trans.PoR.InaccPsi.R2.XcCode
import Googology.Trans.PoR.InaccPsi.R2.XfG1

/-!
# XuVb: THE CODE SIDE OF `φ(α, ·)` ABOVE `G` UP TO `Γ(1)` (region (A3))

`G = Γ_{Ω₁+1} = gcG 0`, `Γ(1) = gcG 1 = Γ_{Ω₁+2}`, `t₀ = Wj.wjT 0 = ε_{G+1}`.  Region (A3) is the levels `ℓ` with
`G < ℓ < Γ(1)`; `t_{n+1} = φ(t_n, 0)` is cofinal in `Γ(1)` (`Wj.wjA3Cof`), so (A3) ends exactly at `Γ(1)`, the least
strongly critical ordinal above `G` (`xu_G1_le`).

Every `ε`-number `e` with `G < e < Γ(1)` is not strongly critical, so it is `φ(α, y)` with `1 ≤ α < e`.  Wilken's
`ϑˣ(Ω₁·β + t)` counts the ordinals of fixed-point level exactly `β` ABOVE `β`; on the code side `Gl.glPsi α η`
counts them above `Ω₁` from `y₀(α)`.  The two counts agree except at the strongly critical level `α = G`, where
`glPsi G 0 = G` itself is counted.  `xuPsi` shifts that one level: `xuPsi G η = glPsi G (1 + η)`, `xuPsi α η =
glPsi α η` otherwise.

* `xu_G1_le` (**no strongly critical ordinal in `(G, Γ(1))`**), `xu_veb_lt_G1`;
* `xuPsi`, `xuPsi_P`, `xuPsi_notP`, `xuPsi_strictMono`, `lt_xuPsi`, `xuPsi_gt` (**above `Ω₁` and above the level**,
  every level `1 ≤ α < Γ(1)`), `xuPsi_lt_of`, `xuPsi_lt_lev`, `xuPsi_lt_lev'` (**comparison across levels**),
  `xuPsi_inj`, `xuPsi_lt_G1`;
* `xuPsi_surj` (**every `ε`-number in `(G, Γ(1))` is `xuPsi α η`, `1 ≤ α`, `α, η` below it**), `xuK`, `xuI`,
  `xuData_spec`, `xuData_eq`;
* `xu_t0_eq` (**`t₀ = xuPsi 1 G`**).

No new axiom.  New definitions: `xuPsi`, `xuK`, `xuI`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xu

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi
  Googology.Notation.InaccPsi.InaccSeq Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gn

/-- **No strongly critical ordinal lies strictly between `G` and `Γ(1)`.** -/
theorem xu_G1_le {b : Ordinal.{0}} (hb : SC b) (h : gcG 0 < b) : gcG 1 ≤ b :=
  gcG_le_of hb ((gcG_Om1_lt 0).trans h) (fun β hβ => by rw [Order.lt_one_iff.1 hβ]; exact h)

theorem xu_G0_lt_G1 : gcG 0 < gcG 1 := gcG_lt zero_lt_one

theorem xu_G1_E : InE (gcG 1) := Low.opow_eq_self_of_SC (gcG_SC 1)

theorem xu_G1_lim : IsSuccLimit (gcG 1) := ev_isSuccLimit_of_inE xu_G1_E

theorem xu_Om1_lt_G1 : Om1 < gcG 1 := gl_Om1_lt_G0.trans xu_G0_lt_G1

theorem xu_veb_lt_G1 {a b : Ordinal.{0}} (ha : a < gcG 1) (hb : b < gcG 1) : veblen a b < gcG 1 :=
  (gcG_SC 1).2 a ha b hb

theorem xu_one_lt_inE {u : Ordinal.{0}} (hu : InE u) : (1 : Ordinal.{0}) < u :=
  one_lt_omega0.trans (omega0_lt_inE hu)

/-- `α < φ(α, 0)` for `G < α < Γ(1)`. -/
theorem xu_veb_zero_gt {α : Ordinal.{0}} (hGα : gcG 0 < α) (hα : α < gcG 1) : α < veblen α 0 := by
  refine lt_of_le_of_ne (left_le_veblen α 0) (fun h => ?_)
  have hSC := gl_SC_of_fix h.symm ((gcG_SC 0).1.trans hGα)
  exact absurd (xu_G1_le hSC hGα) (not_le.2 hα)

/-! ## The shifted count -/

/-- **The `η`-th ordinal of fixed-point level exactly `α` above `Ω₁` and `α`**: `glPsi G (1 + η)` at the level `G`
(skipping `G = φ(G, 0)` itself), `glPsi α η` at every other level. -/
noncomputable def xuPsi (α η : Ordinal.{0}) : Ordinal.{0} := by
  classical
  exact if α = gcG 0 then glPsi α (1 + η) else glPsi α η

theorem xuPsi_G (η : Ordinal.{0}) : xuPsi (gcG 0) η = glPsi (gcG 0) (1 + η) := by
  unfold xuPsi; rw [if_pos rfl]

theorem xuPsi_ne {α : Ordinal.{0}} (h : α ≠ gcG 0) (η : Ordinal.{0}) : xuPsi α η = glPsi α η := by
  unfold xuPsi; rw [if_neg h]

theorem xuPsi_P (α η : Ordinal.{0}) : LuP α (xuPsi α η) := by
  unfold xuPsi; split_ifs <;> exact glPsi_P _ _

theorem xuPsi_notP (α η : Ordinal.{0}) : ¬ LuP (α + 1) (xuPsi α η) := by
  unfold xuPsi; split_ifs <;> exact glPsi_notP _ _

theorem xuPsi_strictMono (α : Ordinal.{0}) : StrictMono (xuPsi α) := by
  intro a b h
  unfold xuPsi
  split_ifs
  · exact glPsi_strictMono _ ((add_lt_add_iff_left 1).2 h)
  · exact glPsi_strictMono _ h

theorem xuPsi_lt_iff {α η η' : Ordinal.{0}} : xuPsi α η < xuPsi α η' ↔ η < η' :=
  (xuPsi_strictMono α).lt_iff_lt

theorem xuPsi_le_iff {α η η' : Ordinal.{0}} : xuPsi α η ≤ xuPsi α η' ↔ η ≤ η' :=
  (xuPsi_strictMono α).le_iff_le

theorem lt_xuPsi (α η : Ordinal.{0}) : η < xuPsi α η := by
  unfold xuPsi
  split_ifs
  · exact (le_add_self : η ≤ 1 + η).trans_lt (lt_glPsi _ _)
  · exact lt_glPsi _ _

theorem xuPsi_E {α : Ordinal.{0}} (hα : 1 ≤ α) (η : Ordinal.{0}) : InE (xuPsi α η) := luP_E hα (xuPsi_P α η)

/-- **`xuPsi α η` lies above `Ω₁` and above `α`** (`1 ≤ α < Γ(1)`). -/
theorem xuPsi_gt {α : Ordinal.{0}} (hα1 : 1 ≤ α) (hαG : α < gcG 1) (η : Ordinal.{0}) :
    Om1 < xuPsi α η ∧ α < xuPsi α η := by
  rcases lt_trichotomy α (gcG 0) with h | h | h
  · rw [xuPsi_ne h.ne]; exact glPsi_gt hα1 h η
  · rw [h, xuPsi_G]
    have h1 : 0 < glLam (gcG 0) (1 + η) :=
      lt_of_lt_of_le zero_lt_one ((le_self_add : (1 : Ordinal.{0}) ≤ 1 + η).trans (glLam_ge _ _))
    have h2 : veblen (gcG 0) 0 < glPsi (gcG 0) (1 + η) := by
      unfold glPsi; exact (veblen_lt_veblen_iff_right).2 h1
    have h3 : gcG 0 < glPsi (gcG 0) (1 + η) := (left_le_veblen _ _).trans_lt h2
    exact ⟨gl_Om1_lt_G0.trans h3, h3⟩
  · rw [xuPsi_ne h.ne']
    have h2 : α < glPsi α η := by
      unfold glPsi
      exact (xu_veb_zero_gt h hαG).trans_le ((veblen_le_veblen_iff_right (o := α)).2 zero_le)
    exact ⟨(gl_Om1_lt_G0.trans h).trans h2, h2⟩

/-- **Below every fixed point of `φ_α`**: `u ∈ P_{α+1}`, `Ω₁ < u`, `η < u` give `xuPsi α η < u`. -/
theorem xuPsi_lt_of {α u η : Ordinal.{0}} (hu : LuP (α + 1) u) (hOu : Om1 < u) (hη : η < u) :
    xuPsi α η < u := by
  unfold xuPsi
  split_ifs
  · have huE : InE u := luP_E le_add_self hu
    exact glPsi_lt_of hu hOu ((inE_indec huE).add_lt (xu_one_lt_inE huE) hη)
  · exact glPsi_lt_of hu hOu hη

/-- **The comparison across levels** (`α' < α`): `xuPsi α' η' < xuPsi α η ↔ η' < xuPsi α η`. -/
theorem xuPsi_lt_lev {α' α : Ordinal.{0}} (hlt : α' < α) (hα1 : 1 ≤ α) (hαG : α < gcG 1) {η' η : Ordinal.{0}} :
    xuPsi α' η' < xuPsi α η ↔ η' < xuPsi α η := by
  refine ⟨fun h => (lt_xuPsi α' η').trans h, fun h => ?_⟩
  exact xuPsi_lt_of (luP_mono le_add_self (add_one_le_of_lt hlt) (xuPsi_P α η)) (xuPsi_gt hα1 hαG η).1 h

/-- **The comparison across levels** (`α < α'`): `xuPsi α' η' < xuPsi α η ↔ xuPsi α' η' ≤ η`. -/
theorem xuPsi_lt_lev' {α' α : Ordinal.{0}} (hlt : α < α') (hα'1 : 1 ≤ α') (hα'G : α' < gcG 1)
    {η' η : Ordinal.{0}} : xuPsi α' η' < xuPsi α η ↔ xuPsi α' η' ≤ η := by
  refine ⟨fun h => ?_, fun h => h.trans_lt (lt_xuPsi α η)⟩
  by_contra hc
  push Not at hc
  exact absurd ((xuPsi_lt_lev hlt hα'1 hα'G).2 hc) (not_lt.2 h.le)

theorem xuPsi_lev_eq {α' α : Ordinal.{0}} (hα'1 : 1 ≤ α') (hα1 : 1 ≤ α) {η' η : Ordinal.{0}}
    (h : xuPsi α' η' = xuPsi α η) : α' = α := by
  rcases lt_trichotomy α' α with hlt | heq | hlt
  · have h1 : LuP (α' + 1) (xuPsi α η) := luP_mono le_add_self (add_one_le_of_lt hlt) (xuPsi_P α η)
    rw [← h] at h1
    exact absurd h1 (xuPsi_notP α' η')
  · exact heq
  · have h1 : LuP (α + 1) (xuPsi α' η') := luP_mono le_add_self (add_one_le_of_lt hlt) (xuPsi_P α' η')
    rw [h] at h1
    exact absurd h1 (xuPsi_notP α η)

/-- **`(α, η)` is unique.** -/
theorem xuPsi_inj {α' α : Ordinal.{0}} (hα'1 : 1 ≤ α') (hα1 : 1 ≤ α) {η' η : Ordinal.{0}}
    (h : xuPsi α' η' = xuPsi α η) : α' = α ∧ η' = η := by
  obtain rfl := xuPsi_lev_eq hα'1 hα1 h
  exact ⟨rfl, (xuPsi_strictMono α').injective h⟩

theorem xuLam_lt_G1 {α η : Ordinal.{0}} (hη : η < gcG 1) : glLam α η < gcG 1 := by
  by_cases h : glFw α η
  · rw [glLam_of h]; exact xu_G1_lim.add_one_lt hη
  · rw [glLam_of_not h]; exact gl_y0_sum_lt xu_G1_E xu_Om1_lt_G1 hη

theorem xuPsi_lt_G1 {α η : Ordinal.{0}} (hα : α < gcG 1) (hη : η < gcG 1) : xuPsi α η < gcG 1 := by
  unfold xuPsi glPsi
  split_ifs
  · exact xu_veb_lt_G1 hα (xuLam_lt_G1 ((inE_indec xu_G1_E).add_lt (xu_one_lt_inE xu_G1_E) hη))
  · exact xu_veb_lt_G1 hα (xuLam_lt_G1 hη)

/-- **Every `ε`-number in `(G, Γ(1))` is `xuPsi α η`** with `1 ≤ α` and `α, η` below it. -/
theorem xuPsi_surj {e : Ordinal.{0}} (he : InE e) (hGe : gcG 0 < e) (heG : e < gcG 1) :
    ∃ α, 1 ≤ α ∧ α < e ∧ ∃ η, η < e ∧ xuPsi α η = e := by
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
    exact absurd heG (not_lt.2 (xu_G1_le (gl_SC_of_fix h3 he.pos) hGe))
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
  by_cases hαG : α = gcG 0
  · -- the level `G`: `η ≠ 0` since `glPsi G 0 = φ(G, 0) = G < e`
    have hη0 : η ≠ 0 := by
      intro h0
      have hG0 : glPsi (gcG 0) 0 = gcG 0 := by
        unfold glPsi
        rw [glLam_of_not (glFw_zero _), glY0_gt gl_Om1_lt_G0, add_zero, Xf.xf_sc_veb0 (gcG_SC 0)]
      have : e = gcG 0 := by rw [← hpsi, hαG, h0, hG0]
      exact absurd hGe (by rw [this]; exact lt_irrefl _)
    refine ⟨α, h1, hαe, η - 1, (sub_le_self η 1).trans_lt hηe, ?_⟩
    rw [hαG, xuPsi_G, Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 hη0), ← hαG, hpsi]
  · exact ⟨α, h1, hαe, η, hηe, by rw [xuPsi_ne hαG, hpsi]⟩

/-! ## The data of an `ε`-number code in `(G, Γ(1))` -/

/-- **The level** of an `ε`-number code `e ∈ (G, Γ(1))`. -/
noncomputable def xuK (e : Ordinal.{0}) : Ordinal.{0} := by
  classical
  exact if h : ∃ α, 1 ≤ α ∧ α < e ∧ ∃ η, η < e ∧ xuPsi α η = e then Classical.choose h else 0

/-- **The index** of an `ε`-number code: `e = xuPsi (xuK e) (xuI e)`. -/
noncomputable def xuI (e : Ordinal.{0}) : Ordinal.{0} := by
  classical
  exact if h : ∃ η, η < e ∧ xuPsi (xuK e) η = e then Classical.choose h else 0

theorem xuData_spec {e : Ordinal.{0}} (he : InE e) (hGe : gcG 0 < e) (heG : e < gcG 1) :
    1 ≤ xuK e ∧ xuK e < e ∧ xuI e < e ∧ xuPsi (xuK e) (xuI e) = e := by
  classical
  have hex := xuPsi_surj he hGe heG
  have hK : xuK e = Classical.choose hex := by unfold xuK; rw [dif_pos hex]
  obtain ⟨hk1, hke, hη⟩ := Classical.choose_spec hex
  rw [← hK] at hk1 hke hη
  have hI : xuI e = Classical.choose hη := by unfold xuI; rw [dif_pos hη]
  obtain ⟨h1, h2⟩ := Classical.choose_spec hη
  rw [← hI] at h1 h2
  exact ⟨hk1, hke, h1, h2⟩

/-- `xuPsi α η` above `G`: either `G ≤ α` (and `(α, η) ≠ (G, ·)` gives more), or the argument is above `G`. -/
theorem xuData_eq {α : Ordinal.{0}} (hα : 1 ≤ α) (hαG : α < gcG 1) {η : Ordinal.{0}} (hηG : η < gcG 1)
    (hGe : gcG 0 < xuPsi α η) : xuK (xuPsi α η) = α ∧ xuI (xuPsi α η) = η := by
  have hE := xuPsi_E hα η
  obtain ⟨h1, -, -, h3⟩ := xuData_spec hE hGe (xuPsi_lt_G1 hαG hηG)
  exact xuPsi_inj h1 hα h3

/-! ## `t₀ = ε_{G+1} = xuPsi 1 G` -/

theorem xu_two_lt_G : (2 : Ordinal.{0}) < gcG 0 :=
  (show (2 : Ordinal.{0}) < ω by exact_mod_cast natCast_lt_omega0 2).trans (omega0_lt_inE gl_G0_E)

theorem xu_G_fix1 : glF 1 (gcG 0) := by
  refine ⟨⟨gcG 0, ?_⟩, gl_Om1_lt_G0⟩
  rw [show (1 : Ordinal.{0}) + 1 = 2 by norm_num]
  exact gn_veb_fix (gcG_SC 0) xu_two_lt_G

/-- **`t₀ = ε_{G+1} = xuPsi 1 G`.** -/
theorem xu_t0_eq : xuPsi 1 (gcG 0) = Wj.wjT 0 := by
  have h1 : (1 : Ordinal.{0}) ≠ gcG 0 := (gl_one_lt_G0).ne
  have hFw : glFw 1 (gcG 0) := ⟨gcG 0, xu_G_fix1, 0, by simp⟩
  rw [xuPsi_ne h1]
  unfold glPsi
  rw [glLam_of hFw]
  rfl

theorem xu_G_lt_t0 : gcG 0 < Wj.wjT 0 := (Wj.wjT_spec 0).1

theorem xu_t0_lt_G1 : Wj.wjT 0 < gcG 1 := (Wj.wjT_spec 0).2.1

theorem xu_t0_E : InE (Wj.wjT 0) := (Wj.wjT_spec 0).2.2.1

/-- **`t₀` is a code with data `(1, G)`.** -/
theorem xu_t0_data : xuK (Wj.wjT 0) = 1 ∧ xuI (Wj.wjT 0) = gcG 0 := by
  rw [← xu_t0_eq]
  exact xuData_eq le_rfl (gl_one_lt_G0.trans xu_G0_lt_G1) xu_G0_lt_G1 (xu_t0_eq ▸ xu_G_lt_t0)

/-- Every `ε`-number `e ≥ t₀` below `Γ(1)` is above `G`. -/
theorem xu_G_lt_of {e : Ordinal.{0}} (he : Wj.wjT 0 ≤ e) : gcG 0 < e := xu_G_lt_t0.trans_le he

end Googology.Trans.PoR.InaccPsi.R2.Xu

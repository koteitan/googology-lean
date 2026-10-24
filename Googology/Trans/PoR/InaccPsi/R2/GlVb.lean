import Googology.Trans.PoR.InaccPsi.R2.GlPkg

/-!
# THE CODE SIDE OF `φ(α, ·)` FOR EVERY LEVEL `1 ≤ α < Γ_{Ω₁+1}`: the ordinals of fixed-point level exactly `α`

Wilken's `ϑˣ(Ω₁·β + η)` is the `η`-th ordinal of fixed-point level exactly `β` above `x` and `β` (`R2.LvLev`, every
level `β ∈ Tˣ ∩ Ω₁`).  On the code side the same enumeration above `Ω₁` and `α` is `glPsi α η = φ(α, Λ_α(η))`,
where `Λ_α` enumerates the arguments `y ≥ y₀(α)` that are not fixed points of `φ_α` (`y₀ = Ω₁ + 1` for `α < Ω₁`,
`1` for `α = Ω₁`, `0` above): with `F_α` the fixed points of `φ_α` above `Ω₁` (`glF`), `Λ_α(η) = η + 1` if `η = f + n`
(`f ∈ F_α`, `n < ω`), else `y₀ + η` (`glLam`).

* `gl_veb_Om1` (`φ(o, Ω₁) = Ω₁` for `o < Ω₁`), `gl_veb_Om1_zero` (`φ(Ω₁, 0) = Ω₁`), `gl_G0_le` (**`Γ_{Ω₁+1}` is the
  least strongly critical ordinal above `Ω₁`**), `gl_veb_zero_gt` (`α < φ(α, 0)` for `Ω₁ < α < Γ_{Ω₁+1}`);
* `glF`, `glFw`, `glY0`, `glLam`, `glLam_strictMono`, `glLam_notP` (**`Λ_α(η)` is never a fixed point of `φ_α`**),
  `glLam_surj` (**every non-fixed argument `y ≥ y₀(α)` is a `Λ_α(η)`**), `glLam_ge`;
* `glPsi` (**`φ(α, Λ_α(η))`**), `glPsi_P`, `glPsi_notP` (**level exactly `α`**), `glPsi_strictMono`, `glPsi_gt`
  (above `Ω₁` and `α`), `lt_glPsi`, `glPsi_E`, `glPsi_lt_of`, `glPsi_lt_lev`, `glPsi_lt_lev'` (**the comparison across
  levels**), `glPsi_inj`, `glPsi_lt_G`;
* `glPsi_surj` (**every `ε`-number in `(Ω₁, Γ_{Ω₁+1})` is `glPsi α η` with `1 ≤ α`, `α, η` below it**);
* `glK`, `glI` (the level and the index of an `ε`-number code), `glData_spec`, `glData_eq`;
* `glB` (`φ(ω, Ω₁+1)`), `glB_lt_G0`, `glB_mem`.

No new axiom.  New definitions: `glF`, `glFw`, `glY0`, `glLam`, `glPsi`, `glK`, `glI`, `glB`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gl

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi
  Googology.Notation.InaccPsi.InaccSeq Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Lu

theorem gl_Om1_E : InE Om1 := Rj.rj_Om1_inE

theorem gl_Om1_lim : IsSuccLimit Om1 := by rw [Br.Om1_eq]; exact InaccSeq.Om_isSuccLimit one_ne_zero

/-- `φ(o, Ω₁) = Ω₁` for every `o < Ω₁`. -/
theorem gl_veb_Om1 {o : Ordinal.{0}} (ho : o < Om1) : veblen o Om1 = Om1 := by
  refine le_antisymm (((isNormal_veblen o).le_iff_forall_le gl_Om1_lim).2 fun c hc => ?_) (right_le_veblen o Om1)
  have h := Ph.ph_SC_Om1.2 o (by rw [← Br.Om1_eq]; exact ho) c (by rw [← Br.Om1_eq]; exact hc)
  rw [← Br.Om1_eq] at h
  exact h.le

theorem gl_nat_lt_Om1 (k : ℕ) : (k : Ordinal.{0}) < Om1 := (natCast_lt_omega0 k).trans omega_lt_Om1

/-- **`φ(Ω₁, 0) = Ω₁`.** -/
theorem gl_veb_Om1_zero : veblen Om1 0 = Om1 := by
  have hO : Om1 ∈ Set.range (veblen Om1) :=
    (mem_range_veblen (gl_Om1_E.pos.ne')).2 fun b hb => gl_veb_Om1 hb
  obtain ⟨z, hz⟩ := hO
  refine le_antisymm ?_ (by simpa using left_le_veblen Om1 0)
  exact ((veblen_le_veblen_iff_right).2 zero_le).trans_eq hz

/-- **`Γ_{Ω₁+1}` is the least strongly critical ordinal above `Ω₁`.** -/
theorem gl_G0_le {b : Ordinal.{0}} (hb : SC b) (h1 : Om1 < b) : gcG 0 ≤ b := by
  rw [gcG, enumOrd_zero]
  exact csInf_le' ⟨hb, by rw [← Br.Om1_eq]; exact h1⟩

/-- A fixed point `α = φ(α, 0)` is strongly critical. -/
theorem gl_SC_of_fix {α : Ordinal.{0}} (hα : veblen α 0 = α) (h0 : 0 < α) : SC α := by
  refine ⟨h0, fun a ha b hb => ?_⟩
  have h1 : veblen a b < veblen a α := (veblen_lt_veblen_iff_right).2 hb
  have h2 : veblen a α = α := by
    conv_lhs => rw [← hα]
    rw [veblen_veblen_of_lt (by rw [hα] at *; exact ha), hα]
  rwa [h2] at h1

/-- `α < φ(α, 0)` for `Ω₁ < α < Γ_{Ω₁+1}`. -/
theorem gl_veb_zero_gt {α : Ordinal.{0}} (hOα : Om1 < α) (hαG : α < gcG 0) : α < veblen α 0 := by
  refine lt_of_le_of_ne (by simpa using left_le_veblen α 0) (fun h => ?_)
  have := gl_G0_le (gl_SC_of_fix h.symm (lt_of_le_of_lt zero_le hOα)) hOα
  exact absurd hαG (not_lt.2 this)

theorem gl_G0_E : InE (gcG 0) := Low.opow_eq_self_of_SC (gcG_SC 0)

theorem gl_Om1_lt_G0 : Om1 < gcG 0 := by rw [Br.Om1_eq]; exact gcG_Om1_lt 0

theorem gl_veb_lt_G0 {a b : Ordinal.{0}} (ha : a < gcG 0) (hb : b < gcG 0) : veblen a b < gcG 0 :=
  (gcG_SC 0).2 a ha b hb

theorem gl_G0_lim : IsSuccLimit (gcG 0) := ev_isSuccLimit_of_inE gl_G0_E

/-- `Ω₁ + 1 + u = u` for every `ε`-number `u > Ω₁`. -/
theorem gl_absorb {u : Ordinal.{0}} (hu : InE u) (hOu : Om1 < u) : Om1 + 1 + u = u :=
  add_of_omega0_opow_le (by rw [hu]; exact (ev_isSuccLimit_of_inE hu).add_one_lt hOu) hu.le

theorem gl_sum_lt {u η : Ordinal.{0}} (hu : InE u) (hOu : Om1 < u) (hη : η < u) : Om1 + 1 + η < u :=
  (inE_indec hu).add_lt ((ev_isSuccLimit_of_inE hu).add_one_lt hOu) hη

/-! ## The arguments `Λ_α` -/

/-- **The fixed points of `φ_α` above `Ω₁`.** -/
def glF (α f : Ordinal.{0}) : Prop := LuP (α + 1) f ∧ Om1 < f

/-- `η = f + n` for a fixed point `f ∈ F_α` and `n < ω`. -/
def glFw (α η : Ordinal.{0}) : Prop := ∃ f, glF α f ∧ ∃ n : ℕ, η = f + n

/-- **The first argument** `y₀(α)` with `φ(α, y₀) > Ω₁, α`: `Ω₁ + 1` for `α < Ω₁`, `1` for `α = Ω₁`, `0` above. -/
noncomputable def glY0 (α : Ordinal.{0}) : Ordinal.{0} := by
  classical
  exact if α < Om1 then Om1 + 1 else if α = Om1 then 1 else 0

/-- **The `η`-th non-fixed argument `≥ y₀(α)`**: `η + 1` after a fixed point (`η ∈ F_α + ω`), else `y₀(α) + η`. -/
noncomputable def glLam (α η : Ordinal.{0}) : Ordinal.{0} := by
  classical
  exact if glFw α η then η + 1 else glY0 α + η

theorem glY0_le (α : Ordinal.{0}) : glY0 α ≤ Om1 + 1 := by
  unfold glY0; split_ifs
  · exact le_rfl
  · exact le_add_self
  · exact zero_le

theorem glY0_lt {α : Ordinal.{0}} (hα : α < Om1) : glY0 α = Om1 + 1 := by unfold glY0; rw [if_pos hα]

theorem glY0_eq : glY0 Om1 = 1 := by unfold glY0; rw [if_neg (lt_irrefl _), if_pos rfl]

theorem glY0_gt {α : Ordinal.{0}} (hα : Om1 < α) : glY0 α = 0 := by
  unfold glY0; rw [if_neg (not_lt.2 hα.le), if_neg hα.ne']

theorem glF_E {α f : Ordinal.{0}} (h : glF α f) : InE f := luP_E le_add_self h.1

/-- `y₀(α) + v = v` above every `ε`-number `u > Ω₁` with `u ≤ v`. -/
theorem gl_absorb_le {α u v : Ordinal.{0}} (hu : InE u) (hOu : Om1 < u) (huv : u ≤ v) : glY0 α + v = v :=
  add_of_omega0_opow_le (by rw [hu]; exact (glY0_le α).trans_lt ((ev_isSuccLimit_of_inE hu).add_one_lt hOu))
    (by rw [hu]; exact huv)

theorem gl_y0_sum_lt {α u η : Ordinal.{0}} (hu : InE u) (hOu : Om1 < u) (hη : η < u) : glY0 α + η < u :=
  (inE_indec hu).add_lt ((glY0_le α).trans_lt ((ev_isSuccLimit_of_inE hu).add_one_lt hOu)) hη

theorem glLam_of {α η : Ordinal.{0}} (h : glFw α η) : glLam α η = η + 1 := by
  unfold glLam; rw [if_pos h]

theorem glLam_of_not {α η : Ordinal.{0}} (h : ¬ glFw α η) : glLam α η = glY0 α + η := by
  unfold glLam; rw [if_neg h]

theorem glFw_ge {α η : Ordinal.{0}} (h : glFw α η) : ∃ f, glF α f ∧ f ≤ η := by
  obtain ⟨f, hf, n, rfl⟩ := h
  exact ⟨f, hf, le_self_add⟩

theorem glFw_zero (α : Ordinal.{0}) : ¬ glFw α 0 := by
  rintro ⟨f, hf, n, hn⟩
  have : f ≤ 0 := hn ▸ le_self_add
  exact absurd (hf.2.trans_le this) (not_lt.2 zero_le)

theorem glLam_ge (α η : Ordinal.{0}) : η ≤ glLam α η := by
  by_cases h : glFw α η
  · rw [glLam_of h]; exact (lt_add_one η).le
  · rw [glLam_of_not h]; exact le_add_self

theorem glLam_ge0 (α η : Ordinal.{0}) : glY0 α ≤ glLam α η := by
  by_cases h : glFw α η
  · rw [glLam_of h]
    obtain ⟨f, hf, hfη⟩ := glFw_ge h
    exact ((glY0_le α).trans ((ev_isSuccLimit_of_inE (glF_E hf)).add_one_lt hf.2).le).trans
      (hfη.trans (lt_add_one η).le)
  · rw [glLam_of_not h]; exact le_self_add

theorem glLam_strictMono (α : Ordinal.{0}) : StrictMono (glLam α) := by
  intro η η' hlt
  by_cases h1 : glFw α η <;> by_cases h2 : glFw α η'
  · rw [glLam_of h1, glLam_of h2]; exact Order.lt_add_one_iff.2 (add_one_le_of_lt hlt)
  · rw [glLam_of h1, glLam_of_not h2]
    obtain ⟨f, hf, n, rfl⟩ := h1
    have hfE := glF_E hf
    rw [gl_absorb_le hfE hf.2 (le_self_add.trans hlt.le)]
    rcases (add_one_le_of_lt hlt).lt_or_eq with h3 | h3
    · exact h3
    · exfalso; apply h2; exact ⟨f, hf, n + 1, by rw [← h3, Nat.cast_succ, add_assoc]⟩
  · rw [glLam_of_not h1, glLam_of h2]
    obtain ⟨f', hf', n', rfl⟩ := h2
    have hfE := glF_E hf'
    rcases lt_or_ge η f' with h3 | h3
    · exact (gl_y0_sum_lt hfE hf'.2 h3).trans_le (le_self_add.trans (lt_add_one _).le)
    · rw [gl_absorb_le hfE hf'.2 h3]; exact hlt.trans (lt_add_one _)
  · rw [glLam_of_not h1, glLam_of_not h2]; exact (add_lt_add_iff_left _).2 hlt

/-- An element of `P_{α+1}` lies above `Ω₁` when `Ω₁ ≤ α`. -/
theorem gl_P_gt {α f : Ordinal.{0}} (hP : LuP (α + 1) f) (h : Om1 ≤ α) : Om1 < f := by
  obtain ⟨j, rfl⟩ := hP
  exact h.trans_lt ((lt_add_one α).trans_le (by simpa using left_le_veblen (α + 1) j))

/-- **`Λ_α(η)` is never a fixed point of `φ_α`.** -/
theorem glLam_notP (α η : Ordinal.{0}) : ¬ LuP (α + 1) (glLam α η) := by
  intro hP
  have hE : InE (glLam α η) := luP_E le_add_self hP
  by_cases h : glFw α η
  · rw [glLam_of h] at hE
    exact Order.not_isSuccLimit_succ η (by rw [succ_eq_add_one]; exact ev_isSuccLimit_of_inE hE)
  · rw [glLam_of_not h] at hP hE
    have hO : Om1 < glY0 α + η := by
      rcases lt_or_ge α Om1 with hα | hα
      · rw [glY0_lt hα, add_assoc]; exact lt_add_of_pos_right _ (lt_of_lt_of_le zero_lt_one le_self_add)
      · exact gl_P_gt hP hα
    rcases (show η ≤ glY0 α + η from le_add_self).lt_or_eq with h3 | h3
    · exact absurd (gl_y0_sum_lt hE hO h3) (lt_irrefl _)
    · exact h ⟨glY0 α + η, ⟨hP, hO⟩, 0, by rw [Nat.cast_zero, add_zero]; exact h3⟩

/-- **Every argument `y ≥ y₀(α)` that is not a fixed point of `φ_α` is some `Λ_α(η)`.** -/
theorem glLam_surj {α y : Ordinal.{0}} (hy : glY0 α ≤ y) (hP : ¬ LuP (α + 1) y) : ∃ η, glLam α η = y := by
  classical
  by_cases hs : ∃ f, glF α f ∧ ∃ n : ℕ, y = f + n + 1
  · obtain ⟨f, hf, n, rfl⟩ := hs
    exact ⟨f + n, glLam_of ⟨f, hf, n, rfl⟩⟩
  · refine ⟨y - glY0 α, ?_⟩
    have e : glY0 α + (y - glY0 α) = y := Ordinal.add_sub_cancel_of_le hy
    have hnot : ¬ glFw α (y - glY0 α) := by
      rintro ⟨f, hf, n, hn⟩
      have hfE := glF_E hf
      have e2 : y = f + n := by rw [← e, hn, ← add_assoc, gl_absorb_le hfE hf.2 le_rfl]
      rcases n with _ | m
      · rw [Nat.cast_zero, add_zero] at e2
        exact hP (e2 ▸ hf.1)
      · exact hs ⟨f, hf, m, by rw [e2, Nat.cast_succ, add_assoc]⟩
    rw [glLam_of_not hnot, e]


/-! ## `glPsi α η = φ(α, Λ_α(η))` -/

/-- **The `η`-th ordinal above `Ω₁` and `α` of fixed-point level exactly `α`**: `φ(α, Λ_α(η))`. -/
noncomputable def glPsi (α η : Ordinal.{0}) : Ordinal.{0} := veblen α (glLam α η)

theorem glPsi_P (α η : Ordinal.{0}) : LuP α (glPsi α η) := luP_veblen α _

theorem gl_veb_ne {α y : Ordinal.{0}} (hP : ¬ LuP (α + 1) y) : veblen α y ≠ y :=
  fun h => hP (luP_succ.2 h)

/-- **Level exactly `α`**: `glPsi α η` is not a fixed point of `φ_α`. -/
theorem glPsi_notP (α η : Ordinal.{0}) : ¬ LuP (α + 1) (glPsi α η) := by
  intro h
  have h1 := luP_succ.1 h
  unfold glPsi at h1
  exact gl_veb_ne (glLam_notP α η) ((veblen_injective _) h1)

theorem glPsi_strictMono (α : Ordinal.{0}) : StrictMono (glPsi α) :=
  fun _ _ h => (veblen_lt_veblen_iff_right).2 (glLam_strictMono α h)

theorem glPsi_lt_iff {α η η' : Ordinal.{0}} : glPsi α η < glPsi α η' ↔ η < η' :=
  (glPsi_strictMono α).lt_iff_lt

theorem glPsi_le_iff {α η η' : Ordinal.{0}} : glPsi α η ≤ glPsi α η' ↔ η ≤ η' :=
  (glPsi_strictMono α).le_iff_le

/-- **`glPsi α η` lies above `Ω₁` and above `α`** (`1 ≤ α < Γ_{Ω₁+1}`). -/
theorem glPsi_gt {α : Ordinal.{0}} (hα1 : 1 ≤ α) (hαG : α < gcG 0) (η : Ordinal.{0}) :
    Om1 < glPsi α η ∧ α < glPsi α η := by
  unfold glPsi
  rcases lt_trichotomy α Om1 with hα | rfl | hα
  · have h1 : Om1 < glLam α η := by
      have := glLam_ge0 α η; rw [glY0_lt hα] at this; exact (lt_add_one Om1).trans_le this
    have h2 := (veblen_lt_veblen_iff_right (o := α)).2 h1
    rw [gl_veb_Om1 hα] at h2
    exact ⟨h2, hα.trans h2⟩
  · have h1 : 0 < glLam Om1 η := by
      have := glLam_ge0 Om1 η; rw [glY0_eq] at this; exact zero_lt_one.trans_le this
    have h2 := (veblen_lt_veblen_iff_right (o := Om1)).2 h1
    rw [gl_veb_Om1_zero] at h2
    exact ⟨h2, h2⟩
  · have h1 := (gl_veb_zero_gt hα hαG).trans_le ((veblen_le_veblen_iff_right (o := α)).2 (zero_le : 0 ≤ glLam α η))
    exact ⟨hα.trans h1, h1⟩

theorem glLam_lt_glPsi (α η : Ordinal.{0}) : glLam α η < glPsi α η :=
  lt_of_le_of_ne (right_le_veblen _ _) (gl_veb_ne (glLam_notP α η)).symm

theorem lt_glPsi (α η : Ordinal.{0}) : η < glPsi α η := (glLam_ge α η).trans_lt (glLam_lt_glPsi α η)

theorem glPsi_E {α : Ordinal.{0}} (hα : 1 ≤ α) (η : Ordinal.{0}) : InE (glPsi α η) := luP_E hα (glPsi_P α η)

/-- **Below every fixed point of `φ_α`**: `u ∈ P_{α+1}`, `Ω₁ < u`, `η < u` give `glPsi α η < u`. -/
theorem glPsi_lt_of {α u η : Ordinal.{0}} (hu : LuP (α + 1) u) (hOu : Om1 < u) (hη : η < u) :
    glPsi α η < u := by
  have huE : InE u := luP_E le_add_self hu
  have hlam : glLam α η < u := by
    by_cases h : glFw α η
    · rw [glLam_of h]; exact (ev_isSuccLimit_of_inE huE).add_one_lt hη
    · rw [glLam_of_not h]; exact gl_y0_sum_lt huE hOu hη
  have := (veblen_lt_veblen_iff_right (o := α)).2 hlam
  rwa [luP_succ.1 hu] at this

/-- **The comparison across levels** (`α' < α`): `glPsi α' η' < glPsi α η ↔ η' < glPsi α η`. -/
theorem glPsi_lt_lev {α' α : Ordinal.{0}} (hlt : α' < α) (hα1 : 1 ≤ α) (hαG : α < gcG 0) {η' η : Ordinal.{0}} :
    glPsi α' η' < glPsi α η ↔ η' < glPsi α η := by
  refine ⟨fun h => (lt_glPsi α' η').trans h, fun h => ?_⟩
  exact glPsi_lt_of (luP_mono le_add_self (add_one_le_of_lt hlt) (glPsi_P α η)) (glPsi_gt hα1 hαG η).1 h

/-- **The comparison across levels** (`α < α'`): `glPsi α' η' < glPsi α η ↔ glPsi α' η' ≤ η`. -/
theorem glPsi_lt_lev' {α' α : Ordinal.{0}} (hlt : α < α') (hα'1 : 1 ≤ α') (hα'G : α' < gcG 0)
    {η' η : Ordinal.{0}} : glPsi α' η' < glPsi α η ↔ glPsi α' η' ≤ η := by
  refine ⟨fun h => ?_, fun h => h.trans_lt (lt_glPsi α η)⟩
  by_contra hc
  push Not at hc
  exact absurd ((glPsi_lt_lev hlt hα'1 hα'G).2 hc) (not_lt.2 h.le)

theorem glPsi_lev_eq {α' α : Ordinal.{0}} (hα'1 : 1 ≤ α') (hα1 : 1 ≤ α) {η' η : Ordinal.{0}}
    (h : glPsi α' η' = glPsi α η) : α' = α := by
  rcases lt_trichotomy α' α with hlt | heq | hlt
  · have h1 : LuP (α' + 1) (glPsi α η) := luP_mono le_add_self (add_one_le_of_lt hlt) (glPsi_P α η)
    rw [← h] at h1
    exact absurd h1 (glPsi_notP α' η')
  · exact heq
  · have h1 : LuP (α + 1) (glPsi α' η') := luP_mono le_add_self (add_one_le_of_lt hlt) (glPsi_P α' η')
    rw [h] at h1
    exact absurd h1 (glPsi_notP α η)

/-- **`(α, η)` is unique.** -/
theorem glPsi_inj {α' α : Ordinal.{0}} (hα'1 : 1 ≤ α') (hα1 : 1 ≤ α) {η' η : Ordinal.{0}}
    (h : glPsi α' η' = glPsi α η) : α' = α ∧ η' = η := by
  obtain rfl := glPsi_lev_eq hα'1 hα1 h
  exact ⟨rfl, (glPsi_strictMono α').injective h⟩

theorem glLam_lt_G {α η : Ordinal.{0}} (hη : η < gcG 0) : glLam α η < gcG 0 := by
  by_cases h : glFw α η
  · rw [glLam_of h]; exact gl_G0_lim.add_one_lt hη
  · rw [glLam_of_not h]; exact gl_y0_sum_lt gl_G0_E gl_Om1_lt_G0 hη

theorem glPsi_lt_G {α η : Ordinal.{0}} (hα : α < gcG 0) (hη : η < gcG 0) : glPsi α η < gcG 0 :=
  gl_veb_lt_G0 hα (glLam_lt_G hη)

/-- **Every `ε`-number in `(Ω₁, Γ_{Ω₁+1})` is `glPsi α η`** with `1 ≤ α` and `α, η` below it. -/
theorem glPsi_surj {e : Ordinal.{0}} (he : InE e) (hOe : Om1 < e) (heG : e < gcG 0) :
    ∃ α, 1 ≤ α ∧ α < e ∧ ∃ η, η < e ∧ glPsi α η = e := by
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
    have h3 : veblen e 0 = e := le_antisymm h2 (by simpa using left_le_veblen e 0)
    exact absurd heG (not_lt.2 (gl_G0_le (gl_SC_of_fix h3 he.pos) hOe))
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
  refine ⟨α, h1, hαe, η, (glLam_ge α η).trans_lt (hη ▸ hye), ?_⟩
  unfold glPsi; rw [hη, hey]

/-! ## The data of an `ε`-number code -/

/-- **The level** of an `ε`-number code `e ∈ (Ω₁, Γ_{Ω₁+1})`. -/
noncomputable def glK (e : Ordinal.{0}) : Ordinal.{0} := by
  classical
  exact if h : ∃ α, 1 ≤ α ∧ α < e ∧ ∃ η, η < e ∧ glPsi α η = e then Classical.choose h else 0

/-- **The index** of an `ε`-number code: `e = glPsi (glK e) (glI e)`. -/
noncomputable def glI (e : Ordinal.{0}) : Ordinal.{0} := by
  classical
  exact if h : ∃ η, η < e ∧ glPsi (glK e) η = e then Classical.choose h else 0

theorem glData_spec {e : Ordinal.{0}} (he : InE e) (hOe : Om1 < e) (heG : e < gcG 0) :
    1 ≤ glK e ∧ glK e < e ∧ glI e < e ∧ glPsi (glK e) (glI e) = e := by
  classical
  have hex := glPsi_surj he hOe heG
  have hK : glK e = Classical.choose hex := by unfold glK; rw [dif_pos hex]
  obtain ⟨hk1, hke, hη⟩ := Classical.choose_spec hex
  rw [← hK] at hk1 hke hη
  have hI : glI e = Classical.choose hη := by unfold glI; rw [dif_pos hη]
  obtain ⟨h1, h2⟩ := Classical.choose_spec hη
  rw [← hI] at h1 h2
  exact ⟨hk1, hke, h1, h2⟩

theorem glData_eq {α : Ordinal.{0}} (hα : 1 ≤ α) (hαG : α < gcG 0) {η : Ordinal.{0}} (hηG : η < gcG 0) :
    glK (glPsi α η) = α ∧ glI (glPsi α η) = η := by
  have hE := glPsi_E hα η
  obtain ⟨h1, -, -, h3⟩ := glData_spec hE (glPsi_gt hα hαG η).1 (glPsi_lt_G hαG hηG)
  exact glPsi_inj h1 hα h3

/-! ## `ε_{Ω₁+1}` and the bound `φ(ω, Ω₁+1)` -/

theorem gl_one_lt_G0 : (1 : Ordinal.{0}) < gcG 0 := one_lt_omega0.trans (omega0_lt_inE gl_G0_E)

/-- **`ε_{Ω₁+1} = glPsi 1 0`.** -/
theorem gl_E_eq : glPsi 1 0 = gfE := by
  unfold glPsi
  rw [glLam_of_not (glFw_zero 1), add_zero, glY0_lt (one_lt_omega0.trans omega_lt_Om1), eW_eq]

theorem gfE_lt_G0 : gfE < gcG 0 := gcG_eW_lt 0

theorem gfE_le_glPsi {α : Ordinal.{0}} (hα : 1 ≤ α) (hαG : α < gcG 0) (η : Ordinal.{0}) : gfE ≤ glPsi α η :=
  eN_le (glPsi_gt hα hαG η).1 (glPsi_E hα η)

/-- **`φ(ω, Ω₁+1)`**, the least common fixed point of all `φ_k`, `k < ω`, above `Ω₁`. -/
noncomputable def glB : Ordinal.{0} := veblen ω (Om1 + 1)

theorem glB_omega : glB ∈ Set.range (veblen ω) := ⟨_, rfl⟩

theorem glB_E : InE glB := by
  have := veblen_veblen_of_lt (o₁ := 0) (o₂ := ω) omega0_pos (Om1 + 1)
  rw [veblen_zero_apply] at this; exact this

theorem Om1_lt_glB : Om1 < glB := by
  have := (veblen_lt_veblen_iff_right (o := ω)).2 (lt_add_one Om1)
  rwa [gl_veb_Om1 omega_lt_Om1] at this

theorem glB_lim : IsSuccLimit glB := ev_isSuccLimit_of_inE glB_E

theorem glB_lt_G0 : glB < gcG 0 :=
  gl_veb_lt_G0 (omega_lt_Om1.trans gl_Om1_lt_G0) (gl_G0_lim.add_one_lt gl_Om1_lt_G0)

theorem glB_mem {S : InaccSeq.{0}} {a b : Ordinal.{0}} : glB ∈ S.CSet a b := by
  have hO : Om1 ∈ S.CSet a b := by rw [Br.Om1_eq]; exact CSet.Om_mem (CSet.one_mem _ _)
  have hω : ω ∈ S.CSet a b := by
    have := CSet.phi_mem (CSet.zero_mem (S := S) a b) (CSet.one_mem a b)
    rwa [veblen_zero_apply, opow_one] at this
  exact CSet.phi_mem hω (CSet.succ_mem hO)

end Googology.Trans.PoR.InaccPsi.R2.Gl

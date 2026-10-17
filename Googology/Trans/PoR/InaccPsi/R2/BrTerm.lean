import Googology.Trans.PoR.InaccPsi.R2.BrThb

/-!
# Normal terms of `T̄^τ` and the subterm sets `Kᵢ`, `K*ᵢ`

[W25] G. Wilken, "Fundamental sequences based on localization" (2025), §2.2.

`Tm` are the terms of `T̄^τ`: parameters `par c` (`c < τ`), `th j t` for `ϑ̄ⱼ(t)`, and sums.  `NF τ t`
says that `t` is a normal term: a parameter below `τ`, a term `ϑ̄ⱼ(t)` with `t` normal and
`ev t ∈ dom(ϑ̄ⱼ)`, or a sum `ϑ̄ⱼ(u) + r` (right nested) with `r ≠ 0` normal whose leading part is at
most `ϑ̄ⱼ(u)` (the additive normal form; a trailing part below `τ` is one parameter).

* `NF.mem_Tbar`: the value of a normal term is in `T̄^τ`;
* `NF.unique`: two normal terms with the same value are equal (from `thb_inj` and the ranges
  `[Ωⱼ, Ω_{j+1})`); so `Kᵢ`, `K*ᵢ` computed on the normal term of `α` are the sets of [W25] Def 2.11;
* `exists_NF`: every element of `T̄^τ` is the value of a normal term.

`Ki i t` is `Kᵢ(α)` and `Kst i t` is `K*ᵢ(α)` with the level of each argument ([W25] Def 2.11:
"1. `Kᵢ(α) := K*ᵢ(α) := ∅` for `α < τ`.  2. `Kᵢ(α) := Kᵢ(ξ) ∪ Kᵢ(η)` and `K*ᵢ(α) := K*ᵢ(ξ) ∪ K*ᵢ(η)` for
`α =NF ξ + η`.  3. `Kᵢ(α) := ∅` if `j < i`, `{α}` if `j = i`, `Kᵢ(ξ)` if `j > i` and `K*ᵢ(α) := ∅` if
`j < i`, `{ξ} ∪ K*ᵢ(ξ)` if `j ≥ i`, for `α = ϑ̄ⱼ(ξ)`."), and `star τ i t` is
`α^{*i} := max(Kᵢ(α) ∪ {0})`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Br

open Ordinal Set Googology.Notation.InaccPsi

/-- Terms of `T̄^τ`. -/
inductive Tm
  | par (c : Ordinal.{0})
  | th (j : ℕ) (t : Tm)
  | add (s t : Tm)

namespace Tm

/-- The value of a term. -/
noncomputable def ev (τ : Ordinal.{0}) : Tm → Ordinal.{0}
  | par c => c
  | th j t => thb τ (ev τ t) j
  | add s t => ev τ s + ev τ t

/-- The leading part: `c` for `par c`, the value of a `ϑ̄`-term, the value of the first summand. -/
noncomputable def hd (τ : Ordinal.{0}) : Tm → Ordinal.{0}
  | par c => c
  | th j t => thb τ (ev τ t) j
  | add s _ => ev τ s

def size : Tm → ℕ
  | par _ => 1
  | th _ t => size t + 1
  | add s t => size s + size t + 1

theorem size_pos (t : Tm) : 0 < size t := by cases t <;> simp [size]

/-- `Kᵢ` ([W25] Def 2.11). -/
def Ki (i : ℕ) : Tm → List Tm
  | par _ => []
  | th j t => if j < i then [] else if j = i then [th j t] else Ki i t
  | add s t => Ki i s ++ Ki i t

/-- `K*ᵢ` ([W25] Def 2.11), with the level `j` of each `ϑ̄ⱼ(ξ)` whose argument `ξ` is listed. -/
def Kst (i : ℕ) : Tm → List (ℕ × Tm)
  | par _ => []
  | th j t => if j < i then [] else (j, t) :: Kst i t
  | add s t => Kst i s ++ Kst i t

/-- `α^{*i} = max(Kᵢ(α) ∪ {0})`. -/
noncomputable def star (τ : Ordinal.{0}) (i : ℕ) (t : Tm) : Ordinal.{0} :=
  ((Ki i t).map (ev τ)).foldr max 0

end Tm

open Tm

/-- Normal terms of `T̄^τ`. -/
inductive NF (τ : Ordinal.{0}) : Tm → Prop
  | cpar {c : Ordinal.{0}} : c < τ → NF τ (par c)
  | cth {j : ℕ} {t : Tm} : NF τ t → Dom τ j (ev τ t) → NF τ (th j t)
  | cadd {j : ℕ} {t r : Tm} : NF τ (th j t) → NF τ r → r ≠ par 0 → hd τ r ≤ ev τ (th j t) →
      NF τ (add (th j t) r)

variable {τ : Ordinal.{0}}

/-! ## Values -/

theorem NF.mem_Tbar {t : Tm} (h : NF τ t) : ev τ t ∈ Tbar τ := by
  induction h with
  | cpar hc => exact Tbar.lt_tau hc
  | cth _ hd ih => exact Tbar.thb ih hd
  | cadd _ _ _ _ ih1 ih2 => exact Tbar.add ih1 ih2

theorem NF.th_bounds (hτ : Base τ) {j : ℕ} {t : Tm} (h : NF τ (th j t)) :
    OmT τ j ≤ ev τ (th j t) ∧ ev τ (th j t) < OmT τ (j + 1) := by
  cases h with
  | cth _ hd => exact ⟨OmT_le_thb hτ hd, thb_lt hτ hd⟩

theorem NF.th_principal (hτ : Base τ) {j : ℕ} {t : Tm} (h : NF τ (th j t)) :
    IsPrincipal (· + ·) (ev τ (th j t)) := by
  cases h with
  | cth _ hd => exact thb_principal hτ hd

theorem NF.th_dom {j : ℕ} {t : Tm} (h : NF τ (th j t)) : Dom τ j (ev τ t) := by
  cases h with
  | cth _ hd => exact hd

theorem NF.th_arg {j : ℕ} {t : Tm} (h : NF τ (th j t)) : NF τ t := by
  cases h with
  | cth ht _ => exact ht

theorem tau_le_th (hτ : Base τ) {j : ℕ} {t : Tm} (h : NF τ (th j t)) : τ ≤ ev τ (th j t) := by
  have h1 := (NF.th_bounds hτ h).1
  calc τ = OmT τ 0 := (OmT_zero τ).symm
    _ ≤ OmT τ j := OmT_mono hτ (Nat.zero_le j)
    _ ≤ _ := h1

/-- A normal term that is not a parameter has its leading part principal and `≥ τ`. -/
theorem NF.hd_ge (hτ : Base τ) {t : Tm} (h : NF τ t) (hp : ∀ c, t ≠ par c) :
    τ ≤ hd τ t ∧ IsPrincipal (· + ·) (hd τ t) := by
  cases h with
  | cpar _ => exact absurd rfl (hp _)
  | cth ht hd => exact ⟨tau_le_th hτ (NF.cth ht hd), NF.th_principal hτ (NF.cth ht hd)⟩
  | cadd h1 _ _ _ => exact ⟨tau_le_th hτ h1, NF.th_principal hτ h1⟩

/-- If the leading part of a normal term is below a principal `P ≥ τ`, so is its value. -/
theorem NF.ev_lt (_hτ : Base τ) {t : Tm} (h : NF τ t) {P : Ordinal.{0}}
    (hP : IsPrincipal (· + ·) P) (hlt : hd τ t < P) : ev τ t < P := by
  induction h with
  | cpar _ => exact hlt
  | cth _ _ => exact hlt
  | cadd _ _ _ hle _ ih2 =>
    exact hP hlt (ih2 (lt_of_le_of_lt hle hlt))

theorem NF.ev_ne_zero (hτ : Base τ) {t : Tm} (h : NF τ t) (h0 : t ≠ par 0) : ev τ t ≠ 0 := by
  cases h with
  | @cpar c _ => exact fun e => h0 (by simp only [ev] at e; rw [e])
  | cth ht hd => exact (thb_pos hτ hd).ne'
  | @cadd j u r h1 _ _ _ =>
    have := (thb_pos hτ (NF.th_dom h1))
    simp only [ev]
    exact (lt_of_lt_of_le this (le_self_add)).ne'

theorem NF.hd_le_ev {t : Tm} (h : NF τ t) : hd τ t ≤ ev τ t := by
  cases h with
  | cpar _ => exact le_rfl
  | cth _ _ => exact le_rfl
  | cadd _ _ _ _ => exact le_self_add

theorem NF.par_lt {c : Ordinal.{0}} (h : NF τ (par c)) : c < τ := by
  cases h with
  | cpar hc => exact hc

/-! ## Leading part and rest -/

theorem lead_tail_sum {h r : Ordinal.{0}} (hp : IsPrincipal (· + ·) h) (h0 : h ≠ 0)
    (hr : r < ω ^ (Ordinal.log ω h + 1)) :
    lead (h + r) = h ∧ tail (h + r) = r := by
  obtain ⟨g, rfl⟩ := exists_opow_of_principal hp h0
  rw [Ordinal.log_opow one_lt_omega0] at hr
  exact ⟨lead_opow_add hr, tail_opow_add hr⟩

theorem principal_lt_next {h : Ordinal.{0}} (hp : IsPrincipal (· + ·) h) (h0 : h ≠ 0) :
    h < ω ^ (Ordinal.log ω h + 1) ∧ IsPrincipal (· + ·) (ω ^ (Ordinal.log ω h + 1)) := by
  obtain ⟨g, rfl⟩ := exists_opow_of_principal hp h0
  rw [Ordinal.log_opow one_lt_omega0]
  exact ⟨opow_lt_opow_add_one g, isPrincipal_add_omega0_opow _⟩

/-- For a normal sum `add h r`: the leading summand of the value is `ev h`, the rest is `ev r`. -/
theorem NF.add_lead_tail (hτ : Base τ) {j : ℕ} {u r : Tm} (h : NF τ (add (th j u) r)) :
    lead (ev τ (add (th j u) r)) = ev τ (th j u) ∧ tail (ev τ (add (th j u) r)) = ev τ r := by
  cases h with
  | cadd h1 h2 _ hle =>
    have hp := NF.th_principal hτ h1
    have h0 : ev τ (th j u) ≠ 0 := (lt_of_lt_of_le hτ.pos (tau_le_th hτ h1)).ne'
    obtain ⟨hlt, hP⟩ := principal_lt_next hp h0
    exact lead_tail_sum hp h0 (NF.ev_lt hτ h2 hP (lt_of_le_of_lt hle hlt))

theorem NF.th_lead_tail (hτ : Base τ) {j : ℕ} {u : Tm} (h : NF τ (th j u)) :
    lead (ev τ (th j u)) = ev τ (th j u) ∧ tail (ev τ (th j u)) = 0 := by
  have hp := NF.th_principal hτ h
  have h0 : ev τ (th j u) ≠ 0 := (lt_of_lt_of_le hτ.pos (tau_le_th hτ h)).ne'
  have := lead_tail_of_principal hp h0
  exact this

/-! ## Uniqueness of normal terms -/

theorem level_eq (hτ : Base τ) {j k : ℕ} {u v : Tm} (hu : NF τ (th j u)) (hv : NF τ (th k v))
    (he : ev τ (th j u) = ev τ (th k v)) : j = k := by
  obtain ⟨hu1, hu2⟩ := NF.th_bounds hτ hu
  obtain ⟨hv1, hv2⟩ := NF.th_bounds hτ hv
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := OmT_mono hτ (Nat.succ_le_of_lt h)
    exact absurd (he ▸ hu2) (not_lt.2 (this.trans hv1))
  · have := OmT_mono hτ (Nat.succ_le_of_lt h)
    exact absurd (he ▸ hv2) (not_lt.2 (this.trans (he ▸ hu1)))

/-- **Normal terms are unique.** -/
theorem NF.unique (hτ : Base τ) {s : Tm} (hs : NF τ s) :
    ∀ {t : Tm}, NF τ t → ev τ s = ev τ t → s = t := by
  induction hs with
  | @cpar c hc =>
    intro t ht he
    cases ht with
    | cpar _ => simp only [ev] at he; rw [he]
    | cth ht' hd' =>
      exact absurd (he ▸ hc) (not_lt.2 (tau_le_th hτ (NF.cth ht' hd')))
    | cadd h1 _ _ _ =>
      exact absurd (lt_of_eq_of_lt he.symm hc) (not_lt.2 ((tau_le_th hτ h1).trans le_self_add))
  | @cth j u hu hd ih =>
    intro t ht he
    have hs' : NF τ (th j u) := NF.cth hu hd
    cases ht with
    | cpar hc =>
      exact absurd (he.symm ▸ hc) (not_lt.2 (tau_le_th hτ hs'))
    | @cth k v hv hdv =>
      have hjk := level_eq hτ hs' (NF.cth hv hdv) he
      subst hjk
      have := thb_inj hτ hd hdv he
      rw [ih hv this]
    | @cadd k v r h1 h2 h3 h4 =>
      have := (NF.add_lead_tail hτ (NF.cadd h1 h2 h3 h4)).2
      rw [← he, (NF.th_lead_tail hτ hs').2] at this
      exact absurd this.symm (NF.ev_ne_zero hτ h2 h3)
  | @cadd j u r h1 h2 h3 h4 ih1 ih2 =>
    intro t ht he
    have hs' : NF τ (add (th j u) r) := NF.cadd h1 h2 h3 h4
    cases ht with
    | cpar hc =>
      exact absurd (lt_of_eq_of_lt he hc) (not_lt.2 ((tau_le_th hτ h1).trans le_self_add))
    | @cth k v hv hdv =>
      have := (NF.add_lead_tail hτ hs').2
      rw [he, (NF.th_lead_tail hτ (NF.cth hv hdv)).2] at this
      exact absurd this.symm (NF.ev_ne_zero hτ h2 h3)
    | @cadd k v r' g1 g2 g3 g4 =>
      have ha := NF.add_lead_tail hτ hs'
      have hb := NF.add_lead_tail hτ (NF.cadd g1 g2 g3 g4)
      rw [he] at ha
      have e1 : ev τ (th j u) = ev τ (th k v) := ha.1.symm.trans hb.1
      have e2 : ev τ r = ev τ r' := ha.2.symm.trans hb.2
      rw [ih1 g1 e1, ih2 g2 e2]

/-! ## Every element of `T̄^τ` has a normal term -/

open Classical in
/-- The normal form of a sum. -/
noncomputable def plus (τ : Ordinal.{0}) : Tm → Tm → Tm
  | .par c, t => match t with
    | .par d => par (c + d)
    | t' => t'
  | .th j u, t => if t = par 0 then th j u else if hd τ t ≤ ev τ (th j u) then add (th j u) t else t
  | .add s r, t => if t = par 0 then add s r else if hd τ t ≤ ev τ s then add s (plus τ r t) else t

/-- A value below the (principal) leading part of a normal non-parameter term is absorbed. -/
theorem NF.absorb (hτ : Base τ) {t : Tm} (h : NF τ t) (hp : ∀ c, t ≠ par c) {x : Ordinal.{0}}
    (hx : x < hd τ t) : x + ev τ t = ev τ t := by
  have hP := (NF.hd_ge hτ h hp).2
  cases h with
  | cpar _ => exact absurd rfl (hp _)
  | cth _ _ => exact hP.add_eq_right hx
  | @cadd j u r _ _ _ _ =>
    have hx' : x < ev τ (th j u) := hx
    have hP' : IsPrincipal (· + ·) (ev τ (th j u)) := hP
    show x + (ev τ (th j u) + ev τ r) = ev τ (th j u) + ev τ r
    rw [← add_assoc, hP'.add_eq_right hx']

theorem not_par_of_hd {t : Tm} (h : NF τ t) (_hτ : Base τ) {P : Ordinal.{0}} (hP : τ ≤ P)
    (hlt : P < hd τ t) : ∀ c, t ≠ par c := by
  intro c e
  subst e
  exact absurd (lt_of_le_of_lt hP hlt) (not_lt.2 (NF.par_lt h).le)

theorem plus_spec (hτ : Base τ) {s : Tm} (hs : NF τ s) :
    ∀ {t : Tm}, NF τ t → NF τ (plus τ s t) ∧ ev τ (plus τ s t) = ev τ s + ev τ t ∧
      ∀ P, τ ≤ P → hd τ s ≤ P → hd τ t ≤ P → hd τ (plus τ s t) ≤ P := by
  induction hs with
  | @cpar c hc =>
    intro t ht
    cases ht with
    | @cpar d hd =>
      refine ⟨NF.cpar (hτ.principal hc hd), rfl, fun P hP _ _ => ?_⟩
      exact (hτ.principal hc hd).le.trans hP
    | cth ht' hd' =>
      have hn : NF τ (th _ _) := NF.cth ht' hd'
      refine ⟨hn, ?_, fun P _ _ h2 => h2⟩
      show _ = c + _
      exact (NF.absorb hτ hn (fun _ e => Tm.noConfusion e)
        (lt_of_lt_of_le hc (tau_le_th hτ hn))).symm
    | cadd h1 h2 h3 h4 =>
      have hn := NF.cadd h1 h2 h3 h4
      refine ⟨hn, ?_, fun P _ _ h2 => h2⟩
      show _ = c + _
      exact (NF.absorb hτ hn (fun _ e => Tm.noConfusion e)
        (lt_of_lt_of_le hc (tau_le_th hτ h1))).symm
  | @cth j u hu hdm _ =>
    intro t ht
    have hs' : NF τ (th j u) := NF.cth hu hdm
    by_cases h0 : t = par 0
    · subst h0
      simp only [plus, if_true]
      exact ⟨hs', by simp [ev], fun P _ h1 _ => h1⟩
    by_cases hle : hd τ t ≤ ev τ (th j u)
    · simp only [plus, h0, hle, if_false, if_true]
      exact ⟨NF.cadd hs' ht h0 hle, rfl, fun P _ h1 _ => h1⟩
    · simp only [plus, h0, hle, if_false]
      have hlt := not_le.1 hle
      have hnp := not_par_of_hd ht hτ (tau_le_th hτ hs') hlt
      exact ⟨ht, (NF.absorb hτ ht hnp hlt).symm, fun P _ _ h2 => h2⟩
  | @cadd j u r h1 h2 h3 h4 _ ih2 =>
    intro t ht
    have hs' := NF.cadd h1 h2 h3 h4
    by_cases h0 : t = par 0
    · subst h0
      simp only [plus, if_true]
      exact ⟨hs', by simp [ev], fun P _ h1 _ => h1⟩
    by_cases hle : hd τ t ≤ ev τ (th j u)
    · simp only [plus, h0, hle, if_false, if_true]
      obtain ⟨n1, e1, b1⟩ := ih2 ht
      have hne : plus τ r t ≠ par 0 := by
        intro e
        have := NF.ev_ne_zero hτ h2 h3
        have hz : ev τ (plus τ r t) = 0 := by rw [e]; rfl
        rw [e1] at hz
        exact this (Ordinal.add_eq_zero_iff.1 hz).1
      refine ⟨NF.cadd h1 n1 hne (b1 _ (tau_le_th hτ h1) h4 hle), ?_, fun P _ hP _ => hP⟩
      show ev τ (th j u) + ev τ (plus τ r t) = ev τ (th j u) + ev τ r + ev τ t
      rw [e1, add_assoc]
    · simp only [plus, h0, hle, if_false]
      have hlt := not_le.1 hle
      have hnp := not_par_of_hd ht hτ (tau_le_th hτ h1) hlt
      have hP := (NF.hd_ge hτ ht hnp).2
      have hr : ev τ r < hd τ t := NF.ev_lt hτ h2 hP (lt_of_le_of_lt h4 hlt)
      refine ⟨ht, (NF.absorb hτ ht hnp (hP hlt hr)).symm, fun P _ _ h2 => h2⟩

/-- **Every element of `T̄^τ` is the value of a normal term.** -/
theorem exists_NF (hτ : Base τ) {x : Ordinal.{0}} (hx : x ∈ Tbar τ) :
    ∃ t, NF τ t ∧ ev τ t = x := by
  unfold Tbar at hx
  generalize ha : Om (ω : Ordinal.{0}) = A at hx
  generalize hi : (0 : ℕ) = i at hx
  generalize hb : (0 : Ordinal.{0}) = b at hx
  induction hx with
  | base h =>
    subst hi
    rw [OmT_zero] at h
    exact ⟨par _, NF.cpar h, rfl⟩
  | small h => rw [← hb] at h; exact absurd h (not_lt.2 zero_le)
  | add _ _ ihx ihy =>
    obtain ⟨s, hs, rfl⟩ := ihx ha hi hb
    obtain ⟨t, ht, rfl⟩ := ihy ha hi hb
    obtain ⟨n, e, _⟩ := plus_spec hτ hs ht
    exact ⟨_, n, e⟩
  | @th a i b j ξ _ hξ hd _ _ ihm =>
    obtain ⟨t, ht, rfl⟩ := ihm ha hi hb
    have hξω : ev τ t < Om (ω : Ordinal.{0}) := ha ▸ hξ
    exact ⟨th j t, NF.cth ht ⟨hξω, hd⟩, rfl⟩

/-! ## The subterm sets -/

theorem Ki_shape {i : ℕ} {t u : Tm} (h : u ∈ Ki i t) : ∃ δ, u = th i δ ∧ size u ≤ size t := by
  induction t with
  | par _ => simp [Ki] at h
  | th j t ih =>
    simp only [Ki] at h
    split_ifs at h with h1 h2
    · simp at h
    · simp at h; subst h; subst h2; exact ⟨t, rfl, le_rfl⟩
    · obtain ⟨δ, e, hs⟩ := ih h; exact ⟨δ, e, by simp [size]; omega⟩
  | add s r ihs ihr =>
    simp only [Ki, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨δ, e, hs⟩ := ihs h; exact ⟨δ, e, by simp [size]; omega⟩
    · obtain ⟨δ, e, hs⟩ := ihr h; exact ⟨δ, e, by simp [size]; omega⟩

theorem Kst_size {i : ℕ} {t : Tm} {p : ℕ × Tm} (h : p ∈ Kst i t) : size (th p.1 p.2) ≤ size t := by
  induction t with
  | par _ => simp [Kst] at h
  | th j t ih =>
    simp only [Kst] at h
    split_ifs at h with h1
    · simp at h
    · simp only [List.mem_cons] at h
      rcases h with h | h
      · subst h; simp [size]
      · have := ih h; simp [size] at this ⊢; omega
  | add s r ihs ihr =>
    simp only [Kst, List.mem_append] at h
    rcases h with h | h
    · have := ihs h; simp [size] at this ⊢; omega
    · have := ihr h; simp [size] at this ⊢; omega

theorem Kst_level {i : ℕ} {t : Tm} {p : ℕ × Tm} (h : p ∈ Kst i t) : i ≤ p.1 := by
  induction t with
  | par _ => simp [Kst] at h
  | th j t ih =>
    simp only [Kst] at h
    split_ifs at h with h1
    · simp at h
    · simp only [List.mem_cons] at h
      rcases h with h | h
      · subst h; exact not_lt.1 h1
      · exact ih h
  | add s r ihs ihr =>
    simp only [Kst, List.mem_append] at h
    rcases h with h | h
    · exact ihs h
    · exact ihr h

/-- A member of `K*_L(t)` is a normal `ϑ̄`-term when `t` is normal. -/
theorem NF.Kst {i : ℕ} {t : Tm} (ht : NF τ t) {p : ℕ × Tm} (h : p ∈ Kst i t) :
    NF τ (th p.1 p.2) := by
  induction ht with
  | cpar _ => simp [Tm.Kst] at h
  | @cth j u hu hdm ih =>
    simp only [Tm.Kst] at h
    split_ifs at h with h1
    · simp at h
    · simp only [List.mem_cons] at h
      rcases h with h | h
      · subst h; exact NF.cth hu hdm
      · exact ih h
  | cadd h1 h2 _ _ ih1 ih2 =>
    simp only [Tm.Kst, List.mem_append] at h
    rcases h with h | h
    · exact ih1 h
    · exact ih2 h

theorem NF.Ki {i : ℕ} {t : Tm} (ht : NF τ t) {u : Tm} (h : u ∈ Ki i t) : NF τ u := by
  induction ht with
  | cpar _ => simp [Tm.Ki] at h
  | @cth j v hv hdm ih =>
    simp only [Tm.Ki] at h
    split_ifs at h with h1 h2
    · simp at h
    · simp at h; subst h; exact NF.cth hv hdm
    · exact ih h
  | cadd h1 h2 _ _ ih1 ih2 =>
    simp only [Tm.Ki, List.mem_append] at h
    rcases h with h | h
    · exact ih1 h
    · exact ih2 h

/-- `K*_L` of a member of `K*_L(t)` is part of `K*_L(t)`. -/
theorem Kst_trans {L : ℕ} {t : Tm} {p : ℕ × Tm} (h : p ∈ Kst L t) : Kst L p.2 ⊆ Kst L t := by
  induction t with
  | par _ => simp [Kst] at h
  | th j t ih =>
    simp only [Kst] at h ⊢
    split_ifs at h ⊢ with h1
    · simp at h
    · simp only [List.mem_cons] at h
      rcases h with h | h
      · subst h; exact List.subset_cons_of_subset _ (List.Subset.refl _)
      · exact List.subset_cons_of_subset _ (ih h)
  | add s r ihs ihr =>
    simp only [Kst, List.mem_append] at h
    rcases h with h | h
    · exact (ihs h).trans (List.subset_append_left _ _)
    · exact (ihr h).trans (List.subset_append_right _ _)

/-- The level-`k` parts `Kₖ(η)` are in `K*_L(η)` for `L ≤ k`. -/
theorem Ki_sub_Kst {L k : ℕ} (hLk : L ≤ k) {η δ : Tm} (h : th k δ ∈ Ki k η) : (k, δ) ∈ Kst L η := by
  induction η with
  | par _ => simp [Ki] at h
  | th j t ih =>
    simp only [Ki] at h
    simp only [Kst]
    split_ifs at h with h1 h2
    · simp at h
    · simp at h
      obtain ⟨rfl, rfl⟩ := h
      rw [if_neg (by omega)]; exact List.mem_cons_self
    · rw [if_neg (by omega)]; exact List.mem_cons_of_mem _ (ih h)
  | add s r ihs ihr =>
    simp only [Ki, List.mem_append] at h
    simp only [Kst, List.mem_append]
    rcases h with h | h
    · exact Or.inl (ihs h)
    · exact Or.inr (ihr h)

/-- Members of `Kᵢ(t)` with `i ≥ L` are in `K*_L(t)`. -/
theorem Ki_sub_Kst' {L i : ℕ} (hLi : L ≤ i) {t δ : Tm} (h : th i δ ∈ Ki i t) : (i, δ) ∈ Kst L t :=
  Ki_sub_Kst hLi h

theorem le_foldr_max {u : Tm} : ∀ {l : List Tm}, u ∈ l → ev τ u ≤ (l.map (ev τ)).foldr max 0
  | [], h => by simp at h
  | v :: l, h => by
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.1 h with h | h
    · subst h; exact le_max_left _ _
    · exact (le_foldr_max h).trans (le_max_right _ _)

theorem foldr_max_cases : ∀ (l : List Tm),
    (l.map (ev τ)).foldr max 0 = 0 ∨ ∃ u ∈ l, (l.map (ev τ)).foldr max 0 = ev τ u
  | [] => Or.inl rfl
  | v :: l => by
    simp only [List.map_cons, List.foldr_cons]
    rcases le_total (ev τ v) (List.foldr max 0 (List.map (ev τ) l)) with h | h
    · rw [max_eq_right h]
      rcases foldr_max_cases l with h0 | ⟨u, hu, e⟩
      · left; exact h0
      · right; exact ⟨u, List.mem_cons_of_mem _ hu, e⟩
    · rw [max_eq_left h]; right; exact ⟨v, List.mem_cons_self, rfl⟩

/-- `star` is the maximum of the values in `Kᵢ`. -/
theorem le_star {i : ℕ} {t u : Tm} (h : u ∈ Ki i t) : ev τ u ≤ Tm.star τ i t := le_foldr_max h

theorem star_cases (i : ℕ) (t : Tm) :
    Tm.star τ i t = 0 ∨ ∃ u ∈ Ki i t, Tm.star τ i t = ev τ u := foldr_max_cases _

/-- **Anchors.** A member `(k, η)` of `K*ᵢ(t)` with `k > i` is in `K*_{i+1}(t)`, or in `K*_{i+1}(η_s)`
for a member `(i, η_s)` of `K*ᵢ(t)`. -/
theorem Kst_anchor {i : ℕ} {t : Tm} {k : ℕ} {η : Tm} (h : (k, η) ∈ Kst i t) (hk : i < k) :
    (k, η) ∈ Kst (i + 1) t ∨ ∃ ηs, (i, ηs) ∈ Kst i t ∧ (k, η) ∈ Kst (i + 1) ηs := by
  induction t with
  | par _ => simp [Kst] at h
  | th j u ih =>
    simp only [Kst] at h
    split_ifs at h with h1
    · simp at h
    · simp only [List.mem_cons] at h
      rcases h with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        left; simp only [Kst]; rw [if_neg (by omega)]; exact List.mem_cons_self
      · rcases Nat.lt_or_ge i j with hij | hij
        · rcases ih h with h' | ⟨ηs, h1', h2'⟩
          · left; simp only [Kst]; rw [if_neg (by omega)]; exact List.mem_cons_of_mem _ h'
          · right; refine ⟨ηs, ?_, h2'⟩
            simp only [Kst]; rw [if_neg h1]; exact List.mem_cons_of_mem _ h1'
        · have hj : j = i := le_antisymm hij (not_lt.1 h1)
          subst hj
          rcases ih h with h' | ⟨ηs, h1', h2'⟩
          · right; refine ⟨u, ?_, h'⟩
            simp only [Kst]; rw [if_neg h1]; exact List.mem_cons_self
          · right; refine ⟨ηs, ?_, h2'⟩
            simp only [Kst]; rw [if_neg h1]; exact List.mem_cons_of_mem _ h1'
  | add s r ihs ihr =>
    simp only [Kst, List.mem_append] at h ⊢
    rcases h with h | h
    · rcases ihs h with h' | ⟨ηs, h1', h2'⟩
      · exact Or.inl (Or.inl h')
      · exact Or.inr ⟨ηs, Or.inl h1', h2'⟩
    · rcases ihr h with h' | ⟨ηs, h1', h2'⟩
      · exact Or.inl (Or.inr h')
      · exact Or.inr ⟨ηs, Or.inr h1', h2'⟩

/-- A member `(i, η)` of `K*ᵢ(t)` is in `Kᵢ(t)` or in `K*ᵢ(η_s)` for some `th i η_s ∈ Kᵢ(t)`. -/
theorem Kst_same {i : ℕ} {t η : Tm} (h : (i, η) ∈ Kst i t) :
    th i η ∈ Ki i t ∨ ∃ ηs, th i ηs ∈ Ki i t ∧ (i, η) ∈ Kst i ηs := by
  induction t with
  | par _ => simp [Kst] at h
  | th j u ih =>
    simp only [Kst] at h
    simp only [Ki]
    split_ifs at h with h1
    · simp at h
    · simp only [List.mem_cons] at h
      by_cases hji : j = i
      · subst hji
        rw [if_neg h1, if_pos rfl]
        rcases h with h | h
        · obtain ⟨-, rfl⟩ := Prod.mk.inj h
          left; exact List.mem_cons_self
        · right; exact ⟨u, List.mem_cons_self, h⟩
      · rw [if_neg h1, if_neg hji]
        rcases h with h | h
        · exact absurd (Prod.mk.inj h).1.symm hji
        · exact ih h
  | add s r ihs ihr =>
    simp only [Kst, List.mem_append] at h
    simp only [Ki, List.mem_append]
    rcases h with h | h
    · rcases ihs h with h' | ⟨ηs, h1', h2'⟩
      · exact Or.inl (Or.inl h')
      · exact Or.inr ⟨ηs, Or.inl h1', h2'⟩
    · rcases ihr h with h' | ⟨ηs, h1', h2'⟩
      · exact Or.inl (Or.inr h')
      · exact Or.inr ⟨ηs, Or.inr h1', h2'⟩

end Googology.Trans.PoR.InaccPsi.R2.Br

import Googology.Trans.PoR.InaccPsi.R2.EvV

/-!
# Terms below `ε_{x+x}`: Lemma EXACT, the uniform comparison, the representation, Lemma RS

The terms `TEv`: a constant (`cst a`), the `ε`-number `ε_{x+c}` with a constant index `c` (`ec c`; `ec 0` is `x`,
`ec n` is `ε_{x+n}`, `ec ω` is `ε_{x+ω}`), a sum (`sm`), and `ω^t` (`pw t`).  For an `ε`-number `x` above the
constants the value is below `ε_{x+cbd(t)}` (`cbd` the largest `c + 1` of an `ec c`), so below `ε_{x+x}`, and every
ordinal below `ε_{ρ+ρ}` is a value at `ρ` (`repV`).  These are the terms of `R2.EpsT` with the index of `ε_{x+·}`
running over all constants instead of `ℕ`.

* `TEv`, `TEv.val`, `TEv.CBv`, `TEv.csv`, `TEv.cbd`, `TEv.noE`; `valV_lt` (`t(x) < ε_{x+cbd(t)}`), `cbd_lt`,
  `valV_noE`, `le_valV_of_not_noE`;
* `pi_opowV` (**`π(ω^γ) = ω^{π(γ)}`** for `γ ∈ Tᵖ[σ]` below some `ε_{ρ+C}`, `C < σ`), `pi_valV` (**Lemma EXACT
  for `TEv`**: `t(ρ) ∈ Tᵖ[σ]` and `π_{σ,ρ}(t(ρ)) = t(σ)`), `uniV_le`, `uniV_lt`, `uniV_eq` (the uniform comparison);
* `repV` (**representation below `ε_{ρ+ρ}`**);
* `rs_rstV` (Lemma RS with the target `t(ρ) ≥ ρ`, from `rs_rstF`), `rsStep_V` (Lemma RS for every term).

No new axiom.

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-- Terms below `ε_{x+x}`: a constant, `ε_{x+c}` (`c` a constant), a sum, or `ω^t`. -/
inductive TEv : Type 1
  | cst : Ordinal.{0} → TEv
  | ec : Ordinal.{0} → TEv
  | sm : TEv → TEv → TEv
  | pw : TEv → TEv

namespace TEv

/-- The value of a term at `x`. -/
noncomputable def val : TEv → Ordinal.{0} → Ordinal.{0}
  | cst a, _ => a
  | ec c, x => evA x c
  | sm a b, x => val a x + val b x
  | pw t, x => ω ^ val t x

/-- All constants (also the indices of the `ec`) below `s`. -/
def CBv : TEv → Ordinal.{0} → Prop
  | cst a, s => a < s
  | ec c, s => c < s
  | sm a b, s => CBv a s ∧ CBv b s
  | pw t, s => CBv t s

/-- The constants (with the indices of the `ec`). -/
def csv : TEv → List Ordinal.{0}
  | cst a => [a]
  | ec c => [c]
  | sm a b => csv a ++ csv b
  | pw t => csv t

/-- The bound index: the largest `c + 1` of an `ec c` (`0` if there is none). -/
noncomputable def cbd : TEv → Ordinal.{0}
  | cst _ => 0
  | ec c => c + 1
  | sm a b => max (cbd a) (cbd b)
  | pw t => cbd t

/-- No `ec` occurs. -/
def noE : TEv → Prop
  | cst _ => True
  | ec _ => False
  | sm a b => noE a ∧ noE b
  | pw t => noE t

@[simp] theorem val_cst (a x : Ordinal.{0}) : val (cst a) x = a := rfl
@[simp] theorem val_ec (c x : Ordinal.{0}) : val (ec c) x = evA x c := rfl
@[simp] theorem val_sm (a b : TEv) (x : Ordinal.{0}) : val (sm a b) x = val a x + val b x := rfl
@[simp] theorem val_pw (t : TEv) (x : Ordinal.{0}) : val (pw t) x = ω ^ val t x := rfl

theorem cbv_iff : ∀ (t : TEv) (s : Ordinal.{0}), CBv t s ↔ ∀ c ∈ csv t, c < s
  | cst a, s => by simp [CBv, csv]
  | ec c, s => by simp [CBv, csv]
  | sm a b, s => by
      simp only [CBv, csv, List.mem_append]
      rw [cbv_iff a s, cbv_iff b s]
      constructor
      · rintro ⟨h1, h2⟩ c (hc | hc)
        · exact h1 c hc
        · exact h2 c hc
      · intro h; exact ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩
  | pw t, s => cbv_iff t s

theorem CBv_mono {t : TEv} {s s' : Ordinal.{0}} (h : CBv t s) (hs : s ≤ s') : CBv t s' :=
  (cbv_iff t s').2 (fun c hc => lt_of_lt_of_le ((cbv_iff t s).1 h c hc) hs)

end TEv

open TEv

/-! ## Values -/

/-- The bound index is below every `ε`-number above the constants. -/
theorem cbd_lt {s : Ordinal.{0}} (hs : InE s) : ∀ t : TEv, CBv t s → cbd t < s
  | cst _, _ => hs.pos
  | ec _, h => (ev_isSuccLimit_of_inE hs).add_one_lt h
  | sm a b, h => max_lt (cbd_lt hs a h.1) (cbd_lt hs b h.2)
  | pw t, h => cbd_lt hs t h

/-- **`t(x) < ε_{x+cbd(t)}`** for an `ε`-number `x` above the constants. -/
theorem valV_lt {x : Ordinal.{0}} (hx : InE x) : ∀ t : TEv, CBv t x → val t x < evA x (cbd t)
  | cst a, h => by simp only [val_cst, cbd]; rw [evA_zero hx]; exact h
  | ec c, _ => evA_lt_iff.2 (lt_add_one c)
  | sm a b, h => by
    have hE := evA_E x (cbd (sm a b))
    have h1 : val a x < evA x (cbd (sm a b)) :=
      lt_of_lt_of_le (valV_lt hx a h.1) (evA_le_iff.2 (le_max_left _ _))
    have h2 : val b x < evA x (cbd (sm a b)) :=
      lt_of_lt_of_le (valV_lt hx b h.2) (evA_le_iff.2 (le_max_right _ _))
    exact (inE_indec hE).add_lt h1 h2
  | pw t, h => by
    have hE := evA_E x (cbd t)
    have h1 := (opow_lt_opow_iff_right one_lt_omega0).2 (valV_lt hx t h)
    have hE' : ω ^ evA x (cbd t) = evA x (cbd t) := hE
    rw [hE'] at h1
    exact h1

theorem valV_lt_AA {x : Ordinal.{0}} (hx : InE x) {t : TEv} (h : CBv t x) : val t x < evA x x :=
  (valV_lt hx t h).trans (evA_lt_iff.2 (cbd_lt hx t h))

theorem valV_lt_Om1 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {t : TEv} (h : CBv t x) :
    val t x < Om1 :=
  (valV_lt hx t h).trans (evA_lt_Om1 hx hx1 (cbd_lt hx t h).le)

/-- A term without `ec` has a constant value. -/
theorem valV_noE : ∀ t : TEv, noE t → ∀ x y, val t x = val t y
  | cst _, _, _, _ => rfl
  | ec _, h, _, _ => absurd h id
  | sm a b, h, x, y => by simp only [val_sm, valV_noE a h.1 x y, valV_noE b h.2 x y]
  | pw t, h, x, y => by simp only [val_pw, valV_noE t h x y]

/-- A term with an `ec` has value `≥ x`. -/
theorem le_valV_of_not_noE {x : Ordinal.{0}} (hx : InE x) : ∀ t : TEv, ¬ noE t → x ≤ val t x
  | cst _, h => absurd trivial h
  | ec c, _ => le_evA hx c
  | sm a b, h => by
    simp only [noE, not_and_or] at h
    rcases h with h | h
    · exact (le_valV_of_not_noE hx a h).trans le_self_add
    · exact (le_valV_of_not_noE hx b h).trans le_add_self
  | pw t, h => (le_valV_of_not_noE hx t h).trans (right_le_opow _ one_lt_omega0)

/-! ## `π(ω^γ) = ω^{π(γ)}` below `ε_{ρ+C}` -/

/-- **`π(ω^γ) = ω^{π(γ)}`** and `ω^γ ∈ Tᵖ[σ]` for `γ ∈ Tᵖ[σ]` below some `ε_{ρ+C}`, `C < σ`. -/
theorem pi_opowV {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {γ C : Ordinal.{0}}
    (hγ : γ ∈ TB ρ σ) (hCσ : C < σ) (hγC : γ < evA ρ C) :
    ω ^ γ ∈ TB ρ σ ∧ pi σ ρ (ω ^ γ) = ω ^ (pi σ ρ γ) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hρE := hB.2.1
  have hσE := hB.1
  have hγ1 : γ < Om1 := hγC.trans (evA_lt_Om1 hρE hρ1 (hCσ.trans hB.2.2.1).le)
  have h1TB : (1 : Ordinal.{0}) ∈ TB ρ σ :=
    mem_TB_of_lt hB (one_lt_omega0.trans (omega0_lt_inE hσE))
  have hp1 : pi σ ρ 1 = 1 := pi_lt hB (one_lt_omega0.trans (omega0_lt_inE hσE))
  rcases lt_or_ge γ ρ with hγρ | hργ
  · have hγσ : γ < σ := (TB_inter_lt hB hγρ).1 hγ
    have hwσ : ω ^ γ < σ := hσE.opow_lt hγσ
    exact ⟨mem_TB_of_lt hB hwσ, by rw [pi_lt hB hwσ, pi_lt hB hγσ]⟩
  obtain ⟨c, hcC, hm1, hm2⟩ := evA_bracket hρE hργ hγC
  have hcσ : c < σ := hcC.trans hCσ
  have hc1σ : c + 1 < σ := (ev_isSuccLimit_of_inE hσE).add_one_lt hcσ
  set e := evA ρ c with hedef
  have heE : InE e := evA_E _ _
  have heTB : e ∈ TB ρ σ := evA_TB hB hcσ
  have hpe : pi σ ρ e = evA σ c := pi_evA hσ hρ hB c hcσ
  have heE' : ω ^ e = e := heE
  have hseE : InE (evA σ c) := evA_E _ _
  have hseE' : ω ^ evA σ c = evA σ c := hseE
  rcases eq_or_lt_of_le hm1 with hγe | hγe
  · rw [← hγe, heE', hpe, hseE']; exact ⟨heTB, rfl⟩
  -- `γ = e + β`, `β ≥ 1`
  obtain ⟨hβTB, hpβ⟩ := TB_sub hB heTB hγ hm1 hγ1
  set β := γ - e with hβdef
  have heβ : e + β = γ := Ordinal.add_sub_cancel_of_le hm1
  have hβ1 : 1 ≤ β := by
    rcases eq_or_ne β 0 with h0 | h0
    · rw [h0, add_zero] at heβ; exact absurd heβ hγe.ne
    · exact one_le_iff_ne_zero.2 h0
  have hpγ : pi σ ρ γ = evA σ c + pi σ ρ β := by rw [← heβ, (pi_add hB heTB hβTB).2, hpe]
  have hpγlt : pi σ ρ γ < evA σ (c + 1) := by
    have := (pi_bijOn hB).2 hγ (evA_TB hB hc1σ) hm2
    rwa [pi_evA hσ hρ hB (c + 1) hc1σ] at this
  rcases eq_or_ne c 0 with hc0 | hc0
  · -- `e = ρ`: `ω^{ρ+β} = ϑᵖ(β)`
    have he0 : e = ρ := by rw [hedef, hc0, evA_zero hρE]
    have hs0 : evA σ c = σ := by rw [hc0, evA_zero hσE]
    rw [he0] at heβ
    rw [hs0] at hpγ
    have hm2' : γ < eN ρ := by
      have := hm2; rw [hc0, zero_add, ← zero_add (1 : Ordinal.{0}), evA_add_one, evA_zero hρE] at this
      exact this
    have hpγlt' : pi σ ρ γ < eN σ := by
      have := hpγlt; rw [hc0, zero_add, ← zero_add (1 : Ordinal.{0}), evA_add_one, evA_zero hσE] at this
      exact this
    have hβ1' : β < Om1 := lt_of_le_of_lt le_add_self (heβ ▸ hγ1)
    have hno : ∀ u, ρ < u → u ≤ ρ + β → ¬ InE u := fun u hu1 hu2 hE =>
      absurd (eN_le hu1 hE) (not_le.2 (lt_of_le_of_lt hu2 (heβ ▸ hm2')))
    have hv := vt_opow' hρE hρ1 hβ1 hβ1' hno
    obtain ⟨hvT, hvP⟩ := vt_mem hρE hρ1 hβTB.1 hβ1'
    rw [← heβ, ← hv]
    refine ⟨⟨hvT, by rw [hvP]; exact hβTB.2⟩, ?_⟩
    rw [pi_vt hB hβTB hβ1']
    have hpβ1 : 1 ≤ pi σ ρ β := by
      have := ((pi_bijOn hB).2.le_iff_le h1TB hβTB).2 hβ1; rwa [hp1] at this
    have hpβO : pi σ ρ β < Om1 := lt_of_le_of_lt le_add_self (hpγ ▸ (hpγlt'.trans (eN_lt_Om1K hσ1)))
    have hno' : ∀ u, σ < u → u ≤ σ + pi σ ρ β → ¬ InE u := fun u hu1 hu2 hE =>
      absurd (eN_le hu1 hE) (not_le.2 (lt_of_le_of_lt hu2 (hpγ ▸ hpγlt')))
    rw [vt_opow' hσE hσ1 hpβ1 hpβO hno', ← hpγ, heβ]
  · -- `e = ε_{ρ+c}`, `c ≥ 1`: `ω^{e+1+β'} = ϑᵖ(e + β')`
    obtain ⟨hβ'TB, hpβ'⟩ := TB_sub hB h1TB hβTB hβ1 (lt_of_le_of_lt le_add_self (heβ ▸ hγ1))
    set β' := β - 1 with hβ'def
    have h1β : 1 + β' = β := Ordinal.add_sub_cancel_of_le hβ1
    rw [hp1] at hpβ'
    have hre : ρ < e := by rw [hedef]; exact lt_evA hρE hc0
    have hse : σ < evA σ c := lt_evA hσE hc0
    have hξTB := pi_add hB heTB hβ'TB
    have hγ' : e + 1 + β' = γ := by rw [add_assoc, h1β, heβ]
    have hξ1 : e + β' < Om1 :=
      lt_of_le_of_lt (add_le_add (le_refl e) (le_add_self : β' ≤ 1 + β')) (by rw [← add_assoc, hγ']; exact hγ1)
    have hm2' : e + 1 + β' < eN e := by rw [hγ', hedef, ← evA_add_one]; exact hm2
    have hv := vt_ps hρE hρ1 heE hre hm2' hξ1
    obtain ⟨hvT, hvP⟩ := vt_mem hρE hρ1 hξTB.1.1 hξ1
    rw [← hγ', ← hv]
    refine ⟨⟨hvT, by rw [hvP]; exact hξTB.1.2⟩, ?_⟩
    rw [pi_vt hB hξTB.1 hξ1, hξTB.2, hpe]
    have hpβ'eq : pi σ ρ β = 1 + pi σ ρ β' := by
      have hpβ'le : 1 ≤ pi σ ρ β := by
        have := ((pi_bijOn hB).2.le_iff_le h1TB hβTB).2 hβ1; rwa [hp1] at this
      rw [hpβ', Ordinal.add_sub_cancel_of_le hpβ'le]
    have hpγ' : pi σ ρ γ = evA σ c + 1 + pi σ ρ β' := by rw [hpγ, hpβ'eq, add_assoc]
    have hlt' : evA σ c + 1 + pi σ ρ β' < eN (evA σ c) := by
      rw [← hpγ', ← evA_add_one]; exact hpγlt
    have hξ1' : evA σ c + pi σ ρ β' < Om1 :=
      lt_of_le_of_lt (add_le_add (le_refl _) (le_add_self : pi σ ρ β' ≤ 1 + pi σ ρ β'))
        (by rw [← add_assoc, ← hpγ']; exact hpγlt.trans (evA_lt_Om1 hσE hσ1 hc1σ.le))
    rw [vt_ps hσE hσ1 hseE hse hlt' hξ1', ← hpγ', hγ']

/-! ## Lemma EXACT -/

/-- **Lemma EXACT for `TEv`**: for `υ`-points `σ < ρ` (`Bases σ ρ`) and a term with constants below `σ`,
`t(ρ) ∈ Tᵖ[σ]` and `π_{σ,ρ}(t(ρ)) = t(σ)`. -/
theorem pi_valV {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) :
    ∀ t : TEv, CBv t σ → val t ρ ∈ TB ρ σ ∧ pi σ ρ (val t ρ) = val t σ
  | cst a, h => ⟨mem_TB_of_lt hB h, pi_lt hB h⟩
  | ec c, h => ⟨evA_TB hB h, pi_evA hσ hρ hB c h⟩
  | sm a b, h => by
    obtain ⟨h1, h2⟩ := pi_valV hσ hρ hB a h.1
    obtain ⟨h3, h4⟩ := pi_valV hσ hρ hB b h.2
    obtain ⟨h5, h6⟩ := pi_add hB h1 h3
    simp only [val_sm]
    exact ⟨h5, by rw [h6, h2, h4]⟩
  | pw t, h => by
    obtain ⟨h1, h2⟩ := pi_valV hσ hρ hB t h
    have hb := valV_lt hB.2.1 t (CBv_mono h hB.2.2.1.le)
    obtain ⟨h3, h4⟩ := pi_opowV hσ hρ hB h1 (cbd_lt hB.1 t h) hb
    simp only [val_pw]
    exact ⟨h3, by rw [h4, h2]⟩

/-- **Uniform comparison** (`≤`) of two terms at `υ`-points `σ < ρ`, constants below `σ`. -/
theorem uniV_le {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : TEv}
    (ht : CBv t σ) (hu : CBv u σ) : val t ρ ≤ val u ρ ↔ val t σ ≤ val u σ := by
  obtain ⟨h1, h2⟩ := pi_valV hσ hρ hB t ht
  obtain ⟨h3, h4⟩ := pi_valV hσ hρ hB u hu
  rw [← h2, ← h4]
  exact ((pi_bijOn hB).2.le_iff_le h1 h3).symm

theorem uniV_lt {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : TEv}
    (ht : CBv t σ) (hu : CBv u σ) : val t ρ < val u ρ ↔ val t σ < val u σ := by
  rw [← not_le, ← not_le, uniV_le hσ hρ hB hu ht]

theorem uniV_eq {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : TEv}
    (ht : CBv t σ) (hu : CBv u σ) : val t ρ = val u ρ ↔ val t σ = val u σ := by
  rw [le_antisymm_iff, le_antisymm_iff, uniV_le hσ hρ hB ht hu, uniV_le hσ hρ hB hu ht]

/-! ## The representation -/

/-- **Representation**: every ordinal below `ε_{ρ+ρ}` is the value at `ρ` of a term of `TEv` with constants
below `ρ`. -/
theorem repV {ρ : Ordinal.{0}} (hρ : InE ρ) :
    ∀ v, v < evA ρ ρ → ∃ t : TEv, CBv t ρ ∧ val t ρ = v := by
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  rcases lt_or_ge v ρ with hvρ | hρv
  · exact ⟨cst v, hvρ, rfl⟩
  by_cases hI : Indec v
  · by_cases hE : InE v
    · obtain ⟨c, hcρ, hc1, hc2⟩ := evA_bracket hρ hρv hv
      refine ⟨ec c, hcρ, ?_⟩
      rcases eq_or_lt_of_le hc1 with e | hlt
      · exact e
      · exact absurd (evA_succ_le hlt hE) (not_le.2 hc2)
    · obtain ⟨L, rfl⟩ := indec_eq_opow hI
      have hL : L < ω ^ L := lt_of_le_of_ne (right_le_opow _ one_lt_omega0)
        (fun h => hE (by unfold InE; rw [← h]; exact h.symm))
      obtain ⟨t, ht, e⟩ := IH L hL (hL.trans hv)
      exact ⟨pw t, ht, by rw [val_pw, e]⟩
  · have hD : DecompR0 v := not_not.1 hI
    rcases hD with h0 | ⟨u1, u2, hu1, hu2, hsum⟩
    · exact absurd h0 (lt_of_lt_of_le hρ.pos hρv).ne'
    obtain ⟨s1, h1, e1⟩ := IH u1 hu1 (hu1.trans hv)
    obtain ⟨s2, h2, e2⟩ := IH u2 hu2 (hu2.trans hv)
    exact ⟨sm s1 s2, ⟨h1, h2⟩, by rw [val_sm, e1, e2, hsum]⟩

/-! ## Lemma RS -/

/-- **Lemma RS with the target `t(ρ)`** (`t(ρ) ≥ ρ`, constants below `ρ`). -/
theorem rs_rstV {r : Ordinal.{0}} (h : RstK (upsilon r) (upsilon (r + ω)) (upsilon (r + ω + 1)))
    {s : TEv} (hs : CBv s (upsilon r)) (hρs : upsilon r ≤ val s (upsilon r))
    (htarget : ∀ κ' < upsilon r, ∃ μ, κ' < upsilon μ ∧ upsilon (μ + ω + 1) < upsilon r ∧
      RstK (upsilon μ) (upsilon (μ + ω)) (upsilon (μ + ω + 1)) ∧
      ∀ g, upsilon μ ≤ g → g ≤ upsilon (μ + ω + 1) + val s (upsilon μ) → le1 (upsilon μ) g) :
    le1 (upsilon r) (upsilon (r + ω + 1) + val s (upsilon r) + 1) := by
  classical
  have hnx := upsilon_isNext r
  have hCs : ∀ σ, (∀ c ∈ (csv s).toFinset, c < σ) → CBv s σ := fun σ hσ =>
    (cbv_iff s σ).2 (fun c hc => hσ c (List.mem_toFinset.2 hc))
  refine rs_rstF (T := val s) (C := (csv s).toFinset) h
    (fun c hc => (cbv_iff s _).1 hs c (List.mem_toFinset.1 hc)) hρs
    ((valV_lt h.ρE s hs).trans (evA_lt_ups h.ρE h.ρ1 (cbd_lt h.ρE s hs).le hnx.1 hnx.2.1)) ?_ ?_ htarget
  · intro σ hσ hB hCσ _
    exact (pi_valV hσ h.ρU hB s (hCs σ hCσ)).2
  · intro σ hσE hσρ _ hCσ
    have hCB := hCs σ hCσ
    exact (valV_lt hσE s hCB).trans
      (evA_lt_next hσE (hσρ.trans h.ρ1) (cbd_lt hσE s hCB).le _ hσρ h.ρU.2)

/-- **Lemma RS for every term of `TEv`** with constants below `ρ_λ`. -/
theorem rsStep_V {l : Ordinal.{0}} (hl : 0 < l) {s : TEv} (hs : CBv s (upsilon l)) : RsStep l (val s) := by
  by_cases hρs : upsilon l ≤ val s (upsilon l)
  · exact fun R htg => rs_rstV R hs hρs htg
  · have hn : noE s := by
      by_contra hn
      exact hρs (le_valV_of_not_noE (upsPt_inE (upsPt_upsilon hl)) s hn)
    set c := val s (upsilon l) with hc
    have e : val s = OT.ev (OT.k c) := funext (fun y => by rw [OT.ev_k, hc, valV_noE s hn y])
    have hcb : OT.CB (OT.k c) (upsilon l) := not_le.1 hρs
    rw [e]
    exact fun R htg => rs_rstT R hcb htg

end Googology.Trans.PoR.InaccPsi.R2

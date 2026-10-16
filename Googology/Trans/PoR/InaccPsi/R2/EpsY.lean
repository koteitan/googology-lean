import Googology.Trans.PoR.InaccPsi.R2.EpsX

/-!
# Terms below `ε_{x+2}`: Lemma EXACT and Lemma RS

The terms `OTY` with the pseudo-base `ε_{x+1}`: a term `t` of `OT` (`kk t`, value below `ε_{x+1}`), an atom
`ω^{ε_{x+1}+s}` (`ew s`, `s` again in `OTY`), or a sum.  Their values at `x = ρ` are exactly the ordinals
below `ε_{ρ+2} = ε_{ε_{ρ+1}+1}` (`repY`).

* `OTY`, `ev2`, `CBY`, `csY`, `hasE` (an atom at the top: the value is `≥ ε_{x+1}`, `hasE_iff`), `big` (an
  atom `ω^{ε+s}` with `s ≥ ε` at the top: the value is `≥ ω^{ε_{x+1}·2}`, `big_iff`), `toOT` (a term
  without atom is a term of `OT`); `ev2_lt` (`ev2 s x < ε_{x+2}`), `repY` (**representation**);
* `eNN_lt_ups` (`ε_{b+2}` is below every `υ`-point above `b`: `ε_{b+2} ≤ ϑ^{ϑᵇ(Δ₁)}(Δ₁) = ϑᵇ(Δ₁+1) ∈ Tᵇ`,
  [W07a] Lemma 4.3, Conv. 4.1, Lemma 6.3, [W07b] Cor 5.10);
* `vt_eN2` (`ϑʳ(ε_{r+1} + β') = ω^{ε_{r+1}+1+β'}` below `ε_{r+2}`), `pi_atomY` (**Lemma EXACT for the
  atom `ω^{ε_{x+1}+β}`** for every `β ∈ Tᵖ[σ]` below `ε_{ρ+2}`), `pi_evY` (**Lemma EXACT for `OTY`**, once
  `ε_{ρ+1} ∈ Tᵖ[σ]`), `eN_TB_of_ge` (`ε_{ρ+1} ∈ Tᵖ[σ]` once some point of `Tᵖ[σ] ∩ [ε_{ρ+1}, ε_{ρ+2})` is:
  the leading component `ω^L` is `ϑᵖ(ξ)` with `ξ ≥ ε_{ρ+1}` smaller, [W07a] Def 3.28, `vt_mem`), `pi_eYt`;
* `rs_rstY` (**Lemma RS with the target `ev2 s`**, `s` with an atom at the top).

No new axiom.

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order OT

/-- Terms below `ε_{x+2}`: a term of `OT` (`kk t`), an atom `ω^{ε_{x+1}+s}` (`ew s`), or a sum. -/
inductive OTY : Type 1
  | kk : OT → OTY
  | ew : OTY → OTY
  | ad : OTY → OTY → OTY

namespace OTY

/-- The value of a term at `x`. -/
noncomputable def ev2 : OTY → Ordinal.{0} → Ordinal.{0}
  | kk t, x => ev t x
  | ew s, x => ω ^ (eN x + ev2 s x)
  | ad a b, x => ev2 a x + ev2 b x

/-- All constants below `σ`. -/
def CBY : OTY → Ordinal.{0} → Prop
  | kk t, σ => CB t σ
  | ew s, σ => CBY s σ
  | ad a b, σ => CBY a σ ∧ CBY b σ

/-- The constants. -/
def csY : OTY → List Ordinal.{0}
  | kk t => cs t
  | ew s => csY s
  | ad a b => csY a ++ csY b

/-- An atom at the top. -/
def hasE : OTY → Prop
  | kk _ => False
  | ew _ => True
  | ad a b => hasE a ∨ hasE b

/-- An atom `ω^{ε+s}` with `hasE s` at the top. -/
def big : OTY → Prop
  | kk _ => False
  | ew s => hasE s
  | ad a b => big a ∨ big b

/-- A term without atom as a term of `OT`. -/
def toOT : OTY → OT
  | kk t => t
  | ew _ => k 0
  | ad a b => add (toOT a) (toOT b)

@[simp] theorem ev2_kk (t : OT) (x : Ordinal.{0}) : ev2 (kk t) x = ev t x := rfl
@[simp] theorem ev2_ew (s : OTY) (x : Ordinal.{0}) : ev2 (ew s) x = ω ^ (eN x + ev2 s x) := rfl
@[simp] theorem ev2_ad (a b : OTY) (x : Ordinal.{0}) : ev2 (ad a b) x = ev2 a x + ev2 b x := rfl

theorem cbY_iff : ∀ (s : OTY) (σ : Ordinal.{0}), CBY s σ ↔ ∀ c ∈ csY s, c < σ
  | kk t, σ => cb_iff t σ
  | ew s, σ => cbY_iff s σ
  | ad a b, σ => by
      simp only [CBY, csY, List.mem_append]
      rw [cbY_iff a σ, cbY_iff b σ]
      constructor
      · rintro ⟨h1, h2⟩ c (hc | hc)
        · exact h1 c hc
        · exact h2 c hc
      · intro h; exact ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩

theorem CBY_mono {s : OTY} {σ σ' : Ordinal.{0}} (h : CBY s σ) (hs : σ ≤ σ') : CBY s σ' :=
  (cbY_iff s σ').2 (fun c hc => lt_of_lt_of_le ((cbY_iff s σ).1 h c hc) hs)

end OTY

open OTY

/-! ## Bounds -/

theorem eN_lt_eNN (x : Ordinal.{0}) : eN x < eN (eN x) := lt_eN _

/-- `ev2 s x < ε_{x+2}`. -/
theorem ev2_lt {x : Ordinal.{0}} : ∀ s : OTY, CBY s x → ev2 s x < eN (eN x)
  | kk t, h => (ev_lt_eN h).trans (eN_lt_eNN x)
  | ew s, h => by
    have hE := eN_E (eN x)
    have h1 : eN x + ev2 s x < eN (eN x) := (inE_indec hE).add_lt (eN_lt_eNN x) (ev2_lt s h)
    have h2 := (opow_lt_opow_iff_right one_lt_omega0).2 h1
    have hE' : ω ^ eN (eN x) = eN (eN x) := hE
    rw [hE'] at h2
    exact h2
  | ad a b, h => (inE_indec (eN_E _)).add_lt (ev2_lt a h.1) (ev2_lt b h.2)

/-- **A term has value `≥ ε_{x+1}` iff it has an atom at the top.** -/
theorem hasE_iff {x : Ordinal.{0}} : ∀ s : OTY, CBY s x → (eN x ≤ ev2 s x ↔ hasE s)
  | kk t, h => by
    simp only [ev2_kk, hasE, iff_false, not_le]; exact ev_lt_eN h
  | ew s, _ => by simp only [ev2_ew, hasE, iff_true]; exact eN_le_atom x _
  | ad a b, h => by
    simp only [ev2_ad, hasE]
    rw [← hasE_iff a h.1, ← hasE_iff b h.2]
    constructor
    · intro hle
      by_contra hno
      push Not at hno
      exact absurd hle (not_le.2 ((inE_indec (eN_E x)).add_lt hno.1 hno.2))
    · rintro (h1 | h1)
      · exact h1.trans le_self_add
      · exact h1.trans le_add_self

/-- **A term has value `≥ ω^{ε_{x+1}·2}` iff it has an atom `ω^{ε+s}` with `hasE s` at the top.** -/
theorem big_iff {x : Ordinal.{0}} : ∀ s : OTY, CBY s x →
    (ω ^ (eN x + eN x) ≤ ev2 s x ↔ big s)
  | kk t, h => by
    simp only [ev2_kk, big, iff_false, not_le]
    exact (ev_lt_eN h).trans_le (eN_le_atom x _)
  | ew s, h => by
    simp only [ev2_ew, big]
    rw [opow_le_opow_iff_right one_lt_omega0, add_le_add_iff_left]
    exact hasE_iff s h
  | ad a b, h => by
    simp only [ev2_ad, big]
    rw [← big_iff a h.1, ← big_iff b h.2]
    constructor
    · intro hle
      by_contra hno
      push Not at hno
      exact absurd hle (not_le.2 (isPrincipal_add_omega0_opow _ hno.1 hno.2))
    · rintro (h1 | h1)
      · exact h1.trans le_self_add
      · exact h1.trans le_add_self

/-- A term without atom is a term of `OT`. -/
theorem toOT_spec : ∀ s : OTY, ¬ hasE s →
    (∀ x, ev2 s x = ev (toOT s) x) ∧ ∀ σ, CBY s σ → CB (toOT s) σ
  | kk t, _ => ⟨fun _ => rfl, fun _ h => h⟩
  | ew s, h => absurd trivial h
  | ad a b, h => by
    simp only [hasE, not_or] at h
    obtain ⟨h1, h2⟩ := toOT_spec a h.1
    obtain ⟨h3, h4⟩ := toOT_spec b h.2
    exact ⟨fun x => by simp only [ev2_ad, toOT, ev_add, h1 x, h3 x],
      fun σ hσ => ⟨h2 σ hσ.1, h4 σ hσ.2⟩⟩

/-- `ε_{b+2}` is below every `υ`-point above a countable `υ`-point `b`. -/
theorem eNN_lt_ups {b : Ordinal.{0}} (hb : UpsPt b) (hb1 : b < Om1) :
    ∀ u, b < u → UpsPt u → eN (eN b) < u := by
  have hbE := upsPt_inE hb
  obtain ⟨m, hbm, hm, hmin, hT, -⟩ := T_next (Or.inr hbE) hb1
  obtain ⟨hDT, hD1, -⟩ := Dp_spec hbE hb1 (le_refl 1)
  obtain ⟨-, hDl1, -⟩ := Dl_spec hbE hb1 1
  obtain ⟨hbD, hDE, -⟩ := Dl_E hbE hb1 (le_refl 1)
  obtain ⟨hDD, hDDE, -⟩ := Dl_E hDE hDl1 (le_refl 1)
  have heD : eN b ≤ Dl b 1 := eN_le hbD hDE
  have h1 : eN (eN b) ≤ Dl (Dl b 1) 1 := eN_le (lt_of_le_of_lt heD hDD) hDDE
  have hDp : Dp b 1 = Dl (Dl b 1) 1 := (Dp_spec hbE hb1 (le_refl 1)).2.2
  have h2 : Dp b 1 < m := (hT _ hD1).1 hDT
  intro u hbu hu
  rw [← hDp] at h1
  exact lt_of_le_of_lt h1 (lt_of_lt_of_le h2 (hmin u hbu hu.2))

theorem eNN_lt_Om1 {b : Ordinal.{0}} (hb : UpsPt b) (hb1 : b < Om1) : eN (eN b) < Om1 := by
  obtain ⟨m, hbm, hm, -, -, hm1⟩ := T_next (Or.inr (upsPt_inE hb)) hb1
  exact (eNN_lt_ups hb hb1 m hbm ⟨lt_of_le_of_lt zero_le hbm, hm⟩).trans hm1

/-- **Representation**: every ordinal below `ε_{ρ+2}` is the value at `ρ` of a term of `OTY` with constants
below `ρ`. -/
theorem repY {ρ : Ordinal.{0}} (hρ : InE ρ) : ∀ v, v < eN (eN ρ) → ∃ s : OTY, CBY s ρ ∧ ev2 s ρ = v := by
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  rcases lt_or_ge v (eN ρ) with hve | hev
  · obtain ⟨t, ht, e⟩ := rep hρ v hve
    exact ⟨kk t, ht, e⟩
  by_cases hI : Indec v
  · obtain ⟨L, rfl⟩ := indec_eq_opow hI
    have he' : ω ^ eN ρ = eN ρ := eN_E ρ
    have hL : eN ρ ≤ L := (opow_le_opow_iff_right one_lt_omega0).1 (by rw [he']; exact hev)
    set β := L - eN ρ with hβ
    have hLβ : eN ρ + β = L := Ordinal.add_sub_cancel_of_le hL
    have hβv : β < ω ^ L := by
      rcases eq_or_lt_of_le hL with e | hlt
      · rw [hβ, ← e, Ordinal.sub_self]; exact opow_pos _ omega0_pos
      · have hnE : ¬ InE L := fun hE =>
          absurd (lt_of_le_of_lt (eN_le hlt hE) (lt_of_le_of_lt (right_le_opow L one_lt_omega0) hv))
            (lt_irrefl _)
        have : L < ω ^ L := lt_of_le_of_ne (right_le_opow _ one_lt_omega0) (fun h => hnE h.symm)
        exact lt_of_le_of_lt ((le_add_self : β ≤ eN ρ + β).trans hLβ.le) this
    obtain ⟨s, hs, e⟩ := IH β hβv (hβv.trans hv)
    exact ⟨ew s, hs, by rw [ev2_ew, e, hLβ]⟩
  · have hD : DecompR0 v := not_not.1 hI
    rcases hD with h0 | ⟨u1, u2, hu1, hu2, hsum⟩
    · exact absurd h0 (lt_of_lt_of_le (eN_E ρ).pos hev).ne'
    obtain ⟨s1, h1, e1⟩ := IH u1 hu1 (hu1.trans hv)
    obtain ⟨s2, h2, e2⟩ := IH u2 hu2 (hu2.trans hv)
    exact ⟨ad s1 s2, ⟨h1, h2⟩, by rw [ev2_ad, e1, e2, hsum]⟩

/-! ## Lemma EXACT -/

/-- `ϑʳ(ε_{r+1} + β') = ω^{ε_{r+1}+1+β'}` for `ε_{r+1} + β' < ε_{r+2}` ([W07a] Lemma 4.2, `wbar_eq` with the
pseudo-base `ε_{r+1}`). -/
theorem vt_eN2 {r β' : Ordinal.{0}} (hr : InE r) (hr1 : r < Om1) (hβ : eN r + β' < eN (eN r))
    (he1 : eN r + β' < Om1) : vt r (eN r + β') = ω ^ (eN r + 1 + β') := by
  have he := eN_E r
  have hω : ω ≤ eN r + β' := (omega0_le_eN r).trans le_self_add
  rw [← one_add_of_omega0_le hω, vt_wbar hr hr1 he1, ← add_assoc, add_eN]
  refine wbar_eq he β' ?_
  intro u hu1 hu2 huE
  have hβ' : β' < eN (eN r) := lt_of_le_of_lt le_add_self hβ
  have h1 : 1 + β' < eN (eN r) :=
    (inE_indec (eN_E _)).add_lt (one_lt_omega0.trans_le (omega0_le_eN _)) hβ'
  have h2 : eN r + (1 + β') < eN (eN r) := (inE_indec (eN_E _)).add_lt (eN_lt_eNN r) h1
  have h3 : eN (eN r) ≤ u := eN_le hu1 huE
  rw [add_assoc] at hu2
  exact absurd (hu2.trans_lt (h2.trans_le h3)) (lt_irrefl _)

/-- **Lemma EXACT for the atom `ω^{ε_{x+1}+β}`** (`β ∈ Tᵖ[σ]` below `ε_{ρ+2}`, its image below `ε_{σ+2}`), once
`ε_{ρ+1} ∈ Tᵖ[σ]`. -/
theorem pi_atomY {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ)
    (heTB : eN ρ ∈ TB ρ σ) {β : Ordinal.{0}} (hβTB : β ∈ TB ρ σ) (hβ : β < eN (eN ρ))
    (hπβ : pi σ ρ β < eN (eN σ)) :
    ω ^ (eN ρ + β) ∈ TB ρ σ ∧ pi σ ρ (ω ^ (eN ρ + β)) = ω ^ (eN σ + pi σ ρ β) := by
  rcases lt_or_ge β σ with hβσ | hσβ
  · rw [pi_lt hB hβσ]; exact pi_eAtom hσ hρ hB heTB hβσ
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hpe := pi_eN hσ hρ hB heTB
  have hee1 := eNN_lt_Om1 hρ hρ1
  have hes1 := eNN_lt_Om1 hσ hσ1
  have hωβ : ω ≤ β := (omega0_lt_inE hB.1).le.trans hσβ
  obtain ⟨hξTB, hpξ⟩ := pi_add hB heTB hβTB
  rw [hpe] at hpξ
  have hξ : eN ρ + β < eN (eN ρ) := (inE_indec (eN_E _)).add_lt (eN_lt_eNN ρ) hβ
  have hξ1 : eN ρ + β < Om1 := hξ.trans hee1
  have hv := vt_eN2 hB.2.1 hρ1 hξ hξ1
  rw [add_assoc, one_add_of_omega0_le hωβ] at hv
  obtain ⟨hvT, hvP⟩ := vt_mem hB.2.1 hρ1 hξTB.1 hξ1
  refine ⟨by rw [← hv]; exact ⟨hvT, by rw [hvP]; exact hξTB.2⟩, ?_⟩
  have hωπ : ω ≤ pi σ ρ β := (omega0_lt_inE hB.1).le.trans (pi_ge hB hβTB hσβ)
  have hξ' : eN σ + pi σ ρ β < eN (eN σ) := (inE_indec (eN_E _)).add_lt (eN_lt_eNN σ) hπβ
  have hv' := vt_eN2 hB.1 hσ1 hξ' (hξ'.trans hes1)
  rw [add_assoc, one_add_of_omega0_le hωπ] at hv'
  rw [← hv, pi_vt hB hξTB hξ1, hpξ, hv']

/-- **Lemma EXACT for `OTY`**: for constants below `σ`, `s(ρ) ∈ Tᵖ[σ]` and `π_{σ,ρ}(s(ρ)) = s(σ)`, once
`ε_{ρ+1} ∈ Tᵖ[σ]`. -/
theorem pi_evY {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ)
    (heTB : eN ρ ∈ TB ρ σ) : ∀ s : OTY, CBY s σ → ev2 s ρ ∈ TB ρ σ ∧ pi σ ρ (ev2 s ρ) = ev2 s σ
  | kk t, h => pi_ev hB t h
  | ew s, h => by
    obtain ⟨h1, h2⟩ := pi_evY hσ hρ hB heTB s h
    have hβ := ev2_lt s (CBY_mono h hB.2.2.1.le)
    have hπ : pi σ ρ (ev2 s ρ) < eN (eN σ) := by rw [h2]; exact ev2_lt s h
    obtain ⟨h3, h4⟩ := pi_atomY hσ hρ hB heTB h1 hβ hπ
    rw [h2] at h4
    exact ⟨h3, h4⟩
  | ad a b, h => by
    obtain ⟨h1, h2⟩ := pi_evY hσ hρ hB heTB a h.1
    obtain ⟨h3, h4⟩ := pi_evY hσ hρ hB heTB b h.2
    obtain ⟨h5, h6⟩ := pi_add hB h1 h3
    simp only [ev2_ad]
    exact ⟨h5, by rw [h6, h2, h4]⟩

/-- **`ε_{ρ+1} ∈ Tᵖ[σ]` once some point of `Tᵖ[σ] ∩ [ε_{ρ+1}, ε_{ρ+2})` is.** -/
theorem eN_TB_of_ge {σ ρ : Ordinal.{0}} (hρ : UpsPt ρ) (hB : Bases σ ρ) :
    ∀ x, x ∈ TB ρ σ → eN ρ ≤ x → x < eN (eN ρ) → eN ρ ∈ TB ρ σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hρE := hB.2.1
  have hee1 := eNN_lt_Om1 hρ hρ1
  have he' : ω ^ eN ρ = eN ρ := eN_E ρ
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx hex hxe
  have hx0 : x ≠ 0 := (lt_of_lt_of_le (eN_E ρ).pos hex).ne'
  have hx1 : x < Om1 := hxe.trans hee1
  set L := log ω x with hLdef
  have hL : eN ρ ≤ L := le_log_of_opow_le one_lt_omega0 (by rw [he']; exact hex)
  have hLx : ω ^ L ≤ x := opow_log_le_self ω hx0
  have hc := Par_comps hρE hρ1 hx.1 ((lt_eN ρ).le.trans hex) hx1 (lead_comp hx0)
  obtain ⟨haT, haP⟩ := hc.2 ((lt_eN ρ).le.trans (by
    have := (opow_le_opow_iff_right one_lt_omega0).2 hL
    rwa [he'] at this))
  have haTB : ω ^ L ∈ TB ρ σ := ⟨haT, fun p hp => hx.2 (Finset.mem_coe.2 (haP (Finset.mem_coe.1 hp)))⟩
  rcases eq_or_lt_of_le hL with e | hlt
  · rw [← e, he'] at haTB; exact haTB
  set β' := L - (eN ρ + 1) with hβ'
  have hLβ : eN ρ + 1 + β' = L := Ordinal.add_sub_cancel_of_le (add_one_le_of_lt hlt)
  have hLe : L < eN (eN ρ) := lt_of_le_of_lt ((right_le_opow L one_lt_omega0).trans hLx) hxe
  have hξL : eN ρ + β' ≤ L := by rw [← hLβ, add_assoc]; exact add_le_add le_rfl le_add_self
  have hξ : eN ρ + β' < eN (eN ρ) := lt_of_le_of_lt hξL hLe
  have hξ1 : eN ρ + β' < Om1 := hξ.trans hee1
  have hξT : eN ρ + β' ∈ Tset ρ := mem_T_below hρ hρ1 (fun u hu1 hu2 =>
    hξ.trans (eNN_lt_ups hρ hρ1 u hu1 hu2)) hξ1
  have hv := vt_eN2 hρE hρ1 hξ hξ1
  rw [hLβ] at hv
  obtain ⟨-, hvP⟩ := vt_mem hρE hρ1 hξT hξ1
  have hξTB : eN ρ + β' ∈ TB ρ σ := ⟨hξT, by rw [← hvP, hv]; exact haTB.2⟩
  have hnE : ¬ InE L := fun hE => absurd (eN_le hlt hE) (not_le.2 hLe)
  have hLlt : L < ω ^ L := lt_of_le_of_ne (right_le_opow _ one_lt_omega0) (fun h => hnE h.symm)
  exact IH _ (lt_of_le_of_lt hξL (hLlt.trans_le hLx)) hξTB le_self_add hξ

/-- **Lemma EXACT for a term with an atom at the top**: if `s(ρ) ∈ Tᵖ[σ]` then `π_{σ,ρ}(s(ρ)) = s(σ)`. -/
theorem pi_eYt {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {s : OTY}
    (hE : hasE s) (hs : CBY s σ) (hx : ev2 s ρ ∈ TB ρ σ) : pi σ ρ (ev2 s ρ) = ev2 s σ := by
  have hsρ := CBY_mono hs hB.2.2.1.le
  have heTB := eN_TB_of_ge hρ hB _ hx ((hasE_iff s hsρ).2 hE) (ev2_lt s hsρ)
  exact (pi_evY hσ hρ hB heTB s hs).2

/-! ## Lemma RS -/

/-- **Lemma RS with the target `ev2 s`** (`s` with an atom at the top, constants below `ρ`): if restarts
`ρ_μ` with `ρ_μ ≤₁ δ_μ + s(ρ_μ)` lie above every `κ' < ρ` (with `δ_μ < ρ`), then `ρ ≤₁ δ + s(ρ) + 1`. -/
theorem rs_rstY {r : Ordinal.{0}} (h : RstK (upsilon r) (upsilon (r + ω)) (upsilon (r + ω + 1)))
    {s : OTY} (hE : hasE s) (hs : CBY s (upsilon r))
    (htarget : ∀ κ' < upsilon r, ∃ μ, κ' < upsilon μ ∧ upsilon (μ + ω + 1) < upsilon r ∧
      RstK (upsilon μ) (upsilon (μ + ω)) (upsilon (μ + ω + 1)) ∧
      ∀ g, upsilon μ ≤ g → g ≤ upsilon (μ + ω + 1) + ev2 s (upsilon μ) → le1 (upsilon μ) g) :
    le1 (upsilon r) (upsilon (r + ω + 1) + ev2 s (upsilon r) + 1) := by
  classical
  have hnx := upsilon_isNext r
  have hCs : ∀ σ, (∀ c ∈ (csY s).toFinset, c < σ) → CBY s σ := fun σ hσ =>
    (cbY_iff s σ).2 (fun c hc => hσ c (List.mem_toFinset.2 hc))
  refine rs_rstF (T := ev2 s) (C := (csY s).toFinset) h
    (fun c hc => (cbY_iff s _).1 hs c (List.mem_toFinset.1 hc))
    ((lt_eN _).le.trans ((hasE_iff s hs).2 hE))
    ((ev2_lt s hs).trans (eNN_lt_ups h.ρU h.ρ1 _ hnx.1 hnx.2.1)) ?_ ?_ htarget
  · intro σ hσ hB hCσ hTB
    exact pi_eYt hσ h.ρU hB hE (hCs σ hCσ) hTB
  · intro σ hσE hσρ heσ hCσ
    exact lt_of_lt_of_le (ev2_lt s (hCs σ hCσ)) (eN_le heσ h.ρE)

end Googology.Trans.PoR.InaccPsi.R2

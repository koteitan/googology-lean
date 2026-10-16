import Googology.Trans.PoR.InaccPsi.R2.EpsM

/-!
# The atoms `ω^{ε_{x+1}+β}` and the terms `ε_{x+1}·q + t` (`q`, `β` constants): EXACT, IMG and RS

The offset terms `ε_{x+1}·q + t` with a constant multiplier `0 < q` below the base and `t` a term of `OT`;
`ε_{x+1}·q` is a sum of atoms `ε_{x+1}·ω^β = ω^{ε_{x+1}+β}` with constants `β`.  The first new atom is
`ω^{ε_{x+1}+1} = ε_{x+1}·ω`, the value of the offset at `Λ_{ε·ω}`.  Here `ε_{x+1}` plays the part of a
base: the atom `ω^{ε+β}` is to `ε` what `ω^{x+β}` is to `x` in `R2.TopO`.

* `eN_mul_opow` (`ε·ω^β = ω^{ε+β}`), `mul_lt_inE` (`ε`-numbers are closed under `·`), `omega0_lt_inE`;
* `vt_eN` (`ϑʳ(ε_{r+1} + β') = ω^{ε_{r+1}+1+β'}` for `β' < ε_{r+1}`: [W07a] Lemma 4.2 (`vt_wbar`) and
  `wbar_eq` with the pseudo-base `ε_{r+1}`; the `ε`-numbers below `ε_{r+1}` do not move the index, since
  `r + ε_{r+1} = ε_{r+1}`);
* `pi_eAtom` (**Lemma EXACT for the atom `ω^{ε_{x+1}+β}`**, `β < σ`: `π_{σ,ρ}(ω^{ε_{ρ+1}+β}) = ω^{ε_{σ+1}+β}`
  once `ε_{ρ+1} ∈ Tᵖ[σ]`; [W07a] Def 5.1 fourth clause (`pi_vt`), Def 3.22/3.28 (`vt_mem`), Lemma 5.3 (c)
  (`pi_add`) and `pi_eN` of stage 7), `eN_TB_of_atom` (`ε_{ρ+1} ∈ Tᵖ[σ]` once an atom `ω^{ε_{ρ+1}+β}` is:
  its parameters are those of `ε_{ρ+1} + β'`, [W07a] Def 3.28, `vt_mem`, `Par_comps`), `pi_eQ`,
  `log_eQt`, `pi_eQt` (**Lemma EXACT for `ε_{x+1}·q + t`**);
* `RstK.pkg_atom` (**Lemma IMG for the atom `ω^{ε_{x+1}+β}`**, `β < ρ`, by induction on `β`: `β = 0` is
  `pkg_eN`; `β = β'' + 1`: the copy of `ω^{ε+β''+1}` is an indecomposable above the copy of `ω^{ε+β''}`;
  `β = β'' + ω^z`, `z > 0`: the source atom `ω^{ε+β} ≤₁ ω^{ε+β} + z` of `R₁⁺` ([W07b] Theorem 2.2,
  `le1R_thm22`, `logend(ε + β) ≥ z`) holds inside the block (`RstK.lowδ`), the copy keeps it, and below `ρ`
  the copy is a `υ`-point or has its `R₁⁺` reach, so its exponent is a multiple of `ω^z` above
  `ε_{f(ρ)+1} + β''`), `RstK.pkg_eQ`, `RstK.pkg_eQt` (the packages of `ε_{x+1}·q` and `ε_{x+1}·q + t`);
* `rs_rstQ` (**Lemma RS with the target `ε_{x+1}·q + t`**: `rs_rstF` of stage 7 with this `T`).

No new axiom.

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order OT

/-! ## Arithmetic -/

/-- `ε·ω^β = ω^{ε+β}` for `ε = ε_{x+1}`. -/
theorem eN_mul_opow (x β : Ordinal.{0}) : eN x * ω ^ β = ω ^ (eN x + β) := by
  rw [opow_add]
  have h : ω ^ eN x = eN x := eN_E x
  rw [h]

/-- `ε`-numbers are closed under multiplication. -/
theorem mul_lt_inE {u a b : Ordinal.{0}} (hu : InE u) (ha : a < u) (hb : b < u) : a * b < u := by
  have h : ω ^ ω ^ u = u := by
    have hu' : ω ^ u = u := hu
    rw [hu', hu']
  rw [← h] at ha hb ⊢
  exact isPrincipal_mul_omega0_opow_opow u ha hb

theorem omega0_le_eN (x : Ordinal.{0}) : ω ≤ eN x := by
  have h1 : (1 : Ordinal.{0}) ≤ eN x := one_le_iff_pos.2 (eN_E x).pos
  have h2 : ω ^ (1 : Ordinal.{0}) ≤ ω ^ eN x := opow_le_opow_right omega0_pos h1
  rw [opow_one] at h2
  have h : ω ^ eN x = eN x := eN_E x
  rwa [h] at h2

theorem le_mul_pos (a : Ordinal.{0}) {q : Ordinal.{0}} (hq : 0 < q) : a ≤ a * q :=
  calc a = a * 1 := (mul_one a).symm
    _ ≤ a * q := mul_le_mul_right (one_le_iff_pos.2 hq) a

theorem omega0_le_inE {x : Ordinal.{0}} (hx : InE x) : ω ≤ x := by
  have h1 : (1 : Ordinal.{0}) ≤ x := one_le_iff_pos.2 hx.pos
  have h2 : ω ^ (1 : Ordinal.{0}) ≤ ω ^ x := opow_le_opow_right omega0_pos h1
  have hx' : ω ^ x = x := hx
  rwa [opow_one, hx'] at h2

theorem omega0_lt_inE {x : Ordinal.{0}} (hx : InE x) : ω < x := by
  rcases (omega0_le_inE hx).lt_or_eq with h | h
  · exact h
  · exfalso
    have hx' : ω ^ x = x := hx
    rw [← h] at hx'
    have : ω ^ (1 : Ordinal.{0}) < ω ^ ω := (opow_lt_opow_iff_right one_lt_omega0).2 one_lt_omega0
    rw [opow_one, hx'] at this
    exact lt_irrefl _ this

/-- `x + ε_{x+1} = ε_{x+1}`. -/
theorem add_eN (x : Ordinal.{0}) : x + eN x = eN x := by
  have h : ω ^ eN x = eN x := eN_E x
  have := add_omega0_opow (a := x) (b := eN x) (by rw [h]; exact lt_eN x)
  rwa [h] at this

/-! ## Lemma EXACT -/

/-- `ϑʳ(ε_{r+1} + β') = ω^{ε_{r+1}+1+β'}` for `β' < ε_{r+1}` ([W07a] Lemma 4.2 and `wbar_eq` with the
pseudo-base `ε_{r+1}`). -/
theorem vt_eN {r β' : Ordinal.{0}} (hr : InE r) (hr1 : r < Om1) (hβ : β' < eN r)
    (he1 : eN r + β' < Om1) : vt r (eN r + β') = ω ^ (eN r + 1 + β') := by
  have he := eN_E r
  have hω : ω ≤ eN r + β' := (omega0_le_eN r).trans le_self_add
  rw [← one_add_of_omega0_le hω, vt_wbar hr hr1 he1, ← add_assoc, add_eN]
  refine wbar_eq he β' ?_
  intro u hu1 hu2 huE
  have h1 : 1 + β' < eN r := (inE_indec he).add_lt (one_lt_omega0.trans_le (omega0_le_eN r)) hβ
  have h2 : eN r + eN r < u := (inE_indec huE).add_lt hu1 hu1
  rw [add_assoc] at hu2
  exact absurd (hu2.trans_lt ((add_lt_add_iff_left _).2 h1)) (not_lt.2 h2.le)

/-- A point below the next `υ`-point after a countable `υ`-point `b` is in `Tᵇ`. -/
theorem mem_T_below {b y : Ordinal.{0}} (hb : UpsPt b) (hb1 : b < Om1)
    (hy : ∀ u, b < u → UpsPt u → y < u) (hy1 : y < Om1) : y ∈ Tset b := by
  obtain ⟨m, hbm, hm, -, hT, hm1⟩ := T_next (Or.inr (upsPt_inE hb)) hb1
  exact (hT y hy1).2 (hy m hbm ⟨lt_of_le_of_lt zero_le hbm, hm⟩)

/-- `ε_{b+1} + β' < u` for every `υ`-point `u > b` and `β' < ε_{b+1}`. -/
theorem eN_add_lt_ups {b β' : Ordinal.{0}} (hb : UpsPt b) (hb1 : b < Om1) (hβ : β' < eN b) :
    ∀ u, b < u → UpsPt u → eN b + β' < u := by
  obtain ⟨-, -, hlt⟩ := eN_lt_upsPt hb hb1
  intro u hbu hu
  exact (indec_of_upsPt hu).add_lt (hlt u hbu hu) (hβ.trans (hlt u hbu hu))

/-- **`ε_{ρ+1} ∈ Tᵖ[σ]` once an atom `ω^{ε_{ρ+1}+β}` (`β < ε_{ρ+1}`) is in `Tᵖ[σ]`.** -/
theorem eN_TB_of_atom {σ ρ : Ordinal.{0}} (hρ : UpsPt ρ) (hB : Bases σ ρ) {β : Ordinal.{0}}
    (hβ : β < eN ρ) (hx : ω ^ (eN ρ + β) ∈ TB ρ σ) : eN ρ ∈ TB ρ σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hρE := hB.2.1
  obtain ⟨he1, heT, -⟩ := eN_lt_upsPt hρ hρ1
  rcases eq_or_ne β 0 with rfl | hβ0
  · have h : ω ^ eN ρ = eN ρ := eN_E ρ
    rwa [add_zero, h] at hx
  set β' := β - 1 with hβ'
  have hb : 1 + β' = β := Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 hβ0)
  have hβ'e : β' < eN ρ := lt_of_le_of_lt (sub_le_self β 1) hβ
  have hξ1 : eN ρ + β' < Om1 := Om1_add_lt he1 (hβ'e.trans he1)
  have hξT : eN ρ + β' ∈ Tset ρ := mem_T_below hρ hρ1 (eN_add_lt_ups hρ hρ1 hβ'e) hξ1
  have hv := vt_eN hρE hρ1 hβ'e hξ1
  rw [add_assoc, hb] at hv
  obtain ⟨-, hvP⟩ := vt_mem hρE hρ1 hξT hξ1
  have hPx : ↑(Par ρ (eN ρ + β')) ⊆ Set.Iio σ := by rw [← hvP, hv]; exact hx.2
  have hc := Par_comps hρE hρ1 hξT ((lt_eN ρ).le.trans le_self_add) hξ1 (comp_eN (eN_E ρ) hβ'e)
  obtain ⟨-, hPe⟩ := hc.2 (lt_eN ρ).le
  exact ⟨heT, fun p hp => hPx (Finset.mem_coe.2 (hPe (Finset.mem_coe.1 hp)))⟩

/-- **Lemma EXACT for the atom `ω^{ε_{x+1}+β}`** (`β < σ` a constant): for countable `υ`-points `σ < ρ`
with `ε_{ρ+1} ∈ Tᵖ[σ]`, the atom is in `Tᵖ[σ]` and `π_{σ,ρ}(ω^{ε_{ρ+1}+β}) = ω^{ε_{σ+1}+β}`. -/
theorem pi_eAtom {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ)
    (heTB : eN ρ ∈ TB ρ σ) {β : Ordinal.{0}} (hβ : β < σ) :
    ω ^ (eN ρ + β) ∈ TB ρ σ ∧ pi σ ρ (ω ^ (eN ρ + β)) = ω ^ (eN σ + β) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hpe := pi_eN hσ hρ hB heTB
  obtain ⟨he1, -, -⟩ := eN_lt_upsPt hρ hρ1
  obtain ⟨hes1, -, -⟩ := eN_lt_upsPt hσ hσ1
  rcases eq_or_ne β 0 with rfl | hβ0
  · have h1 : ω ^ eN ρ = eN ρ := eN_E ρ
    have h2 : ω ^ eN σ = eN σ := eN_E σ
    rw [add_zero, add_zero, h1, h2]
    exact ⟨heTB, hpe⟩
  set β' := β - 1 with hβ'
  have hb : 1 + β' = β := Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 hβ0)
  have hβ'σ : β' < σ := lt_of_le_of_lt (sub_le_self β 1) hβ
  have hβ'TB : β' ∈ TB ρ σ := mem_TB_of_lt hB hβ'σ
  obtain ⟨hξTB, hpξ⟩ := pi_add hB heTB hβ'TB
  rw [pi_lt hB hβ'σ, hpe] at hpξ
  have hβ'ρ : β' < eN ρ := hβ'σ.trans (hB.2.2.1.trans (lt_eN ρ))
  have hξ1 : eN ρ + β' < Om1 := Om1_add_lt he1 (hβ'ρ.trans he1)
  have hv := vt_eN hB.2.1 hρ1 hβ'ρ hξ1
  rw [add_assoc, hb] at hv
  obtain ⟨hvT, hvP⟩ := vt_mem hB.2.1 hρ1 hξTB.1 hξ1
  refine ⟨by rw [← hv]; exact ⟨hvT, by rw [hvP]; exact hξTB.2⟩, ?_⟩
  have hβ'σe : β' < eN σ := hβ'σ.trans (lt_eN σ)
  have hv' := vt_eN hB.1 hσ1 hβ'σe (Om1_add_lt hes1 (hβ'σe.trans hes1))
  rw [add_assoc, hb] at hv'
  rw [← hv, pi_vt hB hξTB hξ1, hpξ, hv']

/-- `π_{σ,ρ}(ε_{ρ+1}·q) = ε_{σ+1}·q` for every `q < σ`, once `ε_{ρ+1} ∈ Tᵖ[σ]`. -/
theorem pi_eQ {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ)
    (heTB : eN ρ ∈ TB ρ σ) : ∀ q, q < σ → eN ρ * q ∈ TB ρ σ ∧ pi σ ρ (eN ρ * q) = eN σ * q := by
  intro q
  induction q using WellFoundedLT.induction with
  | ind q IH =>
  intro hq
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [mul_zero, mul_zero]
    exact ⟨mem_TB_of_lt hB hB.1.pos, pi_lt hB hB.1.pos⟩
  obtain ⟨q'', hgs, -, hq''⟩ := lg_split hq0
  have hz : lg q < σ := lt_of_le_of_lt (lg_le hq0) hq
  obtain ⟨h1, h2⟩ := IH q'' hq'' (hq''.trans hq)
  obtain ⟨h3, h4⟩ := pi_eAtom hσ hρ hB heTB hz
  rw [hgs, mul_add, mul_add, eN_mul_opow, eN_mul_opow]
  obtain ⟨h5, h6⟩ := pi_add hB h1 h3
  exact ⟨h5, by rw [h6, h2, h4]⟩

/-- The leading exponent of `ε·q + v` (`ε` an `ε`-number, `q ≠ 0`, `v < ε`) is `ε + log q`. -/
theorem log_eQt {e q v : Ordinal.{0}} (he : InE e) (hq0 : q ≠ 0) (hv : v < e) :
    log ω (e * q + v) = e + log ω q := by
  have he' : ω ^ e = e := he
  have hpos : 0 < e * q := mul_pos he.pos (pos_iff_ne_zero.2 hq0)
  have hne : e * q + v ≠ 0 := (lt_of_lt_of_le hpos le_self_add).ne'
  rw [log_eq_iff one_lt_omega0 hne]
  constructor
  · rw [opow_add, he']
    exact (mul_le_mul_right (opow_log_le_self ω hq0) e).trans le_self_add
  · rw [opow_add, opow_add, opow_one, he', mul_assoc, ← opow_succ]
    have hq1 : q + 1 ≤ ω ^ succ (log ω q) := add_one_le_of_lt (lt_opow_succ_log_self one_lt_omega0 q)
    calc e * q + v < e * q + e := (add_lt_add_iff_left _).2 hv
      _ = e * (q + 1) := by rw [mul_add_one]
      _ ≤ e * ω ^ succ (log ω q) := mul_le_mul_right hq1 e

/-- **Lemma EXACT for `ε_{x+1}·q + t`** (`0 < q < σ` a constant, `t` a term of `OT` with constants below
`σ`): if `ε_{ρ+1}·q + t(ρ) ∈ Tᵖ[σ]` then `π_{σ,ρ}(ε_{ρ+1}·q + t(ρ)) = ε_{σ+1}·q + t(σ)`. -/
theorem pi_eQt {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {q : Ordinal.{0}}
    (hq0 : q ≠ 0) (hqσ : q < σ) {t : OT} (ht : CB t σ) (hx : eN ρ * q + ev t ρ ∈ TB ρ σ) :
    pi σ ρ (eN ρ * q + ev t ρ) = eN σ * q + ev t σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  obtain ⟨he1, -, -⟩ := eN_lt_upsPt hρ hρ1
  have htρ : ev t ρ < eN ρ := ev_lt_eN (CB_mono ht hB.2.2.1.le)
  have hqρ : q < eN ρ := hqσ.trans (hB.2.2.1.trans (lt_eN ρ))
  have hq1 : q < Om1 := hqρ.trans he1
  have hm1 : eN ρ * q < Om1 := isPrincipal_mul_omega 1 he1 hq1
  have hx1 : eN ρ * q + ev t ρ < Om1 := Om1_add_lt hm1 (htρ.trans he1)
  have hle : eN ρ ≤ eN ρ * q + ev t ρ :=
    (le_mul_pos (eN ρ) (pos_iff_ne_zero.2 hq0)).trans le_self_add
  have hne : eN ρ * q + ev t ρ ≠ 0 := (lt_of_lt_of_le (eN_E ρ).pos hle).ne'
  have hlead := lead_comp hne
  rw [log_eQt (eN_E ρ) hq0 htρ] at hlead
  have hc := Par_comps hB.2.1 hρ1 hx.1 ((lt_eN ρ).le.trans hle) hx1 hlead
  have hρa : ρ ≤ ω ^ (eN ρ + log ω q) :=
    (lt_eN ρ).le.trans (le_self_add.trans (right_le_opow _ one_lt_omega0))
  obtain ⟨haT, haP⟩ := hc.2 hρa
  have haTB : ω ^ (eN ρ + log ω q) ∈ TB ρ σ :=
    ⟨haT, fun p hp => hx.2 (Finset.mem_coe.2 (haP (Finset.mem_coe.1 hp)))⟩
  have hlq : log ω q < eN ρ := lt_of_le_of_lt (log_le_self ω q) hqρ
  have heTB := eN_TB_of_atom hρ hB hlq haTB
  obtain ⟨hqTB, hpq⟩ := pi_eQ hσ hρ hB heTB q hqσ
  obtain ⟨htTB, hpt⟩ := pi_ev hB t ht
  rw [(pi_add hB hqTB htTB).2, hpq, hpt]

/-! ## Lemma IMG -/

namespace RstK

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- `ω^{ε_{ρ+1}+β} < δ` for `β < ρ`. -/
theorem atom_lt_δ {β : Ordinal.{0}} (hβ : β < ρ) : ω ^ (eN ρ + β) < δ := by
  have hδE := h.δE
  have heδ := h.eN_lt_δ
  have : eN ρ + β < δ := (inE_indec hδE).add_lt heδ ((hβ.trans (lt_eN ρ)).trans heδ)
  have h2 := (opow_lt_opow_iff_right one_lt_omega0).2 this
  have hδ' : ω ^ δ = δ := hδE
  rwa [hδ'] at h2

/-- **Lemma IMG for the atom `ω^{ε_{x+1}+β}`** (`β < ρ` a constant). -/
theorem pkg_atom : ∀ β, β < ρ → ImgPkg ρ δ (fun x => ω ^ (eN x + β)) := by
  classical
  intro β
  induction β using WellFoundedLT.induction with
  | ind β IH =>
  intro hβρ
  have hδE := h.δE
  have hδI := inE_indec hδE
  have hρe : ρ < eN ρ := lt_eN ρ
  have hvδ := h.atom_lt_δ hβρ
  have hev : eN ρ ≤ ω ^ (eN ρ + β) := le_self_add.trans (right_le_opow _ one_lt_omega0)
  have hρv : ρ < ω ^ (eN ρ + β) := hρe.trans_le hev
  rcases eq_or_ne β 0 with rfl | hβ0
  · have e : (fun x => ω ^ (eN x + 0)) = eN := funext fun x => by rw [add_zero]; exact eN_E x
    rw [e]; exact h.pkg_eN
  obtain ⟨β'', hgs, hdvd, hβ''β⟩ := lg_split hβ0
  have hzβ : lg β ≤ β := lg_le hβ0
  obtain ⟨-, -, W1, Z1, w1, m1, i1⟩ := IH β'' hβ''β (hβ''β.trans hβρ)
  have hlt'' : ω ^ (eN ρ + β'') < ω ^ (eN ρ + β) :=
    (opow_lt_opow_iff_right one_lt_omega0).2 ((add_lt_add_iff_left _).2 hβ''β)
  rcases eq_or_ne (lg β) 0 with hz0 | hz0
  · -- `β = β'' + 1`
    have hβs : β = β'' + 1 := by rw [hgs, hz0, opow_zero]
    refine ⟨one_le_iff_pos.2 (opow_pos _ omega0_pos), hvδ, insert (ω ^ (eN ρ + β)) W1, Z1,
      w1.insW hρv.le hvδ (Or.inl (indec_opow _)), by simp, ?_⟩
    intro A f hW hZ C
    have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hvA : ω ^ (eN ρ + β) ∈ A := hW (by simp)
    have h1A : ω ^ (eN ρ + β'') ∈ A := mem_A m1 hW1 hZ
    have hb : ω ^ (eN (f ρ) + β'') ≤ f (ω ^ (eN ρ + β'')) := i1 A f hW1 hZ C
    have hlt : f (ω ^ (eN ρ + β'')) < f (ω ^ (eN ρ + β)) := C.mono h1A hvA hlt''
    obtain ⟨c, hc⟩ := indec_eq_opow (C.indec _ hvA (indec_opow _))
    show ω ^ (eN (f ρ) + β) ≤ f (ω ^ (eN ρ + β))
    rw [hc] at hlt ⊢
    have h3 : eN (f ρ) + β'' < c :=
      (opow_lt_opow_iff_right one_lt_omega0).1 (lt_of_le_of_lt hb hlt)
    rw [hβs, ← add_assoc]
    exact (opow_le_opow_iff_right one_lt_omega0).2 (add_one_le_of_lt h3)
  · -- `β = β'' + ω^z`, `z > 0`: the source atom `ω^{ε+β} ≤₁ ω^{ε+β} + z`
    set z := lg β with hzdef
    set v := ω ^ (eN ρ + β) with hvdef
    have hzρ : z < ρ := lt_of_le_of_lt hzβ hβρ
    have hz0' : 0 < z := pos_iff_ne_zero.2 hz0
    have hzv : z < v := hzρ.trans hρv
    have hvzδ : v + z < δ := hδI.add_lt hvδ (hzρ.trans h.ρδ)
    have hdβ : ω ^ z ∣ β := by rw [hgs]; exact dvd_add hdvd (dvd_refl _)
    have hne : eN ρ + β ≠ 0 := (lt_of_lt_of_le (eN_E ρ).pos le_self_add).ne'
    have hdv : ω ^ z ∣ eN ρ + β :=
      dvd_add (opow_dvd_of_inE (eN_E ρ) (hzρ.trans hρe).le) hdβ
    have hsrc : le1 v (v + z) := by
      refine (h.lowδ _ _ hρv hvzδ.le).2 ?_
      exact (le1R_thm22 hz0' hzv.le).2 ⟨eN ρ + β, hne, rfl, (le_lg_iff hne z).2 hdv⟩
    have hβρ' := hβρ
    refine ⟨one_le_iff_pos.2 (opow_pos _ omega0_pos), hvδ, insert (v + z) (insert v W1),
      insert z (insert β Z1), ?_,
      Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)), ?_⟩
    · have w2 : WZ ρ δ (insert v W1) (insert z (insert β Z1)) :=
        ((w1.insZ hβρ).insZ hzρ).insW hρv.le hvδ (Or.inl (indec_opow _))
      exact w2.insW (hρv.le.trans le_self_add) hvzδ
        (Or.inr ⟨v, by simp, z, by simp, lt_add_of_pos_right _ hz0', lt_of_lt_of_le hzv le_self_add,
          rfl⟩)
    intro A f hW hZ C
    have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    have hvA : v ∈ A := hW (by simp)
    have hvzA : v + z ∈ A := hW (by simp)
    have hzA : z ∈ A := hZ (by simp)
    have hβA : β ∈ A := hZ (by simp)
    have h1A : ω ^ (eN ρ + β'') ∈ A := mem_A m1 hW1 hZ1
    have hb : ω ^ (eN (f ρ) + β'') ≤ f (ω ^ (eN ρ + β'')) := i1 A f hW1 hZ1 C
    have hlt : f (ω ^ (eN ρ + β'')) < f v := C.mono h1A hvA hlt''
    have hfz : f z = z := C.fix z hzA hzρ
    have hadd : f v + f z = f (v + z) := C.add v hvA z hzA _ hvzA rfl
    have hcov : le1 (f v) (f v + z) := by
      have := C.cov1 v hvA (v + z) hvzA hsrc
      rwa [← hadd, hfz] at this
    have hβf : β < f ρ := C.above β hβA hβρ
    have hzf : z < f ρ := C.above z hzA hzρ
    have hfρv : f ρ < f v := C.mono C.rho hvA hρv
    have heF : eN (f ρ) ≤ ω ^ (eN (f ρ) + β'') :=
      le_self_add.trans (right_le_opow _ one_lt_omega0)
    have hev' : eN (f ρ) < f v := lt_of_le_of_lt heF (lt_of_le_of_lt hb hlt)
    show ω ^ (eN (f ρ) + β) ≤ f v
    by_cases hU : UpsPt (f v)
    · have hfvE := upsPt_inE hU
      have h1 : eN (eN (f ρ)) ≤ f v := eN_le hev' hfvE
      have hEE := eN_E (eN (f ρ))
      have h2 : eN (f ρ) + β < eN (eN (f ρ)) :=
        (inE_indec hEE).add_lt (lt_eN _) ((hβf.trans (lt_eN _)).trans (lt_eN _))
      have h3 := (opow_lt_opow_iff_right one_lt_omega0).2 h2
      have hEE' : ω ^ eN (eN (f ρ)) = eN (eN (f ρ)) := hEE
      rw [hEE'] at h3
      exact (h3.trans_le h1).le
    · have hR := (C.sk (f v) (C.low v hvA) hU (f v + z)).1 hcov
      obtain ⟨a', ha'0, ha', hza'⟩ := (le1R_thm22 hz0' (hzf.trans hfρv).le).1 hR
      rw [ha'] at hlt ⊢
      have h3 : eN (f ρ) + β'' < a' :=
        (opow_lt_opow_iff_right one_lt_omega0).1 (lt_of_le_of_lt hb hlt)
      have hda : ω ^ z ∣ a' := (le_lg_iff ha'0 z).1 hza'
      have hdb : ω ^ z ∣ eN (f ρ) + β'' :=
        dvd_add (opow_dvd_of_inE (eN_E (f ρ)) (hzf.trans (lt_eN _)).le) hdvd
      have h4 := dvd_next hda hdb h3
      have e : eN (f ρ) + β = eN (f ρ) + β'' + ω ^ z := by rw [hgs, add_assoc]
      rw [e]
      exact (opow_le_opow_iff_right one_lt_omega0).2 h4

/-- **Lemma IMG for `ε_{x+1}·q`** (`0 < q < ρ` a constant). -/
theorem pkg_eQ : ∀ q, 0 < q → q < ρ → ImgPkg ρ δ (fun x => eN x * q) := by
  intro q
  induction q using WellFoundedLT.induction with
  | ind q IH =>
  intro hq0 hqρ
  obtain ⟨q'', hgs, hdvd, hq''⟩ := lg_split hq0.ne'
  have hzρ : lg q < ρ := lt_of_le_of_lt (lg_le hq0.ne') hqρ
  have e : (fun x => eN x * q) = fun x => eN x * q'' + ω ^ (eN x + lg q) := by
    funext x; rw [← eN_mul_opow, ← mul_add, ← hgs]
  rw [e]
  rcases eq_or_ne q'' 0 with h0 | h0
  · have e2 : (fun x => eN x * q'' + ω ^ (eN x + lg q)) = fun x => ω ^ (eN x + lg q) := by
      funext x; rw [h0, mul_zero, zero_add]
    rw [e2]; exact h.pkg_atom _ hzρ
  have hepos := (eN_E ρ).pos
  have hpos'' : 0 < q'' := pos_iff_ne_zero.2 h0
  have hle : ω ^ (eN ρ + lg q) ≤ eN ρ * q'' := by
    rw [← eN_mul_opow]; exact mul_le_mul_right (le_of_dvd h0 hdvd) _
  have hapos : 0 < ω ^ (eN ρ + lg q) := opow_pos _ omega0_pos
  refine ImgPkg.add (IH q'' hq'' hpos'' (hq''.trans hqρ)) (h.pkg_atom _ hzρ) (inE_indec h.δE)
    (lt_add_of_pos_right _ hapos) ?_ ?_
  · exact lt_of_lt_of_le (lt_add_of_pos_right _ hapos) (add_le_add hle le_rfl)
  · exact (lt_eN ρ).le.trans ((le_mul_pos _ hpos'').trans le_self_add)

/-- **Lemma IMG for `ε_{x+1}·q + t`** (`0 < q < ρ`, `t` a term of `OT` with `t(ρ) ≥ 1`). -/
theorem pkg_eQt {q : Ordinal.{0}} (hq0 : 0 < q) (hqρ : q < ρ) {t : OT} (ht : CB t ρ)
    (h1 : 1 ≤ ev t ρ) : ImgPkg ρ δ (fun x => eN x * q + ev t x) := by
  have htρ : ev t ρ < eN ρ := ev_lt_eN ht
  have heq : eN ρ ≤ eN ρ * q := le_mul_pos _ hq0
  exact ImgPkg.add (h.pkg_eQ q hq0 hqρ) (h.pkg_ot ht h1) (inE_indec h.δE)
    (lt_add_of_pos_right _ (lt_of_lt_of_le zero_lt_one h1))
    (lt_of_lt_of_le htρ (heq.trans le_self_add)) ((lt_eN ρ).le.trans (heq.trans le_self_add))

end RstK

/-! ## Lemma RS -/

/-- **Lemma RS with the target `ε_{x+1}·q + t`** (`0 < q < ρ` a constant, `t` a term of `OT` with
constants below `ρ`): if restarts `ρ_μ` with `ρ_μ ≤₁ δ_μ + ε_{ρ_μ+1}·q + t(ρ_μ)` lie above every `κ' < ρ`
(with `δ_μ < ρ`), then `ρ ≤₁ δ + ε_{ρ+1}·q + t(ρ) + 1`. -/
theorem rs_rstQ {r : Ordinal.{0}} (h : RstK (upsilon r) (upsilon (r + ω)) (upsilon (r + ω + 1)))
    {q : Ordinal.{0}} (hq0 : 0 < q) (hqρ : q < upsilon r) {t : OT} (ht : CB t (upsilon r))
    (htarget : ∀ κ' < upsilon r, ∃ μ, κ' < upsilon μ ∧ upsilon (μ + ω + 1) < upsilon r ∧
      RstK (upsilon μ) (upsilon (μ + ω)) (upsilon (μ + ω + 1)) ∧
      ∀ g, upsilon μ ≤ g → g ≤ upsilon (μ + ω + 1) + (eN (upsilon μ) * q + ev t (upsilon μ)) →
        le1 (upsilon μ) g) :
    le1 (upsilon r) (upsilon (r + ω + 1) + (eN (upsilon r) * q + ev t (upsilon r)) + 1) := by
  classical
  have hCt : ∀ σ, (∀ c ∈ insert q (cs t).toFinset, c < σ) → CB t σ := fun σ hσ =>
    (cb_iff t σ).2 (fun c hc => hσ c (Finset.mem_insert_of_mem (List.mem_toFinset.2 hc)))
  have hCq : ∀ σ, (∀ c ∈ insert q (cs t).toFinset, c < σ) → q < σ := fun σ hσ =>
    hσ q (Finset.mem_insert_self _ _)
  have hnx := upsilon_isNext r
  obtain ⟨-, -, hlt⟩ := eN_lt_upsPt h.ρU h.ρ1
  have hu := hlt _ hnx.1 hnx.2.1
  have hmE := upsPt_inE hnx.2.1
  have hI := indec_of_upsPt hnx.2.1
  have htρ : ev t (upsilon r) < eN (upsilon r) := ev_lt_eN ht
  refine rs_rstF (T := fun x => eN x * q + ev t x) (C := insert q (cs t).toFinset) h
    (fun c hc => by
      rcases Finset.mem_insert.1 hc with rfl | hc
      · exact hqρ
      · exact (cb_iff t _).1 ht c (List.mem_toFinset.1 hc))
    ((lt_eN _).le.trans ((le_mul_pos _ hq0).trans le_self_add))
    (hI.add_lt (mul_lt_inE hmE hu (hqρ.trans hnx.1)) (htρ.trans hu)) ?_ ?_ htarget
  · intro σ hσ hB hCσ hTB
    exact pi_eQt hσ h.ρU hB hq0.ne' (hCq σ hCσ) (hCt σ hCσ) hTB
  · intro σ hσE hσρ heσ hCσ
    have hρE := h.ρE
    exact (inE_indec hρE).add_lt (mul_lt_inE hρE heσ ((hCq σ hCσ).trans hσρ))
      ((ev_lt_eN (hCt σ hCσ)).trans heσ)

end Googology.Trans.PoR.InaccPsi.R2

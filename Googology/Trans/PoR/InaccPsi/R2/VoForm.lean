import Googology.Trans.PoR.InaccPsi.R2.VlGdRoad

/-!
# No form of an inner reach can be `δ + c` with a low additive principal `c` that is not a leaf

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

The forms of the inner reaches asked by the roads (`Ub.UbF3`, `Ub.UbForm`, `Vl.VlGdForm`) write
`r(λ+g) ∈ seg(τ)`, `τ = υ_{λ+h}`, over the single base `τ`: its parts below `τ` are sums of leaves (parameters
`p < υ_λ` and `υ`-points), and every `ϑᵗ`-value is `≥ τ` and additive principal.  So `τ + c` with `0 < c < τ`
additive principal, `c` no leaf, has no such form.

* `vo_prin_sum` (`a + b = c`, `c` additive principal: `b = 0` or `b = c`), `vo_not_indec_add`;
* `voUb_inv` (**the values of countable-argument terms `Ub.UbT`**), `voGd_inv` (**the values of the decompositions
  `Vl.VlGd`**): a value below `τ` that is additive principal is a leaf, and no value is `τ + c` with `c` as above;
* `vo_seg_eq` (the segment index of a point is unique), `vo_c_par` (`c ∈ Parᵗ(τ + c)` for `c = ω^e < τ`);
* `voForms_fail` (**at a reach `τ + c`, `τ = υ_{λ+g+ω+1}`, `c = ω^e` additive principal not an `ε`-number with
  `υ_{λ+1} ≤ c < τ`: none of `UbF3`, `UbForm`, `VlGdForm` holds**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vo

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Tv Googology.Trans.PoR.InaccPsi.R2.Ub
  Googology.Trans.PoR.InaccPsi.R2.Vl Googology.Trans.PoR.InaccPsi.R2.Uy

/-- `a + b = c` with `c` additive principal: `b = 0` or `b = c`. -/
theorem vo_prin_sum {a b c : Ordinal.{0}} (hc : Indec c) (h : a + b = c) : b = 0 ∨ b = c := by
  by_contra hne
  push Not at hne
  obtain ⟨hb0, hbc⟩ := hne
  have hbl : b < c := lt_of_le_of_ne (h ▸ (le_add_self : b ≤ a + b)) hbc
  have hal : a < c := by
    refine lt_of_le_of_ne (h ▸ le_self_add) fun hac => hb0 ?_
    have e : a + b = a + 0 := by rw [add_zero, h, hac]
    exact add_left_cancel e
  exact lt_irrefl c (h ▸ hc.add_lt hal hbl)

/-- `τ + c` with `0 < c < τ` is not additive principal. -/
theorem vo_not_indec_add {τ c : Ordinal.{0}} (hc0 : 0 < c) (hcτ : c < τ) : ¬ Indec (τ + c) := fun h =>
  lt_irrefl _ (h.add_lt (lt_add_of_pos_right τ hc0) (hcτ.trans_le le_self_add))

/-- An `ε`-number `τ` absorbs every smaller summand on the left: `a + τ = τ` for `a < τ`. -/
theorem vo_absorb {τ a : Ordinal.{0}} (hτ : InE τ) (ha : a < τ) : a + τ = τ := by
  have h1 : a < ω ^ τ := by rw [hτ]; exact ha
  exact add_of_omega0_opow_le h1 (by rw [hτ])

/-- The sum case: `a + b = τ + c` (`c` principal, `0 < c < τ`, `τ` an `ε`-number) forces `a = τ + c, b = 0`, or
`b = c`, or `b = τ + c`. -/
theorem vo_sum_cases {τ a b c : Ordinal.{0}} (hτ : InE τ) (hc : Indec c)
    (e : a + b = τ + c) : (a = τ + c ∧ b = 0) ∨ b = c ∨ b = τ + c := by
  rcases lt_or_ge a τ with haτ | hτa
  · right; right
    rcases lt_or_ge b τ with hbτ | hτb
    · exact absurd (e ▸ (inE_indec hτ).add_lt haτ hbτ) (not_lt.2 le_self_add)
    obtain ⟨c', rfl⟩ := exists_add_of_le hτb
    rw [← add_assoc, vo_absorb hτ haτ] at e
    rw [add_left_cancel e]
  · obtain ⟨c1, rfl⟩ := exists_add_of_le hτa
    rw [add_assoc] at e
    have e2 : c1 + b = c := add_left_cancel e
    rcases vo_prin_sum hc e2 with h0 | hbc
    · left; subst h0; rw [add_zero] at e2; exact ⟨by rw [e2], rfl⟩
    · right; left; exact hbc

/-- **The values of the countable-argument terms `Ub.UbT` over `τ`**: with leaves `P` that are below `τ` or additive
principal, a value below `τ` that is additive principal satisfies `P`, and no value is `τ + c` (`0 < c < τ`
additive principal, `¬ P c`). -/
theorem voUb_inv {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {P : Ordinal.{0} → Prop}
    (hP : ∀ p, P p → p < τ ∨ Indec p) :
    ∀ t : UbT, UbT.IsA t → UbT.WF τ t → UbT.Lv P t →
      (UbT.ev τ t < τ → Indec (UbT.ev τ t) → P (UbT.ev τ t)) ∧
        ∀ c, 0 < c → c < τ → Indec c → ¬ P c → UbT.ev τ t ≠ τ + c := by
  intro t
  induction t with
  | par p =>
    intro _ _ hl
    refine ⟨fun _ _ => hl, fun c hc0 hcτ _ _ e => ?_⟩
    rcases hP p hl with hp | hp
    · exact absurd ((show p = τ + c from e) ▸ hp) (not_lt.2 le_self_add)
    · exact vo_not_indec_add hc0 hcτ ((show p = τ + c from e) ▸ hp)
  | add s t ihs iht =>
    intro hA hW hl
    have Is := ihs hA.1 hW.1 hl.1
    have It := iht hA.2 hW.2 hl.2
    refine ⟨fun hy hI => ?_, fun c hc0 hcτ hcI hPc e => ?_⟩
    · rcases vo_prin_sum hI (rfl : UbT.ev τ s + UbT.ev τ t = _) with h0 | hb
      · have e : UbT.ev τ (UbT.add s t) = UbT.ev τ s := by
          show UbT.ev τ s + UbT.ev τ t = _; rw [h0, add_zero]
        rw [e] at hy hI ⊢; exact Is.1 hy hI
      · have e : UbT.ev τ (UbT.add s t) = UbT.ev τ t := hb.symm
        rw [e] at hy hI ⊢; exact It.1 hy hI
    · rcases vo_sum_cases hτ hcI e with ⟨ha, -⟩ | hb | hb
      · exact Is.2 c hc0 hcτ hcI hPc ha
      · exact hPc (hb ▸ It.1 (hb ▸ hcτ) (hb ▸ hcI))
      · exact It.2 c hc0 hcτ hcI hPc hb
  | base =>
    intro _ _ _
    refine ⟨fun h => absurd h (lt_irrefl _), fun c hc0 _ _ _ e => ?_⟩
    have e' : τ + 0 = τ + c := by rw [add_zero]; exact e
    exact hc0.ne (add_left_cancel e')
  | th1 s _ =>
    intro _ hW _
    have hs : UbT.ev τ s < Om1 := hW.2
    have hv : UbT.ev τ (UbT.th1 s) = wbar (τ + UbT.ev τ s) := vt_wbar hτ hτ1 hs
    have hmem : wbar (τ + UbT.ev τ s) ∈ NonEAP := enumOrd_mem nonEAP_unbounded _
    have hge : τ ≤ UbT.ev τ (UbT.th1 s) := hv ▸ (le_self_add.trans (le_enumOrd_self nonEAP_unbounded))
    refine ⟨fun h => absurd h (not_lt.2 hge), fun c hc0 hcτ _ _ e => ?_⟩
    exact vo_not_indec_add hc0 hcτ (e ▸ hv ▸ hmem.1)
  | th s _ => intro hA; exact absurd hA id
  | om s _ => intro hA; exact absurd hA id

/-- **The values of the decompositions `Vl.VlGd κ τ P`**: in `Tᵗ`, a value below `τ` that is additive principal
satisfies `P`, and no value is `τ + c` (`0 < c < τ` additive principal, `¬ P c`). -/
theorem voGd_inv {κ τ : Ordinal.{0}} (hB : Bases κ τ) {P : Ordinal.{0} → Prop} {y : Ordinal.{0}}
    (h : VlGd κ τ P y) :
    y ∈ Tset τ ∧ (y < τ → Indec y → P y) ∧ ∀ c, 0 < c → c < τ → Indec c → ¬ P c → y ≠ τ + c := by
  have hτ := hB.2.1
  have hτ1 := hB.2.2.2
  have hvt : ∀ ξ, ξ ∈ Tset τ → ξ < OmTwo →
      vt τ ξ ∈ Tset τ ∧ (vt τ ξ < τ → Indec (vt τ ξ) → P (vt τ ξ)) ∧
        ∀ c, 0 < c → c < τ → Indec c → ¬ P c → vt τ ξ ≠ τ + c := by
    intro ξ hξ hξ2
    obtain ⟨hm, hge, -, hI, -⟩ := vt_memTwo hτ hτ1 hξ hξ2
    exact ⟨hm, fun h => absurd h (not_lt.2 hge), fun c hc0 hcτ _ _ e => vo_not_indec_add hc0 hcτ (e ▸ hI)⟩
  induction h with
  | @par p hp hP =>
    exact ⟨Uh.uh_T_le hτ hτ1 hp.le, fun _ _ => hP,
      fun c _ _ _ _ e => absurd (e ▸ hp) (not_lt.2 le_self_add)⟩
  | base =>
    refine ⟨Uh.uh_T_le hτ hτ1 le_rfl, fun h => absurd h (lt_irrefl _), fun c hc0 _ _ _ e => ?_⟩
    have e' : τ + 0 = τ + c := by rw [add_zero]; exact e
    exact hc0.ne (add_left_cancel e')
  | @add a b _ _ _ iha ihb =>
    refine ⟨vzT_add hτ hτ1 iha.1 ihb.1, fun hy hI => ?_, fun c hc0 hcτ hcI hPc e => ?_⟩
    · rcases vo_prin_sum hI (rfl : a + b = _) with h0 | hb
      · subst h0; rw [add_zero] at hy hI ⊢; exact iha.2.1 hy hI
      · rw [← hb] at hy hI ⊢; exact ihb.2.1 hy hI
    · rcases vo_sum_cases hτ hcI e with ⟨ha, -⟩ | hb | hb
      · exact iha.2.2 c hc0 hcτ hcI hPc ha
      · exact hPc (hb ▸ ihb.2.1 (hb ▸ hcτ) (hb ▸ hcI))
      · exact ihb.2.2 c hc0 hcτ hcI hPc hb
  | @th1 s hs _ ih =>
    have h1 : (1 : Ordinal.{0}) ∈ Tset τ :=
      Uh.uh_T_le hτ hτ1 (Order.one_le_iff_pos.2 (InE.pos hτ))
    have h1O : (1 : Ordinal.{0}) < Om1 :=
      lt_of_lt_of_le one_lt_omega0 (calc ω ≤ ω ^ Om1 := left_le_opow ω Rj.rj_Om1_pos
        _ = Om1 := Rj.rj_Om1_inE)
    have h1s : 1 + s < Om1 := (inE_indec Rj.rj_Om1_inE).add_lt h1O hs
    exact hvt _ (vzT_add hτ hτ1 h1 ih.1) (h1s.trans Uc.uc_Om1_lt_Om2)
  | @thc q r hq hr _ ih =>
    obtain ⟨hm, hlt⟩ := uy_arg_T hB hq ih.1 hr
    exact hvt _ hm hlt
  | @thz q r _ hz hr _ _ _ _ =>
    exact hvt _ hz.mem ((Lq.lq_SC_indec Uc.uc_SC_Om2).add_lt (hz.qB.trans Uc.ucB_lt_Om2)
      (hr.trans Uc.uc_Om1_lt_Om2))
  | @thg M r _ hME _ _ hmem hr _ _ _ => exact hvt _ hmem (Uk.arg_lt2 hME hr)
  | @thl M r _ hME _ hmem hr _ _ _ => exact hvt _ hmem (Uk.arg_lt2 hME hr)

/-- **The segment index of a point is unique**: `υ_x ≤ r < υ_{x+1}` and `υ_y ≤ r < υ_{succ y}` give `x = y`. -/
theorem vo_seg_eq {x y r : Ordinal.{0}} (h1 : upsilon x ≤ r) (h2 : r < upsilon (succ x))
    (h3 : upsilon y ≤ r) (h4 : r < upsilon (succ y)) : x = y := by
  have hm := upsilon_normal.strictMono
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · exact absurd (h2.trans_le (hm.monotone (succ_le_of_lt hxy))) (not_lt.2 h3)
  · rfl
  · exact absurd (h4.trans_le (hm.monotone (succ_le_of_lt hyx))) (not_lt.2 h1)

/-- `c ∈ Parᵗ(τ + c)` for `c = ω^e < τ` (`τ` a countable `ε`-number; [W07a] Def 3.28 through `R2.Par_comps`). -/
theorem vo_c_par {τ e : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hcτ : ω ^ e < τ) :
    ω ^ e ∈ Par τ (τ + ω ^ e) := by
  have hT : τ + ω ^ e ∈ Tset τ := vzT_add hτ hτ1 (Uh.uh_T_le hτ hτ1 le_rfl) (Uh.uh_T_le hτ hτ1 hcτ.le)
  have hx1 : τ + ω ^ e < Om1 :=
    (inE_indec Rj.rj_Om1_inE).add_lt hτ1 (hcτ.trans hτ1)
  have hdvd : ω ^ τ ∣ τ := by rw [hτ]
  have hlt : ω ^ e < ω ^ τ := by rw [hτ]; exact hcτ
  have hc : ω ^ e ∈ comps (τ + ω ^ e) :=
    Rj.rj_comps_add τ hdvd _ hlt _ (by rw [comps_opow]; exact List.mem_singleton_self _)
  exact (Par_comps hτ hτ1 hT le_self_add hx1 hc).1 hcτ

variable {S : InaccSeq.{0}}

/-- **The segment of the reach `τ + c`**: `r = υ_X + c` with `c < υ_X` lies in `[υ_X, υ_{succ X})`, so every
`h` with `υ_{λ+h} ≤ r < υ_{succ(λ+h)}` has `λ + h = X`. -/
theorem vo_segX {l X r c : Ordinal.{0}} (hX0 : 0 < X) (hr : r = upsilon X + c) (hcτ : c < upsilon X) :
    ∀ h, upsilon (l + h) ≤ r → r < upsilon (succ (l + h)) → l + h = X := by
  have hm := upsilon_normal.strictMono
  have hrX : upsilon X ≤ r := hr ▸ le_self_add
  have hrX1 : r < upsilon (succ X) := by
    rw [hr]
    have hE1 : InE (upsilon (succ X)) := upsPt_inE (upsPt_upsilon (hX0.trans (lt_succ X)))
    have hτs : upsilon X < upsilon (succ X) := hm (lt_succ X)
    exact hE1.add_lt hτs (hcτ.trans hτs)
  exact fun h h1 h2 => vo_seg_eq h1 h2 hrX hrX1

/-- **`c` is no leaf**: `c ≥ υ_{λ+1}` is not below `υ_λ`, and `c` (not an `ε`-number) is no `υ`-point. -/
theorem vo_notLeaf {l c : Ordinal.{0}} (hl0 : 0 < l) (hcN : c ∈ NonEAP) (hc1 : upsilon (succ l) ≤ c)
    (Q : Ordinal.{0} → Prop) (hQ : ∀ p, Q p → p < upsilon l ∨ ∃ h', p = upsilon (l + h')) : ¬ Q c := by
  have hlτ : upsilon l < upsilon (succ l) := upsilon_normal.strictMono (lt_succ l)
  intro hq
  rcases hQ c hq with h | ⟨h', e'⟩
  · exact absurd (h.trans hlτ) (not_lt.2 hc1)
  · exact hcN.2 (e' ▸ upsPt_inE (upsPt_upsilon (hl0.trans_le le_self_add)))

/-- **No form at the reach `τ + c`**: if `r(λ+g) = τ + c` with `τ = υ_{λ+(g+ω+1)} < Ω₁`, `c = ω^e` additive
principal and not an `ε`-number, `υ_{λ+1} ≤ c < τ`, and `g + ω + 2 ≤ β`, then none of `Ub.UbF3`, `Ub.UbForm`,
`Vl.VlGdForm` holds at `g`. -/
theorem voForms_fail {l β g e : Ordinal.{0}} (hl0 : 0 < l)
    (hr : cdR S (l + g) = upsilon (l + (g + ω + 1)) + ω ^ e)
    (hcN : ω ^ e ∈ NonEAP) (hc1 : upsilon (succ l) ≤ ω ^ e) (hcτ : ω ^ e < upsilon (l + (g + ω + 1)))
    (hτ1 : upsilon (l + (g + ω + 1)) < Om1) (hβ : g + ω + 2 ≤ β) :
    ¬ UbF3 S l β g ∧ ¬ UbForm S l β g ∧ ¬ VlGdForm S l β g := by
  have hm := upsilon_normal.strictMono
  set X := l + (g + ω + 1) with hX
  set τ := upsilon X with hτdef
  set c := ω ^ e with hcdef
  have hX0 : 0 < X := hl0.trans_le le_self_add
  have hτE : InE τ := upsPt_inE (upsPt_upsilon hX0)
  have hlτ : upsilon l < upsilon (succ l) := hm (lt_succ l)
  have hc0 : 0 < c := lt_of_le_of_lt zero_le (hlτ.trans_le hc1)
  have hcI : Indec c := hcN.1
  have hrX : upsilon X ≤ cdR S (l + g) := hr ▸ le_self_add
  have hrX1 : cdR S (l + g) < upsilon (succ X) := by
    rw [hr]
    have hE1 : InE (upsilon (succ X)) := upsPt_inE (upsPt_upsilon (hX0.trans (lt_succ X)))
    have hτs : τ < upsilon (succ X) := hm (lt_succ X)
    exact hE1.add_lt hτs (hcτ.trans hτs)
  have hseg : ∀ h, upsilon (l + h) ≤ cdR S (l + g) → cdR S (l + g) < upsilon (succ (l + h)) → l + h = X :=
    fun h h1 h2 => vo_seg_eq h1 h2 hrX hrX1
  -- the leaves of the forms: below `υ_λ` or `υ`-points
  have hPc : ∀ (Q : Ordinal.{0} → Prop), (∀ p, Q p → p < upsilon l ∨ ∃ h', p = upsilon (l + h')) → ¬ Q c := by
    intro Q hQ hq
    rcases hQ c hq with h | ⟨h', e'⟩
    · exact absurd (h.trans hlτ) (not_lt.2 hc1)
    · have hpos : 0 < l + h' := hl0.trans_le le_self_add
      exact hcN.2 (e' ▸ upsPt_inE (upsPt_upsilon hpos))
  refine ⟨fun hF => ?_, fun hF => ?_, fun hF => ?_⟩
  · rcases hF with h1 | ⟨h, c', h0, hhβ, hc', e'⟩ | ⟨h, h0, hhβ, hlow⟩
    · have hle : upsilon (succ X) ≤ upsilon (l + β) := by
        refine hm.monotone ?_
        rw [hX, succ_eq_add_one, add_assoc, add_assoc]
        refine (add_le_add_iff_left l).2 ?_
        rw [one_add_one_eq_two]; exact hβ
      exact absurd (h1.trans_lt hrX1) (not_lt.2 hle)
    · have hlh : succ l ≤ succ (l + h) := succ_le_succ (le_self_add)
      have hτh : upsilon (l + h) < upsilon (succ (l + h)) := hm (lt_succ _)
      have hE : InE (upsilon (succ (l + h))) :=
        upsPt_inE (upsPt_upsilon (lt_of_le_of_lt zero_le (lt_succ _)))
      have h2 : cdR S (l + g) < upsilon (succ (l + h)) := by
        rw [e']; exact hE.add_lt hτh (hc'.trans_le (hm.monotone hlh))
      have hXe := hseg h (e' ▸ le_self_add) h2
      rw [hXe, hr] at e'
      have := add_left_cancel e'
      exact absurd (this ▸ hc') (not_lt.2 hc1)
    · have hXe := hseg h hlow.1 hlow.2.1
      have hpar := hlow.2.2
      rw [hXe, hr] at hpar
      have := hpar c (vo_c_par hτE hτ1 hcτ)
      exact absurd (this.trans hlτ) (not_lt.2 hc1)
  · obtain ⟨h, t, -, -, hA, hW, hL, h1, h2, hev⟩ := hF
    have hXe := hseg h h1 h2
    rw [hXe] at hW hev
    rw [hr] at hev
    have hP : ∀ p, (fun p => p < upsilon l ∨ ∃ h', h' < β ∧ p = upsilon (l + h')) p → p < τ ∨ Indec p := by
      rintro p (hp | ⟨h', -, rfl⟩)
      · left; exact hp.trans (hlτ.trans_le hc1 |>.trans hcτ)
      · right
        exact inE_indec (upsPt_inE (upsPt_upsilon (hl0.trans_le le_self_add)))
    exact (voUb_inv hτE hτ1 hP t hA hW hL).2 c hc0 hcτ hcI
      (hPc _ fun p (hp : p < upsilon l ∨ ∃ h', h' < β ∧ p = upsilon (l + h')) =>
        hp.imp id fun ⟨h', _, e'⟩ => ⟨h', e'⟩) hev
  · obtain ⟨h, -, -, hO, h1, h2, hgd⟩ := hF
    have hXe := hseg h h1 h2
    rw [hXe, hr] at hgd
    have hB : Bases (upsilon l) τ :=
      ⟨upsPt_inE (upsPt_upsilon hl0), hτE, hlτ.trans_le hc1 |>.trans hcτ, hτ1⟩
    exact (voGd_inv hB hgd).2.2 c hc0 hcτ hcI
      (hPc _ fun p (hp : p < upsilon l ∨ ∃ h', h' ≤ h ∧ p = upsilon (l + h')) =>
        hp.imp id fun ⟨h', _, e'⟩ => ⟨h', e'⟩) rfl

end Googology.Trans.PoR.InaccPsi.R2.Vo

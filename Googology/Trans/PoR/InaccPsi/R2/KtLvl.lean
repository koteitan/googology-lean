import Googology.Trans.PoR.InaccPsi.R2.KtGap

/-!
# Kt: THE VEBLEN LEVEL OF A MEMBER, and the gap of `b + φ(L(x), 0)`

`φ = veblen`.  A member `x < φ(α, 0)` (`α > 0`) of a closure lies below `φ(α' + 1, 0)` for a member `α' < α` (its
Veblen level): by induction on the member (`φ(·, 0)` is normal, `Ordinal.isNormal_veblen_zero`).

* `ktLvlPre` (`x < φ(α, 0)` ⇒ `x < φ(γ + 1, 0)` for some `γ < α`), `ktLvl` (**the level of a member of
  `Cl(a, b)`**), `ktLvlH` (the same for `HCl`), `KtLvl` (the level property of a set);
* `ktG_phiL0` (**the gap passes to `b + φ(L(x), 0)`**).

No new axiom.  New definition: `KtLvl`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kt

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Kg

variable {S : InaccSeq.{0}}

/-- **The level property** of a set: a member `x < φ(α, 0)`, `α > 0`, lies below `φ(α' + 1, 0)` for a member
`α' < α`. -/
def KtLvl (C : Set Ordinal.{0}) : Prop :=
  ∀ x ∈ C, ∀ α, 0 < α → x < veblen α 0 → ∃ α' ∈ C, α' < α ∧ x < veblen (α' + 1) 0

/-- `x < φ(α, 0)` gives `x < φ(γ + 1, 0)` for some `γ < α`. -/
theorem ktLvlPre {x α : Ordinal.{0}} (hα : 0 < α) (hx : x < veblen α 0) :
    ∃ γ, γ < α ∧ x < veblen (γ + 1) 0 := by
  rcases zero_or_succ_or_isSuccLimit α with h0 | ⟨γ, hγ⟩ | hlim
  · exact absurd h0 hα.ne'
  · rw [succ_eq_add_one] at hγ
    subst hγ
    exact ⟨γ, lt_add_one γ, hx⟩
  · obtain ⟨γ, hγ, hxγ⟩ := (isNormal_veblen_zero.lt_iff_exists_lt hlim).1 hx
    exact ⟨γ, hγ, hxγ.trans_le (veblen_zero_strictMono.monotone (le_of_lt (lt_add_one γ)))⟩

/-- An SC member `z < φ(α, 0)` is its own level. -/
theorem ktLvlSC {z α : Ordinal.{0}} (hz : SC z) (hzα : z < veblen α 0) : z < α ∧ z < veblen (z + 1) 0 := by
  have h1 : veblen z 0 < veblen α 0 := by rwa [hz.veblen_zero]
  refine ⟨veblen_zero_lt_veblen_zero.1 h1, ?_⟩
  calc z = veblen z 0 := hz.veblen_zero.symm
    _ < veblen (z + 1) 0 := veblen_zero_lt_veblen_zero.2 (lt_add_one z)

theorem ktOne_lt : (1 : Ordinal.{0}) < veblen 1 0 := by
  calc (1 : Ordinal.{0}) = veblen 0 0 := by rw [veblen_zero_apply, opow_zero]
    _ < veblen 1 0 := veblen_zero_lt_veblen_zero.2 zero_lt_one

/-- The sum and the `φ`-node steps of the level. -/
theorem ktLvl_add {P : Ordinal.{0} → Prop} {x y α : Ordinal.{0}}
    (hx : ∃ α' , P α' ∧ α' < α ∧ x < veblen (α' + 1) 0) (hy : ∃ α', P α' ∧ α' < α ∧ y < veblen (α' + 1) 0) :
    ∃ α', P α' ∧ α' < α ∧ x + y < veblen (α' + 1) 0 := by
  obtain ⟨a1, h1, h1α, hx1⟩ := hx
  obtain ⟨a2, h2, h2α, hy2⟩ := hy
  rcases le_total a1 a2 with h | h
  · refine ⟨a2, h2, h2α, Ph.ph_veblen_prin _ 0 (hx1.trans_le ?_) hy2⟩
    exact veblen_zero_strictMono.monotone (add_le_add h le_rfl)
  · refine ⟨a1, h1, h1α, Ph.ph_veblen_prin _ 0 hx1 (hy2.trans_le ?_)⟩
    exact veblen_zero_strictMono.monotone (add_le_add h le_rfl)

theorem ktLvl_phi {P : Ordinal.{0} → Prop} {p q α : Ordinal.{0}} (hp : P p) (hpq : veblen p q < veblen α 0)
    (hq : ∃ α', P α' ∧ α' < α ∧ q < veblen (α' + 1) 0) :
    ∃ α', P α' ∧ α' < α ∧ veblen p q < veblen (α' + 1) 0 := by
  obtain ⟨a1, h1, h1α, hq1⟩ := hq
  have hpα : p < α := by
    by_contra hc
    push Not at hc
    have : veblen α 0 ≤ veblen p q :=
      (veblen_left_monotone 0 hc).trans ((veblen_le_veblen_iff_right).2 zero_le)
    exact absurd hpq (not_lt.2 this)
  have key : ∀ a, p < a + 1 → q < veblen (a + 1) 0 → veblen p q < veblen (a + 1) 0 := fun a hpa hqa => by
    calc veblen p q < veblen p (veblen (a + 1) 0) := (veblen_lt_veblen_iff_right).2 hqa
      _ = veblen (a + 1) 0 := veblen_veblen_of_lt hpa 0
  rcases le_total p a1 with h | h
  · exact ⟨a1, h1, h1α, key a1 (h.trans_lt (lt_add_one a1)) hq1⟩
  · refine ⟨p, hp, hpα, key p (lt_add_one p) (hq1.trans_le ?_)⟩
    exact veblen_zero_strictMono.monotone (add_le_add h le_rfl)

/-- **The level of a member of `Cl(a, b)`.** -/
theorem ktLvl {A B : Ordinal.{0}} : KtLvl (S.CSet A B) := by
  intro x hx
  induction hx with
  | @small x hx =>
    intro α hα hxα
    obtain ⟨γ, hγα, hxγ⟩ := ktLvlPre hα hxα
    rcases le_total x γ with h | h
    · refine ⟨x, CSet.of_lt hx, h.trans_lt hγα, ?_⟩
      exact (left_le_veblen (x + 1) 0).trans_lt' (lt_add_one x)
    · exact ⟨γ, CSet.of_lt (h.trans_lt hx), hγα, hxγ⟩
  | zero => intro α hα _; exact ⟨0, CSet.zero_mem _ _, hα, veblen_pos⟩
  | inacc n =>
    intro α _ hxα
    obtain ⟨h1, h2⟩ := ktLvlSC (SC_I (S := S) n) hxα
    exact ⟨_, Clos.inacc n, h1, h2⟩
  | inaccW =>
    intro α _ hxα
    obtain ⟨h1, h2⟩ := ktLvlSC (SC_Iw (S := S)) hxα
    exact ⟨_, Clos.inaccW, h1, h2⟩
  | @add x y _ _ ihx ihy =>
    intro α hα hxα
    have hx' : x < veblen α 0 := (le_self_add).trans_lt hxα
    have hy' : y < veblen α 0 := (le_add_self).trans_lt hxα
    obtain ⟨a1, h1, h1α, hx1⟩ := ihx α hα hx'
    obtain ⟨a2, h2, h2α, hy2⟩ := ihy α hα hy'
    obtain ⟨a', ha', ha'α, h⟩ := ktLvl_add (P := (· ∈ S.CSet A B)) ⟨a1, h1, h1α, hx1⟩ ⟨a2, h2, h2α, hy2⟩
    exact ⟨a', ha', ha'α, h⟩
  | @phi p q hp _ _ ihq =>
    intro α hα hxα
    have hq' : q < veblen α 0 := (right_le_veblen p q).trans_lt hxα
    obtain ⟨a1, h1, h1α, hq1⟩ := ihq α hα hq'
    obtain ⟨a', ha', ha'α, h⟩ := ktLvl_phi (P := (· ∈ S.CSet A B)) hp hxα ⟨a1, h1, h1α, hq1⟩
    exact ⟨a', ha', ha'α, h⟩
  | @om x hx _ =>
    intro α hα hxα
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero] at hxα ⊢
      exact ⟨0, CSet.zero_mem _ _, hα, veblen_pos⟩
    · obtain ⟨h1, h2⟩ := ktLvlSC (SC_Om hx0) hxα
      exact ⟨_, Clos.om hx, h1, h2⟩
  | @coll π e hπ hπC heC _ _ =>
    intro α _ hxα
    obtain ⟨h1, h2⟩ := ktLvlSC (SC_psi hπ e.1) hxα
    exact ⟨_, Clos.coll hπ hπC heC, h1, h2⟩

/-- **The level of a member of `HCl(a, Z)`.** -/
theorem ktLvlH {a Z : Ordinal.{0}} : KtLvl {x | HCl S a Z x} := by
  intro x hx
  induction hx with
  | @small x hx =>
    intro α hα hxα
    obtain ⟨γ, hγα, hxγ⟩ := ktLvlPre hα hxα
    rcases le_total x γ with h | h
    · refine ⟨x, HCl.small hx, h.trans_lt hγα, ?_⟩
      exact (left_le_veblen (x + 1) 0).trans_lt' (lt_add_one x)
    · exact ⟨γ, HCl.small (h.trans_lt hx), hγα, hxγ⟩
  | zero => intro α hα _; exact ⟨0, HCl.zero, hα, veblen_pos⟩
  | inacc n =>
    intro α _ hxα
    obtain ⟨h1, h2⟩ := ktLvlSC (SC_I (S := S) n) hxα
    exact ⟨_, HCl.inacc n, h1, h2⟩
  | inaccW =>
    intro α _ hxα
    obtain ⟨h1, h2⟩ := ktLvlSC (SC_Iw (S := S)) hxα
    exact ⟨_, HCl.inaccW, h1, h2⟩
  | @add x y _ _ ihx ihy =>
    intro α hα hxα
    have hx' : x < veblen α 0 := (le_self_add).trans_lt hxα
    have hy' : y < veblen α 0 := (le_add_self).trans_lt hxα
    obtain ⟨a1, h1, h1α, hx1⟩ := ihx α hα hx'
    obtain ⟨a2, h2, h2α, hy2⟩ := ihy α hα hy'
    obtain ⟨a', ha', ha'α, h⟩ := ktLvl_add (P := fun y => HCl S a Z y) ⟨a1, h1, h1α, hx1⟩ ⟨a2, h2, h2α, hy2⟩
    exact ⟨a', ha', ha'α, h⟩
  | @phi p q hp _ _ ihq =>
    intro α hα hxα
    have hq' : q < veblen α 0 := (right_le_veblen p q).trans_lt hxα
    obtain ⟨a1, h1, h1α, hq1⟩ := ihq α hα hq'
    obtain ⟨a', ha', ha'α, h⟩ := ktLvl_phi (P := fun y => HCl S a Z y) hp hxα ⟨a1, h1, h1α, hq1⟩
    exact ⟨a', ha', ha'α, h⟩
  | @om x hx _ =>
    intro α hα hxα
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero] at hxα ⊢
      exact ⟨0, HCl.zero, hα, veblen_pos⟩
    · obtain ⟨h1, h2⟩ := ktLvlSC (SC_Om hx0) hxα
      exact ⟨_, HCl.om hx, h1, h2⟩
  | @coll π e hπ hπ1 hπC heC he _ _ =>
    intro α _ hxα
    obtain ⟨h1, h2⟩ := ktLvlSC (SC_psi hπ e) hxα
    exact ⟨_, HCl.coll hπ hπ1 hπC heC he, h1, h2⟩

/-- **The gap passes to `b + φ(L(x), 0)`.** -/
theorem ktG_phiL0 {C : Set Ordinal.{0}} {κ z : Ordinal.{0}} (hC : KtCl C κ z) (hlv : KtLvl C) {b : Ordinal.{0}}
    {L : Ordinal.{0} → Ordinal.{0}} (hg : KgGap κ L C z) : KgGap κ (fun x => b + veblen (L x) 0) C z := by
  intro e he hlt
  rcases lt_or_ge e b with h1 | h1
  · exact ⟨0, hC.zSC.1, h1.trans_le le_self_add⟩
  · have hd : e - b < veblen (L κ) 0 := Ry.rySub_lt h1 hlt
    have hdC : e - b ∈ C := hC.sub e he b
    have e1 : e = b + (e - b) := (Ordinal.add_sub_cancel_of_le h1).symm
    rcases eq_or_ne (L κ) 0 with h0 | h0
    · -- `φ(0, 0) = 1`: `e - b = 0`
      have hd0 : e - b = 0 := by
        rw [h0, veblen_zero_apply, opow_zero] at hd; exact Order.lt_one_iff.1 hd
      refine ⟨0, hC.zSC.1, ?_⟩
      show e < b + veblen (L (0 + 1)) 0
      rw [e1, hd0, add_zero]; exact lt_add_of_pos_right b veblen_pos
    · obtain ⟨α', hα'C, hα'L, hdα'⟩ := hlv _ hdC (L κ) (pos_iff_ne_zero.2 h0) hd
      obtain ⟨q, hq, hqα⟩ := hg α' hα'C hα'L
      refine ⟨q, hq, ?_⟩
      show e < b + veblen (L (q + 1)) 0
      rw [e1]
      exact (add_lt_add_iff_left b).2 (hdα'.trans_le (veblen_zero_strictMono.monotone
        (Order.add_one_le_of_lt hqα)))

end Googology.Trans.PoR.InaccPsi.R2.Kt

#print axioms Googology.Trans.PoR.InaccPsi.R2.Kt.ktLvl
#print axioms Googology.Trans.PoR.InaccPsi.R2.Kt.ktG_phiL0

import Googology.Trans.PoR.InaccPsi.R2.KuSucc

/-!
# Kw: THE FIRST USE OF THE LAST EXPONENT (the truncations `β + W^E·c` of a normal `β + W^E·γ` are normal)

`Cl(a, z) = S.CSet a z`.  `KwC a z d` is `Cl(a, z)` cut by the nesting depth `d` of the collapses: the collapses
`ψ_π(e)` at depth `d + 1` take arguments of depth `d`.  Differences, logarithms and the division by `ω^p` keep the
depth, so the exponent `E` of a member `y ∈ [β + W^E, β + W^{E+1})` (`W^{E+1} ∣ β`) is a member of the same depth.

THE FIRST USE: let `b = β + W^E·γ` (`0 < γ < Ω₂`) be normal and `a₁ = β + W^E`, `s = ψ₂(a₁)`.  Every member of
`Cl(b, s)` of depth `d` lies in `Cl(a₁, s)` or `E` has a smaller depth (a collapse `ψ_π(e)` with `e ≥ a₁` gives `E` at
the depth of `e`).  If `E ∉ Cl(b, s)`, then `Cl(b, s) ⊆ Cl(a₁, s)`, so `ψ₂ b ≤ s` and `E ∈ Cl(b, ψ₂ b) ⊆ Cl(b, s)`;
so `E ∈ Cl(b, s)`, and at its least depth `E ∈ Cl(a₁, ψ₂ a₁)`.  No hypothesis on `E`.

* `KwC`, `kwC_CSet`, `CSet_kwC`, `kwC_lift`;
* `kwC_lead_tail`, `kwC_log`, `kwC_sub`, `kwC_rem`, `kwC_div` (the closure facts at one depth);
* `kwExt` (**the exponent of a member of `[β + W^E, β + W^{E+1})` at the same depth**), `kwStar`;
* `kwFU` (**THE FIRST USE**: `E ∈ Cl(β + W^E, ψ₂(β + W^E))`), `kwTrunc` (**`β + W^E·c` is normal** for every owned
  `c ≥ 1`).

No new axiom.  New definition: `KwC`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Kh
  Googology.Trans.PoR.InaccPsi.R2.Kj

variable {S : InaccSeq.{0}}

/-- **`Cl(a, z)` cut by the nesting depth of the collapses.** -/
inductive KwC (S : InaccSeq.{0}) (a z : Ordinal.{0}) : ℕ → Ordinal.{0} → Prop
  | small {d : ℕ} {x : Ordinal.{0}} : x < z → KwC S a z d x
  | zero {d : ℕ} : KwC S a z d 0
  | inacc {d : ℕ} (n : ℕ) : KwC S a z d (S.I n)
  | inaccW {d : ℕ} : KwC S a z d S.Iw
  | add {d : ℕ} {x y : Ordinal.{0}} : KwC S a z d x → KwC S a z d y → KwC S a z d (x + y)
  | phi {d : ℕ} {x y : Ordinal.{0}} : KwC S a z d x → KwC S a z d y → KwC S a z d (veblen x y)
  | om {d : ℕ} {x : Ordinal.{0}} : KwC S a z d x → KwC S a z d (Om x)
  | coll {d : ℕ} {π e : Ordinal.{0}} : S.InR π → KwC S a z d π → KwC S a z d e → e < a →
      KwC S a z (d + 1) (S.psi e π)
  | up {d : ℕ} {x : Ordinal.{0}} : KwC S a z d x → KwC S a z (d + 1) x

variable {a z : Ordinal.{0}}

theorem kwC_CSet {d : ℕ} {x : Ordinal.{0}} (h : KwC S a z d x) : x ∈ S.CSet a z := by
  induction h with
  | small h => exact CSet.of_lt h
  | zero => exact CSet.zero_mem _ _
  | inacc n => exact CSet.I_mem _ _ n
  | inaccW => exact CSet.Iw_mem _ _
  | add _ _ ihx ihy => exact CSet.add_mem ihx ihy
  | phi _ _ ihx ihy => exact CSet.phi_mem ihx ihy
  | om _ ih => exact CSet.Om_mem ih
  | coll hπ _ _ he ihπ ihe => exact CSet.psi_mem he hπ ihπ ihe
  | up _ ih => exact ih

theorem kwC_lift {d d' : ℕ} (h : d ≤ d') {x : Ordinal.{0}} (hx : KwC S a z d x) : KwC S a z d' x := by
  induction h with
  | refl => exact hx
  | step _ ih => exact KwC.up ih

theorem CSet_kwC {x : Ordinal.{0}} (h : x ∈ S.CSet a z) : ∃ d, KwC S a z d x := by
  induction h with
  | small h => exact ⟨0, KwC.small h⟩
  | zero => exact ⟨0, KwC.zero⟩
  | inacc n => exact ⟨0, KwC.inacc n⟩
  | inaccW => exact ⟨0, KwC.inaccW⟩
  | add _ _ ihx ihy =>
    obtain ⟨m, hm⟩ := ihx
    obtain ⟨k, hk⟩ := ihy
    exact ⟨max m k, KwC.add (kwC_lift (le_max_left m k) hm) (kwC_lift (le_max_right m k) hk)⟩
  | phi _ _ ihx ihy =>
    obtain ⟨m, hm⟩ := ihx
    obtain ⟨k, hk⟩ := ihy
    exact ⟨max m k, KwC.phi (kwC_lift (le_max_left m k) hm) (kwC_lift (le_max_right m k) hk)⟩
  | om _ ih =>
    obtain ⟨m, hm⟩ := ih
    exact ⟨m, KwC.om hm⟩
  | @coll π e hπ _ _ ihπ ihe =>
    obtain ⟨m, hm⟩ := ihπ
    obtain ⟨k, hk⟩ := ihe
    exact ⟨max m k + 1, KwC.coll hπ (kwC_lift (le_max_left m k) hm) (kwC_lift (le_max_right m k) hk) e.2⟩

theorem kwC_one {d : ℕ} : KwC S a z d 1 := by
  have := KwC.phi (S := S) (a := a) (z := z) (d := d) KwC.zero KwC.zero
  rwa [veblen_zero_apply, opow_zero] at this

theorem kwC_opow {d : ℕ} {x : Ordinal.{0}} (h : KwC S a z d x) : KwC S a z d (ω ^ x) := by
  have := KwC.phi KwC.zero h; rwa [veblen_zero_apply] at this

theorem kwC_mul_nat {d : ℕ} {p : Ordinal.{0}} (hp : KwC S a z d p) : ∀ n : ℕ, KwC S a z d (p * n) := by
  intro n
  induction n with
  | zero => rw [Nat.cast_zero, mul_zero]; exact KwC.zero
  | succ k ih => rw [Nat.cast_succ, mul_add_one]; exact KwC.add ih hp

theorem kwC_Om2 {d : ℕ} : KwC S a z d (Om (1 + 1)) := KwC.om (KwC.add kwC_one kwC_one)

/-- The leading summand and the rest at one depth. -/
theorem kwC_lead_tail {d : ℕ} {x : Ordinal.{0}} (hx : KwC S a z d x) (h0 : x ≠ 0) :
    KwC S a z d (lead x) ∧ KwC S a z d (tail x) := by
  have prin : ∀ {d y}, KwC S a z d y → IsPrincipal (· + ·) y → y ≠ 0 →
      KwC S a z d (lead y) ∧ KwC S a z d (tail y) := fun hy hP h0 => by
    obtain ⟨h1, h2⟩ := lead_tail_of_principal hP h0
    rw [h1, h2]; exact ⟨hy, KwC.zero⟩
  revert h0
  induction hx with
  | @small _ y h =>
    intro h0
    exact ⟨KwC.small (lt_of_le_of_lt (lead_le h0) h), KwC.small (lt_of_le_of_lt (tail_le y) h)⟩
  | zero => intro h0; exact absurd rfl h0
  | inacc n => intro h0; exact prin (KwC.inacc n) (SC_I n).isPrincipal h0
  | inaccW => intro h0; exact prin KwC.inaccW SC_Iw.isPrincipal h0
  | @add _ p q hp hq ihp ihq =>
    intro h0
    by_cases hq0 : q = 0
    · subst hq0; simp only [add_zero] at h0 ⊢; exact ihp h0
    by_cases hp0 : p = 0
    · subst hp0; simp only [zero_add] at h0 ⊢; exact ihq h0
    rcases lead_tail_add hp0 hq0 with habs | ⟨hl, ht⟩
    · rw [habs]; exact ihq hq0
    · rw [hl, ht]; exact ⟨(ihp hp0).1, KwC.add (ihp hp0).2 hq⟩
  | @phi _ p q hp hq _ _ =>
    intro h0; exact prin (KwC.phi hp hq) (veblen_isPrincipal p q) h0
  | @om _ p hp _ =>
    intro h0
    have hp0 : p ≠ 0 := by rintro rfl; exact h0 Om_zero
    exact prin (KwC.om hp) (SC_Om hp0).isPrincipal h0
  | @coll _ π e hπ hπC heC he _ _ =>
    intro h0; exact prin (KwC.coll hπ hπC heC he) (SC_psi hπ e).isPrincipal h0
  | up _ ih =>
    intro h0; obtain ⟨h1, h2⟩ := ih h0; exact ⟨KwC.up h1, KwC.up h2⟩

/-- `log_ω` at one depth. -/
theorem kwC_log {d : ℕ} {x : Ordinal.{0}} (hx : KwC S a z d x) : KwC S a z d (log ω x) := by
  have fix : ∀ {d p}, ω ^ p = p → KwC S a z d p → KwC S a z d (log ω p) := by
    intro d p hpE hpC
    have : log ω p = p := by conv_lhs => rw [← hpE]; exact log_opow one_lt_omega0 _
    rw [this]; exact hpC
  induction hx with
  | small h => exact KwC.small ((log_le_self ω _).trans_lt h)
  | zero => rw [log_zero_right]; exact KwC.zero
  | inacc n => exact fix (Low.opow_eq_self_of_SC (SC_I (S := S) n)) (KwC.inacc n)
  | inaccW => exact fix (Low.opow_eq_self_of_SC (SC_Iw (S := S))) KwC.inaccW
  | @add _ x y _ _ ihx ihy =>
    rcases ggLog_add x y with e | e <;> rw [e]
    · exact ihx
    · exact ihy
  | @phi _ x y hx hy _ _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [veblen_zero_apply, log_opow one_lt_omega0]; exact hy
    · exact fix (gg_veblen_eps hx0) (KwC.phi hx hy)
  | @om _ x hx _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero, log_zero_right]; exact KwC.zero
    · exact fix (Low.opow_eq_self_of_SC (SC_Om hx0)) (KwC.om hx)
  | @coll _ π e hπ hπC heC he _ _ =>
    exact fix (Low.opow_eq_self_of_SC (SC_psi hπ e)) (KwC.coll hπ hπC heC he)
  | up _ ih => exact KwC.up ih

/-- **`x - y` at one depth**, every `y`. -/
theorem kwC_sub {d : ℕ} : ∀ x, KwC S a z d x → ∀ y, KwC S a z d (x - y) := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx y
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [Ordinal.sub_eq_zero_iff_le.2 zero_le]; exact KwC.zero
  obtain ⟨-, htail⟩ := kwC_lead_tail hx hx0
  have hdec : lead x + tail x = x := lead_add_tail hx0
  rcases lt_or_ge y (lead x) with hy | hy
  · have e : y + x = x := Ordinal.add_of_omega0_opow_le hy (lead_le hx0)
    rw [Ordinal.sub_eq_of_add_eq e]; exact hx
  · obtain ⟨y', rfl⟩ := exists_add_of_le hy
    have e : x - (lead x + y') = tail x - y' := by
      have h := Ordinal.add_sub_add_cancel (lead x) (tail x) y'
      rwa [hdec] at h
    rw [e]
    exact IH _ (tail_lt hx0) htail y'

theorem kwC_rem {d : ℕ} {x : Ordinal.{0}} (hx : KwC S a z d x) : KwC S a z d (x % ω ^ log ω x) := by
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
  have hdm : x = ω ^ log ω x * n + x % ω ^ log ω x := by
    rw [← hn]; exact (Ordinal.div_add_mod x _).symm
  have e : x - ω ^ log ω x * n = x % ω ^ log ω x := by
    have e0 := Ordinal.add_sub_cancel (ω ^ log ω x * n) (x % ω ^ log ω x)
    rwa [← hdm] at e0
  rw [← e]; exact kwC_sub x hx _

/-- **The division by `ω^p` at one depth.** -/
theorem kwC_div {d : ℕ} : ∀ w, KwC S a z d w → ∀ p : Ordinal.{0},
    KwC S a z d (ω ^ p * (w / ω ^ p)) ∧ KwC S a z d (w % ω ^ p) ∧
      (KwC S a z d p → KwC S a z d (w / ω ^ p)) := by
  intro w
  induction w using WellFoundedLT.induction with
  | ind w IH =>
  intro hw p
  rcases eq_or_ne w 0 with rfl | hw0
  · rw [Ordinal.zero_div, Ordinal.zero_mod, mul_zero]
    exact ⟨KwC.zero, KwC.zero, fun _ => KwC.zero⟩
  have hp0 : ω ^ p ≠ 0 := (opow_pos p omega0_pos).ne'
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt w one_lt_omega0)
  have hdm : w = ω ^ log ω w * n + w % ω ^ log ω w := by
    rw [← hn]; exact (Ordinal.div_add_mod w _).symm
  have he : KwC S a z d (log ω w) := kwC_log hw
  have hs : KwC S a z d (w % ω ^ log ω w) := kwC_rem hw
  have hsw : w % ω ^ log ω w < w :=
    (Ordinal.mod_lt w (opow_pos _ omega0_pos).ne').trans_le (opow_log_le_self ω hw0)
  rcases lt_or_ge (log ω w) p with hep | hpe
  · have hwp : w < ω ^ p :=
      (lt_opow_succ_log_self one_lt_omega0 w).trans_le
        (opow_le_opow_right omega0_pos (Order.succ_le_of_lt hep))
    rw [Ordinal.div_eq_zero_of_lt hwp, Ordinal.mod_eq_of_lt hwp, mul_zero]
    exact ⟨KwC.zero, hw, fun _ => KwC.zero⟩
  have hsplit : ω ^ log ω w = ω ^ p * ω ^ (log ω w - p) := by
    rw [← opow_add, Ordinal.add_sub_cancel_of_le hpe]
  have hw' : w = ω ^ p * (ω ^ (log ω w - p) * n) + w % ω ^ log ω w := by
    conv_lhs => rw [hdm]
    rw [hsplit, mul_assoc]
  have hdiv : w / ω ^ p = ω ^ (log ω w - p) * n + w % ω ^ log ω w / ω ^ p := by
    conv_lhs => rw [hw']
    rw [Ordinal.mul_add_div _ hp0]
  have hmod : w % ω ^ p = w % ω ^ log ω w % ω ^ p := by
    conv_lhs => rw [hw']
    rw [Ordinal.mul_add_mod_self]
  obtain ⟨i1, i2, i3⟩ := IH _ hsw hs p
  refine ⟨?_, ?_, ?_⟩
  · rw [hdiv, mul_add, ← mul_assoc, ← hsplit]
    exact KwC.add (kwC_mul_nat (kwC_opow he) n) i1
  · rw [hmod]; exact i2
  · intro hp
    rw [hdiv]
    exact KwC.add (kwC_mul_nat (kwC_opow (kwC_sub _ he p)) n) (i3 hp)

/-- **The exponent of a member of `[β + W^E, β + W^{E+1})` at the same depth**. -/
theorem kwExt {d : ℕ} {β E y : Ordinal.{0}} (hy : KwC S a z d y)
    (h1 : β + leWe E ≤ y) (h2 : y < β + leWe (E + 1)) : KwC S a z d E := by
  have hβy : β ≤ y := le_self_add.trans h1
  set w := y - β with hwdef
  have hw : KwC S a z d w := kwC_sub y hy β
  have e1 : y = β + w := (Ordinal.add_sub_cancel_of_le hβy).symm
  have hw1 : leWe E ≤ w := by
    have := h1; rw [e1] at this; exact (add_le_add_iff_left β).1 this
  have hw2 : w < leWe (E + 1) := by
    have := h2; rw [e1] at this; exact (add_lt_add_iff_left β).1 this
  have hWE0 : leWe E ≠ 0 := (leWe_pos E).ne'
  set δ := w / leWe E with hδdef
  set r := w % leWe E with hrdef
  have hwd : w = leWe E * δ + r := (Ordinal.div_add_mod w _).symm
  have hr : r < leWe E := Ordinal.mod_lt w hWE0
  have hδ0 : δ ≠ 0 := by
    intro h0
    have : w < leWe E := by rw [hwd, h0, mul_zero, zero_add]; exact hr
    exact absurd hw1 (not_le.2 this)
  have hδ2 : δ < Om (1 + 1) := by
    rw [leWe_succ] at hw2
    exact (Ordinal.lt_mul_iff_div_lt hWE0).1 hw2
  have hlog := kwC_log hw
  have hlogδ : log ω δ < Om (1 + 1) := (log_le_self ω δ).trans_lt hδ2
  have e2 : log ω w = Om (1 + 1) * E + log ω δ := by
    rw [hwd]
    unfold leWe at hr ⊢
    exact log_opow_mul_add (b := ω) (u := Om (1 + 1) * E) (v := δ) (w := r) one_lt_omega0 hδ0 hr
  rw [e2] at hlog
  have h3 := (kwC_div _ hlog (Om (1 + 1))).2.2 kwC_Om2
  rwa [gg_SC_eps ldOm2_SC, Ordinal.mul_add_div _ ldOm2_SC.1.ne', Ordinal.div_eq_zero_of_lt hlogδ,
    add_zero] at h3

/-- Every member of `Cl(b, s)` of depth `d` lies in `Cl(a₁, s)`, `a₁ = β + W^E`, or `E` has a smaller depth. -/
theorem kwStar {β E b s : Ordinal.{0}} (hb : b ≤ β + leWe (E + 1)) :
    ∀ {d : ℕ} {y : Ordinal.{0}}, KwC S b s d y →
      y ∈ S.CSet (β + leWe E) s ∨ ∃ d' < d, KwC S b s d' E := by
  intro d y hy
  induction hy with
  | small h => exact Or.inl (CSet.of_lt h)
  | zero => exact Or.inl (CSet.zero_mem _ _)
  | inacc n => exact Or.inl (CSet.I_mem _ _ n)
  | inaccW => exact Or.inl (CSet.Iw_mem _ _)
  | add _ _ ihx ihy =>
    rcases ihx with hx | hx
    · rcases ihy with hy | hy
      · exact Or.inl (CSet.add_mem hx hy)
      · exact Or.inr hy
    · exact Or.inr hx
  | phi _ _ ihx ihy =>
    rcases ihx with hx | hx
    · rcases ihy with hy | hy
      · exact Or.inl (CSet.phi_mem hx hy)
      · exact Or.inr hy
    · exact Or.inr hx
  | om _ ih =>
    rcases ih with hx | hx
    · exact Or.inl (CSet.Om_mem hx)
    · exact Or.inr hx
  | @coll d π e hπ _ heC he ihπ ihe =>
    rcases lt_or_ge e (β + leWe E) with hea | hea
    · rcases ihπ with hπ' | ⟨d', hd', h'⟩
      · rcases ihe with he' | ⟨d', hd', h'⟩
        · exact Or.inl (CSet.psi_mem hea hπ hπ' he')
        · exact Or.inr ⟨d', hd'.trans (lt_add_one d), h'⟩
      · exact Or.inr ⟨d', hd'.trans (lt_add_one d), h'⟩
    · exact Or.inr ⟨d, lt_add_one d, kwExt heC hea (he.trans_le hb)⟩
  | @up d _ _ ih =>
    rcases ih with hx | ⟨d', hd', h'⟩
    · exact Or.inl hx
    · exact Or.inr ⟨d', hd'.trans (lt_add_one d), h'⟩

/-- **THE FIRST USE**: for a normal `b = β + W^E·γ` (`W^{E+1} ∣ β`, `0 < γ < Ω₂`),
`E ∈ Cl(β + W^E, ψ₂(β + W^E))`. -/
theorem kwFU {β E γ : Ordinal.{0}} (hdv : leWe (E + 1) ∣ β) (hγ0 : γ ≠ 0) (hγ2 : γ < Om (1 + 1))
    (hbn : β + leWe E * γ ∈ S.CSet (β + leWe E * γ) (S.psi (β + leWe E * γ) (Om (1 + 1)))) :
    E ∈ S.CSet (β + leWe E) (S.psi (β + leWe E) (Om (1 + 1))) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  set b := β + leWe E * γ with hbdef
  set a₁ := β + leWe E with ha₁def
  set s := S.psi a₁ (Om (1 + 1)) with hsdef
  have hb : b ≤ β + leWe (E + 1) := by
    rw [leWe_succ]; exact add_le_add le_rfl (leMulWe_mono hγ2.le)
  have hEb : E ∈ S.CSet b s := by
    by_contra hne
    have hsub : S.CSet b s ⊆ S.CSet a₁ s := by
      intro y hy
      obtain ⟨d, hd⟩ := CSet_kwC hy
      rcases kwStar hb hd with h | ⟨d', _, h'⟩
      · exact h
      · exact absurd (kwC_CSet h') hne
    have hψ : S.psi b (Om (1 + 1)) ≤ s :=
      psi_le_of_good (mxOm2_mem _ _) fun x hx hx2 => lt_psi_of_mem hκ2 (hsub hx) hx2
    exact hne (CSet_mono le_rfl hψ (kjEfrom hdv hγ0 hγ2 hbn).1)
  obtain ⟨d, hd⟩ := CSet_kwC hEb
  classical
  have hex : ∃ d, KwC S b s d E := ⟨d, hd⟩
  rcases kwStar hb (Nat.find_spec hex) with h | ⟨d', hd', h'⟩
  · exact h
  · exact absurd h' (Nat.find_min hex hd')

/-- **The truncations are normal**: `β + W^E·c` for every `c ≥ 1` with `c < ψ₂(β + W^E·c)`. -/
theorem kwTrunc {β E γ c : Ordinal.{0}} (hdv : leWe (E + 1) ∣ β) (hγ0 : γ ≠ 0) (hγ2 : γ < Om (1 + 1))
    (hbn : β + leWe E * γ ∈ S.CSet (β + leWe E * γ) (S.psi (β + leWe E * γ) (Om (1 + 1))))
    (hβn : β ∈ S.CSet β (S.psi β (Om (1 + 1)))) (hc1 : 1 ≤ c)
    (hown : c < S.psi (β + leWe E * c) (Om (1 + 1))) :
    β + leWe E * c ∈ S.CSet (β + leWe E * c) (S.psi (β + leWe E * c) (Om (1 + 1))) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hle : β + leWe E ≤ β + leWe E * c := add_le_add le_rfl (Ordinal.le_mul_left _ (zero_lt_one.trans_le hc1))
  have hE := CSet_mono hle (psi_mono hκ2 hle).1 (kwFU hdv hγ0 hγ2 hbn)
  have hβle : β ≤ β + leWe E * c := le_self_add
  have hβ := CSet_mono hβle (psi_mono hκ2 hβle).1 hβn
  exact CSet.add_mem hβ (leMulWe_mem hE (CSet.of_lt hown))

end Googology.Trans.PoR.InaccPsi.R2.Kw

#print axioms Googology.Trans.PoR.InaccPsi.R2.Kw.kwFU
#print axioms Googology.Trans.PoR.InaccPsi.R2.Kw.kwTrunc

import Googology.Trans.PoR.InaccPsi.R2.KtOwnY

/-!
# Ku: THE GAPS TOWARD A TARGET (`Kt.KtGapY`), and the `φ`-node of a successor argument

`φ = veblen`.  At a limit level `α`, `φ(α, d + 1) = sup_{λ<α} φ(λ, φ(α, d) + 1)` (`Ta.taVeb_lim_cof`): the context
`x ↦ φ(L(x), c)`, `c = φ(α, d) + 1`, is not continuous at the top, but it has the gap toward the target
`φ(α, d + 1)`.  `KgGap κ L C z` is `KtGapY (L κ) L C z`.

* `KuLvlS` (the level property toward `φ(α, d + 1)`), `kuLvlS` (**for `Cl(a, b)`**), `kuLvlSH` (**for `HCl`**): a
  member `x < φ(α, d + 1)` lies below `φ(λ + 1, φ(α, d) + 1)` for a member `λ < α`;
* `kuG_id`, `kuG_opowY`, `kuG_phiRY`, `kuG_phiL0Y`, `kuG_phiLS` (**the gaps toward a target**: the identity, `ω^·`,
  `φ(d, ·)`, `φ(·, 0)`, and `φ(·, φ(α, d) + 1)` toward `φ(α, d + 1)`).

No new axiom.  New definition: `KuLvlS`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ku

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Kg Googology.Trans.PoR.InaccPsi.R2.Kt Googology.Trans.PoR.InaccPsi.R2.Ta

variable {S : InaccSeq.{0}}

/-- **The level property toward `φ(α, d + 1)`.** -/
def KuLvlS (C : Set Ordinal.{0}) : Prop :=
  ∀ x ∈ C, ∀ α d, IsSuccLimit α → x < veblen α (d + 1) →
    ∃ l ∈ C, l < α ∧ x < veblen (l + 1) (veblen α d + 1)

section Steps

variable {P : Ordinal.{0} → Prop} {α d : Ordinal.{0}}

/-- Anything at most `φ(α, d)` is below `φ(0 + 1, φ(α, d) + 1)`. -/
theorem kuS_low {x : Ordinal.{0}} (hx : x ≤ veblen α d) : x < veblen (0 + 1) (veblen α d + 1) := by
  rw [zero_add]
  exact (hx.trans_lt (lt_add_one _)).trans_le (right_le_veblen 1 _)

theorem kuS_add {x y : Ordinal.{0}} (hx : ∃ l, P l ∧ l < α ∧ x < veblen (l + 1) (veblen α d + 1))
    (hy : ∃ l, P l ∧ l < α ∧ y < veblen (l + 1) (veblen α d + 1)) :
    ∃ l, P l ∧ l < α ∧ x + y < veblen (l + 1) (veblen α d + 1) := by
  obtain ⟨a1, h1, h1α, hx1⟩ := hx
  obtain ⟨a2, h2, h2α, hy2⟩ := hy
  rcases le_total a1 a2 with h | h
  · refine ⟨a2, h2, h2α, Ph.ph_veblen_prin _ _ (hx1.trans_le ?_) hy2⟩
    exact veblen_left_monotone _ (add_le_add h le_rfl)
  · refine ⟨a1, h1, h1α, Ph.ph_veblen_prin _ _ hx1 (hy2.trans_le ?_)⟩
    exact veblen_left_monotone _ (add_le_add h le_rfl)

theorem kuS_phi {p q : Ordinal.{0}} (hP0 : P 0) (hα0 : 0 < α) (hp : P p) (hpq : veblen p q < veblen α (d + 1))
    (hq : q < veblen α (d + 1) → ∃ l, P l ∧ l < α ∧ q < veblen (l + 1) (veblen α d + 1)) :
    ∃ l, P l ∧ l < α ∧ veblen p q < veblen (l + 1) (veblen α d + 1) := by
  rcases lt_trichotomy p α with hpα | rfl | hpα
  · obtain ⟨a1, h1, h1α, hq1⟩ := hq ((right_le_veblen p q).trans_lt hpq)
    have key : ∀ a, p < a + 1 → q < veblen (a + 1) (veblen α d + 1) →
        veblen p q < veblen (a + 1) (veblen α d + 1) := fun a hpa hqa => by
      calc veblen p q < veblen p (veblen (a + 1) (veblen α d + 1)) := (veblen_lt_veblen_iff_right).2 hqa
        _ = veblen (a + 1) (veblen α d + 1) := veblen_veblen_of_lt hpa _
    rcases le_total p a1 with h | h
    · exact ⟨a1, h1, h1α, key a1 (h.trans_lt (lt_add_one a1)) hq1⟩
    · refine ⟨p, hp, hpα, key p (lt_add_one p) (hq1.trans_le ?_)⟩
      exact veblen_left_monotone _ (add_le_add h le_rfl)
  · -- `φ(α, q) < φ(α, d + 1)`: `q ≤ d`
    have hqd : q ≤ d := Order.lt_add_one_iff.1 ((veblen_lt_veblen_iff_right).1 hpq)
    exact ⟨0, hP0, hα0, kuS_low ((veblen_le_veblen_iff_right).2 hqd)⟩
  · -- `φ(p, q)` is a fixed point of `φ(α, ·)`: `φ(p, q) ≤ d`
    have hfix : veblen α (veblen p q) = veblen p q := veblen_veblen_of_lt hpα q
    have hle : veblen p q ≤ d := by
      by_contra hc
      push Not at hc
      have : veblen α (d + 1) ≤ veblen p q := by
        rw [← hfix]; exact (veblen_le_veblen_iff_right).2 (Order.add_one_le_of_lt hc)
      exact absurd hpq (not_lt.2 this)
    exact ⟨0, hP0, hα0, kuS_low (hle.trans (right_le_veblen α d))⟩

theorem kuS_SC {z : Ordinal.{0}} (hP0 : P 0) (hα0 : 0 < α) (hz : SC z) (hPz : P z) (hzα : z < veblen α (d + 1)) :
    ∃ l, P l ∧ l < α ∧ z < veblen (l + 1) (veblen α d + 1) := by
  rcases lt_or_ge z α with h | h
  · refine ⟨z, hPz, h, ?_⟩
    calc z = veblen z 0 := hz.veblen_zero.symm
      _ < veblen (z + 1) 0 := veblen_zero_lt_veblen_zero.2 (lt_add_one z)
      _ ≤ veblen (z + 1) (veblen α d + 1) := (veblen_le_veblen_iff_right).2 zero_le
  · refine ⟨0, hP0, hα0, kuS_low ?_⟩
    rcases eq_or_lt_of_le h with heq | hlt
    · rw [← heq]; exact (left_le_veblen α 0).trans ((veblen_le_veblen_iff_right).2 zero_le)
    · have hfix : veblen α z = z := hz.veblen_right hlt
      have hzd : z ≤ d := by
        by_contra hc
        push Not at hc
        have : veblen α (d + 1) ≤ z := by
          rw [← hfix]; exact (veblen_le_veblen_iff_right).2 (Order.add_one_le_of_lt hc)
        exact absurd hzα (not_lt.2 this)
      exact hzd.trans (right_le_veblen α d)

theorem kuS_small {x B : Ordinal.{0}} (hPs : ∀ y, y < B → P y) (hxB : x < B) (hα : IsSuccLimit α)
    (hx : x < veblen α (d + 1)) : ∃ l, P l ∧ l < α ∧ x < veblen (l + 1) (veblen α d + 1) := by
  obtain ⟨a', ha'α, hxa'⟩ := taVeb_lim_cof hα hx
  rcases le_total x a' with h | h
  · refine ⟨x, hPs x hxB, h.trans_lt ha'α, ?_⟩
    exact (lt_add_one x).trans_le (left_le_veblen (x + 1) _)
  · refine ⟨a', hPs a' (h.trans_lt hxB), ha'α, hxa'.trans_le ?_⟩
    exact veblen_left_monotone _ (le_of_lt (lt_add_one a'))

end Steps

/-- **The level toward `φ(α, d + 1)` of a member of `Cl(a, b)`.** -/
theorem kuLvlS {A B : Ordinal.{0}} : KuLvlS (S.CSet A B) := by
  intro x hx
  induction hx with
  | @small x hx =>
    intro α d hα hxα
    exact kuS_small (P := (· ∈ S.CSet A B)) (fun y hy => CSet.of_lt hy) hx hα hxα
  | zero => intro α d hα _; exact ⟨0, CSet.zero_mem _ _, hα.bot_lt, veblen_pos⟩
  | inacc n =>
    intro α d hα hxα
    exact kuS_SC (P := (· ∈ S.CSet A B)) (CSet.zero_mem _ _) hα.bot_lt (SC_I n) (Clos.inacc n) hxα
  | inaccW =>
    intro α d hα hxα
    exact kuS_SC (P := (· ∈ S.CSet A B)) (CSet.zero_mem _ _) hα.bot_lt SC_Iw Clos.inaccW hxα
  | @add x y _ _ ihx ihy =>
    intro α d hα hxα
    exact kuS_add (P := (· ∈ S.CSet A B)) (ihx α d hα (le_self_add.trans_lt hxα))
      (ihy α d hα (le_add_self.trans_lt hxα))
  | @phi p q hp _ _ ihq =>
    intro α d hα hxα
    exact kuS_phi (P := (· ∈ S.CSet A B)) (CSet.zero_mem _ _) hα.bot_lt hp hxα (ihq α d hα)
  | @om x hx _ =>
    intro α d hα hxα
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero]; exact ⟨0, CSet.zero_mem _ _, hα.bot_lt, veblen_pos⟩
    · exact kuS_SC (P := (· ∈ S.CSet A B)) (CSet.zero_mem _ _) hα.bot_lt (SC_Om hx0) (Clos.om hx) hxα
  | @coll π e hπ hπC heC _ _ =>
    intro α d hα hxα
    exact kuS_SC (P := (· ∈ S.CSet A B)) (CSet.zero_mem _ _) hα.bot_lt (SC_psi hπ e.1) (Clos.coll hπ hπC heC) hxα

/-- **The level toward `φ(α, d + 1)` of a member of `HCl(a, Z)`.** -/
theorem kuLvlSH {a Z : Ordinal.{0}} : KuLvlS {x | HCl S a Z x} := by
  intro x hx
  induction hx with
  | @small x hx =>
    intro α d hα hxα
    exact kuS_small (P := fun y => HCl S a Z y) (fun y hy => HCl.small hy) hx hα hxα
  | zero => intro α d hα _; exact ⟨0, HCl.zero, hα.bot_lt, veblen_pos⟩
  | inacc n =>
    intro α d hα hxα
    exact kuS_SC (P := fun y => HCl S a Z y) HCl.zero hα.bot_lt (SC_I n) (HCl.inacc n) hxα
  | inaccW =>
    intro α d hα hxα
    exact kuS_SC (P := fun y => HCl S a Z y) HCl.zero hα.bot_lt SC_Iw HCl.inaccW hxα
  | @add x y _ _ ihx ihy =>
    intro α d hα hxα
    exact kuS_add (P := fun y => HCl S a Z y) (ihx α d hα (le_self_add.trans_lt hxα))
      (ihy α d hα (le_add_self.trans_lt hxα))
  | @phi p q hp _ _ ihq =>
    intro α d hα hxα
    exact kuS_phi (P := fun y => HCl S a Z y) HCl.zero hα.bot_lt hp hxα (ihq α d hα)
  | @om x hx _ =>
    intro α d hα hxα
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero]; exact ⟨0, HCl.zero, hα.bot_lt, veblen_pos⟩
    · exact kuS_SC (P := fun y => HCl S a Z y) HCl.zero hα.bot_lt (SC_Om hx0) (HCl.om hx) hxα
  | @coll π e hπ hπ1 hπC heC he _ _ =>
    intro α d hα hxα
    exact kuS_SC (P := fun y => HCl S a Z y) HCl.zero hα.bot_lt (SC_psi hπ e)
      (HCl.coll hπ hπ1 hπC heC he) hxα

section Gap

variable {C : Set Ordinal.{0}} {κ z : Ordinal.{0}}

/-- **The identity** has the gap toward `κ`. -/
theorem kuG_id (hC : KtCl C κ z) : KtGapY κ (fun x => x) C z :=
  fun e he hlt => ⟨e, hC.bnd e he hlt, lt_add_one e⟩

/-- **The gap toward `b + ω^Y` of `b + ω^{L(x)}`.** -/
theorem kuG_opowY (hC : KtCl C κ z) {b Y : Ordinal.{0}} {L : Ordinal.{0} → Ordinal.{0}} (hg : KtGapY Y L C z) :
    KtGapY (b + ω ^ Y) (fun x => b + ω ^ L x) C z := by
  intro e he hlt
  rcases lt_or_ge e b with h1 | h1
  · exact ⟨0, hC.zSC.1, h1.trans_le le_self_add⟩
  · have hd : e - b < ω ^ Y := Ry.rySub_lt h1 hlt
    have hdC : e - b ∈ C := hC.sub e he b
    have e1 : e = b + (e - b) := (Ordinal.add_sub_cancel_of_le h1).symm
    rcases eq_or_ne (e - b) 0 with h0 | h0
    · refine ⟨0, hC.zSC.1, ?_⟩
      show e < b + ω ^ L (0 + 1)
      rw [e1, h0, add_zero]
      exact lt_add_of_pos_right b (opow_pos _ omega0_pos)
    · have hlog : log ω (e - b) < Y := (lt_opow_iff_log_lt one_lt_omega0 h0).1 hd
      obtain ⟨q, hq, hqe⟩ := hg _ (hC.log _ hdC) hlog
      refine ⟨q, hq, ?_⟩
      show e < b + ω ^ L (q + 1)
      rw [e1]
      exact (add_lt_add_iff_left b).2 ((lt_opow_iff_log_lt one_lt_omega0 h0).2 hqe)

/-- **The gap toward `b + φ(d, Y)` of `b + φ(d, L(x))`.** -/
theorem kuG_phiRY (hC : KtCl C κ z) {b d Y : Ordinal.{0}} {L : Ordinal.{0} → Ordinal.{0}}
    (hg : KtGapY Y L C z) : KtGapY (b + veblen d Y) (fun x => b + veblen d (L x)) C z := by
  intro e he hlt
  rcases lt_or_ge e b with h1 | h1
  · exact ⟨0, hC.zSC.1, h1.trans_le le_self_add⟩
  · have hd : e - b < veblen d Y := Ry.rySub_lt h1 hlt
    have hdC : e - b ∈ C := hC.sub e he b
    have e1 : e = b + (e - b) := (Ordinal.add_sub_cancel_of_le h1).symm
    rcases lt_or_ge (e - b) (veblen d 0) with h0 | h0
    · refine ⟨0, hC.zSC.1, ?_⟩
      show e < b + veblen d (L (0 + 1))
      rw [e1]
      exact (add_lt_add_iff_left b).2 (h0.trans_le ((veblen_le_veblen_iff_right).2 zero_le))
    · obtain ⟨u, huC, hu1, hu2⟩ := hC.idx d _ hdC h0
      have huY : u < Y := (veblen_lt_veblen_iff_right).1 (hu1.trans_lt hd)
      obtain ⟨q, hq, hqu⟩ := hg u huC huY
      refine ⟨q, hq, ?_⟩
      show e < b + veblen d (L (q + 1))
      rw [e1]
      exact (add_lt_add_iff_left b).2 (hu2.trans_le ((veblen_le_veblen_iff_right).2
        (Order.add_one_le_of_lt hqu)))

/-- **The gap toward `b + φ(Y, 0)` of `b + φ(L(x), 0)`.** -/
theorem kuG_phiL0Y (hC : KtCl C κ z) (hlv : KtLvl C) {b Y : Ordinal.{0}} {L : Ordinal.{0} → Ordinal.{0}}
    (hg : KtGapY Y L C z) : KtGapY (b + veblen Y 0) (fun x => b + veblen (L x) 0) C z := by
  intro e he hlt
  rcases lt_or_ge e b with h1 | h1
  · exact ⟨0, hC.zSC.1, h1.trans_le le_self_add⟩
  · have hd : e - b < veblen Y 0 := Ry.rySub_lt h1 hlt
    have hdC : e - b ∈ C := hC.sub e he b
    have e1 : e = b + (e - b) := (Ordinal.add_sub_cancel_of_le h1).symm
    rcases eq_or_ne Y 0 with h0 | h0
    · have hd0 : e - b = 0 := by
        rw [h0, veblen_zero_apply, opow_zero] at hd; exact Order.lt_one_iff.1 hd
      refine ⟨0, hC.zSC.1, ?_⟩
      show e < b + veblen (L (0 + 1)) 0
      rw [e1, hd0, add_zero]; exact lt_add_of_pos_right b veblen_pos
    · obtain ⟨α', hα'C, hα'Y, hdα'⟩ := hlv _ hdC Y (pos_iff_ne_zero.2 h0) hd
      obtain ⟨q, hq, hqα⟩ := hg α' hα'C hα'Y
      refine ⟨q, hq, ?_⟩
      show e < b + veblen (L (q + 1)) 0
      rw [e1]
      exact (add_lt_add_iff_left b).2 (hdα'.trans_le (veblen_zero_strictMono.monotone
        (Order.add_one_le_of_lt hqα)))

/-- **The gap toward `b + φ(α, d + 1)` of `b + φ(L(x), φ(α, d) + 1)`**, `α` a limit, `L` with the gap toward `α`. -/
theorem kuG_phiLS (hC : KtCl C κ z) (hlv : KuLvlS C) {b α d : Ordinal.{0}} (hα : IsSuccLimit α)
    {L : Ordinal.{0} → Ordinal.{0}} (hg : KtGapY α L C z) :
    KtGapY (b + veblen α (d + 1)) (fun x => b + veblen (L x) (veblen α d + 1)) C z := by
  intro e he hlt
  rcases lt_or_ge e b with h1 | h1
  · exact ⟨0, hC.zSC.1, h1.trans_le le_self_add⟩
  · have hd : e - b < veblen α (d + 1) := Ry.rySub_lt h1 hlt
    have hdC : e - b ∈ C := hC.sub e he b
    have e1 : e = b + (e - b) := (Ordinal.add_sub_cancel_of_le h1).symm
    obtain ⟨l, hlC, hlα, hdl⟩ := hlv _ hdC α d hα hd
    obtain ⟨q, hq, hql⟩ := hg l hlC hlα
    refine ⟨q, hq, ?_⟩
    show e < b + veblen (L (q + 1)) (veblen α d + 1)
    rw [e1]
    exact (add_lt_add_iff_left b).2 (hdl.trans_le (veblen_left_monotone _ (Order.add_one_le_of_lt hql)))

end Gap

end Googology.Trans.PoR.InaccPsi.R2.Ku

#print axioms Googology.Trans.PoR.InaccPsi.R2.Ku.kuLvlS
#print axioms Googology.Trans.PoR.InaccPsi.R2.Ku.kuG_phiLS

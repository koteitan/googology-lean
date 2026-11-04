import Googology.Trans.PoR.InaccPsi.R2.ZiCode

/-!
# THE LEVEL-1 PLATEAU OVER THE COEFFICIENT: `ψ₁(B + Ω^{K+Ω₁·Ω₁}) = sup_m z_m`

`Ω^x = leOe x = ω^{Ω₁·x}`, `ψ₁ = ψ_{Ω₁}`, `X̂_y = Zi.ziXhp K y = K + Ω₁·y`.  The iterates over `B` and `K`:
`z_0 = 0`, `z_{m+1} = ψ₁(B + Ω^{K+Ω₁·z_m})` (`ziZO S K B m`).  The same argument as `Zi.ziPlatC` one level down:

* `ziZO_mono`, `ziR3O`, `ziKeyO`, `ziPlatO` (**`ψ₁(B + Ω^{K+Ω₁·Ω₁}) = sup_m ψ₁(B + Ω^{K+Ω₁·z_m})`**, every `B`, `K`),
  `ziOwnO_iff` (`(∀ ζ ≤ ξ, ζ < ψ₁(B + Ω^{K+Ω₁·ζ})) ⇔ ξ < ψ₁(B + Ω^{K+Ω₁·Ω₁})`).

No new axiom.  New definitions: `ziZO` (the level-1 iterates), `ziTO` (the bound `ψ₁(B + Ω^{K+Ω₁·Ω₁})`).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zi

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ug
  Googology.Trans.PoR.InaccPsi.R2.Zd

variable {S : InaccSeq.{0}}

theorem ziXhp_mono (K : Ordinal.{0}) {x y : Ordinal.{0}} (h : x ≤ y) : ziXhp K x ≤ ziXhp K y := by
  unfold ziXhp; exact (add_le_add_iff_left _).2 (mul_le_mul_left' h _)

/-- The bound `T(B) = ψ₁(B + Ω^{K+Ω₁·Ω₁})` of the coefficients over `B`. -/
noncomputable def ziTO (S : InaccSeq.{0}) (P a : Ordinal.{0}) : Ordinal.{0} :=
  S.psi (a + leOe (ziXhp P (Om 1))) (Om 1)

/-- The coefficient iterates `f_0 = 0`, `f_{m+1} = ψ₁(a + Ω^{K+Ω₁·f_m})`. -/
noncomputable def ziZO (S : InaccSeq.{0}) (P a : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => 0
  | m + 1 => S.psi (a + leOe (ziXhp P (ziZO S P a m))) (Om 1)

theorem ziZO_zero (P a : Ordinal.{0}) : ziZO S P a 0 = 0 := rfl

theorem ziZO_succ (P a : Ordinal.{0}) (m : ℕ) :
    ziZO S P a (m + 1) = S.psi (a + leOe (ziXhp P (ziZO S P a m))) (Om 1) := rfl

theorem ziZO_lt_Om1 (P a : Ordinal.{0}) : ∀ m, ziZO S P a m < Om 1
  | 0 => Ph.ph_SC_Om1.1
  | m + 1 => psi_lt (Low.InR_Om_one) _

theorem ziZO_le_succ (P a : Ordinal.{0}) : ∀ m, ziZO S P a m ≤ ziZO S P a (m + 1)
  | 0 => zero_le
  | m + 1 => by
    rw [ziZO_succ P a (m + 1), ziZO_succ P a m]
    exact (psi_mono (Low.InR_Om_one) (add_le_add_right (leOe_mono (ziXhp_mono P (ziZO_le_succ P a m))) a)).1

theorem ziZO_mono (P a : Ordinal.{0}) : Monotone (ziZO S P a) := monotone_nat_of_le_succ (ziZO_le_succ P a)

/-- `Ω₁·(P + Ω₁·x) = Ω₁·P + ω^{Ω₁+Ω₁}·x`. -/
theorem ziOm1_mul_Xhp (P x : Ordinal.{0}) :
    Om 1 * ziXhp P x = Om 1 * P + ω ^ (Om 1 + Om 1) * x := by
  unfold ziXhp; rw [mul_add, opow_add, gg_SC_eps Ph.ph_SC_Om1, mul_assoc]

/-- **A member of a stage below `a + Ω^{K+Ω₁·Ω₁}` is below the next stage's argument.** -/
theorem ziR3O (P a : Ordinal.{0}) (k : ℕ) {y : Ordinal.{0}}
    (hy : y ∈ S.CSet (a + leOe (ziXhp P (ziZO S P a k))) (S.psi (a + leOe (ziXhp P (ziZO S P a k))) (Om 1)))
    (hlt : y < a + leOe (ziXhp P (Om 1))) : y < a + leOe (ziXhp P (ziZO S P a (k + 1))) := by
  set b := a + leOe (ziXhp P (ziZO S P a k)) with hbdef
  set M := ω ^ (Om 1 + Om 1 : Ordinal.{0}) with hM
  have hκ2 : S.InR (Om (1 : Ordinal.{0})) := Low.InR_Om_one
  have hM0 : M ≠ 0 := opow_ne_zero _ omega0_ne_zero
  rcases lt_or_ge y a with h1 | h1
  · exact h1.trans_le le_self_add
  have hz : y - a ∈ S.CSet b (S.psi b (Om 1)) := Ta.taSub_mem y hy a
  have hzl : y - a < leOe (ziXhp P (Om 1)) := Ry.rySub_lt h1 hlt
  have e1 : y = a + (y - a) := (Ordinal.add_sub_cancel_of_le h1).symm
  rw [e1]
  refine (add_lt_add_iff_left a).2 ?_
  set z := y - a with hzdef
  rcases eq_or_ne z 0 with hz0 | hz0
  · rw [hz0]; exact leOe_pos _
  set L := log ω z with hLdef
  have hLmem : L ∈ S.CSet b (S.psi b (Om 1)) := leLog_mem hz
  have hzl' : z < ω ^ (Om 1 * P + M * Om 1) := by
    have h := hzl; unfold leOe at h; rwa [ziOm1_mul_Xhp] at h
  have hLlt : L < Om 1 * P + M * Om 1 := (lt_opow_iff_log_lt one_lt_omega0 hz0).1 hzl'
  unfold leOe
  refine (lt_opow_iff_log_lt one_lt_omega0 hz0).2 ?_
  rw [ziOm1_mul_Xhp]
  rcases lt_or_ge L (Om 1 * P) with h2 | h2
  · exact h2.trans_le le_self_add
  have hr : L - Om 1 * P < M * Om 1 := Ry.rySub_lt h2 hLlt
  have hrm : L - Om 1 * P ∈ S.CSet b (S.psi b (Om 1)) := Ta.taSub_mem L hLmem _
  set q := (L - Om 1 * P) / M with hq
  have hqm : q ∈ S.CSet b (S.psi b (Om 1)) :=
    (Vh.vhC_div _ hrm (Om 1 + Om 1)).2.2 (CSet.add_mem (CSet.Om_mem (CSet.one_mem _ _)) (CSet.Om_mem (CSet.one_mem _ _)))
  have hq2 : q < Om 1 := (Ordinal.lt_mul_iff_div_lt hM0).1 hr
  have hqf : q < ziZO S P a (k + 1) := by rw [ziZO_succ]; exact lt_psi_of_mem hκ2 hqm hq2
  have hq1 : q + 1 ≤ ziZO S P a (k + 1) := Order.add_one_le_of_lt hqf
  have hlm : L - Om 1 * P < M * (q + 1) := by
    have := Ordinal.lt_mul_succ_div (L - Om 1 * P) hM0
    rwa [Order.succ_eq_add_one] at this
  have e2 : L = Om 1 * P + (L - Om 1 * P) := (Ordinal.add_sub_cancel_of_le h2).symm
  show L < _
  rw [e2]
  exact (add_lt_add_iff_left _).2 (hlm.trans_le (mul_le_mul_left' hq1 _))

theorem ziStgO_mono (P a : Ordinal.{0}) {i j : ℕ} (h : i ≤ j) :
    S.CSet (a + leOe (ziXhp P (ziZO S P a i))) (S.psi (a + leOe (ziXhp P (ziZO S P a i))) (Om 1)) ⊆
      S.CSet (a + leOe (ziXhp P (ziZO S P a j))) (S.psi (a + leOe (ziXhp P (ziZO S P a j))) (Om 1)) :=
  (psi_mono (Low.InR_Om_one) (add_le_add_right (leOe_mono (ziXhp_mono P (ziZO_mono P a h))) a)).2

theorem ziZO_bdd (P a : Ordinal.{0}) :
    BddAbove (range fun m : ℕ => S.psi (a + leOe (ziXhp P (ziZO S P a m))) (Om 1)) :=
  ⟨Om 1, by rintro _ ⟨m, rfl⟩; exact (psi_lt (Low.InR_Om_one) _).le⟩

/-- **Every member of `Cl(a + Ω^{K+Ω₁·Ω₁}, sup_m ψ₁(a + Ω^{K+Ω₁·f_m}))` lies in a stage.** -/
theorem ziKeyO (P a : Ordinal.{0}) :
    ∀ y ∈ S.CSet (a + leOe (ziXhp P (Om 1))) (⨆ m : ℕ, S.psi (a + leOe (ziXhp P (ziZO S P a m))) (Om 1)),
      ∃ k, y ∈ S.CSet (a + leOe (ziXhp P (ziZO S P a k))) (S.psi (a + leOe (ziXhp P (ziZO S P a k))) (Om 1)) := by
  intro y hy
  induction hy with
  | small h =>
    obtain ⟨n, hn⟩ := (lt_ciSup_iff (ziZO_bdd P a)).1 h
    exact ⟨n, CSet.of_lt hn⟩
  | zero => exact ⟨0, CSet.zero_mem _ _⟩
  | inacc n => exact ⟨0, Clos.inacc n⟩
  | inaccW => exact ⟨0, Clos.inaccW⟩
  | add _ _ ihp ihq =>
    obtain ⟨i, hi⟩ := ihp
    obtain ⟨j, hj⟩ := ihq
    exact ⟨max i j, CSet.add_mem (ziStgO_mono P a (le_max_left i j) hi) (ziStgO_mono P a (le_max_right i j) hj)⟩
  | phi _ _ ihp ihq =>
    obtain ⟨i, hi⟩ := ihp
    obtain ⟨j, hj⟩ := ihq
    exact ⟨max i j, Clos.phi (ziStgO_mono P a (le_max_left i j) hi) (ziStgO_mono P a (le_max_right i j) hj)⟩
  | om _ ih =>
    obtain ⟨i, hi⟩ := ih
    exact ⟨i, CSet.Om_mem hi⟩
  | @coll π e hπ _ _ ihπ ihe =>
    obtain ⟨i, hi⟩ := ihπ
    obtain ⟨k, hk⟩ := ihe
    have hlt : e.1 < a + leOe (ziXhp P (ziZO S P a (k + 1))) := ziR3O P a k hk e.2
    set N := max (k + 1) i with hN
    have hltN : e.1 < a + leOe (ziXhp P (ziZO S P a N)) :=
      hlt.trans_le (add_le_add_right (leOe_mono (ziXhp_mono P (ziZO_mono P a (le_max_left (k + 1) i)))) a)
    have heN := ziStgO_mono P a ((Nat.le_succ k).trans (le_max_left (k + 1) i)) hk
    have hπN := ziStgO_mono P a (le_max_right (k + 1) i) hi
    exact ⟨N, Clos.coll (e := ⟨e.1, hltN⟩) hπ hπN heN⟩

/-- **THE PLATEAU OVER THE COEFFICIENT**: `ψ₁(a + Ω^{K+Ω₁·Ω₁}) = sup_m ψ₁(a + Ω^{K+Ω₁·f_m})` (every `a`). -/
theorem ziPlatO (P a : Ordinal.{0}) :
    ziTO S P a = ⨆ m : ℕ, S.psi (a + leOe (ziXhp P (ziZO S P a m))) (Om 1) := by
  have hκ2 : S.InR (Om (1 : Ordinal.{0})) := Low.InR_Om_one
  unfold ziTO
  refine le_antisymm (psi_le_of_good (CSet.Om_mem (CSet.one_mem _ _)) fun y hy hy2 => ?_) (ciSup_le fun m => ?_)
  · obtain ⟨n, hn⟩ := ziKeyO P a y hy
    exact (lt_psi_of_mem hκ2 hn hy2).trans_le (le_ciSup (ziZO_bdd P a) n)
  · exact (psi_mono hκ2 (add_le_add_right (leOe_mono (ziXhp_mono P (ziZO_lt_Om1 P a m).le)) a)).1

/-- Every `ζ < f_m` is own: `ζ < ψ₁(a + Ω^{K+Ω₁·ζ})`. -/
theorem ziOwnZO (P a : Ordinal.{0}) :
    ∀ m ζ, ζ < ziZO S P a m → ζ < S.psi (a + leOe (ziXhp P ζ)) (Om 1)
  | 0, ζ, h => absurd h (not_lt.2 zero_le)
  | m + 1, ζ, h => by
    rcases lt_or_ge ζ (ziZO S P a m) with h1 | h1
    · exact ziOwnZO P a m ζ h1
    · refine h.trans_le ?_
      rw [ziZO_succ]
      exact (psi_mono (Low.InR_Om_one) (add_le_add_right (leOe_mono (ziXhp_mono P h1)) a)).1

/-- **THE HEREDITARY OWN CONDITION OF THE COEFFICIENT**:
`(∀ ζ ≤ ξ, ζ < ψ₁(a + Ω^{K+Ω₁·ζ})) ⇔ ξ < ψ₁(a + Ω^{K+Ω₁·Ω₁})`. -/
theorem ziOwnO_iff (P a ξ : Ordinal.{0}) :
    (∀ ζ, ζ ≤ ξ → ζ < S.psi (a + leOe (ziXhp P ζ)) (Om 1)) ↔ ξ < ziTO S P a := by
  have hκ2 : S.InR (Om (1 : Ordinal.{0})) := Low.InR_Om_one
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have h1 := h _ hc
    have h2 : S.psi (a + leOe (ziXhp P (ziTO S P a))) (Om 1) ≤ ziTO S P a := by
      unfold ziTO
      exact (psi_mono hκ2 (add_le_add_right (leOe_mono (ziXhp_mono P (psi_lt hκ2 _).le)) a)).1
    exact absurd (h1.trans_le h2) (lt_irrefl _)
  · intro hξ ζ hζ
    rw [ziPlatO P] at hξ
    obtain ⟨m, hm⟩ := (lt_ciSup_iff (ziZO_bdd P a)).1 hξ
    rw [← ziZO_succ] at hm
    exact ziOwnZO P a (m + 1) ζ (hζ.trans_lt hm)

theorem ziTO_lt_Om1 (P a : Ordinal.{0}) : ziTO S P a < Om 1 := psi_lt (Low.InR_Om_one) _

end Googology.Trans.PoR.InaccPsi.R2.Zi

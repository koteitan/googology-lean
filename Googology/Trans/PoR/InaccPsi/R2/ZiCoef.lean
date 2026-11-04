import Googology.Trans.PoR.InaccPsi.R2.ZiShM

/-!
# THE PLATEAU OVER THE COEFFICIENT: `ψ₂(a + W^{P+Ω₂·Ω₂}) = sup_m f_m`

`W^x = leWe x`, `X_ξ = ziXp P ξ = P + Ω₂·ξ` over a prefix `P` (`P = Y₃`: `Zd.zdXr`), `ψ₂ = ψ_{Ω₂}`.  The coefficient iterates over a base `a`:
`f_0 = 0`, `f_{m+1} = ψ₂(a + W^{P+Ω₂·f_m})` (`ziFC S P a m`).

* `ziFC_mono`, `ziR3C` (a member of the stage `Cl(a + W^{P+Ω₂·f_k}, ψ₂(·))` below `a + W^{P+Ω₂·Ω₂}` is below
  `a + W^{P+Ω₂·f_{k+1}}`), `ziKeyC`,
* `ziPlatC` (**`ψ₂(a + W^{P+Ω₂·Ω₂}) = sup_m ψ₂(a + W^{P+Ω₂·f_m})`**, every `a`),
* `ziOwnC_iff` (**the hereditary own condition of the coefficient**:
  `(∀ ζ ≤ ξ, ζ < ψ₂(a + W^{P+Ω₂·ζ})) ⇔ ξ < ψ₂(a + W^{P+Ω₂·Ω₂})`, every `a`).

No new axiom.  New definitions: `ziXp`, `ziXhp` (the shift `P + Ω₂·x` and its image `P̂ + Ω₁·y`), `ziFC` (the coefficient iterates), `ziTC` (the bound `ψ₂(a + W^{P+Ω₂·Ω₂})`).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zi

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ug
  Googology.Trans.PoR.InaccPsi.R2.Zd

variable {S : InaccSeq.{0}}

/-- The shift `P + Ω₂·x` over the prefix `P`. -/
noncomputable def ziXp (P x : Ordinal.{0}) : Ordinal.{0} := P + Om (1 + 1) * x

/-- Its image `P̂ + Ω₁·y`. -/
noncomputable def ziXhp (Pt y : Ordinal.{0}) : Ordinal.{0} := Pt + Om 1 * y

theorem ziXp_zero (P : Ordinal.{0}) : ziXp P 0 = P := by unfold ziXp; rw [mul_zero, add_zero]

theorem ziXhp_zero (Pt : Ordinal.{0}) : ziXhp Pt 0 = Pt := by unfold ziXhp; rw [mul_zero, add_zero]

theorem ziXp_succ (P x : Ordinal.{0}) : ziXp P (x + 1) = ziXp P x + Om (1 + 1) := by
  unfold ziXp; rw [mul_add_one]; exact (add_assoc _ _ _).symm

theorem ziXhp_succ (Pt y : Ordinal.{0}) : ziXhp Pt (y + 1) = ziXhp Pt y + Om 1 := by
  unfold ziXhp; rw [mul_add_one]; exact (add_assoc _ _ _).symm

theorem ziXp_mono (P : Ordinal.{0}) {x y : Ordinal.{0}} (h : x ≤ y) : ziXp P x ≤ ziXp P y := by
  unfold ziXp; exact (add_le_add_iff_left _).2 (mul_le_mul_left' h _)

theorem ziXp_lt (P : Ordinal.{0}) {x y : Ordinal.{0}} (h : x < y) : ziXp P x < ziXp P y := by
  unfold ziXp; exact (add_lt_add_iff_left _).2 (mul_lt_mul_of_pos_left h ldOm2_SC.1)

theorem ziXhp_lt (Pt : Ordinal.{0}) {x y : Ordinal.{0}} (h : x < y) : ziXhp Pt x < ziXhp Pt y := by
  unfold ziXhp; exact (add_lt_add_iff_left _).2 (mul_lt_mul_of_pos_left h (Om_pos one_ne_zero))

/-- `Y₃ + Ω₂·x` is the shift over the prefix `Y₃`. -/
theorem ziXp_Y3 (x : Ordinal.{0}) : ziXp (ugY S) x = zdXr S x := rfl

theorem ziXhp_Y2 (y : Ordinal.{0}) : ziXhp (S.psi (Om (1 + 1)) (Om (1 + 1))) y = zdXhr S y := rfl

/-- The bound `T(a) = ψ₂(a + W^{P+Ω₂·Ω₂})` of the coefficients over the base `a`. -/
noncomputable def ziTC (S : InaccSeq.{0}) (P a : Ordinal.{0}) : Ordinal.{0} :=
  S.psi (a + leWe (ziXp P (Om (1 + 1)))) (Om (1 + 1))

/-- The coefficient iterates `f_0 = 0`, `f_{m+1} = ψ₂(a + W^{P+Ω₂·f_m})`. -/
noncomputable def ziFC (S : InaccSeq.{0}) (P a : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => 0
  | m + 1 => S.psi (a + leWe (ziXp P (ziFC S P a m))) (Om (1 + 1))

theorem ziFC_zero (P a : Ordinal.{0}) : ziFC S P a 0 = 0 := rfl

theorem ziFC_succ (P a : Ordinal.{0}) (m : ℕ) :
    ziFC S P a (m + 1) = S.psi (a + leWe (ziXp P (ziFC S P a m))) (Om (1 + 1)) := rfl

theorem ziFC_lt_Om2 (P a : Ordinal.{0}) : ∀ m, ziFC S P a m < Om (1 + 1)
  | 0 => ldOm2_SC.1
  | m + 1 => psi_lt (InR_Om_succ 1) _

theorem ziFC_le_succ (P a : Ordinal.{0}) : ∀ m, ziFC S P a m ≤ ziFC S P a (m + 1)
  | 0 => zero_le
  | m + 1 => by
    rw [ziFC_succ P a (m + 1), ziFC_succ P a m]
    exact (psi_mono (InR_Om_succ 1) (add_le_add_right (leWe_mono (ziXp_mono P (ziFC_le_succ P a m))) a)).1

theorem ziFC_mono (P a : Ordinal.{0}) : Monotone (ziFC S P a) := monotone_nat_of_le_succ (ziFC_le_succ P a)

/-- `Ω₂·(P + Ω₂·x) = Ω₂·P + ω^{Ω₂+Ω₂}·x`. -/
theorem ziOm2_mul_Xp (P x : Ordinal.{0}) :
    Om (1 + 1) * ziXp P x = Om (1 + 1) * P + ω ^ (Om (1 + 1) + Om (1 + 1)) * x := by
  unfold ziXp; rw [mul_add, opow_add, gg_SC_eps ldOm2_SC, mul_assoc]

/-- **A member of a stage below `a + W^{P+Ω₂·Ω₂}` is below the next stage's argument.** -/
theorem ziR3C (P a : Ordinal.{0}) (k : ℕ) {y : Ordinal.{0}}
    (hy : y ∈ S.CSet (a + leWe (ziXp P (ziFC S P a k))) (S.psi (a + leWe (ziXp P (ziFC S P a k))) (Om (1 + 1))))
    (hlt : y < a + leWe (ziXp P (Om (1 + 1)))) : y < a + leWe (ziXp P (ziFC S P a (k + 1))) := by
  set b := a + leWe (ziXp P (ziFC S P a k)) with hbdef
  set M := ω ^ (Om (1 + 1) + Om (1 + 1) : Ordinal.{0}) with hM
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hM0 : M ≠ 0 := opow_ne_zero _ omega0_ne_zero
  rcases lt_or_ge y a with h1 | h1
  · exact h1.trans_le le_self_add
  have hz : y - a ∈ S.CSet b (S.psi b (Om (1 + 1))) := Ta.taSub_mem y hy a
  have hzl : y - a < leWe (ziXp P (Om (1 + 1))) := Ry.rySub_lt h1 hlt
  have e1 : y = a + (y - a) := (Ordinal.add_sub_cancel_of_le h1).symm
  rw [e1]
  refine (add_lt_add_iff_left a).2 ?_
  set z := y - a with hzdef
  rcases eq_or_ne z 0 with hz0 | hz0
  · rw [hz0]; exact leWe_pos _
  set L := log ω z with hLdef
  have hLmem : L ∈ S.CSet b (S.psi b (Om (1 + 1))) := leLog_mem hz
  have hzl' : z < ω ^ (Om (1 + 1) * P + M * Om (1 + 1)) := by
    have h := hzl; unfold leWe at h; rwa [ziOm2_mul_Xp] at h
  have hLlt : L < Om (1 + 1) * P + M * Om (1 + 1) := (lt_opow_iff_log_lt one_lt_omega0 hz0).1 hzl'
  unfold leWe
  refine (lt_opow_iff_log_lt one_lt_omega0 hz0).2 ?_
  rw [ziOm2_mul_Xp]
  rcases lt_or_ge L (Om (1 + 1) * P) with h2 | h2
  · exact h2.trans_le le_self_add
  have hr : L - Om (1 + 1) * P < M * Om (1 + 1) := Ry.rySub_lt h2 hLlt
  have hrm : L - Om (1 + 1) * P ∈ S.CSet b (S.psi b (Om (1 + 1))) := Ta.taSub_mem L hLmem _
  set q := (L - Om (1 + 1) * P) / M with hq
  have hqm : q ∈ S.CSet b (S.psi b (Om (1 + 1))) :=
    (Vh.vhC_div _ hrm (Om (1 + 1) + Om (1 + 1))).2.2 (CSet.add_mem (mxOm2_mem _ _) (mxOm2_mem _ _))
  have hq2 : q < Om (1 + 1) := (Ordinal.lt_mul_iff_div_lt hM0).1 hr
  have hqf : q < ziFC S P a (k + 1) := by rw [ziFC_succ]; exact lt_psi_of_mem hκ2 hqm hq2
  have hq1 : q + 1 ≤ ziFC S P a (k + 1) := Order.add_one_le_of_lt hqf
  have hlm : L - Om (1 + 1) * P < M * (q + 1) := by
    have := Ordinal.lt_mul_succ_div (L - Om (1 + 1) * P) hM0
    rwa [Order.succ_eq_add_one] at this
  have e2 : L = Om (1 + 1) * P + (L - Om (1 + 1) * P) := (Ordinal.add_sub_cancel_of_le h2).symm
  show L < _
  rw [e2]
  exact (add_lt_add_iff_left _).2 (hlm.trans_le (mul_le_mul_left' hq1 _))

theorem ziStgC_mono (P a : Ordinal.{0}) {i j : ℕ} (h : i ≤ j) :
    S.CSet (a + leWe (ziXp P (ziFC S P a i))) (S.psi (a + leWe (ziXp P (ziFC S P a i))) (Om (1 + 1))) ⊆
      S.CSet (a + leWe (ziXp P (ziFC S P a j))) (S.psi (a + leWe (ziXp P (ziFC S P a j))) (Om (1 + 1))) :=
  (psi_mono (InR_Om_succ 1) (add_le_add_right (leWe_mono (ziXp_mono P (ziFC_mono P a h))) a)).2

theorem ziFC_bdd (P a : Ordinal.{0}) :
    BddAbove (range fun m : ℕ => S.psi (a + leWe (ziXp P (ziFC S P a m))) (Om (1 + 1))) :=
  ⟨Om (1 + 1), by rintro _ ⟨m, rfl⟩; exact (psi_lt (InR_Om_succ 1) _).le⟩

/-- **Every member of `Cl(a + W^{P+Ω₂·Ω₂}, sup_m ψ₂(a + W^{P+Ω₂·f_m}))` lies in a stage.** -/
theorem ziKeyC (P a : Ordinal.{0}) :
    ∀ y ∈ S.CSet (a + leWe (ziXp P (Om (1 + 1)))) (⨆ m : ℕ, S.psi (a + leWe (ziXp P (ziFC S P a m))) (Om (1 + 1))),
      ∃ k, y ∈ S.CSet (a + leWe (ziXp P (ziFC S P a k))) (S.psi (a + leWe (ziXp P (ziFC S P a k))) (Om (1 + 1))) := by
  intro y hy
  induction hy with
  | small h =>
    obtain ⟨n, hn⟩ := (lt_ciSup_iff (ziFC_bdd P a)).1 h
    exact ⟨n, CSet.of_lt hn⟩
  | zero => exact ⟨0, CSet.zero_mem _ _⟩
  | inacc n => exact ⟨0, Clos.inacc n⟩
  | inaccW => exact ⟨0, Clos.inaccW⟩
  | add _ _ ihp ihq =>
    obtain ⟨i, hi⟩ := ihp
    obtain ⟨j, hj⟩ := ihq
    exact ⟨max i j, CSet.add_mem (ziStgC_mono P a (le_max_left i j) hi) (ziStgC_mono P a (le_max_right i j) hj)⟩
  | phi _ _ ihp ihq =>
    obtain ⟨i, hi⟩ := ihp
    obtain ⟨j, hj⟩ := ihq
    exact ⟨max i j, Clos.phi (ziStgC_mono P a (le_max_left i j) hi) (ziStgC_mono P a (le_max_right i j) hj)⟩
  | om _ ih =>
    obtain ⟨i, hi⟩ := ih
    exact ⟨i, CSet.Om_mem hi⟩
  | @coll π e hπ _ _ ihπ ihe =>
    obtain ⟨i, hi⟩ := ihπ
    obtain ⟨k, hk⟩ := ihe
    have hlt : e.1 < a + leWe (ziXp P (ziFC S P a (k + 1))) := ziR3C P a k hk e.2
    set N := max (k + 1) i with hN
    have hltN : e.1 < a + leWe (ziXp P (ziFC S P a N)) :=
      hlt.trans_le (add_le_add_right (leWe_mono (ziXp_mono P (ziFC_mono P a (le_max_left (k + 1) i)))) a)
    have heN := ziStgC_mono P a ((Nat.le_succ k).trans (le_max_left (k + 1) i)) hk
    have hπN := ziStgC_mono P a (le_max_right (k + 1) i) hi
    exact ⟨N, Clos.coll (e := ⟨e.1, hltN⟩) hπ hπN heN⟩

/-- **THE PLATEAU OVER THE COEFFICIENT**: `ψ₂(a + W^{P+Ω₂·Ω₂}) = sup_m ψ₂(a + W^{P+Ω₂·f_m})` (every `a`). -/
theorem ziPlatC (P a : Ordinal.{0}) :
    ziTC S P a = ⨆ m : ℕ, S.psi (a + leWe (ziXp P (ziFC S P a m))) (Om (1 + 1)) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  unfold ziTC
  refine le_antisymm (psi_le_of_good (mxOm2_mem _ _) fun y hy hy2 => ?_) (ciSup_le fun m => ?_)
  · obtain ⟨n, hn⟩ := ziKeyC P a y hy
    exact (lt_psi_of_mem hκ2 hn hy2).trans_le (le_ciSup (ziFC_bdd P a) n)
  · exact (psi_mono hκ2 (add_le_add_right (leWe_mono (ziXp_mono P (ziFC_lt_Om2 P a m).le)) a)).1

/-- Every `ζ < f_m` is own: `ζ < ψ₂(a + W^{P+Ω₂·ζ})`. -/
theorem ziOwnFC (P a : Ordinal.{0}) :
    ∀ m ζ, ζ < ziFC S P a m → ζ < S.psi (a + leWe (ziXp P ζ)) (Om (1 + 1))
  | 0, ζ, h => absurd h (not_lt.2 zero_le)
  | m + 1, ζ, h => by
    rcases lt_or_ge ζ (ziFC S P a m) with h1 | h1
    · exact ziOwnFC P a m ζ h1
    · refine h.trans_le ?_
      rw [ziFC_succ]
      exact (psi_mono (InR_Om_succ 1) (add_le_add_right (leWe_mono (ziXp_mono P h1)) a)).1

/-- **THE HEREDITARY OWN CONDITION OF THE COEFFICIENT**:
`(∀ ζ ≤ ξ, ζ < ψ₂(a + W^{P+Ω₂·ζ})) ⇔ ξ < ψ₂(a + W^{P+Ω₂·Ω₂})`. -/
theorem ziOwnC_iff (P a ξ : Ordinal.{0}) :
    (∀ ζ, ζ ≤ ξ → ζ < S.psi (a + leWe (ziXp P ζ)) (Om (1 + 1))) ↔ ξ < ziTC S P a := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have h1 := h _ hc
    have h2 : S.psi (a + leWe (ziXp P (ziTC S P a))) (Om (1 + 1)) ≤ ziTC S P a := by
      unfold ziTC
      exact (psi_mono hκ2 (add_le_add_right (leWe_mono (ziXp_mono P (psi_lt hκ2 _).le)) a)).1
    exact absurd (h1.trans_le h2) (lt_irrefl _)
  · intro hξ ζ hζ
    rw [ziPlatC P] at hξ
    obtain ⟨m, hm⟩ := (lt_ciSup_iff (ziFC_bdd P a)).1 hξ
    rw [← ziFC_succ] at hm
    exact ziOwnFC P a (m + 1) ζ (hζ.trans_lt hm)

theorem ziTC_lt_Om2 (P a : Ordinal.{0}) : ziTC S P a < Om (1 + 1) := psi_lt (InR_Om_succ 1) _

end Googology.Trans.PoR.InaccPsi.R2.Zi

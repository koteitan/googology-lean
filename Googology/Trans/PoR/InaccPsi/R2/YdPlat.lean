import Googology.Trans.PoR.InaccPsi.R2.XmPlat
import Googology.Trans.PoR.InaccPsi.R2.LeEDig

/-!
# The plateau at the level `Ω₂`: `ψ₂(W^{X+Ω₂}) = sup_m e_m`

`W^x = leWe x = ω^{Ω₂·x}`, `e_0 = 0`, `e_{m+1} = ψ₂(W^{X+e_m})` (`ydE`), `E_X = ψ₂(W^{X+Ω₂})`.  The shift `X` is any
ordinal that lies in every closure (`hX`; e.g. `X = Ω_{k+3}`).

* `ydE_lt_succ` (the `e_m` increase strictly), `ydOwn` (**`e < e_m ⇒ e < ψ₂(W^{X+e})`**);
* `ydR3` (**a member of the stage `Cl(W^{X+e_k}, e_{k+1})` below `W^{X+Ω₂}` is below `W^{X+e_{k+1}}`**: its last
  exponent is `Ω₂·X + Ω₂·q + r` with `q` a member below `Ω₂`, so `q < e_{k+1}`), `ydKey` (every member of
  `Cl(W^{X+Ω₂}, sup_m e_m)` lies in a stage), `ydPlat` (**THE PLATEAU** `ψ₂(W^{X+Ω₂}) ≤ sup_m e_m`), `ydTop_eq`;
* `ydOwn_iff` (**for EVERY ordinal `e`: `(∀ e' ≤ e, e' < ψ₂(W^{X+e'})) ⇔ e < E_X`**).

No new axiom.  New definition: `ydE` (the iterates; auxiliary).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Mx

variable {S : InaccSeq.{0}}

/-- The iterates `e_0 = 0`, `e_{m+1} = ψ₂(W^{X+e_m})`. -/
noncomputable def ydE (S : InaccSeq.{0}) (X : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => 0
  | m + 1 => S.psi (leWe (X + ydE S X m)) (Om (1 + 1))

theorem ydE_zero (X : Ordinal.{0}) : ydE S X 0 = 0 := rfl

theorem ydE_succ (X : Ordinal.{0}) (m : ℕ) : ydE S X (m + 1) = S.psi (leWe (X + ydE S X m)) (Om (1 + 1)) := rfl

theorem ydE_lt_Om2 (X : Ordinal.{0}) : ∀ m, ydE S X m < Om (1 + 1)
  | 0 => ldOm2_SC.1
  | m + 1 => by rw [ydE_succ]; exact psi_lt (InR_Om_succ 1) _

theorem ydE_SC (X : Ordinal.{0}) (m : ℕ) : SC (ydE S X (m + 1)) := by
  rw [ydE_succ]; exact SC_psi (InR_Om_succ 1) _

/-- The top `E_X = ψ₂(W^{X+Ω₂})`. -/
theorem ydE_le_top (X : Ordinal.{0}) : ∀ m, ydE S X m ≤ S.psi (leWe (X + Om (1 + 1))) (Om (1 + 1))
  | 0 => by rw [ydE_zero]; exact zero_le
  | m + 1 => by
    rw [ydE_succ]
    exact (psi_mono (InR_Om_succ 1) (leWe_mono ((add_le_add_iff_left X).2 (ydE_lt_Om2 X m).le))).1

theorem ydE_bdd (X : Ordinal.{0}) : BddAbove (range (ydE S X)) :=
  ⟨Om (1 + 1), by rintro _ ⟨m, rfl⟩; exact (ydE_lt_Om2 X m).le⟩

section Gen

variable {X : Ordinal.{0}} (hX : ∀ a b : Ordinal.{0}, X ∈ S.CSet a b)
include hX

/-- **The iterates increase strictly.** -/
theorem ydE_lt_succ : ∀ m, ydE S X m < ydE S X (m + 1)
  | 0 => by rw [ydE_zero]; exact (ydE_SC X 0).1
  | m + 1 => by
    have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
    have ih := ydE_lt_succ m
    rw [ydE_succ X (m + 1)]
    conv_lhs => rw [ydE_succ]
    refine psi_lt_psi_of_mem hκ2 (leWe_lt ((add_lt_add_iff_left X).2 ih)) ?_
    refine leWe_mem (CSet.add_mem (hX _ _) (CSet.of_lt ?_))
    calc ydE S X m < ydE S X (m + 1) := ih
      _ = S.psi (leWe (X + ydE S X m)) (Om (1 + 1)) := ydE_succ X m
      _ ≤ S.psi (leWe (X + ydE S X (m + 1))) (Om (1 + 1)) :=
        (psi_mono hκ2 (leWe_mono ((add_le_add_iff_left X).2 ih.le))).1

theorem ydE_mono : Monotone (ydE S X) :=
  monotone_nat_of_le_succ fun m => (ydE_lt_succ hX m).le

omit hX in
/-- **`e < e_m ⇒ e < ψ₂(W^{X+e})`** (the own clause below every iterate). -/
theorem ydOwn : ∀ m, ∀ e, e < ydE S X m → e < S.psi (leWe (X + e)) (Om (1 + 1))
  | 0, e, h => by rw [ydE_zero] at h; exact absurd h (not_lt.2 zero_le)
  | m + 1, e, h => by
    rcases lt_or_ge e (ydE S X m) with h' | h'
    · exact ydOwn m e h'
    · rw [ydE_succ] at h
      exact h.trans_le (psi_mono (InR_Om_succ 1) (leWe_mono ((add_le_add_iff_left X).2 h'))).1

/-- The stage `Cl(W^{X+e_k}, e_{k+1})` grows with `k`. -/
theorem ydStage_mono {i j : ℕ} (h : i ≤ j) :
    S.CSet (leWe (X + ydE S X i)) (ydE S X (i + 1)) ⊆ S.CSet (leWe (X + ydE S X j)) (ydE S X (j + 1)) := by
  rw [ydE_succ, ydE_succ]
  exact (psi_mono (InR_Om_succ 1) (leWe_mono ((add_le_add_iff_left X).2 (ydE_mono hX h)))).2

/-- **A member of the stage below `W^{X+Ω₂}` is below `W^{X+e_{k+1}}`.** -/
theorem ydR3 (k : ℕ) {y : Ordinal.{0}} (hy : y ∈ S.CSet (leWe (X + ydE S X k)) (ydE S X (k + 1)))
    (hlt : y < leWe (X + Om (1 + 1))) : y < leWe (X + ydE S X (k + 1)) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hΩ0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hεΩ : ω ^ Om (1 + 1 : Ordinal.{0}) = Om (1 + 1) := gg_SC_eps ldOm2_SC
  set a := leWe (X + ydE S X k) with ha
  set E := ydE S X (k + 1) with hEdef
  have hEeq : E = S.psi a (Om (1 + 1)) := ydE_succ X k
  have hESC : SC E := ydE_SC X k
  rcases eq_or_ne y 0 with rfl | hy0
  · exact opow_pos _ omega0_pos
  set L := log ω y with hLdef
  have hLmem : L ∈ S.CSet a E := leLog_mem hy
  have hlt' : y < ω ^ (Om (1 + 1) * (X + Om (1 + 1))) := hlt
  have hLlt : L < Om (1 + 1) * X + Om (1 + 1) * Om (1 + 1) := by
    have := (lt_opow_iff_log_lt one_lt_omega0 hy0).1 hlt'
    rwa [mul_add] at this
  unfold leWe
  refine (lt_opow_iff_log_lt one_lt_omega0 hy0).2 ?_
  rw [mul_add]
  rcases lt_or_ge L (Om (1 + 1) * X) with h1 | h1
  · exact h1.trans_le le_self_add
  · have hsub : L - Om (1 + 1) * X < Om (1 + 1) * Om (1 + 1) := Ry.rySub_lt h1 hLlt
    set q := (L - Om (1 + 1) * X) / Om (1 + 1) with hq
    have hXm : Om (1 + 1) * X ∈ S.CSet a E := ldMulK_mem ldOm2_SC (mxOm2_mem _ _) (hX _ _)
    have hsm : L - Om (1 + 1) * X ∈ S.CSet a E := Ta.taSub_mem L hLmem _
    have hqC : q ∈ S.CSet a E := by
      have h := (Vh.vhC_div _ hsm (Om (1 + 1))).2.2 (mxOm2_mem _ _)
      rwa [hεΩ] at h
    have hq2 : q < Om (1 + 1) := (Ordinal.lt_mul_iff_div_lt hΩ0).1 hsub
    have hqE : q < E := by rw [hEeq] at hqC ⊢; exact lt_psi_of_mem hκ2 hqC hq2
    have hq1 : q + 1 ≤ E := Order.add_one_le_of_lt hqE
    have hlm : L - Om (1 + 1) * X < Om (1 + 1) * (q + 1) := by
      have := Ordinal.lt_mul_succ_div (L - Om (1 + 1) * X) hΩ0
      rwa [Order.succ_eq_add_one] at this
    have e1 : L = Om (1 + 1) * X + (L - Om (1 + 1) * X) := (Ordinal.add_sub_cancel_of_le h1).symm
    show L < _
    rw [e1]
    exact (add_lt_add_iff_left _).2 (hlm.trans_le (mul_le_mul_right hq1 _))

/-- **Every member of `Cl(W^{X+Ω₂}, sup_m e_m)` lies in a stage.** -/
theorem ydKey : ∀ y ∈ S.CSet (leWe (X + Om (1 + 1))) (⨆ m : ℕ, ydE S X m),
    ∃ k, y ∈ S.CSet (leWe (X + ydE S X k)) (ydE S X (k + 1)) := by
  intro y hy
  induction hy with
  | small h =>
    obtain ⟨n, hn⟩ := (lt_ciSup_iff (ydE_bdd X)).1 h
    exact ⟨n, CSet.of_lt (hn.trans (ydE_lt_succ hX n))⟩
  | zero => exact ⟨0, CSet.zero_mem _ _⟩
  | inacc n => exact ⟨0, Clos.inacc n⟩
  | inaccW => exact ⟨0, Clos.inaccW⟩
  | add _ _ ihp ihq =>
    obtain ⟨i, hi⟩ := ihp
    obtain ⟨j, hj⟩ := ihq
    exact ⟨max i j, CSet.add_mem (ydStage_mono hX (le_max_left i j) hi) (ydStage_mono hX (le_max_right i j) hj)⟩
  | phi _ _ ihp ihq =>
    obtain ⟨i, hi⟩ := ihp
    obtain ⟨j, hj⟩ := ihq
    exact ⟨max i j, Clos.phi (ydStage_mono hX (le_max_left i j) hi) (ydStage_mono hX (le_max_right i j) hj)⟩
  | om _ ih =>
    obtain ⟨i, hi⟩ := ih
    exact ⟨i, CSet.Om_mem hi⟩
  | @coll π e hπ _ _ ihπ ihe =>
    obtain ⟨i, hi⟩ := ihπ
    obtain ⟨k, hk⟩ := ihe
    have hlt : e.1 < leWe (X + ydE S X (k + 1)) := ydR3 hX k hk e.2
    set N := max (k + 1) i with hN
    have hltN : e.1 < leWe (X + ydE S X N) :=
      hlt.trans_le (leWe_mono ((add_le_add_iff_left X).2 (ydE_mono hX (le_max_left (k + 1) i))))
    have heN := ydStage_mono hX ((Nat.le_succ k).trans (le_max_left (k + 1) i)) hk
    have hπN := ydStage_mono hX (le_max_right (k + 1) i) hi
    exact ⟨N, Clos.coll (e := ⟨e.1, hltN⟩) hπ hπN heN⟩

/-- **THE PLATEAU**: `ψ₂(W^{X+Ω₂}) ≤ sup_m e_m`. -/
theorem ydPlat : S.psi (leWe (X + Om (1 + 1))) (Om (1 + 1)) ≤ ⨆ m : ℕ, ydE S X m := by
  refine psi_le_of_good (mxOm2_mem _ _) fun y hy hy2 => ?_
  obtain ⟨n, hn⟩ := ydKey hX y hy
  rw [ydE_succ] at hn
  have h := lt_psi_of_mem (InR_Om_succ 1) hn hy2
  rw [← ydE_succ] at h
  exact h.trans_le (le_ciSup (ydE_bdd X) (n + 1))

theorem ydTop_eq : S.psi (leWe (X + Om (1 + 1))) (Om (1 + 1)) = ⨆ m : ℕ, ydE S X m :=
  le_antisymm (ydPlat hX) (ciSup_le (ydE_le_top X))

/-- Below the top some iterate is above. -/
theorem ydLt_top {e : Ordinal.{0}} (he : e < S.psi (leWe (X + Om (1 + 1))) (Om (1 + 1))) :
    ∃ m, e < ydE S X m := by
  rw [ydTop_eq hX] at he
  exact (lt_ciSup_iff (ydE_bdd X)).1 he

omit hX in
/-- **The own clause fails at the top**: `ψ₂(W^{X+E_X}) ≤ E_X`. -/
theorem ydTop_fail :
    S.psi (leWe (X + S.psi (leWe (X + Om (1 + 1))) (Om (1 + 1)))) (Om (1 + 1)) ≤
      S.psi (leWe (X + Om (1 + 1))) (Om (1 + 1)) :=
  (psi_mono (InR_Om_succ 1) (leWe_mono ((add_le_add_iff_left X).2 (psi_lt (InR_Om_succ 1) _).le))).1

/-- **For every ordinal `e`: `(∀ e' ≤ e, e' < ψ₂(W^{X+e'})) ⇔ e < E_X`.** -/
theorem ydOwn_iff (e : Ordinal.{0}) :
    (∀ e', e' ≤ e → e' < S.psi (leWe (X + e')) (Om (1 + 1))) ↔
      e < S.psi (leWe (X + Om (1 + 1))) (Om (1 + 1)) := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    exact absurd ((h _ hc).trans_le ydTop_fail) (lt_irrefl _)
  · intro he e' he'
    obtain ⟨m, hm⟩ := ydLt_top hX (he'.trans_lt he)
    exact ydOwn m e' hm

end Gen

end Googology.Trans.PoR.InaccPsi.R2.Yd

#print axioms Googology.Trans.PoR.InaccPsi.R2.Yd.ydE_lt_succ
#print axioms Googology.Trans.PoR.InaccPsi.R2.Yd.ydOwn
#print axioms Googology.Trans.PoR.InaccPsi.R2.Yd.ydR3
#print axioms Googology.Trans.PoR.InaccPsi.R2.Yd.ydKey
#print axioms Googology.Trans.PoR.InaccPsi.R2.Yd.ydPlat
#print axioms Googology.Trans.PoR.InaccPsi.R2.Yd.ydTop_eq
#print axioms Googology.Trans.PoR.InaccPsi.R2.Yd.ydOwn_iff

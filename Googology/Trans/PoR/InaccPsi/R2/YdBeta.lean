import Googology.Trans.PoR.InaccPsi.R2.YdBase
import Googology.Trans.PoR.InaccPsi.R2.UgB

/-!
# The plateau over a normal base `β`, and its move under `B_n`

`W^x = leWe x`, `e^β_0 = 0`, `e^β_{m+1} = ψ₂(β + W^{X+e^β_m})` (`ydEB`), `E^β_X = ψ₂(β + W^{X+Ω₂})`; `β` normal at the
level `Ω₂` (`β ∈ Cl(β, ψ₂ β)`, hence `β ∈ Cl(β + d, ψ₂(β + d))` for every `d`), `X` in every closure.

* `ydR3c` (**a member of `Cl(a, ψ₂ a)` below `W^{X+Ω₂}` is below `W^{X+ψ₂ a}`**, any `a`), `ydR3B`, `ydKeyB`,
  `ydPlatB` (**`ψ₂(β + W^{X+Ω₂}) = sup_m e^β_m`**), `ydOwnB_iff` (**for every ordinal `e`:
  `(∀ e' ≤ e, e' < ψ₂(β + W^{X+e'})) ⇔ e < E^β_X`**);
* `ydNormB` (**`B_n β` is normal** when `β` is, `Ug.ugB_fix`), `ydFixB` (**`B_n e^β_m = e^{B_n β}_m`**),
  `ydOwnMoveB` (**THE OWN CLAUSE MOVES**: `MvD β`, `β` normal, `MvD e`, `e < E^β_X` ⇒ every ORDINAL `e'' ≤ B_n e` has
  `e'' < ψ₂(B_n β + W^{X+e''})`; no inverse correspondence).

No new axiom.  New definition: `ydEB` (the iterates over `β`; auxiliary).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Mv

variable {S : InaccSeq.{0}}

/-- The iterates over `β`: `e^β_0 = 0`, `e^β_{m+1} = ψ₂(β + W^{X+e^β_m})`. -/
noncomputable def ydEB (S : InaccSeq.{0}) (X β : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => 0
  | m + 1 => S.psi (β + leWe (X + ydEB S X β m)) (Om (1 + 1))

theorem ydEB_zero (X β : Ordinal.{0}) : ydEB S X β 0 = 0 := rfl

theorem ydEB_succ (X β : Ordinal.{0}) (m : ℕ) :
    ydEB S X β (m + 1) = S.psi (β + leWe (X + ydEB S X β m)) (Om (1 + 1)) := rfl

theorem ydEB_lt_Om2 (X β : Ordinal.{0}) : ∀ m, ydEB S X β m < Om (1 + 1)
  | 0 => ldOm2_SC.1
  | m + 1 => by rw [ydEB_succ]; exact psi_lt (InR_Om_succ 1) _

theorem ydEB_SC (X β : Ordinal.{0}) (m : ℕ) : SC (ydEB S X β (m + 1)) := by
  rw [ydEB_succ]; exact SC_psi (InR_Om_succ 1) _

theorem ydEB_le_top (X β : Ordinal.{0}) :
    ∀ m, ydEB S X β m ≤ S.psi (β + leWe (X + Om (1 + 1))) (Om (1 + 1))
  | 0 => by rw [ydEB_zero]; exact zero_le
  | m + 1 => by
    rw [ydEB_succ]
    exact (psi_mono (InR_Om_succ 1)
      (add_le_add_right (leWe_mono ((add_le_add_iff_left X).2 (ydEB_lt_Om2 X β m).le)) β)).1

theorem ydEB_bdd (X β : Ordinal.{0}) : BddAbove (range (ydEB S X β)) :=
  ⟨Om (1 + 1), by rintro _ ⟨m, rfl⟩; exact (ydEB_lt_Om2 X β m).le⟩

/-- **`e < e^β_m ⇒ e < ψ₂(β + W^{X+e})`.** -/
theorem ydOwnB (X β : Ordinal.{0}) : ∀ m, ∀ e, e < ydEB S X β m → e < S.psi (β + leWe (X + e)) (Om (1 + 1))
  | 0, e, h => by rw [ydEB_zero] at h; exact absurd h (not_lt.2 zero_le)
  | m + 1, e, h => by
    rcases lt_or_ge e (ydEB S X β m) with h' | h'
    · exact ydOwnB X β m e h'
    · rw [ydEB_succ] at h
      exact h.trans_le (psi_mono (InR_Om_succ 1)
        (add_le_add_right (leWe_mono ((add_le_add_iff_left X).2 h')) β)).1

/-- **The own clause fails at the top**: `ψ₂(β + W^{X+E^β_X}) ≤ E^β_X`. -/
theorem ydTopFailB (X β : Ordinal.{0}) :
    S.psi (β + leWe (X + S.psi (β + leWe (X + Om (1 + 1))) (Om (1 + 1)))) (Om (1 + 1)) ≤
      S.psi (β + leWe (X + Om (1 + 1))) (Om (1 + 1)) :=
  (psi_mono (InR_Om_succ 1)
    (add_le_add_right (leWe_mono ((add_le_add_iff_left X).2 (psi_lt (InR_Om_succ 1) _).le)) β)).1

section Gen

variable {X : Ordinal.{0}} (hX : ∀ a b : Ordinal.{0}, X ∈ S.CSet a b)
include hX

/-- **A member of `Cl(a, ψ₂ a)` below `W^{X+Ω₂}` is below `W^{X+ψ₂ a}`** (any `a`). -/
theorem ydR3c (a : Ordinal.{0}) {y : Ordinal.{0}} (hy : y ∈ S.CSet a (S.psi a (Om (1 + 1))))
    (hlt : y < leWe (X + Om (1 + 1))) : y < leWe (X + S.psi a (Om (1 + 1))) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hΩ0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hεΩ : ω ^ Om (1 + 1 : Ordinal.{0}) = Om (1 + 1) := gg_SC_eps ldOm2_SC
  set E := S.psi a (Om (1 + 1)) with hEdef
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
    have hsm : L - Om (1 + 1) * X ∈ S.CSet a E := Ta.taSub_mem L hLmem _
    have hqC : q ∈ S.CSet a E := by
      have h := (Vh.vhC_div _ hsm (Om (1 + 1))).2.2 (mxOm2_mem _ _)
      rwa [hεΩ] at h
    have hq2 : q < Om (1 + 1) := (Ordinal.lt_mul_iff_div_lt hΩ0).1 hsub
    have hqE : q < E := lt_psi_of_mem hκ2 hqC hq2
    have hq1 : q + 1 ≤ E := Order.add_one_le_of_lt hqE
    have hlm : L - Om (1 + 1) * X < Om (1 + 1) * (q + 1) := by
      have := Ordinal.lt_mul_succ_div (L - Om (1 + 1) * X) hΩ0
      rwa [Order.succ_eq_add_one] at this
    have e1 : L = Om (1 + 1) * X + (L - Om (1 + 1) * X) := (Ordinal.add_sub_cancel_of_le h1).symm
    show L < _
    rw [e1]
    exact (add_lt_add_iff_left _).2 (hlm.trans_le (mul_le_mul_right hq1 _))

variable {β : Ordinal.{0}} (hβ : β ∈ S.CSet β (S.psi β (Om (1 + 1))))
include hβ

theorem ydNormD (d : Ordinal.{0}) : β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))) :=
  (psi_mono (InR_Om_succ 1) le_self_add).2 hβ

/-- The iterates over `β` increase strictly. -/
theorem ydEB_lt_succ : ∀ m, ydEB S X β m < ydEB S X β (m + 1)
  | 0 => by rw [ydEB_zero]; exact (ydEB_SC X β 0).1
  | m + 1 => by
    have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
    have ih := ydEB_lt_succ m
    rw [ydEB_succ X β (m + 1)]
    conv_lhs => rw [ydEB_succ]
    refine psi_lt_psi_of_mem hκ2 ((add_lt_add_iff_left β).2 (leWe_lt ((add_lt_add_iff_left X).2 ih))) ?_
    refine CSet.add_mem (ydNormD hX hβ _) (leWe_mem (CSet.add_mem (hX _ _) (CSet.of_lt ?_)))
    calc ydEB S X β m < ydEB S X β (m + 1) := ih
      _ = S.psi (β + leWe (X + ydEB S X β m)) (Om (1 + 1)) := ydEB_succ X β m
      _ ≤ S.psi (β + leWe (X + ydEB S X β (m + 1))) (Om (1 + 1)) :=
        (psi_mono hκ2 (add_le_add_right (leWe_mono ((add_le_add_iff_left X).2 ih.le)) β)).1

theorem ydEB_mono : Monotone (ydEB S X β) :=
  monotone_nat_of_le_succ fun m => (ydEB_lt_succ hX hβ m).le

theorem ydStageB_mono {i j : ℕ} (h : i ≤ j) :
    S.CSet (β + leWe (X + ydEB S X β i)) (ydEB S X β (i + 1)) ⊆
      S.CSet (β + leWe (X + ydEB S X β j)) (ydEB S X β (j + 1)) := by
  rw [ydEB_succ, ydEB_succ]
  exact (psi_mono (InR_Om_succ 1)
    (add_le_add_right (leWe_mono ((add_le_add_iff_left X).2 (ydEB_mono hX hβ h))) β)).2

/-- **A member of the stage below `β + W^{X+Ω₂}` is below `β + W^{X+e^β_{k+1}}`.** -/
theorem ydR3B (k : ℕ) {y : Ordinal.{0}} (hy : y ∈ S.CSet (β + leWe (X + ydEB S X β k)) (ydEB S X β (k + 1)))
    (hlt : y < β + leWe (X + Om (1 + 1))) : y < β + leWe (X + ydEB S X β (k + 1)) := by
  rcases lt_or_ge y β with h1 | h1
  · exact h1.trans_le le_self_add
  · rw [ydEB_succ] at hy ⊢
    have hz : y - β ∈ S.CSet (β + leWe (X + ydEB S X β k))
        (S.psi (β + leWe (X + ydEB S X β k)) (Om (1 + 1))) := Ta.taSub_mem y hy β
    have hzl : y - β < leWe (X + Om (1 + 1)) := Ry.rySub_lt h1 hlt
    have h := ydR3c hX _ hz hzl
    have e1 : y = β + (y - β) := (Ordinal.add_sub_cancel_of_le h1).symm
    rw [e1]
    exact (add_lt_add_iff_left β).2 h

/-- **Every member of `Cl(β + W^{X+Ω₂}, sup_m e^β_m)` lies in a stage.** -/
theorem ydKeyB : ∀ y ∈ S.CSet (β + leWe (X + Om (1 + 1))) (⨆ m : ℕ, ydEB S X β m),
    ∃ k, y ∈ S.CSet (β + leWe (X + ydEB S X β k)) (ydEB S X β (k + 1)) := by
  intro y hy
  induction hy with
  | small h =>
    obtain ⟨n, hn⟩ := (lt_ciSup_iff (ydEB_bdd X β)).1 h
    exact ⟨n, CSet.of_lt (hn.trans (ydEB_lt_succ hX hβ n))⟩
  | zero => exact ⟨0, CSet.zero_mem _ _⟩
  | inacc n => exact ⟨0, Clos.inacc n⟩
  | inaccW => exact ⟨0, Clos.inaccW⟩
  | add _ _ ihp ihq =>
    obtain ⟨i, hi⟩ := ihp
    obtain ⟨j, hj⟩ := ihq
    exact ⟨max i j, CSet.add_mem (ydStageB_mono hX hβ (le_max_left i j) hi)
      (ydStageB_mono hX hβ (le_max_right i j) hj)⟩
  | phi _ _ ihp ihq =>
    obtain ⟨i, hi⟩ := ihp
    obtain ⟨j, hj⟩ := ihq
    exact ⟨max i j, Clos.phi (ydStageB_mono hX hβ (le_max_left i j) hi)
      (ydStageB_mono hX hβ (le_max_right i j) hj)⟩
  | om _ ih =>
    obtain ⟨i, hi⟩ := ih
    exact ⟨i, CSet.Om_mem hi⟩
  | @coll π e hπ _ _ ihπ ihe =>
    obtain ⟨i, hi⟩ := ihπ
    obtain ⟨k, hk⟩ := ihe
    have hlt : e.1 < β + leWe (X + ydEB S X β (k + 1)) := ydR3B hX hβ k hk e.2
    set N := max (k + 1) i with hN
    have hltN : e.1 < β + leWe (X + ydEB S X β N) :=
      hlt.trans_le (add_le_add_right (leWe_mono ((add_le_add_iff_left X).2
        (ydEB_mono hX hβ (le_max_left (k + 1) i)))) β)
    have heN := ydStageB_mono hX hβ ((Nat.le_succ k).trans (le_max_left (k + 1) i)) hk
    have hπN := ydStageB_mono hX hβ (le_max_right (k + 1) i) hi
    exact ⟨N, Clos.coll (e := ⟨e.1, hltN⟩) hπ hπN heN⟩

/-- **THE PLATEAU OVER `β`**: `ψ₂(β + W^{X+Ω₂}) = sup_m e^β_m`. -/
theorem ydTopB_eq : S.psi (β + leWe (X + Om (1 + 1))) (Om (1 + 1)) = ⨆ m : ℕ, ydEB S X β m := by
  refine le_antisymm (psi_le_of_good (mxOm2_mem _ _) fun y hy hy2 => ?_) (ciSup_le (ydEB_le_top X β))
  obtain ⟨n, hn⟩ := ydKeyB hX hβ y hy
  rw [ydEB_succ] at hn
  have h := lt_psi_of_mem (InR_Om_succ 1) hn hy2
  rw [← ydEB_succ] at h
  exact h.trans_le (le_ciSup (ydEB_bdd X β) (n + 1))

theorem ydLtTopB {e : Ordinal.{0}} (he : e < S.psi (β + leWe (X + Om (1 + 1))) (Om (1 + 1))) :
    ∃ m, e < ydEB S X β m := by
  rw [ydTopB_eq hX hβ] at he
  exact (lt_ciSup_iff (ydEB_bdd X β)).1 he

/-- **For every ordinal `e`: `(∀ e' ≤ e, e' < ψ₂(β + W^{X+e'})) ⇔ e < E^β_X`.** -/
theorem ydOwnB_iff (e : Ordinal.{0}) :
    (∀ e', e' ≤ e → e' < S.psi (β + leWe (X + e')) (Om (1 + 1))) ↔
      e < S.psi (β + leWe (X + Om (1 + 1))) (Om (1 + 1)) := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    exact absurd ((h _ hc).trans_le (ydTopFailB X β)) (lt_irrefl _)
  · intro he e' he'
    obtain ⟨m, hm⟩ := ydLtTopB hX hβ (he'.trans_lt he)
    exact ydOwnB X β m e' hm

end Gen

/-! ## The move -/

/-- **`B_n` keeps normality at the level `Ω₂`.** -/
theorem ydNormB (n : ℕ) {β : Ordinal.{0}} (hDβ : MvD S β) (hβ : β ∈ S.CSet β (S.psi β (Om (1 + 1)))) :
    Bc.bcB S n β ∈ S.CSet (Bc.bcB S n β) (S.psi (Bc.bcB S n β) (Om (1 + 1))) := by
  have h1c : (1 : Ordinal.{0}) < Bc.bcC S n := Bt.one_lt_SC (Lw.lw_L_SC S _)
  exact (Ug.ugB_fix (n := n) one_ne_zero Rk.rk_one_D (Bc.bcB_fix' S n 1 h1c) hDβ hβ).2.2

/-- **`B_n e^β_m = e^{B_n β}_m`** (`X = Ω_{k+3}`, `β` normal in the domain). -/
theorem ydFixB (k n : ℕ) {β : Ordinal.{0}} (hDβ : MvD S β) (hβ : β ∈ S.CSet β (S.psi β (Om (1 + 1)))) :
    ∀ m, MvD S (ydEB S (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) β m) ∧
      Bc.bcB S n (ydEB S (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) β m) =
        ydEB S (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Bc.bcB S n β) m
  | 0 => by
    rw [ydEB_zero, ydEB_zero]
    have hc : (0 : Ordinal.{0}) < Bc.bcC S n := (Lw.lw_L_SC S _).1
    exact ⟨mvD_of_lt (Lw.lw_L_SC S ω).1, Bc.bcB_fix' S n 0 hc⟩
  | m + 1 => by
    set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
    obtain ⟨hDm, hBm⟩ := ydFixB k n hDβ hβ m
    have hX0 : X ≠ 0 := (Om_pos (add_pos_of_right zero_lt_one _).ne').ne'
    set P : Ordinal.{0} → Prop := fun x => x = 0 ∨ (x = ydEB S X β m ∧ SC x) with hP
    have hPD : ∀ x, P x → MvD S x := by
      rintro x (rfl | ⟨rfl, -⟩)
      · exact mvD_of_lt (Lw.lw_L_SC S ω).1
      · exact hDm
    have hPdec : ∀ x, P x → x ≠ 0 → P (log ω x) ∧ P (x - ω ^ log ω x) := by
      rintro x (rfl | ⟨hx, hxS⟩) hx0
      · exact absurd rfl hx0
      · have hl : log ω x = x := by
          conv_lhs => rw [← gg_SC_eps hxS]
          exact log_opow one_lt_omega0 x
        rw [hl, gg_SC_eps hxS, Ordinal.sub_self]
        exact ⟨Or.inr ⟨hx, hxS⟩, Or.inl rfl⟩
    have hPW : ∀ x, P x → x < Om (1 + 1) := by
      rintro x (rfl | ⟨rfl, -⟩)
      · exact ldOm2_SC.1
      · exact ydEB_lt_Om2 X β m
    have hPm : P (ydEB S X β m) := by
      cases m with
      | zero => exact Or.inl rfl
      | succ j => exact Or.inr ⟨rfl, ydEB_SC X β j⟩
    obtain ⟨hDW, hBW, -, -⟩ := Ro.roB_We (n := n) hX0 (Xv.xvShB (S := S) k) P hPD hPdec hPW hPm hPm
    rw [hBm] at hBW
    obtain ⟨hDa, hBa⟩ := mvB_add (k := n) hDβ hDW
    rw [hBW] at hBa
    have hown : β + leWe (X + ydEB S X β m) ∈ S.CSet (β + leWe (X + ydEB S X β m))
        (S.psi (β + leWe (X + ydEB S X β m)) (Om (1 + 1))) := by
      refine CSet.add_mem (ydNormD (ydX_mem k) hβ _) (leWe_mem (CSet.add_mem (Vn.vnOmK3_mem k _ _) (CSet.of_lt ?_)))
      rw [← ydEB_succ]; exact ydEB_lt_succ (ydX_mem k) hβ m
    obtain ⟨hDs, hBs⟩ := mxB_atom (n := n) hDa hown
    rw [hBa] at hBs
    rw [ydEB_succ, ydEB_succ]
    exact ⟨hDs, hBs⟩

/-- **THE OWN CLAUSE MOVES**: for `β` normal in the domain and `e ∈ MvD` below `E^β_X`, every ordinal
`e'' ≤ B_n e` has `e'' < ψ₂(B_n β + W^{X+e''})`, and `B_n e < E^{B_n β}_X`. -/
theorem ydOwnMoveB (k n : ℕ) {β e : Ordinal.{0}} (hDβ : MvD S β) (hβ : β ∈ S.CSet β (S.psi β (Om (1 + 1))))
    (hDe : MvD S e)
    (he : e < S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Om (1 + 1))) (Om (1 + 1))) :
    Bc.bcB S n e <
        S.psi (Bc.bcB S n β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Om (1 + 1))) (Om (1 + 1)) ∧
      ∀ e'', e'' ≤ Bc.bcB S n e →
        e'' < S.psi (Bc.bcB S n β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e'')) (Om (1 + 1)) := by
  have hXm : ∀ a b : Ordinal.{0}, Om ((k : Ordinal.{0}) + 1 + 1 + 1) ∈ S.CSet a b :=
    fun a b => Vn.vnOmK3_mem k a b
  obtain ⟨m, hm⟩ := ydLtTopB hXm hβ he
  obtain ⟨hDm, hBm⟩ := ydFixB k n hDβ hβ m
  have h := (mvB_lt_iff (k := n) hDe hDm).2 hm
  rw [hBm] at h
  have hB' : Bc.bcB S n e < S.psi (Bc.bcB S n β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Om (1 + 1)))
      (Om (1 + 1)) := h.trans_le (ydEB_le_top _ _ m)
  exact ⟨hB', (ydOwnB_iff hXm (ydNormB n hDβ hβ) _).2 hB'⟩

end Googology.Trans.PoR.InaccPsi.R2.Yd

#print axioms Googology.Trans.PoR.InaccPsi.R2.Yd.ydR3c
#print axioms Googology.Trans.PoR.InaccPsi.R2.Yd.ydKeyB
#print axioms Googology.Trans.PoR.InaccPsi.R2.Yd.ydTopB_eq
#print axioms Googology.Trans.PoR.InaccPsi.R2.Yd.ydOwnB_iff
#print axioms Googology.Trans.PoR.InaccPsi.R2.Yd.ydNormB
#print axioms Googology.Trans.PoR.InaccPsi.R2.Yd.ydFixB
#print axioms Googology.Trans.PoR.InaccPsi.R2.Yd.ydOwnMoveB

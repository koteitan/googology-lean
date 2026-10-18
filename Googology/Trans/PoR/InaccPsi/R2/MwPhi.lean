import Googology.Trans.PoR.InaccPsi.R2.MvLh
import Googology.Trans.PoR.InaccPsi.R2.PhLev

/-!
# `B_n` commutes with the binary Veblen function on its normal-form domain

`B_n = Bc.bcB S n = val ∘ σ ∘ nf`, `MvD S x` its normal-form domain (`R2.MvDom`), `φ = veblen`,
`P_m` the range of `φ_m` (`R2.VzP`).

* `mwB_phi` (**`B_n(φ(a, b)) = φ(B_n a, B_n b)`** for `a, b ∈ MvD` with `a, b < φ(a, b)`, and `φ(a, b) ∈ MvD`):
  the normal form of `φ(a, b)` is `phi (nf a) (nf b)` (the other shapes contradict `a, b < φ(a, b)`);
* `mwB_nat` (`B_n` fixes the natural numbers), `mwB_veblen_nat` (**`B_n(φ_m(y)) = φ_m(B_n y)`** for `m < y`,
  `φ_m(y) ≠ y`);
* `mwB_fix` (**`φ_m(y) = y` gives `φ_m(B_n y) = B_n y`**: the normal form of `y` is `phi c d` with `m < c`,
  or strongly critical), `mwB_vzP_iff` (**`y ∈ P_{m+1} ⇔ B_n y ∈ P_{m+1}`** when `m < y` and `φ_m(y) ∈ MvD`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Mw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Bc Googology.Trans.PoR.InaccPsi.R2.Mv

variable {S : InaccSeq.{0}}

theorem mw_veblen_indec (a b : Ordinal.{0}) : Indec (veblen a b) :=
  indec_iff.2 ⟨veblen_pos.ne', Ph.ph_veblen_prin a b⟩

/-- **`B_n(φ(a, b)) = φ(B_n a, B_n b)`** for `a, b ∈ MvD` with `a, b < φ(a, b)`. -/
theorem mwB_phi {k : ℕ} {a b : Ordinal.{0}} (ha : MvD S a) (hb : MvD S b)
    (hab : a < veblen a b) (hbb : b < veblen a b) :
    MvD S (veblen a b) ∧ bcB S k (veblen a b) = veblen (bcB S k a) (bcB S k b) := by
  have hmem : veblen a b ∈ ⋃ c, S.CSet c 0 := by
    have := exists_mem_CSet S (phi (bcNf S a) (bcNf S b))
    simp only [val, mvD_val ha, mvD_val hb] at this
    exact Set.mem_iUnion.2 this
  obtain ⟨hN, hv⟩ := bcNf_spec S hmem
  have hP : (bcNf S (veblen a b)).isPrin = true :=
    isPrin_of_indec hN (by rw [hv]; exact mw_veblen_indec a b)
  have key : ∀ t : Term, NF t → val S t = veblen a b → t.isPrin = true →
      t = phi (bcNf S a) (bcNf S b) := by
    intro t hN hv hP
    cases t with
    | zero => simp [isPrin, isSC] at hP
    | add _ _ => simp [isPrin, isSC] at hP
    | phi c d =>
      have hdlt : val S d < val S (phi c d) := (cmp_lt_iff S hN.2.1 hN).1 hN.2.2.2
      have hv' : veblen (val S c) (val S d) = veblen a b := hv
      rcases veblen_eq_veblen_iff.1 hv' with ⟨h1, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩
      · have hc : bcNf S a = c := by rw [← h1]; exact bcNf_val S hN.1
        have hd : bcNf S b = d := by rw [← h2]; exact bcNf_val S hN.2.1
        rw [hc, hd]
      · exfalso
        have : val S d = val S (phi c d) := by rw [h2]; exact hv.symm
        exact absurd this hdlt.ne
      · exfalso
        have : veblen a b = b := by rw [← hv', h2]
        exact absurd this hbb.ne'
    | _ =>
      exfalso
      have hsc := SC_val S hN (by simpa [isPrin] using hP)
      rw [hv] at hsc
      exact absurd (hsc.2 a hab b hbb) (lt_irrefl _)
  have ht := key _ hN hv hP
  have hD : bcD S (phi (bcNf S a) (bcNf S b)) := by rw [← ht]; exact ⟨hN, by rw [ht]; exact ⟨ha.2.2, hb.2.2⟩⟩
  refine ⟨⟨hmem, by rw [ht]; exact hD⟩, ?_⟩
  unfold bcB
  rw [ht, bcSig_phi]
  rfl

theorem mw_nat_lt_L (m : ℕ) : (m : Ordinal.{0}) < Nc.ncL S ω :=
  (natCast_lt_omega0 m).trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _))

/-- `B_n` fixes the natural numbers. -/
theorem mwB_nat (k m : ℕ) : bcB S k (m : Ordinal.{0}) = m :=
  bcB_fix ((natCast_lt_omega0 m).trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))

/-- **`B_n(φ_m(y)) = φ_m(B_n y)`** for `y ∈ MvD`, `m < y`, `φ_m(y) ≠ y`. -/
theorem mwB_veblen_nat {k m : ℕ} {y : Ordinal.{0}} (hy : MvD S y) (hmy : (m : Ordinal.{0}) < y)
    (hne : veblen (m : Ordinal.{0}) y ≠ y) :
    MvD S (veblen (m : Ordinal.{0}) y) ∧
      bcB S k (veblen (m : Ordinal.{0}) y) = veblen (m : Ordinal.{0}) (bcB S k y) := by
  have hy' : y < veblen (m : Ordinal.{0}) y := lt_of_le_of_ne (right_le_veblen _ _) (Ne.symm hne)
  obtain ⟨hD, hB⟩ := mwB_phi (k := k) (mvD_of_lt (mw_nat_lt_L (S := S) m)) hy (hmy.trans hy') hy'
  exact ⟨hD, by rw [hB, mwB_nat]⟩

/-- **`φ_m(y) = y` gives `φ_m(B_n y) = B_n y`** on `MvD`. -/
theorem mwB_fix {k m : ℕ} {y : Ordinal.{0}} (hy : MvD S y) (hfix : veblen (m : Ordinal.{0}) y = y) :
    veblen (m : Ordinal.{0}) (bcB S k y) = bcB S k y := by
  obtain ⟨hN, hv⟩ := bcNf_spec S hy.1
  have hI : Indec y := by rw [← hfix]; exact mw_veblen_indec _ _
  have hP : (bcNf S y).isPrin = true := isPrin_of_indec hN (by rw [hv]; exact hI)
  have key : ∀ t : Term, NF t → bcD S t → val S t = y → t.isPrin = true →
      veblen (m : Ordinal.{0}) (val S (bcSig (bcPre (k + 1)) bcPreW t)) =
        val S (bcSig (bcPre (k + 1)) bcPreW t) := by
    intro t hN hD hv hP
    cases t with
    | zero => simp [isPrin, isSC] at hP
    | add _ _ => simp [isPrin, isSC] at hP
    | phi c d =>
      have hdlt : val S d < val S (phi c d) := (cmp_lt_iff S hN.2.1 hN).1 hN.2.2.2
      have hv' : veblen (val S c) (val S d) = y := hv
      have hmc : (m : Ordinal.{0}) < val S c := by
        have e : veblen (m : Ordinal.{0}) (veblen (val S c) (val S d)) = veblen (val S c) (val S d) := by
          rw [hv']; exact hfix
        rcases veblen_eq_veblen_iff.1 e with ⟨_, h2⟩ | ⟨h1, _⟩ | ⟨_, h2⟩
        · exfalso
          have : val S d = val S (phi c d) := by rw [← h2]; rfl
          exact absurd this hdlt.ne
        · exact h1
        · exfalso
          have : val S d = val S (phi c d) := by rw [← h2, e]; rfl
          exact absurd this hdlt.ne
      have hDc : bcD S c := ⟨hN.1, hD.2.1⟩
      have hlt := (mvB_lt_iff (k := k) (mvD_of_lt (mw_nat_lt_L (S := S) m)) (mvD_of_term hDc)).2 hmc
      rw [mwB_nat, mvB_term hDc] at hlt
      simp only [bcSig_phi, val]
      exact veblen_veblen_of_lt hlt _
    | _ =>
      have hsc := SC_val S (bc_NF (k := k) hD) (by rw [isSC_bcSig]; simpa [isPrin] using hP)
      exact hsc.veblen_right (Ph.ph_nat_lt hsc m)
  have hD : bcD S (bcNf S y) := hy.2
  unfold bcB
  exact key _ hN hD hv hP

/-- **`y ∈ P_{m+1} ⇔ B_n y ∈ P_{m+1}`** for `y ∈ MvD`, `m < y`, `φ_m(y) ∈ MvD`. -/
theorem mwB_vzP_iff {k m : ℕ} {y : Ordinal.{0}} (hy : MvD S y) (hmy : (m : Ordinal.{0}) < y)
    (hvy : MvD S (veblen (m : Ordinal.{0}) y)) :
    VzP (m + 1) (bcB S k y) ↔ VzP (m + 1) y := by
  rw [vzP_succ, vzP_succ]
  constructor
  · intro h
    by_contra hne
    obtain ⟨-, hB⟩ := mwB_veblen_nat (k := k) hy hmy hne
    have hlt : y < veblen (m : Ordinal.{0}) y := lt_of_le_of_ne (right_le_veblen _ _) (Ne.symm hne)
    have := (mvB_lt_iff (k := k) hy hvy).2 hlt
    rw [hB, h] at this
    exact lt_irrefl _ this
  · exact mwB_fix hy

end Googology.Trans.PoR.InaccPsi.R2.Mw

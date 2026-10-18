import Googology.Trans.PoR.InaccPsi.R2.PhVeb
import Googology.Trans.PoR.InaccPsi.R2.VzT

/-!
# The level-`k` enumeration `ϑʸ(Ω₁·k + η)` as `φ_k` on the ordinals above `y` off `P_{k+1}`

`P_k` is the range of `φ_k = veblen k` (`R2.VzP`).  For a base `y` and `1 ≤ k < ω`, `phC k y` is the set of the
ordinals `x > y` not in `P_{k+1}`, and `phInd k y β = otp(phC k y ∩ β)` the index of `β` in it.

* `phOtp_shift` (`otp_C(x + δ) = otp_C(x) + δ` when `[x, x + δ) ⊆ C`), `phOtp_low` (`otp_C(m) = 0` when `C` has no
  member below `m`);
* `phInd_low` (**`ind(y + 1 + δ) = δ`** when no member of `P_{k+1}` lies in `(y, y + 1 + δ)`), `phInd_P`
  (**`ind(p) = p`** for `p ∈ P_{k+1}`, `p > y`), `phInd_above` (**`ind(p + 1 + δ) = p + δ`** for `p ∈ P_{k+1}`,
  `p > y`, no member of `P_{k+1}` in `(p, p + 1 + δ)`);
* `phLev` (**THE LEVEL LEMMA**): for a strongly critical `y < Ω₁`, `1 ≤ k < ω`, `β > y` with `β ∉ P_{k+1}` and
  `ind(β) ∈ Tʸ ∩ Ω₁`: `φ_k(β) = ϑʸ(Ω₁·k + ind(β))`.  By induction on `β`, from the minimality of
  `ϑʸ(Ω₁·k + η)` in `P_k` (`R2.vz_th_min`), `ϑʸ(Ω₁·k + η) ∈ P_k \ P_{k+1}` (`R2.vz_th_P`, `R2.vz_th_notP`) and the
  monotonicity in `η` (`R2.vz_th_lt`).

No new axiom (the facts on `ϑʸ` are those of `R2.VzL`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ph

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Cd

/-! ## Order types of sets with a full interval -/

/-- `otp_C(x + δ) = otp_C(x) + δ` when `[x, x + δ) ⊆ C`. -/
theorem phOtp_shift (C : Set Ordinal.{0}) (x : Ordinal.{0}) :
    ∀ δ, (∀ z < δ, x + z ∈ C) → cdOtp C (x + δ) = cdOtp C x + δ := by
  intro δ
  induction δ using WellFoundedLT.induction with
  | ind δ IH =>
  intro hC
  apply le_antisymm
  · classical
    rw [cdOtp_eq C (x + δ)]
    refine ciSup_le' fun c => ?_
    by_cases hc : c.1 ∈ C
    · rw [if_pos hc]
      rcases lt_or_ge c.1 x with hcx | hcx
      · exact (Order.add_one_le_of_lt (cdOtp_lt_of_mem hc hcx)).trans le_self_add
      · obtain ⟨z, hz⟩ := exists_add_of_le hcx
        have hzδ : z < δ := by
          have h2 := c.2; rw [hz] at h2; exact (add_lt_add_iff_left _).1 h2
        rw [hz, IH z hzδ (fun z' hz' => hC z' (hz'.trans hzδ)), add_assoc]
        exact (add_le_add_iff_left _).2 (Order.add_one_le_of_lt hzδ)
    · rw [if_neg hc]; exact zero_le
  · refine le_of_forall_lt fun v hv => ?_
    rcases lt_or_ge v (cdOtp C x) with h | h
    · exact h.trans_le (cdOtp_mono C le_self_add)
    · obtain ⟨w, rfl⟩ := exists_add_of_le h
      have hw : w < δ := (add_lt_add_iff_left _).1 hv
      have h1 := cdOtp_lt_of_mem (hC w hw) ((add_lt_add_iff_left x).2 hw)
      rwa [IH w hw (fun z' hz' => hC z' (hz'.trans hw))] at h1

/-- `otp_C(m) = 0` when `C` has no member below `m`. -/
theorem phOtp_low (C : Set Ordinal.{0}) {m : Ordinal.{0}} (h : ∀ c ∈ C, m ≤ c) : cdOtp C m = 0 := by
  rw [← cdOtp_eq_of_gap C (zero_le : (0 : Ordinal.{0}) ≤ m) fun c hc _ hcm => absurd (h c hc) (not_le.2 hcm),
    ggOtp_zero]

/-! ## The index of `β` among the ordinals above `y` off `P_{k+1}` -/

/-- The ordinals above `y` that are not in `P_{k+1}`. -/
def phC (k : ℕ) (y : Ordinal.{0}) : Set Ordinal.{0} := {x | y < x ∧ ¬ VzP (k + 1) x}

/-- The index of `β` in `phC k y`. -/
noncomputable def phInd (k : ℕ) (y β : Ordinal.{0}) : Ordinal.{0} := cdOtp (phC k y) β

variable {k : ℕ} {y : Ordinal.{0}}

theorem mem_phC {x : Ordinal.{0}} : x ∈ phC k y ↔ y < x ∧ ¬ VzP (k + 1) x := Iff.rfl

theorem ph_opow_lim {c : Ordinal.{0}} (hc : c ≠ 0) : IsSuccLimit (ω ^ c) := by
  have e : ω ^ c = ω * ω ^ (c - 1) := by
    conv_lhs => rw [← Ordinal.add_sub_cancel_of_le (Order.one_le_iff_ne_zero.2 hc)]
    rw [opow_add, opow_one]
  rw [e]
  exact isSuccLimit_mul_left isSuccLimit_omega0 (opow_pos _ omega0_pos)

theorem ph_P_E {v : Ordinal.{0}} (h : VzP (k + 1) v) : InE v := vzP_E (by omega) h

theorem ph_P_lim {v : Ordinal.{0}} (h : VzP (k + 1) v) : IsSuccLimit v := by
  have hE := ph_P_E h
  have hv0 : v ≠ 0 := by
    intro h0; rw [h0] at hE; unfold InE at hE; rw [opow_zero] at hE; exact one_ne_zero hE
  have hE' : ω ^ v = v := hE
  rw [← hE']; exact ph_opow_lim hv0

theorem ph_P_succ_not (v : Ordinal.{0}) : ¬ VzP (k + 1) (v + 1) := fun h =>
  not_isSuccLimit_succ v (by rw [succ_eq_add_one]; exact ph_P_lim h)

theorem ph_P_nat_not (v : Ordinal.{0}) (n : ℕ) : ¬ VzP (k + 1) (v + 1 + n) := by
  have e : v + 1 + (n : Ordinal.{0}) = v + n + 1 := by
    rw [add_assoc, add_assoc]; congr 1; exact_mod_cast Nat.add_comm 1 n
  rw [e]; exact ph_P_succ_not _

/-- **`ind(y + 1 + δ) = δ`** when no member of `P_{k+1}` lies in `(y, y + 1 + δ)`. -/
theorem phInd_low {δ : Ordinal.{0}} (h : ∀ z < δ, ¬ VzP (k + 1) (y + 1 + z)) :
    phInd k y (y + 1 + δ) = δ := by
  unfold phInd
  rw [phOtp_shift _ _ δ fun z hz => mem_phC.2 ⟨lt_of_lt_of_le (lt_add_one y) le_self_add, h z hz⟩,
    phOtp_low _ fun c hc => Order.add_one_le_of_lt (mem_phC.1 hc).1, zero_add]

/-- **`ind(p) = p`** for `p ∈ P_{k+1}` above `y`. -/
theorem phInd_P : ∀ p, VzP (k + 1) p → y < p → phInd k y p = p := by
  intro p
  induction p using WellFoundedLT.induction with
  | ind p IH =>
  intro hP hyp
  refine le_antisymm (cdOtp_le_self _ p) (le_of_forall_lt fun α hα => ?_)
  by_cases hex : ∃ p', VzP (k + 1) p' ∧ max α y < p' ∧ p' < p
  · obtain ⟨p', hP', hm, hp'⟩ := hex
    calc α < p' := (le_max_left α y).trans_lt hm
      _ = phInd k y p' := (IH p' hp' hP' ((le_max_right α y).trans_lt hm)).symm
      _ ≤ phInd k y p := cdOtp_mono _ hp'.le
  · push Not at hex
    have hmp : max α y < p := max_lt hα hyp
    have hm1 : max α y + 1 < p := by rw [← succ_eq_add_one]; exact (ph_P_lim hP).succ_lt hmp
    have hprin : IsPrincipal (· + ·) p := by
      have hE' : ω ^ p = p := ph_P_E hP
      rw [← hE']; exact isPrincipal_add_omega0_opow p
    have e : max α y + 1 + p = p := hprin.add_eq_right hm1
    have hsh := phOtp_shift (phC k y) (max α y + 1) p fun z hz => by
      refine mem_phC.2 ⟨lt_of_le_of_lt (le_max_right α y) ((lt_add_one _).trans_le le_self_add), fun hz' => ?_⟩
      have h1 := hex _ hz' ((lt_add_one _).trans_le le_self_add)
      have h2 : max α y + 1 + z < max α y + 1 + p := (add_lt_add_iff_left _).2 hz
      rw [e] at h2
      exact absurd h1 (not_le.2 h2)
    rw [e] at hsh
    show α < cdOtp (phC k y) p
    rw [hsh]
    exact hα.trans_le le_add_self

/-- **`ind(p + 1 + δ) = p + δ`** for `p ∈ P_{k+1}` above `y` and no member of `P_{k+1}` in `(p, p + 1 + δ)`. -/
theorem phInd_above {p δ : Ordinal.{0}} (hP : VzP (k + 1) p) (hyp : y < p)
    (h : ∀ z < δ, ¬ VzP (k + 1) (p + 1 + z)) : phInd k y (p + 1 + δ) = p + δ := by
  have e1 : cdOtp (phC k y) p = cdOtp (phC k y) (p + 1) :=
    cdOtp_eq_of_gap _ le_self_add fun c hc hpc hcp => by
      have hcp' : c = p := le_antisymm (Order.lt_add_one_iff.1 hcp) hpc
      exact (mem_phC.1 hc).2 (hcp' ▸ hP)
  have e2 : cdOtp (phC k y) p = p := phInd_P p hP hyp
  show cdOtp (phC k y) (p + 1 + δ) = p + δ
  rw [phOtp_shift _ _ δ fun z hz => mem_phC.2 ⟨hyp.trans ((lt_add_one p).trans_le le_self_add), h z hz⟩,
    ← e1, e2]

/-- **THE LEVEL LEMMA**: for a strongly critical `y < Ω₁`, `1 ≤ k < ω` and `β > y` off `P_{k+1}` with
`ind(β) ∈ Tʸ ∩ Ω₁`, `φ_k(β) = ϑʸ(Ω₁·k + ind(β))`. -/
theorem phLev (hy : SC y) (hy1 : y < Om1) (hk : 1 ≤ k) :
    ∀ β, y < β → ¬ VzP (k + 1) β → phInd k y β ∈ Tset y → phInd k y β < Om1 →
      veblen (k : Ordinal.{0}) β = vt y (Om1 * (k : Ordinal.{0}) + phInd k y β) := by
  have hyE : InE y := gg_SC_eps hy
  intro β
  induction β using WellFoundedLT.induction with
  | ind β IH =>
  intro hyβ hβP hT h1
  have hβv : β < veblen (k : Ordinal.{0}) β :=
    lt_of_le_of_ne (right_le_veblen _ _) (fun e => hβP (vzP_succ.2 e.symm))
  apply le_antisymm
  · have hfacts := vz_th_facts hyE hy1 hk hT h1
    have hnP := vz_th_notP hyE hy1 hk hT h1
    obtain ⟨β', hβ'⟩ := vz_th_P hyE hy1 k hk _ hT h1
    have hky : veblen (k : Ordinal.{0}) y = y := hy.veblen_right (ph_nat_lt hy k)
    have hyβ' : y < β' := by
      by_contra hle
      push Not at hle
      have h2 := (veblen_le_veblen_iff_right (o := (k : Ordinal.{0}))).2 hle
      rw [hky, hβ'] at h2
      exact absurd hfacts.2.2.2.1 (not_lt.2 h2)
    have hβ'P : ¬ VzP (k + 1) β' := by
      intro hP
      have hfx : veblen (k : Ordinal.{0}) β' = β' := vzP_succ.1 hP
      apply hnP
      rw [← hβ', hfx]; exact hP
    rcases lt_or_ge β' β with hlt | hge
    · exfalso
      have hmem : β' ∈ phC k y := mem_phC.2 ⟨hyβ', hβ'P⟩
      have hlt' : phInd k y β' < phInd k y β := cdOtp_lt_of_mem hmem hlt
      have hT' := vz_T_down hyE hy1 hT h1 hlt'.le
      have e := IH β' hlt hyβ' hβ'P hT' (hlt'.trans h1)
      have h3 := vz_th_lt hyE hy1 hk hT' hT h1 hlt'
      rw [← e, hβ'] at h3
      exact lt_irrefl _ h3
    · rw [← hβ']; exact veblen_le_veblen_iff_right.2 hge
  · refine vz_th_min hyE hy1 hk hT h1 (vzP_veblen k β) (hyβ.trans_le (right_le_veblen _ _))
      ((cdOtp_le_self _ β).trans_lt hβv) fun σ hσ => ?_
    obtain ⟨β', hβ'C, hβ'β, hσe⟩ := ggOtp_onto (phC k y) β σ hσ
    obtain ⟨hyβ', hβ'P⟩ := mem_phC.1 hβ'C
    have hσe' : phInd k y β' = σ := hσe
    have hT' : phInd k y β' ∈ Tset y := by rw [hσe']; exact vz_T_down hyE hy1 hT h1 hσ.le
    rw [← hσe', ← IH β' hβ'β hyβ' hβ'P hT' (by rw [hσe']; exact hσ.trans h1)]
    exact veblen_lt_veblen_iff_right.2 hβ'β

end Googology.Trans.PoR.InaccPsi.R2.Ph

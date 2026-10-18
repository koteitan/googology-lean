import Googology.Trans.PoR.InaccPsi.R2.TpTC

/-!
# `B_n` commutes with `ω^·` and with the last exponent; the `R₁⁺`-reach at `ω^{α'} ∉ E`

`L(ξ) = Nc.ncL S ξ`, `B_n = Bc.bcB S n` (`B_n x = |σ(nf x)|`, `σ` the base change on terms, which commutes
with `φ`), `lg α` the last exponent of `α` (`ω^{lg α} ∣ α`, maximal).

* `tpOpowB` (**`B_n(ω^a) = ω^{B_n a}`** for `ω^a < L(ω)`): the normal form of `ω^a` is `φ(0, nf a)` when
  `ω^a ∉ E`, and a strongly critical term or `φ(c, d)` with `c ≠ 0` when `ω^a ∈ E`; `σ` keeps each kind;
* `tpDvdB`, `tpLgB` (**`lg(B_n a) = B_n(lg a)`** for `0 < a < L(ω)`), through the last-term decomposition
  `a = q + ω^{lg a}`, `ω^{lg a} ∣ q`;
* `TpLhEps S` (the `R₁⁺`-reach moves with `B_n` at the **ε-numbers** that are not `υ`-points in the windows)
  and `tpLhPrin_of_eps`: at `x = ω^{α'} ∉ E` the reach is `x + lg α'` ([W07b] Thm 2.2, `Lh.lhNonE`), and
  `B_n` maps it to `B_n x + lg(B_n α')`, the reach of `B_n x = ω^{B_n α'} ∉ E`; so `TpLhEps` gives `TpLhPrin`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.Term
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cx

variable {S : InaccSeq.{0}}

/-- `lg` is the last exponent `cdExp`. -/
theorem tpLg_eq (a : Ordinal.{0}) : lg a = cdExp a := rfl

/-- `ω^(φ(c, d)) = φ(c, d)` for `c > 0`. -/
theorem tpVeblen_fix {c d : Ordinal.{0}} (hc : 0 < c) : ω ^ veblen c d = veblen c d := by
  have := veblen_veblen_of_lt hc d
  rwa [veblen_zero] at this

/-- An ε-value of `B_n`: if the normal form of `x < L(ω)` is strongly critical or `φ(c, d)` with `c ≠ 0`,
then `B_n x ∈ E`. -/
theorem tpB_eps_of_term {n : ℕ} {x : Ordinal.{0}} (hx : x < Nc.ncL S ω)
    (h : (Bc.bcNf S x).isSC = true ∨ ∃ c d, Bc.bcNf S x = phi c d ∧ c ≠ Term.zero) :
    ω ^ Bc.bcB S n x = Bc.bcB S n x := by
  have hD := Bc.bcD_nf S hx
  have hN : NF (Bc.bcSig (Bc.bcPre (n + 1)) Bc.bcPreW (Bc.bcNf S x)) := Bc.bc_NF hD
  unfold Bc.bcB
  rcases h with hs | ⟨c, d, he, hc⟩
  · have hs' : (Bc.bcSig (Bc.bcPre (n + 1)) Bc.bcPreW (Bc.bcNf S x)).isSC = true := by
      rw [Bc.isSC_bcSig]; exact hs
    exact Low.opow_eq_self_of_SC (SC_val S hN hs')
  · rw [he] at hN ⊢
    rw [Bc.bcSig_phi] at hN ⊢
    have hc' : Bc.bcSig (Bc.bcPre (n + 1)) Bc.bcPreW c ≠ Term.zero := Bc.bcSig_ne_zero hc
    have hpos : 0 < val S (Bc.bcSig (Bc.bcPre (n + 1)) Bc.bcPreW c) :=
      pos_iff_ne_zero.2 (val_ne_zero S hN.1 hc')
    exact tpVeblen_fix hpos

/-- **`B_n(ω^a) = ω^{B_n a}`** for `ω^a < L(ω)`. -/
theorem tpOpowB {n : ℕ} {a : Ordinal.{0}} (hx : ω ^ a < Nc.ncL S ω) :
    Bc.bcB S n (ω ^ a) = ω ^ Bc.bcB S n a := by
  have hal : a < Nc.ncL S ω := lt_of_le_of_lt (right_le_opow a one_lt_omega0) hx
  have hspec := Bc.bcD_nf S hx
  have hv : val S (Bc.bcNf S (ω ^ a)) = ω ^ a := Bc.val_nf S hx
  have hN : NF (Bc.bcNf S (ω ^ a)) := hspec.1
  have hI : Indec (ω ^ a) := indec_iff.2 ⟨(opow_pos a omega0_pos).ne', isPrincipal_add_omega0_opow a⟩
  have hP : (Bc.bcNf S (ω ^ a)).isPrin = true := Bc.isPrin_of_indec hN (by rw [hv]; exact hI)
  -- the ε case
  have heps : ω ^ a = a → ω ^ Bc.bcB S n (ω ^ a) = Bc.bcB S n (ω ^ a) →
      Bc.bcB S n (ω ^ a) = ω ^ Bc.bcB S n a := by
    intro e h; conv_rhs => rw [← e]
    exact h.symm
  generalize ht : Bc.bcNf S (ω ^ a) = t at hv hN hP
  cases t with
  | zero => simp [isPrin, isSC] at hP
  | add _ _ => simp [isPrin, isSC] at hP
  | phi c d =>
    by_cases hc : c = Term.zero
    · subst hc
      have hvd : val S d = a := by
        simp only [val, veblen_zero] at hv
        exact (opow_right_inj one_lt_omega0).1 hv
      have hnd : Bc.bcNf S a = d := by rw [← hvd]; exact Bc.bcNf_val S hN.2.1
      unfold Bc.bcB
      rw [ht, hnd, Bc.bcSig_phi, Bc.bcSig_zero]
      simp only [val, veblen_zero]
    · have hcpos : 0 < val S c := pos_iff_ne_zero.2 (val_ne_zero S hN.1 hc)
      have hE : ω ^ (ω ^ a) = ω ^ a := by
        rw [← hv]; simp only [val]; exact tpVeblen_fix hcpos
      have e : ω ^ a = a := (opow_right_inj one_lt_omega0).1 hE
      exact heps e (tpB_eps_of_term hx (Or.inr ⟨c, d, ht, hc⟩))
  | _ =>
    have hsc : (Bc.bcNf S (ω ^ a)).isSC = true := by rw [ht]; simpa [isPrin] using hP
    have hE : ω ^ (ω ^ a) = ω ^ a := by
      have := Low.opow_eq_self_of_SC (SC_val S hN (by simpa [isPrin] using hP))
      rwa [hv] at this
    exact heps ((opow_right_inj one_lt_omega0).1 hE) (tpB_eps_of_term hx (Or.inl hsc))

/-- `B_n` is monotone on `[0, L(ω))`. -/
theorem tpB_le {n : ℕ} {x y : Ordinal.{0}} (hy : y < Nc.ncL S ω) (h : x ≤ y) :
    Bc.bcB S n x ≤ Bc.bcB S n y := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · exact le_rfl
  · exact ((Bc.bcB_lt_iff (hlt.trans hy) hy).2 hlt).le

/-- **Divisibility moves with `B_n`**: `ω^e ∣ q < L(ω)` gives `ω^{B_n e} ∣ B_n q`. -/
theorem tpDvdB {n : ℕ} {e : Ordinal.{0}} :
    ∀ q, q < Nc.ncL S ω → ω ^ e ∣ q → ω ^ Bc.bcB S n e ∣ Bc.bcB S n q := by
  intro q
  induction q using WellFoundedLT.induction with
  | ind q IH =>
  intro hq hd
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [Bc.bcB_zero]; exact dvd_zero _
  obtain ⟨q0, e1, hd0⟩ := cdExp_decomp hq0
  have hee : e ≤ cdExp q := cdExp_max hq0 hd
  have hq0lt : q0 < q := by
    have := lt_add_of_pos_right q0 (opow_pos (cdExp q) omega0_pos); rwa [← e1] at this
  have hwq : ω ^ cdExp q ≤ q := by
    have := (le_add_self : ω ^ cdExp q ≤ q0 + ω ^ cdExp q); rwa [← e1] at this
  have hwL : ω ^ cdExp q < Nc.ncL S ω := lt_of_le_of_lt hwq hq
  have hEL : cdExp q < Nc.ncL S ω := lt_of_le_of_lt (right_le_opow _ one_lt_omega0) hwL
  have h0 := IH q0 hq0lt (hq0lt.trans hq) ((opow_dvd_opow ω hee).trans hd0)
  rw [e1, Bc.bcB_add (hq0lt.trans hq) hwL, tpOpowB hwL]
  exact dvd_add h0 (opow_dvd_opow ω (tpB_le hEL hee))

/-- `lg(y + ω^f) = f` when `ω^f ∣ y`. -/
theorem tpLg_add {y f : Ordinal.{0}} (hd : ω ^ f ∣ y) : lg (y + ω ^ f) = f := by
  obtain ⟨m, rfl⟩ := hd
  have hpos : 0 < ω ^ f := opow_pos _ omega0_pos
  have e : ω ^ f * m + ω ^ f = ω ^ f * (m + 1) := by rw [mul_add_one]
  have hη : ω ^ f * m + ω ^ f ≠ 0 := (lt_of_lt_of_le hpos le_add_self).ne'
  rw [tpLg_eq]
  refine cdExp_eq hη (e ▸ dvd_mul_right _ _) fun h => ?_
  rw [e] at h
  obtain ⟨c, hc⟩ := h
  rw [opow_add, opow_one, mul_assoc] at hc
  have hc' : m + 1 = ω * c := (isNormal_mul_right hpos).strictMono.injective hc
  have hdiv : ω ∣ succ m := ⟨c, by rw [succ_eq_add_one]; exact hc'⟩
  exact (isSuccPrelimit_iff_omega0_dvd.2 hdiv).succ_ne _ rfl

/-- **`lg(B_n a) = B_n(lg a)`** for `0 < a < L(ω)`. -/
theorem tpLgB {n : ℕ} {a : Ordinal.{0}} (ha : a ≠ 0) (haL : a < Nc.ncL S ω) :
    lg (Bc.bcB S n a) = Bc.bcB S n (lg a) := by
  obtain ⟨q, e1, hd⟩ := cdExp_decomp ha
  have hql : q ≤ a := by
    have := (le_self_add : q ≤ q + ω ^ cdExp a); rwa [← e1] at this
  have hwa : ω ^ cdExp a ≤ a := by
    have := (le_add_self : ω ^ cdExp a ≤ q + ω ^ cdExp a); rwa [← e1] at this
  have hwL : ω ^ cdExp a < Nc.ncL S ω := lt_of_le_of_lt hwa haL
  rw [e1, Bc.bcB_add (lt_of_le_of_lt hql haL) hwL, tpOpowB hwL]
  have h := tpDvdB (S := S) (n := n) q (lt_of_le_of_lt hql haL) hd
  rw [tpLg_add h, ← e1]
  rfl

/-- **The `R₁⁺`-reach moves with `B_n`** at the ε-numbers that are not `υ`-points in the windows. -/
def TpLhEps (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ x r, Bc.bcC S n < x → x < Bc.bcC S (n + 1) → ¬ UpsPt x → InE x → IsLh1 x r →
    IsLh1 (Bc.bcB S n x) (Bc.bcB S n r)

/-- **Only the ε-numbers remain**: `TpLhEps` gives `TpLhPrin`. -/
theorem tpLhPrin_of_eps (h : TpLhEps S) : TpLhPrin S := by
  intro n x r hx1 hx2 hU hI hr
  by_cases hE : InE x
  · exact h n x r hx1 hx2 hU hE hr
  have hxL : x < Nc.ncL S ω := hx2.trans (Bc.bcC_lt S (n + 1))
  obtain ⟨hne, hP⟩ := indec_iff.1 hI
  rcases isPrincipal_add_iff_zero_or_omega0_opow.1 hP with h0 | ⟨a', ha'⟩
  · exact absurd h0 hne
  replace ha' : ω ^ a' = x := ha'
  subst ha'
  have ha0 : a' ≠ 0 := by
    rintro rfl
    rw [opow_zero] at hx1
    have h1 : (1 : Ordinal.{0}) < Bc.bcC S n := by
      simpa using (cxC_lim (S := S) n).add_one_lt (cxC_lim (S := S) n).bot_lt
    exact absurd (hx1.trans h1) (lt_irrefl _)
  have e : r = ω ^ a' + lg a' := Lh.lhUnique hr (Lh.lhNonE ha0 hE)
  subst e
  have haL : a' < Nc.ncL S ω := lt_of_le_of_lt (right_le_opow a' one_lt_omega0) hxL
  have hlgL : lg a' < Nc.ncL S ω := lt_of_le_of_lt (lg_le ha0) haL
  rw [Bc.bcB_add hxL hlgL, tpOpowB hxL, ← tpLgB ha0 haL]
  have hB0 : Bc.bcB S n a' ≠ 0 := by
    intro h0
    rw [← Bc.bcB_zero (S := S) n] at h0
    have : a' = 0 := by
      rcases lt_trichotomy a' 0 with h' | h' | h'
      · exact absurd h' (not_lt.2 zero_le)
      · exact h'
      · exact absurd h0 ((Bc.bcB_lt_iff (lt_trans h' haL) haL).2 h').ne'
    exact ha0 this
  refine Lh.lhNonE hB0 fun hE' => hE ?_
  -- `ω^{B a'} ∈ E` forces `B a' = ω^{B a'}`, i.e. `B a' = B(ω^{a'})`, so `a' = ω^{a'}`
  have e1 : ω ^ Bc.bcB S n a' = Bc.bcB S n a' := (opow_right_inj one_lt_omega0).1 hE'
  rw [← tpOpowB hxL] at e1
  have e2 : ω ^ a' = a' := by
    rcases lt_trichotomy (ω ^ a') a' with h' | h' | h'
    · exact absurd e1 ((Bc.bcB_lt_iff (lt_trans h' haL) haL).2 h').ne
    · exact h'
    · exact absurd e1 ((Bc.bcB_lt_iff haL hxL).2 h').ne'
  show ω ^ (ω ^ a') = ω ^ a'
  exact congrArg (ω ^ ·) e2

end Googology.Trans.PoR.InaccPsi.R2.Tp

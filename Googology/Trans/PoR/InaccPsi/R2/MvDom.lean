import Googology.Trans.PoR.InaccPsi.R2.MvRoad

/-!
# `B_n` on its normal-form domain beyond `L(ω)`: `+`, `ω^·`, `Ω₁`

`B_n = Bc.bcB S n = val ∘ σ ∘ nf` (`σ = bcSig (bcPre (n+1)) bcPreW`).  The base change is stated in `R2.BcMap` for
arguments below `L(ω)`; it is defined for every ordinal with a normal form, and its laws only use that the normal
form is in the domain `bcD` of `σ` (all `ψ_{Ω₁}`-arguments below `α_ω = Ω_ω·2 + P'·ω`).

* `MvD S x` (**the normal-form domain**): `x` has a normal form (`x ∈ ⋃_a Cl(a, 0)`) and `nf(x) ∈ bcD`;
  `mvD_of_lt` (every `x < L(ω)`), `mvD_of_term` (the value of a term in `bcD`), `mvD_val`;
* `mvB_lt_iff` (**`B_n` is strictly increasing on `MvD`**, `Bc.bc_lt_iff`);
* `mvB_add` (**`B_n(x + y) = B_n x + B_n y`** on `MvD`, and `x + y ∈ MvD`);
* `mvB_Om1` (**`B_n(Ω₁) = Ω₁`**, `Ω₁ ∈ MvD`);
* `mvB_opow` (**`B_n(ω^a) = ω^{B_n a}`** for `a ∈ MvD` with `ω^a ≠ a`, and `ω^a ∈ MvD`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Mv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Bc

variable {S : InaccSeq.{0}}

/-- **The normal-form domain of `B_n`**: `x` has a normal form, and it is in `bcD`. -/
def MvD (S : InaccSeq.{0}) (x : Ordinal.{0}) : Prop :=
  x ∈ ⋃ a, S.CSet a 0 ∧ bcD S (bcNf S x)

theorem mvD_val {x : Ordinal.{0}} (h : MvD S x) : val S (bcNf S x) = x := (bcNf_spec S h.1).2

theorem mvD_of_lt {x : Ordinal.{0}} (hx : x < Nc.ncL S ω) : MvD S x := by
  refine ⟨?_, bcD_nf S hx⟩
  rw [ncL_omega_eq] at hx
  exact mem_of_lt_psi S hx

theorem mvD_of_term {t : Term} (hD : bcD S t) : MvD S (val S t) := by
  refine ⟨Set.mem_iUnion.2 (exists_mem_CSet S t), ?_⟩
  rw [bcNf_val S hD.1]; exact hD

theorem mvB_term {k : ℕ} {t : Term} (hD : bcD S t) :
    bcB S k (val S t) = val S (bcSig (bcPre (k + 1)) bcPreW t) := by
  unfold bcB; rw [bcNf_val S hD.1]

/-- **`B_n` is strictly increasing on `MvD`.** -/
theorem mvB_lt_iff {k : ℕ} {x y : Ordinal.{0}} (hx : MvD S x) (hy : MvD S y) :
    bcB S k x < bcB S k y ↔ x < y := by
  unfold bcB
  rw [bc_lt_iff hx.2 hy.2, mvD_val hx, mvD_val hy]

/-- **`B_n(x + y) = B_n x + B_n y`** on `MvD`. -/
theorem mvB_add {k : ℕ} {x y : Ordinal.{0}} (hx : MvD S x) (hy : MvD S y) :
    MvD S (x + y) ∧ bcB S k (x + y) = bcB S k x + bcB S k y := by
  obtain ⟨hN, hv, -⟩ := addNF_spec (S := S) hx.2.1 hy.2.1
  rw [mvD_val hx, mvD_val hy] at hv
  have hD : bcD S (addNF (bcNf S x) (bcNf S y)) := ⟨hN, Sf.sfArgs_addNF hx.2.2 hy.2.2⟩
  have e : bcNf S (x + y) = addNF (bcNf S x) (bcNf S y) := by rw [← hv]; exact bcNf_val S hN
  refine ⟨?_, ?_⟩
  · rw [← hv]; exact mvD_of_term hD
  · unfold bcB
    rw [e, bcSig_addNF hx.2 hy.2]
    exact (addNF_spec (S := S) (bc_NF hx.2) (bc_NF hy.2)).2.1

theorem mvOm1_val : val S (om tOne) = Om 1 := by
  simp [val, tOne]

theorem mvOm1_D : bcD S (om tOne) :=
  bcD_free ⟨NF_tOne, tOne_ne_zero, rfl⟩ (show bcFree (om tOne) from bcFree_tOne)

/-- **`B_n(Ω₁) = Ω₁`.** -/
theorem mvB_Om1 {k : ℕ} : MvD S (Om 1) ∧ bcB S k (Om 1) = Om 1 := by
  have h := mvOm1_D (S := S)
  rw [← mvOm1_val (S := S)]
  exact ⟨mvD_of_term h, by
    rw [mvB_term h, bcSig_free (show bcFree (om tOne) from bcFree_tOne)]⟩

/-- **`B_n(ω^a) = ω^{B_n a}`** for `a ∈ MvD` with `ω^a ≠ a`. -/
theorem mvB_opow {k : ℕ} {a : Ordinal.{0}} (ha : MvD S a) (hne : ω ^ a ≠ a) :
    MvD S (ω ^ a) ∧ bcB S k (ω ^ a) = ω ^ bcB S k a := by
  have hmem : ω ^ a ∈ ⋃ b, S.CSet b 0 := by
    obtain ⟨b, hb⟩ := Set.mem_iUnion.1 ha.1
    refine Set.mem_iUnion.2 ⟨b, ?_⟩
    have := CSet.phi_mem (S := S) (CSet.zero_mem b 0) hb
    rwa [veblen_zero] at this
  obtain ⟨hN, hv⟩ := bcNf_spec S hmem
  have hI : Indec (ω ^ a) :=
    indec_iff.2 ⟨(opow_pos a omega0_pos).ne', isPrincipal_add_omega0_opow a⟩
  have hP : (bcNf S (ω ^ a)).isPrin = true := isPrin_of_indec hN (by rw [hv]; exact hI)
  have hnE : ω ^ (ω ^ a) ≠ ω ^ a := fun h => hne ((opow_right_inj one_lt_omega0).1 h)
  generalize ht : bcNf S (ω ^ a) = t at hN hv hP
  cases t with
  | zero => simp [isPrin, isSC] at hP
  | add _ _ => simp [isPrin, isSC] at hP
  | phi c d =>
    by_cases hc : c = Term.zero
    · subst hc
      have hvd : val S d = a := by
        simp only [val, veblen_zero] at hv
        exact (opow_right_inj one_lt_omega0).1 hv
      have hnd : bcNf S a = d := by rw [← hvd]; exact bcNf_val S hN.2.1
      have hAd : bcArgsLt S (bcAlphaW S) d := by rw [← hnd]; exact ha.2.2
      have hD : bcD S (phi Term.zero d) := ⟨hN, trivial, hAd⟩
      refine ⟨⟨hmem, by rw [ht]; exact hD⟩, ?_⟩
      unfold bcB
      rw [ht, hnd, bcSig_phi, bcSig_zero]
      simp only [val, veblen_zero]
    · exfalso
      have hcpos : 0 < val S c := pos_iff_ne_zero.2 (val_ne_zero S hN.1 hc)
      apply hnE
      rw [← hv]; simp only [val]; exact Tp.tpVeblen_fix hcpos
  | _ =>
    exfalso
    apply hnE
    have := Low.opow_eq_self_of_SC (SC_val S hN (by simpa [isPrin] using hP))
    rwa [hv] at this

end Googology.Trans.PoR.InaccPsi.R2.Mv

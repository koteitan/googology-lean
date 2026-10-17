import Googology.Trans.PoR.InaccPsi.R2.BtL9

/-!
# LOW-STEP, part 10: Lemma KB at level 0, and case (II) through a head

The repo module `R2.BrLs10` with the summands of `A` given by a list `L` (`R2.Bt.GoodL`) in place of
those of `A_{ω·m+n}`; the statements are the same with `AA S L`, `kA S L` for `AA S m n`, `kA S m n`.


* `KLt_topAtom`, `KLt_dropT`: the `K`-condition passes to top atoms and to `dropT`;
* `KB0`: the level-`0` parts of `E(u)`, `u` visited from the `A`-clause term `μ = ψ_{Ω₁}(A + ζ)`, are below
  a bound (no level-0 code `F` exists);
* `head_mem_Ki_s`, `via_head_s`: case (II) of [W25] Prop 2.15 through a head, over `σ`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Bt

open Googology.Trans.PoR.InaccPsi.R2.Br

open Ordinal Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq Googology.Trans.PoR.InaccPsi.R2.Br.Tm

variable {S : InaccSeq.{0}} {σ : Ordinal.{0}} {L : List Ordinal.{0}}

/-- The oracle of Lemma M over `σ`. -/
def MOs (S : InaccSeq.{0}) (σ : Ordinal.{0}) (L : List Ordinal.{0}) (N M : ℕ) : Prop :=
  ∀ x y : Term, x.size ≤ N → y.size ≤ N → x.size + y.size < M → CL S σ L x → CL S σ L y →
    Term.val S x < Term.val S y → ev σ (Ex S σ L x) < ev σ (Ex S σ L y)

/-- The oracle of Lemma D over `σ`. -/
def DOs (S : InaccSeq.{0}) (σ : Ordinal.{0}) (L : List Ordinal.{0}) (N : ℕ) : Prop :=
  ∀ u : Term, u.size ≤ N → CL S σ L u → DL S σ L u

theorem KLt_topAtom {μ α : Term} : ∀ {t a : Term}, Term.KLt μ t α → a ∈ topAtoms t → Term.KLt μ a α
  | .zero, a, _, h => by simp [topAtoms] at h
  | .add x y, a, hK, h => by
    simp only [topAtoms, List.mem_append] at h
    rcases h with h | h
    · exact KLt_topAtom hK.1 h
    · exact KLt_topAtom hK.2 h
  | .phi x y, a, hK, h => by
    simp only [topAtoms, List.mem_append] at h
    rcases h with h | h
    · exact KLt_topAtom hK.1 h
    · exact KLt_topAtom hK.2 h
  | .om _, a, hK, h => by simp [topAtoms] at h; subst h; exact hK
  | .psiS _ _, a, hK, h => by simp [topAtoms] at h; subst h; exact hK
  | .inacc _, a, hK, h => by simp [topAtoms] at h; subst h; exact hK
  | .inaccW, a, hK, h => by simp [topAtoms] at h; subst h; exact hK
  | .psiI _ _, a, hK, h => by simp [topAtoms] at h; subst h; exact hK

theorem KLt_dropT {μ α : Term} : ∀ (k : ℕ) (x : Term), Term.KLt μ x α → Term.KLt μ (dropT k x) α
  | 0, x, h => h
  | k + 1, x, h => by
    cases x <;> simp only [dropT] <;> first | trivial | exact KLt_dropT k _ h.2

theorem psiA_lvl {s c : Term} (hs0 : Term.val S s = 0) : lvl (Term.val S (.psiS s c)) = 0 := by
  have := (Term.val_psiS_bounds S s c).2
  rw [hs0, zero_add] at this
  exact lvl_zero_of_lt_Om1 this

/-- **Lemma KB at level `0`.** -/
theorem KB0 (hσ : Base σ) {s c : Term} (hμ : Term.NF (.psiS s c)) (hs0 : Term.val S s = 0)
    (hμσ : σ ≤ Term.val S (.psiS s c)) (Y : Ordinal.{0}) {N : ℕ}
    (hD : DOs S σ L N)
    (hO1 : ∀ r : Term, r.size ≤ N → CL S σ L r → r.isPrin = true →
      lvl (Term.val S r) = 0 → Term.val S r < Term.val S (.psiS s c) → ev σ (Ex S σ L r) < Y) :
    ∀ u : Term, CL S σ L u → u.size ≤ N → Term.KLt (.psiS s c) u c →
      ∀ v ∈ Ki 0 (Ex S σ L u), ev σ v < Y := by
  have hpb : ∀ r : Term, CL S σ L r → r.isPrin = true → lvl (Term.val S r) = 0 →
      Term.KLt (.psiS s c) r c → Term.val S r < Term.val S (.psiS s c) :=
    fun r hc hp hl hK => parts_b_CL hσ hμ (k := 0) (by rw [hs0]; rfl) hμσ r.size r le_rfl hc hp hl hK
  intro u hu
  induction hu with
  | par hn hv => intro _ _ v hv'; rw [Ex_par hv] at hv'; simp [Ki] at hv'
  | @add x y hn hv hx hy ihx ihy =>
    intro hs hK v hv'
    rw [(hD _ hs (CL.add hn hv hx hy)).add x y rfl hv] at hv'
    simp only [Ki, List.mem_append] at hv'
    rcases hv' with h | h
    · exact ihx (by simp [Term.size] at hs; omega) hK.1 v h
    · exact ihy (by simp [Term.size] at hs; omega) hK.2 v h
  | @om b j hn hv hj0 hj =>
    intro _ _ v hv'
    rw [Ex, EL_om hv, hj, natOf_nat] at hv'
    simp [Omk, Ki, show ¬ j < 0 by omega, show j ≠ 0 from hj0] at hv'
  | @phi x y hn hv hx hy ihx ihy =>
    intro hs hK v hv'
    have hc' : CL S σ L (.phi x y) := CL.phi hn hv hx hy
    set j := lvl (Term.val S (.phi x y)) with hjdef
    have e : Ex S σ L (.phi x y) = th j (plus σ (th (j + 1) (Ex S σ L x)) (Ex S σ L y)) := by
      rw [Ex, EL_phi hv]
    rw [e] at hv'
    simp only [Ki] at hv'
    split_ifs at hv' with h1 h2
    · simp at hv'
    · simp at hv'; subst hv'
      rw [← e]
      exact hO1 _ hs hc' rfl h2 (hpb _ hc' rfl h2 hK)
    · rcases List.mem_append.1 (Ki_plus σ 0 _ _ hv') with h | h
      · simp only [Ki, show ¬ j + 1 < 0 by omega, show j + 1 ≠ 0 by omega, if_false] at h
        exact ihx (by simp [Term.size] at hs; omega) hK.1 v h
      · exact ihy (by simp [Term.size] at hs; omega) hK.2 v h
  | @psiA s' c' hn hv hs0' h1 h2 h3 h4 _ =>
    intro hs hK v hv'
    have hc' : CL S σ L (.psiS s' c') := CL.psiA hn hv hs0' h1 h2 h3 h4
    have h0 : natOf (Term.val S s') = 0 := by rw [hs0']; exact natOf_nat 0
    have e := EL_psi0 (kA := kA S L) hv h0
    rw [Ex, e] at hv'
    simp only [Ki, show ¬ (0 : ℕ) < 0 by omega, if_false, if_true] at hv'
    simp at hv'; subst hv'
    rw [← e]
    exact hO1 _ hs hc' rfl (psiA_lvl hs0') (hpb _ hc' rfl (psiA_lvl hs0') hK)
  | @psiS s' c' j hn hv hj0 hj hcω' hcc ihc =>
    intro hs hK v hv'
    have hnat : natOf (Term.val S s') ≠ 0 := by rw [hj, natOf_nat]; exact hj0
    rw [Ex, EL_psiS hv hnat, hj, natOf_nat] at hv'
    simp only [Ki, show ¬ j < 0 by omega, show j ≠ 0 from hj0, if_false] at hv'
    rcases hK with hK | ⟨hca, _, hKc⟩
    · exfalso
      have h1' := (Term.cmp_lt_iff S hn hμ).1 hK
      have h2' := (psiS_bounds_nat s' c' hj).1
      have h3' := (Term.val_psiS_bounds S s c).2
      rw [hs0, zero_add] at h3'
      exact absurd (h1'.trans h3') (not_lt.2 ((BP.Om_one_le_Om_nat hj0).trans h2'.le))
    have hsc' : c'.size ≤ N := le_trans (by simp only [Term.size]; omega) hs
    have hDc := hD c' hsc' hcc
    have hEcω : ev σ (Ex S σ L c') < Om (ω : Ordinal.{0}) := hDc.lt.trans (OmT_succ_lt_Om_omega σ _)
    rcases List.mem_append.1 (Ki_plus σ 0 _ _ hv') with h | h
    · simp [Pk, Omk, Ki] at h
    · by_cases hc0 : ev σ (Ex S σ L c') = 0
      · rw [gFc_zero hσ hc0] at h; simp [Ki] at h
      have h' := gKi_Fc hσ hc0 h
      split_ifs at h' with g1 g2
      all_goals first
        | exact ihc hsc' hKc v h'
        | contradiction

/-! ## Case (II) through a head -/

theorem head_mem_Ki_s {N : ℕ} (hD : DOs S σ L N) {z : Term} (hz : z.size ≤ N) (hc : CL S σ L z)
    (hz0 : z ≠ .zero) (hσz : ¬ Term.val S (Term.head z) < σ) {k : ℕ}
    (hk : lvl (Term.val S (Term.head z)) = k) (_hσ : Base σ) :
    Ex S σ L (Term.head z) ∈ Ki k (Ex S σ L z) := by
  have hDz := hD _ hz hc
  have hzσ : ¬ Term.val S z < σ := fun h => hσz (lt_of_le_of_lt (val_head_le z) h)
  cases hc with
  | par _ h => exact absurd h hzσ
  | @add z1 z2 hn hv hz1 hz2 =>
    have hD1 := hD z1 (by simp [Term.size] at hz; omega) hz1
    obtain ⟨-, e, he⟩ := hD1.prin hn.2.2.1 hσz
    simp only [Term.head] at hk hσz ⊢
    rw [hDz.add z1 z2 rfl hv, he, hk]
    simp [Ki]
  | phi hn hv _ _ =>
    obtain ⟨-, e, he⟩ := hDz.prin rfl hv
    simp only [Term.head] at hk ⊢
    rw [he, hk]; simp [Ki]
  | om hn hv _ _ =>
    obtain ⟨-, e, he⟩ := hDz.prin rfl hv
    simp only [Term.head] at hk ⊢
    rw [he, hk]; simp [Ki]
  | psiS hn hv _ _ _ _ =>
    obtain ⟨-, e, he⟩ := hDz.prin rfl hv
    simp only [Term.head] at hk ⊢
    rw [he, hk]; simp [Ki]
  | psiA hn hv _ _ _ _ _ =>
    obtain ⟨-, e, he⟩ := hDz.prin rfl hv
    simp only [Term.head] at hk ⊢
    rw [he, hk]; simp [Ki]

/-- **Case (II) through a head** over `σ`. -/
theorem via_head_s (hσ : Base σ) {N : ℕ} (hD : DOs S σ L N) {p q z : Term} (hsp : p.size ≤ N)
    (hsq : q.size ≤ N) (IHi : MOs S σ L N (p.size + q.size)) (cp : CL S σ L p)
    (pp : p.isPrin = true) (hpσ : ¬ Term.val S p < σ)
    {k : ℕ} (hkp : lvl (Term.val S p) = k) {ep eq : Tm} (hep : Ex S σ L p = th k ep)
    (heq : Ex S σ L q = th k eq) (nEp : NF σ (th k ep)) (nEq : NF σ (th k eq))
    (hsz : z.size < q.size) (hcz : CL S σ L z)
    (hpz : Term.val S p ≤ Term.val S z) (hzq : Term.val S z < OmT 1 (k + 1))
    (hsub : Ki k (Ex S σ L z) ⊆ Ki k eq) : ev σ (Ex S σ L p) < ev σ (Ex S σ L q) := by
  have np := cp.NF
  have hnz := hcz.NF
  have hz0 : z ≠ .zero := by
    rintro rfl
    exact absurd hpz (not_le.2 (pos_iff_ne_zero.2 (Term.val_ne_zero S np
      (Term.NF.ne_zero_of_isPrin pp))))
  have hhead : Term.val S p ≤ Term.val S (Term.head z) := by
    by_contra hl
    exact absurd hpz (not_le.2 (val_lt_of_head hnz (Term.isPrincipal_val S np pp) (not_le.1 hl)))
  have hpOm : OmT 1 k ≤ Term.val S p := hkp ▸ OmT_lvl_le_CL hσ cp pp
  have hlvh : lvl (Term.val S (Term.head z)) = k :=
    lvl_of_th_bounds (hpOm.trans hhead) (lt_of_le_of_lt (val_head_le z) hzq)
  have hσh : ¬ Term.val S (Term.head z) < σ := fun h => hpσ (lt_of_le_of_lt hhead h)
  have hmem := hsub (head_mem_Ki_s hD (by omega) hcz hz0 hσh hlvh hσ)
  have hle : ev σ (Ex S σ L p) ≤ ev σ (Ex S σ L (Term.head z)) := by
    rcases eq_or_lt_of_le hhead with he | he
    · rw [Term.eq_of_val_eq S np hnz.head he]
    · exact (IHi p (Term.head z) hsp (by have := Term.size_head_le z; omega)
        (by have := Term.size_head_le z; omega) cp (CL_head hcz hz0) he).le
  rw [hep, heq]
  rw [hep] at hle
  exact thb_lt_of_II hσ nEp nEq (hle.trans (le_star hmem))

end Googology.Trans.PoR.InaccPsi.R2.Bt

import Googology.Trans.PoR.InaccPsi.R2.BrLs8

/-!
# LOW-STEP, part 9: tools for Lemma M over `σ`

* `OmT_lvl_le_CL`, `parts_b_CL` (Lemma PARTS (b) for the class): a level-`k` principal term visited from
  `μ = ψ_{Ω_{k+1}}(a)` is below `μ`;
* `KBs` (level `k ≥ 1`) and `KB0` (level `0`, the `A`-clause): the level-`k` parts of `E(u)`, `u` visited
  from `μ`, are below a bound;
* `head_mem_Ki_s`, `via_head_s`: case (II) of [W25] Prop 2.15 through a head.

The statements are proved for `A` the sum of any list `L` of summands (namespace `R2.Bt`: `AA S L` the
sum of `L`, `kA S L` its length, `GoodL S L` where it is needed); the original statements for
`A = A_{ω·m+n}` (namespace `R2.Br`, the same names) follow as corollaries at `L = Alist S m n`.
-/

/-! ## The list version (namespace `R2.Bt`) -/

namespace Googology.Trans.PoR.InaccPsi.R2.Bt

open Googology.Trans.PoR.InaccPsi.R2.Br

open Ordinal Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq Googology.Trans.PoR.InaccPsi.R2.Br.Tm

variable {S : InaccSeq.{0}} {σ : Ordinal.{0}} {L : List Ordinal.{0}}

theorem OmT_lvl_le_CL (hσ : Base σ) {r : Term} (hc : CL S σ L r) (hp : r.isPrin = true) :
    OmT 1 (lvl (Term.val S r)) ≤ Term.val S r := by
  have hv := CL_val_lt hσ hc
  rcases Nat.eq_zero_or_pos (lvl (Term.val S r)) with h | h
  · rw [h, OmT_zero]
    exact Order.one_le_iff_ne_zero.2 (Term.val_ne_zero S hc.NF (Term.NF.ne_zero_of_isPrin hp))
  · exact lvl_ge hv h.ne'

/-- **Lemma PARTS (b)** for the class. -/
theorem parts_b_CL (hσ : Base σ) {s a : Term} (hμ : Term.NF (.psiS s a)) {k : ℕ}
    (hk : Term.val S s = k) (hμσ : σ ≤ Term.val S (.psiS s a)) :
    ∀ (N : ℕ) (r : Term), r.size ≤ N → CL S σ L r → r.isPrin = true →
      lvl (Term.val S r) = k → Term.KLt (.psiS s a) r a → Term.val S r < Term.val S (.psiS s a) := by
  intro N
  induction N with
  | zero => intro r h; exact absurd (Term.size_pos r) (by omega)
  | succ N ih =>
    intro r hs hcr hp hl hK
    have hr := hcr.NF
    by_cases hσr : Term.val S r < σ
    · exact lt_of_lt_of_le hσr hμσ
    cases r with
    | zero => simp [Term.isPrin, Term.isSC] at hp
    | add _ _ => simp [Term.isPrin, Term.isSC] at hp
    | inacc _ => cases hcr; contradiction
    | inaccW => cases hcr; contradiction
    | psiI _ _ => cases hcr; contradiction
    | om b =>
      cases hcr with
      | par _ h => exact absurd h hσr
      | om _ _ hk0 hk' =>
        rw [val_om_of_Cw hk', lvl_Om hk0] at hl
        subst hl
        rw [val_om_of_Cw hk']
        exact (psiS_bounds_nat s a hk).1
    | psiS s' c =>
      rcases hK with hK | ⟨hca, _, _⟩
      · exact (Term.cmp_lt_iff S hr hμ).1 hK
      · have hk' : Term.val S s' = k := by
          cases hcr with
          | par _ h => exact absurd h hσr
          | psiS _ _ _ hj _ _ => rw [hj]; rw [lvl_psiS s' c hj] at hl; rw [hl]
          | psiA _ _ hs0 _ _ _ _ => rw [lvl_psiS s' c (k := 0) (by rw [hs0]; rfl)] at hl; rw [hs0, ← hl]; rfl
        have hc : Term.val S c < Term.val S a := (Term.cmp_lt_iff S hr.2.1 hμ.2.1).1 hca
        have hsem := (Term.sem_of_NF (S := S) hr).2.2
        simp only [Term.val] at hsem ⊢
        rw [hk', ← hk] at hsem ⊢
        exact psi_lt_psi (InR_Om_succ _) hc hsem
    | phi x y =>
      obtain ⟨hn, hv, hcx, hcy⟩ : Term.NF (.phi x y) ∧ ¬ Term.val S (.phi x y) < σ ∧ CL S σ L x ∧
          CL S σ L y := by
        cases hcr with
        | par _ h => exact absurd h hσr
        | phi hn hv hx hy => exact ⟨hn, hv, hx, hy⟩
      by_contra hge
      rw [not_lt] at hge
      have hSC : SC (Term.val S (.psiS s a)) := Term.SC_val S hμ rfl
      obtain ⟨hx, hy⟩ := NF_phi_lt (S := S) hr
      have hz : ∃ z, (z = x ∨ z = y) ∧ Term.val S (.psiS s a) ≤ Term.val S z := by
        by_contra hno
        push Not at hno
        have h1 := hno x (Or.inl rfl)
        have h2 := hno y (Or.inr rfl)
        have := hSC.2 _ h1 _ h2
        simp only [Term.val] at hge this
        exact absurd hge (not_le.2 this)
      obtain ⟨z, hzxy, hzge⟩ := hz
      have hnz : Term.NF z := by rcases hzxy with rfl | rfl; exacts [hr.1, hr.2.1]
      have hcz : CL S σ L z := by rcases hzxy with rfl | rfl; exacts [hcx, hcy]
      have hKz : Term.KLt (.psiS s a) z a := by rcases hzxy with rfl | rfl; exacts [hK.1, hK.2]
      have hzlt : Term.val S z < Term.val S (.phi x y) := by rcases hzxy with rfl | rfl; exacts [hx, hy]
      have hsz : z.size < (Term.phi x y).size := by
        rcases hzxy with rfl | rfl <;> simp [Term.size]
      have hz0 : z ≠ .zero := by
        rintro rfl
        simp only [Term.val] at hzge
        exact absurd hzge (not_le.2 hSC.1)
      have hhead : Term.val S (.psiS s a) ≤ Term.val S (Term.head z) := by
        by_contra hlt
        exact absurd hzge (not_le.2 (val_lt_of_head hnz hSC.isPrincipal (not_le.1 hlt)))
      have hlv : lvl (Term.val S (Term.head z)) = k := by
        have hup : Term.val S (Term.head z) < OmT 1 (k + 1) := by
          rw [← hl]
          exact lt_of_le_of_lt ((val_head_le z).trans hzlt.le) (lvl_lt (CL_val_lt hσ hcr))
        rcases Nat.eq_zero_or_pos k with rfl | hpos
        · have := lvl_le_of_lt hup; omega
        · refine lvl_eq ?_ hup hpos.ne'
          rw [← Om_nat_eq_OmT hpos.ne']
          exact ((psiS_bounds_nat s a hk).1.le).trans hhead
      have := ih (Term.head z) (by have := Term.size_head_le z; omega) (CL_head hcz hz0)
        (head_isPrin hnz hz0) hlv (KLt_head hKz)
      exact absurd hhead (not_le.2 this)

/-! ## The level-`k` parts -/

/-- **Lemma KB** over `σ`, level `k ≥ 1`. -/
theorem KBs (hσ : Base σ) {s a : Term} (hμ : Term.NF (.psiS s a)) {k : ℕ} (hk0 : k ≠ 0)
    (hk : Term.val S s = k) (Y : Ordinal.{0})
    (hD : ∀ u : Term, u.size ≤ a.size → CL S σ L u → DL S σ L u)
    (hO1 : ∀ r : Term, r.size ≤ a.size → CL S σ L r → r.isPrin = true →
      lvl (Term.val S r) = k → Term.val S r < Term.val S (.psiS s a) → ev σ (Ex S σ L r) < Y)
    (hO2 : ∀ x : Tm, NF σ x → ev σ x < Om (ω : Ordinal.{0}) → ev σ x ≠ 0 → lvl (ev σ x) + 1 = k →
      ev σ (gFc σ x) < Y) :
    ∀ u : Term, CL S σ L u → u.size ≤ a.size → Term.KLt (.psiS s a) u a →
      ∀ v ∈ Ki k (Ex S σ L u), ev σ v < Y := by
  have hμσ : σ ≤ Term.val S (.psiS s a) := by
    have h1 := (psiS_bounds_nat s a hk).1
    exact (hσ.lt_Om1.le.trans (BP.Om_one_le_Om_nat hk0)).trans h1.le
  have hpb : ∀ r : Term, CL S σ L r → r.isPrin = true → lvl (Term.val S r) = k →
      Term.KLt (.psiS s a) r a → Term.val S r < Term.val S (.psiS s a) :=
    fun r hc hp hl hK => parts_b_CL hσ hμ hk hμσ r.size r le_rfl hc hp hl hK
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
    intro hs hK v hv'
    have hc' : CL S σ L (.om b) := CL.om hn hv hj0 hj
    have hl : lvl (Term.val S (.om b)) = j := by rw [val_om_of_Cw hj]; exact lvl_Om hj0
    rw [Ex, EL_om hv, hj, natOf_nat] at hv'
    simp only [Omk, Ki] at hv'
    split_ifs at hv' with h1 h2
    · simp at hv'
    · simp at hv'; subst hv'; subst h2
      have e : Ex S σ L (.om b) = th j (par 0) := by rw [Ex, EL_om hv, hj, natOf_nat]; rfl
      rw [← e]
      exact hO1 _ hs hc' rfl hl (hpb _ hc' rfl hl hK)
    · simp at hv'
  | @phi x y hn hv hx hy ihx ihy =>
    intro hs hK v hv'
    have hc' : CL S σ L (.phi x y) := CL.phi hn hv hx hy
    have hDx := hD x (by simp [Term.size] at hs; omega) hx
    have hDy := hD y (by simp [Term.size] at hs; omega) hy
    obtain ⟨vx, vy⟩ := NF_phi_lt (S := S) hn
    set j := lvl (Term.val S (.phi x y)) with hjdef
    have hvω := CL_val_lt hσ hc'
    have hxk : ev σ (Ex S σ L x) < OmT σ (j + 1) :=
      lt_of_lt_of_le hDx.lt (OmT_mono hσ (by have := lvl_mono hvω vx.le; omega))
    have e : Ex S σ L (.phi x y) = th j (plus σ (th (j + 1) (Ex S σ L x)) (Ex S σ L y)) := by
      rw [Ex, EL_phi hv]
    rw [e] at hv'
    simp only [Ki] at hv'
    split_ifs at hv' with h1 h2
    · simp at hv'
    · simp at hv'; subst hv'
      rw [← e]
      exact hO1 _ hs hc' rfl h2 (hpb _ hc' rfl h2 hK)
    · rcases List.mem_append.1 (Ki_plus σ k _ _ hv') with h | h
      · simp only [Ki, show ¬ j + 1 < k by omega, show j + 1 ≠ k by omega, if_false] at h
        exact ihx (by simp [Term.size] at hs; omega) hK.1 v h
      · exact ihy (by simp [Term.size] at hs; omega) hK.2 v h
  | @psiA s' c' hn hv hs0 _ _ _ _ _ =>
    intro _ _ v hv'
    have h0 : natOf (Term.val S s') = 0 := by rw [hs0]; exact natOf_nat 0
    rw [Ex, EL_psi0 hv h0] at hv'
    simp only [Ki, show (0 : ℕ) < k by omega, if_true] at hv'
    simp at hv'
  | @psiS s' c' j hn hv hj0 hj hcω' hcc ihc =>
    intro hs hK v hv'
    have hc' : CL S σ L (.psiS s' c') := CL.psiS hn hv hj0 hj hcω' hcc
    have hl : lvl (Term.val S (.psiS s' c')) = j := lvl_psiS s' c' hj
    have hnat : natOf (Term.val S s') ≠ 0 := by rw [hj, natOf_nat]; exact hj0
    have e : Ex S σ L (.psiS s' c') = th j (plus σ (Pk j) (gFc σ (Ex S σ L c'))) := by
      rw [Ex, EL_psiS hv hnat, hj, natOf_nat]
    rw [e] at hv'
    simp only [Ki] at hv'
    split_ifs at hv' with h1 h2
    · simp at hv'
    · simp at hv'; subst hv'
      rw [← e]
      exact hO1 _ hs hc' rfl (hl.trans h2) (hpb _ hc' rfl (hl.trans h2) hK)
    · have hjk : k < j := by omega
      rcases hK with hK | ⟨hca, _, hKc⟩
      · exfalso
        have h1' := (Term.cmp_lt_iff S hn hμ).1 hK
        have h2' := (psiS_bounds_nat s' c' hj).1
        have h3' := (psiS_bounds_nat s a hk).2
        have h4' : OmT 1 (k + 1) ≤ Om (j : Ordinal.{0}) := by
          rw [Om_nat_eq_OmT (by omega)]; exact OmT_mono base_one (by omega)
        exact absurd h1' (not_lt.2 (h3'.le.trans (h4'.trans h2'.le)))
      have hsc : c'.size ≤ a.size := by simp [Term.size] at hs; omega
      have hDc := hD c' hsc hcc
      have hEcω : ev σ (Ex S σ L c') < Om (ω : Ordinal.{0}) := hDc.lt.trans (OmT_succ_lt_Om_omega σ _)
      rcases List.mem_append.1 (Ki_plus σ k _ _ hv') with h | h
      · simp [Pk, Omk, Ki, show ¬ j + 1 < k by omega, show j + 1 ≠ k by omega] at h
      · by_cases hc0 : ev σ (Ex S σ L c') = 0
        · rw [gFc_zero hσ hc0] at h; simp [Ki] at h
        have h' := gKi_Fc hσ hc0 h
        split_ifs at h' with g1 g2
        · simp at h'
        · simp at h'; subst h'; exact hO2 _ hDc.nf hEcω hc0 g2
        · exact ihc (by simp [Term.size] at hs; omega) hKc v h'

end Googology.Trans.PoR.InaccPsi.R2.Bt

/-! ## The interface for `A = A_{ω·m+n}` (namespace `R2.Br`): corollaries at `L = Alist S m n` -/

namespace Googology.Trans.PoR.InaccPsi.R2.Br

open Ordinal Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq Tm

variable {S : InaccSeq.{0}} {σ : Ordinal.{0}} {m n : ℕ}

theorem OmT_lvl_le_CL (hσ : Base σ) {r : Term} (hc : CL S σ m n r) (hp : r.isPrin = true) :
    OmT 1 (lvl (Term.val S r)) ≤ Term.val S r := by
  apply Bt.OmT_lvl_le_CL <;> assumption

/-- **Lemma PARTS (b)** for the class. -/
theorem parts_b_CL (hσ : Base σ) {s a : Term} (hμ : Term.NF (.psiS s a)) {k : ℕ}
    (hk : Term.val S s = k) (hμσ : σ ≤ Term.val S (.psiS s a)) :
    ∀ (N : ℕ) (r : Term), r.size ≤ N → CL S σ m n r → r.isPrin = true →
      lvl (Term.val S r) = k → Term.KLt (.psiS s a) r a → Term.val S r < Term.val S (.psiS s a) := by
  apply Bt.parts_b_CL <;> assumption

/-! ## The level-`k` parts -/

/-- **Lemma KB** over `σ`, level `k ≥ 1`. -/
theorem KBs (hσ : Base σ) {s a : Term} (hμ : Term.NF (.psiS s a)) {k : ℕ} (hk0 : k ≠ 0)
    (hk : Term.val S s = k) (Y : Ordinal.{0})
    (hD : ∀ u : Term, u.size ≤ a.size → CL S σ m n u → DL S σ m n u)
    (hO1 : ∀ r : Term, r.size ≤ a.size → CL S σ m n r → r.isPrin = true →
      lvl (Term.val S r) = k → Term.val S r < Term.val S (.psiS s a) → ev σ (Ex S σ m n r) < Y)
    (hO2 : ∀ x : Tm, NF σ x → ev σ x < Om (ω : Ordinal.{0}) → ev σ x ≠ 0 → lvl (ev σ x) + 1 = k →
      ev σ (gFc σ x) < Y) :
    ∀ u : Term, CL S σ m n u → u.size ≤ a.size → Term.KLt (.psiS s a) u a →
      ∀ v ∈ Ki k (Ex S σ m n u), ev σ v < Y := by
  apply Bt.KBs <;> assumption

end Googology.Trans.PoR.InaccPsi.R2.Br

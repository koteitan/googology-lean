import Googology.Trans.PoR.InaccPsi.R2.BrLow4

/-!
# Lower bound, part 5: Lemma M for `E` on principal terms

The cases of the paper proof of Theorem LOW-0, Lemma M, for two principal terms `p < q` of the same level
`k`, through [W25] Prop 2.15 (`thb_lt_of_I`: `e_p < e_q` and `e_p^{*k} < E(q)`; `thb_lt_of_II`:
`E(p) ≤ e_q^{*k}`):
* `p = Ωₖ` (`PM_om`); `p = φ(a, b)` against `φ(c, d)` by Veblen's comparison and against `ψ` (`PM_phi`);
* `p = ψ_{Ω_{k+1}}(a)` against `φ(c, d)` (through a head of `c` or `d`) and against `ψ_{Ω_{k+1}}(b)` (with
  `F` increasing and Lemma KB) (`PM_psi`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Br

open Ordinal Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq Tm

variable {S : InaccSeq.{0}}

/-- The oracle of Lemma M for the pairs with a smaller sum of sizes. -/
def MO (S : InaccSeq.{0}) (N m : ℕ) : Prop :=
  ∀ x y : Term, x.size ≤ N → y.size ≤ N → x.size + y.size < m → Cw S x → Cw S y → Term.NF x →
    Term.NF y → Term.val S x < Term.val S y → ev 1 (E S x) < ev 1 (E S y)

/-- The oracle of Lemma D. -/
def DO (S : InaccSeq.{0}) (N : ℕ) : Prop := ∀ u : Term, u.size ≤ N → Cw S u → Term.NF u → DI S u

theorem E_om {b : Term} {kb : ℕ} (hkb : Term.val S b = kb) : E S (.om b) = th kb (par 0) := by
  simp only [E]; rw [hkb, natOf_nat]; rfl

theorem E_phi (c d : Term) : E S (.phi c d) = th (lvl (Term.val S (.phi c d)))
    (plus 1 (th (lvl (Term.val S (.phi c d)) + 1) (E S c)) (E S d)) := rfl

theorem E_psiS {s a : Term} {k : ℕ} (hk : Term.val S s = k) :
    E S (.psiS s a) = th k (plus 1 (Pk k) (Fc (E S a))) := by
  simp only [E]; rw [hk, natOf_nat]

/-- The data of a `φ`-term of level `k`. -/
theorem phi_data {N : ℕ} (hD : DO S N) {c d : Term} (hs : (Term.phi c d).size ≤ N)
    (hn : Term.NF (.phi c d)) (hc : Cw S (.phi c d)) :
    NF 1 (E S c) ∧ NF 1 (E S d) ∧ ev 1 (E S c) < OmT 1 (lvl (Term.val S (.phi c d)) + 1) ∧
      ev 1 (E S d) < OmT 1 (lvl (Term.val S (.phi c d)) + 1) := by
  have hDc := hD c (by simp [Term.size] at hs; omega) hc.1 hn.1
  have hDd := hD d (by simp [Term.size] at hs; omega) hc.2 hn.2.1
  obtain ⟨h1, h2⟩ := NF_phi_lt (S := S) hn
  have hvω := Cw_val_lt hc hn
  exact ⟨hDc.nf, hDd.nf,
    lt_of_lt_of_le hDc.lt (OmT_mono base_one (by have := lvl_mono hvω h1.le; omega)),
    lt_of_lt_of_le hDd.lt (OmT_mono base_one (by have := lvl_mono hvω h2.le; omega))⟩

/-- The code of a principal `q ≠ Ωₖ` is positive, and `E(q) = ϑ̄ₖ(code)`. -/
theorem code_pos {N : ℕ} (hD : DO S N) {q : Term} (hs : q.size ≤ N) (hn : Term.NF q) (hc : Cw S q)
    (hp : q.isPrin = true) (hnotom : ∀ b, q ≠ .om b) :
    ∃ e, E S q = th (lvl (Term.val S q)) e ∧ 0 < ev 1 e ∧ NF 1 (th (lvl (Term.val S q)) e) := by
  have hDq := hD q hs hc hn
  obtain ⟨-, e, he⟩ := hDq.prin hp
  refine ⟨e, he, ?_, he ▸ hDq.nf⟩
  cases q with
  | om b => exact absurd rfl (hnotom b)
  | phi c d =>
    obtain ⟨n1, n2, h1, _⟩ := phi_data hD hs hn hc
    rw [E_phi] at he
    cases he
    rw [ev_codephi n1 n2 h1]
    exact lt_of_lt_of_le (thb_pos base_one (dom_of_lt base_one (h1.trans (OmT_lt_succ base_one _))))
      le_self_add
  | psiS s a =>
    obtain ⟨⟨k, hk⟩, _, hca⟩ := hc
    rw [E_psiS hk, lvl_psiS s a hk] at he
    cases he
    have hDa := hD a (by simp [Term.size] at hs; omega) hca hn.2.1
    rw [ev_codepsi hDa.nf (hDa.lt.trans (OmT_succ_lt_Om_omega 1 _))]
    exact lt_of_lt_of_le (lt_of_le_of_lt zero_le (ev_Pk_bounds k).1) le_self_add
  | _ => simp [Term.isPrin, Term.isSC] at hp <;> exact absurd hc (by simp [Cw])

/-- The value of `Ωₖ` and its level. -/
theorem om_val {b : Term} (hc : Cw S (.om b)) :
    ∃ kb : ℕ, kb ≠ 0 ∧ Term.val S b = kb ∧ Term.val S (.om b) = OmT 1 kb ∧
      lvl (Term.val S (.om b)) = kb := by
  obtain ⟨kb, hkb0, hkb⟩ := hc
  refine ⟨kb, hkb0, hkb, by rw [val_om_of_Cw hkb, Om_nat_eq_OmT hkb0], ?_⟩
  rw [val_om_of_Cw hkb]; exact lvl_Om hkb0

/-- `Ωₖ` is the least value of level `k`: no principal term of level `k` is below `Ωₖ`. -/
theorem not_lt_om {p b : Term} (np : Term.NF p) (cp : Cw S p) (pp : p.isPrin = true) (cb : Cw S (.om b))
    (hk : lvl (Term.val S p) = lvl (Term.val S (.om b))) : ¬ Term.val S p < Term.val S (.om b) := by
  obtain ⟨kb, -, -, hv, hl⟩ := om_val cb
  intro h
  have := OmT_lvl_le np cp pp
  rw [hk, hl, ← hv] at this
  exact absurd h (not_lt.2 this)

/-- **Lemma M, `p = Ωₖ`.** -/
theorem PM_om {N : ℕ} (hD : DO S N) {b q : Term} (hsq : q.size ≤ N) (nq : Term.NF q)
    (cp : Cw S (.om b)) (cq : Cw S q) (pq : q.isPrin = true)
    (hk : lvl (Term.val S (.om b)) = lvl (Term.val S q))
    (hlt : Term.val S (.om b) < Term.val S q) : ev 1 (E S (.om b)) < ev 1 (E S q) := by
  have hnotom : ∀ b', q ≠ .om b' := by
    rintro b' rfl
    obtain ⟨kb, -, -, hv, hl⟩ := om_val cp
    obtain ⟨kb', -, -, hv', hl'⟩ := om_val cq
    rw [hl, hl'] at hk; subst hk
    rw [hv, hv'] at hlt; exact lt_irrefl _ hlt
  obtain ⟨e, he, hpos, hne⟩ := code_pos hD hsq nq cq pq hnotom
  obtain ⟨kb, -, hkb, -, hl⟩ := om_val cp
  rw [E_om hkb, he, ← hk, hl]
  rw [← hk, hl] at hne
  exact thb_lt_of_I base_one (NF_Omk kb) hne hpos
    (by rw [show Tm.star 1 kb (par 0) = 0 from rfl]; exact thb_pos base_one (NF.th_dom hne))

/-- The level-`k` parts of `x` and of `y` are level-`k` parts of the `φ`-code. -/
theorem Ki_codephi_sup {k : ℕ} {x y : Tm} (hx : NF 1 x) (hy : NF 1 y) (hxk : ev 1 x < OmT 1 (k + 1))
    (hyk : ev 1 y < OmT 1 (k + 1)) :
    Ki k x ⊆ Ki k (plus 1 (th (k + 1) x) y) ∧ Ki k y ⊆ Ki k (plus 1 (th (k + 1) x) y) := by
  have hnx : NF 1 (th (k + 1) x) := NF.cth hx (dom_of_lt base_one (hxk.trans (OmT_lt_succ base_one _)))
  have hKi : Ki k (th (k + 1) x) = Ki k x := by
    simp [Ki, show ¬ k + 1 < k by omega]
  by_cases h0 : y = par 0
  · subst h0
    have e : plus 1 (th (k + 1) x) (par 0) = th (k + 1) x := by simp [plus]
    rw [e, hKi]
    exact ⟨List.Subset.refl _, by simp [Ki]⟩
  · have hle : hd 1 y ≤ ev 1 (th (k + 1) x) :=
      (NF.hd_le_ev hy).trans (hyk.le.trans (NF.th_bounds base_one hnx).1)
    have e : plus 1 (th (k + 1) x) y = Tm.add (th (k + 1) x) y := by
      simp only [plus, h0, if_false, if_pos hle]
    rw [e]
    show Ki k x ⊆ Ki k (th (k + 1) x) ++ Ki k y ∧ Ki k y ⊆ Ki k (th (k + 1) x) ++ Ki k y
    rw [hKi]
    exact ⟨List.subset_append_left _ _, List.subset_append_right _ _⟩

/-- `E(head z)` is a level-`k` part of `E(z)`. -/
theorem head_mem_Ki {N : ℕ} (hD : DO S N) {z : Term} (hz : z.size ≤ N) (hn : Term.NF z) (hc : Cw S z)
    (hz0 : z ≠ .zero) {k : ℕ} (hk : lvl (Term.val S (Term.head z)) = k) :
    E S (Term.head z) ∈ Ki k (E S z) := by
  have hDz := hD _ hz hc hn
  cases z with
  | zero => exact absurd rfl hz0
  | add z1 z2 =>
    have hD1 := hD z1 (by simp [Term.size] at hz; omega) hc.1 hn.1
    obtain ⟨-, e, he⟩ := hD1.prin hn.2.2.1
    simp only [Term.head] at hk ⊢
    rw [hDz.add z1 z2 rfl, he, hk]
    simp [Ki]
  | inacc _ => exact absurd hc (by simp [Cw])
  | inaccW => exact absurd hc (by simp [Cw])
  | psiI _ _ => exact absurd hc (by simp [Cw])
  | phi c d =>
    obtain ⟨-, e, he⟩ := hDz.prin rfl
    simp only [Term.head] at hk ⊢
    rw [he, hk]; simp [Ki]
  | om b =>
    obtain ⟨-, e, he⟩ := hDz.prin rfl
    simp only [Term.head] at hk ⊢
    rw [he, hk]; simp [Ki]
  | psiS s a =>
    obtain ⟨-, e, he⟩ := hDz.prin rfl
    simp only [Term.head] at hk ⊢
    rw [he, hk]; simp [Ki]

/-- Through a head (case (II)): if `p ≤ z < q` and the level-`k` parts of `E(z)` are level-`k` parts of the
code of `q`, then `E(p) < E(q)`. -/
theorem via_head {N : ℕ} (hD : DO S N) {p q z : Term} (hsp : p.size ≤ N) (hsq : q.size ≤ N)
    (IHi : MO S N (p.size + q.size)) (np : Term.NF p) (cp : Cw S p) (pp : p.isPrin = true)
    {k : ℕ} (hkp : lvl (Term.val S p) = k) {ep eq : Tm} (hep : E S p = th k ep) (heq : E S q = th k eq)
    (nEp : NF 1 (th k ep)) (nEq : NF 1 (th k eq))
    (hsz : z.size < q.size) (hnz : Term.NF z) (hcz : Cw S z)
    (hpz : Term.val S p ≤ Term.val S z) (hzq : Term.val S z < OmT 1 (k + 1))
    (hsub : Ki k (E S z) ⊆ Ki k eq) : ev 1 (E S p) < ev 1 (E S q) := by
  have hz0 : z ≠ .zero := by
    rintro rfl
    exact absurd hpz (not_le.2 (pos_iff_ne_zero.2 (Term.val_ne_zero S np
      (Term.NF.ne_zero_of_isPrin pp))))
  have hhead : Term.val S p ≤ Term.val S (Term.head z) := by
    by_contra hl
    exact absurd hpz (not_le.2 (val_lt_of_head hnz (Term.isPrincipal_val S np pp) (not_le.1 hl)))
  have hpOm : OmT 1 k ≤ Term.val S p := hkp ▸ OmT_lvl_le np cp pp
  have hlvh : lvl (Term.val S (Term.head z)) = k :=
    lvl_of_th_bounds (hpOm.trans hhead) (lt_of_le_of_lt (val_head_le z) hzq)
  have hmem := hsub (head_mem_Ki hD (by omega) hnz hcz hz0 hlvh)
  have hle : ev 1 (E S p) ≤ ev 1 (E S (Term.head z)) := by
    rcases eq_or_lt_of_le hhead with he | he
    · rw [Term.eq_of_val_eq S np hnz.head he]
    · exact (IHi p (Term.head z) hsp (by have := Term.size_head_le z; omega)
        (by have := Term.size_head_le z; omega) cp (Cw_head hcz) np hnz.head he).le
  rw [hep, heq]
  rw [hep] at hle
  exact thb_lt_of_II base_one nEp nEq (hle.trans (le_star hmem))

end Googology.Trans.PoR.InaccPsi.R2.Br

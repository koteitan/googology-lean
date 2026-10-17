import Googology.Trans.PoR.InaccPsi.R2.BrLs11

/-!
# LOW-STEP, part 12: Lemma M for `p = φ(a, b)`, `p = ψ_{Ω_{k+1}}(a)` and the `A`-clause

* `PMs_phi`: `φ` against `φ` (Veblen's comparison), against `ψ_{Ω_{k+1}}`, against the `A`-clause;
* `PMs_psiS`: `ψ_{Ω_{k+1}}(a)` (`k ≥ 1`) against `φ` (through a head) and against `ψ_{Ω_{k+1}}(b)`
  (`F` increasing and Lemma KB);
* `PMs_psiA`: the `A`-clause against `φ` (through a head) and against the `A`-clause (Lemma PMAX and
  Lemma KB at level 0).

The statements are proved for `A` the sum of any list `L` of summands (namespace `R2.Bt`: `AA S L` the
sum of `L`, `kA S L` its length, `GoodL S L` where it is needed); the original statements for
`A = A_{ω·m+n}` (namespace `R2.Br`, the same names) follow as corollaries at `L = Alist S m n`.
-/

/-! ## The list version (namespace `R2.Bt`) -/

namespace Googology.Trans.PoR.InaccPsi.R2.Bt

open Googology.Trans.PoR.InaccPsi.R2.Br

open Ordinal Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq Googology.Trans.PoR.InaccPsi.R2.Br.Tm

variable {S : InaccSeq.{0}} {σ : Ordinal.{0}} {L : List Ordinal.{0}}

/-- The data of a `φ`-term of the class. -/
theorem phi_data_s (hσ : Base σ) {N : ℕ} (hD : DOs S σ L N) {c d : Term} (hs : (Term.phi c d).size ≤ N)
    (hc : CL S σ L (.phi c d)) (hn : Term.NF (.phi c d)) (hcc : CL S σ L c) (hcd : CL S σ L d) :
    NF σ (Ex S σ L c) ∧ NF σ (Ex S σ L d) ∧
      ev σ (Ex S σ L c) < OmT σ (lvl (Term.val S (.phi c d)) + 1) ∧
      ev σ (Ex S σ L d) < OmT σ (lvl (Term.val S (.phi c d)) + 1) := by
  have hDc := hD c (by simp [Term.size] at hs; omega) hcc
  have hDd := hD d (by simp [Term.size] at hs; omega) hcd
  obtain ⟨h1, h2⟩ := NF_phi_lt (S := S) hn
  have hvω := CL_val_lt hσ hc
  exact ⟨hDc.nf, hDd.nf,
    lt_of_lt_of_le hDc.lt (OmT_mono hσ (by have := lvl_mono hvω h1.le; omega)),
    lt_of_lt_of_le hDd.lt (OmT_mono hσ (by have := lvl_mono hvω h2.le; omega))⟩

/-- **Lemma M, `p = φ(a, b)`.** -/
theorem PMs_phi (hσ : Base σ) {N : ℕ} (hD : DOs S σ L N) {a b q : Term}
    (hsp : (Term.phi a b).size ≤ N) (hsq : q.size ≤ N) (IHi : MOs S σ L N ((Term.phi a b).size + q.size))
    (cp : CL S σ L (.phi a b)) (cq : CL S σ L q) (pq : q.isPrin = true)
    (hpσ : ¬ Term.val S (.phi a b) < σ) (hqσ : ¬ Term.val S q < σ)
    (hk : lvl (Term.val S (.phi a b)) = lvl (Term.val S q))
    (hlt : Term.val S (.phi a b) < Term.val S q) : ev σ (Ex S σ L (.phi a b)) < ev σ (Ex S σ L q) := by
  obtain ⟨np, ca, cb⟩ : Term.NF (.phi a b) ∧ CL S σ L a ∧ CL S σ L b := by
    cases cp with
    | par _ h => exact absurd h hpσ
    | phi hn _ ha hb => exact ⟨hn, ha, hb⟩
  set k := lvl (Term.val S (.phi a b)) with hkdef
  obtain ⟨n1, n2, h1, h2⟩ := phi_data_s hσ hD hsp cp np ca cb
  rw [← hkdef] at h1 h2
  have hep : Ex S σ L (.phi a b) = th k (plus σ (th (k + 1) (Ex S σ L a)) (Ex S σ L b)) := by
    rw [Ex, EL_phi hpσ]
  have nEp : NF σ (th k (plus σ (th (k + 1) (Ex S σ L a)) (Ex S σ L b))) := hep ▸ (hD _ hsp cp).nf
  obtain ⟨va, vb⟩ := NF_phi_lt (S := S) np
  have hsa : a.size < (Term.phi a b).size := by simp only [Term.size]; omega
  have hsb : b.size < (Term.phi a b).size := by simp only [Term.size]; omega
  have hEaq : ev σ (Ex S σ L a) < ev σ (Ex S σ L q) :=
    IHi a q (by omega) hsq (by omega) ca cq (va.trans hlt)
  have hEbq : ev σ (Ex S σ L b) < ev σ (Ex S σ L q) :=
    IHi b q (by omega) hsq (by omega) cb cq (vb.trans hlt)
  have hqω := CL_val_lt hσ cq
  cases cq with
  | par _ h => exact absurd h hqσ
  | add => simp [Term.isPrin, Term.isSC] at pq
  | @om b' kb nb vb' kb0 hkb => exact absurd hlt (not_lt_om_s hσ cp rfl (CL.om nb vb' kb0 hkb) hqσ hk)
  | @phi c d nq vq cc cd =>
    obtain ⟨m1, m2, g1, g2⟩ := phi_data_s hσ hD hsq (CL.phi nq vq cc cd) nq cc cd
    rw [← hk] at g1 g2
    have heq : Ex S σ L (.phi c d) = th k (plus σ (th (k + 1) (Ex S σ L c)) (Ex S σ L d)) := by
      rw [Ex, EL_phi hqσ, ← hk]
    have nEq : NF σ (th k (plus σ (th (k + 1) (Ex S σ L c)) (Ex S σ L d))) :=
      heq ▸ (hD _ hsq (CL.phi nq vq cc cd)).nf
    have hsc : c.size < (Term.phi c d).size := by simp only [Term.size]; omega
    have hsd : d.size < (Term.phi c d).size := by simp only [Term.size]; omega
    have hqk : Term.val S (.phi c d) < OmT 1 (k + 1) := by
      have := lvl_lt hqω; rwa [← hk] at this
    rcases veblen_lt_veblen_iff.1 hlt with ⟨hac, hbd⟩ | ⟨hac, hbq⟩ | ⟨hca, hpd⟩
    · have e := Term.eq_of_val_eq S np.1 nq.1 hac
      subst e
      have hbd' := IHi b d (by omega) (by omega) (by omega) cb cd hbd
      rw [hep, heq]
      refine thb_lt_of_I hσ nEp nEq ?_ (gstar_codephi_lt hσ n1 n2 h1 h2 (heq ▸ hEaq) (heq ▸ hEbq))
      rw [gev_codephi hσ n1 n2 h1, gev_codephi hσ n1 m2 h1]
      exact add_lt_add_right hbd' _
    · have hac' := IHi a c (by omega) (by omega) (by omega) ca cc hac
      have hthc : NF σ (th (k + 1) (Ex S σ L c)) :=
        NF.cth m1 (dom_of_lt hσ (g1.trans (OmT_lt_succ hσ _)))
      have htha : NF σ (th (k + 1) (Ex S σ L a)) :=
        NF.cth n1 (dom_of_lt hσ (h1.trans (OmT_lt_succ hσ _)))
      have h3 : ev σ (th (k + 1) (Ex S σ L a)) < ev σ (th (k + 1) (Ex S σ L c)) := by
        refine thb_lt_of_I hσ htha hthc hac' ?_
        rw [show Tm.star σ (k + 1) (Ex S σ L a) = 0 by unfold Tm.star; rw [Ki_nil_of_lt hσ n1 h1]; rfl]
        exact thb_pos hσ (NF.th_dom hthc)
      have hbq' : ev σ (Ex S σ L b) < ev σ (Ex S σ L (.phi c d)) :=
        IHi b _ (by omega) hsq (by omega) cb (CL.phi nq vq cc cd) hbq
      rw [hep, heq]
      refine thb_lt_of_I hσ nEp nEq ?_ (gstar_codephi_lt hσ n1 n2 h1 h2 (heq ▸ hEaq) (heq ▸ hbq'))
      rw [gev_codephi hσ n1 n2 h1, gev_codephi hσ m1 m2 g1]
      refine lt_of_lt_of_le ?_ le_self_add
      exact NF.th_principal hσ hthc h3 (h2.trans_le (NF.th_bounds hσ hthc).1)
    · have hdq : Term.val S d < OmT 1 (k + 1) := (NF_phi_lt (S := S) nq).2.trans hqk
      exact via_head_s hσ hD hsp hsq IHi cp rfl hpσ hkdef.symm hep heq nEp nEq hsd cd hpd.le hdq
        (gKi_codephi_sup hσ m1 m2 g1 g2).2
  | @psiS t b' k' nq vq hk0' hk' hbω hcb' =>
    have hkk : k' = k := by rw [hk, lvl_psiS t b' hk']
    rw [hkk] at hk' hk0'
    have hnat : natOf (Term.val S t) ≠ 0 := by rw [hk', natOf_nat]; exact hk0'
    have heq : Ex S σ L (.psiS t b') = th k (plus σ (Pk k) (gFc σ (Ex S σ L b'))) := by
      rw [Ex, EL_psiS hqσ hnat, hk', natOf_nat]
    have nEq : NF σ (th k (plus σ (Pk k) (gFc σ (Ex S σ L b')))) :=
      heq ▸ (hD _ hsq (CL.psiS nq vq hk0' hk' hbω hcb')).nf
    have hDb' := hD b' (by simp [Term.size] at hsq; omega) hcb'
    have hEbω : ev σ (Ex S σ L b') < Om (ω : Ordinal.{0}) := hDb'.lt.trans (OmT_succ_lt_Om_omega σ _)
    rw [hep, heq]
    refine thb_lt_of_I hσ nEp nEq ?_ (gstar_codephi_lt hσ n1 n2 h1 h2 (heq ▸ hEaq) (heq ▸ hEbq))
    rw [gev_codepsi hσ hDb'.nf hEbω]
    exact lt_of_lt_of_le (gcodephi_lt_Pk hσ n1 n2 h1 h2) le_self_add
  | @psiA t c'' nq vq ht0 hnz hcv hzθ hcz =>
    have hk0 : k = 0 := by rw [hk]; exact psiA_lvl ht0
    obtain ⟨hE, hGnf, hP1, _, hz2, _, _⟩ := Acode hσ nq vq ht0 hcz hzθ (fun u hu hcu => hD u (by omega) hcu)
    have heq : Ex S σ L (.psiS t c'') = th k (plus σ (GcT S σ (EL S σ (kA S L))
        (pmax S (dropT (kA S L) c''))) (Ex S σ L (dropT (kA S L) c''))) := by rw [hE, hk0]
    have nEq := heq ▸ (hD _ hsq (CL.psiA nq vq ht0 hnz hcv hzθ hcz)).nf
    have hDz := hD _ (by have := dropT_size (kA S L) c''; simp [Term.size] at hsq; omega) hcz
    rw [hep, heq]
    refine thb_lt_of_I hσ nEp nEq ?_ (gstar_codephi_lt hσ n1 n2 h1 h2 (heq ▸ hEaq) (heq ▸ hEbq))
    rw [ev_plus hσ hGnf hDz.nf]
    refine lt_of_lt_of_le ?_ (hP1.trans le_self_add)
    rw [hk0] at h1 h2 ⊢
    exact (gcodephi_lt_Pk hσ n1 n2 h1 h2).trans ((gev_Pk_bounds hσ 0).2.trans (gev_Pk_bounds hσ 1).1)

/-- **Lemma M, `p = ψ_{Ω_{k+1}}(a)`, `k ≥ 1`.** -/
theorem PMs_psiS (hσ : Base σ) {N : ℕ} (hD : DOs S σ L N) {s a q : Term}
    (hsp : (Term.psiS s a).size ≤ N) (hsq : q.size ≤ N) (IHi : MOs S σ L N ((Term.psiS s a).size + q.size))
    {k : ℕ} (np : Term.NF (.psiS s a)) (hpσ : ¬ Term.val S (.psiS s a) < σ) (hk0 : k ≠ 0)
    (hks : Term.val S s = k) (haω : Term.val S a < Om (ω : Ordinal.{0})) (ca : CL S σ L a)
    (cq : CL S σ L q) (pq : q.isPrin = true) (hqσ : ¬ Term.val S q < σ)
    (hk : lvl (Term.val S (.psiS s a)) = lvl (Term.val S q))
    (hlt : Term.val S (.psiS s a) < Term.val S q) : ev σ (Ex S σ L (.psiS s a)) < ev σ (Ex S σ L q) := by
  have cp : CL S σ L (.psiS s a) := CL.psiS np hpσ hk0 hks haω ca
  have hlp : lvl (Term.val S (.psiS s a)) = k := lvl_psiS s a hks
  have hnat : natOf (Term.val S s) ≠ 0 := by rw [hks, natOf_nat]; exact hk0
  have hep : Ex S σ L (.psiS s a) = th k (plus σ (Pk k) (gFc σ (Ex S σ L a))) := by
    rw [Ex, EL_psiS hpσ hnat, hks, natOf_nat]
  have nEp : NF σ (th k (plus σ (Pk k) (gFc σ (Ex S σ L a)))) := hep ▸ (hD _ hsp cp).nf
  have hsa : a.size < (Term.psiS s a).size := by simp only [Term.size]; omega
  have hDa := hD a (by omega) ca
  have hEaω : ev σ (Ex S σ L a) < Om (ω : Ordinal.{0}) := hDa.lt.trans (OmT_succ_lt_Om_omega σ _)
  have hqω := CL_val_lt hσ cq
  have hqk : Term.val S q < OmT 1 (k + 1) := by have := lvl_lt hqω; rwa [← hk, hlp] at this
  cases cq with
  | par _ h => exact absurd h hqσ
  | add => simp [Term.isPrin, Term.isSC] at pq
  | @om b' kb nb vb' kb0 hkb => exact absurd hlt (not_lt_om_s hσ cp rfl (CL.om nb vb' kb0 hkb) hqσ hk)
  | @psiA t c'' nq vq ht0 _ _ _ _ =>
    rw [hlp, psiA_lvl ht0] at hk; exact absurd hk hk0
  | @phi c d nq vq cc cd =>
    obtain ⟨m1, m2, g1, g2⟩ := phi_data_s hσ hD hsq (CL.phi nq vq cc cd) nq cc cd
    rw [← hk, hlp] at g1 g2
    have heq : Ex S σ L (.phi c d) = th k (plus σ (th (k + 1) (Ex S σ L c)) (Ex S σ L d)) := by
      rw [Ex, EL_phi hqσ, ← hk, hlp]
    have nEq : NF σ (th k (plus σ (th (k + 1) (Ex S σ L c)) (Ex S σ L d))) :=
      heq ▸ (hD _ hsq (CL.phi nq vq cc cd)).nf
    have hsc : c.size < (Term.phi c d).size := by simp only [Term.size]; omega
    have hsd : d.size < (Term.phi c d).size := by simp only [Term.size]; omega
    obtain ⟨hcq, hdq⟩ := NF_phi_lt (S := S) nq
    have hSC : SC (Term.val S (.psiS s a)) := Term.SC_val S np rfl
    have hcd : Term.val S (.psiS s a) ≤ Term.val S c ∨ Term.val S (.psiS s a) ≤ Term.val S d := by
      by_contra hno
      push Not at hno
      have := hSC.2 _ hno.1 _ hno.2
      exact absurd hlt (not_lt.2 this.le)
    rcases hcd with h | h
    · exact via_head_s hσ hD hsp hsq IHi cp rfl hpσ hlp hep heq nEp nEq hsc cc h (hcq.trans hqk)
        (gKi_codephi_sup hσ m1 m2 g1 g2).1
    · exact via_head_s hσ hD hsp hsq IHi cp rfl hpσ hlp hep heq nEp nEq hsd cd h (hdq.trans hqk)
        (gKi_codephi_sup hσ m1 m2 g1 g2).2
  | @psiS t b' k' nq vq hk0' hk' hbω hcb' =>
    have hkk : k' = k := by rw [← lvl_psiS t b' hk', ← hk, hlp]
    rw [hkk] at hk' hk0'
    have cq' : CL S σ L (.psiS t b') := CL.psiS nq vq hk0' hk' hbω hcb'
    have hnat' : natOf (Term.val S t) ≠ 0 := by rw [hk', natOf_nat]; exact hk0'
    have heq : Ex S σ L (.psiS t b') = th k (plus σ (Pk k) (gFc σ (Ex S σ L b'))) := by
      rw [Ex, EL_psiS hqσ hnat', hk', natOf_nat]
    have nEq : NF σ (th k (plus σ (Pk k) (gFc σ (Ex S σ L b')))) := heq ▸ (hD _ hsq cq').nf
    have hsb' : b'.size < (Term.psiS t b').size := by simp only [Term.size]; omega
    have hDb' := hD b' (by omega) hcb'
    have hEbω : ev σ (Ex S σ L b') < Om (ω : Ordinal.{0}) := hDb'.lt.trans (OmT_succ_lt_Om_omega σ _)
    have hab : Term.val S a < Term.val S b' := by
      by_contra hge
      rw [not_lt] at hge
      have := (psi_mono (S := S) (InR_Om_succ (S := S) (Term.val S t)) hge).1
      simp only [Term.val] at hlt
      rw [hks, ← hk'] at hlt
      exact absurd hlt (not_lt.2 this)
    have hEab := IHi a b' (by omega) (by omega) (by omega) ca hcb' hab
    have hFab := gFc_lt hσ hDa.nf hDb'.nf hEbω hEab
    have hcodeq_pos : 0 < ev σ (plus σ (Pk k) (gFc σ (Ex S σ L b'))) := by
      rw [gev_codepsi hσ hDb'.nf hEbω]
      exact lt_of_lt_of_le (lt_of_le_of_lt zero_le (gev_Pk_bounds hσ k).1) le_self_add
    have hY : OmT σ k < ev σ (th k (plus σ (Pk k) (gFc σ (Ex S σ L b')))) := gOmT_lt_th hσ nEq hcodeq_pos
    rw [hep, heq]
    refine thb_lt_of_I hσ nEp nEq ?_ ?_
    · rw [gev_codepsi hσ hDa.nf hEaω, gev_codepsi hσ hDb'.nf hEbω]
      exact add_lt_add_right hFab _
    · refine star_le_of σ (fun u hu => ?_) (lt_of_le_of_lt zero_le hY)
      rcases List.mem_append.1 (Ki_plus σ k _ _ hu) with h | h
      · rw [Ki_Pk] at h; simp at h
      · have hO2 : ∀ x : Tm, NF σ x → ev σ x < Om (ω : Ordinal.{0}) → ev σ x ≠ 0 →
            lvl (ev σ x) + 1 = k → ev σ (gFc σ x) < ev σ (th k (plus σ (Pk k) (gFc σ (Ex S σ L b')))) := by
          intro x hx hxω hx0 hlx
          have hnF := gNF_Fc hσ hx hxω
          rw [gFc_pos hσ hx0] at hnF ⊢
          rw [hlx] at hnF ⊢
          refine thb_lt_of_I hσ hnF nEq ?_ ?_
          · rw [gev_codepsi hσ hDb'.nf hEbω]
            have := gFarg_lt (m := lvl (ev σ x)) hσ hx (glvl_lt σ hxω)
            rw [hlx] at this
            exact lt_of_lt_of_le (this.trans (gev_Pk_bounds hσ k).1) le_self_add
          · refine star_le_of σ (fun w hw => ?_) (lt_of_le_of_lt zero_le hY)
            have hxl : ev σ x < OmT σ (lvl (ev σ x) + 1) := glvl_lt σ hxω
            have := gstar_Farg hσ hx hxl w (by rw [hlx]; exact hw)
            rw [hlx] at this
            exact lt_of_le_of_lt this hY
        by_cases ha0 : ev σ (Ex S σ L a) = 0
        · rw [gFc_zero hσ ha0] at h; simp [Ki] at h
        have h' := gKi_Fc hσ ha0 h
        split_ifs at h' with g1 g2
        · simp at h'
        · simp at h'; subst h'; exact hO2 _ hDa.nf hEaω ha0 g2
        · refine KBs hσ np hk0 hks _ (fun u hu hcu => hD u (by omega) hcu) ?_ hO2 a ca le_rfl np.2.2 u h'
          intro r hsr hcr hpr hlr hrp
          rw [← heq]
          exact IHi r _ (by omega) hsq (by omega) hcr cq' (hrp.trans hlt)

/-- `pv` determines `pmax`. -/
theorem pmax_eq_of_pv {ζ ζ' : Term} (hn : Term.NF ζ) (hn' : Term.NF ζ')
    (h : pv S (pmax S ζ) = pv S (pmax S ζ')) : pmax S ζ = pmax S ζ' := by
  have pos : ∀ {z u : Term}, Term.NF z → pmax S z = some u → 0 < Term.val S u := by
    intro z u hz hu
    obtain ⟨hu1, ⟨s1, d, rfl, _⟩, _⟩ := (pmaxL_spec (S := S) (topAtoms z)).2 _ hu
    exact (Term.SC_val S (topAtom_NF hz hu1) rfl).1
  rcases hp : pmax S ζ with _ | u <;> rcases hp' : pmax S ζ' with _ | u'
  · rfl
  · rw [hp, hp'] at h; exact absurd h.symm (pos hn' hp').ne'
  · rw [hp, hp'] at h; exact absurd h (pos hn hp).ne'
  · rw [hp, hp'] at h
    have h1 := ((pmaxL_spec (S := S) (topAtoms ζ)).2 _ hp).1
    have h2 := ((pmaxL_spec (S := S) (topAtoms ζ')).2 _ hp').1
    rw [Term.eq_of_val_eq S (topAtom_NF hn h1) (topAtom_NF hn' h2) h]

/-- **Lemma M, the `A`-clause.** -/
theorem PMs_psiA (hσ : Base σ) {N : ℕ} (hD : DOs S σ L N) {s c q : Term}
    (hsp : (Term.psiS s c).size ≤ N) (hsq : q.size ≤ N) (IHi : MOs S σ L N ((Term.psiS s c).size + q.size))
    (np : Term.NF (.psiS s c)) (hpσ : ¬ Term.val S (.psiS s c) < σ) (hs0 : Term.val S s = 0)
    (hnz : Term.NF (dropT (kA S L) c)) (hcv : Term.val S c = AA S L + Term.val S (dropT (kA S L) c))
    (hzθ : Term.val S (dropT (kA S L) c) < ConjT.th S) (hcz : CL S σ L (dropT (kA S L) c))
    (cq : CL S σ L q) (pq : q.isPrin = true) (hqσ : ¬ Term.val S q < σ)
    (hk : lvl (Term.val S (.psiS s c)) = lvl (Term.val S q))
    (hlt : Term.val S (.psiS s c) < Term.val S q) : ev σ (Ex S σ L (.psiS s c)) < ev σ (Ex S σ L q) := by
  have cp : CL S σ L (.psiS s c) := CL.psiA np hpσ hs0 hnz hcv hzθ hcz
  have hlp : lvl (Term.val S (.psiS s c)) = 0 := psiA_lvl hs0
  set ζ := dropT (kA S L) c with hζdef
  have hsz : ζ.size < (Term.psiS s c).size := by
    have := dropT_size (kA S L) c; rw [← hζdef] at this; simp only [Term.size]; omega
  obtain ⟨hE, hGnf, hP1, hGP, hz2, hGnone, hGsome⟩ :=
    Acode hσ np hpσ hs0 hcz hzθ (fun u hu hcu => hD u (by omega) hcu)
  rw [← hζdef] at hE hGnf hP1 hGP hz2 hGnone hGsome
  set G := GcT S σ (EL S σ (kA S L)) (pmax S ζ) with hGdef
  have nEp : NF σ (th 0 (plus σ G (Ex S σ L ζ))) := hE ▸ (hD _ hsp cp).nf
  have hDz := hD ζ (by omega) hcz
  have hqω := CL_val_lt hσ cq
  have hqk : Term.val S q < OmT 1 (0 + 1) := by have := lvl_lt hqω; rwa [← hk, hlp] at this
  cases cq with
  | par _ h => exact absurd h hqσ
  | add => simp [Term.isPrin, Term.isSC] at pq
  | @om b' kb nb vb' kb0 hkb =>
    have hl' : lvl (Term.val S (.om b')) = kb := by rw [val_om_of_Cw hkb]; exact lvl_Om kb0
    rw [hlp, hl'] at hk; exact absurd hk.symm kb0
  | @psiS t b' k' nq vq hk0' hk' _ _ =>
    rw [hlp, lvl_psiS t b' hk'] at hk; exact absurd hk.symm hk0'
  | @phi c' d nq vq cc cd =>
    obtain ⟨m1, m2, g1, g2⟩ := phi_data_s hσ hD hsq (CL.phi nq vq cc cd) nq cc cd
    rw [← hk, hlp] at g1 g2
    have heq : Ex S σ L (.phi c' d) = th 0 (plus σ (th (0 + 1) (Ex S σ L c')) (Ex S σ L d)) := by
      rw [Ex, EL_phi hqσ, ← hk, hlp]
    have nEq := heq ▸ (hD _ hsq (CL.phi nq vq cc cd)).nf
    have hsc : c'.size < (Term.phi c' d).size := by simp only [Term.size]; omega
    have hsd : d.size < (Term.phi c' d).size := by simp only [Term.size]; omega
    obtain ⟨hcq, hdq⟩ := NF_phi_lt (S := S) nq
    have hSC : SC (Term.val S (.psiS s c)) := Term.SC_val S np rfl
    have hcd : Term.val S (.psiS s c) ≤ Term.val S c' ∨ Term.val S (.psiS s c) ≤ Term.val S d := by
      by_contra hno
      push Not at hno
      have := hSC.2 _ hno.1 _ hno.2
      exact absurd hlt (not_lt.2 this.le)
    rcases hcd with h | h
    · exact via_head_s hσ hD hsp hsq IHi cp rfl hpσ hlp hE heq nEp nEq hsc cc h (hcq.trans hqk)
        (gKi_codephi_sup hσ m1 m2 g1 g2).1
    · exact via_head_s hσ hD hsp hsq IHi cp rfl hpσ hlp hE heq nEp nEq hsd cd h (hdq.trans hqk)
        (gKi_codephi_sup hσ m1 m2 g1 g2).2
  | @psiA t c'' nq vq ht0 hnz' hcv' hzθ' hcz' =>
    have cq' : CL S σ L (.psiS t c'') := CL.psiA nq vq ht0 hnz' hcv' hzθ' hcz'
    set ζ' := dropT (kA S L) c'' with hζ'def
    have hsz' : ζ'.size < (Term.psiS t c'').size := by
      have := dropT_size (kA S L) c''; rw [← hζ'def] at this; simp only [Term.size]; omega
    obtain ⟨hE', hGnf', hP1', hGP', hz2', hGnone', hGsome'⟩ :=
      Acode hσ nq vq ht0 hcz' hzθ' (fun u hu hcu => hD u (by omega) hcu)
    rw [← hζ'def] at hE' hGnf' hP1' hGP' hz2' hGnone' hGsome'
    set G' := GcT S σ (EL S σ (kA S L)) (pmax S ζ') with hG'def
    have nEq : NF σ (th 0 (plus σ G' (Ex S σ L ζ'))) := hE' ▸ (hD _ hsq cq').nf
    have hDz' := hD ζ' (by omega) hcz'
    -- `ζ < ζ'`
    have hcc : Term.val S c < Term.val S c'' := by
      have h1 : Term.val S (.psiS s c) = S.psi (Term.val S c) (Om 1) := by
        simp only [Term.val]; rw [hs0, zero_add]
      have h2 : Term.val S (.psiS t c'') = S.psi (Term.val S c'') (Om 1) := by
        simp only [Term.val]; rw [ht0, zero_add]
      rw [h1, h2] at hlt
      exact lt_of_psi_lt InR_Om1 hlt
    have hζζ' : Term.val S ζ < Term.val S ζ' := by
      rw [hcv, hcv'] at hcc; exact (add_lt_add_iff_left _).1 hcc
    have hEzz := IHi ζ ζ' (by omega) (by omega) (by omega) hcz hcz' hζζ'
    have hpm := pmax_mono hnz hnz' hζζ' (hzθ'.trans th_lt_Om2)
    have hY : OmT σ 0 < ev σ (th 0 (plus σ G' (Ex S σ L ζ'))) := by
      refine gOmT_lt_th hσ nEq ?_
      rw [ev_plus hσ hGnf' hDz'.nf]
      exact lt_of_lt_of_le (lt_of_lt_of_le (lt_of_le_of_lt zero_le (gev_Pk_bounds hσ 1).1) hP1') le_self_add
    rw [hE, hE']
    refine thb_lt_of_I hσ nEp nEq ?_ ?_
    · rw [ev_plus hσ hGnf hDz.nf, ev_plus hσ hGnf' hDz'.nf]
      rcases eq_or_lt_of_le hpm with he | he
      · have := pmax_eq_of_pv hnz hnz' he
        have hGG : G = G' := by rw [hGdef, hG'def, this]
        rw [hGG]; exact add_lt_add_right hEzz _
      · -- `G < G'`
        rcases hp' : pmax S ζ' with _ | u'
        · rw [hp'] at he; exact absurd he (not_lt.2 zero_le)
        obtain ⟨s1', d', rfl, hs1', hdc', hnu', hdω', hdsz', hu1', hG'e⟩ := hGsome' _ hp'
        have hDd' := hD d' (by omega) hdc'
        have hEdω' : ev σ (Ex S σ L d') < Om (ω : Ordinal.{0}) := hDd'.lt.trans (OmT_succ_lt_Om_omega σ _)
        have hGG' : ev σ G < ev σ G' := by
          rw [show G' = GT σ (Ex S σ L d') from hG'e]
          rcases hp : pmax S ζ with _ | u
          · rw [show G = Pk 1 from hGnone hp]
            exact Pk_lt_GT hσ hDd'.nf hEdω' (le_max_right _ _)
          · obtain ⟨s1, d, rfl, hs1, hdc, hnu, hdω, hdsz, hu1, hGe⟩ := hGsome _ hp
            rw [show G = GT σ (Ex S σ L d) from hGe]
            have hDd := hD d (by omega) hdc
            rw [hp, hp'] at he
            have hdd : Term.val S d < Term.val S d' := by
              simp only [pv, Term.val] at he
              rw [hs1, hs1'] at he
              exact lt_of_psi_lt (InR_Om_succ (S := S) 1) he
            exact GT_lt hσ hDd.nf hDd'.nf hEdω' (IHi d d' (by omega) (by omega) (by omega) hdc hdc' hdd)
        have hG'P : IsPrincipal (· + ·) (ev σ G') := hGP'
        refine lt_of_lt_of_le (hG'P hGG' ?_) le_self_add
        exact hz2.trans ((gev_Pk_bounds hσ 1).1.trans_le hP1')
    · -- the star
      refine star_le_of σ (fun u hu => ?_) (lt_of_le_of_lt zero_le hY)
      have hO1 : ∀ r : Term, r.size ≤ c.size → CL S σ L r → r.isPrin = true →
          lvl (Term.val S r) = 0 → Term.val S r < Term.val S (.psiS s c) →
          ev σ (Ex S σ L r) < ev σ (th 0 (plus σ G' (Ex S σ L ζ'))) := by
        intro r hsr hcr hpr _ hrp
        have hsr' : r.size < (Term.psiS s c).size := by simp only [Term.size]; omega
        rw [← hE']
        exact IHi r _ (by omega) hsq (by omega) hcr cq' (hrp.trans hlt)
      have hKz : Term.KLt (.psiS s c) ζ c := KLt_dropT _ c np.2.2
      have hμσ : σ ≤ Term.val S (.psiS s c) := not_lt.1 hpσ
      rcases List.mem_append.1 (Ki_plus σ 0 _ _ hu) with h | h
      · -- the level-0 parts of `G`
        rcases hp : pmax S ζ with _ | u0
        · rw [show G = Pk 1 from hGnone hp] at h; simp [Pk, Omk, Ki] at h
        · obtain ⟨s1, d, rfl, hs1, hdc, hnu, hdω, hdsz, hu1, hGe⟩ := hGsome _ hp
          rw [show G = GT σ (Ex S σ L d) from hGe] at h
          unfold GT at h
          simp only [Ki, show ¬ (max (lvl (ev σ (Ex S σ L d))) 1 + 1 < 0) by omega,
            show max (lvl (ev σ (Ex S σ L d))) 1 + 1 ≠ 0 by omega, if_false] at h
          unfold gFarg at h
          rcases List.mem_append.1 (Ki_plus σ 0 _ _ h) with h | h
          · rw [Ki_Omk_of_gt (by omega)] at h; simp at h
          · rcases List.mem_append.1 (Ki_plus σ 0 _ _ h) with h | h
            · rw [Ki_Omk_of_gt (by omega)] at h; simp at h
            · -- `d` is visited from `p`
              have hKa : Term.KLt (.psiS s c) (.psiS s1 d) c := KLt_topAtom hKz hu1
              have hKd : Term.KLt (.psiS s c) d c := by
                rcases hKa with hKa | ⟨_, _, hKd⟩
                · exfalso
                  have h1 := (Term.cmp_lt_iff S hnu np).1 hKa
                  have h2 := (Term.val_psiS_bounds S s1 d).1
                  have h3 := (Term.val_psiS_bounds S s c).2
                  rw [hs1] at h2; rw [hs0, zero_add] at h3
                  exact absurd (h2.trans (h1.trans h3)) (lt_irrefl _)
                · exact hKd
              have hdsz2 : d.size ≤ c.size := by
                have := dropT_size (kA S L) c; rw [← hζdef] at this; omega
              exact KB0 hσ np hs0 hμσ _ (N := c.size) (fun u hu hcu => hD u (by simp only [Term.size] at hsp; omega) hcu)
                hO1 d hdc hdsz2 hKd u h
      · have hzc : ζ.size ≤ c.size := by
          have := dropT_size (kA S L) c; rw [← hζdef] at this; exact this
        exact KB0 hσ np hs0 hμσ _ (N := c.size) (fun u hu hcu => hD u (by simp only [Term.size] at hsp; omega) hcu)
          hO1 ζ hcz hzc hKz u h

end Googology.Trans.PoR.InaccPsi.R2.Bt

/-! ## The interface for `A = A_{ω·m+n}` (namespace `R2.Br`): corollaries at `L = Alist S m n` -/

namespace Googology.Trans.PoR.InaccPsi.R2.Br

open Ordinal Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq Tm

variable {S : InaccSeq.{0}} {σ : Ordinal.{0}} {m n : ℕ}

/-- The data of a `φ`-term of the class. -/
theorem phi_data_s (hσ : Base σ) {N : ℕ} (hD : DOs S σ m n N) {c d : Term} (hs : (Term.phi c d).size ≤ N)
    (hc : CL S σ m n (.phi c d)) (hn : Term.NF (.phi c d)) (hcc : CL S σ m n c) (hcd : CL S σ m n d) :
    NF σ (Ex S σ m n c) ∧ NF σ (Ex S σ m n d) ∧
      ev σ (Ex S σ m n c) < OmT σ (lvl (Term.val S (.phi c d)) + 1) ∧
      ev σ (Ex S σ m n d) < OmT σ (lvl (Term.val S (.phi c d)) + 1) := by
  apply Bt.phi_data_s <;> assumption

/-- **Lemma M, `p = φ(a, b)`.** -/
theorem PMs_phi (hσ : Base σ) {N : ℕ} (hD : DOs S σ m n N) {a b q : Term}
    (hsp : (Term.phi a b).size ≤ N) (hsq : q.size ≤ N) (IHi : MOs S σ m n N ((Term.phi a b).size + q.size))
    (cp : CL S σ m n (.phi a b)) (cq : CL S σ m n q) (pq : q.isPrin = true)
    (hpσ : ¬ Term.val S (.phi a b) < σ) (hqσ : ¬ Term.val S q < σ)
    (hk : lvl (Term.val S (.phi a b)) = lvl (Term.val S q))
    (hlt : Term.val S (.phi a b) < Term.val S q) : ev σ (Ex S σ m n (.phi a b)) < ev σ (Ex S σ m n q) := by
  apply Bt.PMs_phi <;> assumption

/-- **Lemma M, `p = ψ_{Ω_{k+1}}(a)`, `k ≥ 1`.** -/
theorem PMs_psiS (hσ : Base σ) {N : ℕ} (hD : DOs S σ m n N) {s a q : Term}
    (hsp : (Term.psiS s a).size ≤ N) (hsq : q.size ≤ N) (IHi : MOs S σ m n N ((Term.psiS s a).size + q.size))
    {k : ℕ} (np : Term.NF (.psiS s a)) (hpσ : ¬ Term.val S (.psiS s a) < σ) (hk0 : k ≠ 0)
    (hks : Term.val S s = k) (haω : Term.val S a < Om (ω : Ordinal.{0})) (ca : CL S σ m n a)
    (cq : CL S σ m n q) (pq : q.isPrin = true) (hqσ : ¬ Term.val S q < σ)
    (hk : lvl (Term.val S (.psiS s a)) = lvl (Term.val S q))
    (hlt : Term.val S (.psiS s a) < Term.val S q) : ev σ (Ex S σ m n (.psiS s a)) < ev σ (Ex S σ m n q) := by
  apply Bt.PMs_psiS <;> assumption

/-- `pv` determines `pmax`. -/
theorem pmax_eq_of_pv {ζ ζ' : Term} (hn : Term.NF ζ) (hn' : Term.NF ζ')
    (h : pv S (pmax S ζ) = pv S (pmax S ζ')) : pmax S ζ = pmax S ζ' := by
  apply Bt.pmax_eq_of_pv <;> assumption

/-- **Lemma M, the `A`-clause.** -/
theorem PMs_psiA (hσ : Base σ) {N : ℕ} (hD : DOs S σ m n N) {s c q : Term}
    (hsp : (Term.psiS s c).size ≤ N) (hsq : q.size ≤ N) (IHi : MOs S σ m n N ((Term.psiS s c).size + q.size))
    (np : Term.NF (.psiS s c)) (hpσ : ¬ Term.val S (.psiS s c) < σ) (hs0 : Term.val S s = 0)
    (hnz : Term.NF (dropT (kA S m n) c)) (hcv : Term.val S c = AA S m n + Term.val S (dropT (kA S m n) c))
    (hzθ : Term.val S (dropT (kA S m n) c) < ConjT.th S) (hcz : CL S σ m n (dropT (kA S m n) c))
    (cq : CL S σ m n q) (pq : q.isPrin = true) (hqσ : ¬ Term.val S q < σ)
    (hk : lvl (Term.val S (.psiS s c)) = lvl (Term.val S q))
    (hlt : Term.val S (.psiS s c) < Term.val S q) : ev σ (Ex S σ m n (.psiS s c)) < ev σ (Ex S σ m n q) := by
  simp only [AA_eq] at *
  apply Bt.PMs_psiA <;> assumption

end Googology.Trans.PoR.InaccPsi.R2.Br

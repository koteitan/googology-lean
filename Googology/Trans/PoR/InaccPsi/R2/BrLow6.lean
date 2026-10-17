import Googology.Trans.PoR.InaccPsi.R2.BrLow5

/-!
# Lower bound, part 6: Lemma M for `E`, the main induction, and Theorem LOW-0

* `PM_phi`, `PM_psi`: Lemma M for `p = φ(a, b)` and `p = ψ_{Ω_{k+1}}(a)` against a principal `q` of the
  same level; `PM_low`: all principal pairs; `M_step_low`: sums;
* `E_main`: Lemma D and Lemma M for every size;
* `psi_le_ups_one` (**Theorem LOW-0**): `ψ_{Ω₁}(Ω_ω) ≤ υ₁` for every `S : InaccSeq.{0}`;
* `ups_one_eq`: `υ₁ = ψ_{Ω₁}(Ω_ω)`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Br

open Ordinal Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq Tm

variable {S : InaccSeq.{0}}

/-- The star of a `φ`-code is below `E(q)` when the arguments are. -/
theorem star_codephi_lt {k : ℕ} {x y : Tm} (hx : NF 1 x) (hy : NF 1 y) (hxk : ev 1 x < OmT 1 (k + 1))
    (hyk : ev 1 y < OmT 1 (k + 1)) {Y : Ordinal.{0}} (hxY : ev 1 x < Y) (hyY : ev 1 y < Y) :
    Tm.star 1 k (plus 1 (th (k + 1) x) y) < Y := by
  refine star_le_of 1 (fun u hu => ?_) (lt_of_le_of_lt zero_le hxY)
  rcases Ki_codephi hx hy hxk hyk u hu with h | h
  · exact lt_of_le_of_lt h hxY
  · exact lt_of_le_of_lt h hyY

/-- **Lemma M, `p = φ(a, b)`.** -/
theorem PM_phi {N : ℕ} (hD : DO S N) {a b q : Term} (hsp : (Term.phi a b).size ≤ N)
    (hsq : q.size ≤ N) (IHi : MO S N ((Term.phi a b).size + q.size)) (np : Term.NF (.phi a b))
    (nq : Term.NF q) (cp : Cw S (.phi a b)) (cq : Cw S q) (pq : q.isPrin = true)
    (hk : lvl (Term.val S (.phi a b)) = lvl (Term.val S q))
    (hlt : Term.val S (.phi a b) < Term.val S q) : ev 1 (E S (.phi a b)) < ev 1 (E S q) := by
  set k := lvl (Term.val S (.phi a b)) with hkdef
  obtain ⟨n1, n2, h1, h2⟩ := phi_data hD hsp np cp
  rw [← hkdef] at h1 h2
  have hDp := hD _ hsp cp np
  have hep : E S (.phi a b) = th k (plus 1 (th (k + 1) (E S a)) (E S b)) := E_phi a b
  have nEp : NF 1 (th k (plus 1 (th (k + 1) (E S a)) (E S b))) := hep ▸ hDp.nf
  obtain ⟨va, vb⟩ := NF_phi_lt (S := S) np
  have hsa : a.size < (Term.phi a b).size := by simp only [Term.size]; omega
  have hsb : b.size < (Term.phi a b).size := by simp only [Term.size]; omega
  -- `E a, E b < E q`
  have hEaq : ev 1 (E S a) < ev 1 (E S q) :=
    IHi a q (by omega) hsq (by omega) cp.1 cq np.1 nq (va.trans hlt)
  have hEbq : ev 1 (E S b) < ev 1 (E S q) :=
    IHi b q (by omega) hsq (by omega) cp.2 cq np.2.1 nq (vb.trans hlt)
  cases q with
  | zero => simp [Term.isPrin, Term.isSC] at pq
  | add _ _ => simp [Term.isPrin, Term.isSC] at pq
  | inacc _ => exact absurd cq (by simp [Cw])
  | inaccW => exact absurd cq (by simp [Cw])
  | psiI _ _ => exact absurd cq (by simp [Cw])
  | om b' => exact absurd hlt (not_lt_om np cp rfl cq hk)
  | phi c d =>
    obtain ⟨m1, m2, g1, g2⟩ := phi_data hD hsq nq cq
    rw [← hk] at g1 g2
    have hDq := hD _ hsq cq nq
    have heq : E S (.phi c d) = th k (plus 1 (th (k + 1) (E S c)) (E S d)) := by rw [E_phi, ← hk]
    have nEq : NF 1 (th k (plus 1 (th (k + 1) (E S c)) (E S d))) := heq ▸ hDq.nf
    have hsc : c.size < (Term.phi c d).size := by simp only [Term.size]; omega
    have hsd : d.size < (Term.phi c d).size := by simp only [Term.size]; omega
    have hqk : Term.val S (.phi c d) < OmT 1 (k + 1) := by
      have := lvl_lt (Cw_val_lt cq nq); rwa [← hk] at this
    rcases veblen_lt_veblen_iff.1 hlt with ⟨hac, hbd⟩ | ⟨hac, hbq⟩ | ⟨hca, hpd⟩
    · have e := Term.eq_of_val_eq S np.1 nq.1 hac
      subst e
      have hbd' := IHi b d (by omega) (by omega) (by omega) cp.2 cq.2 np.2.1 nq.2.1 hbd
      rw [hep, heq]
      refine thb_lt_of_I base_one nEp nEq ?_ (star_codephi_lt n1 n2 h1 h2 (heq ▸ hEaq) (heq ▸ hEbq))
      rw [ev_codephi n1 n2 h1, ev_codephi n1 m2 h1]
      exact add_lt_add_right hbd' _
    · have hac' := IHi a c (by omega) (by omega) (by omega) cp.1 cq.1 np.1 nq.1 hac
      have hthc : NF 1 (th (k + 1) (E S c)) :=
        NF.cth m1 (dom_of_lt base_one (g1.trans (OmT_lt_succ base_one _)))
      have htha : NF 1 (th (k + 1) (E S a)) :=
        NF.cth n1 (dom_of_lt base_one (h1.trans (OmT_lt_succ base_one _)))
      have h3 : ev 1 (th (k + 1) (E S a)) < ev 1 (th (k + 1) (E S c)) := by
        refine thb_lt_of_I base_one htha hthc hac' ?_
        rw [show Tm.star 1 (k + 1) (E S a) = 0 by unfold Tm.star; rw [Ki_nil_of_lt base_one n1 h1]; rfl]
        exact thb_pos base_one (NF.th_dom hthc)
      have hbq' : ev 1 (E S b) < ev 1 (E S (.phi c d)) :=
        IHi b _ (by omega) hsq (by omega) cp.2 cq np.2.1 nq hbq
      rw [hep, heq]
      refine thb_lt_of_I base_one nEp nEq ?_ (star_codephi_lt n1 n2 h1 h2 (heq ▸ hEaq) (heq ▸ hbq'))
      rw [ev_codephi n1 n2 h1, ev_codephi m1 m2 g1]
      refine lt_of_lt_of_le ?_ le_self_add
      exact NF.th_principal base_one hthc h3 (h2.trans_le (NF.th_bounds base_one hthc).1)
    · have hdq : Term.val S d < OmT 1 (k + 1) := (NF_phi_lt (S := S) nq).2.trans hqk
      exact via_head hD hsp hsq IHi np cp rfl hkdef.symm hep heq nEp nEq hsd nq.2.1 cq.2 hpd.le hdq
        (Ki_codephi_sup m1 m2 g1 g2).2
  | psiS t b' =>
    obtain ⟨⟨k', hk'⟩, hb'ω, hcb'⟩ := cq
    have cq' : Cw S (.psiS t b') := ⟨⟨k', hk'⟩, hb'ω, hcb'⟩
    have hkk : k' = k := by rw [hk, lvl_psiS t b' hk']
    rw [hkk] at hk'
    have hDq := hD _ hsq cq' nq
    have heq := E_psiS (S := S) (a := b') hk'
    have nEq : NF 1 (th k (plus 1 (Pk k) (Fc (E S b')))) := heq ▸ hDq.nf
    have hDb' := hD b' (by simp [Term.size] at hsq; omega) hcb' nq.2.1
    have hEbω : ev 1 (E S b') < Om (ω : Ordinal.{0}) := hDb'.lt.trans (OmT_succ_lt_Om_omega 1 _)
    rw [hep, heq]
    refine thb_lt_of_I base_one nEp nEq ?_ (star_codephi_lt n1 n2 h1 h2 (heq ▸ hEaq) (heq ▸ hEbq))
    rw [ev_codepsi hDb'.nf hEbω]
    exact lt_of_lt_of_le (codephi_lt_Pk n1 n2 h1 h2) le_self_add

/-- `Ωₖ < E(q)` for a `ϑ̄ₖ`-term with a nonzero argument. -/
theorem OmT_lt_th {k : ℕ} {e : Tm} (hn : NF 1 (th k e)) (he : 0 < ev 1 e) : OmT 1 k < ev 1 (th k e) := by
  have h0 : ev 1 (th k (par 0)) = OmT 1 k := thb_zero base_one k
  have := thb_lt_of_I base_one (NF_Omk k) hn he
    (by rw [show Tm.star 1 k (par 0) = 0 from rfl]; exact thb_pos base_one (NF.th_dom hn))
  rwa [h0] at this

/-- **Lemma M, `p = ψ_{Ω_{k+1}}(a)`.** -/
theorem PM_psi {N : ℕ} (hD : DO S N) {s a q : Term} (hsp : (Term.psiS s a).size ≤ N)
    (hsq : q.size ≤ N) (IHi : MO S N ((Term.psiS s a).size + q.size)) (np : Term.NF (.psiS s a))
    (nq : Term.NF q) (cp : Cw S (.psiS s a)) (cq : Cw S q) (pq : q.isPrin = true)
    (hk : lvl (Term.val S (.psiS s a)) = lvl (Term.val S q))
    (hlt : Term.val S (.psiS s a) < Term.val S q) : ev 1 (E S (.psiS s a)) < ev 1 (E S q) := by
  obtain ⟨⟨k, hks⟩, haω, hca⟩ := id cp
  have hlp : lvl (Term.val S (.psiS s a)) = k := lvl_psiS s a hks
  have hDp := hD _ hsp cp np
  have hep := E_psiS (S := S) (a := a) hks
  have nEp : NF 1 (th k (plus 1 (Pk k) (Fc (E S a)))) := hep ▸ hDp.nf
  have hsa : a.size < (Term.psiS s a).size := by simp only [Term.size]; omega
  have hDa := hD a (by omega) hca np.2.1
  have hEaω : ev 1 (E S a) < Om (ω : Ordinal.{0}) := hDa.lt.trans (OmT_succ_lt_Om_omega 1 _)
  have hqk : Term.val S q < OmT 1 (k + 1) := by
    have := lvl_lt (Cw_val_lt cq nq); rwa [← hk, hlp] at this
  cases q with
  | zero => simp [Term.isPrin, Term.isSC] at pq
  | add _ _ => simp [Term.isPrin, Term.isSC] at pq
  | inacc _ => exact absurd cq (by simp [Cw])
  | inaccW => exact absurd cq (by simp [Cw])
  | psiI _ _ => exact absurd cq (by simp [Cw])
  | om b' => exact absurd hlt (not_lt_om np cp rfl cq hk)
  | phi c d =>
    obtain ⟨m1, m2, g1, g2⟩ := phi_data hD hsq nq cq
    rw [← hk, hlp] at g1 g2
    have hDq := hD _ hsq cq nq
    have heq : E S (.phi c d) = th k (plus 1 (th (k + 1) (E S c)) (E S d)) := by rw [E_phi, ← hk, hlp]
    have nEq : NF 1 (th k (plus 1 (th (k + 1) (E S c)) (E S d))) := heq ▸ hDq.nf
    have hsc : c.size < (Term.phi c d).size := by simp only [Term.size]; omega
    have hsd : d.size < (Term.phi c d).size := by simp only [Term.size]; omega
    obtain ⟨hcq, hdq⟩ := NF_phi_lt (S := S) nq
    -- `p` is strongly critical, so `p ≤ c` or `p ≤ d`
    have hSC : SC (Term.val S (.psiS s a)) := Term.SC_val S np rfl
    have hcd : Term.val S (.psiS s a) ≤ Term.val S c ∨ Term.val S (.psiS s a) ≤ Term.val S d := by
      by_contra hno
      push Not at hno
      have := hSC.2 _ hno.1 _ hno.2
      exact absurd hlt (not_lt.2 this.le)
    rcases hcd with h | h
    · exact via_head hD hsp hsq IHi np cp rfl hlp hep heq nEp nEq hsc nq.1 cq.1 h (hcq.trans hqk)
        (Ki_codephi_sup m1 m2 g1 g2).1
    · exact via_head hD hsp hsq IHi np cp rfl hlp hep heq nEp nEq hsd nq.2.1 cq.2 h (hdq.trans hqk)
        (Ki_codephi_sup m1 m2 g1 g2).2
  | psiS t b' =>
    obtain ⟨⟨k', hk'⟩, hb'ω, hcb'⟩ := id cq
    have hkk : k' = k := by rw [← lvl_psiS t b' hk', ← hk, hlp]
    rw [hkk] at hk'
    have hDq := hD _ hsq cq nq
    have heq := E_psiS (S := S) (a := b') hk'
    have nEq : NF 1 (th k (plus 1 (Pk k) (Fc (E S b')))) := heq ▸ hDq.nf
    have hsb' : b'.size < (Term.psiS t b').size := by simp only [Term.size]; omega
    have hDb' := hD b' (by omega) hcb' nq.2.1
    have hEbω : ev 1 (E S b') < Om (ω : Ordinal.{0}) := hDb'.lt.trans (OmT_succ_lt_Om_omega 1 _)
    -- `a < b'`
    have hab : Term.val S a < Term.val S b' := by
      by_contra hge
      rw [not_lt] at hge
      have := (psi_mono (S := S) (InR_Om_succ (S := S) (Term.val S t)) hge).1
      simp only [Term.val] at hlt
      rw [hks, ← hk'] at hlt
      exact absurd hlt (not_lt.2 this)
    have hEab := IHi a b' (by omega) (by omega) (by omega) hca hcb' np.2.1 nq.2.1 hab
    have hFab := Fc_lt hDa.nf hDb'.nf hEbω hEab
    have hcodeq_pos : 0 < ev 1 (plus 1 (Pk k) (Fc (E S b'))) := by
      rw [ev_codepsi hDb'.nf hEbω]
      exact lt_of_lt_of_le (lt_of_le_of_lt zero_le (ev_Pk_bounds k).1) le_self_add
    have hY : OmT 1 k < ev 1 (th k (plus 1 (Pk k) (Fc (E S b')))) := OmT_lt_th nEq hcodeq_pos
    rw [hep, heq]
    refine thb_lt_of_I base_one nEp nEq ?_ ?_
    · rw [ev_codepsi hDa.nf hEaω, ev_codepsi hDb'.nf hEbω]
      exact add_lt_add_right hFab _
    · -- the star of the code of `p`
      refine star_le_of 1 (fun u hu => ?_) (lt_of_le_of_lt zero_le hY)
      rcases List.mem_append.1 (Ki_plus 1 k _ _ hu) with h | h
      · rw [Ki_Pk] at h; simp at h
      · -- bounds of level-`k` codes `F`
        have hO2 : ∀ x : Tm, NF 1 x → ev 1 x < Om (ω : Ordinal.{0}) → ev 1 x ≠ 0 →
            lvl (ev 1 x) + 1 = k → ev 1 (Fc x) < ev 1 (th k (plus 1 (Pk k) (Fc (E S b')))) := by
          intro x hx hxω hx0 hlx
          have hnF := NF_Fc hx hxω
          rw [Fc_pos hx0] at hnF ⊢
          rw [hlx] at hnF ⊢
          refine thb_lt_of_I base_one hnF nEq ?_ ?_
          · rw [ev_codepsi hDb'.nf hEbω]
            have := Farg_lt (m := lvl (ev 1 x)) hx (lvl_lt hxω)
            rw [hlx] at this
            exact lt_of_lt_of_le (this.trans (ev_Pk_bounds k).1) le_self_add
          · refine star_le_of 1 (fun w hw => ?_) (lt_of_le_of_lt zero_le hY)
            have hxl : ev 1 x < OmT 1 (lvl (ev 1 x) + 1) := lvl_lt hxω
            have := star_Farg hx hxl w (by rw [hlx]; exact hw)
            rw [hlx] at this
            exact lt_of_le_of_lt this hY
        by_cases ha0 : ev 1 (E S a) = 0
        · rw [Fc_zero ha0] at h; simp [Ki] at h
        have h' := Ki_Fc ha0 h
        split_ifs at h' with g1 g2
        · simp at h'
        · simp at h'; subst h'; exact hO2 _ hDa.nf hEaω ha0 g2
        · -- Lemma KB
          refine KB np hks _ (fun u hu hcu hnu => hD u (by omega) hcu hnu) ?_ hO2 a le_rfl np.2.1 hca
            np.2.2 u h'
          intro r hsr hnr hcr hpr hlr hrp
          rw [← heq]
          exact IHi r _ (by omega) hsq (by omega) hcr cq hnr nq (hrp.trans hlt)

/-- **Lemma M** for two principal terms. -/
theorem PM_low {N : ℕ} (hD : DO S N) {p q : Term} (hsp : p.size ≤ N) (hsq : q.size ≤ N)
    (IHi : MO S N (p.size + q.size)) (np : Term.NF p) (nq : Term.NF q) (cp : Cw S p) (cq : Cw S q)
    (pp : p.isPrin = true) (pq : q.isPrin = true) (hlt : Term.val S p < Term.val S q) :
    ev 1 (E S p) < ev 1 (E S q) := by
  have hDp := hD p hsp cp np
  have hDq := hD q hsq cq nq
  rcases lt_trichotomy (lvl (Term.val S p)) (lvl (Term.val S q)) with hk | hk | hk
  · exact lt_of_lt_of_le hDp.lt ((OmT_mono base_one (by omega)).trans (hDq.prin pq).1)
  · cases p with
    | zero => simp [Term.isPrin, Term.isSC] at pp
    | add _ _ => simp [Term.isPrin, Term.isSC] at pp
    | inacc _ => exact absurd cp (by simp [Cw])
    | inaccW => exact absurd cp (by simp [Cw])
    | psiI _ _ => exact absurd cp (by simp [Cw])
    | om b => exact PM_om hD hsq nq cp cq pq hk hlt
    | phi a b => exact PM_phi hD hsp hsq IHi np nq cp cq pq hk hlt
    | psiS s a => exact PM_psi hD hsp hsq IHi np nq cp cq pq hk hlt
  · exact absurd hlt (not_lt.2 ((lvl_lt (Cw_val_lt cq nq)).trans_le ((OmT_mono base_one (by omega)).trans
      (OmT_lvl_le np cp pp))).le)

/-- **Lemma M**, a principal term against any term. -/
theorem M_prin_left {N : ℕ} (hD : DO S N) {s t : Term} (hss : s.size ≤ N) (hst : t.size ≤ N)
    (IHi : MO S N (s.size + t.size)) (ns : Term.NF s) (nt : Term.NF t) (cs : Cw S s) (ct : Cw S t)
    (ps : s.isPrin = true) (hlt : Term.val S s < Term.val S t) : ev 1 (E S s) < ev 1 (E S t) := by
  cases t with
  | zero => exact absurd hlt (not_lt.2 zero_le)
  | inacc _ => exact absurd ct (by simp [Cw])
  | inaccW => exact absurd ct (by simp [Cw])
  | psiI _ _ => exact absurd ct (by simp [Cw])
  | add c d =>
    have hDt := hD _ hst ct nt
    rcases lt_trichotomy (Term.val S s) (Term.val S c) with h | h | h
    · have := IHi _ c hss (by simp only [Term.size] at hst; omega) (by simp only [Term.size]; omega)
        cs ct.1 ns nt.1 h
      rw [hDt.add c d rfl]
      exact lt_of_lt_of_le this le_self_add
    · have e := Term.eq_of_val_eq S ns nt.1 h
      subst e
      rw [hDt.add _ d rfl]
      have hd0 : Term.val S d ≠ 0 := Term.val_ne_zero S nt.2.1 nt.2.2.2.1
      exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 ((hD d (by simp only [Term.size] at hst; omega)
        ct.2 nt.2.1).ne hd0))
    · have : Term.val S (.add c d) < Term.val S s := val_lt_of_head nt (Term.isPrincipal_val S ns ps) h
      exact absurd hlt (not_lt.2 this.le)
  | phi c d => exact PM_low hD hss hst IHi ns nt cs ct ps rfl hlt
  | om b => exact PM_low hD hss hst IHi ns nt cs ct ps rfl hlt
  | psiS r c => exact PM_low hD hss hst IHi ns nt cs ct ps rfl hlt

/-- A sum below a principal term. -/
theorem M_sum_prin {N : ℕ} (hD : DO S N) {a b u : Term} (hss : (Term.add a b).size ≤ N)
    (hsu : u.size ≤ N) (IHi : MO S N ((Term.add a b).size + u.size)) (ns : Term.NF (.add a b))
    (nu : Term.NF u) (cs : Cw S (.add a b)) (cu : Cw S u) (pu : u.isPrin = true)
    (hlt : Term.val S (.add a b) < Term.val S u) : ev 1 (E S (.add a b)) < ev 1 (E S u) := by
  have hDs := hD _ hss cs ns
  have hDu := hD u hsu cu nu
  obtain ⟨-, e, he⟩ := hDu.prin pu
  have hP : IsPrincipal (· + ·) (ev 1 (E S u)) := he ▸ NF.th_principal base_one (he ▸ hDu.nf)
  rw [hDs.add a b rfl]
  show ev 1 (E S a) + ev 1 (E S b) < _
  exact hP (IHi a u (by simp only [Term.size] at hss; omega) hsu (by simp only [Term.size]; omega)
    cs.1 cu ns.1 nu (lt_of_le_of_lt (val_le_add_left a b) hlt))
    (IHi b u (by simp only [Term.size] at hss; omega) hsu (by simp only [Term.size]; omega)
    cs.2 cu ns.2.1 nu (lt_of_le_of_lt (val_le_add_right a b) hlt))

/-- **Lemma M**: the inner step. -/
theorem M_step_low {N : ℕ} (hD : DO S N) {s t : Term} (hss : s.size ≤ N) (hst : t.size ≤ N)
    (IHi : MO S N (s.size + t.size)) (ns : Term.NF s) (nt : Term.NF t) (cs : Cw S s) (ct : Cw S t)
    (hlt : Term.val S s < Term.val S t) : ev 1 (E S s) < ev 1 (E S t) := by
  cases s with
  | zero =>
    have ht0 : Term.val S t ≠ 0 := (lt_of_le_of_lt zero_le hlt).ne'
    exact lt_of_le_of_lt zero_le (pos_iff_ne_zero.2 ((hD t hst ct nt).ne ht0))
  | inacc _ => exact absurd cs (by simp [Cw])
  | inaccW => exact absurd cs (by simp [Cw])
  | psiI _ _ => exact absurd cs (by simp [Cw])
  | phi _ _ => exact M_prin_left hD hss hst IHi ns nt cs ct rfl hlt
  | om _ => exact M_prin_left hD hss hst IHi ns nt cs ct rfl hlt
  | psiS _ _ => exact M_prin_left hD hss hst IHi ns nt cs ct rfl hlt
  | add a b =>
    have hDs := hD _ hss cs ns
    have hva : Term.val S a ≤ Term.val S (.add a b) := val_le_add_left a b
    cases t with
    | zero => exact absurd hlt (not_lt.2 zero_le)
    | inacc _ => exact absurd ct (by simp [Cw])
    | inaccW => exact absurd ct (by simp [Cw])
    | psiI _ _ => exact absurd ct (by simp [Cw])
    | phi _ _ => exact M_sum_prin hD hss hst IHi ns nt cs ct rfl hlt
    | om _ => exact M_sum_prin hD hss hst IHi ns nt cs ct rfl hlt
    | psiS _ _ => exact M_sum_prin hD hss hst IHi ns nt cs ct rfl hlt
    | add c d =>
      have hDt := hD _ hst ct nt
      rcases lt_trichotomy (Term.val S a) (Term.val S c) with h | h | h
      · have hsc : Term.val S (.add a b) < Term.val S c :=
          val_lt_of_head ns (Term.isPrincipal_val S nt.1 nt.2.2.1) h
        have := IHi _ c hss (by simp only [Term.size] at hst; omega) (by simp only [Term.size]; omega)
          cs ct.1 ns nt.1 hsc
        rw [hDt.add c d rfl]
        exact lt_of_lt_of_le this le_self_add
      · have e := Term.eq_of_val_eq S ns.1 nt.1 h
        subst e
        have hbd : Term.val S b < Term.val S d := by
          have h' : Term.val S a + Term.val S b < Term.val S a + Term.val S d := hlt
          exact (add_lt_add_iff_left _).1 h'
        have := IHi b d (by simp only [Term.size] at hss; omega) (by simp only [Term.size] at hst; omega)
          (by simp only [Term.size]; omega) cs.2 ct.2 ns.2.1 nt.2.1 hbd
        rw [hDs.add a b rfl, hDt.add a d rfl]
        exact add_lt_add_right this _
      · have : Term.val S (.add c d) < Term.val S a :=
          val_lt_of_head nt (Term.isPrincipal_val S ns.1 ns.2.2.1) h
        exact absurd (lt_of_lt_of_le this hva) (not_lt.2 hlt.le)

/-- **Lemma D and Lemma M for `E`**, for all sizes. -/
theorem E_main (S : InaccSeq.{0}) : ∀ n : ℕ, DO S n ∧ MO S n (2 * n + 1) := by
  intro n
  induction n with
  | zero =>
    exact ⟨fun u h => absurd (Term.size_pos u) (by omega),
      fun x y h => absurd (Term.size_pos x) (by omega)⟩
  | succ n ih =>
    obtain ⟨ihD, ihM⟩ := ih
    have hD : DO S (n + 1) := by
      intro u hu hcu hnu
      exact D_step hnu hcu (fun v hv hcv hnv => ihD v (by omega) hcv hnv)
        (fun x y hx hy hcx hcy hnx hny hxy => ihM x y (by omega) (by omega) (by omega) hcx hcy hnx hny hxy)
    refine ⟨hD, ?_⟩
    have key : ∀ m : ℕ, MO S (n + 1) m := by
      intro m
      induction m with
      | zero => intro x y _ _ h; omega
      | succ m ihm =>
        intro x y hx hy hxy hcx hcy hnx hny hlt
        exact M_step_low hD hx hy (fun x' y' hx' hy' h' => ihm x' y' hx' hy' (by omega)) hnx hny hcx hcy hlt
    exact key _

/-- Lemma M for all normal forms of the class. -/
theorem E_lt (S : InaccSeq.{0}) {x y : Term} (hcx : Cw S x) (hcy : Cw S y) (hnx : Term.NF x)
    (hny : Term.NF y) (h : Term.val S x < Term.val S y) : ev 1 (E S x) < ev 1 (E S y) :=
  (E_main S (max x.size y.size)).2 x y (le_max_left _ _) (le_max_right _ _) (by omega) hcx hcy hnx hny h

/-- Lemma D for all normal forms of the class. -/
theorem E_DI (S : InaccSeq.{0}) {x : Term} (hcx : Cw S x) (hnx : Term.NF x) : DI S x :=
  (E_main S x.size).1 x le_rfl hcx hnx

/-! ## Theorem LOW-0 -/

/-- **Theorem LOW-0**: `ψ_{Ω₁}(Ω_ω) ≤ υ₁`, for every InaccPsi sequence `S` in `Ordinal.{0}`. -/
theorem psi_le_ups_one (S : InaccSeq.{0}) :
    S.psi (Om (ω : Ordinal.{0})) (Om (1 : Ordinal.{0})) ≤ upsilon 1 := by
  set P := S.psi (Om (ω : Ordinal.{0})) (Om (1 : Ordinal.{0})) with hPdef
  by_contra hlt
  rw [not_le] at hlt
  -- `T¹ ∩ Ω₁ = υ₁`
  have hc : upsilon (Order.succ 0) < Om1 := by
    rw [Order.succ_eq_add_one, zero_add]; exact_mod_cast upsilon_nat_lt_Om1 1
  have hT := upsilon_succ_T 0 hc
  rw [if_pos rfl, Order.succ_eq_add_one, zero_add] at hT
  -- terms for the ordinals up to `υ₁`
  have hex : ∀ z, z ≤ upsilon 1 → ∃ t : Term, Term.NF t ∧ Term.val S t = z ∧ Cw S t := by
    intro z hz
    obtain ⟨t, ht, hv⟩ := Low.exists_NF_of_lt_psi_one (Om (ω : Ordinal.{0})) z (lt_of_le_of_lt hz hlt)
    exact ⟨t, ht, hv, cw_of_lt ht (hv ▸ lt_of_le_of_lt hz hlt)⟩
  classical
  let f : Ordinal.{0} → Ordinal.{0} := fun z =>
    if h : z ≤ upsilon 1 then ev 1 (E S (Classical.choose (hex z h))) else 0
  have hf : ∀ a b, a < b → b ≤ upsilon 1 → f a < f b := by
    intro a b hab hb
    have ha : a ≤ upsilon 1 := hab.le.trans hb
    simp only [f, dif_pos ha, dif_pos hb]
    obtain ⟨na, ea, ca⟩ := Classical.choose_spec (hex a ha)
    obtain ⟨nb, eb, cb⟩ := Classical.choose_spec (hex b hb)
    exact E_lt S ca cb na nb (by rw [ea, eb]; exact hab)
  have h1 := BP.le_apply_of_strictMonoOn f hf (upsilon 1) le_rfl
  have h2 : f (upsilon 1) < upsilon 1 := by
    simp only [f, dif_pos (le_refl (upsilon 1))]
    obtain ⟨nu, eu, cu⟩ := Classical.choose_spec (hex (upsilon 1) le_rfl)
    set t := Classical.choose (hex (upsilon 1) le_rfl)
    have hDt := E_DI S cu nu
    have hv1 : Term.val S t < Om (1 : Ordinal.{0}) := by rw [eu, ← Om1_eq]; exact hc.trans_eq' (by
      rw [Order.succ_eq_add_one, zero_add])
    have hl0 : lvl (Term.val S t) = 0 := by
      have := lvl_le_of_lt (n := 0) (by rw [OmT_succ]; simpa using hv1); omega
    have hlt1 : ev 1 (E S t) < Om (1 : Ordinal.{0}) := by
      have := hDt.lt; rw [hl0, OmT_succ] at this; simpa using this
    have hmem : ev 1 (E S t) ∈ Tset 1 := (W25_same base_one hlt1).2 (NF.mem_Tbar hDt.nf)
    exact (hT _ (Om1_eq ▸ hlt1)).1 hmem
  exact absurd h1 (not_le.2 h2)

/-- **`υ₁ = ψ_{Ω₁}(Ω_ω)`**, for every InaccPsi sequence `S` in `Ordinal.{0}`. -/
theorem ups_one_eq (S : InaccSeq.{0}) :
    upsilon 1 = S.psi (Om (ω : Ordinal.{0})) (Om (1 : Ordinal.{0})) :=
  le_antisymm (ups_one_le S) (psi_le_ups_one S)

end Googology.Trans.PoR.InaccPsi.R2.Br

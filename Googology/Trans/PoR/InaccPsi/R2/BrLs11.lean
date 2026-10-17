import Googology.Trans.PoR.InaccPsi.R2.BrLs10

/-!
# LOW-STEP, part 11: the `A`-clause code, and Lemma M for `p = Ωₖ`, `p = φ(a, b)`

* `Acode`: for `t = ψ_{Ω₁}(A + ζ)` of the class, `E(t) = ϑ̄₀(G + E ζ)` with `G = P₁` (no `ψ_{Ω₂}` top atom)
  or `G = G(E d)` for the largest top atom `ψ_{Ω₂}(d)` of `ζ`; `P₁ ≤ G`, `G` principal, `E ζ < Ω₂`;
* `PMs_om`, `PMs_phi`: Lemma M for a principal `p = Ωₖ` or `p = φ(a, b)` against a principal `q` of the same
  level.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Br

open Ordinal Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq Tm

variable {S : InaccSeq.{0}} {σ : Ordinal.{0}} {m n : ℕ}

/-- The top atom `ψ_{Ω₂}(d)` of `ζ` for an `A`-clause term: its argument is in the class. -/
theorem anchor_of {c s1 d : Term} (hσ : Base σ) (hcz : CL S σ m n (dropT (kA S m n) c))
    (hm : Term.psiS s1 d ∈ topAtoms (dropT (kA S m n) c)) (hs1 : Term.val S s1 = 1) :
    CL S σ m n d ∧ Term.NF (.psiS s1 d) ∧ Term.val S d < Om (ω : Ordinal.{0}) ∧
      (Term.psiS s1 d).size ≤ (dropT (kA S m n) c).size := by
  have hge : ¬ Term.val S (.psiS s1 d) < σ := by
    intro h
    have := (Term.val_psiS_bounds S s1 d).1
    rw [hs1] at this
    exact absurd (this.trans h) (not_lt.2 (hσ.lt_Om1.le))
  have hca := CL_topAtom hcz hm hge
  cases hca with
  | par _ h => exact absurd h hge
  | psiS hn' _ _ _ hdω hdc => exact ⟨hdc, hn', hdω, topAtoms_size hm⟩
  | psiA _ _ h0 _ _ _ _ => rw [hs1] at h0; exact absurd h0 one_ne_zero

/-- **The `A`-clause code.** -/
theorem Acode (hσ : Base σ) {s c : Term} (_hn : Term.NF (.psiS s c)) (hv : ¬ Term.val S (.psiS s c) < σ)
    (hs0 : Term.val S s = 0) (hcz : CL S σ m n (dropT (kA S m n) c))
    (hzθ : Term.val S (dropT (kA S m n) c) < ConjT.th S)
    (hD : ∀ u : Term, u.size < (Term.psiS s c).size → CL S σ m n u → DL S σ m n u) :
    Ex S σ m n (.psiS s c) =
        th 0 (plus σ (GcT S σ (EL S σ (kA S m n)) (pmax S (dropT (kA S m n) c)))
          (Ex S σ m n (dropT (kA S m n) c))) ∧
      NF σ (GcT S σ (EL S σ (kA S m n)) (pmax S (dropT (kA S m n) c))) ∧
      ev σ (Pk 1) ≤ ev σ (GcT S σ (EL S σ (kA S m n)) (pmax S (dropT (kA S m n) c))) ∧
      IsPrincipal (· + ·) (ev σ (GcT S σ (EL S σ (kA S m n)) (pmax S (dropT (kA S m n) c)))) ∧
      ev σ (Ex S σ m n (dropT (kA S m n) c)) < OmT σ 2 ∧
      (pmax S (dropT (kA S m n) c) = none →
        GcT S σ (EL S σ (kA S m n)) (pmax S (dropT (kA S m n) c)) = Pk 1) ∧
      (∀ u, pmax S (dropT (kA S m n) c) = some u → ∃ s1 d, u = .psiS s1 d ∧ Term.val S s1 = 1 ∧
        CL S σ m n d ∧ Term.NF (.psiS s1 d) ∧ Term.val S d < Om (ω : Ordinal.{0}) ∧
        d.size < (dropT (kA S m n) c).size ∧ u ∈ topAtoms (dropT (kA S m n) c) ∧
        GcT S σ (EL S σ (kA S m n)) (pmax S (dropT (kA S m n) c)) = GT σ (Ex S σ m n d)) := by
  set ζ := dropT (kA S m n) c with hζdef
  have hsz : ζ.size < (Term.psiS s c).size := by
    have := dropT_size (kA S m n) c; rw [← hζdef] at this; simp only [Term.size]; omega
  have hDz := hD ζ hsz hcz
  have hnat : natOf (Term.val S s) = 0 := by rw [hs0]; exact natOf_nat 0
  have e : Ex S σ m n (.psiS s c) = th 0 (plus σ (GcT S σ (EL S σ (kA S m n)) (pmax S ζ)) (Ex S σ m n ζ)) := by
    rw [Ex, EL_psi0 hv hnat]
  have hz2 : ev σ (Ex S σ m n ζ) < OmT σ 2 := by
    have h1 := hDz.lt
    have h2 : lvl (Term.val S ζ) ≤ 1 :=
      lvl_le_of_lt (by rw [OmT_succ]; simpa using hzθ.trans th_lt_Om2)
    exact h1.trans_le (OmT_mono hσ (by omega))
  have hsome : ∀ u, pmax S ζ = some u → ∃ s1 d, u = .psiS s1 d ∧ Term.val S s1 = 1 ∧
      CL S σ m n d ∧ Term.NF (.psiS s1 d) ∧ Term.val S d < Om (ω : Ordinal.{0}) ∧ d.size < ζ.size ∧
      u ∈ topAtoms ζ ∧ GcT S σ (EL S σ (kA S m n)) (pmax S ζ) = GT σ (Ex S σ m n d) := by
    intro u hpm
    obtain ⟨hu1, ⟨s1, d, rfl, hs1⟩, _⟩ := (pmaxL_spec (S := S) (topAtoms ζ)).2 _ hpm
    obtain ⟨hdc, hnu, hdω, hus⟩ := anchor_of hσ hcz hu1 hs1
    have hus' : (Term.psiS s1 d).size ≤ ζ.size := hus
    have hdsz : d.size < ζ.size := by simp [Term.size] at hus'; omega
    have hDd := hD d (hdsz.trans hsz) hdc
    refine ⟨s1, d, rfl, hs1, hdc, hnu, hdω, hdsz, hu1, ?_⟩
    rw [hpm, GcT_some, ← Gd_eq hDd]; rfl
  refine ⟨e, ?_, ?_, ?_, hz2, fun h => by rw [h]; rfl, hsome⟩
  · rcases hpm : pmax S ζ with _ | u
    · exact gNF_Pk hσ 1
    · obtain ⟨s1, d, rfl, _, hdc, _, _, hdsz, _, hG⟩ := hsome _ hpm
      rw [← hpm, hG]
      have hDd := hD d (hdsz.trans hsz) hdc
      exact GT_NF hσ hDd.nf (hDd.lt.trans (OmT_succ_lt_Om_omega σ _))
  · rcases hpm : pmax S ζ with _ | u
    · exact le_rfl
    · obtain ⟨s1, d, rfl, _, hdc, _, _, hdsz, _, hG⟩ := hsome _ hpm
      rw [← hpm, hG]
      have hDd := hD d (hdsz.trans hsz) hdc
      exact (Pk_lt_GT hσ hDd.nf (hDd.lt.trans (OmT_succ_lt_Om_omega σ _)) (le_max_right _ _)).le
  · rcases hpm : pmax S ζ with _ | u
    · exact gPk_principal hσ 1
    · obtain ⟨s1, d, rfl, _, hdc, _, _, hdsz, _, hG⟩ := hsome _ hpm
      rw [← hpm, hG]
      have hDd := hD d (hdsz.trans hsz) hdc
      exact (GT_bounds hσ hDd.nf (hDd.lt.trans (OmT_succ_lt_Om_omega σ _))).2.2.2

/-- A principal non-parameter has a `ϑ̄`-image of its level. -/
theorem prin_image {N : ℕ} (hD : DOs S σ m n N) {p : Term} (hs : p.size ≤ N) (cp : CL S σ m n p)
    (pp : p.isPrin = true) (hpσ : ¬ Term.val S p < σ) :
    ∃ e, Ex S σ m n p = th (lvl (Term.val S p)) e ∧ NF σ (th (lvl (Term.val S p)) e) := by
  obtain ⟨-, e, he⟩ := (hD p hs cp).prin pp hpσ
  exact ⟨e, he, he ▸ (hD p hs cp).nf⟩

theorem CL_om_val {b : Term} (hc : CL S σ m n (.om b)) (hv : ¬ Term.val S (.om b) < σ) :
    ∃ k : ℕ, k ≠ 0 ∧ Term.val S b = k ∧ Term.val S (.om b) = OmT 1 k ∧
      lvl (Term.val S (.om b)) = k := by
  cases hc with
  | par _ h => exact absurd h hv
  | om _ _ hk0 hk =>
    exact ⟨_, hk0, hk, by rw [val_om_of_Cw hk, Om_nat_eq_OmT hk0], by rw [val_om_of_Cw hk]; exact lvl_Om hk0⟩

/-- The code of a principal `q ≠ Ωₖ`, `q ≥ σ`, is positive. -/
theorem code_pos_s (hσ : Base σ) {N : ℕ} (hD : DOs S σ m n N) {q : Term} (hs : q.size ≤ N)
    (cq : CL S σ m n q) (pq : q.isPrin = true) (hqσ : ¬ Term.val S q < σ) (hnotom : ∀ b, q ≠ .om b) :
    ∃ e, Ex S σ m n q = th (lvl (Term.val S q)) e ∧ 0 < ev σ e ∧ NF σ (th (lvl (Term.val S q)) e) := by
  obtain ⟨e, he, hne⟩ := prin_image hD hs cq pq hqσ
  refine ⟨e, he, ?_, hne⟩
  cases cq with
  | par _ h => exact absurd h hqσ
  | add => simp [Term.isPrin, Term.isSC] at pq
  | om => exact absurd rfl (hnotom _)
  | @phi c d hn hv hc hd =>
    have hDc := hD c (by simp [Term.size] at hs; omega) hc
    rw [Ex, EL_phi hv] at he
    cases he
    have h1 : ev σ (Ex S σ m n c) < OmT σ (lvl (Term.val S (.phi c d)) + 1) :=
      lt_of_lt_of_le hDc.lt (OmT_mono hσ (by
        have := lvl_mono (CL_val_lt hσ (CL.phi hn hv hc hd)) (NF_phi_lt (S := S) hn).1.le; omega))
    rw [gev_codephi hσ hDc.nf (hD d (by simp [Term.size] at hs; omega) hd).nf h1]
    exact lt_of_lt_of_le (thb_pos hσ (dom_of_lt hσ (h1.trans (OmT_lt_succ hσ _)))) le_self_add
  | @psiS s c k hn hv hk0 hk hcω hc =>
    have hnat : natOf (Term.val S s) ≠ 0 := by rw [hk, natOf_nat]; exact hk0
    rw [Ex, EL_psiS hv hnat, hk, natOf_nat, lvl_psiS s c hk] at he
    cases he
    have hDc := hD c (by simp [Term.size] at hs; omega) hc
    rw [gev_codepsi hσ hDc.nf (hDc.lt.trans (OmT_succ_lt_Om_omega σ _))]
    exact lt_of_lt_of_le (lt_of_le_of_lt zero_le (gev_Pk_bounds hσ k).1) le_self_add
  | @psiA s c hn hv hs0 hnz hcv hzθ hcz =>
    obtain ⟨hE, _, hP1, _, _, _, _⟩ := Acode hσ hn hv hs0 hcz hzθ
      (fun u hu hcu => hD u (by omega) hcu)
    rw [hE, psiA_lvl hs0] at he
    cases he
    rw [ev_plus hσ (by
      obtain ⟨_, hG, _⟩ := Acode hσ hn hv hs0 hcz hzθ (fun u hu hcu => hD u (by omega) hcu); exact hG)
      (hD _ (by have := dropT_size (kA S m n) c; simp [Term.size] at hs; omega) hcz).nf]
    exact lt_of_lt_of_le (lt_of_lt_of_le (lt_of_le_of_lt zero_le (gev_Pk_bounds hσ 1).1) hP1) le_self_add

/-- **Lemma M, `p = Ωₖ`.** -/
theorem PMs_om (hσ : Base σ) {N : ℕ} (hD : DOs S σ m n N) {b q : Term} (_hsp : (Term.om b).size ≤ N)
    (hsq : q.size ≤ N) (cp : CL S σ m n (.om b)) (cq : CL S σ m n q) (pq : q.isPrin = true)
    (hpσ : ¬ Term.val S (.om b) < σ) (hqσ : ¬ Term.val S q < σ)
    (hk : lvl (Term.val S (.om b)) = lvl (Term.val S q)) (hlt : Term.val S (.om b) < Term.val S q) :
    ev σ (Ex S σ m n (.om b)) < ev σ (Ex S σ m n q) := by
  obtain ⟨kb, hkb0, hkb, hv, hl⟩ := CL_om_val cp hpσ
  have hnotom : ∀ b', q ≠ .om b' := by
    rintro b' rfl
    obtain ⟨kb', _, _, hv', hl'⟩ := CL_om_val cq hqσ
    rw [hl, hl'] at hk; subst hk
    rw [hv, hv'] at hlt; exact lt_irrefl _ hlt
  obtain ⟨e, he, hpos, hne⟩ := code_pos_s hσ hD hsq cq pq hqσ hnotom
  have hep : Ex S σ m n (.om b) = th kb (par 0) := by rw [Ex, EL_om hpσ, hkb, natOf_nat]; rfl
  rw [hep, he, ← hk, hl]
  rw [← hk, hl] at hne
  exact thb_lt_of_I hσ (gNF_Omk hσ kb) hne hpos
    (by rw [show Tm.star σ kb (par 0) = 0 from rfl]; exact thb_pos hσ (NF.th_dom hne))

/-- `Ωₖ` is the least value of its level. -/
theorem not_lt_om_s (hσ : Base σ) {p b : Term} (cp : CL S σ m n p) (pp : p.isPrin = true)
    (cb : CL S σ m n (.om b)) (hbσ : ¬ Term.val S (.om b) < σ)
    (hk : lvl (Term.val S p) = lvl (Term.val S (.om b))) : ¬ Term.val S p < Term.val S (.om b) := by
  obtain ⟨kb, -, -, hv, hl⟩ := CL_om_val cb hbσ
  intro h
  have := OmT_lvl_le_CL hσ cp pp
  rw [hk, hl, ← hv] at this
  exact absurd h (not_lt.2 this)

end Googology.Trans.PoR.InaccPsi.R2.Br

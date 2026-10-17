import Googology.Trans.PoR.InaccPsi.R2.BtL12
import Googology.Trans.PoR.InaccPsi.LowerT

/-!
# LOW-STEP, part 13: Lemma M over `σ` and Theorem LOW-STEP

The repo module `R2.BrLs13` with the summands of `A` given by a list `L` (`R2.Bt.GoodL`) in place of
those of `A_{ω·m+n}`; the statements are the same with `AA S L`, `kA S L` for `AA S m n`, `kA S m n`.


* `PMs_low`, `M_step_s`, `E_main_s`: Lemma D and Lemma M for the map over `σ`, all sizes;
* `low_step` (**Theorem LOW-STEP**): for `A` the sum of a list `L` with `GoodL S L`, a base `σ` with
  `ψ_{Ω₁}(A) ≤ σ` and `Tᵟ ∩ Ω₁ = M`: `ψ_{Ω₁}(A + θ) ≤ M`;
* `ups_low_step`: `ψ_{Ω₁}(A) ≤ υ_ξ ⇒ ψ_{Ω₁}(A + θ) ≤ υ_{ξ+1}`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Bt

open Googology.Trans.PoR.InaccPsi.R2.Br

open Ordinal Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq Googology.Trans.PoR.InaccPsi.R2.Br.Tm

variable {S : InaccSeq.{0}} {σ : Ordinal.{0}} {L : List Ordinal.{0}}

/-- **Lemma M**, principal terms over `σ`. -/
theorem PMs_low (hσ : Base σ) {N : ℕ} (hD : DOs S σ L N) {p q : Term} (hsp : p.size ≤ N)
    (hsq : q.size ≤ N) (IHi : MOs S σ L N (p.size + q.size)) (cp : CL S σ L p) (cq : CL S σ L q)
    (pp : p.isPrin = true) (pq : q.isPrin = true) (hpσ : ¬ Term.val S p < σ)
    (hqσ : ¬ Term.val S q < σ) (hlt : Term.val S p < Term.val S q) :
    ev σ (Ex S σ L p) < ev σ (Ex S σ L q) := by
  have hDp := hD p hsp cp
  have hDq := hD q hsq cq
  rcases lt_trichotomy (lvl (Term.val S p)) (lvl (Term.val S q)) with hk | hk | hk
  · exact lt_of_lt_of_le hDp.lt ((OmT_mono hσ (by omega)).trans (hDq.prin pq hqσ).1)
  · cases cp with
    | par _ h => exact absurd h hpσ
    | add => simp [Term.isPrin, Term.isSC] at pp
    | om hn hv hk0 hkb => exact PMs_om hσ hD hsp hsq (CL.om hn hv hk0 hkb) cq pq hpσ hqσ hk hlt
    | phi hn hv ha hb => exact PMs_phi hσ hD hsp hsq IHi (CL.phi hn hv ha hb) cq pq hpσ hqσ hk hlt
    | psiS hn hv hk0 hks haω ha => exact PMs_psiS hσ hD hsp hsq IHi hn hv hk0 hks haω ha cq pq hqσ hk hlt
    | psiA hn hv hs0 hnz hcv hzθ hcz =>
      exact PMs_psiA hσ hD hsp hsq IHi hn hv hs0 hnz hcv hzθ hcz cq pq hqσ hk hlt
  · exact absurd hlt (not_lt.2 ((lvl_lt (CL_val_lt hσ cq)).trans_le ((OmT_mono base_one (by omega)).trans
      (OmT_lvl_le_CL hσ cp pp))).le)

/-- A principal non-parameter against any term above it. -/
theorem M_prin_s (hσ : Base σ) {N : ℕ} (hD : DOs S σ L N) {s t : Term} (hss : s.size ≤ N)
    (hst : t.size ≤ N) (IHi : MOs S σ L N (s.size + t.size)) (cs : CL S σ L s) (ct : CL S σ L t)
    (ps : s.isPrin = true) (hsσ : ¬ Term.val S s < σ) (htσ : ¬ Term.val S t < σ)
    (hlt : Term.val S s < Term.val S t) : ev σ (Ex S σ L s) < ev σ (Ex S σ L t) := by
  have ns := cs.NF
  have nt := ct.NF
  cases ct with
  | par _ h => exact absurd h htσ
  | @add c d hn hv hc hd =>
    have hDt := hD _ hst (CL.add hn hv hc hd)
    rcases lt_trichotomy (Term.val S s) (Term.val S c) with h | h | h
    · have := IHi _ c hss (by simp only [Term.size] at hst; omega) (by simp only [Term.size]; omega)
        cs hc h
      rw [hDt.add c d rfl hv]
      exact lt_of_lt_of_le this le_self_add
    · have e := Term.eq_of_val_eq S ns hn.1 h
      subst e
      rw [hDt.add _ d rfl hv]
      have hd0 : Term.val S d ≠ 0 := Term.val_ne_zero S hn.2.1 hn.2.2.2.1
      exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 ((hD d (by simp only [Term.size] at hst; omega)
        hd).ne hd0))
    · have : Term.val S (.add c d) < Term.val S s := val_lt_of_head hn (Term.isPrincipal_val S ns ps) h
      exact absurd hlt (not_lt.2 this.le)
  | phi hn hv hc hd => exact PMs_low hσ hD hss hst IHi cs (CL.phi hn hv hc hd) ps rfl hsσ htσ hlt
  | om hn hv hk0 hk => exact PMs_low hσ hD hss hst IHi cs (CL.om hn hv hk0 hk) ps rfl hsσ htσ hlt
  | psiS hn hv hk0 hk hcω hc =>
    exact PMs_low hσ hD hss hst IHi cs (CL.psiS hn hv hk0 hk hcω hc) ps rfl hsσ htσ hlt
  | psiA hn hv hs0 h1 h2 h3 h4 =>
    exact PMs_low hσ hD hss hst IHi cs (CL.psiA hn hv hs0 h1 h2 h3 h4) ps rfl hsσ htσ hlt

/-- A sum below a principal non-parameter. -/
theorem M_sum_prin_s (hσ : Base σ) {N : ℕ} (hD : DOs S σ L N) {a b u : Term}
    (hss : (Term.add a b).size ≤ N) (hsu : u.size ≤ N) (IHi : MOs S σ L N ((Term.add a b).size + u.size))
    (cs : CL S σ L (.add a b)) (cu : CL S σ L u) (pu : u.isPrin = true)
    (hsσ : ¬ Term.val S (.add a b) < σ) (huσ : ¬ Term.val S u < σ)
    (hlt : Term.val S (.add a b) < Term.val S u) : ev σ (Ex S σ L (.add a b)) < ev σ (Ex S σ L u) := by
  obtain ⟨ns, ca, cb⟩ : Term.NF (.add a b) ∧ CL S σ L a ∧ CL S σ L b := by
    cases cs with
    | par _ h => exact absurd h hsσ
    | add hn _ ha hb => exact ⟨hn, ha, hb⟩
  have hDs := hD _ hss cs
  have hDu := hD u hsu cu
  obtain ⟨-, e, he⟩ := hDu.prin pu huσ
  have hP : IsPrincipal (· + ·) (ev σ (Ex S σ L u)) := he ▸ NF.th_principal hσ (he ▸ hDu.nf)
  rw [hDs.add a b rfl hsσ]
  show ev σ (Ex S σ L a) + ev σ (Ex S σ L b) < _
  exact hP (IHi a u (by simp only [Term.size] at hss; omega) hsu (by simp only [Term.size]; omega)
    ca cu (lt_of_le_of_lt (val_le_add_left a b) hlt))
    (IHi b u (by simp only [Term.size] at hss; omega) hsu (by simp only [Term.size]; omega)
    cb cu (lt_of_le_of_lt (val_le_add_right a b) hlt))

/-- **Lemma M** over `σ`: the inner step. -/
theorem M_step_s (hσ : Base σ) {N : ℕ} (hD : DOs S σ L N) {s t : Term} (hss : s.size ≤ N)
    (hst : t.size ≤ N) (IHi : MOs S σ L N (s.size + t.size)) (cs : CL S σ L s) (ct : CL S σ L t)
    (hlt : Term.val S s < Term.val S t) : ev σ (Ex S σ L s) < ev σ (Ex S σ L t) := by
  by_cases htσ : Term.val S t < σ
  · have hsσ := hlt.trans htσ
    rw [Ex_par hsσ, Ex_par htσ]; exact hlt
  by_cases hsσ : Term.val S s < σ
  · rw [Ex_par hsσ]; exact lt_of_lt_of_le hsσ ((hD t hst ct).ge htσ)
  have ns := cs.NF
  have nt := ct.NF
  cases cs with
  | par _ h => exact absurd h hsσ
  | phi hn hv ha hb => exact M_prin_s hσ hD hss hst IHi (CL.phi hn hv ha hb) ct rfl hsσ htσ hlt
  | om hn hv hk0 hk => exact M_prin_s hσ hD hss hst IHi (CL.om hn hv hk0 hk) ct rfl hsσ htσ hlt
  | psiS hn hv hk0 hk hcω hc => exact M_prin_s hσ hD hss hst IHi (CL.psiS hn hv hk0 hk hcω hc) ct rfl hsσ htσ hlt
  | psiA hn hv hs0 h1 h2 h3 h4 =>
    exact M_prin_s hσ hD hss hst IHi (CL.psiA hn hv hs0 h1 h2 h3 h4) ct rfl hsσ htσ hlt
  | @add a b hn hv ha hb =>
    have cs : CL S σ L (.add a b) := CL.add hn hv ha hb
    have hDs := hD _ hss cs
    have hva : Term.val S a ≤ Term.val S (.add a b) := val_le_add_left a b
    cases ct with
    | par _ h => exact absurd h htσ
    | phi hn' hv' hc hd => exact M_sum_prin_s hσ hD hss hst IHi cs (CL.phi hn' hv' hc hd) rfl hsσ htσ hlt
    | om hn' hv' hk0 hk => exact M_sum_prin_s hσ hD hss hst IHi cs (CL.om hn' hv' hk0 hk) rfl hsσ htσ hlt
    | psiS hn' hv' hk0 hk hcω hc =>
      exact M_sum_prin_s hσ hD hss hst IHi cs (CL.psiS hn' hv' hk0 hk hcω hc) rfl hsσ htσ hlt
    | psiA hn' hv' hs0 h1 h2 h3 h4 =>
      exact M_sum_prin_s hσ hD hss hst IHi cs (CL.psiA hn' hv' hs0 h1 h2 h3 h4) rfl hsσ htσ hlt
    | @add c d hn' hv' hc hd =>
      have hDt := hD _ hst (CL.add hn' hv' hc hd)
      rcases lt_trichotomy (Term.val S a) (Term.val S c) with h | h | h
      · have hsc : Term.val S (.add a b) < Term.val S c :=
          val_lt_of_head hn (Term.isPrincipal_val S hn'.1 hn'.2.2.1) h
        have := IHi _ c hss (by simp only [Term.size] at hst; omega) (by simp only [Term.size]; omega)
          cs hc hsc
        rw [hDt.add c d rfl hv']
        exact lt_of_lt_of_le this le_self_add
      · have e := Term.eq_of_val_eq S hn.1 hn'.1 h
        subst e
        have hbd : Term.val S b < Term.val S d := by
          have h' : Term.val S a + Term.val S b < Term.val S a + Term.val S d := hlt
          exact (add_lt_add_iff_left _).1 h'
        have := IHi b d (by simp only [Term.size] at hss; omega) (by simp only [Term.size] at hst; omega)
          (by simp only [Term.size]; omega) hb hd hbd
        rw [hDs.add a b rfl hv, hDt.add a d rfl hv']
        exact add_lt_add_right this _
      · have : Term.val S (.add c d) < Term.val S a :=
          val_lt_of_head hn' (Term.isPrincipal_val S hn.1 hn.2.2.1) h
        exact absurd (lt_of_lt_of_le this hva) (not_lt.2 hlt.le)

/-- **Lemma D and Lemma M** over `σ`, all sizes. -/
theorem E_main_s (hσ : Base σ) : ∀ N : ℕ, DOs S σ L N ∧ MOs S σ L N (2 * N + 1) := by
  intro N
  induction N with
  | zero =>
    exact ⟨fun u h => absurd (Term.size_pos u) (by omega), fun x y h => absurd (Term.size_pos x) (by omega)⟩
  | succ N ih =>
    obtain ⟨ihD, ihM⟩ := ih
    have hD : DOs S σ L (N + 1) := by
      intro u hu hcu
      exact D_ls hσ hcu (fun v hv hcv => ihD v (by omega) hcv)
        (fun x y hx hy hcx hcy hxy => ihM x y (by omega) (by omega) (by omega) hcx hcy hxy)
    refine ⟨hD, ?_⟩
    have key : ∀ M : ℕ, MOs S σ L (N + 1) M := by
      intro M
      induction M with
      | zero => intro x y _ _ h; omega
      | succ M ihM =>
        intro x y hx hy hxy hcx hcy hlt
        exact M_step_s hσ hD hx hy (fun x' y' hx' hy' h' => ihM x' y' hx' hy' (by omega)) hcx hcy hlt
    exact key _

theorem E_lt_s (hσ : Base σ) {x y : Term} (hcx : CL S σ L x) (hcy : CL S σ L y)
    (h : Term.val S x < Term.val S y) : ev σ (Ex S σ L x) < ev σ (Ex S σ L y) :=
  (E_main_s hσ (max x.size y.size)).2 x y (le_max_left _ _) (le_max_right _ _) (by omega) hcx hcy h

theorem E_DL_s (hσ : Base σ) {x : Term} (hcx : CL S σ L x) : DL S σ L x :=
  (E_main_s hσ x.size).1 x le_rfl hcx

/-! ## Theorem LOW-STEP -/

/-- **Theorem LOW-STEP.**  For `A` the sum of a list `L` with `GoodL S L`, a base `σ` with
`ψ_{Ω₁}(A) ≤ σ`, and `M = Tᵟ ∩ Ω₁`: `ψ_{Ω₁}(A + θ) ≤ M`. -/
theorem low_step (S : InaccSeq.{0}) (L : List Ordinal.{0}) (hL : GoodL S L) {σ M : Ordinal.{0}} (hσ : Base σ)
    (hA : S.psi (AA S L) (Om 1) ≤ σ) (hT : ∀ a, a < Om (1 : Ordinal.{0}) → (a ∈ Tset σ ↔ a < M)) :
    S.psi (AA S L + ConjT.th S) (Om 1) ≤ M := by
  set P := S.psi (AA S L + ConjT.th S) (Om 1) with hPdef
  by_contra hlt
  rw [not_le] at hlt
  have hex : ∀ z, z ≤ M → ∃ t : Term, Term.val S t = z ∧ CL S σ L t := by
    intro z hz
    obtain ⟨t, ht, hv⟩ := Low.exists_NF_of_lt_psi_one (AA S L + ConjT.th S) z (lt_of_le_of_lt hz hlt)
    exact ⟨t, hv, (arg1 hL hσ hA t.size).1 t le_rfl ht (hv ▸ lt_of_le_of_lt hz hlt)⟩
  classical
  let f : Ordinal.{0} → Ordinal.{0} := fun z =>
    if h : z ≤ M then ev σ (Ex S σ L (Classical.choose (hex z h))) else 0
  have hf : ∀ a b, a < b → b ≤ M → f a < f b := by
    intro a b hab hb
    have ha : a ≤ M := hab.le.trans hb
    simp only [f, dif_pos ha, dif_pos hb]
    obtain ⟨ea, ca⟩ := Classical.choose_spec (hex a ha)
    obtain ⟨eb, cb⟩ := Classical.choose_spec (hex b hb)
    exact E_lt_s hσ ca cb (by rw [ea, eb]; exact hab)
  have h1 := BP.le_apply_of_strictMonoOn f hf M le_rfl
  have hP1 : P < Om (1 : Ordinal.{0}) := psi_lt InR_Om1 _
  have h2 : f M < M := by
    simp only [f, dif_pos (le_refl M)]
    obtain ⟨eu, cu⟩ := Classical.choose_spec (hex M le_rfl)
    set t := Classical.choose (hex M le_rfl)
    have hDt := E_DL_s hσ cu
    have hv1 : Term.val S t < Om (1 : Ordinal.{0}) := by rw [eu]; exact hlt.trans hP1
    have hl0 : lvl (Term.val S t) = 0 := lvl_zero_of_lt_Om1 hv1
    have hlt1 : ev σ (Ex S σ L t) < Om (1 : Ordinal.{0}) := by
      have := hDt.lt; rw [hl0] at this; rw [Om1_eq_OmT σ]; simpa using this
    exact (hT _ hlt1).1 ((W25_same hσ hlt1).2 (NF.mem_Tbar hDt.nf))
  exact absurd h1 (not_le.2 h2)

/-- **The lower step for `υ`**: for `A` the sum of a list `L` with `GoodL S L`:
`ψ_{Ω₁}(A) ≤ υ_ξ ⇒ ψ_{Ω₁}(A + θ) ≤ υ_{ξ+1}`. -/
theorem ups_low_step (S : InaccSeq.{0}) (ξ : Ordinal.{0}) (L : List Ordinal.{0}) (hL : GoodL S L)
    (h : S.psi (AA S L) (Om 1) ≤ upsilon ξ) :
    S.psi (AA S L + ConjT.th S) (Om 1) ≤ upsilon (ξ + 1) := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · rw [upsilon_zero] at h
    exact absurd h (not_le.2 (SC_psi InR_Om1 _).1)
  have hb : UpsPt (upsilon ξ) := upsPt_upsilon (pos_iff_ne_zero.2 hξ)
  by_cases hc : upsilon ξ < Om1
  · obtain ⟨M, hMn, hT⟩ := exists_next hb hc
    have hM : M = upsilon (ξ + 1) := by
      rw [← Order.succ_eq_add_one]; exact hMn.unique (upsilon_isNext ξ)
    have hσ : Base (upsilon ξ) := ⟨Or.inr (upsPt_inE hb), Om1_eq ▸ hc⟩
    rw [← hM]
    exact low_step S L hL hσ h (fun a ha => hT a (Om1_eq ▸ ha))
  · rw [not_lt] at hc
    have h1 : upsilon ξ < upsilon (ξ + 1) := upsilon_normal.strictMono (by rw [← Order.succ_eq_add_one]; exact Order.lt_succ ξ)
    exact ((psi_lt InR_Om1 _).le.trans (Om1_eq ▸ hc)).trans h1.le

end Googology.Trans.PoR.InaccPsi.R2.Bt

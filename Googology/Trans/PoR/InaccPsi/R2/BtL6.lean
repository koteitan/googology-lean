import Googology.Trans.PoR.InaccPsi.R2.BtL4

/-!
# LOW-STEP, part 6: the invariants of `E` over `σ`, Lemma Q and Lemma Q1

The repo module `R2.BrLs6` with the summands of `A` given by a list `L` (`R2.Bt.GoodL`) in place of
those of `A_{ω·m+n}`; the statements are the same with `AA S L`, `kA S L` for `AA S m n`, `kA S m n`.


* `DL t`: the invariants of `E(t)` (normal form, level, `σ ≤ E(t)` for `t ≥ σ`, heads, sums);
* `QBs` (Lemma Q): for `μ = ψ_{Ω_{k+1}}(c)` of the class, `k ≥ 1`, the `K*_{k+1}`-elements of `E(c)` are
  below `F(E c)`;
* `Q1s` (Lemma Q1): for an anchor `ψ_{Ω₂}(d)` of the class, the `K*₁`-elements of `E(d)` are below
  `G(d) = ϑ̄_{M+1}(Ω_{M+1}·2 + E d)`, `M = max(lvl d, 1)`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Bt

open Googology.Trans.PoR.InaccPsi.R2.Br

open Ordinal Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq Googology.Trans.PoR.InaccPsi.R2.Br.Tm

variable {S : InaccSeq.{0}} {σ : Ordinal.{0}} {L : List Ordinal.{0}}

/-- `E` for the data `(S, σ, A)`, with `A` the sum of the list `L`. -/
noncomputable abbrev Ex (S : InaccSeq.{0}) (σ : Ordinal.{0}) (L : List Ordinal.{0}) : Term → Tm :=
  EL S σ (kA S L)

/-- The invariants of `E(t)`. -/
structure DL (S : InaccSeq.{0}) (σ : Ordinal.{0}) (L : List Ordinal.{0}) (t : Term) : Prop where
  nf : NF σ (Ex S σ L t)
  lt : ev σ (Ex S σ L t) < OmT σ (lvl (Term.val S t) + 1)
  ne : Term.val S t ≠ 0 → ev σ (Ex S σ L t) ≠ 0
  ge : ¬ Term.val S t < σ → σ ≤ ev σ (Ex S σ L t)
  prin : t.isPrin = true → ¬ Term.val S t < σ →
    OmT σ (lvl (Term.val S t)) ≤ ev σ (Ex S σ L t) ∧ ∃ e, Ex S σ L t = th (lvl (Term.val S t)) e
  hd : ¬ Term.val S t < σ → t ≠ .zero → hd σ (Ex S σ L t) = ev σ (Ex S σ L (Term.head t))
  add : ∀ a b, t = .add a b → ¬ Term.val S t < σ → Ex S σ L t = Tm.add (Ex S σ L a) (Ex S σ L b)
  lv : lvl (ev σ (Ex S σ L t)) = lvl (Term.val S t)

/-- The `G`-code of an anchor argument `d`. -/
noncomputable def Gd (S : InaccSeq.{0}) (σ : Ordinal.{0}) (L : List Ordinal.{0}) (d : Term) : Tm :=
  th (max (lvl (Term.val S d)) 1 + 1) (gFarg σ (max (lvl (Term.val S d)) 1) (Ex S σ L d))

theorem Om1_eq_OmT (σ : Ordinal.{0}) : Om (1 : Ordinal.{0}) = OmT σ 1 := by
  rw [OmT_pos_of_ne one_ne_zero]; simp

theorem lt_OmT1 (hσ : Base σ) : σ < OmT σ 1 := by rw [← Om1_eq_OmT]; exact hσ.lt_Om1

/-- `E` of a parameter. -/
theorem Ex_par {t : Term} (h : Term.val S t < σ) : Ex S σ L t = par (Term.val S t) := EL_par h

theorem DL_par (hσ : Base σ) {t : Term} (h : Term.val S t < σ) : DL S σ L t := by
  have hv1 : Term.val S t < OmT σ 1 := h.trans (lt_OmT1 hσ)
  have hl0 : lvl (Term.val S t) = 0 := by
    have := lvl_le_of_lt (n := 0) (by rw [← OmT_succ_indep σ 0]; simpa using hv1); omega
  refine { nf := ?_, lt := ?_, ne := ?_, ge := fun h' => absurd h h', prin := fun _ h' => absurd h h',
           hd := fun h' => absurd h h', add := fun _ _ _ h' => absurd h h', lv := ?_ }
  · rw [Ex_par h]; exact NF.cpar h
  · rw [Ex_par h, hl0]; simpa using hv1
  · intro h0; rw [Ex_par h]; exact h0
  · rw [Ex_par h]; rfl

/-! ## Lemma Q over `σ` -/

/-- **Lemma Q** for the `ψ`-clause, `μ = ψ_{Ω_{k+1}}(c)`, `k ≥ 1`. -/
theorem QBs (hσ : Base σ) {s c : Term} (hμ : Term.NF (.psiS s c)) {k : ℕ} (_hk0 : k ≠ 0)
    (hk : Term.val S s = k) (hcω : Term.val S c < Om (ω : Ordinal.{0}))
    (hD : ∀ u : Term, u.size ≤ c.size → CL S σ L u → DL S σ L u)
    (hM : ∀ x : Term, x.size < c.size → CL S σ L x → Term.val S x < Term.val S c →
      ev σ (Ex S σ L x) < ev σ (Ex S σ L c))
    (hc : CL S σ L c) (hc0 : ev σ (Ex S σ L c) ≠ 0) :
    ∀ u : Term, CL S σ L u → u.size ≤ c.size → Term.KLt (.psiS s c) u c →
      Term.val S u ≤ Term.val S c →
      ∀ p ∈ Kst (k + 1) (Ex S σ L u), ev σ p.2 < ev σ (gFc σ (Ex S σ L c)) := by
  have hDc := hD c le_rfl hc
  have hEcω : ev σ (Ex S σ L c) < Om (ω : Ordinal.{0}) := hDc.lt.trans (OmT_succ_lt_Om_omega σ _)
  set X := ev σ (gFc σ (Ex S σ L c)) with hX
  have hX0 : 0 < X := lt_of_le_of_lt zero_le (gOmT_lt_Fc hσ hDc.nf hEcω hc0 (Nat.zero_le _))
  have hXP : IsPrincipal (· + ·) X := gFc_principal hσ hDc.nf hEcω hc0
  have hlvX : ∀ j : ℕ, j ≤ lvl (Term.val S c) → ev σ (Pk j) < X ∧ OmT σ (j + 1) < X := by
    intro j hj
    rw [← hDc.lv] at hj
    exact ⟨gPk_lt_Fc hσ hDc.nf hEcω hc0 hj, gOmT_lt_Fc hσ hDc.nf hEcω hc0 hj⟩
  intro u hu
  induction hu with
  | par hn hv =>
    intro _ _ _ p hp
    rw [Ex_par hv] at hp; simp [Kst] at hp
  | @add a b hn hv ha hb iha ihb =>
    intro hs hK hle p hp
    rw [(hD _ hs (CL.add hn hv ha hb)).add a b rfl hv] at hp
    simp only [Kst, List.mem_append] at hp
    rcases hp with hp | hp
    · exact iha (by simp [Term.size] at hs; omega) hK.1 ((val_le_add_left a b).trans hle) p hp
    · exact ihb (by simp [Term.size] at hs; omega) hK.2 ((val_le_add_right a b).trans hle) p hp
  | @om b j hn hv hj0 hj =>
    intro _ _ _ p hp
    rw [Ex, EL_om hv, hj, natOf_nat] at hp
    simp only [Omk, Kst] at hp
    split_ifs at hp
    · simp at hp
    · simp at hp; subst hp; exact hX0
  | @phi x y hn hv hx hy ihx ihy =>
    intro hs hK hle p hp
    have hDx := hD x (by simp [Term.size] at hs; omega) hx
    have hDy := hD y (by simp [Term.size] at hs; omega) hy
    obtain ⟨vx, vy⟩ := NF_phi_lt (S := S) hn
    set j := lvl (Term.val S (.phi x y)) with hjdef
    have hvω : Term.val S (.phi x y) < Om (ω : Ordinal.{0}) := lt_of_le_of_lt hle hcω
    have hxk : ev σ (Ex S σ L x) < OmT σ (j + 1) :=
      lt_of_lt_of_le hDx.lt (OmT_mono hσ (by have := lvl_mono hvω vx.le; omega))
    have hyk : ev σ (Ex S σ L y) < OmT σ (j + 1) :=
      lt_of_lt_of_le hDy.lt (OmT_mono hσ (by have := lvl_mono hvω vy.le; omega))
    have hjm : j ≤ lvl (Term.val S c) := lvl_mono hcω hle
    rw [Ex, EL_phi hv, ← hjdef] at hp
    simp only [Kst] at hp
    split_ifs at hp with hjk
    · simp at hp
    rcases List.mem_cons.1 hp with hp | hp
    · subst hp
      exact (gcodephi_lt_Pk hσ hDx.nf hDy.nf hxk hyk).trans (hlvX j hjm).1
    · rcases List.mem_cons.1 (gKst_codephi hσ (by omega) hp) with h | h
      · subst h; exact hxk.trans_le ((hlvX j hjm).2.le)
      · rcases List.mem_append.1 h with h | h
        · exact ihx (by simp [Term.size] at hs; omega) hK.1 (vx.le.trans hle) p h
        · exact ihy (by simp [Term.size] at hs; omega) hK.2 (vy.le.trans hle) p h
  | @psiA s' c' hn hv hs0 _ _ _ _ _ =>
    intro _ _ _ p hp
    have h0 : natOf (Term.val S s') = 0 := by rw [hs0]; exact natOf_nat 0
    rw [Ex, EL_psi0 hv h0] at hp
    simp [Kst] at hp
  | @psiS s' c' j hn hv hj0 hj hcω' hcc ihc =>
    intro hs hK hle p hp
    have hnat : natOf (Term.val S s') ≠ 0 := by rw [hj, natOf_nat]; exact hj0
    rw [Ex, EL_psiS hv hnat, hj, natOf_nat] at hp
    simp only [Kst] at hp
    split_ifs at hp with hjk
    · simp at hp
    have hjk' : k + 1 ≤ j := not_lt.1 hjk
    rcases hK with hK | ⟨hca, _, hKc⟩
    · exfalso
      have h1 := (Term.cmp_lt_iff S hn hμ).1 hK
      have h2 := (psiS_bounds_nat s' c' hj).1
      have h3 := (psiS_bounds_nat s c hk).2
      have h4 : OmT 1 (k + 1) ≤ Om (j : Ordinal.{0}) := by
        rw [Om_nat_eq_OmT (by omega)]; exact OmT_mono base_one hjk'
      exact absurd h1 (not_lt.2 (h3.le.trans (h4.trans h2.le)))
    have hc_lt : Term.val S c' < Term.val S c := (Term.cmp_lt_iff S hn.2.1 hμ.2.1).1 hca
    have hsc : c'.size < c.size := by simp [Term.size] at hs; omega
    have hDc' := hD c' (le_of_lt hsc) hcc
    have hEc : ev σ (Ex S σ L c') < ev σ (Ex S σ L c) := hM c' hsc hcc hc_lt
    have hjm : j ≤ lvl (Term.val S c) := by
      have := lvl_mono hcω hle; rw [lvl_psiS s' c' hj] at this; exact this
    have hFc : ev σ (gFc σ (Ex S σ L c')) < X := gFc_lt hσ hDc'.nf hDc.nf hEcω hEc
    rcases List.mem_cons.1 hp with hp | hp
    · subst hp
      rw [gev_codepsi hσ hDc'.nf (hEc.trans hEcω)]
      exact hXP (hlvX j hjm).1 hFc
    · rcases List.mem_append.1 (Kst_plus σ (k + 1) _ _ hp) with h | h
      · rw [Kst_Pk (by omega)] at h
        simp at h
        rcases h with rfl | rfl
        · rw [gev_Omk hσ]; exact (hlvX j hjm).2
        · exact hX0
      · by_cases hc0' : ev σ (Ex S σ L c') = 0
        · rw [gFc_zero hσ hc0'] at h; simp [Kst] at h
        have h' := gKst_Fc hσ hc0' h
        split_ifs at h' with hl
        · simp at h'
        rcases List.mem_cons.1 h' with h' | h'
        · subst h'
          exact (gev_Fc_pos hσ hDc'.nf (hEc.trans hEcω) hc0').1.trans hFc
        · rcases List.mem_append.1 h' with h' | h'
          · rw [Kst_Omk (by omega)] at h'; simp at h'; subst h'; exact hX0
          · rcases List.mem_append.1 h' with h' | h'
            · rw [Kst_Omk (by omega)] at h'; simp at h'; subst h'; exact hX0
            · exact ihc (le_of_lt hsc) hKc hc_lt.le p h'

end Googology.Trans.PoR.InaccPsi.R2.Bt

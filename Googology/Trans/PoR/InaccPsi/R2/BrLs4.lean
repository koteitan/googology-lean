import Googology.Trans.PoR.InaccPsi.R2.BrLs3

/-!
# LOW-STEP, part 4: the class of terms and Lemma ARG1

Fix `S`, a base `σ` and a list `L` of summands; `A = AA S L` is the sum of `L`, with `k_A` (`kA S L`, the
length of `L`) summands; `GoodL S L`: the summands are nonzero, additively principal, at least `θ`, and weakly
decreasing.  For `A = A_{ω·m+n} = Ω_ω + θ·(ω·m + n)` the list is `Alist S m n` (`goodL_Alist`, `AA_eq`).
`CL t`: the normal forms handled by the map `E` (parameters below `σ`; sums and `φ`-terms of the class;
`Ωₖ`; `ψ_{Ω_{k+1}}(c)`, `k ≥ 1`, with `c < Ω_ω` of the class; the `A`-clause `ψ_{Ω₁}(A + ζ)`, `ζ < θ`
of the class).  `arg1` (Lemma ARG1): every normal form below `ψ_{Ω₁}(A + θ)` is in the class, when
`ψ_{Ω₁}(A) ≤ σ`.

The statements are proved for `A` the sum of any list `L` of summands (namespace `R2.Bt`: `AA S L` the
sum of `L`, `kA S L` its length, `GoodL S L` where it is needed); the original statements for
`A = A_{ω·m+n}` (namespace `R2.Br`, the same names) follow as corollaries at `L = Alist S m n`.
-/

/-! ## The list version (namespace `R2.Bt`) -/

namespace Googology.Trans.PoR.InaccPsi.R2.Bt

open Googology.Trans.PoR.InaccPsi.R2.Br

open Ordinal Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq

variable (S : InaccSeq.{0}) (σ : Ordinal.{0}) (L : List Ordinal.{0})

/-- `A`: the sum of the list `L` of its summands. -/
noncomputable abbrev AA (_S : InaccSeq.{0}) (L : List Ordinal.{0}) : Ordinal.{0} := L.foldr (· + ·) 0

/-- The number of summands of `A`. -/
abbrev kA (_S : InaccSeq.{0}) (L : List Ordinal.{0}) : ℕ := L.length

/-- The summands of `A`: nonzero additively principal ordinals, each at least `θ = ψ_{Ω₂}(Ω_ω)`, weakly
decreasing. -/
structure GoodL (S : InaccSeq.{0}) (L : List Ordinal.{0}) : Prop where
  prin : ∀ l ∈ L, IsPrincipal (· + ·) l ∧ l ≠ 0 ∧ ConjT.th S ≤ l
  pw : L.Pairwise (· ≥ ·)

/-- The class of terms. -/
inductive CL : Term → Prop
  | par {t : Term} : Term.NF t → Term.val S t < σ → CL t
  | add {a b : Term} : Term.NF (.add a b) → ¬ Term.val S (.add a b) < σ → CL a → CL b → CL (.add a b)
  | phi {a b : Term} : Term.NF (.phi a b) → ¬ Term.val S (.phi a b) < σ → CL a → CL b → CL (.phi a b)
  | om {b : Term} {k : ℕ} : Term.NF (.om b) → ¬ Term.val S (.om b) < σ → k ≠ 0 → Term.val S b = k →
      CL (.om b)
  | psiS {s c : Term} {k : ℕ} : Term.NF (.psiS s c) → ¬ Term.val S (.psiS s c) < σ → k ≠ 0 →
      Term.val S s = k → Term.val S c < Om (ω : Ordinal.{0}) → CL c → CL (.psiS s c)
  | psiA {s c : Term} : Term.NF (.psiS s c) → ¬ Term.val S (.psiS s c) < σ → Term.val S s = 0 →
      Term.NF (dropT (kA S L) c) →
      Term.val S c = AA S L + Term.val S (dropT (kA S L) c) →
      Term.val S (dropT (kA S L) c) < ConjT.th S → CL (dropT (kA S L) c) → CL (.psiS s c)

variable {S σ L}

theorem CL.NF {t : Term} (h : CL S σ L t) : Term.NF t := by
  cases h <;> assumption

/-! ## The argument `A + ζ` -/

/-- `ψ_{Ω₁}(A + ζ)` with `ζ < θ`: `dropT` gives `ζ`. -/
theorem dropT_A (hL : GoodL S L) {c : Term} (hc : Term.NF c) {z : Ordinal.{0}} (hz : z < ConjT.th S)
    (hv : Term.val S c = AA S L + z) :
    Term.NF (dropT (kA S L) c) ∧ Term.val S (dropT (kA S L) c) = z := by
  refine dropT_spec L c z hc (fun l hl => ⟨(hL.prin l hl).1, (hL.prin l hl).2.1⟩)
    hL.pw (fun l hl => ?_) hv
  obtain ⟨hp, h0, hθ⟩ := hL.prin l hl
  obtain ⟨hlt, _⟩ := principal_lt_next hp h0
  exact (hz.trans_le hθ).trans hlt

/-! ## Lemma ARG1 -/

/-- The inequality `ψ_{Ω₁}(c) < ψ_{Ω₁}(a)` gives `c < a` (InaccPsi F11). -/
theorem lt_of_psi_lt {κ c a : Ordinal.{0}} (hκ : S.InR κ) (h : S.psi c κ < S.psi a κ) : c < a := by
  by_contra hle; rw [not_lt] at hle
  exact absurd h (not_lt.2 (psi_mono hκ hle).1)

theorem InR_Om1 : S.InR (Om (1 : Ordinal.{0})) := by simpa using InR_Om_succ (S := S) 0

/-- **Lemma ARG1.**  `P1`: a normal form below `ψ_{Ω₁}(A + θ)` is in the class.  `Ptop`: a part of `ζ`
(through sums and `φ`) for a root `ψ_{Ω₁}(A + ζ)`.  `Pin`: a part of the argument `d` of an anchor
`ψ_{Ω₂}(d)`, `d < Ω_ω`.  Both carry the `K`-condition of the countable root. -/
theorem arg1 (hL : GoodL S L) (hσ : Base σ) (hA : S.psi (AA S L) (Om 1) ≤ σ) : ∀ N : ℕ,
    (∀ t : Term, t.size ≤ N → Term.NF t →
      Term.val S t < S.psi (AA S L + ConjT.th S) (Om 1) → CL S σ L t) ∧
    (∀ s c u : Term, u.size ≤ N → Term.NF (.psiS s c) → Term.val S s = 0 →
      Term.val S c < AA S L + ConjT.th S → Term.NF u → Term.KLt (.psiS s c) u c →
      Term.val S u < ConjT.th S → CL S σ L u) ∧
    (∀ s c sa da u : Term, u.size ≤ N → Term.NF (.psiS s c) → Term.val S s = 0 →
      Term.val S c < AA S L + ConjT.th S → Term.NF (.psiS sa da) → Term.val S sa = 1 →
      Term.val S da < Om (ω : Ordinal.{0}) → Term.NF u → Term.KLt (.psiS s c) u c →
      Term.KLt (.psiS sa da) u da → Term.val S u < Om (ω : Ordinal.{0}) → CL S σ L u) := by
  have hInR := InR_Om1 (S := S)
  have hθ2 : ConjT.th S < Om ((1 : Ordinal.{0}) + 1) := th_lt_Om2
  -- a countable collapse of the root is below the root, so a parameter or an `A`-clause term
  intro N
  induction N with
  | zero =>
    exact ⟨fun t h => absurd (Term.size_pos t) (by omega), fun _ _ u h => absurd (Term.size_pos u) (by omega),
      fun _ _ _ _ u h => absurd (Term.size_pos u) (by omega)⟩
  | succ N ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    -- P1
    have P1 : ∀ t : Term, t.size ≤ N + 1 → Term.NF t →
        Term.val S t < S.psi (AA S L + ConjT.th S) (Om 1) → CL S σ L t := by
      intro t hs ht hv
      by_cases hσt : Term.val S t < σ
      · exact CL.par ht hσt
      have hv1 : Term.val S t < Om (1 : Ordinal.{0}) := hv.trans (psi_lt hInR _)
      cases t with
      | zero => exact absurd (hσ.pos) (by simpa [Term.val] using hσt)
      | add a b =>
        exact CL.add ht hσt (ih1 a (by simp [Term.size] at hs; omega) ht.1
          (lt_of_le_of_lt (val_le_add_left a b) hv))
          (ih1 b (by simp [Term.size] at hs; omega) ht.2.1 (lt_of_le_of_lt (val_le_add_right a b) hv))
      | phi a b =>
        obtain ⟨h1, h2⟩ := NF_phi_lt (S := S) ht
        exact CL.phi ht hσt (ih1 a (by simp [Term.size] at hs; omega) ht.1 (h1.trans hv))
          (ih1 b (by simp [Term.size] at hs; omega) ht.2.1 (h2.trans hv))
      | om b => exact absurd (lt_of_le_of_lt (Om1_le_val_om ht.1 ht.2.1) hv1) (lt_irrefl _)
      | inacc k =>
        simp only [Term.val] at hv1
        exact absurd hv1 (not_lt.2 (Low.Om_one_le_I (S := S) k))
      | inaccW =>
        simp only [Term.val] at hv1
        exact absurd hv1 (not_lt.2 ((Low.Om_one_le_I (S := S) 0).trans (S.I_le_Iw 0)))
      | psiI k b =>
        simp only [Term.val] at hv1
        exact absurd hv1 (not_lt.2 (Om_one_lt_psiI _ _).le)
      | psiS s c =>
        have hs0 : Term.val S s = 0 := by
          by_contra hne
          have h1 := (Term.val_psiS_bounds S s c).1
          have h2 : Om (1 : Ordinal.{0}) ≤ Om (Term.val S s) :=
            Om_le_Om.2 (Order.one_le_iff_ne_zero.2 hne)
          exact absurd (lt_of_le_of_lt h2 (h1.trans hv1)) (lt_irrefl _)
        have hval : Term.val S (.psiS s c) = S.psi (Term.val S c) (Om 1) := by
          simp only [Term.val]; rw [hs0, zero_add]
        have hcA : AA S L ≤ Term.val S c := by
          by_contra hlt
          rw [not_le] at hlt
          have hsem := (Term.sem_of_NF (S := S) ht).2.2
          rw [hs0, zero_add] at hsem
          have := psi_lt_psi hInR hlt hsem
          rw [← hval] at this
          exact hσt (this.trans_le hA)
        have hcAθ : Term.val S c < AA S L + ConjT.th S := by
          rw [hval] at hv; exact lt_of_psi_lt hInR hv
        obtain ⟨z, hz⟩ := le_iff_exists_add.1 hcA
        have hzθ : z < ConjT.th S := by rw [hz] at hcAθ; exact (add_lt_add_iff_left _).1 hcAθ
        obtain ⟨hnz, hvz⟩ := dropT_A hL ht.2.1 hzθ hz
        refine CL.psiA ht hσt hs0 hnz (by rw [hvz]; exact hz) (by rw [hvz]; exact hzθ) ?_
        -- the parts of `ζ`
        have hK : Term.KLt (.psiS s c) (dropT (kA S L) c) c := by
          have key : ∀ (k : ℕ) (x : Term), Term.KLt (.psiS s c) x c →
              Term.KLt (.psiS s c) (dropT k x) c := by
            intro k
            induction k with
            | zero => intro x h; exact h
            | succ k ihk =>
              intro x h
              cases x <;> simp only [dropT] <;> first | trivial | exact ihk _ h.2
          exact key _ c ht.2.2
        exact ih2 s c _ (by have := dropT_size (kA S L) c; simp [Term.size] at hs; omega) ht hs0
          hcAθ hnz hK (by rw [hvz]; exact hzθ)
    refine ⟨P1, ?_, ?_⟩
    · -- Ptop
      intro s c u hs hμ hs0 hcθ hu hK hv
      by_cases hσu : Term.val S u < σ
      · exact CL.par hu hσu
      have hμval : Term.val S (.psiS s c) = S.psi (Term.val S c) (Om 1) := by
        simp only [Term.val]; rw [hs0, zero_add]
      cases u with
      | zero => exact absurd hσ.pos (by simpa [Term.val] using hσu)
      | add a b =>
        exact CL.add hu hσu (ih2 s c a (by simp [Term.size] at hs; omega) hμ hs0 hcθ hu.1 hK.1
          (lt_of_le_of_lt (val_le_add_left a b) hv))
          (ih2 s c b (by simp [Term.size] at hs; omega) hμ hs0 hcθ hu.2.1 hK.2
          (lt_of_le_of_lt (val_le_add_right a b) hv))
      | phi a b =>
        obtain ⟨h1, h2⟩ := NF_phi_lt (S := S) hu
        exact CL.phi hu hσu (ih2 s c a (by simp [Term.size] at hs; omega) hμ hs0 hcθ hu.1 hK.1 (h1.trans hv))
          (ih2 s c b (by simp [Term.size] at hs; omega) hμ hs0 hcθ hu.2.1 hK.2 (h2.trans hv))
      | om b =>
        simp only [Term.val] at hv
        have hb : Term.val S b < 1 + 1 := Om_lt_Om.1 (hv.trans hθ2)
        have hb1 : Term.val S b = 1 := by
          have h0 := Term.val_ne_zero S hu.1 hu.2.1
          rw [← Order.succ_eq_add_one, Order.lt_succ_iff] at hb
          exact le_antisymm hb (Order.one_le_iff_ne_zero.2 h0)
        exact CL.om hu hσu one_ne_zero (by rw [hb1]; norm_num)
      | inacc k =>
        simp only [Term.val] at hv
        exact absurd (hv.trans (hθ2.trans Om2_lt_Om_omega)) (not_lt.2 (Om_omega_lt_I k).le)
      | inaccW =>
        simp only [Term.val] at hv
        exact absurd (hv.trans (hθ2.trans Om2_lt_Om_omega))
          (not_lt.2 ((Om_omega_lt_I 0).trans_le (S.I_le_Iw 0)).le)
      | psiI k b =>
        simp only [Term.val] at hv
        exact absurd (hv.trans (hθ2.trans Om2_lt_Om_omega)) (not_lt.2 (Om_omega_lt_psiI _ _).le)
      | psiS s' d =>
        by_cases hs'0 : Term.val S s' = 0
        · -- a countable atom: below the root
          have hroot : Term.val S (.psiS s c) ≤ S.psi (AA S L + ConjT.th S) (Om 1) := by
            rw [hμval]; exact (psi_mono hInR hcθ.le).1
          have hlt : Term.val S (.psiS s' d) < Term.val S (.psiS s c) := by
            rcases hK with hK | ⟨hdc, _, _⟩
            · exact (Term.cmp_lt_iff S hu hμ).1 hK
            · have hdc' : Term.val S d < Term.val S c := (Term.cmp_lt_iff S hu.2.1 hμ.2.1).1 hdc
              have hsem := (Term.sem_of_NF (S := S) hu).2.2
              simp only [Term.val] at hsem ⊢
              rw [hs'0, zero_add] at hsem ⊢
              rw [hs0, zero_add]
              exact psi_lt_psi hInR hdc' hsem
          exact P1 _ hs hu (hlt.trans_le hroot)
        · -- a level-1 atom `ψ_{Ω₂}(d)` with `d < Ω_ω`
          have hb := Term.val_psiS_bounds S s' d
          have hs'1 : Term.val S s' = 1 := by
            by_contra hne
            have h1 : (1 : Ordinal.{0}) < Term.val S s' :=
              lt_of_le_of_ne (Order.one_le_iff_ne_zero.2 hs'0) (Ne.symm hne)
            have : Om ((1 : Ordinal.{0}) + 1) ≤ Om (Term.val S s') := by
              refine Om_le_Om.2 ?_; rw [← Order.succ_eq_add_one]; exact Order.succ_le_of_lt h1
            exact absurd (this.trans_lt (hb.1.trans (hv.trans hθ2))) (lt_irrefl _)
          have hdω : Term.val S d < Om (ω : Ordinal.{0}) := by
            by_contra hge; rw [not_lt] at hge
            have h1 := (psi_mono (InR_Om_succ (S := S) 1) hge).1
            have h2 : Term.val S (.psiS s' d) = S.psi (Term.val S d) (Om (1 + 1)) := by
              simp only [Term.val]; rw [hs'1]
            rw [h2] at hv
            exact absurd hv (not_lt.2 h1)
          rcases hK with hK | ⟨_, _, hKd⟩
          · exfalso
            have h1 := (Term.cmp_lt_iff S hu hμ).1 hK
            have h2 := (Term.val_psiS_bounds S s c).2
            rw [hs0, zero_add] at h2
            have h3 : Om (1 : Ordinal.{0}) ≤ Term.val S (.psiS s' d) := by
              rw [hs'1] at hb; exact hb.1.le
            exact absurd (h1.trans h2) (not_lt.2 h3)
          refine CL.psiS hu hσu one_ne_zero (by rw [hs'1]; norm_num) hdω ?_
          exact ih3 s c s' d d (by simp [Term.size] at hs; omega) hμ hs0 hcθ hu hs'1 hdω hu.2.1 hKd
            hu.2.2 hdω
    · -- Pin
      intro s c sa da u hs hμ hs0 hcθ hμa hsa1 hdaω hu hK hKa hv
      by_cases hσu : Term.val S u < σ
      · exact CL.par hu hσu
      have hμval : Term.val S (.psiS s c) = S.psi (Term.val S c) (Om 1) := by
        simp only [Term.val]; rw [hs0, zero_add]
      cases u with
      | zero => exact absurd hσ.pos (by simpa [Term.val] using hσu)
      | add a b =>
        exact CL.add hu hσu (ih3 s c sa da a (by simp [Term.size] at hs; omega) hμ hs0 hcθ hμa hsa1 hdaω
            hu.1 hK.1 hKa.1 (lt_of_le_of_lt (val_le_add_left a b) hv))
          (ih3 s c sa da b (by simp [Term.size] at hs; omega) hμ hs0 hcθ hμa hsa1 hdaω hu.2.1 hK.2 hKa.2
            (lt_of_le_of_lt (val_le_add_right a b) hv))
      | phi a b =>
        obtain ⟨h1, h2⟩ := NF_phi_lt (S := S) hu
        exact CL.phi hu hσu (ih3 s c sa da a (by simp [Term.size] at hs; omega) hμ hs0 hcθ hμa hsa1 hdaω
            hu.1 hK.1 hKa.1 (h1.trans hv))
          (ih3 s c sa da b (by simp [Term.size] at hs; omega) hμ hs0 hcθ hμa hsa1 hdaω hu.2.1 hK.2 hKa.2
            (h2.trans hv))
      | om b =>
        simp only [Term.val] at hv
        obtain ⟨k, hk⟩ := lt_omega0.1 (Om_lt_Om.1 hv)
        refine CL.om hu hσu ?_ hk
        rintro rfl
        exact Term.val_ne_zero S hu.1 hu.2.1 (by rw [hk]; rfl)
      | inacc k =>
        simp only [Term.val] at hv; exact absurd hv (not_lt.2 (Om_omega_lt_I k).le)
      | inaccW =>
        simp only [Term.val] at hv
        exact absurd hv (not_lt.2 ((Om_omega_lt_I 0).trans_le (S.I_le_Iw 0)).le)
      | psiI k b =>
        simp only [Term.val] at hv; exact absurd hv (not_lt.2 (Om_omega_lt_psiI _ _).le)
      | psiS s' d =>
        have hb := Term.val_psiS_bounds S s' d
        obtain ⟨j, hj⟩ : ∃ j : ℕ, Term.val S s' = j := lt_omega0.1 (Om_lt_Om.1 (hb.1.trans hv))
        rcases Nat.eq_zero_or_pos j with rfl | hjpos
        · -- countable: below the root
          have hlt : Term.val S (.psiS s' d) < Term.val S (.psiS s c) := by
            rcases hK with hK | ⟨hdc, _, _⟩
            · exact (Term.cmp_lt_iff S hu hμ).1 hK
            · have hdc' : Term.val S d < Term.val S c := (Term.cmp_lt_iff S hu.2.1 hμ.2.1).1 hdc
              rw [hμval]
              simp only [Term.val]
              rw [hj]; simp only [Nat.cast_zero, zero_add]
              have := (Term.sem_of_NF (S := S) hu).2.2
              rw [hj] at this; simp only [Nat.cast_zero, zero_add] at this
              exact psi_lt_psi hInR hdc' this
          refine P1 _ hs hu (hlt.trans_le ?_)
          rw [hμval]; exact (psi_mono hInR hcθ.le).1
        · -- uncountable: visited from the root; visited or a stop for the anchor
          have hgt : Term.val S (.psiS s c) < Term.val S (.psiS s' d) := by
            have h1 := (Term.val_psiS_bounds S s c).2
            rw [hs0, zero_add] at h1
            refine h1.trans_le (hb.1.le.trans' ?_)
            refine Om_le_Om.2 ?_; rw [hj]; exact_mod_cast hjpos
          rcases hK with hK | ⟨_, _, hKd⟩
          · exact absurd ((Term.cmp_lt_iff S hu hμ).1 hK) (not_lt.2 hgt.le)
          have hdda : Term.val S d < Term.val S da ∧ (Term.KLt (.psiS sa da) d da ∨ True) := by
            rcases hKa with hKa | ⟨hdd, _, hKd'⟩
            · -- a stop for the anchor: level `1`, so `d < da` by monotonicity
              have hlt := (Term.cmp_lt_iff S hu hμa).1 hKa
              have hj1 : j = 1 := by
                by_contra hne
                have h2 : 2 ≤ j := by omega
                have h3 : Om ((1 : Ordinal.{0}) + 1) ≤ Om (Term.val S s') := by
                  refine Om_le_Om.2 ?_; rw [hj]; exact_mod_cast h2
                have h4 := (Term.val_psiS_bounds S sa da).2
                rw [hsa1] at h4
                exact absurd (hlt.trans h4) (not_lt.2 (h3.trans hb.1.le))
              subst hj1
              refine ⟨lt_of_psi_lt (InR_Om_succ (S := S) 1) ?_, Or.inr trivial⟩
              simp only [Term.val] at hlt
              rw [hj, hsa1] at hlt; simpa using hlt
            · exact ⟨(Term.cmp_lt_iff S hu.2.1 hμa.2.1).1 hdd, Or.inl hKd'⟩
          refine CL.psiS hu hσu hjpos.ne' hj (hdda.1.trans hdaω) ?_
          -- the argument `d`: under the same anchor, or under `ψ_{Ω₂}(d)` itself
          rcases hKa with hKa | ⟨_, _, hKd'⟩
          · have hlt := (Term.cmp_lt_iff S hu hμa).1 hKa
            have hj1 : j = 1 := by
              by_contra hne
              have h2 : 2 ≤ j := by omega
              have h3 : Om ((1 : Ordinal.{0}) + 1) ≤ Om (Term.val S s') := by
                refine Om_le_Om.2 ?_; rw [hj]; exact_mod_cast h2
              have h4 := (Term.val_psiS_bounds S sa da).2
              rw [hsa1] at h4
              exact absurd (hlt.trans h4) (not_lt.2 (h3.trans hb.1.le))
            subst hj1
            exact ih3 s c s' d d (by simp [Term.size] at hs; omega) hμ hs0 hcθ hu (by rw [hj, Nat.cast_one])
              (hdda.1.trans hdaω) hu.2.1 hKd hu.2.2 (hdda.1.trans hdaω)
          · exact ih3 s c sa da d (by simp [Term.size] at hs; omega) hμ hs0 hcθ hμa hsa1 hdaω hu.2.1 hKd
              hKd' (hdda.1.trans hdaω)

end Googology.Trans.PoR.InaccPsi.R2.Bt

/-! ## The interface for `A = A_{ω·m+n}` (namespace `R2.Br`): corollaries at `L = Alist S m n` -/

namespace Googology.Trans.PoR.InaccPsi.R2.Br

open Ordinal Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq

variable (S : InaccSeq.{0}) (σ : Ordinal.{0}) (m n : ℕ)

/-- `A = A_{ω·m+n}`. -/
noncomputable abbrev AA : Ordinal.{0} := ConjT.Aη S (ω * m + n)

/-- The number of summands of `A`. -/
noncomputable abbrev kA : ℕ := (Alist S m n).length

/-- The class of terms for `A = A_{ω·m+n}`: the class `Bt.CL` of the list `Alist S m n`. -/
abbrev CL : Term → Prop := Bt.CL S σ (Alist S m n)

variable {S σ m n}

theorem CL.NF {t : Term} (h : CL S σ m n t) : Term.NF t := by
  apply Bt.CL.NF <;> assumption

/-! ## The argument `A + ζ` -/

theorem Alist_prin : ∀ l ∈ Alist S m n, IsPrincipal (· + ·) l ∧ l ≠ 0 ∧ ConjT.th S ≤ l := by
  intro l hl
  simp only [Alist, List.mem_cons, List.mem_append, List.mem_replicate] at hl
  rcases hl with rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact ⟨Om_omega_principal, (Om_pos omega0_ne_zero).ne',
      (th_lt_Om2.trans Om2_lt_Om_omega).le⟩
  · exact ⟨th_omega_principal, (mul_pos th_pos omega0_pos).ne', le_mul_left _ omega0_pos⟩
  · exact ⟨(ConjT.SC_th S).isPrincipal, th_pos.ne', le_rfl⟩

theorem Alist_pairwise : (Alist S m n).Pairwise (· ≥ ·) := by
  simp only [Alist, List.pairwise_cons, List.mem_append, List.mem_replicate, List.pairwise_append]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro x (⟨_, rfl⟩ | ⟨_, rfl⟩)
    · exact Om_omega_gt_th_omega.le
    · exact (th_lt_Om2.trans Om2_lt_Om_omega).le
  · exact List.pairwise_replicate.2 (Or.inr le_rfl)
  · exact List.pairwise_replicate.2 (Or.inr le_rfl)
  · rintro x ⟨_, rfl⟩ y ⟨_, rfl⟩; exact le_mul_left _ omega0_pos

/-- The summands of `A_{ω·m+n}` form a `GoodL` list. -/
theorem goodL_Alist : Bt.GoodL S (Alist S m n) := ⟨Alist_prin, Alist_pairwise⟩

/-- `A_{ω·m+n}` is the sum of its summand list. -/
theorem AA_eq : AA S m n = Bt.AA S (Alist S m n) := (Alist_sum m n).symm

/-- `ψ_{Ω₁}(A + ζ)` with `ζ < θ`: `dropT` gives `ζ`. -/
theorem dropT_A {c : Term} (hc : Term.NF c) {z : Ordinal.{0}} (hz : z < ConjT.th S)
    (hv : Term.val S c = AA S m n + z) :
    Term.NF (dropT (kA S m n) c) ∧ Term.val S (dropT (kA S m n) c) = z := by
  simp only [AA_eq] at *
  apply Bt.dropT_A <;> first | assumption | exact goodL_Alist

/-! ## Lemma ARG1 -/

/-- The inequality `ψ_{Ω₁}(c) < ψ_{Ω₁}(a)` gives `c < a` (InaccPsi F11). -/
theorem lt_of_psi_lt {κ c a : Ordinal.{0}} (hκ : S.InR κ) (h : S.psi c κ < S.psi a κ) : c < a := by
  apply Bt.lt_of_psi_lt <;> assumption

theorem InR_Om1 : S.InR (Om (1 : Ordinal.{0})) := by
  exact Bt.InR_Om1

/-- **Lemma ARG1.**  `P1`: a normal form below `ψ_{Ω₁}(A + θ)` is in the class.  `Ptop`: a part of `ζ`
(through sums and `φ`) for a root `ψ_{Ω₁}(A + ζ)`.  `Pin`: a part of the argument `d` of an anchor
`ψ_{Ω₂}(d)`, `d < Ω_ω`.  Both carry the `K`-condition of the countable root. -/
theorem arg1 (hσ : Base σ) (hA : S.psi (AA S m n) (Om 1) ≤ σ) : ∀ N : ℕ,
    (∀ t : Term, t.size ≤ N → Term.NF t →
      Term.val S t < S.psi (AA S m n + ConjT.th S) (Om 1) → CL S σ m n t) ∧
    (∀ s c u : Term, u.size ≤ N → Term.NF (.psiS s c) → Term.val S s = 0 →
      Term.val S c < AA S m n + ConjT.th S → Term.NF u → Term.KLt (.psiS s c) u c →
      Term.val S u < ConjT.th S → CL S σ m n u) ∧
    (∀ s c sa da u : Term, u.size ≤ N → Term.NF (.psiS s c) → Term.val S s = 0 →
      Term.val S c < AA S m n + ConjT.th S → Term.NF (.psiS sa da) → Term.val S sa = 1 →
      Term.val S da < Om (ω : Ordinal.{0}) → Term.NF u → Term.KLt (.psiS s c) u c →
      Term.KLt (.psiS sa da) u da → Term.val S u < Om (ω : Ordinal.{0}) → CL S σ m n u) := by
  simp only [AA_eq] at *
  apply Bt.arg1 <;> first | assumption | exact goodL_Alist

end Googology.Trans.PoR.InaccPsi.R2.Br

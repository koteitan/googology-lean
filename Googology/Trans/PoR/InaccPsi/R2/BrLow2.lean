import Googology.Trans.PoR.InaccPsi.R2.BrLow1
import Googology.Trans.PoR.InaccPsi.LowSeg

/-!
# Lower bound, part 2: the InaccPsi side

For an InaccPsi sequence `S : InaccSeq.{0}`:
* `Cw S t`: the class of InaccPsi terms that the map `E` handles (no `I`-symbols; `Ωₖ` and `ψ_{Ω_{k+1}}`
  with finite `k`; collapse arguments below `Ω_ω`);
* `Cw_val_lt`: such normal forms are below `Ω_ω`; the levels of `Ωₖ` and `ψ_{Ω_{k+1}}(a)` are `k`;
* `parts_b` (Lemma PARTS (b) of the paper proof of Theorem LOW-0): a level-`k` principal term visited
  from `μ = ψ_{Ω_{k+1}}(a)` (in the sense of `KLt μ r a`) is below `μ`;
* `cw_of_lt` (Lemma ARG0): every normal form below `ψ_{Ω₁}(Ω_ω)` is in the class.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Br

open Ordinal Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq

/-- `natOf v = v` for a finite `v`. -/
noncomputable def natOf (v : Ordinal.{0}) : ℕ := sInf {n : ℕ | v ≤ n}

theorem natOf_nat (n : ℕ) : natOf (n : Ordinal.{0}) = n := by
  unfold natOf
  refine le_antisymm (Nat.sInf_le (show (n : Ordinal.{0}) ≤ (n : Ordinal.{0}) from le_refl _))
    (le_csInf ⟨n, show (n : Ordinal.{0}) ≤ (n : Ordinal.{0}) from le_refl _⟩ fun m hm => ?_)
  exact_mod_cast hm

variable (S : InaccSeq.{0})

/-- The class of terms handled by `E`. -/
def Cw : Term → Prop
  | .zero => True
  | .add a b => Cw a ∧ Cw b
  | .phi a b => Cw a ∧ Cw b
  | .om b => ∃ k : ℕ, k ≠ 0 ∧ Term.val S b = k
  | .psiS s a => (∃ k : ℕ, Term.val S s = k) ∧ Term.val S a < Om (ω : Ordinal.{0}) ∧ Cw a
  | _ => False

variable {S}

theorem Om_nat_eq_OmT {k : ℕ} (hk : k ≠ 0) : Om (k : Ordinal.{0}) = OmT 1 k :=
  (OmT_pos_of_ne hk 1).symm

theorem Om_omega_SC : SC (Om (ω : Ordinal.{0})) := SC_Om omega0_ne_zero

/-- Normal forms of the class are below `Ω_ω`. -/
theorem Cw_val_lt : ∀ {t : Term}, Cw S t → Term.NF t → Term.val S t < Om (ω : Ordinal.{0})
  | .zero, _, _ => Om_pos omega0_ne_zero
  | .add a b, h, hn => by
    simp only [Term.val]
    exact Om_omega_principal (Cw_val_lt h.1 hn.1) (Cw_val_lt h.2 hn.2.1)
  | .phi a b, h, hn => by
    simp only [Term.val]
    exact Om_omega_SC.2 _ (Cw_val_lt h.1 hn.1) _ (Cw_val_lt h.2 hn.2.1)
  | .om b, ⟨k, _, hk⟩, _ => by
    simp only [Term.val]; rw [hk]; exact Om_lt_Om_omega k
  | .psiS s a, ⟨⟨k, hk⟩, _, _⟩, _ => by
    have := (Term.val_psiS_bounds S s a).2
    rw [hk] at this
    have h2 : ((k : Ordinal.{0}) + 1) = ((k + 1 : ℕ) : Ordinal.{0}) := by push_cast; rfl
    rw [h2] at this
    exact this.trans (Om_lt_Om_omega _)

theorem val_om_of_Cw {b : Term} {k : ℕ} (hk : Term.val S b = k) :
    Term.val S (.om b) = Om (k : Ordinal.{0}) := by simp only [Term.val]; rw [hk]

theorem lvl_Om {k : ℕ} (hk : k ≠ 0) : lvl (Om (k : Ordinal.{0})) = k := by
  rw [Om_nat_eq_OmT hk]
  exact lvl_eq le_rfl (OmT_lt_succ base_one k) hk

theorem psiS_bounds_nat (s a : Term) {k : ℕ} (hk : Term.val S s = k) :
    Om (k : Ordinal.{0}) < Term.val S (.psiS s a) ∧ Term.val S (.psiS s a) < OmT 1 (k + 1) := by
  have h := Term.val_psiS_bounds S s a
  rw [hk] at h
  refine ⟨h.1, ?_⟩
  rw [OmT_succ]; exact h.2

theorem lvl_psiS (s a : Term) {k : ℕ} (hk : Term.val S s = k) :
    lvl (Term.val S (.psiS s a)) = k := by
  obtain ⟨h1, h2⟩ := psiS_bounds_nat s a hk
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · have := lvl_le_of_lt h2; omega
  · exact lvl_eq ((Om_nat_eq_OmT hpos.ne') ▸ h1.le) h2 hpos.ne'

/-- `Ω₁ ≤ ψ` values etc.: an `I`-symbol is above `Ω_ω`. -/
theorem Om_omega_lt_I (n : ℕ) : Om (ω : Ordinal.{0}) < S.I n := by
  rw [← S.fix n]
  refine Om_lt_Om.2 ?_
  have h := S.uncountable n
  by_contra hle
  rw [not_lt] at hle
  have := Ordinal.card_le_card hle
  rw [Ordinal.card_omega0] at this
  exact absurd (lt_of_lt_of_le h this) (lt_irrefl _)

theorem Om_omega_lt_psiI (a : Ordinal.{0}) (n : ℕ) : Om (ω : Ordinal.{0}) < S.psi a (S.I n) := by
  rw [← Om_psiI a n]
  refine Om_lt_Om.2 ?_
  exact lt_trans (omega0_lt_Om one_ne_zero) (Om_one_lt_psiI a n)

/-! ## Facts on normal forms -/

theorem NF_phi_lt {a b : Term} (h : Term.NF (.phi a b)) :
    Term.val S a < Term.val S (.phi a b) ∧ Term.val S b < Term.val S (.phi a b) :=
  ⟨(Term.cmp_lt_iff S h.1 h).1 h.2.2.1, (Term.cmp_lt_iff S h.2.1 h).1 h.2.2.2⟩

theorem NF_add_head_le {a b : Term} (h : Term.NF (.add a b)) :
    Term.val S (Term.head b) ≤ Term.val S a := by
  have e := Term.cmp_eq_compare S h.2.1.head h.1
  have hh := h.2.2.2.2
  rw [e] at hh
  exact not_lt.1 fun h' => hh (compare_gt_iff_gt.2 h')

theorem val_le_add_left (a b : Term) : Term.val S a ≤ Term.val S (.add a b) := le_self_add

theorem val_le_add_right (a b : Term) : Term.val S b ≤ Term.val S (.add a b) := le_add_self

theorem val_head_le (t : Term) : Term.val S (Term.head t) ≤ Term.val S t := by
  cases t <;> simp only [Term.head] <;> first | exact le_rfl | exact le_self_add

/-- The head of a nonzero normal form is principal. -/
theorem head_isPrin {t : Term} (h : Term.NF t) (h0 : t ≠ .zero) : (Term.head t).isPrin = true := by
  cases t with
  | zero => exact absurd rfl h0
  | add a b => exact h.2.2.1
  | _ => rfl

theorem Cw_head {t : Term} (h : Cw S t) : Cw S (Term.head t) := by
  cases t <;> simp only [Term.head] <;> first | exact h | exact h.1

theorem KLt_head {μ t α : Term} (h : Term.KLt μ t α) : Term.KLt μ (Term.head t) α := by
  cases t <;> simp only [Term.head] <;> first | exact h | exact h.1

theorem size_head_lt_of_add {a b : Term} : (Term.head (.add a b)).size < (Term.add a b).size := by
  simp [Term.head, Term.size]

/-- A normal form is below a principal `P` as soon as its head is. -/
theorem val_lt_of_head {t : Term} (h : Term.NF t) {P : Ordinal.{0}} (hP : IsPrincipal (· + ·) P)
    (hh : Term.val S (Term.head t) < P) : Term.val S t < P :=
  Term.val_lt_of_head_lt (Term.exact_all t.size) le_rfl h (Term.sem_of_NF h) hP hh

/-! ## Lemma PARTS (b) -/

/-- **Lemma PARTS (b).**  For a normal `μ = ψ_{Ω_{k+1}}(a)` and a level-`k` principal term `r` of the
class with `K_μ(r) < a`: `r < μ`. -/
theorem parts_b {s a : Term} (hμ : Term.NF (.psiS s a)) {k : ℕ} (hk : Term.val S s = k) :
    ∀ (n : ℕ) (r : Term), r.size ≤ n → Term.NF r → Cw S r → r.isPrin = true →
      lvl (Term.val S r) = k → Term.KLt (.psiS s a) r a → Term.val S r < Term.val S (.psiS s a) := by
  intro n
  induction n with
  | zero => intro r h; exact absurd (Term.size_pos r) (by omega)
  | succ n ih =>
    intro r hs hr hcw hp hl hK
    cases r with
    | zero => simp [Term.isPrin, Term.isSC] at hp
    | add _ _ => simp [Term.isPrin, Term.isSC] at hp
    | inacc _ => exact absurd hcw (by simp [Cw])
    | inaccW => exact absurd hcw (by simp [Cw])
    | psiI _ _ => exact absurd hcw (by simp [Cw])
    | om b =>
      obtain ⟨k', hk0, hk'⟩ := hcw
      rw [val_om_of_Cw hk', lvl_Om hk0] at hl
      subst hl
      rw [val_om_of_Cw hk']
      exact (psiS_bounds_nat s a hk).1
    | psiS s' c =>
      rcases hK with hK | ⟨hca, _, _⟩
      · exact (Term.cmp_lt_iff S hr hμ).1 hK
      · obtain ⟨⟨k', hk'⟩, _, _⟩ := hcw
        rw [lvl_psiS s' c hk'] at hl
        subst hl
        have hc : Term.val S c < Term.val S a := (Term.cmp_lt_iff S hr.2.1 hμ.2.1).1 hca
        have hsem := (Term.sem_of_NF (S := S) hr).2.2
        simp only [Term.val] at hsem ⊢
        rw [hk', ← hk] at hsem ⊢
        exact psi_lt_psi (InR_Om_succ _) hc hsem
    | phi x y =>
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
      have hcz : Cw S z := by rcases hzxy with rfl | rfl; exacts [hcw.1, hcw.2]
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
          exact lt_of_le_of_lt ((val_head_le z).trans hzlt.le)
            (lvl_lt (Cw_val_lt hcw hr))
        rcases Nat.eq_zero_or_pos k with rfl | hpos
        · have := lvl_le_of_lt hup; omega
        · refine lvl_eq ?_ hup hpos.ne'
          rw [← Om_nat_eq_OmT hpos.ne']
          exact ((psiS_bounds_nat s a hk).1.le).trans hhead
      have := ih (Term.head z) (by have := Term.size_head_le z; omega) hnz.head (Cw_head hcz)
        (head_isPrin hnz hz0) hlv (KLt_head hKz)
      exact absurd hhead (not_le.2 this)

/-! ## Lemma ARG0 -/

theorem psi_Om_omega_lt_Om1 : S.psi (Om (ω : Ordinal.{0})) (Om 1) < Om (1 : Ordinal.{0}) :=
  psi_lt (InR_Om_succ 0 |> fun h => by simpa using h) _

theorem Om1_le_val_om {b : Term} (hb : Term.NF b) (hb0 : b ≠ .zero) :
    Om (1 : Ordinal.{0}) ≤ Term.val S (.om b) := by
  simp only [Term.val]
  exact Om_le_Om.2 (Order.one_le_iff_ne_zero.2 (Term.val_ne_zero S hb hb0))

/-- **Lemma ARG0**, with the inner statement for a countable root `μ₀ = ψ_{Ω₁}(a)`. -/
theorem arg0 : ∀ (n : ℕ),
    (∀ t : Term, t.size ≤ n → Term.NF t → Term.val S t < S.psi (Om (ω : Ordinal.{0})) (Om 1) →
      Cw S t) ∧
    (∀ (s a u : Term), u.size ≤ n → Term.NF (.psiS s a) → Term.val S s = 0 →
      Term.val S a < Om (ω : Ordinal.{0}) → Term.NF u → Term.KLt (.psiS s a) u a →
      Term.val S u < Om (ω : Ordinal.{0}) → Cw S u) := by
  have hP1 : S.psi (Om (ω : Ordinal.{0})) (Om 1) < Om (1 : Ordinal.{0}) := psi_Om_omega_lt_Om1
  have hInR : S.InR (Om (1 : Ordinal.{0})) := by simpa using InR_Om_succ (S := S) 0
  intro n
  induction n with
  | zero => exact ⟨fun t h => absurd (Term.size_pos t) (by omega),
      fun _ _ u h => absurd (Term.size_pos u) (by omega)⟩
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    -- P1 at size `n + 1`
    have P1 : ∀ t : Term, t.size ≤ n + 1 → Term.NF t →
        Term.val S t < S.psi (Om (ω : Ordinal.{0})) (Om 1) → Cw S t := by
      intro t hs ht hv
      cases t with
      | zero => trivial
      | add a b =>
        refine ⟨ih1 a (by simp [Term.size] at hs; omega) ht.1
          (lt_of_le_of_lt (val_le_add_left a b) hv), ih1 b (by simp [Term.size] at hs; omega) ht.2.1
          (lt_of_le_of_lt (val_le_add_right a b) hv)⟩
      | phi a b =>
        obtain ⟨h1, h2⟩ := NF_phi_lt (S := S) ht
        exact ⟨ih1 a (by simp [Term.size] at hs; omega) ht.1 (h1.trans hv),
          ih1 b (by simp [Term.size] at hs; omega) ht.2.1 (h2.trans hv)⟩
      | om b =>
        exact absurd (lt_of_le_of_lt (Om1_le_val_om ht.1 ht.2.1) (hv.trans hP1)) (lt_irrefl _)
      | inacc m =>
        simp only [Term.val] at hv
        exact absurd (hv.trans hP1) (not_lt.2 (Low.Om_one_le_I (S := S) m))
      | inaccW =>
        simp only [Term.val] at hv
        exact absurd (hv.trans hP1) (not_lt.2 ((Low.Om_one_le_I (S := S) 0).trans (S.I_le_Iw 0)))
      | psiI m b =>
        simp only [Term.val] at hv
        exact absurd (hv.trans hP1) (not_lt.2 (Om_one_lt_psiI _ _).le)
      | psiS s a =>
        have hs0 : Term.val S s = 0 := by
          by_contra hne
          have h1 := (Term.val_psiS_bounds S s a).1
          have h2 : Om (1 : Ordinal.{0}) ≤ Om (Term.val S s) :=
            Om_le_Om.2 (Order.one_le_iff_ne_zero.2 hne)
          exact absurd (lt_of_le_of_lt h2 (h1.trans (hv.trans hP1))) (lt_irrefl _)
        have ha : Term.val S a < Om (ω : Ordinal.{0}) := by
          by_contra hge
          rw [not_lt] at hge
          have := (psi_mono hInR hge).1
          simp only [Term.val] at hv
          rw [hs0, zero_add] at hv
          exact absurd hv (not_lt.2 this)
        exact ⟨⟨0, by rw [hs0]; rfl⟩, ha, ih2 s a a (by simp [Term.size] at hs; omega) ht hs0 ha ht.2.1
          ht.2.2 ha⟩
    refine ⟨P1, ?_⟩
    -- P2 at size `n + 1`
    intro s a u hs hμ hs0 ha hu hK hv
    cases u with
    | zero => trivial
    | add x y =>
      exact ⟨ih2 s a x (by simp [Term.size] at hs; omega) hμ hs0 ha hu.1 hK.1
          (lt_of_le_of_lt (val_le_add_left x y) hv),
        ih2 s a y (by simp [Term.size] at hs; omega) hμ hs0 ha hu.2.1 hK.2
          (lt_of_le_of_lt (val_le_add_right x y) hv)⟩
    | phi x y =>
      obtain ⟨h1, h2⟩ := NF_phi_lt (S := S) hu
      exact ⟨ih2 s a x (by simp [Term.size] at hs; omega) hμ hs0 ha hu.1 hK.1 (h1.trans hv),
        ih2 s a y (by simp [Term.size] at hs; omega) hμ hs0 ha hu.2.1 hK.2 (h2.trans hv)⟩
    | om b =>
      simp only [Term.val] at hv
      have hb : Term.val S b < ω := Om_lt_Om.1 hv
      obtain ⟨k, hk⟩ := lt_omega0.1 hb
      refine ⟨k, ?_, hk⟩
      rintro rfl
      exact Term.val_ne_zero S hu.1 hu.2.1 (by rw [hk]; rfl)
    | inacc m =>
      simp only [Term.val] at hv; exact absurd hv (not_lt.2 (Om_omega_lt_I m).le)
    | inaccW =>
      simp only [Term.val] at hv
      exact absurd hv (not_lt.2 ((Om_omega_lt_I 0).trans_le (S.I_le_Iw 0)).le)
    | psiI m b =>
      simp only [Term.val] at hv; exact absurd hv (not_lt.2 (Om_omega_lt_psiI _ _).le)
    | psiS s' c =>
      rcases hK with hK | ⟨hca, _, hKc⟩
      · -- a stop below the root: a smaller root
        have hlt := (Term.cmp_lt_iff S hu hμ).1 hK
        have hroot : Term.val S (.psiS s a) ≤ S.psi (Om (ω : Ordinal.{0})) (Om 1) := by
          simp only [Term.val]; rw [hs0, zero_add]; exact (psi_mono hInR ha.le).1
        exact P1 _ hs hu (lt_of_lt_of_le hlt hroot)
      · have hc : Term.val S c < Term.val S a := (Term.cmp_lt_iff S hu.2.1 hμ.2.1).1 hca
        have hs' : ∃ k : ℕ, Term.val S s' = k := by
          have h1 := (Term.val_psiS_bounds S s' c).1
          have : Term.val S s' < ω := Om_lt_Om.1 (h1.trans hv)
          exact lt_omega0.1 this
        exact ⟨hs', hc.trans ha, ih2 s a c (by simp [Term.size] at hs; omega) hμ hs0 ha hu.2.1 hKc
          (hc.trans ha)⟩

/-- **Lemma ARG0**: normal forms below `ψ_{Ω₁}(Ω_ω)` are in the class. -/
theorem cw_of_lt {t : Term} (ht : Term.NF t)
    (hv : Term.val S t < S.psi (Om (ω : Ordinal.{0})) (Om 1)) : Cw S t :=
  (arg0 t.size).1 t le_rfl ht hv

end Googology.Trans.PoR.InaccPsi.R2.Br

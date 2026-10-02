import Googology.Notation.InaccPsi
import Googology.Trans.PoR.InaccPsi.LowSeg
import Googology.Trans.PoR.InaccPsi.LowTerms

/-!
# Conjecture T, upper half: the InaccPsi side of the assembly

The InaccPsi side of the upper half of Conjecture T (README, §4).  Write `θ = ψ_{Ω_2}(Ω_ω)` and `A_η = Ω_ω + θ · η`.

* `HA_A` : the hypothesis (HA) `A ∈ Cl(A + 1, ψ_{Ω_1}(A))` of the step theorem (Theorem STEP, README §4)
  holds for `A = A_η`, `η = ω · m + n` (`m n : ℕ`).
* `upper_bound` : let `u` be any ordinal function (Wilken's `υ`) with
  `u 1 ≤ ψ_{Ω_1}(Ω_ω)`, the step `u ξ ≤ ψ_{Ω_1}(A) → u (ξ + 1) ≤ ψ_{Ω_1}(A + θ)` for every `A`
  with `Ω_ω ≤ A` and (HA), and `u λ ≤ B` at limits when `u ι ≤ B` for `1 ≤ ι < λ`.
  Then `u (1 + η) ≤ ψ_{Ω_1}(A_η)` for `η < ω²`, and `u (ω²) ≤ ψ_{Ω_1}(A_{ω²})`.
* `conjU` : under the same hypotheses every ordinal below `u (ω²)` is the value of an
  InaccPsi normal form (Lemma IS of LowSeg.lean).

Wilken's `υ` and the step theorem are not formalized: the step is a hypothesis here, proved
on paper (Theorem STEP, README §4).  This file checks only the InaccPsi side and the induction.
The hypothesis `hstep` is stated for every `ξ`, also `ξ = 0`, where Theorem STEP does not
apply; that case is trivial on paper, but it is not checked here for Wilken's `υ`.
-/

namespace Googology.Notation.InaccPsi.ConjT

open Ordinal Order Set Googology.Notation.InaccPsi Term InaccSeq

universe u

variable (S : InaccSeq.{u})

/-- `θ = ψ_{Ω_2}(Ω_ω)`. -/
noncomputable def th : Ordinal.{u} := S.psi (Om ω) (Om (1 + 1))

/-- `A_η = Ω_ω + θ · η`. -/
noncomputable def Aη (η : Ordinal.{u}) : Ordinal.{u} := Om ω + th S * η

/-- The hypothesis (HA) of the step theorem. -/
def HA (A : Ordinal.{u}) : Prop := A ∈ S.CSet (A + 1) (S.psi A (Om 1))

theorem omega_mem (a b : Ordinal.{u}) : ω ∈ S.CSet a b := by
  have h := CSet.phi_mem (CSet.zero_mem (S := S) a b) (CSet.one_mem a b)
  rwa [veblen_zero_apply, opow_one] at h

theorem OmW_mem (a b : Ordinal.{u}) : Om ω ∈ S.CSet a b := CSet.Om_mem (omega_mem S a b)

theorem th_mem {a b : Ordinal.{u}} (h : Om ω < a) : th S ∈ S.CSet a b :=
  CSet.psi_mem h (InR_Om_succ 1) (CSet.Om_mem (CSet.add_mem (CSet.one_mem a b)
    (CSet.one_mem a b))) (OmW_mem S a b)

theorem SC_th : SC (th S) := SC_psi (InR_Om_succ 1) _

theorem mul_nat_mem {a b x : Ordinal.{u}} (hx : x ∈ S.CSet a b) :
    ∀ n : ℕ, x * n ∈ S.CSet a b
  | 0 => by simpa using CSet.zero_mem (S := S) a b
  | n + 1 => by
    rw [Nat.cast_succ, mul_add_one]
    exact CSet.add_mem (mul_nat_mem hx n) hx

theorem th_omega_mem {a b : Ordinal.{u}} (h : Om ω < a) : th S * ω ∈ S.CSet a b := by
  have e : th S * ω = veblen 0 (th S + 1) := by
    rw [veblen_zero_apply, opow_add, opow_one, Low.opow_eq_self_of_SC (SC_th S)]
  rw [e]
  exact CSet.phi_mem (CSet.zero_mem a b) (CSet.succ_mem (th_mem S h))

theorem th_mul_mem {a b : Ordinal.{u}} (h : Om ω < a) (m n : ℕ) :
    th S * (ω * m + n) ∈ S.CSet a b := by
  rw [mul_add, ← mul_assoc]
  exact CSet.add_mem (mul_nat_mem S (th_omega_mem S h) m) (mul_nat_mem S (th_mem S h) n)

/-- **(HA)** for `A = Ω_ω + θ · (ω · m + n)`. -/
theorem HA_A (m n : ℕ) : HA S (Aη S (ω * m + n)) := by
  have hlt : Om ω < Aη S (ω * m + n) + 1 :=
    lt_of_le_of_lt (Ordinal.le_add_right _ _) (lt_add_one _)
  exact CSet.add_mem (OmW_mem S _ _) (th_mul_mem S hlt m n)

theorem OmW_le_A (η : Ordinal.{u}) : Om ω ≤ Aη S η := Ordinal.le_add_right _ _

theorem A_mono {η η' : Ordinal.{u}} (h : η ≤ η') : Aη S η ≤ Aη S η' := by
  unfold Aη; gcongr

theorem A_succ (η : Ordinal.{u}) : Aη S η + th S = Aη S (η + 1) := by
  rw [Aη, Aη, add_assoc, mul_add_one]

/-- Every `η < ω · ω` is `ω · m + n`. -/
theorem decomp {η : Ordinal.{u}} (h : η < ω * ω) : ∃ m n : ℕ, η = ω * m + n := by
  have hw : (ω : Ordinal.{u}) ≠ 0 := omega0_ne_zero
  obtain ⟨m, hm⟩ := lt_omega0.1 ((div_lt hw).2 h)
  obtain ⟨n, hn⟩ := lt_omega0.1 (mod_lt η hw)
  refine ⟨m, n, ?_⟩
  rw [← hm, ← hn, div_add_mod]

theorem nat_lt_of_mul_le {m : ℕ} {k η : Ordinal.{u}} (h1 : ω * m ≤ η) (h2 : η < ω * k) :
    (m : Ordinal.{u}) < k :=
  (mul_lt_mul_iff_right₀ omega0_pos).1 (lt_of_le_of_lt h1 h2)

/-- The induction of Theorem T-UP, with Wilken's step theorem as the hypothesis `hstep`. -/
theorem upper_bound (u : Ordinal.{u} → Ordinal.{u})
    (h1 : u 1 ≤ S.psi (Om ω) (Om 1))
    (hstep : ∀ ξ A, Om ω ≤ A → HA S A → u ξ ≤ S.psi A (Om 1) →
      u (ξ + 1) ≤ S.psi (A + th S) (Om 1))
    (hlim : ∀ l B, IsSuccLimit l → (∀ ι, 1 ≤ ι → ι < l → u ι ≤ B) → u l ≤ B) :
    ∀ m n : ℕ, u (1 + (ω * m + n)) ≤ S.psi (Aη S (ω * m + n)) (Om 1) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
    intro n
    induction n with
    | zero =>
      simp only [Nat.cast_zero, add_zero]
      rcases m with _ | k
      · simpa [Aη] using h1
      · have hpos : (0 : Ordinal.{u}) < ((k + 1 : ℕ) : Ordinal.{u}) := by exact_mod_cast Nat.succ_pos k
        have hω : ω ≤ ω * ((k + 1 : ℕ) : Ordinal.{u}) := le_mul_left _ hpos
        rw [one_add_of_omega0_le hω]
        apply hlim _ _ (isSuccLimit_mul_left isSuccLimit_omega0 hpos)
        intro ι hι1 hιl
        have hsub : 1 + (ι - 1) = ι := Ordinal.add_sub_cancel_of_le hι1
        have hlt : ι - 1 < ω * ((k + 1 : ℕ) : Ordinal.{u}) :=
          lt_of_le_of_lt (Ordinal.le_add_left _ _ |>.trans_eq hsub) hιl
        have hww : ι - 1 < ω * ω :=
          lt_of_lt_of_le hlt (mul_le_mul_left' (natCast_lt_omega0 _).le _)
        obtain ⟨m', n', he⟩ := decomp hww
        have hm' : (m' : Ordinal.{u}) < ((k + 1 : ℕ) : Ordinal.{u}) :=
          nat_lt_of_mul_le (he ▸ Ordinal.le_add_right _ _) hlt
        have hm'' : m' < k + 1 := by exact_mod_cast hm'
        calc u ι = u (1 + (ω * m' + n')) := by rw [← he, hsub]
          _ ≤ S.psi (Aη S (ω * m' + n')) (Om 1) := ihm m' hm'' n'
          _ ≤ S.psi (Aη S (ω * ((k + 1 : ℕ) : Ordinal.{u}))) (Om 1) :=
            (psi_mono Low.InR_Om_one (A_mono S (he ▸ hlt.le))).1
    | succ n ihn =>
      have e1 : (1 : Ordinal.{u}) + (ω * m + ((n + 1 : ℕ) : Ordinal.{u})) =
          1 + (ω * m + n) + 1 := by
        push_cast; simp only [add_assoc]
      have e2 : Aη S (ω * m + ((n + 1 : ℕ) : Ordinal.{u})) = Aη S (ω * m + n) + th S := by
        rw [A_succ]; push_cast; rw [add_assoc]
      rw [e1, e2]
      exact hstep _ _ (OmW_le_A S _) (HA_A S m n) ihn

/-- The limit `η = ω²` (so `ι = 1 + ω² = ω²`). -/
theorem upper_bound_ww (u : Ordinal.{u} → Ordinal.{u})
    (h1 : u 1 ≤ S.psi (Om ω) (Om 1))
    (hstep : ∀ ξ A, Om ω ≤ A → HA S A → u ξ ≤ S.psi A (Om 1) →
      u (ξ + 1) ≤ S.psi (A + th S) (Om 1))
    (hlim : ∀ l B, IsSuccLimit l → (∀ ι, 1 ≤ ι → ι < l → u ι ≤ B) → u l ≤ B) :
    u (ω * ω) ≤ S.psi (Aη S (ω * ω)) (Om 1) := by
  apply hlim _ _ (isSuccLimit_mul_left isSuccLimit_omega0 omega0_pos)
  intro ι hι1 hιl
  have hsub : 1 + (ι - 1) = ι := Ordinal.add_sub_cancel_of_le hι1
  have hlt : ι - 1 < ω * ω := lt_of_le_of_lt (Ordinal.le_add_left _ _ |>.trans_eq hsub) hιl
  obtain ⟨m, n, he⟩ := decomp hlt
  calc u ι = u (1 + (ω * m + n)) := by rw [← he, hsub]
    _ ≤ S.psi (Aη S (ω * m + n)) (Om 1) := upper_bound S u h1 hstep hlim m n
    _ ≤ S.psi (Aη S (ω * ω)) (Om 1) := (psi_mono Low.InR_Om_one (A_mono S (he ▸ hlt.le))).1

/-- **Conjecture U** (given the step theorem): every ordinal below `υ_{ω²}` is the value of an
InaccPsi normal form. -/
theorem conjU (u : Ordinal.{u} → Ordinal.{u})
    (h1 : u 1 ≤ S.psi (Om ω) (Om 1))
    (hstep : ∀ ξ A, Om ω ≤ A → HA S A → u ξ ≤ S.psi A (Om 1) →
      u (ξ + 1) ≤ S.psi (A + th S) (Om 1))
    (hlim : ∀ l B, IsSuccLimit l → (∀ ι, 1 ≤ ι → ι < l → u ι ≤ B) → u l ≤ B)
    (z : Ordinal.{u}) (hz : z < u (ω * ω)) : z ∈ Vals S :=
  Low.lt_psi_one_mem_Vals _ z (lt_of_lt_of_le hz (upper_bound_ww S u h1 hstep hlim))

/-! ## Ordinal arithmetic used in Lemma M (Case III) of the proof of Theorem STEP -/

/-- If `a < c + P` with `P` additively principal and `1 < P`, then `a + 1 + q < c + P` for `q < P`. -/
theorem arith_absorb {a c P q : Ordinal.{u}} (hP : IsPrincipal (· + ·) P) (h1 : 1 < P)
    (ha : a < c + P) (hq : q < P) : a + 1 + q < c + P := by
  rcases lt_or_ge a c with hac | hca
  · calc a + 1 + q ≤ c + q := by
          gcongr; exact Order.add_one_le_iff.2 hac
      _ < c + P := by gcongr
  · obtain ⟨r, rfl⟩ := exists_add_of_le hca
    have hr : r < P := (add_lt_add_iff_left c).1 ha
    rw [add_assoc, add_assoc]
    exact (add_lt_add_iff_left c).2 (hP hr (hP h1 hq))

/-- `c < c'` and `e < e'` give `c + ω ^ e < c' + ω ^ e'`. -/
theorem arith_lex {c c' e e' : Ordinal.{u}} (hc : c < c') (he : e < e') :
    c + ω ^ e < c' + ω ^ e' := by
  have hpe : ω ^ e < ω ^ e' := (opow_lt_opow_iff_right one_lt_omega0).2 he
  rcases lt_or_ge c' (c + ω ^ e) with h | h
  · obtain ⟨r, rfl⟩ := exists_add_of_le hc.le
    have hr : r < ω ^ e := (add_lt_add_iff_left c).1 h
    have hP : IsPrincipal (· + ·) (ω ^ e') := isPrincipal_add_omega0_opow e'
    have : r + ω ^ e' = ω ^ e' := hP.add_eq_right (hr.trans hpe)
    rw [add_assoc, this]
    exact (add_lt_add_iff_left c).2 hpe
  · exact lt_of_le_of_lt h (lt_add_of_pos_right _ (opow_pos _ omega0_pos))

end Googology.Notation.InaccPsi.ConjT

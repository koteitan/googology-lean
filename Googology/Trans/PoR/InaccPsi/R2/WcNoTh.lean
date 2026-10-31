import Googology.Trans.PoR.InaccPsi.R2.VxRead
import Googology.Trans.PoR.InaccPsi.R2.LdEQ
import Googology.Trans.PoR.InaccPsi.R2.SfNF
import Googology.Trans.PoR.InaccPsi.R2.SfPv
import Googology.Trans.PoR.InaccPsi.R2.BcName

/-!
# NO-GO: the readings of `θ` at the levels `k ≥ 1` (`Vn.vnTheta_th`, `Vx.vxTheta_of_it`) are false

`ρ = υ_λ`, `A` with `A ∈ Cl(A, ψ_{Ω₁}(A))` and `ψ_{Ω₁}(A) = ρ` (then `A = A_{η_λ}`), `Θ = gxTh ρ (ldAtR λ)`,
`θ = ψ_{Ω₂}(Ω_ω)`, `Y_{s+2} = Uj.ujY S s = ψ_{Ω_{s+2}}(Ω_{s+2})`.

`Ld.ldTheta_le_psi` gives `Θ(θ) ≤ ψ_{Ω₁}(A + θ) = υ_{λ+1}`.  Every atom `s ≤ θ` is read below it, while
`ψ_{Ω₁}(A + 1 + Y)` with `Y > θ` is above it.  Hence:

* `wcOwn_inj` (`ψ_{Ω₁}` is injective on own arguments), `wcOwnL` (`A_{η_λ}` is own below `L(ω)`);
* `wcTh_le` (**`Θ(θ) ≤ ψ_{Ω₁}(A + θ)`**), `wcNoRead` (**`Θ(s) < ψ_{Ω₁}(A + 1 + Y)` for every `s ≤ θ`, `Y > θ`**);
* `wcNoTh` (**`Θ(θ) ≠ ψ_{Ω₁}(A + 1 + Ω_ω)`**: the conclusion of `Vn.vnTheta_th` and `Vx.vxTheta_of_it` is false);
* `wcNoY1` (**the corrected top of `Vn.vnTheta_th` at `k = 1`, `Θ(ψ₂(Y₄)) = ψ₁(A + 1 + Y₃)`, is false**), `wcNoY`
  (its hypothesis `hY` is refutable), `wcNoIt1` (**the iterate reading of `Vx.vxTheta_of_it` at `k = 1`, `n = 0`,
  `Θ(ψ₂(ψ_{Ω₄}(0))) = ψ₁(A + 1 + ψ_{Ω₃}(0))`, is false**), `wcNoIt` (its hypothesis `hIt` is refutable);
* `wcNoTh_sat` (non-vacuity: the hypotheses hold at every restart below `L(ω)` with `A = A_{η_λ}`).

So `Vn.vnTheta_th` and `Vx.vxTheta_of_it` are VACUOUS at every own `A` with `ψ_{Ω₁}(A) = υ_λ < L(ω)`.  No new
definition, no new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Mx

variable {S : InaccSeq.{0}}

/-- **`ψ_{Ω₁}` is injective on own arguments.** -/
theorem wcOwn_inj {A A' : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1)))
    (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1))) (e : S.psi A (Om 1) = S.psi A' (Om 1)) : A = A' := by
  rcases lt_trichotomy A A' with h | h | h
  · exact absurd e (psi_lt_psi Low.InR_Om_one h hA).ne
  · exact h
  · exact absurd e.symm (psi_lt_psi Low.InR_Om_one h hA').ne

section NoTh

variable {l : Ordinal.{0}} (hl : IsRestartIdx l) (hω : upsilon l < Nc.ncL S ω)
include hl hω

theorem wcLX : upsilon l < Nm.Pv S (Om ω + Nc.ncPp S * ω) := by
  rw [← Lw.lw_L_eq]; exact hω

/-- **`A_{η_λ}` is own** below `L(ω)`. -/
theorem wcOwnL : ConjT.Aη S (cdEta S l) ∈
    S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)) := by
  obtain ⟨hg, -, -, hpv⟩ := cdEta_pv_spec (S := S) hl.1 (wcLX hl hω)
  obtain ⟨n, hn⟩ := Bc.bcC_cof (S := S) _ hω
  have h1 : Nm.Pv S (cdEta S l) < Bc.bcC S (n + 1) := by
    rw [hpv]; exact hn.trans_le (Bc.bcC_mono (S := S) (Nat.le_succ n))
  exact Sf.sfOwn hg (Sf.sfA_lt h1).2

/-- **`Θ(θ) ≤ ψ_{Ω₁}(A_{η_λ} + θ)`.** -/
theorem wcTh_le : gxTh (upsilon l) (Ld.ldAtR S l) (ConjT.th S) ≤
    S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S) (Om 1) := by
  have hX := wcLX hl hω
  rw [← Ld.ldTheta (m := ConjT.th S) hl hX (psi_lt (InR_Om_succ 1) _).le]
  exact Ld.ldTheta_le_psi hl hX (wcOwnL hl hω) _

/-- **Every atom `s ≤ θ` is read below `ψ_{Ω₁}(A + 1 + Y)` for every `Y > θ`.** -/
theorem wcNoRead {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    {s Y : Ordinal.{0}} (hs : s ≤ ConjT.th S) (hY : ConjT.th S < Y) :
    gxTh (upsilon l) (Ld.ldAtR S l) s < S.psi (A + 1 + Y) (Om 1) := by
  have hpv : S.psi (ConjT.Aη S (cdEta S l)) (Om 1) = upsilon l := cdEta_pv (S := S) hl.1 (wcLX hl hω)
  have eA : A = ConjT.Aη S (cdEta S l) := wcOwn_inj hA (wcOwnL hl hω) (hρ.trans hpv.symm)
  have h1 := (gxTh_mono (Z := upsilon l) (At := Ld.ldAtR S l) hs).trans (wcTh_le hl hω)
  rw [← eA] at h1
  have hθω : (ω : Ordinal.{0}) ≤ ConjT.th S := by
    have hΩ := (psiS_bounds (S := S) (Om ω) 1).1
    exact (omega0_lt_Om (v := (1 : Ordinal.{0})) one_ne_zero).le.trans hΩ.le
  have hlt : A + ConjT.th S < A + 1 + Y := by
    rw [add_assoc, Ordinal.one_add_of_omega0_le (hθω.trans hY.le)]
    exact (add_lt_add_iff_left A).2 hY
  have hWA : Om ω < A + ConjT.th S := by
    rw [eA]; exact (ConjT.OmW_le_A S _).trans_lt (lt_add_of_pos_right _ (Sf.sfTh_pos S))
  have hnf : A + ConjT.th S ∈ S.CSet (A + ConjT.th S) (S.psi (A + ConjT.th S) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA) (ConjT.th_mem S hWA)
  exact h1.trans_lt (psi_lt_psi Low.InR_Om_one hlt hnf)

/-- **`Θ(θ) ≠ ψ_{Ω₁}(A + 1 + Ω_ω)`**: the conclusion of `Vn.vnTheta_th` and `Vx.vxTheta_of_it` is false. -/
theorem wcNoTh {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    gxTh (upsilon l) (Ld.ldAtR S l) (ConjT.th S) ≠ S.psi (A + 1 + Om ω) (Om 1) :=
  (wcNoRead hl hω hA hρ le_rfl ((psi_lt (InR_Om_succ 1) _).trans
    (Om_lt_Om.2 (by rw [one_add_one_eq_two]; exact_mod_cast natCast_lt_omega0 2)))).ne

omit hl hω in
theorem wc_th_lt_Y1 : ConjT.th S < Uj.ujY S 1 := by
  have h := (psiS_bounds (S := S) (Om (1 + 1 + 1)) (1 + 1)).1
  exact (psi_lt (InR_Om_succ 1) _).trans h

/-- **The corrected top of `Vn.vnTheta_th` at `k = 1` is false**: `Θ(ψ₂(Y₄)) ≠ ψ₁(A + 1 + Y₃)`. -/
theorem wcNoY1 {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    gxTh (upsilon l) (Ld.ldAtR S l) (S.psi (Uj.ujY S (((1 : ℕ) : Ordinal.{0}) + 1)) (Om (1 + 1))) ≠
      S.psi (A + 1 + Uj.ujY S ((1 : ℕ) : Ordinal.{0})) (Om 1) := by
  rw [Nat.cast_one]
  refine (wcNoRead hl hω hA hρ ?_ wc_th_lt_Y1).ne
  refine (psi_mono (S := S) (InR_Om_succ 1) ?_).1
  refine ((psi_lt (InR_Om_succ _) _).trans (Om_lt_Om.2 ?_)).le
  show (1 + 1 + 1 + 1 : Ordinal.{0}) < ω
  exact_mod_cast natCast_lt_omega0 4

/-- **The hypothesis `hY` of `Vn.vnTheta_th` is refutable.** -/
theorem wcNoY {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    ¬ ∀ k : ℕ, gxTh (upsilon l) (Ld.ldAtR S l) (S.psi (Uj.ujY S ((k : Ordinal.{0}) + 1)) (Om (1 + 1))) =
      S.psi (A + 1 + Uj.ujY S (k : Ordinal.{0})) (Om 1) :=
  fun hY => wcNoY1 hl hω hA hρ (hY 1)

/-- **The iterate reading of `Vx.vxTheta_of_it` at `k = 1`, `n = 0` is false**:
`Θ(ψ₂(ψ_{Ω₄}(0))) ≠ ψ₁(A + 1 + ψ_{Ω₃}(0))`. -/
theorem wcNoIt1 {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    gxTh (upsilon l) (Ld.ldAtR S l)
        (S.psi ((fun x => S.psi x (Om (((1 : ℕ) : Ordinal.{0}) + 1 + 1 + 1)))^[0 + 1] 0) (Om (1 + 1))) ≠
      S.psi (A + 1 + (fun x => S.psi x (Om (((1 : ℕ) : Ordinal.{0}) + 1 + 1)))^[0 + 1] 0) (Om 1) := by
  simp only [zero_add, Function.iterate_one, Nat.cast_one]
  have hY : ConjT.th S < S.psi 0 (Om (1 + 1 + 1)) :=
    (psi_lt (InR_Om_succ 1) _).trans (psiS_bounds (S := S) 0 (1 + 1)).1
  refine (wcNoRead hl hω hA hρ ?_ hY).ne
  refine (psi_mono (S := S) (InR_Om_succ 1) ?_).1
  refine ((psi_lt (InR_Om_succ _) _).trans (Om_lt_Om.2 ?_)).le
  show (1 + 1 + 1 + 1 : Ordinal.{0}) < ω
  exact_mod_cast natCast_lt_omega0 4

/-- **The hypothesis `hIt` of `Vx.vxTheta_of_it` is refutable.** -/
theorem wcNoIt {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    ¬ ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, gxTh (upsilon l) (Ld.ldAtR S l)
        (S.psi ((fun x => S.psi x (Om ((k : Ordinal.{0}) + 1 + 1 + 1)))^[n + 1] 0) (Om (1 + 1))) =
      S.psi (A + 1 + (fun x => S.psi x (Om ((k : Ordinal.{0}) + 1 + 1)))^[n + 1] 0) (Om 1) :=
  fun hIt => wcNoIt1 hl hω hA hρ (hIt 1 le_rfl 0)

/-- **Non-vacuity of the no-go**: its hypotheses hold with `A = A_{η_λ}` at every restart below `L(ω)`. -/
theorem wcNoTh_sat : ConjT.Aη S (cdEta S l) ∈
      S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)) ∧
    S.psi (ConjT.Aη S (cdEta S l)) (Om 1) = upsilon l :=
  ⟨wcOwnL hl hω, cdEta_pv (S := S) hl.1 (wcLX hl hω)⟩

end NoTh

#print axioms wcOwn_inj
#print axioms wcTh_le
#print axioms wcNoRead
#print axioms wcNoTh
#print axioms wcNoY1
#print axioms wcNoY
#print axioms wcNoIt1
#print axioms wcNoIt
#print axioms wcNoTh_sat

end Googology.Trans.PoR.InaccPsi.R2.Wc

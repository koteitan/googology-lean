import Googology.Trans.PoR.InaccPsi.R2.VxRead
import Googology.Trans.PoR.InaccPsi.R2.RnEQ

/-!
# NO-GO: `Θ_λ(θ) ≠ ψ_{Ω₁}(A + 1 + Ω_ω)`; the readings at `Y_{k+3}` (and at the `ψ_{Ω_{k+3}}`-iterates) fail at some `k ≥ 1`

`Θ = gxTh ρ_λ (ldAtR λ)`, `θ = ψ_{Ω₂}(Ω_ω)` (`ConjT.th`), `A_η = Ω_ω + θ·η` (`ConjT.Aη`), `A = A_{η_λ}`,
`Y_{k+2} = ψ_{Ω_{k+2}}(Ω_{k+2})` (`Uj.ujY S k`), `y^{(k)}_n`, `z^{(k)}_n` the iterates of `ψ_{Ω_{k+3}}`, `ψ_{Ω_{k+2}}`
from `0`.  `OWN` = `A ∈ Cl(A, ψ_{Ω₁}(A))` (the hypothesis of `Rn.rnTheta_at`; it holds when `ρ_λ < c_{n+1}` for some
`n`, `Vq.vqA_spec`).

* `wbA_unique` (**the restart data determine `A`**: `A' ∈ Cl(A', ψ₁(A'))`, `ψ₁(A') = ρ_λ`, OWN ⇒ `A' = A`);
* `wbTheta_lt` (**`Θ_λ(θ) ≤ ψ_{Ω₁}(A + θ + 1) < ψ_{Ω₁}(A + 1 + Ω_ω)`**, from `Rn.rnTheta_at` at `c = 0`: the term
  `A + θ + 1` lies in the hull of `ψ_{Ω₁}(A + 1 + Ω_ω)` below its argument), `wbTheta_ne`;
* `wbNoY` (**`¬ ∀ k, Θ(ψ₂(Y_{k+3})) = ψ₁(A + 1 + Y_{k+2})`**: the hypothesis of `Vn.vnTheta_th` is refuted, so
  `Vn.vnTheta_th` is VACUOUS under OWN), `wbNoY_ge1` (**some `k ≥ 1` has `Θ(ψ₂(Y_{k+3})) ≠ ψ₁(A + 1 + Y_{k+2})`**;
  `k = 0` holds by `Vn.vnRead_Y3`);
* `wbNoIt` (**the hypothesis of `Vx.vxTheta_of_it` is refuted**: some `k ≥ 1`, `n` has
  `Θ(ψ₂(y^{(k)}_{n+1})) ≠ ψ₁(A + 1 + z^{(k)}_{n+1})`; so `Vx.vxTheta_of_it` is VACUOUS under OWN), `wbNoIt_A`
  (the same for every `A'` with the restart hypotheses).

So the target "`Θ_λ(θ) = ψ_{Ω₁}(A + 1 + Ω_ω)` by one induction on `k` over the iterate readings" is FALSE under OWN:
the readings with image `z^{(k)}_{n+1}` (constant in the base, with `Ω_{k+3} ↦ Ω_{k+2}` inside the image) cannot all
hold.

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Wb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Uj
  Googology.Trans.PoR.InaccPsi.R2.Vn Googology.Trans.PoR.InaccPsi.R2.Vx Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Le

variable {S : InaccSeq.{0}}

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hown : ConjT.Aη S (cdEta S l) ∈
    S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)))

include hl hX hown

/-- **The restart data determine `A`**: every own `A'` with `ψ_{Ω₁}(A') = ρ_λ` is `A_{η_λ}`. -/
theorem wbA_unique {A' : Ordinal.{0}} (hA : A' ∈ S.CSet A' (S.psi A' (Om 1))) (hρ : S.psi A' (Om 1) = upsilon l) :
    A' = ConjT.Aη S (cdEta S l) := by
  have hpv : S.psi (ConjT.Aη S (cdEta S l)) (Om 1) = upsilon l := cdEta_pv hl.1 hX
  rcases lt_trichotomy A' (ConjT.Aη S (cdEta S l)) with h | h | h
  · exfalso
    have hm : A' ∈ S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)) :=
      CSet_mono h.le (by rw [hρ, hpv]) hA
    have := psi_lt_psi_of_mem Low.InR_Om_one h hm
    rw [hρ, hpv] at this; exact lt_irrefl _ this
  · exact h
  · exfalso
    have hm : ConjT.Aη S (cdEta S l) ∈ S.CSet A' (S.psi A' (Om 1)) :=
      CSet_mono h.le (by rw [hρ, hpv]) hown
    have := psi_lt_psi_of_mem Low.InR_Om_one h hm
    rw [hρ, hpv] at this; exact lt_irrefl _ this

/-- **`Θ_λ(θ) ≤ ψ_{Ω₁}(A + θ + 1) < ψ_{Ω₁}(A + 1 + Ω_ω)`.** -/
theorem wbTheta_lt :
    gxTh (upsilon l) (ldAtR S l) (ConjT.th S) ≤ S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + 1) (Om 1) ∧
      S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + 1) (Om 1) <
        S.psi (ConjT.Aη S (cdEta S l) + 1 + Om ω) (Om 1) := by
  set A := ConjT.Aη S (cdEta S l) with hA_def
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hMW : (0 : Ordinal.{0}) < Rn.rnMW S := by
    unfold Rn.rnMW ldTop; exact (SC_psi (InR_Om_succ 1) _).1
  have h0 := Rn.rnTheta_at hl hX hown 0 (GxCl.zero hρSC.1) hMW
  rw [add_zero, gxTh_zero, add_zero] at h0
  refine ⟨h0, ?_⟩
  have hW : (1 : Ordinal.{0}) + Om ω = Om ω :=
    Ordinal.one_add_of_omega0_le ((omega0_le_of_isSuccLimit (SC_Om omega0_ne_zero).isSuccLimit))
  have hθ1 : ConjT.th S + 1 < Om ω := (SC_Om omega0_ne_zero).isSuccLimit.succ_lt (Sf.sfTh_lt_OmW S)
  have hlt : A + ConjT.th S + 1 < A + 1 + Om ω := by
    rw [add_assoc, add_assoc, hW]; exact (add_lt_add_iff_left A).2 hθ1
  have hWa : Om ω < A + 1 + Om ω := by
    rw [add_assoc, hW]
    calc Om ω < Om ω + Om ω := lt_add_of_pos_right _ (Om_pos omega0_ne_zero)
      _ ≤ A + Om ω := add_le_add_left (le_self_add : Om ω ≤ Om ω + ConjT.th S * cdEta S l) _
  refine psi_lt_psi_of_mem Low.InR_Om_one hlt ?_
  refine CSet.add_mem (CSet.add_mem ?_ (ConjT.th_mem S hWa)) (CSet.one_mem _ _)
  exact (psi_mono (S := S) Low.InR_Om_one (le_self_add.trans le_self_add)).2 hown

/-- **`Θ_λ(θ) ≠ ψ_{Ω₁}(A + 1 + Ω_ω)`.** -/
theorem wbTheta_ne :
    gxTh (upsilon l) (ldAtR S l) (ConjT.th S) ≠ S.psi (ConjT.Aη S (cdEta S l) + 1 + Om ω) (Om 1) := by
  obtain ⟨h1, h2⟩ := wbTheta_lt hl hX hown
  exact (h1.trans_lt h2).ne

/-- **NO-GO for `Vn.vnTheta_th`**: the readings `Θ(ψ₂(Y_{k+3})) = ψ₁(A + 1 + Y_{k+2})` do not hold for every `k`. -/
theorem wbNoY : ¬ ∀ k : ℕ, gxTh (upsilon l) (ldAtR S l) (S.psi (ujY S ((k : Ordinal.{0}) + 1)) (Om (1 + 1))) =
      S.psi (ConjT.Aη S (cdEta S l) + 1 + ujY S (k : Ordinal.{0})) (Om 1) := fun hY =>
  wbTheta_ne hl hX hown (vnTheta_th hY)

/-- **Some `k ≥ 1` has `Θ(ψ₂(Y_{k+3})) ≠ ψ₁(A + 1 + Y_{k+2})`** (`k = 0` holds: `Vn.vnRead_Y3`). -/
theorem wbNoY_ge1 : ∃ k : ℕ, 1 ≤ k ∧ gxTh (upsilon l) (ldAtR S l)
      (S.psi (ujY S ((k : Ordinal.{0}) + 1)) (Om (1 + 1))) ≠
      S.psi (ConjT.Aη S (cdEta S l) + 1 + ujY S (k : Ordinal.{0})) (Om 1) := by
  by_contra h
  push Not at h
  refine wbNoY hl hX hown fun k => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 := vnRead_Y3 hl hX hown (cdEta_pv hl.1 hX)
    rw [Nat.cast_zero, zero_add, ujY_one, ujY_zero]
    exact h0
  · exact h k hk

/-- **NO-GO for `Vx.vxTheta_of_it`**: some `k ≥ 1`, `n` has `Θ(ψ₂(y^{(k)}_{n+1})) ≠ ψ₁(A + 1 + z^{(k)}_{n+1})`. -/
theorem wbNoIt : ∃ k : ℕ, 1 ≤ k ∧ ∃ n : ℕ, gxTh (upsilon l) (ldAtR S l)
      (S.psi ((fun x => S.psi x (Om ((k : Ordinal.{0}) + 1 + 1 + 1)))^[n + 1] 0) (Om (1 + 1))) ≠
      S.psi (ConjT.Aη S (cdEta S l) + 1 + (fun x => S.psi x (Om ((k : Ordinal.{0}) + 1 + 1)))^[n + 1] 0) (Om 1) := by
  by_contra h
  push Not at h
  exact wbTheta_ne hl hX hown (vxTheta_of_it hl hX hown (cdEta_pv hl.1 hX) h)

/-- **The same for every `A'` with the restart hypotheses** (`A' = A` by `wbA_unique`): the hypothesis of
`Vx.vxTheta_of_it` fails. -/
theorem wbNoIt_A {A' : Ordinal.{0}} (hA : A' ∈ S.CSet A' (S.psi A' (Om 1))) (hρ : S.psi A' (Om 1) = upsilon l) :
    ¬ ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, gxTh (upsilon l) (ldAtR S l)
        (S.psi ((fun x => S.psi x (Om ((k : Ordinal.{0}) + 1 + 1 + 1)))^[n + 1] 0) (Om (1 + 1))) =
      S.psi (A' + 1 + (fun x => S.psi x (Om ((k : Ordinal.{0}) + 1 + 1)))^[n + 1] 0) (Om 1) := by
  intro h
  have e := wbA_unique hl hX hown hA hρ
  subst e
  obtain ⟨k, hk, n, hn⟩ := wbNoIt hl hX hown
  exact hn (h k hk n)

end Main

/-- **Under `ρ_λ < c_{n+1}`** (so OWN holds, `Vq.vqA_spec`): `Θ_λ(θ) ≠ ψ_{Ω₁}(A + 1 + Ω_ω)`. -/
theorem wbTheta_ne_c {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) {n : ℕ}
    (hn : upsilon l < Bc.bcC S (n + 1)) :
    gxTh (upsilon l) (ldAtR S l) (ConjT.th S) ≠ S.psi (ConjT.Aη S (cdEta S l) + 1 + Om ω) (Om 1) :=
  wbTheta_ne hl hX (Vq.vqA_spec hl hX hn).1

#print axioms wbA_unique
#print axioms wbTheta_lt
#print axioms wbTheta_ne
#print axioms wbNoY
#print axioms wbNoY_ge1
#print axioms wbNoIt
#print axioms wbNoIt_A
#print axioms wbTheta_ne_c

end Googology.Trans.PoR.InaccPsi.R2.Wb

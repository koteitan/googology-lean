import Googology.Trans.PoR.InaccPsi.R2.VxDyn

/-!
# The corrected tops at `Y_{k+3}` from the readings at the `ψ_{Ω_{k+3}}`-iterates; `Θ_λ(θ)`

`Θ = gxTh ρ_λ (ldAtR λ)`, `Y_{k+2} = ψ_{Ω_{k+2}}(Ω_{k+2}) = Uj.ujY S k`, `y^{(k)}_n` the iterates of `ψ_{Ω_{k+3}}`
from `0` (`y^{(k)}_0 = 0`, `y^{(k)}_{n+1} = ψ_{Ω_{k+3}}(y^{(k)}_n)`), `z^{(k)}_n` those of `ψ_{Ω_{k+2}}`;
`θ = ψ_{Ω₂}(Ω_ω)`.

`VxItRead S λ A k` (abbreviation, a `Prop`, not a new object): `∀ n, Θ(ψ₂(y^{(k)}_{n+1})) = ψ₁(A + 1 + z^{(k)}_{n+1})`.

* `vxReadY_of_it` (**`∀ n, Θ(ψ₂(y^{(k)}_{n+1})) = ψ₁(A + 1 + z^{(k)}_{n+1})` ⇒ `Θ(ψ₂(Y_{k+3})) = ψ₁(A + 1 + Y_{k+2})`**,
  for every `k`, one proof: the limit rule `Ug.ugReadLim` over the iterates, cofinal in `Y_{k+3}`, `Y_{k+2}`);
* `vxIt0` (**the case `k = 0` holds**: `Θ(ψ₂(y_{n+1})) = ψ₁(A + 1 + z_{n+1})`, from `Vn.vnTop_it`);
* `vxTheta_of_it` (**`Θ_λ(θ) = ψ_{Ω₁}(A + 1 + Ω_ω)` from the iterate readings at every level `k ≥ 1`**, with
  `Vn.vnTheta_th`), `vxImg0_of_it` (the image read from the base `0` at `Ω_{k+3}` is `Y_{k+2}`), `vxDyn_le0_of_it`.

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Vx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj Googology.Trans.PoR.InaccPsi.R2.Uu
  Googology.Trans.PoR.InaccPsi.R2.Vk Googology.Trans.PoR.InaccPsi.R2.Vn Googology.Trans.PoR.InaccPsi.R2.Vq

variable {S : InaccSeq.{0}}

theorem vxNat_lt_Om1 (k : ℕ) : (k : Ordinal.{0}) + 1 + 1 + 1 < Om 1 :=
  (vkNat_lt_omega k).trans (omega0_lt_Om one_ne_zero)

/-- **The reading at `Y_{k+3}` from the readings at the iterates `y^{(k)}_{n+1}`**, for every `k`. -/
theorem vxReadY_of_it {l A : Ordinal.{0}} (k : ℕ)
    (hIt : ∀ n : ℕ, gxTh (upsilon l) (ldAtR S l)
        (S.psi ((fun x => S.psi x (Om ((k : Ordinal.{0}) + 1 + 1 + 1)))^[n + 1] 0) (Om (1 + 1))) =
      S.psi (A + 1 + (fun x => S.psi x (Om ((k : Ordinal.{0}) + 1 + 1)))^[n + 1] 0) (Om 1)) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (ujY S ((k : Ordinal.{0}) + 1)) (Om (1 + 1))) =
      S.psi (A + 1 + ujY S (k : Ordinal.{0})) (Om 1) := by
  have hs3 : (k : Ordinal.{0}) + 1 + 1 + 1 < Om 1 := vxNat_lt_Om1 k
  have hs2 : (k : Ordinal.{0}) + 1 + 1 < Om 1 := (lt_add_one _).trans hs3
  have hEX : ∀ n : ℕ, (fun x => S.psi x (Om ((k : Ordinal.{0}) + 1 + 1 + 1)))^[n + 1] 0 ≤
      ujY S ((k : Ordinal.{0}) + 1) := fun n =>
    (vnIt_lt (s := (k : Ordinal.{0}) + 1 + 1) (vnOmK3_mem k) (n + 1)).le
  have hEcof : ∀ e, e < ujY S ((k : Ordinal.{0}) + 1) →
      ∃ n : ℕ, e < (fun x => S.psi x (Om ((k : Ordinal.{0}) + 1 + 1 + 1)))^[n + 1] 0 := by
    intro e he
    obtain ⟨m, hm⟩ := (lt_ciSup_iff (uuIt_bdd (S := S) ((k : Ordinal.{0}) + 1 + 1))).1
      (he.trans_le (uuY_le_sup (S := S) hs3))
    exact ⟨m, hm.trans (uuIt_lt (S := S) _ m)⟩
  have hyY : ∀ n : ℕ, (fun x => S.psi x (Om ((k : Ordinal.{0}) + 1 + 1)))^[n + 1] 0 ≤ ujY S (k : Ordinal.{0}) :=
    fun n => (vnIt_lt (s := (k : Ordinal.{0}) + 1) (vnOmK_mem k) (n + 1)).le
  have hycof : ∀ z, z < ujY S (k : Ordinal.{0}) →
      ∃ n : ℕ, z ≤ (fun x => S.psi x (Om ((k : Ordinal.{0}) + 1 + 1)))^[n + 1] 0 := by
    intro z hz
    obtain ⟨m, hm⟩ := (lt_ciSup_iff (uuIt_bdd (S := S) ((k : Ordinal.{0}) + 1))).1
      (hz.trans_le (uuY_le_sup (S := S) hs2))
    exact ⟨m, (hm.trans (uuIt_lt (S := S) _ m)).le⟩
  have hTop : ∀ n : ℕ, gxTh (upsilon l) (ldAtR S l)
      (S.psi (0 + (fun x => S.psi x (Om ((k : Ordinal.{0}) + 1 + 1 + 1)))^[n + 1] 0) (Om (1 + 1))) =
      S.psi (A + 1 + (fun x => S.psi x (Om ((k : Ordinal.{0}) + 1 + 1)))^[n + 1] 0) (Om 1) := fun n => by
    rw [zero_add]; exact hIt n
  have h := ugReadLim (S := S) (l := l) (β := 0) (Â := A + 1)
    (fun n => (fun x => S.psi x (Om ((k : Ordinal.{0}) + 1 + 1 + 1)))^[n + 1] 0)
    (fun n => (fun x => S.psi x (Om ((k : Ordinal.{0}) + 1 + 1)))^[n + 1] 0)
    (ujY_SC _).isSuccLimit (ujY_SC _).isSuccLimit hEX hEcof hyY hycof hTop
  rw [zero_add] at h
  exact h

section Main

variable {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hl hX hA hρ

/-- **The iterate readings at the level `k = 0` hold**: `Θ(ψ₂(y_{n+1})) = ψ₁(A + 1 + z_{n+1})`. -/
theorem vxIt0 : ∀ n : ℕ, gxTh (upsilon l) (ldAtR S l)
      (S.psi ((fun x => S.psi x (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1)))^[n + 1] 0) (Om (1 + 1))) =
    S.psi (A + 1 + (fun x => S.psi x (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1)))^[n + 1] 0) (Om 1) := by
  intro n
  simp only [Nat.cast_zero, zero_add]
  have h := vnTop_it hl hX hA hρ n
  have hW := (Ua.uaWfix (gg_SC_eps (vqY_SC (S := S) n)) (vqY_gt n)).2
  have hO := Ua.uaOe_fix (gg_SC_eps (vqZ_SC (S := S) n)) (vqZ_gt n)
  rw [hW, hW, hO, hO] at h
  exact h

/-- **`Θ_λ(θ) = ψ_{Ω₁}(A + 1 + Ω_ω)` from the iterate readings at every level `k ≥ 1`.** -/
theorem vxTheta_of_it
    (hIt : ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, gxTh (upsilon l) (ldAtR S l)
        (S.psi ((fun x => S.psi x (Om ((k : Ordinal.{0}) + 1 + 1 + 1)))^[n + 1] 0) (Om (1 + 1))) =
      S.psi (A + 1 + (fun x => S.psi x (Om ((k : Ordinal.{0}) + 1 + 1)))^[n + 1] 0) (Om 1)) :
    gxTh (upsilon l) (ldAtR S l) (ConjT.th S) = S.psi (A + 1 + Om ω) (Om 1) := by
  refine vnTheta_th (fun k => vxReadY_of_it k ?_)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact vxIt0 hl hX hA hρ
  · exact hIt k hk

omit hl hX hA hρ in
/-- **The image read from the base `0` at `Ω_{k+3}` is `Y_{k+2}`**, from the iterate readings at `k`. -/
theorem vxImg0_of_it (k : ℕ)
    (hIt : ∀ n : ℕ, gxTh (upsilon l) (ldAtR S l)
        (S.psi ((fun x => S.psi x (Om ((k : Ordinal.{0}) + 1 + 1 + 1)))^[n + 1] 0) (Om (1 + 1))) =
      S.psi (A + 1 + (fun x => S.psi x (Om ((k : Ordinal.{0}) + 1 + 1)))^[n + 1] 0) (Om 1)) :
    gxTh (upsilon l) (ldAtR S l) (leTe S (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) 0) =
      S.psi (A + 1 + leOe (ujY S (k : Ordinal.{0}))) (Om 1) :=
  vxImg0K k (vxReadY_of_it k hIt)

/-- Every dynamic top at `Ω_{k+3}` over the base `0` has `Ω^{X̂(0)} ≤ Y_{k+2}`, from the iterate readings at `k`;
with the fixed image `Ω_{k+2}` this is `Vn.vnTop_OmK` again. -/
theorem vxDyn_le0_of_it (k : ℕ)
    (hIt : ∀ n : ℕ, gxTh (upsilon l) (ldAtR S l)
        (S.psi ((fun x => S.psi x (Om ((k : Ordinal.{0}) + 1 + 1 + 1)))^[n + 1] 0) (Om (1 + 1))) =
      S.psi (A + 1 + (fun x => S.psi x (Om ((k : Ordinal.{0}) + 1 + 1)))^[n + 1] 0) (Om 1))
    {Xh : Ordinal.{0} → Ordinal.{0}}
    (hT : Vt.VtTopDyn S l 0 (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) Xh 0) :
    leOe (Xh 0) ≤ ujY S (k : Ordinal.{0}) :=
  vxDyn_le0K hl hX hA hρ k (vxReadY_of_it k hIt) hT

end Main

#print axioms vxReadY_of_it
#print axioms vxIt0
#print axioms vxTheta_of_it
#print axioms vxImg0_of_it
#print axioms vxDyn_le0_of_it

end Googology.Trans.PoR.InaccPsi.R2.Vx

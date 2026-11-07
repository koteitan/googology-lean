import Googology.Trans.PoR.InaccPsi.R2.ZrRead
import Googology.Trans.PoR.InaccPsi.R2.GgOtp

/-!
# Zr: the readings of the atoms `ψ_{Ω₂}(Ω_ω + c)` below the plateau are EXACT

Conventions of `Zr.ZrRead`: `H = Cl(A, ρ)`, `ρ = ψ_{Ω₁}(A)`, `Θ(x) = otp(H ∩ x)`, `θ = ψ_{Ω₂}(Ω_ω)` with
`Θ(θ) = ψ_{Ω₁}(A + θ)`, `g(x) = ψ_{Ω₁}(A + θ + x)`, `F_0 = ρ`, `F_{j+1} = g(F_j)`, `K_0 = Ω₁`,
`K_{j+1} = ψ_{Ω₂}(Ω_ω + K_j)`.  `Zr.zrInner` and `Zr.zrOuter` are the upper bounds.  Here the lower bounds:

* `zr_lt_atom` (below the plateau the atom map grows: `x < ψ_{Ω₂}(Ω_ω + x)` for `x < K_j`);
* `zrInnerLow` (**`g(Θ(c)) ≤ Θ(ψ_{Ω₂}(Ω_ω + c))`** for `c ∈ H`, `c < K_j`, `Ω_ω + c < A`): by `Bt.psi_le_of_key` at
  the strongly critical `Z = Θ(ψ_{Ω₂}(Ω_ω + c))` (`Ls.lsOtp_SC`); a collapse argument `e < A + θ` gives at most
  `Θ(θ) < Z`, and `e = A + θ + w` with `w < Θ(c)` is `w = Θ(c')` for some `c' ∈ H ∩ c` (`Gg.ggOtp_onto`), so
  `ψ_{Ω₁}(e) ≤ Θ(ψ_{Ω₂}(Ω_ω + c')) < Z` by induction;
* `zrInner_eq` (**`Θ(ψ_{Ω₂}(Ω_ω + c)) = g(Θ(c))`**, with `Zr.zrInner`), `zrOuterLow`, `zrOuter_eq`
  (**`Θ(K_j) = F_j`** when `Ω_ω + K_i < A` for `i < j`).

No new axiom, no new definition.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Googology.Trans.PoR.InaccPsi.R2.Zr

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Zo Googology.Trans.PoR.InaccPsi.R2.Le

variable {S : InaccSeq.{0}}

theorem zrK_zero : zrK S 0 = Om 1 := rfl

/-- **Below the plateau the atom map grows**: `x < ψ_{Ω₂}(Ω_ω + x)` for `x < K_j`. -/
theorem zr_lt_atom : ∀ j : ℕ, ∀ x, x < zrK S j → x < S.psi (Om ω + x) (Om (1 + 1))
  | 0, x, hx => by
    rw [zrK_zero] at hx
    exact hx.trans (psiS_bounds (S := S) _ 1).1
  | j + 1, x, hx => by
    rcases lt_or_ge x (zrK S j) with h | h
    · exact zr_lt_atom j x h
    · calc x < zrK S (j + 1) := hx
        _ = S.psi (Om ω + zrK S j) (Om (1 + 1)) := zrK_succ j
        _ ≤ S.psi (Om ω + x) (Om (1 + 1)) := (psi_mono (S := S) (InR_Om_succ 1) (add_le_add le_rfl h)).1

/-- An atom `ψ_{Ω₂}(Ω_ω + c)` with `c ∈ H`, `Ω_ω + c < A` lies in `H`. -/
theorem zrAtom_mem {A ρ c : Ordinal.{0}} (hc : c ∈ S.CSet A ρ) (hcA : Om ω + c < A) :
    S.psi (Om ω + c) (Om (1 + 1)) ∈ S.CSet A ρ :=
  CSet.psi_mem hcA (InR_Om_succ 1) (Mx.mxOm2_mem _ _) (CSet.add_mem (ConjT.OmW_mem (S := S) _ _) hc)

/-- The atom map is strictly increasing on `c' < c < K_j`. -/
theorem zrAtom_lt {j : ℕ} {c c' : Ordinal.{0}} (hcK : c < zrK S j) (hc' : c' < c) :
    S.psi (Om ω + c') (Om (1 + 1)) < S.psi (Om ω + c) (Om (1 + 1)) :=
  psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left _).2 hc')
    (CSet.add_mem (Zj.zjOmW_own c) (CSet.of_lt (hc'.trans (zr_lt_atom j c hcK))))

section Low

variable {A ρ : Ordinal.{0}} (hρ : S.psi A (Om 1) = ρ) (hA : Om ω < A)
  (hown : A ∈ S.CSet A ρ)
  (hθ : cdOtp (S.CSet A ρ) (ConjT.th S) = S.psi (A + ConjT.th S) (Om 1))

include hρ hA hown hθ

/-- **`g(Θ(c)) ≤ Θ(ψ_{Ω₂}(Ω_ω + c))`** for `c ∈ H` below the plateau with `Ω_ω + c < A`. -/
theorem zrInnerLow (j : ℕ) :
    ∀ c, c ∈ S.CSet A ρ → c < zrK S j → Om ω + c < A →
      zrPs S A (cdOtp (S.CSet A ρ) c) ≤ cdOtp (S.CSet A ρ) (S.psi (Om ω + c) (Om (1 + 1))) := by
  intro c
  induction c using WellFoundedLT.induction with
  | _ c IH =>
  intro hc hcK hcA
  have htH := zrAtom_mem hc hcA
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [zrHull_zero, add_zero]
    unfold zrPs
    rw [add_zero, ← hθ]
    exact le_rfl
  have hZ : SC (cdOtp (S.CSet A ρ) (S.psi (Om ω + c) (Om (1 + 1)))) :=
    Ls.lsOtp_SC hρ (SC_psi (InR_Om_succ 1) _) (psiS_bounds (S := S) _ 1).1 (psi_lt (InR_Om_succ 1) _).le
  have hθH : ConjT.th S ∈ S.CSet A ρ := ConjT.th_mem (S := S) hA
  have hθt : ConjT.th S < S.psi (Om ω + c) (Om (1 + 1)) :=
    psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hc0)) (Zj.zjOmW_own c)
  have hΘθ : S.psi (A + ConjT.th S) (Om 1) < cdOtp (S.CSet A ρ) (S.psi (Om ω + c) (Om (1 + 1))) := by
    rw [← hθ]; exact cdOtp_lt_of_mem hθH hθt
  unfold zrPs
  refine psi_le_of_key hZ fun e _ hea => ?_
  rcases lt_or_ge e (A + ConjT.th S) with h1 | h1
  · exact ((psi_mono (S := S) Low.InR_Om_one h1.le).1).trans_lt hΘθ
  · obtain ⟨w, rfl⟩ := exists_add_of_le h1
    have hw : w < cdOtp (S.CSet A ρ) c := (add_lt_add_iff_left _).1 hea
    obtain ⟨c', hc'H, hc'c, rfl⟩ := Gg.ggOtp_onto _ c w hw
    have hc'A : Om ω + c' < A := ((add_lt_add_iff_left _).2 hc'c).trans hcA
    have hIH := IH c' hc'c hc'H (hc'c.trans hcK) hc'A
    unfold zrPs at hIH
    exact hIH.trans_lt (cdOtp_lt_of_mem (zrAtom_mem hc'H hc'A) (zrAtom_lt hcK hc'c))

/-- **`Θ(ψ_{Ω₂}(Ω_ω + c)) = g(Θ(c))`** for `c ∈ H` below the plateau with `Ω_ω + c < A`, given `Θ(K_j) ≤ F_j`. -/
theorem zrInner_eq (j : ℕ) (hO : cdOtp (S.CSet A ρ) (zrK S j) ≤ zrF S A ρ j) {c : Ordinal.{0}}
    (hc : c ∈ S.CSet A ρ) (hcK : c < zrK S j) (hcA : Om ω + c < A) :
    cdOtp (S.CSet A ρ) (S.psi (Om ω + c) (Om (1 + 1))) = zrPs S A (cdOtp (S.CSet A ρ) c) :=
  le_antisymm (zrInner hρ hA hown hθ j hO c hc hcK) (zrInnerLow hρ hA hown hθ j c hc hcK hcA)

variable (hΩ : cdOtp (S.CSet A ρ) (Om 1) = ρ)

include hΩ

/-- **`F_j ≤ Θ(K_j)`** when `Ω_ω + K_i < A` for `i < j`. -/
theorem zrOuterLow : ∀ j : ℕ, (∀ i < j, Om ω + zrK S i < A) → zrF S A ρ j ≤ cdOtp (S.CSet A ρ) (zrK S j)
  | 0, _ => by rw [zrK_zero, hΩ]; exact le_rfl
  | j + 1, h => by
    have hIH := zrOuterLow j fun i hi => h i (hi.trans (Nat.lt_succ_self j))
    have hKj : zrK S j ∈ S.CSet A ρ := zrK_mem j fun i hi => h i (hi.trans (Nat.lt_succ_self j))
    have hlow := zrInnerLow hρ hA hown hθ (j + 1) (zrK S j) hKj (zrK_lt_succ j) (h j (Nat.lt_succ_self j))
    rw [zrK_succ]
    exact (zrPs_mono hIH).trans hlow

/-- **`Θ(K_j) = F_j`** when `Ω_ω + K_i < A` for `i < j`. -/
theorem zrOuter_eq (j : ℕ) (h : ∀ i < j, Om ω + zrK S i < A) : cdOtp (S.CSet A ρ) (zrK S j) = zrF S A ρ j :=
  le_antisymm (zrOuter hρ hA hown hθ hΩ j) (zrOuterLow hρ hA hown hθ hΩ j h)

end Low

end Googology.Trans.PoR.InaccPsi.R2.Zr

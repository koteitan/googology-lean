import Googology.Trans.PoR.InaccPsi.R2.LsPsi

/-!
# The hull below `Ω₂` as codes over `ρ` with the atoms `ψ_{Ω₂}(e)`: the reading of a strongly critical code

`ρ = ψ_{Ω₁}(A)`, the hull `Cl(A, ρ)` (at a restart `λ`, `A = A_{η_λ}`, `ρ = ρ_λ`, `Cl(A, ρ) = Cd.cdHull S λ`),
`Θ(m) = otp(Cl(A, ρ) ∩ m)` (`Cd.cdOtp`; `Cd.cdTheta S λ m` at a restart).  `Mx.mxHull_iff` describes the hull
below `K = ψ_{Ω₂}(Ω₁)`; the same induction works below `Ω₂` with every `ψ_{Ω₂}`-value of the hull as an atom:

* `lsAt S A ρ` (**the atoms**): the `ψ_{Ω₂}(e)` with `e < A`, `e ∈ Cl(A, ρ)`; `lsAt_GxAt` (strongly critical,
  above `Ω₁`), `lsAt_mem` (the atoms are in the hull);
* `lsHull_iff` (**below `Ω₂` the hull is the set of codes `Mx.GxCl ρ (lsAt S A ρ)`**: generated from `[0, ρ)`,
  `Ω₁` and the atoms by `+` and `φ`), `lsOtp_eq` (**`Θ(m) = Mx.gxTh ρ (lsAt S A ρ) m` for `m ≤ Ω₂`**);
* `lsOtp_SC` (**`Θ(s)` is strongly critical** for a strongly critical `s ∈ (Ω₁, Ω₂]`), `lsOtp_gt` (`ρ < Θ(s)`
  for `s > Ω₁`), `lsOtp_least` (**`Θ(s)` is the least strongly critical ordinal above `ρ` and above the readings
  of the atoms below `s`**), `lsOtp_atom_lt` (an atom `t < s` has `Θ(t) < Θ(s)`).

No new axiom.  New definition: `lsAt`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ls

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Mx

variable {S : InaccSeq.{0}}

/-- **The atoms** of the hull `Cl(A, ρ)` below `Ω₂`: the `ψ_{Ω₂}(e)` with `e < A` in the hull. -/
def lsAt (S : InaccSeq.{0}) (A ρ : Ordinal.{0}) : Set Ordinal.{0} :=
  {s | ∃ e, e < A ∧ e ∈ S.CSet A ρ ∧ s = S.psi e (Om (1 + 1))}

theorem lsAt_GxAt (A ρ : Ordinal.{0}) : GxAt (lsAt S A ρ) := by
  rintro s ⟨e, -, -, rfl⟩
  exact ⟨SC_psi (InR_Om_succ 1) e, (psiS_bounds (S := S) e 1).1⟩

theorem lsAt_mem {A ρ s : Ordinal.{0}} (hs : s ∈ lsAt S A ρ) : s ∈ S.CSet A ρ := by
  obtain ⟨e, he, heC, rfl⟩ := hs
  exact CSet.psi_mem he (InR_Om_succ 1) (mxOm2_mem _ _) heC

theorem lsAt_lt_Om2 {A ρ s : Ordinal.{0}} (hs : s ∈ lsAt S A ρ) : s < Om (1 + 1) := by
  obtain ⟨e, -, -, rfl⟩ := hs
  exact psi_lt (InR_Om_succ 1) e

/-- **Below `Ω₂` the hull `Cl(A, ψ_{Ω₁}(A))` is the set of codes over `ρ` with the atoms `lsAt S A ρ`.** -/
theorem lsHull_iff {A ρ x : Ordinal.{0}} (hρ : S.psi A (Om 1) = ρ) (hx2 : x < Om (1 + 1)) :
    x ∈ S.CSet A ρ ↔ GxCl ρ (lsAt S A ρ) x := by
  have hρ0 : 0 < ρ := hρ ▸ (SC_psi Low.InR_Om_one A).1
  constructor
  · intro hx
    have key : ∀ y ∈ S.CSet A ρ, y < Om 1 → y < ρ := fun y hy hy1 => by
      rw [← hρ] at hy ⊢; exact lt_psi_of_mem Low.InR_Om_one hy hy1
    revert hx2
    have hx' := hx
    induction hx with
    | small h => exact fun _ => GxCl.small h
    | zero => exact fun _ => GxCl.zero hρ0
    | inacc n => exact fun h => absurd (h.trans (mxOm2_lt_I n)) (lt_irrefl _)
    | inaccW => exact fun h => absurd (h.trans mxOm2_lt_Iw) (lt_irrefl _)
    | @add x y hx1 hy1 ihx ihy =>
      intro h
      exact GxCl.add (ihx hx1 (lt_of_le_of_lt le_self_add h)) (ihy hy1 (lt_of_le_of_lt le_add_self h))
    | @phi x y hx1 hy1 ihx ihy =>
      intro h
      exact GxCl.phi (ihx hx1 (lt_of_le_of_lt (left_le_veblen x y) h))
        (ihy hy1 (lt_of_le_of_lt (right_le_veblen x y) h))
    | @om x hx1 _ =>
      intro h
      have h2 : x < 1 + 1 := Om_lt_Om.1 h
      rcases (Order.lt_add_one_iff.1 h2).lt_or_eq with h0 | h1
      · rw [Order.lt_one_iff] at h0; rw [h0, Om_zero]; exact GxCl.zero hρ0
      · rw [h1]; exact GxCl.om
    | @coll π e hπ hπ1 he1 _ _ =>
      intro h
      rcases hπ with ⟨n, rfl⟩ | ⟨s, rfl⟩
      · exfalso
        have h2 : Om (1 + 1 : Ordinal.{0}) < S.psi e.1 (S.I n) :=
          lt_psi_of_mem (InR_I n) (mxOm2_mem _ _) (mxOm2_lt_I n)
        exact absurd (h2.trans h) (lt_irrefl _)
      rcases eq_or_ne s 0 with rfl | hs0
      · rw [zero_add] at hx' ⊢
        exact GxCl.small (key _ hx' (psi_lt Low.InR_Om_one _))
      rcases eq_or_ne s 1 with rfl | hs1
      · exact GxCl.atom ⟨e.1, e.2, he1, rfl⟩
      · exfalso
        have h2s : 1 + 1 ≤ s := Order.add_one_le_of_lt (lt_of_le_of_ne
          (Order.one_le_iff_ne_zero.2 hs0) (Ne.symm hs1))
        have h2 := (Om_lt_psiS (S := S) e.1 s).2 h2s
        exact absurd (h2.trans h) (lt_irrefl _)
  · intro hx
    clear hx2
    induction hx with
    | small h => exact CSet.of_lt h
    | om => exact CSet.Om_mem (CSet.one_mem _ _)
    | atom hs => exact lsAt_mem hs
    | add _ _ ihx ihy => exact CSet.add_mem ihx ihy
    | phi _ _ ihx ihy => exact CSet.phi_mem ihx ihy

/-- **`Θ(m) = Mx.gxTh ρ (lsAt S A ρ) m`** for `m ≤ Ω₂`. -/
theorem lsOtp_eq {A ρ m : Ordinal.{0}} (hρ : S.psi A (Om 1) = ρ) (hm : m ≤ Om (1 + 1)) :
    cdOtp (S.CSet A ρ) m = gxTh ρ (lsAt S A ρ) m :=
  Gg.ggOtp_congr m fun _ hx => lsHull_iff hρ (hx.trans_le hm)

theorem lsRho_SC {A ρ : Ordinal.{0}} (hρ : S.psi A (Om 1) = ρ) : SC ρ := hρ ▸ SC_psi Low.InR_Om_one A

theorem lsRho_lt {A ρ : Ordinal.{0}} (hρ : S.psi A (Om 1) = ρ) : ρ < Om 1 := hρ ▸ psi_lt Low.InR_Om_one A

/-- **The reading of a strongly critical `s ∈ (Ω₁, Ω₂]` is strongly critical.** -/
theorem lsOtp_SC {A ρ s : Ordinal.{0}} (hρ : S.psi A (Om 1) = ρ) (hs : SC s) (h1 : Om 1 < s)
    (hs2 : s ≤ Om (1 + 1)) : SC (cdOtp (S.CSet A ρ) s) := by
  rw [lsOtp_eq hρ hs2]
  exact gxTh_SC (lsRho_SC hρ) (lsAt_GxAt A ρ) hs ((lsRho_lt hρ).trans h1)

/-- `ρ < Θ(s)` for `Ω₁ < s ≤ Ω₂`. -/
theorem lsOtp_gt {A ρ s : Ordinal.{0}} (hρ : S.psi A (Om 1) = ρ) (h1 : Om 1 < s)
    (hs2 : s ≤ Om (1 + 1)) : ρ < cdOtp (S.CSet A ρ) s := by
  rw [lsOtp_eq hρ hs2]
  have := gxTh_lt (Z := ρ) (At := lsAt S A ρ) GxCl.om h1
  rwa [gxTh_Om1 (lsRho_SC hρ) (lsRho_lt hρ) (lsAt_GxAt A ρ)] at this

/-- An atom `t < s` has `Θ(t) < Θ(s)`. -/
theorem lsOtp_atom_lt {A ρ s t : Ordinal.{0}} (ht : t ∈ lsAt S A ρ) (hts : t < s) :
    cdOtp (S.CSet A ρ) t < cdOtp (S.CSet A ρ) s :=
  cdOtp_lt_of_mem (lsAt_mem ht) hts

/-- **`Θ(s)` is at most every strongly critical `X > ρ` above the readings of the atoms below `s`.** -/
theorem lsOtp_least {A ρ s X : Ordinal.{0}} (hρ : S.psi A (Om 1) = ρ) (hs2 : s ≤ Om (1 + 1))
    (hX : SC X) (hρX : ρ < X)
    (hat : ∀ t ∈ lsAt S A ρ, t < s → cdOtp (S.CSet A ρ) t < X) : cdOtp (S.CSet A ρ) s ≤ X := by
  have hZ := lsRho_SC hρ
  have hAt := lsAt_GxAt (S := S) A ρ
  have hat' : ∀ t ∈ lsAt S A ρ, t < s → gxTh ρ (lsAt S A ρ) t < X := fun t ht hts => by
    rw [← lsOtp_eq hρ (hts.le.trans hs2)]; exact hat t ht hts
  have hb := mxGx_bound hZ (lsRho_lt hρ) hAt hX hρX hat'
  rw [lsOtp_eq hρ hs2]
  exact mxOtp_le (gxSet ρ (lsAt S A ρ)) s X (gxTh ρ (lsAt S A ρ))
    (fun c _ _ c' hc' hc'c => gxTh_lt hc' hc'c) (fun c hc hcs => hb c hc hcs)

end Googology.Trans.PoR.InaccPsi.R2.Ls

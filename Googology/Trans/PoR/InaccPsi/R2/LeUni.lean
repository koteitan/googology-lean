import Googology.Trans.PoR.InaccPsi.R2.LeMove
import Googology.Trans.PoR.InaccPsi.R2.LsHull

/-!
# The hull lemmas of `R2.LsHull` are those of `R2.LdHull`

`Ls.lsAt S A ρ` and `Ld.ldAt S A ρ` are the same set (the `ψ_{Ω₂}(e)`, `e < A`, `e ∈ Cl(A, ρ)`; the two definitions
differ only in the order of the two conditions).  So `Ls.lsHull_iff` is `Ld.ldHullG_iff`, `Ls.lsOtp_eq` is
`Ld.ldTheta` without the restart, and `Ls.lsOtp_least` is `Ld.ldAtom_le` read through `Θ = gxTh`.

* `leAt_eq` (**`lsAt = ldAt`**);
* `leHull_iff` (`Ls.lsHull_iff` from `Ld.ldHullG_iff`), `leOtp_eq` (`Ls.lsOtp_eq` with `ldAt`),
  `leOtp_least` (`Ls.lsOtp_least` from `Ld.ldAtom_le`), `leOtp_ge` (`Ld.ldAtom_ge` for `cdOtp`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Le

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld

variable {S : InaccSeq.{0}}

/-- **`lsAt = ldAt`.** -/
theorem leAt_eq (A ρ : Ordinal.{0}) : Ls.lsAt S A ρ = ldAt S A ρ := by
  ext s
  constructor
  · rintro ⟨e, he, heC, rfl⟩; exact ⟨e, heC, he, rfl⟩
  · rintro ⟨e, heC, he, rfl⟩; exact ⟨e, he, heC, rfl⟩

/-- `Ls.lsHull_iff`, from `Ld.ldHullG_iff`. -/
theorem leHull_iff {A ρ x : Ordinal.{0}} (hρ : S.psi A (Om 1) = ρ) (hx2 : x < Om (1 + 1)) :
    x ∈ S.CSet A ρ ↔ GxCl ρ (Ls.lsAt S A ρ) x := by
  rw [leAt_eq]
  exact ldHullG_iff (hρ ▸ (SC_psi Low.InR_Om_one A).1)
    (fun y hy hy1 => by rw [← hρ] at hy ⊢; exact lt_psi_of_mem Low.InR_Om_one hy hy1) hx2

/-- `Ls.lsOtp_eq` with the atoms `ldAt`. -/
theorem leOtp_eq {A ρ m : Ordinal.{0}} (hρ : S.psi A (Om 1) = ρ) (hm : m ≤ Om (1 + 1)) :
    cdOtp (S.CSet A ρ) m = gxTh ρ (ldAt S A ρ) m := by
  rw [← leAt_eq]
  exact ggOtp_congr m fun _ hx => leHull_iff hρ (hx.trans_le hm)

/-- `Ls.lsOtp_least`, from `Ld.ldAtom_le`. -/
theorem leOtp_least {A ρ s X : Ordinal.{0}} (hρ : S.psi A (Om 1) = ρ) (hs2 : s ≤ Om (1 + 1))
    (hX : SC X) (hρX : ρ < X)
    (hat : ∀ t ∈ Ls.lsAt S A ρ, t < s → cdOtp (S.CSet A ρ) t < X) : cdOtp (S.CSet A ρ) s ≤ X := by
  have hZ : SC ρ := hρ ▸ SC_psi Low.InR_Om_one A
  have hZ1 : ρ < Om 1 := hρ ▸ psi_lt Low.InR_Om_one A
  rw [leOtp_eq hρ hs2]
  refine ldAtom_le hZ hZ1 (ldAt_GxAt A ρ) hX hρX fun t ht hts => ?_
  rw [← leOtp_eq hρ (hts.le.trans hs2)]
  exact hat t (by rw [leAt_eq]; exact ht) hts

/-- `Ld.ldAtom_ge` for `cdOtp`: the reading of an atom is strongly critical, above `ρ` and above the readings of
the atoms below it. -/
theorem leOtp_ge {A ρ s : Ordinal.{0}} (hρ : S.psi A (Om 1) = ρ) (hs : s ∈ Ls.lsAt S A ρ) :
    SC (cdOtp (S.CSet A ρ) s) ∧ ρ < cdOtp (S.CSet A ρ) s ∧
      ∀ t ∈ Ls.lsAt S A ρ, t < s → cdOtp (S.CSet A ρ) t < cdOtp (S.CSet A ρ) s := by
  have hZ : SC ρ := hρ ▸ SC_psi Low.InR_Om_one A
  have hZ1 : ρ < Om 1 := hρ ▸ psi_lt Low.InR_Om_one A
  rw [leAt_eq] at hs ⊢
  have hs2 : s ≤ Om (1 + 1) := by
    obtain ⟨e, -, -, rfl⟩ := hs; exact (psi_lt (InR_Om_succ 1) e).le
  obtain ⟨h1, h2, h3⟩ := ldAtom_ge hZ hZ1 (ldAt_GxAt A ρ) hs
  rw [leOtp_eq hρ hs2]
  refine ⟨h1, h2, fun t ht hts => ?_⟩
  rw [leOtp_eq hρ (hts.le.trans hs2)]
  exact h3 t ht hts

end Googology.Trans.PoR.InaccPsi.R2.Le

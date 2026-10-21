import Googology.Trans.PoR.InaccPsi.R2.LsHull

/-!
# LC-STRICT is exactly a covering of the collapses `ψ_{Ω₁}(A + ζ)` by the readings of the atoms

At a restart `λ` with `ρ_λ = P(η_λ)`: `A = A_{η_λ}`, the hull `Cl(A, ρ_λ)`, `Θ_λ(m) = otp(Cl(A, ρ_λ) ∩ m)`, the atoms
`lsAt S A ρ_λ` (the `ψ_{Ω₂}(e)` of the hull), `G_k = G(θ_k·ω²)` (`Lc.lcG`, `Lc.lcTh`).  `Lc.LcStrictAt S λ k` is
`H(η_λ + G_k) ≤ Θ_λ(G_{k+1})`; `H(η_λ + G_k) = ψ_{Ω₁}(A + G_k)` (`lsH_G`).

* `lsOtp_le_psi` (**the upper bound of every reading**: `Θ(m) ≤ ψ_{Ω₁}(A + m)` for an own `A`; the map
  `c ↦ ψ_{Ω₁}(A + c)` is strictly increasing on the hull, as in `Mx.mxTheta_le_succ`), `lsTheta_le_psi`;
* `LsCover S λ k` (**the covering**): every `ζ < G_k` has `ψ_{Ω₁}(A + ζ) ≤ ρ_λ` or an atom `t < G_{k+1}` with
  `ψ_{Ω₁}(A + ζ) ≤ Θ_λ(t)`; `LsCoverMem` (the same, asked only at the `ζ ∈ Cl(A + G_k, Θ_λ(G_{k+1}))`);
* `lsStrict_of_cover` (**`LsCover → LC-STRICT`**: `Θ_λ(G_{k+1})` is strongly critical, above `ρ_λ` and above
  the readings of the atoms below `G_{k+1}` (`lsOtp_SC`, `lsOtp_gt`, `lsOtp_atom_lt`), so `lsPsi_le` applies);
* `lsStrict_iff` (**`LC-STRICT ↔ LsCoverMem`**, given `A` own and `ω^{G_k} ∣ A`: if `ψ_{Ω₁}(A + ζ)` were above
  `ρ_λ` and every atom reading below `G_{k+1}`, it would bound `Θ_λ(G_{k+1})` (`lsOtp_least`), while it is below
  it (`InaccSeq.psi_lt_psi_of_mem` at the members `ζ`)).

So LC-STRICT asks only for the readings `Θ_λ(ψ_{Ω₂}(e))` of the atoms `ψ_{Ω₂}(e) < G_{k+1}`, `e ∈ Cl(A, ρ_λ)`:
they must dominate the collapses `ψ_{Ω₁}(A + ζ)`, `ζ < G_k`.  Nothing about `+`, `φ` or the other levels of the
hull is left.

No new axiom.  New definitions: `LsCover`, `LsCoverMem`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ls

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Mx

variable {S : InaccSeq.{0}}

/-! ## The upper bound of the reading -/

/-- **`Θ(m) ≤ ψ_{Ω₁}(A + m)`** for an own `A` (`A ∈ Cl(A, ψ_{Ω₁}(A))`). -/
theorem lsOtp_le_psi {A : Ordinal.{0}} (hown : A ∈ S.CSet A (S.psi A (Om 1))) (m : Ordinal.{0}) :
    cdOtp (S.CSet A (S.psi A (Om 1))) m ≤ S.psi (A + m) (Om 1) := by
  have hmem : ∀ c, c ∈ S.CSet A (S.psi A (Om 1)) → ∀ d, A ≤ d →
      A + c ∈ S.CSet d (S.psi d (Om 1)) := by
    intro c hc d hd
    exact CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one hd).2 hown)
      (CSet_mono hd zero_le (mxHull_sub0 hc))
  refine mxOtp_le _ _ _ (fun c => S.psi (A + c) (Om 1)) ?_ ?_
  · intro c _ _ c' hc' hc'c
    exact psi_lt_psi_of_mem Low.InR_Om_one ((add_lt_add_iff_left A).2 hc'c) (hmem c' hc' _ le_self_add)
  · intro c hc hcm
    exact psi_lt_psi_of_mem Low.InR_Om_one ((add_lt_add_iff_left A).2 hcm) (hmem c hc _ le_self_add)

/-- `Θ_λ(m) ≤ ψ_{Ω₁}(A_{η_λ} + m)` at a restart with `ρ_λ = P(η_λ)` and `A_{η_λ}` own. -/
theorem lsTheta_le_psi {l : Ordinal.{0}} (hpv : Nm.Pv S (cdEta S l) = upsilon l)
    (hown : ConjT.Aη S (cdEta S l) ∈ S.CSet (ConjT.Aη S (cdEta S l)) (Nm.Pv S (cdEta S l)))
    (m : Ordinal.{0}) : cdTheta S l m ≤ S.psi (ConjT.Aη S (cdEta S l) + m) (Om 1) := by
  unfold cdTheta cdHull
  rw [← hpv]
  exact lsOtp_le_psi hown m

/-! ## The covering -/

/-- `G_k = G(θ_k·ω²)`. -/
noncomputable abbrev lsG (S : InaccSeq.{0}) (k : ℕ) : Ordinal.{0} := Lc.lcG S (Lc.lcTh S k * ω ^ 2)

theorem lsG_Om1 (k : ℕ) : Om 1 < lsG S k := (psiS_bounds (S := S) _ 1).1

theorem lsG_Om2 (k : ℕ) : lsG S k ≤ Om (1 + 1) := (Lc.lcG_lt_Om2 _).le

/-- **The covering of the collapses below `G_k` by the atom readings below `G_{k+1}`.** -/
def LsCover (S : InaccSeq.{0}) (l : Ordinal.{0}) (k : ℕ) : Prop :=
  ∀ ζ < lsG S k, S.psi (ConjT.Aη S (cdEta S l) + ζ) (Om 1) ≤ upsilon l ∨
    ∃ t ∈ lsAt S (ConjT.Aη S (cdEta S l)) (upsilon l), t < lsG S (k + 1) ∧
      S.psi (ConjT.Aη S (cdEta S l) + ζ) (Om 1) ≤ cdTheta S l t

/-- The covering asked only at the `ζ ∈ Cl(A + G_k, Θ_λ(G_{k+1}))`. -/
def LsCoverMem (S : InaccSeq.{0}) (l : Ordinal.{0}) (k : ℕ) : Prop :=
  ∀ ζ ∈ S.CSet (ConjT.Aη S (cdEta S l) + lsG S k) (cdTheta S l (lsG S (k + 1))), ζ < lsG S k →
    S.psi (ConjT.Aη S (cdEta S l) + ζ) (Om 1) ≤ upsilon l ∨
    ∃ t ∈ lsAt S (ConjT.Aη S (cdEta S l)) (upsilon l), t < lsG S (k + 1) ∧
      S.psi (ConjT.Aη S (cdEta S l) + ζ) (Om 1) ≤ cdTheta S l t

theorem lsCoverMem_of_cover {l : Ordinal.{0}} {k : ℕ} (h : LsCover S l k) : LsCoverMem S l k :=
  fun ζ _ hζ => h ζ hζ

/-- The two facts on `β = Θ_λ(G_{k+1})` that the covering needs: strongly critical, above `ρ_λ`. -/
theorem lsBeta {l : Ordinal.{0}} (hpv : Nm.Pv S (cdEta S l) = upsilon l) (k : ℕ) :
    SC (cdTheta S l (lsG S (k + 1))) ∧ upsilon l < cdTheta S l (lsG S (k + 1)) := by
  unfold cdTheta cdHull
  exact ⟨lsOtp_SC hpv (lsG_SC _) (lsG_Om1 _) (lsG_Om2 _), lsOtp_gt hpv (lsG_Om1 _) (lsG_Om2 _)⟩

theorem lsCover_step {l : Ordinal.{0}} (hpv : Nm.Pv S (cdEta S l) = upsilon l) {k : ℕ} {v : Ordinal.{0}}
    (h : v ≤ upsilon l ∨ ∃ t ∈ lsAt S (ConjT.Aη S (cdEta S l)) (upsilon l), t < lsG S (k + 1) ∧
      v ≤ cdTheta S l t) : v < cdTheta S l (lsG S (k + 1)) := by
  rcases h with h | ⟨t, ht, htG, hv⟩
  · exact h.trans_lt (lsBeta hpv k).2
  · refine hv.trans_lt ?_
    unfold cdTheta cdHull
    exact lsOtp_atom_lt ht htG

/-- **`LsCover → LC-STRICT`.** -/
theorem lsStrict_of_cover {l : Ordinal.{0}} {k : ℕ} (hpv : Nm.Pv S (cdEta S l) = upsilon l)
    (h : LsCover S l k) : Lc.LcStrictAt S l k := by
  unfold Lc.LcStrictAt
  rw [lsH_G]
  obtain ⟨hβ, hρβ⟩ := lsBeta hpv k
  refine lsPsi_le hβ (by rw [← hpv] at hρβ; exact hρβ) fun ζ hζ => lsCover_step hpv (h ζ hζ)

/-- **`LsCoverMem → LC-STRICT`**, given `ω^{G_k} ∣ A_{η_λ}`. -/
theorem lsStrict_of_coverMem {l : Ordinal.{0}} {k : ℕ} (hpv : Nm.Pv S (cdEta S l) = upsilon l)
    (hdiv : ω ^ lsG S k ∣ ConjT.Aη S (cdEta S l)) (h : LsCoverMem S l k) : Lc.LcStrictAt S l k := by
  unfold Lc.LcStrictAt
  rw [lsH_G]
  obtain ⟨hβ, hρβ⟩ := lsBeta hpv k
  refine lsPsi_le_mem hβ (by rw [← hpv] at hρβ; exact hρβ) hdiv
    (right_le_opow _ one_lt_omega0) fun ζ hζC hζ => lsCover_step hpv (h ζ hζC hζ)

/-- **`LC-STRICT ↔ LsCoverMem`**, given `A_{η_λ}` own and `ω^{G_k} ∣ A_{η_λ}`. -/
theorem lsStrict_iff {l : Ordinal.{0}} {k : ℕ} (hpv : Nm.Pv S (cdEta S l) = upsilon l)
    (hown : ConjT.Aη S (cdEta S l) ∈ S.CSet (ConjT.Aη S (cdEta S l)) (Nm.Pv S (cdEta S l)))
    (hdiv : ω ^ lsG S k ∣ ConjT.Aη S (cdEta S l)) : Lc.LcStrictAt S l k ↔ LsCoverMem S l k := by
  refine ⟨fun hs => ?_, lsStrict_of_coverMem hpv hdiv⟩
  set A := ConjT.Aη S (cdEta S l) with hA
  set β := cdTheta S l (lsG S (k + 1)) with hβdef
  have hs' : S.psi (A + lsG S k) (Om 1) ≤ β := by
    have := hs; unfold Lc.LcStrictAt at this; rwa [lsH_G] at this
  intro ζ hζC hζ
  have hvlt : S.psi (A + ζ) (Om 1) < β := by
    rcases hs'.lt_or_eq with hlt | heq
    · exact ((psi_mono (S := S) Low.InR_Om_one
        ((add_lt_add_iff_left A).2 hζ).le).1).trans_lt hlt
    · have hm : A + ζ ∈ S.CSet (A + lsG S k) (S.psi (A + lsG S k) (Om 1)) := by
        refine CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hown) ?_
        rw [heq]; exact hζC
      rw [← heq]
      exact psi_lt_psi_of_mem Low.InR_Om_one ((add_lt_add_iff_left A).2 hζ) hm
  by_contra hno
  push Not at hno
  obtain ⟨h1, h2⟩ := hno
  have hle : β ≤ S.psi (A + ζ) (Om 1) := by
    rw [hβdef]
    unfold cdTheta cdHull
    refine lsOtp_least hpv (lsG_Om2 _) (SC_psi Low.InR_Om_one _) h1 fun t ht htG => ?_
    exact h2 t ht htG
  exact absurd hvlt (not_lt.2 hle)

end Googology.Trans.PoR.InaccPsi.R2.Ls

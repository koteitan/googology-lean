import Googology.Trans.PoR.InaccPsi.R2.UqHi

/-!
# Every `W`-fixed limit in `[Γ₂, Y₃)` except the `ψ₃`-atoms has a member system; the level statement below `ψ₃(1)`

`Θ = gxTh ρ_λ (ldAtR λ)`, `T = Ug.ugTh`, `H_λ = cdHull S λ`, `CL₃ = Ug.UgCL`, `F_u = φ(Ω₂, u)`,
`Γ₂ = Ua.uaGam = ψ₃(0)`, `ψ₃ = ψ_{Ω₃}`, `Y₃ = ψ_{Ω₃}(Ω₃)`, member systems `Uq.UqMA`, `Uq.UqMB`.

A `W`-fixed `r ∈ (Γ₂, Y₃)` of `H_λ` is a `ψ₃`-atom `ψ₃(d)` (`d ∈ H_λ`, `d < ψ₃(d)`, `Ug.ugAtomH`) or a node
`φ(a, y)` with `a, y < r` (`Ug.ugNode`).

* `uqNodeAll` (**EVERY NODE `φ(a, y) ∈ (Γ₂, Y₃)` OF `H_λ` HAS A MEMBER SYSTEM**, given those of the smaller limits:
  a code level in its window `(F_u, F_{u+1})`, `Γ₂ ≤ u`, by `Uq.uqNodeMS`, the level `Ω₂` by `Uq.uqNodeW`, a level
  `a > Ω₂` by `Uq.uqNodeHi`);
* `UqAtomMS` (**the member systems at the `ψ₃`-atoms `ψ₃(d)`, `1 ≤ d`, below `B`**, given those of the smaller
  limits), `uqFix_of_atoms` (**`UqAtomMS S λ B` gives `UqFixMS S λ B`**: `Γ₂` by the members `X_k`, the nodes by
  `uqNodeAll`);
* `uqAtom_one` (`UqAtomMS S λ ψ₃(1)` holds: no atom `ψ₃(d)`, `d ≥ 1`, is below `ψ₃(1)`), `uqLevPsi1`
  (**UNCONDITIONAL: `UjLev (CL₃ E) E (T E)` AT EVERY LEVEL `Ω₂ ≤ E < ψ_{Ω₃}(1)` OF `H_λ`**), `uqLevAtoms`
  (**every `Ω₂ ≤ E < Y₃` of `H_λ`, given `UqAtomMS S λ Y₃`**).

No new axiom.  New definition: `UqAtomMS`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Uq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Ta
  Googology.Trans.PoR.InaccPsi.R2.Tx Googology.Trans.PoR.InaccPsi.R2.Ua Googology.Trans.PoR.InaccPsi.R2.Ud
  Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj

variable {S : InaccSeq.{0}}

/-- **The member systems at the `ψ₃`-atoms `ψ₃(d)` (`1 ≤ d`, `d < ψ₃(d)`) below `B`**, given those of the smaller
limits of `H_λ`. -/
def UqAtomMS (S : InaccSeq.{0}) (l B : Ordinal.{0}) : Prop :=
  ∀ d, d ∈ cdHull S l → 1 ≤ d → d < S.psi d (Om (1 + 1 + 1)) → S.psi d (Om (1 + 1 + 1)) < B →
    (∀ r', r' ∈ cdHull S l → IsSuccLimit r' → r' < S.psi d (Om (1 + 1 + 1)) → UqMA S l r' ∨ UqMB S l r') →
    UqMA S l (S.psi d (Om (1 + 1 + 1))) ∨ UqMB S l (S.psi d (Om (1 + 1 + 1)))

/-- `ψ₃(1) < Y₃`. -/
theorem uqPsi1_lt_Y : S.psi 1 (Om (1 + 1 + 1)) < ugY S :=
  psi_lt_psi_of_mem (InR_Om_succ (1 + 1)) (gg_one_lt_of_SC (SC_Om (by
    rw [one_add_one_eq_two, ← Nat.cast_ofNat]; exact (by norm_num : ((2 : ℕ) : Ordinal.{0}) + 1 ≠ 0))))
    (CSet.one_mem _ _)

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **EVERY NODE `φ(a, y) ∈ (Γ₂, Y₃)` OF `H_λ` HAS A MEMBER SYSTEM**, given those of the smaller limits. -/
theorem uqNodeAll {r : Ordinal.{0}} (hrH : r ∈ cdHull S l) (hGr : uaGam < r) (hrY : r < ugY S)
    (hrs : ¬ sgLW r < r) (hS : ¬ SC r)
    (IH : ∀ r', r' ∈ cdHull S l → IsSuccLimit r' → r' < r → UqMA S l r' ∨ UqMB S l r') :
    UqMA S l r ∨ UqMB S l r := by
  obtain ⟨-, hv, ha0, haE, hbE, -, -⟩ := ugNode hGr.le hS hrs
  set a := invVeblen₁ r with ha_def
  set y := invVeblen₂ r with hy_def
  have hmem := mem_of_veblen_mem (by rw [hv]; exact hrH) (by rw [hv]; exact haE) (by rw [hv]; exact hbE)
  have hFG : veblen (Om (1 + 1)) uaGam = uaGam := uaGam_spec.1.veblen_right uaGam_spec.2
  rcases lt_trichotomy a (Om (1 + 1)) with haW | haW | haW
  · -- a code level: the window of `r`
    have hΩr : veblen (Om (1 + 1)) 0 ≤ r := by
      rw [ldOm2_SC.veblen_zero]; exact (uaGam_spec.2.trans hGr).le
    obtain ⟨u, huH, hu1', hu2'⟩ := txHull_idx hrH hΩr
    have hne : veblen (Om (1 + 1)) u ≠ r := by
      intro he
      have hfix : veblen a r = r := by rw [← he]; exact veblen_veblen_of_lt haW _
      have : y = r := by
        have h2 : veblen a y = veblen a r := by rw [hv, hfix]
        exact veblen_injective a h2
      exact absurd (this ▸ hbE) (lt_irrefl _)
    have hGu : uaGam ≤ u := by
      by_contra hc
      push Not at hc
      have h1 : veblen (Om (1 + 1)) (u + 1) ≤ veblen (Om (1 + 1)) uaGam :=
        (veblen_le_veblen_iff_right).2 (Order.add_one_le_of_lt hc)
      rw [hFG] at h1
      exact absurd (hu2'.trans_le h1) (not_lt.2 hGr.le)
    have h := uqNodeMS hl hX hGu huH hmem.1 (Order.one_le_iff_pos.2 ha0) haW hmem.2
      (by rw [hv]; exact lt_of_le_of_ne hu1' hne) (by rw [hv]; exact hu2') (by rw [hv]; exact hrY)
      (fun hyl => IH _ hmem.2 hyl hbE)
    rwa [hv] at h
  · -- the level `Ω₂`
    have hGy : uaGam < y := by
      rw [← hv, haW, ← hFG] at hGr
      exact (veblen_lt_veblen_iff_right).1 hGr
    have h := uqNodeW hl hX hmem.2 hGy (by rw [← haW, hv]; exact hrY) (fun hyl => IH _ hmem.2 hyl hbE)
    rwa [← haW, hv] at h
  · -- a level above `Ω₂`
    have h := uqNodeHi hl hX hmem.1 hmem.2 haW (by rw [hv]; exact hbE) (by rw [hv]; exact hrY)
      (fun hal => IH _ hmem.1 hal haE) (fun hyl => IH _ hmem.2 hyl hbE)
    rwa [hv] at h

/-- **`UqAtomMS S λ B` gives `UqFixMS S λ B`** (`B ≤ Y₃`). -/
theorem uqFix_of_atoms {B : Ordinal.{0}} (hA : UqAtomMS S l B) (hB : B ≤ ugY S) : UqFixMS S l B := by
  intro r hrH hGr hrB hrs IH
  rcases hGr.lt_or_eq with hlt | heq
  swap
  · rw [← heq]; exact Or.inl (uqMA_gam hl hX)
  have hrY : r < ugY S := hrB.trans_le hB
  by_cases hS : SC r
  · obtain ⟨d, hdH, hd, -, hdr⟩ := ugAtomH hl hX hrH hS (uaGam_spec.2.trans hlt) hrY
    have hd1 : 1 ≤ d := by
      rw [Order.one_le_iff_ne_zero]
      rintro rfl
      rw [← udGam_eq] at hdr
      exact absurd hdr (ne_of_lt hlt)
    rw [← hdr] at hrB IH ⊢
    exact hA d hdH hd1 hd hrB IH
  · exact uqNodeAll hl hX hrH hlt hrY hrs hS IH

omit hl hX in
/-- **`UqAtomMS S λ ψ₃(1)` holds**: no atom `ψ₃(d)` with `1 ≤ d` lies below `ψ₃(1)`. -/
theorem uqAtom_one : UqAtomMS S l (S.psi 1 (Om (1 + 1 + 1))) := by
  intro d _ hd1 _ hlt _
  exact absurd hlt (not_lt.2 (psi_mono (S := S) (InR_Om_succ (1 + 1)) hd1).1)

/-- **UNCONDITIONAL: THE LEVEL STATEMENT PAST `Γ₂` AT EVERY LEVEL `Ω₂ ≤ E < ψ_{Ω₃}(1)` OF `H_λ`** (image `T E`, own
predicate `CL₃ E`). -/
theorem uqLevPsi1 {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hWE : Om (1 + 1) ≤ E)
    (hE : E < S.psi 1 (Om (1 + 1 + 1))) :
    UjOwP S l (UgCL S E) E (ugTh S l E) ∧ UjLev S l (UgCL S E) E (ugTh S l E) :=
  uqLevB hl hX (uqFix_of_atoms hl hX uqAtom_one uqPsi1_lt_Y.le) uqPsi1_lt_Y.le
    (SC_psi (InR_Om_succ (1 + 1)) 1).isSuccLimit hEH hWE hE

/-- **THE LEVEL STATEMENT PAST `Γ₂` AT EVERY LEVEL `Ω₂ ≤ E < Y₃` OF `H_λ`**, given the member systems at the
`ψ₃`-atoms `ψ₃(d)`, `1 ≤ d` (`UqAtomMS S λ Y₃`). -/
theorem uqLevAtoms (hA : UqAtomMS S l (ugY S)) {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hWE : Om (1 + 1) ≤ E)
    (hE : E < ugY S) :
    UjOwP S l (UgCL S E) E (ugTh S l E) ∧ UjLev S l (UgCL S E) E (ugTh S l E) :=
  uqLevAll hl hX (uqFix_of_atoms hl hX hA le_rfl) hEH hWE hE

end Main

end Googology.Trans.PoR.InaccPsi.R2.Uq

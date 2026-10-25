import Googology.Trans.PoR.InaccPsi.R2.UgWall

/-!
# `B_n` on the atoms `ψ_{Ω_{s+1}}(α)` for every finite level `s ≥ 1`, and the atom step of the move of the image

`B_n = Bc.bcB S n`, `σ = bcSig (bcPre (n+1)) bcPreW` (`B_n = val ∘ σ ∘ nf`), `ψ₂ = ψ_{Ω₂}`, `ψ₃ = ψ_{Ω₃}`,
`T = Ug.ugTh S λ`, `Y₃ = ψ₃(Ω₃)`, `H_λ = cdHull S λ`.

* `ugNf_psiS` (**the normal form of `ψ_{Ω_{s+1}}(α)`, `s ≠ 0`, `α` own for `ψ_{Ω_{s+1}}`, is `ψ^S_t(a)` with `|t| = s`,
  `|a| = α`**; `Mx.mxNf_psi2` is `s = 1`);
* `ugB_psiS` (**`B_n(ψ_{Ω_{s+1}}(α)) = ψ_{Ω_{B_n s + 1}}(B_n α)`** for `s ≠ 0` and `α` in the domain of `B_n`, `α` own;
  **GENERIC IN THE LEVEL `s`**), `ugB_own` (`B_n α` is again own), `ugB_fix` (`B_n s = s` gives
  `B_n(ψ_{Ω_{s+1}}(α)) = ψ_{Ω_{s+1}}(B_n α)`), `ugB_two` (`B_n 2 = 2`), `ugB_psi3` (**`B_n(ψ₃(α)) = ψ₃(B_n α)`**);
* `ugB_atomStep` (**THE ATOM STEP OF THE MOVE OF `T`**: if `T_{λ'}(B_n d) = B_n(T_λ d)` at the argument `d` of a
  `ψ₃`-atom, then `T_{λ'}(B_n ψ₃(d)) = B_n(T_λ ψ₃(d))`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ug

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Bc Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Ua

variable {S : InaccSeq.{0}}

/-- An ordinal strictly between `Ω_s` and `Ω_{s+1}` is not a fixed point of `Ω`. -/
theorem ugNotOmFix {s z : Ordinal.{0}} (h1 : Om s < z) (h2 : z < Om (s + 1)) : Om z ≠ z :=
  fun h => not_Om_of_between h1 h2 z h.symm

/-- **The normal form of `ψ_{Ω_{s+1}}(α)`** (`s ≠ 0`, `α ∈ Cl(α, ψ_{Ω_{s+1}}(α))`) is `ψ^S_t(a)` with `|t| = s`,
`|a| = α`. -/
theorem ugNf_psiS {s α : Ordinal.{0}} (hown : α ∈ S.CSet α (S.psi α (Om (s + 1)))) {t : Term} (ht : NF t)
    (hv : val S t = S.psi α (Om (s + 1))) : ∃ u a, t = psiS u a ∧ val S u = s ∧ val S a = α := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  have hSC : SC (val S t) := hv ▸ SC_psi hκ α
  have hb := psiS_bounds (S := S) α s
  rw [← hv] at hb
  have hsc := isSC_of_SC (S := S) ht hSC
  cases t with
  | psiS u a =>
    have hbs := val_psiS_bounds S u a
    have hvs : val S u = s := between_unique hbs.1 hbs.2 hb.1 hb.2
    refine ⟨u, a, rfl, hvs, ?_⟩
    have h : Sem S (psiS u a) := sem_of_NF ht
    have hsem := h.2.2
    rw [hvs] at hsem
    have hc := compare_psi hκ hsem hown
    have hv' : S.psi (val S a) (Om (s + 1)) = S.psi α (Om (s + 1)) := by
      have := hv; simp only [val, hvs] at this; exact this
    rw [hv', compare_eq_iff_eq.2 rfl] at hc
    exact compare_eq_iff_eq.1 hc.symm
  | om a =>
    exfalso
    exact not_Om_of_between hb.1 hb.2 (val S a) rfl
  | psiI n a =>
    exfalso
    exact ugNotOmFix hb.1 hb.2 (val_psiI_bounds S n a).1
  | inacc n =>
    exfalso
    exact ugNotOmFix hb.1 hb.2 (Om_I (S := S) n)
  | inaccW =>
    exfalso
    exact ugNotOmFix hb.1 hb.2 (S.Om_Iw)
  | zero => exact absurd hsc (by simp [isSC])
  | add _ _ => exact absurd hsc (by simp [isSC])
  | phi _ _ => exact absurd hsc (by simp [isSC])

theorem ugPsiS_mem {s α : Ordinal.{0}} (hs : s ∈ ⋃ a, S.CSet a 0) (hα : α ∈ ⋃ a, S.CSet a 0) :
    S.psi α (Om (s + 1)) ∈ ⋃ a, S.CSet a 0 := by
  obtain ⟨c, hc⟩ := Set.mem_iUnion.1 hα
  obtain ⟨c', hc'⟩ := Set.mem_iUnion.1 hs
  refine Set.mem_iUnion.2 ⟨max (max c c') (α + 1), ?_⟩
  exact CSet.psi_mem ((lt_add_one α).trans_le (le_max_right _ _)) (InR_Om_succ s)
    (CSet.Om_mem (CSet.succ_mem (CSet_mono ((le_max_right c c').trans (le_max_left _ _)) le_rfl hc')))
    (CSet_mono ((le_max_left c c').trans (le_max_left _ _)) le_rfl hc)

/-- **`B_n(ψ_{Ω_{s+1}}(α)) = ψ_{Ω_{B_n s + 1}}(B_n α)`** (`s ≠ 0`, `s, α` in the domain of `B_n`, `α` own), with
`ψ_{Ω_{s+1}}(α)` in the domain and `B_n α` own for `ψ_{Ω_{B_n s+1}}`: **GENERIC IN THE LEVEL**. -/
theorem ugB_psiS {n : ℕ} {s α : Ordinal.{0}} (hs0 : s ≠ 0) (hDs : MvD S s) (hDα : MvD S α)
    (hown : α ∈ S.CSet α (S.psi α (Om (s + 1)))) :
    MvD S (S.psi α (Om (s + 1))) ∧
      Bc.bcB S n (S.psi α (Om (s + 1))) = S.psi (Bc.bcB S n α) (Om (Bc.bcB S n s + 1)) ∧
      Bc.bcB S n α ∈ S.CSet (Bc.bcB S n α) (S.psi (Bc.bcB S n α) (Om (Bc.bcB S n s + 1))) := by
  have hmem := ugPsiS_mem hDs.1 hDα.1
  obtain ⟨hN, hv⟩ := Bc.bcNf_spec S hmem
  obtain ⟨u, a, ht, hvu, hva⟩ := ugNf_psiS hown hN hv
  have hNu : NF u := by rw [ht] at hN; exact hN.1
  have hNa : NF a := by rw [ht] at hN; exact hN.2.1
  have hu : Bc.bcNf S s = u := by rw [← hvu]; exact Bc.bcNf_val S hNu
  have ha : Bc.bcNf S α = a := by rw [← hva]; exact Bc.bcNf_val S hNa
  have hu0 : u ≠ Term.zero := by
    rintro rfl; exact hs0 (by rw [← hvu]; rfl)
  have hDu : bcD S u := hu ▸ hDs.2
  have hDa : bcD S a := ha ▸ hDα.2
  have hDt : bcD S (psiS u a) := ⟨ht ▸ hN, hDu.2, hDa.2, fun h => absurd h hu0⟩
  have hBu : Bc.bcB S n s = val S (bcSig (bcPre (n + 1)) bcPreW u) := by rw [← hvu]; exact mvB_term hDu
  have hBa : Bc.bcB S n α = val S (bcSig (bcPre (n + 1)) bcPreW a) := by rw [← hva]; exact mvB_term hDa
  have hBt : Bc.bcB S n (S.psi α (Om (s + 1))) = val S (bcSig (bcPre (n + 1)) bcPreW (psiS u a)) := by
    unfold Bc.bcB; rw [ht]
  have hσ : bcSig (bcPre (n + 1)) bcPreW (psiS u a) =
      psiS (bcSig (bcPre (n + 1)) bcPreW u) (bcSig (bcPre (n + 1)) bcPreW a) := bcSig_psiS_ne hu0 a
  refine ⟨⟨hmem, ht ▸ hDt⟩, ?_, ?_⟩
  · rw [hBt, hσ, hBu, hBa]; rfl
  · have hσN : NF (bcSig (bcPre (n + 1)) bcPreW (psiS u a)) := bc_NF (k := n) hDt
    have hsem : Sem S (bcSig (bcPre (n + 1)) bcPreW (psiS u a)) := sem_of_NF hσN
    rw [hσ] at hsem
    rw [hBu, hBa]; exact hsem.2.2

/-- **`B_n s = s` gives `B_n(ψ_{Ω_{s+1}}(α)) = ψ_{Ω_{s+1}}(B_n α)`** with `B_n α` own. -/
theorem ugB_fix {n : ℕ} {s α : Ordinal.{0}} (hs0 : s ≠ 0) (hDs : MvD S s) (hBs : Bc.bcB S n s = s)
    (hDα : MvD S α) (hown : α ∈ S.CSet α (S.psi α (Om (s + 1)))) :
    MvD S (S.psi α (Om (s + 1))) ∧
      Bc.bcB S n (S.psi α (Om (s + 1))) = S.psi (Bc.bcB S n α) (Om (s + 1)) ∧
      Bc.bcB S n α ∈ S.CSet (Bc.bcB S n α) (S.psi (Bc.bcB S n α) (Om (s + 1))) := by
  have h := ugB_psiS (n := n) hs0 hDs hDα hown
  rw [hBs] at h
  exact h

/-- **`B_n 2 = 2`**, `2 = 1 + 1` in the domain. -/
theorem ugB_two (n : ℕ) : MvD S (1 + 1 : Ordinal.{0}) ∧ Bc.bcB S n (1 + 1 : Ordinal.{0}) = 1 + 1 := by
  have h1 := Rk.rk_one_D (S := S)
  obtain ⟨hD, hB⟩ := mvB_add (k := n) h1 h1
  rw [mwB_one] at hB
  exact ⟨hD, hB⟩

/-- **`B_n(ψ₃(α)) = ψ₃(B_n α)`** for `α` in the domain, own for `ψ₃`; `B_n α` is own for `ψ₃`. -/
theorem ugB_psi3 {n : ℕ} {α : Ordinal.{0}} (hDα : MvD S α)
    (hown : α ∈ S.CSet α (S.psi α (Om (1 + 1 + 1)))) :
    MvD S (S.psi α (Om (1 + 1 + 1))) ∧
      Bc.bcB S n (S.psi α (Om (1 + 1 + 1))) = S.psi (Bc.bcB S n α) (Om (1 + 1 + 1)) ∧
      Bc.bcB S n α ∈ S.CSet (Bc.bcB S n α) (S.psi (Bc.bcB S n α) (Om (1 + 1 + 1))) := by
  obtain ⟨hD2, hB2⟩ := ugB_two (S := S) n
  have h20 : (1 + 1 : Ordinal.{0}) ≠ 0 := by rw [one_add_one_eq_two]; exact two_ne_zero
  exact ugB_fix h20 hD2 hB2 hDα hown

/-- **`B_n(ψ₂(α)) = ψ₂(B_n α)`** with `B_n α` own for `ψ₂` (`Mx.mxB_atom` with the ownness of the image). -/
theorem ugB_psi2 {n : ℕ} {α : Ordinal.{0}} (hDα : MvD S α)
    (hown : α ∈ S.CSet α (S.psi α (Om (1 + 1)))) :
    MvD S (S.psi α (Om (1 + 1))) ∧
      Bc.bcB S n (S.psi α (Om (1 + 1))) = S.psi (Bc.bcB S n α) (Om (1 + 1)) ∧
      Bc.bcB S n α ∈ S.CSet (Bc.bcB S n α) (S.psi (Bc.bcB S n α) (Om (1 + 1))) := by
  have h1 := Rk.rk_one_D (S := S)
  exact ugB_fix one_ne_zero h1 (mwB_one n) hDα hown

section Move

variable {n : ℕ} {l l' ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **THE ATOM STEP OF THE MOVE OF `T`**: at a `ψ₃`-atom `ψ₃(d)` of `H_λ ∩ Y₃` with `d` and `T_λ d` in the domain of
`B_n`, `B_n d ∈ H_{λ'}`, `B_n ψ₃(d) < Y₃` and the move `T_{λ'}(B_n d) = B_n(T_λ d)` at the argument, the atom moves:
`T_{λ'}(B_n ψ₃(d)) = B_n(T_λ ψ₃(d))`. -/
theorem ugB_atomStep {d : Ordinal.{0}} (hdH : d ∈ cdHull S l) (hd : d < S.psi d (Om (1 + 1 + 1)))
    (hY : S.psi d (Om (1 + 1 + 1)) < ugY S) (hDd : MvD S d) (hDT : MvD S (ugTh S l d))
    (hBdH : Bc.bcB S n d ∈ cdHull S l')
    (hBY : Bc.bcB S n (S.psi d (Om (1 + 1 + 1))) < ugY S)
    (hmv : ugTh S l' (Bc.bcB S n d) = Bc.bcB S n (ugTh S l d)) :
    ugTh S l' (Bc.bcB S n (S.psi d (Om (1 + 1 + 1)))) = Bc.bcB S n (ugTh S l (S.psi d (Om (1 + 1 + 1)))) := by
  have hown : d ∈ S.CSet d (S.psi d (Om (1 + 1 + 1))) := CSet.of_lt hd
  obtain ⟨-, hB3, hBown⟩ := ugB_psi3 (n := n) hDd hown
  have hBd : Bc.bcB S n d < S.psi (Bc.bcB S n d) (Om (1 + 1 + 1)) := by
    refine lt_psi_of_mem ugInR3 hBown ?_
    by_contra hc
    have h := hBY
    rw [hB3] at h
    exact absurd ((psi_mono (S := S) ugInR3 (not_lt.1 hc)).1) (not_le.2 h)
  have hT := (ugNormAll hl hX hdH (hd.trans hY)).1
  obtain ⟨-, hB2, -⟩ := ugB_psi2 (n := n) hDT hT
  rw [hB3, ugTh_atom hBd, hmv, ugTh_atom hd, hB2]

end Move

end Googology.Trans.PoR.InaccPsi.R2.Ug

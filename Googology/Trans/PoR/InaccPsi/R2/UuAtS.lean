import Googology.Trans.PoR.InaccPsi.R2.UuCode

/-!
# The member systems at a successor `ψ₃`-atom `ψ₃(d + 1)`

`T = Ug.ugTh`, `H_λ = cdHull S λ`, `C_2(Q) = Ug.UgC S 2 Q`, `ψ_k = ψ_{Ω_k}`, `f(a) = φ(a, 0)`, `Y₃ = ψ₃(Ω₃)`,
`P = ψ₃(d)`, `X'_k = f^{k+1}(P + 1)`.

At `d + 1 < ψ₃(d + 1) < Y₃` the argument `d` is normal (`Uu.uuLt3`), so `ψ₃(d + 1) = nfp f (P + 1)` is the least
strongly critical ordinal above `P` (`Uu.uuSucc_eq`, generalizing `Ud.udGam_nfp`), and its image
`T(ψ₃(d + 1)) = ψ₂(T d + 1) ≤ nfp f (ψ₂(T d) + 1)` (`Uu.uuSucc_le`, generalizing `Ug.ugG1_le_nfp`).

* `uuIt3` (`P < X'_k < ψ₃(d + 1)`, `X'_k ∈ H_λ`), `uuThIt3` (**`T(f^k(P + 1)) = f^k(ψ₂(T d) + 1)`**);
* `uuCodeP3` (**THE OWN TRANSFER**: a `C_2(Q)` code `h` in `[X'_k, ψ₃(d + 1)]` with `Q ≤ P` contains an atom
  `ψ₃(e)`, `d ≤ e ≤ d + 1`, so `P` is a code; `Uu.uuC_atom`);
* `uuMA_succ` (**`UqMA` AT EVERY SUCCESSOR ATOM `ψ₃(d + 1) < Y₃` OF `H_λ`**: members `X'_k`, images
  `f^{k+1}(ψ₂(T d) + 1)`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Uu

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Ua Googology.Trans.PoR.InaccPsi.R2.Ud
  Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uq

variable {S : InaccSeq.{0}}

/-- An ordinal below `Y₃` is below `A_η` (so `ψ₃` of a hull element below `Y₃` is in the hull). -/
theorem uuLtA {l x : Ordinal.{0}} (hx : x < ugY S) : x < ConjT.Aη S (cdEta S l) :=
  (hx.trans ugY_lt_Om3).trans (Ry.ryOm3_lt.trans_le (ConjT.OmW_le_A S _))

/-- `ψ₃(x) ∈ H_λ` for `x ∈ H_λ`, `x < Y₃`. -/
theorem uuPsi3_mem {l x : Ordinal.{0}} (hxH : x ∈ cdHull S l) (hx : x < ugY S) :
    S.psi x (Om (1 + 1 + 1)) ∈ cdHull S l :=
  CSet.psi_mem (uuLtA hx) ugInR3 (Ry.ryOm3_mem _ _) hxH

/-- The iterates `f^k(P + 1)` over a strongly critical `P` below a strongly critical `E`. -/
theorem uuIt_SC {P E : Ordinal.{0}} (hE : SC E) (hPE : P < E) :
    ∀ k : ℕ, P < (fun a : Ordinal.{0} => veblen a 0)^[k] (P + 1) ∧
      (fun a : Ordinal.{0} => veblen a 0)^[k] (P + 1) < E := by
  intro k
  induction k with
  | zero => exact ⟨lt_add_one P, hE.add_one_lt hPE⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨ih.1.trans_le (left_le_veblen _ _), hE.2 _ ih.2 _ hE.1⟩

/-- The iterates `f^k(P + 1)` are in every closure containing `P`. -/
theorem uuIt_mem {a b P : Ordinal.{0}} (hP : P ∈ S.CSet a b) :
    ∀ k : ℕ, (fun a : Ordinal.{0} => veblen a 0)^[k] (P + 1) ∈ S.CSet a b := by
  intro k
  induction k with
  | zero => exact CSet.succ_mem hP
  | succ k ih => rw [Function.iterate_succ_apply']; exact CSet.phi_mem ih (CSet.zero_mem _ _)

/-- The iterates `f^k(P + 1)` are codes when `P` is. -/
theorem uuIt_code {k Q P : Ordinal.{0}} (hQ : SC Q) (hP : UgC S k Q P) :
    ∀ n : ℕ, UgC S k Q ((fun a : Ordinal.{0} => veblen a 0)^[n] (P + 1)) := by
  intro n
  induction n with
  | zero => exact UgC.add hP (UgC.small (gg_one_lt_of_SC hQ))
  | succ n ih => rw [Function.iterate_succ_apply']; exact UgC.phi ih (UgC.zero hQ.1)

/-- **THE OWN TRANSFER AT A SUCCESSOR ATOM**: if a `C_2(Q)` code `h` satisfies `P < h ≤ ψ₃(d + 1)` with `Q ≤ P`
(`P = ψ₃(d)`, `d + 1 < ψ₃(d + 1)`, `d < Y₃`), then `P` is a code. -/
theorem uuCodeP3 {d Q h : Ordinal.{0}} (hQ : SC Q) (hd1 : d + 1 < S.psi (d + 1) (Om (1 + 1 + 1)))
    (hdY : d < ugY S) (hQP : Q ≤ S.psi d (Om (1 + 1 + 1))) (hPh : S.psi d (Om (1 + 1 + 1)) ≤ h)
    (hhE : h ≤ S.psi (d + 1) (Om (1 + 1 + 1))) (hh : UgC S (1 + 1) Q h) :
    UgC S (1 + 1) Q (S.psi d (Om (1 + 1 + 1))) := by
  have hdn : d < S.psi d (Om (1 + 1 + 1)) := uuLt3 hdY
  obtain ⟨e, hec, hel, hPe, heh⟩ :=
    uuC_atom h hh _ (SC_psi ugInR3 d) hQP (ugOm2_lt_psi3 d) hPh
  rcases hPe.lt_or_eq with hlt | heq
  · have hEe : S.psi (d + 1) (Om (1 + 1 + 1)) ≤ S.psi e (Om (1 + 1 + 1)) :=
      uuSucc_next uuThree_lt hdn (SC_psi ugInR3 e) hlt
    have heE : S.psi e (Om (1 + 1 + 1)) = S.psi (d + 1) (Om (1 + 1 + 1)) := le_antisymm (heh.trans hhE) hEe
    have hed : e = d + 1 := by
      have h1 := ugD_eq hel
      rw [heE, ugD_eq hd1] at h1
      exact h1.symm
    subst hed
    exact UgC.psi (uqC_pred hQ ugTwo_ne d hec) hdn
  · rw [heq]; exact UgC.psi hec hel

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **`T(f^k(ψ₃(d) + 1)) = f^k(ψ₂(T d) + 1)`.** -/
theorem uuThIt3 {d : Ordinal.{0}} (hdH : d ∈ cdHull S l) (hdn : d < S.psi d (Om (1 + 1 + 1)))
    {E : Ordinal.{0}} (hE : SC E) (hPE : S.psi d (Om (1 + 1 + 1)) < E) (hEY : E ≤ ugY S) :
    ∀ k : ℕ, ugTh S l ((fun a : Ordinal.{0} => veblen a 0)^[k] (S.psi d (Om (1 + 1 + 1)) + 1)) =
      (fun a : Ordinal.{0} => veblen a 0)^[k] (S.psi (ugTh S l d) (Om (1 + 1)) + 1) := by
  have hdY : d < ugY S := hdn.trans (hPE.trans_le hEY)
  have hPH := uuPsi3_mem hdH hdY
  have hIt := uuIt_SC hE hPE
  have h0H : (0 : Ordinal.{0}) ∈ cdHull S l := CSet.zero_mem _ _
  intro k
  induction k with
  | zero =>
    show ugTh S l (S.psi d (Om (1 + 1 + 1)) + 1) = S.psi (ugTh S l d) (Om (1 + 1)) + 1
    rw [ugSucc hl hX hPH ((hIt 0).2.trans_le hEY), ugTh_atom hdn]
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply' _ k (S.psi (ugTh S l d) (Om (1 + 1)) + 1)]
    have hlt := hIt (k + 1)
    rw [Function.iterate_succ_apply'] at hlt
    have ha0 : (fun a : Ordinal.{0} => veblen a 0)^[k] (S.psi d (Om (1 + 1 + 1)) + 1) ≠ 0 :=
      (zero_le.trans_lt (hIt k).1).ne'
    have hG : uaGam ≤ veblen ((fun a : Ordinal.{0} => veblen a 0)^[k] (S.psi d (Om (1 + 1 + 1)) + 1)) 0 :=
      (ugGam_le_psi3 d).trans hlt.1.le
    rw [ugVeb hl hX (uuIt_mem hPH k) h0H ha0 hG (hlt.2.trans_le hEY), ih, ugTh_zero]

/-- **`UqMA` AT EVERY SUCCESSOR ATOM `ψ₃(d + 1) < Y₃` OF `H_λ`**: the members `f^{k+1}(ψ₃(d) + 1)`. -/
theorem uuMA_succ {d : Ordinal.{0}} (hdH : d + 1 ∈ cdHull S l)
    (hd1 : d + 1 < S.psi (d + 1) (Om (1 + 1 + 1))) (hY : S.psi (d + 1) (Om (1 + 1 + 1)) < ugY S) :
    UqMA S l (S.psi (d + 1) (Om (1 + 1 + 1))) := by
  set P := S.psi d (Om (1 + 1 + 1)) with hP_def
  set E := S.psi (d + 1) (Om (1 + 1 + 1)) with hE_def
  have hd1Y : d + 1 < ugY S := hd1.trans hY
  have hdY : d < ugY S := (lt_add_one d).trans hd1Y
  have hdn : d < P := uuLt3 hdY
  have hd'H : d ∈ cdHull S l := mem_of_add_one_mem hdH
  have hPH : P ∈ cdHull S l := uuPsi3_mem hd'H hdY
  have hESC : SC E := SC_psi ugInR3 _
  have hEeq : E = nfp (fun a : Ordinal.{0} => veblen a 0) (P + 1) := uuSucc_eq uuThree_lt hdn
  have hPE : P < E := by
    rw [hEeq]; exact (lt_add_one P).trans_le (le_nfp _ _)
  have hIt := uuIt_SC hESC hPE
  have hTIt := uuThIt3 hl hX hd'H hdn hESC hPE hY.le
  refine ⟨fun m => ∃ k : ℕ, m = (fun a : Ordinal.{0} => veblen a 0)^[k + 1] (P + 1), ?_, ⟨_, 0, rfl⟩, ?_, ?_, ?_⟩
  · rintro m ⟨k, rfl⟩
    exact ⟨uuIt_mem hPH (k + 1), Order.one_le_iff_pos.2 (zero_le.trans_lt (hIt (k + 1)).1), (hIt (k + 1)).2⟩
  · intro y _ hy
    rw [hEeq] at hy
    obtain ⟨n, hn⟩ := lt_nfp_iff.1 hy
    refine ⟨_, ⟨n, rfl⟩, hn.trans_le ?_⟩
    rw [Function.iterate_succ_apply']; exact left_le_veblen _ _
  · intro z hz
    rw [ugTh_atom hd1, ugSucc hl hX hd'H hd1Y] at hz
    obtain ⟨n, hn⟩ := lt_nfp_iff.1 (hz.trans_le (uuSucc_le uuTwo_lt (ugTh S l d)))
    refine ⟨_, ⟨n, rfl⟩, ?_⟩
    rw [hTIt (n + 1), Function.iterate_succ_apply']
    exact hn.trans_le (left_le_veblen _ _)
  · rintro Q hQ m h ⟨k, rfl⟩ h1 h2 hh
    by_cases hmQ : (fun a : Ordinal.{0} => veblen a 0)^[k + 1] (P + 1) < Q
    · exact UgC.small hmQ
    push Not at hmQ
    have hQP : Q ≤ P := by
      by_contra hc
      push Not at hc
      have := uuSucc_next uuThree_lt hdn hQ hc
      exact absurd ((hmQ.trans_lt (hIt (k + 1)).2).trans_le this) (lt_irrefl _)
    have hPc := uuCodeP3 hQ hd1 hdY hQP ((hIt (k + 1)).1.le.trans h1) h2 hh
    exact uuIt_code hQ hPc (k + 1)

end Main

end Googology.Trans.PoR.InaccPsi.R2.Uu

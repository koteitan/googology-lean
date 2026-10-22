import Googology.Trans.PoR.InaccPsi.R2.RnK

/-!
# `Lj.LjAtMove` up to `ψ_{Ω₂}(Ω₂^{Ω₂}·k)` for every `k`, and the road with the atoms above them

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `θ = ψ_{Ω₂}(Ω_ω)`, `θ⁺ = Lj.ljThP`, `F_W = ψ_{Ω₂}(Ω₂^{Ω₂})`,
`β_k = Ω₂^{Ω₂}·k` (`Rn.rnBk`).

* `rnSetup` (the data of a range restart `λ` and its image `λ'` below `L(n+2)`: own `A`, `A'` with
  `ψ_{Ω₁}(A) = ρ_λ`, `ψ_{Ω₁}(A') = ρ_{λ'}`, `ψ_{Ω₁}(A + d) < c_{n+1}` and `B_n ψ_{Ω₁}(A + d) = ψ_{Ω₁}(A' + B_n d)` for
  own `A + d`, `d ≤ θ`; as in `Lj.ljThMove_P`);
* `RnAtMove S` (a hypothesis name): **`Lj.LjAtMove` for the atoms `s ≤ θ` above every `ψ_{Ω₂}(β_k)`**;
* `rnLjAtMove` (**`RnAtMove` gives `Lj.LjAtMove`**: an atom `F_W ≤ s ≤ ψ_{Ω₂}(β_k)` lies in
  `[ψ_{Ω₂}(β_j), ψ_{Ω₂}(β_{j+1})]` for some `j`, where it moves by `Rn.rnAtMove_k`);
* `rnRoadA` (**the road** of `Lj.ljRoadA` with `RnAtMove` in place of `LjAtMove`).

No new axiom.  New definition: the hypothesis name `RnAtMove`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Sf
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Lj

variable {S : InaccSeq.{0}}

/-- The data of a range restart `λ` with `r(λ) < c_{n+1}` and of its image `λ'`. -/
theorem rnSetup {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hB : Bc.bcB S n (upsilon l) = upsilon l') :
    ∃ A A' ηx ηx', upsilon l < Pv S ηx ∧ upsilon l' < Pv S ηx' ∧
      A ∈ S.CSet A (S.psi A (Om 1)) ∧ A' ∈ S.CSet A' (S.psi A' (Om 1)) ∧
      S.psi A (Om 1) = upsilon l ∧ S.psi A' (Om 1) = upsilon l' ∧
      (∀ d, d ≤ ConjT.th S → S.psi (A + d) (Om 1) < Bc.bcC S (n + 1)) ∧
      (∀ d, MvD S d → A + d ∈ S.CSet (A + d) (S.psi (A + d) (Om 1)) → d ≤ ConjT.th S →
        Bc.bcB S n (S.psi (A + d) (Om 1)) = S.psi (A' + Bc.bcB S n d) (Om 1)) := by
  have hl := hR.1
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans hδr
  have hX : upsilon l < Nm.Pv S (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0})) := by
    rw [← Lw.lw_L_eq S]; exact h2
  have hX' : upsilon l' < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq S, ← hB]; exact Bc.bcB_bound' S n _ h2
  obtain ⟨hg, -, -, hpv⟩ := cdEta_pv_spec (S := S) hl.1 hX
  set η := cdEta S l with hη_def
  set A := ConjT.Aη S η with hA_def
  have hρA : S.psi A (Om 1) = upsilon l := hpv
  have hAL : A < S.Lam := (sfA_lt (S := S) (n := n) (hpv ▸ h2)).2
  have hown : A ∈ S.CSet A (S.psi A (Om 1)) := sfOwn hg hAL
  have hu1 : upsilon (l + 1) < cdDelta l :=
    upsilon_normal.strictMono (by
      calc l + 1 < l + ω := (add_lt_add_iff_left l).2 one_lt_omega0
        _ < l + ω + 1 := lt_add_one _)
  have hsucc := mxUps_succ hl hX
  have hbX : ∀ d, d ≤ ConjT.th S → S.psi (A + d) (Om 1) < Bc.bcC S (n + 1) := by
    intro d hd
    have h3 : S.psi (A + d) (Om 1) ≤ upsilon (l + 1) := by
      rw [hsucc]; exact (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left A).2 hd)).1
    exact (h3.trans_lt hu1).trans hδr
  have hρ0 : (0 : Ordinal.{0}) < Pv S η := hpv ▸ mvUps_pos hl
  obtain ⟨A', hA', hBP, -⟩ := mxB_psi_add (n := n) hg (hpv ▸ h1.le) (by rw [add_zero]; exact hρ0)
    (by rw [add_zero]; show Pv S η < Bc.bcC S (n + 1); rw [hpv]; exact h2)
  have hρA' : S.psi A' (Om 1) = upsilon l' := by rw [← hBP, hpv, hB]
  have hBψ : ∀ d, MvD S d → A + d ∈ S.CSet (A + d) (S.psi (A + d) (Om 1)) → d ≤ ConjT.th S →
      Bc.bcB S n (S.psi (A + d) (Om 1)) = S.psi (A' + Bc.bcB S n d) (Om 1) := by
    intro d hDd hownd hdθ
    obtain ⟨A'', hA'', hBP'', hBd⟩ := ldB_psi_add (n := n) hg (hpv ▸ h1.le) hDd hownd (hbX d hdθ)
    have : A'' = A' := mxPsi_inj hA'' hA' (by rw [← hBP'', hBP])
    rw [hBd, this]
  exact ⟨A, A', _, _, hX, hX', hown, hA', hρA, hρA', hbX, hBψ⟩

/-- **`LjAtMove` for the atoms `s ≤ θ` above every `ψ_{Ω₂}(Ω₂^{Ω₂}·k)`.** -/
def RnAtMove (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    leFWW S ≤ cdCode S l → cdCode S l < ljThP S →
    ∀ s ∈ ldAtR S l, (∀ k : ℕ, S.psi (rnBk k) (Om (1 + 1)) < s) → s ≤ ConjT.th S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)

/-- **`RnAtMove` gives `LjAtMove`.** -/
theorem rnLjAtMove (h : RnAtMove S) : LjAtMove S := by
  intro n l l' hR h1 hr hl' hB hm hF hK s hs hsF hsθ IH
  by_cases hall : ∀ k : ℕ, S.psi (rnBk k) (Om (1 + 1)) < s
  · exact h n l l' hR h1 hr hl' hB hm hF hK s hs hall hsθ IH
  push Not at hall
  classical
  have hex : ∃ k : ℕ, s ≤ S.psi (rnBk k) (Om (1 + 1)) := hall
  set k0 := Nat.find hex with hk0
  have hk0s : s ≤ S.psi (rnBk k0) (Om (1 + 1)) := Nat.find_spec hex
  have h0F : S.psi (rnBk 0) (Om (1 + 1)) < leFWW S := by
    rw [rnBk_zero, ← rnFWW_eq, rnBk_one]
    exact psi_lt_psi_of_mem (InR_Om_succ 1) (leWe_pos _) (CSet.zero_mem _ _)
  obtain ⟨j, hj⟩ : ∃ j, k0 = j + 1 := by
    rcases Nat.exists_eq_succ_of_ne_zero (n := k0) (fun h0 => by
      rw [h0] at hk0s; exact absurd (hk0s.trans_lt h0F) (not_lt.2 hsF)) with ⟨j, hj⟩
    exact ⟨j, hj⟩
  have hjs : S.psi (rnBk j) (Om (1 + 1)) < s := by
    have := Nat.find_min hex (show j < k0 by omega)
    exact not_le.1 this
  rw [hj] at hk0s
  obtain ⟨A, A', ηx, ηx', hX, hX', hA, hA', hρ, hρ', hbX, hBψ⟩ := rnSetup hR h1 hr hB
  obtain ⟨hDs, hBs, hBle, hth, hEq⟩ := rnAtMove_k (n := n) hR.1 hl' hX hX' hA hA' hρ hρ' hbX hBψ j s hs
    hjs.le hk0s (fun x hx hxs => by
      obtain ⟨a1, a2, -, a4, a5⟩ := IH x hx hxs
      exact ⟨a1, a2, a4, a5⟩)
  exact ⟨hDs, hBs, hBle.trans_lt ((rnBk_lt_th (j + 1)).trans ljTh_lt_ThP), hth, hEq⟩

/-- **The road with `RnAtMove` and `LjEQhi`** (each under `L(ω+1) ≤ ν_C`). -/
theorem rnRoadA (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (hat : Nc.ncL S (ω + 1) ≤ nuC → RnAtMove S)
    (hhi : Nc.ncL S (ω + 1) ≤ nuC → LjEQhi S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  ljRoadA hU hO hL hV hN hlh (fun hν => rnLjAtMove (hat hν)) hhi

/-- **Satisfiability**: `LjAtMove` gives `RnAtMove`, so `rnRoadA` asks no more than `Lj.ljRoadA`. -/
theorem rnAtMove_of (h : LjAtMove S) : RnAtMove S :=
  fun n l l' hR h1 hr hl' hB hm hF hK s hs hall hsθ IH => by
    have hsF : leFWW S ≤ s := by rw [← rnFWW_eq]; exact (hall 1).le
    exact h n l l' hR h1 hr hl' hB hm hF hK s hs hsF hsθ IH

end Googology.Trans.PoR.InaccPsi.R2.Rn

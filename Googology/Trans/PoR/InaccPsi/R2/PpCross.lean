import Googology.Trans.PoR.InaccPsi.R2.PpRst
import Googology.Trans.PoR.InaccPsi.R2.NuRst

/-!
# CROSS-LIM at the points `L(ξ)`, condition (P) at `(L(ω), L(ω+1))`, and NU-NAME or `ν_C < L(ω)`

`P(η) = ψ_{Ω₁}(Ω_ω + θ·η)` (`Nm.Pv`), `P' = ψ_{Ω₂}(Ω_ω·2)`, `L(ξ) = P(Ω_ω + P'·ξ)`; so
`L(ξ+1) = P(Ω_ω + P'·ξ + P')` and the realizer points of CROSS-LIM above `L(ξ)` are `P(Ω_ω + P'·ξ + c)`,
`c < P'`.

* `ppCross_close` (**the closing step of CROSS-LIM**): for a limit `X`, if `a ≤₁ P(η + c')` for codes `c'`
  cofinal in `X`, then `a ≤₁ P(η + X)` (Lemma CONT: `P(η + X) = sup_{c<X} P(η + c)`, and `≤₁` is closed);
  `ppCross_L`: at `a = L(ξ)`, `η = Ω_ω + P'·ξ`, `X = P'`: realizers cofinal below `P'` give `L(ξ) ≤₁ L(ξ+1)`;
* `ppChain`, `ppTo_omega`: `L(n) ≤₁ L(n+1)` for every `n ≥ 1` gives `L(n) ≤₁ L(m)` (`n ≤ m`) and
  `L(n) ≤₁ L(ω)`;
* `ppP_of_cross` (**(P) from the CROSS-LIM relations**): `L(n) ≤₁ L(n+1)` (`n ≥ 1`) and `L(ω) ≤₁ L(ω+1)`
  give `L(n) ≤₁ L(ω+1)` for every `n ≥ 1` (the lower half of the reaches at the `L(n)`) and (P) at
  `(L(ω), L(ω+1))`;
* `ppUpper_P`, `ppUpper_cross`: `ncUpper_L` without its hypothesis "`L(ω)` is not a `τ`-point"
  (`ppL_omega_not_tau`): (P) and (Q) at `(L(ω), L(ω+1))` give `ν_C ≤ L(ω+1)`;
* `ppNuName` (**NU-NAME or `ν_C < L(ω)`**): (P) and (Q) at `(L(ω), L(ω+1))` give either
  `L(ω) <₂ ν_C = L(ω+1)` (`L(ω)` is the left end `ρ_L` of the first non-standard pair) or `ν_C < L(ω)`;
  `ppNuName_cross`, `ppNuName_low` (with `L(ω) ≤ ν_C`: `ν_C = L(ω+1) = ψ_{Ω₁}(Ω_ω·2 + ω^{P'+1} + P')`);
* `ppNuName_real`: the same from the realizer hypotheses of CROSS-LIM at every `L(n+1)` and at `L(ω)`;
* `ppL_rst_low` (**the positive `≤₁` relations at the restarts `L(n+1)` that Lean has**): if `L(ω) ≤ ν_C`, then
  `L(n+1) ≤₁ g` for every `g ∈ [L(n+1), δ]`, `δ = υ_{ι(Ω_ω + P'·(n+1)) + ω + 1}` (D2 below `ν_C`), so
  `lh(L(n+1)) ≥ δ`;
* `ppNuName_full`: with `L(ω) ≤ ν_C` in addition, NU-NAME together with the restarts below it: every `L(n+1)`
  is a restart (`ppL_succ_restart`), `L(n+1) < L(ω)` and `L(n+1) ≤₁ L(ω)`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Pp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Nc

variable {S : InaccSeq.{0}}

/-- **The closing step of CROSS-LIM**: for a limit `X`, `a ≤ P(η + X)`, and `a ≤₁ P(η + c')` for codes
`c' < X` cofinal in `X`: `a ≤₁ P(η + X)`. -/
theorem ppCross_close {a η X : Ordinal.{0}} (hX : IsSuccLimit X) (ha : a ≤ Nm.Pv S (η + X))
    (h : ∀ c < X, ∃ c', c ≤ c' ∧ c' < X ∧ le1 a (Nm.Pv S (η + c'))) :
    le1 a (Nm.Pv S (η + X)) := by
  refine le1_of_cofinal ha fun y _ hy => ?_
  have hex : ∃ c < X, y < Nm.Pv S (η + c) := by
    by_contra hall
    push Not at hall
    exact absurd hy (not_lt.2 (Nm.cont_le hX hall))
  obtain ⟨c, hc, hyc⟩ := hex
  obtain ⟨c', hcc', -, h1⟩ := h c hc
  refine ⟨_, lt_of_lt_of_le hyc ?_, h1⟩
  exact (psi_mono Low.InR_Om_one (by unfold ConjT.Aη; gcongr)).1

/-- `L(ξ+1) = P(Ω_ω + P'·ξ + P')`. -/
theorem ppL_succ_eq (ξ : Ordinal.{0}) :
    ncL S (ξ + 1) = Nm.Pv S (Om ω + ncPp S * ξ + ncPp S) := by
  rw [ncL_eq_A, mul_add_one, add_assoc]

/-- **CROSS-LIM at `L(ξ)`, from its realizers**: if `L(ξ) ≤₁ P(Ω_ω + P'·ξ + c')` for codes `c' < P'`
cofinal in `P'`, then `L(ξ) ≤₁ L(ξ+1)`. -/
theorem ppCross_L (ξ : Ordinal.{0})
    (h : ∀ c < ncPp S, ∃ c', c ≤ c' ∧ c' < ncPp S ∧
      le1 (ncL S ξ) (Nm.Pv S (Om ω + ncPp S * ξ + c'))) :
    le1 (ncL S ξ) (ncL S (ξ + 1)) := by
  rw [ppL_succ_eq]
  refine ppCross_close (ncPp_SC S).isSuccLimit ?_ h
  rw [← ppL_succ_eq]; exact ppL_mono le_self_add

/-- `L(n) ≤₁ L(n+1)` for every `n ≥ 1` gives `L(n) ≤₁ L(m)` for `1 ≤ n ≤ m`. -/
theorem ppChain
    (hC : ∀ n : ℕ, le1 (ncL S ((n + 1 : ℕ) : Ordinal.{0})) (ncL S ((n + 2 : ℕ) : Ordinal.{0}))) :
    ∀ n m : ℕ, n ≤ m → le1 (ncL S ((n + 1 : ℕ) : Ordinal.{0})) (ncL S ((m + 1 : ℕ) : Ordinal.{0})) := by
  intro n m hnm
  induction m, hnm using Nat.le_induction with
  | base => exact le1_refl _
  | succ m _ ih => exact le1_trans ih (hC m)

/-- `L(n) ≤₁ L(n+1)` for every `n ≥ 1` gives `L(n) ≤₁ L(ω)` for every `n ≥ 1`. -/
theorem ppTo_omega
    (hC : ∀ n : ℕ, le1 (ncL S ((n + 1 : ℕ) : Ordinal.{0})) (ncL S ((n + 2 : ℕ) : Ordinal.{0}))) :
    ∀ n : ℕ, le1 (ncL S ((n + 1 : ℕ) : Ordinal.{0})) (ncL S ω) := by
  intro n
  refine le1_of_cofinal (ppL_lt_omega n).le fun y _ hy => ?_
  obtain ⟨k, hk⟩ := ppL_cof y hy
  refine ⟨ncL S ((max n k + 1 : ℕ) : Ordinal.{0}), lt_of_lt_of_le hk (ppL_mono ?_),
    ppChain hC n (max n k) (le_max_left _ _)⟩
  exact_mod_cast Nat.succ_le_succ (le_max_right n k)

/-- **(P) at `(L(ω), L(ω+1))` from the CROSS-LIM relations** `L(n) ≤₁ L(n+1)` (`n ≥ 1`) and
`L(ω) ≤₁ L(ω+1)`; also `L(n) ≤₁ L(ω)` and `L(n) ≤₁ L(ω+1)` (`lh(L(n)) ≥ L(ω+1)`) for `n ≥ 1`. -/
theorem ppP_of_cross
    (hC : ∀ n : ℕ, le1 (ncL S ((n + 1 : ℕ) : Ordinal.{0})) (ncL S ((n + 2 : ℕ) : Ordinal.{0})))
    (hT : le1 (ncL S ω) (ncL S (ω + 1))) :
    NcCofPred (ncL S ω) (ncL S (ω + 1)) ∧
      ∀ n : ℕ, le1 (ncL S ((n + 1 : ℕ) : Ordinal.{0})) (ncL S ω) ∧
        le1 (ncL S ((n + 1 : ℕ) : Ordinal.{0})) (ncL S (ω + 1)) := by
  have hL : ∀ n : ℕ, le1 (ncL S ((n + 1 : ℕ) : Ordinal.{0})) (ncL S (ω + 1)) := fun n =>
    le1_trans (ppTo_omega hC n) hT
  refine ⟨fun γ hγ => ?_, fun n => ⟨ppTo_omega hC n, hL n⟩⟩
  obtain ⟨n, hn⟩ := ppL_cof γ hγ
  exact ⟨_, hn, ppL_lt_omega n, hL n⟩

/-- `ncUpper_L` without the hypothesis "`L(ω)` is not a `τ`-point": (P) and (Q) at `(L(ω), L(ω+1))`
give `ν_C ≤ L(ω+1) = ψ_{Ω₁}(Ω_ω·2 + ω^{P'+1} + P')` and a name `ν_C = P(η)`, `η ≤ Ω_ω + P'·(ω+1)`. -/
theorem ppUpper_P (hP : NcCofPred (ncL S ω) (ncL S (ω + 1)))
    (hQ : ¬ le1 (ncL S ω) (ncL S (ω + 1) + 1)) :
    nuC ≤ S.psi (Om ω + Om ω + ω ^ (ncPp S + 1) + ncPp S) (Om 1) ∧
      ∃ η ≤ Om ω + ncPp S * (ω + 1), nuC = S.psi (Om ω + ConjT.th S * η) (Om 1) :=
  ncUpper_L S ppL_omega_not_tau hP hQ

/-- The upper bound from the CROSS-LIM relations and (Q). -/
theorem ppUpper_cross
    (hC : ∀ n : ℕ, le1 (ncL S ((n + 1 : ℕ) : Ordinal.{0})) (ncL S ((n + 2 : ℕ) : Ordinal.{0})))
    (hT : le1 (ncL S ω) (ncL S (ω + 1))) (hQ : ¬ le1 (ncL S ω) (ncL S (ω + 1) + 1)) :
    nuC ≤ S.psi (Om ω + Om ω + ω ^ (ncPp S + 1) + ncPp S) (Om 1) ∧
      ∃ η ≤ Om ω + ncPp S * (ω + 1), nuC = S.psi (Om ω + ConjT.th S * η) (Om 1) :=
  ppUpper_P (ppP_of_cross hC hT).1 hQ

/-- **NU-NAME or `ν_C < L(ω)`**: if (P) and (Q) hold at `(L(ω), L(ω+1))`, then either `L(ω) <₂ ν_C` with
`ν_C = L(ω+1)` (so `L(ω)` is the left end of the first non-standard pair), or `ν_C < L(ω)`. -/
theorem ppNuName (hP : NcCofPred (ncL S ω) (ncL S (ω + 1)))
    (hQ : ¬ le1 (ncL S ω) (ncL S (ω + 1) + 1)) :
    (ncL S ω < nuC ∧ le2 (ncL S ω) nuC ∧ ncL S (ω + 1) = nuC) ∨ nuC < ncL S ω := by
  have hI : Indec (ncL S ω) := by rw [ncL_eq_A]; exact ncPsi_indec S _
  have hub : ncL S ω ≤ ncL S (ω + 1) := ppL_mono le_self_add
  rcases ncCpb_dichotomy hI ppL_omega_not_tau hub hP hQ with ⟨huν, hb⟩ | h
  · left
    obtain ⟨l, hl, hlν, h2, -, -, -, hfin, -⟩ := level2
    rw [hb] at hP
    have hu0 : 0 < ncL S ω := pos_iff_ne_zero.2 (indec_iff.1 hI).1
    rcases lt_trichotomy (ncL S ω) (upsilon l) with hlt | heq | hgt
    · exfalso
      set T : Set Ordinal.{0} := {u | u < ncL S ω ∧ le1 u (upsilon l)} with hT
      have hTf : T.Finite := hfin _ hlt
      have mem : ∀ α, α < ncL S ω → le1 α nuC → α ∈ T := fun α hα h1 =>
        ⟨hα, le1_of_le_of_le1 (hα.trans hlt).le hlν.le h1⟩
      obtain ⟨α0, -, hα0, h0⟩ := hP 0 hu0
      have hne : T.Nonempty := ⟨α0, mem α0 hα0 h0⟩
      have hm := hne.csSup_mem hTf
      obtain ⟨α, hmα, hαu, hα⟩ := hP _ hm.1
      exact absurd hmα (not_lt.2 (le_csSup hTf.bddAbove (mem α hαu hα)))
    · refine ⟨?_, ?_, hb⟩
      · rw [heq]; exact hlν
      · rw [heq]; exact h2
    · exfalso
      obtain ⟨α, hρα, hαu, hα⟩ := hP _ hgt
      exact U2_gap hl hlν h2 hρα (lt_of_lt_of_le hαu huν) hα
  · exact Or.inr h

/-- NU-NAME or `ν_C < L(ω)`, from the CROSS-LIM relations and (Q). -/
theorem ppNuName_cross
    (hC : ∀ n : ℕ, le1 (ncL S ((n + 1 : ℕ) : Ordinal.{0})) (ncL S ((n + 2 : ℕ) : Ordinal.{0})))
    (hT : le1 (ncL S ω) (ncL S (ω + 1))) (hQ : ¬ le1 (ncL S ω) (ncL S (ω + 1) + 1)) :
    (ncL S ω < nuC ∧ le2 (ncL S ω) nuC ∧ ncL S (ω + 1) = nuC) ∨ nuC < ncL S ω :=
  ppNuName (ppP_of_cross hC hT).1 hQ

/-- **NU-NAME** from the CROSS-LIM relations, (Q), and the lower bound `L(ω) ≤ ν_C`:
`L(ω) <₂ ν_C` and `ν_C = L(ω+1) = ψ_{Ω₁}(Ω_ω·2 + ω^{P'+1} + P')`. -/
theorem ppNuName_low
    (hC : ∀ n : ℕ, le1 (ncL S ((n + 1 : ℕ) : Ordinal.{0})) (ncL S ((n + 2 : ℕ) : Ordinal.{0})))
    (hT : le1 (ncL S ω) (ncL S (ω + 1))) (hQ : ¬ le1 (ncL S ω) (ncL S (ω + 1) + 1))
    (hlow : ncL S ω ≤ nuC) :
    ncL S ω < nuC ∧ le2 (ncL S ω) nuC ∧
      nuC = S.psi (Om ω + Om ω + ω ^ (ncPp S + 1) + ncPp S) (Om 1) := by
  rcases ppNuName_cross hC hT hQ with ⟨h1, h2, h3⟩ | h
  · exact ⟨h1, h2, by rw [← h3, ncL_succ_omega]⟩
  · exact absurd hlow (not_le.2 h)

/-- **NU-NAME or `ν_C < L(ω)`, from the realizers of CROSS-LIM**: if every `L(n+1)` and `L(ω)` is
`≤₁ P(Ω_ω + P'·ξ + c')` for codes `c' < P'` cofinal in `P'` (`ξ = n+1`, resp. `ω`), and (Q) holds at
`(L(ω), L(ω+1))`, then `L(ω) <₂ ν_C = L(ω+1)` or `ν_C < L(ω)`, and `ν_C ≤ L(ω+1)`. -/
theorem ppNuName_real
    (hR : ∀ n : ℕ, ∀ c < ncPp S, ∃ c', c ≤ c' ∧ c' < ncPp S ∧
      le1 (ncL S ((n + 1 : ℕ) : Ordinal.{0}))
        (Nm.Pv S (Om ω + ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) + c')))
    (hRω : ∀ c < ncPp S, ∃ c', c ≤ c' ∧ c' < ncPp S ∧
      le1 (ncL S ω) (Nm.Pv S (Om ω + ncPp S * ω + c')))
    (hQ : ¬ le1 (ncL S ω) (ncL S (ω + 1) + 1)) :
    ((ncL S ω < nuC ∧ le2 (ncL S ω) nuC ∧ ncL S (ω + 1) = nuC) ∨ nuC < ncL S ω) ∧
      nuC ≤ S.psi (Om ω + Om ω + ω ^ (ncPp S + 1) + ncPp S) (Om 1) := by
  have hC : ∀ n : ℕ, le1 (ncL S ((n + 1 : ℕ) : Ordinal.{0})) (ncL S ((n + 2 : ℕ) : Ordinal.{0})) := by
    intro n
    have e : ((n + 2 : ℕ) : Ordinal.{0}) = ((n + 1 : ℕ) : Ordinal.{0}) + 1 := Nat.cast_succ (n + 1)
    rw [e]; exact ppCross_L _ (hR n)
  have hT := ppCross_L ω hRω
  exact ⟨ppNuName_cross hC hT hQ, (ppUpper_cross hC hT hQ).1⟩

/-- **The positive `≤₁` relations at the restarts `L(n+1)` below `ν_C`** (D2): if `L(ω) ≤ ν_C`, then
`L(n+1) ≤₁ g` for every `g` with `L(n+1) ≤ g ≤ υ_{ι(Ω_ω + P'·(n+1)) + ω + 1}`. -/
theorem ppL_rst_low (hlow : ncL S ω ≤ nuC) (n : ℕ) :
    ∀ g, ncL S ((n + 1 : ℕ) : Ordinal.{0}) ≤ g →
      g ≤ upsilon (iota S (Om ω + ncPp S * ((n + 1 : ℕ) : Ordinal.{0})) + ω + 1) →
      le1 (ncL S ((n + 1 : ℕ) : Ordinal.{0})) g := by
  set l := iota S (Om ω + ncPp S * ((n + 1 : ℕ) : Ordinal.{0})) with hl
  have hw : (ω : Ordinal.{0}) + 1 < ω * ω := by
    calc (ω : Ordinal.{0}) + 1 < ω + ω := by gcongr; exact one_lt_omega0
      _ = ω * 2 := (mul_two_eq _).symm
      _ < ω * ω := by
          gcongr <;> first | exact omega0_pos | exact_mod_cast Ordinal.natCast_lt_omega0 2
  have hδ : upsilon (l + ω + 1) < nuC := by
    refine lt_of_lt_of_le ?_ hlow
    refine lt_of_lt_of_le ?_ (ppL_mono (S := S) (Ordinal.natCast_lt_omega0 (n + 2)).le)
    rw [ppL_eq_ups ((n + 2 : ℕ) : Ordinal.{0})]
    refine upsilon_normal.strictMono (lt_of_lt_of_le ?_ (ppIota_step n))
    rw [add_assoc]; gcongr
  rw [ppL_eq_ups]
  exact rst_C (ppIota_succ_restart n) hδ

/-- **NU-NAME with its restarts**: from the CROSS-LIM relations, (Q) and `L(ω) ≤ ν_C`: `L(ω) <₂ ν_C`,
`ν_C = L(ω+1) = ψ_{Ω₁}(Ω_ω·2 + ω^{P'+1} + P')`, `L(ω)` and every `L(n+1)` are restarts, and every `L(n+1)` is
a `<₁`-predecessor of `L(ω)`. -/
theorem ppNuName_full
    (hC : ∀ n : ℕ, le1 (ncL S ((n + 1 : ℕ) : Ordinal.{0})) (ncL S ((n + 2 : ℕ) : Ordinal.{0})))
    (hT : le1 (ncL S ω) (ncL S (ω + 1))) (hQ : ¬ le1 (ncL S ω) (ncL S (ω + 1) + 1))
    (hlow : ncL S ω ≤ nuC) :
    ncL S ω < nuC ∧ le2 (ncL S ω) nuC ∧
      nuC = S.psi (Om ω + Om ω + ω ^ (ncPp S + 1) + ncPp S) (Om 1) ∧
      (∃ l, IsRestartIdx l ∧ ncL S ω = upsilon l) ∧
      ∀ n : ℕ, (∃ l, IsRestartIdx l ∧ ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l) ∧
        ncL S ((n + 1 : ℕ) : Ordinal.{0}) < ncL S ω ∧ le1 (ncL S ((n + 1 : ℕ) : Ordinal.{0})) (ncL S ω) := by
  obtain ⟨h1, h2, h3⟩ := ppNuName_low hC hT hQ hlow
  exact ⟨h1, h2, h3, ppL_omega_restart, fun n =>
    ⟨ppL_succ_restart n, ppL_lt_omega n, (ppP_of_cross hC hT).2 n |>.1⟩⟩

end Googology.Trans.PoR.InaccPsi.R2.Pp

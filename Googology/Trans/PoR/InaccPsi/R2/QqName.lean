import Googology.Trans.PoR.InaccPsi.R2.QqCap
import Googology.Trans.PoR.InaccPsi.R2.NcName
import Googology.Trans.PoR.InaccPsi.R2.BtT

/-!
# PAIR, (P) and (Q) at the named pair `(L(ω), L(ω+1))`, from the data of SHIFT at `c_n = L(n)`

`P' = ψ_{Ω₂}(Ω_ω·2)` (`ncPp`), `L(ξ) = ψ_{Ω₁}(Ω_ω·2 + P'·ξ)` (`ncL`), and, by GEN,
`L(ξ) = ψ_{Ω₁}(Ω_ω + θ·(Ω_ω + P'·ξ))` (`ncL_eq_A`).

* `qqL_mono`, `qqL_lt_omega`, `qqL_lt_succ`, `qqL_cof`: `n ↦ L(n)` is monotone, `L(n) < L(ω) < L(ω+1)`,
  and `{L(n)}` is cofinal in `L(ω)` (Lemma CONT, `psi_limit`);
* the data at the named points: (C1) `L(n+1) ≤₁ L(ω)` (the part of CROSS-LIM that SHIFT uses);
  (EMB) `B n` embeds `[0, L(n+1))` into `[0, L(ω+1))` (keeps and reflects `<`, `+`, `≤₁`, `≤₂`, closed
  range) and fixes `[0, L(n))`; (ONTO-FIN) every finite `Y ⊆ [L(ω), L(ω+1))` lies in the range of
  `B n` for arbitrarily large `n`;
* `qqPair_L` (**PAIR**): `L(ω) <₂ L(ω+1)`; `qqP_L`: (P) at `(L(ω), L(ω+1))`;
* `qqQ_L` (**(Q)** and the reach): if `L(ω) < T_ω`, then `¬ L(ω) ≤₁ L(ω+1) + 1` and
  `lh(L(ω)) = L(ω+1)`; `qqCap_L`: for `g ≥ L(ω)`, `L(ω) ≤₁ g ⇔ g ≤ L(ω+1)`;
* `qqQ_L_of_le_nuC`: (Q) when `L(ω) ≤ ν_C`;
* `qqUpper_L` (**the upper bound**): if `L(ω)` is not a `τ`-point, then
  `ν_C ≤ L(ω+1) = ψ_{Ω₁}(Ω_ω·2 + ω^{P'+1} + P')` and `ν_C = ψ_{Ω₁}(Ω_ω + θ·η)` for some
  `η ≤ Ω_ω + P'·(ω+1)`; `qqUpper_L_cpb`: the same through `ncUpper_L`, whose (P) and (Q) are
  discharged here (with `L(ω) < T_ω`);
* `qqNuC_eq_L`: if `L(ω)` is not a `τ`-point and `L(ω) ≤ ν_C`, then `ν_C = L(ω+1)`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Qq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Nc

section Names

variable (S : InaccSeq.{0})

theorem qqPp_pos : 0 < ncPp S := (ncPp_SC S).1

theorem qqPp_mem {a X : Ordinal.{0}} (h : Om ω + Om ω < a) : ncPp S ∈ S.CSet a X :=
  CSet.psi_mem h (InR_Om_succ 1) (CSet.Om_mem (CSet.add_mem (CSet.one_mem a X) (CSet.one_mem a X)))
    (CSet.add_mem (ConjT.OmW_mem S a X) (ConjT.OmW_mem S a X))

/-- The argument of `L(n)` is in its own closure. -/
theorem qqArg_nat_mem (n : ℕ) (X : Ordinal.{0}) :
    Om ω + Om ω + ncPp S * (n : Ordinal.{0}) ∈ S.CSet (Om ω + Om ω + ncPp S * (n : Ordinal.{0})) X := by
  rcases n with _ | n
  · rw [Nat.cast_zero, mul_zero, add_zero]
    exact CSet.add_mem (ConjT.OmW_mem S _ X) (ConjT.OmW_mem S _ X)
  · have hlt : Om ω + Om ω < Om ω + Om ω + ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) :=
      lt_add_of_pos_right _ (mul_pos (qqPp_pos S) (by exact_mod_cast Nat.succ_pos n))
    exact CSet.add_mem (CSet.add_mem (ConjT.OmW_mem S _ X) (ConjT.OmW_mem S _ X))
      (ConjT.mul_nat_mem S (qqPp_mem S hlt) (n + 1))

/-- The argument of `L(ω)` is in its own closure. -/
theorem qqArg_omega_mem (X : Ordinal.{0}) :
    Om ω + Om ω + ncPp S * ω ∈ S.CSet (Om ω + Om ω + ncPp S * ω) X := by
  have hlt : Om ω + Om ω < Om ω + Om ω + ncPp S * ω :=
    lt_add_of_pos_right _ (mul_pos (qqPp_pos S) omega0_pos)
  have e : ncPp S * ω = veblen 0 (ncPp S + 1) := by
    rw [veblen_zero_apply, opow_add, opow_one, Low.opow_eq_self_of_SC (ncPp_SC S)]
  have hm : veblen 0 (ncPp S + 1) ∈ S.CSet (Om ω + Om ω + ncPp S * ω) X :=
    CSet.phi_mem (CSet.zero_mem _ _) (CSet.succ_mem (qqPp_mem S hlt))
  rw [← e] at hm
  exact CSet.add_mem (CSet.add_mem (ConjT.OmW_mem S _ X) (ConjT.OmW_mem S _ X)) hm

theorem qqL_mono : Monotone fun n : ℕ => ncL S (n : Ordinal.{0}) := by
  intro m n hmn
  have h : (m : Ordinal.{0}) ≤ n := Nat.cast_le.2 hmn
  show ncL S m ≤ ncL S n
  unfold ncL
  exact (psi_mono Low.InR_Om_one (by gcongr)).1

theorem qqL_lt_omega (n : ℕ) : ncL S (n : Ordinal.{0}) < ncL S ω :=
  psi_lt_psi Low.InR_Om_one ((add_lt_add_iff_left _).2 ((mul_lt_mul_iff_right₀ (qqPp_pos S)).2
    (natCast_lt_omega0 n))) (qqArg_nat_mem S n _)

theorem qqL_lt_succ : ncL S ω < ncL S (ω + 1) :=
  psi_lt_psi Low.InR_Om_one ((add_lt_add_iff_left _).2 ((mul_lt_mul_iff_right₀ (qqPp_pos S)).2
    (Order.lt_add_one_iff.2 le_rfl))) (qqArg_omega_mem S _)

/-- `{L(n)}` is cofinal in `L(ω)` (Lemma CONT). -/
theorem qqL_cof : ∀ γ < ncL S ω, ∃ n : ℕ, γ < ncL S (n : Ordinal.{0}) := by
  intro γ hγ
  have hlim : IsSuccLimit (Om ω + Om ω + ncPp S * ω) :=
    isSuccLimit_add _ (isSuccLimit_mul_right (qqPp_pos S) isSuccLimit_omega0)
  have hbdd : BddAbove (range fun e : Iio (Om ω + Om ω + ncPp S * ω) => S.psi e.1 (Om 1)) :=
    ⟨Om 1, by rintro _ ⟨e, rfl⟩; exact (psi_lt Low.InR_Om_one _).le⟩
  haveI : Nonempty (Iio (Om ω + Om ω + ncPp S * ω)) := ⟨⟨0, hlim.bot_lt⟩⟩
  unfold ncL at hγ
  rw [psi_limit S hlim] at hγ
  obtain ⟨e, he⟩ := (lt_ciSup_iff hbdd).1 hγ
  obtain ⟨n, hn⟩ : ∃ n : ℕ, e.1 ≤ Om ω + Om ω + ncPp S * (n : Ordinal.{0}) := by
    rcases lt_or_ge e.1 (Om ω + Om ω) with h1 | h1
    · exact ⟨0, by rw [Nat.cast_zero, mul_zero, add_zero]; exact h1.le⟩
    · obtain ⟨d, hd⟩ := exists_add_of_le h1
      have hd' : d < ncPp S * ω := by
        have := e.2
        rw [Set.mem_Iio, hd] at this
        exact (add_lt_add_iff_left _).1 this
      obtain ⟨c, hc, hdc⟩ := (lt_mul_iff_of_isSuccLimit isSuccLimit_omega0).1 hd'
      obtain ⟨n, rfl⟩ := lt_omega0.1 hc
      refine ⟨n, ?_⟩
      rw [hd]
      gcongr
  exact ⟨n, he.trans_le (psi_mono Low.InR_Om_one hn).1⟩

end Names

section Pair

variable (S : InaccSeq.{0}) {B : ℕ → Ordinal.{0} → Ordinal.{0}}
  (hc1 : ∀ n : ℕ, le1 (ncL S ((n + 1 : ℕ) : Ordinal.{0})) (ncL S ω))
  (hBm : ∀ n : ℕ, StrictMonoOn (B n) (Set.Iio (ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
  (hBb : ∀ n : ℕ, ∀ x < ncL S ((n + 1 : ℕ) : Ordinal.{0}), B n x < ncL S (ω + 1))
  (hBadd : ∀ n : ℕ, ∀ x < ncL S ((n + 1 : ℕ) : Ordinal.{0}), ∀ y < ncL S ((n + 1 : ℕ) : Ordinal.{0}),
    ∀ z < ncL S ((n + 1 : ℕ) : Ordinal.{0}), (x + y = z ↔ B n x + B n y = B n z))
  (hB1 : ∀ n : ℕ, ∀ x < ncL S ((n + 1 : ℕ) : Ordinal.{0}), ∀ y < ncL S ((n + 1 : ℕ) : Ordinal.{0}),
    (le1 x y ↔ le1 (B n x) (B n y)))
  (hB2 : ∀ n : ℕ, ∀ x < ncL S ((n + 1 : ℕ) : Ordinal.{0}), ∀ y < ncL S ((n + 1 : ℕ) : Ordinal.{0}),
    (le2 x y ↔ le2 (B n x) (B n y)))
  (hBcl : ∀ n : ℕ, Closed (B n '' Set.Iio (ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
  (hfix : ∀ n : ℕ, ∀ x < ncL S (n : Ordinal.{0}), B n x = x)
  (honto : ∀ Y : Finset Ordinal.{0}, (∀ y ∈ Y, ncL S ω ≤ y ∧ y < ncL S (ω + 1)) → ∀ N, ∃ n, N ≤ n ∧
    ∀ y ∈ Y, ∃ y' < ncL S ((n + 1 : ℕ) : Ordinal.{0}), B n y' = y)

include hc1 hBm hBb hBadd hB1 hB2 hBcl hfix honto

/-- **PAIR**: `L(ω) <₂ L(ω+1)`. -/
theorem qqPair_L : ncL S ω < ncL S (ω + 1) ∧ le2 (ncL S ω) (ncL S (ω + 1)) :=
  ⟨qqL_lt_succ S, qqShift (c := fun n : ℕ => ncL S (n : Ordinal.{0})) (qqL_mono S) (qqL_lt_omega S)
    (qqL_cof S) hc1 (qqL_lt_succ S).le hBm hBb hBadd hB1 hB2 hBcl hfix honto⟩

/-- (P) at `(L(ω), L(ω+1))`. -/
theorem qqP_L : NcCofPred (ncL S ω) (ncL S (ω + 1)) :=
  qqShift_P (c := fun n : ℕ => ncL S (n : Ordinal.{0})) (qqL_mono S) (qqL_lt_omega S)
    (qqL_cof S) hc1 (qqL_lt_succ S).le hBm hBb hBadd hB1 hB2 hBcl hfix honto

/-- **(Q)** at `(L(ω), L(ω+1))` and `lh(L(ω)) = L(ω+1)`, when `L(ω) < T_ω`. -/
theorem qqQ_L (hTw : ncL S ω < shTw) :
    ¬ le1 (ncL S ω) (ncL S (ω + 1) + 1) ∧ IsReach R2C (ncL S ω) (ncL S (ω + 1)) :=
  ⟨qqQ_succ (c := fun n : ℕ => ncL S (n : Ordinal.{0})) (qqL_mono S) (qqL_lt_omega S)
    (qqL_cof S) hc1 (qqL_lt_succ S) hBm hBb hBadd hB1 hB2 hBcl hfix honto hTw,
   qqReach (c := fun n : ℕ => ncL S (n : Ordinal.{0})) (qqL_mono S) (qqL_lt_omega S)
    (qqL_cof S) hc1 (qqL_lt_succ S) hBm hBb hBadd hB1 hB2 hBcl hfix honto hTw⟩

/-- **CAP at `L(ω)`**: when `L(ω) < T_ω`, for `g ≥ L(ω)`, `L(ω) ≤₁ g ⇔ g ≤ L(ω+1)`. -/
theorem qqCap_L (hTw : ncL S ω < shTw) {g : Ordinal.{0}} (hg : ncL S ω ≤ g) :
    le1 (ncL S ω) g ↔ g ≤ ncL S (ω + 1) :=
  qqCap (c := fun n : ℕ => ncL S (n : Ordinal.{0})) (qqL_mono S) (qqL_lt_omega S)
    (qqL_cof S) hc1 (qqL_lt_succ S) hBm hBb hBadd hB1 hB2 hBcl hfix honto hTw hg

/-- **(Q)** at `(L(ω), L(ω+1))` when `L(ω) ≤ ν_C`. -/
theorem qqQ_L_of_le_nuC (hν : ncL S ω ≤ nuC) : ¬ le1 (ncL S ω) (ncL S (ω + 1) + 1) :=
  qqQ_of_le_nuC (c := fun n : ℕ => ncL S (n : Ordinal.{0})) (qqL_mono S) (qqL_lt_omega S)
    (qqL_cof S) hc1 (qqL_lt_succ S) hBm hBb hBadd hB1 hB2 hBcl hfix honto hν

/-- **The upper bound**: if `L(ω)` is not a `τ`-point, `ν_C ≤ L(ω+1) = ψ_{Ω₁}(Ω_ω·2 + ω^{P'+1} + P')`,
and `ν_C = ψ_{Ω₁}(Ω_ω + θ·η)` for some `η ≤ Ω_ω + P'·(ω+1)`. -/
theorem qqUpper_L (hτ : ¬ NcTauPt (ncL S ω)) :
    nuC ≤ S.psi (Om ω + Om ω + ω ^ (ncPp S + 1) + ncPp S) (Om 1) ∧
      ∃ η ≤ Om ω + ncPp S * (ω + 1), nuC = S.psi (Om ω + ConjT.th S * η) (Om 1) := by
  obtain ⟨hlt, h2⟩ := qqPair_L S hc1 hBm hBb hBadd hB1 hB2 hBcl hfix honto
  have := ncUpper_pair_named S hlt h2 hτ (ncL_eq_A S (ω + 1)).le
  rw [← ncL_eq_A, ncL_succ_omega] at this
  exact this

/-- The same bound through `ncUpper_L` (CPB), with (P) and (Q) discharged, when `L(ω) < T_ω`. -/
theorem qqUpper_L_cpb (hτ : ¬ NcTauPt (ncL S ω)) (hTw : ncL S ω < shTw) :
    nuC ≤ S.psi (Om ω + Om ω + ω ^ (ncPp S + 1) + ncPp S) (Om 1) ∧
      ∃ η ≤ Om ω + ncPp S * (ω + 1), nuC = S.psi (Om ω + ConjT.th S * η) (Om 1) :=
  ncUpper_L S hτ (qqP_L S hc1 hBm hBb hBadd hB1 hB2 hBcl hfix honto)
    (qqQ_L S hc1 hBm hBb hBadd hB1 hB2 hBcl hfix honto hTw).1

/-- If `L(ω)` is not a `τ`-point and `L(ω) ≤ ν_C`, then `ν_C = L(ω+1)`. -/
theorem qqNuC_eq_L (hτ : ¬ NcTauPt (ncL S ω)) (hν : ncL S ω ≤ nuC) : nuC = ncL S (ω + 1) :=
  qqNu_eq (c := fun n : ℕ => ncL S (n : Ordinal.{0})) (qqL_mono S) (qqL_lt_omega S)
    (qqL_cof S) hc1 (qqL_lt_succ S) hBm hBb hBadd hB1 hB2 hBcl hfix honto hτ hν

end Pair

end Googology.Trans.PoR.InaccPsi.R2.Qq

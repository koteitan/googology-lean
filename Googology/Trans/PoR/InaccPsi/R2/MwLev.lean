import Googology.Trans.PoR.InaccPsi.R2.MwInd

/-!
# `SfLhTMove` off `P_ω`: `B_n` commutes with `lhᵗ` at every finite fixed-point level

[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `τ = υ_ξ`, `ϑᵗ = vt τ`, `lhᵗ = lhT τ` ([W07b] Def 4.1, a repo constant), `φ_k = veblen k`,
`P_m` the range of `φ_m`, `ind_τ = phInd k τ`, `VzB τ = sup_N ϑᵗ(Ω₁·N)`.  The cited values of `lhᵗ` used are the repo
axioms `CitedVz.vzLhT_fix` and `CitedVz.vzLhT_lim` ([W07b] Def 4.1 at `ϑᵗ(Ω₁·k + η)`, `1 ≤ k < ω`; for `k = 1`,
`η = 0` this is `lhᵗ(ε_{τ+1}) = ε_{τ+1}·2`).

* `mwFix_iff` (**the case split of `lhᵗ` in `B_n`-invariant terms**): for `η ∈ Tᵗ ∩ Ω₁`,
  `(∀ σ < η, ϑᵗ(Ω₁·k + σ) ≤ η) ⇔ η = 0 ∨ (τ < η ∧ η ∈ P_{k+1})`;
* `mwLhT_fixc`, `mwLhT_limc` (**`lhᵗ(φ_k(β)) = φ_k(β)·(k+1) + ζ`**, `ζ = 0` in the first case, `logend(ind_τ β)`
  otherwise; `φ_k(β) = ϑᵗ(Ω₁·k + ind_τ β)` by `Ph.phLev`);
* `mwB_mul_nat` (`B_n(x·m) = B_n x·m`), `mwLevel` (**an ε-number off some `P_{m+1}` is in `P_k ∖ P_{k+1}` for some
  `1 ≤ k < ω`**), `mwNotPw_of_lt` (every ε-number in `(τ, VzB τ)` is off some `P_{m+1}`);
* `mwLhT_fin` (**`SfLhTMove` at every ε-number `x ∈ (υ_ξ, υ_{ξ+1})` that is off some `P_{m+1}`, `m < ω`**, including
  `x = ε_{υ_ξ+1}` and every `x < VzB(υ_ξ)`):
  `x = φ_k(β)`, `B_n x = φ_k(B_n β)` (`Mw.mwB_veblen_nat`), `ind_{τ'}(B_n β) = B_n(ind_τ β)` (`Mw.mwInd_move`), the
  case split moves (`Mw.mwB_vzP_iff`), and `B_n` keeps `·(k+1)`, `+` and `logend`;
* `MwLhTop S` (a hypothesis name): `SfLhTMove` at the ε-numbers `x` in every `P_{m+1}`, `m < ω` (so
  `x ≥ VzB(υ_ξ) = ϑ^{υ_ξ}(Ω₁·ω)`);
  `mwLhT`: `MwLhTop` gives `SfLhTMove`; `mwLhTop_of_mv`: `MvLhTop` gives `MwLhTop` (so `MwLhTop` is weaker);
* `mwRoad` (**the road with `MwLhTop` and `L(ω+1) ≤ ν_C → MwEQtop`**).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Mw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Ph

variable {S : InaccSeq.{0}}

/-- **The case split of `lhᵗ` in invariant terms.** -/
theorem mwFix_iff {k : ℕ} (hk : 1 ≤ k) {τ η : Ordinal.{0}} (hτ : SC τ) (hτ1 : τ < Om1) (hη : η ∈ Tset τ)
    (hη1 : η < Om1) :
    (∀ σ, σ < η → vt τ (Om1 * (k : Ordinal.{0}) + σ) ≤ η) ↔ (η = 0 ∨ (τ < η ∧ VzP (k + 1) η)) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  constructor
  · intro hfix
    rcases eq_or_ne η 0 with h0 | h0
    · exact Or.inl h0
    right
    have h0T : (0 : Ordinal.{0}) ∈ Tset τ := vz_T_down hτE hτ1 hη hη1 zero_le
    have hf0 := vz_th_facts hτE hτ1 hk h0T (lt_of_le_of_lt zero_le hη1)
    have hτη : τ < η := hf0.2.2.2.1.trans_le (hfix 0 (pos_iff_ne_zero.2 h0))
    refine ⟨hτη, ?_⟩
    have hlim : IsSuccLimit η := by
      rcases zero_or_succ_or_isSuccLimit η with h | ⟨σ, hσ⟩ | h
      · exact absurd h h0
      · exfalso
        have hση : σ < η := hσ ▸ lt_succ σ
        have hσT := vz_T_down hτE hτ1 hη hη1 hση.le
        have hf := vz_th_facts hτE hτ1 hk hσT (hση.trans hη1)
        have hle := hfix σ hση
        have heq : vt τ (Om1 * (k : Ordinal.{0}) + σ) = η :=
          le_antisymm hle (hσ ▸ Order.succ_le_of_lt hf.2.2.2.2.2.2.2)
        have hvl : IsSuccLimit (vt τ (Om1 * (k : Ordinal.{0}) + σ)) :=
          ph_P_lim (k := 0) (by rw [zero_add]; exact vzP_one.2 hf.2.2.2.2.2.1)
        rw [heq, ← hσ] at hvl
        exact not_isSuccLimit_succ σ hvl
      · exact h
    have hall : ∀ β' < η, veblen (k : Ordinal.{0}) β' ≤ η := by
      intro β' hβ'
      by_cases hτβ' : β' ≤ τ
      · calc veblen (k : Ordinal.{0}) β' ≤ veblen (k : Ordinal.{0}) τ := veblen_le_veblen_iff_right.2 hτβ'
          _ = τ := hτ.veblen_right (ph_nat_lt hτ k)
          _ ≤ η := hτη.le
      · push Not at hτβ'
        by_cases hP : VzP (k + 1) β'
        · rw [vzP_succ.1 hP]; exact hβ'.le
        · have hmem : β' ∈ phC k τ := mem_phC.2 ⟨hτβ', hP⟩
          have hlt : phInd k τ β' < phInd k τ η := Cd.cdOtp_lt_of_mem hmem hβ'
          have hle : phInd k τ η ≤ η := Cd.cdOtp_le_self _ η
          have hT' := vz_T_down hτE hτ1 hη hη1 (hlt.trans_le hle).le
          rw [phLev hτ hτ1 hk β' hτβ' hP hT' ((hlt.trans_le hle).trans hη1)]
          exact hfix _ (hlt.trans_le hle)
    have hv : veblen (k : Ordinal.{0}) η ≤ η := ((isNormal_veblen _).le_iff_forall_le hlim).2 hall
    exact vzP_succ.2 (le_antisymm hv (right_le_veblen _ _))
  · rintro (h0 | ⟨hτη, hP⟩)
    · intro σ hσ; rw [h0] at hσ; exact absurd hσ (not_lt.2 zero_le)
    · intro σ
      induction σ using WellFoundedLT.induction with
      | ind σ IH =>
      intro hσ
      have hσT := vz_T_down hτE hτ1 hη hη1 hσ.le
      refine vz_th_min hτE hτ1 hk hσT (hσ.trans hη1) (vzP_mono hk (by omega) hP) hτη hσ fun σ' hσ' => ?_
      refine lt_of_le_of_ne (IH σ' hσ' (hσ'.trans hσ)) fun e => ?_
      have hσ'T := vz_T_down hτE hτ1 hη hη1 (hσ'.trans hσ).le
      exact vz_th_notP hτE hτ1 hk hσ'T ((hσ'.trans hσ).trans hη1) (e ▸ hP)

/-- **`lhᵗ(φ_k(β)) = φ_k(β)·(k+1)`** when `η = ind_τ β` has `η = 0 ∨ (τ < η ∧ η ∈ P_{k+1})`. -/
theorem mwLhT_fixc {k : ℕ} (hk : 1 ≤ k) {τ β : Ordinal.{0}} (hτ : SC τ) (hτ1 : τ < Om1) (hτβ : τ < β)
    (hβ : ¬ VzP (k + 1) β) (hT : phInd k τ β ∈ Tset τ) (h1 : phInd k τ β < Om1)
    (hc : phInd k τ β = 0 ∨ (τ < phInd k τ β ∧ VzP (k + 1) (phInd k τ β))) :
    lhT τ (veblen (k : Ordinal.{0}) β) = veblen (k : Ordinal.{0}) β * ((k + 1 : ℕ) : Ordinal.{0}) := by
  rw [phLev hτ hτ1 hk β hτβ hβ hT h1]
  exact vzLhT_fix (Gg.gg_SC_eps hτ) hτ1 hk hT h1 ((mwFix_iff hk hτ hτ1 hT h1).2 hc)

/-- **`lhᵗ(φ_k(β)) = φ_k(β)·(k+1) + logend(η)`** otherwise. -/
theorem mwLhT_limc {k : ℕ} (hk : 1 ≤ k) {τ β : Ordinal.{0}} (hτ : SC τ) (hτ1 : τ < Om1) (hτβ : τ < β)
    (hβ : ¬ VzP (k + 1) β) (hT : phInd k τ β ∈ Tset τ) (h1 : phInd k τ β < Om1)
    (hc : ¬ (phInd k τ β = 0 ∨ (τ < phInd k τ β ∧ VzP (k + 1) (phInd k τ β)))) :
    lhT τ (veblen (k : Ordinal.{0}) β) =
      veblen (k : Ordinal.{0}) β * ((k + 1 : ℕ) : Ordinal.{0}) + lg (phInd k τ β) := by
  have h0 : phInd k τ β ≠ 0 := fun h => hc (Or.inl h)
  have hnf := mt (mwFix_iff hk hτ hτ1 hT h1).1 hc
  push Not at hnf
  rw [phLev hτ hτ1 hk β hτβ hβ hT h1]
  exact vzLhT_lim (Gg.gg_SC_eps hτ) hτ1 hk hT h1 h0 hnf

theorem mw_mul_nat_lt {x : Ordinal.{0}} (hx : x < Nc.ncL S ω) : ∀ m : ℕ, x * (m : Ordinal.{0}) < Nc.ncL S ω
  | 0 => by rw [Nat.cast_zero, mul_zero]; exact (Lw.lw_L_SC S _).1
  | m + 1 => by rw [Nat.cast_succ, mul_add_one]; exact Bc.ncL_add_lt (mw_mul_nat_lt hx m) hx

/-- `B_n(x·m) = B_n x·m`. -/
theorem mwB_mul_nat {n : ℕ} {x : Ordinal.{0}} (hx : x < Nc.ncL S ω) :
    ∀ m : ℕ, Bc.bcB S n (x * (m : Ordinal.{0})) = Bc.bcB S n x * (m : Ordinal.{0})
  | 0 => by rw [Nat.cast_zero, mul_zero, mul_zero, Bc.bcB_zero]
  | m + 1 => by
    rw [Nat.cast_succ, mul_add_one, mul_add_one, Bc.bcB_add (mw_mul_nat_lt hx m) hx, mwB_mul_nat hx m]

/-- **An ε-number outside some `P_{m+1}` is in `P_k ∖ P_{k+1}` for some `1 ≤ k`.** -/
theorem mwLevel {x : Ordinal.{0}} (hE : InE x) (hex : ∃ m : ℕ, ¬ VzP (m + 1) x) :
    ∃ k : ℕ, 1 ≤ k ∧ VzP k x ∧ ¬ VzP (k + 1) x := by
  classical
  set k := Nat.find hex with hk
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exfalso
      have := Nat.find_spec hex
      rw [← hk, h, zero_add] at this
      exact this (vzP_one.2 hE)
    · exact h
  refine ⟨k, hk1, ?_, Nat.find_spec hex⟩
  have hlt : k - 1 < k := by omega
  have := Nat.find_min hex hlt
  push Not at this
  rwa [show k - 1 + 1 = k by omega] at this

/-- Every ε-number `x ∈ (τ, VzB τ)` is outside `P_{N+1}` for some `N`. -/
theorem mwNotPw_of_lt {τ x : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hτx : τ < x)
    (hB : x < VzB τ) : ∃ m : ℕ, ¬ VzP (m + 1) x := by
  obtain ⟨N, hN⟩ := vzB_lt_iff.1 hB
  have hN' : x < vt τ (Om1 * ((N + 1 : ℕ) : Ordinal.{0}) + 0) := hN.trans_le (vzN_le hτ hτ1 (by omega))
  refine ⟨N, fun hP => ?_⟩
  have := (vz_th_least hτ hτ1 (by omega : 1 ≤ N + 1)).2.2 x hP hτx
  exact absurd hN' (not_lt.2 this)

/-- **`SfLhTMove` at every ε-number `x ∈ (υ_ξ, υ_{ξ+1})` off some `P_{m+1}`** (`x` not a fixed point of every
`φ_m`, `m < ω`). -/
theorem mwLhT_fin {n : ℕ} {ξ ξ' x : Ordinal.{0}} (hc : Bc.bcC S n ≤ upsilon ξ) (hτx : upsilon ξ < x)
    (hx2 : x < upsilon (ξ + 1)) (hξ1lt : upsilon (ξ + 1) < Bc.bcC S (n + 1)) (hE : InE x)
    (hBξ : Bc.bcB S n (upsilon ξ) = upsilon ξ')
    (hBξ1 : Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1)) (hnP : ∃ m : ℕ, ¬ VzP (m + 1) x) :
    Bc.bcB S n (lhT (upsilon ξ) x) = lhT (upsilon ξ') (Bc.bcB S n x) := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Qq.qqL_lt_omega S (n + 1 + 1)
  have hXSC : SC (Bc.bcC S (n + 1)) := Lw.lw_L_SC S _
  have hxX : x < Bc.bcC S (n + 1) := hx2.trans hξ1lt
  have hxL : x < Nc.ncL S ω := hxX.trans hLw
  have hτL : upsilon ξ < Nc.ncL S ω := hτx.trans hxL
  have hτ1L : upsilon (ξ + 1) < Nc.ncL S ω := hξ1lt.trans hLw
  have hωC : (ω : Ordinal.{0}) < Bc.bcC S n := Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)
  have h1C : (1 : Ordinal.{0}) < Bc.bcC S n := one_lt_omega0.trans hωC
  have hOm : Nc.ncL S ω < Om1 := by rw [Br.Om1_eq]; exact InaccSeq.psi_lt Low.InR_Om_one _
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    rw [upsilon_zero] at hc
    exact absurd (lt_of_lt_of_le (zero_lt_one.trans h1C) hc) (lt_irrefl _)
  have hLω : Nc.ncL S ω ≤ Bc.bcB S n (upsilon ξ) := by
    rw [← Bc.bcB_base (S := S) n]
    rcases eq_or_lt_of_le hc with e | hlt
    · rw [← e]; exact le_rfl
    · exact ((Bc.bcB_lt_iff (Qq.qqL_lt_omega S (n + 1)) hτL).2 hlt).le
  have hξ'0 : ξ' ≠ 0 := by
    rintro rfl
    rw [hBξ, upsilon_zero] at hLω
    exact absurd (lt_of_lt_of_le (Lw.lw_L_SC S ω).1 hLω) (lt_irrefl _)
  have hτ'L1 : upsilon ξ' < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq S, ← hBξ]; exact Bc.bcB_bound' S n _ (hτx.trans hxX)
  have hτSC : SC (upsilon ξ) := mvUps_SC hξ0 (show upsilon ξ < Nm.Pv S (Om ω + Nc.ncPp S * ω) by
    rw [← Lw.lw_L_eq S]; exact hτL)
  have hτ'SC : SC (upsilon ξ') := mvUps_SC hξ'0 hτ'L1
  have hτ1 : upsilon ξ < Om1 := hτL.trans hOm
  have hτ'1 : upsilon ξ' < Om1 := by rw [Br.Om1_eq]; exact hτ'L1.trans (Nm.Pv_lt_Om1 S _)
  have hu1 : upsilon (ξ + 1) < Om1 := hτ1L.trans hOm
  have hu1' : upsilon (ξ' + 1) < Om1 := by
    rw [← hBξ1, Br.Om1_eq]
    exact (Bc.bcB_bound n _ hξ1lt).trans (InaccSeq.psi_lt Low.InR_Om_one _)
  -- the `T`-membership below `υ_{ξ+1}` and `υ_{ξ'+1}`
  have hTm : ∀ a, a < upsilon (ξ + 1) → a ∈ Tset (upsilon ξ) := by
    intro a ha
    have h := upsilon_succ_T ξ (by rw [succ_eq_add_one]; exact hu1) a (ha.trans hu1)
    rw [if_neg hξ0] at h
    exact h.2 (by rw [succ_eq_add_one]; exact ha)
  have hTm' : ∀ a, a < upsilon (ξ' + 1) → a ∈ Tset (upsilon ξ') := by
    intro a ha
    have h := upsilon_succ_T ξ' (by rw [succ_eq_add_one]; exact hu1') a (ha.trans hu1')
    rw [if_neg hξ'0] at h
    exact h.2 (by rw [succ_eq_add_one]; exact ha)
  -- the level of `x`
  obtain ⟨k, hk1, hPk, hnPk⟩ := mwLevel hE hnP
  obtain ⟨β, hβx⟩ := hPk
  have hkx : veblen (k : Ordinal.{0}) x ≠ x := fun h => hnPk (vzP_succ.2 h)
  have hβlt : β < x := by
    refine lt_of_le_of_ne (hβx ▸ right_le_veblen _ _) fun e => hkx ?_
    rw [← e] at hβx ⊢; rw [hβx]
  have hτβ : upsilon ξ < β := by
    by_contra hle
    push Not at hle
    have h2 := (veblen_le_veblen_iff_right (o := (k : Ordinal.{0}))).2 hle
    rw [hβx, hτSC.veblen_right (ph_nat_lt hτSC k)] at h2
    exact absurd hτx (not_lt.2 h2)
  have hβP : ¬ VzP (k + 1) β := by
    intro hP
    rw [vzP_succ.1 hP] at hβx
    exact absurd hβx hβlt.ne
  have hkβ : (k : Ordinal.{0}) < β := (ph_nat_lt hτSC k).trans hτβ
  have hβne : veblen (k : Ordinal.{0}) β ≠ β := fun h => hβP (vzP_succ.2 h)
  set η := phInd k (upsilon ξ) β with hη_def
  have hηβ : η ≤ β := Cd.cdOtp_le_self _ β
  have hηT : η ∈ Tset (upsilon ξ) := hTm η ((hηβ.trans_lt hβlt).trans hx2)
  have hη1 : η < Om1 := ((hηβ.trans_lt hβlt).trans hx2).trans hu1
  have hβL : β < Nc.ncL S ω := hβlt.trans hxL
  have hηL : η < Nc.ncL S ω := hηβ.trans_lt hβL
  -- the image
  obtain ⟨hτβ', hβP', hind⟩ := mwInd_move (n := n) hk1 hτSC hBξ hτβ hβP hXSC (hβlt.trans hxX) hLw
  have hBx : Bc.bcB S n x = veblen (k : Ordinal.{0}) (Bc.bcB S n β) := by
    rw [← hβx]; exact (mwB_veblen_nat (k := n) (mvD_of_lt hβL) hkβ hβne).2
  have hhi' : Bc.bcB S n x < upsilon (ξ' + 1) := by
    rw [← hBξ1]; exact (Bc.bcB_lt_iff hxL hτ1L).2 hx2
  have hBηβ : Bc.bcB S n η ≤ Bc.bcB S n β := Tp.tpB_le hβL hηβ
  have hBβx : Bc.bcB S n β < Bc.bcB S n x := (Bc.bcB_lt_iff hβL hxL).2 hβlt
  have hBηT : phInd k (upsilon ξ') (Bc.bcB S n β) ∈ Tset (upsilon ξ') := by
    rw [hind]; exact hTm' _ ((hBηβ.trans_lt hBβx).trans hhi')
  have hBη1 : phInd k (upsilon ξ') (Bc.bcB S n β) < Om1 := by
    rw [hind]; exact ((hBηβ.trans_lt hBβx).trans hhi').trans hu1'
  -- the case split moves
  have hvη : MvD S (veblen (k : Ordinal.{0}) η) := by
    refine mvD_of_lt (lt_of_le_of_lt ?_ hxL)
    rw [← hβx]; exact veblen_le_veblen_iff_right.2 hηβ
  have hcase : (η = 0 ∨ (upsilon ξ < η ∧ VzP (k + 1) η)) ↔
      (Bc.bcB S n η = 0 ∨ (upsilon ξ' < Bc.bcB S n η ∧ VzP (k + 1) (Bc.bcB S n η))) := by
    have h0 : η = 0 ↔ Bc.bcB S n η = 0 := by
      constructor
      · intro h; rw [h, Bc.bcB_zero]
      · intro h
        by_contra hne
        have := (Bc.bcB_lt_iff (k := n) (Lw.lw_L_SC S ω).1 hηL).2 (pos_iff_ne_zero.2 hne)
        rw [Bc.bcB_zero, h] at this
        exact lt_irrefl _ this
    have hτη : upsilon ξ < η ↔ upsilon ξ' < Bc.bcB S n η := by
      rw [← hBξ]; exact (Bc.bcB_lt_iff hτL hηL).symm
    have hP : upsilon ξ < η → (VzP (k + 1) η ↔ VzP (k + 1) (Bc.bcB S n η)) := fun h =>
      (mwB_vzP_iff (k := n) (mvD_of_lt hηL) ((ph_nat_lt hτSC k).trans h) hvη).symm
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl (h0.1 h)
      · exact Or.inr ⟨hτη.1 h1, (hP h1).1 h2⟩
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl (h0.2 h)
      · exact Or.inr ⟨hτη.2 h1, (hP (hτη.2 h1)).2 h2⟩
  have hx2L : x * ((k + 1 : ℕ) : Ordinal.{0}) < Nc.ncL S ω := mw_mul_nat_lt hxL _
  by_cases hcd : η = 0 ∨ (upsilon ξ < η ∧ VzP (k + 1) η)
  · have hl := mwLhT_fixc hk1 hτSC hτ1 hτβ hβP hηT hη1 hcd
    have hcd' := hcase.1 hcd
    rw [← hind] at hcd'
    have hl' := mwLhT_fixc hk1 hτ'SC hτ'1 hτβ' hβP' hBηT hBη1 hcd'
    rw [hβx] at hl
    rw [hl, mwB_mul_nat hxL, hBx, hl']
  · have hl := mwLhT_limc hk1 hτSC hτ1 hτβ hβP hηT hη1 hcd
    have hcd' := mt hcase.2 hcd
    rw [← hind] at hcd'
    have hl' := mwLhT_limc hk1 hτ'SC hτ'1 hτβ' hβP' hBηT hBη1 hcd'
    have hη0 : η ≠ 0 := fun h => hcd (Or.inl h)
    rw [hβx] at hl
    rw [hl, Bc.bcB_add hx2L ((lg_le hη0).trans_lt hηL), mwB_mul_nat hxL, ← Tp.tpLgB hη0 hηL, ← hind,
      hBx, hl']

/-- `SfLhTMove` at the ε-numbers `x` in every `P_{m+1}`, `m < ω` (the fixed points of every `φ_m`, `m < ω`;
all of them are `≥ VzB(υ_ξ) = ϑ^{υ_ξ}(Ω₁·ω)`, `mwNotPw_of_lt`). -/
def MwLhTop (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ ξ ξ' x : Ordinal.{0}, Bc.bcC S n ≤ upsilon ξ → upsilon ξ < x → x < upsilon (ξ + 1) →
    upsilon (ξ + 1) < Bc.bcC S (n + 1) → InE x → Bc.bcB S n (upsilon ξ) = upsilon ξ' →
    Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1) → (∀ m : ℕ, VzP (m + 1) x) →
    Bc.bcB S n (lhT (upsilon ξ) x) = lhT (upsilon ξ') (Bc.bcB S n x)

/-- **`MwLhTop` gives `SfLhTMove`.** -/
theorem mwLhT (h : MwLhTop S) : Sf.SfLhTMove S := by
  intro n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1
  by_cases hall : ∀ m : ℕ, VzP (m + 1) x
  · exact h n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall
  · push Not at hall
    exact mwLhT_fin hc hτx hx2 hξ1lt hE hBξ hBξ1 hall

/-- `MvLhTop` gives `MwLhTop` (`MwLhTop` is the weaker hypothesis). -/
theorem mwLhTop_of_mv (h : MvLhTop S) : MwLhTop S := fun n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 _ =>
  mvLhT h n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1

/-- **The road with `MwLhTop` and `L(ω+1) ≤ ν_C → MwEQtop`.** -/
theorem mwRoad (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MwLhTop S) (htop : Nc.ncL S (ω + 1) ≤ nuC → MwEQtop S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  mvRoad_top hU hO hL hV hN (mwLhT hlh) fun hν => mwEQtop_mv hν (htop hν)

end Googology.Trans.PoR.InaccPsi.R2.Mw

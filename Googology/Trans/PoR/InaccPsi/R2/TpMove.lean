import Googology.Trans.PoR.InaccPsi.R2.CxRoad

/-!
# The arithmetic of the base changes `B_n` on `υ`-indices, the standard pairs above `L(n+1)`

`L(ξ) = Nc.ncL S ξ`, `c_n = L(n+1)` (`Bc.bcC`), `B_n = Bc.bcB S n` (the base change `L(n+1) ↦ L(ω)`
on `[0, L(n+2))`).  A restart index is a nonzero multiple of `ω²`; every index `ζ` is `μ + β` with
`ω² ∣ μ` and `β < ω²` in exactly one way (`tpDecomp`, `tpDecomp_unique`).

* `TpShift S` (**the shift of `B_n` on `υ`-indices**): for every restart `μ` with
  `L(n+1) ≤ υ_μ < L(n+2)` there is a restart `μ'` with `B_n(υ_{μ+β}) = υ_{μ'+β}` for every `β < ω²`
  with `υ_{μ+β} < L(n+2)`;
* `TpShiftSteps S`: the three local steps (S1) `TpRstMove` (restart points go to restart points),
  (S2) `TpSuccMove` (consecutive `υ`-points go to consecutive `υ`-points), (S3) `TpLimMove` (`B_n`
  commutes with the limits `υ_{μ+ω·(j+1)}`); `tpShift_of_steps`: they give the shift;
  `tpRstMove_of_shift`: (S1) is the case `β = 0`;
* `tpUpsRefl` (**the converse**): under `TpShift`, `x ∈ [L(n+1), L(n+2))` is a `υ`-point when `B_n x`
  is one, and `tpShift_inv`: `B_n x = υ_{μ'+β}` (`μ'` a restart, `β < ω²`) gives `x = υ_{μ+β}` with
  `B_n(υ_μ) = υ_{μ'}`;
* `tpStdMoveTop`: `TpShift` gives `CxStdMoveTop` (standard pairs are kept and reflected above
  `L(n+1)`), so `CxStdMove` (`tpStdMove`);
* `tpStdPair`: **`L(ω+1) ≤ ν_C` alone gives `CxStdPair`** (every standard pair with right end below
  `ν_C` is a `<₂`-pair, `pair_std`); so `CxStdPairTop` is not needed (`tpStdPairTop`), and
  `tpEMB2`: `L(ω+1) ≤ ν_C` and `TpShift` give (EMB₂).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cx

/-! ## Index arithmetic -/

theorem tpWW_pos : (0 : Ordinal.{0}) < ω * ω := mul_pos omega0_pos omega0_pos

theorem tpWW_lim : IsSuccLimit ((ω : Ordinal.{0}) * ω) :=
  isSuccLimit_mul_left isSuccLimit_omega0 omega0_pos

/-- Every index is `μ + β` with `ω² ∣ μ`, `β < ω²`. -/
theorem tpDecomp (ζ : Ordinal.{0}) : ∃ μ β, ω * ω ∣ μ ∧ β < ω * ω ∧ ζ = μ + β :=
  ⟨ω * ω * (ζ / (ω * ω)), ζ % (ω * ω), dvd_mul_right _ _, Ordinal.mod_lt _ tpWW_pos.ne',
    (Ordinal.div_add_mod _ _).symm⟩

/-- The decomposition `μ + β` (`ω² ∣ μ`, `β < ω²`) is unique. -/
theorem tpDecomp_unique {μ1 β1 μ2 β2 : Ordinal.{0}} (h1 : ω * ω ∣ μ1) (h2 : ω * ω ∣ μ2)
    (hb1 : β1 < ω * ω) (hb2 : β2 < ω * ω) (h : μ1 + β1 = μ2 + β2) : μ1 = μ2 ∧ β1 = β2 := by
  obtain ⟨p, rfl⟩ := h1
  obtain ⟨q, rfl⟩ := h2
  have hm : β1 = β2 := by
    have e := congrArg (· % (ω * ω)) h
    simp only [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hb1, Ordinal.mod_eq_of_lt hb2] at e
    exact e
  have hd := congrArg (· / (ω * ω)) h
  simp only [Ordinal.mul_add_div _ tpWW_pos.ne', Ordinal.div_eq_zero_of_lt hb1,
    Ordinal.div_eq_zero_of_lt hb2, add_zero] at hd
  exact ⟨by rw [hd], hm⟩

/-- `ω·(j+1) + 1 < ω²`. -/
theorem tpStdIdx_lt (j : ℕ) : ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 < ω * ω := by
  have h : ω * ((j + 1 : ℕ) : Ordinal.{0}) < ω * ω :=
    (mul_lt_mul_iff_right₀ omega0_pos).2 (natCast_lt_omega0 _)
  exact tpWW_lim.add_one_lt h

theorem tpStdIdx_lt' (j : ℕ) : ω * ((j + 1 : ℕ) : Ordinal.{0}) < ω * ω :=
  lt_of_le_of_lt le_self_add (tpStdIdx_lt j)

/-- Below a restart index `λ ≥ ζ'`: the part `μ` of `ζ` (`ω² ∣ μ`, `β < ω²`) is `≥ λ` when `λ ≤ ζ`. -/
theorem tpPart_ge {lam μ β : Ordinal.{0}} (hl : IsRestartIdx lam) (hμ : ω * ω ∣ μ) (hβ : β < ω * ω)
    (h : lam ≤ μ + β) : lam ≤ μ := by
  by_contra hlt
  push Not at hlt
  have := next_mult hμ (ri_iff.1 hl).2 hlt
  exact absurd (h.trans_lt ((add_lt_add_iff_left μ).2 hβ)) (not_lt.2 this)

/-- A multiple `μ ≥ λ` of `ω²` (`λ` a restart index) is a restart index. -/
theorem tpPart_ri {lam μ : Ordinal.{0}} (hl : IsRestartIdx lam) (hμ : ω * ω ∣ μ) (h : lam ≤ μ) :
    IsRestartIdx μ :=
  ri_iff.2 ⟨(lt_of_lt_of_le (pos_iff_ne_zero.2 hl.1) h).ne', hμ⟩

/-- `μ + β < λ` (`λ` a restart index, `β < ω²`, `μ < λ`, `ω² ∣ μ`). -/
theorem tpAdd_lt {lam μ β : Ordinal.{0}} (hl : IsRestartIdx lam) (hμ : ω * ω ∣ μ) (hβ : β < ω * ω)
    (h : μ < lam) : μ + β < lam :=
  lt_of_lt_of_le ((add_lt_add_iff_left μ).2 hβ) (next_mult hμ (ri_iff.1 hl).2 h)

/-- The index of `L(n+1)`: a restart `λ_n` with `L(n+1) = υ_{λ_n}`. -/
theorem tpIdx (S : InaccSeq.{0}) (n : ℕ) : ∃ lam, IsRestartIdx lam ∧ Bc.bcC S n = upsilon lam :=
  Pp.ppL_succ_restart (S := S) n

theorem tpUps_lt_iff {a b : Ordinal.{0}} : upsilon a < upsilon b ↔ a < b :=
  upsilon_normal.strictMono.lt_iff_lt

theorem tpUps_le_iff {a b : Ordinal.{0}} : upsilon a ≤ upsilon b ↔ a ≤ b :=
  upsilon_normal.strictMono.le_iff_le

theorem tpUps_inj {a b : Ordinal.{0}} (h : upsilon a = upsilon b) : a = b :=
  upsilon_normal.strictMono.injective h

variable {S : InaccSeq.{0}}

/-! ## The shift -/

/-- **The shift of `B_n` on `υ`-indices**: each restart block `[υ_μ, υ_{μ+ω²})` above `L(n+1)` is
moved by `B_n` onto a restart block `[υ_{μ'}, υ_{μ'+ω²})`, index by index. -/
def TpShift (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ μ, IsRestartIdx μ → Bc.bcC S n ≤ upsilon μ → upsilon μ < Bc.bcC S (n + 1) →
    ∃ μ', IsRestartIdx μ' ∧ ∀ β, β < ω * ω → upsilon (μ + β) < Bc.bcC S (n + 1) →
      Bc.bcB S n (upsilon (μ + β)) = upsilon (μ' + β)

/-- **(S1) restarts go to restarts**: `B_n(υ_μ) = υ_{μ'}` for a restart `μ'`, for every restart `μ` with
`L(n+1) ≤ υ_μ < L(n+2)`. -/
def TpRstMove (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ μ, IsRestartIdx μ → Bc.bcC S n ≤ upsilon μ → upsilon μ < Bc.bcC S (n + 1) →
    ∃ μ', IsRestartIdx μ' ∧ Bc.bcB S n (upsilon μ) = upsilon μ'

/-- **(S2) consecutive `υ`-points go to consecutive `υ`-points**: `B_n(υ_ζ) = υ_{ζ'}` gives
`B_n(υ_{ζ+1}) = υ_{ζ'+1}`. -/
def TpSuccMove (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ ζ ζ', Bc.bcC S n ≤ upsilon ζ → upsilon (ζ + 1) < Bc.bcC S (n + 1) →
    Bc.bcB S n (upsilon ζ) = upsilon ζ' → Bc.bcB S n (upsilon (ζ + 1)) = upsilon (ζ' + 1)

/-- **(S3) `B_n` commutes with the limits `υ_{μ+ω·(j+1)}`** of `υ_{μ+ω·j+k}`, `k < ω` (`μ` a restart). -/
def TpLimMove (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ μ μ' (j : ℕ), IsRestartIdx μ → Bc.bcC S n ≤ upsilon μ →
    upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) < Bc.bcC S (n + 1) →
    (∀ k : ℕ, Bc.bcB S n (upsilon (μ + ω * (j : Ordinal.{0}) + k)) =
      upsilon (μ' + ω * (j : Ordinal.{0}) + k)) →
    Bc.bcB S n (upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}))) =
      upsilon (μ' + ω * ((j + 1 : ℕ) : Ordinal.{0}))

/-- **The three local steps of the shift**: (S1), (S2), (S3). -/
def TpShiftSteps (S : InaccSeq.{0}) : Prop := TpRstMove S ∧ TpSuccMove S ∧ TpLimMove S

/-- (S1) is the case `β = 0` of the shift. -/
theorem tpRstMove_of_shift (h : TpShift S) : TpRstMove S := by
  intro n μ hμ hlo hhi
  obtain ⟨μ', hμ', hB⟩ := h n μ hμ hlo hhi
  refine ⟨μ', hμ', ?_⟩
  have := hB 0 tpWW_pos (by rwa [add_zero])
  simpa only [add_zero] using this

/-- **The shift from its three local steps.** -/
theorem tpShift_of_steps (h : TpShiftSteps S) : TpShift S := by
  obtain ⟨h1, h2, h3⟩ := h
  intro n μ hμ hlo hhi
  obtain ⟨μ', hμ', hB0⟩ := h1 n μ hμ hlo hhi
  refine ⟨μ', hμ', ?_⟩
  have key : ∀ j k : ℕ, upsilon (μ + ω * (j : Ordinal.{0}) + k) < Bc.bcC S (n + 1) →
      Bc.bcB S n (upsilon (μ + ω * (j : Ordinal.{0}) + k)) =
        upsilon (μ' + ω * (j : Ordinal.{0}) + k) := by
    intro j
    induction j with
    | zero =>
      intro k
      induction k with
      | zero => intro _; simpa using hB0
      | succ k ih =>
        intro hk
        have e1 : μ + ω * ((0 : ℕ) : Ordinal.{0}) + ((k + 1 : ℕ) : Ordinal.{0}) =
            μ + ω * ((0 : ℕ) : Ordinal.{0}) + k + 1 := by rw [Nat.cast_succ, ← add_assoc]
        have e2 : μ' + ω * ((0 : ℕ) : Ordinal.{0}) + ((k + 1 : ℕ) : Ordinal.{0}) =
            μ' + ω * ((0 : ℕ) : Ordinal.{0}) + k + 1 := by rw [Nat.cast_succ, ← add_assoc]
        rw [e1] at hk ⊢; rw [e2]
        have hlt : upsilon (μ + ω * ((0 : ℕ) : Ordinal.{0}) + k) < Bc.bcC S (n + 1) :=
          lt_trans (upsilon_normal.strictMono (lt_add_one _)) hk
        refine h2 n _ _ ?_ hk (ih hlt)
        exact hlo.trans (upsilon_normal.strictMono.monotone (le_self_add.trans le_self_add))
    | succ j ihj =>
      have hjk : ∀ k : ℕ, μ + ω * (j : Ordinal.{0}) + k < μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) := by
        intro k
        rw [Nat.cast_succ, mul_add_one, ← add_assoc]
        exact (add_lt_add_iff_left _).2 (natCast_lt_omega0 k)
      intro k
      induction k with
      | zero =>
        intro hk
        simp only [Nat.cast_zero, add_zero] at hk ⊢
        refine h3 n μ μ' j hμ hlo hk fun k => ihj k ?_
        exact lt_trans (upsilon_normal.strictMono (hjk k)) hk
      | succ k ih =>
        intro hk
        have e1 : μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + ((k + 1 : ℕ) : Ordinal.{0}) =
            μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + k + 1 := by rw [Nat.cast_succ (n := k), ← add_assoc]
        have e2 : μ' + ω * ((j + 1 : ℕ) : Ordinal.{0}) + ((k + 1 : ℕ) : Ordinal.{0}) =
            μ' + ω * ((j + 1 : ℕ) : Ordinal.{0}) + k + 1 := by rw [Nat.cast_succ (n := k), ← add_assoc]
        rw [e1] at hk ⊢; rw [e2]
        have hlt : upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + k) < Bc.bcC S (n + 1) :=
          lt_trans (upsilon_normal.strictMono (lt_add_one _)) hk
        refine h2 n _ _ ?_ hk (ih hlt)
        exact hlo.trans (upsilon_normal.strictMono.monotone (le_self_add.trans le_self_add))
  intro β hβ hβL
  have hj : β / ω < ω := (Ordinal.lt_mul_iff_div_lt omega0_ne_zero).1 hβ
  obtain ⟨j, hj'⟩ := lt_omega0.1 hj
  obtain ⟨k, hk'⟩ := lt_omega0.1 (Ordinal.mod_lt β omega0_ne_zero)
  have eβ : β = ω * (j : Ordinal.{0}) + k := by
    rw [← hj', ← hk']; exact (Ordinal.div_add_mod β ω).symm
  rw [eβ, ← add_assoc] at hβL ⊢
  rw [key j k hβL, add_assoc]

/-- The shift applied at a point of `[L(n+1), L(n+2))`: `x = υ_{μ+β}` with `μ` a restart `≥ λ_n`,
`β < ω²`. -/
theorem tpWin_idx {n : ℕ} {ζ : Ordinal.{0}} (h1 : Bc.bcC S n ≤ upsilon ζ) :
    ∃ μ β, IsRestartIdx μ ∧ β < ω * ω ∧ ζ = μ + β ∧ Bc.bcC S n ≤ upsilon μ := by
  obtain ⟨lam, hlam, hL⟩ := tpIdx S n
  obtain ⟨μ, β, hμ, hβ, rfl⟩ := tpDecomp ζ
  rw [hL] at h1 ⊢
  have hle : lam ≤ μ := tpPart_ge hlam hμ hβ (tpUps_le_iff.1 h1)
  exact ⟨μ, β, tpPart_ri hlam hμ hle, hβ, rfl, tpUps_le_iff.2 hle⟩

/-- In `[L(n+1), L(n+2))`: if `υ_ζ < L(n+2)` then `υ_{ζ+1} < L(n+2)`. -/
theorem tpWin_succ {n : ℕ} {ζ : Ordinal.{0}} (h : upsilon ζ < Bc.bcC S (n + 1)) :
    upsilon (ζ + 1) < Bc.bcC S (n + 1) := by
  obtain ⟨lam, hlam, hL⟩ := tpIdx S (n + 1)
  rw [hL] at h ⊢
  exact tpUps_lt_iff.2 ((ri_lim hlam).add_one_lt (tpUps_lt_iff.1 h))

/-- **The converse of the shift at a point**: under `TpShift`, a point `x ∈ [L(n+1), L(n+2))` whose image
`B_n x` is a `υ`-point is a `υ`-point. -/
theorem tpUpsRefl (h : TpShift S) {n : ℕ} {x : Ordinal.{0}} (h1 : Bc.bcC S n ≤ x)
    (h2 : x < Bc.bcC S (n + 1)) (hU : UpsPt (Bc.bcB S n x)) : UpsPt x := by
  obtain ⟨ξ, hξ1, hξ2⟩ := Lh.lhBracket x
  have hξ0 : 0 < ξ := by
    by_contra h0
    push Not at h0
    rw [nonpos_iff_eq_zero.1 h0, zero_add] at hξ2
    obtain ⟨lam, hlam, hL⟩ := tpIdx S n
    have : upsilon lam < upsilon 1 := (hL ▸ h1).trans_lt hξ2
    have hl1 := tpUps_lt_iff.1 this
    exact hlam.1 (Order.lt_one_iff.1 hl1)
  rcases eq_or_lt_of_le hξ1 with he | hlt
  · rw [← he]; exact upsPt_upsilon hξ0
  exfalso
  -- `ξ ≥ λ_n`
  have hξn : Bc.bcC S n ≤ upsilon ξ := by
    obtain ⟨lam, hlam, hL⟩ := tpIdx S n
    rw [hL] at h1 ⊢
    exact tpUps_le_iff.2 (Order.lt_add_one_iff.1 (tpUps_lt_iff.1 (h1.trans_lt hξ2)))
  obtain ⟨μ, β, hμ, hβ, rfl, hμn⟩ := tpWin_idx hξn
  have hμx : upsilon μ < Bc.bcC S (n + 1) :=
    lt_of_le_of_lt (upsilon_normal.strictMono.monotone le_self_add) (hξ1.trans_lt h2)
  obtain ⟨μ', hμ', hB⟩ := h n μ hμ hμn hμx
  have hz : upsilon (μ + β) < Bc.bcC S (n + 1) := hξ1.trans_lt h2
  have hz1 : upsilon (μ + β + 1) < Bc.bcC S (n + 1) := tpWin_succ hz
  have e0 := hB β hβ hz
  have e1 := hB (β + 1) (tpWW_lim.add_one_lt hβ) (by rw [← add_assoc]; exact hz1)
  rw [← add_assoc] at e1
  have hm := Bc.bcB_mono' S n
  have a1 : Bc.bcB S n (upsilon (μ + β)) < Bc.bcB S n x := hm hz h2 hlt
  have a2 : Bc.bcB S n x < Bc.bcB S n (upsilon (μ + β + 1)) := hm h2 hz1 hξ2
  rw [e0] at a1; rw [e1] at a2
  obtain ⟨ι, -, hι⟩ := upsPt_iff_upsilon.1 hU
  rw [hι] at a1 a2
  have b1 := tpUps_lt_iff.1 a1
  have b2 := tpUps_lt_iff.1 a2
  exact absurd (Order.lt_add_one_iff.1 (by rwa [← add_assoc] at b2)) (not_le.2 b1)

/-- **The converse of the shift**: under `TpShift`, if `x ∈ [L(n+1), L(n+2))` and `B_n x = υ_{μ'+β}` with
`μ'` a restart (or `0`) and `β < ω²`, then `x = υ_{μ+β}` for a restart `μ ≥ λ_n` with the same `β`,
and `B_n(υ_{μ+γ}) = υ_{μ'+γ}` for every `γ < ω²` with `υ_{μ+γ} < L(n+2)`. -/
theorem tpShift_inv (h : TpShift S) {n : ℕ} {x μ' β : Ordinal.{0}} (h1 : Bc.bcC S n ≤ x)
    (h2 : x < Bc.bcC S (n + 1)) (hμ' : μ' = 0 ∨ IsRestartIdx μ') (hβ : β < ω * ω)
    (hx : Bc.bcB S n x = upsilon (μ' + β)) (hpos : 0 < μ' + β) :
    ∃ μ, IsRestartIdx μ ∧ Bc.bcC S n ≤ upsilon μ ∧ x = upsilon (μ + β) ∧
      ∀ γ, γ < ω * ω → upsilon (μ + γ) < Bc.bcC S (n + 1) →
        Bc.bcB S n (upsilon (μ + γ)) = upsilon (μ' + γ) := by
  have hU : UpsPt x := tpUpsRefl h h1 h2 (by rw [hx]; exact upsPt_upsilon hpos)
  obtain ⟨ζ, -, rfl⟩ := upsPt_iff_upsilon.1 hU
  obtain ⟨μ, β0, hμ, hβ0, rfl, hμn⟩ := tpWin_idx h1
  have hμx : upsilon μ < Bc.bcC S (n + 1) :=
    lt_of_le_of_lt (upsilon_normal.strictMono.monotone le_self_add) h2
  obtain ⟨μ'', hμ'', hB⟩ := h n μ hμ hμn hμx
  have e := (hB β0 hβ0 h2).symm.trans hx
  obtain ⟨e1, e2⟩ := tpDecomp_unique (ri_iff.1 hμ'').2 (mult_of hμ') hβ0 hβ (tpUps_inj e)
  subst e1 e2
  exact ⟨μ, hμ, hμn, rfl, hB⟩

/-- **Standard pairs above `L(n+1)` are kept and reflected by `B_n`**, given the shift. -/
theorem tpStdMoveTop (h : TpShift S) : CxStdMoveTop S := by
  intro n x y hx hxy hy
  have hm := Bc.bcB_mono' S n
  constructor
  · rintro ⟨μ, j, hμ, rfl, rfl⟩
    obtain ⟨lam, hlam, hL⟩ := tpIdx S n
    have hle : lam ≤ μ := by
      rw [hL] at hx
      exact tpPart_ge hlam (mult_of hμ) (tpStdIdx_lt' j) (tpUps_le_iff.1 hx)
    have hμr : IsRestartIdx μ := tpPart_ri hlam (mult_of hμ) hle
    have hμn : Bc.bcC S n ≤ upsilon μ := by rw [hL]; exact tpUps_le_iff.2 hle
    have hμx : upsilon μ < Bc.bcC S (n + 1) :=
      lt_of_le_of_lt (upsilon_normal.strictMono.monotone le_self_add) (hxy.trans hy)
    obtain ⟨μ', hμ', hB⟩ := h n μ hμr hμn hμx
    refine ⟨μ', j, Or.inr hμ', hB _ (tpStdIdx_lt' j) (hxy.trans hy), ?_⟩
    have := hB _ (tpStdIdx_lt j) (by rw [← add_assoc]; exact hy)
    rwa [← add_assoc, ← add_assoc] at this
  · rintro ⟨μ', j, hμ', hBx, hBy⟩
    have hpos : 0 < μ' + ω * ((j + 1 : ℕ) : Ordinal.{0}) :=
      lt_of_lt_of_le (mul_pos omega0_pos (by exact_mod_cast Nat.succ_pos j)) le_add_self
    obtain ⟨μ, hμ, -, rfl, hB⟩ :=
      tpShift_inv h hx (hxy.trans hy) hμ' (tpStdIdx_lt' j) hBx hpos
    refine ⟨μ, j, Or.inr hμ, rfl, ?_⟩
    have hy' : upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) < Bc.bcC S (n + 1) :=
      tpWin_succ (hxy.trans hy)
    have e := hB _ (tpStdIdx_lt j) (by rw [← add_assoc]; exact hy')
    rw [← add_assoc, ← add_assoc, ← hBy] at e
    exact ((hm.injOn) hy' hy e).symm

/-- **`CxStdMove` from the shift.** -/
theorem tpStdMove (h : TpShift S) : CxStdMove S := cxStdMove_of_top (tpStdMoveTop h)

/-! ## The standard pairs below `L(ω+1)` -/

/-- **`L(ω+1) ≤ ν_C` gives `CxStdPair`**: a standard pair with right end below `L(ω+1) ≤ ν_C` is a
`<₂`-pair (`pair_std`, D3 below `ν_C`). -/
theorem tpStdPair (hν : Nc.ncL S (ω + 1) ≤ nuC) : CxStdPair S := by
  intro c d _ hd hs
  obtain ⟨μ, j, hμ, rfl, rfl⟩ := hs
  exact pair_std hμ j (hd.trans_le hν)

/-- **`CxStdPairTop` from `L(ω+1) ≤ ν_C`.** -/
theorem tpStdPairTop (hν : Nc.ncL S (ω + 1) ≤ nuC) : CxStdPairTop S :=
  fun c d hcd _ hd hs => tpStdPair hν c d hcd hd hs

/-- **(EMB₂) from `L(ω+1) ≤ ν_C` and the shift.** -/
theorem tpEMB2 (hν : Nc.ncL S (ω + 1) ≤ nuC) (h : TpShift S) : CdEMB2 S :=
  cxEMB2_of_std hν (tpStdMove h) (tpStdPair hν)

end Googology.Trans.PoR.InaccPsi.R2.Tp

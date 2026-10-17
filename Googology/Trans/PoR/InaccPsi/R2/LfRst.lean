import Googology.Trans.PoR.InaccPsi.R2.SHTop
import Googology.Trans.PoR.InaccPsi.R2.Inc1
import Googology.Trans.PoR.InaccPsi.R2.SkelC

/-!
# NU-OMEGA in `R₂^C`: `T_ω` is a restart

`T_ω = sup_k T_k` (`shTw`).  Here:

* `lfLeft_ups` (the outer left end of a nest below `Ω₁` is a `υ`-point; Corollary LEFT, `left`);
* `lfIdx_limit` (**if `υ`-points are cofinal below `υ_ι > 0`, then `ι` is a limit**);
* `lfLimUps_cof` (**below `T_ω`, the `υ`-points with a limit index are cofinal**: the outer left end
  `x` of the least `2`-nest above `c` is a `υ`-point with `1`-nests, hence `υ`-points, cofinal below it);
* `lfTw_ups` (**`T_ω` is a `υ`-point**), `lfTw_restart` (**`T_ω` is a restart**: `T_ω = υ_λ = ρ_λ` with `λ` a
  nonzero multiple of `ω²`).  By `classify`, `T_ω` is a restart or lies in a block
  `(υ_{bot}, υ_{μ+ω(j+1)+1}]` with `μ + ω·j ≤ bot`; two `υ`-points `υ_{L₁} < υ_{L₂}` with limit indices
  in `(υ_{bot}, T_ω)` give `μ + ω·j < L₁ < L₂ ≤ μ + ω·(j+1)`, and no limit lies in
  `(μ + ω·j, μ + ω·(j+1))`.

No new axiom.

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-- The outer left end of a nest (below `Ω₁`) is a `υ`-point. -/
theorem lfLeft_ups {k : ℕ} (hk : 1 ≤ k) {a b : ℕ → Ordinal.{0}} (hN : NestSeq k a b)
    (h1 : b 0 < Om1) : UpsPt (a 0) :=
  left (hN.2 0 (by omega)).2 (hN.2 0 (by omega)).1 ((hN.2 0 (by omega)).1.trans h1)

/-- **If `υ`-points are cofinal below `υ_ι > 0`, then `ι` is a limit.** -/
theorem lfIdx_limit {ι : Ordinal.{0}} (h0 : 0 < upsilon ι)
    (hcof : ∀ c < upsilon ι, ∃ u, c < u ∧ u < upsilon ι ∧ UpsPt u) : IsSuccLimit ι := by
  rcases zero_or_succ_or_isSuccLimit ι with hz | ⟨ν, hν⟩ | hl
  · rw [hz, upsilon_zero] at h0; exact absurd h0 (lt_irrefl _)
  · exfalso
    have hlt : upsilon ν < upsilon ι := upsilon_normal.strictMono (by rw [← hν]; exact Order.lt_succ ν)
    obtain ⟨u, h1, h2, hu⟩ := hcof _ hlt
    obtain ⟨κ, -, rfl⟩ := upsPt_iff_upsilon.1 hu
    have i1 : ν < κ := upsilon_normal.strictMono.lt_iff_lt.1 h1
    have i2 : κ < ι := upsilon_normal.strictMono.lt_iff_lt.1 h2
    rw [← hν] at i2
    exact absurd (Order.lt_succ_iff.1 i2) (not_le.2 i1)
  · exact hl

/-- **Below `T_ω`, the `υ`-points with a limit index are cofinal**: for `c < T_ω` there is a limit `L`
with `c < υ_L < T_ω`. -/
theorem lfLimUps_cof {c : Ordinal.{0}} (hc : c < shTw) :
    ∃ L, IsSuccLimit L ∧ c < upsilon L ∧ upsilon L < shTw := by
  have hTW := shTkA_lt_Tw hc 1
  obtain ⟨a, b, hN, hca, hT⟩ := TkA_attained (hTW.trans shTw_lt_Om1)
  have hb1 : b 0 < Om1 := hT ▸ hTW.trans shTw_lt_Om1
  have hxU : UpsPt (a 0) := lfLeft_ups (by omega) hN hb1
  obtain ⟨L, -, hL⟩ := upsPt_iff_upsilon.1 hxU
  have hcof1 := shCof_mem 0 hN le_rfl (le2_le1 (lv_x2 hN))
  have hlim : IsSuccLimit L := by
    refine lfIdx_limit (hL ▸ hxU.1) fun c' hc' => ?_
    rw [← hL] at hc'
    obtain ⟨a', b', hN', hca', hb'⟩ := hcof1 c' hc'
    refine ⟨a' 0, hca', ?_, lfLeft_ups le_rfl hN' ?_⟩
    · rw [← hL]; exact (lv_xT hN').trans hb'
    · exact hb'.trans ((lv_xT hN).trans hb1)
  refine ⟨L, hlim, ?_, ?_⟩
  · rw [← hL]; exact hca
  · rw [← hL]; exact (lv_xT hN).trans (hT ▸ hTW)

/-- **`T_ω` is a `υ`-point.** -/
theorem lfTw_ups : UpsPt shTw :=
  upsPt_of_cofinal shTw_pos fun c hc => by
    obtain ⟨L, hL, h1, h2⟩ := lfLimUps_cof hc
    exact ⟨upsilon L, h1, h2, upsPt_upsilon (lt_of_le_of_lt zero_le hL.bot_lt)⟩

/-- **`T_ω` is a restart**: `T_ω = υ_λ` for a restart index `λ` (a nonzero multiple of `ω²`). -/
theorem lfTw_restart : ∃ l, IsRestartIdx l ∧ shTw = upsilon l := by
  rcases classify shTw_pos with hr | ⟨μ, j, -, hb, hct⟩
  · exact hr
  exfalso
  obtain ⟨L1, hlim1, i1, i2⟩ := lfLimUps_cof hb
  obtain ⟨L2, -, i3, i4⟩ := lfLimUps_cof i2
  have hb1 : botI μ j < L1 := upsilon_normal.strictMono.lt_iff_lt.1 i1
  have h12 : L1 < L2 := upsilon_normal.strictMono.lt_iff_lt.1 i3
  have h2e : L2 < μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 :=
    upsilon_normal.strictMono.lt_iff_lt.1 (lt_of_lt_of_le i4 hct)
  have hL1 : L1 < μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) :=
    lt_of_lt_of_le h12 (Order.lt_add_one_iff.1 h2e)
  have hLe : μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) = μ + ω * (j : Ordinal.{0}) + ω := by
    rw [omega_mul_succ, add_assoc]
  have he := limit_eq_add_omega hlim1 (lt_of_le_of_lt (botI_ge μ j) hb1)
    (by rw [← hLe]; exact hL1.le)
  rw [he, ← hLe] at hL1
  exact lt_irrefl _ hL1

end Googology.Trans.PoR.InaccPsi.R2

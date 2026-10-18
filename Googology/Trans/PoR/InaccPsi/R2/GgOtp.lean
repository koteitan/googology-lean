import Googology.Trans.PoR.InaccPsi.R2.GgCl

/-!
# The reading over `y` is the substitution `Ω₁ ↦ y` on sums and powers

For a set `C` of ordinals, `cdOtp C m` is the order type of `C ∩ [0, m)` (`Cd.cdOtp`).

* `ggOtp_congr` (it depends only on `C ∩ [0, m)`), `ggOtp_onto` (**every ordinal below `cdOtp C m` is the value
  at some member of `C` below `m`**);
* `ggOtp_add` (**`cdOtp C (x + y) = cdOtp C x + cdOtp C y`** for `x ∈ C`, when `C` is closed under `+` and under
  `w ↦ w - x`), `ggOtp_mul_nat`, `ggOtp_opow` (**`cdOtp C (ω^a) = ω^{cdOtp C a}`** for `a ∈ C`, when moreover
  `C` contains `0` and is closed under `ω^·` and `log_ω`);
* for the codes over a strongly critical `y < Ω₁` (`R2.GgCl`): `ggTh_small` (`Θ_y(c) = c` for `c ≤ y`),
  `ggTh_Om1` (`Θ_y(Ω₁) = y`), `ggTh_add`, `ggTh_opow`, `ggTh_lt`, `ggTh_mono`, `ggTh_onto`, `ggTh_le_onto`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Gg

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

/-- `cdOtp C m` depends only on `C ∩ [0, m)`. -/
theorem ggOtp_congr {C C' : Set Ordinal.{0}} :
    ∀ m, (∀ x < m, x ∈ C ↔ x ∈ C') → cdOtp C m = cdOtp C' m := by
  intro m
  induction m using WellFoundedLT.induction with
  | ind m IH =>
  intro h
  classical
  rw [cdOtp_eq C m, cdOtp_eq C' m]
  refine iSup_congr fun c => ?_
  have e := IH c.1 c.2 (fun x hx => h x (hx.trans c.2))
  by_cases hc : c.1 ∈ C
  · rw [if_pos hc, if_pos ((h c.1 c.2).1 hc), e]
  · rw [if_neg hc, if_neg (fun h' => hc ((h c.1 c.2).2 h'))]

theorem ggOtp_zero (C : Set Ordinal.{0}) : cdOtp C 0 = 0 :=
  le_antisymm (cdOtp_le_self C 0) zero_le

/-- **Every ordinal below `cdOtp C m` is the value at some member of `C` below `m`.** -/
theorem ggOtp_onto (C : Set Ordinal.{0}) :
    ∀ m v, v < cdOtp C m → ∃ c ∈ C, c < m ∧ cdOtp C c = v := by
  intro m
  induction m using WellFoundedLT.induction with
  | ind m IH =>
  intro v hv
  classical
  have hm0 : 0 < m := by
    rcases eq_or_ne m 0 with rfl | h
    · rw [ggOtp_zero] at hv; exact absurd hv (not_lt.2 zero_le)
    · exact pos_iff_ne_zero.2 h
  haveI : Nonempty (Iio m) := ⟨⟨0, hm0⟩⟩
  rw [cdOtp_eq] at hv
  obtain ⟨c, hc⟩ := (lt_ciSup_iff (cdOtp_bdd C m)).1 hv
  by_cases hcC : c.1 ∈ C
  · rw [if_pos hcC] at hc
    rcases (Order.lt_add_one_iff.1 hc).lt_or_eq with hlt | heq
    · obtain ⟨c', hc'C, hc'c, e⟩ := IH c.1 c.2 v hlt
      exact ⟨c', hc'C, hc'c.trans c.2, e⟩
    · exact ⟨c.1, hcC, c.2, heq.symm⟩
  · rw [if_neg hcC] at hc
    exact absurd hc (not_lt.2 zero_le)

/-- **The additive law**: `cdOtp C (x + y) = cdOtp C x + cdOtp C y` for `x ∈ C`. -/
theorem ggOtp_add {C : Set Ordinal.{0}} (hadd : ∀ x z, x ∈ C → z ∈ C → x + z ∈ C)
    (hsub : ∀ x w, x ∈ C → w ∈ C → x ≤ w → w - x ∈ C) {x : Ordinal.{0}} (hx : x ∈ C) :
    ∀ y, cdOtp C (x + y) = cdOtp C x + cdOtp C y := by
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  apply le_antisymm
  · classical
    rw [cdOtp_eq C (x + y)]
    refine ciSup_le' fun c => ?_
    by_cases hc : c.1 ∈ C
    · rw [if_pos hc]
      rcases lt_or_ge c.1 x with hcx | hcx
      · exact (Order.add_one_le_of_lt (cdOtp_lt_of_mem hc hcx)).trans le_self_add
      · obtain ⟨z, hcz⟩ := exists_add_of_le hcx
        have hz : z ∈ C := by
          have := hsub x c.1 hx hc hcx
          rwa [hcz, Ordinal.add_sub_cancel] at this
        have hzy : z < y := by
          have h2 := c.2
          rw [hcz] at h2
          exact (add_lt_add_iff_left _).1 h2
        rw [hcz, IH z hzy, add_assoc]
        exact (add_le_add_iff_left _).2 (Order.add_one_le_of_lt (cdOtp_lt_of_mem hz hzy))
    · rw [if_neg hc]; exact zero_le
  · refine le_of_forall_lt fun v hv => ?_
    rcases lt_or_ge v (cdOtp C x) with h | h
    · exact h.trans_le (cdOtp_mono C le_self_add)
    · obtain ⟨w, rfl⟩ := exists_add_of_le h
      have hw : w < cdOtp C y := (add_lt_add_iff_left _).1 hv
      obtain ⟨z, hzC, hzy, hzw⟩ := ggOtp_onto C y w hw
      have h1 := cdOtp_lt_of_mem (hadd x z hx hzC) ((add_lt_add_iff_left x).2 hzy)
      rwa [IH z hzy, hzw] at h1

theorem ggMem_mul_nat {C : Set Ordinal.{0}} (h0 : (0 : Ordinal.{0}) ∈ C)
    (hadd : ∀ x z, x ∈ C → z ∈ C → x + z ∈ C) {x : Ordinal.{0}} (hx : x ∈ C) :
    ∀ n : ℕ, x * n ∈ C
  | 0 => by rw [Nat.cast_zero, mul_zero]; exact h0
  | n + 1 => by rw [Nat.cast_succ, mul_add_one]; exact hadd _ _ (ggMem_mul_nat h0 hadd hx n) hx

/-- `cdOtp C (x·n) = cdOtp C x · n` for `x ∈ C`. -/
theorem ggOtp_mul_nat {C : Set Ordinal.{0}} (h0 : (0 : Ordinal.{0}) ∈ C)
    (hadd : ∀ x z, x ∈ C → z ∈ C → x + z ∈ C)
    (hsub : ∀ x w, x ∈ C → w ∈ C → x ≤ w → w - x ∈ C) {x : Ordinal.{0}} (hx : x ∈ C) :
    ∀ n : ℕ, cdOtp C (x * n) = cdOtp C x * n
  | 0 => by rw [Nat.cast_zero, mul_zero, mul_zero, ggOtp_zero]
  | n + 1 => by
    rw [Nat.cast_succ, mul_add_one, mul_add_one,
      ggOtp_add hadd hsub (ggMem_mul_nat h0 hadd hx n), ggOtp_mul_nat h0 hadd hsub hx n]

theorem gg_opow_mul_lt (b : Ordinal.{0}) (n : ℕ) : ω ^ b * n < ω ^ succ b := by
  rw [opow_succ]
  exact (mul_lt_mul_iff_right₀ (opow_pos b omega0_pos)).2 (natCast_lt_omega0 n)

/-- **The power law**: `cdOtp C (ω^a) = ω^{cdOtp C a}` for `a ∈ C`. -/
theorem ggOtp_opow {C : Set Ordinal.{0}} (h0 : (0 : Ordinal.{0}) ∈ C)
    (hadd : ∀ x z, x ∈ C → z ∈ C → x + z ∈ C)
    (hsub : ∀ x w, x ∈ C → w ∈ C → x ≤ w → w - x ∈ C) (hpow : ∀ a ∈ C, ω ^ a ∈ C)
    (hlog : ∀ c ∈ C, log ω c ∈ C) : ∀ a ∈ C, cdOtp C (ω ^ a) = ω ^ cdOtp C a := by
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IH =>
  intro ha
  have hmul : ∀ a' ∈ C, a' < a → ∀ n : ℕ, cdOtp C (ω ^ a' * n) = ω ^ cdOtp C a' * n :=
    fun a' ha' hlt n => by rw [ggOtp_mul_nat h0 hadd hsub (hpow a' ha') n, IH a' hlt ha']
  apply le_antisymm
  · classical
    rw [cdOtp_eq C (ω ^ a)]
    refine ciSup_le' fun c => ?_
    by_cases hc : c.1 ∈ C
    · rw [if_pos hc]
      refine Order.add_one_le_of_lt ?_
      rcases eq_or_ne c.1 0 with hc0 | hc0
      · rw [hc0, ggOtp_zero]; exact opow_pos _ omega0_pos
      · have hlt : log ω c.1 < a := (lt_opow_iff_log_lt one_lt_omega0 hc0).1 c.2
        have hla := hlog c.1 hc
        obtain ⟨n, hn⟩ := lt_omega0_opow_succ.1 (lt_opow_succ_log_self one_lt_omega0 c.1)
        calc cdOtp C c.1 < cdOtp C (ω ^ log ω c.1 * n) := cdOtp_lt_of_mem hc hn
          _ = ω ^ cdOtp C (log ω c.1) * n := hmul _ hla hlt n
          _ < ω ^ succ (cdOtp C (log ω c.1)) := gg_opow_mul_lt _ n
          _ ≤ ω ^ cdOtp C a := opow_le_opow_right omega0_pos
              (Order.succ_le_of_lt (cdOtp_lt_of_mem hla hlt))
    · rw [if_neg hc]; exact zero_le
  · refine le_of_forall_lt fun v hv => ?_
    have hpos : 0 < cdOtp C (ω ^ a) := by
      have := cdOtp_lt_of_mem h0 (opow_pos a omega0_pos)
      rwa [ggOtp_zero] at this
    rcases eq_or_ne v 0 with rfl | hv0
    · exact hpos
    · have hu : log ω v < cdOtp C a := (lt_opow_iff_log_lt one_lt_omega0 hv0).1 hv
      obtain ⟨a', ha'C, ha'a, e⟩ := ggOtp_onto C a _ hu
      obtain ⟨n, hn⟩ := lt_omega0_opow_succ.1 (lt_opow_succ_log_self one_lt_omega0 v)
      have hmem := ggMem_mul_nat h0 hadd (hpow a' ha'C) n
      have hlt : ω ^ a' * n < ω ^ a :=
        (gg_opow_mul_lt a' n).trans_le (opow_le_opow_right omega0_pos (Order.succ_le_of_lt ha'a))
      have h1 := cdOtp_lt_of_mem hmem hlt
      rw [hmul a' ha'C ha'a n, e] at h1
      exact hn.trans h1

/-! ## The reading over `y` -/

variable {y : Ordinal.{0}}

theorem gg_set_add (x z : Ordinal.{0}) (hx : x ∈ ggSet y) (hz : z ∈ ggSet y) : x + z ∈ ggSet y :=
  GgCl.add hx hz

/-- `Θ_y(c) = c` for `c ≤ y`. -/
theorem ggTh_small {c : Ordinal.{0}} (hc : c ≤ y) : ggTh y c = c :=
  cdOtp_of_Iio _ c fun _ hx => GgCl.small (lt_of_lt_of_le hx hc)

/-- **`Θ_y(Ω₁) = y`** for a strongly critical `y < Ω₁`. -/
theorem ggTh_Om1 (hy : SC y) (hy1 : y < Om 1) : ggTh y (Om 1) = y := by
  unfold ggTh
  rw [← cdOtp_eq_of_gap (ggSet y) hy1.le fun c hc h1 h2 => absurd (hc.lt_of_lt_Om1 hy h2) (not_lt.2 h1)]
  exact ggTh_small le_rfl

theorem ggTh_lt {c d : Ordinal.{0}} (hc : GgCl y c) (hcd : c < d) : ggTh y c < ggTh y d :=
  cdOtp_lt_of_mem hc hcd

theorem ggTh_mono {c d : Ordinal.{0}} (hcd : c ≤ d) : ggTh y c ≤ ggTh y d := cdOtp_mono _ hcd

theorem ggTh_onto {m v : Ordinal.{0}} (hv : v < ggTh y m) : ∃ c, GgCl y c ∧ c < m ∧ ggTh y c = v := by
  obtain ⟨c, hc, hcm, e⟩ := ggOtp_onto (ggSet y) m v hv
  exact ⟨c, hc, hcm, e⟩

theorem ggTh_le_onto {m v : Ordinal.{0}} (hm : GgCl y m) (hv : v ≤ ggTh y m) :
    ∃ c, GgCl y c ∧ c ≤ m ∧ ggTh y c = v := by
  rcases hv.lt_or_eq with h | h
  · obtain ⟨c, hc, hcm, e⟩ := ggTh_onto h
    exact ⟨c, hc, hcm.le, e⟩
  · exact ⟨m, hm, le_rfl, h.symm⟩

theorem gg_set_sub (hy : SC y) (x w : Ordinal.{0}) (hx : x ∈ ggSet y) (hw : w ∈ ggSet y) (hxw : x ≤ w) :
    w - x ∈ ggSet y := (ggDec hy w hw).1 x hx hxw

/-- **`Θ_y(u + v) = Θ_y(u) + Θ_y(v)`** for a code `u` over a strongly critical `y`. -/
theorem ggTh_add (hy : SC y) {u : Ordinal.{0}} (hu : GgCl y u) (v : Ordinal.{0}) :
    ggTh y (u + v) = ggTh y u + ggTh y v :=
  ggOtp_add gg_set_add (gg_set_sub hy) hu v

/-- **`Θ_y(ω^a) = ω^{Θ_y(a)}`** for a code `a` over a strongly critical `y`. -/
theorem ggTh_opow (hy : SC y) {a : Ordinal.{0}} (ha : GgCl y a) : ggTh y (ω ^ a) = ω ^ ggTh y a :=
  ggOtp_opow (GgCl.zero hy.1) gg_set_add (gg_set_sub hy) (fun _ h => GgCl.opow hy.1 h)
    (fun c hc => (ggDec hy c hc).2) a ha

end Googology.Trans.PoR.InaccPsi.R2.Gg

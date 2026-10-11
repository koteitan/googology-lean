import Googology.Trans.PoR.InaccPsi.R2.RstK

/-!
# The offsets of the restarts up to `Ξ_ω` (ordinal arithmetic)

Notation of the project: a restart index is a nonzero multiple `λ` of `ω²`
(`IsRestartIdx`), the restart is `ρ_λ = υ_λ`, the pair of its first block is
`τ_λ = υ_{λ+ω} <₂ δ_λ = υ_{λ+ω+1}`; `Ξ_1 < Ξ_2 < ⋯` are the nonzero fixed points of `ι ↦ υ_ι` and
`Ξ_ω = sup_n Ξ_n`.  The offset of `λ = λ₀ + ω^e` (last Cantor normal form term, `e ≥ 2`) is
`c(λ) = −1 + e`, and `c*(λ) = c(λ)` for `λ < Ξ_ω`, `c*(Ξ_ω) = Ξ_ω + 1`.

* `ups_lt_Om1`: `υ_ι` is countable for countable `ι`.
* `Xi o = deriv υ o` (Mathlib's derivative: `Xi 0 = 0`, `Xi n = Ξ_n`), `XiW = Xi ω = Ξ_ω`;
  `XiW_lt_Om1`, `XiW_fp`, `lt_XiW`, `fix_bound` (below a `λ < Ξ_ω` the fixed points of `υ` are
  bounded below `λ`).
* `cL λ = sup{k : ω^{1+k} ∣ λ}`; for a restart index this is `−1 + logend(λ)`: `le_cL_iff`
  (`k ≤ c(λ) ⇔ ω^{1+k} ∣ λ`, the supremum is attained), `cL_opow` (`c(ω^e) = e − 1`, Mathlib's
  subtraction, so `1 + c = e`), `cL_fp` (`c(λ) = λ` at a fixed point).
* `off λ` (`= c*(λ)`): `υ_λ + 1` at `λ = Ξ_ω` (where `υ_λ = λ`), `c(λ)` otherwise.
* `cL_sep` (the restarts shortly before `λ` have smaller offsets) and `cL_dense` (restarts with
  offset `≥ z` are cofinal below `λ` when `z < c(λ)`).
* `TopIn O λ`, `topIn`: the input of Lemma TOP (`RstK.top_gen`) at every restart index `λ ≤ Ξ_ω`: a
  term `t` with `t(ρ_λ) = c*(λ)` that no restart above a fixed `x₀` below `λ` realizes.
* `RsIn O λ`, `rsIn`: the input of Lemma RS at every limit restart index `λ ≤ Ξ_ω`: every value
  `z < c*(λ)` is `t(ρ_λ)` for a term `t` realized by restarts cofinal below `λ`.
* `succ_ri`, `off_succ`: a restart index not divisible by `ω³` is `λ₀ + ω²` and has offset `1`.

These are the parts of the project's Theorem OFF-V and of the offset lemma that Theorem BLK^Ξ
uses (the recursive offset `O` of Theorem BLK^O is not formalized; `O = c*` up to `Ξ_ω`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-! ## Countability -/

theorem countable_Iio_of_lt_Om1 {l : Ordinal.{0}} (h : l < Om1) : (Set.Iio l).Countable := by
  rw [← Cardinal.le_aleph0_iff_set_countable, Cardinal.mk_Iio_ordinal, Cardinal.lift_le_aleph0,
    ← Order.lt_succ_iff, Cardinal.succ_aleph0, ← Cardinal.lt_ord, Cardinal.ord_aleph]
  exact h

/-- `υ_ι` is countable for every countable `ι`. -/
theorem ups_lt_Om1 : ∀ ι, ι < Om1 → upsilon ι < Om1 := by
  intro ι
  induction ι using WellFoundedLT.induction with
  | ind ι IH =>
  intro hι
  rcases zero_or_succ_or_isSuccLimit ι with rfl | ⟨j, rfl⟩ | hl
  · rw [upsilon_zero]; exact omega_pos 1
  · rw [succ_eq_add_one]
    exact ups_next_lt (IH j (lt_add_one j) ((le_self_add).trans_lt (succ_eq_add_one j ▸ hι)))
  · have hc := countable_Iio_of_lt_Om1 hι
    haveI : Countable (Set.Iio ι) := hc.to_subtype
    have hs : (⨆ i : Set.Iio ι, upsilon i) < Om1 :=
      Ordinal.iSup_lt_omega_one (fun i => IH i i.2 (i.2.trans hι))
    refine lt_of_le_of_lt ((upsilon_limit hl).2 ?_) hs
    rintro _ ⟨i, hi, rfl⟩
    exact le_ciSup (f := fun i : Set.Iio ι => upsilon i)
      ⟨Om1, by rintro _ ⟨j, rfl⟩; exact (IH j j.2 (j.2.trans hι)).le⟩ ⟨i, hi⟩

/-! ## The fixed points of `υ` -/

/-- `Xi o = deriv υ o`: `Xi 0 = 0`, and `Xi n` (`n ≥ 1`) is `Ξ_n`, the `n`-th nonzero fixed point. -/
noncomputable def Xi (o : Ordinal.{0}) : Ordinal.{0} := deriv upsilon o

/-- `Ξ_ω`. -/
noncomputable def XiW : Ordinal.{0} := Xi ω

theorem Xi_fp (o : Ordinal.{0}) : upsilon (Xi o) = Xi o := deriv_fp upsilon_normal o

theorem Xi_strictMono : StrictMono Xi := deriv_strictMono upsilon

theorem Xi_zero : Xi 0 = 0 := by
  unfold Xi; rw [deriv_zero_right]; exact nfp_eq_self upsilon_zero

theorem fp_iff {a : Ordinal.{0}} : upsilon a = a ↔ ∃ o, Xi o = a :=
  (mem_range_deriv upsilon_normal).symm

theorem Xi_nat_lt_Om1 : ∀ n : ℕ, Xi n < Om1 := by
  intro n
  induction n with
  | zero => rw [Nat.cast_zero, Xi_zero]; exact omega_pos 1
  | succ n ih =>
    rw [Nat.cast_succ]
    unfold Xi
    rw [deriv_add_one, ← iSup_iterate_eq_nfp]
    have ha : deriv upsilon (n : Ordinal.{0}) + 1 < Om1 := Om1_add_lt ih (lt_trans one_lt_omega0
      omega0_lt_omega_one)
    refine Ordinal.iSup_lt_omega_one (fun k => ?_)
    induction k with
    | zero => exact ha
    | succ k ihk => rw [Function.iterate_succ_apply']; exact ups_lt_Om1 _ ihk

theorem XiW_eq : XiW = ⨆ n : ℕ, Xi n := by
  apply le_antisymm
  · unfold XiW Xi
    rw [deriv_limit upsilon isSuccLimit_omega0]
    refine ciSup_le' (fun a => ?_)
    obtain ⟨n, hn⟩ := lt_omega0.1 a.2
    rw [hn]
    exact le_ciSup (f := fun n : ℕ => deriv upsilon n)
      ⟨Xi ω, by rintro _ ⟨k, rfl⟩; exact (Xi_strictMono (natCast_lt_omega0 k)).le⟩ n
  · exact ciSup_le' (fun n => (Xi_strictMono (natCast_lt_omega0 n)).le)

theorem XiW_lt_Om1 : XiW < Om1 := by
  rw [XiW_eq]; exact Ordinal.iSup_lt_omega_one Xi_nat_lt_Om1

theorem XiW_fp : upsilon XiW = XiW := Xi_fp ω

theorem XiW_pos : 0 < XiW := by
  have := Xi_strictMono (omega0_pos : (0 : Ordinal.{0}) < ω)
  rwa [Xi_zero] at this

/-- Below `Ξ_ω` every point is below some `Ξ_n`. -/
theorem lt_XiW {ν : Ordinal.{0}} (h : ν < XiW) : ∃ n : ℕ, ν < Xi n := by
  by_contra hne
  have hne : ∀ n : ℕ, Xi n ≤ ν := fun n => not_lt.1 (fun h' => hne ⟨n, h'⟩)
  have : XiW ≤ ν := by rw [XiW_eq]; exact ciSup_le' hne
  exact absurd h (not_lt.2 this)

/-- The fixed points of `υ` below `Ξ_ω` are the `Ξ_n`. -/
theorem fp_lt_XiW {φ : Ordinal.{0}} (hφ : upsilon φ = φ) (h : φ < XiW) : ∃ n : ℕ, φ = Xi n := by
  obtain ⟨o, rfl⟩ := fp_iff.1 hφ
  have ho : o < ω := Xi_strictMono.lt_iff_lt.1 h
  obtain ⟨n, rfl⟩ := lt_omega0.1 ho
  exact ⟨n, rfl⟩

/-- Below a positive `λ < Ξ_ω` the fixed points of `υ` are bounded below `λ`. -/
theorem fix_bound {l : Ordinal.{0}} (hl0 : 0 < l) (hl : l < XiW) :
    ∃ ν < l, ∀ φ, upsilon φ = φ → φ < l → φ ≤ ν := by
  classical
  obtain ⟨n0, hn0⟩ := lt_XiW hl
  have hex : ∃ n : ℕ, l ≤ Xi n := ⟨n0, hn0.le⟩
  set n := Nat.find hex with hn
  have hln : l ≤ Xi n := Nat.find_spec hex
  rcases n with _ | m
  · rw [Nat.cast_zero, Xi_zero] at hln; exact absurd hl0 (not_lt.2 hln)
  have hm : ¬ l ≤ Xi m := Nat.find_min hex (show m < Nat.find hex by omega)
  refine ⟨Xi m, not_le.1 hm, fun φ hφ hφl => ?_⟩
  obtain ⟨k, rfl⟩ := fp_lt_XiW hφ (hφl.trans hl)
  have hk : (k : Ordinal.{0}) < ((m + 1 : ℕ) : Ordinal.{0}) :=
    Xi_strictMono.lt_iff_lt.1 (lt_of_lt_of_le hφl hln)
  have hkm : k ≤ m := by exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast hk)
  exact Xi_strictMono.monotone (by exact_mod_cast hkm)

/-! ## Restart indices -/

theorem ri_iff {l : Ordinal.{0}} : IsRestartIdx l ↔ l ≠ 0 ∧ ω * ω ∣ l := by
  unfold IsRestartIdx; rw [pow_two]

theorem one_lt_of_ups_fp {φ : Ordinal.{0}} (h0 : 0 < φ) (hφ : upsilon φ = φ) : 1 < φ := by
  have := one_lt_of_upsPt (upsPt_upsilon h0); rwa [hφ] at this

theorem inE_of_fp {φ : Ordinal.{0}} (h0 : 0 < φ) (hφ : upsilon φ = φ) : InE φ := by
  have := upsPt_inE (upsPt_upsilon h0); rwa [hφ] at this

/-- A positive fixed point of `υ` is a restart index. -/
theorem ri_of_fp {φ : Ordinal.{0}} (h0 : 0 < φ) (hφ : upsilon φ = φ) : IsRestartIdx φ := by
  refine ⟨h0.ne', ?_⟩
  have hE := inE_of_fp h0 hφ
  unfold InE at hE
  rw [← hE, ← opow_natCast]
  refine opow_dvd_opow ω ?_
  have h1 := one_lt_of_ups_fp h0 hφ
  have : ((2 : ℕ) : Ordinal.{0}) = 1 + 1 := by norm_num
  rw [this]; exact add_one_le_of_lt h1

/-! ## The offset `c(λ) = max{k : ω^{1+k} ∣ λ}` -/

/-- `c(λ) = sup{k : ω^{1+k} ∣ λ}` (for a restart index the supremum is attained, `cL_dvd`, and equals
`−1 + logend(λ)`). -/
noncomputable def cL (l : Ordinal.{0}) : Ordinal.{0} := sSup {k : Ordinal.{0} | ω ^ (1 + k) ∣ l}

theorem cL_bdd {l : Ordinal.{0}} (hl : l ≠ 0) : BddAbove {k : Ordinal.{0} | ω ^ (1 + k) ∣ l} := by
  refine ⟨l, fun k hk => ?_⟩
  exact le_add_self.trans ((right_le_opow (1 + k) one_lt_omega0).trans (le_of_dvd hl hk))

theorem two_eq : ((2 : ℕ) : Ordinal.{0}) = 1 + 1 := by norm_num

theorem dvd_one_of_ri {l : Ordinal.{0}} (hl : IsRestartIdx l) : ω ^ (1 + 1 : Ordinal.{0}) ∣ l := by
  have := hl.2
  rwa [← opow_natCast, two_eq] at this

theorem dvd_of_le_dvd {l a b : Ordinal.{0}} (hab : a ≤ b) (h : ω ^ b ∣ l) : ω ^ a ∣ l :=
  (opow_dvd_opow ω hab).trans h

theorem le_cL {l k : Ordinal.{0}} (hl : l ≠ 0) (hk : ω ^ (1 + k) ∣ l) : k ≤ cL l :=
  le_csSup (cL_bdd hl) hk

/-- The supremum defining `c(λ)` is attained. -/
theorem cL_dvd {l : Ordinal.{0}} (hl : IsRestartIdx l) : ω ^ (1 + cL l) ∣ l := by
  have hl0 : l ≠ 0 := hl.1
  set S := {k : Ordinal.{0} | ω ^ (1 + k) ∣ l} with hS
  have hbdd := cL_bdd hl0
  have h1S : (1 : Ordinal.{0}) ∈ S := dvd_one_of_ri hl
  have hne : S.Nonempty := ⟨1, h1S⟩
  by_contra hnd
  have hsS : cL l ∉ S := hnd
  -- `c(λ)` is a limit
  have hlim : IsSuccLimit (cL l) := by
    rcases zero_or_succ_or_isSuccLimit (cL l) with h0 | ⟨t, ht⟩ | hlim
    · exact absurd (h0 ▸ (le_cL hl0 h1S)) (not_le.2 zero_lt_one)
    · have htl : t < cL l := by rw [← ht]; exact lt_succ t
      obtain ⟨k', hk'S, htk'⟩ := (lt_csSup_iff hbdd hne).1 htl
      have hk'le : k' ≤ cL l := le_csSup hbdd hk'S
      have : cL l ≤ k' := by rw [← ht]; exact succ_le_of_lt htk'
      exact absurd (le_antisymm hk'le this ▸ hk'S) hsS
    · exact hlim
  have hω : ω ≤ cL l := omega0_le_of_isSuccLimit hlim
  have h1c : 1 + cL l = cL l := one_add_of_omega0_le hω
  set a := ω ^ (1 + cL l) with ha
  have ha0 : a ≠ 0 := (opow_pos _ omega0_pos).ne'
  set r := l % a with hr
  have hr0 : r ≠ 0 := fun h => hnd (dvd_of_mod_eq_zero h)
  have hra : r < a := mod_lt l ha0
  rw [ha, h1c] at hra
  obtain ⟨t, htc, hrt⟩ := (lt_opow_of_isSuccLimit omega0_pos.ne' hlim).1 hra
  obtain ⟨k, hkS, htk⟩ := (lt_csSup_iff hbdd hne).1 htc
  have hkc : k ≤ cL l := le_csSup hbdd hkS
  have hka : ω ^ (1 + k) ∣ a := opow_dvd_opow ω ((add_le_add_iff_left 1).2 hkc)
  have hdl : ω ^ (1 + k) ∣ a * (l / a) + r := by
    rw [hr, div_add_mod]; exact hkS
  have hdr : ω ^ (1 + k) ∣ r := (dvd_add_iff (hka.mul_right _)).1 hdl
  have hle := le_of_dvd hr0 hdr
  have : r < ω ^ (1 + k) := hrt.trans ((opow_lt_opow_iff_right one_lt_omega0).2
    (htk.trans_le le_add_self))
  exact absurd hle (not_le.2 this)

/-- `k ≤ c(λ)` iff `ω^{1+k}` divides `λ`. -/
theorem le_cL_iff {l : Ordinal.{0}} (hl : IsRestartIdx l) (k : Ordinal.{0}) :
    k ≤ cL l ↔ ω ^ (1 + k) ∣ l :=
  ⟨fun h => dvd_of_le_dvd ((add_le_add_iff_left 1).2 h) (cL_dvd hl), le_cL hl.1⟩

theorem one_le_cL {l : Ordinal.{0}} (hl : IsRestartIdx l) : 1 ≤ cL l :=
  (le_cL_iff hl 1).2 (dvd_one_of_ri hl)

theorem cL_le {l : Ordinal.{0}} (hl : IsRestartIdx l) : cL l ≤ l :=
  le_add_self.trans ((right_le_opow _ one_lt_omega0).trans (le_of_dvd hl.1 (cL_dvd hl)))

theorem cL_lt_ups {l : Ordinal.{0}} (hl : IsRestartIdx l) (hfix : upsilon l ≠ l) :
    cL l < upsilon l :=
  lt_of_le_of_lt (cL_le hl) (lt_of_le_of_ne (upsilon_normal.strictMono.id_le l) (Ne.symm hfix))

theorem cL_le_ups {l : Ordinal.{0}} (hl : IsRestartIdx l) : cL l ≤ upsilon l :=
  (cL_le hl).trans (upsilon_normal.strictMono.id_le l)

/-- At a fixed point `λ = υ_λ` (an `ε`-number): `c(λ) = λ`. -/
theorem cL_fp {l : Ordinal.{0}} (h0 : 0 < l) (hfix : upsilon l = l) : cL l = l := by
  have hl := ri_of_fp h0 hfix
  refine le_antisymm (cL_le hl) ((le_cL_iff hl l).2 ?_)
  have hE := inE_of_fp h0 hfix
  unfold InE at hE
  have hω : ω ≤ l := by
    calc ω = ω ^ (1 : Ordinal.{0}) := (opow_one ω).symm
      _ ≤ ω ^ l := opow_le_opow_right omega0_pos (one_lt_of_ups_fp h0 hfix).le
      _ = l := hE
  rw [one_add_of_omega0_le hω, hE]

/-- `c(ω^e) = e − 1` (Mathlib's subtraction: `1 + (e − 1) = e`), for `e ≥ 2`. -/
theorem cL_opow {e : Ordinal.{0}} (he : 2 ≤ e) : cL (ω ^ e) = e - 1 := by
  have he1 : 1 ≤ e := le_trans (by norm_num) he
  have hl : IsRestartIdx (ω ^ e) := by
    refine ⟨(opow_pos _ omega0_pos).ne', ?_⟩
    rw [← opow_natCast]; exact opow_dvd_opow ω (by exact_mod_cast he)
  have h1e : 1 + (e - 1) = e := Ordinal.add_sub_cancel_of_le he1
  refine le_antisymm ?_ ((le_cL_iff hl _).2 (by rw [h1e]))
  have hd : 1 + cL (ω ^ e) ≤ e := (opow_dvd_opow_iff one_lt_omega0).1 (cL_dvd hl)
  have hd' : 1 + cL (ω ^ e) ≤ 1 + (e - 1) := by rw [h1e]; exact hd
  exact (add_le_add_iff_left 1).1 hd'

/-- The restart indices shortly before `λ` have smaller offsets: there is `ν < λ` such that every
restart index `μ ∈ (ν, λ)` has `c(μ) < c(λ)`. -/
theorem cL_sep {l : Ordinal.{0}} (hl : IsRestartIdx l) :
    ∃ ν < l, ∀ μ, IsRestartIdx μ → ν < μ → μ < l → cL μ < cL l := by
  set a := ω ^ (1 + cL l) with ha
  have ha0 : 0 < a := opow_pos _ omega0_pos
  have hal : l = a * (l / a) := (div_mul_cancel ha0.ne' (cL_dvd hl)).symm
  set q := l / a with hq
  have hq0 : q ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hal; exact hl.1 hal
  have hqω : ¬ ω ∣ q := by
    rintro ⟨q', hq'⟩
    have hd : ω ^ (1 + (cL l + 1)) ∣ l := by
      refine ⟨q', ?_⟩
      rw [← add_assoc, ← succ_eq_add_one, opow_succ, ← ha, mul_assoc, ← hq', ← hal]
    have := le_cL hl.1 hd
    exact absurd this (not_le.2 (lt_add_one _))
  obtain ⟨q', hq'⟩ : ∃ q', q = q' + 1 := by
    rcases zero_or_succ_or_isSuccLimit q with h0 | ⟨t, ht⟩ | hlim
    · exact absurd h0 hq0
    · exact ⟨t, by rw [← ht, succ_eq_add_one]⟩
    · exact absurd (isSuccPrelimit_iff_omega0_dvd.1 hlim.isSuccPrelimit) hqω
  refine ⟨a * q', ?_, fun μ hμ hνμ hμl => ?_⟩
  · rw [hal, hq', mul_add_one]; exact lt_add_of_pos_right _ ha0
  · by_contra hge
    have hd : a ∣ μ := (le_cL_iff hμ _).1 (not_lt.1 hge)
    obtain ⟨p, rfl⟩ := hd
    have h1 : q' < p := (mul_lt_mul_iff_right₀ ha0).1 hνμ
    have h2 : p < q' + 1 := by
      have := hμl; rw [hal, hq'] at this; exact (mul_lt_mul_iff_right₀ ha0).1 this
    exact absurd (lt_add_one_iff.1 h2) (not_le.2 h1)

/-- Restart indices with offset `≥ z` are cofinal below `λ` when `1 ≤ z < c(λ)`. -/
theorem cL_dense {l z : Ordinal.{0}} (hl : IsRestartIdx l) (hz1 : 1 ≤ z) (hz : z < cL l) :
    ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ z ≤ cL μ := by
  intro ν hν
  set a := ω ^ (1 + z) with ha
  have ha0 : 0 < a := opow_pos _ omega0_pos
  have hd : ω ^ (1 + (z + 1)) ∣ l := (le_cL_iff hl _).1 (add_one_le_of_lt hz)
  obtain ⟨Q, hQ⟩ := hd
  rw [← add_assoc, ← succ_eq_add_one, opow_succ, ← ha, mul_assoc] at hQ
  have hQ0 : Q ≠ 0 := by
    intro h0; rw [h0, mul_zero, mul_zero] at hQ; exact hl.1 hQ
  have hlimQ : IsSuccLimit (ω * Q) := isSuccLimit_mul_left isSuccLimit_omega0 (pos_iff_ne_zero.2 hQ0)
  have hp : ν / a < ω * Q := (lt_mul_iff_div_lt ha0.ne').1 (by rw [← hQ]; exact hν)
  refine ⟨a * (ν / a + 1), ⟨(mul_pos ha0 (lt_of_le_of_lt zero_le (lt_add_one _))).ne', ?_⟩,
    ?_, ?_, ?_⟩
  · refine dvd_mul_of_dvd_left ?_ _
    rw [← opow_natCast, ha]
    exact opow_dvd_opow ω (by rw [two_eq]; exact (add_le_add_iff_left 1).2 hz1)
  · have := lt_mul_succ_div ν ha0.ne'; rwa [succ_eq_add_one] at this
  · rw [hQ]; exact (mul_lt_mul_iff_right₀ ha0).2 (hlimQ.add_one_lt hp)
  · refine (le_cL_iff ⟨(mul_pos ha0 (lt_of_le_of_lt zero_le (lt_add_one _))).ne', ?_⟩ z).2
      (dvd_mul_right a _)
    refine dvd_mul_of_dvd_left ?_ _
    rw [← opow_natCast, ha]
    exact opow_dvd_opow ω (by rw [two_eq]; exact (add_le_add_iff_left 1).2 hz1)

/-! ## The offset `c*(λ)` -/

/-- `c*(λ)`: `υ_λ + 1` at `λ = Ξ_ω` (there `υ_λ = λ`, so this is `Ξ_ω + 1`), `c(λ)` otherwise. -/
noncomputable def off (l : Ordinal.{0}) : Ordinal.{0} := if l = XiW then upsilon l + 1 else cL l

theorem off_XiW : off XiW = XiW + 1 := by simp [off, XiW_fp]

theorem off_ne {l : Ordinal.{0}} (h : l ≠ XiW) : off l = cL l := by simp [off, h]

theorem off_lt_XiW {l : Ordinal.{0}} (h : l < XiW) : off l = cL l := off_ne h.ne

/-- `c*(λ) ≤ υ_λ + 1`. -/
theorem off_le {l : Ordinal.{0}} (hl : IsRestartIdx l) : off l ≤ upsilon l + 1 := by
  unfold off
  split_ifs
  · exact le_rfl
  · exact (cL_le_ups hl).trans le_self_add

theorem one_le_off {l : Ordinal.{0}} (hl : IsRestartIdx l) : 1 ≤ off l := by
  unfold off
  split_ifs
  · exact le_add_self
  · exact one_le_cL hl

/-- **The input of Lemma TOP at `λ`**: a term `t = tv b k` with `t(ρ_λ) = c*(λ)` (`k < ρ_λ`, `k ≥ 1`
for a constant), and `x₀ < ρ_λ` such that no restart `ρ_μ > x₀` below `ρ_λ` realizes `t`
(`c*(μ) < t(ρ_μ)`). -/
def TopIn (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : Prop :=
  ∃ (m : ℕ) (k x0 : Ordinal.{0}), O l = tm m k (upsilon l) ∧ k < upsilon l ∧ (m = 0 → 1 ≤ k) ∧
    x0 < upsilon l ∧ ∀ μ, IsRestartIdx μ → μ < l → x0 < upsilon μ → O μ < tm m k (upsilon μ)

/-- `TopIn` with the terms `k`, `x + k` only. -/
def TopInB (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : Prop :=
  ∃ b k x0, O l = tv b k (upsilon l) ∧ k < upsilon l ∧ (b = false → 1 ≤ k) ∧ x0 < upsilon l ∧
    ∀ μ, IsRestartIdx μ → μ < l → x0 < upsilon μ → O μ < tv b k (upsilon μ)

theorem TopInB.toTopIn {O : Ordinal.{0} → Ordinal.{0}} {l : Ordinal.{0}} (h : TopInB O l) :
    TopIn O l := by
  obtain ⟨b, k, x0, h1, h2, h3, h4, h5⟩ := h
  refine ⟨if b then 1 else 0, k, x0, by rw [← tv_eq_tm]; exact h1, h2, fun hm => h3 ?_, h4,
    fun μ hμ hμl hx => by rw [← tv_eq_tm]; exact h5 μ hμ hμl hx⟩
  cases b
  · rfl
  · simp at hm

/-- **The offset lemma up to `Ξ_ω`**: the input of Lemma TOP holds at every restart index
`λ ≤ Ξ_ω`.  Cases: `λ = Ξ_ω` (term `x + 1`: every restart below has `c*(μ) ≤ ρ_μ`); `λ` a fixed
point below `Ξ_ω` (term `x`: the fixed points below `λ` are bounded, the other restarts have
`c(μ) < ρ_μ`); otherwise (the constant `c(λ)`, by `cL_sep`). -/
theorem topIn {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlX : l ≤ XiW) : TopInB off l := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρU := upsPt_upsilon hl0
  rcases eq_or_lt_of_le hlX with rfl | hlt
  · refine ⟨true, 1, 0, by rw [off_XiW, tv_true, XiW_fp], one_lt_of_upsPt hρU, by simp,
      hρU.1, fun μ hμ hμl _ => ?_⟩
    rw [off_lt_XiW hμl, tv_true]
    exact lt_of_le_of_lt (cL_le_ups hμ) (lt_add_one _)
  rcases eq_or_ne (upsilon l) l with hfix | hfix
  · obtain ⟨ν, hνl, hν⟩ := fix_bound hl0 hlt
    refine ⟨true, 0, upsilon ν, ?_, hρU.1, by simp, upsilon_normal.strictMono hνl,
      fun μ hμ hμl hνμ => ?_⟩
    · rw [off_lt_XiW hlt, tv_true, add_zero, cL_fp hl0 hfix, hfix]
    · rw [off_lt_XiW (hμl.trans hlt), tv_true, add_zero]
      refine cL_lt_ups hμ (fun hμfix => ?_)
      have := hν μ hμfix hμl
      exact absurd (upsilon_normal.strictMono.monotone this) (not_le.2 hνμ)
  · obtain ⟨ν, hνl, hν⟩ := cL_sep hl
    refine ⟨false, cL l, upsilon ν, by rw [off_lt_XiW hlt, tv_false], cL_lt_ups hl hfix,
      fun _ => one_le_cL hl, upsilon_normal.strictMono hνl, fun μ hμ hμl hνμ => ?_⟩
    rw [off_lt_XiW (hμl.trans hlt), tv_false]
    exact hν μ hμ (upsilon_normal.strictMono.lt_iff_lt.1 hνμ) hμl

/-- **The input of Lemma RS at a limit restart index `λ`**: every `z < c*(λ)` is `t(ρ_λ)` for a term
`t = tv b k` (`k < ρ_λ`) such that restarts `μ` with `t(ρ_μ) ≤ c*(μ)` are cofinal below `λ`. -/
def RsIn (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : Prop :=
  ∀ z < O l, ∃ (m : ℕ) (k : Ordinal.{0}), z = tm m k (upsilon l) ∧ k < upsilon l ∧
    ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ tm m k (upsilon μ) ≤ O μ

/-- `RsIn` with the terms `k`, `x + k` only. -/
def RsInB (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : Prop :=
  ∀ z < O l, ∃ b k, z = tv b k (upsilon l) ∧ k < upsilon l ∧
    ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ tv b k (upsilon μ) ≤ O μ

theorem RsInB.toRsIn {O : Ordinal.{0} → Ordinal.{0}} {l : Ordinal.{0}} (h : RsInB O l) :
    RsIn O l := by
  intro z hz
  obtain ⟨b, k, h1, h2, h3⟩ := h z hz
  exact ⟨if b then 1 else 0, k, by rw [← tv_eq_tm]; exact h1, h2, fun ν hν => by
    obtain ⟨μ, a1, a2, a3, a4⟩ := h3 ν hν
    exact ⟨μ, a1, a2, a3, by rw [← tv_eq_tm]; exact a4⟩⟩

theorem rsIn {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlX : l ≤ XiW) (h2 : 2 ≤ cL l) :
    RsInB off l := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  -- the constants `z < c(λ)`
  have hconst : ∀ z < cL l, ∃ b k, z = tv b k (upsilon l) ∧ k < upsilon l ∧
      ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ tv b k (upsilon μ) ≤ off μ := by
    intro z hz
    refine ⟨false, z, (tv_false z _).symm, lt_of_lt_of_le hz (cL_le_ups hl), fun ν hν => ?_⟩
    have hz' : max z 1 < cL l := max_lt hz (lt_of_lt_of_le one_lt_two h2)
    obtain ⟨μ, hμ, hνμ, hμl, hzμ⟩ := cL_dense hl (le_max_right z 1) hz' ν hν
    refine ⟨μ, hμ, hνμ, hμl, ?_⟩
    rw [tv_false, off_ne (ne_of_lt (lt_of_lt_of_le hμl hlX))]
    exact (le_max_left z 1).trans hzμ
  intro z hz
  rcases eq_or_lt_of_le hlX with rfl | hlt
  · rw [off_XiW] at hz
    rcases lt_or_eq_of_le (lt_add_one_iff.1 hz) with hz' | rfl
    · exact hconst z (by rw [cL_fp XiW_pos XiW_fp]; exact hz')
    · refine ⟨true, 0, by rw [tv_true, add_zero, XiW_fp], hl0.trans_le (upsilon_normal.strictMono.id_le _)
        |>.trans_le' le_rfl, fun ν hν => ?_⟩
      obtain ⟨n, hn⟩ := lt_XiW hν
      have hn0 : 0 < Xi n := lt_of_le_of_lt zero_le hn
      refine ⟨Xi n, ri_of_fp hn0 (Xi_fp n), hn, Xi_strictMono (natCast_lt_omega0 n), ?_⟩
      rw [tv_true, add_zero, off_ne (Xi_strictMono (natCast_lt_omega0 n)).ne, Xi_fp,
        cL_fp hn0 (Xi_fp n)]
  · rw [off_lt_XiW hlt] at hz
    exact hconst z hz

/-! ## Successor restart indices -/

/-- A restart index not divisible by `ω³` is `λ₀ + ω²` with `λ₀ = 0` or a restart index. -/
theorem succ_ri {l : Ordinal.{0}} (hl : IsRestartIdx l) (h2 : cL l < 2) :
    ∃ l0, (l0 = 0 ∨ IsRestartIdx l0) ∧ l = l0 + ω * ω := by
  obtain ⟨q, hq⟩ := (ri_iff.1 hl).2
  have hq0 : q ≠ 0 := by intro h0; rw [h0, mul_zero] at hq; exact hl.1 hq
  have hqω : ¬ ω ∣ q := by
    rintro ⟨q', hq'⟩
    have : (2 : Ordinal.{0}) ≤ cL l := by
      refine (le_cL_iff hl 2).2 ⟨q', ?_⟩
      rw [hq, hq', ← mul_assoc, ← opow_one ω, ← opow_add, ← opow_add, opow_one]
      norm_num
    exact absurd this (not_le.2 h2)
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := by
    rcases zero_or_succ_or_isSuccLimit q with h0 | ⟨t, ht⟩ | hlim
    · exact absurd h0 hq0
    · exact ⟨t, by rw [← ht, succ_eq_add_one]⟩
    · exact absurd (isSuccPrelimit_iff_omega0_dvd.1 hlim.isSuccPrelimit) hqω
  refine ⟨ω * ω * q', ?_, by rw [hq, mul_add_one]⟩
  rcases eq_or_ne q' 0 with rfl | hq'0
  · left; rw [mul_zero]
  · right; exact ri_iff.2 ⟨(mul_pos (mul_pos omega0_pos omega0_pos) (pos_iff_ne_zero.2 hq'0)).ne',
      dvd_mul_right _ _⟩

theorem XiW_cL : cL XiW = XiW := cL_fp XiW_pos XiW_fp

/-- A restart index with `c(λ) < 2` has offset `c*(λ) = 1`. -/
theorem off_succ {l : Ordinal.{0}} (hl : IsRestartIdx l) (h2 : cL l < 2) : off l = 1 := by
  have hne : l ≠ XiW := by
    rintro rfl
    rw [XiW_cL] at h2
    have h2ω : (2 : Ordinal.{0}) < ω := by
      have := natCast_lt_omega0 2; rwa [Nat.cast_ofNat] at this
    exact absurd h2 (not_lt.2 (le_of_lt (lt_of_lt_of_le h2ω
      (by
        have h1 := one_lt_of_ups_fp XiW_pos XiW_fp
        have hE := inE_of_fp XiW_pos XiW_fp
        unfold InE at hE
        calc ω = ω ^ (1 : Ordinal.{0}) := (opow_one ω).symm
          _ ≤ ω ^ XiW := opow_le_opow_right omega0_pos h1.le
          _ = XiW := hE))))
  rw [off_ne hne]
  exact le_antisymm (lt_succ_iff.1 (by simpa [one_add_one_eq_two] using h2)) (one_le_cL hl)

end Googology.Trans.PoR.InaccPsi.R2

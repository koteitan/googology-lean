import Googology.Trans.PoR.InaccPsi.R2.RSX

/-!
# Theorem BLK^O in `R₂^C` below `Φ_1` (the first fixed point of `α ↦ Ξ_α`)

The project's Theorem BLK^O gives the reach `lh(ρ_λ) = δ_λ + O(λ)` with the recursive
offset `O`, and Theorem OFF-V its closed form: for a restart index `λ` that is not a fixed point of
`ι ↦ υ_ι`, `O(λ) = −1 + logend(λ) = c(λ)`; for `λ = Ξ_α` (`γ(λ) = 1`, i.e. `1 ≤ α < Φ_1`),
`O(λ) = ρ_λ + logend(α)`.  Below `Φ_1` these are the terms `k` and `x + k` of `RstK.top_gen` and
`rs_rst`, so the parametric block theorem `blk_gen` applies.

* `lg α = sup{k : ω^k ∣ α}` (= `logend(α)` for `α ≠ 0`, attained: `le_lg_iff`), `lg_sep`, `lg_dense`;
  `one_add_cL` (`1 + c(λ) = logend(λ)`: the offset `c` of `Off` is the paper's `−1 + logend(λ)`).
* `Xi_lt_Om1`, `Phi1 = nfp Ξ 1` (`Phi1_fp`, `lt_Xi`: `α < Ξ_α` for `1 ≤ α < Φ_1`, `Phi1_lt_Om1`,
  `XiW_lt_Phi1`); `xiInv`.
* `offP λ` = `ρ_λ + lg(α)` at `λ = Ξ_α`, `c(λ)` otherwise; `offP_eq_off` (it agrees with `c*` up to
  `Ξ_ω`); `topInP`, `rsInP` (the inputs of Lemmas TOP and RS below `Φ_1`), `specPhi`.
* `blkPhi` (**Theorem BLK^O below `Φ_1`**) and `reach_XiA` (`lh(Ξ_α) = δ + Ξ_α + logend(α)`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-! ## `logend` -/

/-- `lg α = sup{k : ω^k ∣ α}`: for `α ≠ 0` the exponent of the last Cantor normal form term. -/
noncomputable def lg (a : Ordinal.{0}) : Ordinal.{0} := sSup {k : Ordinal.{0} | ω ^ k ∣ a}

theorem lg_bdd {a : Ordinal.{0}} (ha : a ≠ 0) : BddAbove {k : Ordinal.{0} | ω ^ k ∣ a} :=
  ⟨a, fun k hk => (right_le_opow k one_lt_omega0).trans (le_of_dvd ha hk)⟩

theorem le_lg {a k : Ordinal.{0}} (ha : a ≠ 0) (hk : ω ^ k ∣ a) : k ≤ lg a :=
  le_csSup (lg_bdd ha) hk

theorem lg_dvd {a : Ordinal.{0}} (ha : a ≠ 0) : ω ^ lg a ∣ a := by
  set S := {k : Ordinal.{0} | ω ^ k ∣ a} with hS
  have hbdd := lg_bdd ha
  have h0S : (0 : Ordinal.{0}) ∈ S := by
    show ω ^ (0 : Ordinal.{0}) ∣ a; rw [opow_zero]; exact one_dvd a
  have hne : S.Nonempty := ⟨0, h0S⟩
  by_contra hnd
  have hsS : lg a ∉ S := hnd
  have hlim : IsSuccLimit (lg a) := by
    rcases zero_or_succ_or_isSuccLimit (lg a) with h0 | ⟨t, ht⟩ | hlim
    · exact absurd (by rw [h0]; exact h0S) hsS
    · have htl : t < lg a := by rw [← ht]; exact lt_succ t
      obtain ⟨k', hk'S, htk'⟩ := (lt_csSup_iff hbdd hne).1 htl
      have hk'le : k' ≤ lg a := le_csSup hbdd hk'S
      have : lg a ≤ k' := by rw [← ht]; exact succ_le_of_lt htk'
      exact absurd (le_antisymm hk'le this ▸ hk'S) hsS
    · exact hlim
  set b := ω ^ lg a with hb
  have hb0 : b ≠ 0 := (opow_pos _ omega0_pos).ne'
  set r := a % b with hr
  have hr0 : r ≠ 0 := fun h => hnd (dvd_of_mod_eq_zero h)
  have hrb : r < b := mod_lt a hb0
  obtain ⟨t, htc, hrt⟩ := (lt_opow_of_isSuccLimit omega0_pos.ne' hlim).1 hrb
  obtain ⟨k, hkS, htk⟩ := (lt_csSup_iff hbdd hne).1 htc
  have hkc : k ≤ lg a := le_csSup hbdd hkS
  have hkb : ω ^ k ∣ b := opow_dvd_opow ω hkc
  have hdl : ω ^ k ∣ b * (a / b) + r := by rw [hr, div_add_mod]; exact hkS
  have hdr : ω ^ k ∣ r := (dvd_add_iff (hkb.mul_right _)).1 hdl
  have hle := le_of_dvd hr0 hdr
  have : r < ω ^ k := hrt.trans ((opow_lt_opow_iff_right one_lt_omega0).2 htk)
  exact absurd hle (not_le.2 this)

theorem le_lg_iff {a : Ordinal.{0}} (ha : a ≠ 0) (k : Ordinal.{0}) : k ≤ lg a ↔ ω ^ k ∣ a :=
  ⟨fun h => (opow_dvd_opow ω h).trans (lg_dvd ha), le_lg ha⟩

theorem lg_le {a : Ordinal.{0}} (ha : a ≠ 0) : lg a ≤ a :=
  (right_le_opow _ one_lt_omega0).trans (le_of_dvd ha (lg_dvd ha))

theorem lg_nat {n : ℕ} (hn : n ≠ 0) : lg (n : Ordinal.{0}) = 0 := by
  have hn' : (n : Ordinal.{0}) ≠ 0 := by exact_mod_cast hn
  by_contra h0
  have h1 : (1 : Ordinal.{0}) ≤ lg n := one_le_iff_ne_zero.2 h0
  have hd := (le_lg_iff hn' 1).1 h1
  rw [opow_one] at hd
  exact absurd (le_of_dvd hn' hd) (not_le.2 (natCast_lt_omega0 n))

theorem lg_omega : lg (ω : Ordinal.{0}) = 1 := by
  have hω : (ω : Ordinal.{0}) ≠ 0 := omega0_pos.ne'
  refine le_antisymm ?_ ((le_lg_iff hω 1).2 (by rw [opow_one]))
  by_contra hlt
  have h2 : (1 : Ordinal.{0}) + 1 ≤ lg ω := add_one_le_of_lt (not_le.1 hlt)
  have hd := (le_lg_iff hω _).1 h2
  rw [opow_add, opow_one] at hd
  exact absurd (le_of_dvd hω hd)
    (not_le.2 (lt_mul_of_one_lt_right omega0_pos one_lt_omega0))

theorem lg_sep {a : Ordinal.{0}} (ha : a ≠ 0) :
    ∃ β0 < a, ∀ β, β0 < β → β < a → lg β < lg a := by
  set b := ω ^ lg a with hb
  have hb0 : 0 < b := opow_pos _ omega0_pos
  have hab : a = b * (a / b) := (div_mul_cancel hb0.ne' (lg_dvd ha)).symm
  set q := a / b with hq
  have hq0 : q ≠ 0 := by intro h0; rw [h0, mul_zero] at hab; exact ha hab
  have hqω : ¬ ω ∣ q := by
    rintro ⟨q', hq'⟩
    have hd : ω ^ (lg a + 1) ∣ a := by
      refine ⟨q', ?_⟩
      rw [← succ_eq_add_one, opow_succ, ← hb, mul_assoc, ← hq', ← hab]
    exact absurd (le_lg ha hd) (not_le.2 (lt_add_one _))
  obtain ⟨q', hq'⟩ : ∃ q', q = q' + 1 := by
    rcases zero_or_succ_or_isSuccLimit q with h0 | ⟨t, ht⟩ | hlim
    · exact absurd h0 hq0
    · exact ⟨t, by rw [← ht, succ_eq_add_one]⟩
    · exact absurd (isSuccPrelimit_iff_omega0_dvd.1 hlim.isSuccPrelimit) hqω
  refine ⟨b * q', ?_, fun β hνβ hβa => ?_⟩
  · rw [hab, hq', mul_add_one]; exact lt_add_of_pos_right _ hb0
  · have hβ0 : β ≠ 0 := (lt_of_le_of_lt zero_le hνβ).ne'
    by_contra hge
    have hd : b ∣ β := (le_lg_iff hβ0 _).1 (not_lt.1 hge)
    obtain ⟨p, rfl⟩ := hd
    have h1 : q' < p := (mul_lt_mul_iff_right₀ hb0).1 hνβ
    have h2 : p < q' + 1 := by
      have := hβa; rw [hab, hq'] at this; exact (mul_lt_mul_iff_right₀ hb0).1 this
    exact absurd (lt_add_one_iff.1 h2) (not_le.2 h1)

theorem lg_dense {a k : Ordinal.{0}} (ha : a ≠ 0) (hk : k < lg a) :
    ∀ ν < a, ∃ β, ν < β ∧ β < a ∧ k ≤ lg β := by
  intro ν hν
  set b := ω ^ k with hb
  have hb0 : 0 < b := opow_pos _ omega0_pos
  obtain ⟨Q, hQ⟩ := (le_lg_iff ha (k + 1)).1 (add_one_le_of_lt hk)
  rw [← succ_eq_add_one, opow_succ, ← hb, mul_assoc] at hQ
  have hQ0 : Q ≠ 0 := by intro h0; rw [h0, mul_zero, mul_zero] at hQ; exact ha hQ
  have hlimQ : IsSuccLimit (ω * Q) := isSuccLimit_mul_left isSuccLimit_omega0 (pos_iff_ne_zero.2 hQ0)
  have hp : ν / b < ω * Q := (lt_mul_iff_div_lt hb0.ne').1 (by rw [← hQ]; exact hν)
  have hβ0 : b * (ν / b + 1) ≠ 0 := (mul_pos hb0 (lt_of_le_of_lt zero_le (lt_add_one _))).ne'
  refine ⟨b * (ν / b + 1), ?_, ?_, (le_lg_iff hβ0 k).2 (dvd_mul_right b _)⟩
  · have := lt_mul_succ_div ν hb0.ne'; rwa [succ_eq_add_one] at this
  · rw [hQ]; exact (mul_lt_mul_iff_right₀ hb0).2 (hlimQ.add_one_lt hp)

/-- For a restart index: `1 + c(λ) = logend(λ)`, i.e. `c(λ) = −1 + logend(λ)`. -/
theorem one_add_cL {l : Ordinal.{0}} (hl : IsRestartIdx l) : 1 + cL l = lg l := by
  refine le_antisymm ((le_lg_iff hl.1 _).2 (cL_dvd hl)) ?_
  have h2 : (1 : Ordinal.{0}) ≤ lg l :=
    (le_lg_iff hl.1 1).2 (dvd_of_le_dvd (by simp) (dvd_one_of_ri hl))
  have he : 1 + (lg l - 1) = lg l := Ordinal.add_sub_cancel_of_le h2
  have hle : lg l - 1 ≤ cL l := (le_cL_iff hl _).2 (by rw [he]; exact lg_dvd hl.1)
  calc lg l = 1 + (lg l - 1) := he.symm
    _ ≤ 1 + cL l := (add_le_add_iff_left 1).2 hle

/-! ## `Ξ_α` for countable `α`, and `Φ_1` -/

theorem Xi_normal : IsNormal Xi := isNormal_deriv upsilon

theorem Xi_lt_Om1 : ∀ o, o < Om1 → Xi o < Om1 := by
  intro o
  induction o using WellFoundedLT.induction with
  | ind o IH =>
  intro ho
  rcases zero_or_succ_or_isSuccLimit o with rfl | ⟨j, rfl⟩ | hl
  · rw [Xi_zero]; exact omega_pos 1
  · have hj : j < Om1 := lt_of_le_of_lt (le_succ j) ho
    unfold Xi
    rw [succ_eq_add_one, deriv_add_one, ← iSup_iterate_eq_nfp]
    have ha : deriv upsilon j + 1 < Om1 := Om1_add_lt (IH j (lt_succ j) hj)
      (lt_trans one_lt_omega0 omega0_lt_omega_one)
    refine Ordinal.iSup_lt_omega_one (fun k => ?_)
    induction k with
    | zero => exact ha
    | succ k ihk => rw [Function.iterate_succ_apply']; exact ups_lt_Om1 _ ihk
  · have hc := countable_Iio_of_lt_Om1 ho
    haveI : Countable (Set.Iio o) := hc.to_subtype
    have hs : (⨆ i : Set.Iio o, Xi i) < Om1 :=
      Ordinal.iSup_lt_omega_one (fun i => IH i i.2 (i.2.trans ho))
    refine lt_of_le_of_lt ((Xi_normal.isLUB_image_Iio_of_isSuccLimit hl).2 ?_) hs
    rintro _ ⟨i, hi, rfl⟩
    exact le_ciSup (f := fun i : Set.Iio o => Xi i)
      ⟨Om1, by rintro _ ⟨j, rfl⟩; exact (IH j j.2 (j.2.trans ho)).le⟩ ⟨i, hi⟩

/-- `Φ_1 = nfp Ξ 1`: the least `α ≥ 1` with `Ξ_α = α`. -/
noncomputable def Phi1 : Ordinal.{0} := nfp Xi 1

theorem Phi1_fp : Xi Phi1 = Phi1 := nfp_fp Xi_normal 1

theorem one_le_Phi1 : 1 ≤ Phi1 := le_nfp _ _

theorem Phi1_pos : 0 < Phi1 := lt_of_lt_of_le zero_lt_one one_le_Phi1

theorem Phi1_ups : upsilon Phi1 = Phi1 := by
  have := Xi_fp Phi1; rwa [Phi1_fp] at this

/-- `α < Ξ_α` for `1 ≤ α < Φ_1`. -/
theorem lt_Xi {a : Ordinal.{0}} (h1 : 1 ≤ a) (h : a < Phi1) : a < Xi a := by
  refine lt_of_le_of_ne (Xi_strictMono.id_le a) (fun e => ?_)
  have : Phi1 ≤ a := nfp_le_fp Xi_strictMono.monotone h1 e.symm.le
  exact absurd h (not_lt.2 this)

theorem Phi1_lt_Om1 : Phi1 < Om1 := by
  unfold Phi1
  rw [← iSup_iterate_eq_nfp]
  refine Ordinal.iSup_lt_omega_one (fun k => ?_)
  induction k with
  | zero => exact lt_trans one_lt_omega0 omega0_lt_omega_one
  | succ k ihk => rw [Function.iterate_succ_apply']; exact Xi_lt_Om1 _ ihk

theorem omega_lt_Xi1 : (ω : Ordinal.{0}) < Xi 1 := by
  have h0 : 0 < Xi 1 := by
    have := Xi_strictMono (zero_lt_one : (0 : Ordinal.{0}) < 1); rwa [Xi_zero] at this
  have hE := inE_of_fp h0 (Xi_fp 1)
  have h1 := one_lt_of_ups_fp h0 (Xi_fp 1)
  unfold InE at hE
  calc (ω : Ordinal.{0}) < ω ^ (2 : Ordinal.{0}) := by
        rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, opow_add, opow_one]
        exact lt_mul_of_one_lt_right omega0_pos one_lt_omega0
    _ ≤ ω ^ Xi 1 := opow_le_opow_right omega0_pos (by
        rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num]; exact add_one_le_of_lt h1)
    _ = Xi 1 := hE

theorem omega_lt_Phi1 : (ω : Ordinal.{0}) < Phi1 :=
  calc (ω : Ordinal.{0}) < Xi 1 := omega_lt_Xi1
    _ ≤ Xi Phi1 := Xi_strictMono.monotone one_le_Phi1
    _ = Phi1 := Phi1_fp

theorem XiW_lt_Phi1 : XiW < Phi1 := by
  have := Xi_strictMono omega_lt_Phi1; rwa [Phi1_fp] at this

/-! ## The inverse of `Ξ` on the fixed points of `υ` -/

noncomputable def xiInv (l : Ordinal.{0}) : Ordinal.{0} := sInf {o | Xi o = l}

theorem xiInv_spec {l : Ordinal.{0}} (h : upsilon l = l) : Xi (xiInv l) = l :=
  csInf_mem (fp_iff.1 h)

theorem xiInv_Xi (o : Ordinal.{0}) : xiInv (Xi o) = o :=
  Xi_strictMono.injective (xiInv_spec (Xi_fp o))

/-! ## The offset below `Φ_1` -/

/-- The offset below `Φ_1` (Theorem OFF-V, levels 0 and 1): `ρ_λ + logend(α)` at `λ = Ξ_α`,
`c(λ)` otherwise. -/
noncomputable def offP (l : Ordinal.{0}) : Ordinal.{0} :=
  if upsilon l = l then upsilon l + lg (xiInv l) else cL l

theorem offP_nf {l : Ordinal.{0}} (h : upsilon l ≠ l) : offP l = cL l := by simp [offP, h]

theorem offP_Xi (o : Ordinal.{0}) : offP (Xi o) = Xi o + lg o := by
  simp [offP, Xi_fp, xiInv_Xi]

theorem cL_le_offP {l : Ordinal.{0}} (hl : IsRestartIdx l) : cL l ≤ offP l := by
  by_cases h : upsilon l = l
  · obtain ⟨o, rfl⟩ := fp_iff.1 h
    rw [offP_Xi, cL_fp (pos_iff_ne_zero.2 hl.1) h]; exact le_self_add
  · rw [offP_nf h]

theorem offP_lt_δ {l : Ordinal.{0}} (hl : IsRestartIdx l) : offP l < upsilon (l + ω + 1) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hU : UpsPt (upsilon (l + ω + 1)) := upsPt_upsilon (lt_of_lt_of_le hl0 (le_self_add.trans
    le_self_add))
  have hlt : upsilon l < upsilon (l + ω + 1) := upsilon_normal.strictMono
    (lt_of_lt_of_le (lt_add_of_pos_right l omega0_pos) le_self_add)
  have hI := indec_of_upsPt hU
  by_cases h : upsilon l = l
  · obtain ⟨o, rfl⟩ := fp_iff.1 h
    rw [offP_Xi]
    have ho : o ≠ 0 := by rintro rfl; rw [Xi_zero] at hl0; exact lt_irrefl 0 hl0
    have hlg : lg o < upsilon (Xi o + ω + 1) :=
      lt_of_le_of_lt ((lg_le ho).trans (Xi_strictMono.id_le o)) (by rwa [Xi_fp] at hlt)
    exact hI.add_lt (by rwa [Xi_fp] at hlt) hlg
  · rw [offP_nf h]; exact lt_of_le_of_lt (cL_le_ups hl) hlt

theorem one_le_offP {l : Ordinal.{0}} (hl : IsRestartIdx l) : 1 ≤ offP l :=
  (one_le_cL hl).trans (cL_le_offP hl)

theorem offP_succ {l : Ordinal.{0}} (hl : IsRestartIdx l) (h2 : cL l < 2) : offP l = 1 := by
  have hnf : upsilon l ≠ l := by
    intro h
    rw [cL_fp (pos_iff_ne_zero.2 hl.1) h] at h2
    have := one_lt_of_ups_fp (pos_iff_ne_zero.2 hl.1) h
    exact absurd h2 (not_lt.2 (by
      rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num]; exact add_one_le_of_lt this))
  rw [offP_nf hnf]
  exact le_antisymm (lt_succ_iff.1 (by simpa [one_add_one_eq_two] using h2)) (one_le_cL hl)

/-- `offP` agrees with `c*` up to `Ξ_ω`. -/
theorem offP_eq_off {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlX : l ≤ XiW) : offP l = off l := by
  by_cases h : upsilon l = l
  · obtain ⟨o, rfl⟩ := fp_iff.1 h
    rw [offP_Xi]
    rcases eq_or_lt_of_le hlX with e | hlt
    · have ho : o = ω := Xi_strictMono.injective e
      rw [e, off_XiW, ho, lg_omega]
    · have ho : o < ω := Xi_strictMono.lt_iff_lt.1 hlt
      obtain ⟨n, rfl⟩ := lt_omega0.1 ho
      have hn : n ≠ 0 := by
        rintro rfl; have := hl.1; simp [Xi_zero] at this
      rw [lg_nat hn, add_zero, off_lt_XiW hlt, cL_fp (pos_iff_ne_zero.2 hl.1) h]
  · rw [offP_nf h]
    rcases eq_or_lt_of_le hlX with e | hlt
    · exact absurd (e ▸ XiW_fp) h
    · rw [off_lt_XiW hlt]

/-- Below a positive `λ` that is not a fixed point of `υ`, the fixed points are bounded below `λ`. -/
theorem fix_bound_gen {l : Ordinal.{0}} (hl0 : 0 < l) (hnf : upsilon l ≠ l) :
    ∃ ν < l, ∀ φ, upsilon φ = φ → φ < l → φ ≤ ν := by
  set A := sInf {o | l ≤ Xi o} with hA
  have hne : {o | l ≤ Xi o}.Nonempty := ⟨l, Xi_strictMono.id_le l⟩
  have hAl : l ≤ Xi A := csInf_mem hne
  have hAl' : l < Xi A := lt_of_le_of_ne hAl (fun e => hnf (by rw [e, Xi_fp]))
  have hmin : ∀ o, Xi o < l → o < A := fun o ho =>
    Xi_strictMono.lt_iff_lt.1 (lt_of_lt_of_le ho hAl)
  have hnot : ∀ o < A, Xi o < l := fun o ho => not_le.1 (fun h =>
    not_lt.2 (csInf_le' (s := {o | l ≤ Xi o}) (show o ∈ {o | l ≤ Xi o} from h)) ho)
  rcases zero_or_succ_or_isSuccLimit A with h0 | ⟨A', hA'⟩ | hlim
  · rw [h0, Xi_zero] at hAl; exact absurd hl0 (not_lt.2 hAl)
  · refine ⟨Xi A', hnot A' (by rw [← hA']; exact lt_succ A'), fun φ hφ hφl => ?_⟩
    obtain ⟨o, rfl⟩ := fp_iff.1 hφ
    have := hmin o hφl
    rw [← hA'] at this
    exact Xi_strictMono.monotone (lt_succ_iff.1 this)
  · obtain ⟨_, ⟨o, ho, rfl⟩, hlo⟩ :=
      (lt_isLUB_iff (Xi_normal.isLUB_image_Iio_of_isSuccLimit hlim)).1 hAl'
    exact absurd (hnot o ho) (not_lt.2 hlo.le)

/-- **The input of Lemma TOP below `Φ_1`.** -/
theorem topInP {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlP : l < Phi1) : TopInB offP l := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρU := upsPt_upsilon hl0
  by_cases hfix : upsilon l = l
  · obtain ⟨α, rfl⟩ := fp_iff.1 hfix
    have hα0 : α ≠ 0 := by rintro rfl; rw [Xi_zero] at hl0; exact lt_irrefl 0 hl0
    have hαP : α < Phi1 := by
      have := hlP; rw [← Phi1_fp] at this; exact Xi_strictMono.lt_iff_lt.1 this
    have hαX : α < Xi α := lt_Xi (one_le_iff_ne_zero.2 hα0) hαP
    obtain ⟨β0, hβ0α, hβ0⟩ := lg_sep hα0
    refine ⟨true, lg α, Xi β0, by rw [offP_Xi, tv_true, Xi_fp], ?_, by simp, ?_,
      fun μ hμ hμl hx0μ => ?_⟩
    · rw [Xi_fp]; exact lt_of_le_of_lt (lg_le hα0) hαX
    · rw [Xi_fp]; exact Xi_strictMono hβ0α
    · rw [tv_true]
      by_cases hμf : upsilon μ = μ
      · obtain ⟨β, rfl⟩ := fp_iff.1 hμf
        rw [offP_Xi, Xi_fp]
        rw [Xi_fp] at hx0μ
        have h1 : β0 < β := Xi_strictMono.lt_iff_lt.1 hx0μ
        have h2 : β < α := Xi_strictMono.lt_iff_lt.1 hμl
        exact (add_lt_add_iff_left _).2 (hβ0 β h1 h2)
      · rw [offP_nf hμf]
        exact lt_of_lt_of_le (cL_lt_ups hμ hμf) le_self_add
  · obtain ⟨ν1, hν1l, hν1⟩ := cL_sep hl
    obtain ⟨ν2, hν2l, hν2⟩ := fix_bound_gen hl0 hfix
    refine ⟨false, cL l, upsilon (max ν1 ν2), by rw [offP_nf hfix, tv_false], cL_lt_ups hl hfix,
      fun _ => one_le_cL hl, upsilon_normal.strictMono (max_lt hν1l hν2l), fun μ hμ hμl hνμ => ?_⟩
    have hνμ' : max ν1 ν2 < μ := upsilon_normal.strictMono.lt_iff_lt.1 hνμ
    have hμf : upsilon μ ≠ μ := fun e =>
      absurd (hν2 μ e hμl) (not_le.2 (lt_of_le_of_lt (le_max_right _ _) hνμ'))
    rw [offP_nf hμf, tv_false]
    exact hν1 μ hμ (lt_of_le_of_lt (le_max_left _ _) hνμ') hμl

/-- **The input of Lemma RS below `Φ_1`.** -/
theorem rsInP {l : Ordinal.{0}} (hl : IsRestartIdx l) (h2 : 2 ≤ cL l) : RsInB offP l := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hconst : ∀ z < cL l, ∃ b k, z = tv b k (upsilon l) ∧ k < upsilon l ∧
      ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ tv b k (upsilon μ) ≤ offP μ := by
    intro z hz
    refine ⟨false, z, (tv_false z _).symm, lt_of_lt_of_le hz (cL_le_ups hl), fun ν hν => ?_⟩
    have hz' : max z 1 < cL l := max_lt hz (lt_of_lt_of_le one_lt_two h2)
    obtain ⟨μ, hμ, hνμ, hμl, hzμ⟩ := cL_dense hl (le_max_right z 1) hz' ν hν
    refine ⟨μ, hμ, hνμ, hμl, ?_⟩
    rw [tv_false]; exact ((le_max_left z 1).trans hzμ).trans (cL_le_offP hμ)
  intro z hz
  by_cases hfix : upsilon l = l
  · obtain ⟨α, rfl⟩ := fp_iff.1 hfix
    have hα0 : α ≠ 0 := by rintro rfl; rw [Xi_zero] at hl0; exact lt_irrefl 0 hl0
    rw [offP_Xi] at hz
    rcases lt_or_ge z (Xi α) with hzl | hlz
    · exact hconst z (by rw [cL_fp hl0 hfix]; exact hzl)
    · have he : Xi α + (z - Xi α) = z := Ordinal.add_sub_cancel_of_le hlz
      have hk : z - Xi α < lg α := by rw [← he] at hz; exact (add_lt_add_iff_left _).1 hz
      refine ⟨true, z - Xi α, by rw [tv_true, Xi_fp, he], ?_, fun ν hν => ?_⟩
      · rw [Xi_fp]; exact lt_of_lt_of_le hk ((lg_le hα0).trans (Xi_strictMono.id_le α))
      · have hαlim : IsSuccLimit α := by
          refine Ordinal.isSuccLimit_iff.2 ⟨hα0, isSuccPrelimit_iff_omega0_dvd.2 ?_⟩
          have := (le_lg_iff hα0 1).1 (one_le_iff_ne_zero.2 (fun h0 => by
            rw [h0] at hk; exact absurd hk (not_lt.2 zero_le)))
          rwa [opow_one] at this
        obtain ⟨_, ⟨β', hβ', rfl⟩, hνβ'⟩ :=
          (lt_isLUB_iff (Xi_normal.isLUB_image_Iio_of_isSuccLimit hαlim)).1 hν
        obtain ⟨β, hβ'β, hβα, hkβ⟩ := lg_dense hα0 hk β' hβ'
        have hβ0 : 0 < Xi β := by
          have := Xi_strictMono (lt_of_le_of_lt zero_le hβ'β); rwa [Xi_zero] at this
        refine ⟨Xi β, ri_of_fp hβ0 (Xi_fp β), hνβ'.trans (Xi_strictMono hβ'β),
          Xi_strictMono hβα, ?_⟩
        rw [tv_true, Xi_fp, offP_Xi]
        exact add_le_add le_rfl hkβ
  · rw [offP_nf hfix] at hz
    exact hconst z hz

/-- `offP` is an offset specification up to `Φ_1`. -/
theorem specPhi : OffSpec offP Phi1 :=
  ⟨(ri_iff.1 (ri_of_fp Phi1_pos Phi1_ups)).2, Phi1_lt_Om1, fun _ hl _ => offP_lt_δ hl,
    fun _ hl _ => one_le_offP hl, fun _ hl hlP => (topInP hl hlP).toTopIn,
    fun _ hl _ h2 => offP_succ hl h2, fun _ hl _ h2 => (rsInP hl h2).toRsIn⟩

/-- **Theorem BLK^O below `Φ_1`** in `R₂^C` (the project's Theorem BLK^O with the closed form of
Theorem OFF-V for the restart indices below `Φ_1`): (i) the `<₂`-pairs with right end below
`Φ_1 = υ_{Φ_1}` are exactly `(υ_{μ+ω·j}, υ_{μ+ω·j+1})`, `j ≥ 1`, `μ < Φ_1` zero or a restart
index; (ii) a restart `ρ_λ` (`λ < Φ_1`) has no `<₁`-predecessor and no `<₂`-successor, and
`{γ : ρ_λ ≤₁ γ} = [ρ_λ, δ_λ + O(λ)]` with `O(Ξ_α) = Ξ_α + logend(α)` and `O(λ) = c(λ)` otherwise;
(iii) every point below `Φ_1` that is not a `υ`-point has its `R₁⁺` reach. -/
theorem blkPhi :
    (∀ c d, c < d → d < Phi1 → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < Phi1 ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < Phi1 →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + offP l)) ∧
    (∀ α < Phi1, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) := by
  have h := blk_gen specPhi
  rw [Phi1_ups] at h
  exact h

/-- `lh(Ξ_α) = δ + Ξ_α + logend(α)` for `1 ≤ α < Φ_1` (`ρ = Ξ_α`); e.g. `δ + ρ + ω` at `Ξ_{ω^ω}`. -/
theorem reach_XiA {α : Ordinal.{0}} (h1 : 1 ≤ α) (hα : α < Phi1) :
    IsReach R2C (Xi α) (upsilon (Xi α + ω + 1) + (Xi α + lg α)) := by
  have h0 : 0 < Xi α := by
    have := Xi_strictMono (lt_of_lt_of_le zero_lt_one h1); rwa [Xi_zero] at this
  have hlP : Xi α < Phi1 := by rw [← Phi1_fp]; exact Xi_strictMono hα
  have h := (blkPhi.2.1 _ (ri_of_fp h0 (Xi_fp α)) hlP).2.2
  rwa [Xi_fp, offP_Xi] at h

end Googology.Trans.PoR.InaccPsi.R2

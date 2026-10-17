import Googology.Trans.PoR.InaccPsi.R2.NcName
import Googology.Trans.PoR.InaccPsi.R2.NmS

/-!
# The `υ`-index of `L(ω)`: `L(ω)` is a restart, and `L(n)` is cofinal in `L(ω)`

`θ = ψ_{Ω₂}(Ω_ω)`, `A_η = Ω_ω + θ·η`, `P(η) = ψ_{Ω₁}(A_η)`; Theorem GEN (`ups_iota`):
`υ_{ι(η)} = P(η)`.  `P' = ψ_{Ω₂}(Ω_ω·2)` (`ncPp`), `η_ξ = Ω_ω + P'·ξ`, so
`L(ξ) = ψ_{Ω₁}(Ω_ω·2 + P'·ξ) = P(η_ξ)` (`ncL_eq_A`).

* `ppIota_add`: if `η + y` is good for every `y < x`, then `ι(η + x) = ι(η) + x`;
* `ppGood_eta`: `η_{m+1} + y` is good for every `y < ω²` (`P'` is in the hull since
  `Ω_ω·2 < A_{η_{m+1}}`);
* `ppIota_step`: `ι(η_{m+1}) + ω² ≤ ι(η_{m+2})` (at least `ω²` many `υ`-points between `L(m+1)` and `L(m+2)`);
* `ppIota_omega_restart`: `ι(η_ω)` is a restart index (a nonzero multiple of `ω²`): every `z < ι(η_ω)` has
  `z + ω² ≤ ι(η_ω)`;
* `ppL_omega_restart` (**`L(ω)` is a restart**): `L(ω) = υ_l` with `l = ι(Ω_ω + P'·ω)` a restart index;
  `ppL_omega_not_tau`: `L(ω)` is not a `τ`-point (the hypothesis (c) of `ncUpper_L`);
* `ppL_lt_succ`, `ppL_lt_omega`, `ppL_cof`, `ppL_mono`: `L(1) < L(2) < ⋯ < L(ω)`, and the `L(n+1)` are cofinal
  in `L(ω)`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Pp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Nc

variable {S : InaccSeq.{0}}

/-- If `η + y` is good for every `y < x`, then `ι(η + x) = ι(η) + x`. -/
theorem ppIota_add (η : Ordinal.{0}) : ∀ x : Ordinal.{0}, (∀ y < x, Bt.Good S (η + y)) →
    iota S (η + x) = iota S η + x := by
  intro x
  induction x using Ordinal.limitRecOn with
  | zero => intro _; simp
  | add_one x ih =>
    intro h
    rw [← add_assoc, iota_good (h x (lt_add_one x)),
      ih (fun y hy => h y (hy.trans (lt_add_one x))), add_assoc]
  | limit l hl ih =>
    intro h
    have hl' : IsSuccLimit (η + l) := isSuccLimit_add η hl
    rw [iota_limit hl']
    haveI : Nonempty (Iio (η + l)) := ⟨⟨η, lt_add_of_pos_right _ hl.bot_lt⟩⟩
    apply le_antisymm
    · refine ciSup_le fun e => ?_
      rcases lt_or_ge e.1 η with he | he
      · exact (iota_mono η e.1 he.le).trans le_self_add
      · obtain ⟨y, hy⟩ := exists_add_of_le he
        have hyl : y < l := by
          have := e.2
          rw [hy] at this
          exact (add_lt_add_iff_left _).1 this
        rw [hy, ih y hyl (fun z hz => h z (hz.trans hyl))]
        gcongr
    · refine le_of_forall_lt fun z hz => ?_
      obtain ⟨y, hyl, hzy⟩ := (lt_add_iff_of_isSuccLimit hl).1 hz
      rw [← ih y hyl (fun z hz => h z (hz.trans hyl))] at hzy
      exact lt_of_lt_of_le hzy (le_ciSup (iota_bdd (η + l)) ⟨η + y, (add_lt_add_iff_left _).2 hyl⟩)

/-- A strongly critical ordinal is above `ω² = ω·ω`. -/
theorem ppSC_ww {γ : Ordinal.{0}} (h : SC γ) : (ω : Ordinal.{0}) * ω < γ := by
  have h1 : (0 : Ordinal.{0}) + 1 < γ := h.add_one_lt h.1
  have h2 : (0 : Ordinal.{0}) + 1 + 1 < γ := h.add_one_lt h1
  have := h.2 0 h.1 _ h2
  rwa [veblen_zero_apply, zero_add, opow_add, opow_one] at this

/-- `P'·k` lies in every hull that contains `P'`. -/
theorem ppPp_mul_mem {a b : Ordinal.{0}} (hP : ncPp S ∈ S.CSet a b) :
    ∀ k : ℕ, ncPp S * (k : Ordinal.{0}) ∈ S.CSet a b := by
  intro k
  induction k with
  | zero => simpa using CSet.zero_mem (S := S) a b
  | succ k ih => rw [Nat.cast_succ, mul_add_one]; exact CSet.add_mem ih hP

/-- `A_{Ω_ω + P'·(m+1) + y} ≥ Ω_ω·2 + P'`. -/
theorem ppA_ge (m : ℕ) (y : Ordinal.{0}) :
    Om ω + Om ω + ncPp S ≤ ConjT.Aη S (Om ω + ncPp S * ((m + 1 : ℕ) : Ordinal.{0}) + y) := by
  unfold ConjT.Aη
  have h1 : ConjT.th S * (Om ω + ncPp S) = Om ω + ncPp S := by
    rw [mul_add, Bt.th_mul_Om_omega, ncTh_mul_Pp]
  have h2 : Om ω + ncPp S ≤ Om ω + ncPp S * ((m + 1 : ℕ) : Ordinal.{0}) + y := by
    refine le_trans ?_ le_self_add
    gcongr
    calc ncPp S = ncPp S * 1 := (mul_one _).symm
      _ ≤ ncPp S * ((m + 1 : ℕ) : Ordinal.{0}) := by
          gcongr; exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
  calc Om ω + Om ω + ncPp S = Om ω + ConjT.th S * (Om ω + ncPp S) := by rw [h1, add_assoc]
    _ ≤ _ := by gcongr

/-- **The points `Ω_ω + P'·(m+1) + y`, `y < ω²`, are good.** -/
theorem ppGood_eta (m : ℕ) {y : Ordinal.{0}} (hy : y < (ω : Ordinal.{0}) * ω) :
    Bt.Good S (Om ω + ncPp S * ((m + 1 : ℕ) : Ordinal.{0}) + y) := by
  set η := Om ω + ncPp S * ((m + 1 : ℕ) : Ordinal.{0}) + y with hη
  set a := ConjT.Aη S η + 1
  set b := S.psi (ConjT.Aη S η) (Om 1)
  have hSC : SC b := SC_psi Low.InR_Om_one _
  have hw2 : (ω : Ordinal.{0}) * ω < b := ppSC_ww hSC
  have hw : (ω : Ordinal.{0}) < b :=
    lt_of_le_of_lt (le_mul_left _ omega0_pos) hw2
  have hΩ : Om ω ∈ S.CSet a b := CSet.Om_mem (CSet.of_lt hw)
  have hΩ2 : Om ω + Om ω ∈ S.CSet a b := CSet.add_mem hΩ hΩ
  have hlt : Om ω + Om ω < a := by
    have h := ppA_ge (S := S) m y
    refine lt_of_lt_of_le ?_ (h.trans (le_self_add))
    exact lt_add_of_pos_right _ (SC_psi (InR_Om_succ 1) _).1
  have hP : ncPp S ∈ S.CSet a b :=
    CSet.psi_mem hlt (InR_Om_succ 1) (CSet.Om_mem (CSet.add_mem (CSet.one_mem a b)
      (CSet.one_mem a b))) hΩ2
  exact CSet.add_mem (CSet.add_mem hΩ (ppPp_mul_mem hP (m + 1))) (CSet.of_lt (hy.trans hw2))

/-- **At least `ω²` many `υ`-points between `L(m+1)` and `L(m+2)`**:
`ι(Ω_ω + P'·(m+1)) + ω² ≤ ι(Ω_ω + P'·(m+2))`. -/
theorem ppIota_step (m : ℕ) :
    iota S (Om ω + ncPp S * ((m + 1 : ℕ) : Ordinal.{0})) + (ω : Ordinal.{0}) * ω ≤
      iota S (Om ω + ncPp S * ((m + 2 : ℕ) : Ordinal.{0})) := by
  rw [← ppIota_add _ _ (fun y hy => ppGood_eta m hy)]
  refine iota_mono _ _ ?_
  have e : ((m + 2 : ℕ) : Ordinal.{0}) = ((m + 1 : ℕ) : Ordinal.{0}) + 1 := Nat.cast_succ (m + 1)
  rw [e, mul_add_one, ← add_assoc]
  gcongr
  exact (ppSC_ww (ncPp_SC S)).le

/-- Below `Ω_ω + P'·ω` every point is below some `Ω_ω + P'·(n+1)`. -/
theorem ppLt_eta_omega {e : Ordinal.{0}} (he : e < Om ω + ncPp S * ω) :
    ∃ n : ℕ, e < Om ω + ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) := by
  have hpos : 0 < ncPp S * ((0 + 1 : ℕ) : Ordinal.{0}) := by
    simpa using (ncPp_SC S).1
  rcases lt_or_ge e (Om ω) with h | h
  · exact ⟨0, lt_of_lt_of_le h le_self_add⟩
  · obtain ⟨d, rfl⟩ := exists_add_of_le h
    have hd : d < ncPp S * ω := (add_lt_add_iff_left _).1 he
    obtain ⟨c, hc, hdc⟩ := (lt_mul_iff_of_isSuccLimit isSuccLimit_omega0).1 hd
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.1 hc
    refine ⟨n, (add_lt_add_iff_left _).2 (lt_of_lt_of_le hdc ?_)⟩
    gcongr; exact_mod_cast Nat.le_succ n

/-- Every `ω²`-step closes: if `z + ω² ≤ s` for every `z < s`, then `ω² ∣ s`. -/
theorem ppDvd_of_add {s : Ordinal.{0}} (h : ∀ z < s, z + (ω : Ordinal.{0}) * ω ≤ s) :
    (ω : Ordinal.{0}) * ω ∣ s := by
  have hw : (ω : Ordinal.{0}) * ω ≠ 0 := (mul_pos omega0_pos omega0_pos).ne'
  rw [Ordinal.dvd_iff_mod_eq_zero]
  by_contra hr
  have hdm := Ordinal.div_add_mod s ((ω : Ordinal.{0}) * ω)
  set q := s / ((ω : Ordinal.{0}) * ω)
  set r := s % ((ω : Ordinal.{0}) * ω)
  have hz : (ω : Ordinal.{0}) * ω * q < s := by
    conv_rhs => rw [← hdm]
    exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 hr)
  have h1 := h _ hz
  rw [← hdm] at h1
  have h2 : (ω : Ordinal.{0}) * ω ≤ r := (add_le_add_iff_left _).1 h1
  exact absurd (Ordinal.mod_lt s hw) (not_lt.2 h2)

/-- **`ι(Ω_ω + P'·ω)` is a restart index.** -/
theorem ppIota_omega_restart : IsRestartIdx (iota S (Om ω + ncPp S * ω)) := by
  have hlim : IsSuccLimit (Om ω + ncPp S * ω) :=
    isSuccLimit_add _ (isSuccLimit_mul_right (ncPp_SC S).1 isSuccLimit_omega0)
  refine ri_iff.2 ⟨(lt_of_lt_of_le zero_lt_one (one_le_iota _)).ne', ppDvd_of_add fun z hz => ?_⟩
  have hz' := hz
  rw [iota_limit hlim] at hz'
  haveI : Nonempty (Iio (Om ω + ncPp S * ω)) := ⟨⟨0, hlim.bot_lt⟩⟩
  obtain ⟨e, he⟩ := (lt_ciSup_iff (iota_bdd _)).1 hz'
  obtain ⟨n, hn⟩ := ppLt_eta_omega e.2
  calc z + (ω : Ordinal.{0}) * ω ≤ iota S e.1 + (ω : Ordinal.{0}) * ω := by gcongr
    _ ≤ iota S (Om ω + ncPp S * ((n + 1 : ℕ) : Ordinal.{0})) + (ω : Ordinal.{0}) * ω := by
        gcongr; exact iota_mono _ _ hn.le
    _ ≤ iota S (Om ω + ncPp S * ((n + 2 : ℕ) : Ordinal.{0})) := ppIota_step n
    _ ≤ iota S (Om ω + ncPp S * ω) := by
        refine iota_mono _ _ ?_
        gcongr; exact (Ordinal.natCast_lt_omega0 _).le

/-- `L(ξ) = υ_{ι(Ω_ω + P'·ξ)}`. -/
theorem ppL_eq_ups (ξ : Ordinal.{0}) : ncL S ξ = upsilon (iota S (Om ω + ncPp S * ξ)) := by
  rw [ncL_eq_A, ups_iota]

/-- **`L(ω)` is a restart**: `L(ω) = υ_l` with `l = ι(Ω_ω + P'·ω)` a restart index. -/
theorem ppL_omega_restart : ∃ l, IsRestartIdx l ∧ ncL S ω = upsilon l :=
  ⟨_, ppIota_omega_restart, ppL_eq_ups ω⟩

/-- **`L(ω)` is not a `τ`-point.** -/
theorem ppL_omega_not_tau : ¬ NcTauPt (ncL S ω) := by
  obtain ⟨l, hl, e⟩ := ppL_omega_restart (S := S)
  rw [e]; exact ncRestart_not_tau hl

/-- `L` is monotone. -/
theorem ppL_mono {ξ ξ' : Ordinal.{0}} (h : ξ ≤ ξ') : ncL S ξ ≤ ncL S ξ' := by
  unfold ncL
  exact (psi_mono Low.InR_Om_one (by gcongr)).1

/-- `L(m+1) < L(m+2)`. -/
theorem ppL_lt_succ (m : ℕ) : ncL S ((m + 1 : ℕ) : Ordinal.{0}) < ncL S ((m + 2 : ℕ) : Ordinal.{0}) := by
  rw [ppL_eq_ups, ppL_eq_ups]
  refine upsilon_normal.strictMono (lt_of_lt_of_le ?_ (ppIota_step m))
  exact lt_add_of_pos_right _ (mul_pos omega0_pos omega0_pos)

/-- `L(m+1) < L(ω)`. -/
theorem ppL_lt_omega (m : ℕ) : ncL S ((m + 1 : ℕ) : Ordinal.{0}) < ncL S ω :=
  lt_of_lt_of_le (ppL_lt_succ m) (ppL_mono (Ordinal.natCast_lt_omega0 _).le)

/-- **The `L(n+1)` are cofinal in `L(ω)`.** -/
theorem ppL_cof : ∀ γ < ncL S ω, ∃ n : ℕ, γ < ncL S ((n + 1 : ℕ) : Ordinal.{0}) := by
  intro γ hγ
  by_contra hall
  push Not at hall
  have hle : ncL S ω ≤ γ := by
    rw [ncL_eq_A]
    have e : Om ω + ncPp S * ω = Om ω + ncPp S * ω + 0 := (add_zero _).symm
    show Nm.Pv S (Om ω + ncPp S * ω) ≤ γ
    refine (Nm.cont_le (S := S) (η0 := Om ω) (X := ncPp S * ω)
      (isSuccLimit_mul_right (ncPp_SC S).1 isSuccLimit_omega0) fun c hc => ?_)
    obtain ⟨n, hn⟩ := ppLt_eta_omega (S := S) ((add_lt_add_iff_left (Om ω)).2 hc)
    have h1 : Nm.Pv S (Om ω + c) ≤ ncL S ((n + 1 : ℕ) : Ordinal.{0}) := by
      rw [ncL_eq_A]
      exact (psi_mono Low.InR_Om_one (by unfold ConjT.Aη; gcongr)).1
    exact h1.trans (hall n)
  exact absurd hγ (not_lt.2 hle)

end Googology.Trans.PoR.InaccPsi.R2.Pp

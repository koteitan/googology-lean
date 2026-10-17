import Googology.Trans.PoR.InaccPsi.R2.LbName
import Googology.Trans.PoR.InaccPsi.R2.NmD

/-!
# The restart reach calculus: codes, the reading `Θ_λ`, the closed points `K_λ`, and `k_λ(Θ_λ(m_λ))`

`θ = ψ_{Ω₂}(Ω_ω)`, `A_η = Ω_ω + θ·η`, `P(η) = ψ_{Ω₁}(A_η)` (`Nm.Pv`), `ι` the index of Theorem GEN
(`υ_{ι(η)} = P(η)`, `Bt.ups_iota`).  A restart index `λ` (a nonzero multiple of `ω²`) has the restart
`ρ_λ = υ_λ` and the first block top `δ_λ = υ_{λ+ω+1}`.

**Definitions** (the data of the docs' restart reach calculus):

* `cdEta S λ` (**the name** `η_λ`): the good `η` with `ι(η) = λ`, so `ρ_λ = P(η_λ)` (`cdEta_pv`);
* `cdExp η` (**the last exponent**): the largest `e` with `ω^e ∣ η`, so `η = η₀ + ω^e` with `ω^e ∣ η₀`
  (`cdExp_decomp`);
* `cdCodeOf S η` (**the code** of a name): `-1 + e` (`cdOff e`: `e - 1` for finite `e`, `e` otherwise)
  when `e = cdExp η < Ω₂`, and the π-code `π_η = ψ_{Ω₂}(A_η)` otherwise; `cdCode S λ` the code `m_λ` of a
  restart;
* `cdHull S λ = Cl(A_{η_λ}, ρ_λ)` (the codes whose constants lie below `ρ_λ`) and `cdTheta S λ m`
  (**the reading** `Θ_λ(m)`): the order type of the codes of `cdHull S λ` below `m` (`cdOtp`);
* `cdClosed λ y` (**`y` is closed relative to `λ`**): `δ_λ ≤ y` and every `α ∈ (ρ_λ, y]` has all its
  `≤₁`-successors at most `y` ("`lh(α) ≤ y`"); `cdK λ` the closed points together with the points
  `≥ max(Ω₁, δ_λ)` (so that the enumeration is total), `cdk λ` (**`k_λ`**) its increasing enumeration;
* `cdRc S λ c = k_λ(Θ_λ(c))` (the value `A^♯_λ(c)` of a code `c` at `λ`) and `cdR S λ = k_λ(Θ_λ(m_λ))`
  (**the predicted long reach** of the corrected calculus).

**Basic properties**: the name exists and is unique for every restart index below a value of `P`
(`cdEta_spec`, `cdEta_unique`, `cdEta_pv`); `cdExp` (`cdExp_dvd`, `cdExp_max`, `cdExp_not_dvd`,
`cdExp_decomp`) and the window lemma `cdWin`; the code is at most the last exponent (`cdCodeOf_le_exp`);
`cdOtp` is monotone, at most its argument, strictly increasing along its set, the identity on initial
segments of its set (`cdOtp_mono`, `cdOtp_le_self`, `cdOtp_lt_of_mem`, `cdOtp_of_Iio`); `Θ_λ(c) = c` for
`c ≤ ρ_λ` and `Θ_λ(Ω₁) = ρ_λ` (`cdTheta_small`, `cdTheta_Om1`); `k_λ` is strictly increasing with values
in `cdK λ`, at least `δ_λ`, closed below `Ω₁` (`cdk_strictMono`, `cdk_mem`, `cdk_ge`, `cdk_closed`);
**every exact reach `r ≥ δ_λ` of `ρ_λ` is closed, hence `r = k_λ(p)` for exactly one `p`**
(`cdClosed_of_reach`, `cdk_index`); on an interval of closed points `k_λ(x) = δ_λ + x` (`cdk_interval`),
so a short code `m_λ ≤ ρ_λ` gives `k_λ(Θ_λ(m_λ)) = δ_λ + m_λ` there (`cdR_short`); the value of a code is
monotone in the code (`cdRc_mono`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Cd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm

/-! ## The last exponent -/

/-- The last exponent of the Cantor normal form: the largest `e` with `ω^e ∣ η` (for `η ≠ 0`). -/
noncomputable def cdExp (η : Ordinal.{0}) : Ordinal.{0} := sSup {e : Ordinal.{0} | ω ^ e ∣ η}

theorem cdExp_bdd {η : Ordinal.{0}} (hη : η ≠ 0) : BddAbove {e : Ordinal.{0} | ω ^ e ∣ η} :=
  ⟨η, fun e he => (right_le_opow e one_lt_omega0).trans (le_of_dvd hη he)⟩

theorem cdExp_nonempty (η : Ordinal.{0}) : ({e : Ordinal.{0} | ω ^ e ∣ η}).Nonempty :=
  ⟨0, by simp⟩

theorem cdExp_max {η e : Ordinal.{0}} (hη : η ≠ 0) (h : ω ^ e ∣ η) : e ≤ cdExp η :=
  le_csSup (cdExp_bdd hη) h

theorem cdExp_lt_dvd {η e : Ordinal.{0}} (hη : η ≠ 0) (he : e < cdExp η) : ω ^ e ∣ η := by
  obtain ⟨e', he', hee'⟩ := (lt_csSup_iff (cdExp_bdd hη) (cdExp_nonempty η)).1 he
  exact (opow_dvd_opow ω hee'.le).trans he'

/-- `ω^{cdExp η} ∣ η`. -/
theorem cdExp_dvd {η : Ordinal.{0}} (hη : η ≠ 0) : ω ^ cdExp η ∣ η := by
  rcases zero_or_succ_or_isSuccLimit (cdExp η) with h0 | ⟨e, he⟩ | hlim
  · rw [h0, opow_zero]; exact one_dvd η
  · have hlt : e < cdExp η := by rw [← he]; exact lt_succ e
    obtain ⟨e', he', hee'⟩ := (lt_csSup_iff (cdExp_bdd hη) (cdExp_nonempty η)).1 hlt
    have hle : cdExp η ≤ e' := by rw [← he]; exact succ_le_of_lt hee'
    exact (opow_dvd_opow ω hle).trans he'
  · by_contra hnd
    have hω0 : ω ^ cdExp η ≠ 0 := (opow_pos _ omega0_pos).ne'
    have hr : η % ω ^ cdExp η ≠ 0 := fun h => hnd (dvd_iff_mod_eq_zero.2 h)
    have hrl : η % ω ^ cdExp η < ω ^ cdExp η := mod_lt η hω0
    obtain ⟨e, he, hre⟩ := (lt_opow_of_isSuccLimit omega0_ne_zero hlim).1 hrl
    have hd : ω ^ e ∣ η := cdExp_lt_dvd hη he
    have hd2 : ω ^ e ∣ ω ^ cdExp η * (η / ω ^ cdExp η) :=
      Dvd.dvd.mul_right (opow_dvd_opow ω he.le) _
    have hdr : ω ^ e ∣ η % ω ^ cdExp η := by
      have e1 := div_add_mod η (ω ^ cdExp η)
      rw [← e1] at hd
      exact (dvd_add_iff hd2).1 hd
    exact absurd (le_of_dvd hr hdr) (not_le.2 hre)

theorem cdExp_not_dvd {η : Ordinal.{0}} (hη : η ≠ 0) : ¬ ω ^ (cdExp η + 1) ∣ η := fun h =>
  absurd (cdExp_max hη h) (not_le.2 (lt_add_one _))

/-- **The last term**: `η = η₀ + ω^e` with `e = cdExp η` and `ω^e ∣ η₀`. -/
theorem cdExp_decomp {η : Ordinal.{0}} (hη : η ≠ 0) :
    ∃ η0, η = η0 + ω ^ cdExp η ∧ ω ^ cdExp η ∣ η0 := by
  have hd := cdExp_dvd hη
  have hnd := cdExp_not_dvd hη
  generalize cdExp η = E at hd hnd ⊢
  obtain ⟨q, rfl⟩ := hd
  have hq0 : q ≠ 0 := by rintro rfl; rw [mul_zero] at hη; exact hη rfl
  rcases zero_or_succ_or_isSuccLimit q with h0 | ⟨q', hq'⟩ | hlim
  · exact absurd h0 hq0
  · refine ⟨ω ^ E * q', ?_, dvd_mul_right _ _⟩
    rw [← hq', succ_eq_add_one, mul_add_one]
  · exfalso
    obtain ⟨k, hk⟩ := isSuccPrelimit_iff_omega0_dvd.1 hlim.isSuccPrelimit
    apply hnd
    rw [hk, ← mul_assoc, ← opow_succ, succ_eq_add_one]
    exact dvd_mul_right _ _

/-- **The window lemma**: if `ω^e ∣ η₀` and `η₀ < x < η₀ + ω^e`, then `cdExp x < e` and
`x + ω^{cdExp x} < η₀ + ω^e`. -/
theorem cdWin {η0 e x : Ordinal.{0}} (hd : ω ^ e ∣ η0) (h1 : η0 < x) (h2 : x < η0 + ω ^ e) :
    cdExp x < e ∧ x + ω ^ cdExp x < η0 + ω ^ e := by
  have hx0 : x ≠ 0 := (lt_of_le_of_lt (zero_le : (0 : Ordinal.{0}) ≤ η0) h1).ne'
  obtain ⟨ζ, rfl⟩ := exists_add_of_le h1.le
  have hζ : ζ < ω ^ e := (add_lt_add_iff_left _).1 h2
  have hζ0 : ζ ≠ 0 := by rintro rfl; rw [add_zero] at h1; exact lt_irrefl _ h1
  have hlt : cdExp (η0 + ζ) < e := by
    by_contra hge
    push Not at hge
    have h3 : ω ^ e ∣ η0 + ζ := (opow_dvd_opow ω hge).trans (cdExp_dvd hx0)
    have h4 : ω ^ e ∣ ζ := (dvd_add_iff hd).1 h3
    exact absurd (le_of_dvd hζ0 h4) (not_le.2 hζ)
  refine ⟨hlt, ?_⟩
  rw [add_assoc]
  exact (add_lt_add_iff_left _).2 (isPrincipal_add_omega0_opow e hζ
    ((opow_lt_opow_iff_right one_lt_omega0).2 hlt))

/-! ## Codes -/

/-- `-1 + e`: `e - 1` for finite `e`, `e` for infinite `e`. -/
noncomputable def cdOff (e : Ordinal.{0}) : Ordinal.{0} := if e < ω then e - 1 else e

theorem cdOff_le (e : Ordinal.{0}) : cdOff e ≤ e := by
  unfold cdOff; split_ifs
  · exact Ordinal.sub_le_self _ _
  · exact le_rfl

/-- The π-code `π_η = ψ_{Ω₂}(A_η)`. -/
noncomputable def cdPi (S : InaccSeq.{0}) (η : Ordinal.{0}) : Ordinal.{0} :=
  S.psi (ConjT.Aη S η) (Om (1 + 1))

/-- **The code of a name** `η = η₀ + ω^e`: `-1 + e` when `e < Ω₂`, the π-code `π_η` otherwise. -/
noncomputable def cdCodeOf (S : InaccSeq.{0}) (η : Ordinal.{0}) : Ordinal.{0} :=
  if cdExp η < Om (1 + 1) then cdOff (cdExp η) else cdPi S η

theorem cdPi_lt (S : InaccSeq.{0}) (η : Ordinal.{0}) : cdPi S η < Om (1 + 1) :=
  psi_lt (InR_Om_succ 1) _

/-- The code is at most the last exponent. -/
theorem cdCodeOf_le_exp (S : InaccSeq.{0}) (η : Ordinal.{0}) : cdCodeOf S η ≤ cdExp η := by
  unfold cdCodeOf; split_ifs with h
  · exact cdOff_le _
  · exact ((cdPi_lt S η).trans_le (not_lt.1 h)).le

theorem cdCodeOf_of_lt {S : InaccSeq.{0}} {η : Ordinal.{0}} (h : cdExp η < Om (1 + 1)) :
    cdCodeOf S η = cdOff (cdExp η) := if_pos h

/-! ## Names of restarts -/

variable {S : InaccSeq.{0}}

/-- **The name** `η_λ` of a restart index: the good `η` with `ι(η) = λ`. -/
noncomputable def cdEta (S : InaccSeq.{0}) (l : Ordinal.{0}) : Ordinal.{0} :=
  sInf {η | Bt.Good S η ∧ iota S η = l}

/-- The code `m_λ` of a restart index. -/
noncomputable def cdCode (S : InaccSeq.{0}) (l : Ordinal.{0}) : Ordinal.{0} := cdCodeOf S (cdEta S l)

theorem cd_iota_lt_of_good {η η' : Ordinal.{0}} (hg : Bt.Good S η) (h : η < η') :
    iota S η < iota S η' :=
  calc iota S η < iota S η + 1 := lt_add_one _
    _ = iota S (η + 1) := (iota_good hg).symm
    _ ≤ iota S η' := iota_mono η' (η + 1) (Order.add_one_le_of_lt h)

theorem cd_good_inj {η η' : Ordinal.{0}} (hg : Bt.Good S η) (hg' : Bt.Good S η')
    (he : iota S η = iota S η') : η = η' := by
  rcases lt_trichotomy η η' with h | h | h
  · exact absurd he (cd_iota_lt_of_good hg h).ne
  · exact h
  · exact absurd he.symm (cd_iota_lt_of_good hg' h).ne

/-- Every `λ` with `1 ≤ λ < ι(η₀)` has a good name `η < η₀`. -/
theorem cd_good_name {l η0 : Ordinal.{0}} (h1 : 1 ≤ l) (hl : l < iota S η0) :
    ∃ η < η0, Bt.Good S η ∧ iota S η = l := by
  have hne : {η | l < iota S η}.Nonempty := ⟨η0, hl⟩
  have hmem : l < iota S (sInf {η | l < iota S η}) := csInf_mem hne
  have hmin : ∀ η < sInf {η | l < iota S η}, iota S η ≤ l := fun η h =>
    not_lt.1 fun hη => (csInf_le' (s := {η | l < iota S η}) hη).not_gt h
  have hle : sInf {η | l < iota S η} ≤ η0 := csInf_le' hl
  generalize sInf {η | l < iota S η} = η' at hmem hmin hle
  rcases zero_or_succ_or_isSuccLimit η' with h0 | ⟨β, hβ⟩ | hlim
  · rw [h0, iota_zero] at hmem; exact absurd h1 (not_le.2 hmem)
  · have hβlt : β < η' := by rw [← hβ]; exact lt_succ β
    have hb := hmin β hβlt
    rw [← hβ, succ_eq_add_one] at hmem
    by_cases hg : Bt.Good S β
    · rw [iota_good hg] at hmem
      exact ⟨β, hβlt.trans_le hle, hg, le_antisymm hb (Order.lt_add_one_iff.1 hmem)⟩
    · rw [iota_bad hg] at hmem; exact absurd hb (not_le.2 hmem)
  · rw [iota_limit hlim] at hmem
    exact absurd hmem (not_lt.2 (ciSup_le' fun e => hmin e.1 e.2))

/-- **The name is well defined**: for `1 ≤ λ < ι(η₀)`, `η_λ` is good, `ι(η_λ) = λ`, and `η_λ < η₀`. -/
theorem cdEta_spec {l η0 : Ordinal.{0}} (h1 : 1 ≤ l) (hl : l < iota S η0) :
    Bt.Good S (cdEta S l) ∧ iota S (cdEta S l) = l ∧ cdEta S l < η0 := by
  obtain ⟨η, hη0, hg, he⟩ := cd_good_name h1 hl
  have e : cdEta S l = η :=
    le_antisymm (csInf_le' ⟨hg, he⟩)
      (le_csInf ⟨η, hg, he⟩ fun _ hη' => (cd_good_inj hg hη'.1 (he.trans hη'.2.symm)).le)
  rw [e]; exact ⟨hg, he, hη0⟩

/-- **The name is unique**: a good `η` with `ι(η) = λ` is `η_λ`. -/
theorem cdEta_unique {l η : Ordinal.{0}} (hg : Bt.Good S η) (he : iota S η = l) : cdEta S l = η :=
  le_antisymm (csInf_le' ⟨hg, he⟩)
    (le_csInf ⟨η, hg, he⟩ fun _ hη' => (cd_good_inj hg hη'.1 (he.trans hη'.2.symm)).le)

/-- A restart index below a value `P(η₀)` is below `ι(η₀)`. -/
theorem cd_lt_iota {l η0 : Ordinal.{0}} (hl : upsilon l < Pv S η0) : l < iota S η0 := by
  have e : Pv S η0 = upsilon (iota S η0) := (ups_iota S η0).symm
  rw [e] at hl
  exact upsilon_normal.strictMono.lt_iff_lt.1 hl

/-- **`ρ_λ = P(η_λ)`** for a restart index below a value of `P`. -/
theorem cdEta_pv_spec {l η0 : Ordinal.{0}} (hl0 : l ≠ 0) (hl : upsilon l < Pv S η0) :
    Bt.Good S (cdEta S l) ∧ iota S (cdEta S l) = l ∧ cdEta S l < η0 ∧ Pv S (cdEta S l) = upsilon l := by
  obtain ⟨hg, he, hlt⟩ := cdEta_spec (Order.one_le_iff_ne_zero.2 hl0) (cd_lt_iota hl)
  refine ⟨hg, he, hlt, ?_⟩
  calc Pv S (cdEta S l) = upsilon (iota S (cdEta S l)) := (ups_iota S _).symm
    _ = upsilon l := by rw [he]

theorem cdEta_pv {l η0 : Ordinal.{0}} (hl0 : l ≠ 0) (hl : upsilon l < Pv S η0) :
    Pv S (cdEta S l) = upsilon l := (cdEta_pv_spec hl0 hl).2.2.2

/-! ## The order type below `m` of a set of codes -/

open Classical in
/-- The order type of `C ∩ [0, m)`: `cdOtp C m = sup_{c ∈ C, c < m} (cdOtp C c + 1)`. -/
noncomputable def cdOtp (C : Set Ordinal.{0}) (m : Ordinal.{0}) : Ordinal.{0} :=
  ⨆ c : Iio m, if c.1 ∈ C then cdOtp C c.1 + 1 else 0
termination_by m
decreasing_by exact c.2

open Classical in
theorem cdOtp_eq (C : Set Ordinal.{0}) (m : Ordinal.{0}) :
    cdOtp C m = ⨆ c : Iio m, if c.1 ∈ C then cdOtp C c.1 + 1 else 0 := by
  rw [cdOtp]

open Classical in
theorem cdOtp_bdd (C : Set Ordinal.{0}) (m : Ordinal.{0}) :
    BddAbove (range fun c : Iio m => if c.1 ∈ C then cdOtp C c.1 + 1 else 0) :=
  Ordinal.bddAbove_of_small

open Classical in
/-- `cdOtp C` is monotone. -/
theorem cdOtp_mono (C : Set Ordinal.{0}) {m m' : Ordinal.{0}} (h : m ≤ m') :
    cdOtp C m ≤ cdOtp C m' := by
  rw [cdOtp_eq C m, cdOtp_eq C m']
  refine ciSup_le' fun c => ?_
  exact le_ciSup (f := fun c : Iio m' => if c.1 ∈ C then cdOtp C c.1 + 1 else 0)
    (cdOtp_bdd C m') ⟨c.1, lt_of_lt_of_le c.2 h⟩

open Classical in
/-- `cdOtp C` is strictly increasing along `C`. -/
theorem cdOtp_lt_of_mem {C : Set Ordinal.{0}} {c m : Ordinal.{0}} (hc : c ∈ C) (hcm : c < m) :
    cdOtp C c < cdOtp C m := by
  rw [cdOtp_eq C m]
  have h2 := le_ciSup (f := fun c : Iio m => if c.1 ∈ C then cdOtp C c.1 + 1 else 0)
    (cdOtp_bdd C m) ⟨c, hcm⟩
  simp only [if_pos hc] at h2
  exact lt_of_lt_of_le (lt_add_one _) h2

open Classical in
/-- `cdOtp C m ≤ m`. -/
theorem cdOtp_le_self (C : Set Ordinal.{0}) : ∀ m, cdOtp C m ≤ m := by
  intro m
  induction m using WellFoundedLT.induction with
  | ind m IH =>
  rw [cdOtp_eq]
  refine ciSup_le' fun c => ?_
  split_ifs
  · exact Order.add_one_le_of_lt ((IH c.1 c.2).trans_lt c.2)
  · exact zero_le

/-- On an initial segment of `C`, `cdOtp C` is the identity. -/
theorem cdOtp_of_Iio (C : Set Ordinal.{0}) : ∀ m, Iio m ⊆ C → cdOtp C m = m := by
  intro m
  induction m using WellFoundedLT.induction with
  | ind m IH =>
  intro hsub
  refine le_antisymm (cdOtp_le_self C m) (le_of_forall_lt fun x hx => ?_)
  have h1 := cdOtp_lt_of_mem (hsub hx) hx
  rwa [IH x hx (fun y hy => hsub (lt_trans hy hx))] at h1

/-! ## The reading `Θ_λ` -/

/-- The codes read at `λ`: `Cl(A_{η_λ}, ρ_λ)` (the constants lie below `ρ_λ`). -/
def cdHull (S : InaccSeq.{0}) (l : Ordinal.{0}) : Set Ordinal.{0} :=
  S.CSet (ConjT.Aη S (cdEta S l)) (upsilon l)

/-- **The reading** `Θ_λ(m)`: the order type of the codes below `m` read at `λ`. -/
noncomputable def cdTheta (S : InaccSeq.{0}) (l m : Ordinal.{0}) : Ordinal.{0} := cdOtp (cdHull S l) m

theorem cdTheta_mono (S : InaccSeq.{0}) (l : Ordinal.{0}) {m m' : Ordinal.{0}} (h : m ≤ m') :
    cdTheta S l m ≤ cdTheta S l m' := cdOtp_mono _ h

theorem cdTheta_le (S : InaccSeq.{0}) (l m : Ordinal.{0}) : cdTheta S l m ≤ m := cdOtp_le_self _ m

/-- A code `c ≤ ρ_λ` is read as itself: `Θ_λ(c) = c`. -/
theorem cdTheta_small (S : InaccSeq.{0}) {l c : Ordinal.{0}} (hc : c ≤ upsilon l) :
    cdTheta S l c = c :=
  cdOtp_of_Iio _ c fun _ hy => CSet.of_lt (lt_of_lt_of_le hy hc)

open Classical in
/-- **`Θ_λ(Ω₁) = ρ_λ`** when `ρ_λ = P(η_λ)` (the countable codes read at `λ` are the ordinals `< ρ_λ`). -/
theorem cdTheta_Om1 {l : Ordinal.{0}} (hpv : Pv S (cdEta S l) = upsilon l) :
    cdTheta S l (Om 1) = upsilon l := by
  have hlt : upsilon l < Om 1 := by rw [← hpv]; exact Pv_lt_Om1 S _
  refine le_antisymm ?_ ?_
  · unfold cdTheta
    rw [cdOtp_eq]
    refine ciSup_le' fun c => ?_
    split_ifs with hc
    · have hcl : c.1 < upsilon l := by
        have hc' : c.1 ∈ S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)) := by
          have : S.psi (ConjT.Aη S (cdEta S l)) (Om 1) = upsilon l := hpv
          rw [this]; exact hc
        have := lt_psi_of_mem Low.InR_Om_one hc' c.2
        rwa [show S.psi (ConjT.Aη S (cdEta S l)) (Om 1) = upsilon l from hpv] at this
      exact Order.add_one_le_of_lt ((cdOtp_le_self _ c.1).trans_lt hcl)
    · exact zero_le
  · calc upsilon l = cdTheta S l (upsilon l) := (cdTheta_small S le_rfl).symm
      _ ≤ cdTheta S l (Om 1) := cdTheta_mono S l hlt.le

/-! ## Closed points and the enumeration `k_λ` -/

/-- "`lh(α) ≤ y`": every `≤₁`-successor of `α` is at most `y`. -/
def cdLhLe (a y : Ordinal.{0}) : Prop := ∀ g, le1 a g → g ≤ y

/-- The first block top `δ_λ = υ_{λ+ω+1}`. -/
noncomputable def cdDelta (l : Ordinal.{0}) : Ordinal.{0} := upsilon (l + ω + 1)

/-- **`y` is closed relative to `λ`**: `δ_λ ≤ y`, and every `α ∈ (ρ_λ, y]` has `lh(α) ≤ y`. -/
def cdClosed (l y : Ordinal.{0}) : Prop :=
  cdDelta l ≤ y ∧ ∀ a, upsilon l < a → a ≤ y → cdLhLe a y

/-- The closed points, and every point `≥ max(Ω₁, δ_λ)` (only read below `Ω₁`). -/
def cdK (l : Ordinal.{0}) : Set Ordinal.{0} :=
  {y | cdClosed l y} ∪ {y | Om1 ≤ y ∧ cdDelta l ≤ y}

/-- **`k_λ`**: the increasing enumeration of `cdK λ`. -/
noncomputable def cdk (l p : Ordinal.{0}) : Ordinal.{0} := enumOrd (cdK l) p

/-- The value `A^♯_λ(c) = k_λ(Θ_λ(c))` of a code `c` at `λ`. -/
noncomputable def cdRc (S : InaccSeq.{0}) (l c : Ordinal.{0}) : Ordinal.{0} := cdk l (cdTheta S l c)

/-- **The predicted long reach** `r(λ) = k_λ(Θ_λ(m_λ))`. -/
noncomputable def cdR (S : InaccSeq.{0}) (l : Ordinal.{0}) : Ordinal.{0} := cdRc S l (cdCode S l)

theorem cdK_unbdd (l : Ordinal.{0}) : ¬ BddAbove (cdK l) := by
  rw [not_bddAbove_iff]
  intro b
  refine ⟨max (b + 1) (max Om1 (cdDelta l)), Or.inr ⟨?_, ?_⟩, ?_⟩
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)
  · exact lt_of_lt_of_le (lt_add_one b) (le_max_left _ _)

theorem cdk_strictMono (l : Ordinal.{0}) : StrictMono (cdk l) := enumOrd_strictMono (cdK_unbdd l)

theorem cdk_mem (l p : Ordinal.{0}) : cdk l p ∈ cdK l := enumOrd_mem (cdK_unbdd l) p

theorem cdk_inj (l : Ordinal.{0}) {p q : Ordinal.{0}} : cdk l p = cdk l q ↔ p = q :=
  enumOrd_inj (cdK_unbdd l)

/-- `δ_λ ≤ k_λ(p)`. -/
theorem cdk_ge (l p : Ordinal.{0}) : cdDelta l ≤ cdk l p := by
  rcases cdk_mem l p with h | h
  · exact h.1
  · exact h.2

/-- Below `Ω₁`, `k_λ(p)` is a closed point. -/
theorem cdk_closed {l p : Ordinal.{0}} (h : cdk l p < Om1) : cdClosed l (cdk l p) := by
  rcases cdk_mem l p with h' | h'
  · exact h'
  · exact absurd h'.1 (not_le.2 h)

theorem cdRc_mono (S : InaccSeq.{0}) (l : Ordinal.{0}) {c c' : Ordinal.{0}} (h : c ≤ c') :
    cdRc S l c ≤ cdRc S l c' :=
  (cdk_strictMono l).monotone (cdTheta_mono S l h)

theorem cdR_ge (S : InaccSeq.{0}) (l : Ordinal.{0}) : cdDelta l ≤ cdR S l := cdk_ge l _

theorem cdRho_lt_delta (l : Ordinal.{0}) : upsilon l < cdDelta l :=
  upsilon_normal.strictMono (lt_of_lt_of_le (lt_add_of_pos_right l omega0_pos) le_self_add)

theorem cdRho_lt_R (S : InaccSeq.{0}) (l : Ordinal.{0}) : upsilon l < cdR S l :=
  (cdRho_lt_delta l).trans_le (cdR_ge S l)

/-- **Every exact reach `r ≥ δ_λ` of `ρ_λ` is closed relative to `λ`.** -/
theorem cdClosed_of_reach {l r : Ordinal.{0}} (hr : IsReach R2C (upsilon l) r) (hδ : cdDelta l ≤ r) :
    cdClosed l r := by
  refine ⟨hδ, fun a ha har g hag => ?_⟩
  have h1 : le1 (upsilon l) a := le1_of_le_of_le1 ha.le har hr.1
  exact hr.2 g (le1_trans h1 hag)

/-- **Every exact reach `r ≥ δ_λ` is `k_λ(p)` for exactly one `p`.** -/
theorem cdk_index {l r : Ordinal.{0}} (hr : IsReach R2C (upsilon l) r) (hδ : cdDelta l ≤ r) :
    ∃ p, cdk l p = r ∧ ∀ q, cdk l q = r → q = p := by
  obtain ⟨p, hp⟩ := enumOrd_surjective (cdK_unbdd l) (Or.inl (cdClosed_of_reach hr hδ))
  exact ⟨p, hp, fun q hq => (cdk_inj l).1 (hq.trans hp.symm)⟩

/-- **On an interval of closed points, `k_λ(x) = δ_λ + x`.** -/
theorem cdk_interval {l c : Ordinal.{0}} (hK : ∀ x ≤ c, cdDelta l + x ∈ cdK l) :
    ∀ x ≤ c, cdk l x = cdDelta l + x := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx
  refine le_antisymm ?_ ?_
  · refine enumOrd_le_of_forall_lt (hK x hx) fun b hb => ?_
    have e : enumOrd (cdK l) b = cdDelta l + b := IH b hb (hb.le.trans hx)
    rw [e]; exact (add_lt_add_iff_left _).2 hb
  · obtain ⟨z, hz⟩ := exists_add_of_le (cdk_ge l x)
    rw [hz]
    refine (add_le_add_iff_left _).2 (not_lt.1 fun hzx => ?_)
    have e1 : cdk l z = cdDelta l + z := IH z hzx (hzx.le.trans hx)
    have e2 : z = x := (cdk_inj l).1 (e1.trans hz.symm)
    exact lt_irrefl _ (e2 ▸ hzx)

/-- **The short value**: a code `m_λ ≤ ρ_λ` with `[δ_λ, δ_λ + m_λ]` closed has `k_λ(Θ_λ(m_λ)) = δ_λ + m_λ`. -/
theorem cdR_short {l : Ordinal.{0}} (hm : cdCode S l ≤ upsilon l)
    (hK : ∀ x ≤ cdCode S l, cdDelta l + x ∈ cdK l) : cdR S l = cdDelta l + cdCode S l := by
  unfold cdR cdRc
  rw [cdTheta_small S hm]
  exact cdk_interval hK _ le_rfl

end Googology.Trans.PoR.InaccPsi.R2.Cd

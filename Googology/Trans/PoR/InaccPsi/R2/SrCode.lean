import Googology.Trans.PoR.InaccPsi.R2.SrReal
import Googology.Trans.PoR.InaccPsi.R2.GhEps
import Googology.Trans.PoR.InaccPsi.R2.GfAt

/-!
# The offsets below `ε_{a+1}` as readings of codes: the offset map `π_{ρ,a}` and the supply below `ε_{ρ+1}`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

Every `ν < ε_{x+1}` is the reading `Gf.rdc A x` of exactly one code `A < ε_{Ω₁+1}` with gate below `x`
(`srCode_ex`, `srCode_uniq`); `srCd x ν` is that code.  For `ε`-numbers `ρ < a < Ω₁` the base change
`π_{ρ,a}` sends `rdc A a` to `rdc A ρ` (`Gf.rdc_pi`), and for a limit code the last exponent moves along:
`e(rdc A ρ) = π_{ρ,a}(e(rdc A a))` (`srLim_pi`).  So the offset map `g ↦ rdc (srCd a g) ρ` is `π_{ρ,a}` itself on
the offsets with gates below `ρ`, and it carries the code `-1 + e(g)` of the inner restart `a + g` to the code of
its image.

* `srCode_ex`, `srCode_uniq`, `srCd` (**the code of an offset**), `srCd_spec`, `srCd_eq`, `srCd_zero`;
* `srPi_mul` (**`π_{ρ,a}(a·J) = ρ·π_{ρ,a}(J)` for `J < ε_{a+1}`**, also `J ≥ ρ`);
* `srCode_lim` (a code reading a nonzero multiple of `ω` is a limit), `srLim_pi` (**`π_{ρ,a}(-1+e(g)) = -1+e(π g)`
  and `ω² ∣ g ⇒ ω² ∣ π g`**);
* `srF ρ a` (**the offset map**: `π_{ρ,a}` on the multiples of `ω²`, the residue `< ω²` kept), `srOff`
  (**`Sl.SlOff (srF ρ a) Os ε_{ρ+1}`** when every gate is below `ρ`), `srF_eq` (`srF ρ a g = rdc (srCd a g) ρ`
  for `ω² ∣ g`), `srF_res` (`srF(g + t) = srF(g) + t`, `t < ω²`);
* `srGood` (`η + y` is good for `y < ε_{P(η)+1}`), `srEN_lt_Om1`, `srCode_shift` (**`η_{ι(η)+g} = η + g`,
  `m_{ι(η)+g} = -1 + e(g)` for `0 < g < ε_{P(η)+1}`**);
* `srThMem` (`θ₂·A ∈ Cl(a, b)` for a code `A` with gate below `b`), `srSupE` (**the supply
  `υ_{μ+ε_{ρ_μ+1}} ≤ Θ_μ(G') ≤ r(μ)` at every Range restart of code `G_{k+1}+1`, unconditionally**: `So.soSup_gen`
  along the inverse reading `x ↦ srCd ρ_μ x`).

No new axiom.  New definitions: `srCd`, `srF` (ordinal functions).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Sr

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-! ## The code of an offset -/

/-- **Every `ν < ε_{x+1}` is the reading of a code with gate below `x`** (`x ≤ Ω₁` an `ε`-number). -/
theorem srCode_ex {x ν : Ordinal.{0}} (hx : InE x) (hx1 : x ≤ Om1) (hν : ν < eN x) :
    ∃ A, A < Gf.gfE ∧ Gf.gtc A < x ∧ Gf.rdc A x = ν := by
  obtain ⟨k, hk⟩ := Gh.ghTw_cof hx hν
  have hg : Gf.gtc (Gh.ghTw k) < x := (Gh.ghTw_gtc k).trans_lt (So.soOne_lt_E hx)
  obtain ⟨b, hb, hgb, hrb⟩ := Gf.rdc_surj hx hx1 (Gh.ghTw_lt k) hg hk
  exact ⟨b, hb.trans (Gh.ghTw_lt k), hgb, hrb⟩

/-- **The code is unique.** -/
theorem srCode_uniq {x A A' : Ordinal.{0}} (hx : InE x) (hA : A < Gf.gfE) (hA' : A' < Gf.gfE)
    (hg : Gf.gtc A < x) (hg' : Gf.gtc A' < x) (e : Gf.rdc A x = Gf.rdc A' x) : A = A' := by
  rcases lt_trichotomy A A' with h | h | h
  · exact absurd e (Gf.rdc_mono hx hA' h hg' hg).ne
  · exact h
  · exact absurd e (Gf.rdc_mono hx hA h hg hg').ne'

/-- **The code of `ν` at the base `x`.** -/
noncomputable def srCd (x ν : Ordinal.{0}) : Ordinal.{0} := by
  classical
  exact if h : ∃ A, A < Gf.gfE ∧ Gf.gtc A < x ∧ Gf.rdc A x = ν then Classical.choose h else 0

theorem srCd_spec {x ν : Ordinal.{0}} (hx : InE x) (hx1 : x ≤ Om1) (hν : ν < eN x) :
    srCd x ν < Gf.gfE ∧ Gf.gtc (srCd x ν) < x ∧ Gf.rdc (srCd x ν) x = ν := by
  have h := srCode_ex hx hx1 hν
  rw [srCd, dif_pos h]
  exact Classical.choose_spec h

theorem srCd_eq {x A : Ordinal.{0}} (hx : InE x) (hA : A < Gf.gfE) (hg : Gf.gtc A < x) :
    srCd x (Gf.rdc A x) = A := by
  have h : ∃ A', A' < Gf.gfE ∧ Gf.gtc A' < x ∧ Gf.rdc A' x = Gf.rdc A x := ⟨A, hA, hg, rfl⟩
  rw [srCd, dif_pos h]
  obtain ⟨h1, h2, h3⟩ := Classical.choose_spec h
  exact srCode_uniq hx h1 hA h2 hg h3

theorem srCd_zero {x : Ordinal.{0}} (hx : InE x) : srCd x 0 = 0 := by
  have := srCd_eq hx Gf.eW_E.pos (by rw [Gf.gtc_zero]; exact hx.pos)
  rwa [Gf.rdc_zero] at this

/-! ## Limit codes: the last exponent moves with the base change -/

theorem srNot_dvd_succ (y : Ordinal.{0}) : ¬ ω ∣ y + 1 := by
  rintro ⟨k, hk⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    exact (lt_of_lt_of_le zero_lt_one le_add_self).ne' hk
  have hl : IsSuccLimit (ω * k) := isSuccLimit_mul_left isSuccLimit_omega0 (pos_iff_ne_zero.2 hk0)
  rw [← hk] at hl
  exact not_isSuccLimit_add_one y hl

/-- A code whose reading is a nonzero multiple of `ω` is a limit code. -/
theorem srCode_lim {x A : Ordinal.{0}} (hA : A < Gf.gfE) (h0 : Gf.rdc A x ≠ 0)
    (hd : ω ∣ Gf.rdc A x) : IsSuccLimit A := by
  rcases zero_or_succ_or_isSuccLimit A with h | ⟨B, hB⟩ | hl
  · rw [h, Gf.rdc_zero] at h0; exact absurd rfl h0
  · exfalso
    have hBA : A = B + 1 := by rw [← succ_eq_add_one]; first | exact hB | exact hB.symm
    have hBW : B < Gf.gfE := lt_of_lt_of_le (lt_add_one B) (hBA ▸ hA.le)
    rw [hBA, (Gf.rdc_succ B hBW x).1] at hd
    exact srNot_dvd_succ _ hd
  · exact hl

theorem srOff_ge {e : Ordinal.{0}} (h : ω ≤ e) : cdOff e = e := by
  unfold cdOff; rw [if_neg (not_lt.2 h)]

/-- **The last exponent moves with the base change**: `π_{ρ,a}(-1 + e(rdc A a)) = -1 + e(rdc A ρ)`, and
`ω² ∣ rdc A a ⇒ ω² ∣ rdc A ρ` (limit codes with gate below `ρ`). -/
theorem srLim_pi {ρ a A : Ordinal.{0}} (hB : Bases ρ a) (hA : A < Gf.gfE) (hl : IsSuccLimit A)
    (hg : Gf.gtc A < ρ) :
    pi ρ a (cdOff (cdExp (Gf.rdc A a))) = cdOff (cdExp (Gf.rdc A ρ)) ∧
      (ω ^ 2 ∣ Gf.rdc A a → ω ^ 2 ∣ Gf.rdc A ρ) := by
  obtain ⟨_, l, d, _, _, hgl, hd, hlW, hF⟩ := Gf.rdc_lim_facts hl hA
  have hρE : InE ρ := hB.1
  have haE : InE a := hB.2.1
  have hga : Gf.gtc A < a := hg.trans hB.2.2.1
  obtain ⟨-, -, eA, -, -, -⟩ := hF a haE hga
  obtain ⟨-, -, eR, -, -, -⟩ := hF ρ hρE hg
  have hEa : cdExp (Gf.rdc A a) = a * Gf.rdc l a + d := by
    show lg _ = _; rw [eA, Gf.ev_tlg haE]
  have hEr : cdExp (Gf.rdc A ρ) = ρ * Gf.rdc l ρ + d := by
    show lg _ = _; rw [eR, Gf.ev_tlg hρE]
  have hdρ : d < ρ := hd.trans_lt hg
  have hcb := Gf.cb_tlg hρE.pos (hgl.trans_lt hg) hdρ
  obtain ⟨-, hpi⟩ := pi_ev hB (Gf.tlg l d) hcb
  rw [Gf.ev_tlg haE, Gf.ev_tlg hρE] at hpi
  have hA0 : A ≠ 0 := hl.bot_lt.ne'
  have hra0 : Gf.rdc A a ≠ 0 := (Gf.rdc_pos haE hA0 hA).ne'
  have hrr0 : Gf.rdc A ρ ≠ 0 := (Gf.rdc_pos hρE hA0 hA).ne'
  rcases eq_or_ne l 0 with rfl | hl0
  · rw [Gf.rdc_zero, mul_zero, zero_add] at hEa hEr
    rw [hEa, hEr]
    refine ⟨pi_lt hB ((cdOff_le d).trans_lt hdρ), fun h => ?_⟩
    have h2 : ((2 : ℕ) : Ordinal.{0}) ≤ d := by
      rw [← hEa]; exact cdExp_max hra0 (by rwa [Ordinal.opow_natCast])
    rw [← hEr] at h2
    have := (opow_dvd_opow ω h2).trans (cdExp_dvd hrr0)
    rwa [Ordinal.opow_natCast] at this
  · have hla : 0 < Gf.rdc l a := Gf.rdc_pos haE hl0 hlW
    have hlρ : 0 < Gf.rdc l ρ := Gf.rdc_pos hρE hl0 hlW
    have hωa : ω ≤ a * Gf.rdc l a + d :=
      (Sl.slE_omega_lt haE).le.trans ((Ordinal.le_mul_left a hla).trans le_self_add)
    have hωρ : ω ≤ ρ * Gf.rdc l ρ + d :=
      (Sl.slE_omega_lt hρE).le.trans ((Ordinal.le_mul_left ρ hlρ).trans le_self_add)
    rw [hEa, hEr, srOff_ge hωa, srOff_ge hωρ]
    refine ⟨hpi, fun _ => ?_⟩
    have h2 : ((2 : ℕ) : Ordinal.{0}) ≤ ρ * Gf.rdc l ρ + d :=
      ((natCast_lt_omega0 2).le.trans hωρ)
    rw [← hEr] at h2
    have := (opow_dvd_opow ω h2).trans (cdExp_dvd hrr0)
    rwa [Ordinal.opow_natCast] at this

/-- **`π_{ρ,a}(a·J) = ρ·π_{ρ,a}(J)` for every `J < ε_{a+1}`** whose code has gate below `ρ` (`J = rdc A a`): the
identity `π(υ_λ·J) = υ_μ·π(J)` with `J ≥ υ_μ` allowed (`R2.pi_mul` has only `J < υ_μ`). -/
theorem srPi_mul {ρ a A : Ordinal.{0}} (hB : Bases ρ a) (hA : A < Gf.gfE) (hg : Gf.gtc A < ρ) :
    a * Gf.rdc A a ∈ TB a ρ ∧ pi ρ a (a * Gf.rdc A a) = ρ * pi ρ a (Gf.rdc A a) := by
  obtain ⟨h1, h2⟩ := pi_ev hB (Gf.tcx A) (Gf.cb_tcx hB.1.pos A hg)
  rw [Gf.ev_tcx hB.2.1] at h1 h2
  rw [Gf.ev_tcx hB.1] at h2
  rw [(Gf.rdc_pi hB hA hg).2]
  exact ⟨h1, h2⟩

/-! ## The offset map -/

theorem srW_pos : (0 : Ordinal.{0}) < ω ^ 2 := pow_pos omega0_pos 2

theorem srW_div (q t : Ordinal.{0}) (ht : t < ω ^ 2) :
    (ω ^ 2 * q + t) / ω ^ 2 = q ∧ (ω ^ 2 * q + t) % ω ^ 2 = t := by
  refine ⟨?_, ?_⟩
  · rw [Ordinal.mul_add_div _ srW_pos.ne', Ordinal.div_eq_zero_of_lt ht, add_zero]
  · rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt ht]

/-- **The offset map**: `π_{ρ,a}` (through the codes) on the multiples of `ω²`, the residue kept. -/
noncomputable def srF (ρ a x : Ordinal.{0}) : Ordinal.{0} :=
  ω ^ 2 * (Gf.rdc (srCd a (ω ^ 2 * (x / ω ^ 2))) ρ / ω ^ 2) + x % ω ^ 2

theorem srF_res (ρ a q t : Ordinal.{0}) (ht : t < ω ^ 2) :
    srF ρ a (ω ^ 2 * q + t) = srF ρ a (ω ^ 2 * q) + t := by
  have h1 := srW_div q t ht
  have h2 := srW_div q 0 srW_pos
  rw [add_zero] at h2
  unfold srF
  rw [h1.1, h1.2, h2.1, h2.2, add_zero]

/-- `ω² ∣ rdc (srCd a w) ρ` for `ω² ∣ w` (gate below `ρ`). -/
theorem srFw_dvd {ρ a w : Ordinal.{0}} (hB : Bases ρ a) (hw : w < eN a) (hd : ω ^ 2 ∣ w)
    (hg : Gf.gtc (srCd a w) < ρ) : ω ^ 2 ∣ Gf.rdc (srCd a w) ρ := by
  have ha1 : a ≤ Om1 := hB.2.2.2.le
  obtain ⟨hAW, -, hr⟩ := srCd_spec hB.2.1 ha1 hw
  rcases eq_or_ne w 0 with rfl | hw0
  · rw [srCd_zero hB.2.1, Gf.rdc_zero]; exact dvd_zero _
  have hdω : ω ∣ Gf.rdc (srCd a w) a := by
    rw [hr]; exact (dvd_pow_self ω two_ne_zero).trans hd
  have hl := srCode_lim hAW (by rw [hr]; exact hw0) hdω
  exact (srLim_pi hB hAW hl hg).2 (by rw [hr]; exact hd)

theorem srF_eq {ρ a g : Ordinal.{0}} (hB : Bases ρ a) (hg : g < eN a) (hd : ω ^ 2 ∣ g)
    (hgt : Gf.gtc (srCd a g) < ρ) : srF ρ a g = Gf.rdc (srCd a g) ρ := by
  have hm : g % ω ^ 2 = 0 := (Ordinal.dvd_iff_mod_eq_zero).1 hd
  have e : ω ^ 2 * (g / ω ^ 2) = g := by
    have := Ordinal.div_add_mod g (ω ^ 2); rwa [hm, add_zero] at this
  have hF := srFw_dvd hB hg hd hgt
  have hm' : Gf.rdc (srCd a g) ρ % ω ^ 2 = 0 := (Ordinal.dvd_iff_mod_eq_zero).1 hF
  have e' : ω ^ 2 * (Gf.rdc (srCd a g) ρ / ω ^ 2) = Gf.rdc (srCd a g) ρ := by
    have := Ordinal.div_add_mod (Gf.rdc (srCd a g) ρ) (ω ^ 2); rwa [hm', add_zero] at this
  unfold srF
  rw [e, hm, add_zero, e']

/-- **The offset map is an `Sl.SlOff` with bound `ε_{ρ+1}`** when every gate is below `ρ`. -/
theorem srOff {ρ a : Ordinal.{0}} (hB : Bases ρ a) (Os : Finset Ordinal.{0}) (hOs : ∀ d ∈ Os, d < eN a)
    (hgt : ∀ d ∈ Os, Gf.gtc (srCd a (ω ^ 2 * (d / ω ^ 2))) < ρ) :
    Sl.SlOff (srF ρ a) Os (eN ρ) := by
  have hρE : InE ρ := hB.1
  have haE : InE a := hB.2.1
  have ha1 : a ≤ Om1 := hB.2.2.2.le
  have hwd : ∀ d, ω ^ 2 * (d / ω ^ 2) ≤ d := fun d =>
    le_self_add.trans_eq (Ordinal.div_add_mod d (ω ^ 2))
  -- the facts for `w = ω²·(d/ω²)`, `d ∈ insert 0 Os`
  have hW : ∀ d ∈ insert 0 Os, ω ^ 2 * (d / ω ^ 2) < eN a ∧
      Gf.gtc (srCd a (ω ^ 2 * (d / ω ^ 2))) < ρ := by
    intro d hd
    rcases Finset.mem_insert.1 hd with rfl | hd
    · simp only [Ordinal.zero_div, mul_zero]
      rw [srCd_zero haE, Gf.gtc_zero]; exact ⟨(eN_E a).pos, hρE.pos⟩
    · exact ⟨(hwd d).trans_lt (hOs d hd), hgt d hd⟩
  have hdecF : ∀ d ∈ insert 0 Os, ω ^ 2 * (Gf.rdc (srCd a (ω ^ 2 * (d / ω ^ 2))) ρ / ω ^ 2) =
      Gf.rdc (srCd a (ω ^ 2 * (d / ω ^ 2))) ρ := by
    intro d hd
    obtain ⟨h1, h2⟩ := hW d hd
    have hF := srFw_dvd hB h1 (dvd_mul_right _ _) h2
    have hm' := (Ordinal.dvd_iff_mod_eq_zero).1 hF
    have := Ordinal.div_add_mod (Gf.rdc (srCd a (ω ^ 2 * (d / ω ^ 2))) ρ) (ω ^ 2)
    rwa [hm', add_zero] at this
  refine ⟨?_, fun q t ht => srF_res ρ a q t ht, fun q => ?_, ?_, fun d hd => ?_⟩
  · unfold srF
    simp only [Ordinal.zero_div, mul_zero, Ordinal.zero_mod, add_zero]
    rw [srCd_zero haE, Gf.rdc_zero, Ordinal.zero_div, mul_zero]
  · have h := (srW_div q 0 srW_pos).2
    rw [add_zero] at h
    unfold srF
    rw [h, add_zero]; exact dvd_mul_right _ _
  · intro d hd d' hd' hdd
    have hd0 : d ∈ insert 0 Os := Finset.mem_coe.1 hd
    have hd0' : d' ∈ insert 0 Os := Finset.mem_coe.1 hd'
    have ed := Ordinal.div_add_mod d (ω ^ 2)
    have ed' := Ordinal.div_add_mod d' (ω ^ 2)
    have hr := Ordinal.mod_lt d srW_pos.ne'
    have hr' := Ordinal.mod_lt d' srW_pos.ne'
    have hqq : d / ω ^ 2 ≤ d' / ω ^ 2 := by
      by_contra hlt
      push Not at hlt
      have : d' < d := by
        calc d' = ω ^ 2 * (d' / ω ^ 2) + d' % ω ^ 2 := ed'.symm
          _ < ω ^ 2 * (d' / ω ^ 2) + ω ^ 2 := (add_lt_add_iff_left _).2 hr'
          _ = ω ^ 2 * (d' / ω ^ 2 + 1) := by rw [mul_add_one]
          _ ≤ ω ^ 2 * (d / ω ^ 2) := mul_le_mul_right (Order.add_one_le_of_lt hlt) _
          _ ≤ d := hwd d
      exact absurd hdd (not_lt.2 this.le)
    unfold srF
    rcases hqq.lt_or_eq with hlt | heq
    · obtain ⟨hw1, hg1⟩ := hW d hd0
      obtain ⟨hw2, hg2⟩ := hW d' hd0'
      obtain ⟨hA1, -, hr1⟩ := srCd_spec haE ha1 hw1
      obtain ⟨hA2, -, hr2⟩ := srCd_spec haE ha1 hw2
      have hga1 := hg1.trans hB.2.2.1
      have hga2 := hg2.trans hB.2.2.1
      have hww : ω ^ 2 * (d / ω ^ 2) < ω ^ 2 * (d' / ω ^ 2) := (mul_lt_mul_iff_right₀ srW_pos).2 hlt
      have hAA := Gf.lt_of_rdc_lt haE hA1 hA2 hga1 hga2 (by rw [hr1, hr2]; exact hww)
      have hFF := Gf.rdc_mono hρE hA2 hAA hg2 hg1
      rw [← hdecF d hd0, ← hdecF d' hd0'] at hFF
      have hΦ := (mul_lt_mul_iff_right₀ srW_pos).1 hFF
      calc _ < ω ^ 2 * (Gf.rdc (srCd a (ω ^ 2 * (d / ω ^ 2))) ρ / ω ^ 2) + ω ^ 2 :=
            (add_lt_add_iff_left _).2 hr
        _ = ω ^ 2 * (Gf.rdc (srCd a (ω ^ 2 * (d / ω ^ 2))) ρ / ω ^ 2 + 1) := by rw [mul_add_one]
        _ ≤ ω ^ 2 * (Gf.rdc (srCd a (ω ^ 2 * (d' / ω ^ 2))) ρ / ω ^ 2) :=
            mul_le_mul_right (Order.add_one_le_of_lt hΦ) _
        _ ≤ _ := le_self_add
    · have hrr : d % ω ^ 2 < d' % ω ^ 2 := by
        have h1 : ω ^ 2 * (d / ω ^ 2) + d % ω ^ 2 < ω ^ 2 * (d / ω ^ 2) + d' % ω ^ 2 := by
          calc _ = d := ed
            _ < d' := hdd
            _ = ω ^ 2 * (d' / ω ^ 2) + d' % ω ^ 2 := ed'.symm
            _ = _ := by rw [heq]
        exact (add_lt_add_iff_left _).1 h1
      rw [← heq]
      exact (add_lt_add_iff_left _).2 hrr
  · have hd0 : d ∈ insert 0 Os := Finset.mem_insert_of_mem hd
    obtain ⟨hw1, hg1⟩ := hW d hd0
    obtain ⟨hA1, -, -⟩ := srCd_spec haE ha1 hw1
    unfold srF
    rw [hdecF d hd0]
    have hE := eN_E ρ
    have hW2 : ω ^ 2 < eN ρ := by
      rw [pow_two]; exact hE.mul_lt (Sl.slE_omega_lt hE) (Sl.slE_omega_lt hE)
    exact (inE_indec hE).add_lt (Gf.rdc_lt_eN hρE _ hg1) ((Ordinal.mod_lt d srW_pos.ne').trans hW2)

/-! ## Names and codes of the inner restarts below `ε_{P(η)+1}` -/

theorem srEN_le_succ {η : Ordinal.{0}} (hg : Bt.Good S η) : eN (Nm.Pv S η) ≤ Nm.Pv S (η + 1) :=
  eN_le (Nm.Pv_lt_succ hg) (Sl.slPv_E (η + 1))

theorem srEN_lt_Om1 {η : Ordinal.{0}} (hg : Bt.Good S η) : eN (Nm.Pv S η) < Om 1 :=
  (srEN_le_succ hg).trans_lt (Nm.Pv_lt_Om1 S _)

/-- `η + y` is good for every `y < ε_{P(η)+1}`. -/
theorem srGood {η y : Ordinal.{0}} (hg : Bt.Good S η) (hy : y < eN (Nm.Pv S η)) : Bt.Good S (η + y) := by
  refine Rz.rz_good_shift hg ?_
  by_cases hyP : y < Nm.Pv S η
  · exact hyP.trans_le (Nm.Pv_mono le_self_add)
  · have h1 : 1 ≤ y := Order.one_le_iff_ne_zero.2 fun h0 => by
      rw [h0] at hyP; exact hyP (Sl.slPv_E (S := S) η).pos
    exact (hy.trans_le (srEN_le_succ hg)).trans_le (Nm.Pv_mono (add_le_add le_rfl h1))

/-- **`η_{ι(η)+g} = η + g` and `m_{ι(η)+g} = -1 + e(g)`** for `0 < g < ε_{P(η)+1}` (`ω^{Ω₁} ∣ η`). -/
theorem srCode_shift {η g : Ordinal.{0}} (hg : Bt.Good S η) (hdiv : ω ^ Om 1 ∣ η) (hg0 : g ≠ 0)
    (hgP : g < eN (Nm.Pv S η)) :
    cdEta S (Bt.iota S η + g) = η + g ∧ cdCode S (Bt.iota S η + g) = cdOff (cdExp g) := by
  have hg1 : g < Om 1 := hgP.trans (srEN_lt_Om1 hg)
  have hι : Bt.iota S (η + g) = Bt.iota S η + g :=
    Pp.ppIota_add η g fun y hy => srGood hg (hy.trans hgP)
  have he : cdEta S (Bt.iota S η + g) = η + g := cdEta_unique (srGood hg hgP) hι
  refine ⟨he, ?_⟩
  unfold cdCode
  rw [he]
  have hexp := Ls.lsExp_add hdiv hg0 hg1
  have h2 : cdExp (η + g) < Om (1 + 1) := by
    rw [hexp]
    exact ((Ls.lsExp_le hg0).trans_lt hg1).trans (Om_lt_Om.2 (lt_add_one 1))
  rw [cdCodeOf_of_lt h2, hexp]

/-! ## The supply below `ε_{ρ_μ+1}` -/

/-- **`θ₂·A ∈ Cl(a, b)`** for a code `A` with gate below `b` (`a > Ω_ω`). -/
theorem srThMem {a b : Ordinal.{0}} (ha : Om ω < a) :
    ∀ A, A < Gf.gfE → Gf.gtc A < b → Lc.lcTh S 2 * A ∈ S.CSet a b := by
  intro A
  induction A using WellFoundedLT.induction with
  | ind A IH =>
  intro hA hg
  rcases eq_or_ne A 0 with rfl | hA0
  · rw [mul_zero]; exact CSet.zero_mem a b
  obtain ⟨-, -, -, hdec, hra, -⟩ := Gf.parts hA0
  obtain ⟨gl, gq, gr⟩ := Gf.gtc_parts hA0 hA
  set l := log Om1 A with hl
  set q := A / Om1 ^ l with hq
  set r := A % Om1 ^ l with hrr
  have hlW : l < Gf.gfE := (Gf.log_lt hA0 hA).trans hA
  have hpow : Lc.lcTh S 2 * Om1 ^ l = ω ^ (Lc.lcTh S 2 + Om1 * l) := by
    rw [Gf.Om1_pow_eq, opow_add, Ls.lsTh_opow]
  have h1 : Lc.lcTh S 2 * (Om1 ^ l * q) ∈ S.CSet a b := by
    rw [← mul_assoc, hpow]
    exact Gf.gfMul_mem (CSet.add_mem (Ls.lsTh_mem ha 2) (Gf.gfW_mem (S := S) l hlW (gl.trans_lt hg)).2)
      q (gq.trans_lt hg)
  have h2 := IH r hra (hra.trans hA) (gr.trans_lt hg)
  rw [← hdec, mul_add]
  exact CSet.add_mem h1 h2

/-- **The supply up to `ε_{ρ_μ+1}`**: `υ_{μ+ε_{ρ_μ+1}} ≤ Θ_μ(G') ≤ r(μ)` at every Range restart `μ` with code
`G_{k+1} + 1`, along the inverse reading `x ↦ srCd ρ_μ x`. -/
theorem srSupE (k : ℕ) {μ : Ordinal.{0}} (hR : CdRange S μ) (hc : cdCode S μ = Ls.lsG S (k + 1) + 1) :
    upsilon (μ + eN (upsilon μ)) ≤ cdTheta S μ (Ls.lsG S (k + 1)) ∧
      upsilon (μ + eN (upsilon μ)) ≤ cdR S μ := by
  obtain ⟨hgμ, -, hpv⟩ := Ra.raName hR
  have hρE : InE (upsilon μ) := by rw [← hpv]; exact Sl.slPv_E _
  have hρΩ : upsilon μ < Om 1 := So.soRho_lt_Om1 hR
  have hρ1 : upsilon μ ≤ Om1 := by rw [Br.Om1_eq]; exact hρΩ.le
  have hspec := fun x (hx : x < eN (upsilon μ)) => srCd_spec hρE hρ1 hx
  refine So.soSup_gen hR hc (So.soE_lim (eN_E _)) (fun y hy => srGood hgμ (by rw [hpv]; exact hy))
    (by have := srEN_lt_Om1 hgμ; rw [hpv] at this; exact this.le) (srCd (upsilon μ)) ?_ ?_ ?_ ?_
  · intro x hx
    have hx' : x < eN (upsilon μ) := (lt_add_one x).trans hx
    obtain ⟨hA, hg, hr⟩ := hspec x hx'
    obtain ⟨e1, -, e3⟩ := Gf.rdc_succ _ hA (upsilon μ)
    have hg1 : Gf.gtc (srCd (upsilon μ) x + 1) < upsilon μ :=
      e3.trans_lt ((So.soE_lim hρE).add_one_lt hg)
    have := srCd_eq hρE (Gf.succ_lt_eW hA) hg1
    rw [e1, hr] at this
    exact this
  · intro y x hyx hx
    rcases hyx.lt_or_eq with h | h
    · obtain ⟨hA, hg, hr⟩ := hspec x hx
      obtain ⟨hA', hg', hr'⟩ := hspec y (h.trans hx)
      exact (Gf.lt_of_rdc_lt hρE hA' hA hg' hg (by rw [hr, hr']; exact h)).le
    · rw [h]
  · intro x hx a b ha hb
    obtain ⟨hA, hg, -⟩ := hspec x hx
    exact CSet.add_mem (ConjT.OmW_mem S a b) (srThMem ha _ hA (hg.trans_le hb))
  · intro x hx
    obtain ⟨hA, -, -⟩ := hspec x hx
    have hE : InE (Lc.lcTh S (k + 1)) := Low.opow_eq_self_of_SC (Ls.lsTh_SC (k + 1))
    have hO : Om1 < Lc.lcTh S (k + 1) := by rw [Br.Om1_eq]; exact Rp.rpOm1_lt_th (S := S) k
    exact hA.trans_le (eN_le hO hE)

end Googology.Trans.PoR.InaccPsi.R2.Sr

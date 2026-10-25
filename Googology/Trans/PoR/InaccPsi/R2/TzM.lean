import Googology.Trans.PoR.InaccPsi.R2.TzW
import Googology.Trans.PoR.InaccPsi.R2.TwBase

/-!
# The collapse `ψ_{Ω₂}(e) < X` of an argument with code components is a code

`ψ = ψ_{Ω₂}`, `w_j = Ω₂^j`, `W = Ω₂^{Ω₂}`, `X = Tl.tlX = ψ(W)`, `TlCl q` the codes over `q` with the atoms `F_β(y)`,
`TzG P` the base-`Ω₂` normal forms with components in `P` (`R2.TzW`).  An argument `e` is *own* when
`e ∈ Cl(e, ψ(e))`.  `M(x)` is the least member of `R = Cl(e, ψ(e))` at or above `x` (`InaccSeq.M`); `M(e)` is own and
`ψ(M(e)) = ψ(e)`.

* `tz_rem_mem` (`x mod w_j` stays in every hull), `tz_hull_dig` (**the members `x < W` of `Cl(a, s)` are `< w_s` and
  have all their digits `< s`** when `Cl(a, s) ∩ Ω₂ ⊆ s`), `tz_hull_top`;
* `tz_M_term` (**`M(w_j·d + r) = w_j·d + M(r)`** for `j, d < s`, `r < w_j`), `tz_M_cd` (**rounding up keeps the
  components**: `M(x)` has every component in `P` and below `s` when `x` has every component in `P`, `P` contains
  `1` and is closed under `+ 1`);
* `tz_own_code` (**`ψ(e)` is a code when `e` is own and every component of `e` is a code**, by the run
  `e = B + w_λ·D` of `Tw.twRun` and induction on `e`);
* `tz_key` (**`ψ(e) < X` is a code over `q` for every `e` whose components are codes or `≥ X`**: `ψ(e) = ψ(M(e))`,
  `M(e)` is own with code components).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tz

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Ts Googology.Trans.PoR.InaccPsi.R2.Tw

variable {S : InaccSeq.{0}}

/-- `W = Ω₂^{Ω₂}`. -/
theorem tz_W_lt_Lam : leWe (Om (1 + 1)) < S.Lam := lt_Lam_of_mem (b := 0) zero_le (tsW_mem (S := S) 0 0)

/-- **`x mod w_j` stays in every hull.** -/
theorem tz_rem_mem (j : Ordinal.{0}) {a b : Ordinal.{0}} :
    ∀ x, x ∈ S.CSet a b → x % leWe j ∈ S.CSet a b := by
  set u := leWe j with hudef
  have h0 : u ≠ 0 := tsU_ne j
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [Ordinal.zero_mod]; exact CSet.zero_mem _ _
  obtain ⟨hl, ht⟩ := lead_tail_mem hx hx0
  have hlt := lead_add_tail hx0
  rcases le_or_gt u (lead x) with h1 | h1
  · have hI : Indec (lead x) := indec_iff.2 ⟨(opow_pos _ omega0_pos).ne', isPrincipal_add_omega0_opow _⟩
    obtain ⟨k', hk'⟩ := ts_dvd_of_indec_u j hI h1
    have e2 : x % u = tail x % u := by
      conv_lhs => rw [← hlt, hk']
      rw [Ordinal.mul_add_mod_self]
    rw [e2]
    exact IH (tail x) (tail_lt hx0) ht
  · have hlog : log ω x < Om (1 + 1) * j := by
      have := h1
      unfold lead at this
      rw [hudef] at this
      unfold leWe at this
      exact (opow_lt_opow_iff_right one_lt_omega0).1 this
    have hxu : x < u := by
      refine (lt_opow_log_add_one x).trans_le ?_
      rw [hudef]; unfold leWe
      exact opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hlog)
    rw [Ordinal.mod_eq_of_lt hxu]
    exact hx

/-- **The members `x < W` of `Cl(a, s)` are `< w_s` and have all their digits below `s`**, for a strongly critical
`s ∈ (Ω₁, Ω₂)` with `Cl(a, s) ∩ Ω₂ ⊆ s`. -/
theorem tz_hull_dig {a s : Ordinal.{0}} (hsS : SC s) (hs1 : Om 1 < s)
    (hR : ∀ x ∈ S.CSet a s, x < Om (1 + 1) → x < s) :
    ∀ x ∈ S.CSet a s, x < leWe (Om (1 + 1)) → x < leWe s ∧ ∀ j : Ordinal.{0}, x / leWe j % Om (1 + 1) < s := by
  have hsI : Indec s := Lq.lq_SC_indec hsS
  have h1s : (1 : Ordinal.{0}) < s := Gg.gg_one_lt_of_SC hsS
  have hsw : s ≤ leWe s := by
    unfold leWe
    conv_lhs => rw [← Gg.gg_SC_eps hsS]
    exact opow_le_opow_right omega0_pos (Ordinal.le_mul_right _ ts_SC_Om2.1)
  have hsmall : ∀ v, v < s → v < leWe s ∧ ∀ j : Ordinal.{0}, v / leWe j % Om (1 + 1) < s :=
    fun v hv => ⟨hv.trans_le hsw, fun j => (tsk_dig_le j v).trans_lt hv⟩
  have hOm2 : Om (1 + 1) < leWe s ∧ ∀ j : Ordinal.{0}, Om (1 + 1) / leWe j % Om (1 + 1) < s := by
    refine ⟨?_, fun j => ?_⟩
    · rw [← leWe_one]; exact leWe_lt h1s
    · have h := tsk_dig_opow j (Om (1 + 1))
      rw [ts_Om2_opow, Ordinal.mod_self, opow_zero] at h
      exact h.trans_lt h1s
  have hbig : ∀ p, ω ^ p = p → Om (1 + 1) < p → ¬ p < leWe (Om (1 + 1)) :=
    fun p hp h2 => not_lt.2 (ts_eps_ge_W hp h2)
  have hall : ∀ x ∈ S.CSet a s, x ∈ S.CSet a s := fun x hx => hx
  intro x hx
  have hxC := hall x hx
  induction hx with
  | @small v hv => exact fun _ => hsmall v hv
  | zero => exact fun _ => hsmall 0 hsS.1
  | inacc n =>
    exact fun h => absurd h (hbig _ (Low.opow_eq_self_of_SC (SC_I (S := S) n)) (Mx.mxOm2_lt_I n))
  | inaccW =>
    exact fun h => absurd h (hbig _ (Low.opow_eq_self_of_SC (SC_Iw (S := S))) Mx.mxOm2_lt_Iw)
  | @add p q hp hq ihp ihq =>
    intro h
    obtain ⟨ha1, ha2⟩ := ihp hp (lt_of_le_of_lt le_self_add h)
    obtain ⟨hb1, hb2⟩ := ihq hq (lt_of_le_of_lt le_add_self h)
    exact ⟨(tsU_indec s).add_lt ha1 hb1, fun j => (tsk_dig_add j p q).trans_lt (hsI.add_lt (ha2 j) (hb2 j))⟩
  | @phi p q hp hq ihp ihq =>
    intro h
    rcases eq_or_ne p 0 with rfl | ha0
    · rw [veblen_zero_apply] at h ⊢
      have hbW : q < leWe (Om (1 + 1)) := (right_le_veblen 0 q).trans_lt (by rwa [veblen_zero_apply])
      obtain ⟨-, hb2⟩ := ihq hq hbW
      have hb0 : q % Om (1 + 1) < s := by have := hb2 0; rwa [tsk_dig_zero] at this
      have hdig : ∀ j : Ordinal.{0}, ω ^ q / leWe j % Om (1 + 1) < s := fun j => by
        have hw := hsS.2 0 hsS.1 _ hb0
        rw [veblen_zero_apply] at hw
        exact (tsk_dig_opow j q).trans_lt hw
      refine ⟨?_, hdig⟩
      have hbq : q < Om (1 + 1) * Om (1 + 1) := by
        unfold leWe at h; exact (opow_lt_opow_iff_right one_lt_omega0).1 h
      have hb1 : q / Om (1 + 1) < s := by
        have h1 := hb2 1
        rw [leWe_one, Ordinal.mod_eq_of_lt ((Ordinal.lt_mul_iff_div_lt ts_Om2_ne).1 hbq)] at h1
        exact h1
      have hbX : q < Om (1 + 1) * s := by
        calc q < Om (1 + 1) * (q / Om (1 + 1)) + Om (1 + 1) := by
              conv_lhs => rw [← Ordinal.div_add_mod q (Om (1 + 1))]
              exact (add_lt_add_iff_left _).2 (Ordinal.mod_lt _ ts_Om2_ne)
          _ = Om (1 + 1) * (q / Om (1 + 1) + 1) := by rw [mul_add, mul_one]
          _ ≤ Om (1 + 1) * s := mul_le_mul_right (Order.add_one_le_of_lt hb1) _
      unfold leWe; exact (opow_lt_opow_iff_right one_lt_omega0).2 hbX
    · have hε : ω ^ veblen p q = veblen p q := Tp.tpVeblen_fix (pos_iff_ne_zero.2 ha0)
      rcases lt_trichotomy (veblen p q) (Om (1 + 1)) with hlt | heq | hgt
      · exact hsmall _ (hR _ (CSet.phi_mem hp hq) hlt)
      · rw [heq]; exact hOm2
      · exact absurd h (hbig _ hε hgt)
  | @om v hv _ =>
    intro h
    rcases eq_or_ne v 0 with rfl | hv0
    · rw [Om_zero]; exact hsmall 0 hsS.1
    have hε : ω ^ Om v = Om v := Low.opow_eq_self_of_SC (SC_Om hv0)
    rcases lt_trichotomy (Om v) (Om (1 + 1)) with hlt | heq | hgt
    · exact hsmall _ (hR _ (CSet.Om_mem hv) hlt)
    · rw [heq]; exact hOm2
    · exact absurd h (hbig _ hε hgt)
  | @coll π e hπ hπC heC _ _ =>
    intro h
    by_cases hπ1 : π = Om 1
    · subst hπ1; exact hsmall _ ((psi_lt Low.InR_Om_one _).trans hs1)
    by_cases hπ2 : π = Om (1 + 1)
    · subst hπ2
      exact hsmall _ (hR _ (CSet.psi_mem e.2 hπ hπC heC) (psi_lt hπ _))
    · exact absurd h (hbig _ (Low.opow_eq_self_of_SC (SC_psi hπ e.1)) (ts_Om2_lt_psi hπ hπ1 hπ2))

/-- **The top term of a member `y < W` of `Cl(a, s)`** has level and digit below `s`. -/
theorem tz_hull_top {a s : Ordinal.{0}} (hsS : SC s) (hs1 : Om 1 < s)
    (hR : ∀ x ∈ S.CSet a s, x < Om (1 + 1) → x < s) {j d r : Ordinal.{0}} (hd0 : 0 < d) (hd2 : d < Om (1 + 1))
    (hr : r < leWe j) (hy : leWe j * d + r ∈ S.CSet a s) (hyW : leWe j * d + r < leWe (Om (1 + 1))) :
    j < s ∧ d < s := by
  obtain ⟨h1, h2⟩ := tz_hull_dig hsS hs1 hR _ hy hyW
  refine ⟨not_le.1 fun hjs => ?_, ?_⟩
  · exact absurd ((leWe_mono hjs).trans (tz_term_bounds hd0 hd2 hr).1) (not_le.2 h1)
  · have := h2 j; rwa [tz_div_eq hr, Ordinal.mod_eq_of_lt hd2] at this

/-! ## Rounding up in `R = Cl(e, s)` -/

/-- **`M(w_j·d + r) = w_j·d + M(r)` and `M(r) ≤ w_j`** for `j, d < s`, `r < w_j`. -/
theorem tz_M_term {e s j d r : Ordinal.{0}} (hjs : j < s) (hds : d < s) (hr : r < leWe j)
    (hx : leWe j * d + r < S.Lam) :
    S.M e s (leWe j * d + r) = leWe j * d + S.M e s r ∧ S.M e s r ≤ leWe j := by
  have hrL : r < S.Lam := (le_add_self.trans_lt hx)
  obtain ⟨hmR, hrm⟩ := M_spec (e := e) (g := s) hrL
  have hwR : leWe j ∈ S.CSet e s := leWe_mem (CSet.of_lt hjs)
  have hmw : S.M e s r ≤ leWe j := M_le hwR hr.le
  refine ⟨le_antisymm (M_le (CSet.add_mem (leMulWe_mem (CSet.of_lt hjs) (CSet.of_lt hds)) hmR)
    ((add_le_add_iff_left _).2 hrm)) ?_, hmw⟩
  obtain ⟨hyR, hxy⟩ := M_spec (e := e) (g := s) hx
  set y := S.M e s (leWe j * d + r) with hydef
  rcases le_or_gt (leWe j * (d + 1)) y with hbig | hlt
  · calc leWe j * d + S.M e s r ≤ leWe j * d + leWe j := (add_le_add_iff_left _).2 hmw
      _ = leWe j * (d + 1) := by rw [mul_add_one]
      _ ≤ y := hbig
  · have hu0 := tsU_ne j
    have hdiv1 : d ≤ y / leWe j := (Ordinal.mul_le_iff_le_div hu0).1 (le_self_add.trans hxy)
    have hdiv2 : y / leWe j < d + 1 := (Ordinal.lt_mul_iff_div_lt hu0).1 hlt
    have hdiv : y / leWe j = d := le_antisymm (Order.lt_add_one_iff.1 hdiv2) hdiv1
    have hye : leWe j * d + y % leWe j = y := by rw [← hdiv]; exact Ordinal.div_add_mod y _
    have hry : r ≤ y % leWe j := by
      have : leWe j * d + r ≤ leWe j * d + y % leWe j := by rw [hye]; exact hxy
      exact (add_le_add_iff_left _).1 this
    have hmy : S.M e s r ≤ y % leWe j := M_le (tz_rem_mem j y hyR) hry
    calc leWe j * d + S.M e s r ≤ leWe j * d + y % leWe j := (add_le_add_iff_left _).2 hmy
      _ = y := hye

/-- **Rounding up keeps the components**: in `R = Cl(e, s)` (`s` strongly critical, `Ω₁ < s < Ω₂`,
`R ∩ Ω₂ ⊆ s`), if every component of `x < W` is in `P` (`P 1`, `P` closed under `+ 1`) and `M(x) < W`, then every
component of `M(x)` is in `P` and below `s`. -/
theorem tz_M_cd {e s : Ordinal.{0}} (hsS : SC s) (hs1 : Om 1 < s)
    (hR : ∀ x ∈ S.CSet e s, x < Om (1 + 1) → x < s) {P : Ordinal.{0} → Prop} (hP1 : P 1)
    (hPs : ∀ z, P z → P (z + 1)) :
    ∀ {x : Ordinal.{0}}, TzG P x → x < leWe (Om (1 + 1)) → S.M e s x < leWe (Om (1 + 1)) →
      TzG (fun z => P z ∧ z < s) (S.M e s x) := by
  have h1s : (1 : Ordinal.{0}) < s := Gg.gg_one_lt_of_SC hsS
  have hslim : IsSuccLimit s := ev_isSuccLimit_of_inE (Gg.gg_SC_eps hsS)
  intro x hx
  induction hx with
  | zero =>
    intro _ _
    rw [M_eq_self (CSet.zero_mem e s)]; exact TzG.zero
  | @cons j d r hj hd hd0 hd2 hr hRr ih =>
    intro hxW hMW
    have hxL : leWe j * d + r < S.Lam := hxW.trans tz_W_lt_Lam
    obtain ⟨hyR, hxy⟩ := M_spec (e := e) (g := s) hxL
    obtain ⟨hxj1, hxj2⟩ := tz_term_bounds hd0 hd2 hr
    obtain ⟨hdig1, hdig2⟩ := tz_hull_dig hsS hs1 hR _ hyR hMW
    have hjs : j < s := by
      by_contra hc
      push Not at hc
      exact absurd (((leWe_mono hc).trans hxj1).trans hxy) (not_le.2 hdig1)
    rcases lt_or_ge d s with hds | hds
    · obtain ⟨heq, hmw⟩ := tz_M_term (e := e) hjs hds hr hxL
      rw [heq]
      rcases hmw.lt_or_eq with hlt | hmeq
      · have hrW : r < leWe (Om (1 + 1)) := hr.trans_le (hxj1.trans hxW.le)
        have hmW : S.M e s r < leWe (Om (1 + 1)) := hlt.trans_le (hxj1.trans hxW.le)
        exact TzG.cons ⟨hj, hjs⟩ ⟨hd, hds⟩ hd0 hd2 hlt (ih hrW hmW)
      · rw [hmeq, ← mul_add_one]
        rw [← add_zero (leWe j * (d + 1))]
        exact TzG.cons ⟨hj, hjs⟩ ⟨hPs d hd, hslim.add_one_lt hds⟩ (lt_of_le_of_lt zero_le (lt_add_one d))
          (SC.add_one_lt ts_SC_Om2 hd2) (leWe_pos j) TzG.zero
    · -- a digit `≥ s`: `M(x) = w_{j+1}`
      have hj1 : j + 1 < s := hslim.add_one_lt hjs
      have hwR : leWe (j + 1) ∈ S.CSet e s := leWe_mem (CSet.of_lt hj1)
      have hMeq : S.M e s (leWe j * d + r) = leWe (j + 1) := by
        refine le_antisymm (M_le hwR hxj2.le) (not_lt.1 fun hlt => ?_)
        set y := S.M e s (leWe j * d + r) with hydef
        have hu0 := tsU_ne j
        have hy1 : y < leWe j * Om (1 + 1) := by rw [← leWe_succ]; exact hlt
        have hdiv2 : y / leWe j < Om (1 + 1) := (Ordinal.lt_mul_iff_div_lt hu0).1 hy1
        have hdiv1 : d ≤ y / leWe j := (Ordinal.mul_le_iff_le_div hu0).1 (le_self_add.trans hxy)
        have := hdig2 j
        rw [Ordinal.mod_eq_of_lt hdiv2] at this
        exact absurd (hds.trans hdiv1) (not_le.2 this)
      rw [hMeq, ← mul_one (leWe (j + 1)), ← add_zero (leWe (j + 1) * 1)]
      exact TzG.cons ⟨hPs j hj, hj1⟩ ⟨hP1, h1s⟩ zero_lt_one (Gg.gg_one_lt_of_SC ts_SC_Om2) (leWe_pos _) TzG.zero

/-! ## Own arguments with code components -/

/-- **`ψ_{Ω₂}(e)` is a code over `q` when `e` is own, every component of `e` is a code over `q`, and `ψ(e) < X`.** -/
theorem tz_own_code {q : Ordinal.{0}} (hq : SC q) :
    ∀ e, e ∈ S.CSet e (S.psi e (Om (1 + 1))) → TzG (TlCl q) e → S.psi e (Om (1 + 1)) < tlX →
      TlCl q (S.psi e (Om (1 + 1))) := by
  have hO1S : SC (Om1 : Ordinal.{0}) := by rw [tw_Om1_eq]; exact Ph.ph_SC_Om1
  have hsmallP : ∀ {z : Ordinal.{0}}, TzG (TlCl q) z → z < Om (1 + 1) → TlCl q z := by
    intro z hz hz2
    rcases eq_or_ne z 0 with rfl | hz0
    · exact TlCl.zero hq.1
    exact (tzG_inv (j := 0) (d := z) (r := 0) (pos_iff_ne_zero.2 hz0) hz2 (by rw [leWe_zero]; exact zero_lt_one)
      (by rw [leWe_zero, one_mul, add_zero]; exact hz)).2.1
  intro e
  induction e using WellFoundedLT.induction with
  | ind e IH =>
  intro hown hG hsX
  set s := S.psi e (Om (1 + 1)) with hsdef
  have hsS : SC s := ts_psi_SC e
  have hs1 : Om 1 < s := ts_Om1_lt_psi e
  have hs1' : Om1 < s := by rw [tw_Om1_eq]; exact hs1
  obtain ⟨hnf, hyz, hlz⟩ := tl_nf hsS hs1' hsX
  generalize hβdef : tlLev s = β at hnf hyz hlz
  generalize hydef : tlI β s = y at hnf hyz
  have hβX : β < tlX := hlz.trans hsX
  have hyX : y < tlX := hyz.trans hsX
  have hyc : TlCl Om1 y := tl_code (by rw [tw_Om1_eq]; exact Om_pos one_ne_zero) y hyX (tlDat_lt_Om1 y)
  have h1' : Om 1 < rhF β y := by rw [hnf]; exact hs1
  have hyz' : y < rhF β y := by rw [hnf]; exact hyz
  have hzX' : rhF β y < tlX := by rw [hnf]; exact hsX
  obtain ⟨B, c, D, hownB, hdvd, hc, hcD, hD2, hval, -, -, hcase⟩ :=
    twRun (S := S) hO1S le_rfl hyc hβX hyz' h1' hzX'
  have hβz : β < rhF β (c + D) := by rw [hcD, hnf]; exact hlz
  obtain ⟨hψe, howne⟩ := twRun_eq hownB hdvd hc hD2 hval hβz
  rw [hcD, hnf] at hψe
  have hee : e = B + leWe β * D := ts_own_unique hown howne (by rw [hψe])
  -- the components `β`, `c`, `D` are codes
  have hcodes : TlCl q β ∧ TlCl q c ∧ TlCl q D := by
    rcases hcase with ⟨hβ0, hB0, hc0⟩ | ⟨hβ1, hBw, hcs⟩ | ⟨hc1, hcf, hdvd1⟩
    · subst hβ0; subst hB0; subst hc0
      rw [zero_add, leWe_zero, one_mul] at hee
      rw [hee] at hG
      refine ⟨TlCl.zero hq.1, ?_, hsmallP hG hD2⟩
      rw [← tw_Om1_eq]; exact TlCl.add TlCl.om (TlCl.one hq.1)
    · subst hBw; subst hcs
      have he2 : e = leWe β * (1 + D) + 0 := by rw [hee, add_zero, mul_add, mul_one]
      rw [he2] at hG
      have h1D : 0 < 1 + D := lt_of_lt_of_le zero_lt_one le_self_add
      have h1D2 : 1 + D < Om (1 + 1) := ts_Om2_indec.add_lt (Gg.gg_one_lt_of_SC ts_SC_Om2) hD2
      obtain ⟨h1, h2, -⟩ := tzG_inv h1D h1D2 (leWe_pos β) hG
      refine ⟨h1, ?_, ?_⟩
      · rcases twS_cases β with e' | e' | e' <;> rw [e']
        · rw [← tw_Om1_eq]; exact TlCl.add TlCl.om (TlCl.one hq.1)
        · exact TlCl.one hq.1
        · exact TlCl.zero hq.1
      · have := (tlDec hq _ h2).1 1 (TlCl.one hq.1) le_self_add
        rwa [Ordinal.add_sub_cancel] at this
    · have hD0 : D ≠ 0 := by
        rintro rfl
        rw [add_zero] at hcD
        rw [← hcD, hcf] at hyz'
        exact lt_irrefl _ hyz'
      have hG' : TzG (TlCl q) (B + leWe β * D) := by rw [← hee]; exact hG
      obtain ⟨h1, h2, h3⟩ := tzG_snoc_inv (pos_iff_ne_zero.2 hD0) hD2 hG' B hdvd1 rfl
      have hBe : B < e := by
        rw [hee]; exact lt_add_of_pos_right _ (mul_pos (leWe_pos β) (pos_iff_ne_zero.2 hD0))
      have hcX : c < tlX := (le_self_add.trans_eq hcD).trans_lt hyX
      have hψB : S.psi B (Om (1 + 1)) = c := by rw [← hc, hcf]
      have := IH B hBe hownB h3 (by rw [hψB]; exact hcX)
      rw [hψB] at this
      exact ⟨h1, this, h2⟩
  obtain ⟨hβc, hcc, hDc⟩ := hcodes
  rw [← hnf, ← hcD]
  exact TlCl.atom hβc (TlCl.add hcc hDc) (by rw [hcD, tw_Om1_eq]; exact h1')

/-- The components predicate of the hull lemma: a code over `q`, or `≥ X`. -/
def TzK (q : Ordinal.{0}) (z : Ordinal.{0}) : Prop := z < tlX → TlCl q z

theorem tzK_zero {q : Ordinal.{0}} (hq : SC q) : TzK q 0 := fun _ => TlCl.zero hq.1

theorem tzK_one {q : Ordinal.{0}} (hq : SC q) : TzK q 1 := fun _ => TlCl.one hq.1

theorem tzK_add {q : Ordinal.{0}} (a b : Ordinal.{0}) (ha : TzK q a) (hb : TzK q b) : TzK q (a + b) :=
  fun h => TlCl.add (ha (le_self_add.trans_lt h)) (hb (le_add_self.trans_lt h))

theorem tzK_phi {q : Ordinal.{0}} (a b : Ordinal.{0}) (ha : TzK q a) (hb : TzK q b) : TzK q (veblen a b) :=
  fun h => TlCl.phi (ha ((left_le_veblen a b).trans_lt h)) (hb ((right_le_veblen a b).trans_lt h))

/-- **The key lemma**: for `e` whose base-`Ω₂` components are codes over `q` or `≥ X`, `ψ_{Ω₂}(e) < X` is a code over
`q`. -/
theorem tz_key {q : Ordinal.{0}} (hq : SC q) {e : Ordinal.{0}} (hG : TzG (TzK q) e)
    (hsX : S.psi e (Om (1 + 1)) < tlX) : TlCl q (S.psi e (Om (1 + 1))) := by
  have hκ : S.InR (Om (1 + 1)) := InR_Om_succ 1
  set s := S.psi e (Om (1 + 1)) with hsdef
  have hWX : S.psi (leWe (Om (1 + 1))) (Om (1 + 1)) = tlX := ts_psiW_eq_X
  have heW : e < leWe (Om (1 + 1)) := by
    by_contra hc
    push Not at hc
    have := (psi_mono hκ hc).1
    rw [hWX] at this
    exact absurd hsX (not_lt.2 this)
  have heL : e < S.Lam := heW.trans tz_W_lt_Lam
  obtain ⟨hmR, hem⟩ := M_spec (e := e) (g := s) heL
  have hψm : S.psi (S.M e s e) (Om (1 + 1)) = s := psi_M_eq hκ heL
  have hownm := M_mem_self (S := S) hκ heL
  have hmW : S.M e s e < leWe (Om (1 + 1)) := by
    by_contra hc
    push Not at hc
    have := (psi_mono hκ hc).1
    rw [hWX, hψm] at this
    exact absurd hsX (not_lt.2 this)
  have hsS : SC s := ts_psi_SC e
  have hs1 : Om 1 < s := ts_Om1_lt_psi e
  have hR : ∀ x ∈ S.CSet e s, x < Om (1 + 1) → x < s := fun x hx hx2 => lt_psi_of_mem hκ hx hx2
  have hcd := tz_M_cd (e := e) hsS hs1 hR (tzK_one hq) (fun z hz => tzK_add z 1 hz (tzK_one hq)) hG heW hmW
  have hcd' : TzG (TlCl q) (S.M e s e) := hcd.mono fun z hz => hz.1 (hz.2.trans hsX)
  have := tz_own_code hq (S.M e s e) hownm hcd' (by rw [hψm]; exact hsX)
  rwa [hψm] at this

end Googology.Trans.PoR.InaccPsi.R2.Tz

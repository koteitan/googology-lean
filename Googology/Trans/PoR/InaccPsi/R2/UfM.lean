import Googology.Trans.PoR.InaccPsi.R2.UfCa
import Googology.Trans.PoR.InaccPsi.R2.TzM

/-!
# The collapse `ψ_{Ω₂}(e) < B₂` of an argument with code components is a code

`ψ = ψ_{Ω₂}`, `E₂ = ε_{Ω₂+1}`, `B₂ = Uc.ucB = ψ(E₂)`, `UcCl q` the codes over `q` (`R2.UcCl`), `UfP P x` (every
hereditary base-`Ω₂` component of `x` is in `P`, `R2.UfCa`).  An argument `e` is *own* when `e ∈ Cl(e, ψ(e))`;
`M(x)` is the least member of `R = Cl(e, ψ(e))` at or above `x` (`InaccSeq.M`), `M(e)` is own and `ψ(M(e)) = ψ(e)`.
The proofs of `R2.TzM` (bound `X`, components below `W = Ω₂^{Ω₂}`) one cardinal up (bound `B₂`, hereditary
components below `E₂`):

* `ufP_succ`, `uf_E_lt_Lam`, `uf_tzG` (below `W` the components are those of `Tz.TzG`);
* `uf_M_cd` (**rounding up keeps the components**: in `R = Cl(e, s)` with every member below `E₂` having its
  components below `s`, if every component of `x < E₂` is in `P` (`0, 1 ∈ P`, `P` closed under `+ 1`) and
  `M(x) < E₂`, every component of `M(x)` is in `P`);
* `uf_own_code` (**`ψ(e) < B₂` is a code over `q` when `e` is own and every component of `e` is a code over `q`**, by
  the run `e = B + Ω₂^λ·D` of `Uf.ufRun` and induction on `e`; below `X` this is `Tz.tz_own_code`);
* `uf_key` (**`ψ(e) < B₂` is a code over `q` for every `e` whose components are codes over `q` or `≥ B₂`**:
  `ψ(e) = ψ(M(e))`, `M(e)` is own with code components).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Tl

variable {S : InaccSeq.{0}}

/-- **`x + 1` keeps the components in `P`** (`P` closed under `+ 1`). -/
theorem ufP_succ {P : Ordinal.{0} → Prop} (hPs : ∀ z, P z → P (z + 1)) :
    ∀ x, x + 1 < ucE → UfP P x → UfP P (x + 1) := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hE hx
  by_cases h1 : x < OmTwo
  · have h1' : x + 1 < OmTwo := uc_SC_Om2.add_one_lt h1
    exact (ufP_small h1').2 (hPs x ((ufP_small h1).1 hx))
  have h2 := not_lt.1 h1
  have hxE : x < ucE := (lt_add_one x).trans hE
  set e := log OmTwo x with hedef
  set d := x / OmTwo ^ e with hddef
  set r := x % OmTwo ^ e with hrdef
  have hx0 : x ≠ 0 := uc_ne_zero h2
  have he1 : 1 ≤ e := one_le_iff_ne_zero.2 (log_pos uc_one_lt_Om2 hx0 h2).ne'
  have hcnf : OmTwo ^ e * d + r = x := uc_cnf_eq x
  have hr : r < OmTwo ^ e := Ordinal.mod_lt _ (uc_W_pos e).ne'
  have hd : d < OmTwo := uc_div_lt x
  have hd0 : d ≠ 0 := (uc_div_pos h2).ne'
  have hlim : IsSuccLimit (OmTwo ^ e) := by
    rw [uc_W_eq]
    exact isSuccLimit_opow_left isSuccLimit_omega0 (mul_ne_zero (uc_SC_Om2.1.ne') (zero_lt_one.trans_le he1).ne')
  have hr1 : r + 1 < OmTwo ^ e := hlim.add_one_lt hr
  have heq : x + 1 = OmTwo ^ e * d + (r + 1) := by rw [← hcnf, add_assoc]
  have hrl : r < x := uc_mod_lt h2
  have hcx := (ufP_cnf (P := P) he1 hd0 hd hr (by rw [hcnf]; exact hxE))
  rw [hcnf] at hcx
  obtain ⟨hPe, hPd, hPr⟩ := hcx.1 hx
  have hr1E : r + 1 < ucE :=
    (hr1.trans_le ((le_mul_left _ (pos_iff_ne_zero.2 hd0)).trans (le_self_add.trans_eq hcnf))).trans hxE
  rw [heq, ufP_cnf he1 hd0 hd hr1 (by rw [← heq]; exact hE)]
  exact ⟨hPe, hPd, IH r hrl hr1E hPr⟩

theorem uf_E_lt_Lam : ucE < S.Lam := lt_Lam_of_mem (b := 0) zero_le (uc_E_mem (S := S) 0 0)

/-- **Below `W` the components give `Tz.TzG`.** -/
theorem uf_tzG {P : Ordinal.{0} → Prop} (hP0 : P 0) :
    ∀ e, e < Le.leWe (Om (1 + 1)) → UfP P e → Tz.TzG P e := by
  intro e
  induction e using WellFoundedLT.induction with
  | ind e IH =>
  intro heW he
  rcases eq_or_ne e 0 with rfl | he0
  · exact Tz.TzG.zero
  by_cases h1 : e < OmTwo
  · have h := Tz.TzG.cons (P := P) (j := 0) (d := e) (r := 0) hP0 ((ufP_small h1).1 he) (pos_iff_ne_zero.2 he0)
      (by rw [← uf_Om2]; exact h1) (by rw [Le.leWe_zero]; exact zero_lt_one) Tz.TzG.zero
    rwa [Le.leWe_zero, one_mul, add_zero] at h
  have h2 := not_lt.1 h1
  set j := log OmTwo e with hjdef
  set d := e / OmTwo ^ j with hddef
  set r := e % OmTwo ^ j with hrdef
  have hj1 : 1 ≤ j := one_le_iff_ne_zero.2 (log_pos uc_one_lt_Om2 he0 h2).ne'
  have hcnf : OmTwo ^ j * d + r = e := uc_cnf_eq e
  have hr : r < OmTwo ^ j := Ordinal.mod_lt _ (uc_W_pos j).ne'
  have hd : d < OmTwo := uc_div_lt e
  have hd0 : d ≠ 0 := (uc_div_pos h2).ne'
  have hWe : Le.leWe (Om (1 + 1)) = OmTwo ^ OmTwo := by rw [uc_leWe, ← uf_Om2]
  have hj2 : j < OmTwo := by
    rw [hWe] at heW
    exact (lt_opow_iff_log_lt uc_one_lt_Om2 he0).1 heW
  have hEe : e < ucE := heW.trans_le (by rw [hWe]; exact (uc_W_lt_E ucE_gt).le)
  have hc := (ufP_cnf (P := P) hj1 hd0 hd hr (by rw [hcnf]; exact hEe))
  rw [hcnf] at hc
  obtain ⟨hPj, hPd, hPr⟩ := hc.1 he
  have hrl : r < e := uc_mod_lt h2
  have h := Tz.TzG.cons (P := P) ((ufP_small hj2).1 hPj) hPd (pos_iff_ne_zero.2 hd0) (by rw [← uf_Om2]; exact hd)
    (by rw [uc_leWe]; exact hr) (IH r hrl (hrl.trans heW) hPr)
  rwa [uc_leWe, hcnf] at h

/-- **Rounding up keeps the components**: in `R = Cl(e, s)` (`s` strongly critical, `Ω₁ < s < Ω₂`) with every
member below `E₂` having its components below `s`, if every component of `x < E₂` is in `P` (`P 0`, `P 1`, `P`
closed under `+ 1`) and `M(x) < E₂`, then every component of `M(x)` is in `P`. -/
theorem uf_M_cd {e s : Ordinal.{0}} (hsS : SC s) (hs1 : Om 1 < s) (hs2 : s < OmTwo)
    (hR : ∀ x ∈ S.CSet e s, UcLt s x) {P : Ordinal.{0} → Prop} (hP0 : P 0) (hP1 : P 1)
    (hPs : ∀ z, P z → P (z + 1)) :
    ∀ x, x < ucE → UfP P x → S.M e s x < ucE → UfP P (S.M e s x) := by
  have h1s : (1 : Ordinal.{0}) < s := uc_one_lt_SC hsS
  have hslim : IsSuccLimit s := ev_isSuccLimit_of_inE (Gg.gg_SC_eps hsS)
  have hO2R : OmTwo ∈ S.CSet e s := by rw [uf_Om2]; exact Mx.mxOm2_mem _ _
  have hWR : ∀ {j : Ordinal.{0}}, j < ucE → UcLt s j → OmTwo ^ j ∈ S.CSet e s := fun hj h => by
    have := uc_W_mem (S := S) (a := e) hj h h1s; rwa [mul_one] at this
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hxE hx hME
  have hxL : x < S.Lam := hxE.trans uf_E_lt_Lam
  obtain ⟨hyR, hxy⟩ := M_spec (e := e) (g := s) hxL
  set y := S.M e s x with hydef
  by_cases h1 : x < OmTwo
  · have hPx := (ufP_small h1).1 hx
    rcases lt_or_ge x s with hxs | hxs
    · rw [hydef, M_eq_self (CSet.of_lt hxs)]; exact (ufP_small h1).2 hPx
    · have hyO : y = OmTwo := by
        refine le_antisymm (M_le hO2R h1.le) (not_lt.1 fun hlt => ?_)
        have := (ucLt_small hlt).1 (hR y hyR)
        exact absurd (hxs.trans hxy) (not_le.2 this)
      rw [hyO]
      intro c hc
      rw [ucComps_Om2] at hc
      rcases hc with rfl | hc
      · exact hP1
      · rw [mem_singleton_iff] at hc; rw [hc]; exact hP0
  have h2 := not_lt.1 h1
  set j := log OmTwo x with hjdef
  set d := x / OmTwo ^ j with hddef
  set r := x % OmTwo ^ j with hrdef
  have hx0 : x ≠ 0 := uc_ne_zero h2
  have hj1 : 1 ≤ j := one_le_iff_ne_zero.2 (log_pos uc_one_lt_Om2 hx0 h2).ne'
  have hcnf : OmTwo ^ j * d + r = x := uc_cnf_eq x
  have hr : r < OmTwo ^ j := Ordinal.mod_lt _ (uc_W_pos j).ne'
  have hd : d < OmTwo := uc_div_lt x
  have hd0 : d ≠ 0 := (uc_div_pos h2).ne'
  have hjl : j < x := uc_log_lt h2 hxE
  have hrl : r < x := uc_mod_lt h2
  have hjE : j < ucE := hjl.trans hxE
  have hcx := ufP_cnf (P := P) hj1 hd0 hd hr (by rw [hcnf]; exact hxE)
  rw [hcnf] at hcx
  obtain ⟨hPj, hPd, hPr⟩ := hcx.1 hx
  have hxj1 : OmTwo ^ j ≤ x := by rw [← hcnf]; exact (le_mul_left _ (pos_iff_ne_zero.2 hd0)).trans le_self_add
  have hxj2 : x < OmTwo ^ (j + 1) := by
    exact lt_opow_succ_log_self uc_one_lt_Om2 x
  -- the exponent of `y` is in `R` and at least `j`
  have hyE : y < ucE := hME
  have hy0 : y ≠ 0 := (lt_of_lt_of_le (uc_W_pos j) (hxj1.trans hxy)).ne'
  have hy2 : OmTwo ≤ y := (h2.trans hxy)
  have hlogy : UcLt s (log OmTwo y) := by
    have hyc := hR y hyR
    have hc := ucLt_cnf (q := s) (one_le_iff_ne_zero.2 (log_pos uc_one_lt_Om2 hy0 hy2).ne') (uc_div_pos hy2).ne'
      (uc_div_lt y) (Ordinal.mod_lt _ (uc_W_pos _).ne') (by rw [uc_cnf_eq]; exact hyE)
    rw [uc_cnf_eq] at hc
    exact (hc.1 hyc).1
  have hjy : j ≤ log OmTwo y := le_log_of_opow_le uc_one_lt_Om2 (hxj1.trans hxy)
  by_cases hjs : UcLt s j
  · have hwR := hWR hjE hjs
    rcases lt_or_ge d s with hds | hds
    · -- `M(w_j·d + r) = w_j·d + M(r)`
      have hwdR : OmTwo ^ j * d ∈ S.CSet e s := uc_W_mem (S := S) hjE hjs hds
      have hrL : r < S.Lam := hrl.trans hxL
      obtain ⟨hmR, hrm⟩ := M_spec (e := e) (g := s) hrL
      have hmw : S.M e s r ≤ OmTwo ^ j := M_le hwR hr.le
      have heqM : y = OmTwo ^ j * d + S.M e s r := by
        refine le_antisymm (M_le (CSet.add_mem hwdR hmR) (by rw [← hcnf]; exact (add_le_add_iff_left _).2 hrm)) ?_
        rcases le_or_gt (OmTwo ^ j * (d + 1)) y with hbig | hlt
        · calc OmTwo ^ j * d + S.M e s r ≤ OmTwo ^ j * d + OmTwo ^ j := (add_le_add_iff_left _).2 hmw
            _ = OmTwo ^ j * (d + 1) := by rw [mul_add_one]
            _ ≤ y := hbig
        · have hu0 := (uc_W_pos j).ne'
          have hdiv1 : d ≤ y / OmTwo ^ j :=
            (Ordinal.mul_le_iff_le_div hu0).1 (le_self_add.trans (by rw [hcnf]; exact hxy))
          have hdiv2 : y / OmTwo ^ j < d + 1 := (Ordinal.lt_mul_iff_div_lt hu0).1 hlt
          have hdiv : y / OmTwo ^ j = d := le_antisymm (Order.lt_add_one_iff.1 hdiv2) hdiv1
          have hye : OmTwo ^ j * d + y % OmTwo ^ j = y := by rw [← hdiv]; exact Ordinal.div_add_mod y _
          have hry : r ≤ y % OmTwo ^ j := by
            have : OmTwo ^ j * d + r ≤ OmTwo ^ j * d + y % OmTwo ^ j := by rw [hye, hcnf]; exact hxy
            exact (add_le_add_iff_left _).1 this
          have hmod : y % OmTwo ^ j ∈ S.CSet e s := by
            have := Tz.tz_rem_mem (S := S) j y hyR; rwa [uc_leWe] at this
          have hmy : S.M e s r ≤ y % OmTwo ^ j := M_le hmod hry
          calc OmTwo ^ j * d + S.M e s r ≤ OmTwo ^ j * d + y % OmTwo ^ j := (add_le_add_iff_left _).2 hmy
            _ = y := hye
      rcases hmw.lt_or_eq with hlt | hmeq
      · have hME' : OmTwo ^ j * d + S.M e s r < ucE := by rw [← heqM]; exact hyE
        rw [heqM, ufP_cnf hj1 hd0 hd hlt hME']
        exact ⟨hPj, hPd, IH r hrl (hrl.trans hxE) hPr (hlt.trans_le ((le_mul_left _ (pos_iff_ne_zero.2 hd0)).trans
          le_self_add) |>.trans_le (by rw [← heqM]) |>.trans hyE)⟩
      · rw [heqM, hmeq, ← mul_add_one]
        have hd1 : d + 1 < OmTwo := uc_SC_Om2.add_one_lt hd
        have hyy : OmTwo ^ j * (d + 1) = y := by rw [heqM, hmeq, mul_add_one]
        have hE' : OmTwo ^ j * (d + 1) + 0 < ucE := by rw [add_zero, hyy]; exact hyE
        have := ufP_cnf (P := P) hj1 (by simp) hd1 (uc_W_pos j) hE'
        rw [add_zero] at this
        exact this.2 ⟨hPj, hPs d hPd, ufP_zero hP0⟩
    · -- a digit `≥ s`: `M(x) = w_{j+1}`
      have hj1E : j + 1 < ucE := uc_E_indec hjE (uc_one_lt_Om2.trans ucE_gt)
      have hjs1 : UcLt s (j + 1) := ucLt_succ hsS hj1E hjs
      have hw1R := hWR hj1E hjs1
      have hMeq : y = OmTwo ^ (j + 1) := by
        refine le_antisymm (M_le hw1R hxj2.le) (not_lt.1 fun hlt => ?_)
        have hu0 := (uc_W_pos j).ne'
        have hy1 : y < OmTwo ^ j * OmTwo := by rw [← uc_W_succ]; exact hlt
        have hdiv2 : y / OmTwo ^ j < OmTwo := (Ordinal.lt_mul_iff_div_lt hu0).1 hy1
        have hdiv1 : d ≤ y / OmTwo ^ j :=
          (Ordinal.mul_le_iff_le_div hu0).1 (le_self_add.trans (by rw [hcnf]; exact hxy))
        have := uc_dig_lt hsS.1 hyE (hR y hyR) j
        rw [Ordinal.mod_eq_of_lt hdiv2] at this
        exact absurd (hds.trans hdiv1) (not_le.2 this)
      rw [hMeq]
      have hE' : OmTwo ^ (j + 1) * 1 + 0 < ucE := by rw [mul_one, add_zero, ← hMeq]; exact hyE
      have := ufP_cnf (P := P) (le_add_self) one_ne_zero uc_one_lt_Om2 (uc_W_pos (j + 1)) hE'
      rw [mul_one, add_zero] at this
      exact this.2 ⟨ufP_succ hPs j hj1E hPj, hP1, ufP_zero hP0⟩
  · -- the exponent `j` is not in `R`: `M(x) = w_{M(j)}`
    have hjL : j < S.Lam := hjE.trans uf_E_lt_Lam
    obtain ⟨hmjR, hjmj⟩ := M_spec (e := e) (g := s) hjL
    set m := S.M e s j with hmdef
    have hlyR : log OmTwo y ∈ S.CSet e s := (uc_mem (S := S) hsS.1 _ ((log_le_self _ _).trans_lt hyE) hlogy).1
    have hmly : m ≤ log OmTwo y := M_le hlyR hjy
    have hmE : m < ucE := hmly.trans_lt ((log_le_self _ _).trans_lt hyE)
    have hms : UcLt s m := hR m hmjR
    have hjm : j < m := lt_of_le_of_ne hjmj fun h => hjs (h ▸ hms)
    have hwmR := hWR hmE hms
    have hMeq : y = OmTwo ^ m := by
      refine le_antisymm (M_le hwmR (hxj2.le.trans (opow_le_opow_right uc_SC_Om2.1
        (Order.add_one_le_of_lt hjm)))) ?_
      exact (opow_le_opow_right uc_SC_Om2.1 hmly).trans (opow_log_le_self _ hy0)
    rw [hMeq]
    have hm1 : 1 ≤ m := hj1.trans hjm.le
    have hE' : OmTwo ^ m * 1 + 0 < ucE := by rw [mul_one, add_zero, ← hMeq]; exact hyE
    have := ufP_cnf (P := P) hm1 one_ne_zero uc_one_lt_Om2 (uc_W_pos m) hE'
    rw [mul_one, add_zero] at this
    exact this.2 ⟨IH j hjl hjE hPj hmE, hP1, ufP_zero hP0⟩

end Googology.Trans.PoR.InaccPsi.R2.Uf

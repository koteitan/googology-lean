import Googology.Trans.PoR.InaccPsi.R2.GjHX

/-!
# HEREDITARY CODES BELOW `ε_{Ω₁+2}`: the last term of a limit code, with Lemma IMG for the specified logend

For a limit code `c = E^k·d + r ∈ (ε_{Ω₁+1}, ε_{Ω₁+2})` (the exponent `k` a hereditary code) the reading is
`l'(x) + ω^{logend}` with Lemma IMG for the logend function itself (`GiLD` of `R2.GiRS`), as in `R2.GiWl`; the logends
`ε_{x+1}·k(x)` and `ε_{x+1}·k(x) + logend(d(x))` now reach every value below `ε_{x+2}`, and their Lemma IMG is the
specified one (`Gj.gjPkg_of_ex`) with Lemma EXACT `Gj.jh_eNk_pi`, where round 80 used `pkg_eNm` / `pkg_eMt`
(finite exponents, an existential term).

* `gj_giQ_le_succ`, `jh_pkg_eNk` (**Lemma IMG for `y ↦ ε_{y+1}·k(y)`**), `jh_pkg_eNkt` (**for
  `y ↦ ε_{y+1}·k(y) + t(y)`**), `jhLD_ne` (**the data exists at every limit code in `(ε_{Ω₁+1}, ε_{Ω₁+2})`**).

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gj

open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gi
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Gd Googology.Trans.PoR.InaccPsi.R2.Gb

theorem gj_giQ_le_succ {d' : Ordinal.{0}} (hd'E : d' < gfE) : giQ d' ≤ giQ (d' + 1) := by
  unfold giQ
  by_cases h1 : d' < ω
  · rw [if_pos h1]; exact zero_le
  · rw [if_neg h1, if_neg (fun h => h1 ((lt_add_one d').trans h))]; exact (rdc_succ d' hd'E 0).2.1

section Pkg

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **Lemma IMG for `y ↦ ε_{y+1}·k(y)`** (a hereditary code `1 ≤ k < ε_{Ω₁+2}` with gate below every base above `g`). -/
theorem jh_pkg_eNk {g k : Ordinal.{0}} (hgρ : g < ρ) (hk : k ≠ 0) (hkB : k < jhB)
    (hgk : ∀ σ, InE σ → g < σ → jhG k < σ) : GhPkg g ρ δ (fun y => eN y * jhR k y) := by
  have hρE := upsPt_inE h.ρU
  refine gjPkg_of_ex h (C := ∅) hgρ (by simp) ?_ (GjEx.of_bases fun σ ρ' hB hgσ =>
    jh_eNk_pi hB hk hkB (hgk σ hB.1 hgσ))
  exact (eN_E (eN ρ)).mul_lt (lt_eN _) (jhR_lt_eNN hρE hkB (hgk ρ hρE hgρ))

/-- **Lemma IMG for `y ↦ ε_{y+1}·k(y) + t(y)`** (`t` a term of `OT` with constants below the gate). -/
theorem jh_pkg_eNkt {g k : Ordinal.{0}} {t : OT} (hgρ : g < ρ) (hk : k ≠ 0) (hkB : k < jhB)
    (hgk : ∀ σ, InE σ → g < σ → jhG k < σ) (hct : ∀ σ, InE σ → g < σ → OT.CB t σ) :
    GhPkg g ρ δ (fun y => eN y * jhR k y + OT.ev t y) := by
  have hρE := upsPt_inE h.ρU
  have hE2 := eN_E (eN ρ)
  refine gjPkg_of_ex h (C := ∅) hgρ (by simp) ?_ (GjEx.of_bases fun σ ρ' hB hgσ => ?_)
  · exact (inE_indec hE2).add_lt (hE2.mul_lt (lt_eN _) (jhR_lt_eNN hρE hkB (hgk ρ hρE hgρ)))
      ((ev_lt_eN (hct ρ hρE hgρ)).trans (lt_eN _))
  · obtain ⟨h1, h2⟩ := jh_eNk_pi hB hk hkB (hgk σ hB.1 hgσ)
    obtain ⟨h3, h4⟩ := pi_ev hB t (hct σ hB.1 hgσ)
    obtain ⟨h5, h6⟩ := pi_add hB h1 h3
    exact ⟨h5, by rw [h6, h2, h4]⟩

end Pkg

/-- **The data `GiLD` exists at every limit code `c ∈ (ε_{Ω₁+1}, ε_{Ω₁+2})`.** -/
theorem jhLD_ne : ∀ c, IsSuccLimit c → gfE < c → c < jhB → Nonempty (GiLD jhK jhR c) := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hl hEc hc
  have hcE : gfE ≤ c := hEc.le
  obtain ⟨hk, hd0, hdE, hr, hdec, hkc, -⟩ := jh_parts hcE hc
  have hkB : log gfE c < jhB := hkc.trans hc
  set k := log gfE c with hkdef
  set d := c / gfE ^ k with hddef
  set r := c % gfE ^ k with hrdef
  have hrc : r < c := mod_opow_log_lt_self gfE (gw_ne_of_le hcE)
  have hgc : jhG c = max (max (jhQ k) (giQ d)) (jhG r) := jhG_dec hcE hc
  have hRc : ∀ x, jhR c x = eN x ^ jhR k x * rdc d x + jhR r x := fun x => jhR_dec hcE hc x
  have hgK : ∀ b, jhK.gt b = jhG b := fun _ => rfl
  have hEk : gfE ≤ gfE ^ k := by
    calc gfE = gfE ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ gfE ^ k := opow_le_opow_right eW_E.pos (one_le_iff_ne_zero.2 hk)
  have hcp_ge : ∀ b, b ≠ 0 → gfE ≤ gfE ^ k * b := fun b hb =>
    hEk.trans (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hb))
  have hcnfB : ∀ b t, b < gfE → t < gfE ^ k → gfE ^ k * b + t < jhB := by
    intro b t hbE ht
    have hk1B : k + 1 < jhB := jhB_lim.add_one_lt hkB
    calc gfE ^ k * b + t < gfE ^ k * b + gfE ^ k := (add_lt_add_iff_left _).2 ht
      _ = gfE ^ k * (b + 1) := by rw [mul_add_one]
      _ ≤ gfE ^ k * gfE := mul_le_mul_left' (Order.add_one_le_of_lt hbE) _
      _ = gfE ^ (k + 1) := by rw [opow_add, opow_one]
      _ < jhB := jhB_gt_pow hk1B
  have hRp : ∀ b t x, b ≠ 0 → b < gfE → t < gfE ^ k →
      jhR (gfE ^ k * b + t) x = eN x ^ jhR k x * rdc b x + jhR t x :=
    fun b t x hb hbE ht => jhR_cnf hk hb hbE ht (hcnfB b t hbE ht) x
  have hGp : ∀ b t, b ≠ 0 → b < gfE → t < gfE ^ k → jhG (gfE ^ k * b + t) = max (max (jhQ k) (giQ b)) (jhG t) :=
    fun b t hb hbE ht => jhG_cnf hk hb hbE ht (hcnfB b t hbE ht)
  have hk0 : (0 : Ordinal.{0}) < gfE ^ k := opow_pos _ eW_E.pos
  have hgkx : ∀ σ, InE σ → jhG c < σ → jhG k < σ := fun σ hσ h => (jh_parts_g hσ hcE hc h).1
  have hKpos : ∀ x, InE x → 0 < jhR k x := fun x hx => jhR_pos hx hk hkB
  rcases eq_or_ne r 0 with hr0 | hr0
  · -- `r = 0`: `c = E^k·d`
    have hRc0 : ∀ x, jhR c x = eN x ^ jhR k x * rdc d x := fun x => by
      rw [hRc, hr0, jhR_low eW_E.pos, rdc_zero, add_zero]
    have hgc0 : jhG c = max (jhQ k) (giQ d) := by rw [hgc, hr0, jhG_zero, max_eq_left zero_le]
    have hcd : c = gfE ^ k * d := by rw [← hdec, hr0, add_zero]
    rcases zero_or_succ_or_isSuccLimit d with h0 | ⟨d', hsucc⟩ | hdl
    · exact absurd h0 hd0
    · -- `d = d' + 1`: the logend is `ε_{x+1}·k(x)`
      rw [succ_eq_add_one] at hsucc
      have hd'E : d' < gfE := (lt_add_one d').trans (by rw [hsucc]; exact hdE)
      have hRs : ∀ x, jhR c x = eN x ^ jhR k x * rdc d' x + ω ^ (eN x * jhR k x) := fun x => by
        rw [hRc0, ← hsucc, (rdc_succ d' hd'E x).1, mul_add_one, gw_eNpow]
      have hlg : ∀ x, lg (jhR c x) = eN x * jhR k x := fun x => by
        rw [hRs]; exact Ge.lg_add_opow (gw_dvd le_rfl)
      refine ⟨{
        cp := if d' = 0 then gfE else gfE ^ k * d' + 0
        lp := (fun x => eN x ^ jhR k x * rdc d' x)
        cp_ge := ?_
        cp_lt := ?_
        cp_g := ?_
        dec := ?_
        pkg := ?_ }⟩
      all_goals try simp only [hgK]
      · split_ifs with h0
        · exact le_rfl
        · rw [add_zero]; exact hcp_ge d' h0
      · split_ifs with h0
        · exact hEc
        · rw [hcd, add_zero, ← hsucc]
          exact (mul_lt_mul_iff_right₀ hk0).2 (lt_add_one d')
      · split_ifs with h0
        · rw [jhG_E]; exact zero_le
        · rw [hGp d' 0 h0 hd'E hk0, jhG_zero, max_eq_left zero_le, hgc0, ← hsucc]
          exact max_le_max le_rfl (gj_giQ_le_succ hd'E)
      · intro x hx _ _
        refine ⟨by rw [hlg x]; exact hRs x, by rw [hlg x]; exact gw_dvd le_rfl,
          by rw [hlg x]; exact (mul_pos (eN_E x).pos (hKpos x hx)).ne', ?_⟩
        split_ifs with h0
        · rw [h0, rdc_zero, mul_zero]; exact zero_le
        · rw [hRp d' 0 x h0 hd'E hk0, jhR_low eW_E.pos, rdc_zero, add_zero]
      · intro ρ τ δ h hg
        refine GhPkg.congr h (jh_pkg_eNk h hg hk hkB (fun σ hσ hgσ => hgkx σ hσ hgσ)) (fun y _ _ _ => ?_) hg
        rw [hlg y]
    · -- `d` a limit: the logend is `ε_{x+1}·k(x) + logend(d(x))`
      obtain ⟨d'', l, dd, hd''d, hg'', hgl, hdd, -, hF⟩ := rdc_lim_facts hdl hdE
      have hdω : ω ≤ d := Ordinal.le_of_dvd hd0 ((isSuccLimit_iff_omega0_dvd.1 hdl).2)
      have hQd : giQ d = gtc d := by unfold giQ; rw [if_neg (not_lt.2 hdω)]
      have hgd : ∀ x, jhG c < x → gtc d < x := fun x h => by
        rw [hgc0, hQd] at h; exact (le_max_right _ _).trans_lt h
      have hd''E : d'' < gfE := hd''d.trans hdE
      have hdec2 : ∀ x, InE x → gtc d < x →
          jhR c x = eN x ^ jhR k x * rdc d'' x + ω ^ (eN x * jhR k x + OT.ev (tlg l dd) x) ∧
            ω ^ (eN x * jhR k x + OT.ev (tlg l dd) x) ∣ eN x ^ jhR k x * rdc d'' x ∧
            lg (jhR c x) = eN x * jhR k x + OT.ev (tlg l dd) x := by
        intro x hx hgx
        obtain ⟨e1, e2, e3, -, -, -⟩ := hF x hx hgx
        have h1 : jhR c x = eN x ^ jhR k x * rdc d'' x + ω ^ (eN x * jhR k x + OT.ev (tlg l dd) x) := by
          rw [hRc0, e1, mul_add, gw_eNpow, ← opow_add, e3]
        have h2 : ω ^ (eN x * jhR k x + OT.ev (tlg l dd) x) ∣ eN x ^ jhR k x * rdc d'' x := by
          rw [e3] at e2
          obtain ⟨m, hm⟩ := e2
          exact ⟨m, by rw [hm, ← mul_assoc, gw_eNpow, ← opow_add]⟩
        exact ⟨h1, h2, by rw [h1]; exact Ge.lg_add_opow h2⟩
      refine ⟨{
        cp := if d'' = 0 then gfE else gfE ^ k * d'' + 0
        lp := (fun x => eN x ^ jhR k x * rdc d'' x)
        cp_ge := ?_
        cp_lt := ?_
        cp_g := ?_
        dec := ?_
        pkg := ?_ }⟩
      all_goals try simp only [hgK]
      · split_ifs with h0
        · exact le_rfl
        · rw [add_zero]; exact hcp_ge d'' h0
      · split_ifs with h0
        · exact hEc
        · rw [hcd, add_zero]
          exact (mul_lt_mul_iff_right₀ hk0).2 hd''d
      · split_ifs with h0
        · rw [jhG_E]; exact zero_le
        · rw [hGp d'' 0 h0 hd''E hk0, jhG_zero, max_eq_left zero_le, hgc0, hQd]
          exact max_le_max le_rfl ((giQ_le d'').trans hg'')
      · intro x hx _ hgx
        obtain ⟨h1, h2, h3⟩ := hdec2 x hx (hgd x hgx)
        refine ⟨by rw [h3]; exact h1, by rw [h3]; exact h2, by rw [h3]; exact (add_pos_of_pos_of_nonneg
          (mul_pos (eN_E x).pos (hKpos x hx)) zero_le).ne', ?_⟩
        split_ifs with h0
        · rw [h0, rdc_zero, mul_zero]; exact zero_le
        · rw [hRp d'' 0 x h0 hd''E hk0, jhR_low eW_E.pos, rdc_zero, add_zero]
      · intro ρ τ δ h hg
        have hct : ∀ σ, InE σ → jhG c < σ → OT.CB (tlg l dd) σ := fun σ hσ hgσ =>
          cb_tlg hσ.pos (hgl.trans_lt (hgd σ hgσ)) (hdd.trans_lt (hgd σ hgσ))
        refine GhPkg.congr h (jh_pkg_eNkt h hg hk hkB (fun σ hσ hgσ => hgkx σ hσ hgσ) hct) (fun y hyE _ hgy => ?_) hg
        rw [(hdec2 y hyE (hgd y hgy)).2.2]
  · -- `r ≠ 0`: `r` a limit
    have hrl : IsSuccLimit r := by
      rcases zero_or_succ_or_isSuccLimit r with h0 | ⟨r', hsucc⟩ | hrl
      · exact absurd h0 hr0
      · exfalso
        rw [succ_eq_add_one] at hsucc
        have e : c = succ (gfE ^ k * d + r') := by rw [← hdec, ← hsucc, ← add_assoc, succ_eq_add_one]
        rw [e] at hl
        exact Order.not_isSuccLimit_succ _ hl
      · exact hrl
    have hgr : ∀ x, jhG c < x → jhG r < x := fun x h => (le_max_right _ _).trans_lt (hgc ▸ h)
    have hrB : r < jhB := hrc.trans hc
    -- the logend of `r(x)` lies below `ε_{x+1}·k(x)`
    have hlgk : ∀ x, InE x → jhG c < x → lg (jhR r x) ≤ eN x * jhR k x := by
      intro x hx hgx
      have hb := jhR_bound hx hrB (hgr x hgx) hk hkB (hgkx x hx hgx) hr
      rw [gw_eNpow] at hb
      have h0 : jhR r x ≠ 0 := by
        rcases lt_or_ge r gfE with hrE' | hrE'
        · rw [jhR_low hrE']; exact (rdc_pos hx hr0 hrE').ne'
        · exact (lt_of_lt_of_le (opow_pos _ (eN_E x).pos) (jh_lead_le hx hrE' hrB)).ne'
      have h1 : ω ^ lg (jhR r x) ≤ jhR r x := Ordinal.le_of_dvd h0 (lg_dvd h0)
      exact ((opow_lt_opow_iff_right one_lt_omega0).1 (h1.trans_lt hb)).le
    rcases lt_or_ge r gfE with hrE | hrE
    · -- `r` a limit below `E`
      obtain ⟨r', l, dd, hr'r, hgr', hgl, hdd, -, hF⟩ := rdc_lim_facts hrl hrE
      have hr'E : r' < gfE := hr'r.trans hrE
      have hr'k : r' < gfE ^ k := hr'E.trans_le hEk
      have hga : ∀ x, jhG c < x → gtc r < x := fun x h => by rw [← jhG_low hrE]; exact hgr x h
      have hdec2 : ∀ x, InE x → jhG c < x →
          jhR c x = (eN x ^ jhR k x * rdc d x + rdc r' x) + ω ^ lg (rdc r x) ∧
            ω ^ lg (rdc r x) ∣ eN x ^ jhR k x * rdc d x + rdc r' x ∧ lg (jhR c x) = lg (rdc r x) ∧
            lg (rdc r x) ≠ 0 := by
        intro x hx hgx
        obtain ⟨e1, e2, -, hω, -, e6⟩ := hF x hx (hga x hgx)
        have hle : lg (rdc r x) ≤ eN x * jhR k x := by
          have := hlgk x hx hgx
          rwa [jhR_low hrE] at this
        have hdv : ω ^ lg (rdc r x) ∣ eN x ^ jhR k x * rdc d x + rdc r' x := Ge.dvd_add' (gw_dvd hle) e2
        have hsum : jhR c x = (eN x ^ jhR k x * rdc d x + rdc r' x) + ω ^ lg (rdc r x) := by
          rw [hRc, jhR_low hrE, add_assoc, ← e1]
        exact ⟨hsum, hdv, by rw [hsum]; exact Ge.lg_add_opow hdv, (Gc.gc_lg_pos e6).ne'⟩
      refine ⟨{
        cp := gfE ^ k * d + r'
        lp := (fun x => eN x ^ jhR k x * rdc d x + rdc r' x)
        cp_ge := (hcp_ge d hd0).trans le_self_add
        cp_lt := ?_
        cp_g := ?_
        dec := ?_
        pkg := ?_ }⟩
      all_goals try simp only [hgK]
      · rw [← hdec]; exact (add_lt_add_iff_left _).2 hr'r
      · rw [hGp d r' hd0 hdE hr'k, jhG_low hr'E, hgc, jhG_low hrE]; exact max_le_max le_rfl hgr'
      · intro x hx _ hgx
        obtain ⟨h1, h2, h3, h4⟩ := hdec2 x hx hgx
        exact ⟨by rw [h3]; exact h1, by rw [h3]; exact h2, by rw [h3]; exact h4,
          by rw [hRp d r' x hd0 hdE hr'k, jhR_low hr'E]⟩
      · intro ρ τ δ h hg
        have hρE := upsPt_inE h.ρU
        have hgρ := hga ρ hg
        obtain ⟨-, -, e3, -, -, e6⟩ := hF ρ hρE hgρ
        have hcb : OT.CB (tlg l dd) ρ := cb_tlg hρE.pos (hgl.trans_lt hgρ) (hdd.trans_lt hgρ)
        have h1 : 1 ≤ OT.ev (tlg l dd) ρ := by rw [← e3]; exact one_le_iff_pos.2 (Gc.gc_lg_pos e6)
        refine GhPkg.congr h (GhPkg.of_img (h.pkg_ot hcb h1)) (fun y hyE _ hgy => ?_) hg
        obtain ⟨-, -, f3, -, -, -⟩ := hF y hyE (hga y hgy)
        rw [(hdec2 y hyE hgy).2.2.1, f3]
    rcases hrE.lt_or_eq with hEr | hEr
    · -- `r > E` a limit: the last term of `r`
      obtain ⟨D⟩ := IH r hrc hrl hEr hrB
      have hDk : D.cp < gfE ^ k := D.cp_lt.trans hr
      have hlgc : ∀ x, InE x → x < Om1 → jhG c < x → lg (jhR c x) = lg (jhR r x) ∧
          ω ^ lg (jhR r x) ∣ eN x ^ jhR k x * rdc d x + D.lp x ∧
          jhR c x = (eN x ^ jhR k x * rdc d x + D.lp x) + ω ^ lg (jhR r x) := by
        intro x hx hx1 hgx
        obtain ⟨e1, e2, -, -⟩ := D.dec x hx hx1 (hgr x hgx)
        have hdv : ω ^ lg (jhR r x) ∣ eN x ^ jhR k x * rdc d x + D.lp x :=
          Ge.dvd_add' (gw_dvd (hlgk x hx hgx)) e2
        have hsum : jhR c x = (eN x ^ jhR k x * rdc d x + D.lp x) + ω ^ lg (jhR r x) := by
          rw [hRc, add_assoc, ← e1]
        exact ⟨by rw [hsum]; exact Ge.lg_add_opow hdv, hdv, hsum⟩
      refine ⟨{
        cp := gfE ^ k * d + D.cp
        lp := (fun x => eN x ^ jhR k x * rdc d x + D.lp x)
        cp_ge := (hcp_ge d hd0).trans le_self_add
        cp_lt := ?_
        cp_g := ?_
        dec := ?_
        pkg := ?_ }⟩
      all_goals try simp only [hgK]
      · rw [← hdec]; exact (add_lt_add_iff_left _).2 D.cp_lt
      · rw [hGp d D.cp hd0 hdE hDk, hgc]; exact max_le_max le_rfl D.cp_g
      · intro x hx hx1 hgx
        obtain ⟨h1, h2, h3⟩ := hlgc x hx hx1 hgx
        obtain ⟨-, -, e3, e4⟩ := D.dec x hx hx1 (hgr x hgx)
        refine ⟨by rw [h1]; exact h3, by rw [h1]; exact h2, by rw [h1]; exact e3, ?_⟩
        rw [hRp d D.cp x hd0 hdE hDk]
        exact add_le_add le_rfl e4
      · intro ρ τ δ h hg
        have hgρ := hgr ρ hg
        refine GhPkg.congr h (gi_pkg_weaken (D.pkg ρ τ δ h hgρ) hgρ) (fun y hyE hy1 hgy => ?_) hg
        exact ((hlgc y hyE hy1 hgy).1).symm
    · -- `r = E`
      have hRE : ∀ x, jhR c x = eN x ^ jhR k x * rdc d x + ω ^ eN x := fun x => by
        rw [hRc, ← hEr, jhR_E, show ω ^ eN x = eN x from eN_E x]
      have hlg : ∀ x, InE x → lg (jhR c x) = eN x := fun x hx => by
        rw [hRE]; exact Ge.lg_add_opow (gw_dvd (gw_one_le_k (hKpos x hx).ne' x))
      refine ⟨{
        cp := gfE ^ k * d + 0
        lp := (fun x => eN x ^ jhR k x * rdc d x)
        cp_ge := by rw [add_zero]; exact hcp_ge d hd0
        cp_lt := ?_
        cp_g := ?_
        dec := ?_
        pkg := ?_ }⟩
      all_goals try simp only [hgK]
      · rw [← hdec, ← hEr]; exact (add_lt_add_iff_left _).2 eW_E.pos
      · rw [hGp d 0 hd0 hdE hk0, hgc, jhG_zero, ← hEr, jhG_E]
      · intro x hx _ _
        refine ⟨by rw [hlg x hx]; exact hRE x, by rw [hlg x hx]; exact gw_dvd (gw_one_le_k (hKpos x hx).ne' x),
          by rw [hlg x hx]; exact (eN_E x).pos.ne', ?_⟩
        rw [hRp d 0 x hd0 hdE hk0, jhR_low eW_E.pos, rdc_zero, add_zero]
      · intro ρ τ δ h hg
        exact GhPkg.congr h (GhPkg.of_img h.pkg_eN) (fun y hyE _ _ => (hlg y hyE).symm) hg

end Googology.Trans.PoR.InaccPsi.R2.Gj

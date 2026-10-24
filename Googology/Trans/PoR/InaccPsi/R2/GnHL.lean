import Googology.Trans.PoR.InaccPsi.R2.GnHX

/-!
# HEREDITARY CODES TO THE BASE `Γ_{Ω₁+1}`: the last term of a limit code, with Lemma IMG for the specified logend

For a limit code `c = G^k·d + r ∈ (ε_{Ω₁+1}, ε_{G+1})` (`G = Γ_{Ω₁+1}`, the exponent `k` a hereditary code) the reading
is `l'(x) + ω^{logend}` with Lemma IMG for the logend function itself (`Gm.GmLD`).  The logends are
`Γ_{x+1}·k(x)` (`d` a successor), `Γ_{x+1}·k(x) + T(x)` (`d` a limit with the logend `T` of `d(x)`), the logend of
`r(x)` (`r` a limit), and `Γ_{x+1}` (`r = G`): they reach every value below `ε_{Γ_{x+1}+1}`, above `Γ_{x+1}` whenever
`k ≥ 1`, where round 84 stopped (the code `Γ_{Ω₁+1}^ω`, logend `ω^{Γ_{y+1}+1}`).  Lemma IMG is the specified one of
`R2.GnImg` (`gnPkg_of_ex`) with Lemma EXACT `gn_mulG_pi`.

* `gn_dvd`, `gn_pkg_Gk` (**Lemma IMG for `y ↦ Γ_{y+1}·k(y)`**), `gn_pkg_Gkt` (**for `y ↦ Γ_{y+1}·k(y) + T(y)`**,
  `T` with Lemma EXACT below `Γ_{y+1}`), `gnLD_low` (limit codes below `G`), `gnLD` (**the data exists at every limit
  code in `(ε_{Ω₁+1}, ε_{G+1})`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gn

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

theorem gn_dvd {x e k q : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (he : e ≤ lgG x * k) :
    ω ^ e ∣ lgG x ^ k * q := by
  rw [gn_Gpow hx hx1]
  exact dvd_trans (opow_dvd_opow ω he) (dvd_mul_right _ _)

theorem gn_one_le_k {x k : Ordinal.{0}} (hk : k ≠ 0) : lgG x ≤ lgG x * k :=
  le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hk)

section Pkg

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **Lemma IMG for `y ↦ Γ_{y+1}·k(y)`** (a hereditary code `1 ≤ k < ε_{G+1}` with gate below every base above
`g`). -/
theorem gn_pkg_Gk {g k : Ordinal.{0}} (hgρ : g < ρ) (hk : k ≠ 0) (hkB : k < gnB)
    (hgk : ∀ σ, InE σ → g < σ → gnG k < σ) : GhPkg g ρ δ (fun y => lgG y * gnR k y) := by
  have hρE := upsPt_inE h.ρU
  refine gnPkg_of_ex h (C := ∅) hgρ (by simp) ?_ (GjEx.of_bases fun σ ρ' hB hgσ =>
    gn_mulG_pi hB hk hkB (hgk σ hB.1 hgσ))
  have h1 := gnR_lt_eNG hρE h.ρ1 (gn_mulG k hk hkB).1 ((gn_mulG k hk hkB).2.1.trans_lt (hgk ρ hρE hgρ))
  rwa [(gn_mulG k hk hkB).2.2 ρ hρE h.ρ1 (hgk ρ hρE hgρ)] at h1

/-- **Lemma IMG for `y ↦ Γ_{y+1}·k(y) + T(y)`** (`T` with Lemma EXACT above the gate, `T(ρ) < Γ_{ρ+1}`). -/
theorem gn_pkg_Gkt {g k : Ordinal.{0}} {T : Ordinal.{0} → Ordinal.{0}} (hgρ : g < ρ) (hk : k ≠ 0) (hkB : k < gnB)
    (hgk : ∀ σ, InE σ → g < σ → gnG k < σ) (hTρ : T ρ < lgG ρ)
    (hex : ∀ σ ρ', Bases σ ρ' → g < σ → T ρ' ∈ TB ρ' σ ∧ pi σ ρ' (T ρ') = T σ) :
    GhPkg g ρ δ (fun y => lgG y * gnR k y + T y) := by
  have hρE := upsPt_inE h.ρU
  have hE2 := eN_E (lgG ρ)
  refine gnPkg_of_ex h (C := ∅) hgρ (by simp) ?_ (GjEx.of_bases fun σ ρ' hB hgσ => ?_)
  · have h1 := gnR_lt_eNG hρE h.ρ1 (gn_mulG k hk hkB).1 ((gn_mulG k hk hkB).2.1.trans_lt (hgk ρ hρE hgρ))
    rw [(gn_mulG k hk hkB).2.2 ρ hρE h.ρ1 (hgk ρ hρE hgρ)] at h1
    exact (inE_indec hE2).add_lt h1 (hTρ.trans (lt_eN _))
  · obtain ⟨h1, h2⟩ := gn_mulG_pi hB hk hkB (hgk σ hB.1 hgσ)
    obtain ⟨h3, h4⟩ := hex σ ρ' hB hgσ
    obtain ⟨h5, h6⟩ := pi_add hB h1 h3
    exact ⟨h5, by rw [h6, h2, h4]⟩

end Pkg

/-- **The data at a limit code below `G`** (from `Gl.gl_ld`). -/
theorem gnLD_low {c : Ordinal.{0}} (hl : IsSuccLimit c) (hEc : gfE < c) (hc : c < gcG 0) :
    Nonempty (GmLD gnK gnR c) := by
  obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := gl_ld c hl hc
  have hlg : ∀ x, InE x → x < Om1 → glG c < x → lg (glR c x) = T x := fun x hx hx1 hg => by
    obtain ⟨e1, e2, -, -⟩ := hdec x hx hx1 hg
    rw [e1]; exact Ge.lg_add_opow e2
  have hgK : ∀ b, b < gcG 0 → gnK.gt b = glG b := fun b hb => gnG_low hb
  refine ⟨{
    cp := if gfE ≤ cp then cp else gfE
    lp := lp
    cp_ge := ?_
    cp_lt := ?_
    cp_g := ?_
    dec := ?_
    pkg := ?_ }⟩
  · split_ifs with h
    · exact h
    · exact le_rfl
  · split_ifs with h
    · exact hcp
    · exact hEc
  · rw [hgK c hc]
    split_ifs with h
    · rw [hgK cp (hcp.trans hc)]; exact hgcp
    · rw [hgK gfE gfE_lt_G0, glG_E]; exact zero_le
  · intro x hx hx1 hg
    rw [hgK c hc] at hg
    obtain ⟨e1, e2, e3, e4⟩ := hdec x hx hx1 hg
    show gnR c x = _ ∧ _
    rw [gnR_low hc, hlg x hx hx1 hg]
    refine ⟨e1, e2, e3, ?_⟩
    split_ifs with h
    · rw [gnR_low (hcp.trans hc)]; exact e4
    · push Not at h
      have hgcp' : gtc cp < x := by rw [← glG_low h]; exact hgcp.trans_lt hg
      rw [gnR_low gfE_lt_G0, glR_E]
      exact e4.trans ((by rw [glR_low h]; exact rdc_lt_eN hx cp hgcp' : glR cp x < eN x)).le
  · intro ρ τ δ h hg
    rw [hgK c hc] at hg ⊢
    have hρE := upsPt_inE h.ρU
    obtain ⟨e1, -, -, -⟩ := hdec ρ hρE h.ρ1 hg
    have hTρ : T ρ < lgG ρ := by
      have h1 : T ρ ≤ glR c ρ := by
        rw [e1]; exact (right_le_opow _ one_lt_omega0).trans le_add_self
      exact h1.trans_lt (glR_lt_G hρE h.ρ1 hc hg)
    have hP := glPkgG_of_ex h (C := ∅) hg (by simp) hTρ
      (Gj.GjEx.of_bases fun σ ρ' hB hgσ => hex σ ρ' hB hgσ)
    exact GhPkg.congr h hP (fun y hyE hy1 hgy => by rw [gnR_low hc]; exact (hlg y hyE hy1 hgy).symm) hg

/-- **The data `GmLD` exists at every limit code `c ∈ (ε_{Ω₁+1}, ε_{Γ_{Ω₁+1}+1})`.** -/
theorem gnLD : ∀ c, IsSuccLimit c → gfE < c → c < gnB → Nonempty (GmLD gnK gnR c) := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hl hEc hc
  rcases lt_or_ge c (gcG 0) with hcG | hcE
  · exact gnLD_low hl hEc hcG
  obtain ⟨hk, hd0, hdE, hr, hdec, hkc, -⟩ := gn_parts hcE hc
  have hkB : log (gcG 0) c < gnB := hkc.trans hc
  set k := log (gcG 0) c with hkdef
  set d := c / gcG 0 ^ k with hddef
  set r := c % gcG 0 ^ k with hrdef
  have hrc : r < c := mod_opow_log_lt_self (gcG 0) (gn_ne_of_le hcE)
  have hgc : gnG c = max (max (gnQ k) (glQ d)) (gnG r) := gnG_dec hcE hc
  have hRc : ∀ x, gnR c x = lgG x ^ gnR k x * glR d x + gnR r x := fun x => gnR_dec hcE hc x
  have hgK : ∀ b, gnK.gt b = gnG b := fun _ => rfl
  have hEk : gcG 0 ≤ gcG 0 ^ k := by
    calc gcG 0 = gcG 0 ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ gcG 0 ^ k := opow_le_opow_right gl_G0_E.pos (one_le_iff_ne_zero.2 hk)
  have hEG : gfE ≤ gcG 0 := gfE_lt_G0.le
  have hcp_ge : ∀ b, b ≠ 0 → gfE ≤ gcG 0 ^ k * b := fun b hb =>
    hEG.trans (hEk.trans (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hb)))
  have hcnfB : ∀ b t, b < gcG 0 → t < gcG 0 ^ k → gcG 0 ^ k * b + t < gnB := by
    intro b t hbE ht
    have hk1B : k + 1 < gnB := gnB_lim.add_one_lt hkB
    calc gcG 0 ^ k * b + t < gcG 0 ^ k * b + gcG 0 ^ k := (add_lt_add_iff_left _).2 ht
      _ = gcG 0 ^ k * (b + 1) := by rw [mul_add_one]
      _ ≤ gcG 0 ^ k * gcG 0 := mul_le_mul_left' (Order.add_one_le_of_lt hbE) _
      _ = gcG 0 ^ (k + 1) := by rw [opow_add, opow_one]
      _ < gnB := gnB_gt_pow hk1B
  have hRp : ∀ b t x, b ≠ 0 → b < gcG 0 → t < gcG 0 ^ k →
      gnR (gcG 0 ^ k * b + t) x = lgG x ^ gnR k x * glR b x + gnR t x :=
    fun b t x hb hbE ht => gnR_cnf hk hb hbE ht (hcnfB b t hbE ht) x
  have hGp : ∀ b t, b ≠ 0 → b < gcG 0 → t < gcG 0 ^ k →
      gnG (gcG 0 ^ k * b + t) = max (max (gnQ k) (glQ b)) (gnG t) :=
    fun b t hb hbE ht => gnG_cnf hk hb hbE ht (hcnfB b t hbE ht)
  have hk0 : (0 : Ordinal.{0}) < gcG 0 ^ k := opow_pos _ gl_G0_E.pos
  have hgkx : ∀ σ, InE σ → gnG c < σ → gnG k < σ := fun σ hσ h =>
    (gn_parts_g (omega0_lt_inE hσ) hcE hc h).1
  have hgdx : ∀ σ, InE σ → gnG c < σ → glG d < σ := fun σ hσ h =>
    (gn_parts_g (omega0_lt_inE hσ) hcE hc h).2.1
  have hKpos : ∀ x, InE x → x < Om1 → gnG c < x → 0 < gnR k x := fun x hx hx1 hg =>
    gnR_pos hx hx1 hk hkB (hgkx x hx hg)
  have hGpos : ∀ x, InE x → x < Om1 → 0 < lgG x := fun x hx hx1 => (lgG_facts hx hx1).2.2.2.1.pos
  have hcpG_E : gnG gfE = 0 := by rw [gnG_low gfE_lt_G0, glG_E]
  have hcpR_E : ∀ x, gnR gfE x = eN x := fun x => by rw [gnR_low gfE_lt_G0, glR_E]
  rcases eq_or_ne r 0 with hr0 | hr0
  · -- `r = 0`: `c = G^k·d`
    have hRc0 : ∀ x, gnR c x = lgG x ^ gnR k x * glR d x := fun x => by
      rw [hRc, hr0, gnR_zero, add_zero]
    have hgc0 : gnG c = max (gnQ k) (glQ d) := by rw [hgc, hr0, gnG_zero, max_eq_left zero_le]
    have hcd : c = gcG 0 ^ k * d := by rw [← hdec, hr0, add_zero]
    rcases zero_or_succ_or_isSuccLimit d with h0 | ⟨d', hsucc⟩ | hdl
    · exact absurd h0 hd0
    · -- `d = d' + 1`: the logend is `Γ_{x+1}·k(x)`
      rw [succ_eq_add_one] at hsucc
      have hd'E : d' < gcG 0 := (lt_add_one d').trans (by rw [hsucc]; exact hdE)
      have hRs : ∀ x, InE x → x < Om1 → gnR c x = lgG x ^ gnR k x * glR d' x + ω ^ (lgG x * gnR k x) :=
        fun x hx hx1 => by rw [hRc0, ← hsucc, glR_succ_all, mul_add_one, gn_Gpow hx hx1]
      have hlg : ∀ x, InE x → x < Om1 → lg (gnR c x) = lgG x * gnR k x := fun x hx hx1 => by
        rw [hRs x hx hx1]; exact Ge.lg_add_opow (gn_dvd hx hx1 le_rfl)
      refine ⟨{
        cp := if d' = 0 then gfE else gcG 0 ^ k * d' + 0
        lp := (fun x => lgG x ^ gnR k x * glR d' x)
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
        · rw [hcpG_E]; exact zero_le
        · rw [hGp d' 0 h0 hd'E hk0, gnG_zero, max_eq_left zero_le, hgc0, ← hsucc]
          exact max_le_max le_rfl (mq_glQ_le_succ d')
      · intro x hx hx1 hgx
        refine ⟨by rw [hlg x hx hx1]; exact hRs x hx hx1, by rw [hlg x hx hx1]; exact gn_dvd hx hx1 le_rfl,
          by rw [hlg x hx hx1]; exact (mul_pos (hGpos x hx hx1) (hKpos x hx hx1 hgx)).ne', ?_⟩
        split_ifs with h0
        · rw [h0, glR_zero, mul_zero]; exact zero_le
        · rw [hRp d' 0 x h0 hd'E hk0, gnR_zero, add_zero]
      · intro ρ τ δ h hg
        refine GhPkg.congr h (gn_pkg_Gk h hg hk hkB (fun σ hσ hgσ => hgkx σ hσ hgσ)) (fun y hyE hy1 _ => ?_) hg
        rw [hlg y hyE hy1]
    · -- `d` a limit: the logend is `Γ_{x+1}·k(x) + logend(d(x))`
      obtain ⟨cpd, lpd, T, hcpd, hgcpd, hdecd, hexd⟩ := gl_ld d hdl hdE
      have hdω : ω ≤ d := Ordinal.le_of_dvd hd0 ((isSuccLimit_iff_omega0_dvd.1 hdl).2)
      have hQd : glQ d = glG d := mq_glQ_inf hdω
      have hgd : ∀ x, gnG c < x → glG d < x := fun x h => by
        rw [hgc0, hQd] at h; exact (le_max_right _ _).trans_lt h
      have hcpdE : cpd < gcG 0 := hcpd.trans hdE
      have hdec2 : ∀ x, InE x → x < Om1 → gnG c < x →
          gnR c x = lgG x ^ gnR k x * lpd x + ω ^ (lgG x * gnR k x + T x) ∧
            ω ^ (lgG x * gnR k x + T x) ∣ lgG x ^ gnR k x * lpd x ∧
            lg (gnR c x) = lgG x * gnR k x + T x := by
        intro x hx hx1 hgx
        obtain ⟨e1, e2, -, -⟩ := hdecd x hx hx1 (hgd x hgx)
        have h1 : gnR c x = lgG x ^ gnR k x * lpd x + ω ^ (lgG x * gnR k x + T x) := by
          rw [hRc0, e1, mul_add, gn_Gpow hx hx1, ← opow_add]
        have h2 : ω ^ (lgG x * gnR k x + T x) ∣ lgG x ^ gnR k x * lpd x := by
          obtain ⟨m, hm⟩ := e2
          exact ⟨m, by rw [hm, ← mul_assoc, gn_Gpow hx hx1, ← opow_add]⟩
        exact ⟨h1, h2, by rw [h1]; exact Ge.lg_add_opow h2⟩
      refine ⟨{
        cp := if cpd = 0 then gfE else gcG 0 ^ k * cpd + 0
        lp := (fun x => lgG x ^ gnR k x * lpd x)
        cp_ge := ?_
        cp_lt := ?_
        cp_g := ?_
        dec := ?_
        pkg := ?_ }⟩
      all_goals try simp only [hgK]
      · split_ifs with h0
        · exact le_rfl
        · rw [add_zero]; exact hcp_ge cpd h0
      · split_ifs with h0
        · exact hEc
        · rw [hcd, add_zero]
          exact (mul_lt_mul_iff_right₀ hk0).2 hcpd
      · split_ifs with h0
        · rw [hcpG_E]; exact zero_le
        · rw [hGp cpd 0 h0 hcpdE hk0, gnG_zero, max_eq_left zero_le, hgc0, hQd]
          exact max_le_max le_rfl ((glQ_le cpd).trans hgcpd)
      · intro x hx hx1 hgx
        obtain ⟨h1, h2, h3⟩ := hdec2 x hx hx1 hgx
        obtain ⟨-, -, -, e4⟩ := hdecd x hx hx1 (hgd x hgx)
        refine ⟨by rw [h3]; exact h1, by rw [h3]; exact h2, by rw [h3]; exact (add_pos_of_pos_of_nonneg
          (mul_pos (hGpos x hx hx1) (hKpos x hx hx1 hgx)) zero_le).ne', ?_⟩
        split_ifs with h0
        · rw [h0, glR_zero] at e4
          rw [le_zero_iff.1 e4, mul_zero]; exact zero_le
        · rw [hRp cpd 0 x h0 hcpdE hk0, gnR_zero, add_zero]
          exact mul_le_mul_left' e4 _
      · intro ρ τ δ h hg
        have hρE := upsPt_inE h.ρU
        obtain ⟨e1, -, -, -⟩ := hdecd ρ hρE h.ρ1 (hgd ρ hg)
        have hTρ : T ρ < lgG ρ := by
          have h1 : T ρ ≤ glR d ρ := by
            rw [e1]; exact (right_le_opow _ one_lt_omega0).trans le_add_self
          exact h1.trans_lt (glR_lt_G hρE h.ρ1 hdE (hgd ρ hg))
        refine GhPkg.congr h (gn_pkg_Gkt h hg hk hkB (fun σ hσ hgσ => hgkx σ hσ hgσ) hTρ
          (fun σ ρ' hB hgσ => hexd σ ρ' hB (hgdx σ hB.1 hgσ))) (fun y hyE hy1 hgy => ?_) hg
        rw [(hdec2 y hyE hy1 hgy).2.2]
  · -- `r ≠ 0`: `r` a limit
    have hrl : IsSuccLimit r := by
      rcases zero_or_succ_or_isSuccLimit r with h0 | ⟨r', hsucc⟩ | hrl
      · exact absurd h0 hr0
      · exfalso
        rw [succ_eq_add_one] at hsucc
        have e : c = succ (gcG 0 ^ k * d + r') := by rw [← hdec, ← hsucc, ← add_assoc, succ_eq_add_one]
        rw [e] at hl
        exact Order.not_isSuccLimit_succ _ hl
      · exact hrl
    have hgr : ∀ x, gnG c < x → gnG r < x := fun x h => (le_max_right _ _).trans_lt (hgc ▸ h)
    have hrB : r < gnB := hrc.trans hc
    -- the logend of `r(x)` lies below `Γ_{x+1}·k(x)`
    have hlgk : ∀ x, InE x → x < Om1 → gnG c < x → lg (gnR r x) ≤ lgG x * gnR k x := by
      intro x hx hx1 hgx
      have hb := gnR_bound hx hx1 hrB (hgr x hgx) hk hkB (hgkx x hx hgx) hr
      rw [gn_Gpow hx hx1] at hb
      have h0 : gnR r x ≠ 0 := (gnR_pos hx hx1 hr0 hrB (hgr x hgx)).ne'
      have h1 : ω ^ lg (gnR r x) ≤ gnR r x := Ordinal.le_of_dvd h0 (lg_dvd h0)
      exact ((opow_lt_opow_iff_right one_lt_omega0).1 (h1.trans_lt hb)).le
    rcases lt_or_ge r (gcG 0) with hrE | hrE
    · -- `r` a limit below `G`
      obtain ⟨r', lpr, T, hr'r, hgr', hdecr, hexr⟩ := gl_ld r hrl hrE
      have hr'E : r' < gcG 0 := hr'r.trans hrE
      have hr'k : r' < gcG 0 ^ k := hr'E.trans_le hEk
      have hga : ∀ x, gnG c < x → glG r < x := fun x h => by rw [← gnG_low hrE]; exact hgr x h
      have hdec2 : ∀ x, InE x → x < Om1 → gnG c < x →
          gnR c x = (lgG x ^ gnR k x * glR d x + lpr x) + ω ^ T x ∧
            ω ^ T x ∣ lgG x ^ gnR k x * glR d x + lpr x ∧ lg (gnR c x) = T x ∧ T x ≠ 0 := by
        intro x hx hx1 hgx
        obtain ⟨e1, e2, e3, -⟩ := hdecr x hx hx1 (hga x hgx)
        have hlgr : lg (gnR r x) = T x := by rw [gnR_low hrE, e1]; exact Ge.lg_add_opow e2
        have hle : T x ≤ lgG x * gnR k x := by rw [← hlgr]; exact hlgk x hx hx1 hgx
        have hdv : ω ^ T x ∣ lgG x ^ gnR k x * glR d x + lpr x := Ge.dvd_add' (gn_dvd hx hx1 hle) e2
        have hsum : gnR c x = (lgG x ^ gnR k x * glR d x + lpr x) + ω ^ T x := by
          rw [hRc, gnR_low hrE, add_assoc, ← e1]
        exact ⟨hsum, hdv, by rw [hsum]; exact Ge.lg_add_opow hdv, e3⟩
      refine ⟨{
        cp := gcG 0 ^ k * d + r'
        lp := (fun x => lgG x ^ gnR k x * glR d x + lpr x)
        cp_ge := (hcp_ge d hd0).trans le_self_add
        cp_lt := ?_
        cp_g := ?_
        dec := ?_
        pkg := ?_ }⟩
      all_goals try simp only [hgK]
      · rw [← hdec]; exact (add_lt_add_iff_left _).2 hr'r
      · rw [hGp d r' hd0 hdE hr'k, gnG_low hr'E, hgc, gnG_low hrE]; exact max_le_max le_rfl hgr'
      · intro x hx hx1 hgx
        obtain ⟨h1, h2, h3, h4⟩ := hdec2 x hx hx1 hgx
        obtain ⟨-, -, -, e4⟩ := hdecr x hx hx1 (hga x hgx)
        exact ⟨by rw [h3]; exact h1, by rw [h3]; exact h2, by rw [h3]; exact h4,
          by rw [hRp d r' x hd0 hdE hr'k, gnR_low hr'E]; exact add_le_add le_rfl e4⟩
      · intro ρ τ δ h hg
        have hρE := upsPt_inE h.ρU
        have hgρ := hga ρ hg
        obtain ⟨e1, -, -, -⟩ := hdecr ρ hρE h.ρ1 hgρ
        have hTρ : T ρ < lgG ρ := by
          have h1 : T ρ ≤ glR r ρ := by
            rw [e1]; exact (right_le_opow _ one_lt_omega0).trans le_add_self
          exact h1.trans_lt (glR_lt_G hρE h.ρ1 hrE hgρ)
        have hP := glPkgG_of_ex h (C := ∅) hg (by simp) hTρ
          (Gj.GjEx.of_bases fun σ ρ' hB hgσ => hexr σ ρ' hB (hga σ hgσ))
        exact GhPkg.congr h hP (fun y hyE hy1 hgy => (hdec2 y hyE hy1 hgy).2.2.1.symm) hg
    rcases hrE.lt_or_eq with hEr | hEr
    · -- `r > G` a limit: the last term of `r`
      obtain ⟨D⟩ := IH r hrc hrl (gfE_lt_G0.trans hEr) hrB
      have hDk : D.cp < gcG 0 ^ k := D.cp_lt.trans hr
      have hlgc : ∀ x, InE x → x < Om1 → gnG c < x → lg (gnR c x) = lg (gnR r x) ∧
          ω ^ lg (gnR r x) ∣ lgG x ^ gnR k x * glR d x + D.lp x ∧
          gnR c x = (lgG x ^ gnR k x * glR d x + D.lp x) + ω ^ lg (gnR r x) := by
        intro x hx hx1 hgx
        obtain ⟨e1, e2, -, -⟩ := D.dec x hx hx1 (hgr x hgx)
        have hdv : ω ^ lg (gnR r x) ∣ lgG x ^ gnR k x * glR d x + D.lp x :=
          Ge.dvd_add' (gn_dvd hx hx1 (hlgk x hx hx1 hgx)) e2
        have hsum : gnR c x = (lgG x ^ gnR k x * glR d x + D.lp x) + ω ^ lg (gnR r x) := by
          rw [hRc, add_assoc, ← e1]
        exact ⟨by rw [hsum]; exact Ge.lg_add_opow hdv, hdv, hsum⟩
      refine ⟨{
        cp := gcG 0 ^ k * d + D.cp
        lp := (fun x => lgG x ^ gnR k x * glR d x + D.lp x)
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
    · -- `r = G`: the logend is `Γ_{x+1}`
      have hRE : ∀ x, InE x → x < Om1 → gnR c x = lgG x ^ gnR k x * glR d x + ω ^ lgG x := fun x hx hx1 => by
        rw [hRc, ← hEr, gnR_G, (lgG_facts hx hx1).2.2.2.1]
      have hlg : ∀ x, InE x → x < Om1 → gnG c < x → lg (gnR c x) = lgG x := fun x hx hx1 hg => by
        rw [hRE x hx hx1]
        exact Ge.lg_add_opow (gn_dvd hx hx1 (gn_one_le_k (hKpos x hx hx1 hg).ne'))
      refine ⟨{
        cp := gcG 0 ^ k * d + 0
        lp := (fun x => lgG x ^ gnR k x * glR d x)
        cp_ge := by rw [add_zero]; exact hcp_ge d hd0
        cp_lt := ?_
        cp_g := ?_
        dec := ?_
        pkg := ?_ }⟩
      all_goals try simp only [hgK]
      · rw [← hdec, ← hEr]; exact (add_lt_add_iff_left _).2 gl_G0_E.pos
      · rw [hGp d 0 hd0 hdE hk0, hgc, gnG_zero, ← hEr, gnG_G]
      · intro x hx hx1 hg
        refine ⟨by rw [hlg x hx hx1 hg]; exact hRE x hx hx1,
          by rw [hlg x hx hx1 hg]; exact gn_dvd hx hx1 (gn_one_le_k (hKpos x hx hx1 hg).ne'),
          by rw [hlg x hx hx1 hg]; exact (hGpos x hx hx1).ne', ?_⟩
        rw [hRp d 0 x hd0 hdE hk0, gnR_zero, add_zero]
      · intro ρ τ δ h hg
        exact GhPkg.congr h (GhPkg.of_img (LgK.lgTopPkg h)) (fun y hyE hy1 hgy => (hlg y hyE hy1 hgy).symm) hg

end Googology.Trans.PoR.InaccPsi.R2.Gn

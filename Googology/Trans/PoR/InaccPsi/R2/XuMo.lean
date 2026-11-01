import Googology.Trans.PoR.InaccPsi.R2.XuR1

/-!
# XuMo: CODES BELOW `Γ(1)`: the reading is strictly increasing

One well-founded induction proves, at every `ε`-number `x < Ω₁` and for the codes with gates below `x`, both

* `XuMo x c`: the codes below `c` read below `c(x)`, and
* `XuTop x c`: a code `c ≥ t₀` reads below the `ε`-number after the reading of its bracket's `ε`-number.

Below `t₀` it is `Wt.wtD.mono`.  The new step is the comparison of two `ε`-number codes `e' < e` in `[t₀, Γ(1))` of
ANY levels (`xu_eps_lt`): the code side gives `η' < η` (`α' = α`), `η' < e` (`α' < α`) or `e' ≤ η` (`α' > α`)
(`R2.XuVb`, the shifted count at the level `G` included), the reading side the same three criteria for
`ϑˣ(Ω₁·α'(x) + η'(x))` against `ϑˣ(Ω₁·α(x) + η(x))` ([W07a] Lemma 3.30, `R2.GlAt`, every level below `Γ_{x+2}`).
The codes below `t₀` read below `ε_{Γ_{x+1}+1}` (`Go.GoD.R_lt_b`), and every `ε`-number code `e ≥ t₀` reads at least
`ε_{Γ_{x+1}+1}` (`xu_eps_ge`: its level or its index is at least `G`).

* `XuMo`, `XuTop`, `xu_At_eq`, `xu_eps_read`, `xu_eps_ge`, `xu_eps_lt` (**`ε`-number codes of any levels**),
  `xu_below_eps`, `xu_bound_of`, `xu_mono_top` (**the induction**), `xuR_mono`, `xuR_top`.

No new axiom.  New definitions: `XuMo`, `XuTop`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xu

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi
  Googology.Notation.InaccPsi.InaccSeq Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Wt Googology.Trans.PoR.InaccPsi.R2.Gk
  Googology.Trans.PoR.InaccPsi.R2.Gh Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gm
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Hi

theorem xu_At_eq {c : Ordinal.{0}} (h1 : Wj.wjT 0 ≤ c) (h2 : c < gcG 1) (x : Ordinal.{0}) :
    xuR (guE c) x = glA (xuR (xuK (guE c)) x) (xuR (xuI (guE c)) x) x :=
  xuR_base (guE_E c) (xu_E_ge h1) (xu_E_lt h1 h2) x

/-- The readings of the codes below `j` are below the reading of `j`. -/
def XuMo (x j : Ordinal.{0}) : Prop := ∀ b, b < j → xuG j < x → xuG b < x → xuR b x < xuR j x

/-- A code `c ≥ t₀` reads below the `ε`-number after the reading of its bracket's `ε`-number. -/
def XuTop (x c : Ordinal.{0}) : Prop := Wj.wjT 0 ≤ c → xuG c < x → xuR c x < eN (xuR (guE c) x)

section Mono

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- The reading of an `ε`-number code `e ≥ t₀` is the atom. -/
theorem xu_eps_read {e : Ordinal.{0}} (he : InE e) (ht : Wj.wjT 0 ≤ e) (heB : e < gcG 1) (hg : xuG e < x) :
    xuR e x = glA (xuR (xuK e) x) (xuR (xuI e) x) x ∧ 1 ≤ xuK e ∧ xuK e < e ∧ xuI e < e ∧ xuG (xuK e) < x ∧
      xuG (xuI e) < x ∧ 1 ≤ xuR (xuK e) x ∧ xuR (xuK e) x ∈ Tset x ∧ xuR (xuK e) x < Om1 ∧
      xuR (xuI e) x ∈ Tset x ∧ xuR (xuI e) x < Om1 ∧ InE (xuR e x) ∧ eN x ≤ xuR e x ∧
      xuR (xuK e) x < xuR e x ∧ xuR (xuI e) x < xuR e x := by
  have hωx := omega0_lt_inE hx
  obtain ⟨hk1, hke, hηe, -⟩ := xuData_spec he (xu_G_lt_of ht) heB
  rw [xuG_base he ht heB] at hg
  have hgk : xuG (xuK e) < x := xuG_of_Q hωx ((xuQE_le_K e).trans_lt hg)
  have hgη : xuG (xuI e) < x := xuG_of_Q hωx ((xuQE_le_I e).trans_lt hg)
  have hk0 : xuK e ≠ 0 := (lt_of_lt_of_le zero_lt_one hk1).ne'
  have hkR := xuR_pos' hx hx1 hk0 (hke.trans heB) hgk
  have hkG := xuR_lt1 hx hx1 (hke.trans heB) hgk
  have hηG := xuR_lt1 hx hx1 (hηe.trans heB) hgη
  obtain ⟨a1, -, a3, a4, -, a6, -, -, hkT, hk1', hT, h1⟩ := xuA_facts hx hx1 hkR hkG hηG
  rw [xuR_base he ht heB]
  exact ⟨rfl, hk1, hke, hηe, hgk, hgη, hkR, hkT, hk1', hT, h1, a1, a6, a4, a3⟩

/-- **Every `ε`-number code `e ≥ t₀` reads at least `ε_{Γ_{x+1}+1}`**, given the order at its level and index. -/
theorem xu_eps_ge {e : Ordinal.{0}} (he : InE e) (ht : Wj.wjT 0 ≤ e) (heB : e < gcG 1) (hg : xuG e < x)
    (hMα : XuMo x (xuK e)) (hMη : XuMo x (xuI e)) : eN (lgG x) ≤ xuR e x := by
  obtain ⟨r, hk1, hke, hηe, hgk, hgη, -, -, -, -, -, hE, -, hKe, hIe⟩ := xu_eps_read hx hx1 he ht heB hg
  have hG0 : (0 : Ordinal.{0}) < x := hx.pos
  refine eN_le ?_ hE
  rcases lt_trichotomy (xuK e) (gcG 0) with hk | hk | hk
  · -- the level is below `G`: the index is at least `G`
    have hIG : gcG 0 ≤ xuI e := by
      by_contra hc
      push Not at hc
      have h := (xuData_spec he (xu_G_lt_of ht) heB).2.2.2
      rw [xuPsi_ne hk.ne] at h
      have := glPsi_lt_G hk hc
      rw [h] at this
      exact absurd (xu_G_lt_of ht) (not_lt.2 this.le)
    rcases hIG.lt_or_eq with hlt | heq
    · have := hMη _ hlt hgη (by rw [xuG_G]; exact hG0)
      rw [xuR_G] at this
      exact this.trans hIe
    · rw [← xuR_G x, heq]; exact hIe
  · rw [← xuR_G x, ← hk]; exact hKe
  · have := hMα _ hk hgk (by rw [xuG_G]; exact hG0)
    rw [xuR_G] at this
    exact this.trans hKe

/-- **The codes below `t₀` read below `ε_{Γ_{x+1}+1}`.** -/
theorem xu_low_lt {b : Ordinal.{0}} (hb : b < Wj.wjT 0) (hg : xuG b < x) : xuR b x < eN (lgG x) := by
  rw [xuG_low hb] at hg
  rw [xuR_low hb]
  exact wtD.R_lt_b x hx hx1 b (xu_lt_wtB hb) hg

/-- **Two `ε`-number codes `≥ t₀` of any levels**: `e' < e` gives `e'(x) < e(x)`, given the order at the levels
and at the index `η` of `e`, and `η'(x) < e(x)` for the index `η'` of `e'`. -/
theorem xu_eps_lt {e' e : Ordinal.{0}} (he' : InE e') (ht' : Wj.wjT 0 ≤ e') (he : InE e)
    (heB : e < gcG 1) (hlt : e' < e) (hg' : xuG e' < x) (hg : xuG e < x) (hMη : XuMo x (xuI e))
    (hMα : XuMo x (xuK e)) (hMα' : XuMo x (xuK e'))
    (hη' : xuR (xuI e') x < xuR e x) : xuR e' x < xuR e x := by
  have ht : Wj.wjT 0 ≤ e := ht'.trans hlt.le
  have he'B : e' < gcG 1 := hlt.trans heB
  obtain ⟨r', hk'1, -, -, hgk', hgη', hkR', hkT', hk1', hT', h1', -, -⟩ := xu_eps_read hx hx1 he' ht' he'B hg'
  obtain ⟨r, hk1, -, -, hgk, hgη, hkR, hkT, hk1x, hT, h1, -, -⟩ := xu_eps_read hx hx1 he ht heB hg
  have ce' := (xuData_spec he' (xu_G_lt_of ht') he'B).2.2.2
  have ce := (xuData_spec he (xu_G_lt_of ht) heB).2.2.2
  have hk'G : xuK e' < gcG 1 := (xuData_spec he' (xu_G_lt_of ht') he'B).2.1.trans he'B
  rw [r] at hη' ⊢
  rw [r']
  rcases lt_trichotomy (xuK e') (xuK e) with hk | hk | hk
  · have hR : xuR (xuK e') x < xuR (xuK e) x := hMα _ hk hgk hgk'
    exact (glA_lev hx hx1 hkR' hR hkT hk1x hT h1 hT' h1').2 hη'
  · have hηη : xuI e' < xuI e := by
      have h := hlt
      rw [← ce', ← ce, hk] at h
      exact xuPsi_lt_iff.1 h
    rw [hk]
    exact glA_lt_of hx hx1 hkR hkT hk1x hT' hT h1 (hMη _ hηη hgη hgη')
  · have hR : xuR (xuK e) x < xuR (xuK e') x := hMα' _ hk hgk' hgk
    have hle : e' ≤ xuI e := by
      have h := hlt
      rw [← ce', ← ce] at h
      have := (xuPsi_lt_lev' hk hk'1 hk'G).1 h
      rwa [ce'] at this
    refine (glA_lev' hx hx1 hkR hR hkT' hk1' hT h1 hT' h1').2 ?_
    rw [← r']
    rcases hle.lt_or_eq with h2 | h2
    · exact (hMη _ h2 hgη hg').le
    · rw [h2]

/-- **The codes below an `ε`-number code `e ≥ t₀` read below `e(x)`**, given the order and the top bound below
`e`. -/
theorem xu_below_eps {e : Ordinal.{0}} (he : InE e) (ht : Wj.wjT 0 ≤ e) (heB : e < gcG 1)
    (IH : ∀ j, j < e → XuMo x j ∧ XuTop x j) : XuMo x e := by
  have hωx := omega0_lt_inE hx
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IHb =>
  intro hbe hge hgb
  obtain ⟨-, -, hke, hηe, -, -, -, -, -, -, -, hRE, -⟩ := xu_eps_read hx hx1 he ht heB hge
  rcases lt_or_ge b (Wj.wjT 0) with hbt | hbt
  · exact (xu_low_lt hx hx1 hbt hgb).trans_le
      (xu_eps_ge hx hx1 he ht heB hge (IH _ hke).1 (IH _ hηe).1)
  have hbB : b < gcG 1 := hbe.trans heB
  have h1 : xuR b x < eN (xuR (guE b) x) := (IH b hbe).2 hbt hgb
  have hEb : guE b ≤ b := gl_E_le (xu_gfE_le hbt)
  have hgEb : xuG (guE b) < x := xu_E_g hbt hbB hgb
  have hηb : xuI (guE b) < b := xu_idx_lt hbt hbB
  have hgηb : xuG (xuI (guE b)) < x := (xu_parts_g hωx hbt hbB hgb).1
  have hkb : xuK (guE b) < b := xu_lev_lt hbt hbB
  have h2 : xuR (guE b) x < xuR e x :=
    xu_eps_lt hx hx1 (guE_E b) (xu_E_ge hbt) he heB (hEb.trans_lt hbe) hgEb hge
      (IH _ hηe).1 (IH _ hke).1 (IH _ (hkb.trans hbe)).1 (IHb _ hηb (hηb.trans hbe) hge hgηb)
  exact h1.trans_le (eN_le h2 hRE)

/-- **`c < e^κ ⇒ c(x) < e(x)^{κ(x)}`** (`e ≥ t₀` an `ε`-number code, `c < ε_{e+1}`). -/
theorem xu_bound_of {N e : Ordinal.{0}} (hM : ∀ j, j < N → XuMo x j) (hT : ∀ j, j < N → XuTop x j)
    (he : InE e) (ht : Wj.wjT 0 ≤ e) (heB : e < gcG 1) (hge : xuG e < x) (hMe : XuMo x e) :
    ∀ c, c < N → c < gcG 1 → xuG c < x → c < eN e → ∀ κ, κ ≠ 0 → κ < N → κ < gcG 1 → xuG κ < x → c < e ^ κ →
    xuR c x < xuR e x ^ xuR κ x := by
  have hωx := omega0_lt_inE hx
  have hOe : Om1 < e := xu_Om1_lt_t0.trans_le ht
  set B := xuR e x with hBdef
  have hBE : InE B := (xu_eps_read hx hx1 he ht heB hge).2.2.2.2.2.2.2.2.2.2.2.1
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hcN hcB hg hcn κ hκ hκN hκB hgκ hcκ
  have hBκ : B ≤ B ^ xuR κ x := by
    calc B = B ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ B ^ xuR κ x := opow_le_opow_right hBE.pos (xuR_pos' hx hx1 hκ hκB hgκ)
  rcases lt_or_ge c e with hcE | hcE
  · exact (hMe c hcE hge hg).trans_le hBκ
  have hct : Wj.wjT 0 ≤ c := ht.trans hcE
  have hgfc := xu_gfE_le hct
  have hEc : guE c = e := gl_E_of_bracket he hOe hcE hcn
  obtain ⟨hj, -, hdE, hr, -, hjc, hrc, hdc⟩ := gl_parts hgfc
  obtain ⟨-, g0, g1, g2⟩ := xu_parts_g hωx hct hcB hg
  rw [hEc] at hj hdE hr hjc hrc hdc g0 g1 g2
  have hjk : log e c < κ := (lt_opow_iff_log_lt (Lu.lu_one_lt_E he) (he.pos.trans_le hcE).ne').1 hcκ
  have hrr := IH _ hrc (hrc.trans hcN) (hrc.trans hcB) g2 ((hrc.trans hcn)) _ hj (hjc.trans hcN)
    (hjc.trans hcB) g0 hr
  have hjx : xuR (log e c) x < xuR κ x := hM κ hκN _ hjk hgκ g0
  have hdB : xuR (c / e ^ log e c) x < B := hMe _ hdE hge g1
  rw [xuR_dec hct hcB, ← xu_At_eq hct hcB, hEc]
  calc B ^ xuR (log e c) x * xuR (c / e ^ log e c) x + xuR (c % e ^ log e c) x
      < B ^ xuR (log e c) x * xuR (c / e ^ log e c) x + B ^ xuR (log e c) x :=
        (add_lt_add_iff_left _).2 hrr
    _ = B ^ xuR (log e c) x * (xuR (c / e ^ log e c) x + 1) := by rw [mul_add_one]
    _ ≤ B ^ xuR (log e c) x * B := mul_le_mul_right (add_one_le_of_lt hdB) _
    _ = B ^ (xuR (log e c) x + 1) := by rw [opow_add, opow_one]
    _ ≤ B ^ xuR κ x := opow_le_opow_right hBE.pos (add_one_le_of_lt hjx)

/-- **THE INDUCTION**: the order and the top bound at every code below `Γ(1)`. -/
theorem xu_mono_top : ∀ c, c < gcG 1 → XuMo x c ∧ XuTop x c := by
  have hωx := omega0_lt_inE hx
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hcB
  have hM : ∀ j, j < c → XuMo x j := fun j hj => (IH j hj (hj.trans hcB)).1
  have hT : ∀ j, j < c → XuTop x j := fun j hj => (IH j hj (hj.trans hcB)).2
  have hIH : ∀ j, j < c → XuMo x j ∧ XuTop x j := fun j hj => IH j hj (hj.trans hcB)
  -- the top bound at `c`
  have hTc : XuTop x c := by
    intro hct hg
    have hgfc := xu_gfE_le hct
    by_cases hcE : InE c
    · rw [gl_eps_self hcE hgfc]; exact lt_eN _
    have hEc := gl_E_lt_self hgfc hcE
    set e := guE c with hedef
    have he : InE e := guE_E c
    have ht : Wj.wjT 0 ≤ e := xu_E_ge hct
    have hOe : Om1 < e := xu_Om1_lt_t0.trans_le ht
    have heB : e < gcG 1 := hEc.trans hcB
    have hge : xuG e < x := xu_E_g hct hcB hg
    have hMe := hM e hEc
    obtain ⟨hk, -, hdE, hr, -, hkc, hrc, hdc⟩ := gl_parts hgfc
    obtain ⟨-, g0, g1, g2⟩ := xu_parts_g hωx hct hcB hg
    set k := log e c with hkdef
    set B := xuR e x with hBdef
    have hBE : InE B := (xu_eps_read hx hx1 he ht heB hge).2.2.2.2.2.2.2.2.2.2.2.1
    have hcN' : c < eN e := gl_lt_eN hgfc
    have hrr : xuR (c % e ^ k) x < B ^ xuR k x :=
      xu_bound_of hx hx1 hM hT he ht heB hge hMe _ hrc (hrc.trans hcB) g2 (hrc.trans hcN') k hk hkc
        (hkc.trans hcB) g0 hr
    have hdB : xuR (c / e ^ k) x < B := hMe _ hdE hge g1
    have hkB : xuR k x < eN B := by
      rcases lt_or_ge k e with hkE | hkE
      · exact (hMe _ hkE hge g0).trans (lt_eN B)
      · have hEk : guE k = e := gl_E_of_bracket he hOe hkE (hkc.trans hcN')
        have := hT k hkc (ht.trans hkE) g0
        rwa [hEk] at this
    have hlt : xuR c x < B ^ (xuR k x + 1) := by
      rw [xuR_dec hct hcB, ← xu_At_eq hct hcB]
      calc B ^ xuR k x * xuR (c / e ^ k) x + xuR (c % e ^ k) x
          < B ^ xuR k x * xuR (c / e ^ k) x + B ^ xuR k x := (add_lt_add_iff_left _).2 hrr
        _ = B ^ xuR k x * (xuR (c / e ^ k) x + 1) := by rw [mul_add_one]
        _ ≤ B ^ xuR k x * B := mul_le_mul_right (add_one_le_of_lt hdB) _
        _ = B ^ (xuR k x + 1) := by rw [opow_add, opow_one]
    exact hlt.trans (gu_pow_lt_eN hBE ((ev_isSuccLimit_of_inE (eN_E B)).add_one_lt hkB))
  refine ⟨?_, hTc⟩
  rcases lt_or_ge c (Wj.wjT 0) with hct | hct
  · intro b hbc hgc hgb
    have hbt := hbc.trans hct
    rw [xuG_low hct] at hgc
    rw [xuG_low hbt] at hgb
    rw [xuR_low hct, xuR_low hbt]
    exact wtD.mono x hx hx1 c (xu_lt_wtB hct) b hbc hgc hgb
  have hcE := xu_gfE_le hct
  by_cases hcI : InE c
  · exact xu_below_eps hx hx1 hcI hct hcB hIH
  intro b hbc hgc hgb
  have hEc := gl_E_lt_self hcE hcI
  set e := guE c with hedef
  have he : InE e := guE_E c
  have ht : Wj.wjT 0 ≤ e := xu_E_ge hct
  have hOe : Om1 < e := xu_Om1_lt_t0.trans_le ht
  have heB : e < gcG 1 := hEc.trans hcB
  have hge : xuG e < x := xu_E_g hct hcB hgc
  have hMe := hM e hEc
  obtain ⟨gcn, gck, gcd, gcr⟩ := xu_parts_g hωx hct hcB hgc
  have hlead := xu_lead hx hx1 hct hcB hgc
  rw [← xu_At_eq hct hcB] at hlead
  obtain ⟨-, -, hke, hηe, -, -, -, -, -, -, -, hRE, -⟩ := xu_eps_read hx hx1 he ht heB hge
  rcases lt_or_ge b (Wj.wjT 0) with hbt | hbt
  · exact ((xu_low_lt hx hx1 hbt hgb).trans_le
      (xu_eps_ge hx hx1 he ht heB hge (hM _ (hke.trans hEc)) (hM _ (hηe.trans hEc)))).trans_le hlead.2
  have hbE := xu_gfE_le hbt
  have hbB : b < gcG 1 := hbc.trans hcB
  obtain ⟨gbn, gbk, gbd, gbr⟩ := xu_parts_g hωx hbt hbB hgb
  have hee : guE b ≤ e := gl_E_mono hbE hbc.le
  rcases hee.lt_or_eq with hlt | heq
  · have h1 := hT b hbc hbt hgb
    have h2 : xuR (guE b) x < xuR e x := hMe _ hlt hge (xu_E_g hbt hbB hgb)
    exact (h1.trans_le (eN_le h2 hRE)).trans_le hlead.2
  -- the same bracket
  set B := xuR e x with hBdef
  have hBE : InE B := hRE
  have hE1 : (1 : Ordinal.{0}) < e := Lu.lu_one_lt_E he
  obtain ⟨hk, hd0, hdE, hr, hdec, hkc, hrc, hdc⟩ := gl_parts hcE
  obtain ⟨hk', hd0', hdE', hr', hdec', hkb, hrb, hdb⟩ := gl_parts hbE
  rw [heq] at hk' hd0' hdE' hr' hdec' hkb hrb hdb gbk gbd gbr
  have hcn : c < eN e := gl_lt_eN hcE
  have hbn : b < eN e := hbc.trans hcn
  have hkk : log e b ≤ log e c := log_mono_right _ hbc.le
  have hRb : xuR b x = B ^ xuR (log e b) x * xuR (b / e ^ log e b) x + xuR (b % e ^ log e b) x := by
    rw [xuR_dec hbt hbB, ← xu_At_eq hbt hbB, heq]
  have hRc : xuR c x = B ^ xuR (log e c) x * xuR (c / e ^ log e c) x + xuR (c % e ^ log e c) x := by
    rw [xuR_dec hct hcB, ← xu_At_eq hct hcB]
  have hpowc : B ^ xuR (log e c) x ≤ xuR c x := by
    refine le_trans ?_ hlead.1
    calc B ^ xuR (log e c) x = B ^ xuR (log e c) x * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_right (xuR_pos' hx hx1 hd0 (hdc.trans hcB) gcd) _
  rcases hkk.lt_or_eq with hlt | heq2
  · have hs1 : log e b + 1 ≤ log e c := add_one_le_of_lt hlt
    have hs1c : log e b + 1 < c := lt_of_le_of_lt hs1 hkc
    have hs1B : log e b + 1 < gcG 1 := hs1c.trans hcB
    have hgs : xuG (log e b + 1) < x := xuG_succ (ev_isSuccLimit_of_inE hx) _ hs1B gbk
    have hb1 : b < e ^ (log e b + 1) := (lt_opow_iff_log_lt hE1 (he.pos.trans_le (by
      rw [← heq]; exact gl_E_le hbE)).ne').2 (lt_add_one _)
    have hmono : xuR (log e b) x < xuR (log e c) x := hM _ hkc _ hlt gck gbk
    have hbd := xu_bound_of hx hx1 hM hT he ht heB hge hMe b hbc hbB hgb hbn _
      (lt_of_le_of_lt zero_le (lt_add_one _)).ne' hs1c hs1B hgs hb1
    rw [xuR_succ _ hs1B] at hbd
    exact (hbd.trans_le (opow_le_opow_right hBE.pos (add_one_le_of_lt hmono))).trans_le hpowc
  set k := log e c with hkdef
  rw [heq2] at hd0' hdE' hr' hdec' hRb gbd gbr hrb
  set d := c / e ^ k
  set r := c % e ^ k
  set d' := b / e ^ k
  set r' := b % e ^ k
  have hdd : d' ≤ d := by
    by_contra hlt
    push Not at hlt
    have : c < b := by
      calc c = e ^ k * d + r := hdec.symm
        _ < e ^ k * d + e ^ k := (add_lt_add_iff_left _).2 hr
        _ = e ^ k * (d + 1) := by rw [mul_add_one]
        _ ≤ e ^ k * d' := mul_le_mul_right (add_one_le_of_lt hlt) _
        _ ≤ b := by rw [← hdec']; exact le_self_add
    exact absurd hbc (not_lt.2 this.le)
  rw [hRb, hRc]
  rcases hdd.lt_or_eq with hd | hd
  · have hr'c : r' < c := hrb.trans hbc
    have hrb' := xu_bound_of hx hx1 hM hT he ht heB hge hMe r' hr'c (hr'c.trans hcB) gbr (hr'c.trans hcn) k hk
      hkc (hkc.trans hcB) gck hr'
    calc B ^ xuR k x * xuR d' x + xuR r' x < B ^ xuR k x * xuR d' x + B ^ xuR k x :=
          (add_lt_add_iff_left _).2 hrb'
      _ = B ^ xuR k x * (xuR d' x + 1) := by rw [mul_add_one]
      _ ≤ B ^ xuR k x * xuR d x := mul_le_mul_right (add_one_le_of_lt (hM _ hdc _ hd gcd gbd)) _
      _ ≤ _ := le_self_add
  · have hrr : r' < r := by
      have hb' : b = e ^ k * d + r' := by rw [← hd]; exact hdec'.symm
      have hc' : c = e ^ k * d + r := hdec.symm
      have h3 := hbc
      rw [hb', hc'] at h3
      exact (add_lt_add_iff_left _).1 h3
    rw [hd]
    exact (add_lt_add_iff_left _).2 (hM r hrc r' hrr gcr gbr)

theorem xuR_mono {b c : Ordinal.{0}} (hc : c < gcG 1) (hbc : b < c) (hgc : xuG c < x) (hgb : xuG b < x) :
    xuR b x < xuR c x := (xu_mono_top hx hx1 c hc).1 b hbc hgc hgb

theorem xuR_top {c : Ordinal.{0}} (hc : c < gcG 1) (ht : Wj.wjT 0 ≤ c) (hg : xuG c < x) :
    xuR c x < eN (xuR (guE c) x) := (xu_mono_top hx hx1 c hc).2 ht hg

theorem xuR_le_mono {b c : Ordinal.{0}} (hc : c < gcG 1) (hbc : b ≤ c) (hgc : xuG c < x) (hgb : xuG b < x) :
    xuR b x ≤ xuR c x := by
  rcases hbc.lt_or_eq with h | rfl
  · exact (xuR_mono hx hx1 hc h hgc hgb).le
  · exact le_rfl

end Mono

end Googology.Trans.PoR.InaccPsi.R2.Xu

import Googology.Trans.PoR.InaccPsi.R2.GlR1

/-!
# CODES BELOW `Γ_{Ω₁+1}`: the reading is strictly increasing

One well-founded induction proves, at every `ε`-number `x < Ω₁` and for the codes with gates below `x`, both

* `GlMo x c`: the codes below `c` read below `c(x)`, and
* `GlTop x c`: a code `c ≥ ε_{Ω₁+1}` reads below the `ε`-number after the reading of its bracket's `ε`-number.

The new step against round 82 is the comparison of two `ε`-number codes of ANY levels (`gl_eps_lt`): for
`e' = glPsi α' η' < e = glPsi α η` the code side gives `η' < η` (`α' = α`), `η' < e` (`α' < α`) or `e' ≤ η`
(`α' > α`) (`R2.GlVb`), and the reading side the same three criteria for `ϑˣ(Ω₁·α'(x) + η'(x))` against
`ϑˣ(Ω₁·α(x) + η(x))` ([W07a] Lemma 3.30, `R2.GlAt`; the levels compare by the order at the smaller codes `α, α'`).
The codes below an `ε`-number code `e` read below `e(x)` by an inner induction (`gl_below_eps`): the case `α' < α`
needs the reading of the index `η' < e'` below `e(x)`, which is the inner hypothesis.

* `gl_E_E`, `gl_E_max`, `gl_E_mono`, `gl_eps_self`, `gl_E_lt_self`, `gl_E_of_bracket`, `gl_At_eq`;
* `GlMo`, `GlTop`, `gl_eps_lt` (**`ε`-number codes of any levels**), `gl_below_eps`, `gl_bound_of`,
  `gl_mono_top` (**the induction**), `glR_mono`, `glR_top`.

No new axiom.  New definitions: `GlMo`, `GlTop`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gl

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu

open Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh Googology.Trans.PoR.InaccPsi.R2.Gi
  Googology.Trans.PoR.InaccPsi.R2.Gk
open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2

/-! ## The bracket's `ε`-number -/

theorem gl_eps_nf {e : Ordinal.{0}} (he : InE e) (hOe : Om1 < e) : guE e = e := by
  obtain ⟨h1, h2⟩ := gl_base_nf he
  have hE1 : (1 : Ordinal.{0}) < e := Lu.lu_one_lt_E he
  have h := (gl_cnf he hOe one_ne_zero one_ne_zero hE1 (by rw [opow_one]; exact he.pos) h2).1
  rwa [← h1] at h

theorem gl_E_E {c : Ordinal.{0}} (h1 : gfE ≤ c) : guE (guE c) = guE c := gl_eps_nf (guE_E c) (gl_Om1_lt_E h1)

/-- **`guE c` is the largest `ε`-number `≤ c`.** -/
theorem gl_E_max {e c : Ordinal.{0}} (he : InE e) (hOe : Om1 < e) (hec : e ≤ c) : e ≤ guE c := by
  have h1 : gfE ≤ c := (eN_le hOe he).trans hec
  obtain ⟨n, rfl⟩ := evA_surj gu_Om1_E he hOe.le
  have h2 := (gl_N_spec h1).2.2
  exact evA_le_iff.2 (Order.lt_add_one_iff.1 (evA_lt_iff.1 (lt_of_le_of_lt hec h2)))

theorem gl_E_mono {b c : Ordinal.{0}} (hb : gfE ≤ b) (hbc : b ≤ c) : guE b ≤ guE c :=
  gl_E_max (guE_E b) (gl_Om1_lt_E hb) ((gl_E_le hb).trans hbc)

theorem gl_eps_self {c : Ordinal.{0}} (hc : InE c) (h1 : gfE ≤ c) : guE c = c :=
  gl_eps_nf hc (Om1_lt_eW.trans_le h1)

theorem gl_E_lt_self {c : Ordinal.{0}} (h1 : gfE ≤ c) (hc : ¬ InE c) : guE c < c :=
  lt_of_le_of_ne (gl_E_le h1) (fun h => hc (h ▸ guE_E c))

/-- A code in the bracket `[e, ε_{e+1})` of an `ε`-number `e > Ω₁` has `guE = e`. -/
theorem gl_E_of_bracket {e c : Ordinal.{0}} (he : InE e) (hOe : Om1 < e) (hec : e ≤ c) (hcN : c < eN e) :
    guE c = e := by
  have h1 := gl_E_max he hOe hec
  have h2 : gfE ≤ c := (eN_le hOe he).trans hec
  refine le_antisymm ?_ h1
  by_contra hlt
  push Not at hlt
  exact absurd ((eN_le hlt (guE_E c)).trans (gl_E_le h2)) (not_le.2 hcN)

theorem gl_At_eq {c : Ordinal.{0}} (h1 : gfE ≤ c) (h2 : c < gcG 0) (x : Ordinal.{0}) :
    glR (guE c) x = glBA (glR (glK (guE c)) x) (glR (glI (guE c)) x) x :=
  glR_base (guE_E c) (gl_Om1_lt_E h1) ((gl_E_le h1).trans_lt h2) x

/-! ## The order -/

/-- The readings of the codes below `j` are below the reading of `j`. -/
def GlMo (x j : Ordinal.{0}) : Prop := ∀ b, b < j → glG j < x → glG b < x → glR b x < glR j x

/-- A code `c ≥ ε_{Ω₁+1}` reads below the `ε`-number after the reading of its bracket's `ε`-number. -/
def GlTop (x c : Ordinal.{0}) : Prop := gfE ≤ c → glG c < x → glR c x < eN (glR (guE c) x)

section Mono

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- The reading of an `ε`-number code is the atom. -/
theorem gl_eps_read {e : Ordinal.{0}} (he : InE e) (hOe : Om1 < e) (heB : e < gcG 0) (hg : glG e < x) :
    glR e x = glA (glR (glK e) x) (glR (glI e) x) x ∧ 1 ≤ glK e ∧ glK e < e ∧ glI e < e ∧ glG (glK e) < x ∧
      glG (glI e) < x ∧ 1 ≤ glR (glK e) x ∧ glR (glK e) x ∈ Tset x ∧ glR (glK e) x < Om1 ∧
      glR (glI e) x ∈ Tset x ∧ glR (glI e) x < Om1 ∧ InE (glR e x) ∧ eN x ≤ glR e x := by
  have hωx := omega0_lt_inE hx
  obtain ⟨hk1, hke, hηe, -⟩ := glData_spec he hOe heB
  rw [glG_base he hOe heB] at hg
  have hgk : glG (glK e) < x := glG_of_Q hωx ((glQE_le_K e).trans_lt hg)
  have hgη : glG (glI e) < x := glG_of_Q hωx ((glQE_le_I e).trans_lt hg)
  have hk0 : glK e ≠ 0 := (lt_of_lt_of_le zero_lt_one hk1).ne'
  have hkR := glR_pos' hx hx1 hk0 (hke.trans heB) hgk
  have hkG := glR_lt_G hx hx1 (hke.trans heB) hgk
  have hηG := glR_lt_G hx hx1 (hηe.trans heB) hgη
  obtain ⟨hkT, hk1'⟩ := gl_T_of_lt_G hx hx1 hkG
  obtain ⟨hT, h1⟩ := gl_T_of_lt_G hx hx1 hηG
  obtain ⟨e1, e2, -, -, -, -, e6, -⟩ := glBA_facts hx hx1 hkR hkG hηG
  rw [glR_base he hOe heB]
  exact ⟨e1, hk1, hke, hηe, hgk, hgη, hkR, hkT, hk1', hT, h1, e2, e6⟩

/-- **Two `ε`-number codes of any levels**: `e' < e` gives `e'(x) < e(x)`, given the order at the levels and at the
index `η` of `e`, and `η'(x) < e(x)` for the index `η'` of `e'`. -/
theorem gl_eps_lt {e' e : Ordinal.{0}} (he' : InE e') (hO' : Om1 < e') (he : InE e) (hO : Om1 < e)
    (heB : e < gcG 0) (hlt : e' < e) (hg' : glG e' < x) (hg : glG e < x) (hMη : GlMo x (glI e))
    (hMα : GlMo x (glK e)) (hMα' : GlMo x (glK e'))
    (hη' : glR (glI e') x < glR e x) : glR e' x < glR e x := by
  have he'B : e' < gcG 0 := hlt.trans heB
  obtain ⟨r', hk'1, -, -, hgk', hgη', hkR', hkT', hk1', hT', h1', -, -⟩ := gl_eps_read hx hx1 he' hO' he'B hg'
  obtain ⟨r, hk1, -, -, hgk, hgη, hkR, hkT, hk1x, hT, h1, -, -⟩ := gl_eps_read hx hx1 he hO heB hg
  have ce' := (glData_spec he' hO' he'B).2.2.2
  have ce := (glData_spec he hO heB).2.2.2
  have hkG : glK e < gcG 0 := (glData_spec he hO heB).2.1.trans heB
  have hk'G : glK e' < gcG 0 := (glData_spec he' hO' he'B).2.1.trans he'B
  rw [r] at hη' ⊢
  rw [r']
  rcases lt_trichotomy (glK e') (glK e) with hk | hk | hk
  · have hR : glR (glK e') x < glR (glK e) x := hMα _ hk hgk hgk'
    exact (glA_lev hx hx1 hkR' hR hkT hk1x hT h1 hT' h1').2 hη'
  · have hηη : glI e' < glI e := by
      have h := hlt
      rw [← ce', ← ce, hk] at h
      exact glPsi_lt_iff.1 h
    rw [hk]
    exact glA_lt_of hx hx1 hkR hkT hk1x hT' hT h1 (hMη _ hηη hgη hgη')
  · have hR : glR (glK e) x < glR (glK e') x := hMα' _ hk hgk' hgk
    have hle : e' ≤ glI e := by
      have h := hlt
      rw [← ce', ← ce] at h
      have := (glPsi_lt_lev' hk hk'1 hk'G).1 h
      rwa [ce'] at this
    refine (glA_lev' hx hx1 hkR hR hkT' hk1' hT h1 hT' h1').2 ?_
    rw [← r']
    rcases hle.lt_or_eq with h2 | h2
    · exact (hMη _ h2 hgη hg').le
    · rw [h2]

/-- **The codes below an `ε`-number code `e` read below `e(x)`**, given the order and the top bound below `e`. -/
theorem gl_below_eps {e : Ordinal.{0}} (he : InE e) (hO : Om1 < e) (heB : e < gcG 0)
    (IH : ∀ j, j < e → GlMo x j ∧ GlTop x j) : GlMo x e := by
  have hωx := omega0_lt_inE hx
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IHb =>
  intro hbe hge hgb
  obtain ⟨-, -, hke, hηe, -, -, -, -, -, -, -, hRE, heR⟩ := gl_eps_read hx hx1 he hO heB hge
  rcases lt_or_ge b gfE with hbE | hbE
  · rw [glG_low hbE] at hgb
    rw [glR_low hbE]
    exact (rdc_lt_eN hx b hgb).trans_le heR
  have hbB : b < gcG 0 := hbe.trans heB
  have h1 : glR b x < eN (glR (guE b) x) := (IH b hbe).2 hbE hgb
  have hEb : guE b ≤ b := gl_E_le hbE
  have hgEb : glG (guE b) < x := gl_E_g hbE hbB hgb
  have hηb : glI (guE b) < b := gl_idx_lt hbE hbB
  have hgηb : glG (glI (guE b)) < x := (gl_parts_g hωx hbE hbB hgb).1
  have hkb : glK (guE b) < b := gl_lev_lt hbE hbB
  have h2 : glR (guE b) x < glR e x :=
    gl_eps_lt hx hx1 (guE_E b) (gl_Om1_lt_E hbE) he hO heB (hEb.trans_lt hbe) hgEb hge
      (IH _ hηe).1 (IH _ hke).1 (IH _ (hkb.trans hbe)).1 (IHb _ hηb (hηb.trans hbe) hge hgηb)
  exact h1.trans_le (eN_le h2 hRE)

/-- **`c < e^κ ⇒ c(x) < e(x)^{κ(x)}`** (`e` an `ε`-number code, `c < ε_{e+1}`), once the order and the top bound
hold below a bound `N`, and the order at `e`. -/
theorem gl_bound_of {N e : Ordinal.{0}} (hM : ∀ j, j < N → GlMo x j) (hT : ∀ j, j < N → GlTop x j)
    (he : InE e) (hOe : Om1 < e) (heB : e < gcG 0) (hge : glG e < x) (hMe : GlMo x e) :
    ∀ c, c < N → c < gcG 0 → glG c < x → c < eN e → ∀ κ, κ ≠ 0 → κ < N → κ < gcG 0 → glG κ < x → c < e ^ κ →
    glR c x < glR e x ^ glR κ x := by
  have hωx := omega0_lt_inE hx
  set B := glR e x with hBdef
  have hBE : InE B := (gl_eps_read hx hx1 he hOe heB hge).2.2.2.2.2.2.2.2.2.2.2.1
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hcN hcB hg hcn κ hκ hκN hκB hgκ hcκ
  have hBκ : B ≤ B ^ glR κ x := by
    calc B = B ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ B ^ glR κ x := opow_le_opow_right hBE.pos (glR_pos' hx hx1 hκ hκB hgκ)
  rcases lt_or_ge c e with hcE | hcE
  · exact (hMe c hcE hge hg).trans_le hBκ
  have hgfc : gfE ≤ c := (eN_le hOe he).trans hcE
  have hEc : guE c = e := gl_E_of_bracket he hOe hcE hcn
  obtain ⟨hj, -, hdE, hr, -, hjc, hrc, hdc⟩ := gl_parts hgfc
  obtain ⟨-, g0, g1, g2⟩ := gl_parts_g hωx hgfc hcB hg
  rw [hEc] at hj hdE hr hjc hrc hdc g0 g1 g2
  have hjk : log e c < κ := (lt_opow_iff_log_lt (Lu.lu_one_lt_E he) (he.pos.trans_le hcE).ne').1 hcκ
  have hrr := IH _ hrc (hrc.trans hcN) (hrc.trans hcB) g2 ((hrc.trans hcn)) _ hj (hjc.trans hcN)
    (hjc.trans hcB) g0 hr
  have hjx : glR (log e c) x < glR κ x := hM κ hκN _ hjk hgκ g0
  have hdB : glR (c / e ^ log e c) x < B := hMe _ hdE hge g1
  rw [glR_dec hgfc hcB, ← gl_At_eq hgfc hcB, hEc]
  calc B ^ glR (log e c) x * glR (c / e ^ log e c) x + glR (c % e ^ log e c) x
      < B ^ glR (log e c) x * glR (c / e ^ log e c) x + B ^ glR (log e c) x :=
        (add_lt_add_iff_left _).2 hrr
    _ = B ^ glR (log e c) x * (glR (c / e ^ log e c) x + 1) := by rw [mul_add_one]
    _ ≤ B ^ glR (log e c) x * B := mul_le_mul_right (add_one_le_of_lt hdB) _
    _ = B ^ (glR (log e c) x + 1) := by rw [opow_add, opow_one]
    _ ≤ B ^ glR κ x := opow_le_opow_right hBE.pos (add_one_le_of_lt hjx)

/-- **THE INDUCTION**: the order and the top bound at every code below `Γ_{Ω₁+1}`. -/
theorem gl_mono_top : ∀ c, c < gcG 0 → GlMo x c ∧ GlTop x c := by
  have hωx := omega0_lt_inE hx
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hcB
  have hM : ∀ j, j < c → GlMo x j := fun j hj => (IH j hj (hj.trans hcB)).1
  have hT : ∀ j, j < c → GlTop x j := fun j hj => (IH j hj (hj.trans hcB)).2
  have hIH : ∀ j, j < c → GlMo x j ∧ GlTop x j := fun j hj => IH j hj (hj.trans hcB)
  -- the top bound at `c`
  have hTc : GlTop x c := by
    intro hgfc hg
    by_cases hcE : InE c
    · rw [gl_eps_self hcE hgfc]; exact lt_eN _
    have hEc := gl_E_lt_self hgfc hcE
    set e := guE c with hedef
    have he : InE e := guE_E c
    have hOe : Om1 < e := gl_Om1_lt_E hgfc
    have heB : e < gcG 0 := hEc.trans hcB
    have hge : glG e < x := gl_E_g hgfc hcB hg
    have hMe := hM e hEc
    obtain ⟨hk, -, hdE, hr, -, hkc, hrc, hdc⟩ := gl_parts hgfc
    obtain ⟨-, g0, g1, g2⟩ := gl_parts_g hωx hgfc hcB hg
    set k := log e c with hkdef
    set B := glR e x with hBdef
    have hBE : InE B := (gl_eps_read hx hx1 he hOe heB hge).2.2.2.2.2.2.2.2.2.2.2.1
    have hcN' : c < eN e := gl_lt_eN hgfc
    have hrr : glR (c % e ^ k) x < B ^ glR k x :=
      gl_bound_of hx hx1 hM hT he hOe heB hge hMe _ hrc (hrc.trans hcB) g2 (hrc.trans hcN') k hk hkc
        (hkc.trans hcB) g0 hr
    have hdB : glR (c / e ^ k) x < B := hMe _ hdE hge g1
    have hkB : glR k x < eN B := by
      rcases lt_or_ge k e with hkE | hkE
      · exact (hMe _ hkE hge g0).trans (lt_eN B)
      · have hgk : gfE ≤ k := (eN_le hOe he).trans hkE
        have hEk : guE k = e := gl_E_of_bracket he hOe hkE (hkc.trans hcN')
        have := hT k hkc hgk g0
        rwa [hEk] at this
    have hlt : glR c x < B ^ (glR k x + 1) := by
      rw [glR_dec hgfc hcB, ← gl_At_eq hgfc hcB]
      calc B ^ glR k x * glR (c / e ^ k) x + glR (c % e ^ k) x
          < B ^ glR k x * glR (c / e ^ k) x + B ^ glR k x := (add_lt_add_iff_left _).2 hrr
        _ = B ^ glR k x * (glR (c / e ^ k) x + 1) := by rw [mul_add_one]
        _ ≤ B ^ glR k x * B := mul_le_mul_right (add_one_le_of_lt hdB) _
        _ = B ^ (glR k x + 1) := by rw [opow_add, opow_one]
    exact hlt.trans (gu_pow_lt_eN hBE ((ev_isSuccLimit_of_inE (eN_E B)).add_one_lt hkB))
  refine ⟨?_, hTc⟩
  rcases lt_or_ge c gfE with hcE | hcE
  · intro b hbc hgc hgb
    have hbE := hbc.trans hcE
    rw [glG_low hcE] at hgc
    rw [glG_low hbE] at hgb
    rw [glR_low hcE, glR_low hbE]
    exact rdc_mono hx hcE hbc hgc hgb
  by_cases hcI : InE c
  · exact gl_below_eps hx hx1 hcI (Om1_lt_eW.trans_le hcE) hcB hIH
  intro b hbc hgc hgb
  have hEc := gl_E_lt_self hcE hcI
  set e := guE c with hedef
  have he : InE e := guE_E c
  have hOe : Om1 < e := gl_Om1_lt_E hcE
  have heB : e < gcG 0 := hEc.trans hcB
  have hge : glG e < x := gl_E_g hcE hcB hgc
  have hMe := hM e hEc
  obtain ⟨gcn, gck, gcd, gcr⟩ := gl_parts_g hωx hcE hcB hgc
  have hlead := gl_lead hx hx1 hcE hcB hgc
  rw [← gl_At_eq hcE hcB] at hlead
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hRE, heR⟩ := gl_eps_read hx hx1 he hOe heB hge
  rcases lt_or_ge b gfE with hbE | hbE
  · rw [glG_low hbE] at hgb
    rw [glR_low hbE]
    exact ((rdc_lt_eN hx b hgb).trans_le heR).trans_le hlead.2
  have hbB : b < gcG 0 := hbc.trans hcB
  obtain ⟨gbn, gbk, gbd, gbr⟩ := gl_parts_g hωx hbE hbB hgb
  have hee : guE b ≤ e := gl_E_mono hbE hbc.le
  rcases hee.lt_or_eq with hlt | heq
  · have h1 := hT b hbc hbE hgb
    have h2 : glR (guE b) x < glR e x := hMe _ hlt hge (gl_E_g hbE hbB hgb)
    exact (h1.trans_le (eN_le h2 hRE)).trans_le hlead.2
  -- the same bracket
  set B := glR e x with hBdef
  have hBE : InE B := hRE
  have hE1 : (1 : Ordinal.{0}) < e := Lu.lu_one_lt_E he
  obtain ⟨hk, hd0, hdE, hr, hdec, hkc, hrc, hdc⟩ := gl_parts hcE
  obtain ⟨hk', hd0', hdE', hr', hdec', hkb, hrb, hdb⟩ := gl_parts hbE
  rw [heq] at hk' hd0' hdE' hr' hdec' hkb hrb hdb gbk gbd gbr
  have hcn : c < eN e := gl_lt_eN hcE
  have hbn : b < eN e := hbc.trans hcn
  have hkk : log e b ≤ log e c := log_mono_right _ hbc.le
  have hRb : glR b x = B ^ glR (log e b) x * glR (b / e ^ log e b) x + glR (b % e ^ log e b) x := by
    rw [glR_dec hbE hbB, ← gl_At_eq hbE hbB, heq]
  have hRc : glR c x = B ^ glR (log e c) x * glR (c / e ^ log e c) x + glR (c % e ^ log e c) x := by
    rw [glR_dec hcE hcB, ← gl_At_eq hcE hcB]
  have hpowc : B ^ glR (log e c) x ≤ glR c x := by
    refine le_trans ?_ hlead.1
    calc B ^ glR (log e c) x = B ^ glR (log e c) x * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_right (glR_pos' hx hx1 hd0 (hdc.trans hcB) gcd) _
  rcases hkk.lt_or_eq with hlt | heq2
  · have hs1 : log e b + 1 ≤ log e c := add_one_le_of_lt hlt
    have hs1c : log e b + 1 < c := lt_of_le_of_lt hs1 hkc
    have hs1B : log e b + 1 < gcG 0 := hs1c.trans hcB
    have hgs : glG (log e b + 1) < x := glG_succ (ev_isSuccLimit_of_inE hx) _ hs1B gbk
    have hb1 : b < e ^ (log e b + 1) := (lt_opow_iff_log_lt hE1 (he.pos.trans_le (by
      rw [← heq]; exact gl_E_le hbE)).ne').2 (lt_add_one _)
    have hmono : glR (log e b) x < glR (log e c) x := hM _ hkc _ hlt gck gbk
    have hbd := gl_bound_of hx hx1 hM hT he hOe heB hge hMe b hbc hbB hgb hbn _
      (lt_of_le_of_lt zero_le (lt_add_one _)).ne' hs1c hs1B hgs hb1
    rw [glR_succ _ hs1B] at hbd
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
    have hrb' := gl_bound_of hx hx1 hM hT he hOe heB hge hMe r' hr'c (hr'c.trans hcB) gbr (hr'c.trans hcn) k hk
      hkc (hkc.trans hcB) gck hr'
    calc B ^ glR k x * glR d' x + glR r' x < B ^ glR k x * glR d' x + B ^ glR k x :=
          (add_lt_add_iff_left _).2 hrb'
      _ = B ^ glR k x * (glR d' x + 1) := by rw [mul_add_one]
      _ ≤ B ^ glR k x * glR d x := mul_le_mul_right (add_one_le_of_lt (hM _ hdc _ hd gcd gbd)) _
      _ ≤ _ := le_self_add
  · have hrr : r' < r := by
      have hb' : b = e ^ k * d + r' := by rw [← hd]; exact hdec'.symm
      have hc' : c = e ^ k * d + r := hdec.symm
      have h3 := hbc
      rw [hb', hc'] at h3
      exact (add_lt_add_iff_left _).1 h3
    rw [hd]
    exact (add_lt_add_iff_left _).2 (hM r hrc r' hrr gcr gbr)

theorem glR_mono {b c : Ordinal.{0}} (hc : c < gcG 0) (hbc : b < c) (hgc : glG c < x) (hgb : glG b < x) :
    glR b x < glR c x := (gl_mono_top hx hx1 c hc).1 b hbc hgc hgb

theorem glR_top {c : Ordinal.{0}} (hc : c < gcG 0) (h1 : gfE ≤ c) (hg : glG c < x) :
    glR c x < eN (glR (guE c) x) := (gl_mono_top hx hx1 c hc).2 h1 hg

/-- **Codes below an `ε`-number code `e` read below `e(x)`.** -/
theorem glR_lt_eps {b e : Ordinal.{0}} (he : InE e) (hOe : Om1 < e) (heB : e < gcG 0) (hge : glG e < x) (hbe : b < e)
    (hgb : glG b < x) : glR b x < glR e x :=
  glR_mono hx hx1 heB hbe hge hgb

end Mono

end Googology.Trans.PoR.InaccPsi.R2.Gl

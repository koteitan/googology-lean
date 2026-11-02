import Googology.Trans.PoR.InaccPsi.R2.YhR1

/-!
# YhMo: CODES BELOW `Γ(N)`: THE READING IS STRICTLY INCREASING (every layer, every base atom)

`b < c ⇒ b(x) < c(x)` for all codes below `Γ(N)` (`N < ε₀`) with gates below `x`, and the top bound
`c(x) < ε_{e(x)+1}` for the bracket's `ε`-number `e` of `c`.  The argument of `Xu.xu_mono_top` with the brackets of all
base atoms: two bracket `ε`-numbers are compared by the four cases atom/atom (`Γ_{x+1+i'} < Γ_{x+1+i}`), non-atom
below an atom (`ϑˣ(Ω₁·α'(x) + η'(x)) < Γ_{x+1+i}` since `α', η' < Γ(i)`), atom below a non-atom (`Γ(i') ≤ α` or
`Γ(i') ≤ η`, `Yh.yhPsi_lt_SC`), and non-atom/non-atom (`Gl.glA_lev`, `Gl.glA_lt_of`, `Gl.glA_lev'`).

* `YhMo`, `YhTop`, `yh_eps_data`, `yh_G_le_read`, `yh_eps_lt`, `yh_below_eps`, `yh_bound_of`;
* `yh_mono_top` (**THE INDUCTION**), `yhR_mono`, `yhR_top`, `yhR_le_mono`.

No new axiom.  New definitions: `YhMo`, `YhTop`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yh

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi
  Googology.Notation.InaccPsi.InaccSeq Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Xu
  Googology.Trans.PoR.InaccPsi.R2.Xx Googology.Trans.PoR.InaccPsi.R2.Xk

/-- The readings of the codes below `j` are below the reading of `j`. -/
def YhMo (x j : Ordinal.{0}) : Prop := ∀ b, b < j → yhG j < x → yhG b < x → yhR b x < yhR j x

/-- A code `c ≥ G` reads below the `ε`-number after the reading of its bracket's `ε`-number. -/
def YhTop (x c : Ordinal.{0}) : Prop := gcG 0 ≤ c → yhG c < x → yhR c x < eN (yhA (guE c) x)

section Mono

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {N : Ordinal.{0}} (hN : N < ε₀)
include hx hx1 hN

/-- **A non-atom `ε`-number code `e ∈ (G, Γ(N))` reads `ϑˣ(Ω₁·α(x) + η(x))`**, with the facts of its level and index. -/
theorem yh_eps_data {e : Ordinal.{0}} (he : InE e) (hGe : gcG 0 < e) (hnA : ¬ YhAt e) (heN : e < gcG N)
    (hg : yhG e < x) :
    yhR e x = glA (yhR (yhK e) x) (yhR (yhI e) x) x ∧ 1 ≤ yhK e ∧ yhK e < e ∧ yhI e < e ∧ yhG (yhK e) < x ∧
      yhG (yhI e) < x ∧ 1 ≤ yhR (yhK e) x ∧ yhR (yhK e) x ∈ Tset x ∧ yhR (yhK e) x < Om1 ∧
      yhR (yhI e) x ∈ Tset x ∧ yhR (yhI e) x < Om1 ∧ InE (yhR e x) ∧
      yhR (yhK e) x < yhR e x ∧ yhR (yhI e) x < yhR e x := by
  have hωx := omega0_lt_inE hx
  obtain ⟨hk1, hke, hie, -⟩ := yhData_spec he hGe hnA
  have hge : yhQE e < x := by rw [← yhG_base he hGe.le]; exact hg
  obtain ⟨gk, gi⟩ := yh_E_parts hωx hnA hge
  have hk0 : yhK e ≠ 0 := (lt_of_lt_of_le zero_lt_one hk1).ne'
  have hkR : 1 ≤ yhR (yhK e) x := one_le_iff_pos.2 (yhR_pos hx hx1 hN hk0 (hke.trans heN) gk)
  obtain ⟨hkT, hk1'⟩ := yhR_T hx hx1 hN (hke.trans heN) gk
  obtain ⟨hT, h1⟩ := yhR_T hx hx1 hN (hie.trans heN) gi
  obtain ⟨-, -, -, a4, a5, a6⟩ := glA_facts hx hx1 hkR hkT hk1' hT h1
  have r : yhR e x = glA (yhR (yhK e) x) (yhR (yhI e) x) x := by rw [yhR_base he hGe.le, yhA_psi hnA]
  rw [r]
  exact ⟨rfl, hk1, hke, hie, gk, gi, hkR, hkT, hk1', hT, h1, a4, a5, a6⟩

/-- **Every `ε`-number code `e ∈ [G, Γ(N))` reads at least `Γ_{x+1}`**, given the order below it. -/
theorem yh_G_le_read {e : Ordinal.{0}} (he : InE e) (hGe : gcG 0 ≤ e) (heN : e < gcG N) (hg : yhG e < x)
    (hM : ∀ j, j < e → YhMo x j) : gq 0 x ≤ yhR e x := by
  have hG0 : yhG (gcG 0) < x := by rw [yhG_atom]; exact hx.pos
  by_cases hA : YhAt e
  · obtain ⟨i, rfl⟩ := yhAt_iff.1 hA
    rw [yhR_atom]
    have hiN : i < N := gcG_strictMono.lt_iff_lt.1 heN
    exact xx_mono hx hx1 hN ((yh_gqN hx hx1 hN).2.2.2.2.1.trans_le' hiN.le) zero_le
  have hGe' : gcG 0 < e := lt_of_le_of_ne hGe (fun h => hA (h ▸ yhAt_gcG 0))
  obtain ⟨-, hk1, hke, hie, gk, gi, -, -, -, -, -, -, hKe, hIe⟩ := yh_eps_data hx hx1 hN he hGe' hA heN hg
  have hge : gcG 0 ≤ yhK e ∨ gcG 0 ≤ yhI e := by
    by_contra hc
    push Not at hc
    have := yhPsi_lt_SC (gcG_SC 0) gl_Om1_lt_G0 hc.1 hc.2
    rw [(yhData_spec he hGe' hA).2.2.2] at this
    exact absurd hGe' (not_lt.2 this.le)
  rcases hge with h | h
  · rcases h.lt_or_eq with h' | h'
    · have := hM _ hke _ h' gk hG0
      rw [yhR_atom] at this
      exact (this.trans hKe).le
    · rw [← yhR_atom 0 x, h']; exact hKe.le
  · rcases h.lt_or_eq with h' | h'
    · have := hM _ hie _ h' gi hG0
      rw [yhR_atom] at this
      exact (this.trans hIe).le
    · rw [← yhR_atom 0 x, h']; exact hIe.le

/-- **Two bracket `ε`-numbers `G ≤ e' < e < Γ(N)`** (gates below `x`): `e'(x) < e(x)`, given the order below `e` and,
when `e'` is not an atom, `η'(x) < e(x)` for its index `η'`. -/
theorem yh_eps_lt {e' e : Ordinal.{0}} (he' : InE e') (hGe' : gcG 0 ≤ e') (he : InE e) (heN : e < gcG N)
    (hlt : e' < e) (hg' : yhG e' < x) (hg : yhG e < x) (hM : ∀ j, j < e → YhMo x j)
    (hη' : ¬ YhAt e' → yhR (yhI e') x < yhR e x) : yhR e' x < yhR e x := by
  have hGe : gcG 0 < e := hGe'.trans_lt hlt
  have he'N : e' < gcG N := hlt.trans heN
  by_cases hA : YhAt e
  · obtain ⟨i, rfl⟩ := yhAt_iff.1 hA
    have hiN : i < N := gcG_strictMono.lt_iff_lt.1 heN
    have hiε : i < ε₀ := hiN.trans hN
    rw [yhR_atom]
    by_cases hA' : YhAt e'
    · -- atom below atom
      obtain ⟨i', rfl⟩ := yhAt_iff.1 hA'
      rw [yhR_atom]
      exact xx_lt hx hx1 hN ((yh_gqN hx hx1 hN).2.2.2.2.1.trans_le' hiN.le) (gcG_strictMono.lt_iff_lt.1 hlt)
    · -- non-atom below an atom: level and index below `Γ(i)`
      have hGe'' : gcG 0 < e' := lt_of_le_of_ne hGe' (fun h => hA' (h ▸ yhAt_gcG 0))
      obtain ⟨r', -, hke', hie', gk', gi', -⟩ := yh_eps_data hx hx1 hN he' hGe'' hA' he'N hg'
      rw [r']
      obtain ⟨-, -, -, -, -, hiT, hi1⟩ := yh_gqN hx hx1 hiε
      exact xkA_lt hx hx1 hiT hi1 (yhR_lt hx hx1 hiε (hke'.trans hlt) gk') (yhR_lt hx hx1 hiε (hie'.trans hlt) gi')
  have hGe'' : gcG 0 < e := hGe
  obtain ⟨r, hk1, hke, hie, gk, gi, hkR, hkT, hk1x, hT, h1, hRE, hKe, hIe⟩ :=
    yh_eps_data hx hx1 hN he hGe'' hA heN hg
  have ce := (yhData_spec he hGe'' hA).2.2.2
  by_cases hA' : YhAt e'
  · -- an atom below a non-atom: `Γ(i') ≤ α` or `Γ(i') ≤ η`
    obtain ⟨i', rfl⟩ := yhAt_iff.1 hA'
    have hG0 : yhG (gcG i') < x := by rw [yhG_atom]; exact hx.pos
    have hge : gcG i' ≤ yhK e ∨ gcG i' ≤ yhI e := by
      by_contra hc
      push Not at hc
      have := yhPsi_lt_SC (gcG_SC i') (by rw [Br.Om1_eq]; exact gcG_Om1_lt i') hc.1 hc.2
      rw [ce] at this
      exact absurd hlt (not_lt.2 this.le)
    rcases hge with h | h
    · rcases h.lt_or_eq with h' | h'
      · exact (hM _ hke _ h' gk hG0).trans hKe
      · rw [h']; exact hKe
    · rcases h.lt_or_eq with h' | h'
      · exact (hM _ hie _ h' gi hG0).trans hIe
      · rw [h']; exact hIe
  -- both non-atoms
  have hGe''' : gcG 0 < e' := lt_of_le_of_ne hGe' (fun h => hA' (h ▸ yhAt_gcG 0))
  obtain ⟨r', hk'1, hke', -, hgk', hgη', hkR', hkT', hk1', hT', h1', -, -⟩ :=
    yh_eps_data hx hx1 hN he' hGe''' hA' he'N hg'
  have ce' := (yhData_spec he' hGe''' hA').2.2.2
  have hη'' := hη' hA'
  rw [r] at hη' hη'' ⊢
  rw [r']
  rcases lt_trichotomy (yhK e') (yhK e) with hk | hk | hk
  · have hR : yhR (yhK e') x < yhR (yhK e) x := hM _ hke _ hk gk hgk'
    exact (glA_lev hx hx1 hkR' hR hkT hk1x hT h1 hT' h1').2 hη''
  · have hηη : yhI e' < yhI e := by
      have h := hlt
      rw [← ce', ← ce, hk] at h
      exact yhPsi_lt_iff.1 h
    rw [hk]
    exact glA_lt_of hx hx1 hkR hkT hk1x hT' hT h1 (hM _ hie _ hηη gi hgη')
  · have hR : yhR (yhK e) x < yhR (yhK e') x := hM _ (hke'.trans hlt) _ hk hgk' gk
    have hle : e' ≤ yhI e := by
      have h := hlt
      rw [← ce', ← ce] at h
      have := (yhPsi_lt_lev' hk hk'1).1 h
      rwa [ce'] at this
    refine (glA_lev' hx hx1 hkR hR hkT' hk1' hT h1 hT' h1').2 ?_
    rw [← r']
    rcases hle.lt_or_eq with h2 | h2
    · exact (hM _ hie _ h2 gi hg').le
    · rw [h2]

/-- **The codes below an `ε`-number code `e ∈ [G, Γ(N))` read below `e(x)`**, given the order and the top bound
below `e`. -/
theorem yh_below_eps {e : Ordinal.{0}} (he : InE e) (hGe : gcG 0 ≤ e) (heN : e < gcG N)
    (IH : ∀ j, j < e → YhMo x j ∧ YhTop x j) : YhMo x e := by
  have hωx := omega0_lt_inE hx
  have hM : ∀ j, j < e → YhMo x j := fun j hj => (IH j hj).1
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IHb =>
  intro hbe hge hgb
  have hRE : InE (yhR e x) := by
    rw [yhR_base he hGe]; exact (yhA_facts hx hx1 hN he hGe heN hge).1
  rcases lt_or_ge b (gcG 0) with hbG | hbG
  · rw [yhG_low hbG] at hgb
    rw [yhR_low hbG]
    exact ((glR_lt_G hx hx1 hbG hgb).trans_le (Gm.mg_gq0 hx hx1).le).trans_le
      (yh_G_le_read hx hx1 hN he hGe heN hge hM)
  have h1 : yhR b x < eN (yhA (guE b) x) := (IH b hbe).2 hbG hgb
  have hEb : guE b ≤ b := gl_E_le (yh_gfE_le hbG)
  have hgEb : yhG (guE b) < x := yh_E_g hbG hgb
  have h2 : yhR (guE b) x < yhR e x := by
    refine yh_eps_lt hx hx1 hN (guE_E b) (yh_G_le_E hbG) he heN (hEb.trans_lt hbe) hgEb hge hM (fun hA' => ?_)
    have hηb : yhI (guE b) < b := yh_idx_lt hbG hA'
    have hgηb : yhG (yhI (guE b)) < x :=
      (yh_E_parts hωx hA' (yh_parts_Q hbG hgb).1).2
    exact IHb _ hηb (hηb.trans hbe) hge hgηb
  rw [yhR_base (guE_E b) (yh_G_le_E hbG)] at h2
  exact h1.trans_le (eN_le h2 hRE)

/-- **`c < e^κ ⇒ c(x) < e(x)^{κ(x)}`** (`e ∈ [G, Γ(N))` an `ε`-number code, `c < ε_{e+1}`). -/
theorem yh_bound_of {M e : Ordinal.{0}} (hM : ∀ j, j < M → YhMo x j) (hT : ∀ j, j < M → YhTop x j)
    (he : InE e) (hGe : gcG 0 ≤ e) (heN : e < gcG N) (hge : yhG e < x) (hMe : YhMo x e) :
    ∀ c, c < M → c < gcG N → yhG c < x → c < eN e → ∀ κ, κ ≠ 0 → κ < M → κ < gcG N → yhG κ < x → c < e ^ κ →
    yhR c x < yhR e x ^ yhR κ x := by
  have hωx := omega0_lt_inE hx
  have hOe : Om1 < e := gl_Om1_lt_G0.trans_le hGe
  set B := yhR e x with hBdef
  have hBE : InE B := by rw [hBdef, yhR_base he hGe]; exact (yhA_facts hx hx1 hN he hGe heN hge).1
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hcM hcN hg hcn κ hκ hκM hκN hgκ hcκ
  have hBκ : B ≤ B ^ yhR κ x := by
    calc B = B ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ B ^ yhR κ x := opow_le_opow_right hBE.pos (one_le_iff_pos.2 (yhR_pos hx hx1 hN hκ hκN hgκ))
  rcases lt_or_ge c e with hcE | hcE
  · exact (hMe c hcE hge hg).trans_le hBκ
  have hcG : gcG 0 ≤ c := hGe.trans hcE
  have hgfc := yh_gfE_le hcG
  have hEc : guE c = e := gl_E_of_bracket he hOe hcE hcn
  obtain ⟨hj, -, hdE, hr, -, hjc, hrc, hdc⟩ := gl_parts hgfc
  obtain ⟨g0, g1, g2⟩ := yh_parts_g hωx hcG hg
  rw [hEc] at hj hdE hr hjc hrc hdc g0 g1 g2
  have hjk : log e c < κ := (lt_opow_iff_log_lt (Lu.lu_one_lt_E he) (he.pos.trans_le hcE).ne').1 hcκ
  have hrr := IH _ hrc (hrc.trans hcM) (hrc.trans hcN) g2 ((hrc.trans hcn)) _ hj (hjc.trans hcM)
    (hjc.trans hcN) g0 hr
  have hjx : yhR (log e c) x < yhR κ x := hM κ hκM _ hjk hgκ g0
  have hdB : yhR (c / e ^ log e c) x < B := hMe _ hdE hge g1
  rw [yhR_dec hcG, hEc, ← yhR_base he hGe]
  calc B ^ yhR (log e c) x * yhR (c / e ^ log e c) x + yhR (c % e ^ log e c) x
      < B ^ yhR (log e c) x * yhR (c / e ^ log e c) x + B ^ yhR (log e c) x :=
        (add_lt_add_iff_left _).2 hrr
    _ = B ^ yhR (log e c) x * (yhR (c / e ^ log e c) x + 1) := by rw [mul_add_one]
    _ ≤ B ^ yhR (log e c) x * B := mul_le_mul_right (add_one_le_of_lt hdB) _
    _ = B ^ (yhR (log e c) x + 1) := by rw [opow_add, opow_one]
    _ ≤ B ^ yhR κ x := opow_le_opow_right hBE.pos (add_one_le_of_lt hjx)

/-- **THE INDUCTION**: the order and the top bound at every code below `Γ(N)`. -/
theorem yh_mono_top : ∀ c, c < gcG N → YhMo x c ∧ YhTop x c := by
  have hωx := omega0_lt_inE hx
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hcN
  have hM : ∀ j, j < c → YhMo x j := fun j hj => (IH j hj (hj.trans hcN)).1
  have hT : ∀ j, j < c → YhTop x j := fun j hj => (IH j hj (hj.trans hcN)).2
  have hIH : ∀ j, j < c → YhMo x j ∧ YhTop x j := fun j hj => IH j hj (hj.trans hcN)
  -- the top bound at `c`
  have hTc : YhTop x c := by
    intro hcG hg
    have hgfc := yh_gfE_le hcG
    by_cases hcE : InE c
    · rw [gl_eps_self hcE hgfc, ← yhR_base hcE hcG]; exact lt_eN _
    have hEc := gl_E_lt_self hgfc hcE
    set e := guE c with hedef
    have he : InE e := guE_E c
    have hGe : gcG 0 ≤ e := yh_G_le_E hcG
    have hOe : Om1 < e := gl_Om1_lt_G0.trans_le hGe
    have heN : e < gcG N := hEc.trans hcN
    have hge : yhG e < x := yh_E_g hcG hg
    have hMe := hM e hEc
    obtain ⟨hk, -, hdE, hr, -, hkc, hrc, hdc⟩ := gl_parts hgfc
    obtain ⟨g0, g1, g2⟩ := yh_parts_g hωx hcG hg
    set k := log e c with hkdef
    set B := yhR e x with hBdef
    have hBA : B = yhA e x := yhR_base he hGe x
    have hBE : InE B := by rw [hBA]; exact (yhA_facts hx hx1 hN he hGe heN hge).1
    have hcN' : c < eN e := gl_lt_eN hgfc
    have hrr : yhR (c % e ^ k) x < B ^ yhR k x :=
      yh_bound_of hx hx1 hN hM hT he hGe heN hge hMe _ hrc (hrc.trans hcN) g2 (hrc.trans hcN') k hk hkc
        (hkc.trans hcN) g0 hr
    have hdB : yhR (c / e ^ k) x < B := hMe _ hdE hge g1
    have hkB : yhR k x < eN B := by
      rcases lt_or_ge k e with hkE | hkE
      · exact (hMe _ hkE hge g0).trans (lt_eN B)
      · have hEk : guE k = e := gl_E_of_bracket he hOe hkE (hkc.trans hcN')
        have := hT k hkc (hGe.trans hkE) g0
        rwa [hEk, ← hBA] at this
    have hlt : yhR c x < B ^ (yhR k x + 1) := by
      rw [yhR_dec hcG, ← hBA]
      calc B ^ yhR k x * yhR (c / e ^ k) x + yhR (c % e ^ k) x
          < B ^ yhR k x * yhR (c / e ^ k) x + B ^ yhR k x := (add_lt_add_iff_left _).2 hrr
        _ = B ^ yhR k x * (yhR (c / e ^ k) x + 1) := by rw [mul_add_one]
        _ ≤ B ^ yhR k x * B := mul_le_mul_right (add_one_le_of_lt hdB) _
        _ = B ^ (yhR k x + 1) := by rw [opow_add, opow_one]
    rw [← hBA]
    exact hlt.trans (gu_pow_lt_eN hBE ((ev_isSuccLimit_of_inE (eN_E B)).add_one_lt hkB))
  refine ⟨?_, hTc⟩
  rcases lt_or_ge c (gcG 0) with hcG | hcG
  · intro b hbc hgc hgb
    have hbG := hbc.trans hcG
    rw [yhG_low hcG] at hgc
    rw [yhG_low hbG] at hgb
    rw [yhR_low hcG, yhR_low hbG]
    exact glR_mono hx hx1 hcG hbc hgc hgb
  have hcE := yh_gfE_le hcG
  by_cases hcI : InE c
  · exact yh_below_eps hx hx1 hN hcI hcG hcN hIH
  intro b hbc hgc hgb
  have hEc := gl_E_lt_self hcE hcI
  set e := guE c with hedef
  have he : InE e := guE_E c
  have hGe : gcG 0 ≤ e := yh_G_le_E hcG
  have heN : e < gcG N := hEc.trans hcN
  have hge : yhG e < x := yh_E_g hcG hgc
  have hMe := hM e hEc
  obtain ⟨gck, gcd, gcr⟩ := yh_parts_g hωx hcG hgc
  set B := yhR e x with hBdef
  have hBA : B = yhA e x := yhR_base he hGe x
  have hBE : InE B := by rw [hBA]; exact (yhA_facts hx hx1 hN he hGe heN hge).1
  obtain ⟨hk, hd0, hdE, hr, hdec, hkc, hrc, hdc⟩ := gl_parts hcE
  have hRc : yhR c x = B ^ yhR (log e c) x * yhR (c / e ^ log e c) x + yhR (c % e ^ log e c) x := by
    rw [yhR_dec hcG, ← hBA]
  have hpowc : B ^ yhR (log e c) x ≤ yhR c x := by
    rw [hRc]
    calc B ^ yhR (log e c) x = B ^ yhR (log e c) x * 1 := (mul_one _).symm
      _ ≤ B ^ yhR (log e c) x * yhR (c / e ^ log e c) x :=
        mul_le_mul_right (one_le_iff_pos.2 (yhR_pos hx hx1 hN hd0 (hdc.trans hcN) gcd)) _
      _ ≤ _ := le_self_add
  have hleadB : B ≤ yhR c x := by
    refine le_trans ?_ hpowc
    calc B = B ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ _ := opow_le_opow_right hBE.pos (one_le_iff_pos.2 (yhR_pos hx hx1 hN hk (hkc.trans hcN) gck))
  rcases lt_or_ge b (gcG 0) with hbG | hbG
  · rw [yhG_low hbG] at hgb
    rw [yhR_low hbG]
    exact (((glR_lt_G hx hx1 hbG hgb).trans_le (Gm.mg_gq0 hx hx1).le).trans_le
      (yh_G_le_read hx hx1 hN he hGe heN hge (fun j hj => hM j (hj.trans hEc)))).trans_le hleadB
  have hbE := yh_gfE_le hbG
  have hbN : b < gcG N := hbc.trans hcN
  obtain ⟨gbk, gbd, gbr⟩ := yh_parts_g hωx hbG hgb
  have hee : guE b ≤ e := gl_E_mono hbE hbc.le
  rcases hee.lt_or_eq with hlt | heq
  · have h1 := hT b hbc hbG hgb
    have h2 : yhR (guE b) x < yhR e x := hMe _ hlt hge (yh_E_g hbG hgb)
    rw [yhR_base (guE_E b) (yh_G_le_E hbG)] at h2
    exact (h1.trans_le (eN_le h2 hBE)).trans_le hleadB
  -- the same bracket
  have hE1 : (1 : Ordinal.{0}) < e := Lu.lu_one_lt_E he
  obtain ⟨hk', hd0', hdE', hr', hdec', hkb, hrb, hdb⟩ := gl_parts hbE
  rw [heq] at hk' hd0' hdE' hr' hdec' hkb hrb hdb gbk gbd gbr
  have hcn : c < eN e := gl_lt_eN hcE
  have hbn : b < eN e := hbc.trans hcn
  have hkk : log e b ≤ log e c := log_mono_right _ hbc.le
  have hRb : yhR b x = B ^ yhR (log e b) x * yhR (b / e ^ log e b) x + yhR (b % e ^ log e b) x := by
    rw [yhR_dec hbG, heq, ← hBA]
  rcases hkk.lt_or_eq with hlt | heq2
  · have hs1 : log e b + 1 ≤ log e c := add_one_le_of_lt hlt
    have hs1c : log e b + 1 < c := lt_of_le_of_lt hs1 hkc
    have hs1N : log e b + 1 < gcG N := hs1c.trans hcN
    have hgs : yhG (log e b + 1) < x := yhG_succ (ev_isSuccLimit_of_inE hx) _ gbk
    have hb1 : b < e ^ (log e b + 1) := (lt_opow_iff_log_lt hE1 (he.pos.trans_le (by
      rw [← heq]; exact gl_E_le hbE)).ne').2 (lt_add_one _)
    have hmono : yhR (log e b) x < yhR (log e c) x := hM _ hkc _ hlt gck gbk
    have hbd := yh_bound_of hx hx1 hN hM hT he hGe heN hge hMe b hbc hbN hgb hbn _
      (lt_of_le_of_lt zero_le (lt_add_one _)).ne' hs1c hs1N hgs hb1
    rw [yhR_succ] at hbd
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
    have hrb' := yh_bound_of hx hx1 hN hM hT he hGe heN hge hMe r' hr'c (hr'c.trans hcN) gbr (hr'c.trans hcn) k hk
      hkc (hkc.trans hcN) gck hr'
    calc B ^ yhR k x * yhR d' x + yhR r' x < B ^ yhR k x * yhR d' x + B ^ yhR k x :=
          (add_lt_add_iff_left _).2 hrb'
      _ = B ^ yhR k x * (yhR d' x + 1) := by rw [mul_add_one]
      _ ≤ B ^ yhR k x * yhR d x := mul_le_mul_right (add_one_le_of_lt (hM _ hdc _ hd gcd gbd)) _
      _ ≤ _ := le_self_add
  · have hrr : r' < r := by
      have hb' : b = e ^ k * d + r' := by rw [← hd]; exact hdec'.symm
      have hc' : c = e ^ k * d + r := hdec.symm
      have h3 := hbc
      rw [hb', hc'] at h3
      exact (add_lt_add_iff_left _).1 h3
    rw [hd]
    exact (add_lt_add_iff_left _).2 (hM r hrc r' hrr gcr gbr)

theorem yhR_mono {b c : Ordinal.{0}} (hc : c < gcG N) (hbc : b < c) (hgc : yhG c < x) (hgb : yhG b < x) :
    yhR b x < yhR c x := (yh_mono_top hx hx1 hN c hc).1 b hbc hgc hgb

theorem yhR_top {c : Ordinal.{0}} (hc : c < gcG N) (hG : gcG 0 ≤ c) (hg : yhG c < x) :
    yhR c x < eN (yhA (guE c) x) := (yh_mono_top hx hx1 hN c hc).2 hG hg

theorem yhR_le_mono {b c : Ordinal.{0}} (hc : c < gcG N) (hbc : b ≤ c) (hgc : yhG c < x) (hgb : yhG b < x) :
    yhR b x ≤ yhR c x := by
  rcases hbc.lt_or_eq with h | rfl
  · exact (yhR_mono hx hx1 hN hc h hgc hgb).le
  · exact le_rfl

end Mono

end Googology.Trans.PoR.InaccPsi.R2.Yh

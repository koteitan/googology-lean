import Googology.Trans.PoR.InaccPsi.R2.YrR1
import Googology.Trans.PoR.InaccPsi.R2.YhMo

/-!
# YrMo: CODES BELOW `B_Γ`, READ ATOM INDICES: THE READING IS STRICTLY INCREASING

`b < c ⇒ b(x) < c(x)` for all codes below `B_Γ` with gates below `x`, and the top bound `c(x) < ε_{e(x)+1}` for the
bracket's `ε`-number `e` of `c`.  The argument of `Yh.yh_mono_top` with the atom `Γ(i)` read `ϑˣ(Ω₁·Ω₁ + i(x))`:
atom/atom by the order of the indices (`i' < i < Γ(i)`, so the order at `i` is already known), a non-atom
`ϑˣ(Ω₁·α'(x) + η'(x))` below an atom `Γ(i)` from `α'(x), η'(x) < Γ(i)(x)` (the order below `Γ(i)`, inner
induction) and `Xk.xkA_lt` at the admissible index `i(x)`; the other two cases as in `Yh.YhMo`.

* `YrMo`, `YrTop`, `yr_eps_data`, `yr_G_le_read`, `yr_eps_lt`, `yr_below_eps`, `yr_bound_of`;
* `yr_mono_top` (**THE INDUCTION**), `yrR_mono`, `yrR_top`, `yrR_le_mono`.

No new axiom.  New definitions: `YrMo`, `YrTop`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yr

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi
  Googology.Notation.InaccPsi.InaccSeq Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Xu
  Googology.Trans.PoR.InaccPsi.R2.Xx Googology.Trans.PoR.InaccPsi.R2.Xk Googology.Trans.PoR.InaccPsi.R2.Yh

/-- The readings of the codes below `j` are below the reading of `j`. -/
def YrMo (x j : Ordinal.{0}) : Prop := ∀ b, b < j → yrG j < x → yrG b < x → yrR b x < yrR j x

/-- A code `c ≥ G` reads below the `ε`-number after the reading of its bracket's `ε`-number. -/
def YrTop (x c : Ordinal.{0}) : Prop := gcG 0 ≤ c → yrG c < x → yrR c x < eN (yrA (guE c) x)

section Mono

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **A non-atom `ε`-number code `e ∈ (G, B_Γ)` reads `ϑˣ(Ω₁·α(x) + η(x))`**, with the facts of its level and index. -/
theorem yr_eps_data {e : Ordinal.{0}} (he : InE e) (hGe : gcG 0 < e) (hnA : ¬ YhAt e) (heB : e < Tf.tfBG)
    (hg : yrG e < x) :
    yrR e x = glA (yrR (yhK e) x) (yrR (yhI e) x) x ∧ 1 ≤ yhK e ∧ yhK e < e ∧ yhI e < e ∧ yrG (yhK e) < x ∧
      yrG (yhI e) < x ∧ 1 ≤ yrR (yhK e) x ∧ yrR (yhK e) x ∈ Tset x ∧ yrR (yhK e) x < Om1 ∧
      yrR (yhI e) x ∈ Tset x ∧ yrR (yhI e) x < Om1 ∧ InE (yrR e x) ∧
      yrR (yhK e) x < yrR e x ∧ yrR (yhI e) x < yrR e x := by
  have hωx := omega0_lt_inE hx
  obtain ⟨hk1, hke, hie, -⟩ := yhData_spec he hGe hnA
  have hge : yrQE e < x := by rw [← yrG_base he hGe.le]; exact hg
  obtain ⟨gk, gi⟩ := yr_E_parts hωx hnA hge
  have hk0 : yhK e ≠ 0 := (lt_of_lt_of_le zero_lt_one hk1).ne'
  have hkR : 1 ≤ yrR (yhK e) x := one_le_iff_pos.2 (yrR_pos hx hx1 hk0 (hke.trans heB) gk)
  obtain ⟨hkT, hk1'⟩ := yrR_T hx hx1 (hke.trans heB) gk
  obtain ⟨hT, h1⟩ := yrR_T hx hx1 (hie.trans heB) gi
  obtain ⟨-, -, -, a4, a5, a6⟩ := glA_facts hx hx1 hkR hkT hk1' hT h1
  have r : yrR e x = glA (yrR (yhK e) x) (yrR (yhI e) x) x := by rw [yrR_base he hGe.le, yrA_psi hnA]
  rw [r]
  exact ⟨rfl, hk1, hke, hie, gk, gi, hkR, hkT, hk1', hT, h1, a4, a5, a6⟩

/-- **Every `ε`-number code `e ∈ [G, B_Γ)` reads at least `Γ_{x+1}`**, given the order below it. -/
theorem yr_G_le_read {e : Ordinal.{0}} (he : InE e) (hGe : gcG 0 ≤ e) (heB : e < Tf.tfBG) (hg : yrG e < x)
    (hM : ∀ j, j < e → YrMo x j) : gq 0 x ≤ yrR e x := by
  have hG0 : yrG (gcG 0) < x := by rw [yrG_G0]; exact hx.pos
  by_cases hA : YhAt e
  · obtain ⟨i, rfl⟩ := yhAt_iff.1 hA
    obtain ⟨hii, hie⟩ := yr_atom_idx rfl heB
    rw [yrR_atom hii]
    have hiN := yrR_N hx hx1 (hie.trans heB) (yr_E_atom (omega0_lt_inE hx) hii hg)
    exact yr_mono hx hx1 hiN zero_le
  have hGe' : gcG 0 < e := lt_of_le_of_ne hGe (fun h => hA (h ▸ yhAt_gcG 0))
  obtain ⟨-, hk1, hke, hie, gk, gi, -, -, -, -, -, -, hKe, hIe⟩ := yr_eps_data hx hx1 he hGe' hA heB hg
  have hge : gcG 0 ≤ yhK e ∨ gcG 0 ≤ yhI e := by
    by_contra hc
    push Not at hc
    have := yhPsi_lt_SC (gcG_SC 0) gl_Om1_lt_G0 hc.1 hc.2
    rw [(yhData_spec he hGe' hA).2.2.2] at this
    exact absurd hGe' (not_lt.2 this.le)
  rcases hge with h | h
  · rcases h.lt_or_eq with h' | h'
    · have := hM _ hke _ h' gk hG0
      rw [yrR_G0] at this
      exact (this.trans hKe).le
    · rw [← yrR_G0 x, h']; exact hKe.le
  · rcases h.lt_or_eq with h' | h'
    · have := hM _ hie _ h' gi hG0
      rw [yrR_G0] at this
      exact (this.trans hIe).le
    · rw [← yrR_G0 x, h']; exact hIe.le

/-- **Two bracket `ε`-numbers `G ≤ e' < e < B_Γ`** (gates below `x`): `e'(x) < e(x)`, given the order below `e` and,
when `e'` is not an atom, `η'(x) < e(x)` for its index `η'`. -/
theorem yr_eps_lt {e' e : Ordinal.{0}} (he' : InE e') (hGe' : gcG 0 ≤ e') (he : InE e) (heB : e < Tf.tfBG)
    (hlt : e' < e) (hg' : yrG e' < x) (hg : yrG e < x) (hM : ∀ j, j < e → YrMo x j)
    (hη' : ¬ YhAt e' → yrR (yhI e') x < yrR e x) (hα' : ¬ YhAt e' → yrR (yhK e') x < yrR e x) :
    yrR e' x < yrR e x := by
  have hGe : gcG 0 < e := hGe'.trans_lt hlt
  have he'B : e' < Tf.tfBG := hlt.trans heB
  by_cases hA : YhAt e
  · obtain ⟨i, rfl⟩ := yhAt_iff.1 hA
    have hωx := omega0_lt_inE hx
    obtain ⟨hii, hie⟩ := yr_atom_idx rfl heB
    have hgi : yrG i < x := yr_E_atom hωx hii hg
    have hiN := yrR_N hx hx1 (hie.trans heB) hgi
    have hAe : yrR (gcG i) x = gq (yrR i x) x := yrR_atom hii x
    by_cases hA' : YhAt e'
    · -- atom below atom: the order of the indices
      obtain ⟨i', rfl⟩ := yhAt_iff.1 hA'
      obtain ⟨hii', -⟩ := yr_atom_idx rfl he'B
      rw [hAe, yrR_atom hii']
      have hi'i : i' < i := gcG_strictMono.lt_iff_lt.1 hlt
      exact yr_lt hx hx1 hiN (hM i hie i' hi'i hgi (yr_E_atom hωx hii' hg'))
    · -- non-atom below an atom: level and index below `Γ(i)(x)`
      have hGe'' : gcG 0 < e' := lt_of_le_of_ne hGe' (fun h => hA' (h ▸ yhAt_gcG 0))
      obtain ⟨r', -, -, -, -, -, -⟩ := yr_eps_data hx hx1 he' hGe'' hA' he'B hg'
      rw [r']
      have h1 := hα' hA'
      have h2 := hη' hA'
      rw [hAe] at h1 h2 ⊢
      exact xkA_lt hx hx1 hiN.1 hiN.2.1 h1 h2
  have hGe'' : gcG 0 < e := hGe
  obtain ⟨r, hk1, hke, hie, gk, gi, hkR, hkT, hk1x, hT, h1, hRE, hKe, hIe⟩ :=
    yr_eps_data hx hx1 he hGe'' hA heB hg
  have ce := (yhData_spec he hGe'' hA).2.2.2
  by_cases hA' : YhAt e'
  · -- an atom below a non-atom: `Γ(i') ≤ α` or `Γ(i') ≤ η`
    obtain ⟨i', rfl⟩ := yhAt_iff.1 hA'
    have hG0 : yrG (gcG i') < x := hg'
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
    yr_eps_data hx hx1 he' hGe''' hA' he'B hg'
  have ce' := (yhData_spec he' hGe''' hA').2.2.2
  have hη'' := hη' hA'
  rw [r] at hη' hη'' ⊢
  rw [r']
  rcases lt_trichotomy (yhK e') (yhK e) with hk | hk | hk
  · have hR : yrR (yhK e') x < yrR (yhK e) x := hM _ hke _ hk gk hgk'
    exact (glA_lev hx hx1 hkR' hR hkT hk1x hT h1 hT' h1').2 hη''
  · have hηη : yhI e' < yhI e := by
      have h := hlt
      rw [← ce', ← ce, hk] at h
      exact yhPsi_lt_iff.1 h
    rw [hk]
    exact glA_lt_of hx hx1 hkR hkT hk1x hT' hT h1 (hM _ hie _ hηη gi hgη')
  · have hR : yrR (yhK e) x < yrR (yhK e') x := hM _ (hke'.trans hlt) _ hk hgk' gk
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

/-- **The codes below an `ε`-number code `e ∈ [G, B_Γ)` read below `e(x)`**, given the order and the top bound
below `e`. -/
theorem yr_below_eps {e : Ordinal.{0}} (he : InE e) (hGe : gcG 0 ≤ e) (heB : e < Tf.tfBG)
    (IH : ∀ j, j < e → YrMo x j ∧ YrTop x j) : YrMo x e := by
  have hωx := omega0_lt_inE hx
  have hM : ∀ j, j < e → YrMo x j := fun j hj => (IH j hj).1
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IHb =>
  intro hbe hge hgb
  have hRE : InE (yrR e x) := by
    rw [yrR_base he hGe]; exact (yrA_facts hx hx1 he hGe heB hge).1
  rcases lt_or_ge b (gcG 0) with hbG | hbG
  · rw [yrG_low hbG] at hgb
    rw [yrR_low hbG]
    exact ((glR_lt_G hx hx1 hbG hgb).trans_le (Gm.mg_gq0 hx hx1).le).trans_le
      (yr_G_le_read hx hx1 he hGe heB hge hM)
  have h1 : yrR b x < eN (yrA (guE b) x) := (IH b hbe).2 hbG hgb
  have hEb : guE b ≤ b := gl_E_le (yh_gfE_le hbG)
  have hgEb : yrG (guE b) < x := yr_E_g hbG hgb
  have h2 : yrR (guE b) x < yrR e x := by
    refine yr_eps_lt hx hx1 (guE_E b) (yh_G_le_E hbG) he heB (hEb.trans_lt hbe) hgEb hge hM (fun hA' => ?_)
      (fun hA' => ?_)
    · have hηb : yhI (guE b) < b := yh_idx_lt hbG hA'
      have hgηb : yrG (yhI (guE b)) < x :=
        (yr_E_parts hωx hA' (yr_parts_Q hbG hgb).1).2
      exact IHb _ hηb (hηb.trans hbe) hge hgηb
    · have hαb : yhK (guE b) < b := yh_lev_lt hbG hA'
      have hgαb : yrG (yhK (guE b)) < x :=
        (yr_E_parts hωx hA' (yr_parts_Q hbG hgb).1).1
      exact IHb _ hαb (hαb.trans hbe) hge hgαb
  rw [yrR_base (guE_E b) (yh_G_le_E hbG)] at h2
  exact h1.trans_le (eN_le h2 hRE)

/-- **`c < e^κ ⇒ c(x) < e(x)^{κ(x)}`** (`e ∈ [G, B_Γ)` an `ε`-number code, `c < ε_{e+1}`). -/
theorem yr_bound_of {M e : Ordinal.{0}} (hM : ∀ j, j < M → YrMo x j) (hT : ∀ j, j < M → YrTop x j)
    (he : InE e) (hGe : gcG 0 ≤ e) (heB : e < Tf.tfBG) (hge : yrG e < x) (hMe : YrMo x e) :
    ∀ c, c < M → c < Tf.tfBG → yrG c < x → c < eN e → ∀ κ, κ ≠ 0 → κ < M → κ < Tf.tfBG → yrG κ < x → c < e ^ κ →
    yrR c x < yrR e x ^ yrR κ x := by
  have hωx := omega0_lt_inE hx
  have hOe : Om1 < e := gl_Om1_lt_G0.trans_le hGe
  set B := yrR e x with hBdef
  have hBE : InE B := by rw [hBdef, yrR_base he hGe]; exact (yrA_facts hx hx1 he hGe heB hge).1
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hcM hcB hg hcn κ hκ hκM hκB hgκ hcκ
  have hBκ : B ≤ B ^ yrR κ x := by
    calc B = B ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ B ^ yrR κ x := opow_le_opow_right hBE.pos (one_le_iff_pos.2 (yrR_pos hx hx1 hκ hκB hgκ))
  rcases lt_or_ge c e with hcE | hcE
  · exact (hMe c hcE hge hg).trans_le hBκ
  have hcG : gcG 0 ≤ c := hGe.trans hcE
  have hgfc := yh_gfE_le hcG
  have hEc : guE c = e := gl_E_of_bracket he hOe hcE hcn
  obtain ⟨hj, -, hdE, hr, -, hjc, hrc, hdc⟩ := gl_parts hgfc
  obtain ⟨g0, g1, g2⟩ := yr_parts_g hωx hcG hg
  rw [hEc] at hj hdE hr hjc hrc hdc g0 g1 g2
  have hjk : log e c < κ := (lt_opow_iff_log_lt (Lu.lu_one_lt_E he) (he.pos.trans_le hcE).ne').1 hcκ
  have hrr := IH _ hrc (hrc.trans hcM) (hrc.trans hcB) g2 ((hrc.trans hcn)) _ hj (hjc.trans hcM)
    (hjc.trans hcB) g0 hr
  have hjx : yrR (log e c) x < yrR κ x := hM κ hκM _ hjk hgκ g0
  have hdB : yrR (c / e ^ log e c) x < B := hMe _ hdE hge g1
  rw [yrR_dec hcG, hEc, ← yrR_base he hGe]
  calc B ^ yrR (log e c) x * yrR (c / e ^ log e c) x + yrR (c % e ^ log e c) x
      < B ^ yrR (log e c) x * yrR (c / e ^ log e c) x + B ^ yrR (log e c) x :=
        (add_lt_add_iff_left _).2 hrr
    _ = B ^ yrR (log e c) x * (yrR (c / e ^ log e c) x + 1) := by rw [mul_add_one]
    _ ≤ B ^ yrR (log e c) x * B := mul_le_mul_right (add_one_le_of_lt hdB) _
    _ = B ^ (yrR (log e c) x + 1) := by rw [opow_add, opow_one]
    _ ≤ B ^ yrR κ x := opow_le_opow_right hBE.pos (add_one_le_of_lt hjx)

/-- **THE INDUCTION**: the order and the top bound at every code below `B_Γ`. -/
theorem yr_mono_top : ∀ c, c < Tf.tfBG → YrMo x c ∧ YrTop x c := by
  have hωx := omega0_lt_inE hx
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hcB
  have hM : ∀ j, j < c → YrMo x j := fun j hj => (IH j hj (hj.trans hcB)).1
  have hT : ∀ j, j < c → YrTop x j := fun j hj => (IH j hj (hj.trans hcB)).2
  have hIH : ∀ j, j < c → YrMo x j ∧ YrTop x j := fun j hj => IH j hj (hj.trans hcB)
  -- the top bound at `c`
  have hTc : YrTop x c := by
    intro hcG hg
    have hgfc := yh_gfE_le hcG
    by_cases hcE : InE c
    · rw [gl_eps_self hcE hgfc, ← yrR_base hcE hcG]; exact lt_eN _
    have hEc := gl_E_lt_self hgfc hcE
    set e := guE c with hedef
    have he : InE e := guE_E c
    have hGe : gcG 0 ≤ e := yh_G_le_E hcG
    have hOe : Om1 < e := gl_Om1_lt_G0.trans_le hGe
    have heB : e < Tf.tfBG := hEc.trans hcB
    have hge : yrG e < x := yr_E_g hcG hg
    have hMe := hM e hEc
    obtain ⟨hk, -, hdE, hr, -, hkc, hrc, hdc⟩ := gl_parts hgfc
    obtain ⟨g0, g1, g2⟩ := yr_parts_g hωx hcG hg
    set k := log e c with hkdef
    set B := yrR e x with hBdef
    have hBA : B = yrA e x := yrR_base he hGe x
    have hBE : InE B := by rw [hBA]; exact (yrA_facts hx hx1 he hGe heB hge).1
    have hcB' : c < eN e := gl_lt_eN hgfc
    have hrr : yrR (c % e ^ k) x < B ^ yrR k x :=
      yr_bound_of hx hx1 hM hT he hGe heB hge hMe _ hrc (hrc.trans hcB) g2 (hrc.trans hcB') k hk hkc
        (hkc.trans hcB) g0 hr
    have hdB : yrR (c / e ^ k) x < B := hMe _ hdE hge g1
    have hkB : yrR k x < eN B := by
      rcases lt_or_ge k e with hkE | hkE
      · exact (hMe _ hkE hge g0).trans (lt_eN B)
      · have hEk : guE k = e := gl_E_of_bracket he hOe hkE (hkc.trans hcB')
        have := hT k hkc (hGe.trans hkE) g0
        rwa [hEk, ← hBA] at this
    have hlt : yrR c x < B ^ (yrR k x + 1) := by
      rw [yrR_dec hcG, ← hBA]
      calc B ^ yrR k x * yrR (c / e ^ k) x + yrR (c % e ^ k) x
          < B ^ yrR k x * yrR (c / e ^ k) x + B ^ yrR k x := (add_lt_add_iff_left _).2 hrr
        _ = B ^ yrR k x * (yrR (c / e ^ k) x + 1) := by rw [mul_add_one]
        _ ≤ B ^ yrR k x * B := mul_le_mul_right (add_one_le_of_lt hdB) _
        _ = B ^ (yrR k x + 1) := by rw [opow_add, opow_one]
    rw [← hBA]
    exact hlt.trans (gu_pow_lt_eN hBE ((ev_isSuccLimit_of_inE (eN_E B)).add_one_lt hkB))
  refine ⟨?_, hTc⟩
  rcases lt_or_ge c (gcG 0) with hcG | hcG
  · intro b hbc hgc hgb
    have hbG := hbc.trans hcG
    rw [yrG_low hcG] at hgc
    rw [yrG_low hbG] at hgb
    rw [yrR_low hcG, yrR_low hbG]
    exact glR_mono hx hx1 hcG hbc hgc hgb
  have hcE := yh_gfE_le hcG
  by_cases hcI : InE c
  · exact yr_below_eps hx hx1 hcI hcG hcB hIH
  intro b hbc hgc hgb
  have hEc := gl_E_lt_self hcE hcI
  set e := guE c with hedef
  have he : InE e := guE_E c
  have hGe : gcG 0 ≤ e := yh_G_le_E hcG
  have heB : e < Tf.tfBG := hEc.trans hcB
  have hge : yrG e < x := yr_E_g hcG hgc
  have hMe := hM e hEc
  obtain ⟨gck, gcd, gcr⟩ := yr_parts_g hωx hcG hgc
  set B := yrR e x with hBdef
  have hBA : B = yrA e x := yrR_base he hGe x
  have hBE : InE B := by rw [hBA]; exact (yrA_facts hx hx1 he hGe heB hge).1
  obtain ⟨hk, hd0, hdE, hr, hdec, hkc, hrc, hdc⟩ := gl_parts hcE
  have hRc : yrR c x = B ^ yrR (log e c) x * yrR (c / e ^ log e c) x + yrR (c % e ^ log e c) x := by
    rw [yrR_dec hcG, ← hBA]
  have hpowc : B ^ yrR (log e c) x ≤ yrR c x := by
    rw [hRc]
    calc B ^ yrR (log e c) x = B ^ yrR (log e c) x * 1 := (mul_one _).symm
      _ ≤ B ^ yrR (log e c) x * yrR (c / e ^ log e c) x :=
        mul_le_mul_right (one_le_iff_pos.2 (yrR_pos hx hx1 hd0 (hdc.trans hcB) gcd)) _
      _ ≤ _ := le_self_add
  have hleadB : B ≤ yrR c x := by
    refine le_trans ?_ hpowc
    calc B = B ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ _ := opow_le_opow_right hBE.pos (one_le_iff_pos.2 (yrR_pos hx hx1 hk (hkc.trans hcB) gck))
  rcases lt_or_ge b (gcG 0) with hbG | hbG
  · rw [yrG_low hbG] at hgb
    rw [yrR_low hbG]
    exact (((glR_lt_G hx hx1 hbG hgb).trans_le (Gm.mg_gq0 hx hx1).le).trans_le
      (yr_G_le_read hx hx1 he hGe heB hge (fun j hj => hM j (hj.trans hEc)))).trans_le hleadB
  have hbE := yh_gfE_le hbG
  have hbB : b < Tf.tfBG := hbc.trans hcB
  obtain ⟨gbk, gbd, gbr⟩ := yr_parts_g hωx hbG hgb
  have hee : guE b ≤ e := gl_E_mono hbE hbc.le
  rcases hee.lt_or_eq with hlt | heq
  · have h1 := hT b hbc hbG hgb
    have h2 : yrR (guE b) x < yrR e x := hMe _ hlt hge (yr_E_g hbG hgb)
    rw [yrR_base (guE_E b) (yh_G_le_E hbG)] at h2
    exact (h1.trans_le (eN_le h2 hBE)).trans_le hleadB
  -- the same bracket
  have hE1 : (1 : Ordinal.{0}) < e := Lu.lu_one_lt_E he
  obtain ⟨hk', hd0', hdE', hr', hdec', hkb, hrb, hdb⟩ := gl_parts hbE
  rw [heq] at hk' hd0' hdE' hr' hdec' hkb hrb hdb gbk gbd gbr
  have hcn : c < eN e := gl_lt_eN hcE
  have hbn : b < eN e := hbc.trans hcn
  have hkk : log e b ≤ log e c := log_mono_right _ hbc.le
  have hRb : yrR b x = B ^ yrR (log e b) x * yrR (b / e ^ log e b) x + yrR (b % e ^ log e b) x := by
    rw [yrR_dec hbG, heq, ← hBA]
  rcases hkk.lt_or_eq with hlt | heq2
  · have hs1 : log e b + 1 ≤ log e c := add_one_le_of_lt hlt
    have hs1c : log e b + 1 < c := lt_of_le_of_lt hs1 hkc
    have hs1B : log e b + 1 < Tf.tfBG := hs1c.trans hcB
    have hgs : yrG (log e b + 1) < x := yrG_succ (ev_isSuccLimit_of_inE hx) _ gbk
    have hb1 : b < e ^ (log e b + 1) := (lt_opow_iff_log_lt hE1 (he.pos.trans_le (by
      rw [← heq]; exact gl_E_le hbE)).ne').2 (lt_add_one _)
    have hmono : yrR (log e b) x < yrR (log e c) x := hM _ hkc _ hlt gck gbk
    have hbd := yr_bound_of hx hx1 hM hT he hGe heB hge hMe b hbc hbB hgb hbn _
      (lt_of_le_of_lt zero_le (lt_add_one _)).ne' hs1c hs1B hgs hb1
    rw [yrR_succ] at hbd
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
    have hrb' := yr_bound_of hx hx1 hM hT he hGe heB hge hMe r' hr'c (hr'c.trans hcB) gbr (hr'c.trans hcn) k hk
      hkc (hkc.trans hcB) gck hr'
    calc B ^ yrR k x * yrR d' x + yrR r' x < B ^ yrR k x * yrR d' x + B ^ yrR k x :=
          (add_lt_add_iff_left _).2 hrb'
      _ = B ^ yrR k x * (yrR d' x + 1) := by rw [mul_add_one]
      _ ≤ B ^ yrR k x * yrR d x := mul_le_mul_right (add_one_le_of_lt (hM _ hdc _ hd gcd gbd)) _
      _ ≤ _ := le_self_add
  · have hrr : r' < r := by
      have hb' : b = e ^ k * d + r' := by rw [← hd]; exact hdec'.symm
      have hc' : c = e ^ k * d + r := hdec.symm
      have h3 := hbc
      rw [hb', hc'] at h3
      exact (add_lt_add_iff_left _).1 h3
    rw [hd]
    exact (add_lt_add_iff_left _).2 (hM r hrc r' hrr gcr gbr)

theorem yrR_mono {b c : Ordinal.{0}} (hc : c < Tf.tfBG) (hbc : b < c) (hgc : yrG c < x) (hgb : yrG b < x) :
    yrR b x < yrR c x := (yr_mono_top hx hx1 c hc).1 b hbc hgc hgb

theorem yrR_top {c : Ordinal.{0}} (hc : c < Tf.tfBG) (hG : gcG 0 ≤ c) (hg : yrG c < x) :
    yrR c x < eN (yrA (guE c) x) := (yr_mono_top hx hx1 c hc).2 hG hg

theorem yrR_le_mono {b c : Ordinal.{0}} (hc : c < Tf.tfBG) (hbc : b ≤ c) (hgc : yrG c < x) (hgb : yrG b < x) :
    yrR b x ≤ yrR c x := by
  rcases hbc.lt_or_eq with h | rfl
  · exact (yrR_mono hx hx1 hc h hgc hgb).le
  · exact le_rfl

end Mono

end Googology.Trans.PoR.InaccPsi.R2.Yr

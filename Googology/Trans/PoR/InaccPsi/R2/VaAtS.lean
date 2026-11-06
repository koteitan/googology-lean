import Googology.Trans.PoR.InaccPsi.R2.VaCuS

/-!
# VaAtS: THE TOP DATA AT AN ATOM BASE `Γ(j)` PAST ITS SEGMENT BASE `F < j < Γ(j)`

As `Va.VaAt` with `B_Γ` replaced by the segment base `F = vaFB E` read `F(x)` (a closed point, `Va.vs_fix_cl`): the
atom `E = Γ(j)` reads `gq(I(x)) x`, `I(x) = F(x) + o(x)`, `o = j − (F+1)` (`Va.vs_vI`); the codes below `E` read below
it and cofinally (at `o = 0` and at a successor `o` by `Xk.xk_sc_iff`, at a limit `o` the index reading is not closed,
`Va.vs_ncE`, and `Zb.zb_lt_lim_iff`).

* `vs_sub_lt`, `vs_idx_lt`, `vs_at_gate`, `vs_at_I`, `vs_F_cl`, `vs_lt_at`, `vs_ltTat`, `vs_top_at`;
* `vsTopAt` (**THE TOP DATA AT AN ATOM PAST THE SEGMENT BASE**).

No new axiom.  New definition: `vsTopAt`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Googology.Trans.PoR.InaccPsi.R2.Va

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Zb
  Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Zm
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Xk Googology.Trans.PoR.InaccPsi.R2.Gm
  Googology.Trans.PoR.InaccPsi.R2.Ge

theorem vs_sub_lt {F j' j : Ordinal.{0}} (h1 : F + 1 ≤ j') (h : j' < j) :
    j' - (F + 1) < j - (F + 1) := by
  obtain ⟨o', rfl⟩ := exists_add_of_le h1
  obtain ⟨o, rfl⟩ := exists_add_of_le (h1.trans h.le)
  rw [Ordinal.add_sub_cancel, Ordinal.add_sub_cancel]; exact (add_lt_add_iff_left _).1 h

/-- **An atom index past the segment base is below its atom.** -/
theorem vs_idx_lt {E i : Ordinal.{0}} (hBE : tfBG ≤ E) (hi : vaFB E < i) (hiE : gcG i ≤ E) : i < gcG i := by
  have hBi : tfBG ≤ gcG i := (vs_FB_ge hBE).trans (hi.le.trans gcG_strictMono.le_apply)
  rcases vs_atom_cases hBi with h | ⟨-, -, h⟩ | h
  · have hF : vaFB (gcG i) = vaFB E := vs_FB_of_le hBE (hi.le.trans gcG_strictMono.le_apply) hiE
    rw [hF] at h
    exact absurd (h ▸ hi.trans_le gcG_strictMono.le_apply) (lt_irrefl _)
  · rwa [yhJ_gcG] at h
  · exact absurd (yhAt_gcG i) h

section Atom

variable {E : Ordinal.{0}} (hE : InE E) (hBE : tfBG < E) (hEX : E < tlX)
  (hlim : ∀ e, InE e → e < E → eN e < E) (hIH : ∀ e, InE e → tfBG ≤ e → e < E → VsGood e)
  (hA : YhAt E) (hjB : vaFB E < yhJ E) (hjE : yhJ E < E)
  {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)

include hA hjE in
theorem vs_at_E : gcG (yhJ E) = E := by
  obtain ⟨j0, rfl⟩ := yhAt_iff.1 hA; rw [yhJ_gcG]

include hjE in
theorem vs_at_o : yhJ E - (vaFB E + 1) < E := (Ordinal.sub_le_self _ _).trans_lt hjE

include hBE hA hjB hjE hx in
theorem vs_at_gate (hgx : max ω (yrQE E) < x) : yrG (yhJ E) < x ∧ yrG (yhJ E - (vaFB E + 1)) < x := by
  have hωx : ω < x := omega0_lt_inE hx
  have hQ : yrQE E = yrQ (yhJ E) := yrQE_atom hA hjE
  have hgj : yrG (yhJ E) < x := yrG_of_Q hωx (by rw [← hQ]; exact (le_max_right _ _).trans_lt hgx)
  exact ⟨hgj, (vs_off_gate (vs_FB_E hBE.le) (va_G_le_BG.trans (vs_FB_ge hBE.le)) hjB).trans_lt (max_lt hωx hgj)⟩

include hE hBE hEX hlim hIH hA hjB hjE hx hx1

/-- **The index reading of the atom.** -/
theorem vs_at_I (hgx : max ω (yrQE E) < x) :
    vR (vaFB E) x + vR (yhJ E - (vaFB E + 1)) x ∈ Tset x ∧ vR (vaFB E) x + vR (yhJ E - (vaFB E + 1)) x < Om1 ∧
      vR (vaFB E) x + vR (yhJ E - (vaFB E + 1)) x < ywX x := by
  obtain ⟨-, hgo⟩ := vs_at_gate hBE hA hjB hjE hx hgx
  obtain ⟨hoT, ho1, hoX⟩ := vs_T hE hBE hlim hIH hx hx1 (vs_at_o hjE) hgo
  obtain ⟨hDT, -, -, hDX⟩ := vs_xF hE hBE hlim hIH hx hx1 (hjB.trans hjE) hgx
  have hD1 : vR (vaFB E) x < Om1 := hDX.trans (ywX_facts hx hx1).2.2.1
  exact ⟨vzT_add hx hx1 hDT hoT, (inE_indec gl_Om1_E).add_lt hD1 ho1,
    (inE_indec (ywX_facts hx hx1).2.2.2).add_lt hDX hoX⟩

/-- **The segment base reads a closed point.** -/
theorem vs_F_cl (hgx : max ω (yrQE E) < x) : YwClosed x (vR (vaFB E) x) := by
  have hωx : ω < x := omega0_lt_inE hx
  have hFE : vaFB E < E := hjB.trans hjE
  have hfixG := vs_FB_fix hBE.le
  have hOF := vs_FB_gt hBE.le
  have hAF : YhAt (vaFB E) := ⟨vs_FB_SC hBE.le, hOF⟩
  have hiF : ¬ yhJ (vaFB E) < vaFB E := by
    have h := yhJ_gcG (vaFB E); rw [vs_gcG_fix hfixG hOF] at h; rw [h]; exact lt_irrefl _
  have hFX : vaFB E < tlX := hFE.trans hEX
  have hgxF : max ω (yrQE (vaFB E)) < x := (vs_QF_le hE hBE.le).trans_lt hgx
  obtain ⟨h1l, hlF, -, -, -⟩ := vs_fix_data hAF hiF hFX
  have hgl : yrG (tlLev (vaFB E)) < x := (vs_fix_gate_l hAF hiF hFX).trans_lt hgxF
  have hl1 : 1 ≤ vR (tlLev (vaFB E)) x := by
    have h := vs_le_mono hE hBE hlim hIH hx hx1 h1l (hlF.trans hFE)
      (by rw [show (1 : Ordinal.{0}) = ((1 : ℕ) : Ordinal.{0}) by norm_num, va_nat_gate];
          exact (natCast_lt_omega0 1).trans hωx) hgl
    rwa [vR_one] at h
  have h := (vs_fix_cl hx hx1 hAF hiF hFX hgxF (fun c hc hgc =>
    ⟨(vs_T hE hBE hlim hIH hx hx1 (hc.trans hFE) hgc).1, (vs_T hE hBE hlim hIH hx hx1 (hc.trans hFE) hgc).2.1⟩)
    hl1).1
  rwa [← vR_base (vs_FB_E hBE.le) (va_G_le_BG.trans (vs_FB_ge hBE.le))] at h

/-- **Every code below the atom reads below `gq(I(x))`.** -/
theorem vs_lt_at (hgx : max ω (yrQE E) < x) :
    ∀ c, c < E → yrG c < x → vR c x < gq (vR (vaFB E) x + vR (yhJ E - (vaFB E + 1)) x) x := by
  have hωx : ω < x := omega0_lt_inE hx
  have hFE : vaFB E < E := hjB.trans hjE
  obtain ⟨hgj, hgo⟩ := vs_at_gate hBE hA hjB hjE hx hgx
  obtain ⟨hIT, hI1, -⟩ := vs_at_I hE hBE hEX hlim hIH hA hjB hjE hx hx1 hgx
  set I := vR (vaFB E) x + vR (yhJ E - (vaFB E + 1)) x with hIdef
  obtain ⟨hqT, hxq, hq1, hqE, -⟩ := geq_facts hx hx1 hIT hI1
  have hDq : vR (vaFB E) x < gq I x := le_self_add.trans_lt (gmq_gt hx hx1 hIT hI1)
  have hgF : yrG (vaFB E) < x :=
    (vs_FB_gate E hBE.le).trans_lt (by rw [yrG_base hE (va_G_le_BG.trans hBE.le)]; exact hgx)
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg
  by_cases hcB : c < vaFB E
  · exact (vs_mono hE hBE hlim hIH hx hx1 hcB hFE hg hgF).trans hDq
  have hcB' : vaFB E ≤ c := not_lt.1 hcB
  have hGc : gcG 0 ≤ c := va_G_le_BG.trans ((vs_FB_ge hBE.le).trans hcB')
  obtain ⟨-, -, -, -, -, hlog, hmod, hdiv⟩ := gl_parts (yh_gfE_le hGc)
  rw [yrG_dec hGc] at hg
  have hgQE : yrQE (guE c) < x := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hg)
  have hgk : yrG (log (guE c) c) < x :=
    yrG_of_Q hωx ((le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hg))
  have hgd : yrG (c / guE c ^ log (guE c) c) < x :=
    yrG_of_Q hωx ((le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hg))
  have hgr : yrG (c % guE c ^ log (guE c) c) < x := (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hg)
  have heB : vaFB E ≤ guE c := gl_E_max (vs_FB_E hBE.le) (vs_FB_gt hBE.le) hcB'
  have hec : guE c ≤ c := gl_E_le (yh_gfE_le hGc)
  have heE' : guE c < E := hec.trans_lt hc
  have hFe : vaFB (guE c) = vaFB E := vs_FB_of_le hBE.le heB heE'.le
  have hA' : vA (guE c) x < gq I x := by
    rcases vs_atom_cases ((vs_FB_ge hBE.le).trans heB) with hB | ⟨hAc, hjB', hjE'⟩ | hnA
    · rw [hFe] at hB
      rw [hB, ← vR_base (vs_FB_E hBE.le) (va_G_le_BG.trans (vs_FB_ge hBE.le))]; exact hDq
    · -- a smaller atom `Γ(j')`, `F < j' < j`
      rw [vA_atom hAc hjE', vs_vI ((vs_FB_ge hBE.le).trans heB) hjB' hjE'.le, hFe]
      have hj'j : yhJ (guE c) < yhJ E := by
        have h := hec.trans_lt hc
        rw [← vs_at_E hAc hjE', ← vs_at_E hA hjE] at h
        exact gcG_strictMono.lt_iff_lt.1 h
      have hgj' : yrG (yhJ (guE c)) < x := by
        rw [yrQE_atom hAc hjE'] at hgQE; exact yrG_of_Q hωx hgQE
      have hjB'' : vaFB E < yhJ (guE c) := by rw [← hFe]; exact hjB'
      have hgo' := (vs_off_gate (vs_FB_E hBE.le) (va_G_le_BG.trans (vs_FB_ge hBE.le)) hjB'').trans_lt
        (max_lt hωx hgj')
      have hlt := vs_mono hE hBE hlim hIH hx hx1 (vs_sub_lt (Order.add_one_le_of_lt hjB'') hj'j)
        (vs_at_o hjE) hgo' hgo
      exact gmq_lt hx hx1 hIT hI1 ((add_lt_add_iff_left _).2 hlt)
    · rw [vA_psi hnA]
      have hK := yh_lev_lt hGc hnA
      have hI' := yh_idx_lt hGc hnA
      rw [yrQE_psi hnA] at hgQE
      exact xkA_lt hx hx1 hIT hI1 (IH _ hK (hK.trans hc) (yrG_of_Q hωx ((le_max_left _ _).trans_lt hgQE)))
        (IH _ hI' (hI'.trans hc) (yrG_of_Q hωx ((le_max_right _ _).trans_lt hgQE)))
  rw [vR_dec hGc]
  exact (inE_indec hqE).add_lt (InE.mul_lt hqE (zm_opow_lt hqE hA' (IH _ hlog (hlog.trans hc) hgk))
    (IH _ hdiv (hdiv.trans hc) hgd)) (IH _ hmod (hmod.trans hc) hgr)

omit hx hx1 in
/-- The top bound as a function of the base. -/
theorem vs_ltTat : ∀ y, InE y → y < Om1 → max ω (yrQE E) < y → ∀ c, c < E → yrG c < y →
    vR c y < vA E y := by
  intro y hy hy1 hgy c hc hg
  rw [vA_atom hA hjE, vs_vI hBE.le hjB hjE.le]
  exact vs_lt_at hE hBE hEX hlim hIH hA hjB hjE hy hy1 hgy c hc hg

/-- **The readings of the codes below the atom are cofinal in `gq(I(x))`.** -/
theorem vs_top_at (hgx : max ω (yrQE E) < x) :
    ∀ ν, ν < gq (vR (vaFB E) x + vR (yhJ E - (vaFB E + 1)) x) x → ∃ b, b < E ∧ yrG b < x ∧ ν ≤ vR b x := by
  have hωx : ω < x := omega0_lt_inE hx
  have hxl : IsSuccLimit x := ev_isSuccLimit_of_inE hx
  have hEl : IsSuccLimit E := ev_isSuccLimit_of_inE hE
  have hxP : ∀ u v, u < x → v < x → u + v < x := fun u v hu hv => (inE_indec hx).add_lt hu hv
  have hFE : vaFB E < E := hjB.trans hjE
  obtain ⟨hgj, hgo⟩ := vs_at_gate hBE hA hjB hjE hx hgx
  have hoE := vs_at_o hjE
  obtain ⟨hIT, hI1, -⟩ := vs_at_I hE hBE hEX hlim hIH hA hjB hjE hx hx1 hgx
  obtain ⟨hDT, hDE, hxD, hDX⟩ := vs_xF hE hBE hlim hIH hx hx1 hFE hgx
  have hD1 : vR (vaFB E) x < Om1 := hDX.trans (ywX_facts hx hx1).2.2.1
  have hDcl := vs_F_cl hE hBE hEX hlim hIH hA hjB hjE hx hx1 hgx
  have hGE : gcG 0 < E := va_G_le_BG.trans_lt hBE
  have hgB : yrG (vaFB E) < x :=
    (vs_FB_gate E hBE.le).trans_lt (by rw [yrG_base hE (va_G_le_BG.trans hBE.le)]; exact hgx)
  have hgG : yrG (gcG 0) < x := by rw [yrG_G0]; exact hx.pos
  -- the atoms `Γ(F + 1 + b)` below `E`
  have hatom : ∀ b, b < yhJ E - (vaFB E + 1) → yrG b < x →
      gcG (vaFB E + 1 + b) < E ∧ yrG (gcG (vaFB E + 1 + b)) < x ∧
        vR (gcG (vaFB E + 1 + b)) x = gq (vR (vaFB E) x + vR b x) x := by
    intro b hb hgb
    have hjb : vaFB E + 1 + b < yhJ E := by
      have := (add_lt_add_iff_left (vaFB E + 1)).2 hb
      rwa [Ordinal.add_sub_cancel_of_le (Order.add_one_le_of_lt hjB)] at this
    have hbE : gcG (vaFB E + 1 + b) < E := (gcG_lt hjb).trans_eq (vs_at_E hA hjE)
    have hB1 : vaFB E < vaFB E + 1 + b := (lt_add_one _).trans_le le_self_add
    have hii := vs_idx_lt hBE.le hB1 hbE.le
    have hg1 : yrG (vaFB E + 1 + b) < x := by
      have h1 : yrG (1 : Ordinal.{0}) < x := by
        rw [show (1 : Ordinal.{0}) = ((1 : ℕ) : Ordinal.{0}) by norm_num, va_nat_gate]
        exact (natCast_lt_omega0 1).trans hωx
      exact yr_add hxP hωx _ _ (yr_add hxP hωx _ _ hgB h1) hgb
    refine ⟨hbE, by rw [yrG_atom hii]; exact (yrQ_le _).trans_lt hg1, ?_⟩
    rw [vR_atom hii, vs_vI hBE.le hB1 (hjb.trans hjE).le, Ordinal.add_sub_cancel]
  intro ν hν
  by_contra hcon
  push Not at hcon
  set S : Set Ordinal.{0} := {s | ∃ b, b < E ∧ yrG b < x ∧ s = vR b x} with hSdef
  have hSne : S.Nonempty := ⟨vR 0 x, 0, hE.pos, by rw [yrG_zero]; exact hx.pos, rfl⟩
  have hSbdd : BddAbove S := ⟨ν, fun s ⟨b, hb, hg, hs⟩ => hs ▸ (hcon b hb hg).le⟩
  set u := sSup S with hudef
  have hu1 : ∀ b, b < E → yrG b < x → vR b x < u := by
    intro b hb hg
    have h1 : vR (b + 1) x ≤ u := le_csSup hSbdd ⟨b + 1, hEl.add_one_lt hb, yrG_succ hxl b hg, rfl⟩
    rw [vR_succ] at h1
    exact (lt_add_one _).trans_le h1
  have hu2 : u ≤ ν := csSup_le hSne fun s ⟨b, hb, hg, hs⟩ => hs ▸ (hcon b hb hg).le
  have hDu : vR (vaFB E) x < u := hu1 (vaFB E) hFE hgB
  have hxu : x < u := hxD.trans hDu
  -- `u` is strongly critical
  have hSC : SC u := by
    refine ⟨hx.pos.trans hxu, fun a ha b hb => ?_⟩
    obtain ⟨w1, ⟨t1, ht1, hgt1, rfl⟩, hat1⟩ := exists_lt_of_lt_csSup hSne ha
    obtain ⟨w2, ⟨t2, ht2, hgt2, rfl⟩, hbt2⟩ := exists_lt_of_lt_csSup hSne hb
    set t2' := max t2 (gcG 0) with ht2'
    have ht2E : t2' < E := max_lt ht2 hGE
    have hgt2' : yrG t2' < x := by
      rcases le_total t2 (gcG 0) with h | h
      · rw [ht2', max_eq_right h]; exact hgG
      · rw [ht2', max_eq_left h]; exact hgt2
    have hbt2' : b < vR t2' x :=
      hbt2.trans_le (vs_le_mono hE hBE hlim hIH hx hx1 (le_max_left _ _) ht2E hgt2 hgt2')
    have ht10 : t1 ≠ 0 := by rintro rfl; rw [vR_zero] at hat1; exact absurd hat1 (not_lt.2 zero_le)
    have ht11 : 1 ≤ t1 := one_le_iff_ne_zero.2 ht10
    obtain ⟨hT1, h11, -⟩ := vs_T hE hBE hlim hIH hx hx1 ht1 hgt1
    obtain ⟨hT2, h12, -⟩ := vs_T hE hBE hlim hIH hx hx1 ht2E hgt2'
    have hR1 : 1 ≤ vR t1 x := by
      have h := vs_le_mono hE hBE hlim hIH hx hx1 ht11 ht1
        (by rw [show (1 : Ordinal.{0}) = ((1 : ℕ) : Ordinal.{0}) by norm_num, va_nat_gate];
            exact (natCast_lt_omega0 1).trans hωx) hgt1
      rwa [vR_one] at h
    have hGp : gcG 0 < yhPsi t1 t2' := (le_max_right _ _).trans_lt (lt_yhPsi t1 t2')
    have hpE : yhPsi t1 t2' < E := yhPsi_lt_SC hA.1 hA.2 ht1 ht2E
    have hgp : yrG (yhPsi t1 t2') < x := by
      rw [yrG_psi ht11 hGp]; exact max_lt ((yrQ_le _).trans_lt hgt1) ((yrQ_le _).trans_lt hgt2')
    calc veblen a b < veblen a (vR t2' x) := veblen_lt_veblen_iff_right.2 hbt2'
      _ ≤ veblen (vR t1 x) (vR t2' x) := veblen_left_monotone _ hat1.le
      _ ≤ glA (vR t1 x) (vR t2' x) x := glA_veb_le hx hx1 hR1 hT1 h11 hT2 h12
      _ = vR (yhPsi t1 t2') x := (vR_psi ht11 hGp x).symm
      _ < u := hu1 _ hpE hgp
  have hveb : veblen u 0 = u := Xf.xf_sc_veb0 hSC
  rcases zero_or_succ_or_isSuccLimit (yhJ E - (vaFB E + 1)) with ho0 | ⟨o', ho'⟩ | hol
  · -- `o = 0`: the index reading is `F(x)`
    rw [ho0, vR_zero, add_zero] at hν
    obtain ⟨hD1T, hD11⟩ := gl_T_succ hx hx1 hDT hD1
    have hu3 : u < gq (vR (vaFB E) x + 1) x := hu2.trans_lt (hν.trans (gmq_lt hx hx1 hD1T hD11 (lt_add_one _)))
    obtain ⟨c', hc', hc'u⟩ := (xk_sc_iff hx hx1 hDT hD1 hxu hDu hu3).1 hveb
    rcases hc'.lt_or_eq with h | h
    · have := hDcl c' (vz_T_down hx hx1 hDT hD1 hc') h
      rw [hc'u] at this; exact absurd hDu (not_lt.2 this.le)
    · rw [h] at hc'u; rw [← hc'u] at hu2; exact absurd hν (not_lt.2 hu2)
  · -- `o = o' + 1`
    rw [Order.succ_eq_add_one] at ho'
    have ho'o : o' < yhJ E - (vaFB E + 1) := by rw [← ho']; exact lt_add_one o'
    have hgo' : yrG o' < x := (yrG_le_succ o').trans_lt (by rw [ho']; exact hgo)
    obtain ⟨hbE, hgb, hrb⟩ := hatom o' ho'o hgo'
    obtain ⟨ho'T, ho'1, -⟩ := vs_T hE hBE hlim hIH hx hx1 (ho'o.trans hoE) hgo'
    have hcT' : vR (vaFB E) x + vR o' x ∈ Tset x := vzT_add hx hx1 hDT ho'T
    have hc1' : vR (vaFB E) x + vR o' x < Om1 := (inE_indec gl_Om1_E).add_lt hD1 ho'1
    have hcu : gq (vR (vaFB E) x + vR o' x) x < u := by rw [← hrb]; exact hu1 _ hbE hgb
    have hIe : vR (vaFB E) x + vR (yhJ E - (vaFB E + 1)) x = vR (vaFB E) x + vR o' x + 1 := by
      rw [← ho', vR_succ, add_assoc]
    rw [hIe] at hν
    have hu3 : u < gq (vR (vaFB E) x + vR o' x + 1) x := hu2.trans_lt hν
    obtain ⟨c', hc', hc'u⟩ := (xk_sc_iff hx hx1 hcT' hc1' hxu ((gmq_gt hx hx1 hcT' hc1').trans hcu) hu3).1 hveb
    have := gmq_mono hx hx1 hcT' hc1' hc'
    rw [hc'u] at this
    exact absurd hcu (not_lt.2 this)
  · -- a limit `o`: the index reading is a limit and not closed
    obtain ⟨M, hoM, -, hEg, -, hR, hG⟩ := vs_memV hE hBE hEX hlim hIH
      (vs_ltTat hE hBE hEX hlim hIH hA hjB hjE) hoE
    have hGo := vs_memG hωx hEg hgo hG hoM hgo
    have hRl : IsSuccLimit (vR (yhJ E - (vaFB E + 1)) x) := by
      rw [← hR _ hoM x hx hx1 hGo]; exact M.lim _ x hx hx1 hol hoM hGo
    have hIl : IsSuccLimit (vR (vaFB E) x + vR (yhJ E - (vaFB E + 1)) x) := isSuccLimit_add _ hRl
    obtain ⟨σ, -, -, hσI, hIσ⟩ := vs_ncE hE hBE hlim hIH hFE _ x hx hx1 hol hoE (max_lt hgx hgo)
    obtain ⟨ν', hν'I, hνν'⟩ := zb_lt_lim_iff hx hx1 hIl hIT hI1 ⟨σ, hσI, hIσ⟩ ν hν
    rcases lt_or_ge ν' (vR (vaFB E) x) with hν'D | hν'D
    · have h1 := hDcl ν' (vz_T_down hx hx1 hDT hD1 hν'D.le) hν'D
      have h2 := hcon (vaFB E) hFE hgB
      exact absurd (hνν'.trans h1) (not_lt.2 h2.le)
    · obtain ⟨δ, rfl⟩ := exists_add_of_le hν'D
      have hδ : δ < vR (yhJ E - (vaFB E + 1)) x := (add_lt_add_iff_left _).1 hν'I
      obtain ⟨b', hb', hgb', hδb⟩ := vs_below hE hBE hlim hIH hx hx1 hoE hol.bot_lt.ne' hgo δ hδ
      obtain ⟨hbE, hgb, hrb⟩ := hatom b' hb' hgb'
      obtain ⟨hb'T, hb'1, -⟩ := vs_T hE hBE hlim hIH hx hx1 (hb'.trans hoE) hgb'
      have hcT : vR (vaFB E) x + vR b' x ∈ Tset x := vzT_add hx hx1 hDT hb'T
      have hc1 : vR (vaFB E) x + vR b' x < Om1 := (inE_indec gl_Om1_E).add_lt hD1 hb'1
      have h1 : gq (vR (vaFB E) x + δ) x ≤ gq (vR (vaFB E) x + vR b' x) x :=
        gmq_mono hx hx1 hcT hc1 ((add_le_add_iff_left _).2 hδb)
      have h2 := hcon _ hbE hgb
      rw [hrb] at h2
      exact absurd (hνν'.trans_le h1) (not_lt.2 h2.le)

/-- **THE TOP DATA AT AN ATOM PAST THE SEGMENT BASE.** -/
noncomputable def vsTopAt : VsTop E where
  Ei := E
  W := vA E
  E_eq := hA.1.veblen_right (gg_one_lt_of_SC hA.1)
  Ei_cl := fun Z hZ hgZ => by
    have hωZ : ω < Z := omega0_lt_inE (Low.opow_eq_self_of_SC hZ)
    have hgj : yrG (yhJ E) < Z := by
      have hQ : yrQE E = yrQ (yhJ E) := yrQE_atom hA hjE
      exact yrG_of_Q hωZ (by rw [← hQ]; exact (le_max_right _ _).trans_lt hgZ)
    have hj := vs_cl_code hE hBE hEX hlim hIH hZ hjE hgj
    rw [← vs_at_E hA hjE, tf_gcG]
    exact TlCl.gam hZ.1 (TlCl.add (TlCl.add TlCl.om (TlCl.one hZ.1)) hj)
      ((lt_add_one _).trans_le le_self_add)
  V_T := fun x hx hx1 hgx => by
    obtain ⟨hIT, hI1, hIX⟩ := vs_at_I hE hBE hEX hlim hIH hA hjB hjE hx hx1 hgx
    obtain ⟨hqT, -, -, hqE, -⟩ := geq_facts hx hx1 hIT hI1
    rw [vA_atom hA hjE, vs_vI hBE.le hjB hjE.le]
    exact ⟨hqT, hqE, le_self_add.trans (gmq_gt hx hx1 hIT hI1).le, zm_gq_lt_X hx hx1 hIT hI1 hIX⟩
  Vq := fun x hx hx1 hgx => by
    obtain ⟨hIT, hI1, -⟩ := vs_at_I hE hBE hEX hlim hIH hA hjB hjE hx hx1 hgx
    obtain ⟨hsT, hs1⟩ := gl_T_succ hx hx1 hIT hI1
    obtain ⟨-, -, -, hqE, -⟩ := geq_facts hx hx1 hIT hI1
    rw [vA_atom hA hjE, vs_vI hBE.le hjB hjE.le]
    exact ⟨_, hsT, hs1, ((ev_isSuccLimit_of_inE hqE).add_one_lt (gmq_gt hx hx1 hIT hI1)).trans_le le_add_self,
      gmq_lt hx hx1 hsT hs1 (lt_add_one _)⟩
  W_T := fun x hx hx1 hgx => by
    obtain ⟨hIT, hI1, -⟩ := vs_at_I hE hBE hEX hlim hIH hA hjB hjE hx hx1 hgx
    obtain ⟨hqT, -, hq1, -, -⟩ := geq_facts hx hx1 hIT hI1
    rw [vA_atom hA hjE, vs_vI hBE.le hjB hjE.le]
    exact ⟨hqT, hq1, va_eN_gq hx hx1 hIT hI1⟩
  V_pi := fun σ ρ hB hgσ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hgρ := hgσ.trans hB.2.2.1
    have hoE := vs_at_o hjE
    obtain ⟨-, hgo⟩ := vs_at_gate hBE hA hjB hjE hB.1 hgσ
    obtain ⟨M, hoM, -, hEg, -, hR, hG⟩ := vs_memV hE hBE hEX hlim hIH
      (vs_ltTat hE hBE hEX hlim hIH hA hjB hjE) hoE
    have hGo := vs_memG (omega0_lt_inE hB.1) hEg hgo hG hoM hgo
    obtain ⟨e1, e2⟩ := M.ex σ ρ _ hB hoM hGo
    rw [hR _ hoM ρ hB.2.1 hρ1 (hGo.trans hB.2.2.1)] at e1 e2
    rw [hR _ hoM σ hB.1 hσ1 hGo] at e2
    obtain ⟨d1, d2⟩ := vs_Dpi hE hBE hlim hIH (hjB.trans hjE) hB hgσ
    obtain ⟨s1, s2⟩ := pi_add hB d1 e1
    rw [d2, e2] at s2
    obtain ⟨-, hI1ρ, -⟩ := vs_at_I hE hBE hEX hlim hIH hA hjB hjE hB.2.1 hρ1 hgρ
    have h0 : (0 : Ordinal.{0}) < σ := hB.1.pos
    have hq := ywV_pi hB (mem_TB_of_lt hB h0) (h0.trans hσ1) s1 hI1ρ
    rw [ywV_zero, pi_lt hB h0, ywV_zero, s2] at hq
    rw [vA_atom hA hjE, vs_vI hBE.le hjB hjE.le, vA_atom hA hjE, vs_vI hBE.le hjB hjE.le]
    exact hq
  W_pi := fun σ ρ hB hgσ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hgρ := hgσ.trans hB.2.2.1
    have hoE := vs_at_o hjE
    obtain ⟨-, hgo⟩ := vs_at_gate hBE hA hjB hjE hB.1 hgσ
    obtain ⟨M, hoM, -, hEg, -, hR, hG⟩ := vs_memV hE hBE hEX hlim hIH
      (vs_ltTat hE hBE hEX hlim hIH hA hjB hjE) hoE
    have hGo := vs_memG (omega0_lt_inE hB.1) hEg hgo hG hoM hgo
    obtain ⟨e1, e2⟩ := M.ex σ ρ _ hB hoM hGo
    rw [hR _ hoM ρ hB.2.1 hρ1 (hGo.trans hB.2.2.1)] at e1 e2
    rw [hR _ hoM σ hB.1 hσ1 hGo] at e2
    obtain ⟨d1, d2⟩ := vs_Dpi hE hBE hlim hIH (hjB.trans hjE) hB hgσ
    obtain ⟨s1, s2⟩ := pi_add hB d1 e1
    rw [d2, e2] at s2
    obtain ⟨-, hI1ρ, -⟩ := vs_at_I hE hBE hEX hlim hIH hA hjB hjE hB.2.1 hρ1 hgρ
    have h0 : (0 : Ordinal.{0}) < σ := hB.1.pos
    have hq := ywV_pi hB (mem_TB_of_lt hB h0) (h0.trans hσ1) s1 hI1ρ
    rw [ywV_zero, pi_lt hB h0, ywV_zero, s2] at hq
    rw [vA_atom hA hjE, vs_vI hBE.le hjB hjE.le, vA_atom hA hjE, vs_vI hBE.le hjB hjE.le]
    exact hq
  lt := fun x hx hx1 hgx c hc hg => vs_ltTat hE hBE hEX hlim hIH hA hjB hjE x hx hx1 hgx c hc hg
  top := fun x hx hx1 hgx ν hν => by
    rw [vA_atom hA hjE, vs_vI hBE.le hjB hjE.le] at hν
    exact vs_top_at hE hBE hEX hlim hIH hA hjB hjE hx hx1 hgx ν hν
  B_cl := fun Z hZ hgZ => by
    have hgF : yrG (vaFB E) < Z :=
      (vs_FB_gate E hBE.le).trans_lt (by rw [yrG_base hE (va_G_le_BG.trans hBE.le)]; exact hgZ)
    exact vs_cl_code hE hBE hEX hlim hIH hZ (hjB.trans hjE) hgF
  D_T := fun x hx hx1 hgx => vs_xF hE hBE hlim hIH hx hx1 (hjB.trans hjE) hgx
  D_pi := fun σ ρ hB hgσ => vs_Dpi hE hBE hlim hIH (hjB.trans hjE) hB hgσ
  nc := fun c x hx hx1 hl hc hg => vs_ncE hE hBE hlim hIH (hjB.trans hjE) c x hx hx1 hl hc hg

end Atom

end Googology.Trans.PoR.InaccPsi.R2.Va

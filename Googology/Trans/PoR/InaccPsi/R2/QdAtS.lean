import Googology.Trans.PoR.InaccPsi.R2.QdCuS

/-!
# QdAtS: THE TOP DATA AT AN ATOM BASE `Γ(j) ∈ [B₂, B₃)` PAST ITS SEGMENT BASE `F < j < Γ(j)`

As `Qc.QcAtS` from `B₂` on: the segment base `F = vaFB E ≥ B₂` reads a closed point (`Qd.qd_fix_cl`), the atom
`E = Γ(j)` reads `gq(I(x)) x`, `I(x) = F(x) + o(x)`, `o = j − (F+1)` (`Qd.qd_vI`); the codes below `E` read below it
and cofinally.

* `qd_cl_gcG` (**`Γ(c)` is a code with `c`**), `qdA_atX`, `qd_at_E`, `qd_at_o`, `qd_at_gate`, `qd_at_I`, `qd_F_cl`,
  `qd_lt_at`, `qd_ltTat`, `qd_top_at`;
* `qdTopAt` (**THE TOP DATA AT AN ATOM PAST THE SEGMENT BASE**).

No new axiom.  New definition: `qdTopAt`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Googology.Trans.PoR.InaccPsi.R2.Qd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Zb
  Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Zm
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Xk Googology.Trans.PoR.InaccPsi.R2.Gm
  Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Va Googology.Trans.PoR.InaccPsi.R2.Uc
  Googology.Trans.PoR.InaccPsi.R2.Qc

/-- **A base atom `Γ(j) ∈ [X, B₂)`, `j < Γ(j)`, reads `gq(qdRI j)`.** -/
theorem qdA_atX {e : Ordinal.{0}} (hB : e < qdB) (hX : ucB ≤ e) (hA : YhAt e) (hi : yhJ e < e) (x : Ordinal.{0}) :
    qdA e x = gq (qdRI (yhJ e) x) x := by
  unfold qdA; rw [if_pos ⟨hX, hB⟩, if_pos hA, if_pos hi]

/-- **`c` a code ⇒ `Γ(c)` a code** below `B₃` (through `K⁽⁰⁾` for `Z ≤ Ω₁`; above `Ω₁` every point below `θ` is in
`K⁽⁰⁾_{Ω₁}`). -/
theorem qd_cl_gcG (S : InaccSeq.{0}) {Z c : Ordinal.{0}} (hZ : SC Z) (hc : QdCl Z c) (hB : gcG c < qdB) :
    QdCl Z (gcG c) := by
  have hcB : c < qdB := gcG_strictMono.le_apply.trans_lt hB
  have hB3 : gcG c < ConjT.th S := hB.trans_le qd_B3_le_th
  rcases le_or_gt Z Om1 with hZ1 | hZ1
  · exact qd_K0_cl hZ hZ1 _ (qd_K_gcG hZ hZ1 (qd_cl_K0 hZ hZ1 _ hc hcB) hB3) hB
  · have h1 : Ul.UlK S 0 Om1 (gcG c) := by rw [Rj.rj_Om1]; exact Vd.vd_K_th _ hB3
    exact (qd_K0_cl qc_Om1_SC le_rfl _ h1 hB).mono hZ1.le

section Atom

variable (S : InaccSeq.{0}) {E : Ordinal.{0}} (hE : InE E) (hBE : tfBG < E) (hEB : E < qdB) (hXE : ucB ≤ E)
  (hlim : ∀ e, InE e → e < E → eN e < E) (hIH : ∀ e, InE e → tfBG ≤ e → e < E → QdGood e)
  (hA : YhAt E) (hjB : vaFB E < yhJ E) (hjE : yhJ E < E)
  {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)

include hA hjE in
theorem qd_at_E : gcG (yhJ E) = E := by
  obtain ⟨j0, rfl⟩ := yhAt_iff.1 hA; rw [yhJ_gcG]

include hjE in
theorem qd_at_o : yhJ E - (vaFB E + 1) < E := (Ordinal.sub_le_self _ _).trans_lt hjE

include hBE hEB hXE hA hjB hjE hx in
theorem qd_at_gate (hgx : max ω (qdQEt E) < x) : qdGt (yhJ E) < x ∧ qdGt (yhJ E - (vaFB E + 1)) < x := by
  have hωx : ω < x := omega0_lt_inE hx
  have hQ : qdQEt E = qdQt (yhJ E) := qdQEt_atom hXE hEB hA hjE
  have hgj : qdGt (yhJ E) < x := qdGt_of_Q hωx (by rw [← hQ]; exact (le_max_right _ _).trans_lt hgx)
  exact ⟨hgj, (qd_off_gate (vs_FB_E hBE.le) (qd_FB_ge_B2 hXE) (hjE.trans hEB) hjB).trans_lt (max_lt hωx hgj)⟩

include S hE hBE hEB hXE hlim hIH hA hjB hjE hx hx1

/-- **The index reading of the atom.** -/
theorem qd_at_I (hgx : max ω (qdQEt E) < x) :
    vD (vaFB E) x + vD (yhJ E - (vaFB E + 1)) x ∈ Tset x ∧ vD (vaFB E) x + vD (yhJ E - (vaFB E + 1)) x < Om1 ∧
      YBd x (vD (vaFB E) x + vD (yhJ E - (vaFB E + 1)) x) := by
  obtain ⟨-, hgo⟩ := qd_at_gate hBE hEB hXE hA hjB hjE hx hgx
  obtain ⟨hoT, ho1, hoX⟩ := qd_T S hE hBE hEB hlim hIH hx hx1 (qd_at_o hjE) hgo
  obtain ⟨hDT, -, -, hDX⟩ := qd_xF S hE hBE hEB hlim hIH hx hx1 (hjB.trans hjE) hgx
  have hD1 : vD (vaFB E) x < Om1 := yBd_lt hx hx1 hDX
  exact ⟨vzT_add hx hx1 hDT hoT, (inE_indec gl_Om1_E).add_lt hD1 ho1, yBd_add hx hx1 hDX hoX⟩

/-- **The segment base reads a closed point.** -/
theorem qd_F_cl (hgx : max ω (qdQEt E) < x) : YwClosed x (vD (vaFB E) x) := by
  have hωx : ω < x := omega0_lt_inE hx
  have hFE : vaFB E < E := hjB.trans hjE
  have hfixG := vs_FB_fix hBE.le
  have hOF := vs_FB_gt hBE.le
  have hAF : YhAt (vaFB E) := ⟨vs_FB_SC hBE.le, hOF⟩
  have hiF : ¬ yhJ (vaFB E) < vaFB E := by
    have h := yhJ_gcG (vaFB E); rw [vs_gcG_fix hfixG hOF] at h; rw [h]; exact lt_irrefl _
  have hFB : vaFB E < qdB := hFE.trans hEB
  have hXF : ucB ≤ vaFB E := qd_FB_ge_B2 hXE
  have hgxF : max ω (qdQEt (vaFB E)) < x := (qd_QF_le hE hBE.le hEB).trans_lt hgx
  have h := qd_fix_cl S hx hx1 hAF hiF hXF hFB hgxF
    (fun c hc hgc => ⟨(qd_T S hE hBE hEB hlim hIH hx hx1 (hc.trans hFE) hgc).1,
      (qd_T S hE hBE hEB hlim hIH hx hx1 (hc.trans hFE) hgc).2.1⟩)
    (fun b c hbc hc hgb hgc => qd_mono S hE hBE hEB hlim hIH hx hx1 hbc (hc.trans hFE) hgb hgc)
  rwa [← vD_base' (vs_FB_E hBE.le) (va_G_le_BG.trans (vs_FB_ge hBE.le)) hFB] at h

/-- **Every code below the atom reads below `gq(I(x))`.** -/
theorem qd_lt_at (hgx : max ω (qdQEt E) < x) :
    ∀ c, c < E → qdGt c < x → vD c x < gq (vD (vaFB E) x + vD (yhJ E - (vaFB E + 1)) x) x := by
  have hωx : ω < x := omega0_lt_inE hx
  have hFE : vaFB E < E := hjB.trans hjE
  obtain ⟨hgj, hgo⟩ := qd_at_gate hBE hEB hXE hA hjB hjE hx hgx
  obtain ⟨hIT, hI1, -⟩ := qd_at_I S hE hBE hEB hXE hlim hIH hA hjB hjE hx hx1 hgx
  set I := vD (vaFB E) x + vD (yhJ E - (vaFB E + 1)) x with hIdef
  obtain ⟨hqT, hxq, hq1, hqE, -⟩ := geq_facts hx hx1 hIT hI1
  have hDq : vD (vaFB E) x < gq I x := le_self_add.trans_lt (gmq_gt hx hx1 hIT hI1)
  have hgF : qdGt (vaFB E) < x :=
    (qd_FB_gate' hBE.le hEB).trans_lt (by rw [qdGt_base' hE (va_G_le_BG.trans hBE.le) hEB]; exact hgx)
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg
  by_cases hcB : c < vaFB E
  · exact (qd_mono S hE hBE hEB hlim hIH hx hx1 hcB hFE hg hgF).trans hDq
  have hcB' : vaFB E ≤ c := not_lt.1 hcB
  have hGc : gcG 0 ≤ c := va_G_le_BG.trans ((vs_FB_ge hBE.le).trans hcB')
  have hcB2 : c < qdB := hc.trans hEB
  have hXc : ucB ≤ c := (qd_FB_ge_B2 hXE).trans hcB'
  obtain ⟨-, -, -, -, -, hlog, hmod, hdiv⟩ := gl_parts (yh_gfE_le hGc)
  rw [qdGt_dec' hGc hcB2] at hg
  have hgQE : qdQEt (guE c) < x := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hg)
  have hgk : qdGt (log (guE c) c) < x :=
    qdGt_of_Q hωx ((le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hg))
  have hgd : qdGt (c / guE c ^ log (guE c) c) < x :=
    qdGt_of_Q hωx ((le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hg))
  have hgr : qdGt (c % guE c ^ log (guE c) c) < x := (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hg)
  have heB : vaFB E ≤ guE c := gl_E_max (vs_FB_E hBE.le) (vs_FB_gt hBE.le) hcB'
  have hec : guE c ≤ c := gl_E_le (yh_gfE_le hGc)
  have heE' : guE c < E := hec.trans_lt hc
  have hFe : vaFB (guE c) = vaFB E := vs_FB_of_le hBE.le heB heE'.le
  have hXe : ucB ≤ guE c := (qd_FB_ge_B2 hXE).trans heB
  have hA' : qdA (guE c) x < gq I x := by
    rcases vs_atom_cases ((vs_FB_ge hBE.le).trans heB) with hB | ⟨hAc, hjB', hjE'⟩ | hnA
    · rw [hFe] at hB
      rw [hB, ← vD_base' (vs_FB_E hBE.le) (va_G_le_BG.trans (vs_FB_ge hBE.le)) (hFE.trans hEB)]; exact hDq
    · -- a smaller atom `Γ(j')`, `F < j' < j`
      rw [show qdA (guE c) x = gq (qdRI (yhJ (guE c)) x) x by
          unfold qdA; rw [if_pos ⟨hXe, heE'.trans hEB⟩, if_pos hAc, if_pos hjE'],
        qd_vI ((vs_FB_ge hBE.le).trans heB) hjB' hjE'.le, hFe]
      have hj'j : yhJ (guE c) < yhJ E := by
        have h := hec.trans_lt hc
        rw [← qd_at_E hAc hjE', ← qd_at_E hA hjE] at h
        exact gcG_strictMono.lt_iff_lt.1 h
      have hgj' : qdGt (yhJ (guE c)) < x := by
        rw [qdQEt_atom hXe (heE'.trans hEB) hAc hjE'] at hgQE; exact qdGt_of_Q hωx hgQE
      have hjB'' : vaFB E < yhJ (guE c) := by rw [← hFe]; exact hjB'
      have hgo' := (qd_off_gate (vs_FB_E hBE.le) (qd_FB_ge_B2 hXE) ((hjE'.trans heE').trans hEB) hjB'').trans_lt
        (max_lt hωx hgj')
      have hlt := qd_mono S hE hBE hEB hlim hIH hx hx1 (vs_sub_lt (Order.add_one_le_of_lt hjB'') hj'j)
        (qd_at_o hjE) hgo' hgo
      exact gmq_lt hx hx1 hIT hI1 ((add_lt_add_iff_left _).2 hlt)
    · rw [qdA_psi'' (guE_E c) (yh_G_lt_E hGc hnA) (heE'.trans hEB) hnA]
      have hK := yh_lev_lt hGc hnA
      have hI' := yh_idx_lt hGc hnA
      rw [qdQEt_psi' (guE_E c) (yh_G_lt_E hGc hnA) (heE'.trans hEB) hnA] at hgQE
      exact xkA_lt hx hx1 hIT hI1 (IH _ hK (hK.trans hc) (qdGt_of_Q hωx ((le_max_left _ _).trans_lt hgQE)))
        (IH _ hI' (hI'.trans hc) (qdGt_of_Q hωx ((le_max_right _ _).trans_lt hgQE)))
  rw [vD_dec hXc hcB2]
  exact (inE_indec hqE).add_lt (InE.mul_lt hqE (zm_opow_lt hqE hA' (IH _ hlog (hlog.trans hc) hgk))
    (IH _ hdiv (hdiv.trans hc) hgd)) (IH _ hmod (hmod.trans hc) hgr)

omit hx hx1 in
/-- The top bound as a function of the base. -/
theorem qd_ltTat : ∀ y, InE y → y < Om1 → max ω (qdQEt E) < y → ∀ c, c < E → qdGt c < y →
    vD c y < qdA E y := by
  intro y hy hy1 hgy c hc hg
  rw [qdA_atX hEB hXE hA hjE, qd_vI hBE.le hjB hjE.le]
  exact qd_lt_at S hE hBE hEB hXE hlim hIH hA hjB hjE hy hy1 hgy c hc hg

/-- **The readings of the codes below the atom are cofinal in `gq(I(x))`.** -/
theorem qd_top_at (hgx : max ω (qdQEt E) < x) :
    ∀ ν, ν < gq (vD (vaFB E) x + vD (yhJ E - (vaFB E + 1)) x) x → ∃ b, b < E ∧ qdGt b < x ∧ ν ≤ vD b x := by
  have hωx : ω < x := omega0_lt_inE hx
  have hxl : IsSuccLimit x := ev_isSuccLimit_of_inE hx
  have hEl : IsSuccLimit E := ev_isSuccLimit_of_inE hE
  have hxP : ∀ u v, u < x → v < x → u + v < x := fun u v hu hv => (inE_indec hx).add_lt hu hv
  have hFE : vaFB E < E := hjB.trans hjE
  obtain ⟨hgj, hgo⟩ := qd_at_gate hBE hEB hXE hA hjB hjE hx hgx
  have hoE := qd_at_o hjE
  obtain ⟨hIT, hI1, -⟩ := qd_at_I S hE hBE hEB hXE hlim hIH hA hjB hjE hx hx1 hgx
  obtain ⟨hDT, hDE, hxD, hDX⟩ := qd_xF S hE hBE hEB hlim hIH hx hx1 hFE hgx
  have hD1 : vD (vaFB E) x < Om1 := yBd_lt hx hx1 hDX
  have hDcl := qd_F_cl S hE hBE hEB hXE hlim hIH hA hjB hjE hx hx1 hgx
  have hGE : gcG 0 < E := va_G_le_BG.trans_lt hBE
  have hgB : qdGt (vaFB E) < x :=
    (qd_FB_gate' hBE.le hEB).trans_lt (by rw [qdGt_base' hE (va_G_le_BG.trans hBE.le) hEB]; exact hgx)
  have hgG : qdGt (gcG 0) < x := by rw [qdGt_G0]; exact hx.pos
  -- the atoms `Γ(F + 1 + b)` below `E`
  have hatom : ∀ b, b < yhJ E - (vaFB E + 1) → qdGt b < x →
      gcG (vaFB E + 1 + b) < E ∧ qdGt (gcG (vaFB E + 1 + b)) < x ∧
        vD (gcG (vaFB E + 1 + b)) x = gq (vD (vaFB E) x + vD b x) x := by
    intro b hb hgb
    have hjb : vaFB E + 1 + b < yhJ E := by
      have := (add_lt_add_iff_left (vaFB E + 1)).2 hb
      rwa [Ordinal.add_sub_cancel_of_le (Order.add_one_le_of_lt hjB)] at this
    have hbE : gcG (vaFB E + 1 + b) < E := (gcG_lt hjb).trans_eq (qd_at_E hA hjE)
    have hB1 : vaFB E < vaFB E + 1 + b := (lt_add_one _).trans_le le_self_add
    have hii := vs_idx_lt hBE.le hB1 hbE.le
    have hjbB : vaFB E + 1 + b < qdB := (hjb.trans hjE).trans hEB
    have hg1 : qdGt (vaFB E + 1 + b) < x := by
      have h1 : qdGt (1 : Ordinal.{0}) < x := by
        rw [show (1 : Ordinal.{0}) = ((1 : ℕ) : Ordinal.{0}) by norm_num, qdGt_nat]
        exact (natCast_lt_omega0 1).trans hωx
      exact qd_add hxP hωx _ _ hjbB (qd_add hxP hωx _ _ (le_self_add.trans_lt hjbB) hgB h1) hgb
    have hXb : ucB ≤ gcG (vaFB E + 1 + b) :=
      (qd_FB_ge_B2 hXE).trans (hB1.le.trans gcG_strictMono.le_apply)
    refine ⟨hbE, by rw [qdGt_atom' hii (hbE.trans hEB)]; exact (qdQt_le _).trans_lt hg1, ?_⟩
    rw [vD_atom hii hXb (hbE.trans hEB), qd_vI hBE.le hB1 (hjb.trans hjE).le, Ordinal.add_sub_cancel]
  intro ν hν
  by_contra hcon
  push Not at hcon
  set St : Set Ordinal.{0} := {s | ∃ b, b < E ∧ qdGt b < x ∧ s = vD b x} with hSdef
  have hSne : St.Nonempty := ⟨vD 0 x, 0, hE.pos, by rw [qdGt_zero]; exact hx.pos, rfl⟩
  have hSbdd : BddAbove St := ⟨ν, fun s ⟨b, hb, hg, hs⟩ => hs ▸ (hcon b hb hg).le⟩
  set u := sSup St with hudef
  have hu1 : ∀ b, b < E → qdGt b < x → vD b x < u := by
    intro b hb hg
    have h1 : vD (b + 1) x ≤ u := le_csSup hSbdd ⟨b + 1, hEl.add_one_lt hb, qdGt_succ hxl b hg, rfl⟩
    rw [vD_succ] at h1
    exact (lt_add_one _).trans_le h1
  have hu2 : u ≤ ν := csSup_le hSne fun s ⟨b, hb, hg, hs⟩ => hs ▸ (hcon b hb hg).le
  have hDu : vD (vaFB E) x < u := hu1 (vaFB E) hFE hgB
  have hxu : x < u := hxD.trans hDu
  -- `u` is strongly critical
  have hSC : SC u := by
    refine ⟨hx.pos.trans hxu, fun a ha b hb => ?_⟩
    obtain ⟨w1, ⟨t1, ht1, hgt1, rfl⟩, hat1⟩ := exists_lt_of_lt_csSup hSne ha
    obtain ⟨w2, ⟨t2, ht2, hgt2, rfl⟩, hbt2⟩ := exists_lt_of_lt_csSup hSne hb
    set t2' := max t2 (gcG 0) with ht2'
    have ht2E : t2' < E := max_lt ht2 hGE
    have hgt2' : qdGt t2' < x := by
      rcases le_total t2 (gcG 0) with h | h
      · rw [ht2', max_eq_right h]; exact hgG
      · rw [ht2', max_eq_left h]; exact hgt2
    have hbt2' : b < vD t2' x :=
      hbt2.trans_le (qd_le_mono S hE hBE hEB hlim hIH hx hx1 (le_max_left _ _) ht2E hgt2 hgt2')
    have ht10 : t1 ≠ 0 := by rintro rfl; rw [vD_zero] at hat1; exact absurd hat1 (not_lt.2 zero_le)
    have ht11 : 1 ≤ t1 := one_le_iff_ne_zero.2 ht10
    obtain ⟨hT1, h11, -⟩ := qd_T S hE hBE hEB hlim hIH hx hx1 ht1 hgt1
    obtain ⟨hT2, h12, -⟩ := qd_T S hE hBE hEB hlim hIH hx hx1 ht2E hgt2'
    have hR1 : 1 ≤ vD t1 x := by
      have h := qd_le_mono S hE hBE hEB hlim hIH hx hx1 ht11 ht1
        (by rw [show (1 : Ordinal.{0}) = ((1 : ℕ) : Ordinal.{0}) by norm_num, qdGt_nat];
            exact (natCast_lt_omega0 1).trans hωx) hgt1
      rwa [vD_one] at h
    have hGp : gcG 0 < yhPsi t1 t2' := (le_max_right _ _).trans_lt (lt_yhPsi t1 t2')
    have hpE : yhPsi t1 t2' < E := yhPsi_lt_SC hA.1 hA.2 ht1 ht2E
    have hgp : qdGt (yhPsi t1 t2') < x := by
      rw [qdGt_psi' ht11 hGp (hpE.trans hEB)]; exact max_lt ((qdQt_le _).trans_lt hgt1) ((qdQt_le _).trans_lt hgt2')
    calc veblen a b < veblen a (vD t2' x) := veblen_lt_veblen_iff_right.2 hbt2'
      _ ≤ veblen (vD t1 x) (vD t2' x) := veblen_left_monotone _ hat1.le
      _ ≤ glA (vD t1 x) (vD t2' x) x := glA_veb_le hx hx1 hR1 hT1 h11 hT2 h12
      _ = vD (yhPsi t1 t2') x := (vD_psi' ht11 hGp (hpE.trans hEB) x).symm
      _ < u := hu1 _ hpE hgp
  have hveb : veblen u 0 = u := Xf.xf_sc_veb0 hSC
  rcases zero_or_succ_or_isSuccLimit (yhJ E - (vaFB E + 1)) with ho0 | ⟨o', ho'⟩ | hol
  · -- `o = 0`: the index reading is `F(x)`
    rw [ho0, vD_zero, add_zero] at hν
    obtain ⟨hD1T, hD11⟩ := gl_T_succ hx hx1 hDT hD1
    have hu3 : u < gq (vD (vaFB E) x + 1) x := hu2.trans_lt (hν.trans (gmq_lt hx hx1 hD1T hD11 (lt_add_one _)))
    obtain ⟨c', hc', hc'u⟩ := (xk_sc_iff hx hx1 hDT hD1 hxu hDu hu3).1 hveb
    rcases hc'.lt_or_eq with h | h
    · have := hDcl c' (vz_T_down hx hx1 hDT hD1 hc') h
      rw [hc'u] at this; exact absurd hDu (not_lt.2 this.le)
    · rw [h] at hc'u; rw [← hc'u] at hu2; exact absurd hν (not_lt.2 hu2)
  · -- `o = o' + 1`
    rw [Order.succ_eq_add_one] at ho'
    have ho'o : o' < yhJ E - (vaFB E + 1) := by rw [← ho']; exact lt_add_one o'
    have hgo' : qdGt o' < x := (qdGt_le_succ o').trans_lt (by rw [ho']; exact hgo)
    obtain ⟨hbE, hgb, hrb⟩ := hatom o' ho'o hgo'
    obtain ⟨ho'T, ho'1, -⟩ := qd_T S hE hBE hEB hlim hIH hx hx1 (ho'o.trans hoE) hgo'
    have hcT' : vD (vaFB E) x + vD o' x ∈ Tset x := vzT_add hx hx1 hDT ho'T
    have hc1' : vD (vaFB E) x + vD o' x < Om1 := (inE_indec gl_Om1_E).add_lt hD1 ho'1
    have hcu : gq (vD (vaFB E) x + vD o' x) x < u := by rw [← hrb]; exact hu1 _ hbE hgb
    have hIe : vD (vaFB E) x + vD (yhJ E - (vaFB E + 1)) x = vD (vaFB E) x + vD o' x + 1 := by
      rw [← ho', vD_succ, add_assoc]
    rw [hIe] at hν
    have hu3 : u < gq (vD (vaFB E) x + vD o' x + 1) x := hu2.trans_lt hν
    obtain ⟨c', hc', hc'u⟩ := (xk_sc_iff hx hx1 hcT' hc1' hxu ((gmq_gt hx hx1 hcT' hc1').trans hcu) hu3).1 hveb
    have := gmq_mono hx hx1 hcT' hc1' hc'
    rw [hc'u] at this
    exact absurd hcu (not_lt.2 this)
  · -- a limit `o`: the index reading is a limit and not closed
    obtain ⟨M, hoM, -, hEg, -, hR, hG⟩ := qd_memV S hE hBE hEB hlim hIH
      (qd_ltTat S hE hBE hEB hXE hlim hIH hA hjB hjE) hoE
    have hGo := qd_memG hωx hEg hgo hG hoM hgo
    have hRl : IsSuccLimit (vD (yhJ E - (vaFB E + 1)) x) := by
      rw [← hR _ hoM x hx hx1 hGo]; exact M.lim _ x hx hx1 hol hoM hGo
    have hIl : IsSuccLimit (vD (vaFB E) x + vD (yhJ E - (vaFB E + 1)) x) := isSuccLimit_add _ hRl
    obtain ⟨σ, -, -, hσI, hIσ⟩ := qd_ncE S hE hBE hEB hlim hIH hFE _ x hx hx1 hol hoE (max_lt hgx hgo)
    obtain ⟨ν', hν'I, hνν'⟩ := zb_lt_lim_iff hx hx1 hIl hIT hI1 ⟨σ, hσI, hIσ⟩ ν hν
    rcases lt_or_ge ν' (vD (vaFB E) x) with hν'D | hν'D
    · have h1 := hDcl ν' (vz_T_down hx hx1 hDT hD1 hν'D.le) hν'D
      have h2 := hcon (vaFB E) hFE hgB
      exact absurd (hνν'.trans h1) (not_lt.2 h2.le)
    · obtain ⟨δ, rfl⟩ := exists_add_of_le hν'D
      have hδ : δ < vD (yhJ E - (vaFB E + 1)) x := (add_lt_add_iff_left _).1 hν'I
      obtain ⟨b', hb', hgb', hδb⟩ := qd_below S hE hBE hEB hlim hIH hx hx1 hoE hol.bot_lt.ne' hgo δ hδ
      obtain ⟨hbE, hgb, hrb⟩ := hatom b' hb' hgb'
      obtain ⟨hb'T, hb'1, -⟩ := qd_T S hE hBE hEB hlim hIH hx hx1 (hb'.trans hoE) hgb'
      have hcT : vD (vaFB E) x + vD b' x ∈ Tset x := vzT_add hx hx1 hDT hb'T
      have hc1 : vD (vaFB E) x + vD b' x < Om1 := (inE_indec gl_Om1_E).add_lt hD1 hb'1
      have h1 : gq (vD (vaFB E) x + δ) x ≤ gq (vD (vaFB E) x + vD b' x) x :=
        gmq_mono hx hx1 hcT hc1 ((add_le_add_iff_left _).2 hδb)
      have h2 := hcon _ hbE hgb
      rw [hrb] at h2
      exact absurd (hνν'.trans_le h1) (not_lt.2 h2.le)

/-- **THE TOP DATA AT AN ATOM PAST THE SEGMENT BASE.** -/
noncomputable def qdTopAt : QdTop E where
  Ei := E
  W := qdA E
  E_eq := hA.1.veblen_right (gg_one_lt_of_SC hA.1)
  Ei_cl := fun Z hZ hgZ => by
    have hωZ : ω < Z := omega0_lt_inE (Low.opow_eq_self_of_SC hZ)
    have hgj : qdGt (yhJ E) < Z := by
      have hQ : qdQEt E = qdQt (yhJ E) := qdQEt_atom hXE hEB hA hjE
      exact qdGt_of_Q hωZ (by rw [← hQ]; exact (le_max_right _ _).trans_lt hgZ)
    have hj := qd_cl_code S hE hBE hEB hlim hIH hZ hjE hgj
    rw [← qd_at_E hA hjE]
    exact qd_cl_gcG S hZ hj ((qd_at_E hA hjE).trans_lt hEB)
  V_T := fun x hx hx1 hgx => by
    obtain ⟨hIT, hI1, hIX⟩ := qd_at_I S hE hBE hEB hXE hlim hIH hA hjB hjE hx hx1 hgx
    obtain ⟨hqT, -, -, hqE, -⟩ := geq_facts hx hx1 hIT hI1
    rw [qdA_atX hEB hXE hA hjE, qd_vI hBE.le hjB hjE.le]
    exact ⟨hqT, hqE, le_self_add.trans (gmq_gt hx hx1 hIT hI1).le, yBd_gq hx hx1 hIT hIX⟩
  Vq := fun x hx hx1 hgx => by
    obtain ⟨hIT, hI1, -⟩ := qd_at_I S hE hBE hEB hXE hlim hIH hA hjB hjE hx hx1 hgx
    obtain ⟨hsT, hs1⟩ := gl_T_succ hx hx1 hIT hI1
    obtain ⟨-, -, -, hqE, -⟩ := geq_facts hx hx1 hIT hI1
    rw [qdA_atX hEB hXE hA hjE, qd_vI hBE.le hjB hjE.le]
    exact ⟨_, hsT, hs1, ((ev_isSuccLimit_of_inE hqE).add_one_lt (gmq_gt hx hx1 hIT hI1)).trans_le le_add_self,
      gmq_lt hx hx1 hsT hs1 (lt_add_one _)⟩
  W_T := fun x hx hx1 hgx => by
    obtain ⟨hIT, hI1, -⟩ := qd_at_I S hE hBE hEB hXE hlim hIH hA hjB hjE hx hx1 hgx
    obtain ⟨hqT, -, hq1, -, -⟩ := geq_facts hx hx1 hIT hI1
    rw [qdA_atX hEB hXE hA hjE, qd_vI hBE.le hjB hjE.le]
    exact ⟨hqT, hq1, va_eN_gq hx hx1 hIT hI1⟩
  V_pi := fun σ ρ hB hgσ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hgρ := hgσ.trans hB.2.2.1
    have hoE := qd_at_o hjE
    obtain ⟨-, hgo⟩ := qd_at_gate hBE hEB hXE hA hjB hjE hB.1 hgσ
    obtain ⟨M, hoM, -, hEg, -, hR, hG⟩ := qd_memV S hE hBE hEB hlim hIH
      (qd_ltTat S hE hBE hEB hXE hlim hIH hA hjB hjE) hoE
    have hGo := qd_memG (omega0_lt_inE hB.1) hEg hgo hG hoM hgo
    obtain ⟨e1, e2⟩ := M.ex σ ρ _ hB hoM hGo
    rw [hR _ hoM ρ hB.2.1 hρ1 (hGo.trans hB.2.2.1)] at e1 e2
    rw [hR _ hoM σ hB.1 hσ1 hGo] at e2
    obtain ⟨d1, d2⟩ := qd_Dpi S hE hBE hEB hlim hIH (hjB.trans hjE) hB hgσ
    obtain ⟨s1, s2⟩ := pi_add hB d1 e1
    rw [d2, e2] at s2
    obtain ⟨-, hI1ρ, -⟩ := qd_at_I S hE hBE hEB hXE hlim hIH hA hjB hjE hB.2.1 hρ1 hgρ
    have h0 : (0 : Ordinal.{0}) < σ := hB.1.pos
    have hq := ywV_pi hB (mem_TB_of_lt hB h0) (h0.trans hσ1) s1 hI1ρ
    rw [ywV_zero, pi_lt hB h0, ywV_zero, s2] at hq
    rw [qdA_atX hEB hXE hA hjE, qd_vI hBE.le hjB hjE.le, qdA_atX hEB hXE hA hjE, qd_vI hBE.le hjB hjE.le]
    exact hq
  W_pi := fun σ ρ hB hgσ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hgρ := hgσ.trans hB.2.2.1
    have hoE := qd_at_o hjE
    obtain ⟨-, hgo⟩ := qd_at_gate hBE hEB hXE hA hjB hjE hB.1 hgσ
    obtain ⟨M, hoM, -, hEg, -, hR, hG⟩ := qd_memV S hE hBE hEB hlim hIH
      (qd_ltTat S hE hBE hEB hXE hlim hIH hA hjB hjE) hoE
    have hGo := qd_memG (omega0_lt_inE hB.1) hEg hgo hG hoM hgo
    obtain ⟨e1, e2⟩ := M.ex σ ρ _ hB hoM hGo
    rw [hR _ hoM ρ hB.2.1 hρ1 (hGo.trans hB.2.2.1)] at e1 e2
    rw [hR _ hoM σ hB.1 hσ1 hGo] at e2
    obtain ⟨d1, d2⟩ := qd_Dpi S hE hBE hEB hlim hIH (hjB.trans hjE) hB hgσ
    obtain ⟨s1, s2⟩ := pi_add hB d1 e1
    rw [d2, e2] at s2
    obtain ⟨-, hI1ρ, -⟩ := qd_at_I S hE hBE hEB hXE hlim hIH hA hjB hjE hB.2.1 hρ1 hgρ
    have h0 : (0 : Ordinal.{0}) < σ := hB.1.pos
    have hq := ywV_pi hB (mem_TB_of_lt hB h0) (h0.trans hσ1) s1 hI1ρ
    rw [ywV_zero, pi_lt hB h0, ywV_zero, s2] at hq
    rw [qdA_atX hEB hXE hA hjE, qd_vI hBE.le hjB hjE.le, qdA_atX hEB hXE hA hjE, qd_vI hBE.le hjB hjE.le]
    exact hq
  lt := fun x hx hx1 hgx c hc hg => qd_ltTat S hE hBE hEB hXE hlim hIH hA hjB hjE x hx hx1 hgx c hc hg
  top := fun x hx hx1 hgx ν hν => by
    rw [qdA_atX hEB hXE hA hjE, qd_vI hBE.le hjB hjE.le] at hν
    exact qd_top_at S hE hBE hEB hXE hlim hIH hA hjB hjE hx hx1 hgx ν hν
  B_cl := fun Z hZ hgZ => by
    have hgF : qdGt (vaFB E) < Z :=
      (qd_FB_gate' hBE.le hEB).trans_lt (by rw [qdGt_base' hE (va_G_le_BG.trans hBE.le) hEB]; exact hgZ)
    exact qd_cl_code S hE hBE hEB hlim hIH hZ (hjB.trans hjE) hgF
  D_T := fun x hx hx1 hgx => qd_xF S hE hBE hEB hlim hIH hx hx1 (hjB.trans hjE) hgx
  D_pi := fun σ ρ hB hgσ => qd_Dpi S hE hBE hEB hlim hIH (hjB.trans hjE) hB hgσ
  nc := fun c x hx hx1 hl hc hg => qd_ncE S hE hBE hEB hlim hIH (hjB.trans hjE) c x hx hx1 hl hc hg

end Atom

end Googology.Trans.PoR.InaccPsi.R2.Qd

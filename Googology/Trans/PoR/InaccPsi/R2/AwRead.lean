import Googology.Trans.PoR.InaccPsi.R2.AwSys

/-!
# AwRead: THE READINGS OF THE CODES BELOW `K_ω`

`Θ_y(c) = gxTh y (awAt S y) c` for a strongly critical `y < Ω₁`, `x = awNx y` the next `υ`-point (`Tʸ ∩ Ω₁ = x`), `m = awNx x`:

* `aw_code_th`, `aw_Rd_qt` (below `θ` the atoms are those of `Qt.qtU`), `aw_Rd_xi` (**below `θ`, `Θ_y = R_y`**);
* `aw_Rd_th` (**`Θ_y(θ) = x`**);
* `aw_read` (**THE ATOM LAW**: `Θ_y(ψ_{Ω₂}(Ω_ω + d)) = ϑˣ(Ω₁·Ω₁ + (-1 + Θ_y(d)))` for a code `0 < d < K_ω`, and every atom
  reads below `m`); by `Lq.lq_sq_min` from below and `mxGx_bound` from above;
* `aw_Rd_lt` (**every code below `K_ω` reads below `m`**).

No new axiom.  New definitions: `awNx`, `awG`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Aw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Zb
  Googology.Trans.PoR.InaccPsi.R2.Zr Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Xi
  Googology.Trans.PoR.InaccPsi.R2.Cp

variable {S : InaccSeq.{0}}

/-- The next `υ`-point above `y`. -/
noncomputable def awNx (y : Ordinal.{0}) : Ordinal.{0} := sInf {u | y < u ∧ UpsPt u}

/-- **`ϑˣ(Ω₁·Ω₁ + (-1 + w))`.** -/
noncomputable def awG (x w : Ordinal.{0}) : Ordinal.{0} := vt x (Om1 * Om1 + cdOff w)

/-- `1 + (-1 + w) = w` for `w ≥ 1`. -/
theorem aw_one_add_off {w : Ordinal.{0}} (h1 : 1 ≤ w) : 1 + cdOff w = w := by
  unfold cdOff
  split_ifs with h
  · exact Ordinal.add_sub_cancel_of_le h1
  · exact one_add_of_omega0_le (not_lt.1 h)

/-- `-1 + (1 + σ) = σ`. -/
theorem aw_off_one_add (σ : Ordinal.{0}) : cdOff (1 + σ) = σ := by
  rcases lt_or_ge σ ω with h | h
  · have h' : 1 + σ < ω := isPrincipal_add_omega0 one_lt_omega0 h
    unfold cdOff
    rw [if_pos h']
    exact Ordinal.add_sub_cancel _ _
  · rw [one_add_of_omega0_le h]
    exact cpOff_of_ge h

theorem aw_one_add_lt {σ w : Ordinal.{0}} (h1 : 1 ≤ w) (h : σ < cdOff w) : 1 + σ < w := by
  have := (add_lt_add_iff_left (1 : Ordinal.{0})).2 h
  rwa [aw_one_add_off h1] at this

section Nx

variable {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om1)
include hy hy1

/-- **The next `υ`-point**: `Tʸ ∩ Ω₁`, strongly critical. -/
theorem awNx_facts : y < awNx y ∧ UpsPt (awNx y) ∧ SC (awNx y) ∧ awNx y < Om1 ∧
    (∀ a, a < Om1 → (a ∈ Tset y ↔ a < awNx y)) ∧ IsNext y (awNx y) := by
  have hyE : InE y := Low.opow_eq_self_of_SC hy
  obtain ⟨m, hym, hmL, hmin, hT, hm1⟩ := T_next (Or.inr hyE) hy1
  obtain ⟨m', -, -, hmS, hmin', hT', -⟩ := xi_next hyE hy1
  have hmU : UpsPt m := ⟨lt_of_le_of_lt zero_le hym, hmL⟩
  have hmm' : m = m' := le_antisymm
    (not_lt.1 fun h => absurd ((hT' m' (h.trans hm1)).1 ((hT m' (h.trans hm1)).2 h)) (lt_irrefl _))
    (hmin' m hym hmU)
  have he : awNx y = m := le_antisymm (csInf_le' ⟨hym, hmU⟩)
    (le_csInf ⟨m, hym, hmU⟩ fun u hu => hmin u hu.1 hu.2.2)
  rw [he]
  exact ⟨hym, hmU, hmm' ▸ hmS, hm1, hT, hym, hmU, fun u hu hU => hmin u hu hU.2⟩

end Nx

/-! ## Below `θ` -/

/-- Below `θ` the codes over the atoms `awAt` are the codes over the atoms `Qt.qtAt`. -/
theorem aw_code_th {y c : Ordinal.{0}} (hc : c < ConjT.th S) :
    GxCl y (awAt S y) c ↔ GxCl y (Qt.qtAt S y) c := by
  constructor
  · intro h
    induction h with
    | small h => exact GxCl.small h
    | om => exact GxCl.om
    | @atom s hs => exact GxCl.atom (show s ∈ Qt.qtAt S y from ⟨hs.1, hs.2.1, hc, hs.2.2.2⟩)
    | add _ _ ihx ihy => exact GxCl.add (ihx (le_self_add.trans_lt hc)) (ihy (le_add_self.trans_lt hc))
    | @phi a b _ _ ihx ihy =>
      exact GxCl.phi (ihx ((left_le_veblen a b).trans_lt hc)) (ihy ((right_le_veblen a b).trans_lt hc))
  · intro h
    exact h.mono le_rfl fun s hs => (show s ∈ awAt S y from ⟨hs.1, hs.2.1, hs.2.2.1.trans aw_th_lt_V, hs.2.2.2⟩)

/-- Below `θ` the readings with the atoms `awAt` are those with the atoms `Qt.qtAt`. -/
theorem aw_Rd_qt {y c : Ordinal.{0}} (hc : c ≤ ConjT.th S) :
    gxTh y (awAt S y) c = gxTh y (Qt.qtAt S y) c :=
  Gg.ggOtp_congr c fun _ hd => aw_code_th (hd.trans_le hc)

/-- **Below `θ`, `Θ_y = R_y`.** -/
theorem aw_Rd_xi {y c : Ordinal.{0}} (hy : SC y) (hy1 : y < Om1) (hc : WDom S y c) :
    gxTh y (awAt S y) c = xiR y c := by
  have hyθ : y < ConjT.th S := hy1.trans (by rw [Rj.rj_Om1]; exact Vd.vd_Om1_lt_B.trans Vd.vd_B_lt_th)
  have hcθ : c < ConjT.th S := by
    rcases hc with h | ⟨-, h, -⟩
    · exact h.trans hyθ
    · exact h
  rw [aw_Rd_qt hcθ.le, xiR_gx hy hy1 c hc]

/-- **`Θ_y(θ)` is the next `υ`-point.** -/
theorem aw_Rd_th {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om1) : gxTh y (awAt S y) (ConjT.th S) = awNx y := by
  have hyE : InE y := Low.opow_eq_self_of_SC hy
  obtain ⟨-, -, -, hm1, hT, -⟩ := awNx_facts hy hy1
  rw [aw_Rd_qt le_rfl]
  refine le_antisymm (le_of_forall_lt fun v hv => ?_) (le_of_forall_lt fun v hv => ?_)
  · obtain ⟨c, hc, hcθ, rfl⟩ := gxTh_onto hv
    have hd := (xi_dom_codes hy hy1 hcθ).1 hc
    rw [xiR_gx hy hy1 c hd]
    obtain ⟨hRT, hR1⟩ := xiR_T S hyE hy1 c hd
    exact (hT _ hR1).1 hRT
  · have hv1 := hv.trans hm1
    obtain ⟨c, hd, rfl⟩ := xiR_onto S hyE hy1 v ((hT v hv1).2 hv) hv1
    have hyθ : y < ConjT.th S := hy1.trans (by rw [Rj.rj_Om1]; exact Vd.vd_Om1_lt_B.trans Vd.vd_B_lt_th)
    have hcθ : c < ConjT.th S := by
      rcases hd with h | ⟨-, h, -⟩
      · exact h.trans hyθ
      · exact h
    rw [← xiR_gx hy hy1 c hd]
    exact gxTh_lt ((xi_dom_codes hy hy1 hcθ).2 hd) hcθ

/-! ## The atom law -/

/-- **THE ATOM LAW**: every atom over `y` reads below `m`, and an atom `ψ_{Ω₂}(Ω_ω + d)`, `d > 0` a code, reads
`ϑˣ(Ω₁·Ω₁ + (-1 + Θ_y(d)))`. -/
theorem aw_read {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om1) :
    ∀ s, s ∈ awAt S y → gxTh y (awAt S y) s < awNx (awNx y) ∧
      ∀ d, s = S.psi (Om ω + d) (Om (1 + 1)) → 0 < d → GxCl y (awAt S y) d →
        gxTh y (awAt S y) s = awG (awNx y) (gxTh y (awAt S y) d) := by
  obtain ⟨hyx, -, hxS, hx1, -, -⟩ := awNx_facts hy hy1
  obtain ⟨hxm, -, hmS, hm1, hTm, -⟩ := awNx_facts hxS hx1
  set x := awNx y with hx
  set m := awNx x with hm
  have hy1' : y < Om 1 := by rw [← Rj.rj_Om1]; exact hy1
  have hy1le : y ≤ Om 1 := hy1'.le
  have hAt : GxAt (awAt S y) := (awU S).gxAt y
  have hθx : gxTh y (awAt S y) (ConjT.th S) = x := aw_Rd_th hy hy1
  intro s
  induction s using WellFoundedLT.induction with
  | ind s IH =>
  intro hs
  have hL : ∀ c, GxCl y (awAt S y) c → c < s → gxTh y (awAt S y) c < m := fun c hc hcs =>
    mxGx_bound hy hy1' hAt hmS (hyx.trans hxm) (fun t ht hts => (IH t hts ht).1) c hc hcs
  have hF : ∀ d, s = S.psi (Om ω + d) (Om (1 + 1)) → 0 < d → GxCl y (awAt S y) d →
      gxTh y (awAt S y) s = awG x (gxTh y (awAt S y) d) := by
    intro d hsd hd0 hdc
    have hV : S.psi (Om ω + d) (Om (1 + 1)) < awV S := hsd ▸ hs.2.2.1
    have hds : d < s := by rw [hsd]; exact aw_lt_atom hV
    have hw0 : 0 < gxTh y (awAt S y) d := by
      have := gxTh_lt (Z := y) (At := awAt S y) (GxCl.zero hy.1) hd0
      rwa [gxTh_zero] at this
    have hw1 : 1 ≤ gxTh y (awAt S y) d := Order.one_le_iff_pos.2 hw0
    have hwm := hL d hdc hds
    have hηle : cdOff (gxTh y (awAt S y) d) ≤ gxTh y (awAt S y) d := cdOff_le _
    have hηm : cdOff (gxTh y (awAt S y) d) < m := hηle.trans_lt hwm
    have hηΩ : cdOff (gxTh y (awAt S y) d) < Om1 := hηm.trans hm1
    have hηT : cdOff (gxTh y (awAt S y) d) ∈ Tset x := (hTm _ hηΩ).2 hηm
    obtain ⟨-, -, -, hxX, -, -, -⟩ := Lq.lq_sq_facts hxS hx1 hηT hηΩ
    have hXS := Lq.lq_sq_SC hxS hx1 hηT hηΩ
    have hθs : ConjT.th S < s := by
      rw [hsd]
      exact psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right _ hd0) (Zj.zjOmW_own d)
    unfold awG
    apply le_antisymm
    · refine le_of_forall_lt fun v hv => ?_
      obtain ⟨c, hc, hcs, rfl⟩ := gxTh_onto hv
      refine mxGx_bound hy hy1' hAt hXS (hyx.trans hxX) (fun t ht hts => ?_) c hc hcs
      rcases lt_or_ge (ConjT.th S) t with hθt | htθ
      · obtain ⟨d', hd'0, -, -, hd'c, e⟩ := aw_atom_form hy hy1le ht hθt
        have hd'd : d' < d := by
          have h1 : S.psi (Om ω + d') (Om (1 + 1)) < S.psi (Om ω + d) (Om (1 + 1)) := by
            rw [← e, ← hsd]; exact hts
          exact (add_lt_add_iff_left _).1 (zrArg_lt h1)
        rw [(IH t hts ht).2 d' e hd'0 hd'c]
        unfold awG
        have hw' : gxTh y (awAt S y) d' < gxTh y (awAt S y) d := gxTh_lt hd'c hd'd
        have hw'0 : 0 < gxTh y (awAt S y) d' := by
          have := gxTh_lt (Z := y) (At := awAt S y) (GxCl.zero hy.1) hd'0
          rwa [gxTh_zero] at this
        have hlt : cdOff (gxTh y (awAt S y) d') < cdOff (gxTh y (awAt S y) d) :=
          cpOff_lt (Order.one_le_iff_pos.2 hw'0) hw'
        have hσm : cdOff (gxTh y (awAt S y) d') < m := hlt.trans hηm
        exact Lq.lq_sq_lt hxS hx1 ((hTm _ (hσm.trans hm1)).2 hσm) hηT hηΩ hlt
      · have h1 : gxTh y (awAt S y) t ≤ x := by
          rw [← hθx]; exact gxTh_mono htθ
        exact h1.trans_lt hxX
    · refine Lq.lq_sq_min hxS hx1 hηT hηΩ (gxTh_SC hy hAt hs.1 (hy1'.trans hs.2.1)) ?_ ?_ ?_
      · rw [← hθx]; exact gxTh_lt (GxCl.atom (aw_th_mem y)) hθs
      · exact hηle.trans_lt (gxTh_lt hdc hds)
      · intro σ hσ
        have hlt := aw_one_add_lt hw1 hσ
        obtain ⟨d', hd'c, hd'd, e⟩ := gxTh_onto hlt
        have hd'0 : 0 < d' := by
          rcases eq_or_ne d' 0 with rfl | h
          · rw [gxTh_zero] at e
            exact absurd e.symm (by
              have : (0 : Ordinal.{0}) < 1 + σ := lt_of_lt_of_le zero_lt_one le_self_add
              exact this.ne')
          · exact pos_iff_ne_zero.2 h
        obtain ⟨j, hj⟩ := aw_lt_V_iff.1 (aw_arg_lt_V hV)
        have hts : S.psi (Om ω + d') (Om (1 + 1)) < s := by rw [hsd]; exact zrAtom_lt hj hd'd
        have htV : S.psi (Om ω + d') (Om (1 + 1)) < awV S := hts.trans hs.2.2.1
        have htAt := aw_atom_mem hd'c htV
        have hIH := (IH _ hts htAt).2 d' rfl hd'0 hd'c
        rw [e] at hIH
        unfold awG at hIH
        rw [aw_off_one_add] at hIH
        rw [← hIH]
        exact gxTh_lt (GxCl.atom htAt) hts
  refine ⟨?_, hF⟩
  rcases lt_or_ge (ConjT.th S) s with hθs | hsθ
  · obtain ⟨d, hd0, hds, -, hdc, e⟩ := aw_atom_form hy hy1le hs hθs
    rw [hF d e hd0 hdc]
    unfold awG
    have hwm := hL d hdc hds
    have hηm : cdOff (gxTh y (awAt S y) d) < m := (cdOff_le _).trans_lt hwm
    have hηΩ := hηm.trans hm1
    obtain ⟨-, -, hvT, -, hv1, -, -⟩ := Lq.lq_sq_facts hxS hx1 ((hTm _ hηΩ).2 hηm) hηΩ
    exact (hTm _ hv1).1 hvT
  · have h1 : gxTh y (awAt S y) s ≤ x := by
      rw [← hθx]; exact gxTh_mono hsθ
    exact h1.trans_lt hxm

/-- **Every code below `K_ω` reads below `m`.** -/
theorem aw_Rd_lt {y c : Ordinal.{0}} (hy : SC y) (hy1 : y < Om1) (hc : GxCl y (awAt S y) c) :
    gxTh y (awAt S y) c < awNx (awNx y) := by
  obtain ⟨hyx, -, hxS, hx1, -, -⟩ := awNx_facts hy hy1
  obtain ⟨hxm, -, hmS, -, -, -⟩ := awNx_facts hxS hx1
  have hy1' : y < Om 1 := by rw [← Rj.rj_Om1]; exact hy1
  exact mxGx_bound hy hy1' ((awU S).gxAt y) hmS (hyx.trans hxm) (fun t ht _ => (aw_read hy hy1 t ht).1) c hc
    (lt_add_one c)

end Googology.Trans.PoR.InaccPsi.R2.Aw

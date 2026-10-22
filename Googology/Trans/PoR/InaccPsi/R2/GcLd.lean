import Googology.Trans.PoR.InaccPsi.R2.GcAt

/-!
# The ladder over a base, with the codes of `R2.GcAt`: terms for every code below the stage tops

`R2.GbLd` with the codes `GxCl Z gcAt` (one atom `Γ_{Ω₁+1+α}` for every `α < ε₀`) and the bound `Γ_{Ω₁+ε₀}`; the
codes `bQ`, `cQ`, `cQs` of the stage tops are those of `R2.GaLad`:

* `gccQ_cl` (the stage codes are codes), `gcNotNoB` (a term that reads a level code `a ≥ Ω₁` at every strongly critical
  `y ≥ Z` is not base-free: some atom `gcG α > a` has a strongly critical reading);
* `gcTop_th` (**`gP n y = Θ_y(cQ c n)`**), `gcPoly` (**`GcPoly (lpSys B n) (cQ c n)` for every `n`**, given `GcPoly K c`
  and `E_K(y) = Θ_y(c)`; `c` may be strongly critical).

No new axiom.
-/
set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gc

open Googology.Trans.PoR.InaccPsi.R2.Ga
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph Googology.Trans.PoR.InaccPsi.R2.Xt Lu
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Lp

theorem gccQ_cl {c : Ordinal.{0}} (hc : ∀ Z, SC Z → GxCl Z gcAt c) {Z : Ordinal.{0}} (hZ : SC Z) :
    ∀ n : ℕ, GxCl Z gcAt (cQ c n)
  | 0 => hc Z hZ
  | n + 1 => GxCl.phi (gccQ_cl hc hZ n) (GxCl.small (bQ_lt hZ _))

/-! ## A level code is not read by a base-free term -/

/-- **A term that reads a level code `a ≥ Ω₁` at every strongly critical `y ≥ Z` is not base-free.** -/
theorem gcNotNoB {B : LpB} {Z a : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z < Om 1)
    (ha : GxCl Z gcAt a) (haO : Om 1 ≤ a) {l : LpT B}
    (hl : ∀ y, SC y → y < Om 1 → Z ≤ y → LpT.val l y = gxTh y gcAt a) : ¬ LpT.noB l := by
  intro hn
  have hAt := gcAt_GxAt
  have haW : a < gcV := gcCl_lt_V hZ1.le ha
  obtain ⟨k, hkε, hk⟩ := gcG_lt_of_lt_limit gc_eps0_lim haW
  obtain ⟨hYS, hZY, hY1⟩ := gcTh_G hZ hZ1 k hkε
  have hlt : gxTh Z gcAt a < gxTh Z gcAt (gcG k) := gxTh_lt ha hk
  have hge : gxTh Z gcAt (gcG k) ≤ gxTh (gxTh Z gcAt (gcG k)) gcAt a := by
    have := gxTh_mono (Z := gxTh Z gcAt (gcG k)) (At := gcAt) haO
    rwa [gxTh_Om1 hYS hY1 hAt] at this
  have e := LpT.noB_val l hn Z (gxTh Z gcAt (gcG k))
  rw [hl Z hZ hZ1 le_rfl, hl _ hYS hY1 hZY.le] at e
  exact absurd (e ▸ hlt) (not_lt.2 hge)

/-! ## The readings of the stage tops and the terms for the codes -/

section Poly

variable (S : InaccSeq.{0}) {B : LpB} {c : Ordinal.{0}} (hc : ∀ Z, SC Z → GxCl Z gcAt c) (hcO : Om 1 ≤ c)
  (hKE : ∀ y, SC y → y < Om 1 → B.K.E y = gxTh y gcAt c)
include S hc hcO hKE

omit hcO in
/-- **`gP n y = Θ_y(cQ c n)`** at every strongly critical `y < Ω₁`. -/
theorem gcTop_th : ∀ n : ℕ, ∀ y, SC y → y < Om 1 → gP B n y = gxTh y gcAt (cQ c n)
  | 0, y, hy, hy1 => hKE y hy hy1
  | n + 1, y, hy, hy1 => by
      have hAt := gcAt_GxAt
      have hyE := gg_SC_eps hy
      have hy1' := lp_y1 hy1
      have ih := gcTop_th n y hy hy1
      have hcn := gccQ_cl hc hy n
      have hbn : GxCl y gcAt (bQ (cQ c n)) := GxCl.small (bQ_lt hy _)
      show vt y (Om1 * gP B n y) = gxTh y gcAt (veblen (cQ c n) (bQ (cQ c n)))
      rw [gxTh_phi hy hAt _ hcn _ hbn, gxTh_small (bQ_lt hy _).le, ← ih]
      obtain ⟨hβT, hyβ, hβ1, -⟩ := gP_facts B hyE hy1' n
      have hβ1' : 1 ≤ gP B n y := (Lu.lu_one_lt_E hyE).le.trans hyβ.le
      by_cases hS : veblen (cQ c n) 0 = cQ c n
      · rw [bQ_of hS]
        have hβS : veblen (gP B n y) 0 = gP B n y := by
          have := congrArg (gxTh y gcAt) hS
          rw [gxTh_phi hy hAt _ hcn _ (GxCl.zero hy.1), gxTh_zero, ← ih] at this
          exact this
        have h0 : lpInd (gP B n y) y 1 = 0 := by
          have := lpInd_low_eq (β := gP B n y) (y := y) (δ := 0) (Or.inr ⟨hβS, hyβ.le⟩)
            (fun z hz => absurd hz (not_lt.2 zero_le))
          rwa [add_zero] at this
        have hnP : ¬ LuP (gP B n y + 1) 1 := by
          have h := lu_P_nat_not (β := gP B n y) 0 0
          have e : (0 : Ordinal.{0}) + 1 + ((0 : ℕ) : Ordinal.{0}) = 1 := by simp
          rwa [e] at h
        have hy1v : y < veblen (gP B n y) 1 :=
          hyβ.trans (lt_of_eq_of_lt hβS.symm (veblen_lt_veblen_iff_right.2 zero_lt_one))
        have e := lpPhLev hy hy1' hβ1' hβT hβ1 1 hy1v (lp_lvl_lt zero_lt_one) hnP
          (by rw [h0]; exact mem_T_of_le hyE hy1' zero_le) (by rw [h0]; exact Ordinal.omega_pos 1)
        rw [e, h0, add_zero]
      · rw [bQ_of_not hS]
        have hβv : gP B n y < veblen (gP B n y) 0 := by
          have := gxTh_lt hcn (lt_of_le_of_ne (left_le_veblen (cQ c n) 0) (Ne.symm hS)) (At := gcAt)
          rwa [gxTh_phi hy hAt _ hcn _ (GxCl.zero hy.1), gxTh_zero, ← ih] at this
        have h0 : lpInd (gP B n y) y 0 = 0 := ggOtp_zero _
        have hnP : ¬ LuP (gP B n y + 1) 0 := by
          rintro ⟨j, hj⟩
          exact absurd hj (gg_veblen_eps (x := gP B n y + 1) (y := j)
            (by simp) ▸ (Ordinal.opow_pos _ omega0_pos)).ne'
        have e := lpPhLev hy hy1' hβ1' hβT hβ1 0 (hyβ.trans hβv) hβv hnP
          (by rw [h0]; exact mem_T_of_le hyE hy1' zero_le) (by rw [h0]; exact Ordinal.omega_pos 1)
        rw [e, h0, add_zero]

/-- **`lpSys B n` has terms for every code below `cQ c n`** (given the terms of `K` for the codes below `c`). -/
theorem gcPoly (hKP : GcPoly B.K.sys c) : ∀ n : ℕ, GcPoly (lpSys B n) (cQ c n) := by
  have hAt := gcAt_GxAt
  have hKterm : ∀ (n : ℕ) (Z d : Ordinal.{0}), GxCl Z gcAt d → d < c → ∃ s : (lpSys B n).Tm, ∀ y, SC y → y < Om 1 →
      Z ≤ y → (lpSys B n).CB s y ∧ (lpSys B n).val s y = gxTh y gcAt d := by
    intro n Z d hd hdc
    obtain ⟨k, hk⟩ := hKP Z d hd hdc
    exact ⟨LpT.ak k, fun y hy hy1 hZy => ⟨⟨(hk y hy hy1 hZy).1, Nat.zero_le n⟩, (hk y hy hy1 hZy).2⟩⟩
  intro n
  induction n with
  | zero => exact fun Z d hd hdc => hKterm 0 Z d hd hdc
  | succ n ihn =>
    refine gcPoly_of_SC fun Z hZ hZ1 => ?_
    intro d
    induction d using WellFoundedLT.induction with
    | ind d IH =>
    intro hd hdB
    rcases lt_trichotomy d c with hdc | rfl | hcd
    · exact hKterm (n + 1) Z d hd hdc
    · exact ⟨LpT.tp, fun y hy hy1 _ => ⟨⟨trivial, by simp [LpT.stage]⟩, hKE y hy hy1⟩⟩
    have hd1 : Om 1 < d := hcO.trans_lt hcd
    have hd0 : d ≠ 0 := (lt_of_le_of_lt zero_le hd1).ne'
    obtain ⟨hsub, hlog⟩ := gxDec hZ hAt d hd
    have hw : GxCl Z gcAt (ω ^ log ω d) := GxCl.opow hZ.1 hlog
    have hwd : ω ^ log ω d ≤ d := opow_log_le_self ω hd0
    rcases hwd.lt_or_eq with hwd' | hwd'
    · have hr := hsub _ hw hwd
      have hdr : ω ^ log ω d + (d - ω ^ log ω d) = d := Ordinal.add_sub_cancel_of_le hwd
      have hrd : d - ω ^ log ω d < d := by
        rcases (Ordinal.sub_le_self d (ω ^ log ω d)).lt_or_eq with h | h
        · exact h
        · exfalso
          have h1 : ω ^ log ω d + d = d := by conv_rhs => rw [← hdr]
                                              rw [h]
          have h2 := add_eq_right_iff_mul_omega0_le.1 h1
          rw [← opow_succ] at h2
          exact absurd (lt_opow_succ_log_self one_lt_omega0 d) (not_lt.2 h2)
      obtain ⟨s1, hs1⟩ := IH _ hwd' hw (hwd'.trans hdB)
      obtain ⟨s2, hs2⟩ := IH _ hrd hr (hrd.trans hdB)
      refine ⟨LpT.sm s1 s2, fun y hy hy1 hZy => ?_⟩
      obtain ⟨c1, v1⟩ := hs1 y hy hy1 hZy
      obtain ⟨c2, v2⟩ := hs2 y hy hy1 hZy
      refine ⟨⟨⟨c1.1, c2.1⟩, max_le c1.2 c2.2⟩, ?_⟩
      show (lpSys B (n + 1)).val s1 y + (lpSys B (n + 1)).val s2 y = _
      rw [v1, v2, ← gxTh_add hy hAt (hw.mono hZy Subset.rfl), hdr]
    rcases (log_le_self ω d).lt_or_eq with hL | hL
    · obtain ⟨s, hs⟩ := IH _ hL hlog (hL.trans hdB)
      refine ⟨LpT.pw s, fun y hy hy1 hZy => ?_⟩
      obtain ⟨c1, v1⟩ := hs y hy hy1 hZy
      refine ⟨c1, ?_⟩
      show ω ^ (lpSys B (n + 1)).val s y = _
      rw [v1, ← gxTh_opow hy hAt (hlog.mono hZy Subset.rfl), hwd']
    have hdE : ω ^ d = d := by conv_lhs => rw [← hL]
                               exact hwd'
    have hdec : veblen (invVeblen₁ d) (invVeblen₂ d) = d := by rw [veblen_invVeblen₁_invVeblen₂, hdE]
    have hb1 : invVeblen₂ d < d := by have := invVeblen₂_lt d; rwa [hdE] at this
    obtain ⟨ha, hb⟩ := gxDecV hZ.1 hAt hd _ _ hdec hb1
    set a := invVeblen₁ d with hadef
    set b := invVeblen₂ d with hbdef
    have ha0 : a ≠ 0 := by
      intro h0
      rw [h0, veblen_zero_apply] at hdec
      have e := hdE
      rw [← hdec] at e
      have e2 := (opow_right_inj one_lt_omega0).1 e
      rw [← hdec, e2] at hb1
      exact lt_irrefl _ hb1
    have hSC1 := ph_SC_Om1
    have haOO : a < cQ c n := by
      have hlt : veblen a b < veblen (cQ c n) (bQ (cQ c n)) := by rw [hdec]; exact hdB
      rcases veblen_lt_veblen_iff.1 hlt with ⟨h1, hb'⟩ | ⟨h', _⟩ | ⟨_, h'⟩
      · exfalso
        have hb0 : b = 0 := Order.lt_one_iff.1 (hb'.trans_le (bQ_le_one _))
        have hsc : veblen (cQ c n) 0 = cQ c n := bQ_ne_zero_iff.1 (pos_iff_ne_zero.1 (lt_of_le_of_lt zero_le hb'))
        have hdc' : d = cQ c n := by rw [← hdec, h1, hb0, hsc]
        cases n with
        | zero => exact hcd.ne' hdc'
        | succ m => exact cQ_succ_notSC hcO m hsc
      · exact h'
      · exact absurd (Order.lt_one_iff.1 (h'.trans_le (bQ_le_one _))) veblen_pos.ne'
    have hbv : b < veblen a b := by rw [hdec]; exact hb1
    -- a strongly critical code `d = φ(d, 0)` below `cQ c n`: a term of the stage `n`
    by_cases hdS : veblen a 0 = a ∧ b = 0
    · have hda : d = a := by rw [← hdec, hdS.2, hdS.1]
      obtain ⟨l, hlv⟩ := ihn Z d hd (hda ▸ haOO)
      refine ⟨l, fun y hy hy1 hZy => ?_⟩
      obtain ⟨c1, v1⟩ := hlv y hy hy1 hZy
      exact ⟨⟨c1.1, c1.2.trans (Nat.le_succ n)⟩, v1⟩
    have had : a < d := by
      refine lt_of_le_of_ne (hdec ▸ left_le_veblen a b) fun e => hdS ?_
      have h1 : veblen a 0 ≤ veblen a b := (veblen_le_veblen_iff_right).2 zero_le
      rw [hdec, ← e] at h1
      have h2 : veblen a 0 = a := le_antisymm h1 (left_le_veblen a 0)
      refine ⟨h2, ?_⟩
      by_contra hb0
      have h3 : veblen a 0 < veblen a b := (veblen_lt_veblen_iff_right).2 (pos_iff_ne_zero.2 hb0)
      rw [h2, hdec, ← e] at h3
      exact lt_irrefl _ h3
    rcases lt_or_ge a (Om 1) with haO | haO
    · have haZ : a < Z := GxCl.lt_of_lt_Om1 hZ hAt ha haO
      have ha1 : 1 ≤ a := one_le_iff_ne_zero.2 ha0
      have hbO : Om 1 < b := by
        by_contra hle
        push Not at hle
        have h3 := (veblen_le_veblen_iff_right (o := a)).2 hle
        rw [hdec, hSC1.veblen_right haO] at h3
        exact absurd hd1 (not_lt.2 h3)
      obtain ⟨d', hd', hd'b, hdθ⟩ := gxIndCodeU hAt hZ haZ hb hbO hbv
      obtain ⟨t, ht⟩ := IH d' (hd'b.trans_lt hb1) hd' ((hd'b.trans_lt hb1).trans hdB)
      refine ⟨LpT.th0 a t, fun y hy hy1 hZy => ?_⟩
      obtain ⟨ct, vt'⟩ := ht y hy hy1 hZy
      have hy1' := lp_y1 hy1
      have hay : a < y := haZ.trans_le hZy
      refine ⟨⟨⟨ha1, hay, ct.1⟩, max_le (Nat.succ_le_succ (Nat.zero_le n)) ct.2⟩, ?_⟩
      show vt y (Om1 * a + (lpSys B (n + 1)).val t y) = gxTh y gcAt d
      have hby := hb.mono hZy Subset.rfl
      have hThd : gxTh y gcAt d = veblen a (gxTh y gcAt b) := by
        rw [← hdec, gxTh_veblen_lvl hy hAt hay hby]
      have hyb : y < gxTh y gcAt b := by
        have := gxTh_lt (GxCl.om (Z := y) (At := gcAt)) hbO; rwa [gxTh_Om1 hy hy1 hAt] at this
      have hbP : ¬ LuP (a + 1) (gxTh y gcAt b) := by
        intro hP
        have h1 := gxTh_lt hby hbv
        rw [gxTh_veblen_lvl hy hAt hay hby, luP_succ.1 hP] at h1
        exact lt_irrefl _ h1
      obtain ⟨htT, htlt⟩ := LpT.lp_T (gg_SC_eps hy) hy1' t ct.1
      have hTv : (lpSys B (n + 1)).val t y ∈ Tset y ∧ (lpSys B (n + 1)).val t y < Om1 :=
        ⟨htT, htlt.trans (gP_facts B (gg_SC_eps hy) hy1' _).2.2.1⟩
      have e1 : (lpSys B (n + 1)).val t y = luInd a y (gxTh y gcAt b) := by rw [vt', hdθ y hy hy1 hZy]
      rw [e1] at hTv ⊢
      rw [hThd, luPhLev hy hy1' ha1 hay _ hyb hbP hTv.1 hTv.2]
    · -- a level code `Ω₁ ≤ a < cQ c n`: the term `tl l t`
      obtain ⟨l, hlv⟩ := ihn Z a ha haOO
      have hl : ¬ LpT.noB l :=
        gcNotNoB hZ hZ1 ha haO (fun y hy hy1 hZy => (hlv y hy hy1 hZy).2)
      have hb0 : veblen a 0 = a → 0 < b := by
        intro hfa
        rcases eq_or_ne b 0 with hb0 | hb0
        · exact absurd ⟨hfa, hb0⟩ hdS
        · exact pos_iff_ne_zero.2 hb0
      obtain ⟨d', hd', hd'b, hdθ⟩ := gxIndCodeV hAt hZ ha haO hb hb0 hbv
      obtain ⟨t, ht⟩ := IH d' (hd'b.trans_lt hb1) hd' ((hd'b.trans_lt hb1).trans hdB)
      refine ⟨LpT.tl l t, fun y hy hy1 hZy => ?_⟩
      obtain ⟨ct, vt'⟩ := ht y hy hy1 hZy
      obtain ⟨clc, clv⟩ := hlv y hy hy1 hZy
      have hyE : InE y := gg_SC_eps hy
      have hy1' := lp_y1 hy1
      refine ⟨⟨⟨hl, clc.1, ct.1⟩, max_le (Nat.succ_le_succ clc.2) ct.2⟩, ?_⟩
      show vt y (Om1 * LpT.val l y + (lpSys B (n + 1)).val t y) = gxTh y gcAt d
      have hby := hb.mono hZy Subset.rfl
      have hay := ha.mono hZy Subset.rfl
      have hThd : gxTh y gcAt d = veblen (gxTh y gcAt a) (gxTh y gcAt b) := by
        rw [← hdec, gxTh_phi hy hAt _ hay _ hby]
      have hyΘ : y ≤ gxTh y gcAt a := by
        rcases haO.lt_or_eq with h | h
        · have := gxTh_lt (GxCl.om (Z := y) (At := gcAt)) h; rw [gxTh_Om1 hy hy1 hAt] at this; exact this.le
        · rw [← h, gxTh_Om1 hy hy1 hAt]
      have hβd : gxTh y gcAt a < veblen (gxTh y gcAt a) (gxTh y gcAt b) := by
        rw [← hThd]; exact gxTh_lt hay had
      have hbP : ¬ LuP (gxTh y gcAt a + 1) (gxTh y gcAt b) := by
        intro hP
        have h1 := gxTh_lt hby hbv
        rw [gxTh_phi hy hAt _ hay _ hby, luP_succ.1 hP] at h1
        exact lt_irrefl _ h1
      obtain ⟨htT, htlt⟩ := LpT.lp_T hyE hy1' t ct.1
      have hTv : (lpSys B (n + 1)).val t y ∈ Tset y ∧ (lpSys B (n + 1)).val t y < Om1 :=
        ⟨htT, htlt.trans (gP_facts B hyE hy1' _).2.2.1⟩
      have e1 : (lpSys B (n + 1)).val t y = lpInd (gxTh y gcAt a) y (gxTh y gcAt b) := by rw [vt', hdθ y hy hy1 hZy]
      rw [e1] at hTv ⊢
      have hLT := (LpT.lp_T hyE hy1' l clc.1).1
      have hL1 := LpT.lp_lt_Om1 hyE hy1' l clc.1
      have clv' : LpT.val l y = gxTh y gcAt a := clv
      rw [clv'] at hLT hL1
      have hβ1 : 1 ≤ gxTh y gcAt a := (lu_one_lt_E hyE).le.trans hyΘ
      rw [clv', hThd, lpPhLev hy hy1' hβ1 hLT hL1 _ (hyΘ.trans_lt hβd) hβd hbP hTv.1 hTv.2]

end Poly

end Googology.Trans.PoR.InaccPsi.R2.Gc

import Googology.Trans.PoR.InaccPsi.R2.GiRd

/-!
# The ladder over a gated base, with the codes of a code system `K`: terms for every code below the stage tops

`R2.GhLd` for an arbitrary code system `K : GiCS` (`R2.GiAt`): for a gated base `B` whose top reads a code `c`
(`E_K(y) = Θ_y(c)` above the gate) and whose layer has terms for the codes below `c`:

* `gicQ_cl` (the stage codes are codes), `giNotNoB` (a term that reads a level code `a ≥ Ω₁` at every strongly
  critical base above `Z` is not base-free);
* `giTop_th` (**`gdP B n y = Θ_y(cQ c n)`** above the gate), `giPoly` (**every code below `cQ c n` over a base above
  the gate is read by a term of stage `≤ n`**).

No new axiom.  New definition: `GiLdP`.
-/
set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gi

open Googology.Trans.PoR.InaccPsi.R2.Gf

open Googology.Trans.PoR.InaccPsi.R2.Ge
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph Googology.Trans.PoR.InaccPsi.R2.Xt Lu
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Lp
  Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd

variable {K : GiCS}

theorem gicQ_cl {g c : Ordinal.{0}} (hc : ∀ Z, SC Z → g < Z → GxCl Z (K.At Z) c) {Z : Ordinal.{0}} (hZ : SC Z)
    (hgZ : g < Z) : ∀ n : ℕ, GxCl Z (K.At Z) (cQ c n)
  | 0 => hc Z hZ hgZ
  | n + 1 => GxCl.phi (gicQ_cl hc hZ hgZ n) (GxCl.small (bQ_lt hZ _))

/-! ## A level code is not read by a base-free term -/

/-- **A term that reads a level code `a ≥ Ω₁` at every strongly critical `y ≥ Z` is not base-free.** -/
theorem giNotNoB {B : GdB} {Z a : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z < Om 1)
    (ha : GxCl Z (K.At Z) a) (haO : Om 1 ≤ a) {l : GdT B}
    (hl : ∀ y, SC y → y < Om 1 → Z ≤ y → GdT.val l y = gxTh y (K.At y) a) : ¬ GdT.noB l := by
  intro hn
  obtain ⟨Y, hYS, hvY, hY1⟩ := gd_SC_above (giTh_lt_Om1 hZ hZ1 ha)
  have hZv : Z ≤ gxTh Z (K.At Z) a := by
    have := gxTh_mono (Z := Z) (At := K.At Z) haO
    rwa [gxTh_Om1 hZ hZ1 (giAt_GxAt Z)] at this
  have hge : Y ≤ gxTh Y (K.At Y) a := by
    have := gxTh_mono (Z := Y) (At := K.At Y) haO
    rwa [gxTh_Om1 hYS hY1 (giAt_GxAt _)] at this
  have e := GdT.noB_val l hn Z Y
  rw [hl Z hZ hZ1 le_rfl, hl _ hYS hY1 (hZv.trans hvY.le)] at e
  exact absurd (e ▸ hvY) (not_lt.2 hge)

/-- **The ladder statement**: every code `d < E` over a base `Z` above the gate is read by a term of stage `≤ n`. -/
def GiLdP (K : GiCS) (B : GdB) (n : ℕ) (E : Ordinal.{0}) : Prop :=
  ∀ Z d, B.g < Z → GxCl Z (K.At Z) d → d < E → ∃ s : GdT B, ∀ y, SC y → y < Om 1 → Z ≤ y →
    (GdT.CBt s y ∧ GdT.stage s ≤ n) ∧ GdT.val s y = gxTh y (K.At y) d

/-! ## The readings of the stage tops and the terms for the codes -/

section Poly

variable {B : GdB} {c : Ordinal.{0}} (hc : ∀ Z, SC Z → B.g < Z → GxCl Z (K.At Z) c) (hcO : Om 1 ≤ c)
  (hKE : ∀ y, SC y → y < Om 1 → B.g < y → B.K.E y = gxTh y (K.At y) c)
include hc hcO hKE

omit hcO in
/-- **`gP n y = Θ_y(cQ c n)`** at every strongly critical `y < Ω₁`. -/
theorem giTop_th : ∀ n : ℕ, ∀ y, SC y → y < Om 1 → B.g < y → gdP B n y = gxTh y (K.At y) (cQ c n)
  | 0, y, hy, hy1, hg => hKE y hy hy1 hg
  | n + 1, y, hy, hy1, hg => by
      have hAt := giAt_GxAt (K := K) y
      have hyE := gg_SC_eps hy
      have hy1' := lp_y1 hy1
      have ih := giTop_th n y hy hy1 hg
      have hcn := gicQ_cl hc hy hg n
      have hbn : GxCl y (K.At y) (bQ (cQ c n)) := GxCl.small (bQ_lt hy _)
      show vt y (Om1 * gdP B n y) = gxTh y (K.At y) (veblen (cQ c n) (bQ (cQ c n)))
      rw [gxTh_phi hy hAt _ hcn _ hbn, gxTh_small (bQ_lt hy _).le, ← ih]
      obtain ⟨hβT, hyβ, hβ1, -⟩ := gdP_facts B hyE hy1' hg n
      have hβ1' : 1 ≤ gdP B n y := (Lu.lu_one_lt_E hyE).le.trans hyβ.le
      by_cases hS : veblen (cQ c n) 0 = cQ c n
      · rw [bQ_of hS]
        have hβS : veblen (gdP B n y) 0 = gdP B n y := by
          have := congrArg (gxTh y (K.At y)) hS
          rw [gxTh_phi hy hAt _ hcn _ (GxCl.zero hy.1), gxTh_zero, ← ih] at this
          exact this
        have h0 : lpInd (gdP B n y) y 1 = 0 := by
          have := lpInd_low_eq (β := gdP B n y) (y := y) (δ := 0) (Or.inr ⟨hβS, hyβ.le⟩)
            (fun z hz => absurd hz (not_lt.2 zero_le))
          rwa [add_zero] at this
        have hnP : ¬ LuP (gdP B n y + 1) 1 := by
          have h := lu_P_nat_not (β := gdP B n y) 0 0
          have e : (0 : Ordinal.{0}) + 1 + ((0 : ℕ) : Ordinal.{0}) = 1 := by simp
          rwa [e] at h
        have hy1v : y < veblen (gdP B n y) 1 :=
          hyβ.trans (lt_of_eq_of_lt hβS.symm (veblen_lt_veblen_iff_right.2 zero_lt_one))
        have e := lpPhLev hy hy1' hβ1' hβT hβ1 1 hy1v (lp_lvl_lt zero_lt_one) hnP
          (by rw [h0]; exact mem_T_of_le hyE hy1' zero_le) (by rw [h0]; exact Ordinal.omega_pos 1)
        rw [e, h0, add_zero]
      · rw [bQ_of_not hS]
        have hβv : gdP B n y < veblen (gdP B n y) 0 := by
          have := gxTh_lt hcn (lt_of_le_of_ne (left_le_veblen (cQ c n) 0) (Ne.symm hS)) (At := K.At y)
          rwa [gxTh_phi hy hAt _ hcn _ (GxCl.zero hy.1), gxTh_zero, ← ih] at this
        have h0 : lpInd (gdP B n y) y 0 = 0 := ggOtp_zero _
        have hnP : ¬ LuP (gdP B n y + 1) 0 := by
          rintro ⟨j, hj⟩
          exact absurd hj (gg_veblen_eps (x := gdP B n y + 1) (y := j)
            (by simp) ▸ (Ordinal.opow_pos _ omega0_pos)).ne'
        have e := lpPhLev hy hy1' hβ1' hβT hβ1 0 (hyβ.trans hβv) hβv hnP
          (by rw [h0]; exact mem_T_of_le hyE hy1' zero_le) (by rw [h0]; exact Ordinal.omega_pos 1)
        rw [e, h0, add_zero]

/-- **Every code below `cQ c n` over a base above the gate is read by a term of stage `≤ n`** (given the terms of `K`
for the codes below `c`). -/
theorem giPoly (hKP : GiPolyG K B.K.sys c) : ∀ n : ℕ, GiLdP K B n (cQ c n) := by
  have hKterm : ∀ (n : ℕ) (Z d : Ordinal.{0}), B.g < Z → GxCl Z (K.At Z) d → d < c → ∃ s : GdT B, ∀ y, SC y →
      y < Om 1 → Z ≤ y → (GdT.CBt s y ∧ GdT.stage s ≤ n) ∧ GdT.val s y = gxTh y (K.At y) d := by
    intro n Z d hgZ hd hdc
    obtain ⟨k, hk⟩ := hKP Z d hgZ hd hdc
    exact ⟨GdT.ak k, fun y hy hy1 hZy => ⟨⟨(hk y hy hy1 hZy).1, Nat.zero_le n⟩, (hk y hy hy1 hZy).2⟩⟩
  intro n
  induction n with
  | zero => exact fun Z d hgZ hd hdc => hKterm 0 Z d hgZ hd hdc
  | succ n ihn =>
    refine giPoly_of_SC (fun s y => GdT.CBt s y ∧ GdT.stage s ≤ n + 1) GdT.val (GdT.cst 0) fun Z hZ hZ1 hgZ => ?_
    intro d
    induction d using WellFoundedLT.induction with
    | ind d IH =>
    intro hd hdB
    rcases lt_trichotomy d c with hdc | rfl | hcd
    · exact hKterm (n + 1) Z d hgZ hd hdc
    · exact ⟨GdT.tp, fun y hy hy1 hZy => ⟨⟨trivial, by simp [GdT.stage]⟩, hKE y hy hy1 (hgZ.trans_le hZy)⟩⟩
    have hd1 : Om 1 < d := hcO.trans_lt hcd
    have hd0 : d ≠ 0 := (lt_of_le_of_lt zero_le hd1).ne'
    obtain ⟨hsub, hlog⟩ := gxDec hZ (giAt_GxAt Z) d hd
    have hw : GxCl Z (K.At Z) (ω ^ log ω d) := GxCl.opow hZ.1 hlog
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
      refine ⟨GdT.sm s1 s2, fun y hy hy1 hZy => ?_⟩
      obtain ⟨c1, v1⟩ := hs1 y hy hy1 hZy
      obtain ⟨c2, v2⟩ := hs2 y hy hy1 hZy
      refine ⟨⟨⟨c1.1, c2.1⟩, max_le c1.2 c2.2⟩, ?_⟩
      show GdT.val s1 y + GdT.val s2 y = _
      rw [v1, v2, ← gxTh_add hy (giAt_GxAt y) (giCl_mono hZy hw), hdr]
    rcases (log_le_self ω d).lt_or_eq with hL | hL
    · obtain ⟨s, hs⟩ := IH _ hL hlog (hL.trans hdB)
      refine ⟨GdT.pw s, fun y hy hy1 hZy => ?_⟩
      obtain ⟨c1, v1⟩ := hs y hy hy1 hZy
      refine ⟨c1, ?_⟩
      show ω ^ GdT.val s y = _
      rw [v1, ← gxTh_opow hy (giAt_GxAt y) (giCl_mono hZy hlog), hwd']
    have hdE : ω ^ d = d := by conv_lhs => rw [← hL]
                               exact hwd'
    have hdec : veblen (invVeblen₁ d) (invVeblen₂ d) = d := by rw [veblen_invVeblen₁_invVeblen₂, hdE]
    have hb1 : invVeblen₂ d < d := by have := invVeblen₂_lt d; rwa [hdE] at this
    obtain ⟨ha, hb⟩ := gxDecV hZ.1 (giAt_GxAt Z) hd _ _ hdec hb1
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
      obtain ⟨l, hlv⟩ := ihn Z d hgZ hd (hda ▸ haOO)
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
    · have haZ : a < Z := GxCl.lt_of_lt_Om1 hZ (giAt_GxAt Z) ha haO
      have ha1 : 1 ≤ a := one_le_iff_ne_zero.2 ha0
      have hbO : Om 1 < b := by
        by_contra hle
        push Not at hle
        have h3 := (veblen_le_veblen_iff_right (o := a)).2 hle
        rw [hdec, hSC1.veblen_right haO] at h3
        exact absurd hd1 (not_lt.2 h3)
      obtain ⟨d', hd', hd'b, hdθ⟩ := giIndCodeU hZ haZ hb hbO hbv
      obtain ⟨t, ht⟩ := IH d' (hd'b.trans_lt hb1) hd' ((hd'b.trans_lt hb1).trans hdB)
      refine ⟨GdT.th0 a t, fun y hy hy1 hZy => ?_⟩
      obtain ⟨ct, vt'⟩ := ht y hy hy1 hZy
      have hy1' := lp_y1 hy1
      have hay : a < y := haZ.trans_le hZy
      refine ⟨⟨⟨ha1, hay, ct.1⟩, max_le (Nat.succ_le_succ (Nat.zero_le n)) ct.2⟩, ?_⟩
      have hgy : B.g < y := hgZ.trans_le hZy
      show vt y (Om1 * a + GdT.val t y) = gxTh y (K.At y) d
      have hby := giCl_mono hZy hb
      have hThd : gxTh y (K.At y) d = veblen a (gxTh y (K.At y) b) := by
        rw [← hdec, gxTh_veblen_lvl hy (giAt_GxAt y) hay hby]
      have hyb : y < gxTh y (K.At y) b := by
        have := gxTh_lt (GxCl.om (Z := y) (At := K.At y)) hbO; rwa [gxTh_Om1 hy hy1 (giAt_GxAt y)] at this
      have hbP : ¬ LuP (a + 1) (gxTh y (K.At y) b) := by
        intro hP
        have h1 := gxTh_lt hby hbv
        rw [gxTh_veblen_lvl hy (giAt_GxAt y) hay hby, luP_succ.1 hP] at h1
        exact lt_irrefl _ h1
      obtain ⟨htT, htlt⟩ := GdT.gd_T (gg_SC_eps hy) hy1' hgy t ct.1
      have hTv : GdT.val t y ∈ Tset y ∧ GdT.val t y < Om1 :=
        ⟨htT, htlt.trans (gdP_facts B (gg_SC_eps hy) hy1' hgy _).2.2.1⟩
      have e1 : GdT.val t y = luInd a y (gxTh y (K.At y) b) := by rw [vt', hdθ y hy hy1 hZy]
      rw [e1] at hTv ⊢
      rw [hThd, luPhLev hy hy1' ha1 hay _ hyb hbP hTv.1 hTv.2]
    · -- a level code `Ω₁ ≤ a < cQ c n`: the term `tl l t`
      obtain ⟨l, hlv⟩ := ihn Z a hgZ ha haOO
      have hl : ¬ GdT.noB l :=
        giNotNoB hZ hZ1 ha haO (fun y hy hy1 hZy => (hlv y hy hy1 hZy).2)
      have hb0 : veblen a 0 = a → 0 < b := by
        intro hfa
        rcases eq_or_ne b 0 with hb0 | hb0
        · exact absurd ⟨hfa, hb0⟩ hdS
        · exact pos_iff_ne_zero.2 hb0
      obtain ⟨d', hd', hd'b, hdθ⟩ := giIndCodeV hZ ha haO hb hb0 hbv
      obtain ⟨t, ht⟩ := IH d' (hd'b.trans_lt hb1) hd' ((hd'b.trans_lt hb1).trans hdB)
      refine ⟨GdT.tl l t, fun y hy hy1 hZy => ?_⟩
      obtain ⟨ct, vt'⟩ := ht y hy hy1 hZy
      obtain ⟨clc, clv⟩ := hlv y hy hy1 hZy
      have hyE : InE y := gg_SC_eps hy
      have hy1' := lp_y1 hy1
      have hgy : B.g < y := hgZ.trans_le hZy
      refine ⟨⟨⟨hl, clc.1, ct.1⟩, max_le (Nat.succ_le_succ clc.2) ct.2⟩, ?_⟩
      show vt y (Om1 * GdT.val l y + GdT.val t y) = gxTh y (K.At y) d
      have hby := giCl_mono hZy hb
      have hay := giCl_mono hZy ha
      have hThd : gxTh y (K.At y) d = veblen (gxTh y (K.At y) a) (gxTh y (K.At y) b) := by
        rw [← hdec, gxTh_phi hy (giAt_GxAt y) _ hay _ hby]
      have hyΘ : y ≤ gxTh y (K.At y) a := by
        rcases haO.lt_or_eq with h | h
        · have := gxTh_lt (GxCl.om (Z := y) (At := K.At y)) h; rw [gxTh_Om1 hy hy1 (giAt_GxAt y)] at this; exact this.le
        · rw [← h, gxTh_Om1 hy hy1 (giAt_GxAt y)]
      have hβd : gxTh y (K.At y) a < veblen (gxTh y (K.At y) a) (gxTh y (K.At y) b) := by
        rw [← hThd]; exact gxTh_lt hay had
      have hbP : ¬ LuP (gxTh y (K.At y) a + 1) (gxTh y (K.At y) b) := by
        intro hP
        have h1 := gxTh_lt hby hbv
        rw [gxTh_phi hy (giAt_GxAt y) _ hay _ hby, luP_succ.1 hP] at h1
        exact lt_irrefl _ h1
      obtain ⟨htT, htlt⟩ := GdT.gd_T hyE hy1' hgy t ct.1
      have hTv : GdT.val t y ∈ Tset y ∧ GdT.val t y < Om1 :=
        ⟨htT, htlt.trans (gdP_facts B hyE hy1' hgy _).2.2.1⟩
      have e1 : GdT.val t y = lpInd (gxTh y (K.At y) a) y (gxTh y (K.At y) b) := by rw [vt', hdθ y hy hy1 hZy]
      rw [e1] at hTv ⊢
      have hLT := (GdT.gd_T hyE hy1' hgy l clc.1).1
      have hL1 := GdT.gd_lt_Om1 hyE hy1' hgy l clc.1
      have clv' : GdT.val l y = gxTh y (K.At y) a := clv
      rw [clv'] at hLT hL1
      have hβ1 : 1 ≤ gxTh y (K.At y) a := (lu_one_lt_E hyE).le.trans hyΘ
      rw [clv', hThd, lpPhLev hy hy1' hβ1 hLT hL1 _ (hyΘ.trans_lt hβd) hβd hbP hTv.1 hTv.2]

end Poly

end Googology.Trans.PoR.InaccPsi.R2.Gi

import Googology.Trans.PoR.InaccPsi.R2.LpIdx
import Googology.Trans.PoR.InaccPsi.R2.LpFam

/-!
# The code calculus shifts by the code of the base: terms for every code below the stage tops over `K`

Let the base layer `K` have terms for the codes below `c` (`LgPoly K c`) and the top `E_K(y) = Θ'_y(c)` at every
strongly critical `y`, with `c < φ(c, 0)` (the top is not strongly critical).  The codes of the stage tops are
`cP c 0 = c`, `cP c (n+1) = φ(cP c n, 0)`, and:

* `lpG_SC` (**`Γ_{y+1}` is strongly critical** for a strongly critical `y`: the φ-law), `lpTh_lt_GG` (**every code
  over `Z` reads below `Γ_{Γ_{Z+1}+1}`**), `lp_notNoB` (a term that reads a level code `a ≥ Ω₁` at every strongly
  critical `y ≥ Z` is not base-free);
* `lpTop_th` (**`gP n y = Θ'_y(cP c n)`**: `ϑʸ(Ω₁·β) = φ(β, 0)` by the level lemma `lpPhLev`);
* `lpPoly` (**`LgPoly (lpSys B n) (cP c n)` for every `n`**: a code `d < φ(cP c n, 0)` is a code below `c` (a term
  of `K`), `c` itself (the atom `tp`), a sum, a power, `φ_a(b)` with a constant level `1 ≤ a < Z` (the term
  `th0 a t`, `lpIndCodeU`) or `φ_a(b)` with a level code `Ω₁ ≤ a < cP c n` (the term `tl l t`, `lpIndCodeV`;
  strongly critical levels such as `Γ_{Ω₁+1}` included), or a strongly critical code below `cP c n`).

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Lp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph Googology.Trans.PoR.InaccPsi.R2.Xt Lu
  Googology.Trans.PoR.InaccPsi.R2.Cd

/-! ## Strongly critical points are unbounded: `Γ_{y+1}` -/

theorem lp_y1 {y : Ordinal.{0}} (hy1 : y < Om 1) : y < Om1 := by rw [ph_Om1_eq]; exact hy1

/-- **`Γ_{y+1} = Θ'_y(Γ_{Ω₁+1})` is strongly critical** for a strongly critical `y < Ω₁`. -/
theorem lpG_SC {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) : SC (lgG y) := by
  rw [← lgTh_Gam hy hy1]
  refine ⟨lt_of_le_of_lt zero_le (lgTh_lt (LgCl.zero hy.1) (ggGam_spec.1.1)), fun x hx x' hx' => ?_⟩
  obtain ⟨a, ha, haG, rfl⟩ := lgTh_onto hx
  obtain ⟨b, hb, hbG, rfl⟩ := lgTh_onto hx'
  rw [← lpTh_phi hy a ha b hb]
  exact lgTh_lt (LgCl.phi ha hb) (ggGam_spec.1.2 a haG b hbG)

theorem lpG_facts {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) : y < lgG y ∧ lgG y < Om 1 := by
  obtain ⟨-, h1, h2, -⟩ := lgG_facts (gg_SC_eps hy) (lp_y1 hy1)
  exact ⟨h1, by rw [← ph_Om1_eq]; exact h2⟩

/-- **Every code over `Z` reads below `Γ_{Γ_{Z+1}+1}`.** -/
theorem lpTh_lt_GG {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z < Om 1) {d : Ordinal.{0}} (hd : LgCl Z d) :
    lgTh Z d < lgG (lgG Z) := by
  obtain ⟨h1, h2⟩ := lpG_facts hZ hZ1
  have hS1 := lpG_SC hZ hZ1
  obtain ⟨h3, -⟩ := lpG_facts hS1 h2
  have hS2 := lpG_SC hS1 h2
  induction hd with
  | small h => rw [lgTh_small h.le]; exact (h.trans h1).trans h3
  | om => rw [lgTh_Om1 hZ hZ1]; exact h1.trans h3
  | gam => rw [lgTh_Gam hZ hZ1]; exact h3
  | @add u v hu _ ihu ihv => rw [lgTh_add hZ hu]; exact hS2.isPrincipal ihu ihv
  | @phi a b ha hb iha ihb => rw [lpTh_phi hZ a ha b hb]; exact hS2.2 _ iha _ ihb

/-- **A term that reads a level code `a ≥ Ω₁` at every strongly critical `y ≥ Z` is not base-free.** -/
theorem lp_notNoB {B : LpB} {Z a : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z < Om 1) (ha : LgCl Z a) (haO : Om 1 ≤ a)
    {l : LpT B} (hl : ∀ y, SC y → y < Om 1 → Z ≤ y → LpT.val l y = lgTh y a) : ¬ LpT.noB l := by
  intro hn
  obtain ⟨h1, h2⟩ := lpG_facts hZ hZ1
  have hS1 := lpG_SC hZ hZ1
  obtain ⟨h3, h4⟩ := lpG_facts hS1 h2
  have hS2 := lpG_SC hS1 h2
  have hZY : Z ≤ lgG (lgG Z) := (h1.trans h3).le
  have hlt := lpTh_lt_GG hZ hZ1 ha
  have hge : lgG (lgG Z) ≤ lgTh (lgG (lgG Z)) a := by
    rcases haO.lt_or_eq with h | h
    · have := lgTh_lt (LgCl.om (Z := lgG (lgG Z))) h (y := lgG (lgG Z))
      rw [lgTh_Om1 hS2 h4] at this; exact this.le
    · rw [← h, lgTh_Om1 hS2 h4]
  have e := LpT.noB_val l hn Z (lgG (lgG Z))
  rw [hl Z hZ hZ1 le_rfl, hl _ hS2 h4 hZY] at e
  exact absurd (e ▸ hlt) (not_lt.2 hge)

/-! ## The codes of the stage tops -/

/-- The codes of the stage tops: `cP c 0 = c`, `cP c (n+1) = φ(cP c n, 0)`. -/
noncomputable def cP (c : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => c
  | n + 1 => veblen (cP c n) 0

section Tower

variable {c : Ordinal.{0}}

theorem cP_cl (hc : ∀ Z, SC Z → LgCl Z c) {Z : Ordinal.{0}} (hZ : SC Z) : ∀ n : ℕ, LgCl Z (cP c n)
  | 0 => hc Z hZ
  | n + 1 => LgCl.phi (cP_cl hc hZ n) (LgCl.zero hZ.1)

theorem cP_lt_v (hcv : c < veblen c 0) : ∀ n : ℕ, cP c n < veblen (cP c n) 0
  | 0 => hcv
  | n + 1 => veblen_zero_lt_veblen_zero.2 (cP_lt_v hcv n)

theorem cP_lt_succ (hcv : c < veblen c 0) (n : ℕ) : cP c n < cP c (n + 1) := cP_lt_v hcv n

theorem cP_Om1_le (hcO : Om 1 ≤ c) : ∀ n : ℕ, Om 1 ≤ cP c n
  | 0 => hcO
  | n + 1 => (cP_Om1_le hcO n).trans (left_le_veblen _ _)

end Tower

/-! ## The readings of the stage tops and the terms for the codes -/

section Poly

variable {B : LpB} {c : Ordinal.{0}} (hc : ∀ Z, SC Z → LgCl Z c) (hcO : Om 1 ≤ c) (hcv : c < veblen c 0)
  (hKE : ∀ y, SC y → y < Om 1 → B.K.E y = lgTh y c)
include hc hcO hcv hKE

omit hcO in
/-- **`gP n y = Θ'_y(cP c n)`** at every strongly critical `y < Ω₁`. -/
theorem lpTop_th : ∀ n : ℕ, ∀ y, SC y → y < Om 1 → gP B n y = lgTh y (cP c n)
  | 0, y, hy, hy1 => hKE y hy hy1
  | n + 1, y, hy, hy1 => by
      have hyE := gg_SC_eps hy
      have hy1' := lp_y1 hy1
      have ih := lpTop_th n y hy hy1
      show vt y (Om1 * gP B n y) = lgTh y (veblen (cP c n) 0)
      rw [lpTh_phi hy _ (cP_cl hc hy n) _ (LgCl.zero hy.1), lpTh_zero, ← ih]
      obtain ⟨hβT, hyβ, hβ1, -⟩ := gP_facts B hyE hy1' n
      have hβv : gP B n y < veblen (gP B n y) 0 := by
        have := lgTh_lt (cP_cl hc hy n) (cP_lt_v hcv n) (y := y)
        rwa [lpTh_phi hy _ (cP_cl hc hy n) _ (LgCl.zero hy.1), lpTh_zero, ← ih] at this
      have h0 : lpInd (gP B n y) y 0 = 0 := ggOtp_zero _
      have hnP : ¬ LuP (gP B n y + 1) 0 := by
        rintro ⟨j, hj⟩
        exact absurd hj (gg_veblen_eps (x := gP B n y + 1) (y := j)
          (by simp) ▸ (Ordinal.opow_pos _ omega0_pos)).ne'
      have e := lpPhLev hy hy1' ((Lu.lu_one_lt_E hyE).le.trans hyβ.le) hβT hβ1 0 (hyβ.trans hβv) hβv hnP
        (by rw [h0]; exact mem_T_of_le hyE hy1' zero_le) (by rw [h0]; exact Ordinal.omega_pos 1)
      rw [e, h0, add_zero]

/-- **`lpSys B n` has terms for every code below `cP c n`** (given the terms of `K` for the codes below `c`). -/
theorem lpPoly (hKP : LgPoly B.K.sys c) : ∀ n : ℕ, LgPoly (lpSys B n) (cP c n) := by
  have hKterm : ∀ (n : ℕ) (Z d : Ordinal.{0}), LgCl Z d → d < c → ∃ s : (lpSys B n).Tm, ∀ y, SC y → y < Om 1 →
      Z ≤ y → (lpSys B n).CB s y ∧ (lpSys B n).val s y = lgTh y d := by
    intro n Z d hd hdc
    obtain ⟨k, hk⟩ := hKP Z d hd hdc
    exact ⟨LpT.ak k, fun y hy hy1 hZy => ⟨⟨(hk y hy hy1 hZy).1, Nat.zero_le n⟩, (hk y hy hy1 hZy).2⟩⟩
  intro n
  induction n with
  | zero => exact fun Z d hd hdc => hKterm 0 Z d hd hdc
  | succ n ihn =>
    refine lgPoly_of_SC fun Z hZ hZ1 => ?_
    intro d
    induction d using WellFoundedLT.induction with
    | ind d IH =>
    intro hd hdB
    rcases lt_trichotomy d c with hdc | rfl | hcd
    · exact hKterm (n + 1) Z d hd hdc
    · exact ⟨LpT.tp, fun y hy hy1 _ => ⟨⟨trivial, by simp [LpT.stage]⟩, hKE y hy hy1⟩⟩
    have hd1 : Om 1 < d := hcO.trans_lt hcd
    have hd0 : d ≠ 0 := (lt_of_le_of_lt zero_le hd1).ne'
    obtain ⟨hsub, hlog⟩ := lgDec hZ d hd
    have hw : LgCl Z (ω ^ log ω d) := LgCl.opow hZ.1 hlog
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
      rw [v1, v2, ← lgTh_add hy (hw.mono hZy), hdr]
    rcases (log_le_self ω d).lt_or_eq with hL | hL
    · obtain ⟨s, hs⟩ := IH _ hL hlog (hL.trans hdB)
      refine ⟨LpT.pw s, fun y hy hy1 hZy => ?_⟩
      obtain ⟨c1, v1⟩ := hs y hy hy1 hZy
      refine ⟨c1, ?_⟩
      show ω ^ (lpSys B (n + 1)).val s y = _
      rw [v1, ← lgTh_opow hy (hlog.mono hZy), hwd']
    have hdE : ω ^ d = d := by conv_lhs => rw [← hL]
                               exact hwd'
    have hdec : veblen (invVeblen₁ d) (invVeblen₂ d) = d := by rw [veblen_invVeblen₁_invVeblen₂, hdE]
    have hb1 : invVeblen₂ d < d := by have := invVeblen₂_lt d; rwa [hdE] at this
    obtain ⟨ha, hb⟩ := lpDec hZ.1 hd _ _ hdec hb1
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
    have haOO : a < cP c n := by
      have hlt : veblen a b < veblen (cP c n) 0 := by rw [hdec]; exact hdB
      rcases veblen_lt_veblen_iff.1 hlt with ⟨_, hb'⟩ | ⟨h', _⟩ | ⟨_, h'⟩
      · exact absurd hb' (not_lt.2 zero_le)
      · exact h'
      · exact absurd h' (not_lt.2 zero_le)
    have hbv : b < veblen a b := by rw [hdec]; exact hb1
    -- a strongly critical code `d = φ(d, 0)` below `cP c n`: a term of the stage `n`
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
    · have haZ : a < Z := ha.lt_of_lt_Om1 hZ haO
      have ha1 : 1 ≤ a := one_le_iff_ne_zero.2 ha0
      have hbO : Om 1 < b := by
        by_contra hle
        push Not at hle
        have h3 := (veblen_le_veblen_iff_right (o := a)).2 hle
        rw [hdec, hSC1.veblen_right haO] at h3
        exact absurd hd1 (not_lt.2 h3)
      obtain ⟨d', hd', hd'b, hdθ⟩ := lpIndCodeU hZ haZ hb hbO hbv
      obtain ⟨t, ht⟩ := IH d' (hd'b.trans_lt hb1) hd' ((hd'b.trans_lt hb1).trans hdB)
      refine ⟨LpT.th0 a t, fun y hy hy1 hZy => ?_⟩
      obtain ⟨ct, vt'⟩ := ht y hy hy1 hZy
      have hy1' := lp_y1 hy1
      have hay : a < y := haZ.trans_le hZy
      refine ⟨⟨⟨ha1, hay, ct.1⟩, max_le (Nat.succ_le_succ (Nat.zero_le n)) ct.2⟩, ?_⟩
      show vt y (Om1 * a + (lpSys B (n + 1)).val t y) = lgTh y d
      have hby := hb.mono hZy
      have hThd : lgTh y d = veblen a (lgTh y b) := by
        rw [← hdec, lpTh_veblen_lvl hy hay hby]
      have hyb : y < lgTh y b := by
        have := lgTh_lt (LgCl.om (Z := y)) hbO (y := y); rwa [lgTh_Om1 hy hy1] at this
      have hbP : ¬ LuP (a + 1) (lgTh y b) := by
        intro hP
        have h1 := lgTh_lt hby hbv
        rw [lpTh_veblen_lvl hy hay hby, luP_succ.1 hP] at h1
        exact lt_irrefl _ h1
      obtain ⟨htT, htlt⟩ := LpT.lp_T (gg_SC_eps hy) hy1' t ct.1
      have hTv : (lpSys B (n + 1)).val t y ∈ Tset y ∧ (lpSys B (n + 1)).val t y < Om1 :=
        ⟨htT, htlt.trans (gP_facts B (gg_SC_eps hy) hy1' _).2.2.1⟩
      have e1 : (lpSys B (n + 1)).val t y = luInd a y (lgTh y b) := by rw [vt', hdθ y hy hy1 hZy]
      rw [e1] at hTv ⊢
      rw [hThd, luPhLev hy hy1' ha1 hay _ hyb hbP hTv.1 hTv.2]
    · -- a level code `Ω₁ ≤ a < cP c n`: the term `tl l t`
      obtain ⟨l, hlv⟩ := ihn Z a ha haOO
      have hl : ¬ LpT.noB l :=
        lp_notNoB hZ hZ1 ha haO (fun y hy hy1 hZy => (hlv y hy hy1 hZy).2)
      have hb0 : veblen a 0 = a → 0 < b := by
        intro hfa
        rcases eq_or_ne b 0 with hb0 | hb0
        · exact absurd ⟨hfa, hb0⟩ hdS
        · exact pos_iff_ne_zero.2 hb0
      obtain ⟨d', hd', hd'b, hdθ⟩ := lpIndCodeV hZ ha haO hb hb0 hbv
      obtain ⟨t, ht⟩ := IH d' (hd'b.trans_lt hb1) hd' ((hd'b.trans_lt hb1).trans hdB)
      refine ⟨LpT.tl l t, fun y hy hy1 hZy => ?_⟩
      obtain ⟨ct, vt'⟩ := ht y hy hy1 hZy
      obtain ⟨clc, clv⟩ := hlv y hy hy1 hZy
      have hyE : InE y := gg_SC_eps hy
      have hy1' := lp_y1 hy1
      refine ⟨⟨⟨hl, clc.1, ct.1⟩, max_le (Nat.succ_le_succ clc.2) ct.2⟩, ?_⟩
      show vt y (Om1 * LpT.val l y + (lpSys B (n + 1)).val t y) = lgTh y d
      have hby := hb.mono hZy
      have hay := ha.mono hZy
      have hThd : lgTh y d = veblen (lgTh y a) (lgTh y b) := by
        rw [← hdec, lpTh_phi hy _ hay _ hby]
      have hyΘ : y ≤ lgTh y a := by
        rcases haO.lt_or_eq with h | h
        · have := lgTh_lt (LgCl.om (Z := y)) h (y := y); rw [lgTh_Om1 hy hy1] at this; exact this.le
        · rw [← h, lgTh_Om1 hy hy1]
      have hβd : lgTh y a < veblen (lgTh y a) (lgTh y b) := by
        rw [← hThd]; exact lgTh_lt hay had
      have hbP : ¬ LuP (lgTh y a + 1) (lgTh y b) := by
        intro hP
        have h1 := lgTh_lt hby hbv
        rw [lpTh_phi hy _ hay _ hby, luP_succ.1 hP] at h1
        exact lt_irrefl _ h1
      obtain ⟨htT, htlt⟩ := LpT.lp_T hyE hy1' t ct.1
      have hTv : (lpSys B (n + 1)).val t y ∈ Tset y ∧ (lpSys B (n + 1)).val t y < Om1 :=
        ⟨htT, htlt.trans (gP_facts B hyE hy1' _).2.2.1⟩
      have e1 : (lpSys B (n + 1)).val t y = lpInd (lgTh y a) y (lgTh y b) := by rw [vt', hdθ y hy hy1 hZy]
      rw [e1] at hTv ⊢
      have hLT := (LpT.lp_T hyE hy1' l clc.1).1
      have hL1 := LpT.lp_lt_Om1 hyE hy1' l clc.1
      have clv' : LpT.val l y = lgTh y a := clv
      rw [clv'] at hLT hL1
      have hβ1 : 1 ≤ lgTh y a := (lu_one_lt_E hyE).le.trans hyΘ
      rw [clv', hThd, lpPhLev hy hy1' hβ1 hLT hL1 _ (hyΘ.trans_lt hβd) hβd hbP hTv.1 hTv.2]

end Poly

end Googology.Trans.PoR.InaccPsi.R2.Lp

import Googology.Trans.PoR.InaccPsi.R2.HeInd

/-!
# HeG1: LEMMA IMG BELOW `Γ_{ρ+2} = ϑᵖ(Ω₁·Ω₁ + 1)`

`He.HeInd` gives the reach test and Lemma IMG over every pseudo-base `P` of every level `2 ≤ α < Γ_{ρ+2}`
(`He.he_DI`).  Here this is assembled into Lemma IMG for EVERY value below `Γ_{ρ+2}` (`he_img_G1`), by induction over
the `ε`-numbers `e ∈ (Γ_{ρ+1}, Γ_{ρ+2})`:

* every such `e` is `ϑᵖ(Ω₁·q + r)` with `1 ≤ q, r ∈ Tᵖ ∩ Ω₁` (`he_rep`, from the cited `vt_rep`, `vt_E_iff`,
  `lgLt_of_vt_lt`, `lgQuot_mem`: the argument lies below `Ω₁·Ω₁ + 1` and is not `Ω₁·Ω₁`), and `e` is a point of
  `φ(q, ·)` that is not a fixed point (`glA_P`, `glA_notP`);
* if some fixed point of `φ(q, ·)` lies below `e`, let `P = φ(q+1, a)` be the largest one: `e ∈ (P, N_q(P))`,
  `ρ < Γ_{ρ+1} ≤ P`, `N_q(P) < Γ_{ρ+2}` (`he_N_lt1`), so Lemma IMG at `e` follows from Lemma IMG up to `P` by
  `He.he_DI` (`q ≥ 2`) or by `Gw.gwI_epsP` (`q = 1`: `e ∈ (P, evZ(P))`);
* otherwise (`e < φ(q+1, 0)`, THE ZERO BASE, only for `q ≥ Γ_{ρ+1}`): `ϑᵖ(Ω₁·q + ν) = φ(q, i₀ + ν)` for `ν ≤ r`
  (`φ(q, ·)` has no fixed point below `φ(q+1, 0)`), and Lemma IMG at `e` by the reach test going down
  (`He.he_img_down`) with `E' = q + 1` (`r = 0`), the previous point (`r` a successor) or `ϑᵖ(Ω₁·q + c')`
  (`r = c' + ω^z` a limit): the `ε`-numbers in between have a lower level, or the level `q` with
  `ζ ≤ logend(r'') < z` (`he_img_zb`).

* `he_rep` (**EVERY `ε`-NUMBER IN `(x, Γ_{x+2})` OTHER THAN `Γ_{x+1}` IS `ϑˣ(Ω₁·q + r)`**), `he_noSC` (**NO STRONGLY
  CRITICAL NUMBER IN `(Γ_{x+1}, Γ_{x+2})`**), `he_N_lt1`, `he_img_zb` (**THE ZERO BASE**), `he_img_G1` (**LEMMA IMG
  BELOW `Γ_{ρ+2}`**), `he_pkg_G1`.

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.He

open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gw
  Googology.Trans.PoR.InaccPsi.R2.Gq Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gh Googology.Trans.PoR.InaccPsi.R2.Hb Googology.Trans.PoR.InaccPsi.R2.Gz
open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gb

/-- A point of `range φ(q+1, ·)` is at least `φ(q+1, 0)`. -/
theorem he_P_ge {q v : Ordinal.{0}} (hv : LuP (q + 1) v) : veblen (q + 1) 0 ≤ v := by
  obtain ⟨b, rfl⟩ := hv; exact (isNormal_veblen _).monotone zero_le

/-- Below `φ(q+1, 0)` no ordinal is a fixed point of `φ(q, ·)`. -/
theorem he_nofix {q y : Ordinal.{0}} (hy : y < veblen (q + 1) 0) : y < veblen q y := by
  rcases (right_le_veblen q y).lt_or_eq with h | h
  · exact h
  · exact absurd (he_P_ge (luP_succ.2 h.symm)) (not_le.2 hy)

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **EVERY `ε`-NUMBER `v ∈ (x, Γ_{x+2})`, `v ≠ Γ_{x+1}`, IS `ϑˣ(Ω₁·q + r)`** with `1 ≤ q`, `q, r ∈ Tˣ ∩ Ω₁`. -/
theorem he_rep {v : Ordinal.{0}} (hvE : InE v) (hxv : x < v) (hv : v < gq 1 x) (hvG : v ≠ lgG x) :
    ∃ q r, 1 ≤ q ∧ q ∈ Tset x ∧ q < Om1 ∧ r ∈ Tset x ∧ r < Om1 ∧ glA q r x = v := by
  obtain ⟨hGT, -, hG1, -⟩ := gm1_facts hx hx1
  have hv1 : v < Om1 := hv.trans hG1
  have hvT : v ∈ Tset x := vz_T_down hx hx1 hGT hG1 hv.le
  obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hx hx1 hvT hxv.le hv1 (inE_indec hvE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξv]; exact hxv, by rw [hξv]; exact hvE⟩
  obtain ⟨h1T, h1Ω⟩ := gm1_one_T hx hx1
  have h1x : (1 : Ordinal.{0}) < x := Lu.lu_one_lt_E hx
  have hξk : ξ < Om1 * Om1 + 1 :=
    lgLt_of_vt_lt hx hx1 hξT hξ2 h1T h1Ω (by rw [hξv]; exact h1x.trans hxv) (by rw [hξv]; exact hv)
  rcases lt_or_ge ξ (Om1 * Om1) with hξs | hξs
  · obtain ⟨hq1, hrT, hr1, hdec⟩ := lu_split hx hx1 hξT hξ2 hΩξ
    have hqT : ξ / Om1 ∈ Tset x := lgQuot_mem hx hx1 hξT hξs
    have hqΩ : ξ / Om1 < Om1 := (Ordinal.lt_mul_iff_div_lt (Ordinal.omega_pos 1).ne').1 hξs
    refine ⟨ξ / Om1, ξ % Om1, hq1, hqT, hqΩ, hrT, hr1, ?_⟩
    show vt x (Om1 * (ξ / Om1) + ξ % Om1) = v
    rw [hdec, hξv]
  · exfalso
    have hξe : ξ = Om1 * Om1 := le_antisymm (Order.lt_add_one_iff.1 hξk) hξs
    apply hvG
    rw [← hξv, hξe, ← lgV_eq hx hx1]
    rfl

/-- **NO STRONGLY CRITICAL NUMBER IN `(Γ_{x+1}, Γ_{x+2})`**: `φ(v, 0) > v` there (`v` an `ε`-number). -/
theorem he_noSC {v : Ordinal.{0}} (hvE : InE v) (hGv : lgG x < v) (hv : v < gq 1 x) : v < veblen v 0 := by
  obtain ⟨-, hxG, -, -, -⟩ := lgG_facts hx hx1
  obtain ⟨q, r, hq1, hqT, hqΩ, hrT, hr1, hev⟩ := he_rep hx hx1 hvE (hxG.trans hGv) hv hGv.ne'
  obtain ⟨-, -, -, -, hqv, -⟩ := glA_facts hx hx1 hq1 hqT hqΩ hrT hr1
  rw [hev] at hqv
  rcases (left_le_veblen v 0).lt_or_eq with h | h
  · exact h
  · exfalso
    have hq1v : q + 1 < v := (ev_isSuccLimit_of_inE hvE).add_one_lt hqv
    have hP : LuP (q + 1) v := by
      refine ⟨veblen v 0, ?_⟩
      rw [veblen_veblen_of_lt hq1v, ← h]
    have hn := glA_notP hx hx1 hq1 hqT hqΩ hrT hr1
    rw [hev] at hn
    exact hn hP

/-- **`N_q(P) < Γ_{x+2}`** for `P, q + 1 < Γ_{x+2}`. -/
theorem he_N_lt1 {q P : Ordinal.{0}} (hq : q + 1 < gq 1 x) (hP : P < gq 1 x) : hcN q P < gq 1 x := by
  obtain ⟨hkT, hk1⟩ := gm1_T hx hx1 hq
  obtain ⟨hPT, hP1⟩ := gm1_T hx hx1 hP
  have h1 : (1 : Ordinal.{0}) ≤ q + 1 := le_add_self
  have hfix : veblen q (glA (q + 1) P x) = glA (q + 1) P x :=
    luP_succ.1 (glA_P hx hx1 h1 hkT hk1 hPT hP1)
  obtain ⟨-, -, -, -, -, hPa⟩ := glA_facts hx hx1 h1 hkT hk1 hPT hP1
  exact (hcN_le hfix hPa).trans_lt (lgVt_lt_low hx hx1 hkT hk1 hPT hP1 (gm1_one_T hx hx1).1
    (gm1_one_T hx hx1).2 hq hP)

end Base

section Img

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **THE ZERO BASE**: Lemma IMG at `e = ϑᵖ(Ω₁·q + r) ∈ (Γ_{ρ+1}, Γ_{ρ+2})` with `e < φ(q+1, 0)` (no fixed point of
`φ(q, ·)` below `e`), given Lemma IMG below `e`. -/
theorem he_img_zb {q r : Ordinal.{0}} (hq1 : 1 ≤ q) (hqT : q ∈ Tset ρ) (hqΩ : q < Om1) (hrT : r ∈ Tset ρ)
    (hr1 : r < Om1) (hGe : lgG ρ < glA q r ρ) (he1 : glA q r ρ < gq 1 ρ) (hzb : glA q r ρ < veblen (q + 1) 0)
    (IH : ∀ u, u < glA q r ρ → GnI ρ δ u) : GnI ρ δ (glA q r ρ) := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  set e := glA q r ρ with hedef
  obtain ⟨-, hρe, -, hE, hqe, hre⟩ := glA_facts hρE hρ1 hq1 hqT hqΩ hrT hr1
  obtain ⟨-, hρG, -, -, -⟩ := lgG_facts hρE hρ1
  have hqq : q < gq 1 ρ := hqe.trans he1
  have h0T : (0 : Ordinal.{0}) ∈ Tset ρ := mem_T_of_le hρE hρ1 zero_le
  have h01 : (0 : Ordinal.{0}) < Om1 := hρE.pos.trans hρ1
  have h0q : (0 : Ordinal.{0}) < gq 1 ρ := hρE.pos.trans (gm1_facts hρE hρ1).2.1
  -- the level is at least `Γ_{ρ+1}`
  have hGq : lgG ρ ≤ q := by
    by_contra hlt
    push Not at hlt
    have hP := hc_LuP_of_fix (hc_G_fix hρE hρ1 hq1 hlt)
    exact absurd ((he_P_ge hP).trans hGe.le) (not_le.2 hzb)
  have hρq : ρ < q := hρG.trans_le hGq
  set Z0 := veblen (q + 1) 0 with hZ0
  have hZ0I : Indec Z0 := inE_indec (Gg.gg_veblen_eps (by simp))
  -- the closed form `ϑᵖ(Ω₁·q + ν) = φ(q, i₀ + ν)`
  obtain ⟨i0, hi0⟩ := glA_P hρE hρ1 hq1 hqT hqΩ h0T h01
  have hG0 : glA q 0 ρ = veblen q i0 := hi0.symm
  have hle0 : glA q 0 ρ ≤ e := (glA_le_iff hρE hρ1 hq1 hqT hqΩ h0T h01 hrT hr1).2 zero_le
  have hi0Z : i0 < Z0 := ((right_le_veblen q i0).trans (hG0 ▸ hle0)).trans_lt hzb
  have hrZ : r < Z0 := hre.trans hzb
  have hcf : ∀ ν, ν ≤ r → glA q ν ρ = veblen q (i0 + ν) := by
    intro ν hν
    have hνq : 0 + ν < gq 1 ρ := by rw [zero_add]; exact (hν.trans_lt hre).trans he1
    have := hc_glAV hρE hρ1 hq1 hqq h0q hG0 ν hνq
      (fun ν' h' _ => he_nofix (hZ0I.add_lt hi0Z ((h'.trans hν).trans_lt hrZ)))
    rwa [zero_add] at this
  have heV : e = veblen q (i0 + r) := hcf r le_rfl
  -- the `ε`-numbers below `e` above `Γ_{ρ+1}`: lower level, or a point of `φ(q, ·)`
  have hlev : ∀ u, InE u → lgG ρ < u → u < e → ∃ q' r', 1 ≤ q' ∧ q' ∈ Tset ρ ∧ q' < Om1 ∧ r' ∈ Tset ρ ∧
      r' < Om1 ∧ glA q' r' ρ = u ∧ q' ≤ q ∧ (q' = q → LuP q u) := by
    intro u hu hGu hue
    obtain ⟨q', r', hq'1, hq'T, hq'Ω, hr'T, hr'1, hu'⟩ :=
      he_rep hρE hρ1 hu (hρG.trans hGu) (hue.trans he1) hGu.ne'
    have hq'q : q' ≤ q := by
      by_contra hlt
      push Not at hlt
      have hP : LuP (q + 1) u := by
        rw [← hu']
        exact (gq_veb_level hρE hρ1 hq'1 hq'T hq'Ω hr'T hr'1 le_add_self).2 (Order.add_one_le_of_lt hlt)
      exact absurd ((he_P_ge hP).trans hue.le) (not_le.2 hzb)
    refine ⟨q', r', hq'1, hq'T, hq'Ω, hr'T, hr'1, hu', hq'q, fun e' => ?_⟩
    subst e'
    rw [← hu']
    exact (gq_veb_level hρE hρ1 hq1 hq'T hq'Ω hr'T hr'1 hq1).2 le_rfl
  -- the reach of such a `u`
  have hreach : ∀ q' r' u, 1 ≤ q' → q' ∈ Tset ρ → q' < Om1 → r' ∈ Tset ρ → r' < Om1 → glA q' r' ρ = u →
      IsLh1 u (u * (1 + q') + hcE q' + luZeta ρ q' r') ∧ luZeta ρ q' r' < u := by
    intro q' r' u hq'1 hq'T hq'Ω hr'T hr'1 hu'
    obtain ⟨H1, H2, -⟩ := he_lhq hρE hρ1 hq'1 hq'T hq'Ω hr'T hr'1
    rw [hu'] at H1 H2
    exact ⟨H1, H2⟩
  rcases zero_or_succ_or_isSuccLimit r with hr0 | ⟨r', hr'⟩ | hlim
  · -- `r = 0`: the reach test with `E' = q + 1`
    subst hr0
    have hqe1 : q + 1 < e := (ev_isSuccLimit_of_inE hE).add_one_lt hqe
    refine he_img_down h hq1 hqT hqΩ hrT hr1 (hρq.trans (lt_add_one q)) (lt_add_one q) hqe1
      (fun u hu hq1u hue => ?_) IH
    obtain ⟨q', r', hq'1, hq'T, hq'Ω, hr'T, hr'1, hu', hq'q, hP⟩ :=
      hlev u hu ((hGq.trans_lt (lt_add_one q)).trans hq1u) hue
    obtain ⟨H1, H2⟩ := hreach q' r' u hq'1 hq'T hq'Ω hr'T hr'1 hu'
    refine ⟨q', _, hq'q, H1, H2, fun e' => ?_⟩
    exfalso
    have hmin := glA_min hρE hρ1 hq1 hqT hqΩ h0T h01 (hP e') (hρq.trans ((lt_add_one q).trans hq1u))
      (hρE.pos.trans (hρq.trans ((lt_add_one q).trans hq1u))) ((lt_add_one q).trans hq1u)
      (fun σ hσ => absurd hσ (not_lt.2 zero_le))
    exact absurd hue (not_lt.2 hmin)
  · -- `r = r' + 1`: the reach test with the previous point
    have hrr : r = r' + 1 := by rw [← hr', succ_eq_add_one]
    have hr'r : r' < r := by rw [hrr]; exact lt_add_one r'
    obtain ⟨hr'T, hr'1⟩ : r' ∈ Tset ρ ∧ r' < Om1 :=
      ⟨vz_T_down hρE hρ1 hrT hr1 hr'r.le, hr'r.trans hr1⟩
    have hE'e : glA q r' ρ < e := glA_lt_of hρE hρ1 hq1 hqT hqΩ hr'T hrT hr1 hr'r
    obtain ⟨-, hρE', -, -, hqE', -⟩ := glA_facts hρE hρ1 hq1 hqT hqΩ hr'T hr'1
    refine he_img_down h hq1 hqT hqΩ hrT hr1 hρE' hqE' hE'e (fun u hu hE'u hue => ?_) IH
    obtain ⟨q', r'', hq'1, hq'T, hq'Ω, hr''T, hr''1, hu', hq'q, hP⟩ :=
      hlev u hu ((hGq.trans_lt hqE').trans hE'u) hue
    obtain ⟨H1, H2⟩ := hreach q' r'' u hq'1 hq'T hq'Ω hr''T hr''1 hu'
    refine ⟨q', _, hq'q, H1, H2, fun e' => ?_⟩
    exfalso
    obtain ⟨j, rfl⟩ := hP e'
    rw [hcf r' hr'r.le] at hE'u
    have hue' : veblen q j < veblen q (i0 + r' + 1) := by rw [add_assoc, ← hrr, ← heV]; exact hue
    have h1 := (veblen_lt_veblen_iff_right).1 hE'u
    have h2 := (veblen_lt_veblen_iff_right).1 hue'
    exact absurd (Order.lt_add_one_iff.1 h2) (not_le.2 h1)
  · -- `r` a limit: the reach test with `E' = ϑᵖ(Ω₁·q + c')`, `r = c' + ω^z`
    have hr0 : r ≠ 0 := hlim.bot_lt.ne'
    obtain ⟨c', hcs, -, hc'r⟩ := lg_split hr0
    set z := lg r with hzdef
    obtain ⟨hc'T, hc'1⟩ : c' ∈ Tset ρ ∧ c' < Om1 := ⟨vz_T_down hρE hρ1 hrT hr1 hc'r.le, hc'r.trans hr1⟩
    have hE'e : glA q c' ρ < e := glA_lt_of hρE hρ1 hq1 hqT hqΩ hc'T hrT hr1 hc'r
    obtain ⟨-, hρE', -, -, hqE', -⟩ := glA_facts hρE hρ1 hq1 hqT hqΩ hc'T hc'1
    have hz' : luZeta ρ q r = z := by
      have := hc_zetaG hρE hρ1 hq1 hqq h0q hG0 (by rw [zero_add]; exact hre.trans he1)
        (fun ν' h' _ => he_nofix (hZ0I.add_lt hi0Z (h'.trans_lt hrZ))) hlim
      rwa [zero_add] at this
    refine he_img_down h hq1 hqT hqΩ hrT hr1 hρE' hqE' hE'e (fun u hu hE'u hue => ?_) IH
    obtain ⟨q', r'', hq'1, hq'T, hq'Ω, hr''T, hr''1, hu', hq'q, -⟩ :=
      hlev u hu ((hGq.trans_lt hqE').trans hE'u) hue
    obtain ⟨H1, H2⟩ := hreach q' r'' u hq'1 hq'T hq'Ω hr''T hr''1 hu'
    refine ⟨q', _, hq'q, H1, H2, fun e' => ?_⟩
    subst e'
    rw [← hu'] at hE'u hue
    have hc'r'' : c' < r'' := (glA_lt_iff hρE hρ1 hq1 hqT hqΩ hc'T hc'1 hr''T hr''1).1 hE'u
    have hr''r : r'' < r := (glA_lt_iff hρE hρ1 hq1 hqT hqΩ hr''T hr''1 hrT hr1).1 hue
    have hr''0 : r'' ≠ 0 := (lt_of_le_of_lt zero_le hc'r'').ne'
    obtain ⟨δ', hδ'⟩ : ∃ δ', r'' = c' + δ' := ⟨r'' - c', (Ordinal.add_sub_cancel_of_le hc'r''.le).symm⟩
    have hδ0 : δ' ≠ 0 := by rintro rfl; rw [add_zero] at hδ'; exact absurd hδ' hc'r''.ne'
    have hδlt : δ' < ω ^ z := by
      have : c' + δ' < c' + ω ^ z := by rw [← hδ', ← hcs]; exact hr''r
      exact (add_lt_add_iff_left _).1 this
    have hlgd : lg r'' < z := by
      rw [hδ', gz_lg_add _ hδ0]
      by_contra hge; push Not at hge
      obtain ⟨δ'', hδs, -, -⟩ := lg_split hδ0
      have h1 : ω ^ z ≤ ω ^ lg δ' := opow_le_opow_right omega0_pos hge
      have h2 : ω ^ lg δ' ≤ δ' := (le_add_self (a := ω ^ lg δ') (b := δ'')).trans_eq hδs.symm
      exact absurd hδlt (not_lt.2 (h1.trans h2))
    rw [hz']
    exact lu_zeta_le_lg.trans_lt hlgd

/-- **LEMMA IMG BELOW `Γ_{ρ+2} = ϑᵖ(Ω₁·Ω₁ + 1)`.** -/
theorem he_img_G1 : ∀ v, v < gq 1 ρ → GnI ρ δ v := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  obtain ⟨-, hρG, -, -, -⟩ := lgG_facts hρE hρ1
  refine gnImg_of_eps h (fun v hv => gm1_T hρE hρ1 hv) (fun e he _ heB IHe => ?_)
  rcases lt_trichotomy e (lgG ρ) with hlt | heq | hgt
  · exact gnI_lowG h hlt
  · rw [heq]; exact gnI_G h
  obtain ⟨q, r, hq1, hqT, hqΩ, hrT, hr1, hev⟩ := he_rep hρE hρ1 he (hρG.trans hgt) heB hgt.ne'
  subst hev
  obtain ⟨-, -, -, -, hqe, -⟩ := glA_facts hρE hρ1 hq1 hqT hqΩ hrT hr1
  have hqq1 : q + 1 < gq 1 ρ := (ev_isSuccLimit_of_inE (gm1_facts hρE hρ1).2.2.2).add_one_lt (hqe.trans heB)
  by_cases hz : glA q r ρ < veblen (q + 1) 0
  · exact he_img_zb h hq1 hqT hqΩ hrT hr1 hgt heB hz IHe
  push Not at hz
  obtain ⟨a, ha1, ha2⟩ := hb_floor (q + 1) (j0 := 0) hz
  set P := veblen (q + 1) a with hPdef
  have hPfix : veblen q P = P := veblen_veblen_of_lt (lt_add_one q) a
  have hPe : P < glA q r ρ := lt_of_le_of_ne ha1 (fun e' =>
    glA_notP hρE hρ1 hq1 hqT hqΩ hrT hr1 (by rw [← e']; exact ⟨a, rfl⟩))
  have heN : glA q r ρ < hcN q P := by
    by_contra hge
    push Not at hge
    obtain ⟨b, hb⟩ := hc_LuP_of_fix (hcN_fix q P)
    have hab : a < b := by
      have := hcN_gt q P; rw [hPdef, ← hb] at this; exact (veblen_lt_veblen_iff_right).1 this
    have hba : b < a + 1 := by
      have := hge.trans_lt ha2; rw [← hb] at this; exact (veblen_lt_veblen_iff_right).1 this
    exact absurd (Order.lt_add_one_iff.1 hba) (not_le.2 hab)
  have hGP : lgG ρ ≤ P := by
    rcases lt_or_ge q (lgG ρ) with hqG | hGq
    · obtain ⟨b, hb⟩ := hc_LuP_of_fix (hc_G_fix hρE hρ1 hq1 hqG)
      have hba : b < a + 1 := by
        have := hgt.trans ha2; rw [← hb] at this; exact (veblen_lt_veblen_iff_right).1 this
      rw [← hb]
      exact (isNormal_veblen _).monotone (Order.lt_add_one_iff.1 hba)
    · exact (hGq.trans (le_self_add.trans (left_le_veblen (q + 1) 0))).trans
        ((isNormal_veblen _).monotone zero_le)
  have hρP : ρ < P := hρG.trans_le hGP
  have hPq : P < gq 1 ρ := hPe.trans heB
  have hNq : hcN q P < gq 1 ρ := he_N_lt1 hρE hρ1 hqq1 hPq
  have IHP : ∀ v, v ≤ P → GnI ρ δ v := fun v hv => IHe v (hv.trans_lt hPe)
  rcases lt_or_ge q 2 with hq2 | hq2
  · -- the level `1`: `e ∈ (P, evZ(P))`
    have hq : q = 1 := by
      refine le_antisymm ?_ hq1
      have : q < 1 + 1 := by rwa [one_add_one_eq_two]
      exact Order.lt_add_one_iff.1 this
    subst hq
    have hPE : InE P := Gg.gg_veblen_eps (by simp)
    exact gwI_epsP h hPE hρP hPq he hPe heN IHe
  · exact (he_DI h q hq2 (hqe.trans heB)).2 P hPfix hρP hNq IHP _ heN

/-- **LEMMA IMG (gated) FOR A SPECIFIED FUNCTION BELOW `Γ_{ρ+2}`.** -/
theorem he_pkg_G1 {g : Ordinal.{0}} {C : Finset Ordinal.{0}} {T : Ordinal.{0} → Ordinal.{0}} (hgρ : g < ρ)
    (hC : ∀ c ∈ C, c < ρ) (hT : T ρ < gq 1 ρ) (hex : GjEx g C T) : GhPkg g ρ δ T :=
  gnPkg_of_GnI h hgρ hC (he_img_G1 h _ hT) hex

end Img

end Googology.Trans.PoR.InaccPsi.R2.He

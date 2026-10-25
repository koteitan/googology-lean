import Googology.Trans.PoR.InaccPsi.R2.GvA

/-!
# LEMMA EXACT FOR `ε_{Γ_{x+1}+ν}` UP TO `ζ_{Γ_{x+1}+1}`; THE INDEX OF A BOUND IS A CODE

`Gp.gp_b_pi_code` and `Gp.gp_b_eN` ask the `ε`-index `ν` of the base reading `φ(1, Γ_{x+1} + ν)` below `Γ_{x+1}`.
Here `ν` may be any ordinal below `ζ_{Γ_{x+1}+1}` (`evZ (lgG x)`), the bound of the readings of every gated digit
system (`Gs.GsD.R_lt_Z`):

* `gw_lt_evA` (**`τ + ν < ε_{τ+1+ν}` below `ζ_{τ+1}`**), `gw_G_add_lt`, `gw_glA_eq` (**`ϑˣ(Ω₁ + Γ_{x+1} + ν) =
  ε_{Γ_{x+1}+1+ν}` for every `ν < ζ_{Γ_{x+1}+1}`**, from `Te.teGlA_eq`), `gw_evA_pi`, `gw_b_pi_code` (**Lemma EXACT for
  `φ(1, gpI ρ + ν(ρ))` for every code index `ν(ρ) < ζ_{Γ_{ρ+1}+1}`**), `gw_b_eN`, `gw_ba_lt`, `gw_b_Z`, `gw_ba_pi`;
* `gw_cl_mod` (**the remainder of a code modulo `G` is a code**), `gw_cl_of_G_add` (**`G + c` a code ⇒ `c` a code**),
  `gw_lt_veb` (**`G + c < φ(1, G + c)` for `0 < c < ζ_{G+1}`**), `gw_self_lt`, `gw_cl_gate` (**THE CODE-GATE CONDITION
  OF AN INDEX READ BY A GATED DIGIT SYSTEM `E`**: `φ(1, G + c)` a code over `Z` ⇒ `g_E(c) < Z`), `gw_veb_lt1`,
  `gw_cover` (**`0 < μ < ζ_{G+1}` ⇒ `μ < φ(1, G + d)` for some `d < μ`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gw

open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Go
  Googology.Trans.PoR.InaccPsi.R2.Gp
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## Lemma EXACT below `ζ_{Γ_{x+1}+1}` -/

/-- **`τ + ν < ε_{τ+1+ν}` for `ν < ζ_{τ+1}`.** -/
theorem gw_lt_evA {τ ν : Ordinal.{0}} (hτ : InE τ) (hν : ν < evZ τ) : τ + ν < evA τ (1 + ν) := by
  have hE := evA_E τ (1 + ν)
  have h1 : τ < evA τ (1 + ν) := by
    have := (evA_lt_iff (x := τ) (a := 0) (b := 1 + ν)).2 (lt_of_lt_of_le zero_lt_one le_self_add)
    rwa [evA_zero hτ] at this
  exact (inE_indec hE).add_lt h1 (lt_evA_of_lt_evZ hτ hν)

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem gw_G_add_lt {ν : Ordinal.{0}} (hν : ν < evZ (lgG x)) : lgG x + ν < gq 1 x :=
  (add_lt_evZ (lt_evZ _) hν).trans (gn_evZG_lt1 hx hx1)

/-- **`ϑˣ(Ω₁ + Γ_{x+1} + ν) = ε_{Γ_{x+1}+1+ν}` for every `ν < ζ_{Γ_{x+1}+1}`.** -/
theorem gw_glA_eq {ν : Ordinal.{0}} (hν : ν < evZ (lgG x)) :
    Gl.glA 1 (lgG x + ν) x = evA (lgG x) (1 + ν) := by
  obtain ⟨-, -, -, hGE, -⟩ := lgG_facts hx hx1
  exact Te.teGlA_eq hx hx1 ν (gw_G_add_lt hx hx1 hν) fun ν' h _ => gw_lt_evA hGE (lt_of_le_of_lt h hν)

/-- **The offset of a code index**: `ε_{b(x)+1} = ϑˣ(Ω₁ + Γ_{x+1} + ν + 1)` for `b(x) = φ(1, gpI x + ν)`. -/
theorem gw_b_eN {ν : Ordinal.{0}} (hω : ω ≤ ν) (hν : ν < evZ (lgG x)) :
    eN (veblen 1 (gpI x + ν)) = glA 1 (lgG x + (ν + 1)) x := by
  have hν1 : ν + 1 < evZ (lgG x) := (ev_isSuccLimit_of_inE (evZ_E _)).add_one_lt hν
  rw [gw_glA_eq hx hx1 hν1, one_add_of_omega0_le (hω.trans le_self_add), go_eN_veb, add_assoc]; rfl

theorem gw_ba_lt {ν : Ordinal.{0}} (hν : ν < evZ (lgG x)) : lgG x + (ν + 1) < gq 1 x :=
  gw_G_add_lt hx hx1 ((ev_isSuccLimit_of_inE (evZ_E _)).add_one_lt hν)

theorem gw_b_Z {ν : Ordinal.{0}} (hν : ν < evZ (lgG x)) : eN (veblen 1 (gpI x + ν)) < evZ (lgG x) := by
  refine go_eN_lt_evZ ?_
  have hZ := evZ_E (lgG x)
  have hGE := (lgG_facts hx hx1).2.2.2.1
  have hi : gpI x < evZ (lgG x) := (evIx_le hGE).trans_lt (lt_evZ _)
  have := (isNormal_veblen 1).strictMono ((inE_indec hZ).add_lt hi hν)
  rwa [show veblen 1 (evZ (lgG x)) = evZ (lgG x) from epsilon_evZ _] at this

end Base

/-- **Lemma EXACT for `ε_{Γ_{ρ+1}+1+ν}`** for every `ν ∈ Tᵖ[σ]` below `ζ_{Γ_{ρ+1}+1}` with `π(ν) < ζ_{Γ_{σ+1}+1}`. -/
theorem gw_evA_pi {σ ρ ν : Ordinal.{0}} (hB : Bases σ ρ) (hνT : ν ∈ TB ρ σ) (hν : ν < evZ (lgG ρ))
    (hν' : pi σ ρ ν < evZ (lgG σ)) :
    evA (lgG ρ) (1 + ν) ∈ TB ρ σ ∧ pi σ ρ (evA (lgG ρ) (1 + ν)) = evA (lgG σ) (1 + pi σ ρ ν) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨o1, o2⟩ := one_TB hB
  obtain ⟨g1, g2⟩ : lgG ρ ∈ TB ρ σ ∧ pi σ ρ (lgG ρ) = lgG σ := goGl.ba_pi σ ρ hB
  obtain ⟨s1, s2⟩ := pi_add hB g1 hνT
  rw [g2] at s2
  have hs1 : lgG ρ + ν < Om1 := (gm1_T hB.2.1 hρ1 (gw_G_add_lt hB.2.1 hρ1 hν)).2
  have h := Gl.glA_pi hB o1 (Gl.gl_one_T hB.2.1 hρ1).2 s1 hs1
  rw [o2, s2, gw_glA_eq hB.2.1 hρ1 hν, gw_glA_eq hB.1 hσ1 hν'] at h
  exact h

/-- **Lemma EXACT for `φ(1, gpI ρ + ν(ρ))` with a code index `ν` below `ζ_{Γ_{ρ+1}+1}`.** -/
theorem gw_b_pi_code {σ ρ ν ν' : Ordinal.{0}} (hB : Bases σ ρ) (hνT : ν ∈ TB ρ σ) (hν : ν < evZ (lgG ρ))
    (hν' : ν' < evZ (lgG σ)) (hω : ω ≤ ν) (hπ : pi σ ρ ν = ν') :
    veblen 1 (gpI ρ + ν) ∈ TB ρ σ ∧ pi σ ρ (veblen 1 (gpI ρ + ν)) = veblen 1 (gpI σ + ν') := by
  obtain ⟨e1, e2⟩ := gw_evA_pi hB hνT hν (by rw [hπ]; exact hν')
  have hωσ : ω < σ := omega0_lt_inE hB.1
  have hωT : ω ∈ TB ρ σ := mem_TB_of_lt hB hωσ
  have hω' : ω ≤ ν' := by
    rw [← hπ, ← pi_lt hB hωσ]
    exact ((pi_bijOn hB).2.le_iff_le hωT hνT).2 hω
  rw [hπ, one_add_of_omega0_le hω'] at e2
  rw [one_add_of_omega0_le hω] at e1 e2
  exact ⟨e1, e2⟩

/-- Lemma EXACT for the offset `Γ_{ρ+1} + ν + 1`. -/
theorem gw_ba_pi {σ ρ ν ν' : Ordinal.{0}} (hB : Bases σ ρ) (h : ν ∈ TB ρ σ ∧ pi σ ρ ν = ν') :
    lgG ρ + (ν + 1) ∈ TB ρ σ ∧ pi σ ρ (lgG ρ + (ν + 1)) = lgG σ + (ν' + 1) := by
  obtain ⟨g1, g2⟩ : lgG ρ ∈ TB ρ σ ∧ pi σ ρ (lgG ρ) = lgG σ := goGl.ba_pi σ ρ hB
  obtain ⟨o1, o2⟩ := one_TB hB
  obtain ⟨s1, s2⟩ := pi_add hB h.1 o1
  obtain ⟨t1, t2⟩ := pi_add hB g1 s1
  exact ⟨t1, by rw [t2, s2, g2, h.2, o2]⟩

/-! ## The index of a bound is a code -/

section Cl

variable {Z : Ordinal.{0}}

theorem gw_G_pos : (0 : Ordinal.{0}) < gcG 0 := (gcG_SC 0).1

theorem gw_mod_eq {q r : Ordinal.{0}} (hr : r < gcG 0) : (gcG 0 * q + r) % gcG 0 = r := by
  rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr]

theorem gw_G_dvd_prin {v : Ordinal.{0}} (hp : IsPrincipal (· + ·) v) (hv0 : v ≠ 0) (hGv : gcG 0 ≤ v) :
    v % gcG 0 = 0 := by
  obtain ⟨e, he⟩ := Bt.prin_eq_opow hp hv0
  have eG : ω ^ gcG 0 = gcG 0 := Low.opow_eq_self_of_SC (gcG_SC 0)
  have hGe : gcG 0 ≤ e := by
    by_contra hlt
    push Not at hlt
    have := (opow_lt_opow_iff_right one_lt_omega0).2 hlt
    rw [eG, ← he] at this
    exact absurd hGv (not_le.2 this)
  have hd := opow_dvd_opow ω hGe
  rw [eG, ← he] at hd
  exact (Ordinal.dvd_iff_mod_eq_zero).1 hd

/-- **The remainder of a code modulo `G` is a code.** -/
theorem gw_cl_mod (hZ : SC Z) (hZ1 : Z ≤ Om 1) {y : Ordinal.{0}} (h : GxCl Z {gcG 0} y) :
    GxCl Z {gcG 0} (y % gcG 0) := by
  have hGO := gcG_Om1_lt 0
  induction h with
  | @small x hx => rw [Ordinal.mod_eq_of_lt ((hx.trans_le hZ1).trans hGO)]; exact GxCl.small hx
  | om => rw [Ordinal.mod_eq_of_lt hGO]; exact GxCl.om
  | @atom s hs =>
    rw [Set.mem_singleton_iff] at hs
    rw [hs, Ordinal.mod_self]; exact GxCl.zero hZ.1
  | @add x y _ hy ihx ihy =>
    have hx' := Ordinal.div_add_mod x (gcG 0)
    have hy' := Ordinal.div_add_mod y (gcG 0)
    have hr : x % gcG 0 < gcG 0 := Ordinal.mod_lt x gw_G_pos.ne'
    rcases lt_or_ge y (gcG 0) with hyG | hyG
    · have e : x + y = gcG 0 * (x / gcG 0) + (x % gcG 0 + y) := by
        conv_lhs => rw [← hx']
        rw [add_assoc]
      rw [e, gw_mod_eq (gr_G_prin hr hyG)]
      exact GxCl.add ihx hy
    · have hq : 1 ≤ y / gcG 0 := by
        rw [Order.one_le_iff_pos]
        exact Ordinal.div_pos gw_G_pos.ne' |>.2 hyG
      obtain ⟨b', hb'⟩ := exists_add_of_le hq
      have hs : y % gcG 0 < gcG 0 := Ordinal.mod_lt y gw_G_pos.ne'
      have e1 : x % gcG 0 + gcG 0 * (1 + b') = gcG 0 * (1 + b') := by
        rw [mul_add, mul_one, ← add_assoc, gr_G_prin.add_eq_right hr]
      have e : x + y = gcG 0 * (x / gcG 0 + y / gcG 0) + y % gcG 0 := by
        conv_lhs => rw [← hx', ← hy']
        rw [hb', ← add_assoc (gcG 0 * (x / gcG 0) + x % gcG 0), add_assoc (gcG 0 * (x / gcG 0)) (x % gcG 0), e1,
          ← mul_add]
      rw [e, gw_mod_eq hs]
      exact ihy
  | @phi a b ha hb _ _ =>
    rcases lt_or_ge (veblen a b) (gcG 0) with hv | hv
    · rw [Ordinal.mod_eq_of_lt hv]; exact GxCl.phi ha hb
    · rw [gw_G_dvd_prin (gr_veb_prin a b) veblen_pos.ne' hv]; exact GxCl.zero hZ.1

theorem gw_cl_Gmul (hZ : SC Z) : ∀ n : ℕ, GxCl Z {gcG 0} (gcG 0 * n)
  | 0 => by rw [Nat.cast_zero, mul_zero]; exact GxCl.zero hZ.1
  | n + 1 => by
    rw [Nat.cast_succ, mul_add_one]
    exact GxCl.add (gw_cl_Gmul hZ n) (GxCl.atom (Set.mem_singleton _))

/-- **`G + c` a code over a strongly critical `Z ≤ Ω₁` ⇒ `c` a code.** -/
theorem gw_cl_of_G_add (hZ : SC Z) (hZ1 : Z ≤ Om 1) {c : Ordinal.{0}} (h : GxCl Z {gcG 0} (gcG 0 + c)) :
    GxCl Z {gcG 0} c := by
  rcases le_or_gt (gcG 0 * ω) c with hc | hc
  · rwa [add_eq_right_iff_mul_omega0_le.2 hc] at h
  · have hc' := Ordinal.div_add_mod c (gcG 0)
    have hs : c % gcG 0 < gcG 0 := Ordinal.mod_lt c gw_G_pos.ne'
    have hq : c / gcG 0 < ω := (Ordinal.lt_mul_iff_div_lt gw_G_pos.ne').1 hc
    obtain ⟨n, hn⟩ := lt_omega0.1 hq
    have e : gcG 0 + c = gcG 0 * (1 + c / gcG 0) + c % gcG 0 := by
      conv_lhs => rw [← hc']
      rw [mul_add, mul_one, add_assoc]
    have hm := gw_cl_mod hZ hZ1 h
    rw [e, gw_mod_eq hs] at hm
    rw [← hc', hn]
    exact GxCl.add (gw_cl_Gmul hZ n) hm

end Cl

/-! ## The indices below `ζ_{G+1}` -/

theorem gw_G_lt_Z : gcG 0 < evZ (gcG 0) := lt_evZ _

/-- **`G + c < φ(1, G + c)` for `0 < c < ζ_{G+1}`.** -/
theorem gw_lt_veb {c : Ordinal.{0}} (hc0 : 0 < c) (hc : c < evZ (gcG 0)) : gcG 0 + c < veblen 1 (gcG 0 + c) := by
  rcases (right_le_veblen 1 (gcG 0 + c)).lt_or_eq with h | h
  · exact h
  · exfalso
    have hfix : Ordinal.epsilon (gcG 0 + c) = gcG 0 + c := h.symm
    have hGc : gcG 0 < gcG 0 + c := lt_add_of_pos_right _ hc0
    have h1 := evZ_le hGc hfix
    exact absurd (add_lt_evZ gw_G_lt_Z hc) (not_lt.2 h1)

/-- `c < φ(1, G + c)` for every `c < ζ_{G+1}`. -/
theorem gw_self_lt {c : Ordinal.{0}} (hc : c < evZ (gcG 0)) : c < veblen 1 (gcG 0 + c) := by
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [add_zero]; exact (gcG_SC 0).1.trans_le (right_le_veblen 1 _)
  · exact (le_add_self : c ≤ gcG 0 + c).trans_lt (gw_lt_veb (pos_iff_ne_zero.2 hc0) hc)

theorem gw_veb_lt_Z {c : Ordinal.{0}} (hc : c < evZ (gcG 0)) : veblen 1 (gcG 0 + c) < evZ (gcG 0) := by
  have := (isNormal_veblen 1).strictMono (add_lt_evZ gw_G_lt_Z hc)
  rwa [show veblen 1 (evZ (gcG 0)) = evZ (gcG 0) from epsilon_evZ _] at this

theorem gw_Z_le1 : evZ (gcG 0) ≤ gcG 1 :=
  evZ_le (gcG_lt zero_lt_one) (gn_veb_fix (gcG_SC 1) (one_lt_omega0.trans
    (omega0_lt_inE (Low.opow_eq_self_of_SC (gcG_SC 1)))))

theorem gw_veb_lt1 {c : Ordinal.{0}} (hc : c < evZ (gcG 0)) : veblen 1 (gcG 0 + c) < gcG 1 :=
  (gw_veb_lt_Z hc).trans_le gw_Z_le1

/-- **`0 < μ < ζ_{G+1}` ⇒ `μ < φ(1, G + d)` for some `d < μ`.** -/
theorem gw_cover {μ : Ordinal.{0}} (hμ0 : 0 < μ) (hμ : μ < evZ (gcG 0)) :
    ∃ d, d < μ ∧ μ < veblen 1 (gcG 0 + d) := by
  rcases zero_or_succ_or_isSuccLimit μ with h0 | ⟨d, hd⟩ | hlim
  · exact absurd h0 hμ0.ne'
  · have hd' : μ = d + 1 := by rw [← hd, Order.succ_eq_add_one]
    have hdμ : d < μ := by rw [hd']; exact lt_add_one d
    refine ⟨d, hdμ, ?_⟩
    rw [hd']
    exact (ev_isSuccLimit_of_inE (omega0_opow_epsilon _)).add_one_lt (gw_self_lt (hdμ.trans hμ))
  · have h := gw_self_lt hμ
    obtain ⟨t, ht, hμt⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ hlim)).1 h
    obtain ⟨d, hd, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    exact ⟨d, hd, hμt.trans_le ((isNormal_veblen 1).monotone htd)⟩

/-- **THE CODE-GATE CONDITION OF AN INDEX**: if `φ(1, G + c)` is a code over a strongly critical `Z ≤ Ω₁` (atom `G`)
and `c` (`0 < c < ζ_{G+1}`) is a code of a gated digit system `E`, then `g_E(c) < Z`. -/
theorem gw_cl_gate (E : GvD) {c Z : Ordinal.{0}} (hcB : c < E.B) (hc0 : 0 < c) (hcZ : c < evZ (gcG 0))
    (hZ : SC Z) (hZ1 : Z ≤ Om 1) (h : GxCl Z {gcG 0} (veblen 1 (gcG 0 + c))) : E.g c < Z := by
  have hOt : Om 1 < gcG 0 + c := (gcG_Om1_lt 0).trans_le le_self_add
  have h1 := gr_cl_veb1 hZ1 hOt (gw_lt_veb hc0 hcZ) h
  have h2 := gw_cl_of_G_add hZ hZ1 h1
  have hZ1' : Z ≤ Om1 := by rw [Br.Om1_eq]; exact hZ1
  exact E.code_gate Z hZ1' hZ.1 (fun _ _ hu hv => hZ.isPrincipal hu hv) (fun _ _ hu hv => hZ.2 _ hu _ hv)
    {gcG 0} (fun s hs => Or.inl (Set.mem_singleton_iff.1 hs)) c h2 hcB

end Googology.Trans.PoR.InaccPsi.R2.Gw

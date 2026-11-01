import Googology.Trans.PoR.InaccPsi.R2.XpKRec

/-!
# XpW: THE `Ω₁`-UNION OF A GENERAL BAND: A SYSTEM AT `φ(L + Ω₁, 0)`, AND THE BAND `G + Ω₁` FROM `Xl.xlW`

* `xpWF B U₀ hU₀ : Ho.HoFam` (the family `xpK B U₀ μ`, `μ < Ω₁`: bound `φ(L + Ω₁, 0)`, gate `g`, base reading
  `φ(ℓ(x) + x, 0)`), `xpW = Ho.hoOU xpWF`;
* `xpW_at` (**THE `Ω₁`-UNION IS A SYSTEM AT THE BOTTOM OF THE NEXT BAND**: `XpAt (B.succ).K.Λ 0 (xpW …)`),
  `xpW_ext` (it extends every `xpK μ`, hence `U₀`);
* `xpAt_congr` (**`XpAt` DEPENDS ONLY ON `L`, ON THE GATE THROUGH ITS CUTS AT `ε`-NUMBERS, AND ON THE READING ABOVE
  THE GATE**);
* `xpBdG1` (the band datum `G + Ω₁`: `HnPk.succ Xf.xfPk`), `xp_at_xlW` (**`Xl.xlW` IS A SYSTEM AT ITS BOTTOM**),
  `xpBandStep` (**THE GENERIC BAND STEP**).

No new axiom.  New definitions: `xpWF`, `xpW`, `xpBdG1`.
-/

set_option autoImplicit false


open Googology.Trans.PoR.InaccPsi.R2.Wm Googology.Trans.PoR.InaccPsi.R2.Wh Googology.Trans.PoR.InaccPsi.R2.Ho
open Googology.Trans.PoR.InaccPsi.R2.Hn Googology.Trans.PoR.InaccPsi.R2.Hl
open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk
open Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Gf
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd
open Googology.Trans.PoR.InaccPsi.R2.Wo Googology.Trans.PoR.InaccPsi.R2.Wn Googology.Trans.PoR.InaccPsi.R2.Wp
  Googology.Trans.PoR.InaccPsi.R2.Ws Googology.Trans.PoR.InaccPsi.R2.Wt Googology.Trans.PoR.InaccPsi.R2.Wy
  Googology.Trans.PoR.InaccPsi.R2.Wx


open Googology.Trans.PoR.InaccPsi.R2.Xc
open Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt

open Googology.Trans.PoR.InaccPsi.R2.Xf

open Googology.Trans.PoR.InaccPsi.R2.Ho

open Googology.Trans.PoR.InaccPsi.R2.Xl
open Googology.Trans.PoR.InaccPsi.R2.Xp

namespace Googology.Trans.PoR.InaccPsi.R2.Xp

theorem xp_LOm_lim (Λ : HnLv) : IsSuccLimit (Λ.L + Om1) := isSuccLimit_add _ gl_Om1_lim

theorem xp_LOm_lt1 (Λ : HnLv) : Λ.L + Om1 < gcG 1 := Λ.succ.L_G

section Fam

variable (B : XpBd) (U0 : HgVD) (hU0 : XpAt B.K.Λ 0 U0)

theorem xp_lxx_lt {x : Ordinal.{0}} (hx : InE x) : B.K.Λ.l x + x < veblen (B.K.Λ.l x + x) 0 :=
  xl_lt_veb0 hx.pos (xp_lt_sum hx.pos (B.K.Λ.l_ge x))

/-- `ϑˣ(Ω₁·(ℓ(x) + x)) = φ(ℓ(x) + x, 0)`. -/
theorem xp_glA_W {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    glA (B.K.Λ.succ.l x + 0) 0 x = veblen (B.K.Λ.l x + x) 0 := by
  have hq : B.K.Λ.l x + x < gq 1 x :=
    (inE_indec (gm1_facts hx hx1).2.2.2).add_lt (B.K.Λ.l_lt x hx hx1) (gm1_facts hx hx1).2.1
  have h := xl_glAv (α := B.K.Λ.l x + x) hx hx1 ((wo_one_lt_inE hx).le.trans ((B.K.Λ.l_ge x).trans le_self_add))
    hq ((B.K.Λ.l_ge x).trans le_self_add) (xp_lxx_lt B hx)
    (he_N_lt1 hx hx1 ((ev_isSuccLimit_of_inE (gm1_facts hx hx1).2.2.2).add_one_lt hq)
      (gm1_facts hx hx1).2.2.2.pos) 0 (hcN_E _ _).pos
  show glA (B.K.Λ.l x + x + 0) 0 x = _
  rw [add_zero]; exact h

include hU0

/-- **THE FAMILY OF THE LEVELS `L + μ`, `μ < Ω₁`**: bound `φ(L + Ω₁, 0)`, gate `g`, base reading
`φ(ℓ(x) + x, 0)`. -/
noncomputable def xpWF : HoFam where
  D := xpK B U0
  B := veblen (B.K.Λ.L + Om1) 0
  γ := B.K.Λ.g
  b := fun x => veblen (B.K.Λ.l x + x) 0
  Zo := xpZ
  γ_lt := B.K.Λ.g_lt
  γ_cl := fun Z hZ hZ1 h => by
    have hGQ : gcG 0 < veblen (B.K.Λ.succ.L + 0) 0 := B.G_lt.trans_le (le_self_add.trans
      (le_self_add.trans (left_le_veblen _ 0)))
    have hs : veblen (B.K.Λ.succ.L + 0) 0 < veblen (B.K.Λ.succ.L + 0) (0 + 1) :=
      (isNormal_veblen _).strictMono (show (0 : Ordinal.{0}) < 0 + 1 by rw [zero_add]; exact zero_lt_one)
    have h' : GxCl Z {gcG 0} (veblen (B.K.Λ.succ.L + 0) 0) := by
      show GxCl _ {gcG 0} (veblen (B.K.Λ.L + Om1 + 0) 0); rw [add_zero]; exact h
    exact hnv_cl_g B.K.Λ.succ gv_Om1_pos hZ hZ1 veblen_pos hGQ h' le_rfl hs
  G_lt := B.G_lt.trans_le (le_self_add.trans (left_le_veblen _ 0))
  B_E := gg_veblen_eps (xp_LOm_lim B.K.Λ).bot_lt.ne'
  B_lt1 := by
    have h := (isNormal_veblen (B.K.Λ.L + Om1)).strictMono (gcG_SC 1).1
    rwa [gn_veb_fix (gcG_SC 1) (xp_LOm_lt1 B.K.Λ)] at h
  B_fix1 := veblen_veblen_of_lt ((wh_one_lt_Om1.trans_le le_add_self)) 0
  B_mem := fun S _ _ ha hb => CSet.phi_mem (B.K.Λ.succ.L_mem S _ _ ha hb) (CSet.zero_mem _ _)
  DB_lt := fun μ hμ => by
    rw [(xpK_at hU0 hμ).B]
    exact veblen_zero_lt_veblen_zero.2 ((add_lt_add_iff_left _).2 hμ)
  B_cof := fun c hc => by
    obtain ⟨a, ha, hca⟩ := wx_veb_lim_cof0 (xp_LOm_lim B.K.Λ) hc
    obtain ⟨d, hd, had⟩ := (lt_add_iff gl_Om1_lim.bot_lt.ne').1 ha
    have hd1 : d + 1 < Om1 := gl_Om1_lim.add_one_lt hd
    refine ⟨d + 1, hd1, ?_⟩
    rw [(xpK_at hU0 hd1).B]
    exact hca.trans_le (veblen_zero_le_veblen_zero.2 (had.trans ((add_le_add_iff_left _).2 (lt_add_one d).le)))
  ext := fun μ' μ h hμ c x hc => xpK_ext hU0 h hμ hc x
  small := fun μ hμ c hc σ hσ hσ1 hg => xpK_small hU0 μ hμ c hc σ hσ hσ1 hg
  γD := fun x hx _ hg μ hμ => (xpK_at hU0 (hμ.trans ‹x < Om1›)).γ_le.trans_lt (max_lt hμ hg)
  bD := fun x hx hx1 hg μ hμ => by
    rw [(xpK_at hU0 (hμ.trans hx1)).b x hx hx1 (max_lt hμ hg)]
    exact veblen_zero_lt_veblen_zero.2 ((add_lt_add_iff_left _).2 hμ)
  ZD := fun x hx hx1 hg μ hμ => by
    rw [(xpK_at hU0 (hμ.trans hx1)).Z x hx hx1, if_pos (max_lt hμ hg)]
    have h2 : (2 : Ordinal.{0}) < B.K.Λ.l x + x :=
      ((show (2 : Ordinal.{0}) < ω from (by exact_mod_cast natCast_lt_omega0 2)).trans_le
        ((omega0_lt_inE hx).le.trans (B.K.Λ.l_ge x))).trans_le le_self_add
    exact (hb_evZ_lt_fix2 (veblen_veblen_of_lt h2 0)
      (veblen_zero_lt_veblen_zero.2 ((add_lt_add_iff_left _).2 hμ))).le
  b_cof := fun x hx hx1 hg ν hν => by
    obtain ⟨a, ha, hνa⟩ := wx_veb_lim_cof0 (isSuccLimit_add _ (ev_isSuccLimit_of_inE hx)) hν
    obtain ⟨d, hd, had⟩ := (lt_add_iff hx.pos.ne').1 ha
    have hd1 : d + 1 < x := (ev_isSuccLimit_of_inE hx).add_one_lt hd
    refine ⟨d + 1, hd1, ?_⟩
    rw [(xpK_at hU0 (hd1.trans hx1)).b x hx hx1 (max_lt hd1 hg)]
    exact hνa.trans_le (veblen_zero_le_veblen_zero.2 (had.trans ((add_le_add_iff_left _).2 (lt_add_one d).le)))
  b_E := fun _ hx _ _ => gg_veblen_eps (hx.pos.trans_le le_add_self).ne'
  x_lt_b := fun x hx _ _ => ((B.K.Λ.l_ge x).trans le_self_add).trans_lt (xp_lxx_lt B hx)
  b_fix1 := fun x hx _ _ => veblen_veblen_of_lt ((wo_one_lt_inE hx).trans_le le_add_self) 0
  b_lt1 := fun x hx hx1 hg => by
    have h : veblen (B.K.Λ.l x + x) 0 < xpZ x := by
      rw [xpZ_eq hx, xl_N_eq]
      refine veblen_zero_lt_veblen_zero.2 (lt_of_lt_of_le ?_ (le_add_right le_rfl))
      exact (inE_indec (xp_aE hx hx1)).add_lt (B.l_lt x hx hx1 hg) (xp_x_lt_a hx hx1)
    exact h.trans (xpZ_G1 hx hx1)
  b_pi := fun σ ρ hB hγ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have h0σ : (0 : Ordinal.{0}) < σ := hB.1.pos
    have h := hnv_glA_pi B.K.Λ.succ (ν := 0) hB hγ h0σ (mem_TB_of_lt hB h0σ) (gm1_facts hB.2.1 hρ1).2.2.2.pos
    rw [pi_lt hB h0σ, xp_glA_W B hB.2.1 hρ1, xp_glA_W B hB.1 hσ1] at h
    exact h
  Z_low := fun μ hμ x hx hx1 h => by
    rw [(xpK_at hU0 hμ).Z x hx hx1, if_neg (fun h' => h (max_lt_iff.1 h').2)]
  Zo_fix := xpZ_fix
  Zo_G1 := fun _ hx hx1 => xpZ_G1 hx hx1

/-- **THE SYSTEM AT `φ(L + Ω₁, 0)`**: the union of all `xpK B U₀ μ`, `μ < Ω₁`; gate `g`. -/
noncomputable def xpW : HgVD := hoOU (xpWF B U0 hU0)

theorem xpW_B : (xpW B U0 hU0).B = veblen (B.K.Λ.L + Om1) 0 := rfl

theorem xpW_γ : (xpW B U0 hU0).γ = B.K.Λ.g := rfl

/-- **`xpW` extends every `xpK μ`.** -/
theorem xpW_ext {μ c : Ordinal.{0}} (hμ : μ < Om1) (hc : c < (xpK B U0 μ).B) (x : Ordinal.{0}) :
    (xpW B U0 hU0).R c x = (xpK B U0 μ).R c x ∧ (xpW B U0 hU0).g c = (xpK B U0 μ).g c :=
  ⟨hoOU_R (xpWF B U0 hU0) hμ hc x, hoOU_g (xpWF B U0 hU0) hμ hc⟩

/-- **`xpW` extends `U₀`.** -/
theorem xpW_ext0 {c : Ordinal.{0}} (hc : c < U0.B) (x : Ordinal.{0}) :
    (xpW B U0 hU0).R c x = U0.R c x ∧ (xpW B U0 hU0).g c = U0.g c := by
  have h := xpW_ext B U0 hU0 gv_Om1_pos (by rw [xpK_zero]; exact hc) x
  rwa [xpK_zero] at h

/-- **THE `Ω₁`-UNION IS A SYSTEM AT THE BOTTOM `φ(L + Ω₁, 0)` OF THE NEXT BAND.** -/
theorem xpW_at : XpAt B.succ.K.Λ 0 (xpW B U0 hU0) where
  B := by show veblen (B.K.Λ.L + Om1) 0 = veblen (B.K.Λ.L + Om1 + 0) 0; rw [add_zero]
  ix := by show veblen (B.K.Λ.L + Om1) 0 = veblen (B.K.Λ.L + Om1 + 0) 0; rw [add_zero]
  γ := fun x _ _ => by show B.K.Λ.g < x ↔ max 0 B.K.Λ.g < x; rw [max_eq_right zero_le]
  b := fun x _ _ _ => by
    show veblen (B.K.Λ.l x + x) 0 = veblen (B.K.Λ.l x + x + 0) 0; rw [add_zero]
  γ_le := le_max_right _ _
  Z := fun x _ _ => by
    rw [show (xpW B U0 hU0).Z x = if B.K.Λ.g < x then evZ (veblen (B.K.Λ.l x + x) 0) else xpZ x from rfl]
    show _ = if max 0 B.K.Λ.g < x then evZ (veblen (B.K.Λ.l x + x + 0) 0) else xpZ x
    rw [max_eq_right zero_le, add_zero]

/-- **THE GENERIC BAND STEP**: a system at `φ(L, 0)` gives a system at `φ(L + Ω₁, 0)` (the bottom of the next band,
gate `g`) extending it. -/
theorem xpBandStep : ∃ V : HgVD, XpAt B.succ.K.Λ 0 V ∧ V.γ = B.K.Λ.g ∧
    ∀ c x, c < U0.B → V.R c x = U0.R c x ∧ V.g c = U0.g c :=
  ⟨xpW B U0 hU0, xpW_at B U0 hU0, rfl, fun _ x hc => xpW_ext0 B U0 hU0 hc x⟩

end Fam

/-! ## Transfer of `XpAt` between data -/

/-- **`XpAt` DEPENDS ONLY ON `L`, ON THE GATE THROUGH ITS CUTS AT `ε`-NUMBERS AND ON THE READING ABOVE IT.** -/
theorem xpAt_congr {Λ Λ' : HnLv} {κ : Ordinal.{0}} {U : HgVD} (h : XpAt Λ κ U) (hL : Λ'.L = Λ.L)
    (hg : ∀ x, InE x → x < Om1 → (Λ.g < x ↔ Λ'.g < x)) (hgle : Λ.g ≤ Λ'.g)
    (hl : ∀ x, InE x → x < Om1 → Λ'.g < x → Λ'.l x = Λ.l x) : XpAt Λ' κ U where
  B := by rw [h.B, hL]
  ix := by rw [h.ix, hL]
  γ := fun x hx hx1 => by
    rw [h.γ x hx hx1, max_lt_iff, max_lt_iff, hg x hx hx1]
  b := fun x hx hx1 hm => by
    have hm' : max κ Λ.g < x := max_lt (max_lt_iff.1 hm).1 ((hg x hx hx1).2 (max_lt_iff.1 hm).2)
    rw [h.b x hx hx1 hm', hl x hx hx1 (max_lt_iff.1 hm).2]
  γ_le := h.γ_le.trans (max_le_max le_rfl hgle)
  Z := fun x hx hx1 => by
    rw [h.Z x hx hx1]
    have hiff : max κ Λ.g < x ↔ max κ Λ'.g < x := by rw [max_lt_iff, max_lt_iff, hg x hx hx1]
    by_cases hm : max κ Λ'.g < x
    · rw [if_pos (hiff.2 hm), if_pos hm, hl x hx hx1 (max_lt_iff.1 hm).2]
    · rw [if_neg (fun h' => hm (hiff.1 h')), if_neg hm]

/-! ## The band `G + Ω₁` -/

/-- **THE BAND DATUM `G + Ω₁`**: the package `HnPk.succ Xf.xfPk` (reading `Γ_{x+1} + x`, gate `1`). -/
noncomputable def xpBdG1 : XpBd where
  K := xfPk.succ
  G_lt := by show gcG 0 < gcG 0 + Om1; exact lt_add_of_pos_right _ gv_Om1_pos
  l_lt := fun x hx hx1 hg => by
    show xfLv.l x + x < _
    rw [xf_l hx hx1]
    exact (inE_indec (xp_aE hx hx1)).add_lt (wnLv3T0.l_gtG x hx hx1 hx.pos) (xp_x_lt_a hx hx1)
  l_nsc := fun x hx _ _ => xl_lt_veb0 hx.pos (xp_lt_sum hx.pos (xfLv.l_ge x))

theorem xpBdG1_L : xpBdG1.K.Λ.L = gcG 0 + Om1 := rfl

theorem xpBdG1_g : xpBdG1.K.Λ.g = 1 := xfLv_g

/-- **`Xl.xlW` IS A SYSTEM AT THE BOTTOM `φ(G + Ω₁, 0)` OF THE BAND `G + Ω₁`.** -/
theorem xp_at_xlW : XpAt xpBdG1.K.Λ 0 xlW where
  B := by show veblen (gcG 0 + Om1) 0 = veblen (gcG 0 + Om1 + 0) 0; rw [add_zero]
  ix := by show veblen (gcG 0 + Om1) 0 = veblen (gcG 0 + Om1 + 0) 0; rw [add_zero]
  γ := fun x _ _ => by rw [xlW_γ, xpBdG1_g, max_eq_right zero_le]
  b := fun x _ _ _ => by rw [xlW_b, add_zero]; rfl
  γ_le := by rw [xlW_γ, xpBdG1_g, max_eq_right zero_le]
  Z := fun x hx _ => by
    rw [show xlW.Z x = if (1 : Ordinal.{0}) < x then evZ (veblen (xfLv.l x + x) 0) else xlZs x from rfl,
      if_pos (wo_one_lt_inE hx), xpBdG1_g, max_eq_right zero_le, if_pos (wo_one_lt_inE hx), add_zero]; rfl

end Googology.Trans.PoR.InaccPsi.R2.Xp

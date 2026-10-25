import Googology.Trans.PoR.InaccPsi.R2.GvIt

/-!
# THE STARTS `G + Ω₁·α + 1` FOR EVERY `α < ε₀`; THE FRONTIER `ι(Γ(ε_{G+Ω₁·ε₀}))`

One recursion `gvA α` (`α < ε₀`) of starts (`GvSt`) with index `G + Ω₁·(1+α) + 1` and base reading
`φ(1, Γ_{x+1} + x·(1+α) + 1)` (base gate `0`): `gvSt0` at `0`, `gvNext` (the union over `Ω₁`, then the step) at
`α+1`, and at a limit `λ < ε₀` the step of the gated union (`Gs.GsCh.lim`, gate `0`) of the starts `gvA (λ_k)` along a
fundamental sequence, with base reading `φ(1, Γ_{x+1} + x·λ)`.  Lemma EXACT for `x·λ` is `Exact.pi_mul`
(`λ < ε₀ ≤ σ` at every base `σ`), so no gate is needed below `ε₀`.  The invariant (`GvAInv`: index, reading,
coherence of the starts, gate `0` of every earlier bound) holds at every `α < ε₀` (`gvA_inv`).  The bound
`ε_{G+Ω₁·(1+α+1)}` of every union is located (`gvLocU`), so ENUM-REACH and CapV hold below `ι(Γ(ε_{G+Ω₁·ε₀}))`.

* `gv_Om_mul_mem`, `gvNext_coh`, `gvNext_gate`; `GvAInv`, `gvACh` (**THE UNION AT A LIMIT**), `gvAStart`, `gvAExt`,
  `gvALim`, `gvA` (**THE RECURSION**), `GvATop`, `gvA_inv`, `gvA_P0`, `gvA_UB`;
* `gvE0`, `gvE0_codes`, `gvE0_cof`, `gvE0_enum`, `gvE0_capV`, `gvE0_road` (**THE ROAD**), `gvE0_lt_G1`,
  `gvE0_le_Om2`, `gvE0_P`, `gvE0_fr_order`.

No new axiom.  New definitions: `GvAInv`, `GvATop`, `gvACh`, `gvAStart`, `gvAExt`, `gvALim`, `gvA`, `gvE0`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gv

open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Go
  Googology.Trans.PoR.InaccPsi.R2.Gp
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

/-- `Ω₁·β ∈ C(a, b)` for every `β < Γ₁`, `0 < a`. -/
theorem gv_Om_mul_mem {S : InaccSeq.{0}} {a b β : Ordinal.{0}} (ha : 0 < a) (hβ : β < gamma 1) :
    Om 1 * β ∈ S.CSet a b := by
  have he : Om 1 ∈ S.CSet a b := CSet.Om_mem (CSet.one_mem _ _)
  rw [← Bt.Om1_opow]
  obtain ⟨L, hL1, -, hL3⟩ := Bt.exists_prin_list β
  rw [← hL3, ← Bt.foldr_map_mul]
  refine Bt.foldr_mem _ fun l hl => ?_
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hl
  obtain ⟨hp, h0, hle⟩ := hL1 y hy
  obtain ⟨c, rfl⟩ := Bt.prin_eq_opow hp h0
  rw [← opow_add, ← veblen_zero_apply]
  refine CSet.phi_mem (CSet.zero_mem _ _) (CSet.add_mem he (gr_cst_mem ha b c ?_))
  exact lt_of_le_of_lt ((Ordinal.right_le_opow c one_lt_omega0).trans hle) hβ

theorem gv_eps0_lt_Om1 : (ε₀ : Ordinal.{0}) < Om1 :=
  (gq_eps0_lt_gam.trans gam0_lt_grK).trans grK_lt_Om1

theorem gv_eps0_lt_gam1 : (ε₀ : Ordinal.{0}) < gamma 1 :=
  (gq_eps0_lt_gam.trans gam0_lt_grK).trans grK_lt_gam1

/-! ## The step from a start to the next one keeps the codes -/

theorem gvNext_D0 (St : GvSt) : (gvNext St).D0 = (gvUof St).step := rfl

theorem gvSt_lt_Ug (St : GvSt) {c : Ordinal.{0}} (hc : c < St.D0.B) :
    c < (gvRD St 0).B ∧ c < (gvUof St).B := by
  have h0 : c < (gvRD St 0).B := by rw [gvRD_zero]; exact hc
  exact ⟨h0, h0.trans ((gvFamOf St).B_ltΩ gv_Om1_pos)⟩

/-- **The next start extends the start** (readings and gates). -/
theorem gvNext_coh (St : GvSt) {c : Ordinal.{0}} (hc : c < St.D0.B) :
    (∀ x, (gvNext St).D0.R c x = St.D0.R c x) ∧ (gvNext St).D0.g c = St.D0.g c := by
  obtain ⟨h0, hU⟩ := gvSt_lt_Ug St hc
  refine ⟨fun x => ?_, ?_⟩
  · rw [gvNext_D0, GvD.step_R_low _ hU x]
    show (gvFamOf St).U.R c x = _
    rw [(gvFamOf St).U_R gv_Om1_pos h0 x]
    show (gvRD St 0).R c x = _
    rw [gvRD_zero]
  · rw [gvNext_D0, GvD.step_g_low _ hU]
    show (gvFamOf St).U.g c = _
    rw [(gvFamOf St).U_g gv_Om1_pos h0]
    show (gvRD St 0).g c = _
    rw [gvRD_zero]

/-- **The bound of a start has gate `0` in the next start.** -/
theorem gvNext_gate (St : GvSt) : (gvNext St).D0.g St.D0.B = 0 := by
  have h1 : St.D0.B < (gvRD St (0 + 1)).B := by
    rw [gvRD_succ, gvRD_zero, GsD.step_B]; exact lt_eN _
  have h11 : (0 : Ordinal.{0}) + 1 < Om1 := by rw [zero_add]; exact gv_one_lt_Om1'
  have hU : St.D0.B < (gvUof St).B := h1.trans ((gvFamOf St).B_ltΩ h11)
  rw [gvNext_D0, GvD.step_g_low _ hU]
  show (gvFamOf St).U.g St.D0.B = 0
  rw [(gvFamOf St).U_g h11 h1]
  show (gvRD St (0 + 1)).g St.D0.B = 0
  rw [gvRD_succ, gvRD_zero, GsD.step_g_B, St.γ0]

theorem gvNext_B_lt (St : GvSt) : St.D0.B < (gvNext St).D0.B := by
  have h0 : (gvRD St 0).B < (gvUof St).B := (gvFamOf St).B_ltΩ gv_Om1_pos
  rw [gvRD_zero] at h0
  exact h0.trans (gvUof St).B_lt_NB

/-! ## The invariant -/

/-- **The invariant of the starts below `λ`**: index `G + Ω₁·(1+β) + 1`, reading `Γ_{x+1} + x·(1+β) + 1`,
coherence, gate `0` of the earlier bounds. -/
structure GvAInv (l : Ordinal.{0}) (F : Ordinal.{0} → GvSt) : Prop where
  P0 : ∀ β, β < l → (F β).P0 = gcG 0 + Om1 * (1 + β)
  i0 : ∀ β, β < l → (F β).i0 = (F β).P0 + 1
  i : ∀ β, β < l → ∀ x, InE x → (F β).i x = gpI x + x * (1 + β) + 1
  coh : ∀ β γ, β ≤ γ → γ < l → ∀ c, c < (F β).D0.B →
    (∀ x, (F γ).D0.R c x = (F β).D0.R c x) ∧ (F γ).D0.g c = (F β).D0.g c
  gate : ∀ β γ, β < γ → γ < l → (F γ).D0.g (F β).D0.B = 0

namespace GvAInv

variable {l : Ordinal.{0}} {F : Ordinal.{0} → GvSt} (H : GvAInv l F)
include H

theorem B_eq {β : Ordinal.{0}} (h : β < l) : (F β).D0.B = veblen 1 (gcG 0 + Om1 * (1 + β) + 1) := by
  rw [(F β).D0.B_ix, (F β).ix0, H.i0 β h, H.P0 β h]

theorem B_lt {β γ : Ordinal.{0}} (hβγ : β < γ) (h : γ < l) : (F β).D0.B < (F γ).D0.B := by
  rw [H.B_eq (hβγ.trans h), H.B_eq h]
  refine (isNormal_veblen 1).strictMono ?_
  refine (Order.add_one_le_of_lt ?_).trans_lt (lt_add_one _)
  refine (add_lt_add_iff_left _).2 ((mul_lt_mul_iff_right₀ gv_Om1_pos).2 ((add_lt_add_iff_left _).2 hβγ))

theorem congr {G : Ordinal.{0} → GvSt} (hFG : ∀ β, β < l → G β = F β) : GvAInv l G where
  P0 := fun β h => by rw [hFG β h]; exact H.P0 β h
  i0 := fun β h => by rw [hFG β h]; exact H.i0 β h
  i := fun β h => by rw [hFG β h]; exact H.i β h
  coh := fun β γ hβγ h c hc => by
    rw [hFG β (lt_of_le_of_lt hβγ h)] at hc ⊢
    rw [hFG γ h]; exact H.coh β γ hβγ h c hc
  gate := fun β γ hβγ h => by rw [hFG β (hβγ.trans h), hFG γ h]; exact H.gate β γ hβγ h

end GvAInv

theorem gvAInv_zero (F : Ordinal.{0} → GvSt) : GvAInv 0 F where
  P0 := fun _ h => absurd h (not_lt.2 zero_le)
  i0 := fun _ h => absurd h (not_lt.2 zero_le)
  i := fun _ h => absurd h (not_lt.2 zero_le)
  coh := fun _ _ _ h => absurd h (not_lt.2 zero_le)
  gate := fun _ _ _ h => absurd h (not_lt.2 zero_le)

/-! ## The union at a limit `λ < ε₀` -/

section Lim

variable {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlE : l < ε₀)
include hl hlE

theorem gvA_l1 : l < Om1 := hlE.trans gv_eps0_lt_Om1

theorem gvA_wl : ω ≤ l := omega0_le_of_isSuccLimit hl

theorem gvA_one_add {β : Ordinal.{0}} (hβ : β < l) : 1 + β + 1 ≤ l := by
  refine Order.add_one_le_of_lt ?_
  rcases lt_or_ge β ω with hω | hω
  · have h1 : 1 + β < ω := isPrincipal_add_omega0 one_lt_omega0 hω
    exact h1.trans_le (gvA_wl hl hlE)
  · rw [one_add_of_omega0_le hω]; exact hβ

theorem gvA_xl {x : Ordinal.{0}} (hx : InE x) : l < x := hlE.trans_le (go_eps0_le hx)

theorem gvA_xl_lt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : x * l + 1 < lgG x := by
  obtain ⟨-, hxG, -, hGE, -⟩ := lgG_facts hx hx1
  exact (ev_isSuccLimit_of_inE hGE).add_one_lt (InE.mul_lt hGE hxG ((gvA_xl hl hlE hx).trans hxG))

theorem gvA_le_xl {x : Ordinal.{0}} (hx : InE x) : ω ≤ x * l :=
  (omega0_lt_inE hx).le.trans (le_mul_left _ hl.bot_lt)

end Lim

/-- **The union of the starts at a limit `λ < ε₀`** (gate `0`, bound `ε_{G+Ω₁·λ}`, base `φ(1, Γ_{x+1} + x·λ)`). -/
noncomputable def gvACh (l : Ordinal.{0}) (hl : IsSuccLimit l) (hlE : l < ε₀) (F : Ordinal.{0} → GvSt)
    (H : GvAInv l F) : GsCh where
  D := fun k => (F (gqFs l k)).D0
  ixω := gcG 0 + Om1 * l
  bω := fun x => veblen 1 (gpI x + x * l)
  baω := fun x => lgG x + (x * l + 1)
  γω := 0
  γω_lt := gv_Om1_pos
  γ_cl := fun _ hZ _ _ => hZ.1
  γ_le := fun k => (F (gqFs l k)).γ0.le
  coh_R := fun k c x hc =>
    (H.coh _ _ (gqFs_mono hl (gvA_l1 hl hlE) k).le (gqFs_lt hl (gvA_l1 hl hlE) (k + 1)) c hc).1 x
  coh_g := fun k c hc =>
    (H.coh _ _ (gqFs_mono hl (gvA_l1 hl hlE) k).le (gqFs_lt hl (gvA_l1 hl hlE) (k + 1)) c hc).2
  B_mono := fun k => H.B_lt (gqFs_mono hl (gvA_l1 hl hlE) k) (gqFs_lt hl (gvA_l1 hl hlE) (k + 1))
  B_lt := fun k => by
    show (F (gqFs l k)).D0.B < _
    have hk := gqFs_lt hl (gvA_l1 hl hlE) k
    rw [H.B_eq hk]
    refine (isNormal_veblen 1).strictMono ?_
    rw [add_assoc]
    refine (add_lt_add_iff_left _).2 ?_
    calc (Om1 : Ordinal.{0}) * (1 + gqFs l k) + 1 < Om1 * (1 + gqFs l k) + Om1 :=
          (add_lt_add_iff_left _).2 gv_one_lt_Om1'
      _ = Om1 * (1 + gqFs l k + 1) := (mul_add_one _ _).symm
      _ ≤ Om1 * l := mul_le_mul_left' (gvA_one_add hl hlE hk) _
  B_cof := fun c hc => by
    have hl1 := gvA_l1 hl hlE
    have hOl : IsSuccLimit (Om1 * l : Ordinal.{0}) := isSuccLimit_mul_right gv_Om1_pos hl
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ hOl)).1 hc
    obtain ⟨d, hd, htd⟩ := (lt_add_iff hOl.bot_lt.ne').1 ht
    obtain ⟨m, hm, hdm⟩ := (lt_mul_iff_of_isSuccLimit hl).1 hd
    obtain ⟨k, hk⟩ := gqFs_cof hl hl1 m hm
    refine ⟨k, ?_⟩
    show c < (F (gqFs l k)).D0.B
    rw [H.B_eq (gqFs_lt hl hl1 k)]
    refine hct.trans_le ((isNormal_veblen 1).monotone (htd.trans ?_))
    rw [add_assoc]
    refine (add_le_add_iff_left _).2 ((hdm.le.trans ?_).trans le_self_add)
    exact mul_le_mul_left' (hk.le.trans le_add_self) _
  ix_mem := fun S a b ha _ => CSet.add_mem (goGl.ix_mem S a b ha) (by
    rw [Br.Om1_eq]; exact gv_Om_mul_mem ha (hlE.trans gv_eps0_lt_gam1))
  ix_lt := by
    have hE : InE (gcG 1) := Low.opow_eq_self_of_SC (gcG_SC 1)
    exact (inE_indec hE).add_lt (gcG_lt zero_lt_one)
      (InE.mul_lt hE gv_Om1_lt_G1 ((gvA_l1 hl hlE).trans gv_Om1_lt_G1))
  cf_g := fun k => by
    rw [H.gate _ _ (gqFs_mono hl (gvA_l1 hl hlE) k) (gqFs_lt hl (gvA_l1 hl hlE) (k + 1))]; exact zero_le
  b_le := fun k x hx hx1 _ => by
    have hk := gqFs_lt hl (gvA_l1 hl hlE) k
    show (F (gqFs l k)).D0.b x ≤ _
    rw [(F (gqFs l k)).b0 x hx hx1, H.i _ hk x hx]
    refine (isNormal_veblen 1).monotone ?_
    rw [add_assoc]
    refine (add_le_add_iff_left _).2 ?_
    calc x * (1 + gqFs l k) + 1 ≤ x * (1 + gqFs l k) + x := (add_le_add_iff_left _).2
          (one_lt_omega0.trans (omega0_lt_inE hx)).le
      _ = x * (1 + gqFs l k + 1) := (mul_add_one _ _).symm
      _ ≤ x * l := mul_le_mul_left' (gvA_one_add hl hlE hk) _
  b_sup := fun x hx hx1 _ ν hν => by
    have hl1 := gvA_l1 hl hlE
    have hxl : IsSuccLimit (x * l) := isSuccLimit_mul_right hx.pos hl
    obtain ⟨t, ht, hνt⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ hxl)).1 hν
    obtain ⟨d, hd, htd⟩ := (lt_add_iff hxl.bot_lt.ne').1 ht
    obtain ⟨m, hm, hdm⟩ := (lt_mul_iff_of_isSuccLimit hl).1 hd
    obtain ⟨k, hk⟩ := gqFs_cof hl hl1 m hm
    refine ⟨k, ?_⟩
    show ν < (F (gqFs l k)).D0.b x
    rw [(F (gqFs l k)).b0 x hx hx1, H.i _ (gqFs_lt hl hl1 k) x hx]
    refine hνt.trans_le ((isNormal_veblen 1).monotone (htd.trans ?_))
    rw [add_assoc]
    refine (add_le_add_iff_left _).2 ((hdm.le.trans ?_).trans le_self_add)
    exact mul_le_mul_left' (hk.le.trans le_add_self) _
  b_E := fun _ _ _ _ => omega0_opow_epsilon _
  b_eN := fun x hx hx1 _ => gp_b_eN hx hx1 (gvA_le_xl hl hlE hx) (gvA_xl_lt hl hlE hx hx1)
  ba_lt := fun x hx hx1 _ => by
    have hq := (gm1_facts hx hx1).2.2.2
    have hG : lgG x < gq 1 x := goGl.ba_lt x hx hx1
    exact (inE_indec hq).add_lt hG ((gvA_xl_lt hl hlE hx hx1).trans hG)
  b_Z := fun x hx hx1 _ => by
    refine go_eN_lt_evZ ?_
    have hZ := evZ_E (lgG x)
    have hGE := (lgG_facts hx hx1).2.2.2.1
    have hGZ : lgG x < evZ (lgG x) := lt_evZ _
    have hi : gpI x < evZ (lgG x) := (evIx_le hGE).trans_lt hGZ
    have hxZ : x * l < evZ (lgG x) := ((lt_add_one _).trans (gvA_xl_lt hl hlE hx hx1)).trans hGZ
    have := (isNormal_veblen 1).strictMono ((inE_indec hZ).add_lt hi hxZ)
    rwa [show veblen 1 (evZ (lgG x)) = evZ (lgG x) from epsilon_evZ _] at this
  b_pi := fun σ ρ hB _ => by
    obtain ⟨m1, m2⟩ := pi_mul hB l (gvA_xl hl hlE hB.1)
    exact gp_b_pi_code hB m1 ((lt_add_one _).trans (gvA_xl_lt hl hlE hB.2.1 hB.2.2.2))
      (gvA_le_xl hl hlE hB.2.1) m2
  ba_pi := fun σ ρ hB _ => by
    obtain ⟨g1, g2⟩ : lgG ρ ∈ TB ρ σ ∧ pi σ ρ (lgG ρ) = lgG σ := goGl.ba_pi σ ρ hB
    obtain ⟨m1, m2⟩ := pi_mul hB l (gvA_xl hl hlE hB.1)
    obtain ⟨o1, o2⟩ := one_TB hB
    obtain ⟨s1, s2⟩ := pi_add hB m1 o1
    obtain ⟨t1, t2⟩ := pi_add hB g1 s1
    exact ⟨t1, by rw [t2, s2, g2, m2, o2]⟩

/-- **The start after a limit `λ < ε₀`**: the step of the union of the starts below `λ`. -/
noncomputable def gvAStart (l : Ordinal.{0}) (hl : IsSuccLimit l) (hlE : l < ε₀) (F : Ordinal.{0} → GvSt)
    (H : GvAInv l F) : GvSt where
  D0 := (gvACh l hl hlE F H).lim.step
  i0 := gcG 0 + Om1 * l + 1
  i := fun x => gpI x + x * l + 1
  a := fun x => lgG x + (x * l + 1) + 1
  P0 := gcG 0 + Om1 * l
  j0 := 1
  γ0 := rfl
  ix0 := rfl
  b0 := fun x _ _ => by
    show eN (veblen 1 (gpI x + x * l)) = _
    rw [go_eN_veb]
  ba0 := fun _ => rfl
  i0_eq := rfl
  P0_dvd := by
    refine dvd_add ?_ (by rw [Br.Om1_eq]; exact dvd_mul_right _ _)
    have e : ω ^ gcG 0 = gcG 0 := Low.opow_eq_self_of_SC (gcG_SC 0)
    have h := gv_Om1_dvd_opow (e.symm ▸ (gcG_Om1_lt 0).le : Om 1 ≤ ω ^ gcG 0)
    rwa [e] at h
  P0_ge := (gcG_Om1_lt 0).le.trans le_self_add
  j0_lt := one_lt_Om1
  i_big := fun x hx hx1 => by
    have e : veblen 1 (gpI x) = lgG x := epsilon_evIx (lgG_facts hx hx1).2.2.2.1
    rw [← e]
    exact (isNormal_veblen 1).monotone (le_self_add.trans le_self_add)

/-- The family of the earlier starts, extended by `gvSt0`. -/
noncomputable def gvAExt (l : Ordinal.{0}) (IH : ∀ β, β < l → GvSt) (β : Ordinal.{0}) : GvSt :=
  if h : β < l then IH β h else gvSt0

open Classical in
/-- The limit step of the recursion of the starts. -/
noncomputable def gvALim (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ β, β < l → GvSt) : GvSt :=
  if H : l < ε₀ ∧ GvAInv l (gvAExt l IH) then gvAStart l hl H.1 (gvAExt l IH) H.2 else gvSt0

/-- **THE RECURSION OF THE STARTS**: `gvSt0` at `0`, `gvNext` at `α+1`, the step of the union at a limit. -/
noncomputable def gvA (α : Ordinal.{0}) : GvSt :=
  Ordinal.limitRecOn (motive := fun _ => GvSt) α gvSt0 (fun _ St => gvNext St) gvALim

theorem gvA_zero : gvA 0 = gvSt0 := by unfold gvA; rw [Ordinal.limitRecOn_zero]

theorem gvA_succ (α : Ordinal.{0}) : gvA (α + 1) = gvNext (gvA α) := by
  unfold gvA; rw [Ordinal.limitRecOn_add_one]

theorem gvA_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) : gvA l = gvALim l hl (fun β _ => gvA β) := by
  unfold gvA; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem gvAExt_eq {l β : Ordinal.{0}} (h : β < l) : gvAExt l (fun β _ => gvA β) β = gvA β := by
  unfold gvAExt; rw [dif_pos h]

/-! ## The invariant at every `α < ε₀` -/

/-- The new facts at the top `α`. -/
structure GvATop (α : Ordinal.{0}) : Prop where
  P0 : (gvA α).P0 = gcG 0 + Om1 * (1 + α)
  i0 : (gvA α).i0 = (gvA α).P0 + 1
  i : ∀ x, InE x → (gvA α).i x = gpI x + x * (1 + α) + 1
  coh : ∀ β, β < α → ∀ c, c < (gvA β).D0.B →
    (∀ x, (gvA α).D0.R c x = (gvA β).D0.R c x) ∧ (gvA α).D0.g c = (gvA β).D0.g c
  gate : ∀ β, β < α → (gvA α).D0.g (gvA β).D0.B = 0

theorem gvAInv_succ {α : Ordinal.{0}} (H : GvAInv α gvA) (T : GvATop α) : GvAInv (α + 1) gvA where
  P0 := fun β h => by
    rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
    · exact H.P0 β h'
    · exact T.P0
  i0 := fun β h => by
    rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
    · exact H.i0 β h'
    · exact T.i0
  i := fun β h => by
    rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
    · exact H.i β h'
    · exact T.i
  coh := fun β γ hβγ h c hc => by
    rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
    · exact H.coh β γ hβγ h' c hc
    · rcases hβγ.lt_or_eq with h'' | rfl
      · exact T.coh β h'' c hc
      · exact ⟨fun _ => rfl, rfl⟩
  gate := fun β γ hβγ h => by
    rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
    · exact H.gate β γ hβγ h'
    · exact T.gate β hβγ

theorem gvAInv_lim {l : Ordinal.{0}} (IH : ∀ β, β < l → GvAInv (β + 1) gvA) : GvAInv l gvA where
  P0 := fun β h => (IH β h).P0 β (lt_add_one β)
  i0 := fun β h => (IH β h).i0 β (lt_add_one β)
  i := fun β h => (IH β h).i β (lt_add_one β)
  coh := fun β γ hβγ h => (IH γ h).coh β γ hβγ (lt_add_one γ)
  gate := fun β γ hβγ h => (IH γ h).gate β γ hβγ (lt_add_one γ)

theorem gvATop_zero : GvATop 0 where
  P0 := by rw [gvA_zero, add_zero, mul_one]; rfl
  i0 := by rw [gvA_zero]; rfl
  i := fun x _ => by rw [gvA_zero, add_zero, mul_one]; rfl
  coh := fun _ h => absurd h (not_lt.2 zero_le)
  gate := fun _ h => absurd h (not_lt.2 zero_le)

theorem gvATop_succ {α : Ordinal.{0}} (H : GvAInv (α + 1) gvA) : GvATop (α + 1) where
  P0 := by
    rw [gvA_succ]
    show (gvA α).P0 + Om1 = _
    rw [H.P0 α (lt_add_one α), add_assoc, ← mul_add_one, add_assoc 1 α 1]
  i0 := by
    rw [gvA_succ]
    show (gvA α).i0 + Om1 + 1 = (gvA α).P0 + Om1 + 1
    rw [H.i0 α (lt_add_one α), add_assoc (gvA α).P0 1 Om1, Br.Om1_eq,
      Fx.fx_Om1_prin.add_eq_right one_lt_Om1]
  i := fun x hx => by
    rw [gvA_succ]
    show (gvA α).i x + x + 1 = _
    rw [H.i α (lt_add_one α) x hx, add_assoc (gpI x + _) 1 x, one_add_of_omega0_le (omega0_lt_inE hx).le,
      add_assoc (gpI x), ← mul_add_one x, add_assoc 1 α 1]
  coh := fun β hβ c hc => by
    have hβα : β ≤ α := Order.lt_add_one_iff.1 hβ
    have hcα : c < (gvA α).D0.B := by
      rcases hβα.lt_or_eq with h | rfl
      · exact hc.trans (H.B_lt h (lt_add_one α))
      · exact hc
    obtain ⟨n1, n2⟩ := gvNext_coh (gvA α) hcα
    obtain ⟨c1, c2⟩ := H.coh β α hβα (lt_add_one α) c hc
    rw [gvA_succ]
    exact ⟨fun x => (n1 x).trans (c1 x), n2.trans c2⟩
  gate := fun β hβ => by
    rcases (Order.lt_add_one_iff.1 hβ).lt_or_eq with h | rfl
    · rw [gvA_succ, (gvNext_coh (gvA α) (H.B_lt h (lt_add_one α))).2]
      exact H.gate β α h (lt_add_one α)
    · rw [gvA_succ]; exact gvNext_gate (gvA β)

theorem gvA_lim_eq {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlE : l < ε₀) (H : GvAInv l gvA) :
    gvA l = gvAStart l hl hlE (gvAExt l fun β _ => gvA β) (H.congr fun β h => gvAExt_eq h) := by
  rw [gvA_limit hl]; unfold gvALim; rw [dif_pos ⟨hlE, H.congr fun β h => gvAExt_eq h⟩]

theorem gvATop_lim {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlE : l < ε₀) (H : GvAInv l gvA) : GvATop l := by
  have hl1 := gvA_l1 hl hlE
  set Hx := H.congr fun β h => gvAExt_eq (l := l) h
  set C := gvACh l hl hlE (gvAExt l fun β _ => gvA β) Hx with hC
  have e : gvA l = gvAStart l hl hlE (gvAExt l fun β _ => gvA β) Hx := gvA_lim_eq hl hlE H
  have hD : ∀ k, C.D k = (gvA (gqFs l k)).D0 := fun k => by
    show (gvAExt l (fun β _ => gvA β) (gqFs l k)).D0 = _
    rw [gvAExt_eq (gqFs_lt hl hl1 k)]
  have hDl : (gvA l).D0 = C.lim.step := by rw [e]; rfl
  have hlw : ω ≤ l := gvA_wl hl hlE
  refine ⟨?_, ?_, fun x hx => ?_, fun β hβ c hc => ?_, fun β hβ => ?_⟩
  · rw [e]; show gcG 0 + Om1 * l = _; rw [one_add_of_omega0_le hlw]
  · rw [e]; rfl
  · rw [e]; show gpI x + x * l + 1 = _; rw [one_add_of_omega0_le hlw]
  · obtain ⟨k, hk⟩ := gqFs_cof hl hl1 β hβ
    have hck : c < (C.D k).B := by rw [hD]; exact hc.trans (H.B_lt hk (gqFs_lt hl hl1 k))
    have hcl : c < C.lim.B := hck.trans (C.B_lt k)
    obtain ⟨c1, c2⟩ := H.coh β _ hk.le (gqFs_lt hl hl1 k) c hc
    rw [hDl]
    refine ⟨fun x => ?_, ?_⟩
    · rw [GsD.step_R_low _ hcl, C.lim_R hck, hD]; exact c1 x
    · rw [GsD.step_g_low _ hcl, C.lim_g hck, hD]; exact c2
  · obtain ⟨k, hk⟩ := gqFs_cof hl hl1 β hβ
    have hck : (gvA β).D0.B < (C.D k).B := by rw [hD]; exact H.B_lt hk (gqFs_lt hl hl1 k)
    have hcl : (gvA β).D0.B < C.lim.B := hck.trans (C.B_lt k)
    rw [hDl, GsD.step_g_low _ hcl, C.lim_g hck, hD]
    exact H.gate β _ hk (gqFs_lt hl hl1 k)

/-- **THE INVARIANT AT EVERY `α < ε₀`.** -/
theorem gvA_inv : ∀ α : Ordinal.{0}, α < ε₀ → GvAInv (α + 1) gvA := by
  intro α
  induction α using Ordinal.limitRecOn with
  | zero => intro _; exact gvAInv_succ (gvAInv_zero gvA) gvATop_zero
  | add_one μ ih =>
    intro hα
    have H := ih ((lt_add_one μ).trans hα)
    exact gvAInv_succ H (gvATop_succ H)
  | limit l hl ih =>
    intro hα
    have H := gvAInv_lim (fun β hβ => ih β hβ (hβ.trans hα))
    exact gvAInv_succ H (gvATop_lim hl hα H)

theorem gvA_P0 {α : Ordinal.{0}} (hα : α < ε₀) : (gvA α).P0 = gcG 0 + Om1 * (1 + α) :=
  (gvA_inv α hα).P0 α (lt_add_one α)

theorem gvA_i0 {α : Ordinal.{0}} (hα : α < ε₀) : (gvA α).i0 = (gvA α).P0 + 1 :=
  (gvA_inv α hα).i0 α (lt_add_one α)

/-- **The bound of the union over the `α`-th start**: `ε_{G+Ω₁·(1+α+1)}`. -/
theorem gvA_UB {α : Ordinal.{0}} (hα : α < ε₀) :
    (gvUof (gvA α)).B = veblen 1 (gcG 0 + Om1 * (1 + α + 1)) := by
  rw [gvUof_B, gvA_i0 hα, gvA_P0 hα, add_assoc (gcG 0 + _) 1 Om1, Br.Om1_eq,
    Fx.fx_Om1_prin.add_eq_right one_lt_Om1, ← Br.Om1_eq, add_assoc (gcG 0), ← mul_add_one (Om1 : Ordinal.{0})]

/-! ## The frontier `ι(Γ(ε_{G+Ω₁·ε₀}))` -/

/-- **The new bound** `ε_{G+Ω₁·ε₀}`. -/
noncomputable def gvE0 : Ordinal.{0} := veblen 1 (gcG 0 + Om1 * ε₀)

theorem gvE0_codes {c : Ordinal.{0}} (hc : c < gvE0) : ∃ α, α < ε₀ ∧ c < (gvUof (gvA α)).B := by
  have hεl : IsSuccLimit (ε₀ : Ordinal.{0}) := ev_isSuccLimit_of_inE (omega0_opow_epsilon 0)
  have hl : IsSuccLimit (Om1 * ε₀ : Ordinal.{0}) := isSuccLimit_mul_right gv_Om1_pos hεl
  obtain ⟨t, ht, hct⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ hl)).1 hc
  obtain ⟨d, hd, htd⟩ := (lt_add_iff hl.bot_lt.ne').1 ht
  obtain ⟨m, hm, hdm⟩ := (lt_mul_iff_of_isSuccLimit hεl).1 hd
  refine ⟨m, hm, ?_⟩
  rw [gvA_UB hm]
  refine hct.trans_le ((isNormal_veblen 1).monotone (htd.trans ((add_le_add_iff_left _).2 ?_)))
  exact hdm.le.trans (mul_le_mul_left' (le_add_self.trans le_self_add) _)

/-- **`ι(Γ(ε_{G+Ω₁·ε₀})) = sup_{α<ε₀} ι(Γ(ε_{G+Ω₁·(1+α+1)})·ω)`.** -/
theorem gvE0_cof (S : InaccSeq.{0}) {l : Ordinal.{0}} (hl : l < iota S (gcG gvE0)) :
    ∃ α, α < ε₀ ∧ l < iota S (gcG (gvUof (gvA α)).B * ω) := by
  have hlim : IsSuccLimit (gcG gvE0) := ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC (gcG_SC _))
  rw [iota_limit hlim] at hl
  haveI : Nonempty (Iio (gcG gvE0)) := ⟨⟨0, hlim.bot_lt⟩⟩
  obtain ⟨e, he⟩ := (lt_ciSup_iff (iota_bdd _)).1 hl
  have hWl : IsSuccLimit gvE0 := ev_isSuccLimit_of_inE (omega0_opow_epsilon _)
  obtain ⟨β, hβ, heβ⟩ := gcG_lt_of_lt_limit hWl e.2
  obtain ⟨α, hα, hk⟩ := gvE0_codes hβ
  refine ⟨α, hα, he.trans_le (iota_mono _ _ ((heβ.trans (gcG_lt hk)).trans_le ?_).le)⟩
  exact le_mul_of_one_le_right' one_lt_omega0.le

/-- **ENUM-REACH at every range restart below `ι(Γ(ε_{G+Ω₁·ε₀}))`, fixed points included** (UNCONDITIONAL). -/
theorem gvE0_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG gvE0)) :
    CdUpper S l ∧ CdLower S l := by
  obtain ⟨α, -, h⟩ := gvE0_cof S hl
  exact gvLocU_enum (gvA α) S hr h

/-- **CapV at every range restart below `ι(Γ(ε_{G+Ω₁·ε₀}))`** (UNCONDITIONAL). -/
theorem gvE0_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG gvE0)) :
    CdCapV S l := by
  obtain ⟨α, -, h⟩ := gvE0_cof S hl
  exact gvLocU_capV (gvA α) S hr h

/-- **THE ROAD**: UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ(ε_{G+Ω₁·ε₀}))` (CapV also `υ_λ < L(ω)`), (CL), EQ,
TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem gvE0_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG gvE0) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG gvE0) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG gvE0) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  gv_road_of S _ (fun _ hr h => gvE0_enum S hr h) (fun _ hr h => gvE0_capV S hr h) hU hL hV hC hEQ hrest hB2

theorem gvE0_lt_G1 : gvE0 < gcG 1 := by
  have hE : InE (gcG 1) := Low.opow_eq_self_of_SC (gcG_SC 1)
  have hOw : (Om1 : Ordinal.{0}) * ε₀ < gcG 1 :=
    InE.mul_lt hE gv_Om1_lt_G1 (gv_eps0_lt_Om1.trans gv_Om1_lt_G1)
  have h1 : gcG 0 + Om1 * ε₀ < gcG 1 := (inE_indec hE).add_lt (gcG_lt zero_lt_one) hOw
  exact (gcG_SC 1).2 1 (one_lt_omega0.trans (omega0_lt_inE hE)) _ h1

/-- **`Γ(ε_{G+Ω₁·ε₀}) < Ω₂`.** -/
theorem gvE0_le_Om2 : gcG gvE0 < Om (1 + 1) := by
  have hBE : InE Tf.tfBG := Low.opow_eq_self_of_SC Tf.tfBG_SC
  have hO : (Om1 : Ordinal.{0}) < Tf.tfBG := Tf.tfBG_gt
  have h1 : (1 : Ordinal.{0}) < Tf.tfBG := one_lt_omega0.trans (omega0_lt_inE hBE)
  have hG1 : gcG 1 < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) h1)
  have h2 : gcG gvE0 < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) (gvE0_lt_G1.trans hG1))
  exact h2.trans Tf.tfBG_lt_Om2

/-- **`P(Γ(ε_{G+Ω₁·ε₀})) < L(0)`.** -/
theorem gvE0_P (S : InaccSeq.{0}) : Pv S (gcG gvE0) < Nc.ncL S 0 := ga_Pv_lt_L0 S gvE0_le_Om2.le

/-- **The order of the frontiers**: `ι(Γ(ε_{G+Ω₁·ω·2})) ≤ ι(Γ(ε_{G+Ω₁·ε₀})) ≤ ι(Ω₂)`, `ε_{G+Ω₁·ω·2} < ε_{G+Ω₁·ε₀}`,
`P(Γ(ε_{G+Ω₁·ε₀})) ≤ P(Ω₂) < L(0)`. -/
theorem gvE0_fr_order (S : InaccSeq.{0}) :
    gvW2 < gvE0 ∧ iota S (gcG gvW2) ≤ iota S (gcG gvE0) ∧ iota S (gcG gvE0) ≤ iota S (Om (1 + 1)) ∧
      Pv S (gcG gvE0) ≤ Pv S (Om (1 + 1)) ∧ Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have hlt : gvW2 < gvE0 := by
    refine (isNormal_veblen 1).strictMono ?_
    rw [add_assoc, ← mul_add]
    refine (add_lt_add_iff_left _).2 ((mul_lt_mul_iff_right₀ gv_Om1_pos).2 ?_)
    have hεl : IsSuccLimit (ε₀ : Ordinal.{0}) := ev_isSuccLimit_of_inE (omega0_opow_epsilon 0)
    have hw : ω < (ε₀ : Ordinal.{0}) := omega0_lt_inE (omega0_opow_epsilon 0)
    exact (inE_indec (omega0_opow_epsilon 0)).add_lt hw hw
  exact ⟨hlt, iota_mono _ _ (gcG_lt hlt).le, iota_mono _ _ gvE0_le_Om2.le, Nm.Pv_mono gvE0_le_Om2.le,
    ga_Pv_lt_L0 S le_rfl⟩

end Googology.Trans.PoR.InaccPsi.R2.Gv

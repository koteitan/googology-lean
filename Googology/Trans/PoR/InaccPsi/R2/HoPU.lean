import Googology.Trans.PoR.InaccPsi.R2.HoPG

/-!
# HoPU: THE LEVEL `Ω₁³` READ AS `x·x·x`: THE UNION OF ALL `hoSg ν`, `ν < Ω₁`, LOCATED

The systems `hoSg ν` (bound `φ(Ω₁²·(1+ν), G+1)`, base gate `hlGt (1+ν)`) for every `ν < Ω₁` have a union (`Ho.hoOU`):
a gated digit system with the bound `φ(Ω₁³, G+1)`, the base gate `0` and the base reading `φ(x·x·x, Γ_{x+1}+1)`
(Lemma EXACT for `ρ·ρ·ρ`: `ho_pi_cube`).  Its bound is located, with BLK^O, exact reaches, ENUM-REACH and CapV below
`ι(Γ(φ(Ω₁³, G+1))·ω)`, all UNCONDITIONAL.  Every intermediate system `hoSg ν` with gate below `K` is located too
(`hoSg_loc`; e.g. every `ν < ε₀`, among them `φ(Ω₁²·k, G+1)`, `k < ω`, and `φ(Ω₁²·ω, G+1)`).

* `ho_pi_cube`, `ho_cof_sq`, `ho_OOO_mem`, `hoB3`, `hoPFam`, `hoUf` (**THE UNION**);
* `hoUf_loc` (**`φ(Ω₁³, G+1)` IS LOCATED**), `hoUf_blk`, `hoUf_enum`, `hoUf_capV`, `hoUf_road`, `hoUf_fr_order`,
  `hoUf_hyp_iff`; `hoSg_loc`, `hoSg_enum`, `hoSg_capV`.

No new axiom.  New definitions: `hoB3`, `hoPFam`, `hoUf`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ho

open Googology.Trans.PoR.InaccPsi.R2.Hn Googology.Trans.PoR.InaccPsi.R2.Hl
open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk
open Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **Lemma EXACT for `ρ·ρ·ρ`**: `π_{σ,ρ}(ρ·ρ·ρ) = σ·σ·σ` (`ρ·ρ·ρ = ω^{ρ+ρ+ρ} = ϑ^ρ(ρ+ρ)`). -/
theorem ho_pi_cube {s r : Ordinal.{0}} (hB : Bases s r) : r * r * r ∈ TB r s ∧ pi s r (r * r * r) = s * s * s := by
  obtain ⟨hsE, hrE, hsr, hr1⟩ := hB
  have hB' : Bases s r := ⟨hsE, hrE, hsr, hr1⟩
  obtain ⟨bT, bP⟩ := pi_base hB'
  obtain ⟨g1, g2⟩ := pi_add hB' bT bT
  rw [bP] at g2
  have hO : r + r < Om1 := (inE_indec gl_Om1_E).add_lt hr1 hr1
  have h1 : (1 : Ordinal.{0}) ≤ r + r := (one_le_iff_pos.2 hrE.pos).trans le_self_add
  have hv := ho_vt_opow hrE hr1 h1 le_rfl
  obtain ⟨hvT, hvP⟩ := vt_mem hrE hr1 g1.1 hO
  have hc : ∀ t : Ordinal.{0}, ω ^ t = t → t * t * t = ω ^ (t + (t + t)) := by
    intro t ht
    have := ho_sq_opow ht t
    rw [ht] at this
    rw [this, add_assoc]
  rw [hc r hrE, hc s hsE]
  refine ⟨by rw [← hv]; exact ⟨hvT, by rw [hvP]; exact g1.2⟩, ?_⟩
  rw [← hv, pi_vt hB' g1 hO, g2, ho_vt_opow hsE (hsr.trans hr1) ((one_le_iff_pos.2 hsE.pos).trans le_self_add) le_rfl]

/-- **`b < a·M` (`M` a limit) gives `b + 1 < a·(1+ν)` for some `ν < M`.** -/
theorem ho_cof_sq {a b M : Ordinal.{0}} (ha : 0 < a) (hM : IsSuccLimit M) (hb : b < a * M) :
    ∃ ν, ν < M ∧ b + 1 < a * (1 + ν) := by
  have hdiv : b / a < M := (lt_mul_iff_div_lt ha.ne').1 hb
  refine ⟨b / a + 1 + 1, hM.add_one_lt (hM.add_one_lt hdiv), ?_⟩
  calc b + 1 ≤ a * (b / a) + a := Order.add_one_le_of_lt (lt_mul_div_add b ha.ne')
  _ = a * (b / a + 1) := by rw [mul_add_one]
  _ < a * (b / a + 1 + 1) := mul_lt_mul_of_pos_left (lt_add_one _) ha
  _ ≤ a * (1 + (b / a + 1 + 1)) := mul_le_mul_left' le_add_self _

theorem ho_OOO_lt_G (α : Ordinal.{0}) : (Om1 : Ordinal.{0}) * Om1 * Om1 < gcG α :=
  InE.mul_lt (Low.opow_eq_self_of_SC (gcG_SC α)) (hl_OO_lt_G α) (hg_Om1_lt_G α)

theorem ho_OOO_mem (S : InaccSeq.{0}) (a b : Ordinal.{0}) : (Om1 : Ordinal.{0}) * Om1 * Om1 ∈ S.CSet a b := by
  have h := ho_OO_opow (Om 1)
  rw [hn_Om_E] at h
  rw [show (Om1 : Ordinal.{0}) * Om1 * Om1 = Om1 * Om1 * Om 1 by rw [← Br.Om1_eq], h]
  exact CSet.phi_mem (CSet.zero_mem _ _) (CSet.add_mem (CSet.Om_mem (CSet.one_mem _ _))
    (CSet.add_mem (CSet.Om_mem (CSet.one_mem _ _)) (CSet.Om_mem (CSet.one_mem _ _))))

theorem ho_OOO_ne : (Om1 : Ordinal.{0}) * Om1 * Om1 ≠ 0 := ho_sqv_ne gl_Om1_E hg_one_lt_Om1.le

/-- **`φ(Ω₁³, G+1)`**: the bound of the union over all prefixes. -/
noncomputable def hoB3 : Ordinal.{0} := veblen (Om1 * Om1 * Om1) (gcG 0 + 1)

theorem hoB3_lt1 : hoB3 < gcG 1 := by
  have hG1 := gcG_SC 1
  have hE := Low.opow_eq_self_of_SC hG1
  have hfix : veblen (Om1 * Om1 * Om1) (gcG 1) = gcG 1 := gn_veb_fix hG1 (ho_OOO_lt_G 1)
  have h2 := (isNormal_veblen (Om1 * Om1 * Om1)).strictMono
    ((ev_isSuccLimit_of_inE hE).add_one_lt (gcG_lt zero_lt_one))
  unfold hoB3; rwa [hfix] at h2

theorem ho_x3_ne {x : Ordinal.{0}} (hx : InE x) : x * x * x ≠ 0 :=
  ho_sqv_ne hx (one_lt_omega0.trans (omega0_lt_inE hx)).le

theorem ho_1nu_lt {x ν : Ordinal.{0}} (hx : InE x) (hν : ν < x) : 1 + ν < x :=
  (inE_indec hx).add_lt (one_lt_omega0.trans (omega0_lt_inE hx)) hν

theorem ho_two_lt_cube {x : Ordinal.{0}} (hx : InE x) : (2 : Ordinal.{0}) < x * x * x :=
  (show (2 : Ordinal.{0}) < ω from by exact_mod_cast natCast_lt_omega0 2).trans ((omega0_lt_inE hx).trans
    ((hl_lt_sq hx).trans_le (le_mul_of_one_le_right' (one_lt_omega0.trans (omega0_lt_inE hx)).le)))

/-- **THE FAMILY `hoSg ν`, `ν < Ω₁`, AS AN `Ho.HoFam`**: bound `φ(Ω₁³, G+1)`, gate `0`, base reading
`φ(x·x·x, Γ_{x+1}+1)`. -/
noncomputable def hoPFam : HoFam where
  D := hoSg
  B := hoB3
  γ := 0
  b := fun x => veblen (x * x * x) (lgG x + 1)
  Zo := hoZo
  γ_lt := gv_Om1_pos
  γ_cl := fun _ hZ _ _ => hZ.1
  G_lt := (lt_add_one _).trans_le (right_le_veblen _ _)
  B_E := gg_veblen_eps ho_OOO_ne
  B_lt1 := hoB3_lt1
  B_fix1 := veblen_veblen_of_lt (ho_sqv_one gl_Om1_E hg_one_lt_Om1.le) _
  B_mem := fun S a b ha _ => CSet.phi_mem (ho_OOO_mem S a b) (CSet.succ_mem (gmS_G0_mem S ha))
  DB_lt := fun ν hν => by
    rw [hoSg_B hν]; exact hd_veb_left_lt (mul_lt_mul_of_pos_left (hl_one_add hν) ho_OO_pos) _
  B_cof := fun c hc => by
    obtain ⟨b, hb, hcb⟩ := hgVeb_cof ho_OOO_ne (gn_veb_fix (gcG_SC 0) (ho_OOO_lt_G 0)) hc
    obtain ⟨ν, hν, hb1⟩ := ho_cof_sq ho_OO_pos gl_Om1_lim hb
    refine ⟨ν, hν, ?_⟩
    rw [hoSg_B hν, ← hdNx_fixP (hoG_fixv (hl_one_add hν))]
    exact hcb.trans (hdN_lt_Nx hb1)
  ext := fun _ _ h hν c x hc => hoSg_ext hν h hc x
  small := hoSg_small
  γD := fun x hx _ _ ν hν => by
    rw [hoSg_γ (hν.trans ‹x < Om1›)]
    exact max_lt hx.pos ((hlGt_le _).trans_lt (ho_1nu_lt hx hν))
  bD := fun x hx hx1 _ ν hν => by
    rw [hoGSh_b (hν.trans hx1) (hoSg_sh _) hx hx1 ((hlGt_le _).trans_lt (ho_1nu_lt hx hν))]
    exact hd_veb_left_lt (ho_xsqv_lt3 hx (ho_1nu_lt hx hν)) _
  ZD := fun x hx hx1 _ ν hν => by
    rw [hoGSh_Z (hν.trans hx1) (hoSg_sh _) hx hx1, if_pos ((hlGt_le _).trans_lt (ho_1nu_lt hx hν))]
    exact (hb_evZ_lt_fix2 (veblen_veblen_of_lt (ho_two_lt_cube hx) _)
      (hd_veb_left_lt (ho_xsqv_lt3 hx (ho_1nu_lt hx hν)) _)).le
  b_cof := fun x hx hx1 _ ν' hν' => by
    obtain ⟨b, hb, hνb⟩ := hgVeb_cof (ho_x3_ne hx) (hjG_fix hx hx1 (ho_cube_one hx) (ho_cube_lt hx hx1)) hν'
    obtain ⟨ν, hν, hb1⟩ := ho_cof_sq (mul_pos hx.pos hx.pos) (ev_isSuccLimit_of_inE hx) hb
    refine ⟨ν, hν, ?_⟩
    rw [hoGSh_b (hν.trans hx1) (hoSg_sh _) hx hx1 ((hlGt_le _).trans_lt (ho_1nu_lt hx hν)),
      ho_x1v hx hx1 le_self_add (ho_1nu_lt hx hν)]
    exact hνb.trans (hdN_lt_Nx hb1)
  b_E := fun x hx _ _ => gg_veblen_eps (ho_x3_ne hx)
  x_lt_b := fun x hx hx1 _ => (lgG_facts hx hx1).2.1.trans ((lt_add_one _).trans_le (right_le_veblen _ _))
  b_fix1 := fun x hx _ _ => veblen_veblen_of_lt (ho_sqv_one hx (one_lt_omega0.trans (omega0_lt_inE hx)).le) _
  b_lt1 := fun x hx hx1 _ => by rw [← hoZo_eq hx]; exact hoZo_G1 x hx hx1
  b_pi := fun σ ρ hB _ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    rw [← hdNx_fixP (hjG_fix hB.2.1 hρ1 (ho_cube_one hB.2.1) (ho_cube_lt hB.2.1 hρ1)),
      ← hdNx_fixP (hjG_fix hB.1 hσ1 (ho_cube_one hB.1) (ho_cube_lt hB.1 hσ1))]
    exact hjG_S_pi hB (ho_pi_cube hB) (ho_cube_one hB.2.1) (ho_cube_lt hB.2.1 hρ1) (ho_cube_one hB.1)
      (ho_cube_lt hB.1 hσ1)
  Z_low := fun _ _ x hx _ h => absurd hx.pos h
  Zo_fix := hoZo_fix
  Zo_G1 := hoZo_G1

/-- **THE UNION OVER ALL PREFIXES `Ω₁²·(1+ν)`, `ν < Ω₁`**: a gated digit system with the bound `φ(Ω₁³, G+1)`, the base
gate `0`, the base reading `φ(x·x·x, Γ_{x+1}+1)`. -/
noncomputable def hoUf : HgVD := hoOU hoPFam

theorem hoUf_B : hoUf.B = veblen (Om1 * Om1 * Om1) (gcG 0 + 1) := rfl

theorem hoUf_γ : hoUf.γ = 0 := rfl

theorem hoUf_b (x : Ordinal.{0}) : hoUf.b x = veblen (x * x * x) (lgG x + 1) := rfl

/-- **The union extends every `hoSg ν`, `ν < Ω₁`.** -/
theorem hoUf_R {ν c : Ordinal.{0}} (hν : ν < Om1) (hc : c < (hoSg ν).B) (x : Ordinal.{0}) :
    hoUf.R c x = (hoSg ν).R c x := hoOU_R hoPFam hν hc x

theorem hoUf_g {ν c : Ordinal.{0}} (hν : ν < Om1) (hc : c < (hoSg ν).B) : hoUf.g c = (hoSg ν).g c :=
  hoOU_g hoPFam hν hc

/-- **`Γ(φ(Ω₁³, G+1)) < Ω₂`.** -/
theorem hoB3_lt_Om2 : gcG hoB3 < Om (1 + 1) := by
  have hBE : InE Tf.tfBG := Low.opow_eq_self_of_SC Tf.tfBG_SC
  have hO : (Om1 : Ordinal.{0}) < Tf.tfBG := Tf.tfBG_gt
  have h1 : (1 : Ordinal.{0}) < Tf.tfBG := one_lt_omega0.trans (omega0_lt_inE hBE)
  have hG1 : gcG 1 < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) h1)
  have h2 : gcG hoB3 < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) (hoB3_lt1.trans hG1))
  exact h2.trans Tf.tfBG_lt_Om2

section Loc

variable (S : InaccSeq.{0})

theorem hoUf_γK : hoUf.γ < Td.tdK S := hg_K_pos S

/-- **`φ(Ω₁³, G+1)` IS LOCATED**: `Λ⁺ = ι(Γ(φ(Ω₁³, G+1))·ω)`, `P(…) < L(0)` (UNCONDITIONAL). -/
theorem hoUf_loc : ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG hoUf.B * ω) ∧
    upsilon (xtB1 X) = Pv S (gcG hoUf.B * ω) ∧ Pv S (gcG hoUf.B * ω) < Nc.ncL S 0 :=
  hgV_locD hoUf S (hoUf_γK S)

/-- **Theorem BLK^O below `P(Γ(φ(Ω₁³, G+1))·ω)`, with the exact reaches** (UNCONDITIONAL). -/
theorem hoUf_blk :
    let X := gsX hoUf.step.toRS _ hoUf.E_lt_B.le hoUf.B_lt_NB S (hgV_locD_g hoUf S (hoUf_γK S))
    (∀ c' d, c' < d → d < upsilon (xtB1 X) → (le2 c' d ↔ ∃ μ, ∃ j : ℕ, (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 X ∧
        c' = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧ d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 X →
      (∀ c' < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c' g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec X l)) ∧
    (∀ α < upsilon (xtB1 X), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  hgV_locD_blk hoUf S (hoUf_γK S)

/-- **ENUM-REACH at every range restart below `ι(Γ(φ(Ω₁³, G+1))·ω)`, fixed points included** (UNCONDITIONAL). -/
theorem hoUf_enum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG hoUf.B * ω)) :
    CdUpper S l ∧ CdLower S l := hgV_locD_enum hoUf S (hoUf_γK S) hr hl

/-- **CapV at every range restart below `ι(Γ(φ(Ω₁³, G+1))·ω)`** (UNCONDITIONAL). -/
theorem hoUf_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG hoUf.B * ω)) : CdCapV S l :=
  hgV_locD_capV hoUf S (hoUf_γK S) hr hl

/-- **THE ROAD**: UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ(φ(Ω₁³, G+1))·ω)` (CapV also `υ_λ < L(ω)`), (CL), EQ,
TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem hoUf_road (hU : ∀ l, CdRange S l → iota S (gcG hoUf.B * ω) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG hoUf.B * ω) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG hoUf.B * ω) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  gv_road_of S _ (fun _ hr h => hoUf_enum S hr h) (fun _ hr h => hoUf_capV S hr h) hU hL hV hC hEQ hrest hB2

/-- **The order of the frontiers**: `φ(Ω₁²·2, G+1) < φ(Ω₁³, G+1)`, `ι(Γ(φ(Ω₁²·2, G+1))·ω) ≤ ι(Γ(φ(Ω₁³, G+1))·ω)
≤ ι(Ω₂)` and `P(Γ(φ(Ω₁³, G+1))·ω) ≤ P(Ω₂) < L(0)`. -/
theorem hoUf_fr_order :
    hnB < hoB3 ∧ iota S (gcG hnB * ω) ≤ iota S (gcG hoB3 * ω) ∧
      iota S (gcG hoB3 * ω) ≤ iota S (Om (1 + 1)) ∧
      Pv S (gcG hoB3 * ω) ≤ Pv S (Om (1 + 1)) ∧ Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have hlt : hnB < hoB3 := by
    unfold hnB hoB3
    refine hd_veb_left_lt ?_ _
    rw [← mul_two_eq]
    exact mul_lt_mul_of_pos_left ((show (2 : Ordinal.{0}) < ω from by exact_mod_cast natCast_lt_omega0 2).trans
      (omega0_lt_inE gl_Om1_E)) ho_OO_pos
  have hVw : gcG hoB3 * ω < Om (1 + 1) := by
    have hO2 : InE (Om (1 + 1) : Ordinal.{0}) := Low.opow_eq_self_of_SC Ld.ldOm2_SC
    exact InE.mul_lt hO2 hoB3_lt_Om2 ((omega0_lt_inE hO2))
  refine ⟨hlt, iota_mono _ _ (mul_le_mul_right' (gcG_lt hlt).le ω),
    iota_mono _ _ hVw.le, Nm.Pv_mono hVw.le, ga_Pv_lt_L0 S le_rfl⟩

/-- **NON-VACUITY (relative)**: the hypotheses UPPER, LOWER, CapV of `hoUf_road` (asked from
`ι(Γ(φ(Ω₁³, G+1))·ω)` on) are EQUIVALENT to those of the round-107 road `Hn.hnU_road` (asked from
`ι(Γ(φ(Ω₁²·2, G+1))·ω)` on): the restarts in between are settled unconditionally (`hoUf_enum`, `hoUf_capV`). -/
theorem hoUf_hyp_iff :
    ((∀ l, CdRange S l → iota S (gcG hnU.B * ω) ≤ l → CdUpper S l) ↔
      (∀ l, CdRange S l → iota S (gcG hoUf.B * ω) ≤ l → CdUpper S l)) ∧
    ((∀ l, CdRange S l → iota S (gcG hnU.B * ω) ≤ l → CdLower S l) ↔
      (∀ l, CdRange S l → iota S (gcG hoUf.B * ω) ≤ l → CdLower S l)) ∧
    ((∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG hnU.B * ω) ≤ l → CdCapV S l) ↔
      (∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG hoUf.B * ω) ≤ l → CdCapV S l)) := by
  have hle : iota S (gcG hnU.B * ω) ≤ iota S (gcG hoUf.B * ω) := (hoUf_fr_order S).2.1
  refine ⟨⟨fun h l hr hl => h l hr (hle.trans hl), fun h l hr hl => ?_⟩,
    ⟨fun h l hr hl => h l hr (hle.trans hl), fun h l hr hl => ?_⟩,
    ⟨fun h l hr hu hl => h l hr hu (hle.trans hl), fun h l hr hu hl => ?_⟩⟩
  · rcases lt_or_ge l (iota S (gcG hoUf.B * ω)) with h' | h'
    · exact (hoUf_enum S hr h').1
    · exact h l hr h'
  · rcases lt_or_ge l (iota S (gcG hoUf.B * ω)) with h' | h'
    · exact (hoUf_enum S hr h').2
    · exact h l hr h'
  · rcases lt_or_ge l (iota S (gcG hoUf.B * ω)) with h' | h'
    · exact hoUf_capV S hr h'
    · exact h l hr hu h'

/-! ## Every intermediate prefix with gate below `K` -/

/-- **`φ(Ω₁²·(1+ν), G+1)` IS LOCATED** whenever the gate `hlGt (1+ν)` of the prefix is below `K` (e.g. every
`ν < ε₀`). -/
theorem hoSg_loc {ν : Ordinal.{0}} (hν : ν < Om1) (hK : hlGt (1 + ν) < Td.tdK S) :
    (hoSg ν).B = veblen (Om1 * Om1 * (1 + ν)) (gcG 0 + 1) ∧
    ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG (hoSg ν).B * ω) ∧
      upsilon (xtB1 X) = Pv S (gcG (hoSg ν).B * ω) ∧ Pv S (gcG (hoSg ν).B * ω) < Nc.ncL S 0 :=
  ⟨hoSg_B hν, hgV_locD (hoSg ν) S (by rw [hoSg_γ hν]; exact max_lt (hg_K_pos S) hK)⟩

theorem hoSg_enum {ν : Ordinal.{0}} (hν : ν < Om1) (hK : hlGt (1 + ν) < Td.tdK S) {l : Ordinal.{0}}
    (hr : CdRange S l) (hl : l < iota S (gcG (hoSg ν).B * ω)) : CdUpper S l ∧ CdLower S l :=
  hgV_locD_enum (hoSg ν) S (by rw [hoSg_γ hν]; exact max_lt (hg_K_pos S) hK) hr hl

theorem hoSg_capV {ν : Ordinal.{0}} (hν : ν < Om1) (hK : hlGt (1 + ν) < Td.tdK S) {l : Ordinal.{0}}
    (hr : CdRange S l) (hl : l < iota S (gcG (hoSg ν).B * ω)) : CdCapV S l :=
  hgV_locD_capV (hoSg ν) S (by rw [hoSg_γ hν]; exact max_lt (hg_K_pos S) hK) hr hl

/-- **`φ(Ω₁²·ω, G+1)` IS LOCATED** (the limit of the finite prefixes `Ω₁²·k`). -/
theorem hoSg_omega_loc : (hoSg ω).B = veblen (Om1 * Om1 * ω) (gcG 0 + 1) ∧
    ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG (hoSg ω).B * ω) ∧
      upsilon (xtB1 X) = Pv S (gcG (hoSg ω).B * ω) ∧ Pv S (gcG (hoSg ω).B * ω) < Nc.ncL S 0 := by
  have hω : (ω : Ordinal.{0}) < Om1 := omega0_lt_inE gl_Om1_E
  have h1 : 1 + ω = (ω : Ordinal.{0}) := one_add_omega0
  have hK : hlGt (1 + ω) < Td.tdK S := by
    rw [h1]; unfold hlGt; rw [if_pos (omega0_lt_inE hc_eps0_E)]; exact hg_K_pos S
  obtain ⟨hB, hX⟩ := hoSg_loc S hω hK
  exact ⟨by rw [hB, h1], hX⟩

end Loc

end Googology.Trans.PoR.InaccPsi.R2.Ho

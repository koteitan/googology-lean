import Googology.Trans.PoR.InaccPsi.R2.GvNx

/-!
# THE UNION OF THE STARTS: the bound `ε_{G+Ω₁·ω}` read `φ(1, Γ_{x+1} + x·ω)`, located

The starts `gvSt k` (`R2.GvNx`) have the bases `φ(1, Γ_{x+1} + x·(k+1) + 1)` (`gvSt_i`) and form a chain
(each start is the step of the union over the previous one, which extends it).  Their gated union (`Gs.GsCh.lim`,
base gate `0`) has the bound `ε_{G+Ω₁·ω}` and the base reading `φ(1, Γ_{x+1} + x·ω)`: Lemma EXACT for it is
`Gp.gp_b_pi_code` with `π(ρ·ω) = σ·ω` (`Exact.pi_mul`).  Its step `gvStω` is a new start (index `G + Ω₁·ω + 1`), and
in that step the code `ε_{G+Ω₁·ω}` has gate `0`: **it is located** (`gv_locWW`), with BLK^O, exact reaches, ENUM-REACH
and CapV below `ι(Γ(ε_{G+Ω₁·ω})·ω)`.

* `gvSt_i`, `gvSt_D0B`, `gvSt_coh`, `gvCh` (**THE CHAIN OF THE STARTS**), `gvDω`, `gvDω_B`, `gvStω` (**THE NEXT
  START**), `gv_locWW`, `gv_enumWW`, `gv_capVW`, `gv_blkWW`.

No new axiom.  New definitions: `gvCh`, `gvDω`, `gvStω`.
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

/-- **The base index of the `k`-th start**: `Γ_{x+1} + x·(k+1) + 1` (through `gpI`). -/
theorem gvSt_i : ∀ (k : ℕ) (x : Ordinal.{0}), InE x → (gvSt k).i x = gpI x + x * ((k : Ordinal.{0}) + 1) + 1
  | 0, x, _ => by
    show gpI x + x + 1 = _
    rw [Nat.cast_zero, zero_add, mul_one]
  | k + 1, x, hx => by
    show (gvSt k).i x + x + 1 = _
    rw [gvSt_i k x hx, add_assoc (gpI x + _) 1 x, one_add_of_omega0_le (omega0_lt_inE hx).le,
      add_assoc (gpI x), ← mul_add_one x]
    push_cast; rfl

theorem gvSt_D0B (n : ℕ) : (gvSt n).D0.B = veblen 1 (gcG 0 + Om1 * ((n : Ordinal.{0}) + 1) + 1) := by
  rw [(gvSt n).D0.B_ix, (gvSt n).ix0, gvSt_i0]

theorem gvSt_next (n : ℕ) : (gvSt (n + 1)).D0 = (gvUof (gvSt n)).step := rfl

theorem gvSt_lt_U (n : ℕ) {c : Ordinal.{0}} (hc : c < (gvSt n).D0.B) :
    c < (gvRD (gvSt n) 0).B ∧ c < (gvUof (gvSt n)).B := by
  have h0 : c < (gvRD (gvSt n) 0).B := by rw [gvRD_zero]; exact hc
  exact ⟨h0, h0.trans ((gvFamOf (gvSt n)).B_ltΩ gv_Om1_pos)⟩

/-- **The chain of the starts**: each start extends the previous one (readings and gates). -/
theorem gvSt_coh (n : ℕ) {c : Ordinal.{0}} (hc : c < (gvSt n).D0.B) :
    (∀ x, (gvSt (n + 1)).D0.R c x = (gvSt n).D0.R c x) ∧ (gvSt (n + 1)).D0.g c = (gvSt n).D0.g c := by
  obtain ⟨h0, hU⟩ := gvSt_lt_U n hc
  refine ⟨fun x => ?_, ?_⟩
  · rw [gvSt_next, GvD.step_R_low _ hU x]
    show (gvFamOf (gvSt n)).U.R c x = _
    rw [(gvFamOf (gvSt n)).U_R gv_Om1_pos h0 x]
    show (gvRD (gvSt n) 0).R c x = _
    rw [gvRD_zero]
  · rw [gvSt_next, GvD.step_g_low _ hU]
    show (gvFamOf (gvSt n)).U.g c = _
    rw [(gvFamOf (gvSt n)).U_g gv_Om1_pos h0]
    show (gvRD (gvSt n) 0).g c = _
    rw [gvRD_zero]

theorem gv_Om1w_eq : (Om1 : Ordinal.{0}) * ω = ω ^ (Om 1 + 1) := by
  rw [opow_add, opow_one, Bt.Om1_opow, Br.Om1_eq]

theorem gv_Om1w_prin : IsPrincipal (· + ·) ((Om1 : Ordinal.{0}) * ω) := by
  rw [gv_Om1w_eq]; exact isPrincipal_add_omega0_opow _

theorem gv_xw_prin {x : Ordinal.{0}} (hx : InE x) : IsPrincipal (· + ·) (x * ω) := by
  have e : x * ω = ω ^ (x + 1) := by rw [opow_add, opow_one, hx]
  rw [e]; exact isPrincipal_add_omega0_opow _

theorem gv_prin_add {o a b : Ordinal.{0}} (hp : IsPrincipal (· + ·) o) (ha : a < o) (hb : b < o) : a + b < o :=
  hp ha hb

theorem gv_xw_lt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : x * ω + 1 < lgG x := by
  obtain ⟨-, hxG, -, hGE, -⟩ := lgG_facts hx hx1
  exact (ev_isSuccLimit_of_inE hGE).add_one_lt (InE.mul_lt hGE hxG (omega0_lt_inE hGE))

theorem gv_k_lt_w (k : ℕ) {u : Ordinal.{0}} (hu : 0 < u) : u * ((k : Ordinal.{0}) + 1) < u * ω := by
  refine (mul_lt_mul_iff_right₀ hu).2 ?_
  rw [← Nat.cast_succ]; exact natCast_lt_omega0 _

theorem gvWW_ix_lt : gcG 0 + Om1 * ω < gcG 1 := by
  have hE : InE (gcG 1) := Low.opow_eq_self_of_SC (gcG_SC 1)
  exact (inE_indec hE).add_lt (gcG_lt zero_lt_one) (InE.mul_lt hE gv_Om1_lt_G1 (omega0_lt_inE hE))

theorem gv_one_lt_Om1' : (1 : Ordinal.{0}) < Om1 := one_lt_omega0.trans omega_lt_Om1

/-- **THE CHAIN OF THE STARTS** (base gate `0`, bound `ε_{G+Ω₁·ω}`, base `φ(1, Γ_{x+1} + x·ω)`). -/
noncomputable def gvCh : GsCh where
  D := fun n => (gvSt n).D0
  ixω := gcG 0 + Om1 * ω
  bω := fun x => veblen 1 (gpI x + x * ω)
  baω := fun x => lgG x + (x * ω + 1)
  γω := 0
  γω_lt := gv_Om1_pos
  γ_cl := fun _ hZ _ _ => hZ.1
  γ_le := fun n => (gvSt n).γ0.le
  coh_R := fun n c x hc => (gvSt_coh n hc).1 x
  coh_g := fun n c hc => (gvSt_coh n hc).2
  B_mono := fun n => by
    show (gvSt n).D0.B < (gvSt (n + 1)).D0.B
    rw [gvSt_next]
    have h0 : (gvRD (gvSt n) 0).B < (gvUof (gvSt n)).B := (gvFamOf (gvSt n)).B_ltΩ gv_Om1_pos
    rw [gvRD_zero] at h0
    exact h0.trans (gvUof (gvSt n)).B_lt_NB
  B_lt := fun n => by
    show (gvSt n).D0.B < _
    rw [gvSt_D0B]
    refine (isNormal_veblen 1).strictMono ?_
    rw [add_assoc]
    refine (add_lt_add_iff_left _).2 (gv_prin_add gv_Om1w_prin (gv_k_lt_w n gv_Om1_pos) ?_)
    exact one_lt_omega0.trans_le (le_mul_right _ gv_Om1_pos)
  B_cof := fun c hc => by
    obtain ⟨k, hk⟩ := gvWW_codes hc
    exact ⟨k + 1, by show c < (gvSt (k + 1)).D0.B; rw [gvSt_next]; exact hk.trans (gvUof (gvSt k)).B_lt_NB⟩
  ix_mem := fun S a b ha _ => CSet.add_mem (goGl.ix_mem S a b ha)
    (by rw [gv_Om1w_eq]; exact go_opow_mem (CSet.succ_mem (CSet.Om_mem (CSet.one_mem _ _))))
  ix_lt := gvWW_ix_lt
  cf_g := fun n => by
    show (gvSt (n + 1)).D0.g (gvSt n).D0.B ≤ _
    set St := gvSt n
    have h1 : St.D0.B < (gvRD St (0 + 1)).B := by
      rw [gvRD_succ, gvRD_zero, GsD.step_B]; exact lt_eN _
    have hU : St.D0.B < (gvUof St).B := h1.trans ((gvFamOf St).B_ltΩ (by rw [zero_add]; exact gv_one_lt_Om1'))
    rw [gvSt_next, GvD.step_g_low _ hU]
    show (gvFamOf St).U.g St.D0.B ≤ _
    rw [(gvFamOf St).U_g (by rw [zero_add]; exact gv_one_lt_Om1') h1]
    show (gvRD St (0 + 1)).g St.D0.B ≤ _
    rw [gvRD_succ, gvRD_zero, GsD.step_g_B, St.γ0]
    exact zero_le
  b_le := fun n x hx hx1 _ => by
    rw [(gvSt n).b0 x hx hx1, gvSt_i n x hx]
    refine (isNormal_veblen 1).monotone ?_
    rw [add_assoc]
    refine (add_le_add_iff_left _).2 (gv_prin_add (gv_xw_prin hx) (gv_k_lt_w n hx.pos) ?_).le
    exact one_lt_omega0.trans_le (le_mul_right _ hx.pos)
  b_sup := fun x hx hx1 _ ν hν => by
    have hl : IsSuccLimit (x * ω) := isSuccLimit_mul_right hx.pos isSuccLimit_omega0
    obtain ⟨t, ht, hνt⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ hl)).1 hν
    obtain ⟨d, hd, htd⟩ := (lt_add_iff hl.bot_lt.ne').1 ht
    obtain ⟨m, hm, hdm⟩ := (lt_mul_iff_of_isSuccLimit isSuccLimit_omega0).1 hd
    obtain ⟨n, rfl⟩ := lt_omega0.1 hm
    refine ⟨n, ?_⟩
    rw [(gvSt n).b0 x hx hx1, gvSt_i n x hx]
    refine hνt.trans_le ((isNormal_veblen 1).monotone (htd.trans ?_))
    rw [add_assoc]
    exact (add_le_add_iff_left _).2 ((hdm.le.trans (mul_le_mul_left' (le_self_add : (n : Ordinal.{0}) ≤ n + 1) x)).trans
      le_self_add)
  b_E := fun _ _ _ _ => omega0_opow_epsilon _
  b_eN := fun x hx hx1 _ => gp_b_eN hx hx1 (le_mul_right _ hx.pos) (gv_xw_lt hx hx1)
  ba_lt := fun x hx hx1 _ => by
    have hq := (gm1_facts hx hx1).2.2.2
    have hG : lgG x < gq 1 x := goGl.ba_lt x hx hx1
    exact (inE_indec hq).add_lt hG ((gv_xw_lt hx hx1).trans hG)
  b_Z := fun x hx hx1 _ => by
    refine go_eN_lt_evZ ?_
    have hZ := evZ_E (lgG x)
    have hGE := (lgG_facts hx hx1).2.2.2.1
    have hGZ : lgG x < evZ (lgG x) := lt_evZ _
    have hi : gpI x < evZ (lgG x) := (evIx_le hGE).trans_lt hGZ
    have hxZ : x * ω < evZ (lgG x) := ((lt_add_one _).trans (gv_xw_lt hx hx1)).trans hGZ
    have := (isNormal_veblen 1).strictMono ((inE_indec hZ).add_lt hi hxZ)
    rwa [show veblen 1 (evZ (lgG x)) = evZ (lgG x) from epsilon_evZ _] at this
  b_pi := fun σ ρ hB _ => by
    obtain ⟨m1, m2⟩ := pi_mul hB ω (omega0_lt_inE hB.1)
    exact gp_b_pi_code hB m1 ((lt_add_one _).trans (gv_xw_lt hB.2.1 hB.2.2.2)) (le_mul_right _ hB.2.1.pos) m2
  ba_pi := fun σ ρ hB _ => by
    obtain ⟨g1, g2⟩ : lgG ρ ∈ TB ρ σ ∧ pi σ ρ (lgG ρ) = lgG σ := goGl.ba_pi σ ρ hB
    obtain ⟨m1, m2⟩ := pi_mul hB ω (omega0_lt_inE hB.1)
    obtain ⟨o1, o2⟩ := one_TB hB
    obtain ⟨s1, s2⟩ := pi_add hB m1 o1
    obtain ⟨t1, t2⟩ := pi_add hB g1 s1
    exact ⟨t1, by rw [t2, s2, g2, m2, o2]⟩

/-- **The union of the starts**: bound `ε_{G+Ω₁·ω}`, base gate `0`. -/
noncomputable def gvDω : GsD := gvCh.lim

theorem gvDω_B : gvDω.B = gvWW := rfl

theorem gvDω_γ : gvDω.γ = 0 := rfl

/-- **THE NEXT START**: the step of the union of the starts (index `G + Ω₁·ω + 1`, base `φ(1, Γ_{x+1} + x·ω + 1)`). -/
noncomputable def gvStω : GvSt where
  D0 := gvDω.step
  i0 := gcG 0 + Om1 * ω + 1
  i := fun x => gpI x + x * ω + 1
  a := fun x => lgG x + (x * ω + 1) + 1
  P0 := gcG 0 + Om1 * ω
  j0 := 1
  γ0 := rfl
  ix0 := rfl
  b0 := fun x _ _ => by
    show eN (veblen 1 (gpI x + x * ω)) = _
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

/-! ## The code `ε_{G+Ω₁·ω}` is located -/

section Loc

variable (S : InaccSeq.{0})

theorem gvWW_E : gfE ≤ gvDω.B := gvDω.E_lt_B.le

theorem gvWW_lt_S : gvDω.B < gvDω.step.B := by rw [GsD.step_B]; exact lt_eN _

theorem gvWW_g : gvDω.step.toRS.K.gt gvDω.B < Td.tdK S := by
  rw [GsD.toRS_gt, GsD.step_g_B, gvDω_γ]; exact gv_K_pos S

/-- **THE CODE `ε_{G+Ω₁·ω}` IS LOCATED**: `Λ⁺ = ι(Γ(ε_{G+Ω₁·ω})·ω)`, `P(Γ(ε_{G+Ω₁·ω})·ω) < L(0)`. -/
theorem gv_locWW : ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG gvWW * ω) ∧
    upsilon (xtB1 X) = Pv S (gcG gvWW * ω) ∧ Pv S (gcG gvWW * ω) < Nc.ncL S 0 :=
  ⟨gsX gvDω.step.toRS _ gvWW_E gvWW_lt_S S (gvWW_g S), gsX_pkg gvDω.step.toRS _ gvWW_E gvWW_lt_S S (gvWW_g S),
    gsLoc gvDω.step.toRS _ gvWW_E gvWW_lt_S S (gvWW_g S)⟩

theorem gv_enumWW {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG gvWW * ω)) :
    CdUpper S l ∧ CdLower S l :=
  gsEnum gvDω.step.toRS _ gvWW_E gvWW_lt_S S (gvWW_g S) hr hl

theorem gv_capVW {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG gvWW * ω)) : CdCapV S l :=
  gsCapV gvDω.step.toRS _ gvWW_E gvWW_lt_S S (gvWW_g S) hr hl

/-- **Theorem BLK^O below `P(Γ(ε_{G+Ω₁·ω})·ω)`**, with the exact reaches. -/
theorem gv_blkWW :
    let X := gsX gvDω.step.toRS _ gvWW_E gvWW_lt_S S (gvWW_g S)
    (∀ c' d, c' < d → d < upsilon (xtB1 X) → (le2 c' d ↔ ∃ μ, ∃ j : ℕ, (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 X ∧
        c' = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧ d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 X →
      (∀ c' < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c' g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec X l)) ∧
    (∀ α < upsilon (xtB1 X), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  gsBlk gvDω.step.toRS _ gvWW_E gvWW_lt_S S (gvWW_g S)

end Loc

end Googology.Trans.PoR.InaccPsi.R2.Gv

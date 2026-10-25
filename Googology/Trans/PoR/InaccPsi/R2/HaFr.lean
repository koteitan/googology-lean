import Googology.Trans.PoR.InaccPsi.R2.HaLRec

/-!
# HaFr: THE FRONTIER `ι(Γ(φ(3, G+1)))`

The `ζ`-indices `λ_0 = 0`, `λ_{k+1} = φ(2, G + 1 + λ_k)` (`haZt`) are cofinal in `φ(3, G+1)` (`haT_cof`); the start
`haLU λ_k` has the bound `λ_{k+1}` and base gate below every base (`haZt_gate`: the gate of the code `λ_{k+1}` is the
base gate of `haLU λ_k`), so every `λ_{k+1}` is located (`haZt_loc`).  More generally the bound `ζ_{G+1+λ}` of every
start whose `ζ`-index has gate below `K` is located (`haLU_loc`), and so is every system of its stage (`haLD_loc`).
**The new frontier is `ι(Γ(φ(3, G+1)))`** (was `ι(Γ(ζ_{G+ε₀}))`): ENUM-REACH and CapV at every range restart below
it, BLK^O and exact reaches below each located bound, unconditionally; the road asks UPPER, LOWER, CapV only above it.

* `haZt`, `haZt_lt_T`, `haZt_B`, `haT_cof` (**the tower is cofinal in `φ(3, G+1)`**), `haZt_gate`, `haZt_K`,
  `haZt_loc`, `haLU_loc`, `ha_gate_lt_K`, `ha_K_lt_T`, `haLU_loc_K` (**every constant `λ < K`**), `haLD_loc`,
  `haT_codes`, `haT_iota_cof`, `haT_enum`, `haT_capV`, `haT_blk`, `haT_road`
  (**THE ROAD**), `haT_lt_G1`, `haT_le_Om2`, `haT_P`, `haT_fr_order`.

No new axiom.  New definition: `haZt`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ha

open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Gw
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

/-! ## The tower of `ζ`-indices -/

/-- **The tower of `ζ`-indices**: `λ_0 = 0`, `λ_{k+1} = φ(2, G + 1 + λ_k)`. -/
noncomputable def haZt : ℕ → Ordinal.{0}
  | 0 => 0
  | k + 1 => veblen 2 (gcG 0 + 1 + haZt k)

theorem haZt_lt_T : ∀ k : ℕ, haZt k < haT
  | 0 => ha_zero_lt_T
  | k + 1 => ha_Q_lt_T (haZt_lt_T k)

theorem haZt_B (k : ℕ) : (haLU (haZt k)).B = haZt (k + 1) := haLU_B (haZt_lt_T k)

theorem haZt_lt_succ (k : ℕ) : haZt k < haZt (k + 1) := ha_lt_Q (haZt_lt_T k)

theorem haT_nfp : haT = nfp (veblen 2) (gcG 0 + 1) := by
  have e3 : (3 : Ordinal.{0}) = 2 + 1 := by
    have : ((2 : ℕ) : Ordinal.{0}) + 1 = ((3 : ℕ) : Ordinal.{0}) := by push_cast; rfl
    exact_mod_cast this.symm
  have h3G : (3 : Ordinal.{0}) < gcG 0 := by
    have : ((3 : ℕ) : Ordinal.{0}) < gcG 0 := (natCast_lt_omega0 3).trans (omega0_lt_inE gr_G_inE)
    exact_mod_cast this
  have hG : deriv (veblen 2) (gcG 0) = gcG 0 := by
    rw [← veblen_add_one, ← e3]; exact gn_veb_fix (gcG_SC 0) h3G
  unfold haT
  rw [e3, veblen_add_one, deriv_add_one, hG]

theorem haZt_iter (n : ℕ) : (veblen 2)^[n] (gcG 0 + 1) ≤ haZt (n + 1) := by
  induction n with
  | zero =>
    show gcG 0 + 1 ≤ veblen 2 (gcG 0 + 1 + 0)
    rw [add_zero]; exact right_le_veblen 2 _
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    show veblen 2 _ ≤ veblen 2 (gcG 0 + 1 + haZt (n + 1))
    exact (isNormal_veblen 2).monotone (ih.trans le_add_self)

/-- **The tower is cofinal in `φ(3, G+1)`.** -/
theorem haT_cof {c : Ordinal.{0}} (hc : c < haT) : ∃ k : ℕ, c < haZt k := by
  rw [haT_nfp] at hc
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hc
  exact ⟨n + 1, hn.trans_le (haZt_iter n)⟩

/-- **Every start `haLU λ_k` has base gate below every `ε`-number base.** -/
theorem haZt_gate : ∀ (k : ℕ) (x : Ordinal.{0}), InE x → x < Om1 → (haLU (haZt k)).γ < x
  | 0, x, hx, _ => by
    show (haLU 0).γ < x
    rw [haLU_zero]; exact hx.pos
  | k + 1, x, hx, hx1 => by
    set l := haZt k with hl
    have hlT : l < haT := haZt_lt_T k
    have hl'T : haZt (k + 1) < haT := haZt_lt_T (k + 1)
    have hst := haLU_start hlT
    have e : haLU (l + 1) = haSU (Bp := haLPB l hlT) hst := haLU_succ_eq hlT (haLU_self hlT) hst
    have hl1 : l + 1 ≤ haZt (k + 1) := Order.add_one_le_of_lt (haZt_lt_succ k)
    have hl1T : l + 1 < haT := hl1.trans_lt hl'T
    have hB : haZt (k + 1) = (haLU l).B := (haZt_B k).symm
    have hcB : haZt (k + 1) < (haLU (l + 1)).B := by
      rw [haLU_B hl1T, hB, haLU_B hlT]; exact ha_Q_lt_Q (lt_add_one l)
    have h1 : (1 : Ordinal.{0}) < evZ (haLPB l hlT).Q := one_lt_omega0.trans (omega0_lt_inE (evZ_E _))
    have hc1 : haZt (k + 1) < (haSD (haLPB l hlT) (haLU l) 1).B := by
      rw [haS_one_eq, GzVD.step_B, hB]; exact lt_eN _
    rw [haLU_γ_iff hl'T hx hx1, (ha_ext hl1 hl'T).2 _ hcB, e, haSU_g hst h1 hc1, haS_one_eq, hB,
      GzVD.step_g_B]
    exact haZt_gate k x hx hx1

theorem haZt_K (S : InaccSeq.{0}) (k : ℕ) : (haLU (haZt k)).γ < Td.tdK S := by
  have hK1 : Td.tdK S < Om1 := by rw [Br.Om1_eq]; exact Td.tdK_lt_Om1
  exact haZt_gate k _ (Low.opow_eq_self_of_SC Td.tdK_SC) hK1

/-! ## Location -/

/-- **`λ_{k+1}` IS LOCATED**: `Λ⁺ = ι(Γ(λ_{k+1})·ω)`, `P(Γ(λ_{k+1})·ω) < L(0)`. -/
theorem haZt_loc (S : InaccSeq.{0}) (k : ℕ) :
    ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG (haZt (k + 1)) * ω) ∧
      upsilon (xtB1 X) = Pv S (gcG (haZt (k + 1)) * ω) ∧ Pv S (gcG (haZt (k + 1)) * ω) < Nc.ncL S 0 := by
  rw [← haZt_B k]; exact gzV_locD (haLU (haZt k)) S (haZt_K S k)

/-- **`ζ_{G+1+λ}` IS LOCATED** for every `λ < φ(3, G+1)` whose gate (in the start) lies below `K`. -/
theorem haLU_loc (S : InaccSeq.{0}) {l : Ordinal.{0}} (hl : l < haT) (hK : (haLU l).g l < Td.tdK S) :
    ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG (veblen 2 (gcG 0 + 1 + l)) * ω) ∧
      upsilon (xtB1 X) = Pv S (gcG (veblen 2 (gcG 0 + 1 + l)) * ω) ∧
      Pv S (gcG (veblen 2 (gcG 0 + 1 + l)) * ω) < Nc.ncL S 0 := by
  have hK1 : Td.tdK S < Om1 := by rw [Br.Om1_eq]; exact Td.tdK_lt_Om1
  rw [← haLU_B hl]
  exact gzV_locD (haLU l) S ((haLU_γ_iff hl (Low.opow_eq_self_of_SC Td.tdK_SC) hK1).2 hK)

/-- **A `ζ`-index `λ < K` has gate below `K`** (it is a code over `K`). -/
theorem ha_gate_lt_K (S : InaccSeq.{0}) {l : Ordinal.{0}} (hl : l < haT) (hlK : l < Td.tdK S) :
    (haLU l).g l < Td.tdK S := by
  have hK : SC (Td.tdK S) := Td.tdK_SC
  have hK1 : Td.tdK S ≤ Om1 := by rw [Br.Om1_eq]; exact Td.tdK_lt_Om1.le
  exact (haLU l).code_gate _ hK1 hK.1 (fun _ _ hu hv => hK.isPrincipal hu hv) (fun _ _ hu hv => hK.2 _ hu _ hv)
    {gcG 0} (fun s hs => Or.inl (Set.mem_singleton_iff.1 hs)) l (GxCl.small hlK) (haLU_self hl)

theorem ha_K_lt_T (S : InaccSeq.{0}) : Td.tdK S < haT :=
  (Td.tdK_lt_Om1.trans (gcG_Om1_lt 0)).trans ((lt_add_one (gcG 0)).trans ha_G1_lt_T)

/-- **`ζ_{G+1+λ}` IS LOCATED for every constant `λ < K`** (`ε₀`, `Γ₀`, `ζ_{Γ₀+1}`, …: the walls of the earlier
rounds). -/
theorem haLU_loc_K (S : InaccSeq.{0}) {l : Ordinal.{0}} (hlK : l < Td.tdK S) :
    ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG (veblen 2 (gcG 0 + 1 + l)) * ω) ∧
      upsilon (xtB1 X) = Pv S (gcG (veblen 2 (gcG 0 + 1 + l)) * ω) ∧
      Pv S (gcG (veblen 2 (gcG 0 + 1 + l)) * ω) < Nc.ncL S 0 :=
  haLU_loc S (hlK.trans (ha_K_lt_T S)) (ha_gate_lt_K S (hlK.trans (ha_K_lt_T S)) hlK)

/-- **`ε_{ζ_{G+1+λ}+d}` IS LOCATED** whenever its system has base gate below `K`. -/
theorem haLD_loc (S : InaccSeq.{0}) {l d : Ordinal.{0}} (hl : l < haT) (hd : d < evZ (haLPB l hl).Q)
    (hγ : (haLD l hl d).γ < Td.tdK S) :
    ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG (veblen 1 ((haLPB l hl).Q + d)) * ω) ∧
      upsilon (xtB1 X) = Pv S (gcG (veblen 1 ((haLPB l hl).Q + d)) * ω) ∧
      Pv S (gcG (veblen 1 ((haLPB l hl).Q + d)) * ω) < Nc.ncL S 0 := by
  rw [← haLD_B hl hd]; exact gzV_locD (haLD l hl d) S hγ

/-! ## The frontier `ι(Γ(φ(3, G+1)))` -/

theorem haT_lim : IsSuccLimit haT := ev_isSuccLimit_of_inE haT_E

/-- **Every `c < φ(3, G+1)` lies below a located bound `λ_{k+1}`** (gate below every base). -/
theorem haT_codes {c : Ordinal.{0}} (hc : c < haT) : ∃ k : ℕ, c < (haLU (haZt k)).B := by
  obtain ⟨k, hk⟩ := haT_cof hc
  exact ⟨k, hk.trans (by rw [haZt_B k]; exact haZt_lt_succ k)⟩

theorem haT_iota_cof (S : InaccSeq.{0}) {l : Ordinal.{0}} (hl : l < iota S (gcG haT)) :
    ∃ k : ℕ, l < iota S (gcG (haLU (haZt k)).B * ω) := by
  have hlim : IsSuccLimit (gcG haT) := ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC (gcG_SC _))
  rw [iota_limit hlim] at hl
  haveI : Nonempty (Iio (gcG haT)) := ⟨⟨0, hlim.bot_lt⟩⟩
  obtain ⟨e, he⟩ := (lt_ciSup_iff (iota_bdd _)).1 hl
  obtain ⟨β, hβ, heβ⟩ := gcG_lt_of_lt_limit haT_lim e.2
  obtain ⟨k, hk⟩ := haT_codes hβ
  refine ⟨k, he.trans_le (iota_mono _ _ ((heβ.trans (gcG_lt hk)).trans_le ?_).le)⟩
  exact le_mul_of_one_le_right' one_lt_omega0.le

/-- **ENUM-REACH at every range restart below `ι(Γ(φ(3, G+1)))`, fixed points included** (UNCONDITIONAL). -/
theorem haT_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG haT)) :
    CdUpper S l ∧ CdLower S l := by
  obtain ⟨k, h⟩ := haT_iota_cof S hl
  exact gzV_locD_enum (haLU (haZt k)) S (haZt_K S k) hr h

/-- **CapV at every range restart below `ι(Γ(φ(3, G+1)))`** (UNCONDITIONAL). -/
theorem haT_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG haT)) :
    CdCapV S l := by
  obtain ⟨k, h⟩ := haT_iota_cof S hl
  exact gzV_locD_capV (haLU (haZt k)) S (haZt_K S k) hr h

/-- **BLK^O and the exact reaches below `P(Γ(λ_{k+1})·ω)` for every `k`** (UNCONDITIONAL). -/
theorem haT_blk (S : InaccSeq.{0}) (k : ℕ) :
    let D := haLU (haZt k)
    let X := gsX D.step.toRS _ D.E_lt_B.le D.B_lt_NB S (gzV_locD_g D S (haZt_K S k))
    xtB1 X = iota S (gcG (haZt (k + 1)) * ω) ∧
    (∀ c' d, c' < d → d < upsilon (xtB1 X) → (le2 c' d ↔ ∃ μ, ∃ j : ℕ, (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 X ∧
        c' = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧ d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 X →
      (∀ c' < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c' g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec X l)) ∧
    (∀ α < upsilon (xtB1 X), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) := by
  intro D X
  refine ⟨?_, gzV_locD_blk D S (haZt_K S k)⟩
  have h := (gsLoc D.step.toRS _ D.E_lt_B.le D.B_lt_NB S (gzV_locD_g D S (haZt_K S k))).1
  rw [← haZt_B k]; exact h

/-- **THE ROAD**: UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ(φ(3, G+1)))` (CapV also `υ_λ < L(ω)`), (CL), EQ, TCrest,
(EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem haT_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG haT) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG haT) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG haT) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  gv_road_of S _ (fun _ hr h => haT_enum S hr h) (fun _ hr h => haT_capV S hr h) hU hL hV hC hEQ hrest hB2

theorem haT_lt_G1 : haT < gcG 1 := by
  have hG1 := gcG_SC 1
  have hE : InE (gcG 1) := Low.opow_eq_self_of_SC hG1
  have h3 : (3 : Ordinal.{0}) < gcG 1 := by
    have : ((3 : ℕ) : Ordinal.{0}) < gcG 1 := (natCast_lt_omega0 3).trans (omega0_lt_inE hE)
    exact_mod_cast this
  exact hG1.2 3 h3 _ (hG1.add_one_lt (gcG_lt zero_lt_one))

/-- **`Γ(φ(3, G+1)) < Ω₂`.** -/
theorem haT_le_Om2 : gcG haT < Om (1 + 1) := by
  have hBE : InE Tf.tfBG := Low.opow_eq_self_of_SC Tf.tfBG_SC
  have hO : (Om1 : Ordinal.{0}) < Tf.tfBG := Tf.tfBG_gt
  have h1 : (1 : Ordinal.{0}) < Tf.tfBG := one_lt_omega0.trans (omega0_lt_inE hBE)
  have hG1 : gcG 1 < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) h1)
  have h2 : gcG haT < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) (haT_lt_G1.trans hG1))
  exact h2.trans Tf.tfBG_lt_Om2

/-- **`P(Γ(φ(3, G+1))) < L(0)`.** -/
theorem haT_P (S : InaccSeq.{0}) : Pv S (gcG haT) < Nc.ncL S 0 := ga_Pv_lt_L0 S haT_le_Om2.le

theorem ha_Ze_lt_T : gzZe < haT := by
  have he : (ε₀ : Ordinal.{0}) < haT :=
    (go_eps0_le gr_G_inE).trans_lt ((lt_add_one (gcG 0)).trans ha_G1_lt_T)
  have h1 : gcG 0 + ε₀ < haT := (inE_indec haT_E).add_lt ((lt_add_one (gcG 0)).trans ha_G1_lt_T) he
  have h := (isNormal_veblen 2).strictMono h1
  rwa [haT_fix] at h

/-- **The order of the frontiers**: `ζ_{G+ε₀} < φ(3, G+1)`, `ι(Γ(ζ_{G+ε₀})) ≤ ι(Γ(λ_{k+1})·ω) ≤ ι(Γ(φ(3, G+1)))
≤ ι(Ω₂)` for every `k` with `ζ_{G+ε₀} ≤ λ_{k+1}`, `P(Γ(φ(3, G+1))) ≤ P(Ω₂) < L(0)`. -/
theorem haT_fr_order (S : InaccSeq.{0}) (k : ℕ) :
    gzZe < haT ∧ iota S (gcG gzZe) ≤ iota S (gcG haT) ∧
      iota S (gcG (haZt (k + 1)) * ω) ≤ iota S (gcG haT) ∧
      iota S (gcG haT) ≤ iota S (Om (1 + 1)) ∧ Pv S (gcG haT) ≤ Pv S (Om (1 + 1)) ∧
      Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have hV : InE (gcG haT) := Low.opow_eq_self_of_SC (gcG_SC _)
  exact ⟨ha_Ze_lt_T, iota_mono _ _ (gcG_lt ha_Ze_lt_T).le, iota_mono _ _ (InE.mul_lt hV
    (gcG_lt (haZt_lt_T (k + 1))) (omega0_lt_inE hV)).le, iota_mono _ _ haT_le_Om2.le, Nm.Pv_mono haT_le_Om2.le,
    ga_Pv_lt_L0 S le_rfl⟩

end Googology.Trans.PoR.InaccPsi.R2.Ha

import Googology.Trans.PoR.InaccPsi.R2.GzZU

/-!
# THE RECURSION OVER `n`: EVERY `ζ_{G+n}`, THE FRONTIER `ι(Γ(ζ_{G+ω}))`, AND THE WALL `ζ_{G+ω}`

The stage `n` (`R2.GzRec`, from a start `U0` with `GzStart n U0`) and its self-read union at `ζ_{G+n+2}`
(`R2.GzZU`, which satisfies `GzStart (n+1)`) are iterated over `n`, starting from `Gw.gwZU` (the union at `ζ_{G+1}`,
`GzStart 0`): `gzU n` is the union at `ζ_{G+n+1}`, `gzD n d = gzYD n (gzU n) d` the system with bound
`ε_{ζ_{G+n+1}+d}` (`d < ζ_{G+n+2}`).  Every `ζ_{G+n+1}` and every `ε_{ζ_{G+n+1}+t_k}` (the tower of the stage) is
located, and **the new frontier is `ι(Γ(ζ_{G+ω}))`**, `ζ_{G+ω} = φ(2, G + ω)` (was `ι(Γ(ζ_{G+2}))`): ENUM-REACH and
CapV at every range restart below it, BLK^O and exact reaches below each located bound, all unconditionally.

The wall: no `GwZD` contains the code `ζ_{G+ω}` with gate below a base `x` while reading the codes `ζ_{G+k+1}` as the
recursion does (`Z_{k+1}(x)`, gate `0`): its readings lie below `Z_{N+1}(x)` for its own finite `N` (`gz_wall`).

* `gwZU_start`, `gzUs`, `gzU`, `gzU_start`, `gzU_zero`, `gzU_succ`, `gzD`, `gzD_B`, `gzD_γ_iff`, `gzU_B`,
  `gzD_loc` (**`ε_{ζ_{G+n+1}+d}` IS LOCATED** when its base gate is below `K`), `gzU_loc` (**`ζ_{G+n+1}` IS
  LOCATED**), `gzD_readZ`, `gzD_gZ` (the recursion reads the code `ζ_{G+n+1}` as `Z_{n+1}(x)`, gate `0`);
* `gzZw`, `gzZ_lt_Zw`, `gzZw_cof`, `gzZw_codes`, `gzZw_iota_cof`, `gzZw_enum`, `gzZw_capV`, `gzZw_blk`, `gzZw_road`
  (**THE ROAD**), `gzZw_le_Om2`, `gzZw_P`, `gzZw_fr_order`, `gz_wall` (**THE WALL `ζ_{G+ω}`**).

No new axiom.  New definitions: `gzUs`, `gzU`, `gzD`, `gzZw`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gz

open Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
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

/-! ## The recursion over `n` -/

/-- **The union at `ζ_{G+1}` starts the stage `0`.** -/
theorem gwZU_start : GzStart 0 gwZU where
  N := rfl
  ix := rfl
  γ := rfl
  b := fun _ => rfl

/-- **The starts**: `gzUs 0 = gwZU`, `gzUs (n+1)` the self-read union of the stage `n`. -/
noncomputable def gzUs : (n : ℕ) → {U : GwZD // GzStart n U}
  | 0 => ⟨gwZU, gwZU_start⟩
  | n + 1 => ⟨gzZU (gzUs n).2, gzZU_start (gzUs n).2⟩

/-- **The union at `ζ_{G+n+1}`.** -/
noncomputable def gzU (n : ℕ) : GwZD := (gzUs n).1

theorem gzU_start (n : ℕ) : GzStart n (gzU n) := (gzUs n).2

theorem gzU_zero : gzU 0 = gwZU := rfl

theorem gzU_succ (n : ℕ) : gzU (n + 1) = gzZU (gzU_start n) := rfl

/-- **The system with bound `ε_{ζ_{G+n+1}+ν}`.** -/
noncomputable def gzD (n : ℕ) (ν : Ordinal.{0}) : GwZD := gzYD n (gzU n) ν

theorem gzD_zero (n : ℕ) : gzD n 0 = gzU n := gzYD_zero n (gzU n)

theorem gzU_B (n : ℕ) : (gzU n).B = gzZ (n + 1) := by
  rw [(gzU n).B_ix, (gzU_start n).ix]; exact epsilon_evZ _

theorem gzU_γ (n : ℕ) : (gzU n).γ = 0 := (gzU_start n).γ

section Main

variable (n : ℕ) {ν : Ordinal.{0}} (hν : ν < gzZ (n + 2))
include hν

/-- **The bound of `gzD n ν` is `ε_{ζ_{G+n+1}+ν}`.** -/
theorem gzD_B : (gzD n ν).B = veblen 1 (gzZ (n + 1) + ν) := gz_B (gzU_start n) hν

theorem gzD_γ_iff {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : (gzD n ν).γ < x ↔ (gzD n ν).g ν < x :=
  gz_γ_iff (gzU_start n) hν hx hx1

theorem gzD_N : (gzD n ν).N = n + 1 := gz_N (gzU_start n) hν

end Main

/-! ## Location -/

/-- **`ε_{ζ_{G+n+1}+ν}` IS LOCATED** for every `ν < ζ_{G+n+2}` whose system has base gate below `K`. -/
theorem gzD_loc (S : InaccSeq.{0}) (n : ℕ) {ν : Ordinal.{0}} (hν : ν < gzZ (n + 2)) (hγ : (gzD n ν).γ < Td.tdK S) :
    ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG (veblen 1 (gzZ (n + 1) + ν)) * ω) ∧
      upsilon (xtB1 X) = Pv S (gcG (veblen 1 (gzZ (n + 1) + ν)) * ω) ∧
      Pv S (gcG (veblen 1 (gzZ (n + 1) + ν)) * ω) < Nc.ncL S 0 := by
  rw [← gzD_B n hν]; exact gwZ_locD (gzD n ν) S hγ

/-- **`ζ_{G+n+1}` IS LOCATED**: `Λ⁺ = ι(Γ(ζ_{G+n+1})·ω)`, `P(Γ(ζ_{G+n+1})·ω) < L(0)`. -/
theorem gzU_loc (S : InaccSeq.{0}) (n : ℕ) : ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG (gzZ (n + 1)) * ω) ∧
    upsilon (xtB1 X) = Pv S (gcG (gzZ (n + 1)) * ω) ∧ Pv S (gcG (gzZ (n + 1)) * ω) < Nc.ncL S 0 := by
  rw [← gzU_B n]; exact gwZ_locD (gzU n) S (by rw [gzU_γ]; exact gv_K_pos S)

/-- **The recursion reads the code `ζ_{G+n+1}` as `Z_{n+1}(x)`** (in `gzD n 1`, the step of the union). -/
theorem gzD_readZ (n : ℕ) (x : Ordinal.{0}) : (gzD n 1).R (gzZ (n + 1)) x = gwZn x (n + 1) := by
  unfold gzD
  rw [gz_one_eq]
  have h1 : (1 : Ordinal.{0}) < (gzU n).NB := (gzU n).one_lt_B.trans (gzU n).B_lt_NB
  have hpow := (gzU n).hR_pow one_ne_zero h1 x
  rw [opow_one, (gzU n).hR_one, opow_one] at hpow
  rw [GwZD.step_R, ← gzU_B n, hpow, (gzU_start n).b]

/-- **The recursion gives the code `ζ_{G+n+1}` the gate `0`.** -/
theorem gzD_gZ (n : ℕ) : (gzD n 1).g (gzZ (n + 1)) = 0 := by
  unfold gzD
  rw [gz_one_eq, ← gzU_B n, GwZD.step_g_B, (gzU_start n).γ]

/-! ## The frontier `ι(Γ(ζ_{G+ω}))` -/

/-- **`ζ_{G+ω} = φ(2, G + ω)`**, the least `ε`-fixed point above every `ζ_{G+n}`. -/
noncomputable def gzZw : Ordinal.{0} := veblen 2 (gcG 0 + ω)

theorem gzZw_E : InE gzZw := gg_veblen_eps two_ne_zero

theorem gzZw_lim : IsSuccLimit gzZw := ev_isSuccLimit_of_inE gzZw_E

theorem gzZ_lt_Zw (n : ℕ) : gzZ n < gzZw := by
  rw [gzZ_eq]
  exact (isNormal_veblen 2).strictMono ((add_lt_add_iff_left _).2 (natCast_lt_omega0 n))

/-- **Every `c < ζ_{G+ω}` lies below some `ζ_{G+n+2}`.** -/
theorem gzZw_cof {c : Ordinal.{0}} (hc : c < gzZw) : ∃ n : ℕ, c < gzZ (n + 2) := by
  obtain ⟨t, ht, hct⟩ := ((isNormal_veblen 2).lt_iff_exists_lt (isSuccLimit_add _ isSuccLimit_omega0)).1 hc
  obtain ⟨d, hd, htd⟩ := (lt_add_iff omega0_ne_zero).1 ht
  obtain ⟨k, rfl⟩ := lt_omega0.1 hd
  refine ⟨k, hct.trans_le ?_⟩
  rw [gzZ_eq]
  refine (isNormal_veblen 2).monotone (htd.trans ((add_le_add_iff_left _).2 ?_))
  exact_mod_cast Nat.le_add_right k 2

/-- **Every `c < ζ_{G+ω}` lies below a located bound `ε_{ζ_{G+n+1}+t_k}`** (gate below every base). -/
theorem gzZw_codes {c : Ordinal.{0}} (hc : c < gzZw) : ∃ n k : ℕ, c < (gzD n (gzT n k)).B := by
  obtain ⟨n, hn⟩ := gzZw_cof hc
  obtain ⟨k, hk⟩ := gzT_sup n hn
  exact ⟨n, k, hk.trans (gz_self (gzU_start n) (gzT_lt n k))⟩

theorem gzZw_iota_cof (S : InaccSeq.{0}) {l : Ordinal.{0}} (hl : l < iota S (gcG gzZw)) :
    ∃ n k : ℕ, l < iota S (gcG (gzD n (gzT n k)).B * ω) := by
  have hlim : IsSuccLimit (gcG gzZw) := ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC (gcG_SC _))
  rw [iota_limit hlim] at hl
  haveI : Nonempty (Iio (gcG gzZw)) := ⟨⟨0, hlim.bot_lt⟩⟩
  obtain ⟨e, he⟩ := (lt_ciSup_iff (iota_bdd _)).1 hl
  obtain ⟨β, hβ, heβ⟩ := gcG_lt_of_lt_limit gzZw_lim e.2
  obtain ⟨n, k, hk⟩ := gzZw_codes hβ
  refine ⟨n, k, he.trans_le (iota_mono _ _ ((heβ.trans (gcG_lt hk)).trans_le ?_).le)⟩
  exact le_mul_of_one_le_right' one_lt_omega0.le

/-- **ENUM-REACH at every range restart below `ι(Γ(ζ_{G+ω}))`, fixed points included** (UNCONDITIONAL). -/
theorem gzZw_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG gzZw)) :
    CdUpper S l ∧ CdLower S l := by
  obtain ⟨n, k, h⟩ := gzZw_iota_cof S hl
  exact gwZ_locD_enum (gzD n (gzT n k)) S (gzT_K (gzU_start n) S k) hr h

/-- **CapV at every range restart below `ι(Γ(ζ_{G+ω}))`** (UNCONDITIONAL). -/
theorem gzZw_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG gzZw)) :
    CdCapV S l := by
  obtain ⟨n, k, h⟩ := gzZw_iota_cof S hl
  exact gwZ_locD_capV (gzD n (gzT n k)) S (gzT_K (gzU_start n) S k) hr h

/-- **BLK^O and the exact reaches below `P(Γ(ε_{ζ_{G+n+1}+t_k})·ω)` for every `n`, `k`** (UNCONDITIONAL). -/
theorem gzZw_blk (S : InaccSeq.{0}) (n k : ℕ) :
    let D := gzD n (gzT n k)
    let X := gsX D.step.toRS _ D.E_lt_B.le D.B_lt_NB S (gwZ_locD_g D S (gzT_K (gzU_start n) S k))
    xtB1 X = iota S (gcG (gzT n (k + 1)) * ω) ∧
    (∀ c' d, c' < d → d < upsilon (xtB1 X) → (le2 c' d ↔ ∃ μ, ∃ j : ℕ, (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 X ∧
        c' = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧ d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 X →
      (∀ c' < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c' g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec X l)) ∧
    (∀ α < upsilon (xtB1 X), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) := by
  intro D X
  refine ⟨?_, gwZ_locD_blk D S (gzT_K (gzU_start n) S k)⟩
  have h := (gsLoc D.step.toRS _ D.E_lt_B.le D.B_lt_NB S (gwZ_locD_g D S (gzT_K (gzU_start n) S k))).1
  rw [← gzT_B (gzU_start n) k]; exact h

/-- **THE ROAD**: UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ(ζ_{G+ω}))` (CapV also `υ_λ < L(ω)`), (CL), EQ, TCrest,
(EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem gzZw_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG gzZw) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG gzZw) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG gzZw) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  gv_road_of S _ (fun _ hr h => gzZw_enum S hr h) (fun _ hr h => gzZw_capV S hr h) hU hL hV hC hEQ hrest hB2

theorem gzZw_lt_G1 : gzZw < gcG 1 := by
  have hE : InE (gcG 1) := Low.opow_eq_self_of_SC (gcG_SC 1)
  have h1 : gcG 0 + ω < gcG 1 := (inE_indec hE).add_lt (gcG_lt zero_lt_one) (omega0_lt_inE hE)
  exact (gcG_SC 1).2 2 (gw_two_lt_G.trans (gcG_lt zero_lt_one)) _ h1

/-- **`Γ(ζ_{G+ω}) < Ω₂`.** -/
theorem gzZw_le_Om2 : gcG gzZw < Om (1 + 1) := by
  have hBE : InE Tf.tfBG := Low.opow_eq_self_of_SC Tf.tfBG_SC
  have hO : (Om1 : Ordinal.{0}) < Tf.tfBG := Tf.tfBG_gt
  have h1 : (1 : Ordinal.{0}) < Tf.tfBG := one_lt_omega0.trans (omega0_lt_inE hBE)
  have hG1 : gcG 1 < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) h1)
  have h2 : gcG gzZw < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) (gzZw_lt_G1.trans hG1))
  exact h2.trans Tf.tfBG_lt_Om2

/-- **`P(Γ(ζ_{G+ω})) < L(0)`.** -/
theorem gzZw_P (S : InaccSeq.{0}) : Pv S (gcG gzZw) < Nc.ncL S 0 := ga_Pv_lt_L0 S gzZw_le_Om2.le

/-- **The order of the frontiers**: `ζ_{G+2} < ζ_{G+ω}`, `ι(Γ(ζ_{G+2})) ≤ ι(Γ(ζ_{G+n+1})·ω) ≤ ι(Γ(ζ_{G+ω})) ≤ ι(Ω₂)`,
`P(Γ(ζ_{G+ω})) ≤ P(Ω₂) < L(0)`. -/
theorem gzZw_fr_order (S : InaccSeq.{0}) (n : ℕ) :
    gwZ2 < gzZw ∧ iota S (gcG gwZ2) ≤ iota S (gcG gzZw) ∧ iota S (gcG (gzZ (n + 1)) * ω) ≤ iota S (gcG gzZw) ∧
      iota S (gcG gzZw) ≤ iota S (Om (1 + 1)) ∧ Pv S (gcG gzZw) ≤ Pv S (Om (1 + 1)) ∧
      Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have hV : InE (gcG gzZw) := Low.opow_eq_self_of_SC (gcG_SC _)
  have h2 : gwZ2 < gzZw := gzZ_lt_Zw 2
  exact ⟨h2, iota_mono _ _ (gcG_lt h2).le, iota_mono _ _ (InE.mul_lt hV (gcG_lt (gzZ_lt_Zw (n + 1)))
    (omega0_lt_inE hV)).le, iota_mono _ _ gzZw_le_Om2.le, Nm.Pv_mono gzZw_le_Om2.le, ga_Pv_lt_L0 S le_rfl⟩

/-! ## The wall `ζ_{G+ω}` -/

/-- **THE WALL `ζ_{G+ω}`**: a `GwZD` that reads every code `ζ_{G+k+1}` as `Z_{k+1}(x)` with gate below `x` (as the
recursion does: `gzD_readZ`, `gzD_gZ`) cannot contain the code `ζ_{G+ω}` with gate below `x`: monotonicity puts its
reading above `Z_{N+1}(x)`, against the field `R_lt_Z`. -/
theorem gz_wall (D : GwZD) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
    (hR : ∀ k : ℕ, D.R (gzZ (k + 1)) x = gwZn x (k + 1)) (hg : ∀ k : ℕ, D.g (gzZ (k + 1)) < x)
    (hZ : gzZw < D.B) (hgZ : D.g gzZw < x) : False := by
  have hlt := D.R_lt_Z x hx hx1 _ hZ hgZ
  have hmono := D.mono x hx hx1 gzZw hZ (gzZ (D.N + 1)) (gzZ_lt_Zw _) hgZ (hg D.N)
  rw [hR] at hmono
  exact absurd hlt (not_lt.2 hmono.le)

end Googology.Trans.PoR.InaccPsi.R2.Gz

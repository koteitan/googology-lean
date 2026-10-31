import Googology.Trans.PoR.InaccPsi.R2.WsStep

/-!
# WsLim: THE `ω`-LIMIT STEP AND THE `Ω₁`-COFINAL STEP FOR EVERY CODE INTERFACE

`R2.WoLimW` and `R2.WoLimO` for an arbitrary code interface `C`.  The only change of proof: where `Wo` used the
surjectivity of `rdc` onto the readings below `rdc ℓ x`, here COFINALITY (`WsC.R_cof`: `ν ≤ R b x` for a smaller
code `b`) suffices, with `R t x + 1 < R ℓ x` for `t + 1 < ℓ` (`WsC.R_succ_lt`).

* `ws_S_gZ` (a code of `hdNx ℓ F` over `Z` forces `max γ (g ℓ) < Z`), the base reading facts `ws_b_*`;
* `wsChW`, `wsLimWE`, `wsStep_fs` (**THE STEP AT EVERY LEVEL WITH AN `ω`-SEQUENCE `C.Fs`**);
* `wsFamO`, `wsLimOE`, `wsStep_om1` (**THE STEP AT EVERY LEVEL WITH AN `Ω₁`-SEQUENCE `C.Fs1`**, generic in the level
  and in the code interface).

No new axiom.  New definitions: `wsChW`, `wsLimWE`, `wsOD`, `wsFamO`, `wsLimOE`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ws

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
open Googology.Trans.PoR.InaccPsi.R2.Wo WsC

variable {C : WsC}

/-! ## The base reading of a good datum -/

section Base

variable {r : WoR} {ℓ : Ordinal.{0}} (hr : WsGood C r ℓ)
include hr

theorem ws_l0 : ℓ ≠ 0 := (wh_Om1_pos.trans_le hr.lev.1).ne'

theorem ws_one_lt_l : (1 : Ordinal.{0}) < ℓ := wh_one_lt_Om1.trans_le hr.lev.1

/-- **A code of the bound `hdNx ℓ F` over `Z` forces `max γ (g ℓ) < Z`.** -/
theorem ws_S_gZ {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) (h : GxCl Z {gcG 0} (hdNx ℓ r.F)) :
    max r.γ (C.g ℓ) < Z := by
  refine max_lt (hr.S_cl Z hZ hZ1 h) ?_
  obtain ⟨i, hi⟩ := hr.F_P
  rw [← hi, hdNx_veb] at h
  have hG : gcG 0 < veblen ℓ (i + 1) :=
    hr.G_le.trans_lt (by rw [← hi]; exact (isNormal_veblen _).strictMono (lt_add_one i))
  have hc := hi_cl_lvl (ws_one_lt_l hr).le hZ1 (hd_succ_lt (ws_l0 hr) _) hG h le_rfl
    ((isNormal_veblen _).strictMono (lt_add_one _))
  have h2 : (C.lv ℓ hr.lev).L + 0 < Om 1 * (C.lv ℓ hr.lev).u + Om 1 * Om 1 :=
    (C.lv ℓ hr.lev).L_add_lt (by rw [← Br.Om1_eq]; exact gv_Om1_pos)
  rw [add_zero] at h2
  exact (C.lv ℓ hr.lev).g_cl Z ℓ hZ hZ1 hc le_rfl h2

section X

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : max r.γ (C.g ℓ) < x)
include hx hx1 hg

theorem ws_rd : LuP (C.R ℓ x) (r.Fr x) ∧ C.R ℓ x < r.Fr x ∧ hdNx (C.R ℓ x) (r.Fr x) < r.Zo x :=
  hr.rd ℓ hr.lev le_rfl x hx hx1 hg

theorem ws_x_le_R : x ≤ C.R ℓ x := C.le_R hx hx1 hr.lev.1 hr.lev.2.2 (max_lt_iff.1 hg).2

theorem ws_b_lt1 : hdNx (C.R ℓ x) (r.Fr x) < gq 1 x :=
  (ws_rd hr hx hx1 hg).2.2.trans (hr.Zo_G1 x hx hx1)

theorem ws_b_gt : x < hdNx (C.R ℓ x) (r.Fr x) :=
  ((ws_x_le_R hr hx hx1 hg).trans_lt (ws_rd hr hx hx1 hg).2.1).trans (hdNx_gt _ _)

theorem ws_b_fixn {n : Ordinal.{0}} (hn : n < ω) :
    veblen n (hdNx (C.R ℓ x) (r.Fr x)) = hdNx (C.R ℓ x) (r.Fr x) :=
  hdNx_fix ((hn.trans (omega0_lt_inE hx)).trans_le (ws_x_le_R hr hx hx1 hg)) _

theorem ws_b_E : InE (hdNx (C.R ℓ x) (r.Fr x)) :=
  hdNx_E ((hx.pos.trans_le (ws_x_le_R hr hx hx1 hg)).ne') _

end X

end Base

/-! ## The `ω`-limit step -/

section W

variable {ℓ : Ordinal.{0}} {ls : ℕ → Ordinal.{0}} (hlev : ∀ k, Om1 ≤ ls k ∧ Om1 ∣ ls k)
  (hmono : ∀ k, ls k < ls (k + 1)) (hlt : ∀ k, ls k < ℓ) (hcof : ∀ t, t < ℓ → ∃ k, t + 1 < ls k)
  (hgk : ∀ k, C.g (ls k) ≤ C.g ℓ) (f : ∀ μ : Ordinal.{0}, μ < ℓ → WoE) (hcoh : WsCoh C ℓ f)

theorem ws_lsL (hℓ : C.Lev ℓ) (hlev : ∀ k, Om1 ≤ ls k ∧ Om1 ∣ ls k) (hlt : ∀ k, ls k < ℓ) (k : ℕ) :
    C.Lev (ls k) := ⟨(hlev k).1, (hlev k).2, (hlt k).trans hℓ.2.2⟩

variable {r : WoR} {S1 : HgVD} (hr : WsGood C r ℓ) (h1 : WsSh C r Om1 S1)

include hlev hlt hcoh hr h1 in
theorem wsW_mem (k : ℕ) : WsSh C r (ls k) (f (ls k) (hlt k) r S1) ∧
    (∀ c x, c < S1.B → (f (ls k) (hlt k) r S1).R c x = S1.R c x ∧ (f (ls k) (hlt k) r S1).g c = S1.g c) ∧
      WsSm C r (ls k) S1 (f (ls k) (hlt k) r S1) :=
  hcoh.1 _ (hlt k) (ws_lsL hr.lev hlev hlt k) r S1 (hr.mono (ws_lsL hr.lev hlev hlt k) (hlt k).le) h1

include hlev hmono hlt hcoh hr h1 in
theorem wsW_ext (k : ℕ) (c x : Ordinal.{0}) (hc : c < (f (ls k) (hlt k) r S1).B) :
    (f (ls (k + 1)) (hlt (k + 1)) r S1).R c x = (f (ls k) (hlt k) r S1).R c x ∧
      (f (ls (k + 1)) (hlt (k + 1)) r S1).g c = (f (ls k) (hlt k) r S1).g c :=
  hcoh.2 _ _ (hlt k) (hlt (k + 1)) (hmono k) (ws_lsL hr.lev hlev hlt k) (ws_lsL hr.lev hlev hlt (k + 1)) r S1
    (hr.mono (ws_lsL hr.lev hlev hlt (k + 1)) (hlt (k + 1)).le) h1 c x hc

/-- **THE GATED `ω`-CHAIN OF THE ENTRIES AT `ℓ_k` OVER `r`.** -/
noncomputable def wsChW : HgfCh where
  D := fun k => f (ls k) (hlt k) r S1
  B := hdNx ℓ r.F
  b := fun x => hdNx (C.R ℓ x) (r.Fr x)
  γ := max r.γ (C.g ℓ)
  Zo := r.Zo
  γ_lt := max_lt hr.γ_lt (C.g_lt ℓ hr.lev.2.2)
  γ0 := fun k => (wsW_mem hlev hlt f hcoh hr h1 k).1.2.1.2.trans (max_le_max le_rfl (hgk k))
  γ_cl := fun Z hZ hZ1 h => ws_S_gZ hr hZ hZ1 h
  B_mono := fun k => by
    rw [(wsW_mem hlev hlt f hcoh hr h1 k).1.1, (wsW_mem hlev hlt f hcoh hr h1 (k + 1)).1.1]
    exact hdNx_mono (hmono k).le _
  B_lt := fun k => by rw [(wsW_mem hlev hlt f hcoh hr h1 k).1.1]; exact ws_N_lt hr.lev hr.F_P (hlt k)
  B_cof := fun c hc => by
    obtain ⟨b, hb, hcb⟩ := hjw_Nx_cof (ws_l0 hr) hr.F_P hc
    obtain ⟨k, hk⟩ := hcof b hb
    exact ⟨k, by rw [(wsW_mem hlev hlt f hcoh hr h1 k).1.1]; exact hcb.trans (hdN_lt_Nx hk)⟩
  R_ext := fun k c x hc => (wsW_ext hlev hmono hlt f hcoh hr h1 k c x hc).1
  g_ext := fun k c hc => (wsW_ext hlev hmono hlt f hcoh hr h1 k c 0 hc).2
  B_lt1 := hr.S_lt1
  B_fix := hdNx_fix (ws_one_lt_l hr) _
  B_mem := fun S a b ha hb => hr.S_mem ℓ hr.lev le_rfl S ha hb
  b_ge := fun k x hx hx1 hγ => by
    have hgk' : max r.γ (C.g (ls k)) < x := (max_le_max le_rfl (hgk k)).trans_lt hγ
    rw [(wsW_mem hlev hlt f hcoh hr h1 k).1.2.2.2.1 x hx hx1 hgk']
    exact hdNx_mono (R_le_mono hx hx1 hr.lev.2.2 (hlt k).le (max_lt_iff.1 hγ).2 (max_lt_iff.1 hgk').2) _
  b_cof := fun x hx hx1 hγ ν hν => by
    have hr0 : C.R ℓ x ≠ 0 := R_ne0 hx hx1 hr.lev.1 hr.lev.2.2 (max_lt_iff.1 hγ).2
    obtain ⟨b, hb, hνb⟩ := hjw_Nx_cof hr0 (ws_rd hr hx hx1 hγ).1 hν
    obtain ⟨t, ht, hgt, hbt⟩ := C.R_cof hx hx1 hr.lev.2.2 (max_lt_iff.1 hγ).2 b hb
    obtain ⟨k, hk⟩ := hcof t ht
    have hgk' : max r.γ (C.g (ls k)) < x := (max_le_max le_rfl (hgk k)).trans_lt hγ
    have hlt' : C.R t x + 1 < C.R (ls k) x :=
      R_succ_lt hx hx1 ((hlt k).trans hr.lev.2.2) hk (max_lt_iff.1 hgk').2 hgt
    refine ⟨k, ?_⟩
    rw [(wsW_mem hlev hlt f hcoh hr h1 k).1.2.2.2.1 x hx hx1 hgk']
    exact hνb.trans (hdN_lt_Nx ((add_le_add hbt le_rfl).trans_lt hlt'))
  b_fix := fun x hx hx1 hγ => ws_b_fixn hr hx hx1 hγ (by exact_mod_cast natCast_lt_omega0 1)
  b_gt := fun x hx hx1 hγ => ws_b_gt hr hx hx1 hγ
  b_lt := fun x hx hx1 hγ => ws_b_lt1 hr hx hx1 hγ
  b_pi := fun σ ρ hB hγ => hr.S_pi ℓ hr.lev le_rfl σ ρ hB hγ
  Z_low := fun k x hx hx1 hγ => by
    rw [(wsW_mem hlev hlt f hcoh hr h1 k).1.2.2.2.2.1 x hx hx1]
    split_ifs with h'
    · exact (hb_evZ_lt_fix2 (hr.Zo_fix x)
        ((hr.rd _ (ws_lsL hr.lev hlev hlt k) (hlt k).le x hx hx1 h').2.2)).le
    · exact le_rfl
  Zo_fix := fun x => hc_fix_down one_le_two (hr.Zo_fix x)
  Zo_G1 := hr.Zo_G1

end W

/-- **THE ENTRY AT AN `ω`-LIMIT LEVEL**: the union of the chain `wsChW`. -/
noncomputable def wsLimWE {ℓ : Ordinal.{0}} {ls : ℕ → Ordinal.{0}} (hlev : ∀ k, Om1 ≤ ls k ∧ Om1 ∣ ls k)
    (hmono : ∀ k, ls k < ls (k + 1)) (hlt : ∀ k, ls k < ℓ) (hcof : ∀ t, t < ℓ → ∃ k, t + 1 < ls k)
    (hgk : ∀ k, C.g (ls k) ≤ C.g ℓ) (f : ∀ μ : Ordinal.{0}, μ < ℓ → WoE) (hcoh : WsCoh C ℓ f) : WoE := by
  classical
  exact fun r S1 => if h : WsGood C r ℓ ∧ WsSh C r Om1 S1 then
    (wsChW hlev hmono hlt hcof hgk f hcoh h.1 h.2).U else S1

/-- **THE `ω`-LIMIT STEP**: every level with an `ω`-sequence of levels (`C.Fs`). -/
theorem wsStep_fs {ℓ : Ordinal.{0}} (hℓ : C.Lev ℓ) (hfs : C.Fs ℓ) : WsStepAt C ℓ := by
  intro f hcoh
  obtain ⟨ls, hlev, hmono, hlt, hcof, hgk⟩ := hfs
  have hL := ws_lsL hℓ hlev hlt
  have e : ∀ r S1 (hr : WsGood C r ℓ) (h1 : WsSh C r Om1 S1),
      wsLimWE hlev hmono hlt hcof hgk f hcoh r S1 = (wsChW hlev hmono hlt hcof hgk f hcoh hr h1).U := by
    intro r S1 hr h1; unfold wsLimWE; rw [dif_pos ⟨hr, h1⟩]
  refine ⟨wsLimWE hlev hmono hlt hcof hgk f hcoh, fun r S1 hr h1 => ?_, fun μ h hμ r S1 hr h1 c x hc => ?_⟩
  · set Ch := wsChW hlev hmono hlt hcof hgk f hcoh hr h1
    have M := wsW_mem hlev hlt f hcoh hr h1
    rw [e r S1 hr h1]
    refine ⟨⟨rfl, ⟨le_max_left _ _, le_rfl⟩, fun x _ _ => Iff.rfl, fun x _ _ _ => rfl, fun x _ _ => rfl,
      fun c σ hFc hc hσ hσ1 hg => ?_⟩, fun c x hc => ?_, fun c σ hSc hc hσ hσ1 hg => ?_⟩
    · obtain ⟨k, hk⟩ := Ch.B_cof c hc
      rw [Ch.U_g hk] at hg
      exact (M k).1.2.2.2.2.2 c σ hFc hk hσ hσ1 hg
    · have hc0 : c < (Ch.D 0).B := hc.trans_le (ws_S1_le (hL 0) h1 (M 0).1)
      rw [Ch.U_R hc0, Ch.U_g hc0]; exact (M 0).2.1 c x hc
    · obtain ⟨k, hk⟩ := Ch.B_cof c hc
      rw [Ch.U_g hk] at hg
      obtain ⟨μ, hμ, hμk, hgμ, hcμ⟩ := (M k).2.2 c σ hSc hk hσ hσ1 hg
      exact ⟨μ, hμ, hμk.trans (hlt k), hgμ, hcμ⟩
  · set Ch := wsChW hlev hmono hlt hcof hgk f hcoh hr h1
    have M := wsW_mem hlev hlt f hcoh hr h1
    obtain ⟨k, hk⟩ := hcof μ h
    have hμk : μ < ls k := (lt_add_one μ).trans hk
    have hsp := hcoh.1 μ h hμ r S1 (hr.mono hμ h.le) h1
    have hc' : c < (Ch.D k).B := by
      show c < (f (ls k) (hlt k) r S1).B
      rw [(M k).1.1]; rw [hsp.1.1] at hc; exact hc.trans_le (hdNx_mono hμk.le _)
    rw [e r S1 hr h1, Ch.U_R hc', Ch.U_g hc']
    exact hcoh.2 μ (ls k) h (hlt k) hμk hμ (hL k) r S1 (hr.mono (hL k) (hlt k).le) h1 c x hc

/-! ## The `Ω₁`-cofinal step -/

/-- The member `μ` over `r`: the entry at `s μ`. -/
noncomputable def wsOD {ℓ : Ordinal.{0}} (s : Ordinal.{0} → Ordinal.{0}) (f : ∀ μ : Ordinal.{0}, μ < ℓ → WoE)
    (r : WoR) (S1 : HgVD) (μ : Ordinal.{0}) : HgVD := by
  classical
  exact if h : s μ < ℓ then f (s μ) h r S1 else S1

section O

variable {ℓ : Ordinal.{0}} {s : Ordinal.{0} → Ordinal.{0}} (hs : C.Fs1 ℓ s) (f : ∀ μ : Ordinal.{0}, μ < ℓ → WoE)
  (hcoh : WsCoh C ℓ f)

include hs

theorem wsO_D_eq (r : WoR) (S1 : HgVD) {μ : Ordinal.{0}} (hμ : μ < Om1) :
    wsOD s f r S1 μ = f (s μ) (hs.1.1 μ hμ).2 r S1 := by
  unfold wsOD; rw [dif_pos (hs.1.1 μ hμ).2]

theorem wsO_sL (hℓ : C.Lev ℓ) {μ : Ordinal.{0}} (hμ : μ < Om1) : C.Lev (s μ) :=
  ⟨(hs.2 μ hμ).1, (hs.2 μ hμ).2, (hs.1.1 μ hμ).2.trans hℓ.2.2⟩

variable {r : WoR} {S1 : HgVD} (hr : WsGood C r ℓ) (h1 : WsSh C r Om1 S1)

include hcoh hr h1 in
theorem wsO_mem {μ : Ordinal.{0}} (hμ : μ < Om1) : WsSh C r (s μ) (wsOD s f r S1 μ) ∧
    (∀ c x, c < S1.B → (wsOD s f r S1 μ).R c x = S1.R c x ∧ (wsOD s f r S1 μ).g c = S1.g c) ∧
      WsSm C r (s μ) S1 (wsOD s f r S1 μ) := by
  rw [wsO_D_eq hs f r S1 hμ]
  exact hcoh.1 _ (hs.1.1 μ hμ).2 (wsO_sL hs hr.lev hμ) r S1 (hr.mono (wsO_sL hs hr.lev hμ) (hs.1.1 μ hμ).2.le) h1

include hcoh hr h1 in
theorem wsO_B {μ : Ordinal.{0}} (hμ : μ < Om1) : (wsOD s f r S1 μ).B = hdNx (s μ) r.F :=
  (wsO_mem hs f hcoh hr h1 hμ).1.1

include hr in
/-- **Gate-cofinality as a bound**: `b < ℓ` lies below some `s μ` (`μ < σ`) with `b + 1 < s μ`. -/
theorem wsO_cof {b σ : Ordinal.{0}} (hb : b < ℓ) (hσ : InE σ) (hσ1 : σ < Om1) (hg : C.g b < σ) :
    ∃ μ, μ < σ ∧ b + 1 < s μ := by
  obtain ⟨μ, hμ, hbμ⟩ := hs.1.2.2.2 σ hσ hσ1 b hb hg
  exact ⟨μ, hμ, lev_lim (wsO_sL hs hr.lev (hμ.trans hσ1)) hbμ⟩

include hr in
theorem wsO_R_lt {x μ : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : C.g ℓ < x) (hμ : μ < x) :
    C.R (s μ) x + 1 < C.R ℓ x := by
  have hμ1 : μ < Om1 := hμ.trans hx1
  exact R_succ_lt hx hx1 hr.lev.2.2 (lev_lim hr.lev (hs.1.1 μ hμ1).2) hg (hs.1.2.2.1 x hx hx1 hg μ hμ)

/-- **THE `Ω₁`-FAMILY OF THE ENTRIES AT `s μ` OVER `r`.** -/
noncomputable def wsFamO : HoFam where
  D := wsOD s f r S1
  B := hdNx ℓ r.F
  γ := max r.γ (C.g ℓ)
  b := fun x => hdNx (C.R ℓ x) (r.Fr x)
  Zo := r.Zo
  γ_lt := max_lt hr.γ_lt (C.g_lt ℓ hr.lev.2.2)
  γ_cl := fun Z hZ hZ1 h => ws_S_gZ hr hZ hZ1 h
  G_lt := hr.G_le.trans_lt (hdNx_gt _ _)
  B_E := hdNx_E (ws_l0 hr) _
  B_lt1 := hr.S_lt1
  B_fix1 := hdNx_fix (ws_one_lt_l hr) _
  B_mem := fun S a b ha hb => hr.S_mem ℓ hr.lev le_rfl S ha hb
  DB_lt := fun μ hμ => by
    rw [wsO_B hs f hcoh hr h1 hμ]; exact ws_N_lt hr.lev hr.F_P (hs.1.1 μ hμ).2
  B_cof := fun c hc => by
    obtain ⟨b, hb, hcb⟩ := hjw_Nx_cof (ws_l0 hr) hr.F_P hc
    have hgb : C.g b < Om1 := C.g_lt b (hb.trans hr.lev.2.2)
    obtain ⟨μ, hμ, hbμ⟩ := wsO_cof hs hr hb (eN_E (C.g b)) (eN_lt_Om1K hgb) (lt_eN _)
    have hμ1 : μ < Om1 := hμ.trans (eN_lt_Om1K hgb)
    exact ⟨μ, hμ1, by rw [wsO_B hs f hcoh hr h1 hμ1]; exact hcb.trans (hdN_lt_Nx hbμ)⟩
  ext := fun μ' μ hle hμ c x hc => by
    rcases hle.lt_or_eq with hlt | rfl
    · have hμ'1 : μ' < Om1 := hlt.trans hμ
      rw [wsO_D_eq hs f r S1 hμ, wsO_D_eq hs f r S1 hμ'1]
      rw [wsO_D_eq hs f r S1 hμ'1] at hc
      exact hcoh.2 _ _ (hs.1.1 μ' hμ'1).2 (hs.1.1 μ hμ).2 (hs.1.2.1 μ' μ hlt hμ) (wsO_sL hs hr.lev hμ'1)
        (wsO_sL hs hr.lev hμ) r S1 (hr.mono (wsO_sL hs hr.lev hμ) (hs.1.1 μ hμ).2.le) h1 c x hc
    · exact ⟨rfl, rfl⟩
  small := fun μ hμ c hc σ hσ hσ1 hg => by
    obtain ⟨m1, -, m3⟩ := wsO_mem hs f hcoh hr h1 hμ
    by_cases hcS : c < S1.B
    · refine ⟨0, hσ.pos, hcS.trans_le ?_⟩
      exact ws_S1_le (wsO_sL hs hr.lev gv_Om1_pos) h1 (wsO_mem hs f hcoh hr h1 gv_Om1_pos).1
    · obtain ⟨lv, hlv, hlvμ, hglv, hclv⟩ := m3 c σ (not_lt.1 hcS) hc hσ hσ1 hg
      obtain ⟨μ', hμ', hlvμ'⟩ := hs.1.2.2.2 σ hσ hσ1 lv (hlvμ.trans (hs.1.1 μ hμ).2) hglv
      have hμ'1 : μ' < Om1 := hμ'.trans hσ1
      refine ⟨μ', hμ', ?_⟩
      rw [wsO_B hs f hcoh hr h1 hμ'1]
      exact hclv.trans_le (hdNx_mono (wh_lev_succ_le hlv.2.1 (hs.2 μ' hμ'1).2 hlvμ') _)
  γD := fun x hx hx1 hγ μ hμ => by
    have hμ1 : μ < Om1 := hμ.trans hx1
    exact (wsO_mem hs f hcoh hr h1 hμ1).1.2.1.2.trans_lt
      (max_lt (max_lt_iff.1 hγ).1 (hs.1.2.2.1 x hx hx1 (max_lt_iff.1 hγ).2 μ hμ))
  bD := fun x hx hx1 hγ μ hμ => by
    have hμ1 : μ < Om1 := hμ.trans hx1
    have hgs : max r.γ (C.g (s μ)) < x :=
      max_lt (max_lt_iff.1 hγ).1 (hs.1.2.2.1 x hx hx1 (max_lt_iff.1 hγ).2 μ hμ)
    rw [(wsO_mem hs f hcoh hr h1 hμ1).1.2.2.2.1 x hx hx1 hgs]
    exact (hdNx_lt_N (hcN_gt _ _)).trans (hdN_lt_Nx (wsO_R_lt hs hr hx hx1 (max_lt_iff.1 hγ).2 hμ))
  ZD := fun x hx hx1 hγ μ hμ => by
    have hμ1 : μ < Om1 := hμ.trans hx1
    have hgs : max r.γ (C.g (s μ)) < x :=
      max_lt (max_lt_iff.1 hγ).1 (hs.1.2.2.1 x hx hx1 (max_lt_iff.1 hγ).2 μ hμ)
    rw [(wsO_mem hs f hcoh hr h1 hμ1).1.2.2.2.2.1 x hx hx1, if_pos hgs]
    refine (hb_evZ_lt_fix2 (ws_b_fixn hr hx hx1 hγ (by exact_mod_cast natCast_lt_omega0 2)) ?_).le
    exact (hdNx_lt_N (hcN_gt _ _)).trans (hdN_lt_Nx (wsO_R_lt hs hr hx hx1 (max_lt_iff.1 hγ).2 hμ))
  b_cof := fun x hx hx1 hγ ν hν => by
    have hr0 : C.R ℓ x ≠ 0 := R_ne0 hx hx1 hr.lev.1 hr.lev.2.2 (max_lt_iff.1 hγ).2
    obtain ⟨b, hb, hνb⟩ := hjw_Nx_cof hr0 (ws_rd hr hx hx1 hγ).1 hν
    obtain ⟨t, ht, hgt, hbt⟩ := C.R_cof hx hx1 hr.lev.2.2 (max_lt_iff.1 hγ).2 b hb
    obtain ⟨μ, hμ, hk⟩ := wsO_cof hs hr ht hx hx1 hgt
    have hμ1 : μ < Om1 := hμ.trans hx1
    have hgs : max r.γ (C.g (s μ)) < x :=
      max_lt (max_lt_iff.1 hγ).1 (hs.1.2.2.1 x hx hx1 (max_lt_iff.1 hγ).2 μ hμ)
    have hlt' : C.R t x + 1 < C.R (s μ) x :=
      R_succ_lt hx hx1 ((hs.1.1 μ hμ1).2.trans hr.lev.2.2) hk (max_lt_iff.1 hgs).2 hgt
    refine ⟨μ, hμ, ?_⟩
    rw [(wsO_mem hs f hcoh hr h1 hμ1).1.2.2.2.1 x hx hx1 hgs]
    exact hνb.trans (hdN_lt_Nx ((add_le_add hbt le_rfl).trans_lt hlt'))
  b_E := fun x hx hx1 hγ => ws_b_E hr hx hx1 hγ
  x_lt_b := fun x hx hx1 hγ => ws_b_gt hr hx hx1 hγ
  b_fix1 := fun x hx hx1 hγ => ws_b_fixn hr hx hx1 hγ (by exact_mod_cast natCast_lt_omega0 1)
  b_lt1 := fun x hx hx1 hγ => ws_b_lt1 hr hx hx1 hγ
  b_pi := fun σ ρ hB hγ => hr.S_pi ℓ hr.lev le_rfl σ ρ hB hγ
  Z_low := fun μ hμ x hx hx1 hγ => by
    rw [(wsO_mem hs f hcoh hr h1 hμ).1.2.2.2.2.1 x hx hx1]
    split_ifs with h'
    · exact (hb_evZ_lt_fix2 (hr.Zo_fix x)
        ((hr.rd _ (wsO_sL hs hr.lev hμ) (hs.1.1 μ hμ).2.le x hx hx1 h').2.2)).le
    · exact le_rfl
  Zo_fix := hr.Zo_fix
  Zo_G1 := hr.Zo_G1

end O

/-- **THE ENTRY AT A LEVEL OF COFINALITY `Ω₁`**: the union of `wsFamO`. -/
noncomputable def wsLimOE {ℓ : Ordinal.{0}} {s : Ordinal.{0} → Ordinal.{0}} (hs : C.Fs1 ℓ s)
    (f : ∀ μ : Ordinal.{0}, μ < ℓ → WoE) (hcoh : WsCoh C ℓ f) : WoE := by
  classical
  exact fun r S1 => if h : WsGood C r ℓ ∧ WsSh C r Om1 S1 then hoOU (wsFamO hs f hcoh h.1 h.2) else S1

/-- **THE `Ω₁`-COFINAL STEP, GENERIC**: the step at every level with an `Ω₁`-sequence of levels, for every code
interface. -/
theorem wsStep_om1 {ℓ : Ordinal.{0}} {s : Ordinal.{0} → Ordinal.{0}} (hs : C.Fs1 ℓ s) : WsStepAt C ℓ := by
  intro f hcoh
  have e : ∀ r S1 (hr : WsGood C r ℓ) (h1 : WsSh C r Om1 S1),
      wsLimOE hs f hcoh r S1 = hoOU (wsFamO hs f hcoh hr h1) := by
    intro r S1 hr h1; unfold wsLimOE; rw [dif_pos ⟨hr, h1⟩]
  refine ⟨wsLimOE hs f hcoh, fun r S1 hr h1 => ?_, fun μ h hμ r S1 hr h1 c x hc => ?_⟩
  · set F := wsFamO hs f hcoh hr h1
    rw [e r S1 hr h1]
    refine ⟨⟨rfl, ⟨le_max_left _ _, le_rfl⟩, fun x _ _ => Iff.rfl, fun x _ _ _ => rfl, fun x _ _ => rfl,
      fun c σ hFc hc hσ hσ1 hg => ?_⟩, fun c x hc => ?_, fun c σ hSc hc hσ hσ1 hg => ?_⟩
    · obtain ⟨μ, hμ, hk⟩ := F.B_cof c hc
      rw [hoOU_g F hμ hk] at hg
      exact (wsO_mem hs f hcoh hr h1 hμ).1.2.2.2.2.2 c σ hFc hk hσ hσ1 hg
    · have hc0 : c < (F.D 0).B :=
        hc.trans_le (ws_S1_le (wsO_sL hs hr.lev gv_Om1_pos) h1 (wsO_mem hs f hcoh hr h1 gv_Om1_pos).1)
      rw [hoOU_R F gv_Om1_pos hc0, hoOU_g F gv_Om1_pos hc0]
      exact (wsO_mem hs f hcoh hr h1 gv_Om1_pos).2.1 c x hc
    · obtain ⟨μ, hμ, hk⟩ := F.B_cof c hc
      rw [hoOU_g F hμ hk] at hg
      obtain ⟨μ', hμ', hμk, hgμ, hcμ⟩ := (wsO_mem hs f hcoh hr h1 hμ).2.2 c σ hSc hk hσ hσ1 hg
      exact ⟨μ', hμ', hμk.trans (hs.1.1 μ hμ).2, hgμ, hcμ⟩
  · set F := wsFamO hs f hcoh hr h1
    have hgμ : C.g μ < Om1 := C.g_lt μ hμ.2.2
    obtain ⟨ν, hν, hk⟩ := wsO_cof hs hr h (eN_E (C.g μ)) (eN_lt_Om1K hgμ) (lt_eN _)
    have hν1 : ν < Om1 := hν.trans (eN_lt_Om1K hgμ)
    have hμk : μ < s ν := (lt_add_one μ).trans hk
    have hsp := hcoh.1 μ h hμ r S1 (hr.mono hμ h.le) h1
    have hc' : c < (F.D ν).B := by
      show c < (wsOD s f r S1 ν).B
      rw [wsO_B hs f hcoh hr h1 hν1]; rw [hsp.1.1] at hc; exact hc.trans_le (hdNx_mono hμk.le _)
    rw [e r S1 hr h1, hoOU_R F hν1 hc', hoOU_g F hν1 hc']
    show (wsOD s f r S1 ν).R c x = _ ∧ (wsOD s f r S1 ν).g c = _
    rw [wsO_D_eq hs f r S1 hν1]
    exact hcoh.2 μ (s ν) h (hs.1.1 ν hν1).2 hμk hμ (wsO_sL hs hr.lev hν1) r S1
      (hr.mono (wsO_sL hs hr.lev hν1) (hs.1.1 ν hν1).2.le) h1 c x hc

end Googology.Trans.PoR.InaccPsi.R2.Ws

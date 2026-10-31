import Googology.Trans.PoR.InaccPsi.R2.WoStep

/-!
# WoLimW: THE `ω`-LIMIT STEP ON FAMILIES OVER RAW DATA

* the facts of the base reading `hdNx (rdc ℓ x) (F(x))` of a datum good up to `ℓ` (`wo_b_*`) and the gate of the
  bound (`wo_S_gZ`: a code of `hdNx ℓ F` over `Z` forces `max γ (gtc ℓ) < Z`);
* `woChW` (**THE GATED `ω`-CHAIN OF THE ENTRIES AT `ℓ_k`** over a datum `r`), `woLimWE` (its union),
  `woStep_fs` (**THE STEP AT EVERY LEVEL WITH AN `ω`-SEQUENCE**, `Wm.WmFs`).

No new axiom.  New definitions: `woChW`, `woLimWE`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wo

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

/-! ## The base reading of a good datum -/

section Base

variable {r : WoR} {ℓ : Ordinal.{0}} (hr : WoGood r ℓ)
include hr

theorem wo_l0 : ℓ ≠ 0 := (wh_Om1_pos.trans_le hr.lev.1).ne'

theorem wo_one_lt_l : (1 : Ordinal.{0}) < ℓ := wh_one_lt_Om1.trans_le hr.lev.1

/-- **A code of the bound `hdNx ℓ F` over `Z` forces `max γ (gtc ℓ) < Z`.** -/
theorem wo_S_gZ {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) (h : GxCl Z {gcG 0} (hdNx ℓ r.F)) :
    max r.γ (gtc ℓ) < Z := by
  refine max_lt (hr.S_cl Z hZ hZ1 h) ?_
  obtain ⟨i, hi⟩ := hr.F_P
  rw [← hi, hdNx_veb] at h
  have hG : gcG 0 < veblen ℓ (i + 1) :=
    hr.G_le.trans_lt (by rw [← hi]; exact (isNormal_veblen _).strictMono (lt_add_one i))
  have hc := hi_cl_lvl (wo_one_lt_l hr).le hZ1 (hd_succ_lt (wo_l0 hr) _) hG h le_rfl
    ((isNormal_veblen _).strictMono (lt_add_one _))
  have h2 : (woLv ℓ hr.lev).L + 0 < Om 1 * (woLv ℓ hr.lev).u + Om 1 * Om 1 :=
    (woLv ℓ hr.lev).L_add_lt (by rw [← Br.Om1_eq]; exact gv_Om1_pos)
  rw [add_zero] at h2
  exact (woLv ℓ hr.lev).g_cl Z ℓ hZ hZ1 hc le_rfl h2

section X

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : max r.γ (gtc ℓ) < x)
include hx hx1 hg

theorem wo_rd : LuP (rdc ℓ x) (r.Fr x) ∧ rdc ℓ x < r.Fr x ∧ hdNx (rdc ℓ x) (r.Fr x) < r.Zo x :=
  hr.rd ℓ hr.lev le_rfl x hx hx1 hg

theorem wo_x_le_rdc : x ≤ rdc ℓ x := wh_le_rdc hx hr.lev.1 hr.lev.2.2

theorem wo_b_lt1 : hdNx (rdc ℓ x) (r.Fr x) < gq 1 x :=
  (wo_rd hr hx hx1 hg).2.2.trans (hr.Zo_G1 x hx hx1)

theorem wo_b_gt : x < hdNx (rdc ℓ x) (r.Fr x) :=
  ((wo_x_le_rdc hr hx hx1 hg).trans_lt (wo_rd hr hx hx1 hg).2.1).trans (hdNx_gt _ _)

theorem wo_b_fixn {n : Ordinal.{0}} (hn : n < ω) : veblen n (hdNx (rdc ℓ x) (r.Fr x)) = hdNx (rdc ℓ x) (r.Fr x) :=
  hdNx_fix ((hn.trans (omega0_lt_inE hx)).trans_le (wo_x_le_rdc hr hx hx1 hg)) _

theorem wo_b_E : InE (hdNx (rdc ℓ x) (r.Fr x)) :=
  hdNx_E ((hx.pos.trans_le (wo_x_le_rdc hr hx hx1 hg)).ne') _

end X

end Base

/-! ## The `ω`-limit step -/

section W

variable {ℓ : Ordinal.{0}} (hℓ : WmLev ℓ) {ls : ℕ → Ordinal.{0}} (hlev : ∀ k, Om1 ≤ ls k ∧ Om1 ∣ ls k)
  (hmono : ∀ k, ls k < ls (k + 1)) (hlt : ∀ k, ls k < ℓ) (hcof : ∀ t, t < ℓ → ∃ k, t + 1 < ls k)
  (hgk : ∀ k, gtc (ls k) ≤ gtc ℓ) (f : ∀ μ : Ordinal.{0}, μ < ℓ → WoE) (hcoh : WoCoh ℓ f)

theorem wo_lsL (hℓ : WmLev ℓ) (hlev : ∀ k, Om1 ≤ ls k ∧ Om1 ∣ ls k) (hlt : ∀ k, ls k < ℓ) (k : ℕ) :
    WmLev (ls k) := ⟨(hlev k).1, (hlev k).2, (hlt k).trans hℓ.2.2⟩

variable {r : WoR} {S1 : HgVD} (hr : WoGood r ℓ) (h1 : WoSh r Om1 S1)

include hlev hlt hcoh hr h1 in
theorem woW_mem (k : ℕ) : WoSh r (ls k) (f (ls k) (hlt k) r S1) ∧
    (∀ c x, c < S1.B → (f (ls k) (hlt k) r S1).R c x = S1.R c x ∧ (f (ls k) (hlt k) r S1).g c = S1.g c) ∧
      WoSm r (ls k) S1 (f (ls k) (hlt k) r S1) :=
  hcoh.1 _ (hlt k) (wo_lsL hr.lev hlev hlt k) r S1 (hr.mono (wo_lsL hr.lev hlev hlt k) (hlt k).le) h1

include hlev hmono hlt hcoh hr h1 in
theorem woW_ext (k : ℕ) (c x : Ordinal.{0}) (hc : c < (f (ls k) (hlt k) r S1).B) :
    (f (ls (k + 1)) (hlt (k + 1)) r S1).R c x = (f (ls k) (hlt k) r S1).R c x ∧
      (f (ls (k + 1)) (hlt (k + 1)) r S1).g c = (f (ls k) (hlt k) r S1).g c :=
  hcoh.2 _ _ (hlt k) (hlt (k + 1)) (hmono k) (wo_lsL hr.lev hlev hlt k) (wo_lsL hr.lev hlev hlt (k + 1)) r S1
    (hr.mono (wo_lsL hr.lev hlev hlt (k + 1)) (hlt (k + 1)).le) h1 c x hc

/-- **THE GATED `ω`-CHAIN OF THE ENTRIES AT `ℓ_k` OVER `r`.** -/
noncomputable def woChW : HgfCh where
  D := fun k => f (ls k) (hlt k) r S1
  B := hdNx ℓ r.F
  b := fun x => hdNx (rdc ℓ x) (r.Fr x)
  γ := max r.γ (gtc ℓ)
  Zo := r.Zo
  γ_lt := max_lt hr.γ_lt (gtc_lt_Om1 ℓ hr.lev.2.2)
  γ0 := fun k => (woW_mem hlev hlt f hcoh hr h1 k).1.2.1.2.trans (max_le_max le_rfl (hgk k))
  γ_cl := fun Z hZ hZ1 h => wo_S_gZ hr hZ hZ1 h
  B_mono := fun k => by
    rw [(woW_mem hlev hlt f hcoh hr h1 k).1.1, (woW_mem hlev hlt f hcoh hr h1 (k + 1)).1.1]
    exact hdNx_mono (hmono k).le _
  B_lt := fun k => by rw [(woW_mem hlev hlt f hcoh hr h1 k).1.1]; exact wo_N_lt hr.lev hr.F_P (hlt k)
  B_cof := fun c hc => by
    obtain ⟨b, hb, hcb⟩ := hjw_Nx_cof (wo_l0 hr) hr.F_P hc
    obtain ⟨k, hk⟩ := hcof b hb
    exact ⟨k, by rw [(woW_mem hlev hlt f hcoh hr h1 k).1.1]; exact hcb.trans (hdN_lt_Nx hk)⟩
  R_ext := fun k c x hc => (woW_ext hlev hmono hlt f hcoh hr h1 k c x hc).1
  g_ext := fun k c hc => (woW_ext hlev hmono hlt f hcoh hr h1 k c 0 hc).2
  B_lt1 := hr.S_lt1
  B_fix := hdNx_fix (wo_one_lt_l hr) _
  B_mem := fun S a b ha hb => hr.S_mem ℓ hr.lev le_rfl S ha hb
  b_ge := fun k x hx hx1 hγ => by
    have hgk' : max r.γ (gtc (ls k)) < x := (max_le_max le_rfl (hgk k)).trans_lt hγ
    rw [(woW_mem hlev hlt f hcoh hr h1 k).1.2.2.2.1 x hx hx1 hgk']
    exact hdNx_mono (rdc_le_mono hx hr.lev.2.2 (hlt k).le (max_lt_iff.1 hγ).2 (max_lt_iff.1 hgk').2) _
  b_cof := fun x hx hx1 hγ ν hν => by
    have hr0 : rdc ℓ x ≠ 0 := (hx.pos.trans_le (wo_x_le_rdc hr hx hx1 hγ)).ne'
    obtain ⟨b, hb, hνb⟩ := hjw_Nx_cof hr0 (wo_rd hr hx hx1 hγ).1 hν
    obtain ⟨t, ht, hgt, rfl⟩ := rdc_surj hx hx1.le hr.lev.2.2 (max_lt_iff.1 hγ).2 hb
    obtain ⟨k, hk⟩ := hcof t ht
    have hgk' : max r.γ (gtc (ls k)) < x := (max_le_max le_rfl (hgk k)).trans_lt hγ
    have hkW : ls k < gfE := (hlt k).trans hr.lev.2.2
    have htW : t < gfE := ht.trans hr.lev.2.2
    have hg1 : gtc (t + 1) < x := ((rdc_succ t htW 0).2.2).trans_lt (wo_add_one_lt_inE hx hgt)
    have hlt' : rdc t x + 1 < rdc (ls k) x := by
      rw [← (rdc_succ t htW x).1]; exact rdc_mono hx hkW hk (max_lt_iff.1 hgk').2 hg1
    refine ⟨k, ?_⟩
    rw [(woW_mem hlev hlt f hcoh hr h1 k).1.2.2.2.1 x hx hx1 hgk']
    exact hνb.trans (hdN_lt_Nx hlt')
  b_fix := fun x hx hx1 hγ => wo_b_fixn hr hx hx1 hγ (by exact_mod_cast natCast_lt_omega0 1)
  b_gt := fun x hx hx1 hγ => wo_b_gt hr hx hx1 hγ
  b_lt := fun x hx hx1 hγ => wo_b_lt1 hr hx hx1 hγ
  b_pi := fun σ ρ hB hγ => hr.S_pi ℓ hr.lev le_rfl σ ρ hB hγ
  Z_low := fun k x hx hx1 hγ => by
    rw [(woW_mem hlev hlt f hcoh hr h1 k).1.2.2.2.2.1 x hx hx1]
    split_ifs with h'
    · exact (hb_evZ_lt_fix2 (hr.Zo_fix x)
        ((hr.rd _ (wo_lsL hr.lev hlev hlt k) (hlt k).le x hx hx1 h').2.2)).le
    · exact le_rfl
  Zo_fix := fun x => hc_fix_down one_le_two (hr.Zo_fix x)
  Zo_G1 := hr.Zo_G1

end W

open Classical in
/-- **THE ENTRY AT AN `ω`-LIMIT LEVEL**: the union of the chain `woChW`. -/
noncomputable def woLimWE {ℓ : Ordinal.{0}} {ls : ℕ → Ordinal.{0}} (hlev : ∀ k, Om1 ≤ ls k ∧ Om1 ∣ ls k)
    (hmono : ∀ k, ls k < ls (k + 1)) (hlt : ∀ k, ls k < ℓ) (hcof : ∀ t, t < ℓ → ∃ k, t + 1 < ls k)
    (hgk : ∀ k, gtc (ls k) ≤ gtc ℓ) (f : ∀ μ : Ordinal.{0}, μ < ℓ → WoE) (hcoh : WoCoh ℓ f) : WoE := fun r S1 =>
  if h : WoGood r ℓ ∧ WoSh r Om1 S1 then (woChW hlev hmono hlt hcof hgk f hcoh h.1 h.2).U else S1

/-- **THE `ω`-LIMIT STEP**: every level with an `ω`-sequence of levels (`Wm.WmFs`). -/
theorem woStep_fs {ℓ : Ordinal.{0}} (hℓ : WmLev ℓ) (hfs : WmFs ℓ) : WoStepAt ℓ := by
  intro f hcoh
  obtain ⟨ls, hlev, hmono, hlt, hcof, hgk⟩ := hfs
  have hL := wo_lsL hℓ hlev hlt
  have e : ∀ r S1 (hr : WoGood r ℓ) (h1 : WoSh r Om1 S1),
      woLimWE hlev hmono hlt hcof hgk f hcoh r S1 = (woChW hlev hmono hlt hcof hgk f hcoh hr h1).U := by
    intro r S1 hr h1; unfold woLimWE; rw [dif_pos ⟨hr, h1⟩]
  refine ⟨woLimWE hlev hmono hlt hcof hgk f hcoh, fun r S1 hr h1 => ?_, fun μ h hμ r S1 hr h1 c x hc => ?_⟩
  · set C := woChW hlev hmono hlt hcof hgk f hcoh hr h1
    have M := woW_mem hlev hlt f hcoh hr h1
    rw [e r S1 hr h1]
    refine ⟨⟨rfl, ⟨le_max_left _ _, le_rfl⟩, fun x _ _ => Iff.rfl, fun x _ _ _ => rfl, fun x _ _ => rfl,
      fun c σ hFc hc hσ hσ1 hg => ?_⟩, fun c x hc => ?_, fun c σ hSc hc hσ hσ1 hg => ?_⟩
    · obtain ⟨k, hk⟩ := C.B_cof c hc
      rw [C.U_g hk] at hg
      exact (M k).1.2.2.2.2.2 c σ hFc hk hσ hσ1 hg
    · have hc0 : c < (C.D 0).B := hc.trans_le (wo_S1_le (hL 0) h1 (M 0).1)
      rw [C.U_R hc0, C.U_g hc0]; exact (M 0).2.1 c x hc
    · obtain ⟨k, hk⟩ := C.B_cof c hc
      rw [C.U_g hk] at hg
      obtain ⟨μ, hμ, hμk, hgμ, hcμ⟩ := (M k).2.2 c σ hSc hk hσ hσ1 hg
      exact ⟨μ, hμ, hμk.trans (hlt k), hgμ, hcμ⟩
  · set C := woChW hlev hmono hlt hcof hgk f hcoh hr h1
    have M := woW_mem hlev hlt f hcoh hr h1
    obtain ⟨k, hk⟩ := hcof μ h
    have hμk : μ < ls k := (lt_add_one μ).trans hk
    have hsp := hcoh.1 μ h hμ r S1 (hr.mono hμ h.le) h1
    have hc' : c < (C.D k).B := by
      show c < (f (ls k) (hlt k) r S1).B
      rw [(M k).1.1]; rw [hsp.1.1] at hc; exact hc.trans_le (hdNx_mono hμk.le _)
    rw [e r S1 hr h1, C.U_R hc', C.U_g hc']
    exact hcoh.2 μ (ls k) h (hlt k) hμk hμ (hL k) r S1 (hr.mono (hL k) (hlt k).le) h1 c x hc

end Googology.Trans.PoR.InaccPsi.R2.Wo

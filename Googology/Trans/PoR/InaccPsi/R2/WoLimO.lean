import Googology.Trans.PoR.InaccPsi.R2.WoLimW

/-!
# WoLimO: THE STEP AT A LEVEL OF COFINALITY `Ω₁` ON FAMILIES OVER RAW DATA

For a level `ℓ` with an `Ω₁`-sequence of levels `s μ` (`Wo.WoFs1`) and a coherent family below `ℓ`, the entries at
the `s μ` over a datum `r` form an `Ho.HoFam` (SMALL from the region gates `Wo.WoSm` and the gate-cofinality of the
sequence); its union `Ho.hoOU` is the entry at `ℓ`.

* `woFamO` (**THE `Ω₁`-FAMILY OF THE ENTRIES AT `s μ` OVER `r`**), `woLimOE` (its union), `woStep_om1` (**THE STEP AT
  EVERY LEVEL WITH AN `Ω₁`-SEQUENCE OF LEVELS**).

No new axiom.  New definitions: `woOD`, `woFamO`, `woLimOE`.
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

open Classical in
/-- The member `μ` over `r`: the entry at `s μ`. -/
noncomputable def woOD {ℓ : Ordinal.{0}} (s : Ordinal.{0} → Ordinal.{0}) (f : ∀ μ : Ordinal.{0}, μ < ℓ → WoE)
    (r : WoR) (S1 : HgVD) (μ : Ordinal.{0}) : HgVD :=
  if h : s μ < ℓ then f (s μ) h r S1 else S1

section O

variable {ℓ : Ordinal.{0}} {s : Ordinal.{0} → Ordinal.{0}} (hs : WoFs1 ℓ s) (f : ∀ μ : Ordinal.{0}, μ < ℓ → WoE)
  (hcoh : WoCoh ℓ f)

include hs

theorem woO_D_eq (r : WoR) (S1 : HgVD) {μ : Ordinal.{0}} (hμ : μ < Om1) :
    woOD s f r S1 μ = f (s μ) (hs.1.1 μ hμ).2 r S1 := by
  unfold woOD; rw [dif_pos (hs.1.1 μ hμ).2]

theorem woO_sL (hℓ : WmLev ℓ) {μ : Ordinal.{0}} (hμ : μ < Om1) : WmLev (s μ) :=
  ⟨(hs.2 μ hμ).1, (hs.2 μ hμ).2, (hs.1.1 μ hμ).2.trans hℓ.2.2⟩

variable {r : WoR} {S1 : HgVD} (hr : WoGood r ℓ) (h1 : WoSh r Om1 S1)

include hcoh hr h1 in
theorem woO_mem {μ : Ordinal.{0}} (hμ : μ < Om1) : WoSh r (s μ) (woOD s f r S1 μ) ∧
    (∀ c x, c < S1.B → (woOD s f r S1 μ).R c x = S1.R c x ∧ (woOD s f r S1 μ).g c = S1.g c) ∧
      WoSm r (s μ) S1 (woOD s f r S1 μ) := by
  rw [woO_D_eq hs f r S1 hμ]
  exact hcoh.1 _ (hs.1.1 μ hμ).2 (woO_sL hs hr.lev hμ) r S1 (hr.mono (woO_sL hs hr.lev hμ) (hs.1.1 μ hμ).2.le) h1

include hcoh hr h1 in
theorem woO_B {μ : Ordinal.{0}} (hμ : μ < Om1) : (woOD s f r S1 μ).B = hdNx (s μ) r.F :=
  (woO_mem hs f hcoh hr h1 hμ).1.1

include hr in
/-- **Gate-cofinality as a bound**: `b < ℓ` lies below some `s μ` (`μ < Ω₁`) with `b + 1 < s μ`. -/
theorem woO_cof {b σ : Ordinal.{0}} (hb : b < ℓ) (hσ : InE σ) (hσ1 : σ < Om1) (hg : gtc b < σ) :
    ∃ μ, μ < σ ∧ b + 1 < s μ := by
  obtain ⟨μ, hμ, hbμ⟩ := hs.1.2.2.2 σ hσ hσ1 b hb hg
  exact ⟨μ, hμ, wo_lev_lim (woO_sL hs hr.lev (hμ.trans hσ1)) hbμ⟩

include hr in
theorem woO_rdc_lt {x μ : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : gtc ℓ < x) (hμ : μ < x) :
    rdc (s μ) x + 1 < rdc ℓ x := by
  have hμ1 : μ < Om1 := hμ.trans hx1
  have hsW : s μ < gfE := (hs.1.1 μ hμ1).2.trans hr.lev.2.2
  have hgs : gtc (s μ) < x := hs.1.2.2.1 x hx hx1 hg μ hμ
  rw [← (rdc_succ (s μ) hsW x).1]
  exact rdc_mono hx hr.lev.2.2 (wo_lev_lim hr.lev (hs.1.1 μ hμ1).2) hg
    (((rdc_succ (s μ) hsW 0).2.2).trans_lt (wo_add_one_lt_inE hx hgs))

/-- **THE `Ω₁`-FAMILY OF THE ENTRIES AT `s μ` OVER `r`.** -/
noncomputable def woFamO : HoFam where
  D := woOD s f r S1
  B := hdNx ℓ r.F
  γ := max r.γ (gtc ℓ)
  b := fun x => hdNx (rdc ℓ x) (r.Fr x)
  Zo := r.Zo
  γ_lt := max_lt hr.γ_lt (gtc_lt_Om1 ℓ hr.lev.2.2)
  γ_cl := fun Z hZ hZ1 h => wo_S_gZ hr hZ hZ1 h
  G_lt := hr.G_le.trans_lt (hdNx_gt _ _)
  B_E := hdNx_E (wo_l0 hr) _
  B_lt1 := hr.S_lt1
  B_fix1 := hdNx_fix (wo_one_lt_l hr) _
  B_mem := fun S a b ha hb => hr.S_mem ℓ hr.lev le_rfl S ha hb
  DB_lt := fun μ hμ => by
    rw [woO_B hs f hcoh hr h1 hμ]; exact wo_N_lt hr.lev hr.F_P (hs.1.1 μ hμ).2
  B_cof := fun c hc => by
    obtain ⟨b, hb, hcb⟩ := hjw_Nx_cof (wo_l0 hr) hr.F_P hc
    have hgb : gtc b < Om1 := gtc_lt_Om1 b (hb.trans hr.lev.2.2)
    obtain ⟨μ, hμ, hbμ⟩ := woO_cof hs hr hb (eN_E (gtc b)) (eN_lt_Om1K hgb) (lt_eN _)
    have hμ1 : μ < Om1 := hμ.trans (eN_lt_Om1K hgb)
    exact ⟨μ, hμ1, by rw [woO_B hs f hcoh hr h1 hμ1]; exact hcb.trans (hdN_lt_Nx hbμ)⟩
  ext := fun μ' μ hle hμ c x hc => by
    rcases hle.lt_or_eq with hlt | rfl
    · have hμ'1 : μ' < Om1 := hlt.trans hμ
      rw [woO_D_eq hs f r S1 hμ, woO_D_eq hs f r S1 hμ'1]
      rw [woO_D_eq hs f r S1 hμ'1] at hc
      exact hcoh.2 _ _ (hs.1.1 μ' hμ'1).2 (hs.1.1 μ hμ).2 (hs.1.2.1 μ' μ hlt hμ) (woO_sL hs hr.lev hμ'1)
        (woO_sL hs hr.lev hμ) r S1 (hr.mono (woO_sL hs hr.lev hμ) (hs.1.1 μ hμ).2.le) h1 c x hc
    · exact ⟨rfl, rfl⟩
  small := fun μ hμ c hc σ hσ hσ1 hg => by
    obtain ⟨m1, -, m3⟩ := woO_mem hs f hcoh hr h1 hμ
    by_cases hcS : c < S1.B
    · refine ⟨0, hσ.pos, hcS.trans_le ?_⟩
      exact wo_S1_le (woO_sL hs hr.lev gv_Om1_pos) h1 (woO_mem hs f hcoh hr h1 gv_Om1_pos).1
    · obtain ⟨lv, hlv, hlvμ, hglv, hclv⟩ := m3 c σ (not_lt.1 hcS) hc hσ hσ1 hg
      obtain ⟨μ', hμ', hlvμ'⟩ := hs.1.2.2.2 σ hσ hσ1 lv (hlvμ.trans (hs.1.1 μ hμ).2) hglv
      have hμ'1 : μ' < Om1 := hμ'.trans hσ1
      refine ⟨μ', hμ', ?_⟩
      rw [woO_B hs f hcoh hr h1 hμ'1]
      exact hclv.trans_le (hdNx_mono (wh_lev_succ_le hlv.2.1 (hs.2 μ' hμ'1).2 hlvμ') _)
  γD := fun x hx hx1 hγ μ hμ => by
    have hμ1 : μ < Om1 := hμ.trans hx1
    exact (woO_mem hs f hcoh hr h1 hμ1).1.2.1.2.trans_lt
      (max_lt (max_lt_iff.1 hγ).1 (hs.1.2.2.1 x hx hx1 (max_lt_iff.1 hγ).2 μ hμ))
  bD := fun x hx hx1 hγ μ hμ => by
    have hμ1 : μ < Om1 := hμ.trans hx1
    have hgs : max r.γ (gtc (s μ)) < x := max_lt (max_lt_iff.1 hγ).1 (hs.1.2.2.1 x hx hx1 (max_lt_iff.1 hγ).2 μ hμ)
    rw [(woO_mem hs f hcoh hr h1 hμ1).1.2.2.2.1 x hx hx1 hgs]
    exact (hdNx_lt_N (hcN_gt _ _)).trans (hdN_lt_Nx (woO_rdc_lt hs hr hx hx1 (max_lt_iff.1 hγ).2 hμ))
  ZD := fun x hx hx1 hγ μ hμ => by
    have hμ1 : μ < Om1 := hμ.trans hx1
    have hgs : max r.γ (gtc (s μ)) < x := max_lt (max_lt_iff.1 hγ).1 (hs.1.2.2.1 x hx hx1 (max_lt_iff.1 hγ).2 μ hμ)
    rw [(woO_mem hs f hcoh hr h1 hμ1).1.2.2.2.2.1 x hx hx1, if_pos hgs]
    refine (hb_evZ_lt_fix2 (wo_b_fixn hr hx hx1 hγ (by exact_mod_cast natCast_lt_omega0 2)) ?_).le
    exact (hdNx_lt_N (hcN_gt _ _)).trans (hdN_lt_Nx (woO_rdc_lt hs hr hx hx1 (max_lt_iff.1 hγ).2 hμ))
  b_cof := fun x hx hx1 hγ ν hν => by
    have hr0 : rdc ℓ x ≠ 0 := (hx.pos.trans_le (wo_x_le_rdc hr hx hx1 hγ)).ne'
    obtain ⟨b, hb, hνb⟩ := hjw_Nx_cof hr0 (wo_rd hr hx hx1 hγ).1 hν
    obtain ⟨t, ht, hgt, rfl⟩ := rdc_surj hx hx1.le hr.lev.2.2 (max_lt_iff.1 hγ).2 hb
    obtain ⟨μ, hμ, hk⟩ := woO_cof hs hr ht hx hx1 hgt
    have hμ1 : μ < Om1 := hμ.trans hx1
    have hgs : max r.γ (gtc (s μ)) < x := max_lt (max_lt_iff.1 hγ).1 (hs.1.2.2.1 x hx hx1 (max_lt_iff.1 hγ).2 μ hμ)
    have hkW : s μ < gfE := (hs.1.1 μ hμ1).2.trans hr.lev.2.2
    have htW : t < gfE := ht.trans hr.lev.2.2
    have hg1 : gtc (t + 1) < x := ((rdc_succ t htW 0).2.2).trans_lt (wo_add_one_lt_inE hx hgt)
    have hlt' : rdc t x + 1 < rdc (s μ) x := by
      rw [← (rdc_succ t htW x).1]; exact rdc_mono hx hkW hk (max_lt_iff.1 hgs).2 hg1
    refine ⟨μ, hμ, ?_⟩
    rw [(woO_mem hs f hcoh hr h1 hμ1).1.2.2.2.1 x hx hx1 hgs]
    exact hνb.trans (hdN_lt_Nx hlt')
  b_E := fun x hx hx1 hγ => wo_b_E hr hx hx1 hγ
  x_lt_b := fun x hx hx1 hγ => wo_b_gt hr hx hx1 hγ
  b_fix1 := fun x hx hx1 hγ => wo_b_fixn hr hx hx1 hγ (by exact_mod_cast natCast_lt_omega0 1)
  b_lt1 := fun x hx hx1 hγ => wo_b_lt1 hr hx hx1 hγ
  b_pi := fun σ ρ hB hγ => hr.S_pi ℓ hr.lev le_rfl σ ρ hB hγ
  Z_low := fun μ hμ x hx hx1 hγ => by
    rw [(woO_mem hs f hcoh hr h1 hμ).1.2.2.2.2.1 x hx hx1]
    split_ifs with h'
    · exact (hb_evZ_lt_fix2 (hr.Zo_fix x)
        ((hr.rd _ (woO_sL hs hr.lev hμ) (hs.1.1 μ hμ).2.le x hx hx1 h').2.2)).le
    · exact le_rfl
  Zo_fix := hr.Zo_fix
  Zo_G1 := hr.Zo_G1

end O

open Classical in
/-- **THE ENTRY AT A LEVEL OF COFINALITY `Ω₁`**: the union of `woFamO`. -/
noncomputable def woLimOE {ℓ : Ordinal.{0}} {s : Ordinal.{0} → Ordinal.{0}} (hs : WoFs1 ℓ s)
    (f : ∀ μ : Ordinal.{0}, μ < ℓ → WoE) (hcoh : WoCoh ℓ f) : WoE := fun r S1 =>
  if h : WoGood r ℓ ∧ WoSh r Om1 S1 then hoOU (woFamO hs f hcoh h.1 h.2) else S1

/-- **THE STEP AT EVERY LEVEL WITH AN `Ω₁`-SEQUENCE OF LEVELS.** -/
theorem woStep_om1 {ℓ : Ordinal.{0}} {s : Ordinal.{0} → Ordinal.{0}} (hs : WoFs1 ℓ s) : WoStepAt ℓ := by
  intro f hcoh
  have e : ∀ r S1 (hr : WoGood r ℓ) (h1 : WoSh r Om1 S1),
      woLimOE hs f hcoh r S1 = hoOU (woFamO hs f hcoh hr h1) := by
    intro r S1 hr h1; unfold woLimOE; rw [dif_pos ⟨hr, h1⟩]
  refine ⟨woLimOE hs f hcoh, fun r S1 hr h1 => ?_, fun μ h hμ r S1 hr h1 c x hc => ?_⟩
  · set F := woFamO hs f hcoh hr h1
    rw [e r S1 hr h1]
    refine ⟨⟨rfl, ⟨le_max_left _ _, le_rfl⟩, fun x _ _ => Iff.rfl, fun x _ _ _ => rfl, fun x _ _ => rfl,
      fun c σ hFc hc hσ hσ1 hg => ?_⟩, fun c x hc => ?_, fun c σ hSc hc hσ hσ1 hg => ?_⟩
    · obtain ⟨μ, hμ, hk⟩ := F.B_cof c hc
      rw [hoOU_g F hμ hk] at hg
      exact (woO_mem hs f hcoh hr h1 hμ).1.2.2.2.2.2 c σ hFc hk hσ hσ1 hg
    · have hc0 : c < (F.D 0).B :=
        hc.trans_le (wo_S1_le (woO_sL hs hr.lev gv_Om1_pos) h1 (woO_mem hs f hcoh hr h1 gv_Om1_pos).1)
      rw [hoOU_R F gv_Om1_pos hc0, hoOU_g F gv_Om1_pos hc0]
      exact (woO_mem hs f hcoh hr h1 gv_Om1_pos).2.1 c x hc
    · obtain ⟨μ, hμ, hk⟩ := F.B_cof c hc
      rw [hoOU_g F hμ hk] at hg
      obtain ⟨μ', hμ', hμk, hgμ, hcμ⟩ := (woO_mem hs f hcoh hr h1 hμ).2.2 c σ hSc hk hσ hσ1 hg
      exact ⟨μ', hμ', hμk.trans (hs.1.1 μ hμ).2, hgμ, hcμ⟩
  · set F := woFamO hs f hcoh hr h1
    have hgμ : gtc μ < Om1 := gtc_lt_Om1 μ hμ.2.2
    obtain ⟨ν, hν, hk⟩ := woO_cof hs hr h (eN_E (gtc μ)) (eN_lt_Om1K hgμ) (lt_eN _)
    have hν1 : ν < Om1 := hν.trans (eN_lt_Om1K hgμ)
    have hμk : μ < s ν := (lt_add_one μ).trans hk
    have hsp := hcoh.1 μ h hμ r S1 (hr.mono hμ h.le) h1
    have hc' : c < (F.D ν).B := by
      show c < (woOD s f r S1 ν).B
      rw [woO_B hs f hcoh hr h1 hν1]; rw [hsp.1.1] at hc; exact hc.trans_le (hdNx_mono hμk.le _)
    rw [e r S1 hr h1, hoOU_R F hν1 hc', hoOU_g F hν1 hc']
    show (woOD s f r S1 ν).R c x = _ ∧ (woOD s f r S1 ν).g c = _
    rw [woO_D_eq hs f r S1 hν1]
    exact hcoh.2 μ (s ν) h (hs.1.1 ν hν1).2 hμk hμ (woO_sL hs hr.lev hν1) r S1
      (hr.mono (woO_sL hs hr.lev hν1) (hs.1.1 ν hν1).2.le) h1 c x hc

end Googology.Trans.PoR.InaccPsi.R2.Wo

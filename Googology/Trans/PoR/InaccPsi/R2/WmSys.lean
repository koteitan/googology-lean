import Googology.Trans.PoR.InaccPsi.R2.WmPkL
import Googology.Trans.PoR.InaccPsi.R2.WmArith

/-!
# WmSys: THE `ω`-LIMIT STEP OF THE LEVEL-CODE INDUCTION, GENERIC IN THE LEVEL

Given a level `ℓ` with an `ω`-sequence of levels `ℓ_k` (`Wm.WmFs`) and entries `(K_k, V_k)` at the `ℓ_k`
(`Wh.WhAt`) that extend each other (packages in the new sense `Wm.WmExt`, systems by agreement), this module builds
the entry at `ℓ`:

* `WmLim ℓ` (the data), `wmLimΛ` (the level datum `Wh.whLv ℓ`, gate `gtc ℓ`), `wmLim_lcof` (**the readings
  `rdc ℓ_k x` are cofinal in `rdc ℓ x`** above the gate), `wmLimSeq` (**the coherent sequence**, `Wm.WmSeq`),
  `wmLimK` (**the limit package** `Wm.wmPkL`);
* `wmLimCh` (**the gated `ω`-chain of the systems `V_k` over `G`**: bound `φ(ℓ, G+1)`, base reading
  `φ(rdc ℓ x, Γ_{x+1}+1)`, base gate `gtc ℓ`, low field `Wh.whZo`), `wmLimV` (its union), `wmLim_shape` (**the union
  is a start over `G` at the limit package**), `wmLim_NB`;
* `wmLim_at` (**THE LIMIT ENTRY IS AN ENTRY AT `ℓ`**), `wmLim_ext` (**it extends every member**), `wmLim_ext_below`
  (**and every entry at a level `ℓ' < ℓ` that some member extends**).

No new axiom.  New definitions: `WmLim`, `wmLimΛ`, `wmLimSeq`, `wmLimK`, `wmLimCh`, `wmLimV`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wm

open Googology.Trans.PoR.InaccPsi.R2.Wh Googology.Trans.PoR.InaccPsi.R2.Ho
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

/-- **THE DATA OF AN `ω`-LIMIT STEP AT `ℓ`**: an `ω`-sequence of levels with gates `≤ gtc ℓ` and entries at them
that extend each other. -/
structure WmLim (ℓ : Ordinal.{0}) where
  h1 : Om1 ≤ ℓ
  h2 : Om1 ∣ ℓ
  h3 : ℓ < gfE
  ls : ℕ → Ordinal.{0}
  lev : ∀ k, Om1 ≤ ls k ∧ Om1 ∣ ls k
  mono : ∀ k, ls k < ls (k + 1)
  lt : ∀ k, ls k < ℓ
  cof : ∀ t, t < ℓ → ∃ k, t + 1 < ls k
  gate : ∀ k, gtc (ls k) ≤ gtc ℓ
  K : ℕ → HnPk
  V : ℕ → HgVD
  at' : ∀ k, WhAt (ls k) (K k) (V k)
  ext : ∀ k, WmExt (K k) (K (k + 1))
  vext : ∀ k c x, c < (V k).B → (V (k + 1)).R c x = (V k).R c x ∧ (V (k + 1)).g c = (V k).g c

namespace WmLim

variable {ℓ : Ordinal.{0}} (W : WmLim ℓ)

/-- The level datum at `ℓ`: `Wh.whLv ℓ` (gate `gtc ℓ`, reading `rdc ℓ x` above it). -/
noncomputable abbrev Λ : HnLv := whLv ℓ W.h1 W.h2 W.h3

theorem lsW (k : ℕ) : ls W k < gfE := (W.lt k).trans W.h3

theorem Kg (k : ℕ) : (W.K k).Λ.g ≤ gtc ℓ := (W.at' k).2.2.2.2.1.trans (W.gate k)

theorem gk {x : Ordinal.{0}} (k : ℕ) (hg : gtc ℓ < x) : gtc (W.ls k) < x := (W.gate k).trans_lt hg

theorem Kgx {x : Ordinal.{0}} (k : ℕ) (hg : gtc ℓ < x) : (W.K k).Λ.g < x := (W.Kg k).trans_lt hg

theorem Kl {x : Ordinal.{0}} (k : ℕ) (hx : InE x) (hx1 : x < Om1) (hg : gtc ℓ < x) :
    (W.K k).Λ.l x = rdc (W.ls k) x := (W.at' k).2.1 x hx hx1 (W.Kgx k hg)

theorem Λl {x : Ordinal.{0}} (hx : InE x) (hg : gtc ℓ < x) : W.Λ.l x = rdc ℓ x := whLv_l W.h1 W.h2 W.h3 hx hg

/-- **The readings `rdc ℓ_k x` are cofinal in `rdc ℓ x`** above the gate. -/
theorem lcof {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : gtc ℓ < x) {t : Ordinal.{0}}
    (ht : t < rdc ℓ x) : ∃ k, t + 1 < rdc (W.ls k) x := by
  obtain ⟨b, hb, hgb, rfl⟩ := rdc_surj hx hx1.le W.h3 hg ht
  obtain ⟨k, hk⟩ := W.cof b hb
  have hbW : b < gfE := hb.trans W.h3
  have h1W : b + 1 < gfE := eW_indec.add_lt hbW (gf_one_lt_Om1.trans Om1_lt_eW)
  have hg1 : gtc (b + 1) < x :=
    gtc_add (fun _ _ hu hv => (inE_indec hx).add_lt hu hv) b 1 hbW (gf_one_lt_Om1.trans Om1_lt_eW) hgb
      (by rw [(rdc_const gf_one_lt_Om1 0).2]; exact one_lt_omega0.trans (omega0_lt_inE hx))
  refine ⟨k, (add_one_le_of_lt (rdc_mono hx h1W (lt_add_one b) hg1 hgb)).trans_lt ?_⟩
  exact rdc_mono hx (W.lsW k) hk (W.gk k hg) hg1

/-- **THE COHERENT SEQUENCE OF THE PACKAGES** below the level datum `Wh.whLv ℓ`. -/
noncomputable def seq : WmSeq W.Λ where
  K := W.K
  hL := fun k => by rw [(W.at' k).1]; exact wh_lev_succ_le (W.lev k).2 W.h2 (W.lt k)
  hl := fun k x hx hx1 hg => by
    rw [W.Kl k hx hx1 hg, W.Λl hx hg]
    exact wh_rdc_step hx (W.lev k).2 W.h2 (W.lt k) W.h3 (W.gk k hg) hg
  hLs := fun k => by
    rw [(W.at' k).1, (W.at' (k + 1)).1]; exact wh_lev_succ_le (W.lev k).2 (W.lev (k + 1)).2 (W.mono k)
  hls := fun k x hx hx1 hg => by
    rw [W.Kl k hx hx1 hg, W.Kl (k + 1) hx hx1 hg]
    exact wh_rdc_step hx (W.lev k).2 (W.lev (k + 1)).2 (W.mono k) (W.lsW (k + 1)) (W.gk k hg) (W.gk (k + 1) hg)
  cof := fun t ht => by
    obtain ⟨k, hk⟩ := W.cof t ht
    exact ⟨k, by rw [(W.at' k).1]; exact hk⟩
  lcof := fun x hx hx1 hg t ht => by
    rw [W.Λl hx hg] at ht
    obtain ⟨k, hk⟩ := W.lcof hx hx1 hg ht
    exact ⟨k, by rw [W.Kl k hx hx1 hg]; exact hk⟩
  Kg := W.Kg
  ext := W.ext

/-- **THE LIMIT PACKAGE.** -/
noncomputable def K' : HnPk := wmPkL W.seq

theorem K'_Λ : W.K'.Λ = W.Λ := rfl

/-! ## The systems over `G` -/

theorem G_fix {a : Ordinal.{0}} (ha : a < gfE) : veblen a (gcG 0) = gcG 0 :=
  gn_veb_fix (gcG_SC 0) (ha.trans gfE_lt_G0)

theorem VB (k : ℕ) : (W.V k).B = veblen (W.ls k) (gcG 0 + 1) := (W.at' k).2.2.1

theorem one_le_l {x : Ordinal.{0}} (Λ' : HnLv) (hx : InE x) : (1 : Ordinal.{0}) ≤ Λ'.l x :=
  (one_lt_omega0.trans (omega0_lt_inE hx)).le.trans (Λ'.l_ge x)

theorem one_lt_l {x : Ordinal.{0}} (Λ' : HnLv) (hx : InE x) : (1 : Ordinal.{0}) < Λ'.l x :=
  (one_lt_omega0.trans (omega0_lt_inE hx)).trans_le (Λ'.l_ge x)

/-- The shape of the member `k`: its base reading above the gate. -/
theorem Vb (k : ℕ) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : gtc ℓ < x) :
    (W.V k).b x = veblen ((W.K k).Λ.l x) (lgG x + 1) := by
  obtain ⟨hN, hsh⟩ := (W.at' k).2.2.2.2.2.2
  have h := hsh.2.2.1 x hx hx1 (max_lt (W.Kgx k hg) hx.pos)
  rw [h, add_zero]; rfl

theorem VZ_le (k : ℕ) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : (W.V k).Z x ≤ whZo x := by
  obtain ⟨hN, hsh⟩ := (W.at' k).2.2.2.2.2.2
  rw [hsh.2.2.2.1 x hx hx1]
  split_ifs with h
  · have hg : (W.K k).Λ.g < x := (max_lt_iff.1 h).1
    have hl : (W.K k).Λ.l x + 0 < eN (max ω x) := by
      rw [add_zero, max_eq_right (omega0_lt_inE hx).le]
      exact (le_self_add.trans_lt (hN x hx hx1 hg))
    refine (hb_evZ_lt_fix2 (whZo_fix x) ?_).le
    show veblen ((W.K k).Λ.l x + 0) (lgG x + 1) < veblen (eN (max ω x)) (lgG x + 1)
    exact hd_veb_left_lt hl _
  · have hg : ¬ (whGW (W.K k).Λ hN).γR < x := fun h' => h (max_lt h' hx.pos)
    rw [(whGW (W.K k).Λ hN).hnwZo_low hg]; exact le_rfl

/-- **THE GATED `ω`-CHAIN OF THE SYSTEMS `V_k` OVER `G`**. -/
noncomputable def ch : HgfCh where
  D := W.V
  B := veblen ℓ (gcG 0 + 1)
  b := fun x => veblen (W.Λ.l x) (lgG x + 1)
  γ := gtc ℓ
  Zo := whZo
  γ_lt := gtc_lt_Om1 ℓ W.h3
  γ0 := fun k => (W.at' k).2.2.2.1.trans (W.gate k)
  γ_cl := fun Z hZ hZ1 h => by
    have ha : (1 : Ordinal.{0}) ≤ ℓ := (one_lt_omega0.trans (omega0_lt_inE gl_Om1_E)).le.trans W.h1
    have hℓ0 : ℓ ≠ 0 := (zero_lt_one.trans_le ha).ne'
    have hG : gcG 0 < veblen ℓ (gcG 0 + 1) := (lt_add_one _).trans_le (right_le_veblen _ _)
    have hc := hi_cl_lvl ha hZ1 (hd_succ_lt hℓ0 _) hG h le_rfl ((isNormal_veblen _).strictMono (lt_add_one _))
    exact whDigitGate Z hZ hZ1 ℓ hc W.h3
  B_mono := fun k => by rw [W.VB, W.VB]; exact (hd_veb_left_lt (W.mono k) _).le
  B_lt := fun k => by rw [W.VB]; exact hd_veb_left_lt (W.lt k) _
  B_cof := fun c hc => by
    have hℓ0 : ℓ ≠ 0 := (wh_Om1_pos.trans_le W.h1).ne'
    obtain ⟨b, hb, hcb⟩ := hgVeb_cof hℓ0 (WmLim.G_fix W.h3) hc
    obtain ⟨k, hk⟩ := W.cof b hb
    refine ⟨k, ?_⟩
    rw [W.VB, ← hdNx_fixP (WmLim.G_fix (W.lsW k))]
    exact hcb.trans (hdN_lt_Nx hk)
  R_ext := fun k c x hc => (W.vext k c x hc).1
  g_ext := fun k c hc => (W.vext k c 0 hc).2
  B_lt1 := by
    have hG1 := gcG_SC 1
    have hE := Low.opow_eq_self_of_SC hG1
    have hfix : veblen ℓ (gcG 1) = gcG 1 := gn_veb_fix hG1 (W.Λ.L_lt 1)
    have h2 := (isNormal_veblen ℓ).strictMono ((ev_isSuccLimit_of_inE hE).add_one_lt (gcG_lt zero_lt_one))
    rwa [hfix] at h2
  B_fix := veblen_veblen_of_lt (hg_one_lt_Om1.trans_le W.h1) _
  B_mem := fun S a b ha hb => CSet.phi_mem (W.Λ.L_mem S a b ha hb) (CSet.succ_mem (gmS_G0_mem S ha))
  b_ge := fun k x hx hx1 hγ => by
    rw [W.Vb k hx hx1 hγ, W.Kl k hx hx1 hγ, W.Λl hx hγ]
    exact (hd_veb_left_lt (rdc_mono hx W.h3 (W.lt k) hγ (W.gk k hγ)) _).le
  b_cof := fun x hx hx1 hγ ν hν => by
    have h0 : W.Λ.l x ≠ 0 := (zero_lt_one.trans (WmLim.one_lt_l W.Λ hx)).ne'
    obtain ⟨b, hb, hνb⟩ := hgVeb_cof h0 (hjG_fix hx hx1 (WmLim.one_le_l W.Λ hx) (W.Λ.l_lt x hx hx1)) hν
    rw [W.Λl hx hγ] at hb
    obtain ⟨k, hk⟩ := W.lcof hx hx1 hγ hb
    refine ⟨k, ?_⟩
    rw [W.Vb k hx hx1 hγ, ← hdNx_fixP (hjG_fix hx hx1 (WmLim.one_le_l (W.K k).Λ hx) ((W.K k).Λ.l_lt x hx hx1))]
    refine hνb.trans (hdN_lt_Nx ?_)
    rw [W.Kl k hx hx1 hγ]; exact hk
  b_fix := fun x hx _ _ => veblen_veblen_of_lt (WmLim.one_lt_l W.Λ hx) _
  b_gt := fun x hx hx1 _ => (lgG_facts hx hx1).2.1.trans ((lt_add_one _).trans_le (right_le_veblen _ _))
  b_lt := fun x hx hx1 _ => by
    rw [← hdNx_fixP (hjG_fix hx hx1 (WmLim.one_le_l W.Λ hx) (W.Λ.l_lt x hx hx1))]
    exact hjG_lt1 hx hx1 (WmLim.one_le_l W.Λ hx) (W.Λ.l_lt x hx hx1)
  b_pi := fun σ ρ hB hγ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    rw [← hdNx_fixP (hjG_fix hB.2.1 hρ1 (WmLim.one_le_l W.Λ hB.2.1) (W.Λ.l_lt ρ hB.2.1 hρ1)),
      ← hdNx_fixP (hjG_fix hB.1 hσ1 (WmLim.one_le_l W.Λ hB.1) (W.Λ.l_lt σ hB.1 hσ1))]
    exact hjG_S_pi hB (W.Λ.l_pi σ ρ hB hγ) (WmLim.one_le_l W.Λ hB.2.1) (W.Λ.l_lt ρ hB.2.1 hρ1)
      (WmLim.one_le_l W.Λ hB.1) (W.Λ.l_lt σ hB.1 hσ1)
  Z_low := fun k x hx hx1 _ => W.VZ_le k hx hx1
  Zo_fix := fun x => hc_fix_down one_le_two (whZo_fix x)
  Zo_G1 := fun x hx hx1 => whZo_G1 hx hx1

/-- **THE LIMIT SYSTEM OVER `G`**: the union of the chain. -/
noncomputable def V' : HgVD := W.ch.U

/-- **The outer-field bound of the limit level datum.** -/
theorem NB : WhNB W.Λ := fun x hx hx1 hg => by
  show W.Λ.l x + x < eN x
  rw [W.Λl hx hg]
  exact (inE_indec (eN_E x)).add_lt (rdc_lt_eN hx _ hg) (lt_eN x)

/-- **THE LIMIT SYSTEM IS A START OVER `G` AT THE LIMIT PACKAGE.** -/
theorem shape : HnWShape (whGW W.Λ W.NB) 0 W.V' := by
  refine ⟨?_, fun x _ _ => ?_, fun x hx hx1 _ => ?_, fun x hx hx1 => ?_, fun _ σ _ _ hσ _ _ => hσ.pos⟩
  · show veblen ℓ (gcG 0 + 1) = veblen (ℓ + 0) (gcG 0 + 1); rw [add_zero]
  · show gtc ℓ < x ↔ max (gtc ℓ) 0 < x
    rw [max_eq_left zero_le]
  · show veblen (W.Λ.l x) (lgG x + 1) = veblen (W.Λ.l x + 0) (lgG x + 1)
    rw [add_zero]
  · show (if gtc ℓ < x then evZ (veblen (W.Λ.l x) (lgG x + 1)) else whZo x) =
      if max (gtc ℓ) 0 < x then evZ (veblen (W.Λ.l x + 0) (lgG x + 1)) else (whGW W.Λ W.NB).hnwZo x
    rw [max_eq_left zero_le, add_zero]
    split_ifs with hg
    · rfl
    · rw [(whGW W.Λ W.NB).hnwZo_low (show ¬ gtc ℓ < x from hg)]; rfl

/-- **THE LIMIT ENTRY IS AN ENTRY AT `ℓ`.** -/
theorem at_lim : WhAt ℓ W.K' W.V' :=
  ⟨rfl, fun x hx _ hg => W.Λl hx hg, rfl, le_rfl, le_rfl, fun _ _ _ hg => hg, W.NB, W.shape⟩

/-- **THE LIMIT ENTRY EXTENDS EVERY MEMBER** (package in the new sense, system by agreement). -/
theorem ext_mem (k : ℕ) : WmExt (W.K k) W.K' ∧ (W.V k).B < W.V'.B ∧
    ∀ c x, c < (W.V k).B → W.V'.R c x = (W.V k).R c x ∧ W.V'.g c = (W.V k).g c :=
  ⟨wmPkL_ext W.seq k, W.ch.B_lt k, fun c x hc => ⟨W.ch.U_R (k := k) hc x, W.ch.U_g (k := k) hc⟩⟩

/-- **THE LIMIT ENTRY EXTENDS EVERY ENTRY AT A LOWER LEVEL THAT SOME MEMBER EXTENDS.** -/
theorem ext_below {ℓ' : Ordinal.{0}} {A : HnPk} {VA : HgVD} (hat : WhAt ℓ' A VA) (hd : Om1 ∣ ℓ') (k : ℕ)
    (hlt : ℓ' < W.ls k) (hA : WmExt A (W.K k)) (hB : VA.B < (W.V k).B)
    (hR : ∀ c x, c < VA.B → (W.V k).R c x = VA.R c x ∧ (W.V k).g c = VA.g c) :
    WmExt A W.K' ∧ VA.B < W.V'.B ∧ ∀ c x, c < VA.B → W.V'.R c x = VA.R c x ∧ W.V'.g c = VA.g c := by
  obtain ⟨m1, m2, m3⟩ := W.ext_mem k
  obtain ⟨hL, hl⟩ := wmLev_step hat (W.at' k) hd (W.lev k).2 hlt (W.lsW k)
  refine ⟨wmPkL_ext_below W.seq k hA hL (fun x hx hx1 h => hl x hx hx1 (max_lt_iff.1 h).1
    ((W.Kg k).trans_lt (max_lt_iff.1 h).2)), hB.trans m2, fun c x hc => ?_⟩
  obtain ⟨r1, g1⟩ := m3 c x (hc.trans hB)
  obtain ⟨r2, g2⟩ := hR c x hc
  exact ⟨r1.trans r2, g1.trans g2⟩

end WmLim

end Googology.Trans.PoR.InaccPsi.R2.Wm

import Googology.Trans.PoR.InaccPsi.R2.WmSys
import Googology.Trans.PoR.InaccPsi.R2.WpLow

/-!
# WpSys: THE `ω`-LIMIT STEP OF REGION (A2) ON `Wn.WnAt`

`Wm.WmLim` builds the limit entry from an `ω`-sequence of (A1) entries `Wh.WhAt` (base `Wh.whGW`, reading `rdc`).
`WpLim` is the same data for (A2) entries `Wn.WnAt`; what differs: the level datum is `Wn.wnLv ℓ` (reading `glR`,
gate `glG`, bound `G`), the base over `G` is `Wn.wnGW` (outer low field `Wn.wnZo`, no bound on the level), the gate
of the level is the digit gate `Wj.wjDigitGateG`, cofinality of readings is `Gl.glR_cof`.  The limit PACKAGE is
`Wm.wmPkL` itself (imported, any level datum), and the extension lemmas are `Wm.wmPkL_ext`, `Wm.wmPkL_ext_below`.

* `WpLim ℓ` (**an `ω`-sequence of (A2) levels with gates `≤ glG ℓ`, entries `Wn.WnAt` extending each other**);
* `WpLim.seq` (**a `Wm.WmSeq` below `Wn.wnLv ℓ`**), `WpLim.K'` (`= Wm.wmPkL`), `WpLim.ch` (**the gated chain of the
  systems over `G`**), `WpLim.V'` (its union), `WpLim.shape` (**a start over `Wn.wnGW` at the limit package**);
* `WpLim.at_lim` (**the limit entry is an (A2) entry at `ℓ`**), `WpLim.ext_mem`, `WpLim.ext_below`.

No new axiom.  New definitions: `WpLim` and its fields' derived data.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wp

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
open Googology.Trans.PoR.InaccPsi.R2.Wm Googology.Trans.PoR.InaccPsi.R2.Wn Googology.Trans.PoR.InaccPsi.R2.Gk

/-- **THE DATA OF AN `ω`-LIMIT STEP AT AN (A2) LEVEL `ℓ`**: an `ω`-sequence of levels with gates `≤ glG ℓ`, entries
`Wn.WnAt` at them extending each other (`Wm.WmExt` for packages, agreement for systems). -/
structure WpLim (ℓ : Ordinal.{0}) where
  h1 : Om1 ≤ ℓ
  h2 : Om1 ∣ ℓ
  h3 : ℓ < gcG 0
  ls : ℕ → Ordinal.{0}
  lev : ∀ k, Om1 ≤ ls k ∧ Om1 ∣ ls k
  mono : ∀ k, ls k < ls (k + 1)
  lt : ∀ k, ls k < ℓ
  cof : ∀ t, t < ℓ → ∃ k, t + 1 < ls k
  gate : ∀ k, glG (ls k) ≤ glG ℓ
  K : ℕ → HnPk
  V : ℕ → HgVD
  at' : ∀ k, WnAt (ls k) (K k) (V k)
  ext : ∀ k, WmExt (K k) (K (k + 1))
  vext : ∀ k c x, c < (V k).B → (V (k + 1)).R c x = (V k).R c x ∧ (V (k + 1)).g c = (V k).g c

namespace WpLim

variable {ℓ : Ordinal.{0}} (W : WpLim ℓ)

/-- The level datum at `ℓ`: `Wn.wnLv ℓ` (gate `glG ℓ`, reading `glR ℓ x` above it). -/
noncomputable abbrev Λ : HnLv := wnLv ℓ W.h1 W.h2 W.h3

theorem lsG (k : ℕ) : ls W k < gcG 0 := (W.lt k).trans W.h3

theorem Kg (k : ℕ) : (W.K k).Λ.g ≤ glG ℓ := (W.at' k).2.2.2.2.1.trans (W.gate k)

theorem gk {x : Ordinal.{0}} (k : ℕ) (hg : glG ℓ < x) : glG (W.ls k) < x := (W.gate k).trans_lt hg

theorem Kgx {x : Ordinal.{0}} (k : ℕ) (hg : glG ℓ < x) : (W.K k).Λ.g < x := (W.Kg k).trans_lt hg

theorem Kl {x : Ordinal.{0}} (k : ℕ) (hx : InE x) (hx1 : x < Om1) (hg : glG ℓ < x) :
    (W.K k).Λ.l x = glR (W.ls k) x := (W.at' k).2.1 x hx hx1 (W.Kgx k hg)

theorem Λl {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : glG ℓ < x) : W.Λ.l x = glR ℓ x :=
  wnRd_eq hx hx1 W.h1 W.h3 hg

/-- **The readings `glR ℓ_k x` are cofinal in `glR ℓ x`** above the gate (`Gl.glR_cof`). -/
theorem lcof {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : glG ℓ < x) {t : Ordinal.{0}}
    (ht : t < glR ℓ x) : ∃ k, t + 1 < glR (W.ls k) x := by
  obtain ⟨b, hb, hgb, htb⟩ := glR_cof hx hx1 ℓ W.h3 hg t ht
  obtain ⟨k, hk⟩ := W.cof b hb
  have hb1G : b + 1 < gcG 0 := hk.trans (W.lsG k)
  have hg1 : glG (b + 1) < x := glG_succ (ev_isSuccLimit_of_inE hx) b hb1G hgb
  refine ⟨k, ?_⟩
  calc t + 1 ≤ glR b x + 1 := add_le_add htb le_rfl
    _ = glR (b + 1) x := (glR_succ b hb1G x).symm
    _ < glR (W.ls k) x := glR_mono hx hx1 (W.lsG k) hk (W.gk k hg) hg1

/-- **THE COHERENT SEQUENCE OF THE PACKAGES** below the level datum `Wn.wnLv ℓ`. -/
noncomputable def seq : WmSeq W.Λ where
  K := W.K
  hL := fun k => by rw [(W.at' k).1]; exact wh_lev_succ_le (W.lev k).2 W.h2 (W.lt k)
  hl := fun k x hx hx1 hg => by
    rw [W.Kl k hx hx1 hg, W.Λl hx hx1 hg]
    exact wn_glR_step hx hx1 (W.lev k).2 W.h2 (W.lt k) W.h3 (W.gk k hg) hg
  hLs := fun k => by
    rw [(W.at' k).1, (W.at' (k + 1)).1]; exact wh_lev_succ_le (W.lev k).2 (W.lev (k + 1)).2 (W.mono k)
  hls := fun k x hx hx1 hg => by
    rw [W.Kl k hx hx1 hg, W.Kl (k + 1) hx hx1 hg]
    exact wn_glR_step hx hx1 (W.lev k).2 (W.lev (k + 1)).2 (W.mono k) (W.lsG (k + 1)) (W.gk k hg)
      (W.gk (k + 1) hg)
  cof := fun t ht => by
    obtain ⟨k, hk⟩ := W.cof t ht
    exact ⟨k, by rw [(W.at' k).1]; exact hk⟩
  lcof := fun x hx hx1 hg t ht => by
    rw [W.Λl hx hx1 hg] at ht
    obtain ⟨k, hk⟩ := W.lcof hx hx1 hg ht
    exact ⟨k, by rw [W.Kl k hx hx1 hg]; exact hk⟩
  Kg := W.Kg
  ext := W.ext

/-- **THE LIMIT PACKAGE** (`Wm.wmPkL`). -/
noncomputable def K' : HnPk := wmPkL W.seq

theorem K'_Λ : W.K'.Λ = W.Λ := rfl

theorem VB (k : ℕ) : (W.V k).B = veblen (W.ls k) (gcG 0 + 1) := (W.at' k).2.2.1

/-- The shape of the member `k`: its base reading above the gate. -/
theorem Vb (k : ℕ) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : glG ℓ < x) :
    (W.V k).b x = veblen ((W.K k).Λ.l x) (lgG x + 1) := by
  have hsh := (W.at' k).2.2.2.2.2.2
  have h := hsh.2.2.1 x hx hx1 (max_lt (W.Kgx k hg) hx.pos)
  rw [h, add_zero]; rfl

theorem G_fix {a : Ordinal.{0}} (ha : a < gcG 0) : veblen a (gcG 0) = gcG 0 := gn_veb_fix (gcG_SC 0) ha

/-- **THE GATED `ω`-CHAIN OF THE SYSTEMS `V_k` OVER `G`** (outer low field `Wn.wnZo`). -/
noncomputable def ch : HgfCh where
  D := W.V
  B := veblen ℓ (gcG 0 + 1)
  b := fun x => veblen (W.Λ.l x) (lgG x + 1)
  γ := glG ℓ
  Zo := wnZo
  γ_lt := glG_lt_Om1 ℓ W.h3
  γ0 := fun k => (W.at' k).2.2.2.1.trans (W.gate k)
  γ_cl := fun Z hZ hZ1 h => by
    have ha : (1 : Ordinal.{0}) ≤ ℓ := (one_lt_omega0.trans (omega0_lt_inE gl_Om1_E)).le.trans W.h1
    have hℓ0 : ℓ ≠ 0 := (zero_lt_one.trans_le ha).ne'
    have hG : gcG 0 < veblen ℓ (gcG 0 + 1) := (lt_add_one _).trans_le (right_le_veblen _ _)
    have hc := hi_cl_lvl ha hZ1 (hd_succ_lt hℓ0 _) hG h le_rfl ((isNormal_veblen _).strictMono (lt_add_one _))
    exact Wj.wjDigitGateG Z hZ hZ1 ℓ hc W.h3
  B_mono := fun k => by rw [W.VB, W.VB]; exact (hd_veb_left_lt (W.mono k) _).le
  B_lt := fun k => by rw [W.VB]; exact hd_veb_left_lt (W.lt k) _
  B_cof := fun c hc => by
    have hℓ0 : ℓ ≠ 0 := (wh_Om1_pos.trans_le W.h1).ne'
    obtain ⟨b, hb, hcb⟩ := hgVeb_cof hℓ0 (WpLim.G_fix W.h3) hc
    obtain ⟨k, hk⟩ := W.cof b hb
    refine ⟨k, ?_⟩
    rw [W.VB, ← hdNx_fixP (WpLim.G_fix (W.lsG k))]
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
    rw [W.Vb k hx hx1 hγ, W.Kl k hx hx1 hγ, W.Λl hx hx1 hγ]
    exact (hd_veb_left_lt (glR_mono hx hx1 W.h3 (W.lt k) hγ (W.gk k hγ)) _).le
  b_cof := fun x hx hx1 hγ ν hν => by
    have h0 : W.Λ.l x ≠ 0 := (zero_lt_one.trans (WmLim.one_lt_l W.Λ hx)).ne'
    obtain ⟨b, hb, hνb⟩ := hgVeb_cof h0 (hjG_fix hx hx1 (WmLim.one_le_l W.Λ hx) (W.Λ.l_lt x hx hx1)) hν
    rw [W.Λl hx hx1 hγ] at hb
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
  Z_low := fun k x hx hx1 _ => wpZ_le (W.at' k).2.2.2.2.2.2 hx hx1
  Zo_fix := fun x => hc_fix_down one_le_two (wnZo_fix x)
  Zo_G1 := fun x hx hx1 => wnZo_G1 hx hx1

/-- **THE LIMIT SYSTEM OVER `G`**: the union of the chain. -/
noncomputable def V' : HgVD := W.ch.U

/-- **THE LIMIT SYSTEM IS A START OVER `Wn.wnGW` AT THE LIMIT PACKAGE.** -/
theorem shape : HnWShape (wnGW W.Λ) 0 W.V' := by
  refine ⟨?_, fun x _ _ => ?_, fun x hx hx1 _ => ?_, fun x hx hx1 => ?_, fun _ σ _ _ hσ _ _ => hσ.pos⟩
  · show veblen ℓ (gcG 0 + 1) = veblen (ℓ + 0) (gcG 0 + 1); rw [add_zero]
  · show glG ℓ < x ↔ max (glG ℓ) 0 < x
    rw [max_eq_left zero_le]
  · show veblen (W.Λ.l x) (lgG x + 1) = veblen (W.Λ.l x + 0) (lgG x + 1)
    rw [add_zero]
  · show (if glG ℓ < x then evZ (veblen (W.Λ.l x) (lgG x + 1)) else wnZo x) =
      if max (glG ℓ) 0 < x then evZ (veblen (W.Λ.l x + 0) (lgG x + 1)) else (wnGW W.Λ).hnwZo x
    rw [max_eq_left zero_le, add_zero]
    split_ifs with hg
    · rfl
    · rw [(wnGW W.Λ).hnwZo_low (show ¬ glG ℓ < x from hg)]; rfl

/-- **THE LIMIT ENTRY IS AN (A2) ENTRY AT `ℓ`.** -/
theorem at_lim : WnAt ℓ W.K' W.V' :=
  ⟨rfl, fun x hx hx1 hg => W.Λl hx hx1 hg, rfl, le_rfl, le_rfl, fun _ _ _ hg => hg, W.shape⟩

/-- **THE LIMIT ENTRY EXTENDS EVERY MEMBER** (package in the corrected sense, system by agreement). -/
theorem ext_mem (k : ℕ) : WmExt (W.K k) W.K' ∧ (W.V k).B < W.V'.B ∧
    ∀ c x, c < (W.V k).B → W.V'.R c x = (W.V k).R c x ∧ W.V'.g c = (W.V k).g c :=
  ⟨wmPkL_ext W.seq k, W.ch.B_lt k, fun c x hc => ⟨W.ch.U_R (k := k) hc x, W.ch.U_g (k := k) hc⟩⟩

/-- **THE LIMIT ENTRY EXTENDS EVERY (A2) ENTRY AT A LOWER LEVEL THAT SOME MEMBER EXTENDS.** -/
theorem ext_below {ℓ' : Ordinal.{0}} {A : HnPk} {VA : HgVD} (hat : WnAt ℓ' A VA) (hd : Om1 ∣ ℓ') (k : ℕ)
    (hlt : ℓ' < W.ls k) (hA : WmExt A (W.K k)) (hB : VA.B < (W.V k).B)
    (hR : ∀ c x, c < VA.B → (W.V k).R c x = VA.R c x ∧ (W.V k).g c = VA.g c) :
    WmExt A W.K' ∧ VA.B < W.V'.B ∧ ∀ c x, c < VA.B → W.V'.R c x = VA.R c x ∧ W.V'.g c = VA.g c := by
  obtain ⟨m1, m2, m3⟩ := W.ext_mem k
  obtain ⟨hL, hl⟩ := wpLev_step hat (W.at' k) hd (W.lev k).2 hlt (W.lsG k)
  refine ⟨wmPkL_ext_below W.seq k hA hL (fun x hx hx1 h => hl x hx hx1 (max_lt_iff.1 h).1
    ((W.Kg k).trans_lt (max_lt_iff.1 h).2)), hB.trans m2, fun c x hc => ?_⟩
  obtain ⟨r1, g1⟩ := m3 c x (hc.trans hB)
  obtain ⟨r2, g2⟩ := hR c x hc
  exact ⟨r1.trans r2, g1.trans g2⟩

end WpLim

end Googology.Trans.PoR.InaccPsi.R2.Wp

import Googology.Trans.PoR.InaccPsi.R2.XlK

/-!
# XlKRec: THE LEVELS `G + κ` FOR EVERY `κ < Ω₁` BY ONE RECURSION ON THE LEVEL

One recursion `xlK κ` (`κ < Ω₁`) gives the system at `φ(G + κ + 1, 0)`, the top of the level `G + κ`:

* `xlK 0 = Xl.xlTop` (the level `G`, `Xl.XlFr`);
* `xlK (κ + 1)`: the bottom recursion of the level `G + κ + 1` (`Xl.XlRec`, base `Xl.xlBK`, step `Hn.hnVLS` of the
  package `Xf.xfPk` at the level offset `κ + 1`) started at `xlK κ` (a system at `φ(G + κ + 1, 0)`), and its top;
* `xlK λ` at a limit: the gated `ω`-chain union of the `xlK (heFs λ k)` (`xlKCh`: bound `φ(G + λ, 0)`, gate `λ`, base
  reading `φ(Γ_{x+1} + λ, 0)`), then the bottom recursion of the level `G + λ` from it, and its top.

* `xlSt` (the step at the level `G + κ`), `xl_at_top`, `xl_at_G`, `xlKCh`, `xlKCh_at`, `xlK`, `xlK_inv`
  (**THE INVARIANT AT EVERY `κ < Ω₁`**: `xlK κ` is a system at `φ(G+κ+1, 0)` with gate `≤ κ + 1`, later systems
  extend earlier ones), `xlK_B`, `xlK_γ`, `xlK_ext`.

No new axiom.  New definitions: `xlSt`, `xlLT`, `XlKInv`, `xlKCh`, `xlKExt`, `xlKLim`, `xlK`.
-/

set_option autoImplicit false


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
open Googology.Trans.PoR.InaccPsi.R2.Wo Googology.Trans.PoR.InaccPsi.R2.Wn Googology.Trans.PoR.InaccPsi.R2.Wp
  Googology.Trans.PoR.InaccPsi.R2.Ws Googology.Trans.PoR.InaccPsi.R2.Wt Googology.Trans.PoR.InaccPsi.R2.Wy
  Googology.Trans.PoR.InaccPsi.R2.Wx


open Googology.Trans.PoR.InaccPsi.R2.Xc
open Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt

open Googology.Trans.PoR.InaccPsi.R2.Xf

namespace Googology.Trans.PoR.InaccPsi.R2.Xl

/-! ## The step and the top of a level -/

/-- **The step at the level `G + κ`**: `Hn.hnVLS` of the package at `G`. -/
noncomputable abbrev xlSt (κ : Ordinal.{0}) : HnVStTy xfLv κ := hnVLS xfPk.St0 κ

theorem xlSt_spec {κ : Ordinal.{0}} (hκ : κ < Om1) : ∀ Q U h, HnVSpec Q U (xlSt κ Q U h) :=
  fun Q U h => hnVLS_spec xfPk.St0 xfPk.h0 hκ Q U h

/-- **THE TOP OF THE LEVEL `G + κ` IS A SYSTEM AT `φ(G + κ + 1, 0)`.** -/
theorem xl_at_top {κ : Ordinal.{0}} (h1 : 1 ≤ κ) (hκ : κ < Om1) {U : HgVD} (hU : XlAt κ U) :
    XlAt (κ + 1) (xlTU (xlSt_spec hκ) (xl_start_of_at h1 hκ hU)) where
  B := by rw [xlTU_B, xl_N_eq, add_assoc]
  ix := by show hcN (xfLv.L + κ) 0 = _; rw [xl_N_eq, add_assoc]
  γ := fun x hx _ => by
    show κ < x ↔ κ + 1 < x
    exact ⟨fun h => (ev_isSuccLimit_of_inE hx).add_one_lt h, fun h => (lt_add_one κ).trans h⟩
  b := fun x _ _ _ => by show hcN (xfLv.l x + κ) 0 = _; rw [xl_N_eq, add_assoc]
  γ_le := by show κ ≤ κ + 1; exact (lt_add_one κ).le
  Z := fun x hx _ => by
    show (if κ < x then evZ (hcN (xfLv.l x + κ) 0) else xlZs x) = _
    by_cases h : κ < x
    · rw [if_pos h, if_pos ((ev_isSuccLimit_of_inE hx).add_one_lt h), xl_N_eq, add_assoc]
    · rw [if_neg h, if_neg (fun h' => h ((lt_add_one κ).trans h'))]

/-- **`Xl.xlTop` IS A SYSTEM AT `φ(G + 1, 0)`.** -/
theorem xl_at_G : XlAt 1 xlTop where
  B := by show hcN (xfLv.L + 0) 0 = _; rw [xl_N_eq, add_zero]
  ix := by show hcN (xfLv.L + 0) 0 = _; rw [xl_N_eq, add_zero]
  γ := fun _ _ _ => Iff.rfl
  b := fun x _ _ _ => by show hcN (xfLv.l x + 0) 0 = _; rw [xl_N_eq, add_zero]
  γ_le := le_rfl
  Z := fun x hx _ => by
    show (if (1 : Ordinal.{0}) < x then evZ (hcN (xfLv.l x + 0) 0) else wnZo x) = _
    rw [if_pos (wo_one_lt_inE hx), if_pos (wo_one_lt_inE hx), xl_N_eq, add_zero]

/-- The top of the level `G + κ` over a system at its bottom (when it is one). -/
noncomputable def xlLT (κ : Ordinal.{0}) (U : HgVD) : HgVD := by
  classical
  exact if h : 1 ≤ κ ∧ κ < Om1 ∧ XlAt κ U then xlTU (xlSt_spec h.2.1) (xl_start_of_at h.1 h.2.1 h.2.2) else U

theorem xlLT_eq {κ : Ordinal.{0}} (h1 : 1 ≤ κ) (hκ : κ < Om1) {U : HgVD} (hU : XlAt κ U) :
    xlLT κ U = xlTU (xlSt_spec hκ) (xl_start_of_at h1 hκ hU) := by
  unfold xlLT; rw [dif_pos ⟨h1, hκ, hU⟩]

/-! ## The invariant -/

/-- **The invariant of a family below `λ`**: each member is a system at `φ(G + μ + 1, 0)`; coherence. -/
structure XlKInv (l : Ordinal.{0}) (F : Ordinal.{0} → HgVD) : Prop where
  at_ : ∀ μ, μ < l → XlAt (μ + 1) (F μ)
  cohR : ∀ β γ, β ≤ γ → γ < l → ∀ c x, c < (F β).B → (F γ).R c x = (F β).R c x
  cohg : ∀ β γ, β ≤ γ → γ < l → ∀ c, c < (F β).B → (F γ).g c = (F β).g c

theorem XlKInv.congr {l : Ordinal.{0}} {F G : Ordinal.{0} → HgVD} (H : XlKInv l F)
    (hFG : ∀ β, β < l → G β = F β) : XlKInv l G where
  at_ := fun μ h => by rw [hFG μ h]; exact H.at_ μ h
  cohR := fun β γ hβγ h c x hc => by
    rw [hFG β (lt_of_le_of_lt hβγ h)] at hc ⊢
    rw [hFG γ h]; exact H.cohR β γ hβγ h c x hc
  cohg := fun β γ hβγ h c hc => by
    rw [hFG β (lt_of_le_of_lt hβγ h)] at hc ⊢
    rw [hFG γ h]; exact H.cohg β γ hβγ h c hc

theorem xl_B_le {β γ : Ordinal.{0}} (hβγ : β ≤ γ) {U V : HgVD} (hU : XlAt (β + 1) U) (hV : XlAt (γ + 1) V) :
    U.B ≤ V.B := by
  rw [hU.B, hV.B]
  exact veblen_zero_le_veblen_zero.2 ((add_le_add_iff_left _).2 (Order.add_one_le_of_lt (hβγ.trans_lt (lt_add_one γ))))

/-! ## The union at a limit level -/

section Lim

variable {l : Ordinal.{0}} (hl : IsSuccLimit l) (hl1 : l < Om1)

include hl1 in
theorem xl_lOm : l < Om (1 : Ordinal.{0}) := by rw [← Br.Om1_eq]; exact hl1

include hl hl1 in
theorem xl_fs_lt (k : ℕ) : heFs l k < l := heFs_lt hl (xl_lOm hl1) k

include hl in
theorem xl_one_le_l : (1 : Ordinal.{0}) ≤ l := one_lt_omega0.le.trans (omega0_le_of_isSuccLimit hl)

include hl hl1 in
theorem xl_fs1_le (k : ℕ) : heFs l k + 1 ≤ l := Order.add_one_le_of_lt (xl_fs_lt hl hl1 k)

include hl in
theorem xl_GQl : gcG 0 < veblen (xfLv.L + l) 0 :=
  (by simpa using (add_lt_add_iff_left (gcG 0)).2 hl.bot_lt : gcG 0 < gcG 0 + l).trans_le (left_le_veblen _ 0)

include hl hl1 in
/-- `ϑˣ(Ω₁·(Γ_{x+1} + λ)) = φ(Γ_{x+1} + λ, 0)` above `λ`. -/
theorem xl_glA_l {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hlx : l < x) :
    glA (xfLv.l x + l) 0 x = veblen (xfLv.l x + l) 0 :=
  xl_glAv hx hx1 (hnv_one xfLv hx hx1 hlx) (hnv_q xfLv hx hx1 hlx) (hnv_xl xfLv hx hx1)
    (xl_lκ_lt_veb0 hx hx1 (xl_one_le_l hl) hlx) (xl_Nκ_lt1 hx hx1 hlx) 0 (hcN_E _ _).pos

variable (F : Ordinal.{0} → HgVD) (H : XlKInv l F)

/-- **THE GATED `ω`-CHAIN AT A LIMIT LEVEL `λ < Ω₁`**: the members `F (heFs λ k)`, bound `φ(G + λ, 0)`, gate `λ`. -/
noncomputable def xlKCh : HgfCh where
  D := fun k => F (heFs l k)
  B := veblen (xfLv.L + l) 0
  b := fun x => veblen (xfLv.l x + l) 0
  γ := l
  Zo := xlZs
  γ_lt := hl1
  γ0 := fun k => (H.at_ _ (xl_fs_lt hl hl1 k)).γ_le.trans (xl_fs1_le hl hl1 k)
  γ_cl := fun _ hZ hZ1 h => hnv_cl_gate xfLv hl1 hZ hZ1 veblen_pos (xl_GQl hl) h le_rfl
    ((isNormal_veblen _).strictMono (show (0 : Ordinal.{0}) < 0 + 1 by rw [zero_add]; exact zero_lt_one))
  B_mono := fun k => xl_B_le (heFs_mono hl (xl_lOm hl1) k).le (H.at_ _ (xl_fs_lt hl hl1 k))
    (H.at_ _ (xl_fs_lt hl hl1 (k + 1)))
  B_lt := fun k => by
    rw [(H.at_ _ (xl_fs_lt hl hl1 k)).B]
    exact veblen_zero_lt_veblen_zero.2 ((add_lt_add_iff_left _).2 (hl.add_one_lt (xl_fs_lt hl hl1 k)))
  B_cof := fun c hc => by
    obtain ⟨a, ha, hca⟩ := wx_veb_lim_cof0 (isSuccLimit_add _ hl) hc
    obtain ⟨d, hd, had⟩ := (lt_add_iff hl.bot_lt.ne').1 ha
    obtain ⟨k, hk⟩ := heFs_cof hl (xl_lOm hl1) d hd
    refine ⟨k, ?_⟩
    rw [(H.at_ _ (xl_fs_lt hl hl1 k)).B]
    exact hca.trans_le (veblen_zero_le_veblen_zero.2 (had.trans ((add_le_add_iff_left _).2 (hk.le.trans le_self_add))))
  R_ext := fun k c x hc => H.cohR _ _ (heFs_mono hl (xl_lOm hl1) k).le (xl_fs_lt hl hl1 (k + 1)) c x hc
  g_ext := fun k c hc => H.cohg _ _ (heFs_mono hl (xl_lOm hl1) k).le (xl_fs_lt hl hl1 (k + 1)) c hc
  B_lt1 := by
    show veblen (gcG 0 + l) 0 < gcG 1
    have hE := Low.opow_eq_self_of_SC (gcG_SC 1)
    have hlt : gcG 0 + l < gcG 1 := (inE_indec hE).add_lt (gcG_lt zero_lt_one)
      (hl1.trans (gl_Om1_lt_G0.trans (gcG_lt zero_lt_one)))
    have h := (isNormal_veblen (gcG 0 + l)).strictMono (gcG_SC 1).1
    rwa [gn_veb_fix (gcG_SC 1) hlt] at h
  B_fix := veblen_veblen_of_lt ((wh_one_lt_Om1.trans_le xfLv.OL).trans_le le_self_add) 0
  B_mem := fun S _ _ ha hb => CSet.phi_mem
    (hnv_L_mem xfLv S ha (by rw [xfLv_g]; exact (xl_one_le_l hl).trans_lt hb) hb) (CSet.zero_mem _ _)
  b_ge := fun k x hx hx1 hγ => by
    rw [(H.at_ _ (xl_fs_lt hl hl1 k)).b x hx hx1 ((xl_fs1_le hl hl1 k).trans_lt hγ)]
    exact veblen_zero_le_veblen_zero.2 ((add_le_add_iff_left _).2 (xl_fs1_le hl hl1 k))
  b_cof := fun x hx hx1 hγ ν hν => by
    obtain ⟨a, ha, hνa⟩ := wx_veb_lim_cof0 (isSuccLimit_add _ hl) hν
    obtain ⟨d, hd, had⟩ := (lt_add_iff hl.bot_lt.ne').1 ha
    obtain ⟨k, hk⟩ := heFs_cof hl (xl_lOm hl1) d hd
    refine ⟨k, ?_⟩
    rw [(H.at_ _ (xl_fs_lt hl hl1 k)).b x hx hx1 ((xl_fs1_le hl hl1 k).trans_lt hγ)]
    exact hνa.trans_le (veblen_zero_le_veblen_zero.2 (had.trans ((add_le_add_iff_left _).2 (hk.le.trans le_self_add))))
  b_fix := fun x hx hx1 _ => veblen_veblen_of_lt ((wo_one_lt_inE hx).trans_le (hnv_xl xfLv hx hx1)) 0
  b_gt := fun x hx hx1 hγ => (hnv_xl xfLv hx hx1).trans_lt (xl_lκ_lt_veb0 hx hx1 (xl_one_le_l hl) hγ)
  b_lt := fun x hx hx1 hγ => (xl_veb_lt_Zs hx hγ).trans (xlZs_G1 hx hx1)
  b_pi := fun σ ρ hB hγ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have h0σ : (0 : Ordinal.{0}) < σ := hB.1.pos
    have h := hnv_glA_pi xfLv (ν := l) hB (by rw [xfLv_g]; exact (xl_one_le_l hl).trans_lt hγ) hγ
      (mem_TB_of_lt hB h0σ) (gm1_facts hB.2.1 hρ1).2.2.2.pos
    rw [pi_lt hB h0σ, xl_glA_l hl hl1 hB.2.1 hρ1 (hγ.trans hB.2.2.1), xl_glA_l hl hl1 hB.1 hσ1 hγ] at h
    exact h
  Z_low := fun k x hx _ _ => by
    rw [(H.at_ _ (xl_fs_lt hl hl1 k)).Z x hx ‹_›]
    split_ifs with h
    · exact (hb_evZ_lt_fix2 (xlZs_fix x) (xl_veb_lt_Zs hx h)).le
    · exact le_rfl
  Zo_fix := xlZs_fix1
  Zo_G1 := fun _ hx hx1 => xlZs_G1 hx hx1

/-- **THE UNION AT A LIMIT LEVEL `λ` IS A SYSTEM AT `φ(G + λ, 0)`.** -/
theorem xlKCh_at : XlAt l (xlKCh hl hl1 F H).U where
  B := rfl
  ix := rfl
  γ := fun _ _ _ => Iff.rfl
  b := fun _ _ _ _ => rfl
  γ_le := le_rfl
  Z := fun x _ _ => (xlKCh hl hl1 F H).U_Z x

end Lim

/-! ## The recursion -/

/-- The family of the earlier values, extended by `Xl.xlTop`. -/
noncomputable def xlKExt (l : Ordinal.{0}) (IH : ∀ β, β < l → HgVD) (β : Ordinal.{0}) : HgVD :=
  if h : β < l then IH β h else xlTop

open Classical in
/-- The limit step: the top of the level `G + λ` over the union (when the invariant holds; it always does). -/
noncomputable def xlKLim (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ β, β < l → HgVD) : HgVD :=
  if H : l < Om1 ∧ XlKInv l (xlKExt l IH) then xlLT l (xlKCh hl H.1 (xlKExt l IH) H.2).U else xlTop

/-- **THE RECURSION**: `xlK κ` is the system at `φ(G + κ + 1, 0)`, the top of the level `G + κ`. -/
noncomputable def xlK (κ : Ordinal.{0}) : HgVD :=
  Ordinal.limitRecOn (motive := fun _ => HgVD) κ xlTop (fun κ U => xlLT (κ + 1) U) xlKLim

theorem xlK_zero : xlK 0 = xlTop := by unfold xlK; rw [Ordinal.limitRecOn_zero]

theorem xlK_succ (κ : Ordinal.{0}) : xlK (κ + 1) = xlLT (κ + 1) (xlK κ) := by
  unfold xlK; rw [Ordinal.limitRecOn_add_one]

theorem xlK_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) : xlK l = xlKLim l hl (fun β _ => xlK β) := by
  unfold xlK; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem xlKExt_eq {l β : Ordinal.{0}} (h : β < l) : xlKExt l (fun β _ => xlK β) β = xlK β := by
  unfold xlKExt; rw [dif_pos h]

theorem xlKInv_zero (F : Ordinal.{0} → HgVD) : XlKInv 0 F where
  at_ := fun _ h => absurd h (not_lt.2 zero_le)
  cohR := fun _ _ _ h => absurd h (not_lt.2 zero_le)
  cohg := fun _ _ _ h => absurd h (not_lt.2 zero_le)

/-- The new facts at the top `ν`. -/
structure XlKTop (ν : Ordinal.{0}) : Prop where
  at_ : XlAt (ν + 1) (xlK ν)
  cohR : ∀ β, β < ν → ∀ c x, c < (xlK β).B → (xlK ν).R c x = (xlK β).R c x
  cohg : ∀ β, β < ν → ∀ c, c < (xlK β).B → (xlK ν).g c = (xlK β).g c

theorem xlKInv_succ {ν : Ordinal.{0}} (H : XlKInv ν xlK) (T : XlKTop ν) : XlKInv (ν + 1) xlK where
  at_ := fun β h => by
    rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
    · exact H.at_ β h'
    · exact T.at_
  cohR := fun β γ hβγ h c x hc => by
    rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
    · exact H.cohR β γ hβγ h' c x hc
    · rcases hβγ.lt_or_eq with h'' | rfl
      · exact T.cohR β h'' c x hc
      · rfl
  cohg := fun β γ hβγ h c hc => by
    rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
    · exact H.cohg β γ hβγ h' c hc
    · rcases hβγ.lt_or_eq with h'' | rfl
      · exact T.cohg β h'' c hc
      · rfl

theorem xlKInv_lim {l : Ordinal.{0}} (IH : ∀ β, β < l → XlKInv (β + 1) xlK) : XlKInv l xlK where
  at_ := fun β h => (IH β h).at_ β (lt_add_one β)
  cohR := fun β γ hβγ h => (IH γ h).cohR β γ hβγ (lt_add_one γ)
  cohg := fun β γ hβγ h => (IH γ h).cohg β γ hβγ (lt_add_one γ)

theorem xlKTop_zero : XlKTop 0 where
  at_ := by rw [xlK_zero, zero_add]; exact xl_at_G
  cohR := fun _ h => absurd h (not_lt.2 zero_le)
  cohg := fun _ h => absurd h (not_lt.2 zero_le)

theorem xlKTop_succ {ν : Ordinal.{0}} (hν : ν + 1 < Om1) (H : XlKInv (ν + 1) xlK) : XlKTop (ν + 1) := by
  have hat : XlAt (ν + 1) (xlK ν) := H.at_ ν (lt_add_one ν)
  have e : xlK (ν + 1) = xlTU (xlSt_spec hν) (xl_start_of_at le_add_self hν hat) := by
    rw [xlK_succ]; exact xlLT_eq le_add_self hν hat
  refine ⟨?_, fun β hβ c x hc => ?_, fun β hβ c hc => ?_⟩
  · rw [e]; exact xl_at_top le_add_self hν hat
  · have hβν : β ≤ ν := Order.lt_add_one_iff.1 hβ
    have hcν : c < (xlK ν).B := hc.trans_le (xl_B_le hβν (H.at_ β (lt_of_le_of_lt hβν (lt_add_one ν))) hat)
    rw [e, xlTU_R0 _ _ hcν]
    exact H.cohR β ν hβν (lt_add_one ν) c x hc
  · have hβν : β ≤ ν := Order.lt_add_one_iff.1 hβ
    have hcν : c < (xlK ν).B := hc.trans_le (xl_B_le hβν (H.at_ β (lt_of_le_of_lt hβν (lt_add_one ν))) hat)
    rw [e, xlTU_g0 _ _ hcν]
    exact H.cohg β ν hβν (lt_add_one ν) c hc

theorem xlKTop_lim {l : Ordinal.{0}} (hl : IsSuccLimit l) (hl1 : l < Om1) (H : XlKInv l xlK) : XlKTop l := by
  have Hx : XlKInv l (xlKExt l fun β _ => xlK β) := H.congr fun β h => xlKExt_eq h
  obtain ⟨C, hC⟩ : ∃ C, C = xlKCh hl hl1 (xlKExt l fun β _ => xlK β) Hx := ⟨_, rfl⟩
  have hCat : XlAt l C.U := by rw [hC]; exact xlKCh_at hl hl1 _ Hx
  have e : xlK l = xlTU (xlSt_spec hl1) (xl_start_of_at (xl_one_le_l hl) hl1 hCat) := by
    rw [xlK_limit hl]; unfold xlKLim; rw [dif_pos ⟨hl1, Hx⟩, ← hC]
    exact xlLT_eq (xl_one_le_l hl) hl1 hCat
  have hD : ∀ k, C.D k = xlK (heFs l k) := fun k => by
    rw [hC]; exact xlKExt_eq (xl_fs_lt hl hl1 k)
  refine ⟨?_, fun β hβ c x hc => ?_, fun β hβ c hc => ?_⟩
  · rw [e]; exact xl_at_top (xl_one_le_l hl) hl1 hCat
  · obtain ⟨k, hk⟩ := heFs_cof hl (xl_lOm hl1) β hβ
    have hc' : c < (C.D k).B := by
      rw [hD]; exact hc.trans_le (xl_B_le hk.le (H.at_ β hβ) (H.at_ _ (xl_fs_lt hl hl1 k)))
    have hcU : c < C.U.B := hc'.trans (C.B_lt k)
    rw [e, xlTU_R0 _ _ hcU, C.U_R hc' x, hD]
    exact H.cohR β _ hk.le (xl_fs_lt hl hl1 k) c x hc
  · obtain ⟨k, hk⟩ := heFs_cof hl (xl_lOm hl1) β hβ
    have hc' : c < (C.D k).B := by
      rw [hD]; exact hc.trans_le (xl_B_le hk.le (H.at_ β hβ) (H.at_ _ (xl_fs_lt hl hl1 k)))
    have hcU : c < C.U.B := hc'.trans (C.B_lt k)
    rw [e, xlTU_g0 _ _ hcU, C.U_g hc', hD]
    exact H.cohg β _ hk.le (xl_fs_lt hl hl1 k) c hc

/-- **THE INVARIANT AT EVERY `κ < Ω₁`** (one induction; the coherence is carried along). -/
theorem xlK_inv : ∀ ν : Ordinal.{0}, ν < Om1 → XlKInv (ν + 1) xlK := by
  intro ν
  induction ν using Ordinal.limitRecOn with
  | zero => intro _; exact xlKInv_succ (xlKInv_zero xlK) xlKTop_zero
  | add_one μ ih =>
    intro hν
    have H := ih ((lt_add_one μ).trans hν)
    exact xlKInv_succ H (xlKTop_succ hν H)
  | limit l hl ih =>
    intro hν
    have H := xlKInv_lim (fun β hβ => ih β hβ (hβ.trans hν))
    exact xlKInv_succ H (xlKTop_lim hl hν H)

section Main

variable {κ : Ordinal.{0}} (hκ : κ < Om1)
include hκ

/-- **`xlK κ` IS A SYSTEM AT `φ(G + κ + 1, 0)`** (the top of the level `G + κ`). -/
theorem xlK_at : XlAt (κ + 1) (xlK κ) := (xlK_inv κ hκ).at_ κ (lt_add_one κ)

theorem xlK_B : (xlK κ).B = veblen (gcG 0 + (κ + 1)) 0 := (xlK_at hκ).B

theorem xlK_γ : (xlK κ).γ ≤ κ + 1 := (xlK_at hκ).γ_le

end Main

/-- **Later systems keep the readings and gates of earlier ones.** -/
theorem xlK_ext {β γ : Ordinal.{0}} (hβγ : β ≤ γ) (hγ : γ < Om1) {c : Ordinal.{0}} (hc : c < (xlK β).B)
    (x : Ordinal.{0}) : (xlK γ).R c x = (xlK β).R c x ∧ (xlK γ).g c = (xlK β).g c :=
  ⟨(xlK_inv γ hγ).cohR β γ hβγ (lt_add_one γ) c x hc, (xlK_inv γ hγ).cohg β γ hβγ (lt_add_one γ) c hc⟩

end Googology.Trans.PoR.InaccPsi.R2.Xl

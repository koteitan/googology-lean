import Googology.Trans.PoR.InaccPsi.R2.XpBand

/-!
# XpKRec: THE BOTTOMS `φ(L + κ, 0)` OF A GENERAL BAND FOR EVERY `κ < Ω₁`, BY ONE RECURSION ON `κ`

Given a band datum `B` and a system `U₀` at the bottom `φ(L, 0)` (`XpAt B.K.Λ 0 U₀`), one recursion `xpK B U₀ κ`:
`xpK 0 = U₀`, `xpK (κ+1)` = the top of the level `L + κ` over `xpK κ` (`Xp.xp_at_top`), `xpK λ` = the gated
`ω`-chain union of the `xpK (heFs λ k)` (`xpCh`: bound `φ(L + λ, 0)`, gate `max λ g`).

* `XpInv` (the invariant), `xpCh`, `xpCh_at`, `xpK`, `xpK_inv` (**THE INVARIANT AT EVERY `κ < Ω₁`**), `xpK_at`,
  `xpK_ext` (later systems extend earlier ones), `xpK_small` (**SMALL**: a code of `xpK ν` with gate below an
  `ε`-number `σ` lies in some `xpK μ`, `μ < σ`).

No new axiom.  New definitions: `xpLT`, `XpInv`, `xpCh`, `xpExt`, `xpKLim`, `xpK`, `XpKTop`.
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

open Googology.Trans.PoR.InaccPsi.R2.Ho

open Googology.Trans.PoR.InaccPsi.R2.Xl
open Googology.Trans.PoR.InaccPsi.R2.Xp

namespace Googology.Trans.PoR.InaccPsi.R2.Xp

variable (B : XpBd)

/-- The top of the level `L + κ` over a system at its bottom (when it is one). -/
noncomputable def xpLT (κ : Ordinal.{0}) (U : HgVD) : HgVD := by
  classical
  exact if h : κ < Om1 ∧ XpAt B.K.Λ κ U then xlTU (xpSt_spec B.toXpBd0 h.1) (xp_start_of_at B.toXpBd0 h.1 h.2) else U

theorem xpLT_eq {κ : Ordinal.{0}} (hκ : κ < Om1) {U : HgVD} (hU : XpAt B.K.Λ κ U) :
    xpLT B κ U = xlTU (xpSt_spec B.toXpBd0 hκ) (xp_start_of_at B.toXpBd0 hκ hU) := by
  unfold xpLT; rw [dif_pos ⟨hκ, hU⟩]

/-- **The invariant below `λ`**: each member `F μ` is a system at `φ(L + μ, 0)`; coherence. -/
structure XpInv (l : Ordinal.{0}) (F : Ordinal.{0} → HgVD) : Prop where
  at_ : ∀ μ, μ < l → XpAt B.K.Λ μ (F μ)
  cohR : ∀ β γ, β ≤ γ → γ < l → ∀ c x, c < (F β).B → (F γ).R c x = (F β).R c x
  cohg : ∀ β γ, β ≤ γ → γ < l → ∀ c, c < (F β).B → (F γ).g c = (F β).g c

variable {B}

theorem XpInv.congr {l : Ordinal.{0}} {F G : Ordinal.{0} → HgVD} (H : XpInv B l F)
    (hFG : ∀ β, β < l → G β = F β) : XpInv B l G where
  at_ := fun μ h => by rw [hFG μ h]; exact H.at_ μ h
  cohR := fun β γ hβγ h c x hc => by
    rw [hFG β (lt_of_le_of_lt hβγ h)] at hc ⊢
    rw [hFG γ h]; exact H.cohR β γ hβγ h c x hc
  cohg := fun β γ hβγ h c hc => by
    rw [hFG β (lt_of_le_of_lt hβγ h)] at hc ⊢
    rw [hFG γ h]; exact H.cohg β γ hβγ h c hc

theorem xp_B_le {Λ : HnLv} {β γ : Ordinal.{0}} (hβγ : β ≤ γ) {U V : HgVD} (hU : XpAt Λ β U) (hV : XpAt Λ γ V) :
    U.B ≤ V.B := by
  rw [hU.B, hV.B]
  exact veblen_zero_le_veblen_zero.2 ((add_le_add_iff_left _).2 hβγ)

/-! ## The union at a limit level -/

section Lim

variable {l : Ordinal.{0}} (hl : IsSuccLimit l) (hl1 : l < Om1)

include hl hl1 in
theorem xp_fs_lt (k : ℕ) : heFs l k < l := heFs_lt hl (xl_lOm hl1) k

theorem xp_GQl (B : XpBd) : gcG 0 < veblen (B.K.Λ.L + l) 0 :=
  B.G_lt.trans_le (le_self_add.trans (left_le_veblen _ 0))

theorem xp_glA_l (B : XpBd) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : B.K.Λ.g < x) (hlx : l < x) :
    glA (B.K.Λ.l x + l) 0 x = veblen (B.K.Λ.l x + l) 0 :=
  xp_glA B.toXpBd0 hx hx1 hg hlx 0 (hcN_E _ _).pos

variable (F : Ordinal.{0} → HgVD) (H : XpInv B l F)

/-- **THE GATED `ω`-CHAIN AT A LIMIT LEVEL `λ < Ω₁`**: the members `F (heFs λ k)`, bound `φ(L + λ, 0)`, gate
`max λ g`. -/
noncomputable def xpCh : HgfCh where
  D := fun k => F (heFs l k)
  B := veblen (B.K.Λ.L + l) 0
  b := fun x => veblen (B.K.Λ.l x + l) 0
  γ := max l B.K.Λ.g
  Zo := xpZ
  γ_lt := max_lt hl1 B.K.Λ.g_lt
  γ0 := fun k => (H.at_ _ (xp_fs_lt hl hl1 k)).γ_le.trans (max_le_max (xp_fs_lt hl hl1 k).le le_rfl)
  γ_cl := fun _ hZ hZ1 h => by
    have hs : veblen (B.K.Λ.L + l) 0 < veblen (B.K.Λ.L + l) (0 + 1) :=
      (isNormal_veblen _).strictMono (show (0 : Ordinal.{0}) < 0 + 1 by rw [zero_add]; exact zero_lt_one)
    exact max_lt (hnv_cl_gate B.K.Λ hl1 hZ hZ1 veblen_pos (xp_GQl (l := l) B) h le_rfl hs)
      (hnv_cl_g B.K.Λ hl1 hZ hZ1 veblen_pos (xp_GQl (l := l) B) h le_rfl hs)
  B_mono := fun k => xp_B_le (heFs_mono hl (xl_lOm hl1) k).le (H.at_ _ (xp_fs_lt hl hl1 k))
    (H.at_ _ (xp_fs_lt hl hl1 (k + 1)))
  B_lt := fun k => by
    rw [(H.at_ _ (xp_fs_lt hl hl1 k)).B]
    exact veblen_zero_lt_veblen_zero.2 ((add_lt_add_iff_left _).2 (xp_fs_lt hl hl1 k))
  B_cof := fun c hc => by
    obtain ⟨a, ha, hca⟩ := wx_veb_lim_cof0 (isSuccLimit_add _ hl) hc
    obtain ⟨d, hd, had⟩ := (lt_add_iff hl.bot_lt.ne').1 ha
    obtain ⟨k, hk⟩ := heFs_cof hl (xl_lOm hl1) d hd
    refine ⟨k, ?_⟩
    rw [(H.at_ _ (xp_fs_lt hl hl1 k)).B]
    exact hca.trans_le (veblen_zero_le_veblen_zero.2 (had.trans ((add_le_add_iff_left _).2 hk.le)))
  R_ext := fun k c x hc => H.cohR _ _ (heFs_mono hl (xl_lOm hl1) k).le (xp_fs_lt hl hl1 (k + 1)) c x hc
  g_ext := fun k c hc => H.cohg _ _ (heFs_mono hl (xl_lOm hl1) k).le (xp_fs_lt hl hl1 (k + 1)) c hc
  B_lt1 := by
    have hlt : B.K.Λ.L + l < gcG 1 := (lt_add_one _).trans (xp_L1_lt B.K.Λ hl1)
    have h := (isNormal_veblen (B.K.Λ.L + l)).strictMono (gcG_SC 1).1
    rwa [gn_veb_fix (gcG_SC 1) hlt] at h
  B_fix := veblen_veblen_of_lt ((wh_one_lt_Om1.trans_le B.K.Λ.OL).trans_le le_self_add) 0
  B_mem := fun S _ _ ha hb => CSet.phi_mem
    (hnv_L_mem B.K.Λ S ha ((le_max_right _ _).trans_lt hb) ((le_max_left _ _).trans_lt hb)) (CSet.zero_mem _ _)
  b_ge := fun k x hx hx1 hγ => by
    rw [(H.at_ _ (xp_fs_lt hl hl1 k)).b x hx hx1 ((max_le_max (xp_fs_lt hl hl1 k).le le_rfl).trans_lt hγ)]
    exact veblen_zero_le_veblen_zero.2 ((add_le_add_iff_left _).2 (xp_fs_lt hl hl1 k).le)
  b_cof := fun x hx hx1 hγ ν hν => by
    obtain ⟨a, ha, hνa⟩ := wx_veb_lim_cof0 (isSuccLimit_add _ hl) hν
    obtain ⟨d, hd, had⟩ := (lt_add_iff hl.bot_lt.ne').1 ha
    obtain ⟨k, hk⟩ := heFs_cof hl (xl_lOm hl1) d hd
    refine ⟨k, ?_⟩
    rw [(H.at_ _ (xp_fs_lt hl hl1 k)).b x hx hx1 ((max_le_max (xp_fs_lt hl hl1 k).le le_rfl).trans_lt hγ)]
    exact hνa.trans_le (veblen_zero_le_veblen_zero.2 (had.trans ((add_le_add_iff_left _).2 hk.le)))
  b_fix := fun x hx hx1 _ => veblen_veblen_of_lt ((wo_one_lt_inE hx).trans_le (hnv_xl B.K.Λ hx hx1)) 0
  b_gt := fun x hx hx1 hγ => (hnv_xl B.K.Λ hx hx1).trans_lt
    (xp_lt_veb0 B.toXpBd0 hx hx1 (max_lt_iff.1 hγ).2 (max_lt_iff.1 hγ).1)
  b_lt := fun x hx hx1 hγ => (xp_veb_lt_Z B hx hx1 (max_lt_iff.1 hγ).2 (max_lt_iff.1 hγ).1).trans (xpZ_G1 hx hx1)
  b_pi := fun σ ρ hB hγ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have h0σ : (0 : Ordinal.{0}) < σ := hB.1.pos
    have hlσ := (max_lt_iff.1 hγ).1
    have hgσ := (max_lt_iff.1 hγ).2
    have h := hnv_glA_pi B.K.Λ (ν := l) hB hgσ hlσ (mem_TB_of_lt hB h0σ) (gm1_facts hB.2.1 hρ1).2.2.2.pos
    rw [pi_lt hB h0σ, xp_glA_l (l := l) B hB.2.1 hρ1 (hgσ.trans hB.2.2.1) (hlσ.trans hB.2.2.1),
      xp_glA_l (l := l) B hB.1 hσ1 hgσ hlσ] at h
    exact h
  Z_low := fun k x hx hx1 _ => by
    rw [(H.at_ _ (xp_fs_lt hl hl1 k)).Z x hx hx1]
    split_ifs with h
    · exact (hb_evZ_lt_fix2 (xpZ_fix x) (xp_veb_lt_Z B hx hx1 (max_lt_iff.1 h).2 (max_lt_iff.1 h).1)).le
    · exact le_rfl
  Zo_fix := xpZ_fix1
  Zo_G1 := fun _ hx hx1 => xpZ_G1 hx hx1

/-- **THE UNION AT A LIMIT LEVEL `λ` IS A SYSTEM AT `φ(L + λ, 0)`.** -/
theorem xpCh_at : XpAt B.K.Λ l (xpCh hl hl1 F H).U where
  B := rfl
  ix := rfl
  γ := fun _ _ _ => Iff.rfl
  b := fun _ _ _ _ => rfl
  γ_le := le_rfl
  Z := fun x _ _ => (xpCh hl hl1 F H).U_Z x

end Lim

/-! ## The recursion -/

variable (B) (U0 : HgVD)

/-- The family of the earlier values, extended by `U₀`. -/
noncomputable def xpExt (l : Ordinal.{0}) (IH : ∀ β, β < l → HgVD) (β : Ordinal.{0}) : HgVD :=
  if h : β < l then IH β h else U0

open Classical in
/-- The limit step: the union (when the invariant holds; it always does). -/
noncomputable def xpKLim (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ β, β < l → HgVD) : HgVD :=
  if H : l < Om1 ∧ XpInv B l (xpExt U0 l IH) then (xpCh hl H.1 (xpExt U0 l IH) H.2).U else U0

/-- **THE RECURSION**: `xpK B U₀ κ` is the system at the bottom `φ(L + κ, 0)`. -/
noncomputable def xpK (κ : Ordinal.{0}) : HgVD :=
  Ordinal.limitRecOn (motive := fun _ => HgVD) κ U0 (fun κ U => xpLT B κ U) (xpKLim B U0)

theorem xpK_zero : xpK B U0 0 = U0 := by unfold xpK; rw [Ordinal.limitRecOn_zero]

theorem xpK_succ (κ : Ordinal.{0}) : xpK B U0 (κ + 1) = xpLT B κ (xpK B U0 κ) := by
  unfold xpK; rw [Ordinal.limitRecOn_add_one]

theorem xpK_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) :
    xpK B U0 l = xpKLim B U0 l hl (fun β _ => xpK B U0 β) := by
  unfold xpK; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem xpExt_eq {l β : Ordinal.{0}} (h : β < l) : xpExt U0 l (fun β _ => xpK B U0 β) β = xpK B U0 β := by
  unfold xpExt; rw [dif_pos h]

theorem xpInv_zero (F : Ordinal.{0} → HgVD) : XpInv B 0 F where
  at_ := fun _ h => absurd h (not_lt.2 zero_le)
  cohR := fun _ _ _ h => absurd h (not_lt.2 zero_le)
  cohg := fun _ _ _ h => absurd h (not_lt.2 zero_le)

/-- The new facts at the top `ν`. -/
structure XpKTop (ν : Ordinal.{0}) : Prop where
  at_ : XpAt B.K.Λ ν (xpK B U0 ν)
  cohR : ∀ β, β < ν → ∀ c x, c < (xpK B U0 β).B → (xpK B U0 ν).R c x = (xpK B U0 β).R c x
  cohg : ∀ β, β < ν → ∀ c, c < (xpK B U0 β).B → (xpK B U0 ν).g c = (xpK B U0 β).g c

variable {B U0}

theorem xpInv_succ {ν : Ordinal.{0}} (H : XpInv B ν (xpK B U0)) (T : XpKTop B U0 ν) :
    XpInv B (ν + 1) (xpK B U0) where
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

theorem xpInv_lim {l : Ordinal.{0}} (IH : ∀ β, β < l → XpInv B (β + 1) (xpK B U0)) : XpInv B l (xpK B U0) where
  at_ := fun β h => (IH β h).at_ β (lt_add_one β)
  cohR := fun β γ hβγ h => (IH γ h).cohR β γ hβγ (lt_add_one γ)
  cohg := fun β γ hβγ h => (IH γ h).cohg β γ hβγ (lt_add_one γ)

theorem xpKTop_zero (hU0 : XpAt B.K.Λ 0 U0) : XpKTop B U0 0 where
  at_ := by rw [xpK_zero]; exact hU0
  cohR := fun _ h => absurd h (not_lt.2 zero_le)
  cohg := fun _ h => absurd h (not_lt.2 zero_le)

theorem xpK_succ_eq {ν : Ordinal.{0}} (hν : ν < Om1) (hat : XpAt B.K.Λ ν (xpK B U0 ν)) :
    xpK B U0 (ν + 1) = xlTU (xpSt_spec B.toXpBd0 hν) (xp_start_of_at B.toXpBd0 hν hat) := by
  rw [xpK_succ]; exact xpLT_eq B hν hat

theorem xpKTop_succ {ν : Ordinal.{0}} (hν : ν + 1 < Om1) (H : XpInv B (ν + 1) (xpK B U0)) : XpKTop B U0 (ν + 1) := by
  have hν' : ν < Om1 := (lt_add_one ν).trans hν
  have hat : XpAt B.K.Λ ν (xpK B U0 ν) := H.at_ ν (lt_add_one ν)
  have e := xpK_succ_eq hν' hat
  refine ⟨?_, fun β hβ c x hc => ?_, fun β hβ c hc => ?_⟩
  · rw [e]; exact xp_at_top B.toXpBd0 hν' hat
  · have hβν : β ≤ ν := Order.lt_add_one_iff.1 hβ
    have hcν : c < (xpK B U0 ν).B := hc.trans_le (xp_B_le hβν (H.at_ β (lt_of_le_of_lt hβν (lt_add_one ν))) hat)
    rw [e, xlTU_R0 _ _ hcν]
    exact H.cohR β ν hβν (lt_add_one ν) c x hc
  · have hβν : β ≤ ν := Order.lt_add_one_iff.1 hβ
    have hcν : c < (xpK B U0 ν).B := hc.trans_le (xp_B_le hβν (H.at_ β (lt_of_le_of_lt hβν (lt_add_one ν))) hat)
    rw [e, xlTU_g0 _ _ hcν]
    exact H.cohg β ν hβν (lt_add_one ν) c hc

/-- The shape of `xpK λ` at a limit: the union of a chain of the `xpK (heFs λ k)`. -/
theorem xpK_lim_eq {l : Ordinal.{0}} (hl : IsSuccLimit l) (hl1 : l < Om1) (H : XpInv B l (xpK B U0)) :
    ∃ (C : HgfCh), XpAt B.K.Λ l C.U ∧ (∀ k, C.D k = xpK B U0 (heFs l k)) ∧ xpK B U0 l = C.U := by
  have Hx : XpInv B l (xpExt U0 l fun β _ => xpK B U0 β) := H.congr fun β h => xpExt_eq B U0 h
  refine ⟨xpCh hl hl1 (xpExt U0 l fun β _ => xpK B U0 β) Hx, xpCh_at hl hl1 _ Hx,
    fun k => xpExt_eq B U0 (xp_fs_lt hl hl1 k), ?_⟩
  rw [xpK_limit B U0 hl]; unfold xpKLim; rw [dif_pos ⟨hl1, Hx⟩]

theorem xpKTop_lim {l : Ordinal.{0}} (hl : IsSuccLimit l) (hl1 : l < Om1) (H : XpInv B l (xpK B U0)) :
    XpKTop B U0 l := by
  obtain ⟨C, hCat, hD, e⟩ := xpK_lim_eq hl hl1 H
  refine ⟨by rw [e]; exact hCat, fun β hβ c x hc => ?_, fun β hβ c hc => ?_⟩
  · obtain ⟨k, hk⟩ := heFs_cof hl (xl_lOm hl1) β hβ
    have hc' : c < (C.D k).B := by
      rw [hD]; exact hc.trans_le (xp_B_le hk.le (H.at_ β hβ) (H.at_ _ (xp_fs_lt hl hl1 k)))
    rw [e, C.U_R hc' x, hD]
    exact H.cohR β _ hk.le (xp_fs_lt hl hl1 k) c x hc
  · obtain ⟨k, hk⟩ := heFs_cof hl (xl_lOm hl1) β hβ
    have hc' : c < (C.D k).B := by
      rw [hD]; exact hc.trans_le (xp_B_le hk.le (H.at_ β hβ) (H.at_ _ (xp_fs_lt hl hl1 k)))
    rw [e, C.U_g hc', hD]
    exact H.cohg β _ hk.le (xp_fs_lt hl hl1 k) c hc

/-- **THE INVARIANT AT EVERY `κ < Ω₁`** (one induction; the coherence is carried along). -/
theorem xpK_inv (hU0 : XpAt B.K.Λ 0 U0) : ∀ ν : Ordinal.{0}, ν < Om1 → XpInv B (ν + 1) (xpK B U0) := by
  intro ν
  induction ν using Ordinal.limitRecOn with
  | zero => intro _; exact xpInv_succ (xpInv_zero B _) (xpKTop_zero hU0)
  | add_one μ ih =>
    intro hν
    have H := ih ((lt_add_one μ).trans hν)
    exact xpInv_succ H (xpKTop_succ hν H)
  | limit l hl ih =>
    intro hν
    have H := xpInv_lim (fun β hβ => ih β hβ (hβ.trans hν))
    exact xpInv_succ H (xpKTop_lim hl hν H)

section Main

variable (hU0 : XpAt B.K.Λ 0 U0)
include hU0

/-- **`xpK B U₀ κ` IS A SYSTEM AT `φ(L + κ, 0)`** for every `κ < Ω₁`. -/
theorem xpK_at {κ : Ordinal.{0}} (hκ : κ < Om1) : XpAt B.K.Λ κ (xpK B U0 κ) := (xpK_inv hU0 κ hκ).at_ κ (lt_add_one κ)

/-- **Later systems keep the readings and gates of earlier ones.** -/
theorem xpK_ext {β γ : Ordinal.{0}} (hβγ : β ≤ γ) (hγ : γ < Om1) {c : Ordinal.{0}} (hc : c < (xpK B U0 β).B)
    (x : Ordinal.{0}) : (xpK B U0 γ).R c x = (xpK B U0 β).R c x ∧ (xpK B U0 γ).g c = (xpK B U0 β).g c :=
  ⟨(xpK_inv hU0 γ hγ).cohR β γ hβγ (lt_add_one γ) c x hc, (xpK_inv hU0 γ hγ).cohg β γ hβγ (lt_add_one γ) c hc⟩

/-- **SMALL**: a code of `xpK ν` with gate below an `ε`-number `σ` lies in some `xpK μ`, `μ < σ`. -/
theorem xpK_small : ∀ ν, ν < Om1 → ∀ c, c < (xpK B U0 ν).B → ∀ σ, InE σ → σ < Om1 → (xpK B U0 ν).g c < σ →
    ∃ μ, μ < σ ∧ c < (xpK B U0 μ).B := by
  intro ν
  induction ν using WellFoundedLT.induction with
  | ind ν IH =>
  intro hν c hc σ hσ hσ1 hg
  by_cases hνσ : ν < σ
  · exact ⟨ν, hνσ, hc⟩
  rcases zero_or_succ_or_isSuccLimit ν with h0 | ⟨μ, hμ⟩ | hlim
  · exact absurd (by rw [h0]; exact hσ.pos) hνσ
  · have hμ' : ν = μ + 1 := by rw [← hμ, Order.succ_eq_add_one]
    subst hμ'
    have hμ1 : μ < Om1 := (lt_add_one μ).trans hν
    by_cases hcμ : c < (xpK B U0 μ).B
    · rw [(xpK_ext hU0 (le_add_right le_rfl) hν hcμ 0).2] at hg
      exact IH μ (lt_add_one μ) hμ1 c hcμ σ hσ hσ1 hg
    · exfalso
      have e := xpK_succ_eq hμ1 (xpK_at hU0 hμ1)
      rw [e] at hc hg
      have h := xlT_high _ _ hc (not_lt.1 hcμ) hσ hσ1 hg
      rw [xpBK_γN] at h
      exact hνσ ((ev_isSuccLimit_of_inE hσ).add_one_lt (max_lt_iff.1 h).1)
  · obtain ⟨C, -, hD, e⟩ := xpK_lim_eq hlim hν (xpInv_lim (fun β hβ => xpK_inv hU0 β (hβ.trans hν)))
    rw [e] at hc hg
    obtain ⟨k, hk⟩ := C.B_cof c hc
    have hk1 : heFs ν k < ν := xp_fs_lt hlim hν k
    rw [C.U_g hk, hD] at hg
    rw [hD] at hk
    exact IH _ hk1 (hk1.trans hν) c hk σ hσ hσ1 hg

/-- **HIGH CODES**: a code of `xpK ν` at or above `U₀.B` with gate below an `ε`-number `σ` forces `g < σ`. -/
theorem xpK_high : ∀ ν, ν < Om1 → ∀ c, U0.B ≤ c → c < (xpK B U0 ν).B → ∀ σ, InE σ → σ < Om1 →
    (xpK B U0 ν).g c < σ → B.K.Λ.g < σ := by
  intro ν
  induction ν using WellFoundedLT.induction with
  | ind ν IH =>
  intro hν c hc0 hc σ hσ hσ1 hg
  rcases zero_or_succ_or_isSuccLimit ν with h0 | ⟨μ, hμ⟩ | hlim
  · subst h0; rw [xpK_zero] at hc; exact absurd hc (not_lt.2 hc0)
  · have hμ' : ν = μ + 1 := by rw [← hμ, Order.succ_eq_add_one]
    subst hμ'
    have hμ1 : μ < Om1 := (lt_add_one μ).trans hν
    by_cases hcμ : c < (xpK B U0 μ).B
    · rw [(xpK_ext hU0 (le_add_right le_rfl) hν hcμ 0).2] at hg
      exact IH μ (lt_add_one μ) hμ1 c hc0 hcμ σ hσ hσ1 hg
    · have e := xpK_succ_eq hμ1 (xpK_at hU0 hμ1)
      rw [e] at hc hg
      have h := xlT_high _ _ hc (not_lt.1 hcμ) hσ hσ1 hg
      rw [xpBK_γN] at h
      exact (max_lt_iff.1 h).2
  · obtain ⟨C, -, hD, e⟩ := xpK_lim_eq hlim hν (xpInv_lim (fun β hβ => xpK_inv hU0 β (hβ.trans hν)))
    rw [e] at hc hg
    obtain ⟨k, hk⟩ := C.B_cof c hc
    have hk1 : heFs ν k < ν := xp_fs_lt hlim hν k
    rw [C.U_g hk, hD] at hg
    rw [hD] at hk
    exact IH _ hk1 (hk1.trans hν) c hc0 hk σ hσ hσ1 hg

end Main

end Googology.Trans.PoR.InaccPsi.R2.Xp

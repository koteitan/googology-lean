import Googology.Trans.PoR.InaccPsi.R2.XfQ

/-!
# XfRec: THE OFFSET RECURSION OF THE LEVEL `G` FROM THE BOTTOM: A START OF `φ(G, ν)` FOR EVERY `1 ≤ ν < Γ₀`

The offsets of the level `G` start at `0` (`φ(G, 0) = G`), not at a base `F + 1` as in `Hn.HnVRec`.  One recursion
`xfV ν` (`ν < Γ₀`): `Xf.xfV1` at `0`, the package at `G` (`Xf.xfPk`) at `ν + 1`, the gated `ω`-chain union (gate
`λ`) along the fundamental sequence `He.heFs λ` at a limit `λ` (nothing depends on the choice of the sequence).  The
invariant (`XfInv`, `xf_inv`): `xfV ν` starts the pseudo-base `φ(G, 1 + ν)` (`Xf.xfQ`, gate `1 + ν`), its gate is
`≤ 1 + ν`, and later systems keep the readings and gates of earlier ones.

* `xfQt` (the pseudo-base `φ(G, o)` for every `o`, `Xf.xfQ` when `1 ≤ o < Γ₀`), `XfInv`, `xfChL` (**THE UNION AT A
  LIMIT `λ < Γ₀`**), `xfV` (**THE RECURSION**), `xf_inv` (**THE INVARIANT AT EVERY `ν < Γ₀`**);
* `xfV_start` (**`xfV ν` STARTS `φ(G, 1+ν)`**), `xfV_B` (`B = φ(G, 1+ν)`), `xfV_γ` (gate `≤ 1+ν`), `xfV_ext`,
  `xfV_hgU`.

No new axiom.  New definitions: `xfQt`, `XfInv`, `xfChL`, `xfExt`, `xfLimD`, `xfStep`, `xfV`, `XfTop`.
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
open Googology.Trans.PoR.InaccPsi.R2.He

namespace Googology.Trans.PoR.InaccPsi.R2.Xf

open Classical in
/-- The pseudo-base `φ(G, o)` for every `o` (`Xf.xfQ` when `1 ≤ o < Γ₀`, else `φ(G, 1)`). -/
noncomputable def xfQt (o : Ordinal.{0}) : HnVQ xfLv 0 :=
  if h : 1 ≤ o ∧ o < gamma 0 then xfQ o h.1 h.2 else xfQ 1 le_rfl xf_one_lt_gam0

theorem xfQt_eq {o : Ordinal.{0}} (h1 : 1 ≤ o) (hε : o < gamma 0) : xfQt o = xfQ o h1 hε := by
  unfold xfQt; rw [dif_pos ⟨h1, hε⟩]

theorem xf_one_add_lt {ν : Ordinal.{0}} (hν : ν < gamma 0) : 1 + ν < gamma 0 := gc_one_add_lt xf_gam0_lim hν

theorem xfQt_one_add {ν : Ordinal.{0}} (hν : ν < gamma 0) : xfQt (1 + ν) = xfQ (1 + ν) le_self_add (xf_one_add_lt hν) :=
  xfQt_eq le_self_add (xf_one_add_lt hν)

/-! ## The invariant -/

/-- **The invariant of a family below `λ`**: each member starts `φ(G, 1+μ)` with gate `≤ 1+μ`; coherence. -/
structure XfInv (l : Ordinal.{0}) (F : Ordinal.{0} → HgVD) : Prop where
  st : ∀ μ, μ < l → HgSStart (hnVPB (xfQt (1 + μ))) (F μ)
  γ : ∀ μ, μ < l → (F μ).γ ≤ 1 + μ
  cohR : ∀ β γ, β ≤ γ → γ < l → ∀ c x, c < (F β).B → (F γ).R c x = (F β).R c x
  cohg : ∀ β γ, β ≤ γ → γ < l → ∀ c, c < (F β).B → (F γ).g c = (F β).g c

namespace XfInv

variable {l : Ordinal.{0}} {F : Ordinal.{0} → HgVD} (H : XfInv l F) (hlε : l ≤ gamma 0)
include H hlε

theorem start {μ : Ordinal.{0}} (h : μ < l) :
    HgSStart (hnVPB (xfQ (1 + μ) le_self_add (xf_one_add_lt (h.trans_le hlε)))) (F μ) := by
  have := H.st μ h; rwa [xfQt_one_add (h.trans_le hlε)] at this

theorem B_eq {μ : Ordinal.{0}} (h : μ < l) : (F μ).B = veblen (gcG 0) (1 + μ) := xf_start_B (H.start hlε h)

theorem b_eq {μ : Ordinal.{0}} (h : μ < l) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hμx : 1 + μ < x) :
    (F μ).b x = veblen (lgG x) (1 + μ) :=
  ((xf_start_iff _ _ _ _).1 (H.start hlε h)).2.2.1 x hx hx1 hμx

theorem Z_eq {μ : Ordinal.{0}} (h : μ < l) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    (F μ).Z x = if 1 + μ < x then evZ (veblen (lgG x) (1 + μ)) else wnZo x :=
  ((xf_start_iff _ _ _ _).1 (H.start hlε h)).2.2.2 x hx hx1

theorem B_le {β γ : Ordinal.{0}} (hβγ : β ≤ γ) (h : γ < l) : (F β).B ≤ (F γ).B := by
  rw [H.B_eq hlε (hβγ.trans_lt h), H.B_eq hlε h]
  exact (isNormal_veblen _).monotone (add_le_add le_rfl hβγ)

theorem B_lt {β γ : Ordinal.{0}} (hβγ : β < γ) (h : γ < l) : (F β).B < (F γ).B := by
  rw [H.B_eq hlε (hβγ.trans h), H.B_eq hlε h]
  exact (isNormal_veblen _).strictMono ((add_lt_add_iff_left 1).2 hβγ)

end XfInv

theorem XfInv.congr {l : Ordinal.{0}} {F G : Ordinal.{0} → HgVD} (H : XfInv l F) (hFG : ∀ β, β < l → G β = F β) :
    XfInv l G where
  st := fun μ h => by rw [hFG μ h]; exact H.st μ h
  γ := fun μ h => by rw [hFG μ h]; exact H.γ μ h
  cohR := fun β γ hβγ h c x hc => by
    rw [hFG β (lt_of_le_of_lt hβγ h)] at hc ⊢
    rw [hFG γ h]; exact H.cohR β γ hβγ h c x hc
  cohg := fun β γ hβγ h c hc => by
    rw [hFG β (lt_of_le_of_lt hβγ h)] at hc ⊢
    rw [hFG γ h]; exact H.cohg β γ hβγ h c hc

theorem xfInv_zero (F : Ordinal.{0} → HgVD) : XfInv 0 F where
  st := fun _ h => absurd h (not_lt.2 zero_le)
  γ := fun _ h => absurd h (not_lt.2 zero_le)
  cohR := fun _ _ _ h => absurd h (not_lt.2 zero_le)
  cohg := fun _ _ _ h => absurd h (not_lt.2 zero_le)

/-! ## The union at a limit -/

section Lim

theorem xf_one_le_lim {l : Ordinal.{0}} (hl : IsSuccLimit l) : (1 : Ordinal.{0}) ≤ l :=
  one_lt_omega0.le.trans (omega0_le_of_isSuccLimit hl)

theorem xf_one_add_lim {l : Ordinal.{0}} (hl : IsSuccLimit l) : 1 + l = l :=
  one_add_of_omega0_le (omega0_le_of_isSuccLimit hl)

theorem xf_lt_Om {l : Ordinal.{0}} (hl0 : l < gamma 0) : l < Om (1 : Ordinal.{0}) := by
  rw [← Br.Om1_eq]; exact hl0.trans xf_gam0_lt_Om1

theorem xf_fs_le {l : Ordinal.{0}} (hl : IsSuccLimit l) (hl0 : l < gamma 0) (k : ℕ) : 1 + heFs l k < l :=
  gc_one_add_lt hl (heFs_lt hl (xf_lt_Om hl0) k)

/-- **THE GATED `ω`-CHAIN AT A LIMIT `λ < Γ₀`**: the members `F (heFs λ k)`, bound `φ(G, λ)`, gate `λ`. -/
noncomputable def xfChL {l : Ordinal.{0}} (hl : IsSuccLimit l) (hl0 : l < gamma 0) (F : Ordinal.{0} → HgVD)
    (H : XfInv l F) : HgfCh where
  D := fun k => F (heFs l k)
  B := veblen (gcG 0) l
  b := fun x => veblen (lgG x) l
  γ := l
  Zo := wnZo
  γ_lt := hl0.trans xf_gam0_lt_Om1
  γ0 := fun k => (H.γ _ (heFs_lt hl (xf_lt_Om hl0) k)).trans (xf_fs_le hl hl0 k).le
  γ_cl := fun _ hZ _ _ => xf_lt_SC hl0 hZ
  B_mono := fun k => H.B_le hl0.le (heFs_mono hl (xf_lt_Om hl0) k).le (heFs_lt hl (xf_lt_Om hl0) (k + 1))
  B_lt := fun k => by
    rw [H.B_eq hl0.le (heFs_lt hl (xf_lt_Om hl0) k)]
    exact (isNormal_veblen _).strictMono (xf_fs_le hl hl0 k)
  B_cof := fun c hc => by
    obtain ⟨β, hβ, hcβ⟩ := ((isNormal_veblen (gcG 0)).lt_iff_exists_lt hl).1 hc
    obtain ⟨k, hk⟩ := heFs_cof hl (xf_lt_Om hl0) β hβ
    refine ⟨k, ?_⟩
    rw [H.B_eq hl0.le (heFs_lt hl (xf_lt_Om hl0) k)]
    exact hcβ.trans ((isNormal_veblen _).strictMono (hk.trans_le le_add_self))
  R_ext := fun k c x hc =>
    H.cohR _ _ (heFs_mono hl (xf_lt_Om hl0) k).le (heFs_lt hl (xf_lt_Om hl0) (k + 1)) c x hc
  g_ext := fun k c hc =>
    H.cohg _ _ (heFs_mono hl (xf_lt_Om hl0) k).le (heFs_lt hl (xf_lt_Om hl0) (k + 1)) c hc
  B_lt1 := xf_vG_lt1 (hl0.trans xf_gam0_lt_G1)
  B_fix := veblen_veblen_of_lt xf_one_lt_G _
  B_mem := fun S _ _ ha _ => CSet.phi_mem (gmS_G0_mem S ha) (gr_cst_mem ha _ l (hl0.trans xf_gam0_lt_gam1))
  b_ge := fun k x hx hx1 hγ => by
    rw [H.b_eq hl0.le (heFs_lt hl (xf_lt_Om hl0) k) hx hx1 ((xf_fs_le hl hl0 k).trans hγ)]
    exact (isNormal_veblen _).monotone (xf_fs_le hl hl0 k).le
  b_cof := fun x hx hx1 hγ ν hν => by
    obtain ⟨β, hβ, hνβ⟩ := ((isNormal_veblen (lgG x)).lt_iff_exists_lt hl).1 hν
    obtain ⟨k, hk⟩ := heFs_cof hl (xf_lt_Om hl0) β hβ
    refine ⟨k, ?_⟩
    rw [H.b_eq hl0.le (heFs_lt hl (xf_lt_Om hl0) k) hx hx1 ((xf_fs_le hl hl0 k).trans hγ)]
    exact hνβ.trans ((isNormal_veblen _).strictMono (hk.trans_le le_add_self))
  b_fix := fun x hx hx1 _ => veblen_veblen_of_lt (xf_one_lt_Gx hx hx1) _
  b_gt := fun x hx hx1 _ =>
    (lgG_facts hx hx1).2.1.trans (xf_Gx_lt_v hx hx1 (zero_lt_one.trans_le (xf_one_le_lim hl)))
  b_lt := fun x hx hx1 hγ => (xf_vGx_lt_Zo hx hx1 hγ).trans (wnZo_G1 hx hx1)
  b_pi := fun σ ρ hB hγ => xf_veb_pi hB (xf_one_le_lim hl) hγ
  Z_low := fun k x hx hx1 _ => by
    rw [H.Z_eq hl0.le (heFs_lt hl (xf_lt_Om hl0) k) hx hx1]
    split_ifs with h
    · exact (hb_evZ_lt_fix2 (wnZo_fix x) (xf_vGx_lt_Zo hx hx1 h)).le
    · exact le_rfl
  Zo_fix := fun x => hc_fix_down one_le_two (wnZo_fix x)
  Zo_G1 := fun x hx hx1 => wnZo_G1 hx hx1

/-- **THE UNION AT A LIMIT STARTS `φ(G, λ)`.** -/
theorem xfChL_start {l : Ordinal.{0}} (hl : IsSuccLimit l) (hl0 : l < gamma 0) (F : Ordinal.{0} → HgVD)
    (H : XfInv l F) : HgSStart (hnVPB (xfQt (1 + l))) (xfChL hl hl0 F H).U := by
  rw [xfQt_one_add hl0]
  refine (xf_start_iff _ _ _ _).2 ⟨?_, fun _ _ _ => ?_, fun x _ _ _ => ?_, fun x _ _ => ?_⟩
  · show veblen (gcG 0) l = _; rw [xf_one_add_lim hl]
  · show l < _ ↔ _; rw [xf_one_add_lim hl]
  · show veblen (lgG x) l = _; rw [xf_one_add_lim hl]
  · rw [HgfCh.U_Z]; show (if l < x then evZ (veblen (lgG x) l) else wnZo x) = _
    rw [xf_one_add_lim hl]

end Lim

/-! ## The recursion -/

/-- The successor step: the package at `G` at the pseudo-base `φ(G, 1+ν)` started at `U` (when `U` starts it). -/
noncomputable def xfStep (ν : Ordinal.{0}) (U : HgVD) : HgVD := by
  classical
  exact if h : HgSStart (hnVPB (xfQt (1 + ν))) U then xfPk.St0 (xfQt (1 + ν)) U h else U

/-- The family of the earlier values, extended by `xfV1`. -/
noncomputable def xfExt (l : Ordinal.{0}) (IH : ∀ β, β < l → HgVD) (β : Ordinal.{0}) : HgVD :=
  if h : β < l then IH β h else xfV1

open Classical in
/-- The limit step: the union when the invariant holds (it always does, `xf_inv`). -/
noncomputable def xfLimD (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ β, β < l → HgVD) : HgVD :=
  if H : l < gamma 0 ∧ XfInv l (xfExt l IH) then (xfChL hl H.1 (xfExt l IH) H.2).U else xfV1

/-- **THE RECURSION**: `xfV 0 = xfV1`, `xfV (ν+1)` the package at `G` over `xfV ν`, `xfV λ` the union. -/
noncomputable def xfV (ν : Ordinal.{0}) : HgVD :=
  Ordinal.limitRecOn (motive := fun _ => HgVD) ν xfV1 xfStep xfLimD

theorem xfV_zero : xfV 0 = xfV1 := by unfold xfV; rw [Ordinal.limitRecOn_zero]

theorem xfV_succ (ν : Ordinal.{0}) : xfV (ν + 1) = xfStep ν (xfV ν) := by
  unfold xfV; rw [Ordinal.limitRecOn_add_one]

theorem xfV_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) : xfV l = xfLimD l hl (fun β _ => xfV β) := by
  unfold xfV; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem xfExt_eq {l β : Ordinal.{0}} (h : β < l) : xfExt l (fun β _ => xfV β) β = xfV β := by
  unfold xfExt; rw [dif_pos h]

/-! ## The invariant at every `ν < Γ₀` -/

/-- The new facts at the top `ν`. -/
structure XfTop (ν : Ordinal.{0}) : Prop where
  st : HgSStart (hnVPB (xfQt (1 + ν))) (xfV ν)
  γ : (xfV ν).γ ≤ 1 + ν
  cohR : ∀ β, β < ν → ∀ c x, c < (xfV β).B → (xfV ν).R c x = (xfV β).R c x
  cohg : ∀ β, β < ν → ∀ c, c < (xfV β).B → (xfV ν).g c = (xfV β).g c

theorem xfInv_succ {ν : Ordinal.{0}} (H : XfInv ν xfV) (T : XfTop ν) : XfInv (ν + 1) xfV where
  st := fun β h => by
    rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
    · exact H.st β h'
    · exact T.st
  γ := fun β h => by
    rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
    · exact H.γ β h'
    · exact T.γ
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

theorem xfInv_lim {l : Ordinal.{0}} (IH : ∀ β, β < l → XfInv (β + 1) xfV) : XfInv l xfV where
  st := fun β h => (IH β h).st β (lt_add_one β)
  γ := fun β h => (IH β h).γ β (lt_add_one β)
  cohR := fun β γ hβγ h => (IH γ h).cohR β γ hβγ (lt_add_one γ)
  cohg := fun β γ hβγ h => (IH γ h).cohg β γ hβγ (lt_add_one γ)

theorem xfTop_zero : XfTop 0 where
  st := by rw [xfV_zero, add_zero, xfQt_eq le_rfl xf_one_lt_gam0]; exact xf_start1
  γ := by rw [xfV_zero, add_zero]; exact le_rfl
  cohR := fun _ h => absurd h (not_lt.2 zero_le)
  cohg := fun _ h => absurd h (not_lt.2 zero_le)

/-- **The successor step at `xfQt o`** (`1 ≤ o`, `o + 1 < Γ₀`): a start of `φ(G, o+1)`, gate `o`, extension. -/
theorem xf_succ_t (o : Ordinal.{0}) (h1 : 1 ≤ o) (hε1 : o + 1 < gamma 0) (U : HgVD)
    (h : HgSStart (hnVPB (xfQt o)) U) :
    HgSStart (hnVPB (xfQt (o + 1))) (xfPk.St0 (xfQt o) U h) ∧ (xfPk.St0 (xfQt o) U h).γ = o ∧
      ∀ c x, c < U.B → (xfPk.St0 (xfQt o) U h).R c x = U.R c x ∧ (xfPk.St0 (xfQt o) U h).g c = U.g c := by
  have hε : o < gamma 0 := (lt_add_one o).trans hε1
  revert h
  rw [xfQt_eq h1 hε, xfQt_eq (h1.trans le_self_add) hε1]
  intro h
  exact ⟨xf_start_succ o h1 hε hε1 U h, xf_succ_γ o h1 hε U h, fun c x hc => xf_succ_ext o h1 hε U h hc x⟩

theorem xfTop_succ {ν : Ordinal.{0}} (hν : ν + 1 < gamma 0) (H : XfInv (ν + 1) xfV) : XfTop (ν + 1) := by
  have hst : HgSStart (hnVPB (xfQt (1 + ν))) (xfV ν) := H.st ν (lt_add_one ν)
  have e : xfV (ν + 1) = xfPk.St0 (xfQt (1 + ν)) (xfV ν) hst := by
    rw [xfV_succ]; unfold xfStep; rw [dif_pos hst]
  have hε1 : 1 + ν + 1 < gamma 0 := by rw [add_assoc]; exact xf_one_add_lt hν
  obtain ⟨T1, T2, T3⟩ := xf_succ_t (1 + ν) le_self_add hε1 (xfV ν) hst
  refine ⟨?_, ?_, fun β hβ c x hc => ?_, fun β hβ c hc => ?_⟩
  · rw [e, ← add_assoc]; exact T1
  · rw [e, T2, ← add_assoc]; exact (lt_add_one _).le
  · have hβν : β ≤ ν := Order.lt_add_one_iff.1 hβ
    rw [e, (T3 c x (hc.trans_le (H.B_le hν.le hβν (lt_add_one ν)))).1]
    exact H.cohR β ν hβν (lt_add_one ν) c x hc
  · have hβν : β ≤ ν := Order.lt_add_one_iff.1 hβ
    rw [e, (T3 c 0 (hc.trans_le (H.B_le hν.le hβν (lt_add_one ν)))).2]
    exact H.cohg β ν hβν (lt_add_one ν) c hc

theorem xfTop_lim {l : Ordinal.{0}} (hl : IsSuccLimit l) (hl0 : l < gamma 0) (H : XfInv l xfV) : XfTop l := by
  have Hx : XfInv l (xfExt l fun β _ => xfV β) := H.congr fun β h => xfExt_eq h
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = xfChL hl hl0 (xfExt l fun β _ => xfV β) Hx := ⟨_, rfl⟩
  have e : xfV l = Q.U := by
    rw [xfV_limit hl, hQ]; unfold xfLimD; rw [dif_pos ⟨hl0, Hx⟩]
  have hD : ∀ k, Q.D k = xfV (heFs l k) := fun k => by
    rw [hQ]; exact xfExt_eq (heFs_lt hl (xf_lt_Om hl0) k)
  refine ⟨?_, ?_, fun β hβ c x hc => ?_, fun β hβ c hc => ?_⟩
  · rw [e, hQ]; exact xfChL_start hl hl0 _ Hx
  · rw [e, hQ]; show l ≤ 1 + l; exact le_add_self
  · obtain ⟨k, hk⟩ := heFs_cof hl (xf_lt_Om hl0) β hβ
    have hc' : c < (Q.D k).B := by rw [hD]; exact hc.trans (H.B_lt hl0.le hk (heFs_lt hl (xf_lt_Om hl0) k))
    rw [e, Q.U_R hc' x, hD]
    exact H.cohR β _ hk.le (heFs_lt hl (xf_lt_Om hl0) k) c x hc
  · obtain ⟨k, hk⟩ := heFs_cof hl (xf_lt_Om hl0) β hβ
    have hc' : c < (Q.D k).B := by rw [hD]; exact hc.trans (H.B_lt hl0.le hk (heFs_lt hl (xf_lt_Om hl0) k))
    rw [e, Q.U_g hc', hD]
    exact H.cohg β _ hk.le (heFs_lt hl (xf_lt_Om hl0) k) c hc

/-- **THE INVARIANT AT EVERY `ν < Γ₀`** (one induction; the coherence is carried along). -/
theorem xf_inv : ∀ ν : Ordinal.{0}, ν < gamma 0 → XfInv (ν + 1) xfV := by
  intro ν
  induction ν using Ordinal.limitRecOn with
  | zero => intro _; exact xfInv_succ (xfInv_zero xfV) xfTop_zero
  | add_one μ ih =>
    intro hν
    have H := ih ((lt_add_one μ).trans hν)
    exact xfInv_succ H (xfTop_succ hν H)
  | limit l hl ih =>
    intro hν
    have H := xfInv_lim (fun β hβ => ih β hβ (hβ.trans hν))
    exact xfInv_succ H (xfTop_lim hl hν H)

/-! ## The systems `xfV ν` -/

section Main

variable {ν : Ordinal.{0}} (hν : ν < gamma 0)
include hν

/-- **`xfV ν` STARTS THE PSEUDO-BASE `φ(G, 1+ν)`.** -/
theorem xfV_start : HgSStart (hnVPB (xfQ (1 + ν) le_self_add (xf_one_add_lt hν))) (xfV ν) :=
  (xf_inv ν hν).start (Order.add_one_le_of_lt hν) (lt_add_one ν)

theorem xfV_B : (xfV ν).B = veblen (gcG 0) (1 + ν) :=
  (xf_inv ν hν).B_eq (Order.add_one_le_of_lt hν) (lt_add_one ν)

theorem xfV_γ : (xfV ν).γ ≤ 1 + ν := (xf_inv ν hν).γ ν (lt_add_one ν)

theorem xfV_b {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hνx : 1 + ν < x) :
    (xfV ν).b x = veblen (lgG x) (1 + ν) :=
  (xf_inv ν hν).b_eq (Order.add_one_le_of_lt hν) (lt_add_one ν) hx hx1 hνx

end Main

/-- **Later systems keep the readings and gates of earlier ones.** -/
theorem xfV_ext {β γ : Ordinal.{0}} (hβγ : β ≤ γ) (hγ : γ < gamma 0) {c : Ordinal.{0}} (hc : c < (xfV β).B)
    (x : Ordinal.{0}) : (xfV γ).R c x = (xfV β).R c x ∧ (xfV γ).g c = (xfV β).g c :=
  ⟨(xf_inv γ hγ).cohR β γ hβγ (lt_add_one γ) c x hc, (xf_inv γ hγ).cohg β γ hβγ (lt_add_one γ) c hc⟩

/-- `xfV 0 = Xf.xfV1`, so every `xfV ν` extends `Hg.hgU` and lies above every (A2) system over `G`. -/
theorem xfV_hgU {ν : Ordinal.{0}} (hν : ν < gamma 0) {c : Ordinal.{0}} (hc : c < hgU.B) (x : Ordinal.{0}) :
    (xfV ν).R c x = hgU.R c x ∧ (xfV ν).g c = hgU.g c := by
  have hc1 : c < (xfV 0).B := by
    rw [xfV_zero]
    exact (hc.trans_le (ws_S1_le (xf_cf_lev 0) (wsSh_hgU wsA2_G) (xfD_M 0).1)).trans (xfCh.B_lt 0)
  have h0 := xfV_ext (zero_le) hν hc1 x
  have h1 := xfV1_ext hc x
  rw [xfV_zero] at h0
  exact ⟨h0.1.trans h1.1, h0.2.trans h1.2⟩

end Googology.Trans.PoR.InaccPsi.R2.Xf

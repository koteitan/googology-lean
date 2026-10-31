import Googology.Trans.PoR.InaccPsi.R2.WsCode

/-!
# WsDat: RAW BASE DATA GOOD UP TO A LEVEL OF A CODE INTERFACE; THE TWO-GATE BASE; THE SHAPE OF A SYSTEM

`R2.Wo`'s data layer (`Wo.WoGood`, `Wo.woWB`, `Wo.WoSh`, `Wo.woSh_W`, `Wo.woSh_succ`, `Wo.woGood_G`, `Wo.woGood_Q`)
written once for an arbitrary code interface `C : Ws.WsC`.  The raw datum `Wo.WoR` and the pseudo-base datum
`Wo.woQR` are reused.

* `WsGood C r ℓ` (**a raw datum good up to the level `ℓ` of `C`**), `WsGood.mono`;
* `wsWB` (**the two-gate base of every level `μ` with `μ + Ω₁ ≤ ℓ`**: an `Hn.HnWB (C.lv μ)`);
* `WsSh C r ℓ S` (**the shape of a system at the level `ℓ` over `r`**), `wsSh_W`, `wsSh_succ`;
* `wsG C` (`G` with the low field `C.Zo`), `wsGood_G` (**`G` is good up to every level**), `wsGood_Q` (**every
  pseudo-base of a level is good up to it**).

No new axiom.  New definitions: `WsGood`, `wsWB`, `WsSh`, `wsG`.
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

variable (C : WsC)

/-- **`hdNx μ F < hdNx ℓ F`** for `F` a value of `φ(ℓ, ·)` and `μ < ℓ`. -/
theorem ws_N_lt {C : WsC} {μ ℓ F : Ordinal.{0}} (hℓ : C.Lev ℓ) (hF : LuP ℓ F) (h : μ < ℓ) : hdNx μ F < hdNx ℓ F :=
  (hdNx_lt_N (hcN_gt _ _)).trans (hdN_lt_Nx (lev_lim hℓ h))

/-- **A RAW DATUM GOOD UP TO THE LEVEL `ℓ` OF `C`.** -/
structure WsGood (r : WoR) (ℓ : Ordinal.{0}) : Prop where
  lev : C.Lev ℓ
  γ_lt : r.γ < Om1
  F_P : LuP ℓ r.F
  G_le : gcG 0 ≤ r.F
  S_lt1 : hdNx ℓ r.F < gcG 1
  F_mem : ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}}, 0 < a → r.γ < b → r.F ∈ S.CSet a b
  S_mem : ∀ μ, C.Lev μ → μ ≤ ℓ → ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}}, 0 < a → max r.γ (C.g μ) < b →
    hdNx μ r.F ∈ S.CSet a b
  S_memW : ∀ μ, C.Lev μ → μ + Om1 ≤ ℓ → ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}}, 0 < a →
    max r.γ (C.g μ) < b → hdNx (μ + Om1) r.F ∈ S.CSet a b
  F_code : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → ∀ y, GxCl Z {gcG 0} y → r.F ≤ y → y < hdNx ℓ r.F →
    GxCl Z {gcG 0} r.F
  F_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → ∀ y, GxCl Z {gcG 0} y → r.F ≤ y → y < hdNx ℓ r.F → r.γ < Z
  S_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → GxCl Z {gcG 0} (hdNx ℓ r.F) → r.γ < Z
  rd : ∀ μ, C.Lev μ → μ ≤ ℓ → ∀ x, InE x → x < Om1 → max r.γ (C.g μ) < x →
    LuP (C.R μ x) (r.Fr x) ∧ C.R μ x < r.Fr x ∧ hdNx (C.R μ x) (r.Fr x) < r.Zo x
  S_pi : ∀ μ, C.Lev μ → μ ≤ ℓ → ∀ σ ρ, Bases σ ρ → max r.γ (C.g μ) < σ →
    hdNx (C.R μ ρ) (r.Fr ρ) ∈ TB ρ σ ∧ pi σ ρ (hdNx (C.R μ ρ) (r.Fr ρ)) = hdNx (C.R μ σ) (r.Fr σ)
  Zo_fix : ∀ x, veblen 2 (r.Zo x) = r.Zo x
  Zo_G1 : ∀ x, InE x → x < Om1 → r.Zo x < gq 1 x
  Fr_pi : ∀ {σ ρ}, Bases σ ρ → r.γ < σ → r.Fr ρ ∈ TB ρ σ ∧ pi σ ρ (r.Fr ρ) = r.Fr σ

namespace WsGood

variable {C} {r : WoR} {ℓ : Ordinal.{0}} (h : WsGood C r ℓ)
include h

/-- **GOOD UP TO `ℓ` ⇒ GOOD UP TO EVERY LOWER LEVEL.** -/
theorem mono {μ : Ordinal.{0}} (hμ : C.Lev μ) (hle : μ ≤ ℓ) : WsGood C r μ where
  lev := hμ
  γ_lt := h.γ_lt
  F_P := hd_LuP_mono hle h.F_P
  G_le := h.G_le
  S_lt1 := (hdNx_mono hle _).trans_lt h.S_lt1
  F_mem := h.F_mem
  S_mem := fun ν hν hνμ => h.S_mem ν hν (hνμ.trans hle)
  S_memW := fun ν hν hνμ => h.S_memW ν hν (hνμ.trans hle)
  F_code := fun Z hZ hZ1 y hy hQy hyZ => h.F_code Z hZ hZ1 y hy hQy (hyZ.trans_le (hdNx_mono hle _))
  F_cl := fun Z hZ hZ1 y hy hQy hyZ => h.F_cl Z hZ hZ1 y hy hQy (hyZ.trans_le (hdNx_mono hle _))
  S_cl := fun Z hZ hZ1 hc => by
    rcases hle.lt_or_eq with hlt | rfl
    · exact h.F_cl Z hZ hZ1 _ hc (hdNx_gt _ _).le (ws_N_lt h.lev h.F_P hlt)
    · exact h.S_cl Z hZ hZ1 hc
  rd := fun ν hν hνμ => h.rd ν hν (hνμ.trans hle)
  S_pi := fun ν hν hνμ => h.S_pi ν hν (hνμ.trans hle)
  Zo_fix := h.Zo_fix
  Zo_G1 := h.Zo_G1
  Fr_pi := h.Fr_pi

section Base

variable {μ x : Ordinal.{0}} (hμ : C.Lev μ) (hμℓ : μ + Om1 ≤ ℓ) (hx : InE x) (hx1 : x < Om1)
  (hg : max r.γ (C.g μ) < x)
include hμ hμℓ hx hx1 hg

theorem rdS : max r.γ (C.g (μ + Om1)) < x :=
  max_lt (max_lt_iff.1 hg).1 ((g_succ_iff hμ hx).2 (max_lt_iff.1 hg).2)

/-- `F(x)` is a value of `φ(R μ x + x, ·)`. -/
theorem rP : LuP (C.R μ x + x) (r.Fr x) := by
  have := (h.rd _ (lev_succ hμ h.lev hμℓ) hμℓ x hx hx1 (rdS h hμ hμℓ hx hx1 hg)).1
  rwa [C.succ_R μ hμ.2.2 hμ.2.1] at this

theorem rgt : C.R μ x + x < r.Fr x := by
  have := (h.rd _ (lev_succ hμ h.lev hμℓ) hμℓ x hx hx1 (rdS h hμ hμℓ hx hx1 hg)).2.1
  rwa [C.succ_R μ hμ.2.2 hμ.2.1] at this

theorem rZo : hdNx (C.R μ x + x) (r.Fr x) < r.Zo x := by
  have := (h.rd _ (lev_succ hμ h.lev hμℓ) hμℓ x hx hx1 (rdS h hμ hμℓ hx hx1 hg)).2.2
  rwa [C.succ_R μ hμ.2.2 hμ.2.1] at this

/-- **`F(x)` is a fixed point of `φ(R μ x, ·)`.** -/
theorem rfix : veblen (C.R μ x) (r.Fr x) = r.Fr x :=
  wo_fix_of_LuP (rP h hμ hμℓ hx hx1 hg) (lt_add_of_pos_right _ hx.pos)

end Base

end WsGood

/-! ## The two-gate base at a lower level -/

/-- **THE TWO-GATE BASE OF THE LEVEL `μ`** (`μ + Ω₁ ≤ ℓ`): point `F`, reading `F(x)`, code gate `γ`, reading gate
`max γ (g μ)`, outer low field `Z_o`. -/
noncomputable def wsWB (r : WoR) (μ : Ordinal.{0}) (hμ : C.Lev μ) (h : WsGood C r (μ + Om1)) : HnWB (C.lv μ hμ) where
  F := r.F
  Fr := r.Fr
  γ := r.γ
  γR := max r.γ (C.g μ)
  Zo := r.Zo
  γ_lt := h.γ_lt
  γR_lt := max_lt h.γ_lt (C.g_lt μ hμ.2.2)
  γ_le := le_max_left _ _
  lg := le_max_right _ _
  γR_cl := fun _ _ _ h1 h2 => max_lt h1 h2
  F_P := h.F_P
  G_le := h.G_le
  S_lt1 := h.S_lt1
  F_mem := h.F_mem
  S_mem := fun S _ _ ha hb => h.S_memW μ hμ le_rfl S ha hb
  F_code := h.F_code
  F_cl := h.F_cl
  S_cl := h.S_cl
  Fr_gt := fun hx hx1 hγ => by
    show C.rd μ _ + _ < _
    rw [C.rd_eq hx hx1 hμ.1 hμ.2.2 (max_lt_iff.1 hγ).2]; exact h.rgt hμ le_rfl hx hx1 hγ
  Fr_P := fun hx hx1 hγ => by
    show LuP (C.rd μ _ + _) _
    rw [C.rd_eq hx hx1 hμ.1 hμ.2.2 (max_lt_iff.1 hγ).2]; exact h.rP hμ le_rfl hx hx1 hγ
  S_Zo := fun hx hx1 hγ => by
    show hdNx (C.rd μ _ + _) _ < _
    rw [C.rd_eq hx hx1 hμ.1 hμ.2.2 (max_lt_iff.1 hγ).2]; exact h.rZo hμ le_rfl hx hx1 hγ
  Zo_fix := h.Zo_fix
  Zo_G1 := h.Zo_G1
  Fr_pi := fun hB hγ => h.Fr_pi hB ((le_max_left _ _).trans_lt hγ)
  S_pi := fun {σ ρ} hB hγ => by
    show hdNx (C.rd μ ρ + ρ) _ ∈ _ ∧ pi σ ρ (hdNx (C.rd μ ρ + ρ) _) = hdNx (C.rd μ σ + σ) _
    have hσg : C.g μ < σ := (max_lt_iff.1 hγ).2
    rw [C.rd_eq hB.2.1 hB.2.2.2 hμ.1 hμ.2.2 (hσg.trans hB.2.2.1),
      C.rd_eq hB.1 (hB.2.2.1.trans hB.2.2.2) hμ.1 hμ.2.2 hσg,
      ← C.succ_R μ hμ.2.2 hμ.2.1, ← C.succ_R μ hμ.2.2 hμ.2.1]
    exact h.S_pi _ (lev_succ hμ h.lev le_rfl) le_rfl σ ρ hB
      (h.rdS hμ le_rfl hB.1 (hB.2.2.1.trans hB.2.2.2) hγ)

theorem wsWB_γR (r : WoR) (μ : Ordinal.{0}) (hμ : C.Lev μ) (h : WsGood C r (μ + Om1)) :
    (wsWB C r μ hμ h).γR = max r.γ (C.g μ) := rfl

/-! ## The shape of a system -/

/-- **THE SHAPE OF A SYSTEM AT THE LEVEL `ℓ` OVER `r`.** -/
def WsSh (r : WoR) (ℓ : Ordinal.{0}) (S : HgVD) : Prop :=
  S.B = hdNx ℓ r.F ∧ (r.γ ≤ S.γ ∧ S.γ ≤ max r.γ (C.g ℓ)) ∧
    (∀ x, InE x → x < Om1 → (S.γ < x ↔ max r.γ (C.g ℓ) < x)) ∧
    (∀ x, InE x → x < Om1 → max r.γ (C.g ℓ) < x → S.b x = hdNx (C.R ℓ x) (r.Fr x)) ∧
    (∀ x, InE x → x < Om1 → S.Z x = if max r.γ (C.g ℓ) < x then evZ (hdNx (C.R ℓ x) (r.Fr x)) else r.Zo x) ∧
    ∀ c σ, r.F ≤ c → c < S.B → InE σ → σ < Om1 → S.g c < σ → r.γ < σ

variable {C}

/-- **A SHAPE AT `μ` IS A START OVER `wsWB r μ`.** -/
theorem wsSh_W {r : WoR} {μ : Ordinal.{0}} (hμ : C.Lev μ) (h : WsGood C r (μ + Om1)) {S : HgVD}
    (hS : WsSh C r μ S) : HnWShape (wsWB C r μ hμ h) 0 S := by
  obtain ⟨hB, -, hγ, hb, hZ, hhi⟩ := hS
  have hmx : ∀ x : Ordinal.{0}, max (max r.γ (C.g μ)) 0 < x ↔ max r.γ (C.g μ) < x := fun x => by
    rw [max_eq_left zero_le]
  refine ⟨?_, fun x hx hx1 => ?_, fun x hx hx1 hk => ?_, fun x hx hx1 => ?_, hhi⟩
  · rw [hB]; show hdNx μ r.F = veblen (μ + 0) (r.F + 1)
    rw [add_zero]; exact hdNx_fixP (wo_fix_of_LuP h.F_P (lt_add_of_pos_right _ wh_Om1_pos))
  · rw [hγ x hx hx1]; exact (hmx x).symm
  · have hk' := (hmx x).1 hk
    rw [hb x hx hx1 hk']
    show hdNx (C.R μ x) (r.Fr x) = veblen (C.rd μ x + 0) (r.Fr x + 1)
    rw [add_zero, C.rd_eq hx hx1 hμ.1 hμ.2.2 (max_lt_iff.1 hk').2]
    exact hdNx_fixP (h.rfix hμ le_rfl hx hx1 hk')
  · rw [hZ x hx hx1]
    show _ = if max (max r.γ (C.g μ)) 0 < x then evZ (veblen (C.rd μ x + 0) (r.Fr x + 1))
      else (wsWB C r μ hμ h).hnwZo x
    by_cases hk : max r.γ (C.g μ) < x
    · rw [if_pos hk, if_pos ((hmx x).2 hk), add_zero, C.rd_eq hx hx1 hμ.1 hμ.2.2 (max_lt_iff.1 hk).2,
        hdNx_fixP (h.rfix hμ le_rfl hx hx1 hk)]
    · rw [if_neg hk, if_neg (fun h' => hk ((hmx x).1 h')), (wsWB C r μ hμ h).hnwZo_low hk]
      rfl

/-- **THE UNION OVER `wsWB r μ` HAS THE SHAPE AT `μ + Ω₁`.** -/
theorem wsSh_succ {r : WoR} {μ : Ordinal.{0}} (hμ : C.Lev μ) (h : WsGood C r (μ + Om1))
    (St0 : HnVStTy (C.lv μ hμ) 0) (h0 : ∀ Q U h, HnVSpec Q U (St0 Q U h)) {S : HgVD} (hS : WsSh C r μ S) :
    WsSh C r (μ + Om1) (hnwU (wsWB C r μ hμ h) St0 h0 S (wsSh_W hμ h hS)) := by
  set P := wsWB C r μ hμ h
  have hcut : ∀ x, InE x → (max r.γ (C.g μ) < x ↔ max r.γ (C.g (μ + Om1)) < x) := fun x hx => by
    rw [max_lt_iff, max_lt_iff, g_succ_iff hμ hx]
  have hgl : C.g μ ≤ C.g (μ + Om1) := C.succ_g μ hμ.2.2 hμ.2.1
  refine ⟨rfl, ⟨le_max_left _ _, max_le_max le_rfl hgl⟩, fun x hx _ => hcut x hx, fun x hx hx1 hk => ?_,
    fun x hx hx1 => ?_, fun c σ hFc hc hσ hσ1 hg => ?_⟩
  · have hk' := (hcut x hx).2 hk
    show hdNx (C.rd μ x + x) (r.Fr x) = _
    rw [C.rd_eq hx hx1 hμ.1 hμ.2.2 (max_lt_iff.1 hk').2, C.succ_R μ hμ.2.2 hμ.2.1]
  · show hnwUZ P x = _
    unfold hnwUZ
    by_cases hk : max r.γ (C.g μ) < x
    · rw [if_pos (show P.γR < x from hk), if_pos ((hcut x hx).1 hk)]
      show evZ (hdNx (C.rd μ x + x) (r.Fr x)) = _
      rw [C.rd_eq hx hx1 hμ.1 hμ.2.2 (max_lt_iff.1 hk).2, C.succ_R μ hμ.2.2 hμ.2.1]
    · rw [if_neg (show ¬ P.γR < x from hk), if_neg (fun h' => hk ((hcut x hx).2 h'))]
      rfl
  · by_cases hSc : S.B ≤ c
    · exact (le_max_left _ _).trans_lt (hnwU_highR P St0 h0 S (wsSh_W hμ h hS) hSc hc hσ hσ1 hg)
    · have hc0 : c < S.B := not_le.1 hSc
      rw [hnwU_g0 P St0 h0 S (wsSh_W hμ h hS) hc0] at hg
      exact hS.2.2.2.2.2 c σ hFc hc0 hσ hσ1 hg

/-! ## The instance `G` -/

variable (C)

/-- **`G` as a raw datum**: point `G`, reading `Γ_{x+1}`, code gate `0`, outer low field `C.Zo`. -/
noncomputable def wsG : WoR := ⟨gcG 0, lgG, 0, C.Zo⟩

variable {C}

theorem ws_G_fix {μ : Ordinal.{0}} (hμ : C.Lev μ) : veblen μ (gcG 0) = gcG 0 :=
  gn_veb_fix (gcG_SC 0) (C.lt_G hμ.2.2)

/-- **`G` IS GOOD UP TO EVERY LEVEL.** -/
theorem wsGood_G {ℓ : Ordinal.{0}} (hℓ : C.Lev ℓ) : WsGood C (wsG C) ℓ where
  lev := hℓ
  γ_lt := gv_Om1_pos
  F_P := ⟨gcG 0, ws_G_fix hℓ⟩
  G_le := le_rfl
  S_lt1 := by
    have hG1 := gcG_SC 1
    have hE := Low.opow_eq_self_of_SC hG1
    have hfix : veblen ℓ (gcG 1) = gcG 1 := gn_veb_fix hG1 (hℓ.2.2.trans C.Bd_lt_G1)
    have h2 := (isNormal_veblen ℓ).strictMono ((ev_isSuccLimit_of_inE hE).add_one_lt (gcG_lt zero_lt_one))
    show hdNx ℓ (gcG 0) < gcG 1
    rw [hdNx_fixP (ws_G_fix hℓ)]; rwa [hfix] at h2
  F_mem := fun S _ _ ha _ => gmS_G0_mem S ha
  S_mem := fun μ hμ _ S _ _ ha hb => by
    show hdNx μ (gcG 0) ∈ _
    rw [hdNx_fixP (ws_G_fix hμ)]
    exact CSet.phi_mem ((C.lv μ hμ).L_mem S _ _ ha (max_lt_iff.1 hb).2) (CSet.succ_mem (gmS_G0_mem S ha))
  S_memW := fun μ hμ hle S _ _ ha hb => by
    show hdNx (μ + Om1) (gcG 0) ∈ _
    rw [hdNx_fixP (ws_G_fix (lev_succ hμ hℓ hle))]
    exact CSet.phi_mem ((C.lv μ hμ).succ.L_mem S _ _ ha (max_lt_iff.1 hb).2) (CSet.succ_mem (gmS_G0_mem S ha))
  F_code := fun _ _ _ _ _ _ _ => GxCl.atom (Set.mem_singleton _)
  F_cl := fun _ hZ _ _ _ _ _ => hZ.1
  S_cl := fun _ hZ _ _ => hZ.1
  rd := fun μ hμ _ x hx hx1 hg => by
    have hgx : C.g μ < x := (max_lt_iff.1 hg).2
    have hlt := C.R_lt hx hx1 hμ.2.2 hgx
    have hfix := hjG_fix hx hx1 (one_le_R hx hx1 hμ.1 hμ.2.2 hgx) hlt
    exact ⟨⟨lgG x, hfix⟩, hlt, C.Zo_gt hx hx1 hμ.1 hμ.2.2 hgx⟩
  S_pi := fun μ hμ _ σ ρ hB hg => by
    have hgσ : C.g μ < σ := (max_lt_iff.1 hg).2
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hgρ : C.g μ < ρ := hgσ.trans hB.2.2.1
    exact hjG_S_pi hB (C.R_pi hB hμ.2.2 hgσ) (one_le_R hB.2.1 hρ1 hμ.1 hμ.2.2 hgρ)
      (C.R_lt hB.2.1 hρ1 hμ.2.2 hgρ) (one_le_R hB.1 hσ1 hμ.1 hμ.2.2 hgσ) (C.R_lt hB.1 hσ1 hμ.2.2 hgσ)
  Zo_fix := C.Zo_fix
  Zo_G1 := fun _ hx hx1 => C.Zo_G1 _ hx hx1
  Fr_pi := fun hB _ => Go.goGl.ba_pi _ _ hB

/-! ## The instance: a pseudo-base of a level -/

section QInst

variable {ℓ : Ordinal.{0}} (hℓ : C.Lev ℓ) (Q : HnVQ (C.lv ℓ hℓ) 0)

include hℓ in
theorem ws_Q_g : C.g ℓ ≤ Q.γ := Q.lg

theorem ws_Q_l {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : Q.γ < x) : (C.lv ℓ hℓ).l x + 0 = C.R ℓ x := by
  rw [add_zero]; exact C.lv_l hℓ hx hx1 ((ws_Q_g hℓ Q).trans_lt hγ)

theorem ws_Q_N : hdNx ((C.lv ℓ hℓ).L + 0) Q.F = hdNx ℓ Q.F := by rw [add_zero]; rfl

theorem ws_Q_FP : LuP ℓ Q.F := by have := Q.F_P; rwa [add_zero] at this

/-- **EVERY PSEUDO-BASE OF A LEVEL `ℓ` IS GOOD UP TO `ℓ`.** -/
theorem wsGood_Q : WsGood C (woQR Q) ℓ where
  lev := hℓ
  γ_lt := Q.γ_lt
  F_P := ws_Q_FP hℓ Q
  G_le := Q.G_lt.le
  S_lt1 := by show hdNx ℓ Q.F < _; rw [← ws_Q_N hℓ Q]; exact Q.S_lt1
  F_mem := Q.F_mem
  S_mem := fun μ hμ hle S _ _ ha hb => by
    rcases hle.lt_or_eq with hlt | rfl
    · show hdNx μ Q.F ∈ _
      rw [hdNx_fixP (wo_fix_of_LuP (ws_Q_FP hℓ Q) hlt)]
      exact CSet.phi_mem ((C.lv μ hμ).L_mem S _ _ ha (max_lt_iff.1 hb).2)
        (CSet.succ_mem (Q.F_mem S ha (max_lt_iff.1 hb).1))
    · show hdNx μ Q.F ∈ _
      rw [← ws_Q_N hℓ Q]; exact Q.S_mem S ha (max_lt_iff.1 hb).1
  S_memW := fun μ hμ hle S _ _ ha hb => by
    rcases hle.lt_or_eq with hlt | heq
    · show hdNx (μ + Om1) Q.F ∈ _
      rw [hdNx_fixP (wo_fix_of_LuP (ws_Q_FP hℓ Q) hlt)]
      exact CSet.phi_mem ((C.lv μ hμ).succ.L_mem S _ _ ha (max_lt_iff.1 hb).2)
        (CSet.succ_mem (Q.F_mem S ha (max_lt_iff.1 hb).1))
    · show hdNx (μ + Om1) Q.F ∈ _
      rw [heq, ← ws_Q_N hℓ Q]; exact Q.S_mem S ha (max_lt_iff.1 hb).1
  F_code := fun Z hZ hZ1 y hy hQy hyZ => Q.F_code Z hZ hZ1 y hy hQy (by rw [ws_Q_N hℓ Q]; exact hyZ)
  F_cl := fun Z hZ hZ1 y hy hQy hyZ => Q.F_cl Z hZ hZ1 y hy hQy (by rw [ws_Q_N hℓ Q]; exact hyZ)
  S_cl := fun Z hZ hZ1 hc => Q.S_cl Z hZ hZ1 (by rw [ws_Q_N hℓ Q]; exact hc)
  rd := fun μ hμ hle x hx hx1 hg => by
    have hγ : Q.γ < x := (max_lt_iff.1 hg).1
    have hgℓ : C.g ℓ < x := (ws_Q_g hℓ Q).trans_lt hγ
    have hmon : C.R μ x ≤ C.R ℓ x := R_le_mono hx hx1 hℓ.2.2 hle hgℓ (max_lt_iff.1 hg).2
    have h1 := Q.Fr_P hx hx1 hγ
    have h2 := Q.Fr_gt hx hx1 hγ
    have h3 := Q.S_Zo hx hx1 hγ
    rw [ws_Q_l hℓ Q hx hx1 hγ] at h1 h2 h3
    exact ⟨hd_LuP_mono hmon h1, hmon.trans_lt h2, (hdNx_mono hmon _).trans_lt h3⟩
  S_pi := fun μ hμ hle σ ρ hB hg => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hγσ : Q.γ < σ := (max_lt_iff.1 hg).1
    have hγρ : Q.γ < ρ := hγσ.trans hB.2.2.1
    have hgμσ : C.g μ < σ := (max_lt_iff.1 hg).2
    have hgμρ : C.g μ < ρ := hgμσ.trans hB.2.2.1
    rcases hle.lt_or_eq with hlt | heq
    · have hfix : ∀ {y}, InE y → y < Om1 → Q.γ < y → C.g μ < y →
          veblen ((C.lv μ hμ).l y + 0) (Q.Fr y) = Q.Fr y := by
        intro y hy hy1 hγy hgμy
        have hgy : C.g ℓ < y := (ws_Q_g hℓ Q).trans_lt hγy
        rw [add_zero, C.lv_l hμ hy hy1 hgμy]
        have h1 := Q.Fr_P hy hy1 hγy
        rw [ws_Q_l hℓ Q hy hy1 hγy] at h1
        exact wo_fix_of_LuP h1 (C.R_mono hy hy1 hℓ.2.2 hlt hgy hgμy)
      have hgt : ∀ {y}, InE y → y < Om1 → Q.γ < y → C.g μ < y → (C.lv μ hμ).l y + 0 < Q.Fr y := by
        intro y hy hy1 hγy hgμy
        have hgy : C.g ℓ < y := (ws_Q_g hℓ Q).trans_lt hγy
        have h2 := Q.Fr_gt hy hy1 hγy
        rw [ws_Q_l hℓ Q hy hy1 hγy] at h2
        rw [add_zero, C.lv_l hμ hy hy1 hgμy]
        exact (C.R_mono hy hy1 hℓ.2.2 hlt hgy hgμy).trans h2
      obtain ⟨f1, f2⟩ := Q.Fr_pi hB hγσ
      have hh := hnv_glA_pi (C.lv μ hμ) hB hgμσ hB.1.pos f1 (Q.Fr_lt1 hB.2.1 hρ1 hγρ)
      rw [f2, hnv_glA_fixP (C.lv μ hμ) hB.2.1 hρ1 (hB.1.pos.trans hB.2.2.1) (hfix hB.2.1 hρ1 hγρ hgμρ)
        (hgt hB.2.1 hρ1 hγρ hgμρ) (Q.Fr_lt1 hB.2.1 hρ1 hγρ),
        hnv_glA_fixP (C.lv μ hμ) hB.1 hσ1 hB.1.pos (hfix hB.1 hσ1 hγσ hgμσ) (hgt hB.1 hσ1 hγσ hgμσ)
        (Q.Fr_lt1 hB.1 hσ1 hγσ)] at hh
      rwa [add_zero, add_zero, C.lv_l hμ hB.2.1 hρ1 hgμρ, C.lv_l hμ hB.1 hσ1 hgμσ] at hh
    · subst heq
      have := Q.S_pi hB hγσ
      rwa [ws_Q_l hμ Q hB.2.1 hρ1 hγρ, ws_Q_l hμ Q hB.1 hσ1 hγσ] at this
  Zo_fix := Q.Zo_fix
  Zo_G1 := Q.Zo_G1
  Fr_pi := Q.Fr_pi

end QInst

end Googology.Trans.PoR.InaccPsi.R2.Ws

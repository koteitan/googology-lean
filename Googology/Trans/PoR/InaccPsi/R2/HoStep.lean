import Googology.Trans.PoR.InaccPsi.R2.HoBR

/-!
# HoStep: ONE PREFIX STEP `Ω₁²·v → Ω₁²·(v+1)`: THE NEXT PREFIX PACKAGE AND THE NEXT START OVER `G`

For a prefix package `P` of the level `Ω₁²·v` (`1 ≤ v < Ω₁`; read `x·x·v` above its gate `hlGt v`) with its band family
`Kf = Ho.hoBF P`:

* at every pseudo-base `Q` of the next prefix `hoLv (v+1) 0`, the union `Ho.hoRU` over the base datum `Ho.hoQD Q`
  started at the step of `P` at `Q.lowr` is the step of the next prefix (`hoQU_spec`); so `hoPkNx P` is **THE PACKAGE AT
  THE LEVEL `Ω₁²·(v+1)`**, and it extends `P` (`hoPkNx_ext`).  This generalizes `Hn.hnQU_spec` / `Hn.hnPkSq` (there
  `v = 0` with `Hl` packages);
* over `G`, the union `Ho.hoRU` over `Ho.hoGD v` started at a start over `G` at `P` is a start over `G` at every
  package of the next prefix (`hoGU_shape`): this is the step `φ(Ω₁²·v, G+1) → φ(Ω₁²·(v+1), G+1)`, generalizing
  `Hn.hnU` (`v = 1`).

No new axiom.  New definitions: `hoNxLv`, `hoQS0`, `hoQU`, `hoPkNx`, `hoGU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ho

open Googology.Trans.PoR.InaccPsi.R2.Hn Googology.Trans.PoR.InaccPsi.R2.Hl
open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk
open Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **A package `K` transported along an equality of packages gives the same step at the lowered pseudo-base.** -/
theorem ho_St0_congr {K P : HnPk} (e : K = P) {Λ' : HnLv} (Q : HnVQ Λ' 0) (hg : K.Λ.g ≤ Λ'.g)
    (hL : K.Λ.L + Om1 ≤ Λ'.L) (hl : ∀ x, InE x → x < Om1 → Λ'.g < x → K.Λ.l x + x ≤ Λ'.l x)
    (hg' : P.Λ.g ≤ Λ'.g) (hL' : P.Λ.L + Om1 ≤ Λ'.L) (hl' : ∀ x, InE x → x < Om1 → Λ'.g < x → P.Λ.l x + x ≤ Λ'.l x)
    (U : HgVD) (hU : HgSStart (hnVPB Q) U) :
    K.St0 (Q.lowr K.Λ hg hL hl) U hU = P.St0 (Q.lowr P.Λ hg' hL' hl') U hU := by
  subst e; rfl

theorem ho_1le_succ (v : Ordinal.{0}) : (1 : Ordinal.{0}) ≤ v + 1 :=
  Order.one_le_iff_pos.2 (Order.lt_add_one_iff.2 zero_le)

/-- **The next prefix datum `Ω₁²·(v+1)`**, read `x·x·(v+1)`. -/
noncomputable def hoNxLv {v : Ordinal.{0}} (hv : v < Om1) : HnLv :=
  hoLv (v + 1) 0 (ho_1le_succ v) (gl_Om1_lim.add_one_lt hv) gv_Om1_pos

section Nx

variable {v : Ordinal.{0}} (hv : v < Om1)

theorem hoNx_L : (hoNxLv hv).L = Om1 * Om1 * (v + 1) := hoLv_L0 _ _

theorem hoNx_l (x : Ordinal.{0}) (hx : (hoNxLv hv).g < x) : (hoNxLv hv).l x = x * x * (v + 1) := hoLv_l0 _ _ hx

theorem hoNx_g : (hoNxLv hv).g = hlGt (v + 1) := by
  show max (hlGt (v + 1)) (hlGt 0) = _; rw [ho_hlGt0, max_eq_left zero_le]

theorem hoNx_g' : hlGt (v + 1) ≤ (hoNxLv hv).g := (hoNx_g hv).ge

end Nx

section Step

variable {v : Ordinal.{0}} (hv1 : 1 ≤ v) (hv : v < Om1) (P : HnPk) (hPL : P.Λ.L = Om1 * Om1 * v)
  (hPl : ∀ x, P.Λ.g < x → P.Λ.l x = x * x * v) (hPg : P.Λ.g = hlGt v)

/-- The band family of `P`. -/
noncomputable abbrev hoKf : HoBF v hv1 hv := hoBF hv1 hv P hPL hPl hPg

include hPL hPl hPg in
theorem hoK0_g : ((hoKf hv1 hv P hPL hPl hPg).K 0).Λ.g ≤ (hoNxLv hv).g := by
  refine ((hoKf hv1 hv P hPL hPl hPg).ghi 0 gv_Om1_pos).trans ?_
  rw [ho_hlGt0, max_eq_left zero_le]; exact (ho_hlGt_le_succ v).trans (hoNx_g' hv)

include hPL hPl hPg in
theorem hoK0_L : ((hoKf hv1 hv P hPL hPl hPg).K 0).Λ.L + Om1 ≤ (hoNxLv hv).L := by
  rw [hoNx_L]; exact ((lt_add_one _).trans ((hoKf hv1 hv P hPL hPl hPg).good gv_Om1_pos).1).le

include hPL hPl hPg in
theorem hoK0_l : ∀ x, InE x → x < Om1 → (hoNxLv hv).g < x →
    ((hoKf hv1 hv P hPL hPl hPg).K 0).Λ.l x + x ≤ (hoNxLv hv).l x := fun x hx hx1 hg => by
  rw [hoNx_l hv x hg]
  exact (((hoKf hv1 hv P hPL hPl hPg).good gv_Om1_pos).2.2 x hx hx1 ((hoK0_g hv1 hv P hPL hPl hPg).trans_lt hg)).le

theorem hoP_g {Λ' : HnLv} (hΛ' : (hoNxLv hv).g ≤ Λ'.g) (hPg : P.Λ.g = hlGt v) : P.Λ.g ≤ Λ'.g := by
  rw [hPg]; exact ((ho_hlGt_le_succ v).trans (hoNx_g' hv)).trans hΛ'

/-! ## The next prefix package -/

section Q

variable (Q : HnVQ (hoNxLv hv) 0) (U : HgVD) (hU : HgSStart (hnVPB Q) U)

/-- The base datum of `Q`. -/
noncomputable abbrev hoQD' : HoWD v := hoQD Q (hoNx_L hv) (hoNx_l hv) (hoNx_g' hv)

/-- The start of the band recursion at `Q`: the step of the first band package at `Q.lowr`. -/
noncomputable def hoQS0 : HgVD :=
  ((hoKf hv1 hv P hPL hPl hPg).K 0).St0 (Q.lowr ((hoKf hv1 hv P hPL hPl hPg).K 0).Λ (hoK0_g hv1 hv P hPL hPl hPg)
    (hoK0_L hv1 hv P hPL hPl hPg) (hoK0_l hv1 hv P hPL hPl hPg)) U hU

theorem hoQS0_spec : HnVSpec (Q.lowr ((hoKf hv1 hv P hPL hPl hPg).K 0).Λ (hoK0_g hv1 hv P hPL hPl hPg)
    (hoK0_L hv1 hv P hPL hPl hPg) (hoK0_l hv1 hv P hPL hPl hPg)) U (hoQS0 hv1 hv P hPL hPl hPg Q U hU) :=
  ((hoKf hv1 hv P hPL hPl hPg).K 0).h0 _ U hU

theorem hoQS0_shape : HnWShape (hoW (hoQD' hv Q) ((hoKf hv1 hv P hPL hPl hPg).K 0).Λ
    ((hoKf hv1 hv P hPL hPl hPg).good gv_Om1_pos)) 0 (hoQS0 hv1 hv P hPL hPl hPg Q U hU) :=
  hoQ_shape_dn Q (hoNx_L hv) (hoNx_l hv) (hoNx_g' hv) _ (hoK0_g hv1 hv P hPL hPl hPg) (hoK0_L hv1 hv P hPL hPl hPg)
    (hoK0_l hv1 hv P hPL hPl hPg) _ (hoQS0_spec hv1 hv P hPL hPl hPg Q U hU)

theorem hoQS0_γ : (hoQS0 hv1 hv P hPL hPl hPg Q U hU).γ =
    max (hoQD' hv Q).γ ((hoKf hv1 hv P hPL hPl hPg).K 0).Λ.g := by
  rw [(hoQS0_spec hv1 hv P hPL hPl hPg Q U hU).γ]
  exact (max_eq_left ((hoK0_g hv1 hv P hPL hPl hPg).trans Q.lg)).symm

/-- **THE STEP OF THE NEXT PREFIX AT `Q`**: the union over `hoQD Q` of the band systems started at `hoQS0`. -/
noncomputable def hoQU : HgVD :=
  hoRU (hoKf hv1 hv P hPL hPl hPg) (hoQD' hv Q) (hoQS0 hv1 hv P hPL hPl hPg Q U hU)
    (hoQS0_shape hv1 hv P hPL hPl hPg Q U hU) (hoQS0_γ hv1 hv P hPL hPl hPg Q U hU)

theorem hoQ_gmax : max Q.γ (hlGt (v + 1)) = Q.γ := max_eq_left ((hoNx_g' hv).trans Q.lg)

/-- **THE UNION AT `Q` HAS THE SPECIFICATION OF THE LEVEL `Ω₁²·(v+1) + 0`.** -/
theorem hoQU_spec : HnVSpec Q U (hoQU hv1 hv P hPL hPl hPg Q U hU) := by
  have hUB : U.B = Q.F := hg_B_of_start hU
  have hs0 := hoQS0_spec hv1 hv P hPL hPl hPg Q U hU
  have hF0 : Q.F < (hoQS0 hv1 hv P hPL hPl hPg Q U hU).B := by rw [hs0.B]; exact hdNx_gt _ _
  have hU0 : ∀ c, c < U.B → c < (hoQS0 hv1 hv P hPL hPl hPg Q U hU).B :=
    fun c hc => hc.trans (by rw [hUB]; exact hF0)
  have hgm := hoQ_gmax hv Q
  refine ⟨?_, ?_, fun x _ _ hγ => ?_, fun x _ _ => ?_, fun c x hc => ?_, fun c hc => ?_,
    fun c σ hFc hc hσ hσ1 hg => ?_, fun x hx hx1 hγ => ?_, fun x hx hx1 => ?_⟩
  · show hdNx (Om1 * Om1 * (v + 1)) Q.F = hdNx ((hoNxLv hv).L + 0) Q.F
    rw [add_zero, hoNx_L]
  · show max Q.γ (hlGt (v + 1)) = Q.γ
    exact hgm
  · show hdNx (x * x * (v + 1)) (Q.Fr x) = hdNx ((hoNxLv hv).l x + 0) (Q.Fr x)
    rw [add_zero, hoNx_l hv x (Q.lg.trans_lt hγ)]
  · show (if max Q.γ (hlGt (v + 1)) < x then evZ (hdNx (x * x * (v + 1)) (Q.Fr x)) else Q.Zo x) =
      if Q.γ < x then evZ (hdNx ((hoNxLv hv).l x + 0) (Q.Fr x)) else Q.Zo x
    rw [hgm]
    split_ifs with h
    · rw [add_zero, hoNx_l hv x (Q.lg.trans_lt h)]
    · rfl
  · unfold hoQU; rw [(hoRU_ext0 _ _ _ _ _ (hU0 c hc) x).1]; exact hs0.extR c x hc
  · unfold hoQU; rw [(hoRU_ext0 _ _ _ _ _ (hU0 c hc) 0).2]; exact hs0.extg c hc
  · exact hoRU_highF _ _ _ _ _ hFc (by rw [hoRU_B]; rw [add_zero, hoNx_L] at hc; exact hc) hσ hσ1 hg
  · unfold hoQU; rw [(hoRU_ext0 _ _ _ _ _ hF0 x).1]; exact hs0.RF x hx hx1 hγ
  · unfold hoQU; rw [(hoRU_ext0 _ _ _ _ _ hF0 0).2]; exact hs0.gF x hx hx1

end Q

/-- **THE PACKAGE AT THE LEVEL `Ω₁²·(v+1)`** (the step at every pseudo-base is `hoQU`). -/
noncomputable def hoPkNx : HnPk :=
  ⟨hoNxLv hv, fun Q U hU => hoQU hv1 hv P hPL hPl hPg Q U hU, fun Q U hU => hoQU_spec hv1 hv P hPL hPl hPg Q U hU⟩

theorem hoPkNx_Λ : (hoPkNx hv1 hv P hPL hPl hPg).Λ = hoNxLv hv := rfl

/-- **THE NEXT PREFIX PACKAGE EXTENDS `P`.** -/
theorem hoPkNx_ext : HnkExt P (hoPkNx hv1 hv P hPL hPl hPg) := by
  intro hg hL hl Q U hU c x hc
  have e := ho_St0_congr (hoBF_K0 hv1 hv P hPL hPl hPg) Q (hoK0_g hv1 hv P hPL hPl hPg)
    (hoK0_L hv1 hv P hPL hPl hPg) (hoK0_l hv1 hv P hPL hPl hPg) hg hL hl U hU
  have e' : hoQS0 hv1 hv P hPL hPl hPg Q U hU = P.St0 (Q.lowr P.Λ hg hL hl) U hU := e
  have hc' : c < (hoQS0 hv1 hv P hPL hPl hPg Q U hU).B := by rw [e']; exact hc
  have h := hoRU_ext0 (hoKf hv1 hv P hPL hPl hPg) (hoQD' hv Q) (hoQS0 hv1 hv P hPL hPl hPg Q U hU)
    (hoQS0_shape hv1 hv P hPL hPl hPg Q U hU) (hoQS0_γ hv1 hv P hPL hPl hPg Q U hU) hc' x
  exact ⟨h.1.trans (congrArg (fun T : HgVD => T.R c x) e'), h.2.trans (congrArg (fun T : HgVD => T.g c) e')⟩

/-! ## The next start over `G` -/

section G

variable (S0 : HgVD)
  (hS0 : HnWShape (hoW (hoGD v hv) ((hoKf hv1 hv P hPL hPl hPg).K 0).Λ ((hoKf hv1 hv P hPL hPl hPg).good gv_Om1_pos))
    0 S0)
  (hS0γ : S0.γ = max (hoGD v hv).γ ((hoKf hv1 hv P hPL hPl hPg).K 0).Λ.g)

/-- **THE SYSTEM AT `φ(Ω₁²·(v+1), G+1)`**: the union over `G` of the band systems started at `S₀`. -/
noncomputable def hoGU : HgVD := hoRU (hoKf hv1 hv P hPL hPl hPg) (hoGD v hv) S0 hS0 hS0γ

include hv in
theorem hoG_fix : veblen (Om1 * Om1 * (v + 1)) (gcG 0) = gcG 0 := gn_veb_fix (gcG_SC 0) (ho_next_lt_G hv 0)

theorem hoGU_B : (hoGU hv1 hv P hPL hPl hPg S0 hS0 hS0γ).B = veblen (Om1 * Om1 * (v + 1)) (gcG 0 + 1) :=
  hdNx_fixP (hoG_fix hv)

theorem hoGU_γ : (hoGU hv1 hv P hPL hPl hPg S0 hS0 hS0γ).γ = max 0 (hlGt (v + 1)) := rfl

theorem hoGU_ext0 {c : Ordinal.{0}} (hc : c < S0.B) (x : Ordinal.{0}) :
    (hoGU hv1 hv P hPL hPl hPg S0 hS0 hS0γ).R c x = S0.R c x ∧ (hoGU hv1 hv P hPL hPl hPg S0 hS0 hS0γ).g c = S0.g c :=
  hoRU_ext0 _ _ _ _ _ hc x

theorem hoGU_high {c σ : Ordinal.{0}} (hSc : S0.B ≤ c) (hc : c < (hoGU hv1 hv P hPL hPl hPg S0 hS0 hS0γ).B)
    (hσ : InE σ) (hσ1 : σ < Om1) (hg : (hoGU hv1 hv P hPL hPl hPg S0 hS0 hS0γ).g c < σ) : hlGt v < σ :=
  hoRU_high _ _ _ _ _ hSc hc hσ hσ1 hg

/-- **THE SYSTEM AT `φ(Ω₁²·(v+1), G+1)` IS A START OVER `G` AT EVERY PACKAGE `K` OF THE NEXT PREFIX** (`w = v + 1`;
`K` of level `Ω₁²·w`, read `x·x·w` above its gate `hlGt w`). -/
theorem hoGU_shape (w : Ordinal.{0}) (hw : w = v + 1) (hw1 : w < Om1) (K : HnPk) (hKL : K.Λ.L = Om1 * Om1 * w)
    (hKl : ∀ x, K.Λ.g < x → K.Λ.l x = x * x * w) (hKg : K.Λ.g = hlGt w) (hK : HoGood w K.Λ) :
    HnWShape (hoW (hoGD w hw1) K.Λ hK) 0 (hoGU hv1 hv P hPL hPl hPg S0 hS0 hS0γ) ∧
      (hoGU hv1 hv P hPL hPl hPg S0 hS0 hS0γ).γ = max (hoGD w hw1).γ K.Λ.g := by
  subst hw
  refine ⟨⟨?_, fun x _ _ => ?_, fun x hx hx1 hg => ?_, fun x hx hx1 => ?_, fun _ σ _ _ hσ _ _ => hσ.pos⟩, ?_⟩
  · rw [hoGU_B]; show _ = veblen (K.Λ.L + 0) (gcG 0 + 1); rw [add_zero, hKL]
  · show max 0 (hlGt (v + 1)) < x ↔ max (max 0 K.Λ.g) 0 < x
    rw [hKg, max_eq_left zero_le]
  · have hgx : K.Λ.g < x := (max_lt_iff.1 (max_lt_iff.1 hg).1).2
    have hvx : v < x := (lt_add_one v).trans (by rw [hKg] at hgx; exact hl_gt_E hx hgx)
    show hdNx (x * x * (v + 1)) (lgG x) = veblen (K.Λ.l x + 0) (lgG x + 1)
    rw [add_zero, hKl x hgx, hdNx_fixP (hjG_fix hx hx1 (ho_xnext_one hx) (ho_xnext_lt hx hx1 hvx))]
  · show (if max 0 (hlGt (v + 1)) < x then evZ (hdNx (x * x * (v + 1)) (lgG x)) else hoZo x) =
      if max (max 0 K.Λ.g) 0 < x then evZ (veblen (K.Λ.l x + 0) (lgG x + 1))
        else (hoW (hoGD (v + 1) hw1) K.Λ hK).hnwZo x
    rw [hKg, max_eq_left zero_le]
    split_ifs with h
    · have hvx : v < x := (lt_add_one v).trans (hl_gt_E hx (max_lt_iff.1 h).2)
      rw [add_zero, hKl x (by rw [hKg]; exact (max_lt_iff.1 h).2),
        hdNx_fixP (hjG_fix hx hx1 (ho_xnext_one hx) (ho_xnext_lt hx hx1 hvx))]
    · rw [hoW_Zo_low (hoGD (v + 1) hw1) K.Λ hK (by rw [hKg]; exact h)]; rfl
  · show max 0 (hlGt (v + 1)) = max 0 K.Λ.g
    rw [hKg]

end G

end Step

end Googology.Trans.PoR.InaccPsi.R2.Ho

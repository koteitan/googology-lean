import Googology.Trans.PoR.InaccPsi.R2.HlVL

/-!
# HlVG: A BASE OF THE GATED LEVEL `L + Ω₁` WITH TWO GATES; THE RECURSION ON THE LEVEL OVER IT

PORT of `Hj.HjVG`.  In addition, a base `HlWB` has TWO gates: a CODE gate `γ` (hull membership of `F`, the gates of
the codes `≥ F`, the high condition of a start) and a READING gate `γR ≥ γ`, `γR ≥ g` (the reading `F(x)` and its
Lemma EXACT), as `Hf.hfGB` has for the countable levels; `hlwB` reads at `max(γR, κ)`, `HlWShape` / `HlWOK` ask the
base gate `↔ max(γR, κ)` and the high condition with `γ`.  `hlw_S_g`: the level gate from a code of the bound.

What differs from the source: the level datum is a GATED one (`Hl.HlLv`: Lemma EXACT for the reading `ℓ` only at
base pairs `(σ, ρ)` above the level gate `g`, the hull membership of `L` only at `0 < a`, `g < b`, the code gate
`g < Z` only when a code over `Z` exists at the level); every pseudo-base and base carries `g ≤` its reading gate
(fields `lg`), and the code-gate fields take the extra hypothesis `g < Z`.  Proofs are otherwise those of the source;
names: prefix `hl`/`Hl` in place of `hj`/`Hj`.

No new axiom.  New definitions: `hlwZo`, `hlwB`, `HlWShape`, `HlWOK`, `hlwSt`, `HlWCoh`, `hlwCh`, `hlwChU`, `hlwL`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hl

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
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

variable {Λ : HlLv}

/-! ## A base of level `L + Ω₁` -/

/-- **A base of level `L + Ω₁`**: a point `F ∈ range φ(L+Ω₁, ·)`, `G ≤ F`, its reading `F(x) ∈ range φ(ℓ(x)+x, ·)`
above the gate `γ`, an outer low field `Z_o` above `hdNx (ℓ(x)+x) (F(x))`.  (`G` itself is one, `hlGW`, and so is
every pseudo-base of level `L + Ω₁`, `HlVQ.toW`.) -/
structure HlWB (Λ : HlLv) where
  F : Ordinal.{0}
  Fr : Ordinal.{0} → Ordinal.{0}
  γ : Ordinal.{0}
  γR : Ordinal.{0}
  Zo : Ordinal.{0} → Ordinal.{0}
  γ_lt : γ < Om1
  γR_lt : γR < Om1
  γ_le : γ ≤ γR
  lg : Λ.g ≤ γR
  γR_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → γ < Z → Λ.g < Z → γR < Z
  F_P : LuP (Λ.L + Om1) F
  G_le : gcG 0 ≤ F
  S_lt1 : hdNx (Λ.L + Om1) F < gcG 1
  F_mem : ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}}, 0 < a → γ < b → F ∈ S.CSet a b
  S_mem : ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}}, 0 < a → γR < b → hdNx (Λ.L + Om1) F ∈ S.CSet a b
  F_code : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → ∀ y, GxCl Z {gcG 0} y → F ≤ y → y < hdNx (Λ.L + Om1) F →
    GxCl Z {gcG 0} F
  F_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → ∀ y, GxCl Z {gcG 0} y → F ≤ y → y < hdNx (Λ.L + Om1) F → γ < Z
  S_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → GxCl Z {gcG 0} (hdNx (Λ.L + Om1) F) → γ < Z
  Fr_gt : ∀ {x}, InE x → x < Om1 → γR < x → Λ.l x + x < Fr x
  Fr_P : ∀ {x}, InE x → x < Om1 → γR < x → LuP (Λ.l x + x) (Fr x)
  S_Zo : ∀ {x}, InE x → x < Om1 → γR < x → hdNx (Λ.l x + x) (Fr x) < Zo x
  Zo_fix : ∀ x, veblen 2 (Zo x) = Zo x
  Zo_G1 : ∀ x, InE x → x < Om1 → Zo x < gq 1 x
  Fr_pi : ∀ {σ ρ}, Bases σ ρ → γR < σ → Fr ρ ∈ TB ρ σ ∧ pi σ ρ (Fr ρ) = Fr σ
  S_pi : ∀ {σ ρ}, Bases σ ρ → γR < σ →
    hdNx (Λ.l ρ + ρ) (Fr ρ) ∈ TB ρ σ ∧ pi σ ρ (hdNx (Λ.l ρ + ρ) (Fr ρ)) = hdNx (Λ.l σ + σ) (Fr σ)

namespace HlWB

variable (P : HlWB Λ)

theorem wfix {α : Ordinal.{0}} (hα : α < Λ.L + Om1) : veblen α P.F = P.F := by
  obtain ⟨a, ha⟩ := P.F_P; rw [← ha]; exact veblen_veblen_of_lt hα a

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : P.γR < x)
include hx hx1 hγ

theorem wrfix {α : Ordinal.{0}} (hα : α < Λ.l x + x) : veblen α (P.Fr x) = P.Fr x := by
  obtain ⟨a, ha⟩ := P.Fr_P hx hx1 hγ; rw [← ha]; exact veblen_veblen_of_lt hα a

theorem wS_lt1x : hdNx (Λ.l x + x) (P.Fr x) < gq 1 x := (P.S_Zo hx hx1 hγ).trans (P.Zo_G1 x hx hx1)

theorem Fr_lt1 : P.Fr x < gq 1 x := (hdNx_gt _ _).trans (P.wS_lt1x hx hx1 hγ)

theorem Fr_gtx : x < P.Fr x := ((Λ.l_ge x).trans le_self_add).trans_lt (P.Fr_gt hx hx1 hγ)

end Base

/-- **The outer low field of `P` as a base of level `L + κ`**: `hdNx (ℓ(x)+x) (F(x))` above `γ`, `Z_o(x)` below. -/
noncomputable def hlwZo (x : Ordinal.{0}) : Ordinal.{0} :=
  if P.γR < x then hdNx (Λ.l (max ω x) + max ω x) (P.Fr x) else P.Zo x

theorem hlwZo_eq {x : Ordinal.{0}} (hx : InE x) (hγ : P.γR < x) : P.hlwZo x = hdNx (Λ.l x + x) (P.Fr x) := by
  unfold hlwZo; rw [if_pos hγ, max_eq_right (omega0_lt_inE hx).le]

theorem hlwZo_low {x : Ordinal.{0}} (hγ : ¬ P.γR < x) : P.hlwZo x = P.Zo x := by unfold hlwZo; rw [if_neg hγ]

theorem hlwZo_fix (x : Ordinal.{0}) : veblen 2 (P.hlwZo x) = P.hlwZo x := by
  unfold hlwZo; split_ifs
  · refine hdNx_fix (((show (2 : Ordinal.{0}) < ω from by exact_mod_cast natCast_lt_omega0 2).trans_le
      (le_max_left ω x)).trans_le le_add_self) _
  · exact P.Zo_fix x

theorem hlwZo_G1 (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : P.hlwZo x < gq 1 x := by
  by_cases hγ : P.γR < x
  · rw [P.hlwZo_eq hx hγ]; exact P.wS_lt1x hx hx1 hγ
  · rw [P.hlwZo_low hγ]; exact P.Zo_G1 x hx hx1

end HlWB

/-! ## `P` as a base of every level `L + κ` -/

section WBase

variable (P : HlWB Λ)

theorem hlw_Lk1 {κ : Ordinal.{0}} (hκ : κ < Om1) : Λ.L + κ + 1 < Λ.L + Om1 := by
  rw [add_assoc]; exact (add_lt_add_iff_left _).2 (gl_Om1_lim.add_one_lt hκ)

theorem hlw_Lk {κ : Ordinal.{0}} (hκ : κ < Om1) : Λ.L + κ < Λ.L + Om1 := (add_lt_add_iff_left _).2 hκ

theorem hlw_lk1 {κ x : Ordinal.{0}} (hx : InE x) (hκx : κ < x) : Λ.l x + κ + 1 < Λ.l x + x := by
  rw [add_assoc]; exact (add_lt_add_iff_left _).2 ((ev_isSuccLimit_of_inE hx).add_one_lt hκx)

theorem hlw_lk {κ x : Ordinal.{0}} (hκx : κ < x) : Λ.l x + κ < Λ.l x + x := (add_lt_add_iff_left _).2 hκx

theorem hlw_N_eq {κ : Ordinal.{0}} (hκ : κ < Om1) : hcN (Λ.L + κ) P.F = veblen (Λ.L + κ + 1) (P.F + 1) := by
  have := hcN_veb (Λ.L + κ) P.F; rwa [P.wfix (hlw_Lk1 hκ)] at this

theorem hlw_N_lt_S {κ : Ordinal.{0}} (hκ : κ < Om1) : hcN (Λ.L + κ) P.F < hdNx (Λ.L + Om1) P.F :=
  hdN_lt_Nx (hlw_Lk1 hκ)

theorem hlw_rN_eq {κ x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : P.γR < x) (hκx : κ < x) :
    hcN (Λ.l x + κ) (P.Fr x) = veblen (Λ.l x + κ + 1) (P.Fr x + 1) := by
  have := hcN_veb (Λ.l x + κ) (P.Fr x); rwa [P.wrfix hx hx1 hγ (hlw_lk1 hx hκx)] at this

theorem hlw_rN_lt_S {κ x : Ordinal.{0}} (hx : InE x) (hκx : κ < x) :
    hcN (Λ.l x + κ) (P.Fr x) < hdNx (Λ.l x + x) (P.Fr x) := hdN_lt_Nx (hlw_lk1 hx hκx)

/-- **Lemma EXACT for `N_{ℓ(ρ)+κ}(F(ρ)) = ϑᵖ(Ω₁·(ℓ(ρ)+κ+1) + F(ρ))`**, `max(γ, κ) < σ`. -/
theorem hlw_N_pi {κ σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (hγ : max P.γR κ < σ) :
    hcN (Λ.l ρ + κ) (P.Fr ρ) ∈ TB ρ σ ∧ pi σ ρ (hcN (Λ.l ρ + κ) (P.Fr ρ)) = hcN (Λ.l σ + κ) (P.Fr σ) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hγσ : P.γR < σ := (max_lt_iff.1 hγ).1
  have hκσ : κ < σ := (max_lt_iff.1 hγ).2
  have hγρ : P.γR < ρ := hγσ.trans hB.2.2.1
  have hκρ : κ < ρ := hκσ.trans hB.2.2.1
  obtain ⟨u1, u2⟩ := hlv_lev1_pi Λ hB (P.lg.trans_lt hγσ) hκσ
  obtain ⟨g1, g2⟩ := P.Fr_pi hB hγσ
  have hq1 : Λ.l ρ + κ + 1 < Om1 := (hlv_G1 Λ hB.2.1 hρ1 hκρ).trans (lgG_facts hB.2.1 hρ1).2.2.1
  have h := glA_pi hB u1 hq1 g1 (gm1_T hB.2.1 hρ1 (P.Fr_lt1 hB.2.1 hρ1 hγρ)).2
  rw [u2, g2] at h
  have hgt : ∀ {y}, InE y → y < Om1 → P.γR < y → κ < y → Λ.l y + κ + 1 < P.Fr y := fun hy hy1 hγy hκy =>
    (hlw_lk1 hy hκy).trans (P.Fr_gt hy hy1 hγy)
  rw [hlv_N_glA Λ hB.2.1 hρ1 hκρ (P.wrfix hB.2.1 hρ1 hγρ (hlw_lk1 hB.2.1 hκρ)) (hgt hB.2.1 hρ1 hγρ hκρ)
      (P.Fr_lt1 hB.2.1 hρ1 hγρ),
    hlv_N_glA Λ hB.1 hσ1 hκσ (P.wrfix hB.1 hσ1 hγσ (hlw_lk1 hB.1 hκσ)) (hgt hB.1 hσ1 hγσ hκσ)
      (P.Fr_lt1 hB.1 hσ1 hγσ)]
  exact h

/-- **`P` AS A BASE OF LEVEL `L + κ`** (code gate `γ`, reading gate `max(γ, κ)`). -/
noncomputable def hlwB (κ : Ordinal.{0}) (hκ : κ < Om1) : HlVB Λ κ where
  F := P.F
  Fr := P.Fr
  γ := P.γ
  γN := max P.γR κ
  Zo := P.hlwZo
  lv := hκ
  γ_le := P.γ_le.trans (le_max_left _ _)
  lvN := le_max_right _ _
  lg := P.lg.trans (le_max_left _ _)
  γN_lt := max_lt P.γR_lt hκ
  F_fix := P.wfix (hlw_Lk hκ)
  G_le := P.G_le
  N_lt1 := (hlw_N_lt_S P hκ).trans P.S_lt1
  F_mem := P.F_mem
  N_mem := fun S _ _ ha hb => by
    rw [hlw_N_eq P hκ]
    exact CSet.phi_mem (CSet.succ_mem (hlv_L_mem Λ S ha (P.lg.trans_lt (max_lt_iff.1 hb).1) (max_lt_iff.1 hb).2))
      (CSet.succ_mem (P.F_mem S ha (P.γ_le.trans_lt (max_lt_iff.1 hb).1)))
  F_code := fun Z hZ hZ1 y hy hQy hyZ =>
    P.F_code Z hZ hZ1 y hy hQy (by exact hyZ.trans (hlw_N_lt_S P hκ))
  F_cl := fun Z hZ hZ1 y hy hQy hyZ =>
    P.F_cl Z hZ hZ1 y hy hQy (by exact hyZ.trans (hlw_N_lt_S P hκ))
  N_cl := fun Z hZ hZ1 h => by
    have hγ0 : P.γ < Z := P.F_cl Z hZ hZ1 _ h (hcN_gt _ _).le (by exact hlw_N_lt_S P hκ)
    rw [hlw_N_eq P hκ, add_assoc] at h
    have hκ1 : κ + 1 < Om1 := gl_Om1_lim.add_one_lt hκ
    have hG : gcG 0 < veblen (Λ.L + (κ + 1)) (P.F + 1) :=
      P.G_le.trans_lt ((lt_add_one _).trans_le (right_le_veblen _ _))
    have hγZ : P.γR < Z := P.γR_cl Z hZ hZ1 hγ0 (hlv_cl_g Λ hκ1 hZ hZ1 (hd_succ_lt (hlv_L0 Λ _) _) hG h le_rfl
      ((isNormal_veblen _).strictMono (lt_add_one _)))
    exact max_lt hγZ ((lt_add_one κ).trans (hlv_cl_gate Λ hκ1 hZ hZ1 (hd_succ_lt (hlv_L0 Λ _) _) hG h le_rfl
      ((isNormal_veblen _).strictMono (lt_add_one _))))
  γN_cl := fun Z hZ hZ1 hγ hκZ hgZ => max_lt (P.γR_cl Z hZ hZ1 hγ hgZ) hκZ
  Fr_gt := fun hx hx1 hγ => (hlw_lk (max_lt_iff.1 hγ).2).trans (P.Fr_gt hx hx1 (max_lt_iff.1 hγ).1)
  Fr_fix := fun hx hx1 hγ => P.wrfix hx hx1 (max_lt_iff.1 hγ).1 (hlw_lk (max_lt_iff.1 hγ).2)
  N_Zo := fun {x} hx _ hγ => by
    rw [P.hlwZo_eq hx (max_lt_iff.1 hγ).1]; exact hlw_rN_lt_S P hx (max_lt_iff.1 hγ).2
  Zo_fix := P.hlwZo_fix
  Zo_G1 := P.hlwZo_G1
  Fr_pi := fun hB hγ => P.Fr_pi hB (max_lt_iff.1 hγ).1
  N_pi := fun hB hγ => hlw_N_pi P hB hγ

theorem hlwB_γN {κ : Ordinal.{0}} (hκ : κ < Om1) : (hlwB P κ hκ).γN = max P.γR κ := rfl

/-- **The level gate from a code of the bound `hdNx (L+Ω₁) F`.** -/
theorem hlw_S_g {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) (h : GxCl Z {gcG 0} (hdNx (Λ.L + Om1) P.F)) :
    Λ.g < Z := by
  obtain ⟨i, hi⟩ := P.F_P
  rw [← hi, hdNx_veb] at h
  have hG : gcG 0 < veblen (Λ.L + Om1) (i + 1) :=
    P.G_le.trans_lt (by rw [← hi]; exact (isNormal_veblen _).strictMono (lt_add_one i))
  have hc := hi_cl_lvl (hlv_L1 Λ Om1) hZ1 (hd_succ_lt (hlv_L0 Λ Om1) _) hG h le_rfl
    ((isNormal_veblen _).strictMono (lt_add_one _))
  have h2 : Λ.L + Om1 < Om 1 * Om 1 := by
    have := Λ.succ.L_add_lt (ν := 0) (by rw [← Br.Om1_eq]; exact gv_Om1_pos)
    rwa [add_zero] at this
  exact Λ.g_cl Z _ hZ hZ1 hc le_self_add h2

end WBase

/-! ## The start of the offset recursion over `P` at level `L + κ` -/

section Start

variable (P : HlWB Λ)

/-- **The shape of a start at `φ(L+κ, F+1)`.** -/
def HlWShape (κ : Ordinal.{0}) (S0 : HgVD) : Prop :=
  S0.B = veblen (Λ.L + κ) (P.F + 1) ∧ (∀ x, InE x → x < Om1 → (S0.γ < x ↔ max P.γR κ < x)) ∧
    (∀ x, InE x → x < Om1 → max P.γR κ < x → S0.b x = veblen (Λ.l x + κ) (P.Fr x + 1)) ∧
    (∀ x, InE x → x < Om1 → S0.Z x = if max P.γR κ < x then evZ (veblen (Λ.l x + κ) (P.Fr x + 1))
      else P.hlwZo x) ∧
    ∀ c σ, P.F ≤ c → c < S0.B → InE σ → σ < Om1 → S0.g c < σ → P.γ < σ

theorem hlw_glA {κ x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : P.γR < x) (hκx : κ < x) :
    glA (Λ.l x + κ) (P.Fr x) x = veblen (Λ.l x + κ) (P.Fr x + 1) := by
  have hfix := P.wrfix hx hx1 hγ (hlw_lk hκx)
  rw [hlv_glA_fixP Λ hx hx1 hκx hfix ((hlw_lk hκx).trans (P.Fr_gt hx hx1 hγ)) (P.Fr_lt1 hx hx1 hγ),
    hdNx_fixP hfix]

/-- **A system of the shape starts the offset recursion over `P` at level `L + κ`.** -/
theorem hlw_start (κ : Ordinal.{0}) (hκ : κ < Om1) (S0 : HgVD) (h : HlWShape P κ S0) :
    HlVStart (hlwB P κ hκ) S0 where
  B := by rw [add_zero]; exact h.1
  Zb := fun x hx hx1 => by
    rw [h.2.2.2.1 x hx hx1]
    by_cases hk : max P.γR κ < x
    · rw [if_pos hk, (hlwB P κ hκ).Zl_eq hx hk]
      exact (hb_evZ_lt_fix2 (hc_fix_down ((show (2 : Ordinal.{0}) ≤ ω from
        (by exact_mod_cast (natCast_lt_omega0 2).le)).trans (hlv_ωl Λ hx hx1).le)
        (hcN_fix _ _)) hc_next_lt_N).le
    · rw [if_neg hk, (hlwB P κ hκ).Zl_low hk]; rfl
  st := fun h2 hZ => {
    ix := by
      show S0.ix = veblen (Λ.L + κ) (P.F + 1 + 0)
      rw [add_zero]
      exact hg_ix_of_B (veblen_veblen_of_lt ((hg_one_lt_Om1.trans_le Λ.OL).trans_le le_self_add) _) h.1
    γ := fun x hx hx1 => by
      show S0.γ < x ↔ max (max P.γR κ) (S0.g 0) < x
      rw [S0.g_zero, max_eq_left zero_le]; exact h.2.1 x hx hx1
    b := fun x hx hx1 hg => by
      have hk : max P.γR κ < x := by
        have : max (max P.γR κ) (S0.g 0) < x := hg
        rwa [S0.g_zero, max_eq_left zero_le] at this
      show S0.b x = glA (Λ.l x + κ) (P.Fr x + S0.R 0 x) x
      rw [S0.R_zero, add_zero, h.2.2.1 x hx hx1 hk,
        hlw_glA P hx hx1 (max_lt_iff.1 hk).1 (max_lt_iff.1 hk).2]
    Z := fun x hx hx1 => by
      unfold HgPB.Zst
      show S0.Z x = if max (max P.γR κ) (S0.g 0) < x then evZ (glA (Λ.l x + κ) (P.Fr x + S0.R 0 x) x)
        else (hlwB P κ hκ).Zl x
      rw [S0.g_zero, max_eq_left zero_le, S0.R_zero, add_zero, h.2.2.2.1 x hx hx1]
      by_cases hk : max P.γR κ < x
      · rw [if_pos hk, if_pos hk, hlw_glA P hx hx1 (max_lt_iff.1 hk).1 (max_lt_iff.1 hk).2]
      · rw [if_neg hk, if_neg hk, (hlwB P κ hκ).Zl_low hk]; rfl }
  high0 := fun c σ hFc hc hσ hσ1 hg => h.2.2.2.2 c σ hFc hc hσ hσ1 hg

end Start

/-! ## The recursion on the level over `P` -/

section LevRec

variable (P : HlWB Λ)

/-- **The shape of the system at level `L + κ` over `P`.** -/
def HlWOK (κ : Ordinal.{0}) (T : HgVD) : Prop :=
  T.B = hcN (Λ.L + κ) P.F ∧ T.γ = max P.γR κ ∧
    (∀ x, InE x → x < Om1 → max P.γR κ < x → T.b x = hcN (Λ.l x + κ) (P.Fr x)) ∧
    (∀ x, InE x → x < Om1 → T.Z x = if max P.γR κ < x then evZ (hcN (Λ.l x + κ) (P.Fr x)) else P.hlwZo x) ∧
    ∀ c σ, P.F ≤ c → c < T.B → InE σ → σ < Om1 → T.g c < σ → P.γ < σ

/-- **The system at level `L + μ` has the shape of a start at level `L + μ + 1`.** -/
theorem hlw_ok_shape {μ : Ordinal.{0}} (hμ : μ + 1 < Om1) {T : HgVD} (h : HlWOK P μ T) :
    HlWShape P (μ + 1) T := by
  have hμ1 : μ < Om1 := (lt_add_one μ).trans hμ
  refine ⟨by rw [h.1, hlw_N_eq P hμ1, add_assoc], fun x hx hx1 => ?_, fun x hx hx1 hk => ?_,
    fun x hx hx1 => ?_, h.2.2.2.2⟩
  · rw [h.2.1]; exact hjw_max_succ hx
  · have hk' : max P.γR μ < x := (hjw_max_succ hx).2 hk
    rw [h.2.2.1 x hx hx1 hk', hlw_rN_eq P hx hx1 (max_lt_iff.1 hk').1 (max_lt_iff.1 hk').2, add_assoc]
  · rw [h.2.2.2.1 x hx hx1]
    by_cases hk : max P.γR μ < x
    · rw [if_pos hk, if_pos ((hjw_max_succ hx).1 hk),
        hlw_rN_eq P hx hx1 (max_lt_iff.1 hk).1 (max_lt_iff.1 hk).2, add_assoc]
    · rw [if_neg hk, if_neg (fun h' => hk ((hjw_max_succ hx).2 h'))]

variable (St0 : HlVStTy Λ 0) (h0 : ∀ Q U h, HlVSpec Q U (St0 Q U h))

open Classical in
/-- **The step of the level recursion over `P`**: the union of all offsets over `P` at level `L + κ`, started at
`S0` (when `S0` has the shape). -/
noncomputable def hlwSt (κ : Ordinal.{0}) (S0 : HgVD) : HgVD :=
  if H : ∃ hκ : κ < Om1, HlWShape P κ S0 ∧ ∀ Q U h, HlVSpec Q U (St0 Q U h) then
    hlVTU (St := hlVLS St0 κ) (fun Q U h => hlVLS_spec St0 H.choose_spec.2 H.choose Q U h)
      (hlw_start P κ H.choose S0 H.choose_spec.1)
  else S0

include h0

theorem hlwSt_eq {κ : Ordinal.{0}} (hκ : κ < Om1) {S0 : HgVD} (h : HlWShape P κ S0) :
    hlwSt P St0 κ S0 = hlVTU (St := hlVLS St0 κ) (fun Q U h => hlVLS_spec St0 h0 hκ Q U h)
      (hlw_start P κ hκ S0 h) := by
  unfold hlwSt; rw [dif_pos ⟨hκ, h, h0⟩]

theorem hlwSt_OK {κ : Ordinal.{0}} (hκ : κ < Om1) {S0 : HgVD} (h : HlWShape P κ S0) :
    HlWOK P κ (hlwSt P St0 κ S0) := by
  rw [hlwSt_eq P St0 h0 hκ h]
  refine ⟨rfl, rfl, fun _ _ _ _ => rfl, fun x _ _ => rfl, fun c σ hFc hc hσ hσ1 hg => ?_⟩
  exact hlVT_high (fun Q U h => hlVLS_spec St0 h0 hκ Q U h) (hlw_start P κ hκ S0 h) hc hFc hσ hσ1 hg

theorem hlwSt_ext {κ : Ordinal.{0}} (hκ : κ < Om1) {S0 : HgVD} (h : HlWShape P κ S0) {c : Ordinal.{0}}
    (hc : c < S0.B) : (∀ x, (hlwSt P St0 κ S0).R c x = S0.R c x) ∧ (hlwSt P St0 κ S0).g c = S0.g c := by
  rw [hlwSt_eq P St0 h0 hκ h]
  exact ⟨fun x => hlVTU_R0 _ _ hc x, hlVTU_g0 _ _ hc⟩

omit h0

/-- **The condition at a limit level.** -/
def HlWCoh (l : Ordinal.{0}) (IH : ∀ κ, κ < l → HgVD) : Prop :=
  (∀ κ (h : κ < l), HlWOK P κ (IH κ h)) ∧ ∀ κ κ' (h : κ < l) (h' : κ' < l), κ ≤ κ' → ∀ c x, c < (IH κ h).B →
    (IH κ' h').R c x = (IH κ h).R c x ∧ (IH κ' h').g c = (IH κ h).g c

section LimCh

variable (l : Ordinal.{0}) (hl : IsSuccLimit l) (hle : l < Om1) (IH : ∀ κ, κ < l → HgVD) (H : HlWCoh P l IH)

include hle in
theorem hlw_NxQ : hdNx (Λ.L + l) P.F = veblen (Λ.L + l) (P.F + 1) := hdNx_fixP (P.wfix (hlw_Lk hle))

theorem hlw_Nxx {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : P.γR < x) (h : l < x) :
    hdNx (Λ.l x + l) (P.Fr x) = veblen (Λ.l x + l) (P.Fr x + 1) := hdNx_fixP (P.wrfix hx hx1 hγ (hlw_lk h))

include hle in
theorem hlw_Nx_lt_S : hdNx (Λ.L + l) P.F < hdNx (Λ.L + Om1) P.F :=
  (hdNx_lt_N (hcN_gt _ _)).trans (hlw_N_lt_S P hle)

include H in
/-- **THE CHAIN AT A LIMIT LEVEL** over `P`. -/
noncomputable def hlwCh : HgfCh where
  D := fun k => IH (heFs l k) (heFs_lt hl (hgf_om hle) k)
  B := hdNx (Λ.L + l) P.F
  b := fun x => hdNx (Λ.l x + l) (P.Fr x)
  γ := max P.γR l
  Zo := P.hlwZo
  γ_lt := max_lt P.γR_lt hle
  γ0 := fun k => by rw [(H.1 _ _).2.1]; exact max_le_max le_rfl (heFs_lt hl (hgf_om hle) k).le
  γ_cl := fun Z hZ hZ1 h => by
    have hγ0 : P.γ < Z := P.F_cl Z hZ hZ1 _ h (hdNx_gt _ _).le (by exact hlw_Nx_lt_S P l hle)
    rw [hlw_NxQ P l hle] at h
    have hG : gcG 0 < veblen (Λ.L + l) (P.F + 1) := P.G_le.trans_lt ((lt_add_one _).trans_le (right_le_veblen _ _))
    have hγZ : P.γR < Z := P.γR_cl Z hZ hZ1 hγ0 (hlv_cl_g Λ hle hZ hZ1 (hd_succ_lt (hlv_L0 Λ _) _) hG h le_rfl
      ((isNormal_veblen _).strictMono (lt_add_one _)))
    exact max_lt hγZ (hlv_cl_gate Λ hle hZ hZ1 (hd_succ_lt (hlv_L0 Λ _) _) hG h le_rfl
      ((isNormal_veblen _).strictMono (lt_add_one _)))
  B_mono := fun k => by
    rw [(H.1 _ _).1, (H.1 _ _).1]
    exact hcN_mono (add_le_add le_rfl (heFs_mono hl (hgf_om hle) k).le) _
  B_lt := fun k => by
    rw [(H.1 _ _).1]
    exact hdN_lt_Nx (hjw_kk_lt l hl hle Λ.L k)
  B_cof := fun c hc => by
    obtain ⟨k, hk⟩ := (hjVLmOf l hl hle).cofNx Λ.L hc
    refine ⟨k, ?_⟩
    rw [(H.1 _ _).1]
    exact hk.trans_le (hdNx_le (hc_LuP_of_fix (hcN_fix _ _) |> hd_LuP_mono le_self_add) (hcN_gt _ _))
  R_ext := fun k c x hc => (H.2 _ _ _ _ (heFs_mono hl (hgf_om hle) k).le c x hc).1
  g_ext := fun k c hc => (H.2 _ _ _ _ (heFs_mono hl (hgf_om hle) k).le c 0 hc).2
  B_lt1 := (hlw_Nx_lt_S P l hle).trans P.S_lt1
  B_fix := hdNx_fix ((hg_one_lt_Om1.trans_le Λ.OL).trans_le le_self_add) _
  B_mem := fun S _ _ ha hb => by
    rw [hlw_NxQ P l hle]
    exact CSet.phi_mem (hlv_L_mem Λ S ha (P.lg.trans_lt (max_lt_iff.1 hb).1) (max_lt_iff.1 hb).2)
      (CSet.succ_mem (P.F_mem S ha (P.γ_le.trans_lt (max_lt_iff.1 hb).1)))
  b_ge := fun k x hx hx1 hγ => by
    have hk := heFs_lt hl (hgf_om hle) k
    rw [(H.1 _ _).2.2.1 x hx hx1 (max_lt (max_lt_iff.1 hγ).1 (hk.trans (max_lt_iff.1 hγ).2))]
    exact (hdN_lt_Nx (hjw_kk_lt l hl hle (Λ.l x) k)).le
  b_cof := fun x hx hx1 hγ μ hμ => by
    obtain ⟨k, hk⟩ := (hjVLmOf l hl hle).cofNx (Λ.l x) hμ
    have hkl := heFs_lt hl (hgf_om hle) k
    refine ⟨k, ?_⟩
    rw [(H.1 _ _).2.2.1 x hx hx1 (max_lt (max_lt_iff.1 hγ).1 (hkl.trans (max_lt_iff.1 hγ).2))]
    exact hk.trans_le (hdNx_le (hc_LuP_of_fix (hcN_fix _ _) |> hd_LuP_mono le_self_add) (hcN_gt _ _))
  b_fix := fun x hx hx1 _ => hdNx_fix (one_lt_omega0.trans (hlv_ωl Λ hx hx1)) _
  b_gt := fun x hx hx1 hγ => (P.Fr_gtx hx hx1 (max_lt_iff.1 hγ).1).trans (hdNx_gt _ _)
  b_lt := fun x hx hx1 hγ =>
    (hdNx_mono (add_le_add le_rfl (max_lt_iff.1 hγ).2.le) _).trans_lt (P.wS_lt1x hx hx1 (max_lt_iff.1 hγ).1)
  b_pi := fun σ ρ hB hγ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hγσ : P.γR < σ := (max_lt_iff.1 hγ).1
    have hlσ : l < σ := (max_lt_iff.1 hγ).2
    have hγρ : P.γR < ρ := hγσ.trans hB.2.2.1
    have hlρ : l < ρ := hlσ.trans hB.2.2.1
    obtain ⟨g1, g2⟩ := P.Fr_pi hB hγσ
    have h := hlv_glA_pi Λ hB (P.lg.trans_lt hγσ) hlσ g1 (P.Fr_lt1 hB.2.1 hρ1 hγρ)
    rw [g2, hlw_glA P hB.2.1 hρ1 hγρ hlρ, hlw_glA P hB.1 hσ1 hγσ hlσ] at h
    rw [hlw_Nxx P l hB.2.1 hρ1 hγρ hlρ, hlw_Nxx P l hB.1 hσ1 hγσ hlσ]
    exact h
  Z_low := fun k x hx hx1 hγ => by
    rw [(H.1 _ _).2.2.2.1 x hx hx1]
    split_ifs with h
    · rw [P.hlwZo_eq hx (max_lt_iff.1 h).1]
      exact (hb_evZ_lt_fix2 (hdNx_fix (lt_of_lt_of_le (show (2 : Ordinal.{0}) < ω from by
          exact_mod_cast natCast_lt_omega0 2) (hlv_ωl Λ hx hx1).le) _)
        (hlw_rN_lt_S P hx (max_lt_iff.1 h).2)).le
    · exact le_rfl
  Zo_fix := fun x => hc_fix_down one_le_two (P.hlwZo_fix x)
  Zo_G1 := fun x hx hx1 => P.hlwZo_G1 x hx hx1

theorem hlwCh_shape : HlWShape P l (hlwCh P l hl hle IH H).U := by
  refine ⟨hlw_NxQ P l hle, fun x _ _ => Iff.rfl, fun x hx hx1 h => hlw_Nxx P l hx hx1 (max_lt_iff.1 h).1
    (max_lt_iff.1 h).2, fun x hx hx1 => ?_, fun c σ hFc hc hσ hσ1 hg => ?_⟩
  · show (if max P.γR l < x then evZ (hdNx (Λ.l x + l) (P.Fr x)) else P.hlwZo x) = _
    by_cases h : max P.γR l < x
    · rw [if_pos h, if_pos h, hlw_Nxx P l hx hx1 (max_lt_iff.1 h).1 (max_lt_iff.1 h).2]
    · rw [if_neg h, if_neg h]
  · set C := hlwCh P l hl hle IH H
    obtain ⟨k, hk⟩ := C.B_cof c hc
    have e : C.U.g c = (C.D k).g c := C.U_g (k := k) hk
    rw [e] at hg
    exact (H.1 _ _).2.2.2.2 c σ hFc hk hσ hσ1 hg

end LimCh

open Classical in
/-- The start at a limit level: the union of the chain (when the condition holds), else `S0`. -/
noncomputable def hlwChU (S0 : HgVD) (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ κ, κ < l → HgVD) : HgVD :=
  if H : ∃ hle : l < Om1, HlWCoh P l IH then (hlwCh P l hl H.choose IH H.choose_spec).U else S0

/-- **THE SYSTEM AT `φ(L+κ+1, F+1)`, BY ONE RECURSION ON THE LEVEL `κ < Ω₁`, OVER `P` FROM THE START `S0`.** -/
noncomputable def hlwL (S0 : HgVD) (κ : Ordinal.{0}) : HgVD :=
  Ordinal.limitRecOn (motive := fun _ => HgVD) κ (hlwSt P St0 0 S0) (fun μ T => hlwSt P St0 (μ + 1) T)
    (fun l hl IH => hlwSt P St0 l (hlwChU P S0 l hl IH))

theorem hlwL_zero (S0 : HgVD) : hlwL P St0 S0 0 = hlwSt P St0 0 S0 := by
  unfold hlwL; rw [Ordinal.limitRecOn_zero]

theorem hlwL_succ (S0 : HgVD) (μ : Ordinal.{0}) : hlwL P St0 S0 (μ + 1) = hlwSt P St0 (μ + 1) (hlwL P St0 S0 μ) := by
  unfold hlwL; rw [Ordinal.limitRecOn_add_one]

theorem hlwL_limit (S0 : HgVD) {l : Ordinal.{0}} (hl : IsSuccLimit l) :
    hlwL P St0 S0 l = hlwSt P St0 l (hlwChU P S0 l hl (fun κ _ => hlwL P St0 S0 κ)) := by
  unfold hlwL; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

include h0 in
/-- **THE INVARIANT**: for a start `S0` of the shape at level `L + 0`, every `hlwL κ`, `κ < Ω₁`, has the shape at
level `L + κ` and extends every `hlwL κ'`, `κ' ≤ κ`. -/
theorem hlwL_inv (S0 : HgVD) (hS0 : HlWShape P 0 S0) :
    ∀ κ, κ < Om1 → HlWOK P κ (hlwL P St0 S0 κ) ∧ ∀ κ', κ' ≤ κ → ∀ c x, c < (hlwL P St0 S0 κ').B →
    (hlwL P St0 S0 κ).R c x = (hlwL P St0 S0 κ').R c x ∧ (hlwL P St0 S0 κ).g c = (hlwL P St0 S0 κ').g c := by
  intro κ
  induction κ using WellFoundedLT.induction with
  | ind κ IH =>
  intro hκ
  rcases zero_or_succ_or_isSuccLimit κ with h0' | ⟨μ, hμ⟩ | hlim
  · subst h0'
    rw [hlwL_zero]
    refine ⟨hlwSt_OK P St0 h0 hκ hS0, fun κ' hκ' c x _ => ?_⟩
    rw [nonpos_iff_eq_zero.1 hκ', hlwL_zero]; exact ⟨rfl, rfl⟩
  · have hμ' : κ = μ + 1 := by rw [← hμ, succ_eq_add_one]
    subst hμ'
    have hμ1 : μ < Om1 := (lt_add_one μ).trans hκ
    obtain ⟨hok, hext⟩ := IH μ (lt_add_one μ) hμ1
    have hsh := hlw_ok_shape P hκ hok
    rw [hlwL_succ]
    refine ⟨hlwSt_OK P St0 h0 hκ hsh, fun κ' hκ' c x hc => ?_⟩
    rcases hκ'.lt_or_eq with hlt | heq
    · have hle : κ' ≤ μ := Order.lt_add_one_iff.1 hlt
      have hcμ : c < (hlwL P St0 S0 μ).B := by
        rw [hok.1]; rw [(IH κ' (lt_of_le_of_lt hle (lt_add_one μ)) (hle.trans_lt hμ1)).1.1] at hc
        exact hc.trans_le (hcN_mono (add_le_add le_rfl hle) _)
      obtain ⟨r2, g2⟩ := hext κ' hle c x hc
      exact ⟨((hlwSt_ext P St0 h0 hκ hsh hcμ).1 x).trans r2, (hlwSt_ext P St0 h0 hκ hsh hcμ).2.trans g2⟩
    · subst heq; rw [hlwL_succ]; exact ⟨rfl, rfl⟩
  · have hcoh : HlWCoh P κ (fun κ' _ => hlwL P St0 S0 κ') :=
      ⟨fun κ' h => (IH κ' h (h.trans hκ)).1, fun κ₁ κ₂ h₁ h₂ h12 c x hc =>
        (IH κ₂ h₂ (h₂.trans hκ)).2 κ₁ h12 c x hc⟩
    have eU : hlwChU P S0 κ hlim (fun κ' _ => hlwL P St0 S0 κ') =
        (hlwCh P κ hlim hκ (fun κ' _ => hlwL P St0 S0 κ') hcoh).U := by
      unfold hlwChU; rw [dif_pos ⟨hκ, hcoh⟩]
    have hsh := hlwCh_shape P κ hlim hκ (fun κ' _ => hlwL P St0 S0 κ') hcoh
    rw [hlwL_limit P St0 S0 hlim, eU]
    refine ⟨hlwSt_OK P St0 h0 hκ hsh, fun κ' hκ' c x hc => ?_⟩
    rcases hκ'.lt_or_eq with hlt | heq
    · obtain ⟨k, hk⟩ := heFs_cof hlim (hgf_om hκ) κ' hlt
      have hkl := heFs_lt hlim (hgf_om hκ) k
      obtain ⟨hokk, hextk⟩ := IH _ hkl (hkl.trans hκ)
      have hck : c < (hlwL P St0 S0 (heFs κ k)).B := by
        rw [hokk.1]; rw [(IH κ' hlt (hlt.trans hκ)).1.1] at hc
        exact hc.trans_le (hcN_mono (add_le_add le_rfl hk.le) _)
      set C := hlwCh P κ hlim hκ (fun κ' _ => hlwL P St0 S0 κ') hcoh with hC
      have hcC : c < C.U.B := hck.trans (C.B_lt k)
      obtain ⟨r2, g2⟩ := hextk κ' hk.le c x hc
      refine ⟨((hlwSt_ext P St0 h0 hκ hsh hcC).1 x).trans ((C.U_R (k := k) hck x).trans r2),
        (hlwSt_ext P St0 h0 hκ hsh hcC).2.trans ((C.U_g (k := k) hck).trans g2)⟩
    · subst heq; rw [hlwL_limit P St0 S0 hlim, eU]; exact ⟨rfl, rfl⟩

end LevRec

end Googology.Trans.PoR.InaccPsi.R2.Hl

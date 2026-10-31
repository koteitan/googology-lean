import Googology.Trans.PoR.InaccPsi.R2.HoLv

/-!
# HoW: ONE TWO-GATE BASE FOR EVERY LEVEL BELOW THE NEXT PREFIX, FROM ONE BASE DATUM

Generalizes `Hn.hnQW` (a pseudo-base of the level `Ω₁·Ω₁` as a two-gate base of every `Hl.HlLv`) and `Hn.hnGW` (`G` as a
two-gate base of every band datum) to ONE construction: a base datum `D : HoWD v` (a point `F` fixed by every level
below `Ω₁²·(v+1)`, a reading `Fr` fixed by every level below `x·x·(v+1)`, a code gate `γ`, an outer low field `Zo`)
gives a two-gate base `hoW D Λ h : Hn.HnWB Λ` of every level `Λ` below the next prefix (`h : HoGood v Λ`), with the
reading gate `max γ Λ.g`.  What differs from `Hn.hnQW` / `Hn.hnGW`: the next prefix `Ω₁²·(v+1)` in place of `Ω₁²`
(resp. `Ω₁²·2`), the datum `Hn.HnLv` in place of `Hl.HlLv` for the pseudo-base case, the outer low field of `G` is
`hoZo` (`φ(x·x·x, Γ_{x+1}+1)`, one field for every prefix) in place of `φ(x·x·2, Γ_{x+1}+1)`.

* `HoWD`, `hoW` (**THE TWO-GATE BASE**), `hoW_S_pi` (Lemma EXACT for `hdNx (ℓ(ρ)+ρ) (F(ρ))`);
* `hoGD v` (**`G` as a base datum**), `hoQD Q` (**a pseudo-base of the prefix `Ω₁²·(v+1)` as a base datum**);
* `hoWU_shape` (**the union over `hoW D Λ` started at a start over it is a start over `hoW D Λ.succ`**);
* `hoQ_shape_dn` (**a system with the specification of a lower level `Λ₀` at `Q.lowr Λ₀` is a start over
  `hoW (hoQD Q) Λ₀`**).

No new axiom.  New definitions: `HoWD`, `hoW`, `hoGD`, `hoQD`.
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

/-- **A base datum below the next prefix `Ω₁²·(v+1)`**: a point `F` fixed by every level below `Ω₁²·(v+1)`, a reading
`Fr` fixed by every level below `x·x·(v+1)` (above the code gate `γ` and the prefix gate `hlGt v`), an outer low field
`Zo`. -/
structure HoWD (v : Ordinal.{0}) where
  F : Ordinal.{0}
  Fr : Ordinal.{0} → Ordinal.{0}
  γ : Ordinal.{0}
  Zo : Ordinal.{0} → Ordinal.{0}
  γ_lt : γ < Om1
  F_fix : ∀ α, α < Om1 * Om1 * (v + 1) → veblen α F = F
  G_le : gcG 0 ≤ F
  S_lt1 : hdNx (Om1 * Om1 * (v + 1)) F < gcG 1
  F_mem : ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}}, 0 < a → γ < b → F ∈ S.CSet a b
  F_code : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → ∀ y, GxCl Z {gcG 0} y → F ≤ y →
    y < hdNx (Om1 * Om1 * (v + 1)) F → GxCl Z {gcG 0} F
  F_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → ∀ y, GxCl Z {gcG 0} y → F ≤ y →
    y < hdNx (Om1 * Om1 * (v + 1)) F → γ < Z
  Fr_fix : ∀ {x}, InE x → x < Om1 → γ < x → hlGt v < x → ∀ α, α < x * x * (v + 1) → veblen α (Fr x) = Fr x
  Fr_gt : ∀ {x}, InE x → x < Om1 → γ < x → hlGt v < x → x * x * (v + 1) ≤ Fr x
  S_Zo : ∀ {x}, InE x → x < Om1 → γ < x → hlGt v < x → hdNx (x * x * (v + 1)) (Fr x) < Zo x
  Zo_fix : ∀ x, veblen 2 (Zo x) = Zo x
  Zo_G1 : ∀ x, InE x → x < Om1 → Zo x < gq 1 x
  Fr_pi : ∀ {σ ρ}, Bases σ ρ → γ < σ → Fr ρ ∈ TB ρ σ ∧ pi σ ρ (Fr ρ) = Fr σ
  F_P : LuP (Om1 * Om1 * (v + 1)) F
  S_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → GxCl Z {gcG 0} (hdNx (Om1 * Om1 * (v + 1)) F) →
    max γ (hlGt (v + 1)) < Z
  S_mem : ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}}, 0 < a → max γ (hlGt v) < b →
    hdNx (Om1 * Om1 * (v + 1)) F ∈ S.CSet a b
  Fr_P : ∀ {x}, InE x → x < Om1 → γ < x → hlGt v < x → LuP (x * x * (v + 1)) (Fr x)
  S_pi : ∀ {σ ρ}, Bases σ ρ → max γ (hlGt v) < σ → hdNx (ρ * ρ * (v + 1)) (Fr ρ) ∈ TB ρ σ ∧
    pi σ ρ (hdNx (ρ * ρ * (v + 1)) (Fr ρ)) = hdNx (σ * σ * (v + 1)) (Fr σ)

namespace HoWD

variable {v : Ordinal.{0}} (D : HoWD v) {Λ : HnLv} (h : HoGood v Λ)
include h

omit D in
theorem goodL : Λ.L + Om1 < Om1 * Om1 * (v + 1) := (lt_add_one _).trans h.1

theorem Ffix : veblen (Λ.L + Om1) D.F = D.F := D.F_fix _ (goodL h)

theorem S_lt : hdNx (Λ.L + Om1) D.F < hdNx (Om1 * Om1 * (v + 1)) D.F :=
  (hdNx_lt_N (hcN_gt _ _)).trans (hdN_lt_Nx h.1)

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : D.γ < x) (hg : Λ.g < x)
include hx hx1 hγ hg

theorem rfix : veblen (Λ.l x + x) (D.Fr x) = D.Fr x :=
  D.Fr_fix hx hx1 hγ (h.2.1.trans_lt hg) _ (h.2.2 x hx hx1 hg)

theorem rgt : Λ.l x + x < D.Fr x := (h.2.2 x hx hx1 hg).trans_le (D.Fr_gt hx hx1 hγ (h.2.1.trans_lt hg))

theorem rlt1 : D.Fr x < gq 1 x :=
  ((hdNx_gt _ _).trans (D.S_Zo hx hx1 hγ (h.2.1.trans_lt hg))).trans (D.Zo_G1 x hx hx1)

theorem rS_Zo : hdNx (Λ.l x + x) (D.Fr x) < D.Zo x :=
  (hdNx_mono (h.2.2 x hx hx1 hg).le _).trans_lt (D.S_Zo hx hx1 hγ (h.2.1.trans_lt hg))

end Base

end HoWD

/-- **Lemma EXACT for `hdNx (ℓ(ρ)+ρ) (F(ρ))`** above both gates (the proof of `Hn.hnq_S_pi` with `Hn.hnv_glA_pi`). -/
theorem hoW_S_pi {v : Ordinal.{0}} (D : HoWD v) {Λ : HnLv} (h : HoGood v Λ) {σ ρ : Ordinal.{0}} (hB : Bases σ ρ)
    (hγ : D.γ < σ) (hg : Λ.g < σ) :
    hdNx (Λ.l ρ + ρ) (D.Fr ρ) ∈ TB ρ σ ∧ pi σ ρ (hdNx (Λ.l ρ + ρ) (D.Fr ρ)) = hdNx (Λ.l σ + σ) (D.Fr σ) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hγρ : D.γ < ρ := hγ.trans hB.2.2.1
  have hgρ : Λ.g < ρ := hg.trans hB.2.2.1
  obtain ⟨f1, f2⟩ := D.Fr_pi hB hγ
  have hh := hnv_glA_pi Λ.succ hB hg hB.1.pos f1 (D.rlt1 h hB.2.1 hρ1 hγρ hgρ)
  have hfρ : veblen (Λ.succ.l ρ + 0) (D.Fr ρ) = D.Fr ρ := by rw [add_zero]; exact D.rfix h hB.2.1 hρ1 hγρ hgρ
  have hfσ : veblen (Λ.succ.l σ + 0) (D.Fr σ) = D.Fr σ := by rw [add_zero]; exact D.rfix h hB.1 hσ1 hγ hg
  have hgtρ : Λ.succ.l ρ + 0 < D.Fr ρ := by rw [add_zero]; exact D.rgt h hB.2.1 hρ1 hγρ hgρ
  have hgtσ : Λ.succ.l σ + 0 < D.Fr σ := by rw [add_zero]; exact D.rgt h hB.1 hσ1 hγ hg
  rw [f2, hnv_glA_fixP Λ.succ hB.2.1 hρ1 (hB.1.pos.trans hB.2.2.1) hfρ hgtρ (D.rlt1 h hB.2.1 hρ1 hγρ hgρ),
    hnv_glA_fixP Λ.succ hB.1 hσ1 hB.1.pos hfσ hgtσ (D.rlt1 h hB.1 hσ1 hγ hg)] at hh
  simpa only [HnLv.succ_l, add_zero] using hh

/-- **THE TWO-GATE BASE OF A LEVEL `Λ` BELOW THE NEXT PREFIX**: point `F`, reading `Fr`, outer low field `Zo`, code
gate `γ`, reading gate `max γ Λ.g`. -/
noncomputable def hoW {v : Ordinal.{0}} (D : HoWD v) (Λ : HnLv) (h : HoGood v Λ) : HnWB Λ where
  F := D.F
  Fr := D.Fr
  γ := D.γ
  γR := max D.γ Λ.g
  Zo := D.Zo
  γ_lt := D.γ_lt
  γR_lt := max_lt D.γ_lt Λ.g_lt
  γ_le := le_max_left _ _
  lg := le_max_right _ _
  γR_cl := fun _ _ _ h1 h2 => max_lt h1 h2
  F_P := ⟨D.F, D.Ffix h⟩
  G_le := D.G_le
  S_lt1 := (hdNx_mono (HoWD.goodL h).le _).trans_lt D.S_lt1
  F_mem := D.F_mem
  S_mem := fun S _ _ ha hb => by
    rw [hdNx_fixP (D.Ffix h)]
    exact CSet.phi_mem (Λ.succ.L_mem S _ _ ha ((le_max_right _ _).trans_lt hb))
      (CSet.succ_mem (D.F_mem S ha ((le_max_left _ _).trans_lt hb)))
  F_code := fun Z hZ hZ1 y hy hQy hyZ => D.F_code Z hZ hZ1 y hy hQy (hyZ.trans_le (hdNx_mono (HoWD.goodL h).le _))
  F_cl := fun Z hZ hZ1 y hy hQy hyZ => D.F_cl Z hZ hZ1 y hy hQy (hyZ.trans_le (hdNx_mono (HoWD.goodL h).le _))
  S_cl := fun Z hZ hZ1 hc => D.F_cl Z hZ hZ1 _ hc (hdNx_gt _ _).le (D.S_lt h)
  Fr_gt := fun hx hx1 hγ => D.rgt h hx hx1 ((le_max_left _ _).trans_lt hγ) ((le_max_right _ _).trans_lt hγ)
  Fr_P := fun hx hx1 hγ => ⟨_, D.rfix h hx hx1 ((le_max_left _ _).trans_lt hγ) ((le_max_right _ _).trans_lt hγ)⟩
  S_Zo := fun hx hx1 hγ => D.rS_Zo h hx hx1 ((le_max_left _ _).trans_lt hγ) ((le_max_right _ _).trans_lt hγ)
  Zo_fix := D.Zo_fix
  Zo_G1 := D.Zo_G1
  Fr_pi := fun hB hγ => D.Fr_pi hB ((le_max_left _ _).trans_lt hγ)
  S_pi := fun hB hγ => hoW_S_pi D h hB ((le_max_left _ _).trans_lt hγ) ((le_max_right _ _).trans_lt hγ)

section WAPI

variable {v : Ordinal.{0}} (D : HoWD v) (Λ : HnLv) (h : HoGood v Λ)

theorem hoW_F : (hoW D Λ h).F = D.F := rfl

theorem hoW_Fr : (hoW D Λ h).Fr = D.Fr := rfl

theorem hoW_γ : (hoW D Λ h).γ = D.γ := rfl

theorem hoW_γR : (hoW D Λ h).γR = max D.γ Λ.g := rfl

theorem hoW_Zo_low {x : Ordinal.{0}} (hx : ¬ max D.γ Λ.g < x) : (hoW D Λ h).hnwZo x = D.Zo x :=
  (hoW D Λ h).hnwZo_low hx

/-- **The base depends only on the level datum.** -/
theorem hoW_congr {Λ' : HnLv} (e : Λ = Λ') (h' : HoGood v Λ') {κ : Ordinal.{0}} {S : HgVD}
    (hS : HnWShape (hoW D Λ h) κ S) : HnWShape (hoW D Λ' h') κ S := by
  subst e; exact hS

end WAPI

/-! ## `G` as a base datum -/

theorem ho_next_lt_G {v : Ordinal.{0}} (hv : v < Om1) (α : Ordinal.{0}) : (Om1 : Ordinal.{0}) * Om1 * (v + 1) < gcG α :=
  ho_sqv_lt_G (gl_Om1_lim.add_one_lt hv) α

theorem ho_xnext_one {x v : Ordinal.{0}} (hx : InE x) : (1 : Ordinal.{0}) ≤ x * x * (v + 1) :=
  ((one_lt_omega0.trans (omega0_lt_inE hx)).le.trans (hl_lt_sq hx).le).trans
    (le_mul_of_one_le_right' (Order.one_le_iff_pos.2 (Order.lt_add_one_iff.2 zero_le)))

theorem ho_xnext_lt {x v : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hv : v < x) : x * x * (v + 1) < lgG x :=
  (ho_next_lt3 hx hv).trans (ho_cube_lt hx hx1)

/-- **`G` AS A BASE DATUM BELOW `Ω₁²·(v+1)`** (code gate `0`, reading `Γ_{x+1}`, outer low field `hoZo`). -/
noncomputable def hoGD (v : Ordinal.{0}) (hv : v < Om1) : HoWD v where
  F := gcG 0
  Fr := lgG
  γ := 0
  Zo := hoZo
  γ_lt := gv_Om1_pos
  F_fix := fun _ hα => gn_veb_fix (gcG_SC 0) (hα.trans (ho_next_lt_G hv 0))
  G_le := le_rfl
  S_lt1 := by
    have hG1 := gcG_SC 1
    have hE := Low.opow_eq_self_of_SC hG1
    have hfix : veblen (Om1 * Om1 * (v + 1)) (gcG 1) = gcG 1 := gn_veb_fix hG1 (ho_next_lt_G hv 1)
    have h2 := (isNormal_veblen (Om1 * Om1 * (v + 1))).strictMono
      ((ev_isSuccLimit_of_inE hE).add_one_lt (gcG_lt zero_lt_one))
    rw [hdNx_fixP (gn_veb_fix (gcG_SC 0) (ho_next_lt_G hv 0))]; rwa [hfix] at h2
  F_mem := fun S _ _ ha _ => gmS_G0_mem S ha
  F_code := fun _ _ _ _ _ _ _ => GxCl.atom (Set.mem_singleton _)
  F_cl := fun _ hZ _ _ _ _ _ => hZ.1
  Fr_fix := fun {x} hx hx1 _ hv' α hα =>
    hc_fix_down hα.le (hjG_fix hx hx1 (ho_xnext_one hx) (ho_xnext_lt hx hx1 (hl_gt_E hx hv')))
  Fr_gt := fun {x} hx hx1 _ hv' => (ho_xnext_lt hx hx1 (hl_gt_E hx hv')).le
  S_Zo := fun {x} hx hx1 _ hv' => hoZo_gtG hx hx1 (ho_xnext_one hx) (ho_next_lt3 hx (hl_gt_E hx hv'))
  Zo_fix := hoZo_fix
  Zo_G1 := hoZo_G1
  Fr_pi := fun hB _ => Go.goGl.ba_pi _ _ hB
  F_P := ⟨gcG 0, gn_veb_fix (gcG_SC 0) (ho_next_lt_G hv 0)⟩
  S_cl := fun Z hZ hZ1 h => by
    have hfix := gn_veb_fix (gcG_SC 0) (ho_next_lt_G hv 0)
    rw [hdNx_fixP hfix] at h
    have h1 : (1 : Ordinal.{0}) ≤ Om1 * Om1 * (v + 1) := (hg_one_lt_Om1.le.trans
      (le_mul_of_one_le_right' hg_one_lt_Om1.le)).trans
        (ho_xsq_le (Order.one_le_iff_pos.2 (Order.lt_add_one_iff.2 zero_le)))
    have hne : Om1 * Om1 * (v + 1) ≠ 0 := (zero_lt_one.trans_le h1).ne'
    have hG : gcG 0 < veblen (Om1 * Om1 * (v + 1)) (gcG 0 + 1) := (lt_add_one _).trans_le (right_le_veblen _ _)
    have hc := hi_cl_lvl h1 hZ1 (hd_succ_lt hne _) hG h le_rfl ((isNormal_veblen _).strictMono (lt_add_one _))
    have hlo : Om1 * Om1 * (v + 1) ≤ Om1 * Om1 * (v + 1) := le_rfl
    have hhi : Om1 * Om1 * (v + 1) < Om1 * Om1 * Om1 :=
      mul_lt_mul_of_pos_left (gl_Om1_lim.add_one_lt hv) ho_OO_pos
    exact max_lt hZ.1 ((hlGt_le (v + 1)).trans_lt (ho_cl_sq hZ hZ1 hc hlo hhi))
  S_mem := fun S _ _ ha hb => by
    rw [hdNx_fixP (gn_veb_fix (gcG_SC 0) (ho_next_lt_G hv 0)), mul_add_one]
    exact CSet.phi_mem (CSet.add_mem (ho_sqmul_mem S _ _ v (ho_gt_or ((le_max_right _ _).trans_lt hb)))
      (hl_OO_mem S _ _)) (CSet.succ_mem (gmS_G0_mem S ha))
  Fr_P := fun {x} hx hx1 _ hv' => ⟨_, hjG_fix hx hx1 (ho_xnext_one hx) (ho_xnext_lt hx hx1 (hl_gt_E hx hv'))⟩
  S_pi := fun {σ ρ} hB hγ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hvσ : v < σ := hl_gt_E hB.1 ((le_max_right _ _).trans_lt hγ)
    have hvρ : v < ρ := hvσ.trans hB.2.2.1
    have hp := ho_pi_sqmul hB (v + 1) ((ev_isSuccLimit_of_inE hB.1).add_one_lt hvσ)
    exact hjG_S_pi hB hp (ho_xnext_one hB.2.1) (ho_xnext_lt hB.2.1 hρ1 hvρ) (ho_xnext_one hB.1)
      (ho_xnext_lt hB.1 hσ1 hvσ)

theorem hoGD_γ (v : Ordinal.{0}) (hv : v < Om1) : (hoGD v hv).γ = 0 := rfl

/-! ## A pseudo-base of the next prefix as a base datum -/

section QD

variable {v : Ordinal.{0}} {Λ' : HnLv} (Q : HnVQ Λ' 0) (hL' : Λ'.L = Om1 * Om1 * (v + 1))
  (hl' : ∀ x, Λ'.g < x → Λ'.l x = x * x * (v + 1)) (hg' : hlGt (v + 1) ≤ Λ'.g)

include hL' in
theorem hoQ_S : hdNx (Λ'.L + 0) Q.F = hdNx (Om1 * Om1 * (v + 1)) Q.F := by rw [add_zero, hL']

include hl' in
theorem hoQ_r {x : Ordinal.{0}} (hγ : Q.γ < x) : Λ'.l x + 0 = x * x * (v + 1) := by
  rw [add_zero, hl' x (Q.lg.trans_lt hγ)]

/-- **A PSEUDO-BASE OF THE PREFIX `Ω₁²·(v+1)` AS A BASE DATUM BELOW IT** (the same point, reading, gate, outer low
field). -/
noncomputable def hoQD : HoWD v where
  F := Q.F
  Fr := Q.Fr
  γ := Q.γ
  Zo := Q.Zo
  γ_lt := Q.γ_lt
  F_fix := fun α hα => by
    obtain ⟨a, ha⟩ := Q.F_P; rw [← ha]
    exact veblen_veblen_of_lt (by rw [add_zero, hL']; exact hα) a
  G_le := Q.G_lt.le
  S_lt1 := by rw [← hoQ_S Q hL']; exact Q.S_lt1
  F_mem := Q.F_mem
  F_code := fun Z hZ hZ1 y hy hQy hyZ => Q.F_code Z hZ hZ1 y hy hQy (by rw [hoQ_S Q hL']; exact hyZ)
  F_cl := fun Z hZ hZ1 y hy hQy hyZ => Q.F_cl Z hZ hZ1 y hy hQy (by rw [hoQ_S Q hL']; exact hyZ)
  Fr_fix := fun {x} hx hx1 hγ _ α hα => by
    obtain ⟨a, ha⟩ := Q.Fr_P hx hx1 hγ; rw [← ha]
    exact veblen_veblen_of_lt (by rw [hoQ_r Q hl' hγ]; exact hα) a
  Fr_gt := fun {x} hx hx1 hγ _ => by have := Q.Fr_gt hx hx1 hγ; rw [hoQ_r Q hl' hγ] at this; exact this.le
  S_Zo := fun {x} hx hx1 hγ _ => by have := Q.S_Zo hx hx1 hγ; rwa [hoQ_r Q hl' hγ] at this
  Zo_fix := Q.Zo_fix
  Zo_G1 := Q.Zo_G1
  Fr_pi := fun hB hγ => Q.Fr_pi hB hγ
  F_P := by have := Q.F_P; rwa [add_zero, hL'] at this
  S_cl := fun Z hZ hZ1 h => by
    have hc := Q.S_cl Z hZ hZ1 (by rw [hoQ_S Q hL']; exact h)
    exact max_lt hc ((hg'.trans Q.lg).trans_lt hc)
  S_mem := fun S _ _ ha hb => by rw [← hoQ_S Q hL']; exact Q.S_mem S ha ((le_max_left _ _).trans_lt hb)
  Fr_P := fun {x} hx hx1 hγ _ => by have := Q.Fr_P hx hx1 hγ; rwa [hoQ_r Q hl' hγ] at this
  S_pi := fun {σ ρ} hB hγ => by
    have hγσ : Q.γ < σ := (le_max_left _ _).trans_lt hγ
    have := Q.S_pi hB hγσ
    rwa [hoQ_r Q hl' (hγσ.trans hB.2.2.1), hoQ_r Q hl' hγσ] at this

theorem hoQD_F : (hoQD Q hL' hl' hg').F = Q.F := rfl

theorem hoQD_γ : (hoQD Q hL' hl' hg').γ = Q.γ := rfl

theorem hoQD_Zo : (hoQD Q hL' hl' hg').Zo = Q.Zo := rfl

end QD

/-! ## The union over a base starts the next level -/

/-- **The union over `hoW D Λ` started at a start over it is a start over `hoW D Λ.succ`.** -/
theorem hoWU_shape {v : Ordinal.{0}} (D : HoWD v) (Λ : HnLv) (h : HoGood v Λ) (h' : HoGood v Λ.succ)
    (St0 : HnVStTy Λ 0) (h0 : ∀ Q U h, HnVSpec Q U (St0 Q U h)) (S0 : HgVD) (hS0 : HnWShape (hoW D Λ h) 0 S0) :
    HnWShape (hoW D Λ.succ h') 0 (hnwU (hoW D Λ h) St0 h0 S0 hS0) := by
  have hmx : ∀ x : Ordinal.{0}, max (max D.γ Λ.succ.g) 0 < x ↔ max D.γ Λ.g < x := fun x => by
    rw [max_eq_left zero_le]; rfl
  refine ⟨?_, fun x _ _ => ?_, fun x hx hx1 hk => ?_, fun x hx hx1 => ?_, fun c σ hFc hc hσ hσ1 hg => ?_⟩
  · show hdNx (Λ.L + Om1) D.F = veblen (Λ.succ.L + 0) (D.F + 1)
    rw [add_zero, hdNx_fixP (D.Ffix h)]; rfl
  · show max D.γ Λ.g < x ↔ max (max D.γ Λ.succ.g) 0 < x
    rw [hmx]
  · have hk' : max D.γ Λ.g < x := (hmx x).1 hk
    show hdNx (Λ.l x + x) (D.Fr x) = veblen (Λ.succ.l x + 0) (D.Fr x + 1)
    rw [add_zero, hdNx_fixP (D.rfix h hx hx1 (max_lt_iff.1 hk').1 (max_lt_iff.1 hk').2)]; rfl
  · show hnwUZ (hoW D Λ h) x = if max (max D.γ Λ.succ.g) 0 < x then evZ (veblen (Λ.succ.l x + 0) (D.Fr x + 1))
      else (hoW D Λ.succ h').hnwZo x
    unfold hnwUZ
    by_cases hg : max D.γ Λ.g < x
    · rw [if_pos (show (hoW D Λ h).γR < x from hg), if_pos ((hmx x).2 hg), add_zero]
      show evZ (hdNx (Λ.l x + x) (D.Fr x)) = evZ (veblen (Λ.l x + x) (D.Fr x + 1))
      rw [hdNx_fixP (D.rfix h hx hx1 (max_lt_iff.1 hg).1 (max_lt_iff.1 hg).2)]
    · rw [if_neg (show ¬ (hoW D Λ h).γR < x from hg), if_neg (fun h' => hg ((hmx x).1 h')),
        (hoW D Λ.succ h').hnwZo_low (show ¬ (hoW D Λ.succ h').γR < x from hg)]
      rfl
  · by_cases hSc : S0.B ≤ c
    · exact (le_max_left _ _).trans_lt (hnwU_highR (hoW D Λ h) St0 h0 S0 hS0 hSc hc hσ hσ1 hg)
    · have hc0 : c < S0.B := not_le.1 hSc
      rw [hnwU_g0 (hoW D Λ h) St0 h0 S0 hS0 hc0] at hg
      exact hS0.2.2.2.2 c σ hFc hc0 hσ hσ1 hg

/-! ## The start at a pseudo-base -/

section Dn

variable {v : Ordinal.{0}} {Λ' : HnLv} (Q : HnVQ Λ' 0) (hL' : Λ'.L = Om1 * Om1 * (v + 1))
  (hl' : ∀ x, Λ'.g < x → Λ'.l x = x * x * (v + 1)) (hg' : hlGt (v + 1) ≤ Λ'.g) (Λ₀ : HnLv) (hg : Λ₀.g ≤ Λ'.g)
  (hL : Λ₀.L + Om1 ≤ Λ'.L)
  (hl : ∀ x, InE x → x < Om1 → Λ'.g < x → Λ₀.l x + x ≤ Λ'.l x) (h₀ : HoGood v Λ₀)

/-- **A system with the specification of the level `Λ₀ + 0` at `Q.lowr Λ₀` is a start over `hoW (hoQD Q) Λ₀`.** -/
theorem hoQ_shape_dn {U T : HgVD} (hT : HnVSpec (Q.lowr Λ₀ hg hL hl) U T) :
    HnWShape (hoW (hoQD Q hL' hl' hg') Λ₀ h₀) 0 T := by
  have hmx : ∀ x : Ordinal.{0}, max (max Q.γ Λ₀.g) 0 < x ↔ Q.γ < x := fun x => by
    rw [max_eq_left zero_le, max_eq_left (hg.trans Q.lg)]
  have hfix : veblen (Λ₀.L + 0) Q.F = Q.F := (hoQD Q hL' hl' hg').F_fix _
    ((add_zero Λ₀.L).trans_lt ((lt_add_of_pos_right _ gv_Om1_pos).trans (HoWD.goodL h₀)))
  have hrfix : ∀ x, InE x → x < Om1 → Q.γ < x → veblen (Λ₀.l x + 0) (Q.Fr x) = Q.Fr x := fun x hx hx1 hγ =>
    hc_fix_down (by rw [add_zero]; exact le_self_add)
      ((hoQD Q hL' hl' hg').rfix h₀ hx hx1 hγ ((hg.trans Q.lg).trans_lt hγ))
  refine ⟨?_, fun x _ _ => ?_, fun x hx hx1 hγ => ?_, fun x hx hx1 => ?_, fun c σ hFc hc hσ hσ1 hgc => ?_⟩
  · rw [hT.B]; exact hdNx_fixP hfix
  · rw [hT.γ]; exact (hmx x).symm
  · have hγ' : Q.γ < x := (hmx x).1 hγ
    rw [hT.b x hx hx1 hγ']; exact hdNx_fixP (hrfix x hx hx1 hγ')
  · rw [hT.Z x hx hx1]
    show (if Q.γ < x then evZ (hdNx (Λ₀.l x + 0) (Q.Fr x)) else Q.Zo x) =
      if max (max Q.γ Λ₀.g) 0 < x then evZ (veblen (Λ₀.l x + 0) (Q.Fr x + 1))
        else (hoW (hoQD Q hL' hl' hg') Λ₀ h₀).hnwZo x
    by_cases hγ : Q.γ < x
    · rw [if_pos hγ, if_pos ((hmx x).2 hγ), hdNx_fixP (hrfix x hx hx1 hγ)]
    · rw [if_neg hγ, if_neg (fun h' => hγ ((hmx x).1 h')), hoW_Zo_low]
      · rfl
      · exact fun h' => hγ ((le_max_left _ _).trans_lt h')
  · refine hT.high c σ hFc ?_ hσ hσ1 hgc
    rw [← hT.B]; exact hc

end Dn

end Googology.Trans.PoR.InaccPsi.R2.Ho

import Googology.Trans.PoR.InaccPsi.R2.HjWP
import Googology.Trans.PoR.InaccPsi.R2.HjLoc

/-!
# HjWG: `G` AS A BASE OF EVERY LEVEL `L + Ω₁`; EVERY `φ(Ω₁·(n+2), G+1)` IS LOCATED; THE FRONTIER `ι(Γ(φ(Ω₁·ω, G+1)))`

`G = Γ_{Ω₁+1}` is a base of every level `L + Ω₁` (`hjGW Λ`: gate `0`, reading `Γ_{x+1}`).  Starting at `Hg.hgU`
(bound `φ(Ω₁, G+1)`), the union of all levels `L + κ` over `G` with the package `Hj.hjPkN n` (`Hj.hjwU`) is a start of
the next package: one recursion on `n < ω` gives the systems `hjGU n` with the bound `φ(Ω₁·(n+2), G+1)`, the base
gate `0` and the base reading `φ(x·(n+2), Γ_{x+1}+1)` (the level `Ω₁·(n+2)` read as `x·(n+2)`).  Each is located
(`Hg.hgV_locD`, gate `0 < K`); their bounds are cofinal in `φ(Ω₁·ω, G+1)`: ENUM-REACH and CapV hold at every range
restart below `ι(Γ(φ(Ω₁·ω, G+1)))`, UNCONDITIONALLY.

* `hjG_glA`, `hjG_S_pi`, `hjGW` (**`G` AS A BASE OF LEVEL `L + Ω₁`**), `hjGU_shape`, `hgU_shapeJ`, `hjGCg`, `hjGC`,
  `hjGU`
  (**THE SYSTEM AT `φ(Ω₁·(n+2), G+1)`**), `hjGU_γ`, `hjGU_B`;
* `hjGU_loc`, `hjGU_blk`, `hjGE`, `hjGE_cofB`, `hjGE_cof`, `hjGE_enum`, `hjGE_capV`, `hjGE_road`, `hjGE_lt1`,
  `hjGE_lt_Om2`, `hjGE_P`, `hjGE_fr_order`.

No new axiom.  New definitions: `hjGW`, `hjGCg`, `hjGC`, `hjGU`, `hjGE`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hj

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

/-! ## `G` as a base of level `L + Ω₁` -/

section GBase

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem hjG_fix {q : Ordinal.{0}} (h1 : 1 ≤ q) (hq : q < lgG x) : veblen q (lgG x) = lgG x :=
  hc_G_fix hx hx1 h1 hq

/-- **`ϑˣ(Ω₁·q + Γ_{x+1}) = hdNx q (Γ_{x+1})`** for `1 ≤ q < Γ_{x+1}`. -/
theorem hjG_glA {q : Ordinal.{0}} (h1 : 1 ≤ q) (hq : q < lgG x) : glA q (lgG x) x = hdNx q (lgG x) := by
  rw [hdNx_fixP (hjG_fix hx hx1 h1 hq)]
  exact hc_glA_fixG hx hx1 h1 (hq.trans (mg_lgG_lt_G1 hx hx1)) (hjG_fix hx hx1 h1 hq) hq (lgG_facts hx hx1).2.1
    (mg_lgG_lt_G1 hx hx1)

theorem hjG_lt1 {q : Ordinal.{0}} (h1 : 1 ≤ q) (hq : q < lgG x) : hdNx q (lgG x) < gq 1 x := by
  rw [← hjG_glA hx hx1 h1 hq]; exact hi_glA_lt1 hx hx1 (hq.trans (mg_lgG_lt_G1 hx hx1)) (mg_lgG_lt_G1 hx hx1)

end GBase

/-- **Lemma EXACT for `hdNx q(ρ) (Γ_{ρ+1})`** for a level `q` with Lemma EXACT. -/
theorem hjG_S_pi {σ ρ qρ qσ : Ordinal.{0}} (hB : Bases σ ρ) (hq : qρ ∈ TB ρ σ ∧ pi σ ρ qρ = qσ)
    (h1ρ : 1 ≤ qρ) (hqρ : qρ < lgG ρ) (h1σ : 1 ≤ qσ) (hqσ : qσ < lgG σ) :
    hdNx qρ (lgG ρ) ∈ TB ρ σ ∧ pi σ ρ (hdNx qρ (lgG ρ)) = hdNx qσ (lgG σ) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨g1, g2⟩ : lgG ρ ∈ TB ρ σ ∧ pi σ ρ (lgG ρ) = lgG σ := Go.goGl.ba_pi σ ρ hB
  have h := glA_pi hB hq.1 (hqρ.trans (lgG_facts hB.2.1 hρ1).2.2.1) g1 (lgG_facts hB.2.1 hρ1).2.2.1
  rw [hq.2, g2, hjG_glA hB.2.1 hρ1 h1ρ hqρ, hjG_glA hB.1 hσ1 h1σ hqσ] at h
  exact h

section GW

variable (Λ : HjLv)

theorem hjG_one {x : Ordinal.{0}} (hx : InE x) : (1 : Ordinal.{0}) ≤ Λ.l x + x :=
  (one_lt_omega0.trans (omega0_lt_inE hx)).le.trans le_add_self

theorem hjG_q {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : Λ.l x + x < lgG x := Λ.succ.l_lt x hx hx1

theorem hjG_q2 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : Λ.l x + x + x < lgG x :=
  (inE_indec (lgG_facts hx hx1).2.2.2.1).add_lt (hjG_q Λ hx hx1) (lgG_facts hx hx1).2.1

theorem hjG_FP : veblen (Λ.L + Om1) (gcG 0) = gcG 0 := gn_veb_fix (gcG_SC 0) Λ.succ.L_G

/-- **`G` AS A BASE OF LEVEL `L + Ω₁`** (gate `0`, reading `Γ_{x+1}`, outer low field `hdNx (ℓ(x)+x+x) (Γ_{x+1})`). -/
noncomputable def hjGW : HjWB Λ where
  F := gcG 0
  Fr := lgG
  γ := 0
  Zo := fun x => hdNx (Λ.l (max ω x) + max ω x + max ω x) (lgG x)
  γ_lt := gv_Om1_pos
  F_P := ⟨gcG 0, hjG_FP Λ⟩
  G_le := le_rfl
  S_lt1 := by
    have hG1 := gcG_SC 1
    have hE := Low.opow_eq_self_of_SC hG1
    have hfix : veblen (Λ.L + Om1) (gcG 1) = gcG 1 := gn_veb_fix hG1 (Λ.succ.L_lt 1)
    have h2 := (isNormal_veblen (Λ.L + Om1)).strictMono
      ((ev_isSuccLimit_of_inE hE).add_one_lt (gcG_lt zero_lt_one))
    rw [hdNx_fixP (hjG_FP Λ)]; rwa [hfix] at h2
  F_mem := fun S _ _ ha _ => gmS_G0_mem S ha
  S_mem := fun S a b ha _ => by
    rw [hdNx_fixP (hjG_FP Λ)]
    exact CSet.phi_mem (Λ.succ.L_mem S a b) (CSet.succ_mem (gmS_G0_mem S ha))
  F_code := fun _ _ _ _ _ _ _ => GxCl.atom (Set.mem_singleton _)
  F_cl := fun _ hZ _ _ _ _ _ => hZ.1
  S_cl := fun _ hZ _ _ => hZ.1
  Fr_gt := fun hx hx1 _ => hjG_q Λ hx hx1
  Fr_P := fun hx hx1 _ => ⟨lgG _, hjG_fix hx hx1 (hjG_one Λ hx) (hjG_q Λ hx hx1)⟩
  S_Zo := fun {x} hx hx1 _ => by
    show hdNx (Λ.l x + x) (lgG x) < hdNx (Λ.l (max ω x) + max ω x + max ω x) (lgG x)
    rw [max_eq_right (omega0_lt_inE hx).le, hdNx_fixP (hjG_fix hx hx1 (hjG_one Λ hx) (hjG_q Λ hx hx1)),
      hdNx_fixP (hjG_fix hx hx1 ((hjG_one Λ hx).trans le_self_add) (hjG_q2 Λ hx hx1))]
    exact hd_veb_left_lt ((lt_add_iff_pos_right _).2 hx.pos) _
  Zo_fix := fun x => hdNx_fix (((show (2 : Ordinal.{0}) < ω from by exact_mod_cast natCast_lt_omega0 2).trans_le
    (le_max_left ω x)).trans_le le_add_self) _
  Zo_G1 := fun x hx hx1 => by
    show hdNx (Λ.l (max ω x) + max ω x + max ω x) (lgG x) < gq 1 x
    rw [max_eq_right (omega0_lt_inE hx).le]
    exact hjG_lt1 hx hx1 ((hjG_one Λ hx).trans le_self_add) (hjG_q2 Λ hx hx1)
  Fr_pi := fun hB _ => Go.goGl.ba_pi _ _ hB
  S_pi := fun hB _ => hjG_S_pi hB (Λ.succ.l_pi _ _ hB) (hjG_one Λ hB.2.1) (hjG_q Λ hB.2.1 hB.2.2.2)
    (hjG_one Λ hB.1) (hjG_q Λ hB.1 (hB.2.2.1.trans hB.2.2.2))

theorem hjGW_γ : (hjGW Λ).γ = 0 := rfl

/-- **The union over `G` with a package at `Λ` starts the next package at `Λ.succ`.** -/
theorem hjGU_shape (St0 : HjVStTy Λ 0) (h0 : ∀ Q U h, HjVSpec Q U (St0 Q U h)) (S0 : HgVD)
    (hS0 : HjWShape (hjGW Λ) 0 S0) : HjWShape (hjGW Λ.succ) 0 (hjwU (hjGW Λ) St0 h0 S0 hS0) := by
  refine ⟨?_, fun x _ _ => ?_, fun x hx hx1 _ => ?_, fun x hx hx1 => ?_, fun _ σ _ _ hσ _ _ => hσ.pos⟩
  · show hdNx (Λ.L + Om1) (gcG 0) = veblen (Λ.succ.L + 0) (gcG 0 + 1)
    rw [add_zero, hdNx_fixP (hjG_FP Λ)]; rfl
  · show (0 : Ordinal.{0}) < x ↔ max 0 0 < x
    rw [max_self]
  · show hdNx (Λ.l x + x) (lgG x) = veblen (Λ.succ.l x + 0) (lgG x + 1)
    rw [add_zero, hdNx_fixP (hjG_fix hx hx1 (hjG_one Λ hx) (hjG_q Λ hx hx1))]; rfl
  · show hjwUZ (hjGW Λ) x = if max 0 0 < x then evZ (veblen (Λ.succ.l x + 0) (lgG x + 1))
      else (hjGW Λ.succ).hjwZo x
    unfold hjwUZ
    rw [max_self, if_pos (show (hjGW Λ).γ < x from hx.pos), if_pos hx.pos, add_zero]
    show evZ (hdNx (Λ.l x + x) (lgG x)) = evZ (veblen (Λ.l x + x) (lgG x + 1))
    rw [hdNx_fixP (hjG_fix hx hx1 (hjG_one Λ hx) (hjG_q Λ hx hx1))]

end GW

/-- **`Hg.hgU` is a start over `G` at the level `Ω₁ + 0`.** -/
theorem hgU_shapeJ : HjWShape (hjGW hjL1) 0 hgU := by
  refine ⟨by show veblen Om1 (gcG 0 + 1) = veblen (Om1 + 0) (gcG 0 + 1); rw [add_zero], fun x _ _ => ?_,
    fun x _ _ _ => ?_, fun x hx _ => ?_, fun _ σ _ _ hσ _ _ => hσ.pos⟩
  · show (0 : Ordinal.{0}) < x ↔ max 0 0 < x
    rw [max_self]
  · show veblen x (lgG x + 1) = veblen (x + 0) (lgG x + 1)
    rw [add_zero]
  · show evZ (hcBR x) = if max 0 0 < x then evZ (veblen (x + 0) (lgG x + 1)) else (hjGW hjL1).hjwZo x
    rw [max_self, if_pos hx.pos, add_zero]; rfl

/-- **The starts over `G` at the packages `hjPkI K n`** from a start `S0` at `K`, by one recursion on `n < ω`. -/
noncomputable def hjGCg (K : HjPk) (S0 : HgVD) (hS0 : HjWShape (hjGW K.Λ) 0 S0) :
    (n : ℕ) → {S : HgVD // HjWShape (hjGW (hjPkI K n).Λ) 0 S}
  | 0 => ⟨S0, hS0⟩
  | n + 1 => ⟨hjwU (hjGW (hjPkI K n).Λ) (hjPkI K n).St0 (hjPkI K n).h0 (hjGCg K S0 hS0 n).1 (hjGCg K S0 hS0 n).2,
      hjGU_shape (hjPkI K n).Λ (hjPkI K n).St0 (hjPkI K n).h0 (hjGCg K S0 hS0 n).1 (hjGCg K S0 hS0 n).2⟩

/-- **The starts over `G` at the packages `Hj.hjPkN n`.** -/
noncomputable def hjGC (n : ℕ) : {S : HgVD // HjWShape (hjGW (hjPkN n).Λ) 0 S} := hjGCg hjPk1 hgU hgU_shapeJ n

/-- **THE SYSTEM AT `φ(Ω₁·(n+2), G+1)`**: the union of all levels `Ω₁·(n+1) + κ` over `G`. -/
noncomputable def hjGU (n : ℕ) : HgVD := (hjGC (n + 1)).1

theorem hjGU_γ (n : ℕ) : (hjGU n).γ = 0 := rfl

theorem hjGU_B (n : ℕ) : (hjGU n).B = veblen (Om1 * ((n + 2 : ℕ) : Ordinal.{0})) (gcG 0 + 1) := by
  show hdNx ((hjPkN n).Λ.L + Om1) (gcG 0) = _
  rw [hdNx_fixP (hjG_FP _), hjPkN_L, Nat.cast_succ (n + 1), mul_add_one]

theorem hjGU_b (n : ℕ) (x : Ordinal.{0}) : (hjGU n).b x = hdNx ((hjPkN n).Λ.l x + x) (lgG x) := rfl

theorem hjGU_lt1 (n : ℕ) : (hjGU n).B < gcG 1 := (hjGU n).B_lt1

/-! ## The location -/

theorem hjGU_γK (S : InaccSeq.{0}) (n : ℕ) : (hjGU n).γ < Td.tdK S := hg_K_pos S

/-- **`φ(Ω₁·(n+2), G+1)` IS LOCATED** for every `n < ω`: `Λ⁺ = ι(Γ(φ(Ω₁·(n+2), G+1))·ω)`, `P(…) < L(0)`
(UNCONDITIONAL). -/
theorem hjGU_loc (S : InaccSeq.{0}) (n : ℕ) :
    ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG (hjGU n).B * ω) ∧
      upsilon (xtB1 X) = Pv S (gcG (hjGU n).B * ω) ∧ Pv S (gcG (hjGU n).B * ω) < Nc.ncL S 0 :=
  hgV_locD (hjGU n) S (hjGU_γK S n)

/-- **Theorem BLK^O below `P(Γ(φ(Ω₁·(n+2), G+1))·ω)`, with the exact reaches** (UNCONDITIONAL). -/
theorem hjGU_blk (S : InaccSeq.{0}) (n : ℕ) :
    let X := gsX (hjGU n).step.toRS _ (hjGU n).E_lt_B.le (hjGU n).B_lt_NB S (hgV_locD_g (hjGU n) S (hjGU_γK S n))
    (∀ c' d, c' < d → d < upsilon (xtB1 X) → (le2 c' d ↔ ∃ μ, ∃ j : ℕ, (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 X ∧
        c' = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧ d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 X →
      (∀ c' < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c' g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec X l)) ∧
    (∀ α < upsilon (xtB1 X), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  hgV_locD_blk (hjGU n) S (hjGU_γK S n)

/-- **`φ(Ω₁·ω, G+1)`.** -/
noncomputable def hjGE : Ordinal.{0} := veblen (Om1 * ω) (gcG 0 + 1)

theorem hjG_Ow_lt (α : Ordinal.{0}) : (Om1 : Ordinal.{0}) * ω < gcG α :=
  InE.mul_lt (Low.opow_eq_self_of_SC (gcG_SC α)) (hg_Om1_lt_G α) (omega0_lt_inE (Low.opow_eq_self_of_SC (gcG_SC α)))

theorem hjG_Ow_ne : (Om1 : Ordinal.{0}) * ω ≠ 0 := (mul_pos gv_Om1_pos omega0_pos).ne'

/-- **Every ordinal below `φ(Ω₁·ω, G+1)` lies below some `φ(Ω₁·(n+2), G+1)`.** -/
theorem hjGE_cofB {β : Ordinal.{0}} (hβ : β < hjGE) : ∃ n : ℕ, β < (hjGU n).B := by
  obtain ⟨b, hb, hβb⟩ := hgVeb_cof hjG_Ow_ne (gn_veb_fix (gcG_SC 0) (hjG_Ow_lt 0)) hβ
  have hdiv : b / Om1 < ω := (lt_mul_iff_div_lt gv_Om1_pos.ne').1 hb
  obtain ⟨n, hn⟩ := lt_omega0.1 hdiv
  have hbn : b < Om1 * ((n + 1 : ℕ) : Ordinal.{0}) := by
    have := lt_mul_div_add b gv_Om1_pos.ne'
    rw [hn] at this
    rwa [Nat.cast_succ, mul_add_one]
  refine ⟨n, hβb.trans_le ?_⟩
  show hcN b (gcG 0) ≤ hdNx ((hjPkN n).Λ.L + Om1) (gcG 0)
  rw [hjPkN_L]
  exact (hcN_mono hbn.le _).trans (hdN_lt_Nx ((add_lt_add_iff_left _).2 hg_one_lt_Om1)).le

theorem hjGE_lim : IsSuccLimit hjGE := ev_isSuccLimit_of_inE (gg_veblen_eps hjG_Ow_ne)

/-- **The located bounds `ι(Γ(φ(Ω₁·(n+2), G+1))·ω)` are cofinal below `ι(Γ(φ(Ω₁·ω, G+1)))`.** -/
theorem hjGE_cof (S : InaccSeq.{0}) {l : Ordinal.{0}} (hl : l < iota S (gcG hjGE)) :
    ∃ n : ℕ, l < iota S (gcG (hjGU n).B * ω) := by
  have hlim : IsSuccLimit (gcG hjGE) := ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC (gcG_SC _))
  rw [iota_limit hlim] at hl
  haveI : Nonempty (Iio (gcG hjGE)) := ⟨⟨0, hlim.bot_lt⟩⟩
  obtain ⟨e, he⟩ := (lt_ciSup_iff (iota_bdd _)).1 hl
  obtain ⟨β, hβ, heβ⟩ := gcG_lt_of_lt_limit hjGE_lim e.2
  obtain ⟨n, hβn⟩ := hjGE_cofB hβ
  refine ⟨n, he.trans_le (iota_mono _ _ ((heβ.trans (gcG_lt hβn)).trans_le ?_).le)⟩
  exact le_mul_of_one_le_right' one_lt_omega0.le

/-- **ENUM-REACH at every range restart below `ι(Γ(φ(Ω₁·ω, G+1)))`, fixed points included** (UNCONDITIONAL). -/
theorem hjGE_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG hjGE)) :
    CdUpper S l ∧ CdLower S l := by
  obtain ⟨n, h⟩ := hjGE_cof S hl
  exact hgV_locD_enum (hjGU n) S (hjGU_γK S n) hr h

/-- **CapV at every range restart below `ι(Γ(φ(Ω₁·ω, G+1)))`** (UNCONDITIONAL). -/
theorem hjGE_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG hjGE)) :
    CdCapV S l := by
  obtain ⟨n, h⟩ := hjGE_cof S hl
  exact hgV_locD_capV (hjGU n) S (hjGU_γK S n) hr h

/-- **THE ROAD**: UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ(φ(Ω₁·ω, G+1)))` (CapV also `υ_λ < L(ω)`), (CL), EQ,
TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem hjGE_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG hjGE) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG hjGE) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG hjGE) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  gv_road_of S _ (fun _ hr h => hjGE_enum S hr h) (fun _ hr h => hjGE_capV S hr h) hU hL hV hC hEQ hrest hB2

theorem hjGE_lt1 : hjGE < gcG 1 := by
  have hG1 := gcG_SC 1
  have hE := Low.opow_eq_self_of_SC hG1
  have hfix : veblen (Om1 * ω) (gcG 1) = gcG 1 := gn_veb_fix hG1 (hjG_Ow_lt 1)
  have h2 := (isNormal_veblen (Om1 * ω)).strictMono ((ev_isSuccLimit_of_inE hE).add_one_lt (gcG_lt zero_lt_one))
  unfold hjGE; rwa [hfix] at h2

/-- **`Γ(φ(Ω₁·ω, G+1)) < Ω₂`.** -/
theorem hjGE_lt_Om2 : gcG hjGE < Om (1 + 1) := by
  have hBE : InE Tf.tfBG := Low.opow_eq_self_of_SC Tf.tfBG_SC
  have hO : (Om1 : Ordinal.{0}) < Tf.tfBG := Tf.tfBG_gt
  have h1 : (1 : Ordinal.{0}) < Tf.tfBG := one_lt_omega0.trans (omega0_lt_inE hBE)
  have hG1 : gcG 1 < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) h1)
  have h2 : gcG hjGE < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) (hjGE_lt1.trans hG1))
  exact h2.trans Tf.tfBG_lt_Om2

/-- **`P(Γ(φ(Ω₁·ω, G+1))) < L(0)`.** -/
theorem hjGE_P (S : InaccSeq.{0}) : Pv S (gcG hjGE) < Nc.ncL S 0 := ga_Pv_lt_L0 S hjGE_lt_Om2.le

/-- **The order of the frontiers**: `φ(Ω₁+Ω₁, G+1) < φ(Ω₁·ω, G+1)`, `ι(Γ(φ(Ω₁+Ω₁, G+1))·ω) ≤ ι(Γ(φ(Ω₁·ω, G+1))) ≤
ι(Ω₂)` and `P(Γ(φ(Ω₁·ω, G+1))) ≤ P(Ω₂) < L(0)`. -/
theorem hjGE_fr_order (S : InaccSeq.{0}) :
    hjB < hjGE ∧ iota S (gcG hjB * ω) ≤ iota S (gcG hjGE) ∧ iota S (gcG hjGE) ≤ iota S (Om (1 + 1)) ∧
      Pv S (gcG hjGE) ≤ Pv S (Om (1 + 1)) ∧ Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have hlt : hjB < hjGE := by
    unfold hjB hjGE
    refine hd_veb_left_lt ?_ _
    rw [← Ordinal.mul_two]
    exact mul_lt_mul_of_pos_left (show (2 : Ordinal.{0}) < ω from by exact_mod_cast natCast_lt_omega0 2)
      gv_Om1_pos
  have hV : InE (gcG hjGE) := Low.opow_eq_self_of_SC (gcG_SC _)
  refine ⟨hlt, iota_mono _ _ (InE.mul_lt hV (gcG_lt hlt) (omega0_lt_inE hV)).le,
    iota_mono _ _ hjGE_lt_Om2.le, Nm.Pv_mono hjGE_lt_Om2.le, ga_Pv_lt_L0 S le_rfl⟩

end Googology.Trans.PoR.InaccPsi.R2.Hj

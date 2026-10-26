import Googology.Trans.PoR.InaccPsi.R2.HgQU

/-!
# HgQR: THE OFFSETS `φ(Ω₁, G+1+ν)` OF THE LEVEL `Ω₁` (READ AS `x`), `ν < ε₀`, BY ONE RECURSION ON THE OFFSET

The points `Q_ν = φ(Ω₁, G+1+ν)` (`hgFQ ν`, `ν < ε₀` a constant) are read as `P_ν(x) = φ(x, Γ_{x+1}+1+ν) =
ϑˣ(Ω₁·x + Γ_{x+1} + ν)` (`hgF_glA`), with Lemma EXACT (`hgFP_pi`: the level `x` and the base `Γ_{x+1}` move, `ν`
is a constant).  Each `Q_ν` is an abstract base of every countable level (`hgFB ν : Hg.HgQB`), and the union over
all levels over it (`Hg.hgQU`) has the bound `hdNx Ω₁ Q_ν = Q_{ν+1}` and the reading `P_{ν+1}(x)`: it starts the
stage at `Q_{ν+1}`.  The recursion `hgFV ν` (`hgFV 0 = Hg.hgU`, the system at `φ(Ω₁, G+1)`; `hgFV (ν+1)` the union
over all levels over `Q_ν`; `hgFV λ` the union of the `ω`-chain `hgFV (Gp.gpFs λ k)`, `Hg.HgCh`) keeps the
invariant (`hgF_inv`): base gate `0`, a start of the stage at `Q_ν`, and extension of every `hgFV μ`, `μ ≤ ν`.
So every `φ(Ω₁, G+1+ν)`, `ν < ε₀`, is located (`hgFV_loc`), and the frontier is `ι(Γ(φ(Ω₁, G+ε₀)))`
(`hgFE_enum`, `hgFE_capV`, `hgFE_road`, `hgFE_P`), unconditionally.

* `hgFQ`, `hgFP`, `hgF_nofix`, `hgF_glA`, `hgF_glA_lt`, `hgFP_lt`, `hgFP_pi`, `hgFB` (**`Q_ν` AS AN ABSTRACT BASE**),
  `hgU_startF`, `hgQU_ext` (**the union over the levels extends its start**), `hgQU_startF`;
* `HgFLimC`, `hgFLimCh`, `hgFLim_start`, `hgFSt`, `hgFExt`, `hgFLimD`, `hgFV` (**THE RECURSION ON THE OFFSET**),
  `hgF_inv` (**THE INVARIANT**), `hgFV_B`, `hgFV_γ`, `hgFV_loc`, `hgFE_cof`, `hgFE_enum`, `hgFE_capV`, `hgFE_road`,
  `hgFE_lt_Om2`, `hgFE_P`, `hgFE_fr_order`.

No new axiom.  New definitions: `hgFQ`, `hgFP`, `hgFB`, `HgFLimC`, `hgFLimCh`, `hgFSt`, `hgFExt`, `hgFLimD`, `hgFV`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hg

open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv Googology.Trans.PoR.InaccPsi.R2.Gp
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The points `Q_ν = φ(Ω₁, G+1+ν)` and their readings -/

/-- **`Q_ν = φ(Ω₁, G+1+ν)`.** -/
noncomputable def hgFQ (ν : Ordinal.{0}) : Ordinal.{0} := veblen Om1 (gcG 0 + 1 + ν)

/-- **`P_ν(x) = φ(x, Γ_{x+1}+1+ν)`.** -/
noncomputable def hgFP (ν x : Ordinal.{0}) : Ordinal.{0} := veblen x (lgG x + 1 + ν)

theorem hgFQ_zero : hgFQ 0 = hgB := by unfold hgFQ hgB; rw [add_zero]

theorem hgFP_zero (x : Ordinal.{0}) : hgFP 0 x = hcBR x := by unfold hgFP hcBR; rw [add_zero]

theorem hgFQ_mono {μ ν : Ordinal.{0}} (h : μ < ν) : hgFQ μ < hgFQ ν :=
  (isNormal_veblen Om1).strictMono ((add_lt_add_iff_left _).2 h)

theorem hgFQ_mono' {μ ν : Ordinal.{0}} (h : μ ≤ ν) : hgFQ μ ≤ hgFQ ν :=
  (isNormal_veblen Om1).monotone ((add_le_add_iff_left _).2 h)

theorem hgFP_mono {μ ν x : Ordinal.{0}} (h : μ < ν) : hgFP μ x < hgFP ν x :=
  (isNormal_veblen x).strictMono ((add_lt_add_iff_left _).2 h)

theorem hgFQ_succ (ν : Ordinal.{0}) : hdNx Om1 (hgFQ ν) = hgFQ (ν + 1) := by
  unfold hgFQ; rw [hdNx_veb, ← add_assoc]

theorem hgFP_succ (ν x : Ordinal.{0}) : hdNx x (hgFP ν x) = hgFP (ν + 1) x := by
  unfold hgFP; rw [hdNx_veb, ← add_assoc]

theorem hgF_eps0_lt_G1 : (ε₀ : Ordinal.{0}) < gcG 1 :=
  (gc_eps0_le_Om1.trans_lt (gcG_Om1_lt 1))

theorem hgFQ_lt1 {ν : Ordinal.{0}} (hν : ν < ε₀) : hgFQ ν < gcG 1 := by
  have hG1 := gcG_SC 1
  have hE := Low.opow_eq_self_of_SC hG1
  have hfix : veblen Om1 (gcG 1) = gcG 1 := gn_veb_fix hG1 (hg_Om1_lt_G 1)
  have h1 : gcG 0 + 1 + ν < gcG 1 :=
    (inE_indec hE).add_lt ((ev_isSuccLimit_of_inE hE).add_one_lt (gcG_lt zero_lt_one)) (hν.trans hgF_eps0_lt_G1)
  have h2 := (isNormal_veblen Om1).strictMono h1
  rwa [hfix] at h2

theorem hgFQ_mem {ν : Ordinal.{0}} (hν : ν < ε₀) (S : InaccSeq.{0}) {a b : Ordinal.{0}} (ha : 0 < a) :
    hgFQ ν ∈ S.CSet a b :=
  CSet.phi_mem (by rw [Br.Om1_eq]; exact CSet.Om_mem (CSet.one_mem _ _))
    (CSet.add_mem (CSet.succ_mem (gmS_G0_mem S ha)) (gr_cst_mem ha _ ν (hν.trans hc_eps0_lt_gam1)))

theorem hgFQ_code {ν Z : Ordinal.{0}} (hν : ν < ε₀) (hZ : SC Z) : GxCl Z {gcG 0} (hgFQ ν) := by
  have hZE : InE Z := Low.opow_eq_self_of_SC hZ
  unfold hgFQ; rw [Br.Om1_eq]
  exact GxCl.phi GxCl.om (GxCl.add (GxCl.add (GxCl.atom (Set.mem_singleton _))
    (GxCl.small (one_lt_omega0.trans (omega0_lt_inE hZE)))) (GxCl.small (hν.trans_le (gc_eps0_le hZE))))

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem hgF_one_le : (1 : Ordinal.{0}) ≤ x := one_lt_omega0.le.trans (omega0_lt_inE hx).le

/-- **`Γ_{x+1}+1+ν` is not a fixed point of `φ(x, ·)`** for `0 < ν < Γ_{x+1}`. -/
theorem hgF_nofix {ν : Ordinal.{0}} (hν0 : 0 < ν) (hνG : ν < lgG x) :
    lgG x + 1 + ν < veblen x (lgG x + 1 + ν) := by
  rcases (right_le_veblen x (lgG x + 1 + ν)).lt_or_eq with h | h
  · exact h
  · exfalso
    have hfix : veblen 0 (lgG x + 1 + ν) = lgG x + 1 + ν := hc_fix_down zero_le h.symm
    rw [veblen_zero_apply] at hfix
    have hE : InE (lgG x + 1 + ν) := hfix
    have h1 : lgG x + 1 < lgG x + 1 + ν := lt_add_of_pos_right _ hν0
    have h2 : ν < lgG x + 1 + ν := hνG.trans_le (le_self_add.trans le_self_add)
    exact absurd ((inE_indec hE).add_lt h1 h2) (lt_irrefl _)

/-- **`ϑˣ(Ω₁·x + Γ_{x+1} + μ) = φ(x, Γ_{x+1}+1+μ)`** for `μ < ε₀`. -/
theorem hgF_glA {μ : Ordinal.{0}} (hμ : μ < ε₀) : glA x (lgG x + μ) x = veblen x (lgG x + 1 + μ) := by
  have hq := (gm1_facts hx hx1).2.2.2
  have hxq : x < gq 1 x := (gm1_facts hx hx1).2.1
  have hGq := mg_lgG_lt_G1 hx hx1
  have hG0 := hc_glA_GG hx hx1 (hgF_one_le hx hx1) (lgG_facts hx hx1).2.1
  have hμG : μ < lgG x := hμ.trans_le ((gc_eps0_le hx).trans (lgG_facts hx hx1).2.1.le)
  exact hc_glAV hx hx1 (hgF_one_le hx hx1) hxq hGq hG0 μ ((inE_indec hq).add_lt hGq (hμ.trans_le (gc_eps0_le hq)))
    (fun ν' hν' hl => hgF_nofix hx hx1 hl.bot_lt ((hν'.trans_lt hμ).trans_le
      ((gc_eps0_le hx).trans (lgG_facts hx hx1).2.1.le)))

/-- **`ϑˣ(Ω₁·x + t) < Γ_{x+2}`** for `t < Γ_{x+2}` ([W07a] Lemma 3.30, `lgVt_lt_low`). -/
theorem hgF_glA_lt {t : Ordinal.{0}} (ht : t < gq 1 x) : glA x t x < gq 1 x :=
  lgVt_lt_low hx hx1 (mem_T_of_le hx hx1 le_rfl) hx1 (gm1_T hx hx1 ht).1 (gm1_T hx hx1 ht).2
    (gm1_one_T hx hx1).1 (gm1_one_T hx hx1).2 (gm1_facts hx hx1).2.1 ht

theorem hgF_add_lt {ν : Ordinal.{0}} (hν : ν < ε₀) : lgG x + ν < gq 1 x := by
  have hq := (gm1_facts hx hx1).2.2.2
  exact (inE_indec hq).add_lt (mg_lgG_lt_G1 hx hx1) (hν.trans_le (gc_eps0_le hq))

theorem hgFP_glA {ν : Ordinal.{0}} (hν : ν < ε₀) : hgFP ν x = glA x (lgG x + ν) x := (hgF_glA hx hx1 hν).symm

theorem hgFP_lt {ν : Ordinal.{0}} (hν : ν < ε₀) : hgFP ν x < gq 1 x := by
  rw [hgFP_glA hx hx1 hν]; exact hgF_glA_lt hx hx1 (hgF_add_lt hx hx1 hν)

theorem hgFP_gt (ν : Ordinal.{0}) : x < hgFP ν x :=
  (lgG_facts hx hx1).2.1.trans (((lt_add_one _).trans_le le_self_add).trans_le (right_le_veblen _ _))

end Base

/-- **Lemma EXACT for `P_ν(ρ) = ϑᵖ(Ω₁·ρ + Γ_{ρ+1} + ν)`**, `ν < ε₀` (the level `ρ` itself goes to `σ`). -/
theorem hgFP_pi {σ ρ ν : Ordinal.{0}} (hB : Bases σ ρ) (hν : ν < ε₀) :
    hgFP ν ρ ∈ TB ρ σ ∧ pi σ ρ (hgFP ν ρ) = hgFP ν σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hνσ : ν < σ := hν.trans_le (gc_eps0_le hB.1)
  obtain ⟨g1, g2⟩ : lgG ρ ∈ TB ρ σ ∧ pi σ ρ (lgG ρ) = lgG σ := Go.goGl.ba_pi σ ρ hB
  obtain ⟨s1, s2⟩ := pi_add hB g1 (mem_TB_of_lt hB hνσ)
  rw [pi_lt hB hνσ, g2] at s2
  obtain ⟨r1, r2⟩ := pi_base hB
  have h := glA_pi hB r1 hρ1 s1 (gm1_T hB.2.1 hρ1 (hgF_add_lt hB.2.1 hρ1 hν)).2
  rw [r2, s2, ← hgFP_glA hB.2.1 hρ1 hν, ← hgFP_glA hB.1 hσ1 hν] at h
  exact h

/-- **`Q_ν` AS AN ABSTRACT BASE OF EVERY COUNTABLE LEVEL** (`ν < ε₀`), reading `P_ν`. -/
noncomputable def hgFB (ν : Ordinal.{0}) (hν : ν < ε₀) : HgQB where
  Q := hgFQ ν
  P := hgFP ν
  Q_fix := fun _ h => veblen_veblen_of_lt h _
  G_lt := ((lt_add_one _).trans_le le_self_add).trans_le (right_le_veblen _ _)
  Q_lt1 := hgFQ_lt1 hν
  Q_mem := fun S _ _ ha => hgFQ_mem hν S ha
  Q_code := fun _ hZ _ => hgFQ_code hν hZ
  P_fix := fun _ _ _ h => veblen_veblen_of_lt h _
  P_gt := fun hx hx1 => hgFP_gt hx hx1 ν
  Pn_lt := fun hx hx1 => by rw [hgFP_succ]; exact hgFP_lt hx hx1 (hc_eps0_lim.add_one_lt hν)
  P_pi := fun hB => hgFP_pi hB hν
  Pn_pi := fun hB => by rw [hgFP_succ, hgFP_succ]; exact hgFP_pi hB (hc_eps0_lim.add_one_lt hν)
  Qn_mem := fun S _ _ ha => by rw [hgFQ_succ]; exact hgFQ_mem (hc_eps0_lim.add_one_lt hν) S ha

theorem hgFB_Q {ν : Ordinal.{0}} (hν : ν < ε₀) : (hgFB ν hν).Q = hgFQ ν := rfl

theorem hgFB_Zo {ν x : Ordinal.{0}} (hν : ν < ε₀) (hx : InE x) : (hgFB ν hν).Zo x = hgFP (ν + 1) x := by
  rw [HgQB.Zo_eq _ hx]; exact hgFP_succ ν x

/-- **`Hg.hgU` (the system at `φ(Ω₁, G+1)`) starts the stage at `Q_0`.** -/
theorem hgU_startF : HgQStart (hgFB 0 hc_eps0_lim.bot_lt) hgU where
  ix := by show hgB = hgFQ 0; rw [hgFQ_zero]
  γ := fun _ _ _ => Iff.rfl
  b := fun x _ _ _ => by show hcBR x = hgFP 0 x; rw [hgFP_zero]
  Z := fun x hx _ => by
    rw [HgPB.Zst_eq _ hx.pos]
    show evZ (hcBR x) = evZ (hgFP 0 x); rw [hgFP_zero]

/-- **The union over all levels over `Q` extends its start `U`.** -/
theorem hgQU_ext (B : HgQB) (U : HgVD) (hU : HgQStart B U) {c : Ordinal.{0}} (hc : c < U.B) :
    (∀ x, (hgQU B U hU).R c x = U.R c x) ∧ (hgQU B U hU).g c = U.g c := by
  have hUB : U.B = B.Q := hg_B_of_start hU
  have hQW : c < (hgQW B U hU).B := by
    rw [(hgQW_spec B U hU).B]; show c < hcS B.Q; rw [← hUB]; exact hc.trans (hcS_gt _)
  have hQL : c < (hgQL B U hU 0).B := by
    rw [hgQL_zero, hgQT_B]; exact hQW.trans_le (by rw [(hgQW_spec B U hU).B]; exact (hdS_lt_Nw (hcNw_gt _)).le)
  refine ⟨fun x => ?_, ?_⟩
  · rw [hgQU_R B U hU gv_Om1_pos hQL, hgQL_zero]
    show (hgdLvTU (hgQW_start B U hU)).R c x = U.R c x
    rw [hgdLvTU_R0 _ hQW x]; exact (hgQW_spec B U hU).extR c x hc
  · rw [hgQU_g B U hU gv_Om1_pos hQL, hgQL_zero]
    show (hgdLvTU (hgQW_start B U hU)).g c = U.g c
    rw [hgdLvTU_g0 _ hQW]; exact (hgQW_spec B U hU).extg c hc

/-- **The union over all levels over `Q_ν` starts the stage at `Q_{ν+1}`.** -/
theorem hgQU_startF {ν : Ordinal.{0}} (hν : ν < ε₀) (hν1 : ν + 1 < ε₀) (U : HgVD) (hU : HgQStart (hgFB ν hν) U) :
    HgQStart (hgFB (ν + 1) hν1) (hgQU (hgFB ν hν) U hU) where
  ix := by show hdNx Om1 (hgFQ ν) = hgFQ (ν + 1); exact hgFQ_succ ν
  γ := fun _ _ _ => Iff.rfl
  b := fun x hx _ _ => by rw [hgQU_b]; exact hgFB_Zo hν hx
  Z := fun x hx _ => by
    rw [HgPB.Zst_eq _ hx.pos, hgQU_Z]
    show evZ ((hgFB ν hν).Zo x) = evZ (hgFP (ν + 1) x); rw [hgFB_Zo hν hx]

end Googology.Trans.PoR.InaccPsi.R2.Hg

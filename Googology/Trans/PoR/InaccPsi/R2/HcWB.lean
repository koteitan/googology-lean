import Googology.Trans.PoR.InaccPsi.R2.HcRec
import Googology.Trans.PoR.InaccPsi.R2.HcCh
import Googology.Trans.PoR.InaccPsi.R2.GpFs

/-!
# HcWB: THE OFFSETS `φ(ω, G+1+ν)` OF LEVEL `ω`, `ν < ε₀`, BY ONE RECURSION ON THE OFFSET

The points `F_ν = φ(ω, G+1+ν)` (`hcWF ν`, `ν < ε₀` a constant, gate `0`) are read as
`F_ν(x) = φ(ω, Γ_{x+1}+1+ν) = ϑˣ(Ω₁·ω + Γ_{x+1} + ν)` (`hcWFr_glA`, the closed form `Hc.hc_glAV` at the level `ω`),
with Lemma EXACT (`hcWFr_pi`).  Each `F_ν` is a fixed point of every `φ(j+1, ·)`, so it is a pseudo-base of every
finite level (`hcWX ν j : Hc.HcX j`, outer low field `B_{ω^ω}(x) < B_x(x)`), and `(hcWX ν (j+1)).down = hcWX ν j`.

**The `ω`-step** (`hcWStep`): from a start `U` at `F_ν` (bound `F_ν`, base reading `F_ν(x)`, bound field
`evZ(F_ν(x))`), the steps of every finite level `Hc.hcRecS j (hcWX ν j) U` form an `ω`-chain (each is the union over
the offsets of the base `F_ν` of level `j+1` started at the previous one), whose union (`Hc.HcCh.U`) is a start at
`F_{ν+1} = hcS(F_ν) = φ(ω, G+2+ν)`.  At a limit `λ < ε₀` the union of the starts along the fundamental sequence
`Gp.gpFs λ` is a start at `F_λ`.  The recursion `hcWV ν` (start `Hc.hcWU` at `F_0 = φ(ω, G+1)`) keeps the invariant
(`hcW_inv`): `hcWV ν` has base gate `0`, starts the stage at `F_ν`, and extends every `hcWV μ`, `μ ≤ ν`.

So every `φ(ω, G+1+ν)`, `ν < ε₀`, is located (`hcWV_loc`), and the frontier is `ι(Γ(φ(ω, G+ε₀)))`
(`hcWE_enum`, `hcWE_capV`, `hcWE_road`, `hcWE_P`), unconditionally.

* `hcWF`, `hcWFr`, `hcWF_lt_N`, `hcWFr_glA`, `hcWFr_pi`, `hcWF_mem`, `hcWF_code`, `hcWX` (**`F_ν` AS A
  PSEUDO-BASE OF EVERY FINITE LEVEL**), `hcWX_down`, `hcWU_start`;
* `hcWCh` (**THE `ω`-CHAIN OVER `F_ν`**), `hcWStep`, `hcWStep_start`, `hcWStep_ext`; `hcWLimCh` (the union along
  `gpFs λ`), `hcWV` (**THE RECURSION ON THE OFFSET**), `hcW_inv` (**THE INVARIANT**), `hcWV_B`, `hcWV_loc`,
  `hcWE_cof`, `hcWE_enum`, `hcWE_capV`, `hcWE_road`, `hcWE_P`.

No new axiom.  New definitions: `hcWF`, `hcWFr`, `hcWX`, `hcWCh`, `hcWStep`, `hcWSt`, `hcWExt`, `HcWLimC`,
`hcWLimCh`, `hcWLimD`, `hcWV`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hc

open Googology.Trans.PoR.InaccPsi.R2.Hb Googology.Trans.PoR.InaccPsi.R2.Gp
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

/-! ## The points `F_ν = φ(ω, G+1+ν)` and their readings -/

/-- **`F_ν = φ(ω, G+1+ν)`.** -/
noncomputable def hcWF (ν : Ordinal.{0}) : Ordinal.{0} := veblen ω (gcG 0 + 1 + ν)

/-- **The reading `F_ν(x) = φ(ω, Γ_{x+1}+1+ν)`.** -/
noncomputable def hcWFr (ν x : Ordinal.{0}) : Ordinal.{0} := veblen ω (lgG x + 1 + ν)

theorem hcWF_zero : hcWF 0 = hbTw := by unfold hcWF; rw [add_zero, hbTw_eq]

theorem hcWF_succ (ν : Ordinal.{0}) : hcWF (ν + 1) = hcS (hcWF ν) := by
  unfold hcWF; rw [hcS_veb_eq, ← add_assoc]

theorem hcWFr_succ (ν x : Ordinal.{0}) : hcWFr (ν + 1) x = hcS (hcWFr ν x) := by
  unfold hcWFr; rw [hcS_veb_eq, ← add_assoc]

theorem hcWF_fix (k : ℕ) (ν : Ordinal.{0}) : veblen (k : Ordinal.{0}) (hcWF ν) = hcWF ν :=
  veblen_veblen_of_lt (natCast_lt_omega0 k) _

theorem hcWFr_fix (k : ℕ) (ν x : Ordinal.{0}) : veblen (k : Ordinal.{0}) (hcWFr ν x) = hcWFr ν x :=
  veblen_veblen_of_lt (natCast_lt_omega0 k) _

theorem hcWF_E (ν : Ordinal.{0}) : InE (hcWF ν) := hc_fix_E (hcWF_fix 0 ν)

theorem hcWFr_E (ν x : Ordinal.{0}) : InE (hcWFr ν x) := hc_fix_E (hcWFr_fix 0 ν x)

theorem hcWF_mono {μ ν : Ordinal.{0}} (h : μ < ν) : hcWF μ < hcWF ν :=
  (isNormal_veblen ω).strictMono ((add_lt_add_iff_left _).2 h)

theorem hcWF_mono' {μ ν : Ordinal.{0}} (h : μ ≤ ν) : hcWF μ ≤ hcWF ν :=
  (isNormal_veblen ω).monotone ((add_le_add_iff_left _).2 h)

theorem hcWFr_mono {μ ν x : Ordinal.{0}} (h : μ < ν) : hcWFr μ x < hcWFr ν x :=
  (isNormal_veblen ω).strictMono ((add_lt_add_iff_left _).2 h)

theorem hcWF_G_lt (ν : Ordinal.{0}) : gcG 0 < hcWF ν :=
  ((lt_add_one _).trans_le le_self_add).trans_le (right_le_veblen _ _)

theorem hc_eps0_E : InE (ε₀ : Ordinal.{0}) := omega0_opow_epsilon 0

theorem hc_eps0_lim : IsSuccLimit (ε₀ : Ordinal.{0}) := ev_isSuccLimit_of_inE hc_eps0_E

theorem hc_eps0_lt_gam1 : (ε₀ : Ordinal.{0}) < gamma 1 := gq_eps0_lt_gam.trans (gamma_lt_gamma.2 zero_lt_one)

/-- `φ(ω, P+1+ν) < N_ω(P)` for a fixed point `P` of `φ(ω, ·)` and `ν < ε₀`. -/
theorem hcW_lt_N {P ν : Ordinal.{0}} (hP : veblen ω P = P) (hν : ν < ε₀) : veblen ω (P + 1 + ν) < hcNw P := by
  have hNE := hcNw_E P
  have h1 : P + 1 + ν < hcNw P :=
    (inE_indec hNE).add_lt ((hcNw_lim P).add_one_lt (hcNw_gt P)) (hν.trans_le (gc_eps0_le hNE))
  have := (isNormal_veblen ω).strictMono h1
  rwa [hcNw_fix] at this

theorem hcW_G_fixW : veblen ω (gcG 0) = gcG 0 := hb_G_veb_w

/-- `F_ν < Γ_{Ω₁+2}`. -/
theorem hcWF_lt_G1 {ν : Ordinal.{0}} (hν : ν < ε₀) : hcWF ν < gcG 1 := by
  have hG1 := gcG_SC 1
  have hfix : veblen ω (gcG 1) = gcG 1 := gn_veb_fix hG1 (omega0_lt_inE (Low.opow_eq_self_of_SC hG1))
  exact (hcW_lt_N hcW_G_fixW hν).trans_le (hcNw_le hfix (gcG_lt zero_lt_one))

theorem hcWF_mem {ν : Ordinal.{0}} (hν : ν < ε₀) (S : InaccSeq.{0}) {a b : Ordinal.{0}} (ha : 0 < a) :
    hcWF ν ∈ S.CSet a b :=
  CSet.phi_mem (gr_cst_mem ha _ ω (omega0_lt_gamma 1))
    (CSet.add_mem (CSet.succ_mem (gmS_G0_mem S ha)) (gr_cst_mem ha _ ν (hν.trans hc_eps0_lt_gam1)))

/-- **`F_ν` is a code over every strongly critical `Z`.** -/
theorem hcWF_code {ν Z : Ordinal.{0}} (hν : ν < ε₀) (hZ : SC Z) : GxCl Z {gcG 0} (hcWF ν) := by
  have hZE : InE Z := Low.opow_eq_self_of_SC hZ
  exact GxCl.phi (GxCl.small (omega0_lt_inE hZE)) (GxCl.add (GxCl.add (GxCl.atom (Set.mem_singleton _))
    (GxCl.small (one_lt_omega0.trans (omega0_lt_inE hZE)))) (GxCl.small (hν.trans_le (gc_eps0_le hZE))))

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem hcWFr_lt_N {ν : Ordinal.{0}} (hν : ν < ε₀) : hcWFr ν x < hcB1 x := hcW_lt_N (hc_G_fixW hx hx1) hν

theorem hcWFr_lt_BW {ν : Ordinal.{0}} (hν : ν < ε₀) : hcWFr ν x < hcBW x :=
  (hcWFr_lt_N hx hx1 hν).trans (hc_B1_lt_BW hx hx1)

theorem hcWFr_lt_BR {ν : Ordinal.{0}} (hν : ν < ε₀) : hcWFr ν x < hcBR x :=
  (hcWFr_lt_BW hx hx1 hν).trans (hc_BW_lt_BR hx hx1)

theorem hcWFr_lt1 {ν : Ordinal.{0}} (hν : ν < ε₀) : hcWFr ν x < gq 1 x :=
  (hcWFr_lt_N hx hx1 hν).trans (hcB1_lt1 hx hx1)

theorem hcWFr_gt (ν : Ordinal.{0}) : x < hcWFr ν x :=
  (lgG_facts hx hx1).2.1.trans (((lt_add_one _).trans_le le_self_add).trans_le (right_le_veblen _ _))

/-- **`ϑˣ(Ω₁·ω + Γ_{x+1} + ν) = φ(ω, Γ_{x+1}+1+ν)`** for `ν < ε₀`. -/
theorem hcWFr_glA {ν : Ordinal.{0}} (hν : ν < ε₀) : glA ω (lgG x + ν) x = hcWFr ν x := by
  have hq := (gm1_facts hx hx1).2.2.2
  have hGq := mg_lgG_lt_G1 hx hx1
  have hG := hc_G_fixW hx hx1
  have hG0 : glA ω (lgG x) x = veblen ω (lgG x + 1) := (hc_glA_GW hx hx1).1.trans (hc_glA_GW hx hx1).2
  have hdq : lgG x + ν < gq 1 x := (inE_indec hq).add_lt hGq (hν.trans_le (gc_eps0_le hq))
  exact hc_glAV hx hx1 hc_one_le_om (hc_om_q hx hx1) hGq hG0 ν hdq (fun ν' h' _ =>
    hc_nofixW (hc_lt_next hG) le_self_add (hcW_lt_N hG (h'.trans_lt hν)))

end Base

/-- **Lemma EXACT for `F_ν(ρ)`**, `ν < ε₀`. -/
theorem hcWFr_pi {σ ρ ν : Ordinal.{0}} (hB : Bases σ ρ) (hν : ν < ε₀) :
    hcWFr ν ρ ∈ TB ρ σ ∧ pi σ ρ (hcWFr ν ρ) = hcWFr ν σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hωσ : ω < σ := omega0_lt_inE hB.1
  have hνσ : ν < σ := hν.trans_le (gc_eps0_le hB.1)
  obtain ⟨g1, g2⟩ : lgG ρ ∈ TB ρ σ ∧ pi σ ρ (lgG ρ) = lgG σ := Go.goGl.ba_pi σ ρ hB
  obtain ⟨s1, s2⟩ := pi_add hB g1 (mem_TB_of_lt hB hνσ)
  rw [pi_lt hB hνσ, g2] at s2
  have hq := (gm1_facts hB.2.1 hρ1).2.2.2
  have hs1 : lgG ρ + ν < Om1 :=
    ((inE_indec hq).add_lt (mg_lgG_lt_G1 hB.2.1 hρ1) (hν.trans_le (gc_eps0_le hq))).trans
      (gm1_facts hB.2.1 hρ1).2.2.1
  have h := glA_pi hB (mem_TB_of_lt hB hωσ) (hc_om_T hB.2.1 hρ1).2 s1 hs1
  rw [pi_lt hB hωσ, s2, hcWFr_glA hB.2.1 hρ1 hν, hcWFr_glA hB.1 hσ1 hν] at h
  exact h

/-- `N_{j+1}(F_ν(x)) < F_{ν+1}(x)`. -/
theorem hcW_N_lt_next (j : ℕ) (ν x : Ordinal.{0}) : hbN j (hcWFr ν x) < hcWFr (ν + 1) x := by
  rw [hcWFr_succ]; exact hbN_lt_S j _

theorem hcW_NF_lt_next (j : ℕ) (ν : Ordinal.{0}) : hbN j (hcWF ν) < hcWF (ν + 1) := by
  rw [hcWF_succ]; exact hbN_lt_S j _

/-! ## `F_ν` as a pseudo-base of every finite level -/

/-- **`F_ν` AS A PSEUDO-BASE OF LEVEL `j+1`**: reading `F_ν(x)`, gate `0`, outer low field `B_{ω^ω}(x) < B_x(x)`. -/
noncomputable def hcWX (ν : Ordinal.{0}) (hν : ν < ε₀) (j : ℕ) : HcX j where
  F := hcWF ν
  Fr := hcWFr ν
  γ := 0
  Zo := hcBW
  γ_lt := Ordinal.omega_pos 1
  F_fix := hcWF_fix (j + 1) ν
  G_le := (hcWF_G_lt ν).le
  N_lt1 := (hcW_NF_lt_next (j + 1) ν).trans (hcWF_lt_G1 (hc_eps0_lim.add_one_lt hν))
  F_mem := fun S _ _ ha _ => hcWF_mem hν S ha
  N_mem := fun S _ _ ha _ => by
    have e : hbN (j + 1) (hcWF ν) = veblen ((j + 1 + 1 : ℕ) : Ordinal.{0}) (hcWF ν + 1) := by
      have := hbN_veb (j + 1) (hcWF ν); rwa [hcWF_fix (j + 1 + 1)] at this
    rw [e]
    exact CSet.phi_mem (hcX_nat_mem S ha _ _) (CSet.succ_mem (hcWF_mem hν S ha))
  F_code := fun _ hZ _ _ _ _ _ => hcWF_code hν hZ
  F_cl := fun _ hZ _ _ _ _ _ => hZ.1
  N_cl := fun _ hZ _ _ => hZ.1
  Fr_gt := fun hx hx1 _ => hcWFr_gt hx hx1 ν
  Fr_glA := fun hx hx1 _ => hb_glA_fixP hx hx1 j (hcWFr_fix (j + 1) ν _) (hcWFr_gt hx hx1 ν) (hcWFr_lt1 hx hx1 hν)
  N_Zo := fun hx hx1 _ => (hcW_N_lt_next (j + 1) ν _).trans
    (hcWFr_lt_BW hx hx1 (hc_eps0_lim.add_one_lt hν))
  Zo_fix := fun _ => veblen_veblen_of_lt ((natCast_lt_omega0 2).trans hc_om_lt_ww) _
  Zo_BR := fun _ hx hx1 => (hc_BW_lt_BR hx hx1).le
  Fr_pi := fun hB _ => hcWFr_pi hB hν
  N_pi := fun {σ ρ} hB _ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hkσ : ((j + 1 + 1 : ℕ) : Ordinal.{0}) < σ := (natCast_lt_omega0 _).trans (omega0_lt_inE hB.1)
    obtain ⟨f1, f2⟩ := hcWFr_pi hB hν
    have h := glA_pi hB (mem_TB_of_lt hB hkσ) (hb_lev_T hB.2.1 hρ1 (j + 1 + 1)).2 f1
      (gm1_T hB.2.1 hρ1 (hcWFr_lt1 hB.2.1 hρ1 hν)).2
    rw [pi_lt hB hkσ, f2, hb_glA_fixP hB.2.1 hρ1 (j + 1) (hcWFr_fix _ ν _) (hcWFr_gt hB.2.1 hρ1 ν)
      (hcWFr_lt1 hB.2.1 hρ1 hν), hb_glA_fixP hB.1 hσ1 (j + 1) (hcWFr_fix _ ν _) (hcWFr_gt hB.1 hσ1 ν)
      (hcWFr_lt1 hB.1 hσ1 hν)] at h
    exact h
  G_lt := hcWF_G_lt ν
  Fr_fix := fun _ _ _ => hcWFr_fix (j + 1) ν _

theorem hcWX_down (ν : Ordinal.{0}) (hν : ν < ε₀) (j : ℕ) : (hcWX ν hν (j + 1)).down = hcWX ν hν j := rfl

theorem hcWX_PB (ν : Ordinal.{0}) (hν : ν < ε₀) (j : ℕ) : hcXPB (hcWX ν hν j) = hcXPB (hcWX ν hν 0) := rfl

/-- **The system `Hc.hcWU` at `φ(ω, G+1)` starts the stage at `F_0`.** -/
theorem hcWU_start : HcSStart (hcXPB (hcWX 0 hc_eps0_lim.bot_lt 0)) hcWU where
  ix := by show hbTw = hcWF 0; rw [hcWF_zero]
  γ := fun _ _ _ => Iff.rfl
  b := fun x hx hx1 _ => by
    show hbBw x = hcWFr 0 x
    unfold hcWFr; rw [add_zero]; exact (hc_glA_GW hx hx1).2
  Z := fun x hx hx1 => by
    rw [HcPB.Zst_eq _ hx.pos]
    show evZ (hbBw x) = evZ (hcWFr 0 x)
    unfold hcWFr; rw [add_zero, (hc_glA_GW hx hx1).2]

/-! ## The `ω`-step -/

section Step

variable (ν : Ordinal.{0}) (hν : ν < ε₀) (U : HcVD) (hU : HcSStart (hcXPB (hcWX ν hν 0)) U)

/-- The step of level `j+1` at `F_ν` started at `U`. -/
noncomputable def hcWT (j : ℕ) : HcVD := (hcRecS j (hcWX ν hν j) U hU).1

theorem hcWT_spec (j : ℕ) : HcSpec (hcWX ν hν j) U (hcWT ν hν U hU j) := (hcRecS j (hcWX ν hν j) U hU).2

theorem hcWT_succ (j : ℕ) :
    hcWT ν hν U hU (j + 1) = hcLvTU (St := fun X U h => (hcRecS j X U h).1) (fun X U h => (hcRecS j X U h).2)
      (hcLv_start_of_spec (hcWX ν hν (j + 1)) U (hcWT ν hν U hU j) (hcWT_spec ν hν U hU j)) := rfl

theorem hcWT_R_ext (j : ℕ) (c x : Ordinal.{0}) (hc : c < (hcWT ν hν U hU j).B) :
    (hcWT ν hν U hU (j + 1)).R c x = (hcWT ν hν U hU j).R c x := by
  rw [hcWT_succ]; exact hcLvTU_R0 _ _ hc x

theorem hcWT_g_ext (j : ℕ) (c : Ordinal.{0}) (hc : c < (hcWT ν hν U hU j).B) :
    (hcWT ν hν U hU (j + 1)).g c = (hcWT ν hν U hU j).g c := by
  rw [hcWT_succ]; exact hcLvTU_g0 _ _ hc

theorem hcWT_B (j : ℕ) : (hcWT ν hν U hU j).B = hbN (j + 1) (hcWF ν) := (hcWT_spec ν hν U hU j).B

/-- **THE `ω`-CHAIN OVER `F_ν`**: union bound `F_{ν+1}`, union base reading `F_{ν+1}(x)`. -/
noncomputable def hcWCh : HcCh where
  D := hcWT ν hν U hU
  B := hcWF (ν + 1)
  b := hcWFr (ν + 1)
  γ0 := fun j => (hcWT_spec ν hν U hU j).γ
  B_mono := fun j => by rw [hcWT_B, hcWT_B]; exact (hbN_lt_succ _ _).le
  B_lt := fun j => by rw [hcWT_B, hcWF_succ]; exact hbN_lt_S _ _
  B_cof := fun c hc => by
    rw [hcWF_succ] at hc
    obtain ⟨k, hk⟩ := hc_lt_S hc
    exact ⟨k, by rw [hcWT_B]; exact hk.trans_le (hbN_mono (Nat.le_succ k) _)⟩
  R_ext := hcWT_R_ext ν hν U hU
  g_ext := hcWT_g_ext ν hν U hU
  B_lt1 := hcWF_lt_G1 (hc_eps0_lim.add_one_lt hν)
  B_fix := by have := hcWF_fix 1 (ν + 1); rwa [Nat.cast_one] at this
  B_mem := fun S _ _ ha _ => hcWF_mem (hc_eps0_lim.add_one_lt hν) S ha
  b_ge := fun j x hx hx1 => by
    rw [(hcWT_spec ν hν U hU j).b x hx hx1 hx.pos, hcWFr_succ]; exact (hbN_lt_S _ _).le
  b_cof := fun x hx hx1 μ hμ => by
    rw [hcWFr_succ] at hμ
    obtain ⟨k, hk⟩ := hc_lt_S hμ
    exact ⟨k, by rw [(hcWT_spec ν hν U hU k).b x hx hx1 hx.pos]; exact hk.trans_le (hbN_mono (Nat.le_succ k) _)⟩
  b_fix := fun x _ _ => by have := hcWFr_fix 1 (ν + 1) x; rwa [Nat.cast_one] at this
  b_gt := fun x hx hx1 => hcWFr_gt hx hx1 _
  b_lt := fun x hx hx1 => hcWFr_lt_BR hx hx1 (hc_eps0_lim.add_one_lt hν)
  b_pi := fun _ _ hB => hcWFr_pi hB (hc_eps0_lim.add_one_lt hν)

/-- **THE `ω`-STEP**: the union of the `ω`-chain over `F_ν`. -/
noncomputable def hcWStep : HcVD := (hcWCh ν hν U hU).U

theorem hcWStep_γ : (hcWStep ν hν U hU).γ = 0 := rfl

theorem hcWStep_B : (hcWStep ν hν U hU).B = hcWF (ν + 1) := rfl

/-- **The `ω`-step starts the stage at `F_{ν+1}`.** -/
theorem hcWStep_start (hν1 : ν + 1 < ε₀) : HcSStart (hcXPB (hcWX (ν + 1) hν1 0)) (hcWStep ν hν U hU) where
  ix := rfl
  γ := fun _ _ _ => Iff.rfl
  b := fun _ _ _ _ => rfl
  Z := fun x hx _ => by rw [HcPB.Zst_eq _ hx.pos]; rfl

/-- **The `ω`-step extends its start.** -/
theorem hcWStep_ext {c : Ordinal.{0}} (hc : c < U.B) :
    (∀ x, (hcWStep ν hν U hU).R c x = U.R c x) ∧ (hcWStep ν hν U hU).g c = U.g c := by
  have hUB : U.B = hcWF ν := hc_B_of_start hU
  have hc0 : c < (hcWT ν hν U hU 0).B := by rw [hcWT_B, ← hUB]; exact hc.trans (hbN_gt _ _)
  refine ⟨fun x => ?_, ?_⟩
  · rw [hcWStep, (hcWCh ν hν U hU).U_R (k := 0) hc0]; exact (hcWT_spec ν hν U hU 0).extR c x hc
  · rw [hcWStep, (hcWCh ν hν U hU).U_g (k := 0) hc0]; exact (hcWT_spec ν hν U hU 0).extg c hc

end Step

/-! ## The limit step: the union along a fundamental sequence -/

/-- **The condition at a limit `λ < ε₀`**: every earlier value has base gate `0`, starts the stage at its offset,
and later values extend earlier ones. -/
def HcWLimC (l : Ordinal.{0}) (V : Ordinal.{0} → HcVD) : Prop :=
  l < ε₀ ∧ IsSuccLimit l ∧ (∀ μ, μ < l → (V μ).γ = 0 ∧ ∃ hμ : μ < ε₀, HcSStart (hcXPB (hcWX μ hμ 0)) (V μ)) ∧
    ∀ μ μ', μ ≤ μ' → μ' < l → ∀ c, c < (V μ).B → (∀ x, (V μ').R c x = (V μ).R c x) ∧ (V μ').g c = (V μ).g c

section Lim

variable {l : Ordinal.{0}} {V : Ordinal.{0} → HcVD} (H : HcWLimC l V)
include H

theorem hcWLim_B {μ : Ordinal.{0}} (hμ : μ < l) : (V μ).B = hcWF μ := by
  obtain ⟨-, hst⟩ := H.2.2.1 μ hμ
  exact hc_B_of_start hst.choose_spec

theorem hcWLim_b {μ x : Ordinal.{0}} (hμ : μ < l) (hx : InE x) (hx1 : x < Om1) : (V μ).b x = hcWFr μ x := by
  obtain ⟨-, hst⟩ := H.2.2.1 μ hμ
  exact hst.choose_spec.b x hx hx1 hx.pos

theorem hcWLim_fs (k : ℕ) : gpFs l k < l := gpFs_lt H.2.1 H.1 k

/-- `c < F_λ` lies below some `F_{λ_k}`. -/
theorem hcWLim_cofF {c : Ordinal.{0}} (hc : c < hcWF l) : ∃ k, c < hcWF (gpFs l k) := by
  obtain ⟨a, ha, hca⟩ := ((isNormal_veblen ω).lt_iff_exists_lt (isSuccLimit_add _ H.2.1)).1 hc
  obtain ⟨t, ht, hat⟩ := (lt_add_iff H.2.1.bot_lt.ne').1 ha
  obtain ⟨k, hk⟩ := gpFs_cof H.2.1 H.1 t ht
  exact ⟨k, hca.trans_le (((isNormal_veblen ω).monotone hat).trans
    ((isNormal_veblen ω).strictMono ((add_lt_add_iff_left _).2 hk)).le)⟩

theorem hcWLim_cofFr {μ x : Ordinal.{0}} (hμ : μ < hcWFr l x) : ∃ k, μ < hcWFr (gpFs l k) x := by
  obtain ⟨a, ha, hca⟩ := ((isNormal_veblen ω).lt_iff_exists_lt (isSuccLimit_add _ H.2.1)).1 hμ
  obtain ⟨t, ht, hat⟩ := (lt_add_iff H.2.1.bot_lt.ne').1 ha
  obtain ⟨k, hk⟩ := gpFs_cof H.2.1 H.1 t ht
  exact ⟨k, hca.trans_le (((isNormal_veblen ω).monotone hat).trans
    ((isNormal_veblen ω).strictMono ((add_lt_add_iff_left _).2 hk)).le)⟩

end Lim

end Googology.Trans.PoR.InaccPsi.R2.Hc

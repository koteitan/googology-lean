import Googology.Trans.PoR.InaccPsi.R2.GoStep

/-!
# THE FIRST DIGIT SYSTEM: the codes below `Γ_{Ω₁+1}` at the base `Γ_{Ω₁+1}`

The codes `c < Γ_{Ω₁+1}` of `R2.Gl` (reading `Gl.glR`, gate `Gl.glG`) with the base read `Γ_{x+1}` form a digit
system `goGl : GoD` at the base `G = Γ_{Ω₁+1}` (`B = φ(1, G)`, `ε_{Γ_{x+1}+1} = ϑˣ(Ω₁ + Γ_{x+1})`).  Its digit rule is
`R2.GnHX` `gn_Gr_pi` (through `Gl.gl_dig`), its last terms `Gl.gl_ld`, its cofinal codes `Gm.gmC`.

* `goGl` (**THE DIGIT SYSTEM BELOW `Γ_{Ω₁+1}`**), `goGl_B`, `goGl_R`, `goGl_g`, `goGl_b`.

No new axiom.  New definition: `goGl`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Go

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **THE DIGIT SYSTEM BELOW `Γ_{Ω₁+1}`** at the base `Γ_{Ω₁+1}` (read `Γ_{x+1}`). -/
noncomputable def goGl : GoD where
  B := gcG 0
  R := glR
  g := glG
  b := lgG
  ba := lgG
  ix := gcG 0
  B_E := gl_G0_E
  G_le := le_rfl
  B_lt1 := gcG_lt zero_lt_one
  B_ix := (gn_veb_fix (gcG_SC 0) gn_one_lt).symm
  ix_mem := fun S _ _ ha => gmS_G0_mem S ha
  g_lt := glG_lt_Om1
  g_zero := glG_zero
  g_nat := fun n => by rw [glG_nat]; exact natCast_lt_omega0 n
  g_E := glG_E
  g_lowE := fun _ hc => glG_low hc
  g_G0 := fun h => absurd h (lt_irrefl _)
  g_add := fun _ hZ hωZ => gl_add hZ hωZ
  g_opow := fun _ hZw hωZ => gl_opow_gate hZw hωZ
  code_gate := fun _ hZ1 hZ0 hZa hZp _ hAt _ hc hcB => by
    have hAtG : ∀ s ∈ _, gcG 0 ≤ s := fun s hs => by
      rcases hAt s hs with rfl | h
      · exact le_rfl
      · exact h
    exact gl_code_gate le_rfl hZ1 hZ0 hZa hZp (fun s hs => absurd hs (Set.notMem_empty s)) gfE_lt_G0.le
      (mg_noAt hAtG hc hcB) hcB
  g_succ := fun _ hZ c hc hg => glG_succ hZ c hc hg
  g_le_succ := glG_le_succ_all
  mem := fun _ _ _ _ c hc hg => gl_mem c hc hg
  R_zero := glR_zero
  R_nat := glR_nat
  R_E := glR_E
  R_succ := glR_succ_all
  R_pos := fun _ hx hx1 _ hc0 hc hg => glR_pos hx hx1 hc0 hc hg
  R_omega := fun _ hx hx1 _ ha haB hg => gl_omega_le hx hx1 ha haB hg
  R_lt_b := fun _ hx hx1 _ hc hg => glR_lt_G hx hx1 hc hg
  mono := fun _ hx hx1 _ hc _ hdc hgc hgd => glR_mono hx hx1 hc hdc hgc hgd
  cof := fun _ hx hx1 c hc hg ν hν => glR_cof hx hx1 c hc hg ν hν
  b_cof := fun _ hx hx1 _ hν => by
    obtain ⟨b, -, hbG, hgb, hb⟩ := mg_cof_G hx hx1 hν
    exact ⟨b, hbG, by rw [hgb]; exact hx.pos, hb⟩
  b_E := fun _ hx hx1 => (lgG_facts hx hx1).2.2.2.1
  x_lt_b := fun _ hx hx1 => (lgG_facts hx hx1).2.1
  b_eN := fun _ hx hx1 => gn_eNG hx hx1
  ba_lt := fun _ hx hx1 => mg_lgG_lt_G1 hx hx1
  b_Z := fun _ _ _ => go_eN_lt_evZ (lt_evZ _)
  b_pi := fun _ _ hB => mg_lgG_pi hB
  ba_pi := fun _ _ hB => mg_lgG_pi hB
  ex := fun _ _ hB c hc hg => gl_pi hB c hc hg
  dig := fun _ _ hB _ hd hg _ _ hat => gn_Gr_pi hB hat hd hg
  ld := fun c hl hc => gl_ld c hl hc
  cf := gmC
  cf_ge := fun k => (gmC_spec k).1
  cf_lt := gmC_lt_G0
  cf_g := fun k => by rw [(gmC_spec k).2.2]; exact epsilon_pos 0
  cf_mono := gmC_mono
  cf_cof := fun _ hc => gmC_cof hc

theorem goGl_B : goGl.B = gcG 0 := rfl

theorem goGl_R : goGl.R = glR := rfl

theorem goGl_g : goGl.g = glG := rfl

theorem goGl_b : goGl.b = lgG := rfl

end Googology.Trans.PoR.InaccPsi.R2.Go

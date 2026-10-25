import Googology.Trans.PoR.InaccPsi.R2.GvStep
import Googology.Trans.PoR.InaccPsi.R2.GvLow

/-!
# THE CODE-INDEXED UNION OVER `Ω₁`: the bound `ε_{i₀+Ω₁}` read with `Ω₁ ↦ x`

A family `F ν` (`ν < Ω₁`) of gated digit systems with bounds `φ(1, i₀ + ν)`, base readings `φ(1, i(x) + ν)` at the
bases `x > ν`, base gates `≤ ν` and coherent readings and gates (`GvFam`) has a union over all `ν < Ω₁`: a gated
digit system WITHOUT a cofinal sequence (`GvD`; the bound `φ(1, i₀ + Ω₁)` has cofinality `Ω₁`) with base gate `0`
and base reading `φ(1, i(x) + x)`: the index `Ω₁` is read as the base `x` itself.  Lemma EXACT for this reading needs
`π(ρ) = σ` (`b_pi`, a field; for `i₀ = G` it is `Gp.gp_b_pi_x`).  A code `c` of the union with gate below an
`ε`-number `σ` lies in some `F μ` with `μ < σ` (`small`, a field), so the digit rule and `R < b` of the members apply
at the bases above the gate.

* `GvFam`, `GvFam.N`, `GvFam.R`, `GvFam.g`, `GvFam.U` (**THE UNION OVER `Ω₁`**, base gate `0`), `U_R`, `U_g`, `U_B`;
* `gv_small` (**`small` for the recursion `Gs.gsD`**: the least `ν` with `c < (gsD ν).B` is `γ_μ + n + 1` with the
  gate of `c` at least `γ_μ`), `gvGs : GvFam` (`i₀ = G`, `i = gpI`), `gvU = gvGs.U` (**the bound `ε_{G+Ω₁}`, read
  `φ(1, Γ_{x+1} + x)`**), `gvU_B`, `gvU_γ`, `gvU_R`, `gvU_g`.

No new axiom.  New definitions: `GvFam`, `GvFam.N`, `GvFam.R`, `GvFam.g`, `GvFam.U`, `gvGs`, `gvU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gv

open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Go
  Googology.Trans.PoR.InaccPsi.R2.Gp
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

theorem gv_Om1_lim : IsSuccLimit (Om1 : Ordinal.{0}) := by rw [Br.Om1_eq]; exact Fx.fx_Om1_lim

theorem gv_Om1_pos : (0 : Ordinal.{0}) < Om1 := gv_Om1_lim.bot_lt

/-- **A family of gated digit systems over all `ν < Ω₁`** with the base data of its union. -/
structure GvFam where
  F : Ordinal.{0} → GsD
  i0 : Ordinal.{0}
  i : Ordinal.{0} → Ordinal.{0}
  baΩ : Ordinal.{0} → Ordinal.{0}
  ix : ∀ ν, ν < Om1 → (F ν).ix = i0 + ν
  hb : ∀ ν, ν < Om1 → ∀ x, InE x → x < Om1 → ν < x → (F ν).b x = veblen 1 (i x + ν)
  γ_le : ∀ ν, ν < Om1 → (F ν).γ ≤ ν
  cohR : ∀ β γ, β ≤ γ → γ < Om1 → ∀ c x, c < (F β).B → (F γ).R c x = (F β).R c x
  cohg : ∀ β γ, β ≤ γ → γ < Om1 → ∀ c, c < (F β).B → (F γ).g c = (F β).g c
  small : ∀ ν, ν < Om1 → ∀ c, c < (F ν).B → ∀ σ, InE σ → (F ν).g c < σ →
    ∃ μ, μ < σ ∧ μ < Om1 ∧ c < (F μ).B
  i0_mem : ∀ (S : InaccSeq.{0}) (a b : Ordinal.{0}), 0 < a → 0 < b → i0 ∈ S.CSet a b
  ix_lt : i0 + Om1 < gcG 1
  b_eN : ∀ x, InE x → x < Om1 → eN (veblen 1 (i x + x)) = glA 1 (baΩ x) x
  ba_lt : ∀ x, InE x → x < Om1 → baΩ x < gq 1 x
  b_Z : ∀ x, InE x → x < Om1 → eN (veblen 1 (i x + x)) < evZ (lgG x)
  b_pi : ∀ σ ρ, Bases σ ρ → veblen 1 (i ρ + ρ) ∈ TB ρ σ ∧ pi σ ρ (veblen 1 (i ρ + ρ)) = veblen 1 (i σ + σ)
  ba_pi : ∀ σ ρ, Bases σ ρ → baΩ ρ ∈ TB ρ σ ∧ pi σ ρ (baΩ ρ) = baΩ σ

namespace GvFam

variable (Q : GvFam)

theorem B_eq {ν : Ordinal.{0}} (h : ν < Om1) : (Q.F ν).B = veblen 1 (Q.i0 + ν) := by
  rw [(Q.F ν).B_ix, Q.ix ν h]

theorem B_lt {β γ : Ordinal.{0}} (hβγ : β < γ) (h : γ ≤ Om1) : (Q.F β).B < veblen 1 (Q.i0 + γ) := by
  rw [Q.B_eq (hβγ.trans_le h)]
  exact (isNormal_veblen 1).strictMono ((add_lt_add_iff_left _).2 hβγ)

theorem B_ltΩ {β : Ordinal.{0}} (h : β < Om1) : (Q.F β).B < veblen 1 (Q.i0 + Om1) := Q.B_lt h le_rfl

theorem B_cof {c : Ordinal.{0}} (hc : c < veblen 1 (Q.i0 + Om1)) : ∃ ν, ν < Om1 ∧ c < (Q.F ν).B := by
  obtain ⟨t, ht, hct⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ gv_Om1_lim)).1 hc
  obtain ⟨d, hd, htd⟩ := (lt_add_iff gv_Om1_pos.ne').1 ht
  exact ⟨d, hd, by rw [Q.B_eq hd]; exact hct.trans_le ((isNormal_veblen 1).monotone htd)⟩

/-- The first member containing `c`. -/
noncomputable def N (c : Ordinal.{0}) : Ordinal.{0} := sInf {ν | ν < Om1 ∧ c < (Q.F ν).B}

theorem N_spec {c ν : Ordinal.{0}} (hν : ν < Om1) (hc : c < (Q.F ν).B) :
    Q.N c ≤ ν ∧ Q.N c < Om1 ∧ c < (Q.F (Q.N c)).B := by
  have hne : ({ν | ν < Om1 ∧ c < (Q.F ν).B} : Set Ordinal.{0}).Nonempty := ⟨ν, hν, hc⟩
  have hm := csInf_mem hne
  exact ⟨csInf_le' ⟨hν, hc⟩, hm.1, hm.2⟩

theorem N_high {c : Ordinal.{0}} (hc : veblen 1 (Q.i0 + Om1) ≤ c) : Q.N c = 0 := by
  unfold GvFam.N
  have he : ({ν | ν < Om1 ∧ c < (Q.F ν).B} : Set Ordinal.{0}) = ∅ := by
    ext ν
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hν hcν
    exact absurd ((hcν.trans (Q.B_ltΩ hν))) (not_lt.2 hc)
  rw [he]; exact Ordinal.sInf_empty

/-- The reading of the union. -/
noncomputable def R (c x : Ordinal.{0}) : Ordinal.{0} := (Q.F (Q.N c)).R c x

/-- The gate of the union. -/
noncomputable def g (c : Ordinal.{0}) : Ordinal.{0} := (Q.F (Q.N c)).g c

theorem R_eq {c ν : Ordinal.{0}} (hν : ν < Om1) (hc : c < (Q.F ν).B) (x : Ordinal.{0}) :
    Q.R c x = (Q.F ν).R c x := by
  obtain ⟨h1, -, h3⟩ := Q.N_spec hν hc
  exact (Q.cohR _ _ h1 hν c x h3).symm

theorem g_eq {c ν : Ordinal.{0}} (hν : ν < Om1) (hc : c < (Q.F ν).B) : Q.g c = (Q.F ν).g c := by
  obtain ⟨h1, -, h3⟩ := Q.N_spec hν hc
  exact (Q.cohg _ _ h1 hν c h3).symm

theorem lim' : IsSuccLimit (veblen 1 (Q.i0 + Om1)) := ev_isSuccLimit_of_inE (omega0_opow_epsilon _)

theorem R_succ' (c x : Ordinal.{0}) : Q.R (c + 1) x = Q.R c x + 1 := by
  rcases lt_or_ge c (veblen 1 (Q.i0 + Om1)) with h | h
  · obtain ⟨n, hn1, hn⟩ := Q.B_cof (Q.lim'.add_one_lt h)
    rw [Q.R_eq hn1 hn, Q.R_eq hn1 ((lt_add_one c).trans hn), (Q.F n).R_succ]
  · unfold GvFam.R
    rw [Q.N_high h, Q.N_high (h.trans (le_self_add (a := c) (b := 1))), (Q.F 0).R_succ]

theorem g_le_succ' (c : Ordinal.{0}) : Q.g c ≤ Q.g (c + 1) := by
  rcases lt_or_ge c (veblen 1 (Q.i0 + Om1)) with h | h
  · obtain ⟨n, hn1, hn⟩ := Q.B_cof (Q.lim'.add_one_lt h)
    rw [Q.g_eq hn1 hn, Q.g_eq hn1 ((lt_add_one c).trans hn)]; exact (Q.F n).g_le_succ c
  · unfold GvFam.g
    rw [Q.N_high h, Q.N_high (h.trans (le_self_add (a := c) (b := 1)))]; exact (Q.F 0).g_le_succ c

/-- A code of the union with gate below an `ε`-number `σ` lies in a member `F μ`, `μ < σ`. -/
theorem small' {c σ : Ordinal.{0}} (hc : c < veblen 1 (Q.i0 + Om1)) (hσ : InE σ) (hg : Q.g c < σ) :
    ∃ μ, μ < σ ∧ μ < Om1 ∧ c < (Q.F μ).B := by
  obtain ⟨n, hn1, hn⟩ := Q.B_cof hc
  rw [Q.g_eq hn1 hn] at hg
  exact Q.small n hn1 c hn σ hσ hg

theorem b_le {ν x : Ordinal.{0}} (hν : ν < Om1) (hx : InE x) (hx1 : x < Om1) (hνx : ν < x) :
    (Q.F ν).b x ≤ veblen 1 (Q.i x + x) := by
  rw [Q.hb ν hν x hx hx1 hνx]
  exact (isNormal_veblen 1).monotone ((add_le_add_iff_left _).2 hνx.le)

theorem F0_γ : (Q.F 0).γ = 0 := nonpos_iff_eq_zero.1 (Q.γ_le 0 gv_Om1_pos)

/-- **THE UNION OVER `Ω₁`**: a gated digit system without a cofinal sequence, bound `φ(1, i₀ + Ω₁)`, base gate `0`,
base reading `φ(1, i(x) + x)`. -/
noncomputable def U : GvD where
  B := veblen 1 (Q.i0 + Om1)
  γ := 0
  γ_lt := gv_Om1_pos
  γ_cl := fun _ hZ _ _ => hZ.1
  γ_G := fun _ => rfl
  R := Q.R
  g := Q.g
  b := fun x => veblen 1 (Q.i x + x)
  ba := Q.baΩ
  ix := Q.i0 + Om1
  B_E := omega0_opow_epsilon _
  G_le := (Q.F 0).G_le.trans (Q.B_ltΩ gv_Om1_pos).le
  B_lt1 := (gcG_SC 1).2 1 (one_lt_omega0.trans (omega0_lt_inE (Low.opow_eq_self_of_SC (gcG_SC 1)))) _ Q.ix_lt
  B_ix := rfl
  ix_mem := fun S a b ha hb => CSet.add_mem (Q.i0_mem S a b ha hb)
    (by rw [Br.Om1_eq]; exact CSet.Om_mem (CSet.one_mem _ _))
  g_lt := fun c hc => by
    obtain ⟨n, hn1, hn⟩ := Q.B_cof hc
    rw [Q.g_eq hn1 hn]; exact (Q.F n).g_lt c hn
  g_zero := by rw [Q.g_eq gv_Om1_pos (Q.F 0).B_pos]; exact (Q.F 0).g_zero
  g_nat := fun k => by rw [Q.g_eq gv_Om1_pos ((Q.F 0).nat_lt_B k)]; exact (Q.F 0).g_nat k
  g_E := by rw [Q.g_eq gv_Om1_pos (Q.F 0).E_lt_B]; exact (Q.F 0).g_E
  g_lowE := fun c hc => by rw [Q.g_eq gv_Om1_pos (hc.trans (Q.F 0).E_lt_B)]; exact (Q.F 0).g_lowE c hc
  g_G0 := fun h => by
    obtain ⟨n, hn1, hn⟩ := Q.B_cof h
    rw [Q.g_eq hn1 hn]; exact (Q.F n).g_G0 hn
  g_add := fun Z hZ hωZ x y hxy hgx hgy => by
    obtain ⟨n, hn1, hn⟩ := Q.B_cof hxy
    have hx : x < (Q.F n).B := lt_of_le_of_lt le_self_add hn
    have hy : y < (Q.F n).B := lt_of_le_of_lt le_add_self hn
    rw [Q.g_eq hn1 hn]; rw [Q.g_eq hn1 hx] at hgx; rw [Q.g_eq hn1 hy] at hgy
    exact (Q.F n).g_add Z hZ hωZ x y hn hgx hgy
  g_opow := fun Z hZw hωZ y hy hg => by
    obtain ⟨n, hn1, hn⟩ := Q.B_cof hy
    have hy' : y < (Q.F n).B := lt_of_le_of_lt (right_le_opow y one_lt_omega0) hn
    rw [Q.g_eq hn1 hn]; rw [Q.g_eq hn1 hy'] at hg
    exact (Q.F n).g_opow Z hZw hωZ y hn hg
  code_gate := fun Z hZ1 hZ0 hZa hZp At hAt c hc hcB => by
    obtain ⟨n, hn1, hn⟩ := Q.B_cof hcB
    rw [Q.g_eq hn1 hn]
    exact (Q.F n).code_gate Z hZ1 hZ0 hZa hZp At (fun s hs => (hAt s hs).imp_right
      (fun h => (Q.B_ltΩ hn1).le.trans h)) c hc hn
  g_succ := fun Z hZ c hc hg => by
    obtain ⟨n, hn1, hn⟩ := Q.B_cof hc
    have hc' : c < (Q.F n).B := (lt_add_one c).trans hn
    rw [Q.g_eq hn1 hn]; rw [Q.g_eq hn1 hc'] at hg
    exact (Q.F n).g_succ Z hZ c hn hg
  g_le_succ := Q.g_le_succ'
  mem := fun S a b ha c hc hg => by
    obtain ⟨n, hn1, hn⟩ := Q.B_cof hc
    rw [Q.g_eq hn1 hn] at hg
    exact (Q.F n).mem S a b ha c hn hg
  R_zero := fun x => by rw [Q.R_eq gv_Om1_pos (Q.F 0).B_pos]; exact (Q.F 0).R_zero x
  R_nat := fun k x => by rw [Q.R_eq gv_Om1_pos ((Q.F 0).nat_lt_B k)]; exact (Q.F 0).R_nat k x
  R_E := fun x => by rw [Q.R_eq gv_Om1_pos (Q.F 0).E_lt_B]; exact (Q.F 0).R_E x
  R_succ := Q.R_succ'
  R_pos := fun x hx hx1 c hc0 hc hg => by
    obtain ⟨n, hn1, hn⟩ := Q.B_cof hc
    rw [Q.R_eq hn1 hn]; rw [Q.g_eq hn1 hn] at hg
    exact (Q.F n).R_pos x hx hx1 c hc0 hn hg
  R_omega := fun x hx hx1 c hω hc hg => by
    obtain ⟨n, hn1, hn⟩ := Q.B_cof hc
    rw [Q.R_eq hn1 hn]; rw [Q.g_eq hn1 hn] at hg
    exact (Q.F n).R_omega x hx hx1 c hω hn hg
  R_lt_b := fun x hx hx1 _ c hc hg => by
    obtain ⟨μ, hμx, hμ1, hcμ⟩ := Q.small' hc hx hg
    rw [Q.R_eq hμ1 hcμ]; rw [Q.g_eq hμ1 hcμ] at hg
    exact ((Q.F μ).R_lt_b x hx hx1 ((Q.γ_le μ hμ1).trans_lt hμx) c hcμ hg).trans_le
      (Q.b_le hμ1 hx hx1 hμx)
  R_lt_Z := fun x hx hx1 c hc hg => by
    obtain ⟨n, hn1, hn⟩ := Q.B_cof hc
    rw [Q.R_eq hn1 hn]; rw [Q.g_eq hn1 hn] at hg
    exact (Q.F n).R_lt_Z x hx hx1 c hn hg
  mono := fun x hx hx1 c hc d hdc hgc hgd => by
    obtain ⟨n, hn1, hn⟩ := Q.B_cof hc
    have hd : d < (Q.F n).B := hdc.trans hn
    rw [Q.R_eq hn1 hn, Q.R_eq hn1 hd]; rw [Q.g_eq hn1 hn] at hgc; rw [Q.g_eq hn1 hd] at hgd
    exact (Q.F n).mono x hx hx1 c hn d hdc hgc hgd
  cof := fun x hx hx1 c hc hg ν hν => by
    obtain ⟨n, hn1, hn⟩ := Q.B_cof hc
    rw [Q.R_eq hn1 hn] at hν; rw [Q.g_eq hn1 hn] at hg
    obtain ⟨d, hdc, hgd, hνd⟩ := (Q.F n).cof x hx hx1 c hn hg ν hν
    have hd : d < (Q.F n).B := hdc.trans hn
    exact ⟨d, hdc, by rw [Q.g_eq hn1 hd]; exact hgd, by rw [Q.R_eq hn1 hd]; exact hνd⟩
  b_cof := fun x hx hx1 _ ν hν => by
    have hx0 : x ≠ 0 := hx.pos.ne'
    obtain ⟨t, ht, hνt⟩ := ((isNormal_veblen 1).lt_iff_exists_lt
      (isSuccLimit_add _ (ev_isSuccLimit_of_inE hx))).1 hν
    obtain ⟨d0, hd0, htd⟩ := (lt_add_iff hx0).1 ht
    have hd01 : d0 < Om1 := hd0.trans hx1
    have hνb : ν < (Q.F d0).b x := by
      rw [Q.hb d0 hd01 x hx hx1 hd0]; exact hνt.trans_le ((isNormal_veblen 1).monotone htd)
    obtain ⟨d, hd, hgd, hνd⟩ := (Q.F d0).b_cof x hx hx1 ((Q.γ_le d0 hd01).trans_lt hd0) ν hνb
    exact ⟨d, hd.trans (Q.B_ltΩ hd01), by rw [Q.g_eq hd01 hd]; exact hgd, by rw [Q.R_eq hd01 hd]; exact hνd⟩
  b_E := fun _ _ _ _ => omega0_opow_epsilon _
  x_lt_b := fun x hx hx1 _ => by
    have h := (Q.F 0).x_lt_b x hx hx1 (by rw [Q.F0_γ]; exact hx.pos)
    rw [Q.hb 0 gv_Om1_pos x hx hx1 hx.pos] at h
    exact h.trans_le ((isNormal_veblen 1).monotone ((add_le_add_iff_left _).2 zero_le))
  b_eN := fun x hx hx1 _ => Q.b_eN x hx hx1
  ba_lt := fun x hx hx1 _ => Q.ba_lt x hx hx1
  b_Z := fun x hx hx1 _ => Q.b_Z x hx hx1
  b_pi := fun σ ρ hB _ => Q.b_pi σ ρ hB
  ba_pi := fun σ ρ hB _ => Q.ba_pi σ ρ hB
  ex := fun σ ρ hB c hc hg => by
    obtain ⟨n, hn1, hn⟩ := Q.B_cof hc
    rw [Q.R_eq hn1 hn, Q.R_eq hn1 hn]; rw [Q.g_eq hn1 hn] at hg
    exact (Q.F n).ex σ ρ hB c hn hg
  dig := fun σ ρ hB _ d hd hg P P' hat => by
    obtain ⟨μ, hμσ, hμ1, hdμ⟩ := Q.small' hd hB.1 hg
    rw [Q.R_eq hμ1 hdμ, Q.R_eq hμ1 hdμ]; rw [Q.g_eq hμ1 hdμ] at hg
    exact (Q.F μ).dig σ ρ hB ((Q.γ_le μ hμ1).trans_lt hμσ) d hdμ hg P P' (fun β hβ hβe =>
      hat β hβ (hβe.trans_le (Q.b_le hμ1 hB.2.1 hB.2.2.2 (hμσ.trans hB.2.2.1))))
  ld := fun c hl hc => by
    obtain ⟨n, hn1, hn⟩ := Q.B_cof hc
    obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := (Q.F n).ld c hl hn
    have hcpn : cp < (Q.F n).B := hcp.trans hn
    refine ⟨cp, lp, T, hcp, by rw [Q.g_eq hn1 hn, Q.g_eq hn1 hcpn]; exact hgcp, fun x hx hx1 hg => ?_,
      fun σ ρ hB hg => hex σ ρ hB (by rw [← Q.g_eq hn1 hn]; exact hg)⟩
    rw [Q.g_eq hn1 hn] at hg
    rw [Q.R_eq hn1 hn, Q.R_eq hn1 hcpn]
    exact hdec x hx hx1 hg

theorem U_B : Q.U.B = veblen 1 (Q.i0 + Om1) := rfl

theorem U_γ : Q.U.γ = 0 := rfl

theorem U_b (x : Ordinal.{0}) : Q.U.b x = veblen 1 (Q.i x + x) := rfl

/-- **The union extends every member** (readings). -/
theorem U_R {ν c : Ordinal.{0}} (hν : ν < Om1) (hc : c < (Q.F ν).B) (x : Ordinal.{0}) : Q.U.R c x = (Q.F ν).R c x :=
  Q.R_eq hν hc x

/-- **The union extends every member** (gates). -/
theorem U_g {ν c : Ordinal.{0}} (hν : ν < Om1) (hc : c < (Q.F ν).B) : Q.U.g c = (Q.F ν).g c := Q.g_eq hν hc

end GvFam

/-! ## The recursion `Gs.gsD` as a family -/

/-- **`small` for `Gs.gsD`**: a code `c < (gsD ν).B` with gate below an `ε`-number `σ` lies in `gsD μ` for some
`μ < σ`. -/
theorem gv_small {ν : Ordinal.{0}} (hν : ν < Om1) {c : Ordinal.{0}} (hc : c < (gsD ν).B) {σ : Ordinal.{0}}
    (hσ : InE σ) (hg : (gsD ν).g c < σ) : ∃ μ, μ < σ ∧ μ < Om1 ∧ c < (gsD μ).B := by
  have hne : ({μ | μ < Om1 ∧ c < (gsD μ).B} : Set Ordinal.{0}).Nonempty := ⟨ν, hν, hc⟩
  set N := sInf {μ | μ < Om1 ∧ c < (gsD μ).B} with hN
  obtain ⟨hN1, hcN⟩ : N < Om1 ∧ c < (gsD N).B := csInf_mem hne
  have hNν : N ≤ ν := csInf_le' ⟨hν, hc⟩
  have hmin : ∀ μ, μ < N → μ < Om1 → ¬ c < (gsD μ).B := fun μ hμ hμ1 hcμ =>
    absurd (csInf_le' ⟨hμ1, hcμ⟩ : N ≤ μ) (not_le.2 hμ)
  have hgN : (gsD N).g c = (gsD ν).g c := ((gsD_ext hNν hν).2.1 c hcN).symm
  rw [← hgN] at hg
  rcases zero_or_succ_or_isSuccLimit N with h0 | ⟨m, hm⟩ | hlim
  · exact ⟨N, by rw [h0]; exact hσ.pos, hN1, hcN⟩
  · have hm' : N = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < N := by rw [hm']; exact lt_add_one m
    have hm1 : m < Om1 := hmN.trans hN1
    have hBc : (gsD m).B ≤ c := not_lt.1 (hmin m hmN hm1)
    have hγ : (gsD m).γ < σ := by
      have h1 := (gsD m).γ_le_sG hBc
      rw [hm', gsD_succ, GsD.step_g] at hg
      exact h1.trans_lt hg
    have hmσ : m < σ := gsD_lt_of_γ hm1 hσ hγ
    exact ⟨N, by rw [hm']; exact (ev_isSuccLimit_of_inE hσ).add_one_lt hmσ, hN1, hcN⟩
  · obtain ⟨β, hβ, hcβ⟩ := gsD_lim_cof hlim hN1 hcN
    exact absurd hcβ (hmin β hβ (hβ.trans hN1))

theorem gv_ix_lt : gcG 0 + Om1 < gcG 1 := by
  have hE : InE (gcG 1) := Low.opow_eq_self_of_SC (gcG_SC 1)
  exact (inE_indec hE).add_lt (gcG_lt zero_lt_one) (by rw [Br.Om1_eq]; exact gcG_Om1_lt 1)

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem gv_x1_lt : x + 1 < lgG x := (ev_isSuccLimit_of_inE (lgG_facts hx hx1).2.2.2.1).add_one_lt
  (lgG_facts hx hx1).2.1

theorem gv_b_eN : eN (veblen 1 (gpI x + x)) = glA 1 (lgG x + (x + 1)) x :=
  gp_b_eN hx hx1 (omega0_lt_inE hx).le (gv_x1_lt hx hx1)

theorem gv_ba_lt : lgG x + (x + 1) < gq 1 x := by
  have hq := (gm1_facts hx hx1).2.2.2
  have hG : lgG x < gq 1 x := goGl.ba_lt x hx hx1
  exact (inE_indec hq).add_lt hG ((gv_x1_lt hx hx1).trans hG)

theorem gv_b_Z : eN (veblen 1 (gpI x + x)) < evZ (lgG x) := by
  refine go_eN_lt_evZ ?_
  have hZ := evZ_E (lgG x)
  have hGE := (lgG_facts hx hx1).2.2.2.1
  have hGZ : lgG x < evZ (lgG x) := lt_evZ _
  have hi : gpI x < evZ (lgG x) := (evIx_le hGE).trans_lt hGZ
  have hxZ : x < evZ (lgG x) := (lgG_facts hx hx1).2.1.trans hGZ
  have := (isNormal_veblen 1).strictMono ((inE_indec hZ).add_lt hi hxZ)
  rwa [show veblen 1 (evZ (lgG x)) = evZ (lgG x) from epsilon_evZ _] at this

end Base

theorem gv_b_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) :
    veblen 1 (gpI ρ + ρ) ∈ TB ρ σ ∧ pi σ ρ (veblen 1 (gpI ρ + ρ)) = veblen 1 (gpI σ + σ) := by
  have h := gp_b_pi_x hB (t := 0) hB.1.pos
  simp only [add_zero] at h
  exact h

theorem gv_ba_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) :
    lgG ρ + (ρ + 1) ∈ TB ρ σ ∧ pi σ ρ (lgG ρ + (ρ + 1)) = lgG σ + (σ + 1) := by
  obtain ⟨g1, g2⟩ : lgG ρ ∈ TB ρ σ ∧ pi σ ρ (lgG ρ) = lgG σ := goGl.ba_pi σ ρ hB
  obtain ⟨r1, r2⟩ := pi_base hB
  obtain ⟨o1, o2⟩ := one_TB hB
  obtain ⟨s1, s2⟩ := pi_add hB r1 o1
  obtain ⟨t1, t2⟩ := pi_add hB g1 s1
  exact ⟨t1, by rw [t2, s2, g2, r2, o2]⟩

/-- **The recursion `Gs.gsD` as a family over `Ω₁`** (`i₀ = G`, index read `Γ_{x+1}` through `gpI`). -/
noncomputable def gvGs : GvFam where
  F := gsD
  i0 := gcG 0
  i := gpI
  baΩ := fun x => lgG x + (x + 1)
  ix := fun ν hν => (gs_inv ν hν).ix ν (lt_add_one ν)
  hb := fun ν hν x hx hx1 hνx => gsD_b hν hx hx1 hνx
  γ_le := fun ν hν => gsD_γ hν
  cohR := fun β γ hβγ hγ => (gsD_ext hβγ hγ).1
  cohg := fun β γ hβγ hγ => (gsD_ext hβγ hγ).2.1
  small := fun ν hν c hc σ hσ hg => gv_small hν hc hσ hg
  i0_mem := fun S a b ha _ => goGl.ix_mem S a b ha
  ix_lt := gv_ix_lt
  b_eN := fun x hx hx1 => gv_b_eN hx hx1
  ba_lt := fun x hx hx1 => gv_ba_lt hx hx1
  b_Z := fun x hx hx1 => gv_b_Z hx hx1
  b_pi := fun σ ρ hB => gv_b_pi hB
  ba_pi := fun σ ρ hB => gv_ba_pi hB

/-- **THE BOUND `ε_{G+Ω₁}` AS A GATED DIGIT SYSTEM** (no cofinal sequence; base gate `0`; base reading
`φ(1, Γ_{x+1} + x)`: the index `Ω₁` read as `x`). -/
noncomputable def gvU : GvD := gvGs.U

theorem gvU_B : gvU.B = veblen 1 (gcG 0 + Om1) := rfl

theorem gvU_γ : gvU.γ = 0 := rfl

theorem gvU_b (x : Ordinal.{0}) : gvU.b x = veblen 1 (gpI x + x) := rfl

/-- **`gvU` extends every `gsD ν`, `ν < Ω₁`** (readings and gates). -/
theorem gvU_R {ν c : Ordinal.{0}} (hν : ν < Om1) (hc : c < (gsD ν).B) (x : Ordinal.{0}) :
    gvU.R c x = (gsD ν).R c x := gvGs.U_R hν hc x

theorem gvU_g {ν c : Ordinal.{0}} (hν : ν < Om1) (hc : c < (gsD ν).B) : gvU.g c = (gsD ν).g c := gvGs.U_g hν hc

end Googology.Trans.PoR.InaccPsi.R2.Gv

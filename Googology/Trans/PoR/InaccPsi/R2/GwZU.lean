import Googology.Trans.PoR.InaccPsi.R2.GwZRS
import Googology.Trans.PoR.InaccPsi.R2.GwWall
import Googology.Trans.PoR.InaccPsi.R2.GwZb

/-!
# PAST THE WALL: THE UNION AT THE INDEX `ζ_{G+1}`, WHICH READS ITS OWN INDEX

The union of all `gwD c`, `c < ζ_{G+1}` (`G = Γ_{Ω₁+1}`), has the bound `ζ_{G+1} = φ(1, ζ_{G+1})` and cannot read its
index through an earlier system (`gw_wall`).  As a `GwZD` with `N = 1` (readings below `ζ_{Γ_{x+1}+2}`) it reads the
index itself: base reading `b(x) = ζ_{Γ_{x+1}+1}`, base gate `0`:

* `b_cof`: the tower readings `r_k(x)` are cofinal in `ζ_{Γ_{x+1}+1}` (`gwRR_cof`);
* `R_lt_b`: every member reads below `ζ_{Γ_{x+1}+1}` (field `R_lt_Z` of `Gv.GvD`);
* `b_eN`, `b_pi`, `ba_pi`: `ε_{ζ+1} = ϑˣ(Ω₁ + ζ)` and Lemma EXACT for `ζ_{Γ_{ρ+1}+1}` (`gw_eNZ`, `gw_Z_pi`);
* `b_Z`: `ε_{ζ_{Γ+1}+1} < ζ_{Γ+2}`; the readings of the members lie below `ζ_{Γ+1} < ζ_{Γ+2}`;
* a code with gate below an `ε`-number `σ` lies in a member with base gate below `σ` (`gwZ_small`, as in
  `GwFam.small'`).

Its base gate is `0 < K`, so `ζ_{G+1}` is located: `Λ⁺ = ι(Γ(ζ_{G+1})·ω)`, and so is every `ε_{ζ_{G+1}+k}` (the steps
of the union): **THE FRONTIER PASSES `ι(Γ(ζ_{G+1}))`; new frontier `ι(Γ(ε_{ζ_{G+1}+ω}))`**.

* `gwZ_eq_veb2` (`ζ_{G+1} = φ(2, G+1)`), `gwZ_lt_G1`, `gwZN`, `gwZR`, `gwZg`, `gwZ_small`, `gwZU` (**THE UNION AT
  `ζ_{G+1}`**), `gwZU_B`, `gwZU_γ`, `gwZU_R`, `gwZU_g`;
* `gwZU_loc` (**`ζ_{G+1}` IS LOCATED**), `gwZS` (the steps), `gwZS_B`, `gwZS_γ`, `gwZw`, `gwZw_codes`, `gwZw_cof`,
  `gwZw_enum`, `gwZw_capV`, `gwZw_road` (**THE ROAD**), `gwZw_le_Om2`, `gwZw_P`, `gwZw_fr_order`.

No new axiom.  New definitions: `gwZN`, `gwZR`, `gwZg`, `gwZU`, `gwZS`, `gwZw`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gw

open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Go
  Googology.Trans.PoR.InaccPsi.R2.Gp
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The bound `ζ_{G+1}` -/

theorem gw_two_lt_w : (2 : Ordinal.{0}) < ω := by exact_mod_cast natCast_lt_omega0 2

theorem gw_two_lt_G : (2 : Ordinal.{0}) < gcG 0 :=
  gw_two_lt_w.trans (omega0_lt_inE (Low.opow_eq_self_of_SC (gcG_SC 0)))

/-- **`ζ_{G+1} = φ(2, G + 1)`.** -/
theorem gwZ_eq_veb2 : gwZ = veblen 2 (gcG 0 + 1) := by
  have hG2 : veblen 2 (gcG 0) = gcG 0 := (gcG_SC 0).veblen_right gw_two_lt_G
  have hlt : gcG 0 < veblen 2 (gcG 0 + 1) := by
    conv_lhs => rw [← hG2]
    exact (veblen_lt_veblen_iff_right).2 (lt_add_one _)
  refine le_antisymm (evZ_le hlt (veblen_veblen_of_lt one_lt_two _)) ?_
  obtain ⟨i, hi⟩ := gw_LuP2 (gcG 0)
  have hGi : gcG 0 < i := by
    have h := lt_evZ (gcG 0)
    rw [← hi, ← hG2] at h
    rw [hG2] at h
    exact (veblen_lt_veblen_iff_right).1 (by rw [hG2]; exact h)
  show veblen 2 (gcG 0 + 1) ≤ evZ (gcG 0)
  rw [← hi]
  exact (veblen_le_veblen_iff_right).2 (Order.add_one_le_of_lt hGi)

theorem gwZ_lt_G1 : gwZ < gcG 1 := by
  rw [gwZ_eq_veb2]
  have h1 : gcG 0 + 1 < gcG 1 := (gcG_SC 1).add_one_lt (gcG_lt zero_lt_one)
  exact (gcG_SC 1).2 2 (gw_two_lt_G.trans (gcG_lt zero_lt_one)) _ h1

theorem gwZ_E : InE gwZ := evZ_E _

/-! ## The union -/

/-- The first system `gwD ν` containing `c`. -/
noncomputable def gwZN (c : Ordinal.{0}) : Ordinal.{0} := sInf {ν | ν < gwZ ∧ c < (gwD ν).B}

/-- The reading of the union. -/
noncomputable def gwZR (c x : Ordinal.{0}) : Ordinal.{0} := (gwD (gwZN c)).R c x

/-- The gate of the union. -/
noncomputable def gwZg (c : Ordinal.{0}) : Ordinal.{0} := (gwD (gwZN c)).g c

theorem gwZ_memB {c : Ordinal.{0}} (hc : c < gwZ) : ∃ ν, ν < gwZ ∧ c < (gwD ν).B := ⟨c, hc, gw_self hc⟩

theorem gwZN_spec {c ν : Ordinal.{0}} (hν : ν < gwZ) (hc : c < (gwD ν).B) :
    gwZN c ≤ ν ∧ gwZN c < gwZ ∧ c < (gwD (gwZN c)).B := by
  have hne : ({ν | ν < gwZ ∧ c < (gwD ν).B} : Set Ordinal.{0}).Nonempty := ⟨ν, hν, hc⟩
  have hm := csInf_mem hne
  exact ⟨csInf_le' ⟨hν, hc⟩, hm.1, hm.2⟩

theorem gwZN_min {c μ : Ordinal.{0}} (hμ : μ < gwZN c) (hμl : μ < gwZ) : ¬ c < (gwD μ).B := fun hcμ =>
  absurd (csInf_le' ⟨hμl, hcμ⟩ : gwZN c ≤ μ) (not_le.2 hμ)

theorem gwZN_high {c : Ordinal.{0}} (hc : gwZ ≤ c) : gwZN c = 0 := by
  unfold gwZN
  have he : ({ν | ν < gwZ ∧ c < (gwD ν).B} : Set Ordinal.{0}) = ∅ := by
    ext ν
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hν hcν
    exact absurd ((hcν.trans (gw_B_lt_Z hν))) (not_lt.2 hc)
  rw [he]; exact Ordinal.sInf_empty

theorem gwZR_eq {c ν : Ordinal.{0}} (hν : ν < gwZ) (hc : c < (gwD ν).B) (x : Ordinal.{0}) :
    gwZR c x = (gwD ν).R c x := by
  obtain ⟨h1, -, h3⟩ := gwZN_spec hν hc
  exact ((gw_ext h1 hν).1 c x h3).symm

theorem gwZg_eq {c ν : Ordinal.{0}} (hν : ν < gwZ) (hc : c < (gwD ν).B) : gwZg c = (gwD ν).g c := by
  obtain ⟨h1, -, h3⟩ := gwZN_spec hν hc
  exact ((gw_ext h1 hν).2 c h3).symm

theorem gwZR_succ (c x : Ordinal.{0}) : gwZR (c + 1) x = gwZR c x + 1 := by
  rcases lt_or_ge c gwZ with h | h
  · have h1 : c + 1 < gwZ := (ev_isSuccLimit_of_inE gwZ_E).add_one_lt h
    rw [gwZR_eq h1 (gw_self h1), gwZR_eq h1 ((lt_add_one c).trans (gw_self h1)), (gwD (c + 1)).R_succ]
  · unfold gwZR
    rw [gwZN_high h, gwZN_high (h.trans (le_self_add (a := c) (b := 1))), (gwD 0).R_succ]

theorem gwZg_le_succ (c : Ordinal.{0}) : gwZg c ≤ gwZg (c + 1) := by
  rcases lt_or_ge c gwZ with h | h
  · have h1 : c + 1 < gwZ := (ev_isSuccLimit_of_inE gwZ_E).add_one_lt h
    rw [gwZg_eq h1 (gw_self h1), gwZg_eq h1 ((lt_add_one c).trans (gw_self h1))]
    exact (gwD (c + 1)).g_le_succ c
  · unfold gwZg
    rw [gwZN_high h, gwZN_high (h.trans (le_self_add (a := c) (b := 1)))]; exact (gwD 0).g_le_succ c

theorem gwZ_zero_lt : (0 : Ordinal.{0}) < gwZ := gwZ_E.pos

/-- **A code of the union with gate below an `ε`-number `σ` lies in a member with base gate below `σ`.** -/
theorem gwZ_small {c σ : Ordinal.{0}} (hc : c < gwZ) (hσ : InE σ) (hg : gwZg c < σ) :
    ∃ μ, μ < gwZ ∧ c < (gwD μ).B ∧ (gwD μ).γ < σ := by
  obtain ⟨n, hn1, hn⟩ := gwZ_memB hc
  obtain ⟨-, hN1, hcN⟩ := gwZN_spec hn1 hn
  have hgN : gwZg c = (gwD (gwZN c)).g c := rfl
  rcases zero_or_succ_or_isSuccLimit (gwZN c) with h0 | ⟨m, hm⟩ | hlim
  · refine ⟨gwZN c, hN1, hcN, ?_⟩
    rw [h0, gwD_zero, gw0_γ]; exact hσ.pos
  · have hm' : gwZN c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < gwZN c := by rw [hm']; exact lt_add_one m
    have hml : m < gwZ := hmN.trans hN1
    have hBc : (gwD m).B ≤ c := not_lt.1 (gwZN_min hmN hml)
    have hs : gwD (gwZN c) = GvD.ofGs (gwD m).step := by rw [hm']; exact gwD_succ m
    refine ⟨gwZN c, hN1, hcN, ?_⟩
    rw [hgN, hs] at hg
    rw [hs]
    exact ((gwD m).γ_le_sG hBc).trans_lt hg
  · exfalso
    rw [gw_B hN1] at hcN
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ hlim)).1 hcN
    obtain ⟨d, hd, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    have hdl : d < gwZ := hd.trans hN1
    refine gwZN_min hd hdl ?_
    rw [gw_B hdl]; exact hct.trans_le ((isNormal_veblen 1).monotone htd)

theorem gwZ_b_lt {μ x : Ordinal.{0}} (hμ : μ < gwZ) (hx : InE x) (hx1 : x < Om1) (hμx : (gwD μ).γ < x) :
    (gwD μ).b x < evZ (lgG x) :=
  (lt_eN _).trans ((gwD μ).b_Z x hx hx1 hμx)

theorem gw_Z2_eq (x : Ordinal.{0}) : gwZn x (1 + 1) = evZ (evZ (lgG x)) := rfl

/-- **THE UNION AT `ζ_{G+1}`**: bound `ζ_{G+1}`, base gate `0`, base reading `ζ_{Γ_{x+1}+1}` (its own index),
readings below `ζ_{Γ_{x+1}+2}` (`N = 1`). -/
noncomputable def gwZU : GwZD where
  N := 1
  B := gwZ
  γ := 0
  γ_lt := gv_Om1_pos
  γ_cl := fun _ hZ _ _ => hZ.1
  γ_G := fun h => absurd h gw_G_lt_Z.ne'
  R := gwZR
  g := gwZg
  b := fun x => evZ (lgG x)
  ba := fun x => evZ (lgG x)
  ix := gwZ
  B_E := gwZ_E
  G_le := gw_G_lt_Z.le
  B_lt1 := gwZ_lt_G1
  B_ix := (epsilon_evZ _).symm
  ix_mem := fun S a b ha _ => by
    rw [gwZ_eq_veb2]
    exact CSet.phi_mem (gr_cst_mem ha b 2 (gw_two_lt_w.trans (omega0_lt_gamma 1)))
      (CSet.succ_mem (gmS_G0_mem S ha))
  g_lt := fun c hc => by
    rw [gwZg_eq hc (gw_self hc)]; exact (gwD c).g_lt c (gw_self hc)
  g_zero := by rw [gwZg_eq gwZ_zero_lt (gwD 0).B_pos]; exact (gwD 0).g_zero
  g_nat := fun k => by rw [gwZg_eq gwZ_zero_lt ((gwD 0).nat_lt_B k)]; exact (gwD 0).g_nat k
  g_E := by rw [gwZg_eq gwZ_zero_lt (gwD 0).E_lt_B]; exact (gwD 0).g_E
  g_lowE := fun c hc => by rw [gwZg_eq gwZ_zero_lt (hc.trans (gwD 0).E_lt_B)]; exact (gwD 0).g_lowE c hc
  g_G0 := fun h => by
    rw [gwZg_eq h (gw_self h)]; exact (gwD (gcG 0)).g_G0 (gw_self h)
  g_add := fun Z hZ hωZ x y hxy hgx hgy => by
    obtain ⟨n, hn1, hn⟩ := gwZ_memB hxy
    have hx : x < (gwD n).B := lt_of_le_of_lt le_self_add hn
    have hy : y < (gwD n).B := lt_of_le_of_lt le_add_self hn
    rw [gwZg_eq hn1 hn]; rw [gwZg_eq hn1 hx] at hgx; rw [gwZg_eq hn1 hy] at hgy
    exact (gwD n).g_add Z hZ hωZ x y hn hgx hgy
  g_opow := fun Z hZw hωZ y hy hg => by
    obtain ⟨n, hn1, hn⟩ := gwZ_memB hy
    have hy' : y < (gwD n).B := lt_of_le_of_lt (right_le_opow y one_lt_omega0) hn
    rw [gwZg_eq hn1 hn]; rw [gwZg_eq hn1 hy'] at hg
    exact (gwD n).g_opow Z hZw hωZ y hn hg
  code_gate := fun Z hZ1 hZ0 hZa hZp At hAt c hc hcB => by
    obtain ⟨n, hn1, hn⟩ := gwZ_memB hcB
    rw [gwZg_eq hn1 hn]
    exact (gwD n).code_gate Z hZ1 hZ0 hZa hZp At (fun s hs => (hAt s hs).imp_right
      (fun h => (gw_B_lt_Z hn1).le.trans h)) c hc hn
  g_succ := fun Z hZ c hc hg => by
    obtain ⟨n, hn1, hn⟩ := gwZ_memB hc
    have hc' : c < (gwD n).B := (lt_add_one c).trans hn
    rw [gwZg_eq hn1 hn]; rw [gwZg_eq hn1 hc'] at hg
    exact (gwD n).g_succ Z hZ c hn hg
  g_le_succ := gwZg_le_succ
  mem := fun S a b ha c hc hg => by
    obtain ⟨n, hn1, hn⟩ := gwZ_memB hc
    rw [gwZg_eq hn1 hn] at hg
    exact (gwD n).mem S a b ha c hn hg
  R_zero := fun x => by rw [gwZR_eq gwZ_zero_lt (gwD 0).B_pos]; exact (gwD 0).R_zero x
  R_nat := fun k x => by rw [gwZR_eq gwZ_zero_lt ((gwD 0).nat_lt_B k)]; exact (gwD 0).R_nat k x
  R_E := fun x => by rw [gwZR_eq gwZ_zero_lt (gwD 0).E_lt_B]; exact (gwD 0).R_E x
  R_succ := gwZR_succ
  R_pos := fun x hx hx1 c hc0 hc hg => by
    obtain ⟨n, hn1, hn⟩ := gwZ_memB hc
    rw [gwZR_eq hn1 hn]; rw [gwZg_eq hn1 hn] at hg
    exact (gwD n).R_pos x hx hx1 c hc0 hn hg
  R_omega := fun x hx hx1 c hω hc hg => by
    obtain ⟨n, hn1, hn⟩ := gwZ_memB hc
    rw [gwZR_eq hn1 hn]; rw [gwZg_eq hn1 hn] at hg
    exact (gwD n).R_omega x hx hx1 c hω hn hg
  R_lt_b := fun x hx hx1 _ c hc hg => by
    obtain ⟨n, hn1, hn⟩ := gwZ_memB hc
    rw [gwZR_eq hn1 hn]; rw [gwZg_eq hn1 hn] at hg
    exact (gwD n).R_lt_Z x hx hx1 c hn hg
  R_lt_Z := fun x hx hx1 c hc hg => by
    obtain ⟨n, hn1, hn⟩ := gwZ_memB hc
    rw [gwZR_eq hn1 hn]; rw [gwZg_eq hn1 hn] at hg
    rw [gw_Z2_eq]
    exact ((gwD n).R_lt_Z x hx hx1 c hn hg).trans (lt_evZ _)
  mono := fun x hx hx1 c hc d hdc hgc hgd => by
    obtain ⟨n, hn1, hn⟩ := gwZ_memB hc
    have hd : d < (gwD n).B := hdc.trans hn
    rw [gwZR_eq hn1 hn, gwZR_eq hn1 hd]; rw [gwZg_eq hn1 hn] at hgc; rw [gwZg_eq hn1 hd] at hgd
    exact (gwD n).mono x hx hx1 c hn d hdc hgc hgd
  cof := fun x hx hx1 c hc hg ν hν => by
    obtain ⟨n, hn1, hn⟩ := gwZ_memB hc
    rw [gwZR_eq hn1 hn] at hν; rw [gwZg_eq hn1 hn] at hg
    obtain ⟨d, hdc, hgd, hνd⟩ := (gwD n).cof x hx hx1 c hn hg ν hν
    have hd : d < (gwD n).B := hdc.trans hn
    exact ⟨d, hdc, by rw [gwZg_eq hn1 hd]; exact hgd, by rw [gwZR_eq hn1 hd]; exact hνd⟩
  b_cof := fun x hx hx1 _ ν hν => by
    obtain ⟨k, hk⟩ := gwRR_cof hx hx1 hν
    have hkZ : gwT k < gwZ := gwT_lt k
    have hkB : gwT k < (gwD (gwT k)).B := gw_self hkZ
    refine ⟨gwT k, hkZ, ?_, ?_⟩
    · rw [gwZg_eq hkZ hkB]; exact gwRR_g hx hx1 k
    · rw [gwZR_eq hkZ hkB]; exact hk
  b_E := fun _ _ _ _ => evZ_E _
  x_lt_b := fun x hx hx1 _ => (lgG_facts hx hx1).2.1.trans (lt_evZ _)
  b_eN := fun x hx hx1 _ => gw_eNZ hx hx1
  ba_lt := fun x hx hx1 _ => gn_evZG_lt1 hx hx1
  b_Z := fun x _ _ _ => by rw [gw_Z2_eq]; exact go_eN_lt_evZ (lt_evZ _)
  b_pi := fun _ _ hB _ => gw_Z_pi hB
  ba_pi := fun _ _ hB _ => gw_Z_pi hB
  ex := fun σ ρ hB c hc hg => by
    obtain ⟨n, hn1, hn⟩ := gwZ_memB hc
    rw [gwZR_eq hn1 hn, gwZR_eq hn1 hn]; rw [gwZg_eq hn1 hn] at hg
    exact (gwD n).ex σ ρ hB c hn hg
  dig := fun σ ρ hB _ d hd hg P P' hat => by
    obtain ⟨μ, hμ, hdμ, hγμ⟩ := gwZ_small hd hB.1 hg
    rw [gwZR_eq hμ hdμ, gwZR_eq hμ hdμ]; rw [gwZg_eq hμ hdμ] at hg
    exact (gwD μ).dig σ ρ hB hγμ d hdμ hg P P' (fun β hβ hβe =>
      hat β hβ (hβe.trans (gwZ_b_lt hμ hB.2.1 hB.2.2.2 (hγμ.trans hB.2.2.1))))
  ld := fun c hl hc => by
    obtain ⟨n, hn1, hn⟩ := gwZ_memB hc
    obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := (gwD n).ld c hl hn
    have hcpn : cp < (gwD n).B := hcp.trans hn
    refine ⟨cp, lp, T, hcp, by rw [gwZg_eq hn1 hn, gwZg_eq hn1 hcpn]; exact hgcp, fun x hx hx1 hg => ?_,
      fun σ ρ hB hg => hex σ ρ hB (by rw [← gwZg_eq hn1 hn]; exact hg)⟩
    rw [gwZg_eq hn1 hn] at hg
    rw [gwZR_eq hn1 hn, gwZR_eq hn1 hcpn]
    exact hdec x hx hx1 hg

theorem gwZU_B : gwZU.B = gwZ := rfl

theorem gwZU_γ : gwZU.γ = 0 := rfl

theorem gwZU_N : gwZU.N = 1 := rfl

theorem gwZU_b (x : Ordinal.{0}) : gwZU.b x = evZ (lgG x) := rfl

/-- **The union extends every `gwD ν`, `ν < ζ_{G+1}`** (readings). -/
theorem gwZU_R {ν c : Ordinal.{0}} (hν : ν < gwZ) (hc : c < (gwD ν).B) (x : Ordinal.{0}) :
    gwZU.R c x = (gwD ν).R c x := gwZR_eq hν hc x

/-- **The union extends every `gwD ν`, `ν < ζ_{G+1}`** (gates). -/
theorem gwZU_g {ν c : Ordinal.{0}} (hν : ν < gwZ) (hc : c < (gwD ν).B) : gwZU.g c = (gwD ν).g c := gwZg_eq hν hc

/-! ## Location of `ζ_{G+1}` and of its steps -/

/-- **`ζ_{G+1}` IS LOCATED**: `Λ⁺ = ι(Γ(ζ_{G+1})·ω)`, `P(Γ(ζ_{G+1})·ω) < L(0)`. -/
theorem gwZU_loc (S : InaccSeq.{0}) : ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG gwZ * ω) ∧
    upsilon (xtB1 X) = Pv S (gcG gwZ * ω) ∧ Pv S (gcG gwZ * ω) < Nc.ncL S 0 :=
  gwZ_locD gwZU S (gv_K_pos S)

/-- **The steps of the union**: `gwZS 0 = gwZU`, `gwZS (k+1) = (gwZS k).step` (bounds `ε_{ζ_{G+1}+k}`). -/
noncomputable def gwZS : ℕ → GwZD
  | 0 => gwZU
  | k + 1 => (gwZS k).step

theorem gwZS_γ : ∀ k : ℕ, (gwZS k).γ = 0
  | 0 => rfl
  | k + 1 => by show (gwZS k).step.γ = 0; rw [GwZD.step_γ]; exact gwZS_γ k

theorem gwZS_B : ∀ k : ℕ, (gwZS k).B = veblen 1 (gwZ + k)
  | 0 => by rw [Nat.cast_zero, add_zero]; exact (epsilon_evZ _).symm
  | k + 1 => by
    show (gwZS k).step.B = _
    rw [GwZD.step_B, gwZS_B k, go_eN_veb, Nat.cast_succ, add_assoc]

/-- **The new bound** `ε_{ζ_{G+1}+ω}`. -/
noncomputable def gwZw : Ordinal.{0} := veblen 1 (gwZ + ω)

theorem gwZw_lim : IsSuccLimit gwZw := ev_isSuccLimit_of_inE (omega0_opow_epsilon _)

theorem gwZw_codes {c : Ordinal.{0}} (hc : c < gwZw) : ∃ k : ℕ, c < (gwZS k).B := by
  obtain ⟨t, ht, hct⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ isSuccLimit_omega0)).1 hc
  obtain ⟨d, hd, htd⟩ := (lt_add_iff omega0_ne_zero).1 ht
  obtain ⟨k, rfl⟩ := lt_omega0.1 hd
  exact ⟨k, by rw [gwZS_B]; exact hct.trans_le ((isNormal_veblen 1).monotone htd)⟩

theorem gwZw_cof (S : InaccSeq.{0}) {l : Ordinal.{0}} (hl : l < iota S (gcG gwZw)) :
    ∃ k : ℕ, l < iota S (gcG (gwZS k).B * ω) := by
  have hlim : IsSuccLimit (gcG gwZw) := ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC (gcG_SC _))
  rw [iota_limit hlim] at hl
  haveI : Nonempty (Iio (gcG gwZw)) := ⟨⟨0, hlim.bot_lt⟩⟩
  obtain ⟨e, he⟩ := (lt_ciSup_iff (iota_bdd _)).1 hl
  obtain ⟨β, hβ, heβ⟩ := gcG_lt_of_lt_limit gwZw_lim e.2
  obtain ⟨k, hk⟩ := gwZw_codes hβ
  refine ⟨k, he.trans_le (iota_mono _ _ ((heβ.trans (gcG_lt hk)).trans_le ?_).le)⟩
  exact le_mul_of_one_le_right' one_lt_omega0.le

/-- **ENUM-REACH at every range restart below `ι(Γ(ε_{ζ_{G+1}+ω}))`, fixed points included** (UNCONDITIONAL). -/
theorem gwZw_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG gwZw)) :
    CdUpper S l ∧ CdLower S l := by
  obtain ⟨k, h⟩ := gwZw_cof S hl
  exact gwZ_locD_enum (gwZS k) S (by rw [gwZS_γ]; exact gv_K_pos S) hr h

/-- **CapV at every range restart below `ι(Γ(ε_{ζ_{G+1}+ω}))`** (UNCONDITIONAL). -/
theorem gwZw_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG gwZw)) :
    CdCapV S l := by
  obtain ⟨k, h⟩ := gwZw_cof S hl
  exact gwZ_locD_capV (gwZS k) S (by rw [gwZS_γ]; exact gv_K_pos S) hr h

/-- **THE ROAD**: UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ(ε_{ζ_{G+1}+ω}))` (CapV also `υ_λ < L(ω)`), (CL), EQ,
TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem gwZw_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG gwZw) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG gwZw) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG gwZw) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  gv_road_of S _ (fun _ hr h => gwZw_enum S hr h) (fun _ hr h => gwZw_capV S hr h) hU hL hV hC hEQ hrest hB2

theorem gwZw_lt_G1 : gwZw < gcG 1 := by
  have hE : InE (gcG 1) := Low.opow_eq_self_of_SC (gcG_SC 1)
  have h1 : gwZ + ω < gcG 1 := (inE_indec hE).add_lt gwZ_lt_G1 (omega0_lt_inE hE)
  exact (gcG_SC 1).2 1 (one_lt_omega0.trans (omega0_lt_inE hE)) _ h1

/-- **`Γ(ε_{ζ_{G+1}+ω}) < Ω₂`.** -/
theorem gwZw_le_Om2 : gcG gwZw < Om (1 + 1) := by
  have hBE : InE Tf.tfBG := Low.opow_eq_self_of_SC Tf.tfBG_SC
  have hO : (Om1 : Ordinal.{0}) < Tf.tfBG := Tf.tfBG_gt
  have h1 : (1 : Ordinal.{0}) < Tf.tfBG := one_lt_omega0.trans (omega0_lt_inE hBE)
  have hG1 : gcG 1 < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) h1)
  have h2 : gcG gwZw < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) (gwZw_lt_G1.trans hG1))
  exact h2.trans Tf.tfBG_lt_Om2

/-- **`P(Γ(ε_{ζ_{G+1}+ω})) < L(0)`.** -/
theorem gwZw_P (S : InaccSeq.{0}) : Pv S (gcG gwZw) < Nc.ncL S 0 := ga_Pv_lt_L0 S gwZw_le_Om2.le

/-- **The order of the frontiers**: `ι(Γ(ζ_{G+1})) < ι(Γ(ζ_{G+1})·ω) ≤ ι(Γ(ε_{ζ_{G+1}+ω})) ≤ ι(Ω₂)`,
`P(Γ(ε_{ζ_{G+1}+ω})) ≤ P(Ω₂) < L(0)`. -/
theorem gwZw_fr_order (S : InaccSeq.{0}) :
    gwZ < gwZw ∧ iota S (gcG gwZ) < iota S (gcG gwZ * ω) ∧ iota S (gcG gwZ * ω) ≤ iota S (gcG gwZw) ∧
      iota S (gcG gwZw) ≤ iota S (Om (1 + 1)) ∧ Pv S (gcG gwZw) ≤ Pv S (Om (1 + 1)) ∧
      Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have hZw : gwZ < gwZw := by
    have e : veblen 1 gwZ = gwZ := epsilon_evZ _
    calc gwZ = veblen 1 gwZ := e.symm
      _ < veblen 1 (gwZ + ω) := (isNormal_veblen 1).strictMono (lt_add_of_pos_right _ omega0_pos)
  have hg0 := gwZ_locD_g gwZU S (gv_K_pos S)
  have hgood : Bt.Good S (gcG gwZU.B) :=
    gs_good (K := gwZU.step.toRS.K) fun Z _ hKZ =>
      GxCl.atom (gsmG_atom (K := gwZU.step.toRS.K) gwZU.B_lt_NB (hg0.trans_le hKZ))
  have hG : InE (gcG gwZ) := Low.opow_eq_self_of_SC (gcG_SC _)
  have hV : InE (gcG gwZw) := Low.opow_eq_self_of_SC (gcG_SC _)
  exact ⟨hZw, cd_iota_lt_of_good hgood (lt_mul_of_one_lt_right hG.pos one_lt_omega0),
    iota_mono _ _ (InE.mul_lt hV (gcG_lt hZw) (omega0_lt_inE hV)).le,
    iota_mono _ _ gwZw_le_Om2.le, Nm.Pv_mono gwZw_le_Om2.le, ga_Pv_lt_L0 S le_rfl⟩

end Googology.Trans.PoR.InaccPsi.R2.Gw

import Googology.Trans.PoR.InaccPsi.R2.HcVRS

/-!
# HcCh: THE UNION OF AN `ω`-CHAIN OF DIGIT SYSTEMS; THE CODE `φ(ω, G+1)` IS LOCATED

An `ω`-chain (`HcCh`) is a sequence `D k : Hc.HcVD` with base gate `0`, increasing bounds `B_k`, each extending the
previous one (readings and gates), whose bounds are cofinal in an `ε`-fixed point `B` and whose base readings
`b_k(x)` are cofinal in an `ε`-fixed point `b(x) < B_x(x)` with Lemma EXACT.  Its union (`HcCh.U`) is again an
`HcVD`: bound `B`, base gate `0`, base reading `b(x)`, bound field `evZ(b(x))`; every field below `B` comes from the
first member containing the code.

The chain `Hb.hbTG k` (bounds `N_{k+2}(G) = φ(k+3, G+1)`, base readings `N_{k+2}(Γ_{x+1})`) is an `ω`-chain with
`B = φ(ω, G+1)` and `b(x) = B_ω(x)` (`hcWG`): its union `hcWU` reads every code of the chain as the chain does, so
**the wall `Hb.hb_wall_Tw` is passed** (it was a wall only for the bound field `Z(x) ≤ B_ω(x)`), and the code
`φ(ω, G+1)` itself is located: `Λ⁺ = ι(Γ(φ(ω, G+1))·ω)`, `P(Γ(φ(ω, G+1))·ω) < L(0)` (`hcWU_loc`).

* `HcCh`, `HcCh.R_coh`, `HcCh.g_coh`, `HcCh.N`, `HcCh.R_eq`, `HcCh.g_eq`, `HcCh.U` (**THE UNION OF AN `ω`-CHAIN**),
  `HcCh.U_R`, `HcCh.U_g`, `HcCh.U_B`, `HcCh.U_b`;
* `hc_Bw_pi` (**Lemma EXACT for `B_ω(ρ) = ϑᵖ(Ω₁·ω + Γ_{ρ+1})`**), `hcWG` (the chain `Hb.hbTG` as an `ω`-chain),
  `hcWU`, `hcWU_R`, `hcWU_g`, `hcWU_B` (**THE SYSTEM AT `φ(ω, G+1)`**), `hcWU_loc` (**`φ(ω, G+1)` IS LOCATED**),
  `hcWU_enum`, `hcWU_capV`, `hcWU_road`, `hcWU_P`.

No new axiom.  New definitions: `HcCh`, `HcCh.N`, `HcCh.R`, `HcCh.g`, `HcCh.U`, `hcWG`, `hcWU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hc

open Googology.Trans.PoR.InaccPsi.R2.Hb
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

/-! ## `ω`-chains -/

/-- **An `ω`-chain of digit systems** with base gate `0`, union bound `B` and union base reading `b`. -/
structure HcCh where
  D : ℕ → HcVD
  B : Ordinal.{0}
  b : Ordinal.{0} → Ordinal.{0}
  γ0 : ∀ k, (D k).γ = 0
  B_mono : ∀ k, (D k).B ≤ (D (k + 1)).B
  B_lt : ∀ k, (D k).B < B
  B_cof : ∀ c, c < B → ∃ k, c < (D k).B
  R_ext : ∀ k c x, c < (D k).B → (D (k + 1)).R c x = (D k).R c x
  g_ext : ∀ k c, c < (D k).B → (D (k + 1)).g c = (D k).g c
  B_lt1 : B < gcG 1
  B_fix : veblen 1 B = B
  B_mem : ∀ (S : InaccSeq.{0}) (a b : Ordinal.{0}), 0 < a → 0 < b → B ∈ S.CSet a b
  b_ge : ∀ k x, InE x → x < Om1 → (D k).b x ≤ b x
  b_cof : ∀ x, InE x → x < Om1 → ∀ ν, ν < b x → ∃ k, ν < (D k).b x
  b_fix : ∀ x, InE x → x < Om1 → veblen 1 (b x) = b x
  b_gt : ∀ x, InE x → x < Om1 → x < b x
  b_lt : ∀ x, InE x → x < Om1 → b x < hcBR x
  b_pi : ∀ σ ρ, Bases σ ρ → b ρ ∈ TB ρ σ ∧ pi σ ρ (b ρ) = b σ

namespace HcCh

variable (C : HcCh)

theorem B_mono' {k k' : ℕ} (h : k ≤ k') : (C.D k).B ≤ (C.D k').B := by
  induction k', h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact ih.trans (C.B_mono n)

theorem R_coh {k k' : ℕ} (h : k ≤ k') {c : Ordinal.{0}} (hc : c < (C.D k).B) (x : Ordinal.{0}) :
    (C.D k').R c x = (C.D k).R c x := by
  induction k', h using Nat.le_induction with
  | base => rfl
  | succ n hkn ih => rw [C.R_ext n c x (hc.trans_le (C.B_mono' hkn)), ih]

theorem g_coh {k k' : ℕ} (h : k ≤ k') {c : Ordinal.{0}} (hc : c < (C.D k).B) : (C.D k').g c = (C.D k).g c := by
  induction k', h using Nat.le_induction with
  | base => rfl
  | succ n hkn ih => rw [C.g_ext n c (hc.trans_le (C.B_mono' hkn)), ih]

theorem B_E : InE C.B := by
  have h := veblen_veblen_of_lt zero_lt_one C.B; rw [C.B_fix, veblen_zero_apply] at h; exact h

theorem B_lim : IsSuccLimit C.B := ev_isSuccLimit_of_inE C.B_E

/-- The first member containing the code `c` (`0` above the union bound). -/
noncomputable def N (c : Ordinal.{0}) : ℕ := sInf {k : ℕ | c < (C.D k).B}

/-- The union reading. -/
noncomputable def R (c x : Ordinal.{0}) : Ordinal.{0} := (C.D (C.N c)).R c x

/-- The union gate. -/
noncomputable def g (c : Ordinal.{0}) : Ordinal.{0} := (C.D (C.N c)).g c

theorem N_spec {c : Ordinal.{0}} {k : ℕ} (hc : c < (C.D k).B) : C.N c ≤ k ∧ c < (C.D (C.N c)).B :=
  ⟨Nat.sInf_le hc, Nat.sInf_mem (s := {k : ℕ | c < (C.D k).B}) ⟨k, hc⟩⟩

theorem R_eq {c : Ordinal.{0}} {k : ℕ} (hc : c < (C.D k).B) (x : Ordinal.{0}) : C.R c x = (C.D k).R c x := by
  obtain ⟨h1, h2⟩ := C.N_spec hc
  exact (C.R_coh h1 h2 x).symm

theorem g_eq {c : Ordinal.{0}} {k : ℕ} (hc : c < (C.D k).B) : C.g c = (C.D k).g c := by
  obtain ⟨h1, h2⟩ := C.N_spec hc
  exact (C.g_coh h1 h2).symm

theorem N_high {c : Ordinal.{0}} (hc : C.B ≤ c) : C.N c = 0 := by
  have : {k : ℕ | c < (C.D k).B} = ∅ := by
    ext k; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    exact (C.B_lt k).le.trans hc
  unfold HcCh.N; rw [this, Nat.sInf_empty]

theorem R_succ' (c x : Ordinal.{0}) : C.R (c + 1) x = C.R c x + 1 := by
  rcases lt_or_ge c C.B with hc | hc
  · obtain ⟨k, hk⟩ := C.B_cof _ (C.B_lim.add_one_lt hc)
    rw [C.R_eq hk, C.R_eq ((lt_add_one c).trans hk)]; exact (C.D k).R_succ c x
  · unfold HcCh.R; rw [C.N_high hc, C.N_high (hc.trans le_self_add)]; exact (C.D 0).R_succ c x

theorem g_le_succ' (c : Ordinal.{0}) : C.g c ≤ C.g (c + 1) := by
  rcases lt_or_ge c C.B with hc | hc
  · obtain ⟨k, hk⟩ := C.B_cof _ (C.B_lim.add_one_lt hc)
    rw [C.g_eq hk, C.g_eq ((lt_add_one c).trans hk)]; exact (C.D k).g_le_succ c
  · unfold HcCh.g; rw [C.N_high hc, C.N_high (hc.trans le_self_add)]; exact (C.D 0).g_le_succ c

theorem γ_lt {k : ℕ} {x : Ordinal.{0}} (hx : InE x) : (C.D k).γ < x := by rw [C.γ0 k]; exact hx.pos

theorem b_E {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : InE (C.b x) := hc_fix_E (C.b_fix x hx hx1)

theorem b_lt1 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : C.b x < gq 1 x :=
  (C.b_lt x hx hx1).trans (hcBR_lt1 hx hx1)

theorem evZ_b_le {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : evZ (C.b x) ≤ hcBR x :=
  evZ_le (C.b_lt x hx hx1) (veblen_veblen_of_lt (one_lt_omega0.trans (omega0_lt_inE hx)) _)

/-- **THE UNION OF AN `ω`-CHAIN**: bound `B`, base gate `0`, base reading `b(x)`, bound field `evZ(b(x))`. -/
noncomputable def U : HcVD where
  B := C.B
  γ := 0
  γ_lt := Ordinal.omega_pos 1
  γ_cl := fun _ hZ _ _ => hZ.1
  γ_G := fun _ => rfl
  R := C.R
  g := C.g
  b := C.b
  ba := C.b
  ix := C.B
  Z := fun x => evZ (C.b x)
  B_E := C.B_E
  G_le := (C.D 0).G_le.trans (C.B_lt 0).le
  B_lt1 := C.B_lt1
  B_ix := C.B_fix.symm
  Z_fix := fun x _ _ => epsilon_evZ _
  Z_BR := fun x hx hx1 => C.evZ_b_le hx hx1
  ix_mem := fun S _ _ ha hb => C.B_mem S _ _ ha hb
  g_lt := fun c hc => by
    obtain ⟨n, hn⟩ := C.B_cof c hc
    rw [C.g_eq hn]; exact (C.D n).g_lt c hn
  g_zero := by rw [C.g_eq (C.D 0).B_pos]; exact (C.D 0).g_zero
  g_nat := fun k => by rw [C.g_eq ((C.D 0).nat_lt_B k)]; exact (C.D 0).g_nat k
  g_E := by rw [C.g_eq (C.D 0).E_lt_B]; exact (C.D 0).g_E
  g_lowE := fun c hc => by rw [C.g_eq (hc.trans (C.D 0).E_lt_B)]; exact (C.D 0).g_lowE c hc
  g_G0 := fun h => by
    obtain ⟨n, hn⟩ := C.B_cof _ h
    rw [C.g_eq hn]; exact (C.D n).g_G0 hn
  g_add := fun Z hZ hωZ x y hxy hgx hgy => by
    obtain ⟨n, hn⟩ := C.B_cof _ hxy
    have hx : x < (C.D n).B := lt_of_le_of_lt le_self_add hn
    have hy : y < (C.D n).B := lt_of_le_of_lt le_add_self hn
    rw [C.g_eq hn]; rw [C.g_eq hx] at hgx; rw [C.g_eq hy] at hgy
    exact (C.D n).g_add Z hZ hωZ x y hn hgx hgy
  g_opow := fun Z hZw hωZ y hy hg => by
    obtain ⟨n, hn⟩ := C.B_cof _ hy
    have hy' : y < (C.D n).B := lt_of_le_of_lt (right_le_opow y one_lt_omega0) hn
    rw [C.g_eq hn]; rw [C.g_eq hy'] at hg
    exact (C.D n).g_opow Z hZw hωZ y hn hg
  code_gate := fun Z hZ1 hZ0 hZa hZp At hAt c hc hcB => by
    obtain ⟨n, hn⟩ := C.B_cof c hcB
    rw [C.g_eq hn]
    exact (C.D n).code_gate Z hZ1 hZ0 hZa hZp At (fun s hs => (hAt s hs).imp_right
      (fun h => (C.B_lt n).le.trans h)) c hc hn
  g_succ := fun Z hZ c hc hg => by
    obtain ⟨n, hn⟩ := C.B_cof _ hc
    have hc' : c < (C.D n).B := (lt_add_one c).trans hn
    rw [C.g_eq hn]; rw [C.g_eq hc'] at hg
    exact (C.D n).g_succ Z hZ c hn hg
  g_le_succ := C.g_le_succ'
  mem := fun S a b ha c hc hg => by
    obtain ⟨n, hn⟩ := C.B_cof c hc
    rw [C.g_eq hn] at hg
    exact (C.D n).mem S a b ha c hn hg
  R_zero := fun x => by rw [C.R_eq (C.D 0).B_pos]; exact (C.D 0).R_zero x
  R_nat := fun k x => by rw [C.R_eq ((C.D 0).nat_lt_B k)]; exact (C.D 0).R_nat k x
  R_E := fun x => by rw [C.R_eq (C.D 0).E_lt_B]; exact (C.D 0).R_E x
  R_succ := C.R_succ'
  R_pos := fun x hx hx1 c hc0 hc hg => by
    obtain ⟨n, hn⟩ := C.B_cof c hc
    rw [C.R_eq hn]; rw [C.g_eq hn] at hg
    exact (C.D n).R_pos x hx hx1 c hc0 hn hg
  R_omega := fun x hx hx1 c hω hc hg => by
    obtain ⟨n, hn⟩ := C.B_cof c hc
    rw [C.R_eq hn]; rw [C.g_eq hn] at hg
    exact (C.D n).R_omega x hx hx1 c hω hn hg
  R_lt_b := fun x hx hx1 _ c hc hg => by
    obtain ⟨n, hn⟩ := C.B_cof c hc
    rw [C.R_eq hn]; rw [C.g_eq hn] at hg
    exact ((C.D n).R_lt_b x hx hx1 (C.γ_lt hx) c hn hg).trans_le (C.b_ge n x hx hx1)
  R_lt_Z := fun x hx hx1 c hc hg => by
    obtain ⟨n, hn⟩ := C.B_cof c hc
    rw [C.R_eq hn]; rw [C.g_eq hn] at hg
    exact (((C.D n).R_lt_b x hx hx1 (C.γ_lt hx) c hn hg).trans_le (C.b_ge n x hx hx1)).trans (lt_evZ _)
  mono := fun x hx hx1 c hc d hdc hgc hgd => by
    obtain ⟨n, hn⟩ := C.B_cof c hc
    have hd : d < (C.D n).B := hdc.trans hn
    rw [C.R_eq hn, C.R_eq hd]; rw [C.g_eq hn] at hgc; rw [C.g_eq hd] at hgd
    exact (C.D n).mono x hx hx1 c hn d hdc hgc hgd
  cof := fun x hx hx1 c hc hg ν hν => by
    obtain ⟨n, hn⟩ := C.B_cof c hc
    rw [C.R_eq hn] at hν; rw [C.g_eq hn] at hg
    obtain ⟨d, hdc, hgd, hνd⟩ := (C.D n).cof x hx hx1 c hn hg ν hν
    have hd : d < (C.D n).B := hdc.trans hn
    exact ⟨d, hdc, by rw [C.g_eq hd]; exact hgd, by rw [C.R_eq hd]; exact hνd⟩
  b_cof := fun x hx hx1 _ ν hν => by
    obtain ⟨k, hk⟩ := C.b_cof x hx hx1 ν hν
    obtain ⟨c, hc, hgc, hνc⟩ := (C.D k).b_cof x hx hx1 (C.γ_lt hx) ν hk
    exact ⟨c, hc.trans (C.B_lt k), by rw [C.g_eq hc]; exact hgc, by rw [C.R_eq hc]; exact hνc⟩
  b_E := fun x hx hx1 _ => C.b_E hx hx1
  x_lt_b := fun x hx hx1 _ => C.b_gt x hx hx1
  b_eN := fun x hx hx1 _ => gz_eN_fix hx hx1 (C.b_fix x hx hx1) (C.b_gt x hx hx1) (C.b_lt1 hx hx1)
  ba_lt := fun x hx hx1 _ => C.b_lt1 hx hx1
  b_Z := fun x _ _ _ => go_eN_lt_evZ (lt_evZ _)
  b_pi := fun σ ρ hB _ => C.b_pi σ ρ hB
  ba_pi := fun σ ρ hB _ => C.b_pi σ ρ hB
  ex := fun σ ρ hB c hc hg => by
    obtain ⟨n, hn⟩ := C.B_cof c hc
    rw [C.R_eq hn, C.R_eq hn]; rw [C.g_eq hn] at hg
    exact (C.D n).ex σ ρ hB c hn hg
  dig := fun σ ρ hB _ d hd hg P P' hat => by
    obtain ⟨n, hn⟩ := C.B_cof d hd
    rw [C.R_eq hn, C.R_eq hn]; rw [C.g_eq hn] at hg
    exact (C.D n).dig σ ρ hB (C.γ_lt hB.1) d hn hg P P' (fun β hβ hβe =>
      hat β hβ (hβe.trans_le (C.b_ge n ρ hB.2.1 hB.2.2.2)))
  ld := fun c hl hc => by
    obtain ⟨n, hn⟩ := C.B_cof c hc
    obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := (C.D n).ld c hl hn
    have hcpn : cp < (C.D n).B := hcp.trans hn
    refine ⟨cp, lp, T, hcp, by rw [C.g_eq hn, C.g_eq hcpn]; exact hgcp, fun x hx hx1 hg => ?_,
      fun σ ρ hB hg => hex σ ρ hB (by rw [← C.g_eq hn]; exact hg)⟩
    rw [C.g_eq hn] at hg
    rw [C.R_eq hn, C.R_eq hcpn]
    exact hdec x hx hx1 hg

theorem U_B : C.U.B = C.B := rfl

theorem U_γ : C.U.γ = 0 := rfl

theorem U_b (x : Ordinal.{0}) : C.U.b x = C.b x := rfl

/-- **The union extends every member.** -/
theorem U_R {k : ℕ} {c : Ordinal.{0}} (hc : c < (C.D k).B) (x : Ordinal.{0}) : C.U.R c x = (C.D k).R c x :=
  C.R_eq hc x

theorem U_g {k : ℕ} {c : Ordinal.{0}} (hc : c < (C.D k).B) : C.U.g c = (C.D k).g c := C.g_eq hc

end HcCh

/-! ## The chain over `G`: the system at `φ(ω, G+1)` -/

/-- **Lemma EXACT for `B_ω(ρ) = ϑᵖ(Ω₁·ω + Γ_{ρ+1})`.** -/
theorem hc_Bw_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) : hbBw ρ ∈ TB ρ σ ∧ pi σ ρ (hbBw ρ) = hbBw σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hωσ : ω < σ := omega0_lt_inE hB.1
  obtain ⟨g1, g2⟩ : lgG ρ ∈ TB ρ σ ∧ pi σ ρ (lgG ρ) = lgG σ := Go.goGl.ba_pi σ ρ hB
  have h := glA_pi hB (mem_TB_of_lt hB hωσ) (hc_om_T hB.2.1 hρ1).2 g1 (lgG_facts hB.2.1 hρ1).2.2.1
  rw [pi_lt hB hωσ, g2, (hc_glA_GW hB.2.1 hρ1).1, (hc_glA_GW hB.1 hσ1).1] at h
  exact h

theorem hcWG_R_ext (k : ℕ) (c x : Ordinal.{0}) (hc : c < (hbTG k).1.B) :
    (hbTG (k + 1)).1.R c x = (hbTG k).1.R c x :=
  hbLvTU_R0 (St := fun X U h => (hbRecS (k + 1) X U h).1) (fun X U h => (hbRecS (k + 1) X U h).2)
    (hbG_next_start k (hbTG k).2) hc x

theorem hcWG_g_ext (k : ℕ) (c : Ordinal.{0}) (hc : c < (hbTG k).1.B) :
    (hbTG (k + 1)).1.g c = (hbTG k).1.g c :=
  hbLvTU_g0 (St := fun X U h => (hbRecS (k + 1) X U h).1) (fun X U h => (hbRecS (k + 1) X U h).2)
    (hbG_next_start k (hbTG k).2) hc

/-- **The chain `Hb.hbTG` as an `ω`-chain**: union bound `φ(ω, G+1)`, union base reading `B_ω(x)`. -/
noncomputable def hcWG : HcCh where
  D := fun k => HcVD.ofHb (hbTG k).1
  B := hbTw
  b := hbBw
  γ0 := fun k => hbTG_γ k
  B_mono := fun k => by
    show (hbTG k).1.B ≤ (hbTG (k + 1)).1.B
    rw [hbTG_B, hbTG_B]; exact (hbN_lt_succ _ _).le
  B_lt := fun k => by show (hbTG k).1.B < hbTw; rw [hbTG_B]; exact hbN_lt_Tw _
  B_cof := fun _ hc => hbTw_codes hc
  R_ext := fun k c x hc => hcWG_R_ext k c x hc
  g_ext := fun k c hc => hcWG_g_ext k c hc
  B_lt1 := hbTw_lt_G1
  B_fix := by have := hbTw_veb 1; rwa [Nat.cast_one] at this
  B_mem := fun S _ _ ha _ => by
    rw [hbTw_eq]
    exact CSet.phi_mem (gr_cst_mem ha _ ω (omega0_lt_gamma 1)) (CSet.succ_mem (gmS_G0_mem S ha))
  b_ge := fun k x hx hx1 => by
    show (hbTG k).1.b x ≤ hbBw x
    rw [hbTG_b hx hx1]; exact hbN_le_Bw _ x
  b_cof := fun x hx hx1 ν hν => by
    obtain ⟨k, hk⟩ := hc_lt_S (Q := lgG x) (by rw [hcS_Bw]; exact hν)
    refine ⟨k, ?_⟩
    show ν < (hbTG k).1.b x
    rw [hbTG_b hx hx1]; exact hk.trans_le (hbN_mono (by omega) _)
  b_fix := fun x _ _ => by have := hbBw_veb 1 x; rwa [Nat.cast_one] at this
  b_gt := fun x hx hx1 => (lgG_facts hx hx1).2.1.trans (by rw [← hcS_Bw]; exact hcS_gt _)
  b_lt := fun x hx hx1 => ((hc_Bw_lt_B1 hx hx1).trans (hc_B1_lt_BW hx hx1)).trans (hc_BW_lt_BR hx hx1)
  b_pi := fun _ _ hB => hc_Bw_pi hB

/-- **THE SYSTEM AT `φ(ω, G+1)`**: the union of the chain `Hb.hbTG`. -/
noncomputable def hcWU : HcVD := hcWG.U

theorem hcWU_B : hcWU.B = veblen ω (gcG 0 + 1) := hbTw_eq

theorem hcWU_γ : hcWU.γ = 0 := rfl

theorem hcWU_b (x : Ordinal.{0}) : hcWU.b x = hbBw x := rfl

/-- **`hcWU` extends every `Hb.hbTG k`** (readings and gates). -/
theorem hcWU_R (k : ℕ) {c : Ordinal.{0}} (hc : c < (hbTG k).1.B) (x : Ordinal.{0}) :
    hcWU.R c x = (hbTG k).1.R c x := hcWG.U_R (k := k) hc x

theorem hcWU_g (k : ℕ) {c : Ordinal.{0}} (hc : c < (hbTG k).1.B) : hcWU.g c = (hbTG k).1.g c :=
  hcWG.U_g (k := k) hc

/-- **`φ(ω, G+1)` IS LOCATED**: `Λ⁺ = ι(Γ(φ(ω, G+1))·ω)`, `P(Γ(φ(ω, G+1))·ω) < L(0)`. -/
theorem hcWU_loc (S : InaccSeq.{0}) :
    ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG hbTw * ω) ∧
      upsilon (xtB1 X) = Pv S (gcG hbTw * ω) ∧ Pv S (gcG hbTw * ω) < Nc.ncL S 0 :=
  hcV_locD hcWU S (by rw [hcWU_γ]; exact Td.tdK_SC.1)

/-- **ENUM-REACH at every range restart below `ι(Γ(φ(ω, G+1))·ω)`** (UNCONDITIONAL). -/
theorem hcWU_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG hbTw * ω)) :
    CdUpper S l ∧ CdLower S l :=
  hcV_locD_enum hcWU S (by rw [hcWU_γ]; exact Td.tdK_SC.1) hr hl

/-- **CapV at every range restart below `ι(Γ(φ(ω, G+1))·ω)`** (UNCONDITIONAL). -/
theorem hcWU_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG hbTw * ω)) :
    CdCapV S l :=
  hcV_locD_capV hcWU S (by rw [hcWU_γ]; exact Td.tdK_SC.1) hr hl

/-- **THE ROAD**: UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ(φ(ω, G+1))·ω)` (CapV also `υ_λ < L(ω)`), (CL), EQ,
TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem hcWU_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG hbTw * ω) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG hbTw * ω) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG hbTw * ω) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  gv_road_of S _ (fun _ hr h => hcWU_enum S hr h) (fun _ hr h => hcWU_capV S hr h) hU hL hV hC hEQ hrest hB2

/-- **`ι(Γ(φ(ω, G+1))) ≤ ι(Γ(φ(ω, G+1))·ω)`, and `P(Γ(φ(ω, G+1))·ω) < L(0)`.** -/
theorem hcWU_P (S : InaccSeq.{0}) :
    iota S (gcG hbTw) ≤ iota S (gcG hbTw * ω) ∧ Pv S (gcG hbTw * ω) < Nc.ncL S 0 := by
  obtain ⟨-, -, -, -, h⟩ := hcWU_loc S
  exact ⟨iota_mono _ _ (le_mul_of_one_le_right' one_lt_omega0.le), h⟩

end Googology.Trans.PoR.InaccPsi.R2.Hc

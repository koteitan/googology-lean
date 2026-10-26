import Googology.Trans.PoR.InaccPsi.R2.HgVRS

/-!
# HgCh: THE UNION OF AN `ω`-CHAIN OF DIGIT SYSTEMS; THE CODE `φ(ω, G+1)` IS LOCATED

(Textual copy of `Hc.HcCh` for `Hg.HgVD`: bound fields `< Γ_{x+2}` in place of `≤ B_x(x)` (`Hc.hcBR`); the proofs
are unchanged except where the bound enters.  Names: prefix `hg`/`Hg` (from `hc`/`Hc`), `hgd`/`Hgd` (from `hd`/`Hd`),
`hgf`/`Hgf` (from `hf`/`Hf`), `hge`/`Hge` (from `he`/`He`).)

An `ω`-chain (`HgCh`) is a sequence `D k : Hc.HgVD` with base gate `0`, increasing bounds `B_k`, each extending the
previous one (readings and gates), whose bounds are cofinal in an `ε`-fixed point `B` and whose base readings
`b_k(x)` are cofinal in an `ε`-fixed point `b(x) < B_x(x)` with Lemma EXACT.  Its union (`HgCh.U`) is again an
`HgVD`: bound `B`, base gate `0`, base reading `b(x)`, bound field `evZ(b(x))`; every field below `B` comes from the
first member containing the code.

The chain `Hb.hbTG k` (bounds `N_{k+2}(G) = φ(k+3, G+1)`, base readings `N_{k+2}(Γ_{x+1})`) is an `ω`-chain with
`B = φ(ω, G+1)` and `b(x) = B_ω(x)` (`hgWG`): its union `hgWU` reads every code of the chain as the chain does, so
**the wall `Hb.hb_wall_Tw` is passed** (it was a wall only for the bound field `Z(x) ≤ B_ω(x)`), and the code
`φ(ω, G+1)` itself is located: `Λ⁺ = ι(Γ(φ(ω, G+1))·ω)`, `P(Γ(φ(ω, G+1))·ω) < L(0)` (`hgWU_loc`).

* `HgCh`, `HgCh.R_coh`, `HgCh.g_coh`, `HgCh.N`, `HgCh.R_eq`, `HgCh.g_eq`, `HgCh.U` (**THE UNION OF AN `ω`-CHAIN**),
  `HgCh.U_R`, `HgCh.U_g`, `HgCh.U_B`, `HgCh.U_b`;
* `hg_Bw_pi` (**Lemma EXACT for `B_ω(ρ) = ϑᵖ(Ω₁·ω + Γ_{ρ+1})`**), `hgWG` (the chain `Hb.hbTG` as an `ω`-chain),
  `hgWU`, `hgWU_R`, `hgWU_g`, `hgWU_B` (**THE SYSTEM AT `φ(ω, G+1)`**), `hgWU_loc` (**`φ(ω, G+1)` IS LOCATED**),
  `hgWU_enum`, `hgWU_capV`, `hgWU_road`, `hgWU_P`.

No new axiom.  New definitions: `HgCh`, `HgCh.N`, `HgCh.R`, `HgCh.g`, `HgCh.U`, `hgWG`, `hgWU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hg

open Googology.Trans.PoR.InaccPsi.R2.Hc

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
structure HgCh where
  D : ℕ → HgVD
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
  b_lt : ∀ x, InE x → x < Om1 → b x < gq 1 x
  b_pi : ∀ σ ρ, Bases σ ρ → b ρ ∈ TB ρ σ ∧ pi σ ρ (b ρ) = b σ

namespace HgCh

variable (C : HgCh)

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
  unfold HgCh.N; rw [this, Nat.sInf_empty]

theorem R_succ' (c x : Ordinal.{0}) : C.R (c + 1) x = C.R c x + 1 := by
  rcases lt_or_ge c C.B with hc | hc
  · obtain ⟨k, hk⟩ := C.B_cof _ (C.B_lim.add_one_lt hc)
    rw [C.R_eq hk, C.R_eq ((lt_add_one c).trans hk)]; exact (C.D k).R_succ c x
  · unfold HgCh.R; rw [C.N_high hc, C.N_high (hc.trans le_self_add)]; exact (C.D 0).R_succ c x

theorem g_le_succ' (c : Ordinal.{0}) : C.g c ≤ C.g (c + 1) := by
  rcases lt_or_ge c C.B with hc | hc
  · obtain ⟨k, hk⟩ := C.B_cof _ (C.B_lim.add_one_lt hc)
    rw [C.g_eq hk, C.g_eq ((lt_add_one c).trans hk)]; exact (C.D k).g_le_succ c
  · unfold HgCh.g; rw [C.N_high hc, C.N_high (hc.trans le_self_add)]; exact (C.D 0).g_le_succ c

theorem γ_lt {k : ℕ} {x : Ordinal.{0}} (hx : InE x) : (C.D k).γ < x := by rw [C.γ0 k]; exact hx.pos

theorem b_E {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : InE (C.b x) := hc_fix_E (C.b_fix x hx hx1)

theorem b_lt1 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : C.b x < gq 1 x :=
  C.b_lt x hx hx1

theorem evZ_b_lt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : evZ (C.b x) < gq 1 x :=
  gw_evZ_lt1 hx hx1 (C.b_lt x hx hx1)

/-- **THE UNION OF AN `ω`-CHAIN**: bound `B`, base gate `0`, base reading `b(x)`, bound field `evZ(b(x))`. -/
noncomputable def U : HgVD where
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
  Z_G1 := fun x hx hx1 => C.evZ_b_lt hx hx1
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

end HgCh

end Googology.Trans.PoR.InaccPsi.R2.Hg

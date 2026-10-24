import Googology.Trans.PoR.InaccPsi.R2.GoGl

/-!
# THE LIMIT OF A CHAIN OF DIGIT SYSTEMS

A chain `C : GoCh` is a sequence of digit systems `C.D n` (`R2.GoD`) with increasing bounds, each extending the
previous one (same readings and gates below the old bound), together with the base data of the union: the bound
`φ(1, ixω) = sup_n B_n` and a base reading `bω` with `b_n(x) ≤ bω(x)` cofinal (`bω(x) = sup_n b_n(x)`), Lemma EXACT
and the bounds of a digit system.  The union `C.lim : GoD` reads a code `c < φ(1, ixω)` by the first system that
contains it; every field of a digit system passes to the union, the cofinal codes are the bounds `B_n` themselves.
So the step `GoD.step` (`R2.GoStep`) can be continued past every `ω`-limit of bases.

* `go_glA_sup` (**`ϑˣ(Ω₁ + T) = φ(1, F)`** when `T = sup_n s_n`, `F = sup_n f_n` and `ϑˣ(Ω₁ + s_n) = φ(1, f_n)`,
  [W07a] through `Gl.glA_min`), `go_lt_add_omega`;
* `GoCh`, `GoCh.N`, `GoCh.coh_R'`, `GoCh.coh_g'`, `GoCh.R_eq`, `GoCh.g_eq`, `GoCh.lim` (**THE UNION**),
  `GoCh.lim_R`, `GoCh.lim_g` (**the union extends every member of the chain**), `GoCh.lim_B`.

No new axiom.  New definitions: `GoCh`, `GoCh.N`, `GoCh.lim`.

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
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

/-- `σ < a + ω ⇒ σ < a + n` for some `n`. -/
theorem go_lt_add_omega {a σ : Ordinal.{0}} (h : σ < a + ω) : ∃ n : ℕ, σ < a + n := by
  rcases lt_or_ge σ a with hσ | hσ
  · exact ⟨0, by rw [Nat.cast_zero, add_zero]; exact hσ⟩
  · have e : a + (σ - a) = σ := Ordinal.add_sub_cancel_of_le hσ
    have h2 : σ - a < ω := by rw [← e] at h; exact (add_lt_add_iff_left a).1 h
    obtain ⟨n, hn⟩ := lt_omega0.1 h2
    refine ⟨n + 1, ?_⟩
    rw [← e, Nat.cast_succ, hn]
    exact (add_lt_add_iff_left a).2 (lt_add_one _)

/-- **`ϑˣ(Ω₁ + T) = φ(1, F)` at a limit** (`T = sup_n s_n`, `F = sup_n f_n`, `ϑˣ(Ω₁ + s_n) = φ(1, f_n)`). -/
theorem go_glA_sup {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {s f : ℕ → Ordinal.{0}} {T F : Ordinal.{0}}
    (hT : T < gq 1 x) (hsT : ∀ n, s n < T) (hTs : ∀ σ, σ < T → ∃ n, σ < s n) (hfF : ∀ n, f n < F)
    (hFf : ∀ σ, σ < F → ∃ n, σ < f n) (hF : IsSuccLimit F) (hTu : T < veblen 1 F)
    (hval : ∀ n, glA 1 (s n) x = veblen 1 (f n)) : glA 1 T x = veblen 1 F := by
  obtain ⟨hTT, hT1⟩ := gm1_T hx hx1 hT
  obtain ⟨h1T, h11⟩ := gl_one_T hx hx1
  have hsTT : ∀ σ, σ < T → σ ∈ Tset x := fun σ hσ => (gm1_T hx hx1 (hσ.trans hT)).1
  refine le_antisymm ?_ ?_
  · have hxu : x < veblen 1 F := by
      have h0 := (glA_facts hx hx1 le_rfl h1T h11 (hsTT _ (hsT 0)) ((hsT 0).trans hT1)).2.1
      rw [hval 0] at h0
      exact h0.trans ((isNormal_veblen 1).strictMono (hfF 0))
    have h1u : (1 : Ordinal.{0}) < veblen 1 F :=
      one_lt_omega0.trans (omega0_lt_inE (omega0_opow_epsilon F))
    refine glA_min hx hx1 le_rfl h1T h11 hTT hT1 (luP_veblen 1 F) hxu hTu h1u fun σ hσ => ?_
    obtain ⟨n, hn⟩ := hTs σ hσ
    have h2 := glA_lt_of hx hx1 le_rfl h1T h11 (hsTT σ hσ) (hsTT _ (hsT n)) ((hsT n).trans hT1) hn
    rw [hval n] at h2
    exact h2.trans ((isNormal_veblen 1).strictMono (hfF n))
  · refine ((isNormal_veblen 1).le_iff_forall_le hF).2 fun σ hσ => ?_
    obtain ⟨n, hn⟩ := hFf σ hσ
    have h2 := glA_lt_of hx hx1 le_rfl h1T h11 (hsTT _ (hsT n)) hTT hT1 (hsT n)
    rw [hval n] at h2
    exact (((isNormal_veblen 1).strictMono hn).trans h2).le

/-- **A chain of digit systems** with the base data of its union. -/
structure GoCh where
  D : ℕ → GoD
  ixω : Ordinal.{0}
  bω : Ordinal.{0} → Ordinal.{0}
  baω : Ordinal.{0} → Ordinal.{0}
  coh_R : ∀ n c x, c < (D n).B → (D (n + 1)).R c x = (D n).R c x
  coh_g : ∀ n c, c < (D n).B → (D (n + 1)).g c = (D n).g c
  B_mono : ∀ n, (D n).B < (D (n + 1)).B
  B_lt : ∀ n, (D n).B < veblen 1 ixω
  B_cof : ∀ c, c < veblen 1 ixω → ∃ n, c < (D n).B
  ix_mem : ∀ (S : InaccSeq.{0}) (a b : Ordinal.{0}), 0 < a → ixω ∈ S.CSet a b
  ix_lt : ixω < gcG 1
  cf_g : ∀ n, (D (n + 1)).g (D n).B < ε₀
  b_le : ∀ n x, InE x → x < Om1 → (D n).b x ≤ bω x
  b_sup : ∀ x, InE x → x < Om1 → ∀ ν, ν < bω x → ∃ n, ν < (D n).b x
  b_E : ∀ x, InE x → x < Om1 → InE (bω x)
  b_eN : ∀ x, InE x → x < Om1 → eN (bω x) = glA 1 (baω x) x
  ba_lt : ∀ x, InE x → x < Om1 → baω x < gq 1 x
  b_Z : ∀ x, InE x → x < Om1 → eN (bω x) < evZ (lgG x)
  b_pi : ∀ σ ρ, Bases σ ρ → bω ρ ∈ TB ρ σ ∧ pi σ ρ (bω ρ) = bω σ
  ba_pi : ∀ σ ρ, Bases σ ρ → baω ρ ∈ TB ρ σ ∧ pi σ ρ (baω ρ) = baω σ

namespace GoCh

variable (C : GoCh)

theorem B_mono' {n m : ℕ} (h : n ≤ m) : (C.D n).B ≤ (C.D m).B := by
  induction m, h using Nat.le_induction with
  | base => exact le_rfl
  | succ m _ ih => exact ih.trans (C.B_mono m).le

/-- **Coherence**: a later system keeps the readings of an earlier one. -/
theorem coh_R' {n m : ℕ} (h : n ≤ m) {c : Ordinal.{0}} (hc : c < (C.D n).B) (x : Ordinal.{0}) :
    (C.D m).R c x = (C.D n).R c x := by
  induction m, h using Nat.le_induction with
  | base => rfl
  | succ m hnm ih => rw [C.coh_R m c x (hc.trans_le (C.B_mono' hnm)), ih]

theorem coh_g' {n m : ℕ} (h : n ≤ m) {c : Ordinal.{0}} (hc : c < (C.D n).B) : (C.D m).g c = (C.D n).g c := by
  induction m, h using Nat.le_induction with
  | base => rfl
  | succ m hnm ih => rw [C.coh_g m c (hc.trans_le (C.B_mono' hnm)), ih]

open Classical in
/-- The first system containing `c` (`0` above the union). -/
noncomputable def N (c : Ordinal.{0}) : ℕ := if h : ∃ n, c < (C.D n).B then Nat.find h else 0

theorem N_spec {c : Ordinal.{0}} {n : ℕ} (hc : c < (C.D n).B) : C.N c ≤ n ∧ c < (C.D (C.N c)).B := by
  classical
  have h : ∃ n, c < (C.D n).B := ⟨n, hc⟩
  unfold GoCh.N
  rw [dif_pos h]
  exact ⟨Nat.find_min' h hc, Nat.find_spec h⟩

theorem N_high {c : Ordinal.{0}} (hc : veblen 1 C.ixω ≤ c) : C.N c = 0 := by
  classical
  unfold GoCh.N
  rw [dif_neg]
  rintro ⟨n, hn⟩
  exact absurd (hn.trans (C.B_lt n)) (not_lt.2 hc)

/-- The reading of the union. -/
noncomputable def R (c x : Ordinal.{0}) : Ordinal.{0} := (C.D (C.N c)).R c x

/-- The gate of the union. -/
noncomputable def g (c : Ordinal.{0}) : Ordinal.{0} := (C.D (C.N c)).g c

theorem R_eq {c : Ordinal.{0}} {n : ℕ} (hc : c < (C.D n).B) (x : Ordinal.{0}) : C.R c x = (C.D n).R c x := by
  obtain ⟨h1, h2⟩ := C.N_spec hc
  exact (C.coh_R' h1 h2 x).symm

theorem g_eq {c : Ordinal.{0}} {n : ℕ} (hc : c < (C.D n).B) : C.g c = (C.D n).g c := by
  obtain ⟨h1, h2⟩ := C.N_spec hc
  exact (C.coh_g' h1 h2).symm

theorem B_lim' : IsSuccLimit (veblen 1 C.ixω) := ev_isSuccLimit_of_inE (omega0_opow_epsilon C.ixω)

theorem R_succ' (c x : Ordinal.{0}) : C.R (c + 1) x = C.R c x + 1 := by
  rcases lt_or_ge c (veblen 1 C.ixω) with h | h
  · obtain ⟨n, hn⟩ := C.B_cof _ (C.B_lim'.add_one_lt h)
    rw [C.R_eq hn, C.R_eq ((lt_add_one c).trans hn), (C.D n).R_succ]
  · unfold GoCh.R
    rw [C.N_high h, C.N_high (h.trans (le_self_add (a := c) (b := 1))), (C.D 0).R_succ]

theorem g_le_succ' (c : Ordinal.{0}) : C.g c ≤ C.g (c + 1) := by
  rcases lt_or_ge c (veblen 1 C.ixω) with h | h
  · obtain ⟨n, hn⟩ := C.B_cof _ (C.B_lim'.add_one_lt h)
    rw [C.g_eq hn, C.g_eq ((lt_add_one c).trans hn)]; exact (C.D n).g_le_succ c
  · unfold GoCh.g
    rw [C.N_high h, C.N_high (h.trans (le_self_add (a := c) (b := 1)))]; exact (C.D 0).g_le_succ c

theorem B0_lt : (C.D 0).B < veblen 1 C.ixω := C.B_lt 0

/-- **THE UNION OF A CHAIN OF DIGIT SYSTEMS** (a digit system at the base `φ(1, ixω)`). -/
noncomputable def lim : GoD where
  B := veblen 1 C.ixω
  R := C.R
  g := C.g
  b := C.bω
  ba := C.baω
  ix := C.ixω
  B_E := omega0_opow_epsilon C.ixω
  G_le := (C.D 0).G_le.trans C.B0_lt.le
  B_lt1 := (gcG_SC 1).2 1 (one_lt_omega0.trans (omega0_lt_inE (Low.opow_eq_self_of_SC (gcG_SC 1)))) _ C.ix_lt
  B_ix := rfl
  ix_mem := C.ix_mem
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
    obtain ⟨n, hn⟩ := C.B_cof _ hcB
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
    obtain ⟨n, hn⟩ := C.B_cof _ hc
    rw [C.g_eq hn] at hg
    exact (C.D n).mem S a b ha c hn hg
  R_zero := fun x => by rw [C.R_eq (C.D 0).B_pos]; exact (C.D 0).R_zero x
  R_nat := fun k x => by rw [C.R_eq ((C.D 0).nat_lt_B k)]; exact (C.D 0).R_nat k x
  R_E := fun x => by rw [C.R_eq (C.D 0).E_lt_B]; exact (C.D 0).R_E x
  R_succ := C.R_succ'
  R_pos := fun x hx hx1 c hc0 hc hg => by
    obtain ⟨n, hn⟩ := C.B_cof _ hc
    rw [C.R_eq hn]; rw [C.g_eq hn] at hg
    exact (C.D n).R_pos x hx hx1 c hc0 hn hg
  R_omega := fun x hx hx1 c hω hc hg => by
    obtain ⟨n, hn⟩ := C.B_cof _ hc
    rw [C.R_eq hn]; rw [C.g_eq hn] at hg
    exact (C.D n).R_omega x hx hx1 c hω hn hg
  R_lt_b := fun x hx hx1 c hc hg => by
    obtain ⟨n, hn⟩ := C.B_cof _ hc
    rw [C.R_eq hn]; rw [C.g_eq hn] at hg
    exact ((C.D n).R_lt_b x hx hx1 c hn hg).trans_le (C.b_le n x hx hx1)
  mono := fun x hx hx1 c hc d hdc hgc hgd => by
    obtain ⟨n, hn⟩ := C.B_cof _ hc
    have hd : d < (C.D n).B := hdc.trans hn
    rw [C.R_eq hn, C.R_eq hd]; rw [C.g_eq hn] at hgc; rw [C.g_eq hd] at hgd
    exact (C.D n).mono x hx hx1 c hn d hdc hgc hgd
  cof := fun x hx hx1 c hc hg ν hν => by
    obtain ⟨n, hn⟩ := C.B_cof _ hc
    rw [C.R_eq hn] at hν; rw [C.g_eq hn] at hg
    obtain ⟨d, hdc, hgd, hνd⟩ := (C.D n).cof x hx hx1 c hn hg ν hν
    have hd : d < (C.D n).B := hdc.trans hn
    exact ⟨d, hdc, by rw [C.g_eq hd]; exact hgd, by rw [C.R_eq hd]; exact hνd⟩
  b_cof := fun x hx hx1 ν hν => by
    obtain ⟨n, hn⟩ := C.b_sup x hx hx1 ν hν
    obtain ⟨d, hd, hgd, hνd⟩ := (C.D n).b_cof x hx hx1 ν hn
    exact ⟨d, hd.trans (C.B_lt n), by rw [C.g_eq hd]; exact hgd, by rw [C.R_eq hd]; exact hνd⟩
  b_E := C.b_E
  x_lt_b := fun x hx hx1 => ((C.D 0).x_lt_b x hx hx1).trans_le (C.b_le 0 x hx hx1)
  b_eN := C.b_eN
  ba_lt := C.ba_lt
  b_Z := C.b_Z
  b_pi := C.b_pi
  ba_pi := C.ba_pi
  ex := fun σ ρ hB c hc hg => by
    obtain ⟨n, hn⟩ := C.B_cof _ hc
    rw [C.R_eq hn, C.R_eq hn]; rw [C.g_eq hn] at hg
    exact (C.D n).ex σ ρ hB c hn hg
  dig := fun σ ρ hB d hd hg P P' hat => by
    obtain ⟨n, hn⟩ := C.B_cof _ hd
    rw [C.R_eq hn, C.R_eq hn]; rw [C.g_eq hn] at hg
    exact (C.D n).dig σ ρ hB d hn hg P P' (fun β hβ hβe =>
      hat β hβ (hβe.trans_le (C.b_le n ρ hB.2.1 hB.2.2.2)))
  ld := fun c hl hc => by
    obtain ⟨n, hn⟩ := C.B_cof _ hc
    obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := (C.D n).ld c hl hn
    have hcpn : cp < (C.D n).B := hcp.trans hn
    refine ⟨cp, lp, T, hcp, by rw [C.g_eq hn, C.g_eq hcpn]; exact hgcp, fun x hx hx1 hg => ?_,
      fun σ ρ hB hg => hex σ ρ hB (by rw [← C.g_eq hn]; exact hg)⟩
    rw [C.g_eq hn] at hg
    rw [C.R_eq hn, C.R_eq hcpn]
    exact hdec x hx hx1 hg
  cf := fun k => (C.D k).B
  cf_ge := fun k => (C.D k).E_lt_B.le
  cf_lt := C.B_lt
  cf_g := fun k => by rw [C.g_eq (C.B_mono k)]; exact C.cf_g k
  cf_mono := C.B_mono
  cf_cof := C.B_cof

theorem lim_B : C.lim.B = veblen 1 C.ixω := rfl

theorem lim_b : C.lim.b = C.bω := rfl

/-- **The union extends every member of the chain** (readings). -/
theorem lim_R {n : ℕ} {c : Ordinal.{0}} (hc : c < (C.D n).B) (x : Ordinal.{0}) : C.lim.R c x = (C.D n).R c x :=
  C.R_eq hc x

/-- **The union extends every member of the chain** (gates). -/
theorem lim_g {n : ℕ} {c : Ordinal.{0}} (hc : c < (C.D n).B) : C.lim.g c = (C.D n).g c := C.g_eq hc

end GoCh

end Googology.Trans.PoR.InaccPsi.R2.Go

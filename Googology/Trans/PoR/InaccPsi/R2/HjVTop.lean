import Googology.Trans.PoR.InaccPsi.R2.HjVRec

/-!
# HjVTop: THE UNION OF ALL OFFSETS OF A BASE OF THE LEVEL `L + ν`: THE TOWER TO `N_{L + ν}(F) = φ(L + ν+1, F+1)`

PORT of `Hi.HiVTop` to a level datum `Λ : Hj.HjLv`: the prefix `Ω₁` of the level `Ω₁ + ν` (read `x + ν`) is replaced
by `Λ.L` (read `Λ.l x`), so every level below is `Λ.L + ν`, read `Λ.l x + ν`.  What differs: the statements carry the
parameter `Λ`; the facts `Ω₁ ≤ L`, `x ≤ ℓ(x) < Γ_{x+1}`, the level gate (`Hj.hjv_cl_gate`) and Lemma EXACT for `ℓ`
come from `Λ`.  With `Λ = Hj.hjL1` it is `Hi.HiVTop` again.

The port of `Hg.HgfMTop` to the level `L + ν` read as `Λ.l x + ν`: for a base `A : Hj.HjVB Λ ν` and a start `S0`,
the union
of all starts `Hj.hjVU St A S0 λ`, `λ < N_{L + ν}(F)`, is a system `hjVTU` with the bound `N_{L + ν}(F)`, base gate
`γN`, base reading `N_{x+ν}(F(x))`, bound field `evZ(N_{x+ν}(F(x)))` above `γN` and `Z_o(x)` below; the tower
`t_0 = 0`, `t_{k+1} = φ(L + ν, F + 1 + t_k)` is cofinal in `N_{L + ν}(F)` and its readings are cofinal in
`N_{x+ν}(F(x))`; a code in `[F, N(F))` with gate below `σ` forces the CODE gate `γ` below `σ` (`hjVT_high`).

* `hjVTt`, `hjVTt_cof`, `hjVTt_gate`, `hjVTr`, `hjVTr_succ`, `hjVTr_cof`; `hjVTN`, `hjVTR`, `hjVTg`, `hjVTZ`,
  `hjVT_small`, `hjVT_high`, `hjVTU` (**THE SYSTEM AT `N_{L + ν}(F)`**), `hjVTU_R0`, `hjVTU_g0`, `hjVTU_high`.

No new axiom.  New definitions: `hjVTt`, `hjVTr`, `hjVTN`, `hjVTR`, `hjVTg`, `hjVTZ`, `hjVTU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hj

open Googology.Trans.PoR.InaccPsi.R2.Hi

open Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

variable {Λ : HjLv}

/-! ## The tower of offsets -/

section Tower

variable {κ : Ordinal.{0}} (A : HjVB Λ κ)

/-- **The tower of offsets**: `t_0 = 0`, `t_{k+1} = φ(2, F + 1 + t_k)`. -/
noncomputable def hjVTt : ℕ → Ordinal.{0}
  | 0 => 0
  | k + 1 => veblen (Λ.L + κ) (A.F + 1 + hjVTt k)

theorem hjVTt_lt : ∀ k : ℕ, hjVTt A k < hcN (Λ.L + κ) A.F
  | 0 => hjV_zero_lt_N A
  | k + 1 => A.Q_lt_N (hjVTt_lt k)

theorem hjVTt_lt_succ (k : ℕ) : hjVTt A k < hjVTt A (k + 1) := A.lt_Q (hjVTt_lt A k)

theorem hjVTt_iter (n : ℕ) : (veblen (Λ.L + κ))^[n] (A.F + 1) ≤ hjVTt A (n + 1) := by
  induction n with
  | zero =>
    show A.F + 1 ≤ veblen (Λ.L + κ) (A.F + 1 + 0)
    rw [add_zero]; exact right_le_veblen (Λ.L + κ) _
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    show veblen (Λ.L + κ) _ ≤ veblen (Λ.L + κ) (A.F + 1 + hjVTt A (n + 1))
    exact (isNormal_veblen (Λ.L + κ)).monotone (ih.trans le_add_self)

theorem hjV_N_nfp : hcN (Λ.L + κ) A.F = nfp (veblen (Λ.L + κ)) (A.F + 1) := rfl

/-- **The tower is cofinal in `N(F)`.** -/
theorem hjVTt_cof {c : Ordinal.{0}} (hc : c < hcN (Λ.L + κ) A.F) : ∃ k : ℕ, c < hjVTt A k := by
  rw [hjV_N_nfp] at hc
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hc
  exact ⟨n + 1, hn.trans_le (hjVTt_iter A n)⟩

variable {St : ∀ (Q : HjVQ Λ κ) (U : HgVD), HgSStart (hjVPB Q) U → HgVD} {S0 : HgVD}
  (hSt : ∀ Q U h, HjVSpec Q U (St Q U h)) (hS : HjVStart A S0)
include hSt hS

theorem hjVTt_B (k : ℕ) : (hjVU St A S0 (hjVTt A k)).B = hjVTt A (k + 1) := hjVU_B hSt hS (hjVTt_lt A k)

/-- **Every start `hjVU St A S0 t_k` has base gate below every base above `γN`.** -/
theorem hjVTt_gate : ∀ (k : ℕ) (x : Ordinal.{0}), InE x → x < Om1 → A.γN < x → (hjVU St A S0 (hjVTt A k)).γ < x
  | 0, x, hx, hx1, hA => by
    show (hjVU St A S0 0).γ < x
    rw [hjVU_γ_iff hSt hS (hjV_zero_lt_N A) hx hx1, (hjVU St A S0 0).g_zero, max_eq_left zero_le]; exact hA
  | k + 1, x, hx, hx1, hA => by
    set l := hjVTt A k with hl
    have hlT : l < hcN (Λ.L + κ) A.F := hjVTt_lt A k
    have hl'T : hjVTt A (k + 1) < hcN (Λ.L + κ) A.F := hjVTt_lt A (k + 1)
    have hsp := hjVU_succ_spec hSt hS hlT
    have hl1 : l + 1 ≤ hjVTt A (k + 1) := Order.add_one_le_of_lt (hjVTt_lt_succ A k)
    have hl1T : l + 1 < hcN (Λ.L + κ) A.F := hl1.trans_lt hl'T
    have hB : hjVTt A (k + 1) = (hjVU St A S0 l).B := (hjVTt_B A hSt hS k).symm
    have hcB : hjVTt A (k + 1) < (hjVU St A S0 (l + 1)).B := by
      rw [hjVU_B hSt hS hl1T, hB, hjVU_B hSt hS hlT]; exact A.Q_lt_Q (lt_add_one l)
    rw [hjVU_γ_iff hSt hS hl'T hx hx1, (hjV_ext hSt hS hl1 hl'T).2 _ hcB, hB, hjVU_B hSt hS hlT]
    refine max_lt hA ((hsp.gF x hx hx1).2 ?_)
    exact max_lt hA ((max_lt_iff.1 ((hjVU_γ_iff hSt hS hlT hx hx1).1 (hjVTt_gate k x hx hx1 hA))).2)

end Tower

/-- The reading of the tower code `t_k` (in its start). -/
noncomputable def hjVTr {κ : Ordinal.{0}} (St : ∀ (Q : HjVQ Λ κ) (U : HgVD), HgSStart (hjVPB Q) U → HgVD) (A : HjVB Λ κ)
    (S0 : HgVD) (k : ℕ)
    (x : Ordinal.{0}) : Ordinal.{0} := (hjVU St A S0 (hjVTt A k)).R (hjVTt A k) x

section TowerRead

variable {κ : Ordinal.{0}} {St : ∀ (Q : HjVQ Λ κ) (U : HgVD), HgSStart (hjVPB Q) U → HgVD}
  (hSt : ∀ Q U h, HjVSpec Q U (St Q U h))
  {A : HjVB Λ κ} {S0 : HgVD} (hS : HjVStart A S0) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hA : A.γN < x)
include hSt hS hx hx1 hA

theorem hjVTt_g (k : ℕ) : (hjVU St A S0 (hjVTt A k)).g (hjVTt A k) < x :=
  (max_lt_iff.1 ((hjVU_γ_iff hSt hS (hjVTt_lt A k) hx hx1).1 (hjVTt_gate A hSt hS k x hx hx1 hA))).2

/-- **`r_{k+1}(x) = ϑˣ(Ω₁·2 + F(x) + r_k(x))`**: the code `t_{k+1} = Q_{t_k}` is read as the base reading of the start
`t_k`. -/
theorem hjVTr_succ (k : ℕ) :
    hjVTr St A S0 (k + 1) x = glA (Λ.l x + κ) (A.Fr x + hjVTr St A S0 k x) x := by
  set l := hjVTt A k with hl
  have hlT : l < hcN (Λ.L + κ) A.F := hjVTt_lt A k
  have hl'T : hjVTt A (k + 1) < hcN (Λ.L + κ) A.F := hjVTt_lt A (k + 1)
  have hsp := hjVU_succ_spec hSt hS hlT
  have hl1 : l + 1 ≤ hjVTt A (k + 1) := Order.add_one_le_of_lt (hjVTt_lt_succ A k)
  have hl1T : l + 1 < hcN (Λ.L + κ) A.F := hl1.trans_lt hl'T
  have hB : hjVTt A (k + 1) = (hjVU St A S0 l).B := (hjVTt_B A hSt hS k).symm
  have hcB : hjVTt A (k + 1) < (hjVU St A S0 (l + 1)).B := by
    rw [hjVU_B hSt hS hl1T, hB, hjVU_B hSt hS hlT]; exact A.Q_lt_Q (lt_add_one l)
  have hg : max A.γN ((hjVU St A S0 l).g l) < x := max_lt hA (hjVTt_g hSt hS hx hx1 hA k)
  unfold hjVTr
  rw [(hjV_ext hSt hS hl1 hl'T).1 _ x hcB, hB, hjVU_B hSt hS hlT]
  exact hsp.RF x hx hx1 hg

theorem hjVTr_zero : hjVTr St A S0 0 x = 0 := by unfold hjVTr; exact (hjVU St A S0 (hjVTt A 0)).R_zero x

theorem hjVTr_lt_N (k : ℕ) : hjVTr St A S0 k x < hcN (Λ.l x + κ) (A.Fr x) :=
  A.lvR_lt_N _ (hjVU_Zb hSt hS (hjVTt_lt A k)) (hjVU_self hSt hS (hjVTt_lt A k)) hx hx1 hA
    (hjVTt_g hSt hS hx hx1 hA k)

/-- **The iterates of `φ((Λ.L + κ), ·)` from `hdNx (Λ.L + κ) (F(x)) + 1` lie below the tower readings.** -/
theorem hjVTr_iter (n : ℕ) :
    (veblen (Λ.l x + κ))^[n] (hdNx (Λ.l x + κ) (A.Fr x) + 1) ≤ hjVTr St A S0 (n + 2) x := by
  obtain ⟨i0, hi0⟩ := hdNx_LuP (Λ.l x + κ) (A.Fr x)
  have hstep : ∀ k : ℕ, hjVTr St A S0 (k + 1) x = veblen (Λ.l x + κ)
      (i0 + hjVTr St A S0 k x) := fun k => by
    rw [hjVTr_succ hSt hS hx hx1 hA k, A.lvglAV hx hx1 hA hi0 (hjVTr_lt_N hSt hS hx hx1 hA k)]
  have h1 : hjVTr St A S0 1 x = hdNx (Λ.l x + κ) (A.Fr x) := by
    rw [hstep 0, hjVTr_zero hSt hS hx hx1 hA, add_zero, hi0]
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply]
    refine Order.add_one_le_of_lt ?_
    rw [hstep 1, h1]
    refine (le_add_self : hdNx (Λ.l x + κ) (A.Fr x) ≤ i0 + hdNx (Λ.l x + κ) (A.Fr x)).trans_lt ?_
    have h2 := hjVTr_lt_N hSt hS hx hx1 hA 2
    rw [hstep 1, h1] at h2
    exact hc_nofixG (by rw [hi0]; exact hdNx_gt _ _) le_self_add h2
  | succ n ih =>
    rw [Function.iterate_succ_apply', hstep (n + 2)]
    exact (isNormal_veblen (Λ.l x + κ)).monotone (ih.trans le_add_self)

/-- **The tower readings are cofinal in `N_α(F(x))`.** -/
theorem hjVTr_cof {v : Ordinal.{0}} (hv : v < hcN (Λ.l x + κ) (A.Fr x)) : ∃ k : ℕ, v < hjVTr St A S0 k x := by
  have e : hcN (Λ.l x + κ) (A.Fr x) = nfp (veblen (Λ.l x + κ)) (hdNx (Λ.l x + κ) (A.Fr x) + 1) := by
    refine le_antisymm ?_ ?_
    · exact hcN_le (nfp_fp (isNormal_veblen _) _)
        ((hdNx_gt (Λ.l x + κ) (A.Fr x)).trans ((lt_add_one _).trans_le (le_nfp _ _)))
    · exact nfp_le_fp (isNormal_veblen (Λ.l x + κ)).strictMono.monotone
        (Order.add_one_le_of_lt (hdNx_lt_N (hcN_gt (Λ.l x + κ) (A.Fr x)))) (hcN_fix (Λ.l x + κ) _).le
  rw [e] at hv
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hv
  exact ⟨n + 2, hn.trans_le (hjVTr_iter hSt hS hx hx1 hA n)⟩

end TowerRead

/-! ## The union of all offsets -/

section Union

variable {κ : Ordinal.{0}} (St : ∀ (Q : HjVQ Λ κ) (U : HgVD), HgSStart (hjVPB Q) U → HgVD) (A : HjVB Λ κ) (S0 : HgVD)

/-- The first start containing `c`. -/
noncomputable def hjVTN (c : Ordinal.{0}) : Ordinal.{0} := sInf {ν | ν < hcN (Λ.L + κ) A.F ∧ c < (hjVU St A S0 ν).B}

/-- The reading of the union. -/
noncomputable def hjVTR (c x : Ordinal.{0}) : Ordinal.{0} := (hjVU St A S0 (hjVTN St A S0 c)).R c x

/-- The gate of the union. -/
noncomputable def hjVTg (c : Ordinal.{0}) : Ordinal.{0} := (hjVU St A S0 (hjVTN St A S0 c)).g c

open Classical in
/-- The bound field of the union: `evZ(N_α(F(x)))` above `γ`, `Z_o(x)` below. -/
noncomputable def hjVTZ (x : Ordinal.{0}) : Ordinal.{0} :=
  if A.γN < x then evZ (hcN (Λ.l x + κ) (A.Fr x)) else A.Zo x

variable {St A S0} (hSt : ∀ Q U h, HjVSpec Q U (St Q U h)) (hS : HjVStart A S0)
include hSt hS

theorem hjVT_cof {c : Ordinal.{0}} (hc : c < hcN (Λ.L + κ) A.F) : ∃ ν, ν < hcN (Λ.L + κ) A.F ∧ c <
    (hjVU St A S0 ν).B := by
  obtain ⟨k, hk⟩ := hjVTt_cof A hc
  exact ⟨hjVTt A k, hjVTt_lt A k, hk.trans (by rw [hjVTt_B A hSt hS k]; exact hjVTt_lt_succ A k)⟩

omit hSt hS in
theorem hjVTN_spec {c ν : Ordinal.{0}} (hν : ν < hcN (Λ.L + κ) A.F) (hc : c < (hjVU St A S0 ν).B) :
    hjVTN St A S0 c ≤ ν ∧ hjVTN St A S0 c < hcN (Λ.L + κ) A.F ∧ c < (hjVU St A S0 (hjVTN St A S0 c)).B := by
  have hne : ({ν | ν < hcN (Λ.L + κ) A.F ∧ c < (hjVU St A S0 ν).B} : Set Ordinal.{0}).Nonempty := ⟨ν, hν, hc⟩
  have hm := csInf_mem hne
  exact ⟨csInf_le' ⟨hν, hc⟩, hm.1, hm.2⟩

omit hSt hS in
theorem hjVTN_min {c μ : Ordinal.{0}} (hμ : μ < hjVTN St A S0 c) (hμl : μ < hcN (Λ.L + κ) A.F) : ¬ c <
    (hjVU St A S0 μ).B :=
  fun hcμ => absurd (csInf_le' ⟨hμl, hcμ⟩ : hjVTN St A S0 c ≤ μ) (not_le.2 hμ)

theorem hjVT_B_lt {ν : Ordinal.{0}} (hν : ν < hcN (Λ.L + κ) A.F) : (hjVU St A S0 ν).B < hcN (Λ.L + κ) A.F := by
  rw [hjVU_B hSt hS hν]; exact A.Q_lt_N hν

theorem hjVTN_high {c : Ordinal.{0}} (hc : hcN (Λ.L + κ) A.F ≤ c) : hjVTN St A S0 c = 0 := by
  unfold hjVTN
  have he : ({ν | ν < hcN (Λ.L + κ) A.F ∧ c < (hjVU St A S0 ν).B} : Set Ordinal.{0}) = ∅ := by
    ext ν
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hν hcν
    exact absurd (hcν.trans (hjVT_B_lt hSt hS hν)) (not_lt.2 hc)
  rw [he]; exact Ordinal.sInf_empty

theorem hjVTR_eq {c ν : Ordinal.{0}} (hν : ν < hcN (Λ.L + κ) A.F) (hc : c < (hjVU St A S0 ν).B) (x : Ordinal.{0}) :
    hjVTR St A S0 c x = (hjVU St A S0 ν).R c x := by
  obtain ⟨h1, -, h3⟩ := hjVTN_spec hν hc
  exact ((hjV_ext hSt hS h1 hν).1 c x h3).symm

theorem hjVTg_eq {c ν : Ordinal.{0}} (hν : ν < hcN (Λ.L + κ) A.F) (hc : c < (hjVU St A S0 ν).B) :
    hjVTg St A S0 c = (hjVU St A S0 ν).g c := by
  obtain ⟨h1, -, h3⟩ := hjVTN_spec hν hc
  exact ((hjV_ext hSt hS h1 hν).2 c h3).symm

theorem hjVTR_succ (c x : Ordinal.{0}) : hjVTR St A S0 (c + 1) x = hjVTR St A S0 c x + 1 := by
  rcases lt_or_ge c (hcN (Λ.L + κ) A.F) with h | h
  · obtain ⟨n, hn1, hn⟩ := hjVT_cof hSt hS (A.N_lim.add_one_lt h)
    rw [hjVTR_eq hSt hS hn1 hn, hjVTR_eq hSt hS hn1 ((lt_add_one c).trans hn), (hjVU St A S0 n).R_succ]
  · unfold hjVTR
    rw [hjVTN_high hSt hS h, hjVTN_high hSt hS (h.trans (le_self_add (a := c) (b := 1))), (hjVU St A S0 0).R_succ]

theorem hjVTg_le_succ (c : Ordinal.{0}) : hjVTg St A S0 c ≤ hjVTg St A S0 (c + 1) := by
  rcases lt_or_ge c (hcN (Λ.L + κ) A.F) with h | h
  · obtain ⟨n, hn1, hn⟩ := hjVT_cof hSt hS (A.N_lim.add_one_lt h)
    rw [hjVTg_eq hSt hS hn1 hn, hjVTg_eq hSt hS hn1 ((lt_add_one c).trans hn)]; exact (hjVU St A S0 n).g_le_succ c
  · unfold hjVTg
    rw [hjVTN_high hSt hS h, hjVTN_high hSt hS (h.trans (le_self_add (a := c) (b := 1)))]; exact
        (hjVU St A S0 0).g_le_succ c

/-- **A code of the union with gate below a base `σ > γ_F` lies in a start with base gate below `σ`.** -/
theorem hjVT_small {c σ : Ordinal.{0}} (hc : c < hcN (Λ.L + κ) A.F) (hσ : InE σ) (hσ1 : σ < Om1) (hAσ : A.γN < σ)
    (hg : hjVTg St A S0 c < σ) : ∃ μ, μ < hcN (Λ.L + κ) A.F ∧ c < (hjVU St A S0 μ).B ∧ (hjVU St A S0 μ).γ < σ := by
  obtain ⟨n, hn1, hn⟩ := hjVT_cof hSt hS hc
  obtain ⟨-, hN1, hcNc⟩ := hjVTN_spec hn1 hn
  have hgN : hjVTg St A S0 c = (hjVU St A S0 (hjVTN St A S0 c)).g c := rfl
  have I := hjV_inv hSt hS _ hN1
  rcases zero_or_succ_or_isSuccLimit (hjVTN St A S0 c) with h0 | ⟨m, hm⟩ | hlim
  · refine ⟨hjVTN St A S0 c, hN1, hcNc, ?_⟩
    rw [h0, hjVU_γ_iff hSt hS (hjV_zero_lt_N A) hσ hσ1, (hjVU St A S0 0).g_zero, max_eq_left zero_le]
    exact hAσ
  · have hm' : hjVTN St A S0 c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < hjVTN St A S0 c := by rw [hm']; exact lt_add_one m
    have hml : m < hcN (Λ.L + κ) A.F := hmN.trans hN1
    have hBc : (hjVU St A S0 m).B ≤ c := not_lt.1 (hjVTN_min hmN hml)
    refine ⟨hjVTN St A S0 c, hN1, hcNc, ?_⟩
    rw [hgN, hm'] at hg
    rw [hm'] at hcNc I ⊢
    exact I.high m (lt_add_one _) c σ hBc hcNc hσ hσ1 hg
  · exfalso
    rw [hjVU_B hSt hS hN1] at hcNc
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen (Λ.L + κ)).lt_iff_exists_lt
        (isSuccLimit_add _ hlim)).1 hcNc
    obtain ⟨d, hf, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    have hfl : d < hcN (Λ.L + κ) A.F := hf.trans hN1
    refine hjVTN_min hf hfl ?_
    rw [hjVU_B hSt hS hfl]; exact hct.trans_le ((isNormal_veblen (Λ.L + κ)).monotone htd)

/-- **A code `c ∈ [F, N(F))` of the union with gate below a base `σ` forces `γ_F < σ`.** -/
theorem hjVT_high {c σ : Ordinal.{0}} (hc : c < hcN (Λ.L + κ) A.F) (hFc : A.F ≤ c) (hσ : InE σ) (hσ1 : σ < Om1)
    (hg : hjVTg St A S0 c < σ) : A.γ < σ := by
  obtain ⟨n, hn1, hn⟩ := hjVT_cof hSt hS hc
  obtain ⟨-, hN1, hcNc⟩ := hjVTN_spec hn1 hn
  have hgN : hjVTg St A S0 c = (hjVU St A S0 (hjVTN St A S0 c)).g c := rfl
  have I := hjV_inv hSt hS _ hN1
  rcases zero_or_succ_or_isSuccLimit (hjVTN St A S0 c) with h0 | ⟨m, hm⟩ | hlim
  · rw [hgN, h0, hjVU_zero] at hg
    rw [h0, hjVU_zero] at hcNc
    exact hS.high0 c σ hFc hcNc hσ hσ1 hg
  · have hm' : hjVTN St A S0 c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < hjVTN St A S0 c := by rw [hm']; exact lt_add_one m
    have hml : m < hcN (Λ.L + κ) A.F := hmN.trans hN1
    have hBc : (hjVU St A S0 m).B ≤ c := not_lt.1 (hjVTN_min hmN hml)
    rw [hgN, hm'] at hg
    rw [hm'] at hcNc I hN1
    have hγ := I.high m (lt_add_one _) c σ hBc hcNc hσ hσ1 hg
    exact A.γ_le.trans_lt (max_lt_iff.1 ((hjVU_γ_iff hSt hS hN1 hσ hσ1).1 hγ)).1
  · exfalso
    rw [hjVU_B hSt hS hN1] at hcNc
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen (Λ.L + κ)).lt_iff_exists_lt
        (isSuccLimit_add _ hlim)).1 hcNc
    obtain ⟨d, hf, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    have hfl : d < hcN (Λ.L + κ) A.F := hf.trans hN1
    refine hjVTN_min hf hfl ?_
    rw [hjVU_B hSt hS hfl]; exact hct.trans_le ((isNormal_veblen (Λ.L + κ)).monotone htd)

/-- **`b_μ(x) < N(F(x))`** for every start with base gate below `x`. -/
theorem hjVT_b_lt {μ x : Ordinal.{0}} (hμ : μ < hcN (Λ.L + κ) A.F) (hx : InE x) (hx1 : x < Om1) (hγ :
    (hjVU St A S0 μ).γ < x) :
    (hjVU St A S0 μ).b x < hcN (Λ.l x + κ) (A.Fr x) := by
  have hg : max A.γN ((hjVU St A S0 μ).g μ) < x := (hjVU_γ_iff hSt hS hμ hx hx1).1 hγ
  have hA : A.γN < x := (max_lt_iff.1 hg).1
  rw [(hjVU_start hSt hS hμ).b x hx hx1 hg]
  exact A.glA_lt_N hx hx1 hA (A.lvR_lt_N _ (hjVU_Zb hSt hS hμ) (hjVU_self hSt hS hμ) hx hx1 hA (max_lt_iff.1 hg).2)

omit hSt hS in
theorem hjVTZ_fix (x : Ordinal.{0}) : veblen 1 (hjVTZ A x) = hjVTZ A x := by
  unfold hjVTZ; split_ifs
  · exact epsilon_evZ _
  · exact ha_fix1_of_fix2 (A.Zo_fix x)

omit hSt hS in
theorem hjVTZ_G1 (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : hjVTZ A x < gq 1 x := by
  unfold hjVTZ; split_ifs with h
  · exact (hb_evZ_lt_fix2 (A.Zo_fix x) (A.N_Zo hx hx1 h)).trans (A.Zo_G1 x hx hx1)
  · exact A.Zo_G1 x hx hx1

omit hSt hS in
theorem hjVTZ_ge (x : Ordinal.{0}) (hx : InE x) : A.Zl x ≤ hjVTZ A x := by
  by_cases h : A.γN < x
  · rw [A.Zl_eq hx h]; unfold hjVTZ; rw [if_pos h]; exact (lt_evZ _).le
  · rw [A.Zl_low h]; unfold hjVTZ; rw [if_neg h]

/-- **THE SYSTEM AT `N(F)`**: the union of all starts `hjVU St A S0 λ`, `λ < N(F)`: bound `N(F)`, base gate `γN`, base
reading `N(F(x))`, bound field `hjVTZ`. -/
noncomputable def hjVTU : HgVD where
  B := hcN (Λ.L + κ) A.F
  γ := A.γN
  γ_lt := A.γN_lt
  γ_cl := fun Z hZ hZ1 h => A.N_cl Z hZ hZ1 h
  γ_G := fun h => absurd h (A.G_le.trans_lt A.F_lt_N).ne'
  R := hjVTR St A S0
  g := hjVTg St A S0
  b := fun x => hcN (Λ.l x + κ) (A.Fr x)
  ba := fun x => hcN (Λ.l x + κ) (A.Fr x)
  ix := hcN (Λ.L + κ) A.F
  Z := hjVTZ A
  B_E := A.N_E
  G_le := (A.G_le.trans_lt A.F_lt_N).le
  B_lt1 := A.N_lt1
  B_ix := (hc_fix_down (hjv_L1 Λ κ) (hcN_fix (Λ.L + κ) A.F)).symm
  Z_fix := fun x _ _ => hjVTZ_fix x
  Z_G1 := hjVTZ_G1
  ix_mem := fun S _ _ ha hb => A.N_mem S ha hb
  g_lt := fun c hc => by
    obtain ⟨n, hn1, hn⟩ := hjVT_cof hSt hS hc
    rw [hjVTg_eq hSt hS hn1 hn]; exact (hjVU St A S0 n).g_lt c hn
  g_zero := by
    rw [hjVTg_eq hSt hS (hjV_zero_lt_N A) (hjVU St A S0 0).B_pos]; exact (hjVU St A S0 0).g_zero
  g_nat := fun k => by
    rw [hjVTg_eq hSt hS (hjV_zero_lt_N A) ((hjVU St A S0 0).nat_lt_B k)]; exact (hjVU St A S0 0).g_nat k
  g_E := by rw [hjVTg_eq hSt hS (hjV_zero_lt_N A) (hjVU St A S0 0).E_lt_B]; exact (hjVU St A S0 0).g_E
  g_lowE := fun c hc => by
    rw [hjVTg_eq hSt hS (hjV_zero_lt_N A) (hc.trans (hjVU St A S0 0).E_lt_B)]; exact (hjVU St A S0 0).g_lowE c hc
  g_G0 := fun h => by
    obtain ⟨n, hn1, hn⟩ := hjVT_cof hSt hS h
    rw [hjVTg_eq hSt hS hn1 hn]; exact (hjVU St A S0 n).g_G0 hn
  g_add := fun Z hZ hωZ x y hxy hgx hgy => by
    obtain ⟨n, hn1, hn⟩ := hjVT_cof hSt hS hxy
    have hx : x < (hjVU St A S0 n).B := lt_of_le_of_lt le_self_add hn
    have hy : y < (hjVU St A S0 n).B := lt_of_le_of_lt le_add_self hn
    rw [hjVTg_eq hSt hS hn1 hn]; rw [hjVTg_eq hSt hS hn1 hx] at hgx; rw [hjVTg_eq hSt hS hn1 hy] at hgy
    exact (hjVU St A S0 n).g_add Z hZ hωZ x y hn hgx hgy
  g_opow := fun Z hZw hωZ y hy hg => by
    obtain ⟨n, hn1, hn⟩ := hjVT_cof hSt hS hy
    have hy' : y < (hjVU St A S0 n).B := lt_of_le_of_lt (right_le_opow y one_lt_omega0) hn
    rw [hjVTg_eq hSt hS hn1 hn]; rw [hjVTg_eq hSt hS hn1 hy'] at hg
    exact (hjVU St A S0 n).g_opow Z hZw hωZ y hn hg
  code_gate := fun Z hZ1 hZ0 hZa hZp At hAt c hc hcB => by
    obtain ⟨n, hn1, hn⟩ := hjVT_cof hSt hS hcB
    rw [hjVTg_eq hSt hS hn1 hn]
    exact (hjVU St A S0 n).code_gate Z hZ1 hZ0 hZa hZp At (fun s hs => (hAt s hs).imp_right
      (fun h => (hjVT_B_lt hSt hS hn1).le.trans h)) c hc hn
  g_succ := fun Z hZ c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hjVT_cof hSt hS hc
    have hc' : c < (hjVU St A S0 n).B := (lt_add_one c).trans hn
    rw [hjVTg_eq hSt hS hn1 hn]; rw [hjVTg_eq hSt hS hn1 hc'] at hg
    exact (hjVU St A S0 n).g_succ Z hZ c hn hg
  g_le_succ := hjVTg_le_succ hSt hS
  mem := fun S a b ha c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hjVT_cof hSt hS hc
    rw [hjVTg_eq hSt hS hn1 hn] at hg
    exact (hjVU St A S0 n).mem S a b ha c hn hg
  R_zero := fun x => by
    rw [hjVTR_eq hSt hS (hjV_zero_lt_N A) (hjVU St A S0 0).B_pos]; exact (hjVU St A S0 0).R_zero x
  R_nat := fun k x => by
    rw [hjVTR_eq hSt hS (hjV_zero_lt_N A) ((hjVU St A S0 0).nat_lt_B k)]; exact (hjVU St A S0 0).R_nat k x
  R_E := fun x => by rw [hjVTR_eq hSt hS (hjV_zero_lt_N A) (hjVU St A S0 0).E_lt_B]; exact (hjVU St A S0 0).R_E x
  R_succ := hjVTR_succ hSt hS
  R_pos := fun x hx hx1 c hc0 hc hg => by
    obtain ⟨n, hn1, hn⟩ := hjVT_cof hSt hS hc
    rw [hjVTR_eq hSt hS hn1 hn]; rw [hjVTg_eq hSt hS hn1 hn] at hg
    exact (hjVU St A S0 n).R_pos x hx hx1 c hc0 hn hg
  R_omega := fun x hx hx1 c hω hc hg => by
    obtain ⟨n, hn1, hn⟩ := hjVT_cof hSt hS hc
    rw [hjVTR_eq hSt hS hn1 hn]; rw [hjVTg_eq hSt hS hn1 hn] at hg
    exact (hjVU St A S0 n).R_omega x hx hx1 c hω hn hg
  R_lt_b := fun x hx hx1 hγx c hc hg => by
    obtain ⟨μ, hμ, hcμ, hγμ⟩ := hjVT_small hSt hS hc hx hx1 hγx hg
    rw [hjVTR_eq hSt hS hμ hcμ]; rw [hjVTg_eq hSt hS hμ hcμ] at hg
    exact ((hjVU St A S0 μ).R_lt_b x hx hx1 hγμ c hcμ hg).trans (hjVT_b_lt hSt hS hμ hx hx1 hγμ)
  R_lt_Z := fun x hx hx1 c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hjVT_cof hSt hS hc
    rw [hjVTR_eq hSt hS hn1 hn]; rw [hjVTg_eq hSt hS hn1 hn] at hg
    exact (((hjVU St A S0 n).R_lt_Z x hx hx1 c hn hg).trans_le (hjVU_Zb hSt hS hn1 x hx hx1)).trans_le (hjVTZ_ge x hx)
  mono := fun x hx hx1 c hc d hfc hgc hgd => by
    obtain ⟨n, hn1, hn⟩ := hjVT_cof hSt hS hc
    have hf : d < (hjVU St A S0 n).B := hfc.trans hn
    rw [hjVTR_eq hSt hS hn1 hn,
        hjVTR_eq hSt hS hn1 hf]; rw [hjVTg_eq hSt hS hn1 hn] at hgc; rw [hjVTg_eq hSt hS hn1 hf] at hgd
    exact (hjVU St A S0 n).mono x hx hx1 c hn d hfc hgc hgd
  cof := fun x hx hx1 c hc hg ν hν => by
    obtain ⟨n, hn1, hn⟩ := hjVT_cof hSt hS hc
    rw [hjVTR_eq hSt hS hn1 hn] at hν; rw [hjVTg_eq hSt hS hn1 hn] at hg
    obtain ⟨d, hfc, hgd, hνd⟩ := (hjVU St A S0 n).cof x hx hx1 c hn hg ν hν
    have hf : d < (hjVU St A S0 n).B := hfc.trans hn
    exact ⟨d, hfc, by rw [hjVTg_eq hSt hS hn1 hf]; exact hgd, by rw [hjVTR_eq hSt hS hn1 hf]; exact hνd⟩
  b_cof := fun x hx hx1 hγx ν hν => by
    obtain ⟨k, hk⟩ := hjVTr_cof hSt hS hx hx1 hγx hν
    have hkT : hjVTt A k < hcN (Λ.L + κ) A.F := hjVTt_lt A k
    have hkB : hjVTt A k < (hjVU St A S0 (hjVTt A k)).B := hjVU_self hSt hS hkT
    refine ⟨hjVTt A k, hkT, ?_, ?_⟩
    · rw [hjVTg_eq hSt hS hkT hkB]; exact hjVTt_g hSt hS hx hx1 hγx k
    · rw [hjVTR_eq hSt hS hkT hkB]; exact hk
  b_E := fun x _ _ _ => hcN_E (Λ.l x + κ) _
  x_lt_b := fun x hx hx1 hγx => ((hjv_xl Λ hx hx1).trans_lt (A.Fr_gt hx hx1 hγx)).trans (A.Fr_lt_N x)
  b_eN := fun x hx hx1 hγx => gz_eN_fix hx hx1
    (hc_fix_down (hjv_one Λ hx hx1 (A.ν_lt hx hx1 hγx)) (hcN_fix (Λ.l x + κ) _))
    (((hjv_xl Λ hx hx1).trans_lt (A.Fr_gt hx hx1 hγx)).trans (A.Fr_lt_N x)) (A.N_lt1x hx hx1 hγx)
  ba_lt := fun x hx hx1 hγx => A.N_lt1x hx hx1 hγx
  b_Z := fun x _ _ hγx => by
    show _ < hjVTZ A x
    unfold hjVTZ; rw [if_pos hγx]
    exact go_eN_lt_evZ (lt_evZ _)
  b_pi := fun _ _ hB hγ => A.N_pi hB hγ
  ba_pi := fun _ _ hB hγ => A.N_pi hB hγ
  ex := fun σ ρ hB c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hjVT_cof hSt hS hc
    rw [hjVTR_eq hSt hS hn1 hn, hjVTR_eq hSt hS hn1 hn]; rw [hjVTg_eq hSt hS hn1 hn] at hg
    exact (hjVU St A S0 n).ex σ ρ hB c hn hg
  dig := fun σ ρ hB hγσ d hf hg P P' hat => by
    obtain ⟨μ, hμ, hfμ, hγμ⟩ := hjVT_small hSt hS hf hB.1 (hB.2.2.1.trans hB.2.2.2) hγσ hg
    rw [hjVTR_eq hSt hS hμ hfμ, hjVTR_eq hSt hS hμ hfμ]; rw [hjVTg_eq hSt hS hμ hfμ] at hg
    exact (hjVU St A S0 μ).dig σ ρ hB hγμ d hfμ hg P P' (fun β hβ hβe =>
      hat β hβ (hβe.trans (hjVT_b_lt hSt hS hμ hB.2.1 hB.2.2.2 (hγμ.trans hB.2.2.1))))
  ld := fun c hl hc => by
    obtain ⟨n, hn1, hn⟩ := hjVT_cof hSt hS hc
    obtain ⟨cp, lp, T, hcp, hgcp, hfec, hex⟩ := (hjVU St A S0 n).ld c hl hn
    have hcpn : cp < (hjVU St A S0 n).B := hcp.trans hn
    refine ⟨cp, lp, T, hcp, by rw [hjVTg_eq hSt hS hn1 hn, hjVTg_eq hSt hS hn1 hcpn]; exact hgcp,
        fun x hx hx1 hg => ?_,
      fun σ ρ hB hg => hex σ ρ hB (by rw [← hjVTg_eq hSt hS hn1 hn]; exact hg)⟩
    rw [hjVTg_eq hSt hS hn1 hn] at hg
    rw [hjVTR_eq hSt hS hn1 hn, hjVTR_eq hSt hS hn1 hcpn]
    exact hfec x hx hx1 hg

theorem hjVTU_B : (hjVTU hSt hS).B = hcN (Λ.L + κ) A.F := rfl

theorem hjVTU_γ : (hjVTU hSt hS).γ = A.γN := rfl

theorem hjVTU_b (x : Ordinal.{0}) : (hjVTU hSt hS).b x = hcN (Λ.l x + κ) (A.Fr x) := rfl

/-- **The union extends every start** (readings). -/
theorem hjVTU_R {ν c : Ordinal.{0}} (hν : ν < hcN (Λ.L + κ) A.F) (hc : c < (hjVU St A S0 ν).B) (x : Ordinal.{0}) :
    (hjVTU hSt hS).R c x = (hjVU St A S0 ν).R c x := hjVTR_eq hSt hS hν hc x

/-- **The union extends every start** (gates). -/
theorem hjVTU_g {ν c : Ordinal.{0}} (hν : ν < hcN (Λ.L + κ) A.F) (hc : c < (hjVU St A S0 ν).B) :
    (hjVTU hSt hS).g c = (hjVU St A S0 ν).g c := hjVTg_eq hSt hS hν hc

/-- **The union extends the start `S0`.** -/
theorem hjVTU_R0 {c : Ordinal.{0}} (hc : c < S0.B) (x : Ordinal.{0}) : (hjVTU hSt hS).R c x = S0.R c x := by
  rw [hjVTU_R hSt hS (hjV_zero_lt_N A) (by rw [hjVU_zero]; exact hc), hjVU_zero]

theorem hjVTU_g0 {c : Ordinal.{0}} (hc : c < S0.B) : (hjVTU hSt hS).g c = S0.g c := by
  rw [hjVTU_g hSt hS (hjV_zero_lt_N A) (by rw [hjVU_zero]; exact hc), hjVU_zero]

/-- **A code `c ∈ [F, N(F))` of the union with gate below a base `σ` forces the base gate below `σ`.** -/
theorem hjVTU_high (hγN : A.γN = A.γ) {c σ : Ordinal.{0}} (hc : c < hcN (Λ.L + κ) A.F) (hFc : A.F ≤ c) (hσ : InE σ)
    (hσ1 : σ < Om1) (hg : (hjVTU hSt hS).g c < σ) : (hjVTU hSt hS).γ < σ := by
  show A.γN < σ
  rw [hγN]; exact hjVT_high hSt hS hc hFc hσ hσ1 hg

end Union

end Googology.Trans.PoR.InaccPsi.R2.Hj

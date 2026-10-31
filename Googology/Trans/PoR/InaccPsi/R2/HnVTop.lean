import Googology.Trans.PoR.InaccPsi.R2.HnVRec

/-!
# HnVTop (port of HlVTop): THE UNION OF ALL OFFSETS OF A BASE OF THE GATED LEVEL `L + ν`

PORT of `Hl.HlVTop` (the same proofs) to the band level datum `Hn.HnLv`.  What differs from `Hl.HlLv`: a level is
`L = Ω₁·u + Ω₁·q` (`q < Ω₁`, any `u`) in place of `L = Ω₁·q`; the code gate `g < Z` is asked for codes in
`[L, Ω₁·u + Ω₁²)` in place of `[L, Ω₁²)`; there is no field `ℓ(x) + x < x·x` (it is a hypothesis of the base `G`
only).  Declarations that do not mention a level datum are imported from `Hl`, not copied.

PORT of `Hj.HjVTop`.

What differs from the source: the level datum is a GATED one (`Hl.HlLv`: Lemma EXACT for the reading `ℓ` only at
base pairs `(σ, ρ)` above the level gate `g`, the hull membership of `L` only at `0 < a`, `g < b`, the code gate
`g < Z` only when a code over `Z` exists at the level); every pseudo-base and base carries `g ≤` its reading gate
(fields `lg`), and the code-gate fields take the extra hypothesis `g < Z`.  Proofs are otherwise those of the source;
names: prefix `hl`/`Hl` in place of `hj`/`Hj`.

No new axiom.  New definitions: `hnVTt`, `hnVTr`, `hnVTN`, `hnVTR`, `hnVTg`, `hnVTZ`, `hnVTU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hn

open Googology.Trans.PoR.InaccPsi.R2.Hl

open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk

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

variable {Λ : HnLv}

/-! ## The tower of offsets -/

section Tower

variable {κ : Ordinal.{0}} (A : HnVB Λ κ)

/-- **The tower of offsets**: `t_0 = 0`, `t_{k+1} = φ(2, F + 1 + t_k)`. -/
noncomputable def hnVTt : ℕ → Ordinal.{0}
  | 0 => 0
  | k + 1 => veblen (Λ.L + κ) (A.F + 1 + hnVTt k)

theorem hnVTt_lt : ∀ k : ℕ, hnVTt A k < hcN (Λ.L + κ) A.F
  | 0 => hnV_zero_lt_N A
  | k + 1 => A.Q_lt_N (hnVTt_lt k)

theorem hnVTt_lt_succ (k : ℕ) : hnVTt A k < hnVTt A (k + 1) := A.lt_Q (hnVTt_lt A k)

theorem hnVTt_iter (n : ℕ) : (veblen (Λ.L + κ))^[n] (A.F + 1) ≤ hnVTt A (n + 1) := by
  induction n with
  | zero =>
    show A.F + 1 ≤ veblen (Λ.L + κ) (A.F + 1 + 0)
    rw [add_zero]; exact right_le_veblen (Λ.L + κ) _
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    show veblen (Λ.L + κ) _ ≤ veblen (Λ.L + κ) (A.F + 1 + hnVTt A (n + 1))
    exact (isNormal_veblen (Λ.L + κ)).monotone (ih.trans le_add_self)

theorem hnV_N_nfp : hcN (Λ.L + κ) A.F = nfp (veblen (Λ.L + κ)) (A.F + 1) := rfl

/-- **The tower is cofinal in `N(F)`.** -/
theorem hnVTt_cof {c : Ordinal.{0}} (hc : c < hcN (Λ.L + κ) A.F) : ∃ k : ℕ, c < hnVTt A k := by
  rw [hnV_N_nfp] at hc
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hc
  exact ⟨n + 1, hn.trans_le (hnVTt_iter A n)⟩

variable {St : ∀ (Q : HnVQ Λ κ) (U : HgVD), HgSStart (hnVPB Q) U → HgVD} {S0 : HgVD}
  (hSt : ∀ Q U h, HnVSpec Q U (St Q U h)) (hS : HnVStart A S0)
include hSt hS

theorem hnVTt_B (k : ℕ) : (hnVU St A S0 (hnVTt A k)).B = hnVTt A (k + 1) := hnVU_B hSt hS (hnVTt_lt A k)

/-- **Every start `hnVU St A S0 t_k` has base gate below every base above `γN`.** -/
theorem hnVTt_gate : ∀ (k : ℕ) (x : Ordinal.{0}), InE x → x < Om1 → A.γN < x → (hnVU St A S0 (hnVTt A k)).γ < x
  | 0, x, hx, hx1, hA => by
    show (hnVU St A S0 0).γ < x
    rw [hnVU_γ_iff hSt hS (hnV_zero_lt_N A) hx hx1, (hnVU St A S0 0).g_zero, max_eq_left zero_le]; exact hA
  | k + 1, x, hx, hx1, hA => by
    set l := hnVTt A k with hl
    have hlT : l < hcN (Λ.L + κ) A.F := hnVTt_lt A k
    have hl'T : hnVTt A (k + 1) < hcN (Λ.L + κ) A.F := hnVTt_lt A (k + 1)
    have hsp := hnVU_succ_spec hSt hS hlT
    have hl1 : l + 1 ≤ hnVTt A (k + 1) := Order.add_one_le_of_lt (hnVTt_lt_succ A k)
    have hl1T : l + 1 < hcN (Λ.L + κ) A.F := hl1.trans_lt hl'T
    have hB : hnVTt A (k + 1) = (hnVU St A S0 l).B := (hnVTt_B A hSt hS k).symm
    have hcB : hnVTt A (k + 1) < (hnVU St A S0 (l + 1)).B := by
      rw [hnVU_B hSt hS hl1T, hB, hnVU_B hSt hS hlT]; exact A.Q_lt_Q (lt_add_one l)
    rw [hnVU_γ_iff hSt hS hl'T hx hx1, (hnV_ext hSt hS hl1 hl'T).2 _ hcB, hB, hnVU_B hSt hS hlT]
    refine max_lt hA ((hsp.gF x hx hx1).2 ?_)
    exact max_lt hA ((max_lt_iff.1 ((hnVU_γ_iff hSt hS hlT hx hx1).1 (hnVTt_gate k x hx hx1 hA))).2)

end Tower

/-- The reading of the tower code `t_k` (in its start). -/
noncomputable def hnVTr {κ : Ordinal.{0}} (St : ∀ (Q : HnVQ Λ κ) (U : HgVD), HgSStart (hnVPB Q) U → HgVD) (A : HnVB Λ κ)
    (S0 : HgVD) (k : ℕ)
    (x : Ordinal.{0}) : Ordinal.{0} := (hnVU St A S0 (hnVTt A k)).R (hnVTt A k) x

section TowerRead

variable {κ : Ordinal.{0}} {St : ∀ (Q : HnVQ Λ κ) (U : HgVD), HgSStart (hnVPB Q) U → HgVD}
  (hSt : ∀ Q U h, HnVSpec Q U (St Q U h))
  {A : HnVB Λ κ} {S0 : HgVD} (hS : HnVStart A S0) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hA : A.γN < x)
include hSt hS hx hx1 hA

theorem hnVTt_g (k : ℕ) : (hnVU St A S0 (hnVTt A k)).g (hnVTt A k) < x :=
  (max_lt_iff.1 ((hnVU_γ_iff hSt hS (hnVTt_lt A k) hx hx1).1 (hnVTt_gate A hSt hS k x hx hx1 hA))).2

/-- **`r_{k+1}(x) = ϑˣ(Ω₁·2 + F(x) + r_k(x))`**: the code `t_{k+1} = Q_{t_k}` is read as the base reading of the start
`t_k`. -/
theorem hnVTr_succ (k : ℕ) :
    hnVTr St A S0 (k + 1) x = glA (Λ.l x + κ) (A.Fr x + hnVTr St A S0 k x) x := by
  set l := hnVTt A k with hl
  have hlT : l < hcN (Λ.L + κ) A.F := hnVTt_lt A k
  have hl'T : hnVTt A (k + 1) < hcN (Λ.L + κ) A.F := hnVTt_lt A (k + 1)
  have hsp := hnVU_succ_spec hSt hS hlT
  have hl1 : l + 1 ≤ hnVTt A (k + 1) := Order.add_one_le_of_lt (hnVTt_lt_succ A k)
  have hl1T : l + 1 < hcN (Λ.L + κ) A.F := hl1.trans_lt hl'T
  have hB : hnVTt A (k + 1) = (hnVU St A S0 l).B := (hnVTt_B A hSt hS k).symm
  have hcB : hnVTt A (k + 1) < (hnVU St A S0 (l + 1)).B := by
    rw [hnVU_B hSt hS hl1T, hB, hnVU_B hSt hS hlT]; exact A.Q_lt_Q (lt_add_one l)
  have hg : max A.γN ((hnVU St A S0 l).g l) < x := max_lt hA (hnVTt_g hSt hS hx hx1 hA k)
  unfold hnVTr
  rw [(hnV_ext hSt hS hl1 hl'T).1 _ x hcB, hB, hnVU_B hSt hS hlT]
  exact hsp.RF x hx hx1 hg

theorem hnVTr_zero : hnVTr St A S0 0 x = 0 := by unfold hnVTr; exact (hnVU St A S0 (hnVTt A 0)).R_zero x

theorem hnVTr_lt_N (k : ℕ) : hnVTr St A S0 k x < hcN (Λ.l x + κ) (A.Fr x) :=
  A.lvR_lt_N _ (hnVU_Zb hSt hS (hnVTt_lt A k)) (hnVU_self hSt hS (hnVTt_lt A k)) hx hx1 hA
    (hnVTt_g hSt hS hx hx1 hA k)

/-- **The iterates of `φ((Λ.L + κ), ·)` from `hdNx (Λ.L + κ) (F(x)) + 1` lie below the tower readings.** -/
theorem hnVTr_iter (n : ℕ) :
    (veblen (Λ.l x + κ))^[n] (hdNx (Λ.l x + κ) (A.Fr x) + 1) ≤ hnVTr St A S0 (n + 2) x := by
  obtain ⟨i0, hi0⟩ := hdNx_LuP (Λ.l x + κ) (A.Fr x)
  have hstep : ∀ k : ℕ, hnVTr St A S0 (k + 1) x = veblen (Λ.l x + κ)
      (i0 + hnVTr St A S0 k x) := fun k => by
    rw [hnVTr_succ hSt hS hx hx1 hA k, A.lvglAV hx hx1 hA hi0 (hnVTr_lt_N hSt hS hx hx1 hA k)]
  have h1 : hnVTr St A S0 1 x = hdNx (Λ.l x + κ) (A.Fr x) := by
    rw [hstep 0, hnVTr_zero hSt hS hx hx1 hA, add_zero, hi0]
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply]
    refine Order.add_one_le_of_lt ?_
    rw [hstep 1, h1]
    refine (le_add_self : hdNx (Λ.l x + κ) (A.Fr x) ≤ i0 + hdNx (Λ.l x + κ) (A.Fr x)).trans_lt ?_
    have h2 := hnVTr_lt_N hSt hS hx hx1 hA 2
    rw [hstep 1, h1] at h2
    exact hc_nofixG (by rw [hi0]; exact hdNx_gt _ _) le_self_add h2
  | succ n ih =>
    rw [Function.iterate_succ_apply', hstep (n + 2)]
    exact (isNormal_veblen (Λ.l x + κ)).monotone (ih.trans le_add_self)

/-- **The tower readings are cofinal in `N_α(F(x))`.** -/
theorem hnVTr_cof {v : Ordinal.{0}} (hv : v < hcN (Λ.l x + κ) (A.Fr x)) : ∃ k : ℕ, v < hnVTr St A S0 k x := by
  have e : hcN (Λ.l x + κ) (A.Fr x) = nfp (veblen (Λ.l x + κ)) (hdNx (Λ.l x + κ) (A.Fr x) + 1) := by
    refine le_antisymm ?_ ?_
    · exact hcN_le (nfp_fp (isNormal_veblen _) _)
        ((hdNx_gt (Λ.l x + κ) (A.Fr x)).trans ((lt_add_one _).trans_le (le_nfp _ _)))
    · exact nfp_le_fp (isNormal_veblen (Λ.l x + κ)).strictMono.monotone
        (Order.add_one_le_of_lt (hdNx_lt_N (hcN_gt (Λ.l x + κ) (A.Fr x)))) (hcN_fix (Λ.l x + κ) _).le
  rw [e] at hv
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hv
  exact ⟨n + 2, hn.trans_le (hnVTr_iter hSt hS hx hx1 hA n)⟩

end TowerRead

/-! ## The union of all offsets -/

section Union

variable {κ : Ordinal.{0}} (St : ∀ (Q : HnVQ Λ κ) (U : HgVD), HgSStart (hnVPB Q) U → HgVD) (A : HnVB Λ κ) (S0 : HgVD)

/-- The first start containing `c`. -/
noncomputable def hnVTN (c : Ordinal.{0}) : Ordinal.{0} := sInf {ν | ν < hcN (Λ.L + κ) A.F ∧ c < (hnVU St A S0 ν).B}

/-- The reading of the union. -/
noncomputable def hnVTR (c x : Ordinal.{0}) : Ordinal.{0} := (hnVU St A S0 (hnVTN St A S0 c)).R c x

/-- The gate of the union. -/
noncomputable def hnVTg (c : Ordinal.{0}) : Ordinal.{0} := (hnVU St A S0 (hnVTN St A S0 c)).g c

open Classical in
/-- The bound field of the union: `evZ(N_α(F(x)))` above `γ`, `Z_o(x)` below. -/
noncomputable def hnVTZ (x : Ordinal.{0}) : Ordinal.{0} :=
  if A.γN < x then evZ (hcN (Λ.l x + κ) (A.Fr x)) else A.Zo x

variable {St A S0} (hSt : ∀ Q U h, HnVSpec Q U (St Q U h)) (hS : HnVStart A S0)
include hSt hS

theorem hnVT_cof {c : Ordinal.{0}} (hc : c < hcN (Λ.L + κ) A.F) : ∃ ν, ν < hcN (Λ.L + κ) A.F ∧ c <
    (hnVU St A S0 ν).B := by
  obtain ⟨k, hk⟩ := hnVTt_cof A hc
  exact ⟨hnVTt A k, hnVTt_lt A k, hk.trans (by rw [hnVTt_B A hSt hS k]; exact hnVTt_lt_succ A k)⟩

omit hSt hS in
theorem hnVTN_spec {c ν : Ordinal.{0}} (hν : ν < hcN (Λ.L + κ) A.F) (hc : c < (hnVU St A S0 ν).B) :
    hnVTN St A S0 c ≤ ν ∧ hnVTN St A S0 c < hcN (Λ.L + κ) A.F ∧ c < (hnVU St A S0 (hnVTN St A S0 c)).B := by
  have hne : ({ν | ν < hcN (Λ.L + κ) A.F ∧ c < (hnVU St A S0 ν).B} : Set Ordinal.{0}).Nonempty := ⟨ν, hν, hc⟩
  have hm := csInf_mem hne
  exact ⟨csInf_le' ⟨hν, hc⟩, hm.1, hm.2⟩

omit hSt hS in
theorem hnVTN_min {c μ : Ordinal.{0}} (hμ : μ < hnVTN St A S0 c) (hμl : μ < hcN (Λ.L + κ) A.F) : ¬ c <
    (hnVU St A S0 μ).B :=
  fun hcμ => absurd (csInf_le' ⟨hμl, hcμ⟩ : hnVTN St A S0 c ≤ μ) (not_le.2 hμ)

theorem hnVT_B_lt {ν : Ordinal.{0}} (hν : ν < hcN (Λ.L + κ) A.F) : (hnVU St A S0 ν).B < hcN (Λ.L + κ) A.F := by
  rw [hnVU_B hSt hS hν]; exact A.Q_lt_N hν

theorem hnVTN_high {c : Ordinal.{0}} (hc : hcN (Λ.L + κ) A.F ≤ c) : hnVTN St A S0 c = 0 := by
  unfold hnVTN
  have he : ({ν | ν < hcN (Λ.L + κ) A.F ∧ c < (hnVU St A S0 ν).B} : Set Ordinal.{0}) = ∅ := by
    ext ν
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hν hcν
    exact absurd (hcν.trans (hnVT_B_lt hSt hS hν)) (not_lt.2 hc)
  rw [he]; exact Ordinal.sInf_empty

theorem hnVTR_eq {c ν : Ordinal.{0}} (hν : ν < hcN (Λ.L + κ) A.F) (hc : c < (hnVU St A S0 ν).B) (x : Ordinal.{0}) :
    hnVTR St A S0 c x = (hnVU St A S0 ν).R c x := by
  obtain ⟨h1, -, h3⟩ := hnVTN_spec hν hc
  exact ((hnV_ext hSt hS h1 hν).1 c x h3).symm

theorem hnVTg_eq {c ν : Ordinal.{0}} (hν : ν < hcN (Λ.L + κ) A.F) (hc : c < (hnVU St A S0 ν).B) :
    hnVTg St A S0 c = (hnVU St A S0 ν).g c := by
  obtain ⟨h1, -, h3⟩ := hnVTN_spec hν hc
  exact ((hnV_ext hSt hS h1 hν).2 c h3).symm

theorem hnVTR_succ (c x : Ordinal.{0}) : hnVTR St A S0 (c + 1) x = hnVTR St A S0 c x + 1 := by
  rcases lt_or_ge c (hcN (Λ.L + κ) A.F) with h | h
  · obtain ⟨n, hn1, hn⟩ := hnVT_cof hSt hS (A.N_lim.add_one_lt h)
    rw [hnVTR_eq hSt hS hn1 hn, hnVTR_eq hSt hS hn1 ((lt_add_one c).trans hn), (hnVU St A S0 n).R_succ]
  · unfold hnVTR
    rw [hnVTN_high hSt hS h, hnVTN_high hSt hS (h.trans (le_self_add (a := c) (b := 1))), (hnVU St A S0 0).R_succ]

theorem hnVTg_le_succ (c : Ordinal.{0}) : hnVTg St A S0 c ≤ hnVTg St A S0 (c + 1) := by
  rcases lt_or_ge c (hcN (Λ.L + κ) A.F) with h | h
  · obtain ⟨n, hn1, hn⟩ := hnVT_cof hSt hS (A.N_lim.add_one_lt h)
    rw [hnVTg_eq hSt hS hn1 hn, hnVTg_eq hSt hS hn1 ((lt_add_one c).trans hn)]; exact (hnVU St A S0 n).g_le_succ c
  · unfold hnVTg
    rw [hnVTN_high hSt hS h, hnVTN_high hSt hS (h.trans (le_self_add (a := c) (b := 1)))]; exact
        (hnVU St A S0 0).g_le_succ c

/-- **A code of the union with gate below a base `σ > γ_F` lies in a start with base gate below `σ`.** -/
theorem hnVT_small {c σ : Ordinal.{0}} (hc : c < hcN (Λ.L + κ) A.F) (hσ : InE σ) (hσ1 : σ < Om1) (hAσ : A.γN < σ)
    (hg : hnVTg St A S0 c < σ) : ∃ μ, μ < hcN (Λ.L + κ) A.F ∧ c < (hnVU St A S0 μ).B ∧ (hnVU St A S0 μ).γ < σ := by
  obtain ⟨n, hn1, hn⟩ := hnVT_cof hSt hS hc
  obtain ⟨-, hN1, hcNc⟩ := hnVTN_spec hn1 hn
  have hgN : hnVTg St A S0 c = (hnVU St A S0 (hnVTN St A S0 c)).g c := rfl
  have I := hnV_inv hSt hS _ hN1
  rcases zero_or_succ_or_isSuccLimit (hnVTN St A S0 c) with h0 | ⟨m, hm⟩ | hlim
  · refine ⟨hnVTN St A S0 c, hN1, hcNc, ?_⟩
    rw [h0, hnVU_γ_iff hSt hS (hnV_zero_lt_N A) hσ hσ1, (hnVU St A S0 0).g_zero, max_eq_left zero_le]
    exact hAσ
  · have hm' : hnVTN St A S0 c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < hnVTN St A S0 c := by rw [hm']; exact lt_add_one m
    have hml : m < hcN (Λ.L + κ) A.F := hmN.trans hN1
    have hBc : (hnVU St A S0 m).B ≤ c := not_lt.1 (hnVTN_min hmN hml)
    refine ⟨hnVTN St A S0 c, hN1, hcNc, ?_⟩
    rw [hgN, hm'] at hg
    rw [hm'] at hcNc I ⊢
    exact I.high m (lt_add_one _) c σ hBc hcNc hσ hσ1 hg
  · exfalso
    rw [hnVU_B hSt hS hN1] at hcNc
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen (Λ.L + κ)).lt_iff_exists_lt
        (isSuccLimit_add _ hlim)).1 hcNc
    obtain ⟨d, hf, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    have hfl : d < hcN (Λ.L + κ) A.F := hf.trans hN1
    refine hnVTN_min hf hfl ?_
    rw [hnVU_B hSt hS hfl]; exact hct.trans_le ((isNormal_veblen (Λ.L + κ)).monotone htd)

/-- **A code `c ∈ [F, N(F))` of the union with gate below a base `σ` forces `γ_F < σ`.** -/
theorem hnVT_high {c σ : Ordinal.{0}} (hc : c < hcN (Λ.L + κ) A.F) (hFc : A.F ≤ c) (hσ : InE σ) (hσ1 : σ < Om1)
    (hg : hnVTg St A S0 c < σ) : A.γ < σ := by
  obtain ⟨n, hn1, hn⟩ := hnVT_cof hSt hS hc
  obtain ⟨-, hN1, hcNc⟩ := hnVTN_spec hn1 hn
  have hgN : hnVTg St A S0 c = (hnVU St A S0 (hnVTN St A S0 c)).g c := rfl
  have I := hnV_inv hSt hS _ hN1
  rcases zero_or_succ_or_isSuccLimit (hnVTN St A S0 c) with h0 | ⟨m, hm⟩ | hlim
  · rw [hgN, h0, hnVU_zero] at hg
    rw [h0, hnVU_zero] at hcNc
    exact hS.high0 c σ hFc hcNc hσ hσ1 hg
  · have hm' : hnVTN St A S0 c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < hnVTN St A S0 c := by rw [hm']; exact lt_add_one m
    have hml : m < hcN (Λ.L + κ) A.F := hmN.trans hN1
    have hBc : (hnVU St A S0 m).B ≤ c := not_lt.1 (hnVTN_min hmN hml)
    rw [hgN, hm'] at hg
    rw [hm'] at hcNc I hN1
    have hγ := I.high m (lt_add_one _) c σ hBc hcNc hσ hσ1 hg
    exact A.γ_le.trans_lt (max_lt_iff.1 ((hnVU_γ_iff hSt hS hN1 hσ hσ1).1 hγ)).1
  · exfalso
    rw [hnVU_B hSt hS hN1] at hcNc
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen (Λ.L + κ)).lt_iff_exists_lt
        (isSuccLimit_add _ hlim)).1 hcNc
    obtain ⟨d, hf, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    have hfl : d < hcN (Λ.L + κ) A.F := hf.trans hN1
    refine hnVTN_min hf hfl ?_
    rw [hnVU_B hSt hS hfl]; exact hct.trans_le ((isNormal_veblen (Λ.L + κ)).monotone htd)

/-- **`b_μ(x) < N(F(x))`** for every start with base gate below `x`. -/
theorem hnVT_b_lt {μ x : Ordinal.{0}} (hμ : μ < hcN (Λ.L + κ) A.F) (hx : InE x) (hx1 : x < Om1) (hγ :
    (hnVU St A S0 μ).γ < x) :
    (hnVU St A S0 μ).b x < hcN (Λ.l x + κ) (A.Fr x) := by
  have hg : max A.γN ((hnVU St A S0 μ).g μ) < x := (hnVU_γ_iff hSt hS hμ hx hx1).1 hγ
  have hA : A.γN < x := (max_lt_iff.1 hg).1
  rw [(hnVU_start hSt hS hμ).b x hx hx1 hg]
  exact A.glA_lt_N hx hx1 hA (A.lvR_lt_N _ (hnVU_Zb hSt hS hμ) (hnVU_self hSt hS hμ) hx hx1 hA (max_lt_iff.1 hg).2)

omit hSt hS in
theorem hnVTZ_fix (x : Ordinal.{0}) : veblen 1 (hnVTZ A x) = hnVTZ A x := by
  unfold hnVTZ; split_ifs
  · exact epsilon_evZ _
  · exact ha_fix1_of_fix2 (A.Zo_fix x)

omit hSt hS in
theorem hnVTZ_G1 (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : hnVTZ A x < gq 1 x := by
  unfold hnVTZ; split_ifs with h
  · exact (hb_evZ_lt_fix2 (A.Zo_fix x) (A.N_Zo hx hx1 h)).trans (A.Zo_G1 x hx hx1)
  · exact A.Zo_G1 x hx hx1

omit hSt hS in
theorem hnVTZ_ge (x : Ordinal.{0}) (hx : InE x) : A.Zl x ≤ hnVTZ A x := by
  by_cases h : A.γN < x
  · rw [A.Zl_eq hx h]; unfold hnVTZ; rw [if_pos h]; exact (lt_evZ _).le
  · rw [A.Zl_low h]; unfold hnVTZ; rw [if_neg h]

/-- **THE SYSTEM AT `N(F)`**: the union of all starts `hnVU St A S0 λ`, `λ < N(F)`: bound `N(F)`, base gate `γN`, base
reading `N(F(x))`, bound field `hnVTZ`. -/
noncomputable def hnVTU : HgVD where
  B := hcN (Λ.L + κ) A.F
  γ := A.γN
  γ_lt := A.γN_lt
  γ_cl := fun Z hZ hZ1 h => A.N_cl Z hZ hZ1 h
  γ_G := fun h => absurd h (A.G_le.trans_lt A.F_lt_N).ne'
  R := hnVTR St A S0
  g := hnVTg St A S0
  b := fun x => hcN (Λ.l x + κ) (A.Fr x)
  ba := fun x => hcN (Λ.l x + κ) (A.Fr x)
  ix := hcN (Λ.L + κ) A.F
  Z := hnVTZ A
  B_E := A.N_E
  G_le := (A.G_le.trans_lt A.F_lt_N).le
  B_lt1 := A.N_lt1
  B_ix := (hc_fix_down (hnv_L1 Λ κ) (hcN_fix (Λ.L + κ) A.F)).symm
  Z_fix := fun x _ _ => hnVTZ_fix x
  Z_G1 := hnVTZ_G1
  ix_mem := fun S _ _ ha hb => A.N_mem S ha hb
  g_lt := fun c hc => by
    obtain ⟨n, hn1, hn⟩ := hnVT_cof hSt hS hc
    rw [hnVTg_eq hSt hS hn1 hn]; exact (hnVU St A S0 n).g_lt c hn
  g_zero := by
    rw [hnVTg_eq hSt hS (hnV_zero_lt_N A) (hnVU St A S0 0).B_pos]; exact (hnVU St A S0 0).g_zero
  g_nat := fun k => by
    rw [hnVTg_eq hSt hS (hnV_zero_lt_N A) ((hnVU St A S0 0).nat_lt_B k)]; exact (hnVU St A S0 0).g_nat k
  g_E := by rw [hnVTg_eq hSt hS (hnV_zero_lt_N A) (hnVU St A S0 0).E_lt_B]; exact (hnVU St A S0 0).g_E
  g_lowE := fun c hc => by
    rw [hnVTg_eq hSt hS (hnV_zero_lt_N A) (hc.trans (hnVU St A S0 0).E_lt_B)]; exact (hnVU St A S0 0).g_lowE c hc
  g_G0 := fun h => by
    obtain ⟨n, hn1, hn⟩ := hnVT_cof hSt hS h
    rw [hnVTg_eq hSt hS hn1 hn]; exact (hnVU St A S0 n).g_G0 hn
  g_add := fun Z hZ hωZ x y hxy hgx hgy => by
    obtain ⟨n, hn1, hn⟩ := hnVT_cof hSt hS hxy
    have hx : x < (hnVU St A S0 n).B := lt_of_le_of_lt le_self_add hn
    have hy : y < (hnVU St A S0 n).B := lt_of_le_of_lt le_add_self hn
    rw [hnVTg_eq hSt hS hn1 hn]; rw [hnVTg_eq hSt hS hn1 hx] at hgx; rw [hnVTg_eq hSt hS hn1 hy] at hgy
    exact (hnVU St A S0 n).g_add Z hZ hωZ x y hn hgx hgy
  g_opow := fun Z hZw hωZ y hy hg => by
    obtain ⟨n, hn1, hn⟩ := hnVT_cof hSt hS hy
    have hy' : y < (hnVU St A S0 n).B := lt_of_le_of_lt (right_le_opow y one_lt_omega0) hn
    rw [hnVTg_eq hSt hS hn1 hn]; rw [hnVTg_eq hSt hS hn1 hy'] at hg
    exact (hnVU St A S0 n).g_opow Z hZw hωZ y hn hg
  code_gate := fun Z hZ1 hZ0 hZa hZp At hAt c hc hcB => by
    obtain ⟨n, hn1, hn⟩ := hnVT_cof hSt hS hcB
    rw [hnVTg_eq hSt hS hn1 hn]
    exact (hnVU St A S0 n).code_gate Z hZ1 hZ0 hZa hZp At (fun s hs => (hAt s hs).imp_right
      (fun h => (hnVT_B_lt hSt hS hn1).le.trans h)) c hc hn
  g_succ := fun Z hZ c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hnVT_cof hSt hS hc
    have hc' : c < (hnVU St A S0 n).B := (lt_add_one c).trans hn
    rw [hnVTg_eq hSt hS hn1 hn]; rw [hnVTg_eq hSt hS hn1 hc'] at hg
    exact (hnVU St A S0 n).g_succ Z hZ c hn hg
  g_le_succ := hnVTg_le_succ hSt hS
  mem := fun S a b ha c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hnVT_cof hSt hS hc
    rw [hnVTg_eq hSt hS hn1 hn] at hg
    exact (hnVU St A S0 n).mem S a b ha c hn hg
  R_zero := fun x => by
    rw [hnVTR_eq hSt hS (hnV_zero_lt_N A) (hnVU St A S0 0).B_pos]; exact (hnVU St A S0 0).R_zero x
  R_nat := fun k x => by
    rw [hnVTR_eq hSt hS (hnV_zero_lt_N A) ((hnVU St A S0 0).nat_lt_B k)]; exact (hnVU St A S0 0).R_nat k x
  R_E := fun x => by rw [hnVTR_eq hSt hS (hnV_zero_lt_N A) (hnVU St A S0 0).E_lt_B]; exact (hnVU St A S0 0).R_E x
  R_succ := hnVTR_succ hSt hS
  R_pos := fun x hx hx1 c hc0 hc hg => by
    obtain ⟨n, hn1, hn⟩ := hnVT_cof hSt hS hc
    rw [hnVTR_eq hSt hS hn1 hn]; rw [hnVTg_eq hSt hS hn1 hn] at hg
    exact (hnVU St A S0 n).R_pos x hx hx1 c hc0 hn hg
  R_omega := fun x hx hx1 c hω hc hg => by
    obtain ⟨n, hn1, hn⟩ := hnVT_cof hSt hS hc
    rw [hnVTR_eq hSt hS hn1 hn]; rw [hnVTg_eq hSt hS hn1 hn] at hg
    exact (hnVU St A S0 n).R_omega x hx hx1 c hω hn hg
  R_lt_b := fun x hx hx1 hγx c hc hg => by
    obtain ⟨μ, hμ, hcμ, hγμ⟩ := hnVT_small hSt hS hc hx hx1 hγx hg
    rw [hnVTR_eq hSt hS hμ hcμ]; rw [hnVTg_eq hSt hS hμ hcμ] at hg
    exact ((hnVU St A S0 μ).R_lt_b x hx hx1 hγμ c hcμ hg).trans (hnVT_b_lt hSt hS hμ hx hx1 hγμ)
  R_lt_Z := fun x hx hx1 c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hnVT_cof hSt hS hc
    rw [hnVTR_eq hSt hS hn1 hn]; rw [hnVTg_eq hSt hS hn1 hn] at hg
    exact (((hnVU St A S0 n).R_lt_Z x hx hx1 c hn hg).trans_le (hnVU_Zb hSt hS hn1 x hx hx1)).trans_le (hnVTZ_ge x hx)
  mono := fun x hx hx1 c hc d hfc hgc hgd => by
    obtain ⟨n, hn1, hn⟩ := hnVT_cof hSt hS hc
    have hf : d < (hnVU St A S0 n).B := hfc.trans hn
    rw [hnVTR_eq hSt hS hn1 hn,
        hnVTR_eq hSt hS hn1 hf]; rw [hnVTg_eq hSt hS hn1 hn] at hgc; rw [hnVTg_eq hSt hS hn1 hf] at hgd
    exact (hnVU St A S0 n).mono x hx hx1 c hn d hfc hgc hgd
  cof := fun x hx hx1 c hc hg ν hν => by
    obtain ⟨n, hn1, hn⟩ := hnVT_cof hSt hS hc
    rw [hnVTR_eq hSt hS hn1 hn] at hν; rw [hnVTg_eq hSt hS hn1 hn] at hg
    obtain ⟨d, hfc, hgd, hνd⟩ := (hnVU St A S0 n).cof x hx hx1 c hn hg ν hν
    have hf : d < (hnVU St A S0 n).B := hfc.trans hn
    exact ⟨d, hfc, by rw [hnVTg_eq hSt hS hn1 hf]; exact hgd, by rw [hnVTR_eq hSt hS hn1 hf]; exact hνd⟩
  b_cof := fun x hx hx1 hγx ν hν => by
    obtain ⟨k, hk⟩ := hnVTr_cof hSt hS hx hx1 hγx hν
    have hkT : hnVTt A k < hcN (Λ.L + κ) A.F := hnVTt_lt A k
    have hkB : hnVTt A k < (hnVU St A S0 (hnVTt A k)).B := hnVU_self hSt hS hkT
    refine ⟨hnVTt A k, hkT, ?_, ?_⟩
    · rw [hnVTg_eq hSt hS hkT hkB]; exact hnVTt_g hSt hS hx hx1 hγx k
    · rw [hnVTR_eq hSt hS hkT hkB]; exact hk
  b_E := fun x _ _ _ => hcN_E (Λ.l x + κ) _
  x_lt_b := fun x hx hx1 hγx => ((hnv_xl Λ hx hx1).trans_lt (A.Fr_gt hx hx1 hγx)).trans (A.Fr_lt_N x)
  b_eN := fun x hx hx1 hγx => gz_eN_fix hx hx1
    (hc_fix_down (hnv_one Λ hx hx1 (A.ν_lt hx hx1 hγx)) (hcN_fix (Λ.l x + κ) _))
    (((hnv_xl Λ hx hx1).trans_lt (A.Fr_gt hx hx1 hγx)).trans (A.Fr_lt_N x)) (A.N_lt1x hx hx1 hγx)
  ba_lt := fun x hx hx1 hγx => A.N_lt1x hx hx1 hγx
  b_Z := fun x _ _ hγx => by
    show _ < hnVTZ A x
    unfold hnVTZ; rw [if_pos hγx]
    exact go_eN_lt_evZ (lt_evZ _)
  b_pi := fun _ _ hB hγ => A.N_pi hB hγ
  ba_pi := fun _ _ hB hγ => A.N_pi hB hγ
  ex := fun σ ρ hB c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hnVT_cof hSt hS hc
    rw [hnVTR_eq hSt hS hn1 hn, hnVTR_eq hSt hS hn1 hn]; rw [hnVTg_eq hSt hS hn1 hn] at hg
    exact (hnVU St A S0 n).ex σ ρ hB c hn hg
  dig := fun σ ρ hB hγσ d hf hg P P' hat => by
    obtain ⟨μ, hμ, hfμ, hγμ⟩ := hnVT_small hSt hS hf hB.1 (hB.2.2.1.trans hB.2.2.2) hγσ hg
    rw [hnVTR_eq hSt hS hμ hfμ, hnVTR_eq hSt hS hμ hfμ]; rw [hnVTg_eq hSt hS hμ hfμ] at hg
    exact (hnVU St A S0 μ).dig σ ρ hB hγμ d hfμ hg P P' (fun β hβ hβe =>
      hat β hβ (hβe.trans (hnVT_b_lt hSt hS hμ hB.2.1 hB.2.2.2 (hγμ.trans hB.2.2.1))))
  ld := fun c hl hc => by
    obtain ⟨n, hn1, hn⟩ := hnVT_cof hSt hS hc
    obtain ⟨cp, lp, T, hcp, hgcp, hfec, hex⟩ := (hnVU St A S0 n).ld c hl hn
    have hcpn : cp < (hnVU St A S0 n).B := hcp.trans hn
    refine ⟨cp, lp, T, hcp, by rw [hnVTg_eq hSt hS hn1 hn, hnVTg_eq hSt hS hn1 hcpn]; exact hgcp,
        fun x hx hx1 hg => ?_,
      fun σ ρ hB hg => hex σ ρ hB (by rw [← hnVTg_eq hSt hS hn1 hn]; exact hg)⟩
    rw [hnVTg_eq hSt hS hn1 hn] at hg
    rw [hnVTR_eq hSt hS hn1 hn, hnVTR_eq hSt hS hn1 hcpn]
    exact hfec x hx hx1 hg

theorem hnVTU_B : (hnVTU hSt hS).B = hcN (Λ.L + κ) A.F := rfl

theorem hnVTU_γ : (hnVTU hSt hS).γ = A.γN := rfl

theorem hnVTU_b (x : Ordinal.{0}) : (hnVTU hSt hS).b x = hcN (Λ.l x + κ) (A.Fr x) := rfl

/-- **The union extends every start** (readings). -/
theorem hnVTU_R {ν c : Ordinal.{0}} (hν : ν < hcN (Λ.L + κ) A.F) (hc : c < (hnVU St A S0 ν).B) (x : Ordinal.{0}) :
    (hnVTU hSt hS).R c x = (hnVU St A S0 ν).R c x := hnVTR_eq hSt hS hν hc x

/-- **The union extends every start** (gates). -/
theorem hnVTU_g {ν c : Ordinal.{0}} (hν : ν < hcN (Λ.L + κ) A.F) (hc : c < (hnVU St A S0 ν).B) :
    (hnVTU hSt hS).g c = (hnVU St A S0 ν).g c := hnVTg_eq hSt hS hν hc

/-- **The union extends the start `S0`.** -/
theorem hnVTU_R0 {c : Ordinal.{0}} (hc : c < S0.B) (x : Ordinal.{0}) : (hnVTU hSt hS).R c x = S0.R c x := by
  rw [hnVTU_R hSt hS (hnV_zero_lt_N A) (by rw [hnVU_zero]; exact hc), hnVU_zero]

theorem hnVTU_g0 {c : Ordinal.{0}} (hc : c < S0.B) : (hnVTU hSt hS).g c = S0.g c := by
  rw [hnVTU_g hSt hS (hnV_zero_lt_N A) (by rw [hnVU_zero]; exact hc), hnVU_zero]

/-- **A code `c ∈ [F, N(F))` of the union with gate below a base `σ` forces the base gate below `σ`.** -/
theorem hnVTU_high (hγN : A.γN = A.γ) {c σ : Ordinal.{0}} (hc : c < hcN (Λ.L + κ) A.F) (hFc : A.F ≤ c) (hσ : InE σ)
    (hσ1 : σ < Om1) (hg : (hnVTU hSt hS).g c < σ) : (hnVTU hSt hS).γ < σ := by
  show A.γN < σ
  rw [hγN]; exact hnVT_high hSt hS hc hFc hσ hσ1 hg

end Union

end Googology.Trans.PoR.InaccPsi.R2.Hn

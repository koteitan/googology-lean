import Googology.Trans.PoR.InaccPsi.R2.HgPB
import Googology.Trans.PoR.InaccPsi.R2.HgS
import Googology.Trans.PoR.InaccPsi.R2.HgSRec
import Googology.Trans.PoR.InaccPsi.R2.HgSU
import Googology.Trans.PoR.InaccPsi.R2.HgX
import Googology.Trans.PoR.InaccPsi.R2.HgLv
import Googology.Trans.PoR.InaccPsi.R2.HgLvRec
import Googology.Trans.PoR.InaccPsi.R2.HgLvTop
import Googology.Trans.PoR.InaccPsi.R2.HgRec
import Googology.Trans.PoR.InaccPsi.R2.HgCh
import Googology.Trans.PoR.InaccPsi.R2.HgdX
import Googology.Trans.PoR.InaccPsi.R2.HgdCh
import Googology.Trans.PoR.InaccPsi.R2.HgdStep
import Googology.Trans.PoR.InaccPsi.R2.HgdLv
import Googology.Trans.PoR.InaccPsi.R2.HgdLvRec
import Googology.Trans.PoR.InaccPsi.R2.HgdLvTop
import Googology.Trans.PoR.InaccPsi.R2.HgdM
import Googology.Trans.PoR.InaccPsi.R2.HgdMLv
import Googology.Trans.PoR.InaccPsi.R2.HgdMRec

/-!
# HgdMTop: THE UNION OF ALL OFFSETS OF A BASE OF EVERY CONSTANT LEVEL `α`: THE TOWER TO `N_α(F) = φ(α+1, F+1)`

(Textual copy of `Hd.HdMTop` for `Hg.HgVD`: bound fields `< Γ_{x+2}` in place of `≤ B_x(x)` (`Hc.hcBR`); the proofs
are unchanged except where the bound enters.  Names: prefix `hg`/`Hg` (from `hc`/`Hc`), `hgd`/`Hgd` (from `hd`/`Hd`),
`hgf`/`Hgf` (from `hf`/`Hf`), `hge`/`Hge` (from `he`/`He`).)

The level-`α` version of `Hd.HdLvTop`, for any step `St` of level `α` with the specification.  For a base
`A : Hd.HgdB α` and a start `S0`, the union of all starts `Hg.hgdMU St A S0 λ`, `λ < N_α(F)`, is a system `hgdMTU` with
the bound `N_α(F)`, base gate `γ`, base reading `N_α(F(x))`, bound field `evZ(N_α(F(x)))` above `γ` and `Z_o(x)`
below; the tower `t_0 = 0`, `t_{k+1} = φ(α, F + 1 + t_k)` is cofinal in `N_α(F)` and its readings are cofinal in
`N_α(F(x))`; the union extends the start, reads it, and has the high-gate property (`hgdMTU_high`).

* `hgdMTt`, `hgdMTt_cof`, `hgdMTt_gate`, `hgdMTr`, `hgdMTr_succ`, `hgdMTr_cof`; `hgdMTN`, `hgdMTR`, `hgdMTg`, `hgdMTZ`,
  `hgdMT_small`, `hgdMT_high`, `hgdMTU` (**THE SYSTEM AT `N_α(F)`, EVERY CONSTANT LEVEL**), `hgdMTU_R0`, `hgdMTU_g0`,
  `hgdMTU_high`.

No new axiom.  New definitions: `hgdMTt`, `hgdMTr`, `hgdMTN`, `hgdMTR`, `hgdMTg`, `hgdMTZ`, `hgdMTU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hg

open Googology.Trans.PoR.InaccPsi.R2.Hc
open Googology.Trans.PoR.InaccPsi.R2.Hd

open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The tower of offsets -/

section Tower

variable {α : Ordinal.{0}} (A : HgdB α)

/-- **The tower of offsets**: `t_0 = 0`, `t_{k+1} = φ(2, F + 1 + t_k)`. -/
noncomputable def hgdMTt : ℕ → Ordinal.{0}
  | 0 => 0
  | k + 1 => veblen α (A.F + 1 + hgdMTt k)

theorem hgdMTt_lt : ∀ k : ℕ, hgdMTt A k < hcN α A.F
  | 0 => hgdM_zero_lt_N A
  | k + 1 => A.Q_lt_N (hgdMTt_lt k)

theorem hgdMTt_lt_succ (k : ℕ) : hgdMTt A k < hgdMTt A (k + 1) := A.lt_Q (hgdMTt_lt A k)

theorem hgdMTt_iter (n : ℕ) : (veblen α)^[n] (A.F + 1) ≤ hgdMTt A (n + 1) := by
  induction n with
  | zero =>
    show A.F + 1 ≤ veblen α (A.F + 1 + 0)
    rw [add_zero]; exact right_le_veblen α _
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    show veblen α _ ≤ veblen α (A.F + 1 + hgdMTt A (n + 1))
    exact (isNormal_veblen α).monotone (ih.trans le_add_self)

theorem hgdM_N_nfp : hcN α A.F = nfp (veblen α) (A.F + 1) := rfl

/-- **The tower is cofinal in `N(F)`.** -/
theorem hgdMTt_cof {c : Ordinal.{0}} (hc : c < hcN α A.F) : ∃ k : ℕ, c < hgdMTt A k := by
  rw [hgdM_N_nfp] at hc
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hc
  exact ⟨n + 1, hn.trans_le (hgdMTt_iter A n)⟩

variable {St : ∀ (Q : HgdQ α) (U : HgVD), HgSStart (hgdQPB Q) U → HgVD} {S0 : HgVD}
  (hSt : ∀ Q U h, HgdQSpec Q U (St Q U h)) (hS : HgdMStart A S0)
include hSt hS

theorem hgdMTt_B (k : ℕ) : (hgdMU St A S0 (hgdMTt A k)).B = hgdMTt A (k + 1) := hgdMU_B hSt hS (hgdMTt_lt A k)

/-- **Every start `hgdMU St A S0 t_k` has base gate below every base above `γ_F`.** -/
theorem hgdMTt_gate : ∀ (k : ℕ) (x : Ordinal.{0}), InE x → x < Om1 → A.γ < x → (hgdMU St A S0 (hgdMTt A k)).γ < x
  | 0, x, hx, hx1, hA => by
    show (hgdMU St A S0 0).γ < x
    rw [hgdMU_γ_iff hSt hS (hgdM_zero_lt_N A) hx hx1, (hgdMU St A S0 0).g_zero, max_eq_left zero_le]; exact hA
  | k + 1, x, hx, hx1, hA => by
    set l := hgdMTt A k with hl
    have hlT : l < hcN α A.F := hgdMTt_lt A k
    have hl'T : hgdMTt A (k + 1) < hcN α A.F := hgdMTt_lt A (k + 1)
    have hsp := hgdMU_succ_spec hSt hS hlT
    have hl1 : l + 1 ≤ hgdMTt A (k + 1) := Order.add_one_le_of_lt (hgdMTt_lt_succ A k)
    have hl1T : l + 1 < hcN α A.F := hl1.trans_lt hl'T
    have hB : hgdMTt A (k + 1) = (hgdMU St A S0 l).B := (hgdMTt_B A hSt hS k).symm
    have hcB : hgdMTt A (k + 1) < (hgdMU St A S0 (l + 1)).B := by
      rw [hgdMU_B hSt hS hl1T, hB, hgdMU_B hSt hS hlT]; exact A.Q_lt_Q (lt_add_one l)
    rw [hgdMU_γ_iff hSt hS hl'T hx hx1, (hgdM_ext hSt hS hl1 hl'T).2 _ hcB, hB, hgdMU_B hSt hS hlT]
    refine max_lt hA ((hsp.gF x hx hx1).2 ?_)
    exact max_lt hA ((max_lt_iff.1 ((hgdMU_γ_iff hSt hS hlT hx hx1).1 (hgdMTt_gate k x hx hx1 hA))).2)

end Tower

/-- The reading of the tower code `t_k` (in its start). -/
noncomputable def hgdMTr {α : Ordinal.{0}} (St : ∀ (Q : HgdQ α) (U : HgVD), HgSStart (hgdQPB Q) U → HgVD) (A : HgdB α)
    (S0 : HgVD) (k : ℕ)
    (x : Ordinal.{0}) : Ordinal.{0} := (hgdMU St A S0 (hgdMTt A k)).R (hgdMTt A k) x

section TowerRead

variable {α : Ordinal.{0}} {St : ∀ (Q : HgdQ α) (U : HgVD), HgSStart (hgdQPB Q) U → HgVD}
  (hSt : ∀ Q U h, HgdQSpec Q U (St Q U h))
  {A : HgdB α} {S0 : HgVD} (hS : HgdMStart A S0) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hA : A.γ < x)
include hSt hS hx hx1 hA

theorem hgdMTt_g (k : ℕ) : (hgdMU St A S0 (hgdMTt A k)).g (hgdMTt A k) < x :=
  (max_lt_iff.1 ((hgdMU_γ_iff hSt hS (hgdMTt_lt A k) hx hx1).1 (hgdMTt_gate A hSt hS k x hx hx1 hA))).2

/-- **`r_{k+1}(x) = ϑˣ(Ω₁·2 + F(x) + r_k(x))`**: the code `t_{k+1} = Q_{t_k}` is read as the base reading of the start
`t_k`. -/
theorem hgdMTr_succ (k : ℕ) :
    hgdMTr St A S0 (k + 1) x = glA α (A.Fr x + hgdMTr St A S0 k x) x := by
  set l := hgdMTt A k with hl
  have hlT : l < hcN α A.F := hgdMTt_lt A k
  have hl'T : hgdMTt A (k + 1) < hcN α A.F := hgdMTt_lt A (k + 1)
  have hsp := hgdMU_succ_spec hSt hS hlT
  have hl1 : l + 1 ≤ hgdMTt A (k + 1) := Order.add_one_le_of_lt (hgdMTt_lt_succ A k)
  have hl1T : l + 1 < hcN α A.F := hl1.trans_lt hl'T
  have hB : hgdMTt A (k + 1) = (hgdMU St A S0 l).B := (hgdMTt_B A hSt hS k).symm
  have hcB : hgdMTt A (k + 1) < (hgdMU St A S0 (l + 1)).B := by
    rw [hgdMU_B hSt hS hl1T, hB, hgdMU_B hSt hS hlT]; exact A.Q_lt_Q (lt_add_one l)
  have hg : max A.γ ((hgdMU St A S0 l).g l) < x := max_lt hA (hgdMTt_g hSt hS hx hx1 hA k)
  unfold hgdMTr
  rw [(hgdM_ext hSt hS hl1 hl'T).1 _ x hcB, hB, hgdMU_B hSt hS hlT]
  exact hsp.RF x hx hx1 hg

theorem hgdMTr_zero : hgdMTr St A S0 0 x = 0 := by unfold hgdMTr; exact (hgdMU St A S0 (hgdMTt A 0)).R_zero x

theorem hgdMTr_lt_N (k : ℕ) : hgdMTr St A S0 k x < hcN α (A.Fr x) :=
  A.lvR_lt_N _ (hgdMU_Zb hSt hS (hgdMTt_lt A k)) (hgdMU_self hSt hS (hgdMTt_lt A k)) hx hx1 hA
    (hgdMTt_g hSt hS hx hx1 hA k)

/-- **The iterates of `φ(α, ·)` from `hdNx α (F(x)) + 1` lie below the tower readings.** -/
theorem hgdMTr_iter (n : ℕ) :
    (veblen α)^[n] (hdNx α (A.Fr x) + 1) ≤ hgdMTr St A S0 (n + 2) x := by
  obtain ⟨i0, hi0⟩ := hdNx_LuP α (A.Fr x)
  have hstep : ∀ k : ℕ, hgdMTr St A S0 (k + 1) x = veblen α
      (i0 + hgdMTr St A S0 k x) := fun k => by
    rw [hgdMTr_succ hSt hS hx hx1 hA k, A.lvglAV hx hx1 hA hi0 (hgdMTr_lt_N hSt hS hx hx1 hA k)]
  have h1 : hgdMTr St A S0 1 x = hdNx α (A.Fr x) := by
    rw [hstep 0, hgdMTr_zero hSt hS hx hx1 hA, add_zero, hi0]
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply]
    refine Order.add_one_le_of_lt ?_
    rw [hstep 1, h1]
    refine (le_add_self : hdNx α (A.Fr x) ≤ i0 + hdNx α (A.Fr x)).trans_lt ?_
    have h2 := hgdMTr_lt_N hSt hS hx hx1 hA 2
    rw [hstep 1, h1] at h2
    exact hc_nofixG (by rw [hi0]; exact hdNx_gt _ _) le_self_add h2
  | succ n ih =>
    rw [Function.iterate_succ_apply', hstep (n + 2)]
    exact (isNormal_veblen α).monotone (ih.trans le_add_self)

/-- **The tower readings are cofinal in `N_α(F(x))`.** -/
theorem hgdMTr_cof {v : Ordinal.{0}} (hv : v < hcN α (A.Fr x)) : ∃ k : ℕ, v < hgdMTr St A S0 k x := by
  have e : hcN α (A.Fr x) = nfp (veblen α) (hdNx α (A.Fr x) + 1) := by
    refine le_antisymm ?_ ?_
    · exact hcN_le (nfp_fp (isNormal_veblen _) _)
        ((hdNx_gt α (A.Fr x)).trans ((lt_add_one _).trans_le (le_nfp _ _)))
    · exact nfp_le_fp (isNormal_veblen α).strictMono.monotone
        (Order.add_one_le_of_lt (hdNx_lt_N (hcN_gt α (A.Fr x)))) (hcN_fix α _).le
  rw [e] at hv
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hv
  exact ⟨n + 2, hn.trans_le (hgdMTr_iter hSt hS hx hx1 hA n)⟩

end TowerRead

/-! ## The union of all offsets -/

section Union

variable {α : Ordinal.{0}} (St : ∀ (Q : HgdQ α) (U : HgVD), HgSStart (hgdQPB Q) U → HgVD) (A : HgdB α) (S0 : HgVD)

/-- The first start containing `c`. -/
noncomputable def hgdMTN (c : Ordinal.{0}) : Ordinal.{0} := sInf {ν | ν < hcN α A.F ∧ c < (hgdMU St A S0 ν).B}

/-- The reading of the union. -/
noncomputable def hgdMTR (c x : Ordinal.{0}) : Ordinal.{0} := (hgdMU St A S0 (hgdMTN St A S0 c)).R c x

/-- The gate of the union. -/
noncomputable def hgdMTg (c : Ordinal.{0}) : Ordinal.{0} := (hgdMU St A S0 (hgdMTN St A S0 c)).g c

open Classical in
/-- The bound field of the union: `evZ(N_α(F(x)))` above `γ`, `Z_o(x)` below. -/
noncomputable def hgdMTZ (x : Ordinal.{0}) : Ordinal.{0} :=
  if A.γ < x then evZ (hcN α (A.Fr x)) else A.Zo x

variable {St A S0} (hSt : ∀ Q U h, HgdQSpec Q U (St Q U h)) (hS : HgdMStart A S0)
include hSt hS

theorem hgdMT_cof {c : Ordinal.{0}} (hc : c < hcN α A.F) : ∃ ν, ν < hcN α A.F ∧ c <
    (hgdMU St A S0 ν).B := by
  obtain ⟨k, hk⟩ := hgdMTt_cof A hc
  exact ⟨hgdMTt A k, hgdMTt_lt A k, hk.trans (by rw [hgdMTt_B A hSt hS k]; exact hgdMTt_lt_succ A k)⟩

omit hSt hS in
theorem hgdMTN_spec {c ν : Ordinal.{0}} (hν : ν < hcN α A.F) (hc : c < (hgdMU St A S0 ν).B) :
    hgdMTN St A S0 c ≤ ν ∧ hgdMTN St A S0 c < hcN α A.F ∧ c < (hgdMU St A S0 (hgdMTN St A S0 c)).B := by
  have hne : ({ν | ν < hcN α A.F ∧ c < (hgdMU St A S0 ν).B} : Set Ordinal.{0}).Nonempty := ⟨ν, hν, hc⟩
  have hm := csInf_mem hne
  exact ⟨csInf_le' ⟨hν, hc⟩, hm.1, hm.2⟩

omit hSt hS in
theorem hgdMTN_min {c μ : Ordinal.{0}} (hμ : μ < hgdMTN St A S0 c) (hμl : μ < hcN α A.F) : ¬ c <
    (hgdMU St A S0 μ).B :=
  fun hcμ => absurd (csInf_le' ⟨hμl, hcμ⟩ : hgdMTN St A S0 c ≤ μ) (not_le.2 hμ)

theorem hgdMT_B_lt {ν : Ordinal.{0}} (hν : ν < hcN α A.F) : (hgdMU St A S0 ν).B < hcN α A.F := by
  rw [hgdMU_B hSt hS hν]; exact A.Q_lt_N hν

theorem hgdMTN_high {c : Ordinal.{0}} (hc : hcN α A.F ≤ c) : hgdMTN St A S0 c = 0 := by
  unfold hgdMTN
  have he : ({ν | ν < hcN α A.F ∧ c < (hgdMU St A S0 ν).B} : Set Ordinal.{0}) = ∅ := by
    ext ν
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hν hcν
    exact absurd (hcν.trans (hgdMT_B_lt hSt hS hν)) (not_lt.2 hc)
  rw [he]; exact Ordinal.sInf_empty

theorem hgdMTR_eq {c ν : Ordinal.{0}} (hν : ν < hcN α A.F) (hc : c < (hgdMU St A S0 ν).B) (x : Ordinal.{0}) :
    hgdMTR St A S0 c x = (hgdMU St A S0 ν).R c x := by
  obtain ⟨h1, -, h3⟩ := hgdMTN_spec hν hc
  exact ((hgdM_ext hSt hS h1 hν).1 c x h3).symm

theorem hgdMTg_eq {c ν : Ordinal.{0}} (hν : ν < hcN α A.F) (hc : c < (hgdMU St A S0 ν).B) :
    hgdMTg St A S0 c = (hgdMU St A S0 ν).g c := by
  obtain ⟨h1, -, h3⟩ := hgdMTN_spec hν hc
  exact ((hgdM_ext hSt hS h1 hν).2 c h3).symm

theorem hgdMTR_succ (c x : Ordinal.{0}) : hgdMTR St A S0 (c + 1) x = hgdMTR St A S0 c x + 1 := by
  rcases lt_or_ge c (hcN α A.F) with h | h
  · obtain ⟨n, hn1, hn⟩ := hgdMT_cof hSt hS (A.N_lim.add_one_lt h)
    rw [hgdMTR_eq hSt hS hn1 hn, hgdMTR_eq hSt hS hn1 ((lt_add_one c).trans hn), (hgdMU St A S0 n).R_succ]
  · unfold hgdMTR
    rw [hgdMTN_high hSt hS h, hgdMTN_high hSt hS (h.trans (le_self_add (a := c) (b := 1))), (hgdMU St A S0 0).R_succ]

theorem hgdMTg_le_succ (c : Ordinal.{0}) : hgdMTg St A S0 c ≤ hgdMTg St A S0 (c + 1) := by
  rcases lt_or_ge c (hcN α A.F) with h | h
  · obtain ⟨n, hn1, hn⟩ := hgdMT_cof hSt hS (A.N_lim.add_one_lt h)
    rw [hgdMTg_eq hSt hS hn1 hn, hgdMTg_eq hSt hS hn1 ((lt_add_one c).trans hn)]; exact (hgdMU St A S0 n).g_le_succ c
  · unfold hgdMTg
    rw [hgdMTN_high hSt hS h, hgdMTN_high hSt hS (h.trans (le_self_add (a := c) (b := 1)))]; exact
        (hgdMU St A S0 0).g_le_succ c

/-- **A code of the union with gate below a base `σ > γ_F` lies in a start with base gate below `σ`.** -/
theorem hgdMT_small {c σ : Ordinal.{0}} (hc : c < hcN α A.F) (hσ : InE σ) (hσ1 : σ < Om1) (hAσ : A.γ < σ)
    (hg : hgdMTg St A S0 c < σ) : ∃ μ, μ < hcN α A.F ∧ c < (hgdMU St A S0 μ).B ∧ (hgdMU St A S0 μ).γ < σ := by
  obtain ⟨n, hn1, hn⟩ := hgdMT_cof hSt hS hc
  obtain ⟨-, hN1, hcNc⟩ := hgdMTN_spec hn1 hn
  have hgN : hgdMTg St A S0 c = (hgdMU St A S0 (hgdMTN St A S0 c)).g c := rfl
  have I := hgdM_inv hSt hS _ hN1
  rcases zero_or_succ_or_isSuccLimit (hgdMTN St A S0 c) with h0 | ⟨m, hm⟩ | hlim
  · refine ⟨hgdMTN St A S0 c, hN1, hcNc, ?_⟩
    rw [h0, hgdMU_γ_iff hSt hS (hgdM_zero_lt_N A) hσ hσ1, (hgdMU St A S0 0).g_zero, max_eq_left zero_le]
    exact hAσ
  · have hm' : hgdMTN St A S0 c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < hgdMTN St A S0 c := by rw [hm']; exact lt_add_one m
    have hml : m < hcN α A.F := hmN.trans hN1
    have hBc : (hgdMU St A S0 m).B ≤ c := not_lt.1 (hgdMTN_min hmN hml)
    refine ⟨hgdMTN St A S0 c, hN1, hcNc, ?_⟩
    rw [hgN, hm'] at hg
    rw [hm'] at hcNc I ⊢
    exact I.high m (lt_add_one _) c σ hBc hcNc hσ hσ1 hg
  · exfalso
    rw [hgdMU_B hSt hS hN1] at hcNc
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen α).lt_iff_exists_lt
        (isSuccLimit_add _ hlim)).1 hcNc
    obtain ⟨d, hd, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    have hdl : d < hcN α A.F := hd.trans hN1
    refine hgdMTN_min hd hdl ?_
    rw [hgdMU_B hSt hS hdl]; exact hct.trans_le ((isNormal_veblen α).monotone htd)

/-- **A code `c ∈ [F, N(F))` of the union with gate below a base `σ` forces `γ_F < σ`.** -/
theorem hgdMT_high {c σ : Ordinal.{0}} (hc : c < hcN α A.F) (hFc : A.F ≤ c) (hσ : InE σ) (hσ1 : σ < Om1)
    (hg : hgdMTg St A S0 c < σ) : A.γ < σ := by
  obtain ⟨n, hn1, hn⟩ := hgdMT_cof hSt hS hc
  obtain ⟨-, hN1, hcNc⟩ := hgdMTN_spec hn1 hn
  have hgN : hgdMTg St A S0 c = (hgdMU St A S0 (hgdMTN St A S0 c)).g c := rfl
  have I := hgdM_inv hSt hS _ hN1
  rcases zero_or_succ_or_isSuccLimit (hgdMTN St A S0 c) with h0 | ⟨m, hm⟩ | hlim
  · rw [hgN, h0, hgdMU_zero] at hg
    rw [h0, hgdMU_zero] at hcNc
    exact hS.high0 c σ hFc hcNc hσ hσ1 hg
  · have hm' : hgdMTN St A S0 c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < hgdMTN St A S0 c := by rw [hm']; exact lt_add_one m
    have hml : m < hcN α A.F := hmN.trans hN1
    have hBc : (hgdMU St A S0 m).B ≤ c := not_lt.1 (hgdMTN_min hmN hml)
    rw [hgN, hm'] at hg
    rw [hm'] at hcNc I hN1
    have hγ := I.high m (lt_add_one _) c σ hBc hcNc hσ hσ1 hg
    exact (max_lt_iff.1 ((hgdMU_γ_iff hSt hS hN1 hσ hσ1).1 hγ)).1
  · exfalso
    rw [hgdMU_B hSt hS hN1] at hcNc
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen α).lt_iff_exists_lt
        (isSuccLimit_add _ hlim)).1 hcNc
    obtain ⟨d, hd, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    have hdl : d < hcN α A.F := hd.trans hN1
    refine hgdMTN_min hd hdl ?_
    rw [hgdMU_B hSt hS hdl]; exact hct.trans_le ((isNormal_veblen α).monotone htd)

/-- **`b_μ(x) < N(F(x))`** for every start with base gate below `x`. -/
theorem hgdMT_b_lt {μ x : Ordinal.{0}} (hμ : μ < hcN α A.F) (hx : InE x) (hx1 : x < Om1) (hγ :
    (hgdMU St A S0 μ).γ < x) :
    (hgdMU St A S0 μ).b x < hcN α (A.Fr x) := by
  have hg : max A.γ ((hgdMU St A S0 μ).g μ) < x := (hgdMU_γ_iff hSt hS hμ hx hx1).1 hγ
  have hA : A.γ < x := (max_lt_iff.1 hg).1
  rw [(hgdMU_start hSt hS hμ).b x hx hx1 hg]
  exact A.glA_lt_N hx hx1 hA (A.lvR_lt_N _ (hgdMU_Zb hSt hS hμ) (hgdMU_self hSt hS hμ) hx hx1 hA (max_lt_iff.1 hg).2)

omit hSt hS in
theorem hgdMTZ_fix (x : Ordinal.{0}) : veblen 1 (hgdMTZ A x) = hgdMTZ A x := by
  unfold hgdMTZ; split_ifs
  · exact epsilon_evZ _
  · exact ha_fix1_of_fix2 (A.Zo_fix x)

omit hSt hS in
theorem hgdMTZ_G1 (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : hgdMTZ A x < gq 1 x := by
  unfold hgdMTZ; split_ifs with h
  · exact (hb_evZ_lt_fix2 (A.Zo_fix x) (A.N_Zo hx hx1 h)).trans (A.Zo_G1 x hx hx1)
  · exact A.Zo_G1 x hx hx1

omit hSt hS in
theorem hgdMTZ_ge (x : Ordinal.{0}) : A.Zl x ≤ hgdMTZ A x := by
  unfold hgdMTZ HgdB.Zl; split_ifs
  · exact (lt_evZ _).le
  · exact le_rfl

/-- **THE SYSTEM AT `N(F)`**: the union of all starts `hgdMU St A S0 λ`, `λ < N(F)`: bound `N(F)`, base gate `γ_F`, base
reading `N(F(x))`, bound field `hgdMTZ`. -/
noncomputable def hgdMTU : HgVD where
  B := hcN α A.F
  γ := A.γ
  γ_lt := A.γ_lt
  γ_cl := fun Z hZ hZ1 h => A.N_cl Z hZ hZ1 h
  γ_G := fun h => absurd h (A.G_le.trans_lt A.F_lt_N).ne'
  R := hgdMTR St A S0
  g := hgdMTg St A S0
  b := fun x => hcN α (A.Fr x)
  ba := fun x => hcN α (A.Fr x)
  ix := hcN α A.F
  Z := hgdMTZ A
  B_E := A.N_E
  G_le := (A.G_le.trans_lt A.F_lt_N).le
  B_lt1 := A.N_lt1
  B_ix := (hc_fix_down A.lv.one_le (hcN_fix α A.F)).symm
  Z_fix := fun x _ _ => hgdMTZ_fix x
  Z_G1 := hgdMTZ_G1
  ix_mem := fun S _ _ ha hb => A.N_mem S ha hb
  g_lt := fun c hc => by
    obtain ⟨n, hn1, hn⟩ := hgdMT_cof hSt hS hc
    rw [hgdMTg_eq hSt hS hn1 hn]; exact (hgdMU St A S0 n).g_lt c hn
  g_zero := by
    rw [hgdMTg_eq hSt hS (hgdM_zero_lt_N A) (hgdMU St A S0 0).B_pos]; exact (hgdMU St A S0 0).g_zero
  g_nat := fun k => by
    rw [hgdMTg_eq hSt hS (hgdM_zero_lt_N A) ((hgdMU St A S0 0).nat_lt_B k)]; exact (hgdMU St A S0 0).g_nat k
  g_E := by rw [hgdMTg_eq hSt hS (hgdM_zero_lt_N A) (hgdMU St A S0 0).E_lt_B]; exact (hgdMU St A S0 0).g_E
  g_lowE := fun c hc => by
    rw [hgdMTg_eq hSt hS (hgdM_zero_lt_N A) (hc.trans (hgdMU St A S0 0).E_lt_B)]; exact (hgdMU St A S0 0).g_lowE c hc
  g_G0 := fun h => by
    obtain ⟨n, hn1, hn⟩ := hgdMT_cof hSt hS h
    rw [hgdMTg_eq hSt hS hn1 hn]; exact (hgdMU St A S0 n).g_G0 hn
  g_add := fun Z hZ hωZ x y hxy hgx hgy => by
    obtain ⟨n, hn1, hn⟩ := hgdMT_cof hSt hS hxy
    have hx : x < (hgdMU St A S0 n).B := lt_of_le_of_lt le_self_add hn
    have hy : y < (hgdMU St A S0 n).B := lt_of_le_of_lt le_add_self hn
    rw [hgdMTg_eq hSt hS hn1 hn]; rw [hgdMTg_eq hSt hS hn1 hx] at hgx; rw [hgdMTg_eq hSt hS hn1 hy] at hgy
    exact (hgdMU St A S0 n).g_add Z hZ hωZ x y hn hgx hgy
  g_opow := fun Z hZw hωZ y hy hg => by
    obtain ⟨n, hn1, hn⟩ := hgdMT_cof hSt hS hy
    have hy' : y < (hgdMU St A S0 n).B := lt_of_le_of_lt (right_le_opow y one_lt_omega0) hn
    rw [hgdMTg_eq hSt hS hn1 hn]; rw [hgdMTg_eq hSt hS hn1 hy'] at hg
    exact (hgdMU St A S0 n).g_opow Z hZw hωZ y hn hg
  code_gate := fun Z hZ1 hZ0 hZa hZp At hAt c hc hcB => by
    obtain ⟨n, hn1, hn⟩ := hgdMT_cof hSt hS hcB
    rw [hgdMTg_eq hSt hS hn1 hn]
    exact (hgdMU St A S0 n).code_gate Z hZ1 hZ0 hZa hZp At (fun s hs => (hAt s hs).imp_right
      (fun h => (hgdMT_B_lt hSt hS hn1).le.trans h)) c hc hn
  g_succ := fun Z hZ c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hgdMT_cof hSt hS hc
    have hc' : c < (hgdMU St A S0 n).B := (lt_add_one c).trans hn
    rw [hgdMTg_eq hSt hS hn1 hn]; rw [hgdMTg_eq hSt hS hn1 hc'] at hg
    exact (hgdMU St A S0 n).g_succ Z hZ c hn hg
  g_le_succ := hgdMTg_le_succ hSt hS
  mem := fun S a b ha c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hgdMT_cof hSt hS hc
    rw [hgdMTg_eq hSt hS hn1 hn] at hg
    exact (hgdMU St A S0 n).mem S a b ha c hn hg
  R_zero := fun x => by
    rw [hgdMTR_eq hSt hS (hgdM_zero_lt_N A) (hgdMU St A S0 0).B_pos]; exact (hgdMU St A S0 0).R_zero x
  R_nat := fun k x => by
    rw [hgdMTR_eq hSt hS (hgdM_zero_lt_N A) ((hgdMU St A S0 0).nat_lt_B k)]; exact (hgdMU St A S0 0).R_nat k x
  R_E := fun x => by rw [hgdMTR_eq hSt hS (hgdM_zero_lt_N A) (hgdMU St A S0 0).E_lt_B]; exact (hgdMU St A S0 0).R_E x
  R_succ := hgdMTR_succ hSt hS
  R_pos := fun x hx hx1 c hc0 hc hg => by
    obtain ⟨n, hn1, hn⟩ := hgdMT_cof hSt hS hc
    rw [hgdMTR_eq hSt hS hn1 hn]; rw [hgdMTg_eq hSt hS hn1 hn] at hg
    exact (hgdMU St A S0 n).R_pos x hx hx1 c hc0 hn hg
  R_omega := fun x hx hx1 c hω hc hg => by
    obtain ⟨n, hn1, hn⟩ := hgdMT_cof hSt hS hc
    rw [hgdMTR_eq hSt hS hn1 hn]; rw [hgdMTg_eq hSt hS hn1 hn] at hg
    exact (hgdMU St A S0 n).R_omega x hx hx1 c hω hn hg
  R_lt_b := fun x hx hx1 hγx c hc hg => by
    obtain ⟨μ, hμ, hcμ, hγμ⟩ := hgdMT_small hSt hS hc hx hx1 hγx hg
    rw [hgdMTR_eq hSt hS hμ hcμ]; rw [hgdMTg_eq hSt hS hμ hcμ] at hg
    exact ((hgdMU St A S0 μ).R_lt_b x hx hx1 hγμ c hcμ hg).trans (hgdMT_b_lt hSt hS hμ hx hx1 hγμ)
  R_lt_Z := fun x hx hx1 c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hgdMT_cof hSt hS hc
    rw [hgdMTR_eq hSt hS hn1 hn]; rw [hgdMTg_eq hSt hS hn1 hn] at hg
    exact (((hgdMU St A S0 n).R_lt_Z x hx hx1 c hn hg).trans_le (hgdMU_Zb hSt hS hn1 x hx hx1)).trans_le (hgdMTZ_ge x)
  mono := fun x hx hx1 c hc d hdc hgc hgd => by
    obtain ⟨n, hn1, hn⟩ := hgdMT_cof hSt hS hc
    have hd : d < (hgdMU St A S0 n).B := hdc.trans hn
    rw [hgdMTR_eq hSt hS hn1 hn,
        hgdMTR_eq hSt hS hn1 hd]; rw [hgdMTg_eq hSt hS hn1 hn] at hgc; rw [hgdMTg_eq hSt hS hn1 hd] at hgd
    exact (hgdMU St A S0 n).mono x hx hx1 c hn d hdc hgc hgd
  cof := fun x hx hx1 c hc hg ν hν => by
    obtain ⟨n, hn1, hn⟩ := hgdMT_cof hSt hS hc
    rw [hgdMTR_eq hSt hS hn1 hn] at hν; rw [hgdMTg_eq hSt hS hn1 hn] at hg
    obtain ⟨d, hdc, hgd, hνd⟩ := (hgdMU St A S0 n).cof x hx hx1 c hn hg ν hν
    have hd : d < (hgdMU St A S0 n).B := hdc.trans hn
    exact ⟨d, hdc, by rw [hgdMTg_eq hSt hS hn1 hd]; exact hgd, by rw [hgdMTR_eq hSt hS hn1 hd]; exact hνd⟩
  b_cof := fun x hx hx1 hγx ν hν => by
    obtain ⟨k, hk⟩ := hgdMTr_cof hSt hS hx hx1 hγx hν
    have hkT : hgdMTt A k < hcN α A.F := hgdMTt_lt A k
    have hkB : hgdMTt A k < (hgdMU St A S0 (hgdMTt A k)).B := hgdMU_self hSt hS hkT
    refine ⟨hgdMTt A k, hkT, ?_, ?_⟩
    · rw [hgdMTg_eq hSt hS hkT hkB]; exact hgdMTt_g hSt hS hx hx1 hγx k
    · rw [hgdMTR_eq hSt hS hkT hkB]; exact hk
  b_E := fun x _ _ _ => hcN_E α _
  x_lt_b := fun x hx hx1 hγx => (A.Fr_gt hx hx1 hγx).trans (A.Fr_lt_N x)
  b_eN := fun x hx hx1 hγx => gz_eN_fix hx hx1 (hc_fix_down A.lv.one_le (hcN_fix α _))
    ((A.Fr_gt hx hx1 hγx).trans (A.Fr_lt_N x)) (A.N_lt1x hx hx1 hγx)
  ba_lt := fun x hx hx1 hγx => A.N_lt1x hx hx1 hγx
  b_Z := fun x _ _ hγx => by
    show _ < hgdMTZ A x
    unfold hgdMTZ; rw [if_pos hγx]
    exact go_eN_lt_evZ (lt_evZ _)
  b_pi := fun _ _ hB hγ => A.N_pi hB hγ
  ba_pi := fun _ _ hB hγ => A.N_pi hB hγ
  ex := fun σ ρ hB c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hgdMT_cof hSt hS hc
    rw [hgdMTR_eq hSt hS hn1 hn, hgdMTR_eq hSt hS hn1 hn]; rw [hgdMTg_eq hSt hS hn1 hn] at hg
    exact (hgdMU St A S0 n).ex σ ρ hB c hn hg
  dig := fun σ ρ hB hγσ d hd hg P P' hat => by
    obtain ⟨μ, hμ, hdμ, hγμ⟩ := hgdMT_small hSt hS hd hB.1 (hB.2.2.1.trans hB.2.2.2) hγσ hg
    rw [hgdMTR_eq hSt hS hμ hdμ, hgdMTR_eq hSt hS hμ hdμ]; rw [hgdMTg_eq hSt hS hμ hdμ] at hg
    exact (hgdMU St A S0 μ).dig σ ρ hB hγμ d hdμ hg P P' (fun β hβ hβe =>
      hat β hβ (hβe.trans (hgdMT_b_lt hSt hS hμ hB.2.1 hB.2.2.2 (hγμ.trans hB.2.2.1))))
  ld := fun c hl hc => by
    obtain ⟨n, hn1, hn⟩ := hgdMT_cof hSt hS hc
    obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := (hgdMU St A S0 n).ld c hl hn
    have hcpn : cp < (hgdMU St A S0 n).B := hcp.trans hn
    refine ⟨cp, lp, T, hcp, by rw [hgdMTg_eq hSt hS hn1 hn, hgdMTg_eq hSt hS hn1 hcpn]; exact hgcp,
        fun x hx hx1 hg => ?_,
      fun σ ρ hB hg => hex σ ρ hB (by rw [← hgdMTg_eq hSt hS hn1 hn]; exact hg)⟩
    rw [hgdMTg_eq hSt hS hn1 hn] at hg
    rw [hgdMTR_eq hSt hS hn1 hn, hgdMTR_eq hSt hS hn1 hcpn]
    exact hdec x hx hx1 hg

theorem hgdMTU_B : (hgdMTU hSt hS).B = hcN α A.F := rfl

theorem hgdMTU_γ : (hgdMTU hSt hS).γ = A.γ := rfl

theorem hgdMTU_b (x : Ordinal.{0}) : (hgdMTU hSt hS).b x = hcN α (A.Fr x) := rfl

/-- **The union extends every start** (readings). -/
theorem hgdMTU_R {ν c : Ordinal.{0}} (hν : ν < hcN α A.F) (hc : c < (hgdMU St A S0 ν).B) (x : Ordinal.{0}) :
    (hgdMTU hSt hS).R c x = (hgdMU St A S0 ν).R c x := hgdMTR_eq hSt hS hν hc x

/-- **The union extends every start** (gates). -/
theorem hgdMTU_g {ν c : Ordinal.{0}} (hν : ν < hcN α A.F) (hc : c < (hgdMU St A S0 ν).B) :
    (hgdMTU hSt hS).g c = (hgdMU St A S0 ν).g c := hgdMTg_eq hSt hS hν hc

/-- **The union extends the start `S0`.** -/
theorem hgdMTU_R0 {c : Ordinal.{0}} (hc : c < S0.B) (x : Ordinal.{0}) : (hgdMTU hSt hS).R c x = S0.R c x := by
  rw [hgdMTU_R hSt hS (hgdM_zero_lt_N A) (by rw [hgdMU_zero]; exact hc), hgdMU_zero]

theorem hgdMTU_g0 {c : Ordinal.{0}} (hc : c < S0.B) : (hgdMTU hSt hS).g c = S0.g c := by
  rw [hgdMTU_g hSt hS (hgdM_zero_lt_N A) (by rw [hgdMU_zero]; exact hc), hgdMU_zero]

/-- **A code `c ∈ [F, N(F))` of the union with gate below a base `σ` forces the base gate below `σ`.** -/
theorem hgdMTU_high {c σ : Ordinal.{0}} (hc : c < hcN α A.F) (hFc : A.F ≤ c) (hσ : InE σ) (hσ1 : σ < Om1)
    (hg : (hgdMTU hSt hS).g c < σ) : (hgdMTU hSt hS).γ < σ := hgdMT_high hSt hS hc hFc hσ hσ1 hg

end Union

end Googology.Trans.PoR.InaccPsi.R2.Hg

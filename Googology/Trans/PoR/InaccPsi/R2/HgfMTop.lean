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
import Googology.Trans.PoR.InaccPsi.R2.HgdMTop
import Googology.Trans.PoR.InaccPsi.R2.HgdMSc
import Googology.Trans.PoR.InaccPsi.R2.HgdMRecL
import Googology.Trans.PoR.InaccPsi.R2.HgfM
import Googology.Trans.PoR.InaccPsi.R2.HgfMLv
import Googology.Trans.PoR.InaccPsi.R2.HgfMRec

/-!
# HgfMTop: THE UNION OF ALL OFFSETS OF A BASE OF EVERY COUNTABLE LEVEL `α`: THE TOWER TO `N_α(F) = φ(α+1, F+1)`

(Textual copy of `Hf.HfMTop` for `Hg.HgVD`: bound fields `< Γ_{x+2}` in place of `≤ B_x(x)` (`Hc.hcBR`); the proofs
are unchanged except where the bound enters.  Names: prefix `hg`/`Hg` (from `hc`/`Hc`), `hgd`/`Hgd` (from `hd`/`Hd`),
`hgf`/`Hgf` (from `hf`/`Hf`), `hge`/`Hge` (from `he`/`He`).)

The level-`α` version of `Hd.HdLvTop`, for any step `St` of level `α` with the specification.  For a base
`A : Hf.HgfB α` and a start `S0`, the union of all starts `Hg.hgfMU St A S0 λ`, `λ < N_α(F)`, is a system `hgfMTU` with
the bound `N_α(F)`, base gate `γN`, base reading `N_α(F(x))`, bound field `evZ(N_α(F(x)))` above `γN` and `Z_o(x)`
below; the tower `t_0 = 0`, `t_{k+1} = φ(α, F + 1 + t_k)` is cofinal in `N_α(F)` and its readings are cofinal in
`N_α(F(x))`; the union extends the start, reads it, and a code in `[F, N(F))` with gate below `σ` forces the CODE
gate `γ` below `σ` (`hgfMT_high`); when the two gates agree (`γN = γ`, every base `Hg.HgfQ.toB`), the base gate `γN`
of the union (`hgfMTU_high`).

* `hgfMTt`, `hgfMTt_cof`, `hgfMTt_gate`, `hgfMTr`, `hgfMTr_succ`, `hgfMTr_cof`; `hgfMTN`, `hgfMTR`, `hgfMTg`, `hgfMTZ`,
  `hgfMT_small`, `hgfMT_high`, `hgfMTU` (**THE SYSTEM AT `N_α(F)`, EVERY COUNTABLE LEVEL**), `hgfMTU_R0`, `hgfMTU_g0`,
  `hgfMTU_high`.

No new axiom.  New definitions: `hgfMTt`, `hgfMTr`, `hgfMTN`, `hgfMTR`, `hgfMTg`, `hgfMTZ`, `hgfMTU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hg

open Googology.Trans.PoR.InaccPsi.R2.Hc
open Googology.Trans.PoR.InaccPsi.R2.Hd
open Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hf

open Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He

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

variable {α : Ordinal.{0}} (A : HgfB α)

/-- **The tower of offsets**: `t_0 = 0`, `t_{k+1} = φ(2, F + 1 + t_k)`. -/
noncomputable def hgfMTt : ℕ → Ordinal.{0}
  | 0 => 0
  | k + 1 => veblen α (A.F + 1 + hgfMTt k)

theorem hgfMTt_lt : ∀ k : ℕ, hgfMTt A k < hcN α A.F
  | 0 => hgfM_zero_lt_N A
  | k + 1 => A.Q_lt_N (hgfMTt_lt k)

theorem hgfMTt_lt_succ (k : ℕ) : hgfMTt A k < hgfMTt A (k + 1) := A.lt_Q (hgfMTt_lt A k)

theorem hgfMTt_iter (n : ℕ) : (veblen α)^[n] (A.F + 1) ≤ hgfMTt A (n + 1) := by
  induction n with
  | zero =>
    show A.F + 1 ≤ veblen α (A.F + 1 + 0)
    rw [add_zero]; exact right_le_veblen α _
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    show veblen α _ ≤ veblen α (A.F + 1 + hgfMTt A (n + 1))
    exact (isNormal_veblen α).monotone (ih.trans le_add_self)

theorem hgfM_N_nfp : hcN α A.F = nfp (veblen α) (A.F + 1) := rfl

/-- **The tower is cofinal in `N(F)`.** -/
theorem hgfMTt_cof {c : Ordinal.{0}} (hc : c < hcN α A.F) : ∃ k : ℕ, c < hgfMTt A k := by
  rw [hgfM_N_nfp] at hc
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hc
  exact ⟨n + 1, hn.trans_le (hgfMTt_iter A n)⟩

variable {St : ∀ (Q : HgfQ α) (U : HgVD), HgSStart (hgfQPB Q) U → HgVD} {S0 : HgVD}
  (hSt : ∀ Q U h, HgfQSpec Q U (St Q U h)) (hS : HgfMStart A S0)
include hSt hS

theorem hgfMTt_B (k : ℕ) : (hgfMU St A S0 (hgfMTt A k)).B = hgfMTt A (k + 1) := hgfMU_B hSt hS (hgfMTt_lt A k)

/-- **Every start `hgfMU St A S0 t_k` has base gate below every base above `γN`.** -/
theorem hgfMTt_gate : ∀ (k : ℕ) (x : Ordinal.{0}), InE x → x < Om1 → A.γN < x → (hgfMU St A S0 (hgfMTt A k)).γ < x
  | 0, x, hx, hx1, hA => by
    show (hgfMU St A S0 0).γ < x
    rw [hgfMU_γ_iff hSt hS (hgfM_zero_lt_N A) hx hx1, (hgfMU St A S0 0).g_zero, max_eq_left zero_le]; exact hA
  | k + 1, x, hx, hx1, hA => by
    set l := hgfMTt A k with hl
    have hlT : l < hcN α A.F := hgfMTt_lt A k
    have hl'T : hgfMTt A (k + 1) < hcN α A.F := hgfMTt_lt A (k + 1)
    have hsp := hgfMU_succ_spec hSt hS hlT
    have hl1 : l + 1 ≤ hgfMTt A (k + 1) := Order.add_one_le_of_lt (hgfMTt_lt_succ A k)
    have hl1T : l + 1 < hcN α A.F := hl1.trans_lt hl'T
    have hB : hgfMTt A (k + 1) = (hgfMU St A S0 l).B := (hgfMTt_B A hSt hS k).symm
    have hcB : hgfMTt A (k + 1) < (hgfMU St A S0 (l + 1)).B := by
      rw [hgfMU_B hSt hS hl1T, hB, hgfMU_B hSt hS hlT]; exact A.Q_lt_Q (lt_add_one l)
    rw [hgfMU_γ_iff hSt hS hl'T hx hx1, (hgfM_ext hSt hS hl1 hl'T).2 _ hcB, hB, hgfMU_B hSt hS hlT]
    refine max_lt hA ((hsp.gF x hx hx1).2 ?_)
    exact max_lt hA ((max_lt_iff.1 ((hgfMU_γ_iff hSt hS hlT hx hx1).1 (hgfMTt_gate k x hx hx1 hA))).2)

end Tower

/-- The reading of the tower code `t_k` (in its start). -/
noncomputable def hgfMTr {α : Ordinal.{0}} (St : ∀ (Q : HgfQ α) (U : HgVD), HgSStart (hgfQPB Q) U → HgVD) (A : HgfB α)
    (S0 : HgVD) (k : ℕ)
    (x : Ordinal.{0}) : Ordinal.{0} := (hgfMU St A S0 (hgfMTt A k)).R (hgfMTt A k) x

section TowerRead

variable {α : Ordinal.{0}} {St : ∀ (Q : HgfQ α) (U : HgVD), HgSStart (hgfQPB Q) U → HgVD}
  (hSt : ∀ Q U h, HgfQSpec Q U (St Q U h))
  {A : HgfB α} {S0 : HgVD} (hS : HgfMStart A S0) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hA : A.γN < x)
include hSt hS hx hx1 hA

theorem hgfMTt_g (k : ℕ) : (hgfMU St A S0 (hgfMTt A k)).g (hgfMTt A k) < x :=
  (max_lt_iff.1 ((hgfMU_γ_iff hSt hS (hgfMTt_lt A k) hx hx1).1 (hgfMTt_gate A hSt hS k x hx hx1 hA))).2

/-- **`r_{k+1}(x) = ϑˣ(Ω₁·2 + F(x) + r_k(x))`**: the code `t_{k+1} = Q_{t_k}` is read as the base reading of the start
`t_k`. -/
theorem hgfMTr_succ (k : ℕ) :
    hgfMTr St A S0 (k + 1) x = glA α (A.Fr x + hgfMTr St A S0 k x) x := by
  set l := hgfMTt A k with hl
  have hlT : l < hcN α A.F := hgfMTt_lt A k
  have hl'T : hgfMTt A (k + 1) < hcN α A.F := hgfMTt_lt A (k + 1)
  have hsp := hgfMU_succ_spec hSt hS hlT
  have hl1 : l + 1 ≤ hgfMTt A (k + 1) := Order.add_one_le_of_lt (hgfMTt_lt_succ A k)
  have hl1T : l + 1 < hcN α A.F := hl1.trans_lt hl'T
  have hB : hgfMTt A (k + 1) = (hgfMU St A S0 l).B := (hgfMTt_B A hSt hS k).symm
  have hcB : hgfMTt A (k + 1) < (hgfMU St A S0 (l + 1)).B := by
    rw [hgfMU_B hSt hS hl1T, hB, hgfMU_B hSt hS hlT]; exact A.Q_lt_Q (lt_add_one l)
  have hg : max A.γN ((hgfMU St A S0 l).g l) < x := max_lt hA (hgfMTt_g hSt hS hx hx1 hA k)
  unfold hgfMTr
  rw [(hgfM_ext hSt hS hl1 hl'T).1 _ x hcB, hB, hgfMU_B hSt hS hlT]
  exact hsp.RF x hx hx1 hg

theorem hgfMTr_zero : hgfMTr St A S0 0 x = 0 := by unfold hgfMTr; exact (hgfMU St A S0 (hgfMTt A 0)).R_zero x

theorem hgfMTr_lt_N (k : ℕ) : hgfMTr St A S0 k x < hcN α (A.Fr x) :=
  A.lvR_lt_N _ (hgfMU_Zb hSt hS (hgfMTt_lt A k)) (hgfMU_self hSt hS (hgfMTt_lt A k)) hx hx1 hA
    (hgfMTt_g hSt hS hx hx1 hA k)

/-- **The iterates of `φ(α, ·)` from `hdNx α (F(x)) + 1` lie below the tower readings.** -/
theorem hgfMTr_iter (n : ℕ) :
    (veblen α)^[n] (hdNx α (A.Fr x) + 1) ≤ hgfMTr St A S0 (n + 2) x := by
  obtain ⟨i0, hi0⟩ := hdNx_LuP α (A.Fr x)
  have hstep : ∀ k : ℕ, hgfMTr St A S0 (k + 1) x = veblen α
      (i0 + hgfMTr St A S0 k x) := fun k => by
    rw [hgfMTr_succ hSt hS hx hx1 hA k, A.lvglAV hx hx1 hA hi0 (hgfMTr_lt_N hSt hS hx hx1 hA k)]
  have h1 : hgfMTr St A S0 1 x = hdNx α (A.Fr x) := by
    rw [hstep 0, hgfMTr_zero hSt hS hx hx1 hA, add_zero, hi0]
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply]
    refine Order.add_one_le_of_lt ?_
    rw [hstep 1, h1]
    refine (le_add_self : hdNx α (A.Fr x) ≤ i0 + hdNx α (A.Fr x)).trans_lt ?_
    have h2 := hgfMTr_lt_N hSt hS hx hx1 hA 2
    rw [hstep 1, h1] at h2
    exact hc_nofixG (by rw [hi0]; exact hdNx_gt _ _) le_self_add h2
  | succ n ih =>
    rw [Function.iterate_succ_apply', hstep (n + 2)]
    exact (isNormal_veblen α).monotone (ih.trans le_add_self)

/-- **The tower readings are cofinal in `N_α(F(x))`.** -/
theorem hgfMTr_cof {v : Ordinal.{0}} (hv : v < hcN α (A.Fr x)) : ∃ k : ℕ, v < hgfMTr St A S0 k x := by
  have e : hcN α (A.Fr x) = nfp (veblen α) (hdNx α (A.Fr x) + 1) := by
    refine le_antisymm ?_ ?_
    · exact hcN_le (nfp_fp (isNormal_veblen _) _)
        ((hdNx_gt α (A.Fr x)).trans ((lt_add_one _).trans_le (le_nfp _ _)))
    · exact nfp_le_fp (isNormal_veblen α).strictMono.monotone
        (Order.add_one_le_of_lt (hdNx_lt_N (hcN_gt α (A.Fr x)))) (hcN_fix α _).le
  rw [e] at hv
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hv
  exact ⟨n + 2, hn.trans_le (hgfMTr_iter hSt hS hx hx1 hA n)⟩

end TowerRead

/-! ## The union of all offsets -/

section Union

variable {α : Ordinal.{0}} (St : ∀ (Q : HgfQ α) (U : HgVD), HgSStart (hgfQPB Q) U → HgVD) (A : HgfB α) (S0 : HgVD)

/-- The first start containing `c`. -/
noncomputable def hgfMTN (c : Ordinal.{0}) : Ordinal.{0} := sInf {ν | ν < hcN α A.F ∧ c < (hgfMU St A S0 ν).B}

/-- The reading of the union. -/
noncomputable def hgfMTR (c x : Ordinal.{0}) : Ordinal.{0} := (hgfMU St A S0 (hgfMTN St A S0 c)).R c x

/-- The gate of the union. -/
noncomputable def hgfMTg (c : Ordinal.{0}) : Ordinal.{0} := (hgfMU St A S0 (hgfMTN St A S0 c)).g c

open Classical in
/-- The bound field of the union: `evZ(N_α(F(x)))` above `γ`, `Z_o(x)` below. -/
noncomputable def hgfMTZ (x : Ordinal.{0}) : Ordinal.{0} :=
  if A.γN < x then evZ (hcN α (A.Fr x)) else A.Zo x

variable {St A S0} (hSt : ∀ Q U h, HgfQSpec Q U (St Q U h)) (hS : HgfMStart A S0)
include hSt hS

theorem hgfMT_cof {c : Ordinal.{0}} (hc : c < hcN α A.F) : ∃ ν, ν < hcN α A.F ∧ c <
    (hgfMU St A S0 ν).B := by
  obtain ⟨k, hk⟩ := hgfMTt_cof A hc
  exact ⟨hgfMTt A k, hgfMTt_lt A k, hk.trans (by rw [hgfMTt_B A hSt hS k]; exact hgfMTt_lt_succ A k)⟩

omit hSt hS in
theorem hgfMTN_spec {c ν : Ordinal.{0}} (hν : ν < hcN α A.F) (hc : c < (hgfMU St A S0 ν).B) :
    hgfMTN St A S0 c ≤ ν ∧ hgfMTN St A S0 c < hcN α A.F ∧ c < (hgfMU St A S0 (hgfMTN St A S0 c)).B := by
  have hne : ({ν | ν < hcN α A.F ∧ c < (hgfMU St A S0 ν).B} : Set Ordinal.{0}).Nonempty := ⟨ν, hν, hc⟩
  have hm := csInf_mem hne
  exact ⟨csInf_le' ⟨hν, hc⟩, hm.1, hm.2⟩

omit hSt hS in
theorem hgfMTN_min {c μ : Ordinal.{0}} (hμ : μ < hgfMTN St A S0 c) (hμl : μ < hcN α A.F) : ¬ c <
    (hgfMU St A S0 μ).B :=
  fun hcμ => absurd (csInf_le' ⟨hμl, hcμ⟩ : hgfMTN St A S0 c ≤ μ) (not_le.2 hμ)

theorem hgfMT_B_lt {ν : Ordinal.{0}} (hν : ν < hcN α A.F) : (hgfMU St A S0 ν).B < hcN α A.F := by
  rw [hgfMU_B hSt hS hν]; exact A.Q_lt_N hν

theorem hgfMTN_high {c : Ordinal.{0}} (hc : hcN α A.F ≤ c) : hgfMTN St A S0 c = 0 := by
  unfold hgfMTN
  have he : ({ν | ν < hcN α A.F ∧ c < (hgfMU St A S0 ν).B} : Set Ordinal.{0}) = ∅ := by
    ext ν
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hν hcν
    exact absurd (hcν.trans (hgfMT_B_lt hSt hS hν)) (not_lt.2 hc)
  rw [he]; exact Ordinal.sInf_empty

theorem hgfMTR_eq {c ν : Ordinal.{0}} (hν : ν < hcN α A.F) (hc : c < (hgfMU St A S0 ν).B) (x : Ordinal.{0}) :
    hgfMTR St A S0 c x = (hgfMU St A S0 ν).R c x := by
  obtain ⟨h1, -, h3⟩ := hgfMTN_spec hν hc
  exact ((hgfM_ext hSt hS h1 hν).1 c x h3).symm

theorem hgfMTg_eq {c ν : Ordinal.{0}} (hν : ν < hcN α A.F) (hc : c < (hgfMU St A S0 ν).B) :
    hgfMTg St A S0 c = (hgfMU St A S0 ν).g c := by
  obtain ⟨h1, -, h3⟩ := hgfMTN_spec hν hc
  exact ((hgfM_ext hSt hS h1 hν).2 c h3).symm

theorem hgfMTR_succ (c x : Ordinal.{0}) : hgfMTR St A S0 (c + 1) x = hgfMTR St A S0 c x + 1 := by
  rcases lt_or_ge c (hcN α A.F) with h | h
  · obtain ⟨n, hn1, hn⟩ := hgfMT_cof hSt hS (A.N_lim.add_one_lt h)
    rw [hgfMTR_eq hSt hS hn1 hn, hgfMTR_eq hSt hS hn1 ((lt_add_one c).trans hn), (hgfMU St A S0 n).R_succ]
  · unfold hgfMTR
    rw [hgfMTN_high hSt hS h, hgfMTN_high hSt hS (h.trans (le_self_add (a := c) (b := 1))), (hgfMU St A S0 0).R_succ]

theorem hgfMTg_le_succ (c : Ordinal.{0}) : hgfMTg St A S0 c ≤ hgfMTg St A S0 (c + 1) := by
  rcases lt_or_ge c (hcN α A.F) with h | h
  · obtain ⟨n, hn1, hn⟩ := hgfMT_cof hSt hS (A.N_lim.add_one_lt h)
    rw [hgfMTg_eq hSt hS hn1 hn, hgfMTg_eq hSt hS hn1 ((lt_add_one c).trans hn)]; exact (hgfMU St A S0 n).g_le_succ c
  · unfold hgfMTg
    rw [hgfMTN_high hSt hS h, hgfMTN_high hSt hS (h.trans (le_self_add (a := c) (b := 1)))]; exact
        (hgfMU St A S0 0).g_le_succ c

/-- **A code of the union with gate below a base `σ > γ_F` lies in a start with base gate below `σ`.** -/
theorem hgfMT_small {c σ : Ordinal.{0}} (hc : c < hcN α A.F) (hσ : InE σ) (hσ1 : σ < Om1) (hAσ : A.γN < σ)
    (hg : hgfMTg St A S0 c < σ) : ∃ μ, μ < hcN α A.F ∧ c < (hgfMU St A S0 μ).B ∧ (hgfMU St A S0 μ).γ < σ := by
  obtain ⟨n, hn1, hn⟩ := hgfMT_cof hSt hS hc
  obtain ⟨-, hN1, hcNc⟩ := hgfMTN_spec hn1 hn
  have hgN : hgfMTg St A S0 c = (hgfMU St A S0 (hgfMTN St A S0 c)).g c := rfl
  have I := hgfM_inv hSt hS _ hN1
  rcases zero_or_succ_or_isSuccLimit (hgfMTN St A S0 c) with h0 | ⟨m, hm⟩ | hlim
  · refine ⟨hgfMTN St A S0 c, hN1, hcNc, ?_⟩
    rw [h0, hgfMU_γ_iff hSt hS (hgfM_zero_lt_N A) hσ hσ1, (hgfMU St A S0 0).g_zero, max_eq_left zero_le]
    exact hAσ
  · have hm' : hgfMTN St A S0 c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < hgfMTN St A S0 c := by rw [hm']; exact lt_add_one m
    have hml : m < hcN α A.F := hmN.trans hN1
    have hBc : (hgfMU St A S0 m).B ≤ c := not_lt.1 (hgfMTN_min hmN hml)
    refine ⟨hgfMTN St A S0 c, hN1, hcNc, ?_⟩
    rw [hgN, hm'] at hg
    rw [hm'] at hcNc I ⊢
    exact I.high m (lt_add_one _) c σ hBc hcNc hσ hσ1 hg
  · exfalso
    rw [hgfMU_B hSt hS hN1] at hcNc
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen α).lt_iff_exists_lt
        (isSuccLimit_add _ hlim)).1 hcNc
    obtain ⟨d, hf, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    have hfl : d < hcN α A.F := hf.trans hN1
    refine hgfMTN_min hf hfl ?_
    rw [hgfMU_B hSt hS hfl]; exact hct.trans_le ((isNormal_veblen α).monotone htd)

/-- **A code `c ∈ [F, N(F))` of the union with gate below a base `σ` forces `γ_F < σ`.** -/
theorem hgfMT_high {c σ : Ordinal.{0}} (hc : c < hcN α A.F) (hFc : A.F ≤ c) (hσ : InE σ) (hσ1 : σ < Om1)
    (hg : hgfMTg St A S0 c < σ) : A.γ < σ := by
  obtain ⟨n, hn1, hn⟩ := hgfMT_cof hSt hS hc
  obtain ⟨-, hN1, hcNc⟩ := hgfMTN_spec hn1 hn
  have hgN : hgfMTg St A S0 c = (hgfMU St A S0 (hgfMTN St A S0 c)).g c := rfl
  have I := hgfM_inv hSt hS _ hN1
  rcases zero_or_succ_or_isSuccLimit (hgfMTN St A S0 c) with h0 | ⟨m, hm⟩ | hlim
  · rw [hgN, h0, hgfMU_zero] at hg
    rw [h0, hgfMU_zero] at hcNc
    exact hS.high0 c σ hFc hcNc hσ hσ1 hg
  · have hm' : hgfMTN St A S0 c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < hgfMTN St A S0 c := by rw [hm']; exact lt_add_one m
    have hml : m < hcN α A.F := hmN.trans hN1
    have hBc : (hgfMU St A S0 m).B ≤ c := not_lt.1 (hgfMTN_min hmN hml)
    rw [hgN, hm'] at hg
    rw [hm'] at hcNc I hN1
    have hγ := I.high m (lt_add_one _) c σ hBc hcNc hσ hσ1 hg
    exact A.γ_le.trans_lt (max_lt_iff.1 ((hgfMU_γ_iff hSt hS hN1 hσ hσ1).1 hγ)).1
  · exfalso
    rw [hgfMU_B hSt hS hN1] at hcNc
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen α).lt_iff_exists_lt
        (isSuccLimit_add _ hlim)).1 hcNc
    obtain ⟨d, hf, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    have hfl : d < hcN α A.F := hf.trans hN1
    refine hgfMTN_min hf hfl ?_
    rw [hgfMU_B hSt hS hfl]; exact hct.trans_le ((isNormal_veblen α).monotone htd)

/-- **`b_μ(x) < N(F(x))`** for every start with base gate below `x`. -/
theorem hgfMT_b_lt {μ x : Ordinal.{0}} (hμ : μ < hcN α A.F) (hx : InE x) (hx1 : x < Om1) (hγ :
    (hgfMU St A S0 μ).γ < x) :
    (hgfMU St A S0 μ).b x < hcN α (A.Fr x) := by
  have hg : max A.γN ((hgfMU St A S0 μ).g μ) < x := (hgfMU_γ_iff hSt hS hμ hx hx1).1 hγ
  have hA : A.γN < x := (max_lt_iff.1 hg).1
  rw [(hgfMU_start hSt hS hμ).b x hx hx1 hg]
  exact A.glA_lt_N hx hx1 hA (A.lvR_lt_N _ (hgfMU_Zb hSt hS hμ) (hgfMU_self hSt hS hμ) hx hx1 hA (max_lt_iff.1 hg).2)

omit hSt hS in
theorem hgfMTZ_fix (x : Ordinal.{0}) : veblen 1 (hgfMTZ A x) = hgfMTZ A x := by
  unfold hgfMTZ; split_ifs
  · exact epsilon_evZ _
  · exact ha_fix1_of_fix2 (A.Zo_fix x)

omit hSt hS in
theorem hgfMTZ_G1 (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : hgfMTZ A x < gq 1 x := by
  unfold hgfMTZ; split_ifs with h
  · exact (hb_evZ_lt_fix2 (A.Zo_fix x) (A.N_Zo hx hx1 h)).trans (A.Zo_G1 x hx hx1)
  · exact A.Zo_G1 x hx hx1

omit hSt hS in
theorem hgfMTZ_ge (x : Ordinal.{0}) : A.Zl x ≤ hgfMTZ A x := by
  unfold hgfMTZ HgfB.Zl; split_ifs
  · exact (lt_evZ _).le
  · exact le_rfl

/-- **THE SYSTEM AT `N(F)`**: the union of all starts `hgfMU St A S0 λ`, `λ < N(F)`: bound `N(F)`, base gate `γN`, base
reading `N(F(x))`, bound field `hgfMTZ`. -/
noncomputable def hgfMTU : HgVD where
  B := hcN α A.F
  γ := A.γN
  γ_lt := A.γN_lt
  γ_cl := fun Z hZ hZ1 h => A.N_cl Z hZ hZ1 h
  γ_G := fun h => absurd h (A.G_le.trans_lt A.F_lt_N).ne'
  R := hgfMTR St A S0
  g := hgfMTg St A S0
  b := fun x => hcN α (A.Fr x)
  ba := fun x => hcN α (A.Fr x)
  ix := hcN α A.F
  Z := hgfMTZ A
  B_E := A.N_E
  G_le := (A.G_le.trans_lt A.F_lt_N).le
  B_lt1 := A.N_lt1
  B_ix := (hc_fix_down A.lv.one_le (hcN_fix α A.F)).symm
  Z_fix := fun x _ _ => hgfMTZ_fix x
  Z_G1 := hgfMTZ_G1
  ix_mem := fun S _ _ ha hb => A.N_mem S ha hb
  g_lt := fun c hc => by
    obtain ⟨n, hn1, hn⟩ := hgfMT_cof hSt hS hc
    rw [hgfMTg_eq hSt hS hn1 hn]; exact (hgfMU St A S0 n).g_lt c hn
  g_zero := by
    rw [hgfMTg_eq hSt hS (hgfM_zero_lt_N A) (hgfMU St A S0 0).B_pos]; exact (hgfMU St A S0 0).g_zero
  g_nat := fun k => by
    rw [hgfMTg_eq hSt hS (hgfM_zero_lt_N A) ((hgfMU St A S0 0).nat_lt_B k)]; exact (hgfMU St A S0 0).g_nat k
  g_E := by rw [hgfMTg_eq hSt hS (hgfM_zero_lt_N A) (hgfMU St A S0 0).E_lt_B]; exact (hgfMU St A S0 0).g_E
  g_lowE := fun c hc => by
    rw [hgfMTg_eq hSt hS (hgfM_zero_lt_N A) (hc.trans (hgfMU St A S0 0).E_lt_B)]; exact (hgfMU St A S0 0).g_lowE c hc
  g_G0 := fun h => by
    obtain ⟨n, hn1, hn⟩ := hgfMT_cof hSt hS h
    rw [hgfMTg_eq hSt hS hn1 hn]; exact (hgfMU St A S0 n).g_G0 hn
  g_add := fun Z hZ hωZ x y hxy hgx hgy => by
    obtain ⟨n, hn1, hn⟩ := hgfMT_cof hSt hS hxy
    have hx : x < (hgfMU St A S0 n).B := lt_of_le_of_lt le_self_add hn
    have hy : y < (hgfMU St A S0 n).B := lt_of_le_of_lt le_add_self hn
    rw [hgfMTg_eq hSt hS hn1 hn]; rw [hgfMTg_eq hSt hS hn1 hx] at hgx; rw [hgfMTg_eq hSt hS hn1 hy] at hgy
    exact (hgfMU St A S0 n).g_add Z hZ hωZ x y hn hgx hgy
  g_opow := fun Z hZw hωZ y hy hg => by
    obtain ⟨n, hn1, hn⟩ := hgfMT_cof hSt hS hy
    have hy' : y < (hgfMU St A S0 n).B := lt_of_le_of_lt (right_le_opow y one_lt_omega0) hn
    rw [hgfMTg_eq hSt hS hn1 hn]; rw [hgfMTg_eq hSt hS hn1 hy'] at hg
    exact (hgfMU St A S0 n).g_opow Z hZw hωZ y hn hg
  code_gate := fun Z hZ1 hZ0 hZa hZp At hAt c hc hcB => by
    obtain ⟨n, hn1, hn⟩ := hgfMT_cof hSt hS hcB
    rw [hgfMTg_eq hSt hS hn1 hn]
    exact (hgfMU St A S0 n).code_gate Z hZ1 hZ0 hZa hZp At (fun s hs => (hAt s hs).imp_right
      (fun h => (hgfMT_B_lt hSt hS hn1).le.trans h)) c hc hn
  g_succ := fun Z hZ c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hgfMT_cof hSt hS hc
    have hc' : c < (hgfMU St A S0 n).B := (lt_add_one c).trans hn
    rw [hgfMTg_eq hSt hS hn1 hn]; rw [hgfMTg_eq hSt hS hn1 hc'] at hg
    exact (hgfMU St A S0 n).g_succ Z hZ c hn hg
  g_le_succ := hgfMTg_le_succ hSt hS
  mem := fun S a b ha c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hgfMT_cof hSt hS hc
    rw [hgfMTg_eq hSt hS hn1 hn] at hg
    exact (hgfMU St A S0 n).mem S a b ha c hn hg
  R_zero := fun x => by
    rw [hgfMTR_eq hSt hS (hgfM_zero_lt_N A) (hgfMU St A S0 0).B_pos]; exact (hgfMU St A S0 0).R_zero x
  R_nat := fun k x => by
    rw [hgfMTR_eq hSt hS (hgfM_zero_lt_N A) ((hgfMU St A S0 0).nat_lt_B k)]; exact (hgfMU St A S0 0).R_nat k x
  R_E := fun x => by rw [hgfMTR_eq hSt hS (hgfM_zero_lt_N A) (hgfMU St A S0 0).E_lt_B]; exact (hgfMU St A S0 0).R_E x
  R_succ := hgfMTR_succ hSt hS
  R_pos := fun x hx hx1 c hc0 hc hg => by
    obtain ⟨n, hn1, hn⟩ := hgfMT_cof hSt hS hc
    rw [hgfMTR_eq hSt hS hn1 hn]; rw [hgfMTg_eq hSt hS hn1 hn] at hg
    exact (hgfMU St A S0 n).R_pos x hx hx1 c hc0 hn hg
  R_omega := fun x hx hx1 c hω hc hg => by
    obtain ⟨n, hn1, hn⟩ := hgfMT_cof hSt hS hc
    rw [hgfMTR_eq hSt hS hn1 hn]; rw [hgfMTg_eq hSt hS hn1 hn] at hg
    exact (hgfMU St A S0 n).R_omega x hx hx1 c hω hn hg
  R_lt_b := fun x hx hx1 hγx c hc hg => by
    obtain ⟨μ, hμ, hcμ, hγμ⟩ := hgfMT_small hSt hS hc hx hx1 hγx hg
    rw [hgfMTR_eq hSt hS hμ hcμ]; rw [hgfMTg_eq hSt hS hμ hcμ] at hg
    exact ((hgfMU St A S0 μ).R_lt_b x hx hx1 hγμ c hcμ hg).trans (hgfMT_b_lt hSt hS hμ hx hx1 hγμ)
  R_lt_Z := fun x hx hx1 c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hgfMT_cof hSt hS hc
    rw [hgfMTR_eq hSt hS hn1 hn]; rw [hgfMTg_eq hSt hS hn1 hn] at hg
    exact (((hgfMU St A S0 n).R_lt_Z x hx hx1 c hn hg).trans_le (hgfMU_Zb hSt hS hn1 x hx hx1)).trans_le (hgfMTZ_ge x)
  mono := fun x hx hx1 c hc d hfc hgc hgd => by
    obtain ⟨n, hn1, hn⟩ := hgfMT_cof hSt hS hc
    have hf : d < (hgfMU St A S0 n).B := hfc.trans hn
    rw [hgfMTR_eq hSt hS hn1 hn,
        hgfMTR_eq hSt hS hn1 hf]; rw [hgfMTg_eq hSt hS hn1 hn] at hgc; rw [hgfMTg_eq hSt hS hn1 hf] at hgd
    exact (hgfMU St A S0 n).mono x hx hx1 c hn d hfc hgc hgd
  cof := fun x hx hx1 c hc hg ν hν => by
    obtain ⟨n, hn1, hn⟩ := hgfMT_cof hSt hS hc
    rw [hgfMTR_eq hSt hS hn1 hn] at hν; rw [hgfMTg_eq hSt hS hn1 hn] at hg
    obtain ⟨d, hfc, hgd, hνd⟩ := (hgfMU St A S0 n).cof x hx hx1 c hn hg ν hν
    have hf : d < (hgfMU St A S0 n).B := hfc.trans hn
    exact ⟨d, hfc, by rw [hgfMTg_eq hSt hS hn1 hf]; exact hgd, by rw [hgfMTR_eq hSt hS hn1 hf]; exact hνd⟩
  b_cof := fun x hx hx1 hγx ν hν => by
    obtain ⟨k, hk⟩ := hgfMTr_cof hSt hS hx hx1 hγx hν
    have hkT : hgfMTt A k < hcN α A.F := hgfMTt_lt A k
    have hkB : hgfMTt A k < (hgfMU St A S0 (hgfMTt A k)).B := hgfMU_self hSt hS hkT
    refine ⟨hgfMTt A k, hkT, ?_, ?_⟩
    · rw [hgfMTg_eq hSt hS hkT hkB]; exact hgfMTt_g hSt hS hx hx1 hγx k
    · rw [hgfMTR_eq hSt hS hkT hkB]; exact hk
  b_E := fun x _ _ _ => hcN_E α _
  x_lt_b := fun x hx hx1 hγx => (A.Fr_gt hx hx1 hγx).trans (A.Fr_lt_N x)
  b_eN := fun x hx hx1 hγx => gz_eN_fix hx hx1 (hc_fix_down A.lv.one_le (hcN_fix α _))
    ((A.Fr_gt hx hx1 hγx).trans (A.Fr_lt_N x)) (A.N_lt1x hx hx1 hγx)
  ba_lt := fun x hx hx1 hγx => A.N_lt1x hx hx1 hγx
  b_Z := fun x _ _ hγx => by
    show _ < hgfMTZ A x
    unfold hgfMTZ; rw [if_pos hγx]
    exact go_eN_lt_evZ (lt_evZ _)
  b_pi := fun _ _ hB hγ => A.N_pi hB hγ
  ba_pi := fun _ _ hB hγ => A.N_pi hB hγ
  ex := fun σ ρ hB c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hgfMT_cof hSt hS hc
    rw [hgfMTR_eq hSt hS hn1 hn, hgfMTR_eq hSt hS hn1 hn]; rw [hgfMTg_eq hSt hS hn1 hn] at hg
    exact (hgfMU St A S0 n).ex σ ρ hB c hn hg
  dig := fun σ ρ hB hγσ d hf hg P P' hat => by
    obtain ⟨μ, hμ, hfμ, hγμ⟩ := hgfMT_small hSt hS hf hB.1 (hB.2.2.1.trans hB.2.2.2) hγσ hg
    rw [hgfMTR_eq hSt hS hμ hfμ, hgfMTR_eq hSt hS hμ hfμ]; rw [hgfMTg_eq hSt hS hμ hfμ] at hg
    exact (hgfMU St A S0 μ).dig σ ρ hB hγμ d hfμ hg P P' (fun β hβ hβe =>
      hat β hβ (hβe.trans (hgfMT_b_lt hSt hS hμ hB.2.1 hB.2.2.2 (hγμ.trans hB.2.2.1))))
  ld := fun c hl hc => by
    obtain ⟨n, hn1, hn⟩ := hgfMT_cof hSt hS hc
    obtain ⟨cp, lp, T, hcp, hgcp, hfec, hex⟩ := (hgfMU St A S0 n).ld c hl hn
    have hcpn : cp < (hgfMU St A S0 n).B := hcp.trans hn
    refine ⟨cp, lp, T, hcp, by rw [hgfMTg_eq hSt hS hn1 hn, hgfMTg_eq hSt hS hn1 hcpn]; exact hgcp,
        fun x hx hx1 hg => ?_,
      fun σ ρ hB hg => hex σ ρ hB (by rw [← hgfMTg_eq hSt hS hn1 hn]; exact hg)⟩
    rw [hgfMTg_eq hSt hS hn1 hn] at hg
    rw [hgfMTR_eq hSt hS hn1 hn, hgfMTR_eq hSt hS hn1 hcpn]
    exact hfec x hx hx1 hg

theorem hgfMTU_B : (hgfMTU hSt hS).B = hcN α A.F := rfl

theorem hgfMTU_γ : (hgfMTU hSt hS).γ = A.γN := rfl

theorem hgfMTU_b (x : Ordinal.{0}) : (hgfMTU hSt hS).b x = hcN α (A.Fr x) := rfl

/-- **The union extends every start** (readings). -/
theorem hgfMTU_R {ν c : Ordinal.{0}} (hν : ν < hcN α A.F) (hc : c < (hgfMU St A S0 ν).B) (x : Ordinal.{0}) :
    (hgfMTU hSt hS).R c x = (hgfMU St A S0 ν).R c x := hgfMTR_eq hSt hS hν hc x

/-- **The union extends every start** (gates). -/
theorem hgfMTU_g {ν c : Ordinal.{0}} (hν : ν < hcN α A.F) (hc : c < (hgfMU St A S0 ν).B) :
    (hgfMTU hSt hS).g c = (hgfMU St A S0 ν).g c := hgfMTg_eq hSt hS hν hc

/-- **The union extends the start `S0`.** -/
theorem hgfMTU_R0 {c : Ordinal.{0}} (hc : c < S0.B) (x : Ordinal.{0}) : (hgfMTU hSt hS).R c x = S0.R c x := by
  rw [hgfMTU_R hSt hS (hgfM_zero_lt_N A) (by rw [hgfMU_zero]; exact hc), hgfMU_zero]

theorem hgfMTU_g0 {c : Ordinal.{0}} (hc : c < S0.B) : (hgfMTU hSt hS).g c = S0.g c := by
  rw [hgfMTU_g hSt hS (hgfM_zero_lt_N A) (by rw [hgfMU_zero]; exact hc), hgfMU_zero]

/-- **A code `c ∈ [F, N(F))` of the union with gate below a base `σ` forces the base gate below `σ`.** -/
theorem hgfMTU_high (hγN : A.γN = A.γ) {c σ : Ordinal.{0}} (hc : c < hcN α A.F) (hFc : A.F ≤ c) (hσ : InE σ)
    (hσ1 : σ < Om1) (hg : (hgfMTU hSt hS).g c < σ) : (hgfMTU hSt hS).γ < σ := by
  show A.γN < σ
  rw [hγN]; exact hgfMT_high hSt hS hc hFc hσ hσ1 hg

end Union

end Googology.Trans.PoR.InaccPsi.R2.Hg

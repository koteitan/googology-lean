import Googology.Trans.PoR.InaccPsi.R2.HcLvRec

/-!
# HcLvTop: THE UNION OF ALL OFFSETS OF A BASE OF ANY LEVEL

(Textual copy of `Hb.HbLvTop` for `Hc.HcVD`: bound fields `≤ B_x(x)` (`Hc.hcBR`) in place of `≤ B_ω(x)`;
the proofs are unchanged.)

For a base `A : Hb.HcA (j+1)` (level `j+2`), a start `S0` and a step with the specification, the union of all starts
`hcLvU St A S0 λ`, `λ < N_{j+2}(F)`, is a system `hcLvTU` with the bound `N_{j+2}(F)`, base gate `γ`, base reading
`N_{j+2}(F(x))`, bound field `evZ(N_{j+2}(F(x)))` above `γ` and `Z_o(x)` below.  The tower `t_0 = 0`,
`t_{k+1} = φ(j+2, F + 1 + t_k)` is cofinal in `N_{j+2}(F)`, its readings `r_{k+1}(x) = ϑˣ(Ω₁·(j+2) + F(x) + r_k(x))`
(by the specification of the step) are cofinal in `N_{j+2}(F(x))` and its starts have base gate below every base above
`γ`.  The union extends the start, reads it, and every code in `[F, N_{j+2}(F))` with gate below a base forces `γ`
below it (`hcLvTU_high`).

* `hcLvTt`, `hcLvTt_cof`, `hcLvTt_gate`, `hcLvTr`, `hcLvTr_succ`, `hcLvTr_cof`; `hcLvTN`, `hcLvTR`, `hcLvTg`, `hcLvTZ`,
  `hcLvT_small`, `hcLvT_high`, `hcLvTU` (**THE SYSTEM AT `N_{j+2}(F)`**), `hcLvTU_R0`, `hcLvTU_g0`, `hcLvTU_high`.

No new axiom.  New definitions: `hcLvTt`, `hcLvTr`, `hcLvTN`, `hcLvTR`, `hcLvTg`, `hcLvTZ`, `hcLvTU`.
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
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The tower of offsets -/

section Tower

variable {j : ℕ} (A : HcA (j + 1))

/-- **The tower of offsets**: `t_0 = 0`, `t_{k+1} = φ(2, F + 1 + t_k)`. -/
noncomputable def hcLvTt : ℕ → Ordinal.{0}
  | 0 => 0
  | k + 1 => veblen ((j + 1 + 1 : ℕ) : Ordinal.{0}) (A.F + 1 + hcLvTt k)

theorem hcLvTt_lt : ∀ k : ℕ, hcLvTt A k < hbN (j + 1 + 1) A.F
  | 0 => hcLv_zero_lt_N A
  | k + 1 => A.Q_lt_N (hcLvTt_lt k)

theorem hcLvTt_lt_succ (k : ℕ) : hcLvTt A k < hcLvTt A (k + 1) := A.lt_Q (hcLvTt_lt A k)

theorem hcLvTt_iter (n : ℕ) : (veblen ((j + 1 + 1 : ℕ) : Ordinal.{0}))^[n] (A.F + 1) ≤ hcLvTt A (n + 1) := by
  induction n with
  | zero =>
    show A.F + 1 ≤ veblen ((j + 1 + 1 : ℕ) : Ordinal.{0}) (A.F + 1 + 0)
    rw [add_zero]; exact right_le_veblen ((j + 1 + 1 : ℕ) : Ordinal.{0}) _
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    show veblen ((j + 1 + 1 : ℕ) : Ordinal.{0}) _ ≤ veblen ((j + 1 + 1 : ℕ) : Ordinal.{0}) (A.F + 1 + hcLvTt A (n + 1))
    exact (isNormal_veblen ((j + 1 + 1 : ℕ) : Ordinal.{0})).monotone (ih.trans le_add_self)

theorem hcLv_N_nfp : hbN (j + 1 + 1) A.F = nfp (veblen ((j + 1 + 1 : ℕ) : Ordinal.{0})) (A.F + 1) := rfl

/-- **The tower is cofinal in `N(F)`.** -/
theorem hcLvTt_cof {c : Ordinal.{0}} (hc : c < hbN (j + 1 + 1) A.F) : ∃ k : ℕ, c < hcLvTt A k := by
  rw [hcLv_N_nfp] at hc
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hc
  exact ⟨n + 1, hn.trans_le (hcLvTt_iter A n)⟩

variable {St : ∀ (X : HcX j) (U : HcVD), HcSStart (hcXPB X) U → HcVD} {S0 : HcVD}
  (hSt : ∀ X U h, HcSpec X U (St X U h)) (hS : HcLvStart A S0)
include hSt hS

theorem hcLvTt_B (k : ℕ) : (hcLvU St A S0 (hcLvTt A k)).B = hcLvTt A (k + 1) := hcLvU_B hSt hS (hcLvTt_lt A k)

/-- **Every start `hcLvU St A S0 t_k` has base gate below every base above `γ_F`.** -/
theorem hcLvTt_gate : ∀ (k : ℕ) (x : Ordinal.{0}), InE x → x < Om1 → A.γ < x → (hcLvU St A S0 (hcLvTt A k)).γ < x
  | 0, x, hx, hx1, hA => by
    show (hcLvU St A S0 0).γ < x
    rw [hcLvU_γ_iff hSt hS (hcLv_zero_lt_N A) hx hx1, (hcLvU St A S0 0).g_zero, max_eq_left zero_le]; exact hA
  | k + 1, x, hx, hx1, hA => by
    set l := hcLvTt A k with hl
    have hlT : l < hbN (j + 1 + 1) A.F := hcLvTt_lt A k
    have hl'T : hcLvTt A (k + 1) < hbN (j + 1 + 1) A.F := hcLvTt_lt A (k + 1)
    have hsp := hcLvU_succ_spec hSt hS hlT
    have hl1 : l + 1 ≤ hcLvTt A (k + 1) := Order.add_one_le_of_lt (hcLvTt_lt_succ A k)
    have hl1T : l + 1 < hbN (j + 1 + 1) A.F := hl1.trans_lt hl'T
    have hB : hcLvTt A (k + 1) = (hcLvU St A S0 l).B := (hcLvTt_B A hSt hS k).symm
    have hcB : hcLvTt A (k + 1) < (hcLvU St A S0 (l + 1)).B := by
      rw [hcLvU_B hSt hS hl1T, hB, hcLvU_B hSt hS hlT]; exact A.Q_lt_Q (lt_add_one l)
    rw [hcLvU_γ_iff hSt hS hl'T hx hx1, (hcLv_ext hSt hS hl1 hl'T).2 _ hcB, hB, hcLvU_B hSt hS hlT]
    refine max_lt hA ((hsp.gF x hx hx1).2 ?_)
    exact max_lt hA ((max_lt_iff.1 ((hcLvU_γ_iff hSt hS hlT hx hx1).1 (hcLvTt_gate k x hx hx1 hA))).2)

end Tower

/-- The reading of the tower code `t_k` (in its start). -/
noncomputable def hcLvTr {j : ℕ} (St : ∀ (X : HcX j) (U : HcVD), HcSStart (hcXPB X) U → HcVD) (A : HcA (j + 1)) (S0 :
    HcVD) (k : ℕ) (x : Ordinal.{0}) :
    Ordinal.{0} := (hcLvU St A S0 (hcLvTt A k)).R (hcLvTt A k) x

section TowerRead

variable {j : ℕ} {St : ∀ (X : HcX j) (U : HcVD), HcSStart (hcXPB X) U → HcVD} (hSt : ∀ X U h, HcSpec X U (St X U h))
  {A : HcA (j + 1)} {S0 : HcVD} (hS : HcLvStart A S0) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hA : A.γ < x)
include hSt hS hx hx1 hA

theorem hcLvTt_g (k : ℕ) : (hcLvU St A S0 (hcLvTt A k)).g (hcLvTt A k) < x :=
  (max_lt_iff.1 ((hcLvU_γ_iff hSt hS (hcLvTt_lt A k) hx hx1).1 (hcLvTt_gate A hSt hS k x hx hx1 hA))).2

/-- **`r_{k+1}(x) = ϑˣ(Ω₁·2 + F(x) + r_k(x))`**: the code `t_{k+1} = Q_{t_k}` is read as the base reading of the start
`t_k`. -/
theorem hcLvTr_succ (k : ℕ) :
    hcLvTr St A S0 (k + 1) x = glA ((j + 1 + 1 : ℕ) : Ordinal.{0}) (A.Fr x + hcLvTr St A S0 k x) x := by
  set l := hcLvTt A k with hl
  have hlT : l < hbN (j + 1 + 1) A.F := hcLvTt_lt A k
  have hl'T : hcLvTt A (k + 1) < hbN (j + 1 + 1) A.F := hcLvTt_lt A (k + 1)
  have hsp := hcLvU_succ_spec hSt hS hlT
  have hl1 : l + 1 ≤ hcLvTt A (k + 1) := Order.add_one_le_of_lt (hcLvTt_lt_succ A k)
  have hl1T : l + 1 < hbN (j + 1 + 1) A.F := hl1.trans_lt hl'T
  have hB : hcLvTt A (k + 1) = (hcLvU St A S0 l).B := (hcLvTt_B A hSt hS k).symm
  have hcB : hcLvTt A (k + 1) < (hcLvU St A S0 (l + 1)).B := by
    rw [hcLvU_B hSt hS hl1T, hB, hcLvU_B hSt hS hlT]; exact A.Q_lt_Q (lt_add_one l)
  have hg : max A.γ ((hcLvU St A S0 l).g l) < x := max_lt hA (hcLvTt_g hSt hS hx hx1 hA k)
  unfold hcLvTr
  rw [(hcLv_ext hSt hS hl1 hl'T).1 _ x hcB, hB, hcLvU_B hSt hS hlT]
  exact hsp.RF x hx hx1 hg

theorem hcLvTr_zero : hcLvTr St A S0 0 x = 0 := by unfold hcLvTr; exact (hcLvU St A S0 (hcLvTt A 0)).R_zero x

theorem hcLvTr_lt_N (k : ℕ) : hcLvTr St A S0 k x < hbN (j + 1 + 1) (A.Fr x) :=
  A.lvR_lt_N _ (hcLvU_Zb hSt hS (hcLvTt_lt A k)) (hcLvU_self hSt hS (hcLvTt_lt A k)) hx hx1 hA
    (hcLvTt_g hSt hS hx hx1 hA k)

/-- **The iterates of `φ(j+2, ·)` from `N_{j+1}(F(x)) + 1` lie below the tower readings.** -/
theorem hcLvTr_iter (n : ℕ) :
    (veblen ((j + 1 + 1 : ℕ) : Ordinal.{0}))^[n] (hbN (j + 1) (A.Fr x) + 1) ≤ hcLvTr St A S0 (n + 2) x := by
  obtain ⟨i0, hi0⟩ := hb_LuP_of_fix (j + 1) (hbN_fix (j + 1) (A.Fr x))
  have hstep : ∀ k : ℕ, hcLvTr St A S0 (k + 1) x = veblen ((j + 1 + 1 : ℕ) : Ordinal.{0})
      (i0 + hcLvTr St A S0 k x) := fun k => by
    rw [hcLvTr_succ hSt hS hx hx1 hA k, A.lvglAV hx hx1 hA hi0 (hcLvTr_lt_N hSt hS hx hx1 hA k)]
  have h1 : hcLvTr St A S0 1 x = hbN (j + 1) (A.Fr x) := by
    rw [hstep 0, hcLvTr_zero hSt hS hx hx1 hA, add_zero, hi0]
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply]
    refine Order.add_one_le_of_lt ?_
    rw [hstep 1, h1]
    refine (le_add_self : hbN (j + 1) (A.Fr x) ≤ i0 + hbN (j + 1) (A.Fr x)).trans_lt ?_
    have h2 := hcLvTr_lt_N hSt hS hx hx1 hA 2
    rw [hstep 1, h1] at h2
    exact hb_nofixV (j + 1) hi0 le_self_add h2
  | succ n ih =>
    rw [Function.iterate_succ_apply', hstep (n + 2)]
    exact (isNormal_veblen ((j + 1 + 1 : ℕ) : Ordinal.{0})).monotone (ih.trans le_add_self)

/-- **The tower readings are cofinal in `N_{j+2}(F(x))`.** -/
theorem hcLvTr_cof {v : Ordinal.{0}} (hv : v < hbN (j + 1 + 1) (A.Fr x)) : ∃ k : ℕ, v < hcLvTr St A S0 k x := by
  have e : hbN (j + 1 + 1) (A.Fr x) = nfp (veblen ((j + 1 + 1 : ℕ) : Ordinal.{0})) (hbN (j + 1) (A.Fr x) + 1) := by
    refine le_antisymm ?_ ?_
    · exact hbN_le (j + 1 + 1) (nfp_fp (isNormal_veblen _) _)
        ((hbN_gt (j + 1) (A.Fr x)).trans ((lt_add_one _).trans_le (le_nfp _ _)))
    · exact nfp_le_fp (isNormal_veblen ((j + 1 + 1 : ℕ) : Ordinal.{0})).strictMono.monotone
        (Order.add_one_le_of_lt (hbN_lt_succ (j + 1) (A.Fr x))) (hbN_fix _ _).le
  rw [e] at hv
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hv
  exact ⟨n + 2, hn.trans_le (hcLvTr_iter hSt hS hx hx1 hA n)⟩

end TowerRead

/-! ## The union of all offsets -/

section Union

variable {j : ℕ} (St : ∀ (X : HcX j) (U : HcVD), HcSStart (hcXPB X) U → HcVD) (A : HcA (j + 1)) (S0 : HcVD)

/-- The first start containing `c`. -/
noncomputable def hcLvTN (c : Ordinal.{0}) : Ordinal.{0} := sInf {ν | ν < hbN (j + 1 + 1) A.F ∧ c < (hcLvU St A S0 ν).B}

/-- The reading of the union. -/
noncomputable def hcLvTR (c x : Ordinal.{0}) : Ordinal.{0} := (hcLvU St A S0 (hcLvTN St A S0 c)).R c x

/-- The gate of the union. -/
noncomputable def hcLvTg (c : Ordinal.{0}) : Ordinal.{0} := (hcLvU St A S0 (hcLvTN St A S0 c)).g c

open Classical in
/-- The bound field of the union: `evZ(N_{j+2}(F(x)))` above `γ`, `Z_o(x)` below. -/
noncomputable def hcLvTZ (x : Ordinal.{0}) : Ordinal.{0} :=
  if A.γ < x then evZ (hbN (j + 1 + 1) (A.Fr x)) else A.Zo x

variable {St A S0} (hSt : ∀ X U h, HcSpec X U (St X U h)) (hS : HcLvStart A S0)
include hSt hS

theorem hcLvT_cof {c : Ordinal.{0}} (hc : c < hbN (j + 1 + 1) A.F) : ∃ ν, ν < hbN (j + 1 + 1) A.F ∧ c <
    (hcLvU St A S0 ν).B := by
  obtain ⟨k, hk⟩ := hcLvTt_cof A hc
  exact ⟨hcLvTt A k, hcLvTt_lt A k, hk.trans (by rw [hcLvTt_B A hSt hS k]; exact hcLvTt_lt_succ A k)⟩

omit hSt hS in
theorem hcLvTN_spec {c ν : Ordinal.{0}} (hν : ν < hbN (j + 1 + 1) A.F) (hc : c < (hcLvU St A S0 ν).B) :
    hcLvTN St A S0 c ≤ ν ∧ hcLvTN St A S0 c < hbN (j + 1 + 1) A.F ∧ c < (hcLvU St A S0 (hcLvTN St A S0 c)).B := by
  have hne : ({ν | ν < hbN (j + 1 + 1) A.F ∧ c < (hcLvU St A S0 ν).B} : Set Ordinal.{0}).Nonempty := ⟨ν, hν, hc⟩
  have hm := csInf_mem hne
  exact ⟨csInf_le' ⟨hν, hc⟩, hm.1, hm.2⟩

omit hSt hS in
theorem hcLvTN_min {c μ : Ordinal.{0}} (hμ : μ < hcLvTN St A S0 c) (hμl : μ < hbN (j + 1 + 1) A.F) : ¬ c <
    (hcLvU St A S0 μ).B :=
  fun hcμ => absurd (csInf_le' ⟨hμl, hcμ⟩ : hcLvTN St A S0 c ≤ μ) (not_le.2 hμ)

theorem hcLvT_B_lt {ν : Ordinal.{0}} (hν : ν < hbN (j + 1 + 1) A.F) : (hcLvU St A S0 ν).B < hbN (j + 1 + 1) A.F := by
  rw [hcLvU_B hSt hS hν]; exact A.Q_lt_N hν

theorem hcLvTN_high {c : Ordinal.{0}} (hc : hbN (j + 1 + 1) A.F ≤ c) : hcLvTN St A S0 c = 0 := by
  unfold hcLvTN
  have he : ({ν | ν < hbN (j + 1 + 1) A.F ∧ c < (hcLvU St A S0 ν).B} : Set Ordinal.{0}) = ∅ := by
    ext ν
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hν hcν
    exact absurd (hcν.trans (hcLvT_B_lt hSt hS hν)) (not_lt.2 hc)
  rw [he]; exact Ordinal.sInf_empty

theorem hcLvTR_eq {c ν : Ordinal.{0}} (hν : ν < hbN (j + 1 + 1) A.F) (hc : c < (hcLvU St A S0 ν).B) (x : Ordinal.{0}) :
    hcLvTR St A S0 c x = (hcLvU St A S0 ν).R c x := by
  obtain ⟨h1, -, h3⟩ := hcLvTN_spec hν hc
  exact ((hcLv_ext hSt hS h1 hν).1 c x h3).symm

theorem hcLvTg_eq {c ν : Ordinal.{0}} (hν : ν < hbN (j + 1 + 1) A.F) (hc : c < (hcLvU St A S0 ν).B) :
    hcLvTg St A S0 c = (hcLvU St A S0 ν).g c := by
  obtain ⟨h1, -, h3⟩ := hcLvTN_spec hν hc
  exact ((hcLv_ext hSt hS h1 hν).2 c h3).symm

theorem hcLvTR_succ (c x : Ordinal.{0}) : hcLvTR St A S0 (c + 1) x = hcLvTR St A S0 c x + 1 := by
  rcases lt_or_ge c (hbN (j + 1 + 1) A.F) with h | h
  · obtain ⟨n, hn1, hn⟩ := hcLvT_cof hSt hS (A.N_lim.add_one_lt h)
    rw [hcLvTR_eq hSt hS hn1 hn, hcLvTR_eq hSt hS hn1 ((lt_add_one c).trans hn), (hcLvU St A S0 n).R_succ]
  · unfold hcLvTR
    rw [hcLvTN_high hSt hS h, hcLvTN_high hSt hS (h.trans (le_self_add (a := c) (b := 1))), (hcLvU St A S0 0).R_succ]

theorem hcLvTg_le_succ (c : Ordinal.{0}) : hcLvTg St A S0 c ≤ hcLvTg St A S0 (c + 1) := by
  rcases lt_or_ge c (hbN (j + 1 + 1) A.F) with h | h
  · obtain ⟨n, hn1, hn⟩ := hcLvT_cof hSt hS (A.N_lim.add_one_lt h)
    rw [hcLvTg_eq hSt hS hn1 hn, hcLvTg_eq hSt hS hn1 ((lt_add_one c).trans hn)]; exact (hcLvU St A S0 n).g_le_succ c
  · unfold hcLvTg
    rw [hcLvTN_high hSt hS h, hcLvTN_high hSt hS (h.trans (le_self_add (a := c) (b := 1)))]; exact
        (hcLvU St A S0 0).g_le_succ c

/-- **A code of the union with gate below a base `σ > γ_F` lies in a start with base gate below `σ`.** -/
theorem hcLvT_small {c σ : Ordinal.{0}} (hc : c < hbN (j + 1 + 1) A.F) (hσ : InE σ) (hσ1 : σ < Om1) (hAσ : A.γ < σ)
    (hg : hcLvTg St A S0 c < σ) : ∃ μ, μ < hbN (j + 1 + 1) A.F ∧ c < (hcLvU St A S0 μ).B ∧ (hcLvU St A S0 μ).γ < σ := by
  obtain ⟨n, hn1, hn⟩ := hcLvT_cof hSt hS hc
  obtain ⟨-, hN1, hcN⟩ := hcLvTN_spec hn1 hn
  have hgN : hcLvTg St A S0 c = (hcLvU St A S0 (hcLvTN St A S0 c)).g c := rfl
  have I := hcLv_inv hSt hS _ hN1
  rcases zero_or_succ_or_isSuccLimit (hcLvTN St A S0 c) with h0 | ⟨m, hm⟩ | hlim
  · refine ⟨hcLvTN St A S0 c, hN1, hcN, ?_⟩
    rw [h0, hcLvU_γ_iff hSt hS (hcLv_zero_lt_N A) hσ hσ1, (hcLvU St A S0 0).g_zero, max_eq_left zero_le]
    exact hAσ
  · have hm' : hcLvTN St A S0 c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < hcLvTN St A S0 c := by rw [hm']; exact lt_add_one m
    have hml : m < hbN (j + 1 + 1) A.F := hmN.trans hN1
    have hBc : (hcLvU St A S0 m).B ≤ c := not_lt.1 (hcLvTN_min hmN hml)
    refine ⟨hcLvTN St A S0 c, hN1, hcN, ?_⟩
    rw [hgN, hm'] at hg
    rw [hm'] at hcN I ⊢
    exact I.high m (lt_add_one _) c σ hBc hcN hσ hσ1 hg
  · exfalso
    rw [hcLvU_B hSt hS hN1] at hcN
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen ((j + 1 + 1 : ℕ) : Ordinal.{0})).lt_iff_exists_lt
        (isSuccLimit_add _ hlim)).1 hcN
    obtain ⟨d, hd, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    have hdl : d < hbN (j + 1 + 1) A.F := hd.trans hN1
    refine hcLvTN_min hd hdl ?_
    rw [hcLvU_B hSt hS hdl]; exact hct.trans_le ((isNormal_veblen ((j + 1 + 1 : ℕ) : Ordinal.{0})).monotone htd)

/-- **A code `c ∈ [F, N(F))` of the union with gate below a base `σ` forces `γ_F < σ`.** -/
theorem hcLvT_high {c σ : Ordinal.{0}} (hc : c < hbN (j + 1 + 1) A.F) (hFc : A.F ≤ c) (hσ : InE σ) (hσ1 : σ < Om1)
    (hg : hcLvTg St A S0 c < σ) : A.γ < σ := by
  obtain ⟨n, hn1, hn⟩ := hcLvT_cof hSt hS hc
  obtain ⟨-, hN1, hcN⟩ := hcLvTN_spec hn1 hn
  have hgN : hcLvTg St A S0 c = (hcLvU St A S0 (hcLvTN St A S0 c)).g c := rfl
  have I := hcLv_inv hSt hS _ hN1
  rcases zero_or_succ_or_isSuccLimit (hcLvTN St A S0 c) with h0 | ⟨m, hm⟩ | hlim
  · rw [hgN, h0, hcLvU_zero] at hg
    rw [h0, hcLvU_zero] at hcN
    exact hS.high0 c σ hFc hcN hσ hσ1 hg
  · have hm' : hcLvTN St A S0 c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < hcLvTN St A S0 c := by rw [hm']; exact lt_add_one m
    have hml : m < hbN (j + 1 + 1) A.F := hmN.trans hN1
    have hBc : (hcLvU St A S0 m).B ≤ c := not_lt.1 (hcLvTN_min hmN hml)
    rw [hgN, hm'] at hg
    rw [hm'] at hcN I hN1
    have hγ := I.high m (lt_add_one _) c σ hBc hcN hσ hσ1 hg
    exact (max_lt_iff.1 ((hcLvU_γ_iff hSt hS hN1 hσ hσ1).1 hγ)).1
  · exfalso
    rw [hcLvU_B hSt hS hN1] at hcN
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen ((j + 1 + 1 : ℕ) : Ordinal.{0})).lt_iff_exists_lt
        (isSuccLimit_add _ hlim)).1 hcN
    obtain ⟨d, hd, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    have hdl : d < hbN (j + 1 + 1) A.F := hd.trans hN1
    refine hcLvTN_min hd hdl ?_
    rw [hcLvU_B hSt hS hdl]; exact hct.trans_le ((isNormal_veblen ((j + 1 + 1 : ℕ) : Ordinal.{0})).monotone htd)

/-- **`b_μ(x) < N(F(x))`** for every start with base gate below `x`. -/
theorem hcLvT_b_lt {μ x : Ordinal.{0}} (hμ : μ < hbN (j + 1 + 1) A.F) (hx : InE x) (hx1 : x < Om1) (hγ :
    (hcLvU St A S0 μ).γ < x) :
    (hcLvU St A S0 μ).b x < hbN (j + 1 + 1) (A.Fr x) := by
  have hg : max A.γ ((hcLvU St A S0 μ).g μ) < x := (hcLvU_γ_iff hSt hS hμ hx hx1).1 hγ
  have hA : A.γ < x := (max_lt_iff.1 hg).1
  rw [(hcLvU_start hSt hS hμ).b x hx hx1 hg]
  exact hcX_glA_lt hx hx1 (j + 1) (A.Fr_glA hx hx1 hA) (A.Fr_lt1 hx hx1 hA) (A.N_lt1x hx hx1 hA)
    (A.lvR_lt_N _ (hcLvU_Zb hSt hS hμ) (hcLvU_self hSt hS hμ) hx hx1 hA (max_lt_iff.1 hg).2)

omit hSt hS in
theorem hcLvTZ_fix (x : Ordinal.{0}) : veblen 1 (hcLvTZ A x) = hcLvTZ A x := by
  unfold hcLvTZ; split_ifs
  · exact epsilon_evZ _
  · exact ha_fix1_of_fix2 (A.Zo_fix x)

omit hSt hS in
theorem hcLvTZ_BR (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : hcLvTZ A x ≤ hcBR x := by
  unfold hcLvTZ; split_ifs with h
  · exact (hb_evZ_lt_fix2 (A.Zo_fix x) (A.N_Zo hx hx1 h)).le.trans (A.Zo_BR x hx hx1)
  · exact A.Zo_BR x hx hx1

omit hSt hS in
theorem hcLvTZ_ge (x : Ordinal.{0}) : A.Zl x ≤ hcLvTZ A x := by
  unfold hcLvTZ HcA.Zl; split_ifs
  · exact (lt_evZ _).le
  · exact le_rfl

/-- **THE SYSTEM AT `N(F)`**: the union of all starts `hcLvU St A S0 λ`, `λ < N(F)`: bound `N(F)`, base gate `γ_F`, base
reading `N(F(x))`, bound field `hcLvTZ`. -/
noncomputable def hcLvTU : HcVD where
  B := hbN (j + 1 + 1) A.F
  γ := A.γ
  γ_lt := A.γ_lt
  γ_cl := fun Z hZ hZ1 h => A.N_cl Z hZ hZ1 h
  γ_G := fun h => absurd h (A.G_le.trans_lt A.F_lt_N).ne'
  R := hcLvTR St A S0
  g := hcLvTg St A S0
  b := fun x => hbN (j + 1 + 1) (A.Fr x)
  ba := fun x => hbN (j + 1 + 1) (A.Fr x)
  ix := hbN (j + 1 + 1) A.F
  Z := hcLvTZ A
  B_E := A.N_E
  G_le := (A.G_le.trans_lt A.F_lt_N).le
  B_lt1 := A.N_lt1
  B_ix := (show veblen 1 (hbN (j + 1 + 1) A.F) = hbN (j + 1 + 1) A.F by
    have := hb_fix_down (j := 1) (by omega) (hbN_fix (j + 1 + 1) A.F); rwa [Nat.cast_one] at this).symm
  Z_fix := fun x _ _ => hcLvTZ_fix x
  Z_BR := hcLvTZ_BR
  ix_mem := fun S _ _ ha hb => A.N_mem S ha hb
  g_lt := fun c hc => by
    obtain ⟨n, hn1, hn⟩ := hcLvT_cof hSt hS hc
    rw [hcLvTg_eq hSt hS hn1 hn]; exact (hcLvU St A S0 n).g_lt c hn
  g_zero := by
    rw [hcLvTg_eq hSt hS (hcLv_zero_lt_N A) (hcLvU St A S0 0).B_pos]; exact (hcLvU St A S0 0).g_zero
  g_nat := fun k => by
    rw [hcLvTg_eq hSt hS (hcLv_zero_lt_N A) ((hcLvU St A S0 0).nat_lt_B k)]; exact (hcLvU St A S0 0).g_nat k
  g_E := by rw [hcLvTg_eq hSt hS (hcLv_zero_lt_N A) (hcLvU St A S0 0).E_lt_B]; exact (hcLvU St A S0 0).g_E
  g_lowE := fun c hc => by
    rw [hcLvTg_eq hSt hS (hcLv_zero_lt_N A) (hc.trans (hcLvU St A S0 0).E_lt_B)]; exact (hcLvU St A S0 0).g_lowE c hc
  g_G0 := fun h => by
    obtain ⟨n, hn1, hn⟩ := hcLvT_cof hSt hS h
    rw [hcLvTg_eq hSt hS hn1 hn]; exact (hcLvU St A S0 n).g_G0 hn
  g_add := fun Z hZ hωZ x y hxy hgx hgy => by
    obtain ⟨n, hn1, hn⟩ := hcLvT_cof hSt hS hxy
    have hx : x < (hcLvU St A S0 n).B := lt_of_le_of_lt le_self_add hn
    have hy : y < (hcLvU St A S0 n).B := lt_of_le_of_lt le_add_self hn
    rw [hcLvTg_eq hSt hS hn1 hn]; rw [hcLvTg_eq hSt hS hn1 hx] at hgx; rw [hcLvTg_eq hSt hS hn1 hy] at hgy
    exact (hcLvU St A S0 n).g_add Z hZ hωZ x y hn hgx hgy
  g_opow := fun Z hZw hωZ y hy hg => by
    obtain ⟨n, hn1, hn⟩ := hcLvT_cof hSt hS hy
    have hy' : y < (hcLvU St A S0 n).B := lt_of_le_of_lt (right_le_opow y one_lt_omega0) hn
    rw [hcLvTg_eq hSt hS hn1 hn]; rw [hcLvTg_eq hSt hS hn1 hy'] at hg
    exact (hcLvU St A S0 n).g_opow Z hZw hωZ y hn hg
  code_gate := fun Z hZ1 hZ0 hZa hZp At hAt c hc hcB => by
    obtain ⟨n, hn1, hn⟩ := hcLvT_cof hSt hS hcB
    rw [hcLvTg_eq hSt hS hn1 hn]
    exact (hcLvU St A S0 n).code_gate Z hZ1 hZ0 hZa hZp At (fun s hs => (hAt s hs).imp_right
      (fun h => (hcLvT_B_lt hSt hS hn1).le.trans h)) c hc hn
  g_succ := fun Z hZ c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hcLvT_cof hSt hS hc
    have hc' : c < (hcLvU St A S0 n).B := (lt_add_one c).trans hn
    rw [hcLvTg_eq hSt hS hn1 hn]; rw [hcLvTg_eq hSt hS hn1 hc'] at hg
    exact (hcLvU St A S0 n).g_succ Z hZ c hn hg
  g_le_succ := hcLvTg_le_succ hSt hS
  mem := fun S a b ha c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hcLvT_cof hSt hS hc
    rw [hcLvTg_eq hSt hS hn1 hn] at hg
    exact (hcLvU St A S0 n).mem S a b ha c hn hg
  R_zero := fun x => by
    rw [hcLvTR_eq hSt hS (hcLv_zero_lt_N A) (hcLvU St A S0 0).B_pos]; exact (hcLvU St A S0 0).R_zero x
  R_nat := fun k x => by
    rw [hcLvTR_eq hSt hS (hcLv_zero_lt_N A) ((hcLvU St A S0 0).nat_lt_B k)]; exact (hcLvU St A S0 0).R_nat k x
  R_E := fun x => by rw [hcLvTR_eq hSt hS (hcLv_zero_lt_N A) (hcLvU St A S0 0).E_lt_B]; exact (hcLvU St A S0 0).R_E x
  R_succ := hcLvTR_succ hSt hS
  R_pos := fun x hx hx1 c hc0 hc hg => by
    obtain ⟨n, hn1, hn⟩ := hcLvT_cof hSt hS hc
    rw [hcLvTR_eq hSt hS hn1 hn]; rw [hcLvTg_eq hSt hS hn1 hn] at hg
    exact (hcLvU St A S0 n).R_pos x hx hx1 c hc0 hn hg
  R_omega := fun x hx hx1 c hω hc hg => by
    obtain ⟨n, hn1, hn⟩ := hcLvT_cof hSt hS hc
    rw [hcLvTR_eq hSt hS hn1 hn]; rw [hcLvTg_eq hSt hS hn1 hn] at hg
    exact (hcLvU St A S0 n).R_omega x hx hx1 c hω hn hg
  R_lt_b := fun x hx hx1 hγx c hc hg => by
    obtain ⟨μ, hμ, hcμ, hγμ⟩ := hcLvT_small hSt hS hc hx hx1 hγx hg
    rw [hcLvTR_eq hSt hS hμ hcμ]; rw [hcLvTg_eq hSt hS hμ hcμ] at hg
    exact ((hcLvU St A S0 μ).R_lt_b x hx hx1 hγμ c hcμ hg).trans (hcLvT_b_lt hSt hS hμ hx hx1 hγμ)
  R_lt_Z := fun x hx hx1 c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hcLvT_cof hSt hS hc
    rw [hcLvTR_eq hSt hS hn1 hn]; rw [hcLvTg_eq hSt hS hn1 hn] at hg
    exact (((hcLvU St A S0 n).R_lt_Z x hx hx1 c hn hg).trans_le (hcLvU_Zb hSt hS hn1 x hx hx1)).trans_le (hcLvTZ_ge x)
  mono := fun x hx hx1 c hc d hdc hgc hgd => by
    obtain ⟨n, hn1, hn⟩ := hcLvT_cof hSt hS hc
    have hd : d < (hcLvU St A S0 n).B := hdc.trans hn
    rw [hcLvTR_eq hSt hS hn1 hn,
        hcLvTR_eq hSt hS hn1 hd]; rw [hcLvTg_eq hSt hS hn1 hn] at hgc; rw [hcLvTg_eq hSt hS hn1 hd] at hgd
    exact (hcLvU St A S0 n).mono x hx hx1 c hn d hdc hgc hgd
  cof := fun x hx hx1 c hc hg ν hν => by
    obtain ⟨n, hn1, hn⟩ := hcLvT_cof hSt hS hc
    rw [hcLvTR_eq hSt hS hn1 hn] at hν; rw [hcLvTg_eq hSt hS hn1 hn] at hg
    obtain ⟨d, hdc, hgd, hνd⟩ := (hcLvU St A S0 n).cof x hx hx1 c hn hg ν hν
    have hd : d < (hcLvU St A S0 n).B := hdc.trans hn
    exact ⟨d, hdc, by rw [hcLvTg_eq hSt hS hn1 hd]; exact hgd, by rw [hcLvTR_eq hSt hS hn1 hd]; exact hνd⟩
  b_cof := fun x hx hx1 hγx ν hν => by
    obtain ⟨k, hk⟩ := hcLvTr_cof hSt hS hx hx1 hγx hν
    have hkT : hcLvTt A k < hbN (j + 1 + 1) A.F := hcLvTt_lt A k
    have hkB : hcLvTt A k < (hcLvU St A S0 (hcLvTt A k)).B := hcLvU_self hSt hS hkT
    refine ⟨hcLvTt A k, hkT, ?_, ?_⟩
    · rw [hcLvTg_eq hSt hS hkT hkB]; exact hcLvTt_g hSt hS hx hx1 hγx k
    · rw [hcLvTR_eq hSt hS hkT hkB]; exact hk
  b_E := fun x _ _ _ => hbN_E _ _
  x_lt_b := fun x hx hx1 hγx => (A.Fr_gt hx hx1 hγx).trans (A.Fr_lt_N hx hx1 hγx)
  b_eN := fun x hx hx1 hγx => gz_eN_fix hx hx1
    (by have := hb_fix_down (j := 1) (by omega) (hbN_fix (j + 1 + 1) (A.Fr x)); rwa [Nat.cast_one] at this)
    ((A.Fr_gt hx hx1 hγx).trans (A.Fr_lt_N hx hx1 hγx)) (A.N_lt1x hx hx1 hγx)
  ba_lt := fun x hx hx1 hγx => A.N_lt1x hx hx1 hγx
  b_Z := fun x _ _ hγx => by
    show _ < hcLvTZ A x
    unfold hcLvTZ; rw [if_pos hγx]
    exact go_eN_lt_evZ (lt_evZ _)
  b_pi := fun _ _ hB hγ => A.N_pi hB hγ
  ba_pi := fun _ _ hB hγ => A.N_pi hB hγ
  ex := fun σ ρ hB c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hcLvT_cof hSt hS hc
    rw [hcLvTR_eq hSt hS hn1 hn, hcLvTR_eq hSt hS hn1 hn]; rw [hcLvTg_eq hSt hS hn1 hn] at hg
    exact (hcLvU St A S0 n).ex σ ρ hB c hn hg
  dig := fun σ ρ hB hγσ d hd hg P P' hat => by
    obtain ⟨μ, hμ, hdμ, hγμ⟩ := hcLvT_small hSt hS hd hB.1 (hB.2.2.1.trans hB.2.2.2) hγσ hg
    rw [hcLvTR_eq hSt hS hμ hdμ, hcLvTR_eq hSt hS hμ hdμ]; rw [hcLvTg_eq hSt hS hμ hdμ] at hg
    exact (hcLvU St A S0 μ).dig σ ρ hB hγμ d hdμ hg P P' (fun β hβ hβe =>
      hat β hβ (hβe.trans (hcLvT_b_lt hSt hS hμ hB.2.1 hB.2.2.2 (hγμ.trans hB.2.2.1))))
  ld := fun c hl hc => by
    obtain ⟨n, hn1, hn⟩ := hcLvT_cof hSt hS hc
    obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := (hcLvU St A S0 n).ld c hl hn
    have hcpn : cp < (hcLvU St A S0 n).B := hcp.trans hn
    refine ⟨cp, lp, T, hcp, by rw [hcLvTg_eq hSt hS hn1 hn, hcLvTg_eq hSt hS hn1 hcpn]; exact hgcp,
        fun x hx hx1 hg => ?_,
      fun σ ρ hB hg => hex σ ρ hB (by rw [← hcLvTg_eq hSt hS hn1 hn]; exact hg)⟩
    rw [hcLvTg_eq hSt hS hn1 hn] at hg
    rw [hcLvTR_eq hSt hS hn1 hn, hcLvTR_eq hSt hS hn1 hcpn]
    exact hdec x hx hx1 hg

theorem hcLvTU_B : (hcLvTU hSt hS).B = hbN (j + 1 + 1) A.F := rfl

theorem hcLvTU_γ : (hcLvTU hSt hS).γ = A.γ := rfl

theorem hcLvTU_b (x : Ordinal.{0}) : (hcLvTU hSt hS).b x = hbN (j + 1 + 1) (A.Fr x) := rfl

/-- **The union extends every start** (readings). -/
theorem hcLvTU_R {ν c : Ordinal.{0}} (hν : ν < hbN (j + 1 + 1) A.F) (hc : c < (hcLvU St A S0 ν).B) (x : Ordinal.{0}) :
    (hcLvTU hSt hS).R c x = (hcLvU St A S0 ν).R c x := hcLvTR_eq hSt hS hν hc x

/-- **The union extends every start** (gates). -/
theorem hcLvTU_g {ν c : Ordinal.{0}} (hν : ν < hbN (j + 1 + 1) A.F) (hc : c < (hcLvU St A S0 ν).B) :
    (hcLvTU hSt hS).g c = (hcLvU St A S0 ν).g c := hcLvTg_eq hSt hS hν hc

/-- **The union extends the start `S0`.** -/
theorem hcLvTU_R0 {c : Ordinal.{0}} (hc : c < S0.B) (x : Ordinal.{0}) : (hcLvTU hSt hS).R c x = S0.R c x := by
  rw [hcLvTU_R hSt hS (hcLv_zero_lt_N A) (by rw [hcLvU_zero]; exact hc), hcLvU_zero]

theorem hcLvTU_g0 {c : Ordinal.{0}} (hc : c < S0.B) : (hcLvTU hSt hS).g c = S0.g c := by
  rw [hcLvTU_g hSt hS (hcLv_zero_lt_N A) (by rw [hcLvU_zero]; exact hc), hcLvU_zero]

/-- **A code `c ∈ [F, N(F))` of the union with gate below a base `σ` forces the base gate below `σ`.** -/
theorem hcLvTU_high {c σ : Ordinal.{0}} (hc : c < hbN (j + 1 + 1) A.F) (hFc : A.F ≤ c) (hσ : InE σ) (hσ1 : σ < Om1)
    (hg : (hcLvTU hSt hS).g c < σ) : (hcLvTU hSt hS).γ < σ := hcLvT_high hSt hS hc hFc hσ hσ1 hg

end Union

end Googology.Trans.PoR.InaccPsi.R2.Hc

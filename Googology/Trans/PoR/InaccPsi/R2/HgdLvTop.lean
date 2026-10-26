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

/-!
# HgdLvTop: THE UNION OF ALL OFFSETS OF A BASE OF LEVEL `ω`: THE TOP TOWER TO `N_ω(F) = φ(ω+1, F+1)`

(Textual copy of `Hd.HdLvTop` for `Hg.HgVD`: bound fields `< Γ_{x+2}` in place of `≤ B_x(x)` (`Hc.hcBR`); the proofs
are unchanged except where the bound enters.  Names: prefix `hg`/`Hg` (from `hc`/`Hc`), `hgd`/`Hgd` (from `hd`/`Hd`),
`hgf`/`Hgf` (from `hf`/`Hf`), `hge`/`Hge` (from `he`/`He`).)

The level-`ω` version of `Hc.HcLvTop`.  For a base `A : Hd.HgdA` of level `ω` and a start `S0`, the union of all
starts `Hg.hgdLvU A S0 λ`, `λ < N_ω(F)`, is a system `hgdLvTU` with the bound `N_ω(F)`, base gate `γ`, base reading
`N_ω(F(x))`, bound field `evZ(N_ω(F(x)))` above `γ` and `Z_o(x)` below.  The tower `t_0 = 0`,
`t_{k+1} = φ(ω, F + 1 + t_k)` is cofinal in `N_ω(F)`, its readings `r_{k+1}(x) = ϑˣ(Ω₁·ω + F(x) + r_k(x))` (by the
specification of the `ω`-step) are cofinal in `N_ω(F(x))` and its starts have base gate below every base above `γ`.
The union extends the start, reads it, and every code in `[F, N_ω(F))` with gate below a base forces `γ` below it
(`hgdLvTU_high`).

* `hgdLvTt`, `hgdLvTt_cof`, `hgdLvTt_gate`, `hgdLvTr`, `hgdLvTr_succ`, `hgdLvTr_cof`; `hgdLvTN`, `hgdLvTR`, `hgdLvTg`,
  `hgdLvTZ`,
  `hgdLvT_small`, `hgdLvT_high`, `hgdLvTU` (**THE SYSTEM AT `N_ω(F)`**), `hgdLvTU_R0`, `hgdLvTU_g0`, `hgdLvTU_high`.

No new axiom.  New definitions: `hgdLvTt`, `hgdLvTr`, `hgdLvTN`, `hgdLvTR`, `hgdLvTg`, `hgdLvTZ`, `hgdLvTU`.
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

variable (A : HgdA)

/-- **The tower of offsets**: `t_0 = 0`, `t_{k+1} = φ(2, F + 1 + t_k)`. -/
noncomputable def hgdLvTt : ℕ → Ordinal.{0}
  | 0 => 0
  | k + 1 => veblen ω (A.F + 1 + hgdLvTt k)

theorem hgdLvTt_lt : ∀ k : ℕ, hgdLvTt A k < hcNw A.F
  | 0 => hgdLv_zero_lt_N A
  | k + 1 => A.Q_lt_N (hgdLvTt_lt k)

theorem hgdLvTt_lt_succ (k : ℕ) : hgdLvTt A k < hgdLvTt A (k + 1) := A.lt_Q (hgdLvTt_lt A k)

theorem hgdLvTt_iter (n : ℕ) : (veblen ω)^[n] (A.F + 1) ≤ hgdLvTt A (n + 1) := by
  induction n with
  | zero =>
    show A.F + 1 ≤ veblen ω (A.F + 1 + 0)
    rw [add_zero]; exact right_le_veblen ω _
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    show veblen ω _ ≤ veblen ω (A.F + 1 + hgdLvTt A (n + 1))
    exact (isNormal_veblen ω).monotone (ih.trans le_add_self)

theorem hgdLv_N_nfp : hcNw A.F = nfp (veblen ω) (A.F + 1) := rfl

/-- **The tower is cofinal in `N(F)`.** -/
theorem hgdLvTt_cof {c : Ordinal.{0}} (hc : c < hcNw A.F) : ∃ k : ℕ, c < hgdLvTt A k := by
  rw [hgdLv_N_nfp] at hc
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hc
  exact ⟨n + 1, hn.trans_le (hgdLvTt_iter A n)⟩

variable {S0 : HgVD} (hS : HgdLvStart A S0)
include hS

theorem hgdLvTt_B (k : ℕ) : (hgdLvU A S0 (hgdLvTt A k)).B = hgdLvTt A (k + 1) := hgdLvU_B hS (hgdLvTt_lt A k)

/-- **Every start `hgdLvU A S0 t_k` has base gate below every base above `γ_F`.** -/
theorem hgdLvTt_gate : ∀ (k : ℕ) (x : Ordinal.{0}), InE x → x < Om1 → A.γ < x → (hgdLvU A S0 (hgdLvTt A k)).γ < x
  | 0, x, hx, hx1, hA => by
    show (hgdLvU A S0 0).γ < x
    rw [hgdLvU_γ_iff hS (hgdLv_zero_lt_N A) hx hx1, (hgdLvU A S0 0).g_zero, max_eq_left zero_le]; exact hA
  | k + 1, x, hx, hx1, hA => by
    set l := hgdLvTt A k with hl
    have hlT : l < hcNw A.F := hgdLvTt_lt A k
    have hl'T : hgdLvTt A (k + 1) < hcNw A.F := hgdLvTt_lt A (k + 1)
    have hsp := hgdLvU_succ_spec hS hlT
    have hl1 : l + 1 ≤ hgdLvTt A (k + 1) := Order.add_one_le_of_lt (hgdLvTt_lt_succ A k)
    have hl1T : l + 1 < hcNw A.F := hl1.trans_lt hl'T
    have hB : hgdLvTt A (k + 1) = (hgdLvU A S0 l).B := (hgdLvTt_B A hS k).symm
    have hcB : hgdLvTt A (k + 1) < (hgdLvU A S0 (l + 1)).B := by
      rw [hgdLvU_B hS hl1T, hB, hgdLvU_B hS hlT]; exact A.Q_lt_Q (lt_add_one l)
    rw [hgdLvU_γ_iff hS hl'T hx hx1, (hgdLv_ext hS hl1 hl'T).2 _ hcB, hB, hgdLvU_B hS hlT]
    refine max_lt hA ((hsp.gF x hx hx1).2 ?_)
    exact max_lt hA ((max_lt_iff.1 ((hgdLvU_γ_iff hS hlT hx hx1).1 (hgdLvTt_gate k x hx hx1 hA))).2)

end Tower

/-- The reading of the tower code `t_k` (in its start). -/
noncomputable def hgdLvTr (A : HgdA) (S0 : HgVD) (k : ℕ) (x : Ordinal.{0}) : Ordinal.{0} :=
  (hgdLvU A S0 (hgdLvTt A k)).R (hgdLvTt A k) x

section TowerRead

variable {A : HgdA} {S0 : HgVD} (hS : HgdLvStart A S0) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hA : A.γ < x)
include hS hx hx1 hA

theorem hgdLvTt_g (k : ℕ) : (hgdLvU A S0 (hgdLvTt A k)).g (hgdLvTt A k) < x :=
  (max_lt_iff.1 ((hgdLvU_γ_iff hS (hgdLvTt_lt A k) hx hx1).1 (hgdLvTt_gate A hS k x hx hx1 hA))).2

/-- **`r_{k+1}(x) = ϑˣ(Ω₁·2 + F(x) + r_k(x))`**: the code `t_{k+1} = Q_{t_k}` is read as the base reading of the start
`t_k`. -/
theorem hgdLvTr_succ (k : ℕ) :
    hgdLvTr A S0 (k + 1) x = glA ω (A.Fr x + hgdLvTr A S0 k x) x := by
  set l := hgdLvTt A k with hl
  have hlT : l < hcNw A.F := hgdLvTt_lt A k
  have hl'T : hgdLvTt A (k + 1) < hcNw A.F := hgdLvTt_lt A (k + 1)
  have hsp := hgdLvU_succ_spec hS hlT
  have hl1 : l + 1 ≤ hgdLvTt A (k + 1) := Order.add_one_le_of_lt (hgdLvTt_lt_succ A k)
  have hl1T : l + 1 < hcNw A.F := hl1.trans_lt hl'T
  have hB : hgdLvTt A (k + 1) = (hgdLvU A S0 l).B := (hgdLvTt_B A hS k).symm
  have hcB : hgdLvTt A (k + 1) < (hgdLvU A S0 (l + 1)).B := by
    rw [hgdLvU_B hS hl1T, hB, hgdLvU_B hS hlT]; exact A.Q_lt_Q (lt_add_one l)
  have hg : max A.γ ((hgdLvU A S0 l).g l) < x := max_lt hA (hgdLvTt_g hS hx hx1 hA k)
  unfold hgdLvTr
  rw [(hgdLv_ext hS hl1 hl'T).1 _ x hcB, hB, hgdLvU_B hS hlT]
  exact hsp.RF x hx hx1 hg

theorem hgdLvTr_zero : hgdLvTr A S0 0 x = 0 := by unfold hgdLvTr; exact (hgdLvU A S0 (hgdLvTt A 0)).R_zero x

theorem hgdLvTr_lt_N (k : ℕ) : hgdLvTr A S0 k x < hcNw (A.Fr x) :=
  A.lvR_lt_N _ (hgdLvU_Zb hS (hgdLvTt_lt A k)) (hgdLvU_self hS (hgdLvTt_lt A k)) hx hx1 hA
    (hgdLvTt_g hS hx hx1 hA k)

/-- **The iterates of `φ(ω, ·)` from `hcS(F(x)) + 1` lie below the tower readings.** -/
theorem hgdLvTr_iter (n : ℕ) :
    (veblen ω)^[n] (hcS (A.Fr x) + 1) ≤ hgdLvTr A S0 (n + 2) x := by
  obtain ⟨i0, hi0⟩ := hcS_LuP (A.Fr x)
  have hstep : ∀ k : ℕ, hgdLvTr A S0 (k + 1) x = veblen ω
      (i0 + hgdLvTr A S0 k x) := fun k => by
    rw [hgdLvTr_succ hS hx hx1 hA k, A.lvglAV hx hx1 hA hi0 (hgdLvTr_lt_N hS hx hx1 hA k)]
  have h1 : hgdLvTr A S0 1 x = hcS (A.Fr x) := by
    rw [hstep 0, hgdLvTr_zero hS hx hx1 hA, add_zero, hi0]
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply]
    refine Order.add_one_le_of_lt ?_
    rw [hstep 1, h1]
    refine (le_add_self : hcS (A.Fr x) ≤ i0 + hcS (A.Fr x)).trans_lt ?_
    have h2 := hgdLvTr_lt_N hS hx hx1 hA 2
    rw [hstep 1, h1] at h2
    exact hc_nofixW (by rw [hi0]; exact hcS_gt _) le_self_add h2
  | succ n ih =>
    rw [Function.iterate_succ_apply', hstep (n + 2)]
    exact (isNormal_veblen ω).monotone (ih.trans le_add_self)

/-- **The tower readings are cofinal in `N_ω(F(x))`.** -/
theorem hgdLvTr_cof {v : Ordinal.{0}} (hv : v < hcNw (A.Fr x)) : ∃ k : ℕ, v < hgdLvTr A S0 k x := by
  have e : hcNw (A.Fr x) = nfp (veblen ω) (hcS (A.Fr x) + 1) := by
    refine le_antisymm ?_ ?_
    · exact hcNw_le (nfp_fp (isNormal_veblen _) _)
        ((hcS_gt (A.Fr x)).trans ((lt_add_one _).trans_le (le_nfp _ _)))
    · exact nfp_le_fp (isNormal_veblen ω).strictMono.monotone
        (Order.add_one_le_of_lt (hdS_lt_Nw (hcNw_gt (A.Fr x)))) (hcNw_fix _).le
  rw [e] at hv
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hv
  exact ⟨n + 2, hn.trans_le (hgdLvTr_iter hS hx hx1 hA n)⟩

end TowerRead

/-! ## The union of all offsets -/

section Union

variable (A : HgdA) (S0 : HgVD)

/-- The first start containing `c`. -/
noncomputable def hgdLvTN (c : Ordinal.{0}) : Ordinal.{0} := sInf {ν | ν < hcNw A.F ∧ c < (hgdLvU A S0 ν).B}

/-- The reading of the union. -/
noncomputable def hgdLvTR (c x : Ordinal.{0}) : Ordinal.{0} := (hgdLvU A S0 (hgdLvTN A S0 c)).R c x

/-- The gate of the union. -/
noncomputable def hgdLvTg (c : Ordinal.{0}) : Ordinal.{0} := (hgdLvU A S0 (hgdLvTN A S0 c)).g c

open Classical in
/-- The bound field of the union: `evZ(N_ω(F(x)))` above `γ`, `Z_o(x)` below. -/
noncomputable def hgdLvTZ (x : Ordinal.{0}) : Ordinal.{0} :=
  if A.γ < x then evZ (hcNw (A.Fr x)) else A.Zo x

variable {A S0} (hS : HgdLvStart A S0)
include hS

theorem hgdLvT_cof {c : Ordinal.{0}} (hc : c < hcNw A.F) : ∃ ν, ν < hcNw A.F ∧ c <
    (hgdLvU A S0 ν).B := by
  obtain ⟨k, hk⟩ := hgdLvTt_cof A hc
  exact ⟨hgdLvTt A k, hgdLvTt_lt A k, hk.trans (by rw [hgdLvTt_B A hS k]; exact hgdLvTt_lt_succ A k)⟩

omit hS in
theorem hgdLvTN_spec {c ν : Ordinal.{0}} (hν : ν < hcNw A.F) (hc : c < (hgdLvU A S0 ν).B) :
    hgdLvTN A S0 c ≤ ν ∧ hgdLvTN A S0 c < hcNw A.F ∧ c < (hgdLvU A S0 (hgdLvTN A S0 c)).B := by
  have hne : ({ν | ν < hcNw A.F ∧ c < (hgdLvU A S0 ν).B} : Set Ordinal.{0}).Nonempty := ⟨ν, hν, hc⟩
  have hm := csInf_mem hne
  exact ⟨csInf_le' ⟨hν, hc⟩, hm.1, hm.2⟩

omit hS in
theorem hgdLvTN_min {c μ : Ordinal.{0}} (hμ : μ < hgdLvTN A S0 c) (hμl : μ < hcNw A.F) : ¬ c <
    (hgdLvU A S0 μ).B :=
  fun hcμ => absurd (csInf_le' ⟨hμl, hcμ⟩ : hgdLvTN A S0 c ≤ μ) (not_le.2 hμ)

theorem hgdLvT_B_lt {ν : Ordinal.{0}} (hν : ν < hcNw A.F) : (hgdLvU A S0 ν).B < hcNw A.F := by
  rw [hgdLvU_B hS hν]; exact A.Q_lt_N hν

theorem hgdLvTN_high {c : Ordinal.{0}} (hc : hcNw A.F ≤ c) : hgdLvTN A S0 c = 0 := by
  unfold hgdLvTN
  have he : ({ν | ν < hcNw A.F ∧ c < (hgdLvU A S0 ν).B} : Set Ordinal.{0}) = ∅ := by
    ext ν
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hν hcν
    exact absurd (hcν.trans (hgdLvT_B_lt hS hν)) (not_lt.2 hc)
  rw [he]; exact Ordinal.sInf_empty

theorem hgdLvTR_eq {c ν : Ordinal.{0}} (hν : ν < hcNw A.F) (hc : c < (hgdLvU A S0 ν).B) (x : Ordinal.{0}) :
    hgdLvTR A S0 c x = (hgdLvU A S0 ν).R c x := by
  obtain ⟨h1, -, h3⟩ := hgdLvTN_spec hν hc
  exact ((hgdLv_ext hS h1 hν).1 c x h3).symm

theorem hgdLvTg_eq {c ν : Ordinal.{0}} (hν : ν < hcNw A.F) (hc : c < (hgdLvU A S0 ν).B) :
    hgdLvTg A S0 c = (hgdLvU A S0 ν).g c := by
  obtain ⟨h1, -, h3⟩ := hgdLvTN_spec hν hc
  exact ((hgdLv_ext hS h1 hν).2 c h3).symm

theorem hgdLvTR_succ (c x : Ordinal.{0}) : hgdLvTR A S0 (c + 1) x = hgdLvTR A S0 c x + 1 := by
  rcases lt_or_ge c (hcNw A.F) with h | h
  · obtain ⟨n, hn1, hn⟩ := hgdLvT_cof hS (A.N_lim.add_one_lt h)
    rw [hgdLvTR_eq hS hn1 hn, hgdLvTR_eq hS hn1 ((lt_add_one c).trans hn), (hgdLvU A S0 n).R_succ]
  · unfold hgdLvTR
    rw [hgdLvTN_high hS h, hgdLvTN_high hS (h.trans (le_self_add (a := c) (b := 1))), (hgdLvU A S0 0).R_succ]

theorem hgdLvTg_le_succ (c : Ordinal.{0}) : hgdLvTg A S0 c ≤ hgdLvTg A S0 (c + 1) := by
  rcases lt_or_ge c (hcNw A.F) with h | h
  · obtain ⟨n, hn1, hn⟩ := hgdLvT_cof hS (A.N_lim.add_one_lt h)
    rw [hgdLvTg_eq hS hn1 hn, hgdLvTg_eq hS hn1 ((lt_add_one c).trans hn)]; exact (hgdLvU A S0 n).g_le_succ c
  · unfold hgdLvTg
    rw [hgdLvTN_high hS h, hgdLvTN_high hS (h.trans (le_self_add (a := c) (b := 1)))]; exact
        (hgdLvU A S0 0).g_le_succ c

/-- **A code of the union with gate below a base `σ > γ_F` lies in a start with base gate below `σ`.** -/
theorem hgdLvT_small {c σ : Ordinal.{0}} (hc : c < hcNw A.F) (hσ : InE σ) (hσ1 : σ < Om1) (hAσ : A.γ < σ)
    (hg : hgdLvTg A S0 c < σ) : ∃ μ, μ < hcNw A.F ∧ c < (hgdLvU A S0 μ).B ∧ (hgdLvU A S0 μ).γ < σ := by
  obtain ⟨n, hn1, hn⟩ := hgdLvT_cof hS hc
  obtain ⟨-, hN1, hcN⟩ := hgdLvTN_spec hn1 hn
  have hgN : hgdLvTg A S0 c = (hgdLvU A S0 (hgdLvTN A S0 c)).g c := rfl
  have I := hgdLv_inv hS _ hN1
  rcases zero_or_succ_or_isSuccLimit (hgdLvTN A S0 c) with h0 | ⟨m, hm⟩ | hlim
  · refine ⟨hgdLvTN A S0 c, hN1, hcN, ?_⟩
    rw [h0, hgdLvU_γ_iff hS (hgdLv_zero_lt_N A) hσ hσ1, (hgdLvU A S0 0).g_zero, max_eq_left zero_le]
    exact hAσ
  · have hm' : hgdLvTN A S0 c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < hgdLvTN A S0 c := by rw [hm']; exact lt_add_one m
    have hml : m < hcNw A.F := hmN.trans hN1
    have hBc : (hgdLvU A S0 m).B ≤ c := not_lt.1 (hgdLvTN_min hmN hml)
    refine ⟨hgdLvTN A S0 c, hN1, hcN, ?_⟩
    rw [hgN, hm'] at hg
    rw [hm'] at hcN I ⊢
    exact I.high m (lt_add_one _) c σ hBc hcN hσ hσ1 hg
  · exfalso
    rw [hgdLvU_B hS hN1] at hcN
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen ω).lt_iff_exists_lt
        (isSuccLimit_add _ hlim)).1 hcN
    obtain ⟨d, hd, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    have hdl : d < hcNw A.F := hd.trans hN1
    refine hgdLvTN_min hd hdl ?_
    rw [hgdLvU_B hS hdl]; exact hct.trans_le ((isNormal_veblen ω).monotone htd)

/-- **A code `c ∈ [F, N(F))` of the union with gate below a base `σ` forces `γ_F < σ`.** -/
theorem hgdLvT_high {c σ : Ordinal.{0}} (hc : c < hcNw A.F) (hFc : A.F ≤ c) (hσ : InE σ) (hσ1 : σ < Om1)
    (hg : hgdLvTg A S0 c < σ) : A.γ < σ := by
  obtain ⟨n, hn1, hn⟩ := hgdLvT_cof hS hc
  obtain ⟨-, hN1, hcN⟩ := hgdLvTN_spec hn1 hn
  have hgN : hgdLvTg A S0 c = (hgdLvU A S0 (hgdLvTN A S0 c)).g c := rfl
  have I := hgdLv_inv hS _ hN1
  rcases zero_or_succ_or_isSuccLimit (hgdLvTN A S0 c) with h0 | ⟨m, hm⟩ | hlim
  · rw [hgN, h0, hgdLvU_zero] at hg
    rw [h0, hgdLvU_zero] at hcN
    exact hS.high0 c σ hFc hcN hσ hσ1 hg
  · have hm' : hgdLvTN A S0 c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < hgdLvTN A S0 c := by rw [hm']; exact lt_add_one m
    have hml : m < hcNw A.F := hmN.trans hN1
    have hBc : (hgdLvU A S0 m).B ≤ c := not_lt.1 (hgdLvTN_min hmN hml)
    rw [hgN, hm'] at hg
    rw [hm'] at hcN I hN1
    have hγ := I.high m (lt_add_one _) c σ hBc hcN hσ hσ1 hg
    exact (max_lt_iff.1 ((hgdLvU_γ_iff hS hN1 hσ hσ1).1 hγ)).1
  · exfalso
    rw [hgdLvU_B hS hN1] at hcN
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen ω).lt_iff_exists_lt
        (isSuccLimit_add _ hlim)).1 hcN
    obtain ⟨d, hd, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    have hdl : d < hcNw A.F := hd.trans hN1
    refine hgdLvTN_min hd hdl ?_
    rw [hgdLvU_B hS hdl]; exact hct.trans_le ((isNormal_veblen ω).monotone htd)

/-- **`b_μ(x) < N(F(x))`** for every start with base gate below `x`. -/
theorem hgdLvT_b_lt {μ x : Ordinal.{0}} (hμ : μ < hcNw A.F) (hx : InE x) (hx1 : x < Om1) (hγ :
    (hgdLvU A S0 μ).γ < x) :
    (hgdLvU A S0 μ).b x < hcNw (A.Fr x) := by
  have hg : max A.γ ((hgdLvU A S0 μ).g μ) < x := (hgdLvU_γ_iff hS hμ hx hx1).1 hγ
  have hA : A.γ < x := (max_lt_iff.1 hg).1
  rw [(hgdLvU_start hS hμ).b x hx hx1 hg]
  exact A.glA_lt_N hx hx1 hA (A.lvR_lt_N _ (hgdLvU_Zb hS hμ) (hgdLvU_self hS hμ) hx hx1 hA (max_lt_iff.1 hg).2)

omit hS in
theorem hgdLvTZ_fix (x : Ordinal.{0}) : veblen 1 (hgdLvTZ A x) = hgdLvTZ A x := by
  unfold hgdLvTZ; split_ifs
  · exact epsilon_evZ _
  · exact ha_fix1_of_fix2 (A.Zo_fix x)

omit hS in
theorem hgdLvTZ_G1 (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : hgdLvTZ A x < gq 1 x := by
  unfold hgdLvTZ; split_ifs with h
  · exact (hb_evZ_lt_fix2 (A.Zo_fix x) (A.N_Zo hx hx1 h)).trans (A.Zo_G1 x hx hx1)
  · exact A.Zo_G1 x hx hx1

omit hS in
theorem hgdLvTZ_ge (x : Ordinal.{0}) : A.Zl x ≤ hgdLvTZ A x := by
  unfold hgdLvTZ HgdA.Zl; split_ifs
  · exact (lt_evZ _).le
  · exact le_rfl

/-- **THE SYSTEM AT `N(F)`**: the union of all starts `hgdLvU A S0 λ`, `λ < N(F)`: bound `N(F)`, base gate `γ_F`, base
reading `N(F(x))`, bound field `hgdLvTZ`. -/
noncomputable def hgdLvTU : HgVD where
  B := hcNw A.F
  γ := A.γ
  γ_lt := A.γ_lt
  γ_cl := fun Z hZ hZ1 h => A.N_cl Z hZ hZ1 h
  γ_G := fun h => absurd h (A.G_le.trans_lt A.F_lt_N).ne'
  R := hgdLvTR A S0
  g := hgdLvTg A S0
  b := fun x => hcNw (A.Fr x)
  ba := fun x => hcNw (A.Fr x)
  ix := hcNw A.F
  Z := hgdLvTZ A
  B_E := A.N_E
  G_le := (A.G_le.trans_lt A.F_lt_N).le
  B_lt1 := A.N_lt1
  B_ix := (hdNw_fix1 A.F).symm
  Z_fix := fun x _ _ => hgdLvTZ_fix x
  Z_G1 := hgdLvTZ_G1
  ix_mem := fun S _ _ ha hb => A.N_mem S ha hb
  g_lt := fun c hc => by
    obtain ⟨n, hn1, hn⟩ := hgdLvT_cof hS hc
    rw [hgdLvTg_eq hS hn1 hn]; exact (hgdLvU A S0 n).g_lt c hn
  g_zero := by
    rw [hgdLvTg_eq hS (hgdLv_zero_lt_N A) (hgdLvU A S0 0).B_pos]; exact (hgdLvU A S0 0).g_zero
  g_nat := fun k => by
    rw [hgdLvTg_eq hS (hgdLv_zero_lt_N A) ((hgdLvU A S0 0).nat_lt_B k)]; exact (hgdLvU A S0 0).g_nat k
  g_E := by rw [hgdLvTg_eq hS (hgdLv_zero_lt_N A) (hgdLvU A S0 0).E_lt_B]; exact (hgdLvU A S0 0).g_E
  g_lowE := fun c hc => by
    rw [hgdLvTg_eq hS (hgdLv_zero_lt_N A) (hc.trans (hgdLvU A S0 0).E_lt_B)]; exact (hgdLvU A S0 0).g_lowE c hc
  g_G0 := fun h => by
    obtain ⟨n, hn1, hn⟩ := hgdLvT_cof hS h
    rw [hgdLvTg_eq hS hn1 hn]; exact (hgdLvU A S0 n).g_G0 hn
  g_add := fun Z hZ hωZ x y hxy hgx hgy => by
    obtain ⟨n, hn1, hn⟩ := hgdLvT_cof hS hxy
    have hx : x < (hgdLvU A S0 n).B := lt_of_le_of_lt le_self_add hn
    have hy : y < (hgdLvU A S0 n).B := lt_of_le_of_lt le_add_self hn
    rw [hgdLvTg_eq hS hn1 hn]; rw [hgdLvTg_eq hS hn1 hx] at hgx; rw [hgdLvTg_eq hS hn1 hy] at hgy
    exact (hgdLvU A S0 n).g_add Z hZ hωZ x y hn hgx hgy
  g_opow := fun Z hZw hωZ y hy hg => by
    obtain ⟨n, hn1, hn⟩ := hgdLvT_cof hS hy
    have hy' : y < (hgdLvU A S0 n).B := lt_of_le_of_lt (right_le_opow y one_lt_omega0) hn
    rw [hgdLvTg_eq hS hn1 hn]; rw [hgdLvTg_eq hS hn1 hy'] at hg
    exact (hgdLvU A S0 n).g_opow Z hZw hωZ y hn hg
  code_gate := fun Z hZ1 hZ0 hZa hZp At hAt c hc hcB => by
    obtain ⟨n, hn1, hn⟩ := hgdLvT_cof hS hcB
    rw [hgdLvTg_eq hS hn1 hn]
    exact (hgdLvU A S0 n).code_gate Z hZ1 hZ0 hZa hZp At (fun s hs => (hAt s hs).imp_right
      (fun h => (hgdLvT_B_lt hS hn1).le.trans h)) c hc hn
  g_succ := fun Z hZ c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hgdLvT_cof hS hc
    have hc' : c < (hgdLvU A S0 n).B := (lt_add_one c).trans hn
    rw [hgdLvTg_eq hS hn1 hn]; rw [hgdLvTg_eq hS hn1 hc'] at hg
    exact (hgdLvU A S0 n).g_succ Z hZ c hn hg
  g_le_succ := hgdLvTg_le_succ hS
  mem := fun S a b ha c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hgdLvT_cof hS hc
    rw [hgdLvTg_eq hS hn1 hn] at hg
    exact (hgdLvU A S0 n).mem S a b ha c hn hg
  R_zero := fun x => by
    rw [hgdLvTR_eq hS (hgdLv_zero_lt_N A) (hgdLvU A S0 0).B_pos]; exact (hgdLvU A S0 0).R_zero x
  R_nat := fun k x => by
    rw [hgdLvTR_eq hS (hgdLv_zero_lt_N A) ((hgdLvU A S0 0).nat_lt_B k)]; exact (hgdLvU A S0 0).R_nat k x
  R_E := fun x => by rw [hgdLvTR_eq hS (hgdLv_zero_lt_N A) (hgdLvU A S0 0).E_lt_B]; exact (hgdLvU A S0 0).R_E x
  R_succ := hgdLvTR_succ hS
  R_pos := fun x hx hx1 c hc0 hc hg => by
    obtain ⟨n, hn1, hn⟩ := hgdLvT_cof hS hc
    rw [hgdLvTR_eq hS hn1 hn]; rw [hgdLvTg_eq hS hn1 hn] at hg
    exact (hgdLvU A S0 n).R_pos x hx hx1 c hc0 hn hg
  R_omega := fun x hx hx1 c hω hc hg => by
    obtain ⟨n, hn1, hn⟩ := hgdLvT_cof hS hc
    rw [hgdLvTR_eq hS hn1 hn]; rw [hgdLvTg_eq hS hn1 hn] at hg
    exact (hgdLvU A S0 n).R_omega x hx hx1 c hω hn hg
  R_lt_b := fun x hx hx1 hγx c hc hg => by
    obtain ⟨μ, hμ, hcμ, hγμ⟩ := hgdLvT_small hS hc hx hx1 hγx hg
    rw [hgdLvTR_eq hS hμ hcμ]; rw [hgdLvTg_eq hS hμ hcμ] at hg
    exact ((hgdLvU A S0 μ).R_lt_b x hx hx1 hγμ c hcμ hg).trans (hgdLvT_b_lt hS hμ hx hx1 hγμ)
  R_lt_Z := fun x hx hx1 c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hgdLvT_cof hS hc
    rw [hgdLvTR_eq hS hn1 hn]; rw [hgdLvTg_eq hS hn1 hn] at hg
    exact (((hgdLvU A S0 n).R_lt_Z x hx hx1 c hn hg).trans_le (hgdLvU_Zb hS hn1 x hx hx1)).trans_le (hgdLvTZ_ge x)
  mono := fun x hx hx1 c hc d hdc hgc hgd => by
    obtain ⟨n, hn1, hn⟩ := hgdLvT_cof hS hc
    have hd : d < (hgdLvU A S0 n).B := hdc.trans hn
    rw [hgdLvTR_eq hS hn1 hn,
        hgdLvTR_eq hS hn1 hd]; rw [hgdLvTg_eq hS hn1 hn] at hgc; rw [hgdLvTg_eq hS hn1 hd] at hgd
    exact (hgdLvU A S0 n).mono x hx hx1 c hn d hdc hgc hgd
  cof := fun x hx hx1 c hc hg ν hν => by
    obtain ⟨n, hn1, hn⟩ := hgdLvT_cof hS hc
    rw [hgdLvTR_eq hS hn1 hn] at hν; rw [hgdLvTg_eq hS hn1 hn] at hg
    obtain ⟨d, hdc, hgd, hνd⟩ := (hgdLvU A S0 n).cof x hx hx1 c hn hg ν hν
    have hd : d < (hgdLvU A S0 n).B := hdc.trans hn
    exact ⟨d, hdc, by rw [hgdLvTg_eq hS hn1 hd]; exact hgd, by rw [hgdLvTR_eq hS hn1 hd]; exact hνd⟩
  b_cof := fun x hx hx1 hγx ν hν => by
    obtain ⟨k, hk⟩ := hgdLvTr_cof hS hx hx1 hγx hν
    have hkT : hgdLvTt A k < hcNw A.F := hgdLvTt_lt A k
    have hkB : hgdLvTt A k < (hgdLvU A S0 (hgdLvTt A k)).B := hgdLvU_self hS hkT
    refine ⟨hgdLvTt A k, hkT, ?_, ?_⟩
    · rw [hgdLvTg_eq hS hkT hkB]; exact hgdLvTt_g hS hx hx1 hγx k
    · rw [hgdLvTR_eq hS hkT hkB]; exact hk
  b_E := fun x _ _ _ => hcNw_E _
  x_lt_b := fun x hx hx1 hγx => (A.Fr_gt hx hx1 hγx).trans (A.Fr_lt_N x)
  b_eN := fun x hx hx1 hγx => gz_eN_fix hx hx1 (hdNw_fix1 _)
    ((A.Fr_gt hx hx1 hγx).trans (A.Fr_lt_N x)) (A.N_lt1x hx hx1 hγx)
  ba_lt := fun x hx hx1 hγx => A.N_lt1x hx hx1 hγx
  b_Z := fun x _ _ hγx => by
    show _ < hgdLvTZ A x
    unfold hgdLvTZ; rw [if_pos hγx]
    exact go_eN_lt_evZ (lt_evZ _)
  b_pi := fun _ _ hB hγ => A.N_pi hB hγ
  ba_pi := fun _ _ hB hγ => A.N_pi hB hγ
  ex := fun σ ρ hB c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hgdLvT_cof hS hc
    rw [hgdLvTR_eq hS hn1 hn, hgdLvTR_eq hS hn1 hn]; rw [hgdLvTg_eq hS hn1 hn] at hg
    exact (hgdLvU A S0 n).ex σ ρ hB c hn hg
  dig := fun σ ρ hB hγσ d hd hg P P' hat => by
    obtain ⟨μ, hμ, hdμ, hγμ⟩ := hgdLvT_small hS hd hB.1 (hB.2.2.1.trans hB.2.2.2) hγσ hg
    rw [hgdLvTR_eq hS hμ hdμ, hgdLvTR_eq hS hμ hdμ]; rw [hgdLvTg_eq hS hμ hdμ] at hg
    exact (hgdLvU A S0 μ).dig σ ρ hB hγμ d hdμ hg P P' (fun β hβ hβe =>
      hat β hβ (hβe.trans (hgdLvT_b_lt hS hμ hB.2.1 hB.2.2.2 (hγμ.trans hB.2.2.1))))
  ld := fun c hl hc => by
    obtain ⟨n, hn1, hn⟩ := hgdLvT_cof hS hc
    obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := (hgdLvU A S0 n).ld c hl hn
    have hcpn : cp < (hgdLvU A S0 n).B := hcp.trans hn
    refine ⟨cp, lp, T, hcp, by rw [hgdLvTg_eq hS hn1 hn, hgdLvTg_eq hS hn1 hcpn]; exact hgcp,
        fun x hx hx1 hg => ?_,
      fun σ ρ hB hg => hex σ ρ hB (by rw [← hgdLvTg_eq hS hn1 hn]; exact hg)⟩
    rw [hgdLvTg_eq hS hn1 hn] at hg
    rw [hgdLvTR_eq hS hn1 hn, hgdLvTR_eq hS hn1 hcpn]
    exact hdec x hx hx1 hg

theorem hgdLvTU_B : (hgdLvTU hS).B = hcNw A.F := rfl

theorem hgdLvTU_γ : (hgdLvTU hS).γ = A.γ := rfl

theorem hgdLvTU_b (x : Ordinal.{0}) : (hgdLvTU hS).b x = hcNw (A.Fr x) := rfl

/-- **The union extends every start** (readings). -/
theorem hgdLvTU_R {ν c : Ordinal.{0}} (hν : ν < hcNw A.F) (hc : c < (hgdLvU A S0 ν).B) (x : Ordinal.{0}) :
    (hgdLvTU hS).R c x = (hgdLvU A S0 ν).R c x := hgdLvTR_eq hS hν hc x

/-- **The union extends every start** (gates). -/
theorem hgdLvTU_g {ν c : Ordinal.{0}} (hν : ν < hcNw A.F) (hc : c < (hgdLvU A S0 ν).B) :
    (hgdLvTU hS).g c = (hgdLvU A S0 ν).g c := hgdLvTg_eq hS hν hc

/-- **The union extends the start `S0`.** -/
theorem hgdLvTU_R0 {c : Ordinal.{0}} (hc : c < S0.B) (x : Ordinal.{0}) : (hgdLvTU hS).R c x = S0.R c x := by
  rw [hgdLvTU_R hS (hgdLv_zero_lt_N A) (by rw [hgdLvU_zero]; exact hc), hgdLvU_zero]

theorem hgdLvTU_g0 {c : Ordinal.{0}} (hc : c < S0.B) : (hgdLvTU hS).g c = S0.g c := by
  rw [hgdLvTU_g hS (hgdLv_zero_lt_N A) (by rw [hgdLvU_zero]; exact hc), hgdLvU_zero]

/-- **A code `c ∈ [F, N(F))` of the union with gate below a base `σ` forces the base gate below `σ`.** -/
theorem hgdLvTU_high {c σ : Ordinal.{0}} (hc : c < hcNw A.F) (hFc : A.F ≤ c) (hσ : InE σ) (hσ1 : σ < Om1)
    (hg : (hgdLvTU hS).g c < σ) : (hgdLvTU hS).γ < σ := hgdLvT_high hS hc hFc hσ hσ1 hg

end Union

end Googology.Trans.PoR.InaccPsi.R2.Hg

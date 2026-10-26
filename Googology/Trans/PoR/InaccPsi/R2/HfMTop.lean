import Googology.Trans.PoR.InaccPsi.R2.HfMRec

/-!
# HfMTop: THE UNION OF ALL OFFSETS OF A BASE OF EVERY COUNTABLE LEVEL `α`: THE TOWER TO `N_α(F) = φ(α+1, F+1)`

The level-`α` version of `Hd.HdLvTop`, for any step `St` of level `α` with the specification.  For a base
`A : Hf.HfB α` and a start `S0`, the union of all starts `Hf.hfMU St A S0 λ`, `λ < N_α(F)`, is a system `hfMTU` with
the bound `N_α(F)`, base gate `γN`, base reading `N_α(F(x))`, bound field `evZ(N_α(F(x)))` above `γN` and `Z_o(x)`
below; the tower `t_0 = 0`, `t_{k+1} = φ(α, F + 1 + t_k)` is cofinal in `N_α(F)` and its readings are cofinal in
`N_α(F(x))`; the union extends the start, reads it, and a code in `[F, N(F))` with gate below `σ` forces the CODE
gate `γ` below `σ` (`hfMT_high`); when the two gates agree (`γN = γ`, every base `Hf.HfQ.toB`), the base gate `γN`
of the union (`hfMTU_high`).

* `hfMTt`, `hfMTt_cof`, `hfMTt_gate`, `hfMTr`, `hfMTr_succ`, `hfMTr_cof`; `hfMTN`, `hfMTR`, `hfMTg`, `hfMTZ`,
  `hfMT_small`, `hfMT_high`, `hfMTU` (**THE SYSTEM AT `N_α(F)`, EVERY COUNTABLE LEVEL**), `hfMTU_R0`, `hfMTU_g0`,
  `hfMTU_high`.

No new axiom.  New definitions: `hfMTt`, `hfMTr`, `hfMTN`, `hfMTR`, `hfMTg`, `hfMTZ`, `hfMTU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hf

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

variable {α : Ordinal.{0}} (A : HfB α)

/-- **The tower of offsets**: `t_0 = 0`, `t_{k+1} = φ(2, F + 1 + t_k)`. -/
noncomputable def hfMTt : ℕ → Ordinal.{0}
  | 0 => 0
  | k + 1 => veblen α (A.F + 1 + hfMTt k)

theorem hfMTt_lt : ∀ k : ℕ, hfMTt A k < hcN α A.F
  | 0 => hfM_zero_lt_N A
  | k + 1 => A.Q_lt_N (hfMTt_lt k)

theorem hfMTt_lt_succ (k : ℕ) : hfMTt A k < hfMTt A (k + 1) := A.lt_Q (hfMTt_lt A k)

theorem hfMTt_iter (n : ℕ) : (veblen α)^[n] (A.F + 1) ≤ hfMTt A (n + 1) := by
  induction n with
  | zero =>
    show A.F + 1 ≤ veblen α (A.F + 1 + 0)
    rw [add_zero]; exact right_le_veblen α _
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    show veblen α _ ≤ veblen α (A.F + 1 + hfMTt A (n + 1))
    exact (isNormal_veblen α).monotone (ih.trans le_add_self)

theorem hfM_N_nfp : hcN α A.F = nfp (veblen α) (A.F + 1) := rfl

/-- **The tower is cofinal in `N(F)`.** -/
theorem hfMTt_cof {c : Ordinal.{0}} (hc : c < hcN α A.F) : ∃ k : ℕ, c < hfMTt A k := by
  rw [hfM_N_nfp] at hc
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hc
  exact ⟨n + 1, hn.trans_le (hfMTt_iter A n)⟩

variable {St : ∀ (Q : HfQ α) (U : HcVD), HcSStart (hfQPB Q) U → HcVD} {S0 : HcVD}
  (hSt : ∀ Q U h, HfQSpec Q U (St Q U h)) (hS : HfMStart A S0)
include hSt hS

theorem hfMTt_B (k : ℕ) : (hfMU St A S0 (hfMTt A k)).B = hfMTt A (k + 1) := hfMU_B hSt hS (hfMTt_lt A k)

/-- **Every start `hfMU St A S0 t_k` has base gate below every base above `γN`.** -/
theorem hfMTt_gate : ∀ (k : ℕ) (x : Ordinal.{0}), InE x → x < Om1 → A.γN < x → (hfMU St A S0 (hfMTt A k)).γ < x
  | 0, x, hx, hx1, hA => by
    show (hfMU St A S0 0).γ < x
    rw [hfMU_γ_iff hSt hS (hfM_zero_lt_N A) hx hx1, (hfMU St A S0 0).g_zero, max_eq_left zero_le]; exact hA
  | k + 1, x, hx, hx1, hA => by
    set l := hfMTt A k with hl
    have hlT : l < hcN α A.F := hfMTt_lt A k
    have hl'T : hfMTt A (k + 1) < hcN α A.F := hfMTt_lt A (k + 1)
    have hsp := hfMU_succ_spec hSt hS hlT
    have hl1 : l + 1 ≤ hfMTt A (k + 1) := Order.add_one_le_of_lt (hfMTt_lt_succ A k)
    have hl1T : l + 1 < hcN α A.F := hl1.trans_lt hl'T
    have hB : hfMTt A (k + 1) = (hfMU St A S0 l).B := (hfMTt_B A hSt hS k).symm
    have hcB : hfMTt A (k + 1) < (hfMU St A S0 (l + 1)).B := by
      rw [hfMU_B hSt hS hl1T, hB, hfMU_B hSt hS hlT]; exact A.Q_lt_Q (lt_add_one l)
    rw [hfMU_γ_iff hSt hS hl'T hx hx1, (hfM_ext hSt hS hl1 hl'T).2 _ hcB, hB, hfMU_B hSt hS hlT]
    refine max_lt hA ((hsp.gF x hx hx1).2 ?_)
    exact max_lt hA ((max_lt_iff.1 ((hfMU_γ_iff hSt hS hlT hx hx1).1 (hfMTt_gate k x hx hx1 hA))).2)

end Tower

/-- The reading of the tower code `t_k` (in its start). -/
noncomputable def hfMTr {α : Ordinal.{0}} (St : ∀ (Q : HfQ α) (U : HcVD), HcSStart (hfQPB Q) U → HcVD) (A : HfB α)
    (S0 : HcVD) (k : ℕ)
    (x : Ordinal.{0}) : Ordinal.{0} := (hfMU St A S0 (hfMTt A k)).R (hfMTt A k) x

section TowerRead

variable {α : Ordinal.{0}} {St : ∀ (Q : HfQ α) (U : HcVD), HcSStart (hfQPB Q) U → HcVD}
  (hSt : ∀ Q U h, HfQSpec Q U (St Q U h))
  {A : HfB α} {S0 : HcVD} (hS : HfMStart A S0) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hA : A.γN < x)
include hSt hS hx hx1 hA

theorem hfMTt_g (k : ℕ) : (hfMU St A S0 (hfMTt A k)).g (hfMTt A k) < x :=
  (max_lt_iff.1 ((hfMU_γ_iff hSt hS (hfMTt_lt A k) hx hx1).1 (hfMTt_gate A hSt hS k x hx hx1 hA))).2

/-- **`r_{k+1}(x) = ϑˣ(Ω₁·2 + F(x) + r_k(x))`**: the code `t_{k+1} = Q_{t_k}` is read as the base reading of the start
`t_k`. -/
theorem hfMTr_succ (k : ℕ) :
    hfMTr St A S0 (k + 1) x = glA α (A.Fr x + hfMTr St A S0 k x) x := by
  set l := hfMTt A k with hl
  have hlT : l < hcN α A.F := hfMTt_lt A k
  have hl'T : hfMTt A (k + 1) < hcN α A.F := hfMTt_lt A (k + 1)
  have hsp := hfMU_succ_spec hSt hS hlT
  have hl1 : l + 1 ≤ hfMTt A (k + 1) := Order.add_one_le_of_lt (hfMTt_lt_succ A k)
  have hl1T : l + 1 < hcN α A.F := hl1.trans_lt hl'T
  have hB : hfMTt A (k + 1) = (hfMU St A S0 l).B := (hfMTt_B A hSt hS k).symm
  have hcB : hfMTt A (k + 1) < (hfMU St A S0 (l + 1)).B := by
    rw [hfMU_B hSt hS hl1T, hB, hfMU_B hSt hS hlT]; exact A.Q_lt_Q (lt_add_one l)
  have hg : max A.γN ((hfMU St A S0 l).g l) < x := max_lt hA (hfMTt_g hSt hS hx hx1 hA k)
  unfold hfMTr
  rw [(hfM_ext hSt hS hl1 hl'T).1 _ x hcB, hB, hfMU_B hSt hS hlT]
  exact hsp.RF x hx hx1 hg

theorem hfMTr_zero : hfMTr St A S0 0 x = 0 := by unfold hfMTr; exact (hfMU St A S0 (hfMTt A 0)).R_zero x

theorem hfMTr_lt_N (k : ℕ) : hfMTr St A S0 k x < hcN α (A.Fr x) :=
  A.lvR_lt_N _ (hfMU_Zb hSt hS (hfMTt_lt A k)) (hfMU_self hSt hS (hfMTt_lt A k)) hx hx1 hA
    (hfMTt_g hSt hS hx hx1 hA k)

/-- **The iterates of `φ(α, ·)` from `hdNx α (F(x)) + 1` lie below the tower readings.** -/
theorem hfMTr_iter (n : ℕ) :
    (veblen α)^[n] (hdNx α (A.Fr x) + 1) ≤ hfMTr St A S0 (n + 2) x := by
  obtain ⟨i0, hi0⟩ := hdNx_LuP α (A.Fr x)
  have hstep : ∀ k : ℕ, hfMTr St A S0 (k + 1) x = veblen α
      (i0 + hfMTr St A S0 k x) := fun k => by
    rw [hfMTr_succ hSt hS hx hx1 hA k, A.lvglAV hx hx1 hA hi0 (hfMTr_lt_N hSt hS hx hx1 hA k)]
  have h1 : hfMTr St A S0 1 x = hdNx α (A.Fr x) := by
    rw [hstep 0, hfMTr_zero hSt hS hx hx1 hA, add_zero, hi0]
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply]
    refine Order.add_one_le_of_lt ?_
    rw [hstep 1, h1]
    refine (le_add_self : hdNx α (A.Fr x) ≤ i0 + hdNx α (A.Fr x)).trans_lt ?_
    have h2 := hfMTr_lt_N hSt hS hx hx1 hA 2
    rw [hstep 1, h1] at h2
    exact hc_nofixG (by rw [hi0]; exact hdNx_gt _ _) le_self_add h2
  | succ n ih =>
    rw [Function.iterate_succ_apply', hstep (n + 2)]
    exact (isNormal_veblen α).monotone (ih.trans le_add_self)

/-- **The tower readings are cofinal in `N_α(F(x))`.** -/
theorem hfMTr_cof {v : Ordinal.{0}} (hv : v < hcN α (A.Fr x)) : ∃ k : ℕ, v < hfMTr St A S0 k x := by
  have e : hcN α (A.Fr x) = nfp (veblen α) (hdNx α (A.Fr x) + 1) := by
    refine le_antisymm ?_ ?_
    · exact hcN_le (nfp_fp (isNormal_veblen _) _)
        ((hdNx_gt α (A.Fr x)).trans ((lt_add_one _).trans_le (le_nfp _ _)))
    · exact nfp_le_fp (isNormal_veblen α).strictMono.monotone
        (Order.add_one_le_of_lt (hdNx_lt_N (hcN_gt α (A.Fr x)))) (hcN_fix α _).le
  rw [e] at hv
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hv
  exact ⟨n + 2, hn.trans_le (hfMTr_iter hSt hS hx hx1 hA n)⟩

end TowerRead

/-! ## The union of all offsets -/

section Union

variable {α : Ordinal.{0}} (St : ∀ (Q : HfQ α) (U : HcVD), HcSStart (hfQPB Q) U → HcVD) (A : HfB α) (S0 : HcVD)

/-- The first start containing `c`. -/
noncomputable def hfMTN (c : Ordinal.{0}) : Ordinal.{0} := sInf {ν | ν < hcN α A.F ∧ c < (hfMU St A S0 ν).B}

/-- The reading of the union. -/
noncomputable def hfMTR (c x : Ordinal.{0}) : Ordinal.{0} := (hfMU St A S0 (hfMTN St A S0 c)).R c x

/-- The gate of the union. -/
noncomputable def hfMTg (c : Ordinal.{0}) : Ordinal.{0} := (hfMU St A S0 (hfMTN St A S0 c)).g c

open Classical in
/-- The bound field of the union: `evZ(N_α(F(x)))` above `γ`, `Z_o(x)` below. -/
noncomputable def hfMTZ (x : Ordinal.{0}) : Ordinal.{0} :=
  if A.γN < x then evZ (hcN α (A.Fr x)) else A.Zo x

variable {St A S0} (hSt : ∀ Q U h, HfQSpec Q U (St Q U h)) (hS : HfMStart A S0)
include hSt hS

theorem hfMT_cof {c : Ordinal.{0}} (hc : c < hcN α A.F) : ∃ ν, ν < hcN α A.F ∧ c <
    (hfMU St A S0 ν).B := by
  obtain ⟨k, hk⟩ := hfMTt_cof A hc
  exact ⟨hfMTt A k, hfMTt_lt A k, hk.trans (by rw [hfMTt_B A hSt hS k]; exact hfMTt_lt_succ A k)⟩

omit hSt hS in
theorem hfMTN_spec {c ν : Ordinal.{0}} (hν : ν < hcN α A.F) (hc : c < (hfMU St A S0 ν).B) :
    hfMTN St A S0 c ≤ ν ∧ hfMTN St A S0 c < hcN α A.F ∧ c < (hfMU St A S0 (hfMTN St A S0 c)).B := by
  have hne : ({ν | ν < hcN α A.F ∧ c < (hfMU St A S0 ν).B} : Set Ordinal.{0}).Nonempty := ⟨ν, hν, hc⟩
  have hm := csInf_mem hne
  exact ⟨csInf_le' ⟨hν, hc⟩, hm.1, hm.2⟩

omit hSt hS in
theorem hfMTN_min {c μ : Ordinal.{0}} (hμ : μ < hfMTN St A S0 c) (hμl : μ < hcN α A.F) : ¬ c <
    (hfMU St A S0 μ).B :=
  fun hcμ => absurd (csInf_le' ⟨hμl, hcμ⟩ : hfMTN St A S0 c ≤ μ) (not_le.2 hμ)

theorem hfMT_B_lt {ν : Ordinal.{0}} (hν : ν < hcN α A.F) : (hfMU St A S0 ν).B < hcN α A.F := by
  rw [hfMU_B hSt hS hν]; exact A.Q_lt_N hν

theorem hfMTN_high {c : Ordinal.{0}} (hc : hcN α A.F ≤ c) : hfMTN St A S0 c = 0 := by
  unfold hfMTN
  have he : ({ν | ν < hcN α A.F ∧ c < (hfMU St A S0 ν).B} : Set Ordinal.{0}) = ∅ := by
    ext ν
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hν hcν
    exact absurd (hcν.trans (hfMT_B_lt hSt hS hν)) (not_lt.2 hc)
  rw [he]; exact Ordinal.sInf_empty

theorem hfMTR_eq {c ν : Ordinal.{0}} (hν : ν < hcN α A.F) (hc : c < (hfMU St A S0 ν).B) (x : Ordinal.{0}) :
    hfMTR St A S0 c x = (hfMU St A S0 ν).R c x := by
  obtain ⟨h1, -, h3⟩ := hfMTN_spec hν hc
  exact ((hfM_ext hSt hS h1 hν).1 c x h3).symm

theorem hfMTg_eq {c ν : Ordinal.{0}} (hν : ν < hcN α A.F) (hc : c < (hfMU St A S0 ν).B) :
    hfMTg St A S0 c = (hfMU St A S0 ν).g c := by
  obtain ⟨h1, -, h3⟩ := hfMTN_spec hν hc
  exact ((hfM_ext hSt hS h1 hν).2 c h3).symm

theorem hfMTR_succ (c x : Ordinal.{0}) : hfMTR St A S0 (c + 1) x = hfMTR St A S0 c x + 1 := by
  rcases lt_or_ge c (hcN α A.F) with h | h
  · obtain ⟨n, hn1, hn⟩ := hfMT_cof hSt hS (A.N_lim.add_one_lt h)
    rw [hfMTR_eq hSt hS hn1 hn, hfMTR_eq hSt hS hn1 ((lt_add_one c).trans hn), (hfMU St A S0 n).R_succ]
  · unfold hfMTR
    rw [hfMTN_high hSt hS h, hfMTN_high hSt hS (h.trans (le_self_add (a := c) (b := 1))), (hfMU St A S0 0).R_succ]

theorem hfMTg_le_succ (c : Ordinal.{0}) : hfMTg St A S0 c ≤ hfMTg St A S0 (c + 1) := by
  rcases lt_or_ge c (hcN α A.F) with h | h
  · obtain ⟨n, hn1, hn⟩ := hfMT_cof hSt hS (A.N_lim.add_one_lt h)
    rw [hfMTg_eq hSt hS hn1 hn, hfMTg_eq hSt hS hn1 ((lt_add_one c).trans hn)]; exact (hfMU St A S0 n).g_le_succ c
  · unfold hfMTg
    rw [hfMTN_high hSt hS h, hfMTN_high hSt hS (h.trans (le_self_add (a := c) (b := 1)))]; exact
        (hfMU St A S0 0).g_le_succ c

/-- **A code of the union with gate below a base `σ > γ_F` lies in a start with base gate below `σ`.** -/
theorem hfMT_small {c σ : Ordinal.{0}} (hc : c < hcN α A.F) (hσ : InE σ) (hσ1 : σ < Om1) (hAσ : A.γN < σ)
    (hg : hfMTg St A S0 c < σ) : ∃ μ, μ < hcN α A.F ∧ c < (hfMU St A S0 μ).B ∧ (hfMU St A S0 μ).γ < σ := by
  obtain ⟨n, hn1, hn⟩ := hfMT_cof hSt hS hc
  obtain ⟨-, hN1, hcNc⟩ := hfMTN_spec hn1 hn
  have hgN : hfMTg St A S0 c = (hfMU St A S0 (hfMTN St A S0 c)).g c := rfl
  have I := hfM_inv hSt hS _ hN1
  rcases zero_or_succ_or_isSuccLimit (hfMTN St A S0 c) with h0 | ⟨m, hm⟩ | hlim
  · refine ⟨hfMTN St A S0 c, hN1, hcNc, ?_⟩
    rw [h0, hfMU_γ_iff hSt hS (hfM_zero_lt_N A) hσ hσ1, (hfMU St A S0 0).g_zero, max_eq_left zero_le]
    exact hAσ
  · have hm' : hfMTN St A S0 c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < hfMTN St A S0 c := by rw [hm']; exact lt_add_one m
    have hml : m < hcN α A.F := hmN.trans hN1
    have hBc : (hfMU St A S0 m).B ≤ c := not_lt.1 (hfMTN_min hmN hml)
    refine ⟨hfMTN St A S0 c, hN1, hcNc, ?_⟩
    rw [hgN, hm'] at hg
    rw [hm'] at hcNc I ⊢
    exact I.high m (lt_add_one _) c σ hBc hcNc hσ hσ1 hg
  · exfalso
    rw [hfMU_B hSt hS hN1] at hcNc
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen α).lt_iff_exists_lt
        (isSuccLimit_add _ hlim)).1 hcNc
    obtain ⟨d, hf, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    have hfl : d < hcN α A.F := hf.trans hN1
    refine hfMTN_min hf hfl ?_
    rw [hfMU_B hSt hS hfl]; exact hct.trans_le ((isNormal_veblen α).monotone htd)

/-- **A code `c ∈ [F, N(F))` of the union with gate below a base `σ` forces `γ_F < σ`.** -/
theorem hfMT_high {c σ : Ordinal.{0}} (hc : c < hcN α A.F) (hFc : A.F ≤ c) (hσ : InE σ) (hσ1 : σ < Om1)
    (hg : hfMTg St A S0 c < σ) : A.γ < σ := by
  obtain ⟨n, hn1, hn⟩ := hfMT_cof hSt hS hc
  obtain ⟨-, hN1, hcNc⟩ := hfMTN_spec hn1 hn
  have hgN : hfMTg St A S0 c = (hfMU St A S0 (hfMTN St A S0 c)).g c := rfl
  have I := hfM_inv hSt hS _ hN1
  rcases zero_or_succ_or_isSuccLimit (hfMTN St A S0 c) with h0 | ⟨m, hm⟩ | hlim
  · rw [hgN, h0, hfMU_zero] at hg
    rw [h0, hfMU_zero] at hcNc
    exact hS.high0 c σ hFc hcNc hσ hσ1 hg
  · have hm' : hfMTN St A S0 c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < hfMTN St A S0 c := by rw [hm']; exact lt_add_one m
    have hml : m < hcN α A.F := hmN.trans hN1
    have hBc : (hfMU St A S0 m).B ≤ c := not_lt.1 (hfMTN_min hmN hml)
    rw [hgN, hm'] at hg
    rw [hm'] at hcNc I hN1
    have hγ := I.high m (lt_add_one _) c σ hBc hcNc hσ hσ1 hg
    exact A.γ_le.trans_lt (max_lt_iff.1 ((hfMU_γ_iff hSt hS hN1 hσ hσ1).1 hγ)).1
  · exfalso
    rw [hfMU_B hSt hS hN1] at hcNc
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen α).lt_iff_exists_lt
        (isSuccLimit_add _ hlim)).1 hcNc
    obtain ⟨d, hf, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    have hfl : d < hcN α A.F := hf.trans hN1
    refine hfMTN_min hf hfl ?_
    rw [hfMU_B hSt hS hfl]; exact hct.trans_le ((isNormal_veblen α).monotone htd)

/-- **`b_μ(x) < N(F(x))`** for every start with base gate below `x`. -/
theorem hfMT_b_lt {μ x : Ordinal.{0}} (hμ : μ < hcN α A.F) (hx : InE x) (hx1 : x < Om1) (hγ :
    (hfMU St A S0 μ).γ < x) :
    (hfMU St A S0 μ).b x < hcN α (A.Fr x) := by
  have hg : max A.γN ((hfMU St A S0 μ).g μ) < x := (hfMU_γ_iff hSt hS hμ hx hx1).1 hγ
  have hA : A.γN < x := (max_lt_iff.1 hg).1
  rw [(hfMU_start hSt hS hμ).b x hx hx1 hg]
  exact A.glA_lt_N hx hx1 hA (A.lvR_lt_N _ (hfMU_Zb hSt hS hμ) (hfMU_self hSt hS hμ) hx hx1 hA (max_lt_iff.1 hg).2)

omit hSt hS in
theorem hfMTZ_fix (x : Ordinal.{0}) : veblen 1 (hfMTZ A x) = hfMTZ A x := by
  unfold hfMTZ; split_ifs
  · exact epsilon_evZ _
  · exact ha_fix1_of_fix2 (A.Zo_fix x)

omit hSt hS in
theorem hfMTZ_BR (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : hfMTZ A x ≤ hcBR x := by
  unfold hfMTZ; split_ifs with h
  · exact (hb_evZ_lt_fix2 (A.Zo_fix x) (A.N_Zo hx hx1 h)).le.trans (A.Zo_BR x hx hx1)
  · exact A.Zo_BR x hx hx1

omit hSt hS in
theorem hfMTZ_ge (x : Ordinal.{0}) : A.Zl x ≤ hfMTZ A x := by
  unfold hfMTZ HfB.Zl; split_ifs
  · exact (lt_evZ _).le
  · exact le_rfl

/-- **THE SYSTEM AT `N(F)`**: the union of all starts `hfMU St A S0 λ`, `λ < N(F)`: bound `N(F)`, base gate `γN`, base
reading `N(F(x))`, bound field `hfMTZ`. -/
noncomputable def hfMTU : HcVD where
  B := hcN α A.F
  γ := A.γN
  γ_lt := A.γN_lt
  γ_cl := fun Z hZ hZ1 h => A.N_cl Z hZ hZ1 h
  γ_G := fun h => absurd h (A.G_le.trans_lt A.F_lt_N).ne'
  R := hfMTR St A S0
  g := hfMTg St A S0
  b := fun x => hcN α (A.Fr x)
  ba := fun x => hcN α (A.Fr x)
  ix := hcN α A.F
  Z := hfMTZ A
  B_E := A.N_E
  G_le := (A.G_le.trans_lt A.F_lt_N).le
  B_lt1 := A.N_lt1
  B_ix := (hc_fix_down A.lv.one_le (hcN_fix α A.F)).symm
  Z_fix := fun x _ _ => hfMTZ_fix x
  Z_BR := hfMTZ_BR
  ix_mem := fun S _ _ ha hb => A.N_mem S ha hb
  g_lt := fun c hc => by
    obtain ⟨n, hn1, hn⟩ := hfMT_cof hSt hS hc
    rw [hfMTg_eq hSt hS hn1 hn]; exact (hfMU St A S0 n).g_lt c hn
  g_zero := by
    rw [hfMTg_eq hSt hS (hfM_zero_lt_N A) (hfMU St A S0 0).B_pos]; exact (hfMU St A S0 0).g_zero
  g_nat := fun k => by
    rw [hfMTg_eq hSt hS (hfM_zero_lt_N A) ((hfMU St A S0 0).nat_lt_B k)]; exact (hfMU St A S0 0).g_nat k
  g_E := by rw [hfMTg_eq hSt hS (hfM_zero_lt_N A) (hfMU St A S0 0).E_lt_B]; exact (hfMU St A S0 0).g_E
  g_lowE := fun c hc => by
    rw [hfMTg_eq hSt hS (hfM_zero_lt_N A) (hc.trans (hfMU St A S0 0).E_lt_B)]; exact (hfMU St A S0 0).g_lowE c hc
  g_G0 := fun h => by
    obtain ⟨n, hn1, hn⟩ := hfMT_cof hSt hS h
    rw [hfMTg_eq hSt hS hn1 hn]; exact (hfMU St A S0 n).g_G0 hn
  g_add := fun Z hZ hωZ x y hxy hgx hgy => by
    obtain ⟨n, hn1, hn⟩ := hfMT_cof hSt hS hxy
    have hx : x < (hfMU St A S0 n).B := lt_of_le_of_lt le_self_add hn
    have hy : y < (hfMU St A S0 n).B := lt_of_le_of_lt le_add_self hn
    rw [hfMTg_eq hSt hS hn1 hn]; rw [hfMTg_eq hSt hS hn1 hx] at hgx; rw [hfMTg_eq hSt hS hn1 hy] at hgy
    exact (hfMU St A S0 n).g_add Z hZ hωZ x y hn hgx hgy
  g_opow := fun Z hZw hωZ y hy hg => by
    obtain ⟨n, hn1, hn⟩ := hfMT_cof hSt hS hy
    have hy' : y < (hfMU St A S0 n).B := lt_of_le_of_lt (right_le_opow y one_lt_omega0) hn
    rw [hfMTg_eq hSt hS hn1 hn]; rw [hfMTg_eq hSt hS hn1 hy'] at hg
    exact (hfMU St A S0 n).g_opow Z hZw hωZ y hn hg
  code_gate := fun Z hZ1 hZ0 hZa hZp At hAt c hc hcB => by
    obtain ⟨n, hn1, hn⟩ := hfMT_cof hSt hS hcB
    rw [hfMTg_eq hSt hS hn1 hn]
    exact (hfMU St A S0 n).code_gate Z hZ1 hZ0 hZa hZp At (fun s hs => (hAt s hs).imp_right
      (fun h => (hfMT_B_lt hSt hS hn1).le.trans h)) c hc hn
  g_succ := fun Z hZ c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hfMT_cof hSt hS hc
    have hc' : c < (hfMU St A S0 n).B := (lt_add_one c).trans hn
    rw [hfMTg_eq hSt hS hn1 hn]; rw [hfMTg_eq hSt hS hn1 hc'] at hg
    exact (hfMU St A S0 n).g_succ Z hZ c hn hg
  g_le_succ := hfMTg_le_succ hSt hS
  mem := fun S a b ha c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hfMT_cof hSt hS hc
    rw [hfMTg_eq hSt hS hn1 hn] at hg
    exact (hfMU St A S0 n).mem S a b ha c hn hg
  R_zero := fun x => by
    rw [hfMTR_eq hSt hS (hfM_zero_lt_N A) (hfMU St A S0 0).B_pos]; exact (hfMU St A S0 0).R_zero x
  R_nat := fun k x => by
    rw [hfMTR_eq hSt hS (hfM_zero_lt_N A) ((hfMU St A S0 0).nat_lt_B k)]; exact (hfMU St A S0 0).R_nat k x
  R_E := fun x => by rw [hfMTR_eq hSt hS (hfM_zero_lt_N A) (hfMU St A S0 0).E_lt_B]; exact (hfMU St A S0 0).R_E x
  R_succ := hfMTR_succ hSt hS
  R_pos := fun x hx hx1 c hc0 hc hg => by
    obtain ⟨n, hn1, hn⟩ := hfMT_cof hSt hS hc
    rw [hfMTR_eq hSt hS hn1 hn]; rw [hfMTg_eq hSt hS hn1 hn] at hg
    exact (hfMU St A S0 n).R_pos x hx hx1 c hc0 hn hg
  R_omega := fun x hx hx1 c hω hc hg => by
    obtain ⟨n, hn1, hn⟩ := hfMT_cof hSt hS hc
    rw [hfMTR_eq hSt hS hn1 hn]; rw [hfMTg_eq hSt hS hn1 hn] at hg
    exact (hfMU St A S0 n).R_omega x hx hx1 c hω hn hg
  R_lt_b := fun x hx hx1 hγx c hc hg => by
    obtain ⟨μ, hμ, hcμ, hγμ⟩ := hfMT_small hSt hS hc hx hx1 hγx hg
    rw [hfMTR_eq hSt hS hμ hcμ]; rw [hfMTg_eq hSt hS hμ hcμ] at hg
    exact ((hfMU St A S0 μ).R_lt_b x hx hx1 hγμ c hcμ hg).trans (hfMT_b_lt hSt hS hμ hx hx1 hγμ)
  R_lt_Z := fun x hx hx1 c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hfMT_cof hSt hS hc
    rw [hfMTR_eq hSt hS hn1 hn]; rw [hfMTg_eq hSt hS hn1 hn] at hg
    exact (((hfMU St A S0 n).R_lt_Z x hx hx1 c hn hg).trans_le (hfMU_Zb hSt hS hn1 x hx hx1)).trans_le (hfMTZ_ge x)
  mono := fun x hx hx1 c hc d hfc hgc hgd => by
    obtain ⟨n, hn1, hn⟩ := hfMT_cof hSt hS hc
    have hf : d < (hfMU St A S0 n).B := hfc.trans hn
    rw [hfMTR_eq hSt hS hn1 hn,
        hfMTR_eq hSt hS hn1 hf]; rw [hfMTg_eq hSt hS hn1 hn] at hgc; rw [hfMTg_eq hSt hS hn1 hf] at hgd
    exact (hfMU St A S0 n).mono x hx hx1 c hn d hfc hgc hgd
  cof := fun x hx hx1 c hc hg ν hν => by
    obtain ⟨n, hn1, hn⟩ := hfMT_cof hSt hS hc
    rw [hfMTR_eq hSt hS hn1 hn] at hν; rw [hfMTg_eq hSt hS hn1 hn] at hg
    obtain ⟨d, hfc, hgd, hνd⟩ := (hfMU St A S0 n).cof x hx hx1 c hn hg ν hν
    have hf : d < (hfMU St A S0 n).B := hfc.trans hn
    exact ⟨d, hfc, by rw [hfMTg_eq hSt hS hn1 hf]; exact hgd, by rw [hfMTR_eq hSt hS hn1 hf]; exact hνd⟩
  b_cof := fun x hx hx1 hγx ν hν => by
    obtain ⟨k, hk⟩ := hfMTr_cof hSt hS hx hx1 hγx hν
    have hkT : hfMTt A k < hcN α A.F := hfMTt_lt A k
    have hkB : hfMTt A k < (hfMU St A S0 (hfMTt A k)).B := hfMU_self hSt hS hkT
    refine ⟨hfMTt A k, hkT, ?_, ?_⟩
    · rw [hfMTg_eq hSt hS hkT hkB]; exact hfMTt_g hSt hS hx hx1 hγx k
    · rw [hfMTR_eq hSt hS hkT hkB]; exact hk
  b_E := fun x _ _ _ => hcN_E α _
  x_lt_b := fun x hx hx1 hγx => (A.Fr_gt hx hx1 hγx).trans (A.Fr_lt_N x)
  b_eN := fun x hx hx1 hγx => gz_eN_fix hx hx1 (hc_fix_down A.lv.one_le (hcN_fix α _))
    ((A.Fr_gt hx hx1 hγx).trans (A.Fr_lt_N x)) (A.N_lt1x hx hx1 hγx)
  ba_lt := fun x hx hx1 hγx => A.N_lt1x hx hx1 hγx
  b_Z := fun x _ _ hγx => by
    show _ < hfMTZ A x
    unfold hfMTZ; rw [if_pos hγx]
    exact go_eN_lt_evZ (lt_evZ _)
  b_pi := fun _ _ hB hγ => A.N_pi hB hγ
  ba_pi := fun _ _ hB hγ => A.N_pi hB hγ
  ex := fun σ ρ hB c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hfMT_cof hSt hS hc
    rw [hfMTR_eq hSt hS hn1 hn, hfMTR_eq hSt hS hn1 hn]; rw [hfMTg_eq hSt hS hn1 hn] at hg
    exact (hfMU St A S0 n).ex σ ρ hB c hn hg
  dig := fun σ ρ hB hγσ d hf hg P P' hat => by
    obtain ⟨μ, hμ, hfμ, hγμ⟩ := hfMT_small hSt hS hf hB.1 (hB.2.2.1.trans hB.2.2.2) hγσ hg
    rw [hfMTR_eq hSt hS hμ hfμ, hfMTR_eq hSt hS hμ hfμ]; rw [hfMTg_eq hSt hS hμ hfμ] at hg
    exact (hfMU St A S0 μ).dig σ ρ hB hγμ d hfμ hg P P' (fun β hβ hβe =>
      hat β hβ (hβe.trans (hfMT_b_lt hSt hS hμ hB.2.1 hB.2.2.2 (hγμ.trans hB.2.2.1))))
  ld := fun c hl hc => by
    obtain ⟨n, hn1, hn⟩ := hfMT_cof hSt hS hc
    obtain ⟨cp, lp, T, hcp, hgcp, hfec, hex⟩ := (hfMU St A S0 n).ld c hl hn
    have hcpn : cp < (hfMU St A S0 n).B := hcp.trans hn
    refine ⟨cp, lp, T, hcp, by rw [hfMTg_eq hSt hS hn1 hn, hfMTg_eq hSt hS hn1 hcpn]; exact hgcp,
        fun x hx hx1 hg => ?_,
      fun σ ρ hB hg => hex σ ρ hB (by rw [← hfMTg_eq hSt hS hn1 hn]; exact hg)⟩
    rw [hfMTg_eq hSt hS hn1 hn] at hg
    rw [hfMTR_eq hSt hS hn1 hn, hfMTR_eq hSt hS hn1 hcpn]
    exact hfec x hx hx1 hg

theorem hfMTU_B : (hfMTU hSt hS).B = hcN α A.F := rfl

theorem hfMTU_γ : (hfMTU hSt hS).γ = A.γN := rfl

theorem hfMTU_b (x : Ordinal.{0}) : (hfMTU hSt hS).b x = hcN α (A.Fr x) := rfl

/-- **The union extends every start** (readings). -/
theorem hfMTU_R {ν c : Ordinal.{0}} (hν : ν < hcN α A.F) (hc : c < (hfMU St A S0 ν).B) (x : Ordinal.{0}) :
    (hfMTU hSt hS).R c x = (hfMU St A S0 ν).R c x := hfMTR_eq hSt hS hν hc x

/-- **The union extends every start** (gates). -/
theorem hfMTU_g {ν c : Ordinal.{0}} (hν : ν < hcN α A.F) (hc : c < (hfMU St A S0 ν).B) :
    (hfMTU hSt hS).g c = (hfMU St A S0 ν).g c := hfMTg_eq hSt hS hν hc

/-- **The union extends the start `S0`.** -/
theorem hfMTU_R0 {c : Ordinal.{0}} (hc : c < S0.B) (x : Ordinal.{0}) : (hfMTU hSt hS).R c x = S0.R c x := by
  rw [hfMTU_R hSt hS (hfM_zero_lt_N A) (by rw [hfMU_zero]; exact hc), hfMU_zero]

theorem hfMTU_g0 {c : Ordinal.{0}} (hc : c < S0.B) : (hfMTU hSt hS).g c = S0.g c := by
  rw [hfMTU_g hSt hS (hfM_zero_lt_N A) (by rw [hfMU_zero]; exact hc), hfMU_zero]

/-- **A code `c ∈ [F, N(F))` of the union with gate below a base `σ` forces the base gate below `σ`.** -/
theorem hfMTU_high (hγN : A.γN = A.γ) {c σ : Ordinal.{0}} (hc : c < hcN α A.F) (hFc : A.F ≤ c) (hσ : InE σ)
    (hσ1 : σ < Om1) (hg : (hfMTU hSt hS).g c < σ) : (hfMTU hSt hS).γ < σ := by
  show A.γN < σ
  rw [hγN]; exact hfMT_high hSt hS hc hFc hσ hσ1 hg

end Union

end Googology.Trans.PoR.InaccPsi.R2.Hf

import Googology.Trans.PoR.InaccPsi.R2.HiVRec

/-!
# HiVTop: THE UNION OF ALL OFFSETS OF A BASE OF THE LEVEL `Ω₁ + ν`: THE TOWER TO `N_{Ω₁+ν}(F) = φ(Ω₁+ν+1, F+1)`

The port of `Hg.HgfMTop` to the level `Ω₁ + ν` read as `x + ν`: for a base `A : Hi.HiVB ν` and a start `S0`, the union
of all starts `Hi.hiVU St A S0 λ`, `λ < N_{Ω₁+ν}(F)`, is a system `hiVTU` with the bound `N_{Ω₁+ν}(F)`, base gate
`γN`, base reading `N_{x+ν}(F(x))`, bound field `evZ(N_{x+ν}(F(x)))` above `γN` and `Z_o(x)` below; the tower
`t_0 = 0`, `t_{k+1} = φ(Ω₁+ν, F + 1 + t_k)` is cofinal in `N_{Ω₁+ν}(F)` and its readings are cofinal in
`N_{x+ν}(F(x))`; a code in `[F, N(F))` with gate below `σ` forces the CODE gate `γ` below `σ` (`hiVT_high`).

* `hiVTt`, `hiVTt_cof`, `hiVTt_gate`, `hiVTr`, `hiVTr_succ`, `hiVTr_cof`; `hiVTN`, `hiVTR`, `hiVTg`, `hiVTZ`,
  `hiVT_small`, `hiVT_high`, `hiVTU` (**THE SYSTEM AT `N_{Ω₁+ν}(F)`**), `hiVTU_R0`, `hiVTU_g0`, `hiVTU_high`.

No new axiom.  New definitions: `hiVTt`, `hiVTr`, `hiVTN`, `hiVTR`, `hiVTg`, `hiVTZ`, `hiVTU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hi

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

/-! ## The tower of offsets -/

section Tower

variable {κ : Ordinal.{0}} (A : HiVB κ)

/-- **The tower of offsets**: `t_0 = 0`, `t_{k+1} = φ(2, F + 1 + t_k)`. -/
noncomputable def hiVTt : ℕ → Ordinal.{0}
  | 0 => 0
  | k + 1 => veblen (Om1 + κ) (A.F + 1 + hiVTt k)

theorem hiVTt_lt : ∀ k : ℕ, hiVTt A k < hcN (Om1 + κ) A.F
  | 0 => hiV_zero_lt_N A
  | k + 1 => A.Q_lt_N (hiVTt_lt k)

theorem hiVTt_lt_succ (k : ℕ) : hiVTt A k < hiVTt A (k + 1) := A.lt_Q (hiVTt_lt A k)

theorem hiVTt_iter (n : ℕ) : (veblen (Om1 + κ))^[n] (A.F + 1) ≤ hiVTt A (n + 1) := by
  induction n with
  | zero =>
    show A.F + 1 ≤ veblen (Om1 + κ) (A.F + 1 + 0)
    rw [add_zero]; exact right_le_veblen (Om1 + κ) _
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    show veblen (Om1 + κ) _ ≤ veblen (Om1 + κ) (A.F + 1 + hiVTt A (n + 1))
    exact (isNormal_veblen (Om1 + κ)).monotone (ih.trans le_add_self)

theorem hiV_N_nfp : hcN (Om1 + κ) A.F = nfp (veblen (Om1 + κ)) (A.F + 1) := rfl

/-- **The tower is cofinal in `N(F)`.** -/
theorem hiVTt_cof {c : Ordinal.{0}} (hc : c < hcN (Om1 + κ) A.F) : ∃ k : ℕ, c < hiVTt A k := by
  rw [hiV_N_nfp] at hc
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hc
  exact ⟨n + 1, hn.trans_le (hiVTt_iter A n)⟩

variable {St : ∀ (Q : HiVQ κ) (U : HgVD), HgSStart (hiVPB Q) U → HgVD} {S0 : HgVD}
  (hSt : ∀ Q U h, HiVSpec Q U (St Q U h)) (hS : HiVStart A S0)
include hSt hS

theorem hiVTt_B (k : ℕ) : (hiVU St A S0 (hiVTt A k)).B = hiVTt A (k + 1) := hiVU_B hSt hS (hiVTt_lt A k)

/-- **Every start `hiVU St A S0 t_k` has base gate below every base above `γN`.** -/
theorem hiVTt_gate : ∀ (k : ℕ) (x : Ordinal.{0}), InE x → x < Om1 → A.γN < x → (hiVU St A S0 (hiVTt A k)).γ < x
  | 0, x, hx, hx1, hA => by
    show (hiVU St A S0 0).γ < x
    rw [hiVU_γ_iff hSt hS (hiV_zero_lt_N A) hx hx1, (hiVU St A S0 0).g_zero, max_eq_left zero_le]; exact hA
  | k + 1, x, hx, hx1, hA => by
    set l := hiVTt A k with hl
    have hlT : l < hcN (Om1 + κ) A.F := hiVTt_lt A k
    have hl'T : hiVTt A (k + 1) < hcN (Om1 + κ) A.F := hiVTt_lt A (k + 1)
    have hsp := hiVU_succ_spec hSt hS hlT
    have hl1 : l + 1 ≤ hiVTt A (k + 1) := Order.add_one_le_of_lt (hiVTt_lt_succ A k)
    have hl1T : l + 1 < hcN (Om1 + κ) A.F := hl1.trans_lt hl'T
    have hB : hiVTt A (k + 1) = (hiVU St A S0 l).B := (hiVTt_B A hSt hS k).symm
    have hcB : hiVTt A (k + 1) < (hiVU St A S0 (l + 1)).B := by
      rw [hiVU_B hSt hS hl1T, hB, hiVU_B hSt hS hlT]; exact A.Q_lt_Q (lt_add_one l)
    rw [hiVU_γ_iff hSt hS hl'T hx hx1, (hiV_ext hSt hS hl1 hl'T).2 _ hcB, hB, hiVU_B hSt hS hlT]
    refine max_lt hA ((hsp.gF x hx hx1).2 ?_)
    exact max_lt hA ((max_lt_iff.1 ((hiVU_γ_iff hSt hS hlT hx hx1).1 (hiVTt_gate k x hx hx1 hA))).2)

end Tower

/-- The reading of the tower code `t_k` (in its start). -/
noncomputable def hiVTr {κ : Ordinal.{0}} (St : ∀ (Q : HiVQ κ) (U : HgVD), HgSStart (hiVPB Q) U → HgVD) (A : HiVB κ)
    (S0 : HgVD) (k : ℕ)
    (x : Ordinal.{0}) : Ordinal.{0} := (hiVU St A S0 (hiVTt A k)).R (hiVTt A k) x

section TowerRead

variable {κ : Ordinal.{0}} {St : ∀ (Q : HiVQ κ) (U : HgVD), HgSStart (hiVPB Q) U → HgVD}
  (hSt : ∀ Q U h, HiVSpec Q U (St Q U h))
  {A : HiVB κ} {S0 : HgVD} (hS : HiVStart A S0) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hA : A.γN < x)
include hSt hS hx hx1 hA

theorem hiVTt_g (k : ℕ) : (hiVU St A S0 (hiVTt A k)).g (hiVTt A k) < x :=
  (max_lt_iff.1 ((hiVU_γ_iff hSt hS (hiVTt_lt A k) hx hx1).1 (hiVTt_gate A hSt hS k x hx hx1 hA))).2

/-- **`r_{k+1}(x) = ϑˣ(Ω₁·2 + F(x) + r_k(x))`**: the code `t_{k+1} = Q_{t_k}` is read as the base reading of the start
`t_k`. -/
theorem hiVTr_succ (k : ℕ) :
    hiVTr St A S0 (k + 1) x = glA (x + κ) (A.Fr x + hiVTr St A S0 k x) x := by
  set l := hiVTt A k with hl
  have hlT : l < hcN (Om1 + κ) A.F := hiVTt_lt A k
  have hl'T : hiVTt A (k + 1) < hcN (Om1 + κ) A.F := hiVTt_lt A (k + 1)
  have hsp := hiVU_succ_spec hSt hS hlT
  have hl1 : l + 1 ≤ hiVTt A (k + 1) := Order.add_one_le_of_lt (hiVTt_lt_succ A k)
  have hl1T : l + 1 < hcN (Om1 + κ) A.F := hl1.trans_lt hl'T
  have hB : hiVTt A (k + 1) = (hiVU St A S0 l).B := (hiVTt_B A hSt hS k).symm
  have hcB : hiVTt A (k + 1) < (hiVU St A S0 (l + 1)).B := by
    rw [hiVU_B hSt hS hl1T, hB, hiVU_B hSt hS hlT]; exact A.Q_lt_Q (lt_add_one l)
  have hg : max A.γN ((hiVU St A S0 l).g l) < x := max_lt hA (hiVTt_g hSt hS hx hx1 hA k)
  unfold hiVTr
  rw [(hiV_ext hSt hS hl1 hl'T).1 _ x hcB, hB, hiVU_B hSt hS hlT]
  exact hsp.RF x hx hx1 hg

theorem hiVTr_zero : hiVTr St A S0 0 x = 0 := by unfold hiVTr; exact (hiVU St A S0 (hiVTt A 0)).R_zero x

theorem hiVTr_lt_N (k : ℕ) : hiVTr St A S0 k x < hcN (x + κ) (A.Fr x) :=
  A.lvR_lt_N _ (hiVU_Zb hSt hS (hiVTt_lt A k)) (hiVU_self hSt hS (hiVTt_lt A k)) hx hx1 hA
    (hiVTt_g hSt hS hx hx1 hA k)

/-- **The iterates of `φ((Om1 + κ), ·)` from `hdNx (Om1 + κ) (F(x)) + 1` lie below the tower readings.** -/
theorem hiVTr_iter (n : ℕ) :
    (veblen (x + κ))^[n] (hdNx (x + κ) (A.Fr x) + 1) ≤ hiVTr St A S0 (n + 2) x := by
  obtain ⟨i0, hi0⟩ := hdNx_LuP (x + κ) (A.Fr x)
  have hstep : ∀ k : ℕ, hiVTr St A S0 (k + 1) x = veblen (x + κ)
      (i0 + hiVTr St A S0 k x) := fun k => by
    rw [hiVTr_succ hSt hS hx hx1 hA k, A.lvglAV hx hx1 hA hi0 (hiVTr_lt_N hSt hS hx hx1 hA k)]
  have h1 : hiVTr St A S0 1 x = hdNx (x + κ) (A.Fr x) := by
    rw [hstep 0, hiVTr_zero hSt hS hx hx1 hA, add_zero, hi0]
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply]
    refine Order.add_one_le_of_lt ?_
    rw [hstep 1, h1]
    refine (le_add_self : hdNx (x + κ) (A.Fr x) ≤ i0 + hdNx (x + κ) (A.Fr x)).trans_lt ?_
    have h2 := hiVTr_lt_N hSt hS hx hx1 hA 2
    rw [hstep 1, h1] at h2
    exact hc_nofixG (by rw [hi0]; exact hdNx_gt _ _) le_self_add h2
  | succ n ih =>
    rw [Function.iterate_succ_apply', hstep (n + 2)]
    exact (isNormal_veblen (x + κ)).monotone (ih.trans le_add_self)

/-- **The tower readings are cofinal in `N_α(F(x))`.** -/
theorem hiVTr_cof {v : Ordinal.{0}} (hv : v < hcN (x + κ) (A.Fr x)) : ∃ k : ℕ, v < hiVTr St A S0 k x := by
  have e : hcN (x + κ) (A.Fr x) = nfp (veblen (x + κ)) (hdNx (x + κ) (A.Fr x) + 1) := by
    refine le_antisymm ?_ ?_
    · exact hcN_le (nfp_fp (isNormal_veblen _) _)
        ((hdNx_gt (x + κ) (A.Fr x)).trans ((lt_add_one _).trans_le (le_nfp _ _)))
    · exact nfp_le_fp (isNormal_veblen (x + κ)).strictMono.monotone
        (Order.add_one_le_of_lt (hdNx_lt_N (hcN_gt (x + κ) (A.Fr x)))) (hcN_fix (x + κ) _).le
  rw [e] at hv
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hv
  exact ⟨n + 2, hn.trans_le (hiVTr_iter hSt hS hx hx1 hA n)⟩

end TowerRead

/-! ## The union of all offsets -/

section Union

variable {κ : Ordinal.{0}} (St : ∀ (Q : HiVQ κ) (U : HgVD), HgSStart (hiVPB Q) U → HgVD) (A : HiVB κ) (S0 : HgVD)

/-- The first start containing `c`. -/
noncomputable def hiVTN (c : Ordinal.{0}) : Ordinal.{0} := sInf {ν | ν < hcN (Om1 + κ) A.F ∧ c < (hiVU St A S0 ν).B}

/-- The reading of the union. -/
noncomputable def hiVTR (c x : Ordinal.{0}) : Ordinal.{0} := (hiVU St A S0 (hiVTN St A S0 c)).R c x

/-- The gate of the union. -/
noncomputable def hiVTg (c : Ordinal.{0}) : Ordinal.{0} := (hiVU St A S0 (hiVTN St A S0 c)).g c

open Classical in
/-- The bound field of the union: `evZ(N_α(F(x)))` above `γ`, `Z_o(x)` below. -/
noncomputable def hiVTZ (x : Ordinal.{0}) : Ordinal.{0} :=
  if A.γN < x then evZ (hcN (x + κ) (A.Fr x)) else A.Zo x

variable {St A S0} (hSt : ∀ Q U h, HiVSpec Q U (St Q U h)) (hS : HiVStart A S0)
include hSt hS

theorem hiVT_cof {c : Ordinal.{0}} (hc : c < hcN (Om1 + κ) A.F) : ∃ ν, ν < hcN (Om1 + κ) A.F ∧ c <
    (hiVU St A S0 ν).B := by
  obtain ⟨k, hk⟩ := hiVTt_cof A hc
  exact ⟨hiVTt A k, hiVTt_lt A k, hk.trans (by rw [hiVTt_B A hSt hS k]; exact hiVTt_lt_succ A k)⟩

omit hSt hS in
theorem hiVTN_spec {c ν : Ordinal.{0}} (hν : ν < hcN (Om1 + κ) A.F) (hc : c < (hiVU St A S0 ν).B) :
    hiVTN St A S0 c ≤ ν ∧ hiVTN St A S0 c < hcN (Om1 + κ) A.F ∧ c < (hiVU St A S0 (hiVTN St A S0 c)).B := by
  have hne : ({ν | ν < hcN (Om1 + κ) A.F ∧ c < (hiVU St A S0 ν).B} : Set Ordinal.{0}).Nonempty := ⟨ν, hν, hc⟩
  have hm := csInf_mem hne
  exact ⟨csInf_le' ⟨hν, hc⟩, hm.1, hm.2⟩

omit hSt hS in
theorem hiVTN_min {c μ : Ordinal.{0}} (hμ : μ < hiVTN St A S0 c) (hμl : μ < hcN (Om1 + κ) A.F) : ¬ c <
    (hiVU St A S0 μ).B :=
  fun hcμ => absurd (csInf_le' ⟨hμl, hcμ⟩ : hiVTN St A S0 c ≤ μ) (not_le.2 hμ)

theorem hiVT_B_lt {ν : Ordinal.{0}} (hν : ν < hcN (Om1 + κ) A.F) : (hiVU St A S0 ν).B < hcN (Om1 + κ) A.F := by
  rw [hiVU_B hSt hS hν]; exact A.Q_lt_N hν

theorem hiVTN_high {c : Ordinal.{0}} (hc : hcN (Om1 + κ) A.F ≤ c) : hiVTN St A S0 c = 0 := by
  unfold hiVTN
  have he : ({ν | ν < hcN (Om1 + κ) A.F ∧ c < (hiVU St A S0 ν).B} : Set Ordinal.{0}) = ∅ := by
    ext ν
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hν hcν
    exact absurd (hcν.trans (hiVT_B_lt hSt hS hν)) (not_lt.2 hc)
  rw [he]; exact Ordinal.sInf_empty

theorem hiVTR_eq {c ν : Ordinal.{0}} (hν : ν < hcN (Om1 + κ) A.F) (hc : c < (hiVU St A S0 ν).B) (x : Ordinal.{0}) :
    hiVTR St A S0 c x = (hiVU St A S0 ν).R c x := by
  obtain ⟨h1, -, h3⟩ := hiVTN_spec hν hc
  exact ((hiV_ext hSt hS h1 hν).1 c x h3).symm

theorem hiVTg_eq {c ν : Ordinal.{0}} (hν : ν < hcN (Om1 + κ) A.F) (hc : c < (hiVU St A S0 ν).B) :
    hiVTg St A S0 c = (hiVU St A S0 ν).g c := by
  obtain ⟨h1, -, h3⟩ := hiVTN_spec hν hc
  exact ((hiV_ext hSt hS h1 hν).2 c h3).symm

theorem hiVTR_succ (c x : Ordinal.{0}) : hiVTR St A S0 (c + 1) x = hiVTR St A S0 c x + 1 := by
  rcases lt_or_ge c (hcN (Om1 + κ) A.F) with h | h
  · obtain ⟨n, hn1, hn⟩ := hiVT_cof hSt hS (A.N_lim.add_one_lt h)
    rw [hiVTR_eq hSt hS hn1 hn, hiVTR_eq hSt hS hn1 ((lt_add_one c).trans hn), (hiVU St A S0 n).R_succ]
  · unfold hiVTR
    rw [hiVTN_high hSt hS h, hiVTN_high hSt hS (h.trans (le_self_add (a := c) (b := 1))), (hiVU St A S0 0).R_succ]

theorem hiVTg_le_succ (c : Ordinal.{0}) : hiVTg St A S0 c ≤ hiVTg St A S0 (c + 1) := by
  rcases lt_or_ge c (hcN (Om1 + κ) A.F) with h | h
  · obtain ⟨n, hn1, hn⟩ := hiVT_cof hSt hS (A.N_lim.add_one_lt h)
    rw [hiVTg_eq hSt hS hn1 hn, hiVTg_eq hSt hS hn1 ((lt_add_one c).trans hn)]; exact (hiVU St A S0 n).g_le_succ c
  · unfold hiVTg
    rw [hiVTN_high hSt hS h, hiVTN_high hSt hS (h.trans (le_self_add (a := c) (b := 1)))]; exact
        (hiVU St A S0 0).g_le_succ c

/-- **A code of the union with gate below a base `σ > γ_F` lies in a start with base gate below `σ`.** -/
theorem hiVT_small {c σ : Ordinal.{0}} (hc : c < hcN (Om1 + κ) A.F) (hσ : InE σ) (hσ1 : σ < Om1) (hAσ : A.γN < σ)
    (hg : hiVTg St A S0 c < σ) : ∃ μ, μ < hcN (Om1 + κ) A.F ∧ c < (hiVU St A S0 μ).B ∧ (hiVU St A S0 μ).γ < σ := by
  obtain ⟨n, hn1, hn⟩ := hiVT_cof hSt hS hc
  obtain ⟨-, hN1, hcNc⟩ := hiVTN_spec hn1 hn
  have hgN : hiVTg St A S0 c = (hiVU St A S0 (hiVTN St A S0 c)).g c := rfl
  have I := hiV_inv hSt hS _ hN1
  rcases zero_or_succ_or_isSuccLimit (hiVTN St A S0 c) with h0 | ⟨m, hm⟩ | hlim
  · refine ⟨hiVTN St A S0 c, hN1, hcNc, ?_⟩
    rw [h0, hiVU_γ_iff hSt hS (hiV_zero_lt_N A) hσ hσ1, (hiVU St A S0 0).g_zero, max_eq_left zero_le]
    exact hAσ
  · have hm' : hiVTN St A S0 c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < hiVTN St A S0 c := by rw [hm']; exact lt_add_one m
    have hml : m < hcN (Om1 + κ) A.F := hmN.trans hN1
    have hBc : (hiVU St A S0 m).B ≤ c := not_lt.1 (hiVTN_min hmN hml)
    refine ⟨hiVTN St A S0 c, hN1, hcNc, ?_⟩
    rw [hgN, hm'] at hg
    rw [hm'] at hcNc I ⊢
    exact I.high m (lt_add_one _) c σ hBc hcNc hσ hσ1 hg
  · exfalso
    rw [hiVU_B hSt hS hN1] at hcNc
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen (Om1 + κ)).lt_iff_exists_lt
        (isSuccLimit_add _ hlim)).1 hcNc
    obtain ⟨d, hf, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    have hfl : d < hcN (Om1 + κ) A.F := hf.trans hN1
    refine hiVTN_min hf hfl ?_
    rw [hiVU_B hSt hS hfl]; exact hct.trans_le ((isNormal_veblen (Om1 + κ)).monotone htd)

/-- **A code `c ∈ [F, N(F))` of the union with gate below a base `σ` forces `γ_F < σ`.** -/
theorem hiVT_high {c σ : Ordinal.{0}} (hc : c < hcN (Om1 + κ) A.F) (hFc : A.F ≤ c) (hσ : InE σ) (hσ1 : σ < Om1)
    (hg : hiVTg St A S0 c < σ) : A.γ < σ := by
  obtain ⟨n, hn1, hn⟩ := hiVT_cof hSt hS hc
  obtain ⟨-, hN1, hcNc⟩ := hiVTN_spec hn1 hn
  have hgN : hiVTg St A S0 c = (hiVU St A S0 (hiVTN St A S0 c)).g c := rfl
  have I := hiV_inv hSt hS _ hN1
  rcases zero_or_succ_or_isSuccLimit (hiVTN St A S0 c) with h0 | ⟨m, hm⟩ | hlim
  · rw [hgN, h0, hiVU_zero] at hg
    rw [h0, hiVU_zero] at hcNc
    exact hS.high0 c σ hFc hcNc hσ hσ1 hg
  · have hm' : hiVTN St A S0 c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < hiVTN St A S0 c := by rw [hm']; exact lt_add_one m
    have hml : m < hcN (Om1 + κ) A.F := hmN.trans hN1
    have hBc : (hiVU St A S0 m).B ≤ c := not_lt.1 (hiVTN_min hmN hml)
    rw [hgN, hm'] at hg
    rw [hm'] at hcNc I hN1
    have hγ := I.high m (lt_add_one _) c σ hBc hcNc hσ hσ1 hg
    exact A.γ_le.trans_lt (max_lt_iff.1 ((hiVU_γ_iff hSt hS hN1 hσ hσ1).1 hγ)).1
  · exfalso
    rw [hiVU_B hSt hS hN1] at hcNc
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen (Om1 + κ)).lt_iff_exists_lt
        (isSuccLimit_add _ hlim)).1 hcNc
    obtain ⟨d, hf, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    have hfl : d < hcN (Om1 + κ) A.F := hf.trans hN1
    refine hiVTN_min hf hfl ?_
    rw [hiVU_B hSt hS hfl]; exact hct.trans_le ((isNormal_veblen (Om1 + κ)).monotone htd)

/-- **`b_μ(x) < N(F(x))`** for every start with base gate below `x`. -/
theorem hiVT_b_lt {μ x : Ordinal.{0}} (hμ : μ < hcN (Om1 + κ) A.F) (hx : InE x) (hx1 : x < Om1) (hγ :
    (hiVU St A S0 μ).γ < x) :
    (hiVU St A S0 μ).b x < hcN (x + κ) (A.Fr x) := by
  have hg : max A.γN ((hiVU St A S0 μ).g μ) < x := (hiVU_γ_iff hSt hS hμ hx hx1).1 hγ
  have hA : A.γN < x := (max_lt_iff.1 hg).1
  rw [(hiVU_start hSt hS hμ).b x hx hx1 hg]
  exact A.glA_lt_N hx hx1 hA (A.lvR_lt_N _ (hiVU_Zb hSt hS hμ) (hiVU_self hSt hS hμ) hx hx1 hA (max_lt_iff.1 hg).2)

omit hSt hS in
theorem hiVTZ_fix (x : Ordinal.{0}) : veblen 1 (hiVTZ A x) = hiVTZ A x := by
  unfold hiVTZ; split_ifs
  · exact epsilon_evZ _
  · exact ha_fix1_of_fix2 (A.Zo_fix x)

omit hSt hS in
theorem hiVTZ_G1 (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : hiVTZ A x < gq 1 x := by
  unfold hiVTZ; split_ifs with h
  · exact (hb_evZ_lt_fix2 (A.Zo_fix x) (A.N_Zo hx hx1 h)).trans (A.Zo_G1 x hx hx1)
  · exact A.Zo_G1 x hx hx1

omit hSt hS in
theorem hiVTZ_ge (x : Ordinal.{0}) (hx : InE x) : A.Zl x ≤ hiVTZ A x := by
  by_cases h : A.γN < x
  · rw [A.Zl_eq hx h]; unfold hiVTZ; rw [if_pos h]; exact (lt_evZ _).le
  · rw [A.Zl_low h]; unfold hiVTZ; rw [if_neg h]

/-- **THE SYSTEM AT `N(F)`**: the union of all starts `hiVU St A S0 λ`, `λ < N(F)`: bound `N(F)`, base gate `γN`, base
reading `N(F(x))`, bound field `hiVTZ`. -/
noncomputable def hiVTU : HgVD where
  B := hcN (Om1 + κ) A.F
  γ := A.γN
  γ_lt := A.γN_lt
  γ_cl := fun Z hZ hZ1 h => A.N_cl Z hZ hZ1 h
  γ_G := fun h => absurd h (A.G_le.trans_lt A.F_lt_N).ne'
  R := hiVTR St A S0
  g := hiVTg St A S0
  b := fun x => hcN (x + κ) (A.Fr x)
  ba := fun x => hcN (x + κ) (A.Fr x)
  ix := hcN (Om1 + κ) A.F
  Z := hiVTZ A
  B_E := A.N_E
  G_le := (A.G_le.trans_lt A.F_lt_N).le
  B_lt1 := A.N_lt1
  B_ix := (hc_fix_down (hiv_L1 κ) (hcN_fix (Om1 + κ) A.F)).symm
  Z_fix := fun x _ _ => hiVTZ_fix x
  Z_G1 := hiVTZ_G1
  ix_mem := fun S _ _ ha hb => A.N_mem S ha hb
  g_lt := fun c hc => by
    obtain ⟨n, hn1, hn⟩ := hiVT_cof hSt hS hc
    rw [hiVTg_eq hSt hS hn1 hn]; exact (hiVU St A S0 n).g_lt c hn
  g_zero := by
    rw [hiVTg_eq hSt hS (hiV_zero_lt_N A) (hiVU St A S0 0).B_pos]; exact (hiVU St A S0 0).g_zero
  g_nat := fun k => by
    rw [hiVTg_eq hSt hS (hiV_zero_lt_N A) ((hiVU St A S0 0).nat_lt_B k)]; exact (hiVU St A S0 0).g_nat k
  g_E := by rw [hiVTg_eq hSt hS (hiV_zero_lt_N A) (hiVU St A S0 0).E_lt_B]; exact (hiVU St A S0 0).g_E
  g_lowE := fun c hc => by
    rw [hiVTg_eq hSt hS (hiV_zero_lt_N A) (hc.trans (hiVU St A S0 0).E_lt_B)]; exact (hiVU St A S0 0).g_lowE c hc
  g_G0 := fun h => by
    obtain ⟨n, hn1, hn⟩ := hiVT_cof hSt hS h
    rw [hiVTg_eq hSt hS hn1 hn]; exact (hiVU St A S0 n).g_G0 hn
  g_add := fun Z hZ hωZ x y hxy hgx hgy => by
    obtain ⟨n, hn1, hn⟩ := hiVT_cof hSt hS hxy
    have hx : x < (hiVU St A S0 n).B := lt_of_le_of_lt le_self_add hn
    have hy : y < (hiVU St A S0 n).B := lt_of_le_of_lt le_add_self hn
    rw [hiVTg_eq hSt hS hn1 hn]; rw [hiVTg_eq hSt hS hn1 hx] at hgx; rw [hiVTg_eq hSt hS hn1 hy] at hgy
    exact (hiVU St A S0 n).g_add Z hZ hωZ x y hn hgx hgy
  g_opow := fun Z hZw hωZ y hy hg => by
    obtain ⟨n, hn1, hn⟩ := hiVT_cof hSt hS hy
    have hy' : y < (hiVU St A S0 n).B := lt_of_le_of_lt (right_le_opow y one_lt_omega0) hn
    rw [hiVTg_eq hSt hS hn1 hn]; rw [hiVTg_eq hSt hS hn1 hy'] at hg
    exact (hiVU St A S0 n).g_opow Z hZw hωZ y hn hg
  code_gate := fun Z hZ1 hZ0 hZa hZp At hAt c hc hcB => by
    obtain ⟨n, hn1, hn⟩ := hiVT_cof hSt hS hcB
    rw [hiVTg_eq hSt hS hn1 hn]
    exact (hiVU St A S0 n).code_gate Z hZ1 hZ0 hZa hZp At (fun s hs => (hAt s hs).imp_right
      (fun h => (hiVT_B_lt hSt hS hn1).le.trans h)) c hc hn
  g_succ := fun Z hZ c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hiVT_cof hSt hS hc
    have hc' : c < (hiVU St A S0 n).B := (lt_add_one c).trans hn
    rw [hiVTg_eq hSt hS hn1 hn]; rw [hiVTg_eq hSt hS hn1 hc'] at hg
    exact (hiVU St A S0 n).g_succ Z hZ c hn hg
  g_le_succ := hiVTg_le_succ hSt hS
  mem := fun S a b ha c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hiVT_cof hSt hS hc
    rw [hiVTg_eq hSt hS hn1 hn] at hg
    exact (hiVU St A S0 n).mem S a b ha c hn hg
  R_zero := fun x => by
    rw [hiVTR_eq hSt hS (hiV_zero_lt_N A) (hiVU St A S0 0).B_pos]; exact (hiVU St A S0 0).R_zero x
  R_nat := fun k x => by
    rw [hiVTR_eq hSt hS (hiV_zero_lt_N A) ((hiVU St A S0 0).nat_lt_B k)]; exact (hiVU St A S0 0).R_nat k x
  R_E := fun x => by rw [hiVTR_eq hSt hS (hiV_zero_lt_N A) (hiVU St A S0 0).E_lt_B]; exact (hiVU St A S0 0).R_E x
  R_succ := hiVTR_succ hSt hS
  R_pos := fun x hx hx1 c hc0 hc hg => by
    obtain ⟨n, hn1, hn⟩ := hiVT_cof hSt hS hc
    rw [hiVTR_eq hSt hS hn1 hn]; rw [hiVTg_eq hSt hS hn1 hn] at hg
    exact (hiVU St A S0 n).R_pos x hx hx1 c hc0 hn hg
  R_omega := fun x hx hx1 c hω hc hg => by
    obtain ⟨n, hn1, hn⟩ := hiVT_cof hSt hS hc
    rw [hiVTR_eq hSt hS hn1 hn]; rw [hiVTg_eq hSt hS hn1 hn] at hg
    exact (hiVU St A S0 n).R_omega x hx hx1 c hω hn hg
  R_lt_b := fun x hx hx1 hγx c hc hg => by
    obtain ⟨μ, hμ, hcμ, hγμ⟩ := hiVT_small hSt hS hc hx hx1 hγx hg
    rw [hiVTR_eq hSt hS hμ hcμ]; rw [hiVTg_eq hSt hS hμ hcμ] at hg
    exact ((hiVU St A S0 μ).R_lt_b x hx hx1 hγμ c hcμ hg).trans (hiVT_b_lt hSt hS hμ hx hx1 hγμ)
  R_lt_Z := fun x hx hx1 c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hiVT_cof hSt hS hc
    rw [hiVTR_eq hSt hS hn1 hn]; rw [hiVTg_eq hSt hS hn1 hn] at hg
    exact (((hiVU St A S0 n).R_lt_Z x hx hx1 c hn hg).trans_le (hiVU_Zb hSt hS hn1 x hx hx1)).trans_le (hiVTZ_ge x hx)
  mono := fun x hx hx1 c hc d hfc hgc hgd => by
    obtain ⟨n, hn1, hn⟩ := hiVT_cof hSt hS hc
    have hf : d < (hiVU St A S0 n).B := hfc.trans hn
    rw [hiVTR_eq hSt hS hn1 hn,
        hiVTR_eq hSt hS hn1 hf]; rw [hiVTg_eq hSt hS hn1 hn] at hgc; rw [hiVTg_eq hSt hS hn1 hf] at hgd
    exact (hiVU St A S0 n).mono x hx hx1 c hn d hfc hgc hgd
  cof := fun x hx hx1 c hc hg ν hν => by
    obtain ⟨n, hn1, hn⟩ := hiVT_cof hSt hS hc
    rw [hiVTR_eq hSt hS hn1 hn] at hν; rw [hiVTg_eq hSt hS hn1 hn] at hg
    obtain ⟨d, hfc, hgd, hνd⟩ := (hiVU St A S0 n).cof x hx hx1 c hn hg ν hν
    have hf : d < (hiVU St A S0 n).B := hfc.trans hn
    exact ⟨d, hfc, by rw [hiVTg_eq hSt hS hn1 hf]; exact hgd, by rw [hiVTR_eq hSt hS hn1 hf]; exact hνd⟩
  b_cof := fun x hx hx1 hγx ν hν => by
    obtain ⟨k, hk⟩ := hiVTr_cof hSt hS hx hx1 hγx hν
    have hkT : hiVTt A k < hcN (Om1 + κ) A.F := hiVTt_lt A k
    have hkB : hiVTt A k < (hiVU St A S0 (hiVTt A k)).B := hiVU_self hSt hS hkT
    refine ⟨hiVTt A k, hkT, ?_, ?_⟩
    · rw [hiVTg_eq hSt hS hkT hkB]; exact hiVTt_g hSt hS hx hx1 hγx k
    · rw [hiVTR_eq hSt hS hkT hkB]; exact hk
  b_E := fun x _ _ _ => hcN_E (x + κ) _
  x_lt_b := fun x hx hx1 hγx => (le_self_add.trans_lt (A.Fr_gt hx hx1 hγx)).trans (A.Fr_lt_N x)
  b_eN := fun x hx hx1 hγx => gz_eN_fix hx hx1 (hc_fix_down (hiv_one hx hx1 (A.ν_lt hx hx1 hγx)) (hcN_fix (x + κ) _))
    ((le_self_add.trans_lt (A.Fr_gt hx hx1 hγx)).trans (A.Fr_lt_N x)) (A.N_lt1x hx hx1 hγx)
  ba_lt := fun x hx hx1 hγx => A.N_lt1x hx hx1 hγx
  b_Z := fun x _ _ hγx => by
    show _ < hiVTZ A x
    unfold hiVTZ; rw [if_pos hγx]
    exact go_eN_lt_evZ (lt_evZ _)
  b_pi := fun _ _ hB hγ => A.N_pi hB hγ
  ba_pi := fun _ _ hB hγ => A.N_pi hB hγ
  ex := fun σ ρ hB c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hiVT_cof hSt hS hc
    rw [hiVTR_eq hSt hS hn1 hn, hiVTR_eq hSt hS hn1 hn]; rw [hiVTg_eq hSt hS hn1 hn] at hg
    exact (hiVU St A S0 n).ex σ ρ hB c hn hg
  dig := fun σ ρ hB hγσ d hf hg P P' hat => by
    obtain ⟨μ, hμ, hfμ, hγμ⟩ := hiVT_small hSt hS hf hB.1 (hB.2.2.1.trans hB.2.2.2) hγσ hg
    rw [hiVTR_eq hSt hS hμ hfμ, hiVTR_eq hSt hS hμ hfμ]; rw [hiVTg_eq hSt hS hμ hfμ] at hg
    exact (hiVU St A S0 μ).dig σ ρ hB hγμ d hfμ hg P P' (fun β hβ hβe =>
      hat β hβ (hβe.trans (hiVT_b_lt hSt hS hμ hB.2.1 hB.2.2.2 (hγμ.trans hB.2.2.1))))
  ld := fun c hl hc => by
    obtain ⟨n, hn1, hn⟩ := hiVT_cof hSt hS hc
    obtain ⟨cp, lp, T, hcp, hgcp, hfec, hex⟩ := (hiVU St A S0 n).ld c hl hn
    have hcpn : cp < (hiVU St A S0 n).B := hcp.trans hn
    refine ⟨cp, lp, T, hcp, by rw [hiVTg_eq hSt hS hn1 hn, hiVTg_eq hSt hS hn1 hcpn]; exact hgcp,
        fun x hx hx1 hg => ?_,
      fun σ ρ hB hg => hex σ ρ hB (by rw [← hiVTg_eq hSt hS hn1 hn]; exact hg)⟩
    rw [hiVTg_eq hSt hS hn1 hn] at hg
    rw [hiVTR_eq hSt hS hn1 hn, hiVTR_eq hSt hS hn1 hcpn]
    exact hfec x hx hx1 hg

theorem hiVTU_B : (hiVTU hSt hS).B = hcN (Om1 + κ) A.F := rfl

theorem hiVTU_γ : (hiVTU hSt hS).γ = A.γN := rfl

theorem hiVTU_b (x : Ordinal.{0}) : (hiVTU hSt hS).b x = hcN (x + κ) (A.Fr x) := rfl

/-- **The union extends every start** (readings). -/
theorem hiVTU_R {ν c : Ordinal.{0}} (hν : ν < hcN (Om1 + κ) A.F) (hc : c < (hiVU St A S0 ν).B) (x : Ordinal.{0}) :
    (hiVTU hSt hS).R c x = (hiVU St A S0 ν).R c x := hiVTR_eq hSt hS hν hc x

/-- **The union extends every start** (gates). -/
theorem hiVTU_g {ν c : Ordinal.{0}} (hν : ν < hcN (Om1 + κ) A.F) (hc : c < (hiVU St A S0 ν).B) :
    (hiVTU hSt hS).g c = (hiVU St A S0 ν).g c := hiVTg_eq hSt hS hν hc

/-- **The union extends the start `S0`.** -/
theorem hiVTU_R0 {c : Ordinal.{0}} (hc : c < S0.B) (x : Ordinal.{0}) : (hiVTU hSt hS).R c x = S0.R c x := by
  rw [hiVTU_R hSt hS (hiV_zero_lt_N A) (by rw [hiVU_zero]; exact hc), hiVU_zero]

theorem hiVTU_g0 {c : Ordinal.{0}} (hc : c < S0.B) : (hiVTU hSt hS).g c = S0.g c := by
  rw [hiVTU_g hSt hS (hiV_zero_lt_N A) (by rw [hiVU_zero]; exact hc), hiVU_zero]

/-- **A code `c ∈ [F, N(F))` of the union with gate below a base `σ` forces the base gate below `σ`.** -/
theorem hiVTU_high (hγN : A.γN = A.γ) {c σ : Ordinal.{0}} (hc : c < hcN (Om1 + κ) A.F) (hFc : A.F ≤ c) (hσ : InE σ)
    (hσ1 : σ < Om1) (hg : (hiVTU hSt hS).g c < σ) : (hiVTU hSt hS).γ < σ := by
  show A.γN < σ
  rw [hγN]; exact hiVT_high hSt hS hc hFc hσ hσ1 hg

end Union

end Googology.Trans.PoR.InaccPsi.R2.Hi

import Googology.Trans.PoR.InaccPsi.R2.HdLvRec

/-!
# HdLvTop: THE UNION OF ALL OFFSETS OF A BASE OF LEVEL `ω`: THE TOP TOWER TO `N_ω(F) = φ(ω+1, F+1)`

The level-`ω` version of `Hc.HcLvTop`.  For a base `A : Hd.HdA` of level `ω` and a start `S0`, the union of all
starts `Hd.hdLvU A S0 λ`, `λ < N_ω(F)`, is a system `hdLvTU` with the bound `N_ω(F)`, base gate `γ`, base reading
`N_ω(F(x))`, bound field `evZ(N_ω(F(x)))` above `γ` and `Z_o(x)` below.  The tower `t_0 = 0`,
`t_{k+1} = φ(ω, F + 1 + t_k)` is cofinal in `N_ω(F)`, its readings `r_{k+1}(x) = ϑˣ(Ω₁·ω + F(x) + r_k(x))` (by the
specification of the `ω`-step) are cofinal in `N_ω(F(x))` and its starts have base gate below every base above `γ`.
The union extends the start, reads it, and every code in `[F, N_ω(F))` with gate below a base forces `γ` below it
(`hdLvTU_high`).

* `hdLvTt`, `hdLvTt_cof`, `hdLvTt_gate`, `hdLvTr`, `hdLvTr_succ`, `hdLvTr_cof`; `hdLvTN`, `hdLvTR`, `hdLvTg`, `hdLvTZ`,
  `hdLvT_small`, `hdLvT_high`, `hdLvTU` (**THE SYSTEM AT `N_ω(F)`**), `hdLvTU_R0`, `hdLvTU_g0`, `hdLvTU_high`.

No new axiom.  New definitions: `hdLvTt`, `hdLvTr`, `hdLvTN`, `hdLvTR`, `hdLvTg`, `hdLvTZ`, `hdLvTU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hd

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

variable (A : HdA)

/-- **The tower of offsets**: `t_0 = 0`, `t_{k+1} = φ(2, F + 1 + t_k)`. -/
noncomputable def hdLvTt : ℕ → Ordinal.{0}
  | 0 => 0
  | k + 1 => veblen ω (A.F + 1 + hdLvTt k)

theorem hdLvTt_lt : ∀ k : ℕ, hdLvTt A k < hcNw A.F
  | 0 => hdLv_zero_lt_N A
  | k + 1 => A.Q_lt_N (hdLvTt_lt k)

theorem hdLvTt_lt_succ (k : ℕ) : hdLvTt A k < hdLvTt A (k + 1) := A.lt_Q (hdLvTt_lt A k)

theorem hdLvTt_iter (n : ℕ) : (veblen ω)^[n] (A.F + 1) ≤ hdLvTt A (n + 1) := by
  induction n with
  | zero =>
    show A.F + 1 ≤ veblen ω (A.F + 1 + 0)
    rw [add_zero]; exact right_le_veblen ω _
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    show veblen ω _ ≤ veblen ω (A.F + 1 + hdLvTt A (n + 1))
    exact (isNormal_veblen ω).monotone (ih.trans le_add_self)

theorem hdLv_N_nfp : hcNw A.F = nfp (veblen ω) (A.F + 1) := rfl

/-- **The tower is cofinal in `N(F)`.** -/
theorem hdLvTt_cof {c : Ordinal.{0}} (hc : c < hcNw A.F) : ∃ k : ℕ, c < hdLvTt A k := by
  rw [hdLv_N_nfp] at hc
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hc
  exact ⟨n + 1, hn.trans_le (hdLvTt_iter A n)⟩

variable {S0 : HcVD} (hS : HdLvStart A S0)
include hS

theorem hdLvTt_B (k : ℕ) : (hdLvU A S0 (hdLvTt A k)).B = hdLvTt A (k + 1) := hdLvU_B hS (hdLvTt_lt A k)

/-- **Every start `hdLvU A S0 t_k` has base gate below every base above `γ_F`.** -/
theorem hdLvTt_gate : ∀ (k : ℕ) (x : Ordinal.{0}), InE x → x < Om1 → A.γ < x → (hdLvU A S0 (hdLvTt A k)).γ < x
  | 0, x, hx, hx1, hA => by
    show (hdLvU A S0 0).γ < x
    rw [hdLvU_γ_iff hS (hdLv_zero_lt_N A) hx hx1, (hdLvU A S0 0).g_zero, max_eq_left zero_le]; exact hA
  | k + 1, x, hx, hx1, hA => by
    set l := hdLvTt A k with hl
    have hlT : l < hcNw A.F := hdLvTt_lt A k
    have hl'T : hdLvTt A (k + 1) < hcNw A.F := hdLvTt_lt A (k + 1)
    have hsp := hdLvU_succ_spec hS hlT
    have hl1 : l + 1 ≤ hdLvTt A (k + 1) := Order.add_one_le_of_lt (hdLvTt_lt_succ A k)
    have hl1T : l + 1 < hcNw A.F := hl1.trans_lt hl'T
    have hB : hdLvTt A (k + 1) = (hdLvU A S0 l).B := (hdLvTt_B A hS k).symm
    have hcB : hdLvTt A (k + 1) < (hdLvU A S0 (l + 1)).B := by
      rw [hdLvU_B hS hl1T, hB, hdLvU_B hS hlT]; exact A.Q_lt_Q (lt_add_one l)
    rw [hdLvU_γ_iff hS hl'T hx hx1, (hdLv_ext hS hl1 hl'T).2 _ hcB, hB, hdLvU_B hS hlT]
    refine max_lt hA ((hsp.gF x hx hx1).2 ?_)
    exact max_lt hA ((max_lt_iff.1 ((hdLvU_γ_iff hS hlT hx hx1).1 (hdLvTt_gate k x hx hx1 hA))).2)

end Tower

/-- The reading of the tower code `t_k` (in its start). -/
noncomputable def hdLvTr (A : HdA) (S0 : HcVD) (k : ℕ) (x : Ordinal.{0}) : Ordinal.{0} :=
  (hdLvU A S0 (hdLvTt A k)).R (hdLvTt A k) x

section TowerRead

variable {A : HdA} {S0 : HcVD} (hS : HdLvStart A S0) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hA : A.γ < x)
include hS hx hx1 hA

theorem hdLvTt_g (k : ℕ) : (hdLvU A S0 (hdLvTt A k)).g (hdLvTt A k) < x :=
  (max_lt_iff.1 ((hdLvU_γ_iff hS (hdLvTt_lt A k) hx hx1).1 (hdLvTt_gate A hS k x hx hx1 hA))).2

/-- **`r_{k+1}(x) = ϑˣ(Ω₁·2 + F(x) + r_k(x))`**: the code `t_{k+1} = Q_{t_k}` is read as the base reading of the start
`t_k`. -/
theorem hdLvTr_succ (k : ℕ) :
    hdLvTr A S0 (k + 1) x = glA ω (A.Fr x + hdLvTr A S0 k x) x := by
  set l := hdLvTt A k with hl
  have hlT : l < hcNw A.F := hdLvTt_lt A k
  have hl'T : hdLvTt A (k + 1) < hcNw A.F := hdLvTt_lt A (k + 1)
  have hsp := hdLvU_succ_spec hS hlT
  have hl1 : l + 1 ≤ hdLvTt A (k + 1) := Order.add_one_le_of_lt (hdLvTt_lt_succ A k)
  have hl1T : l + 1 < hcNw A.F := hl1.trans_lt hl'T
  have hB : hdLvTt A (k + 1) = (hdLvU A S0 l).B := (hdLvTt_B A hS k).symm
  have hcB : hdLvTt A (k + 1) < (hdLvU A S0 (l + 1)).B := by
    rw [hdLvU_B hS hl1T, hB, hdLvU_B hS hlT]; exact A.Q_lt_Q (lt_add_one l)
  have hg : max A.γ ((hdLvU A S0 l).g l) < x := max_lt hA (hdLvTt_g hS hx hx1 hA k)
  unfold hdLvTr
  rw [(hdLv_ext hS hl1 hl'T).1 _ x hcB, hB, hdLvU_B hS hlT]
  exact hsp.RF x hx hx1 hg

theorem hdLvTr_zero : hdLvTr A S0 0 x = 0 := by unfold hdLvTr; exact (hdLvU A S0 (hdLvTt A 0)).R_zero x

theorem hdLvTr_lt_N (k : ℕ) : hdLvTr A S0 k x < hcNw (A.Fr x) :=
  A.lvR_lt_N _ (hdLvU_Zb hS (hdLvTt_lt A k)) (hdLvU_self hS (hdLvTt_lt A k)) hx hx1 hA
    (hdLvTt_g hS hx hx1 hA k)

/-- **The iterates of `φ(ω, ·)` from `hcS(F(x)) + 1` lie below the tower readings.** -/
theorem hdLvTr_iter (n : ℕ) :
    (veblen ω)^[n] (hcS (A.Fr x) + 1) ≤ hdLvTr A S0 (n + 2) x := by
  obtain ⟨i0, hi0⟩ := hcS_LuP (A.Fr x)
  have hstep : ∀ k : ℕ, hdLvTr A S0 (k + 1) x = veblen ω
      (i0 + hdLvTr A S0 k x) := fun k => by
    rw [hdLvTr_succ hS hx hx1 hA k, A.lvglAV hx hx1 hA hi0 (hdLvTr_lt_N hS hx hx1 hA k)]
  have h1 : hdLvTr A S0 1 x = hcS (A.Fr x) := by
    rw [hstep 0, hdLvTr_zero hS hx hx1 hA, add_zero, hi0]
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply]
    refine Order.add_one_le_of_lt ?_
    rw [hstep 1, h1]
    refine (le_add_self : hcS (A.Fr x) ≤ i0 + hcS (A.Fr x)).trans_lt ?_
    have h2 := hdLvTr_lt_N hS hx hx1 hA 2
    rw [hstep 1, h1] at h2
    exact hc_nofixW (by rw [hi0]; exact hcS_gt _) le_self_add h2
  | succ n ih =>
    rw [Function.iterate_succ_apply', hstep (n + 2)]
    exact (isNormal_veblen ω).monotone (ih.trans le_add_self)

/-- **The tower readings are cofinal in `N_ω(F(x))`.** -/
theorem hdLvTr_cof {v : Ordinal.{0}} (hv : v < hcNw (A.Fr x)) : ∃ k : ℕ, v < hdLvTr A S0 k x := by
  have e : hcNw (A.Fr x) = nfp (veblen ω) (hcS (A.Fr x) + 1) := by
    refine le_antisymm ?_ ?_
    · exact hcNw_le (nfp_fp (isNormal_veblen _) _)
        ((hcS_gt (A.Fr x)).trans ((lt_add_one _).trans_le (le_nfp _ _)))
    · exact nfp_le_fp (isNormal_veblen ω).strictMono.monotone
        (Order.add_one_le_of_lt (hdS_lt_Nw (hcNw_gt (A.Fr x)))) (hcNw_fix _).le
  rw [e] at hv
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hv
  exact ⟨n + 2, hn.trans_le (hdLvTr_iter hS hx hx1 hA n)⟩

end TowerRead

/-! ## The union of all offsets -/

section Union

variable (A : HdA) (S0 : HcVD)

/-- The first start containing `c`. -/
noncomputable def hdLvTN (c : Ordinal.{0}) : Ordinal.{0} := sInf {ν | ν < hcNw A.F ∧ c < (hdLvU A S0 ν).B}

/-- The reading of the union. -/
noncomputable def hdLvTR (c x : Ordinal.{0}) : Ordinal.{0} := (hdLvU A S0 (hdLvTN A S0 c)).R c x

/-- The gate of the union. -/
noncomputable def hdLvTg (c : Ordinal.{0}) : Ordinal.{0} := (hdLvU A S0 (hdLvTN A S0 c)).g c

open Classical in
/-- The bound field of the union: `evZ(N_ω(F(x)))` above `γ`, `Z_o(x)` below. -/
noncomputable def hdLvTZ (x : Ordinal.{0}) : Ordinal.{0} :=
  if A.γ < x then evZ (hcNw (A.Fr x)) else A.Zo x

variable {A S0} (hS : HdLvStart A S0)
include hS

theorem hdLvT_cof {c : Ordinal.{0}} (hc : c < hcNw A.F) : ∃ ν, ν < hcNw A.F ∧ c <
    (hdLvU A S0 ν).B := by
  obtain ⟨k, hk⟩ := hdLvTt_cof A hc
  exact ⟨hdLvTt A k, hdLvTt_lt A k, hk.trans (by rw [hdLvTt_B A hS k]; exact hdLvTt_lt_succ A k)⟩

omit hS in
theorem hdLvTN_spec {c ν : Ordinal.{0}} (hν : ν < hcNw A.F) (hc : c < (hdLvU A S0 ν).B) :
    hdLvTN A S0 c ≤ ν ∧ hdLvTN A S0 c < hcNw A.F ∧ c < (hdLvU A S0 (hdLvTN A S0 c)).B := by
  have hne : ({ν | ν < hcNw A.F ∧ c < (hdLvU A S0 ν).B} : Set Ordinal.{0}).Nonempty := ⟨ν, hν, hc⟩
  have hm := csInf_mem hne
  exact ⟨csInf_le' ⟨hν, hc⟩, hm.1, hm.2⟩

omit hS in
theorem hdLvTN_min {c μ : Ordinal.{0}} (hμ : μ < hdLvTN A S0 c) (hμl : μ < hcNw A.F) : ¬ c <
    (hdLvU A S0 μ).B :=
  fun hcμ => absurd (csInf_le' ⟨hμl, hcμ⟩ : hdLvTN A S0 c ≤ μ) (not_le.2 hμ)

theorem hdLvT_B_lt {ν : Ordinal.{0}} (hν : ν < hcNw A.F) : (hdLvU A S0 ν).B < hcNw A.F := by
  rw [hdLvU_B hS hν]; exact A.Q_lt_N hν

theorem hdLvTN_high {c : Ordinal.{0}} (hc : hcNw A.F ≤ c) : hdLvTN A S0 c = 0 := by
  unfold hdLvTN
  have he : ({ν | ν < hcNw A.F ∧ c < (hdLvU A S0 ν).B} : Set Ordinal.{0}) = ∅ := by
    ext ν
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hν hcν
    exact absurd (hcν.trans (hdLvT_B_lt hS hν)) (not_lt.2 hc)
  rw [he]; exact Ordinal.sInf_empty

theorem hdLvTR_eq {c ν : Ordinal.{0}} (hν : ν < hcNw A.F) (hc : c < (hdLvU A S0 ν).B) (x : Ordinal.{0}) :
    hdLvTR A S0 c x = (hdLvU A S0 ν).R c x := by
  obtain ⟨h1, -, h3⟩ := hdLvTN_spec hν hc
  exact ((hdLv_ext hS h1 hν).1 c x h3).symm

theorem hdLvTg_eq {c ν : Ordinal.{0}} (hν : ν < hcNw A.F) (hc : c < (hdLvU A S0 ν).B) :
    hdLvTg A S0 c = (hdLvU A S0 ν).g c := by
  obtain ⟨h1, -, h3⟩ := hdLvTN_spec hν hc
  exact ((hdLv_ext hS h1 hν).2 c h3).symm

theorem hdLvTR_succ (c x : Ordinal.{0}) : hdLvTR A S0 (c + 1) x = hdLvTR A S0 c x + 1 := by
  rcases lt_or_ge c (hcNw A.F) with h | h
  · obtain ⟨n, hn1, hn⟩ := hdLvT_cof hS (A.N_lim.add_one_lt h)
    rw [hdLvTR_eq hS hn1 hn, hdLvTR_eq hS hn1 ((lt_add_one c).trans hn), (hdLvU A S0 n).R_succ]
  · unfold hdLvTR
    rw [hdLvTN_high hS h, hdLvTN_high hS (h.trans (le_self_add (a := c) (b := 1))), (hdLvU A S0 0).R_succ]

theorem hdLvTg_le_succ (c : Ordinal.{0}) : hdLvTg A S0 c ≤ hdLvTg A S0 (c + 1) := by
  rcases lt_or_ge c (hcNw A.F) with h | h
  · obtain ⟨n, hn1, hn⟩ := hdLvT_cof hS (A.N_lim.add_one_lt h)
    rw [hdLvTg_eq hS hn1 hn, hdLvTg_eq hS hn1 ((lt_add_one c).trans hn)]; exact (hdLvU A S0 n).g_le_succ c
  · unfold hdLvTg
    rw [hdLvTN_high hS h, hdLvTN_high hS (h.trans (le_self_add (a := c) (b := 1)))]; exact
        (hdLvU A S0 0).g_le_succ c

/-- **A code of the union with gate below a base `σ > γ_F` lies in a start with base gate below `σ`.** -/
theorem hdLvT_small {c σ : Ordinal.{0}} (hc : c < hcNw A.F) (hσ : InE σ) (hσ1 : σ < Om1) (hAσ : A.γ < σ)
    (hg : hdLvTg A S0 c < σ) : ∃ μ, μ < hcNw A.F ∧ c < (hdLvU A S0 μ).B ∧ (hdLvU A S0 μ).γ < σ := by
  obtain ⟨n, hn1, hn⟩ := hdLvT_cof hS hc
  obtain ⟨-, hN1, hcN⟩ := hdLvTN_spec hn1 hn
  have hgN : hdLvTg A S0 c = (hdLvU A S0 (hdLvTN A S0 c)).g c := rfl
  have I := hdLv_inv hS _ hN1
  rcases zero_or_succ_or_isSuccLimit (hdLvTN A S0 c) with h0 | ⟨m, hm⟩ | hlim
  · refine ⟨hdLvTN A S0 c, hN1, hcN, ?_⟩
    rw [h0, hdLvU_γ_iff hS (hdLv_zero_lt_N A) hσ hσ1, (hdLvU A S0 0).g_zero, max_eq_left zero_le]
    exact hAσ
  · have hm' : hdLvTN A S0 c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < hdLvTN A S0 c := by rw [hm']; exact lt_add_one m
    have hml : m < hcNw A.F := hmN.trans hN1
    have hBc : (hdLvU A S0 m).B ≤ c := not_lt.1 (hdLvTN_min hmN hml)
    refine ⟨hdLvTN A S0 c, hN1, hcN, ?_⟩
    rw [hgN, hm'] at hg
    rw [hm'] at hcN I ⊢
    exact I.high m (lt_add_one _) c σ hBc hcN hσ hσ1 hg
  · exfalso
    rw [hdLvU_B hS hN1] at hcN
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen ω).lt_iff_exists_lt
        (isSuccLimit_add _ hlim)).1 hcN
    obtain ⟨d, hd, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    have hdl : d < hcNw A.F := hd.trans hN1
    refine hdLvTN_min hd hdl ?_
    rw [hdLvU_B hS hdl]; exact hct.trans_le ((isNormal_veblen ω).monotone htd)

/-- **A code `c ∈ [F, N(F))` of the union with gate below a base `σ` forces `γ_F < σ`.** -/
theorem hdLvT_high {c σ : Ordinal.{0}} (hc : c < hcNw A.F) (hFc : A.F ≤ c) (hσ : InE σ) (hσ1 : σ < Om1)
    (hg : hdLvTg A S0 c < σ) : A.γ < σ := by
  obtain ⟨n, hn1, hn⟩ := hdLvT_cof hS hc
  obtain ⟨-, hN1, hcN⟩ := hdLvTN_spec hn1 hn
  have hgN : hdLvTg A S0 c = (hdLvU A S0 (hdLvTN A S0 c)).g c := rfl
  have I := hdLv_inv hS _ hN1
  rcases zero_or_succ_or_isSuccLimit (hdLvTN A S0 c) with h0 | ⟨m, hm⟩ | hlim
  · rw [hgN, h0, hdLvU_zero] at hg
    rw [h0, hdLvU_zero] at hcN
    exact hS.high0 c σ hFc hcN hσ hσ1 hg
  · have hm' : hdLvTN A S0 c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < hdLvTN A S0 c := by rw [hm']; exact lt_add_one m
    have hml : m < hcNw A.F := hmN.trans hN1
    have hBc : (hdLvU A S0 m).B ≤ c := not_lt.1 (hdLvTN_min hmN hml)
    rw [hgN, hm'] at hg
    rw [hm'] at hcN I hN1
    have hγ := I.high m (lt_add_one _) c σ hBc hcN hσ hσ1 hg
    exact (max_lt_iff.1 ((hdLvU_γ_iff hS hN1 hσ hσ1).1 hγ)).1
  · exfalso
    rw [hdLvU_B hS hN1] at hcN
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen ω).lt_iff_exists_lt
        (isSuccLimit_add _ hlim)).1 hcN
    obtain ⟨d, hd, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    have hdl : d < hcNw A.F := hd.trans hN1
    refine hdLvTN_min hd hdl ?_
    rw [hdLvU_B hS hdl]; exact hct.trans_le ((isNormal_veblen ω).monotone htd)

/-- **`b_μ(x) < N(F(x))`** for every start with base gate below `x`. -/
theorem hdLvT_b_lt {μ x : Ordinal.{0}} (hμ : μ < hcNw A.F) (hx : InE x) (hx1 : x < Om1) (hγ :
    (hdLvU A S0 μ).γ < x) :
    (hdLvU A S0 μ).b x < hcNw (A.Fr x) := by
  have hg : max A.γ ((hdLvU A S0 μ).g μ) < x := (hdLvU_γ_iff hS hμ hx hx1).1 hγ
  have hA : A.γ < x := (max_lt_iff.1 hg).1
  rw [(hdLvU_start hS hμ).b x hx hx1 hg]
  exact A.glA_lt_N hx hx1 hA (A.lvR_lt_N _ (hdLvU_Zb hS hμ) (hdLvU_self hS hμ) hx hx1 hA (max_lt_iff.1 hg).2)

omit hS in
theorem hdLvTZ_fix (x : Ordinal.{0}) : veblen 1 (hdLvTZ A x) = hdLvTZ A x := by
  unfold hdLvTZ; split_ifs
  · exact epsilon_evZ _
  · exact ha_fix1_of_fix2 (A.Zo_fix x)

omit hS in
theorem hdLvTZ_BR (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : hdLvTZ A x ≤ hcBR x := by
  unfold hdLvTZ; split_ifs with h
  · exact (hb_evZ_lt_fix2 (A.Zo_fix x) (A.N_Zo hx hx1 h)).le.trans (A.Zo_BR x hx hx1)
  · exact A.Zo_BR x hx hx1

omit hS in
theorem hdLvTZ_ge (x : Ordinal.{0}) : A.Zl x ≤ hdLvTZ A x := by
  unfold hdLvTZ HdA.Zl; split_ifs
  · exact (lt_evZ _).le
  · exact le_rfl

/-- **THE SYSTEM AT `N(F)`**: the union of all starts `hdLvU A S0 λ`, `λ < N(F)`: bound `N(F)`, base gate `γ_F`, base
reading `N(F(x))`, bound field `hdLvTZ`. -/
noncomputable def hdLvTU : HcVD where
  B := hcNw A.F
  γ := A.γ
  γ_lt := A.γ_lt
  γ_cl := fun Z hZ hZ1 h => A.N_cl Z hZ hZ1 h
  γ_G := fun h => absurd h (A.G_le.trans_lt A.F_lt_N).ne'
  R := hdLvTR A S0
  g := hdLvTg A S0
  b := fun x => hcNw (A.Fr x)
  ba := fun x => hcNw (A.Fr x)
  ix := hcNw A.F
  Z := hdLvTZ A
  B_E := A.N_E
  G_le := (A.G_le.trans_lt A.F_lt_N).le
  B_lt1 := A.N_lt1
  B_ix := (hdNw_fix1 A.F).symm
  Z_fix := fun x _ _ => hdLvTZ_fix x
  Z_BR := hdLvTZ_BR
  ix_mem := fun S _ _ ha hb => A.N_mem S ha hb
  g_lt := fun c hc => by
    obtain ⟨n, hn1, hn⟩ := hdLvT_cof hS hc
    rw [hdLvTg_eq hS hn1 hn]; exact (hdLvU A S0 n).g_lt c hn
  g_zero := by
    rw [hdLvTg_eq hS (hdLv_zero_lt_N A) (hdLvU A S0 0).B_pos]; exact (hdLvU A S0 0).g_zero
  g_nat := fun k => by
    rw [hdLvTg_eq hS (hdLv_zero_lt_N A) ((hdLvU A S0 0).nat_lt_B k)]; exact (hdLvU A S0 0).g_nat k
  g_E := by rw [hdLvTg_eq hS (hdLv_zero_lt_N A) (hdLvU A S0 0).E_lt_B]; exact (hdLvU A S0 0).g_E
  g_lowE := fun c hc => by
    rw [hdLvTg_eq hS (hdLv_zero_lt_N A) (hc.trans (hdLvU A S0 0).E_lt_B)]; exact (hdLvU A S0 0).g_lowE c hc
  g_G0 := fun h => by
    obtain ⟨n, hn1, hn⟩ := hdLvT_cof hS h
    rw [hdLvTg_eq hS hn1 hn]; exact (hdLvU A S0 n).g_G0 hn
  g_add := fun Z hZ hωZ x y hxy hgx hgy => by
    obtain ⟨n, hn1, hn⟩ := hdLvT_cof hS hxy
    have hx : x < (hdLvU A S0 n).B := lt_of_le_of_lt le_self_add hn
    have hy : y < (hdLvU A S0 n).B := lt_of_le_of_lt le_add_self hn
    rw [hdLvTg_eq hS hn1 hn]; rw [hdLvTg_eq hS hn1 hx] at hgx; rw [hdLvTg_eq hS hn1 hy] at hgy
    exact (hdLvU A S0 n).g_add Z hZ hωZ x y hn hgx hgy
  g_opow := fun Z hZw hωZ y hy hg => by
    obtain ⟨n, hn1, hn⟩ := hdLvT_cof hS hy
    have hy' : y < (hdLvU A S0 n).B := lt_of_le_of_lt (right_le_opow y one_lt_omega0) hn
    rw [hdLvTg_eq hS hn1 hn]; rw [hdLvTg_eq hS hn1 hy'] at hg
    exact (hdLvU A S0 n).g_opow Z hZw hωZ y hn hg
  code_gate := fun Z hZ1 hZ0 hZa hZp At hAt c hc hcB => by
    obtain ⟨n, hn1, hn⟩ := hdLvT_cof hS hcB
    rw [hdLvTg_eq hS hn1 hn]
    exact (hdLvU A S0 n).code_gate Z hZ1 hZ0 hZa hZp At (fun s hs => (hAt s hs).imp_right
      (fun h => (hdLvT_B_lt hS hn1).le.trans h)) c hc hn
  g_succ := fun Z hZ c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hdLvT_cof hS hc
    have hc' : c < (hdLvU A S0 n).B := (lt_add_one c).trans hn
    rw [hdLvTg_eq hS hn1 hn]; rw [hdLvTg_eq hS hn1 hc'] at hg
    exact (hdLvU A S0 n).g_succ Z hZ c hn hg
  g_le_succ := hdLvTg_le_succ hS
  mem := fun S a b ha c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hdLvT_cof hS hc
    rw [hdLvTg_eq hS hn1 hn] at hg
    exact (hdLvU A S0 n).mem S a b ha c hn hg
  R_zero := fun x => by
    rw [hdLvTR_eq hS (hdLv_zero_lt_N A) (hdLvU A S0 0).B_pos]; exact (hdLvU A S0 0).R_zero x
  R_nat := fun k x => by
    rw [hdLvTR_eq hS (hdLv_zero_lt_N A) ((hdLvU A S0 0).nat_lt_B k)]; exact (hdLvU A S0 0).R_nat k x
  R_E := fun x => by rw [hdLvTR_eq hS (hdLv_zero_lt_N A) (hdLvU A S0 0).E_lt_B]; exact (hdLvU A S0 0).R_E x
  R_succ := hdLvTR_succ hS
  R_pos := fun x hx hx1 c hc0 hc hg => by
    obtain ⟨n, hn1, hn⟩ := hdLvT_cof hS hc
    rw [hdLvTR_eq hS hn1 hn]; rw [hdLvTg_eq hS hn1 hn] at hg
    exact (hdLvU A S0 n).R_pos x hx hx1 c hc0 hn hg
  R_omega := fun x hx hx1 c hω hc hg => by
    obtain ⟨n, hn1, hn⟩ := hdLvT_cof hS hc
    rw [hdLvTR_eq hS hn1 hn]; rw [hdLvTg_eq hS hn1 hn] at hg
    exact (hdLvU A S0 n).R_omega x hx hx1 c hω hn hg
  R_lt_b := fun x hx hx1 hγx c hc hg => by
    obtain ⟨μ, hμ, hcμ, hγμ⟩ := hdLvT_small hS hc hx hx1 hγx hg
    rw [hdLvTR_eq hS hμ hcμ]; rw [hdLvTg_eq hS hμ hcμ] at hg
    exact ((hdLvU A S0 μ).R_lt_b x hx hx1 hγμ c hcμ hg).trans (hdLvT_b_lt hS hμ hx hx1 hγμ)
  R_lt_Z := fun x hx hx1 c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hdLvT_cof hS hc
    rw [hdLvTR_eq hS hn1 hn]; rw [hdLvTg_eq hS hn1 hn] at hg
    exact (((hdLvU A S0 n).R_lt_Z x hx hx1 c hn hg).trans_le (hdLvU_Zb hS hn1 x hx hx1)).trans_le (hdLvTZ_ge x)
  mono := fun x hx hx1 c hc d hdc hgc hgd => by
    obtain ⟨n, hn1, hn⟩ := hdLvT_cof hS hc
    have hd : d < (hdLvU A S0 n).B := hdc.trans hn
    rw [hdLvTR_eq hS hn1 hn,
        hdLvTR_eq hS hn1 hd]; rw [hdLvTg_eq hS hn1 hn] at hgc; rw [hdLvTg_eq hS hn1 hd] at hgd
    exact (hdLvU A S0 n).mono x hx hx1 c hn d hdc hgc hgd
  cof := fun x hx hx1 c hc hg ν hν => by
    obtain ⟨n, hn1, hn⟩ := hdLvT_cof hS hc
    rw [hdLvTR_eq hS hn1 hn] at hν; rw [hdLvTg_eq hS hn1 hn] at hg
    obtain ⟨d, hdc, hgd, hνd⟩ := (hdLvU A S0 n).cof x hx hx1 c hn hg ν hν
    have hd : d < (hdLvU A S0 n).B := hdc.trans hn
    exact ⟨d, hdc, by rw [hdLvTg_eq hS hn1 hd]; exact hgd, by rw [hdLvTR_eq hS hn1 hd]; exact hνd⟩
  b_cof := fun x hx hx1 hγx ν hν => by
    obtain ⟨k, hk⟩ := hdLvTr_cof hS hx hx1 hγx hν
    have hkT : hdLvTt A k < hcNw A.F := hdLvTt_lt A k
    have hkB : hdLvTt A k < (hdLvU A S0 (hdLvTt A k)).B := hdLvU_self hS hkT
    refine ⟨hdLvTt A k, hkT, ?_, ?_⟩
    · rw [hdLvTg_eq hS hkT hkB]; exact hdLvTt_g hS hx hx1 hγx k
    · rw [hdLvTR_eq hS hkT hkB]; exact hk
  b_E := fun x _ _ _ => hcNw_E _
  x_lt_b := fun x hx hx1 hγx => (A.Fr_gt hx hx1 hγx).trans (A.Fr_lt_N x)
  b_eN := fun x hx hx1 hγx => gz_eN_fix hx hx1 (hdNw_fix1 _)
    ((A.Fr_gt hx hx1 hγx).trans (A.Fr_lt_N x)) (A.N_lt1x hx hx1 hγx)
  ba_lt := fun x hx hx1 hγx => A.N_lt1x hx hx1 hγx
  b_Z := fun x _ _ hγx => by
    show _ < hdLvTZ A x
    unfold hdLvTZ; rw [if_pos hγx]
    exact go_eN_lt_evZ (lt_evZ _)
  b_pi := fun _ _ hB hγ => A.N_pi hB hγ
  ba_pi := fun _ _ hB hγ => A.N_pi hB hγ
  ex := fun σ ρ hB c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hdLvT_cof hS hc
    rw [hdLvTR_eq hS hn1 hn, hdLvTR_eq hS hn1 hn]; rw [hdLvTg_eq hS hn1 hn] at hg
    exact (hdLvU A S0 n).ex σ ρ hB c hn hg
  dig := fun σ ρ hB hγσ d hd hg P P' hat => by
    obtain ⟨μ, hμ, hdμ, hγμ⟩ := hdLvT_small hS hd hB.1 (hB.2.2.1.trans hB.2.2.2) hγσ hg
    rw [hdLvTR_eq hS hμ hdμ, hdLvTR_eq hS hμ hdμ]; rw [hdLvTg_eq hS hμ hdμ] at hg
    exact (hdLvU A S0 μ).dig σ ρ hB hγμ d hdμ hg P P' (fun β hβ hβe =>
      hat β hβ (hβe.trans (hdLvT_b_lt hS hμ hB.2.1 hB.2.2.2 (hγμ.trans hB.2.2.1))))
  ld := fun c hl hc => by
    obtain ⟨n, hn1, hn⟩ := hdLvT_cof hS hc
    obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := (hdLvU A S0 n).ld c hl hn
    have hcpn : cp < (hdLvU A S0 n).B := hcp.trans hn
    refine ⟨cp, lp, T, hcp, by rw [hdLvTg_eq hS hn1 hn, hdLvTg_eq hS hn1 hcpn]; exact hgcp,
        fun x hx hx1 hg => ?_,
      fun σ ρ hB hg => hex σ ρ hB (by rw [← hdLvTg_eq hS hn1 hn]; exact hg)⟩
    rw [hdLvTg_eq hS hn1 hn] at hg
    rw [hdLvTR_eq hS hn1 hn, hdLvTR_eq hS hn1 hcpn]
    exact hdec x hx hx1 hg

theorem hdLvTU_B : (hdLvTU hS).B = hcNw A.F := rfl

theorem hdLvTU_γ : (hdLvTU hS).γ = A.γ := rfl

theorem hdLvTU_b (x : Ordinal.{0}) : (hdLvTU hS).b x = hcNw (A.Fr x) := rfl

/-- **The union extends every start** (readings). -/
theorem hdLvTU_R {ν c : Ordinal.{0}} (hν : ν < hcNw A.F) (hc : c < (hdLvU A S0 ν).B) (x : Ordinal.{0}) :
    (hdLvTU hS).R c x = (hdLvU A S0 ν).R c x := hdLvTR_eq hS hν hc x

/-- **The union extends every start** (gates). -/
theorem hdLvTU_g {ν c : Ordinal.{0}} (hν : ν < hcNw A.F) (hc : c < (hdLvU A S0 ν).B) :
    (hdLvTU hS).g c = (hdLvU A S0 ν).g c := hdLvTg_eq hS hν hc

/-- **The union extends the start `S0`.** -/
theorem hdLvTU_R0 {c : Ordinal.{0}} (hc : c < S0.B) (x : Ordinal.{0}) : (hdLvTU hS).R c x = S0.R c x := by
  rw [hdLvTU_R hS (hdLv_zero_lt_N A) (by rw [hdLvU_zero]; exact hc), hdLvU_zero]

theorem hdLvTU_g0 {c : Ordinal.{0}} (hc : c < S0.B) : (hdLvTU hS).g c = S0.g c := by
  rw [hdLvTU_g hS (hdLv_zero_lt_N A) (by rw [hdLvU_zero]; exact hc), hdLvU_zero]

/-- **A code `c ∈ [F, N(F))` of the union with gate below a base `σ` forces the base gate below `σ`.** -/
theorem hdLvTU_high {c σ : Ordinal.{0}} (hc : c < hcNw A.F) (hFc : A.F ≤ c) (hσ : InE σ) (hσ1 : σ < Om1)
    (hg : (hdLvTU hS).g c < σ) : (hdLvTU hS).γ < σ := hdLvT_high hS hc hFc hσ hσ1 hg

end Union

end Googology.Trans.PoR.InaccPsi.R2.Hd

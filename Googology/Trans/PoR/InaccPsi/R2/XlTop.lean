import Googology.Trans.PoR.InaccPsi.R2.XlRec

/-!
# XlTop: THE TOP OF A LEVEL: THE SYSTEM AT `N = φ(L+κ+1, 0)`

PORT of `Hn.HnVTop` to a bottom base `Xl.XlB` (`Xl.XlRec`).  The tower `t_0 = 0`, `t_{k+1} = φ(L+κ, e + t_k)` is
cofinal in `N = N_{L+κ}(0) = φ(L+κ+1, 0)`; its readings `r_{k+1}(x) = φ(ℓ(x)+κ, e + r_k(x))` are cofinal in
`N_{ℓ(x)+κ}(0)`; every start of the tower has gate `≤ γN`.  The union of all starts `xlU λ`, `λ < N`, is

* `xlTU` (**THE SYSTEM AT `φ(L+κ+1, 0)`**: bound `N`, base gate `γN`, base reading `N_{ℓ(x)+κ}(0)`, bound field
  `xlTZ`), extending every start (`xlTU_R`, `xlTU_g`, `xlTU_R0`, `xlTU_g0`).

No new axiom.  New definitions: `xlTt`, `xlTr`, `xlTN`, `xlTR`, `xlTg`, `xlTZ`, `xlTU`.
-/

set_option autoImplicit false


open Googology.Trans.PoR.InaccPsi.R2.Wm Googology.Trans.PoR.InaccPsi.R2.Wh Googology.Trans.PoR.InaccPsi.R2.Ho
open Googology.Trans.PoR.InaccPsi.R2.Hn Googology.Trans.PoR.InaccPsi.R2.Hl
open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk
open Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Gf
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd
open Googology.Trans.PoR.InaccPsi.R2.Wo Googology.Trans.PoR.InaccPsi.R2.Wn Googology.Trans.PoR.InaccPsi.R2.Wp
  Googology.Trans.PoR.InaccPsi.R2.Ws Googology.Trans.PoR.InaccPsi.R2.Wt Googology.Trans.PoR.InaccPsi.R2.Wy
  Googology.Trans.PoR.InaccPsi.R2.Wx

open Googology.Trans.PoR.InaccPsi.R2.Xc
open Googology.Trans.PoR.InaccPsi.R2.Xf

open Googology.Trans.PoR.InaccPsi.R2.Xf

namespace Googology.Trans.PoR.InaccPsi.R2.Xl

variable {Λ : HnLv}

/-! ## The tower of offsets -/

section Tower

variable {κ : Ordinal.{0}} (A : XlB Λ κ)

/-- **The tower of offsets**: `t_0 = 0`, `t_{k+1} = φ(2, F + 1 + t_k)`. -/
noncomputable def xlTt : ℕ → Ordinal.{0}
  | 0 => 0
  | k + 1 => veblen (Λ.L + κ) (A.e + xlTt k)

theorem xlTt_lt : ∀ k : ℕ, xlTt A k < hcN (Λ.L + κ) 0
  | 0 => xl_zero_lt_N A
  | k + 1 => A.Q_lt_N (xlTt_lt k)

theorem xlTt_lt_succ (k : ℕ) : xlTt A k < xlTt A (k + 1) := A.lt_Q (xlTt_lt A k)

theorem xlTt_iter (n : ℕ) : (veblen (Λ.L + κ))^[n] 1 ≤ xlTt A (n + 1) := by
  induction n with
  | zero =>
    show (1 : Ordinal.{0}) ≤ veblen (Λ.L + κ) (A.e + 0)
    exact Order.one_le_iff_pos.2 veblen_pos
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    show veblen (Λ.L + κ) _ ≤ veblen (Λ.L + κ) (A.e + xlTt A (n + 1))
    exact (isNormal_veblen (Λ.L + κ)).monotone (ih.trans le_add_self)

theorem xl_N_nfp : hcN (Λ.L + κ) 0 = nfp (veblen (Λ.L + κ)) 1 := by unfold hcN; rw [zero_add]

/-- **The tower is cofinal in `N(F)`.** -/
theorem xlTt_cof {c : Ordinal.{0}} (hc : c < hcN (Λ.L + κ) 0) : ∃ k : ℕ, c < xlTt A k := by
  rw [xl_N_nfp] at hc
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hc
  exact ⟨n + 1, hn.trans_le (xlTt_iter A n)⟩

variable {St : ∀ (Q : HnVQ Λ κ) (U : HgVD), HgSStart (hnVPB Q) U → HgVD} {S0 : HgVD}
  (hSt : ∀ Q U h, HnVSpec Q U (St Q U h)) (hS : XlStart A S0)
include hSt hS

theorem xlTt_B (k : ℕ) : (xlU St A S0 (xlTt A k)).B = xlTt A (k + 1) := xlU_B hSt hS (xlTt_lt A k)

/-- **Every start `xlU St A S0 t_k` has base gate below every base above `γN`.** -/
theorem xlTt_gate : ∀ (k : ℕ) (x : Ordinal.{0}), InE x → x < Om1 → A.γN < x → (xlU St A S0 (xlTt A k)).γ < x
  | 0, x, hx, hx1, hA => by
    show (xlU St A S0 0).γ < x
    rw [xlU_γ_iff hSt hS (xl_zero_lt_N A) hx hx1, (xlU St A S0 0).g_zero, max_eq_left zero_le]; exact hA
  | k + 1, x, hx, hx1, hA => by
    set l := xlTt A k with hl
    have hlT : l < hcN (Λ.L + κ) 0 := xlTt_lt A k
    have hl'T : xlTt A (k + 1) < hcN (Λ.L + κ) 0 := xlTt_lt A (k + 1)
    have hsp := xlU_succ_spec hSt hS hlT
    have hl1 : l + 1 ≤ xlTt A (k + 1) := Order.add_one_le_of_lt (xlTt_lt_succ A k)
    have hl1T : l + 1 < hcN (Λ.L + κ) 0 := hl1.trans_lt hl'T
    have hB : xlTt A (k + 1) = (xlU St A S0 l).B := (xlTt_B A hSt hS k).symm
    have hcB : xlTt A (k + 1) < (xlU St A S0 (l + 1)).B := by
      rw [xlU_B hSt hS hl1T, hB, xlU_B hSt hS hlT]; exact A.Q_lt_Q (lt_add_one l)
    rw [xlU_γ_iff hSt hS hl'T hx hx1, (xl_ext hSt hS hl1 hl'T).2 _ hcB, hB, xlU_B hSt hS hlT]
    refine max_lt hA ((hsp.gF x hx hx1).2 ?_)
    exact max_lt hA ((max_lt_iff.1 ((xlU_γ_iff hSt hS hlT hx hx1).1 (xlTt_gate k x hx hx1 hA))).2)

end Tower

/-- The reading of the tower code `t_k` (in its start). -/
noncomputable def xlTr {κ : Ordinal.{0}} (St : ∀ (Q : HnVQ Λ κ) (U : HgVD), HgSStart (hnVPB Q) U → HgVD) (A : XlB Λ κ)
    (S0 : HgVD) (k : ℕ)
    (x : Ordinal.{0}) : Ordinal.{0} := (xlU St A S0 (xlTt A k)).R (xlTt A k) x

section TowerRead

variable {κ : Ordinal.{0}} {St : ∀ (Q : HnVQ Λ κ) (U : HgVD), HgSStart (hnVPB Q) U → HgVD}
  (hSt : ∀ Q U h, HnVSpec Q U (St Q U h))
  {A : XlB Λ κ} {S0 : HgVD} (hS : XlStart A S0) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hA : A.γN < x)
include hSt hS hx hx1 hA

theorem xlTt_g (k : ℕ) : (xlU St A S0 (xlTt A k)).g (xlTt A k) < x :=
  (max_lt_iff.1 ((xlU_γ_iff hSt hS (xlTt_lt A k) hx hx1).1 (xlTt_gate A hSt hS k x hx hx1 hA))).2

/-- **`r_{k+1}(x) = ϑˣ(Ω₁·2 + F(x) + r_k(x))`**: the code `t_{k+1} = Q_{t_k}` is read as the base reading of the start
`t_k`. -/
theorem xlTr_succ (k : ℕ) :
    xlTr St A S0 (k + 1) x = glA (Λ.l x + κ) (xlTr St A S0 k x) x := by
  set l := xlTt A k with hl
  have hlT : l < hcN (Λ.L + κ) 0 := xlTt_lt A k
  have hl'T : xlTt A (k + 1) < hcN (Λ.L + κ) 0 := xlTt_lt A (k + 1)
  have hsp := xlU_succ_spec hSt hS hlT
  have hl1 : l + 1 ≤ xlTt A (k + 1) := Order.add_one_le_of_lt (xlTt_lt_succ A k)
  have hl1T : l + 1 < hcN (Λ.L + κ) 0 := hl1.trans_lt hl'T
  have hB : xlTt A (k + 1) = (xlU St A S0 l).B := (xlTt_B A hSt hS k).symm
  have hcB : xlTt A (k + 1) < (xlU St A S0 (l + 1)).B := by
    rw [xlU_B hSt hS hl1T, hB, xlU_B hSt hS hlT]; exact A.Q_lt_Q (lt_add_one l)
  have hg : max A.γN ((xlU St A S0 l).g l) < x := max_lt hA (xlTt_g hSt hS hx hx1 hA k)
  unfold xlTr
  rw [(xl_ext hSt hS hl1 hl'T).1 _ x hcB, hB, xlU_B hSt hS hlT]
  exact hsp.RF x hx hx1 hg

theorem xlTr_zero : xlTr St A S0 0 x = 0 := by unfold xlTr; exact (xlU St A S0 (xlTt A 0)).R_zero x

theorem xlTr_lt_N (k : ℕ) : xlTr St A S0 k x < hcN (Λ.l x + κ) 0 :=
  A.lvR_lt_N _ (xlU_Zb hSt hS (xlTt_lt A k)) (xlU_self hSt hS (xlTt_lt A k)) hx hx1 hA
    (xlTt_g hSt hS hx hx1 hA k)

/-- **The iterates of `φ(ℓ(x)+κ, ·)` from `1` lie below the tower readings.** -/
theorem xlTr_iter (n : ℕ) : (veblen (Λ.l x + κ))^[n] 1 ≤ xlTr St A S0 (n + 1) x := by
  have hstep : ∀ k : ℕ, xlTr St A S0 (k + 1) x = veblen (Λ.l x + κ) (A.e + xlTr St A S0 k x) := fun k => by
    rw [xlTr_succ hSt hS hx hx1 hA k, A.read hx hx1 hA _ (xlTr_lt_N hSt hS hx hx1 hA k)]
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply, hstep 0]
    exact Order.one_le_iff_pos.2 veblen_pos
  | succ n ih =>
    rw [Function.iterate_succ_apply', hstep (n + 1)]
    exact (isNormal_veblen (Λ.l x + κ)).monotone (ih.trans le_add_self)

/-- **The tower readings are cofinal in `N_{ℓ(x)+κ}(0)`.** -/
theorem xlTr_cof {v : Ordinal.{0}} (hv : v < hcN (Λ.l x + κ) 0) : ∃ k : ℕ, v < xlTr St A S0 k x := by
  have e : hcN (Λ.l x + κ) 0 = nfp (veblen (Λ.l x + κ)) 1 := by unfold hcN; rw [zero_add]
  rw [e] at hv
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hv
  exact ⟨n + 1, hn.trans_le (xlTr_iter hSt hS hx hx1 hA n)⟩

end TowerRead

/-! ## The union of all offsets -/

section Union

variable {κ : Ordinal.{0}} (St : ∀ (Q : HnVQ Λ κ) (U : HgVD), HgSStart (hnVPB Q) U → HgVD) (A : XlB Λ κ) (S0 : HgVD)

/-- The first start containing `c`. -/
noncomputable def xlTN (c : Ordinal.{0}) : Ordinal.{0} := sInf {ν | ν < hcN (Λ.L + κ) 0 ∧ c < (xlU St A S0 ν).B}

/-- The reading of the union. -/
noncomputable def xlTR (c x : Ordinal.{0}) : Ordinal.{0} := (xlU St A S0 (xlTN St A S0 c)).R c x

/-- The gate of the union. -/
noncomputable def xlTg (c : Ordinal.{0}) : Ordinal.{0} := (xlU St A S0 (xlTN St A S0 c)).g c

open Classical in
/-- The bound field of the union: `evZ(N_α(F(x)))` above `γ`, `Z_o(x)` below. -/
noncomputable def xlTZ (x : Ordinal.{0}) : Ordinal.{0} :=
  if A.γN < x then evZ (hcN (Λ.l x + κ) 0) else A.Zo x

variable {St A S0} (hSt : ∀ Q U h, HnVSpec Q U (St Q U h)) (hS : XlStart A S0)
include hSt hS

theorem xlT_cof {c : Ordinal.{0}} (hc : c < hcN (Λ.L + κ) 0) : ∃ ν, ν < hcN (Λ.L + κ) 0 ∧ c <
    (xlU St A S0 ν).B := by
  obtain ⟨k, hk⟩ := xlTt_cof A hc
  exact ⟨xlTt A k, xlTt_lt A k, hk.trans (by rw [xlTt_B A hSt hS k]; exact xlTt_lt_succ A k)⟩

omit hSt hS in
theorem xlTN_spec {c ν : Ordinal.{0}} (hν : ν < hcN (Λ.L + κ) 0) (hc : c < (xlU St A S0 ν).B) :
    xlTN St A S0 c ≤ ν ∧ xlTN St A S0 c < hcN (Λ.L + κ) 0 ∧ c < (xlU St A S0 (xlTN St A S0 c)).B := by
  have hne : ({ν | ν < hcN (Λ.L + κ) 0 ∧ c < (xlU St A S0 ν).B} : Set Ordinal.{0}).Nonempty := ⟨ν, hν, hc⟩
  have hm := csInf_mem hne
  exact ⟨csInf_le' ⟨hν, hc⟩, hm.1, hm.2⟩

omit hSt hS in
theorem xlTN_min {c μ : Ordinal.{0}} (hμ : μ < xlTN St A S0 c) (hμl : μ < hcN (Λ.L + κ) 0) : ¬ c <
    (xlU St A S0 μ).B :=
  fun hcμ => absurd (csInf_le' ⟨hμl, hcμ⟩ : xlTN St A S0 c ≤ μ) (not_le.2 hμ)

theorem xlT_B_lt {ν : Ordinal.{0}} (hν : ν < hcN (Λ.L + κ) 0) : (xlU St A S0 ν).B < hcN (Λ.L + κ) 0 := by
  rw [xlU_B hSt hS hν]; exact A.Q_lt_N hν

theorem xlTN_high {c : Ordinal.{0}} (hc : hcN (Λ.L + κ) 0 ≤ c) : xlTN St A S0 c = 0 := by
  unfold xlTN
  have he : ({ν | ν < hcN (Λ.L + κ) 0 ∧ c < (xlU St A S0 ν).B} : Set Ordinal.{0}) = ∅ := by
    ext ν
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hν hcν
    exact absurd (hcν.trans (xlT_B_lt hSt hS hν)) (not_lt.2 hc)
  rw [he]; exact Ordinal.sInf_empty

theorem xlTR_eq {c ν : Ordinal.{0}} (hν : ν < hcN (Λ.L + κ) 0) (hc : c < (xlU St A S0 ν).B) (x : Ordinal.{0}) :
    xlTR St A S0 c x = (xlU St A S0 ν).R c x := by
  obtain ⟨h1, -, h3⟩ := xlTN_spec hν hc
  exact ((xl_ext hSt hS h1 hν).1 c x h3).symm

theorem xlTg_eq {c ν : Ordinal.{0}} (hν : ν < hcN (Λ.L + κ) 0) (hc : c < (xlU St A S0 ν).B) :
    xlTg St A S0 c = (xlU St A S0 ν).g c := by
  obtain ⟨h1, -, h3⟩ := xlTN_spec hν hc
  exact ((xl_ext hSt hS h1 hν).2 c h3).symm

theorem xlTR_succ (c x : Ordinal.{0}) : xlTR St A S0 (c + 1) x = xlTR St A S0 c x + 1 := by
  rcases lt_or_ge c (hcN (Λ.L + κ) 0) with h | h
  · obtain ⟨n, hn1, hn⟩ := xlT_cof hSt hS (A.N_lim.add_one_lt h)
    rw [xlTR_eq hSt hS hn1 hn, xlTR_eq hSt hS hn1 ((lt_add_one c).trans hn), (xlU St A S0 n).R_succ]
  · unfold xlTR
    rw [xlTN_high hSt hS h, xlTN_high hSt hS (h.trans (le_self_add (a := c) (b := 1))), (xlU St A S0 0).R_succ]

theorem xlTg_le_succ (c : Ordinal.{0}) : xlTg St A S0 c ≤ xlTg St A S0 (c + 1) := by
  rcases lt_or_ge c (hcN (Λ.L + κ) 0) with h | h
  · obtain ⟨n, hn1, hn⟩ := xlT_cof hSt hS (A.N_lim.add_one_lt h)
    rw [xlTg_eq hSt hS hn1 hn, xlTg_eq hSt hS hn1 ((lt_add_one c).trans hn)]; exact (xlU St A S0 n).g_le_succ c
  · unfold xlTg
    rw [xlTN_high hSt hS h, xlTN_high hSt hS (h.trans (le_self_add (a := c) (b := 1)))]; exact
        (xlU St A S0 0).g_le_succ c

/-- **A code of the union with gate below a base `σ > γ_F` lies in a start with base gate below `σ`.** -/
theorem xlT_small {c σ : Ordinal.{0}} (hc : c < hcN (Λ.L + κ) 0) (hσ : InE σ) (hσ1 : σ < Om1) (hAσ : A.γN < σ)
    (hg : xlTg St A S0 c < σ) : ∃ μ, μ < hcN (Λ.L + κ) 0 ∧ c < (xlU St A S0 μ).B ∧ (xlU St A S0 μ).γ < σ := by
  obtain ⟨n, hn1, hn⟩ := xlT_cof hSt hS hc
  obtain ⟨-, hN1, hcNc⟩ := xlTN_spec hn1 hn
  have hgN : xlTg St A S0 c = (xlU St A S0 (xlTN St A S0 c)).g c := rfl
  have I := xl_inv hSt hS _ hN1
  rcases zero_or_succ_or_isSuccLimit (xlTN St A S0 c) with h0 | ⟨m, hm⟩ | hlim
  · refine ⟨xlTN St A S0 c, hN1, hcNc, ?_⟩
    rw [h0, xlU_γ_iff hSt hS (xl_zero_lt_N A) hσ hσ1, (xlU St A S0 0).g_zero, max_eq_left zero_le]
    exact hAσ
  · have hm' : xlTN St A S0 c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < xlTN St A S0 c := by rw [hm']; exact lt_add_one m
    have hml : m < hcN (Λ.L + κ) 0 := hmN.trans hN1
    have hBc : (xlU St A S0 m).B ≤ c := not_lt.1 (xlTN_min hmN hml)
    refine ⟨xlTN St A S0 c, hN1, hcNc, ?_⟩
    rw [hgN, hm'] at hg
    rw [hm'] at hcNc I ⊢
    exact I.high m (lt_add_one _) c σ hBc hcNc hσ hσ1 hg
  · exfalso
    rw [xlU_B hSt hS hN1] at hcNc
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen (Λ.L + κ)).lt_iff_exists_lt
        (isSuccLimit_add _ hlim)).1 hcNc
    obtain ⟨d, hf, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    have hfl : d < hcN (Λ.L + κ) 0 := hf.trans hN1
    refine xlTN_min hf hfl ?_
    rw [xlU_B hSt hS hfl]; exact hct.trans_le ((isNormal_veblen (Λ.L + κ)).monotone htd)

/-- **`b_μ(x) < N(F(x))`** for every start with base gate below `x`. -/
theorem xlT_b_lt {μ x : Ordinal.{0}} (hμ : μ < hcN (Λ.L + κ) 0) (hx : InE x) (hx1 : x < Om1) (hγ :
    (xlU St A S0 μ).γ < x) :
    (xlU St A S0 μ).b x < hcN (Λ.l x + κ) 0 := by
  have hg : max A.γN ((xlU St A S0 μ).g μ) < x := (xlU_γ_iff hSt hS hμ hx hx1).1 hγ
  have hA : A.γN < x := (max_lt_iff.1 hg).1
  rw [(xlU_start hSt hS hμ).b x hx hx1 hg]
  exact A.glA_lt_N hx hx1 hA (A.lvR_lt_N _ (xlU_Zb hSt hS hμ) (xlU_self hSt hS hμ) hx hx1 hA (max_lt_iff.1 hg).2)

omit hSt hS in
theorem xlTZ_fix (x : Ordinal.{0}) : veblen 1 (xlTZ A x) = xlTZ A x := by
  unfold xlTZ; split_ifs
  · exact epsilon_evZ _
  · exact ha_fix1_of_fix2 (A.Zo_fix x)

omit hSt hS in
theorem xlTZ_G1 (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : xlTZ A x < gq 1 x := by
  unfold xlTZ; split_ifs with h
  · have h2 : (2 : Ordinal.{0}) ≤ Λ.l x + κ :=
      (show (2 : Ordinal.{0}) ≤ ω from (by exact_mod_cast (natCast_lt_omega0 2).le)).trans (hnv_ωl Λ hx hx1).le
    have hN2 : veblen 2 (hcN (Λ.l x + κ) (hcN (Λ.l x + κ) 0)) = hcN (Λ.l x + κ) (hcN (Λ.l x + κ) 0) :=
      hc_fix_down h2 (hcN_fix _ _)
    refine (hb_evZ_lt_fix2 hN2 (hcN_gt _ _)).trans ?_
    exact he_N_lt1 hx hx1 ((ev_isSuccLimit_of_inE (gm1_facts hx hx1).2.2.2).add_one_lt
      (hnv_q Λ hx hx1 (A.ν_lt hx hx1 h))) (A.N_lt1x hx hx1 h)
  · exact A.Zo_G1 x hx hx1

omit hSt hS in
theorem xlTZ_ge (x : Ordinal.{0}) (hx : InE x) : A.Zl x ≤ xlTZ A x := by
  by_cases h : A.γN < x
  · rw [A.Zl_eq hx h]; unfold xlTZ; rw [if_pos h]; exact (lt_evZ _).le
  · rw [A.Zl_low h]; unfold xlTZ; rw [if_neg h]

/-- **THE SYSTEM AT `N(F)`**: the union of all starts `xlU St A S0 λ`, `λ < N(F)`: bound `N(F)`, base gate `γN`, base
reading `N(F(x))`, bound field `xlTZ`. -/
noncomputable def xlTU : HgVD where
  B := hcN (Λ.L + κ) 0
  γ := A.γN
  γ_lt := A.γN_lt
  γ_cl := fun Z hZ hZ1 h => A.N_cl Z hZ hZ1 h
  γ_G := fun h => absurd h A.G_lt_N.ne'
  R := xlTR St A S0
  g := xlTg St A S0
  b := fun x => hcN (Λ.l x + κ) 0
  ba := fun x => hcN (Λ.l x + κ) 0
  ix := hcN (Λ.L + κ) 0
  Z := xlTZ A
  B_E := A.N_E
  G_le := A.G_lt_N.le
  B_lt1 := A.N_lt1
  B_ix := (hc_fix_down (hnv_L1 Λ κ) (hcN_fix (Λ.L + κ) 0)).symm
  Z_fix := fun x _ _ => xlTZ_fix x
  Z_G1 := xlTZ_G1
  ix_mem := fun S _ _ ha hb => A.N_mem S ha hb
  g_lt := fun c hc => by
    obtain ⟨n, hn1, hn⟩ := xlT_cof hSt hS hc
    rw [xlTg_eq hSt hS hn1 hn]; exact (xlU St A S0 n).g_lt c hn
  g_zero := by
    rw [xlTg_eq hSt hS (xl_zero_lt_N A) (xlU St A S0 0).B_pos]; exact (xlU St A S0 0).g_zero
  g_nat := fun k => by
    rw [xlTg_eq hSt hS (xl_zero_lt_N A) ((xlU St A S0 0).nat_lt_B k)]; exact (xlU St A S0 0).g_nat k
  g_E := by rw [xlTg_eq hSt hS (xl_zero_lt_N A) (xlU St A S0 0).E_lt_B]; exact (xlU St A S0 0).g_E
  g_lowE := fun c hc => by
    rw [xlTg_eq hSt hS (xl_zero_lt_N A) (hc.trans (xlU St A S0 0).E_lt_B)]; exact (xlU St A S0 0).g_lowE c hc
  g_G0 := fun h => by
    obtain ⟨n, hn1, hn⟩ := xlT_cof hSt hS h
    rw [xlTg_eq hSt hS hn1 hn]; exact (xlU St A S0 n).g_G0 hn
  g_add := fun Z hZ hωZ x y hxy hgx hgy => by
    obtain ⟨n, hn1, hn⟩ := xlT_cof hSt hS hxy
    have hx : x < (xlU St A S0 n).B := lt_of_le_of_lt le_self_add hn
    have hy : y < (xlU St A S0 n).B := lt_of_le_of_lt le_add_self hn
    rw [xlTg_eq hSt hS hn1 hn]; rw [xlTg_eq hSt hS hn1 hx] at hgx; rw [xlTg_eq hSt hS hn1 hy] at hgy
    exact (xlU St A S0 n).g_add Z hZ hωZ x y hn hgx hgy
  g_opow := fun Z hZw hωZ y hy hg => by
    obtain ⟨n, hn1, hn⟩ := xlT_cof hSt hS hy
    have hy' : y < (xlU St A S0 n).B := lt_of_le_of_lt (right_le_opow y one_lt_omega0) hn
    rw [xlTg_eq hSt hS hn1 hn]; rw [xlTg_eq hSt hS hn1 hy'] at hg
    exact (xlU St A S0 n).g_opow Z hZw hωZ y hn hg
  code_gate := fun Z hZ1 hZ0 hZa hZp At hAt c hc hcB => by
    obtain ⟨n, hn1, hn⟩ := xlT_cof hSt hS hcB
    rw [xlTg_eq hSt hS hn1 hn]
    exact (xlU St A S0 n).code_gate Z hZ1 hZ0 hZa hZp At (fun s hs => (hAt s hs).imp_right
      (fun h => (xlT_B_lt hSt hS hn1).le.trans h)) c hc hn
  g_succ := fun Z hZ c hc hg => by
    obtain ⟨n, hn1, hn⟩ := xlT_cof hSt hS hc
    have hc' : c < (xlU St A S0 n).B := (lt_add_one c).trans hn
    rw [xlTg_eq hSt hS hn1 hn]; rw [xlTg_eq hSt hS hn1 hc'] at hg
    exact (xlU St A S0 n).g_succ Z hZ c hn hg
  g_le_succ := xlTg_le_succ hSt hS
  mem := fun S a b ha c hc hg => by
    obtain ⟨n, hn1, hn⟩ := xlT_cof hSt hS hc
    rw [xlTg_eq hSt hS hn1 hn] at hg
    exact (xlU St A S0 n).mem S a b ha c hn hg
  R_zero := fun x => by
    rw [xlTR_eq hSt hS (xl_zero_lt_N A) (xlU St A S0 0).B_pos]; exact (xlU St A S0 0).R_zero x
  R_nat := fun k x => by
    rw [xlTR_eq hSt hS (xl_zero_lt_N A) ((xlU St A S0 0).nat_lt_B k)]; exact (xlU St A S0 0).R_nat k x
  R_E := fun x => by rw [xlTR_eq hSt hS (xl_zero_lt_N A) (xlU St A S0 0).E_lt_B]; exact (xlU St A S0 0).R_E x
  R_succ := xlTR_succ hSt hS
  R_pos := fun x hx hx1 c hc0 hc hg => by
    obtain ⟨n, hn1, hn⟩ := xlT_cof hSt hS hc
    rw [xlTR_eq hSt hS hn1 hn]; rw [xlTg_eq hSt hS hn1 hn] at hg
    exact (xlU St A S0 n).R_pos x hx hx1 c hc0 hn hg
  R_omega := fun x hx hx1 c hω hc hg => by
    obtain ⟨n, hn1, hn⟩ := xlT_cof hSt hS hc
    rw [xlTR_eq hSt hS hn1 hn]; rw [xlTg_eq hSt hS hn1 hn] at hg
    exact (xlU St A S0 n).R_omega x hx hx1 c hω hn hg
  R_lt_b := fun x hx hx1 hγx c hc hg => by
    obtain ⟨μ, hμ, hcμ, hγμ⟩ := xlT_small hSt hS hc hx hx1 hγx hg
    rw [xlTR_eq hSt hS hμ hcμ]; rw [xlTg_eq hSt hS hμ hcμ] at hg
    exact ((xlU St A S0 μ).R_lt_b x hx hx1 hγμ c hcμ hg).trans (xlT_b_lt hSt hS hμ hx hx1 hγμ)
  R_lt_Z := fun x hx hx1 c hc hg => by
    obtain ⟨n, hn1, hn⟩ := xlT_cof hSt hS hc
    rw [xlTR_eq hSt hS hn1 hn]; rw [xlTg_eq hSt hS hn1 hn] at hg
    exact (((xlU St A S0 n).R_lt_Z x hx hx1 c hn hg).trans_le (xlU_Zb hSt hS hn1 x hx hx1)).trans_le (xlTZ_ge x hx)
  mono := fun x hx hx1 c hc d hfc hgc hgd => by
    obtain ⟨n, hn1, hn⟩ := xlT_cof hSt hS hc
    have hf : d < (xlU St A S0 n).B := hfc.trans hn
    rw [xlTR_eq hSt hS hn1 hn,
        xlTR_eq hSt hS hn1 hf]; rw [xlTg_eq hSt hS hn1 hn] at hgc; rw [xlTg_eq hSt hS hn1 hf] at hgd
    exact (xlU St A S0 n).mono x hx hx1 c hn d hfc hgc hgd
  cof := fun x hx hx1 c hc hg ν hν => by
    obtain ⟨n, hn1, hn⟩ := xlT_cof hSt hS hc
    rw [xlTR_eq hSt hS hn1 hn] at hν; rw [xlTg_eq hSt hS hn1 hn] at hg
    obtain ⟨d, hfc, hgd, hνd⟩ := (xlU St A S0 n).cof x hx hx1 c hn hg ν hν
    have hf : d < (xlU St A S0 n).B := hfc.trans hn
    exact ⟨d, hfc, by rw [xlTg_eq hSt hS hn1 hf]; exact hgd, by rw [xlTR_eq hSt hS hn1 hf]; exact hνd⟩
  b_cof := fun x hx hx1 hγx ν hν => by
    obtain ⟨k, hk⟩ := xlTr_cof hSt hS hx hx1 hγx hν
    have hkT : xlTt A k < hcN (Λ.L + κ) 0 := xlTt_lt A k
    have hkB : xlTt A k < (xlU St A S0 (xlTt A k)).B := xlU_self hSt hS hkT
    refine ⟨xlTt A k, hkT, ?_, ?_⟩
    · rw [xlTg_eq hSt hS hkT hkB]; exact xlTt_g hSt hS hx hx1 hγx k
    · rw [xlTR_eq hSt hS hkT hkB]; exact hk
  b_E := fun x _ _ _ => hcN_E (Λ.l x + κ) _
  x_lt_b := fun x hx hx1 hγx => A.x_lt_N hx hx1 hγx
  b_eN := fun x hx hx1 hγx => gz_eN_fix hx hx1
    (hc_fix_down (hnv_one Λ hx hx1 (A.ν_lt hx hx1 hγx)) (hcN_fix (Λ.l x + κ) _)) (A.x_lt_N hx hx1 hγx)
    (A.N_lt1x hx hx1 hγx)
  ba_lt := fun x hx hx1 hγx => A.N_lt1x hx hx1 hγx
  b_Z := fun x _ _ hγx => by
    show _ < xlTZ A x
    unfold xlTZ; rw [if_pos hγx]
    exact go_eN_lt_evZ (lt_evZ _)
  b_pi := fun _ _ hB hγ => A.N_pi hB hγ
  ba_pi := fun _ _ hB hγ => A.N_pi hB hγ
  ex := fun σ ρ hB c hc hg => by
    obtain ⟨n, hn1, hn⟩ := xlT_cof hSt hS hc
    rw [xlTR_eq hSt hS hn1 hn, xlTR_eq hSt hS hn1 hn]; rw [xlTg_eq hSt hS hn1 hn] at hg
    exact (xlU St A S0 n).ex σ ρ hB c hn hg
  dig := fun σ ρ hB hγσ d hf hg P P' hat => by
    obtain ⟨μ, hμ, hfμ, hγμ⟩ := xlT_small hSt hS hf hB.1 (hB.2.2.1.trans hB.2.2.2) hγσ hg
    rw [xlTR_eq hSt hS hμ hfμ, xlTR_eq hSt hS hμ hfμ]; rw [xlTg_eq hSt hS hμ hfμ] at hg
    exact (xlU St A S0 μ).dig σ ρ hB hγμ d hfμ hg P P' (fun β hβ hβe =>
      hat β hβ (hβe.trans (xlT_b_lt hSt hS hμ hB.2.1 hB.2.2.2 (hγμ.trans hB.2.2.1))))
  ld := fun c hl hc => by
    obtain ⟨n, hn1, hn⟩ := xlT_cof hSt hS hc
    obtain ⟨cp, lp, T, hcp, hgcp, hfec, hex⟩ := (xlU St A S0 n).ld c hl hn
    have hcpn : cp < (xlU St A S0 n).B := hcp.trans hn
    refine ⟨cp, lp, T, hcp, by rw [xlTg_eq hSt hS hn1 hn, xlTg_eq hSt hS hn1 hcpn]; exact hgcp,
        fun x hx hx1 hg => ?_,
      fun σ ρ hB hg => hex σ ρ hB (by rw [← xlTg_eq hSt hS hn1 hn]; exact hg)⟩
    rw [xlTg_eq hSt hS hn1 hn] at hg
    rw [xlTR_eq hSt hS hn1 hn, xlTR_eq hSt hS hn1 hcpn]
    exact hfec x hx hx1 hg

theorem xlTU_B : (xlTU hSt hS).B = hcN (Λ.L + κ) 0 := rfl

theorem xlTU_γ : (xlTU hSt hS).γ = A.γN := rfl

theorem xlTU_b (x : Ordinal.{0}) : (xlTU hSt hS).b x = hcN (Λ.l x + κ) 0 := rfl

/-- **The union extends every start** (readings). -/
theorem xlTU_R {ν c : Ordinal.{0}} (hν : ν < hcN (Λ.L + κ) 0) (hc : c < (xlU St A S0 ν).B) (x : Ordinal.{0}) :
    (xlTU hSt hS).R c x = (xlU St A S0 ν).R c x := xlTR_eq hSt hS hν hc x

/-- **The union extends every start** (gates). -/
theorem xlTU_g {ν c : Ordinal.{0}} (hν : ν < hcN (Λ.L + κ) 0) (hc : c < (xlU St A S0 ν).B) :
    (xlTU hSt hS).g c = (xlU St A S0 ν).g c := xlTg_eq hSt hS hν hc

/-- **The union extends the start `S0`.** -/
theorem xlTU_R0 {c : Ordinal.{0}} (hc : c < S0.B) (x : Ordinal.{0}) : (xlTU hSt hS).R c x = S0.R c x := by
  rw [xlTU_R hSt hS (xl_zero_lt_N A) (by rw [xlU_zero]; exact hc), xlU_zero]

theorem xlTU_g0 {c : Ordinal.{0}} (hc : c < S0.B) : (xlTU hSt hS).g c = S0.g c := by
  rw [xlTU_g hSt hS (xl_zero_lt_N A) (by rw [xlU_zero]; exact hc), xlU_zero]

end Union

end Googology.Trans.PoR.InaccPsi.R2.Xl

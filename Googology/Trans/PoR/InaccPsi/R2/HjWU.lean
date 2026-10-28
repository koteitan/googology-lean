import Googology.Trans.PoR.InaccPsi.R2.HjVG

/-!
# HjWU: THE UNION OF ALL LEVELS `L + κ`, `κ < Ω₁`, OVER A BASE OF LEVEL `L + Ω₁`; THE LEVEL `L + Ω₁` READ `ℓ(x) + x`

The generic form of `Hj.hjU`.  Over a base `P` of level `L + Ω₁` (`Hj.HjWB`) the systems `Hj.hjwL P St0 S0 κ` (bound
`φ(L+κ+1, F+1)`, base gate `max(γ, κ)`) exist for every `κ < Ω₁`.  Their union over ALL `κ < Ω₁` is a gated digit
system (`Hg.HgVD`) with the bound `hdNx (L+Ω₁) F`, the base gate `γ` and the base reading `hdNx (ℓ(x)+x) (F(x))`:
the index `κ` of the level `L + κ` is read with `Ω₁ ↦ x`.  A code of `hjwL κ` with gate below an `ε`-number
`σ > γ` lies in some `hjwL μ`, `μ < σ` (`hjw_small`: the codes past the start of a level `L + κ` have gate `≥ κ`,
`hjw_highN`).

* `hjw_veb_cof` (**`φ(l, i+1)` is the supremum of `N_b(φ(l, i))`, `b < l`**), `hjw_highN`, `hjw_small`;
* `hjwN`, `hjwU` (**THE UNION OVER ALL LEVELS `L + κ` OVER `P`**), `hjwU_B`, `hjwU_γ`, `hjwU_b`, `hjwU_Z`,
  `hjwU_R`, `hjwU_g`, `hjwU_R0`, `hjwU_g0`, `hjwU_high`.

What differs from `Hj.hjU`: a base `P` of level `L + Ω₁` (any gate) in place of `G` at the level `Ω₁ + Ω₁`.

No new axiom.  New definitions: `hjwN`, `hjwU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hj

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

/-- **`φ(l, i+1)` is the supremum of `N_b(φ(l, i))`, `b < l`** (any `i`; `Hg.hgVeb_cof` is the case of a fixed
point). -/
theorem hjw_veb_cof {l i : Ordinal.{0}} (hl0 : l ≠ 0) {c : Ordinal.{0}} (hc : c < veblen l (i + 1)) :
    ∃ b, b < l ∧ c < hcN b (veblen l i) := by
  have e := congrFun (veblen_of_ne_zero hl0) i
  rw [veblen_of_ne_zero hl0, derivFamily_add_one, ← e] at hc
  obtain ⟨L, hL⟩ := lt_nfpFamily_iff.1 hc
  have key : ∀ L : List (Iio l), ∃ b, b < l ∧
      List.foldr (fun x : Iio l => veblen x.1) (veblen l i + 1) L < hcN b (veblen l i) := by
    intro L
    induction L with
    | nil =>
      exact ⟨0, pos_iff_ne_zero.2 hl0,
        (ev_isSuccLimit_of_inE (hcN_E 0 (veblen l i))).add_one_lt (hcN_gt 0 (veblen l i))⟩
    | cons j L ih =>
      obtain ⟨b, hb, hbL⟩ := ih
      refine ⟨max b j.1, max_lt hb j.2, ?_⟩
      show veblen j.1 (List.foldr (fun x : Iio l => veblen x.1) (veblen l i + 1) L) < hcN (max b j.1) (veblen l i)
      calc veblen j.1 (List.foldr (fun x : Iio l => veblen x.1) (veblen l i + 1) L)
          < veblen j.1 (hcN (max b j.1) (veblen l i)) :=
            (isNormal_veblen j.1).strictMono (hbL.trans_le (hcN_mono (le_max_left _ _) _))
        _ = hcN (max b j.1) (veblen l i) := hc_fix_down (le_max_right _ _) (hcN_fix _ _)
  obtain ⟨b, hb, hbL⟩ := key L
  exact ⟨b, hb, hL.trans hbL⟩

/-- **`c < hdNx l v`, `v ∈ range φ(l, ·)`, lies below some `N_b(v)`, `b < l`.** -/
theorem hjw_Nx_cof {l v : Ordinal.{0}} (hl0 : l ≠ 0) (hv : LuP l v) {c : Ordinal.{0}} (hc : c < hdNx l v) :
    ∃ b, b < l ∧ c < hcN b v := by
  obtain ⟨i, rfl⟩ := hv
  rw [hdNx_veb] at hc
  exact hjw_veb_cof hl0 hc

variable {Λ : HjLv}

/-! ## The gates past the start of an offset union over a base of level `L + κ` -/

/-- **The codes past the start `S0` of the offset union of a base `A` of level `L + κ` have a gate `≥` the reading
gate `γN`.** -/
theorem hjw_highN {κ : Ordinal.{0}} {St : ∀ (Q : HjVQ Λ κ) (U : HgVD), HgSStart (hjVPB Q) U → HgVD}
    (hSt : ∀ Q U h, HjVSpec Q U (St Q U h)) {A : HjVB Λ κ} {S0 : HgVD} (hS : HjVStart A S0)
    {c σ : Ordinal.{0}} (hc : c < hcN (Λ.L + κ) A.F) (hBc : S0.B ≤ c) (hσ : InE σ) (hσ1 : σ < Om1)
    (hg : (hjVTU hSt hS).g c < σ) : A.γN < σ := by
  obtain ⟨n, hn1, hn⟩ := hjVT_cof hSt hS hc
  obtain ⟨-, hN1, hcNc⟩ := hjVTN_spec hn1 hn
  have hgN : (hjVTU hSt hS).g c = (hjVU St A S0 (hjVTN St A S0 c)).g c := rfl
  have I := hjV_inv hSt hS _ hN1
  rcases zero_or_succ_or_isSuccLimit (hjVTN St A S0 c) with h0 | ⟨m, hm⟩ | hlim
  · rw [h0, hjVU_zero] at hcNc
    exact absurd hBc (not_le.2 hcNc)
  · have hm' : hjVTN St A S0 c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < hjVTN St A S0 c := by rw [hm']; exact lt_add_one m
    have hml : m < hcN (Λ.L + κ) A.F := hmN.trans hN1
    have hBc' : (hjVU St A S0 m).B ≤ c := not_lt.1 (hjVTN_min hmN hml)
    rw [hgN, hm'] at hg
    rw [hm'] at hcNc I hN1
    have hγ := I.high m (lt_add_one _) c σ hBc' hcNc hσ hσ1 hg
    exact (max_lt_iff.1 ((hjVU_γ_iff hSt hS hN1 hσ hσ1).1 hγ)).1
  · exfalso
    rw [hjVU_B hSt hS hN1] at hcNc
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen (Λ.L + κ)).lt_iff_exists_lt
        (isSuccLimit_add _ hlim)).1 hcNc
    obtain ⟨d, hf, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    have hfl : d < hcN (Λ.L + κ) A.F := hf.trans hN1
    refine hjVTN_min hf hfl ?_
    rw [hjVU_B hSt hS hfl]; exact hct.trans_le ((isNormal_veblen (Λ.L + κ)).monotone htd)

section Union

variable (P : HjWB Λ) (St0 : HjVStTy Λ 0) (h0 : ∀ Q U h, HjVSpec Q U (St0 Q U h)) (S0 : HgVD)
  (hS0 : HjWShape P 0 S0)

include h0 hS0

/-! ## SMALL for the level recursion over `P` -/

/-- **SMALL**: a code of `hjwL κ` with gate below an `ε`-number `σ` lies in some `hjwL μ`, `μ < σ`. -/
theorem hjw_small : ∀ κ, κ < Om1 → ∀ c, c < (hjwL P St0 S0 κ).B → ∀ σ, InE σ → σ < Om1 →
    (hjwL P St0 S0 κ).g c < σ → ∃ μ, μ < σ ∧ c < (hjwL P St0 S0 μ).B := by
  intro κ
  induction κ using WellFoundedLT.induction with
  | ind κ IH =>
  intro hκ c hc σ hσ hσ1 hg
  by_cases hκσ : κ < σ
  · exact ⟨κ, hκσ, hc⟩
  have hI := hjwL_inv P St0 h0 S0 hS0
  rcases zero_or_succ_or_isSuccLimit κ with h0' | ⟨μ, hμ⟩ | hlim
  · exact absurd (by rw [h0']; exact hσ.pos) hκσ
  · have hμ' : κ = μ + 1 := by rw [← hμ, succ_eq_add_one]
    subst hμ'
    have hμ1 : μ < Om1 := (lt_add_one μ).trans hκ
    by_cases hcμ : c < (hjwL P St0 S0 μ).B
    · have e := ((hI (μ + 1) hκ).2 μ (le_add_right le_rfl) c 0 hcμ).2
      rw [e] at hg
      exact IH μ (lt_add_one μ) hμ1 c hcμ σ hσ hσ1 hg
    · exfalso
      have hsh := hjw_ok_shape P hκ (hI μ hμ1).1
      rw [hjwL_succ, hjwSt_eq P St0 h0 hκ hsh] at hc hg
      have h := hjw_highN _ _ hc (not_lt.1 hcμ) hσ hσ1 hg
      exact hκσ (max_lt_iff.1 h).2
  · have hcoh : HjWCoh P κ (fun κ' _ => hjwL P St0 S0 κ') :=
      ⟨fun κ' h => (hI κ' (h.trans hκ)).1, fun κ₁ κ₂ h₁ h₂ h12 c x hc =>
        (hI κ₂ (h₂.trans hκ)).2 κ₁ h12 c x hc⟩
    have eU : hjwChU P S0 κ hlim (fun κ' _ => hjwL P St0 S0 κ') =
        (hjwCh P κ hlim hκ (fun κ' _ => hjwL P St0 S0 κ') hcoh).U := by
      unfold hjwChU; rw [dif_pos ⟨hκ, hcoh⟩]
    have hsh := hjwCh_shape P κ hlim hκ (fun κ' _ => hjwL P St0 S0 κ') hcoh
    by_cases hcS : c < veblen (Λ.L + κ) (P.F + 1)
    · obtain ⟨b, hb, hcb⟩ := hgVeb_cof (hjv_L0 Λ κ) (P.wfix (hjw_Lk hκ)) hcS
      obtain ⟨κ'', hκ'', hbκ⟩ := (lt_add_iff hlim.bot_lt.ne').1 hb
      have hκ''1 : κ'' < Om1 := hκ''.trans hκ
      have hcν : c < (hjwL P St0 S0 κ'').B := by
        rw [(hI κ'' hκ''1).1.1]; exact hcb.trans_le (hcN_mono hbκ _)
      have e2 := ((hI κ hκ).2 κ'' hκ''.le c 0 hcν).2
      rw [e2] at hg
      exact IH κ'' hκ'' hκ''1 c hcν σ hσ hσ1 hg
    · exfalso
      rw [hjwL_limit P St0 S0 hlim, eU, hjwSt_eq P St0 h0 hκ hsh] at hc hg
      have h := hjw_highN _ _ hc (by rw [hsh.1]; exact not_lt.1 hcS) hσ hσ1 hg
      exact hκσ (max_lt_iff.1 h).2

/-! ## The union -/

theorem hjwB_gt {κ : Ordinal.{0}} (hκ : κ < Om1) : (hjwL P St0 S0 κ).B < hdNx (Λ.L + Om1) P.F := by
  rw [((hjwL_inv P St0 h0 S0 hS0) κ hκ).1.1]; exact hjw_N_lt_S P hκ

theorem hjwB_cof {c : Ordinal.{0}} (hc : c < hdNx (Λ.L + Om1) P.F) :
    ∃ κ, κ < Om1 ∧ c < (hjwL P St0 S0 κ).B := by
  obtain ⟨b, hb, hcb⟩ := hjw_Nx_cof (hjv_L0 Λ Om1) P.F_P hc
  obtain ⟨κ, hκ, hbκ⟩ := (lt_add_iff gv_Om1_pos.ne').1 hb
  exact ⟨κ, hκ, by rw [((hjwL_inv P St0 h0 S0 hS0) κ hκ).1.1]; exact hcb.trans_le (hcN_mono hbκ _)⟩

omit h0 hS0 in
theorem hjw_B_E : InE (hdNx (Λ.L + Om1) P.F) := hdNx_E (hjv_L0 Λ Om1) _

omit h0 hS0 in
theorem hjw_B_lim : IsSuccLimit (hdNx (Λ.L + Om1) P.F) := ev_isSuccLimit_of_inE (hjw_B_E P)

omit h0 hS0 in
/-- The first level containing `c`. -/
noncomputable def hjwN (c : Ordinal.{0}) : Ordinal.{0} := sInf {κ | κ < Om1 ∧ c < (hjwL P St0 S0 κ).B}

omit h0 hS0 in
theorem hjwN_spec {c κ : Ordinal.{0}} (hκ : κ < Om1) (hc : c < (hjwL P St0 S0 κ).B) :
    hjwN P St0 S0 c ≤ κ ∧ hjwN P St0 S0 c < Om1 ∧ c < (hjwL P St0 S0 (hjwN P St0 S0 c)).B := by
  have hne : ({κ | κ < Om1 ∧ c < (hjwL P St0 S0 κ).B} : Set Ordinal.{0}).Nonempty := ⟨κ, hκ, hc⟩
  have hm := csInf_mem hne
  exact ⟨csInf_le' ⟨hκ, hc⟩, hm.1, hm.2⟩

theorem hjwN_high {c : Ordinal.{0}} (hc : hdNx (Λ.L + Om1) P.F ≤ c) : hjwN P St0 S0 c = 0 := by
  unfold hjwN
  have he : ({κ | κ < Om1 ∧ c < (hjwL P St0 S0 κ).B} : Set Ordinal.{0}) = ∅ := by
    ext κ
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hκ hcκ
    exact absurd (hcκ.trans (hjwB_gt P St0 h0 S0 hS0 hκ)) (not_lt.2 hc)
  rw [he]; exact Ordinal.sInf_empty

theorem hjw_R_eq {c κ : Ordinal.{0}} (hκ : κ < Om1) (hc : c < (hjwL P St0 S0 κ).B) (x : Ordinal.{0}) :
    (hjwL P St0 S0 (hjwN P St0 S0 c)).R c x = (hjwL P St0 S0 κ).R c x := by
  obtain ⟨h1, -, h3⟩ := hjwN_spec P St0 S0 hκ hc
  exact (((hjwL_inv P St0 h0 S0 hS0) κ hκ).2 _ h1 c x h3).1.symm

theorem hjw_g_eq {c κ : Ordinal.{0}} (hκ : κ < Om1) (hc : c < (hjwL P St0 S0 κ).B) :
    (hjwL P St0 S0 (hjwN P St0 S0 c)).g c = (hjwL P St0 S0 κ).g c := by
  obtain ⟨h1, -, h3⟩ := hjwN_spec P St0 S0 hκ hc
  exact (((hjwL_inv P St0 h0 S0 hS0) κ hκ).2 _ h1 c 0 h3).2.symm

theorem hjw_R_succ (c x : Ordinal.{0}) :
    (hjwL P St0 S0 (hjwN P St0 S0 (c + 1))).R (c + 1) x = (hjwL P St0 S0 (hjwN P St0 S0 c)).R c x + 1 := by
  rcases lt_or_ge c (hdNx (Λ.L + Om1) P.F) with h | h
  · obtain ⟨n, hn1, hn⟩ := hjwB_cof P St0 h0 S0 hS0 ((hjw_B_lim P).add_one_lt h)
    rw [hjw_R_eq P St0 h0 S0 hS0 hn1 hn, hjw_R_eq P St0 h0 S0 hS0 hn1 ((lt_add_one c).trans hn),
      (hjwL P St0 S0 n).R_succ]
  · rw [hjwN_high P St0 h0 S0 hS0 h, hjwN_high P St0 h0 S0 hS0 (h.trans (le_self_add (a := c) (b := 1))),
      (hjwL P St0 S0 0).R_succ]

theorem hjw_g_le_succ (c : Ordinal.{0}) :
    (hjwL P St0 S0 (hjwN P St0 S0 c)).g c ≤ (hjwL P St0 S0 (hjwN P St0 S0 (c + 1))).g (c + 1) := by
  rcases lt_or_ge c (hdNx (Λ.L + Om1) P.F) with h | h
  · obtain ⟨n, hn1, hn⟩ := hjwB_cof P St0 h0 S0 hS0 ((hjw_B_lim P).add_one_lt h)
    rw [hjw_g_eq P St0 h0 S0 hS0 hn1 hn, hjw_g_eq P St0 h0 S0 hS0 hn1 ((lt_add_one c).trans hn)]
    exact (hjwL P St0 S0 n).g_le_succ c
  · rw [hjwN_high P St0 h0 S0 hS0 h, hjwN_high P St0 h0 S0 hS0 (h.trans (le_self_add (a := c) (b := 1)))]
    exact (hjwL P St0 S0 0).g_le_succ c

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : P.γ < x)
include hx hx1 hγ

/-- **The bound field of every `hjwL κ` lies below `hdNx (ℓ(x)+x) (F(x))`** (`γ < x`). -/
theorem hjw_Z_le {κ : Ordinal.{0}} (hκ : κ < Om1) : (hjwL P St0 S0 κ).Z x ≤ hdNx (Λ.l x + x) (P.Fr x) := by
  rw [((hjwL_inv P St0 h0 S0 hS0) κ hκ).1.2.2.2.1 x hx hx1]
  split_ifs with h
  · exact (hb_evZ_lt_fix2 (hdNx_fix (lt_of_lt_of_le (show (2 : Ordinal.{0}) < ω from by
        exact_mod_cast natCast_lt_omega0 2) (hjv_ωl Λ hx hx1).le) _)
      (hjw_rN_lt_S P hx (max_lt_iff.1 h).2)).le
  · rw [P.hjwZo_eq hx hγ]

/-- **The base reading of `hjwL κ` lies below `hdNx (ℓ(x)+x) (F(x))`** (`κ < x`). -/
theorem hjw_b_lt {κ : Ordinal.{0}} (hκ : κ < x) : (hjwL P St0 S0 κ).b x < hdNx (Λ.l x + x) (P.Fr x) := by
  rw [((hjwL_inv P St0 h0 S0 hS0) κ (hκ.trans hx1)).1.2.2.1 x hx hx1 (max_lt hγ hκ)]
  exact hjw_rN_lt_S P hx hκ

end Base

omit h0 hS0 in
theorem hjw_b_fix1 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    veblen 1 (hdNx (Λ.l x + x) (P.Fr x)) = hdNx (Λ.l x + x) (P.Fr x) :=
  hdNx_fix (one_lt_omega0.trans (hjv_ωl Λ hx hx1)) _

omit h0 hS0 in
theorem hjw_x_lt_b {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : P.γ < x) :
    x < hdNx (Λ.l x + x) (P.Fr x) := (P.Fr_gtx hx hx1 hγ).trans (hdNx_gt _ _)

/-- **A code of the union with gate below an `ε`-number `σ` lies in `hjwL μ`, `μ < σ`.** -/
theorem hjw_small' {c σ : Ordinal.{0}} (hc : c < hdNx (Λ.L + Om1) P.F) (hσ : InE σ) (hσ1 : σ < Om1)
    (hg : (hjwL P St0 S0 (hjwN P St0 S0 c)).g c < σ) : ∃ μ, μ < σ ∧ c < (hjwL P St0 S0 μ).B := by
  obtain ⟨n, hn1, hn⟩ := hjwB_cof P St0 h0 S0 hS0 hc
  rw [hjw_g_eq P St0 h0 S0 hS0 hn1 hn] at hg
  exact hjw_small P St0 h0 S0 hS0 n hn1 c hn σ hσ hσ1 hg

theorem hjw_γ_lt {μ x : Ordinal.{0}} (hγ : P.γ < x) (hμ : μ < x) (hμ1 : μ < Om1) : (hjwL P St0 S0 μ).γ < x := by
  rw [((hjwL_inv P St0 h0 S0 hS0) μ hμ1).1.2.1]; exact max_lt hγ hμ

omit h0 hS0 in
open Classical in
/-- The bound field of the union. -/
noncomputable def hjwUZ (x : Ordinal.{0}) : Ordinal.{0} :=
  if P.γ < x then evZ (hdNx (Λ.l x + x) (P.Fr x)) else P.Zo x

/-- **THE UNION OVER ALL LEVELS `L + κ`, `κ < Ω₁`, OVER `P`**: a gated digit system (`HgVD`) with the bound
`hdNx (L+Ω₁) F`, the base gate `γ`, the base reading `hdNx (ℓ(x)+x) (F(x))` (the level `L + Ω₁` read as `ℓ(x)+x`). -/
noncomputable def hjwU : HgVD where
  B := hdNx (Λ.L + Om1) P.F
  γ := P.γ
  γ_lt := P.γ_lt
  γ_cl := fun Z hZ hZ1 h => P.S_cl Z hZ hZ1 h
  γ_G := fun h => absurd h (P.G_le.trans_lt (hdNx_gt _ _)).ne'
  R := fun c x => (hjwL P St0 S0 (hjwN P St0 S0 c)).R c x
  g := fun c => (hjwL P St0 S0 (hjwN P St0 S0 c)).g c
  b := fun x => hdNx (Λ.l x + x) (P.Fr x)
  ba := fun x => hdNx (Λ.l x + x) (P.Fr x)
  ix := hdNx (Λ.L + Om1) P.F
  Z := hjwUZ P
  B_E := hjw_B_E P
  G_le := P.G_le.trans (hdNx_gt _ _).le
  B_lt1 := P.S_lt1
  B_ix := (hdNx_fix ((hg_one_lt_Om1.trans_le Λ.OL).trans_le le_self_add) _).symm
  Z_fix := fun x _ _ => by
    unfold hjwUZ; split_ifs
    · exact epsilon_evZ _
    · exact hc_fix_down one_le_two (P.Zo_fix x)
  Z_G1 := fun x hx hx1 => by
    unfold hjwUZ; split_ifs with h
    · exact gw_evZ_lt1 hx hx1 (P.wS_lt1x hx hx1 h)
    · exact P.Zo_G1 x hx hx1
  ix_mem := fun S a b ha hb => P.S_mem S ha hb
  g_lt := fun c hc => by
    obtain ⟨n, hn1, hn⟩ := hjwB_cof P St0 h0 S0 hS0 hc
    show (hjwL P St0 S0 (hjwN P St0 S0 c)).g c < Om1
    rw [hjw_g_eq P St0 h0 S0 hS0 hn1 hn]; exact (hjwL P St0 S0 n).g_lt c hn
  g_zero := by
    show (hjwL P St0 S0 (hjwN P St0 S0 0)).g 0 = 0
    rw [hjw_g_eq P St0 h0 S0 hS0 gv_Om1_pos (hjwL P St0 S0 0).B_pos]; exact (hjwL P St0 S0 0).g_zero
  g_nat := fun k => by
    show (hjwL P St0 S0 (hjwN P St0 S0 k)).g k < ω
    rw [hjw_g_eq P St0 h0 S0 hS0 gv_Om1_pos ((hjwL P St0 S0 0).nat_lt_B k)]; exact (hjwL P St0 S0 0).g_nat k
  g_E := by
    show (hjwL P St0 S0 (hjwN P St0 S0 gfE)).g gfE = 0
    rw [hjw_g_eq P St0 h0 S0 hS0 gv_Om1_pos (hjwL P St0 S0 0).E_lt_B]; exact (hjwL P St0 S0 0).g_E
  g_lowE := fun c hc => by
    show (hjwL P St0 S0 (hjwN P St0 S0 c)).g c = gtc c
    rw [hjw_g_eq P St0 h0 S0 hS0 gv_Om1_pos (hc.trans (hjwL P St0 S0 0).E_lt_B)]
    exact (hjwL P St0 S0 0).g_lowE c hc
  g_G0 := fun h => by
    obtain ⟨n, hn1, hn⟩ := hjwB_cof P St0 h0 S0 hS0 h
    show (hjwL P St0 S0 (hjwN P St0 S0 (gcG 0))).g (gcG 0) = 0
    rw [hjw_g_eq P St0 h0 S0 hS0 hn1 hn]; exact (hjwL P St0 S0 n).g_G0 hn
  g_add := fun Z hZ hωZ x y hxy hgx hgy => by
    obtain ⟨n, hn1, hn⟩ := hjwB_cof P St0 h0 S0 hS0 hxy
    have hx : x < (hjwL P St0 S0 n).B := lt_of_le_of_lt le_self_add hn
    have hy : y < (hjwL P St0 S0 n).B := lt_of_le_of_lt le_add_self hn
    show (hjwL P St0 S0 (hjwN P St0 S0 (x + y))).g (x + y) < Z
    have hgx' : (hjwL P St0 S0 (hjwN P St0 S0 x)).g x < Z := hgx
    have hgy' : (hjwL P St0 S0 (hjwN P St0 S0 y)).g y < Z := hgy
    rw [hjw_g_eq P St0 h0 S0 hS0 hn1 hn]; rw [hjw_g_eq P St0 h0 S0 hS0 hn1 hx] at hgx'
    rw [hjw_g_eq P St0 h0 S0 hS0 hn1 hy] at hgy'
    exact (hjwL P St0 S0 n).g_add Z hZ hωZ x y hn hgx' hgy'
  g_opow := fun Z hZw hωZ y hy hg => by
    obtain ⟨n, hn1, hn⟩ := hjwB_cof P St0 h0 S0 hS0 hy
    have hy' : y < (hjwL P St0 S0 n).B := lt_of_le_of_lt (right_le_opow y one_lt_omega0) hn
    show (hjwL P St0 S0 (hjwN P St0 S0 (ω ^ y))).g (ω ^ y) < Z
    have hg' : (hjwL P St0 S0 (hjwN P St0 S0 y)).g y < Z := hg
    rw [hjw_g_eq P St0 h0 S0 hS0 hn1 hn]; rw [hjw_g_eq P St0 h0 S0 hS0 hn1 hy'] at hg'
    exact (hjwL P St0 S0 n).g_opow Z hZw hωZ y hn hg'
  code_gate := fun Z hZ1 hZ0 hZa hZp At hAt c hc hcB => by
    obtain ⟨n, hn1, hn⟩ := hjwB_cof P St0 h0 S0 hS0 hcB
    show (hjwL P St0 S0 (hjwN P St0 S0 c)).g c < Z
    rw [hjw_g_eq P St0 h0 S0 hS0 hn1 hn]
    exact (hjwL P St0 S0 n).code_gate Z hZ1 hZ0 hZa hZp At (fun s hs => (hAt s hs).imp_right
      (fun h => (hjwB_gt P St0 h0 S0 hS0 hn1).le.trans h)) c hc hn
  g_succ := fun Z hZ c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hjwB_cof P St0 h0 S0 hS0 hc
    have hc' : c < (hjwL P St0 S0 n).B := (lt_add_one c).trans hn
    show (hjwL P St0 S0 (hjwN P St0 S0 (c + 1))).g (c + 1) < Z
    have hg' : (hjwL P St0 S0 (hjwN P St0 S0 c)).g c < Z := hg
    rw [hjw_g_eq P St0 h0 S0 hS0 hn1 hn]; rw [hjw_g_eq P St0 h0 S0 hS0 hn1 hc'] at hg'
    exact (hjwL P St0 S0 n).g_succ Z hZ c hn hg'
  g_le_succ := hjw_g_le_succ P St0 h0 S0 hS0
  mem := fun S a b ha c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hjwB_cof P St0 h0 S0 hS0 hc
    have hg' : (hjwL P St0 S0 (hjwN P St0 S0 c)).g c < b := hg
    rw [hjw_g_eq P St0 h0 S0 hS0 hn1 hn] at hg'
    exact (hjwL P St0 S0 n).mem S a b ha c hn hg'
  R_zero := fun x => by
    show (hjwL P St0 S0 (hjwN P St0 S0 0)).R 0 x = 0
    rw [hjw_R_eq P St0 h0 S0 hS0 gv_Om1_pos (hjwL P St0 S0 0).B_pos]; exact (hjwL P St0 S0 0).R_zero x
  R_nat := fun k x => by
    show (hjwL P St0 S0 (hjwN P St0 S0 k)).R k x = k
    rw [hjw_R_eq P St0 h0 S0 hS0 gv_Om1_pos ((hjwL P St0 S0 0).nat_lt_B k)]; exact (hjwL P St0 S0 0).R_nat k x
  R_E := fun x => by
    show (hjwL P St0 S0 (hjwN P St0 S0 gfE)).R gfE x = eN x
    rw [hjw_R_eq P St0 h0 S0 hS0 gv_Om1_pos (hjwL P St0 S0 0).E_lt_B]; exact (hjwL P St0 S0 0).R_E x
  R_succ := hjw_R_succ P St0 h0 S0 hS0
  R_pos := fun x hx hx1 c hc0 hc hg => by
    obtain ⟨n, hn1, hn⟩ := hjwB_cof P St0 h0 S0 hS0 hc
    show 0 < (hjwL P St0 S0 (hjwN P St0 S0 c)).R c x
    have hg' : (hjwL P St0 S0 (hjwN P St0 S0 c)).g c < x := hg
    rw [hjw_R_eq P St0 h0 S0 hS0 hn1 hn]; rw [hjw_g_eq P St0 h0 S0 hS0 hn1 hn] at hg'
    exact (hjwL P St0 S0 n).R_pos x hx hx1 c hc0 hn hg'
  R_omega := fun x hx hx1 c hω hc hg => by
    obtain ⟨n, hn1, hn⟩ := hjwB_cof P St0 h0 S0 hS0 hc
    show ω ≤ (hjwL P St0 S0 (hjwN P St0 S0 c)).R c x
    have hg' : (hjwL P St0 S0 (hjwN P St0 S0 c)).g c < x := hg
    rw [hjw_R_eq P St0 h0 S0 hS0 hn1 hn]; rw [hjw_g_eq P St0 h0 S0 hS0 hn1 hn] at hg'
    exact (hjwL P St0 S0 n).R_omega x hx hx1 c hω hn hg'
  R_lt_b := fun x hx hx1 hγ c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hjwB_cof P St0 h0 S0 hS0 hc
    show (hjwL P St0 S0 (hjwN P St0 S0 c)).R c x < hdNx (Λ.l x + x) (P.Fr x)
    have hg' : (hjwL P St0 S0 (hjwN P St0 S0 c)).g c < x := hg
    rw [hjw_R_eq P St0 h0 S0 hS0 hn1 hn]; rw [hjw_g_eq P St0 h0 S0 hS0 hn1 hn] at hg'
    exact ((hjwL P St0 S0 n).R_lt_Z x hx hx1 c hn hg').trans_le (hjw_Z_le P St0 h0 S0 hS0 hx hx1 hγ hn1)
  R_lt_Z := fun x hx hx1 c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hjwB_cof P St0 h0 S0 hS0 hc
    show (hjwL P St0 S0 (hjwN P St0 S0 c)).R c x < hjwUZ P x
    have hg' : (hjwL P St0 S0 (hjwN P St0 S0 c)).g c < x := hg
    rw [hjw_R_eq P St0 h0 S0 hS0 hn1 hn]; rw [hjw_g_eq P St0 h0 S0 hS0 hn1 hn] at hg'
    have h1 := (hjwL P St0 S0 n).R_lt_Z x hx hx1 c hn hg'
    unfold hjwUZ
    split_ifs with hγ
    · exact (h1.trans_le (hjw_Z_le P St0 h0 S0 hS0 hx hx1 hγ hn1)).trans (lt_evZ _)
    · rw [((hjwL_inv P St0 h0 S0 hS0) n hn1).1.2.2.2.1 x hx hx1,
        if_neg (fun h => hγ (max_lt_iff.1 h).1), P.hjwZo_low hγ] at h1
      exact h1
  mono := fun x hx hx1 c hc d hdc hgc hgd => by
    obtain ⟨n, hn1, hn⟩ := hjwB_cof P St0 h0 S0 hS0 hc
    have hd : d < (hjwL P St0 S0 n).B := hdc.trans hn
    show (hjwL P St0 S0 (hjwN P St0 S0 d)).R d x < (hjwL P St0 S0 (hjwN P St0 S0 c)).R c x
    have hgc' : (hjwL P St0 S0 (hjwN P St0 S0 c)).g c < x := hgc
    have hgd' : (hjwL P St0 S0 (hjwN P St0 S0 d)).g d < x := hgd
    rw [hjw_R_eq P St0 h0 S0 hS0 hn1 hn, hjw_R_eq P St0 h0 S0 hS0 hn1 hd]
    rw [hjw_g_eq P St0 h0 S0 hS0 hn1 hn] at hgc'; rw [hjw_g_eq P St0 h0 S0 hS0 hn1 hd] at hgd'
    exact (hjwL P St0 S0 n).mono x hx hx1 c hn d hdc hgc' hgd'
  cof := fun x hx hx1 c hc hg ν hν => by
    obtain ⟨n, hn1, hn⟩ := hjwB_cof P St0 h0 S0 hS0 hc
    have hg' : (hjwL P St0 S0 (hjwN P St0 S0 c)).g c < x := hg
    have hν' : ν < (hjwL P St0 S0 (hjwN P St0 S0 c)).R c x := hν
    rw [hjw_R_eq P St0 h0 S0 hS0 hn1 hn] at hν'; rw [hjw_g_eq P St0 h0 S0 hS0 hn1 hn] at hg'
    obtain ⟨d, hdc, hgd, hνd⟩ := (hjwL P St0 S0 n).cof x hx hx1 c hn hg' ν hν'
    have hd : d < (hjwL P St0 S0 n).B := hdc.trans hn
    exact ⟨d, hdc, by
      show (hjwL P St0 S0 (hjwN P St0 S0 d)).g d < x; rw [hjw_g_eq P St0 h0 S0 hS0 hn1 hd]; exact hgd,
      by show ν ≤ (hjwL P St0 S0 (hjwN P St0 S0 d)).R d x; rw [hjw_R_eq P St0 h0 S0 hS0 hn1 hd]; exact hνd⟩
  b_cof := fun x hx hx1 hγ ν hν => by
    obtain ⟨b, hb, hνb⟩ := hjw_Nx_cof (omega0_pos.trans (hjv_ωl Λ hx hx1 (ν := x))).ne' (P.Fr_P hx hx1 hγ) hν
    obtain ⟨κ, hκ, hbκ⟩ := (lt_add_iff hx.pos.ne').1 hb
    have hκ1 : κ < Om1 := hκ.trans hx1
    have hνb' : ν < (hjwL P St0 S0 κ).b x := by
      rw [((hjwL_inv P St0 h0 S0 hS0) κ hκ1).1.2.2.1 x hx hx1 (max_lt hγ hκ)]
      exact hνb.trans_le (hcN_mono hbκ _)
    obtain ⟨d, hd, hgd, hνd⟩ := (hjwL P St0 S0 κ).b_cof x hx hx1 (hjw_γ_lt P St0 h0 S0 hS0 hγ hκ hκ1) ν hνb'
    exact ⟨d, hd.trans (hjwB_gt P St0 h0 S0 hS0 hκ1), by
      show (hjwL P St0 S0 (hjwN P St0 S0 d)).g d < x; rw [hjw_g_eq P St0 h0 S0 hS0 hκ1 hd]; exact hgd,
      by show ν < (hjwL P St0 S0 (hjwN P St0 S0 d)).R d x; rw [hjw_R_eq P St0 h0 S0 hS0 hκ1 hd]; exact hνd⟩
  b_E := fun x hx hx1 _ => hdNx_E (omega0_pos.trans (hjv_ωl Λ hx hx1 (ν := x))).ne' _
  x_lt_b := fun x hx hx1 hγ => hjw_x_lt_b P hx hx1 hγ
  b_eN := fun x hx hx1 hγ => gz_eN_fix hx hx1 (hjw_b_fix1 P hx hx1) (hjw_x_lt_b P hx hx1 hγ) (P.wS_lt1x hx hx1 hγ)
  ba_lt := fun x hx hx1 hγ => P.wS_lt1x hx hx1 hγ
  b_Z := fun x _ _ hγ => by unfold hjwUZ; rw [if_pos hγ]; exact go_eN_lt_evZ (lt_evZ _)
  b_pi := fun _ _ hB hγ => P.S_pi hB hγ
  ba_pi := fun _ _ hB hγ => P.S_pi hB hγ
  ex := fun σ ρ hB c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hjwB_cof P St0 h0 S0 hS0 hc
    show (hjwL P St0 S0 (hjwN P St0 S0 c)).R c ρ ∈ TB ρ σ ∧
      pi σ ρ ((hjwL P St0 S0 (hjwN P St0 S0 c)).R c ρ) = (hjwL P St0 S0 (hjwN P St0 S0 c)).R c σ
    have hg' : (hjwL P St0 S0 (hjwN P St0 S0 c)).g c < σ := hg
    rw [hjw_R_eq P St0 h0 S0 hS0 hn1 hn, hjw_R_eq P St0 h0 S0 hS0 hn1 hn]
    rw [hjw_g_eq P St0 h0 S0 hS0 hn1 hn] at hg'
    exact (hjwL P St0 S0 n).ex σ ρ hB c hn hg'
  dig := fun σ ρ hB hγ d hd hg P' P'' hat => by
    have hσ1 : σ < Om1 := hB.2.2.1.trans hB.2.2.2
    obtain ⟨μ, hμσ, hdμ⟩ := hjw_small' P St0 h0 S0 hS0 hd hB.1 hσ1 hg
    have hμ1 : μ < Om1 := hμσ.trans hσ1
    show ω ^ P' * (hjwL P St0 S0 (hjwN P St0 S0 d)).R d ρ ∈ TB ρ σ ∧
      pi σ ρ (ω ^ P' * (hjwL P St0 S0 (hjwN P St0 S0 d)).R d ρ) =
        ω ^ P'' * (hjwL P St0 S0 (hjwN P St0 S0 d)).R d σ
    have hg' : (hjwL P St0 S0 (hjwN P St0 S0 d)).g d < σ := hg
    rw [hjw_R_eq P St0 h0 S0 hS0 hμ1 hdμ, hjw_R_eq P St0 h0 S0 hS0 hμ1 hdμ]
    rw [hjw_g_eq P St0 h0 S0 hS0 hμ1 hdμ] at hg'
    exact (hjwL P St0 S0 μ).dig σ ρ hB (hjw_γ_lt P St0 h0 S0 hS0 hγ hμσ hμ1) d hdμ hg' P' P'' (fun β hβ hβe =>
      hat β hβ (hβe.trans (hjw_b_lt P St0 h0 S0 hS0 hB.2.1 hB.2.2.2 (hγ.trans hB.2.2.1)
        (hμσ.trans hB.2.2.1))))
  ld := fun c hl hc => by
    obtain ⟨n, hn1, hn⟩ := hjwB_cof P St0 h0 S0 hS0 hc
    obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := (hjwL P St0 S0 n).ld c hl hn
    have hcpn : cp < (hjwL P St0 S0 n).B := hcp.trans hn
    refine ⟨cp, lp, T, hcp, ?_, fun x hx hx1 hg => ?_, fun σ ρ hB hg => hex σ ρ hB ?_⟩
    · show (hjwL P St0 S0 (hjwN P St0 S0 cp)).g cp ≤ (hjwL P St0 S0 (hjwN P St0 S0 c)).g c
      rw [hjw_g_eq P St0 h0 S0 hS0 hn1 hn, hjw_g_eq P St0 h0 S0 hS0 hn1 hcpn]; exact hgcp
    · have hg' : (hjwL P St0 S0 n).g c < x := by rw [← hjw_g_eq P St0 h0 S0 hS0 hn1 hn]; exact hg
      show (hjwL P St0 S0 (hjwN P St0 S0 c)).R c x = _ ∧ _
      rw [hjw_R_eq P St0 h0 S0 hS0 hn1 hn, hjw_R_eq P St0 h0 S0 hS0 hn1 hcpn]
      exact hdec x hx hx1 hg'
    · rw [← hjw_g_eq P St0 h0 S0 hS0 hn1 hn]; exact hg

theorem hjwU_B : (hjwU P St0 h0 S0 hS0).B = hdNx (Λ.L + Om1) P.F := rfl

theorem hjwU_γ : (hjwU P St0 h0 S0 hS0).γ = P.γ := rfl

theorem hjwU_b (x : Ordinal.{0}) : (hjwU P St0 h0 S0 hS0).b x = hdNx (Λ.l x + x) (P.Fr x) := rfl

theorem hjwU_Z (x : Ordinal.{0}) :
    (hjwU P St0 h0 S0 hS0).Z x = if P.γ < x then evZ (hdNx (Λ.l x + x) (P.Fr x)) else P.Zo x := rfl

/-- **The union extends every `hjwL κ`** (readings). -/
theorem hjwU_R {κ c : Ordinal.{0}} (hκ : κ < Om1) (hc : c < (hjwL P St0 S0 κ).B) (x : Ordinal.{0}) :
    (hjwU P St0 h0 S0 hS0).R c x = (hjwL P St0 S0 κ).R c x := hjw_R_eq P St0 h0 S0 hS0 hκ hc x

/-- **The union extends every `hjwL κ`** (gates). -/
theorem hjwU_g {κ c : Ordinal.{0}} (hκ : κ < Om1) (hc : c < (hjwL P St0 S0 κ).B) :
    (hjwU P St0 h0 S0 hS0).g c = (hjwL P St0 S0 κ).g c := hjw_g_eq P St0 h0 S0 hS0 hκ hc

/-- **The union extends its start** (readings and gates). -/
theorem hjwU_R0 {c : Ordinal.{0}} (hc : c < S0.B) (x : Ordinal.{0}) : (hjwU P St0 h0 S0 hS0).R c x = S0.R c x := by
  rw [hjwU_R P St0 h0 S0 hS0 gv_Om1_pos (?_ : c < (hjwL P St0 S0 0).B) x, hjwL_zero]
  · exact (hjwSt_ext P St0 h0 gv_Om1_pos hS0 hc).1 x
  · rw [((hjwL_inv P St0 h0 S0 hS0) 0 gv_Om1_pos).1.1, add_zero]
    refine hc.trans_le ?_
    rw [hS0.1, add_zero, ← hdNx_fixP (P.wfix ((lt_add_iff_pos_right _).2 gv_Om1_pos))]
    exact (hdNx_lt_N (hcN_gt _ _)).le

theorem hjwU_g0 {c : Ordinal.{0}} (hc : c < S0.B) : (hjwU P St0 h0 S0 hS0).g c = S0.g c := by
  rw [hjwU_g P St0 h0 S0 hS0 gv_Om1_pos (?_ : c < (hjwL P St0 S0 0).B), hjwL_zero]
  · exact (hjwSt_ext P St0 h0 gv_Om1_pos hS0 hc).2
  · rw [((hjwL_inv P St0 h0 S0 hS0) 0 gv_Om1_pos).1.1, add_zero]
    refine hc.trans_le ?_
    rw [hS0.1, add_zero, ← hdNx_fixP (P.wfix ((lt_add_iff_pos_right _).2 gv_Om1_pos))]
    exact (hdNx_lt_N (hcN_gt _ _)).le

/-- **A code `c ∈ [F, hdNx (L+Ω₁) F)` of the union with gate below an `ε`-number `σ` forces `γ < σ`.** -/
theorem hjwU_high {c σ : Ordinal.{0}} (hFc : P.F ≤ c) (hc : c < hdNx (Λ.L + Om1) P.F) (hσ : InE σ)
    (hσ1 : σ < Om1) (hg : (hjwU P St0 h0 S0 hS0).g c < σ) : P.γ < σ := by
  obtain ⟨n, hn1, hn⟩ := hjwB_cof P St0 h0 S0 hS0 hc
  rw [hjwU_g P St0 h0 S0 hS0 hn1 hn] at hg
  exact ((hjwL_inv P St0 h0 S0 hS0) n hn1).1.2.2.2.2 c σ hFc hn hσ hσ1 hg

end Union

end Googology.Trans.PoR.InaccPsi.R2.Hj

import Googology.Trans.PoR.InaccPsi.R2.HlVG

/-!
# HlWU: THE UNION OF ALL GATED LEVELS `L + κ`, `κ < Ω₁`, OVER A TWO-GATE BASE OF LEVEL `L + Ω₁`

PORT of `Hj.HjWU` (`Hj.hjw_veb_cof`, `Hj.hjw_Nx_cof` are imported); the union `hlwU` has the base gate `γR`.

What differs from the source: the level datum is a GATED one (`Hl.HlLv`: Lemma EXACT for the reading `ℓ` only at
base pairs `(σ, ρ)` above the level gate `g`, the hull membership of `L` only at `0 < a`, `g < b`, the code gate
`g < Z` only when a code over `Z` exists at the level); every pseudo-base and base carries `g ≤` its reading gate
(fields `lg`), and the code-gate fields take the extra hypothesis `g < Z`.  Proofs are otherwise those of the source;
names: prefix `hl`/`Hl` in place of `hj`/`Hj`.

No new axiom.  New definitions: `hlwN`, `hlwU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hl

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

variable {Λ : HlLv}

/-! ## The gates past the start of an offset union over a base of level `L + κ` -/

/-- **The codes past the start `S0` of the offset union of a base `A` of level `L + κ` have a gate `≥` the reading
gate `γN`.** -/
theorem hlw_highN {κ : Ordinal.{0}} {St : ∀ (Q : HlVQ Λ κ) (U : HgVD), HgSStart (hlVPB Q) U → HgVD}
    (hSt : ∀ Q U h, HlVSpec Q U (St Q U h)) {A : HlVB Λ κ} {S0 : HgVD} (hS : HlVStart A S0)
    {c σ : Ordinal.{0}} (hc : c < hcN (Λ.L + κ) A.F) (hBc : S0.B ≤ c) (hσ : InE σ) (hσ1 : σ < Om1)
    (hg : (hlVTU hSt hS).g c < σ) : A.γN < σ := by
  obtain ⟨n, hn1, hn⟩ := hlVT_cof hSt hS hc
  obtain ⟨-, hN1, hcNc⟩ := hlVTN_spec hn1 hn
  have hgN : (hlVTU hSt hS).g c = (hlVU St A S0 (hlVTN St A S0 c)).g c := rfl
  have I := hlV_inv hSt hS _ hN1
  rcases zero_or_succ_or_isSuccLimit (hlVTN St A S0 c) with h0 | ⟨m, hm⟩ | hlim
  · rw [h0, hlVU_zero] at hcNc
    exact absurd hBc (not_le.2 hcNc)
  · have hm' : hlVTN St A S0 c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < hlVTN St A S0 c := by rw [hm']; exact lt_add_one m
    have hml : m < hcN (Λ.L + κ) A.F := hmN.trans hN1
    have hBc' : (hlVU St A S0 m).B ≤ c := not_lt.1 (hlVTN_min hmN hml)
    rw [hgN, hm'] at hg
    rw [hm'] at hcNc I hN1
    have hγ := I.high m (lt_add_one _) c σ hBc' hcNc hσ hσ1 hg
    exact (max_lt_iff.1 ((hlVU_γ_iff hSt hS hN1 hσ hσ1).1 hγ)).1
  · exfalso
    rw [hlVU_B hSt hS hN1] at hcNc
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen (Λ.L + κ)).lt_iff_exists_lt
        (isSuccLimit_add _ hlim)).1 hcNc
    obtain ⟨d, hf, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    have hfl : d < hcN (Λ.L + κ) A.F := hf.trans hN1
    refine hlVTN_min hf hfl ?_
    rw [hlVU_B hSt hS hfl]; exact hct.trans_le ((isNormal_veblen (Λ.L + κ)).monotone htd)

section Union

variable (P : HlWB Λ) (St0 : HlVStTy Λ 0) (h0 : ∀ Q U h, HlVSpec Q U (St0 Q U h)) (S0 : HgVD)
  (hS0 : HlWShape P 0 S0)

include h0 hS0

/-! ## SMALL for the level recursion over `P` -/

/-- **SMALL**: a code of `hlwL κ` with gate below an `ε`-number `σ` lies in some `hlwL μ`, `μ < σ`. -/
theorem hlw_small : ∀ κ, κ < Om1 → ∀ c, c < (hlwL P St0 S0 κ).B → ∀ σ, InE σ → σ < Om1 →
    (hlwL P St0 S0 κ).g c < σ → ∃ μ, μ < σ ∧ c < (hlwL P St0 S0 μ).B := by
  intro κ
  induction κ using WellFoundedLT.induction with
  | ind κ IH =>
  intro hκ c hc σ hσ hσ1 hg
  by_cases hκσ : κ < σ
  · exact ⟨κ, hκσ, hc⟩
  have hI := hlwL_inv P St0 h0 S0 hS0
  rcases zero_or_succ_or_isSuccLimit κ with h0' | ⟨μ, hμ⟩ | hlim
  · exact absurd (by rw [h0']; exact hσ.pos) hκσ
  · have hμ' : κ = μ + 1 := by rw [← hμ, succ_eq_add_one]
    subst hμ'
    have hμ1 : μ < Om1 := (lt_add_one μ).trans hκ
    by_cases hcμ : c < (hlwL P St0 S0 μ).B
    · have e := ((hI (μ + 1) hκ).2 μ (le_add_right le_rfl) c 0 hcμ).2
      rw [e] at hg
      exact IH μ (lt_add_one μ) hμ1 c hcμ σ hσ hσ1 hg
    · exfalso
      have hsh := hlw_ok_shape P hκ (hI μ hμ1).1
      rw [hlwL_succ, hlwSt_eq P St0 h0 hκ hsh] at hc hg
      have h := hlw_highN _ _ hc (not_lt.1 hcμ) hσ hσ1 hg
      exact hκσ (max_lt_iff.1 h).2
  · have hcoh : HlWCoh P κ (fun κ' _ => hlwL P St0 S0 κ') :=
      ⟨fun κ' h => (hI κ' (h.trans hκ)).1, fun κ₁ κ₂ h₁ h₂ h12 c x hc =>
        (hI κ₂ (h₂.trans hκ)).2 κ₁ h12 c x hc⟩
    have eU : hlwChU P S0 κ hlim (fun κ' _ => hlwL P St0 S0 κ') =
        (hlwCh P κ hlim hκ (fun κ' _ => hlwL P St0 S0 κ') hcoh).U := by
      unfold hlwChU; rw [dif_pos ⟨hκ, hcoh⟩]
    have hsh := hlwCh_shape P κ hlim hκ (fun κ' _ => hlwL P St0 S0 κ') hcoh
    by_cases hcS : c < veblen (Λ.L + κ) (P.F + 1)
    · obtain ⟨b, hb, hcb⟩ := hgVeb_cof (hlv_L0 Λ κ) (P.wfix (hlw_Lk hκ)) hcS
      obtain ⟨κ'', hκ'', hbκ⟩ := (lt_add_iff hlim.bot_lt.ne').1 hb
      have hκ''1 : κ'' < Om1 := hκ''.trans hκ
      have hcν : c < (hlwL P St0 S0 κ'').B := by
        rw [(hI κ'' hκ''1).1.1]; exact hcb.trans_le (hcN_mono hbκ _)
      have e2 := ((hI κ hκ).2 κ'' hκ''.le c 0 hcν).2
      rw [e2] at hg
      exact IH κ'' hκ'' hκ''1 c hcν σ hσ hσ1 hg
    · exfalso
      rw [hlwL_limit P St0 S0 hlim, eU, hlwSt_eq P St0 h0 hκ hsh] at hc hg
      have h := hlw_highN _ _ hc (by rw [hsh.1]; exact not_lt.1 hcS) hσ hσ1 hg
      exact hκσ (max_lt_iff.1 h).2

/-! ## The union -/

theorem hlwB_gt {κ : Ordinal.{0}} (hκ : κ < Om1) : (hlwL P St0 S0 κ).B < hdNx (Λ.L + Om1) P.F := by
  rw [((hlwL_inv P St0 h0 S0 hS0) κ hκ).1.1]; exact hlw_N_lt_S P hκ

theorem hlwB_cof {c : Ordinal.{0}} (hc : c < hdNx (Λ.L + Om1) P.F) :
    ∃ κ, κ < Om1 ∧ c < (hlwL P St0 S0 κ).B := by
  obtain ⟨b, hb, hcb⟩ := hjw_Nx_cof (hlv_L0 Λ Om1) P.F_P hc
  obtain ⟨κ, hκ, hbκ⟩ := (lt_add_iff gv_Om1_pos.ne').1 hb
  exact ⟨κ, hκ, by rw [((hlwL_inv P St0 h0 S0 hS0) κ hκ).1.1]; exact hcb.trans_le (hcN_mono hbκ _)⟩

omit h0 hS0 in
theorem hlw_B_E : InE (hdNx (Λ.L + Om1) P.F) := hdNx_E (hlv_L0 Λ Om1) _

omit h0 hS0 in
theorem hlw_B_lim : IsSuccLimit (hdNx (Λ.L + Om1) P.F) := ev_isSuccLimit_of_inE (hlw_B_E P)

omit h0 hS0 in
/-- The first level containing `c`. -/
noncomputable def hlwN (c : Ordinal.{0}) : Ordinal.{0} := sInf {κ | κ < Om1 ∧ c < (hlwL P St0 S0 κ).B}

omit h0 hS0 in
theorem hlwN_spec {c κ : Ordinal.{0}} (hκ : κ < Om1) (hc : c < (hlwL P St0 S0 κ).B) :
    hlwN P St0 S0 c ≤ κ ∧ hlwN P St0 S0 c < Om1 ∧ c < (hlwL P St0 S0 (hlwN P St0 S0 c)).B := by
  have hne : ({κ | κ < Om1 ∧ c < (hlwL P St0 S0 κ).B} : Set Ordinal.{0}).Nonempty := ⟨κ, hκ, hc⟩
  have hm := csInf_mem hne
  exact ⟨csInf_le' ⟨hκ, hc⟩, hm.1, hm.2⟩

theorem hlwN_high {c : Ordinal.{0}} (hc : hdNx (Λ.L + Om1) P.F ≤ c) : hlwN P St0 S0 c = 0 := by
  unfold hlwN
  have he : ({κ | κ < Om1 ∧ c < (hlwL P St0 S0 κ).B} : Set Ordinal.{0}) = ∅ := by
    ext κ
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hκ hcκ
    exact absurd (hcκ.trans (hlwB_gt P St0 h0 S0 hS0 hκ)) (not_lt.2 hc)
  rw [he]; exact Ordinal.sInf_empty

theorem hlw_R_eq {c κ : Ordinal.{0}} (hκ : κ < Om1) (hc : c < (hlwL P St0 S0 κ).B) (x : Ordinal.{0}) :
    (hlwL P St0 S0 (hlwN P St0 S0 c)).R c x = (hlwL P St0 S0 κ).R c x := by
  obtain ⟨h1, -, h3⟩ := hlwN_spec P St0 S0 hκ hc
  exact (((hlwL_inv P St0 h0 S0 hS0) κ hκ).2 _ h1 c x h3).1.symm

theorem hlw_g_eq {c κ : Ordinal.{0}} (hκ : κ < Om1) (hc : c < (hlwL P St0 S0 κ).B) :
    (hlwL P St0 S0 (hlwN P St0 S0 c)).g c = (hlwL P St0 S0 κ).g c := by
  obtain ⟨h1, -, h3⟩ := hlwN_spec P St0 S0 hκ hc
  exact (((hlwL_inv P St0 h0 S0 hS0) κ hκ).2 _ h1 c 0 h3).2.symm

theorem hlw_R_succ (c x : Ordinal.{0}) :
    (hlwL P St0 S0 (hlwN P St0 S0 (c + 1))).R (c + 1) x = (hlwL P St0 S0 (hlwN P St0 S0 c)).R c x + 1 := by
  rcases lt_or_ge c (hdNx (Λ.L + Om1) P.F) with h | h
  · obtain ⟨n, hn1, hn⟩ := hlwB_cof P St0 h0 S0 hS0 ((hlw_B_lim P).add_one_lt h)
    rw [hlw_R_eq P St0 h0 S0 hS0 hn1 hn, hlw_R_eq P St0 h0 S0 hS0 hn1 ((lt_add_one c).trans hn),
      (hlwL P St0 S0 n).R_succ]
  · rw [hlwN_high P St0 h0 S0 hS0 h, hlwN_high P St0 h0 S0 hS0 (h.trans (le_self_add (a := c) (b := 1))),
      (hlwL P St0 S0 0).R_succ]

theorem hlw_g_le_succ (c : Ordinal.{0}) :
    (hlwL P St0 S0 (hlwN P St0 S0 c)).g c ≤ (hlwL P St0 S0 (hlwN P St0 S0 (c + 1))).g (c + 1) := by
  rcases lt_or_ge c (hdNx (Λ.L + Om1) P.F) with h | h
  · obtain ⟨n, hn1, hn⟩ := hlwB_cof P St0 h0 S0 hS0 ((hlw_B_lim P).add_one_lt h)
    rw [hlw_g_eq P St0 h0 S0 hS0 hn1 hn, hlw_g_eq P St0 h0 S0 hS0 hn1 ((lt_add_one c).trans hn)]
    exact (hlwL P St0 S0 n).g_le_succ c
  · rw [hlwN_high P St0 h0 S0 hS0 h, hlwN_high P St0 h0 S0 hS0 (h.trans (le_self_add (a := c) (b := 1)))]
    exact (hlwL P St0 S0 0).g_le_succ c

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : P.γR < x)
include hx hx1 hγ

/-- **The bound field of every `hlwL κ` lies below `hdNx (ℓ(x)+x) (F(x))`** (`γ < x`). -/
theorem hlw_Z_le {κ : Ordinal.{0}} (hκ : κ < Om1) : (hlwL P St0 S0 κ).Z x ≤ hdNx (Λ.l x + x) (P.Fr x) := by
  rw [((hlwL_inv P St0 h0 S0 hS0) κ hκ).1.2.2.2.1 x hx hx1]
  split_ifs with h
  · exact (hb_evZ_lt_fix2 (hdNx_fix (lt_of_lt_of_le (show (2 : Ordinal.{0}) < ω from by
        exact_mod_cast natCast_lt_omega0 2) (hlv_ωl Λ hx hx1).le) _)
      (hlw_rN_lt_S P hx (max_lt_iff.1 h).2)).le
  · rw [P.hlwZo_eq hx hγ]

/-- **The base reading of `hlwL κ` lies below `hdNx (ℓ(x)+x) (F(x))`** (`κ < x`). -/
theorem hlw_b_lt {κ : Ordinal.{0}} (hκ : κ < x) : (hlwL P St0 S0 κ).b x < hdNx (Λ.l x + x) (P.Fr x) := by
  rw [((hlwL_inv P St0 h0 S0 hS0) κ (hκ.trans hx1)).1.2.2.1 x hx hx1 (max_lt hγ hκ)]
  exact hlw_rN_lt_S P hx hκ

end Base

omit h0 hS0 in
theorem hlw_b_fix1 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    veblen 1 (hdNx (Λ.l x + x) (P.Fr x)) = hdNx (Λ.l x + x) (P.Fr x) :=
  hdNx_fix (one_lt_omega0.trans (hlv_ωl Λ hx hx1)) _

omit h0 hS0 in
theorem hlw_x_lt_b {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : P.γR < x) :
    x < hdNx (Λ.l x + x) (P.Fr x) := (P.Fr_gtx hx hx1 hγ).trans (hdNx_gt _ _)

/-- **A code of the union with gate below an `ε`-number `σ` lies in `hlwL μ`, `μ < σ`.** -/
theorem hlw_small' {c σ : Ordinal.{0}} (hc : c < hdNx (Λ.L + Om1) P.F) (hσ : InE σ) (hσ1 : σ < Om1)
    (hg : (hlwL P St0 S0 (hlwN P St0 S0 c)).g c < σ) : ∃ μ, μ < σ ∧ c < (hlwL P St0 S0 μ).B := by
  obtain ⟨n, hn1, hn⟩ := hlwB_cof P St0 h0 S0 hS0 hc
  rw [hlw_g_eq P St0 h0 S0 hS0 hn1 hn] at hg
  exact hlw_small P St0 h0 S0 hS0 n hn1 c hn σ hσ hσ1 hg

theorem hlw_γ_lt {μ x : Ordinal.{0}} (hγ : P.γR < x) (hμ : μ < x) (hμ1 : μ < Om1) : (hlwL P St0 S0 μ).γ < x := by
  rw [((hlwL_inv P St0 h0 S0 hS0) μ hμ1).1.2.1]; exact max_lt hγ hμ

omit h0 hS0 in
open Classical in
/-- The bound field of the union. -/
noncomputable def hlwUZ (x : Ordinal.{0}) : Ordinal.{0} :=
  if P.γR < x then evZ (hdNx (Λ.l x + x) (P.Fr x)) else P.Zo x

/-- **THE UNION OVER ALL LEVELS `L + κ`, `κ < Ω₁`, OVER `P`**: a gated digit system (`HgVD`) with the bound
`hdNx (L+Ω₁) F`, the base gate `γ`, the base reading `hdNx (ℓ(x)+x) (F(x))` (the level `L + Ω₁` read as `ℓ(x)+x`). -/
noncomputable def hlwU : HgVD where
  B := hdNx (Λ.L + Om1) P.F
  γ := P.γR
  γ_lt := P.γR_lt
  γ_cl := fun Z hZ hZ1 h => P.γR_cl Z hZ hZ1 (P.S_cl Z hZ hZ1 h) (hlw_S_g P hZ hZ1 h)
  γ_G := fun h => absurd h (P.G_le.trans_lt (hdNx_gt _ _)).ne'
  R := fun c x => (hlwL P St0 S0 (hlwN P St0 S0 c)).R c x
  g := fun c => (hlwL P St0 S0 (hlwN P St0 S0 c)).g c
  b := fun x => hdNx (Λ.l x + x) (P.Fr x)
  ba := fun x => hdNx (Λ.l x + x) (P.Fr x)
  ix := hdNx (Λ.L + Om1) P.F
  Z := hlwUZ P
  B_E := hlw_B_E P
  G_le := P.G_le.trans (hdNx_gt _ _).le
  B_lt1 := P.S_lt1
  B_ix := (hdNx_fix ((hg_one_lt_Om1.trans_le Λ.OL).trans_le le_self_add) _).symm
  Z_fix := fun x _ _ => by
    unfold hlwUZ; split_ifs
    · exact epsilon_evZ _
    · exact hc_fix_down one_le_two (P.Zo_fix x)
  Z_G1 := fun x hx hx1 => by
    unfold hlwUZ; split_ifs with h
    · exact gw_evZ_lt1 hx hx1 (P.wS_lt1x hx hx1 h)
    · exact P.Zo_G1 x hx hx1
  ix_mem := fun S a b ha hb => P.S_mem S ha hb
  g_lt := fun c hc => by
    obtain ⟨n, hn1, hn⟩ := hlwB_cof P St0 h0 S0 hS0 hc
    show (hlwL P St0 S0 (hlwN P St0 S0 c)).g c < Om1
    rw [hlw_g_eq P St0 h0 S0 hS0 hn1 hn]; exact (hlwL P St0 S0 n).g_lt c hn
  g_zero := by
    show (hlwL P St0 S0 (hlwN P St0 S0 0)).g 0 = 0
    rw [hlw_g_eq P St0 h0 S0 hS0 gv_Om1_pos (hlwL P St0 S0 0).B_pos]; exact (hlwL P St0 S0 0).g_zero
  g_nat := fun k => by
    show (hlwL P St0 S0 (hlwN P St0 S0 k)).g k < ω
    rw [hlw_g_eq P St0 h0 S0 hS0 gv_Om1_pos ((hlwL P St0 S0 0).nat_lt_B k)]; exact (hlwL P St0 S0 0).g_nat k
  g_E := by
    show (hlwL P St0 S0 (hlwN P St0 S0 gfE)).g gfE = 0
    rw [hlw_g_eq P St0 h0 S0 hS0 gv_Om1_pos (hlwL P St0 S0 0).E_lt_B]; exact (hlwL P St0 S0 0).g_E
  g_lowE := fun c hc => by
    show (hlwL P St0 S0 (hlwN P St0 S0 c)).g c = gtc c
    rw [hlw_g_eq P St0 h0 S0 hS0 gv_Om1_pos (hc.trans (hlwL P St0 S0 0).E_lt_B)]
    exact (hlwL P St0 S0 0).g_lowE c hc
  g_G0 := fun h => by
    obtain ⟨n, hn1, hn⟩ := hlwB_cof P St0 h0 S0 hS0 h
    show (hlwL P St0 S0 (hlwN P St0 S0 (gcG 0))).g (gcG 0) = 0
    rw [hlw_g_eq P St0 h0 S0 hS0 hn1 hn]; exact (hlwL P St0 S0 n).g_G0 hn
  g_add := fun Z hZ hωZ x y hxy hgx hgy => by
    obtain ⟨n, hn1, hn⟩ := hlwB_cof P St0 h0 S0 hS0 hxy
    have hx : x < (hlwL P St0 S0 n).B := lt_of_le_of_lt le_self_add hn
    have hy : y < (hlwL P St0 S0 n).B := lt_of_le_of_lt le_add_self hn
    show (hlwL P St0 S0 (hlwN P St0 S0 (x + y))).g (x + y) < Z
    have hgx' : (hlwL P St0 S0 (hlwN P St0 S0 x)).g x < Z := hgx
    have hgy' : (hlwL P St0 S0 (hlwN P St0 S0 y)).g y < Z := hgy
    rw [hlw_g_eq P St0 h0 S0 hS0 hn1 hn]; rw [hlw_g_eq P St0 h0 S0 hS0 hn1 hx] at hgx'
    rw [hlw_g_eq P St0 h0 S0 hS0 hn1 hy] at hgy'
    exact (hlwL P St0 S0 n).g_add Z hZ hωZ x y hn hgx' hgy'
  g_opow := fun Z hZw hωZ y hy hg => by
    obtain ⟨n, hn1, hn⟩ := hlwB_cof P St0 h0 S0 hS0 hy
    have hy' : y < (hlwL P St0 S0 n).B := lt_of_le_of_lt (right_le_opow y one_lt_omega0) hn
    show (hlwL P St0 S0 (hlwN P St0 S0 (ω ^ y))).g (ω ^ y) < Z
    have hg' : (hlwL P St0 S0 (hlwN P St0 S0 y)).g y < Z := hg
    rw [hlw_g_eq P St0 h0 S0 hS0 hn1 hn]; rw [hlw_g_eq P St0 h0 S0 hS0 hn1 hy'] at hg'
    exact (hlwL P St0 S0 n).g_opow Z hZw hωZ y hn hg'
  code_gate := fun Z hZ1 hZ0 hZa hZp At hAt c hc hcB => by
    obtain ⟨n, hn1, hn⟩ := hlwB_cof P St0 h0 S0 hS0 hcB
    show (hlwL P St0 S0 (hlwN P St0 S0 c)).g c < Z
    rw [hlw_g_eq P St0 h0 S0 hS0 hn1 hn]
    exact (hlwL P St0 S0 n).code_gate Z hZ1 hZ0 hZa hZp At (fun s hs => (hAt s hs).imp_right
      (fun h => (hlwB_gt P St0 h0 S0 hS0 hn1).le.trans h)) c hc hn
  g_succ := fun Z hZ c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hlwB_cof P St0 h0 S0 hS0 hc
    have hc' : c < (hlwL P St0 S0 n).B := (lt_add_one c).trans hn
    show (hlwL P St0 S0 (hlwN P St0 S0 (c + 1))).g (c + 1) < Z
    have hg' : (hlwL P St0 S0 (hlwN P St0 S0 c)).g c < Z := hg
    rw [hlw_g_eq P St0 h0 S0 hS0 hn1 hn]; rw [hlw_g_eq P St0 h0 S0 hS0 hn1 hc'] at hg'
    exact (hlwL P St0 S0 n).g_succ Z hZ c hn hg'
  g_le_succ := hlw_g_le_succ P St0 h0 S0 hS0
  mem := fun S a b ha c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hlwB_cof P St0 h0 S0 hS0 hc
    have hg' : (hlwL P St0 S0 (hlwN P St0 S0 c)).g c < b := hg
    rw [hlw_g_eq P St0 h0 S0 hS0 hn1 hn] at hg'
    exact (hlwL P St0 S0 n).mem S a b ha c hn hg'
  R_zero := fun x => by
    show (hlwL P St0 S0 (hlwN P St0 S0 0)).R 0 x = 0
    rw [hlw_R_eq P St0 h0 S0 hS0 gv_Om1_pos (hlwL P St0 S0 0).B_pos]; exact (hlwL P St0 S0 0).R_zero x
  R_nat := fun k x => by
    show (hlwL P St0 S0 (hlwN P St0 S0 k)).R k x = k
    rw [hlw_R_eq P St0 h0 S0 hS0 gv_Om1_pos ((hlwL P St0 S0 0).nat_lt_B k)]; exact (hlwL P St0 S0 0).R_nat k x
  R_E := fun x => by
    show (hlwL P St0 S0 (hlwN P St0 S0 gfE)).R gfE x = eN x
    rw [hlw_R_eq P St0 h0 S0 hS0 gv_Om1_pos (hlwL P St0 S0 0).E_lt_B]; exact (hlwL P St0 S0 0).R_E x
  R_succ := hlw_R_succ P St0 h0 S0 hS0
  R_pos := fun x hx hx1 c hc0 hc hg => by
    obtain ⟨n, hn1, hn⟩ := hlwB_cof P St0 h0 S0 hS0 hc
    show 0 < (hlwL P St0 S0 (hlwN P St0 S0 c)).R c x
    have hg' : (hlwL P St0 S0 (hlwN P St0 S0 c)).g c < x := hg
    rw [hlw_R_eq P St0 h0 S0 hS0 hn1 hn]; rw [hlw_g_eq P St0 h0 S0 hS0 hn1 hn] at hg'
    exact (hlwL P St0 S0 n).R_pos x hx hx1 c hc0 hn hg'
  R_omega := fun x hx hx1 c hω hc hg => by
    obtain ⟨n, hn1, hn⟩ := hlwB_cof P St0 h0 S0 hS0 hc
    show ω ≤ (hlwL P St0 S0 (hlwN P St0 S0 c)).R c x
    have hg' : (hlwL P St0 S0 (hlwN P St0 S0 c)).g c < x := hg
    rw [hlw_R_eq P St0 h0 S0 hS0 hn1 hn]; rw [hlw_g_eq P St0 h0 S0 hS0 hn1 hn] at hg'
    exact (hlwL P St0 S0 n).R_omega x hx hx1 c hω hn hg'
  R_lt_b := fun x hx hx1 hγ c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hlwB_cof P St0 h0 S0 hS0 hc
    show (hlwL P St0 S0 (hlwN P St0 S0 c)).R c x < hdNx (Λ.l x + x) (P.Fr x)
    have hg' : (hlwL P St0 S0 (hlwN P St0 S0 c)).g c < x := hg
    rw [hlw_R_eq P St0 h0 S0 hS0 hn1 hn]; rw [hlw_g_eq P St0 h0 S0 hS0 hn1 hn] at hg'
    exact ((hlwL P St0 S0 n).R_lt_Z x hx hx1 c hn hg').trans_le (hlw_Z_le P St0 h0 S0 hS0 hx hx1 hγ hn1)
  R_lt_Z := fun x hx hx1 c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hlwB_cof P St0 h0 S0 hS0 hc
    show (hlwL P St0 S0 (hlwN P St0 S0 c)).R c x < hlwUZ P x
    have hg' : (hlwL P St0 S0 (hlwN P St0 S0 c)).g c < x := hg
    rw [hlw_R_eq P St0 h0 S0 hS0 hn1 hn]; rw [hlw_g_eq P St0 h0 S0 hS0 hn1 hn] at hg'
    have h1 := (hlwL P St0 S0 n).R_lt_Z x hx hx1 c hn hg'
    unfold hlwUZ
    split_ifs with hγ
    · exact (h1.trans_le (hlw_Z_le P St0 h0 S0 hS0 hx hx1 hγ hn1)).trans (lt_evZ _)
    · rw [((hlwL_inv P St0 h0 S0 hS0) n hn1).1.2.2.2.1 x hx hx1,
        if_neg (fun h => hγ (max_lt_iff.1 h).1), P.hlwZo_low hγ] at h1
      exact h1
  mono := fun x hx hx1 c hc d hdc hgc hgd => by
    obtain ⟨n, hn1, hn⟩ := hlwB_cof P St0 h0 S0 hS0 hc
    have hd : d < (hlwL P St0 S0 n).B := hdc.trans hn
    show (hlwL P St0 S0 (hlwN P St0 S0 d)).R d x < (hlwL P St0 S0 (hlwN P St0 S0 c)).R c x
    have hgc' : (hlwL P St0 S0 (hlwN P St0 S0 c)).g c < x := hgc
    have hgd' : (hlwL P St0 S0 (hlwN P St0 S0 d)).g d < x := hgd
    rw [hlw_R_eq P St0 h0 S0 hS0 hn1 hn, hlw_R_eq P St0 h0 S0 hS0 hn1 hd]
    rw [hlw_g_eq P St0 h0 S0 hS0 hn1 hn] at hgc'; rw [hlw_g_eq P St0 h0 S0 hS0 hn1 hd] at hgd'
    exact (hlwL P St0 S0 n).mono x hx hx1 c hn d hdc hgc' hgd'
  cof := fun x hx hx1 c hc hg ν hν => by
    obtain ⟨n, hn1, hn⟩ := hlwB_cof P St0 h0 S0 hS0 hc
    have hg' : (hlwL P St0 S0 (hlwN P St0 S0 c)).g c < x := hg
    have hν' : ν < (hlwL P St0 S0 (hlwN P St0 S0 c)).R c x := hν
    rw [hlw_R_eq P St0 h0 S0 hS0 hn1 hn] at hν'; rw [hlw_g_eq P St0 h0 S0 hS0 hn1 hn] at hg'
    obtain ⟨d, hdc, hgd, hνd⟩ := (hlwL P St0 S0 n).cof x hx hx1 c hn hg' ν hν'
    have hd : d < (hlwL P St0 S0 n).B := hdc.trans hn
    exact ⟨d, hdc, by
      show (hlwL P St0 S0 (hlwN P St0 S0 d)).g d < x; rw [hlw_g_eq P St0 h0 S0 hS0 hn1 hd]; exact hgd,
      by show ν ≤ (hlwL P St0 S0 (hlwN P St0 S0 d)).R d x; rw [hlw_R_eq P St0 h0 S0 hS0 hn1 hd]; exact hνd⟩
  b_cof := fun x hx hx1 hγ ν hν => by
    obtain ⟨b, hb, hνb⟩ := hjw_Nx_cof (omega0_pos.trans (hlv_ωl Λ hx hx1 (ν := x))).ne' (P.Fr_P hx hx1 hγ) hν
    obtain ⟨κ, hκ, hbκ⟩ := (lt_add_iff hx.pos.ne').1 hb
    have hκ1 : κ < Om1 := hκ.trans hx1
    have hνb' : ν < (hlwL P St0 S0 κ).b x := by
      rw [((hlwL_inv P St0 h0 S0 hS0) κ hκ1).1.2.2.1 x hx hx1 (max_lt hγ hκ)]
      exact hνb.trans_le (hcN_mono hbκ _)
    obtain ⟨d, hd, hgd, hνd⟩ := (hlwL P St0 S0 κ).b_cof x hx hx1 (hlw_γ_lt P St0 h0 S0 hS0 hγ hκ hκ1) ν hνb'
    exact ⟨d, hd.trans (hlwB_gt P St0 h0 S0 hS0 hκ1), by
      show (hlwL P St0 S0 (hlwN P St0 S0 d)).g d < x; rw [hlw_g_eq P St0 h0 S0 hS0 hκ1 hd]; exact hgd,
      by show ν < (hlwL P St0 S0 (hlwN P St0 S0 d)).R d x; rw [hlw_R_eq P St0 h0 S0 hS0 hκ1 hd]; exact hνd⟩
  b_E := fun x hx hx1 _ => hdNx_E (omega0_pos.trans (hlv_ωl Λ hx hx1 (ν := x))).ne' _
  x_lt_b := fun x hx hx1 hγ => hlw_x_lt_b P hx hx1 hγ
  b_eN := fun x hx hx1 hγ => gz_eN_fix hx hx1 (hlw_b_fix1 P hx hx1) (hlw_x_lt_b P hx hx1 hγ) (P.wS_lt1x hx hx1 hγ)
  ba_lt := fun x hx hx1 hγ => P.wS_lt1x hx hx1 hγ
  b_Z := fun x _ _ hγ => by unfold hlwUZ; rw [if_pos hγ]; exact go_eN_lt_evZ (lt_evZ _)
  b_pi := fun _ _ hB hγ => P.S_pi hB hγ
  ba_pi := fun _ _ hB hγ => P.S_pi hB hγ
  ex := fun σ ρ hB c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hlwB_cof P St0 h0 S0 hS0 hc
    show (hlwL P St0 S0 (hlwN P St0 S0 c)).R c ρ ∈ TB ρ σ ∧
      pi σ ρ ((hlwL P St0 S0 (hlwN P St0 S0 c)).R c ρ) = (hlwL P St0 S0 (hlwN P St0 S0 c)).R c σ
    have hg' : (hlwL P St0 S0 (hlwN P St0 S0 c)).g c < σ := hg
    rw [hlw_R_eq P St0 h0 S0 hS0 hn1 hn, hlw_R_eq P St0 h0 S0 hS0 hn1 hn]
    rw [hlw_g_eq P St0 h0 S0 hS0 hn1 hn] at hg'
    exact (hlwL P St0 S0 n).ex σ ρ hB c hn hg'
  dig := fun σ ρ hB hγ d hd hg P' P'' hat => by
    have hσ1 : σ < Om1 := hB.2.2.1.trans hB.2.2.2
    obtain ⟨μ, hμσ, hdμ⟩ := hlw_small' P St0 h0 S0 hS0 hd hB.1 hσ1 hg
    have hμ1 : μ < Om1 := hμσ.trans hσ1
    show ω ^ P' * (hlwL P St0 S0 (hlwN P St0 S0 d)).R d ρ ∈ TB ρ σ ∧
      pi σ ρ (ω ^ P' * (hlwL P St0 S0 (hlwN P St0 S0 d)).R d ρ) =
        ω ^ P'' * (hlwL P St0 S0 (hlwN P St0 S0 d)).R d σ
    have hg' : (hlwL P St0 S0 (hlwN P St0 S0 d)).g d < σ := hg
    rw [hlw_R_eq P St0 h0 S0 hS0 hμ1 hdμ, hlw_R_eq P St0 h0 S0 hS0 hμ1 hdμ]
    rw [hlw_g_eq P St0 h0 S0 hS0 hμ1 hdμ] at hg'
    exact (hlwL P St0 S0 μ).dig σ ρ hB (hlw_γ_lt P St0 h0 S0 hS0 hγ hμσ hμ1) d hdμ hg' P' P'' (fun β hβ hβe =>
      hat β hβ (hβe.trans (hlw_b_lt P St0 h0 S0 hS0 hB.2.1 hB.2.2.2 (hγ.trans hB.2.2.1)
        (hμσ.trans hB.2.2.1))))
  ld := fun c hl hc => by
    obtain ⟨n, hn1, hn⟩ := hlwB_cof P St0 h0 S0 hS0 hc
    obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := (hlwL P St0 S0 n).ld c hl hn
    have hcpn : cp < (hlwL P St0 S0 n).B := hcp.trans hn
    refine ⟨cp, lp, T, hcp, ?_, fun x hx hx1 hg => ?_, fun σ ρ hB hg => hex σ ρ hB ?_⟩
    · show (hlwL P St0 S0 (hlwN P St0 S0 cp)).g cp ≤ (hlwL P St0 S0 (hlwN P St0 S0 c)).g c
      rw [hlw_g_eq P St0 h0 S0 hS0 hn1 hn, hlw_g_eq P St0 h0 S0 hS0 hn1 hcpn]; exact hgcp
    · have hg' : (hlwL P St0 S0 n).g c < x := by rw [← hlw_g_eq P St0 h0 S0 hS0 hn1 hn]; exact hg
      show (hlwL P St0 S0 (hlwN P St0 S0 c)).R c x = _ ∧ _
      rw [hlw_R_eq P St0 h0 S0 hS0 hn1 hn, hlw_R_eq P St0 h0 S0 hS0 hn1 hcpn]
      exact hdec x hx hx1 hg'
    · rw [← hlw_g_eq P St0 h0 S0 hS0 hn1 hn]; exact hg

theorem hlwU_B : (hlwU P St0 h0 S0 hS0).B = hdNx (Λ.L + Om1) P.F := rfl

theorem hlwU_γ : (hlwU P St0 h0 S0 hS0).γ = P.γR := rfl

theorem hlwU_b (x : Ordinal.{0}) : (hlwU P St0 h0 S0 hS0).b x = hdNx (Λ.l x + x) (P.Fr x) := rfl

theorem hlwU_Z (x : Ordinal.{0}) :
    (hlwU P St0 h0 S0 hS0).Z x = if P.γR < x then evZ (hdNx (Λ.l x + x) (P.Fr x)) else P.Zo x := rfl

/-- **The union extends every `hlwL κ`** (readings). -/
theorem hlwU_R {κ c : Ordinal.{0}} (hκ : κ < Om1) (hc : c < (hlwL P St0 S0 κ).B) (x : Ordinal.{0}) :
    (hlwU P St0 h0 S0 hS0).R c x = (hlwL P St0 S0 κ).R c x := hlw_R_eq P St0 h0 S0 hS0 hκ hc x

/-- **The union extends every `hlwL κ`** (gates). -/
theorem hlwU_g {κ c : Ordinal.{0}} (hκ : κ < Om1) (hc : c < (hlwL P St0 S0 κ).B) :
    (hlwU P St0 h0 S0 hS0).g c = (hlwL P St0 S0 κ).g c := hlw_g_eq P St0 h0 S0 hS0 hκ hc

/-- **The union extends its start** (readings and gates). -/
theorem hlwU_R0 {c : Ordinal.{0}} (hc : c < S0.B) (x : Ordinal.{0}) : (hlwU P St0 h0 S0 hS0).R c x = S0.R c x := by
  rw [hlwU_R P St0 h0 S0 hS0 gv_Om1_pos (?_ : c < (hlwL P St0 S0 0).B) x, hlwL_zero]
  · exact (hlwSt_ext P St0 h0 gv_Om1_pos hS0 hc).1 x
  · rw [((hlwL_inv P St0 h0 S0 hS0) 0 gv_Om1_pos).1.1, add_zero]
    refine hc.trans_le ?_
    rw [hS0.1, add_zero, ← hdNx_fixP (P.wfix ((lt_add_iff_pos_right _).2 gv_Om1_pos))]
    exact (hdNx_lt_N (hcN_gt _ _)).le

theorem hlwU_g0 {c : Ordinal.{0}} (hc : c < S0.B) : (hlwU P St0 h0 S0 hS0).g c = S0.g c := by
  rw [hlwU_g P St0 h0 S0 hS0 gv_Om1_pos (?_ : c < (hlwL P St0 S0 0).B), hlwL_zero]
  · exact (hlwSt_ext P St0 h0 gv_Om1_pos hS0 hc).2
  · rw [((hlwL_inv P St0 h0 S0 hS0) 0 gv_Om1_pos).1.1, add_zero]
    refine hc.trans_le ?_
    rw [hS0.1, add_zero, ← hdNx_fixP (P.wfix ((lt_add_iff_pos_right _).2 gv_Om1_pos))]
    exact (hdNx_lt_N (hcN_gt _ _)).le

/-- **A code `c ∈ [F, hdNx (L+Ω₁) F)` of the union with gate below an `ε`-number `σ` forces `γ < σ`.** -/
theorem hlwU_high {c σ : Ordinal.{0}} (hFc : P.F ≤ c) (hc : c < hdNx (Λ.L + Om1) P.F) (hσ : InE σ)
    (hσ1 : σ < Om1) (hg : (hlwU P St0 h0 S0 hS0).g c < σ) : P.γ < σ := by
  obtain ⟨n, hn1, hn⟩ := hlwB_cof P St0 h0 S0 hS0 hc
  rw [hlwU_g P St0 h0 S0 hS0 hn1 hn] at hg
  exact ((hlwL_inv P St0 h0 S0 hS0) n hn1).1.2.2.2.2 c σ hFc hn hσ hσ1 hg

end Union

end Googology.Trans.PoR.InaccPsi.R2.Hl

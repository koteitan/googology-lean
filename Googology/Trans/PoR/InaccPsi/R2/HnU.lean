import Googology.Trans.PoR.InaccPsi.R2.HnG

/-!
# HnU: THE LEVEL `Ω₁·Ω₁·2` READ AS `x·x·2`: THE UNION OF ALL `hnkGS μ`, `μ < Ω₁`

PORT of `Hl.HlU` to the band levels: the systems `hnkGS μ` (bound `φ(Ω₁·Ω₁ + Ω₁·μ, G+1)`, base gate `≤ μ`) for every
`μ < Ω₁` have a union, a gated digit system with the bound `φ(Ω₁·Ω₁·2, G+1)` (written `φ(Ω₁·Ω₁ + Ω₁·Ω₁, G+1)`), the
base gate `0` and the base reading `φ(x·x + x·x, Γ_{x+1}+1)`; Lemma EXACT for `ρ·ρ + ρ·ρ` is `Exact.pi_sq` twice
with `Exact.pi_add`.  What differs from `Hl.HlU`: the members (`hnkGS μ`), their bounds, the cofinality of
`Ω₁·Ω₁ + Ω₁·μ` in `Ω₁·Ω₁·2` (`hnkGS_Bcof`), the base reading, SMALL via `hnkPk_g_lt`; the lemmas of the section `High`
(`hnw_highR`, `hnwU_highR`) are the ports of `Hl.hlw_highR`, `Hl.hlwU_highR` to `Hn.HnWB`.

* `hnw_highR`, `hnwU_highR`, `hnkGS_Bcof`, `hnk_small` (**SMALL**);
* `hnB` (`φ(Ω₁·Ω₁ + Ω₁·Ω₁, G+1)`), `hnBR`, `hn_BR_pi` (**EXACT for it**), `hnU` (**THE UNION OVER ALL BAND LEVELS**);
* `hnU_loc` (**`φ(Ω₁·Ω₁·2, G+1)` IS LOCATED**), `hnU_blk`, `hnU_enum`, `hnU_capV`, `hnU_road`, `hnU_fr_order`,
  `hnU_hyp_iff`.

No new axiom.  New definitions: `hnB`, `hnN`, `hnBR`, `hnU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hn

open Googology.Trans.PoR.InaccPsi.R2.Hl
open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk
open Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The reading gate past the start of the union over a base -/

section High

variable {Λ : HnLv} (P : HnWB Λ) (St0 : HnVStTy Λ 0) (h0 : ∀ Q U h, HnVSpec Q U (St0 Q U h)) (S0 : HgVD)
  (hS0 : HnWShape P 0 S0)

include h0 hS0

/-- **The codes of `hnwL κ` past the start `S0` have a gate `≥` the reading gate `γR` of `P`.** -/
theorem hnw_highR : ∀ κ, κ < Om1 → ∀ c, S0.B ≤ c → c < (hnwL P St0 S0 κ).B → ∀ σ, InE σ → σ < Om1 →
    (hnwL P St0 S0 κ).g c < σ → P.γR < σ := by
  intro κ
  induction κ using WellFoundedLT.induction with
  | ind κ IH =>
  intro hκ c hSc hc σ hσ hσ1 hg
  have hI := hnwL_inv P St0 h0 S0 hS0
  rcases zero_or_succ_or_isSuccLimit κ with h0' | ⟨μ, hμ⟩ | hlim
  · subst h0'
    rw [hnwL_zero, hnwSt_eq P St0 h0 hκ hS0] at hc hg
    exact (max_lt_iff.1 (hnw_highN _ _ hc hSc hσ hσ1 hg)).1
  · have hμ' : κ = μ + 1 := by rw [← hμ, succ_eq_add_one]
    subst hμ'
    have hμ1 : μ < Om1 := (lt_add_one μ).trans hκ
    by_cases hcμ : c < (hnwL P St0 S0 μ).B
    · have e := ((hI (μ + 1) hκ).2 μ (le_add_right le_rfl) c 0 hcμ).2
      rw [e] at hg
      exact IH μ (lt_add_one μ) hμ1 c hSc hcμ σ hσ hσ1 hg
    · have hsh := hnw_ok_shape P hκ (hI μ hμ1).1
      rw [hnwL_succ, hnwSt_eq P St0 h0 hκ hsh] at hc hg
      exact (max_lt_iff.1 (hnw_highN _ _ hc (not_lt.1 hcμ) hσ hσ1 hg)).1
  · have hcoh : HnWCoh P κ (fun κ' _ => hnwL P St0 S0 κ') :=
      ⟨fun κ' h => (hI κ' (h.trans hκ)).1, fun κ₁ κ₂ h₁ h₂ h12 c x hc =>
        (hI κ₂ (h₂.trans hκ)).2 κ₁ h12 c x hc⟩
    have eU : hnwChU P S0 κ hlim (fun κ' _ => hnwL P St0 S0 κ') =
        (hnwCh P κ hlim hκ (fun κ' _ => hnwL P St0 S0 κ') hcoh).U := by
      unfold hnwChU; rw [dif_pos ⟨hκ, hcoh⟩]
    have hsh := hnwCh_shape P κ hlim hκ (fun κ' _ => hnwL P St0 S0 κ') hcoh
    by_cases hcS : c < veblen (Λ.L + κ) (P.F + 1)
    · obtain ⟨b, hb, hcb⟩ := hgVeb_cof (hnv_L0 Λ κ) (P.wfix (hnw_Lk hκ)) hcS
      obtain ⟨κ'', hκ'', hbκ⟩ := (lt_add_iff hlim.bot_lt.ne').1 hb
      have hκ''1 : κ'' < Om1 := hκ''.trans hκ
      have hcν : c < (hnwL P St0 S0 κ'').B := by
        rw [(hI κ'' hκ''1).1.1]; exact hcb.trans_le (hcN_mono hbκ _)
      have e2 := ((hI κ hκ).2 κ'' hκ''.le c 0 hcν).2
      rw [e2] at hg
      exact IH κ'' hκ'' hκ''1 c hSc hcν σ hσ hσ1 hg
    · rw [hnwL_limit P St0 S0 hlim, eU, hnwSt_eq P St0 h0 hκ hsh] at hc hg
      exact (max_lt_iff.1 (hnw_highN _ _ hc (by rw [hsh.1]; exact not_lt.1 hcS) hσ hσ1 hg)).1

/-- **A code of the union over `P` past the start `S0` with gate below an `ε`-number `σ` forces `P.γR < σ`.** -/
theorem hnwU_highR {c σ : Ordinal.{0}} (hSc : S0.B ≤ c) (hc : c < (hnwU P St0 h0 S0 hS0).B) (hσ : InE σ)
    (hσ1 : σ < Om1) (hg : (hnwU P St0 h0 S0 hS0).g c < σ) : P.γR < σ := by
  obtain ⟨n, hn1, hn⟩ := hnwB_cof P St0 h0 S0 hS0 hc
  rw [hnwU_g P St0 h0 S0 hS0 hn1 hn] at hg
  exact hnw_highR P St0 h0 S0 hS0 n hn1 c hSc hn σ hσ hσ1 hg

end High

/-! ## SMALL for the recursion `hnkGS` -/

theorem hnkGS_ext' {μ' μ : Ordinal.{0}} (hμ : μ < Om1) (h : μ' ≤ μ) {c : Ordinal.{0}} (hc : c < (hnkGS μ').B)
    (x : Ordinal.{0}) : (hnkGS μ).R c x = (hnkGS μ').R c x ∧ (hnkGS μ).g c = (hnkGS μ').g c := by
  rcases h.lt_or_eq with h | rfl
  · exact hnkGS_ext hμ h hc x
  · exact ⟨rfl, rfl⟩

/-- **`b < Ω₁·Ω₁ + Ω₁·λ` (`λ` a limit) gives `hcN b G < φ(Ω₁·Ω₁ + Ω₁·μ, G+1)` for some `μ < λ`.** -/
theorem hnkGS_Bcof {l b : Ordinal.{0}} (hl : IsSuccLimit l) (hle : l ≤ Om1) (hb : b < Om1 * Om1 + Om1 * l) :
    ∃ μ, μ < l ∧ hcN b (gcG 0) < (hnkGS μ).B := by
  rcases lt_or_ge b (Om1 * Om1) with h | h
  · refine ⟨0, hl.bot_lt, ?_⟩
    rw [hnkGS_B (gv_Om1_pos), hnkG_B_eq gv_Om1_pos]
    refine hdN_lt_Nx ?_
    rw [mul_zero, add_zero]; exact hn_sq_succ gl_Om1_E h
  · obtain ⟨b', rfl⟩ := exists_add_of_le h
    have hb' : b' < Om1 * l := (add_lt_add_iff_left _).1 hb
    have hdiv : b' / Om1 < l := (lt_mul_iff_div_lt gv_Om1_pos.ne').1 hb'
    have hμ : b' / Om1 + 1 + 1 < l := hl.add_one_lt (hl.add_one_lt hdiv)
    refine ⟨_, hμ, ?_⟩
    rw [hnkGS_B (hμ.trans_le hle), hnkG_B_eq (hμ.trans_le hle)]
    refine hdN_lt_Nx ?_
    rw [add_assoc]
    refine (add_lt_add_iff_left _).2 ?_
    calc b' + 1 ≤ Om1 * (b' / Om1) + Om1 := Order.add_one_le_of_lt (lt_mul_div_add b' gv_Om1_pos.ne')
    _ = Om1 * (b' / Om1 + 1) := by rw [mul_add_one]
    _ < Om1 * (b' / Om1 + 1 + 1) := mul_lt_mul_of_pos_left (lt_add_one _) gv_Om1_pos

/-- **SMALL**: a code of `hnkGS μ` with gate below an `ε`-number `σ` lies in some `hnkGS μ'`, `μ' < σ`. -/
theorem hnk_small : ∀ μ, μ < Om1 → ∀ c, c < (hnkGS μ).B → ∀ σ, InE σ → σ < Om1 → (hnkGS μ).g c < σ →
    ∃ μ', μ' < σ ∧ c < (hnkGS μ').B := by
  intro μ
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  intro hμ c hc σ hσ hσ1 hg
  by_cases hμσ : μ < σ
  · exact ⟨μ, hμσ, hc⟩
  rcases zero_or_succ_or_isSuccLimit μ with h0 | ⟨ν, hν⟩ | hlim
  · exact absurd (by rw [h0]; exact hσ.pos) hμσ
  · have hν' : μ = ν + 1 := by rw [← hν, succ_eq_add_one]
    subst hν'
    have hν1 : ν < Om1 := (lt_add_one ν).trans hμ
    by_cases hcν : c < (hnkGS ν).B
    · rw [(hnkGS_ext hμ (lt_add_one ν) hcν 0).2] at hg
      exact IH ν (lt_add_one ν) hν1 c hcν σ hσ hσ1 hg
    · exfalso
      obtain ⟨⟨hsh, -⟩, -⟩ := hnkGS_inv ν hν1
      have e : hnkGS (ν + 1) = hnwU (hnGW (hnkPk ν).Λ (hnkNB hν1)) (hnkPk ν).St0 (hnkPk ν).h0 (hnkGS ν) hsh := by
        rw [hnkGS_succ]; unfold hnkGSucc; rw [dif_pos hν1, dif_pos hsh]
      rw [e] at hc hg
      have h := hnwU_highR _ _ _ _ hsh (not_lt.1 hcν) hc hσ hσ1 hg
      exact hμσ ((ev_isSuccLimit_of_inE hσ).add_one_lt (hnkPk_g_lt ν hν1 σ hσ h))
  · have hcS : c < veblen (Om1 * Om1 + Om1 * μ) (gcG 0 + 1) := by rw [← hnkGS_B hμ]; exact hc
    obtain ⟨b, hb, hcb⟩ := hgVeb_cof (hnkG_ne μ) (hnkG_fixG hμ) hcS
    obtain ⟨μ'', hμ'', hbμ⟩ := hnkGS_Bcof hlim hμ.le hb
    have hcμ : c < (hnkGS μ'').B := hcb.trans hbμ
    rw [(hnkGS_ext hμ hμ'' hcμ 0).2] at hg
    exact IH μ'' hμ'' (hμ''.trans hμ) c hcμ σ hσ hσ1 hg

/-! ## The union over all band levels -/

/-- **`φ(Ω₁·Ω₁ + Ω₁·Ω₁, G+1)`**: the bound of the union over all band levels (`= φ(Ω₁·Ω₁·2, G+1)`). -/
noncomputable def hnB : Ordinal.{0} := veblen (Om1 * Om1 + Om1 * Om1) (gcG 0 + 1)

theorem hnB_eq2 : hnB = veblen (Om1 * Om1 * 2) (gcG 0 + 1) := by unfold hnB; rw [mul_two_eq]

theorem hn_OO2_lt_G (α : Ordinal.{0}) : (Om1 : Ordinal.{0}) * Om1 + Om1 * Om1 < gcG α :=
  (inE_indec (Low.opow_eq_self_of_SC (gcG_SC α))).add_lt (hl_OO_lt_G α) (hl_OO_lt_G α)

theorem hn_OO2_ne : (Om1 : Ordinal.{0}) * Om1 + Om1 * Om1 ≠ 0 := hnkG_ne Om1

theorem hn_G_fixOO2 : veblen (Om1 * Om1 + Om1 * Om1) (gcG 0) = gcG 0 := gn_veb_fix (gcG_SC 0) (hn_OO2_lt_G 0)

/-- **Every `hnkGS μ`, `μ < Ω₁`, lies below `φ(Ω₁·Ω₁·2, G+1)`.** -/
theorem hnB_gt {μ : Ordinal.{0}} (hμ : μ < Om1) : (hnkGS μ).B < hnB := by
  rw [hnkGS_B hμ]; exact hnk_veb_lt hμ

/-- **The bounds `φ(Ω₁·Ω₁ + Ω₁·μ, G+1)`, `μ < Ω₁`, are cofinal in `φ(Ω₁·Ω₁·2, G+1)`.** -/
theorem hnB_cof {c : Ordinal.{0}} (hc : c < hnB) : ∃ μ, μ < Om1 ∧ c < (hnkGS μ).B := by
  obtain ⟨b, hb, hcb⟩ := hgVeb_cof hn_OO2_ne hn_G_fixOO2 hc
  obtain ⟨μ, hμ, hbμ⟩ := hnkGS_Bcof gl_Om1_lim le_rfl hb
  exact ⟨μ, hμ, hcb.trans hbμ⟩

theorem hnB_lt1 : hnB < gcG 1 := by
  have hG1 := gcG_SC 1
  have hE := Low.opow_eq_self_of_SC hG1
  have hfix : veblen (Om1 * Om1 + Om1 * Om1) (gcG 1) = gcG 1 := gn_veb_fix hG1 (hn_OO2_lt_G 1)
  have h2 := (isNormal_veblen (Om1 * Om1 + Om1 * Om1)).strictMono
    ((ev_isSuccLimit_of_inE hE).add_one_lt (gcG_lt zero_lt_one))
  unfold hnB; rwa [hfix] at h2

theorem hnB_fix1 : veblen 1 hnB = hnB := veblen_veblen_of_lt (hnkG_one Om1) _

theorem hnB_E : InE hnB := gg_veblen_eps hn_OO2_ne

theorem hnB_lim : IsSuccLimit hnB := ev_isSuccLimit_of_inE hnB_E

/-- The first band level containing `c`. -/
noncomputable def hnN (c : Ordinal.{0}) : Ordinal.{0} := sInf {μ | μ < Om1 ∧ c < (hnkGS μ).B}

theorem hnN_spec {c μ : Ordinal.{0}} (hμ : μ < Om1) (hc : c < (hnkGS μ).B) :
    hnN c ≤ μ ∧ hnN c < Om1 ∧ c < (hnkGS (hnN c)).B := by
  have hne : ({μ | μ < Om1 ∧ c < (hnkGS μ).B} : Set Ordinal.{0}).Nonempty := ⟨μ, hμ, hc⟩
  have hm := csInf_mem hne
  exact ⟨csInf_le' ⟨hμ, hc⟩, hm.1, hm.2⟩

theorem hnN_high {c : Ordinal.{0}} (hc : hnB ≤ c) : hnN c = 0 := by
  unfold hnN
  have he : ({μ | μ < Om1 ∧ c < (hnkGS μ).B} : Set Ordinal.{0}) = ∅ := by
    ext μ
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hμ hcμ
    exact absurd (hcμ.trans (hnB_gt hμ)) (not_lt.2 hc)
  rw [he]; exact Ordinal.sInf_empty

theorem hn_R_eq {c μ : Ordinal.{0}} (hμ : μ < Om1) (hc : c < (hnkGS μ).B) (x : Ordinal.{0}) :
    (hnkGS (hnN c)).R c x = (hnkGS μ).R c x := by
  obtain ⟨h1, -, h3⟩ := hnN_spec hμ hc
  exact (hnkGS_ext' hμ h1 h3 x).1.symm

theorem hn_g_eq {c μ : Ordinal.{0}} (hμ : μ < Om1) (hc : c < (hnkGS μ).B) :
    (hnkGS (hnN c)).g c = (hnkGS μ).g c := by
  obtain ⟨h1, -, h3⟩ := hnN_spec hμ hc
  exact (hnkGS_ext' hμ h1 h3 0).2.symm

theorem hn_R_succ (c x : Ordinal.{0}) : (hnkGS (hnN (c + 1))).R (c + 1) x = (hnkGS (hnN c)).R c x + 1 := by
  rcases lt_or_ge c hnB with h | h
  · obtain ⟨n, hn1, hn⟩ := hnB_cof (hnB_lim.add_one_lt h)
    rw [hn_R_eq hn1 hn, hn_R_eq hn1 ((lt_add_one c).trans hn), (hnkGS n).R_succ]
  · rw [hnN_high h, hnN_high (h.trans (le_self_add (a := c) (b := 1))), (hnkGS 0).R_succ]

theorem hn_g_le_succ (c : Ordinal.{0}) : (hnkGS (hnN c)).g c ≤ (hnkGS (hnN (c + 1))).g (c + 1) := by
  rcases lt_or_ge c hnB with h | h
  · obtain ⟨n, hn1, hn⟩ := hnB_cof (hnB_lim.add_one_lt h)
    rw [hn_g_eq hn1 hn, hn_g_eq hn1 ((lt_add_one c).trans hn)]; exact (hnkGS n).g_le_succ c
  · rw [hnN_high h, hnN_high (h.trans (le_self_add (a := c) (b := 1)))]; exact (hnkGS 0).g_le_succ c

/-- **The base reading of the union**: `φ(x·x + x·x, Γ_{x+1}+1)`. -/
noncomputable def hnBR (x : Ordinal.{0}) : Ordinal.{0} := veblen (x * x + x * x) (lgG x + 1)

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem hn_sq2l : x * x + x * x < lgG x :=
  (inE_indec (lgG_facts hx hx1).2.2.2.1).add_lt (hl_sq_lt hx hx1) (hl_sq_lt hx hx1)

theorem hn_sq2_one' : (1 : Ordinal.{0}) ≤ x * x + x * x :=
  ((one_lt_omega0.trans (omega0_lt_inE hx)).le.trans (hl_lt_sq hx).le).trans le_self_add

theorem hn_BR_eq : hnBR x = hdNx (x * x + x * x) (lgG x) :=
  (hdNx_fixP (hjG_fix hx hx1 (hn_sq2_one' hx hx1) (hn_sq2l hx hx1))).symm

theorem hn_BR_lt1 : hnBR x < gq 1 x := by
  rw [hn_BR_eq hx hx1]; exact hjG_lt1 hx hx1 (hn_sq2_one' hx hx1) (hn_sq2l hx hx1)

theorem hn_x_lt_BR : x < hnBR x := (lgG_facts hx hx1).2.1.trans ((lt_add_one _).trans_le (right_le_veblen _ _))

theorem hn_BR_fix1 : veblen 1 (hnBR x) = hnBR x :=
  veblen_veblen_of_lt ((one_lt_omega0.trans (omega0_lt_inE hx)).trans ((hl_lt_sq hx).trans_le le_self_add)) _

theorem hn_BR_fix2 : veblen 2 (hnBR x) = hnBR x :=
  veblen_veblen_of_lt ((show (2 : Ordinal.{0}) < ω from by exact_mod_cast natCast_lt_omega0 2).trans
    ((omega0_lt_inE hx).trans ((hl_lt_sq hx).trans_le le_self_add))) _

/-- **The bound field of every `hnkGS μ` lies below `φ(x·x + x·x, Γ_{x+1}+1)`.** -/
theorem hn_Z_le {μ : Ordinal.{0}} (hμ : μ < Om1) : (hnkGS μ).Z x ≤ hnBR x := by
  rw [(hnkGS_shape hμ).2.2.2.1 x hx hx1]
  split_ifs with h
  · refine (hb_evZ_lt_fix2 (hn_BR_fix2 hx hx1) ?_).le
    show veblen ((hnkPk μ).Λ.l x + 0) (lgG x + 1) < hnBR x
    rw [add_zero]
    refine hd_veb_left_lt ?_ _
    rw [← mul_two_eq]
    exact le_self_add.trans_lt (hnkNB hμ x hx hx1 (max_lt_iff.1 h).1)
  · rw [(hnGW (hnkPk μ).Λ (hnkNB hμ)).hnwZo_low (fun h' => h (max_lt h' hx.pos))]
    show veblen (max ω x * max ω x * 2) (lgG x + 1) ≤ hnBR x
    rw [max_eq_right (omega0_lt_inE hx).le, mul_two_eq]; exact le_rfl

/-- **The gate of `hnkGS μ` is below `x` for `μ < x`.** -/
theorem hn_γ_lt {μ : Ordinal.{0}} (hμ : μ < x) : (hnkGS μ).γ < x :=
  (hnkGS_γ_le (hμ.trans hx1)).trans_lt hμ

/-- **The base reading of `hnkGS μ` at `μ < x`**: `φ(x·x + x·μ, Γ_{x+1}+1)`. -/
theorem hn_b_eq {μ : Ordinal.{0}} (hμ : μ < x) : (hnkGS μ).b x = hdNx (x * x + x * μ) (lgG x) := by
  have hμ1 : μ < Om1 := hμ.trans hx1
  have hg : (hnkPk μ).Λ.g < x := by rw [← hnkGS_γ hμ1]; exact hn_γ_lt hx hx1 hμ
  rw [(hnkGS_shape hμ1).2.2.1 x hx hx1 (max_lt hg hx.pos)]
  show veblen ((hnkPk μ).Λ.l x + 0) (lgG x + 1) = _
  rw [hnkPk_l hμ1 hg, add_zero, hnkG_b_eq hμ hx hx1]

/-- **The base reading of `hnkGS μ` lies below `φ(x·x + x·x, Γ_{x+1}+1)`** (`μ < x`). -/
theorem hn_b_lt {μ : Ordinal.{0}} (hμ : μ < x) : (hnkGS μ).b x < hnBR x := by
  rw [hn_b_eq hx hx1 hμ, ← hnkG_b_eq hμ hx hx1]
  exact hd_veb_left_lt ((add_lt_add_iff_left _).2 (mul_lt_mul_of_pos_left hμ hx.pos)) _

end Base

/-- **Lemma EXACT for `φ(ρ·ρ + ρ·ρ, Γ_{ρ+1}+1)`** (`Exact.pi_sq`, `Exact.pi_add`). -/
theorem hn_BR_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) : hnBR ρ ∈ TB ρ σ ∧ pi σ ρ (hnBR ρ) = hnBR σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨s1, s2⟩ := pi_sq hB
  obtain ⟨a1, a2⟩ := pi_add hB s1 s1
  rw [s2] at a2
  rw [hn_BR_eq hB.2.1 hρ1, hn_BR_eq hB.1 hσ1]
  exact hjG_S_pi hB ⟨a1, a2⟩ (hn_sq2_one' hB.2.1 hρ1) (hn_sq2l hB.2.1 hρ1) (hn_sq2_one' hB.1 hσ1)
    (hn_sq2l hB.1 hσ1)

/-- **A code of the union with gate below an `ε`-number `σ` lies in `hnkGS μ`, `μ < σ`.** -/
theorem hn_small' {c σ : Ordinal.{0}} (hc : c < hnB) (hσ : InE σ) (hσ1 : σ < Om1)
    (hg : (hnkGS (hnN c)).g c < σ) : ∃ μ, μ < σ ∧ c < (hnkGS μ).B := by
  obtain ⟨n, hn1, hn⟩ := hnB_cof hc
  rw [hn_g_eq hn1 hn] at hg
  exact hnk_small n hn1 c hn σ hσ hσ1 hg

theorem hn_OO2_mem (S : InaccSeq.{0}) (a b : Ordinal.{0}) : (Om1 : Ordinal.{0}) * Om1 + Om1 * Om1 ∈ S.CSet a b :=
  CSet.add_mem (hl_OO_mem S a b) (hl_OO_mem S a b)
/-- **THE UNION OVER ALL BAND LEVELS `Ω₁·Ω₁ + Ω₁·μ`, `μ < Ω₁`**: a gated digit system (`HgVD`) with the bound
`φ(Ω₁·Ω₁·2, G+1)`, the base gate `0`, the base reading `φ(x·x + x·x, Γ_{x+1}+1)` (the level `Ω₁·Ω₁·2` read as
`x·x + x·x`) and the
bound field `evZ(φ(x·x + x·x, Γ_{x+1}+1)) < Γ_{x+2}`. -/
noncomputable def hnU : HgVD where
  B := hnB
  γ := 0
  γ_lt := gv_Om1_pos
  γ_cl := fun _ hZ _ _ => hZ.1
  γ_G := fun _ => rfl
  R := fun c x => (hnkGS (hnN c)).R c x
  g := fun c => (hnkGS (hnN c)).g c
  b := hnBR
  ba := hnBR
  ix := hnB
  Z := fun x => evZ (hnBR x)
  B_E := hnB_E
  G_le := (lt_add_one _).le.trans (right_le_veblen _ _)
  B_lt1 := hnB_lt1
  B_ix := hnB_fix1.symm
  Z_fix := fun _ _ _ => epsilon_evZ _
  Z_G1 := fun x hx hx1 => gw_evZ_lt1 hx hx1 (hn_BR_lt1 hx hx1)
  ix_mem := fun S a b ha _ => CSet.phi_mem (hn_OO2_mem S a b) (CSet.succ_mem (gmS_G0_mem S ha))
  g_lt := fun c hc => by
    obtain ⟨n, hn1, hn⟩ := hnB_cof hc
    rw [hn_g_eq hn1 hn]; exact (hnkGS n).g_lt c hn
  g_zero := by rw [hn_g_eq gv_Om1_pos (hnkGS 0).B_pos]; exact (hnkGS 0).g_zero
  g_nat := fun k => by rw [hn_g_eq gv_Om1_pos ((hnkGS 0).nat_lt_B k)]; exact (hnkGS 0).g_nat k
  g_E := by rw [hn_g_eq gv_Om1_pos (hnkGS 0).E_lt_B]; exact (hnkGS 0).g_E
  g_lowE := fun c hc => by rw [hn_g_eq gv_Om1_pos (hc.trans (hnkGS 0).E_lt_B)]; exact (hnkGS 0).g_lowE c hc
  g_G0 := fun h => by
    obtain ⟨n, hn1, hn⟩ := hnB_cof h
    rw [hn_g_eq hn1 hn]; exact (hnkGS n).g_G0 hn
  g_add := fun Z hZ hωZ x y hxy hgx hgy => by
    obtain ⟨n, hn1, hn⟩ := hnB_cof hxy
    have hx : x < (hnkGS n).B := lt_of_le_of_lt le_self_add hn
    have hy : y < (hnkGS n).B := lt_of_le_of_lt le_add_self hn
    show (hnkGS (hnN (x + y))).g (x + y) < Z
    rw [hn_g_eq hn1 hn]; rw [hn_g_eq hn1 hx] at hgx; rw [hn_g_eq hn1 hy] at hgy
    exact (hnkGS n).g_add Z hZ hωZ x y hn hgx hgy
  g_opow := fun Z hZw hωZ y hy hg => by
    obtain ⟨n, hn1, hn⟩ := hnB_cof hy
    have hy' : y < (hnkGS n).B := lt_of_le_of_lt (right_le_opow y one_lt_omega0) hn
    show (hnkGS (hnN (ω ^ y))).g (ω ^ y) < Z
    rw [hn_g_eq hn1 hn]; rw [hn_g_eq hn1 hy'] at hg
    exact (hnkGS n).g_opow Z hZw hωZ y hn hg
  code_gate := fun Z hZ1 hZ0 hZa hZp At hAt c hc hcB => by
    obtain ⟨n, hn1, hn⟩ := hnB_cof hcB
    show (hnkGS (hnN c)).g c < Z
    rw [hn_g_eq hn1 hn]
    exact (hnkGS n).code_gate Z hZ1 hZ0 hZa hZp At (fun s hs => (hAt s hs).imp_right
      (fun h => (hnB_gt hn1).le.trans h)) c hc hn
  g_succ := fun Z hZ c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hnB_cof hc
    have hc' : c < (hnkGS n).B := (lt_add_one c).trans hn
    show (hnkGS (hnN (c + 1))).g (c + 1) < Z
    rw [hn_g_eq hn1 hn]; rw [hn_g_eq hn1 hc'] at hg
    exact (hnkGS n).g_succ Z hZ c hn hg
  g_le_succ := hn_g_le_succ
  mem := fun S a b ha c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hnB_cof hc
    rw [hn_g_eq hn1 hn] at hg
    exact (hnkGS n).mem S a b ha c hn hg
  R_zero := fun x => by rw [hn_R_eq gv_Om1_pos (hnkGS 0).B_pos]; exact (hnkGS 0).R_zero x
  R_nat := fun k x => by rw [hn_R_eq gv_Om1_pos ((hnkGS 0).nat_lt_B k)]; exact (hnkGS 0).R_nat k x
  R_E := fun x => by rw [hn_R_eq gv_Om1_pos (hnkGS 0).E_lt_B]; exact (hnkGS 0).R_E x
  R_succ := hn_R_succ
  R_pos := fun x hx hx1 c hc0 hc hg => by
    obtain ⟨n, hn1, hn⟩ := hnB_cof hc
    show 0 < (hnkGS (hnN c)).R c x
    rw [hn_R_eq hn1 hn]; rw [hn_g_eq hn1 hn] at hg
    exact (hnkGS n).R_pos x hx hx1 c hc0 hn hg
  R_omega := fun x hx hx1 c hω hc hg => by
    obtain ⟨n, hn1, hn⟩ := hnB_cof hc
    show ω ≤ (hnkGS (hnN c)).R c x
    rw [hn_R_eq hn1 hn]; rw [hn_g_eq hn1 hn] at hg
    exact (hnkGS n).R_omega x hx hx1 c hω hn hg
  R_lt_b := fun x hx hx1 _ c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hnB_cof hc
    show (hnkGS (hnN c)).R c x < hnBR x
    rw [hn_R_eq hn1 hn]; rw [hn_g_eq hn1 hn] at hg
    exact ((hnkGS n).R_lt_Z x hx hx1 c hn hg).trans_le (hn_Z_le hx hx1 hn1)
  R_lt_Z := fun x hx hx1 c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hnB_cof hc
    show (hnkGS (hnN c)).R c x < evZ (hnBR x)
    rw [hn_R_eq hn1 hn]; rw [hn_g_eq hn1 hn] at hg
    exact (((hnkGS n).R_lt_Z x hx hx1 c hn hg).trans_le (hn_Z_le hx hx1 hn1)).trans (lt_evZ _)
  mono := fun x hx hx1 c hc d hdc hgc hgd => by
    obtain ⟨n, hn1, hn⟩ := hnB_cof hc
    have hd : d < (hnkGS n).B := hdc.trans hn
    show (hnkGS (hnN d)).R d x < (hnkGS (hnN c)).R c x
    rw [hn_R_eq hn1 hn, hn_R_eq hn1 hd]; rw [hn_g_eq hn1 hn] at hgc; rw [hn_g_eq hn1 hd] at hgd
    exact (hnkGS n).mono x hx hx1 c hn d hdc hgc hgd
  cof := fun x hx hx1 c hc hg ν hν => by
    obtain ⟨n, hn1, hn⟩ := hnB_cof hc
    rw [hn_R_eq hn1 hn] at hν; rw [hn_g_eq hn1 hn] at hg
    obtain ⟨d, hdc, hgd, hνd⟩ := (hnkGS n).cof x hx hx1 c hn hg ν hν
    have hd : d < (hnkGS n).B := hdc.trans hn
    exact ⟨d, hdc, by show (hnkGS (hnN d)).g d < x; rw [hn_g_eq hn1 hd]; exact hgd,
      by show ν ≤ (hnkGS (hnN d)).R d x; rw [hn_R_eq hn1 hd]; exact hνd⟩
  b_cof := fun x hx hx1 _ ν hν => by
    have hfix : veblen (x * x + x * x) (lgG x) = lgG x := hjG_fix hx hx1 (hn_sq2_one' hx hx1) (hn_sq2l hx hx1)
    obtain ⟨b, hb, hνb⟩ := hgVeb_cof (zero_lt_one.trans_le (hn_sq2_one' hx hx1)).ne' hfix hν
    obtain ⟨μ, hμ, hb1⟩ : ∃ μ, μ < x ∧ b + 1 < x * x + x * μ := by
      rcases lt_or_ge b (x * x) with h | h
      · exact ⟨0, hx.pos, by rw [mul_zero, add_zero]; exact hn_sq_succ hx h⟩
      · obtain ⟨b', rfl⟩ := exists_add_of_le h
        have hb' : b' < x * x := (add_lt_add_iff_left _).1 hb
        have hdiv : b' / x < x := (lt_mul_iff_div_lt hx.pos.ne').1 hb'
        have hlx := ev_isSuccLimit_of_inE hx
        refine ⟨b' / x + 1 + 1, hlx.add_one_lt (hlx.add_one_lt hdiv), ?_⟩
        rw [add_assoc]
        refine (add_lt_add_iff_left _).2 ?_
        calc b' + 1 ≤ x * (b' / x) + x := Order.add_one_le_of_lt (lt_mul_div_add b' hx.pos.ne')
        _ = x * (b' / x + 1) := by rw [mul_add_one]
        _ < x * (b' / x + 1 + 1) := mul_lt_mul_of_pos_left (lt_add_one _) hx.pos
    have hμ1 : μ < Om1 := hμ.trans hx1
    have hνb' : ν < (hnkGS μ).b x := by
      rw [hn_b_eq hx hx1 hμ]; exact hνb.trans (hdN_lt_Nx hb1)
    obtain ⟨d, hd, hgd, hνd⟩ := (hnkGS μ).b_cof x hx hx1 (hn_γ_lt hx hx1 hμ) ν hνb'
    exact ⟨d, hd.trans (hnB_gt hμ1), by show (hnkGS (hnN d)).g d < x; rw [hn_g_eq hμ1 hd]; exact hgd,
      by show ν < (hnkGS (hnN d)).R d x; rw [hn_R_eq hμ1 hd]; exact hνd⟩
  b_E := fun x hx hx1 _ => gg_veblen_eps (zero_lt_one.trans_le (hn_sq2_one' hx hx1)).ne'
  x_lt_b := fun x hx hx1 _ => hn_x_lt_BR hx hx1
  b_eN := fun x hx hx1 _ => gz_eN_fix hx hx1 (hn_BR_fix1 hx hx1) (hn_x_lt_BR hx hx1) (hn_BR_lt1 hx hx1)
  ba_lt := fun x hx hx1 _ => hn_BR_lt1 hx hx1
  b_Z := fun _ _ _ _ => go_eN_lt_evZ (lt_evZ _)
  b_pi := fun _ _ hB _ => hn_BR_pi hB
  ba_pi := fun _ _ hB _ => hn_BR_pi hB
  ex := fun σ ρ hB c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hnB_cof hc
    show (hnkGS (hnN c)).R c ρ ∈ TB ρ σ ∧ pi σ ρ ((hnkGS (hnN c)).R c ρ) = (hnkGS (hnN c)).R c σ
    rw [hn_R_eq hn1 hn, hn_R_eq hn1 hn]; rw [hn_g_eq hn1 hn] at hg
    exact (hnkGS n).ex σ ρ hB c hn hg
  dig := fun σ ρ hB _ d hd hg P P' hat => by
    have hσ1 : σ < Om1 := hB.2.2.1.trans hB.2.2.2
    obtain ⟨μ, hμσ, hdμ⟩ := hn_small' hd hB.1 hσ1 hg
    have hμ1 : μ < Om1 := hμσ.trans hσ1
    show ω ^ P * (hnkGS (hnN d)).R d ρ ∈ TB ρ σ ∧
      pi σ ρ (ω ^ P * (hnkGS (hnN d)).R d ρ) = ω ^ P' * (hnkGS (hnN d)).R d σ
    rw [hn_R_eq hμ1 hdμ, hn_R_eq hμ1 hdμ]; rw [hn_g_eq hμ1 hdμ] at hg
    exact (hnkGS μ).dig σ ρ hB (hn_γ_lt hB.1 hσ1 hμσ) d hdμ hg P P' (fun β hβ hβe =>
      hat β hβ (hβe.trans (hn_b_lt hB.2.1 hB.2.2.2 (hμσ.trans hB.2.2.1))))
  ld := fun c hl hc => by
    obtain ⟨n, hn1, hn⟩ := hnB_cof hc
    obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := (hnkGS n).ld c hl hn
    have hcpn : cp < (hnkGS n).B := hcp.trans hn
    refine ⟨cp, lp, T, hcp, ?_, fun x hx hx1 hg => ?_, fun σ ρ hB hg => hex σ ρ hB ?_⟩
    · show (hnkGS (hnN cp)).g cp ≤ (hnkGS (hnN c)).g c
      rw [hn_g_eq hn1 hn, hn_g_eq hn1 hcpn]; exact hgcp
    · have hg' : (hnkGS n).g c < x := by rw [← hn_g_eq hn1 hn]; exact hg
      show (hnkGS (hnN c)).R c x = _ ∧ _
      rw [hn_R_eq hn1 hn, hn_R_eq hn1 hcpn]
      exact hdec x hx hx1 hg'
    · rw [← hn_g_eq hn1 hn]; exact hg

theorem hnU_B : hnU.B = veblen (Om1 * Om1 + Om1 * Om1) (gcG 0 + 1) := rfl

theorem hnU_γ : hnU.γ = 0 := rfl

theorem hnU_b (x : Ordinal.{0}) : hnU.b x = veblen (x * x + x * x) (lgG x + 1) := rfl

/-- **The union extends every `hnkGS μ`, `μ < Ω₁`** (readings). -/
theorem hnU_R {μ c : Ordinal.{0}} (hμ : μ < Om1) (hc : c < (hnkGS μ).B) (x : Ordinal.{0}) :
    hnU.R c x = (hnkGS μ).R c x := hn_R_eq hμ hc x

/-- **The union extends every `hnkGS μ`, `μ < Ω₁`** (gates). -/
theorem hnU_g {μ c : Ordinal.{0}} (hμ : μ < Om1) (hc : c < (hnkGS μ).B) : hnU.g c = (hnkGS μ).g c := hn_g_eq hμ hc

/-! ## The location -/

section Loc

variable (S : InaccSeq.{0})

theorem hnU_γK : hnU.γ < Td.tdK S := hg_K_pos S

/-- **`φ(Ω₁·Ω₁·2, G+1)` IS LOCATED**: `Λ⁺ = ι(Γ(φ(Ω₁·Ω₁·2, G+1))·ω)`, `P(…) < L(0)` (UNCONDITIONAL). -/
theorem hnU_loc : ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG hnU.B * ω) ∧
    upsilon (xtB1 X) = Pv S (gcG hnU.B * ω) ∧ Pv S (gcG hnU.B * ω) < Nc.ncL S 0 :=
  hgV_locD hnU S (hnU_γK S)

/-- **Theorem BLK^O below `P(Γ(φ(Ω₁·Ω₁·2, G+1))·ω)`, with the exact reaches** (UNCONDITIONAL). -/
theorem hnU_blk :
    let X := gsX hnU.step.toRS _ hnU.E_lt_B.le hnU.B_lt_NB S (hgV_locD_g hnU S (hnU_γK S))
    (∀ c' d, c' < d → d < upsilon (xtB1 X) → (le2 c' d ↔ ∃ μ, ∃ j : ℕ, (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 X ∧
        c' = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧ d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 X →
      (∀ c' < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c' g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec X l)) ∧
    (∀ α < upsilon (xtB1 X), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  hgV_locD_blk hnU S (hnU_γK S)

/-- **ENUM-REACH at every range restart below `ι(Γ(φ(Ω₁·Ω₁·2, G+1))·ω)`, fixed points included** (UNCONDITIONAL). -/
theorem hnU_enum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG hnU.B * ω)) :
    CdUpper S l ∧ CdLower S l := hgV_locD_enum hnU S (hnU_γK S) hr hl

/-- **CapV at every range restart below `ι(Γ(φ(Ω₁·Ω₁·2, G+1))·ω)`** (UNCONDITIONAL). -/
theorem hnU_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG hnU.B * ω)) : CdCapV S l :=
  hgV_locD_capV hnU S (hnU_γK S) hr hl

/-- **THE ROAD**: UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ(φ(Ω₁·Ω₁·2, G+1))·ω)` (CapV also `υ_λ < L(ω)`), (CL),
EQ, TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem hnU_road (hU : ∀ l, CdRange S l → iota S (gcG hnU.B * ω) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG hnU.B * ω) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG hnU.B * ω) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  gv_road_of S _ (fun _ hr h => hnU_enum S hr h) (fun _ hr h => hnU_capV S hr h) hU hL hV hC hEQ hrest hB2

/-- **`Γ(φ(Ω₁·Ω₁·2, G+1)) < Ω₂`.** -/
theorem hnB_lt_Om2 : gcG hnB < Om (1 + 1) := by
  have hBE : InE Tf.tfBG := Low.opow_eq_self_of_SC Tf.tfBG_SC
  have hO : (Om1 : Ordinal.{0}) < Tf.tfBG := Tf.tfBG_gt
  have h1 : (1 : Ordinal.{0}) < Tf.tfBG := one_lt_omega0.trans (omega0_lt_inE hBE)
  have hG1 : gcG 1 < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) h1)
  have h2 : gcG hnB < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) (hnB_lt1.trans hG1))
  exact h2.trans Tf.tfBG_lt_Om2

/-- **The order of the frontiers**: `φ(Ω₁·Ω₁, G+1) < φ(Ω₁·Ω₁·2, G+1)`, `ι(Γ(φ(Ω₁·Ω₁, G+1))·ω) ≤
ι(Γ(φ(Ω₁·Ω₁·2, G+1))·ω) ≤ ι(Ω₂)` and `P(Γ(φ(Ω₁·Ω₁·2, G+1))·ω) ≤ P(Ω₂) < L(0)`. -/
theorem hnU_fr_order :
    hlB < hnB ∧ iota S (gcG hlB * ω) ≤ iota S (gcG hnB * ω) ∧
      iota S (gcG hnB * ω) ≤ iota S (Om (1 + 1)) ∧
      Pv S (gcG hnB * ω) ≤ Pv S (Om (1 + 1)) ∧ Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have hlt : hlB < hnB := by
    unfold hlB hnB
    exact hd_veb_left_lt (lt_add_of_pos_right _ (mul_pos gv_Om1_pos gv_Om1_pos)) _
  have hVw : gcG hnB * ω < Om (1 + 1) := by
    have hO2 : InE (Om (1 + 1) : Ordinal.{0}) := Low.opow_eq_self_of_SC Ld.ldOm2_SC
    exact InE.mul_lt hO2 hnB_lt_Om2 ((omega0_lt_inE hO2))
  refine ⟨hlt, iota_mono _ _ (mul_le_mul_right' (gcG_lt hlt).le ω),
    iota_mono _ _ hVw.le, Nm.Pv_mono hVw.le, ga_Pv_lt_L0 S le_rfl⟩

/-- **NON-VACUITY (relative)**: the hypotheses UPPER, LOWER, CapV of `hnU_road` (asked from
`ι(Γ(φ(Ω₁·Ω₁·2, G+1))·ω)` on) are EQUIVALENT to those of the round-105 road `Hl.hlU_road` (asked from
`ι(Γ(φ(Ω₁·Ω₁, G+1))·ω)` on): the restarts in between are settled unconditionally (`hnU_enum`, `hnU_capV`). -/
theorem hnU_hyp_iff :
    ((∀ l, CdRange S l → iota S (gcG hlU.B * ω) ≤ l → CdUpper S l) ↔
      (∀ l, CdRange S l → iota S (gcG hnU.B * ω) ≤ l → CdUpper S l)) ∧
    ((∀ l, CdRange S l → iota S (gcG hlU.B * ω) ≤ l → CdLower S l) ↔
      (∀ l, CdRange S l → iota S (gcG hnU.B * ω) ≤ l → CdLower S l)) ∧
    ((∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG hlU.B * ω) ≤ l → CdCapV S l) ↔
      (∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG hnU.B * ω) ≤ l → CdCapV S l)) := by
  have hle : iota S (gcG hlU.B * ω) ≤ iota S (gcG hnU.B * ω) := (hnU_fr_order S).2.1
  refine ⟨⟨fun h l hr hl => h l hr (hle.trans hl), fun h l hr hl => ?_⟩,
    ⟨fun h l hr hl => h l hr (hle.trans hl), fun h l hr hl => ?_⟩,
    ⟨fun h l hr hu hl => h l hr hu (hle.trans hl), fun h l hr hu hl => ?_⟩⟩
  · rcases lt_or_ge l (iota S (gcG hnU.B * ω)) with h' | h'
    · exact (hnU_enum S hr h').1
    · exact h l hr h'
  · rcases lt_or_ge l (iota S (gcG hnU.B * ω)) with h' | h'
    · exact (hnU_enum S hr h').2
    · exact h l hr h'
  · rcases lt_or_ge l (iota S (gcG hnU.B * ω)) with h' | h'
    · exact hnU_capV S hr h'
    · exact h l hr hu h'

end Loc

end Googology.Trans.PoR.InaccPsi.R2.Hn

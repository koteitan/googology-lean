import Googology.Trans.PoR.InaccPsi.R2.HlFr

/-!
# HlU: THE LEVEL `Ω₁·Ω₁` READ AS `x·x`: THE UNION OF ALL `Hl.hlkGS μ`, `μ < Ω₁`; THE FRONTIER PASSES `Ω₁·K`

The systems `Hl.hlkGS μ` (bound `φ(Ω₁·(1+μ), G+1)`, base gate `≤ 1+μ`) exist for every `μ < Ω₁`, but only those with
`μ < K = ψ_{Ω₁}(Ω_ω)` are located by `Hg.hgV_locD` (base gate below `K`).  Their union over ALL `μ < Ω₁` is a gated
digit system (`Hg.HgVD`) with the bound `φ(Ω₁·Ω₁, G+1)`, the base gate `0` and the base reading
`φ(x·x, Γ_{x+1}+1)`: the level `Ω₁·Ω₁` is read as `x·x` (Lemma EXACT `π(ρ·ρ) = σ·σ` is `Exact.pi_sq`).  A code of
`hlkGS μ` with gate below an `ε`-number `σ` lies in some `hlkGS μ'`, `μ' < σ` (`hl_small`): the codes past the start of
the union over `G` at the level `Ω₁·(1+ν) + Ω₁` have a gate `≥` the reading gate of `G` there, the gate of the
level datum (`hlw_highR`), and that gate lies below an `ε`-number `σ` only if `ν < σ` (`hlkPk_g_lt`).  So the union is
located with base gate `0 < K`.

This is the port of `Hg.hgU` (the union of `Hf.hfGL ν`, level `Ω₁` read `x`) to the systems `Hl.hlkGS μ` (level
`Ω₁·Ω₁` read `x·x`): what differs is the family of members, their bounds `φ(Ω₁·(1+μ), G+1)`, the base reading
`φ(x·x, Γ_{x+1}+1)` in place of `φ(x, Γ_{x+1}+1)`, and the SMALL lemma (`hl_small`, via `hlw_highR`, `hlkPk_g_lt`).

* `hlw_highR` (**codes past the start of the union over a base `P` have a gate `≥ P.γR`**), `hlwU_highR`;
* `hlkPk_g_lt` (**the gate of `hlkPk ν` below an `ε`-number `σ` forces `ν < σ`**), `hlkGS_ext'`, `hlkGS_Bcof`,
  `hl_small` (**SMALL for the recursion `hlkGS`**);
* `hlB` (`φ(Ω₁·Ω₁, G+1)`), `hlB_gt`, `hlB_cof`, `hlBR` (`φ(x·x, Γ_{x+1}+1)`), `hl_BR_pi` (**EXACT for it**),
  `hlU` (**THE UNION OVER ALL LEVELS `Ω₁·(1+μ)`**), `hlU_R`, `hlU_g`;
* `hlU_loc` (**`φ(Ω₁·Ω₁, G+1)` IS LOCATED**), `hlU_blk`, `hlU_enum`, `hlU_capV`, `hlU_road`, `hlU_fr_order`.

No new axiom.  New definitions: `hlB`, `hlN`, `hlBR`, `hlU`.
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
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The reading gate past the start of the union over a base -/

section High

variable {Λ : HlLv} (P : HlWB Λ) (St0 : HlVStTy Λ 0) (h0 : ∀ Q U h, HlVSpec Q U (St0 Q U h)) (S0 : HgVD)
  (hS0 : HlWShape P 0 S0)

include h0 hS0

/-- **The codes of `hlwL κ` past the start `S0` have a gate `≥` the reading gate `γR` of `P`.** -/
theorem hlw_highR : ∀ κ, κ < Om1 → ∀ c, S0.B ≤ c → c < (hlwL P St0 S0 κ).B → ∀ σ, InE σ → σ < Om1 →
    (hlwL P St0 S0 κ).g c < σ → P.γR < σ := by
  intro κ
  induction κ using WellFoundedLT.induction with
  | ind κ IH =>
  intro hκ c hSc hc σ hσ hσ1 hg
  have hI := hlwL_inv P St0 h0 S0 hS0
  rcases zero_or_succ_or_isSuccLimit κ with h0' | ⟨μ, hμ⟩ | hlim
  · subst h0'
    rw [hlwL_zero, hlwSt_eq P St0 h0 hκ hS0] at hc hg
    exact (max_lt_iff.1 (hlw_highN _ _ hc hSc hσ hσ1 hg)).1
  · have hμ' : κ = μ + 1 := by rw [← hμ, succ_eq_add_one]
    subst hμ'
    have hμ1 : μ < Om1 := (lt_add_one μ).trans hκ
    by_cases hcμ : c < (hlwL P St0 S0 μ).B
    · have e := ((hI (μ + 1) hκ).2 μ (le_add_right le_rfl) c 0 hcμ).2
      rw [e] at hg
      exact IH μ (lt_add_one μ) hμ1 c hSc hcμ σ hσ hσ1 hg
    · have hsh := hlw_ok_shape P hκ (hI μ hμ1).1
      rw [hlwL_succ, hlwSt_eq P St0 h0 hκ hsh] at hc hg
      exact (max_lt_iff.1 (hlw_highN _ _ hc (not_lt.1 hcμ) hσ hσ1 hg)).1
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
      exact IH κ'' hκ'' hκ''1 c hSc hcν σ hσ hσ1 hg
    · rw [hlwL_limit P St0 S0 hlim, eU, hlwSt_eq P St0 h0 hκ hsh] at hc hg
      exact (max_lt_iff.1 (hlw_highN _ _ hc (by rw [hsh.1]; exact not_lt.1 hcS) hσ hσ1 hg)).1

/-- **A code of the union over `P` past the start `S0` with gate below an `ε`-number `σ` forces `P.γR < σ`.** -/
theorem hlwU_highR {c σ : Ordinal.{0}} (hSc : S0.B ≤ c) (hc : c < (hlwU P St0 h0 S0 hS0).B) (hσ : InE σ)
    (hσ1 : σ < Om1) (hg : (hlwU P St0 h0 S0 hS0).g c < σ) : P.γR < σ := by
  obtain ⟨n, hn1, hn⟩ := hlwB_cof P St0 h0 S0 hS0 hc
  rw [hlwU_g P St0 h0 S0 hS0 hn1 hn] at hg
  exact hlw_highR P St0 h0 S0 hS0 n hn1 c hSc hn σ hσ hσ1 hg

end High

/-! ## SMALL for the recursion `hlkGS` -/

/-- **The gate of `hlkPk ν` below an `ε`-number `σ` forces `ν < σ`.** -/
theorem hlkPk_g_lt : ∀ ν, ν < Om1 → ∀ σ, InE σ → (hlkPk ν).Λ.g < σ → ν < σ := by
  intro ν
  induction ν using WellFoundedLT.induction with
  | ind ν IH =>
  intro hν σ hσ hg
  rcases zero_or_succ_or_isSuccLimit ν with h0 | ⟨μ, hμ⟩ | hlim
  · rw [h0]; exact hσ.pos
  · have hμ' : ν = μ + 1 := by rw [← hμ, succ_eq_add_one]
    subst hμ'
    have hg' : (hlkPk μ).Λ.g < σ := by rw [hlkPk_succ] at hg; exact hg
    exact (ev_isSuccLimit_of_inE hσ).add_one_lt (IH μ (lt_add_one μ) ((lt_add_one μ).trans hν) σ hσ hg')
  · rw [hlkPk_lim_Λ hlim hν] at hg
    exact le_add_self.trans_lt (hl_gt_E hσ hg)

theorem hlkGS_ext' {μ' μ : Ordinal.{0}} (hμ : μ < Om1) (h : μ' ≤ μ) {c : Ordinal.{0}} (hc : c < (hlkGS μ').B)
    (x : Ordinal.{0}) : (hlkGS μ).R c x = (hlkGS μ').R c x ∧ (hlkGS μ).g c = (hlkGS μ').g c := by
  rcases h.lt_or_eq with h | rfl
  · exact hlkGS_ext hμ h hc x
  · exact ⟨rfl, rfl⟩

/-- **`b < Ω₁·λ` (`λ` a limit) gives `hcN b G < φ(Ω₁·(1+μ''), G+1)` for some `μ'' < λ`.** -/
theorem hlkGS_Bcof {l b : Ordinal.{0}} (hl : IsSuccLimit l) (hle : l ≤ Om1) (hb : b < Om1 * (1 + l)) :
    ∃ μ, μ < l ∧ hcN b (gcG 0) < (hlkGS μ).B := by
  rw [one_add_of_omega0_le (omega0_le_of_isSuccLimit hl)] at hb
  have hdiv : b / Om1 < l := (lt_mul_iff_div_lt gv_Om1_pos.ne').1 hb
  have hμ : b / Om1 + 1 + 1 < l := hl.add_one_lt (hl.add_one_lt hdiv)
  refine ⟨_, hμ, ?_⟩
  rw [hlkGS_B (hμ.trans_le hle), hlkG_B_eq (hl_one_add (hμ.trans_le hle))]
  refine hdN_lt_Nx ?_
  calc b + 1 ≤ Om1 * (b / Om1) + Om1 := Order.add_one_le_of_lt (lt_mul_div_add b gv_Om1_pos.ne')
  _ = Om1 * (b / Om1 + 1) := by rw [mul_add_one]
  _ < Om1 * (b / Om1 + 1 + 1) := mul_lt_mul_of_pos_left (lt_add_one _) gv_Om1_pos
  _ ≤ Om1 * (1 + (b / Om1 + 1 + 1)) := mul_le_mul_left' le_add_self _

/-- **SMALL**: a code of `hlkGS μ` with gate below an `ε`-number `σ` lies in some `hlkGS μ'`, `μ' < σ`. -/
theorem hl_small : ∀ μ, μ < Om1 → ∀ c, c < (hlkGS μ).B → ∀ σ, InE σ → σ < Om1 → (hlkGS μ).g c < σ →
    ∃ μ', μ' < σ ∧ c < (hlkGS μ').B := by
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
    by_cases hcν : c < (hlkGS ν).B
    · rw [(hlkGS_ext hμ (lt_add_one ν) hcν 0).2] at hg
      exact IH ν (lt_add_one ν) hν1 c hcν σ hσ hσ1 hg
    · exfalso
      obtain ⟨⟨hsh, -⟩, -⟩ := hlkGS_inv ν hν1
      have e : hlkGS (ν + 1) = hlwU (hlGW (hlkPk ν).Λ) (hlkPk ν).St0 (hlkPk ν).h0 (hlkGS ν) hsh := by
        rw [hlkGS_succ]; unfold hlkGSucc; rw [dif_pos hsh]
      rw [e] at hc hg
      have h := hlwU_highR _ _ _ _ hsh (not_lt.1 hcν) hc hσ hσ1 hg
      exact hμσ ((ev_isSuccLimit_of_inE hσ).add_one_lt (hlkPk_g_lt ν hν1 σ hσ h))
  · have hcS : c < veblen (Om1 * (1 + μ)) (gcG 0 + 1) := by rw [← hlkGS_B hμ]; exact hc
    have hL0 : (Om1 : Ordinal.{0}) * (1 + μ) ≠ 0 := hkG_ne le_self_add
    obtain ⟨b, hb, hcb⟩ := hgVeb_cof hL0 (hlkG_fixG (hl_one_add hμ)) hcS
    obtain ⟨μ'', hμ'', hbμ⟩ := hlkGS_Bcof hlim hμ.le hb
    have hcμ : c < (hlkGS μ'').B := hcb.trans hbμ
    rw [(hlkGS_ext hμ hμ'' hcμ 0).2] at hg
    exact IH μ'' hμ'' (hμ''.trans hμ) c hcμ σ hσ hσ1 hg

/-! ## The union over all levels -/

/-- **`φ(Ω₁·Ω₁, G+1)`**: the bound of the union over all levels. -/
noncomputable def hlB : Ordinal.{0} := veblen (Om1 * Om1) (gcG 0 + 1)

theorem hl_OO_lt_G (α : Ordinal.{0}) : (Om1 : Ordinal.{0}) * Om1 < gcG α :=
  InE.mul_lt (Low.opow_eq_self_of_SC (gcG_SC α)) (hg_Om1_lt_G α) (hg_Om1_lt_G α)

theorem hl_OO_ne : (Om1 : Ordinal.{0}) * Om1 ≠ 0 := (mul_pos gv_Om1_pos gv_Om1_pos).ne'

theorem hl_G_fixOO : veblen (Om1 * Om1) (gcG 0) = gcG 0 := gn_veb_fix (gcG_SC 0) (hl_OO_lt_G 0)

/-- **Every `hlkGS μ`, `μ < Ω₁`, lies below `φ(Ω₁·Ω₁, G+1)`.** -/
theorem hlB_gt {μ : Ordinal.{0}} (hμ : μ < Om1) : (hlkGS μ).B < hlB := by
  rw [hlkGS_B hμ]; exact hd_veb_left_lt (mul_lt_mul_of_pos_left (hl_one_add hμ) gv_Om1_pos) _

/-- **The bounds `φ(Ω₁·(1+μ), G+1)`, `μ < Ω₁`, are cofinal in `φ(Ω₁·Ω₁, G+1)`.** -/
theorem hlB_cof {c : Ordinal.{0}} (hc : c < hlB) : ∃ μ, μ < Om1 ∧ c < (hlkGS μ).B := by
  obtain ⟨b, hb, hcb⟩ := hgVeb_cof hl_OO_ne hl_G_fixOO hc
  have hb' : b < Om1 * (1 + Om1) := by rwa [one_add_of_omega0_le (omega0_lt_inE gl_Om1_E).le]
  obtain ⟨μ, hμ, hbμ⟩ := hlkGS_Bcof gl_Om1_lim le_rfl hb'
  exact ⟨μ, hμ, hcb.trans hbμ⟩

theorem hlB_lt1 : hlB < gcG 1 := by
  have hG1 := gcG_SC 1
  have hE := Low.opow_eq_self_of_SC hG1
  have hfix : veblen (Om1 * Om1) (gcG 1) = gcG 1 := gn_veb_fix hG1 (hl_OO_lt_G 1)
  have h2 := (isNormal_veblen (Om1 * Om1)).strictMono ((ev_isSuccLimit_of_inE hE).add_one_lt (gcG_lt zero_lt_one))
  unfold hlB; rwa [hfix] at h2

theorem hl_one_lt_OO : (1 : Ordinal.{0}) < Om1 * Om1 :=
  hg_one_lt_Om1.trans_le (le_mul_of_one_le_right' hg_one_lt_Om1.le)

theorem hlB_fix1 : veblen 1 hlB = hlB := veblen_veblen_of_lt hl_one_lt_OO _

theorem hlB_E : InE hlB := gg_veblen_eps hl_OO_ne

theorem hlB_lim : IsSuccLimit hlB := ev_isSuccLimit_of_inE hlB_E

/-- The first level containing `c`. -/
noncomputable def hlN (c : Ordinal.{0}) : Ordinal.{0} := sInf {μ | μ < Om1 ∧ c < (hlkGS μ).B}

theorem hlN_spec {c μ : Ordinal.{0}} (hμ : μ < Om1) (hc : c < (hlkGS μ).B) :
    hlN c ≤ μ ∧ hlN c < Om1 ∧ c < (hlkGS (hlN c)).B := by
  have hne : ({μ | μ < Om1 ∧ c < (hlkGS μ).B} : Set Ordinal.{0}).Nonempty := ⟨μ, hμ, hc⟩
  have hm := csInf_mem hne
  exact ⟨csInf_le' ⟨hμ, hc⟩, hm.1, hm.2⟩

theorem hlN_high {c : Ordinal.{0}} (hc : hlB ≤ c) : hlN c = 0 := by
  unfold hlN
  have he : ({μ | μ < Om1 ∧ c < (hlkGS μ).B} : Set Ordinal.{0}) = ∅ := by
    ext μ
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hμ hcμ
    exact absurd (hcμ.trans (hlB_gt hμ)) (not_lt.2 hc)
  rw [he]; exact Ordinal.sInf_empty

theorem hl_R_eq {c μ : Ordinal.{0}} (hμ : μ < Om1) (hc : c < (hlkGS μ).B) (x : Ordinal.{0}) :
    (hlkGS (hlN c)).R c x = (hlkGS μ).R c x := by
  obtain ⟨h1, -, h3⟩ := hlN_spec hμ hc
  exact (hlkGS_ext' hμ h1 h3 x).1.symm

theorem hl_g_eq {c μ : Ordinal.{0}} (hμ : μ < Om1) (hc : c < (hlkGS μ).B) :
    (hlkGS (hlN c)).g c = (hlkGS μ).g c := by
  obtain ⟨h1, -, h3⟩ := hlN_spec hμ hc
  exact (hlkGS_ext' hμ h1 h3 0).2.symm

theorem hl_R_succ (c x : Ordinal.{0}) : (hlkGS (hlN (c + 1))).R (c + 1) x = (hlkGS (hlN c)).R c x + 1 := by
  rcases lt_or_ge c hlB with h | h
  · obtain ⟨n, hn1, hn⟩ := hlB_cof (hlB_lim.add_one_lt h)
    rw [hl_R_eq hn1 hn, hl_R_eq hn1 ((lt_add_one c).trans hn), (hlkGS n).R_succ]
  · rw [hlN_high h, hlN_high (h.trans (le_self_add (a := c) (b := 1))), (hlkGS 0).R_succ]

theorem hl_g_le_succ (c : Ordinal.{0}) : (hlkGS (hlN c)).g c ≤ (hlkGS (hlN (c + 1))).g (c + 1) := by
  rcases lt_or_ge c hlB with h | h
  · obtain ⟨n, hn1, hn⟩ := hlB_cof (hlB_lim.add_one_lt h)
    rw [hl_g_eq hn1 hn, hl_g_eq hn1 ((lt_add_one c).trans hn)]; exact (hlkGS n).g_le_succ c
  · rw [hlN_high h, hlN_high (h.trans (le_self_add (a := c) (b := 1)))]; exact (hlkGS 0).g_le_succ c

/-- **The base reading of the union**: `φ(x·x, Γ_{x+1}+1)`. -/
noncomputable def hlBR (x : Ordinal.{0}) : Ordinal.{0} := veblen (x * x) (lgG x + 1)

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem hl_sq_lt : x * x < lgG x :=
  InE.mul_lt (lgG_facts hx hx1).2.2.2.1 (lgG_facts hx hx1).2.1 (lgG_facts hx hx1).2.1

theorem hl_sq_one : (1 : Ordinal.{0}) ≤ x * x :=
  (one_lt_omega0.trans (omega0_lt_inE hx)).le.trans (hl_lt_sq hx).le

theorem hl_BR_eq : hlBR x = hdNx (x * x) (lgG x) :=
  (hdNx_fixP (hjG_fix hx hx1 (hl_sq_one hx hx1) (hl_sq_lt hx hx1))).symm

theorem hl_BR_lt1 : hlBR x < gq 1 x := by
  rw [hl_BR_eq hx hx1]; exact hjG_lt1 hx hx1 (hl_sq_one hx hx1) (hl_sq_lt hx hx1)

theorem hl_x_lt_BR : x < hlBR x := (lgG_facts hx hx1).2.1.trans ((lt_add_one _).trans_le (right_le_veblen _ _))

theorem hl_BR_fix1 : veblen 1 (hlBR x) = hlBR x :=
  veblen_veblen_of_lt ((one_lt_omega0.trans (omega0_lt_inE hx)).trans (hl_lt_sq hx)) _

theorem hl_BR_fix2 : veblen 2 (hlBR x) = hlBR x :=
  veblen_veblen_of_lt ((show (2 : Ordinal.{0}) < ω from by exact_mod_cast natCast_lt_omega0 2).trans
    ((omega0_lt_inE hx).trans (hl_lt_sq hx))) _

/-- **The bound field of every `hlkGS μ` lies below `φ(x·x, Γ_{x+1}+1)`.** -/
theorem hl_Z_le {μ : Ordinal.{0}} (hμ : μ < Om1) : (hlkGS μ).Z x ≤ hlBR x := by
  rw [(hlkGS_shape hμ).2.2.2.1 x hx hx1]
  split_ifs with h
  · refine (hb_evZ_lt_fix2 (hl_BR_fix2 hx hx1) ?_).le
    show veblen ((hlkPk μ).Λ.l x + 0) (lgG x + 1) < hlBR x
    rw [add_zero]
    exact hd_veb_left_lt (le_self_add.trans_lt ((hlkPk μ).Λ.l_lt2 x hx hx1 (max_lt_iff.1 h).1)) _
  · rw [hlGW_Zo_low _ (fun h' => h (max_lt h' hx.pos)), max_eq_right (omega0_lt_inE hx).le]; exact le_rfl

/-- **The gate of `hlkGS μ` is below `x` for `μ < x`.** -/
theorem hl_γ_lt {μ : Ordinal.{0}} (hμ : μ < x) : (hlkGS μ).γ < x :=
  (hlkGS_γ_le (hμ.trans hx1)).trans_lt ((inE_indec hx).add_lt (one_lt_omega0.trans (omega0_lt_inE hx)) hμ)

/-- **The base reading of `hlkGS μ` at `μ < x`**: `φ(x·(1+μ), Γ_{x+1}+1)`. -/
theorem hl_b_eq {μ : Ordinal.{0}} (hμ : μ < x) : (hlkGS μ).b x = hdNx (x * (1 + μ)) (lgG x) := by
  have hμ1 : μ < Om1 := hμ.trans hx1
  have hg : (hlkPk μ).Λ.g < x := by rw [← hlkGS_γ hμ1]; exact hl_γ_lt hx hx1 hμ
  have h1x : 1 + μ < x := (inE_indec hx).add_lt (one_lt_omega0.trans (omega0_lt_inE hx)) hμ
  rw [(hlkGS_shape hμ1).2.2.1 x hx hx1 (max_lt hg hx.pos)]
  show veblen ((hlkPk μ).Λ.l x + 0) (lgG x + 1) = _
  rw [hlkPk_l hμ1 hg, add_zero, hlkG_b_eq le_self_add h1x hx hx1]

/-- **The base reading of `hlkGS μ` lies below `φ(x·x, Γ_{x+1}+1)`** (`μ < x`). -/
theorem hl_b_lt {μ : Ordinal.{0}} (hμ : μ < x) : (hlkGS μ).b x < hlBR x := by
  have h1x : 1 + μ < x := (inE_indec hx).add_lt (one_lt_omega0.trans (omega0_lt_inE hx)) hμ
  rw [hl_b_eq hx hx1 hμ, ← hlkG_b_eq le_self_add h1x hx hx1]
  exact hd_veb_left_lt (mul_lt_mul_of_pos_left h1x hx.pos) _

end Base

/-- **Lemma EXACT for `φ(ρ·ρ, Γ_{ρ+1}+1)`** (`Exact.pi_sq`). -/
theorem hl_BR_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) : hlBR ρ ∈ TB ρ σ ∧ pi σ ρ (hlBR ρ) = hlBR σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  rw [hl_BR_eq hB.2.1 hρ1, hl_BR_eq hB.1 hσ1]
  exact hjG_S_pi hB (pi_sq hB) (hl_sq_one hB.2.1 hρ1) (hl_sq_lt hB.2.1 hρ1) (hl_sq_one hB.1 hσ1)
    (hl_sq_lt hB.1 hσ1)

/-- **A code of the union with gate below an `ε`-number `σ` lies in `hlkGS μ`, `μ < σ`.** -/
theorem hl_small' {c σ : Ordinal.{0}} (hc : c < hlB) (hσ : InE σ) (hσ1 : σ < Om1)
    (hg : (hlkGS (hlN c)).g c < σ) : ∃ μ, μ < σ ∧ c < (hlkGS μ).B := by
  obtain ⟨n, hn1, hn⟩ := hlB_cof hc
  rw [hl_g_eq hn1 hn] at hg
  exact hl_small n hn1 c hn σ hσ hσ1 hg

theorem hl_OO_mem (S : InaccSeq.{0}) (a b : Ordinal.{0}) : (Om1 : Ordinal.{0}) * Om1 ∈ S.CSet a b := by
  have e : (Om1 : Ordinal.{0}) * Om1 = veblen 0 (Om 1 + Om 1) := by
    rw [veblen_zero_apply, opow_add, show ω ^ Om (1 : Ordinal.{0}) = Om 1 from hj_Om_E, Br.Om1_eq]
  rw [e]
  exact CSet.phi_mem (CSet.zero_mem _ _)
    (CSet.add_mem (CSet.Om_mem (CSet.one_mem _ _)) (CSet.Om_mem (CSet.one_mem _ _)))

/-- **THE UNION OVER ALL LEVELS `Ω₁·(1+μ)`, `μ < Ω₁`**: a gated digit system (`HgVD`) with the bound
`φ(Ω₁·Ω₁, G+1)`, the base gate `0`, the base reading `φ(x·x, Γ_{x+1}+1)` (the level `Ω₁·Ω₁` read as `x·x`) and the
bound field `evZ(φ(x·x, Γ_{x+1}+1)) < Γ_{x+2}`. -/
noncomputable def hlU : HgVD where
  B := hlB
  γ := 0
  γ_lt := gv_Om1_pos
  γ_cl := fun _ hZ _ _ => hZ.1
  γ_G := fun _ => rfl
  R := fun c x => (hlkGS (hlN c)).R c x
  g := fun c => (hlkGS (hlN c)).g c
  b := hlBR
  ba := hlBR
  ix := hlB
  Z := fun x => evZ (hlBR x)
  B_E := hlB_E
  G_le := (lt_add_one _).le.trans (right_le_veblen _ _)
  B_lt1 := hlB_lt1
  B_ix := hlB_fix1.symm
  Z_fix := fun _ _ _ => epsilon_evZ _
  Z_G1 := fun x hx hx1 => gw_evZ_lt1 hx hx1 (hl_BR_lt1 hx hx1)
  ix_mem := fun S a b ha _ => CSet.phi_mem (hl_OO_mem S a b) (CSet.succ_mem (gmS_G0_mem S ha))
  g_lt := fun c hc => by
    obtain ⟨n, hn1, hn⟩ := hlB_cof hc
    rw [hl_g_eq hn1 hn]; exact (hlkGS n).g_lt c hn
  g_zero := by rw [hl_g_eq gv_Om1_pos (hlkGS 0).B_pos]; exact (hlkGS 0).g_zero
  g_nat := fun k => by rw [hl_g_eq gv_Om1_pos ((hlkGS 0).nat_lt_B k)]; exact (hlkGS 0).g_nat k
  g_E := by rw [hl_g_eq gv_Om1_pos (hlkGS 0).E_lt_B]; exact (hlkGS 0).g_E
  g_lowE := fun c hc => by rw [hl_g_eq gv_Om1_pos (hc.trans (hlkGS 0).E_lt_B)]; exact (hlkGS 0).g_lowE c hc
  g_G0 := fun h => by
    obtain ⟨n, hn1, hn⟩ := hlB_cof h
    rw [hl_g_eq hn1 hn]; exact (hlkGS n).g_G0 hn
  g_add := fun Z hZ hωZ x y hxy hgx hgy => by
    obtain ⟨n, hn1, hn⟩ := hlB_cof hxy
    have hx : x < (hlkGS n).B := lt_of_le_of_lt le_self_add hn
    have hy : y < (hlkGS n).B := lt_of_le_of_lt le_add_self hn
    show (hlkGS (hlN (x + y))).g (x + y) < Z
    rw [hl_g_eq hn1 hn]; rw [hl_g_eq hn1 hx] at hgx; rw [hl_g_eq hn1 hy] at hgy
    exact (hlkGS n).g_add Z hZ hωZ x y hn hgx hgy
  g_opow := fun Z hZw hωZ y hy hg => by
    obtain ⟨n, hn1, hn⟩ := hlB_cof hy
    have hy' : y < (hlkGS n).B := lt_of_le_of_lt (right_le_opow y one_lt_omega0) hn
    show (hlkGS (hlN (ω ^ y))).g (ω ^ y) < Z
    rw [hl_g_eq hn1 hn]; rw [hl_g_eq hn1 hy'] at hg
    exact (hlkGS n).g_opow Z hZw hωZ y hn hg
  code_gate := fun Z hZ1 hZ0 hZa hZp At hAt c hc hcB => by
    obtain ⟨n, hn1, hn⟩ := hlB_cof hcB
    show (hlkGS (hlN c)).g c < Z
    rw [hl_g_eq hn1 hn]
    exact (hlkGS n).code_gate Z hZ1 hZ0 hZa hZp At (fun s hs => (hAt s hs).imp_right
      (fun h => (hlB_gt hn1).le.trans h)) c hc hn
  g_succ := fun Z hZ c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hlB_cof hc
    have hc' : c < (hlkGS n).B := (lt_add_one c).trans hn
    show (hlkGS (hlN (c + 1))).g (c + 1) < Z
    rw [hl_g_eq hn1 hn]; rw [hl_g_eq hn1 hc'] at hg
    exact (hlkGS n).g_succ Z hZ c hn hg
  g_le_succ := hl_g_le_succ
  mem := fun S a b ha c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hlB_cof hc
    rw [hl_g_eq hn1 hn] at hg
    exact (hlkGS n).mem S a b ha c hn hg
  R_zero := fun x => by rw [hl_R_eq gv_Om1_pos (hlkGS 0).B_pos]; exact (hlkGS 0).R_zero x
  R_nat := fun k x => by rw [hl_R_eq gv_Om1_pos ((hlkGS 0).nat_lt_B k)]; exact (hlkGS 0).R_nat k x
  R_E := fun x => by rw [hl_R_eq gv_Om1_pos (hlkGS 0).E_lt_B]; exact (hlkGS 0).R_E x
  R_succ := hl_R_succ
  R_pos := fun x hx hx1 c hc0 hc hg => by
    obtain ⟨n, hn1, hn⟩ := hlB_cof hc
    show 0 < (hlkGS (hlN c)).R c x
    rw [hl_R_eq hn1 hn]; rw [hl_g_eq hn1 hn] at hg
    exact (hlkGS n).R_pos x hx hx1 c hc0 hn hg
  R_omega := fun x hx hx1 c hω hc hg => by
    obtain ⟨n, hn1, hn⟩ := hlB_cof hc
    show ω ≤ (hlkGS (hlN c)).R c x
    rw [hl_R_eq hn1 hn]; rw [hl_g_eq hn1 hn] at hg
    exact (hlkGS n).R_omega x hx hx1 c hω hn hg
  R_lt_b := fun x hx hx1 _ c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hlB_cof hc
    show (hlkGS (hlN c)).R c x < hlBR x
    rw [hl_R_eq hn1 hn]; rw [hl_g_eq hn1 hn] at hg
    exact ((hlkGS n).R_lt_Z x hx hx1 c hn hg).trans_le (hl_Z_le hx hx1 hn1)
  R_lt_Z := fun x hx hx1 c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hlB_cof hc
    show (hlkGS (hlN c)).R c x < evZ (hlBR x)
    rw [hl_R_eq hn1 hn]; rw [hl_g_eq hn1 hn] at hg
    exact (((hlkGS n).R_lt_Z x hx hx1 c hn hg).trans_le (hl_Z_le hx hx1 hn1)).trans (lt_evZ _)
  mono := fun x hx hx1 c hc d hdc hgc hgd => by
    obtain ⟨n, hn1, hn⟩ := hlB_cof hc
    have hd : d < (hlkGS n).B := hdc.trans hn
    show (hlkGS (hlN d)).R d x < (hlkGS (hlN c)).R c x
    rw [hl_R_eq hn1 hn, hl_R_eq hn1 hd]; rw [hl_g_eq hn1 hn] at hgc; rw [hl_g_eq hn1 hd] at hgd
    exact (hlkGS n).mono x hx hx1 c hn d hdc hgc hgd
  cof := fun x hx hx1 c hc hg ν hν => by
    obtain ⟨n, hn1, hn⟩ := hlB_cof hc
    rw [hl_R_eq hn1 hn] at hν; rw [hl_g_eq hn1 hn] at hg
    obtain ⟨d, hdc, hgd, hνd⟩ := (hlkGS n).cof x hx hx1 c hn hg ν hν
    have hd : d < (hlkGS n).B := hdc.trans hn
    exact ⟨d, hdc, by show (hlkGS (hlN d)).g d < x; rw [hl_g_eq hn1 hd]; exact hgd,
      by show ν ≤ (hlkGS (hlN d)).R d x; rw [hl_R_eq hn1 hd]; exact hνd⟩
  b_cof := fun x hx hx1 _ ν hν => by
    have hfix : veblen (x * x) (lgG x) = lgG x := hjG_fix hx hx1 (hl_sq_one hx hx1) (hl_sq_lt hx hx1)
    obtain ⟨b, hb, hνb⟩ := hgVeb_cof (hl_sq_one hx hx1 |> fun h => (zero_lt_one.trans_le h).ne') hfix hν
    have hdiv : b / x < x := (lt_mul_iff_div_lt hx.pos.ne').1 hb
    have hlx := ev_isSuccLimit_of_inE hx
    have hμ : b / x + 1 + 1 < x := hlx.add_one_lt (hlx.add_one_lt hdiv)
    have hμ1 : b / x + 1 + 1 < Om1 := hμ.trans hx1
    have hb1 : b + 1 < x * (1 + (b / x + 1 + 1)) := by
      calc b + 1 ≤ x * (b / x) + x := Order.add_one_le_of_lt (lt_mul_div_add b hx.pos.ne')
      _ = x * (b / x + 1) := by rw [mul_add_one]
      _ < x * (b / x + 1 + 1) := mul_lt_mul_of_pos_left (lt_add_one _) hx.pos
      _ ≤ x * (1 + (b / x + 1 + 1)) := mul_le_mul_left' le_add_self _
    have hνb' : ν < (hlkGS (b / x + 1 + 1)).b x := by
      rw [hl_b_eq hx hx1 hμ]; exact hνb.trans (hdN_lt_Nx hb1)
    obtain ⟨d, hd, hgd, hνd⟩ := (hlkGS (b / x + 1 + 1)).b_cof x hx hx1 (hl_γ_lt hx hx1 hμ) ν hνb'
    exact ⟨d, hd.trans (hlB_gt hμ1), by show (hlkGS (hlN d)).g d < x; rw [hl_g_eq hμ1 hd]; exact hgd,
      by show ν < (hlkGS (hlN d)).R d x; rw [hl_R_eq hμ1 hd]; exact hνd⟩
  b_E := fun x hx hx1 _ => gg_veblen_eps (zero_lt_one.trans_le (hl_sq_one hx hx1)).ne'
  x_lt_b := fun x hx hx1 _ => hl_x_lt_BR hx hx1
  b_eN := fun x hx hx1 _ => gz_eN_fix hx hx1 (hl_BR_fix1 hx hx1) (hl_x_lt_BR hx hx1) (hl_BR_lt1 hx hx1)
  ba_lt := fun x hx hx1 _ => hl_BR_lt1 hx hx1
  b_Z := fun _ _ _ _ => go_eN_lt_evZ (lt_evZ _)
  b_pi := fun _ _ hB _ => hl_BR_pi hB
  ba_pi := fun _ _ hB _ => hl_BR_pi hB
  ex := fun σ ρ hB c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hlB_cof hc
    show (hlkGS (hlN c)).R c ρ ∈ TB ρ σ ∧ pi σ ρ ((hlkGS (hlN c)).R c ρ) = (hlkGS (hlN c)).R c σ
    rw [hl_R_eq hn1 hn, hl_R_eq hn1 hn]; rw [hl_g_eq hn1 hn] at hg
    exact (hlkGS n).ex σ ρ hB c hn hg
  dig := fun σ ρ hB _ d hd hg P P' hat => by
    have hσ1 : σ < Om1 := hB.2.2.1.trans hB.2.2.2
    obtain ⟨μ, hμσ, hdμ⟩ := hl_small' hd hB.1 hσ1 hg
    have hμ1 : μ < Om1 := hμσ.trans hσ1
    show ω ^ P * (hlkGS (hlN d)).R d ρ ∈ TB ρ σ ∧
      pi σ ρ (ω ^ P * (hlkGS (hlN d)).R d ρ) = ω ^ P' * (hlkGS (hlN d)).R d σ
    rw [hl_R_eq hμ1 hdμ, hl_R_eq hμ1 hdμ]; rw [hl_g_eq hμ1 hdμ] at hg
    exact (hlkGS μ).dig σ ρ hB (hl_γ_lt hB.1 hσ1 hμσ) d hdμ hg P P' (fun β hβ hβe =>
      hat β hβ (hβe.trans (hl_b_lt hB.2.1 hB.2.2.2 (hμσ.trans hB.2.2.1))))
  ld := fun c hl hc => by
    obtain ⟨n, hn1, hn⟩ := hlB_cof hc
    obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := (hlkGS n).ld c hl hn
    have hcpn : cp < (hlkGS n).B := hcp.trans hn
    refine ⟨cp, lp, T, hcp, ?_, fun x hx hx1 hg => ?_, fun σ ρ hB hg => hex σ ρ hB ?_⟩
    · show (hlkGS (hlN cp)).g cp ≤ (hlkGS (hlN c)).g c
      rw [hl_g_eq hn1 hn, hl_g_eq hn1 hcpn]; exact hgcp
    · have hg' : (hlkGS n).g c < x := by rw [← hl_g_eq hn1 hn]; exact hg
      show (hlkGS (hlN c)).R c x = _ ∧ _
      rw [hl_R_eq hn1 hn, hl_R_eq hn1 hcpn]
      exact hdec x hx hx1 hg'
    · rw [← hl_g_eq hn1 hn]; exact hg

theorem hlU_B : hlU.B = veblen (Om1 * Om1) (gcG 0 + 1) := rfl

theorem hlU_γ : hlU.γ = 0 := rfl

theorem hlU_b (x : Ordinal.{0}) : hlU.b x = veblen (x * x) (lgG x + 1) := rfl

/-- **The union extends every `hlkGS μ`, `μ < Ω₁`** (readings). -/
theorem hlU_R {μ c : Ordinal.{0}} (hμ : μ < Om1) (hc : c < (hlkGS μ).B) (x : Ordinal.{0}) :
    hlU.R c x = (hlkGS μ).R c x := hl_R_eq hμ hc x

/-- **The union extends every `hlkGS μ`, `μ < Ω₁`** (gates). -/
theorem hlU_g {μ c : Ordinal.{0}} (hμ : μ < Om1) (hc : c < (hlkGS μ).B) : hlU.g c = (hlkGS μ).g c := hl_g_eq hμ hc

/-! ## The location -/

section Loc

variable (S : InaccSeq.{0})

theorem hlU_γK : hlU.γ < Td.tdK S := hg_K_pos S

/-- **`φ(Ω₁·Ω₁, G+1)` IS LOCATED**: `Λ⁺ = ι(Γ(φ(Ω₁·Ω₁, G+1))·ω)`, `P(…) < L(0)` (UNCONDITIONAL). -/
theorem hlU_loc : ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG hlU.B * ω) ∧
    upsilon (xtB1 X) = Pv S (gcG hlU.B * ω) ∧ Pv S (gcG hlU.B * ω) < Nc.ncL S 0 :=
  hgV_locD hlU S (hlU_γK S)

/-- **Theorem BLK^O below `P(Γ(φ(Ω₁·Ω₁, G+1))·ω)`, with the exact reaches** (UNCONDITIONAL). -/
theorem hlU_blk :
    let X := gsX hlU.step.toRS _ hlU.E_lt_B.le hlU.B_lt_NB S (hgV_locD_g hlU S (hlU_γK S))
    (∀ c' d, c' < d → d < upsilon (xtB1 X) → (le2 c' d ↔ ∃ μ, ∃ j : ℕ, (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 X ∧
        c' = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧ d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 X →
      (∀ c' < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c' g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec X l)) ∧
    (∀ α < upsilon (xtB1 X), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  hgV_locD_blk hlU S (hlU_γK S)

/-- **ENUM-REACH at every range restart below `ι(Γ(φ(Ω₁·Ω₁, G+1))·ω)`, fixed points included** (UNCONDITIONAL). -/
theorem hlU_enum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG hlU.B * ω)) :
    CdUpper S l ∧ CdLower S l := hgV_locD_enum hlU S (hlU_γK S) hr hl

/-- **CapV at every range restart below `ι(Γ(φ(Ω₁·Ω₁, G+1))·ω)`** (UNCONDITIONAL). -/
theorem hlU_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG hlU.B * ω)) : CdCapV S l :=
  hgV_locD_capV hlU S (hlU_γK S) hr hl

/-- **THE ROAD**: UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ(φ(Ω₁·Ω₁, G+1))·ω)` (CapV also `υ_λ < L(ω)`), (CL),
EQ, TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem hlU_road (hU : ∀ l, CdRange S l → iota S (gcG hlU.B * ω) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG hlU.B * ω) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG hlU.B * ω) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  gv_road_of S _ (fun _ hr h => hlU_enum S hr h) (fun _ hr h => hlU_capV S hr h) hU hL hV hC hEQ hrest hB2

/-- **`Γ(φ(Ω₁·Ω₁, G+1)) < Ω₂`.** -/
theorem hlB_lt_Om2 : gcG hlB < Om (1 + 1) := by
  have hBE : InE Tf.tfBG := Low.opow_eq_self_of_SC Tf.tfBG_SC
  have hO : (Om1 : Ordinal.{0}) < Tf.tfBG := Tf.tfBG_gt
  have h1 : (1 : Ordinal.{0}) < Tf.tfBG := one_lt_omega0.trans (omega0_lt_inE hBE)
  have hG1 : gcG 1 < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) h1)
  have h2 : gcG hlB < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) (hlB_lt1.trans hG1))
  exact h2.trans Tf.tfBG_lt_Om2

/-- **The order of the frontiers**: `φ(Ω₁·K, G+1) < φ(Ω₁·Ω₁, G+1)`, `ι(Γ(φ(Ω₁·K, G+1))) ≤ ι(Γ(φ(Ω₁·Ω₁, G+1))·ω)
≤ ι(Ω₂)` and `P(Γ(φ(Ω₁·Ω₁, G+1))·ω) ≤ P(Ω₂) < L(0)`. -/
theorem hlU_fr_order :
    hlkGE S < hlB ∧ iota S (gcG (hlkGE S)) ≤ iota S (gcG hlB * ω) ∧
      iota S (gcG hlB * ω) ≤ iota S (Om (1 + 1)) ∧
      Pv S (gcG hlB * ω) ≤ Pv S (Om (1 + 1)) ∧ Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have hlt : hlkGE S < hlB := by
    unfold hlkGE hlB
    exact hd_veb_left_lt (mul_lt_mul_of_pos_left (hlK_lt S) gv_Om1_pos) _
  have hV : InE (gcG hlB) := Low.opow_eq_self_of_SC (gcG_SC _)
  have hVw : gcG hlB * ω < Om (1 + 1) := by
    have hO2 : InE (Om (1 + 1) : Ordinal.{0}) := Low.opow_eq_self_of_SC Ld.ldOm2_SC
    exact InE.mul_lt hO2 hlB_lt_Om2 ((omega0_lt_inE hO2))
  refine ⟨hlt, iota_mono _ _ ((gcG_lt hlt).trans_le (le_mul_of_one_le_right' one_lt_omega0.le)).le,
    iota_mono _ _ hVw.le, Nm.Pv_mono hVw.le, ga_Pv_lt_L0 S le_rfl⟩

/-- **NON-VACUITY (relative)**: the hypotheses UPPER, LOWER, CapV of `hlU_road` (asked from `ι(Γ(φ(Ω₁·Ω₁, G+1))·ω)`
on) are EQUIVALENT to those of the round-104 road `Hk.hkGE_road` (asked from `ι(Γ(φ(Ω₁·ε₀, G+1)))` on): the
restarts in between are settled unconditionally (`hlU_enum`, `hlU_capV`). -/
theorem hlU_hyp_iff :
    ((∀ l, CdRange S l → iota S (gcG hkGE) ≤ l → CdUpper S l) ↔
      (∀ l, CdRange S l → iota S (gcG hlU.B * ω) ≤ l → CdUpper S l)) ∧
    ((∀ l, CdRange S l → iota S (gcG hkGE) ≤ l → CdLower S l) ↔
      (∀ l, CdRange S l → iota S (gcG hlU.B * ω) ≤ l → CdLower S l)) ∧
    ((∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG hkGE) ≤ l → CdCapV S l) ↔
      (∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG hlU.B * ω) ≤ l → CdCapV S l)) := by
  have hle : iota S (gcG hkGE) ≤ iota S (gcG hlU.B * ω) :=
    (hlkGE_fr_order S).2.1.trans (hlU_fr_order S).2.1
  refine ⟨⟨fun h l hr hl => h l hr (hle.trans hl), fun h l hr hl => ?_⟩,
    ⟨fun h l hr hl => h l hr (hle.trans hl), fun h l hr hl => ?_⟩,
    ⟨fun h l hr hu hl => h l hr hu (hle.trans hl), fun h l hr hu hl => ?_⟩⟩
  · rcases lt_or_ge l (iota S (gcG hlU.B * ω)) with h' | h'
    · exact (hlU_enum S hr h').1
    · exact h l hr h'
  · rcases lt_or_ge l (iota S (gcG hlU.B * ω)) with h' | h'
    · exact (hlU_enum S hr h').2
    · exact h l hr h'
  · rcases lt_or_ge l (iota S (gcG hlU.B * ω)) with h' | h'
    · exact hlU_capV S hr h'
    · exact h l hr hu h'

end Loc

end Googology.Trans.PoR.InaccPsi.R2.Hl

import Googology.Trans.PoR.InaccPsi.R2.HnQG

/-!
# HnQU: THE STEP OF THE LEVEL `Ω₁·Ω₁ + 0` OVER EVERY PSEUDO-BASE: THE PACKAGE `hnPkSq`

PORT of the union `Hl.hlU` (over `G`) to an arbitrary pseudo-base `Q : HnVQ hnSqLv 0` with a start `U`: the union of
all `hnQGS Q U hU μ`, `μ < Ω₁`, is a gated digit system with the bound `φ(Ω₁·Ω₁, F+1)`, the base gate `Q.γ`, the base
reading `φ(x·x, F(x)+1)` and the bound field `evZ(φ(x·x, F(x)+1))` above `Q.γ`, `Q.Zo` below.  What differs from
`Hl.hlU`: the point `Q.F` in place of `G`, the gate `Q.γ` in place of `0` (so SMALL, `R_lt_b`, `R_lt_Z` go through the
member `μ < x`), and the specification `HnVSpec` of level `Ω₁·Ω₁ + 0` is proved, so the union is the step of a
package.

* `hnQGS_Bcof`, `hnQ_small` (**SMALL**: a code of `hnQGS μ` with gate below an `ε`-number `σ` lies in some
  `hnQGS μ'`, `μ' < σ`; via `Hl.hlwU_highR`, `Hl.hlkPk_g_lt`);
* `hnQU Q U hU` (**THE UNION OVER ALL LEVELS `Ω₁·(1+μ)` AT `Q`**), `hnQU_spec` (**its specification at level
  `Ω₁·Ω₁ + 0`**);
* `hnPkSq` (**THE PACKAGE AT THE LEVEL `Ω₁·Ω₁`**).

No new axiom.  New definitions: `hnQN`, `hnQU`, `hnSqSt0`, `hnPkSq`.
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

section U

variable (Q : HnVQ hnSqLv 0) (U : HgVD) (hU : HgSStart (hnVPB Q) U)

theorem hnQGS_Bcof {l b : Ordinal.{0}} (hl : IsSuccLimit l) (hle : l ≤ Om1) (hb : b < Om1 * (1 + l)) :
    ∃ μ, μ < l ∧ hcN b Q.F < (hnQGS Q U hU μ).B := by
  rw [one_add_of_omega0_le (omega0_le_of_isSuccLimit hl)] at hb
  have hdiv : b / Om1 < l := (lt_mul_iff_div_lt gv_Om1_pos.ne').1 hb
  have hμ : b / Om1 + 1 + 1 < l := hl.add_one_lt (hl.add_one_lt hdiv)
  refine ⟨_, hμ, ?_⟩
  rw [hnQGS_B Q U hU (hμ.trans_le hle), hnq_B_eq Q (hl_one_add (hμ.trans_le hle))]
  refine hdN_lt_Nx ?_
  calc b + 1 ≤ Om1 * (b / Om1) + Om1 := Order.add_one_le_of_lt (lt_mul_div_add b gv_Om1_pos.ne')
  _ = Om1 * (b / Om1 + 1) := by rw [mul_add_one]
  _ < Om1 * (b / Om1 + 1 + 1) := mul_lt_mul_of_pos_left (lt_add_one _) gv_Om1_pos
  _ ≤ Om1 * (1 + (b / Om1 + 1 + 1)) := mul_le_mul_left' le_add_self _

/-- **SMALL**: a code of `hnQGS μ` with gate below an `ε`-number `σ` lies in some `hnQGS μ'`, `μ' < σ`. -/
theorem hnQ_small : ∀ μ, μ < Om1 → ∀ c, c < (hnQGS Q U hU μ).B → ∀ σ, InE σ → σ < Om1 →
    (hnQGS Q U hU μ).g c < σ → ∃ μ', μ' < σ ∧ c < (hnQGS Q U hU μ').B := by
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
    by_cases hcν : c < (hnQGS Q U hU ν).B
    · rw [(hnQGS_ext Q U hU hμ (lt_add_one ν) hcν 0).2] at hg
      exact IH ν (lt_add_one ν) hν1 c hcν σ hσ hσ1 hg
    · exfalso
      obtain ⟨⟨hsh, -⟩, -⟩ := hnQGS_inv Q U hU ν hν1
      have e : hnQGS Q U hU (ν + 1) =
          hlwU (hnQW Q (hlkPk ν).Λ) (hlkPk ν).St0 (hlkPk ν).h0 (hnQGS Q U hU ν) hsh := by
        rw [hnQGS_succ]; unfold hnQSucc; rw [dif_pos hsh]
      rw [e] at hc hg
      have h := hlwU_highR _ _ _ _ hsh (not_lt.1 hcν) hc hσ hσ1 hg
      exact hμσ ((ev_isSuccLimit_of_inE hσ).add_one_lt
        (hlkPk_g_lt ν hν1 σ hσ ((le_max_right _ _).trans_lt h)))
  · have hcS : c < veblen (Om1 * (1 + μ)) (Q.F + 1) := by rw [← hnQGS_B Q U hU hμ]; exact hc
    have hL0 : (Om1 : Ordinal.{0}) * (1 + μ) ≠ 0 := hkG_ne le_self_add
    obtain ⟨b, hb, hcb⟩ := hgVeb_cof hL0 (hnq_FM Q (hl_one_add hμ)) hcS
    obtain ⟨μ'', hμ'', hbμ⟩ := hnQGS_Bcof Q U hU hlim hμ.le hb
    have hcμ : c < (hnQGS Q U hU μ'').B := hcb.trans hbμ
    rw [(hnQGS_ext Q U hU hμ hμ'' hcμ 0).2] at hg
    exact IH μ'' hμ'' (hμ''.trans hμ) c hcμ σ hσ hσ1 hg

/-! ## The union over all levels at `Q` -/

theorem hnq_OO : hnSqLv.L + 0 = Om1 * Om1 := by rw [add_zero]; rfl

theorem hnq_OO_ne : hnSqLv.L + 0 ≠ 0 := by rw [hnq_OO]; exact hl_OO_ne

/-- **Every `hnQGS μ`, `μ < Ω₁`, lies below `hdNx (Ω₁·Ω₁) F`.** -/
theorem hnQB_gt {μ : Ordinal.{0}} (hμ : μ < Om1) : (hnQGS Q U hU μ).B < hdNx (hnSqLv.L + 0) Q.F := by
  rw [hnQGS_B Q U hU hμ, hnq_B_eq Q (hl_one_add hμ)]
  have := hnq_B0_lt Q (hlkPk μ).Λ
  rwa [hlkPk_L hμ, add_zero] at this

theorem hnQB_cof {c : Ordinal.{0}} (hc : c < hdNx (hnSqLv.L + 0) Q.F) :
    ∃ μ, μ < Om1 ∧ c < (hnQGS Q U hU μ).B := by
  obtain ⟨b, hb, hcb⟩ := hjw_Nx_cof hnq_OO_ne Q.F_P hc
  rw [hnq_OO] at hb
  have hb' : b < Om1 * (1 + Om1) := by rwa [one_add_of_omega0_le (omega0_lt_inE gl_Om1_E).le]
  obtain ⟨μ, hμ, hbμ⟩ := hnQGS_Bcof Q U hU gl_Om1_lim le_rfl hb'
  exact ⟨μ, hμ, hcb.trans hbμ⟩

theorem hnQB_E : InE (hdNx (hnSqLv.L + 0) Q.F) := by unfold hdNx; exact gg_veblen_eps hnq_OO_ne

theorem hnQB_lim : IsSuccLimit (hdNx (hnSqLv.L + 0) Q.F) := ev_isSuccLimit_of_inE (hnQB_E Q)

theorem hnq_one_OO : (1 : Ordinal.{0}) < hnSqLv.L + 0 := by rw [hnq_OO]; exact hl_one_lt_OO

/-- The first level at `Q` containing `c`. -/
noncomputable def hnQN (c : Ordinal.{0}) : Ordinal.{0} := sInf {μ | μ < Om1 ∧ c < (hnQGS Q U hU μ).B}

theorem hnQN_spec {c μ : Ordinal.{0}} (hμ : μ < Om1) (hc : c < (hnQGS Q U hU μ).B) :
    hnQN Q U hU c ≤ μ ∧ hnQN Q U hU c < Om1 ∧ c < (hnQGS Q U hU (hnQN Q U hU c)).B := by
  have hne : ({μ | μ < Om1 ∧ c < (hnQGS Q U hU μ).B} : Set Ordinal.{0}).Nonempty := ⟨μ, hμ, hc⟩
  have hm := csInf_mem hne
  exact ⟨csInf_le' ⟨hμ, hc⟩, hm.1, hm.2⟩

theorem hnQN_high {c : Ordinal.{0}} (hc : hdNx (hnSqLv.L + 0) Q.F ≤ c) : hnQN Q U hU c = 0 := by
  unfold hnQN
  have he : ({μ | μ < Om1 ∧ c < (hnQGS Q U hU μ).B} : Set Ordinal.{0}) = ∅ := by
    ext μ
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hμ hcμ
    exact absurd (hcμ.trans (hnQB_gt Q U hU hμ)) (not_lt.2 hc)
  rw [he]; exact Ordinal.sInf_empty

theorem hnq_R_eq {c μ : Ordinal.{0}} (hμ : μ < Om1) (hc : c < (hnQGS Q U hU μ).B) (x : Ordinal.{0}) :
    (hnQGS Q U hU (hnQN Q U hU c)).R c x = (hnQGS Q U hU μ).R c x := by
  obtain ⟨h1, -, h3⟩ := hnQN_spec Q U hU hμ hc
  exact (hnQGS_ext' Q U hU hμ h1 h3 x).1.symm

theorem hnq_g_eq {c μ : Ordinal.{0}} (hμ : μ < Om1) (hc : c < (hnQGS Q U hU μ).B) :
    (hnQGS Q U hU (hnQN Q U hU c)).g c = (hnQGS Q U hU μ).g c := by
  obtain ⟨h1, -, h3⟩ := hnQN_spec Q U hU hμ hc
  exact (hnQGS_ext' Q U hU hμ h1 h3 0).2.symm

theorem hnq_R_succ (c x : Ordinal.{0}) :
    (hnQGS Q U hU (hnQN Q U hU (c + 1))).R (c + 1) x = (hnQGS Q U hU (hnQN Q U hU c)).R c x + 1 := by
  rcases lt_or_ge c (hdNx (hnSqLv.L + 0) Q.F) with h | h
  · obtain ⟨n, hn1, hn⟩ := hnQB_cof Q U hU ((hnQB_lim Q).add_one_lt h)
    rw [hnq_R_eq Q U hU hn1 hn, hnq_R_eq Q U hU hn1 ((lt_add_one c).trans hn), (hnQGS Q U hU n).R_succ]
  · rw [hnQN_high Q U hU h, hnQN_high Q U hU (h.trans (le_self_add (a := c) (b := 1))),
      (hnQGS Q U hU 0).R_succ]

theorem hnq_g_le_succ (c : Ordinal.{0}) :
    (hnQGS Q U hU (hnQN Q U hU c)).g c ≤ (hnQGS Q U hU (hnQN Q U hU (c + 1))).g (c + 1) := by
  rcases lt_or_ge c (hdNx (hnSqLv.L + 0) Q.F) with h | h
  · obtain ⟨n, hn1, hn⟩ := hnQB_cof Q U hU ((hnQB_lim Q).add_one_lt h)
    rw [hnq_g_eq Q U hU hn1 hn, hnq_g_eq Q U hU hn1 ((lt_add_one c).trans hn)]; exact (hnQGS Q U hU n).g_le_succ c
  · rw [hnQN_high Q U hU h, hnQN_high Q U hU (h.trans (le_self_add (a := c) (b := 1)))]
    exact (hnQGS Q U hU 0).g_le_succ c

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : Q.γ < x)
include hx hx1 hγ

theorem hnq_sq1 : (1 : Ordinal.{0}) < hnSqLv.l x + 0 := by
  rw [add_zero]; exact (one_lt_omega0.trans (omega0_lt_inE hx)).trans (hl_lt_sq hx)

theorem hnq_BR_lt1 : hdNx (hnSqLv.l x + 0) (Q.Fr x) < gq 1 x := Q.S_lt1x hx hx1 hγ

theorem hnq_x_lt_BR : x < hdNx (hnSqLv.l x + 0) (Q.Fr x) := (Q.Fr_gtx hx hx1 hγ).trans (hdNx_gt _ _)

theorem hnq_BR_fix1 : veblen 1 (hdNx (hnSqLv.l x + 0) (Q.Fr x)) = hdNx (hnSqLv.l x + 0) (Q.Fr x) :=
  hdNx_fix (hnq_sq1 Q hx hx1 hγ) _

theorem hnq_BR_fix2 : veblen 2 (hdNx (hnSqLv.l x + 0) (Q.Fr x)) = hdNx (hnSqLv.l x + 0) (Q.Fr x) := by
  refine hdNx_fix ?_ _
  rw [add_zero]
  exact (show (2 : Ordinal.{0}) < ω from by exact_mod_cast natCast_lt_omega0 2).trans
    ((omega0_lt_inE hx).trans (hl_lt_sq hx))

theorem hnq_BR_E : InE (hdNx (hnSqLv.l x + 0) (Q.Fr x)) := by
  unfold hdNx; exact gg_veblen_eps (zero_lt_one.trans (hnq_sq1 Q hx hx1 hγ)).ne'

/-- **`hdNx a (F(x)) < hdNx (x·x) (F(x))`** for `a + 1 < x·x`. -/
theorem hnq_lt_BR {a : Ordinal.{0}} (ha : a + 1 < x * x) : hdNx a (Q.Fr x) < hdNx (hnSqLv.l x + 0) (Q.Fr x) :=
  (hdNx_lt_N (hcN_gt _ _)).trans (hdN_lt_Nx (by rw [add_zero]; exact ha))

/-- **The gate of `hnQGS μ` is below `x` for `μ < x`.** -/
theorem hnq_γ_lt {μ : Ordinal.{0}} (hμ : μ < x) : (hnQGS Q U hU μ).γ < x := by
  rw [hnQGS_γ Q U hU (hμ.trans hx1)]
  exact max_lt hγ ((hlkPk_g (hμ.trans hx1)).trans_lt ((hlGt_le _).trans_lt
    ((inE_indec hx).add_lt (one_lt_omega0.trans (omega0_lt_inE hx)) hμ)))

omit hγ in
theorem hnq_gk_lt {μ : Ordinal.{0}} (hμ : μ < x) : (hlkPk μ).Λ.g < x :=
  (hlkPk_g (hμ.trans hx1)).trans_lt ((hlGt_le _).trans_lt
    ((inE_indec hx).add_lt (one_lt_omega0.trans (omega0_lt_inE hx)) hμ))

/-- **The base reading of `hnQGS μ` at `μ < x`**: `φ(x·(1+μ), F(x)+1)`. -/
theorem hnq_b_eqμ {μ : Ordinal.{0}} (hμ : μ < x) : (hnQGS Q U hU μ).b x = hdNx (x * (1 + μ)) (Q.Fr x) := by
  have hμ1 : μ < Om1 := hμ.trans hx1
  have hg := hnq_gk_lt hx hx1 hμ
  have h1x : 1 + μ < x := (inE_indec hx).add_lt (one_lt_omega0.trans (omega0_lt_inE hx)) hμ
  rw [(hnQGS_shape Q U hU hμ1).2.2.1 x hx hx1 (max_lt (max_lt hγ hg) hx.pos)]
  show veblen ((hlkPk μ).Λ.l x + 0) (Q.Fr x + 1) = _
  rw [hlkPk_l hμ1 hg, add_zero, hnq_b_eq Q hx hx1 hγ h1x]

theorem hnq_b_lt {μ : Ordinal.{0}} (hμ : μ < x) : (hnQGS Q U hU μ).b x < hdNx (hnSqLv.l x + 0) (Q.Fr x) := by
  have h1x : 1 + μ < x := (inE_indec hx).add_lt (one_lt_omega0.trans (omega0_lt_inE hx)) hμ
  rw [hnq_b_eqμ Q U hU hx hx1 hγ hμ]
  refine hnq_lt_BR Q hx hx1 hγ ?_
  calc x * (1 + μ) + 1 < x * (1 + μ) + x := (add_lt_add_iff_left _).2 (one_lt_omega0.trans (omega0_lt_inE hx))
  _ = x * (1 + μ + 1) := by rw [mul_add_one]
  _ < x * x := mul_lt_mul_of_pos_left ((ev_isSuccLimit_of_inE hx).add_one_lt h1x) hx.pos

/-- **The bound field of `hnQGS μ` at `μ < x` lies below `hdNx (x·x) (F(x))`.** -/
theorem hnq_Z_lt {μ : Ordinal.{0}} (hμ : μ < x) : (hnQGS Q U hU μ).Z x ≤ hdNx (hnSqLv.l x + 0) (Q.Fr x) := by
  have hμ1 : μ < Om1 := hμ.trans hx1
  have hg := hnq_gk_lt hx hx1 hμ
  rw [(hnQGS_shape Q U hU hμ1).2.2.2.1 x hx hx1,
    if_pos (show max (hnQW Q (hlkPk μ).Λ).γR 0 < x from max_lt (max_lt hγ hg) hx.pos)]
  refine (hb_evZ_lt_fix2 (hnq_BR_fix2 Q hx hx1 hγ) ?_).le
  show veblen ((hlkPk μ).Λ.l x + 0) (Q.Fr x + 1) < _
  rw [← hdNx_fixP (hnq_rfix0 Q (hlkPk μ).Λ hx hx1 hγ hg)]
  refine hnq_lt_BR Q hx hx1 hγ ?_
  rw [add_zero]
  exact ((add_lt_add_iff_left _).2 (one_lt_omega0.trans (omega0_lt_inE hx))).trans ((hlkPk μ).Λ.l_lt2 x hx hx1 hg)

end Base

/-- **Below the gate `Q.γ` every member's bound field is `Q.Zo`.** -/
theorem hnq_Z_low {μ x : Ordinal.{0}} (hμ : μ < Om1) (hx : InE x) (hx1 : x < Om1) (hγ : ¬ Q.γ < x) :
    (hnQGS Q U hU μ).Z x = Q.Zo x := by
  have hn : ¬ max (hnQW Q (hlkPk μ).Λ).γR 0 < x := fun h => hγ ((le_max_left _ _).trans_lt
    ((le_max_left _ _).trans_lt h))
  rw [(hnQGS_shape Q U hU hμ).2.2.2.1 x hx hx1, if_neg hn,
    hnQW_Zo_low Q _ (fun h => hγ ((le_max_left _ _).trans_lt h))]

theorem hnq_small' {c σ : Ordinal.{0}} (hc : c < hdNx (hnSqLv.L + 0) Q.F) (hσ : InE σ) (hσ1 : σ < Om1)
    (hg : (hnQGS Q U hU (hnQN Q U hU c)).g c < σ) : ∃ μ, μ < σ ∧ c < (hnQGS Q U hU μ).B := by
  obtain ⟨n, hn1, hn⟩ := hnQB_cof Q U hU hc
  rw [hnq_g_eq Q U hU hn1 hn] at hg
  exact hnQ_small Q U hU n hn1 c hn σ hσ hσ1 hg

theorem hnq_F_lt0 : Q.F < (hnQGS Q U hU 0).B := by
  rw [hnQGS_B Q U hU gv_Om1_pos, add_zero, mul_one]
  exact (lt_add_one _).trans_le (right_le_veblen _ _)

open Classical in
/-- **THE UNION OVER ALL LEVELS `Ω₁·(1+μ)`, `μ < Ω₁`, AT `Q`**: a gated digit system with the bound
`hdNx (Ω₁·Ω₁) F`, the base gate `Q.γ`, the base reading `hdNx (x·x) (F(x))`. -/
noncomputable def hnQU : HgVD where
  B := hdNx (hnSqLv.L + 0) Q.F
  γ := Q.γ
  γ_lt := Q.γ_lt
  γ_cl := fun Z hZ hZ1 h => Q.S_cl Z hZ hZ1 h
  γ_G := fun h => absurd h (Q.G_lt.trans (hdNx_gt _ _)).ne'
  R := fun c x => (hnQGS Q U hU (hnQN Q U hU c)).R c x
  g := fun c => (hnQGS Q U hU (hnQN Q U hU c)).g c
  b := fun x => hdNx (hnSqLv.l x + 0) (Q.Fr x)
  ba := fun x => hdNx (hnSqLv.l x + 0) (Q.Fr x)
  ix := hdNx (hnSqLv.L + 0) Q.F
  Z := fun x => if Q.γ < x then evZ (hdNx (hnSqLv.l x + 0) (Q.Fr x)) else Q.Zo x
  B_E := hnQB_E Q
  G_le := (Q.G_lt.trans (hdNx_gt _ _)).le
  B_lt1 := Q.S_lt1
  B_ix := (hdNx_fix hnq_one_OO _).symm
  Z_fix := fun x _ _ => by
    split_ifs
    · exact epsilon_evZ _
    · exact hc_fix_down one_le_two (Q.Zo_fix x)
  Z_G1 := fun x hx hx1 => by
    split_ifs with h
    · exact gw_evZ_lt1 hx hx1 (hnq_BR_lt1 Q hx hx1 h)
    · exact Q.Zo_G1 x hx hx1
  ix_mem := fun S a b ha hb => Q.S_mem S ha hb
  g_lt := fun c hc => by
    obtain ⟨n, hn1, hn⟩ := hnQB_cof Q U hU hc
    rw [hnq_g_eq Q U hU hn1 hn]; exact (hnQGS Q U hU n).g_lt c hn
  g_zero := by rw [hnq_g_eq Q U hU gv_Om1_pos (hnQGS Q U hU 0).B_pos]; exact (hnQGS Q U hU 0).g_zero
  g_nat := fun k => by
    rw [hnq_g_eq Q U hU gv_Om1_pos ((hnQGS Q U hU 0).nat_lt_B k)]; exact (hnQGS Q U hU 0).g_nat k
  g_E := by rw [hnq_g_eq Q U hU gv_Om1_pos (hnQGS Q U hU 0).E_lt_B]; exact (hnQGS Q U hU 0).g_E
  g_lowE := fun c hc => by
    rw [hnq_g_eq Q U hU gv_Om1_pos (hc.trans (hnQGS Q U hU 0).E_lt_B)]; exact (hnQGS Q U hU 0).g_lowE c hc
  g_G0 := fun h => by
    obtain ⟨n, hn1, hn⟩ := hnQB_cof Q U hU h
    rw [hnq_g_eq Q U hU hn1 hn]; exact (hnQGS Q U hU n).g_G0 hn
  g_add := fun Z hZ hωZ x y hxy hgx hgy => by
    obtain ⟨n, hn1, hn⟩ := hnQB_cof Q U hU hxy
    have hx : x < (hnQGS Q U hU n).B := lt_of_le_of_lt le_self_add hn
    have hy : y < (hnQGS Q U hU n).B := lt_of_le_of_lt le_add_self hn
    show (hnQGS Q U hU (hnQN Q U hU (x + y))).g (x + y) < Z
    rw [hnq_g_eq Q U hU hn1 hn]; rw [hnq_g_eq Q U hU hn1 hx] at hgx; rw [hnq_g_eq Q U hU hn1 hy] at hgy
    exact (hnQGS Q U hU n).g_add Z hZ hωZ x y hn hgx hgy
  g_opow := fun Z hZw hωZ y hy hg => by
    obtain ⟨n, hn1, hn⟩ := hnQB_cof Q U hU hy
    have hy' : y < (hnQGS Q U hU n).B := lt_of_le_of_lt (right_le_opow y one_lt_omega0) hn
    show (hnQGS Q U hU (hnQN Q U hU (ω ^ y))).g (ω ^ y) < Z
    rw [hnq_g_eq Q U hU hn1 hn]; rw [hnq_g_eq Q U hU hn1 hy'] at hg
    exact (hnQGS Q U hU n).g_opow Z hZw hωZ y hn hg
  code_gate := fun Z hZ1 hZ0 hZa hZp At hAt c hc hcB => by
    obtain ⟨n, hn1, hn⟩ := hnQB_cof Q U hU hcB
    show (hnQGS Q U hU (hnQN Q U hU c)).g c < Z
    rw [hnq_g_eq Q U hU hn1 hn]
    exact (hnQGS Q U hU n).code_gate Z hZ1 hZ0 hZa hZp At (fun s hs => (hAt s hs).imp_right
      (fun h => (hnQB_gt Q U hU hn1).le.trans h)) c hc hn
  g_succ := fun Z hZ c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hnQB_cof Q U hU hc
    have hc' : c < (hnQGS Q U hU n).B := (lt_add_one c).trans hn
    show (hnQGS Q U hU (hnQN Q U hU (c + 1))).g (c + 1) < Z
    rw [hnq_g_eq Q U hU hn1 hn]; rw [hnq_g_eq Q U hU hn1 hc'] at hg
    exact (hnQGS Q U hU n).g_succ Z hZ c hn hg
  g_le_succ := hnq_g_le_succ Q U hU
  mem := fun S a b ha c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hnQB_cof Q U hU hc
    rw [hnq_g_eq Q U hU hn1 hn] at hg
    exact (hnQGS Q U hU n).mem S a b ha c hn hg
  R_zero := fun x => by
    rw [hnq_R_eq Q U hU gv_Om1_pos (hnQGS Q U hU 0).B_pos]; exact (hnQGS Q U hU 0).R_zero x
  R_nat := fun k x => by
    rw [hnq_R_eq Q U hU gv_Om1_pos ((hnQGS Q U hU 0).nat_lt_B k)]; exact (hnQGS Q U hU 0).R_nat k x
  R_E := fun x => by rw [hnq_R_eq Q U hU gv_Om1_pos (hnQGS Q U hU 0).E_lt_B]; exact (hnQGS Q U hU 0).R_E x
  R_succ := hnq_R_succ Q U hU
  R_pos := fun x hx hx1 c hc0 hc hg => by
    obtain ⟨n, hn1, hn⟩ := hnQB_cof Q U hU hc
    show 0 < (hnQGS Q U hU (hnQN Q U hU c)).R c x
    rw [hnq_R_eq Q U hU hn1 hn]; rw [hnq_g_eq Q U hU hn1 hn] at hg
    exact (hnQGS Q U hU n).R_pos x hx hx1 c hc0 hn hg
  R_omega := fun x hx hx1 c hω hc hg => by
    obtain ⟨n, hn1, hn⟩ := hnQB_cof Q U hU hc
    show ω ≤ (hnQGS Q U hU (hnQN Q U hU c)).R c x
    rw [hnq_R_eq Q U hU hn1 hn]; rw [hnq_g_eq Q U hU hn1 hn] at hg
    exact (hnQGS Q U hU n).R_omega x hx hx1 c hω hn hg
  R_lt_b := fun x hx hx1 hγ c hc hg => by
    obtain ⟨μ, hμx, hcμ⟩ := hnq_small' Q U hU hc hx hx1 hg
    have hμ1 : μ < Om1 := hμx.trans hx1
    show (hnQGS Q U hU (hnQN Q U hU c)).R c x < hdNx (hnSqLv.l x + 0) (Q.Fr x)
    rw [hnq_R_eq Q U hU hμ1 hcμ]; rw [hnq_g_eq Q U hU hμ1 hcμ] at hg
    exact ((hnQGS Q U hU μ).R_lt_Z x hx hx1 c hcμ hg).trans_le (hnq_Z_lt Q U hU hx hx1 hγ hμx)
  R_lt_Z := fun x hx hx1 c hc hg => by
    show (hnQGS Q U hU (hnQN Q U hU c)).R c x <
      if Q.γ < x then evZ (hdNx (hnSqLv.l x + 0) (Q.Fr x)) else Q.Zo x
    split_ifs with hγ
    · obtain ⟨μ, hμx, hcμ⟩ := hnq_small' Q U hU hc hx hx1 hg
      have hμ1 : μ < Om1 := hμx.trans hx1
      rw [hnq_R_eq Q U hU hμ1 hcμ]; rw [hnq_g_eq Q U hU hμ1 hcμ] at hg
      exact (((hnQGS Q U hU μ).R_lt_Z x hx hx1 c hcμ hg).trans_le (hnq_Z_lt Q U hU hx hx1 hγ hμx)).trans
        (lt_evZ _)
    · obtain ⟨n, hn1, hn⟩ := hnQB_cof Q U hU hc
      rw [hnq_R_eq Q U hU hn1 hn]; rw [hnq_g_eq Q U hU hn1 hn] at hg
      have := (hnQGS Q U hU n).R_lt_Z x hx hx1 c hn hg
      rwa [hnq_Z_low Q U hU hn1 hx hx1 hγ] at this
  mono := fun x hx hx1 c hc d hdc hgc hgd => by
    obtain ⟨n, hn1, hn⟩ := hnQB_cof Q U hU hc
    have hd : d < (hnQGS Q U hU n).B := hdc.trans hn
    show (hnQGS Q U hU (hnQN Q U hU d)).R d x < (hnQGS Q U hU (hnQN Q U hU c)).R c x
    rw [hnq_R_eq Q U hU hn1 hn, hnq_R_eq Q U hU hn1 hd]; rw [hnq_g_eq Q U hU hn1 hn] at hgc
    rw [hnq_g_eq Q U hU hn1 hd] at hgd
    exact (hnQGS Q U hU n).mono x hx hx1 c hn d hdc hgc hgd
  cof := fun x hx hx1 c hc hg ν hν => by
    obtain ⟨n, hn1, hn⟩ := hnQB_cof Q U hU hc
    rw [hnq_R_eq Q U hU hn1 hn] at hν; rw [hnq_g_eq Q U hU hn1 hn] at hg
    obtain ⟨d, hdc, hgd, hνd⟩ := (hnQGS Q U hU n).cof x hx hx1 c hn hg ν hν
    have hd : d < (hnQGS Q U hU n).B := hdc.trans hn
    exact ⟨d, hdc, by show (hnQGS Q U hU (hnQN Q U hU d)).g d < x; rw [hnq_g_eq Q U hU hn1 hd]; exact hgd,
      by show ν ≤ (hnQGS Q U hU (hnQN Q U hU d)).R d x; rw [hnq_R_eq Q U hU hn1 hd]; exact hνd⟩
  b_cof := fun x hx hx1 hγ ν hν => by
    obtain ⟨b, hb, hνb⟩ := hjw_Nx_cof (zero_lt_one.trans (hnq_sq1 Q hx hx1 hγ)).ne' (Q.Fr_P hx hx1 hγ) hν
    rw [add_zero] at hb
    have hdiv : b / x < x := (lt_mul_iff_div_lt hx.pos.ne').1 hb
    have hlx := ev_isSuccLimit_of_inE hx
    have hμ : b / x + 1 + 1 < x := hlx.add_one_lt (hlx.add_one_lt hdiv)
    have hμ1 : b / x + 1 + 1 < Om1 := hμ.trans hx1
    have hb1 : b + 1 < x * (1 + (b / x + 1 + 1)) := by
      calc b + 1 ≤ x * (b / x) + x := Order.add_one_le_of_lt (lt_mul_div_add b hx.pos.ne')
      _ = x * (b / x + 1) := by rw [mul_add_one]
      _ < x * (b / x + 1 + 1) := mul_lt_mul_of_pos_left (lt_add_one _) hx.pos
      _ ≤ x * (1 + (b / x + 1 + 1)) := mul_le_mul_left' le_add_self _
    have hνb' : ν < (hnQGS Q U hU (b / x + 1 + 1)).b x := by
      rw [hnq_b_eqμ Q U hU hx hx1 hγ hμ]; exact hνb.trans (hdN_lt_Nx hb1)
    obtain ⟨d, hd, hgd, hνd⟩ :=
      (hnQGS Q U hU (b / x + 1 + 1)).b_cof x hx hx1 (hnq_γ_lt Q U hU hx hx1 hγ hμ) ν hνb'
    exact ⟨d, hd.trans (hnQB_gt Q U hU hμ1),
      by show (hnQGS Q U hU (hnQN Q U hU d)).g d < x; rw [hnq_g_eq Q U hU hμ1 hd]; exact hgd,
      by show ν < (hnQGS Q U hU (hnQN Q U hU d)).R d x; rw [hnq_R_eq Q U hU hμ1 hd]; exact hνd⟩
  b_E := fun x hx hx1 hγ => hnq_BR_E Q hx hx1 hγ
  x_lt_b := fun x hx hx1 hγ => hnq_x_lt_BR Q hx hx1 hγ
  b_eN := fun x hx hx1 hγ => gz_eN_fix hx hx1 (hnq_BR_fix1 Q hx hx1 hγ) (hnq_x_lt_BR Q hx hx1 hγ)
    (hnq_BR_lt1 Q hx hx1 hγ)
  ba_lt := fun x hx hx1 hγ => hnq_BR_lt1 Q hx hx1 hγ
  b_Z := fun x _ _ hγ => by
    show eN (hdNx (hnSqLv.l x + 0) (Q.Fr x)) < if Q.γ < x then evZ (hdNx (hnSqLv.l x + 0) (Q.Fr x)) else Q.Zo x
    rw [if_pos hγ]; exact go_eN_lt_evZ (lt_evZ _)
  b_pi := fun _ _ hB hγ => Q.S_pi hB hγ
  ba_pi := fun _ _ hB hγ => Q.S_pi hB hγ
  ex := fun σ ρ hB c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hnQB_cof Q U hU hc
    show (hnQGS Q U hU (hnQN Q U hU c)).R c ρ ∈ TB ρ σ ∧
      pi σ ρ ((hnQGS Q U hU (hnQN Q U hU c)).R c ρ) = (hnQGS Q U hU (hnQN Q U hU c)).R c σ
    rw [hnq_R_eq Q U hU hn1 hn, hnq_R_eq Q U hU hn1 hn]; rw [hnq_g_eq Q U hU hn1 hn] at hg
    exact (hnQGS Q U hU n).ex σ ρ hB c hn hg
  dig := fun σ ρ hB hγ d hd hg P P' hat => by
    have hσ1 : σ < Om1 := hB.2.2.1.trans hB.2.2.2
    obtain ⟨μ, hμσ, hdμ⟩ := hnq_small' Q U hU hd hB.1 hσ1 hg
    have hμ1 : μ < Om1 := hμσ.trans hσ1
    show ω ^ P * (hnQGS Q U hU (hnQN Q U hU d)).R d ρ ∈ TB ρ σ ∧
      pi σ ρ (ω ^ P * (hnQGS Q U hU (hnQN Q U hU d)).R d ρ) = ω ^ P' * (hnQGS Q U hU (hnQN Q U hU d)).R d σ
    rw [hnq_R_eq Q U hU hμ1 hdμ, hnq_R_eq Q U hU hμ1 hdμ]; rw [hnq_g_eq Q U hU hμ1 hdμ] at hg
    exact (hnQGS Q U hU μ).dig σ ρ hB (hnq_γ_lt Q U hU hB.1 hσ1 hγ hμσ) d hdμ hg P P' (fun β hβ hβe =>
      hat β hβ (hβe.trans (hnq_b_lt Q U hU hB.2.1 hB.2.2.2 (hγ.trans hB.2.2.1) (hμσ.trans hB.2.2.1))))
  ld := fun c hl hc => by
    obtain ⟨n, hn1, hn⟩ := hnQB_cof Q U hU hc
    obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := (hnQGS Q U hU n).ld c hl hn
    have hcpn : cp < (hnQGS Q U hU n).B := hcp.trans hn
    refine ⟨cp, lp, T, hcp, ?_, fun x hx hx1 hg => ?_, fun σ ρ hB hg => hex σ ρ hB ?_⟩
    · show (hnQGS Q U hU (hnQN Q U hU cp)).g cp ≤ (hnQGS Q U hU (hnQN Q U hU c)).g c
      rw [hnq_g_eq Q U hU hn1 hn, hnq_g_eq Q U hU hn1 hcpn]; exact hgcp
    · have hg' : (hnQGS Q U hU n).g c < x := by rw [← hnq_g_eq Q U hU hn1 hn]; exact hg
      show (hnQGS Q U hU (hnQN Q U hU c)).R c x = _ ∧ _
      rw [hnq_R_eq Q U hU hn1 hn, hnq_R_eq Q U hU hn1 hcpn]
      exact hdec x hx hx1 hg'
    · rw [← hnq_g_eq Q U hU hn1 hn]; exact hg

theorem hnQU_B : (hnQU Q U hU).B = hdNx (hnSqLv.L + 0) Q.F := rfl

theorem hnQU_R {μ c : Ordinal.{0}} (hμ : μ < Om1) (hc : c < (hnQGS Q U hU μ).B) (x : Ordinal.{0}) :
    (hnQU Q U hU).R c x = (hnQGS Q U hU μ).R c x := hnq_R_eq Q U hU hμ hc x

theorem hnQU_g {μ c : Ordinal.{0}} (hμ : μ < Om1) (hc : c < (hnQGS Q U hU μ).B) :
    (hnQU Q U hU).g c = (hnQGS Q U hU μ).g c := hnq_g_eq Q U hU hμ hc

/-- **THE UNION AT `Q` HAS THE SPECIFICATION OF THE LEVEL `Ω₁·Ω₁ + 0`.** -/
theorem hnQU_spec : HnVSpec Q U (hnQU Q U hU) := by
  have hUB : U.B = Q.F := hg_B_of_start hU
  have hU0 : ∀ c, c < U.B → c < (hnQGS Q U hU 0).B := fun c hc => hc.trans (by rw [hUB]; exact hnq_F_lt0 Q U hU)
  have hs0 := hnQM0_spec Q U hU
  have e0 : hnQGS Q U hU 0 = hnQM0 Q U hU := hnQGS_zero Q U hU
  refine ⟨rfl, rfl, fun x _ _ _ => rfl, fun x _ _ => rfl, fun c x hc => ?_,
    fun c hc => ?_, fun c σ hFc hc hσ hσ1 hg => ?_, fun x hx hx1 hγ => ?_, fun x hx hx1 => ?_⟩
  · rw [hnQU_R Q U hU gv_Om1_pos (hU0 c hc), e0]; exact hs0.extR c x hc
  · rw [hnQU_g Q U hU gv_Om1_pos (hU0 c hc), e0]; exact hs0.extg c hc
  · obtain ⟨n, hn1, hn⟩ := hnQB_cof Q U hU hc
    rw [hnQU_g Q U hU hn1 hn] at hg
    exact (hnQGS_shape Q U hU hn1).2.2.2.2 c σ hFc hn hσ hσ1 hg
  · rw [hnQU_R Q U hU gv_Om1_pos (hnq_F_lt0 Q U hU), e0]; exact hs0.RF x hx hx1 hγ
  · rw [hnQU_g Q U hU gv_Om1_pos (hnq_F_lt0 Q U hU), e0]; exact hs0.gF x hx hx1

end U

/-- **THE STEP OF THE LEVEL `Ω₁·Ω₁ + 0`.** -/
noncomputable def hnSqSt0 : HnVStTy hnSqLv 0 := fun Q U h => hnQU Q U h

/-- **THE PACKAGE AT THE LEVEL `Ω₁·Ω₁`.** -/
noncomputable def hnPkSq : HnPk := ⟨hnSqLv, hnSqSt0, fun Q U h => hnQU_spec Q U h⟩

theorem hnPkSq_Λ : hnPkSq.Λ = hnSqLv := rfl

end Googology.Trans.PoR.InaccPsi.R2.Hn

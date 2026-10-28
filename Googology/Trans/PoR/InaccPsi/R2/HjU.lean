import Googology.Trans.PoR.InaccPsi.R2.HiVFr

/-!
# HjU: THE UNION OF ALL LEVELS `Ω₁ + κ`, `κ < Ω₁`, READ AS `x + κ`; THE LEVEL `Ω₁·2` READ AS `x·2`

`Hi.hiGL κ` (bound `φ(Ω₁+κ+1, G+1)`, base gate `κ`) exists for every `κ < Ω₁` but is located only for `κ < K`
(`Hi.hiGL_loc`).  Their union over ALL `κ < Ω₁` is a gated digit system (`Hg.HgVD`) with the bound
`φ(Ω₁·2, G+1) = φ(Ω₁+Ω₁, G+1)`, the base gate `0` and the base reading `φ(x+x, Γ_{x+1}+1)`: the index `κ` of the
level is read with `Ω₁ ↦ x` (`κ < x` at the base `x`).  Lemma EXACT for the base reading is `π(ρ+ρ) = σ+σ` inside
`ϑ` (`hj_b_pi`).  A code of `hiGL κ` with gate below an `ε`-number `σ` lies in some `hiGL μ`, `μ < σ` (`hj_small`, one
induction on the level: the codes past the start of the level `Ω₁ + κ` have a gate `≥ κ`, `hj_highN`).

* `hj_highN` (**the codes past the start of an offset union over `G` at level `Ω₁+κ` have gate `≥ κ`**), `hj_small`
  (**SMALL for the level recursion over `G`**);
* `hjB` (`φ(Ω₁+Ω₁, G+1)`), `hjB_gt`, `hjB_cof`, `hjb` (`φ(x+x, Γ_{x+1}+1)`), `hj_b_pi` (**EXACT for
  `φ(ρ+ρ, Γ_{ρ+1}+1)`**), `hjU` (**THE UNION OVER ALL LEVELS `Ω₁+κ`, `Ω₁ ↦ x`**), `hjU_R`, `hjU_g`.

No new axiom.  New definitions: `hjB`, `hjb`, `hjN`, `hjU`.
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

/-! ## The gates past the start of an offset union over a base of level `Ω₁ + κ` -/

/-- **The codes past the start `S0` of the offset union of a base `A` of level `Ω₁ + κ` have a gate `≥` the reading
gate `γN`**: a code `c ∈ [S0.B, N_{Ω₁+κ}(F))` with gate below an `ε`-number `σ` forces `A.γN < σ`. -/
theorem hj_highN {κ : Ordinal.{0}} {St : ∀ (Q : HiVQ κ) (U : HgVD), HgSStart (hiVPB Q) U → HgVD}
    (hSt : ∀ Q U h, HiVSpec Q U (St Q U h)) {A : HiVB κ} {S0 : HgVD} (hS : HiVStart A S0)
    {c σ : Ordinal.{0}} (hc : c < hcN (Om1 + κ) A.F) (hBc : S0.B ≤ c) (hσ : InE σ) (hσ1 : σ < Om1)
    (hg : (hiVTU hSt hS).g c < σ) : A.γN < σ := by
  obtain ⟨n, hn1, hn⟩ := hiVT_cof hSt hS hc
  obtain ⟨-, hN1, hcNc⟩ := hiVTN_spec hn1 hn
  have hgN : (hiVTU hSt hS).g c = (hiVU St A S0 (hiVTN St A S0 c)).g c := rfl
  have I := hiV_inv hSt hS _ hN1
  rcases zero_or_succ_or_isSuccLimit (hiVTN St A S0 c) with h0 | ⟨m, hm⟩ | hlim
  · rw [h0, hiVU_zero] at hcNc
    exact absurd hBc (not_le.2 hcNc)
  · have hm' : hiVTN St A S0 c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < hiVTN St A S0 c := by rw [hm']; exact lt_add_one m
    have hml : m < hcN (Om1 + κ) A.F := hmN.trans hN1
    have hBc' : (hiVU St A S0 m).B ≤ c := not_lt.1 (hiVTN_min hmN hml)
    rw [hgN, hm'] at hg
    rw [hm'] at hcNc I hN1
    have hγ := I.high m (lt_add_one _) c σ hBc' hcNc hσ hσ1 hg
    exact (max_lt_iff.1 ((hiVU_γ_iff hSt hS hN1 hσ hσ1).1 hγ)).1
  · exfalso
    rw [hiVU_B hSt hS hN1] at hcNc
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen (Om1 + κ)).lt_iff_exists_lt
        (isSuccLimit_add _ hlim)).1 hcNc
    obtain ⟨d, hf, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    have hfl : d < hcN (Om1 + κ) A.F := hf.trans hN1
    refine hiVTN_min hf hfl ?_
    rw [hiVU_B hSt hS hfl]; exact hct.trans_le ((isNormal_veblen (Om1 + κ)).monotone htd)

/-! ## SMALL for the level recursion over `G` -/

/-- **SMALL**: a code of `hiGL κ` with gate below an `ε`-number `σ` lies in some `hiGL μ`, `μ < σ` (one induction on
the level: the codes past the start of the level `Ω₁ + κ` have a gate `≥ κ`, `hj_highN`). -/
theorem hj_small : ∀ κ, κ < Om1 → ∀ c, c < (hiGL κ).B → ∀ σ, InE σ → σ < Om1 → (hiGL κ).g c < σ →
    ∃ μ, μ < σ ∧ c < (hiGL μ).B := by
  intro κ
  induction κ using WellFoundedLT.induction with
  | ind κ IH =>
  intro hκ c hc σ hσ hσ1 hg
  by_cases hκσ : κ < σ
  · exact ⟨κ, hκσ, hc⟩
  rcases zero_or_succ_or_isSuccLimit κ with h0 | ⟨μ, hμ⟩ | hlim
  · exact absurd (by rw [h0]; exact hσ.pos) hκσ
  · have hμ' : κ = μ + 1 := by rw [← hμ, succ_eq_add_one]
    subst hμ'
    have hμ1 : μ < Om1 := (lt_add_one μ).trans hκ
    by_cases hcμ : c < (hiGL μ).B
    · have e := (hiGL_ext hκ (le_add_right le_rfl) hcμ 0).2
      rw [e] at hg
      exact IH μ (lt_add_one μ) hμ1 c hcμ σ hσ hσ1 hg
    · exfalso
      have hsh := hiG_ok_shape hκ (hiGL_inv μ hμ1).1
      rw [hiGL_succ, hiGSt_eq hκ hsh] at hc hg
      exact hκσ (hj_highN _ _ hc (not_lt.1 hcμ) hσ hσ1 hg)
  · have hcoh : HiGCoh κ (fun κ' _ => hiGL κ') :=
      ⟨fun κ' h => (hiGL_inv κ' (h.trans hκ)).1, fun κ₁ κ₂ h₁ h₂ h12 c x hc =>
        (hiGL_inv κ₂ (h₂.trans hκ)).2 κ₁ h12 c x hc⟩
    have eU : hiGChU κ hlim (fun κ' _ => hiGL κ') = (hiGCh κ hlim hκ (fun κ' _ => hiGL κ') hcoh).U := by
      unfold hiGChU; rw [dif_pos ⟨hκ, hcoh⟩]
    have hsh := hiGCh_shape κ hlim hκ (fun κ' _ => hiGL κ') hcoh
    by_cases hcS : c < veblen (Om1 + κ) (gcG 0 + 1)
    · obtain ⟨b, hb, hcb⟩ := hgVeb_cof (hiv_L0 κ) (hiG_fixL hκ) hcS
      obtain ⟨κ'', hκ'', hbκ⟩ := (lt_add_iff hlim.bot_lt.ne').1 hb
      have hκ''1 : κ'' < Om1 := hκ''.trans hκ
      have hcν : c < (hiGL κ'').B := by
        rw [(hiGL_inv κ'' hκ''1).1.1]; exact hcb.trans_le (hcN_mono hbκ _)
      have e2 := (hiGL_ext hκ hκ''.le hcν 0).2
      rw [e2] at hg
      exact IH κ'' hκ'' hκ''1 c hcν σ hσ hσ1 hg
    · exfalso
      rw [hiGL_limit hlim, eU, hiGSt_eq hκ hsh] at hc hg
      refine hκσ (hj_highN _ _ hc ?_ hσ hσ1 hg)
      rw [hsh.1]; exact not_lt.1 hcS

/-! ## The bound `φ(Ω₁+Ω₁, G+1)` -/

/-- **`φ(Ω₁·2, G+1) = φ(Ω₁+Ω₁, G+1)`**: the bound of the union over all levels `Ω₁ + κ`. -/
noncomputable def hjB : Ordinal.{0} := veblen (Om1 + Om1) (gcG 0 + 1)

theorem hj_OO_lt_G (α : Ordinal.{0}) : (Om1 : Ordinal.{0}) + Om1 < gcG α :=
  (inE_indec (Low.opow_eq_self_of_SC (gcG_SC α))).add_lt (hg_Om1_lt_G α) (hg_Om1_lt_G α)

theorem hj_OO_ne : (Om1 : Ordinal.{0}) + Om1 ≠ 0 := hiv_L0 Om1

theorem hj_G_fixOO : veblen (Om1 + Om1) (gcG 0) = gcG 0 := gn_veb_fix (gcG_SC 0) (hj_OO_lt_G 0)

/-- **Every `hiGL κ`, `κ < Ω₁`, lies below `φ(Ω₁+Ω₁, G+1)`.** -/
theorem hjB_gt {κ : Ordinal.{0}} (hκ : κ < Om1) : (hiGL κ).B < hjB := by
  rw [hiGL_B hκ, add_assoc]
  exact hd_veb_left_lt ((add_lt_add_iff_left _).2 (gl_Om1_lim.add_one_lt hκ)) _

/-- **The bounds `φ(Ω₁+κ+1, G+1)`, `κ < Ω₁`, are cofinal in `φ(Ω₁+Ω₁, G+1)`.** -/
theorem hjB_cof {c : Ordinal.{0}} (hc : c < hjB) : ∃ κ, κ < Om1 ∧ c < (hiGL κ).B := by
  obtain ⟨b, hb, hcb⟩ := hgVeb_cof hj_OO_ne hj_G_fixOO hc
  obtain ⟨κ, hκ, hbκ⟩ := (lt_add_iff gv_Om1_pos.ne').1 hb
  exact ⟨κ, hκ, by rw [(hiGL_inv κ hκ).1.1]; exact hcb.trans_le (hcN_mono hbκ _)⟩

theorem hjB_lt1 : hjB < gcG 1 := by
  have hG1 := gcG_SC 1
  have hE := Low.opow_eq_self_of_SC hG1
  have hfix : veblen (Om1 + Om1) (gcG 1) = gcG 1 := gn_veb_fix hG1 (hj_OO_lt_G 1)
  have h2 := (isNormal_veblen (Om1 + Om1)).strictMono
    ((ev_isSuccLimit_of_inE hE).add_one_lt (gcG_lt zero_lt_one))
  unfold hjB; rwa [hfix] at h2

theorem hjB_fix1 : veblen 1 hjB = hjB := veblen_veblen_of_lt (hg_one_lt_Om1.trans_le le_self_add) _

theorem hjB_E : InE hjB := gg_veblen_eps hj_OO_ne

theorem hjB_lim : IsSuccLimit hjB := ev_isSuccLimit_of_inE hjB_E

/-- **`φ(Ω₁+K, G+1) < φ(Ω₁+Ω₁, G+1)`.** -/
theorem hiGE_lt_hjB (S : InaccSeq.{0}) : hiGE S < hjB := by
  have hK := hf_K_lt S
  have h1 : hiGE S < (hiGL (Td.tdK S)).B := by
    rw [hiGL_B hK]
    exact hd_veb_left_lt (lt_add_one _) _
  exact h1.trans (hjB_gt hK)

/-- The first level containing `c`. -/
noncomputable def hjN (c : Ordinal.{0}) : Ordinal.{0} := sInf {κ | κ < Om1 ∧ c < (hiGL κ).B}

theorem hjN_spec {c κ : Ordinal.{0}} (hκ : κ < Om1) (hc : c < (hiGL κ).B) :
    hjN c ≤ κ ∧ hjN c < Om1 ∧ c < (hiGL (hjN c)).B := by
  have hne : ({κ | κ < Om1 ∧ c < (hiGL κ).B} : Set Ordinal.{0}).Nonempty := ⟨κ, hκ, hc⟩
  have hm := csInf_mem hne
  exact ⟨csInf_le' ⟨hκ, hc⟩, hm.1, hm.2⟩

theorem hjN_high {c : Ordinal.{0}} (hc : hjB ≤ c) : hjN c = 0 := by
  unfold hjN
  have he : ({κ | κ < Om1 ∧ c < (hiGL κ).B} : Set Ordinal.{0}) = ∅ := by
    ext κ
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hκ hcκ
    exact absurd (hcκ.trans (hjB_gt hκ)) (not_lt.2 hc)
  rw [he]; exact Ordinal.sInf_empty

theorem hj_R_eq {c κ : Ordinal.{0}} (hκ : κ < Om1) (hc : c < (hiGL κ).B) (x : Ordinal.{0}) :
    (hiGL (hjN c)).R c x = (hiGL κ).R c x := by
  obtain ⟨h1, -, h3⟩ := hjN_spec hκ hc
  exact (hiGL_ext hκ h1 h3 x).1.symm

theorem hj_g_eq {c κ : Ordinal.{0}} (hκ : κ < Om1) (hc : c < (hiGL κ).B) :
    (hiGL (hjN c)).g c = (hiGL κ).g c := by
  obtain ⟨h1, -, h3⟩ := hjN_spec hκ hc
  exact (hiGL_ext hκ h1 h3 0).2.symm

theorem hj_R_succ (c x : Ordinal.{0}) : (hiGL (hjN (c + 1))).R (c + 1) x = (hiGL (hjN c)).R c x + 1 := by
  rcases lt_or_ge c hjB with h | h
  · obtain ⟨n, hn1, hn⟩ := hjB_cof (hjB_lim.add_one_lt h)
    rw [hj_R_eq hn1 hn, hj_R_eq hn1 ((lt_add_one c).trans hn), (hiGL n).R_succ]
  · rw [hjN_high h, hjN_high (h.trans (le_self_add (a := c) (b := 1))), (hiGL 0).R_succ]

theorem hj_g_le_succ (c : Ordinal.{0}) : (hiGL (hjN c)).g c ≤ (hiGL (hjN (c + 1))).g (c + 1) := by
  rcases lt_or_ge c hjB with h | h
  · obtain ⟨n, hn1, hn⟩ := hjB_cof (hjB_lim.add_one_lt h)
    rw [hj_g_eq hn1 hn, hj_g_eq hn1 ((lt_add_one c).trans hn)]; exact (hiGL n).g_le_succ c
  · rw [hjN_high h, hjN_high (h.trans (le_self_add (a := c) (b := 1)))]; exact (hiGL 0).g_le_succ c

/-! ## The base reading `φ(x+x, Γ_{x+1}+1)` -/

/-- **The base reading `φ(x+x, Γ_{x+1}+1)`** (the level `Ω₁ + Ω₁` read as `x + x`). -/
noncomputable def hjb (x : Ordinal.{0}) : Ordinal.{0} := veblen (x + x) (lgG x + 1)

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem hj_xx_q : x + x < gq 1 x :=
  (inE_indec (gm1_facts hx hx1).2.2.2).add_lt (gm1_facts hx hx1).2.1 (gm1_facts hx hx1).2.1

theorem hj_fix_xx : veblen (x + x) (lgG x) = lgG x :=
  hc_G_fix hx hx1 ((hi_one_le hx hx1).trans le_self_add) (hi_xx_lt_G hx hx1)

/-- **`ϑˣ(Ω₁·(x+x) + Γ_{x+1}) = φ(x+x, Γ_{x+1}+1)`.** -/
theorem hj_glA : glA (x + x) (lgG x) x = hjb x :=
  hc_glA_fixG hx hx1 ((hi_one_le hx hx1).trans le_self_add) (hj_xx_q hx hx1) (hj_fix_xx hx hx1)
    (hi_xx_lt_G hx hx1) (lgG_facts hx hx1).2.1 (mg_lgG_lt_G1 hx hx1)

theorem hj_Zo_eq : hiGZo x = hjb x := by
  rw [hiGZo_eq hx hx1, hdNx_fixP (hj_fix_xx hx hx1)]; rfl

theorem hj_b_lt1 : hjb x < gq 1 x := by rw [← hj_Zo_eq hx hx1]; exact hiGZo_lt1 hx hx1

theorem hj_b_fix1 : veblen 1 (hjb x) = hjb x :=
  veblen_veblen_of_lt ((one_lt_omega0.trans (omega0_lt_inE hx)).trans_le le_self_add) _

theorem hj_x_lt_b : x < hjb x := (lgG_facts hx hx1).2.1.trans ((lt_add_one _).trans_le (right_le_veblen _ _))

theorem hj_b_E : InE (hjb x) := gg_veblen_eps (by
  have : (0 : Ordinal.{0}) < x + x := hx.pos.trans_le le_self_add
  exact this.ne')

/-- **The bound field of every `hiGL κ` lies below `φ(x+x, Γ_{x+1}+1)`.** -/
theorem hj_Z_le {κ : Ordinal.{0}} (hκ : κ < Om1) : (hiGL κ).Z x ≤ hjb x := by
  rw [(hiGL_inv κ hκ).1.2.2.2 x hx hx1, ← hj_Zo_eq hx hx1]
  split_ifs with h
  · exact (hb_evZ_lt_fix2 (hiGZo_fix x) (hiG_N_lt_Zo hx hx1 h)).le
  · exact le_rfl

/-- **The base reading of `hiGL κ` lies below `φ(x+x, Γ_{x+1}+1)`** (`κ < x`). -/
theorem hj_b_lt {κ : Ordinal.{0}} (hκ : κ < x) : (hiGL κ).b x < hjb x := by
  rw [(hiGL_inv κ (hκ.trans hx1)).1.2.2.1 x hx hx1 hκ, ← hj_Zo_eq hx hx1]
  exact hiG_N_lt_Zo hx hx1 hκ

end Base

/-- **Lemma EXACT for `φ(ρ+ρ, Γ_{ρ+1}+1) = ϑᵖ(Ω₁·(ρ+ρ) + Γ_{ρ+1})`**: the level `ρ+ρ` goes to `σ+σ`. -/
theorem hj_b_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) : hjb ρ ∈ TB ρ σ ∧ pi σ ρ (hjb ρ) = hjb σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨g1, g2⟩ : lgG ρ ∈ TB ρ σ ∧ pi σ ρ (lgG ρ) = lgG σ := Go.goGl.ba_pi σ ρ hB
  obtain ⟨r1, r2⟩ := pi_base hB
  obtain ⟨u1, u2⟩ := pi_add hB r1 r1
  rw [r2] at u2
  have hq : ρ + ρ < Om1 := (hi_xx_lt_G hB.2.1 hρ1).trans (lgG_facts hB.2.1 hρ1).2.2.1
  have h := glA_pi hB u1 hq g1 (lgG_facts hB.2.1 hρ1).2.2.1
  rw [u2, g2, hj_glA hB.2.1 hρ1, hj_glA hB.1 hσ1] at h
  exact h

/-- **A code of the union with gate below an `ε`-number `σ` lies in `hiGL μ`, `μ < σ`.** -/
theorem hj_small' {c σ : Ordinal.{0}} (hc : c < hjB) (hσ : InE σ) (hσ1 : σ < Om1) (hg : (hiGL (hjN c)).g c < σ) :
    ∃ μ, μ < σ ∧ c < (hiGL μ).B := by
  obtain ⟨n, hn1, hn⟩ := hjB_cof hc
  rw [hj_g_eq hn1 hn] at hg
  exact hj_small n hn1 c hn σ hσ hσ1 hg

theorem hj_γ_lt {μ x : Ordinal.{0}} (hμ : μ < x) (hμ1 : μ < Om1) : (hiGL μ).γ < x := by
  rw [hiGL_γ hμ1]; exact hμ

/-- **THE UNION OVER ALL LEVELS `Ω₁ + κ`, `κ < Ω₁`**: a gated digit system (`HgVD`) with the bound `φ(Ω₁+Ω₁, G+1)`,
the base gate `0`, the base reading `φ(x+x, Γ_{x+1}+1)` (the level `Ω₁ + Ω₁` read as `x + x`) and the bound field
`evZ(φ(x+x, Γ_{x+1}+1)) < Γ_{x+2}`. -/
noncomputable def hjU : HgVD where
  B := hjB
  γ := 0
  γ_lt := gv_Om1_pos
  γ_cl := fun _ hZ _ _ => hZ.1
  γ_G := fun _ => rfl
  R := fun c x => (hiGL (hjN c)).R c x
  g := fun c => (hiGL (hjN c)).g c
  b := hjb
  ba := hjb
  ix := hjB
  Z := fun x => evZ (hjb x)
  B_E := hjB_E
  G_le := (lt_add_one _).le.trans (right_le_veblen _ _)
  B_lt1 := hjB_lt1
  B_ix := hjB_fix1.symm
  Z_fix := fun _ _ _ => epsilon_evZ _
  Z_G1 := fun x hx hx1 => gw_evZ_lt1 hx hx1 (hj_b_lt1 hx hx1)
  ix_mem := fun S a b ha _ => CSet.phi_mem (by
      rw [Br.Om1_eq]; exact CSet.add_mem (CSet.Om_mem (CSet.one_mem _ _)) (CSet.Om_mem (CSet.one_mem _ _)))
    (CSet.succ_mem (gmS_G0_mem S ha))
  g_lt := fun c hc => by
    obtain ⟨n, hn1, hn⟩ := hjB_cof hc
    show (hiGL (hjN c)).g c < Om1
    rw [hj_g_eq hn1 hn]; exact (hiGL n).g_lt c hn
  g_zero := by
    show (hiGL (hjN 0)).g 0 = 0
    rw [hj_g_eq gv_Om1_pos (hiGL 0).B_pos]; exact (hiGL 0).g_zero
  g_nat := fun k => by
    show (hiGL (hjN k)).g k < ω
    rw [hj_g_eq gv_Om1_pos ((hiGL 0).nat_lt_B k)]; exact (hiGL 0).g_nat k
  g_E := by
    show (hiGL (hjN gfE)).g gfE = 0
    rw [hj_g_eq gv_Om1_pos (hiGL 0).E_lt_B]; exact (hiGL 0).g_E
  g_lowE := fun c hc => by
    show (hiGL (hjN c)).g c = gtc c
    rw [hj_g_eq gv_Om1_pos (hc.trans (hiGL 0).E_lt_B)]; exact (hiGL 0).g_lowE c hc
  g_G0 := fun h => by
    obtain ⟨n, hn1, hn⟩ := hjB_cof h
    show (hiGL (hjN (gcG 0))).g (gcG 0) = 0
    rw [hj_g_eq hn1 hn]; exact (hiGL n).g_G0 hn
  g_add := fun Z hZ hωZ x y hxy hgx hgy => by
    obtain ⟨n, hn1, hn⟩ := hjB_cof hxy
    have hx : x < (hiGL n).B := lt_of_le_of_lt le_self_add hn
    have hy : y < (hiGL n).B := lt_of_le_of_lt le_add_self hn
    show (hiGL (hjN (x + y))).g (x + y) < Z
    have hgx' : (hiGL (hjN x)).g x < Z := hgx
    have hgy' : (hiGL (hjN y)).g y < Z := hgy
    rw [hj_g_eq hn1 hn]; rw [hj_g_eq hn1 hx] at hgx'; rw [hj_g_eq hn1 hy] at hgy'
    exact (hiGL n).g_add Z hZ hωZ x y hn hgx' hgy'
  g_opow := fun Z hZw hωZ y hy hg => by
    obtain ⟨n, hn1, hn⟩ := hjB_cof hy
    have hy' : y < (hiGL n).B := lt_of_le_of_lt (right_le_opow y one_lt_omega0) hn
    show (hiGL (hjN (ω ^ y))).g (ω ^ y) < Z
    have hg' : (hiGL (hjN y)).g y < Z := hg
    rw [hj_g_eq hn1 hn]; rw [hj_g_eq hn1 hy'] at hg'
    exact (hiGL n).g_opow Z hZw hωZ y hn hg'
  code_gate := fun Z hZ1 hZ0 hZa hZp At hAt c hc hcB => by
    obtain ⟨n, hn1, hn⟩ := hjB_cof hcB
    show (hiGL (hjN c)).g c < Z
    rw [hj_g_eq hn1 hn]
    exact (hiGL n).code_gate Z hZ1 hZ0 hZa hZp At (fun s hs => (hAt s hs).imp_right
      (fun h => (hjB_gt hn1).le.trans h)) c hc hn
  g_succ := fun Z hZ c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hjB_cof hc
    have hc' : c < (hiGL n).B := (lt_add_one c).trans hn
    show (hiGL (hjN (c + 1))).g (c + 1) < Z
    have hg' : (hiGL (hjN c)).g c < Z := hg
    rw [hj_g_eq hn1 hn]; rw [hj_g_eq hn1 hc'] at hg'
    exact (hiGL n).g_succ Z hZ c hn hg'
  g_le_succ := hj_g_le_succ
  mem := fun S a b ha c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hjB_cof hc
    have hg' : (hiGL (hjN c)).g c < b := hg
    rw [hj_g_eq hn1 hn] at hg'
    exact (hiGL n).mem S a b ha c hn hg'
  R_zero := fun x => by
    show (hiGL (hjN 0)).R 0 x = 0
    rw [hj_R_eq gv_Om1_pos (hiGL 0).B_pos]; exact (hiGL 0).R_zero x
  R_nat := fun k x => by
    show (hiGL (hjN k)).R k x = k
    rw [hj_R_eq gv_Om1_pos ((hiGL 0).nat_lt_B k)]; exact (hiGL 0).R_nat k x
  R_E := fun x => by
    show (hiGL (hjN gfE)).R gfE x = eN x
    rw [hj_R_eq gv_Om1_pos (hiGL 0).E_lt_B]; exact (hiGL 0).R_E x
  R_succ := hj_R_succ
  R_pos := fun x hx hx1 c hc0 hc hg => by
    obtain ⟨n, hn1, hn⟩ := hjB_cof hc
    show 0 < (hiGL (hjN c)).R c x
    have hg' : (hiGL (hjN c)).g c < x := hg
    rw [hj_R_eq hn1 hn]; rw [hj_g_eq hn1 hn] at hg'
    exact (hiGL n).R_pos x hx hx1 c hc0 hn hg'
  R_omega := fun x hx hx1 c hω hc hg => by
    obtain ⟨n, hn1, hn⟩ := hjB_cof hc
    show ω ≤ (hiGL (hjN c)).R c x
    have hg' : (hiGL (hjN c)).g c < x := hg
    rw [hj_R_eq hn1 hn]; rw [hj_g_eq hn1 hn] at hg'
    exact (hiGL n).R_omega x hx hx1 c hω hn hg'
  R_lt_b := fun x hx hx1 _ c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hjB_cof hc
    show (hiGL (hjN c)).R c x < hjb x
    have hg' : (hiGL (hjN c)).g c < x := hg
    rw [hj_R_eq hn1 hn]; rw [hj_g_eq hn1 hn] at hg'
    exact ((hiGL n).R_lt_Z x hx hx1 c hn hg').trans_le (hj_Z_le hx hx1 hn1)
  R_lt_Z := fun x hx hx1 c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hjB_cof hc
    show (hiGL (hjN c)).R c x < evZ (hjb x)
    have hg' : (hiGL (hjN c)).g c < x := hg
    rw [hj_R_eq hn1 hn]; rw [hj_g_eq hn1 hn] at hg'
    exact (((hiGL n).R_lt_Z x hx hx1 c hn hg').trans_le (hj_Z_le hx hx1 hn1)).trans (lt_evZ _)
  mono := fun x hx hx1 c hc d hdc hgc hgd => by
    obtain ⟨n, hn1, hn⟩ := hjB_cof hc
    have hd : d < (hiGL n).B := hdc.trans hn
    show (hiGL (hjN d)).R d x < (hiGL (hjN c)).R c x
    have hgc' : (hiGL (hjN c)).g c < x := hgc
    have hgd' : (hiGL (hjN d)).g d < x := hgd
    rw [hj_R_eq hn1 hn, hj_R_eq hn1 hd]; rw [hj_g_eq hn1 hn] at hgc'; rw [hj_g_eq hn1 hd] at hgd'
    exact (hiGL n).mono x hx hx1 c hn d hdc hgc' hgd'
  cof := fun x hx hx1 c hc hg ν hν => by
    obtain ⟨n, hn1, hn⟩ := hjB_cof hc
    have hg' : (hiGL (hjN c)).g c < x := hg
    have hν' : ν < (hiGL (hjN c)).R c x := hν
    rw [hj_R_eq hn1 hn] at hν'; rw [hj_g_eq hn1 hn] at hg'
    obtain ⟨d, hdc, hgd, hνd⟩ := (hiGL n).cof x hx hx1 c hn hg' ν hν'
    have hd : d < (hiGL n).B := hdc.trans hn
    exact ⟨d, hdc, by show (hiGL (hjN d)).g d < x; rw [hj_g_eq hn1 hd]; exact hgd,
      by show ν ≤ (hiGL (hjN d)).R d x; rw [hj_R_eq hn1 hd]; exact hνd⟩
  b_cof := fun x hx hx1 _ ν hν => by
    have hx0 : x + x ≠ 0 := (hx.pos.trans_le le_self_add).ne'
    obtain ⟨b, hb, hνb⟩ := hgVeb_cof hx0 (hj_fix_xx hx hx1) hν
    obtain ⟨κ, hκ, hbκ⟩ := (lt_add_iff hx.pos.ne').1 hb
    have hκ1 : κ < Om1 := hκ.trans hx1
    have hνb' : ν < (hiGL κ).b x := by
      rw [(hiGL_inv κ hκ1).1.2.2.1 x hx hx1 hκ]
      exact hνb.trans_le (hcN_mono hbκ _)
    obtain ⟨d, hd, hgd, hνd⟩ := (hiGL κ).b_cof x hx hx1 (hj_γ_lt hκ hκ1) ν hνb'
    exact ⟨d, hd.trans (hjB_gt hκ1), by show (hiGL (hjN d)).g d < x; rw [hj_g_eq hκ1 hd]; exact hgd,
      by show ν < (hiGL (hjN d)).R d x; rw [hj_R_eq hκ1 hd]; exact hνd⟩
  b_E := fun x hx hx1 _ => hj_b_E hx hx1
  x_lt_b := fun x hx hx1 _ => hj_x_lt_b hx hx1
  b_eN := fun x hx hx1 _ => gz_eN_fix hx hx1 (hj_b_fix1 hx hx1) (hj_x_lt_b hx hx1) (hj_b_lt1 hx hx1)
  ba_lt := fun x hx hx1 _ => hj_b_lt1 hx hx1
  b_Z := fun _ _ _ _ => go_eN_lt_evZ (lt_evZ _)
  b_pi := fun _ _ hB _ => hj_b_pi hB
  ba_pi := fun _ _ hB _ => hj_b_pi hB
  ex := fun σ ρ hB c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hjB_cof hc
    show (hiGL (hjN c)).R c ρ ∈ TB ρ σ ∧ pi σ ρ ((hiGL (hjN c)).R c ρ) = (hiGL (hjN c)).R c σ
    have hg' : (hiGL (hjN c)).g c < σ := hg
    rw [hj_R_eq hn1 hn, hj_R_eq hn1 hn]; rw [hj_g_eq hn1 hn] at hg'
    exact (hiGL n).ex σ ρ hB c hn hg'
  dig := fun σ ρ hB _ d hd hg P P' hat => by
    have hσ1 : σ < Om1 := hB.2.2.1.trans hB.2.2.2
    obtain ⟨μ, hμσ, hdμ⟩ := hj_small' hd hB.1 hσ1 hg
    have hμ1 : μ < Om1 := hμσ.trans hσ1
    show ω ^ P * (hiGL (hjN d)).R d ρ ∈ TB ρ σ ∧
      pi σ ρ (ω ^ P * (hiGL (hjN d)).R d ρ) = ω ^ P' * (hiGL (hjN d)).R d σ
    have hg' : (hiGL (hjN d)).g d < σ := hg
    rw [hj_R_eq hμ1 hdμ, hj_R_eq hμ1 hdμ]; rw [hj_g_eq hμ1 hdμ] at hg'
    exact (hiGL μ).dig σ ρ hB (hj_γ_lt hμσ hμ1) d hdμ hg' P P' (fun β hβ hβe =>
      hat β hβ (hβe.trans (hj_b_lt hB.2.1 hB.2.2.2 (hμσ.trans hB.2.2.1))))
  ld := fun c hl hc => by
    obtain ⟨n, hn1, hn⟩ := hjB_cof hc
    obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := (hiGL n).ld c hl hn
    have hcpn : cp < (hiGL n).B := hcp.trans hn
    refine ⟨cp, lp, T, hcp, ?_, fun x hx hx1 hg => ?_, fun σ ρ hB hg => hex σ ρ hB ?_⟩
    · show (hiGL (hjN cp)).g cp ≤ (hiGL (hjN c)).g c
      rw [hj_g_eq hn1 hn, hj_g_eq hn1 hcpn]; exact hgcp
    · have hg' : (hiGL n).g c < x := by rw [← hj_g_eq hn1 hn]; exact hg
      show (hiGL (hjN c)).R c x = _ ∧ _
      rw [hj_R_eq hn1 hn, hj_R_eq hn1 hcpn]
      exact hdec x hx hx1 hg'
    · rw [← hj_g_eq hn1 hn]; exact hg

theorem hjU_B : hjU.B = veblen (Om1 + Om1) (gcG 0 + 1) := rfl

theorem hjU_γ : hjU.γ = 0 := rfl

theorem hjU_b (x : Ordinal.{0}) : hjU.b x = veblen (x + x) (lgG x + 1) := rfl

/-- **The union extends every `hiGL κ`, `κ < Ω₁`** (readings). -/
theorem hjU_R {κ c : Ordinal.{0}} (hκ : κ < Om1) (hc : c < (hiGL κ).B) (x : Ordinal.{0}) :
    hjU.R c x = (hiGL κ).R c x := hj_R_eq hκ hc x

/-- **The union extends every `hiGL κ`, `κ < Ω₁`** (gates). -/
theorem hjU_g {κ c : Ordinal.{0}} (hκ : κ < Om1) (hc : c < (hiGL κ).B) : hjU.g c = (hiGL κ).g c := hj_g_eq hκ hc

end Googology.Trans.PoR.InaccPsi.R2.Hj

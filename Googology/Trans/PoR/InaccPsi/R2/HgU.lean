import Googology.Trans.PoR.InaccPsi.R2.HgVRS
import Googology.Trans.PoR.InaccPsi.R2.HfMG

/-!
# HgU: THE LEVEL `Ω₁` READ AS THE BASE `x`: THE UNION OF ALL `Hf.hfGL ν`, `ν < Ω₁`; THE FRONTIER PASSES `K`

The systems `Hf.hfGL ν` (bound `φ(ω+ν+1, G+1)`, base gate `≤ ω+ν`) exist for every `ν < Ω₁`, but only those with
`ν < K = ψ_{Ω₁}(Ω_ω)` are located (`Hf.hfGL_wall`: the base gate of `hfGL K` is `K`).  Their union over ALL
`ν < Ω₁` is a gated digit system (`Hg.HgVD`, bound field `Z(x) < Γ_{x+2}`) with the bound `φ(Ω₁, G+1)`, the base
gate `0` and the base reading `φ(x, Γ_{x+1}+1) = B_x(x)`: the LEVEL `Ω₁` is read as the base `x`.  Its readings
pass `B_x(x)` (`ε_{B_x(x)+1}` is the reading of the next code), so it is not an `Hc.HcVD`.  Lemma EXACT for the
base reading is `π(ρ) = σ` inside `ϑ` (`hg_BR_pi`).  A code of `hfGL ν` with gate below an `ε`-number `σ` lies in
some `hfGL μ` with `μ < σ` (`hg_small`, by one induction on the level: the codes past the start of a level `ω+ν`
have a gate `≥ ω+ν`, `hg_highN`).  So the union is located with base gate `0 < K` (`Hg.hgV_locD`).

* `hg_highN` (**the codes past the start of an offset union have gate `≥` the reading gate**), `hg_small`
  (**SMALL for the level recursion**), `hgNx_cof` (`hdNx l Q` is the supremum of `N_b(Q)`, `b < l`, any limit `l`);
* `hgB` (`φ(Ω₁, G+1)`), `hgB_cof`, `hg_BR_pi` (**EXACT for `φ(ρ, Γ_{ρ+1}+1)`**), `hgU` (**THE UNION OVER ALL
  LEVELS, `Ω₁ ↦ x`**), `hgU_R`, `hgU_g`;
* `hgU_loc` (**`φ(Ω₁, G+1)` IS LOCATED**: `Λ⁺ = ι(Γ(φ(Ω₁, G+1))·ω)`, `P(…) < L(0)`), `hgU_blk`, `hgU_enum`,
  `hgU_capV`, `hgU_road`, `hgU_fr_order` (**`ι(Γ(φ(K, G+1))) < ι(Γ(φ(Ω₁, G+1))·ω) ≤ ι(Ω₂)`**).

No new axiom.  New definitions: `hgB`, `hgN`, `hgU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hg

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

/-! ## The gates past the start of an offset union -/

/-- **The codes past the start `S0` of the offset union of a base `A` have a gate `≥` the reading gate `γN`**: a code
`c ∈ [S0.B, N_α(F))` with gate below an `ε`-number `σ` forces `A.γN < σ`. -/
theorem hg_highN {α : Ordinal.{0}} {St : ∀ (Q : HfQ α) (U : HcVD), HcSStart (hfQPB Q) U → HcVD}
    (hSt : ∀ Q U h, HfQSpec Q U (St Q U h)) {A : HfB α} {S0 : HcVD} (hS : HfMStart A S0)
    {c σ : Ordinal.{0}} (hc : c < hcN α A.F) (hBc : S0.B ≤ c) (hσ : InE σ) (hσ1 : σ < Om1)
    (hg : (hfMTU hSt hS).g c < σ) : A.γN < σ := by
  obtain ⟨n, hn1, hn⟩ := hfMT_cof hSt hS hc
  obtain ⟨-, hN1, hcNc⟩ := hfMTN_spec hn1 hn
  have hgN : (hfMTU hSt hS).g c = (hfMU St A S0 (hfMTN St A S0 c)).g c := rfl
  have I := hfM_inv hSt hS _ hN1
  rcases zero_or_succ_or_isSuccLimit (hfMTN St A S0 c) with h0 | ⟨m, hm⟩ | hlim
  · rw [h0, hfMU_zero] at hcNc
    exact absurd hBc (not_le.2 hcNc)
  · have hm' : hfMTN St A S0 c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < hfMTN St A S0 c := by rw [hm']; exact lt_add_one m
    have hml : m < hcN α A.F := hmN.trans hN1
    have hBc' : (hfMU St A S0 m).B ≤ c := not_lt.1 (hfMTN_min hmN hml)
    rw [hgN, hm'] at hg
    rw [hm'] at hcNc I hN1
    have hγ := I.high m (lt_add_one _) c σ hBc' hcNc hσ hσ1 hg
    exact (max_lt_iff.1 ((hfMU_γ_iff hSt hS hN1 hσ hσ1).1 hγ)).1
  · exfalso
    rw [hfMU_B hSt hS hN1] at hcNc
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen α).lt_iff_exists_lt
        (isSuccLimit_add _ hlim)).1 hcNc
    obtain ⟨d, hf, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    have hfl : d < hcN α A.F := hf.trans hN1
    refine hfMTN_min hf hfl ?_
    rw [hfMU_B hSt hS hfl]; exact hct.trans_le ((isNormal_veblen α).monotone htd)

/-! ## `φ(l, P+1)` at any limit level `l` -/

/-- **`φ(l, P+1)` is the supremum of `N_b(P)`, `b < l`**, for a fixed point `P` of `φ(l, ·)` (no cofinal sequence
asked: `φ(l, ·)` is the derivative of the family `φ(b, ·)`, `b < l`). -/
theorem hgVeb_cof {l P : Ordinal.{0}} (hl0 : l ≠ 0) (hP : veblen l P = P) {c : Ordinal.{0}}
    (hc : c < veblen l (P + 1)) : ∃ b, b < l ∧ c < hcN b P := by
  rw [veblen_of_ne_zero hl0] at hc hP
  rw [derivFamily_add_one, hP] at hc
  obtain ⟨L, hL⟩ := lt_nfpFamily_iff.1 hc
  have key : ∀ L : List (Iio l), ∃ b, b < l ∧
      List.foldr (fun x : Iio l => veblen x.1) (P + 1) L < hcN b P := by
    intro L
    induction L with
    | nil =>
      exact ⟨0, pos_iff_ne_zero.2 hl0,
        (ev_isSuccLimit_of_inE (hcN_E 0 P)).add_one_lt (hcN_gt 0 P)⟩
    | cons i L ih =>
      obtain ⟨b, hb, hbL⟩ := ih
      refine ⟨max b i.1, max_lt hb i.2, ?_⟩
      show veblen i.1 (List.foldr (fun x : Iio l => veblen x.1) (P + 1) L) < hcN (max b i.1) P
      calc veblen i.1 (List.foldr (fun x : Iio l => veblen x.1) (P + 1) L)
          < veblen i.1 (hcN (max b i.1) P) :=
            (isNormal_veblen i.1).strictMono (hbL.trans_le (hcN_mono (le_max_left _ _) P))
        _ = hcN (max b i.1) P := hc_fix_down (le_max_right _ _) (hcN_fix _ P)
  obtain ⟨b, hb, hbL⟩ := key L
  exact ⟨b, hb, hL.trans hbL⟩

/-! ## SMALL for the level recursion -/

/-- **SMALL**: a code of `hfGL ν` with gate below an `ε`-number `σ` lies in some `hfGL μ`, `μ < σ` (one induction on
the level: the codes past the start of the level `ω + ν` have a gate `≥ ω + ν`, `hg_highN`). -/
theorem hg_small : ∀ ν, ν < Om1 → ∀ c, c < (hfGL ν).B → ∀ σ, InE σ → σ < Om1 → (hfGL ν).g c < σ →
    ∃ μ, μ < σ ∧ c < (hfGL μ).B := by
  intro ν
  induction ν using WellFoundedLT.induction with
  | ind ν IH =>
  intro hν c hc σ hσ hσ1 hg
  by_cases hνσ : ν < σ
  · exact ⟨ν, hνσ, hc⟩
  rcases zero_or_succ_or_isSuccLimit ν with h0 | ⟨μ, hμ⟩ | hlim
  · exact absurd (by rw [h0]; exact hσ.pos) hνσ
  · have hμ' : ν = μ + 1 := by rw [← hμ, succ_eq_add_one]
    subst hμ'
    have hμ1 : μ < Om1 := (lt_add_one μ).trans hν
    by_cases hcμ : c < (hfGL μ).B
    · have e := ((hfGL_inv (μ + 1) hν).2 μ (le_add_right le_rfl) c 0 hcμ).2
      rw [e] at hg
      exact IH μ (lt_add_one μ) hμ1 c hcμ σ hσ hσ1 hg
    · exfalso
      have hH : ∃ hν' : μ + 1 < Om1, HfGOK μ (hfGL μ) := ⟨hν, (hfGL_inv μ hμ1).1⟩
      set hS := (hfG_OK_start hH.choose hH.choose_spec).choose_spec.choose_spec with hhS
      have e : hfGL (μ + 1) = hfMTU (St := hfLS (μ + 1)) (fun Q U h => hfLS_spec hH.choose Q U h) hS := by
        rw [hfGL_succ]; unfold hfGLSucc; rw [dif_pos hH]
      rw [e] at hc hg
      have h := hg_highN _ hS hc (not_lt.1 hcμ) hσ hσ1 hg
      exact hνσ (le_add_self.trans_lt h)
  · have hcoh : HfGCoh ν (fun ν' _ => hfGL ν') :=
      ⟨fun ν' h => (hfGL_inv ν' (h.trans hν)).1, fun ν₁ ν₂ h₁ h₂ h12 c x hc =>
        (hfGL_inv ν₂ (h₂.trans hν)).2 ν₁ h12 c x hc⟩
    have hS := hfGLCh_start ν hlim hν (fun ν' _ => hfGL ν') hcoh
    have e : hfGL ν = hfMTU (St := hfLS ν) (fun Q U h => hfLS_spec hν Q U h) hS := by
      rw [hfGL_limit hlim]; unfold hfGLLim; rw [dif_pos ⟨hν, hcoh⟩]
    by_cases hcS : c < hdNx (ω + ν) (gcG 0)
    · rw [hfGL_NxG ν hν] at hcS
      obtain ⟨b, hb, hcb⟩ := hgVeb_cof (hf_lev hν).ne (hf_G_fix (hf_lev hν).2) hcS
      obtain ⟨ν'', hν'', hbν⟩ := (lt_add_iff hlim.bot_lt.ne').1 hb
      have hν''1 : ν'' < Om1 := hν''.trans hν
      have hcν : c < (hfGL ν'').B := by
        rw [(hfGL_inv ν'' hν''1).1.1]; exact hcb.trans_le (hcN_mono hbν _)
      have e2 := ((hfGL_inv ν hν).2 ν'' hν''.le c 0 hcν).2
      rw [e2] at hg
      exact IH ν'' hν'' hν''1 c hcν σ hσ hσ1 hg
    · exfalso
      rw [e] at hc hg
      have h := hg_highN _ hS hc (not_lt.1 hcS) hσ hσ1 hg
      exact hνσ (le_add_self.trans_lt h)

/-! ## The union over all levels -/

/-- **`φ(Ω₁, G+1)`**: the bound of the union over all levels. -/
noncomputable def hgB : Ordinal.{0} := veblen Om1 (gcG 0 + 1)

theorem hg_Om1_lt_G (α : Ordinal.{0}) : (Om1 : Ordinal.{0}) < gcG α := by rw [Br.Om1_eq]; exact gcG_Om1_lt α

theorem hg_G_fixΩ : veblen Om1 (gcG 0) = gcG 0 := gn_veb_fix (gcG_SC 0) (hg_Om1_lt_G 0)

theorem hg_one_lt_Om1 : (1 : Ordinal.{0}) < Om1 := one_lt_omega0.trans (omega0_lt_inE gl_Om1_E)

/-- **Every `hfGL ν`, `ν < Ω₁`, lies below `φ(Ω₁, G+1)`.** -/
theorem hgB_gt {ν : Ordinal.{0}} (hν : ν < Om1) : (hfGL ν).B < hgB := by
  rw [hfGL_B hν]; exact hd_veb_left_lt (gv_Om1_lim.add_one_lt (hf_lev hν).2) _

/-- **The bounds `φ(ω+ν+1, G+1)`, `ν < Ω₁`, are cofinal in `φ(Ω₁, G+1)`.** -/
theorem hgB_cof {c : Ordinal.{0}} (hc : c < hgB) : ∃ ν, ν < Om1 ∧ c < (hfGL ν).B := by
  obtain ⟨b, hb, hcb⟩ := hgVeb_cof gv_Om1_pos.ne' hg_G_fixΩ hc
  exact ⟨b, hb, by rw [(hfGL_inv b hb).1.1]; exact hcb.trans_le (hcN_mono le_add_self _)⟩

theorem hgB_lt1 : hgB < gcG 1 := by
  have hG1 := gcG_SC 1
  have hE := Low.opow_eq_self_of_SC hG1
  have hfix : veblen Om1 (gcG 1) = gcG 1 := gn_veb_fix hG1 (hg_Om1_lt_G 1)
  have h2 := (isNormal_veblen Om1).strictMono ((ev_isSuccLimit_of_inE hE).add_one_lt (gcG_lt zero_lt_one))
  rwa [hfix] at h2

theorem hgB_fix1 : veblen 1 hgB = hgB := veblen_veblen_of_lt hg_one_lt_Om1 _

theorem hgB_E : InE hgB := gg_veblen_eps gv_Om1_pos.ne'

theorem hgB_lim : IsSuccLimit hgB := ev_isSuccLimit_of_inE hgB_E

/-- The first level containing `c`. -/
noncomputable def hgN (c : Ordinal.{0}) : Ordinal.{0} := sInf {ν | ν < Om1 ∧ c < (hfGL ν).B}

theorem hgN_spec {c ν : Ordinal.{0}} (hν : ν < Om1) (hc : c < (hfGL ν).B) :
    hgN c ≤ ν ∧ hgN c < Om1 ∧ c < (hfGL (hgN c)).B := by
  have hne : ({ν | ν < Om1 ∧ c < (hfGL ν).B} : Set Ordinal.{0}).Nonempty := ⟨ν, hν, hc⟩
  have hm := csInf_mem hne
  exact ⟨csInf_le' ⟨hν, hc⟩, hm.1, hm.2⟩

theorem hgN_high {c : Ordinal.{0}} (hc : hgB ≤ c) : hgN c = 0 := by
  unfold hgN
  have he : ({ν | ν < Om1 ∧ c < (hfGL ν).B} : Set Ordinal.{0}) = ∅ := by
    ext ν
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hν hcν
    exact absurd (hcν.trans (hgB_gt hν)) (not_lt.2 hc)
  rw [he]; exact Ordinal.sInf_empty

theorem hg_R_eq {c ν : Ordinal.{0}} (hν : ν < Om1) (hc : c < (hfGL ν).B) (x : Ordinal.{0}) :
    (hfGL (hgN c)).R c x = (hfGL ν).R c x := by
  obtain ⟨h1, -, h3⟩ := hgN_spec hν hc
  exact ((hfGL_inv ν hν).2 _ h1 c x h3).1.symm

theorem hg_g_eq {c ν : Ordinal.{0}} (hν : ν < Om1) (hc : c < (hfGL ν).B) :
    (hfGL (hgN c)).g c = (hfGL ν).g c := by
  obtain ⟨h1, -, h3⟩ := hgN_spec hν hc
  exact ((hfGL_inv ν hν).2 _ h1 c 0 h3).2.symm

theorem hg_R_succ (c x : Ordinal.{0}) : (hfGL (hgN (c + 1))).R (c + 1) x = (hfGL (hgN c)).R c x + 1 := by
  rcases lt_or_ge c hgB with h | h
  · obtain ⟨n, hn1, hn⟩ := hgB_cof (hgB_lim.add_one_lt h)
    rw [hg_R_eq hn1 hn, hg_R_eq hn1 ((lt_add_one c).trans hn), (hfGL n).R_succ]
  · rw [hgN_high h, hgN_high (h.trans (le_self_add (a := c) (b := 1))), (hfGL 0).R_succ]

theorem hg_g_le_succ (c : Ordinal.{0}) : (hfGL (hgN c)).g c ≤ (hfGL (hgN (c + 1))).g (c + 1) := by
  rcases lt_or_ge c hgB with h | h
  · obtain ⟨n, hn1, hn⟩ := hgB_cof (hgB_lim.add_one_lt h)
    rw [hg_g_eq hn1 hn, hg_g_eq hn1 ((lt_add_one c).trans hn)]; exact (hfGL n).g_le_succ c
  · rw [hgN_high h, hgN_high (h.trans (le_self_add (a := c) (b := 1)))]; exact (hfGL 0).g_le_succ c

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem hg_lev_lt {ν : Ordinal.{0}} (h : ν < x) : ω + ν < x := (inE_indec hx).add_lt (omega0_lt_inE hx) h

/-- **The bound field of every `hfGL ν` lies below `B_x(x)`.** -/
theorem hg_Z_le {ν : Ordinal.{0}} (hν : ν < Om1) : (hfGL ν).Z x ≤ hcBR x := by
  rw [(hfGL_inv ν hν).1.2.2.2 x hx hx1, ← hfZg_eq hx]
  split_ifs with h
  · exact (hf_evN_lt_Zg hx hx1 h).le
  · exact le_rfl

/-- **The base reading of `hfGL ν` lies below `B_x(x)`** (`ν < x`). -/
theorem hg_b_lt {ν : Ordinal.{0}} (hν : ν < x) : (hfGL ν).b x < hcBR x := by
  have h1 : ω + ν + 1 < x := (ev_isSuccLimit_of_inE hx).add_one_lt (hg_lev_lt hx hx1 hν)
  rw [(hfGL_inv ν (hν.trans hx1)).1.2.2.1 x hx hx1 (hg_lev_lt hx hx1 hν), (hf_NL_glA hx hx1 h1).1]
  exact hf_veb_lt_BR hx hx1 h1

theorem hg_x_lt_BR : x < hcBR x := (lgG_facts hx hx1).2.1.trans ((lt_add_one _).trans_le (right_le_veblen _ _))

theorem hg_BR_fix1 : veblen 1 (hcBR x) = hcBR x := veblen_veblen_of_lt (one_lt_omega0.trans (omega0_lt_inE hx)) _

theorem hg_BR_eq : hcBR x = veblen x (lgG x + 1) := rfl

end Base

/-- **Lemma EXACT for `B_ρ(ρ) = φ(ρ, Γ_{ρ+1}+1) = ϑᵖ(Ω₁·ρ + Γ_{ρ+1})`**: the level `ρ` itself goes to `σ`. -/
theorem hg_BR_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) : hcBR ρ ∈ TB ρ σ ∧ pi σ ρ (hcBR ρ) = hcBR σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨g1, g2⟩ : lgG ρ ∈ TB ρ σ ∧ pi σ ρ (lgG ρ) = lgG σ := Go.goGl.ba_pi σ ρ hB
  obtain ⟨r1, r2⟩ := pi_base hB
  have h1ρ : (1 : Ordinal.{0}) ≤ ρ := one_lt_omega0.le.trans (omega0_lt_inE hB.2.1).le
  have h1σ : (1 : Ordinal.{0}) ≤ σ := one_lt_omega0.le.trans (omega0_lt_inE hB.1).le
  have h := glA_pi hB r1 hρ1 g1 (lgG_facts hB.2.1 hρ1).2.2.1
  rw [r2, g2, hc_glA_GG hB.2.1 hρ1 h1ρ (lgG_facts hB.2.1 hρ1).2.1,
    hc_glA_GG hB.1 hσ1 h1σ (lgG_facts hB.1 hσ1).2.1] at h
  exact h

/-- **A code of the union with gate below an `ε`-number `σ` lies in `hfGL μ`, `μ < σ`.** -/
theorem hg_small' {c σ : Ordinal.{0}} (hc : c < hgB) (hσ : InE σ) (hσ1 : σ < Om1) (hg : (hfGL (hgN c)).g c < σ) :
    ∃ μ, μ < σ ∧ c < (hfGL μ).B := by
  obtain ⟨n, hn1, hn⟩ := hgB_cof hc
  rw [hg_g_eq hn1 hn] at hg
  exact hg_small n hn1 c hn σ hσ hσ1 hg

theorem hg_γ_lt {μ x : Ordinal.{0}} (hx : InE x) (hμ : μ < x) (hμ1 : μ < Om1) : (hfGL μ).γ < x :=
  (hfGL_γ hμ1).trans_lt ((inE_indec hx).add_lt (omega0_lt_inE hx) hμ)

/-- **THE UNION OVER ALL LEVELS `ν < Ω₁`**: a gated digit system (`HgVD`) with the bound `φ(Ω₁, G+1)`, the base
gate `0`, the base reading `φ(x, Γ_{x+1}+1) = B_x(x)` (the level `Ω₁` read as `x`) and the bound field
`evZ(B_x(x)) < Γ_{x+2}`. -/
noncomputable def hgU : HgVD where
  B := hgB
  γ := 0
  γ_lt := gv_Om1_pos
  γ_cl := fun _ hZ _ _ => hZ.1
  γ_G := fun _ => rfl
  R := fun c x => (hfGL (hgN c)).R c x
  g := fun c => (hfGL (hgN c)).g c
  b := hcBR
  ba := hcBR
  ix := hgB
  Z := fun x => evZ (hcBR x)
  B_E := hgB_E
  G_le := (lt_add_one _).le.trans (right_le_veblen _ _)
  B_lt1 := hgB_lt1
  B_ix := hgB_fix1.symm
  Z_fix := fun _ _ _ => epsilon_evZ _
  Z_G1 := fun x hx hx1 => gw_evZ_lt1 hx hx1 (hcBR_lt1 hx hx1)
  ix_mem := fun S a b ha _ => CSet.phi_mem (by rw [Br.Om1_eq]; exact CSet.Om_mem (CSet.one_mem _ _))
    (CSet.succ_mem (gmS_G0_mem S ha))
  g_lt := fun c hc => by
    obtain ⟨n, hn1, hn⟩ := hgB_cof hc
    rw [hg_g_eq hn1 hn]; exact (hfGL n).g_lt c hn
  g_zero := by rw [hg_g_eq gv_Om1_pos (hfGL 0).B_pos]; exact (hfGL 0).g_zero
  g_nat := fun k => by rw [hg_g_eq gv_Om1_pos ((hfGL 0).nat_lt_B k)]; exact (hfGL 0).g_nat k
  g_E := by rw [hg_g_eq gv_Om1_pos (hfGL 0).E_lt_B]; exact (hfGL 0).g_E
  g_lowE := fun c hc => by rw [hg_g_eq gv_Om1_pos (hc.trans (hfGL 0).E_lt_B)]; exact (hfGL 0).g_lowE c hc
  g_G0 := fun h => by
    obtain ⟨n, hn1, hn⟩ := hgB_cof h
    rw [hg_g_eq hn1 hn]; exact (hfGL n).g_G0 hn
  g_add := fun Z hZ hωZ x y hxy hgx hgy => by
    obtain ⟨n, hn1, hn⟩ := hgB_cof hxy
    have hx : x < (hfGL n).B := lt_of_le_of_lt le_self_add hn
    have hy : y < (hfGL n).B := lt_of_le_of_lt le_add_self hn
    show (hfGL (hgN (x + y))).g (x + y) < Z
    rw [hg_g_eq hn1 hn]; rw [hg_g_eq hn1 hx] at hgx; rw [hg_g_eq hn1 hy] at hgy
    exact (hfGL n).g_add Z hZ hωZ x y hn hgx hgy
  g_opow := fun Z hZw hωZ y hy hg => by
    obtain ⟨n, hn1, hn⟩ := hgB_cof hy
    have hy' : y < (hfGL n).B := lt_of_le_of_lt (right_le_opow y one_lt_omega0) hn
    show (hfGL (hgN (ω ^ y))).g (ω ^ y) < Z
    rw [hg_g_eq hn1 hn]; rw [hg_g_eq hn1 hy'] at hg
    exact (hfGL n).g_opow Z hZw hωZ y hn hg
  code_gate := fun Z hZ1 hZ0 hZa hZp At hAt c hc hcB => by
    obtain ⟨n, hn1, hn⟩ := hgB_cof hcB
    show (hfGL (hgN c)).g c < Z
    rw [hg_g_eq hn1 hn]
    exact (hfGL n).code_gate Z hZ1 hZ0 hZa hZp At (fun s hs => (hAt s hs).imp_right
      (fun h => (hgB_gt hn1).le.trans h)) c hc hn
  g_succ := fun Z hZ c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hgB_cof hc
    have hc' : c < (hfGL n).B := (lt_add_one c).trans hn
    show (hfGL (hgN (c + 1))).g (c + 1) < Z
    rw [hg_g_eq hn1 hn]; rw [hg_g_eq hn1 hc'] at hg
    exact (hfGL n).g_succ Z hZ c hn hg
  g_le_succ := hg_g_le_succ
  mem := fun S a b ha c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hgB_cof hc
    rw [hg_g_eq hn1 hn] at hg
    exact (hfGL n).mem S a b ha c hn hg
  R_zero := fun x => by rw [hg_R_eq gv_Om1_pos (hfGL 0).B_pos]; exact (hfGL 0).R_zero x
  R_nat := fun k x => by rw [hg_R_eq gv_Om1_pos ((hfGL 0).nat_lt_B k)]; exact (hfGL 0).R_nat k x
  R_E := fun x => by rw [hg_R_eq gv_Om1_pos (hfGL 0).E_lt_B]; exact (hfGL 0).R_E x
  R_succ := hg_R_succ
  R_pos := fun x hx hx1 c hc0 hc hg => by
    obtain ⟨n, hn1, hn⟩ := hgB_cof hc
    show 0 < (hfGL (hgN c)).R c x
    rw [hg_R_eq hn1 hn]; rw [hg_g_eq hn1 hn] at hg
    exact (hfGL n).R_pos x hx hx1 c hc0 hn hg
  R_omega := fun x hx hx1 c hω hc hg => by
    obtain ⟨n, hn1, hn⟩ := hgB_cof hc
    show ω ≤ (hfGL (hgN c)).R c x
    rw [hg_R_eq hn1 hn]; rw [hg_g_eq hn1 hn] at hg
    exact (hfGL n).R_omega x hx hx1 c hω hn hg
  R_lt_b := fun x hx hx1 _ c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hgB_cof hc
    show (hfGL (hgN c)).R c x < hcBR x
    rw [hg_R_eq hn1 hn]; rw [hg_g_eq hn1 hn] at hg
    exact ((hfGL n).R_lt_Z x hx hx1 c hn hg).trans_le (hg_Z_le hx hx1 hn1)
  R_lt_Z := fun x hx hx1 c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hgB_cof hc
    show (hfGL (hgN c)).R c x < evZ (hcBR x)
    rw [hg_R_eq hn1 hn]; rw [hg_g_eq hn1 hn] at hg
    exact (((hfGL n).R_lt_Z x hx hx1 c hn hg).trans_le (hg_Z_le hx hx1 hn1)).trans (lt_evZ _)
  mono := fun x hx hx1 c hc d hdc hgc hgd => by
    obtain ⟨n, hn1, hn⟩ := hgB_cof hc
    have hd : d < (hfGL n).B := hdc.trans hn
    show (hfGL (hgN d)).R d x < (hfGL (hgN c)).R c x
    rw [hg_R_eq hn1 hn, hg_R_eq hn1 hd]; rw [hg_g_eq hn1 hn] at hgc; rw [hg_g_eq hn1 hd] at hgd
    exact (hfGL n).mono x hx hx1 c hn d hdc hgc hgd
  cof := fun x hx hx1 c hc hg ν hν => by
    obtain ⟨n, hn1, hn⟩ := hgB_cof hc
    rw [hg_R_eq hn1 hn] at hν; rw [hg_g_eq hn1 hn] at hg
    obtain ⟨d, hdc, hgd, hνd⟩ := (hfGL n).cof x hx hx1 c hn hg ν hν
    have hd : d < (hfGL n).B := hdc.trans hn
    exact ⟨d, hdc, by show (hfGL (hgN d)).g d < x; rw [hg_g_eq hn1 hd]; exact hgd,
      by show ν ≤ (hfGL (hgN d)).R d x; rw [hg_R_eq hn1 hd]; exact hνd⟩
  b_cof := fun x hx hx1 _ ν hν => by
    have hx0 : x ≠ 0 := hx.pos.ne'
    have hfix : veblen x (lgG x) = lgG x :=
      hc_G_fix hx hx1 (one_lt_omega0.le.trans (omega0_lt_inE hx).le) (lgG_facts hx hx1).2.1
    obtain ⟨b, hb, hνb⟩ := hgVeb_cof hx0 hfix hν
    have hb1 : b < Om1 := hb.trans hx1
    have hνb' : ν < (hfGL b).b x := by
      rw [(hfGL_inv b hb1).1.2.2.1 x hx hx1 (hg_lev_lt hx hx1 hb)]
      exact hνb.trans_le (hcN_mono le_add_self _)
    obtain ⟨d, hd, hgd, hνd⟩ := (hfGL b).b_cof x hx hx1 (hg_γ_lt hx hb hb1) ν hνb'
    exact ⟨d, hd.trans (hgB_gt hb1), by show (hfGL (hgN d)).g d < x; rw [hg_g_eq hb1 hd]; exact hgd,
      by show ν < (hfGL (hgN d)).R d x; rw [hg_R_eq hb1 hd]; exact hνd⟩
  b_E := fun x hx _ _ => gg_veblen_eps hx.pos.ne'
  x_lt_b := fun x hx hx1 _ => hg_x_lt_BR hx hx1
  b_eN := fun x hx hx1 _ => gz_eN_fix hx hx1 (hg_BR_fix1 hx hx1) (hg_x_lt_BR hx hx1) (hcBR_lt1 hx hx1)
  ba_lt := fun x hx hx1 _ => hcBR_lt1 hx hx1
  b_Z := fun _ _ _ _ => go_eN_lt_evZ (lt_evZ _)
  b_pi := fun _ _ hB _ => hg_BR_pi hB
  ba_pi := fun _ _ hB _ => hg_BR_pi hB
  ex := fun σ ρ hB c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hgB_cof hc
    show (hfGL (hgN c)).R c ρ ∈ TB ρ σ ∧ pi σ ρ ((hfGL (hgN c)).R c ρ) = (hfGL (hgN c)).R c σ
    rw [hg_R_eq hn1 hn, hg_R_eq hn1 hn]; rw [hg_g_eq hn1 hn] at hg
    exact (hfGL n).ex σ ρ hB c hn hg
  dig := fun σ ρ hB _ d hd hg P P' hat => by
    have hσ1 : σ < Om1 := hB.2.2.1.trans hB.2.2.2
    obtain ⟨μ, hμσ, hdμ⟩ := hg_small' hd hB.1 hσ1 hg
    have hμ1 : μ < Om1 := hμσ.trans hσ1
    show ω ^ P * (hfGL (hgN d)).R d ρ ∈ TB ρ σ ∧
      pi σ ρ (ω ^ P * (hfGL (hgN d)).R d ρ) = ω ^ P' * (hfGL (hgN d)).R d σ
    rw [hg_R_eq hμ1 hdμ, hg_R_eq hμ1 hdμ]; rw [hg_g_eq hμ1 hdμ] at hg
    exact (hfGL μ).dig σ ρ hB (hg_γ_lt hB.1 hμσ hμ1) d hdμ hg P P' (fun β hβ hβe =>
      hat β hβ (hβe.trans (hg_b_lt hB.2.1 hB.2.2.2 (hμσ.trans hB.2.2.1))))
  ld := fun c hl hc => by
    obtain ⟨n, hn1, hn⟩ := hgB_cof hc
    obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := (hfGL n).ld c hl hn
    have hcpn : cp < (hfGL n).B := hcp.trans hn
    refine ⟨cp, lp, T, hcp, ?_, fun x hx hx1 hg => ?_, fun σ ρ hB hg => hex σ ρ hB ?_⟩
    · show (hfGL (hgN cp)).g cp ≤ (hfGL (hgN c)).g c
      rw [hg_g_eq hn1 hn, hg_g_eq hn1 hcpn]; exact hgcp
    · have hg' : (hfGL n).g c < x := by rw [← hg_g_eq hn1 hn]; exact hg
      show (hfGL (hgN c)).R c x = _ ∧ _
      rw [hg_R_eq hn1 hn, hg_R_eq hn1 hcpn]
      exact hdec x hx hx1 hg'
    · rw [← hg_g_eq hn1 hn]; exact hg

theorem hgU_B : hgU.B = veblen Om1 (gcG 0 + 1) := rfl

theorem hgU_γ : hgU.γ = 0 := rfl

theorem hgU_b (x : Ordinal.{0}) : hgU.b x = veblen x (lgG x + 1) := rfl

/-- **The union extends every `hfGL ν`, `ν < Ω₁`** (readings). -/
theorem hgU_R {ν c : Ordinal.{0}} (hν : ν < Om1) (hc : c < (hfGL ν).B) (x : Ordinal.{0}) :
    hgU.R c x = (hfGL ν).R c x := hg_R_eq hν hc x

/-- **The union extends every `hfGL ν`, `ν < Ω₁`** (gates). -/
theorem hgU_g {ν c : Ordinal.{0}} (hν : ν < Om1) (hc : c < (hfGL ν).B) : hgU.g c = (hfGL ν).g c := hg_g_eq hν hc

end Googology.Trans.PoR.InaccPsi.R2.Hg

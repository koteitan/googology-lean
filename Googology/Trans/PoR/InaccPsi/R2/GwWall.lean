import Googology.Trans.PoR.InaccPsi.R2.GwFr

/-!
# THE WALL `ζ_{G+1}`: no gated digit system extending the recursion has the code `ζ_{G+1}`

The readings of the tower codes `t_k` (`Gw.gwT`) at an `ε`-number base `x` are `r₀ = 1`, `r_{k+1} = φ(1, Γ_{x+1} + r_k)`
(`gwRR_succ`: the reading of the bound `B` in the step is the base reading `b(x)`, `Gv.GvD.hR_pow`), and they are
cofinal in `ζ_{Γ_{x+1}+1} = evZ(Γ_{x+1})` (`gwRR_cof`).  A gated digit system (`Gv.GvD`) that reads the tower codes
as the recursion does and contains `ζ_{G+1}` as a code with gate below `x` would read `ζ_{G+1}` above every `r_k`
(monotonicity), i.e. at least `ζ_{Γ_{x+1}+1}`, against its field `R_lt_Z` (`gw_wall`).  So the recursion `Gw.gwD`
stops exactly at the index `ζ_{G+1}`; passing it needs a digit structure whose readings may reach `ζ_{Γ_{x+1}+1}` and
beyond (Lemma IMG there is `Gw.gwImg_Zn`), and a union at `ζ_{G+1}` that reads its own index (no earlier system has
it as a code: every bound `ε_{G+c}`, `c < ζ_{G+1}`, is below `ζ_{G+1}`, `gw_B_lt_Z`).

* `gwRR`, `gwRR_zero`, `gwRR_g`, `gwRR_succ`, `gwRR_cof`, `gw_B_lt_Z`, `gw_wall` (**THE WALL**).

No new axiom.  New definition: `gwRR`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gw

open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Gp Googology.Trans.PoR.InaccPsi.R2.Go
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **The reading of the tower code `t_k`** at the base `x` (in `gwD t_k`). -/
noncomputable def gwRR (k : ℕ) (x : Ordinal.{0}) : Ordinal.{0} := (gwD (gwT k)).R (gwT k) x

theorem gwRR_zero (x : Ordinal.{0}) : gwRR 0 x = 1 := (gwD 1).R_one x

/-- **Every bound of the recursion is below `ζ_{G+1}`.** -/
theorem gw_B_lt_Z {c : Ordinal.{0}} (hc : c < evZ (gcG 0)) : (gwD c).B < evZ (gcG 0) := by
  rw [gw_B hc]; exact gw_veb_lt_Z hc

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem gwRR_g (k : ℕ) : (gwD (gwT k)).g (gwT k) < x :=
  (gw_γ_iff (gwT_lt k) hx hx1).1 (gwT_gate k x hx hx1)

/-- **`r_{k+1} = φ(1, Γ_{x+1} + r_k)`.** -/
theorem gwRR_succ (k : ℕ) : gwRR (k + 1) x = veblen 1 (gpI x + gwRR k x) := by
  set a := gwT k with ha
  have haZ : a < evZ (gcG 0) := gwT_lt k
  have hμ : gwT (k + 1) = (gwD a).B := (gwT_B k).symm
  have hμZ : gwT (k + 1) < evZ (gcG 0) := gwT_lt (k + 1)
  have ha1 : a + 1 ≤ gwT (k + 1) := Order.add_one_le_of_lt (by rw [hμ]; exact gw_self haZ)
  have ha1Z : a + 1 < evZ (gcG 0) := (ev_isSuccLimit_of_inE (evZ_E _)).add_one_lt haZ
  have hμB : gwT (k + 1) < (gwD (a + 1)).B := by
    rw [gw_B ha1Z]
    show veblen 1 (gcG 0 + a) < _
    exact (isNormal_veblen 1).strictMono ((add_lt_add_iff_left _).2 (lt_add_one a))
  have hγ : (gwD a).γ < x := gwT_gate k x hx hx1
  unfold gwRR
  rw [(gw_ext ha1 hμZ).1 _ x hμB, gwD_succ]
  show (gwD a).step.R (gwT (k + 1)) x = _
  have h1 : (1 : Ordinal.{0}) < (gwD a).NB := (gwD a).one_lt_B.trans (gwD a).B_lt_NB
  have hpow := (gwD a).hR_pow one_ne_zero h1 x
  rw [opow_one, (gwD a).hR_one, opow_one] at hpow
  rw [GvD.step_R, hμ, hpow, gw_b haZ hx hx1 hγ]

theorem gwRR_iter (n : ℕ) : Ordinal.epsilon^[n] (lgG x + 1) ≤ gwRR (n + 1) x := by
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply, gwRR_succ hx hx1 0, gwRR_zero]
    have e : veblen 1 (gpI x) = lgG x := epsilon_evIx (lgG_facts hx hx1).2.2.2.1
    rw [← go_eN_veb, e]
    exact Order.add_one_le_of_lt (lt_eN _)
  | succ n ih =>
    rw [Function.iterate_succ_apply', gwRR_succ hx hx1 (n + 1)]
    show veblen 1 _ ≤ _
    exact (isNormal_veblen 1).monotone (ih.trans le_add_self)

/-- **The tower readings are cofinal in `ζ_{Γ_{x+1}+1}`.** -/
theorem gwRR_cof {t : Ordinal.{0}} (ht : t < evZ (lgG x)) : ∃ k : ℕ, t < gwRR k x := by
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 ht
  exact ⟨n + 1, hn.trans_le (gwRR_iter hx hx1 n)⟩

end Base

/-- **THE WALL**: a gated digit system that reads the tower codes `t_k` as the recursion does (readings and gates)
cannot contain the code `ζ_{G+1}` with gate below an `ε`-number base `x`. -/
theorem gw_wall (D : GvD) (hR : ∀ (k : ℕ) (x : Ordinal.{0}), D.R (gwT k) x = gwRR k x)
    (hg : ∀ k : ℕ, D.g (gwT k) = (gwD (gwT k)).g (gwT k)) (hZ : evZ (gcG 0) < D.B) {x : Ordinal.{0}} (hx : InE x)
    (hx1 : x < Om1) (hgZ : D.g (evZ (gcG 0)) < x) : False := by
  have hlt := D.R_lt_Z x hx hx1 _ hZ hgZ
  obtain ⟨k, hk⟩ := gwRR_cof hx hx1 hlt
  have hmono := D.mono x hx hx1 (evZ (gcG 0)) hZ (gwT k) (gwT_lt k) hgZ
    (by rw [hg]; exact gwRR_g hx hx1 k)
  rw [hR] at hmono
  exact absurd hk (not_lt.2 hmono.le)

end Googology.Trans.PoR.InaccPsi.R2.Gw

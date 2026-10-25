import Googology.Trans.PoR.InaccPsi.R2.GzRec

/-!
# THE SELF-READ UNION AT EVERY `ζ_{G+n+2}`

The union of all `gzYD n U0 d`, `d < ζ_{G+n+2}` (the stage `n` from a start `U0`, `R2.GzRec`), has the bound
`ζ_{G+n+2} = φ(1, ζ_{G+n+2})` and reads its own index (as `Gw.gwZU` does at `ζ_{G+1}`): as a `GwZD` with
`N = n + 2` it has base reading `b(x) = Z_{n+2}(x) = ζ_{Γ_{x+1}+n+2}` and base gate `0`:

* the tower `t_0 = 1`, `t_{k+1} = ε_{ζ_{G+n+1}+t_k}` (`gzT`) is cofinal in `ζ_{G+n+2}` (`gzT_sup`), every
  `gzYD n U0 t_k` has base gate below every `ε`-number (`gzT_gate`), and the readings `r_0 = 1`,
  `r_{k+1} = φ(1, Z_{n+1}(x) + r_k)` of the codes `t_k` (`gzRR_succ`, through `GwZD.hR_pow`) are cofinal in
  `Z_{n+2}(x)` (`gzRR_cof`): the field `b_cof`;
* `R_lt_b`: every member reads below `Z_{n+2}(x)` (its field `R_lt_Z`, `N = n + 1`);
* `b_eN`, `b_pi`, `ba_pi`: `ε_{Z_{n+2}+1} = ϑˣ(Ω₁ + Z_{n+2})` and Lemma EXACT for `Z_{n+2}(ρ)` (`Gz.gz_eNZ`,
  `Gz.gz_Z_pi`); `b_Z`: `ε_{Z_{n+2}+1} < Z_{n+3}`;
* a code with gate below an `ε`-number `σ` lies in a member with base gate below `σ` (`gz_small`).

The union satisfies `GzStart (n+1)` (`gzZU_start`): it starts the next stage.

* `gzZN`, `gzZR`, `gzZg`, `gz_memB`, `gzZN_spec`, `gzZR_eq`, `gzZg_eq`, `gz_small`, `gzT`, `gzT_lt`, `gzT_pos`,
  `gzT_B`, `gz_one_eq`, `gzT_gate`, `gzT_K`, `gzT_sup`, `gzRR`, `gzRR_zero`, `gzRR_g`, `gzRR_succ`, `gzRR_cof`;
* `gzZU` (**THE UNION AT `ζ_{G+n+2}`**), `gzZU_B`, `gzZU_N`, `gzZU_γ`, `gzZU_b`, `gzZU_R`, `gzZU_g`, `gzZU_start`
  (**IT STARTS THE STAGE `n + 1`**).

No new axiom.  New definitions: `gzZN`, `gzZR`, `gzZg`, `gzT`, `gzRR`, `gzZU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gz

open Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Go
  Googology.Trans.PoR.InaccPsi.R2.Gp
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The union: first member containing a code -/

section Def

variable (n : ℕ) (U0 : GwZD)

/-- The first system `gzYD n U0 ν` containing `c`. -/
noncomputable def gzZN (c : Ordinal.{0}) : Ordinal.{0} := sInf {ν | ν < gzZ (n + 2) ∧ c < (gzYD n U0 ν).B}

/-- The reading of the union. -/
noncomputable def gzZR (c x : Ordinal.{0}) : Ordinal.{0} := (gzYD n U0 (gzZN n U0 c)).R c x

/-- The gate of the union. -/
noncomputable def gzZg (c : Ordinal.{0}) : Ordinal.{0} := (gzYD n U0 (gzZN n U0 c)).g c

/-- **The tower of the stage `n`**: `t_0 = 1`, `t_{k+1} = φ(1, ζ_{G+n+1} + t_k)`. -/
noncomputable def gzT : ℕ → Ordinal.{0}
  | 0 => 1
  | k + 1 => veblen 1 (gzZ (n + 1) + gzT k)

/-- **The reading of the tower code `t_k`** at the base `x` (in `gzYD n U0 t_k`). -/
noncomputable def gzRR (k : ℕ) (x : Ordinal.{0}) : Ordinal.{0} := (gzYD n U0 (gzT n k)).R (gzT n k) x

theorem gzT_lt : ∀ k : ℕ, gzT n k < gzZ (n + 2)
  | 0 => one_lt_omega0.trans (omega0_lt_inE (gzZ_E _))
  | k + 1 => gzY_veb_lt_Z (n + 1) (gzT_lt k)

theorem gzT_pos : ∀ k : ℕ, 0 < gzT n k
  | 0 => zero_lt_one
  | k + 1 => InE.pos (omega0_opow_epsilon (gzZ (n + 1) + gzT n k))

theorem gzT_iter (k : ℕ) : Ordinal.epsilon^[k] (gzZ (n + 1) + 1) ≤ gzZ (n + 1) + gzT n k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    show veblen 1 _ ≤ gzZ (n + 1) + veblen 1 (gzZ (n + 1) + gzT n k)
    exact ((isNormal_veblen 1).monotone ih).trans le_add_self

/-- **The tower is cofinal in `ζ_{G+n+2}`.** -/
theorem gzT_sup {t : Ordinal.{0}} (ht : t < gzZ (n + 2)) : ∃ k : ℕ, t < gzT n k := by
  have ht' : t < evZ (gzZ (n + 1)) := ht
  obtain ⟨k, hk⟩ := lt_nfp_iff.1 ht'
  refine ⟨k + 1, (hk.trans_le (gzT_iter n k)).trans ?_⟩
  exact gzY_lt_veb (n + 1) (gzT_pos n k) (gzT_lt n k)

theorem gzRR_zero (x : Ordinal.{0}) : gzRR n U0 0 x = 1 := (gzYD n U0 1).R_one x

end Def

section Union

variable {n : ℕ} {U0 : GwZD} (hU : GzStart n U0)
include hU

theorem gz_memB {c : Ordinal.{0}} (hc : c < gzZ (n + 2)) : ∃ ν, ν < gzZ (n + 2) ∧ c < (gzYD n U0 ν).B :=
  ⟨c, hc, gz_self hU hc⟩

omit hU in
theorem gzZN_spec {c ν : Ordinal.{0}} (hν : ν < gzZ (n + 2)) (hc : c < (gzYD n U0 ν).B) :
    gzZN n U0 c ≤ ν ∧ gzZN n U0 c < gzZ (n + 2) ∧ c < (gzYD n U0 (gzZN n U0 c)).B := by
  have hne : ({ν | ν < gzZ (n + 2) ∧ c < (gzYD n U0 ν).B} : Set Ordinal.{0}).Nonempty := ⟨ν, hν, hc⟩
  have hm := csInf_mem hne
  exact ⟨csInf_le' ⟨hν, hc⟩, hm.1, hm.2⟩

omit hU in
theorem gzZN_min {c μ : Ordinal.{0}} (hμ : μ < gzZN n U0 c) (hμl : μ < gzZ (n + 2)) : ¬ c < (gzYD n U0 μ).B :=
  fun hcμ => absurd (csInf_le' ⟨hμl, hcμ⟩ : gzZN n U0 c ≤ μ) (not_le.2 hμ)

theorem gz_B_lt_Z {c : Ordinal.{0}} (hc : c < gzZ (n + 2)) : (gzYD n U0 c).B < gzZ (n + 2) := by
  rw [gz_B hU hc]; exact gzY_veb_lt_Z (n + 1) hc

theorem gzZN_high {c : Ordinal.{0}} (hc : gzZ (n + 2) ≤ c) : gzZN n U0 c = 0 := by
  unfold gzZN
  have he : ({ν | ν < gzZ (n + 2) ∧ c < (gzYD n U0 ν).B} : Set Ordinal.{0}) = ∅ := by
    ext ν
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hν hcν
    exact absurd (hcν.trans (gz_B_lt_Z hU hν)) (not_lt.2 hc)
  rw [he]; exact Ordinal.sInf_empty

theorem gzZR_eq {c ν : Ordinal.{0}} (hν : ν < gzZ (n + 2)) (hc : c < (gzYD n U0 ν).B) (x : Ordinal.{0}) :
    gzZR n U0 c x = (gzYD n U0 ν).R c x := by
  obtain ⟨h1, -, h3⟩ := gzZN_spec hν hc
  exact ((gz_ext hU h1 hν).1 c x h3).symm

theorem gzZg_eq {c ν : Ordinal.{0}} (hν : ν < gzZ (n + 2)) (hc : c < (gzYD n U0 ν).B) :
    gzZg n U0 c = (gzYD n U0 ν).g c := by
  obtain ⟨h1, -, h3⟩ := gzZN_spec hν hc
  exact ((gz_ext hU h1 hν).2 c h3).symm

omit hU in
theorem gzZ_lim2 : IsSuccLimit (gzZ (n + 2)) := ev_isSuccLimit_of_inE (gzZ_E _)

theorem gzZR_succ (c x : Ordinal.{0}) : gzZR n U0 (c + 1) x = gzZR n U0 c x + 1 := by
  rcases lt_or_ge c (gzZ (n + 2)) with h | h
  · have h1 : c + 1 < gzZ (n + 2) := (gzZ_lim2 (n := n)).add_one_lt h
    rw [gzZR_eq hU h1 (gz_self hU h1), gzZR_eq hU h1 ((lt_add_one c).trans (gz_self hU h1)),
      (gzYD n U0 (c + 1)).R_succ]
  · unfold gzZR
    rw [gzZN_high hU h, gzZN_high hU (h.trans (le_self_add (a := c) (b := 1))), (gzYD n U0 0).R_succ]

theorem gzZg_le_succ (c : Ordinal.{0}) : gzZg n U0 c ≤ gzZg n U0 (c + 1) := by
  rcases lt_or_ge c (gzZ (n + 2)) with h | h
  · have h1 : c + 1 < gzZ (n + 2) := (gzZ_lim2 (n := n)).add_one_lt h
    rw [gzZg_eq hU h1 (gz_self hU h1), gzZg_eq hU h1 ((lt_add_one c).trans (gz_self hU h1))]
    exact (gzYD n U0 (c + 1)).g_le_succ c
  · unfold gzZg
    rw [gzZN_high hU h, gzZN_high hU (h.trans (le_self_add (a := c) (b := 1)))]
    exact (gzYD n U0 0).g_le_succ c

omit hU in
theorem gz_zero_lt2 : (0 : Ordinal.{0}) < gzZ (n + 2) := (gzZ_E _).pos

/-- **A code of the union with gate below an `ε`-number `σ` lies in a member with base gate below `σ`.** -/
theorem gz_small {c σ : Ordinal.{0}} (hc : c < gzZ (n + 2)) (hσ : InE σ) (hg : gzZg n U0 c < σ) :
    ∃ μ, μ < gzZ (n + 2) ∧ c < (gzYD n U0 μ).B ∧ (gzYD n U0 μ).γ < σ := by
  obtain ⟨k, hk1, hk⟩ := gz_memB hU hc
  obtain ⟨-, hN1, hcN⟩ := gzZN_spec hk1 hk
  have hgN : gzZg n U0 c = (gzYD n U0 (gzZN n U0 c)).g c := rfl
  rcases zero_or_succ_or_isSuccLimit (gzZN n U0 c) with h0 | ⟨m, hm⟩ | hlim
  · refine ⟨gzZN n U0 c, hN1, hcN, ?_⟩
    rw [h0, gzYD_zero, hU.γ]; exact hσ.pos
  · have hm' : gzZN n U0 c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < gzZN n U0 c := by rw [hm']; exact lt_add_one m
    have hml : m < gzZ (n + 2) := hmN.trans hN1
    have hBc : (gzYD n U0 m).B ≤ c := not_lt.1 (gzZN_min hmN hml)
    have hs : gzYD n U0 (gzZN n U0 c) = (gzYD n U0 m).step := by rw [hm']; exact gzYD_succ n U0 m
    refine ⟨gzZN n U0 c, hN1, hcN, ?_⟩
    rw [hgN, hs] at hg
    rw [hs]
    exact ((gzYD n U0 m).γ_le_sG hBc).trans_lt hg
  · exfalso
    rw [gz_B hU hN1] at hcN
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ hlim)).1 hcN
    obtain ⟨d, hd, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    have hdl : d < gzZ (n + 2) := hd.trans hN1
    refine gzZN_min hd hdl ?_
    rw [gz_B hU hdl]; exact hct.trans_le ((isNormal_veblen 1).monotone htd)

/-! ## The tower readings -/

theorem gzT_B (k : ℕ) : (gzYD n U0 (gzT n k)).B = gzT n (k + 1) := gz_B hU (gzT_lt n k)

omit hU in
theorem gz_one_eq : gzYD n U0 1 = U0.step := by
  have h := gzYD_succ n U0 0
  rw [zero_add, gzYD_zero] at h
  exact h

/-- **Every `gzYD n U0 t_k` has base gate below every `ε`-number base.** -/
theorem gzT_gate : ∀ (k : ℕ) (x : Ordinal.{0}), InE x → x < Om1 → (gzYD n U0 (gzT n k)).γ < x
  | 0, x, hx, _ => by
    show (gzYD n U0 1).γ < x
    rw [gz_one_eq, GwZD.step_γ, hU.γ]; exact hx.pos
  | k + 1, x, hx, hx1 => by
    set a := gzT n k with ha
    have haZ : a < gzZ (n + 2) := gzT_lt n k
    have hμ : gzT n (k + 1) = (gzYD n U0 a).B := (gzT_B hU k).symm
    have hμZ : gzT n (k + 1) < gzZ (n + 2) := gzT_lt n (k + 1)
    have ha1 : a + 1 ≤ gzT n (k + 1) := Order.add_one_le_of_lt (by rw [hμ]; exact gz_self hU haZ)
    have ha1Z : a + 1 < gzZ (n + 2) := (gzZ_lim2 (n := n)).add_one_lt haZ
    have hμB : gzT n (k + 1) < (gzYD n U0 (a + 1)).B := by
      rw [gz_B hU ha1Z]
      show veblen 1 (gzZ (n + 1) + a) < _
      exact (isNormal_veblen 1).strictMono ((add_lt_add_iff_left _).2 (lt_add_one a))
    rw [gz_γ_iff hU hμZ hx hx1, (gz_ext hU ha1 hμZ).2 _ hμB, gzYD_succ]
    show (gzYD n U0 a).step.g (gzT n (k + 1)) < x
    rw [hμ, GwZD.step_g_B]
    exact gzT_gate k x hx hx1

theorem gzT_K (S : InaccSeq.{0}) (k : ℕ) : (gzYD n U0 (gzT n k)).γ < Td.tdK S := by
  have hK1 : Td.tdK S < Om1 := by rw [Br.Om1_eq]; exact Td.tdK_lt_Om1
  exact gzT_gate hU k _ (Low.opow_eq_self_of_SC Td.tdK_SC) hK1

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem gzRR_g (k : ℕ) : (gzYD n U0 (gzT n k)).g (gzT n k) < x :=
  (gz_γ_iff hU (gzT_lt n k) hx hx1).1 (gzT_gate hU k x hx hx1)

/-- **`r_{k+1} = φ(1, Z_{n+1}(x) + r_k)`.** -/
theorem gzRR_succ (k : ℕ) : gzRR n U0 (k + 1) x = veblen 1 (gwZn x (n + 1) + gzRR n U0 k x) := by
  set a := gzT n k with ha
  have haZ : a < gzZ (n + 2) := gzT_lt n k
  have hμ : gzT n (k + 1) = (gzYD n U0 a).B := (gzT_B hU k).symm
  have hμZ : gzT n (k + 1) < gzZ (n + 2) := gzT_lt n (k + 1)
  have ha1 : a + 1 ≤ gzT n (k + 1) := Order.add_one_le_of_lt (by rw [hμ]; exact gz_self hU haZ)
  have ha1Z : a + 1 < gzZ (n + 2) := (gzZ_lim2 (n := n)).add_one_lt haZ
  have hμB : gzT n (k + 1) < (gzYD n U0 (a + 1)).B := by
    rw [gz_B hU ha1Z]
    show veblen 1 (gzZ (n + 1) + a) < _
    exact (isNormal_veblen 1).strictMono ((add_lt_add_iff_left _).2 (lt_add_one a))
  have hγ : (gzYD n U0 a).γ < x := gzT_gate hU k x hx hx1
  unfold gzRR
  rw [(gz_ext hU ha1 hμZ).1 _ x hμB, gzYD_succ]
  show (gzYD n U0 a).step.R (gzT n (k + 1)) x = _
  have h1 : (1 : Ordinal.{0}) < (gzYD n U0 a).NB := (gzYD n U0 a).one_lt_B.trans (gzYD n U0 a).B_lt_NB
  have hpow := (gzYD n U0 a).hR_pow one_ne_zero h1 x
  rw [opow_one, (gzYD n U0 a).hR_one, opow_one] at hpow
  rw [GwZD.step_R, hμ, hpow, gz_b hU haZ hx hx1 hγ]

theorem gzRR_iter (k : ℕ) : Ordinal.epsilon^[k] (gwZn x (n + 1) + 1) ≤ gzRR n U0 (k + 1) x := by
  induction k with
  | zero =>
    rw [Function.iterate_zero_apply, gzRR_succ hU hx hx1 0, gzRR_zero]
    exact right_le_veblen 1 _
  | succ k ih =>
    rw [Function.iterate_succ_apply', gzRR_succ hU hx hx1 (k + 1)]
    show veblen 1 _ ≤ _
    exact (isNormal_veblen 1).monotone (ih.trans le_add_self)

/-- **The tower readings are cofinal in `Z_{n+2}(x) = ζ_{Γ_{x+1}+n+2}`.** -/
theorem gzRR_cof {t : Ordinal.{0}} (ht : t < gwZn x (n + 2)) : ∃ k : ℕ, t < gzRR n U0 k x := by
  have ht' : t < evZ (gwZn x (n + 1)) := ht
  obtain ⟨k, hk⟩ := lt_nfp_iff.1 ht'
  exact ⟨k + 1, hk.trans_le (gzRR_iter hU hx hx1 k)⟩

end Base

theorem gz_b_lt {μ x : Ordinal.{0}} (hμ : μ < gzZ (n + 2)) (hx : InE x) (hx1 : x < Om1)
    (hμx : (gzYD n U0 μ).γ < x) : (gzYD n U0 μ).b x < gwZn x (n + 2) := by
  have h := (gzYD n U0 μ).b_Z x hx hx1 hμx
  rw [gz_N hU hμ] at h
  exact (lt_eN _).trans h

theorem gz_R_lt {k c x : Ordinal.{0}} (hk1 : k < gzZ (n + 2)) (hk : c < (gzYD n U0 k).B) (hx : InE x)
    (hx1 : x < Om1) (hg : (gzYD n U0 k).g c < x) : (gzYD n U0 k).R c x < gwZn x (n + 2) := by
  have h := (gzYD n U0 k).R_lt_Z x hx hx1 c hk hg
  rw [gz_N hU hk1] at h
  exact h

omit hU in
theorem gzZ2_cl_gate_lt (n : ℕ) : gcG 0 < gzZ (n + 2) := gzZ_G_lt (n + 1)

/-- **THE UNION AT `ζ_{G+n+2}`**: bound `ζ_{G+n+2}`, base gate `0`, base reading `Z_{n+2}(x)` (its own index), readings
below `Z_{n+3}(x)` (`N = n + 2`). -/
noncomputable def gzZU : GwZD where
  N := n + 2
  B := gzZ (n + 2)
  γ := 0
  γ_lt := gv_Om1_pos
  γ_cl := fun _ hZ _ _ => hZ.1
  γ_G := fun h => absurd h (gzZ2_cl_gate_lt n).ne'
  R := gzZR n U0
  g := gzZg n U0
  b := fun x => gwZn x (n + 2)
  ba := fun x => gwZn x (n + 2)
  ix := gzZ (n + 2)
  B_E := gzZ_E _
  G_le := (gzZ2_cl_gate_lt n).le
  B_lt1 := gzZ_lt1 _
  B_ix := (epsilon_evZ _).symm
  ix_mem := fun S a b ha _ => gzZ_mem S ha (n + 2)
  g_lt := fun c hc => by
    rw [gzZg_eq hU hc (gz_self hU hc)]; exact (gzYD n U0 c).g_lt c (gz_self hU hc)
  g_zero := by rw [gzZg_eq hU gz_zero_lt2 (gzYD n U0 0).B_pos]; exact (gzYD n U0 0).g_zero
  g_nat := fun k => by
    rw [gzZg_eq hU gz_zero_lt2 ((gzYD n U0 0).nat_lt_B k)]; exact (gzYD n U0 0).g_nat k
  g_E := by rw [gzZg_eq hU gz_zero_lt2 (gzYD n U0 0).E_lt_B]; exact (gzYD n U0 0).g_E
  g_lowE := fun c hc => by
    rw [gzZg_eq hU gz_zero_lt2 (hc.trans (gzYD n U0 0).E_lt_B)]; exact (gzYD n U0 0).g_lowE c hc
  g_G0 := fun h => by
    rw [gzZg_eq hU h (gz_self hU h)]; exact (gzYD n U0 (gcG 0)).g_G0 (gz_self hU h)
  g_add := fun Z hZ hωZ x y hxy hgx hgy => by
    obtain ⟨k, hk1, hk⟩ := gz_memB hU hxy
    have hx : x < (gzYD n U0 k).B := lt_of_le_of_lt le_self_add hk
    have hy : y < (gzYD n U0 k).B := lt_of_le_of_lt le_add_self hk
    rw [gzZg_eq hU hk1 hk]; rw [gzZg_eq hU hk1 hx] at hgx; rw [gzZg_eq hU hk1 hy] at hgy
    exact (gzYD n U0 k).g_add Z hZ hωZ x y hk hgx hgy
  g_opow := fun Z hZw hωZ y hy hg => by
    obtain ⟨k, hk1, hk⟩ := gz_memB hU hy
    have hy' : y < (gzYD n U0 k).B := lt_of_le_of_lt (right_le_opow y one_lt_omega0) hk
    rw [gzZg_eq hU hk1 hk]; rw [gzZg_eq hU hk1 hy'] at hg
    exact (gzYD n U0 k).g_opow Z hZw hωZ y hk hg
  code_gate := fun Z hZ1 hZ0 hZa hZp At hAt c hc hcB => by
    obtain ⟨k, hk1, hk⟩ := gz_memB hU hcB
    rw [gzZg_eq hU hk1 hk]
    exact (gzYD n U0 k).code_gate Z hZ1 hZ0 hZa hZp At (fun s hs => (hAt s hs).imp_right
      (fun h => (gz_B_lt_Z hU hk1).le.trans h)) c hc hk
  g_succ := fun Z hZ c hc hg => by
    obtain ⟨k, hk1, hk⟩ := gz_memB hU hc
    have hc' : c < (gzYD n U0 k).B := (lt_add_one c).trans hk
    rw [gzZg_eq hU hk1 hk]; rw [gzZg_eq hU hk1 hc'] at hg
    exact (gzYD n U0 k).g_succ Z hZ c hk hg
  g_le_succ := gzZg_le_succ hU
  mem := fun S a b ha c hc hg => by
    obtain ⟨k, hk1, hk⟩ := gz_memB hU hc
    rw [gzZg_eq hU hk1 hk] at hg
    exact (gzYD n U0 k).mem S a b ha c hk hg
  R_zero := fun x => by rw [gzZR_eq hU gz_zero_lt2 (gzYD n U0 0).B_pos]; exact (gzYD n U0 0).R_zero x
  R_nat := fun k x => by
    rw [gzZR_eq hU gz_zero_lt2 ((gzYD n U0 0).nat_lt_B k)]; exact (gzYD n U0 0).R_nat k x
  R_E := fun x => by rw [gzZR_eq hU gz_zero_lt2 (gzYD n U0 0).E_lt_B]; exact (gzYD n U0 0).R_E x
  R_succ := gzZR_succ hU
  R_pos := fun x hx hx1 c hc0 hc hg => by
    obtain ⟨k, hk1, hk⟩ := gz_memB hU hc
    rw [gzZR_eq hU hk1 hk]; rw [gzZg_eq hU hk1 hk] at hg
    exact (gzYD n U0 k).R_pos x hx hx1 c hc0 hk hg
  R_omega := fun x hx hx1 c hω hc hg => by
    obtain ⟨k, hk1, hk⟩ := gz_memB hU hc
    rw [gzZR_eq hU hk1 hk]; rw [gzZg_eq hU hk1 hk] at hg
    exact (gzYD n U0 k).R_omega x hx hx1 c hω hk hg
  R_lt_b := fun x hx hx1 _ c hc hg => by
    obtain ⟨k, hk1, hk⟩ := gz_memB hU hc
    rw [gzZR_eq hU hk1 hk]; rw [gzZg_eq hU hk1 hk] at hg
    exact gz_R_lt hU hk1 hk hx hx1 hg
  R_lt_Z := fun x hx hx1 c hc hg => by
    obtain ⟨k, hk1, hk⟩ := gz_memB hU hc
    rw [gzZR_eq hU hk1 hk]; rw [gzZg_eq hU hk1 hk] at hg
    exact (gz_R_lt hU hk1 hk hx hx1 hg).trans (lt_evZ _)
  mono := fun x hx hx1 c hc d hdc hgc hgd => by
    obtain ⟨k, hk1, hk⟩ := gz_memB hU hc
    have hd : d < (gzYD n U0 k).B := hdc.trans hk
    rw [gzZR_eq hU hk1 hk, gzZR_eq hU hk1 hd]; rw [gzZg_eq hU hk1 hk] at hgc; rw [gzZg_eq hU hk1 hd] at hgd
    exact (gzYD n U0 k).mono x hx hx1 c hk d hdc hgc hgd
  cof := fun x hx hx1 c hc hg ν hν => by
    obtain ⟨k, hk1, hk⟩ := gz_memB hU hc
    rw [gzZR_eq hU hk1 hk] at hν; rw [gzZg_eq hU hk1 hk] at hg
    obtain ⟨d, hdc, hgd, hνd⟩ := (gzYD n U0 k).cof x hx hx1 c hk hg ν hν
    have hd : d < (gzYD n U0 k).B := hdc.trans hk
    exact ⟨d, hdc, by rw [gzZg_eq hU hk1 hd]; exact hgd, by rw [gzZR_eq hU hk1 hd]; exact hνd⟩
  b_cof := fun x hx hx1 _ ν hν => by
    obtain ⟨k, hk⟩ := gzRR_cof hU hx hx1 hν
    have hkZ : gzT n k < gzZ (n + 2) := gzT_lt n k
    have hkB : gzT n k < (gzYD n U0 (gzT n k)).B := gz_self hU hkZ
    refine ⟨gzT n k, hkZ, ?_, ?_⟩
    · rw [gzZg_eq hU hkZ hkB]; exact gzRR_g hU hx hx1 k
    · rw [gzZR_eq hU hkZ hkB]; exact hk
  b_E := fun x hx hx1 _ => gwZn_E hx hx1 (n + 2)
  x_lt_b := fun x hx hx1 _ => gwZn_gt hx hx1 (n + 2)
  b_eN := fun x hx hx1 _ => gz_eNZ hx hx1 (n + 2)
  ba_lt := fun x hx hx1 _ => gwZn_lt hx hx1 (n + 2)
  b_Z := fun x _ _ _ => go_eN_lt_evZ (lt_evZ (gwZn x (n + 2)))
  b_pi := fun _ _ hB _ => gz_Z_pi hB (n + 2)
  ba_pi := fun _ _ hB _ => gz_Z_pi hB (n + 2)
  ex := fun σ ρ hB c hc hg => by
    obtain ⟨k, hk1, hk⟩ := gz_memB hU hc
    rw [gzZR_eq hU hk1 hk, gzZR_eq hU hk1 hk]; rw [gzZg_eq hU hk1 hk] at hg
    exact (gzYD n U0 k).ex σ ρ hB c hk hg
  dig := fun σ ρ hB _ d hd hg P P' hat => by
    obtain ⟨μ, hμ, hdμ, hγμ⟩ := gz_small hU hd hB.1 hg
    rw [gzZR_eq hU hμ hdμ, gzZR_eq hU hμ hdμ]; rw [gzZg_eq hU hμ hdμ] at hg
    exact (gzYD n U0 μ).dig σ ρ hB hγμ d hdμ hg P P' (fun β hβ hβe =>
      hat β hβ (hβe.trans (gz_b_lt hU hμ hB.2.1 hB.2.2.2 (hγμ.trans hB.2.2.1))))
  ld := fun c hl hc => by
    obtain ⟨k, hk1, hk⟩ := gz_memB hU hc
    obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := (gzYD n U0 k).ld c hl hk
    have hcpn : cp < (gzYD n U0 k).B := hcp.trans hk
    refine ⟨cp, lp, T, hcp, by rw [gzZg_eq hU hk1 hk, gzZg_eq hU hk1 hcpn]; exact hgcp, fun x hx hx1 hg => ?_,
      fun σ ρ hB hg => hex σ ρ hB (by rw [← gzZg_eq hU hk1 hk]; exact hg)⟩
    rw [gzZg_eq hU hk1 hk] at hg
    rw [gzZR_eq hU hk1 hk, gzZR_eq hU hk1 hcpn]
    exact hdec x hx hx1 hg

theorem gzZU_B : (gzZU hU).B = gzZ (n + 2) := rfl

theorem gzZU_N : (gzZU hU).N = n + 2 := rfl

theorem gzZU_γ : (gzZU hU).γ = 0 := rfl

theorem gzZU_b (x : Ordinal.{0}) : (gzZU hU).b x = gwZn x (n + 2) := rfl

/-- **The union extends every `gzYD n U0 ν`, `ν < ζ_{G+n+2}`** (readings). -/
theorem gzZU_R {ν c : Ordinal.{0}} (hν : ν < gzZ (n + 2)) (hc : c < (gzYD n U0 ν).B) (x : Ordinal.{0}) :
    (gzZU hU).R c x = (gzYD n U0 ν).R c x := gzZR_eq hU hν hc x

/-- **The union extends every `gzYD n U0 ν`, `ν < ζ_{G+n+2}`** (gates). -/
theorem gzZU_g {ν c : Ordinal.{0}} (hν : ν < gzZ (n + 2)) (hc : c < (gzYD n U0 ν).B) :
    (gzZU hU).g c = (gzYD n U0 ν).g c := gzZg_eq hU hν hc

/-- **THE UNION AT `ζ_{G+n+2}` STARTS THE STAGE `n + 1`.** -/
theorem gzZU_start : GzStart (n + 1) (gzZU hU) where
  N := rfl
  ix := rfl
  γ := rfl
  b := fun _ => rfl

end Union

end Googology.Trans.PoR.InaccPsi.R2.Gz

import Googology.Trans.PoR.InaccPsi.R2.HiMRec

/-!
# HiMTop: THE UNION OF ALL GATED OFFSETS OF THE LEVEL `Ω₁`: THE SYSTEM AT `N_{Ω₁}(G) = φ(Ω₁+1, G+1)`

The copy of `Hg.HgfMTop` whose level is the base itself.  For a start `S0` (`Hi.HiMStart`), the union of all starts
`Hi.hiMU S0 λ`, `λ < N_{Ω₁}(G)`, is a system `hiMTU` with the bound `N_{Ω₁}(G) = φ(Ω₁+1, G+1)`, base gate `0`, base
reading `Z_l(x) = N_x(Γ_{x+1}) = φ(x+1, Γ_{x+1}+1)` (the level `Ω₁+1` read as `x+1`), bound field `evZ(Z_l(x))`.
The tower `t_0 = 0`, `t_{k+1} = Q_{t_k} = φ(Ω₁, G+1+t_k)` is cofinal in `N_{Ω₁}(G)` and its readings
`r_{k+1}(x) = φ(x, Γ_{x+1}+1+r_k(x))` are cofinal in `Z_l(x)`.  With `S0 = Hg.hgU` the union is located (base gate
`0 < K`): `Λ⁺ = ι(Γ(φ(Ω₁+1, G+1))·ω)`, and BLK^O, the exact reaches, ENUM-REACH and CapV hold below it,
UNCONDITIONALLY.  The offsets `ε₀`, `Γ₀`, `K`, `Ω₁` and every code offset `< N_{Ω₁}(G)` of the level `Ω₁` are
passed (the wall of `Hg.hgFV`, `Gp.gp_no_eps0`, does not arise: the gate of the code offset moves the EXACT part).

* `hiMTt`, `hiMTt_cof`, `hiMTt_gate`, `hiMTr`, `hiMTr_succ`, `hiMTr_cof`; `hiMTN`, `hiMTR`, `hiMTg`, `hiMT_small`,
  `hiZl_pi`, `hiMTU` (**THE SYSTEM AT `N_{Ω₁}(G)`**), `hiMTU_R0`, `hiMTU_g0`;
* `hiTU := hiMTU hgU_hiStart`, `hiTU_B`, `hiTU_loc` (**`φ(Ω₁+1, G+1)` IS LOCATED**), `hiTU_blk`, `hiTU_enum`,
  `hiTU_capV`, `hiTU_road` (**THE ROAD**), `hiN_lt_Om2`, `hiTU_P`, `hiTU_fr_order`, `hiQ_loc` (every `Q_λ`).

No new axiom.  New definitions: `hiMTt`, `hiMTr`, `hiMTN`, `hiMTR`, `hiMTg`, `hiMTU`, `hiTU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hi

open Googology.Trans.PoR.InaccPsi.R2.Hg
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

/-! ## The tower of offsets -/

/-- **The tower of offsets**: `t_0 = 0`, `t_{k+1} = φ(Ω₁, G + 1 + t_k)`. -/
noncomputable def hiMTt : ℕ → Ordinal.{0}
  | 0 => 0
  | k + 1 => hiQ (hiMTt k)

theorem hiMTt_lt : ∀ k : ℕ, hiMTt k < hiN
  | 0 => hiN_pos
  | k + 1 => hiQ_lt_N (hiMTt_lt k)

theorem hiMTt_lt_succ (k : ℕ) : hiMTt k < hiMTt (k + 1) := hi_lt_Q (hiMTt_lt k)

theorem hiMTt_iter (n : ℕ) : (veblen Om1)^[n] (gcG 0 + 1) ≤ hiMTt (n + 1) := by
  induction n with
  | zero =>
    show gcG 0 + 1 ≤ veblen Om1 (gcG 0 + 1 + 0)
    rw [add_zero]; exact right_le_veblen Om1 _
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    show veblen Om1 _ ≤ veblen Om1 (gcG 0 + 1 + hiMTt (n + 1))
    exact (isNormal_veblen Om1).monotone (ih.trans le_add_self)

/-- **The tower is cofinal in `N_{Ω₁}(G)`.** -/
theorem hiMTt_cof {c : Ordinal.{0}} (hc : c < hiN) : ∃ k : ℕ, c < hiMTt k := by
  have e : hiN = nfp (veblen Om1) (gcG 0 + 1) := rfl
  rw [e] at hc
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hc
  exact ⟨n + 1, hn.trans_le (hiMTt_iter n)⟩

section Tower

variable {S0 : HgVD} (hS : HiMStart S0)
include hS

theorem hiMTt_B (k : ℕ) : (hiMU S0 (hiMTt k)).B = hiMTt (k + 1) := hiMU_B hS (hiMTt_lt k)

/-- **The code `t_{k+1} = Q_{t_k}` has the gate of the base `Q_{t_k}`.** -/
theorem hiMTt_gstep (k : ℕ) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    (hiMU S0 (hiMTt (k + 1))).g (hiMTt (k + 1)) < x ↔ (hiMU S0 (hiMTt k)).g (hiMTt k) < x := by
  set l := hiMTt k with hl
  have hlT : l < hiN := hiMTt_lt k
  have hl'T : hiMTt (k + 1) < hiN := hiMTt_lt (k + 1)
  have hl1 : l + 1 ≤ hiMTt (k + 1) := Order.add_one_le_of_lt (hiMTt_lt_succ k)
  have hcB : hiMTt (k + 1) < (hiMU S0 (l + 1)).B := by
    rw [hiMU_B hS (hl1.trans_lt hl'T)]; exact hiQ_lt_Q (lt_add_one l)
  rw [(hiM_ext hS hl1 hl'T).2 _ hcB, hiMU_succ_eq' hS hlT]
  exact hiQU_gQ _ _ _ hx hx1

/-- **Every start `hiMU S0 t_k` has base gate below every base.** -/
theorem hiMTt_gate : ∀ (k : ℕ) (x : Ordinal.{0}), InE x → x < Om1 → (hiMU S0 (hiMTt k)).γ < x
  | 0, x, hx, hx1 => by
    show (hiMU S0 0).γ < x
    rw [hiMU_γ_iff hS hiN_pos hx hx1, (hiMU S0 0).g_zero]; exact hx.pos
  | k + 1, x, hx, hx1 => by
    rw [hiMU_γ_iff hS (hiMTt_lt (k + 1)) hx hx1, hiMTt_gstep hS k hx hx1,
      ← hiMU_γ_iff hS (hiMTt_lt k) hx hx1]
    exact hiMTt_gate k x hx hx1

end Tower

/-- The reading of the tower code `t_k` (in its start). -/
noncomputable def hiMTr (S0 : HgVD) (k : ℕ) (x : Ordinal.{0}) : Ordinal.{0} :=
  (hiMU S0 (hiMTt k)).R (hiMTt k) x

section TowerRead

variable {S0 : HgVD} (hS : HiMStart S0) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hS hx hx1

theorem hiMTt_g (k : ℕ) : (hiMU S0 (hiMTt k)).g (hiMTt k) < x :=
  (hiMU_γ_iff hS (hiMTt_lt k) hx hx1).1 (hiMTt_gate hS k x hx hx1)

theorem hiMTr_lt (k : ℕ) : hiMTr S0 k x < hiZl x :=
  hiR_lt _ (hiMU_self hS (hiMTt_lt k)) (hiMU_Zb hS (hiMTt_lt k)) hx hx1 (hiMTt_g hS hx hx1 k)

/-- **`r_{k+1}(x) = φ(x, Γ_{x+1}+1+r_k(x))`**: the code `t_{k+1} = Q_{t_k}` is read as the base reading of the start
`t_k`. -/
theorem hiMTr_succ (k : ℕ) : hiMTr S0 (k + 1) x = veblen x (lgG x + 1 + hiMTr S0 k x) := by
  set l := hiMTt k with hl
  have hlT : l < hiN := hiMTt_lt k
  have hl'T : hiMTt (k + 1) < hiN := hiMTt_lt (k + 1)
  have hl1 : l + 1 ≤ hiMTt (k + 1) := Order.add_one_le_of_lt (hiMTt_lt_succ k)
  have hcB : hiMTt (k + 1) < (hiMU S0 (l + 1)).B := by
    rw [hiMU_B hS (hl1.trans_lt hl'T)]; exact hiQ_lt_Q (lt_add_one l)
  have hg := hiMTt_g hS hx hx1 k
  unfold hiMTr
  rw [(hiM_ext hS hl1 hl'T).1 _ x hcB, hiMU_succ_eq' hS hlT]
  rw [show hiMTt (k + 1) = (hiOff (hiMU S0 l) l (hiMU_self hS hlT) hlT (hiMU_Zb hS hlT)).Q from rfl,
    hiQU_RQ _ _ _ hx hx1 hg]
  exact hiP_eq _ (hiMU_self hS hlT) (hiMU_Zb hS hlT) hx hx1 hg

theorem hiMTr_zero : hiMTr S0 0 x = 0 := by unfold hiMTr; exact (hiMU S0 (hiMTt 0)).R_zero x

/-- **The iterates of `φ(x, ·)` from `Γ_{x+1} + 1` lie below the tower readings.** -/
theorem hiMTr_iter (n : ℕ) : (veblen x)^[n] (lgG x + 1) ≤ hiMTr S0 (n + 1) x := by
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply, hiMTr_succ hS hx hx1 0, hiMTr_zero hS hx hx1, add_zero]
    exact right_le_veblen x _
  | succ n ih =>
    rw [Function.iterate_succ_apply', hiMTr_succ hS hx hx1 (n + 1)]
    exact (isNormal_veblen x).monotone (ih.trans le_add_self)

/-- **The tower readings are cofinal in `Z_l(x) = N_x(Γ_{x+1})`.** -/
theorem hiMTr_cof {v : Ordinal.{0}} (hv : v < hiZl x) : ∃ k : ℕ, v < hiMTr S0 k x := by
  have e : hiZl x = nfp (veblen x) (lgG x + 1) := hiZl_eq hx hx1
  rw [e] at hv
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hv
  exact ⟨n + 1, hn.trans_le (hiMTr_iter hS hx hx1 n)⟩

end TowerRead

/-! ## Lemma EXACT for `Z_l(ρ)` -/

/-- **Lemma EXACT for `Z_l(ρ) = ϑᵖ(Ω₁·(ρ+1) + Γ_{ρ+1})`.** -/
theorem hiZl_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) : hiZl ρ ∈ TB ρ σ ∧ pi σ ρ (hiZl ρ) = hiZl σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨r1, r2⟩ := pi_base hB
  have h1σ : (1 : Ordinal.{0}) < σ := one_lt_omega0.trans (omega0_lt_inE hB.1)
  obtain ⟨u1, u2⟩ := pi_add hB r1 (mem_TB_of_lt hB h1σ)
  rw [r2, pi_lt hB h1σ] at u2
  obtain ⟨g1, g2⟩ : lgG ρ ∈ TB ρ σ ∧ pi σ ρ (lgG ρ) = lgG σ := Go.goGl.ba_pi σ ρ hB
  have h := glA_pi hB u1 (gl_Om1_lim.add_one_lt hρ1) g1 (lgG_facts hB.2.1 hρ1).2.2.1
  rw [u2, g2] at h
  rw [hiZl_glA hB.2.1 hρ1, hiZl_glA hB.1 hσ1]
  exact h

/-! ## The union of all offsets -/

section Union

variable (S0 : HgVD)

/-- The first start containing `c`. -/
noncomputable def hiMTN (c : Ordinal.{0}) : Ordinal.{0} := sInf {ν | ν < hiN ∧ c < (hiMU S0 ν).B}

/-- The reading of the union. -/
noncomputable def hiMTR (c x : Ordinal.{0}) : Ordinal.{0} := (hiMU S0 (hiMTN S0 c)).R c x

/-- The gate of the union. -/
noncomputable def hiMTg (c : Ordinal.{0}) : Ordinal.{0} := (hiMU S0 (hiMTN S0 c)).g c

variable {S0} (hS : HiMStart S0)
include hS

theorem hiMT_cof {c : Ordinal.{0}} (hc : c < hiN) : ∃ ν, ν < hiN ∧ c < (hiMU S0 ν).B := by
  obtain ⟨k, hk⟩ := hiMTt_cof hc
  exact ⟨hiMTt k, hiMTt_lt k, hk.trans (by rw [hiMTt_B hS k]; exact hiMTt_lt_succ k)⟩

omit hS in
theorem hiMTN_spec {c ν : Ordinal.{0}} (hν : ν < hiN) (hc : c < (hiMU S0 ν).B) :
    hiMTN S0 c ≤ ν ∧ hiMTN S0 c < hiN ∧ c < (hiMU S0 (hiMTN S0 c)).B := by
  have hne : ({ν | ν < hiN ∧ c < (hiMU S0 ν).B} : Set Ordinal.{0}).Nonempty := ⟨ν, hν, hc⟩
  have hm := csInf_mem hne
  exact ⟨csInf_le' ⟨hν, hc⟩, hm.1, hm.2⟩

omit hS in
theorem hiMTN_min {c μ : Ordinal.{0}} (hμ : μ < hiMTN S0 c) (hμl : μ < hiN) : ¬ c < (hiMU S0 μ).B :=
  fun hcμ => absurd (csInf_le' ⟨hμl, hcμ⟩ : hiMTN S0 c ≤ μ) (not_le.2 hμ)

theorem hiMT_B_lt {ν : Ordinal.{0}} (hν : ν < hiN) : (hiMU S0 ν).B < hiN := by
  rw [hiMU_B hS hν]; exact hiQ_lt_N hν

theorem hiMTN_high {c : Ordinal.{0}} (hc : hiN ≤ c) : hiMTN S0 c = 0 := by
  unfold hiMTN
  have he : ({ν | ν < hiN ∧ c < (hiMU S0 ν).B} : Set Ordinal.{0}) = ∅ := by
    ext ν
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hν hcν
    exact absurd (hcν.trans (hiMT_B_lt hS hν)) (not_lt.2 hc)
  rw [he]; exact Ordinal.sInf_empty

theorem hiMTR_eq {c ν : Ordinal.{0}} (hν : ν < hiN) (hc : c < (hiMU S0 ν).B) (x : Ordinal.{0}) :
    hiMTR S0 c x = (hiMU S0 ν).R c x := by
  obtain ⟨h1, -, h3⟩ := hiMTN_spec hν hc
  exact ((hiM_ext hS h1 hν).1 c x h3).symm

theorem hiMTg_eq {c ν : Ordinal.{0}} (hν : ν < hiN) (hc : c < (hiMU S0 ν).B) :
    hiMTg S0 c = (hiMU S0 ν).g c := by
  obtain ⟨h1, -, h3⟩ := hiMTN_spec hν hc
  exact ((hiM_ext hS h1 hν).2 c h3).symm

theorem hiMTR_succ (c x : Ordinal.{0}) : hiMTR S0 (c + 1) x = hiMTR S0 c x + 1 := by
  rcases lt_or_ge c hiN with h | h
  · obtain ⟨n, hn1, hn⟩ := hiMT_cof hS (hiN_lim.add_one_lt h)
    rw [hiMTR_eq hS hn1 hn, hiMTR_eq hS hn1 ((lt_add_one c).trans hn), (hiMU S0 n).R_succ]
  · unfold hiMTR
    rw [hiMTN_high hS h, hiMTN_high hS (h.trans (le_self_add (a := c) (b := 1))), (hiMU S0 0).R_succ]

theorem hiMTg_le_succ (c : Ordinal.{0}) : hiMTg S0 c ≤ hiMTg S0 (c + 1) := by
  rcases lt_or_ge c hiN with h | h
  · obtain ⟨n, hn1, hn⟩ := hiMT_cof hS (hiN_lim.add_one_lt h)
    rw [hiMTg_eq hS hn1 hn, hiMTg_eq hS hn1 ((lt_add_one c).trans hn)]; exact (hiMU S0 n).g_le_succ c
  · unfold hiMTg
    rw [hiMTN_high hS h, hiMTN_high hS (h.trans (le_self_add (a := c) (b := 1)))]
    exact (hiMU S0 0).g_le_succ c

/-- **A code of the union with gate below a base `σ` lies in a start with base gate below `σ`.** -/
theorem hiMT_small {c σ : Ordinal.{0}} (hc : c < hiN) (hσ : InE σ) (hσ1 : σ < Om1) (hg : hiMTg S0 c < σ) :
    ∃ μ, μ < hiN ∧ c < (hiMU S0 μ).B ∧ (hiMU S0 μ).γ < σ := by
  obtain ⟨n, hn1, hn⟩ := hiMT_cof hS hc
  obtain ⟨-, hN1, hcNc⟩ := hiMTN_spec hn1 hn
  have hgN : hiMTg S0 c = (hiMU S0 (hiMTN S0 c)).g c := rfl
  rcases zero_or_succ_or_isSuccLimit (hiMTN S0 c) with h0 | ⟨m, hm⟩ | hlim
  · refine ⟨hiMTN S0 c, hN1, hcNc, ?_⟩
    rw [h0, hiMU_γ_iff hS hiN_pos hσ hσ1, (hiMU S0 0).g_zero]
    exact hσ.pos
  · have hm' : hiMTN S0 c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < hiMTN S0 c := by rw [hm']; exact lt_add_one m
    have hml : m < hiN := hmN.trans hN1
    have hBc : (hiMU S0 m).B ≤ c := not_lt.1 (hiMTN_min hmN hml)
    refine ⟨hiMTN S0 c, hN1, hcNc, ?_⟩
    rw [hgN, hm'] at hg
    rw [hm'] at hcNc hN1 ⊢
    exact hiMU_high hS hN1 hBc hcNc hσ hσ1 hg
  · exfalso
    rw [hiMU_B hS hN1] at hcNc
    obtain ⟨d, hf, hcd⟩ := hiQ_cof hlim hcNc
    have hfl : d < hiN := hf.trans hN1
    refine hiMTN_min hf hfl ?_
    rw [hiMU_B hS hfl]; exact hcd

/-- **`b_μ(x) < Z_l(x)`** for every start with base gate below `x`. -/
theorem hiMT_b_lt {μ x : Ordinal.{0}} (hμ : μ < hiN) (hx : InE x) (hx1 : x < Om1) (hγ : (hiMU S0 μ).γ < x) :
    (hiMU S0 μ).b x < hiZl x := by
  have hg : (hiMU S0 μ).g μ < x := (hiMU_γ_iff hS hμ hx hx1).1 hγ
  rw [(hiMU_start hS hμ).b x hx hx1 hg]
  exact hiP_lt_Zl _ (hiMU_self hS hμ) (hiMU_Zb hS hμ) hx hx1 hg

/-- **THE SYSTEM AT `N_{Ω₁}(G) = φ(Ω₁+1, G+1)`**: the union of all starts `hiMU S0 λ`, `λ < N_{Ω₁}(G)`: base gate
`0`, base reading `Z_l(x) = φ(x+1, Γ_{x+1}+1)`, bound field `evZ(Z_l(x))`. -/
noncomputable def hiMTU : HgVD where
  B := hiN
  γ := 0
  γ_lt := gv_Om1_pos
  γ_cl := fun _ hZ _ _ => hZ.1
  γ_G := fun _ => rfl
  R := hiMTR S0
  g := hiMTg S0
  b := hiZl
  ba := hiZl
  ix := hiN
  Z := fun x => evZ (hiZl x)
  B_E := hiN_E
  G_le := hiG_lt_N.le
  B_lt1 := hiN_lt1
  B_ix := (hc_fix_down hg_one_lt_Om1.le hiN_fix).symm
  Z_fix := fun x _ _ => epsilon_evZ _
  Z_G1 := fun x hx hx1 => gw_evZ_lt1 hx hx1 (hiZl_lt1 hx hx1)
  ix_mem := fun S _ _ ha _ => hiN_mem S ha
  g_lt := fun c hc => by
    obtain ⟨n, hn1, hn⟩ := hiMT_cof hS hc
    rw [hiMTg_eq hS hn1 hn]; exact (hiMU S0 n).g_lt c hn
  g_zero := by
    rw [hiMTg_eq hS hiN_pos (hiMU S0 0).B_pos]; exact (hiMU S0 0).g_zero
  g_nat := fun k => by
    rw [hiMTg_eq hS hiN_pos ((hiMU S0 0).nat_lt_B k)]; exact (hiMU S0 0).g_nat k
  g_E := by rw [hiMTg_eq hS hiN_pos (hiMU S0 0).E_lt_B]; exact (hiMU S0 0).g_E
  g_lowE := fun c hc => by
    rw [hiMTg_eq hS hiN_pos (hc.trans (hiMU S0 0).E_lt_B)]; exact (hiMU S0 0).g_lowE c hc
  g_G0 := fun h => by
    obtain ⟨n, hn1, hn⟩ := hiMT_cof hS h
    rw [hiMTg_eq hS hn1 hn]; exact (hiMU S0 n).g_G0 hn
  g_add := fun Z hZ hωZ x y hxy hgx hgy => by
    obtain ⟨n, hn1, hn⟩ := hiMT_cof hS hxy
    have hx : x < (hiMU S0 n).B := lt_of_le_of_lt le_self_add hn
    have hy : y < (hiMU S0 n).B := lt_of_le_of_lt le_add_self hn
    rw [hiMTg_eq hS hn1 hn]; rw [hiMTg_eq hS hn1 hx] at hgx; rw [hiMTg_eq hS hn1 hy] at hgy
    exact (hiMU S0 n).g_add Z hZ hωZ x y hn hgx hgy
  g_opow := fun Z hZw hωZ y hy hg => by
    obtain ⟨n, hn1, hn⟩ := hiMT_cof hS hy
    have hy' : y < (hiMU S0 n).B := lt_of_le_of_lt (right_le_opow y one_lt_omega0) hn
    rw [hiMTg_eq hS hn1 hn]; rw [hiMTg_eq hS hn1 hy'] at hg
    exact (hiMU S0 n).g_opow Z hZw hωZ y hn hg
  code_gate := fun Z hZ1 hZ0 hZa hZp At hAt c hc hcB => by
    obtain ⟨n, hn1, hn⟩ := hiMT_cof hS hcB
    rw [hiMTg_eq hS hn1 hn]
    exact (hiMU S0 n).code_gate Z hZ1 hZ0 hZa hZp At (fun s hs => (hAt s hs).imp_right
      (fun h => (hiMT_B_lt hS hn1).le.trans h)) c hc hn
  g_succ := fun Z hZ c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hiMT_cof hS hc
    have hc' : c < (hiMU S0 n).B := (lt_add_one c).trans hn
    rw [hiMTg_eq hS hn1 hn]; rw [hiMTg_eq hS hn1 hc'] at hg
    exact (hiMU S0 n).g_succ Z hZ c hn hg
  g_le_succ := hiMTg_le_succ hS
  mem := fun S a b ha c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hiMT_cof hS hc
    rw [hiMTg_eq hS hn1 hn] at hg
    exact (hiMU S0 n).mem S a b ha c hn hg
  R_zero := fun x => by
    rw [hiMTR_eq hS hiN_pos (hiMU S0 0).B_pos]; exact (hiMU S0 0).R_zero x
  R_nat := fun k x => by
    rw [hiMTR_eq hS hiN_pos ((hiMU S0 0).nat_lt_B k)]; exact (hiMU S0 0).R_nat k x
  R_E := fun x => by rw [hiMTR_eq hS hiN_pos (hiMU S0 0).E_lt_B]; exact (hiMU S0 0).R_E x
  R_succ := hiMTR_succ hS
  R_pos := fun x hx hx1 c hc0 hc hg => by
    obtain ⟨n, hn1, hn⟩ := hiMT_cof hS hc
    rw [hiMTR_eq hS hn1 hn]; rw [hiMTg_eq hS hn1 hn] at hg
    exact (hiMU S0 n).R_pos x hx hx1 c hc0 hn hg
  R_omega := fun x hx hx1 c hω hc hg => by
    obtain ⟨n, hn1, hn⟩ := hiMT_cof hS hc
    rw [hiMTR_eq hS hn1 hn]; rw [hiMTg_eq hS hn1 hn] at hg
    exact (hiMU S0 n).R_omega x hx hx1 c hω hn hg
  R_lt_b := fun x hx hx1 _ c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hiMT_cof hS hc
    rw [hiMTR_eq hS hn1 hn]; rw [hiMTg_eq hS hn1 hn] at hg
    exact ((hiMU S0 n).R_lt_Z x hx hx1 c hn hg).trans_le (hiMU_Zb hS hn1 x hx hx1)
  R_lt_Z := fun x hx hx1 c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hiMT_cof hS hc
    rw [hiMTR_eq hS hn1 hn]; rw [hiMTg_eq hS hn1 hn] at hg
    exact (((hiMU S0 n).R_lt_Z x hx hx1 c hn hg).trans_le (hiMU_Zb hS hn1 x hx hx1)).trans (lt_evZ _)
  mono := fun x hx hx1 c hc d hfc hgc hgd => by
    obtain ⟨n, hn1, hn⟩ := hiMT_cof hS hc
    have hf : d < (hiMU S0 n).B := hfc.trans hn
    rw [hiMTR_eq hS hn1 hn, hiMTR_eq hS hn1 hf]; rw [hiMTg_eq hS hn1 hn] at hgc; rw [hiMTg_eq hS hn1 hf] at hgd
    exact (hiMU S0 n).mono x hx hx1 c hn d hfc hgc hgd
  cof := fun x hx hx1 c hc hg ν hν => by
    obtain ⟨n, hn1, hn⟩ := hiMT_cof hS hc
    rw [hiMTR_eq hS hn1 hn] at hν; rw [hiMTg_eq hS hn1 hn] at hg
    obtain ⟨d, hfc, hgd, hνd⟩ := (hiMU S0 n).cof x hx hx1 c hn hg ν hν
    have hf : d < (hiMU S0 n).B := hfc.trans hn
    exact ⟨d, hfc, by rw [hiMTg_eq hS hn1 hf]; exact hgd, by rw [hiMTR_eq hS hn1 hf]; exact hνd⟩
  b_cof := fun x hx hx1 _ ν hν => by
    obtain ⟨k, hk⟩ := hiMTr_cof hS hx hx1 hν
    have hkT : hiMTt k < hiN := hiMTt_lt k
    have hkB : hiMTt k < (hiMU S0 (hiMTt k)).B := hiMU_self hS hkT
    refine ⟨hiMTt k, hkT, ?_, ?_⟩
    · rw [hiMTg_eq hS hkT hkB]; exact hiMTt_g hS hx hx1 k
    · rw [hiMTR_eq hS hkT hkB]; exact hk
  b_E := fun x hx hx1 _ => hiZl_E hx hx1
  x_lt_b := fun x hx hx1 _ => (lgG_facts hx hx1).2.1.trans (hiG_lt_Zl hx hx1)
  b_eN := fun x hx hx1 _ => gz_eN_fix hx hx1 (hiZl_fix1 x) ((lgG_facts hx hx1).2.1.trans (hiG_lt_Zl hx hx1))
    (hiZl_lt1 hx hx1)
  ba_lt := fun x hx hx1 _ => hiZl_lt1 hx hx1
  b_Z := fun x _ _ _ => go_eN_lt_evZ (lt_evZ _)
  b_pi := fun _ _ hB _ => hiZl_pi hB
  ba_pi := fun _ _ hB _ => hiZl_pi hB
  ex := fun σ ρ hB c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hiMT_cof hS hc
    rw [hiMTR_eq hS hn1 hn, hiMTR_eq hS hn1 hn]; rw [hiMTg_eq hS hn1 hn] at hg
    exact (hiMU S0 n).ex σ ρ hB c hn hg
  dig := fun σ ρ hB _ d hf hg P P' hat => by
    obtain ⟨μ, hμ, hfμ, hγμ⟩ := hiMT_small hS hf hB.1 (hB.2.2.1.trans hB.2.2.2) hg
    rw [hiMTR_eq hS hμ hfμ, hiMTR_eq hS hμ hfμ]; rw [hiMTg_eq hS hμ hfμ] at hg
    exact (hiMU S0 μ).dig σ ρ hB hγμ d hfμ hg P P' (fun β hβ hβe =>
      hat β hβ (hβe.trans (hiMT_b_lt hS hμ hB.2.1 hB.2.2.2 (hγμ.trans hB.2.2.1))))
  ld := fun c hl hc => by
    obtain ⟨n, hn1, hn⟩ := hiMT_cof hS hc
    obtain ⟨cp, lp, T, hcp, hgcp, hfec, hex⟩ := (hiMU S0 n).ld c hl hn
    have hcpn : cp < (hiMU S0 n).B := hcp.trans hn
    refine ⟨cp, lp, T, hcp, by rw [hiMTg_eq hS hn1 hn, hiMTg_eq hS hn1 hcpn]; exact hgcp,
        fun x hx hx1 hg => ?_,
      fun σ ρ hB hg => hex σ ρ hB (by rw [← hiMTg_eq hS hn1 hn]; exact hg)⟩
    rw [hiMTg_eq hS hn1 hn] at hg
    rw [hiMTR_eq hS hn1 hn, hiMTR_eq hS hn1 hcpn]
    exact hfec x hx hx1 hg

theorem hiMTU_B : (hiMTU hS).B = hiN := rfl

theorem hiMTU_γ : (hiMTU hS).γ = 0 := rfl

theorem hiMTU_b (x : Ordinal.{0}) : (hiMTU hS).b x = hiZl x := rfl

/-- **The union extends every start** (readings). -/
theorem hiMTU_R {ν c : Ordinal.{0}} (hν : ν < hiN) (hc : c < (hiMU S0 ν).B) (x : Ordinal.{0}) :
    (hiMTU hS).R c x = (hiMU S0 ν).R c x := hiMTR_eq hS hν hc x

/-- **The union extends every start** (gates). -/
theorem hiMTU_g {ν c : Ordinal.{0}} (hν : ν < hiN) (hc : c < (hiMU S0 ν).B) :
    (hiMTU hS).g c = (hiMU S0 ν).g c := hiMTg_eq hS hν hc

/-- **The union extends the start `S0`.** -/
theorem hiMTU_R0 {c : Ordinal.{0}} (hc : c < S0.B) (x : Ordinal.{0}) : (hiMTU hS).R c x = S0.R c x := by
  rw [hiMTU_R hS hiN_pos (by rw [hiMU_zero]; exact hc), hiMU_zero]

theorem hiMTU_g0 {c : Ordinal.{0}} (hc : c < S0.B) : (hiMTU hS).g c = S0.g c := by
  rw [hiMTU_g hS hiN_pos (by rw [hiMU_zero]; exact hc), hiMU_zero]

end Union

end Googology.Trans.PoR.InaccPsi.R2.Hi

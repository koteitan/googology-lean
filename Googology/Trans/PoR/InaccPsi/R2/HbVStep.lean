import Googology.Trans.PoR.InaccPsi.R2.HbVHL

/-!
# HbVStep: TEXTUAL COPY OF `Gz.GzVStep` FOR `Hb.HbVD` (readings below `B_ω(x)`)

The declarations of `Gz.GzVStep` with `Gz.GzVD` (bound field `Z(x) ≤ B₃(x)`) replaced by `Hb.HbVD` (bound field
`Z(x) ≤ B_ω(x)`, `Hb.hbBw`); the proofs are unchanged except where the bound enters (`HbVD.R_lt_gq`, the field `Z_Bw`,
Lemma IMG in `HbVD.toLD` through `Hb.hb_pkg_Bw`).

No new axiom.  New definitions: the copies of the definitions of `Gz.GzVStep` (namespace `HbVD`).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hb

open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha

open Googology.Trans.PoR.InaccPsi.R2.Gw

open Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq Googology.Trans.PoR.InaccPsi.R2.Gr

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Go
  Googology.Trans.PoR.InaccPsi.R2.Gq
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

namespace HbVD

variable (D : HbVD)

theorem γ_lt_Om1 : D.γ < Om1 := D.γ_lt

/-! ## The gate of the step -/

/-- **The gate of the step**: `max γ (D.hG c)` for the codes `c ≥ B` (they use the base reading), `D.hG c` below. -/
noncomputable def sG (c : Ordinal.{0}) : Ordinal.{0} := if D.B ≤ c then max D.γ (D.hG c) else D.hG c

theorem sG_low {c : Ordinal.{0}} (hc : c < D.B) : D.sG c = D.g c := by
  unfold HbVD.sG; rw [if_neg (not_le.2 hc), D.hG_low hc]

theorem sG_high {c : Ordinal.{0}} (hc : D.B ≤ c) : D.sG c = max D.γ (D.hG c) := by
  unfold HbVD.sG; rw [if_pos hc]

theorem hG_le_sG (c : Ordinal.{0}) : D.hG c ≤ D.sG c := by
  unfold HbVD.sG; split_ifs
  · exact le_max_right _ _
  · exact le_rfl

theorem γ_le_sG {c : Ordinal.{0}} (hc : D.B ≤ c) : D.γ ≤ D.sG c := by
  rw [D.sG_high hc]; exact le_max_left _ _

theorem sG_lt {c Z : Ordinal.{0}} (h1 : D.hG c < Z) (h2 : D.B ≤ c → D.γ < Z) : D.sG c < Z := by
  unfold HbVD.sG; split_ifs with h
  · exact max_lt (h2 h) h1
  · exact h1

theorem γ_lt_of_sG {c Z : Ordinal.{0}} (hc : D.B ≤ c) (h : D.sG c < Z) : D.γ < Z :=
  (D.γ_le_sG hc).trans_lt h

theorem B_le_add {x y : Ordinal.{0}} (h : D.B ≤ x + y) : D.B ≤ x ∨ D.B ≤ y := by
  by_contra hc
  push Not at hc
  exact absurd h (not_le.2 ((inE_indec D.B_E).add_lt hc.1 hc.2))

/-! ## The towers (as in `R2.GoStep`) -/

theorem hR_succ_all (b x : Ordinal.{0}) : D.hR (b + 1) x = D.hR b x + 1 := by
  rcases lt_or_ge (b + 1) D.NB with h | h
  · exact D.hR_succ b h x
  · have hb : D.NB ≤ b := by
      by_contra hb; push Not at hb; exact absurd (D.NB_lim.add_one_lt hb) (not_lt.2 h)
    rw [D.hR_high h, D.hR_high hb, D.R_succ]

theorem hG_le_succ_all (b : Ordinal.{0}) : D.hG b ≤ D.hG (b + 1) := by
  rcases lt_or_ge (b + 1) D.NB with h | h
  · exact D.hG_le_succ b h
  · have hb : D.NB ≤ b := by
      by_contra hb; push Not at hb; exact absurd (D.NB_lim.add_one_lt hb) (not_lt.2 h)
    rw [D.hG_high h, D.hG_high hb]; exact D.g_le_succ b

theorem hG_pow {k : Ordinal.{0}} (hk : k ≠ 0) (hkB : k < D.NB) : D.hG (D.B ^ k) = D.hQ k := by
  have e : D.B ^ k = D.B ^ k * 1 + 0 := by rw [mul_one, add_zero]
  rw [e, D.hG_cnf hk one_ne_zero D.one_lt_B (opow_pos _ D.B_pos) (by rw [← e]; exact D.NB_gt_pow hkB), D.Q_one,
    D.hG_zero, max_eq_left zero_le, max_eq_left zero_le]

theorem hR_pow {k : Ordinal.{0}} (hk : k ≠ 0) (hkB : k < D.NB) (x : Ordinal.{0}) :
    D.hR (D.B ^ k) x = D.b x ^ D.hR k x := by
  have e : D.B ^ k = D.B ^ k * 1 + 0 := by rw [mul_one, add_zero]
  rw [e, D.hR_cnf hk one_ne_zero D.one_lt_B (opow_pos _ D.B_pos) (by rw [← e]; exact D.NB_gt_pow hkB),
    D.R_one, mul_one, D.hR_zero, add_zero]

theorem hTw_g : ∀ n : ℕ, D.hG (D.hTw n) = 0
  | 0 => D.hG_G
  | n + 1 => by
    show D.hG (D.B ^ D.hTw n) = 0
    have h0 : D.hTw n ≠ 0 := (D.B_pos.trans_le (D.hTw_ge n)).ne'
    rw [D.hG_pow h0 (D.hTw_lt n)]
    unfold HbVD.hQ
    rw [if_neg (not_lt.2 (D.omega_lt_B.le.trans (D.hTw_ge n))), hTw_g n]

theorem sG_tw (n : ℕ) : D.sG (D.hTw n) = D.γ := by
  rw [D.sG_high (D.hTw_ge n), D.hTw_g, max_eq_left zero_le]

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγx : D.γ < x)
include hx hx1 hγx

theorem hTw_read : ∀ n : ℕ, (fun a : Ordinal.{0} => ω ^ a)^[n] (D.b x + 1) ≤ D.hR (D.hTw (n + 1)) x := by
  have hGE := D.b_E x hx hx1 hγx
  have h1G : (1 : Ordinal.{0}) < D.b x := one_lt_omega0.trans (omega0_lt_inE hGE)
  intro n
  induction n with
  | zero =>
    show D.b x + 1 ≤ D.hR (D.B ^ D.B) x
    rw [D.hR_pow D.B_ne D.B_lt_NB, D.hR_G]
    have : D.b x ^ (1 : Ordinal.{0}) < D.b x ^ D.b x := (opow_lt_opow_iff_right h1G).2 h1G
    rw [opow_one] at this
    exact Order.add_one_le_of_lt this
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    show ω ^ ((fun a : Ordinal.{0} => ω ^ a)^[n] (D.b x + 1)) ≤ D.hR (D.B ^ D.hTw (n + 1)) x
    have h0 : D.hTw (n + 1) ≠ 0 := (D.B_pos.trans_le (D.hTw_ge _)).ne'
    rw [D.hR_pow h0 (D.hTw_lt _)]
    calc ω ^ ((fun a : Ordinal.{0} => ω ^ a)^[n] (D.b x + 1)) ≤ ω ^ D.hR (D.hTw (n + 1)) x :=
          opow_le_opow_right omega0_pos ih
      _ ≤ D.b x ^ D.hR (D.hTw (n + 1)) x := opow_le_opow_left _ (omega0_lt_inE hGE).le

/-- **The readings of the codes below `ε_{B+1}` are cofinal in `ε_{b(x)+1}`** at every base above the gate. -/
theorem NB_cof {ν : Ordinal.{0}} (hν : ν < eN (D.b x)) :
    ∃ c, c < D.NB ∧ D.sG c < x ∧ ν < D.hR c x := by
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hν
  exact ⟨D.hTw (n + 1), D.hTw_lt _, by rw [D.sG_tw]; exact hγx, hn.trans_le (D.hTw_read hx hx1 hγx n)⟩

end Base

/-! ## The step -/

theorem step_g_add {Z : Ordinal.{0}} (hZ : ∀ u v, u < Z → v < Z → u + v < Z) (hωZ : ω < Z) (x y : Ordinal.{0})
    (hxy : x + y < D.NB) (hgx : D.sG x < Z) (hgy : D.sG y < Z) : D.sG (x + y) < Z := by
  refine D.sG_lt (D.h_add hZ hωZ x y hxy ((D.hG_le_sG x).trans_lt hgx) ((D.hG_le_sG y).trans_lt hgy)) fun h => ?_
  rcases D.B_le_add h with h1 | h1
  · exact D.γ_lt_of_sG h1 hgx
  · exact D.γ_lt_of_sG h1 hgy

theorem step_g_opow {Z : Ordinal.{0}} (hZw : ∀ u, u < Z → ω ^ u < Z) (hωZ : ω < Z) (y : Ordinal.{0})
    (hy : ω ^ y < D.NB) (hg : D.sG y < Z) : D.sG (ω ^ y) < Z := by
  refine D.sG_lt (D.h_opow hZw hωZ (omega0_pos.trans hωZ) y hy ((D.hG_le_sG y).trans_lt hg)) fun h => ?_
  refine D.γ_lt_of_sG ?_ hg
  by_contra hyB
  push Not at hyB
  exact absurd h (not_le.2 (D.B_E.opow_lt hyB))

theorem step_g_succ {Z : Ordinal.{0}} (hZ : IsSuccLimit Z) (c : Ordinal.{0}) (hc : c + 1 < D.NB)
    (hg : D.sG c < Z) : D.sG (c + 1) < Z := by
  refine D.sG_lt (D.hG_succ hZ c hc ((D.hG_le_sG c).trans_lt hg)) fun h => ?_
  refine D.γ_lt_of_sG ?_ hg
  by_contra hcB
  push Not at hcB
  exact absurd h (not_le.2 (D.B_lim.add_one_lt hcB))

theorem step_g_le_succ (c : Ordinal.{0}) : D.sG c ≤ D.sG (c + 1) := by
  rcases lt_or_ge c D.B with h | h
  · have h1 : c + 1 < D.B := D.B_lim.add_one_lt h
    rw [D.sG_low h, D.sG_low h1]
    exact D.g_le_succ c
  · rw [D.sG_high h, D.sG_high (h.trans (le_self_add (a := c) (b := 1)))]
    exact max_le_max le_rfl (D.hG_le_succ_all c)

theorem step_cof {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (c : Ordinal.{0}) (hc : c < D.NB)
    (hg : D.sG c < x) (ν : Ordinal.{0}) (hν : ν < D.hR c x) : ∃ d, d < c ∧ D.sG d < x ∧ ν ≤ D.hR d x := by
  rcases lt_or_ge c D.B with hcB | hcB
  · rw [D.sG_low hcB] at hg
    rw [D.hR_low hcB] at hν
    obtain ⟨d, hdc, hgd, hνd⟩ := D.cof x hx hx1 c hcB hg ν hν
    exact ⟨d, hdc, by rw [D.sG_low (hdc.trans hcB)]; exact hgd, by rw [D.hR_low (hdc.trans hcB)]; exact hνd⟩
  · have hγx := D.γ_lt_of_sG hcB hg
    obtain ⟨d, hdc, hgd, hνd⟩ := D.hR_cof hx hx1 hγx c hc ((D.hG_le_sG c).trans_lt hg) ν hν
    exact ⟨d, hdc, D.sG_lt hgd fun _ => hγx, hνd⟩

theorem step_ex (σ ρ : Ordinal.{0}) (hB : Bases σ ρ) (c : Ordinal.{0}) (hc : c < D.NB) (hg : D.sG c < σ) :
    D.hR c ρ ∈ TB ρ σ ∧ pi σ ρ (D.hR c ρ) = D.hR c σ := by
  rcases lt_or_ge c D.B with hcB | hcB
  · rw [D.sG_low hcB] at hg
    rw [D.hR_low hcB, D.hR_low hcB]
    exact D.ex σ ρ hB c hcB hg
  · exact D.hR_pi hB (D.γ_lt_of_sG hcB hg) c hc ((D.hG_le_sG c).trans_lt hg)

theorem step_dig (σ ρ : Ordinal.{0}) (hB : Bases σ ρ) (hγ : D.γ < σ) (d : Ordinal.{0}) (hd : d < D.NB) (hg : D.sG d < σ)
    (P P' : Ordinal.{0})
    (hat : ∀ β, β ∈ TB ρ σ → β < eN (D.b ρ) → ω ^ (P + β) ∈ TB ρ σ ∧ pi σ ρ (ω ^ (P + β)) = ω ^ (P' + pi σ ρ β)) :
    ω ^ P * D.hR d ρ ∈ TB ρ σ ∧ pi σ ρ (ω ^ P * D.hR d ρ) = ω ^ P' * D.hR d σ := by
  rcases lt_or_ge d D.B with hdB | hdB
  · rw [D.sG_low hdB] at hg
    rw [D.hR_low hdB, D.hR_low hdB]
    exact D.dig σ ρ hB hγ d hdB hg P P' (fun β hβ hβe => hat β hβ (hβe.trans (lt_eN _)))
  · exact D.hdig hB hγ d hd ((D.hG_le_sG d).trans_lt hg) P P' hat

theorem step_ld : ∀ c, IsSuccLimit c → c < D.NB → ∃ (cp : Ordinal.{0}) (lp T : Ordinal.{0} → Ordinal.{0}),
    cp < c ∧ D.sG cp ≤ D.sG c ∧
    (∀ x, InE x → x < Om1 → D.sG c < x →
      D.hR c x = lp x + ω ^ T x ∧ ω ^ T x ∣ lp x ∧ T x ≠ 0 ∧ lp x ≤ D.hR cp x) ∧
    ∀ σ ρ, Bases σ ρ → D.sG c < σ → T ρ ∈ TB ρ σ ∧ pi σ ρ (T ρ) = T σ := by
  intro c hl hc
  rcases lt_or_ge c D.B with hcB | hcB
  · obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := D.ld c hl hcB
    have hcpB : cp < D.B := hcp.trans hcB
    refine ⟨cp, lp, T, hcp, by rw [D.sG_low hcB, D.sG_low hcpB]; exact hgcp, fun x hx hx1 hg => ?_,
      fun σ ρ hB hg => hex σ ρ hB (by rw [← D.sG_low hcB]; exact hg)⟩
    rw [D.sG_low hcB] at hg
    rw [D.hR_low hcB, D.hR_low hcpB]
    exact hdec x hx hx1 hg
  · obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := D.hld c hl hc
    refine ⟨cp, lp, T, hcp, ?_, fun x hx hx1 hg => hdec x hx hx1 ((D.hG_le_sG c).trans_lt hg) (D.γ_lt_of_sG hcB hg),
      fun σ ρ hB hg => hex σ ρ hB ((D.hG_le_sG c).trans_lt hg) (D.γ_lt_of_sG hcB hg)⟩
    rcases lt_or_ge cp D.B with hcpB | hcpB
    · rw [D.sG_low hcpB, ← D.hG_low hcpB]; exact hgcp.trans (D.hG_le_sG c)
    · rw [D.sG_high hcpB, D.sG_high hcB]; exact max_le_max le_rfl hgcp

/-! ## The fields of the step that hold at every base (case split at `B`) -/

theorem step_mem {S : InaccSeq.{0}} {a b : Ordinal.{0}} (ha : 0 < a) (c : Ordinal.{0}) (hc : c < D.NB)
    (hg : D.sG c < b) : c ∈ S.CSet a b ∧ ∀ e ∈ S.CSet a b, ω ^ e * c ∈ S.CSet a b := by
  rcases lt_or_ge c D.B with hcB | hcB
  · rw [D.sG_low hcB] at hg; exact D.mem S a b ha c hcB hg
  · exact D.hmem ha (D.γ_lt_of_sG hcB hg) c hc ((D.hG_le_sG c).trans_lt hg)

section Any

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem step_pos {c : Ordinal.{0}} (hc0 : c ≠ 0) (hcB : c < D.NB) (hg : D.sG c < x) : 0 < D.hR c x := by
  rcases lt_or_ge c D.B with h | h
  · rw [D.sG_low h] at hg; rw [D.hR_low h]; exact D.R_pos x hx hx1 c hc0 h hg
  · exact D.hR_pos hx hx1 (D.γ_lt_of_sG h hg) hc0 hcB ((D.hG_le_sG c).trans_lt hg)

theorem step_omega {c : Ordinal.{0}} (hω : ω ≤ c) (hcB : c < D.NB) (hg : D.sG c < x) : ω ≤ D.hR c x := by
  rcases lt_or_ge c D.B with h | h
  · rw [D.sG_low h] at hg; rw [D.hR_low h]; exact D.R_omega x hx hx1 c hω h hg
  · exact D.omega_le_hR hx hx1 (D.γ_lt_of_sG h hg) hω hcB ((D.hG_le_sG c).trans_lt hg)

/-- **The readings of the step lie below `Z(x)` at every base** (above the gate through `ε_{b(x)+1}`). -/
theorem step_lt_Z {c : Ordinal.{0}} (hcB : c < D.NB) (hg : D.sG c < x) : D.hR c x < D.Z x := by
  rcases lt_or_ge c D.B with h | h
  · rw [D.sG_low h] at hg; rw [D.hR_low h]; exact D.R_lt_Z x hx hx1 c h hg
  · have hγx := D.γ_lt_of_sG h hg
    exact (D.hR_lt_eNb hx hx1 hγx hcB ((D.hG_le_sG c).trans_lt hg)).trans
      ((lt_eN _).trans (gz_eN_lt_fix (D.Z_fix x hx hx1) (D.b_Z x hx hx1 hγx)))

theorem step_mono {c d : Ordinal.{0}} (hc : c < D.NB) (hdc : d < c) (hgc : D.sG c < x) (hgd : D.sG d < x) :
    D.hR d x < D.hR c x := by
  rcases lt_or_ge c D.B with h | h
  · rw [D.sG_low h] at hgc; rw [D.sG_low (hdc.trans h)] at hgd
    rw [D.hR_low h, D.hR_low (hdc.trans h)]; exact D.mono x hx hx1 c h d hdc hgc hgd
  · exact D.hR_mono hx hx1 (D.γ_lt_of_sG h hgc) c hc d hdc ((D.hG_le_sG c).trans_lt hgc)
      ((D.hG_le_sG d).trans_lt hgd)

end Any

/-- **The code-gate condition of the codes `c ≥ B`**: such a code over `Z` (atoms `G` and `≥ ε_{B+1}`) has `B` as a
code over `Z` (`gr_cl_restrict`, `gr_cl_B`), so `γ < Z` by the condition of the base. -/
theorem step_cl (Z : Ordinal.{0}) (hZ1 : Z ≤ Om1) (hZ0 : 0 < Z) (hZp : ∀ u v, u < Z → v < Z → veblen u v < Z)
    {At : Set Ordinal.{0}} (hAt : ∀ s ∈ At, s = gcG 0 ∨ D.NB ≤ s) {c : Ordinal.{0}} (hc : GxCl Z At c)
    (hcB : c < D.NB) (hBc : D.B ≤ c) : D.γ < Z := by
  have hZ1' : Z ≤ Om 1 := by rw [← Br.Om1_eq]; exact hZ1
  exact D.γ_cl Z (gr_SC_of hZ0 hZp) hZ1' (gr_cl_B hZ1' D.B_E D.G_le (gr_cl_restrict hAt hc hcB) hBc hcB)

/-- **The code-gate condition of the new base `ε_{B+1} = φ(1, ix + 1)`**: a code over `Z` has `B = φ(1, ix)` as a
code (`gr_cl_NB`). -/
theorem step_γ_cl (Z : Ordinal.{0}) (hZ : SC Z) (hZ1 : Z ≤ Om 1) (h : GxCl Z {gcG 0} D.NB) : D.γ < Z := by
  refine D.γ_cl Z hZ hZ1 ?_
  have hix : Om 1 ≤ D.ix := gr_Om1_le_ix (D.B_ix ▸ D.G_le)
  rw [D.NB_eq] at h
  rw [D.B_ix]
  exact gr_cl_NB hZ hZ1 hix h

/-- **THE GATED STEP**: the hereditary codes `B^k·d + r < ε_{B+1}` over a gated digit system at the base `B` form a
gated digit system at the base `ε_{B+1}` with the same base gate. -/
noncomputable def step : HbVD where
  Z := D.Z
  Z_fix := D.Z_fix
  Z_Bw := D.Z_Bw
  B := D.NB
  γ := D.γ
  γ_lt := D.γ_lt
  γ_cl := fun Z hZ hZ1 h => D.step_γ_cl Z hZ hZ1 h
  γ_G := fun h => absurd h (ne_of_gt (D.G_le.trans_lt D.B_lt_NB))
  R := D.hR
  g := D.sG
  b := fun x => eN (D.b x)
  ba := fun x => D.ba x + 1
  ix := D.ix + 1
  B_E := D.NB_E
  G_le := D.G_le.trans D.B_lt_NB.le
  B_lt1 := D.NB_lt1
  B_ix := D.NB_eq
  ix_mem := fun S a b ha hγb => CSet.succ_mem (D.ix_mem S a b ha hγb)
  g_lt := fun c hc => D.sG_lt (D.hG_lt_Om1 c hc) fun _ => D.γ_lt_Om1
  g_zero := by rw [D.sG_low D.B_pos]; exact D.g_zero
  g_nat := fun n => by rw [D.sG_low (D.nat_lt_B n)]; exact D.g_nat n
  g_E := by rw [D.sG_low D.E_lt_B]; exact D.g_E
  g_lowE := fun c hc => by rw [D.sG_low (hc.trans D.E_lt_B)]; exact D.g_lowE c hc
  g_G0 := fun _ => by
    rcases D.G_le.lt_or_eq with hlt | heq
    · rw [D.sG_low hlt, D.g_G0 hlt]
    · rw [heq, D.sG_high le_rfl, D.hG_G, D.γ_G heq.symm, max_self]
  g_add := fun _ hZ hωZ => D.step_g_add hZ hωZ
  g_opow := fun _ hZw hωZ => D.step_g_opow hZw hωZ
  code_gate := fun Z hZ1 hZ0 hZa hZp _ hAt _ hc hcB =>
    D.sG_lt (D.h_code_gate hZ1 hZ0 hZa hZp hAt hc hcB) fun hBc => D.step_cl Z hZ1 hZ0 hZp hAt hc hcB hBc
  g_succ := fun _ hZ c hc hg => D.step_g_succ hZ c hc hg
  g_le_succ := D.step_g_le_succ
  mem := fun _ _ _ ha c hc hg => D.step_mem ha c hc hg
  R_zero := D.hR_zero
  R_nat := D.hR_nat
  R_E := fun x => by rw [D.hR_low D.E_lt_B]; exact D.R_E x
  R_succ := D.hR_succ_all
  R_pos := fun _ hx hx1 _ hc0 hcB hg => D.step_pos hx hx1 hc0 hcB hg
  R_omega := fun _ hx hx1 _ ha haB hg => D.step_omega hx hx1 ha haB hg
  R_lt_b := fun _ hx hx1 hγx _ hc hg => D.hR_lt_eNb hx hx1 hγx hc ((D.hG_le_sG _).trans_lt hg)
  R_lt_Z := fun _ hx hx1 _ hc hg => D.step_lt_Z hx hx1 hc hg
  mono := fun _ hx hx1 c hc d hdc hgc hgd => D.step_mono hx hx1 hc hdc hgc hgd
  cof := fun _ hx hx1 c hc hg ν hν => D.step_cof hx hx1 c hc hg ν hν
  b_cof := fun _ hx hx1 hγx _ hν => D.NB_cof hx hx1 hγx hν
  b_E := fun _ _ _ _ => eN_E _
  x_lt_b := fun x hx hx1 hγx => (D.x_lt_b x hx hx1 hγx).trans (lt_eN _)
  b_eN := fun x hx hx1 hγx => by
    obtain ⟨hT, h1⟩ := gm1_T hx hx1 (D.ba_lt x hx hx1 hγx)
    rw [D.b_eN x hx hx1 hγx]; exact glA_eN_one hx hx1 hT h1
  ba_lt := fun x hx hx1 hγx =>
    (ev_isSuccLimit_of_inE (gm1_facts hx hx1).2.2.2).add_one_lt (D.ba_lt x hx hx1 hγx)
  b_Z := fun x hx hx1 hγx => gz_eN_lt_fix (D.Z_fix x hx hx1) (D.b_Z x hx hx1 hγx)
  b_pi := fun _ _ hB hγ => D.eN_b_pi hB hγ
  ba_pi := fun σ ρ hB hγ => by
    obtain ⟨g1, g2⟩ := D.ba_pi σ ρ hB hγ
    obtain ⟨o1, o2⟩ := one_TB hB
    obtain ⟨s1, s2⟩ := pi_add hB g1 o1
    exact ⟨s1, by rw [s2, g2, o2]⟩
  ex := D.step_ex
  dig := D.step_dig
  ld := D.step_ld

theorem step_B : D.step.B = eN D.B := rfl

theorem step_γ : D.step.γ = D.γ := rfl

theorem step_Z : D.step.Z = D.Z := rfl

theorem step_R : D.step.R = D.hR := rfl

theorem step_g : D.step.g = D.sG := rfl

theorem step_b (x : Ordinal.{0}) : D.step.b x = eN (D.b x) := rfl

theorem step_ba (x : Ordinal.{0}) : D.step.ba x = D.ba x + 1 := rfl

theorem step_ix : D.step.ix = D.ix + 1 := rfl

/-- The step keeps the readings and the gates of the digits. -/
theorem step_R_low {c : Ordinal.{0}} (hc : c < D.B) (x : Ordinal.{0}) : D.step.R c x = D.R c x := D.hR_low hc x

theorem step_g_low {c : Ordinal.{0}} (hc : c < D.B) : D.step.g c = D.g c := D.sG_low hc

/-- The gate of the old bound in the step is the base gate. -/
theorem step_g_B : D.step.g D.B = D.γ := by
  show D.sG D.B = D.γ
  rw [D.sG_high le_rfl, D.hG_G, max_eq_left zero_le]

end HbVD

end Googology.Trans.PoR.InaccPsi.R2.Hb

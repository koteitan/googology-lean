import Googology.Trans.PoR.InaccPsi.R2.YrLDN
import Googology.Trans.PoR.InaccPsi.R2.YrLoc
import Googology.Trans.PoR.InaccPsi.R2.YrImg

/-!
# YrDir: THE DIRECT READING OF EVERY LAYER BELOW `B_Γ` — `YrDirect S B_Γ` (ONE THEOREM, NO CONSTANT INDEX)

The reading `Yr.yrR` (atom indices read) below every `ε`-number bound `G < B < B_Γ` is a reading system with
admissible readings (`Yr.YrRS`): code system `yrKN B` (hulls `Yr.yr_mem`, code gate `Yr.yr_code_gate`,
countability through `Tˣ ∩ Ω₁` being a countable ordinal), Lemma EXACT `Yr.yr_pi`, cofinality `Yr.yrR_cof`, the
limit data `Yr.yr_ldN` with Lemma IMG by `Yr.yrPkgN` (Lemma IMG below every admissible read bound, `Yr.YrImg`).
The tower `a₀ = G`, `a_{n+1} = Γ(a_n)` (gate `0`) is cofinal in `B_Γ = nfp Γ (Ω₁+1)`, so the route (c) holds below
`B_Γ`, for every layer `c < B_Γ` at once (the layers with `ε₀ ≤ c + 1` included):

* `yrKN`, `yrRSN` (**THE READING SYSTEM BELOW `B`**, `G < B < B_Γ` an `ε`-number), `yrTw`, `yrTw_cof`;
* `yrDirect` (**`YrDirect S B_Γ`, UNCONDITIONAL**), `yrLayAll` (**UPPER ∧ LOWER ∧ CapV at every range restart below
  `ι(Γ(φ(ℓ, Γ(c)+1))·ω)` for every layer `c < B_Γ` and every `ℓ < Γ(c+1)`**: the conclusions of `skLayLo` and
  `skLayHi`, so of `skLayLoBig` and `skLayHiBig` for `c < B_Γ`);
* non-vacuity: `yrDirect_eps0` (**the layer `c = ε₀`**, the first case `Yh.yhDirect` does not reach), `yr_eps0_lt_BG`.

No new axiom.  New definitions: `yrKN`, `yrRSN`, `yrTw`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yr

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi
  Googology.Notation.InaccPsi.InaccSeq Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Xu
  Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Xk Googology.Trans.PoR.InaccPsi.R2.Xx
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gh Googology.Trans.PoR.InaccPsi.R2.Yh

theorem yr_count {B c y : Ordinal.{0}} (hBB : B < Tf.tfBG) (hc : c ≤ B) (hy : InE y) (hy1 : y < Om1) :
    Countable {b : Iio c // yrG b.1 < y} := by
  obtain ⟨m, -, -, -, hTm, hm1⟩ := T_next (Or.inr hy) hy1
  have hm1' : m < Om (1 : Ordinal.{0}) := by rw [← Br.Om1_eq]; exact hm1
  haveI := Gc.gc_countable hm1'
  have hlt : ∀ b : {b : Iio c // yrG b.1 < y}, yrR b.1.1 y < m := fun b => by
    obtain ⟨hT, h1⟩ := yrR_T hy hy1 ((lt_of_lt_of_le b.1.2 hc).trans hBB) b.2
    exact (hTm _ h1).1 hT
  let f : {b : Iio c // yrG b.1 < y} → Iio m := fun b => ⟨yrR b.1.1 y, hlt b⟩
  refine Function.Injective.countable (f := f) fun b b' hbb => ?_
  have e : yrR b.1.1 y = yrR b'.1.1 y := congrArg Subtype.val hbb
  rcases lt_trichotomy b.1.1 b'.1.1 with h | h | h
  · exact absurd e (yrR_mono hy hy1 ((lt_of_lt_of_le b'.1.2 hc).trans hBB) h b'.2 b.2).ne
  · exact Subtype.ext (Subtype.ext h)
  · exact absurd e (yrR_mono hy hy1 ((lt_of_lt_of_le b.1.2 hc).trans hBB) h b.2 b'.2).ne'

/-- **The code system of the codes below `B < B_Γ`**: gate `yrG`, atoms `Γ(c)`. -/
noncomputable def yrKN (B : Ordinal.{0}) (hBB : B < Tf.tfBG) : GsCS where
  B := B
  gt := yrG
  B_V := yr_idx_BG hBB
  gt_zero := yrG_zero
  gt_lt := fun c _ => yrG_lt_Om1 c
  gt_succ := fun b _ hZ _ hg => yrG_succ hZ b hg
  mem := fun S _ _ c hc hca hg => (yr_mem (S := S) c (hc.trans hBB) hca hg).1
  κ := yrG B
  κ_lt := yrG_lt_Om1 B
  B_mem := fun S _ _ ha hκ => (yr_mem (S := S) B hBB ha hκ).1
  code_gate := fun Z hZ1 hZ0 _ hZp c hc _ => by
    have hSC : SC Z := ⟨hZ0, fun u hu v hv => hZp u v hu hv⟩
    have hZ1' : Z ≤ Om1 := hZ1
    refine yr_code_gate hSC hZ1' ?_ c hc
    rintro s ⟨c', hc', hg', rfl⟩
    exact ⟨c', rfl, yr_idx_BG (hc'.trans hBB), hg'⟩
  count := fun _ _ hc hy hy1 => yr_count hBB hc hy hy1

theorem yr_cofEN {x c : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hc : c < Tf.tfBG)
    (hEc : gfE < c) (hg : yrG c < x) {ν : Ordinal.{0}} (hν : ν < yrR c x) :
    ∃ b, gfE ≤ b ∧ b < c ∧ yrG b < x ∧ ν ≤ yrR b x := by
  have hgE : yrG gfE = 0 := by rw [yrG_low gfE_lt_G0, glG_E]
  obtain ⟨b, hbc, hgb, hνb⟩ := yrR_cof hx hx1 c hc hg ν hν
  rcases lt_or_ge b gfE with hbE | hbE
  · refine ⟨gfE, le_rfl, hEc, by rw [hgE]; exact hx.pos, ?_⟩
    exact hνb.trans (yrR_mono hx hx1 (hEc.trans hc) hbE (by rw [hgE]; exact hx.pos) hgb).le
  · exact ⟨b, hbE, hbc, hgb, hνb⟩

/-- **The limit data with Lemma IMG** at every limit code `ε_{Ω₁+1} < d < B`. -/
theorem yr_ldGsN (B : Ordinal.{0}) (hBB : B < Tf.tfBG) :
    ∀ d, IsSuccLimit d → gfE < d → d < B → Nonempty (GsmLD (yrKN B hBB) yrR d) := by
  intro d hl hEd hd
  have hdB : d < Tf.tfBG := hd.trans hBB
  have hgE : yrG gfE = 0 := by rw [yrG_low gfE_lt_G0, glG_E]
  obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := yr_ldN d hl hdB
  have hlg : ∀ x, InE x → x < Om1 → yrG d < x → lg (yrR d x) = T x := fun x hx hx1 hg => by
    obtain ⟨e1, e2, -, -⟩ := hdec x hx hx1 hg
    rw [e1]; exact Ge.lg_add_opow e2
  refine ⟨{
    cp := if gfE ≤ cp then cp else gfE
    lp := lp
    cp_ge := ?_
    cp_lt := ?_
    cp_g := ?_
    dec := ?_
    pkg := ?_ }⟩
  · split_ifs with h
    · exact h
    · exact le_rfl
  · split_ifs with h
    · exact hcp
    · exact hEd
  · show yrG _ ≤ yrG d
    split_ifs with h
    · exact hgcp
    · rw [hgE]; exact zero_le
  · intro x hx hx1 hg
    obtain ⟨e1, e2, e3, e4⟩ := hdec x hx hx1 hg
    show yrR d x = _ ∧ _
    rw [hlg x hx hx1 hg]
    refine ⟨e1, e2, e3, ?_⟩
    split_ifs with h
    · exact e4
    · push Not at h
      exact e4.trans (yrR_mono hx hx1 (hEd.trans hdB) h (by rw [hgE]; exact hx.pos)
        (hgcp.trans_lt hg)).le
  · intro ρ τ δ h hg
    show GhPkg (yrG d) ρ δ (fun y => lg (yrR d y))
    have hρE := upsPt_inE h.ρU
    obtain ⟨e1, -, -, -⟩ := hdec ρ hρE h.ρ1 hg
    have hTN : YrN ρ (T ρ) := by
      have h1 : T ρ ≤ yrR d ρ := by
        rw [e1]; exact (right_le_opow _ one_lt_omega0).trans le_add_self
      exact yrN_down hρE h.ρ1 (yrR_N hρE h.ρ1 hdB hg) h1
    have hP := yrPkgN h hTN hg (C := ∅) (by simp) (Gj.GjEx.of_bases fun σ ρ' hB hgσ => hex σ ρ' hB hgσ)
    exact GhPkg.congr h hP (fun y hyE hy1 hgy => (hlg y hyE hy1 hgy).symm) hg

/-- **THE READING SYSTEM BELOW AN `ε`-NUMBER BOUND `G < B < B_Γ`** (read atom indices, admissible readings). -/
noncomputable def yrRSN (B : Ordinal.{0}) (hBE : InE B) (hGB : gcG 0 < B) (hBB : B < Tf.tfBG) : YrRS where
  K := yrKN B hBB
  R := yrR
  E_lt := gfE_lt_G0.trans hGB
  B_lim := ev_isSuccLimit_of_inE hBE
  gt_E := by show yrG gfE = 0; rw [yrG_low gfE_lt_G0, glG_E]
  gt_lowE := fun d hd => by show yrG d = gtc d; rw [yrG_low (hd.trans gfE_lt_G0), glG_low hd]
  R_E := fun x _ _ => by rw [yrR_low gfE_lt_G0, glR_E]
  lt0 := fun d x hx hx1 hd hg => yrR_N hx hx1 (hd.trans hBB) hg
  mono := fun b d x hx hx1 hd hbd hgb hgd => yrR_mono hx hx1 (hd.trans hBB) hbd hgd hgb
  succ := fun b x _ => yrR_succ b x
  gt_le_succ := yrG_le_succ
  cof := fun d x hx hx1 hd hEd hg ν hν => yr_cofEN hx hx1 (hd.trans hBB) hEd hg hν
  ex := fun σ ρ d hB hd hg => yr_pi hB d (hd.trans hBB) hg
  ld := yr_ldGsN B hBB

theorem yrRSN_B (B : Ordinal.{0}) (hBE : InE B) (hGB : gcG 0 < B) (hBB : B < Tf.tfBG) :
    (yrRSN B hBE hGB hBB).K.B = B := rfl

theorem yrRSN_gt (B : Ordinal.{0}) (hBE : InE B) (hGB : gcG 0 < B) (hBB : B < Tf.tfBG) :
    (yrRSN B hBE hGB hBB).K.gt = yrG := rfl

/-! ## The tower `G, Γ(G), Γ(Γ(G)), …` cofinal in `B_Γ` -/

/-- `Γ(c) < B_Γ` for `c < B_Γ`. -/
theorem yr_gcG_lt_BG {c : Ordinal.{0}} (hc : c < Tf.tfBG) : gcG c < Tf.tfBG := by
  rw [Tf.tf_gcG, ← Tf.tfBG_fix]
  exact gamma_lt_gamma.2 (SC.isPrincipal Tf.tfBG_SC (SC.add_one_lt Tf.tfBG_SC Tf.tfBG_gt) hc)

/-- **The tower**: `a₀ = G`, `a_{n+1} = Γ(a_n)`. -/
noncomputable def yrTw : ℕ → Ordinal.{0}
  | 0 => gcG 0
  | n + 1 => gcG (yrTw n)

theorem yrTw_lt_BG : ∀ n, yrTw n < Tf.tfBG
  | 0 => yr_gcG_lt_BG (lt_of_le_of_lt zero_le Tf.tfBG_gt)
  | n + 1 => yr_gcG_lt_BG (yrTw_lt_BG n)

theorem yrTw_lt_succ (n : ℕ) : yrTw n < yrTw (n + 1) := yr_idx_BG (yrTw_lt_BG n)

theorem yrTw_g : ∀ n, yrG (yrTw n) = 0
  | 0 => yrG_G0
  | n + 1 => by
    show yrG (gcG (yrTw n)) = 0
    rw [yrG_atom (yr_idx_BG (yrTw_lt_BG n))]
    unfold yrQ; split_ifs
    · rfl
    · exact yrTw_g n

theorem yrTw_ge (n : ℕ) : gcG 0 ≤ yrTw n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact ih.trans (yrTw_lt_succ n).le

theorem yrTw_E (n : ℕ) : InE (yrTw n) := by
  cases n with
  | zero => exact Low.opow_eq_self_of_SC (gcG_SC 0)
  | succ n => exact Low.opow_eq_self_of_SC (gcG_SC _)

/-- **THE TOWER IS COFINAL IN `B_Γ = nfp Γ (Ω₁+1)`**: `Γ^[n](Ω₁+1) ≤ a_n`. -/
theorem yrTw_cof : ∀ B, B < Tf.tfBG → ∃ n, B < yrTw n := by
  intro B hB
  have hit : ∀ n, gamma^[n] (Om1 + 1) ≤ yrTw n := by
    intro n
    induction n with
    | zero =>
      show Om1 + 1 ≤ gcG 0
      exact Order.add_one_le_of_lt (by rw [Br.Om1_eq]; exact gcG_Om1_lt 0)
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      show gamma (gamma^[n] (Om1 + 1)) ≤ gcG (yrTw n)
      rw [Tf.tf_gcG]
      exact gamma_le_gamma.2 (ih.trans le_add_self)
  obtain ⟨n, hn⟩ := (lt_nfp_iff (f := gamma)).1 hB
  exact ⟨n, hn.trans_le (hit n)⟩

/-- **ROUTE (c) BELOW `B_Γ`: `YrDirect S B_Γ`, UNCONDITIONAL**: every `B < B_Γ` lies below a tower code `a_n` (gate
`0`) of the reading system `yrRSN a_{n+1}`. -/
theorem yrDirect (S : InaccSeq.{0}) : YrDirect S Tf.tfBG := by
  intro B hB
  obtain ⟨n, hn⟩ := yrTw_cof B hB
  have hG : gcG 0 < yrTw (n + 1) := (yrTw_ge n).trans_lt (yrTw_lt_succ n)
  refine ⟨yrRSN (yrTw (n + 1)) (yrTw_E (n + 1)) hG (yrTw_lt_BG (n + 1)), yrTw n, hn.le,
    (gfE_lt_G0.trans_le (yrTw_ge n)).le, yrTw_lt_succ n, ?_⟩
  show yrG (yrTw n) < Td.tdK S
  rw [yrTw_g]; exact Td.tdK_SC.1

/-- **EVERY LAYER `c < B_Γ`** (`c + 1 < ε₀` or not): UPPER ∧ LOWER ∧ CapV at every range restart below
`ι(Γ(φ(ℓ, Γ(c)+1))·ω)`, `ℓ < Γ(c+1)` (the conclusions of `skLayLo` and `skLayHi` at `c`). -/
theorem yrLayAll (S : InaccSeq.{0}) {c : Ordinal.{0}} (hc : c < Tf.tfBG) : ∀ l, Cd.CdRange S l →
    (∃ ℓ, ℓ < gcG (c + 1) ∧ l < Bt.iota S (gcG (veblen ℓ (gcG c + 1)) * ω)) →
      Cd.CdUpper S l ∧ Cd.CdLower S l ∧ Cd.CdCapV S l := by
  have hc1 : c + 1 < Tf.tfBG := SC.add_one_lt Tf.tfBG_SC hc
  have hle : gcG (c + 1) ≤ Tf.tfBG := (yr_gcG_lt_BG hc1).le
  exact yrLay_of_direct (fun B hB => yrDirect S B (hB.trans_le hle))

/-- `ε₀ < B_Γ`. -/
theorem yr_eps0_lt_BG : ε₀ < Tf.tfBG := gc_eps0_le_Om1.trans_lt (by rw [← Br.Om1_eq]; exact Tf.tfBG_gt)

/-- **Non-vacuity: the layer `c = ε₀`** (`ε₀ ≤ c + 1`, out of reach of `Yh.yhDirect`). -/
theorem yrDirect_eps0 (S : InaccSeq.{0}) : YrDirect S (gcG (ε₀ + 1)) := fun B hB =>
  yrDirect S B (hB.trans (yr_gcG_lt_BG (SC.add_one_lt Tf.tfBG_SC yr_eps0_lt_BG)))

end Googology.Trans.PoR.InaccPsi.R2.Yr

import Googology.Trans.PoR.InaccPsi.R2.ZbAg
import Googology.Trans.PoR.InaccPsi.R2.YwU

/-!
# ZbBG: THE CODE `B_Γ` READ WITH THE ATOMS OF `zbU` — THE FIRST FRONTIER PAST `B_Γ`

The layer `Yw.ywBGB` of the code `B_Γ` (the union of the tower layers `Yw.ywTwL n`, top `D(x) = ϑˣ(Ω₁·Ω₁ + Ω₁)`)
reads its top code `B_Γ` with the atoms of `Zb.zbU`: `D(y) = Θ_y(B_Γ)` at every strongly critical `y`
(`Θ_y` continuous, the tower codes `a_n` cofinal in `B_Γ`, `Yr.YrRS.gqL_codes` at every `a_n`, `Zb.zb_th_yr`), and it
has terms for every code below `B_Γ` over every base.  `B_Γ = F_1(Ω₁+1)` is an atom of `zbU` over every `Z`.  So the
frontier lemma for the abstract atom system (`Zb.zbUV`) gives UPPER ∧ LOWER ∧ CapV at every range restart below
`ι(B_Γ·ω)`, the first frontier past every layer of `Yr` (`Yr.yrLayAll` reaches only below `ι(B_Γ)`).

* `zbPolyG_of_SC` (reduction to strongly critical bases), `zbRS`, `zbTw_sup` (`sup_n a_{n+1} = B_Γ`);
* `zbBG_top` (**`D(y) = Θ_y(B_Γ)` with the atoms of `zbU`**), `zbBG_poly` (**terms for every code below `B_Γ`**),
  `zbBG_cl` (`B_Γ` is a code over every `Z`), `zbBG_topE`;
* `zbBG_UV` (**UPPER ∧ LOWER ∧ CapV at every range restart below `ι(B_Γ·ω)`, UNCONDITIONAL**), `zbBG_loc`
  (`Λ⁺ = ι(B_Γ·ω)`, `P(B_Γ·ω) < L(0)`).

No new axiom.  New definition: `zbRS`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Tf
  Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Gs
  Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Gd Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gf

/-- **Reduction to strongly critical bases below `Ω₁`.** -/
theorem zbPolyG_of_SC (A : ZbAS) {g E : Ordinal.{0}} (X : GdSys g)
    (h : ∀ Z, SC Z → Z < Om 1 → g < Z → ∀ c, GxCl Z (A.At Z) c → c < E → ∃ s : X.Tm, ∀ y, SC y → y < Om 1 →
      Z ≤ y → X.CB s y ∧ X.val s y = gxTh y (A.At y) c) : ZbPolyG A X E := by
  intro Z c hg hc hcE
  by_cases hex : ∃ y, SC y ∧ y < Om 1 ∧ Z ≤ y
  · have hmem : sInf {y | SC y ∧ y < Om 1 ∧ Z ≤ y} ∈ {y | SC y ∧ y < Om 1 ∧ Z ≤ y} := csInf_mem hex
    obtain ⟨h1, h2, h3⟩ := hmem
    obtain ⟨s, hs⟩ := h _ h1 h2 (hg.trans_le h3) c (A.cl_mono h3 hc) hcE
    exact ⟨s, fun y hy hy1 hZy => hs y hy hy1 (csInf_le' ⟨hy, hy1, hZy⟩)⟩
  · push Not at hex
    exact ⟨X.cst 0, fun y hy hy1 hZy => absurd hZy (not_le.2 (hex y hy hy1))⟩

/-- The reading system of the tower layer `n`. -/
noncomputable abbrev zbRS (n : ℕ) : YrRS :=
  yrRSN (yrTw (n + 1)) (yrTw_E (n + 1)) ((yrTw_ge n).trans_lt (yrTw_lt_succ n)) (yrTw_lt_BG (n + 1))

theorem zbRS_K (n : ℕ) : (zbRS n).K = yrKN (yrTw (n + 1)) (yrTw_lt_BG (n + 1)) := rfl

theorem zbTwL_eq (n : ℕ) :
    ywTwL n = (zbRS n).gqL (yrTw n) (gfE_lt_G0.trans_le (yrTw_ge n)).le (yrTw_lt_succ n) := rfl

/-- **The reading statement of the tower layer `n`** (`Yr.YrRS.gqL_codes`). -/
theorem zbTw_codes (S : InaccSeq.{0}) (n : ℕ) :
    (zbRS n).GqLC (yrTw n) (gfE_lt_G0.trans_le (yrTw_ge n)).le (yrTw_lt_succ n) :=
  (zbRS n).gqL_codes S (yrTw n) _ _

/-- `sup_n a_{n+1} = B_Γ`. -/
theorem zbTw_sup : (⨆ n : ℕ, gcG (yrTw n)) = tfBG := by
  refine le_antisymm (Ordinal.iSup_le fun n => (yrTw_lt_BG (n + 1)).le) (le_of_forall_lt fun B hB => ?_)
  obtain ⟨n, hn⟩ := yrTw_cof B hB
  exact hn.trans_le ((yrTw_lt_succ n).le.trans (Ordinal.le_iSup (fun n => gcG (yrTw n)) n))

/-- **The tower layer `n` reads `Θ_y(Γ_{Ω₁+1+a_n})` with the atoms of `zbU`.** -/
theorem zbTw_top (S : InaccSeq.{0}) (n : ℕ) {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) :
    (ywTwL n).K.E y = gxTh y (zbU.At y) (gcG (yrTw n)) := by
  have hg : (zbRS n).K.gt (yrTw n) < y := by
    show yrG (yrTw n) < y; rw [yrTw_g]; exact hy.1
  rw [zbTwL_eq, (zbTw_codes S n).1 y hy hy1 hg, zbRS_K]
  exact zb_th_yr (yrTw_lt_BG (n + 1)) hy hy1 (gcG_le (yrTw_lt_succ n).le)

/-- **`D(y) = Θ_y(B_Γ)` with the atoms of `zbU`** at every strongly critical `y < Ω₁`. -/
theorem zbBG_top (S : InaccSeq.{0}) {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) :
    ywBGB.K.E y = gxTh y (zbU.At y) tfBG := by
  have hyE := gg_SC_eps hy
  have hy1' : y < Om1 := by rw [Br.Om1_eq]; exact hy1
  rw [← zbTw_sup, gxTh_iSup, ywBGB_E]
  have e : ∀ n : ℕ, gxTh y (zbU.At y) (gcG (yrTw n)) = ywS (n + 1) y := fun n => by
    rw [← zbTw_top S n hy hy1, ywTwL_E n hyE hy1']
  simp_rw [e]
  refine le_antisymm (le_of_forall_lt fun v hv => ?_) (Ordinal.iSup_le fun n => (ywS_lt_D hyE hy1' (n + 1)).1.le)
  obtain ⟨n, hn⟩ := ywS_cof hyE hy1' v hv
  exact (hn.trans (ywS_lt_succ hyE hy1' n)).trans_le (Ordinal.le_iSup (fun n => ywS (n + 1) y) n)

/-- **Terms for every code below `B_Γ`** (atoms of `zbU`) in the layer of `B_Γ`. -/
theorem zbBG_poly (S : InaccSeq.{0}) : ZbPolyG zbU ywBGB.K.sys tfBG := by
  refine zbPolyG_of_SC zbU _ fun Z hZ hZ1 _ c hc hcB => ?_
  obtain ⟨n, hn⟩ := yrTw_cof c hcB
  have hcn : c < gcG (yrTw n) := hn.trans (yrTw_lt_succ n)
  have hZ1' : Z ≤ Om1 := by rw [Br.Om1_eq]; exact hZ1.le
  have hcK : GxCl Z ((yrKN (yrTw (n + 1)) (yrTw_lt_BG (n + 1))).At Z) c :=
    (zb_cl_yr_iff (yrTw_lt_BG (n + 1)) hZ hZ1' (hcn.trans (yrTw_lt_succ (n + 1)))).2 hc
  have hg0 : (ywTwL n).g < Z := by rw [ywTwL_g]; exact hZ.1
  obtain ⟨t, ht⟩ := (zbTw_codes S n).2 Z c (by rw [← zbTwL_eq]; exact hg0) hcK hcn
  refine ⟨⟨⟨n⟩, t⟩, fun y hy hy1 hZy => ⟨⟨hZ.1.trans_le hZy, (ht y hy hy1 hZy).1⟩, ?_⟩⟩
  have e2 := (ht y hy hy1 hZy).2
  rw [zbRS_K, zb_th_yr (yrTw_lt_BG (n + 1)) hy hy1 (hcn.trans (yrTw_lt_succ (n + 1))).le] at e2
  exact e2

/-- **`B_Γ = F_1(Ω₁+1)` is an atom of `zbU` over every `Z > 0`.** -/
theorem zbBG_atom {Z : Ordinal.{0}} (hZ : 0 < Z) : tfBG ∈ zbU.At Z := by
  refine Or.inl ⟨tfBG_SC, by rw [← Br.Om1_eq]; exact tfBG_gt, tl_BG_lt_X, ?_⟩
  rw [tl_BG_eq]
  exact TlCl.atom (TlCl.one hZ) (TlCl.add TlCl.om (TlCl.one hZ)) (by rw [← tl_BG_eq]; exact tfBG_gt)

theorem zbBG_cl {Z : Ordinal.{0}} (hZ : SC Z) : GxCl Z (zbU.At Z) tfBG := GxCl.atom (zbBG_atom hZ.1)

theorem zbBG_topE : ∀ x, InE x → x < Om1 → ywBGB.g < x → eN x < ywBGB.K.E x := by
  intro x hx hx1 _
  rw [ywBGB_E]
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  have h1 := gmq_eN_lt hx hx1 h0T (hx.pos.trans hx1)
  rw [← ywS_zero] at h1
  exact h1.trans (ywS_lt_D hx hx1 0).1

theorem zbBG_g (S : InaccSeq.{0}) : ywBGB.g < Td.tdK S := by rw [ywBGB_g]; exact Td.tdK_SC.1

/-- **WHERE THE FRONTIER OF THE CODE `B_Γ` LIES**: `Λ⁺ = ι(B_Γ·ω)`, `ρ` of it `= P(B_Γ·ω) < L(0)`. -/
theorem zbBG_loc (S : InaccSeq.{0}) :
    xtB1 (zbX ywBGB S (zbBG_g S)) = iota S (tfBG * ω) ∧
    upsilon (xtB1 (zbX ywBGB S (zbBG_g S))) = Pv S (tfBG * ω) ∧ Pv S (tfBG * ω) < Nc.ncL S 0 := by
  have h := zbLoc zbU ywBGB S (zbBG_g S) tfBG tl_BG_lt_X.le (fun y hy hy1 _ => zbBG_top S hy hy1)
    (zbBG_poly S) (fun Z hZ _ => zbBG_cl hZ) zbBG_topE (by rw [← Br.Om1_eq]; exact tfBG_gt.le)
  rwa [Low.opow_eq_self_of_SC tfBG_SC] at h

/-- **UPPER ∧ LOWER ∧ CapV AT EVERY RANGE RESTART BELOW `ι(B_Γ·ω)`** (UNCONDITIONAL). -/
theorem zbBG_UV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (tfBG * ω)) :
    CdUpper S l ∧ CdLower S l ∧ CdCapV S l := by
  have hl' : l < iota S (ω ^ tfBG * ω) := by rw [Low.opow_eq_self_of_SC tfBG_SC]; exact hl
  exact zbUV zbU ywBGB S (zbBG_g S) tfBG tl_BG_lt_X.le (fun y hy hy1 _ => zbBG_top S hy hy1)
    (zbBG_poly S) (fun Z hZ _ => zbBG_cl hZ) zbBG_topE (by rw [← Br.Om1_eq]; exact tfBG_gt.le) hr hl'

end Googology.Trans.PoR.InaccPsi.R2.Zb

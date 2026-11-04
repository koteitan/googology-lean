import Googology.Trans.PoR.InaccPsi.R2.ZbCnt
import Googology.Trans.PoR.InaccPsi.R2.YwLad

/-!
# ZbLad: THE LADDER STEP READS `cQs c` WITH ANY ATOM SYSTEM — THE CODES `B_Γ + 1 + n`

For a gated layer `B` whose top reads a code `c ≥ Ω₁` (a code over every strongly critical base above the gate) with
the atoms of `A : Zb.ZbAS` (`ZbTh A`), with terms for every code below `c`, the ladder layer `Yw.ywLadB B e H`
(`e(x) ≤ E_K(x)` allowed, `Yw.YwLH`) reads `cQs c` (the least strongly critical ordinal above `c`) and has terms for
every code below it (`zbLad_top`, `zbLad_poly`; the proofs of `Gs.gsmLim_top`, `Gs.gsmLim_poly` with `Zb.zbTop_th`,
`Zb.zbPoly`).

Instance: the layers `zbBGn n` of the codes `B_Γ + 1 + n` (`zbBGn 0 = Yw.ywBG1B`, top `Γ_{x+1+D(x)+n}` written
`ϑˣ(Ω₁·Ω₁ + D(x) + n)`, `D(x) = ϑˣ(Ω₁·Ω₁ + Ω₁)`), reading `Γ_{B_Γ+1+n} = Γ_{Ω₁+1+(B_Γ+(n+1))}` with the atoms of
`Zb.zbU`; so UPPER ∧ LOWER ∧ CapV at every range restart below `ι(Γ_{B_Γ+1+n}·ω)` for every `n`.

* `zbLad_top`, `zbLad_poly`; `zbBGnH`, `zbBGn` (**THE LAYERS OF THE CODES `B_Γ + 1 + n`**), `zbBGn_g`, `zbBGn_E`;
* `zbT`, `zbT_atom`, `zbT_succ`, `zbBGn_codes` (**the reading statement of every `zbBGn n`**);
* `zbBGn_UV` (**UPPER ∧ LOWER ∧ CapV below `ι(Γ_{Ω₁+1+(B_Γ+(n+1))}·ω)`, every `n`, UNCONDITIONAL**), `zbBGn_loc`.

No new axiom.  New definitions: `zbBGnH` (a proof), `zbBGn`, `zbT`.
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
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Lp

section Lad

variable {A : ZbAS} {B : GdB} {c : Ordinal.{0}} (hc : ∀ Z, SC Z → B.g < Z → GxCl Z (A.At Z) c) (hcO : Om 1 ≤ c)
  (hKE : ∀ y, SC y → y < Om 1 → B.g < y → B.K.E y = gxTh y (A.At y) c) {e : Ordinal.{0} → Ordinal.{0}}
  (H : YwLH B e)
include hc hKE H

/-- **The ladder top reads the code `cQs c`**: `ϑʸ(Ω₁·Ω₁ + e(y)) = Θ_y(cQs c)` above the gate. -/
theorem zbLad_top {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) (hg : B.g < y) :
    (ywLadB B e H).K.E y = gxTh y (A.At y) (cQs c) := by
  have hyE := gg_SC_eps hy
  have hy1' := lp_y1 hy1
  rw [ywLadB_E, cQs, gxTh_iSup]
  have e1 : gq (e y) y = ⨆ n : ℕ, gdP B n y := by
    refine le_antisymm (le_of_forall_lt fun v hv => ?_) (Ordinal.iSup_le fun n => (ywL_gP_lt H hyE hy1' hg n).le)
    obtain ⟨n, hn⟩ := ywL_lt_iff H hyE hy1' hg v hv
    exact hn.trans_le (Ordinal.le_iSup (fun n => gdP B n y) n)
  rw [e1]
  exact iSup_congr fun n => zbTop_th hc hKE n y hy hy1 hg

include hcO in
/-- **The ladder layer has terms for every code below `cQs c`.** -/
theorem zbLad_poly (hth : ZbTh A) (hKP : ZbPolyG A B.K.sys c) : ZbPolyG A (ywLadB B e H).K.sys (cQs c) := by
  intro Z d hg hd hdE
  obtain ⟨n, hn⟩ := cQs_lt hdE
  obtain ⟨s, hs⟩ := zbPoly hc hcO hKE hth hKP n Z d hg hd hn
  exact ⟨s, fun y hy hy1 hZy => ⟨(hs y hy hy1 hZy).1.1, (hs y hy hy1 hZy).2⟩⟩

end Lad

/-! ## The layers of the codes `B_Γ + 1 + n` -/

section BGn

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem zbD_n_T (n : ℕ) : ywV 1 0 x + (n : Ordinal.{0}) ∈ Tset x ∧ ywV 1 0 x + (n : Ordinal.{0}) < ywX x := by
  obtain ⟨-, hDT, -⟩ := ywD_closed hx hx1
  have hnx : (n : Ordinal.{0}) < x := (natCast_lt_omega0 n).trans (omega0_lt_inE hx)
  obtain ⟨-, hxX, -, hXE⟩ := ywX_facts hx hx1
  exact ⟨vzT_add hx hx1 hDT (mem_T_of_le hx hx1 hnx.le),
    (inE_indec hXE).add_lt (ywD_lt_X hx hx1) (hnx.trans hxX)⟩

theorem zbD_n_lt (n : ℕ) : ywV 1 0 x + (n : Ordinal.{0}) < Om1 :=
  (zbD_n_T hx hx1 n).2.trans (ywX_facts hx hx1).2.2.1

theorem zbgq_lt_X (n : ℕ) : gq (ywV 1 0 x + (n : Ordinal.{0})) x < ywX x := by
  rw [← ywV_zero]
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  obtain ⟨-, hxX, hX1, -⟩ := ywX_facts hx hx1
  exact ywV_lt_X hx hx1 h0T (hx.pos.trans hx1) (zbD_n_T hx hx1 n).1 (zbD_n_lt hx hx1 n) (hx.pos.trans hxX)
    (zbD_n_T hx hx1 n).2

end BGn

/-- **The ladder hypothesis over the layer of `B_Γ + 1 + n`**, `e(x) = D(x) + (n + 1)`. -/
theorem zbBGnH (n : ℕ) (L : GdB) (hE : ∀ x, L.K.E x = gq (ywV 1 0 x + (n : Ordinal.{0})) x) :
    YwLH L (fun x => ywV 1 0 x + ((n + 1 : ℕ) : Ordinal.{0})) := by
  refine ⟨fun x hx hx1 _ => ⟨(zbD_n_T hx hx1 (n + 1)).1, zbD_n_lt hx hx1 (n + 1)⟩, fun x hx hx1 _ => ?_,
    fun x hx hx1 _ j hjT hj => ?_, fun x hx hx1 _ => ?_, fun x hx hx1 _ => zbgq_lt_X hx hx1 (n + 1),
    fun σ ρ hB _ => ?_⟩
  · rw [hE, Nat.cast_succ, ← add_assoc]
    exact Order.add_one_le_of_lt (gmq_gt hx hx1 (zbD_n_T hx hx1 n).1 (zbD_n_lt hx hx1 n))
  · rw [hE]
    rw [Nat.cast_succ, ← add_assoc] at hj
    exact gmq_mono hx hx1 (zbD_n_T hx hx1 n).1 (zbD_n_lt hx hx1 n) (Order.lt_add_one_iff.1 hj)
  · rw [hE]
    have h := gmq_lt hx hx1 (zbD_n_T hx hx1 (n + 1)).1 (zbD_n_lt hx hx1 (n + 1))
      (show ywV 1 0 x + (n : Ordinal.{0}) < ywV 1 0 x + ((n + 1 : ℕ) : Ordinal.{0}) from by
        rw [Nat.cast_succ, ← add_assoc]; exact lt_add_one _)
    exact h
  · have h1σ : (1 : Ordinal.{0}) < σ := lu_one_lt_E hB.1
    have h0σ : (0 : Ordinal.{0}) < σ := hB.1.pos
    have hnσ : ((n + 1 : ℕ) : Ordinal.{0}) < σ := (natCast_lt_omega0 _).trans (omega0_lt_inE hB.1)
    have h1 := ywV_pi hB (mem_TB_of_lt hB h1σ) ((lu_one_lt_E hB.2.1).trans hB.2.2.2) (mem_TB_of_lt hB h0σ)
      (hB.2.1.pos.trans hB.2.2.2)
    rw [pi_lt hB h1σ, pi_lt hB h0σ] at h1
    obtain ⟨h2, h3⟩ := pi_add hB h1.1 (mem_TB_of_lt hB hnσ)
    exact ⟨h2, by rw [h3, h1.2, pi_lt hB hnσ]⟩

/-- **THE LAYERS OF THE CODES `B_Γ + 1 + n`**: gate `0`, top `ϑˣ(Ω₁·Ω₁ + D(x) + n)`. -/
noncomputable def zbBGn : (n : ℕ) → {L : GdB // L.g = 0 ∧ ∀ x, L.K.E x = gq (ywV 1 0 x + (n : Ordinal.{0})) x}
  | 0 => ⟨ywBG1B, ywBG1B_g, fun x => by rw [ywBG1B_E, Nat.cast_zero, add_zero]⟩
  | n + 1 => ⟨ywLadB (zbBGn n).1 _ (zbBGnH n (zbBGn n).1 (zbBGn n).2.2), (zbBGn n).2.1, fun _ => rfl⟩

theorem zbBGn_g (n : ℕ) : (zbBGn n).1.g = 0 := (zbBGn n).2.1

theorem zbBGn_E (n : ℕ) (x : Ordinal.{0}) : (zbBGn n).1.K.E x = gq (ywV 1 0 x + (n : Ordinal.{0})) x :=
  (zbBGn n).2.2 x

theorem zbBGn_succ (n : ℕ) :
    (zbBGn (n + 1)).1 = ywLadB (zbBGn n).1 _ (zbBGnH n (zbBGn n).1 (zbBGn n).2.2) := rfl

theorem zbBGn_zero : (zbBGn 0).1 = ywLadB ywBGB (fun x => ywV 1 0 x) ywBG1H := rfl

/-- **The top code of the layer `n`**: `Γ_{Ω₁+1+(B_Γ+(n+1))} = Γ_{B_Γ+1+n}`. -/
noncomputable def zbT (n : ℕ) : Ordinal.{0} := gcG (tfBG + ((n + 1 : ℕ) : Ordinal.{0}))

theorem zb_gcG_BG : gcG tfBG = tfBG := by
  rw [tf_gcG, add_assoc]
  have h : Om1 + (1 + tfBG) = tfBG := by
    rw [one_add_of_omega0_le ((omega0_lt_inE (Low.opow_eq_self_of_SC tfBG_SC)).le)]
    exact tfBG_SC.isPrincipal.add_eq_right tfBG_gt
  rw [h, tfBG_fix]

theorem zbT_zero : cQs tfBG = zbT 0 := by
  conv_lhs => rw [← zb_gcG_BG]
  rw [gc_cQs]; unfold zbT; norm_num

theorem zbT_SC (n : ℕ) : SC (zbT n) := gcG_SC _

theorem zbT_succ (n : ℕ) : cQs (zbT n) = zbT (n + 1) := by
  unfold zbT; rw [gc_cQs, Nat.cast_succ (n + 1), ← add_assoc]

theorem zbT_lt_X (n : ℕ) : zbT n < tlX := by
  unfold zbT
  rw [tf_gcG]
  have h1 : tfBG + ((n + 1 : ℕ) : Ordinal.{0}) < tlX :=
    tlX_SC.isPrincipal tl_BG_lt_X ((natCast_lt_omega0 _).trans (omega0_lt_inE (Low.opow_eq_self_of_SC tlX_SC)))
  have h2 : Om1 + 1 + (tfBG + ((n + 1 : ℕ) : Ordinal.{0})) < tlX :=
    tlX_SC.isPrincipal (tlX_SC.add_one_lt tlX_gt) h1
  calc gamma (Om1 + 1 + (tfBG + ((n + 1 : ℕ) : Ordinal.{0}))) < gamma tlX := gamma_lt_gamma.2 h2
    _ = tlX := tl_gamma_X

/-- **`Γ_{B_Γ+1+n}` is an atom of `zbU` over every `Z > 0`.** -/
theorem zbT_atom (n : ℕ) {Z : Ordinal.{0}} (hZ : 0 < Z) : zbT n ∈ zbU.At Z := by
  have hnat : ∀ k : ℕ, TlCl Z (k : Ordinal.{0}) := fun k => by
    have := TlCl.mul_nat hZ (TlCl.one hZ) k; rwa [one_mul] at this
  have hBG : TlCl Z tfBG := (zbBG_atom hZ).elim (fun h => h.2.2.2) fun h => by
    obtain ⟨c, hc, -, e⟩ := h
    exact absurd (e ▸ yr_gcG_lt_BG hc) (lt_irrefl _)
  have harg : TlCl Z (Om1 + 1 + (tfBG + ((n + 1 : ℕ) : Ordinal.{0}))) :=
    TlCl.add (TlCl.add TlCl.om (TlCl.one hZ)) (TlCl.add hBG (hnat _))
  have hO : Om1 < Om1 + 1 + (tfBG + ((n + 1 : ℕ) : Ordinal.{0})) :=
    (lt_add_one _).trans_le le_self_add
  refine Or.inl ⟨gcG_SC _, gcG_Om1_lt _, zbT_lt_X n, ?_⟩
  unfold zbT; rw [tf_gcG]
  exact TlCl.gam hZ harg hO

theorem zbT_cl (n : ℕ) {Z : Ordinal.{0}} (hZ : SC Z) : GxCl Z (zbU.At Z) (zbT n) := GxCl.atom (zbT_atom n hZ.1)

/-- **THE READING STATEMENT OF THE LAYER `n`**: its top reads `Γ_{B_Γ+1+n}` with the atoms of `zbU`, and it has terms
for every code below it. -/
theorem zbBGn_codes (S : InaccSeq.{0}) : ∀ n : ℕ,
    (∀ y, SC y → y < Om 1 → (zbBGn n).1.g < y → (zbBGn n).1.K.E y = gxTh y (zbU.At y) (zbT n)) ∧
      ZbPolyG zbU (zbBGn n).1.K.sys (zbT n)
  | 0 => by
    rw [zbBGn_zero, ← zbT_zero]
    have hc : ∀ Z, SC Z → ywBGB.g < Z → GxCl Z (zbU.At Z) tfBG := fun Z hZ _ => zbBG_cl hZ
    have hKE : ∀ y, SC y → y < Om 1 → ywBGB.g < y → ywBGB.K.E y = gxTh y (zbU.At y) tfBG :=
      fun y hy hy1 _ => zbBG_top S hy hy1
    exact ⟨fun y hy hy1 hg => zbLad_top hc hKE ywBG1H hy hy1 hg,
      zbLad_poly hc (by rw [← Br.Om1_eq]; exact tfBG_gt.le) hKE ywBG1H zbU_th (zbBG_poly S)⟩
  | n + 1 => by
    obtain ⟨ihE, ihP⟩ := zbBGn_codes S n
    rw [zbBGn_succ, ← zbT_succ]
    have hc : ∀ Z, SC Z → (zbBGn n).1.g < Z → GxCl Z (zbU.At Z) (zbT n) := fun Z hZ _ => zbT_cl n hZ
    exact ⟨fun y hy hy1 hg => zbLad_top hc ihE _ hy hy1 hg,
      zbLad_poly hc (gcG_Om1_lt _).le ihE _ zbU_th ihP⟩

theorem zbBGn_gK (S : InaccSeq.{0}) (n : ℕ) : (zbBGn n).1.g < Td.tdK S := by
  rw [zbBGn_g]; exact Td.tdK_SC.1

theorem zbBGn_topE (n : ℕ) : ∀ x, InE x → x < Om1 → (zbBGn n).1.g < x → eN x < (zbBGn n).1.K.E x := by
  intro x hx hx1 _
  rw [zbBGn_E]
  exact gmq_eN_lt hx hx1 (zbD_n_T hx hx1 n).1 (zbD_n_lt hx hx1 n)

/-- **WHERE THE FRONTIER OF THE CODE `B_Γ + 1 + n` LIES**: `Λ⁺ = ι(Γ_{B_Γ+1+n}·ω)`, `P(Γ_{B_Γ+1+n}·ω) < L(0)`. -/
theorem zbBGn_loc (S : InaccSeq.{0}) (n : ℕ) :
    xtB1 (zbX (zbBGn n).1 S (zbBGn_gK S n)) = iota S (zbT n * ω) ∧
    upsilon (xtB1 (zbX (zbBGn n).1 S (zbBGn_gK S n))) = Pv S (zbT n * ω) ∧ Pv S (zbT n * ω) < Nc.ncL S 0 := by
  have h := zbLoc zbU (zbBGn n).1 S (zbBGn_gK S n) (zbT n) (zbT_lt_X n).le (zbBGn_codes S n).1
    (zbBGn_codes S n).2 (fun Z hZ _ => zbT_cl n hZ) (zbBGn_topE n) (gcG_Om1_lt _).le
  rwa [Low.opow_eq_self_of_SC (zbT_SC n)] at h

/-- **UPPER ∧ LOWER ∧ CapV AT EVERY RANGE RESTART BELOW `ι(Γ_{B_Γ+1+n}·ω)`, EVERY `n`** (UNCONDITIONAL). -/
theorem zbBGn_UV (S : InaccSeq.{0}) (n : ℕ) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (zbT n * ω)) :
    CdUpper S l ∧ CdLower S l ∧ CdCapV S l := by
  have hl' : l < iota S (ω ^ zbT n * ω) := by rw [Low.opow_eq_self_of_SC (zbT_SC n)]; exact hl
  exact zbUV zbU (zbBGn n).1 S (zbBGn_gK S n) (zbT n) (zbT_lt_X n).le (zbBGn_codes S n).1
    (zbBGn_codes S n).2 (fun Z hZ _ => zbT_cl n hZ) (zbBGn_topE n) (gcG_Om1_lt _).le hr hl'

end Googology.Trans.PoR.InaccPsi.R2.Zb

import Googology.Trans.PoR.InaccPsi.R2.CpRoad
import Googology.Trans.PoR.InaccPsi.R2.XtRel

/-!
# ENUM-REACH below the bound of any offset specification, and the road with the rest asked only outside

`r(λ) = k_λ(Θ_λ(m_λ))` (`cdR`), `δ_λ = υ_{λ+ω+1}`, UPPER = `CdUpper`, LOWER = `CdLower`.  `R2.CpUp`, `R2.CpFix` and
`R2.CpRoad` prove ENUM-REACH and the caps below `cpB1` from the block structure of `VzOrec` there.  Here the same
for **any general offset specification** `SP : OffSpecGen O B` (namespace `Xt`):

* `xtClosed`, `xtk_eq` (`k_λ(x) = δ_λ + x` for `x < δ_λ`, `λ < B`);
* `xtUpper_iff`, `xtLower_iff`, `xtExact_iff` (**ENUM-REACH below `B` as an equation of offsets**: UPPER iff
  `O(λ) ≤ Θ_λ(m_λ)`, LOWER iff `Θ_λ(m_λ) ≤ O(λ)`);
* `xtEnum_nonfix` (**both halves at a restart `λ < B` with `ω² < λ < υ_λ`, a name, and `O(λ) = -1 + e(λ)`**),
  `xtCapV_nonfix`, `xtCapAt_nonfix` (the caps there);
* `xtFix_iff` (at a fixed point `F = υ_F < B` with `O(F) = F`: UPPER iff `F ≤ Θ_F(m_F)`, LOWER iff `Θ_F(m_F) ≤ F`);
* `XtOut B λ` (`B ≤ λ` or `υ_λ = λ`) and the road (`xtUPPER`, `xtLOWER`, `xtCapV`, `xtCAP0`, `xtCAP1`, `xtLow`,
  `xtRoad`, `xtRoad_cap`, `xtUPPER3`, `xtLOWER3`, `xtRoad3`): the hypotheses of `R2.CdNu`'s road asked only at the
  restarts outside, when `O(μ) = -1 + e(μ)` off the fixed points below `B` (`XtNonfix O B`, true for every term
  system by `xtNonfix`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Xt

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp

variable {S : InaccSeq.{0}} {O : Ordinal.{0} → Ordinal.{0}} {B : Ordinal.{0}}

theorem xtB_lt_add (SP : OffSpecGen O B) {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < B) :
    l + ω + 1 + 1 < B := by
  have h1 : l + ω * ω ≤ B := next_mult (ri_iff.1 hl).2 SP.mult hlB
  refine lt_of_lt_of_le ?_ h1
  rw [add_assoc, add_assoc]
  refine (add_lt_add_iff_left l).2 ?_
  have h2 : (1 + 1 : Ordinal.{0}) < ω := by
    rw [one_add_one_eq_two]; exact_mod_cast natCast_lt_omega0 2
  have h3 : ω + (1 + 1) < ω + ω := (add_lt_add_iff_left ω).2 h2
  calc ω + (1 + 1) < ω + ω := h3
    _ = ω * 2 := (Ordinal.mul_two ω).symm
    _ < ω * ω := mul_lt_mul_of_pos_left (by exact_mod_cast natCast_lt_omega0 2) omega0_pos

/-- **`δ_λ + x` is closed relative to `λ`** for `x < δ_λ`, `λ < B`. -/
theorem xtClosed (SP : OffSpecGen O B) {l x : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < B)
    (hx : x < cdDelta l) : cdClosed l (cdDelta l + x) := by
  have R := (rstGen SP hl hlB).1
  refine ⟨le_self_add, fun a hρa hax g hg => ?_⟩
  rcases le_or_gt a (cdDelta l) with haδ | hδa
  · exact (not_lt.1 fun h => R.capδ a hρa haδ g h hg).trans le_self_add
  · have hnI : ¬ Indec a := decomp_mid hx hδa hax
    have hnU : ¬ UpsPt a := fun h => hnI (indec_of_upsPt h)
    have hacp : a < upsilon B :=
      (hax.trans_lt (cp_delta_add_lt hx)).trans (upsilon_normal.strictMono (xtB_lt_add SP hl hlB))
    have hR := ((blk_genGen SP).2.2 a hacp hnU g).1 hg
    exact ((Lh.lhDecomp hnI).2 g hR).trans hax

theorem xtk_eq (SP : OffSpecGen O B) {l x : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < B)
    (hx : x < cdDelta l) : cdk l x = cdDelta l + x :=
  cdk_interval (fun _ hy => Or.inl (xtClosed SP hl hlB (hy.trans_lt hx))) x le_rfl

/-- **UPPER below `B`**: UPPER at `λ` iff `O(λ) ≤ Θ_λ(m_λ)`. -/
theorem xtUpper_iff (SP : OffSpecGen O B) {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < B) :
    CdUpper S l ↔ O l ≤ cdTheta S l (cdCode S l) := by
  rw [cdUpper_iff_ge (reach_allGen SP hl hlB)]
  have e : upsilon (l + ω + 1) + O l = cdk l (O l) := (xtk_eq SP hl hlB (SP.le l hl hlB)).symm
  rw [e]
  exact (cdk_strictMono l).le_iff_le

/-- **LOWER below `B`**: LOWER at `λ` iff `Θ_λ(m_λ) ≤ O(λ)`. -/
theorem xtLower_iff (SP : OffSpecGen O B) {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < B) :
    CdLower S l ↔ cdTheta S l (cdCode S l) ≤ O l := by
  rw [cdLower_iff_le (reach_allGen SP hl hlB)]
  have e : upsilon (l + ω + 1) + O l = cdk l (O l) := (xtk_eq SP hl hlB (SP.le l hl hlB)).symm
  rw [e]
  exact (cdk_strictMono l).le_iff_le

/-- **ENUM-REACH below `B`**: both halves at `λ` iff `Θ_λ(m_λ) = O(λ)`. -/
theorem xtExact_iff (SP : OffSpecGen O B) {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < B) :
    (CdUpper S l ∧ CdLower S l) ↔ cdTheta S l (cdCode S l) = O l := by
  rw [xtUpper_iff SP hl hlB, xtLower_iff SP hl hlB]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

/-- **ENUM-REACH, both halves, at a restart below `B` that is not a fixed point of `υ`** (with
`O(λ) = -1 + e(λ)`). -/
theorem xtEnum_nonfix (SP : OffSpecGen O B) {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hww : ω * ω < l)
    (hfix : l < upsilon l) (hlB : l < B) (hn : upsilon l < Pv S η1) (hO : O l = cdOff (cdExp l)) :
    cdCode S l = cdOff (cdExp l) ∧ cdTheta S l (cdCode S l) = cdOff (cdExp l) ∧
      cdR S l = cdDelta l + cdOff (cdExp l) ∧ IsReach R2C (upsilon l) (cdR S l) ∧
      CdUpper S l ∧ CdLower S l := by
  have hm : cdCode S l = cdOff (cdExp l) := cpCode_exp hl hww hfix hn
  have hml : cdOff (cdExp l) ≤ l := (cdOff_le _).trans (cpExp_le hl.1)
  have hθ : cdTheta S l (cdCode S l) = cdOff (cdExp l) := by
    rw [hm]; exact cdTheta_small S (hml.trans upsilon_normal.strictMono.le_apply)
  have hmδ : cdOff (cdExp l) < cdDelta l :=
    (hml.trans upsilon_normal.strictMono.le_apply).trans_lt (cdRho_lt_delta l)
  have hR : cdR S l = cdDelta l + cdOff (cdExp l) := by
    show cdk l (cdTheta S l (cdCode S l)) = _
    rw [hθ]; exact xtk_eq SP hl hlB hmδ
  have hex : CdUpper S l ∧ CdLower S l := (xtExact_iff SP hl hlB).2 (hθ.trans hO.symm)
  exact ⟨hm, hθ, hR, cdExact_iff.1 hex, hex.1, hex.2⟩

/-- **The cap of the value** at a restart below `B` that is not a fixed point of `υ`. -/
theorem xtCapV_nonfix (SP : OffSpecGen O B) {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hww : ω * ω < l)
    (hfix : l < upsilon l) (hlB : l < B) (hn : upsilon l < Pv S η1) (hO : O l = cdOff (cdExp l)) :
    CdCapV S l := by
  obtain ⟨-, -, hR, -, -, -⟩ := xtEnum_nonfix SP hl hww hfix hlB hn hO
  obtain ⟨l0, z, hl0, hz0, hzρ, -, rfl⟩ := cpDecomp hl hww hfix
  have hn0 : upsilon l0 < Pv S η1 :=
    (upsilon_normal.strictMono (lt_add_of_pos_right l0 hz0)).trans hn
  obtain ⟨heta, hg, -⟩ := cpEta_add (S := S) hl0.1 hn0 hzρ
  obtain ⟨hg', hι', -, hpv'⟩ := cdEta_pv_spec (S := S) hl.1 hn
  have hml : cdOff (cdExp (l0 + z)) ≤ l0 + z := (cdOff_le _).trans (cpExp_le hl.1)
  have hmδ : cdOff (cdExp (l0 + z)) < cdDelta (l0 + z) :=
    (hml.trans upsilon_normal.strictMono.le_apply).trans_lt (cdRho_lt_delta _)
  have hw2 : (ω + 1 + 1 : Ordinal.{0}) < Pv S (cdEta S (l0 + z)) := by
    rw [hpv']
    have hU := upsPt_upsilon (pos_iff_ne_zero.2 hl.1)
    have hp := (indec_iff.1 (indec_of_upsPt hU)).2
    have hω : ω < upsilon (l0 + z) :=
      lt_of_le_of_lt (le_mul_left _ omega0_pos) (hww.trans hfix)
    have h1 : (1 : Ordinal.{0}) < upsilon (l0 + z) := one_lt_omega0.trans hω
    exact hp (hp hω h1) h1
  have hP : Pv S (cdEta S (l0 + z) + (ω + 1 + 1)) = upsilon (l0 + z + ω + 1 + 1) := by
    calc Pv S (cdEta S (l0 + z) + (ω + 1 + 1))
        = upsilon (iota S (cdEta S (l0 + z) + (ω + 1 + 1))) := (ups_iota S _).symm
      _ = upsilon (l0 + z + ω + 1 + 1) := by rw [cpIota_add hg' hw2, hι']; simp only [add_assoc]
  have hexp : cdExp (cdEta S (l0 + z)) = cdExp (l0 + z) := by
    rw [heta, cpExp_add _ hz0.ne', cpExp_add _ hz0.ne']
  have he2 : 2 ≤ cdExp (l0 + z) := cp_two_le_exp hl.1 (ri_iff.1 hl).2
  have hle : ω + 1 + 1 ≤ ω ^ cdExp (cdEta S (l0 + z)) := by
    rw [hexp]
    refine le_trans ?_ (opow_le_opow_right omega0_pos he2)
    rw [cp_ww_eq]
    refine le_of_lt ?_
    have h2 : (1 + 1 : Ordinal.{0}) < ω := by
      rw [one_add_one_eq_two]; exact_mod_cast natCast_lt_omega0 2
    calc ω + 1 + 1 = ω + (1 + 1) := add_assoc _ _ _
      _ < ω + ω := (add_lt_add_iff_left ω).2 h2
      _ = ω * 2 := (Ordinal.mul_two ω).symm
      _ < ω * ω := mul_lt_mul_of_pos_left (by exact_mod_cast natCast_lt_omega0 2) omega0_pos
  unfold CdCapV cdCapB
  rw [hR]
  calc cdDelta (l0 + z) + cdOff (cdExp (l0 + z)) < upsilon (l0 + z + ω + 1 + 1) := cp_delta_add_lt hmδ
    _ = Pv S (cdEta S (l0 + z) + (ω + 1 + 1)) := hP.symm
    _ ≤ Pv S (cdEta S (l0 + z) + ω ^ cdExp (cdEta S (l0 + z))) := Pv_mono (add_le_add le_rfl hle)

theorem xtCapAt_nonfix (SP : OffSpecGen O B) {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hww : ω * ω < l)
    (hfix : l < upsilon l) (hlB : l < B) (hn : upsilon l < Pv S η1) (hO : O l = cdOff (cdExp l)) :
    CdCapAt S l :=
  cdCapAt_of_upper (xtEnum_nonfix SP hl hww hfix hlB hn hO).2.2.2.2.1 (xtCapV_nonfix SP hl hww hfix hlB hn hO)

/-- **ENUM-REACH at a fixed point `F < B` of `υ` with `O(F) = F`**. -/
theorem xtFix_iff (SP : OffSpecGen O B) {F : Ordinal.{0}} (hF : IsRestartIdx F) (hFB : F < B)
    (hO : O F = F) :
    (CdUpper S F ↔ F ≤ cdTheta S F (cdCode S F)) ∧ (CdLower S F ↔ cdTheta S F (cdCode S F) ≤ F) := by
  refine ⟨?_, ?_⟩
  · rw [xtUpper_iff SP hF hFB, hO]
  · rw [xtLower_iff SP hF hFB, hO]

/-- **The reduction to the code** at a fixed point `F < B` with `O(F) = F` and a name. -/
theorem xtFix_code (SP : OffSpecGen O B) {F η1 : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F)
    (hFB : F < B) (hO : O F = F) (hn : upsilon F < Pv S η1) :
    (F ≤ cdCode S F → CdUpper S F) ∧ (cdCode S F ≤ Om1 → CdLower S F) := by
  obtain ⟨hU, hL⟩ := xtFix_iff (S := S) SP hF hFB hO
  have hpv : Pv S (cdEta S F) = upsilon F := cdEta_pv hF.1 hn
  refine ⟨fun h => hU.2 ?_, fun h => hL.2 ?_⟩
  · calc F = cdTheta S F F := (cdTheta_small S hfix.ge).symm
      _ ≤ cdTheta S F (cdCode S F) := cdTheta_mono S F h
  · calc cdTheta S F (cdCode S F) ≤ cdTheta S F (Om 1) := cdTheta_mono S F (by rw [← Br.Om1_eq]; exact h)
      _ = upsilon F := cdTheta_Om1 hpv
      _ = F := hfix

/-! ## The road with the hypotheses asked only outside -/

/-- `O(μ) = -1 + e(μ)` at every restart index `ω² < μ < B` that is not a fixed point of `υ`. -/
def XtNonfix (O : Ordinal.{0} → Ordinal.{0}) (B : Ordinal.{0}) : Prop :=
  ∀ μ, IsRestartIdx μ → ω * ω < μ → μ < upsilon μ → μ < B → O μ = cdOff (cdExp μ)

/-- `λ` is **outside** `B`: `B ≤ λ` or `λ` is a fixed point of `υ`. -/
def XtOut (B l : Ordinal.{0}) : Prop := B ≤ l ∨ upsilon l = l

theorem xtOut_or (B l : Ordinal.{0}) : XtOut B l ∨ (l < B ∧ l < upsilon l) := by
  rcases le_or_gt B l with h | h
  · exact Or.inl (Or.inl h)
  · rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with h' | h'
    · exact Or.inr ⟨h, h'⟩
    · exact Or.inl (Or.inr h'.symm)

/-- UPPER and LOWER at every restart of the range below `B` that is not a fixed point of `υ`. -/
theorem xtInit (SP : OffSpecGen O B) (hN : XtNonfix O B) {l : Ordinal.{0}} (hr : CdRange S l) (hlB : l < B)
    (hfix : l < upsilon l) : CdUpper S l ∧ CdLower S l := by
  have hww := cp_ww_lt_B0.trans_le hr.2.1
  obtain ⟨-, -, -, -, hU, hL⟩ :=
    xtEnum_nonfix SP hr.1 hww hfix hlB (cp_name_L hr.2.2.1) (hN l hr.1 hww hfix hlB)
  exact ⟨hU, hL⟩

theorem xtUPPER (SP : OffSpecGen O B) (hN : XtNonfix O B)
    (hU : ∀ l, CdRange S l → XtOut B l → CdUpper S l) : CdUPPER S := fun l hr => by
  rcases xtOut_or B l with h | ⟨hlB, hfix⟩
  · exact hU l hr h
  · exact (xtInit SP hN hr hlB hfix).1

theorem xtLOWER (SP : OffSpecGen O B) (hN : XtNonfix O B)
    (hL : ∀ l, CdRange S l → XtOut B l → CdLower S l) : CdLOWER S := fun l hr => by
  rcases xtOut_or B l with h | ⟨hlB, hfix⟩
  · exact hL l hr h
  · exact (xtInit SP hN hr hlB hfix).2

theorem xtCapV (SP : OffSpecGen O B) (hN : XtNonfix O B)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut B l → CdCapV S l) :
    ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CdCapV S l := fun l hr hX => by
  rcases xtOut_or B l with h | ⟨hlB, hfix⟩
  · exact hV l hr hX h
  · have hww := cp_ww_lt_B0.trans_le hr.2.1
    exact xtCapV_nonfix SP hr.1 hww hfix hlB (cp_name_L hr.2.2.1) (hN l hr.1 hww hfix hlB)

theorem xtCAP0 (SP : OffSpecGen O B) (hN : XtNonfix O B)
    (h0 : ∀ l, IsRestartIdx l → cdB0 ≤ l → upsilon l < cdMstar S → XtOut B l → CdCapAt S l) :
    CdCAP0 S := fun l hl hB hlev => by
  rcases xtOut_or B l with h | ⟨hlB, hfix⟩
  · exact h0 l hl hB hlev h
  · have hww := cp_ww_lt_B0.trans_le hB
    exact xtCapAt_nonfix SP hl hww hfix hlB hlev (hN l hl hww hfix hlB)

theorem xtCAP1 (SP : OffSpecGen O B) (hN : XtNonfix O B)
    (h1 : ∀ l, IsRestartIdx l → cdB0 ≤ l → cdMstar S ≤ upsilon l → upsilon l < Nc.ncL S ω →
      cdCode S l < Nc.ncPp S → XtOut B l → CdCapAt S l) :
    CdCAP1 S (Nc.ncL S ω) := fun l hl hB hlev hX hc => by
  rcases xtOut_or B l with h | ⟨hlB, hfix⟩
  · exact h1 l hl hB hlev hX hc h
  · have hww := cp_ww_lt_B0.trans_le hB
    exact xtCapAt_nonfix SP hl hww hfix hlB (Lw.lw_L_eq S ω ▸ hX) (hN l hl hww hfix hlB)

/-- **NU-LOW″ from the caps outside `B`**: `L(ω) ≤ ν_C`. -/
theorem xtLow (SP : OffSpecGen O B) (hN : XtNonfix O B)
    (h0 : ∀ l, IsRestartIdx l → cdB0 ≤ l → upsilon l < cdMstar S → XtOut B l → CdCapAt S l)
    (h1 : ∀ l, IsRestartIdx l → cdB0 ≤ l → cdMstar S ≤ upsilon l → upsilon l < Nc.ncL S ω →
      cdCode S l < Nc.ncPp S → XtOut B l → CdCapAt S l) : Nc.ncL S ω ≤ nuC :=
  cdLow (xtCAP0 SP hN h0) (xtCAP1 SP hN h1)

/-- **The road with ENUM-REACH and the cap of the values asked only outside `B`.** -/
theorem xtRoad (SP : OffSpecGen O B) (hN : XtNonfix O B)
    (hU : ∀ l, CdRange S l → XtOut B l → CdUpper S l) (hL : ∀ l, CdRange S l → XtOut B l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut B l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  cdRoad (xtUPPER SP hN hU) (xtLOWER SP hN hL) (xtCapV SP hN hV) hC hEQ hrest hB2

/-- **The road with the caps asked only outside `B`**: CAP-0, CAP-1 outside, (CL), (TC), (EMB₂). -/
theorem xtRoad_cap (SP : OffSpecGen O B) (hN : XtNonfix O B)
    (h0 : ∀ l, IsRestartIdx l → cdB0 ≤ l → upsilon l < cdMstar S → XtOut B l → CdCapAt S l)
    (h1 : ∀ l, IsRestartIdx l → cdB0 ≤ l → cdMstar S ≤ upsilon l → upsilon l < Nc.ncL S ω →
      cdCode S l < Nc.ncPp S → XtOut B l → CdCapAt S l) (hC : CdCL S) (hTC : CdTC S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  cdRoad_cap (xtCAP0 SP hN h0) (xtCAP1 SP hN h1) hC hTC hB2

/-- **UPPER from UPPER at `λ ≥ B` and the notation `Θ_F(m_F) = O(F)` at the fixed points below `B`.** -/
theorem xtUPPER3 (SP : OffSpecGen O B) (hN : XtNonfix O B)
    (hU : ∀ l, CdRange S l → B ≤ l → CdUpper S l)
    (hT : ∀ l, CdRange S l → l < B → upsilon l = l → cdTheta S l (cdCode S l) = O l) : CdUPPER S :=
  fun l hr => by
  rcases le_or_gt B l with hB | hlB
  · exact hU l hr hB
  · rcases xtOut_or B l with (h | h) | ⟨-, hfix⟩
    · exact absurd h (not_le.2 hlB)
    · exact ((xtExact_iff SP hr.1 hlB).2 (hT l hr hlB h)).1
    · exact (xtInit SP hN hr hlB hfix).1

theorem xtLOWER3 (SP : OffSpecGen O B) (hN : XtNonfix O B)
    (hL : ∀ l, CdRange S l → B ≤ l → CdLower S l)
    (hT : ∀ l, CdRange S l → l < B → upsilon l = l → cdTheta S l (cdCode S l) = O l) : CdLOWER S :=
  fun l hr => by
  rcases le_or_gt B l with hB | hlB
  · exact hL l hr hB
  · rcases xtOut_or B l with (h | h) | ⟨-, hfix⟩
    · exact absurd h (not_le.2 hlB)
    · exact ((xtExact_iff SP hr.1 hlB).2 (hT l hr hlB h)).2
    · exact (xtInit SP hN hr hlB hfix).2

/-- **The road with UPPER and LOWER asked only at `λ ≥ B`** and `Θ_F(m_F) = O(F)` at the fixed points below
`B`, the cap of the values outside, (CL), EQ, TCrest, (EMB₂). -/
theorem xtRoad3 (SP : OffSpecGen O B) (hN : XtNonfix O B)
    (hU : ∀ l, CdRange S l → B ≤ l → CdUpper S l) (hL : ∀ l, CdRange S l → B ≤ l → CdLower S l)
    (hT : ∀ l, CdRange S l → l < B → upsilon l = l → cdTheta S l (cdCode S l) = O l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut B l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  cdRoad (xtUPPER3 SP hN hU hT) (xtLOWER3 SP hN hL hT) (xtCapV SP hN hV) hC hEQ hrest hB2

/-- **Every term system satisfies `XtNonfix` below its frontier** (`xtNonfix`). -/
theorem xtNonfix_sys (X : XtSys) : XtNonfix (xtOrec X) (xtLam X) :=
  fun _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans xtLam_lt_Om1)

end Googology.Trans.PoR.InaccPsi.R2.Xt

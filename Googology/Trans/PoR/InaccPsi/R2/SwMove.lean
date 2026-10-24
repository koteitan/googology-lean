import Googology.Trans.PoR.InaccPsi.R2.SwSys

/-!
# The move of the level system up to `ε_{Ω₂+ω}` under `B_n`

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `Θ' = gxTh ρ_{λ'} (ldAtR λ')`, `W^E = Ω₂^E`,
`Ω^x = Ω₁^x`, `L_k = ε_{Ω₂+1+k}`, `Θ̂ = Sw.swTh S λ`, `Θ̂' = Sw.swTh S λ'`.  The move hypothesis `IHm` (as in
`Sj.sjB_thH`): the codes `x < B` at `λ` are in `MvD`, `B_n x` is a code at `λ'`, `Θ x < c_{n+1}` and
`Θ'(B_n x) = B_n(Θ x)`.

* `swB_thH` (**THE MOVE OF THE EXPONENTS BELOW `ε_{Ω₂+ω}`**: for `E ∈ H_λ`, `E < ε_{Ω₂+ω}`, `E` a code over a
  strongly critical `B` whose codes move: `E ∈ MvD`, `B_n(Ω₂·E) = Ω₂·B_n E`, `B_n E < ε_{Ω₂+ω}`,
  `B_n E ∈ H_{λ'}`, the closure condition transfers, `B_n(Ω₁·Θ̂ E) = Ω₁·B_n(Θ̂ E)` and **`Θ̂'(B_n E) = B_n(Θ̂ E)`**;
  the leaves are fixed by `B_n`, the rest by the base-`Ω₂` normal form as in `Sj.sjB_thH`);
* `swLSB` (**`St.StLSB S n λ λ' ε_{Ω₂+ω} Θ̂`**).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj
  Googology.Trans.PoR.InaccPsi.R2.St

variable {S : InaccSeq.{0}}

section Thh

variable {n : ℕ} {l l' ηx ηx' : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hl' : IsRestartIdx l') (hX' : upsilon l' < Pv S ηx')
  {B : Ordinal.{0}} (hBSC : SC B)
  (IHm : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < B → MvD S x ∧
    GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
    gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x))

include hl hX hl' hX' hBSC IHm

/-- **THE MOVE OF THE EXPONENTS BELOW `ε_{Ω₂+ω}`.** -/
theorem swB_thH : ∀ E, E ∈ cdHull S l → E < swTop S → LeCl (Om (1 + 1)) B E →
    MvD S E ∧ MvD S (Om (1 + 1) * E) ∧ Bc.bcB S n (Om (1 + 1) * E) = Om (1 + 1) * Bc.bcB S n E ∧
      Bc.bcB S n E < swTop S ∧ Bc.bcB S n E ∈ cdHull S l' ∧
      (MvD S B → ∀ Q, SC Q → Bc.bcB S n B ≤ Q → LeCl (Om (1 + 1)) Q (Bc.bcB S n E)) ∧
      MvD S (swTh S l E) ∧ MvD S (Om 1 * swTh S l E) ∧
      Bc.bcB S n (Om 1 * swTh S l E) = Om 1 * Bc.bcB S n (swTh S l E) ∧
      swTh S l' (Bc.bcB S n E) = Bc.bcB S n (swTh S l E) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have h1ρ : (1 : Ordinal.{0}) ≤ upsilon l := (gg_one_lt_of_SC hρSC).le
  have h1ρ' : (1 : Ordinal.{0}) ≤ upsilon l' := (gg_one_lt_of_SC (leRho hl' hX').1).le
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hc1 : Bc.bcC S (n + 1) < Om 1 := hLw.trans (psi_lt Low.InR_Om_one _)
  have hD0 : MvD S (0 : Ordinal.{0}) := mvD_of_lt (Lw.lw_L_SC S ω).1
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  obtain ⟨hDtop, hBtop⟩ := swB_top (S := S) (n := n)
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  set Pc : Ordinal.{0} → Prop := fun x => GxCl (upsilon l) (ldAtR S l) x ∧ x < B with hPc
  have hPcD : ∀ x, Pc x → MvD S x := fun x hx => (IHm x hx.1 hx.2).1
  have hD0' : (0 : Ordinal.{0}) ∈ cdHull S l' := CSet.zero_mem _ _
  have hPcdec : ∀ x, Pc x → x ≠ 0 → Pc (log ω x) ∧ Pc (x - ω ^ log ω x) := fun x hx hx0 => by
    obtain ⟨hsub, hlog⟩ := gxDec hρSC hAt x hx.1
    exact ⟨⟨hlog, (log_le_self ω x).trans_lt hx.2⟩,
      ⟨hsub _ (GxCl.opow hρSC.1 hlog) (opow_log_le_self ω hx0), (Ordinal.sub_le_self _ _).trans_lt hx.2⟩⟩
  set P1 : Ordinal.{0} → Prop := fun x => x < Om 1 ∧ x < Bc.bcC S (n + 1) with hP1
  have hP1D : ∀ x, P1 x → MvD S x := fun x hx => mvD_of_lt (hx.2.trans hLw)
  have hP1dec : ∀ x, P1 x → x ≠ 0 → P1 (log ω x) ∧ P1 (x - ω ^ log ω x) := fun x hx _ =>
    ⟨⟨(log_le_self ω x).trans_lt hx.1, (log_le_self ω x).trans_lt hx.2⟩,
      ⟨(Ordinal.sub_le_self _ _).trans_lt hx.1, (Ordinal.sub_le_self _ _).trans_lt hx.2⟩⟩
  have eW : ∀ z w : Ordinal.{0}, Om (1 + 1) * (leWe z * w) = ω ^ (Om (1 + 1) + Om (1 + 1) * z) * w :=
    fun z w => by rw [← mul_assoc]; unfold leWe; rw [opow_add, gg_SC_eps ldOm2_SC]
  have eO : ∀ z w : Ordinal.{0}, Om 1 * (leOe z * w) = ω ^ (Om 1 + Om 1 * z) * w :=
    fun z w => by rw [← mul_assoc]; unfold leOe; rw [opow_add, gg_SC_eps Ph.ph_SC_Om1]
  intro E
  induction E using WellFoundedLT.induction with
  | ind E IH =>
  intro hEH hE hEB
  rcases eq_or_ne E 0 with rfl | hE0
  · refine ⟨hD0, by rw [mul_zero]; exact hD0, by rw [mul_zero, Bc.bcB_zero, mul_zero], ?_,
      by rw [Bc.bcB_zero]; exact hD0', fun _ Q hQ _ => by rw [Bc.bcB_zero]; exact LeCl.zero hQ.1, ?_, ?_, ?_, ?_⟩
    · rw [Bc.bcB_zero]; exact veblen_pos
    · rw [swTh_zero]; exact hD0
    · rw [swTh_zero, mul_zero]; exact hD0
    · rw [swTh_zero, mul_zero, Bc.bcB_zero, mul_zero]
    · rw [Bc.bcB_zero, swTh_zero, swTh_zero, Bc.bcB_zero]
  by_cases hLf : ∃ k, E = swL k
  · -- a leaf
    obtain ⟨k, rfl⟩ := hLf
    obtain ⟨hDL, hBL⟩ := swB_L (S := S) (n := n) k
    obtain ⟨hDLh, hBLh⟩ := swB_Lh (S := S) (n := n) k
    have eL : Om (1 + 1) * swL k = swL k := swK_mul_L ldOm2_SC k
    have eLh : Om 1 * swLh k = swLh k := swK_mul_L Ph.ph_SC_Om1 k
    rw [swTh_leaf, hBL, swTh_leaf, hBLh, eL, eLh, hBL, hBLh]
    exact ⟨hDL, hDL, rfl, swL_lt_top k, swL_mem k, fun _ Q hQ _ => swL_cl hQ k, hDLh, hDLh, rfl, rfl⟩
  push Not at hLf
  have hE1 : 1 ≤ E := Order.one_le_iff_ne_zero.2 hE0
  have hpos : 0 < E := pos_iff_ne_zero.2 hE0
  set e := sgLW E with he
  set q := E / leWe e with hq
  set r := E % leWe e with hr_def
  have hel : e < E := swLW_lt_self hE1 hE hLf
  have hWe : leWe e ≤ E := sgLW_le hpos
  have hWe0 : leWe e ≠ 0 := (leWe_pos e).ne'
  have heH : e ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hEH)
  have hrW : r < leWe e := Ordinal.mod_lt _ hWe0
  have hr : r < E := hrW.trans_le hWe
  have hrH : r ∈ cdHull S l := leModP_mem (Om (1 + 1) * e) hEH
  have hE2 : E < leWe e * Om (1 + 1) := by rw [← leWe_succ]; exact sgLW_lt E
  have hqW : q < Om (1 + 1) := (Ordinal.lt_mul_iff_div_lt hWe0).1 hE2
  have hqH : q ∈ cdHull S l := by
    refine leDivOp_mem (K := Om (1 + 1) * e) (dvd_mul_right _ _) hEH ?_
    have : leWe (e + 1) = ω ^ (Om (1 + 1) * e + Om (1 + 1)) := by unfold leWe; rw [mul_add_one]
    rw [← this]; exact sgLW_lt E
  have hq1 : 1 ≤ q := Order.one_le_iff_pos.2 ((Ordinal.div_pos hWe0).2 hWe)
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq1).ne'
  have hqc : GxCl (upsilon l) (ldAtR S l) q := (ldHull_iff hl hX hqW).1 hqH
  have hEdec : leWe e * q + r = E := Ordinal.div_add_mod E (leWe e)
  -- the codes of `e`, `r` and the bound of `q` (the base-`Ω₂` normal form of a code)
  obtain ⟨heB, hrB, hqB⟩ := swCl_cnf hBSC hEB
  obtain ⟨hDq, hBqc, hΘq, hΘ'q⟩ := IHm q hqc hqB
  obtain ⟨hDe, hDWe, hBWe, hBetop, hBeH, hcle, hDΘe, hDOΘe, hBOΘe, hΘ'e⟩ := IH e hel heH (hel.trans hE) heB
  obtain ⟨hDr, hDWr, hBWr, hBrtop, hBrH, hclr, hDΘr, hDOΘr, hBOΘr, hΘ'r⟩ := IH r hr hrH (hr.trans hE) hrB
  -- `W^e`, `W^e·q`, `E`
  obtain ⟨hDWe0, hBWe'⟩ := ldB_opow (n := n) hDWe
  have hDWe' : MvD S (leWe e) := hDWe0
  rw [hBWe] at hBWe'
  have hBWe'' : Bc.bcB S n (leWe e) = leWe (Bc.bcB S n e) := hBWe'
  obtain ⟨hDWq0, hBWq⟩ := sjB_mulOp (n := n) hDWe Pc hPcD hPcdec q ⟨hqc, hqB⟩
  have hDWq : MvD S (leWe e * q) := hDWq0
  rw [hBWe] at hBWq
  have hBWq' : Bc.bcB S n (leWe e * q) = leWe (Bc.bcB S n e) * Bc.bcB S n q := hBWq
  obtain ⟨hDE, hBE⟩ := mvB_add (k := n) hDWq hDr
  rw [hEdec, hBWq'] at hBE
  rw [hEdec] at hDE
  -- `Ω₂·E`
  obtain ⟨hDK, hBK⟩ := mvB_add (k := n) hD2 hDWe
  rw [hB2, hBWe] at hBK
  obtain ⟨hDKq, hBKq⟩ := sjB_mulOp (n := n) hDK Pc hPcD hPcdec q ⟨hqc, hqB⟩
  rw [hBK] at hBKq
  obtain ⟨hDΩE, hBΩE⟩ := mvB_add (k := n) hDKq hDWr
  have eΩE : Om (1 + 1) * E = ω ^ (Om (1 + 1) + Om (1 + 1) * e) * q + Om (1 + 1) * r := by
    conv_lhs => rw [← hEdec]
    rw [mul_add, eW]
  -- the bounds of the digits after `B_n`
  have hBq1 : 1 ≤ Bc.bcB S n q := by
    have := leB_le (n := n) hD1 hDq hq1; rwa [mwB_one] at this
  have hBqW : Bc.bcB S n q < Om (1 + 1) := by
    have := (mvB_lt_iff (k := n) hDq hD2).2 hqW; rwa [hB2] at this
  have hBrW : Bc.bcB S n r < leWe (Bc.bcB S n e) := by
    have := (mvB_lt_iff (k := n) hDr hDWe').2 hrW; rwa [hBWe''] at this
  obtain ⟨hlogB, hdivB, hmodB⟩ := sjCnf_W hBq1 hBqW hBrW
  rw [← hBE] at hlogB hdivB hmodB
  have hBE1 : 1 ≤ Bc.bcB S n E := by
    have := leB_le (n := n) hD1 hDE hE1; rwa [mwB_one] at this
  have hBEtop : Bc.bcB S n E < swTop S := by
    have := (mvB_lt_iff (k := n) hDE hDtop).2 hE; rwa [hBtop] at this
  have hBLf : ∀ k, Bc.bcB S n E ≠ swL k := by
    intro k hk
    obtain ⟨hDL, hBL⟩ := swB_L (S := S) (n := n) k
    rcases lt_trichotomy E (swL k) with h | h | h
    · have := (mvB_lt_iff (k := n) hDE hDL).2 h; rw [hBL, ← hk] at this; exact lt_irrefl _ this
    · exact hLf k h
    · have := (mvB_lt_iff (k := n) hDL hDE).2 h; rw [hBL, ← hk] at this; exact lt_irrefl _ this
  -- `Θ̂ E`
  have hΘqP1 : P1 (gxTh (upsilon l) (ldAtR S l) q) := ⟨hΘq.trans hc1, hΘq⟩
  obtain ⟨hDOq0, hBOq⟩ := sjB_mulOp (n := n) hDOΘe P1 hP1D hP1dec _ hΘqP1
  have hDOq : MvD S (leOe (swTh S l e) * gxTh (upsilon l) (ldAtR S l) q) := hDOq0
  rw [hBOΘe] at hBOq
  have hBOq' : Bc.bcB S n (leOe (swTh S l e) * gxTh (upsilon l) (ldAtR S l) q) =
      leOe (Bc.bcB S n (swTh S l e)) * Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) q) := hBOq
  have hΘE := swTh_cnf (S := S) h1ρ hE1 hE hLf
  rw [← he, ← hq, ← hr_def] at hΘE
  obtain ⟨hDΘE, hBΘE⟩ := mvB_add (k := n) hDOq hDΘr
  rw [← hΘE, hBOq'] at hBΘE
  rw [← hΘE] at hDΘE
  -- `Ω₁·Θ̂ E`
  obtain ⟨hDK1, hBK1⟩ := mvB_add (k := n) hDO hDOΘe
  rw [hBO, hBOΘe] at hBK1
  obtain ⟨hDK1q, hBK1q⟩ := sjB_mulOp (n := n) hDK1 P1 hP1D hP1dec _ hΘqP1
  rw [hBK1] at hBK1q
  obtain ⟨hDOΘE, hBOΘE⟩ := mvB_add (k := n) hDK1q hDOΘr
  have eOΘE : Om 1 * swTh S l E = ω ^ (Om 1 + Om 1 * swTh S l e) * gxTh (upsilon l) (ldAtR S l) q +
      Om 1 * swTh S l r := by
    rw [hΘE, mul_add, eO]
  refine ⟨hDE, by rw [eΩE]; exact hDΩE, ?_, hBEtop, ?_, ?_, hDΘE, by rw [eOΘE]; exact hDOΘE, ?_, ?_⟩
  · rw [eΩE, hBΩE, hBKq, hBWr, hBE, mul_add, eW]
  · rw [hBE]
    exact CSet.add_mem (leMulWe_mem hBeH ((ldHull_iff hl' hX' hBqW).2 hBqc)) hBrH
  · intro hDB Q hQ hQB
    rw [hBE]
    have hBqQ : Bc.bcB S n q < Q := ((mvB_lt_iff (k := n) hDq hDB).2 hqB).trans_le hQB
    exact LeCl.add (rvCl_mulOp hQ (LeCl.mulK hQ ldOm2_SC _ (hcle hDB Q hQ hQB)) ldOm2_SC _ (LeCl.small hBqQ))
      (hclr hDB Q hQ hQB)
  · rw [eOΘE, hBOΘE, hBK1q, hBOΘr, hBΘE, mul_add, eO]
  · rw [swTh_cnf (S := S) h1ρ' hBE1 hBEtop hBLf, hlogB, hdivB, hmodB, hΘ'e, hΘ'q, hΘ'r, hBΘE]

end Thh

section Sys

variable {n : ℕ} {l l' ηx ηx' : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hl' : IsRestartIdx l') (hX' : upsilon l' < Pv S ηx')

include hl hX hl' hX'

/-- **THE MOVE OF THE LEVEL SYSTEM UP TO `ε_{Ω₂+ω}`**: `St.StLSB S n λ λ' ε_{Ω₂+ω} Θ̂`. -/
theorem swLSB : StLSB S n l l' (swTop S) (swTh S) :=
  fun _ hBSC _ IHm E hEH _ hE hEB => swB_thH hl hX hl' hX' hBSC IHm E hEH hE hEB

end Sys

end Googology.Trans.PoR.InaccPsi.R2.Sw

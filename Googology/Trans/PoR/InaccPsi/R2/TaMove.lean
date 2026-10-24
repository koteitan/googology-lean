import Googology.Trans.PoR.InaccPsi.R2.TaSys

/-!
# The move of the level system up to `E_Γ = φ(Γ₀, Ω₂ + 1)` under `B_n`

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `Θ' = gxTh ρ_{λ'} (ldAtR λ')`, `W^E = Ω₂^E`,
`Ω^x = Ω₁^x`, `Θ̂ = Ta.taTh S λ`, `Θ̂' = Ta.taTh S λ'`, `TaSm a`: `1 ≤ a < Γ₀`.  The move hypothesis `IHm` (as in
`Sj.sjB_thH`): the codes `x < B` at `λ` are in `MvD`, `B_n x` is a code at `λ'`, `Θ x < c_{n+1}` and
`Θ'(B_n x) = B_n(Θ x)`.

* `taGam_lt_L` (`Γ₀ < L(ξ)`), `taSm_B` (**`B_n` fixes the small levels**), `taB_veb` (**`B_n(φ(a, y)) = φ(a, B_n y)`**
  for a small level `a` and every `y ∈ MvD` above `a`, fixed point or not), `taB_top` (`B_n E_Γ = E_Γ`),
  `taSgLW_We`, `taTh_veb` (**THE φ LAW `Θ̂(φ(a, Ω₂ + z)) = φ(a, Ω₁ + Θ̂ z)`** off the fixed points of `φ(a, ·)`);
* `taB_thH` (**THE MOVE OF THE EXPONENTS BELOW `E_Γ`**: for `E ∈ H_λ`, `E < E_Γ`, `E` a code over a strongly
  critical `B` whose codes move: `E ∈ MvD`, `B_n(Ω₂·E) = Ω₂·B_n E`, `B_n E < E_Γ`, `B_n E ∈ H_{λ'}`, the closure
  condition transfers, `B_n(Ω₁·Θ̂ E) = Ω₁·B_n(Θ̂ E)` and **`Θ̂'(B_n E) = B_n(Θ̂ E)`**; at a node by the φ law and
  `taB_veb`, off the nodes by the base-`Ω₂` normal form as in `Sw.swB_thH`);
* `taLSB` (**`St.StLSB S n λ λ' E_Γ Θ̂`**).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ta

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj
  Googology.Trans.PoR.InaccPsi.R2.St

variable {S : InaccSeq.{0}}

/-- `Γ₀ < L(ξ)`. -/
theorem taGam_lt_L (ξ : Ordinal.{0}) : gamma 0 < Nc.ncL S ξ := by
  have h0 : (0 : Ordinal.{0}) < Om ω + Om ω + Nc.ncPp S * ξ :=
    (Om_pos omega0_ne_zero).trans_le (le_self_add.trans le_self_add)
  exact (taGam_le_SC (SC_psi (S := S) Low.InR_Om_one 0)).trans_lt
    (psi_lt_psi_of_mem Low.InR_Om_one h0 (CSet.zero_mem _ _))

/-- **`B_n` fixes the small levels.** -/
theorem taSm_B {n : ℕ} {a : Ordinal.{0}} (ha : TaSm a) : MvD S a ∧ Bc.bcB S n a = a :=
  ⟨mvD_of_lt (ha.2.trans (taGam_lt_L ω)), Bc.bcB_fix (ha.2.trans (taGam_lt_L _))⟩

/-- **`B_n(φ(a, y)) = φ(a, B_n y)`** for a small level `a` and `y ∈ MvD` above `a`. -/
theorem taB_veb {n : ℕ} {a y : Ordinal.{0}} (ha : TaSm a) (hy : MvD S y) (hay : a < y) :
    MvD S (veblen a y) ∧ Bc.bcB S n (veblen a y) = veblen a (Bc.bcB S n y) := by
  have haL : a < Nc.ncL S ω := ha.2.trans (taGam_lt_L ω)
  have hBa : Bc.bcB S n a = a := (taSm_B (S := S) (n := n) ha).2
  by_cases hfix : veblen a y = y
  · rw [hfix, mwB_fixA haL hBa hy hfix]; exact ⟨hy, rfl⟩
  · exact mwB_veblenA haL hBa hy hay hfix

theorem taB_top {n : ℕ} : MvD S (taTop S) ∧ Bc.bcB S n (taTop S) = taTop S := by
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  obtain ⟨hDa, hBa⟩ := mvB_add (k := n) hD2 hD1
  rw [hB2, mwB_one] at hBa
  have hgL : gamma 0 < Nc.ncL S ω := taGam_lt_L ω
  have hDg : MvD S (gamma 0) := mvD_of_lt hgL
  have hBg : Bc.bcB S n (gamma 0) = gamma 0 := Bc.bcB_fix (taGam_lt_L _)
  have hlt : Om (1 + 1 : Ordinal.{0}) + 1 < taTop S :=
    (taVeb_lim gamma_pos.ne').add_one_lt (taKy_lt (le_refl 1))
  have hglt : gamma 0 < taTop S := taGam_lt_Om2.trans ((lt_add_one _).trans hlt)
  obtain ⟨hDv, hBv⟩ := mwB_phi (k := n) hDg hDa hglt hlt
  rw [hBg, hBa] at hBv
  exact ⟨hDv, hBv⟩

theorem taSgLW_We (e : Ordinal.{0}) : sgLW (leWe e) = e := by
  unfold sgLW leWe
  rw [log_opow one_lt_omega0, Ordinal.mul_div_cancel _ ldOm2_SC.1.ne']

/-- **THE φ LAW: `Θ̂(φ(a, Ω₂ + z)) = φ(a, Ω₁ + Θ̂ z)`** for a small level `a`, `z ≥ 1`, `Ω₂ + z < φ(a, Ω₂ + z)`. -/
theorem taTh_veb {l a z : Ordinal.{0}} (ha : TaSm a) (hz : 1 ≤ z)
    (hlt : Om (1 + 1) + z < veblen a (Om (1 + 1) + z)) :
    taTh S l (veblen a (Om (1 + 1) + z)) = veblen a (Om 1 + taTh S l z) := by
  have ha0 := taSm_ne0 ha
  have hW := taWe_veb ha0 hz
  have hc : ¬ (0 < veblen a (Om (1 + 1) + z) ∧ sgLW (veblen a (Om (1 + 1) + z)) < veblen a (Om (1 + 1) + z)) := by
    rintro ⟨-, h⟩
    conv_lhs at h => rw [← hW]
    rw [taSgLW_We] at h
    exact lt_irrefl _ h
  have h1 : invVeblen₁ (veblen a (Om (1 + 1) + z)) = a := invVeblen₁_veblen hlt
  have h2 : invVeblen₂ (veblen a (Om (1 + 1) + z)) = Om (1 + 1) + z := invVeblen₂_veblen ha0 hlt
  have hΩ : Om (1 + 1) < Om (1 + 1) + z := lt_add_of_pos_right _ (zero_lt_one.trans_le hz)
  rw [taTh_node hc (by rw [h2]; exact ⟨hΩ, hlt⟩), h1, h2, Ordinal.add_sub_cancel]

section Thh

variable {n : ℕ} {l l' ηx ηx' : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hl' : IsRestartIdx l') (hX' : upsilon l' < Pv S ηx')
  {B : Ordinal.{0}} (hBSC : SC B)
  (IHm : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < B → MvD S x ∧
    GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
    gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x))

include hl hX hl' hX' hBSC IHm

/-- **THE MOVE OF THE EXPONENTS BELOW `E_Γ = φ(Γ₀, Ω₂ + 1)`.** -/
theorem taB_thH : ∀ E, E ∈ cdHull S l → E < taTop S → LeCl (Om (1 + 1)) B E →
    MvD S E ∧ MvD S (Om (1 + 1) * E) ∧ Bc.bcB S n (Om (1 + 1) * E) = Om (1 + 1) * Bc.bcB S n E ∧
      Bc.bcB S n E < taTop S ∧ Bc.bcB S n E ∈ cdHull S l' ∧
      (MvD S B → ∀ Q, SC Q → Bc.bcB S n B ≤ Q → LeCl (Om (1 + 1)) Q (Bc.bcB S n E)) ∧
      MvD S (taTh S l E) ∧ MvD S (Om 1 * taTh S l E) ∧
      Bc.bcB S n (Om 1 * taTh S l E) = Om 1 * Bc.bcB S n (taTh S l E) ∧
      taTh S l' (Bc.bcB S n E) = Bc.bcB S n (taTh S l E) := by
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
  obtain ⟨hDtop, hBtop⟩ := taB_top (S := S) (n := n)
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
    · rw [taTh_zero]; exact hD0
    · rw [taTh_zero, mul_zero]; exact hD0
    · rw [taTh_zero, mul_zero, Bc.bcB_zero, mul_zero]
    · rw [Bc.bcB_zero, taTh_zero, taTh_zero, Bc.bcB_zero]
  have hE1 : 1 ≤ E := Order.one_le_iff_ne_zero.2 hE0
  have hpos : 0 < E := pos_iff_ne_zero.2 hE0
  by_cases hc : 0 < E ∧ sgLW E < E
  swap
  · -- a node `E = φ(a, Ω₂ + y')`
    obtain ⟨ha, hΩy, hyE, hval⟩ := taNode_nf hE1 hE (fun h => hc ⟨hpos, h⟩)
    have hΘE := taTh_node (S := S) (l := l) hc ⟨hΩy, hyE⟩
    set a := invVeblen₁ E with ha_def
    set y' := invVeblen₂ E - Om (1 + 1) with hy'_def
    have ha0 := taSm_ne0 ha
    have hyadd : Om (1 + 1) + y' = invVeblen₂ E := taNode_add hΩy
    have hy'1 : 1 ≤ y' := taNode_one hΩy
    have hEv : E = veblen a (Om (1 + 1) + y') := by rw [hyadd, hval]
    have haE : a < E := (taSm_lt_Om2 ha).trans (hΩy.trans hyE)
    have hyH : invVeblen₂ E ∈ cdHull S l := (mem_of_veblen_mem (by rw [hval]; exact hEH)
      (by rw [hval]; exact haE) (by rw [hval]; exact hyE)).2
    have hy'H : y' ∈ cdHull S l := taSub_mem _ hyH _
    have hy'E : y' < E := (Ordinal.sub_le_self _ _).trans_lt hyE
    have hy'B : LeCl (Om (1 + 1)) B y' := by
      have h : LeCl (Om (1 + 1)) B (veblen a (invVeblen₂ E)) := by rw [hval]; exact hEB
      exact (leClDec hBSC ldOm2_SC _ (taCl_inv hBSC ldOm2_SC (taSm_lt_Om2 ha) h)).1 _ LeCl.om hΩy.le
    obtain ⟨hDy', -, -, -, hBy'H, hcly', hDΘy', -, -, hΘ'y'⟩ := IH y' hy'E hy'H (hy'E.trans hE) hy'B
    obtain ⟨hDa, hBa⟩ := taSm_B (S := S) (n := n) ha
    obtain ⟨hDy, hBy⟩ := mvB_add (k := n) hD2 hDy'
    rw [hB2] at hBy
    obtain ⟨hDE, hBE⟩ := taB_veb (n := n) ha hDy ((taSm_lt_Om2 ha).trans_le le_self_add)
    rw [hBy, ← hEv] at hBE
    rw [← hEv] at hDE
    have hBy'1 : 1 ≤ Bc.bcB S n y' := by have := leB_le (n := n) hD1 hDy' hy'1; rwa [mwB_one] at this
    have hyEv : Om (1 + 1) + y' < E := by rw [hyadd]; exact hyE
    have hBlt : Om (1 + 1) + Bc.bcB S n y' < veblen a (Om (1 + 1) + Bc.bcB S n y') := by
      have := (mvB_lt_iff (k := n) hDy hDE).2 hyEv
      rwa [hBy, hBE] at this
    -- the image `Θ̂ E = φ(a, Ω₁ + Θ̂ y')`
    obtain ⟨hy'w, hy'v⟩ := taTm_spec hl hX y' hy'H (hy'E.trans hE)
    have hne : taTm y' ≠ TaT.zero := fun h0 => by
      rw [h0] at hy'v; exact absurd hy'1 (by rw [← hy'v]; exact not_le.2 zero_lt_one)
    have hΘ1 : 1 ≤ taTh S l y' := (taV_pos (gg_one_lt_of_SC hρSC) _ hy'w hne).2
    have hBΘ1 : 1 ≤ Bc.bcB S n (taTh S l y') := by
      have := leB_le (n := n) hD1 hDΘy' hΘ1; rwa [mwB_one] at this
    obtain ⟨hDb, hBb⟩ := mvB_add (k := n) hDO hDΘy'
    rw [hBO] at hBb
    obtain ⟨hDΘE, hBΘE⟩ := taB_veb (n := n) ha hDb ((taSm_lt_Om1 ha).trans_le le_self_add)
    rw [hBb] at hBΘE
    rw [← hΘE] at hDΘE hBΘE
    have hWE : Om (1 + 1) * E = E := by rw [hEv]; exact taK_mul_veb ldOm2_SC ha0 (taKy_lt hy'1)
    have hOE : Om 1 * taTh S l E = taTh S l E := by rw [hΘE]; exact taK_mul_veb Ph.ph_SC_Om1 ha0 (taKy_lt hΘ1)
    refine ⟨hDE, by rw [hWE]; exact hDE, ?_, ?_, ?_, ?_, hDΘE, by rw [hOE]; exact hDΘE, ?_, ?_⟩
    · rw [hWE, hBE, taK_mul_veb ldOm2_SC ha0 (taKy_lt hBy'1)]
    · have := (mvB_lt_iff (k := n) hDE hDtop).2 hE; rwa [hBtop] at this
    · rw [hBE]; exact CSet.phi_mem (taSm_hull hl' hX' ha) (CSet.add_mem (mxOm2_mem _ _) hBy'H)
    · intro hDB Q hQ hQB
      rw [hBE]
      exact LeCl.phi (LeCl.small (taSm_lt_SC ha hQ)) (LeCl.add LeCl.om (hcly' hDB Q hQ hQB))
    · rw [hOE, hBΘE, taK_mul_veb Ph.ph_SC_Om1 ha0 (taKy_lt hBΘ1)]
    · rw [hBE, taTh_veb (l := l') ha hBy'1 hBlt, hΘ'y', hBΘE]
  set e := sgLW E with he
  set q := E / leWe e with hq
  set r := E % leWe e with hr_def
  have hel : e < E := hc.2
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
  obtain ⟨heB, hrB, hqB⟩ := Sw.swCl_cnf hBSC hEB
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
  have hBEtop : Bc.bcB S n E < taTop S := by
    have := (mvB_lt_iff (k := n) hDE hDtop).2 hE; rwa [hBtop] at this
  have hcB : 0 < Bc.bcB S n E ∧ sgLW (Bc.bcB S n E) < Bc.bcB S n E := by
    refine ⟨zero_lt_one.trans_le hBE1, ?_⟩
    rw [hlogB]; exact (mvB_lt_iff (k := n) hDe hDE).2 hel
  -- `Θ̂ E`
  have hΘqP1 : P1 (gxTh (upsilon l) (ldAtR S l) q) := ⟨hΘq.trans hc1, hΘq⟩
  obtain ⟨hDOq0, hBOq⟩ := sjB_mulOp (n := n) hDOΘe P1 hP1D hP1dec _ hΘqP1
  have hDOq : MvD S (leOe (taTh S l e) * gxTh (upsilon l) (ldAtR S l) q) := hDOq0
  rw [hBOΘe] at hBOq
  have hBOq' : Bc.bcB S n (leOe (taTh S l e) * gxTh (upsilon l) (ldAtR S l) q) =
      leOe (Bc.bcB S n (taTh S l e)) * Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) q) := hBOq
  have hΘE := taTh_cnf (S := S) h1ρ hc (taTm_spec hl hX _ hrH (hr.trans hE)).1
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
  have eOΘE : Om 1 * taTh S l E = ω ^ (Om 1 + Om 1 * taTh S l e) * gxTh (upsilon l) (ldAtR S l) q +
      Om 1 * taTh S l r := by
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
  · rw [taTh_cnf (S := S) h1ρ' hcB (by rw [hlogB, hmodB]; exact (taTm_spec hl' hX' _ hBrH hBrtop).1),
      hlogB, hdivB, hmodB,
      hΘ'e, hΘ'q, hΘ'r, hBΘE]

end Thh

section Sys

variable {n : ℕ} {l l' ηx ηx' : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hl' : IsRestartIdx l') (hX' : upsilon l' < Pv S ηx')

include hl hX hl' hX'

/-- **THE MOVE OF THE LEVEL SYSTEM UP TO `E_Γ`**: `St.StLSB S n λ λ' E_Γ Θ̂`. -/
theorem taLSB : StLSB S n l l' (taTop S) (taTh S) :=
  fun _ hBSC _ IHm E hEH _ hE hEB => taB_thH hl hX hl' hX' hBSC IHm E hEH hE hEB

end Sys

end Googology.Trans.PoR.InaccPsi.R2.Ta

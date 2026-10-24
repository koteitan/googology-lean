import Googology.Trans.PoR.InaccPsi.R2.SjTop

/-!
# `B_n` commutes with `W^·`, with the Cantor normal form in base `Ω₂` and with `Θ̂ = Sg.sgThH`

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `Θ' = gxTh ρ_{λ'} (ldAtR λ')`, `W^E = Ω₂^E`,
`Ω^x = Ω₁^x`, `ε = ε_{Ω₂+1} = φ(1, Ω₂ + 1)`, `Θ̂ = Sg.sgThH S λ`, `Θ̂' = Sg.sgThH S λ'`.
The move hypothesis `IHm` (as in `Rw.RwAtMove10`): the codes `x < B` at `λ` are in `MvD`, `B_n x` is a code at
`λ'`, `Θ x < c_{n+1}` and `Θ'(B_n x) = B_n(Θ x)`.

* `sjB_mulOp` (**`B_n(ω^K·x) = ω^{B_n K}·B_n x`** for every `x` of a class closed under `log` and the remainder;
  no bound `x < K`, unlike `Le.leB_mulOp2`), `sjB_eps` (**`B_n ε = ε`**);
* `sjCnf_W` (`W^a·q + r` with `1 ≤ q < Ω₂`, `r < W^a` has `log_W = a`, quotient `q`, remainder `r`);
* `sjB_thH` (**THE MOVE OF THE EXPONENTS BELOW `ε_{Ω₂+1}`**: for `E ∈ H_λ`, `E < ε`, `E` a code over a strongly
  critical `B ∈ MvD` whose codes move: `E ∈ MvD`, `B_n(Ω₂·E) = Ω₂·B_n E` (so `B_n(W^E) = W^{B_n E}`),
  `B_n E < ε`, `B_n E ∈ H_{λ'}`, `B_n E` a code over every strongly critical `Q ≥ B_n B` when `B ∈ MvD` (**the
  closure condition transfers**),
  `B_n(Ω₁·Θ̂ E) = Ω₁·B_n(Θ̂ E)` and **`Θ̂'(B_n E) = B_n(Θ̂ E)`**), by induction on `E` with `Sg.sgThH_cnf` at `λ`
  and at `λ'`.

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg

variable {S : InaccSeq.{0}}

/-- **`B_n(ω^K·x) = ω^{B_n K}·B_n x`** for every `x` of a class closed under `log` and the remainder. -/
theorem sjB_mulOp {n : ℕ} {K : Ordinal.{0}} (hDK : MvD S K)
    (P : Ordinal.{0} → Prop) (hPD : ∀ x, P x → MvD S x)
    (hPdec : ∀ x, P x → x ≠ 0 → P (log ω x) ∧ P (x - ω ^ log ω x)) :
    ∀ x, P x → MvD S (ω ^ K * x) ∧ Bc.bcB S n (ω ^ K * x) = ω ^ Bc.bcB S n K * Bc.bcB S n x := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx
  have hDx := hPD x hx
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨by rw [mul_zero]; exact hDx, by rw [mul_zero, Bc.bcB_zero, mul_zero]⟩
  obtain ⟨hPg, hPr⟩ := hPdec x hx hx0
  have hlead : ω ^ log ω x ≤ x := opow_log_le_self ω hx0
  have hdec : ω ^ log ω x + (x - ω ^ log ω x) = x := Ordinal.add_sub_cancel_of_le hlead
  have hDg := hPD _ hPg
  have hDr := hPD _ hPr
  obtain ⟨hDκr, hBκr⟩ := IH _ (leRest_lt hx0) hPr
  obtain ⟨hDog, hBog⟩ := ldB_opow (n := n) hDg
  obtain ⟨-, hBx⟩ := mvB_add (k := n) hDog hDr
  rw [hdec] at hBx
  obtain ⟨hDKg, hBKg⟩ := mvB_add (k := n) hDK hDg
  obtain ⟨hDl, hBl⟩ := ldB_opow (n := n) hDKg
  have e : ω ^ K * x = ω ^ (K + log ω x) + ω ^ K * (x - ω ^ log ω x) := by
    conv_lhs => rw [← hdec]
    rw [mul_add, opow_add]
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDl hDκr
  rw [e, hBx, hBog, mul_add]
  refine ⟨hDs, ?_⟩
  rw [hBs, hBl, hBKg, hBκr, opow_add]

/-- `Ω₂ + 1 < ε` and `1 < ε`, `Ω₂ < ε`. -/
theorem sjEps_bounds : Om (1 + 1 : Ordinal.{0}) < veblen 1 (Om (1 + 1) + 1) ∧
    (1 : Ordinal.{0}) < veblen 1 (Om (1 + 1) + 1) ∧ Om (1 + 1 : Ordinal.{0}) + 1 < veblen 1 (Om (1 + 1) + 1) := by
  have hW1 : (1 : Ordinal.{0}) < Om (1 + 1) := gg_one_lt_of_SC ldOm2_SC
  have hΩ : Om (1 + 1 : Ordinal.{0}) < veblen 1 (Om (1 + 1) + 1) := by
    have h := (veblen_right_strictMono 1).lt_iff_lt.2 (lt_add_one (Om (1 + 1 : Ordinal.{0})))
    rwa [ldOm2_SC.veblen_right hW1] at h
  have h1 : (1 : Ordinal.{0}) < veblen 1 (Om (1 + 1) + 1) := hW1.trans hΩ
  exact ⟨hΩ, h1, Ph.ph_veblen_prin 1 _ hΩ h1⟩

/-- **`B_n ε = ε`**, `ε ∈ MvD`. -/
theorem sjB_eps {n : ℕ} : MvD S (veblen 1 (Om (1 + 1) + 1)) ∧
    Bc.bcB S n (veblen 1 (Om (1 + 1) + 1)) = veblen 1 (Om (1 + 1) + 1) := by
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hDW1, hBW1⟩ := mvB_add (k := n) hD2 hD1
  rw [hB2, mwB_one] at hBW1
  obtain ⟨-, h1, h2⟩ := sjEps_bounds
  obtain ⟨hD, hB⟩ := mwB_phi (k := n) hD1 hDW1 h1 h2
  rw [mwB_one, hBW1] at hB
  exact ⟨hD, hB⟩

/-- **The Cantor normal form in base `Ω₂`**: `log_W(W^a·q + r) = a`, `(W^a·q + r)/W^a = q`,
`(W^a·q + r) mod W^a = r` for `1 ≤ q < Ω₂`, `r < W^a`. -/
theorem sjCnf_W {a q r : Ordinal.{0}} (hq1 : 1 ≤ q) (hqW : q < Om (1 + 1)) (hr : r < leWe a) :
    sgLW (leWe a * q + r) = a ∧ (leWe a * q + r) / leWe a = q ∧ (leWe a * q + r) % leWe a = r := by
  have hW0 : leWe a ≠ 0 := (leWe_pos a).ne'
  have hlo : leWe a ≤ leWe a * q + r := by
    calc leWe a = leWe a * 1 := (mul_one _).symm
      _ ≤ leWe a * q := leMulWe_mono hq1
      _ ≤ leWe a * q + r := le_self_add
  have hhi : leWe a * q + r < leWe (a + 1) := by
    calc leWe a * q + r < leWe a * q + leWe a := (add_lt_add_iff_left _).2 hr
      _ = leWe a * (q + 1) := (mul_add_one _ _).symm
      _ ≤ leWe a * Om (1 + 1) := leMulWe_mono (Order.add_one_le_of_lt hqW)
      _ = leWe (a + 1) := (leWe_succ a).symm
  obtain ⟨h1, h2⟩ := sjLogW hlo hhi
  refine ⟨le_antisymm (Order.lt_add_one_iff.1 h2) h1, ?_, ?_⟩
  · rw [Ordinal.mul_add_div _ hW0, Ordinal.div_eq_zero_of_lt hr, add_zero]
  · rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr]

section Thh

variable {n : ℕ} {l l' ηx ηx' : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hl' : IsRestartIdx l') (hX' : upsilon l' < Pv S ηx')
  {B : Ordinal.{0}} (hBSC : SC B)
  (IHm : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < B → MvD S x ∧
    GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
    gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x))

include hl hX hl' hX' hBSC IHm

/-- **THE MOVE OF THE EXPONENTS BELOW `ε_{Ω₂+1}`**: `B_n` commutes with `W^·` and with `Θ̂`, and the closure
condition transfers. -/
theorem sjB_thH : ∀ E, E ∈ cdHull S l → E < veblen 1 (Om (1 + 1) + 1) → LeCl (Om (1 + 1)) B E →
    MvD S E ∧ MvD S (Om (1 + 1) * E) ∧ Bc.bcB S n (Om (1 + 1) * E) = Om (1 + 1) * Bc.bcB S n E ∧
      Bc.bcB S n E < veblen 1 (Om (1 + 1) + 1) ∧ Bc.bcB S n E ∈ cdHull S l' ∧
      (MvD S B → ∀ Q, SC Q → Bc.bcB S n B ≤ Q → LeCl (Om (1 + 1)) Q (Bc.bcB S n E)) ∧
      MvD S (sgThH S l E) ∧ MvD S (Om 1 * sgThH S l E) ∧
      Bc.bcB S n (Om 1 * sgThH S l E) = Om 1 * Bc.bcB S n (sgThH S l E) ∧
      sgThH S l' (Bc.bcB S n E) = Bc.bcB S n (sgThH S l E) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hc1 : Bc.bcC S (n + 1) < Om 1 := hLw.trans (psi_lt Low.InR_Om_one _)
  have hD0 : MvD S (0 : Ordinal.{0}) := mvD_of_lt (Lw.lw_L_SC S ω).1
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  obtain ⟨hDε, hBε⟩ := sjB_eps (S := S) (n := n)
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  -- the classes
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
    · rw [Bc.bcB_zero]; exact zero_lt_one.trans sjEps_bounds.2.1
    · rw [sgThH_zero]; exact hD0
    · rw [sgThH_zero, mul_zero]; exact hD0
    · rw [sgThH_zero, mul_zero, Bc.bcB_zero, mul_zero]
    · rw [Bc.bcB_zero, sgThH_zero, sgThH_zero, Bc.bcB_zero]
  have hE1 : 1 ≤ E := Order.one_le_iff_ne_zero.2 hE0
  have hpos : 0 < E := pos_iff_ne_zero.2 hE0
  set e := sgLW E with he
  set q := E / leWe e with hq
  set r := E % leWe e with hr_def
  have hel : e < E := sgLW_lt_self hE1 hE
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
  -- the codes of `e`, `r` and the bound of `q`
  have hlogE : LeCl (Om (1 + 1)) B (log ω E) := (leClDec hBSC ldOm2_SC E hEB).2
  have heB : LeCl (Om (1 + 1)) B e := sjCl_div hBSC ldOm2_SC _ hlogE
  have hrB : LeCl (Om (1 + 1)) B r := LeCl.mod hBSC.1 ldOm2_SC.isPrincipal (Om (1 + 1) * e) hEB
  have hqB : q < B := by
    have hlog : log ω E = Om (1 + 1) * e + log ω q := by
      rw [← hEdec]; exact log_opow_mul_add one_lt_omega0 hq0 hrW
    have hlq : log ω q < Om (1 + 1) := (log_le_self ω q).trans_lt hqW
    have hmod : log ω E % Om (1 + 1) = log ω q := by
      rw [hlog, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hlq]
    have hc := LeCl.mod hBSC.1 ldOm2_SC.isPrincipal (Om (1 + 1)) hlogE
    rw [gg_SC_eps ldOm2_SC, hmod] at hc
    have hlqB := LeCl.lt_of_lt hBSC hc hlq
    have h1 := lt_opow_succ_log_self one_lt_omega0 q
    rw [Order.succ_eq_add_one] at h1
    have h2 : ω ^ (log ω q + 1) < B := by
      have := hBSC.2 0 hBSC.1 _ (hBSC.isSuccLimit.succ_lt hlqB)
      rwa [veblen_zero_apply] at this
    exact h1.trans h2
  obtain ⟨hDq, hBqc, hΘq, hΘ'q⟩ := IHm q hqc hqB
  obtain ⟨hDe, hDWe, hBWe, hBeε, hBeH, hcle, hDΘe, hDOΘe, hBOΘe, hΘ'e⟩ := IH e hel heH (hel.trans hE) heB
  obtain ⟨hDr, hDWr, hBWr, hBrε, hBrH, hclr, hDΘr, hDOΘr, hBOΘr, hΘ'r⟩ := IH r hr hrH (hr.trans hE) hrB
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
  have hBEε : Bc.bcB S n E < veblen 1 (Om (1 + 1) + 1) := by
    have := (mvB_lt_iff (k := n) hDE hDε).2 hE; rwa [hBε] at this
  -- `Θ̂ E`
  have hΘqP1 : P1 (gxTh (upsilon l) (ldAtR S l) q) := ⟨hΘq.trans hc1, hΘq⟩
  obtain ⟨hDOq0, hBOq⟩ := sjB_mulOp (n := n) hDOΘe P1 hP1D hP1dec _ hΘqP1
  have hDOq : MvD S (leOe (sgThH S l e) * gxTh (upsilon l) (ldAtR S l) q) := hDOq0
  rw [hBOΘe] at hBOq
  have hBOq' : Bc.bcB S n (leOe (sgThH S l e) * gxTh (upsilon l) (ldAtR S l) q) =
      leOe (Bc.bcB S n (sgThH S l e)) * Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) q) := hBOq
  have hΘE := sgThH_cnf (S := S) l hE1 hE
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
  have eOΘE : Om 1 * sgThH S l E = ω ^ (Om 1 + Om 1 * sgThH S l e) * gxTh (upsilon l) (ldAtR S l) q +
      Om 1 * sgThH S l r := by
    rw [hΘE, mul_add, eO]
  refine ⟨hDE, by rw [eΩE]; exact hDΩE, ?_, hBEε, ?_, ?_, hDΘE, by rw [eOΘE]; exact hDOΘE, ?_, ?_⟩
  · rw [eΩE, hBΩE, hBKq, hBWr, hBE, mul_add, eW]
  · rw [hBE]
    exact CSet.add_mem (leMulWe_mem hBeH ((ldHull_iff hl' hX' hBqW).2 hBqc)) hBrH
  · intro hDB Q hQ hQB
    rw [hBE]
    have hBqQ : Bc.bcB S n q < Q := ((mvB_lt_iff (k := n) hDq hDB).2 hqB).trans_le hQB
    exact LeCl.add (rvCl_mulOp hQ (LeCl.mulK hQ ldOm2_SC _ (hcle hDB Q hQ hQB)) ldOm2_SC _ (LeCl.small hBqQ))
      (hclr hDB Q hQ hQB)
  · rw [eOΘE, hBOΘE, hBK1q, hBOΘr, hBΘE, mul_add, eO]
  · rw [sgThH_cnf (S := S) l' hBE1 hBEε, hlogB, hdivB, hmodB, hΘ'e, hΘ'q, hΘ'r, hBΘE]

end Thh

end Googology.Trans.PoR.InaccPsi.R2.Sj

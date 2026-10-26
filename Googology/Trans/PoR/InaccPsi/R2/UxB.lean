import Googology.Trans.PoR.InaccPsi.R2.UxAt

/-!
# The move of the levels below `Y₃` under `B_n`: `UxLSB S n λ λ' Y₃ T`

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `Θ' = gxTh ρ_{λ'} (ldAtR λ')`, `T = Ug.ugTh`,
`W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `log_W = Sg.sgLW`, `Γ₂ = ψ_{Ω₃}(0)`, `Y₃ = ψ_{Ω₃}(Ω₃)`, `C₂(Q) = Ug.UgC S 2 Q`.
The move hypothesis `IHm` (every code `x < B` of `λ` moves with its reading), as in `St.StLSB`.

* `uxGam_B` (`B_n Γ₂ = Γ₂`), `uxGam_lt_Y`, `uxK_mul_SC` (`κ·E = E` for strongly critical `E > κ`);
* `uxB_thH` (**THE MOVE OF EVERY LEVEL `E < Y₃` OF THE HULL THAT IS A `C₂` CODE OVER `B`**, including
  **`T_{λ'}(B_n E) = B_n(T_λ E)`**, `B_n E < Y₃`, `B_n E ∈ H_{λ'}` and the `C₂` codes of `B_n E`): below `Γ₂` by
  `Ud.udB_thH` at a level `X_k > E` (`Ud.udX_cof`); at a `ψ₃`-atom `ψ₃(d)` (`Ug.ugAtomH`) by `Ug.ugB_psi3`,
  `Ug.ugB_psi2`, `Ug.ugB_atomStep`; at a node `φ(a, y) ≥ Γ₂` (`Ug.ugNode`) by `Mw.mwB_phi` and the φ law
  `Ug.ugVeb` on both sides; at a Cantor normal form `W^e·q + r ≥ Γ₂` (`Ug.ugParts`, `Ug.ugC_cnf`) by `Ug.ugTh_cnf`;
* `uxLSB_Y` (**`UxLSB S n λ λ' Y₃ T`**).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ux

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj
  Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Ua Googology.Trans.PoR.InaccPsi.R2.Ud
  Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj Googology.Trans.PoR.InaccPsi.R2.Uq
  Googology.Trans.PoR.InaccPsi.R2.Uu

variable {S : InaccSeq.{0}}

/-- **`B_n Γ₂ = Γ₂`.** -/
theorem uxGam_B (n : ℕ) : MvD S uaGam ∧ Bc.bcB S n uaGam = uaGam := by
  have hD0 : MvD S (0 : Ordinal.{0}) := mvD_of_lt (Lw.lw_L_SC S ω).1
  obtain ⟨hD, hB, -⟩ := ugB_psi3 (n := n) hD0 (CSet.zero_mem (S := S) 0 (S.psi 0 (Om (1 + 1 + 1))))
  rw [Bc.bcB_zero] at hB
  rw [udGam_eq]; exact ⟨hD, hB⟩

theorem uxGam_lt_Y : uaGam < ugY S := by rw [udGam_eq]; exact ujG3_lt_Y

/-- `κ·E = E` for a strongly critical `E > κ`, `κ` strongly critical. -/
theorem uxK_mul_SC {κ E : Ordinal.{0}} (hκ : SC κ) (hE : SC E) (hlt : κ < E) : κ * E = E := by
  have e : veblen E 0 = E := hE.veblen_zero
  rw [← e]; exact taK_mul_veb hκ hE.1.ne' (by rw [e]; exact hlt)

/-- `ψ₃(x) < Y₃` for `x < Y₃`. -/
theorem uxPsi3_lt_Y {x : Ordinal.{0}} (hx : x < ugY S) : S.psi x (Om (1 + 1 + 1)) < ugY S :=
  psi_lt_psi_of_mem ugInR3 (hx.trans ugY_lt_Om3) (CSet.of_lt hx)

section Thh

variable {n : ℕ} {l l' ηx ηx' : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hl' : IsRestartIdx l') (hX' : upsilon l' < Pv S ηx')
  {B : Ordinal.{0}} (hBSC : SC B)
  (IHm : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < B → MvD S x ∧
    GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
    gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x))

include hl hX hl' hX' hBSC IHm

/-- **THE MOVE OF EVERY LEVEL `E < Y₃` OF THE HULL THAT IS A `C₂` CODE OVER `B`.** -/
theorem uxB_thH : ∀ E, E ∈ cdHull S l → E < ugY S → UgC S (1 + 1) B E →
    MvD S E ∧ MvD S (Om (1 + 1) * E) ∧ Bc.bcB S n (Om (1 + 1) * E) = Om (1 + 1) * Bc.bcB S n E ∧
      Bc.bcB S n E < ugY S ∧ Bc.bcB S n E ∈ cdHull S l' ∧
      (MvD S B → ∀ Q, SC Q → Bc.bcB S n B ≤ Q → UgC S (1 + 1) Q (Bc.bcB S n E)) ∧
      MvD S (ugTh S l E) ∧ MvD S (Om 1 * ugTh S l E) ∧
      Bc.bcB S n (Om 1 * ugTh S l E) = Om 1 * Bc.bcB S n (ugTh S l E) ∧
      ugTh S l' (Bc.bcB S n E) = Bc.bcB S n (ugTh S l E) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hc1 : Bc.bcC S (n + 1) < Om 1 := hLw.trans (psi_lt Low.InR_Om_one _)
  have hD0 : MvD S (0 : Ordinal.{0}) := mvD_of_lt (Lw.lw_L_SC S ω).1
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  have h2 : (1 + 1 : Ordinal.{0}) ≠ 0 := uxTwo_ne
  have hY := uqY_SC (S := S)
  have hWY := uqW_lt_Y (S := S)
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  obtain ⟨hDG, hBG⟩ := uxGam_B (S := S) n
  set Pc : Ordinal.{0} → Prop := fun x => GxCl (upsilon l) (ldAtR S l) x ∧ x < B with hPc
  have hPcD : ∀ x, Pc x → MvD S x := fun x hx => (IHm x hx.1 hx.2).1
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
  intro hEH hEY hEB
  rcases lt_or_ge E uaGam with hEG | hGE
  · -- below `Γ₂`: the move of `Ud.udB_thH` at a level `X_k > E`
    obtain ⟨k, hk⟩ := udX_cof hEG
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ :=
      udB_thH hl hX hl' hX' (udX_lt k) (udX_B k) hBSC IHm E hEH hk (ugC_toLe hEB hEG)
    have hBEG : Bc.bcB S n E < uaGam := a4.trans (udX_lt k)
    rw [ugTh_lt hEG, ugTh_lt hBEG]
    exact ⟨a1, a2, a3, hBEG.trans uxGam_lt_Y, a5, fun hDB Q hQ hQB => UgC.of_le (a6 hDB Q hQ hQB),
      a7, a8, a9, a10⟩
  have hpos : 0 < E := ugGam_pos.trans_le hGE
  have hΩE : Om (1 + 1) < E := uaGam_spec.2.trans_le hGE
  by_cases hcs : sgLW E < E
  · -- a Cantor normal form `E = W^e·q + r ≥ Γ₂`
    set e := sgLW E with he
    set q := E / leWe e with hq
    set r := E % leWe e with hr_def
    obtain ⟨heH, -, hqc, hq1, hqW, hrH, hrW, hEdec', hΘE, -⟩ := ugParts hl hX hEH hpos hEY
    have hel : e < E := hcs
    have hr : r < E := hrW.trans_le (sgLW_le hpos)
    have hEdec : leWe e * q + r = E := hEdec'.symm
    obtain ⟨heB, hrB, hqB⟩ := ugC_cnf hBSC hEB
    obtain ⟨hDq, hBqc, hΘq, hΘ'q⟩ := IHm q hqc hqB
    obtain ⟨hDe, hDWe, hBWe, hBeY, hBeH, hcle, hDΘe, hDOΘe, hBOΘe, hΘ'e⟩ :=
      IH e hel heH (hel.trans hEY) heB
    obtain ⟨hDr, hDWr, hBWr, hBrY, hBrH, hclr, hDΘr, hDOΘr, hBOΘr, hΘ'r⟩ :=
      IH r hr hrH (hr.trans hEY) hrB
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
    obtain ⟨hDK, hBK⟩ := mvB_add (k := n) hD2 hDWe
    rw [hB2, hBWe] at hBK
    obtain ⟨hDKq, hBKq⟩ := sjB_mulOp (n := n) hDK Pc hPcD hPcdec q ⟨hqc, hqB⟩
    rw [hBK] at hBKq
    obtain ⟨hDΩE, hBΩE⟩ := mvB_add (k := n) hDKq hDWr
    have eΩE : Om (1 + 1) * E = ω ^ (Om (1 + 1) + Om (1 + 1) * e) * q + Om (1 + 1) * r := by
      conv_lhs => rw [← hEdec]
      rw [mul_add, eW]
    have hBq1 : 1 ≤ Bc.bcB S n q := by
      have := leB_le (n := n) hD1 hDq hq1; rwa [mwB_one] at this
    have hBqW : Bc.bcB S n q < Om (1 + 1) := by
      have := (mvB_lt_iff (k := n) hDq hD2).2 hqW; rwa [hB2] at this
    have hBrW : Bc.bcB S n r < leWe (Bc.bcB S n e) := by
      have := (mvB_lt_iff (k := n) hDr hDWe').2 hrW; rwa [hBWe''] at this
    obtain ⟨hlogB, hdivB, hmodB⟩ := sjCnf_W hBq1 hBqW hBrW
    rw [← hBE] at hlogB hdivB hmodB
    have hBEY : Bc.bcB S n E < ugY S := by
      rw [hBE]
      refine hY.isPrincipal ((rvWe_lt_succ hBqW).trans (uuWe_lt_Y hBeY)) hBrY
    have hBGE : uaGam ≤ Bc.bcB S n E := by
      have := leB_le (n := n) hDG hDE hGE; rwa [hBG] at this
    have hcB : sgLW (Bc.bcB S n E) < Bc.bcB S n E := by
      rw [hlogB]; exact (mvB_lt_iff (k := n) hDe hDE).2 hel
    have hΘqP1 : P1 (gxTh (upsilon l) (ldAtR S l) q) := ⟨hΘq.trans hc1, hΘq⟩
    obtain ⟨hDOq0, hBOq⟩ := sjB_mulOp (n := n) hDOΘe P1 hP1D hP1dec _ hΘqP1
    have hDOq : MvD S (leOe (ugTh S l e) * gxTh (upsilon l) (ldAtR S l) q) := hDOq0
    rw [hBOΘe] at hBOq
    have hBOq' : Bc.bcB S n (leOe (ugTh S l e) * gxTh (upsilon l) (ldAtR S l) q) =
        leOe (Bc.bcB S n (ugTh S l e)) * Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) q) := hBOq
    obtain ⟨hDΘE, hBΘE⟩ := mvB_add (k := n) hDOq hDΘr
    rw [← hΘE, hBOq'] at hBΘE
    rw [← hΘE] at hDΘE
    obtain ⟨hDK1, hBK1⟩ := mvB_add (k := n) hDO hDOΘe
    rw [hBO, hBOΘe] at hBK1
    obtain ⟨hDK1q, hBK1q⟩ := sjB_mulOp (n := n) hDK1 P1 hP1D hP1dec _ hΘqP1
    rw [hBK1] at hBK1q
    obtain ⟨hDOΘE, hBOΘE⟩ := mvB_add (k := n) hDK1q hDOΘr
    have eOΘE : Om 1 * ugTh S l E = ω ^ (Om 1 + Om 1 * ugTh S l e) * gxTh (upsilon l) (ldAtR S l) q +
        Om 1 * ugTh S l r := by
      rw [hΘE, mul_add, eO]
    refine ⟨hDE, by rw [eΩE]; exact hDΩE, ?_, hBEY, ?_, ?_, hDΘE, by rw [eOΘE]; exact hDOΘE, ?_, ?_⟩
    · rw [eΩE, hBΩE, hBKq, hBWr, hBE, mul_add, eW]
    · rw [hBE]
      exact CSet.add_mem (leMulWe_mem hBeH ((ldHull_iff hl' hX' hBqW).2 hBqc)) hBrH
    · intro hDB Q hQ hQB
      rw [hBE]
      have hBqQ : Bc.bcB S n q < Q := ((mvB_lt_iff (k := n) hDq hDB).2 hqB).trans_le hQB
      exact UgC.add (ugC_mulOp hQ h2 (ugC_mulK hQ h2 _ (hcle hDB Q hQ hQB)) _ (UgC.small hBqQ))
        (hclr hDB Q hQ hQB)
    · rw [eOΘE, hBOΘE, hBK1q, hBOΘr, hBΘE, mul_add, eO]
    · rw [ugTh_cnf hBGE hcB, hlogB, hdivB, hmodB, hΘ'e, hΘ'q, hΘ'r, hBΘE]
  by_cases hSC : SC E
  · -- a `ψ₃`-atom `E = ψ₃(d)`
    obtain ⟨d, hdH, hd, hdown, rfl⟩ := ugAtomH hl hX hEH hSC hΩE hEY
    have hdY : d < ugY S := hd.trans hEY
    have hdB : UgC S (1 + 1) B d := ugC_psiArg hd _ hEB rfl
    obtain ⟨hDd, -, -, hBdY, hBdH, hcld, hDTd, -, -, hT'd⟩ := IH d hd hdH hdY hdB
    obtain ⟨hDE, hBE3, hBown⟩ := ugB_psi3 (n := n) hDd hdown
    have hBd : Bc.bcB S n d < S.psi (Bc.bcB S n d) (Om (1 + 1 + 1)) :=
      lt_psi_of_mem ugInR3 hBown (hBdY.trans ugY_lt_Om3)
    have hBEY : S.psi (Bc.bcB S n d) (Om (1 + 1 + 1)) < ugY S := uxPsi3_lt_Y hBdY
    have hTE : ugTh S l (S.psi d (Om (1 + 1 + 1))) = S.psi (ugTh S l d) (Om (1 + 1)) := ugTh_atom hd
    have hTdown := (ugNormAll hl hX hdH hdY).1
    obtain ⟨hDTE, hBTE, -⟩ := ugB_psi2 (n := n) hDTd hTdown
    have hmove := ugB_atomStep (n := n) (l' := l') hl hX hdH hd hEY hDd hDTd hBdH (by rw [hBE3]; exact hBEY) hT'd
    have hSC3 : SC (S.psi (Bc.bcB S n d) (Om (1 + 1 + 1))) := SC_psi ugInR3 _
    have hSC2 : SC (S.psi (ugTh S l d) (Om (1 + 1))) := SC_psi (InR_Om_succ 1) _
    have hSC2' : SC (S.psi (Bc.bcB S n (ugTh S l d)) (Om (1 + 1))) := SC_psi (InR_Om_succ 1) _
    have hWE := uxK_mul_SC ldOm2_SC hSC hΩE
    have hWBE := uxK_mul_SC ldOm2_SC hSC3 (ugOm2_lt_psi3 _)
    have hOE := uxK_mul_SC Ph.ph_SC_Om1 hSC2 (psiS_bounds (S := S) _ 1).1
    have hOBE := uxK_mul_SC Ph.ph_SC_Om1 hSC2' (psiS_bounds (S := S) _ 1).1
    refine ⟨hDE, by rw [hWE]; exact hDE, ?_, by rw [hBE3]; exact hBEY, ?_, ?_, ?_, ?_, ?_, hmove⟩
    · rw [hWE, hBE3, hWBE]
    · rw [hBE3]; exact uuPsi3_mem hBdH hBdY
    · intro hDB Q hQ hQB
      rw [hBE3]; exact UgC.psi (hcld hDB Q hQ hQB) hBd
    · rw [hTE]; exact hDTE
    · rw [hTE, hOE]; exact hDTE
    · rw [hTE, hOE, hBTE, hOBE]
  · -- a node `E = φ(a, y) ≥ Γ₂`
    obtain ⟨-, hv, ha0, haE, hyE, -, -⟩ := ugNode hGE hSC hcs
    set a := invVeblen₁ E with ha_def
    set y := invVeblen₂ E with hy_def
    have hmem := mem_of_veblen_mem (by rw [hv]; exact hEH) (by rw [hv]; exact haE) (by rw [hv]; exact hyE)
    have hEB' : UgC S (1 + 1) B (veblen a y) := by rw [hv]; exact hEB
    have hyEv : y < veblen a y := by rw [hv]; exact hyE
    have haEv : a < veblen a y := by rw [hv]; exact haE
    have haB : UgC S (1 + 1) B a := ugC_lev _ hEB' a y rfl hyEv
    have hyB : UgC S (1 + 1) B y := ugC_arg hBSC _ hEB' a y rfl hyEv
    obtain ⟨hDa, -, -, hBaY, hBaH, hcla, hDTa, -, -, hT'a⟩ := IH a haE hmem.1 (haE.trans hEY) haB
    obtain ⟨hDy, -, -, hByY, hByH, hcly, hDTy, -, -, hT'y⟩ := IH y hyE hmem.2 (hyE.trans hEY) hyB
    obtain ⟨hDE0, hBE0⟩ := mwB_phi (k := n) hDa hDy haEv hyEv
    rw [hv] at hDE0 hBE0
    have hBa0 : Bc.bcB S n a ≠ 0 := by
      have := (mvB_lt_iff (k := n) hD0 hDa).2 ha0; rw [Bc.bcB_zero] at this; exact this.ne'
    have hBGE : uaGam ≤ Bc.bcB S n E := by
      have := leB_le (n := n) hDG hDE0 hGE; rwa [hBG] at this
    have hBlt : veblen (Bc.bcB S n a) (Bc.bcB S n y) < ugY S := hY.2 _ hBaY _ hByY
    have hTE : ugTh S l E = veblen (ugTh S l a) (ugTh S l y) := by
      conv_lhs => rw [← hv]
      exact ugVeb hl hX hmem.1 hmem.2 ha0.ne' (by rw [hv]; exact hGE) (by rw [hv]; exact hEY)
    have hTaE : ugTh S l a < ugTh S l E := ugLt hl hX hmem.1 hEH hEY haE
    have hTyE : ugTh S l y < ugTh S l E := ugLt hl hX hmem.2 hEH hEY hyE
    obtain ⟨hDTE, hBTE⟩ := mwB_phi (k := n) hDTa hDTy (by rw [← hTE]; exact hTaE) (by rw [← hTE]; exact hTyE)
    rw [← hTE] at hDTE hBTE
    have hTa0 : 0 < ugTh S l a := ugPos hl hX hmem.1 ha0 (haE.trans hEY)
    have hBTa0 : Bc.bcB S n (ugTh S l a) ≠ 0 := by
      have := (mvB_lt_iff (k := n) hD0 hDTa).2 hTa0; rw [Bc.bcB_zero] at this; exact this.ne'
    have hΩTE : Om 1 < ugTh S l E := ugGtOm1 hl hX hEH hGE hEY
    have hBΩTE : Om 1 < Bc.bcB S n (ugTh S l E) := by
      have := (mvB_lt_iff (k := n) hDO hDTE).2 hΩTE; rwa [hBO] at this
    have hWE : Om (1 + 1) * E = E := by
      rw [← hv]; exact taK_mul_veb ldOm2_SC ha0.ne' (by rw [hv]; exact hΩE)
    have hOE : Om 1 * ugTh S l E = ugTh S l E := by
      rw [hTE]; exact taK_mul_veb Ph.ph_SC_Om1 hTa0.ne' (by rw [← hTE]; exact hΩTE)
    refine ⟨hDE0, by rw [hWE]; exact hDE0, ?_, by rw [hBE0]; exact hBlt, ?_, ?_, hDTE,
      by rw [hOE]; exact hDTE, ?_, ?_⟩
    · rw [hWE, hBE0, taK_mul_veb ldOm2_SC hBa0 (by rw [← hBE0]; exact uaGam_spec.2.trans_le hBGE)]
    · rw [hBE0]; exact CSet.phi_mem hBaH hByH
    · intro hDB Q hQ hQB
      rw [hBE0]
      exact UgC.phi (hcla hDB Q hQ hQB) (hcly hDB Q hQ hQB)
    · rw [hOE, hBTE, taK_mul_veb Ph.ph_SC_Om1 hBTa0 (by rw [← hBTE]; exact hBΩTE)]
    · have hBGE' : uaGam ≤ veblen (Bc.bcB S n a) (Bc.bcB S n y) := by rw [← hBE0]; exact hBGE
      rw [hBE0, ugVeb hl' hX' hBaH hByH hBa0 hBGE' hBlt, hT'a, hT'y, hBTE]

end Thh

section Sys

variable {n : ℕ} {l l' ηx ηx' : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hl' : IsRestartIdx l') (hX' : upsilon l' < Pv S ηx')

include hl hX hl' hX'

/-- **THE MOVE OF THE LEVEL SYSTEM OF ALL LEVELS BELOW `Y₃`**: `UxLSB S n λ λ' Y₃ T`. -/
theorem uxLSB_Y : UxLSB S n l l' (ugY S) (ugTh S) :=
  fun _ hBSC _ IHm E hEH _ hE hEB => uxB_thH hl hX hl' hX' hBSC IHm E hEH hE hEB

end Sys

end Googology.Trans.PoR.InaccPsi.R2.Ux

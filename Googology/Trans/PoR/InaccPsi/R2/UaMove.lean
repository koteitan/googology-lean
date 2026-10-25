import Googology.Trans.PoR.InaccPsi.R2.UaLad

/-!
# The move of the level system up to `X₃ = φ(Ω₂ + 1, 0)` under `B_n`

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `Θ' = gxTh ρ_{λ'} (ldAtR λ')`, `T = Ua.uaTh`,
`W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `G = φ(Ω₂, 1)`, `Ĝ = φ(Ω₁, 1)`, `X₃ = Ua.uaX3 = φ(Ω₂ + 1, 0)`.  The move hypothesis `IHm` as
in
`St.StLSB` (every code `x < B` of `λ` moves with its reading).

* `uaB_X3` (`B_n X₃ = X₃`);
* `uaB_thH` (**THE MOVE OF THE EXPONENTS BELOW `X₃`**, including **`T_{λ'}(B_n E) = B_n(T_λ E)`**: below `G` by
  `Tj.tjB_thH`, at `G` (`B_n G = G`, `T G = Ĝ`), above `G` off the nodes along the base-`Ω₂` normal form, at the
  nodes `φ(a, y)` of `(G, X₃)` with a code level `a` by `B_n φ(a, y) = φ(B_n a, B_n y)` (`Tj.tjB_veb`), at the
  nodes `φ(Ω₂, y)` by `B_n φ(Ω₂, y) = φ(Ω₂, B_n y)` and `T φ(Ω₂, y) = φ(Ω₁, T y)`);
* `uaLSB` (**`St.StLSB S n λ λ' X₃ T`**).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ua

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj
  Googology.Trans.PoR.InaccPsi.R2.St
  Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td Googology.Trans.PoR.InaccPsi.R2.Tg
  Googology.Trans.PoR.InaccPsi.R2.Tj Googology.Trans.PoR.InaccPsi.R2.Tn

variable {S : InaccSeq.{0}}

/-- `B_n X₃ = X₃`. -/
theorem uaB_X3 {n : ℕ} : MvD S uaX3 ∧ Bc.bcB S n uaX3 = uaX3 := by
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  have hD0 : MvD S (0 : Ordinal.{0}) := mvD_of_lt (Lw.lw_L_SC S ω).1
  obtain ⟨hD21, hB21⟩ := mvB_add (k := n) hD2 hD1
  rw [hB2, mwB_one] at hB21
  have hlt : Om (1 + 1 : Ordinal.{0}) + 1 < uaX3 := (tnOm2_lt_G.trans uaG_lt_X2).trans uaX2_lt_X3
  obtain ⟨hD, hB⟩ := mwB_phi (k := n) hD21 hD0 hlt veblen_pos
  rw [hB21, Bc.bcB_zero] at hB
  exact ⟨hD, hB⟩

section Thh

variable {n : ℕ} {l l' ηx ηx' : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hl' : IsRestartIdx l') (hX' : upsilon l' < Pv S ηx')
  {B : Ordinal.{0}} (hBSC : SC B)
  (IHm : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < B → MvD S x ∧
    GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
    gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x))

include hl hX hl' hX' hBSC IHm

/-- **THE MOVE OF THE EXPONENTS BELOW `X₃`.** -/
theorem uaB_thH : ∀ E, E ∈ cdHull S l → E < uaX3 → LeCl (Om (1 + 1)) B E →
    MvD S E ∧ MvD S (Om (1 + 1) * E) ∧ Bc.bcB S n (Om (1 + 1) * E) = Om (1 + 1) * Bc.bcB S n E ∧
      Bc.bcB S n E < uaX3 ∧ Bc.bcB S n E ∈ cdHull S l' ∧
      (MvD S B → ∀ Q, SC Q → Bc.bcB S n B ≤ Q → LeCl (Om (1 + 1)) Q (Bc.bcB S n E)) ∧
      MvD S (uaTh S l E) ∧ MvD S (Om 1 * uaTh S l E) ∧
      Bc.bcB S n (Om 1 * uaTh S l E) = Om 1 * Bc.bcB S n (uaTh S l E) ∧
      uaTh S l' (Bc.bcB S n E) = Bc.bcB S n (uaTh S l E) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hc1 : Bc.bcC S (n + 1) < Om 1 := hLw.trans (psi_lt Low.InR_Om_one _)
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  obtain ⟨hDG, hBG⟩ := tjB_G (S := S) (n := n)
  obtain ⟨hDGh, hBGh⟩ := tnB_Gh (S := S) (n := n)
  obtain ⟨hDtop, hBtop⟩ := uaB_X3 (S := S) (n := n)
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
  intro hEH hE hEB
  rcases lt_or_ge E (veblen (Om (1 + 1)) 1) with hEG | hGE
  · -- below `G`
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := tjB_thH hl hX hl' hX' hBSC IHm E hEH hEG hEB
    rw [uaTh_lt hEG, uaTh_lt a4]
    exact ⟨a1, a2, a3, a4.trans (uaG_lt_X2.trans uaX2_lt_X3), a5, a6, a7, a8, a9, a10⟩
  rcases hGE.lt_or_eq with hGlt | hGeq
  swap
  · -- the node `G`
    rw [← hGeq, uaG hl hX, hBG, uaG hl' hX', tnK_mul_G, tnK_mul_Gh]
    exact ⟨hDG, hDG, hBG, (uaG_lt_X2.trans uaX2_lt_X3), tnG_mem, fun _ Q hQ _ => tnG_cl hQ, hDGh, hDGh,
      by rw [hBGh, tnK_mul_Gh], hBGh.symm⟩
  -- above `G`: off the nodes
  have hpos : 0 < E := veblen_pos.trans hGlt
  have hEG' : E < uaGam := hE.trans uaX3_lt_Gam
  by_cases hcs : sgLW E < E
  swap
  · -- a node `E = φ(a, y)` in `(G, X₃)`: a code level `a` or the level `Ω₂`
    obtain ⟨-, hv, ha0, haE, hyE, -, -⟩ := uaNode hGE hEG' hcs
    set a := invVeblen₁ E with ha_def
    set y := invVeblen₂ E with hy_def
    have hmem := mem_of_veblen_mem (by rw [hv]; exact hEH) (by rw [hv]; exact haE) (by rw [hv]; exact hyE)
    have haW3 : a ≤ Om (1 + 1) := uaX3_lev (by rw [hv]; exact hE)
    rcases haW3.lt_or_eq with haW | haW
    swap
    · -- the level `Ω₂`: `E = φ(Ω₂, y)`
      rw [haW] at hv
      have hEB' : LeCl (Om (1 + 1)) B (veblen (Om (1 + 1)) y) := by rw [hv]; exact hEB
      have hyEv : y < veblen (Om (1 + 1)) y := by rw [hv]; exact hyE
      have hyB : LeCl (Om (1 + 1)) B y := uaCl_arg hBSC ldOm2_SC _ hEB' _ y rfl hyEv
      have hy1 : 1 ≤ y := by
        rw [Order.one_le_iff_ne_zero]
        intro h0
        rw [h0, ldOm2_SC.veblen_zero] at hv
        rw [← hv] at hGlt
        exact absurd hGlt (not_lt.2 tgOm_lt_G.le)
      obtain ⟨hDy, -, -, hBytop, hByH, hcly, hDTy, -, -, hT'y⟩ := IH y hyE hmem.2 (hyE.trans hE) hyB
      have hΩE : Om (1 + 1) < veblen (Om (1 + 1)) y := tgOm_lt_G.trans_le (uaG_le_F hy1)
      obtain ⟨hDE0, hBE0⟩ := mwB_phi (k := n) hD2 hDy hΩE hyEv
      rw [hB2, hv] at hBE0
      rw [hv] at hDE0
      have hBy1 : 1 ≤ Bc.bcB S n y := by have := leB_le (n := n) hD1 hDy hy1; rwa [mwB_one] at this
      have hBEtop : Bc.bcB S n E < uaX3 := by
        have := (mvB_lt_iff (k := n) hDE0 hDtop).2 hE; rwa [hBtop] at this
      have hTE : uaTh S l E = veblen (Om 1) (uaTh S l y) := by
        rw [← hv]; exact uaThF hl hX hmem.2 hy1 (by rw [hv]; exact hEG')
      have hTyE : uaTh S l y < veblen (Om 1) (uaTh S l y) := by
        rw [← hTE]; exact uaLt hl hX hmem.2 hEH hEG' hyE
      have hΩTE : Om 1 < veblen (Om 1) (uaTh S l y) := by
        rw [← hTE]; exact uaGtOm hl hX hEH (tgOm_lt_G.trans hGlt) hEG'
      obtain ⟨hDTE, hBTE⟩ := mwB_phi (k := n) hDO hDTy hΩTE hTyE
      rw [hBO, ← hTE] at hBTE
      rw [← hTE] at hDTE
      have hBTy1 : 1 ≤ Bc.bcB S n (uaTh S l y) := by
        have hTy1 : 1 ≤ uaTh S l y := Order.one_le_iff_pos.2 (uaPos hl hX hmem.2 (zero_lt_one.trans_le hy1)
          (hyE.trans hEG'))
        have := leB_le (n := n) hD1 hDTy hTy1; rwa [mwB_one] at this
      have hWE : Om (1 + 1) * E = E := by
        rw [← hv]; exact taK_mul_veb ldOm2_SC ldOm2_SC.1.ne' hΩE
      have hOE : Om 1 * uaTh S l E = uaTh S l E := by
        rw [hTE]; exact taK_mul_veb Ph.ph_SC_Om1 (Om_pos one_ne_zero).ne' hΩTE
      refine ⟨hDE0, by rw [hWE]; exact hDE0, ?_, hBEtop, ?_, ?_, hDTE, by rw [hOE]; exact hDTE, ?_, ?_⟩
      · rw [hWE, hBE0, taK_mul_veb ldOm2_SC ldOm2_SC.1.ne' (tgOm_lt_G.trans_le (uaG_le_F hBy1))]
      · rw [hBE0]; exact CSet.phi_mem (mxOm2_mem _ _) hByH
      · intro hDB Q hQ hQB
        rw [hBE0]
        exact LeCl.phi LeCl.om (hcly hDB Q hQ hQB)
      · rw [hOE, hBTE, taK_mul_veb Ph.ph_SC_Om1 (Om_pos one_ne_zero).ne'
          (Ph.ph_SC_Om1.veblen_zero.symm.le.trans_lt ((veblen_lt_veblen_iff_right).2 (zero_lt_one.trans_le hBTy1)))]
      · have hBlt : veblen (Om (1 + 1)) (Bc.bcB S n y) < uaGam := by
          rw [← hBE0]; exact hBEtop.trans uaX3_lt_Gam
        rw [hBE0, uaThF hl' hX' hByH hBy1 hBlt, hT'y, hBTE]
    have ha1 : 1 ≤ a := Order.one_le_iff_pos.2 ha0
    have hac : GxCl (upsilon l) (ldAtR S l) a := (ldHull_iff hl hX haW).1 hmem.1
    have hEB' : LeCl (Om (1 + 1)) B (veblen a y) := by rw [hv]; exact hEB
    have hyEv : y < veblen a y := by rw [hv]; exact hyE
    have haB : a < B := tdCl_lev_lt hBSC ldOm2_SC hEB' hyEv haW
    have hyB : LeCl (Om (1 + 1)) B y := uaCl_arg hBSC ldOm2_SC _ hEB' a y rfl hyEv
    have hGy : veblen (Om (1 + 1)) 1 < y := by
      by_contra hc
      push Not at hc
      have h1 : veblen a y ≤ veblen a (veblen (Om (1 + 1)) 1) := (veblen_le_veblen_iff_right).2 hc
      rw [veblen_veblen_of_lt haW, hv] at h1
      exact absurd hGlt (not_lt.2 h1)
    obtain ⟨hDy, -, -, hBytop, hByH, hcly, hDTy, -, -, hT'y⟩ := IH y hyE hmem.2 (hyE.trans hE) hyB
    obtain ⟨hDa, hBac, hΘac, hΘ'a⟩ := IHm a hac haB
    have hay : a < y := haW.trans (tgOm_lt_G.trans hGy)
    obtain ⟨hDE0, hBE0⟩ := tjB_veb (k := n) hDa hDy hay
    rw [hv] at hDE0 hBE0
    have hBa1 : 1 ≤ Bc.bcB S n a := by have := leB_le (n := n) hD1 hDa ha1; rwa [mwB_one] at this
    have hBa0 : Bc.bcB S n a ≠ 0 := (zero_lt_one.trans_le hBa1).ne'
    have hBaW : Bc.bcB S n a < Om (1 + 1) := by
      have := (mvB_lt_iff (k := n) hDa hD2).2 haW; rwa [hB2] at this
    have hBGE : veblen (Om (1 + 1)) 1 < Bc.bcB S n E := by
      have := (mvB_lt_iff (k := n) hDG hDE0).2 hGlt; rwa [hBG] at this
    have hBEtop : Bc.bcB S n E < uaX3 := by
      have := (mvB_lt_iff (k := n) hDE0 hDtop).2 hE; rwa [hBtop] at this
    have hBaH : Bc.bcB S n a ∈ cdHull S l' := (ldHull_iff hl' hX' hBaW).2 hBac
    -- the image `T E = φ(Θ a, T y)`
    have hTE : uaTh S l E = veblen (gxTh (upsilon l) (ldAtR S l) a) (uaTh S l y) := by
      conv_lhs => rw [← hv]
      rw [uaVeb hl hX hmem.1 hmem.2 ha0.ne' (by rw [hv]; exact hGE) (by rw [hv]; exact hEG'),
        uaThCode hl hX haW]
    have hΘaO : gxTh (upsilon l) (ldAtR S l) a < Om 1 := Sn.snTh_lt_Om1 hl hX haW.le
    have hDΘa : MvD S (gxTh (upsilon l) (ldAtR S l) a) := mvD_of_lt (hΘac.trans hLw)
    have hGhTy : veblen (Om 1) 1 < uaTh S l y := by
      rw [← uaG hl hX]; exact uaLt hl hX tnG_mem hmem.2 (hyE.trans hEG') hGy
    have hΩTy : Om 1 < uaTh S l y := ((lt_add_one _).trans tnOm1_lt_Gh).trans hGhTy
    have hΘTy : gxTh (upsilon l) (ldAtR S l) a < uaTh S l y := hΘaO.trans hΩTy
    obtain ⟨hDTE, hBTE⟩ := tjB_veb (k := n) hDΘa hDTy hΘTy
    rw [← hTE] at hDTE hBTE
    have hΘa1 : 1 ≤ gxTh (upsilon l) (ldAtR S l) a := by
      have h := gxTh_mono (Z := upsilon l) (At := ldAtR S l) ha1
      rwa [Sq.sqTh_one hl hX] at h
    have hBΘa1 : 1 ≤ Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) a) := by
      have := leB_le (n := n) hD1 hDΘa hΘa1; rwa [mwB_one] at this
    have hBΩTy : Om 1 < Bc.bcB S n (uaTh S l y) := by
      have := (mvB_lt_iff (k := n) hDO hDTy).2 hΩTy; rwa [hBO] at this
    have hWE : Om (1 + 1) * E = E := by
      rw [← hv]; exact taK_mul_veb ldOm2_SC ha0.ne' (by rw [hv]; exact tgOm_lt_G.trans hGlt)
    have hOE : Om 1 * uaTh S l E = uaTh S l E := by
      rw [hTE]; exact taK_mul_veb Ph.ph_SC_Om1 (zero_lt_one.trans_le hΘa1).ne' (hΩTy.trans_le (right_le_veblen _ _))
    refine ⟨hDE0, by rw [hWE]; exact hDE0, ?_, hBEtop, ?_, ?_, hDTE, by rw [hOE]; exact hDTE, ?_, ?_⟩
    · rw [hWE, hBE0, taK_mul_veb ldOm2_SC hBa0 (by rw [← hBE0]; exact tgOm_lt_G.trans hBGE)]
    · rw [hBE0]; exact CSet.phi_mem hBaH hByH
    · intro hDB Q hQ hQB
      rw [hBE0]
      have hBaQ : Bc.bcB S n a < Q := ((mvB_lt_iff (k := n) hDa hDB).2 haB).trans_le hQB
      exact LeCl.phi (LeCl.small hBaQ) (hcly hDB Q hQ hQB)
    · rw [hOE, hBTE, taK_mul_veb Ph.ph_SC_Om1 (zero_lt_one.trans_le hBΘa1).ne'
        (hBΩTy.trans_le (right_le_veblen _ _))]
    · have hBGE' : veblen (Om (1 + 1)) 1 ≤ veblen (Bc.bcB S n a) (Bc.bcB S n y) := by
        rw [← hBE0]; exact hBGE.le
      have hBlt : veblen (Bc.bcB S n a) (Bc.bcB S n y) < uaGam := by
        rw [← hBE0]; exact hBEtop.trans uaX3_lt_Gam
      rw [hBE0, uaVeb hl' hX' hBaH hByH hBa0 hBGE' hBlt, uaThCode hl' hX' hBaW, hΘ'a, hT'y, hBTE]
  set e := sgLW E with he
  set q := E / leWe e with hq
  set r := E % leWe e with hr_def
  obtain ⟨heH, -, hqc, hq1, hqW, hrH, hrW, hEdec', hΘE, -⟩ := uaParts hl hX hEH hpos hEG'
  have hel : e < E := hcs
  have hr : r < E := hrW.trans_le (sgLW_le hpos)
  have hEdec : leWe e * q + r = E := hEdec'.symm
  obtain ⟨heB, hrB, hqB⟩ := Sw.swCl_cnf hBSC hEB
  obtain ⟨hDq, hBqc, hΘq, hΘ'q⟩ := IHm q hqc hqB
  obtain ⟨hDe, hDWe, hBWe, hBetop, hBeH, hcle, hDΘe, hDOΘe, hBOΘe, hΘ'e⟩ := IH e hel heH (hel.trans hE) heB
  obtain ⟨hDr, hDWr, hBWr, hBrtop, hBrH, hclr, hDΘr, hDOΘr, hBOΘr, hΘ'r⟩ := IH r hr hrH (hr.trans hE) hrB
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
  have hBEtop : Bc.bcB S n E < uaX3 := by
    have := (mvB_lt_iff (k := n) hDE hDtop).2 hE; rwa [hBtop] at this
  have hBGE : veblen (Om (1 + 1)) 1 ≤ Bc.bcB S n E := by
    have := leB_le (n := n) hDG hDE hGE; rwa [hBG] at this
  have hcB : sgLW (Bc.bcB S n E) < Bc.bcB S n E := by
    rw [hlogB]; exact (mvB_lt_iff (k := n) hDe hDE).2 hel
  have hΘqP1 : P1 (gxTh (upsilon l) (ldAtR S l) q) := ⟨hΘq.trans hc1, hΘq⟩
  obtain ⟨hDOq0, hBOq⟩ := sjB_mulOp (n := n) hDOΘe P1 hP1D hP1dec _ hΘqP1
  have hDOq : MvD S (leOe (uaTh S l e) * gxTh (upsilon l) (ldAtR S l) q) := hDOq0
  rw [hBOΘe] at hBOq
  have hBOq' : Bc.bcB S n (leOe (uaTh S l e) * gxTh (upsilon l) (ldAtR S l) q) =
      leOe (Bc.bcB S n (uaTh S l e)) * Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) q) := hBOq
  obtain ⟨hDΘE, hBΘE⟩ := mvB_add (k := n) hDOq hDΘr
  rw [← hΘE, hBOq'] at hBΘE
  rw [← hΘE] at hDΘE
  obtain ⟨hDK1, hBK1⟩ := mvB_add (k := n) hDO hDOΘe
  rw [hBO, hBOΘe] at hBK1
  obtain ⟨hDK1q, hBK1q⟩ := sjB_mulOp (n := n) hDK1 P1 hP1D hP1dec _ hΘqP1
  rw [hBK1] at hBK1q
  obtain ⟨hDOΘE, hBOΘE⟩ := mvB_add (k := n) hDK1q hDOΘr
  have eOΘE : Om 1 * uaTh S l E = ω ^ (Om 1 + Om 1 * uaTh S l e) * gxTh (upsilon l) (ldAtR S l) q +
      Om 1 * uaTh S l r := by
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
  · rw [uaTh_cnf hBGE hcB, hlogB, hdivB, hmodB, hΘ'e, hΘ'q, hΘ'r, hBΘE]

end Thh

section Sys

variable {n : ℕ} {l l' ηx ηx' : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hl' : IsRestartIdx l') (hX' : upsilon l' < Pv S ηx')

include hl hX hl' hX'

/-- **THE MOVE OF THE LEVEL SYSTEM UP TO `X₃`**: `St.StLSB S n λ λ' X₃ T`. -/
theorem uaLSB : StLSB S n l l' uaX3 (uaTh S) :=
  fun _ hBSC _ IHm E hEH _ hE hEB => uaB_thH hl hX hl' hX' hBSC IHm E hEH hE hEB

end Sys

end Googology.Trans.PoR.InaccPsi.R2.Ua

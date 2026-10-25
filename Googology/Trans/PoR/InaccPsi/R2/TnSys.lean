import Googology.Trans.PoR.InaccPsi.R2.TnG

/-!
# The level system up to `G + Ω₂²` (`G = φ(Ω₂, 1)`) and its move under `B_n`

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `Θ̂_L = Td.tdThL`, `W^E = Ω₂^E`,
`G = φ(Ω₂, 1)`, `Ĝ = φ(Ω₁, 1)`.

`tnGW S = G + Ω₂·Ω₂` (the bound of the system), `tnTh S λ E` (**the image of a level**): `Θ̂_L E` for `E < G`, and
`Ĝ + Ω₁·Θ((E - G)/Ω₂) + Θ((E - G) mod Ω₂)` for `E ≥ G`, so `Th(G + Ω₂·d + c) = Ĝ + Ω₁·Θ d + Θ c`.

* `tnK_mul`, `tnW2_lt_G`, `tnGW_lt_G3`, `tnGW_lim`, `tnG_rem`, `tnDec2` (**every level `G ≤ E < G + Ω₂²` of the
  hull is `G + Ω₂·d + c` with codes `d, c < Ω₂`**), `tnTh_lt`, `tnTh_ge`;
* `tnLS` (**THE LEVEL SYSTEM UP TO `G + Ω₂²`**: `Tj.tjLS` below `G`; from `G` on the prefix `G + Ω₂·d` of the
  ladder `St.stLad` over `Tn.tnPD_G` and the levels over it, `St.stPreOwP`, `St.stPreLev`; no hypothesis beyond
  the restart index);
* `tnB_Gh` (`B_n Ĝ = Ĝ`), `tnLSB` (**ITS MOVE**: `Tj.tjB_thH` below `G`; from `G` on `B_n(G + x) = G + B_n x`,
  `Th'(B_n E) = Ĝ + Ω₁·Θ'(B_n d) + Θ'(B_n c) = B_n(Th E)`, the proof of `St.stLSB_EW`).

No new axiom.  New definitions: `tnGW`, `tnTh`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rq
  Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj
  Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Sq Googology.Trans.PoR.InaccPsi.R2.St
  Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td Googology.Trans.PoR.InaccPsi.R2.Tg
  Googology.Trans.PoR.InaccPsi.R2.Tj

variable {S : InaccSeq.{0}}

/-- **The bound `G + Ω₂·Ω₂` of the level system.** -/
noncomputable def tnGW (_S : InaccSeq.{0}) : Ordinal.{0} :=
  veblen (Om (1 + 1)) 1 + Om (1 + 1) * Om (1 + 1)

/-- **The image of a level**: `Θ̂_L E` below `G`, `Ĝ + Ω₁·Θ((E-G)/Ω₂) + Θ((E-G) mod Ω₂)` from `G` on. -/
noncomputable def tnTh (S : InaccSeq.{0}) (l E : Ordinal.{0}) : Ordinal.{0} :=
  if E < veblen (Om (1 + 1)) 1 then tdThL S l E
  else veblen (Om 1) 1 +
    Om 1 * gxTh (upsilon l) (ldAtR S l) ((E - veblen (Om (1 + 1)) 1) / Om (1 + 1)) +
    gxTh (upsilon l) (ldAtR S l) ((E - veblen (Om (1 + 1)) 1) % Om (1 + 1))

/-- `κ·X = X` for a strongly critical `κ < X` with `ω^X = X`. -/
theorem tnK_mul {κ X : Ordinal.{0}} (hκ : SC κ) (hX : ω ^ X = X) (hlt : κ < X) : κ * X = X := by
  have h1 : κ < ω ^ X := by rw [hX]; exact hlt
  calc κ * X = ω ^ κ * ω ^ X := by rw [gg_SC_eps hκ, hX]
    _ = ω ^ (κ + X) := (opow_add _ _ _).symm
    _ = ω ^ X := by rw [Ordinal.add_of_omega0_opow_le h1 hX.le]
    _ = X := hX

theorem tnK_mul_G : Om (1 + 1 : Ordinal.{0}) * veblen (Om (1 + 1)) 1 = veblen (Om (1 + 1)) 1 :=
  tnK_mul ldOm2_SC (gg_veblen_eps ldOm2_SC.1.ne') tgOm_lt_G

theorem tnK_mul_Gh : Om (1 : Ordinal.{0}) * veblen (Om 1) 1 = veblen (Om 1) 1 :=
  tnK_mul Ph.ph_SC_Om1 (gg_veblen_eps (Om_pos one_ne_zero).ne') ((lt_add_one _).trans tnOm1_lt_Gh)

theorem tnG_mem {a b : Ordinal.{0}} : veblen (Om (1 + 1)) 1 ∈ S.CSet a b :=
  CSet.phi_mem (Mx.mxOm2_mem _ _) (CSet.one_mem _ _)

theorem tnG_cl {Q : Ordinal.{0}} (hQ : SC Q) : LeCl (Om (1 + 1)) Q (veblen (Om (1 + 1)) 1) :=
  LeCl.phi LeCl.om (LeCl.small (gg_one_lt_of_SC hQ))

/-- `Ω₂·Ω₂ < G`. -/
theorem tnW2_lt_G : Om (1 + 1 : Ordinal.{0}) * Om (1 + 1) < veblen (Om (1 + 1)) 1 := by
  rw [← stW2_opow]
  conv_rhs => rw [← gg_veblen_eps (y := 1) ldOm2_SC.1.ne']
  refine (opow_lt_opow_iff_right one_lt_omega0).2 ?_
  have h2 : Om (1 + 1 : Ordinal.{0}) * (1 + 1) = Om (1 + 1) + Om (1 + 1) := by
    rw [mul_add, mul_one]
  rw [h2]
  exact (Ph.ph_veblen_prin _ _) tgOm_lt_G tgOm_lt_G

theorem tnGW_lt_G3 : tnGW S < S.psi 0 (Om (1 + 1 + 1)) :=
  rwG3_SC.isPrincipal tjG_lt_G3 (ldMul_lt_SC rwG3_SC rwW_lt_G3 rwW_lt_G3)

theorem tnGW_lim : IsSuccLimit (tnGW S) := by
  refine isSuccLimit_add _ ?_
  rw [← stW2_opow]
  exact Ph.ph_opow_lim (mul_ne_zero ldOm2_SC.1.ne' (by simp))

/-- `G + c` in a closure with `c < Ω₂²` gives `c` in the closure. -/
theorem tnG_rem {A ρ c : Ordinal.{0}} (h : veblen (Om (1 + 1)) 1 + c ∈ S.CSet A ρ)
    (hc : c < Om (1 + 1) * Om (1 + 1)) : c ∈ S.CSet A ρ := by
  have hW : leWe (1 + 1) = Om (1 + 1) * Om (1 + 1) := stW2_opow
  rw [← hW] at hc
  exact snHullRem h (by rw [hW]; exact tnG_dvd2) hc

theorem tnTh_lt {l E : Ordinal.{0}} (hE : E < veblen (Om (1 + 1)) 1) : tnTh S l E = tdThL S l E := by
  unfold tnTh; rw [if_pos hE]

theorem tnTh_ge {l d c : Ordinal.{0}} (hc : c < Om (1 + 1)) :
    tnTh S l (veblen (Om (1 + 1)) 1 + Om (1 + 1) * d + c) =
      veblen (Om 1) 1 + Om 1 * gxTh (upsilon l) (ldAtR S l) d + gxTh (upsilon l) (ldAtR S l) c := by
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  unfold tnTh
  have e : veblen (Om (1 + 1)) 1 + Om (1 + 1) * d + c - veblen (Om (1 + 1)) 1 = Om (1 + 1) * d + c := by
    rw [add_assoc, Ordinal.add_sub_cancel]
  rw [if_neg (not_lt.2 (le_self_add.trans le_self_add)), e, Ordinal.mul_add_div _ hW0,
    Ordinal.div_eq_zero_of_lt hc, add_zero, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hc]

theorem tnB_Gh {n : ℕ} : MvD S (veblen (Om 1) 1) ∧ Bc.bcB S n (veblen (Om 1) 1) = veblen (Om 1) 1 := by
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  have hΩG : Om (1 : Ordinal.{0}) < veblen (Om 1) 1 := (lt_add_one _).trans tnOm1_lt_Gh
  have h1G : (1 : Ordinal.{0}) < veblen (Om 1) 1 := (gg_one_lt_of_SC Ph.ph_SC_Om1).trans hΩG
  obtain ⟨hD, hB⟩ := mwB_phi (k := n) hDO hD1 hΩG h1G
  rw [hBO, mwB_one] at hB
  exact ⟨hD, hB⟩

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **Every level `G ≤ E < G + Ω₂²` of the hull is `G + Ω₂·d + c` with codes `d, c < Ω₂`.** -/
theorem tnDec2 {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hGE : veblen (Om (1 + 1)) 1 ≤ E)
    (hE : E < tnGW S) : ∃ d c, E = veblen (Om (1 + 1)) 1 + Om (1 + 1) * d + c ∧
      GxCl (upsilon l) (ldAtR S l) d ∧ d < Om (1 + 1) ∧ GxCl (upsilon l) (ldAtR S l) c ∧ c < Om (1 + 1) := by
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  obtain ⟨x, rfl⟩ := exists_add_of_le hGE
  have hxW : x < Om (1 + 1) * Om (1 + 1) := (add_lt_add_iff_left _).1 hE
  have hxH := tnG_rem hEH hxW
  have hdW : x / Om (1 + 1) < Om (1 + 1) := (Ordinal.div_lt hW0).2 hxW
  have hcW : x % Om (1 + 1) < Om (1 + 1) := Ordinal.mod_lt x hW0
  have hdH : x / Om (1 + 1) ∈ cdHull S l := ldDivK_mem ldOm2_SC hxH
  have hcH : x % Om (1 + 1) ∈ cdHull S l := by
    have h := leModP_mem (S := S) (Om (1 + 1)) hxH; rwa [stW_opow] at h
  refine ⟨x / Om (1 + 1), x % Om (1 + 1), ?_, (ldHull_iff hl hX hdW).1 hdH, hdW,
    (ldHull_iff hl hX hcW).1 hcH, hcW⟩
  rw [add_assoc, Ordinal.div_add_mod]

/-- **THE LEVEL SYSTEM UP TO `G + Ω₂²`.** -/
theorem tnLS : StLS S l (tnGW S) (tnTh S) := by
  have hD0 := tnPD_G (S := S) hl hX
  have hT := tjLS (S := S) hl hX
  refine ⟨tnGW_lim, tnGW_lt_G3, ?_, ?_, ?_⟩
  · intro E hEH h1 hE
    rcases lt_or_ge E (veblen (Om (1 + 1)) 1) with hlt | hge
    · rw [tnTh_lt hlt]; exact hT.ltG E hEH h1 hlt
    · obtain ⟨d, c, rfl, hd, hdW, hc, hcW⟩ := tnDec2 hl hX hEH hge hE
      rw [tnTh_ge hcW]
      exact rwG_SC.isPrincipal (stLad hl hX hD0 tnG_dvd2 d hd hdW).ltG
        ((snTh_lt_Om1 hl hX hcW.le).trans rwO_lt_G)
  · intro E hEH h1 hE
    rcases lt_or_ge E (veblen (Om (1 + 1)) 1) with hlt | hge
    · rw [tnTh_lt hlt]; exact hT.own E hEH h1 hlt
    · obtain ⟨d, c, rfl, hd, hdW, hc, hcW⟩ := tnDec2 hl hX hEH hge hE
      rw [tnTh_ge hcW]
      exact stPreOwP hl hX (stLad hl hX hD0 tnG_dvd2 d hd hdW) hc hcW
  · intro E hEH h1 hE
    rcases lt_or_ge E (veblen (Om (1 + 1)) 1) with hlt | hge
    · rw [tnTh_lt hlt]; exact hT.lev E hEH h1 hlt
    · obtain ⟨d, c, rfl, hd, hdW, hc, hcW⟩ := tnDec2 hl hX hEH hge hE
      rw [tnTh_ge hcW]
      exact stPreLev hl hX (stLad hl hX hD0 tnG_dvd2 d hd hdW) c hc hcW

end Main

section Move

variable {n : ℕ} {l l' ηx ηx' : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hl' : IsRestartIdx l') (hX' : upsilon l' < Pv S ηx')

include hl hX hl' hX'

/-- **THE MOVE OF THE LEVEL SYSTEM UP TO `G + Ω₂²`.** -/
theorem tnLSB : StLSB S n l l' (tnGW S) (tnTh S) := by
  intro B hBSC hGB IHm E hEH h1 hE hEcl
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  obtain ⟨hDε, hBε⟩ := tjB_G (S := S) (n := n)
  obtain ⟨hDεh, hBεh⟩ := tnB_Gh (S := S) (n := n)
  obtain ⟨hDW, hBW⟩ := ldOm2_D (S := S) (k := n)
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  rcases lt_or_ge E (veblen (Om (1 + 1)) 1) with hlt | hge
  · obtain ⟨hDE, hDE2, hBE2, hBEε, hBEH, hBcl, hDT, hDΘ1, hBΘ1, hΘmove⟩ :=
      tjB_thH hl hX hl' hX' hBSC IHm E hEH hlt hEcl
    refine ⟨hDE, hDE2, hBE2, hBEε.trans_le le_self_add, hBEH, hBcl, ?_, ?_, ?_, ?_⟩
    · rw [tnTh_lt hlt]; exact hDT
    · rw [tnTh_lt hlt]; exact hDΘ1
    · rw [tnTh_lt hlt]; exact hBΘ1
    · rw [tnTh_lt hlt, tnTh_lt hBEε]; exact hΘmove
  · obtain ⟨d, c, rfl, hd, hdW, hc, hcW⟩ := tnDec2 hl hX hEH hge hE
    set x := Om (1 + 1) * d + c with hx_def
    have eE : veblen (Om (1 + 1)) 1 + Om (1 + 1) * d + c = veblen (Om (1 + 1)) 1 + x := add_assoc _ _ _
    have hxW2 : x < Om (1 + 1) * Om (1 + 1) := by
      calc x < Om (1 + 1) * d + Om (1 + 1) := (add_lt_add_iff_left _).2 hcW
        _ = Om (1 + 1) * (d + 1) := (mul_add_one _ _).symm
        _ ≤ Om (1 + 1) * Om (1 + 1) := mul_le_mul_left' (Order.add_one_le_of_lt hdW) _
    have hxε : x < veblen (Om (1 + 1)) 1 := hxW2.trans tnW2_lt_G
    have hdH : d ∈ cdHull S l := (ldHull_iff hl hX hdW).2 hd
    have hcH : c ∈ cdHull S l := (ldHull_iff hl hX hcW).2 hc
    have hxH : x ∈ cdHull S l := by
      have := leMulWe_mem (S := S) (CSet.one_mem _ _) hdH
      rw [leWe_one] at this
      exact CSet.add_mem this hcH
    have hxB : LeCl (Om (1 + 1)) B x := by
      have h := (leClDec hBSC ldOm2_SC _ (eE ▸ hEcl)).1 _ (tnG_cl hBSC) le_self_add
      rwa [Ordinal.add_sub_cancel] at h
    obtain ⟨hdxB, hcB⟩ := stCodeHead hBSC (dvd_mul_right _ d) hcW hxB
    have hdB' : LeCl (Om (1 + 1)) B d := by
      have h := sjCl_div hBSC ldOm2_SC _ hdxB; rwa [Ordinal.mul_div_cancel _ hW0] at h
    obtain ⟨hDd, hBdc, hΘd, hΘmd⟩ := IHm d hd (LeCl.lt_of_lt hBSC hdB' hdW)
    obtain ⟨hDc, hBcc, hΘc, hΘmc⟩ := IHm c hc (LeCl.lt_of_lt hBSC hcB hcW)
    obtain ⟨hDx, hDx2, hBx2, -, hBxH, hBxcl, -, -, -, -⟩ :=
      tjB_thH hl hX hl' hX' hBSC IHm x hxH hxε hxB
    obtain ⟨-, hDd2, hBd2, -, -, -, -, -, -, -⟩ :=
      tjB_thH hl hX hl' hX' hBSC IHm d hdH (hdW.trans tgOm_lt_G) hdB'
    -- `B_n x = Ω₂·B_n d + B_n c`
    obtain ⟨-, hBx⟩ := mvB_add (k := n) hDd2 hDc
    rw [hBd2] at hBx
    have hBdW : Bc.bcB S n d < Om (1 + 1) := by
      have h := (mvB_lt_iff (k := n) hDd hDW).2 hdW; rwa [hBW] at h
    have hBcW : Bc.bcB S n c < Om (1 + 1) := by
      have h := (mvB_lt_iff (k := n) hDc hDW).2 hcW; rwa [hBW] at h
    obtain ⟨hDE, hBE⟩ := mvB_add (k := n) hDε hDx
    rw [hBε] at hBE
    have e2 : ∀ y, Om (1 + 1) * (veblen (Om (1 + 1)) 1 + y) = veblen (Om (1 + 1)) 1 + Om (1 + 1) * y :=
      fun y => by rw [mul_add, tnK_mul_G]
    obtain ⟨hDE2, hBE2⟩ := mvB_add (k := n) hDε hDx2
    rw [hBε, hBx2] at hBE2
    have hBEf : Bc.bcB S n (veblen (Om (1 + 1)) 1 + Om (1 + 1) * d + c) =
        veblen (Om (1 + 1)) 1 + Om (1 + 1) * Bc.bcB S n d + Bc.bcB S n c := by
      rw [eE, hBE, hx_def, hBx, add_assoc]
    -- the image
    have hΘdL : gxTh (upsilon l) (ldAtR S l) d < Om 1 := snTh_lt_Om1 hl hX hdW.le
    have hDΘd : MvD S (gxTh (upsilon l) (ldAtR S l) d) := mvD_of_lt (hΘd.trans hLw)
    have hDΘc : MvD S (gxTh (upsilon l) (ldAtR S l) c) := mvD_of_lt (hΘc.trans hLw)
    obtain ⟨hDOd, hBOd⟩ := leB_mulOm1 (S := S) (n := n) hΘdL hΘd
    obtain ⟨hDa, hBa⟩ := mvB_add (k := n) hDεh hDOd
    rw [hBεh, hBOd] at hBa
    obtain ⟨hDT, hBT⟩ := mvB_add (k := n) hDa hDΘc
    rw [hBa] at hBT
    -- `Ω₁·Th` by `Sn.snB_levO` twice
    have hD0 : MvD S (0 : Ordinal.{0}) := mvD_of_lt (Lw.lw_L_SC S ω).1
    obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
    obtain ⟨hDL1, hBL1⟩ := snB_levO (S := S) (n := n) (Xh0 := veblen (Om 1) 1) (Xh0B := veblen (Om 1) 1)
      (a := 1) (b := gxTh (upsilon l) (ldAtR S l) d) (by rw [tnK_mul_Gh]; exact hDεh) (by rw [tnK_mul_Gh, hBεh])
      (by rw [mul_one]; exact hDO) (by rw [mul_one, mwB_one, mul_one, hBO]) hΘd
    obtain ⟨hDL2, hBL2⟩ := snB_levO (S := S) (n := n)
      (Xh0 := veblen (Om 1) 1 + leOe 1 * gxTh (upsilon l) (ldAtR S l) d)
      (Xh0B := veblen (Om 1) 1 + leOe (Bc.bcB S n 1) * Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) d))
      (a := 0) (b := gxTh (upsilon l) (ldAtR S l) c) hDL1 hBL1
      (by rw [mul_zero]; exact hD0) (by rw [mul_zero, Bc.bcB_zero, mul_zero]) hΘc
    simp only [leOe_one, leOe_zero, one_mul, mwB_one, Bc.bcB_zero] at hDL2 hBL2
    refine ⟨by rw [eE]; exact hDE, by rw [eE, e2]; exact hDE2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [eE, e2, hBE2, hBE, e2]
    · rw [hBEf, add_assoc]
      refine (add_lt_add_iff_left _).2 ?_
      calc Om (1 + 1) * Bc.bcB S n d + Bc.bcB S n c < Om (1 + 1) * Bc.bcB S n d + Om (1 + 1) :=
            (add_lt_add_iff_left _).2 hBcW
        _ = Om (1 + 1) * (Bc.bcB S n d + 1) := (mul_add_one _ _).symm
        _ ≤ Om (1 + 1) * Om (1 + 1) := mul_le_mul_left' (Order.add_one_le_of_lt hBdW) _
    · rw [eE, hBE]; exact CSet.add_mem tnG_mem hBxH
    · intro hDB Q hQ hQ'
      rw [eE, hBE]
      exact LeCl.add (tnG_cl hQ) (hBxcl hDB Q hQ hQ')
    · rw [tnTh_ge hcW]; exact hDT
    · rw [tnTh_ge hcW]; exact hDL2
    · rw [tnTh_ge hcW, hBL2, hBT]
    · rw [hBEf, tnTh_ge hBcW, tnTh_ge hcW, hΘmd, hΘmc, hBT]

end Move

end Googology.Trans.PoR.InaccPsi.R2.Tn

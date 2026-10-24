import Googology.Trans.PoR.InaccPsi.R2.StLad

/-!
# The level system up to `ε + Ω₂²` and its move under `B_n`

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `Θ̂ = Sg.sgThH S λ`, `W^E = Ω₂^E`,
`ε = ε_{Ω₂+1}`, `ε̂ = ε_{Ω₁+1}`.

`stEW S = ε + Ω₂·Ω₂` (the bound of the system), `stTh2 S λ E` (**the image of a level**): `Θ̂ E` for `E < ε`, and
`ε̂ + Ω₁·Θ((E - ε)/Ω₂) + Θ((E - ε) mod Ω₂)` for `E ≥ ε`, so `Th(ε + Ω₂·d + c) = ε̂ + Ω₁·Θ d + Θ c` (the image
law `Ω₂ ↦ Ω₁`, codes `↦ Θ`, the leaf `ε ↦ ε̂`).

* `stEps_rem`, `stDec2` (**every level `ε ≤ E < ε + Ω₂²` of the hull is `ε + Ω₂·d + c` with codes `d, c < Ω₂`**),
  `stTh2_lt`, `stTh2_ge`;
* `stLS_EW` (**THE LEVEL SYSTEM UP TO `ε + Ω₂²`**: `Sn.snOwP`, `Sn.snLev` below `ε`; from `ε` on the prefix
  `ε + Ω₂·d` of the ladder `St.stLad` over `St.stPD_eps` and the levels over it, `St.stPreOwP`, `St.stPreLev`;
  no hypothesis beyond the restart index);
* `stLSB_EW` (**ITS MOVE**: `Sj.sjB_thH` below `ε`; from `ε` on `B_n(ε + x) = ε + B_n x` with `x = Ω₂·d + c`
  moved by `Sj.sjB_thH`, and `Th'(B_n E) = ε̂ + Ω₁·Θ'(B_n d) + Θ'(B_n c) = B_n(Th E)` from the moving codes `d`,
  `c`, `B_n ε̂ = ε̂` and `Sn.snB_levO`).

No new axiom.  New definitions: `stEW`, `stTh2`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.St

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rq
  Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj
  Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Sq

variable {S : InaccSeq.{0}}

/-- **The bound `ε + Ω₂·Ω₂` of the level system.** -/
noncomputable def stEW (_S : InaccSeq.{0}) : Ordinal.{0} :=
  veblen 1 (Om (1 + 1) + 1) + Om (1 + 1) * Om (1 + 1)

/-- **The image of a level**: `Θ̂ E` below `ε`, `ε̂ + Ω₁·Θ((E-ε)/Ω₂) + Θ((E-ε) mod Ω₂)` from `ε` on. -/
noncomputable def stTh2 (S : InaccSeq.{0}) (l E : Ordinal.{0}) : Ordinal.{0} :=
  if E < veblen 1 (Om (1 + 1) + 1) then sgThH S l E
  else veblen 1 (Om 1 + 1) +
    Om 1 * gxTh (upsilon l) (ldAtR S l) ((E - veblen 1 (Om (1 + 1) + 1)) / Om (1 + 1)) +
    gxTh (upsilon l) (ldAtR S l) ((E - veblen 1 (Om (1 + 1) + 1)) % Om (1 + 1))

theorem stTh2_lt {l E : Ordinal.{0}} (hE : E < veblen 1 (Om (1 + 1) + 1)) : stTh2 S l E = sgThH S l E := by
  unfold stTh2; rw [if_pos hE]

theorem stTh2_ge {l d c : Ordinal.{0}} (hc : c < Om (1 + 1)) :
    stTh2 S l (veblen 1 (Om (1 + 1) + 1) + Om (1 + 1) * d + c) =
      veblen 1 (Om 1 + 1) + Om 1 * gxTh (upsilon l) (ldAtR S l) d + gxTh (upsilon l) (ldAtR S l) c := by
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  unfold stTh2
  have e : veblen 1 (Om (1 + 1) + 1) + Om (1 + 1) * d + c - veblen 1 (Om (1 + 1) + 1) = Om (1 + 1) * d + c := by
    rw [add_assoc, Ordinal.add_sub_cancel]
  rw [if_neg (not_lt.2 (le_self_add.trans le_self_add)), e, Ordinal.mul_add_div _ hW0,
    Ordinal.div_eq_zero_of_lt hc, add_zero, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hc]

/-- `ε + c` in a closure with `c < ε` gives `c` in the closure. -/
theorem stEps_rem {A ρ c : Ordinal.{0}} (h : veblen 1 (Om (1 + 1) + 1) + c ∈ S.CSet A ρ)
    (hc : c < veblen 1 (Om (1 + 1) + 1)) : c ∈ S.CSet A ρ := by
  have h' := leModP_mem (S := S) (Om (1 + 1) * veblen 1 (Om (1 + 1) + 1)) h
  have hW : ω ^ (Om (1 + 1) * veblen 1 (Om (1 + 1) + 1)) = veblen 1 (Om (1 + 1) + 1) := sqEps_We
  rw [hW] at h'
  have e3 : veblen 1 (Om (1 + 1) + 1) + c = veblen 1 (Om (1 + 1) + 1) * 1 + c := by rw [mul_one]
  rwa [e3, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hc] at h'

/-- `Ω₂·Ω₂ < ε`. -/
theorem stW2_lt_eps : Om (1 + 1 : Ordinal.{0}) * Om (1 + 1) < veblen 1 (Om (1 + 1) + 1) := by
  rw [← stW2_opow]
  have h2 : (1 + 1 : Ordinal.{0}) < ω := isSuccLimit_omega0.succ_lt one_lt_omega0
  exact sqOpow_lt ldOm2_SC ((h2.trans (Lw.lw_omega_lt_SC ldOm2_SC)).trans sqK_lt_eps)

/-- `ε + Ω₂·Ω₂ < ψ_{Ω₃}(0)`. -/
theorem stEW_lt_G3 : stEW S < S.psi 0 (Om (1 + 1 + 1)) :=
  rwG3_SC.isPrincipal snEps_lt_G3 (ldMul_lt_SC rwG3_SC rwW_lt_G3 rwW_lt_G3)

theorem stEW_lim : IsSuccLimit (stEW S) := by
  refine isSuccLimit_add _ ?_
  rw [← stW2_opow]
  exact Googology.Trans.PoR.InaccPsi.R2.Ph.ph_opow_lim (mul_ne_zero ldOm2_SC.1.ne' (by simp))

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **Every level `ε ≤ E < ε + Ω₂²` of the hull is `ε + Ω₂·d + c` with codes `d, c < Ω₂`.** -/
theorem stDec2 {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hεE : veblen 1 (Om (1 + 1) + 1) ≤ E)
    (hE : E < stEW S) : ∃ d c, E = veblen 1 (Om (1 + 1) + 1) + Om (1 + 1) * d + c ∧
      GxCl (upsilon l) (ldAtR S l) d ∧ d < Om (1 + 1) ∧ GxCl (upsilon l) (ldAtR S l) c ∧ c < Om (1 + 1) := by
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  obtain ⟨x, rfl⟩ := exists_add_of_le hεE
  have hxW : x < Om (1 + 1) * Om (1 + 1) := (add_lt_add_iff_left _).1 hE
  have hxH := stEps_rem hEH (hxW.trans stW2_lt_eps)
  have hdW : x / Om (1 + 1) < Om (1 + 1) := (Ordinal.div_lt hW0).2 hxW
  have hcW : x % Om (1 + 1) < Om (1 + 1) := Ordinal.mod_lt x hW0
  have hdH : x / Om (1 + 1) ∈ cdHull S l := ldDivK_mem ldOm2_SC hxH
  have hcH : x % Om (1 + 1) ∈ cdHull S l := by
    have h := leModP_mem (S := S) (Om (1 + 1)) hxH; rwa [stW_opow] at h
  refine ⟨x / Om (1 + 1), x % Om (1 + 1), ?_, (ldHull_iff hl hX hdW).1 hdH, hdW,
    (ldHull_iff hl hX hcW).1 hcH, hcW⟩
  rw [add_assoc, Ordinal.div_add_mod]

/-- **THE LEVEL SYSTEM UP TO `ε + Ω₂²`.** -/
theorem stLS_EW : StLS S l (stEW S) (stTh2 S) := by
  have hD0 := stPD_eps (S := S) hl hX
  refine ⟨stEW_lim, stEW_lt_G3, ?_, ?_, ?_⟩
  · intro E hEH h1 hE
    rcases lt_or_ge E (veblen 1 (Om (1 + 1) + 1)) with hlt | hge
    · rw [stTh2_lt hlt]; exact snThH_lt_G hl hX E hEH hlt
    · obtain ⟨d, c, rfl, hd, hdW, hc, hcW⟩ := stDec2 hl hX hEH hge hE
      rw [stTh2_ge hcW]
      exact rwG_SC.isPrincipal (stLad hl hX hD0 stEps_dvd2 d hd hdW).ltG
        ((snTh_lt_Om1 hl hX hcW.le).trans rwO_lt_G)
  · intro E hEH h1 hE
    rcases lt_or_ge E (veblen 1 (Om (1 + 1) + 1)) with hlt | hge
    · rw [stTh2_lt hlt]; exact snOwP hl hX hEH h1 hlt
    · obtain ⟨d, c, rfl, hd, hdW, hc, hcW⟩ := stDec2 hl hX hEH hge hE
      rw [stTh2_ge hcW]
      exact stPreOwP hl hX (stLad hl hX hD0 stEps_dvd2 d hd hdW) hc hcW
  · intro E hEH h1 hE
    rcases lt_or_ge E (veblen 1 (Om (1 + 1) + 1)) with hlt | hge
    · rw [stTh2_lt hlt]; exact snLev hl hX hEH h1 hlt
    · obtain ⟨d, c, rfl, hd, hdW, hc, hcW⟩ := stDec2 hl hX hEH hge hE
      rw [stTh2_ge hcW]
      exact stPreLev hl hX (stLad hl hX hD0 stEps_dvd2 d hd hdW) c hc hcW

end Main

section Move

variable {n : ℕ} {l l' ηx ηx' : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hl' : IsRestartIdx l') (hX' : upsilon l' < Pv S ηx')

include hl hX hl' hX'

/-- **THE MOVE OF THE LEVEL SYSTEM UP TO `ε + Ω₂²`.** -/
theorem stLSB_EW : StLSB S n l l' (stEW S) (stTh2 S) := by
  intro B hBSC hGB IHm E hEH h1 hE hEcl
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  obtain ⟨hDε, hBε⟩ := sqB_eps (S := S) (n := n)
  obtain ⟨hDεh, hBεh⟩ := sqB_epsH (S := S) (n := n)
  obtain ⟨hDW, hBW⟩ := ldOm2_D (S := S) (k := n)
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  rcases lt_or_ge E (veblen 1 (Om (1 + 1) + 1)) with hlt | hge
  · obtain ⟨hDE, hDE2, hBE2, hBEε, hBEH, hBcl, hDT, hDΘ1, hBΘ1, hΘmove⟩ :=
      sjB_thH hl hX hl' hX' hBSC IHm E hEH hlt hEcl
    refine ⟨hDE, hDE2, hBE2, hBEε.trans_le le_self_add, hBEH, hBcl, ?_, ?_, ?_, ?_⟩
    · rw [stTh2_lt hlt]; exact hDT
    · rw [stTh2_lt hlt]; exact hDΘ1
    · rw [stTh2_lt hlt]; exact hBΘ1
    · rw [stTh2_lt hlt, stTh2_lt hBEε]; exact hΘmove
  · obtain ⟨d, c, rfl, hd, hdW, hc, hcW⟩ := stDec2 hl hX hEH hge hE
    set x := Om (1 + 1) * d + c with hx_def
    have eE : veblen 1 (Om (1 + 1) + 1) + Om (1 + 1) * d + c = veblen 1 (Om (1 + 1) + 1) + x := add_assoc _ _ _
    have hxW2 : x < Om (1 + 1) * Om (1 + 1) := by
      calc x < Om (1 + 1) * d + Om (1 + 1) := (add_lt_add_iff_left _).2 hcW
        _ = Om (1 + 1) * (d + 1) := (mul_add_one _ _).symm
        _ ≤ Om (1 + 1) * Om (1 + 1) := mul_le_mul_left' (Order.add_one_le_of_lt hdW) _
    have hxε : x < veblen 1 (Om (1 + 1) + 1) := hxW2.trans stW2_lt_eps
    have hdH : d ∈ cdHull S l := (ldHull_iff hl hX hdW).2 hd
    have hcH : c ∈ cdHull S l := (ldHull_iff hl hX hcW).2 hc
    have hxH : x ∈ cdHull S l := by
      have := leMulWe_mem (S := S) (CSet.one_mem _ _) hdH
      rw [leWe_one] at this
      exact CSet.add_mem this hcH
    have hxB : LeCl (Om (1 + 1)) B x := by
      have h := (leClDec hBSC ldOm2_SC _ (eE ▸ hEcl)).1 _ (sqEps_cl hBSC) le_self_add
      rwa [Ordinal.add_sub_cancel] at h
    obtain ⟨hdxB, hcB⟩ := stCodeHead hBSC (dvd_mul_right _ d) hcW hxB
    have hdB' : LeCl (Om (1 + 1)) B d := by
      have h := sjCl_div hBSC ldOm2_SC _ hdxB; rwa [Ordinal.mul_div_cancel _ hW0] at h
    obtain ⟨hDd, hBdc, hΘd, hΘmd⟩ := IHm d hd (LeCl.lt_of_lt hBSC hdB' hdW)
    obtain ⟨hDc, hBcc, hΘc, hΘmc⟩ := IHm c hc (LeCl.lt_of_lt hBSC hcB hcW)
    obtain ⟨hDx, hDx2, hBx2, -, hBxH, hBxcl, -, -, -, -⟩ :=
      sjB_thH hl hX hl' hX' hBSC IHm x hxH hxε hxB
    obtain ⟨-, hDd2, hBd2, -, -, -, -, -, -, -⟩ :=
      sjB_thH hl hX hl' hX' hBSC IHm d hdH (hdW.trans sqK_lt_eps) hdB'
    -- `B_n x = Ω₂·B_n d + B_n c`
    obtain ⟨-, hBx⟩ := mvB_add (k := n) hDd2 hDc
    rw [hBd2] at hBx
    have hBdW : Bc.bcB S n d < Om (1 + 1) := by
      have h := (mvB_lt_iff (k := n) hDd hDW).2 hdW; rwa [hBW] at h
    have hBcW : Bc.bcB S n c < Om (1 + 1) := by
      have h := (mvB_lt_iff (k := n) hDc hDW).2 hcW; rwa [hBW] at h
    obtain ⟨hDE, hBE⟩ := mvB_add (k := n) hDε hDx
    rw [hBε] at hBE
    have e2 : ∀ y, Om (1 + 1) * (veblen 1 (Om (1 + 1) + 1) + y) = veblen 1 (Om (1 + 1) + 1) + Om (1 + 1) * y :=
      fun y => by rw [mul_add, sqK_mul_eps ldOm2_SC]
    obtain ⟨hDE2, hBE2⟩ := mvB_add (k := n) hDε hDx2
    rw [hBε, hBx2] at hBE2
    have hBEf : Bc.bcB S n (veblen 1 (Om (1 + 1) + 1) + Om (1 + 1) * d + c) =
        veblen 1 (Om (1 + 1) + 1) + Om (1 + 1) * Bc.bcB S n d + Bc.bcB S n c := by
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
    have hεh1 : Om 1 * veblen 1 (Om 1 + 1) = veblen 1 (Om 1 + 1) :=
      sqK_mul_eps Googology.Trans.PoR.InaccPsi.R2.Ph.ph_SC_Om1
    obtain ⟨hDL1, hBL1⟩ := snB_levO (S := S) (n := n) (Xh0 := veblen 1 (Om 1 + 1)) (Xh0B := veblen 1 (Om 1 + 1))
      (a := 1) (b := gxTh (upsilon l) (ldAtR S l) d) (by rw [hεh1]; exact hDεh) (by rw [hεh1, hBεh])
      (by rw [mul_one]; exact hDO) (by rw [mul_one, mwB_one, mul_one, hBO]) hΘd
    obtain ⟨hDL2, hBL2⟩ := snB_levO (S := S) (n := n)
      (Xh0 := veblen 1 (Om 1 + 1) + leOe 1 * gxTh (upsilon l) (ldAtR S l) d)
      (Xh0B := veblen 1 (Om 1 + 1) + leOe (Bc.bcB S n 1) * Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) d))
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
    · rw [eE, hBE]; exact CSet.add_mem sqEps_mem hBxH
    · intro hDB Q hQ hQ'
      rw [eE, hBE]
      exact LeCl.add (sqEps_cl hQ) (hBxcl hDB Q hQ hQ')
    · rw [stTh2_ge hcW]; exact hDT
    · rw [stTh2_ge hcW]; exact hDL2
    · rw [stTh2_ge hcW, hBL2, hBT]
    · rw [hBEf, stTh2_ge hBcW, stTh2_ge hcW, hΘmd, hΘmc, hBT]

end Move

end Googology.Trans.PoR.InaccPsi.R2.St

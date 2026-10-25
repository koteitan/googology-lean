import Googology.Trans.PoR.InaccPsi.R2.TnLad2

/-!
# The level system up to `G + Ω₂³` (`G = φ(Ω₂, 1)`) and its move under `B_n`

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `Θ̂_L = Td.tdThL`, `W = Ω₂`, `O = Ω₁`,
`G = φ(Ω₂, 1)`, `Ĝ = φ(Ω₁, 1)`.

`tnGW3 S = G + W³` (the bound of the system), `tnTh3 S λ E` (**the image of a level**): `Θ̂_L E` for `E < G`, and for
`E = G + W²·c₂ + W·c₁ + c₀` (codes `cᵢ < W`) the image `Ĝ + O²·Θ c₂ + O·Θ c₁ + Θ c₀`.

* `tnW3_opow`, `tnG_dvd3`, `tnO3_opow`, `tnGh_dvd3`, `tnW3_lt_G`, `tnGW3_lt_G3`, `tnGW3_lim`, `tnG_rem3`,
  `tnTh3_lt`, `tnTh3_ge`, `tnDec3` (**every level `G ≤ E < G + W³` of the hull is `G + W²·c₂ + W·c₁ + c₀` with codes
  `cᵢ < W`**);
* `tnLS3` (**THE LEVEL SYSTEM UP TO `G + Ω₂³`**: `Tj.tjLS` below `G`; from `G` on the prefix `G + W²·c₂` of the
  ladder `Tn.tnLad2` over `Tn.tnPD_G`, the prefix `G + W²·c₂ + W·c₁` of `St.stLad` and the levels over it,
  `St.stPreOwP`, `St.stPreLev`; no hypothesis beyond the restart index);
* `tnLSB3` (**ITS MOVE**: `Tj.tjB_thH` below `G`; from `G` on `B_n(G + x) = G + B_n x` with
  `B_n x = W²·B_n c₂ + W·B_n c₁ + B_n c₀`, and `Th'(B_n E) = B_n(Th E)` from the moving codes, `B_n Ĝ = Ĝ`,
  `Sj.sjB_mulOp` and `Sn.snB_levO`).

No new axiom.  New definitions: `tnGW3`, `tnTh3`.
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

/-- **The bound `G + Ω₂³` of the level system.** -/
noncomputable def tnGW3 (_S : InaccSeq.{0}) : Ordinal.{0} :=
  veblen (Om (1 + 1)) 1 + Om (1 + 1) * Om (1 + 1) * Om (1 + 1)

/-- **The image of a level**: `Θ̂_L E` below `G`; `Ĝ + O²·Θ c₂ + O·Θ c₁ + Θ c₀` at `G + W²·c₂ + W·c₁ + c₀`. -/
noncomputable def tnTh3 (S : InaccSeq.{0}) (l E : Ordinal.{0}) : Ordinal.{0} :=
  if E < veblen (Om (1 + 1)) 1 then tdThL S l E
  else veblen (Om 1) 1 +
    Om 1 * Om 1 * gxTh (upsilon l) (ldAtR S l) ((E - veblen (Om (1 + 1)) 1) / Om (1 + 1) / Om (1 + 1)) +
    Om 1 * gxTh (upsilon l) (ldAtR S l) ((E - veblen (Om (1 + 1)) 1) / Om (1 + 1) % Om (1 + 1)) +
    gxTh (upsilon l) (ldAtR S l) ((E - veblen (Om (1 + 1)) 1) % Om (1 + 1))

theorem tnW3_opow : ω ^ (Om (1 + 1 : Ordinal.{0}) * (1 + 1 + 1)) = Om (1 + 1) * Om (1 + 1) * Om (1 + 1) := by
  rw [mul_add, mul_add, mul_one, opow_add, opow_add, gg_SC_eps ldOm2_SC]

theorem tnO3_opow : ω ^ (Om (1 : Ordinal.{0}) * (1 + 1 + 1)) = Om 1 * Om 1 * Om 1 := by
  rw [mul_add, mul_add, mul_one, opow_add, opow_add, gg_SC_eps tnSC1]

theorem tnG_dvd3 : Om (1 + 1 : Ordinal.{0}) * Om (1 + 1) * Om (1 + 1) ∣ veblen (Om (1 + 1)) 1 := by
  rw [← tnW3_opow]
  conv_rhs => rw [← gg_veblen_eps (y := 1) ldOm2_SC.1.ne']
  refine opow_dvd_opow ω ?_
  have h : Om (1 + 1 : Ordinal.{0}) * (1 + 1 + 1) = Om (1 + 1) + Om (1 + 1) + Om (1 + 1) := by
    rw [mul_add, mul_add, mul_one]
  rw [h]
  have hp := Ph.ph_veblen_prin (Om (1 + 1 : Ordinal.{0})) 1
  exact (hp (hp tgOm_lt_G tgOm_lt_G) tgOm_lt_G).le

theorem tnGh_dvd3 : Om (1 : Ordinal.{0}) * Om 1 * Om 1 ∣ veblen (Om 1) 1 := by
  rw [← tnO3_opow]
  conv_rhs => rw [← gg_veblen_eps (y := 1) (Om_pos one_ne_zero).ne']
  refine opow_dvd_opow ω ?_
  have h : Om (1 : Ordinal.{0}) * (1 + 1 + 1) = Om 1 + Om 1 + Om 1 := by rw [mul_add, mul_add, mul_one]
  rw [h]
  have hp := Ph.ph_veblen_prin (Om (1 : Ordinal.{0})) 1
  have h1 : Om (1 : Ordinal.{0}) < veblen (Om 1) 1 := (lt_add_one _).trans tnOm1_lt_Gh
  exact (hp (hp h1 h1) h1).le

theorem tnW3_lt_G : Om (1 + 1 : Ordinal.{0}) * Om (1 + 1) * Om (1 + 1) < veblen (Om (1 + 1)) 1 := by
  rw [← tnW3_opow]
  conv_rhs => rw [← gg_veblen_eps (y := 1) ldOm2_SC.1.ne']
  refine (opow_lt_opow_iff_right one_lt_omega0).2 ?_
  have h : Om (1 + 1 : Ordinal.{0}) * (1 + 1 + 1) = Om (1 + 1) + Om (1 + 1) + Om (1 + 1) := by
    rw [mul_add, mul_add, mul_one]
  rw [h]
  have hp := Ph.ph_veblen_prin (Om (1 + 1 : Ordinal.{0})) 1
  exact hp (hp tgOm_lt_G tgOm_lt_G) tgOm_lt_G

theorem tnGW3_lt_G3 : tnGW3 S < S.psi 0 (Om (1 + 1 + 1)) :=
  rwG3_SC.isPrincipal tjG_lt_G3
    (ldMul_lt_SC rwG3_SC (ldMul_lt_SC rwG3_SC rwW_lt_G3 rwW_lt_G3) rwW_lt_G3)

theorem tnGW3_lim : IsSuccLimit (tnGW3 S) := by
  refine isSuccLimit_add _ ?_
  rw [← tnW3_opow]
  exact Ph.ph_opow_lim (mul_ne_zero ldOm2_SC.1.ne' (by simp))

/-- `G + c` in a closure with `c < Ω₂³` gives `c` in the closure. -/
theorem tnG_rem3 {A ρ c : Ordinal.{0}} (h : veblen (Om (1 + 1)) 1 + c ∈ S.CSet A ρ)
    (hc : c < Om (1 + 1) * Om (1 + 1) * Om (1 + 1)) : c ∈ S.CSet A ρ := by
  have hW : leWe (1 + 1 + 1) = Om (1 + 1) * Om (1 + 1) * Om (1 + 1) := tnW3_opow
  rw [← hW] at hc
  exact snHullRem h (by rw [hW]; exact tnG_dvd3) hc

theorem tnTh3_lt {l E : Ordinal.{0}} (hE : E < veblen (Om (1 + 1)) 1) : tnTh3 S l E = tdThL S l E := by
  unfold tnTh3; rw [if_pos hE]

theorem tnTh3_ge {l c2 c1 c0 : Ordinal.{0}} (hc1 : c1 < Om (1 + 1)) (hc0 : c0 < Om (1 + 1)) :
    tnTh3 S l (veblen (Om (1 + 1)) 1 + Om (1 + 1) * Om (1 + 1) * c2 + Om (1 + 1) * c1 + c0) =
      veblen (Om 1) 1 + Om 1 * Om 1 * gxTh (upsilon l) (ldAtR S l) c2 + Om 1 * gxTh (upsilon l) (ldAtR S l) c1 +
        gxTh (upsilon l) (ldAtR S l) c0 := by
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  unfold tnTh3
  have e : veblen (Om (1 + 1)) 1 + Om (1 + 1) * Om (1 + 1) * c2 + Om (1 + 1) * c1 + c0 -
      veblen (Om (1 + 1)) 1 = Om (1 + 1) * (Om (1 + 1) * c2 + c1) + c0 := by
    rw [add_assoc, add_assoc, Ordinal.add_sub_cancel, mul_add, mul_assoc, add_assoc]
  have e1 : (Om (1 + 1) * (Om (1 + 1) * c2 + c1) + c0) % Om (1 + 1) = c0 := by
    rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hc0]
  have e2 : (Om (1 + 1) * (Om (1 + 1) * c2 + c1) + c0) / Om (1 + 1) = Om (1 + 1) * c2 + c1 := by
    rw [Ordinal.mul_add_div _ hW0, Ordinal.div_eq_zero_of_lt hc0, add_zero]
  have e3 : (Om (1 + 1) * c2 + c1) / Om (1 + 1) = c2 := by
    rw [Ordinal.mul_add_div _ hW0, Ordinal.div_eq_zero_of_lt hc1, add_zero]
  have e4 : (Om (1 + 1) * c2 + c1) % Om (1 + 1) = c1 := by
    rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hc1]
  rw [if_neg (not_lt.2 (le_self_add.trans (le_self_add.trans le_self_add))), e, e1, e2, e3, e4]

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **Every level `G ≤ E < G + Ω₂³` of the hull is `G + W²·c₂ + W·c₁ + c₀` with codes `cᵢ < W`.** -/
theorem tnDec3 {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hGE : veblen (Om (1 + 1)) 1 ≤ E)
    (hE : E < tnGW3 S) : ∃ c2 c1 c0,
      E = veblen (Om (1 + 1)) 1 + Om (1 + 1) * Om (1 + 1) * c2 + Om (1 + 1) * c1 + c0 ∧
      GxCl (upsilon l) (ldAtR S l) c2 ∧ c2 < Om (1 + 1) ∧ GxCl (upsilon l) (ldAtR S l) c1 ∧ c1 < Om (1 + 1) ∧
      GxCl (upsilon l) (ldAtR S l) c0 ∧ c0 < Om (1 + 1) := by
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  obtain ⟨x, rfl⟩ := exists_add_of_le hGE
  have hxW : x < Om (1 + 1) * Om (1 + 1) * Om (1 + 1) := (add_lt_add_iff_left _).1 hE
  have hxH := tnG_rem3 hEH hxW
  have hyW : x / Om (1 + 1) < Om (1 + 1) * Om (1 + 1) := by
    rw [mul_assoc] at hxW; exact (Ordinal.div_lt hW0).2 hxW
  have hc2W : x / Om (1 + 1) / Om (1 + 1) < Om (1 + 1) := (Ordinal.div_lt hW0).2 hyW
  have hc1W : x / Om (1 + 1) % Om (1 + 1) < Om (1 + 1) := Ordinal.mod_lt _ hW0
  have hc0W : x % Om (1 + 1) < Om (1 + 1) := Ordinal.mod_lt _ hW0
  have hyH : x / Om (1 + 1) ∈ cdHull S l := ldDivK_mem ldOm2_SC hxH
  have hc2H : x / Om (1 + 1) / Om (1 + 1) ∈ cdHull S l := ldDivK_mem ldOm2_SC hyH
  have hc1H : x / Om (1 + 1) % Om (1 + 1) ∈ cdHull S l := by
    have h := leModP_mem (S := S) (Om (1 + 1)) hyH; rwa [stW_opow] at h
  have hc0H : x % Om (1 + 1) ∈ cdHull S l := by
    have h := leModP_mem (S := S) (Om (1 + 1)) hxH; rwa [stW_opow] at h
  refine ⟨_, _, _, ?_, (ldHull_iff hl hX hc2W).1 hc2H, hc2W, (ldHull_iff hl hX hc1W).1 hc1H, hc1W,
    (ldHull_iff hl hX hc0W).1 hc0H, hc0W⟩
  conv_lhs => rw [← Ordinal.div_add_mod x (Om (1 + 1)), ← Ordinal.div_add_mod (x / Om (1 + 1)) (Om (1 + 1))]
  rw [mul_add, ← mul_assoc, add_assoc, add_assoc, add_assoc]

/-- **THE LEVEL SYSTEM UP TO `G + Ω₂³`.** -/
theorem tnLS3 : StLS S l (tnGW3 S) (tnTh3 S) := by
  have hD0 := tnPD_G (S := S) hl hX
  have hT := tjLS (S := S) hl hX
  have hpre : ∀ c2 c1, GxCl (upsilon l) (ldAtR S l) c2 → c2 < Om (1 + 1) → GxCl (upsilon l) (ldAtR S l) c1 →
      c1 < Om (1 + 1) → StPD S l (veblen (Om (1 + 1)) 1 + Om (1 + 1) * Om (1 + 1) * c2 + Om (1 + 1) * c1)
        (veblen (Om 1) 1 + Om 1 * Om 1 * gxTh (upsilon l) (ldAtR S l) c2 + Om 1 * gxTh (upsilon l) (ldAtR S l) c1) := by
    intro c2 c1 hc2 hc2W hc1 hc1W
    have hD2 := tnLad2 hl hX hD0 tnG_dvd3 tnGh_dvd3 c2 hc2 hc2W
    have hd2 : Om (1 + 1) * Om (1 + 1) ∣ veblen (Om (1 + 1)) 1 + Om (1 + 1) * Om (1 + 1) * c2 :=
      dvd_add ((dvd_mul_right _ _).trans tnG_dvd3) (dvd_mul_right _ _)
    exact stLad hl hX hD2 hd2 c1 hc1 hc1W
  refine ⟨tnGW3_lim, tnGW3_lt_G3, ?_, ?_, ?_⟩
  · intro E hEH h1 hE
    rcases lt_or_ge E (veblen (Om (1 + 1)) 1) with hlt | hge
    · rw [tnTh3_lt hlt]; exact hT.ltG E hEH h1 hlt
    · obtain ⟨c2, c1, c0, rfl, hc2, hc2W, hc1, hc1W, hc0, hc0W⟩ := tnDec3 hl hX hEH hge hE
      rw [tnTh3_ge hc1W hc0W]
      exact rwG_SC.isPrincipal (hpre c2 c1 hc2 hc2W hc1 hc1W).ltG ((snTh_lt_Om1 hl hX hc0W.le).trans rwO_lt_G)
  · intro E hEH h1 hE
    rcases lt_or_ge E (veblen (Om (1 + 1)) 1) with hlt | hge
    · rw [tnTh3_lt hlt]; exact hT.own E hEH h1 hlt
    · obtain ⟨c2, c1, c0, rfl, hc2, hc2W, hc1, hc1W, hc0, hc0W⟩ := tnDec3 hl hX hEH hge hE
      rw [tnTh3_ge hc1W hc0W]
      exact stPreOwP hl hX (hpre c2 c1 hc2 hc2W hc1 hc1W) hc0 hc0W
  · intro E hEH h1 hE
    rcases lt_or_ge E (veblen (Om (1 + 1)) 1) with hlt | hge
    · rw [tnTh3_lt hlt]; exact hT.lev E hEH h1 hlt
    · obtain ⟨c2, c1, c0, rfl, hc2, hc2W, hc1, hc1W, hc0, hc0W⟩ := tnDec3 hl hX hEH hge hE
      rw [tnTh3_ge hc1W hc0W]
      exact stPreLev hl hX (hpre c2 c1 hc2 hc2W hc1 hc1W) c0 hc0 hc0W

end Main

/-- `B_n(Ω₁·2) = Ω₁·2` and `B_n(1 + 1) = 1 + 1`. -/
theorem tnB_two {n : ℕ} : MvD S (Om 1 * (1 + 1)) ∧ Bc.bcB S n (Om 1 * (1 + 1)) = Om 1 * (1 + 1) ∧
    MvD S (1 + 1 : Ordinal.{0}) ∧ Bc.bcB S n (1 + 1 : Ordinal.{0}) = 1 + 1 := by
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  obtain ⟨hD2, hB2⟩ := mvB_add (k := n) hD1 hD1
  obtain ⟨hDOO, hBOO⟩ := mvB_add (k := n) hDO hDO
  rw [mwB_one] at hB2
  rw [hBO] at hBOO
  have e : Om (1 : Ordinal.{0}) * (1 + 1) = Om 1 + Om 1 := by rw [mul_add, mul_one]
  exact ⟨by rw [e]; exact hDOO, by rw [e]; exact hBOO, hD2, hB2⟩

section Move

variable {n : ℕ} {l l' ηx ηx' : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hl' : IsRestartIdx l') (hX' : upsilon l' < Pv S ηx')

include hl hX hl' hX'

/-- **THE MOVE OF THE LEVEL SYSTEM UP TO `G + Ω₂³`.** -/
theorem tnLSB3 : StLSB S n l l' (tnGW3 S) (tnTh3 S) := by
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
    · rw [tnTh3_lt hlt]; exact hDT
    · rw [tnTh3_lt hlt]; exact hDΘ1
    · rw [tnTh3_lt hlt]; exact hBΘ1
    · rw [tnTh3_lt hlt, tnTh3_lt hBEε]; exact hΘmove
  obtain ⟨c2, c1, c0, rfl, hc2, hc2W, hc1, hc1W, hc0, hc0W⟩ := tnDec3 hl hX hEH hge hE
  set W := Om (1 + 1 : Ordinal.{0}) with hW_def
  set G := veblen W 1 with hG_def
  set y := W * c2 + c1 with hy_def
  set x := W * y + c0 with hx_def
  have eE : G + W * W * c2 + W * c1 + c0 = G + x := by
    rw [hx_def, hy_def, mul_add, ← mul_assoc, add_assoc, add_assoc, add_assoc]
  have hyW2 : y < W * W := by
    calc y < W * c2 + W := (add_lt_add_iff_left _).2 hc1W
      _ = W * (c2 + 1) := (mul_add_one _ _).symm
      _ ≤ W * W := mul_le_mul_left' (Order.add_one_le_of_lt hc2W) _
  have hxW3 : x < W * W * W := by
    calc x < W * y + W := (add_lt_add_iff_left _).2 hc0W
      _ = W * (y + 1) := (mul_add_one _ _).symm
      _ ≤ W * (W * W) := mul_le_mul_left' (Order.add_one_le_of_lt hyW2) _
      _ = W * W * W := (mul_assoc _ _ _).symm
  have hxG : x < G := hxW3.trans tnW3_lt_G
  have hyG : y < G := hyW2.trans tnW2_lt_G
  have hc2H : c2 ∈ cdHull S l := (ldHull_iff hl hX hc2W).2 hc2
  have hc1H : c1 ∈ cdHull S l := (ldHull_iff hl hX hc1W).2 hc1
  have hc0H : c0 ∈ cdHull S l := (ldHull_iff hl hX hc0W).2 hc0
  have hyH : y ∈ cdHull S l := CSet.add_mem (ldMulK_mem ldOm2_SC (Mx.mxOm2_mem _ _) hc2H) hc1H
  have hxH : x ∈ cdHull S l := CSet.add_mem (ldMulK_mem ldOm2_SC (Mx.mxOm2_mem _ _) hyH) hc0H
  have hxB : LeCl W B x := by
    have h := (leClDec hBSC ldOm2_SC _ (eE ▸ hEcl)).1 _ (tnG_cl hBSC) le_self_add
    rwa [Ordinal.add_sub_cancel] at h
  obtain ⟨hWyB, hc0B⟩ := stCodeHead hBSC (dvd_mul_right _ y) hc0W hxB
  have hyB : LeCl W B y := by
    have h := sjCl_div hBSC ldOm2_SC _ hWyB; rwa [Ordinal.mul_div_cancel _ hW0] at h
  obtain ⟨hWc2B, hc1B⟩ := stCodeHead hBSC (dvd_mul_right _ c2) hc1W hyB
  have hc2B : LeCl W B c2 := by
    have h := sjCl_div hBSC ldOm2_SC _ hWc2B; rwa [Ordinal.mul_div_cancel _ hW0] at h
  obtain ⟨hDc2, hBc2c, hΘc2, hΘm2⟩ := IHm c2 hc2 (LeCl.lt_of_lt hBSC hc2B hc2W)
  obtain ⟨hDc1, hBc1c, hΘc1, hΘm1⟩ := IHm c1 hc1 (LeCl.lt_of_lt hBSC hc1B hc1W)
  obtain ⟨hDc0, hBc0c, hΘc0, hΘm0⟩ := IHm c0 hc0 (LeCl.lt_of_lt hBSC hc0B hc0W)
  obtain ⟨hDx, hDx2, hBx2, -, hBxH, hBxcl, -, -, -, -⟩ := tjB_thH hl hX hl' hX' hBSC IHm x hxH hxG hxB
  obtain ⟨-, hDy2, hBy2, -, -, -, -, -, -, -⟩ := tjB_thH hl hX hl' hX' hBSC IHm y hyH hyG hyB
  obtain ⟨-, hDc22, hBc22, -, -, -, -, -, -, -⟩ :=
    tjB_thH hl hX hl' hX' hBSC IHm c2 hc2H (hc2W.trans tgOm_lt_G) hc2B
  -- `B_n x = W²·B_n c₂ + W·B_n c₁ + B_n c₀`
  obtain ⟨hDy, hBy⟩ := mvB_add (k := n) hDc22 hDc1
  rw [hBc22] at hBy
  obtain ⟨-, hBx⟩ := mvB_add (k := n) hDy2 hDc0
  rw [hBy2, hBy] at hBx
  have hBlt : ∀ c, MvD S c → c < W → Bc.bcB S n c < W := fun c hDc hcW => by
    have h := (mvB_lt_iff (k := n) hDc hDW).2 hcW; rwa [hBW] at h
  have hBc2W := hBlt c2 hDc2 hc2W
  have hBc1W := hBlt c1 hDc1 hc1W
  have hBc0W := hBlt c0 hDc0 hc0W
  obtain ⟨hDE, hBE⟩ := mvB_add (k := n) hDε hDx
  rw [hBε] at hBE
  have e2 : ∀ z, W * (G + z) = G + W * z := fun z => by rw [mul_add, tnK_mul_G]
  obtain ⟨hDE2, hBE2⟩ := mvB_add (k := n) hDε hDx2
  rw [hBε, hBx2] at hBE2
  have hBEf : Bc.bcB S n (G + W * W * c2 + W * c1 + c0) =
      G + W * W * Bc.bcB S n c2 + W * Bc.bcB S n c1 + Bc.bcB S n c0 := by
    rw [eE, hBE, hBx, mul_add, ← mul_assoc, add_assoc, add_assoc, add_assoc]
  -- the image
  set O := Om (1 : Ordinal.{0}) with hO_def
  have hΘ2L : gxTh (upsilon l) (ldAtR S l) c2 < O := snTh_lt_Om1 hl hX hc2W.le
  have hΘ1L : gxTh (upsilon l) (ldAtR S l) c1 < O := snTh_lt_Om1 hl hX hc1W.le
  have hDΘ0 : MvD S (gxTh (upsilon l) (ldAtR S l) c0) := mvD_of_lt (hΘc0.trans hLw)
  obtain ⟨hDK, hBK, hD11, hB11⟩ := tnB_two (S := S) (n := n)
  have hOO : ω ^ (O * (1 + 1)) = O * O := tnO2_opow
  obtain ⟨hDm2, hBm2⟩ := sjB_mulOp (n := n) hDK (fun x => x < Bc.bcC S (n + 1))
    (fun x hx => mvD_of_lt (hx.trans hLw))
    (fun x hx _ => ⟨(log_le_self ω x).trans_lt hx, (Ordinal.sub_le_self _ _).trans_lt hx⟩) _ hΘc2
  rw [hOO, hBK, hOO] at hBm2
  rw [hOO] at hDm2
  obtain ⟨hDm1, hBm1⟩ := leB_mulOm1 (S := S) (n := n) hΘ1L hΘc1
  obtain ⟨hDa, hBa⟩ := mvB_add (k := n) hDεh hDm2
  rw [hBεh, hBm2] at hBa
  obtain ⟨hDb, hBb⟩ := mvB_add (k := n) hDa hDm1
  rw [hBa, hBm1] at hBb
  obtain ⟨hDT, hBT⟩ := mvB_add (k := n) hDb hDΘ0
  rw [hBb] at hBT
  -- `Ω₁·Th` by `Sn.snB_levO` three times
  have hD0 : MvD S (0 : Ordinal.{0}) := mvD_of_lt (Lw.lw_L_SC S ω).1
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  have hεh1 : O * veblen O 1 = veblen O 1 := tnK_mul_Gh
  obtain ⟨hDL1, hBL1⟩ := snB_levO (S := S) (n := n) (Xh0 := veblen O 1) (Xh0B := veblen O 1)
    (a := 1 + 1) (b := gxTh (upsilon l) (ldAtR S l) c2) (by rw [hεh1]; exact hDεh) (by rw [hεh1, hBεh])
    hDK (by rw [hBK, hB11]) hΘc2
  obtain ⟨hDL2, hBL2⟩ := snB_levO (S := S) (n := n)
    (Xh0 := veblen O 1 + leOe (1 + 1) * gxTh (upsilon l) (ldAtR S l) c2)
    (Xh0B := veblen O 1 + leOe (Bc.bcB S n (1 + 1)) * Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) c2))
    (a := 1) (b := gxTh (upsilon l) (ldAtR S l) c1) hDL1 hBL1
    (by rw [mul_one]; exact hDO) (by rw [mul_one, mwB_one, mul_one, hBO]) hΘc1
  obtain ⟨hDL3, hBL3⟩ := snB_levO (S := S) (n := n)
    (Xh0 := veblen O 1 + leOe (1 + 1) * gxTh (upsilon l) (ldAtR S l) c2 + leOe 1 * gxTh (upsilon l) (ldAtR S l) c1)
    (Xh0B := veblen O 1 + leOe (Bc.bcB S n (1 + 1)) * Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) c2) +
      leOe (Bc.bcB S n 1) * Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) c1))
    (a := 0) (b := gxTh (upsilon l) (ldAtR S l) c0) hDL2 hBL2
    (by rw [mul_zero]; exact hD0) (by rw [mul_zero, Bc.bcB_zero, mul_zero]) hΘc0
  have hOe2 : leOe (1 + 1) = O * O := by unfold leOe; exact hOO
  simp only [leOe_one, leOe_zero, one_mul, mwB_one, Bc.bcB_zero, hB11, hOe2] at hDL3 hBL3
  refine ⟨by rw [eE]; exact hDE, by rw [eE, e2]; exact hDE2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eE, e2, hBE2, hBE, e2]
  · rw [hBEf]
    have hlt3 : W * W * Bc.bcB S n c2 + W * Bc.bcB S n c1 + Bc.bcB S n c0 < W * W * W := by
      have hyB : W * Bc.bcB S n c2 + Bc.bcB S n c1 < W * W := by
        calc W * Bc.bcB S n c2 + Bc.bcB S n c1 < W * Bc.bcB S n c2 + W := (add_lt_add_iff_left _).2 hBc1W
          _ = W * (Bc.bcB S n c2 + 1) := (mul_add_one _ _).symm
          _ ≤ W * W := mul_le_mul_left' (Order.add_one_le_of_lt hBc2W) _
      calc W * W * Bc.bcB S n c2 + W * Bc.bcB S n c1 + Bc.bcB S n c0
          = W * (W * Bc.bcB S n c2 + Bc.bcB S n c1) + Bc.bcB S n c0 := by rw [mul_add, mul_assoc]
        _ < W * (W * Bc.bcB S n c2 + Bc.bcB S n c1) + W := (add_lt_add_iff_left _).2 hBc0W
        _ = W * (W * Bc.bcB S n c2 + Bc.bcB S n c1 + 1) := (mul_add_one _ _).symm
        _ ≤ W * (W * W) := mul_le_mul_left' (Order.add_one_le_of_lt hyB) _
        _ = W * W * W := (mul_assoc _ _ _).symm
    have := (add_lt_add_iff_left G).2 hlt3
    simpa only [add_assoc] using this
  · rw [eE, hBE]; exact CSet.add_mem tnG_mem hBxH
  · intro hDB Q hQ hQ'
    rw [eE, hBE]
    exact LeCl.add (tnG_cl hQ) (hBxcl hDB Q hQ hQ')
  · rw [tnTh3_ge hc1W hc0W]; exact hDT
  · rw [tnTh3_ge hc1W hc0W]; exact hDL3
  · rw [tnTh3_ge hc1W hc0W, hBL3, hBT]
  · rw [hBEf, tnTh3_ge hBc1W hBc0W, tnTh3_ge hc1W hc0W, hΘm2, hΘm1, hΘm0, hBT]

end Move

end Googology.Trans.PoR.InaccPsi.R2.Tn

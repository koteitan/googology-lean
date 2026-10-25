import Googology.Trans.PoR.InaccPsi.R2.TuStepG
import Googology.Trans.PoR.InaccPsi.R2.TuSysX

/-!
# The level system up to `G + ε_{Ω₂+1}` (`G = φ(Ω₂, 1)`), its move under `B_n`, and the road

`B_n = Bc.bcB S n`, `Θ = gxTh ρ_λ (ldAtR λ)`, `Θ̂_L = Td.tdThL`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `G = φ(Ω₂, 1)`,
`Ĝ = φ(Ω₁, 1)`, `ε = ε_{Ω₂+1} = φ(1, Ω₂ + 1)`, `ε̂ = φ(1, Ω₁ + 1)`, the image `Tu.tuTh` (`Θ̂_L E` below `G`,
`Ĝ + Θ̂_L x` at `G + x`), `F_E = ψ_{Ω₂}(W^{W^{G + ε}})`.

`tuGE S = G + ε` (the bound).

* `tuWe_eps` (`W^ε = ε`), `tuMul_lt_fix`, `tuWe_lt_eps` (`W^x < ε` for `x < ε`), `tuEpsh_lt_Gh` (`ε̂ < Ĝ`),
  `tuThG_lt_epsh` (`Θ̂_L x < ε̂` below `ε`);
* `tuLevXG` (**every `x < ε` of the hull over a prefix `P`** (`W^{log_W x + 1} ∣ P`): own data and the level
  statement of `P + x` with the image `P̂ + Θ̂_L x`; the prefixes `P + W^e·c` of `Tu.tuStepLadG`), `tuPD_GG`
  (**`G + W^e·c` is a prefix for every `1 ≤ e < ε` of `H_λ` and every code `c < Ω₂`**);
* `tuLSG` (**THE LEVEL SYSTEM UP TO `G + ε_{Ω₂+1}`**), `tuLSBG` (**ITS MOVE**);
* `tuAtMoveTopG` (**every atom `ψ_{Ω₂}(0) < s < F_E` moves** once the codes below it move), `TuAtMove21 S` (a
  hypothesis name: the move of the atoms `F_E ≤ s ≤ θ`), `tuAtMove20_of21`, `tuAtMove21_of20`, `tuAtMove17_of21`,
  `tuRoadG` (**the road**), `tuRoadG_hyps`.

No new axiom.  New definitions: `tuGE`, the hypothesis name `TuAtMove21`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tu

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Lj Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Rq
  Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw Googology.Trans.PoR.InaccPsi.R2.Sc
  Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj Googology.Trans.PoR.InaccPsi.R2.Sn
  Googology.Trans.PoR.InaccPsi.R2.St Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td
  Googology.Trans.PoR.InaccPsi.R2.Tg Googology.Trans.PoR.InaccPsi.R2.Tj Googology.Trans.PoR.InaccPsi.R2.Tn

variable {S : InaccSeq.{0}}

/-- **The bound `G + ε_{Ω₂+1}` of the level system.** -/
noncomputable def tuGE (_S : InaccSeq.{0}) : Ordinal.{0} := veblen (Om (1 + 1)) 1 + veblen 1 (Om (1 + 1) + 1)

/-- `a·b < E` and `a + b < E` for `a, b < E = ω^E`. -/
theorem tuMul_lt_fix {E a b : Ordinal.{0}} (hE : ω ^ E = E) (ha : a < E) (hb : b < E) : a * b < E := by
  have hp : IsPrincipal (· + ·) E := by rw [← hE]; exact isPrincipal_add_omega0_opow E
  calc a * b ≤ ω ^ a * ω ^ b := mul_le_mul' (right_le_opow a one_lt_omega0) (right_le_opow b one_lt_omega0)
    _ = ω ^ (a + b) := (opow_add _ _ _).symm
    _ < ω ^ E := (opow_lt_opow_iff_right one_lt_omega0).2 (hp ha hb)
    _ = E := hE

theorem tuEps_fix : ω ^ veblen 1 (Om (1 + 1 : Ordinal.{0}) + 1) = veblen 1 (Om (1 + 1) + 1) :=
  gg_veblen_eps one_ne_zero

/-- `W^x < ε` for `x < ε`. -/
theorem tuWe_lt_eps {x : Ordinal.{0}} (hx : x < veblen 1 (Om (1 + 1) + 1)) :
    leWe x < veblen 1 (Om (1 + 1 : Ordinal.{0}) + 1) := by
  unfold leWe
  conv_rhs => rw [← tuEps_fix]
  exact (opow_lt_opow_iff_right one_lt_omega0).2 (tuMul_lt_fix tuEps_fix tuOm2_lt_eps hx)

/-- **`W^ε = ε`.** -/
theorem tuWe_eps : leWe (veblen 1 (Om (1 + 1 : Ordinal.{0}) + 1)) = veblen 1 (Om (1 + 1) + 1) := by
  unfold leWe
  rw [tnK_mul ldOm2_SC tuEps_fix tuOm2_lt_eps, tuEps_fix]

/-- `ε̂ = φ(1, Ω₁ + 1) < Ĝ = φ(Ω₁, 1)`. -/
theorem tuEpsh_lt_Gh : veblen 1 (Om (1 : Ordinal.{0}) + 1) < veblen (Om 1) 1 := by
  have h1 : (1 : Ordinal.{0}) < Om 1 := gg_one_lt_of_SC Ph.ph_SC_Om1
  have hfix : veblen 1 (veblen (Om (1 : Ordinal.{0})) 1) = veblen (Om 1) 1 := veblen_veblen_of_lt h1 1
  calc veblen 1 (Om 1 + 1) < veblen 1 (veblen (Om 1) 1) := (veblen_lt_veblen_iff_right).2 tnOm1_lt_Gh
    _ = veblen (Om 1) 1 := hfix

theorem tuGE_lt_G3 : tuGE S < S.psi 0 (Om (1 + 1 + 1)) :=
  rwG3_SC.isPrincipal tjG_lt_G3 (tuEps_lt_G.trans tjG_lt_G3)

theorem tuGE_lim : IsSuccLimit (tuGE S) := isSuccLimit_add _ tuEps_lim

/-- `G + Ω₂^{Ω₂^{Ω₂}} ≤ G + ε`. -/
theorem tuGV_le_GE : tuGV S ≤ tuGE S :=
  (add_le_add_iff_left _).2 (tuWe_lt_eps (tuWe_lt_eps tuOm2_lt_eps)).le

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **`Θ̂_L x < ε̂ = φ(1, Ω₁ + 1)`** for `x ∈ H_λ`, `x < ε`. -/
theorem tuThG_lt_epsh : ∀ x, x ∈ cdHull S l → x < veblen 1 (Om (1 + 1) + 1) →
    tdThL S l x < veblen 1 (Om (1 : Ordinal.{0}) + 1) := by
  have hfix : ω ^ veblen 1 (Om (1 : Ordinal.{0}) + 1) = veblen 1 (Om 1 + 1) := gg_veblen_eps one_ne_zero
  have hp : IsPrincipal (· + ·) (veblen 1 (Om (1 : Ordinal.{0}) + 1)) := by
    rw [← hfix]; exact isPrincipal_add_omega0_opow _
  have hO : Om (1 : Ordinal.{0}) < veblen 1 (Om 1 + 1) := (lt_add_one _).trans_le (right_le_veblen _ _)
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hxH hxE
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [tjThL_zero]; exact (Ph.ph_SC_Om1.1).trans hO
  have h0 := pos_iff_ne_zero.2 hx0
  obtain ⟨hgH, hgx, -, -, hdW, hrH, hrg, -⟩ := tuPartsG hl hX hxH h0 hxE
  have hrx : x % leWe (sgLW x) < x := hrg.trans_le (sgLW_le h0)
  have hTg := IH _ hgx hgH (hgx.trans hxE)
  have hTr := IH _ hrx hrH (hrx.trans hxE)
  have hOe : leOe (tdThL S l (sgLW x)) < veblen 1 (Om (1 : Ordinal.{0}) + 1) := by
    unfold leOe; conv_rhs => rw [← hfix]
    exact (opow_lt_opow_iff_right one_lt_omega0).2 (tuMul_lt_fix hfix hO hTg)
  have hΘd : gxTh (upsilon l) (ldAtR S l) (x / leWe (sgLW x)) < veblen 1 (Om (1 : Ordinal.{0}) + 1) :=
    (snTh_lt_Om1 hl hX hdW.le).trans hO
  rw [tuThG_cnf hl hX hxH h0 hxE]
  exact hp (tuMul_lt_fix hfix hOe hΘd) hTr

/-- `Θ̂_L x + 1 < Ĝ` for `x ∈ H_λ`, `x < ε`. -/
theorem tuThG_succ_Gh {x : Ordinal.{0}} (hxH : x ∈ cdHull S l) (hxE : x < veblen 1 (Om (1 + 1) + 1)) :
    tdThL S l x + 1 < veblen (Om 1) 1 :=
  (Ph.ph_veblen_prin _ _) ((tuThG_lt_epsh hl hX x hxH hxE).trans tuEpsh_lt_Gh) tuOne_Gh

/-- **`G + W^e·c` with the image `Ĝ + Ω^{Θ̂_L e}·Θ c` is a prefix** for every `1 ≤ e < ε` of `H_λ` and every code
`c < Ω₂`. -/
theorem tuPD_GG {e c : Ordinal.{0}} (heH : e ∈ cdHull S l) (he1 : 1 ≤ e) (heE : e < veblen 1 (Om (1 + 1) + 1))
    (hc : GxCl (upsilon l) (ldAtR S l) c) (hcW : c < Om (1 + 1)) :
    StPD S l (veblen (Om (1 + 1)) 1 + leWe e * c)
      (veblen (Om 1) 1 + leOe (tdThL S l e) * gxTh (upsilon l) (ldAtR S l) c) := by
  have he2 : e + 1 < veblen (Om (1 + 1)) 1 := (tuEps_lim.add_one_lt heE).trans tuEps_lt_G
  exact (tuStepLadG hl hX e heH he1 heE).2 _ _ (tnPD_G hl hX) (tuWe_G he2).2
    (tuOe_Gh (tuThG_succ_Gh hl hX heH heE)).2 c hc hcW

/-- **Every `x < ε` of the hull over a prefix `P`**: own data and the level statement of `P + x` with the image
`P̂ + Θ̂_L x`. -/
theorem tuLevXG : ∀ x, x ∈ cdHull S l → x < veblen 1 (Om (1 + 1) + 1) → ∀ P Ph, StPD S l P Ph →
    leWe (sgLW x + 1) ∣ P → leOe (tdThL S l (sgLW x) + 1) ∣ Ph →
    ScOwP S l (SnCL S (P + x)) (P + x) (Ph + tdThL S l x) ∧
      ScLev S l (SnCL S (P + x)) (P + x) (Ph + tdThL S l x) ∧ Ph + tdThL S l x < S.psi 0 (Om (1 + 1)) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have h1ρ : (1 : Ordinal.{0}) ≤ upsilon l := (gg_one_lt_of_SC hρSC).le
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hxH hxE P Ph hD hd hdh
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [add_zero, tjThL_zero, add_zero]; exact ⟨stOwP_img hD.img hD.hull hD.one, hD.lev, hD.ltG⟩
  have hpos : 0 < x := pos_iff_ne_zero.2 hx0
  obtain ⟨heH, hex, hqc, -, hqW, hrH, hr, hxdec⟩ := tuPartsG hl hX hxH hpos hxE
  set e := sgLW x with he_def
  have hWe : leWe e ≤ x := sgLW_le hpos
  have heE : e < veblen 1 (Om (1 + 1) + 1) := hex.trans hxE
  rcases eq_or_ne e 0 with he0 | he0
  · have hE2 : x < leWe e * Om (1 + 1) := by rw [← leWe_succ]; exact sgLW_lt x
    have hxW2 : x < Om (1 + 1) := by rw [he0, leWe_zero, one_mul] at hE2; exact hE2
    have hxc : GxCl (upsilon l) (ldAtR S l) x := (ldHull_iff hl hX hxW2).1 hxH
    rw [tuThL_small h1ρ hpos hxW2]
    exact ⟨stPreOwP hl hX hD hxc hxW2, stPreLev hl hX hD x hxc hxW2,
      rwG_SC.isPrincipal hD.ltG (tuTh_lt hl hX hxW2.le).2⟩
  have he1 : 1 ≤ e := Order.one_le_iff_ne_zero.2 he0
  have hD' := (tuStepLadG hl hX e heH he1 heE).2 P Ph hD hd hdh _ hqc hqW
  have hT : tdThL S l x = leOe (tdThL S l e) * gxTh (upsilon l) (ldAtR S l) (x / leWe e) +
      tdThL S l (x % leWe e) := tuThG_cnf hl hX hxH hpos hxE
  have eP : P + x = P + leWe e * (x / leWe e) + x % leWe e := by
    conv_lhs => rw [hxdec]
    rw [add_assoc]
  have eT : Ph + tdThL S l x = Ph + leOe (tdThL S l e) * gxTh (upsilon l) (ldAtR S l) (x / leWe e) +
      tdThL S l (x % leWe e) := by rw [hT, add_assoc]
  rw [eP, eT]
  rcases eq_or_ne (x % leWe e) 0 with hr0 | hr0
  · rw [hr0, add_zero, tjThL_zero, add_zero]; exact ⟨stOwP_img hD'.img hD'.hull hD'.one, hD'.lev, hD'.ltG⟩
  have hrx : x % leWe e < x := hr.trans_le hWe
  have hsr : sgLW (x % leWe e) < e := tuLogW_lt hr0 hr
  have hsrH : sgLW (x % leWe e) ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hrH)
  have hTlt := tuThG_lt hl hX hsrH heH heE hsr
  refine IH _ hrx hrH (hrx.trans hxE) _ _ hD' ?_ ?_
  · exact (leWe_dvd (Order.add_one_le_of_lt hsr)).trans
      (dvd_add ((leWe_dvd (le_self_add : e ≤ e + 1)).trans hd) (dvd_mul_right _ _))
  · exact (tuOe_dvd (Order.add_one_le_of_lt hTlt)).trans
      (dvd_add ((tuOe_dvd (le_self_add : tdThL S l e ≤ _ + 1)).trans hdh) (dvd_mul_right _ _))

/-- **Every level `G ≤ E < G + ε` of the hull is `G + x` with `x < ε` in the hull.** -/
theorem tuDecG {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hGE : veblen (Om (1 + 1)) 1 ≤ E) (hE : E < tuGE S) :
    ∃ x, E = veblen (Om (1 + 1)) 1 + x ∧ x ∈ cdHull S l ∧ x < veblen 1 (Om (1 + 1) + 1) := by
  obtain ⟨x, rfl⟩ := exists_add_of_le hGE
  have hxE : x < veblen 1 (Om (1 + 1) + 1) := (add_lt_add_iff_left _).1 hE
  have hdG := (tuWe_G tuEps_lt_G).2
  rw [tuWe_eps] at hdG
  refine ⟨x, rfl, snHullRem (K := veblen 1 (Om (1 + 1) + 1)) hEH (by rw [tuWe_eps]; exact hdG)
    (by rw [tuWe_eps]; exact hxE), hxE⟩

/-- **The data of a level `G + x`, `x < ε`.** -/
theorem tuLevGG {x : Ordinal.{0}} (hxH : x ∈ cdHull S l) (hxE : x < veblen 1 (Om (1 + 1) + 1)) :
    ScOwP S l (SnCL S (veblen (Om (1 + 1)) 1 + x)) (veblen (Om (1 + 1)) 1 + x) (veblen (Om 1) 1 + tdThL S l x) ∧
      ScLev S l (SnCL S (veblen (Om (1 + 1)) 1 + x)) (veblen (Om (1 + 1)) 1 + x) (veblen (Om 1) 1 + tdThL S l x) ∧
      veblen (Om 1) 1 + tdThL S l x < S.psi 0 (Om (1 + 1)) := by
  have hsH : sgLW x ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hxH)
  have hsE : sgLW x < veblen 1 (Om (1 + 1) + 1) := by
    rcases eq_or_ne x 0 with rfl | hx0
    · unfold sgLW; rw [Ordinal.log_zero_right, Ordinal.zero_div]; exact tuEps_lim.bot_lt
    exact (tuSg_lt (pos_iff_ne_zero.2 hx0) hxE).trans hxE
  have hs2 : sgLW x + 1 < veblen (Om (1 + 1)) 1 := (tuEps_lim.add_one_lt hsE).trans tuEps_lt_G
  exact tuLevXG hl hX x hxH hxE _ _ (tnPD_G hl hX) (tuWe_G hs2).2 (tuOe_Gh (tuThG_succ_Gh hl hX hsH hsE)).2

/-- **THE LEVEL SYSTEM UP TO `G + ε_{Ω₂+1}`.** -/
theorem tuLSG : StLS S l (tuGE S) (tuTh S) := by
  have hT := tjLS (S := S) hl hX
  refine ⟨tuGE_lim, tuGE_lt_G3, ?_, ?_, ?_⟩
  · intro E hEH h1 hE
    rcases lt_or_ge E (veblen (Om (1 + 1)) 1) with hlt | hge
    · rw [tuThE_lt hlt]; exact hT.ltG E hEH h1 hlt
    · obtain ⟨x, rfl, hxH, hxE⟩ := tuDecG hl hX hEH hge hE
      rw [tuThE_ge]; exact (tuLevGG hl hX hxH hxE).2.2
  · intro E hEH h1 hE
    rcases lt_or_ge E (veblen (Om (1 + 1)) 1) with hlt | hge
    · rw [tuThE_lt hlt]; exact hT.own E hEH h1 hlt
    · obtain ⟨x, rfl, hxH, hxE⟩ := tuDecG hl hX hEH hge hE
      rw [tuThE_ge]; exact (tuLevGG hl hX hxH hxE).1
  · intro E hEH h1 hE
    rcases lt_or_ge E (veblen (Om (1 + 1)) 1) with hlt | hge
    · rw [tuThE_lt hlt]; exact hT.lev E hEH h1 hlt
    · obtain ⟨x, rfl, hxH, hxE⟩ := tuDecG hl hX hEH hge hE
      rw [tuThE_ge]; exact (tuLevGG hl hX hxH hxE).2.1

end Main

section Move

variable {n : ℕ} {l l' ηx ηx' : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hl' : IsRestartIdx l') (hX' : upsilon l' < Pv S ηx')

include hl hX hl' hX'

/-- **THE MOVE OF THE LEVEL SYSTEM UP TO `G + ε_{Ω₂+1}`.** -/
theorem tuLSBG : StLSB S n l l' (tuGE S) (tuTh S) := by
  intro B hBSC hGB IHm E hEH h1 hE hEcl
  obtain ⟨hDε, hBε⟩ := tjB_G (S := S) (n := n)
  obtain ⟨hDεh, hBεh⟩ := tnB_Gh (S := S) (n := n)
  have hGB_G : veblen (Om (1 + 1)) 1 ≤ tuGE S := le_self_add
  rcases lt_or_ge E (veblen (Om (1 + 1)) 1) with hlt | hge
  · obtain ⟨hDE, hDE2, hBE2, hBEε, hBEH, hBcl, hDT, hDΘ1, hBΘ1, hΘmove⟩ :=
      tjB_thH hl hX hl' hX' hBSC IHm E hEH hlt hEcl
    refine ⟨hDE, hDE2, hBE2, hBEε.trans_le hGB_G, hBEH, hBcl, ?_, ?_, ?_, ?_⟩
    · rw [tuThE_lt hlt]; exact hDT
    · rw [tuThE_lt hlt]; exact hDΘ1
    · rw [tuThE_lt hlt]; exact hBΘ1
    · rw [tuThE_lt hlt, tuThE_lt hBEε]; exact hΘmove
  obtain ⟨x, rfl, hxH, hxE⟩ := tuDecG hl hX hEH hge hE
  set G := veblen (Om (1 + 1 : Ordinal.{0})) 1 with hG_def
  set Gh := veblen (Om (1 : Ordinal.{0})) 1 with hGh_def
  have hxG : x < G := hxE.trans tuEps_lt_G
  have hxB : LeCl (Om (1 + 1)) B x := by
    have h := (leClDec hBSC ldOm2_SC _ hEcl).1 _ (tnG_cl hBSC) le_self_add
    rwa [Ordinal.add_sub_cancel] at h
  obtain ⟨hDx, hDx2, hBx2, -, hBxH, hBxcl, hDT, hDΘ1, hBΘ1, hΘmove⟩ :=
    tjB_thH hl hX hl' hX' hBSC IHm x hxH hxG hxB
  obtain ⟨hDE, hBE⟩ := mvB_add (k := n) hDε hDx
  rw [hBε] at hBE
  have e2 : ∀ z, Om (1 + 1) * (G + z) = G + Om (1 + 1) * z := fun z => by rw [mul_add, tnK_mul_G]
  have e2h : ∀ z, Om 1 * (Gh + z) = Gh + Om 1 * z := fun z => by rw [mul_add, tnK_mul_Gh]
  obtain ⟨hDE2, hBE2⟩ := mvB_add (k := n) hDε hDx2
  rw [hBε, hBx2] at hBE2
  obtain ⟨hDe, hBe⟩ := sjB_eps (S := S) (n := n)
  have hBxE : Bc.bcB S n x < veblen 1 (Om (1 + 1) + 1) := by
    have h := (mvB_lt_iff (k := n) hDx hDe).2 hxE; rwa [hBe] at h
  obtain ⟨hDTh, hBTh⟩ := mvB_add (k := n) hDεh hDT
  rw [hBεh] at hBTh
  obtain ⟨hDTh2, hBTh2⟩ := mvB_add (k := n) hDεh hDΘ1
  rw [hBεh, hBΘ1] at hBTh2
  refine ⟨hDE, by rw [e2]; exact hDE2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e2, hBE2, hBE, e2]
  · rw [hBE]; exact (add_lt_add_iff_left G).2 hBxE
  · rw [hBE]; exact CSet.add_mem tnG_mem hBxH
  · intro hDB Q hQ hQ'
    rw [hBE]
    exact LeCl.add (tnG_cl hQ) (hBxcl hDB Q hQ hQ')
  · rw [tuThE_ge]; exact hDTh
  · rw [tuThE_ge, e2h]; exact hDTh2
  · rw [tuThE_ge, e2h, hBTh2, hBTh, e2h]
  · rw [hBE, tuThE_ge, tuThE_ge, hΘmove, hBTh]

end Move

/-- **Every atom `ψ_{Ω₂}(0) < s < ψ_{Ω₂}(W^{W^{G + ε}})` moves** once the codes below it move. -/
theorem tuAtMoveTopG {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
    (s : Ordinal.{0}) (hs : s ∈ ldAtR S l) (hs0 : S.psi 0 (Om (1 + 1)) < s)
    (hsT : s < S.psi (leWe (leWe (tuGE S))) (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) :=
  stAtMoveG (fun _ _ hl hX => tuLSG hl hX) (fun _ _ _ _ _ hl hX hl' hX' => tuLSBG hl hX hl' hX')
    hR h1 hr hl' hB s hs hs0 hsT IH

/-- `ψ_{Ω₂}(W^{W^{G + Ω₂^{Ω₂^{Ω₂}}}}) ≤ ψ_{Ω₂}(W^{W^{G + ε}})`. -/
theorem tuFE_le :
    S.psi (leWe (leWe (tuGV S))) (Om (1 + 1)) ≤ S.psi (leWe (leWe (tuGE S))) (Om (1 + 1)) :=
  (psi_mono (S := S) (InR_Om_succ 1) (leWe_mono (leWe_mono tuGV_le_GE))).1

/-- **`LjAtMove` for the atoms `ψ_{Ω₂}(W^{W^{G + ε_{Ω₂+1}}}) ≤ s ≤ θ`.** -/
def TuAtMove21 (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    leFWW S ≤ cdCode S l → cdCode S l < ljThP S →
    ∀ s ∈ ldAtR S l, S.psi (leWe (leWe (tuGE S))) (Om (1 + 1)) ≤ s → s ≤ ConjT.th S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)

/-- **`TuAtMove21` gives `TuAtMove20`.** -/
theorem tuAtMove20_of21 (h : TuAtMove21 S) : TuAtMove20 S := by
  intro n l l' hR h1 hr hl' hB hm hF hK s hs hsT hsθ IH
  rcases lt_or_ge s (S.psi (leWe (leWe (tuGE S))) (Om (1 + 1))) with hlt | hge
  · have hs0 : S.psi 0 (Om (1 + 1)) < s :=
      (psi_lt_psi_of_mem (InR_Om_succ 1) tjG_lim.bot_lt (CSet.zero_mem _ _)).trans_le
        (tnG_le_FN.trans (tuFN_le.trans (tuFU_le.trans hsT)))
    exact tuAtMoveTopG hR h1 hr hl' hB s hs hs0 hlt IH
  · exact h n l l' hR h1 hr hl' hB hm hF hK s hs hge hsθ IH

/-- **`TuAtMove20` gives `TuAtMove21`.** -/
theorem tuAtMove21_of20 (h : TuAtMove20 S) : TuAtMove21 S :=
  fun n l l' hR h1 hr hl' hB hm hF hK s hs hsT hsθ IH =>
    h n l l' hR h1 hr hl' hB hm hF hK s hs (tuFE_le.trans hsT) hsθ IH

/-- **`TuAtMove21` gives `Tj.TjAtMove17`.** -/
theorem tuAtMove17_of21 (h : TuAtMove21 S) : TjAtMove17 S := tuAtMove17_of20 (tuAtMove20_of21 h)

/-- **The road with `TuAtMove21`, `Rn.RnThMoveM` and `Rn.RnEQhi2`** (each under `L(ω+1) ≤ ν_C`). -/
theorem tuRoadG (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (hat : Nc.ncL S (ω + 1) ≤ nuC → TuAtMove21 S)
    (hM : Nc.ncL S (ω + 1) ≤ nuC → RnThMoveM S) (hhi : Nc.ncL S (ω + 1) ≤ nuC → RnEQhi2 S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  tuRoadX hU hO hL hV hN hlh (fun hν => tuAtMove20_of21 (hat hν)) hM hhi

/-- **Satisfiability**: the hypothesis of `tuRoadG` follows from that of `Tn.tnRoadL`. -/
theorem tuRoadG_hyps (hat : Nc.ncL S (ω + 1) ≤ nuC → TnAtMove18 S) :
    Nc.ncL S (ω + 1) ≤ nuC → TuAtMove21 S :=
  fun hν => tuAtMove21_of20 (tuAtMove20_of19 (tuAtMove19_of18 (hat hν)))

end Googology.Trans.PoR.InaccPsi.R2.Tu

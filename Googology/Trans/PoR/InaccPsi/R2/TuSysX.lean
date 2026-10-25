import Googology.Trans.PoR.InaccPsi.R2.TuStepY

/-!
# The level system up to `G + Ω₂^{Ω₂^{Ω₂}}` (`G = φ(Ω₂, 1)`), its move under `B_n`, and the road

`B_n = Bc.bcB S n`, `Θ = gxTh ρ_λ (ldAtR λ)`, `Θ̂_L = Td.tdThL`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `G = φ(Ω₂, 1)`,
`Ĝ = φ(Ω₁, 1)`, the image `Tu.tuTh` (`Θ̂_L E` below `G`, `Ĝ + Θ̂_L x` at `G + x`),
`F_V = ψ_{Ω₂}(W^{W^{G + W^{W^{Ω₂}}}})`.

`tuGV S = G + W^{W^{Ω₂}}` (the bound).

* `tuWWW_G`, `tuGV_lt_G3`, `tuGV_lim`, `tuB_WWW` (`B_n W^{W^{Ω₂}} = W^{W^{Ω₂}}`), `tuWe_gt` (`e < W^e` below
  `W^{Ω₂}`);
* `tuLevXX` (**every `x < W^{W^{Ω₂}}` of the hull over a prefix `P`** (`W^{log_W x + 1} ∣ P`): own data and the level
  statement of `P + x` with the image `P̂ + Θ̂_L x`; the prefixes `P + W^e·c` of `Tu.tuStepLadAll`), `tuPD_GX`
  (**`G + W^e·c` is a prefix for every `1 ≤ e < W^{Ω₂}` of `H_λ` and every code `c < Ω₂`**);
* `tuLSX` (**THE LEVEL SYSTEM UP TO `G + Ω₂^{Ω₂^{Ω₂}}`**), `tuLSBX` (**ITS MOVE**);
* `tuAtMoveTopX` (**every atom `ψ_{Ω₂}(0) < s < F_V` moves** once the codes below it move), `TuAtMove20 S` (a
  hypothesis name: the move of the atoms `F_V ≤ s ≤ θ`), `tuAtMove19_of20`, `tuAtMove20_of19`,
  `tuAtMove17_of20`, `tuRoadX` (**the road**), `tuRoadX_hyps`.

No new axiom.  New definitions: `tuGV`, the hypothesis name `TuAtMove20`.
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

/-- **The bound `G + Ω₂^{Ω₂^{Ω₂}}` of the level system.** -/
noncomputable def tuGV (_S : InaccSeq.{0}) : Ordinal.{0} := veblen (Om (1 + 1)) 1 + leWe (leWe (Om (1 + 1)))

/-- `W^{W^{Ω₂}} < G`, `W^{W^{Ω₂}} ∣ G`. -/
theorem tuWWW_G : leWe (leWe (Om (1 + 1 : Ordinal.{0}))) < veblen (Om (1 + 1)) 1 ∧
    leWe (leWe (Om (1 + 1 : Ordinal.{0}))) ∣ veblen (Om (1 + 1)) 1 := tuWe_G tuWW_G.1

theorem tuGV_lt_G3 : tuGV S < S.psi 0 (Om (1 + 1 + 1)) :=
  rwG3_SC.isPrincipal tjG_lt_G3 (tuWWW_G.1.trans tjG_lt_G3)

theorem tuGV_lim : IsSuccLimit (tuGV S) :=
  isSuccLimit_add _ (Ph.ph_opow_lim (mul_ne_zero ldOm2_SC.1.ne' (leWe_pos _).ne'))

/-- `G + Ω₂^{Ω₂} ≤ G + Ω₂^{Ω₂^{Ω₂}}`. -/
theorem tuGB_le_GV : tuGB S ≤ tuGV S :=
  (add_le_add_iff_left _).2 (leWe_mono (tnLe_We _))

/-- `e < W^e` for `e < W^{Ω₂}`. -/
theorem tuWe_gt {e : Ordinal.{0}} (he : e < leWe (Om (1 + 1))) : e < leWe e := by
  rcases lt_or_ge e (Om (1 + 1)) with hlt | hge
  · rcases eq_or_ne e 0 with rfl | he0
    · rw [leWe_zero]; exact zero_lt_one
    · exact hlt.trans_le (by rw [← leWe_one]; exact leWe_mono (Order.one_le_iff_ne_zero.2 he0))
  · exact he.trans_le (leWe_mono hge)

/-- **`B_n W^{W^{Ω₂}} = W^{W^{Ω₂}}`.** -/
theorem tuB_WWW {n : ℕ} : MvD S (leWe (leWe (Om (1 + 1)))) ∧
    Bc.bcB S n (leWe (leWe (Om (1 + 1)))) = leWe (leWe (Om (1 + 1))) := by
  obtain ⟨hDW, hBW⟩ := rnB_WW (S := S) (n := n)
  have eWW : Om (1 + 1 : Ordinal.{0}) * leWe (Om (1 + 1)) = leWe (Om (1 + 1)) := by
    rw [rvWe_mul, Ordinal.one_add_of_omega0_le (Lw.lw_omega_lt_SC ldOm2_SC).le]
  have e2 : leWe (leWe (Om (1 + 1))) = ω ^ leWe (Om (1 + 1)) := by
    show ω ^ (Om (1 + 1) * leWe (Om (1 + 1))) = ω ^ leWe (Om (1 + 1)); rw [eWW]
  obtain ⟨hD, hB⟩ := ldB_opow (n := n) hDW
  rw [hBW] at hB
  rw [e2]; exact ⟨hD, hB⟩

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

omit hl hX in
theorem tuWW_lim : IsSuccLimit (leWe (Om (1 + 1 : Ordinal.{0}))) :=
  Ph.ph_opow_lim (mul_ne_zero ldOm2_SC.1.ne' ldOm2_SC.1.ne')

omit hl hX in
theorem tuOne_Gh : (1 : Ordinal.{0}) < veblen (Om 1) 1 :=
  (gg_one_lt_of_SC Ph.ph_SC_Om1).trans ((lt_add_one _).trans tnOm1_lt_Gh)

omit hl hX in
theorem tuOO_Gh : leOe (Om (1 : Ordinal.{0})) < veblen (Om 1) 1 :=
  (tuOe_Gh ((lt_add_one _).trans tnOm1_lt_Gh)).1

/-- **`G + W^e·c` with the image `Ĝ + Ω^{Θ̂_L e}·Θ c` is a prefix** for every `1 ≤ e < W^{Ω₂}` of `H_λ` and every
code `c < Ω₂`. -/
theorem tuPD_GX {e c : Ordinal.{0}} (heH : e ∈ cdHull S l) (he1 : 1 ≤ e) (heW : e < leWe (Om (1 + 1)))
    (hc : GxCl (upsilon l) (ldAtR S l) c) (hcW : c < Om (1 + 1)) :
    StPD S l (veblen (Om (1 + 1)) 1 + leWe e * c)
      (veblen (Om 1) 1 + leOe (tdThL S l e) * gxTh (upsilon l) (ldAtR S l) c) := by
  have he2 : e + 1 < veblen (Om (1 + 1)) 1 := (tuWW_lim.add_one_lt heW).trans tuWW_G.1
  have hΘ : tdThL S l e + 1 < veblen (Om 1) 1 :=
    (Ph.ph_veblen_prin _ _) ((tuThX_lt_OO hl hX heH heW).trans tuOO_Gh) tuOne_Gh
  exact (tuStepLadAll hl hX heH he1 heW).2 _ _ (tnPD_G hl hX) (tuWe_G he2).2 (tuOe_Gh hΘ).2 c hc hcW

/-- **Every `x < W^{W^{Ω₂}}` of the hull over a prefix `P`**: own data and the level statement of `P + x` with the
image `P̂ + Θ̂_L x`. -/
theorem tuLevXX : ∀ x, x ∈ cdHull S l → x < leWe (leWe (Om (1 + 1))) → ∀ P Ph, StPD S l P Ph →
    leWe (sgLW x + 1) ∣ P → leOe (tdThL S l (sgLW x) + 1) ∣ Ph →
    ScOwP S l (SnCL S (P + x)) (P + x) (Ph + tdThL S l x) ∧
      ScLev S l (SnCL S (P + x)) (P + x) (Ph + tdThL S l x) ∧ Ph + tdThL S l x < S.psi 0 (Om (1 + 1)) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have h1ρ : (1 : Ordinal.{0}) ≤ upsilon l := (gg_one_lt_of_SC hρSC).le
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hxH hxW P Ph hD hd hdh
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [add_zero, tjThL_zero, add_zero]; exact ⟨stOwP_img hD.img hD.hull hD.one, hD.lev, hD.ltG⟩
  have hpos : 0 < x := pos_iff_ne_zero.2 hx0
  set e := sgLW x with he_def
  have hWe : leWe e ≤ x := sgLW_le hpos
  have heW : e < leWe (Om (1 + 1)) := by
    by_contra hc; push Not at hc
    exact absurd ((leWe_mono hc).trans hWe) (not_le.2 hxW)
  have heH : e ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hxH)
  have hW0 : leWe e ≠ 0 := (leWe_pos e).ne'
  have hrH : x % leWe e ∈ cdHull S l := leModP_mem (Om (1 + 1) * e) hxH
  have hr : x % leWe e < leWe e := Ordinal.mod_lt _ hW0
  have hE2 : x < leWe e * Om (1 + 1) := by rw [← leWe_succ]; exact sgLW_lt x
  have hqW : x / leWe e < Om (1 + 1) := (Ordinal.lt_mul_iff_div_lt hW0).1 hE2
  have hqH : x / leWe e ∈ cdHull S l := by
    refine leDivOp_mem (K := Om (1 + 1) * e) (dvd_mul_right _ _) hxH ?_
    have : leWe (e + 1) = ω ^ (Om (1 + 1) * e + Om (1 + 1)) := by unfold leWe; rw [mul_add_one]
    rw [← this]; exact sgLW_lt x
  have hqc : GxCl (upsilon l) (ldAtR S l) (x / leWe e) := (ldHull_iff hl hX hqW).1 hqH
  have hxdec : x = leWe e * (x / leWe e) + x % leWe e := (Ordinal.div_add_mod x (leWe e)).symm
  rcases eq_or_ne e 0 with he0 | he0
  · have hxW2 : x < Om (1 + 1) := by rw [he0, leWe_zero, one_mul] at hE2; exact hE2
    have hxc : GxCl (upsilon l) (ldAtR S l) x := (ldHull_iff hl hX hxW2).1 hxH
    rw [tuThL_small h1ρ hpos hxW2]
    exact ⟨stPreOwP hl hX hD hxc hxW2, stPreLev hl hX hD x hxc hxW2,
      rwG_SC.isPrincipal hD.ltG (tuTh_lt hl hX hxW2.le).2⟩
  have he1 : 1 ≤ e := Order.one_le_iff_ne_zero.2 he0
  have hD' := (tuStepLadAll hl hX heH he1 heW).2 P Ph hD hd hdh _ hqc hqW
  have hex : e < x := (tuWe_gt heW).trans_le hWe
  have hxG : x < veblen (Om (1 + 1)) 1 := hxW.trans tuWWW_G.1
  have hrw : TgWF S l (taTm (x % leWe e)) := (tgTm_spec hl hX _ hrH ((hr.trans_le hWe).trans hxG)).1
  have hT : tdThL S l x = leOe (tdThL S l e) * gxTh (upsilon l) (ldAtR S l) (x / leWe e) +
      tdThL S l (x % leWe e) := by
    rw [tjThL_cnf h1ρ ⟨hpos, hex⟩ hrw]
  have eP : P + x = P + leWe e * (x / leWe e) + x % leWe e := by
    conv_lhs => rw [hxdec]
    rw [add_assoc]
  have eT : Ph + tdThL S l x = Ph + leOe (tdThL S l e) * gxTh (upsilon l) (ldAtR S l) (x / leWe e) +
      tdThL S l (x % leWe e) := by rw [hT, add_assoc]
  rw [eP, eT]
  rcases eq_or_ne (x % leWe e) 0 with hr0 | hr0
  · rw [hr0, add_zero, tjThL_zero, add_zero]; exact ⟨stOwP_img hD'.img hD'.hull hD'.one, hD'.lev, hD'.ltG⟩
  have hrx : x % leWe e < x := hr.trans_le hWe
  have hsr : sgLW (x % leWe e) < e := by
    by_contra hc; push Not at hc
    exact absurd ((leWe_mono hc).trans (sgLW_le (pos_iff_ne_zero.2 hr0))) (not_le.2 hr)
  have hsrH : sgLW (x % leWe e) ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hrH)
  have hTlt := tuThX_lt hl hX _ hsrH e heH heW hsr
  refine IH _ hrx hrH (hrx.trans hxW) _ _ hD' ?_ ?_
  · exact (leWe_dvd (Order.add_one_le_of_lt hsr)).trans
      (dvd_add ((leWe_dvd (le_self_add : e ≤ e + 1)).trans hd) (dvd_mul_right _ _))
  · exact (tuOe_dvd (Order.add_one_le_of_lt hTlt)).trans
      (dvd_add ((tuOe_dvd (le_self_add : tdThL S l e ≤ _ + 1)).trans hdh) (dvd_mul_right _ _))

/-- **Every level `G ≤ E < G + W^{W^{Ω₂}}` of the hull is `G + x` with `x < W^{W^{Ω₂}}` in the hull.** -/
theorem tuDecX {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hGE : veblen (Om (1 + 1)) 1 ≤ E) (hE : E < tuGV S) :
    ∃ x, E = veblen (Om (1 + 1)) 1 + x ∧ x ∈ cdHull S l ∧ x < leWe (leWe (Om (1 + 1))) := by
  obtain ⟨x, rfl⟩ := exists_add_of_le hGE
  have hxW : x < leWe (leWe (Om (1 + 1))) := (add_lt_add_iff_left _).1 hE
  exact ⟨x, rfl, snHullRem hEH tuWWW_G.2 hxW, hxW⟩

/-- **The data of a level `G + x`, `x < W^{W^{Ω₂}}`.** -/
theorem tuLevGX {x : Ordinal.{0}} (hxH : x ∈ cdHull S l) (hxW : x < leWe (leWe (Om (1 + 1)))) :
    ScOwP S l (SnCL S (veblen (Om (1 + 1)) 1 + x)) (veblen (Om (1 + 1)) 1 + x) (veblen (Om 1) 1 + tdThL S l x) ∧
      ScLev S l (SnCL S (veblen (Om (1 + 1)) 1 + x)) (veblen (Om (1 + 1)) 1 + x) (veblen (Om 1) 1 + tdThL S l x) ∧
      veblen (Om 1) 1 + tdThL S l x < S.psi 0 (Om (1 + 1)) := by
  have hsW : sgLW x < leWe (Om (1 + 1)) := by
    rcases eq_or_ne x 0 with rfl | hx0
    · unfold sgLW; rw [Ordinal.log_zero_right, Ordinal.zero_div]; exact leWe_pos _
    by_contra hc; push Not at hc
    exact absurd ((leWe_mono hc).trans (sgLW_le (pos_iff_ne_zero.2 hx0))) (not_le.2 hxW)
  have hsH : sgLW x ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hxH)
  have hs2 : sgLW x + 1 < veblen (Om (1 + 1)) 1 := (tuWW_lim.add_one_lt hsW).trans tuWW_G.1
  have hΘ : tdThL S l (sgLW x) + 1 < veblen (Om 1) 1 :=
    (Ph.ph_veblen_prin _ _) ((tuThX_lt_OO hl hX hsH hsW).trans tuOO_Gh) tuOne_Gh
  exact tuLevXX hl hX x hxH hxW _ _ (tnPD_G hl hX) (tuWe_G hs2).2 (tuOe_Gh hΘ).2

/-- **THE LEVEL SYSTEM UP TO `G + Ω₂^{Ω₂^{Ω₂}}`.** -/
theorem tuLSX : StLS S l (tuGV S) (tuTh S) := by
  have hT := tjLS (S := S) hl hX
  refine ⟨tuGV_lim, tuGV_lt_G3, ?_, ?_, ?_⟩
  · intro E hEH h1 hE
    rcases lt_or_ge E (veblen (Om (1 + 1)) 1) with hlt | hge
    · rw [tuThE_lt hlt]; exact hT.ltG E hEH h1 hlt
    · obtain ⟨x, rfl, hxH, hxW⟩ := tuDecX hl hX hEH hge hE
      rw [tuThE_ge]; exact (tuLevGX hl hX hxH hxW).2.2
  · intro E hEH h1 hE
    rcases lt_or_ge E (veblen (Om (1 + 1)) 1) with hlt | hge
    · rw [tuThE_lt hlt]; exact hT.own E hEH h1 hlt
    · obtain ⟨x, rfl, hxH, hxW⟩ := tuDecX hl hX hEH hge hE
      rw [tuThE_ge]; exact (tuLevGX hl hX hxH hxW).1
  · intro E hEH h1 hE
    rcases lt_or_ge E (veblen (Om (1 + 1)) 1) with hlt | hge
    · rw [tuThE_lt hlt]; exact hT.lev E hEH h1 hlt
    · obtain ⟨x, rfl, hxH, hxW⟩ := tuDecX hl hX hEH hge hE
      rw [tuThE_ge]; exact (tuLevGX hl hX hxH hxW).2.1

end Main


section Move

variable {n : ℕ} {l l' ηx ηx' : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hl' : IsRestartIdx l') (hX' : upsilon l' < Pv S ηx')

include hl hX hl' hX'

/-- **THE MOVE OF THE LEVEL SYSTEM UP TO `G + Ω₂^{Ω₂^{Ω₂}}`.** -/
theorem tuLSBX : StLSB S n l l' (tuGV S) (tuTh S) := by
  intro B hBSC hGB IHm E hEH h1 hE hEcl
  obtain ⟨hDε, hBε⟩ := tjB_G (S := S) (n := n)
  obtain ⟨hDεh, hBεh⟩ := tnB_Gh (S := S) (n := n)
  have hGB_G : veblen (Om (1 + 1)) 1 ≤ tuGV S := le_self_add
  rcases lt_or_ge E (veblen (Om (1 + 1)) 1) with hlt | hge
  · obtain ⟨hDE, hDE2, hBE2, hBEε, hBEH, hBcl, hDT, hDΘ1, hBΘ1, hΘmove⟩ :=
      tjB_thH hl hX hl' hX' hBSC IHm E hEH hlt hEcl
    refine ⟨hDE, hDE2, hBE2, hBEε.trans_le hGB_G, hBEH, hBcl, ?_, ?_, ?_, ?_⟩
    · rw [tuThE_lt hlt]; exact hDT
    · rw [tuThE_lt hlt]; exact hDΘ1
    · rw [tuThE_lt hlt]; exact hBΘ1
    · rw [tuThE_lt hlt, tuThE_lt hBEε]; exact hΘmove
  obtain ⟨x, rfl, hxH, hxW⟩ := tuDecX hl hX hEH hge hE
  set G := veblen (Om (1 + 1 : Ordinal.{0})) 1 with hG_def
  set Gh := veblen (Om (1 : Ordinal.{0})) 1 with hGh_def
  have hxG : x < G := hxW.trans tuWWW_G.1
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
  obtain ⟨hDWW, hBWW⟩ := tuB_WWW (S := S) (n := n)
  have hBxW : Bc.bcB S n x < leWe (leWe (Om (1 + 1))) := by
    have h := (mvB_lt_iff (k := n) hDx hDWW).2 hxW; rwa [hBWW] at h
  obtain ⟨hDTh, hBTh⟩ := mvB_add (k := n) hDεh hDT
  rw [hBεh] at hBTh
  obtain ⟨hDTh2, hBTh2⟩ := mvB_add (k := n) hDεh hDΘ1
  rw [hBεh, hBΘ1] at hBTh2
  refine ⟨hDE, by rw [e2]; exact hDE2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e2, hBE2, hBE, e2]
  · rw [hBE]; exact (add_lt_add_iff_left G).2 hBxW
  · rw [hBE]; exact CSet.add_mem tnG_mem hBxH
  · intro hDB Q hQ hQ'
    rw [hBE]
    exact LeCl.add (tnG_cl hQ) (hBxcl hDB Q hQ hQ')
  · rw [tuThE_ge]; exact hDTh
  · rw [tuThE_ge, e2h]; exact hDTh2
  · rw [tuThE_ge, e2h, hBTh2, hBTh, e2h]
  · rw [hBE, tuThE_ge, tuThE_ge, hΘmove, hBTh]

end Move

/-- **Every atom `ψ_{Ω₂}(0) < s < ψ_{Ω₂}(W^{W^{G + W^{W^{Ω₂}}}})` moves** once the codes below it move. -/
theorem tuAtMoveTopX {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
    (s : Ordinal.{0}) (hs : s ∈ ldAtR S l) (hs0 : S.psi 0 (Om (1 + 1)) < s)
    (hsT : s < S.psi (leWe (leWe (tuGV S))) (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) :=
  stAtMoveG (fun _ _ hl hX => tuLSX hl hX) (fun _ _ _ _ _ hl hX hl' hX' => tuLSBX hl hX hl' hX')
    hR h1 hr hl' hB s hs hs0 hsT IH

/-- `ψ_{Ω₂}(W^{W^{G + Ω₂^{Ω₂}}}) ≤ ψ_{Ω₂}(W^{W^{G + Ω₂^{Ω₂^{Ω₂}}}})`. -/
theorem tuFU_le :
    S.psi (leWe (leWe (tuGB S))) (Om (1 + 1)) ≤ S.psi (leWe (leWe (tuGV S))) (Om (1 + 1)) :=
  (psi_mono (S := S) (InR_Om_succ 1) (leWe_mono (leWe_mono tuGB_le_GV))).1

/-- **`LjAtMove` for the atoms `ψ_{Ω₂}(W^{W^{G + Ω₂^{Ω₂^{Ω₂}}}}) ≤ s ≤ θ`.** -/
def TuAtMove20 (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    leFWW S ≤ cdCode S l → cdCode S l < ljThP S →
    ∀ s ∈ ldAtR S l, S.psi (leWe (leWe (tuGV S))) (Om (1 + 1)) ≤ s → s ≤ ConjT.th S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)

/-- **`TuAtMove20` gives `TuAtMove19`.** -/
theorem tuAtMove19_of20 (h : TuAtMove20 S) : TuAtMove19 S := by
  intro n l l' hR h1 hr hl' hB hm hF hK s hs hsT hsθ IH
  rcases lt_or_ge s (S.psi (leWe (leWe (tuGV S))) (Om (1 + 1))) with hlt | hge
  · have hs0 : S.psi 0 (Om (1 + 1)) < s :=
      (psi_lt_psi_of_mem (InR_Om_succ 1) tjG_lim.bot_lt (CSet.zero_mem _ _)).trans_le
        (tnG_le_FN.trans (tuFN_le.trans hsT))
    exact tuAtMoveTopX hR h1 hr hl' hB s hs hs0 hlt IH
  · exact h n l l' hR h1 hr hl' hB hm hF hK s hs hge hsθ IH

/-- **`TuAtMove19` gives `TuAtMove20`.** -/
theorem tuAtMove20_of19 (h : TuAtMove19 S) : TuAtMove20 S :=
  fun n l l' hR h1 hr hl' hB hm hF hK s hs hsT hsθ IH =>
    h n l l' hR h1 hr hl' hB hm hF hK s hs (tuFU_le.trans hsT) hsθ IH

/-- **`TuAtMove20` gives `Tj.TjAtMove17`.** -/
theorem tuAtMove17_of20 (h : TuAtMove20 S) : TjAtMove17 S := tuAtMove17_of19 (tuAtMove19_of20 h)

/-- **The road with `TuAtMove20`, `Rn.RnThMoveM` and `Rn.RnEQhi2`** (each under `L(ω+1) ≤ ν_C`). -/
theorem tuRoadX (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (hat : Nc.ncL S (ω + 1) ≤ nuC → TuAtMove20 S)
    (hM : Nc.ncL S (ω + 1) ≤ nuC → RnThMoveM S) (hhi : Nc.ncL S (ω + 1) ≤ nuC → RnEQhi2 S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  tuRoadL hU hO hL hV hN hlh (fun hν => tuAtMove19_of20 (hat hν)) hM hhi

/-- **Satisfiability**: the hypothesis of `tuRoadX` follows from that of `Tu.tuRoadL`. -/
theorem tuRoadX_hyps (hat : Nc.ncL S (ω + 1) ≤ nuC → TuAtMove19 S) :
    Nc.ncL S (ω + 1) ≤ nuC → TuAtMove20 S :=
  fun hν => tuAtMove20_of19 (hat hν)

end Googology.Trans.PoR.InaccPsi.R2.Tu

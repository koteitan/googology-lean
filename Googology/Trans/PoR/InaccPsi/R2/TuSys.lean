import Googology.Trans.PoR.InaccPsi.R2.TuStep

/-!
# The level system up to `G + Ω₂^{Ω₂}` (`G = φ(Ω₂, 1)`) and its move under `B_n`

`B_n = Bc.bcB S n`, `Θ = gxTh ρ_λ (ldAtR λ)`, `Θ̂_L = Td.tdThL`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `G = φ(Ω₂, 1)`,
`Ĝ = φ(Ω₁, 1)`.

`tuGB S = G + W^{Ω₂}` (the bound), `tuTh S λ E` (**the image of a level**): `Θ̂_L E` for `E < G` and `Ĝ + Θ̂_L x` for
`E = G + x`.

* `tuThL_small` (`Θ̂_L c = Θ c` for `0 < c < Ω₂`), `tuThL_cnf` (`Θ̂_L(W^e·c + r) = Ω^{Θ e}·Θ c + Θ̂_L r` at the
  base-`Ω₂` normal form of `x < W^{Ω₂}`);
* `tuPD_G` (**`G + W^e·c` with the image `Ĝ + Ω^{Θ e}·Θ c` is a prefix for all codes `1 ≤ e < Ω₂`, `c < Ω₂`**),
  `tuPD_Gk` (**`G + Ω₂^k·c` for every `1 ≤ k < ω`**), `tuPD_Gw` (**`G + Ω₂^ω`**);
* `tuLevX` (**every `x < W^{Ω₂}` of the hull over a prefix `P`** (`W^{log_W x + 1} ∣ P`): own data, the level
  statement of `P + x` with the image `P̂ + Θ̂_L x`; one induction on `x` along its base-`Ω₂` normal form);
* `tuLS` (**THE LEVEL SYSTEM UP TO `G + Ω₂^{Ω₂}`**: `Tj.tjLS` below `G`, `tuLevX` over `Tn.tnPD_G` from `G` on);
* `tuLSB` (**ITS MOVE**: `Tj.tjB_thH` below `G` and at the part `x` of `G + x`; `B_n(G + x) = G + B_n x`,
  `B_n Ĝ = Ĝ`, `B_n W^{Ω₂} = W^{Ω₂}`).

No new axiom.  New definitions: `tuGB`, `tuTh`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tu

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj
  Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.St Googology.Trans.PoR.InaccPsi.R2.Ta
  Googology.Trans.PoR.InaccPsi.R2.Td Googology.Trans.PoR.InaccPsi.R2.Tg Googology.Trans.PoR.InaccPsi.R2.Tj
  Googology.Trans.PoR.InaccPsi.R2.Tn

variable {S : InaccSeq.{0}}

/-- **The bound `G + Ω₂^{Ω₂}` of the level system.** -/
noncomputable def tuGB (_S : InaccSeq.{0}) : Ordinal.{0} := veblen (Om (1 + 1)) 1 + leWe (Om (1 + 1))

/-- **The image of a level**: `Θ̂_L E` below `G`; `Ĝ + Θ̂_L x` at `G + x`. -/
noncomputable def tuTh (S : InaccSeq.{0}) (l E : Ordinal.{0}) : Ordinal.{0} :=
  if E < veblen (Om (1 + 1)) 1 then tdThL S l E
  else veblen (Om 1) 1 + tdThL S l (E - veblen (Om (1 + 1)) 1)

theorem tuThE_lt {l E : Ordinal.{0}} (hE : E < veblen (Om (1 + 1)) 1) : tuTh S l E = tdThL S l E := by
  unfold tuTh; rw [if_pos hE]

theorem tuThE_ge {l x : Ordinal.{0}} :
    tuTh S l (veblen (Om (1 + 1)) 1 + x) = veblen (Om 1) 1 + tdThL S l x := by
  unfold tuTh; rw [if_neg (not_lt.2 le_self_add), Ordinal.add_sub_cancel]

/-- `W^{Ω₂} < G`, `W^{Ω₂} ∣ G`. -/
theorem tuWW_G : leWe (Om (1 + 1 : Ordinal.{0})) < veblen (Om (1 + 1)) 1 ∧
    leWe (Om (1 + 1 : Ordinal.{0})) ∣ veblen (Om (1 + 1)) 1 := tuWe_G tgOm_lt_G

theorem tuGB_lt_G3 : tuGB S < S.psi 0 (Om (1 + 1 + 1)) :=
  rwG3_SC.isPrincipal tjG_lt_G3 (leWe_lt_SC rwG3_SC rwW_lt_G3 rwW_lt_G3).1

theorem tuGB_lim : IsSuccLimit (tuGB S) :=
  isSuccLimit_add _ (Ph.ph_opow_lim (mul_ne_zero ldOm2_SC.1.ne' ldOm2_SC.1.ne'))

/-- **`Θ̂_L c = Θ c` for `0 < c < Ω₂`.** -/
theorem tuThL_small {l c : Ordinal.{0}} (h1 : (1 : Ordinal.{0}) ≤ upsilon l) (hc0 : 0 < c)
    (hcW : c < Om (1 + 1)) : tdThL S l c = gxTh (upsilon l) (ldAtR S l) c := by
  have hs : sgLW c = 0 := by
    unfold sgLW
    exact Ordinal.div_eq_zero_of_lt ((Ordinal.log_le_self _ _).trans_lt hcW)
  have hc : 0 < c ∧ sgLW c < c := ⟨hc0, by rw [hs]; exact hc0⟩
  have hr : TgWF S l (taTm (c % leWe (sgLW c))) := by
    rw [hs, leWe_zero, Ordinal.mod_one, taTm_zero]; trivial
  rw [tjThL_cnf h1 hc hr, hs, leWe_zero, Ordinal.mod_one, Ordinal.div_one, tjThL_zero, leOe_zero, one_mul,
    add_zero]

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **`G + W^e·c` with the image `Ĝ + Ω^{Θ e}·Θ c` is a prefix** for all codes `1 ≤ e < Ω₂`, `c < Ω₂`. -/
theorem tuPD_G {e c : Ordinal.{0}} (he : GxCl (upsilon l) (ldAtR S l) e) (he1 : 1 ≤ e) (heW : e < Om (1 + 1))
    (hc : GxCl (upsilon l) (ldAtR S l) c) (hcW : c < Om (1 + 1)) :
    StPD S l (veblen (Om (1 + 1)) 1 + leWe e * c)
      (veblen (Om 1) 1 + leOe (gxTh (upsilon l) (ldAtR S l) e) * gxTh (upsilon l) (ldAtR S l) c) := by
  have he2 : e + 1 < veblen (Om (1 + 1)) 1 := (ldOm2_SC.isSuccLimit.add_one_lt heW).trans tgOm_lt_G
  have hΘ : gxTh (upsilon l) (ldAtR S l) e + 1 < veblen (Om 1) 1 :=
    (tnSC1.isSuccLimit.add_one_lt (tuTh_lt hl hX heW.le).1).trans ((lt_add_one _).trans tnOm1_lt_Gh)
  exact (tuStepLad hl hX e he he1 heW).2 _ _ (tnPD_G hl hX) (tuWe_G he2).2 (tuOe_Gh hΘ).2 c hc hcW

/-- **`G + Ω₂^k·c` with the image `Ĝ + Ω₁^k·Θ c` is a prefix** for every `1 ≤ k < ω` and every code `c < Ω₂`. -/
theorem tuPD_Gk (k : ℕ) (hk : 1 ≤ k) {c : Ordinal.{0}} (hc : GxCl (upsilon l) (ldAtR S l) c)
    (hcW : c < Om (1 + 1)) :
    StPD S l (veblen (Om (1 + 1)) 1 + leWe k * c) (veblen (Om 1) 1 + leOe k * gxTh (upsilon l) (ldAtR S l) c) := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hkρ : (k : Ordinal.{0}) < upsilon l := (nat_lt_omega0 k).trans (Lw.lw_omega_lt_SC hρSC)
  have hkW : (k : Ordinal.{0}) < Om (1 + 1) :=
    hkρ.trans (hρ1.trans ((rwO_lt_G (S := S)).trans (psi_lt (S := S) (InR_Om_succ 1) 0)))
  have h := tuPD_G hl hX (GxCl.small hkρ) (by exact_mod_cast hk) hkW hc hcW
  rwa [gxTh_small hkρ.le] at h

/-- **`G + Ω₂^ω` with the image `Ĝ + Ω₁^ω` is a prefix.** -/
theorem tuPD_Gw : StPD S l (veblen (Om (1 + 1)) 1 + leWe ω) (veblen (Om 1) 1 + leOe ω) := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hωρ : (ω : Ordinal.{0}) < upsilon l := Lw.lw_omega_lt_SC hρSC
  have hωW : (ω : Ordinal.{0}) < Om (1 + 1) :=
    hωρ.trans (hρ1.trans ((rwO_lt_G (S := S)).trans (psi_lt (S := S) (InR_Om_succ 1) 0)))
  have h1ρ : (1 : Ordinal.{0}) < upsilon l := gg_one_lt_of_SC hρSC
  have h := tuPD_G hl hX (GxCl.small hωρ) one_lt_omega0.le hωW (GxCl.small h1ρ)
    (h1ρ.trans (hρ1.trans ((rwO_lt_G (S := S)).trans (psi_lt (S := S) (InR_Om_succ 1) 0))))
  rwa [gxTh_small hωρ.le, gxTh_small h1ρ.le, mul_one, mul_one] at h

/-- **Every `x < W^{Ω₂}` of the hull over a prefix `P`**: own data and the level statement of `P + x` with the
image `P̂ + Θ̂_L x`. -/
theorem tuLevX : ∀ x, x ∈ cdHull S l → x < leWe (Om (1 + 1)) → ∀ P Ph, StPD S l P Ph →
    leWe (sgLW x + 1) ∣ P → leOe (gxTh (upsilon l) (ldAtR S l) (sgLW x) + 1) ∣ Ph →
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
  have heW : e < Om (1 + 1) := by
    by_contra hc; push Not at hc
    exact absurd ((leWe_mono hc).trans hWe) (not_le.2 hxW)
  have heH : e ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hxH)
  have hec : GxCl (upsilon l) (ldAtR S l) e := (ldHull_iff hl hX heW).1 heH
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
  have hD' := (tuStepLad hl hX e hec he1 heW).2 P Ph hD hd hdh _ hqc hqW
  have hex : e < x := heW.trans_le (by rw [← leWe_one]; exact (leWe_mono he1).trans hWe)
  have hxG : x < veblen (Om (1 + 1)) 1 := hxW.trans tuWW_G.1
  have hrw : TgWF S l (taTm (x % leWe e)) :=
    (tgTm_spec hl hX _ hrH ((hr.trans_le hWe).trans hxG)).1
  have hT : tdThL S l x = leOe (gxTh (upsilon l) (ldAtR S l) e) * gxTh (upsilon l) (ldAtR S l) (x / leWe e) +
      tdThL S l (x % leWe e) := by
    rw [tjThL_cnf h1ρ ⟨hpos, hex⟩ hrw, ← he_def, tuThL_small h1ρ (zero_lt_one.trans_le he1) heW]
  have eP : P + x = P + leWe e * (x / leWe e) + x % leWe e := by
    conv_lhs => rw [hxdec]
    rw [add_assoc]
  have eT : Ph + tdThL S l x = Ph + leOe (gxTh (upsilon l) (ldAtR S l) e) * gxTh (upsilon l) (ldAtR S l)
      (x / leWe e) + tdThL S l (x % leWe e) := by rw [hT, add_assoc]
  rw [eP, eT]
  rcases eq_or_ne (x % leWe e) 0 with hr0 | hr0
  · rw [hr0, add_zero, tjThL_zero, add_zero]; exact ⟨stOwP_img hD'.img hD'.hull hD'.one, hD'.lev, hD'.ltG⟩
  have hrx : x % leWe e < x := hr.trans_le hWe
  have hsr : sgLW (x % leWe e) < e := by
    by_contra hc; push Not at hc
    exact absurd ((leWe_mono hc).trans (sgLW_le (pos_iff_ne_zero.2 hr0))) (not_le.2 hr)
  have hsrH : sgLW (x % leWe e) ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hrH)
  have hsrc : GxCl (upsilon l) (ldAtR S l) (sgLW (x % leWe e)) := (ldHull_iff hl hX (hsr.trans heW)).1 hsrH
  refine IH _ hrx hrH (hrx.trans hxW) _ _ hD' ?_ ?_
  · exact (leWe_dvd (Order.add_one_le_of_lt hsr)).trans
      (dvd_add ((leWe_dvd (le_self_add : e ≤ e + 1)).trans hd) (dvd_mul_right _ _))
  · exact (tuOe_dvd (Order.add_one_le_of_lt (gxTh_lt hsrc hsr))).trans
      (dvd_add ((tuOe_dvd (le_self_add : gxTh (upsilon l) (ldAtR S l) e ≤ _ + 1)).trans hdh) (dvd_mul_right _ _))

/-- **Every level `G ≤ E < G + W^{Ω₂}` of the hull is `G + x` with `x < W^{Ω₂}` in the hull.** -/
theorem tuDec {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hGE : veblen (Om (1 + 1)) 1 ≤ E) (hE : E < tuGB S) :
    ∃ x, E = veblen (Om (1 + 1)) 1 + x ∧ x ∈ cdHull S l ∧ x < leWe (Om (1 + 1)) := by
  obtain ⟨x, rfl⟩ := exists_add_of_le hGE
  have hxW : x < leWe (Om (1 + 1)) := (add_lt_add_iff_left _).1 hE
  exact ⟨x, rfl, snHullRem hEH tuWW_G.2 hxW, hxW⟩

/-- **The data of a level `G + x`, `x < W^{Ω₂}`.** -/
theorem tuLevG {x : Ordinal.{0}} (hxH : x ∈ cdHull S l) (hxW : x < leWe (Om (1 + 1))) :
    ScOwP S l (SnCL S (veblen (Om (1 + 1)) 1 + x)) (veblen (Om (1 + 1)) 1 + x) (veblen (Om 1) 1 + tdThL S l x) ∧
      ScLev S l (SnCL S (veblen (Om (1 + 1)) 1 + x)) (veblen (Om (1 + 1)) 1 + x) (veblen (Om 1) 1 + tdThL S l x) ∧
      veblen (Om 1) 1 + tdThL S l x < S.psi 0 (Om (1 + 1)) := by
  have hsW : sgLW x < Om (1 + 1) := by
    rcases eq_or_ne x 0 with rfl | hx0
    · unfold sgLW; rw [Ordinal.log_zero_right, Ordinal.zero_div]; exact ldOm2_SC.1
    by_contra hc; push Not at hc
    exact absurd ((leWe_mono hc).trans (sgLW_le (pos_iff_ne_zero.2 hx0))) (not_le.2 hxW)
  have hs2 : sgLW x + 1 < veblen (Om (1 + 1)) 1 := (ldOm2_SC.isSuccLimit.add_one_lt hsW).trans tgOm_lt_G
  have hΘ : gxTh (upsilon l) (ldAtR S l) (sgLW x) + 1 < veblen (Om 1) 1 :=
    (tnSC1.isSuccLimit.add_one_lt (tuTh_lt hl hX hsW.le).1).trans ((lt_add_one _).trans tnOm1_lt_Gh)
  exact tuLevX hl hX x hxH hxW _ _ (tnPD_G hl hX) (tuWe_G hs2).2 (tuOe_Gh hΘ).2

/-- **THE LEVEL SYSTEM UP TO `G + Ω₂^{Ω₂}`.** -/
theorem tuLS : StLS S l (tuGB S) (tuTh S) := by
  have hT := tjLS (S := S) hl hX
  refine ⟨tuGB_lim, tuGB_lt_G3, ?_, ?_, ?_⟩
  · intro E hEH h1 hE
    rcases lt_or_ge E (veblen (Om (1 + 1)) 1) with hlt | hge
    · rw [tuThE_lt hlt]; exact hT.ltG E hEH h1 hlt
    · obtain ⟨x, rfl, hxH, hxW⟩ := tuDec hl hX hEH hge hE
      rw [tuThE_ge]; exact (tuLevG hl hX hxH hxW).2.2
  · intro E hEH h1 hE
    rcases lt_or_ge E (veblen (Om (1 + 1)) 1) with hlt | hge
    · rw [tuThE_lt hlt]; exact hT.own E hEH h1 hlt
    · obtain ⟨x, rfl, hxH, hxW⟩ := tuDec hl hX hEH hge hE
      rw [tuThE_ge]; exact (tuLevG hl hX hxH hxW).1
  · intro E hEH h1 hE
    rcases lt_or_ge E (veblen (Om (1 + 1)) 1) with hlt | hge
    · rw [tuThE_lt hlt]; exact hT.lev E hEH h1 hlt
    · obtain ⟨x, rfl, hxH, hxW⟩ := tuDec hl hX hEH hge hE
      rw [tuThE_ge]; exact (tuLevG hl hX hxH hxW).2.1

end Main

section Move

variable {n : ℕ} {l l' ηx ηx' : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hl' : IsRestartIdx l') (hX' : upsilon l' < Pv S ηx')

include hl hX hl' hX'

/-- **THE MOVE OF THE LEVEL SYSTEM UP TO `G + Ω₂^{Ω₂}`.** -/
theorem tuLSB : StLSB S n l l' (tuGB S) (tuTh S) := by
  intro B hBSC hGB IHm E hEH h1 hE hEcl
  obtain ⟨hDε, hBε⟩ := tjB_G (S := S) (n := n)
  obtain ⟨hDεh, hBεh⟩ := tnB_Gh (S := S) (n := n)
  have hGB_G : veblen (Om (1 + 1)) 1 ≤ tuGB S := le_self_add
  rcases lt_or_ge E (veblen (Om (1 + 1)) 1) with hlt | hge
  · obtain ⟨hDE, hDE2, hBE2, hBEε, hBEH, hBcl, hDT, hDΘ1, hBΘ1, hΘmove⟩ :=
      tjB_thH hl hX hl' hX' hBSC IHm E hEH hlt hEcl
    refine ⟨hDE, hDE2, hBE2, hBEε.trans_le hGB_G, hBEH, hBcl, ?_, ?_, ?_, ?_⟩
    · rw [tuThE_lt hlt]; exact hDT
    · rw [tuThE_lt hlt]; exact hDΘ1
    · rw [tuThE_lt hlt]; exact hBΘ1
    · rw [tuThE_lt hlt, tuThE_lt hBEε]; exact hΘmove
  obtain ⟨x, rfl, hxH, hxW⟩ := tuDec hl hX hEH hge hE
  set G := veblen (Om (1 + 1 : Ordinal.{0})) 1 with hG_def
  set Gh := veblen (Om (1 : Ordinal.{0})) 1 with hGh_def
  have hxG : x < G := hxW.trans tuWW_G.1
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
  -- `B_n x < W^{Ω₂}`
  obtain ⟨hDWW, hBWW⟩ := Rn.rnB_WW (S := S) (n := n)
  have hBxW : Bc.bcB S n x < leWe (Om (1 + 1)) := by
    have h := (mvB_lt_iff (k := n) hDx hDWW).2 hxW; rwa [hBWW] at h
  -- the image
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

end Googology.Trans.PoR.InaccPsi.R2.Tu

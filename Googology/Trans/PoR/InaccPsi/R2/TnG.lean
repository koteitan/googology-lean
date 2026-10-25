import Googology.Trans.PoR.InaccPsi.R2.TnOwn

/-!
# The level `G = φ(Ω₂, 1)` with the image `Ĝ = φ(Ω₁, 1)`: the level statement and the prefix

`Θ = gxTh ρ_λ (ldAtR λ)`, `Θ̂_L = Td.tdThL`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_y(β, X₀) = ψ_{Ω₂}(β + W^{X₀ + W^y})`,
`CL = Sn.SnCL`, `G1 = ψ_{Ω₂}(0)`, `G3 = ψ_{Ω₃}(0)`.

* `tnThL_one` (`Θ̂_L(1) = 1`), `tnOm_lt_veb` (`Ω₂ + 1 < φ(c, Ω₂ + 1)`), `tnThL_node1`
  (`Θ̂_L(φ(c, Ω₂ + 1)) = φ(Θ c, Ω₁ + 1)`);
* `tnMemG` (**THE MEMBERS**: for every code `1 ≤ c < T_G(β, X₀)` of `λ` the level `φ(c, Ω₂ + 1) < G` of the
  system `Tj.tjLS` is own at `(β, X₀)` (`Tn.tnOwnCL`) with the image `φ(Θ c, Ω₁ + 1) < Ĝ`);
* `tnLev_G` (**THE LEVEL STATEMENT AT `G`**: `Sc.ScLev (CL G) G Ĝ`, by `Tn.tnLevLimC`: the exponents of the
  normal-form atoms below `T_G` are below `φ(s, Ω₂ + 1)` for an atom `s < T_G`, the level-1 codes below `Ĝ` over
  `Θ(T_G)` are below `φ(Θ c, Ω₁ + 1)` for a code `c < T_G`, `Td.tdCl_levDec` at `Ω₂` and at `Ω₁`);
* `tnPD_G` (**`G` WITH THE IMAGE `Ĝ` IS A PREFIX**, `St.StPD`), `tnG_dvd2` (`Ω₂² ∣ G`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Rw Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg
  Googology.Trans.PoR.InaccPsi.R2.Sj
  Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.St Googology.Trans.PoR.InaccPsi.R2.Ta
  Googology.Trans.PoR.InaccPsi.R2.Td Googology.Trans.PoR.InaccPsi.R2.Tg Googology.Trans.PoR.InaccPsi.R2.Tj

variable {S : InaccSeq.{0}}

/-- `Θ̂_L(1) = 1`. -/
theorem tnThL_one {l : Ordinal.{0}} (h1 : (1 : Ordinal.{0}) ≤ upsilon l) : tdThL S l 1 = 1 := by
  have hs : sgLW 1 = 0 := by unfold sgLW; rw [Ordinal.log_one_right, Ordinal.zero_div]
  have hc : 0 < (1 : Ordinal.{0}) ∧ sgLW 1 < 1 := ⟨zero_lt_one, by rw [hs]; exact zero_lt_one⟩
  have hr : TgWF S l (taTm (1 % leWe (sgLW 1))) := by
    rw [hs, leWe_zero, Ordinal.mod_one, taTm_zero]; trivial
  rw [tjThL_cnf h1 hc hr, hs, leWe_zero, Ordinal.mod_one, Ordinal.div_one, tjThL_zero, leOe_zero, one_mul,
    add_zero, gxTh_small h1]

/-- `Ω₂ + 1 < φ(c, Ω₂ + 1)`. -/
theorem tnOm_lt_veb (c : Ordinal.{0}) : Om (1 + 1) + 1 < veblen c (Om (1 + 1) + 1) := by
  refine (right_le_veblen c _).lt_of_ne fun h => ?_
  have hp : IsPrincipal (· + ·) (Om (1 + 1) + 1) := by rw [h]; exact Ph.ph_veblen_prin c _
  have := hp (lt_add_one (Om (1 + 1))) (gg_one_lt_of_SC ldOm2_SC |>.trans (lt_add_one _))
  exact lt_irrefl _ this

/-- `Θ̂_L(φ(c, Ω₂ + 1)) = φ(Θ c, Ω₁ + 1)` for `c ≠ 0`. -/
theorem tnThL_node1 {l c : Ordinal.{0}} (h1 : (1 : Ordinal.{0}) ≤ upsilon l) (hc0 : c ≠ 0) :
    tdThL S l (veblen c (Om (1 + 1) + 1)) = veblen (gxTh (upsilon l) (ldAtR S l) c) (Om 1 + 1) := by
  rw [tdThL_veb hc0 le_rfl (tnOm_lt_veb c), tnThL_one h1]

/-- `Ω₁ + 1 < φ(Ω₁, 1)`. -/
theorem tnOm1_lt_Gh : Om (1 : Ordinal.{0}) + 1 < veblen (Om 1) 1 := by
  have h : Om (1 : Ordinal.{0}) < veblen (Om 1) 1 := by
    conv_lhs => rw [← Ph.ph_SC_Om1.veblen_zero]
    exact (veblen_lt_veblen_iff_right).2 zero_lt_one
  exact (taVeb_lim (Om_pos one_ne_zero).ne').add_one_lt h

/-- `φ(Ω₁, 1) < ψ_{Ω₂}(0)`. -/
theorem tnGh_lt_G1 : veblen (Om 1) 1 < S.psi 0 (Om (1 + 1)) :=
  rwG_SC.2 _ rwO_lt_G _ (gg_one_lt_of_SC rwG_SC)

/-- `Ω₂ + 1 < φ(Ω₂, 1)`. -/
theorem tnOm2_lt_G : Om (1 + 1 : Ordinal.{0}) + 1 < veblen (Om (1 + 1)) 1 := tjG_lim.add_one_lt tgOm_lt_G

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **THE MEMBERS** `φ(c, Ω₂ + 1)` for the codes `1 ≤ c < T_G(β, X₀)`. -/
theorem tnMemG {β X0 c : Ordinal.{0}} (hc : GxCl (upsilon l) (ldAtR S l) c) (hc1 : 1 ≤ c)
    (hcT : c < S.psi (β + leWe (X0 + leWe (veblen (Om (1 + 1)) 1))) (Om (1 + 1))) :
    ScOwP S l (SnCL S (veblen c (Om (1 + 1) + 1))) (veblen c (Om (1 + 1) + 1))
        (veblen (gxTh (upsilon l) (ldAtR S l) c) (Om 1 + 1)) ∧
      ScLev S l (SnCL S (veblen c (Om (1 + 1) + 1))) (veblen c (Om (1 + 1) + 1))
        (veblen (gxTh (upsilon l) (ldAtR S l) c) (Om 1 + 1)) ∧
      SnCL S (veblen c (Om (1 + 1) + 1)) β X0 ∧ veblen c (Om (1 + 1) + 1) < veblen (Om (1 + 1)) 1 ∧
      veblen (gxTh (upsilon l) (ldAtR S l) c) (Om 1 + 1) < veblen (Om 1) 1 := by
  have h1ρ : (1 : Ordinal.{0}) ≤ upsilon l := (gg_one_lt_of_SC (leRho hl hX).1).le
  have hc0 : c ≠ 0 := (zero_lt_one.trans_le hc1).ne'
  have hcW : c < Om (1 + 1) := hcT.trans (psi_lt (InR_Om_succ 1) _)
  have hcH : c ∈ cdHull S l := (ldHull_iff hl hX hcW).2 hc
  have hEH : veblen c (Om (1 + 1) + 1) ∈ cdHull S l := CSet.phi_mem hcH (CSet.succ_mem (Mx.mxOm2_mem _ _))
  have hE1 : 1 ≤ veblen c (Om (1 + 1) + 1) := Order.one_le_iff_pos.2 veblen_pos
  have hEG : veblen c (Om (1 + 1) + 1) < veblen (Om (1 + 1)) 1 := by
    calc veblen c (Om (1 + 1) + 1) < veblen c (veblen (Om (1 + 1)) 1) := (veblen_lt_veblen_iff_right).2 tnOm2_lt_G
      _ = veblen (Om (1 + 1)) 1 := veblen_veblen_of_lt hcW 1
  have hΘc : gxTh (upsilon l) (ldAtR S l) c < Om 1 := snTh_lt_Om1 hl hX hcW.le
  have hEh : veblen (gxTh (upsilon l) (ldAtR S l) c) (Om 1 + 1) < veblen (Om 1) 1 := by
    calc veblen (gxTh (upsilon l) (ldAtR S l) c) (Om 1 + 1)
        < veblen (gxTh (upsilon l) (ldAtR S l) c) (veblen (Om 1) 1) := (veblen_lt_veblen_iff_right).2 tnOm1_lt_Gh
      _ = veblen (Om 1) 1 := veblen_veblen_of_lt hΘc 1
  have hS := tjLS hl hX
  have hown := hS.own _ hEH hE1 hEG
  have hlev := hS.lev _ hEH hE1 hEG
  rw [tnThL_node1 h1ρ hc0] at hown hlev
  exact ⟨hown, hlev, tnOwnCL hl hX hc hcT, hEG, hEh⟩

/-- **THE LEVEL STATEMENT AT `G = φ(Ω₂, 1)`** with the image `Ĝ = φ(Ω₁, 1)`. -/
theorem tnLev_G : ScLev S l (SnCL S (veblen (Om (1 + 1)) 1)) (veblen (Om (1 + 1)) 1) (veblen (Om 1) 1) := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hGH : veblen (Om (1 + 1)) 1 ∈ cdHull S l := CSet.phi_mem (Mx.mxOm2_mem _ _) (CSet.one_mem _ _)
  have hP : ScOwP S l (SnCL S (veblen (Om (1 + 1)) 1)) (veblen (Om (1 + 1)) 1) (veblen (Om 1) 1) :=
    stOwP_img (fun _ _ _ => ⟨CSet.phi_mem (CSet.Om_mem (CSet.one_mem _ _)) (CSet.one_mem _ _),
      fun _ hQ _ => LeCl.phi LeCl.om (LeCl.small (gg_one_lt_of_SC hQ))⟩) hGH
      (Order.one_le_iff_pos.2 veblen_pos)
  refine tnLevLimC hl hX hP tjG_lt_G3 tnGh_lt_G1 ?_ ?_
  · intro β X0 Xh0 hoff hd hG3 hb hOw y hyH hyC hy
    obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hb
    rw [add_zero] at hβd hβA hβown
    obtain ⟨-, hX0H, hX0m, -, -, -⟩ := rvOff_data hoff
    set a := X0 + y + 1 with ha_def
    have hyG : y + 1 < leWe (veblen (Om (1 + 1)) 1) := by
      rw [tgWe_G] at hy ⊢; exact tjG_lim.add_one_lt hy
    have ha_lt : a < X0 + leWe (veblen (Om (1 + 1)) 1) := by
      rw [ha_def, add_assoc]; exact (add_lt_add_iff_left X0).2 hyG
    have hyC' : y ∈ S.CSet (β + leWe a) (S.psi (β + leWe a) (Om (1 + 1))) := by
      have h1 := taSub_mem (S := S) _ hyC X0
      rwa [Ordinal.add_sub_cancel] at h1
    have hargH : β + leWe a ∈ cdHull S l :=
      CSet.add_mem hβH (leWe_mem (CSet.succ_mem (CSet.add_mem hX0H hyH)))
    have hle : β + leWe a ≤ β + leWe (X0 + leWe (veblen (Om (1 + 1)) 1)) :=
      (add_le_add_iff_left β).2 (leWe_mono ha_lt.le)
    have hs'at : S.psi (β + leWe a) (Om (1 + 1)) ∈ ldAtR S l := ⟨_, hargH, hle.trans_lt hβA, rfl⟩
    have hmem : β + leWe a ∈ S.CSet (β + leWe (X0 + leWe (veblen (Om (1 + 1)) 1)))
        (S.psi (β + leWe (X0 + leWe (veblen (Om (1 + 1)) 1))) (Om (1 + 1))) := by
      have hX0' : X0 ∈ S.CSet (β + leWe (X0 + leWe (veblen (Om (1 + 1)) 1)))
          (S.psi (β + leWe (X0 + leWe (veblen (Om (1 + 1)) 1))) (Om (1 + 1))) :=
        CSet_mono zero_le (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono
          (le_self_add : X0 ≤ X0 + leWe (veblen (Om (1 + 1)) 1))))).1 hX0m
      have hy' := (psi_mono (S := S) (InR_Om_succ 1) hle).2 hyC'
      exact CSet.add_mem (hβown _ le_rfl) (leWe_mem (CSet.succ_mem (CSet.add_mem hX0' hy')))
    have hs'T : S.psi (β + leWe a) (Om (1 + 1)) < S.psi (β + leWe (X0 + leWe (veblen (Om (1 + 1)) 1))) (Om (1 + 1)) :=
      psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left β).2 (leWe_lt ha_lt)) hmem
    have hs'1 : 1 ≤ S.psi (β + leWe a) (Om (1 + 1)) :=
      (gg_one_lt_of_SC (SC_psi (InR_Om_succ 1) _)).le
    obtain ⟨hPk, hLk, hOk, hek, hehk⟩ := tnMemG hl hX (GxCl.atom hs'at) hs'1 hs'T
    refine ⟨_, _, _, hPk, hLk, hOk, hek, hehk, ?_⟩
    rcases eq_or_ne y 0 with rfl | hy0
    · exact leWe_pos _
    set w := log ω y / Om (1 + 1) with hw
    have hwG : w < veblen (Om (1 + 1)) 1 := tnLogW_lt hy0 hy
    have hwC : w ∈ S.CSet (β + leWe a) (S.psi (β + leWe a) (Om (1 + 1))) := ldDivK_mem ldOm2_SC (leLog_mem hyC')
    have hsSC : SC (S.psi (β + leWe a) (Om (1 + 1))) := SC_psi (InR_Om_succ 1) _
    have hwc : LeCl (Om (1 + 1)) (S.psi (β + leWe a) (Om (1 + 1))) w :=
      snLeCl_mem hsSC le_rfl hwC (hwG.trans tjG_lt_G3)
    have hlt : w < veblen (Om (1 + 1)) (0 + 1) := by rw [zero_add]; exact hwG
    obtain ⟨ζ, hζ, hζW, hwζ⟩ := tdCl_levDec hsSC ldOm2_SC ldOm2_SC.isSuccLimit w hwc hlt
    have hζs := tdCl_lt hsSC ζ hζ hζW
    rw [ldOm2_SC.veblen_zero] at hwζ
    have hwφ : w < veblen (S.psi (β + leWe a) (Om (1 + 1))) (Om (1 + 1) + 1) :=
      hwζ.trans_le (veblen_left_monotone _ hζs.le)
    exact (roLt_We_log y).trans_le (leWe_mono (Order.add_one_le_of_lt hwφ))
  · intro β X0 Xh0 hoff hd hG3 hb hOw z hzc hz
    obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hb
    rw [add_zero] at hβd hβA hβown
    obtain ⟨-, hX0H, -, -, -, -⟩ := rvOff_data hoff
    have hTat : leTe S (X0 + leWe (veblen (Om (1 + 1)) 1)) β ∈ ldAtR S l :=
      ⟨_, CSet.add_mem hβH (leWe_mem (CSet.add_mem hX0H (leWe_mem hGH))), hβA, rfl⟩
    have hTSC := (ldAtom_ge hρSC hρ1 hAt hTat).1
    have hTlim : IsSuccLimit (S.psi (β + leWe (X0 + leWe (veblen (Om (1 + 1)) 1))) (Om (1 + 1))) :=
      (SC_psi (InR_Om_succ 1) _).isSuccLimit
    have hΩT : Om (1 : Ordinal.{0}) < S.psi (β + leWe (X0 + leWe (veblen (Om (1 + 1)) 1))) (Om (1 + 1)) :=
      (psiS_bounds (S := S) _ 1).1
    -- a code `c` below `T_G` with `ζ̂ ≤ Θ c`
    have hmem : ∀ ζh, ζh < gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe (veblen (Om (1 + 1)) 1)) β) →
        ∃ c, GxCl (upsilon l) (ldAtR S l) c ∧ 1 ≤ c ∧
          c < S.psi (β + leWe (X0 + leWe (veblen (Om (1 + 1)) 1))) (Om (1 + 1)) ∧
          ζh ≤ gxTh (upsilon l) (ldAtR S l) c := by
      intro ζh hζh
      obtain ⟨c, hc, hcm, hΘc⟩ := gxTh_onto hζh
      refine ⟨c + 1, GxCl.add hc (GxCl.small (gg_one_lt_of_SC hρSC)), le_add_self, hTlim.add_one_lt hcm, ?_⟩
      rw [← hΘc]; exact gxTh_mono le_self_add
    rcases eq_or_ne z 0 with rfl | hz0
    · obtain ⟨c, hc, hc1, hcT, -⟩ := hmem 0 hTSC.1
      obtain ⟨hPk, hLk, hOk, hek, hehk⟩ := tnMemG hl hX hc hc1 hcT
      exact ⟨_, _, _, hPk, hLk, hOk, hek, hehk, leOe_pos _⟩
    have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
    set w := log ω z / Om 1 with hw
    have hwG : w < veblen (Om 1) 1 := by
      have hlog : log ω z < Om 1 * veblen (Om 1) 1 :=
        (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hz0).trans_lt hz)
      exact (Ordinal.lt_mul_iff_div_lt hΩ0).1 hlog
    have hwc : LeCl (Om 1) (gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe (veblen (Om (1 + 1)) 1)) β)) w :=
      sjCl_div hTSC Ph.ph_SC_Om1 _ (leClDec hTSC Ph.ph_SC_Om1 z hzc).2
    have hlt : w < veblen (Om 1) (0 + 1) := by rw [zero_add]; exact hwG
    obtain ⟨ζh, hζh, hζhΩ, hwζ⟩ := tdCl_levDec hTSC Ph.ph_SC_Om1 Ph.ph_SC_Om1.isSuccLimit w hwc hlt
    have hζhT := tdCl_lt hTSC ζh hζh hζhΩ
    rw [Ph.ph_SC_Om1.veblen_zero] at hwζ
    obtain ⟨c, hc, hc1, hcT, hζc⟩ := hmem ζh hζhT
    obtain ⟨hPk, hLk, hOk, hek, hehk⟩ := tnMemG hl hX hc hc1 hcT
    refine ⟨_, _, _, hPk, hLk, hOk, hek, hehk, ?_⟩
    have hwφ : w < veblen (gxTh (upsilon l) (ldAtR S l) c) (Om 1 + 1) :=
      hwζ.trans_le (veblen_left_monotone _ hζc)
    exact (roLt_Oe_log z).trans_le (leOe_mono (Order.add_one_le_of_lt hwφ))

/-- **`G = φ(Ω₂, 1)` WITH THE IMAGE `Ĝ = φ(Ω₁, 1)` IS A PREFIX.** -/
theorem tnPD_G : StPD S l (veblen (Om (1 + 1)) 1) (veblen (Om 1) 1) := by
  have hG1 : (1 : Ordinal.{0}) ≤ veblen (Om (1 + 1)) 1 := Order.one_le_iff_pos.2 veblen_pos
  refine ⟨?_, CSet.phi_mem (Mx.mxOm2_mem _ _) (CSet.one_mem _ _), hG1, tjG_lt_G3, tnGh_lt_G1,
    fun _ _ _ => ⟨CSet.phi_mem (CSet.Om_mem (CSet.one_mem _ _)) (CSet.one_mem _ _),
      fun _ hQ _ => LeCl.phi LeCl.om (LeCl.small (gg_one_lt_of_SC hQ))⟩, tnLev_G hl hX⟩
  have h := leWe_dvd hG1
  rwa [leWe_one, tgWe_G] at h

end Main

/-- `Ω₂² ∣ G`. -/
theorem tnG_dvd2 : Om (1 + 1 : Ordinal.{0}) * Om (1 + 1) ∣ veblen (Om (1 + 1)) 1 := by
  have h2 : (1 + 1 : Ordinal.{0}) ≤ veblen (Om (1 + 1)) 1 :=
    ((ldOm2_SC.isSuccLimit.add_one_lt (gg_one_lt_of_SC ldOm2_SC)).trans tgOm_lt_G).le
  have h := leWe_dvd h2
  unfold leWe at h
  rwa [stW2_opow, ← leWe, tgWe_G] at h

end Googology.Trans.PoR.InaccPsi.R2.Tn

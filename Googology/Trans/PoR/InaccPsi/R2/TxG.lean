import Googology.Trans.PoR.InaccPsi.R2.TxSys

/-!
# The step at the exponent `G = φ(Ω₂, 1)` and the prefixes `G·c`

`Θ = gxTh ρ_λ (ldAtR λ)`, `Θ̂_L = Td.tdThL`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `H_λ = cdHull S λ`, `G = φ(Ω₂, 1) = W^G`,
`Ĝ = φ(Ω₁, 1) = Ω^Ĝ`, prefixes `St.StPD`.

* `txOe_Gh` (`Ω^Ĝ = Ĝ`), `txDvdW_G` (`Ω₂ ∣ G`);
* `txStepG` (**THE STEP AT THE EXPONENT `G` FROM EVERY PREFIX**: `G ∣ P`, `Ĝ ∣ P̂` give the prefix `P + G` with the
  image `P̂ + Ĝ`; members `P + φ(c, Ω₂ + 1)`, `c` a code, by `Tn.tnLevLimM` and `Tx.txStepLad` at `φ(c, Ω₂ + 1)`);
* `txPDGc` (**THE PREFIXES `G·c`**: `G·c` with the image `Ĝ·Θ c` is a prefix for every code `1 ≤ c < Ω₂`: `c = 1` is
  `Tn.tnPD_G`, successors by `txStepG`, limits by `St.stLevLimB` with the members `G·c'`, `c' < c`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rq
  Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw Googology.Trans.PoR.InaccPsi.R2.Sc
  Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj Googology.Trans.PoR.InaccPsi.R2.Sn
  Googology.Trans.PoR.InaccPsi.R2.Sq Googology.Trans.PoR.InaccPsi.R2.St Googology.Trans.PoR.InaccPsi.R2.Sw
  Googology.Trans.PoR.InaccPsi.R2.Ta
  Googology.Trans.PoR.InaccPsi.R2.Td Googology.Trans.PoR.InaccPsi.R2.Tg Googology.Trans.PoR.InaccPsi.R2.Tj
  Googology.Trans.PoR.InaccPsi.R2.Tn Googology.Trans.PoR.InaccPsi.R2.Tu

variable {S : InaccSeq.{0}}

/-- **`Ω^Ĝ = Ĝ`.** -/
theorem txOe_Gh : leOe (veblen (Om (1 : Ordinal.{0})) 1) = veblen (Om 1) 1 := by
  unfold leOe; rw [tnK_mul_Gh, gg_veblen_eps (Om_pos one_ne_zero).ne']

/-- `Ω₂ ∣ G`. -/
theorem txDvdW_G : Om (1 + 1 : Ordinal.{0}) ∣ veblen (Om (1 + 1)) 1 :=
  (dvd_mul_right (Om (1 + 1 : Ordinal.{0})) (Om (1 + 1))).trans tnG_dvd2

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **THE STEP AT THE EXPONENT `G`**: for a prefix `(P, P̂)` with `G ∣ P`, `Ĝ ∣ P̂`, the level `P + G` with the image
`P̂ + Ĝ` is a prefix. -/
theorem txStepG {P Ph : Ordinal.{0}} (hD : StPD S l P Ph) (hdP : veblen (Om (1 + 1)) 1 ∣ P)
    (hdh : veblen (Om 1) 1 ∣ Ph) : StPD S l (P + veblen (Om (1 + 1)) 1) (Ph + veblen (Om 1) 1) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have h1ρ : (1 : Ordinal.{0}) ≤ upsilon l := (gg_one_lt_of_SC hρSC).le
  have hWG : leWe (veblen (Om (1 + 1 : Ordinal.{0})) 1) = veblen (Om (1 + 1)) 1 := tgWe_G
  have hdW : leWe (veblen (Om (1 + 1 : Ordinal.{0})) 1) ∣ P := by rw [hWG]; exact hdP
  have hdO : leOe (veblen (Om (1 : Ordinal.{0})) 1) ∣ Ph := by rw [txOe_Gh]; exact hdh
  have hGH : veblen (Om (1 + 1)) 1 ∈ cdHull S l := tnG_mem
  have hH : P + veblen (Om (1 + 1)) 1 ∈ cdHull S l := CSet.add_mem hD.hull hGH
  have h1 : 1 ≤ P + veblen (Om (1 + 1)) 1 := hD.one.trans le_self_add
  have hEG3 : P + veblen (Om (1 + 1)) 1 < S.psi 0 (Om (1 + 1 + 1)) := rwG3_SC.isPrincipal hD.ltG3 tjG_lt_G3
  have hEhG : Ph + veblen (Om 1) 1 < S.psi 0 (Om (1 + 1)) := rwG_SC.isPrincipal hD.ltG tnGh_lt_G1
  have himg : StImg S l (P + veblen (Om (1 + 1)) 1) (Ph + veblen (Om 1) 1) := by
    intro T hT hcl
    have hPc : ∀ Q, SC Q → T ≤ Q → LeCl (Om (1 + 1)) Q P := fun Q hQ hTQ =>
      (tuHead (g := veblen (Om (1 + 1)) 1) hQ hdW le_rfl le_rfl (by rw [hWG]; exact hcl Q hQ hTQ)).1
    obtain ⟨k1, k2⟩ := hD.img T hT hPc
    exact ⟨CSet.add_mem k1 (CSet.phi_mem (CSet.Om_mem (CSet.one_mem _ _)) (CSet.one_mem _ _)),
      fun Q hQ hΘQ => LeCl.add (k2 Q hQ hΘQ) (LeCl.phi LeCl.om (LeCl.small (gg_one_lt_of_SC hQ)))⟩
  refine ⟨dvd_add hD.dvd txDvdW_G, hH, h1, hEG3, hEhG, himg, ?_⟩
  -- the members `P + φ(c, Ω₂ + 1)`, `P̂ + φ(Θ c, Ω₁ + 1)`
  have hmemb : ∀ c, GxCl (upsilon l) (ldAtR S l) c → 1 ≤ c → c < Om (1 + 1) →
      StPD S l (P + veblen c (Om (1 + 1) + 1)) (Ph + veblen (gxTh (upsilon l) (ldAtR S l) c) (Om 1 + 1)) ∧
        veblen c (Om (1 + 1) + 1) < veblen (Om (1 + 1)) 1 ∧
        veblen (gxTh (upsilon l) (ldAtR S l) c) (Om 1 + 1) < veblen (Om 1) 1 := by
    intro c hc hc1 hcW
    have hc0 : c ≠ 0 := (zero_lt_one.trans_le hc1).ne'
    have hcH : c ∈ cdHull S l := (ldHull_iff hl hX hcW).2 hc
    have hmH : veblen c (Om (1 + 1) + 1) ∈ cdHull S l := CSet.phi_mem hcH (CSet.succ_mem (mxOm2_mem _ _))
    have hmG : veblen c (Om (1 + 1) + 1) < veblen (Om (1 + 1)) 1 := by
      calc veblen c (Om (1 + 1) + 1) < veblen c (veblen (Om (1 + 1)) 1) :=
            (veblen_lt_veblen_iff_right).2 tnOm2_lt_G
        _ = veblen (Om (1 + 1)) 1 := veblen_veblen_of_lt hcW 1
    have hΘc : gxTh (upsilon l) (ldAtR S l) c < Om 1 := snTh_lt_Om1 hl hX hcW.le
    have hmh : veblen (gxTh (upsilon l) (ldAtR S l) c) (Om 1 + 1) < veblen (Om 1) 1 := by
      calc veblen (gxTh (upsilon l) (ldAtR S l) c) (Om 1 + 1)
          < veblen (gxTh (upsilon l) (ldAtR S l) c) (veblen (Om 1) 1) := (veblen_lt_veblen_iff_right).2 tnOm1_lt_Gh
        _ = veblen (Om 1) 1 := veblen_veblen_of_lt hΘc 1
    have hT : tdThL S l (veblen c (Om (1 + 1) + 1)) = veblen (gxTh (upsilon l) (ldAtR S l) c) (Om 1 + 1) :=
      tnThL_node1 h1ρ hc0
    have hWm : leWe (veblen c (Om (1 + 1) + 1)) = veblen c (Om (1 + 1) + 1) := taWe_veb hc0 le_rfl
    have hΘc0 : gxTh (upsilon l) (ldAtR S l) c ≠ 0 := by
      have h := gxTh_mono (Z := upsilon l) (At := ldAtR S l) hc1
      rw [sqTh_one hl hX] at h
      exact (zero_lt_one.trans_le h).ne'
    have hOm : leOe (veblen (gxTh (upsilon l) (ldAtR S l) c) (Om 1 + 1)) =
        veblen (gxTh (upsilon l) (ldAtR S l) c) (Om 1 + 1) := taOe_veb hΘc0 le_rfl
    have hd1 : leWe (veblen c (Om (1 + 1) + 1)) ∣ P := (leWe_dvd hmG.le).trans hdW
    have hd2 : leOe (tdThL S l (veblen c (Om (1 + 1) + 1))) ∣ Ph := by
      have h2 := (tuOe_Gh hmh).2
      rw [hOm] at h2
      rw [hT, hOm]; exact h2.trans hdh
    have h := (txStepLad hl hX _ hmH (Order.one_le_iff_pos.2 veblen_pos) hmG).1 P Ph hD hd1 hd2
    rw [hWm, hT, hOm] at h
    exact ⟨h, hmG, hmh⟩
  refine tnLevLimM hl hX (M := fun c => P + veblen c (Om (1 + 1) + 1)) (Mh := fun c => Ph + veblen c (Om 1 + 1))
    (fun a b h => (add_le_add_iff_left _).2 (veblen_left_monotone _ h))
    (fun a b h => (add_le_add_iff_left _).2 (veblen_left_monotone _ h))
    (stOwP_img himg hH h1) hEG3 hEhG ?_ ?_ ?_ ?_
  · intro Q hQ _ w hw hwE
    have hM1 : P < P + veblen 1 (Om (1 + 1) + 1) := lt_add_of_pos_right _ veblen_pos
    rcases lt_or_ge w P with hwP | hwP
    · exact ⟨1, gg_one_lt_of_SC hQ, hwP.trans hM1⟩
    obtain ⟨x, rfl⟩ := exists_add_of_le hwP
    have hx : x < leWe (veblen (Om (1 + 1)) 1) := by rw [hWG]; exact (add_lt_add_iff_left P).1 hwE
    have hxc := tuModW hQ hdW hx hw
    rw [hWG] at hx
    have hx' : x < veblen (Om (1 + 1)) (0 + 1) := by rw [zero_add]; exact hx
    obtain ⟨c', hc', hc'W, hxc'⟩ := tdCl_levDec hQ ldOm2_SC ldOm2_SC.isSuccLimit x hxc hx'
    rw [ldOm2_SC.veblen_zero] at hxc'
    exact ⟨c', tdCl_lt hQ c' hc' hc'W, (add_lt_add_iff_left P).2 hxc'⟩
  · intro Q hQ w hw hwE
    have hM1 : Ph < Ph + veblen 1 (Om 1 + 1) := lt_add_of_pos_right _ veblen_pos
    rcases lt_or_ge w Ph with hwP | hwP
    · exact ⟨1, gg_one_lt_of_SC hQ, hwP.trans hM1⟩
    obtain ⟨x, rfl⟩ := exists_add_of_le hwP
    have hx : x < leOe (veblen (Om 1) 1) := by rw [txOe_Gh]; exact (add_lt_add_iff_left Ph).1 hwE
    have hxc := tuModO hQ hdO hx hw
    rw [txOe_Gh] at hx
    have hx' : x < veblen (Om 1) (0 + 1) := by rw [zero_add]; exact hx
    obtain ⟨c', hc', hc'W, hxc'⟩ := tdCl_levDec hQ tnSC1 tnSC1.isSuccLimit x hxc hx'
    rw [tnSC1.veblen_zero] at hxc'
    exact ⟨c', tdCl_lt hQ c' hc' hc'W, (add_lt_add_iff_left Ph).2 hxc'⟩
  · intro c hc hc1 hcW
    obtain ⟨hDc, hmG, hmh⟩ := hmemb c hc hc1 hcW
    exact ⟨stOwP_img hDc.img hDc.hull hDc.one, hDc.lev, (add_lt_add_iff_left P).2 hmG,
      (add_lt_add_iff_left Ph).2 hmh⟩
  · intro β X0 Xh0 hoff _ hG3 hb hOw c _ hc1 hcW hcT
    obtain ⟨-, hmG, -⟩ := hmemb c ‹_› hc1 hcW
    have hy : P + veblen c (Om (1 + 1) + 1) ≤ P + veblen (Om (1 + 1)) 1 := (add_le_add_iff_left P).2 hmG.le
    obtain ⟨z, hz1, hz2, hz⟩ := stCollD hoff (le_self_add.trans_lt hG3) hb hOw hy
    intro Q hQ hQ'
    have hz1' : P + leWe (veblen c (Om (1 + 1) + 1)) ≤ z := by
      rw [taWe_veb (zero_lt_one.trans_le hc1).ne' le_rfl]; exact hz1
    have hz2' : z ≤ P + leWe (veblen (Om (1 + 1)) 1) := by rw [hWG]; exact hz2
    obtain ⟨hPc, -⟩ := tuHead hQ hdW hz1' hz2' (hz Q hQ hQ')
    exact LeCl.add hPc (LeCl.phi (LeCl.small (hcT.trans_le hQ'))
      (LeCl.add LeCl.om (LeCl.small (gg_one_lt_of_SC hQ))))

/-- **THE PREFIXES `G·c`**: `G·c` with the image `Ĝ·Θ c` is a prefix for every code `1 ≤ c < Ω₂`. -/
theorem txPDGc : ∀ c, GxCl (upsilon l) (ldAtR S l) c → 1 ≤ c → c < Om (1 + 1) →
    StPD S l (veblen (Om (1 + 1)) 1 * c) (veblen (Om 1) 1 * gxTh (upsilon l) (ldAtR S l) c) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 := sqTh_one (S := S) hl hX
  have hc1 : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small (gg_one_lt_of_SC hρSC)
  have hWG : leWe (veblen (Om (1 + 1 : Ordinal.{0})) 1) = veblen (Om (1 + 1)) 1 := tgWe_G
  have hG0 : veblen (Om (1 + 1 : Ordinal.{0})) 1 ≠ 0 := veblen_pos.ne'
  have hGh0 : veblen (Om (1 : Ordinal.{0})) 1 ≠ 0 := veblen_pos.ne'
  have hd0 : leWe (veblen (Om (1 + 1 : Ordinal.{0})) 1 + 1) ∣ (0 : Ordinal.{0}) := dvd_zero _
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hc1' hcW
  have hcH : c ∈ cdHull S l := (ldHull_iff hl hX hcW).2 hc
  rcases zero_or_succ_or_isSuccLimit c with h0 | ⟨c0, hc0⟩ | hlim
  · rw [h0] at hc1'; exact absurd hc1' (not_le.2 zero_lt_one)
  · rw [succ_eq_add_one] at hc0
    subst hc0
    have hc0c : GxCl (upsilon l) (ldAtR S l) c0 := rqCode_pred hl hX hc hcW
    have hc0W : c0 < Om (1 + 1) := (lt_add_one c0).trans hcW
    rcases eq_or_ne c0 0 with rfl | hc00
    · rw [zero_add, mul_one, hΘ1, mul_one]; exact tnPD_G hl hX
    have IH0 := IH c0 (lt_add_one c0) hc0c (Order.one_le_iff_ne_zero.2 hc00) hc0W
    have h := txStepG hl hX IH0 (dvd_mul_right _ _) (dvd_mul_right _ _)
    rw [mul_add_one, gxTh_add hρSC hAt hc0c, hΘ1, mul_add_one]
    exact h
  · -- a limit code `c`: the members `G·c'`, `1 ≤ c' < c`
    set G := veblen (Om (1 + 1 : Ordinal.{0})) 1 with hG_def
    set Gh := veblen (Om (1 : Ordinal.{0})) 1 with hGh_def
    have h1c : (1 : Ordinal.{0}) < c := rvLim_one_lt hlim
    have hΘcO : gxTh (upsilon l) (ldAtR S l) c < Om 1 := snTh_lt_Om1 hl hX hcW.le
    have hEH : G * c ∈ cdHull S l := by
      have h := leMulWe_mem (S := S) (tnG_mem (S := S)) hcH
      rwa [hWG] at h
    have hE1 : 1 ≤ G * c :=
      Order.one_le_iff_pos.2 (mul_pos veblen_pos (zero_lt_one.trans h1c))
    have hEG : G * c < S.psi 0 (Om (1 + 1 + 1)) :=
      ldMul_lt_SC rwG3_SC tjG_lt_G3 (hcW.trans rwW_lt_G3)
    have hEhG : Gh * gxTh (upsilon l) (ldAtR S l) c < S.psi 0 (Om (1 + 1)) :=
      ldMul_lt_SC rwG_SC tnGh_lt_G1 (hΘcO.trans rwO_lt_G)
    have himg : StImg S l (G * c) (Gh * gxTh (upsilon l) (ldAtR S l) c) := by
      intro T hT hcl
      have hcT : c < T := by
        have h := hcl T hT le_rfl
        rw [← zero_add (G * c), ← hWG] at h
        exact (tuCodeHeadX hT hd0 h1c.le hcW h).2.2
      have hΘcT := gxTh_lt (Z := upsilon l) (At := ldAtR S l) hc hcT
      have hGhm : Gh ∈ S.CSet 0 (gxTh (upsilon l) (ldAtR S l) T) :=
        CSet.phi_mem (CSet.Om_mem (CSet.one_mem _ _)) (CSet.one_mem _ _)
      refine ⟨?_, fun Q hQ hΘQ => ?_⟩
      · have h := leMulOe_mem (S := S) hGhm (CSet.of_lt hΘcT)
        rwa [txOe_Gh] at h
      · have hGc : LeCl (Om 1) Q Gh := LeCl.phi LeCl.om (LeCl.small (gg_one_lt_of_SC hQ))
        have h := rvCl_mulOp hQ (LeCl.mulK hQ tnSC1 _ hGc) tnSC1 _ (LeCl.small (hΘcT.trans_le hΘQ))
        have e0 : ω ^ (Om 1 * Gh) = Gh := txOe_Gh
        rwa [e0] at h
    have hWd : Om (1 + 1) ∣ G * c := txDvdW_G.trans (dvd_mul_right _ _)
    refine ⟨hWd, hEH, hE1, hEG, hEhG, himg, ?_⟩
    have hP := stOwP_img himg hEH hE1
    have hmem : ∀ β X0 Xh0, RvOff S l β X0 Xh0 →
        X0 + leWe (G * c) < S.psi 0 (Om (1 + 1 + 1)) →
        RoBaseE S l (X0 + leWe (G * c)) 0 β → SnCL S (G * c) β X0 →
        ∀ c', GxCl (upsilon l) (ldAtR S l) c' → 1 ≤ c' → c' < c →
        ∃ e' eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, ScOwP S l Owe e' eh ∧ ScLev S l Owe e' eh ∧
          Owe β X0 ∧ e' < G * c ∧ eh < Gh * gxTh (upsilon l) (ldAtR S l) c ∧
          e' = G * c' ∧ eh = Gh * gxTh (upsilon l) (ldAtR S l) c' := by
      intro β X0 Xh0 hoff hG3 hb hcl c' hc' hc'1 hc'c
      have hD' := IH c' hc'c hc' hc'1 (hc'c.trans hcW)
      have hown : SnCL S (G * c') β X0 := by
        have h := tuLadDownX (P := 0) (e := G) hoff (by rw [zero_add, hWG]; exact hG3)
          (by rw [zero_add, hWG]; exact hb) hd0 hcW (by rw [zero_add, hWG]; exact hcl) hc'1 hc'c.le
        rwa [zero_add, hWG] at h
      exact ⟨_, _, SnCL S (G * c'), stOwP_img hD'.img hD'.hull hD'.one, hD'.lev, hown,
        mul_lt_mul_of_pos_left hc'c veblen_pos,
        mul_lt_mul_of_pos_left (gxTh_lt hc' hc'c) veblen_pos, rfl, rfl⟩
    refine stLevLimB hl hX hP hEG hEhG ?_ ?_
    · intro β X0 Xh0 hoff _ hG3 hb hcl y hyH hy
      have hG3' := le_self_add.trans_lt hG3
      rcases eq_or_ne y 0 with rfl | hy0
      · obtain ⟨e', eh, Owe, a1, a2, a3, a4, a5, rfl, -⟩ := hmem β X0 Xh0 hoff hG3' hb hcl 1 hc1 le_rfl h1c
        exact ⟨_, eh, Owe, a1, a2, a3, a4, a5, leWe_pos _⟩
      have hY2 : log ω y / Om (1 + 1) < G * c := by
        have h := (lt_opow_iff_log_lt one_lt_omega0 hy0).1 hy
        exact (Ordinal.lt_mul_iff_div_lt ldOm2_SC.1.ne').1 h
      set Y := log ω y / Om (1 + 1) with hY_def
      have hYH : Y ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hyH)
      set c1 := Y / G with hc1_def
      have hc1c : c1 < c := (Ordinal.div_lt hG0).2 hY2
      have hc1W : c1 < Om (1 + 1) := hc1c.trans hcW
      have hYW : Y < ω ^ (Om (1 + 1) * G + Om (1 + 1)) := by
        have : leWe (G + 1) = ω ^ (Om (1 + 1) * G + Om (1 + 1)) := by unfold leWe; rw [mul_add_one]
        rw [← this, leWe_succ, hWG]; exact hY2.trans_le (mul_le_mul_left' hcW.le _)
      have hc1H : c1 ∈ cdHull S l := by
        have h := leDivOp_mem (K := Om (1 + 1) * G) (dvd_mul_right _ _) hYH hYW
        have e0 : ω ^ (Om (1 + 1) * G) = G := hWG
        rwa [e0] at h
      have hc1c' : GxCl (upsilon l) (ldAtR S l) c1 := (ldHull_iff hl hX hc1W).1 hc1H
      have hcs : c1 + 1 < c := hlim.succ_lt hc1c
      have hcc := rqCode_succ hl hX hc1c' (hcs.trans hcW)
      obtain ⟨e', eh, Owe, a1, a2, a3, a4, a5, rfl, -⟩ := hmem β X0 Xh0 hoff hG3' hb hcl _ hcc le_add_self hcs
      refine ⟨_, eh, Owe, a1, a2, a3, a4, a5, (roLt_We_log y).trans_le (leWe_mono ?_)⟩
      rw [← hY_def]
      have h := Ordinal.lt_mul_succ_div Y hG0
      rw [Order.succ_eq_add_one] at h
      exact Order.add_one_le_of_lt h
    · intro β X0 Xh0 hoff _ hG3 hb hcl z hz
      have hG3' := le_self_add.trans_lt hG3
      set Θc := gxTh (upsilon l) (ldAtR S l) c with hΘc
      rcases eq_or_ne z 0 with rfl | hz0
      · obtain ⟨e', eh, Owe, a1, a2, a3, a4, a5, -, -⟩ := hmem β X0 Xh0 hoff hG3' hb hcl 1 hc1 le_rfl h1c
        exact ⟨e', eh, Owe, a1, a2, a3, a4, a5, leOe_pos _⟩
      have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
      have hq : log ω z / Om 1 < Gh * Θc :=
        (Ordinal.lt_mul_iff_div_lt hΩ0).1 ((lt_opow_iff_log_lt one_lt_omega0 hz0).1 hz)
      have hzq := roLt_Oe_log z
      set v := log ω z / Om 1 with hv
      have hv2 : v / Gh < Θc := (Ordinal.div_lt hGh0).2 hq
      obtain ⟨c0, hc0, hc0c, e0⟩ := gxTh_onto hv2
      have hcs : c0 + 1 < c := hlim.succ_lt hc0c
      have hcc := rqCode_succ hl hX hc0 (hcs.trans hcW)
      obtain ⟨e', eh, Owe, a1, a2, a3, a4, a5, -, rfl⟩ := hmem β X0 Xh0 hoff hG3' hb hcl _ hcc le_add_self hcs
      refine ⟨e', _, Owe, a1, a2, a3, a4, a5, hzq.trans_le (leOe_mono ?_)⟩
      rw [gxTh_add hρSC hAt hc0, hΘ1, e0]
      have h := Ordinal.lt_mul_succ_div v hGh0
      rw [Order.succ_eq_add_one] at h
      exact Order.add_one_le_of_lt h

end Main

end Googology.Trans.PoR.InaccPsi.R2.Tx

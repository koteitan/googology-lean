import Googology.Trans.PoR.InaccPsi.R2.UaStep

/-!
# Member systems of the limit exponents below `ε_{G+1}` (image `T = Ua.uaTh`)

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `H_λ = cdHull S λ`, `G = φ(Ω₂, 1)`, `Ĝ = φ(Ω₁, 1)`,
`ε_{G+1} = Ua.uaE = φ(1, G + 1)` (the least `W`-fixed point above `G`), `Γ₂ = Ua.uaGam`.

* `uaE`, `uaE_lt_Gam`, `uaE_lim`, `uaNode_G` (**the only `W`-fixed point in `[G, ε_{G+1})` is `G`**), `uaW_fix`;
* `uaMA_of_tu`, `uaMB_of_tu` (the member systems of `Tu` below `G` are member systems for `T`);
* `uaMB_G` (**THE MEMBER SYSTEM OF THE NODE `G = φ(Ω₂, 1)` AT THE LEVEL `Ω₂`**: members `φ(c, Ω₂ + 1)` indexed by the
  codes `c`, images `φ(Θ c, Ω₁ + 1)`; the own transfer is free since every `φ(c, Ω₂ + 1)`, `c < Q`, is a code);
* `uaMA_coef`, `uaMB_succ`, `uaMA_lift`, `uaMB_lift` (`Tu.tuMA_coef`, … for `T`, bound `Γ₂`);
* `uaMS` (**EVERY LIMIT EXPONENT `e + r < ε_{G+1}` OF `H_λ` (`W^{log_W r + 1} ∣ e`) HAS A MEMBER SYSTEM**: off the
  nodes along the base-`Ω₂` normal form of `r`; at a node `r < G` by `Tx.txMS`; at `r = G` by `uaMB_G`).

No new axiom.  New definition: `uaE`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ua

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj Googology.Trans.PoR.InaccPsi.R2.Sn
  Googology.Trans.PoR.InaccPsi.R2.Sq Googology.Trans.PoR.InaccPsi.R2.Sw Googology.Trans.PoR.InaccPsi.R2.Ta
  Googology.Trans.PoR.InaccPsi.R2.Td Googology.Trans.PoR.InaccPsi.R2.Tg Googology.Trans.PoR.InaccPsi.R2.Tj
  Googology.Trans.PoR.InaccPsi.R2.Tn Googology.Trans.PoR.InaccPsi.R2.Tu Googology.Trans.PoR.InaccPsi.R2.Tx

variable {S : InaccSeq.{0}}

/-- **The bound `ε_{G+1} = φ(1, G + 1)`.** -/
noncomputable def uaE : Ordinal.{0} := veblen 1 (veblen (Om (1 + 1)) 1 + 1)

theorem uaE_lim : IsSuccLimit uaE := taVeb_lim one_ne_zero

theorem uaG_lt_E : veblen (Om (1 + 1 : Ordinal.{0})) 1 < uaE := by
  unfold uaE
  calc veblen (Om (1 + 1 : Ordinal.{0})) 1 = veblen 1 (veblen (Om (1 + 1)) 1) :=
        (veblen_veblen_of_lt (gg_one_lt_of_SC ldOm2_SC) 1).symm
    _ < veblen 1 (veblen (Om (1 + 1)) 1 + 1) := veblen_lt_veblen_iff_right.2 (lt_add_one _)

theorem uaE_lt_Gam : uaE < uaGam :=
  uaGam_spec.1.2 _ (gg_one_lt_of_SC uaGam_spec.1) _ (uaGam_spec.1.isSuccLimit.add_one_lt uaG_lt_Gam)

theorem uaE_lt_G3 : uaE < S.psi 0 (Om (1 + 1 + 1)) := uaE_lt_Gam.trans_le uaGam_le_G3

/-- `W^r = r` at a `W`-fixed point `r > 0`. -/
theorem uaW_fix {r : Ordinal.{0}} (h0 : 0 < r) (hs : ¬ sgLW r < r) : leWe r = r := by
  have hsr : sgLW r = r := le_antisymm (txSg_le r) (not_lt.1 hs)
  refine le_antisymm ?_ ?_
  · have := sgLW_le h0; rwa [hsr] at this
  · unfold leWe
    exact (Ordinal.le_mul_right r ldOm2_SC.1).trans (right_le_opow _ one_lt_omega0)

/-- **The only `W`-fixed point in `[G, ε_{G+1})` is `G`.** -/
theorem uaNode_G {r : Ordinal.{0}} (hG : veblen (Om (1 + 1)) 1 ≤ r) (hrE : r < uaE) (hs : ¬ sgLW r < r) :
    r = veblen (Om (1 + 1)) 1 := by
  obtain ⟨hε, -⟩ := uaNode hG (hrE.trans uaE_lt_Gam) hs
  have hr : r ∈ range (veblen 1) := (mem_range_veblen one_ne_zero).2 fun a ha => by
    rw [Order.lt_one_iff] at ha; subst ha; rw [veblen_zero_apply]; exact hε
  obtain ⟨b, rfl⟩ := hr
  have hGe : veblen 1 (veblen (Om (1 + 1 : Ordinal.{0})) 1) = veblen (Om (1 + 1)) 1 :=
    veblen_veblen_of_lt (gg_one_lt_of_SC ldOm2_SC) 1
  rw [← hGe] at hG ⊢
  have hb1 : veblen (Om (1 + 1)) 1 ≤ b := (veblen_le_veblen_iff_right).1 hG
  have hb2 : b < veblen (Om (1 + 1)) 1 + 1 := (veblen_lt_veblen_iff_right).1 hrE
  rw [le_antisymm (Order.lt_add_one_iff.1 hb2) hb1]

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- A member system of `Tu` below `G` is one for `T`. -/
theorem uaMA_of_tu {E : Ordinal.{0}} (hEG : E < veblen (Om (1 + 1)) 1) (h : TuMA S l E) : UaMA S l E := by
  obtain ⟨Mem, hdat, hne, hA1, hA2, hA3⟩ := h
  refine ⟨Mem, hdat, hne, hA1, ?_, hA3⟩
  intro z hz
  rw [uaTh_lt hEG] at hz
  obtain ⟨m, hm, hzm⟩ := hA2 z hz
  exact ⟨m, hm, by rw [uaTh_lt ((hdat m hm).2.2.trans hEG)]; exact hzm⟩

theorem uaMB_of_tu {E : Ordinal.{0}} (hEG : E < veblen (Om (1 + 1)) 1) (h : TuMB S l E) : UaMB S l E := by
  obtain ⟨M, Mh, hM, hMh, hB0, hB1, hB2, hB3⟩ := h
  refine ⟨M, Mh, hM, hMh, ?_, hB1, ?_, hB3⟩
  · intro c hc hc1 hcW
    obtain ⟨a1, a2, a3, a4, a5⟩ := hB0 c hc hc1 hcW
    exact ⟨a1, a2, a3, by rw [uaTh_lt (a3.trans hEG)]; exact a4, by rw [uaTh_lt hEG]; exact a5⟩
  · intro Q hQ w hw hwE
    rw [uaTh_lt hEG] at hwE
    exact hB2 Q hQ w hw hwE

/-- **THE MEMBER SYSTEM OF THE NODE `G = φ(Ω₂, 1)`**: members `φ(c, Ω₂ + 1)` indexed by the codes `c`. -/
theorem uaMB_G : UaMB S l (veblen (Om (1 + 1)) 1) := by
  have h1ρ : (1 : Ordinal.{0}) ≤ upsilon l := (gg_one_lt_of_SC (leRho hl hX).1).le
  have hTG := uaG (S := S) hl hX
  refine ⟨fun c => veblen c (Om (1 + 1) + 1), fun v => veblen v (Om 1 + 1),
    fun a b h => veblen_left_monotone _ h, fun a b h => veblen_left_monotone _ h, ?_, ?_, ?_, ?_⟩
  · intro c hc hc1 hcW
    have hc0 : c ≠ 0 := (zero_lt_one.trans_le hc1).ne'
    have hcH : c ∈ cdHull S l := (ldHull_iff hl hX hcW).2 hc
    have hmG : veblen c (Om (1 + 1) + 1) < veblen (Om (1 + 1)) 1 := by
      calc veblen c (Om (1 + 1) + 1) < veblen c (veblen (Om (1 + 1)) 1) :=
            (veblen_lt_veblen_iff_right).2 tnOm2_lt_G
        _ = veblen (Om (1 + 1)) 1 := veblen_veblen_of_lt hcW 1
    have hΘc : gxTh (upsilon l) (ldAtR S l) c < Om 1 := snTh_lt_Om1 hl hX hcW.le
    refine ⟨CSet.phi_mem hcH (CSet.succ_mem (mxOm2_mem _ _)), Order.one_le_iff_pos.2 veblen_pos, hmG, ?_, ?_⟩
    · rw [uaTh_lt hmG]; exact tnThL_node1 h1ρ hc0
    · rw [hTG]
      calc veblen (gxTh (upsilon l) (ldAtR S l) c) (Om 1 + 1)
          < veblen (gxTh (upsilon l) (ldAtR S l) c) (veblen (Om 1) 1) := (veblen_lt_veblen_iff_right).2 tnOm1_lt_Gh
        _ = veblen (Om 1) 1 := veblen_veblen_of_lt hΘc 1
  · intro Q hQ _ w hw hwE
    have hx' : w < veblen (Om (1 + 1)) (0 + 1) := by rw [zero_add]; exact hwE
    obtain ⟨c', hc', hc'W, hxc'⟩ := tdCl_levDec hQ ldOm2_SC ldOm2_SC.isSuccLimit w hw hx'
    rw [ldOm2_SC.veblen_zero] at hxc'
    exact ⟨c', tdCl_lt hQ c' hc' hc'W, hxc'⟩
  · intro Q hQ w hw hwE
    rw [hTG] at hwE
    have hx' : w < veblen (Om 1) (0 + 1) := by rw [zero_add]; exact hwE
    obtain ⟨c', hc', hc'W, hxc'⟩ := tdCl_levDec hQ tnSC1 tnSC1.isSuccLimit w hw hx'
    rw [tnSC1.veblen_zero] at hxc'
    exact ⟨c', tdCl_lt hQ c' hc' hc'W, hxc'⟩
  · intro Q hQ c h _ hcQ _ _ _
    exact LeCl.phi (LeCl.small hcQ) (LeCl.add LeCl.om (LeCl.small (gg_one_lt_of_SC hQ)))

/-- **`e + W^f·c`, `c` a limit code** (`W^{f+1} ∣ e`): countable members `e + W^f·c'`. -/
theorem uaMA_coef {e f c : Ordinal.{0}} (heH : e ∈ cdHull S l) (hfH : f ∈ cdHull S l)
    (hc : GxCl (upsilon l) (ldAtR S l) c) (hlim : IsSuccLimit c) (hcW : c < Om (1 + 1))
    (hd : leWe (f + 1) ∣ e) (hlt : e + leWe f * c < uaGam) :
    UaMA S l (e + leWe f * c) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 := sqTh_one (S := S) hl hX
  have hc1 : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small (gg_one_lt_of_SC hρSC)
  have h1c : (1 : Ordinal.{0}) < c := rvLim_one_lt hlim
  have hmlt : ∀ c', c' < c → e + leWe f * c' < e + leWe f * c := fun c' h =>
    (add_lt_add_iff_left e).2 (mul_lt_mul_of_pos_left h (leWe_pos f))
  have hT : ∀ c', GxCl (upsilon l) (ldAtR S l) c' → 1 ≤ c' → c' ≤ c →
      uaTh S l (e + leWe f * c') = uaTh S l e + leOe (uaTh S l f) * gxTh (upsilon l) (ldAtR S l) c' :=
    fun c' hc' hc'1 hc'c => uaAddT hl hX heH hfH ((ldHull_iff hl hX (hc'c.trans_lt hcW)).2 hc') hc'1
      (hc'c.trans_lt hcW) hd ((add_le_add_iff_left e).2 (mul_le_mul_left' hc'c _) |>.trans_lt hlt)
  have hOf0 : leOe (uaTh S l f) ≠ 0 := (leOe_pos _).ne'
  refine ⟨fun m => ∃ c', GxCl (upsilon l) (ldAtR S l) c' ∧ 1 ≤ c' ∧ c' < c ∧ m = e + leWe f * c', ?_,
    ⟨_, 1, hc1, le_rfl, h1c, rfl⟩, ?_, ?_, ?_⟩
  · rintro m ⟨c', hc', hc'1, hc'c, rfl⟩
    exact ⟨CSet.add_mem heH (leMulWe_mem hfH ((ldHull_iff hl hX (hc'c.trans hcW)).2 hc')),
      (Order.one_le_iff_pos.2 (mul_pos (leWe_pos _) (zero_lt_one.trans_le hc'1))).trans le_add_self,
      hmlt c' hc'c⟩
  · intro y hyH hy
    rcases lt_or_ge y e with hye | hye
    · exact ⟨_, ⟨1, hc1, le_rfl, h1c, rfl⟩, hye.trans_le le_self_add⟩
    obtain ⟨v, rfl⟩ := exists_add_of_le hye
    have hvc : v < leWe f * c := (add_lt_add_iff_left e).1 hy
    have hvH : v ∈ cdHull S l := by
      have h := Ta.taSub_mem (S := S) _ hyH e; rwa [Ordinal.add_sub_cancel] at h
    set c1 := v / leWe f with hc1_def
    have hc1c : c1 < c := (Ordinal.div_lt (leWe_pos f).ne').2 hvc
    have hvW : v < ω ^ (Om (1 + 1) * f + Om (1 + 1)) := by
      have : leWe (f + 1) = ω ^ (Om (1 + 1) * f + Om (1 + 1)) := by unfold leWe; rw [mul_add_one]
      rw [← this, leWe_succ]; exact hvc.trans_le (mul_le_mul_left' hcW.le _)
    have hc1H : c1 ∈ cdHull S l := leDivOp_mem (K := Om (1 + 1) * f) (dvd_mul_right _ _) hvH hvW
    have hc1c' : GxCl (upsilon l) (ldAtR S l) c1 := (ldHull_iff hl hX (hc1c.trans hcW)).1 hc1H
    have hcs : c1 + 1 < c := hlim.add_one_lt hc1c
    refine ⟨_, ⟨c1 + 1, rqCode_succ hl hX hc1c' (hcs.trans hcW), le_add_self, hcs, rfl⟩, ?_⟩
    refine (add_lt_add_iff_left e).2 ?_
    have h := Ordinal.lt_mul_succ_div v (leWe_pos f).ne'
    rwa [Order.succ_eq_add_one] at h
  · intro z hz
    rw [hT c hc h1c.le le_rfl] at hz
    rcases lt_or_ge z (uaTh S l e) with hze | hze
    · refine ⟨_, ⟨1, hc1, le_rfl, h1c, rfl⟩, ?_⟩
      rw [hT 1 hc1 le_rfl h1c.le, hΘ1, mul_one]; exact hze.trans_le le_self_add
    obtain ⟨w, rfl⟩ := exists_add_of_le hze
    have hwc : w < leOe (uaTh S l f) * gxTh (upsilon l) (ldAtR S l) c := (add_lt_add_iff_left _).1 hz
    have hw2 : w / leOe (uaTh S l f) < gxTh (upsilon l) (ldAtR S l) c := (Ordinal.div_lt hOf0).2 hwc
    obtain ⟨c0, hc0, hc0c, e0⟩ := gxTh_onto hw2
    have hcs : c0 + 1 < c := hlim.add_one_lt hc0c
    have hcc := rqCode_succ hl hX hc0 (hcs.trans hcW)
    refine ⟨_, ⟨c0 + 1, hcc, le_add_self, hcs, rfl⟩, ?_⟩
    rw [hT _ hcc le_add_self hcs.le, gxTh_add hρSC hAt hc0, hΘ1, e0]
    refine (add_lt_add_iff_left _).2 ?_
    have h := Ordinal.lt_mul_succ_div w hOf0
    rwa [Order.succ_eq_add_one] at h
  · rintro Q hQ m h ⟨c', hc', hc'1, hc'c, rfl⟩ h1 h2 hh
    exact tuRangeX hQ hd hcW hc'1 h1 h2 hh

/-- **`e + W^{f+1}`** (`W^{f+1} ∣ e`): members `e + W^f·c` indexed by the codes `c`. -/
theorem uaMB_succ {e f : Ordinal.{0}} (heH : e ∈ cdHull S l) (hfH : f ∈ cdHull S l) (hd : leWe (f + 1) ∣ e)
    (hlt : e + leWe (f + 1) < uaGam) : UaMB S l (e + leWe (f + 1)) := by
  have hf1H : f + 1 ∈ cdHull S l := CSet.succ_mem hfH
  have hfE : f + 1 < uaGam := (tnLe_We _).trans_lt (le_add_self.trans_lt hlt)
  have hTf1 : uaTh S l (f + 1) = uaTh S l f + 1 := uaSucc hl hX hfH hfE
  have hTE : uaTh S l (e + leWe (f + 1)) = uaTh S l e + leOe (uaTh S l f + 1) := by
    rw [uaAddW hl hX heH hf1H hd hlt, hTf1]
  have hmlt : ∀ c, c < Om (1 + 1) → e + leWe f * c < e + leWe (f + 1) := fun c hc => by
    rw [leWe_succ]; exact (add_lt_add_iff_left e).2 (mul_lt_mul_of_pos_left hc (leWe_pos f))
  have hTedvd : leOe (uaTh S l f + 1) ∣ uaTh S l e := by
    have h := uaDvd hl hX e heH (le_self_add.trans_lt hlt) (f + 1) hf1H hd
    rwa [hTf1] at h
  refine ⟨fun c => e + leWe f * c, fun c => uaTh S l e + leOe (uaTh S l f) * c,
    fun a b h => (add_le_add_iff_left _).2 (mul_le_mul_left' h _),
    fun a b h => (add_le_add_iff_left _).2 (mul_le_mul_left' h _), ?_, ?_, ?_, ?_⟩
  · intro c hc hc1 hcW
    have hcH : c ∈ cdHull S l := (ldHull_iff hl hX hcW).2 hc
    refine ⟨CSet.add_mem heH (leMulWe_mem hfH hcH),
      (Order.one_le_iff_pos.2 (mul_pos (leWe_pos _) (zero_lt_one.trans_le hc1))).trans le_add_self,
      hmlt c hcW, uaAddT hl hX heH hfH hcH hc1 hcW hd ((hmlt c hcW).trans hlt), ?_⟩
    rw [hTE, leOe_succ]
    exact (add_lt_add_iff_left _).2 (mul_lt_mul_of_pos_left (snTh_lt_Om1 hl hX hcW.le) (leOe_pos _))
  · intro Q hQ _ w hw hwE
    rcases lt_or_ge w e with hwe | hwe
    · exact ⟨1, gg_one_lt_of_SC hQ, hwe.trans_le le_self_add⟩
    obtain ⟨x, rfl⟩ := exists_add_of_le hwe
    have hx : x < leWe (f + 1) := (add_lt_add_iff_left e).1 hwE
    have hxc := tuModW hQ hd hx hw
    have hxe : x < leWe f * Om (1 + 1) := by rwa [← leWe_succ]
    obtain ⟨c', hc'Q, hxc'⟩ := tuCofK hQ ldOm2_SC hxc hxe
    exact ⟨c', hc'Q, (add_lt_add_iff_left e).2 hxc'⟩
  · intro Q hQ w hw hwE
    rw [hTE] at hwE
    rcases lt_or_ge w (uaTh S l e) with hwe | hwe
    · exact ⟨1, gg_one_lt_of_SC hQ, hwe.trans_le le_self_add⟩
    obtain ⟨x, rfl⟩ := exists_add_of_le hwe
    have hx : x < leOe (uaTh S l f + 1) := (add_lt_add_iff_left _).1 hwE
    have hxc := tuModO hQ hTedvd hx hw
    have hxe : x < leOe (uaTh S l f) * Om 1 := by rwa [← leOe_succ]
    obtain ⟨c', hc'Q, hxc'⟩ := tuCofK hQ tnSC1 hxc hxe
    exact ⟨c', hc'Q, (add_lt_add_iff_left _).2 hxc'⟩
  · intro Q hQ c h hc1 hcQ h1 h2 hh
    have k1 : e + leWe f ≤ h :=
      ((add_le_add_iff_left e).2 ((mul_one (leWe f)).symm.le.trans (mul_le_mul_left' hc1 _))).trans h1
    obtain ⟨heQ, h', hh'1, hh'2, hh'c⟩ := tuHead hQ hd k1 h2 hh
    exact LeCl.add heQ (swCl_mulW hQ (tuCl_of_succ hQ hh'1 hh'2 hh'c) (LeCl.small hcQ))

/-- **`e + W^f` from the countable members of `f`** (`W^f ∣ e`): members `e + W^m`. -/
theorem uaMA_lift {e f : Ordinal.{0}} (heH : e ∈ cdHull S l) (hfH : f ∈ cdHull S l) (hd : leWe f ∣ e)
    (hlt : e + leWe f < uaGam) (hA : UaMA S l f) : UaMA S l (e + leWe f) := by
  obtain ⟨Mem, hdat, ⟨m0, hm0⟩, hA1, hA2, hA3⟩ := hA
  have hTm : ∀ m, Mem m → uaTh S l (e + leWe m) = uaTh S l e + leOe (uaTh S l m) := fun m hm =>
    uaAddW hl hX heH (hdat m hm).1 ((leWe_dvd (hdat m hm).2.2.le).trans hd)
      (((add_le_add_iff_left e).2 (leWe_mono (hdat m hm).2.2.le)).trans_lt hlt)
  have hTE := uaAddW hl hX heH hfH hd hlt
  refine ⟨fun m' => ∃ m, Mem m ∧ m' = e + leWe m, ?_, ⟨_, m0, hm0, rfl⟩, ?_, ?_, ?_⟩
  · rintro m' ⟨m, hm, rfl⟩
    obtain ⟨hmH, -, hmf⟩ := hdat m hm
    exact ⟨CSet.add_mem heH (leWe_mem hmH), (Order.one_le_iff_pos.2 (leWe_pos _)).trans le_add_self,
      (add_lt_add_iff_left e).2 (leWe_lt hmf)⟩
  · intro y hyH hy
    rcases lt_or_ge y e with hye | hye
    · exact ⟨_, ⟨m0, hm0, rfl⟩, hye.trans_le le_self_add⟩
    obtain ⟨v, rfl⟩ := exists_add_of_le hye
    have hvf : v < leWe f := (add_lt_add_iff_left e).1 hy
    rcases eq_or_ne v 0 with rfl | hv0
    · exact ⟨_, ⟨m0, hm0, rfl⟩, by rw [add_zero]; exact lt_add_of_pos_right _ (leWe_pos _)⟩
    have hvH : v ∈ cdHull S l := by
      have h := Ta.taSub_mem (S := S) _ hyH e; rwa [Ordinal.add_sub_cancel] at h
    have htH : sgLW v ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hvH)
    obtain ⟨m, hm, htm⟩ := hA1 _ htH (tuLogW_lt hv0 hvf)
    exact ⟨_, ⟨m, hm, rfl⟩, (add_lt_add_iff_left e).2 (tuWe_step (sgLW_lt v) (Order.add_one_le_of_lt htm))⟩
  · intro z hz
    rw [hTE] at hz
    have hany : ∀ m, Mem m → uaTh S l e < uaTh S l (e + leWe m) := fun m hm => by
      rw [hTm m hm]; exact lt_add_of_pos_right _ (leOe_pos _)
    rcases lt_or_ge z (uaTh S l e) with hze | hze
    · exact ⟨_, ⟨m0, hm0, rfl⟩, hze.trans (hany m0 hm0)⟩
    obtain ⟨w, rfl⟩ := exists_add_of_le hze
    have hwf : w < leOe (uaTh S l f) := (add_lt_add_iff_left _).1 hz
    rcases eq_or_ne w 0 with rfl | hw0
    · exact ⟨_, ⟨m0, hm0, rfl⟩, by rw [add_zero]; exact hany m0 hm0⟩
    obtain ⟨m, hm, hum⟩ := hA2 _ (tuLogO_lt hw0 hwf)
    refine ⟨_, ⟨m, hm, rfl⟩, ?_⟩
    rw [hTm m hm]
    exact (add_lt_add_iff_left _).2 (tuOe_step (roLt_Oe_log w) (Order.add_one_le_of_lt hum))
  · rintro Q hQ m' h ⟨m, hm, rfl⟩ h1 h2 hh
    obtain ⟨heQ, h', hh'1, hh'2, hh'c⟩ := tuHead hQ hd h1 h2 hh
    exact LeCl.add heQ (tuWe_clX hQ (hA3 Q hQ m h' hm hh'1 hh'2 hh'c))

/-- **`e + W^f` from the members of `f` indexed by the codes** (`W^f ∣ e`): members `e + W^{M c}`. -/
theorem uaMB_lift {e f : Ordinal.{0}} (heH : e ∈ cdHull S l) (hfH : f ∈ cdHull S l) (hd : leWe f ∣ e)
    (hlt : e + leWe f < uaGam) (hB : UaMB S l f) : UaMB S l (e + leWe f) := by
  obtain ⟨M, Mh, hM, hMh, hB0, hB1, hB2, hB3⟩ := hB
  have hTE := uaAddW hl hX heH hfH hd hlt
  have hTedvd : leOe (uaTh S l f) ∣ uaTh S l e :=
    uaDvd hl hX e heH (le_self_add.trans_lt hlt) f hfH hd
  refine ⟨fun c => e + leWe (M c), fun c => uaTh S l e + leOe (Mh c),
    fun a b h => (add_le_add_iff_left _).2 (leWe_mono (hM h)),
    fun a b h => (add_le_add_iff_left _).2 (leOe_mono (hMh h)), ?_, ?_, ?_, ?_⟩
  · intro c hc hc1' hcW
    obtain ⟨hMH, -, hMf, hTM, hMhT⟩ := hB0 c hc hc1' hcW
    refine ⟨CSet.add_mem heH (leWe_mem hMH), (Order.one_le_iff_pos.2 (leWe_pos _)).trans le_add_self,
      (add_lt_add_iff_left e).2 (leWe_lt hMf), ?_, ?_⟩
    · rw [uaAddW hl hX heH hMH ((leWe_dvd hMf.le).trans hd)
        (((add_le_add_iff_left e).2 (leWe_mono hMf.le)).trans_lt hlt), hTM]
    · rw [hTE]; exact (add_lt_add_iff_left _).2 (leOe_lt hMhT)
  · intro Q hQ hQ1 w hw hwE
    have hM1lt : e < e + leWe (M 1) := lt_add_of_pos_right _ (leWe_pos _)
    rcases lt_or_ge w e with hwe | hwe
    · exact ⟨1, gg_one_lt_of_SC hQ, hwe.trans hM1lt⟩
    obtain ⟨x, rfl⟩ := exists_add_of_le hwe
    have hx : x < leWe f := (add_lt_add_iff_left e).1 hwE
    rcases eq_or_ne x 0 with rfl | hx0
    · exact ⟨1, gg_one_lt_of_SC hQ, by rw [add_zero]; exact hM1lt⟩
    have hxc := tuModW hQ hd hx hw
    obtain ⟨c', hc'Q, htc'⟩ := hB1 Q hQ hQ1 _ (swCl_cnf hQ hxc).1 (tuLogW_lt hx0 hx)
    exact ⟨c', hc'Q, (add_lt_add_iff_left e).2 (tuWe_step (sgLW_lt x) (Order.add_one_le_of_lt htc'))⟩
  · intro Q hQ w hw hwE
    rw [hTE] at hwE
    have hM1lt : uaTh S l e < uaTh S l e + leOe (Mh 1) := lt_add_of_pos_right _ (leOe_pos _)
    rcases lt_or_ge w (uaTh S l e) with hwe | hwe
    · exact ⟨1, gg_one_lt_of_SC hQ, hwe.trans hM1lt⟩
    obtain ⟨x, rfl⟩ := exists_add_of_le hwe
    have hx : x < leOe (uaTh S l f) := (add_lt_add_iff_left _).1 hwE
    rcases eq_or_ne x 0 with rfl | hx0
    · exact ⟨1, gg_one_lt_of_SC hQ, by rw [add_zero]; exact hM1lt⟩
    have hxc := tuModO hQ hTedvd hx hw
    have huc : LeCl (Om 1) Q (log ω x / Om 1) := sjCl_div hQ tnSC1 _ (leClDec hQ tnSC1 x hxc).2
    obtain ⟨c', hc'Q, huc'⟩ := hB2 Q hQ _ huc (tuLogO_lt hx0 hx)
    exact ⟨c', hc'Q, (add_lt_add_iff_left _).2 (tuOe_step (roLt_Oe_log x) (Order.add_one_le_of_lt huc'))⟩
  · intro Q hQ c h hc1' hcQ h1 h2 hh
    obtain ⟨heQ, h', hh'1, hh'2, hh'c⟩ := tuHead hQ hd h1 h2 hh
    exact LeCl.add heQ (tuWe_clX hQ (hB3 Q hQ c h' hc1' hcQ hh'1 hh'2 hh'c))

/-- **EVERY LIMIT EXPONENT `e + r < ε_{G+1}` OF `H_λ` (`W^{log_W r + 1} ∣ e`) HAS A MEMBER SYSTEM.** -/
theorem uaMS : ∀ r, r ∈ cdHull S l → IsSuccLimit r → ∀ e, e ∈ cdHull S l →
    e + r < uaE → leWe (sgLW r + 1) ∣ e → UaMA S l (e + r) ∨ UaMB S l (e + r) := by
  intro r
  induction r using WellFoundedLT.induction with
  | ind r IH =>
  intro hrH hrlim e heH hlt hd
  have hltG : e + r < uaGam := hlt.trans uaE_lt_Gam
  have hrE : r < uaE := le_add_self.trans_lt hlt
  have hr0 : 0 < r := hrlim.bot_lt
  by_cases hrs : sgLW r < r
  swap
  · -- a node: `r < G` by `Tx.txMS`, or `r = G`
    have hWr : leWe r = r := uaW_fix hr0 hrs
    have hsr : sgLW r = r := le_antisymm (txSg_le r) (not_lt.1 hrs)
    have hdr : leWe r ∣ e := (leWe_dvd (le_self_add : r ≤ r + 1)).trans (by rw [← hsr]; exact hd)
    have hlt' : e + leWe r < uaGam := by rw [hWr]; exact hltG
    rw [← hWr]
    rcases lt_or_ge r (veblen (Om (1 + 1)) 1) with hrG | hrG
    · have hMS := txMS hl hX r hrH hrlim 0 (CSet.zero_mem _ _) (by rwa [zero_add]) (dvd_zero _)
      rw [zero_add] at hMS
      rcases hMS with hA | hB
      · exact Or.inl (uaMA_lift hl hX heH hrH hdr hlt' (uaMA_of_tu hl hX hrG hA))
      · exact Or.inr (uaMB_lift hl hX heH hrH hdr hlt' (uaMB_of_tu hl hX hrG hB))
    · have hrG' := uaNode_G hrG hrE hrs
      have hB := uaMB_G (S := S) hl hX
      rw [← hrG'] at hB
      exact Or.inr (uaMB_lift hl hX heH hrH hdr hlt' hB)
  obtain ⟨hfH, -, hcc, hc1, hcW, hr'H, hr'f, hrdec⟩ := uaBase hl hX hrH hr0
  have hfr : sgLW r < r := hrs
  set f := sgLW r with hf_def
  set c := r / leWe f with hc_def
  set r' := r % leWe f with hr'_def
  have hcH : c ∈ cdHull S l := (ldHull_iff hl hX hcW).2 hcc
  have hdf : leWe f ∣ e := (leWe_dvd (le_self_add : f ≤ f + 1)).trans hd
  rcases eq_or_ne r' 0 with hr'0 | hr'0
  · have hrc : r = leWe f * c := by rw [hr'0, add_zero] at hrdec; exact hrdec
    rcases zero_or_succ_or_isSuccLimit c with h0 | ⟨c1, hcs⟩ | hclim
    · exact absurd hc1 (by rw [h0]; exact not_le.2 zero_lt_one)
    · rw [succ_eq_add_one] at hcs
      have hc1W : c1 < Om (1 + 1) := (lt_add_one c1).trans (hcs ▸ hcW)
      have hc1c : GxCl (upsilon l) (ldAtR S l) c1 := rqCode_pred hl hX (hcs ▸ hcc) (hcs ▸ hcW)
      have hc1H : c1 ∈ cdHull S l := (ldHull_iff hl hX hc1W).2 hc1c
      have he2H : e + leWe f * c1 ∈ cdHull S l := CSet.add_mem heH (leMulWe_mem hfH hc1H)
      have he2r : e + leWe f * c1 + leWe f = e + r := by rw [hrc, ← hcs, mul_add_one, add_assoc]
      have hd2 : leWe f ∣ e + leWe f * c1 := dvd_add hdf (dvd_mul_right _ _)
      have hlt2 : e + leWe f * c1 + leWe f < uaGam := he2r ▸ hltG
      rw [← he2r]
      rcases zero_or_succ_or_isSuccLimit f with hf0 | ⟨f1, hfs⟩ | hflim
      · exfalso
        have hrc1 : r = c1 + 1 := by rw [hrc, hf0, leWe_zero, one_mul, ← hcs]
        have h := hrlim.succ_lt (show c1 < r from hrc1 ▸ lt_add_one c1)
        rw [Order.succ_eq_add_one, ← hrc1] at h
        exact lt_irrefl _ h
      · rw [succ_eq_add_one] at hfs
        have hf1H : f1 ∈ cdHull S l := mem_of_add_one_mem (hfs ▸ hfH)
        rw [← hfs] at hd2 hlt2 he2H ⊢
        exact Or.inr (uaMB_succ hl hX he2H hf1H hd2 hlt2)
      · have hMSf := IH f hfr hfH hflim 0 (CSet.zero_mem _ _) (by rw [zero_add]; exact hfr.trans hrE)
          (dvd_zero _)
        rw [zero_add] at hMSf
        rcases hMSf with hA | hB
        · exact Or.inl (uaMA_lift hl hX he2H hfH hd2 hlt2 hA)
        · exact Or.inr (uaMB_lift hl hX he2H hfH hd2 hlt2 hB)
    · rw [hrc] at hltG ⊢
      exact Or.inl (uaMA_coef hl hX heH hfH hcc hclim hcW hd hltG)
  · have hr'lim : IsSuccLimit r' := by
      rcases zero_or_succ_or_isSuccLimit r' with h0 | ⟨r1, hr1⟩ | hl'
      · exact absurd h0 hr'0
      · exfalso
        rw [succ_eq_add_one] at hr1
        have hr2 : r = leWe f * c + r1 + 1 := by rw [add_assoc, hr1]; exact hrdec
        have h := hrlim.succ_lt (show leWe f * c + r1 < r from hr2 ▸ lt_add_one _)
        rw [Order.succ_eq_add_one, ← hr2] at h
        exact lt_irrefl _ h
      · exact hl'
    have hs' : sgLW r' < f := tuLogW_lt hr'0 hr'f
    have he2 : e + leWe f * c + r' = e + r := by
      conv_rhs => rw [hrdec]
      rw [add_assoc]
    have hr'r : r' < r := hr'f.trans_le (sgLW_le hr0)
    have h := IH r' hr'r hr'H hr'lim (e + leWe f * c) (CSet.add_mem heH (leMulWe_mem hfH hcH))
      (he2 ▸ hlt) ((leWe_dvd (Order.add_one_le_of_lt hs')).trans (dvd_add hdf (dvd_mul_right _ _)))
    rwa [he2] at h

end Main

end Googology.Trans.PoR.InaccPsi.R2.Ua

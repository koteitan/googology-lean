import Googology.Trans.PoR.InaccPsi.R2.QdDS
import Googology.Trans.PoR.InaccPsi.R2.QtCnt
import Googology.Trans.PoR.InaccPsi.R2.QcRS

/-!
# QdRS: A READING SYSTEM BELOW `B₃` (ATOMS OF `qtU S`), ITS LAYERS AND THEIR READINGS

`Qc.QbRS` with the atom system `Qt.qtU S` (bound `θ`) in place of `Qc.qcU`, the indices below `B₃ = Qd.qdB`, and the
readings of the atoms `Γ_{Ω₁+1+c}` in the bound `Qc.YBd` (a point of a generic level, or of a Veblen level under
`Qd.QdImgH`).  The same recursion (`Yw.ywLadB` at a successor, `Yw.ywLimB` at a limit) builds the layer of every code
with its reading; `ZbTh (qtU S)` is `Qt.qtU_th`.

* `qd_gcG_lt_B3` (**`Γ_{Ω₁+1+c} < B₃` for `c < B₃`**: `B₃` is a fixed point of `Hᵛ_0 = H_0`), `QdRS`, `QdRS.St`,
  `QdRS.stBase`, `QdRS.stSuccH`, `QdRS.stSucc`, `QdRS.stLimF`, `QdRS.stLim`, `QdRS.lay`, `QdRS.layAt`
  (**`Zm.ZmLayA (qtU S) S c` for every code with gate below `K`**).

No new axiom.  New definitions: `QdRS`, `QdRS.St`, `QdRS.stBase`, `QdRS.stSucc`, `QdRS.stLimF`, `QdRS.stLim`,
`QdRS.lay`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Ge
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Zb
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Zm Googology.Trans.PoR.InaccPsi.R2.Qc
  Googology.Trans.PoR.InaccPsi.R2.Qt

/-- **`Γ_{Ω₁+1+c} < B₃`** for `c < B₃` (`B₃` is a fixed point of `Hᵛ_0 = H_0 = Γ`). -/
theorem qd_gcG_lt_B3 (S : InaccSeq.{0}) {c : Ordinal.{0}} (hc : c < qdB) : gcG c < qdB := by
  have h0G : (0 : Ordinal.{0}) < qdG2 := qd_Om2_pos.trans qd_Om2_lt_G2
  have h0E : (0 : Ordinal.{0}) < ucE := uc_SC_Om2.1.trans ucE_gt
  have h0O : (0 : Ordinal.{0}) < OmTwo := uc_SC_Om2.1
  have h1' : Om 1 < qdB := by rw [← Rj.rj_Om1]; exact qdB_gt
  have hqd : qdH 0 qdB = qdB := qdB_spec h0G (by
    have : qdFold id 0 = 0 := by rw [qdFold, dif_neg (fun h => absurd h.1 (not_lt.2 h0O.le)), if_pos h0O]; rfl
    rw [this]; exact qdB_SC.1)
  have hH : ucH 0 qdB = qdB := by
    rw [← (Vd.vd_lev_uc (S := S) h0E qdB_SC h1').1, ← qdH_eq_ul S h0G]; exact hqd
  have hG : gamma qdB = qdB := by
    rw [← Rh.rhF_zero]
    exact (ucH_fix_iff_F h0O (max_lt qdB_gt qdB_SC.1)).1 hH
  have h1 : Om1 + 1 + c < qdB := qdB_SC.isPrincipal (qdB_SC.isSuccLimit.add_one_lt qdB_gt) hc
  rw [tf_gcG]
  calc gamma (Om1 + 1 + c) < gamma qdB := gamma_lt_gamma.2 h1
    _ = qdB := hG

/-- **A reading system past `B_Γ`** for the atom indices `c ∈ [c₀, Bd)`, `Bd ≤ B₃`, atoms of `qtU S`. -/
structure QdRS (S : InaccSeq.{0}) where
  c0 : Ordinal.{0}
  Bd : Ordinal.{0}
  gt : Ordinal.{0} → Ordinal.{0}
  R : Ordinal.{0} → Ordinal.{0} → Ordinal.{0}
  L0 : GdB
  c0_ne : c0 ≠ 0
  c0_lt : c0 < Bd
  Bd_X : Bd ≤ qdB
  L0_g : L0.g = gt c0
  L0_E : ∀ x, InE x → x < Om1 → L0.K.E x = gq (R c0 x) x
  L0_top : ∀ y, SC y → y < Om 1 → gt c0 < y → L0.K.E y = gxTh y ((qtU S).At y) (gcG c0)
  L0_poly : ZbPolyG (qtU S) L0.K.sys (gcG c0)
  RT : ∀ c x, InE x → x < Om1 → c0 ≤ c → c < Bd → gt c < x →
    R c x ∈ Tset x ∧ R c x < Om1 ∧ YBd x (gq (R c x) x)
  mono : ∀ b c x, InE x → x < Om1 → c0 ≤ b → b < c → c < Bd → gt b < x → gt c < x → R b x < R c x
  succ : ∀ b x, c0 ≤ b → R (b + 1) x = R b x + 1
  gt_le_succ : ∀ b, gt b ≤ gt (b + 1)
  lim_R : ∀ c x, IsSuccLimit c → c0 < c → c < Bd → InE x → x < Om1 → gt c < x →
    IsSuccLimit (R c x) ∧ ∃ σ, σ < R c x ∧ R c x < gq σ x
  cof : ∀ c x, IsSuccLimit c → c0 < c → c < Bd → InE x → x < Om1 → gt c < x → ∀ ν < R c x,
    ∃ b, c0 ≤ b ∧ b < c ∧ gt b < x ∧ ν ≤ R b x
  ex : ∀ σ ρ c, Bases σ ρ → c0 ≤ c → c < Bd → gt c < σ →
    R c ρ ∈ TB ρ σ ∧ Googology.Trans.PoR.InaccPsi.R2.pi σ ρ (R c ρ) = R c σ
  cover : ∀ c Z, IsSuccLimit c → c0 < c → c < Bd → SC Z → Z < Om 1 → gt c < Z → ∀ d,
    GxCl Z ((qtU S).At Z) d → d < gcG c → ∃ b, c0 ≤ b ∧ b < c ∧ gt b < Z ∧ d < gcG b
  cl : ∀ c Z, c0 ≤ c → c < Bd → SC Z → gt c < Z → GxCl Z ((qtU S).At Z) (gcG c)
  D_le : ∀ c x, InE x → x < Om1 → c0 < c → c < Bd → gt c < x → ywV 1 0 x ≤ R c x
  BG_top : ∀ y, SC y → y < Om 1 → ywBGB.K.E y = gxTh y ((qtU S).At y) tfBG
  BG_poly : ZbPolyG (qtU S) ywBGB.K.sys tfBG
  BG_c0 : tfBG ≤ gcG c0

namespace QdRS

variable {S : InaccSeq.{0}} (RS : QdRS S)

/-- **A layer of the code `c` with its reading statement**: gate `gt c`, top `ϑˣ(Ω₁·Ω₁ + R(c)(x))` above the
gate, reading `Γ_{Ω₁+1+c}` with the atoms of `zbU`, terms for every code below it. -/
def St (c : Ordinal.{0}) : Type 2 :=
  {L : GdB // L.g = RS.gt c ∧ (∀ x, InE x → x < Om1 → RS.gt c < x → L.K.E x = gq (RS.R c x) x) ∧
    (∀ y, SC y → y < Om 1 → RS.gt c < y → L.K.E y = gxTh y ((qtU S).At y) (gcG c)) ∧
    ZbPolyG (qtU S) L.K.sys (gcG c)}

/-- The base. -/
noncomputable def stBase (c : Ordinal.{0}) (hE : c = RS.c0) : RS.St c :=
  ⟨RS.L0, by rw [hE, RS.L0_g], fun x hx hx1 _ => by rw [hE]; exact RS.L0_E x hx hx1,
    fun y hy hy1 h => by subst hE; exact RS.L0_top y hy hy1 h, by rw [hE]; exact RS.L0_poly⟩

/-- The ladder hypothesis for the successor `b + 1`. -/
theorem stSuccH {b : Ordinal.{0}} (hb : RS.c0 ≤ b) (hbB : b < RS.Bd) (s : RS.St b) :
    YwLH s.1 (fun x => RS.R b x + 1) := by
  have hg : ∀ x, s.1.g < x → RS.gt b < x := fun x h => by rw [← s.2.1]; exact h
  refine ⟨fun x hx hx1 h => ?_, fun x hx hx1 h => ?_, fun x hx hx1 h j hjT hj => ?_, fun x hx hx1 h => ?_,
    fun x hx hx1 h => ?_, fun σ ρ hB h => ?_⟩
  · obtain ⟨hT, h1, -⟩ := RS.RT b x hx hx1 hb hbB (hg x h)
    exact Xk.xk_succT hx hx1 hT h1
  · obtain ⟨hT, h1, -⟩ := RS.RT b x hx hx1 hb hbB (hg x h)
    rw [s.2.2.1 x hx hx1 (hg x h)]
    exact Order.add_one_le_of_lt (gmq_gt hx hx1 hT h1)
  · obtain ⟨hT, h1, -⟩ := RS.RT b x hx hx1 hb hbB (hg x h)
    rw [s.2.2.1 x hx hx1 (hg x h)]
    exact gmq_mono hx hx1 hT h1 (Order.lt_add_one_iff.1 hj)
  · obtain ⟨hT, h1, -⟩ := RS.RT b x hx hx1 hb hbB (hg x h)
    obtain ⟨hT', h1'⟩ := Xk.xk_succT hx hx1 hT h1
    rw [s.2.2.1 x hx hx1 (hg x h)]
    exact gmq_lt hx hx1 hT' h1' (lt_add_one _)
  · obtain ⟨hT, h1, hX⟩ := RS.RT b x hx hx1 hb hbB (hg x h)
    obtain ⟨hT', h1'⟩ := Xk.xk_succT hx hx1 hT h1
    have hRb : YBd x (RS.R b x) := yBd_mono (gmq_gt hx hx1 hT h1).le hX
    have h1b : YBd x 1 := yBd_of_qc <| qcBd_of_X hx ((Lu.lu_one_lt_E hx).trans (ywX_facts hx hx1).2.1)
    exact yBd_gq hx hx1 hT' (yBd_add hx hx1 hRb h1b)
  · have h1σ : (1 : Ordinal.{0}) < σ := lu_one_lt_E hB.1
    obtain ⟨h1, h2⟩ := RS.ex σ ρ b hB hb hbB (hg σ h)
    obtain ⟨h3, h4⟩ := pi_add hB h1 (mem_TB_of_lt hB h1σ)
    exact ⟨h3, by rw [h4, h2, pi_lt hB h1σ]⟩

/-- **The successor step**: the ladder over the layer of `b`. -/
noncomputable def stSucc (b : Ordinal.{0}) (hb : RS.c0 ≤ b) (hc : b + 1 < RS.Bd) (s : RS.St b) : RS.St (b + 1) := by
  have hbB : b < RS.Bd := (lt_add_one b).trans hc
  have hgle : s.1.g ≤ RS.gt (b + 1) := by rw [s.2.1]; exact RS.gt_le_succ b
  have hg : ∀ y, RS.gt (b + 1) < y → s.1.g < y := fun y h => hgle.trans_lt h
  have H := RS.stSuccH hb hbB s
  have hcl : ∀ Z, SC Z → s.1.g < Z → GxCl Z ((qtU S).At Z) (gcG b) := fun Z hZ h =>
    RS.cl b Z hb hbB hZ (by rw [← s.2.1]; exact h)
  have hKE : ∀ y, SC y → y < Om 1 → s.1.g < y → s.1.K.E y = gxTh y ((qtU S).At y) (gcG b) := fun y hy hy1 h =>
    s.2.2.2.1 y hy hy1 (by rw [← s.2.1]; exact h)
  refine ⟨(ywLadB s.1 (fun x => RS.R b x + 1) H).mono hgle, rfl, fun x _ _ _ => ?_, fun y hy hy1 h => ?_, ?_⟩
  · show gq (RS.R b x + 1) x = gq (RS.R (b + 1) x) x
    rw [RS.succ b x hb]
  · show (ywLadB s.1 (fun x => RS.R b x + 1) H).K.E y = _
    rw [zbLad_top hcl hKE H hy hy1 (hg y h), gc_cQs]
  · have hP := (zbLad_poly hcl (gcG_Om1_lt _).le hKE H qtU_th s.2.2.2.2).mono hgle
    rw [gc_cQs] at hP
    exact hP

/-- **The union data at a limit code `c`**: the layers of the codes `b ∈ [c₀, c)`, target `ϑˣ(Ω₁·Ω₁ + R(c)(x))`. -/
noncomputable def stLimF (c : Ordinal.{0}) (hl : IsSuccLimit c) (hc0 : RS.c0 < c) (hc : c < RS.Bd)
    (IH : ∀ b, RS.c0 ≤ b → b < c → RS.St b) : YwUF (RS.gt c) where
  I := Option {b : Ordinal.{0} // RS.c0 ≤ b ∧ b < c}
  K := fun i => Option.elim i ywBGB fun b => (IH b.1 b.2.1 b.2.2).1
  gi := fun i => Option.elim i 0 fun b => RS.gt b.1
  i0 := none
  g_le := fun i => by
    cases i with
    | none => exact le_of_eq ywBGB_g
    | some b => exact (IH b.1 b.2.1 b.2.2).2.1.le
  gi0 := rfl
  T := fun x => gq (RS.R c x) x
  T_E := fun x hx hx1 hg => (geq_facts hx hx1 (RS.RT c x hx hx1 hc0.le hc hg).1
    (RS.RT c x hx hx1 hc0.le hc hg).2.1).2.2.2.1
  T_mem := fun x hx hx1 hg => (geq_facts hx hx1 (RS.RT c x hx hx1 hc0.le hc hg).1
    (RS.RT c x hx hx1 hc0.le hc hg).2.1).1
  T_gt := fun x hx hx1 hg => (geq_facts hx hx1 (RS.RT c x hx hx1 hc0.le hc hg).1
    (RS.RT c x hx hx1 hc0.le hc hg).2.1).2.1
  T_X := fun x hx hx1 hg => (RS.RT c x hx hx1 hc0.le hc hg).2.2
  E_lt := fun i x hx hx1 hg hgb => by
    obtain ⟨hT, h1, -⟩ := RS.RT c x hx hx1 hc0.le hc hg
    cases i with
    | none =>
      show ywBGB.K.E x < gq (RS.R c x) x
      rw [ywBGB_E]
      exact (RS.D_le c x hx hx1 hc0 hc hg).trans_lt (gmq_gt hx hx1 hT h1)
    | some b =>
      show (IH b.1 b.2.1 b.2.2).1.K.E x < gq (RS.R c x) x
      rw [(IH b.1 b.2.1 b.2.2).2.2.1 x hx hx1 hgb]
      exact gmq_lt hx hx1 hT h1 (RS.mono b.1 c x hx hx1 b.2.1 b.2.2 hc hgb hg)
  cof := fun x hx hx1 hg v hv => by
    obtain ⟨hT, h1, -⟩ := RS.RT c x hx hx1 hc0.le hc hg
    obtain ⟨hlR, hσ⟩ := RS.lim_R c x hl hc0 hc hx hx1 hg
    obtain ⟨ν, hν, hvν⟩ := zb_lt_lim_iff hx hx1 hlR hT h1 hσ v hv
    obtain ⟨b, h1b, h2b, h3b, h4b⟩ := RS.cof c x hl hc0 hc hx hx1 hg ν hν
    obtain ⟨hTb, h1b', -⟩ := RS.RT b x hx hx1 h1b (h2b.trans hc) h3b
    refine ⟨some ⟨b, h1b, h2b⟩, h3b, ?_⟩
    show v < (IH b h1b h2b).1.K.E x
    rw [(IH b h1b h2b).2.2.1 x hx hx1 h3b]
    exact hvν.trans_le (gmq_mono hx hx1 hTb h1b' h4b)
  pi := fun σ ρ _ _ hB hg => by
    have h0σ : (0 : Ordinal.{0}) < σ := hB.1.pos
    obtain ⟨hRT, hRπ⟩ := RS.ex σ ρ c hB hc0.le hc hg
    have hR1 : RS.R c ρ < Om1 :=
      (RS.RT c ρ hB.2.1 hB.2.2.2 hc0.le hc (hg.trans hB.2.2.1)).2.1
    have h := ywV_pi hB (mem_TB_of_lt hB h0σ) (hB.2.1.pos.trans hB.2.2.2) hRT hR1
    rw [pi_lt hB h0σ, hRπ, ywV_zero, ywV_zero] at h
    exact h

/-- **The limit step**: the union (with the layer of `B_Γ` for the constants). -/
noncomputable def stLim (c : Ordinal.{0}) (hl : IsSuccLimit c) (hc0 : RS.c0 < c) (hc : c < RS.Bd)
    (IH : ∀ b, RS.c0 ≤ b → b < c → RS.St b) : RS.St c := by
  set F := RS.stLimF c hl hc0 hc IH with hF
  have hres := zbUnion_codes (A := qtU S) F (fun i => Option.elim i tfBG fun b => gcG b.1) (Tc := gcG c)
    (fun i y hy hy1 hi => by
      cases i with
      | none => exact RS.BG_top y hy hy1
      | some b => exact (IH b.1 b.2.1 b.2.2).2.2.2.1 y hy hy1 hi)
    (fun i => by
      cases i with
      | none => exact RS.BG_poly
      | some b => exact (IH b.1 b.2.1 b.2.2).2.2.2.2)
    (fun i => by
      cases i with
      | none => exact RS.BG_c0.trans (gcG_le hc0.le)
      | some b => exact gcG_le b.2.2.le)
    (fun Z hZ hZ1 hgZ d hd hdT => by
      obtain ⟨b, h1, h2, h3, h4⟩ := RS.cover c Z hl hc0 hc hZ hZ1 hgZ d hd hdT
      exact ⟨some ⟨b, h1, h2⟩, h3, h4⟩)
  exact ⟨ywLimB F, rfl, fun _ _ _ _ => rfl, hres.1, hres.2⟩

/-- **THE LAYER OF EVERY CODE `c ∈ [c₀, Bd)`**, with its reading statement. -/
noncomputable def lay (c : Ordinal.{0}) : RS.c0 ≤ c → c < RS.Bd → RS.St c :=
  Ordinal.limitRecOn (motive := fun c => RS.c0 ≤ c → c < RS.Bd → RS.St c) c
    (fun h _ => absurd (le_zero_iff.1 h) RS.c0_ne)
    (fun b ih h hc => if hb : RS.c0 ≤ b then RS.stSucc b hb hc (ih hb ((lt_add_one b).trans hc))
      else RS.stBase (b + 1) (le_antisymm (Order.add_one_le_of_lt (not_le.1 hb)) h))
    (fun c hl ih h hc => if hE : c = RS.c0 then RS.stBase c hE
      else RS.stLim c hl (lt_of_le_of_ne h (Ne.symm hE)) hc (fun b hb1 hb2 => ih b hb2 hb1 (hb2.trans hc)))

/-- **`ZmLayA (qtU S) S c` for every code `c ∈ [c₀, Bd)` with gate below `K`.** -/
theorem layAt {c : Ordinal.{0}} (h1 : RS.c0 ≤ c) (h2 : c < RS.Bd) (hg : RS.gt c < Td.tdK S) :
    ZmLayA (qtU S) S c := by
  obtain ⟨L, hLg, hLE, hLtop, hLP⟩ := RS.lay c h1 h2
  refine ⟨L, gcG c, le_rfl, by rw [hLg]; exact hg, ((qd_gcG_lt_B3 S (h2.trans_le RS.Bd_X)).trans_le qd_B3_le_th).le, (gcG_Om1_lt _).le,
    Low.opow_eq_self_of_SC (gcG_SC _), fun y hy hy1 h => hLtop y hy hy1 (by rw [← hLg]; exact h), hLP,
    fun Z hZ hKZ => RS.cl c Z h1 h2 hZ (hg.trans_le hKZ), fun x hx hx1 h => ?_⟩
  have h' : RS.gt c < x := by rw [← hLg]; exact h
  rw [hLE x hx hx1 h']
  obtain ⟨hT, h1', -⟩ := RS.RT c x hx hx1 h1 h2 h'
  exact gmq_eN_lt hx hx1 hT h1'

end QdRS

end Googology.Trans.PoR.InaccPsi.R2.Qd

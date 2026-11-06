import Googology.Trans.PoR.InaccPsi.R2.ZbUn

/-!
# ZbRS: A READING SYSTEM PAST `B_Γ` (ATOMS OF `zbU`), ITS LAYERS AND THEIR READINGS, AND `ZbDirect` FROM IT

`Yr.YrRS` (atoms of a `Gs.GsCS`) ends below `B_Γ` (`Zb.zbYrRS_lt_BG`).  `ZbRS` is a reading of the atom indices
`c ∈ [c₀, Bd)` (`ϑˣ(Ω₁·Ω₁ + R(c)(x))` reads `Γ_{Ω₁+1+c}`) with a base layer at `c₀` reading `Γ_{Ω₁+1+c₀}` with the
atoms of `Zb.zbU`, gates, the order, `R(b+1) = R(b) + 1`, cofinality and the absence of a fixed point at limit codes
(`ν ↦ ϑˣ(Ω₁·Ω₁ + ν)` continuous there, `Zb.zb_lt_lim_iff`), Lemma EXACT, the cover of the codes below a limit atom
(`Zb.zbCover`) and the atom `Γ_{Ω₁+1+c}` a code above its gate.  One recursion on `c` builds the layer of every code
together with its reading: successors by the ladder `Yw.ywLadB` (`Zb.zbLad_top`, `Zb.zbLad_poly`), limits by the
union `Yw.ywLimB` (top witness from Lemma IMG; `Zb.zbUnion_codes`).

* `ZbRS`, `ZbRS.St` (a layer of the code `c` WITH its reading statement), `ZbRS.stBase`, `ZbRS.stSucc`,
  `ZbRS.stLimF`, `ZbRS.stLim`, `ZbRS.lay` (**THE LAYER OF EVERY CODE `c ∈ [c₀, Bd)`**);
* `ZbRS.layAt` (**`ZbLayAt S c` for every code with gate below `K`**), `ZbRS.direct` (**`ZbDirect S Bd`** when
  `c₀ = B_Γ + 1` and every gate is below `K`).

No new axiom.  New definitions: `ZbRS`, `ZbRS.St`, `ZbRS.stBase`, `ZbRS.stSuccH` (a proof), `ZbRS.stSucc`,
`ZbRS.stLimF`, `ZbRS.stLim`, `ZbRS.lay`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Ge
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gb

/-- **A reading system past `B_Γ`** for the atom indices `c ∈ [c₀, Bd)`, atoms of `zbU`. -/
structure ZbRS where
  c0 : Ordinal.{0}
  Bd : Ordinal.{0}
  gt : Ordinal.{0} → Ordinal.{0}
  R : Ordinal.{0} → Ordinal.{0} → Ordinal.{0}
  L0 : GdB
  c0_ne : c0 ≠ 0
  c0_lt : c0 < Bd
  Bd_X : Bd ≤ tlX
  L0_g : L0.g = gt c0
  L0_E : ∀ x, InE x → x < Om1 → L0.K.E x = gq (R c0 x) x
  L0_top : ∀ y, SC y → y < Om 1 → gt c0 < y → L0.K.E y = gxTh y (zbU.At y) (gcG c0)
  L0_poly : ZbPolyG zbU L0.K.sys (gcG c0)
  RT : ∀ c x, InE x → x < Om1 → c0 ≤ c → c < Bd → gt c < x →
    R c x ∈ Tset x ∧ R c x < Om1 ∧ gq (R c x) x < ywX x
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
    GxCl Z (zbU.At Z) d → d < gcG c → ∃ b, c0 ≤ b ∧ b < c ∧ gt b < Z ∧ d < gcG b
  cl : ∀ c Z, c0 ≤ c → c < Bd → SC Z → gt c < Z → GxCl Z (zbU.At Z) (gcG c)
  D_le : ∀ c x, InE x → x < Om1 → c0 < c → c < Bd → gt c < x → ywV 1 0 x ≤ R c x
  BG_top : ∀ y, SC y → y < Om 1 → ywBGB.K.E y = gxTh y (zbU.At y) tfBG
  BG_poly : ZbPolyG zbU ywBGB.K.sys tfBG
  BG_c0 : tfBG ≤ gcG c0

namespace ZbRS

variable (RS : ZbRS)

/-- **A layer of the code `c` with its reading statement**: gate `gt c`, top `ϑˣ(Ω₁·Ω₁ + R(c)(x))` above the
gate, reading `Γ_{Ω₁+1+c}` with the atoms of `zbU`, terms for every code below it. -/
def St (c : Ordinal.{0}) : Type 2 :=
  {L : GdB // L.g = RS.gt c ∧ (∀ x, InE x → x < Om1 → RS.gt c < x → L.K.E x = gq (RS.R c x) x) ∧
    (∀ y, SC y → y < Om 1 → RS.gt c < y → L.K.E y = gxTh y (zbU.At y) (gcG c)) ∧
    ZbPolyG zbU L.K.sys (gcG c)}

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
    obtain ⟨hXT, hxX, hX1, hXE⟩ := ywX_facts hx hx1
    have hRX : RS.R b x < ywX x := (gmq_gt hx hx1 hT h1).trans hX
    rw [← ywV_zero]
    exact Qc.qcBd_of_X hx (ywV_lt_X hx hx1 (mem_T_of_le hx hx1 zero_le) (hx.pos.trans hx1) hT' h1'
      (hx.pos.trans hxX) ((ev_isSuccLimit_of_inE hXE).add_one_lt hRX))
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
  have hcl : ∀ Z, SC Z → s.1.g < Z → GxCl Z (zbU.At Z) (gcG b) := fun Z hZ h =>
    RS.cl b Z hb hbB hZ (by rw [← s.2.1]; exact h)
  have hKE : ∀ y, SC y → y < Om 1 → s.1.g < y → s.1.K.E y = gxTh y (zbU.At y) (gcG b) := fun y hy hy1 h =>
    s.2.2.2.1 y hy hy1 (by rw [← s.2.1]; exact h)
  refine ⟨(ywLadB s.1 (fun x => RS.R b x + 1) H).mono hgle, rfl, fun x _ _ _ => ?_, fun y hy hy1 h => ?_, ?_⟩
  · show gq (RS.R b x + 1) x = gq (RS.R (b + 1) x) x
    rw [RS.succ b x hb]
  · show (ywLadB s.1 (fun x => RS.R b x + 1) H).K.E y = _
    rw [zbLad_top hcl hKE H hy hy1 (hg y h), gc_cQs]
  · have hP := (zbLad_poly hcl (gcG_Om1_lt _).le hKE H zbU_th s.2.2.2.2).mono hgle
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
  T_X := fun x hx hx1 hg => Qc.qcBd_of_X hx (RS.RT c x hx hx1 hc0.le hc hg).2.2
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
  have hres := zbUnion_codes (A := zbU) F (fun i => Option.elim i tfBG fun b => gcG b.1) (Tc := gcG c)
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

theorem gcG_lt_X {c : Ordinal.{0}} (hc : c < tlX) : gcG c < tlX := by
  rw [tf_gcG]
  have h2 : Om1 + 1 + c < tlX := tlX_SC.isPrincipal (tlX_SC.add_one_lt tlX_gt) hc
  calc gamma (Om1 + 1 + c) < gamma tlX := gamma_lt_gamma.2 h2
    _ = tlX := tl_gamma_X

/-- **`ZbLayAt S c` for every code `c ∈ [c₀, Bd)` with gate below `K`.** -/
theorem layAt (S : InaccSeq.{0}) {c : Ordinal.{0}} (h1 : RS.c0 ≤ c) (h2 : c < RS.Bd) (hg : RS.gt c < Td.tdK S) :
    ZbLayAt S c := by
  obtain ⟨L, hLg, hLE, hLtop, hLP⟩ := RS.lay c h1 h2
  refine ⟨L, gcG c, le_rfl, by rw [hLg]; exact hg, (gcG_lt_X (h2.trans_le RS.Bd_X)).le, (gcG_Om1_lt _).le,
    Low.opow_eq_self_of_SC (gcG_SC _), fun y hy hy1 h => hLtop y hy hy1 (by rw [← hLg]; exact h), hLP,
    fun Z hZ hKZ => RS.cl c Z h1 h2 hZ (hg.trans_le hKZ), fun x hx hx1 h => ?_⟩
  have h' : RS.gt c < x := by rw [← hLg]; exact h
  rw [hLE x hx hx1 h']
  obtain ⟨hT, h1', -⟩ := RS.RT c x hx hx1 h1 h2 h'
  exact gmq_eN_lt hx hx1 hT h1'

/-- **`ZbDirect S Bd`** for a reading system starting at `B_Γ + 1` with every gate below `K`. -/
theorem direct (S : InaccSeq.{0}) (hc0 : RS.c0 = tfBG + 1) (hg : ∀ c, RS.gt c < Td.tdK S) : ZbDirect S RS.Bd := by
  intro B hB1 hB2
  rcases hB1.lt_or_eq with hlt | heq
  · exact RS.layAt S (by rw [hc0]; exact Order.add_one_le_of_lt hlt) hB2 (hg B)
  · rw [← heq]; exact zbLayAt_BG S

end ZbRS

end Googology.Trans.PoR.InaccPsi.R2.Zb

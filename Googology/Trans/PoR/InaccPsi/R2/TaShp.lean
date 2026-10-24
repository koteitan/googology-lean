import Googology.Trans.PoR.InaccPsi.R2.TaTm

/-!
# Shapes with the fine closure law, the lift through `φ(a, ·)`, and shapes through contexts with Veblen nodes

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, codes = `Le.LeCl κ Q`, `TaSm a`: `1 ≤ a < Γ₀`.

The closure law of a shape (`Sc.ScShCl`) is at the scale `Ω₂·g`.  The lift through `φ(a, ·)` needs the **fine
closure law** `TaFine g g* Q`: every code `y < g*` is below `g ζ` for some `ζ < Q` (image: `TaFineH`, below
`ĝ(v+1)`).  A **shape with fine laws** (`TaShp`) is a `Sc.ScShp` whose tops are limits, with both fine laws.

* `taShp_lin` (`ζ ↦ W^F·ζ`), `taShp_pre` (`ζ ↦ E₀ + g ζ`), `taShp_lift` (`ζ ↦ W^{g ζ}`): the fine laws are kept;
* `taShp_veb` (**THE LIFT THROUGH `φ(a, ·)`**: `ζ ↦ φ(a, g ζ)`, image `v ↦ φ(a, ĝ v)`, for `g* > Ω₂`, `ĝ* > Ω₁`:
  closure laws from the fine decomposition `Ta.taCl_dec`, the index from the hull index `Ta.taHull_idx`,
  continuity of the image from that of `ĝ`);
* `TaDatC`, `taOwnC_dat`, `taShp_ctx` (**a shape carried through a context with nodes is a shape**), `taShp_path`
  (**the path shape `ζ ↦ K(W^F·ζ)`**), `taDatE` (the data of `K(y)`), `taOwP_succ` (**the own data of
  `K(Q + 1)`** for every context `K` and term `Q`).

No new axiom.  New definitions: `TaFine`, `TaFineH`, `TaShp`, `TaDatC`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ta

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg

variable {S : InaccSeq.{0}}

/-- **The fine closure law** of `g` with top `g*` at `Q`. -/
def TaFine (g : Ordinal.{0} → Ordinal.{0}) (gs Q : Ordinal.{0}) : Prop :=
  ∀ y, LeCl (Om (1 + 1)) Q y → y < gs → ∃ ζ, ζ < Q ∧ y < g ζ

/-- **The fine closure law of an image** `ĝ` with top `ĝ*` at `Q`. -/
def TaFineH (gh : Ordinal.{0} → Ordinal.{0}) (ghs Q : Ordinal.{0}) : Prop :=
  ∀ y, LeCl (Om 1) Q y → y < ghs → ∃ v, v < Q ∧ y < gh (v + 1)

/-- **A shape with the fine closure laws** (tops are limits). -/
structure TaShp (S : InaccSeq.{0}) (l : Ordinal.{0}) (g gh : Ordinal.{0} → Ordinal.{0})
    (gs ghs bot both : Ordinal.{0}) : Prop where
  shp : ScShp S l g gh gs ghs bot both
  lim : IsSuccLimit gs
  limh : IsSuccLimit ghs
  fine : ∀ Q, SC Q → bot ≤ Q → TaFine g gs Q
  fineh : ∀ Q, SC Q → both ≤ Q → TaFineH gh ghs Q

/-- `Ω^{log_Ω y} ≤ y` for `y ≠ 0`. -/
theorem taOe_log_le {y : Ordinal.{0}} (hy0 : y ≠ 0) : leOe (log ω y / Om 1) ≤ y :=
  (opow_le_opow_right omega0_pos (Ordinal.mul_div_le _ _)).trans (opow_log_le_self ω hy0)

theorem taLim_We {x : Ordinal.{0}} (hx : 0 < x) : IsSuccLimit (leWe x) :=
  isSuccLimit_opow_left isSuccLimit_omega0 (mul_pos ldOm2_SC.1 hx).ne'

theorem taLim_Oe {x : Ordinal.{0}} (hx : 0 < x) : IsSuccLimit (leOe x) :=
  isSuccLimit_opow_left isSuccLimit_omega0 (mul_pos (Om_pos one_ne_zero) hx).ne'

section Cons

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  {g gh : Ordinal.{0} → Ordinal.{0}} {gs ghs bot both : Ordinal.{0}}

include hl hX

/-- **The linear shape `ζ ↦ W^F·ζ`** with the fine laws. -/
theorem taShp_lin {F Fh : Ordinal.{0}} (hFH : F ∈ cdHull S l) (hFm : F ∈ S.CSet 0 bot)
    (hFhm : Fh ∈ S.CSet 0 both) (hFcl : ∀ Q, SC Q → bot ≤ Q → LeCl (Om (1 + 1)) Q F)
    (hFhcl : ∀ Q, SC Q → both ≤ Q → LeCl (Om 1) Q Fh) :
    TaShp S l (fun z => leWe F * z) (fun v => leOe Fh * v) (leWe (F + 1)) (leOe (Fh + 1)) bot both := by
  refine ⟨scShp_lin hl hX hFH hFm hFhm hFcl hFhcl, taLim_We (zero_lt_one.trans_le le_add_self),
    taLim_Oe (zero_lt_one.trans_le le_add_self), ?_, ?_⟩
  · intro Q hQ hQb y hy hlt
    have hW0 : leWe F ≠ 0 := (leWe_pos F).ne'
    have hq := Sw.swCl_divW hQ (hFcl Q hQ hQb) hy
    have hqW : y / leWe F < Om (1 + 1) := (Ordinal.lt_mul_iff_div_lt hW0).1 (by rw [← leWe_succ]; exact hlt)
    refine ⟨y / leWe F + 1, hQ.add_one_lt (LeCl.lt_of_lt hQ hq hqW), ?_⟩
    have := Ordinal.lt_mul_succ_div y hW0
    rwa [Order.succ_eq_add_one] at this
  · intro Q hQ hQb y hy hlt
    have hO0 : leOe Fh ≠ 0 := (leOe_pos Fh).ne'
    have hq : LeCl (Om 1) Q (y / leOe Fh) :=
      Sw.swCl_divOp hQ Ph.ph_SC_Om1 (LeCl.mulK hQ Ph.ph_SC_Om1 _ (hFhcl Q hQ hQb)) y hy
    have hqO : y / leOe Fh < Om 1 := (Ordinal.lt_mul_iff_div_lt hO0).1 (by rw [← leOe_succ]; exact hlt)
    refine ⟨y / leOe Fh, LeCl.lt_of_lt hQ hq hqO, ?_⟩
    have := Ordinal.lt_mul_succ_div y hO0
    rwa [Order.succ_eq_add_one] at this

/-- **The prefix `ζ ↦ E₀ + g ζ`** with the fine laws. -/
theorem taShp_pre {E0 Eh0 : Ordinal.{0}} (h : TaShp S l g gh gs ghs bot both) (hE0H : E0 ∈ cdHull S l)
    (hE0m : E0 ∈ S.CSet 0 bot) (hEh0m : Eh0 ∈ S.CSet 0 both)
    (hE0cl : ∀ Q, SC Q → bot ≤ Q → LeCl (Om (1 + 1)) Q E0) (hEh0cl : ∀ Q, SC Q → both ≤ Q → LeCl (Om 1) Q Eh0) :
    TaShp S l (fun z => E0 + g z) (fun v => Eh0 + gh v) (E0 + gs) (Eh0 + ghs) bot both := by
  refine ⟨sgShp_preG hl hX h.shp hE0H hE0m hEh0m hE0cl hEh0cl, isSuccLimit_add E0 h.lim,
    isSuccLimit_add Eh0 h.limh, ?_, ?_⟩
  · intro Q hQ hQb y hy hlt
    by_cases hyE : y < E0
    · exact ⟨0, hQ.1, hyE.trans_le le_self_add⟩
    · push Not at hyE
      have e := Ordinal.add_sub_cancel_of_le hyE
      have hr := (leClDec hQ ldOm2_SC y hy).1 E0 (hE0cl Q hQ hQb) hyE
      obtain ⟨ζ, hζ, hrζ⟩ := h.fine Q hQ hQb _ hr ((add_lt_add_iff_left E0).1 (by rw [e]; exact hlt))
      refine ⟨ζ, hζ, ?_⟩
      calc y = E0 + (y - E0) := e.symm
        _ < E0 + g ζ := (add_lt_add_iff_left E0).2 hrζ
  · intro Q hQ hQb y hy hlt
    by_cases hyE : y < Eh0
    · exact ⟨0, hQ.1, hyE.trans_le le_self_add⟩
    · push Not at hyE
      have e := Ordinal.add_sub_cancel_of_le hyE
      have hr := (leClDec hQ Ph.ph_SC_Om1 y hy).1 Eh0 (hEh0cl Q hQ hQb) hyE
      obtain ⟨v, hv, hrv⟩ := h.fineh Q hQ hQb _ hr ((add_lt_add_iff_left Eh0).1 (by rw [e]; exact hlt))
      refine ⟨v, hv, ?_⟩
      calc y = Eh0 + (y - Eh0) := e.symm
        _ < Eh0 + gh (v + 1) := (add_lt_add_iff_left Eh0).2 hrv

/-- **The lift `ζ ↦ W^{g ζ}`** with the fine laws. -/
theorem taShp_lift (h : TaShp S l g gh gs ghs bot both) :
    TaShp S l (fun z => leWe (g z)) (fun v => leOe (gh v)) (leWe gs) (leOe ghs) bot both := by
  have hgs0 : 0 < gs := omega0_pos.trans_le h.shp.inf
  have hghs0 : 0 < ghs := omega0_pos.trans_le h.shp.infh
  refine ⟨scShp_lift hl hX h.shp, taLim_We hgs0, taLim_Oe hghs0, ?_, ?_⟩
  · intro Q hQ hQb y hy hlt
    rcases eq_or_ne y 0 with rfl | hy0
    · exact ⟨0, hQ.1, leWe_pos _⟩
    have he := Sn.snLogW hQ hy
    have heg : log ω y / Om (1 + 1) < gs := by
      by_contra hc
      push Not at hc
      exact absurd ((leWe_mono hc).trans (sgLW_le (pos_iff_ne_zero.2 hy0))) (not_le.2 hlt)
    obtain ⟨ζ, hζ, heζ⟩ := h.fine Q hQ hQb _ he heg
    exact ⟨ζ, hζ, (sgLW_lt y).trans_le (leWe_mono (Order.add_one_le_of_lt heζ))⟩
  · intro Q hQ hQb y hy hlt
    rcases eq_or_ne y 0 with rfl | hy0
    · exact ⟨0, hQ.1, leOe_pos _⟩
    have he : LeCl (Om 1) Q (log ω y / Om 1) :=
      Sj.sjCl_div hQ Ph.ph_SC_Om1 _ (leClDec hQ Ph.ph_SC_Om1 y hy).2
    have heg : log ω y / Om 1 < ghs := by
      by_contra hc
      push Not at hc
      exact absurd ((leOe_mono hc).trans (taOe_log_le hy0)) (not_le.2 hlt)
    obtain ⟨v, hv, hev⟩ := h.fineh Q hQ hQb _ he heg
    exact ⟨v, hv, (roLt_Oe_log y).trans_le (leOe_mono (Order.add_one_le_of_lt hev))⟩

/-- **THE LIFT THROUGH `φ(a, ·)`**: `ζ ↦ φ(a, g ζ)` (image `v ↦ φ(a, ĝ v)`) for `g* > Ω₂`, `ĝ* > Ω₁`. -/
theorem taShp_veb {a : Ordinal.{0}} (h : TaShp S l g gh gs ghs bot both) (ha : TaSm a)
    (hbot : gamma 0 ≤ bot) (hboth : gamma 0 ≤ both) (hgs : Om (1 + 1) < gs) (hghs : Om 1 < ghs) :
    TaShp S l (fun z => veblen a (g z)) (fun v => veblen a (gh v)) (veblen a gs) (veblen a ghs) bot both := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have ha0 := taSm_ne0 ha
  have haW := taSm_lt_Om2 ha
  have haO := taSm_lt_Om1 ha
  have hWs : Om (1 + 1) * veblen a gs = veblen a gs :=
    Ta.taK_mul_veb ldOm2_SC ha0 (hgs.trans_le (right_le_veblen a gs))
  have hOs : Om 1 * veblen a ghs = veblen a ghs :=
    Ta.taK_mul_veb Ph.ph_SC_Om1 ha0 (hghs.trans_le (right_le_veblen a ghs))
  -- the fine laws
  have hfine : ∀ Q, SC Q → bot ≤ Q → TaFine (fun z => veblen a (g z)) (veblen a gs) Q := by
    intro Q hQ hQb y hy hlt
    obtain ⟨u, hu, hugs, hyu⟩ := taCl_dec hQ ldOm2_SC haW h.lim y hy hlt
    obtain ⟨ζ, hζ, huζ⟩ := h.fine Q hQ hQb u hu hugs
    exact ⟨ζ, hζ, hyu.trans ((veblen_lt_veblen_iff_right).2 huζ)⟩
  have hfineh : ∀ Q, SC Q → both ≤ Q → TaFineH (fun v => veblen a (gh v)) (veblen a ghs) Q := by
    intro Q hQ hQb y hy hlt
    obtain ⟨u, hu, hugs, hyu⟩ := taCl_dec hQ Ph.ph_SC_Om1 haO h.limh y hy hlt
    obtain ⟨v, hv, huv⟩ := h.fineh Q hQ hQb u hu hugs
    exact ⟨v, hv, hyu.trans ((veblen_lt_veblen_iff_right).2 huv)⟩
  refine ⟨⟨fun x y hxy => (veblen_lt_veblen_iff_right).2 (h.shp.st hxy),
    fun ζ hζ => (veblen_lt_veblen_iff_right).2 (h.shp.lt ζ hζ),
    fun v hv => (veblen_lt_veblen_iff_right).2 (h.shp.lth v hv),
    h.shp.inf.trans (right_le_veblen a gs), h.shp.infh.trans (right_le_veblen a ghs),
    fun ζ hζ hζW => CSet.phi_mem (taSm_hull hl hX ha) (h.shp.hull ζ hζ hζW),
    CSet.phi_mem (taSm_hull hl hX ha) h.shp.hullS,
    fun x c hx hc => CSet.phi_mem (taSm_mem ha (hbot.trans hc)) (h.shp.mem x c hx hc),
    fun v c hv hc => CSet.phi_mem (taSm_mem ha (hboth.trans hc)) (h.shp.memh v c hv hc),
    fun Q hQ hQb w hw hlt => ?_, fun Q hQ hQb w hw hlt => ?_, fun c hc hcs => ?_,
    fun Q hQ hQb ζ hζ => LeCl.phi (LeCl.small (taSm_lt_SC ha hQ)) (h.shp.clm Q hQ hQb ζ hζ),
    fun Q hQ hQb v hv => LeCl.phi (LeCl.small (taSm_lt_SC ha hQ)) (h.shp.clmh Q hQ hQb v hv),
    fun x y hxy => (veblen_lt_veblen_iff_right).2 (h.shp.sth hxy), fun v hv u hu => ?_,
    fun c hc => CSet.phi_mem (taSm_mem ha (hbot.trans hc)) (h.shp.memS c hc),
    fun c hc => CSet.phi_mem (taSm_mem ha (hboth.trans hc)) (h.shp.memhS c hc),
    fun Q hQ hQb => LeCl.phi (LeCl.small (taSm_lt_SC ha hQ)) (h.shp.clS Q hQ hQb),
    fun Q hQ hQb => LeCl.phi (LeCl.small (taSm_lt_SC ha hQ)) (h.shp.clhS Q hQ hQb)⟩,
    taVeb_lim ha0, taVeb_lim ha0, hfine, hfineh⟩
  · -- the closure law
    rw [hWs] at hlt
    obtain ⟨ζ, hζ, hwζ⟩ := hfine Q hQ hQb w hw hlt
    exact ⟨ζ, hζ, hwζ.trans_le (Ordinal.le_mul_right _ ldOm2_SC.1)⟩
  · -- the image closure law
    rw [hOs] at hlt
    obtain ⟨v, hv, hwv⟩ := hfineh Q hQ hQb w hw hlt
    exact ⟨v, hv, hwv.trans_le (Ordinal.le_mul_right _ (Om_pos one_ne_zero))⟩
  · -- the index
    by_cases h0 : veblen a 0 ≤ c
    · obtain ⟨u, hu, h1, h2⟩ := taHull_idx ha.2 hc h0
      have hugs : u < gs := (veblen_lt_veblen_iff_right).1 (h1.trans_lt hcs)
      obtain ⟨q, hq, hqW, huq, hqu⟩ := h.shp.idx u hu hugs
      refine ⟨q, hq, hqW, h2.trans_le ((veblen_le_veblen_iff_right).2 (Order.add_one_le_of_lt huq)), ?_⟩
      exact fun hq0 => ((veblen_le_veblen_iff_right).2 (hqu hq0)).trans h1
    · push Not at h0
      refine ⟨0, GxCl.zero hρSC.1, ldOm2_SC.1, h0.trans_le ((veblen_le_veblen_iff_right).2 zero_le), ?_⟩
      exact fun h' => absurd rfl h'
  · -- continuity of the image
    have hlimv : IsSuccLimit (gh v) := scLim_of_cont h.shp.sth h.shp.cont hv
    obtain ⟨w, hw, huw⟩ := ((isNormal_veblen a).lt_iff_exists_lt hlimv).1 hu
    obtain ⟨v', hv', hwv'⟩ := h.shp.cont v hv w hw
    exact ⟨v', hv', huw.trans ((veblen_lt_veblen_iff_right).2 hwv')⟩

end Cons

end Googology.Trans.PoR.InaccPsi.R2.Ta

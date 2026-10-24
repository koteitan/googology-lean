import Googology.Trans.PoR.InaccPsi.R2.TdTm

/-!
# The lift of a shape through `φ(a, ·)` for every level `a` below `K`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, codes = `Le.LeCl κ Q`, `K = tdK S = ψ_{Ω₁}(Ω_ω)`,
`TdSm S a`: `1 ≤ a < K`.  Shapes with the fine closure
laws are `Ta.TaShp`.

* `tdShp_veb` (**THE LIFT THROUGH `φ(a, ·)`**: `ζ ↦ φ(a, g ζ)`, image `v ↦ φ(a, ĝ v)`, for bottoms `≥ K`; the
  index from `Td.tdHull_idx`, which needs no bound on the level).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Td

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg
  Googology.Trans.PoR.InaccPsi.R2.Ta

variable {S : InaccSeq.{0}}

section Cons

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  {g gh : Ordinal.{0} → Ordinal.{0}} {gs ghs bot both : Ordinal.{0}}

include hl hX

/-- **THE LIFT THROUGH `φ(a, ·)`**: `ζ ↦ φ(a, g ζ)` (image `v ↦ φ(a, ĝ v)`) for `g* > Ω₂`, `ĝ* > Ω₁`. -/
theorem tdShp_veb {a : Ordinal.{0}} (h : TaShp S l g gh gs ghs bot both) (ha : TdSm S a)
    (hbot : tdK S ≤ bot) (hboth : tdK S ≤ both) (hgs : Om (1 + 1) < gs) (hghs : Om 1 < ghs) :
    TaShp S l (fun z => veblen a (g z)) (fun v => veblen a (gh v)) (veblen a gs) (veblen a ghs) bot both := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have ha0 := tdSm_ne0 ha
  have haW := tdSm_lt_Om2 ha
  have haO := tdSm_lt_Om1 ha
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
    fun ζ hζ hζW => CSet.phi_mem (tdSm_hull hl hX ha) (h.shp.hull ζ hζ hζW),
    CSet.phi_mem (tdSm_hull hl hX ha) h.shp.hullS,
    fun x c hx hc => CSet.phi_mem (tdSm_mem ha (hbot.trans hc)) (h.shp.mem x c hx hc),
    fun v c hv hc => CSet.phi_mem (tdSm_mem ha (hboth.trans hc)) (h.shp.memh v c hv hc),
    fun Q hQ hQb w hw hlt => ?_, fun Q hQ hQb w hw hlt => ?_, fun c hc hcs => ?_,
    fun Q hQ hQb ζ hζ => LeCl.phi (LeCl.small (tdSm_lt ha (hbot.trans hQb))) (h.shp.clm Q hQ hQb ζ hζ),
    fun Q hQ hQb v hv => LeCl.phi (LeCl.small (tdSm_lt ha (hboth.trans hQb))) (h.shp.clmh Q hQ hQb v hv),
    fun x y hxy => (veblen_lt_veblen_iff_right).2 (h.shp.sth hxy), fun v hv u hu => ?_,
    fun c hc => CSet.phi_mem (tdSm_mem ha (hbot.trans hc)) (h.shp.memS c hc),
    fun c hc => CSet.phi_mem (tdSm_mem ha (hboth.trans hc)) (h.shp.memhS c hc),
    fun Q hQ hQb => LeCl.phi (LeCl.small (tdSm_lt ha (hbot.trans hQb))) (h.shp.clS Q hQ hQb),
    fun Q hQ hQb => LeCl.phi (LeCl.small (tdSm_lt ha (hboth.trans hQb))) (h.shp.clhS Q hQ hQb)⟩,
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
    · obtain ⟨u, hu, h1, h2⟩ := tdHull_idx hc h0
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

end Googology.Trans.PoR.InaccPsi.R2.Td

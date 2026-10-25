import Googology.Trans.PoR.InaccPsi.R2.UmShp

/-!
# The members of a shape are own exponents past `Γ₂`, and the small limits past `Γ₂`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ_{Ω₂}(β + W^E)`, `SQ_j = Sc.scSq` of the lifted
shape `ζ ↦ W^{g ζ}`, `Y₃ = ψ_{Ω₃}(Ω₃)`, `Y₂ = ψ_{Ω₂}(Ω₂)`.

`Sc.scOwP_mem`, `Sc.scLev_lim` with the offsets past `Γ₂` (`Uj.UjOff`), the own data `Uj.UjOwP`, the shifts
`Uj.UjSh` (`Uj.ujSh_own`) and the limit shift `Uj.ujTopLimSh`.

* `umOwP_of_sc` (**every own predicate with the data of `Sc` has the data past `Γ₂`**), `umOwP_mem` (the own
  predicate `Ow b X₀ ∧ ∃ j, ζ < SQ_j(X₀, b)` of the member `g ζ` has the data past `Γ₂`, image `ĝ(Θ ζ)`);
* `umLev_lim` (**THE SMALL LIMIT PAST `Γ₂`**: for a limit code `η`, the members `g(ζ+1)`, `ζ < η`, with `UjLev`
  give `g η`, image `ĝ(Θ η)`, over every offset past `Γ₂`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Um

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj

variable {S : InaccSeq.{0}}

/-- **Every own predicate with the data of `Sc` has the data past `Γ₂`.** -/
theorem umOwP_of_sc {l : Ordinal.{0}} {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {E Eh : Ordinal.{0}}
    (h : ScOwP S l Ow E Eh) : UjOwP S l Ow E Eh :=
  ⟨fun b X0 hO => ujOwn_of_sc (h.dat b X0 hO), h.mono⟩

section Mem

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  {g gh : Ordinal.{0} → Ordinal.{0}} {gs ghs : Ordinal.{0}} {Ow : Ordinal.{0} → Ordinal.{0} → Prop}
  (hshp : ∀ b X0, Ow b X0 → ScShp S l g gh gs ghs (leTe S (X0 + leWe (g 1)) b)
    (gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe (g 1)) b)))
  (hmono : ∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0')

include hshp hmono

/-- **The own predicate of the member `g ζ` has the data past `Γ₂`.** -/
theorem umOwP_mem {ζ : Ordinal.{0}} (hζ : GxCl (upsilon l) (ldAtR S l) ζ) (h1 : 1 ≤ ζ) :
    UjOwP S l (fun b X0 => Ow b X0 ∧ ∃ j, ζ < scSq S (fun z => leWe (g z)) X0 b j) (g ζ)
      (gh (gxTh (upsilon l) (ldAtR S l) ζ)) :=
  umOwP_of_sc (scOwP_mem hshp hmono hζ h1)

include hl hX

/-- **THE SMALL LIMIT PAST `Γ₂`: the members `g(ζ+1)`, `ζ < η`, give `g η`** (`η` a limit code), image
`ĝ(Θ η)`, over every offset past `Γ₂`. -/
theorem umLev_lim {η : Ordinal.{0}} (hη : GxCl (upsilon l) (ldAtR S l) η) (hηW : η < Om (1 + 1))
    (hlim : IsSuccLimit η)
    (hmem : ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → ζ < η →
      UjLev S l (fun b X0 => Ow b X0 ∧ ∃ j, ζ + 1 < scSq S (fun z => leWe (g z)) X0 b j) (g (ζ + 1))
        (gh (gxTh (upsilon l) (ldAtR S l) (ζ + 1)))) :
    UjLev S l (fun b X0 => Ow b X0 ∧ ∃ j, η < scSq S (fun z => leWe (g z)) X0 b j) (g η)
      (gh (gxTh (upsilon l) (ldAtR S l) η)) := by
  intro b X0 Xh0 hoff hd hG3 hG hOwη
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hη1 : 1 ≤ η := (rvLim_one_lt hlim).le
  have hEo := (umOwP_mem hshp hmono hη hη1).dat b X0 hOwη
  have hs := ujSh_own hoff hEo hG3 hG
  obtain ⟨hOw, j, hj⟩ := hOwη
  have hsh := hshp b X0 hOw
  have hsub : ∀ c, GxCl (upsilon l) (ldAtR S l) c → c < η →
      UjSh S l b (X0 + leWe (g (c + 1))) (Xh0 + leOe (gh (gxTh (upsilon l) (ldAtR S l) (c + 1)))) ∧
      RvTop S l b (X0 + leWe (g (c + 1))) (Xh0 + leOe (gh (gxTh (upsilon l) (ldAtR S l) (c + 1)))) 0 ∧
      gh (gxTh (upsilon l) (ldAtR S l) (c + 1)) < gh (gxTh (upsilon l) (ldAtR S l) η) ∧ g (c + 1) < g η := by
    intro c hc hcη
    have hc1 := hlim.succ_lt hcη
    have hc1c := rqCode_succ hl hX hc (hc1.trans hηW)
    have hown : Ow b X0 ∧ ∃ j, c + 1 < scSq S (fun z => leWe (g z)) X0 b j := ⟨hOw, j, hc1.trans hj⟩
    have hEo1 := (umOwP_mem hshp hmono hc1c le_add_self).dat b X0 hown
    have hgl := hsh.st hc1
    have hΘl := hsh.sth (gxTh_lt (Z := upsilon l) (At := ldAtR S l) hc1c hc1)
    have hle1 : X0 + leWe (g (c + 1)) + Om (1 + 1) ≤ X0 + leWe (g η) + Om (1 + 1) :=
      add_le_add_left ((add_le_add_iff_left X0).2 (leWe_mono hgl.le)) _
    have hle2 : Xh0 + leOe (gh (gxTh (upsilon l) (ldAtR S l) (c + 1))) + Om 1 ≤
        Xh0 + leOe (gh (gxTh (upsilon l) (ldAtR S l) η)) + Om 1 :=
      add_le_add_left ((add_le_add_iff_left Xh0).2 (leOe_mono hΘl.le)) _
    exact ⟨ujSh_own hoff hEo1 (hle1.trans_lt hG3) (hle2.trans_lt hG),
      hmem c hc hcη b X0 Xh0 hoff ((leWe_dvd hgl.le).trans hd) (hle1.trans_lt hG3)
        (hle2.trans_lt hG) hown, hΘl, hgl⟩
  refine ujTopLimSh hl hX hs (fun x hxH hx => ?_) (fun z hz => ?_)
  · rcases lt_or_ge x X0 with hxX | hxX
    · obtain ⟨hs0, ht0⟩ := ujOff_ne hoff (zero_le.trans_lt hxX).ne'
      exact ⟨X0, Xh0, le_self_add, hxX, lt_add_of_pos_right _ (leOe_pos _), hs0, ht0⟩
    obtain ⟨r, rfl⟩ := exists_add_of_le hxX
    have hr : r < leWe (g η) := (add_lt_add_iff_left X0).1 hx
    have hrH : r ∈ cdHull S l := by
      have h1 := leModP_mem (S := S) (Om (1 + 1) * g η) hxH
      have hm : (X0 + r) % ω ^ (Om (1 + 1) * g η) = r := by
        obtain ⟨q, hq⟩ := hd
        change (X0 + r) % leWe (g η) = r
        rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr]
      rwa [hm] at h1
    set c := log ω r / Om (1 + 1) with hc_def
    have hcH : c ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hrH)
    have hcg : c < g η := by
      rcases eq_or_ne r 0 with h0 | hr0
      · rw [hc_def, h0, log_zero_right, Ordinal.zero_div]
        exact zero_le.trans_lt (hsh.st (pos_iff_ne_zero.2 hlim.ne_bot))
      have hlogr : log ω r < Om (1 + 1) * g η :=
        (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hr0).trans_lt hr)
      exact (Ordinal.lt_mul_iff_div_lt hW0).1 hlogr
    obtain ⟨q, hq, -, hcq, hgq⟩ := hsh.idx c hcH (hcg.trans (hsh.lt η hηW))
    have hqη : q < η := by
      by_contra h
      push Not at h
      have hq0 : q ≠ 0 := by rintro rfl; exact hlim.ne_bot (le_antisymm h zero_le)
      exact absurd ((hsh.st.monotone h).trans (hgq hq0)) (not_le.2 hcg)
    obtain ⟨hs1, ht1, hΘl, hgl⟩ := hsub q hq hqη
    exact ⟨_, _, (add_le_add_iff_left X0).2 (leWe_mono hgl.le),
      (add_lt_add_iff_left X0).2 ((roLt_We_log r).trans_le (leWe_mono (Order.add_one_le_of_lt hcq))),
      (add_lt_add_iff_left Xh0).2 (leOe_lt hΘl), hs1, ht1⟩
  · rcases lt_or_ge z Xh0 with hzX | hzX
    · obtain ⟨hs0, ht0⟩ := ujOff_neh hoff (zero_le.trans_lt hzX).ne'
      exact ⟨X0, Xh0, lt_add_of_pos_right _ (leWe_pos _), hzX, hs0, ht0⟩
    obtain ⟨u, rfl⟩ := exists_add_of_le hzX
    have hu : u < leOe (gh (gxTh (upsilon l) (ldAtR S l) η)) := (add_lt_add_iff_left Xh0).1 hz
    have hΘlim := rwTh_lim hl hX hηW hlim
    obtain ⟨e', -, he', hue'⟩ := rvLt_Oe_lim (scLim_of_cont hsh.sth hsh.cont hΘlim) hu
    obtain ⟨v', hv', he'v⟩ := hsh.cont _ hΘlim e' he'
    obtain ⟨c, hc, hcη, hcv⟩ := gxTh_onto hv'
    obtain ⟨hs1, ht1, -, hgl⟩ := hsub c hc hcη
    refine ⟨_, _, (add_lt_add_iff_left X0).2 (leWe_lt hgl), (add_lt_add_iff_left Xh0).2 ?_, hs1, ht1⟩
    refine hue'.trans ((leOe_lt he'v).trans_le (leOe_mono (hsh.sth.monotone ?_)))
    rw [← hcv]; exact gxTh_mono (lt_add_one c).le

end Mem

end Googology.Trans.PoR.InaccPsi.R2.Um

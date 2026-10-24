import Googology.Trans.PoR.InaccPsi.R2.ScShpA

/-!
# The members of a shape are own exponents, and the small limits

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ_{Ω₂}(β + W^E)`, `SQ_j = Sc.scSq` of the lifted
shape `ζ ↦ W^{g ζ}`.

* `scShLev` (`(X₀ + W^E, X̂₀ + Ω^Ê)` is a shift own relative to `b` for an own exponent `E` of any level, as
  `Rw.rwShLevC`), `scSq_mono_off`;
* `scOwP_mem` (**the own predicate `Ow b X₀ ∧ ∃ j, ζ < SQ_j(X₀, b)` of the member `g ζ` has the data**, image
  `ĝ(Θ ζ)`, for a shape valid under a monotone `Ow`);
* `scLev_lim` (**THE SMALL LIMIT**: for a limit code `η`, the members `g(ζ+1)`, `ζ < η`, give `g η`, image
  `ĝ(Θ η)`; by `Rv.rvTopLimSh`, the index of the shape, and the continuity of `ĝ`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw

variable {S : InaccSeq.{0}}

theorem scSq_mono_off {G : Ordinal.{0} → Ordinal.{0}} (hGmo : Monotone G) {X0 X0' β : Ordinal.{0}}
    (hXX : X0 ≤ X0') : ∀ j, scSq S G X0 β j ≤ scSq S G X0' β j
  | 0 => le_rfl
  | j + 1 => (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono (add_le_add hXX
      (hGmo (scSq_mono_off hGmo hXX j)))))).1

section Sh

variable {l : Ordinal.{0}}

/-- **`(X₀ + W^E, X̂₀ + Ω^Ê)` is a shift own relative to `b`** for an own exponent `E` of any level. -/
theorem scShLev {b X0 Xh0 E Eh : Ordinal.{0}} (hoff : RvOff S l b X0 Xh0) (hEo : ScOwn S l b X0 E Eh)
    (hG3 : X0 + leWe E + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)))
    (hG : Xh0 + leOe Eh + Om 1 < S.psi 0 (Om (1 + 1))) :
    RvSh S l b (X0 + leWe E) (Xh0 + leOe Eh) := by
  obtain ⟨hd, hH, hm, hmh, hcl, hclh⟩ := rvOff_data hoff
  have hle : S.psi (b + leWe X0) (Om (1 + 1)) ≤ S.psi (b + leWe (X0 + leWe E)) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left b).2 (leWe_mono le_self_add))).1
  have hWe : Om (1 + 1) ∣ leWe E := by have h := leWe_dvd hEo.one; rwa [leWe_one] at h
  exact ⟨fun h => (leWe_pos E).ne' (le_antisymm (h ▸ le_add_self) zero_le), dvd_add hd hWe,
    CSet.add_mem hH (leWe_mem hEo.hull), CSet.add_mem (CSet_mono le_rfl hle hm) (leWe_mem hEo.mem),
    CSet.add_mem (CSet_mono le_rfl (gxTh_mono hle) hmh) (leOe_mem hEo.memh), hG3, hG,
    fun Q hQ hb => LeCl.add (hcl Q hQ (hle.trans hb)) (LeCl.opow hQ.1 (LeCl.mulK hQ ldOm2_SC E (hEo.cl Q hQ hb))),
    fun Q hQ hb => LeCl.add (hclh Q hQ ((gxTh_mono hle).trans hb)) (LeCl.opow hQ.1 (LeCl.mulK hQ Ph.ph_SC_Om1 _
      (hEo.clh Q hQ hb)))⟩

end Sh

section Mem

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  {g gh : Ordinal.{0} → Ordinal.{0}} {gs ghs : Ordinal.{0}} {Ow : Ordinal.{0} → Ordinal.{0} → Prop}
  (hshp : ∀ b X0, Ow b X0 → ScShp S l g gh gs ghs (leTe S (X0 + leWe (g 1)) b)
    (gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe (g 1)) b)))
  (hmono : ∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0')

include hshp hmono

/-- **The own predicate of the member `g ζ` has the data.** -/
theorem scOwP_mem {ζ : Ordinal.{0}} (hζ : GxCl (upsilon l) (ldAtR S l) ζ) (h1 : 1 ≤ ζ) :
    ScOwP S l (fun b X0 => Ow b X0 ∧ ∃ j, ζ < scSq S (fun z => leWe (g z)) X0 b j) (g ζ)
      (gh (gxTh (upsilon l) (ldAtR S l) ζ)) := by
  refine ⟨fun b X0 ⟨hOw, j, hj⟩ => ?_, fun b β X0 X0' ⟨hOw, j, hj⟩ hb hXX => ?_⟩
  · have hsh := hshp b X0 hOw
    have hmo : Monotone (fun z => leWe (g z)) := fun a c h => leWe_mono (hsh.st.monotone h)
    have hown := scSq_gt hmo j ζ hj
    have hζW : ζ < Om (1 + 1) := hj.trans (scSq_lt_Om2 j)
    have hbotY : leTe S (X0 + leWe (g 1)) b ≤ S.psi (b + leWe (X0 + leWe (g ζ))) (Om (1 + 1)) :=
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left b).2
        (leWe_mono ((add_le_add_iff_left X0).2 (leWe_mono (hsh.st.monotone h1)))))).1
    have hΘo := gxTh_lt (Z := upsilon l) (At := ldAtR S l) hζ hown
    exact ⟨Order.one_le_iff_pos.2 (zero_le.trans_lt (hsh.st (zero_lt_one.trans_le h1))),
      hsh.hull ζ hζ hζW, hsh.mem ζ _ (CSet.of_lt hown) hbotY,
      hsh.memh _ _ (CSet.of_lt hΘo) (gxTh_mono hbotY),
      fun Q hQ hY => hsh.clm Q hQ (hbotY.trans hY) ζ (hown.trans_le hY),
      fun Q hQ hY => hsh.clmh Q hQ ((gxTh_mono hbotY).trans hY) _ (hΘo.trans_le hY)⟩
  · have hmo : Monotone (fun z => leWe (g z)) := fun a c h => leWe_mono ((hshp b X0 hOw).st.monotone h)
    exact ⟨hmono _ _ _ _ hOw hb hXX, j, hj.trans_le ((scSq_mono_base hmo hb j).trans (scSq_mono_off hmo hXX j))⟩

include hl hX

/-- **THE SMALL LIMIT: the members `g(ζ+1)`, `ζ < η`, give `g η`** (`η` a limit code), image `ĝ(Θ η)`. -/
theorem scLev_lim {η : Ordinal.{0}} (hη : GxCl (upsilon l) (ldAtR S l) η) (hηW : η < Om (1 + 1))
    (hlim : IsSuccLimit η)
    (hmem : ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → ζ < η →
      ScLev S l (fun b X0 => Ow b X0 ∧ ∃ j, ζ + 1 < scSq S (fun z => leWe (g z)) X0 b j) (g (ζ + 1))
        (gh (gxTh (upsilon l) (ldAtR S l) (ζ + 1)))) :
    ScLev S l (fun b X0 => Ow b X0 ∧ ∃ j, η < scSq S (fun z => leWe (g z)) X0 b j) (g η)
      (gh (gxTh (upsilon l) (ldAtR S l) η)) := by
  intro b X0 Xh0 hoff hd hG3 hG hOwη
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hη1 : 1 ≤ η := (rvLim_one_lt hlim).le
  have hEo := (scOwP_mem hshp hmono hη hη1).dat b X0 hOwη
  have hs := scShLev hoff hEo hG3 hG
  obtain ⟨hOw, j, hj⟩ := hOwη
  have hsh := hshp b X0 hOw
  have hsub : ∀ c, GxCl (upsilon l) (ldAtR S l) c → c < η →
      RvSh S l b (X0 + leWe (g (c + 1))) (Xh0 + leOe (gh (gxTh (upsilon l) (ldAtR S l) (c + 1)))) ∧
      RvTop S l b (X0 + leWe (g (c + 1))) (Xh0 + leOe (gh (gxTh (upsilon l) (ldAtR S l) (c + 1)))) 0 ∧
      gh (gxTh (upsilon l) (ldAtR S l) (c + 1)) < gh (gxTh (upsilon l) (ldAtR S l) η) ∧ g (c + 1) < g η := by
    intro c hc hcη
    have hc1 := hlim.succ_lt hcη
    have hc1c := rqCode_succ hl hX hc (hc1.trans hηW)
    have hown : Ow b X0 ∧ ∃ j, c + 1 < scSq S (fun z => leWe (g z)) X0 b j := ⟨hOw, j, hc1.trans hj⟩
    have hEo1 := (scOwP_mem hshp hmono hc1c le_add_self).dat b X0 hown
    have hgl := hsh.st hc1
    have hΘl := hsh.sth (gxTh_lt (Z := upsilon l) (At := ldAtR S l) hc1c hc1)
    have hle1 : X0 + leWe (g (c + 1)) + Om (1 + 1) ≤ X0 + leWe (g η) + Om (1 + 1) :=
      add_le_add_left ((add_le_add_iff_left X0).2 (leWe_mono hgl.le)) _
    have hle2 : Xh0 + leOe (gh (gxTh (upsilon l) (ldAtR S l) (c + 1))) + Om 1 ≤
        Xh0 + leOe (gh (gxTh (upsilon l) (ldAtR S l) η)) + Om 1 :=
      add_le_add_left ((add_le_add_iff_left Xh0).2 (leOe_mono hΘl.le)) _
    exact ⟨scShLev hoff hEo1 (hle1.trans_lt hG3) (hle2.trans_lt hG),
      hmem c hc hcη b X0 Xh0 hoff ((leWe_dvd hgl.le).trans hd) (hle1.trans_lt hG3)
        (hle2.trans_lt hG) hown, hΘl, hgl⟩
  refine rvTopLimSh hl hX hs (fun x hxH hx => ?_) (fun z hz => ?_)
  · rcases lt_or_ge x X0 with hxX | hxX
    · obtain ⟨hs0, ht0⟩ := rvOff_ne hoff (zero_le.trans_lt hxX).ne'
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
    · obtain ⟨hs0, ht0⟩ := rvOff_neh hoff (zero_le.trans_lt hzX).ne'
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

end Googology.Trans.PoR.InaccPsi.R2.Sc

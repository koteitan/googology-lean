import Googology.Trans.PoR.InaccPsi.R2.TsMove
import Googology.Trans.PoR.InaccPsi.R2.TsX
import Googology.Trans.PoR.InaccPsi.R2.TlCl

/-!
# The runs of an atom `F_β(y)` below `X`: its own argument `B + Ω₂^β·D`

`ψ = ψ_{Ω₂} = S.psi · Ω₂`, `F_β = Rh.rhF β = veblenWith Γ β`, `w_β = Ω₂^β = Le.leWe β`, `X = Tl.tlX` (the least fixed
point of `β ↦ F_β(0)` above `Ω₁`; `X = ψ(Ω₂^{Ω₂})` by `Ts.ts_psiW_eq_X`), `TlCl Z` the codes over `Z` with the atoms
`F_β(y)` (`R2.TlCl`).  An argument `B` is *own* when `B ∈ Cl(B, ψ(B))`.

* `tw_lt_psiU` (**`β < ψ(w_β)` for every `β < X`**, so `w_β` is own: at a limit `β = ψ(w_β)` would be a fixed point
  of every `F_j`, `j < β`, hence of `β ↦ F_β(0)`, below `X`);
* `twS` (the start: `Ω₁ + 1`, `1`, `0` for `β <, =, > Ω₁`), `tw_psiU_s` (**`ψ(w_β) = F_β(twS β)`** for `1 ≤ β < X`,
  and `twS β` is the least `s` with `F_β(s) > Ω₁`);
* `tw_fix_code` (**every fixed point `q > Ω₁` of `F_β` below a code `y` lies below a fixed point `p ≤ y` that is a
  code**), `tw_cl_lt` (codes over `Z ≤ Ω₁` are `< X`);
* `twRun` (**the run of an atom**: for `F_β(y) ∈ (Ω₁, X)`, `y < F_β(y)`, `y` a code: `y = c + D` with `F_β(c) =
  ψ(B)`, `B` own, `w_β ∣ B`, `D` valid, `c`, `D` codes, and either `β = 0`, `B = 0`, `c = Ω₁ + 1`; or `1 ≤ β`,
  `B = w_β`, `c = twS β`; or `c > Ω₁` is the largest fixed point of `F_β` in `(Ω₁, y]`, `w_{β+1} ∣ B`),
  `twRun_eq` (**`ψ(B + w_β·D) = F_β(y)`, and `B + w_β·D` is own**).

No new axiom.  New definition: `twS`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Ts

variable {S : InaccSeq.{0}}

theorem tw_Om1_eq : (Om1 : Ordinal.{0}) = Om 1 := Rj.rj_Om1

theorem tw_Om1_lt_X : Om 1 < (tlX : Ordinal.{0}) := by rw [← tw_Om1_eq]; exact tlX_gt

theorem tw_X_lt_Om2 : (tlX : Ordinal.{0}) < Om (1 + 1) := tlX_lt_Om2

/-- **`β < ψ_{Ω₂}(Ω₂^β)` for every `β < X`.** -/
theorem tw_lt_psiU : ∀ β : Ordinal.{0}, β < tlX → β < S.psi (leWe β) (Om (1 + 1)) := by
  intro β
  induction β using WellFoundedLT.induction with
  | ind β IH =>
  intro hβX
  have hκ : S.InR (Om (1 + 1)) := InR_Om_succ 1
  rcases zero_or_succ_or_isSuccLimit β with h0 | ⟨γ, rfl⟩ | hl
  · rw [h0]; exact (ts_psi_SC _).1
  · rw [Order.succ_eq_add_one] at IH hβX ⊢
    have hγ := IH γ (lt_add_one γ) ((lt_add_one γ).trans hβX)
    have hle : S.psi (leWe γ) (Om (1 + 1)) ≤ S.psi (leWe (γ + 1)) (Om (1 + 1)) :=
      (psi_mono hκ (leWe_mono le_self_add)).1
    exact (ts_psi_SC _).add_one_lt (hγ.trans_le hle)
  · set q := S.psi (leWe β) (Om (1 + 1)) with hq
    have hlow : ∀ j < β, j < q := fun j hj =>
      (IH j hj (hj.trans hβX)).trans_le (psi_mono hκ (leWe_mono hj.le)).1
    have hβq : β ≤ q := not_lt.1 fun h => lt_irrefl _ (hlow q h)
    refine lt_of_le_of_ne hβq fun e => ?_
    have hqSC : SC q := ts_psi_SC _
    have hqlim : IsSuccLimit q := ev_isSuccLimit_of_inE (Gg.gg_SC_eps hqSC)
    have hfix : ∀ j < q, rhF j q = q := by
      intro j hj
      refine le_antisymm (((rhF_normal j).le_iff_forall_le hqlim).2 fun z hz => ?_) (rhF_le_self j q)
      have hj'q : max j z + 1 < q := hqlim.add_one_lt (max_lt hj hz)
      have hj'β : max j z + 1 < β := by rw [e]; exact hj'q
      have hIH := IH _ hj'β (hj'β.trans hβX)
      have hown : leWe (max j z + 1) ∈ S.CSet (leWe (max j z + 1)) (S.psi (leWe (max j z + 1)) (Om (1 + 1))) :=
        tsU_mem hIH
      have hjψ : j < S.psi (leWe (max j z + 1)) (Om (1 + 1)) :=
        (le_max_left j z).trans_lt ((lt_add_one _).trans hIH)
      have hzψ : z < S.psi (leWe (max j z + 1)) (Om (1 + 1)) :=
        (le_max_right j z).trans_lt ((lt_add_one _).trans hIH)
      have hfj := ts_fwd (S := S) j _ hown (tsU_dvd (add_le_add_left (le_max_left j z) 1)) (tsU_ne _) hjψ
      calc rhF j z ≤ rhF j (S.psi (leWe (max j z + 1)) (Om (1 + 1))) := (rhF_le j).2 hzψ.le
        _ = S.psi (leWe (max j z + 1)) (Om (1 + 1)) := hfj
        _ ≤ q := (psi_mono hκ (leWe_mono hj'β.le)).1
    obtain ⟨e', he'⟩ := rhF_range hqSC hfix
    have hg : tlG q = q := by
      refine le_antisymm ?_ (rhF_left_le _ _)
      unfold tlG
      calc rhF q 0 ≤ rhF q e' := (rhF_le _).2 zero_le
        _ = q := he'
    have hXq := tlX_le hg (by rw [tw_Om1_eq]; exact ts_Om1_lt_psi _)
    rw [← e] at hXq
    exact absurd hβX (not_lt.2 hXq)

/-- `w_β` is own for `β < X`. -/
theorem tw_own_U {β : Ordinal.{0}} (hβ : β < tlX) :
    leWe β ∈ S.CSet (leWe β) (S.psi (leWe β) (Om (1 + 1))) := tsU_mem (tw_lt_psiU β hβ)

/-- **The start of `F_β` above `Ω₁`**: `Ω₁ + 1`, `1`, `0` for `β <, =, > Ω₁`. -/
noncomputable def twS (β : Ordinal.{0}) : Ordinal.{0} :=
  if β < Om 1 then Om 1 + 1 else if β = Om 1 then 1 else 0

/-- **`ψ_{Ω₂}(Ω₂^β) = F_β(twS β)`** for `1 ≤ β < X`; `Ω₁ < F_β(twS β)`, and `F_β(s) ≤ Ω₁` for `s < twS β`. -/
theorem tw_psiU_s {β : Ordinal.{0}} (h1 : 1 ≤ β) (hβX : β < tlX) :
    S.psi (leWe β) (Om (1 + 1)) = rhF β (twS β) ∧ Om 1 < rhF β (twS β) ∧
      ∀ s, s < twS β → rhF β s ≤ Om 1 := by
  unfold twS
  rcases lt_trichotomy β (Om 1) with hβ | hβ | hβ
  · rw [if_pos hβ]
    have hF : rhF β (Om 1) = Om 1 := by
      have := Tl.tl_rhF_Om1 (β := β) (by rw [tw_Om1_eq]; exact hβ); rwa [tw_Om1_eq] at this
    refine ⟨ts_psiU_small h1 hβ, (lt_add_one _).trans_le (rhF_le_self _ _), fun s hs => ?_⟩
    rw [← hF]; exact (rhF_le β).2 (Order.lt_add_one_iff.1 hs)
  · subst hβ
    rw [if_neg (lt_irrefl _), if_pos rfl]
    refine ⟨ts_psiU_Om1, ?_, fun s hs => ?_⟩
    · conv_lhs => rw [← ts_rhF_Om1_zero]
      exact (rhF_lt _).2 zero_lt_one
    · rw [Order.lt_one_iff] at hs; rw [hs, ts_rhF_Om1_zero]
  · rw [if_neg (not_lt.2 hβ.le), if_neg hβ.ne']
    exact ⟨ts_psiU_big hβ (tw_lt_psiU β hβX), hβ.trans_le (rhF_left_le _ _),
      fun s hs => absurd hs (not_lt.2 zero_le)⟩

/-- `twS β` is `Ω₁ + 1`, `1` or `0`. -/
theorem twS_cases (β : Ordinal.{0}) : twS β = Om 1 + 1 ∨ twS β = 1 ∨ twS β = 0 := by
  unfold twS; split_ifs <;> simp

/-! ## Fixed points below a code -/

/-- **A fixed point `q > Ω₁` of `F_β` below a code `y` lies below a fixed point `p ≤ y` of `F_β` that is a code.** -/
theorem tw_fix_code {Z : Ordinal.{0}} (hZ : Z ≤ Om1) (β : Ordinal.{0}) :
    ∀ y, TlCl Z y → ∀ q, rhF β q = q → Om1 < q → q ≤ y →
      ∃ p, TlCl Z p ∧ rhF β p = p ∧ q ≤ p ∧ p ≤ y := by
  intro y hy
  induction hy with
  | small h => exact fun q _ hq hqy => absurd ((hqy.trans_lt h).trans_le hZ) (not_lt.2 hq.le)
  | om => exact fun q _ hq hqy => absurd hq (not_lt.2 hqy)
  | @add x y _ _ ihx ihy =>
    intro q hfix hq hqy
    have hqI : IsPrincipal (· + ·) q := tl_SC_prin (by rw [← hfix]; exact rhF_SC β q)
    by_cases hxq : q ≤ x
    · obtain ⟨p, a, b, c, d⟩ := ihx q hfix hq hxq; exact ⟨p, a, b, c, d.trans le_self_add⟩
    by_cases hyq : q ≤ y
    · obtain ⟨p, a, b, c, d⟩ := ihy q hfix hq hyq; exact ⟨p, a, b, c, d.trans le_add_self⟩
    exact absurd (hqI (not_le.1 hxq) (not_le.1 hyq)) (not_lt.2 hqy)
  | @phi x y _ _ ihx ihy =>
    intro q hfix hq hqy
    have hqS : SC q := by rw [← hfix]; exact rhF_SC β q
    by_cases hxq : q ≤ x
    · obtain ⟨p, a, b, c, d⟩ := ihx q hfix hq hxq; exact ⟨p, a, b, c, d.trans (left_le_veblen x y)⟩
    by_cases hyq : q ≤ y
    · obtain ⟨p, a, b, c, d⟩ := ihy q hfix hq hyq; exact ⟨p, a, b, c, d.trans (right_le_veblen x y)⟩
    exact absurd (hqS.2 _ (not_le.1 hxq) _ (not_le.1 hyq)) (not_lt.2 hqy)
  | @atom β' y' hβ' hy' h1 _ ihy =>
    intro q hfix hq hqy
    by_cases hF : rhF β (rhF β' y') = rhF β' y'
    · exact ⟨_, TlCl.atom hβ' hy' h1, hF, hqy, le_rfl⟩
    have hβ'β : β' ≤ β := not_lt.1 fun h => hF (rhF_fix_lower h y')
    have hq' : rhF β' q = q := rhF_fix_mono hβ'β hfix
    have hqlt : q < rhF β' y' := lt_of_le_of_ne hqy fun e => hF (by rw [← e]; exact hfix)
    have hqy' : q < y' := by rw [← hq'] at hqlt; exact (rhF_lt β').1 hqlt
    obtain ⟨p, a, b, c, d⟩ := ihy q hfix hq hqy'.le
    exact ⟨p, a, b, c, d.trans (rhF_le_self β' y')⟩

/-- **Every code over `Z ≤ Ω₁` is below `X`.** -/
theorem tw_cl_lt {Z : Ordinal.{0}} (hZ : Z ≤ Om1) {x : Ordinal.{0}} (hx : TlCl Z x) : x < tlX := by
  induction hx with
  | small h => exact (h.trans_le hZ).trans tlX_gt
  | om => exact tlX_gt
  | add _ _ ihx ihy => exact (Lq.lq_SC_indec tlX_SC).add_lt ihx ihy
  | phi _ _ ihx ihy => exact tlX_SC.2 _ ihx _ ihy
  | @atom β y _ _ _ ihβ ihy =>
    have := (rhF_lt β).2 ihy; rwa [ts_X_fix ihβ] at this

/-- An atom `F_β(y) < X` is below `ψ_{Ω₂}(Ω₂^{Ω₂})`. -/
theorem tw_lt_psiW {z : Ordinal.{0}} (hz : z < tlX) : z < S.psi (leWe (Om (1 + 1))) (Om (1 + 1)) := by
  rw [ts_psiW_eq_X]; exact hz

/-! ## The run of an atom -/

/-- **The run of an atom `F_β(y) ∈ (Ω₁, X)`** (`y < F_β(y)`, `y` a code over a countable strongly critical `Z`):
`y = c + D` with `F_β(c) = ψ_{Ω₂}(B)`, `B` own, `w_β ∣ B`, `D < Ω₂` valid, `c` and `D` codes, and one of three bases:
`β = 0`, `B = 0`, `c = Ω₁ + 1`; or `1 ≤ β`, `B = w_β`, `c = twS β`; or `c > Ω₁` the largest fixed point of `F_β` in
`(Ω₁, y]`, `w_{β+1} ∣ B`. -/
theorem twRun {Z : Ordinal.{0}} (hZS : SC Z) (hZ : Z ≤ Om1) {β y : Ordinal.{0}} (hy : TlCl Z y)
    (hβX : β < tlX) (hyz : y < rhF β y) (h1 : Om 1 < rhF β y) (hzX : rhF β y < tlX) :
    ∃ B c D, B ∈ S.CSet B (S.psi B (Om (1 + 1))) ∧ leWe β ∣ B ∧ rhF β c = S.psi B (Om (1 + 1)) ∧
      c + D = y ∧ D < Om (1 + 1) ∧ (∀ d, d ≤ D → d < rhF β (c + d)) ∧ TlCl Z c ∧ TlCl Z D ∧
      ((β = 0 ∧ B = 0 ∧ c = Om 1 + 1) ∨ (1 ≤ β ∧ B = leWe β ∧ c = twS β) ∨
        (Om 1 < c ∧ rhF β c = c ∧ leWe (β + 1) ∣ B)) := by
  have hyW : y < Om (1 + 1) := hyz.trans (hzX.trans tw_X_lt_Om2)
  have hO1 : TlCl Z (Om 1 + 1) := by rw [← tw_Om1_eq]; exact TlCl.add TlCl.om (TlCl.one hZS.1)
  by_cases hA : ∃ q, rhF β q = q ∧ Om 1 < q ∧ q ≤ y
  · obtain ⟨q, hqf, hq1, hqy⟩ := hA
    have hne : rhF β (y + 1) ≠ y + 1 := SC.ne_add_one (rhF_SC β (y + 1)) y
    obtain ⟨p, hpb, hpy, hmax⟩ := rh_base_below (rhF_normal β) (hq1.trans_le (hqy.trans (le_self_add : y ≤ y + 1)))
      hne
    have hqp : q ≤ p := hmax q hqf hq1 (Order.lt_add_one_iff.2 hqy)
    have hp1 : Om 1 < p := hq1.trans_le hqp
    have hpf : rhF β p = p := by
      rcases hpb with e | ⟨-, hf⟩
      · exact absurd e hp1.ne'
      · exact hf
    have hpy' : p ≤ y := Order.lt_add_one_iff.1 hpy
    obtain ⟨p', hp'c, hp'f, hpp', hp'y⟩ := tw_fix_code hZ β y hy p hpf (by rw [tw_Om1_eq]; exact hp1) hpy'
    have hpe : p' = p := le_antisymm (hmax p' hp'f (hp1.trans_le hpp') (Order.lt_add_one_iff.2 hp'y)) hpp'
    rw [hpe] at hp'c
    have hpz : p < rhF β y := hpy'.trans_lt hyz
    have hpSC : SC p := by rw [← hpf]; exact rhF_SC β p
    obtain ⟨Bp, hown, hBp⟩ := ts_own_of_SC (S := S) hpSC hp1 (tw_lt_psiW (hpz.trans hzX))
    have hdvd1 : leWe (β + 1) ∣ Bp := ts_conv β Bp hown (by rw [hBp]; exact hpf)
    have hDc : TlCl Z (y - p) := (tlDec hZS y hy).1 p hp'c hpy'
    refine ⟨Bp, p, y - p, hown, (tsU_dvd le_self_add).trans hdvd1, by rw [hBp, hpf],
      Ordinal.add_sub_cancel_of_le hpy', (Ordinal.sub_le_self y p).trans_lt hyW, fun d hd => ?_, hp'c, hDc,
      Or.inr (Or.inr ⟨hp1, hpf, hdvd1⟩)⟩
    rcases eq_or_ne d 0 with rfl | hd0
    · rw [add_zero, hpf]; exact lt_of_le_of_lt zero_le hp1
    have hpd : p < p + d := lt_add_of_pos_right p (pos_iff_ne_zero.2 hd0)
    have hdy : p + d ≤ y := by
      calc p + d ≤ p + (y - p) := add_le_add_right hd p
        _ = y := Ordinal.add_sub_cancel_of_le hpy'
    have hnf : rhF β (p + d) ≠ p + d := fun hf =>
      absurd (hmax (p + d) hf (hp1.trans hpd) (Order.lt_add_one_iff.2 hdy)) (not_le.2 hpd)
    exact le_add_self.trans_lt (lt_of_le_of_ne (rhF_le_self β _) hnf.symm)
  push Not at hA
  rcases eq_or_ne β 0 with rfl | hβ0
  · -- level `0`: the base `ψ_{Ω₂}(0) = Γ_{Ω₁+1}`
    have hF0 : rhF 0 (Om 1) = Om 1 := by
      have := Tl.tl_rhF_Om1 (β := 0) (by rw [tw_Om1_eq]; exact Om_pos one_ne_zero); rwa [tw_Om1_eq] at this
    have hy1 : Om 1 < y := not_le.1 fun h => absurd ((rhF_le 0).2 h) (by rw [hF0]; exact not_le.2 h1)
    have hyO : Om 1 + 1 ≤ y := Order.add_one_le_of_lt hy1
    have hψ0 : rhF 0 (Om 1 + 1) = S.psi 0 (Om (1 + 1)) := by
      rw [rhF_zero, Tf.tf_psi S 0 zero_le, add_zero, tw_Om1_eq]
    have hDc : TlCl Z (y - (Om 1 + 1)) := (tlDec hZS y hy).1 _ hO1 hyO
    refine ⟨0, Om 1 + 1, y - (Om 1 + 1), CSet.zero_mem _ _, dvd_zero _, hψ0,
      Ordinal.add_sub_cancel_of_le hyO, (Ordinal.sub_le_self _ _).trans_lt hyW, fun d hd => ?_, hO1, hDc,
      Or.inl ⟨rfl, rfl, rfl⟩⟩
    have hdy : Om 1 + 1 + d ≤ y := by
      calc Om 1 + 1 + d ≤ Om 1 + 1 + (y - (Om 1 + 1)) := add_le_add_right hd _
        _ = y := Ordinal.add_sub_cancel_of_le hyO
    have hnf : rhF 0 (Om 1 + 1 + d) ≠ Om 1 + 1 + d := fun hf =>
      absurd hdy (not_le.2 (hA _ hf ((lt_add_one _).trans_le le_self_add)))
    exact le_add_self.trans_lt (lt_of_le_of_ne (rhF_le_self 0 _) hnf.symm)
  · -- level `β ≥ 1`: the base `ψ_{Ω₂}(w_β) = F_β(twS β)`
    have hβ1 : 1 ≤ β := Order.one_le_iff_ne_zero.2 hβ0
    obtain ⟨hψ, hs1, hmin⟩ := tw_psiU_s (S := S) hβ1 hβX
    have hsy : twS β ≤ y := not_lt.1 fun h => absurd (hmin y h) (not_le.2 h1)
    have hsc : TlCl Z (twS β) := by
      rcases twS_cases β with e | e | e <;> rw [e]
      · exact hO1
      · exact TlCl.one hZS.1
      · exact TlCl.zero hZS.1
    have hDc : TlCl Z (y - twS β) := (tlDec hZS y hy).1 _ hsc hsy
    refine ⟨leWe β, twS β, y - twS β, tw_own_U hβX, dvd_rfl, hψ.symm, Ordinal.add_sub_cancel_of_le hsy,
      (Ordinal.sub_le_self _ _).trans_lt hyW, fun d hd => ?_, hsc, hDc, Or.inr (Or.inl ⟨hβ1, rfl, rfl⟩)⟩
    have hdy : twS β + d ≤ y := by
      calc twS β + d ≤ twS β + (y - twS β) := add_le_add_right hd _
        _ = y := Ordinal.add_sub_cancel_of_le hsy
    rcases le_or_gt (twS β + d) (Om 1) with hle | hgt
    · exact le_add_self.trans_lt (hle.trans_lt (hs1.trans_le ((rhF_le β).2 le_self_add)))
    · have hnf : rhF β (twS β + d) ≠ twS β + d := fun hf => absurd hdy (not_le.2 (hA _ hf hgt))
      exact le_add_self.trans_lt (lt_of_le_of_ne (rhF_le_self β _) hnf.symm)

/-- **The own argument of an atom from its run**: `ψ_{Ω₂}(B + w_β·D) = F_β(y)`, and `B + w_β·D` is own. -/
theorem twRun_eq {β B c D : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om (1 + 1)))) (hB : leWe β ∣ B)
    (hc : rhF β c = S.psi B (Om (1 + 1))) (hD : D < Om (1 + 1)) (hval : ∀ d, d ≤ D → d < rhF β (c + d))
    (hβz : β < rhF β (c + D)) :
    S.psi (B + leWe β * D) (Om (1 + 1)) = rhF β (c + D) ∧
      B + leWe β * D ∈ S.CSet (B + leWe β * D) (S.psi (B + leWe β * D) (Om (1 + 1))) := by
  obtain ⟨hDψ, heq⟩ := ts_eq_all hown hB hc hD hval
  refine ⟨heq, CSet.add_mem ((psi_mono (InR_Om_succ 1) le_self_add).2 hown) (tsU_mul_mem ?_ hDψ)⟩
  rw [heq]; exact hβz

end Googology.Trans.PoR.InaccPsi.R2.Tw

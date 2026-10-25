import Googology.Trans.PoR.InaccPsi.R2.TsOwn

/-!
# The `ψ_{Ω₂} ↔ F_β` lemma: `ψ_{Ω₂}(B + Ω₂^β·D) = F_β(c + D)` and the fixed points of `F_β` among the collapses

`ψ_{Ω₂}(α) = S.psi α Ω₂`, `F_β = Rh.rhF β = veblenWith Γ β`, `w_β = Ω₂^β = Le.leWe β`.  An argument `B` is *own* when
`B ∈ Cl(B, ψ_{Ω₂}(B))`.  This is `R2.RhPsi` (the same lemma for `ψ_{Ω₁}` and `Ω₁^β`) one cardinal up, generic in the
level `β`, from the definition of `ψ` (closure `Cl`) only; the own points below a collapse come from `R2.TsOwn`
instead of `InaccPsi` normal forms, and the fixed points of `Γ` are found above `ψ_{Ω₂}(0) = Γ_{Ω₁+1}`.

* `ts_mod_mem` (`Cl(a, b)` contains `w_m·(x / w_m)` with `x`, `m ≥ 1`);
* `ts_eq` (**`ψ_{Ω₂}(B + w_β·D) = F_β(c + D)` and `D < ψ_{Ω₂}(B + w_β·D)`** when `d < F_β(c+d)` for every `d ≤ D`,
  `D < Ω₂`, `B` own, `w_β ∣ B`, `F_β(c) = ψ_{Ω₂}(B)`, given FWD below `β`), `ts_valid` (the converse of the
  condition);
* `ts_fix0` (**`ψ_{Ω₂}(B)` is a fixed point of `Γ`** for every own `B ≠ 0` with `Ω₂ ∣ B`);
* `ts_fwd_conv` (by induction on `β`): **FWD(β)** (`ψ_{Ω₂}(B)` is a fixed point of `F_β` for every own `B ≠ 0` with
  `w_{β+1} ∣ B` and `β < ψ_{Ω₂}(B)`) and **CONV(β)** (`w_{β+1} ∣ B` for every own `B` with `ψ_{Ω₂}(B)` a fixed point
  of `F_β`); `ts_fwd`, `ts_conv`, `ts_eq_all` (`ts_eq` with FWD discharged: no hypothesis on the level).

No new axiom.  New definitions: the statement names `TsFWD`, `TsCONV`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ts

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Rb Googology.Trans.PoR.InaccPsi.R2.Rd
  Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Le

variable {S : InaccSeq.{0}}

/-- An additive principal `p ≥ w_m` is a multiple of `w_m`. -/
theorem ts_dvd_of_indec_u (m : Ordinal.{0}) {p : Ordinal.{0}} (hp : Indec p) (h : leWe m ≤ p) : leWe m ∣ p := by
  obtain ⟨e, rfl⟩ := indec_eq_opow hp
  unfold leWe at h ⊢
  have he : Om (1 + 1) * m ≤ e := (opow_le_opow_iff_right one_lt_omega0).1 h
  exact ⟨ω ^ (e - Om (1 + 1) * m), by rw [← opow_add, Ordinal.add_sub_cancel_of_le he]⟩

/-- **`Cl(a, b)` contains `w_m·(x / w_m)` with `x`** (`m ≥ 1`). -/
theorem ts_mod_mem {m : Ordinal.{0}} (hm : 1 ≤ m) {a b : Ordinal.{0}} :
    ∀ x, x ∈ S.CSet a b → leWe m * (x / leWe m) ∈ S.CSet a b := by
  set u := leWe m with hudef
  have h0 : u ≠ 0 := tsU_ne m
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [Ordinal.zero_div, mul_zero]
    exact CSet.zero_mem _ _
  obtain ⟨hl, ht⟩ := lead_tail_mem hx hx0
  have hlt := lead_add_tail hx0
  rcases le_or_gt u (lead x) with h1 | h1
  · have hI : Indec (lead x) := indec_iff.2 ⟨(opow_pos _ omega0_pos).ne', isPrincipal_add_omega0_opow _⟩
    obtain ⟨k', hk'⟩ := ts_dvd_of_indec_u m hI h1
    have ih := IH (tail x) (tail_lt hx0) ht
    have e2 : u * (x / u) = lead x + u * (tail x / u) := by
      conv_lhs => rw [← hlt, hk']
      rw [Ordinal.mul_add_div _ h0, mul_add, hk']
    rw [e2]
    exact CSet.add_mem hl ih
  · have hlim : IsSuccLimit (Om (1 + 1) * m) :=
      isSuccLimit_mul_left ts_Om2_lim (lt_of_lt_of_le zero_lt_one hm)
    have hlog : Ordinal.log ω x < Om (1 + 1) * m := by
      have := h1
      unfold lead at this
      rw [hudef] at this
      unfold leWe at this
      exact (opow_lt_opow_iff_right one_lt_omega0).1 this
    have hxu : x < u := by
      refine (lt_opow_log_add_one x).trans ?_
      rw [hudef]; unfold leWe
      exact (opow_lt_opow_iff_right one_lt_omega0).2 (hlim.add_one_lt hlog)
    rw [Ordinal.div_eq_zero_of_lt hxu, mul_zero]
    exact CSet.zero_mem _ _

/-! ## The fixed-point statements -/

/-- **FWD(β)** for `ψ_{Ω₂}`: `ψ_{Ω₂}(B)` is a fixed point of `F_β` for every own `B ≠ 0` with `w_{β+1} ∣ B` and
`β < ψ_{Ω₂}(B)`. -/
def TsFWD (S : InaccSeq.{0}) (β : Ordinal.{0}) : Prop :=
  ∀ B : Ordinal.{0}, B ∈ S.CSet B (S.psi B (Om (1 + 1))) → leWe (β + 1) ∣ B → B ≠ 0 →
    β < S.psi B (Om (1 + 1)) → rhF β (S.psi B (Om (1 + 1))) = S.psi B (Om (1 + 1))

/-- **CONV(β)** for `ψ_{Ω₂}`: `w_{β+1} ∣ B` for every own `B` with `ψ_{Ω₂}(B)` a fixed point of `F_β`. -/
def TsCONV (S : InaccSeq.{0}) (β : Ordinal.{0}) : Prop :=
  ∀ B : Ordinal.{0}, B ∈ S.CSet B (S.psi B (Om (1 + 1))) →
    rhF β (S.psi B (Om (1 + 1))) = S.psi B (Om (1 + 1)) → leWe (β + 1) ∣ B

/-- `ψ_{Ω₂}(B) < ψ_{Ω₂}(B')` for an own `B < B'`. -/
theorem ts_psi_lt_of_own {B B' : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om (1 + 1)))) (h : B < B') :
    S.psi B (Om (1 + 1)) < S.psi B' (Om (1 + 1)) :=
  psi_lt_psi_of_mem (InR_Om_succ 1) h ((psi_mono (S := S) (InR_Om_succ 1) h.le).2 hown)

/-! ## The bridge at level `β` -/

/-- **`ψ_{Ω₂}(B + w_β·D) = F_β(c + D)`, and `D < ψ_{Ω₂}(B + w_β·D)`**, when `d < F_β(c+d)` for every `d ≤ D`, for an
own `B` with `w_β ∣ B` and `F_β(c) = ψ_{Ω₂}(B)`, `D < Ω₂`, given FWD below `β`. -/
theorem ts_eq {β : Ordinal.{0}} (hF : ∀ j < β, TsFWD S j)
    {B c : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om (1 + 1)))) (hB : leWe β ∣ B)
    (hc : rhF β c = S.psi B (Om (1 + 1))) :
    ∀ D, D < Om (1 + 1) → (∀ d, d ≤ D → d < rhF β (c + d)) →
      D < S.psi (B + leWe β * D) (Om (1 + 1)) ∧ S.psi (B + leWe β * D) (Om (1 + 1)) = rhF β (c + D) := by
  have hκ : S.InR (Om (1 + 1)) := InR_Om_succ 1
  set u := leWe β with hudef
  have hupos : 0 < u := tsU_pos β
  intro D
  induction D using WellFoundedLT.induction with
  | ind D IH =>
  intro hDΩ hcond
  have hIH : ∀ d, d < D → S.psi (B + u * d) (Om (1 + 1)) = rhF β (c + d) :=
    fun d hd => (IH d hd (hd.trans hDΩ) fun d' hd' => hcond d' (hd'.trans hd.le)).2
  have heq : S.psi (B + u * D) (Om (1 + 1)) = rhF β (c + D) := by
    rcases eq_or_ne D 0 with rfl | hD0
    · rw [mul_zero, add_zero, add_zero, hc]
    set v := S.psi (B + u * D) (Om (1 + 1)) with hv
    have hvSC : SC v := ts_psi_SC _
    have hBv : S.psi B (Om (1 + 1)) < v :=
      ts_psi_lt_of_own hown (lt_add_of_pos_right _ (mul_pos hupos (pos_iff_ne_zero.2 hD0)))
    have hβv : β < v := (rhF_left_le β c).trans_lt (hc ▸ hBv)
    have hlt : ∀ d, d < D → rhF β (c + d) < v := by
      intro d hd
      have hle : S.psi (B + u * d) (Om (1 + 1)) ≤ v :=
        (psi_mono (S := S) hκ ((add_le_add_iff_left B).2 (mul_le_mul_right hd.le _))).1
      have hdv : d < v := (hcond d hd.le).trans_le (by rw [← hIH d hd]; exact hle)
      have hmem : B + u * d ∈ S.CSet (B + u * D) v :=
        CSet.add_mem ((psi_mono (S := S) hκ (le_self_add : B ≤ B + u * D)).2 hown)
          (tsU_mul_mem hβv hdv)
      rw [← hIH d hd]
      exact psi_lt_psi_of_mem hκ ((add_lt_add_iff_left B).2 ((mul_lt_mul_iff_right₀ hupos).2 hd)) hmem
    apply le_antisymm
    · exact tsk_UB β B c D hB hc.ge hDΩ.le
    · rcases zero_or_succ_or_isSuccLimit D with h0 | ⟨d0, rfl⟩ | hlim
      · exact absurd h0 hD0
      · rw [Order.succ_eq_add_one] at hlt hDΩ ⊢
        have hd0v : d0 < v := (hcond d0 (Order.le_succ d0)).trans (hlt d0 (lt_add_one d0))
        have hDv : d0 + 1 < v := hvSC.add_one_lt hd0v
        have hown1 : B + u * (d0 + 1) ∈ S.CSet (B + u * (d0 + 1)) v :=
          CSet.add_mem ((psi_mono (S := S) hκ (le_self_add : B ≤ B + u * (d0 + 1))).2 hown)
            (tsU_mul_mem hβv hDv)
        have hne : B + u * (d0 + 1) ≠ 0 :=
          (lt_of_lt_of_le (mul_pos hupos (lt_of_le_of_lt zero_le (lt_add_one d0))) le_add_self).ne'
        have hfix : ∀ j < β, rhF j v = v := fun j hj =>
          hF j hj _ hown1 ((tsU_dvd_succ hj).trans (dvd_add hB (dvd_mul_right _ _))) hne (hj.trans hβv)
        obtain ⟨e, he⟩ := rhF_range hvSC hfix
        rw [← he]
        refine (rhF_le β).2 (not_lt.1 fun hlt' => ?_)
        have hle : e ≤ c + d0 := by
          rw [← add_assoc] at hlt'; exact Order.lt_add_one_iff.1 hlt'
        have := ((rhF_le β).2 hle).trans_lt (hlt d0 (lt_add_one d0))
        rw [he] at this
        exact lt_irrefl _ this
      · refine not_lt.1 fun hlt' => ?_
        obtain ⟨e, he, hve⟩ := ((rhF_normal β).lt_iff_exists_lt (isSuccLimit_add c hlim)).1 hlt'
        rcases lt_or_ge e c with hec | hce
        · have : rhF β e < v := ((rhF_lt β).2 hec).trans_le (by rw [hc]; exact hBv.le)
          exact absurd hve (not_lt.2 this.le)
        · have hσe : c + (e - c) = e := Ordinal.add_sub_cancel_of_le hce
          have hσ : e - c < D := by rw [← hσe] at he; exact (add_lt_add_iff_left c).1 he
          have := hlt _ hσ
          rw [hσe] at this
          exact absurd hve (not_lt.2 this.le)
  exact ⟨by rw [heq]; exact hcond D le_rfl, heq⟩

/-- **A valid `D` has `d < F_β(c+d)` for every `d ≤ D`** (`w_β ∣ B`, `F_β(c) = ψ_{Ω₂}(B)`). -/
theorem ts_valid {β B c D : Ordinal.{0}} (hB : leWe β ∣ B) (hc : rhF β c = S.psi B (Om (1 + 1)))
    (hv : D < S.psi (B + leWe β * D) (Om (1 + 1))) : ∀ d, d ≤ D → d < rhF β (c + d) := by
  intro d hd
  by_contra hle
  push Not at hle
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact absurd hle (not_le.2 (rhF_SC _ _).1)
  have hDΩ : D ≤ Om (1 + 1) := hv.le.trans (ts_psi_lt _).le
  have hcl : ∀ j < β, ∀ z < rhF β (c + d), rhF j z < rhF β (c + d) := fun j hj z hz => by
    have := (rhF_lt j).2 hz
    rwa [rhF_fix_lower hj] at this
  have hprev : ∀ d'', d'' < D → d'' < rhF β (c + d) →
      S.psi (B + leWe β * d'') (Om (1 + 1)) < rhF β (c + d) := fun d'' hd'' hq =>
    (tsk_UB β B c d'' hB hc.ge (hd''.le.trans hDΩ)).trans_lt
      ((rhF_lt β).2 ((add_lt_add_iff_left c).2 (hq.trans_le hle)))
  have h := tsk_inv (S := S) hB (rhF_SC β (c + d)) hcl
    (by rw [← hc]; exact (rhF_lt β).2 (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hd0))) hDΩ hprev
  exact absurd ((h.trans hle).trans hd) (not_le.2 hv)

/-! ## The fixed points of `Γ` -/

/-- `ψ_{Ω₂}(0) < ψ_{Ω₂}(B)` for every `B ≠ 0`. -/
theorem ts_psi0_lt {B : Ordinal.{0}} (hB0 : B ≠ 0) :
    S.psi 0 (Om (1 + 1)) < S.psi B (Om (1 + 1)) :=
  psi_lt_psi (InR_Om_succ 1) (pos_iff_ne_zero.2 hB0) (CSet.zero_mem _ _)

/-- **`ψ_{Ω₂}(B)` is a fixed point of `Γ`** for every own `B ≠ 0` with `Ω₂ ∣ B` (else `ψ_{Ω₂}(B) = Γ_{c+D} =
`ψ_{Ω₂}(B_p + D)` with `B_p + D < B` in `Cl(B, ψ_{Ω₂}(B))`, `ψ_{Ω₂}(B_p) = Γ_c` the first collapse at or above the
largest fixed point of `Γ` (or `ψ_{Ω₂}(0)`) below `ψ_{Ω₂}(B)`). -/
theorem ts_fix0 {B : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om (1 + 1))))
    (hdvd : Om (1 + 1) ∣ B) (hB0 : B ≠ 0) :
    gamma (S.psi B (Om (1 + 1))) = S.psi B (Om (1 + 1)) := by
  have hκ : S.InR (Om (1 + 1)) := InR_Om_succ 1
  set x := S.psi B (Om (1 + 1)) with hxdef
  set τ := S.psi 0 (Om (1 + 1)) with hτdef
  have hxSC : SC x := ts_psi_SC B
  have hx2 : x < Om (1 + 1) := ts_psi_lt B
  have hτx : τ < x := ts_psi0_lt hB0
  have hτ1 : Om 1 < τ := ts_Om1_lt_psi 0
  by_contra hnf
  obtain ⟨y, hy⟩ := lq_SC_gamma hxSC
  have hyx : y < x := by
    refine lt_of_le_of_ne (hy ▸ lq_le_gamma y) fun e => hnf ?_
    rw [← e] at hy ⊢; rw [hy]
  obtain ⟨p, hbase, hpx, hmax⟩ := rb_base_below hτx hnf
  have hτp : τ ≤ p := by
    rcases hbase with e | ⟨h, -⟩
    · exact e.ge
    · exact h.le
  have hpSC : SC p := by
    rcases hbase with e | ⟨-, h⟩
    · rw [e]; exact ts_psi_SC 0
    · rw [← h]; exact lq_gamma_SC p
  -- an own `B_p` with `p ≤ ψ_{Ω₂}(B_p) < x`
  obtain ⟨Bp, hownp, hpBp, hBpx⟩ : ∃ Bp, Bp ∈ S.CSet Bp (S.psi Bp (Om (1 + 1))) ∧
      p ≤ S.psi Bp (Om (1 + 1)) ∧ S.psi Bp (Om (1 + 1)) < x := by
    rcases hbase with e | -
    · exact ⟨0, CSet.zero_mem _ _, e.le, hτx⟩
    · exact ts_own_below hpSC (hτ1.trans_le hτp) hpx
  obtain ⟨c, hc⟩ := lq_SC_gamma (ts_psi_SC Bp)
  have hcy : c < y := gamma_lt_gamma.1 (by rw [hc, hy]; exact hBpx)
  set D := y - c with hDdef
  have hcD : c + D = y := Ordinal.add_sub_cancel_of_le hcy.le
  have hcond : ∀ d, d ≤ D → d < gamma (c + d) := by
    intro d hd
    by_contra hle
    push Not at hle
    have hz : gamma (c + d) = c + d :=
      le_antisymm (hle.trans le_add_self) (lq_le_gamma _)
    have hzy : c + d ≤ y := by rw [← hcD]; exact (add_le_add_iff_left c).2 hd
    have hcz : gamma c ≤ c + d := by rw [← hz]; exact gamma_le_gamma.2 le_self_add
    have hpz : p ≤ c + d := hpBp.trans (by rw [← hc]; exact hcz)
    rcases hpz.lt_or_eq with hpz | hpz
    · exact absurd (hmax _ hz (hτp.trans_lt hpz) (hzy.trans_lt hyx)) (not_le.2 hpz)
    · -- `c + d = p`: then `Γ_c = p`, `c = c + d`, `d = 0`
      have hcp : gamma c = gamma (c + d) := by
        refine le_antisymm (gamma_le_gamma.2 le_self_add) ?_
        rw [hz, ← hpz, hc]; exact hpBp
      have hcc : c = c + d := isNormal_gamma.strictMono.injective hcp
      have hd0 : d = 0 := by
        have : c + d = c + 0 := by rw [add_zero, ← hcc]
        exact add_left_cancel this
      rw [hd0, add_zero] at hle
      exact absurd hle (not_le.2 gamma_pos)
  have hDx : D < x := (Ordinal.sub_le_self y c).trans_lt hyx
  obtain ⟨-, hψ⟩ := ts_eq (S := S) (β := 0) (fun j hj => absurd hj (not_lt.2 zero_le)) hownp
    (by rw [leWe_zero]; exact one_dvd _) (by rw [rhF_zero, hc]) D (hDx.trans hx2)
    (by intro d hd; rw [rhF_zero]; exact hcond d hd)
  rw [leWe_zero, one_mul, rhF_zero, hcD, hy] at hψ
  have hBpB : Bp < B := by
    have h := compare_psi hκ hownp hown
    rw [compare_lt_iff_lt.2 hBpx] at h
    exact compare_lt_iff_lt.1 h.symm
  have hlt2 : Bp + D < B := rd_add_lt_of_dvd ts_Om2_indec hdvd hBpB (hDx.trans hx2)
  have hmem : Bp + D ∈ S.CSet B x :=
    CSet.add_mem ((psi_mono (S := S) hκ hBpB.le).2 hownp) (CSet.of_lt hDx)
  have hψmem : S.psi (Bp + D) (Om (1 + 1)) ∈ S.CSet B x :=
    CSet.psi_mem hlt2 hκ (mem_CSet_psi hκ B) hmem
  have := lt_psi_of_mem hκ hψmem (ts_psi_lt _)
  rw [hψ] at this
  exact lt_irrefl _ this

/-! ## The fixed points of `F_β` among the collapses -/

/-- **At every level `β`: FWD(β) and CONV(β)** for `ψ_{Ω₂}` and `w_β = Ω₂^β`. -/
theorem ts_fwd_conv (β : Ordinal.{0}) : TsFWD S β ∧ TsCONV S β := by
  have hκ : S.InR (Om (1 + 1)) := InR_Om_succ 1
  induction β using WellFoundedLT.induction with
  | ind β IH =>
  have h0 := ts_Om2_ne
  constructor
  · -- FWD
    intro B hown hB hB0 hβx
    rcases eq_or_ne β 0 with rfl | hβ0
    · rw [rhF_zero]
      rw [zero_add, leWe_one] at hB
      exact ts_fix0 hown hB hB0
    set x := S.psi B (Om (1 + 1)) with hxdef
    have hx2 : x < Om (1 + 1) := ts_psi_lt B
    have hxSC : SC x := ts_psi_SC B
    have hx1 : Om 1 < x := ts_Om1_lt_psi B
    have hxΓ : gamma x = x := by
      have h1 : leWe (0 + 1) ∣ B := (tsU_dvd (by rw [zero_add]; exact le_add_self)).trans hB
      have := (IH 0 (pos_iff_ne_zero.2 hβ0)).1 B hown h1 hB0 hxSC.1
      rwa [rhF_zero] at this
    have hlimx : IsSuccLimit x := ev_isSuccLimit_of_inE (Gg.gg_SC_eps hxSC)
    set u := leWe β with hudef
    have hu0 : u ≠ 0 := tsU_ne β
    have hupos : 0 < u := tsU_pos β
    obtain ⟨m, hm⟩ := hB
    rw [leWe_succ, ← hudef, mul_assoc] at hm
    have key : ∀ z < x, rhF β z < x := by
      intro z hz
      have hxI : Indec x := lq_SC_indec hxSC
      set a := Om 1 + β + z + 1 with hadef
      have hax : a < x := hxSC.add_one_lt (hxI.add_lt (hxI.add_lt hx1 hβx) hz)
      set p := gamma a with hpdef
      have hpx : p < x := by rw [← hxΓ]; exact gamma_lt_gamma.2 hax
      have hpSC : SC p := lq_gamma_SC a
      have hap : a < p := lt_of_le_of_ne (lq_le_gamma a) fun e => SC.ne_add_one hpSC (Om 1 + β + z) e.symm
      have hβp : β < p := by
        refine lt_of_le_of_lt ?_ hap
        rw [hadef]; exact le_add_self.trans (le_self_add.trans le_self_add)
      have hz1p : z + 1 < p := by
        refine lt_of_le_of_lt ?_ hap
        rw [hadef, add_assoc]; exact le_add_self
      have hp1 : Om 1 < p := by
        refine lt_of_le_of_lt ?_ hap
        rw [hadef]; exact le_self_add.trans (le_self_add.trans le_self_add)
      obtain ⟨Bp, hownp, hBpB, hpBp, -⟩ := ts_own_below_lt hown hpSC hp1 hpx
      set e := u * (Bp / u) + u with hedef
      have hBpe : Bp ≤ e := by
        calc Bp = u * (Bp / u) + Bp % u := (Ordinal.div_add_mod Bp u).symm
          _ ≤ e := add_le_add_right (Ordinal.mod_lt Bp hu0).le _
      have hpe : p ≤ S.psi e (Om (1 + 1)) := hpBp.trans (psi_mono hκ hBpe).1
      have hβe : β < S.psi e (Om (1 + 1)) := hβp.trans_le hpe
      have hBpmem : Bp ∈ S.CSet e (S.psi e (Om (1 + 1))) := (psi_mono hκ hBpe).2 hownp
      have howne : e ∈ S.CSet e (S.psi e (Om (1 + 1))) :=
        CSet.add_mem (ts_mod_mem (one_le_iff_ne_zero.2 hβ0) Bp hBpmem) (tsU_mem hβe)
      have hue : u ∣ e := ⟨Bp / u + 1, by rw [hedef, mul_add, mul_one]⟩
      have hue0 : 0 < e := lt_of_lt_of_le hupos le_add_self
      have hed : ∀ d, d < S.psi e (Om (1 + 1)) →
          e + u * d ∈ S.CSet (e + u * d) (S.psi (e + u * d) (Om (1 + 1))) ∧
            ∃ w, rhF β w = S.psi (e + u * d) (Om (1 + 1)) := by
        intro d hd
        have hle : S.psi e (Om (1 + 1)) ≤ S.psi (e + u * d) (Om (1 + 1)) := (psi_mono hκ le_self_add).1
        have hownd : e + u * d ∈ S.CSet (e + u * d) (S.psi (e + u * d) (Om (1 + 1))) :=
          CSet.add_mem ((psi_mono hκ le_self_add).2 howne)
            (tsU_mul_mem (hβe.trans_le hle) (hd.trans_le hle))
        refine ⟨hownd, rhF_range (ts_psi_SC _) fun j hj => ?_⟩
        exact (IH j hj).1 _ hownd ((tsU_dvd_succ hj).trans (dvd_add hue (dvd_mul_right _ _)))
          (lt_of_lt_of_le hue0 le_self_add).ne' (hj.trans (hβe.trans_le hle))
      have hmono : ∀ d d', d < d' → d' < S.psi e (Om (1 + 1)) →
          S.psi (e + u * d) (Om (1 + 1)) < S.psi (e + u * d') (Om (1 + 1)) := fun d d' hdd hd' =>
        ts_psi_lt_of_own (hed d (hdd.trans hd')).1
          ((add_lt_add_iff_left e).2 ((mul_lt_mul_iff_right₀ hupos).2 hdd))
      have hcount : ∀ d, d < S.psi e (Om (1 + 1)) → ∀ w, rhF β w = S.psi (e + u * d) (Om (1 + 1)) → d ≤ w := by
        intro d
        induction d using WellFoundedLT.induction with
        | ind d IHd =>
        intro hd w hw
        by_contra hwd
        push Not at hwd
        obtain ⟨w', hw'⟩ := (hed w (hwd.trans hd)).2
        have h1 := IHd w hwd (hwd.trans hd) w' hw'
        have h2 : rhF β w' < rhF β w := by rw [hw', hw]; exact hmono w d hwd hd
        exact absurd ((rhF_lt β).1 h2) (not_lt.2 h1)
      have hz1e : z + 1 < S.psi e (Om (1 + 1)) := hz1p.trans_le hpe
      obtain ⟨w, hw⟩ := (hed (z + 1) hz1e).2
      have hzw : z < w := (lt_add_one z).trans_le (hcount (z + 1) hz1e w hw)
      have hlt : e + u * (z + 1) < B := by
        have hq : Bp / u < Om (1 + 1) * m := by
          rw [hm] at hBpB; exact (Ordinal.lt_mul_iff_div_lt hu0).1 hBpB
        have h12 : (1 : Ordinal.{0}) < Om (1 + 1) := Gg.gg_one_lt_of_SC ts_SC_Om2
        have hc1 : 1 + (z + 1) < Om (1 + 1) :=
          ts_Om2_indec.add_lt h12 (ts_Om2_lim.add_one_lt (hz.trans hx2))
        have e1 : e + u * (z + 1) = u * (Bp / u + (1 + (z + 1))) := by
          simp only [hedef, mul_add, mul_one, add_assoc]
        rw [e1, hm]
        exact (mul_lt_mul_iff_right₀ hupos).2 (rd_add_lt_of_dvd ts_Om2_indec (dvd_mul_right _ _) hq hc1)
      have hψlt : S.psi (e + u * (z + 1)) (Om (1 + 1)) < x :=
        psi_lt_psi_of_mem hκ hlt ((psi_mono hκ hlt.le).2 (hed (z + 1) hz1e).1)
      calc rhF β z < rhF β w := (rhF_lt β).2 hzw
        _ = _ := hw
        _ < x := hψlt
    exact le_antisymm (((rhF_normal β).le_iff_forall_le hlimx).2 fun z hz => (key z hz).le)
      (rhF_le_self β x)
  · -- CONV
    intro B hown hfix
    set p := S.psi B (Om (1 + 1)) with hpdef
    have hpSC : SC p := ts_psi_SC B
    have hp1 : Om 1 < p := ts_Om1_lt_psi B
    have hu : leWe β ∣ B := by
      rcases zero_or_succ_or_isSuccLimit β with hz | ⟨j, rfl⟩ | hl
      · rw [hz, leWe_zero]; exact one_dvd B
      · rw [Order.succ_eq_add_one] at IH hfix ⊢
        exact (IH j (lt_add_one j)).2 B hown (rhF_fix_mono le_self_add hfix)
      · exact tsU_dvd_lim hl fun j hj =>
          (tsU_dvd le_self_add).trans ((IH j hj).2 B hown (rhF_fix_mono hj.le hfix))
    set u := leWe β with hudef
    set u2 := leWe (β + 1) with hu2def
    have hu2 : u2 = u * Om (1 + 1) := leWe_succ β
    have huu2 : u ∣ u2 := tsU_dvd le_self_add
    have hupos : 0 < u := tsU_pos β
    obtain ⟨m, hm⟩ := hu
    by_contra hnd
    set D0 := m % Om (1 + 1) with hD0
    set B0 := u2 * (m / Om (1 + 1)) with hB0
    have hBe : B0 + u * D0 = B := by
      rw [hm, hB0, hD0, hu2, mul_assoc, ← mul_add, Ordinal.div_add_mod]
    have hD0lt : D0 < Om (1 + 1) := Ordinal.mod_lt m h0
    have hD00 : D0 ≠ 0 := by
      intro e
      apply hnd
      rw [← hBe, e, mul_zero, add_zero, hB0]
      exact dvd_mul_right _ _
    have hcoll : ∀ e, e < B → e ∈ S.CSet B p →
        (∀ j : Ordinal.{0}, e / leWe j % Om (1 + 1) < p) → S.psi e (Om (1 + 1)) < p :=
      fun e he heC _ => lt_psi_of_mem hκ
        (CSet.psi_mem he hκ (mem_CSet_psi hκ B) heC) (psi_lt hκ _)
    have hdig := tsk_digits (S := S) hpSC hp1 hcoll B hown β
    have hmdiv : B / u = m := by rw [hm, Ordinal.mul_div_cancel _ (tsU_ne _)]
    rw [← hudef, hmdiv] at hdig
    have hD0p : D0 < p := hdig
    have hlt' : u * D0 < u2 := by rw [hu2]; exact (mul_lt_mul_iff_right₀ hupos).2 hD0lt
    have hBdiv : B / u2 = m / Om (1 + 1) := by
      calc B / u2 = (u2 * (m / Om (1 + 1)) + u * D0) / u2 := by rw [← hB0, hBe]
        _ = m / Om (1 + 1) := by
          rw [Ordinal.mul_add_div _ (tsU_ne (β + 1)), Ordinal.div_eq_zero_of_lt hlt', add_zero]
    have hB0m : B0 ∈ S.CSet B p := by
      have := ts_mod_mem (S := S) (m := β + 1) le_add_self B hown
      rwa [← hu2def, hBdiv] at this
    have hB0B : B0 < B := by
      rw [← hBe]; exact lt_add_of_pos_right _ (mul_pos hupos (pos_iff_ne_zero.2 hD00))
    have hB0p : S.psi B0 (Om (1 + 1)) < p := psi_lt_psi_of_mem hκ hB0B hB0m
    have hle := tsk_UB (S := S) β B0 (S.psi B0 (Om (1 + 1))) D0
      (by rw [hB0]; exact huu2.trans (dvd_mul_right _ _)) (rhF_le_self _ _) hD0lt.le
    rw [hBe] at hle
    have hlt : S.psi B0 (Om (1 + 1)) + D0 < p := (lq_SC_indec hpSC).add_lt hB0p hD0p
    have h2 : rhF β (S.psi B0 (Om (1 + 1)) + D0) < p := by
      conv_rhs => rw [← hfix]
      exact (rhF_lt β).2 hlt
    exact absurd (hle.trans_lt h2) (lt_irrefl _)

/-- **`ψ_{Ω₂}(B)` is a fixed point of `F_β`** for every own `B ≠ 0` with `Ω₂^{β+1} ∣ B` and `β < ψ_{Ω₂}(B)`. -/
theorem ts_fwd (β : Ordinal.{0}) : TsFWD S β := (ts_fwd_conv β).1

/-- **`Ω₂^{β+1} ∣ B`** for every own `B` with `ψ_{Ω₂}(B)` a fixed point of `F_β`. -/
theorem ts_conv (β : Ordinal.{0}) : TsCONV S β := (ts_fwd_conv β).2

/-- **The `ψ_{Ω₂} ↔ F_β` lemma at every level `β`**: for an own `B` with `Ω₂^β ∣ B`, `F_β(c) = ψ_{Ω₂}(B)` and
`D < Ω₂` with `d < F_β(c + d)` for every `d ≤ D`: `ψ_{Ω₂}(B + Ω₂^β·D) = F_β(c + D)` (and `D` is below it). -/
theorem ts_eq_all {β B c : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om (1 + 1)))) (hB : leWe β ∣ B)
    (hc : rhF β c = S.psi B (Om (1 + 1))) {D : Ordinal.{0}} (hD : D < Om (1 + 1))
    (hcond : ∀ d, d ≤ D → d < rhF β (c + d)) :
    D < S.psi (B + leWe β * D) (Om (1 + 1)) ∧ S.psi (B + leWe β * D) (Om (1 + 1)) = rhF β (c + D) :=
  ts_eq (fun j _ => ts_fwd j) hown hB hc D hD hcond

end Googology.Trans.PoR.InaccPsi.R2.Ts

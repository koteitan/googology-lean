import Googology.Trans.PoR.InaccPsi.R2.LwFix

/-!
# The first layer above `Φ_Γ`: Theorem START and SEG at `U = Ω₁^{Ω₁+1}`, and the fixed points of `GG`

`θ = ψ_{Ω₂}(Ω_ω)`, `P(η) = ψ_{Ω₁}(Ω_ω + θ·η)` (`Nm.Pv`), `W = Ω₁^{Ω₁}`, `U = Ω₁^{Ω₁+1} = W·Ω₁`,
`GG` = the enumeration of `{0} ∪ {Γ-points}`, `D = deriv GG` = the enumeration of the fixed points of
`GG` (Mathlib's `Ordinal.deriv`; `D(0) = 0`, `D(1) = Φ_Γ`).  `nxt F x` = the least value of `F` above `x`,
`Zu η₀ u` = the least `β` with `P(η₀ + u·β) ≤ β`.

* `lw_core` (the segment after one step `W`): for a good `η₁` that is a multiple of `W`,
  `P(η₁ + W) = GG(c')`, `P(η₁ + W + W·β) = GG(c' + β)` for `β ≤ Z' = Zu (η₁ + W) W`, `c' < Z'`, and
  `Z' = nxt D (P(η₁))`;
* `lw_start_U` (**Theorem START at `U`**): for a good `η₁` that is a multiple of `U`,
  `P(η₁ + U) = nxt D (P(η₁))` (the jump over level `Ω₁` with the invariant `linvG_HCl`);
* `lw_seg_U` (**Theorem SEG at `U`**): for a good `η₀` that is a multiple of `U` with `P(η₀) = D(c₀)`,
  `P(η₀ + U·β) = D(c₀ + β)` for every `β ≤ Zu η₀ U`;
* `lw_PU`, `lw_D_one`: `P(U) = D(1) = Φ_Γ`; `lw_Zu_U`: `Zu U U = nfp D 1` (the least fixed point of `D`
  above 0, i.e. the first point of the next layer);
* `lw_D_eq` (**the names of the fixed points of `GG`**): `D(α) = ψ_{Ω₁}(Ω_ω + θ·Ω₁^{Ω₁+1}·α)` for
  `1 ≤ α ≤ nfp D 1`; `lw_iota_D`: `ι(Ω₁^{Ω₁+1}·α) = D(α)` there; `lw_good_D`: `Ω₁^{Ω₁+1}·α` is good for
  `1 ≤ α < nfp D 1`.

No new axiom, no new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lw

open Googology.Trans.PoR.InaccPsi.R2.Br Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Nm

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq

variable {S : InaccSeq.{0}}

/-! ## `D = deriv GG` -/

theorem lw_D_zero : deriv GG 0 = 0 := by rw [deriv_zero_right, nfp_eq_self GG_zero]

theorem lw_D_one : deriv GG 1 = PhiG := by
  have := deriv_add_one GG 0
  rw [zero_add, lw_D_zero, zero_add] at this
  exact this

theorem lw_D_normal : IsNormal (deriv GG) := isNormal_deriv GG

theorem lw_D_fix (o : Ordinal.{0}) : GG (deriv GG o) = deriv GG o := deriv_fp GG_normal o

theorem lw_GP_isSuccLimit {l : Ordinal.{0}} (h : IsGP l) : IsSuccLimit l := by
  obtain ⟨c, hc⟩ : l ∈ range (VG (0 + 1)) := mem_range_VG_succ.2 (h.2 0 h.1)
  have hc0 : c ≠ 0 := by rintro rfl; rw [VG_at_zero] at hc; exact h.1.ne' hc.symm
  rw [← hc]; exact VG_isSuccLimit _ hc0

theorem lw_GP_principal {l : Ordinal.{0}} (h : IsGP l) : IsPrincipal (· + ·) l := by
  obtain ⟨d, hd⟩ : l ∈ range (VG (0 + 1)) := mem_range_VG_succ.2 (h.2 0 h.1)
  rw [← hd]; exact VG_principal _ d

theorem lw_GP_of_GGfix {w : Ordinal.{0}} (hw0 : 0 < w) (hfix : GG w = w) : IsGP w := by
  rw [← hfix]; exact isGP_GG hw0

theorem lw_D_pos {α : Ordinal.{0}} (hα : α ≠ 0) : 0 < deriv GG α := by
  have := lw_D_normal.strictMono (pos_iff_ne_zero.2 hα); rwa [lw_D_zero] at this

/-- The least value of `GG` above `x` is not a fixed point of `GG`. -/
theorem lw_nxtGG_not_fix (x : Ordinal.{0}) : GG (nxt GG x) ≠ nxt GG x := by
  obtain ⟨c, -, -, h2⟩ := nxt_spec GG_normal GG_zero x
  intro hfix
  rw [h2] at hfix
  have e := GG_strictMono.injective hfix
  have hlim := lw_GP_isSuccLimit (isGP_GG (lt_of_le_of_lt zero_le (lt_add_one c)))
  rw [e] at hlim
  exact lt_irrefl _ (hlim.add_one_lt (lt_add_one c))

theorem lw_U_eq : Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1) = W * Om 1 := by
  rw [opow_add, opow_one]

theorem lw_W_dvd_U : W ∣ Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1) := ⟨Om 1, lw_U_eq⟩

theorem lw_mem_U_mul {a b β : Ordinal.{0}} (hβ : β < b) :
    Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1) * β ∈ S.CSet a b := by
  have h1 : Om (1 : Ordinal.{0}) ∈ S.CSet a b := CSet.Om_mem (CSet.one_mem a b)
  have h2 : Om (1 : Ordinal.{0}) * Om 1 ∈ S.CSet a b := by
    rw [← Om1_opow, ← opow_add, ← veblen_zero_apply]
    exact CSet.phi_mem (CSet.zero_mem _ _) (CSet.add_mem h1 h1)
  rw [Om1_pow, mul_add_one]
  exact mem_opow_mul (CSet.add_mem h2 h1) hβ

/-! ## The segment after one step `W` -/

theorem lw_core {η1 : Ordinal.{0}} (hg : Bt.Good S η1) (hdvd : W ∣ η1) :
    ∃ c', Pv S (η1 + W) = GG c' ∧
      (∀ β ≤ Zu S (η1 + W) W, Pv S (η1 + W + W * β) = GG (c' + β)) ∧
      c' < Zu S (η1 + W) W ∧ Zu S (η1 + W) W = nxt (deriv GG) (Pv S η1) := by
  set x1 := Pv S η1 with hx1
  have h1 := start_GG hg hdvd
  obtain ⟨c', hc'⟩ := nxt_mem GG x1
  set η1' := η1 + W with hη1'
  set Z' := Zu S η1' W with hZ'
  have hy1 : Pv S η1' = GG c' := h1.trans hc'.symm
  have hg' : Bt.Good S η1' := by
    have := good_add (δ := W * 1) hg (mem_W_mul (one_lt_SC (Pv_SC S _)))
    rwa [mul_one] at this
  have hseg := seg_GG hg' (dvd_add hdvd dvd_rfl) hy1
  have hZSC : SC Z' := Zu_SC S η1' _
  have hfix : Pv S (η1' + W * Z') = Z' := Zu_fix S η1' _
  have hyZ : Pv S η1' < Z' := by
    by_contra hle
    rw [not_lt] at hle
    have hle2 : Pv S (η1' + 1) ≤ Pv S (η1' + W * Z') := by
      refine Pv_mono ((add_le_add_iff_left _).2 ?_)
      exact Order.one_le_iff_pos.2 (mul_pos W_pos hZSC.1)
    have := (Pv_lt_succ hg').trans_le hle2
    rw [hfix] at this
    exact absurd (this.trans_le hle) (lt_irrefl _)
  have hcZ : c' < Z' := ((GG_strictMono.id_le c').trans hy1.symm.le).trans_lt hyZ
  have hGZ : GG Z' = Z' := by
    have := hseg Z' le_rfl
    rw [hfix, hZSC.isPrincipal.add_eq_right hcZ] at this
    exact this.symm
  have hx1y : x1 < Pv S η1' := by rw [h1]; exact lt_nxt GG_normal GG_zero x1
  refine ⟨c', hy1, hseg, hcZ, le_antisymm ?_ ?_⟩
  · by_contra hlt
    rw [not_le] at hlt
    set w := nxt (deriv GG) x1 with hw
    have hwfix : GG w = w := (mem_range_deriv GG_normal).1 (nxt_mem _ _)
    have hxw : x1 < w := lt_nxt lw_D_normal lw_D_zero x1
    have hyw : Pv S η1' ≤ w := by
      rw [h1]; exact nxt_le GG_normal GG_zero ⟨w, hwfix⟩ hxw
    have hyw' : Pv S η1' < w := by
      refine lt_of_le_of_ne hyw fun e => ?_
      rw [h1] at e
      exact lw_nxtGG_not_fix x1 (by rw [e]; exact hwfix)
    have hcw : c' < w := by
      rw [hy1, ← hwfix] at hyw'; exact GG_strictMono.lt_iff_lt.1 hyw'
    have h2 := lt_Pv_of_lt_Zu hlt
    have hwp : IsPrincipal (· + ·) w :=
      lw_GP_principal (lw_GP_of_GGfix (lt_of_le_of_lt zero_le hcw) hwfix)
    rw [hseg w hlt.le, hwp.add_eq_right hcw, hwfix] at h2
    exact lt_irrefl _ h2
  · exact nxt_le lw_D_normal lw_D_zero ((mem_range_deriv GG_normal).2 hGZ) (hx1y.trans hyZ)

/-! ## Theorem START at `U` -/

/-- **Theorem START at `U = Ω₁^{Ω₁+1}`**: `P(η₁ + U) = nxt D (P(η₁))` for a good multiple `η₁` of `U`. -/
theorem lw_start_U {η1 : Ordinal.{0}} (hg : Bt.Good S η1)
    (hdvd : Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1) ∣ η1) :
    Pv S (η1 + Om 1 ^ (Om 1 + 1)) = nxt (deriv GG) (Pv S η1) := by
  have hdvd' : W ∣ η1 := dvd_trans lw_W_dvd_U hdvd
  obtain ⟨c', hy1, hseg, hcZ, hZ⟩ := lw_core hg hdvd'
  rw [← hZ]
  set x1 := Pv S η1 with hx1
  set η1' := η1 + W with hη1'
  set Z' := Zu S η1' W with hZ'
  have hZSC : SC Z' := Zu_SC S η1' _
  have hZ1 : Z' < Om 1 := Zu_lt_Om1 S η1' _
  have hfix : Pv S (η1' + W * Z') = Z' := Zu_fix S η1' _
  have hGZ : GG Z' = Z' := by
    have := hseg Z' le_rfl
    rw [hfix, hZSC.isPrincipal.add_eq_right hcZ] at this
    exact this.symm
  have hxZ : x1 < Z' := by
    have := lt_nxt lw_D_normal lw_D_zero x1; rwa [← hZ] at this
  apply le_antisymm
  · refine psi_le_of_key hZSC fun e he hea => ?_
    rcases lt_or_ge e (Om (ω : Ordinal.{0})) with he1 | he1
    · calc S.psi e (Om 1) ≤ Pv S 0 := by rw [Pv, A_zero]; exact (psi_mono Low.InR_Om_one he1.le).1
        _ ≤ x1 := Pv_mono zero_le
        _ < Z' := hxZ
    obtain ⟨η, hη, k1, k2⟩ := quotA hZ1 he he1
    have hψ : S.psi e (Om 1) ≤ Pv S (η + 1) := by
      rw [Pv, ← ConjT.A_succ]; exact (psi_mono Low.InR_Om_one k2.le).1
    have hηlt : η < η1 + Om 1 ^ (Om 1 + 1) := A_lt_A_iff.1 (k1.trans_lt hea)
    rcases lt_or_ge η η1 with hlt | hge
    · exact hψ.trans_lt ((Pv_mono (Order.add_one_le_of_lt hlt)).trans_lt hxZ)
    obtain ⟨q, z, r, hz, hr, hq⟩ := linvG_HCl hZSC hZ1 (le_rfl : Om (1 : Ordinal.{0}) ≤ Om 1) hη
    obtain ⟨q1, hq1⟩ := hdvd
    have hU0 : Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1) ≠ 0 := (Om1_pow_pos _).ne'
    have hlow : W * z + r < Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1) := by
      calc W * z + r < W * z + W := (add_lt_add_iff_left _).2 hr
        _ = W * (z + 1) := (mul_add_one _ _).symm
        _ ≤ W * Om 1 := by gcongr; exact Order.add_one_le_of_lt (hz.trans hZ1)
        _ = Om 1 ^ (Om 1 + 1) := lw_U_eq.symm
    have hq' : q = q1 := quot_eq hU0 hlow (by rw [hq, add_assoc]) (hq1 ▸ hge)
      (by rw [← hq1]; exact hηlt)
    subst hq'
    have hηe : η = η1 + (W * z + r) := by rw [hq, hq1, add_assoc]
    have hle : η + 1 ≤ η1' + W * (z + 1) := by
      rw [hηe, hη1', add_assoc, add_assoc, add_assoc]
      refine (add_le_add_iff_left η1).2 ?_
      calc W * z + (r + 1) ≤ W * z + W := (add_le_add_iff_left _).2 (Order.add_one_le_of_lt hr)
        _ = W * (z + 1) := (mul_add_one _ _).symm
        _ ≤ W + W * (z + 1) := le_add_self
    have hz1 : z + 1 ≤ Z' := Order.add_one_le_of_lt hz
    calc S.psi e (Om 1) ≤ Pv S (η + 1) := hψ
      _ ≤ Pv S (η1' + W * (z + 1)) := Pv_mono hle
      _ = GG (c' + (z + 1)) := hseg (z + 1) hz1
      _ < GG Z' := GG_strictMono (hZSC.isPrincipal hcZ (hZSC.add_one_lt hz))
      _ = Z' := hGZ
  · calc Z' = Pv S (η1' + W * Z') := hfix.symm
      _ ≤ Pv S (η1 + Om 1 ^ (Om 1 + 1)) := by
        refine Pv_mono ?_
        rw [hη1', add_assoc, ← mul_one_add, (hZSC.isPrincipal.add_eq_right (one_lt_SC hZSC)),
          lw_U_eq]
        gcongr

/-! ## Theorem SEG at `U` and the names of the fixed points of `GG` -/

/-- **Theorem SEG at `U`.** -/
theorem lw_seg_U {η0 c0 : Ordinal.{0}} (hg0 : Bt.Good S η0)
    (hdvd : Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1) ∣ η0) (h0 : Pv S η0 = deriv GG c0) :
    ∀ β ≤ Zu S η0 (Om 1 ^ (Om 1 + 1)),
      Pv S (η0 + Om 1 ^ (Om 1 + 1) * β) = deriv GG (c0 + β) := by
  refine aseg lw_D_normal (Om1_pow_pos _) h0 fun β' hβ' ih => ?_
  set η1 := η0 + Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1) * β' with hη1
  have hβP : β' < Pv S η1 := lt_Pv_of_lt_Zu hβ'
  have hg1 : Bt.Good S η1 := good_add hg0 (lw_mem_U_mul hβP)
  have hd1 : Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1) ∣ η1 :=
    dvd_add hdvd (dvd_mul_right _ _)
  have := lw_start_U hg1 hd1
  rw [ih, nxt_apply lw_D_normal lw_D_zero] at this
  rw [mul_add_one, ← add_assoc]
  exact this

theorem lw_good_U (S : InaccSeq.{0}) : Bt.Good S (Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1)) := by
  have h := lw_mem_U_mul (S := S) (a := ConjT.Aη S (Om 1 ^ (Om 1 + 1)) + 1)
    (b := Pv S (Om 1 ^ (Om 1 + 1))) (β := 1) (one_lt_SC (Pv_SC S _))
  rwa [mul_one] at h

/-- `P(U) = D(1) = Φ_Γ`. -/
theorem lw_PU (S : InaccSeq.{0}) : Pv S (Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1)) = deriv GG 1 := by
  rw [lw_D_one]; exact (PhiG_eq S).symm

/-- `Zu U U = nfp D 1`: the segment from `U` runs up to the least fixed point of `D`. -/
theorem lw_Zu_U (S : InaccSeq.{0}) :
    Zu S (Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1)) (Om 1 ^ (Om 1 + 1)) = nfp (deriv GG) 1 := by
  have hseg := lw_seg_U (S := S) (lw_good_U S) dvd_rfl (lw_PU S)
  set Z := Zu S (Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1)) (Om 1 ^ (Om 1 + 1)) with hZ
  have hZSC : SC Z := Zu_SC S _ _
  have hfix := Zu_fix S (Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1)) (Om 1 ^ (Om 1 + 1))
  have hωZ : (ω : Ordinal.{0}) ≤ Z := Ordinal.omega0_le_of_isSuccLimit hZSC.isSuccLimit
  have hDZ : deriv GG Z = Z := by
    have := hseg Z le_rfl
    rw [← hZ] at hfix
    rw [hfix, one_add_of_omega0_le hωZ] at this
    exact this.symm
  set N := nfp (deriv GG) 1 with hN
  have hNfix : deriv GG N = N := nfp_fp lw_D_normal 1
  have hN1 : 1 ≤ N := le_nfp _ _
  have hωN : (ω : Ordinal.{0}) ≤ N := by
    have hN0 : N ≠ 0 := (lt_of_lt_of_le zero_lt_one hN1).ne'
    have hGGN : GG N = N := by have := lw_D_fix N; rwa [hNfix] at this
    exact Ordinal.omega0_le_of_isSuccLimit
      (lw_GP_isSuccLimit (lw_GP_of_GGfix (pos_iff_ne_zero.2 hN0) hGGN))
  refine le_antisymm ?_ ?_
  · by_contra hlt
    rw [not_le] at hlt
    have h2 := lt_Pv_of_lt_Zu hlt
    rw [hseg N hlt.le, one_add_of_omega0_le hωN, hNfix] at h2
    exact lt_irrefl _ h2
  · exact nfp_le_fp lw_D_normal.strictMono.monotone (Order.one_le_iff_pos.2 hZSC.1) hDZ.le

/-- **The names of the fixed points of `GG`**: `D(α) = ψ_{Ω₁}(Ω_ω + θ·Ω₁^{Ω₁+1}·α)` for
`1 ≤ α ≤ nfp D 1`. -/
theorem lw_D_eq (S : InaccSeq.{0}) {α : Ordinal.{0}} (hα1 : 1 ≤ α) (hα : α ≤ nfp (deriv GG) 1) :
    deriv GG α =
      S.psi (Om ω + ConjT.th S * (Om 1 ^ (Om (1 : Ordinal.{0}) + 1) * α)) (Om 1) := by
  have hseg := lw_seg_U (S := S) (lw_good_U S) dvd_rfl (lw_PU S)
  have e1 : 1 + (α - 1) = α := Ordinal.add_sub_cancel_of_le hα1
  have hb : α - 1 ≤ Zu S (Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1)) (Om 1 ^ (Om 1 + 1)) := by
    rw [lw_Zu_U]; exact (Ordinal.sub_le_self _ _).trans hα
  have := hseg (α - 1) hb
  rw [e1] at this
  show deriv GG α = Pv S (Om 1 ^ (Om 1 + 1) * α)
  rw [← this, ← e1, mul_add, mul_one, e1]

/-- `ι(Ω₁^{Ω₁+1}·α) = D(α)` for `1 ≤ α ≤ nfp D 1`. -/
theorem lw_iota_D (S : InaccSeq.{0}) {α : Ordinal.{0}} (hα1 : 1 ≤ α) (hα : α ≤ nfp (deriv GG) 1) :
    iota S (Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1) * α) = deriv GG α := by
  have hα0 : α ≠ 0 := (lt_of_lt_of_le zero_lt_one hα1).ne'
  have hGP : IsGP (deriv GG α) := lw_GP_of_GGfix (lw_D_pos hα0) (lw_D_fix α)
  exact iota_of_fix (lw_D_eq S hα1 hα).symm (lw_ups_of_GP hGP)

/-- `Ω₁^{Ω₁+1}·α` is good for `1 ≤ α < nfp D 1`. -/
theorem lw_good_D (S : InaccSeq.{0}) {α : Ordinal.{0}} (hα1 : 1 ≤ α) (hα : α < nfp (deriv GG) 1) :
    Bt.Good S (Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1) * α) := by
  have hP : Pv S (Om 1 ^ (Om 1 + 1) * α) = deriv GG α := (lw_D_eq S hα1 hα.le).symm
  have hαP : α < Pv S (Om 1 ^ (Om 1 + 1) * α) := by
    rw [hP]
    refine lt_of_le_of_ne (lw_D_normal.strictMono.id_le α) fun e => ?_
    have : nfp (deriv GG) 1 ≤ α := nfp_le_fp lw_D_normal.strictMono.monotone hα1 e.symm.le
    exact absurd hα (not_lt.2 this)
  exact lw_mem_U_mul hαP

end Googology.Trans.PoR.InaccPsi.R2.Lw

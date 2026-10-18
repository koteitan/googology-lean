import Googology.Trans.PoR.InaccPsi.R2.FpLev

/-!
# `GgPoly` for `lzWw`, `ltS K`, `ltSw`, `lnS K`, `lnSw` up to the codes of their tops

Tops and their codes (`Θ_y(code) = top(y)` at every strongly critical `y < Ω₁`, `R2.Fp.FpLev`):
`lzWw`: `y_ω`, `phYw = φ(ω, Ω₁ + ω)`; `ltS K`: `T_K`, `fpTc K = φ(ω, phW K)`; `ltSw`: `sup_K T_K`,
`fpTw = φ(ω, phYw)`; `lnS K`: `c_{K+1}`, `fpCc (K+1)`; `lnSw`: `P`, `fpPc = φ(ω+1, Ω₁ + 1)`.

A code `c` over a strongly critical `Z` above `Ω₁` is a sum, a power, `φ_k(b)` (the term `th k`, with
`Ph.phIndCode`, `Ph.phTh_th`), or `φ(ω, γ)`: then `γ = Ω₁ + 1 + d` and `Θ_y(c) = φ(ω, y + 1 + Θ_y(d)) =
ϑʸ(Ω₁·ω + Θ_y(d))` (`Fp.fpW_eq`), the term `tw` of a term of `d`.

* `fpSub` (the argument `d = γ - (Ω₁ + 1)` of `φ(ω, γ)` and the reading of `φ(ω, γ)`);
* `fpPoly_lzWw`, `fpPoly_ltS`, `fpPoly_ltSw`, `fpLn` (terms of `LnW` of depth `≤ K` for the codes below
  `fpCc K`), `fpPoly_lnS`, `fpPoly_lnSw` (**`GgPoly` of the five systems up to the codes of their tops**).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Fp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ly
  Googology.Trans.PoR.InaccPsi.R2.Lz Googology.Trans.PoR.InaccPsi.R2.Lt Googology.Trans.PoR.InaccPsi.R2.Ph

variable {Z : Ordinal.{0}}

/-- **The argument of `φ(ω, γ)`**: `d = γ - (Ω₁ + 1)` is a code, `d ≤ γ`, `Ω₁ + 1 + d = γ`, and
`Θ_y(φ(ω, γ)) = φ(ω, y + 1 + Θ_y(d))`. -/
theorem fpSub (hZ : SC Z) {γ : Ordinal.{0}} (hγ : GgCl Z γ) (hγ1 : Om 1 < γ) :
    GgCl Z (γ - (Om 1 + 1)) ∧ γ - (Om 1 + 1) ≤ γ ∧ Om 1 + 1 + (γ - (Om 1 + 1)) = γ ∧
      ∀ y, SC y → y < Om 1 → Z ≤ y → ggTh y (veblen ω γ) = veblen ω (y + 1 + ggTh y (γ - (Om 1 + 1))) := by
  have hb1 : Om 1 + 1 ≤ γ := Order.add_one_le_of_lt hγ1
  have hγe : Om 1 + 1 + (γ - (Om 1 + 1)) = γ := Ordinal.add_sub_cancel_of_le hb1
  refine ⟨(ggDec hZ γ hγ).1 _ (ph_cl_Om1_one hZ) hb1, Ordinal.sub_le_self _ _, hγe, fun y hy hy1 hZy => ?_⟩
  have h : ggTh y γ = y + 1 + ggTh y (γ - (Om 1 + 1)) := by
    conv_lhs => rw [← hγe]
    rw [ggTh_add hy (ph_cl_Om1_one hy), phTh_Om1_one hy hy1]
  rw [phTh_veblen_omega hy (hγ.mono hZy), h]

/-- **`lzWw` has terms for every code below `phYw`.** -/
theorem fpPoly_lzWw : GgPoly lzWw phYw := fun Z c hc hcE => by
  obtain ⟨K, hK⟩ := fp_lt_Yw hcE
  obtain ⟨s, hs⟩ := phPoly_lzW K Z c hc hK
  exact ⟨s, fun y hy hy1 hZy => ⟨(hs y hy hy1 hZy).1.1, (hs y hy hy1 hZy).2⟩⟩

/-- **`ltS K` has terms for every code below `fpTc K`.** -/
theorem fpPoly_ltS (K : ℕ) : GgPoly (ltS K) (fpTc K) := by
  refine phPoly_of_SC fun Z hZ _ => ?_
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hcT
  rcases lt_trichotomy c (Om 1) with hc1 | hc1 | hc1
  · have hcZ : c < Z := hc.lt_of_lt_Om1 hZ hc1
    exact ⟨LtW.lz (LzW.vz (VzTm.cst c)), fun y _ _ hZy =>
      ⟨⟨lt_of_lt_of_le hcZ hZy, Nat.zero_le _⟩, by show c = ggTh y c; rw [ggTh_small (hcZ.le.trans hZy)]⟩⟩
  · subst hc1
    exact ⟨LtW.lz (LzW.vz VzTm.bs), fun y hy hy1 _ =>
      ⟨⟨trivial, Nat.zero_le _⟩, by show y = ggTh y (Om 1); rw [ggTh_Om1 hy hy1]⟩⟩
  have hc0 : c ≠ 0 := (lt_of_le_of_lt zero_le hc1).ne'
  rcases phShape hZ hc hc0 with ⟨u, v, hu, hv, huc, hvc, rfl⟩ | ⟨L, hL, hLc, rfl⟩ | hcE'
  · obtain ⟨s1, hs1⟩ := IH u huc hu (huc.trans hcT)
    obtain ⟨s2, hs2⟩ := IH v hvc hv (hvc.trans hcT)
    refine ⟨LtW.sm s1 s2, fun y hy hy1 hZy => ?_⟩
    obtain ⟨c1, v1⟩ := hs1 y hy hy1 hZy
    obtain ⟨c2, v2⟩ := hs2 y hy hy1 hZy
    exact ⟨⟨⟨c1.1, c2.1⟩, max_le c1.2 c2.2⟩, by
      show (ltS K).val s1 y + (ltS K).val s2 y = _
      rw [v1, v2, ggTh_add hy (hu.mono hZy)]⟩
  · obtain ⟨s1, hs1⟩ := IH L hLc hL (hLc.trans hcT)
    refine ⟨LtW.pw s1, fun y hy hy1 hZy => ?_⟩
    obtain ⟨c1, v1⟩ := hs1 y hy hy1 hZy
    exact ⟨c1, by show ω ^ (ltS K).val s1 y = _; rw [v1, ggTh_opow hy (hL.mono hZy)]⟩
  rcases phEpsDec hZ hc hc1 hcE' with ⟨γ, hγ, hγ1, -, e⟩ | ⟨k, hk, b, hb, hbO, hbv, e⟩ | ⟨a, b, ha, -, e⟩
  · -- `c = φ(ω, γ)`, `γ < phW K`: the term `tw` of the `LzW`-term of `γ - (Ω₁ + 1)`
    have hγK : γ < phW K := by
      have h0 : veblen ω γ < veblen ω (phW K) := by rw [← e]; exact hcT
      exact veblen_lt_veblen_iff_right.1 h0
    obtain ⟨hd, hdγ, -, hTh⟩ := fpSub hZ hγ hγ1
    obtain ⟨a, ha⟩ := phPoly_lzW K Z _ hd (hdγ.trans_lt hγK)
    refine ⟨LtW.tw a, fun y hy hy1 hZy => ?_⟩
    obtain ⟨⟨ca, la⟩, va⟩ := ha y hy hy1 hZy
    have hyE := gg_SC_eps hy
    have h1 := fp_Om1' hy1
    have hT := lzw_T hyE h1 a ca
    have hP : LzW.val a y < ltP y :=
      ((lzw_lt_top hyE h1 a ca la).trans (lzY_lt_w hyE h1 K)).trans (ltC_lt_P hyE h1 0)
    have va' : LzW.val a y = ggTh y (γ - (Om 1 + 1)) := va
    refine ⟨⟨ca, la⟩, ?_⟩
    show vt y (Om1 * ω + LzW.val a y) = ggTh y c
    rw [fpW_eq hy h1 _ hT.1 hT.2 hP, e, hTh y hy hy1 hZy, va']
  · obtain ⟨d, hd, hdb, hdθ⟩ := phIndCode hZ hb hbO hbv
    have hbc : b < c := by rw [e]; exact hbv
    obtain ⟨t, ht⟩ := IH d (hdb.trans_lt hbc) hd ((hdb.trans_lt hbc).trans hcT)
    refine ⟨LtW.th k t, fun y hy hy1 hZy => ?_⟩
    obtain ⟨ct, vt'⟩ := ht y hy hy1 hZy
    have hy1' := fp_Om1' hy1
    refine ⟨⟨⟨hk, ct.1⟩, ct.2⟩, ?_⟩
    show vt y (Om1 * (k : Ordinal.{0}) + (ltS K).val t y) = ggTh y c
    have hTv : (ltS K).val t y ∈ Tset y ∧ (ltS K).val t y < Om1 := ltw_T (gg_SC_eps hy) hy1' t ct.1
    have e1 : (ltS K).val t y = phInd k y (ggTh y b) := by rw [vt', hdθ y hy hy1 hZy]
    rw [e1] at hTv ⊢
    rw [e, phTh_th hy hy1 hk (hb.mono hZy) hbO hbv hTv.1 hTv.2]
  · exfalso
    have h0 : veblen a b < veblen ω (phW K) := by rw [← e]; exact hcT
    have h1 := ph_veblen_lt_of_gt ha h0
    have h2 : veblen a b < veblen ω (Om 1 + 1 + K) := h1
    have h3 := ph_veblen_lt_of_gt ha h2
    rw [← e] at h3
    have h4 := ph_eps_gt hcE' hc1 (1 + K)
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc] at h4
    exact absurd h3 (not_lt.2 h4.le)

/-- **`ltSw` has terms for every code below `fpTw`.** -/
theorem fpPoly_ltSw : GgPoly ltSw fpTw := by
  refine phPoly_of_SC fun Z hZ _ => ?_
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hcT
  rcases lt_trichotomy c (Om 1) with hc1 | hc1 | hc1
  · have hcZ : c < Z := hc.lt_of_lt_Om1 hZ hc1
    exact ⟨LtW.lz (LzW.vz (VzTm.cst c)), fun y _ _ hZy =>
      ⟨lt_of_lt_of_le hcZ hZy, by show c = ggTh y c; rw [ggTh_small (hcZ.le.trans hZy)]⟩⟩
  · subst hc1
    exact ⟨LtW.lz (LzW.vz VzTm.bs), fun y hy hy1 _ =>
      ⟨trivial, by show y = ggTh y (Om 1); rw [ggTh_Om1 hy hy1]⟩⟩
  have hc0 : c ≠ 0 := (lt_of_le_of_lt zero_le hc1).ne'
  rcases phShape hZ hc hc0 with ⟨u, v, hu, hv, huc, hvc, rfl⟩ | ⟨L, hL, hLc, rfl⟩ | hcE'
  · obtain ⟨s1, hs1⟩ := IH u huc hu (huc.trans hcT)
    obtain ⟨s2, hs2⟩ := IH v hvc hv (hvc.trans hcT)
    refine ⟨LtW.sm s1 s2, fun y hy hy1 hZy => ?_⟩
    obtain ⟨c1, v1⟩ := hs1 y hy hy1 hZy
    obtain ⟨c2, v2⟩ := hs2 y hy hy1 hZy
    exact ⟨⟨c1, c2⟩, by
      show ltSw.val s1 y + ltSw.val s2 y = _
      rw [v1, v2, ggTh_add hy (hu.mono hZy)]⟩
  · obtain ⟨s1, hs1⟩ := IH L hLc hL (hLc.trans hcT)
    refine ⟨LtW.pw s1, fun y hy hy1 hZy => ?_⟩
    obtain ⟨c1, v1⟩ := hs1 y hy hy1 hZy
    exact ⟨c1, by show ω ^ ltSw.val s1 y = _; rw [v1, ggTh_opow hy (hL.mono hZy)]⟩
  rcases phEpsDec hZ hc hc1 hcE' with ⟨γ, hγ, hγ1, -, e⟩ | ⟨k, hk, b, hb, hbO, hbv, e⟩ | ⟨a, b, ha, -, e⟩
  · have hγK : γ < phYw := by
      have h0 : veblen ω γ < veblen ω phYw := by rw [← e]; exact hcT
      exact veblen_lt_veblen_iff_right.1 h0
    obtain ⟨hd, hdγ, -, hTh⟩ := fpSub hZ hγ hγ1
    obtain ⟨K, hK⟩ := fp_lt_Yw (hdγ.trans_lt hγK)
    obtain ⟨a, ha⟩ := phPoly_lzW K Z _ hd hK
    refine ⟨LtW.tw a, fun y hy hy1 hZy => ?_⟩
    obtain ⟨⟨ca, la⟩, va⟩ := ha y hy hy1 hZy
    have hyE := gg_SC_eps hy
    have h1 := fp_Om1' hy1
    have hT := lzw_T hyE h1 a ca
    have hP : LzW.val a y < ltP y :=
      ((lzw_lt_top hyE h1 a ca la).trans (lzY_lt_w hyE h1 K)).trans (ltC_lt_P hyE h1 0)
    have va' : LzW.val a y = ggTh y (γ - (Om 1 + 1)) := va
    refine ⟨ca, ?_⟩
    show vt y (Om1 * ω + LzW.val a y) = ggTh y c
    rw [fpW_eq hy h1 _ hT.1 hT.2 hP, e, hTh y hy hy1 hZy, va']
  · obtain ⟨d, hd, hdb, hdθ⟩ := phIndCode hZ hb hbO hbv
    have hbc : b < c := by rw [e]; exact hbv
    obtain ⟨t, ht⟩ := IH d (hdb.trans_lt hbc) hd ((hdb.trans_lt hbc).trans hcT)
    refine ⟨LtW.th k t, fun y hy hy1 hZy => ?_⟩
    obtain ⟨ct, vt'⟩ := ht y hy hy1 hZy
    have hy1' := fp_Om1' hy1
    refine ⟨⟨hk, ct⟩, ?_⟩
    show vt y (Om1 * (k : Ordinal.{0}) + ltSw.val t y) = ggTh y c
    have hTv : ltSw.val t y ∈ Tset y ∧ ltSw.val t y < Om1 := ltw_T (gg_SC_eps hy) hy1' t ct
    have e1 : ltSw.val t y = phInd k y (ggTh y b) := by rw [vt', hdθ y hy hy1 hZy]
    rw [e1] at hTv ⊢
    rw [e, phTh_th hy hy1 hk (hb.mono hZy) hbO hbv hTv.1 hTv.2]
  · exfalso
    have h0 : veblen a b < veblen ω phYw := by rw [← e]; exact hcT
    have h1 := ph_veblen_lt_of_gt ha h0
    have h2 : veblen a b < veblen ω (Om 1 + ω) := h1
    have h3 := ph_veblen_lt_of_gt ha h2
    rw [← e] at h3
    have h4 : Om 1 + ω < c := fp_prin hcE' hc1 (omega0_lt_inE hcE')
    exact absurd h3 (not_lt.2 h4.le)

theorem fp_Om1_lt_C : ∀ K, Om 1 < fpCc K
  | 0 => (lt_add_of_pos_right _ omega0_pos).trans_le (right_le_veblen _ _)
  | K + 1 => (fp_Om1_lt_C K).trans_le (right_le_veblen _ _)

/-- **Terms of `LnW` of depth `≤ K` for the codes below `fpCc K`.** -/
theorem fpLn (hZ : SC Z) : ∀ K : ℕ, ∀ c, GgCl Z c → c < fpCc K →
    ∃ t : LnW, LnW.dp t ≤ K ∧ ∀ y, SC y → y < Om 1 → Z ≤ y → LnW.CBt t y ∧ LnW.val t y = ggTh y c := by
  intro K
  induction K with
  | zero =>
    intro c hc hcK
    obtain ⟨K', hK'⟩ := fp_lt_Yw hcK
    obtain ⟨a, ha⟩ := phPoly_lzW K' Z c hc hK'
    exact ⟨LnW.lz a, le_rfl, fun y hy hy1 hZy => ⟨(ha y hy hy1 hZy).1.1, (ha y hy hy1 hZy).2⟩⟩
  | succ K ihK =>
    intro c
    induction c using WellFoundedLT.induction with
    | ind c IH =>
    intro hc hcK
    rcases lt_or_ge c (fpCc K) with hlt | hge
    · obtain ⟨t, hdp, ht⟩ := ihK c hc hlt
      exact ⟨t, hdp.trans (Nat.le_succ K), ht⟩
    have hc1 : Om 1 < c := (fp_Om1_lt_C K).trans_le hge
    have hc0 : c ≠ 0 := (lt_of_le_of_lt zero_le hc1).ne'
    rcases phShape hZ hc hc0 with ⟨u, v, hu, hv, huc, hvc, rfl⟩ | ⟨L, hL, hLc, rfl⟩ | hcE'
    · obtain ⟨s1, d1, hs1⟩ := IH u huc hu (huc.trans hcK)
      obtain ⟨s2, d2, hs2⟩ := IH v hvc hv (hvc.trans hcK)
      refine ⟨LnW.sm s1 s2, max_le d1 d2, fun y hy hy1 hZy => ?_⟩
      obtain ⟨c1, v1⟩ := hs1 y hy hy1 hZy
      obtain ⟨c2, v2⟩ := hs2 y hy hy1 hZy
      exact ⟨⟨c1, c2⟩, by rw [LnW.val_sm, v1, v2, ggTh_add hy (hu.mono hZy)]⟩
    · obtain ⟨s1, d1, hs1⟩ := IH L hLc hL (hLc.trans hcK)
      refine ⟨LnW.pw s1, d1, fun y hy hy1 hZy => ?_⟩
      obtain ⟨c1, v1⟩ := hs1 y hy hy1 hZy
      exact ⟨c1, by rw [LnW.val_pw, v1, ggTh_opow hy (hL.mono hZy)]⟩
    rcases phEpsDec hZ hc hc1 hcE' with ⟨γ, hγ, hγ1, -, e⟩ | ⟨k, hk, b, hb, hbO, hbv, e⟩ | ⟨a, b, ha, -, e⟩
    · have hγK : γ < fpCc K := by
        have h0 : veblen ω γ < veblen ω (fpCc K) := by rw [← e]; exact hcK
        exact veblen_lt_veblen_iff_right.1 h0
      obtain ⟨hd, hdγ, -, hTh⟩ := fpSub hZ hγ hγ1
      obtain ⟨t, hdp, ht⟩ := ihK _ hd (hdγ.trans_lt hγK)
      refine ⟨LnW.tw t, Nat.succ_le_succ hdp, fun y hy hy1 hZy => ?_⟩
      obtain ⟨ct, vt'⟩ := ht y hy hy1 hZy
      have hyE := gg_SC_eps hy
      have h1 := fp_Om1' hy1
      have hT := ln_T hyE h1 t ct
      have hP : LnW.val t y < ltP y := (ln_lt_top hyE h1 t ct hdp).trans (ltC_lt_P hyE h1 K)
      refine ⟨ct, ?_⟩
      rw [LnW.val_tw, fpW_eq hy h1 _ hT.1 hT.2 hP, e, hTh y hy hy1 hZy, vt']
    · obtain ⟨d, hd, hdb, hdθ⟩ := phIndCode hZ hb hbO hbv
      have hbc : b < c := by rw [e]; exact hbv
      obtain ⟨t, hdp, ht⟩ := IH d (hdb.trans_lt hbc) hd ((hdb.trans_lt hbc).trans hcK)
      refine ⟨LnW.th k t, hdp, fun y hy hy1 hZy => ?_⟩
      obtain ⟨ct, vt'⟩ := ht y hy hy1 hZy
      have hy1' := fp_Om1' hy1
      refine ⟨⟨hk, ct⟩, ?_⟩
      have hTv : LnW.val t y ∈ Tset y ∧ LnW.val t y < Om1 := ln_T (gg_SC_eps hy) hy1' t ct
      have e1 : LnW.val t y = phInd k y (ggTh y b) := by rw [vt', hdθ y hy hy1 hZy]
      rw [e1] at hTv
      rw [LnW.val_th, e1, e, phTh_th hy hy1 hk (hb.mono hZy) hbO hbv hTv.1 hTv.2]
    · exfalso
      have h0 : veblen a b < veblen ω (fpCc K) := by rw [← e]; exact hcK
      have h1 := ph_veblen_lt_of_gt ha h0
      rw [← e] at h1
      exact absurd h1 (not_lt.2 hge)

/-- **`lnS K` has terms for every code below `fpCc (K+1)`.** -/
theorem fpPoly_lnS (K : ℕ) : GgPoly (lnS K) (fpCc (K + 1)) := by
  refine phPoly_of_SC fun Z hZ _ c hc hcT => ?_
  obtain ⟨t, hdp, ht⟩ := fpLn hZ (K + 1) c hc hcT
  exact ⟨t, fun y hy hy1 hZy => ⟨⟨(ht y hy hy1 hZy).1, hdp⟩, (ht y hy hy1 hZy).2⟩⟩

/-- **`lnSw` has terms for every code below `fpPc = φ(ω+1, Ω₁ + 1)`.** -/
theorem fpPoly_lnSw : GgPoly lnSw fpPc := by
  refine phPoly_of_SC fun Z hZ _ c hc hcT => ?_
  obtain ⟨K, hK⟩ := fp_lt_C hcT
  obtain ⟨t, -, ht⟩ := fpLn hZ K c hc hK
  exact ⟨t, ht⟩

end Googology.Trans.PoR.InaccPsi.R2.Fp

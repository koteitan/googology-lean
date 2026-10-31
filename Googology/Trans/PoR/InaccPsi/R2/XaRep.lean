import Googology.Trans.PoR.InaccPsi.R2.WwRoad
import Googology.Trans.PoR.InaccPsi.R2.CitedUz
import Googology.Trans.PoR.InaccPsi.R2.SePi

/-!
# Every countable ordinal below `υ_{λ+β}` is the value of a repaired decomposition

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

The repaired decompositions `Ww.WwE` (old nodes, `ϑ`-nodes `ϑ^{υ_{λ+h}}(Ω₁·M + val e)` of every level `M`, sums) reach
every countable ordinal `x < υ_{λ+β}`, by induction on `x`:

* `x < υ_{λ+1}`: the leaf `lo x`;
* `x` decomposable: `x = y + z` with `y, z < x`, a sum node;
* `x` indecomposable, `υ_{λ+1} ≤ x`: `x` lies in a segment `[υ_{λ+h}, υ_{λ+h+1})`, `0 < h < β` (`xa_seg_ex`), so
  `x ∈ T^{υ_{λ+h}}` (`exists_next`, [W07b] Cor 5.10); if `x = υ_{λ+h}` it is the node `sg h x` (parameters below
  `υ_λ`, `pi_base`); otherwise `x = ϑ^{υ_{λ+h}}(ξ)` with `ξ ∈ T ∩ Ω₂` (`vt_rep`), `ξ = Ω₁·M + η`, and the countable
  part `η` lies in `T` and below `x` (`xa_arg`: `vt_wbar` with `se_wbar_gt` for `ξ < Ω₁`, `CitedLu.luLt_vt_self`
  for `1 ≤ M < τ`, `CitedLv.lvLevel_lt_vt` for `τ ≤ M < Ω₁`, `CitedVd.vdLevel_lt` for `Ω₁ ≤ M`, the level bound
  `M < θ` from `CitedUz.uzTBound`), so `η` has a decomposition `e` and `x` is the `ϑ`-node `th h M e`.

* `xa_seg_ex` (the segment index of a point of the range of `υ`), `xa_arg` (**the countable part of a `ϑ`-argument
  lies in `T` and below the `ϑ`-value**), `xaRep` (**every `x < υ_{λ+β}`, `x < Ω₁`, is `wwVal l E` for some
  well-formed `E`**), `xaForm_all` (**the forms clause of `Ww.WwGen` holds at every offset**, given `υ_{λ+β} ≤ Ω₁`),
  `xaGen_iff` (**`Ww.WwGen` is the UPPER clause together with `Ww.WwSup`**), `xaImg_X` (the image of the
  decomposition of the gap witness of `Ww.wwForm_X`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xa

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

/-- **The segment of a point**: every `x ≥ υ_0` lies in some `[υ_γ, υ_{γ+1})`. -/
theorem xa_seg_ex {x : Ordinal.{0}} (hx : upsilon 0 ≤ x) :
    ∃ γ, upsilon γ ≤ x ∧ x < upsilon (succ γ) := by
  have hm := upsilon_normal.strictMono
  have hex : ∃ g, x < upsilon g := ⟨succ x, (lt_succ x).trans_le hm.le_apply⟩
  obtain ⟨g0, hmem, hmin⟩ : ∃ g0, x < upsilon g0 ∧ ∀ g, g < g0 → upsilon g ≤ x :=
    ⟨sInf {g | x < upsilon g}, csInf_mem (s := {g | x < upsilon g}) hex,
      fun g hg => not_lt.1 fun h => absurd (csInf_le' (s := {g | x < upsilon g}) h) (not_le.2 hg)⟩
  rcases zero_or_succ_or_isSuccLimit g0 with h0 | ⟨d, rfl⟩ | hl
  · rw [h0] at hmem; exact absurd hx (not_le.2 hmem)
  · exact ⟨d, hmin d (lt_succ d), hmem⟩
  · obtain ⟨c, hc, hxc⟩ := (upsilon_normal.lt_iff_exists_lt hl).1 hmem
    exact absurd (hmin c hc) (not_le.2 hxc)

/-- **The countable part of a `ϑ`-argument**: for `ξ ∈ Tᵗ ∩ Ω₂`, `ξ mod Ω₁ ∈ Tᵗ` and `ξ mod Ω₁ < ϑᵗ(ξ)`. -/
theorem xa_arg (S : InaccSeq.{0}) {τ ξ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hξT : ξ ∈ Tset τ)
    (hξ2 : ξ < OmTwo) : ξ % Om1 ∈ Tset τ ∧ ξ % Om1 < vt τ ξ := by
  have hO0 : (Om1 : Ordinal.{0}) ≠ 0 := Rj.rj_Om1_inE.pos.ne'
  have hdec : Om1 * (ξ / Om1) + ξ % Om1 = ξ := div_add_mod ξ Om1
  have hηO : ξ % Om1 < Om1 := mod_lt ξ hO0
  rcases lt_or_ge ξ Om1 with hξ1 | hΩ
  · have hmod : ξ % Om1 = ξ := by
      have h0 : ξ / Om1 = 0 := (Ordinal.div_eq_zero_of_lt hξ1)
      rw [h0, mul_zero, zero_add] at hdec; exact hdec
    rw [hmod]
    refine ⟨hξT, ?_⟩
    rcases eq_or_ne ξ 0 with h0 | h0
    · have hv := (vt_memTwo hτ hτ1 hξT hξ2).2.1
      rw [h0] at hv ⊢
      exact (InE.pos hτ).trans_le hv
    · have h1 : (1 : Ordinal.{0}) ≤ ξ := Order.one_le_iff_ne_zero.2 h0
      have he : 1 + (ξ - 1) = ξ := Ordinal.add_sub_cancel_of_le h1
      have hα : ξ - 1 < Om1 := (Ordinal.sub_le_self ξ 1).trans_lt hξ1
      have hv : vt τ ξ = wbar (τ + (ξ - 1)) := by
        conv_lhs => rw [← he]
        exact vt_wbar hτ hτ1 hα
      rw [hv]
      have hτ1' : (1 : Ordinal.{0}) ≤ τ := Order.one_le_iff_pos.2 (InE.pos hτ)
      calc ξ = 1 + (ξ - 1) := he.symm
        _ ≤ τ + (ξ - 1) := add_le_add_left hτ1' _
        _ < wbar (τ + (ξ - 1)) := Se.se_wbar_gt _
  · have hτξ : τ ≤ ξ := (hτ1.trans_le hΩ).le
    have hηT : ξ % Om1 ∈ Tset τ := by
      have hd : ω ^ Om1 ∣ Om1 * (ξ / Om1) := by rw [Rj.rj_Om1_inE]; exact dvd_mul_right _ _
      have hlt : ξ % Om1 < ω ^ Om1 := by rw [Rj.rj_Om1_inE]; exact hηO
      refine Si.siT_of_comps hτ hτ1 _ fun p hp => ?_
      have hp' := Rj.rj_comps_add (Om1 * (ξ / Om1)) hd (ξ % Om1) hlt p hp
      rw [hdec] at hp'
      exact (Par_comps_eq hτ hτ1 hξT hτξ).1 p hp'
    refine ⟨hηT, ?_⟩
    set M := ξ / Om1 with hMdef
    set η := ξ % Om1 with hηdef
    have hMξ : M ≤ ξ :=
      calc M ≤ Om1 * M := Ordinal.le_mul_right M Rj.rj_Om1_inE.pos
        _ ≤ Om1 * M + η := le_self_add
        _ = ξ := hdec
    have hM1 : 1 ≤ M := by
      rw [Order.one_le_iff_ne_zero]
      intro h0
      rw [h0, mul_zero, zero_add] at hdec
      exact absurd (hdec ▸ hηO) (not_lt.2 hΩ)
    rw [← hdec]
    rcases lt_or_ge M τ with hMτ | hτM
    · exact luLt_vt_self hτ hτ1 hM1 hMτ hηT hηO
    rcases lt_or_ge M Om1 with hMΩ | hΩM
    · have h : Om1 * (Om1 * 0 + M) + η ∈ Tset τ := by rw [mul_zero, zero_add, hdec]; exact hξT
      have hMT : M ∈ Tset τ := (Rk.rkArg_T hτ hτ1 Rj.rj_Om1_inE.pos hMΩ hηO h).2
      exact (lvLevel_lt_vt hτ hτ1 hMT hτM hMΩ hηT hηO).2
    · have hall := vdArg_dat hτ hτ1 hΩM hηO (by rw [hdec]; exact hξT)
      have hξθ : ξ < ConjT.th S := uzTBound (S := S) τ hτ hτ1 ξ hξT hξ2
      have hMθ : M < ConjT.th S := hMξ.trans_lt hξθ
      have hMT : Vd.VdDatIn (· ∈ Tset τ) M := by
        by_cases hMB : M < Uc.ucB
        · exact Or.inl ⟨hMB, hall.1 hMB⟩
        · push Not at hMB
          exact Or.inr ⟨S, hMB, hMθ, hall.2 S hMB hMθ⟩
      exact (vdLevel_lt hτ hτ1 hΩM hMT hηT hηO).2

/-- **Every countable ordinal below `υ_{λ+β}` is the value of a well-formed repaired decomposition** (`0 < λ`). -/
theorem xaRep (S : InaccSeq.{0}) {l β : Ordinal.{0}} (hl0 : 0 < l) :
    ∀ x, x < upsilon (l + β) → x < Om1 → ∃ E : Ww.WwE, Ww.WwWF l β E ∧ Ww.wwVal l E = x := by
  have hm := upsilon_normal.strictMono
  have hlE : InE (upsilon l) := upsPt_inE (upsPt_upsilon hl0)
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hxβ hx1
  rcases lt_or_ge x (upsilon (succ l)) with hxl | hxl
  · exact ⟨.old (.lo x), hxl, rfl⟩
  by_cases hI : Indec x
  · obtain ⟨γ, hγx, hxγ⟩ := xa_seg_ex ((hm.monotone (zero_le : (0 : Ordinal.{0}) ≤ succ l)).trans hxl)
    have hlγ : l < γ := by
      by_contra hc
      push Not at hc
      exact absurd (hxγ.trans_le (hm.monotone (Order.succ_le_succ hc))) (not_lt.2 hxl)
    obtain ⟨h, rfl⟩ : ∃ h, l + h = γ := ⟨γ - l, Ordinal.add_sub_cancel_of_le hlγ.le⟩
    have h0 : 0 < h := pos_iff_ne_zero.2 fun e => by rw [e, add_zero] at hlγ; exact lt_irrefl l hlγ
    have hβ : h < β := (add_lt_add_iff_left l).1 (hm.lt_iff_lt.1 (hγx.trans_lt hxβ))
    have hτP : UpsPt (upsilon (l + h)) := upsPt_upsilon (hl0.trans_le le_self_add)
    have hτ1 : upsilon (l + h) < Om1 := hγx.trans_lt hx1
    have hτE : InE (upsilon (l + h)) := upsPt_inE hτP
    have hlτ : upsilon l < upsilon (l + h) := hm (lt_add_of_pos_right l h0)
    obtain ⟨m, hn, hT⟩ := exists_next hτP hτ1
    have hm2 : m = upsilon (succ (l + h)) := hn.unique (upsilon_isNext (l + h))
    have hxT : x ∈ Tset (upsilon (l + h)) := (hT x hx1).2 (hm2 ▸ hxγ)
    rcases eq_or_lt_of_le hγx with hτx | hτx
    · refine ⟨.old (.sg h x), ⟨h0, hβ, hγx, hxγ, ?_⟩, rfl⟩
      rw [← hτx]
      exact Ww.ww_par_self hlE hlτ hτE hτ1
    · obtain ⟨ξ, hξT, hξ2, hv⟩ := vt_rep hτE hτ1 hxT hγx hx1 hI
      obtain ⟨hηT, hηx⟩ := xa_arg S hτE hτ1 hξT hξ2
      rw [hv] at hηx
      have hηO : ξ % Om1 < Om1 := mod_lt ξ Rj.rj_Om1_inE.pos.ne'
      obtain ⟨e, he, hev⟩ := IH (ξ % Om1) hηx (hηx.trans hxβ) hηO
      have hdec : Om1 * (ξ / Om1) + Ww.wwVal l e = ξ := by rw [hev]; exact div_add_mod ξ Om1
      refine ⟨.th h (ξ / Om1) e, ⟨h0, hβ, he, hev ▸ hηO, ?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [hdec]; exact hξT
      · rw [hdec]; exact hξ2
      · rw [hdec, hv]; exact hγx
      · rw [hdec, hv]; exact hxγ
      · show vt (upsilon (l + h)) (Om1 * (ξ / Om1) + Ww.wwVal l e) = x
        rw [hdec, hv]
  · have hD : DecompR0 x := not_not.1 hI
    rcases hD with h0 | ⟨y, z, hy, hz, hyz⟩
    · rw [h0] at hxl
      exact absurd hxl (not_le.2 (zero_le.trans_lt (hm (lt_succ l))))
    obtain ⟨Ey, hEy, hvy⟩ := IH y hy (hy.trans hxβ) (hy.trans hx1)
    obtain ⟨Ez, hEz, hvz⟩ := IH z hz (hz.trans hxβ) (hz.trans hx1)
    refine ⟨.add Ey Ez, ⟨hEy, hEz⟩, ?_⟩
    show Ww.wwVal l Ey + Ww.wwVal l Ez = x
    rw [hvy, hvz, hyz]

/-- **The forms clause holds at every offset**: if `0 < λ` and `υ_{λ+β} ≤ Ω₁`, every inner reach is big or the
value of a repaired decomposition. -/
theorem xaForm_all (S : InaccSeq.{0}) {l β : Ordinal.{0}} (hl0 : 0 < l) (hβ1 : upsilon (l + β) ≤ Om1)
    (g : Ordinal.{0}) : upsilon (l + β) ≤ cdR S (l + g) ∨ Ww.WwForm S l β g := by
  rcases le_or_gt (upsilon (l + β)) (cdR S (l + g)) with h | h
  · exact Or.inl h
  · obtain ⟨E, hE, hv⟩ := xaRep S hl0 _ h (h.trans_le hβ1)
    exact Or.inr ⟨E, hE, hv⟩

/-- **`Ww.WwGen` is the UPPER clause together with `Ww.WwSup`** (the forms clause is a theorem). -/
theorem xaGen_iff (S : InaccSeq.{0}) {l β : Ordinal.{0}} (hl0 : 0 < l) (hβ1 : upsilon (l + β) ≤ Om1) :
    Ww.WwGen S l β ↔ (∀ g, 0 < g → g < β → ω ^ 2 ∣ g → CdUpper S (l + g)) ∧ Ww.WwSup S l β :=
  ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, fun g _ _ _ => xaForm_all S hl0 hβ1 g, h.2⟩⟩

/-- **The image of the decomposition of the gap witness** (`Ww.wwForm_X`): under `(μ, f)` with `υ_μ < υ_λ`
(`Bases`), `sg h τ + th 1 B₂ (lo λ)` (`λ = υ_λ`) goes to `mv τ υ_{μ+f(h)} τ + ϑ^{υ_{μ+f(1)}}(Ω₁·B₂ + υ_μ)`. -/
theorem xaImg_X {l μ h τ : Ordinal.{0}} (f : Ordinal.{0} → Ordinal.{0}) (hb : Bases (upsilon μ) (upsilon l))
    (hl : upsilon l = l) :
    Ww.wwImg l μ f (.add (.old (.sg h τ)) (.th 1 Uc.ucB (.old (.lo l)))) =
      mv (upsilon (l + h)) (upsilon (μ + f h)) τ + vt (upsilon (μ + f 1)) (Om1 * Uc.ucB + upsilon μ) := by
  show mv (upsilon (l + h)) (upsilon (μ + f h)) τ +
      vt (upsilon (μ + f 1)) (Om1 * Uc.ucB + pi (upsilon μ) (upsilon l) l) = _
  have hp : pi (upsilon μ) (upsilon l) l = upsilon μ := by
    have h' := (pi_base hb).2
    rw [hl] at h' ⊢
    exact h'
  rw [hp]

end Googology.Trans.PoR.InaccPsi.R2.Xa

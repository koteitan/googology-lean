import Googology.Trans.PoR.InaccPsi.R2.ZbDir

/-!
# ZbUn: THE UNION STEP WITH ANY TOP CODE AND ANY ATOM SYSTEM, CONTINUITY OF `ν ↦ ϑˣ(Ω₁·Ω₁ + ν)` PAST A FIXED POINT

* `zb_lt_lim_iff` (**`v < ϑˣ(Ω₁·Ω₁ + λ)` iff `v < ϑˣ(Ω₁·Ω₁ + ν)` for some `ν < λ`**, for every limit `λ ∈ Tˣ ∩ Ω₁`
  with some `σ < λ`, `λ < ϑˣ(Ω₁·Ω₁ + σ)`: the proof of `Yr.yr_lt_lim_iff`, whose hypothesis `Yr.YrN x λ` (no limit
  `≤ λ` closed) fails for every `λ ≥ D(x) = ϑˣ(Ω₁·Ω₁ + Ω₁)`, e.g. `λ = D(x) + ω`);
* `zbUnion_codes` (**THE UNION READS THE TARGET CODE**: a union step `Yw.YwUF` whose members read codes `C_i ≤ T_c`
  with the atoms of `A`, with terms below them, and every code below `T_c` over a base `Z` above the gate lies below
  some `C_i` with side gate below `Z`: the union top reads `T_c`, with terms below it);
* `zbCover` (**a code over `Z ≤ Ω₁` with the atoms of `zbU` below `Γ_{Ω₁+1+c_L}`, `c_L` a limit, is below some
  `Γ_{Ω₁+1+b}`, `b < c_L`**: every atom of `zbU` is some `Γ_{Ω₁+1+b}`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gm
  Googology.Trans.PoR.InaccPsi.R2.Xx Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Lp

/-- **`v < ϑˣ(Ω₁·Ω₁ + λ)` iff `v < ϑˣ(Ω₁·Ω₁ + ν)` for some `ν < λ`** for every limit `λ ∈ Tˣ ∩ Ω₁` that is not a
fixed point of `ν ↦ ϑˣ(Ω₁·Ω₁ + ν)` from below (the hypothesis of `Yr.yr_lt_lim_iff` asked only at `λ` itself). -/
theorem zb_lt_lim_iff {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {l : Ordinal.{0}} (hl : IsSuccLimit l)
    (hlT : l ∈ Tset x) (hl1 : l < Om1) (hσl : ∃ σ, σ < l ∧ l < gq σ x) :
    ∀ v, v < gq l x → ∃ ν < l, v < gq ν x := by
  obtain ⟨hGT, -, hG1, -, -⟩ := geq_facts hx hx1 hlT hl1
  have hdown : ∀ ν, ν ≤ l → ν ∈ Tset x ∧ ν < Om1 := fun ν hν => ⟨vz_T_down hx hx1 hlT hl1 hν, hν.trans_lt hl1⟩
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  rcases le_or_gt v (max x l) with hvx | hxv0
  · rcases le_or_gt v x with hvx' | hxv'
    · exact ⟨0, hl.bot_lt, hvx'.trans_lt (gfq0_facts hx hx1).2.1⟩
    · have hvl : v ≤ l := by
        rcases le_max_iff.1 hvx with h | h
        · exact absurd h (not_le.2 hxv')
        · exact h
      obtain ⟨σ, hσl, hlσ⟩ := hσl
      exact ⟨σ, hσl, hvl.trans_lt hlσ⟩
  have hxv : x < v := (le_max_left _ _).trans_lt hxv0
  have hlv : l < v := (le_max_right _ _).trans_lt hxv0
  have hv1 : v < Om1 := hv.trans hG1
  have hvT : v ∈ Tset x := vz_T_down hx hx1 hGT hG1 hv.le
  by_cases hI : Indec v
  · by_cases hvE' : InE v
    · obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hx hx1 hvT hxv.le hv1 hI
      have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξv]; exact hxv, by rw [hξv]; exact hvE'⟩
      have hξk : ξ < Om1 * Om1 + l :=
        lgLt_of_vt_lt hx hx1 hξT hξ2 hlT hl1 (by rw [hξv]; exact hlv) (by rw [hξv]; exact hv)
      rcases lt_or_ge ξ (Om1 * Om1) with hξs | hξs
      · obtain ⟨hq1, hrT, hr1, hdec⟩ := lu_split hx hx1 hξT hξ2 hΩξ
        have hqT : ξ / Om1 ∈ Tset x := lgQuot_mem hx hx1 hξT hξs
        have hqΩ : ξ / Om1 < Om1 := (Ordinal.lt_mul_iff_div_lt (Ordinal.omega_pos 1).ne').1 hξs
        have hqr : ξ / Om1 < v ∧ ξ % Om1 < v := by
          rcases lt_or_ge (ξ / Om1) x with hqx | hxq
          · have h := luLt_vt_self hx hx1 hq1 hqx hrT hr1
            rw [hdec, hξv] at h
            exact ⟨hqx.trans hxv, h⟩
          · have h := lvLevel_lt_vt hx hx1 hqT hxq hqΩ hrT hr1
            rw [hdec, hξv] at h
            exact h
        obtain ⟨n1, hn1l, hn1⟩ := IH _ hqr.1 (hqr.1.trans hv)
        obtain ⟨n2, hn2l, hn2⟩ := IH _ hqr.2 (hqr.2.trans hv)
        have hml : max n1 n2 < l := max_lt hn1l hn2l
        obtain ⟨hmT, hm1⟩ := hdown _ hml.le
        refine ⟨max n1 n2, hml, ?_⟩
        have hq' : ξ / Om1 < gq (max n1 n2) x :=
          hn1.trans_le (gmq_mono hx hx1 hmT hm1 (le_max_left _ _))
        have hr' : ξ % Om1 < gq (max n1 n2) x :=
          hn2.trans_le (gmq_mono hx hx1 hmT hm1 (le_max_right _ _))
        have h := lgVt_lt_low hx hx1 hqT hqΩ hrT hr1 hmT hm1 hq' hr'
        rw [hdec, hξv] at h
        exact h
      · have hje : Om1 * Om1 + (ξ - Om1 * Om1) = ξ := Ordinal.add_sub_cancel_of_le hξs
        obtain ⟨j, hj⟩ : ∃ j, ξ - Om1 * Om1 = j := ⟨_, rfl⟩
        rw [hj] at hje
        have hjk : j < l := (add_lt_add_iff_left _).1 (by rw [hje]; exact hξk)
        refine ⟨j + 1, hl.add_one_lt hjk, ?_⟩
        have hvj : v = gq j x := by rw [← hξv, ← hje]; rfl
        obtain ⟨hj1T, hj11⟩ := hdown _ (hl.add_one_lt hjk).le
        rw [hvj]
        exact gmq_lt hx hx1 hj1T hj11 (lt_add_one _)
    · obtain ⟨L, rfl⟩ := indec_eq_opow hI
      have hL : L < ω ^ L := lt_of_le_of_ne (right_le_opow _ one_lt_omega0)
        (fun h => hvE' (by unfold InE; rw [← h]; exact h.symm))
      obtain ⟨n, hnl, hn⟩ := IH L hL (hL.trans hv)
      obtain ⟨hnT, hn1⟩ := hdown _ hnl.le
      exact ⟨n, hnl, (geq_facts hx hx1 hnT hn1).2.2.2.1.opow_lt hn⟩
  · have hD : DecompR0 v := not_not.1 hI
    rcases hD with h0 | ⟨u1, u2, hu1, hu2, hsum⟩
    · exact absurd h0 (lt_of_le_of_lt zero_le hxv).ne'
    obtain ⟨n1, hn1l, h1⟩ := IH u1 hu1 (hu1.trans hv)
    obtain ⟨n2, hn2l, h2⟩ := IH u2 hu2 (hu2.trans hv)
    have hml : max n1 n2 < l := max_lt hn1l hn2l
    obtain ⟨hmT, hm1⟩ := hdown _ hml.le
    refine ⟨max n1 n2, hml, ?_⟩
    rw [← hsum]
    exact (inE_indec (geq_facts hx hx1 hmT hm1).2.2.2.1).add_lt
      (h1.trans_le (gmq_mono hx hx1 hmT hm1 (le_max_left _ _)))
      (h2.trans_le (gmq_mono hx hx1 hmT hm1 (le_max_right _ _)))


/-- **THE UNION READS THE TARGET CODE** (any atom system, any target top). -/
theorem zbUnion_codes {A : ZbAS} {g : Ordinal.{0}} (F : YwUF g) (C : F.I → Ordinal.{0}) {Tc : Ordinal.{0}}
    (hK : ∀ i y, SC y → y < Om 1 → F.gi i < y → (F.K i).K.E y = gxTh y (A.At y) (C i))
    (hKP : ∀ i, ZbPolyG A (F.K i).K.sys (C i)) (hCle : ∀ i, C i ≤ Tc)
    (hcov : ∀ Z, SC Z → Z < Om 1 → g < Z → ∀ d, GxCl Z (A.At Z) d → d < Tc → ∃ i, F.gi i < Z ∧ d < C i) :
    (∀ y, SC y → y < Om 1 → g < y → (ywLimB F).K.E y = gxTh y (A.At y) Tc) ∧
      ZbPolyG A (ywLimB F).K.sys Tc := by
  refine ⟨fun y hy hy1 hg => ?_, ?_⟩
  · have hyE := gg_SC_eps hy
    have hy1' := lp_y1 hy1
    rw [ywLimB_E]
    refine le_antisymm (le_of_forall_lt fun v hv => ?_) (gxTh_le_of fun d hd hdT => ?_)
    · obtain ⟨i, hi, hvi⟩ := F.cof y hyE hy1' hg v hv
      calc v < (F.K i).K.E y := hvi
        _ = gxTh y (A.At y) (C i) := hK i y hy hy1 hi
        _ ≤ gxTh y (A.At y) Tc := gxTh_mono (hCle i)
    · obtain ⟨i, hi, hdi⟩ := hcov y hy hy1 hg d hd hdT
      calc gxTh y (A.At y) d < gxTh y (A.At y) (C i) := gxTh_lt hd hdi
        _ = (F.K i).K.E y := (hK i y hy hy1 hi).symm
        _ < F.T y := F.E_lt i y hyE hy1' hg hi
  · refine zbPolyG_of_SC A _ fun Z hZ hZ1 hgZ d hd hdT => ?_
    obtain ⟨i, hi, hdi⟩ := hcov Z hZ hZ1 hgZ d hd hdT
    obtain ⟨t, ht⟩ := hKP i Z d ((F.g_le i).trans_lt hi) hd hdi
    exact ⟨⟨i, t⟩, fun y hy hy1 hZy => ⟨⟨hi.trans_le hZy, (ht y hy hy1 hZy).1⟩, (ht y hy hy1 hZy).2⟩⟩

/-- **Every atom of `zbU` is some `Γ_{Ω₁+1+b}`.** -/
theorem zbU_atom_gcG {Z s : Ordinal.{0}} (hs : s ∈ zbU.At Z) : ∃ b, gcG b = s :=
  enumOrd_surjective gcSet_unbdd (zbU.gxAt Z s hs)

/-- **A code with the atoms of `zbU` below `Γ_{Ω₁+1+c_L}` (`c_L` a limit) is below some `Γ_{Ω₁+1+b}`, `b < c_L`.** -/
theorem zbCover {Z : Ordinal.{0}} (hZ1 : Z ≤ Om 1) {cL : Ordinal.{0}} (hcL : IsSuccLimit cL) :
    ∀ d, GxCl Z (zbU.At Z) d → d < gcG cL → ∃ b < cL, d < gcG b := by
  intro d hd
  induction hd with
  | small h => exact fun _ => ⟨0, hcL.bot_lt, (h.trans_le hZ1).trans (gcG_Om1_lt 0)⟩
  | om => exact fun _ => ⟨0, hcL.bot_lt, gcG_Om1_lt 0⟩
  | @atom s hs =>
    intro h
    obtain ⟨b, rfl⟩ := zbU_atom_gcG hs
    exact ⟨b + 1, hcL.add_one_lt (gcG_lt_iff.1 h), gcG_lt (lt_add_one b)⟩
  | @add a b _ _ iha ihb =>
    intro h
    obtain ⟨b1, h1, e1⟩ := iha (lt_of_le_of_lt le_self_add h)
    obtain ⟨b2, h2, e2⟩ := ihb (lt_of_le_of_lt le_add_self h)
    exact ⟨max b1 b2, max_lt h1 h2, (gcG_SC _).isPrincipal (e1.trans_le (gcG_le (le_max_left _ _)))
      (e2.trans_le (gcG_le (le_max_right _ _)))⟩
  | @phi a b _ _ iha ihb =>
    intro h
    obtain ⟨b1, h1, e1⟩ := iha (lt_of_le_of_lt (left_le_veblen a b) h)
    obtain ⟨b2, h2, e2⟩ := ihb (lt_of_le_of_lt (right_le_veblen a b) h)
    exact ⟨max b1 b2, max_lt h1 h2, (gcG_SC _).2 _ (e1.trans_le (gcG_le (le_max_left _ _))) _
      (e2.trans_le (gcG_le (le_max_right _ _)))⟩

end Googology.Trans.PoR.InaccPsi.R2.Zb

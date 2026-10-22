import Googology.Trans.PoR.InaccPsi.R2.GaTow
import Googology.Trans.PoR.InaccPsi.R2.LqLh

/-!
# The limit of the tower of bases: the layer with top `ϑˣ(Ω₁·Ω₁ + ω) = Γ_{x+ω}`

The tower `lpTK k` (`R2.LpTow`, tops `gk (k+1) x = ϑˣ(Ω₁·Ω₁ + k + 1)`) has as union one term system `gbUSys` with
top `gbW x = ϑˣ(Ω₁·Ω₁ + ω)`, and it is again a layer (`R2.XtLay`) with an `ε`-number top in `Tˣ`, so it is a new
base package `gbWB` for the generic ladder of `R2.LpTm` … `R2.LpFam`.

The witness pair of the new top separates `Γ_{x+ω}` from every `Γ_{x+1+k}` by its exact `R₁⁺`-reach:

* `gbW_lh` (**`lh(gbW x) = G·G + G + 1`**, `G = gbW x`: `Lq.lq_lh_sq` at `η = ω`, `ζ = logend(ω) = 1`), `gk_lh`
  (**`lh(gk k x) = G·G + G`**: `ζ = logend(k) = 0`);
* `gb_not_le1R` (**no `ε`-number `a ∈ (x, gbW x)` has `a ≤₁ a·a + a + 1`**: `a = ϑˣ(ξ)` with `Ω₁ ≤ ξ < Ω₁·Ω₁ + ω`;
  below `Ω₁·Ω₁` the reach is `< a·a`, at `Ω₁·Ω₁ + j` it is `a·a + a`);
* `gb_lt_W_iff`, `gbW_sup` (**`gbW x = sup_k gk k x`**), `gk_lt_W`, `gbW_pi` (EXACT), `gbW_lt_next`;
* `GbK.gbTopWit` (**the witness pair of the top**: `f(G) ∈ E`, and `gbW(fρ) ≤ f(G)` from `f(G) ≤₁ f(G)·f(G) + f(G) + 1`
  (the copy of `G ≤₁ G·G + G + 1`) and `gb_not_le1R`);
* `gbUSys`, `gbWL : XtLay`, `gbWB : LpB`; `gb_topIn` (the tops of the tower are terms), `gb_tow_lt`
  (**`Λ⁺(lpTK k) < Λ⁺(gbUSys)`**), `gb_tow_eq` (`O_{gbUSys} = O_{lpTK k}` below `Λ⁺(lpTK k)`), `gb_towSup_lt`
  (**`ι(Γ_{Ω₁+ω}) = sup_k Λ⁺(lpTK k) < Λ⁺(gbUSys)`**).

The value `lhᵗ(α·α)` that the separation needs is already a theorem of the repo (`Lq.lq_lh_sq`, from `lqLhT` of
`R2.CitedLq` with [W07b] Theorem 2.2 and Theorem 5.3 through `le1R_thm22` and `lh_eq_lhT`), so no new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Lp Lu
  Googology.Trans.PoR.InaccPsi.R2.Bt

/-- **`gbW x = ϑˣ(Ω₁·Ω₁ + ω)`** (`= Γ_{x+ω}`). -/
noncomputable def gbW (x : Ordinal.{0}) : Ordinal.{0} := vt x (Om1 * Om1 + ω)

section W

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem gb_omega : (ω : Ordinal.{0}) ∈ Tset x ∧ (ω : Ordinal.{0}) < Om1 ∧ (ω : Ordinal.{0}) < x :=
  ⟨mem_T_of_le hx hx1 (omega0_lt_inE hx).le, (omega0_lt_inE hx).trans hx1, omega0_lt_inE hx⟩

theorem gb_arg : Om1 * Om1 + ω ∈ Tset x ∧ Om1 * Om1 + ω < OmTwo := by
  obtain ⟨hT, h1, -⟩ := gb_omega hx hx1
  exact ⟨lgArg_mem hx hx1 hT h1, lg_OmOm_lt h1⟩

/-- The facts on `gbW x`. -/
theorem gbW_facts : gbW x ∈ Tset x ∧ x < gbW x ∧ gbW x < Om1 ∧ InE (gbW x) ∧ Indec (gbW x) := by
  obtain ⟨hT, h2⟩ := gb_arg hx hx1
  obtain ⟨hvT, -, hv1, hvP, -⟩ := vt_memTwo hx hx1 hT h2
  have hE := (vt_E_iff hx hx1 hT h2).2 (lg_Om1_le_OmOm.trans le_self_add)
  exact ⟨hvT, hE.1, hv1, hE.2, hvP⟩

/-- **`gk k x < gbW x`.** -/
theorem gk_lt_W (k : ℕ) : gk k x < gbW x := by
  have h1T : (1 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 (lu_one_lt_E hx).le
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  have h1Ω : (1 : Ordinal.{0}) < Om1 := (lu_one_lt_E hx).trans hx1
  have h0Ω : (0 : Ordinal.{0}) < Om1 := hx.pos.trans hx1
  obtain ⟨hjT, hj1, hjx⟩ := gk_nat hx hx1 k
  obtain ⟨hwT, hw1, -⟩ := gb_omega hx hx1
  obtain ⟨-, hxv, -, -, -⟩ := gbW_facts hx hx1
  have e1 : ∀ z, Om1 * (Om1 * 1 + 0) + z = Om1 * Om1 + z := fun z => by rw [mul_one, add_zero]
  have := lqVt_lt hx hx1 h1T h1Ω h0T h0Ω hjT hj1 le_rfl h1T h1Ω h0T h0Ω hwT hw1
    (by rw [e1, e1]; exact (add_lt_add_iff_left _).2 (natCast_lt_omega0 k))
    (by rw [e1]; exact (lu_one_lt_E hx).trans hxv) (by rw [e1]; exact hx.pos.trans hxv)
    (by rw [e1]; exact hjx.trans hxv)
  rw [e1, e1] at this
  exact this

/-- `gbW x` lies below every next point above the base. -/
theorem gbW_lt_next {u : Ordinal.{0}} (hxu : x < u) (hu : LtInf1 u) : gbW x < u := by
  obtain ⟨m, -, -, hmin, hTm, -⟩ := T_next (Or.inr hx) hx1
  obtain ⟨hT, -, h1, -, -⟩ := gbW_facts hx hx1
  exact ((hTm _ h1).1 hT).trans_le (hmin u hxu hu)

/-- **`v < ϑˣ(Ω₁·Ω₁ + ω)` iff `v < ϑˣ(Ω₁·Ω₁ + k)` for some `k < ω`.** -/
theorem gb_lt_W_iff : ∀ v, v < gbW x → ∃ k : ℕ, v < gk k x := by
  obtain ⟨hGT, -, hG1, -, -⟩ := gbW_facts hx hx1
  obtain ⟨hwT, hw1, hwx⟩ := gb_omega hx hx1
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  rcases le_or_gt v x with hvx | hxv
  · exact ⟨0, hvx.trans_lt (gk_facts hx hx1 0).2.1⟩
  have hv1 : v < Om1 := hv.trans hG1
  have hvT : v ∈ Tset x := vz_T_down hx hx1 hGT hG1 hv.le
  by_cases hI : Indec v
  · by_cases hvE' : InE v
    · obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hx hx1 hvT hxv.le hv1 hI
      have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξv]; exact hxv, by rw [hξv]; exact hvE'⟩
      have hξk : ξ < Om1 * Om1 + ω :=
        lgLt_of_vt_lt hx hx1 hξT hξ2 hwT hw1 (by rw [hξv]; exact hwx.trans hxv) (by rw [hξv]; exact hv)
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
        obtain ⟨n1, hn1⟩ := IH _ hqr.1 (hqr.1.trans hv)
        obtain ⟨n2, hn2⟩ := IH _ hqr.2 (hqr.2.trans hv)
        refine ⟨max n1 n2, ?_⟩
        have hq' : ξ / Om1 < gk (max n1 n2) x := hn1.trans_le (gk_mono hx hx1 (le_max_left _ _))
        have hr' : ξ % Om1 < gk (max n1 n2) x := hn2.trans_le (gk_mono hx hx1 (le_max_right _ _))
        obtain ⟨hmT, hm1, -⟩ := gk_nat hx hx1 (max n1 n2)
        have h := lgVt_lt_low hx hx1 hqT hqΩ hrT hr1 hmT hm1 hq' hr'
        rw [hdec, hξv] at h
        exact h
      · have hje : Om1 * Om1 + (ξ - Om1 * Om1) = ξ := Ordinal.add_sub_cancel_of_le hξs
        have hjk : ξ - Om1 * Om1 < ω := (add_lt_add_iff_left _).1 (by rw [hje]; exact hξk)
        obtain ⟨j, hj⟩ := lt_omega0.1 hjk
        refine ⟨j + 1, ?_⟩
        have hvj : v = gk j x := by rw [← hξv, ← hje, hj]; rfl
        rw [hvj]
        exact gk_lt hx hx1 (Nat.lt_succ_self j)
    · obtain ⟨L, rfl⟩ := indec_eq_opow hI
      have hL : L < ω ^ L := lt_of_le_of_ne (right_le_opow _ one_lt_omega0)
        (fun h => hvE' (by unfold InE; rw [← h]; exact h.symm))
      obtain ⟨n, hn⟩ := IH L hL (hL.trans hv)
      exact ⟨n, (gk_facts hx hx1 n).2.2.2.1.opow_lt hn⟩
  · have hD : DecompR0 v := not_not.1 hI
    rcases hD with h0 | ⟨u1, u2, hu1, hu2, hsum⟩
    · exact absurd h0 (lt_of_le_of_lt zero_le hxv).ne'
    obtain ⟨n1, h1⟩ := IH u1 hu1 (hu1.trans hv)
    obtain ⟨n2, h2⟩ := IH u2 hu2 (hu2.trans hv)
    refine ⟨max n1 n2, ?_⟩
    rw [← hsum]
    exact (inE_indec (gk_facts hx hx1 _).2.2.2.1).add_lt (h1.trans_le (gk_mono hx hx1 (le_max_left _ _)))
      (h2.trans_le (gk_mono hx hx1 (le_max_right _ _)))

/-- **`ϑˣ(Ω₁·Ω₁ + ω) = sup_k ϑˣ(Ω₁·Ω₁ + k)`.** -/
theorem gbW_sup : gbW x = ⨆ k : ℕ, gk k x := by
  apply le_antisymm
  · by_contra hlt
    push Not at hlt
    obtain ⟨k, hk⟩ := gb_lt_W_iff hx hx1 _ hlt
    exact absurd (Ordinal.le_iSup (fun k : ℕ => gk k x) k) (not_le.2 hk)
  · exact Ordinal.iSup_le fun k => (gk_lt_W hx hx1 k).le

/-- `ζ^x = logend(ω) = 1` at `ϑˣ(Ω₁·Ω₁ + ω)`. -/
theorem gbW_zeta : lqZeta x (Om1 * Om1) ω = 1 := by
  have h0 := (gk_facts hx hx1 0).2.1
  unfold gk at h0
  rw [Nat.cast_zero] at h0
  unfold lqZeta
  rw [if_pos ⟨0, omega0_pos, (omega0_lt_inE hx).trans h0⟩, lg_omega]

/-- **`lh(gbW x) = G·G + G + 1`** in `R₁⁺` (`G = gbW x`). -/
theorem gbW_lh : IsLh1 (gbW x) (gbW x * gbW x + gbW x + 1) := by
  obtain ⟨hwT, hw1, -⟩ := gb_omega hx hx1
  have h := (Lq.lq_lh_sq hx hx1 hwT hw1).1
  rw [gbW_zeta hx hx1] at h
  exact h

/-- **`lh(gk k x) = G·G + G`** in `R₁⁺` (`G = gk k x`). -/
theorem gk_lh (k : ℕ) : IsLh1 (gk k x) (gk k x * gk k x + gk k x) := by
  obtain ⟨hkT, hk1, -⟩ := gk_nat hx hx1 k
  have h := (Lq.lq_lh_sq hx hx1 hkT hk1).1
  have hz : lqZeta x (Om1 * Om1) (k : Ordinal.{0}) = 0 := by
    unfold lqZeta
    split_ifs with hc
    · rcases eq_or_ne k 0 with rfl | hk0
      · obtain ⟨σ, hσ, -⟩ := hc
        rw [Nat.cast_zero] at hσ
        exact absurd hσ (not_lt.2 zero_le)
      · exact lg_nat hk0
    · rfl
  rw [hz, add_zero] at h
  exact h

/-- **No `ε`-number `a ∈ (x, ϑˣ(Ω₁·Ω₁ + ω))` has `a ≤₁ a·a + a + 1` in `R₁⁺`.** -/
theorem gb_not_le1R {a : Ordinal.{0}} (haE : InE a) (hxa : x < a) (haW : a < gbW x) :
    ¬ le1R a (a * a + a + 1) := by
  intro hR
  obtain ⟨hGT, -, hG1, -, -⟩ := gbW_facts hx hx1
  obtain ⟨hwT, hw1, hwx⟩ := gb_omega hx hx1
  have ha1 : a < Om1 := haW.trans hG1
  have haT : a ∈ Tset x := vz_T_down hx hx1 hGT hG1 haW.le
  obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hx hx1 haT hxa.le ha1 (inE_indec haE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξv]; exact hxa, by rw [hξv]; exact haE⟩
  have hξk : ξ < Om1 * Om1 + ω :=
    lgLt_of_vt_lt hx hx1 hξT hξ2 hwT hw1 (by rw [hξv]; exact hwx.trans hxa) (by rw [hξv]; exact haW)
  have haa : a * a ≤ a * a + a + 1 := le_self_add.trans le_self_add
  rcases lt_or_ge ξ (Om1 * Om1) with hξs | hξs
  · obtain ⟨hq1, hrT, hr1, hdec⟩ := lu_split hx hx1 hξT hξ2 hΩξ
    have hqT : ξ / Om1 ∈ Tset x := lgQuot_mem hx hx1 hξT hξs
    have hqΩ : ξ / Om1 < Om1 := (Ordinal.lt_mul_iff_div_lt (Ordinal.omega_pos 1).ne').1 hξs
    set q := ξ / Om1 with hq
    set r := ξ % Om1 with hr
    have hv : vt x (Om1 * q + r) = a := by rw [hdec, hξv]
    have hζr : luZeta x q r < a := by
      refine lu_zeta_le.trans_lt ?_
      rcases lt_or_ge q x with hqx | hxq
      · have := (lu_th_facts hx hx1 hq1 hqx hrT hr1).2.2.2.2.2.2.2
        rwa [hv] at this
      · have := (Lv.gen_facts hx hx1 hqT hxq hqΩ hrT hr1).2.2.2.2.2.2.2.2
        rwa [hv] at this
    have hL : IsLh1 a (luL a q + luZeta x q r) ∧ q < a := by
      rcases lt_or_ge q x with hqx | hxq
      · have h := lu_lh_th hx hx1 hq1 hqx hrT hr1
        rw [hv] at h
        exact ⟨h, hqx.trans hxa⟩
      · have h := Lv.lv_lh_gen hx hx1 hqT hxq hqΩ hrT hr1
        have hqv := (Lv.gen_facts hx hx1 hqT hxq hqΩ hrT hr1).2.2.2.2.2.2.2.1
        rw [hv] at h hqv
        exact ⟨h, hqv⟩
    have hle := hL.1.2 _ hR
    exact absurd ((haa.trans hle).trans_lt (lg_luL_lt_sq haE hL.2 hζr)) (lt_irrefl _)
  · have hje : Om1 * Om1 + (ξ - Om1 * Om1) = ξ := Ordinal.add_sub_cancel_of_le hξs
    have hjk : ξ - Om1 * Om1 < ω := (add_lt_add_iff_left _).1 (by rw [hje]; exact hξk)
    obtain ⟨j, hj⟩ := lt_omega0.1 hjk
    have hvj : a = gk j x := by rw [← hξv, ← hje, hj]; rfl
    have hL := gk_lh hx hx1 j
    rw [← hvj] at hL
    exact absurd (hL.2 _ hR) (not_le.2 (lt_add_one _))

end W

/-- **Lemma EXACT for `gbW`**: `π_{σ,ρ}(ϑ^ρ(Ω₁·Ω₁ + ω)) = ϑ^σ(Ω₁·Ω₁ + ω)`. -/
theorem gbW_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) : gbW ρ ∈ TB ρ σ ∧ pi σ ρ (gbW ρ) = gbW σ := by
  obtain ⟨hσE, hρE, hσρ, hρ1⟩ := hB
  have hB' : Bases σ ρ := ⟨hσE, hρE, hσρ, hρ1⟩
  obtain ⟨hTB0, hpi0⟩ := lgPi_OmOm hB'
  have hwσ : (ω : Ordinal.{0}) < σ := omega0_lt_inE hσE
  obtain ⟨hTBs, hpis⟩ := pi_add hB' hTB0 (mem_TB_of_lt hB' hwσ)
  rw [hpi0, pi_lt hB' hwσ] at hpis
  have h2 := (gb_arg hρE hρ1).2
  obtain ⟨hvT, -, -, -, hPar⟩ := vt_memTwo hρE hρ1 hTBs.1 h2
  refine ⟨⟨hvT, ?_⟩, ?_⟩
  · show ↑(Par ρ (vt ρ (Om1 * Om1 + ω))) ⊆ Set.Iio σ
    rw [hPar]; exact hTBs.2
  · show pi σ ρ (vt ρ (Om1 * Om1 + ω)) = vt σ (Om1 * Om1 + ω)
    rw [pi_vt_two hB' hTBs h2, hpis]

theorem gbW_lt_next_ups {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) :
    gbW (upsilon l) < upsilon (l + ω + 1) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have h1 : l < l + ω := lt_add_of_pos_right l omega0_pos
  have hτU := upsPt_upsilon (hl0.trans h1)
  exact (gbW_lt_next (ups_inE hl) (ups_lt_Om1 l hl1) (upsilon_normal.strictMono h1) hτU.2).trans
    (upsilon_normal.strictMono (lt_add_one _))

namespace GbK

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

theorem gbW_lt_δ : gbW ρ < δ := (gbW_lt_next (upsPt_inE h.ρU) h.ρ1 h.ρτ h.τU.2).trans h.τδ

/-- **The image of an `ε`-number `G ∈ (ρ, δ)`**: `f(G) ∈ E` and `f(G)·f(G) ≤ f(G·G)`. -/
theorem gbImg {G : Ordinal.{0}} (hGE : InE G) (hρG : ρ < G) (hGδ : G < δ)
    {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (C : ImgCtx ρ A f)
    (hGA : G ∈ A) (hGGA : G + G ∈ A) (hPA : G * G ∈ A) (hPGA : G * G + G ∈ A) :
    InE (f G) ∧ f G * f G ≤ f (G * G) := by
  have hPδ : G * G < δ := h.δE.mul_lt hGδ hGδ
  have hPGδ : G * G + G < δ := (inE_indec h.δE).add_lt hPδ hGδ
  have hfE : InE (f G) := LuK.luFE h C hGE hρG.le hGδ hGA hGGA
  refine ⟨hfE, ?_⟩
  have hGP : G < G * G := lt_mul_of_one_lt_right hGE.pos (lu_one_lt_E hGE)
  have hfGP : f G < f (G * G) := C.mono hGA hPA hGP
  by_cases hUP : UpsPt (f (G * G))
  · exact ((upsPt_inE hUP).mul_lt hfGP hfGP).le
  have hPe : G * G = ω ^ (G + G) := by
    conv_lhs => rw [← show ω ^ G = G from hGE]
    rw [← opow_add]
  have hc0 : G + G ≠ 0 := (lt_of_lt_of_le hGE.pos le_self_add).ne'
  have hclt : G + G < ω ^ (G + G) := by
    rw [← hPe, ← mul_two_eq G]
    have h2ω : (2 : Ordinal.{0}) < ω := by simpa using natCast_lt_omega0 2
    exact (mul_lt_mul_iff_right₀ hGE.pos).2 (h2ω.trans_le (lu_omega_lt_E hGE).le)
  have hGlg : G ≤ lg (G + G) := le_lg hc0 ⟨2, by rw [show ω ^ G = G from hGE]; exact (mul_two_eq G).symm⟩
  have hLP := lu_lh_opow hc0 hclt
  have hsrcR : le1R (G * G) (G * G + G) := by
    rw [hPe]
    exact le1R_of_le le_self_add ((add_le_add_iff_left _).2 hGlg) hLP.1
  have hρP : ρ < G * G := hρG.trans hGP
  have hsrc2 : le1 (G * G) (G * G + G) := (h.lowδ _ _ hρP hPGδ.le).2 hsrcR
  have himg : le1 (f (G * G)) (f (G * G) + f G) := by
    have := C.cov1 (G * G) hPA _ hPGA hsrc2
    rwa [← C.add (G * G) hPA G hGA _ hPGA rfl] at this
  have hR2 := (C.sk _ (C.low _ hPA) hUP _).1 himg
  obtain ⟨d, hd⟩ := indec_eq_opow (C.indec (G * G) hPA (by rw [hPe]; exact indec_opow _))
  rw [hd] at hR2 hfGP ⊢
  exact LgK.lg_sq_le_of_reach hfE hfGP hR2

/-- **The witness pair of the top `gbW`**: `f(gbW ρ) ∈ E` and `gbW(fρ) ≤ f(gbW ρ)`. -/
theorem gbTopWit : ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ gbW ρ ∈ W ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      (∃ e', f (gbW ρ) = ω ^ e' ∧ ω ^ f ρ ∣ e') ∧ gbW (f ρ) ≤ f (gbW ρ) := by
  classical
  have hρE := upsPt_inE h.ρU
  obtain ⟨-, hρG, -, hGE, hGI⟩ := gbW_facts hρE h.ρ1
  have hLG := gbW_lh hρE h.ρ1
  set G := gbW ρ with hG
  have hGδ : G < δ := gbW_lt_δ h
  have hPδ : G * G < δ := h.δE.mul_lt hGδ hGδ
  have hGGδ : G + G < δ := (inE_indec h.δE).add_lt hGδ hGδ
  have hPGδ : G * G + G < δ := (inE_indec h.δE).add_lt hPδ hGδ
  have hPG1δ : G * G + G + 1 < δ := (inE_indec h.δE).add_lt hPGδ (lu_one_lt_E h.δE)
  have hG0 : 0 < G := hGE.pos
  have hGP : G < G * G := lt_mul_of_one_lt_right hG0 (lu_one_lt_E hGE)
  have hPe : G * G = ω ^ (G + G) := by
    conv_lhs => rw [← show ω ^ G = G from hGE]
    rw [← opow_add]
  have h1ρ : (1 : Ordinal.{0}) < ρ := lu_one_lt_E hρE
  have hρPG : ρ ≤ G * G + G := (hρG.le.trans hGP.le).trans le_self_add
  have w1 : WZ ρ δ {G} ∅ := by
    have := (WZ.empty (ρ := ρ) (δ := δ)).insW hρG.le hGδ (Or.inl hGI)
    simpa using this
  have w2 : WZ ρ δ {G + G, G} ∅ := by
    have := w1.insW (hρG.le.trans le_self_add) hGGδ
      (Or.inr ⟨G, by simp, G, by simp, lt_add_of_pos_right _ hG0, lt_add_of_pos_right _ hG0, rfl⟩)
    simpa using this
  have w3 : WZ ρ δ {G * G, G + G, G} ∅ := by
    have := w2.insW (hρG.le.trans hGP.le) hPδ (Or.inl (by rw [hPe]; exact indec_opow _))
    simpa using this
  have w4 : WZ ρ δ {G * G + G, G * G, G + G, G} ∅ := by
    have := w3.insW hρPG hPGδ
      (Or.inr ⟨G * G, by simp, G, by simp, lt_add_of_pos_right _ hG0, hGP.trans_le le_self_add, rfl⟩)
    simpa using this
  have w5 : WZ ρ δ {G * G + G + 1, G * G + G, G * G, G + G, G} {1} := by
    have := (w4.insZ h1ρ).insW (hρPG.trans le_self_add) hPG1δ
      (Or.inr ⟨G * G + G, by simp, 1, by simp, lt_add_one _, h1ρ.trans_le (hρPG.trans le_self_add), rfl⟩)
    simpa using this
  refine ⟨{G * G + G + 1, G * G + G, G * G, G + G, G}, {1}, w5, by simp, fun A f hW hZ C => ?_⟩
  have hGA : G ∈ A := hW (by simp)
  have hGGA : G + G ∈ A := hW (by simp)
  have hPA : G * G ∈ A := hW (by simp)
  have hPGA : G * G + G ∈ A := hW (by simp)
  have hPG1A : G * G + G + 1 ∈ A := hW (by simp)
  have h1A : (1 : Ordinal.{0}) ∈ A := hZ (by simp)
  obtain ⟨hfE, hPge⟩ := gbImg h hGE hρG hGδ C hGA hGGA hPA hPGA
  have hyG : f ρ < f G := C.mono C.rho hGA hρG
  refine ⟨⟨f G, hfE.symm, opow_dvd_of_inE hfE hyG.le⟩, ?_⟩
  obtain ⟨hyE, hy1, -⟩ := h.vz_img_base C
  by_cases hU : UpsPt (f G)
  · exact (gbW_lt_next hyE hy1 hyG hU.2).le
  · by_contra hlt
    push Not at hlt
    have hsrc : le1 G (G * G + G + 1) := (h.lowδ _ _ hρG hPG1δ.le).2 hLG.1
    have himg := C.cov1 G hGA _ hPG1A hsrc
    have hR := (C.sk _ (C.low _ hGA) hU _).1 himg
    have hf1 : f 1 = 1 := C.fix 1 h1A h1ρ
    have hadd1 : f (G * G + G) + f 1 = f (G * G + G + 1) := C.add (G * G + G) hPGA 1 h1A _ hPG1A rfl
    have hadd2 : f (G * G) + f G = f (G * G + G) := C.add (G * G) hPA G hGA _ hPGA rfl
    have hle : f G * f G + f G + 1 ≤ f (G * G + G + 1) := by
      rw [← hadd1, hf1, ← hadd2]
      exact add_le_add_left (add_le_add_left hPge _) _
    have hlo : f G ≤ f G * f G + f G + 1 :=
      ((le_mul_left _ hfE.pos).trans le_self_add).trans le_self_add
    exact gb_not_le1R hyE hy1 hfE hyG hlt (le1R_of_le hlo hle hR)

end GbK

/-! ## The union of the tower and the new layer -/

/-- The values of the union of the tower. -/
noncomputable def gbVal (p : Σ k : ℕ, (lpTK k).sys.Tm) (x : Ordinal.{0}) : Ordinal.{0} :=
  (lpTK p.1).sys.val p.2 x

theorem gb_val_lt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (p : Σ k : ℕ, (lpTK k).sys.Tm)
    (h : (lpTK p.1).sys.CB p.2 x) : gbVal p x < gbW x :=
  ((lpTK p.1).lt_top_E x hx hx1 p.2 h).trans (gk_lt_W hx hx1 (p.1 + 1))

/-- **The union of the tower**: the terms of every `lpTK k`, top `gbW = ϑˣ(Ω₁·Ω₁ + ω)`. -/
noncomputable def gbUSys : XtSys where
  Tm := Σ k : ℕ, (lpTK k).sys.Tm
  val := gbVal
  CB := fun p x => (lpTK p.1).sys.CB p.2 x
  cs := fun p => (lpTK p.1).sys.cs p.2
  cst := fun c => ⟨0, (lpTK 0).sys.cst c⟩
  top := gbW
  cb_cst := fun p s h => (lpTK p.1).sys.cb_cst p.2 s h
  cb_iff := fun p s s' h h' => (lpTK p.1).sys.cb_iff p.2 s s' h h'
  val_cst := fun c x => (lpTK 0).sys.val_cst c x
  cb_cstI := fun c x h => (lpTK 0).sys.cb_cstI c x h
  lt_top := fun l hl hl1 p h => gb_val_lt (ups_inE hl) (ups_lt_Om1 l hl1) p h
  one_le_top := fun l hl hl1 => one_le_iff_pos.2 (gbW_facts (ups_inE hl) (ups_lt_Om1 l hl1)).2.2.2.1.pos
  rep := fun l hl hl1 v hv => by
    obtain ⟨k, hk⟩ := gb_lt_W_iff (ups_inE hl) (ups_lt_Om1 l hl1) v hv
    obtain ⟨t, ht, et⟩ := (lpTK k).sys.rep l hl hl1 v
      (hk.trans (gk_lt (ups_inE hl) (ups_lt_Om1 l hl1) (Nat.lt_succ_self k)))
    exact ⟨⟨k, t⟩, ht, et⟩
  top_lt := fun l hl hl1 => gbW_lt_next_ups hl hl1
  pkg := fun l hl hl1 p h h1 R => (lpTK p.1).sys.pkg l hl hl1 p.2 h h1 R
  rs := fun l hl hl1 p h => (lpTK p.1).sys.rs l hl hl1 p.2 h
  uni_le := fun σ ρ hσ hρ hB p q hp hq =>
    xt_uni_of_exact hB ((lpTK p.1).exact σ ρ hσ hρ hB p.2 hp) ((lpTK q.1).exact σ ρ hσ hρ hB q.2 hq)
  small := fun p => (lpTK p.1).sys.small p.2

theorem gbUSys_top (x : Ordinal.{0}) : gbUSys.top x = gbW x := rfl

/-- **The limit layer of the tower**: `gbUSys` with top `ϑˣ(Ω₁·Ω₁ + ω)`. -/
noncomputable def gbWL : XtLay where
  sys := gbUSys
  E := gbW
  top_eq := fun x hx hx1 => (gbW_facts hx hx1).2.2.2.1.symm
  exp_dvd := fun x hx hx1 => opow_dvd_of_inE (gbW_facts hx hx1).2.2.2.1 (gbW_facts hx hx1).2.1.le
  exp_lt := fun x hx hx1 => (gbW_facts hx hx1).2.2.1
  top_gt := fun x hx hx1 => (gbW_facts hx hx1).2.1
  top_lt_ups := fun x u hx hx1 hxu hu => gbW_lt_next hx hx1 hxu hu.2
  lt_top_E := fun x hx hx1 p h => gb_val_lt hx hx1 p h
  exact := fun σ ρ hσ hρ hB p hp => (lpTK p.1).exact σ ρ hσ hρ hB p.2 hp
  exp_pi := fun _ _ _ _ hB => gbW_pi hB
  top_wit := fun _ _ _ h => GbK.gbTopWit h

/-- **The new base package**: the limit layer of the tower. -/
noncomputable def gbWB : LpB where
  K := gbWL
  ek := fun x hx hx1 => (gbW_facts hx hx1).2.2.2.1
  mem := fun x hx hx1 => (gbW_facts hx hx1).1

theorem gbWB_E (x : Ordinal.{0}) : gbWB.K.E x = gbW x := rfl

theorem gbWB_sys : gbWB.K.sys = gbUSys := rfl

/-- **The tops of the tower are terms of the union**, with gap `> 1`. -/
theorem gb_topIn (k : ℕ) : LyTopIn gbUSys (lpTK k).sys := by
  refine ⟨⟨k + 1, (LpT.tp : LpT (lpTB (k + 1)))⟩, fun x _ _ => ⟨trivial, rfl⟩, fun l hl hl1 => ?_⟩
  have hρE := ups_inE hl
  have hρ1 := ups_lt_Om1 l hl1
  have hW := (gbW_facts hρE hρ1).2.2.2.1
  exact (inE_indec hW).add_lt (gk_lt_W hρE hρ1 (k + 1)) (lu_one_lt_E hW)

theorem gb_topPkg : XtTopPkg gbUSys := XtLay.topPkg gbWL

/-- **`Λ⁺(lpTK k) < Λ⁺(gbUSys)`.** -/
theorem gb_tow_lt (k : ℕ) : xtB1 (lpTK k).sys < xtB1 gbUSys :=
  lyB1_lt gb_topPkg (XtLay.topPkg (lpTK k)) (gb_topIn k)

/-- **`O_{gbUSys} = O_{lpTK k}` below `Λ⁺(lpTK k)`.** -/
theorem gb_tow_eq (k : ℕ) {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h : μ < xtB1 (lpTK k).sys) :
    xtOrec gbUSys μ = xtOrec (lpTK k).sys μ :=
  lyEq (XtLay.topPkg (lpTK k)) (gb_topIn k) hμ h

/-- **`ι(Γ_{Ω₁+ω}) = sup_k Λ⁺(lpTK k) < Λ⁺(gbUSys)`.** -/
theorem gb_towSup_lt (S : InaccSeq.{0}) : iota S Ga.gaW < xtB1 gbUSys ∧ lpTowFam.famSup < xtB1 gbUSys := by
  have h : lpTowFam.famSup < xtB1 gbUSys :=
    lt_of_le_of_lt (Ordinal.iSup_le fun k => (lyLamGt (XtLay.topPkg (lpTK k)) (gb_topIn k)).le)
      (lyLamLtB1 gb_topPkg)
  refine ⟨?_, h⟩
  rw [← (Ga.gaTowSup (S := S)).1]
  exact h

end Googology.Trans.PoR.InaccPsi.R2.Gb

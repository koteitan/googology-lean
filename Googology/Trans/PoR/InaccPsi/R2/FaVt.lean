import Googology.Trans.PoR.InaccPsi.R2.FaZB
import Googology.Trans.PoR.InaccPsi.R2.VjTh

/-!
# Fa: THE READING OF AN ATOM AS A `ϑ`-NODE

`Φ_μ = Ul.ulH S 0 μ`, `Δ_μ = Ω₁·(Ω₁ + μ)`, `b` strongly critical, `m` the next `υ`-point above `b`, `μ < θ`.

* `fa_phi_T` (the level datum and the argument are in `T^b`);
* `fa_phi_first` (**`Φ_μ(D) = ϑᵇ(Δ_μ + D)`**, the first run), `fa_phi_base` (**`Φ_μ(b + 1 + δ) = ϑᵇ(Δ_μ + δ)`**, `b` fixed),
  `fa_phi_fix` (**`Φ_μ(p + 1 + δ) = ϑᵇ(Δ_μ + (p + δ))`**, `p > b` fixed).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Fa

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul Googology.Trans.PoR.InaccPsi.R2.Vd
  Googology.Trans.PoR.InaccPsi.R2.Aw

variable {S : InaccSeq.{0}}

section Phi

variable {b μ : Ordinal.{0}} (hb : SC b) (hb1 : b < Om1) (hμ : μ < ConjT.th S)

include hb hb1

/-- **Below the next `υ`-point every value is in `T^b`**, and the level datum is below a value of `Φ_μ`. -/
theorem fa_phi_T {e : Ordinal.{0}} (hx : ulH S 0 μ e < Aw.awNx b) :
    vdDat S (Om1 + μ) ∈ Tset b ∧ vdDat S (Om1 + μ) < Om1 := by
  obtain ⟨-, -, -, hm1, hTm, -⟩ := Aw.awNx_facts hb hb1
  have hSC : SC (ulH S 0 μ e) := ulH_SC _ _
  have hx1 : ulH S 0 μ e ≤ Om1 := (hx.trans hm1).le
  have hd : vdDat S (Om1 + μ) < ulH S 0 μ e := (Vj.vj_datv hSC hx1).2 (ulH_D_lt μ e)
  have hdm := hd.trans hx
  exact ⟨(hTm _ (hdm.trans hm1)).2 hdm, hdm.trans hm1⟩

include hμ

/-- **`Φ_μ(D) = ϑᵇ(Δ_μ + D)`**: the first run. -/
theorem fa_phi_first {D : Ordinal.{0}} (hx : ulH S 0 μ D < Aw.awNx b) (hb0 : b < ulH S 0 μ 0)
    (hcond : ∀ d, d ≤ D → d < ulH S 0 μ (0 + d)) : ulH S 0 μ D = vt b (Om1 * (Om1 + μ) + D) := by
  obtain ⟨-, -, -, hm1, hTm, -⟩ := Aw.awNx_facts hb hb1
  obtain ⟨hμT, -⟩ := fa_phi_T hb hb1 hx
  have hDlt : D < ulH S 0 μ D := by
    have := hcond D le_rfl; rwa [zero_add] at this
  have hDm := hDlt.trans hx
  have h := Vj.vjK_enum0 hb hb1 hμ hμT (c0 := 0) hb0 (ulH_D_lt μ 0)
    (fun c hc => absurd hc (not_lt.2 zero_le)) D ((hTm _ (hDm.trans hm1)).2 hDm) (hDm.trans hm1) hcond
  rw [zero_add] at h
  exact h.symm

/-- **`Φ_μ(b + 1 + δ) = ϑᵇ(Δ_μ + δ)`** for a fixed point `b` of `Φ_μ`. -/
theorem fa_phi_base {δ : Ordinal.{0}} (hbf : ulH S 0 μ b = b) (hx : ulH S 0 μ (b + 1 + δ) < Aw.awNx b)
    (hcond : ∀ d, d ≤ δ → d < ulH S 0 μ (b + 1 + d)) : ulH S 0 μ (b + 1 + δ) = vt b (Om1 * (Om1 + μ) + δ) := by
  obtain ⟨-, -, -, hm1, hTm, -⟩ := Aw.awNx_facts hb hb1
  obtain ⟨hμT, -⟩ := fa_phi_T hb hb1 hx
  have hδm := (hcond δ le_rfl).trans hx
  have hb0 : b < ulH S 0 μ (b + 1) := by
    conv_lhs => rw [← hbf]
    exact (ulH_lt_iff μ).2 (lt_add_one b)
  have hmin : ∀ c, c < b + 1 → ulH S 0 μ c ≤ b ∨ ulH S 0 μ c ≤ ulD S 0 μ := fun c hc => by
    left
    have : ulH S 0 μ c ≤ ulH S 0 μ b := (ulH_le_iff μ).2 (Order.lt_add_one_iff.1 hc)
    rwa [hbf] at this
  exact (Vj.vjK_enum0 hb hb1 hμ hμT hb0 (ulH_D_lt μ _) hmin δ ((hTm _ (hδm.trans hm1)).2 hδm) (hδm.trans hm1) hcond).symm

/-- **`Φ_μ(p + 1 + δ) = ϑᵇ(Δ_μ + (p + δ))`** for a fixed point `p > b` of `Φ_μ`. -/
theorem fa_phi_fix {p δ : Ordinal.{0}} (hp : ulH S 0 μ p = p) (hbp : b < p) (hx : ulH S 0 μ (p + 1 + δ) < Aw.awNx b)
    (hcond : ∀ d, d ≤ δ → d < ulH S 0 μ (p + 1 + d)) :
    ulH S 0 μ (p + 1 + δ) = vt b (Om1 * (Om1 + μ) + (p + δ)) := by
  obtain ⟨-, -, -, hm1, hTm, -⟩ := Aw.awNx_facts hb hb1
  obtain ⟨hμT, -⟩ := fa_phi_T hb hb1 hx
  have hplt : ∀ d, p < ulH S 0 μ (p + 1 + d) := fun d => by
    conv_lhs => rw [← hp]
    exact (ulH_lt_iff μ).2 ((lt_add_one p).trans_le le_self_add)
  have hsum : p + δ < ulH S 0 μ (p + 1 + δ) :=
    (ulH_SC μ _).isPrincipal (hplt δ) (hcond δ le_rfl)
  have hm := hsum.trans hx
  have hcond' : ∀ σ, σ ≤ δ → p + 1 + σ < ulH S 0 μ (p + 1 + σ) := fun σ hσ => by
    have hS := ulH_SC (S := S) (s := 0) μ (p + 1 + σ)
    have h1 : 1 + σ < ulH S 0 μ (p + 1 + σ) := hS.isPrincipal (Gg.gg_one_lt_of_SC hS) (hcond σ hσ)
    have h2 : p + (1 + σ) < ulH S 0 μ (p + 1 + σ) := hS.isPrincipal (hplt σ) h1
    rwa [← add_assoc] at h2
  exact (Vj.vjK_enum_fix2 hb hb1 hμ hμT hp hbp δ ((hTm _ (hm.trans hm1)).2 hm) (hm.trans hm1) hcond').symm

end Phi

section Atom

open Googology.Trans.PoR.InaccPsi.R2.Kz Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Nm

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) {K : Ordinal.{0}} (hKB : KzB S K)
  (hown : ConjT.Aη S (cdEta S l) ∈ S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)))
  (hρ : S.psi (ConjT.Aη S (cdEta S l)) (Om 1) = upsilon l) (hWK : Om ω < K) (hAK : ConjT.Aη S (cdEta S l) < K)

include hl hX hKB hown hρ hWK hAK

/-- A member of the hull below `Ω₂` is in `D_K`. -/
theorem fa_hull_D {c : Ordinal.{0}} (hc : GxCl (upsilon l) (ldAtR S l) c) (hc2 : c < Om (1 + 1)) : VbDK S l K c := by
  obtain ⟨hZ, hZ1⟩ := Vb.vbZ hl hX
  have h2K : Om (1 + 1 : Ordinal.{0}) < K := (Om_lt_Om.2 (Ui.ui_s1_lt_omega one_lt_omega0)).trans_le hKB.ge
  have hρK : upsilon l ≤ S.psi K (Om (1 + 1)) := (hZ1.trans (Ui.ui_L_lt_psi (s := 1) K)).le
  have hH := (ldHull_iff hl hX hc2).2 hc
  exact ⟨hH, CSet_mono hAK.le hρK hH, hc2.trans h2K⟩

/-- **A reading of a code `z`, with `w` the largest closed atom below `z`, is below the next `υ`-point above `Θ w`.** -/
theorem fa_seg {w z : Ordinal.{0}} (hw : FaLvB S w) (hwz : w ≤ z) (hmax : ∀ u, FaLvB S u → u ≤ z → u ≤ w)
    (hzc : GxCl (upsilon l) (ldAtR S l) z) (hz2 : z < Om (1 + 1)) (hwc : GxCl (upsilon l) (ldAtR S l) w) :
    ∀ u, gxTh (upsilon l) (ldAtR S l) w < u → UpsPt u → gxTh (upsilon l) (ldAtR S l) z < u := by
  intro u huw hU
  by_contra hc
  have huz : u ≤ gxTh (upsilon l) (ldAtR S l) z := not_lt.1 hc
  have hcode : ∃ c', GxCl (upsilon l) (ldAtR S l) c' ∧ c' ≤ z ∧ gxTh (upsilon l) (ldAtR S l) c' = u := by
    rcases huz.lt_or_eq with h | h
    · obtain ⟨c', h1, h2, h3⟩ := gxTh_onto h
      exact ⟨c', h1, h2.le, h3⟩
    · exact ⟨z, hzc, le_rfl, h.symm⟩
  obtain ⟨c', hc'c, hc'z, rfl⟩ := hcode
  have hwc' : w < c' := by
    by_contra hle
    exact absurd huw (not_lt.2 (gxTh_mono (not_lt.1 hle)))
  have hc'2 := hc'z.trans_lt hz2
  have hc'D := fa_hull_D hl hX hKB hown hρ hWK hAK hc'c hc'2
  have hLv := fa_ups_Lv hl hX hKB hown hρ hWK hAK hc'D hc'2 ((fa_θ_le_Lv hw).trans hwc'.le) hU
  exact absurd (hmax c' hLv hc'z) (not_le.2 hwc')

/-- **THE READING OF AN ATOM AS A `ϑ`-NODE**: for `z = Hˡ¹_γ(c + D)`, `γ < θ₂`, `θ < z`, `w` the largest closed atom below `z`:
`Θ z = ϑ^{Θ w}(Δ_{T γ} + Θ η)`, with `η = D` on the first run, `η = -1 + D` for `c = w`, `η = c + (-1 + D)` otherwise. -/
theorem fa_atom_vt {γ B c D ηc w : Ordinal.{0}} (hγ : γ < S.psi (Om ω) (Om (1 + 1 + 1)))
    (hy : c + D < ulH S 1 γ (c + D)) (hzW : ulH S 1 γ (c + D) < Om (1 + 1))
    (hzc : GxCl (upsilon l) (ldAtR S l) (ulH S 1 γ (c + D))) (hθz : ConjT.th S < ulH S 1 γ (c + D))
    (hownB : B ∈ S.CSet B (S.psi B (Om (1 + 1)))) (hc : ulH S 1 γ c = S.psi B (Om (1 + 1)))
    (hcond : ∀ d, d ≤ D → d < ulH S 1 γ (c + d))
    (hcase : c = 0 ∨ (ulH S 1 γ c = c ∧ ∀ q, ulH S 1 γ q = q → q ≤ c + D → q ≤ c))
    (hw : FaLvB S w) (hwz : w ≤ ulH S 1 γ (c + D)) (hmax : ∀ u, FaLvB S u → u ≤ ulH S 1 γ (c + D) → u ≤ w)
    (hwc : GxCl (upsilon l) (ldAtR S l) w)
    (hηc : (c = 0 ∧ ηc = D) ∨ (c ≠ 0 ∧ c = w ∧ ηc = cdOff D) ∨ (c ≠ 0 ∧ c ≠ w ∧ ηc = c + cdOff D)) :
    gxTh (upsilon l) (ldAtR S l) (ulH S 1 γ (c + D)) =
      vt (gxTh (upsilon l) (ldAtR S l) w) (Om1 * (Om1 + vbTK S l K γ) + gxTh (upsilon l) (ldAtR S l) ηc) ∧
    VbDK S l K γ ∧ vbTK S l K γ < ConjT.th S ∧ VbDK S l K D ∧ VbDK S l K c ∧
      vdDat S (Om1 + vbTK S l K γ) ∈ Tset (gxTh (upsilon l) (ldAtR S l) w) := by
  obtain ⟨hZ, hZ1⟩ := Vb.vbZ hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hPC := faPC_D (S := S) (l := l) hKB
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hO1 : (Om1 : Ordinal.{0}) = Om 1 := Rj.rj_Om1
  have hzD := fa_hull_D hl hX hKB hown hρ hWK hAK hzc hzW
  obtain ⟨hγD, hyD, hDD, hcD', hTγ, hcond', hbase, hTy, hTz, hBD, hBA, hWB⟩ :=
    faALc hl hX hKB hown hρ hWK hγ hy hzW hzD hθz hownB hc rfl hcond hcase
  have h3W : Om (1 + 1 + 1 : Ordinal.{0}) < Om ω := Om_lt_Om.2 Vp.vp_three_lt_omega
  have hDle : D ≤ c + D := le_add_self
  have hD2 : D < Om (1 + 1) := (hDle.trans_lt hy).trans hzW
  have hcle : c ≤ c + D := le_self_add
  have hc2 : c < Om (1 + 1) := (hcle.trans_lt hy).trans hzW
  have hw2 : w < Om (1 + 1) := hwz.trans_lt hzW
  have hwD := fa_hull_D hl hX hKB hown hρ hWK hAK hwc hw2
  have hΘT : ∀ {x : Ordinal.{0}}, x < Om (1 + 1) → VbDK S l K x →
      gxTh (upsilon l) (ldAtR S l) x = vbTK S l K x := fun hx2 hx => (vbTK_code hl hX hKB hx2 hx.1).symm
  -- the base
  obtain ⟨E, hownE, hWE, hdE, hEw⟩ := id hw
  have hψD : VbDK S l K (S.psi E (Om (1 + 1))) := by rw [hEw]; exact hwD
  obtain ⟨hED, hEA⟩ := fa_arg hl hX (r := 1) le_rfl hψD hownE
  have hbG : gxTh (upsilon l) (ldAtR S l) w = S.psi (faG S l K E) (Om 1) := by
    rw [← hEw]; exact (faG_law hl hX hKB hown hρ hED hownE hEA (h3W.le.trans hWE)).1
  set b := gxTh (upsilon l) (ldAtR S l) w with hbdef
  have hbS : SC b := by rw [hbG]; exact fa0_SC _
  have hb1 : b < Om1 := by rw [hbG, hO1]; exact fa0_lt _
  obtain ⟨-, hbU, -, -, -, -⟩ := Aw.awNx_facts hbS hb1
  have hbn : b < Aw.awNx b := (Aw.awNx_facts hbS hb1).1
  have hseg := fa_seg hl hX hKB hown hρ hWK hAK hw hwz hmax hzc hzW hwc _ hbn hbU
  rw [hΘT hzW hzD, hTz] at hseg
  refine ⟨?_, hγD, hTγ, hDD, hcD', (fa_phi_T hbS hb1 hseg).1⟩
  rw [hΘT hzW hzD, hTz]
  have hLvS : SC w := fa_Lv_SC hw
  have h1w : Om 1 < w := (Ui.ui_L_lt_psi (s := 1) (Om ω)).trans_le (fa_θ_le_Lv hw)
  rcases hηc with ⟨hc0, hη⟩ | ⟨hc0, hcw, hη⟩ | ⟨hc0, hcw, hη⟩ <;> rw [hη]
  · -- the first run
    subst hc0
    rw [vbTK_zero hl hX hKB, zero_add] at hTy
    rw [vbTK_zero hl hX hKB] at hcond' hbase
    rw [zero_add] at *
    rw [hTy, hΘT hD2 hDD]
    rw [hTy] at hseg
    have hwlt : w < S.psi B (Om (1 + 1)) := by
      by_contra hle
      have hle' : S.psi B (Om (1 + 1)) ≤ w := not_lt.1 hle
      have hd : ulD S 1 γ < w := by
        have := ulH_D_lt (S := S) (s := 1) γ 0
        rw [hc] at this
        exact this.trans_le hle'
      have hK := (ul_vis hLvS).1 hd
      have hfix := fa_Lv_fix hw hγ hK
      have hwy : w ≤ D := by
        have h1 : ulH S 1 γ w ≤ ulH S 1 γ D := by rw [hfix]; exact hwz
        exact (ulH_le_iff γ).1 h1
      have h2 := hcond w hwy
      rw [zero_add, hfix] at h2
      exact lt_irrefl _ h2
    have hψB : gxTh (upsilon l) (ldAtR S l) (S.psi B (Om (1 + 1))) = S.psi (faG S l K B) (Om 1) :=
      (faG_law hl hX hKB hown hρ hBD hownB hBA (h3W.le.trans hWB)).1
    have hb0 : b < ulH S 0 (vbTK S l K γ) 0 := by
      rw [hbase, ← hψB]; exact gxTh_lt hwc hwlt
    exact fa_phi_first hbS hb1 hTγ hseg hb0 hcond'
  all_goals
    obtain ⟨hcf, hmaxc⟩ := hcase.resolve_left hc0
    have hD0 : D ≠ 0 := by
      rintro rfl
      rw [add_zero, hcf] at hy
      exact lt_irrefl _ hy
    have hψc : S.psi B (Om (1 + 1)) = c := hc.symm.trans hcf
    have hψB : vbTK S l K (S.psi B (Om (1 + 1))) = S.psi (faG S l K B) (Om 1) :=
      (faG_law hl hX hKB hown hρ hBD hownB hBA (h3W.le.trans hWB)).2.2
    have hpf : ulH S 0 (vbTK S l K γ) (vbTK S l K c) = vbTK S l K c := by
      rw [hbase, ← hψB, hψc]
    have h1D : 1 ≤ D := one_le_iff_ne_zero.2 hD0
    have hδD : VbDK S l K (cdOff D) := by
      unfold cdOff
      split_ifs with h
      · exact hPC.sub hDD hPC.one h1D
      · exact hDD
    have hδe : 1 + cdOff D = D := Aw.aw_one_add_off h1D
    have hδ2 : cdOff D < Om (1 + 1) := (cdOff_le D).trans_lt hD2
    have hTD : vbTK S l K D = 1 + vbTK S l K (cdOff D) := by
      conv_lhs => rw [← hδe]
      rw [kzT_add hl hX hKB hPC.one hδD, fa_T_one hl hX hKB]
    have hcondδ : ∀ d, d ≤ vbTK S l K (cdOff D) →
        d < ulH S 0 (vbTK S l K γ) (vbTK S l K c + 1 + d) := fun d hd => by
      have h1 := hcond' (1 + d) (by rw [hTD]; exact add_le_add le_rfl hd)
      rw [← add_assoc] at h1
      exact (le_add_self (a := d)).trans_lt h1
    have hTy' : vbTK S l K (c + D) = vbTK S l K c + 1 + vbTK S l K (cdOff D) := by
      rw [hTy, hTD, add_assoc]
    rw [hTy'] at hseg ⊢
  · -- `c = w`
    subst hcw
    have hTc : vbTK S l K c = b := (hΘT hc2 hcD').symm
    rw [hTc] at hpf hseg hcondδ ⊢
    rw [hΘT hδ2 hδD]
    exact fa_phi_base hbS hb1 hTγ hpf hseg hcondδ
  · -- `w < c`
    have hwc' : w < c := by
      refine lt_of_le_of_ne ?_ (Ne.symm hcw)
      by_cases hK : UlK S 1 w γ
      · have hfix := fa_Lv_fix hw hγ hK
        have hwy : w ≤ c + D := by
          have h1 : ulH S 1 γ w ≤ ulH S 1 γ (c + D) := by rw [hfix]; exact hwz
          exact (ulH_le_iff γ).1 h1
        exact hmaxc w hfix hwy
      · have hd : w ≤ ulD S 1 γ := not_lt.1 fun h => hK ((ul_vis hLvS).1 h)
        rw [← hcf]
        exact hd.trans (ulH_D_lt γ c).le
    have hcc : GxCl (upsilon l) (ldAtR S l) c := (ldHull_iff hl hX hc2).1 hcD'.1
    have hbp : b < vbTK S l K c := by
      rw [← hΘT hc2 hcD']; exact gxTh_lt hwc hwc'
    rw [gxTh_add hZ hAt hcc, hΘT hc2 hcD', hΘT hδ2 hδD]
    exact fa_phi_fix hbS hb1 hTγ hpf hbp hseg hcondδ

end Atom

end Googology.Trans.PoR.InaccPsi.R2.Fa

import Googology.Trans.PoR.InaccPsi.R2.YvUp

/-!
# The image of a level below `θ` is a level; the base change of a `ϑ`-node with a moving level

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`π = pi σ τ`, `θ = ConjT.th S`, `Γ = Ω₁·M` a level (`1 ≤ M`, `Γ < θ`).

* `yv_pi_lt_th` (**`π z < θ` for every `z ∈ Tᵗ[σ] ∩ Ω₂`**: `R2.uzTBound`, [W07a] Thm 3.14, 3.23), `yv_pi_gt_Om1`;
* `yv_pi_opow` (**`π(ω^l) = ω^{π l}`** for every code `Ω₁ ≤ l` with `ω^l < θ`), `yv_pi_dvd` (**`Ω₁ ∣ z ⇒ Ω₁ ∣ π z`**
  below `θ`: `Vc.vc_pi_dvd` widened);
* `yv_level_img` (**the image of a level is a level**: `π(Ω₁·M) = Ω₁·M'`, `1 ≤ M'`, `Ω₁·M' < θ`, `= yvSub π (Ω₁·M)`),
  `yv_node_img` (**`π(ϑᵗ(Ω₁·M + ρ)) = ϑ^σ(Ω₁·M' + π ρ)` with `Ω₁·M' = yvSub π (Ω₁·M)` a level**: `Vc.vc_node_img`
  widened from `B₂` to `θ`, the leaves of `M` moving).

Axioms: those of `R2.CitedVd`, `R2.CitedVp`, `R2.CitedUz` (`uzTBound`) and the base-change axioms of `R2.Cited`.  No new
axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul Googology.Trans.PoR.InaccPsi.R2.Uc
  Googology.Trans.PoR.InaccPsi.R2.Vs

variable {S : InaccSeq.{0}}

/-- **`π z < θ`** for every `z ∈ Tᵗ[σ]` below `Ω₂`. -/
theorem yv_pi_lt_th (S : InaccSeq.{0}) {σ τ z : Ordinal.{0}} (h : Bases σ τ) (hT : z ∈ TB τ σ) (h2 : z < OmTwo) :
    pi σ τ z < ConjT.th S := by
  have hπT : pi σ τ z ∈ Tset σ := (pi_bijOn h).1.mapsTo hT
  have h2' : z < Om (1 + 1) := by rw [Ui.ui_one_W]; exact h2
  have hπ2 : pi σ τ z < OmTwo := by
    rw [← Ui.ui_one_W]; exact vs_pi_lt_Om h (Ui.ui_s1_lt_omega (s := 0) omega0_pos |>.trans_le' (by simp))
      le_rfl hT h2'
  exact uzTBound (S := S) σ h.1 (h.2.2.1.trans h.2.2.2) _ hπT hπ2

/-- **`Ω₁ < z ⇒ Ω₁ < π z`** on `Tᵗ[σ]`. -/
theorem yv_pi_gt_Om1 {σ τ z : Ordinal.{0}} (h : Bases σ τ) (hT : z ∈ TB τ σ) (h1 : Om1 < z) :
    Om1 < pi σ τ z := by
  obtain ⟨o1, o2⟩ := pi_Om1 h
  have := (pi_bijOn h).2 o1 hT h1; rwa [o2] at this

/-- **`π(ω^l) = ω^{π l}`** for `l ≥ Ω₁` with `ω^l ∈ Tᵗ[σ]`, `ω^l < θ` (and then `l ∈ Tᵗ[σ]`). -/
theorem yv_pi_opow {σ τ l : Ordinal.{0}} (h : Bases σ τ) (hl1 : Om1 ≤ l) (hlθ : ω ^ l < ConjT.th S)
    (hwT : ω ^ l ∈ TB τ σ) : l ∈ TB τ σ ∧ pi σ τ (ω ^ l) = ω ^ pi σ τ l := by
  have hlθ' : l < ConjT.th S := (right_le_opow l one_lt_omega0).trans_lt hlθ
  rcases lt_or_ge l Gg.ggE with hlE1 | hlE1
  · have hwB : ω ^ l < ucB := by
      have : ω ^ l < ω ^ Gg.ggE := (opow_lt_opow_iff_right one_lt_omega0).2 hlE1
      rw [Rk.rk_E_inE] at this; exact this.trans_le Vm.vm_E_le_B
    obtain ⟨h1, h2, -⟩ := Vc.vc_pi_opow h hl1 hwB hwT
    exact ⟨h1, h2⟩
  by_cases hlE : ω ^ l = l
  · have hlT : l ∈ TB τ σ := by rw [← hlE]; exact hwT
    refine ⟨hlT, ?_⟩
    obtain ⟨r, hG, hr⟩ := yv_bound (S := S) hlθ'
    rw [hlE]
    exact (yv_pi_eps h r ((yv_TB_iff h hlθ').1 hlT) hG hr hl1 hlE).symm
  · obtain ⟨hiff, hπp⟩ := (vsPkg_one (S := S)).opow h hlE1 hlE hlθ
    have hlT := hiff.1 hwT
    exact ⟨hlT, hπp hlT⟩

/-- **`Ω₁ ∣ z ⇒ Ω₁ ∣ π z`** for codes `z ∈ Tᵗ[σ]` below `θ`. -/
theorem yv_pi_dvd {σ τ : Ordinal.{0}} (h : Bases σ τ) :
    ∀ z, z < ConjT.th S → z ∈ TB τ σ → Om1 ∣ z → Om1 ∣ pi σ τ z := by
  have hΩe : ∀ e, Om1 ≤ e → Om1 ∣ ω ^ e := fun e he => by
    rw [← Rj.rj_Om1_opow]; exact opow_dvd_opow ω he
  have hεd : ∀ x, Om1 ≤ x → ω ^ x = x → Om1 ∣ x := fun x hx hxE => by rw [← hxE]; exact hΩe x hx
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hzθ hT hd
  rcases lt_or_ge z ucB with hB | hB
  · exact Vc.vc_pi_dvd h z hB hT hd
  have h1 : Om1 < z := ucB_gt.trans_le hB
  have hπ1 := yv_pi_gt_Om1 h hT h1
  by_cases hE : ω ^ z = z
  · obtain ⟨r, hG, hr⟩ := yv_bound (S := S) hzθ
    exact hεd _ hπ1.le (yv_pi_eps h r ((yv_TB_iff h hzθ).1 hT) hG hr h1.le hE)
  have hz0 : z ≠ 0 := (Rj.rj_Om1_pos.trans h1).ne'
  set l := log ω z with hldef
  have hl1 : Om1 ≤ l := Si.si_Om1_le_log h1.le
  have hrz : z % ω ^ l < z := Rj.rj_mod_lt hz0
  have hτz : τ ≤ z := (h.2.2.2.trans h1).le
  have hwz : ω ^ l ≤ z := opow_log_le_self ω hz0
  have hcomps := Si.si_comps_cons hz0
  have hwT : ω ^ l ∈ TB τ σ := Si.siTB_of_comps h hT hτz (fun p hp => by
    rw [comps_opow, List.mem_singleton] at hp
    rw [hcomps, hp]; exact List.mem_cons_self ..)
  have hrT : z % ω ^ l ∈ TB τ σ :=
    Si.siTB_of_comps h hT hτz (fun p hp => by rw [hcomps]; exact List.mem_cons_of_mem _ hp)
  obtain ⟨hlT, hπw⟩ := yv_pi_opow (S := S) h hl1 (hwz.trans_lt hzθ) hwT
  have hpos : ω ^ l ≠ 0 := opow_ne_zero _ omega0_ne_zero
  have hlt : z < ω ^ l * ω := by
    rw [← opow_succ]; exact lt_opow_succ_log_self one_lt_omega0 z
  obtain ⟨n, hn⟩ := lt_omega0.1 ((Ordinal.div_lt hpos).2 hlt)
  have hdec : ω ^ l * (n : Ordinal.{0}) + z % ω ^ l = z := by rw [← hn]; exact Ordinal.div_add_mod _ _
  have hdr : Om1 ∣ z % ω ^ l := by
    have h' : Om1 ∣ ω ^ l * (n : Ordinal.{0}) := Dvd.dvd.mul_right (hΩe l hl1) _
    rw [← hdec] at hd
    exact (Ordinal.dvd_add_iff h').1 hd
  have hrθ := hrz.trans hzθ
  have IHr := IH _ hrz hrθ hrT hdr
  obtain ⟨hk1, hk2⟩ := pi_mul_nat h hwT hπw n
  obtain ⟨c1, c2⟩ := pi_add h hk1 hrT
  rw [hdec] at c2
  rw [c2, hk2]
  have hπl : Om1 ≤ pi σ τ l := by
    rcases hl1.lt_or_eq with hl | hl
    · exact (yv_pi_gt_Om1 h hlT hl).le
    · rw [← hl, (pi_Om1 h).2]
  exact (Ordinal.dvd_add_iff (Dvd.dvd.mul_right (hΩe _ hπl) _)).2 IHr

/-- **The image of a level is a level**: `Γ = Ω₁·M ∈ Tᵗ[σ]`, `1 ≤ M`, `Γ < θ` ⇒ `π Γ = Ω₁·M'` with `1 ≤ M'`,
`Ω₁·M' < θ`, and `π Γ = yvSub π Γ`. -/
theorem yv_level_img {σ τ M : Ordinal.{0}} (h : Bases σ τ) (hM1 : 1 ≤ M) (hθ : Om1 * M < ConjT.th S)
    (hT : Om1 * M ∈ TB τ σ) :
    ∃ M', pi σ τ (Om1 * M) = Om1 * M' ∧ 1 ≤ M' ∧ Om1 * M' < ConjT.th S ∧
      pi σ τ (Om1 * M) = yvSub S (pi σ τ) (Om1 * M) := by
  obtain ⟨M', hM'⟩ := yv_pi_dvd h _ hθ hT (dvd_mul_right _ _)
  have hΓ2 : Om1 * M < OmTwo := hθ.trans (Xe.xe_th S).2.2
  have hπθ := yv_pi_lt_th S h hT hΓ2
  have hΓ1 : Om1 ≤ Om1 * M := le_mul_left Om1 (one_le_iff_pos.1 hM1)
  have hπ1 : Om1 ≤ pi σ τ (Om1 * M) := by
    rcases hΓ1.lt_or_eq with hlt | heq
    · exact (yv_pi_gt_Om1 h hT hlt).le
    · rw [← heq, (pi_Om1 h).2]
  refine ⟨M', hM', ?_, hM' ▸ hπθ, yv_pi_TB h hθ hT⟩
  rcases eq_or_ne M' 0 with h0 | h0
  · rw [hM', h0, mul_zero] at hπ1
    exact absurd hπ1 (not_le.2 Rj.rj_Om1_pos)
  · exact one_le_iff_ne_zero.2 h0

/-- **The base change of a `ϑ`-node with a moving level below `θ`**: for bases `σ < τ`, a level `Ω₁·M ∈ Tᵗ[σ]`
(`1 ≤ M`, `Ω₁·M < θ`) and `ρ ∈ Tᵗ[σ] ∩ Ω₁`: `π(ϑᵗ(Ω₁·M + ρ)) = ϑ^σ(Ω₁·M' + π ρ)`, where `Ω₁·M' = yvSub π (Ω₁·M)`
is a level (`1 ≤ M'`, `Ω₁·M' < θ`). -/
theorem yv_node_img {σ τ M ρ : Ordinal.{0}} (h : Bases σ τ) (hM1 : 1 ≤ M) (hθ : Om1 * M < ConjT.th S)
    (hT : Om1 * M ∈ TB τ σ) (hρ : ρ ∈ TB τ σ) (hρ1 : ρ < Om1) :
    ∃ M', Om1 * M' = yvSub S (pi σ τ) (Om1 * M) ∧ 1 ≤ M' ∧ Om1 * M' < ConjT.th S ∧
      Om1 * M + ρ ∈ TB τ σ ∧ pi σ τ (vt τ (Om1 * M + ρ)) = vt σ (Om1 * M' + pi σ τ ρ) := by
  obtain ⟨M', hM', h1, hθ', hsub⟩ := yv_level_img h hM1 hθ hT
  obtain ⟨c1, c2⟩ := pi_add h hT hρ
  have h2 : Om1 * M + ρ < OmTwo :=
    ((Xe.xe_th S).1.add_lt hθ (hρ1.trans (Xe.xe_th S).2.1)).trans (Xe.xe_th S).2.2
  refine ⟨M', by rw [← hsub, hM'], h1, hθ', c1, ?_⟩
  rw [pi_vt_two h c1 h2, c2, hM']

end Googology.Trans.PoR.InaccPsi.R2.Yv

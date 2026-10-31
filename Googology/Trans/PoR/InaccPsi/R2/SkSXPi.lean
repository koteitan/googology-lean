import Googology.Trans.PoR.InaccPsi.R2.WdRoad
import Googology.Trans.PoR.InaccPsi.R2.WcSupLo
import Googology.Trans.PoR.InaccPsi.R2.VrRoad
import Googology.Trans.PoR.InaccPsi.R2.TyRng

/-!
# Refuter of the skeleton part "supply": the base change `π` on `[σ, τ)` and on `[τ, τ^∞)`

* `skSX_piT`: every `c ∈ [τ, τ^∞)` lies in `Tᵗ[σ]` for all large `σ < τ` (from `exists_next`, `Par_sub`).  So the
  SUSPECT leaf `skPiT` is a THEOREM.
* `skSX_notTB`: a point `p ∈ [σ, τ)` is NOT in `Tᵗ[σ]` (`TB_inter_lt`); every axiom that fixes a value of `π_{σ,τ}`
  asks membership in `Tᵗ[σ]`, so `π_{σ,τ}(p)` is not determined by the axioms.
* `skSX_offMap_pi`: the exponent clause of the map data forces `π_{υ_μ,υ_λ}(m z) < λ`; at `z = ω^{υ_μ}` this is
  `π_{υ_μ,υ_λ}(υ_μ) < λ` (`skSX_offMap_free`), a condition on an undetermined value.
* `skSX_img_pi`: the image clause of `Vr.VrCarry` at `E = lo p + D` forces `π_{υ_μ,υ_λ}(p) + img D ≤ r(μ+f g)` for
  every `p < υ_λ`, in particular for every `p ∈ [υ_μ, υ_λ)`, again an undetermined value.

No new axiom.
-/

set_option autoImplicit false

namespace R2Skel.SkSX

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **`skPiT` holds**: for a `υ`-point `τ` with next `υ`-point `u`, every `c ∈ [τ, u)` lies in `Tᵗ[σ]` for every
base `σ` above some `σ₀ < τ`. -/
theorem skSX_piT {τ u : Ordinal.{0}} (hτ : UpsPt τ) (hn : IsNext τ u) :
    ∀ c, τ ≤ c → c < u → ∃ σ₀ < τ, ∀ σ, σ₀ ≤ σ → Bases σ τ → c ∈ TB τ σ := by
  intro c _ hcu
  by_cases h1 : τ < Om1
  · obtain ⟨m, hm, hT⟩ := exists_next hτ h1
    have hmu : m = u := hm.unique hn
    have hu1 : u < Om1 := next_lt_Om1 hn (Or.inr hτ) h1
    have hcT : c ∈ Tset τ := (hT c (hcu.trans hu1)).2 (hmu ▸ hcu)
    have hP : ↑(Par τ c) ⊆ Set.Iio τ := Par_sub (upsPt_inE hτ) h1 hcT
    set s := (Par τ c).sup id with hs
    have hsl : s < τ := by
      rcases (Par τ c).eq_empty_or_nonempty with he | hne
      · have : s = ⊥ := by rw [hs, he]; rfl
        rw [this]; exact hτ.1
      · obtain ⟨p, hp, hpe⟩ := Finset.exists_mem_eq_sup (Par τ c) hne id
        rw [hs, hpe]; exact hP hp
    have hτl : IsSuccLimit τ := by
      have hE : InE τ := upsPt_inE hτ
      have : IsSuccLimit (ω ^ τ) := isSuccLimit_opow_left isSuccLimit_omega0 hτ.1.ne'
      unfold InE at hE; rwa [hE] at this
    refine ⟨s + 1, hτl.add_one_lt hsl, fun σ hσ _ => ⟨hcT, fun p hp => ?_⟩⟩
    have : p ≤ s := Finset.le_sup (f := id) hp
    exact lt_of_lt_of_le (Order.lt_add_one_iff.2 this) hσ
  · exact ⟨0, hτ.1, fun σ _ hB => absurd hB.2.2.2 h1⟩

/-- **`p ∈ [σ, τ)` is not in `Tᵗ[σ]`.** -/
theorem skSX_notTB {σ τ p : Ordinal.{0}} (hB : Bases σ τ) (hσp : σ ≤ p) (hpτ : p < τ) : p ∉ TB τ σ :=
  fun h => absurd ((TB_inter_lt hB hpτ).1 h) (not_lt.2 hσp)

theorem skSX_cdExp_le {x : Ordinal.{0}} (hx : x ≠ 0) : cdExp x ≤ x :=
  (right_le_opow _ one_lt_omega0).trans (le_of_dvd hx (cdExp_dvd hx))

/-- **The exponent clause of `SkMapP` bounds `π(m z)` by `λ`.** -/
theorem skSX_offMap_pi {l μ B : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}}
    (hB : μ + B ≤ l) (hO : Sl.SlOff f Os B) {z : Ordinal.{0}} (hz : z ∈ Os) (hz0 : 0 < z)
    (hc : pi (upsilon μ) (upsilon l) (cdOff (cdExp z)) ≤ cdOff (cdExp (f z))) :
    pi (upsilon μ) (upsilon l) (cdOff (cdExp z)) < l := by
  have hf0 : f 0 < f z := by
    have := hO.mono (Finset.mem_coe.2 (Finset.mem_insert_self 0 Os))
      (Finset.mem_coe.2 (Finset.mem_insert_of_mem hz)) hz0
    exact this
  rw [hO.zero] at hf0
  calc pi (upsilon μ) (upsilon l) (cdOff (cdExp z)) ≤ cdOff (cdExp (f z)) := hc
    _ ≤ cdExp (f z) := cdOff_le _
    _ ≤ f z := skSX_cdExp_le hf0.ne'
    _ < B := hO.bd z hz
    _ ≤ μ + B := le_add_self
    _ ≤ l := hB

theorem skSX_cdExp_opow {a : Ordinal.{0}} : cdExp (ω ^ a) = a := by
  have h0 : (ω : Ordinal.{0}) ^ a ≠ 0 := (opow_pos a omega0_pos).ne'
  refine cdExp_eq h0 dvd_rfl fun h => ?_
  have h1 := le_of_dvd h0 h
  exact absurd h1 (not_le.2 ((opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_one a)))

/-- **At `z = ω^{υ_μ}` the exponent clause asks `π_{υ_μ,υ_λ}(υ_μ) < λ`**, where `υ_μ ∉ T^{υ_λ}[υ_μ]`. -/
theorem skSX_offMap_free {l μ B : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}}
    (hB : μ + B ≤ l) (hO : Sl.SlOff f Os B) (hz : ω ^ upsilon μ ∈ Os) (hω : ω ≤ upsilon μ)
    (hc : pi (upsilon μ) (upsilon l) (cdOff (cdExp (ω ^ upsilon μ))) ≤ cdOff (cdExp (f (ω ^ upsilon μ))))
    (hBs : Bases (upsilon μ) (upsilon l)) :
    pi (upsilon μ) (upsilon l) (upsilon μ) < l ∧ upsilon μ ∉ TB (upsilon l) (upsilon μ) := by
  have hoff : cdOff (cdExp (ω ^ upsilon μ)) = upsilon μ := by
    rw [skSX_cdExp_opow]; unfold cdOff; rw [if_neg (not_lt.2 hω)]
  have h := skSX_offMap_pi hB hO hz (opow_pos _ omega0_pos) hc
  rw [hoff] at h
  exact ⟨h, skSX_notTB hBs le_rfl hBs.2.2.1⟩

/-- **The image clause of `Vr.VrCarry` at `E = lo p + D`**: for every `p < υ_λ`,
`π_{υ_μ,υ_λ}(p) + img D ≤ r(μ + f g)`. -/
theorem skSX_img_pi {l β μ g : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}}
    (hlE : InE (upsilon l)) (hg0 : 0 < g)
    (hI : ∀ E : Vr.VrE, Vr.VrWF l β E → Vr.vrVal l E = cdR S (l + g) → Vr.VrOs l Os E →
      Vr.vrImg l μ f E ≤ cdR S (μ + f g))
    (D : Vr.VrE) (hD : Vr.VrWF l β D) (hDv : Vr.vrVal l D = cdR S (l + g)) (hDo : Vr.VrOs l Os D)
    {p : Ordinal.{0}} (hp : p < upsilon l) :
    pi (upsilon μ) (upsilon l) p + Vr.vrImg l μ f D ≤ cdR S (μ + f g) := by
  have hm := upsilon_normal.strictMono
  have hlt : upsilon l ≤ cdR S (l + g) :=
    (hm (lt_add_of_pos_right l hg0)).le.trans (cdRho_lt_R S (l + g)).le
  have habs : p + cdR S (l + g) = cdR S (l + g) := by
    have hp' : p < ω ^ upsilon l := by unfold InE at hlE; rw [hlE]; exact hp
    exact Ordinal.add_of_omega0_opow_le hp' (by unfold InE at hlE; rw [hlE]; exact hlt)
  have hWF : Vr.VrWF l β (.add (.lo p) D) :=
    ⟨hp.trans (hm (lt_succ l)), hD⟩
  have hv : Vr.vrVal l (.add (.lo p) D) = cdR S (l + g) := by
    show p + Vr.vrVal l D = _
    rw [hDv, habs]
  exact hI _ hWF hv ⟨trivial, hDo⟩

/-- **`Vr.VrSup` itself (hence `Vr.VrVisGen`, the `h0` / `hn` of `Wd.wdRoadL`) asks bounds on `π_{υ_μ,υ_λ}` at
every `p < υ_λ`**, including `p ∈ [υ_μ, υ_λ)` where `π_{υ_μ,υ_λ}(p)` is not fixed by any axiom (`skSX_notTB`). -/
theorem skSX_sup_pi {l β g : Ordinal.{0}} (hlE : InE (upsilon l)) (hg0 : 0 < g) (hgd : ω ^ 2 ∣ g)
    (hsup : Vr.VrSup S l β) {Os : Finset Ordinal.{0}} (hOs : ∀ d ∈ Os, d < β) (hg : g ∈ Os)
    (D : Vr.VrE) (hD : Vr.VrWF l β D) (hDv : Vr.vrVal l D = cdR S (l + g)) (hDo : Vr.VrOs l Os D)
    {γ : Ordinal.{0}} (hγ : γ < upsilon l) :
    ∃ μ f, γ < upsilon μ ∧ upsilon μ < upsilon l ∧
      ∀ p < upsilon l, pi (upsilon μ) (upsilon l) p + Vr.vrImg l μ f D ≤ cdR S (μ + f g) := by
  obtain ⟨μ, f, B, -, h1, h2, -, -, -, -, hC⟩ := hsup γ hγ Os hOs
  refine ⟨μ, f, h1, h2, fun p hp => ?_⟩
  exact skSX_img_pi hlE hg0 (fun E hE hv ho => (hC g hg hg0 hgd).2.2 E hE hv ho) D hD hDv hDo hp

end R2Skel.SkSX

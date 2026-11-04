import Googology.Trans.PoR.InaccPsi.R2.ZaTr
import Googology.Trans.PoR.InaccPsi.R2.XjFrag

/-!
# The moving-level node for FRAG: the segment move, and the composed level of the FRAG step

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`mv b c` the segment move (`π_{c,b}`, `π⁻¹_{b,c}` or the identity), `θ = ConjT.th S`, `B₂ = Uc.ucB`, `Γ₀ = gamma 0`.

* `za_lt_next` (**a countable point of `Tᵗ` lies below every `υ`-point above `τ`**, `R2.T_inter_Om1`);
* `za_mv_node` (**the base case of FRAG at a moving level `B₂ ≤ q`**: `yvSub (mv b c) (Ω₁·q) = Ω₁·q'` with `B₂ ≤
  q'`, substitutions compose after `mv b c`, the leaves move, the argument stays in `T^c`, and `mv b c
  (ϑ^b(Ω₁·q + ρ)) = ϑ^c(Ω₁·q' + mv b c ρ)`);
* `za_lev_comp` (**the step of FRAG at a moving level**: for `Ψ = π⁻¹_{γ,t'} ∘ Ψ' ∘ π_{β,t}`, if `Ψ'` moves the
  compressed level `π(Ω₁·q) = Ω₁·q₁` to `Ω₁·q₂` with composition and leaf transfer, and `π⁻¹(Ω₁·q₂) = Ω₁·q₃`, then
  `yvSub Ψ (Ω₁·q) = Ω₁·q₃` with composition and leaf transfer).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Za

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Yv

variable {S : InaccSeq.{0}}

/-- **A countable point of `Tᵗ` lies below every `υ`-point above `τ`.** -/
theorem za_lt_next {τ x u : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hx : x ∈ Tset τ) (hx1 : x < Om1)
    (hτu : τ < u) (hu : UpsPt u) : x < u := by
  obtain ⟨m, -, -, hmin, hT⟩ := T_inter_Om1 hτ hτ1
  exact ((hT x hx1).1 hx).trans_le (hmin u hτu hu.2)

/-- **The segment move at a node with a moving level `Ω₁·q ≥ B₂`** (the base case of FRAG). -/
theorem za_mv_node {κ b c q ρ : Ordinal.{0}} (hBκ : Bases κ b) (hc : InE c) (hc1 : c < Om1) (hκc : κ ≤ c)
    (hbΓ : gamma 0 ≤ b) (hcΓ : gamma 0 ≤ c) (hq1 : 1 ≤ q) (hqB : Uc.ucB ≤ q) (hqθ : Om1 * q < ConjT.th S)
    (hL : YvLv S (· ∈ TB b κ) (Om1 * q)) (hρ : ρ ∈ TB b κ) (hρ1 : ρ < Om1) :
    ∃ q', yvSub S (mv b c) (Om1 * q) = Om1 * q' ∧ 1 ≤ q' ∧ Uc.ucB ≤ q' ∧ Om1 * q' < ConjT.th S ∧
      (∀ f : Ordinal.{0} → Ordinal.{0},
        yvSub S f (yvSub S (mv b c) (Om1 * q)) = yvSub S (fun x => f (mv b c x)) (Om1 * q)) ∧
      (∀ P : Ordinal.{0} → Prop,
        YvLv S P (yvSub S (mv b c) (Om1 * q)) ↔ YvLv S (fun x => P (mv b c x)) (Om1 * q)) ∧
      Om1 * q' + mv b c ρ ∈ Tset c ∧ mv b c (vt b (Om1 * q + ρ)) = vt c (Om1 * q' + mv b c ρ) := by
  have hb := hBκ.2.1
  have hb1 := hBκ.2.2.2
  have hΓT : Om1 * q ∈ TB b κ := (yv_TB_iff hBκ hqθ).2 hL
  have h2 : Om1 * q + ρ < OmTwo :=
    ((Xe.xe_th S).1.add_lt hqθ (hρ1.trans (Xe.xe_th S).2.1)).trans (Xe.xe_th S).2.2
  have hq2 : Om1 * q < OmTwo := hqθ.trans (Xe.xe_th S).2.2
  obtain ⟨s1, -⟩ := pi_add hBκ hΓT hρ
  unfold mv
  rcases lt_trichotomy c b with hcb | rfl | hbc
  · rw [if_pos hcb]
    have hB : Bases c b := ⟨hc, hb, hcb, hb1⟩
    have hL' : YvLv S (· ∈ TB b c) (Om1 * q) := hL.mono fun x hx => Ub.ub_TB_mono hκc hx
    have hΓT' : Om1 * q ∈ TB b c := (yv_TB_iff hB hqθ).2 hL'
    have hρ' : ρ ∈ TB b c := Ub.ub_TB_mono hκc hρ
    obtain ⟨q', e, h1, hθ', hs, hBq⟩ := za_pi_level hB hcΓ hq1 hqθ hΓT'
    obtain ⟨c1, c2⟩ := pi_add hB hΓT' hρ'
    refine ⟨q', hs.symm.trans e, h1, hBq hqB, hθ', fun f => ?_, fun P => ?_, ?_, ?_⟩
    · rw [← hs]; exact yv_comp_sub hB hcΓ f hqθ hL' (yvR_ex _ hL')
    · rw [← hs]; exact za_lv_pi_th hB hcΓ hqθ hΓT' P
    · rw [← e, ← c2]; exact (pi_bijOn hB).1.mapsTo c1
    · rw [pi_vt_two hB c1 h2, c2, e]
  · rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _)]
    obtain ⟨r, hG, hr⟩ := yv_bound (S := S) hqθ
    have hid : yvSub S id (Om1 * q) = Om1 * q := yvSub_eq (yv_sub_id r _ hL hG hr)
    refine ⟨q, hid, hq1, hqB, hqθ, fun f => by rw [hid]; rfl, fun P => by rw [hid]; rfl, s1.1, rfl⟩
  · rw [if_neg (not_lt.2 hbc.le), if_pos hbc]
    have hB : Bases b c := ⟨hb, hc, hbc, hc1⟩
    obtain ⟨hGT, -, hsumTB, -, hnode, -⟩ := za_node_up S hB hbΓ hq1 hq2 s1.1 hρ1
    obtain ⟨q', e, h1, hθ', -, -, hBq⟩ := za_up_level (S := S) hB hbΓ hq1 hGT hq2
    obtain ⟨hsub, hcomp⟩ := za_sub_up (S := S) hB hbΓ hGT hq2
    refine ⟨q', hsub.trans e, h1, hBq hqB, hθ', fun f => by rw [hsub]; exact hcomp f,
      fun P => by rw [hsub]; exact za_lv_up hB hbΓ hGT hq2 P, ?_, ?_⟩
    · rw [← e]; exact hsumTB.1
    · rw [hnode, e]

/-- **The level of the FRAG step**: `Ψ = π⁻¹_{γ,t'} ∘ Ψ' ∘ π_{β,t}` at a level `Ω₁·q` with leaves in `Tᵗ[β]`. -/
theorem za_lev_comp {β t γ t' q q₁ q₂ q₃ : Ordinal.{0}} {Ψ' : Ordinal.{0} → Ordinal.{0}} (hβ : Bases β t)
    (hβΓ : gamma 0 ≤ β) (hγ : Bases γ t') (hγΓ : gamma 0 ≤ γ) (hqθ : Om1 * q < ConjT.th S)
    (hL : YvLv S (· ∈ TB t β) (Om1 * q)) (eq₁ : pi β t (Om1 * q) = Om1 * q₁)
    (e₂ : yvSub S Ψ' (Om1 * q₁) = Om1 * q₂)
    (hcomp₂ : ∀ f : Ordinal.{0} → Ordinal.{0},
      yvSub S f (yvSub S Ψ' (Om1 * q₁)) = yvSub S (fun x => f (Ψ' x)) (Om1 * q₁))
    (hleaf₂ : ∀ P : Ordinal.{0} → Prop,
      YvLv S P (yvSub S Ψ' (Om1 * q₁)) ↔ YvLv S (fun x => P (Ψ' x)) (Om1 * q₁))
    (hG : Om1 * q₂ ∈ Tset γ) (hG2 : Om1 * q₂ < OmTwo) (e₃ : up γ t' (Om1 * q₂) = Om1 * q₃) :
    yvSub S (fun x => up γ t' (Ψ' (pi β t x))) (Om1 * q) = Om1 * q₃ ∧
      (∀ f : Ordinal.{0} → Ordinal.{0}, yvSub S f (yvSub S (fun x => up γ t' (Ψ' (pi β t x))) (Om1 * q)) =
        yvSub S (fun x => f (up γ t' (Ψ' (pi β t x)))) (Om1 * q)) ∧
      (∀ P : Ordinal.{0} → Prop, YvLv S P (yvSub S (fun x => up γ t' (Ψ' (pi β t x))) (Om1 * q)) ↔
        YvLv S (fun x => P (up γ t' (Ψ' (pi β t x)))) (Om1 * q)) := by
  have hΓT : Om1 * q ∈ TB t β := (yv_TB_iff hβ hqθ).2 hL
  obtain ⟨hsubU, hcompU⟩ := za_sub_up (S := S) hγ hγΓ hG hG2
  have hsubΨ : yvSub S (fun x => up γ t' (Ψ' (pi β t x))) (Om1 * q) = Om1 * q₃ := by
    calc yvSub S (fun x => up γ t' (Ψ' (pi β t x))) (Om1 * q)
        = yvSub S (fun y => up γ t' (Ψ' y)) (pi β t (Om1 * q)) :=
          (yv_comp_sub hβ hβΓ (fun y => up γ t' (Ψ' y)) hqθ hL (yvR_ex _ hL)).symm
      _ = yvSub S (fun y => up γ t' (Ψ' y)) (Om1 * q₁) := by rw [eq₁]
      _ = yvSub S (up γ t') (yvSub S Ψ' (Om1 * q₁)) := (hcomp₂ (up γ t')).symm
      _ = yvSub S (up γ t') (Om1 * q₂) := by rw [e₂]
      _ = Om1 * q₃ := by rw [hsubU, e₃]
  refine ⟨hsubΨ, fun f => ?_, fun P => ?_⟩
  · rw [hsubΨ, ← e₃, hcompU f, ← e₂, hcomp₂ (fun x => f (up γ t' x)), ← eq₁]
    exact yv_comp_sub hβ hβΓ (fun y => f (up γ t' (Ψ' y))) hqθ hL (yvR_ex _ hL)
  · rw [hsubΨ, ← e₃, za_lv_up hγ hγΓ hG hG2 P, ← e₂, hleaf₂ (fun x => P (up γ t' x)), ← eq₁]
    exact za_lv_pi_th hβ hβΓ hqθ hΓT (fun y => P (up γ t' (Ψ' y)))

end Googology.Trans.PoR.InaccPsi.R2.Za

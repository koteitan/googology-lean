import Googology.Trans.PoR.InaccPsi.R2.TrLow

/-!
# The carry through the compression point: reduction to one statement per segment pair

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

In the induction step of Theorem FRAG (`R2.soFrag_step`) the top segment `seg(b)` is compressed by `π_{β,b}`
into `seg(b')` (`β = ϑ^{b'}(Δ_M) = Dl b' M`, the previous base `b' < b`), moved there by the map of the
induction hypothesis, and expanded by `π_{γ,c}⁻¹` (`γ` the image of `β`).  If the induction hypothesis is
`mv b' c'` on the low-parameter points of `seg(b')`, the composite on a low-parameter point `x ∈ seg(b)` of
height `≤ M` is `mv b c x` **iff** `mv b' c' ∘ π_{β,b} = π_{γ,c} ∘ mv b c` there.  Here:

* `trHt_mv` (`mv b c` keeps the height), `trPi_image_ht` (`π_{σ,τ}` maps `{x ∈ Tᵗ[ρ] | τ ≤ x < Ω₁, htᵗ x ≤ M}`
  onto the same set over `σ`), `trMv_image_ht`;
* `trDl_pi` (**`π_{σ,τ}(ϑᵗ(Δₙ)) = ϑ^σ(Δₙ)`**, `n ≥ 1`, from [W07a] Lemma 3.27 and 5.3 (e)), `trMv_Dl`;
* `trParDown` ([W07a] Lemma 6.10 at `X = κ`: a point `y ∈ T^β[κ]` with `β ≤ y < Ω₁`, `ht^β y ≤ M` lies in
  `T^{b'}[κ] ∩ seg(b')`);
* `TrInner κ b' c' M` (**the one missing statement per segment pair**: `mv b' c'` maps `T^β[κ] ∩ [β, Ω₁)` (height
  `≤ M`) onto `T^γ[κ] ∩ [γ, Ω₁)` (height `≤ M`), `β = Dl b' M`, `γ = Dl c' M`);
* `trComm_of_inner`, `trInner_of_comm`, `trComm_iff_inner` (**`TrInner` iff `mv b' c' ∘ π_{β,b} = π_{γ,c} ∘ mv b c`
  on the low-parameter points of `seg(b)` of height `≤ M`**), `trCarry_of_inner` (the composite of the FRAG step,
  `π_{γ,c}⁻¹ ∘ mv b' c' ∘ π_{β,b}`, is `mv b c` there).

No new axiom.  New definition: `TrInner` (a statement).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Googology.Trans.PoR.InaccPsi.R2.Tr

open Ordinal Set Googology.Trans.PoR.InaccPsi.R2

/-- The low-parameter points of `T^τ[ρ]` in `[τ, Ω₁)` of height `≤ M`. -/
def TrTop (τ ρ : Ordinal.{0}) (M : ℕ) : Set Ordinal.{0} :=
  {x | x ∈ TB τ ρ ∧ τ ≤ x ∧ x < Om1 ∧ ht τ x ≤ M}

/-- `π_{σ,τ}` maps `TrTop τ ρ M` onto `TrTop σ ρ M`. -/
theorem trPi_image_ht {ρ σ τ : Ordinal.{0}} (h : Bases σ τ) (hρ : ρ ≤ σ) (M : ℕ) :
    pi σ τ '' TrTop τ ρ M = TrTop σ ρ M := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hτx, hx1, hxM⟩, rfl⟩
    have hx' := trTB_mono hρ hx
    exact ⟨trPi_TB h hρ hx, down_ge h hx' hτx, down_lt_Om1 h hx' hx1, by
      rw [(pi_ht_Par h hx').1]; exact hxM⟩
  · rintro ⟨hy, hσy, hy1, hyM⟩
    obtain ⟨hu, hpu⟩ := up_spec h hy.1
    refine ⟨up σ τ y, ⟨trUp_TB h hy, up_ge h hy.1 hσy, up_lt_Om1 h hy.1 hy1, ?_⟩, hpu⟩
    have := (pi_ht_Par h hu).1
    rw [hpu] at this; rw [← this]; exact hyM

section Pair

variable {κ b c : Ordinal.{0}} (hb : UpsPt b) (hb1 : b < Om1) (hc : UpsPt c) (hc1 : c < Om1)
  (hκb : κ < b) (hκc : κ < c)
include hb hb1 hc hc1 hκb hκc

/-- `mv b c` keeps the height on `Tᵇ[κ] ∩ Ω₁`. -/
theorem trHt_mv {x : Ordinal.{0}} (hx : x ∈ TrLowT b κ) : ht c (mv b c x) = ht b x := by
  rcases trMv_cases hb1 hc1 hb hc with ⟨h, hB, e⟩ | ⟨rfl, e⟩ | ⟨h, hB, e⟩ <;> rw [e]
  · exact (pi_ht_Par hB (trTB_mono hκc.le hx.1)).1
  · rfl
  · have hs := up_spec hB hx.1.1
    have := (pi_ht_Par hB hs.1).1
    rw [hs.2] at this; exact this.symm

/-- `mv b c` maps `TrTop b κ M` onto `TrTop c κ M`. -/
theorem trMv_image_ht (M : ℕ) : mv b c '' TrTop b κ M = TrTop c κ M := by
  ext w
  constructor
  · rintro ⟨x, ⟨hx, hbx, hx1, hxM⟩, rfl⟩
    have hL : x ∈ TrLowT b κ := ⟨hx, hx1⟩
    have hm := trMv_maps hb hb1 hc hc1 hκb hκc hL
    exact ⟨hm.1, trMv_ge hb hb1 hc hc1 hκb hκc hL hbx, hm.2, by
      rw [trHt_mv hb hb1 hc hc1 hκb hκc hL]; exact hxM⟩
  · rintro ⟨hw, hcw, hw1, hwM⟩
    have hL : w ∈ TrLowT c κ := ⟨hw, hw1⟩
    have hm := trMv_maps hc hc1 hb hb1 hκc hκb hL
    refine ⟨mv c b w, ⟨hm.1, trMv_ge hc hc1 hb hb1 hκc hκb hL hcw, hm.2, ?_⟩,
      trMv_inv hc hc1 hb hb1 hκc hκb hL⟩
    rw [trHt_mv hc hc1 hb hb1 hκc hκb hL]; exact hwM

end Pair

/-- **`π_{σ,τ}(ϑᵗ(Δₙ)) = ϑ^σ(Δₙ)`** for `n ≥ 1`. -/
theorem trDl_pi {σ τ : Ordinal.{0}} (h : Bases σ τ) {n : ℕ} (hn : 1 ≤ n) :
    Dl τ n ∈ TB τ σ ∧ pi σ τ (Dl τ n) = Dl σ n := by
  have hσ1 : σ < Om1 := h.2.2.1.trans h.2.2.2
  obtain ⟨hDT, hD1, hDh⟩ := Dl_spec h.2.1 h.2.2.2 n
  obtain ⟨hET, hE1, hEh⟩ := Dl_spec h.1 hσ1 n
  have hP := (Dl_E h.2.1 h.2.2.2 hn).2.2
  have hDTB : Dl τ n ∈ TB τ σ := ⟨hDT, fun p hp => by
    have := hP hp
    rw [Set.mem_singleton_iff] at this
    rw [this]; exact InE.pos h.1⟩
  refine ⟨hDTB, ?_⟩
  -- `x < Dl τ n ↔ ht x ≤ n`
  have key : ∀ {ρ x : Ordinal.{0}}, InE ρ → ρ < Om1 → x ∈ Tset ρ → x < Om1 → x < Dl ρ n →
      ht ρ x ≤ n := by
    intro ρ x hρ hρ1 hxT hx1 hlt
    rw [(ht_spec hρ hρ1 hxT hx1).2]
    exact Nat.sInf_le hlt
  set w := pi σ τ (Dl τ n) with hw
  have hwT : w ∈ Tset σ := (pi_bijOn h).1.mapsTo hDTB
  have hw1 : w < Om1 := down_lt_Om1 h hDTB hD1
  have hwh : ht σ w = n + 1 := by rw [hw, (pi_ht_Par h hDTB).1, hDh]
  have h1 : Dl σ n ≤ w := by
    by_contra hlt
    have := key h.1 hσ1 hwT hw1 (not_le.1 hlt)
    omega
  obtain ⟨huT, hpu⟩ := up_spec h hET
  have hu1 : up σ τ (Dl σ n) < Om1 := up_lt_Om1 h hET hE1
  have huh : ht τ (up σ τ (Dl σ n)) = n + 1 := by
    have := (pi_ht_Par h huT).1
    rw [hpu, hEh] at this; exact this.symm
  have h2 : Dl τ n ≤ up σ τ (Dl σ n) := by
    by_contra hlt
    have := key h.2.1 h.2.2.2 huT.1 hu1 (not_le.1 hlt)
    omega
  have h3 : w ≤ Dl σ n := by
    have := (pi_bijOn h).2.monotoneOn hDTB huT h2
    rwa [hpu] at this
  exact le_antisymm h3 h1

/-- `mv b c (ϑᵇ(Δₙ)) = ϑᶜ(Δₙ)` for `n ≥ 1`. -/
theorem trMv_Dl {b c : Ordinal.{0}} (hb : UpsPt b) (hb1 : b < Om1) (hc : UpsPt c) (hc1 : c < Om1)
    {n : ℕ} (hn : 1 ≤ n) : mv b c (Dl b n) = Dl c n := by
  rcases trMv_cases hb1 hc1 hb hc with ⟨h, hB, e⟩ | ⟨rfl, e⟩ | ⟨h, hB, e⟩ <;> rw [e]
  · exact (trDl_pi hB hn).2
  · rfl
  · obtain ⟨hT, hp⟩ := trDl_pi hB hn
    rw [← hp, up_pi hB hT]

/-- **[W07a] Lemma 6.10 at `X = κ`**: a point of `T^β[κ]` (`β = ϑ^{b}(Δ_M)`) in `[β, Ω₁)` of height `≤ M` is a
low-parameter point of `seg(b)`. -/
theorem trParDown {κ b : Ordinal.{0}} (hκ : InE κ) (hb : UpsPt b) (hb1 : b < Om1) (hκb : κ < b) {M : ℕ}
    (hM : 1 ≤ M) {y : Ordinal.{0}} (hy : y ∈ TrTop (Dl b M) κ M) : y ∈ TrLowT b κ ∧ InSeg b y := by
  obtain ⟨hyT, hβy, hy1, hyM⟩ := hy
  have hbE := upsPt_inE hb
  obtain ⟨hbβ, hβE, hβP⟩ := Dl_E hbE hb1 hM
  obtain ⟨-, hβ1, -⟩ := Dl_spec hbE hb1 M
  obtain ⟨hDpT, hDp1, hDpeq⟩ := Dp_spec hbE hb1 hM
  have hyDp : y < Dp b M := by
    rw [hDpeq]; exact lt_Dl_of_ht hβE hβ1 hyT.1 hy1 hyM
  have hP := par_track hbE hb1 hM hyT.1 hβy hyDp (X := Set.Iio κ)
    (fun x hx => (show x < κ from hx).trans (hκb.trans hbβ)) (InE.pos hκ) (DC_Iio κ)
    (fun ξ hξ => by
      rw [Par_lt hbE hb1 ((show ξ < κ from hξ).trans hκb)]
      intro p hp
      rw [Finset.coe_singleton, Set.mem_singleton_iff] at hp
      rw [hp]; exact ClS.sub _ ⟨hξ, (show ξ < κ from hξ).trans hκb⟩)
    (fun p hp => by
      have := hβP hp
      rw [Set.mem_singleton_iff] at this
      rw [this]; exact ClS.sub _ ⟨InE.pos hκ, (InE.pos hκ).trans hκb⟩)
    (hyT.2.trans (ClS.sub _))
  have hP' : ↑(Par b y) ⊆ Set.Iio κ := hP.trans (ClS.lt_of_E hκ Set.inter_subset_left)
  obtain ⟨m, -, -, -, hT, -⟩ := T_next (Or.inr hbE) hb1
  have hyb : y ∈ Tset b := (hT y hy1).2 (hyDp.trans ((hT _ hDp1).1 hDpT))
  exact ⟨⟨⟨hyb, hP'⟩, hy1⟩, (inSeg_iff hb hb1).2 ⟨(hbβ.trans_le hβy).le, hy1, hyb⟩⟩

/-- **The missing statement per segment pair**: `mv b c` maps the low-parameter points of `T^{ϑᵇ(Δ_M)}` in
`[ϑᵇ(Δ_M), Ω₁)` of height `≤ M` onto those of `T^{ϑᶜ(Δ_M)}`. -/
def TrInner (κ b c : Ordinal.{0}) (M : ℕ) : Prop :=
  mv b c '' TrTop (Dl b M) κ M = TrTop (Dl c M) κ M

/-- The base `β = ϑ^{b'}(Δ_M)` lies in `seg(b')`, below `b`. -/
private theorem trBeta {b b' : Ordinal.{0}} (hb' : UpsPt b') (hb1 : b < Om1) (hb : UpsPt b) (hb'b : b' < b) {M : ℕ}
    (hM : 1 ≤ M) : Bases (Dl b' M) b ∧ b' < Dl b' M := by
  have hb'1 := hb'b.trans hb1
  have hE := upsPt_inE hb'
  obtain ⟨hbβ, hβE, -⟩ := Dl_E hE hb'1 hM
  obtain ⟨hβT, hβ1, -⟩ := Dl_spec hE hb'1 M
  have hs : InSeg b' (Dl b' M) := (inSeg_iff hb' hb'1).2 ⟨hbβ.le, hβ1, hβT⟩
  exact ⟨⟨hβE, upsPt_inE hb, hs.2.2 b hb'b hb, hb1⟩, hbβ⟩

section Comm

variable {κ b c b' c' : Ordinal.{0}} (hκ : InE κ) (hb : UpsPt b) (hb1 : b < Om1) (hc : UpsPt c)
  (hc1 : c < Om1) (hb' : UpsPt b') (hc' : UpsPt c') (hb'b : b' < b) (hc'c : c' < c) (hκb' : κ < b')
  (hκc' : κ < c') {M : ℕ} (hM : 1 ≤ M)
include hκ hb hb1 hc hc1 hb' hc' hb'b hc'c hκb' hκc' hM

/-- **The commutation from `TrInner`.** -/
theorem trComm_of_inner (hI : TrInner κ b' c' M) {x : Ordinal.{0}} (hx : x ∈ TrTop b κ M) :
    mv b' c' (pi (Dl b' M) b x) = pi (Dl c' M) c (mv b c x) := by
  obtain ⟨hBβ, hb'β⟩ := trBeta hb' hb1 hb hb'b hM
  obtain ⟨hBγ, hc'γ⟩ := trBeta hc' hc1 hc hc'c hM
  have hb'1 := hb'b.trans hb1
  have hc'1 := hc'c.trans hc1
  have hκb := hκb'.trans hb'b
  have hκc := hκc'.trans hc'c
  have hκβ := hκb'.trans hb'β
  have hκγ := hκc'.trans hc'γ
  have hpiβ := trPi_image_ht hBβ hκβ.le M
  have hpiγ := trPi_image_ht hBγ hκγ.le M
  refine trEqOn_of_image (A := TrTop b κ M) (f := fun u => mv b' c' (pi (Dl b' M) b u))
    (g := fun u => pi (Dl c' M) c (mv b c u)) ?_ ?_ ?_ hx
  · intro u hu v hv huv
    have hu' : pi (Dl b' M) b u ∈ TrTop (Dl b' M) κ M := hpiβ ▸ ⟨u, hu, rfl⟩
    have hv' : pi (Dl b' M) b v ∈ TrTop (Dl b' M) κ M := hpiβ ▸ ⟨v, hv, rfl⟩
    exact trMv_mono hb' hb'1 hc' hc'1 hκb' hκc' (trParDown hκ hb' hb'1 hκb' hM hu').1
      (trParDown hκ hb' hb'1 hκb' hM hv').1
      ((pi_bijOn hBβ).2 (trTB_mono hκβ.le hu.1) (trTB_mono hκβ.le hv.1) huv)
  · intro u hu v hv huv
    have hu' : mv b c u ∈ TrTop c κ M := (trMv_image_ht hb hb1 hc hc1 hκb hκc M) ▸ ⟨u, hu, rfl⟩
    have hv' : mv b c v ∈ TrTop c κ M := (trMv_image_ht hb hb1 hc hc1 hκb hκc M) ▸ ⟨v, hv, rfl⟩
    exact (pi_bijOn hBγ).2 (trTB_mono hκγ.le hu'.1) (trTB_mono hκγ.le hv'.1)
      (trMv_mono hb hb1 hc hc1 hκb hκc ⟨hu.1, hu.2.2.1⟩ ⟨hv.1, hv.2.2.1⟩ huv)
  · rw [show (fun u => mv b' c' (pi (Dl b' M) b u)) = mv b' c' ∘ pi (Dl b' M) b from rfl,
      show (fun u => pi (Dl c' M) c (mv b c u)) = pi (Dl c' M) c ∘ mv b c from rfl,
      Set.image_comp, Set.image_comp, hpiβ, trMv_image_ht hb hb1 hc hc1 hκb hκc M, hpiγ]
    exact hI

/-- **`TrInner` from the commutation.** -/
theorem trInner_of_comm
    (h : ∀ x ∈ TrTop b κ M, mv b' c' (pi (Dl b' M) b x) = pi (Dl c' M) c (mv b c x)) :
    TrInner κ b' c' M := by
  obtain ⟨hBβ, hb'β⟩ := trBeta hb' hb1 hb hb'b hM
  obtain ⟨hBγ, hc'γ⟩ := trBeta hc' hc1 hc hc'c hM
  have hκb := hκb'.trans hb'b
  have hκc := hκc'.trans hc'c
  unfold TrInner
  rw [← trPi_image_ht hBβ (hκb'.trans hb'β).le M, ← trPi_image_ht hBγ (hκc'.trans hc'γ).le M,
    ← trMv_image_ht hb hb1 hc hc1 hκb hκc M, ← Set.image_comp, ← Set.image_comp]
  exact Set.image_congr fun x hx => h x hx

/-- **`TrInner` iff the commutation `mv b' c' ∘ π_{β,b} = π_{γ,c} ∘ mv b c` on `TrTop b κ M`.** -/
theorem trComm_iff_inner :
    TrInner κ b' c' M ↔
      ∀ x ∈ TrTop b κ M, mv b' c' (pi (Dl b' M) b x) = pi (Dl c' M) c (mv b c x) :=
  ⟨fun hI _ hx => trComm_of_inner hκ hb hb1 hc hc1 hb' hc' hb'b hc'c hκb' hκc' hM hI hx,
    trInner_of_comm hκ hb hb1 hc hc1 hb' hc' hb'b hc'c hκb' hκc' hM⟩

/-- **The carry of the FRAG step**: under `TrInner`, `π_{γ,c}⁻¹ ∘ mv b' c' ∘ π_{β,b} = mv b c` on the low-parameter
points of `seg(b)` of height `≤ M`; and `mv b' c'` sends `β` to `γ`. -/
theorem trCarry_of_inner (hI : TrInner κ b' c' M) {x : Ordinal.{0}} (hx : x ∈ TrTop b κ M) :
    up (Dl c' M) c (mv b' c' (pi (Dl b' M) b x)) = mv b c x ∧ mv b' c' (Dl b' M) = Dl c' M := by
  obtain ⟨hBγ, hc'γ⟩ := trBeta hc' hc1 hc hc'c hM
  have hκb := hκb'.trans hb'b
  have hκc := hκc'.trans hc'c
  have hm := trMv_maps hb hb1 hc hc1 hκb hκc ⟨hx.1, hx.2.2.1⟩
  refine ⟨?_, trMv_Dl hb' (hb'b.trans hb1) hc' (hc'c.trans hc1) hM⟩
  rw [trComm_of_inner hκ hb hb1 hc hc1 hb' hc' hb'b hc'c hκb' hκc' hM hI hx]
  exact up_pi hBγ (trTB_mono (hκc'.trans hc'γ).le hm.1)

end Comm

end Googology.Trans.PoR.InaccPsi.R2.Tr

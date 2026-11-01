import Googology.Trans.PoR.InaccPsi.R2.YbCov

/-!
# The level statement of the covering lemma is a statement about the notation only

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`Yb.YbLevK` asks, at a `ϑ`-node `x = ϑ^{υ_{λ+h}}(Ω₁·M + η)`, that the level `M` lies in the inacc-free closure
`Yb.YbK S x` (small members below `x`).  Here it is reduced to `YbIF S`: **every level `Ω₁ ≤ M < θ` lies in the
inacc-free closure at every strongly critical threshold `q ≤ Ω₁` above its datum** (`ucDat M` below `B₂`, the
`K⁽⁰⁾`-datum `d_S(M)` on `[B₂, θ)`).  `YbIF` does not mention restarts, reaches or realizers.

* `ybK_lower` (lowering the threshold: members of `YbK S q` are in `YbK S x` if every `y < q` is);
* `ybK_gap` (**no strongly critical point in `[x, q)` ⇒ every `y < q` is in `YbK S x`**: a non-strongly-critical
  `y ≥ x` is a sum `a + b`, a power `ω^a` or a value `φ(a, b)` of smaller ordinals, `MxLev.mxDec`);
* `ybSCnext` (the least strongly critical `q₀ ≥ x`, `q₀ ≤ Ω₁`);
* `ybLevK_of_IF` (**`YbIF S` ⇒ `YbLevK S λ β`** for `0 < λ`, `υ_{λ+β} ≤ Ω₁`: the datum of a level is below every
  strongly critical `q ≥ x` (`CitedVd.vdLevel_lt`, `vdArg_dat`, `CitedUz.uzTBound`), so `M ∈ YbK S q₀` and then
  `M ∈ YbK S x`);
* `ybCover_IF` (**the covering lemma under `YbIF` alone**).

No new axiom.  New definition: `YbIF` (a statement).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

/-- **The inacc-free level statement**: every level `Ω₁ ≤ M < θ` is in the inacc-free closure `YbK S q` at every
strongly critical `q ≤ Ω₁` above its datum. -/
def YbIF (S : InaccSeq.{0}) : Prop :=
  ∀ M q : Ordinal.{0}, Om1 ≤ M → M < ConjT.th S → SC q → q ≤ Om1 →
    (M < Uc.ucB → Uc.ucDat M < q) → (Uc.ucB ≤ M → Vd.vdD S 0 M < q) → YbK S q M

variable {S : InaccSeq.{0}}

/-- **Lowering the threshold.** -/
theorem ybK_lower {x q : Ordinal.{0}} (hy : ∀ y, y < q → YbK S x y) : ∀ M, YbK S q M → YbK S x M := by
  intro M hM
  induction hM with
  | small h => exact hy _ h
  | fix hv => exact .fix hv
  | add _ _ ih1 ih2 => exact .add ih1 ih2
  | phi _ _ ih1 ih2 => exact .phi ih1 ih2
  | om _ ih => exact .om ih
  | coll hπ hπ1 _ _ ihp ihe => exact .coll hπ hπ1 ihp ihe

/-- **No strongly critical point in `[x, q)`**: every `y < q` is in `YbK S x`. -/
theorem ybK_gap {x q : Ordinal.{0}} (hx0 : 0 < x) (hq : ∀ z, x ≤ z → z < q → ¬ SC z) :
    ∀ y, y < q → YbK S x y := by
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hyq
  rcases lt_or_ge y x with hyx | hxy
  · exact .small hyx
  have hnS : ¬ SC y := hq y hxy hyq
  have hy0 : 0 < y := hx0.trans_le hxy
  by_cases hI : Indec y
  · obtain ⟨a, ha⟩ : ∃ a : Ordinal.{0}, ω ^ a = y := by
      rcases isPrincipal_add_iff_zero_or_omega0_opow.1 (indec_iff.1 hI).2 with h | ⟨a, ha⟩
      · exact absurd h hI.ne_zero
      · exact ⟨a, ha⟩
    rcases lt_or_eq_of_le (show a ≤ y from ha ▸ right_le_opow a one_lt_omega0) with hay | hay
    · have h0 : YbK S x 0 := .small hx0
      have := YbK.phi h0 (IH a hay (hay.trans hyq))
      rwa [veblen_zero_apply, ha] at this
    · have hE : InE y := by
        show ω ^ y = y
        conv_lhs => rw [← hay]
        exact ha
      obtain ⟨hv, h1, h2, -⟩ := Mx.mxDec hE hy0 hnS
      have := YbK.phi (IH _ h1 (h1.trans hyq)) (IH _ h2 (h2.trans hyq))
      rwa [hv] at this
  · rcases (not_not.1 hI : DecompR0 y) with h0 | ⟨a, b, ha, hb, hab⟩
    · exact absurd h0 hy0.ne'
    · have := YbK.add (IH a ha (ha.trans hyq)) (IH b hb (hb.trans hyq))
      rwa [hab] at this

/-- `Ω₁` is strongly critical. -/
theorem yb_SC_Om1 : SC (Om1 : Ordinal.{0}) := by rw [Tw.tw_Om1_eq]; exact SC_Om one_ne_zero

/-- **The least strongly critical `q₀ ≥ x`** (`x ≤ Ω₁`). -/
theorem ybSCnext {x : Ordinal.{0}} (hx : x ≤ Om1) :
    ∃ q, SC q ∧ x ≤ q ∧ q ≤ Om1 ∧ ∀ z, x ≤ z → z < q → ¬ SC z := by
  set T := {q : Ordinal.{0} | SC q ∧ x ≤ q} with hT
  have hne : T.Nonempty := ⟨Om1, yb_SC_Om1, hx⟩
  have hmem := csInf_mem hne
  refine ⟨sInf T, hmem.1, hmem.2, csInf_le' (s := T) ⟨yb_SC_Om1, hx⟩, fun z hxz hzq hz => ?_⟩
  exact absurd (csInf_le' (s := T) ⟨hz, hxz⟩) (not_le.2 hzq)

/-- **`YbIF` gives the level statement of the covering lemma.** -/
theorem ybLevK_of_IF {l β : Ordinal.{0}} (hl0 : 0 < l) (hb1 : upsilon (l + β) ≤ Om1) (hIF : YbIF S) :
    YbLevK S l β := by
  intro h M η h0 _ hΩM hηO hηT hξT hξ2 hτx hxβ _
  set τ := upsilon (l + h) with hτdef
  set x := vt τ (Om1 * M + η) with hxdef
  have hτP : UpsPt τ := upsPt_upsilon (hl0.trans_le le_self_add)
  have hτE : InE τ := upsPt_inE hτP
  have hx1 : x < Om1 := hxβ.trans_le hb1
  have hτ1 : τ < Om1 := hτx.trans_lt hx1
  have hx0 : 0 < x := (InE.pos hτE).trans_le hτx
  have hξθ : Om1 * M + η < ConjT.th S := uzTBound (S := S) τ hτE hτ1 _ hξT hξ2
  have hMξ : M ≤ Om1 * M + η :=
    (Ordinal.le_mul_right M Rj.rj_Om1_inE.pos).trans le_self_add
  have hMθ : M < ConjT.th S := hMξ.trans_lt hξθ
  have hall := vdArg_dat hτE hτ1 hΩM hηO hξT
  have hMT : Vd.VdDatIn (· ∈ Tset τ) M := by
    by_cases hMB : M < Uc.ucB
    · exact Or.inl ⟨hMB, hall.1 hMB⟩
    · push Not at hMB
      exact Or.inr ⟨S, hMB, hMθ, hall.2 S hMB hMθ⟩
  have hlt := (vdLevel_lt hτE hτ1 hΩM hMT hηT hηO).1
  obtain ⟨q, hqS, hxq, hq1, hgap⟩ := ybSCnext hx1.le
  have hMq : YbK S q M := hIF M q hΩM hMθ hqS hq1 (fun hMB => (hlt.1 hMB).trans_le hxq)
    (fun hMB => hlt.2 S hMB hMθ q hqS hxq)
  exact ybK_lower (ybK_gap hx0 hgap) M hMq

/-- **The covering lemma under `YbIF` alone.** -/
theorem ybCover_IF {l β : Ordinal.{0}} (hl0 : 0 < l) (hb1 : upsilon (l + β) ≤ Om1) (hIF : YbIF S) :
    ∀ x, x < upsilon (l + β) → x < Om1 → YbCov S l β x :=
  ybCover hl0 (ybLevK_of_IF hl0 hb1 hIF)

/-! ## `YbIF` is not vacuous: the levels `Ω₁` and `B₂` -/

/-- A strongly critical `q` is above `2`. -/
theorem yb_two_lt {q : Ordinal.{0}} (hq : SC q) : (1 + 1 : Ordinal.{0}) < q := by
  have h1 : veblen 0 0 < q := hq.2 0 hq.1 0 hq.1
  rw [veblen_zero_apply, opow_zero] at h1
  have hw : veblen 0 1 < q := hq.2 0 hq.1 1 h1
  rw [veblen_zero_apply, opow_one] at hw
  exact (lt_of_lt_of_le (by rw [one_add_one_eq_two]; exact natCast_lt_omega0 2) le_rfl).trans hw

/-- **`Ω₁` is in every inacc-free closure at a strongly critical threshold.** -/
theorem ybK_Om1 {q : Ordinal.{0}} (hq : SC q) : YbK S q Om1 := by
  rw [Tw.tw_Om1_eq]
  exact .om (.small ((lt_add_of_pos_right 1 zero_lt_one).trans (yb_two_lt hq)))

/-- **`B₂ = ψ_{Ω₂}(φ(1, Ω₂ + 1))` is in every inacc-free closure at a strongly critical threshold.** -/
theorem ybK_B {q : Ordinal.{0}} (hq : SC q) : YbK S q Uc.ucB := by
  have h2 : (1 + 1 : Ordinal.{0}) < q := yb_two_lt hq
  have h1 : (1 : Ordinal.{0}) < q := (lt_add_of_pos_right 1 zero_lt_one).trans h2
  have hO2 : YbK S q (Om (1 + 1)) := .om (.small h2)
  have hne : (Om (1 + 1) : Ordinal.{0}) ≠ Om 1 := fun h =>
    (lt_add_of_pos_right (1 : Ordinal.{0}) zero_lt_one).ne' (Om_strictMono.injective h)
  rw [← Uc.uc_psiE_eq_B (S := S), Uc.uc_E_eq_veblen, Uc.uc_Om2_eq]
  exact .coll (InaccSeq.InR_Om_succ (S := S) 1) hne hO2 (.phi (.small h1) (.add hO2 (.small h1)))

/-- **`YbIF` holds at the levels `Ω₁` and `B₂`** (its hypotheses are satisfiable: the data of `Ω₁` and `B₂` are below
every strongly critical `q`). -/
theorem ybIF_wit {q : Ordinal.{0}} (hq : SC q) : YbK S q Om1 ∧ YbK S q Uc.ucB := ⟨ybK_Om1 hq, ybK_B hq⟩

end Googology.Trans.PoR.InaccPsi.R2.Yb

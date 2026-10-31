import Googology.Trans.PoR.InaccPsi.R2.WwRoad

/-!
# The image of the gap form under the shift: a well-formed `ε`-number of the image segment

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

The gap witness `X = ϑ^{u₁}(B₂ + λ)` (`Ww.wwX`, `λ = L(k) = υ_λ`) has the repaired form
`sg (X+ω+1) … + th 1 B₂ (lo λ)` (`Ww.wwForm_X`).  Its `ϑ`-node has the image (`Ww.wwImg`)
`ϑ^{υ_{μ+f(1)}}(Ω₁·B₂ + π_{υ_μ,υ_λ}(λ))`.  Here: for an offset map with `f(1) = 1` this is
`ϑ^{υ_{μ+1}}(B₂ + υ_μ)` (`π` sends the base `υ_λ` to `υ_μ`, `Cited.pi_base`), and at every countable `υ`-point
`υ_μ` this ordinal is an `ε`-number of `T^{υ_{μ+1}}` strictly inside the segment `(υ_{μ+1}, υ_{μ+2})` with the
parameter `υ_μ` — exactly the shape of the gap witness one segment down.  So the image the realizer must produce
is a legitimate point of the image segment: no evidence against `skRealB` at the gap witness.

* `xbIX` (the candidate image `ϑ^{υ_{μ+1}}(B₂ + υ_μ)`), `xb_arg` (its argument is in `T^{υ_{μ+1}} ∩ Ω₂`, `≥ Ω₁`,
  with the component `υ_μ`), `xbIX_spec` (**`ε`-number of `T^{υ_{μ+1}}` in `(υ_{μ+1}, υ_{μ+2})` with the parameter
  `υ_μ`**), `xb_img_gap` (**the image of the `ϑ`-node of the gap form is `xbIX μ`**), `xb_img_gap_k` (the same at
  the gap witness of `L(k)`, with its value `Ww.wwX`).

No new axiom.  New definition: `xbIX` (an ordinal).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **The candidate image** `ϑ^{υ_{μ+1}}(B₂ + υ_μ)`. -/
noncomputable def xbIX (μ : Ordinal.{0}) : Ordinal.{0} :=
  vt (upsilon (μ + 1)) (Uc.ucB + upsilon μ)

/-- The segment of `υ_{μ+1}`: a countable `υ`-point, `υ_μ < υ_{μ+1}`, and `T^{υ_{μ+1}} ∩ Ω₁ = υ_{μ+2}`. -/
theorem xb_seg {μ : Ordinal.{0}} (hμ : 0 < μ) (hu1 : upsilon (μ + 1) < Om1) :
    UpsPt (upsilon (μ + 1)) ∧ upsilon μ < upsilon (μ + 1) ∧ upsilon (μ + 1) < upsilon (μ + 2) ∧
    ∀ a, a < Om1 → (a ∈ Tset (upsilon (μ + 1)) ↔ a < upsilon (μ + 2)) := by
  have hm := upsilon_normal.strictMono
  have hP : UpsPt (upsilon (μ + 1)) := upsPt_upsilon (hμ.trans_le le_self_add)
  obtain ⟨m, hn, hT⟩ := exists_next hP hu1
  have hn' : IsNext (upsilon (μ + 1)) (upsilon (μ + 2)) := by
    have h := upsilon_isNext (μ + 1)
    rwa [succ_eq_add_one, add_assoc, one_add_one_eq_two] at h
  have hm2 : m = upsilon (μ + 2) := hn.unique hn'
  refine ⟨hP, hm (lt_add_one μ), ?_, fun a ha => hm2 ▸ hT a ha⟩
  exact hm (by
    rw [show (2 : Ordinal.{0}) = 1 + 1 from one_add_one_eq_two.symm, ← add_assoc]; exact lt_add_one _)

/-- **The argument `B₂ + υ_μ`** lies in `T^{υ_{μ+1}} ∩ Ω₂`, is `≥ Ω₁`, and has the additive component `υ_μ`. -/
theorem xb_arg (S : InaccSeq.{0}) {μ : Ordinal.{0}} (hμ : 0 < μ) (hu1 : upsilon (μ + 1) < Om1) :
    Uc.ucB + upsilon μ ∈ Tset (upsilon (μ + 1)) ∧ Uc.ucB + upsilon μ < OmTwo ∧
    Om1 ≤ Uc.ucB + upsilon μ ∧ upsilon μ ∈ comps (Uc.ucB + upsilon μ) := by
  obtain ⟨hP, hlu1, hu12, hT⟩ := xb_seg hμ hu1
  set u1 := upsilon (μ + 1) with hu1def
  have hu1E : InE u1 := upsPt_inE hP
  have hlO : upsilon μ < Om1 := hlu1.trans hu1
  have hlT : upsilon μ ∈ Tset u1 := (hT _ hlO).2 (hlu1.trans hu12)
  have hγ : gamma 0 ≤ u1 := Gq.gq_gam_le_ups S hP
  have hd1 : Vd.vdD S 0 Uc.ucB < u1 :=
    (Ww.ww_B_dat (S := S) (Lq.lq_gamma_SC 0)).trans_le hγ
  have hdT : Vd.vdD S 0 Uc.ucB ∈ Tset u1 := (hT _ (hd1.trans hu1)).2 (hd1.trans hu12)
  have hMT : Vd.VdDatIn (· ∈ Tset u1) Uc.ucB := Vd.vdDatIn_th (S := S) le_rfl Vd.vd_B_lt_th hdT
  have hmem := vdArg_mem hu1E hu1 Uc.ucB_gt.le hMT hlT hlO
  rw [Uf.uf_Om1_mul_B] at hmem
  refine ⟨hmem, Ww.ww_Om2_E.add_lt Uc.ucB_lt_Om2 (hlO.trans tqc_Om1_lt_OmTwo),
    Uc.ucB_gt.le.trans le_self_add, ?_⟩
  have hlE : InE (upsilon μ) := upsPt_inE (upsPt_upsilon hμ)
  have hd : ω ^ Om1 ∣ Uc.ucB := by
    rw [Rj.rj_Om1_inE]; exact ⟨Uc.ucB, Uf.uf_Om1_mul_B.symm⟩
  have hlt : upsilon μ < ω ^ Om1 := by rw [Rj.rj_Om1_inE]; exact hlO
  refine Rj.rj_comps_add Uc.ucB hd (upsilon μ) hlt (upsilon μ) ?_
  have : comps (upsilon μ) = [upsilon μ] := by
    have h := comps_opow (upsilon μ); rwa [hlE] at h
  rw [this]; exact List.mem_singleton_self _

/-- **The candidate image is an `ε`-number of `T^{υ_{μ+1}}` in `(υ_{μ+1}, υ_{μ+2})` with the parameter `υ_μ`**
(the shape of `Ww.wwX_spec` one segment down). -/
theorem xbIX_spec (S : InaccSeq.{0}) {μ : Ordinal.{0}} (hμ : 0 < μ) (hu1 : upsilon (μ + 1) < Om1) :
    xbIX μ ∈ Tset (upsilon (μ + 1)) ∧ InE (xbIX μ) ∧ upsilon (μ + 1) < xbIX μ ∧
    xbIX μ < upsilon (μ + 2) ∧ upsilon μ ∈ Par (upsilon (μ + 1)) (xbIX μ) := by
  obtain ⟨hP, hlu1, -, hT⟩ := xb_seg hμ hu1
  obtain ⟨hξT, hξ2, hΩξ, hlc⟩ := xb_arg S hμ hu1
  have hu1E : InE (upsilon (μ + 1)) := upsPt_inE hP
  obtain ⟨hXT, -, hX1, -, hPar⟩ := vt_memTwo hu1E hu1 hξT hξ2
  obtain ⟨hu1X', hXE⟩ := (vt_E_iff hu1E hu1 hξT hξ2).2 hΩξ
  have hXu2 := (hT _ hX1).1 hXT
  refine ⟨hXT, hXE, hu1X', hXu2, ?_⟩
  unfold xbIX
  rw [hPar]
  obtain ⟨-, hiff⟩ := Par_comps_eq hu1E hu1 hξT (hu1.trans_le hΩξ).le
  refine (hiff (upsilon μ)).2 ⟨upsilon μ, hlc, ?_⟩
  rw [Par_lt hu1E hu1 hlu1]; exact Finset.mem_singleton_self _

/-- **The image of the `ϑ`-node of the gap form** `th 1 B₂ (lo λ)` (`λ = υ_λ`) under an offset map with `f(1) = 1`
is `xbIX μ = ϑ^{υ_{μ+1}}(B₂ + υ_μ)`. -/
theorem xb_img_gap {l μ : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (hl0 : 0 < l) (hlfix : upsilon l = l)
    (hμ : 0 < μ) (hμl : upsilon μ < upsilon l) (hl1 : upsilon l < Om1) (hf : f 1 = 1) :
    Ww.wwImg l μ f (.th 1 Uc.ucB (.old (.lo l))) = xbIX μ := by
  have hB : Bases (upsilon μ) (upsilon l) :=
    ⟨upsPt_inE (upsPt_upsilon hμ), upsPt_inE (upsPt_upsilon hl0), hμl, hl1⟩
  show vt (upsilon (μ + f 1)) (Om1 * Uc.ucB + pi (upsilon μ) (upsilon l) l) = xbIX μ
  have hp : pi (upsilon μ) (upsilon l) l = upsilon μ := by
    exact (congrArg (pi (upsilon μ) (upsilon l)) hlfix.symm).trans (pi_base hB).2
  rw [hp, hf, Uf.uf_Om1_mul_B]; rfl

/-- **At the gap witness of `L(k)`**: the `ϑ`-node `th 1 B₂ (lo λ)` has the value `Ww.wwX S k` and, for every
countable `υ`-point `υ_μ < υ_λ` and `f(1) = 1`, the image `xbIX μ`, an `ε`-number of `T^{υ_{μ+1}}` in
`(υ_{μ+1}, υ_{μ+2})` with the parameter `υ_μ`. -/
theorem xb_img_gap_k (k : ℕ) {μ : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (hμ : 0 < μ)
    (hμl : upsilon μ < upsilon (Nc.ncL S (k : Ordinal.{0}))) (hf : f 1 = 1) :
    Ww.wwVal (Nc.ncL S (k : Ordinal.{0})) (.th 1 Uc.ucB (.old (.lo (Nc.ncL S (k : Ordinal.{0}))))) = Ww.wwX S k ∧
    Ww.wwImg (Nc.ncL S (k : Ordinal.{0})) μ f (.th 1 Uc.ucB (.old (.lo (Nc.ncL S (k : Ordinal.{0}))))) =
      xbIX μ ∧
    xbIX μ ∈ Tset (upsilon (μ + 1)) ∧ InE (xbIX μ) ∧ upsilon (μ + 1) < xbIX μ ∧
    xbIX μ < upsilon (μ + 2) ∧ upsilon μ ∈ Par (upsilon (μ + 1)) (xbIX μ) := by
  obtain ⟨hl0, -, -, -, -, -, -, -, -⟩ := Vr.vr_facts (S := S) k
  obtain ⟨-, hu1O, -, hlfix, -, -⟩ := Ww.ww_seg (S := S) k
  have hm := upsilon_normal.strictMono
  have hl1 : upsilon (Nc.ncL S (k : Ordinal.{0})) < Om1 :=
    (hm (lt_add_one _)).trans hu1O
  have hμ1 : upsilon (μ + 1) < Om1 := by
    have hμl' : μ < Nc.ncL S (k : Ordinal.{0}) := hm.lt_iff_lt.1 hμl
    have : μ + 1 ≤ Nc.ncL S (k : Ordinal.{0}) := Order.add_one_le_of_lt hμl'
    exact (hm.monotone this).trans_lt hl1
  refine ⟨?_, xb_img_gap hl0 hlfix hμ hμl hl1 hf, xbIX_spec S hμ hμ1⟩
  show vt (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) (Om1 * Uc.ucB + Nc.ncL S (k : Ordinal.{0})) = Ww.wwX S k
  rw [Uf.uf_Om1_mul_B]; rfl

end Googology.Trans.PoR.InaccPsi.R2.Xb

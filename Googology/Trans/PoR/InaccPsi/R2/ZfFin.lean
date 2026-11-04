import Googology.Trans.PoR.InaccPsi.R2.ZfNo4

/-!
# Finite leaf sets (a1): every canonical decomposition has finitely many leaves

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

The shift needs the leaves of the level of every configuration node inside the configuration (`Za.ZaHiD`,
`Vl.VlLC`), and a configuration is a `Finset`.  Here: a code whose leaves satisfy `Q` has a finite set `F` of leaves,
`VcLv (· ∈ F ∧ Q)` resp. `YvLv (· ∈ F ∧ Q)`.

* `zf_comps_fin` (`Uc.ucComps γ` is finite), `zf_parts_fin` (`Uc.ucParts z` is finite);
* `zf_fin_union` (finitely many finite witnesses give one);
* `zf_vc_fin` (**`VcLv Q z ⇒ ∃ F, VcLv (· ∈ F ∧ Q) z`**), `zf_yv_fin` (**`YvLv Q z ⇒ ∃ F, YvLv (· ∈ F ∧ Q) z`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Vc Googology.Trans.PoR.InaccPsi.R2.Yv

variable {S : InaccSeq.{0}}

/-- `Uc.ucComps γ` is finite. -/
theorem zf_comps_fin : ∀ γ : Ordinal.{0}, (ucComps γ).Finite := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  rw [ucComps]
  by_cases h1 : γ < OmTwo
  · rw [dif_pos h1]; exact Set.finite_singleton γ
  rw [dif_neg h1]
  by_cases h2 : γ < ucE
  · rw [dif_pos h2]
    exact (IH _ (uc_log_lt (not_lt.1 h1) h2)).union
      ((Set.finite_singleton _).union (IH _ (uc_mod_lt (not_lt.1 h1))))
  · rw [dif_neg h2]; exact Set.finite_empty

/-- `Uc.ucParts z` is finite. -/
theorem zf_parts_fin (z : Ordinal.{0}) : (ucParts z).Finite := by
  rw [ucParts]
  split_ifs
  · exact (Set.finite_singleton _).insert _
  · exact (zf_comps_fin _).union (Set.finite_singleton _)

/-- **Finitely many finite witnesses give one**: `R x` monotone in the finite set, `∃ F, R x F` for every `x` of a
finite set `A` ⇒ one `F` serves every `x ∈ A`. -/
theorem zf_fin_union {A : Set Ordinal.{0}} (hA : A.Finite) (R : Ordinal.{0} → Finset Ordinal.{0} → Prop)
    (hmono : ∀ x F F', F ⊆ F' → R x F → R x F') (h : ∀ x ∈ A, ∃ F, R x F) : ∃ F, ∀ x ∈ A, R x F := by
  classical
  let g : Ordinal.{0} → Finset Ordinal.{0} := fun x => if hx : ∃ F, R x F then Classical.choose hx else ∅
  refine ⟨hA.toFinset.biUnion g, fun x hx => ?_⟩
  have hex : ∃ F, R x F := h x hx
  have hg : R x (g x) := by
    show R x (if hx : ∃ F, R x F then Classical.choose hx else ∅)
    rw [dif_pos hex]; exact Classical.choose_spec hex
  exact hmono x _ _ (Finset.subset_biUnion_of_mem g (hA.mem_toFinset.2 hx)) hg

/-- **Finite leaf sets below `B₂`.** -/
theorem zf_vc_fin {Q : Ordinal.{0} → Prop} :
    ∀ z, VcLv Q z → ∃ F : Finset Ordinal.{0}, VcLv (fun p => p ∈ F ∧ Q p) z := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hQ
  rcases lt_or_ge z Om1 with hz | hz
  · refine ⟨{z}, (VcLv_small _ hz).2 ⟨Finset.mem_singleton_self z, (VcLv_small Q hz).1 hQ⟩⟩
  rcases hz.eq_or_lt with hz | h1
  · exact ⟨∅, by rw [← hz]; exact VcLv_Om1 _⟩
  rcases le_or_gt ucB z with hB | hB
  · exact ⟨∅, VcLv_big _ hB⟩
  have hmonoF : ∀ (x : Ordinal.{0}) (F F' : Finset Ordinal.{0}), F ⊆ F' →
      VcLv (fun p => p ∈ F ∧ Q p) x → VcLv (fun p => p ∈ F' ∧ Q p) x :=
    fun x F F' hFF' h => VcLv_mono (fun p _ hp => ⟨hFF' hp.1, hp.2⟩) x h
  by_cases hE : ω ^ z = z
  · by_cases hI : invVeblen₁ z < z
    · rw [VcLv_phi Q h1 hB hE hI] at hQ
      obtain ⟨F1, h1F⟩ := IH _ hI hQ.1
      obtain ⟨F2, h2F⟩ := IH _ (Tf.tf_inv2_lt hE) hQ.2
      exact ⟨F1 ∪ F2, (VcLv_phi _ h1 hB hE hI).2 ⟨hmonoF _ _ _ Finset.subset_union_left h1F,
        hmonoF _ _ _ Finset.subset_union_right h2F⟩⟩
    · rw [VcLv_atom Q h1 hB hE hI] at hQ
      obtain ⟨F, hF⟩ := zf_fin_union (zf_parts_fin z)
        (fun x F => x < z → VcLv (fun p => p ∈ F ∧ Q p) x)
        (fun x F F' hFF' h hxz => hmonoF x F F' hFF' (h hxz))
        (fun x hx => by
          by_cases hxz : x < z
          · obtain ⟨F, hF⟩ := IH x hxz (hQ x hx hxz); exact ⟨F, fun _ => hF⟩
          · exact ⟨∅, fun h => absurd h hxz⟩)
      exact ⟨F, (VcLv_atom _ h1 hB hE hI).2 fun x hx hxz => hF x hx hxz⟩
  · rw [VcLv_cnf Q h1 hB hE] at hQ
    have hlz := Tf.tf_log_lt h1 hE
    obtain ⟨F2, h2F⟩ := IH _ (Rj.rj_mod_lt (Rj.rj_Om1_pos.trans h1).ne') hQ.2
    have hQ1 := hQ.1
    by_cases hl : ω ^ log ω z = log ω z
    · rw [if_pos hl] at hQ1
      obtain ⟨F1, h1F⟩ := IH _ hlz hQ1
      refine ⟨F1 ∪ F2, (VcLv_cnf _ h1 hB hE).2 ⟨?_, hmonoF _ _ _ Finset.subset_union_right h2F⟩⟩
      rw [if_pos hl]; exact hmonoF _ _ _ Finset.subset_union_left h1F
    · rw [if_neg hl] at hQ1
      obtain ⟨F1, h1F⟩ := IH _ ((Ordinal.sub_le_self _ _).trans_lt hlz) hQ1
      refine ⟨F1 ∪ F2, (VcLv_cnf _ h1 hB hE).2 ⟨?_, hmonoF _ _ _ Finset.subset_union_right h2F⟩⟩
      rw [if_neg hl]; exact hmonoF _ _ _ Finset.subset_union_left h1F

/-- **Finite leaf sets below `θ`.** -/
theorem zf_yv_fin {Q : Ordinal.{0} → Prop} {z : Ordinal.{0}} (h : YvLv S Q z) :
    ∃ F : Finset Ordinal.{0}, YvLv S (fun p => p ∈ F ∧ Q p) z := by
  have hmono : ∀ (x : Ordinal.{0}) (F F' : Finset Ordinal.{0}), F ⊆ F' →
      YvLv S (fun p => p ∈ F ∧ Q p) x → YvLv S (fun p => p ∈ F' ∧ Q p) x :=
    fun x F F' hFF' h => h.mono fun p hp => ⟨hFF' hp.1, hp.2⟩
  induction h with
  | low hz hL =>
    obtain ⟨F, hF⟩ := zf_vc_fin _ hL
    exact ⟨F, YvLv.low hz hF⟩
  | om hs hs' e => exact ⟨∅, YvLv.om hs hs' e⟩
  | cnf a b c d e g _ _ ih1 ih2 =>
    obtain ⟨F1, h1⟩ := ih1
    obtain ⟨F2, h2⟩ := ih2
    exact ⟨F1 ∪ F2, YvLv.cnf a b c d e g (hmono _ _ _ Finset.subset_union_left h1)
      (hmono _ _ _ Finset.subset_union_right h2)⟩
  | veb a b c d e g k _ _ ih1 ih2 =>
    obtain ⟨F1, h1⟩ := ih1
    obtain ⟨F2, h2⟩ := ih2
    exact ⟨F1 ∪ F2, YvLv.veb a b c d e g k (hmono _ _ _ Finset.subset_union_left h1)
      (hmono _ _ _ Finset.subset_union_right h2)⟩
  | atom a b c d e g _ _ ih1 ih2 =>
    obtain ⟨F1, h1⟩ := ih1
    obtain ⟨F2, h2⟩ := ih2
    exact ⟨F1 ∪ F2, YvLv.atom a b c d e g (hmono _ _ _ Finset.subset_union_left h1)
      (hmono _ _ _ Finset.subset_union_right h2)⟩

end Googology.Trans.PoR.InaccPsi.R2.Zf

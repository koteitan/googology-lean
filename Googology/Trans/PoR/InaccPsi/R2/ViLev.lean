import Googology.Trans.PoR.InaccPsi.R2.ViTerm

/-!
# The leaves of a moved level and the composition of level maps

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`π = pi σ τ`, `up σ τ = π⁻¹`, `vcSub`, `VcLv` of `R2.VcSub`.  For the hull isomorphism of FRAG on terms with the node
`thz G r` the leaves of a moved level must be known: **the leaves of `π z` are the `π`-images of the leaves of `z`**
(`vi_lv_pi`, by the canonical decomposition of `π z` read off that of `z`: `Vc.vc_pi_cnf`, `Vc.vc_pi_eps`, the
Veblen inverses, the parts of a rebuilt atom `Uc.ucParts_F`, `Uc.ucParts_H` with `vi_comps_map`), and the level maps
compose (`Vc.vc_comp`, `vi_sub_up`).

* `vi_comps_map` (**`ucComps (ucMap f γ) = f '' ucComps γ`** for `f` strictly increasing on the components, `f 0 = 0`,
  values below `Ω₂`);
* `vi_lv_pi` (**`VcLv P (π z) ↔ VcLv (P ∘ π) z`** for `z ∈ Tᵗ[σ]`, `z < B₂`), `vi_lv_up` (**the same for `π⁻¹`** on
  `T^σ`), `vi_sub_up` (**`vcSub f (π⁻¹ z) = vcSub (f ∘ π⁻¹) z`**);
* on terms: `vmap_congr`, `ZL_vmap_pi`, `ZL_vmap_up`, `vmap_vmap_pi`, `vmap_vmap_up`
  (**`vmap f ∘ vmap π = vmap (f ∘ π)`,  `vmap f ∘ vmap π⁻¹ = vmap (f ∘ π⁻¹)`** on terms with the node conditions).

No new definition.  No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vi

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Rh
  Googology.Trans.PoR.InaccPsi.R2.Vc Googology.Trans.PoR.InaccPsi.R2.Un Googology.Trans.PoR.InaccPsi.R2.Un.UnT

/-- **The components of a mapped level**: `ucComps (ucMap f γ) = f '' ucComps γ`. -/
theorem vi_comps_map {f : Ordinal.{0} → Ordinal.{0}} {A : Set Ordinal.{0}} (hf : StrictMonoOn f A)
    (hfΩ : ∀ x ∈ A, x < OmTwo → f x < OmTwo) (h0A : (0 : Ordinal.{0}) ∈ A) (hf0 : f 0 = 0) :
    ∀ γ, γ < ucE → (∀ x ∈ ucComps γ, x ∈ A) → ucComps (ucMap f γ) = f '' ucComps γ := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hE hA
  by_cases h1 : γ < OmTwo
  · have hfγ : f γ < OmTwo := hfΩ γ (hA γ (by rw [ucComps_small h1]; rfl)) h1
    rw [ucMap_small f h1, ucComps_small hfγ, ucComps_small h1, Set.image_singleton]
  have h1' := not_lt.1 h1
  obtain ⟨hl1, hd0, hdΩ, hr, hdec⟩ := vc_cnf2 h1'
  set e := log OmTwo γ with hedef
  set d := γ / OmTwo ^ e with hddef
  set r := γ % OmTwo ^ e with hrdef
  have hc := ucComps_big h1' hE
  have hAe : ∀ x ∈ ucComps e, x ∈ A := fun x hx => hA x (by rw [hc]; exact Or.inl hx)
  have hAd : d ∈ A := hA d (by rw [hc]; exact Or.inr (Or.inl rfl))
  have hAr : ∀ x ∈ ucComps r, x ∈ A := fun x hx => hA x (by rw [hc]; exact Or.inr (Or.inr hx))
  have he2 : e < γ := uc_log_lt h1' hE
  have hr2 : r < γ := uc_mod_lt h1'
  obtain ⟨-, hR, -, hge1⟩ := vc_map_mono hf hfΩ h0A hf0 γ hE hA
  have hEe : 1 ≤ ucMap f e := (vc_map_mono hf hfΩ h0A hf0 e (he2.trans hE) hAe).2.2.2 hl1
  have hmap : ucMap f γ = OmTwo ^ ucMap f e * f d + ucMap f r := ucMap_big f h1' hE
  have hR' : ucMap f r < OmTwo ^ ucMap f e := hR h1'
  have hDd : f d < OmTwo := hfΩ d hAd hdΩ
  have hD0 : f d ≠ 0 := by
    have := hf h0A hAd (pos_iff_ne_zero.2 hd0)
    rw [hf0] at this; exact this.ne'
  have hγ'E : ucMap f γ < ucE := vc_map_lt_E hfΩ γ hE hA
  have hW1 : OmTwo ≤ OmTwo ^ ucMap f e := by
    conv_lhs => rw [← opow_one (OmTwo : Ordinal.{0})]
    exact opow_le_opow_right uc_SC_Om2.1 hEe
  have hγ'2 : OmTwo ≤ ucMap f γ := by
    rw [hmap]; exact hW1.trans ((le_mul_left _ (pos_iff_ne_zero.2 hD0)).trans le_self_add)
  have hlog : log OmTwo (ucMap f γ) = ucMap f e := by
    rw [hmap, log_opow_mul_add uc_one_lt_Om2 hD0 hR', log_eq_zero hDd, add_zero]
  have hpos : (OmTwo : Ordinal.{0}) ^ ucMap f e ≠ 0 := (opow_pos _ uc_SC_Om2.1).ne'
  have hdiv : ucMap f γ / OmTwo ^ ucMap f e = f d := by
    rw [hmap, Ordinal.mul_add_div _ hpos, Ordinal.div_eq_zero_of_lt hR', add_zero]
  have hmod : ucMap f γ % OmTwo ^ ucMap f e = ucMap f r := by
    rw [hmap, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hR']
  rw [ucComps_big hγ'2 hγ'E, hlog, hdiv, hmod, IH e he2 (he2.trans hE) hAe, IH r hr2 (hr2.trans hE) hAr, hc,
    Set.image_union, Set.image_union, Set.image_singleton]

/-- `VcLv` respects a predicate equivalence on the leaves. -/
theorem vi_lv_congr {P Q : Ordinal.{0} → Prop} {z : Ordinal.{0}} (h : VcLv (fun x => P x ↔ Q x) z) :
    VcLv P z ↔ VcLv Q z :=
  ⟨fun hP => VcLv_mono (fun _ _ hx => hx.1.1 hx.2) z (VcLv_and z h hP),
    fun hQ => VcLv_mono (fun _ _ hx => hx.1.2 hx.2) z (VcLv_and z h hQ)⟩

/-- **THE LEAVES OF A MOVED LEVEL**: for `z ∈ Tᵗ[σ]` below `B₂`, every leaf of `π z` satisfies `P` iff `P ∘ π` holds
at every leaf of `z` (the canonical decomposition of `π z` is the `π`-image of that of `z`). -/
theorem vi_lv_pi {σ τ : Ordinal.{0}} (h : Bases σ τ) (P : Ordinal.{0} → Prop) :
    ∀ z, z < ucB → z ∈ TB τ σ → (VcLv P (pi σ τ z) ↔ VcLv (fun x => P (pi σ τ x)) z) := by
  obtain ⟨o1, o2⟩ := pi_Om1 h
  have hsm := (pi_bijOn h).2
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hB hT
  have hπB := vc_pi_lt_B h hB hT
  rcases lt_or_ge z Om1 with hz | hz
  · have hπ1 : pi σ τ z < Om1 := by
      calc pi σ τ z < pi σ τ Om1 := hsm hT o1 hz
        _ = Om1 := o2
    rw [VcLv_small _ hπ1, VcLv_small _ hz]
  rcases hz.eq_or_lt with hz | h1
  · rw [← hz, o2]; exact iff_of_true (VcLv_Om1 _) (VcLv_Om1 _)
  have hπ1 := vc_pi_gt_Om1 h hT h1
  have hL := vc_lv_TB h z hB hT
  have hπeq := vc_pi_TB h hB hT
  by_cases hE : ω ^ z = z
  · have hπE := vc_pi_eps h hB hT h1 hE
    by_cases hI : invVeblen₁ z < z
    · have hcz : invVeblen₂ z < z := Tf.tf_inv2_lt hE
      rw [VcLv_phi _ h1 hB hE hI] at hL
      obtain ⟨haT, haπ⟩ := vc_pi h _ (hI.trans hB) hL.1
      obtain ⟨hcT, hcπ⟩ := vc_pi h _ (hcz.trans hB) hL.2
      have hpz : pi σ τ z = veblen (pi σ τ (invVeblen₁ z)) (pi σ τ (invVeblen₂ z)) := by
        rw [hπeq, vcSub_phi _ h1 hB hE hI, ← haπ, ← hcπ]
      have hπa : pi σ τ (invVeblen₁ z) < pi σ τ z := hsm haT hT hI
      have hπc : pi σ τ (invVeblen₂ z) < pi σ τ z := hsm hcT hT hcz
      have hI1 : invVeblen₁ (pi σ τ z) = pi σ τ (invVeblen₁ z) := by
        rw [hpz]; exact invVeblen₁_veblen (by rw [← hpz]; exact hπc)
      have hI2 : invVeblen₂ (pi σ τ z) = pi σ τ (invVeblen₂ z) := by
        rw [invVeblen₂_eq_iff, hπE, hI1]; exact hpz
      rw [VcLv_phi P hπ1 hπB hπE (by rw [hI1]; exact hπa), hI1, hI2, IH _ hI (hI.trans hB) haT,
        IH _ hcz (hcz.trans hB) hcT, VcLv_phi _ h1 hB hE hI]
    · -- an atom
      have hSC : SC z := tl_SC_of h1 hI
      have hA := ucAtom_TB h hSC h1 hB
      have hplt := vc_parts_lt h1 hB hI
      rw [VcLv_atom _ h1 hB hE hI] at hL
      have hpT : ∀ x ∈ ucParts z, x ∈ TB τ σ := fun x hx =>
        (vc_pi h x ((hplt x hx).trans hB) (hL x hx (hplt x hx))).1
      have hpz : pi σ τ z = ucRebuild (pi σ τ) z := hA.2 hpT
      have hπSC : SC (pi σ τ z) := by
        rw [hpz]; unfold ucRebuild; split_ifs
        · exact rhF_SC _ _
        · exact ucH_SC _ _
      obtain ⟨hπE', hπI⟩ := uc_SC_facts hπSC
      have hπplt := vc_parts_lt hπ1 hπB hπI
      -- the parts of `π z` are the `π`-images of the parts of `z`
      have hparts : ucParts (pi σ τ z) = pi σ τ '' ucParts z := by
        obtain ⟨hXT, hXπ⟩ := vc_pi_X h
        by_cases hX : z < tlX
        · obtain ⟨-, hyz, -⟩ := tl_nf hSC h1 hX
          have hparts : ucParts z = {tlLev z, tlI (tlLev z) z} := by rw [ucParts, if_pos hX]
          have hyP : tlI (tlLev z) z ∈ ucParts z := by rw [hparts]; exact mem_insert_of_mem _ rfl
          have hpz' : pi σ τ z = rhF (pi σ τ (tlLev z)) (pi σ τ (tlI (tlLev z) z)) := by
            rw [hpz, ucRebuild, if_pos hX]
          have hπX : pi σ τ z < tlX := by rw [← hXπ]; exact hsm hT hXT hX
          have hπy : pi σ τ (tlI (tlLev z) z) < pi σ τ z := hsm (hpT _ hyP) hT hyz
          rw [hpz'] at hπX hπy
          rw [hpz', ucParts_F hπX hπy, hparts, Set.image_insert_eq, Set.image_singleton]
        · have hX' := not_lt.1 hX
          have hne := uc_nf_of_lt hSC h1 hB
          obtain ⟨hlE, hlv, -, -, -⟩ := ucLev_spec hSC h1 hne
          obtain ⟨-, hyz⟩ := uc_nf hSC h1 hne
          have hparts : ucParts z = ucComps (ucLev z) ∪ {ucI (ucLev z) z} := by rw [ucParts, if_neg hX]
          have hyP : ucI (ucLev z) z ∈ ucParts z := by
            rw [hparts]; exact mem_union_right _ (mem_singleton _)
          have hcP : ∀ x ∈ ucComps (ucLev z), x ∈ ucParts z := fun x hx => by
            rw [hparts]; exact mem_union_left _ hx
          have hpz' : pi σ τ z = ucH (ucMap (pi σ τ) (ucLev z)) (pi σ τ (ucI (ucLev z) z)) := by
            rw [hpz, ucRebuild, if_neg hX]
          have hπX : tlX ≤ pi σ τ z := by rw [← hXπ]; exact ((pi_bijOn h).2.le_iff_le hXT hT).2 hX'
          have hπy : pi σ τ (ucI (ucLev z) z) < pi σ τ z := hsm (hpT _ hyP) hT hyz
          set A : Set Ordinal.{0} := {x | x ∈ TB τ σ ∧ x < ucB} with hAdef
          have h0σ : (0 : Ordinal.{0}) < σ := Si.si_inE_pos h.1
          have hfA : StrictMonoOn (pi σ τ) A := fun x hx y hy hxy => hsm hx.1 hy.1 hxy
          have hfΩ : ∀ x ∈ A, x < OmTwo → pi σ τ x < OmTwo := fun x hx _ =>
            (vc_pi_lt_B h hx.2 hx.1).trans ucB_lt_Om2
          have h0A : (0 : Ordinal.{0}) ∈ A := ⟨mem_TB_of_lt h h0σ, Rj.rj_Om1_pos.trans ucB_gt⟩
          have hcA : ∀ x ∈ ucComps (ucLev z), x ∈ A := fun x hx =>
            ⟨hpT x (hcP x hx), (((le_ucC hx).trans_lt hlv)).trans hB⟩
          have hγ' : ucMap (pi σ τ) (ucLev z) < ucE := vc_map_lt_E hfΩ _ hlE hcA
          rw [hpz'] at hπX hπy
          rw [hpz', ucParts_H hγ' hπy hπX, vi_comps_map hfA hfΩ h0A (pi_lt h h0σ) _ hlE hcA, hparts,
            Set.image_union, Set.image_singleton]
      rw [VcLv_atom P hπ1 hπB hπE' hπI, VcLv_atom _ h1 hB hE hI, hparts]
      constructor
      · intro hP x hx hxz
        exact (IH x hxz (hxz.trans hB) (hpT x hx)).1 (hP _ ⟨x, hx, rfl⟩ (hsm (hpT x hx) hT hxz))
      · rintro hP _ ⟨x, hx, rfl⟩ -
        exact (IH x (hplt x hx) ((hplt x hx).trans hB) (hpT x hx)).2 (hP x hx (hplt x hx))
  · -- not an `ε`-number
    obtain ⟨hπE, hlog, -, hmod, hlT, hrT, hwT⟩ := vc_pi_cnf h h1 hB hE hT
    have hz0 : z ≠ 0 := (Rj.rj_Om1_pos.trans h1).ne'
    have hl1 : Om1 ≤ log ω z := Si.si_Om1_le_log h1.le
    have hlz : log ω z < z := Tf.tf_log_lt h1 hE
    have hrz : z % ω ^ log ω z < z := Rj.rj_mod_lt hz0
    have hwz : ω ^ log ω z ≤ z := opow_log_le_self ω hz0
    obtain ⟨-, -, hb⟩ := vc_pi_opow h hl1 (hwz.trans_lt hB) hwT
    rw [hlog] at hmod
    rw [VcLv_cnf P hπ1 hπB hπE, VcLv_cnf _ h1 hB hE, hlog, hmod, IH _ hrz (hrz.trans hB) hrT]
    by_cases hl : ω ^ log ω z = log ω z
    · have hπl : ω ^ pi σ τ (log ω z) = pi σ τ (log ω z) := by
        rcases hl1.eq_or_lt with e | e
        · rw [← e, o2, Rj.rj_Om1_opow]
        · exact vc_pi_eps h ((hl ▸ hwz).trans_lt hB) hlT e hl
      rw [if_pos hl, if_pos hπl, IH _ hlz (hlz.trans hB) hlT]
    · obtain ⟨hbT, hbπ⟩ := hb hl
      have hπl : ω ^ pi σ τ (log ω z) ≠ pi σ τ (log ω z) := by
        have hl1' : Om1 < log ω z := lt_of_le_of_ne hl1 fun e => hl (by rw [← e, Rj.rj_Om1_opow])
        exact (vc_pi_cnf h hl1' (hlz.trans hB) hl hlT).1
      have hbz : log ω z - Om1 < z := (Ordinal.sub_le_self _ _).trans_lt hlz
      rw [if_neg hl, if_neg hπl, hbπ, Ordinal.add_sub_cancel, IH _ hbz (hbz.trans hB) hbT]

/-- **The leaves of `π⁻¹ G`**: for `G ∈ T^σ` below `B₂`, `VcLv P (π⁻¹ G) ↔ VcLv (P ∘ π⁻¹) G`. -/
theorem vi_lv_up {σ τ G : Ordinal.{0}} (h : Bases σ τ) (P : Ordinal.{0} → Prop) (hB : G < ucB) (hG : G ∈ Tset σ) :
    VcLv P (up σ τ G) ↔ VcLv (fun x => P (up σ τ x)) G := by
  obtain ⟨u1, u2⟩ := up_spec h hG
  have hUB := vc_up_lt_B h hB hG
  have hc := vi_lv_pi h (fun x => P (up σ τ x)) (up σ τ G) hUB u1
  rw [u2] at hc
  rw [hc]
  refine (vi_lv_congr (VcLv_mono (fun x _ hx => ?_) _ (vc_up h hB hG).2)).symm
  show P (up σ τ (pi σ τ x)) ↔ P x
  rw [up_pi h hx]

/-- **The leaf substitution after the inverse base change**: `vcSub f (π⁻¹ G) = vcSub (f ∘ π⁻¹) G` for `G ∈ T^σ`
below `B₂`. -/
theorem vi_sub_up {σ τ G : Ordinal.{0}} (h : Bases σ τ) (f : Ordinal.{0} → Ordinal.{0}) (hB : G < ucB)
    (hG : G ∈ Tset σ) : vcSub f (up σ τ G) = vcSub (f ∘ up σ τ) G := by
  obtain ⟨u1, u2⟩ := up_spec h hG
  have hUB := vc_up_lt_B h hB hG
  have hc := vc_comp h (f ∘ up σ τ) (up σ τ G) hUB u1
  rw [u2] at hc
  rw [hc]
  exact vcSub_congr _ (VcLv_mono (fun x _ hx => by simp only [Function.comp, up_pi h hx]) _ (vc_up h hB hG).2)

/-! ## On terms -/

/-- `vmap` depends only on the parameters and the level leaves. -/
theorem vmap_congr {f g : Ordinal.{0} → Ordinal.{0}} :
    ∀ {k : Bool} (t : UnT k), Lv (fun x => f x = g x) t → ZL (fun x => f x = g x) t → vmap f t = vmap g t
  | _, .par _, hl, _ => by simp only [vmap]; rw [show f _ = g _ from hl]
  | _, .add s t, hl, hz => by simp only [vmap, vmap_congr s hl.1 hz.1, vmap_congr t hl.2 hz.2]
  | _, .base, _, _ => rfl
  | _, .th1 s, hl, hz => by simp only [vmap, vmap_congr s hl hz]
  | _, .thc q r, hl, hz => by
    have : vq f q = vq g q := by unfold vq; rw [vcSub_congr _ hz.1]
    simp only [vmap, vmap_congr r hl hz.2, this]
  | _, .thg _ G r, hl, hz => by simp only [vmap, vmap_congr G hl.1 hz.1, vmap_congr r hl.2 hz.2]
  | _, .lf c, hl, hz => by simp only [vmap, vmap_congr c hl hz]
  | _, .om b, hl, hz => by simp only [vmap, vmap_congr b hl hz]
  | _, .ad x y, hl, hz => by simp only [vmap, vmap_congr x hl.1 hz.1, vmap_congr y hl.2 hz.2]

/-- The level `Ω₁ · vq π q` is `π(Ω₁·q)`. -/
theorem vi_vq_pi {σ τ q : Ordinal.{0}} (h : Bases σ τ) (hq1 : 1 ≤ q) (hqB : Om1 * q < ucB)
    (hL : VcLv (· ∈ TB τ σ) (Om1 * q)) :
    Om1 * vq (pi σ τ) q = pi σ τ (Om1 * q) ∧ Om1 * q ∈ TB τ σ := by
  obtain ⟨hGT, hGpi⟩ := vc_pi h _ hqB hL
  obtain ⟨M', hM'e, -, -, hM'⟩ := vc_level_img h hq1 hqB hGT
  have hvq : vq (pi σ τ) q = M' := by
    unfold vq; rw [← hM', hM'e]; exact Ordinal.mul_div_cancel M' Rj.rj_Om1_pos.ne'
  exact ⟨by rw [hvq, hM'e], hGT⟩

/-- **The level leaves after `π`**: `ZL P (vmap π t) ↔ ZL (P ∘ π) t`. -/
theorem ZL_vmap_pi {σ τ : Ordinal.{0}} (h : Bases σ τ) (P : Ordinal.{0} → Prop) :
    ∀ {k : Bool} (t : UnT k), ZW τ t → ZL (· ∈ TB τ σ) t →
      (ZL P (vmap (pi σ τ) t) ↔ ZL (fun x => P (pi σ τ x)) t)
  | _, .par _, _, _ => Iff.rfl
  | _, .add s t, hz, hl => and_congr (ZL_vmap_pi h P s hz.1 hl.1) (ZL_vmap_pi h P t hz.2 hl.2)
  | _, .base, _, _ => Iff.rfl
  | _, .th1 s, hz, hl => ZL_vmap_pi h P s hz hl
  | _, .thc q r, hz, hl => by
    obtain ⟨e, hGT⟩ := vi_vq_pi h hz.1.q1 hz.1.qB hl.1
    show VcLv P (Om1 * vq (pi σ τ) q) ∧ _ ↔ _
    rw [e, vi_lv_pi h P _ hz.1.qB hGT]
    exact and_congr Iff.rfl (ZL_vmap_pi h P r hz.2 hl.2)
  | _, .thg _ G r, hz, hl => and_congr (ZL_vmap_pi h P G hz.1 hl.1) (ZL_vmap_pi h P r hz.2 hl.2)
  | _, .lf c, hz, hl => ZL_vmap_pi h P c hz hl
  | _, .om b, hz, hl => ZL_vmap_pi h P b hz hl
  | _, .ad x y, hz, hl => and_congr (ZL_vmap_pi h P x hz.1 hl.1) (ZL_vmap_pi h P y hz.2 hl.2)

/-- **The level leaves after `π⁻¹`**: `ZL P (vmap π⁻¹ t) ↔ ZL (P ∘ π⁻¹) t`. -/
theorem ZL_vmap_up {σ τ : Ordinal.{0}} (h : Bases σ τ) (P : Ordinal.{0} → Prop) :
    ∀ {k : Bool} (t : UnT k), ZW σ t → (ZL P (vmap (up σ τ) t) ↔ ZL (fun x => P (up σ τ x)) t)
  | _, .par _, _ => Iff.rfl
  | _, .add s t, hz => and_congr (ZL_vmap_up h P s hz.1) (ZL_vmap_up h P t hz.2)
  | _, .base, _ => Iff.rfl
  | _, .th1 s, hz => ZL_vmap_up h P s hz
  | _, .thc q r, hz => by
    obtain ⟨e, -⟩ := vi_up_level (τ := τ) h hz.1.q1 hz.1.qB hz.1.gm
    show VcLv P (Om1 * vq (up σ τ) q) ∧ _ ↔ _
    rw [e, vi_lv_up h P hz.1.qB hz.1.gm]
    exact and_congr Iff.rfl (ZL_vmap_up h P r hz.2)
  | _, .thg _ G r, hz => and_congr (ZL_vmap_up h P G hz.1) (ZL_vmap_up h P r hz.2)
  | _, .lf c, hz => ZL_vmap_up h P c hz
  | _, .om b, hz => ZL_vmap_up h P b hz
  | _, .ad x y, hz => and_congr (ZL_vmap_up h P x hz.1) (ZL_vmap_up h P y hz.2)

/-- **`vmap f ∘ vmap π = vmap (f ∘ π)`** on terms with the node conditions and level leaves in `Tᵗ[σ]`. -/
theorem vmap_vmap_pi {σ τ : Ordinal.{0}} (h : Bases σ τ) (f : Ordinal.{0} → Ordinal.{0}) :
    ∀ {k : Bool} (t : UnT k), ZW τ t → ZL (· ∈ TB τ σ) t →
      vmap f (vmap (pi σ τ) t) = vmap (fun x => f (pi σ τ x)) t
  | _, .par _, _, _ => rfl
  | _, .add s t, hz, hl => by simp only [vmap, vmap_vmap_pi h f s hz.1 hl.1, vmap_vmap_pi h f t hz.2 hl.2]
  | _, .base, _, _ => rfl
  | _, .th1 s, hz, hl => by simp only [vmap, vmap_vmap_pi h f s hz hl]
  | _, .thc q r, hz, hl => by
    obtain ⟨e, hGT⟩ := vi_vq_pi h hz.1.q1 hz.1.qB hl.1
    have hq : vq f (vq (pi σ τ) q) = vq (fun x => f (pi σ τ x)) q := by
      unfold vq at e ⊢; rw [e, vc_comp h f _ hz.1.qB hGT]; rfl
    simp only [vmap, vmap_vmap_pi h f r hz.2 hl.2, hq]
  | _, .thg _ G r, hz, hl => by
    simp only [vmap, vmap_vmap_pi h f G hz.1 hl.1, vmap_vmap_pi h f r hz.2 hl.2]
  | _, .lf c, hz, hl => by simp only [vmap, vmap_vmap_pi h f c hz hl]
  | _, .om b, hz, hl => by simp only [vmap, vmap_vmap_pi h f b hz hl]
  | _, .ad x y, hz, hl => by simp only [vmap, vmap_vmap_pi h f x hz.1 hl.1, vmap_vmap_pi h f y hz.2 hl.2]

/-- **`vmap f ∘ vmap π⁻¹ = vmap (f ∘ π⁻¹)`** on terms with the node conditions over `σ`. -/
theorem vmap_vmap_up {σ τ : Ordinal.{0}} (h : Bases σ τ) (f : Ordinal.{0} → Ordinal.{0}) :
    ∀ {k : Bool} (t : UnT k), ZW σ t → vmap f (vmap (up σ τ) t) = vmap (fun x => f (up σ τ x)) t
  | _, .par _, _ => rfl
  | _, .add s t, hz => by simp only [vmap, vmap_vmap_up h f s hz.1, vmap_vmap_up h f t hz.2]
  | _, .base, _ => rfl
  | _, .th1 s, hz => by simp only [vmap, vmap_vmap_up h f s hz]
  | _, .thc q r, hz => by
    obtain ⟨e, -⟩ := vi_up_level (τ := τ) h hz.1.q1 hz.1.qB hz.1.gm
    have hq : vq f (vq (up σ τ) q) = vq (fun x => f (up σ τ x)) q := by
      unfold vq at e ⊢; rw [e, vi_sub_up h f hz.1.qB hz.1.gm]; rfl
    simp only [vmap, vmap_vmap_up h f r hz.2, hq]
  | _, .thg _ G r, hz => by simp only [vmap, vmap_vmap_up h f G hz.1, vmap_vmap_up h f r hz.2]
  | _, .lf c, hz => by simp only [vmap, vmap_vmap_up h f c hz]
  | _, .om b, hz => by simp only [vmap, vmap_vmap_up h f b hz]
  | _, .ad x y, hz => by simp only [vmap, vmap_vmap_up h f x hz.1, vmap_vmap_up h f y hz.2]

end Googology.Trans.PoR.InaccPsi.R2.Vi

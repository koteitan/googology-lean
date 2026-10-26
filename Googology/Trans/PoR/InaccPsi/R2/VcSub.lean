import Googology.Trans.PoR.InaccPsi.R2.UyFix

/-!
# Codes below `B₂` with parameter leaves: the leaf substitution and its base change

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`B₂ = Uc.ucB = ψ_{Ω₂}(ε_{Ω₂+1})`, `E₁ = Gg.ggE = ε_{Ω₁+1}`, `X = Tl.tlX`, `π = pi σ τ`, `Tᵗ[σ] = TB τ σ`.  Every
`z < B₂` has a unique canonical decomposition (the clauses of `Uc.ucDat`): a countable `z` is a **leaf**; `Ω₁` is a
constant; a non-`ε`-number `z > Ω₁` is `ω^l·k + r` (`l = log_ω z ≥ Ω₁`, `0 < k < ω`, `r < ω^l`), and `ω^l` is
`l` itself (an `ε`-number `l`) or `Ω₁·ω^b` with `b = −Ω₁ + l`; an `ε`-number `φ(a, c)` in normal form has the parts
`a, c`; an atom (strongly critical, `Uc.ucParts`) has its parts.  This module turns the decomposition into a
substitution on the leaves, i.e. **a level sort whose terms are the codes themselves**.

* `vcSub f z` (**the leaf substitution**): every leaf `x` of `z` replaced by `f x` (`ω^l ↦ ω^{l'}` if `l` is an
  `ε`-number, `Ω₁·ω^{b'}` otherwise, `φ(a, c) ↦ φ(a', c')`, atoms rebuilt by `Uc.ucRebuild`);
* `VcLv P z` (**every leaf of `z` satisfies `P`**);
* `vcSub_fix` (**`f` fixes every leaf ⇒ `vcSub f z = z`**), `vcSub_congr`, `VcLv_mono`, `VcLv_and`;
* `vc_dat_lt` (**`ucDat z < κ ⇔ every leaf of `z` is `< κ`** for an `ε`-number `κ`: the data is the largest leaf up to
  finite ones);
* `vc_pi` (**THE BASE CHANGE ON CODES: leaves in `Tᵗ[σ]` ⇒ `z ∈ Tᵗ[σ]` and `π z = vcSub π z`**), `vc_lv_TB` (**the
  converse: `z ∈ Tᵗ[σ]` ⇒ every leaf in `Tᵗ[σ]`**), `vc_TB_iff`, `vc_pi_TB` (`π z = vcSub π z` on `Tᵗ[σ] ∩ B₂`),
  `vc_pi_fix` (`Uy.uy_pi_fix` as a corollary).

By [W07a] Def 5.1 / Lemma 5.3 through `R2.pi_add`, `R2.om1_opow_TB_all`, `R2.ucOpow_TB`, `R2.ucPhi_TB`,
`R2.ucAtom_TB`, `R2.Par_comps_eq` (through `Si.siTB_of_comps`).  No new axiom.  New definitions: `vcSub`, `VcLv`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Rh

/-- **The leaf substitution on codes below `B₂`.** -/
noncomputable def vcSub (f : Ordinal.{0} → Ordinal.{0}) (z : Ordinal.{0}) : Ordinal.{0} :=
  if hz : Om1 < z ∧ z < ucB then
    if hE : ω ^ z = z then
      if _hI : invVeblen₁ z < z then
        have : invVeblen₂ z < z := Tf.tf_inv2_lt hE
        veblen (vcSub f (invVeblen₁ z)) (vcSub f (invVeblen₂ z))
      else ucRebuild (fun x => if _hx : x < z then vcSub f x else x) z
    else
      have hl : log ω z < z := Tf.tf_log_lt hz.1 hE
      have : z % ω ^ log ω z < z := Rj.rj_mod_lt (Rj.rj_Om1_pos.trans hz.1).ne'
      have : log ω z - Om1 < z := (Ordinal.sub_le_self _ _).trans_lt hl
      (if ω ^ log ω z = log ω z then vcSub f (log ω z) else Om1 * ω ^ vcSub f (log ω z - Om1)) *
        (z / ω ^ log ω z) + vcSub f (z % ω ^ log ω z)
  else if z < Om1 then f z else z
termination_by z

/-- **Every leaf of `z` satisfies `P`.** -/
def VcLv (P : Ordinal.{0} → Prop) (z : Ordinal.{0}) : Prop :=
  if hz : Om1 < z ∧ z < ucB then
    if hE : ω ^ z = z then
      if _hI : invVeblen₁ z < z then
        have : invVeblen₂ z < z := Tf.tf_inv2_lt hE
        VcLv P (invVeblen₁ z) ∧ VcLv P (invVeblen₂ z)
      else ∀ x ∈ ucParts z, if _hx : x < z then VcLv P x else True
    else
      have hl : log ω z < z := Tf.tf_log_lt hz.1 hE
      have : z % ω ^ log ω z < z := Rj.rj_mod_lt (Rj.rj_Om1_pos.trans hz.1).ne'
      have : log ω z - Om1 < z := (Ordinal.sub_le_self _ _).trans_lt hl
      (if ω ^ log ω z = log ω z then VcLv P (log ω z) else VcLv P (log ω z - Om1)) ∧
        VcLv P (z % ω ^ log ω z)
  else if z < Om1 then P z else True
termination_by z

/-! ## The clauses -/

theorem vcSub_small (f : Ordinal.{0} → Ordinal.{0}) {z : Ordinal.{0}} (h : z < Om1) : vcSub f z = f z := by
  rw [vcSub, dif_neg (fun hz => absurd hz.1 (not_lt.2 h.le)), if_pos h]

theorem vcSub_Om1 (f : Ordinal.{0} → Ordinal.{0}) : vcSub f Om1 = Om1 := by
  rw [vcSub, dif_neg (fun hz => absurd hz.1 (lt_irrefl _)), if_neg (lt_irrefl _)]

theorem vcSub_big (f : Ordinal.{0} → Ordinal.{0}) {z : Ordinal.{0}} (h : ucB ≤ z) : vcSub f z = z := by
  have h1 : Om1 < z := (Uv.uv_E_lt_B.trans_le h) |> Rj.rj_Om1_lt_E.trans
  rw [vcSub, dif_neg (fun hz => absurd hz.2 (not_lt.2 h)), if_neg (not_lt.2 h1.le)]

theorem vcSub_cnf (f : Ordinal.{0} → Ordinal.{0}) {z : Ordinal.{0}} (h1 : Om1 < z) (hB : z < ucB)
    (hE : ω ^ z ≠ z) :
    vcSub f z = (if ω ^ log ω z = log ω z then vcSub f (log ω z) else Om1 * ω ^ vcSub f (log ω z - Om1)) *
      (z / ω ^ log ω z) + vcSub f (z % ω ^ log ω z) := by
  rw [vcSub, dif_pos ⟨h1, hB⟩, dif_neg hE]

theorem vcSub_phi (f : Ordinal.{0} → Ordinal.{0}) {z : Ordinal.{0}} (h1 : Om1 < z) (hB : z < ucB)
    (hE : ω ^ z = z) (hI : invVeblen₁ z < z) :
    vcSub f z = veblen (vcSub f (invVeblen₁ z)) (vcSub f (invVeblen₂ z)) := by
  rw [vcSub, dif_pos ⟨h1, hB⟩, dif_pos hE, dif_pos hI]

theorem vcSub_atom (f : Ordinal.{0} → Ordinal.{0}) {z : Ordinal.{0}} (h1 : Om1 < z) (hB : z < ucB)
    (hE : ω ^ z = z) (hI : ¬ invVeblen₁ z < z) :
    vcSub f z = ucRebuild (fun x => if x < z then vcSub f x else x) z := by
  rw [vcSub, dif_pos ⟨h1, hB⟩, dif_pos hE, dif_neg hI]
  rfl

theorem VcLv_small (P : Ordinal.{0} → Prop) {z : Ordinal.{0}} (h : z < Om1) : VcLv P z ↔ P z := by
  rw [VcLv, dif_neg (fun hz => absurd hz.1 (not_lt.2 h.le)), if_pos h]

theorem VcLv_Om1 (P : Ordinal.{0} → Prop) : VcLv P Om1 := by
  rw [VcLv, dif_neg (fun hz => absurd hz.1 (lt_irrefl _)), if_neg (lt_irrefl _)]; trivial

theorem VcLv_cnf (P : Ordinal.{0} → Prop) {z : Ordinal.{0}} (h1 : Om1 < z) (hB : z < ucB) (hE : ω ^ z ≠ z) :
    VcLv P z ↔ (if ω ^ log ω z = log ω z then VcLv P (log ω z) else VcLv P (log ω z - Om1)) ∧
      VcLv P (z % ω ^ log ω z) := by
  rw [VcLv, dif_pos ⟨h1, hB⟩, dif_neg hE]

theorem VcLv_phi (P : Ordinal.{0} → Prop) {z : Ordinal.{0}} (h1 : Om1 < z) (hB : z < ucB) (hE : ω ^ z = z)
    (hI : invVeblen₁ z < z) : VcLv P z ↔ VcLv P (invVeblen₁ z) ∧ VcLv P (invVeblen₂ z) := by
  rw [VcLv, dif_pos ⟨h1, hB⟩, dif_pos hE, dif_pos hI]

theorem VcLv_atom (P : Ordinal.{0} → Prop) {z : Ordinal.{0}} (h1 : Om1 < z) (hB : z < ucB) (hE : ω ^ z = z)
    (hI : ¬ invVeblen₁ z < z) : VcLv P z ↔ ∀ x ∈ ucParts z, x < z → VcLv P x := by
  rw [VcLv, dif_pos ⟨h1, hB⟩, dif_pos hE, dif_neg hI]
  refine forall₂_congr fun x _ => ?_
  by_cases hx : x < z
  · rw [dif_pos hx]; exact ⟨fun h _ => h, fun h => h hx⟩
  · rw [dif_neg hx]; exact ⟨fun _ h => absurd h hx, fun _ => trivial⟩

theorem VcLv_big (P : Ordinal.{0} → Prop) {z : Ordinal.{0}} (h : ucB ≤ z) : VcLv P z := by
  have h1 : Om1 < z := Rj.rj_Om1_lt_E.trans (Uv.uv_E_lt_B.trans_le h)
  rw [VcLv, dif_neg (fun hz => absurd hz.2 (not_lt.2 h)), if_neg (not_lt.2 h1.le)]; trivial

/-! ## The parts of an atom and the atom rebuilt -/

/-- **`ucMap` depends only on the components.** -/
theorem vc_map_congr (f g : Ordinal.{0} → Ordinal.{0}) :
    ∀ γ : Ordinal.{0}, (∀ x ∈ ucComps γ, f x = g x) → ucMap f γ = ucMap g γ := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hf
  by_cases h1 : γ < OmTwo
  · rw [ucMap_small f h1, ucMap_small g h1]; exact hf γ (by rw [ucComps_small h1]; exact mem_singleton _)
  by_cases h2 : γ < ucE
  · have h1' := not_lt.1 h1
    have hc := ucComps_big h1' h2
    rw [ucMap_big f h1' h2, ucMap_big g h1' h2,
      IH _ (uc_log_lt h1' h2) (fun x hx => hf x (by rw [hc]; exact Or.inl hx)),
      IH _ (uc_mod_lt h1') (fun x hx => hf x (by rw [hc]; exact Or.inr (Or.inr hx))),
      hf _ (by rw [hc]; exact Or.inr (Or.inl rfl))]
  · rw [ucMap_out f (not_lt.1 h2), ucMap_out g (not_lt.1 h2)]

/-- **The parts of an atom are below it.** -/
theorem vc_parts_lt {z : Ordinal.{0}} (h1 : Om1 < z) (hB : z < ucB) (hI : ¬ invVeblen₁ z < z) :
    ∀ x ∈ ucParts z, x < z := by
  have hSC : SC z := tl_SC_of h1 hI
  by_cases hX : z < tlX
  · obtain ⟨-, hyz, hlz⟩ := tl_nf hSC h1 hX
    rw [ucParts, if_pos hX]
    rintro x (hx | hx)
    · rw [hx]; exact hlz
    · rw [mem_singleton_iff] at hx; rw [hx]; exact hyz
  · have hne := uc_nf_of_lt hSC h1 hB
    obtain ⟨-, hlv, -, -, -⟩ := ucLev_spec hSC h1 hne
    obtain ⟨-, hyz⟩ := uc_nf hSC h1 hne
    rw [ucParts, if_neg hX]
    rintro x (hx | hx)
    · exact (le_ucC hx).trans_lt hlv
    · rw [mem_singleton_iff] at hx; rw [hx]; exact hyz

/-- **`ucRebuild` depends only on the values at the parts.** -/
theorem vc_rebuild_congr {f g : Ordinal.{0} → Ordinal.{0}} {z : Ordinal.{0}}
    (h : ∀ x ∈ ucParts z, f x = g x) : ucRebuild f z = ucRebuild g z := by
  unfold ucRebuild
  by_cases hX : z < tlX
  · rw [ucParts, if_pos hX] at h
    rw [if_pos hX, if_pos hX, h _ (mem_insert _ _), h _ (mem_insert_of_mem _ rfl)]
  · rw [ucParts, if_neg hX] at h
    rw [if_neg hX, if_neg hX, vc_map_congr f g _ (fun x hx => h x (mem_union_left _ hx)),
      h _ (mem_union_right _ (mem_singleton _))]

/-- **An atom rebuilt with a map fixing its parts is the atom.** -/
theorem vc_rebuild_self {f : Ordinal.{0} → Ordinal.{0}} {z : Ordinal.{0}} (h1 : Om1 < z) (hB : z < ucB)
    (hI : ¬ invVeblen₁ z < z) (h : ∀ x ∈ ucParts z, f x = x) : ucRebuild f z = z := by
  have hSC : SC z := tl_SC_of h1 hI
  unfold ucRebuild
  by_cases hX : z < tlX
  · rw [ucParts, if_pos hX] at h
    rw [if_pos hX, h _ (mem_insert _ _), h _ (mem_insert_of_mem _ rfl)]
    exact (tl_nf hSC h1 hX).1
  · have hne := uc_nf_of_lt hSC h1 hB
    rw [ucParts, if_neg hX] at h
    rw [if_neg hX, Uy.uy_map_fix f _ (fun x hx => h x (mem_union_left _ hx)),
      h _ (mem_union_right _ (mem_singleton _))]
    exact (uc_nf hSC h1 hne).1

/-! ## Monotonicity, congruence, the fixed case -/

/-- **`VcLv` is monotone in the predicate** (only the countable leaves matter). -/
theorem VcLv_mono {P Q : Ordinal.{0} → Prop} (hPQ : ∀ x, x < Om1 → P x → Q x) :
    ∀ z, VcLv P z → VcLv Q z := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hP
  rcases lt_or_ge z Om1 with hz | hz
  · exact (VcLv_small Q hz).2 (hPQ z hz ((VcLv_small P hz).1 hP))
  rcases hz.eq_or_lt with hz | h1
  · rw [← hz]; exact VcLv_Om1 Q
  rcases le_or_gt ucB z with hB | hB
  · exact VcLv_big Q hB
  by_cases hE : ω ^ z = z
  · by_cases hI : invVeblen₁ z < z
    · rw [VcLv_phi P h1 hB hE hI] at hP
      exact (VcLv_phi Q h1 hB hE hI).2 ⟨IH _ hI hP.1, IH _ (Tf.tf_inv2_lt hE) hP.2⟩
    · rw [VcLv_atom P h1 hB hE hI] at hP
      exact (VcLv_atom Q h1 hB hE hI).2 fun x hx hxz => IH x hxz (hP x hx hxz)
  · rw [VcLv_cnf P h1 hB hE] at hP
    have hlz := Tf.tf_log_lt h1 hE
    refine (VcLv_cnf Q h1 hB hE).2 ⟨?_, IH _ (Rj.rj_mod_lt (Rj.rj_Om1_pos.trans h1).ne') hP.2⟩
    have hP1 := hP.1
    by_cases hl : ω ^ log ω z = log ω z
    · rw [if_pos hl] at hP1 ⊢; exact IH _ hlz hP1
    · rw [if_neg hl] at hP1 ⊢; exact IH _ ((Ordinal.sub_le_self _ _).trans_lt hlz) hP1

theorem VcLv_and {P Q : Ordinal.{0} → Prop} :
    ∀ z, VcLv P z → VcLv Q z → VcLv (fun x => P x ∧ Q x) z := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hP hQ
  rcases lt_or_ge z Om1 with hz | hz
  · exact (VcLv_small _ hz).2 ⟨(VcLv_small P hz).1 hP, (VcLv_small Q hz).1 hQ⟩
  rcases hz.eq_or_lt with hz | h1
  · rw [← hz]; exact VcLv_Om1 _
  rcases le_or_gt ucB z with hB | hB
  · exact VcLv_big _ hB
  by_cases hE : ω ^ z = z
  · by_cases hI : invVeblen₁ z < z
    · rw [VcLv_phi P h1 hB hE hI] at hP
      rw [VcLv_phi Q h1 hB hE hI] at hQ
      exact (VcLv_phi _ h1 hB hE hI).2 ⟨IH _ hI hP.1 hQ.1, IH _ (Tf.tf_inv2_lt hE) hP.2 hQ.2⟩
    · rw [VcLv_atom P h1 hB hE hI] at hP
      rw [VcLv_atom Q h1 hB hE hI] at hQ
      exact (VcLv_atom _ h1 hB hE hI).2 fun x hx hxz => IH x hxz (hP x hx hxz) (hQ x hx hxz)
  · rw [VcLv_cnf P h1 hB hE] at hP
    rw [VcLv_cnf Q h1 hB hE] at hQ
    have hlz := Tf.tf_log_lt h1 hE
    refine (VcLv_cnf _ h1 hB hE).2
      ⟨?_, IH _ (Rj.rj_mod_lt (Rj.rj_Om1_pos.trans h1).ne') hP.2 hQ.2⟩
    have hP1 := hP.1
    have hQ1 := hQ.1
    by_cases hl : ω ^ log ω z = log ω z
    · rw [if_pos hl] at hP1 hQ1 ⊢; exact IH _ hlz hP1 hQ1
    · rw [if_neg hl] at hP1 hQ1 ⊢; exact IH _ ((Ordinal.sub_le_self _ _).trans_lt hlz) hP1 hQ1

/-- **`vcSub` depends only on the values at the leaves.** -/
theorem vcSub_congr {f g : Ordinal.{0} → Ordinal.{0}} :
    ∀ z, VcLv (fun x => f x = g x) z → vcSub f z = vcSub g z := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hP
  rcases lt_or_ge z Om1 with hz | hz
  · rw [vcSub_small f hz, vcSub_small g hz]; exact (VcLv_small _ hz).1 hP
  rcases hz.eq_or_lt with hz | h1
  · rw [← hz, vcSub_Om1, vcSub_Om1]
  rcases le_or_gt ucB z with hB | hB
  · rw [vcSub_big f hB, vcSub_big g hB]
  by_cases hE : ω ^ z = z
  · by_cases hI : invVeblen₁ z < z
    · rw [VcLv_phi _ h1 hB hE hI] at hP
      rw [vcSub_phi f h1 hB hE hI, vcSub_phi g h1 hB hE hI, IH _ hI hP.1, IH _ (Tf.tf_inv2_lt hE) hP.2]
    · rw [VcLv_atom _ h1 hB hE hI] at hP
      rw [vcSub_atom f h1 hB hE hI, vcSub_atom g h1 hB hE hI]
      have hplt := vc_parts_lt h1 hB hI
      exact vc_rebuild_congr fun x hx => by
        rw [if_pos (hplt x hx), if_pos (hplt x hx)]; exact IH x (hplt x hx) (hP x hx (hplt x hx))
  · rw [VcLv_cnf _ h1 hB hE] at hP
    have hlz := Tf.tf_log_lt h1 hE
    rw [vcSub_cnf f h1 hB hE, vcSub_cnf g h1 hB hE, IH _ (Rj.rj_mod_lt (Rj.rj_Om1_pos.trans h1).ne') hP.2]
    have hP1 := hP.1
    by_cases hl : ω ^ log ω z = log ω z
    · rw [if_pos hl] at hP1; simp only [if_pos hl]; rw [IH _ hlz hP1]
    · rw [if_neg hl] at hP1; simp only [if_neg hl]; rw [IH _ ((Ordinal.sub_le_self _ _).trans_lt hlz) hP1]

/-- **A map fixing every leaf fixes the code**: `vcSub f z = z`. -/
theorem vcSub_fix {f : Ordinal.{0} → Ordinal.{0}} :
    ∀ z, VcLv (fun x => f x = x) z → vcSub f z = z := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hP
  rcases lt_or_ge z Om1 with hz | hz
  · rw [vcSub_small f hz]; exact (VcLv_small (fun x => f x = x) hz).1 hP
  rcases hz.eq_or_lt with hz | h1
  · rw [← hz, vcSub_Om1]
  rcases le_or_gt ucB z with hB | hB
  · rw [vcSub_big f hB]
  by_cases hE : ω ^ z = z
  · by_cases hI : invVeblen₁ z < z
    · rw [VcLv_phi _ h1 hB hE hI] at hP
      rw [vcSub_phi f h1 hB hE hI, IH _ hI hP.1, IH _ (Tf.tf_inv2_lt hE) hP.2,
        veblen_invVeblen₁_invVeblen₂, hE]
    · rw [VcLv_atom _ h1 hB hE hI] at hP
      rw [vcSub_atom f h1 hB hE hI]
      have hplt := vc_parts_lt h1 hB hI
      exact vc_rebuild_self h1 hB hI fun x hx => by
        rw [if_pos (hplt x hx)]; exact IH x (hplt x hx) (hP x hx (hplt x hx))
  · rw [VcLv_cnf _ h1 hB hE] at hP
    have hz0 : z ≠ 0 := (Rj.rj_Om1_pos.trans h1).ne'
    have hlz := Tf.tf_log_lt h1 hE
    rw [vcSub_cnf f h1 hB hE, IH _ (Rj.rj_mod_lt hz0) hP.2]
    have hP1 := hP.1
    have hw : (if ω ^ log ω z = log ω z then vcSub f (log ω z) else Om1 * ω ^ vcSub f (log ω z - Om1)) =
        ω ^ log ω z := by
      by_cases hl : ω ^ log ω z = log ω z
      · rw [if_pos hl] at hP1 ⊢; rw [IH _ hlz hP1, hl]
      · rw [if_neg hl] at hP1 ⊢
        rw [IH _ ((Ordinal.sub_le_self _ _).trans_lt hlz) hP1, Si.si_Om1_opow_eq,
          Ordinal.add_sub_cancel_of_le (Si.si_Om1_le_log h1.le)]
    rw [hw]; exact (Si.si_dec hz0).1

/-! ## The data is the largest leaf -/

/-- `ucDat(−Ω₁ + l) = ucDat l` for `Ω₁ ≤ l < B₂`. -/
theorem vc_dat_sub {l : Ordinal.{0}} (hl1 : Om1 ≤ l) (hB : l < ucB) : ucDat (l - Om1) = ucDat l := by
  obtain ⟨b, rfl⟩ : ∃ b, l = Om1 + b := ⟨l - Om1, (Ordinal.add_sub_cancel_of_le hl1).symm⟩
  rw [Ordinal.add_sub_cancel]
  rcases lt_or_ge b Om1 with hb | hb
  · rw [Uy.uy_dat_Om1_add_small hb, ucDat_small hb]
  · rw [Uy.uy_dat_Om1_add hb hB]

/-- **The data of a code is below an `ε`-number `κ` iff every leaf is** (`ucDat` drops finite coefficients and the
`1 +` of `Γ_{Ω₁+1+d}`, which `κ > ω` absorbs). -/
theorem vc_dat_lt {κ : Ordinal.{0}} (hκ : InE κ) :
    ∀ z, z < ucB → (VcLv (· < κ) z ↔ ucDat z < κ) := by
  have hκ0 : (0 : Ordinal.{0}) < κ := Si.si_inE_pos hκ
  have hωκ : ω ≤ κ := by
    have h1 : ω ≤ ω ^ κ := left_le_opow ω hκ0
    have h2 : ω ^ κ = κ := hκ
    exact h2 ▸ h1
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hB
  rcases lt_or_ge z Om1 with hz | hz
  · rw [VcLv_small _ hz, ucDat_small hz]
  rcases hz.eq_or_lt with hz | h1
  · rw [← hz, ucDat_Om1]; exact ⟨fun _ => hκ0, fun _ => VcLv_Om1 _⟩
  by_cases hE : ω ^ z = z
  · by_cases hI : invVeblen₁ z < z
    · rw [VcLv_phi _ h1 hB hE hI, Uy.uy_dat_phi h1 hB hE hI, max_lt_iff,
        IH _ hI (hI.trans hB), IH _ (Tf.tf_inv2_lt hE) ((Tf.tf_inv2_lt hE).trans hB)]
    have hplt := vc_parts_lt h1 hB hI
    rw [VcLv_atom _ h1 hB hE hI]
    have hiff : (∀ x ∈ ucParts z, x < z → VcLv (· < κ) x) ↔ ∀ x ∈ ucParts z, ucDat x < κ :=
      forall₂_congr fun x hx => by
        rw [IH x (hplt x hx) ((hplt x hx).trans hB)]; exact ⟨fun h => h (hplt x hx), fun h _ => h⟩
    rw [hiff]
    have hSC : SC z := tl_SC_of h1 hI
    by_cases hX : z < tlX
    · rw [ucParts, if_pos hX, ucDat_lt_X hX]
      by_cases h0 : tlLev z = 0
      · rw [tlDat_atom0 h1 hX hE hI h0, h0, tlI_zero]
        set ν := Tf.tfIdx z with hνdef
        have hνz : ν < z := by
          have := (tl_nf hSC h1 hX).2.1; rwa [h0, tlI_zero] at this
        have hgz : gamma ν = z := Tf.tf_SC_gamma h1 hI
        have hν1 : Om1 < ν := Tf.tf_Om1_lt_gamma.1 (by rw [hgz]; exact h1)
        have hdX : ν - (Om1 + 1) < tlX := ((Ordinal.sub_le_self _ _).trans_lt hνz).trans hX
        rw [← ucDat_lt_X hdX]
        have hall : (∀ x ∈ ({0, ν} : Set Ordinal.{0}), ucDat x < κ) ↔ ucDat ν < κ := by
          refine ⟨fun h => h ν (mem_insert_of_mem _ rfl), fun h x hx => ?_⟩
          rcases hx with hx | hx
          · rw [hx, ucDat_small Rj.rj_Om1_pos]; exact hκ0
          · rw [mem_singleton_iff] at hx; rw [hx]; exact h
        rw [hall, ← vc_dat_sub hν1.le (hνz.trans hB), ← Ordinal.sub_sub]
        set c := ν - Om1 with hcdef
        have hc0 : c ≠ 0 := by
          intro e
          have : Om1 + c = ν := Ordinal.add_sub_cancel_of_le hν1.le
          rw [e, add_zero] at this; exact absurd this hν1.ne
        rcases lt_or_ge c ω with hcω | hcω
        · have hc1 : c < Om1 := hcω.trans (omega0_lt_inE Rj.rj_Om1_inE)
          have hd1 : c - 1 < Om1 := (Ordinal.sub_le_self _ _).trans_lt hc1
          rw [ucDat_small hc1, ucDat_small hd1]
          exact ⟨fun _ => ((Ordinal.sub_le_self _ _).trans_lt hcω).trans_le hωκ,
            fun _ => hcω.trans_le hωκ⟩
        · have h1c : 1 + (c - 1) = c := Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 hc0)
          have hdω : ω ≤ c - 1 := by
            by_contra hlt
            push Not at hlt
            have : 1 + (c - 1) < ω := (isPrincipal_add_omega0) one_lt_omega0 hlt
            rw [h1c] at this; exact absurd hcω (not_le.2 this)
          rw [Ordinal.one_add_of_omega0_le hdω] at h1c
          rw [h1c]
      · have hdz := tlDat_atomF h1 hX hE hI h0
        obtain ⟨-, hyz, hlz⟩ := tl_nf hSC h1 hX
        rw [hdz, max_lt_iff, ← ucDat_lt_X (hlz.trans hX), ← ucDat_lt_X (hyz.trans hX)]
        constructor
        · intro h; exact ⟨h _ (mem_insert _ _), h _ (mem_insert_of_mem _ rfl)⟩
        · rintro ⟨ha, hb⟩ x (hx | hx)
          · rw [hx]; exact ha
          · rw [mem_singleton_iff] at hx; rw [hx]; exact hb
    · rw [ucParts, if_neg hX, ucDat_atom (not_lt.1 hX) hB hE hI, max_lt_iff, ucFold_lt_iff ucDat hκ0]
      constructor
      · intro h; exact ⟨fun x hx => h x (mem_union_left _ hx), h _ (mem_union_right _ (mem_singleton _))⟩
      · rintro ⟨ha, hb⟩ x (hx | hx)
        · exact ha x hx
        · rw [mem_singleton_iff] at hx; rw [hx]; exact hb
  · have hlz := Tf.tf_log_lt h1 hE
    have hrz := Rj.rj_mod_lt (Rj.rj_Om1_pos.trans h1).ne'
    rw [VcLv_cnf _ h1 hB hE, Uy.uy_dat_cnf h1 hB hE, max_lt_iff, IH _ hrz (hrz.trans hB)]
    by_cases hl : ω ^ log ω z = log ω z
    · rw [if_pos hl, IH _ hlz (hlz.trans hB)]
    · have hbz : log ω z - Om1 < z := (Ordinal.sub_le_self _ _).trans_lt hlz
      rw [if_neg hl, IH _ hbz (hbz.trans hB), vc_dat_sub (Si.si_Om1_le_log h1.le) (hlz.trans hB)]

/-! ## The base change on codes -/

/-- `π(x·k) = π(x)·k` for finite `k`. -/
theorem vc_mul_nat {σ τ x : Ordinal.{0}} (h : Bases σ τ) (hx : x ∈ TB τ σ) :
    ∀ k : ℕ, x * (k : Ordinal.{0}) ∈ TB τ σ ∧ pi σ τ (x * (k : Ordinal.{0})) = pi σ τ x * (k : Ordinal.{0}) := by
  intro k
  induction k with
  | zero =>
    have h0σ : (0 : Ordinal.{0}) < σ := Si.si_inE_pos h.1
    simp only [Nat.cast_zero, mul_zero]; exact ⟨mem_TB_of_lt h h0σ, pi_lt h h0σ⟩
  | succ k ihk =>
    obtain ⟨c1, c2⟩ := pi_add h ihk.1 hx
    rw [Nat.cast_succ, mul_add_one, mul_add_one]; exact ⟨c1, by rw [c2, ihk.2]⟩

/-- `ε_{Ω₁+1} ∈ Tᵗ[σ]` and `π(ε_{Ω₁+1}) = ε_{Ω₁+1}` (data `1`). -/
theorem vc_pi_E {σ τ : Ordinal.{0}} (h : Bases σ τ) : Gg.ggE ∈ TB τ σ ∧ pi σ τ Gg.ggE = Gg.ggE := by
  have hd : ucDat Gg.ggE = 1 := by rw [← Uv.uv_Om1_mul_E]; exact Uv.uvDat_E
  exact Uy.uy_pi_fix h _ Uv.uv_E_lt_B (by rw [hd]; exact Ub.ub_one_lt h.1)

/-- `Ω₁ + x = x` for `x ≥ ε_{Ω₁+1}`. -/
theorem vc_Om1_add_big {x : Ordinal.{0}} (hx : Gg.ggE ≤ x) : Om1 + x = x :=
  Ordinal.add_of_omega0_opow_le (by rw [Gg.ggE_spec.1]; exact Rj.rj_Om1_lt_E) (by rw [Gg.ggE_spec.1]; exact hx)

/-- **THE BASE CHANGE ON CODES**: for bases `σ < τ` and `z < B₂` whose leaves lie in `Tᵗ[σ]`: `z ∈ Tᵗ[σ]` and
`π_{σ,τ}(z) = vcSub π_{σ,τ} z` (every leaf moved by `π`, the shape kept). -/
theorem vc_pi {σ τ : Ordinal.{0}} (h : Bases σ τ) :
    ∀ z, z < ucB → VcLv (· ∈ TB τ σ) z → z ∈ TB τ σ ∧ pi σ τ z = vcSub (pi σ τ) z := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hB hL
  rcases lt_or_ge z Om1 with hz | hz
  · rw [vcSub_small _ hz]; exact ⟨(VcLv_small _ hz).1 hL, rfl⟩
  rcases hz.eq_or_lt with hz | h1
  · rw [← hz, vcSub_Om1]; exact pi_Om1 h
  by_cases hE : ω ^ z = z
  · by_cases hI : invVeblen₁ z < z
    · -- an `ε`-number `z = φ(a, c)`
      set a := invVeblen₁ z with hadef
      set c := invVeblen₂ z with hcdef
      have hcz : c < z := Tf.tf_inv2_lt hE
      have hev : veblen a c = z := by rw [hadef, hcdef, veblen_invVeblen₁_invVeblen₂, hE]
      have ha0 : a ≠ 0 := by
        intro e
        rw [e, veblen_zero_apply] at hev
        have : ω ^ c = ω ^ z := by rw [hev, hE]
        exact absurd ((opow_right_inj one_lt_omega0).1 this) hcz.ne
      rw [VcLv_phi _ h1 hB hE hI] at hL
      obtain ⟨haT, haπ⟩ := IH a hI (hI.trans hB) hL.1
      obtain ⟨hcT, hcπ⟩ := IH c hcz (hcz.trans hB) hL.2
      have hP := ucPhi_TB h (one_le_iff_ne_zero.2 ha0) (by rw [hev]; exact hI) (by rw [hev]; exact hcz)
        (by rw [hev]; exact h1) (by rw [hev]; exact hB)
      rw [hev] at hP
      refine ⟨hP.1.2 ⟨haT, hcT⟩, ?_⟩
      rw [hP.2 haT hcT, haπ, hcπ, vcSub_phi _ h1 hB hE hI]
    · -- an atom
      have hSC : SC z := tl_SC_of h1 hI
      have hA := ucAtom_TB h hSC h1 hB
      have hplt := vc_parts_lt h1 hB hI
      rw [VcLv_atom _ h1 hB hE hI] at hL
      have hall : ∀ x ∈ ucParts z, x ∈ TB τ σ ∧ pi σ τ x = vcSub (pi σ τ) x := fun x hx =>
        IH x (hplt x hx) ((hplt x hx).trans hB) (hL x hx (hplt x hx))
      refine ⟨hA.1.2 fun x hx => (hall x hx).1, ?_⟩
      rw [hA.2 (fun x hx => (hall x hx).1), vcSub_atom _ h1 hB hE hI]
      exact vc_rebuild_congr fun x hx => by rw [if_pos (hplt x hx)]; exact (hall x hx).2
  · -- not an `ε`-number: `z = ω^l·k + r`
    have hz0 : z ≠ 0 := (Rj.rj_Om1_pos.trans h1).ne'
    obtain ⟨hdec, -, hvω, -⟩ := Si.si_dec hz0
    have hl1 : Om1 ≤ log ω z := Si.si_Om1_le_log h1.le
    have hlz : log ω z < z := Tf.tf_log_lt h1 hE
    have hrz : z % ω ^ log ω z < z := Rj.rj_mod_lt hz0
    have hwz : ω ^ log ω z ≤ z := opow_log_le_self ω hz0
    rw [VcLv_cnf _ h1 hB hE] at hL
    obtain ⟨hrT, hrπ⟩ := IH _ hrz (hrz.trans hB) hL.2
    have hw : ω ^ log ω z ∈ TB τ σ ∧ pi σ τ (ω ^ log ω z) =
        (if ω ^ log ω z = log ω z then vcSub (pi σ τ) (log ω z)
          else Om1 * ω ^ vcSub (pi σ τ) (log ω z - Om1)) := by
      have hL1 := hL.1
      by_cases hl : ω ^ log ω z = log ω z
      · rw [if_pos hl] at hL1 ⊢; rw [hl]; exact IH _ hlz (hlz.trans hB) hL1
      · rw [if_neg hl] at hL1 ⊢
        have hbz : log ω z - Om1 < z := (Ordinal.sub_le_self _ _).trans_lt hlz
        obtain ⟨hbT, hbπ⟩ := IH _ hbz (hbz.trans hB) hL1
        have hbl : Om1 + (log ω z - Om1) = log ω z := Ordinal.add_sub_cancel_of_le hl1
        have hwl : ω ^ log ω z = Om1 * ω ^ (log ω z - Om1) := by rw [Si.si_Om1_opow_eq, hbl]
        rcases lt_or_ge (log ω z) Gg.ggE with hlE | hlE
        · have hbE : ∀ e : Ordinal.{0}, InE e → Om1 < e → log ω z - Om1 < e := fun e he he1 =>
            ((Ordinal.sub_le_self _ _).trans_lt hlE).trans_le (Gg.ggE_le he (by rw [← Rj.rj_Om1]; exact he1))
          obtain ⟨o1, o2⟩ := om1_opow_TB_all h hbE
          rw [hwl]; exact ⟨o1.2 hbT, by rw [o2 hbT, hbπ]⟩
        · have hbeq : log ω z - Om1 = log ω z := by
            conv_lhs => rw [← vc_Om1_add_big hlE]
            exact Ordinal.add_sub_cancel _ _
          rw [hbeq] at hbT hbπ ⊢
          obtain ⟨o1, o2⟩ := ucOpow_TB h hlE hl (hwz.trans_lt hB)
          refine ⟨o1.2 hbT, ?_⟩
          obtain ⟨hET, hEπ⟩ := vc_pi_E h
          have hle : Gg.ggE ≤ pi σ τ (log ω z) := by
            rw [← hEπ]; exact ((pi_bijOn h).2.le_iff_le hET hbT).2 hlE
          rw [o2 hbT, Si.si_Om1_opow_eq, ← hbπ, vc_Om1_add_big hle]
    obtain ⟨k, hk⟩ := Ordinal.lt_omega0.1 hvω
    have hm := vc_mul_nat h hw.1 k
    obtain ⟨c1, c2⟩ := pi_add h hm.1 hrT
    have e : ω ^ log ω z * (k : Ordinal.{0}) + z % ω ^ log ω z = z := by rw [← hk]; exact hdec
    rw [vcSub_cnf _ h1 hB hE, ← hw.2, hk, ← hm.2, ← hrπ, ← c2, e]
    exact ⟨e ▸ c1, rfl⟩

/-- **The converse**: every leaf of a code `z ∈ Tᵗ[σ]` below `B₂` lies in `Tᵗ[σ]`. -/
theorem vc_lv_TB {σ τ : Ordinal.{0}} (h : Bases σ τ) :
    ∀ z, z < ucB → z ∈ TB τ σ → VcLv (· ∈ TB τ σ) z := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hB hT
  rcases lt_or_ge z Om1 with hz | hz
  · exact (VcLv_small _ hz).2 hT
  rcases hz.eq_or_lt with hz | h1
  · rw [← hz]; exact VcLv_Om1 _
  have hτz : τ ≤ z := (h.2.2.2.trans h1).le
  by_cases hE : ω ^ z = z
  · by_cases hI : invVeblen₁ z < z
    · have hcz : invVeblen₂ z < z := Tf.tf_inv2_lt hE
      have hev : veblen (invVeblen₁ z) (invVeblen₂ z) = z := by rw [veblen_invVeblen₁_invVeblen₂, hE]
      have ha0 : invVeblen₁ z ≠ 0 := by
        intro e
        rw [e, veblen_zero_apply] at hev
        have : ω ^ invVeblen₂ z = ω ^ z := by rw [hev, hE]
        exact absurd ((opow_right_inj one_lt_omega0).1 this) hcz.ne
      have hP := ucPhi_TB h (one_le_iff_ne_zero.2 ha0) (by rw [hev]; exact hI) (by rw [hev]; exact hcz)
        (by rw [hev]; exact h1) (by rw [hev]; exact hB)
      rw [hev] at hP
      obtain ⟨haT, hcT⟩ := hP.1.1 hT
      exact (VcLv_phi _ h1 hB hE hI).2 ⟨IH _ hI (hI.trans hB) haT, IH _ hcz (hcz.trans hB) hcT⟩
    · have hA := ucAtom_TB h (tl_SC_of h1 hI) h1 hB
      exact (VcLv_atom _ h1 hB hE hI).2 fun x hx hxz => IH x hxz (hxz.trans hB) (hA.1.1 hT x hx)
  · have hz0 : z ≠ 0 := (Rj.rj_Om1_pos.trans h1).ne'
    have hl1 : Om1 ≤ log ω z := Si.si_Om1_le_log h1.le
    have hlz : log ω z < z := Tf.tf_log_lt h1 hE
    have hrz : z % ω ^ log ω z < z := Rj.rj_mod_lt hz0
    have hwz : ω ^ log ω z ≤ z := opow_log_le_self ω hz0
    have hcomps := Si.si_comps_cons hz0
    have hwT : ω ^ log ω z ∈ TB τ σ := Si.siTB_of_comps h hT hτz (fun p hp => by
      rw [comps_opow, List.mem_singleton] at hp
      rw [hcomps, hp]; exact List.mem_cons_self ..)
    have hrT : z % ω ^ log ω z ∈ TB τ σ :=
      Si.siTB_of_comps h hT hτz (fun p hp => by rw [hcomps]; exact List.mem_cons_of_mem _ hp)
    refine (VcLv_cnf _ h1 hB hE).2 ⟨?_, IH _ hrz (hrz.trans hB) hrT⟩
    by_cases hl : ω ^ log ω z = log ω z
    · rw [if_pos hl]; rw [hl] at hwT; exact IH _ hlz (hlz.trans hB) hwT
    · rw [if_neg hl]
      have hbz : log ω z - Om1 < z := (Ordinal.sub_le_self _ _).trans_lt hlz
      have hbl : Om1 + (log ω z - Om1) = log ω z := Ordinal.add_sub_cancel_of_le hl1
      have hwl : ω ^ log ω z = Om1 * ω ^ (log ω z - Om1) := by rw [Si.si_Om1_opow_eq, hbl]
      rcases lt_or_ge (log ω z) Gg.ggE with hlE | hlE
      · have hbE : ∀ e : Ordinal.{0}, InE e → Om1 < e → log ω z - Om1 < e := fun e he he1 =>
          ((Ordinal.sub_le_self _ _).trans_lt hlE).trans_le (Gg.ggE_le he (by rw [← Rj.rj_Om1]; exact he1))
        rw [hwl] at hwT
        exact IH _ hbz (hbz.trans hB) ((om1_opow_TB_all h hbE).1.1 hwT)
      · have hbeq : log ω z - Om1 = log ω z := by
          conv_lhs => rw [← vc_Om1_add_big hlE]
          exact Ordinal.add_sub_cancel _ _
        rw [hbeq]
        exact IH _ hlz (hlz.trans hB) ((ucOpow_TB h hlE hl (hwz.trans_lt hB)).1.1 hwT)

/-- **Membership in `Tᵗ[σ]` is decided by the leaves.** -/
theorem vc_TB_iff {σ τ z : Ordinal.{0}} (h : Bases σ τ) (hB : z < ucB) :
    z ∈ TB τ σ ↔ VcLv (· ∈ TB τ σ) z :=
  ⟨vc_lv_TB h z hB, fun hL => (vc_pi h z hB hL).1⟩

/-- **`π_{σ,τ} = vcSub π_{σ,τ}` on `Tᵗ[σ] ∩ B₂`.** -/
theorem vc_pi_TB {σ τ z : Ordinal.{0}} (h : Bases σ τ) (hB : z < ucB) (hT : z ∈ TB τ σ) :
    pi σ τ z = vcSub (pi σ τ) z :=
  (vc_pi h z hB (vc_lv_TB h z hB hT)).2

/-- **`Uy.uy_pi_fix` from `vc_pi`**: data `< σ` ⇒ `z ∈ Tᵗ[σ]`, `π z = z`. -/
theorem vc_pi_fix {σ τ z : Ordinal.{0}} (h : Bases σ τ) (hB : z < ucB) (hd : ucDat z < σ) :
    z ∈ TB τ σ ∧ pi σ τ z = z := by
  have hL : VcLv (· < σ) z := (vc_dat_lt h.1 z hB).2 hd
  obtain ⟨hT, hπ⟩ := vc_pi h z hB (VcLv_mono (fun x _ hx => mem_TB_of_lt h hx) z hL)
  exact ⟨hT, hπ.trans (vcSub_fix z (VcLv_mono (fun x _ hx => pi_lt h hx) z hL))⟩

end Googology.Trans.PoR.InaccPsi.R2.Vc

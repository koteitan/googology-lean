import Googology.Trans.PoR.InaccPsi.R2.XiPast
import Googology.Trans.PoR.InaccPsi.R2.CitedXc

/-!
# XiImg: LEMMA IMG AT EVERY POINT OF `Tᵖ ∩ Ω₁`, FROM [W07b] CLAIM 5.6

In a restart context `RstK ρ τ δ` and for a copy `f` (`ImgCtx ρ A f`, `σ = f ρ`), Lemma IMG at a point `e` says
`π_{σ,ρ}(e) ≤ f(e)`.  For an `ε`-number `e ∈ Tᵖ ∩ (ρ, Ω₁)` let `τ'` be its greatest `<₁`-predecessor in `[ρ, e)`
(or `ρ`; [W07b] Def 5.8, `R2.le1R_loc`), so that `e` is `τ'`-`≤₁`-minimal, and let `X`, `Z` be the sets of [W07b]
Claim 5.6 (`R2.claim56pw`).  If `f(e) < π(e)`, then `h := π⁻¹ ∘ f` is a covering of `X ∪ Z` (it keeps `<`, `+` and
`≤₁`: `f` keeps them on `A`, `≤₁` of `R₂` and of `R₁⁺` agree on `(ρ, δ]` and at the non-`υ`-points below `ρ`, and `π⁻¹`
keeps them on `T^σ`, `R2.down_le1R`) with `X ≤pw h[X]` (Lemma IMG below `e`), `h[X] < h[Z]`, and `h[Z] ≤ lh(u) < e` for
`u = h(e) ∈ (τ', e)` (`π` commutes with `lh`, `R2.lh_pi`, and `e` is `τ'`-minimal): Claim 5.6 says there is no such
covering.  No reach formula is needed.

* `xiPinv` (`π⁻¹` on `T^σ`) and its facts `xiPinv_spec`, `xiPinv_pi`, `xiPinv_lt`, `xiPinv_le`, `xiPinv_small`,
  `xiPinv_base`, `xiPinv_ge`, `xiPinv_add`, `xiPinv_lt_Om1`, `xiPinv_le1R`;
* `xi_base` (the base `τ'`), `xi_gnI_fin` (witness sets for finitely many points);
* `xi_img_eps` (**LEMMA IMG AT AN `ε`-NUMBER, GIVEN IT BELOW**), `xi_img_rho`, `xi_img_all` (**LEMMA IMG AT EVERY POINT
  OF `Tᵖ ∩ Ω₁`**), `xi_imgAll` (**`Xi.XiImgAll`**).

No new axiom (it uses `R2.claim56pw`).  New definition: `xiPinv`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xi

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2

open Classical in
/-- `π_{σ,ρ}⁻¹` on `T^σ`. -/
noncomputable def xiPinv (σ ρ y : Ordinal.{0}) : Ordinal.{0} :=
  if hy : ∃ u, u ∈ TB ρ σ ∧ pi σ ρ u = y then Classical.choose hy else y

section Pinv

variable {σ ρ : Ordinal.{0}} (hB : Bases σ ρ)
include hB

theorem xiPinv_spec {y : Ordinal.{0}} (hy : y ∈ Tset σ) : xiPinv σ ρ y ∈ TB ρ σ ∧ pi σ ρ (xiPinv σ ρ y) = y := by
  have hex : ∃ u, u ∈ TB ρ σ ∧ pi σ ρ u = y := (pi_bijOn hB).1.surjOn hy
  unfold xiPinv
  rw [dif_pos hex]
  exact Classical.choose_spec hex

theorem xiPinv_pi {u : Ordinal.{0}} (hu : u ∈ TB ρ σ) : xiPinv σ ρ (pi σ ρ u) = u := by
  have hT : pi σ ρ u ∈ Tset σ := (pi_bijOn hB).1.mapsTo hu
  obtain ⟨h1, h2⟩ := xiPinv_spec hB hT
  exact (pi_bijOn hB).1.injOn h1 hu h2

theorem xiPinv_lt {y y' : Ordinal.{0}} (hy : y ∈ Tset σ) (hy' : y' ∈ Tset σ) (h : y < y') :
    xiPinv σ ρ y < xiPinv σ ρ y' := by
  obtain ⟨h1, h2⟩ := xiPinv_spec hB hy
  obtain ⟨h1', h2'⟩ := xiPinv_spec hB hy'
  by_contra hle
  push Not at hle
  have := (pi_bijOn hB).2.monotoneOn h1' h1 hle
  rw [h2, h2'] at this
  exact absurd h (not_lt.2 this)

theorem xiPinv_le {y y' : Ordinal.{0}} (hy : y ∈ Tset σ) (hy' : y' ∈ Tset σ) (h : y ≤ y') :
    xiPinv σ ρ y ≤ xiPinv σ ρ y' := by
  rcases h.lt_or_eq with h | rfl
  · exact (xiPinv_lt hB hy hy' h).le
  · exact le_rfl

theorem xiPinv_small {y : Ordinal.{0}} (hy : y < σ) : xiPinv σ ρ y = y := by
  have := xiPinv_pi hB (mem_TB_of_lt hB hy)
  rwa [pi_lt hB hy] at this

theorem xiPinv_base : xiPinv σ ρ σ = ρ := by
  have := xiPinv_pi hB (pi_base hB).1
  rwa [(pi_base hB).2] at this

theorem xi_sigma_T : σ ∈ Tset σ := by
  have := (pi_bijOn hB).1.mapsTo (pi_base hB).1
  rwa [(pi_base hB).2] at this

theorem xiPinv_ge {y : Ordinal.{0}} (hy : y ∈ Tset σ) (hσy : σ ≤ y) : ρ ≤ xiPinv σ ρ y := by
  exact (xiPinv_base hB).symm.le.trans (xiPinv_le hB (xi_sigma_T hB) hy hσy)

theorem xiPinv_add {y y' : Ordinal.{0}} (hy : y ∈ Tset σ) (hy' : y' ∈ Tset σ) :
    xiPinv σ ρ (y + y') = xiPinv σ ρ y + xiPinv σ ρ y' := by
  obtain ⟨h1, h2⟩ := xiPinv_spec hB hy
  obtain ⟨h1', h2'⟩ := xiPinv_spec hB hy'
  obtain ⟨hs, hps⟩ := pi_add hB h1 h1'
  rw [h2, h2'] at hps
  rw [← hps]
  exact xiPinv_pi hB hs

theorem xiPinv_lt_Om1 {y : Ordinal.{0}} (hy : y ∈ Tset σ) (hy1 : y < Om1) : xiPinv σ ρ y < Om1 := by
  obtain ⟨h1, h2⟩ := xiPinv_spec hB hy
  by_contra hle
  push Not at hle
  obtain ⟨hOT, hpO⟩ := pi_Om1 hB
  have := ((pi_bijOn hB).2.le_iff_le hOT h1).2 hle
  rw [hpO, h2] at this
  exact absurd hy1 (not_lt.2 this)

theorem xiPinv_le1R (hσ : UpsPt σ) (hρ : UpsPt ρ) {y y' : Ordinal.{0}} (hy : y ∈ Tset σ) (hy' : y' ∈ Tset σ)
    (hy1 : y < Om1) (h : le1R y y') : le1R (xiPinv σ ρ y) (xiPinv σ ρ y') := by
  obtain ⟨h1, h2⟩ := xiPinv_spec hB hy
  obtain ⟨h1', h2'⟩ := xiPinv_spec hB hy'
  refine (down_le1R hσ hρ hB h1 h1' (xiPinv_lt_Om1 hB hy hy1)).2 ?_
  rw [h2, h2']; exact h

end Pinv

section Img

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **The base of minimality**: the greatest `<₁`-predecessor `τ'` of `e` in `[ρ, e)` (or `ρ`). -/
theorem xi_base {e : Ordinal.{0}} (heT : e ∈ Tset ρ) (hρe : ρ < e) (he1 : e < Om1) (heI : Indec e) :
    ∃ τ', ρ ≤ τ' ∧ τ' < e ∧ InE τ' ∧ le1R τ' e ∧ e ∈ Tset τ' ∧ ∀ d, le1R d e → d < e → d ≤ τ' := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  obtain ⟨mρ, hρm, hmL, hmmin, hTm⟩ := T_inter_Om1 hρE hρ1
  have hem : e < mρ := (hTm e he1).1 heT
  obtain ⟨n, β, hβn, hρβ0, hmin0, hch⟩ := le1R_loc (Or.inr hρE) hρ1 heT hρe he1 heI
  have hβρ : ∀ i ≤ n, ρ < β i := by
    intro i
    induction i with
    | zero => exact fun _ => hρβ0
    | succ k ih => exact fun hk => (ih (Nat.le_of_succ_le hk)).trans (hch k (Nat.lt_of_succ_le hk)).1
  cases n with
  | zero =>
    rw [← hβn]
    refine ⟨ρ, le_rfl, hρβ0, hρE, h.ρU.2 _ hρβ0.le, ?_, hmin0⟩
    rw [hβn]; exact heT
  | succ k =>
    obtain ⟨hlt, hR, hmin⟩ := hch k (Nat.lt_succ_self k)
    rw [hβn] at hlt hR hmin
    have hρk : ρ < β k := hβρ k (Nat.le_succ k)
    have hk0 : 0 < β k := lt_of_le_of_lt zero_le hρk
    have hkk : β k * 2 ≤ e := by rw [mul_two_eq]; exact (heI.add_lt hlt hlt).le
    have hkE : InE (β k) := (le1R_two_iff hk0).1
      (le1R_of_le (by rw [mul_two_eq]; exact le_self_add) hkk hR)
    have hk1 : β k < Om1 := hlt.trans he1
    obtain ⟨m', hkm', hm'L, hm'min, hTm'⟩ := T_inter_Om1 hkE hk1
    have hem' : e < m' := by
      by_contra hle
      push Not at hle
      have := hmmin m' (hρk.trans hkm') hm'L
      exact absurd (hem.trans_le (this.trans hle)) (lt_irrefl _)
    exact ⟨β k, hρk.le, hlt, hkE, hR, (hTm' e he1).2 hem', hmin⟩

/-- Witness sets for finitely many points with Lemma IMG. -/
theorem xi_gnI_fin : ∀ s : Finset Ordinal.{0}, (∀ x ∈ s, Gn.GnI ρ δ x) →
    ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A →
      ↑Z ⊆ A → ImgCtx ρ A f → ∀ x ∈ s, x ∈ A ∧ x ∈ TB ρ (f ρ) ∧ pi (f ρ) ρ x ≤ f x := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => exact fun _ => ⟨∅, ∅, WZ.empty, fun _ _ _ _ _ x hx => absurd hx (Finset.notMem_empty x)⟩
  | @insert a s _ IH =>
    intro hs
    obtain ⟨W, Z, w, b⟩ := IH fun x hx => hs x (Finset.mem_insert_of_mem hx)
    obtain ⟨Wa, Za, wa, -, -, -, ba⟩ := Gn.gnI_use h (hs a (Finset.mem_insert_self a s))
    refine ⟨W ∪ Wa, Z ∪ Za, w.union wa, fun A f hW hZ C x hx => ?_⟩
    have hW1 : ↑W ⊆ A := fun y hy => hW (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 hy)))
    have hZ1 : ↑Z ⊆ A := fun y hy => hZ (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 hy)))
    have hW2 : ↑Wa ⊆ A := fun y hy => hW (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_coe.1 hy)))
    have hZ2 : ↑Za ⊆ A := fun y hy => hZ (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_coe.1 hy)))
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact ba A f hW2 hZ2 C
    · exact b A f hW1 hZ1 C x hx

/-- **LEMMA IMG AT AN `ε`-NUMBER `e ∈ Tᵖ ∩ (ρ, Ω₁)`**, given it below `e` ([W07b] Claim 5.6 at the base `τ'`). -/
theorem xi_img_eps {e : Ordinal.{0}} (heE : InE e) (hρe : ρ < e) (heT : e ∈ Tset ρ) (he1 : e < Om1)
    (IH : ∀ u, u < e → Gn.GnI ρ δ u) : Gn.GnI ρ δ e := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have heI : Indec e := inE_indec heE
  obtain ⟨m, -, hmL, -, hTm, hm1⟩ := T_next (Or.inr hρE) hρ1
  obtain ⟨τ', -, hτ'e, hτ'E, -, heT', hmin⟩ := xi_base h heT hρe he1 heI
  obtain ⟨l, hl, X, Z, hX, hZ, heZ, hlZ, hno⟩ :=
    claim56pw (Or.inr hτ'E) (hτ'e.trans he1) heT' hτ'e he1 heI hmin
  have hem : e < m := (hTm e he1).1 heT
  have hel : e ≤ l := le1R_le hl.1
  have hlh : ∀ a r, a < m → IsLh1 a r → r < m := by
    intro a r ham hr
    by_contra hle
    push Not at hle
    have h1 : le1R a m := le1R_of_le ham.le hle hr.1
    have h2 : le1R m (r + 1) := hmL (r + 1) (hle.trans le_self_add)
    exact absurd (hr.2 _ (le1R_trans h1 h2)) (not_le.2 (lt_add_one r))
  have hlm : l < m := hlh e l hem hl
  have hl1 : l < Om1 := hlm.trans hm1
  have hlT : l ∈ Tset ρ := (hTm l hl1).2 hlm
  have hlδ : l < δ := Gn.gn_lt_δ h hlT hl1
  have hδI := inE_indec h.δE
  -- the closed hull of `X ∪ Z ∪ {τ'}`, with the sums of two of its members
  set S0 : Finset Ordinal.{0} := insert τ' (X ∪ Z) with hS0
  obtain ⟨Cs, hSC, hCcl, hCb⟩ := exists_closed S0
  have hS0l : ∀ s ∈ S0, s ≤ l := by
    intro s hs
    rcases Finset.mem_insert.1 hs with rfl | hs
    · exact (hτ'e.trans_le hel).le
    rcases Finset.mem_union.1 hs with hs | hs
    · exact ((hX s hs).trans_le hel).le
    · exact (hZ s hs).2
  have hCl : ∀ c ∈ Cs, c ≤ l := fun c hc => by
    obtain ⟨s, hs, hcs⟩ := hCb c hc
    exact hcs.trans (hS0l s hs)
  set D : Finset Ordinal.{0} := Cs ∪ Finset.image₂ (· + ·) Cs Cs with hD
  have hDδ : ∀ d ∈ D, d < δ := by
    intro d hd
    rcases Finset.mem_union.1 hd with hd | hd
    · exact (hCl d hd).trans_lt hlδ
    · obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_image₂.1 hd
      exact hδI.add_lt ((hCl a ha).trans_lt hlδ) ((hCl b hb).trans_lt hlδ)
  set W1 := D.filter (fun d => ρ ≤ d) with hW1
  set Z1 := D.filter (fun d => d < ρ) with hZ1
  have hDWZ : ∀ d ∈ D, d ∈ W1 ∪ Z1 := fun d hd => by
    rcases le_or_gt ρ d with hρd | hdρ
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hd, hρd⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hd, hdρ⟩)
  have hCD : ∀ c ∈ Cs, c ∈ D := fun c hc => Finset.mem_union_left _ hc
  have w1 : WZ ρ δ W1 Z1 := by
    refine ⟨fun w hw => ⟨(Finset.mem_filter.1 hw).2, hDδ w (Finset.mem_filter.1 hw).1⟩,
      fun z hz => (Finset.mem_filter.1 hz).2, fun w hw => ?_⟩
    obtain ⟨hwD, hρw⟩ := Finset.mem_filter.1 hw
    have hw0 : w ≠ 0 := (lt_of_lt_of_le hρE.pos hρw).ne'
    by_cases hwC : w ∈ Cs
    · by_cases hdec : DecompR0 w
      · rcases hCcl w hwC hdec with h0 | ⟨y, hy, z, hz, hyw, hzw, hyz⟩
        · exact absurd h0 hw0
        · exact Or.inr ⟨y, hDWZ y (hCD y hy), z, hDWZ z (hCD z hz), hyw, hzw, hyz⟩
      · exact Or.inl hdec
    · rcases Finset.mem_union.1 hwD with hwC' | hw2
      · exact absurd hwC' hwC
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_image₂.1 hw2
      have hb0 : b ≠ 0 := fun h0 => hwC (by rw [← hab, h0, add_zero]; exact ha)
      have hbw : b ≠ w := fun e => hwC (e ▸ hb)
      refine Or.inr ⟨a, hDWZ a (hCD a ha), b, hDWZ b (hCD b hb), ?_, ?_, hab⟩
      · rw [← hab]; exact lt_add_of_pos_right a (pos_iff_ne_zero.2 hb0)
      · exact lt_of_le_of_ne (le_add_self.trans_eq hab) hbw
  -- witness sets for Lemma IMG at the points of `insert τ' X`
  obtain ⟨W2, Z2, w2, b2⟩ := xi_gnI_fin h (insert τ' X) fun x hx => IH x (by
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hτ'e
    · exact hX x hx)
  have heS : e ∈ S0 := Finset.mem_insert_of_mem (Finset.mem_union_right _ heZ)
  have hlS : l ∈ S0 := Finset.mem_insert_of_mem (Finset.mem_union_right _ hlZ)
  have heW1 : e ∈ W1 := Finset.mem_filter.2 ⟨hCD e (hSC heS), hρe.le⟩
  refine Gn.gnI_mk h (w1.union w2) (Finset.mem_union_left _ (Finset.mem_union_left _ heW1)) heT he1
    fun A f hWg hZg Cx => ?_
  have hWA1 : ∀ d ∈ W1, d ∈ A := fun d hd => hWg (Finset.mem_coe.2 (Finset.mem_union_left _ hd))
  have hZA1 : ∀ d ∈ Z1, d ∈ A := fun d hd =>
    hZg (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_union_left _ hd)))
  have hDA : ∀ d ∈ D, d ∈ A := fun d hd => by
    rcases Finset.mem_union.1 (hDWZ d hd) with h1 | h1
    · exact hWA1 d h1
    · exact hZA1 d h1
  have hSA : ∀ s ∈ S0, s ∈ A := fun s hs => hDA s (hCD s (hSC hs))
  have hW2A : ↑W2 ⊆ A := fun y hy => hWg (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_coe.1 hy)))
  have hZ2A : ↑Z2 ⊆ A := fun y hy =>
    hZg (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_coe.1 hy))))
  have hIMG := b2 A f hW2A hZ2A Cx
  have hB : Bases (f ρ) ρ := h.img_bases Cx
  have hσU : UpsPt (f ρ) := Cx.ups
  have hσE : InE (f ρ) := upsPt_inE hσU
  have hσ1 : f ρ < Om1 := hB.2.2.1.trans hρ1
  have heA : e ∈ A := hSA e heS
  have hlA : l ∈ A := hSA l hlS
  have heTB : e ∈ TB ρ (f ρ) :=
    Gn.gnI_TB h Cx heT (fun p hp => hZg (Finset.mem_coe.2 (Finset.mem_union_right _ hp)))
  by_contra hlt
  push Not at hlt
  obtain ⟨hOT, hpO⟩ := pi_Om1 hB
  have hpeT : pi (f ρ) ρ e ∈ Tset (f ρ) := (pi_bijOn hB).1.mapsTo heTB
  have hpe1 : pi (f ρ) ρ e < Om1 := by rw [← hpO]; exact (pi_bijOn hB).2 heTB hOT he1
  have hfeT : f e ∈ Tset (f ρ) := vz_T_down hσE hσ1 hpeT hpe1 hlt.le
  obtain ⟨hu0TB, hpu0⟩ := xiPinv_spec hB hfeT
  have hu0e : xiPinv (f ρ) ρ (f e) < e := by
    by_contra hle
    push Not at hle
    have := (pi_bijOn hB).2.monotoneOn heTB hu0TB hle
    rw [hpu0] at this
    exact absurd hlt (not_lt.2 this)
  have hfρe : f ρ < f e := Cx.mono Cx.rho heA hρe
  have hρu0 : ρ < xiPinv (f ρ) ρ (f e) := by
    have := xiPinv_lt hB (xi_sigma_T hB) hfeT hfρe
    rwa [xiPinv_base hB] at this
  have hu01 : xiPinv (f ρ) ρ (f e) < Om1 := hu0e.trans he1
  obtain ⟨l0, hl0, hl0TB, hpl0⟩ := lh_pi hB hu0TB hρu0 hu01
  rw [hpu0] at hpl0
  have hle1R : ∀ a b, a ∈ A → b ∈ A → ρ < a → b ≤ δ → le1R a b → le1R (f a) (f b) := by
    intro a b haA hbA hρa hbδ hab
    have hf1 := Cx.cov1 a haA b hbA ((h.lowδ a b hρa hbδ).2 hab)
    by_cases hU : UpsPt (f a)
    · exact hU.2 _ (Cx.mono.monotoneOn haA hbA (le1R_le hab))
    · exact (Cx.sk (f a) (Cx.low a haA) hU (f b)).1 hf1
  have hl0m : l0 < m := hlh _ l0 (hu0e.trans hem) hl0
  have hpl0T : pi (f ρ) ρ l0 ∈ Tset (f ρ) := (pi_bijOn hB).1.mapsTo hl0TB
  have hpl01 : pi (f ρ) ρ l0 < Om1 := by
    rw [← hpO]; exact (pi_bijOn hB).2 hl0TB hOT (hl0m.trans hm1)
  have hfl : f l ≤ pi (f ρ) ρ l0 := hpl0.2 _ (hle1R e l heA hlA hρe hlδ.le hl.1)
  have hflT : f l ∈ Tset (f ρ) := vz_T_down hσE hσ1 hpl0T hpl01 hfl
  have hfl1 : f l < Om1 := hfl.trans_lt hpl01
  have hfT : ∀ x ∈ A, x ≤ l → f x ∈ Tset (f ρ) := fun x hxA hxl =>
    vz_T_down hσE hσ1 hflT hfl1 (Cx.mono.monotoneOn hxA hlA hxl)
  have hgl : xiPinv (f ρ) ρ (f l) ≤ l0 := by
    have := xiPinv_le hB hflT hpl0T hfl
    rwa [xiPinv_pi hB hl0TB] at this
  have hpw : ∀ x ∈ insert τ' X, x ≤ xiPinv (f ρ) ρ (f x) := by
    intro x hx
    obtain ⟨hxA, hxTB, hπx⟩ := hIMG x hx
    have hxS : x ∈ S0 := by
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hx)
    have hpxT : pi (f ρ) ρ x ∈ Tset (f ρ) := (pi_bijOn hB).1.mapsTo hxTB
    have := xiPinv_le hB hpxT (hfT x hxA (hS0l x hxS)) hπx
    rwa [xiPinv_pi hB hxTB] at this
  have hτ'u0 : τ' < xiPinv (f ρ) ρ (f e) := by
    have hτ'A : τ' ∈ A := hSA τ' (Finset.mem_insert_self _ _)
    exact (hpw τ' (Finset.mem_insert_self _ _)).trans_lt (xiPinv_lt hB (hfT τ' hτ'A (hS0l τ'
      (Finset.mem_insert_self _ _))) hfeT (Cx.mono hτ'A heA hτ'e))
  have hl0e : l0 < e := by
    by_contra hle
    push Not at hle
    have := hmin _ (le1R_of_le hu0e.le hle hl0.1) hu0e
    exact absurd hτ'u0 (not_lt.2 this)
  have hXZ : ∀ x ∈ X ∪ Z, x ∈ A ∧ x ≤ l ∧ f x ∈ Tset (f ρ) := fun x hx => by
    have hxS : x ∈ S0 := Finset.mem_insert_of_mem hx
    exact ⟨hSA x hxS, hS0l x hxS, hfT x (hSA x hxS) (hS0l x hxS)⟩
  have hmono : StrictMonoOn (fun x => xiPinv (f ρ) ρ (f x)) ↑(X ∪ Z) := fun a ha b hb hab =>
    xiPinv_lt hB (hXZ a ha).2.2 (hXZ b hb).2.2 (Cx.mono (hXZ a ha).1 (hXZ b hb).1 hab)
  apply hno
  refine ⟨fun x => xiPinv (f ρ) ρ (f x), ⟨hmono, fun a ha b hb c hc => ?_, fun a ha b hb hab => ?_⟩,
    fun x hx => hpw x (Finset.mem_insert_of_mem hx), fun x hx z hz => ?_, fun z hz => ?_⟩
  · -- `+`, both directions
    obtain ⟨haA, hal, hfaT⟩ := hXZ a ha
    obtain ⟨hbA, hbl, hfbT⟩ := hXZ b hb
    obtain ⟨hcA, -, hfcT⟩ := hXZ c hc
    have habD : a + b ∈ D := Finset.mem_union_right _ (Finset.mem_image₂.2
      ⟨a, hSC (Finset.mem_insert_of_mem ha), b, hSC (Finset.mem_insert_of_mem hb), rfl⟩)
    have habA : a + b ∈ A := hDA _ habD
    have hfab : f a + f b = f (a + b) := Cx.add a haA b hbA (a + b) habA rfl
    constructor
    · rintro rfl
      show xiPinv (f ρ) ρ (f a) + xiPinv (f ρ) ρ (f b) = xiPinv (f ρ) ρ (f (a + b))
      rw [← hfab, xiPinv_add hB hfaT hfbT]
    · intro hg
      obtain ⟨hga, hpga⟩ := xiPinv_spec hB hfaT
      obtain ⟨hgb, hpgb⟩ := xiPinv_spec hB hfbT
      obtain ⟨-, hpgc⟩ := xiPinv_spec hB hfcT
      obtain ⟨-, hps⟩ := pi_add hB hga hgb
      have e1 : f a + f b = f c := by
        have := congrArg (pi (f ρ) ρ) hg
        rw [hps, hpga, hpgb] at this
        exact this.trans hpgc
      exact Cx.mono.injOn habA hcA (hfab.symm.trans e1)
  · -- `≤₁`
    obtain ⟨haA, hal, hfaT⟩ := hXZ a ha
    obtain ⟨hbA, hbl, hfbT⟩ := hXZ b hb
    have hfa1 : f a < Om1 := (Cx.low a haA).trans hρ1
    rcases (le1R_le hab).lt_or_eq with hab' | rfl
    swap
    · exact le1R_refl _
    have hgab := (hmono ha hb hab').le
    rcases lt_or_ge a ρ with haρ | hρa
    · have hfa : f a = a := Cx.fix a haA haρ
      by_cases haU : UpsPt a
      · have hgaU : UpsPt (xiPinv (f ρ) ρ (f a)) := by
          rw [hfa]
          rcases lt_or_ge a (f ρ) with haσ | hσa
          · rw [xiPinv_small hB haσ]; exact haU
          · have haT : a ∈ Tset (f ρ) := by rw [← hfa]; exact hfaT
            obtain ⟨mσ, -, -, hmσmin, hTmσ⟩ := T_inter_Om1 hσE hσ1
            have ham : a < mσ := (hTmσ a (haρ.trans hρ1)).1 haT
            have haσ' : a = f ρ := by
              rcases hσa.lt_or_eq with hlt' | heq
              · exact absurd (ham.trans_le (hmσmin a hlt' haU.2)) (lt_irrefl _)
              · exact heq.symm
            rw [haσ', xiPinv_base hB]; exact h.ρU
        exact hgaU.2 _ hgab
      · rcases lt_or_ge b ρ with hbρ | hρb
        · have hfb : f b = b := Cx.fix b hbA hbρ
          refine xiPinv_le1R hB hσU h.ρU hfaT hfbT hfa1 ?_
          rw [hfa, hfb]; exact hab
        · exact absurd ((Cx.sk a haρ haU b).2 hab) (h.below a haρ b hρb)
    · rcases hρa.lt_or_eq with hρa' | heq
      · exact xiPinv_le1R hB hσU h.ρU hfaT hfbT hfa1
          (hle1R a b haA hbA hρa' (hbl.trans hlδ.le) hab)
      · have hga : xiPinv (f ρ) ρ (f a) = ρ := by rw [← heq]; exact xiPinv_base hB
        show le1R (xiPinv (f ρ) ρ (f a)) (xiPinv (f ρ) ρ (f b))
        rw [hga]
        exact h.ρU.2 _ (hga.symm.le.trans (by exact hgab))
  · -- `h[X] < h[Z]`
    exact hmono (Finset.mem_union_left _ hx) (Finset.mem_union_right _ hz)
      ((hX x hx).trans_le (hZ z hz).1)
  · -- `h[Z] < e`
    obtain ⟨hzA, hzl, hfzT⟩ := hXZ z (Finset.mem_union_right _ hz)
    exact ((xiPinv_le hB hfzT hflT (Cx.mono.monotoneOn hzA hlA hzl)).trans hgl).trans_lt hl0e

/-- Lemma IMG at the base `ρ` itself. -/
theorem xi_img_rho : Gn.GnI ρ δ ρ := by
  obtain ⟨m, hρm, -, -, hTm, hm1⟩ := T_next (Or.inr h.ρE) h.ρ1
  have hρT : ρ ∈ Tset ρ := (hTm ρ h.ρ1).2 hρm
  have w : WZ ρ δ (insert ρ ∅) ∅ :=
    WZ.empty.insW le_rfl (Gn.gn_lt_δ h hρT h.ρ1) (Or.inl (inE_indec h.ρE))
  refine Gn.gnI_mk h w (by simp) hρT h.ρ1 fun A f _ _ C => ?_
  rw [(pi_base (h.img_bases C)).2]

/-- **LEMMA IMG AT EVERY POINT OF `Tᵖ ∩ Ω₁`** in a restart context. -/
theorem xi_img_all : ∀ v, v ∈ Tset ρ → v < Om1 → Gn.GnI ρ δ v := by
  obtain ⟨m, -, -, -, hTm, hm1⟩ := T_next (Or.inr h.ρE) h.ρ1
  have hall := Gn.gnImg_of_eps h (B := m) (fun v hv => ⟨(hTm v (hv.trans hm1)).2 hv, hv.trans hm1⟩)
    (fun e heE hρe hem IH => by
      rcases hρe.lt_or_eq with hlt | heq
      · exact xi_img_eps h heE hlt ((hTm e (hem.trans hm1)).2 hem) (hem.trans hm1) IH
      · rw [← heq]; exact xi_img_rho h)
  intro v hv hv1
  exact hall v ((hTm v hv1).1 hv)

end Img

/-- **`Xi.XiImgAll`**: Lemma IMG at every reading of a code below `θ`. -/
theorem xi_imgAll (S : InaccSeq.{0}) : XiImgAll S := fun _ _ _ c h _ hd _ _ => by
  obtain ⟨hT, h1⟩ := xiR_T S h.ρE h.ρ1 c hd
  exact xi_img_all h _ hT h1

end Googology.Trans.PoR.InaccPsi.R2.Xi

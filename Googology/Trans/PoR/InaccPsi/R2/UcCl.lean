import Googology.Trans.PoR.InaccPsi.R2.UcDat
import Googology.Trans.PoR.InaccPsi.R2.TlCl

/-!
# Codes below `B₂`: the closure with the atoms `H_γ(y)` and the code test `UcCl q z ↔ ucDat z < q`

`Ω₁ = Om1`, `X = Tl.tlX`, `H_γ = Uc.ucH γ`, `B₂ = Uc.ucB` (the least strongly critical `z > Ω₁` with no normal form
`H_λ(y)`), `TlCl Z` the codes below `X` (`R2.TlCl`).  `UcCl Z` is generated from the ordinals below `Z` and `Ω₁` by
`+`, `φ`, the codes of `TlCl Z`, and the atoms `H_γ(y) ≥ X` (`γ < E₂` with every component a code, `y` a code).

* `UcCl`, `UcCl.mono`, `UcCl.zero`, `UcCl.one`, `UcCl.opow`, `UcCl.mul_nat`, `uc_tl_lt_X` (codes of `TlCl Z`,
  `Z ≤ Ω₁`, are `< X`), `uc_cl_lt_X` (**below `X` the codes are those of `TlCl`**);
* `ucDec` (**decomposition**: `w − x` and `log_ω w` are codes), `uc_cl_inv` (inverse Veblen functions), `uc_cl_atom`
  (**the components of the level and the index of an atom code `≥ X` are codes**);
* `uc_cl_dat`, `uc_code`, `uc_cl_iff` (**for a strongly critical `q` and `z < B₂`: `UcCl q z ↔ ucDat z < q`**; it
  extends `Tl.tl_cl_iff` from `X` to `B₂`), `uc_cl_Om1_add`, `ucDatL`, `uc_code_lvlL` (`ucDatL μ < b`
  makes `μ < B₂` a code over `b`).

No new axiom.  New definitions: `UcCl`, `ucDatL`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf
  Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Gg

/-- **The codes over `Z` below `B₂`**: generated from the ordinals below `Z` and `Ω₁` by `+`, `φ`, the codes of
`TlCl Z` and the atoms `H_γ(y) ≥ X` (`γ < E₂`, every component of `γ` and `y` codes). -/
inductive UcCl (Z : Ordinal.{0}) : Ordinal.{0} → Prop
  | small {x : Ordinal.{0}} : x < Z → UcCl Z x
  | om : UcCl Z Om1
  | add {x y : Ordinal.{0}} : UcCl Z x → UcCl Z y → UcCl Z (x + y)
  | phi {x y : Ordinal.{0}} : UcCl Z x → UcCl Z y → UcCl Z (veblen x y)
  | tl {x : Ordinal.{0}} : TlCl Z x → UcCl Z x
  | hatom {γ y : Ordinal.{0}} : γ < ucE → (∀ x ∈ ucComps γ, UcCl Z x) → UcCl Z y → tlX ≤ ucH γ y →
      UcCl Z (ucH γ y)

variable {Z : Ordinal.{0}}

theorem UcCl.mono {Z' : Ordinal.{0}} (h : Z ≤ Z') {x : Ordinal.{0}} (hx : UcCl Z x) : UcCl Z' x := by
  induction hx with
  | small h' => exact UcCl.small (lt_of_lt_of_le h' h)
  | om => exact UcCl.om
  | add _ _ ihx ihy => exact UcCl.add ihx ihy
  | phi _ _ ihx ihy => exact UcCl.phi ihx ihy
  | tl h' => exact UcCl.tl (h'.mono h)
  | hatom hγ _ _ hX ihc ihy => exact UcCl.hatom hγ ihc ihy hX

theorem UcCl.zero (hZ : 0 < Z) : UcCl Z 0 := UcCl.small hZ

theorem UcCl.opow (hZ : 0 < Z) {c : Ordinal.{0}} (h : UcCl Z c) : UcCl Z (ω ^ c) := by
  have := UcCl.phi (UcCl.zero hZ) h; rwa [veblen_zero_apply] at this

theorem UcCl.one (hZ : 0 < Z) : UcCl Z 1 := by
  have := UcCl.opow hZ (UcCl.zero hZ); rwa [opow_zero] at this

theorem UcCl.mul_nat (hZ : 0 < Z) {x : Ordinal.{0}} (h : UcCl Z x) : ∀ n : ℕ, UcCl Z (x * n)
  | 0 => by rw [Nat.cast_zero, mul_zero]; exact UcCl.zero hZ
  | n + 1 => by rw [Nat.cast_succ, mul_add_one]; exact UcCl.add (UcCl.mul_nat hZ h n) h

/-- **The codes of `TlCl Z`, `Z ≤ Ω₁`, are below `X`.** -/
theorem uc_tl_lt_X (hZ : Z ≤ Om1) {x : Ordinal.{0}} (hx : TlCl Z x) : x < tlX := by
  induction hx with
  | small h => exact h.trans_le (hZ.trans tlX_gt.le)
  | om => exact tlX_gt
  | add _ _ ihx ihy => exact (Lq.lq_SC_indec tlX_SC).add_lt ihx ihy
  | phi _ _ ihx ihy => exact tlX_SC.2 _ ihx _ ihy
  | @atom β y _ _ _ ihβ ihy =>
    have h := (rhF_lt β).2 ihy
    rwa [uc_F_X ihβ] at h

/-- **Below `X` the codes are those of `TlCl`.** -/
theorem uc_cl_lt_X {x : Ordinal.{0}} (hx : UcCl Z x) : x < tlX → TlCl Z x := by
  induction hx with
  | small h => exact fun _ => TlCl.small h
  | om => exact fun _ => TlCl.om
  | add _ _ ihx ihy =>
    exact fun h => TlCl.add (ihx (le_self_add.trans_lt h)) (ihy (le_add_self.trans_lt h))
  | @phi x y _ _ ihx ihy =>
    exact fun h => TlCl.phi (ihx ((left_le_veblen x y).trans_lt h)) (ihy ((right_le_veblen x y).trans_lt h))
  | tl h => exact fun _ => h
  | hatom _ _ _ hX _ _ => exact fun h => absurd hX (not_le.2 h)

/-! ## Decomposition -/

/-- **Decomposition**: for a strongly critical `Z ≤ Ω₁`, a code `w` has `w − x` (every code `x ≤ w`) and `log_ω w`
codes. -/
theorem ucDec (hZ : SC Z) (hZ1 : Z ≤ Om1) : ∀ w, UcCl Z w →
    (∀ x, UcCl Z x → x ≤ w → UcCl Z (w - x)) ∧ UcCl Z (log ω w) := by
  have h0 : UcCl Z 0 := UcCl.zero hZ.1
  intro w
  induction w using WellFoundedLT.induction with
  | ind w IHo =>
  intro hw
  suffices H : ∀ v, UcCl Z v → v ≤ w →
      (∀ x, UcCl Z x → x ≤ v → UcCl Z (v - x)) ∧ UcCl Z (log ω v) from H w hw le_rfl
  intro v hv
  induction hv with
  | @small v h =>
    intro _
    exact ⟨fun x _ _ => UcCl.small ((Ordinal.sub_le_self v x).trans_lt h),
      UcCl.small ((log_le_self ω v).trans_lt h)⟩
  | om =>
    intro _
    have hp : IsPrincipal (· + ·) (Om1 : Ordinal.{0}) := by
      rw [← rj_Om1_opow]; exact isPrincipal_add_omega0_opow _
    refine ⟨fun x _ hx => ?_, ?_⟩
    · rcases gg_sub_prin hp hx with e | e <;> rw [e]
      · exact UcCl.om
      · exact h0
    · have : log ω (Om1 : Ordinal.{0}) = Om1 := by
        conv_lhs => rw [← rj_Om1_opow]
        exact log_opow one_lt_omega0 _
      rw [this]; exact UcCl.om
  | @tl v hv' =>
    intro _
    have hvX := uc_tl_lt_X hZ1 hv'
    obtain ⟨hs, hl⟩ := tlDec hZ v hv'
    exact ⟨fun x hx hxv => UcCl.tl (hs x (uc_cl_lt_X hx (hxv.trans_lt hvX)) hxv), UcCl.tl hl⟩
  | @hatom γ y hγ hc hy hX _ _ =>
    intro _
    have hSC := ucH_SC γ y
    have hA : UcCl Z (ucH γ y) := UcCl.hatom hγ hc hy hX
    refine ⟨fun x _ hx => ?_, ?_⟩
    · rcases gg_sub_prin (tl_SC_prin hSC) hx with e | e <;> rw [e]
      · exact hA
      · exact h0
    · rw [tl_log_SC hSC]; exact hA
  | @add u v hu hv ihu ihv =>
    intro hle
    have hu' := ihu (le_self_add.trans hle)
    have hv' := ihv (le_add_self.trans hle)
    refine ⟨fun x hx hxuv => ?_, ?_⟩
    · rcases le_or_gt x u with hxu | hux
      · have e : u + v - x = (u - x) + v := by
          refine Ordinal.sub_eq_of_add_eq ?_
          rw [← add_assoc, Ordinal.add_sub_cancel_of_le hxu]
        rw [e]; exact UcCl.add (hu'.1 x hx hxu) hv
      · rcases hxuv.lt_or_eq with hlt | heq
        · have hxw : x < w := hlt.trans_le hle
          have hxu' : UcCl Z (x - u) := (IHo x hxw hx).1 u hu hux.le
          have e1 : x = u + (x - u) := (Ordinal.add_sub_cancel_of_le hux.le).symm
          have hxv : x - u ≤ v := by
            have : u + (x - u) ≤ u + v := by rw [← e1]; exact hxuv
            exact (add_le_add_iff_left _).1 this
          have e : u + v - x = v - (x - u) := by
            conv_lhs => rw [e1]
            rw [← Ordinal.sub_sub, Ordinal.add_sub_cancel]
          rw [e]; exact hv'.1 (x - u) hxu' hxv
        · rw [heq, Ordinal.sub_self]; exact h0
    · rcases ggLog_add u v with e | e <;> rw [e]
      · exact hu'.2
      · exact hv'.2
  | @phi a b ha hb iha ihb =>
    intro hle
    rcases eq_or_ne a 0 with rfl | ha0
    · rw [veblen_zero_apply]
      refine ⟨fun x _ hx => ?_, ?_⟩
      · rcases gg_sub_prin (isPrincipal_add_omega0_opow b) hx with e | e <;> rw [e]
        · exact UcCl.opow hZ.1 hb
        · exact h0
      · rw [log_opow one_lt_omega0]; exact hb
    · have hE := gg_veblen_eps (y := b) ha0
      have hp : IsPrincipal (· + ·) (veblen a b) := by rw [← hE]; exact isPrincipal_add_omega0_opow _
      refine ⟨fun x _ hx => ?_, ?_⟩
      · rcases gg_sub_prin hp hx with e | e <;> rw [e]
        · exact UcCl.phi ha hb
        · exact h0
      · have : log ω (veblen a b) = veblen a b := by
          conv_lhs => rw [← hE]
          exact log_opow one_lt_omega0 _
        rw [this]; exact UcCl.phi ha hb

/-- **The codes over `Z ≤ Ω₁` are closed under the inverse Veblen functions** at the `ε`-numbers `z > Ω₁` that are
not strongly critical. -/
theorem uc_cl_inv (hZ : Z ≤ Om1) : ∀ z, UcCl Z z → Om1 < z → ω ^ z = z → invVeblen₁ z < z →
    UcCl Z (invVeblen₁ z) ∧ UcCl Z (invVeblen₂ z) := by
  intro z hz
  induction hz with
  | small h => exact fun h1 _ _ => absurd (h.trans_le hZ) (not_lt.2 h1.le)
  | om => exact fun h1 _ _ => absurd h1 (lt_irrefl _)
  | @tl x hx =>
    intro h1 hE hI
    obtain ⟨a, b⟩ := tl_cl_inv hZ x hx h1 hE hI
    exact ⟨UcCl.tl a, UcCl.tl b⟩
  | @hatom γ y _ _ _ _ _ _ => exact fun _ _ hI => absurd hI (tl_SC_facts (ucH_SC γ y)).2
  | @add x y _ _ ihx ihy =>
    intro h1 hE hI
    have hp : IsPrincipal (· + ·) (x + y) := by rw [← hE]; exact isPrincipal_add_omega0_opow _
    rcases tf_prin_sum hp rfl with ex | ey
    · rw [← ex] at h1 hE hI ⊢; exact ihx h1 hE hI
    · rw [← ey] at h1 hE hI ⊢; exact ihy h1 hE hI
  | @phi x y hx hy _ ihy =>
    intro h1 hE hI
    rcases eq_or_lt_of_le (right_le_veblen x y) with ey | hlt
    · rw [← ey] at h1 hE hI ⊢; exact ihy h1 hE hI
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [veblen_zero_apply] at hE hlt
      exact absurd ((opow_right_inj one_lt_omega0).1 hE).symm hlt.ne
    rw [invVeblen₁_veblen hlt, invVeblen₂_veblen hx0 hlt]
    exact ⟨hx, hy⟩

/-- **The components of the level and the index of an atom code `z ≥ X` are codes** (`Z ≤ Ω₁`, `z < B₂`). -/
theorem uc_cl_atom (hZ : Z ≤ Om1) : ∀ z, UcCl Z z → SC z → tlX ≤ z → z < ucB →
    (∀ x ∈ ucComps (ucLev z), UcCl Z x) ∧ UcCl Z (ucI (ucLev z) z) := by
  intro z hz
  induction hz with
  | small h => exact fun _ hX _ => absurd ((h.trans_le hZ).trans tlX_gt) (not_lt.2 hX)
  | om => exact fun _ hX _ => absurd tlX_gt (not_lt.2 hX)
  | tl h => exact fun _ hX _ => absurd (uc_tl_lt_X hZ h) (not_lt.2 hX)
  | @hatom γ y hγ hc hy _ _ ihy =>
    intro hSC hX hB
    rcases lt_or_eq_of_le (ucH_le_self γ y) with hlt | heq
    · obtain ⟨hl, hi⟩ := ucLev_H hγ hlt
      rw [hl, hi]; exact ⟨hc, hy⟩
    · rw [← heq] at hSC hX hB ⊢; exact ihy hSC hX hB
  | @add x y _ _ ihx ihy =>
    intro hSC hX hB
    rcases tf_prin_sum (tl_SC_prin hSC) rfl with ex | ey
    · rw [← ex] at hSC hX hB ⊢; exact ihx hSC hX hB
    · rw [← ey] at hSC hX hB ⊢; exact ihy hSC hX hB
  | @phi x y _ _ ihx ihy =>
    intro hSC hX hB
    rcases SC.eq_of_veblen_eq hSC rfl with ex | ey
    · rw [← ex] at hSC hX hB ⊢; exact ihx hSC hX hB
    · rw [← ey] at hSC hX hB ⊢; exact ihy hSC hX hB

/-! ## Codes and data -/

/-- **The data of a code over a strongly critical `q` is below `q`.** -/
theorem uc_cl_dat {q : Ordinal.{0}} (hq : SC q) : ∀ z, UcCl q z → ucDat z < q := by
  rcases lt_or_ge Om1 q with hq1 | hq1
  · exact fun z _ => (ucDat_lt_Om1 z).trans hq1
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hz
  rcases lt_or_ge z tlX with hzX | hXz
  · rw [ucDat_lt_X hzX]; exact tl_cl_dat hq z (uc_cl_lt_X hz hzX)
  rcases le_or_gt ucB z with hB | hzB
  · rw [ucDat_big hB]; exact hq.1
  have h := uc_Om1_lt_of_X hXz
  by_cases hE : ω ^ z = z
  · by_cases hI : invVeblen₁ z < z
    · obtain ⟨h1, h2⟩ := uc_cl_inv hq1 z hz h hE hI
      rw [ucDat_phi hXz hzB hE hI]
      exact max_lt (IH _ hI h1) (IH _ (tf_inv2_lt hE) h2)
    · have hSC := tl_SC_of h hI
      obtain ⟨hc, hy⟩ := uc_cl_atom hq1 z hz hSC hXz hzB
      have hlv := (ucLev_spec hSC h (uc_nf_of_lt hSC h hzB)).2.1
      rw [ucDat_atom hXz hzB hE hI]
      exact max_lt ((ucFold_lt_iff ucDat hq.1 _).2 fun x hx => IH x ((le_ucC hx).trans_lt hlv) (hc x hx))
        (IH _ (uc_atom_lt hXz hzB hI) hy)
  · have hz0 : z ≠ 0 := (rj_Om1_pos.trans h).ne'
    obtain ⟨hsub, hlog⟩ := ucDec hq hq1 z hz
    set g := log ω z with hg
    obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt z one_lt_omega0)
    have hdec : ω ^ g * k + z % ω ^ g = z := by
      have := Ordinal.div_add_mod z (ω ^ g); rwa [hk] at this
    have hwk : UcCl q (ω ^ g * k) := UcCl.mul_nat hq.1 (UcCl.opow hq.1 hlog) k
    have hle : ω ^ g * k ≤ z := by
      conv_rhs => rw [← hdec]
      exact le_self_add
    have hr : UcCl q (z % ω ^ g) := by
      have e : z - ω ^ g * k = z % ω ^ g := by
        nth_rewrite 1 [← hdec]; exact Ordinal.add_sub_cancel _ _
      rw [← e]; exact hsub _ hwk hle
    rw [ucDat_cnf hXz hzB hE]
    exact max_lt (IH _ (tf_log_lt h hE) hlog) (IH _ (rj_mod_lt hz0) hr)

/-- **A code**: `z < B₂` with `ucDat z < a` (`0 < a`) is a code over `a`. -/
theorem uc_code {a : Ordinal.{0}} (ha : 0 < a) : ∀ z : Ordinal.{0}, z < ucB → ucDat z < a → UcCl a z := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hzB hd
  rcases lt_or_ge z tlX with hzX | hXz
  · rw [ucDat_lt_X hzX] at hd; exact UcCl.tl (tl_code ha z hzX hd)
  have h := uc_Om1_lt_of_X hXz
  by_cases hE : ω ^ z = z
  · by_cases hI : invVeblen₁ z < z
    · rw [ucDat_phi hXz hzB hE hI] at hd
      have h2 := tf_inv2_lt hE
      have e : veblen (invVeblen₁ z) (invVeblen₂ z) = z := by rw [veblen_invVeblen₁_invVeblen₂, hE]
      rw [← e]
      exact UcCl.phi (IH _ hI (hI.trans hzB) ((le_max_left _ _).trans_lt hd))
        (IH _ h2 (h2.trans hzB) ((le_max_right _ _).trans_lt hd))
    · have hSC := tl_SC_of h hI
      have hne := uc_nf_of_lt hSC h hzB
      obtain ⟨hlE, hlv, -, -, -⟩ := ucLev_spec hSC h hne
      obtain ⟨hnf, hyz⟩ := uc_nf hSC h hne
      rw [ucDat_atom hXz hzB hE hI] at hd
      have hc : ∀ x ∈ ucComps (ucLev z), UcCl a x := fun x hx => by
        have hxz : x < z := (le_ucC hx).trans_lt hlv
        exact IH x hxz (hxz.trans hzB)
          (((ucFold_le_of_mem ucDat _ x hx).trans (le_max_left _ _)).trans_lt hd)
      have hy := IH _ hyz (hyz.trans hzB) ((le_max_right _ _).trans_lt hd)
      rw [← hnf]
      exact UcCl.hatom hlE hc hy (by rw [hnf]; exact hXz)
  · rw [ucDat_cnf hXz hzB hE] at hd
    have hz0 : z ≠ 0 := (rj_Om1_pos.trans h).ne'
    have hl := tf_log_lt h hE
    have hm := rj_mod_lt hz0
    have he := IH _ hl (hl.trans hzB) ((le_max_left _ _).trans_lt hd)
    have hr := IH _ hm (hm.trans hzB) ((le_max_right _ _).trans_lt hd)
    obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt z one_lt_omega0)
    have hdec : ω ^ log ω z * (z / ω ^ log ω z) + z % ω ^ log ω z = z := Ordinal.div_add_mod z _
    rw [← hdec, hk]
    exact UcCl.add (UcCl.mul_nat ha (UcCl.opow ha he) k) hr

/-- **For a strongly critical `q` and `z < B₂`: `UcCl q z ↔ ucDat z < q`.** -/
theorem uc_cl_iff {q z : Ordinal.{0}} (hq : SC q) (hz : z < ucB) : UcCl q z ↔ ucDat z < q :=
  ⟨uc_cl_dat hq z, uc_code hq.1 z hz⟩

/-- `B₂` is additively principal. -/
theorem uc_B_indec : Indec (ucB : Ordinal.{0}) := Lq.lq_SC_indec ucB_SC

/-- `UcCl Z (Ω₁ + μ) ↔ UcCl Z μ` (`Z ≤ Ω₁` strongly critical). -/
theorem uc_cl_Om1_add {μ : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om1) : UcCl Z (Om1 + μ) ↔ UcCl Z μ := by
  refine ⟨fun h => ?_, fun h => UcCl.add UcCl.om h⟩
  have := (ucDec hZ hZ1 _ h).1 _ UcCl.om le_self_add
  rwa [Ordinal.add_sub_cancel] at this

/-- **The data of the level `μ`**: `ucDat (Ω₁ + μ)`. -/
noncomputable def ucDatL (μ : Ordinal.{0}) : Ordinal.{0} := ucDat (Om1 + μ)

theorem ucDatL_lt_Om1 (μ : Ordinal.{0}) : ucDatL μ < Om1 := ucDat_lt_Om1 _

/-- **`ucDatL μ < b` makes `μ < B₂` a code over a strongly critical `b ≤ Ω₁`.** -/
theorem uc_code_lvlL {μ b : Ordinal.{0}} (hb : SC b) (hb1 : b ≤ Om1) (hμ : μ < ucB) (hd : ucDatL μ < b) :
    UcCl b μ := by
  have hO : Om1 + μ < ucB := uc_B_indec.add_lt ucB_gt hμ
  exact (uc_cl_Om1_add hb hb1).1 (uc_code hb.1 (Om1 + μ) hO hd)

end Googology.Trans.PoR.InaccPsi.R2.Uc

import Googology.Trans.PoR.InaccPsi.R2.TfCl
import Googology.Trans.PoR.InaccPsi.R2.GdAt

/-!
# The atoms below `B_Γ` are the collapses `ψ_{Ω₂}(c)`: the link of `Tf.tfDat` with the `InaccPsi` notation

`ψ_{Ω₂}(c) = S.psi c Ω₂` (`Googology.Notation.InaccPsi`), `Γ_ν = gamma ν`, `B_Γ = Tf.tfBG`.

* `tf_gcG` (`gcG α = Γ_{Ω₁+1+α}`), `tf_psi` (**`ψ_{Ω₂}(α) = Γ_{Ω₁+1+α}` for every `α ≤ B_Γ`**; it extends `Gd.gd_psi`
  from `α ≤ Ω₁ + 1` to `B_Γ`), `tf_psi_BG` (`ψ_{Ω₂}(B_Γ) = B_Γ`), `tf_atom_psi` (**every atom `Γ_ν` below `B_Γ` is
  `ψ_{Ω₂}(ν − (Ω₁ + 1))`**), `tf_psi_lt_iff` (`ψ_{Ω₂}(e) < B_Γ ↔ e < B_Γ`);
* `tfDat_psi` (**the data of a collapse: `tfDat (ψ_{Ω₂}(c)) = tfDat c` for `c < B_Γ`**: the data of the atoms read on
  `ψ_{Ω₂}` normal forms);
* `tfCl_of_CSet` (**the hull below `B_Γ` consists of codes**: if every countable member of `Cl(a, Z)` is below `Z`,
  every member of `Cl(a, Z)` below `B_Γ` is in `TfCl Z`; it extends `R2.lgCl_of_CSet` from `Γ'` to `B_Γ`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj
  Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Gc

variable {S : InaccSeq.{0}}

/-- **`gcG α = Γ_{Ω₁+1+α}`.** -/
theorem tf_gcG (α : Ordinal.{0}) : gcG α = gamma (Om1 + 1 + α) := by
  have h := (eq_enumOrd (fun a => gamma (Om1 + 1 + a)) gcSet_unbdd).2 ⟨fun a b hab => ?_, ?_⟩
  · exact congrFun h α
  · exact gamma_lt_gamma.2 ((add_lt_add_iff_left _).2 hab)
  · ext b
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨Lq.lq_gamma_SC _, ?_⟩
      rw [← rj_Om1]; exact tf_Om1_lt_gamma.2 ((lt_add_one _).trans_le le_self_add)
    · rintro ⟨hb, hb1⟩
      obtain ⟨ν, rfl⟩ := mem_range_gamma.2 hb.veblen_zero
      have h1 : Om1 < ν := by rw [← tf_Om1_lt_gamma, rj_Om1]; exact hb1
      exact ⟨ν - (Om1 + 1), by
        show gamma (Om1 + 1 + (ν - (Om1 + 1))) = gamma ν
        rw [Ordinal.add_sub_cancel_of_le (Order.add_one_le_of_lt h1)]⟩

/-- `β < Γ_{Ω₁+1+β}` for `β < B_Γ`. -/
theorem tf_lt_gamma_shift {β : Ordinal.{0}} (hβ : β < tfBG) : β < gamma (Om1 + 1 + β) := by
  refine lt_of_le_of_ne (le_add_self.trans isNormal_gamma.strictMono.le_apply) fun e => ?_
  have h2 : Om1 + 1 + β = β := le_antisymm (by
    calc Om1 + 1 + β ≤ gamma (Om1 + 1 + β) := isNormal_gamma.strictMono.le_apply
      _ = β := e.symm) le_add_self
  have hfix : gamma β = β := by
    conv_lhs => rw [← h2]
    exact e.symm
  have h1 : Om1 < β := by rw [← h2]; exact (lt_add_one _).trans_le le_self_add
  exact absurd (tfBG_le hfix h1) (not_le.2 hβ)

/-- **`ψ_{Ω₂}(α) = Γ_{Ω₁+1+α}`** for every `α ≤ B_Γ`. -/
theorem tf_psi (S : InaccSeq.{0}) : ∀ α : Ordinal.{0}, α ≤ tfBG →
    S.psi α (Om (1 + 1)) = gamma (Om1 + 1 + α) := by
  intro α
  induction α using WellFoundedLT.induction with
  | ind α IH =>
  intro hα
  have hκ : S.InR (Om (1 + 1)) := InR_Om_succ 1
  refine le_antisymm (gaPsi_le S (Lq.lq_gamma_SC _) ?_ fun e he => ?_) ?_
  · rw [← rj_Om1]; exact tf_Om1_lt_gamma.2 ((lt_add_one _).trans_le le_self_add)
  · rw [IH e he (he.le.trans hα)]; exact gamma_lt_gamma.2 ((add_lt_add_iff_left _).2 he)
  · -- every `Γ_{Ω₁+1+β}`, `β < α`, is below `ψ_{Ω₂}(α)`
    have hlt : ∀ β < α, gamma (Om1 + 1 + β) < S.psi α (Om (1 + 1)) := by
      intro β hβ
      have hβB : β < tfBG := hβ.trans_le hα
      have hle : S.psi β (Om (1 + 1)) ≤ S.psi α (Om (1 + 1)) := (psi_mono hκ hβ.le).1
      rw [IH β hβ hβB.le] at hle
      have hβψ : β < S.psi α (Om (1 + 1)) := (tf_lt_gamma_shift hβB).trans_le hle
      rw [← IH β hβ hβB.le]
      exact psi_lt_psi_of_mem hκ hβ (CSet.of_lt hβψ)
    obtain ⟨μ, hμ⟩ := mem_range_gamma.2 (ga_psi_SC (S := S) α).veblen_zero
    have hμ1 : Om1 < μ := by rw [← tf_Om1_lt_gamma, hμ, rj_Om1]; exact ga_Om1_lt_psi α
    have hle : Om1 + 1 + α ≤ μ := by
      have e : Om1 + 1 + (μ - (Om1 + 1)) = μ := Ordinal.add_sub_cancel_of_le (Order.add_one_le_of_lt hμ1)
      rw [← e]
      refine (add_le_add_iff_left _).2 (not_lt.1 fun h => ?_)
      have := hlt _ h
      rw [← hμ, e] at this
      exact lt_irrefl _ this
    rw [← hμ]; exact gamma_le_gamma.2 hle

/-- `ψ_{Ω₂}(B_Γ) = B_Γ`. -/
theorem tf_psi_BG (S : InaccSeq.{0}) : S.psi tfBG (Om (1 + 1)) = tfBG := by
  have hw : ω ^ tfBG = tfBG := Low.opow_eq_self_of_SC tfBG_SC
  have e : Om1 + 1 + tfBG = tfBG :=
    Ordinal.add_of_omega0_opow_le (a := Om1 + 1) (b := tfBG) (c := tfBG)
      (by rw [hw]; exact SC.add_one_lt tfBG_SC tfBG_gt) (by rw [hw])
  rw [tf_psi S _ le_rfl, e, tfBG_fix]

/-- **Every atom below `B_Γ` is a collapse**: `Γ_ν = ψ_{Ω₂}(ν − (Ω₁ + 1))` for `Ω₁ < ν`, `Γ_ν < B_Γ`. -/
theorem tf_atom_psi (S : InaccSeq.{0}) {ν : Ordinal.{0}} (h1 : Om1 < ν) (h2 : gamma ν < tfBG) :
    gamma ν = S.psi (ν - (Om1 + 1)) (Om (1 + 1)) := by
  have hν : ν < tfBG := isNormal_gamma.strictMono.le_apply.trans_lt h2
  rw [tf_psi S _ ((Ordinal.sub_le_self _ _).trans hν.le),
    Ordinal.add_sub_cancel_of_le (Order.add_one_le_of_lt h1)]

/-- `ψ_{Ω₂}(e) < B_Γ ↔ e < B_Γ`. -/
theorem tf_psi_lt_iff (S : InaccSeq.{0}) {e : Ordinal.{0}} : S.psi e (Om (1 + 1)) < tfBG ↔ e < tfBG := by
  constructor
  · intro h
    by_contra he
    have := (psi_mono (S := S) (InR_Om_succ 1) (not_lt.1 he)).1
    rw [tf_psi_BG S] at this
    exact absurd h (not_lt.2 this)
  · intro he
    rw [tf_psi S _ he.le, ← tfBG_fix]
    exact gamma_lt_gamma.2 (SC.isPrincipal tfBG_SC (SC.add_one_lt tfBG_SC tfBG_gt) he)

/-- **The data of a collapse below `B_Γ`**: `tfDat (ψ_{Ω₂}(c)) = tfDat c`. -/
theorem tfDat_psi (S : InaccSeq.{0}) {c : Ordinal.{0}} (hc : c < tfBG) :
    tfDat (S.psi c (Om (1 + 1))) = tfDat c := by
  have hB := (tf_psi_lt_iff S).2 hc
  rw [tf_psi S _ hc.le] at hB ⊢
  rw [tfDat_gamma ((lt_add_one _).trans_le le_self_add) hB, Ordinal.add_sub_cancel]

/-! ## The hull below `B_Γ` -/

/-- **The hull below `B_Γ` consists of codes**: if every countable member of `Cl(a, Z)` is below `Z`, every member of
`Cl(a, Z)` below `B_Γ` is a code over `Z` (a collapse `ψ_π(e) < B_Γ` with `π ≠ Ω₁` has `π = Ω₂`, `e < B_Γ`, and is the
atom `Γ_{Ω₁+1+e}`). -/
theorem tfCl_of_CSet {a Z : Ordinal.{0}} (hZ : 0 < Z) (hkey : ∀ y ∈ S.CSet a Z, y < Om 1 → y < Z) :
    ∀ x ∈ S.CSet a Z, x < tfBG → TfCl Z x := by
  intro x hx
  have hx' := hx
  have hB2 := tfBG_lt_Om2
  induction hx with
  | small h => exact fun _ => TfCl.small h
  | zero => exact fun _ => TfCl.zero hZ
  | inacc n =>
    intro h
    have h1 : Om (1 + 1 : Ordinal.{0}) < Om (S.I n) :=
      Om_lt_Om.2 (lg_two_lt_Om1.trans_le (Low.Om_one_le_I n))
    rw [S.fix n] at h1
    exact absurd (h.trans hB2) (not_lt.2 h1.le)
  | inaccW =>
    intro h
    have h1 : Om (1 + 1 : Ordinal.{0}) < Om (S.I 0) :=
      Om_lt_Om.2 (lg_two_lt_Om1.trans_le (Low.Om_one_le_I 0))
    rw [S.fix 0] at h1
    exact absurd (h.trans hB2) (not_lt.2 (h1.le.trans (S.I_le_Iw 0)))
  | @add x y hx1 hy1 ihx ihy =>
    intro h
    exact TfCl.add (ihx hx1 (lt_of_le_of_lt le_self_add h)) (ihy hy1 (lt_of_le_of_lt le_add_self h))
  | @phi x y hx1 hy1 ihx ihy =>
    intro h
    exact TfCl.phi (ihx hx1 (lt_of_le_of_lt (left_le_veblen x y) h))
      (ihy hy1 (lt_of_le_of_lt (right_le_veblen x y) h))
  | @om x hx1 _ =>
    intro h
    have h2 : x < 1 + 1 := Om_lt_Om.1 (h.trans hB2)
    rcases (Order.lt_add_one_iff.1 h2).lt_or_eq with h0 | h1
    · rw [Order.lt_one_iff] at h0; rw [h0, Om_zero]; exact TfCl.zero hZ
    · rw [h1, ← rj_Om1]; exact TfCl.om
  | @coll π e hπ hπ1 he1 _ ihe =>
    intro h
    by_cases hπ0 : π = Om 1
    · have hlt : S.psi e.1 π < Om 1 := by rw [hπ0]; exact psi_lt Low.InR_Om_one _
      exact TfCl.small (hkey _ hx' hlt)
    rcases hπ with ⟨n, rfl⟩ | ⟨s, rfl⟩
    · exfalso
      have h2 : Om (1 + 1 : Ordinal.{0}) < S.psi e.1 (S.I n) :=
        lt_psi_of_mem (InR_I n) (Mx.mxOm2_mem _ _) (Mx.mxOm2_lt_I n)
      exact absurd (h.trans (hB2.trans h2)) (lt_irrefl _)
    · have hs0 : s ≠ 0 := fun e0 => hπ0 (by rw [e0, zero_add])
      rcases (Order.one_le_iff_ne_zero.2 hs0).lt_or_eq with hs1 | hs1
      · exfalso
        have h2 : Om (1 + 1 : Ordinal.{0}) ≤ Om s := Om_le_Om.2 (Order.add_one_le_of_lt hs1)
        exact absurd (h.trans (hB2.trans_le (h2.trans (psiS_bounds (S := S) e.1 s).1.le))) (lt_irrefl _)
      · subst hs1
        have heB : e.1 < tfBG := (tf_psi_lt_iff S).1 h
        have hec : TfCl Z e.1 := ihe he1 heB
        show TfCl Z (S.psi e.1 (Om (1 + 1)))
        rw [tf_psi S _ heB.le]
        exact TfCl.gam (TfCl.add (TfCl.add TfCl.om (TfCl.one hZ)) hec) ((lt_add_one _).trans_le le_self_add)

/-- `B_Γ` is closed under multiplication. -/
theorem tf_BG_mul_lt {x y : Ordinal.{0}} (hx : x < tfBG) (hy : y < tfBG) : x * y < tfBG := by
  have hw : ω ^ tfBG = tfBG := Low.opow_eq_self_of_SC tfBG_SC
  have hP := isPrincipal_mul_omega0_opow_opow tfBG
  rw [hw, hw] at hP
  exact hP hx hy

/-- **A code below `B_Γ` lies in every hull `Cl(a, b)` with `x ≤ a`, `Z ≤ b`** (`Z ≤ Ω₁` strongly critical; an atom
`Γ_ν` of the code is `ψ_{Ω₂}(c)` with `c < Γ_ν ≤ x ≤ a`). -/
theorem tf_mem_CSet {Z a b : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om1) (hZb : Z ≤ b) :
    ∀ x, TfCl Z x → x < tfBG → x ≤ a → x ∈ S.CSet a b := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx hxB hxa
  rcases lt_trichotomy x Om1 with h | rfl | h
  · exact CSet.of_lt ((hx.lt_of_lt_Om1 hZ h).trans_le hZb)
  · rw [rj_Om1]; exact CSet.Om_mem (CSet.one_mem _ _)
  by_cases hE : ω ^ x = x
  · by_cases hI : invVeblen₁ x < x
    · obtain ⟨h1, h2⟩ := tf_cl_inv hZ1 x hx h hE hI
      have h2l := tf_inv2_lt hE
      have e : veblen (invVeblen₁ x) (invVeblen₂ x) = x := by rw [veblen_invVeblen₁_invVeblen₂, hE]
      rw [← e]
      exact CSet.phi_mem (IH _ hI h1 (hI.trans hxB) (hI.le.trans hxa))
        (IH _ h2l h2 (h2l.trans hxB) (h2l.le.trans hxa))
    · have hg := tf_SC_gamma h hI
      have h1 : Om1 < tfIdx x := by rw [← tf_Om1_lt_gamma, hg]; exact h
      have hν : TfCl Z (tfIdx x) := tf_cl_atom hZ1 x hx _ h1 hg
      have hc : TfCl Z (tfIdx x - (Om1 + 1)) :=
        (tfDec hZ _ hν).1 _ (TfCl.add TfCl.om (TfCl.one hZ.1)) (Order.add_one_le_of_lt h1)
      have hclt := tf_atom_lt h hxB hI
      rw [← hg, tf_atom_psi S h1 (by rw [hg]; exact hxB)]
      exact CSet.psi_mem (hclt.trans_le hxa) (InR_Om_succ 1) (Mx.mxOm2_mem _ _)
        (IH _ hclt hc (hclt.trans hxB) (hclt.le.trans hxa))
  · have hz0 : x ≠ 0 := (rj_Om1_pos.trans h).ne'
    obtain ⟨hsub, hlog⟩ := tfDec hZ x hx
    set g := log ω x with hg
    obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
    have hdec : ω ^ g * k + x % ω ^ g = x := by
      have := Ordinal.div_add_mod x (ω ^ g); rwa [hk] at this
    have hwk : TfCl Z (ω ^ g * k) := TfCl.mul_nat hZ.1 (TfCl.opow hZ.1 hlog) k
    have hle : ω ^ g * k ≤ x := by
      conv_rhs => rw [← hdec]
      exact le_self_add
    have hr : TfCl Z (x % ω ^ g) := by
      have e : x - ω ^ g * k = x % ω ^ g := by
        nth_rewrite 1 [← hdec]; exact Ordinal.add_sub_cancel _ _
      rw [← e]; exact hsub _ hwk hle
    have hgl := tf_log_lt h hE
    have hml := rj_mod_lt hz0
    have hgC := IH _ hgl hlog (hgl.trans hxB) (hgl.le.trans hxa)
    have hmC := IH _ hml hr (hml.trans hxB) (hml.le.trans hxa)
    have hwC : ω ^ g ∈ S.CSet a b := by
      have := CSet.phi_mem (CSet.zero_mem a b) hgC; rwa [veblen_zero_apply] at this
    rw [← hdec]
    exact CSet.add_mem (mul_nat_mem hwC k) hmC

end Googology.Trans.PoR.InaccPsi.R2.Tf

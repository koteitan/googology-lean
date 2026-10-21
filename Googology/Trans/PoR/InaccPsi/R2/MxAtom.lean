import Googology.Trans.PoR.InaccPsi.R2.MxGx

/-!
# The hull below `ψ_{Ω₂}(Ω₁)`: codes with the atoms `ψ_{Ω₂}(α)`, `α < ρ_λ`, and their readings

`ψ = S.psi`, `A_η = Ω_ω + θ·η`, `ρ_λ = υ_λ = ψ_{Ω₁}(A_{η_λ})`, `H_λ = Cl(A_{η_λ}, ρ_λ)` (`Cd.cdHull`),
`Θ_λ(m) = otp(H_λ ∩ m)` (`Cd.cdTheta`), `K = ψ_{Ω₂}(Ω₁)` (`mxK`), `mxAt S ρ = {ψ_{Ω₂}(α) | α < ρ}`.  An argument
`A` is own when `A ∈ Cl(A, ψ_{Ω₁}(A))`.

* `mxPsi2_lt`, `mxPsi2_lt_iff` (`ψ_{Ω₂}` is strictly increasing on `[0, Ω₁)`), `mxAt_GxAt`, `mxAt_lt_K`;
* `mxHull_iff` (**at every named restart the hull below `K` is the set of codes over `ρ_λ` with the atoms
  `ψ_{Ω₂}(α)`, `α < ρ_λ`**: a collapse `ψ_{Ω₂}(e)` of the hull below `K` has `e < Ω₁`, hence `e < ρ_λ`), `mxTheta_K`
  (**`Θ_λ(m) = gxTh ρ_λ (mxAt ρ_λ) m` for `m ≤ K`**);
* `mxGx_bound` (a code below `m` is read below every strongly critical `X > ρ` that is above the readings of the
  atoms below `m`);
* `mxPsi_inj` (`ψ_{Ω₁}` is injective on own arguments), `mxTh_atom` (**`Θ(ψ_{Ω₂}(α)) = ψ_{Ω₁}(A + 1 + α)`** for
  `α < ρ = ψ_{Ω₁}(A)`, `A` own: both sides are the least strongly critical ordinal above `ρ` and above the values at
  every `β < α`; for `α = 0` this is `Γ_{ρ+1}`, `Mx.mxTheta_gam`).

No new axiom.  New definitions: `mxAt`, `mxK`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Mx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Sf

variable {S : InaccSeq.{0}}

/-- The atoms `ψ_{Ω₂}(α)`, `α < ρ`. -/
def mxAt (S : InaccSeq.{0}) (ρ : Ordinal.{0}) : Set Ordinal.{0} := {s | ∃ α < ρ, s = S.psi α (Om (1 + 1))}

/-- `K = ψ_{Ω₂}(Ω₁)`. -/
noncomputable def mxK (S : InaccSeq.{0}) : Ordinal.{0} := S.psi (Om 1) (Om (1 + 1))

theorem mxPsi2_lt {α β : Ordinal.{0}} (h : α < β) (hα : α < Om 1) :
    S.psi α (Om (1 + 1)) < S.psi β (Om (1 + 1)) :=
  psi_lt_psi_of_mem (InR_Om_succ 1) h (CSet.of_lt (hα.trans (psiS_bounds (S := S) β 1).1))

theorem mxPsi2_lt_iff {α β : Ordinal.{0}} (hα : α < Om 1) (hβ : β < Om 1) :
    S.psi α (Om (1 + 1)) < S.psi β (Om (1 + 1)) ↔ α < β := by
  refine ⟨fun h => ?_, fun h => mxPsi2_lt h hα⟩
  by_contra h'
  push Not at h'
  rcases h'.lt_or_eq with h'' | rfl
  · exact absurd (mxPsi2_lt h'' hβ) (not_lt.2 h.le)
  · exact lt_irrefl _ h

theorem mxAt_GxAt (ρ : Ordinal.{0}) : GxAt (mxAt S ρ) := by
  rintro s ⟨α, -, rfl⟩
  exact ⟨SC_psi (InR_Om_succ 1) α, (psiS_bounds α 1).1⟩

theorem mxAt_lt_K {α : Ordinal.{0}} (hα : α < Om 1) : S.psi α (Om (1 + 1)) < mxK S := mxPsi2_lt hα hα

theorem mxK_SC : SC (mxK S) := SC_psi (InR_Om_succ 1) _

theorem mxK_lt_Om2 : mxK S < Om (1 + 1) := psi_lt (InR_Om_succ 1) _

theorem mxOm1_lt_K : Om (1 : Ordinal.{0}) < mxK S := (psiS_bounds (S := S) _ 1).1

theorem mxOm1_lt_OmW : Om (1 : Ordinal.{0}) < Om ω := Om_lt_Om.2 one_lt_omega0

/-- `K < θ`. -/
theorem mxK_lt_th : mxK S < ConjT.th S :=
  psi_lt_psi_of_mem (InR_Om_succ 1) mxOm1_lt_OmW (CSet.Om_mem (CSet.one_mem _ _))

theorem mxOm2_mem (a b : Ordinal.{0}) : Om (1 + 1 : Ordinal.{0}) ∈ S.CSet a b :=
  CSet.Om_mem (CSet.add_mem (CSet.one_mem _ _) (CSet.one_mem _ _))

/-! ## The hull below `K` -/

/-- **At a named restart the hull below `K` is the set of codes over `ρ_λ` with the atoms `ψ_{Ω₂}(α)`, `α < ρ_λ`.** -/
theorem mxHull_iff {l ηx x : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) (hxK : x < mxK S) :
    x ∈ cdHull S l ↔ GxCl (upsilon l) (mxAt S (upsilon l)) x := by
  have hpv := cdEta_pv (S := S) hl.1 hX
  set A := ConjT.Aη S (cdEta S l) with hA
  have hρ : S.psi A (Om 1) = upsilon l := hpv
  have hρ0 : 0 < upsilon l := mvUps_pos hl
  have hWA : Om ω ≤ A := le_self_add
  unfold cdHull
  rw [← hA]
  constructor
  · intro hx
    have key : ∀ y ∈ S.CSet A (upsilon l), y < Om 1 → y < upsilon l := fun y hy hy1 => by
      rw [← hρ] at hy ⊢; exact lt_psi_of_mem Low.InR_Om_one hy hy1
    revert hxK
    have hx' := hx
    induction hx with
    | small h => exact fun _ => GxCl.small h
    | zero => exact fun _ => GxCl.zero hρ0
    | inacc n =>
      exact fun h => absurd ((h.trans mxK_lt_Om2).trans (mxOm2_lt_I n)) (lt_irrefl _)
    | inaccW =>
      exact fun h => absurd ((h.trans mxK_lt_Om2).trans mxOm2_lt_Iw) (lt_irrefl _)
    | @add x y hx1 hy1 ihx ihy =>
      intro h
      exact GxCl.add (ihx hx1 (lt_of_le_of_lt le_self_add h)) (ihy hy1 (lt_of_le_of_lt le_add_self h))
    | @phi x y hx1 hy1 ihx ihy =>
      intro h
      exact GxCl.phi (ihx hx1 (lt_of_le_of_lt (left_le_veblen x y) h))
        (ihy hy1 (lt_of_le_of_lt (right_le_veblen x y) h))
    | @om x hx1 _ =>
      intro h
      have h2 : x < 1 + 1 := Om_lt_Om.1 (h.trans mxK_lt_Om2)
      rcases (Order.lt_add_one_iff.1 h2).lt_or_eq with h0 | h1
      · rw [Order.lt_one_iff] at h0; rw [h0, Om_zero]; exact GxCl.zero hρ0
      · rw [h1]; exact GxCl.om
    | @coll π e hπ hπ1 he1 _ _ =>
      intro h
      rcases hπ with ⟨n, rfl⟩ | ⟨s, rfl⟩
      · exfalso
        have h2 : Om (1 + 1 : Ordinal.{0}) < S.psi e.1 (S.I n) :=
          lt_psi_of_mem (InR_I n) (mxOm2_mem _ _) (mxOm2_lt_I n)
        exact absurd (h2.trans (h.trans mxK_lt_Om2)) (lt_irrefl _)
      rcases eq_or_ne s 0 with rfl | hs0
      · rw [zero_add] at hx' ⊢
        exact GxCl.small (key _ hx' (psi_lt Low.InR_Om_one _))
      rcases eq_or_ne s 1 with rfl | hs1
      · rcases lt_or_ge e.1 (Om 1) with he | he
        · exact GxCl.atom ⟨e.1, key _ he1 he, rfl⟩
        · exact absurd ((psi_mono (S := S) (InR_Om_succ 1) he).1) (not_le.2 h)
      · exfalso
        have h2s : 1 + 1 ≤ s := Order.add_one_le_of_lt (lt_of_le_of_ne
          (Order.one_le_iff_ne_zero.2 hs0) (Ne.symm hs1))
        have h2 := (Om_lt_psiS (S := S) e.1 s).2 h2s
        exact absurd (h2.trans (h.trans mxK_lt_Om2)) (lt_irrefl _)
  · intro hx
    clear hxK
    induction hx with
    | small h => exact CSet.of_lt h
    | om => exact CSet.Om_mem (CSet.one_mem _ _)
    | atom hs =>
      obtain ⟨α, hα, rfl⟩ := hs
      have hα1 : α < Om 1 := hα.trans (hρ ▸ psi_lt Low.InR_Om_one _)
      exact CSet.psi_mem ((hα1.trans mxOm1_lt_OmW).trans_le hWA) (InR_Om_succ 1) (mxOm2_mem _ _)
        (CSet.of_lt hα)
    | add _ _ ihx ihy => exact CSet.add_mem ihx ihy
    | phi _ _ ihx ihy => exact CSet.phi_mem ihx ihy

/-- **`Θ_λ(m) = gxTh ρ_λ (mxAt ρ_λ) m`** for `m ≤ K` at a named restart. -/
theorem mxTheta_K {l ηx m : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) (hm : m ≤ mxK S) :
    cdTheta S l m = gxTh (upsilon l) (mxAt S (upsilon l)) m :=
  ggOtp_congr m fun _ hx => mxHull_iff hl hX (hx.trans_le hm)

/-! ## The readings of the atoms -/

/-- A code below `m` is read below every strongly critical `X > Z` that is above the readings of the atoms below
`m`. -/
theorem mxGx_bound {Z m X : Ordinal.{0}} {At : Set Ordinal.{0}} (hZ : SC Z) (hZ1 : Z < Om 1) (hAt : GxAt At)
    (hX : SC X) (hZX : Z < X) (hatom : ∀ s ∈ At, s < m → gxTh Z At s < X) :
    ∀ c, GxCl Z At c → c < m → gxTh Z At c < X := by
  intro c hc
  induction hc with
  | small h => exact fun _ => by rw [gxTh_small h.le]; exact h.trans hZX
  | om => exact fun _ => by rw [gxTh_Om1 hZ hZ1 hAt]; exact hZX
  | atom hs => exact hatom _ hs
  | @add u v hu _ ihu ihv =>
    intro h
    rw [gxTh_add hZ hAt hu]
    exact hX.isPrincipal (ihu (lt_of_le_of_lt le_self_add h)) (ihv (lt_of_le_of_lt le_add_self h))
  | @phi a b ha hb iha ihb =>
    intro h
    rw [gxTh_phi hZ hAt a ha b hb]
    exact hX.2 _ (iha (lt_of_le_of_lt (left_le_veblen a b) h)) _ (ihb (lt_of_le_of_lt (right_le_veblen a b) h))

/-- `ψ_{Ω₁}` is injective on own arguments. -/
theorem mxPsi_inj {A A' : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1)))
    (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1))) (h : S.psi A (Om 1) = S.psi A' (Om 1)) : A = A' := by
  have hc := compare_psi Low.InR_Om_one hA hA'
  rw [h, compare_eq_iff_eq.2 rfl] at hc
  exact compare_eq_iff_eq.1 hc.symm

/-- **`Θ(ψ_{Ω₂}(α)) = ψ_{Ω₁}(A + 1 + α)`** for `α < ρ = ψ_{Ω₁}(A)`, `A` own. -/
theorem mxTh_atom {ρ A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = ρ) :
    ∀ α, α < ρ → gxTh ρ (mxAt S ρ) (S.psi α (Om (1 + 1))) = S.psi (A + 1 + α) (Om 1) := by
  have hρSC : SC ρ := hρ ▸ SC_psi Low.InR_Om_one A
  have hρ1 : ρ < Om 1 := hρ ▸ psi_lt Low.InR_Om_one A
  have hAt : GxAt (mxAt S ρ) := mxAt_GxAt ρ
  -- the right side: strictly increasing, above `ρ`
  have hown : ∀ α, α < ρ → ∀ d, A + 1 + α ≤ d → A + 1 + α ∈ S.CSet d (S.psi d (Om 1)) := by
    intro α hα d hd
    have hAd : A ≤ d := le_self_add.trans (le_self_add.trans hd)
    have hρd : ρ ≤ S.psi d (Om 1) := hρ ▸ (psi_mono (S := S) Low.InR_Om_one hAd).1
    exact CSet.add_mem (CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one hAd).2 hA) (CSet.one_mem _ _))
      (CSet.of_lt (hα.trans_le hρd))
  have hbmono : ∀ β α, β < α → α < ρ → S.psi (A + 1 + β) (Om 1) < S.psi (A + 1 + α) (Om 1) :=
    fun β α h hα => psi_lt_psi_of_mem Low.InR_Om_one ((add_lt_add_iff_left _).2 h)
      (hown β (h.trans hα) _ ((add_le_add_iff_left _).2 h.le))
  have hρb : ∀ α, ρ < S.psi (A + 1 + α) (Om 1) := by
    intro α
    rw [← hρ]
    refine psi_lt_psi_of_mem Low.InR_Om_one ((lt_add_one A).trans_le le_self_add) ?_
    exact (psi_mono (S := S) Low.InR_Om_one (le_self_add.trans le_self_add)).2 hA
  intro α
  induction α using WellFoundedLT.induction with
  | ind α IH =>
  intro hαρ
  have hα1 : α < Om 1 := hαρ.trans hρ1
  set T := gxTh ρ (mxAt S ρ) (S.psi α (Om (1 + 1))) with hT
  set b := S.psi (A + 1 + α) (Om 1) with hb
  have hTSC : SC T := gxTh_SC hρSC hAt (SC_psi (InR_Om_succ 1) α)
    (hρ1.trans (psiS_bounds (S := S) α 1).1)
  have hρT : ρ < T := by
    have := gxTh_lt (Z := ρ) (At := mxAt S ρ) GxCl.om (psiS_bounds (S := S) α 1).1
    rwa [gxTh_Om1 hρSC hρ1 hAt] at this
  have hβT : ∀ β < α, S.psi (A + 1 + β) (Om 1) < T := by
    intro β hβ
    rw [← IH β hβ (hβ.trans hαρ)]
    exact gxTh_lt (GxCl.atom ⟨β, hβ.trans hαρ, rfl⟩) (mxPsi2_lt hβ (hβ.trans hα1))
  apply le_antisymm
  · -- `T ≤ b`
    have hbd : ∀ c, GxCl ρ (mxAt S ρ) c → c < S.psi α (Om (1 + 1)) → gxTh ρ (mxAt S ρ) c < b := by
      refine mxGx_bound hρSC hρ1 hAt (SC_psi Low.InR_Om_one _) (hρb α) ?_
      rintro s ⟨β, hβρ, rfl⟩ hs
      have hβα : β < α := (mxPsi2_lt_iff (hβρ.trans hρ1) hα1).1 hs
      rw [IH β hβα hβρ]
      exact hbmono β α hβα hαρ
    rw [hT]
    unfold gxTh
    rw [cdOtp_eq]
    refine ciSup_le' fun c => ?_
    split_ifs with hc
    · exact Order.add_one_le_of_lt (hbd c.1 hc c.2)
    · exact zero_le
  · -- `b ≤ T`
    refine psi_le_of_good (CSet.Om_mem (CSet.one_mem _ _)) ?_
    intro x hx
    induction hx with
    | @small x hxb => exact fun _ => hxb
    | zero => exact fun _ => hTSC.1
    | inacc n => exact fun h => absurd h (not_lt.2 (gg_Om1_lt_I S n).le)
    | inaccW => exact fun h => absurd h (not_lt.2 (gg_Om1_lt_Iw S).le)
    | @add x y _ _ ihx ihy =>
      intro h
      exact hTSC.isPrincipal (ihx (lt_of_le_of_lt le_self_add h)) (ihy (lt_of_le_of_lt le_add_self h))
    | @phi x y _ _ ihx ihy =>
      intro h
      exact hTSC.2 x (ihx (lt_of_le_of_lt (left_le_veblen x y) h)) y
        (ihy (lt_of_le_of_lt (right_le_veblen x y) h))
    | @om x _ _ =>
      intro h
      rw [mxOm_lt_one h, Om_zero]
      exact hTSC.1
    | @coll π e hπ _ _ _ _ =>
      intro h
      have hπ1 : π = Om 1 := by
        by_contra hne
        exact absurd h (not_lt.2 (mxOm1_le_psi hπ hne))
      subst hπ1
      rcases le_or_gt e.1 A with heA | heA
      · exact lt_of_le_of_lt (hρ ▸ (psi_mono (S := S) Low.InR_Om_one heA).1) hρT
      · obtain ⟨d, hd⟩ := exists_add_of_le heA.le
        have hd0 : d ≠ 0 := by rintro rfl; rw [add_zero] at hd; exact absurd hd heA.ne'
        have hd1 : d < 1 + α := by
          have := e.2; rw [hd, add_assoc] at this; exact (add_lt_add_iff_left A).1 this
        have hdec : 1 + (d - 1) = d := Ordinal.add_sub_cancel_of_le (Order.one_le_iff_ne_zero.2 hd0)
        have hβα : d - 1 < α := by
          rw [← hdec] at hd1; exact (add_lt_add_iff_left 1).1 hd1
        have he : e.1 = A + 1 + (d - 1) := by rw [hd, add_assoc, hdec]
        show S.psi e.1 (Om 1) < T
        rw [he]
        exact hβT _ hβα

end Googology.Trans.PoR.InaccPsi.R2.Mx

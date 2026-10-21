import Googology.Trans.PoR.InaccPsi.R2.LdHull

/-!
# The first atom above the layers: `F = ψ_{Ω₂}(Ω₂) = sup_j K_j`, its reading `ψ_{Ω₁}(A + Ω₁)`, and `F⁺ = ψ_{Ω₂}(Ω₂ + 1)`

`ψ = S.psi`, `K_0 = Ω₁`, `K_{j+1} = ψ_{Ω₂}(K_j)` (`Mx.mxKs`), `F = ψ_{Ω₂}(Ω₂)` (`ldF`), `F⁺ = ψ_{Ω₂}(Ω₂ + 1)` (`ldFp`),
`H_λ = Cl(A_{η_λ}, ρ_λ)`, `ldAtR λ` the atoms of `H_λ` below `Ω₂` (`R2.LdHull`), `Θ = gxTh ρ_λ (ldAtR λ)`,
`B_n = Bc.bcB S n`.

* `ldKs_lt_F`, `ldF_sup` (**`F = sup_j K_j`**: every `x < F` is below some `K_j`), `ldF_le_of`, `ldPsi2_ge_F`
  (`ψ_{Ω₂}(a) ≥ F` for `a ≥ F`);
* `ldF_lt_Fp`, `ldFp_le` (**`F⁺` is the least strongly critical ordinal above `F`**), `ldFp_lt_th`, `ldAt_le_F`
  (an atom below `F⁺` is at most `F`);
* `ldAtR_lt_F` (**an atom of the hull below `F` is an atom `ψ_{Ω₂}(a)` of a layer**, `a` a code of the layer `j`,
  `a < K_j`), `ldTh_layAtom` (its reading `ψ_{Ω₁}(A + 1 + Θ(a))` in the full hull);
* `ldTh_F` (**`Θ_λ(F) = ψ_{Ω₁}(A + Ω₁)`** for every own `A` with `ψ_{Ω₁}(A) = ρ_λ`: both are the least strongly
  critical ordinal above `ρ_λ` closed under `d ↦ ψ_{Ω₁}(A + d)`);
* `ldOm2_D` (`Ω₂ ∈ MvD`, `B_n Ω₂ = Ω₂`), `ldB_F` (**`B_n F = F`**), `ldB_psi_add` (**`B_n(ψ_{Ω₁}(A_η + d)) =
  ψ_{Ω₁}(A' + B_n d)` for every `d ∈ MvD` with `A_η + d` own**, uncountable `d` included; the proof of
  `Mx.mxB_psi_add`, which asked `d < ψ_{Ω₁}(A_η + d)` only to get these two facts).

No new axiom.  New definitions: `ldF`, `ldFp`, `ldTwoT`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ld

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Bc Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Sf
  Googology.Trans.PoR.InaccPsi.R2.Mx

variable {S : InaccSeq.{0}}

/-- `F = ψ_{Ω₂}(Ω₂)`. -/
noncomputable def ldF (S : InaccSeq.{0}) : Ordinal.{0} := S.psi (Om (1 + 1)) (Om (1 + 1))

/-- `F⁺ = ψ_{Ω₂}(Ω₂ + 1)`. -/
noncomputable def ldFp (S : InaccSeq.{0}) : Ordinal.{0} := S.psi (Om (1 + 1) + 1) (Om (1 + 1))

theorem ldOm2_lt_OmW : Om (1 + 1 : Ordinal.{0}) < Om ω :=
  Om_lt_Om.2 (by rw [one_add_one_eq_two]; exact natCast_lt_omega0 2)

theorem ldF_SC : SC (ldF S) := SC_psi (InR_Om_succ 1) _
theorem ldFp_SC : SC (ldFp S) := SC_psi (InR_Om_succ 1) _
theorem ldF_lt_Om2 : ldF S < Om (1 + 1) := psi_lt (InR_Om_succ 1) _
theorem ldFp_lt_Om2 : ldFp S < Om (1 + 1) := psi_lt (InR_Om_succ 1) _
theorem ldOm1_lt_F : Om (1 : Ordinal.{0}) < ldF S := (psiS_bounds (S := S) _ 1).1
theorem ldOm1_lt_Fp : Om (1 : Ordinal.{0}) < ldFp S := (psiS_bounds (S := S) _ 1).1

theorem ldKs_le_F : ∀ j, mxKs S j ≤ ldF S
  | 0 => ldOm1_lt_F.le
  | j + 1 => (psi_mono (S := S) (InR_Om_succ 1) (mxKs_lt_Om2 j).le).1

theorem ldKs_lt_F (j : ℕ) : mxKs S j < ldF S := (mxKs_lt_succ j).trans_le (ldKs_le_F (j + 1))

/-- **`F = sup_j K_j`**: every `x < F` is below some `K_j`. -/
theorem ldF_sup {x : Ordinal.{0}} (hx : x < ldF S) : ∃ j, x < mxKs S j := by
  have hbdd : BddAbove (Set.range (mxKs S)) := Ordinal.bddAbove_of_small
  have hlt : ∀ y, y < ⨆ j, mxKs S j ↔ ∃ j, y < mxKs S j := fun y => lt_ciSup_iff hbdd
  have hKQ : ∀ j, mxKs S j < ⨆ j, mxKs S j := fun j => (hlt _).2 ⟨j + 1, mxKs_lt_succ j⟩
  have hΩQ : Om (1 : Ordinal.{0}) < ⨆ j, mxKs S j := hKQ 0
  have hFQ : ldF S ≤ ⨆ j, mxKs S j := by
    refine psi_le_of_good (mxOm2_mem _ _) ?_
    intro y hy
    induction hy with
    | small h => exact fun _ => h
    | zero => exact fun _ => (Om_pos one_ne_zero).trans hΩQ
    | inacc n => exact fun h => absurd (h.trans (mxOm2_lt_I n)) (lt_irrefl _)
    | inaccW => exact fun h => absurd (h.trans mxOm2_lt_Iw) (lt_irrefl _)
    | @add x y _ _ ihx ihy =>
      intro h
      obtain ⟨i, hi⟩ := (hlt _).1 (ihx (lt_of_le_of_lt le_self_add h))
      obtain ⟨k, hk⟩ := (hlt _).1 (ihy (lt_of_le_of_lt le_add_self h))
      have hi' := hi.trans_le (mxKs_mono (S := S) (le_max_left i k))
      have hk' := hk.trans_le (mxKs_mono (S := S) (le_max_right i k))
      exact ((mxKs_SC (max i k)).isPrincipal hi' hk').trans (hKQ _)
    | @phi x y _ _ ihx ihy =>
      intro h
      obtain ⟨i, hi⟩ := (hlt _).1 (ihx (lt_of_le_of_lt (left_le_veblen x y) h))
      obtain ⟨k, hk⟩ := (hlt _).1 (ihy (lt_of_le_of_lt (right_le_veblen x y) h))
      have hi' := hi.trans_le (mxKs_mono (S := S) (le_max_left i k))
      have hk' := hk.trans_le (mxKs_mono (S := S) (le_max_right i k))
      exact ((mxKs_SC (max i k)).2 _ hi' _ hk').trans (hKQ _)
    | @om x _ _ =>
      intro h
      have h2 : x < 1 + 1 := Om_lt_Om.1 h
      rcases (Order.lt_add_one_iff.1 h2).lt_or_eq with h0 | h1
      · rw [Order.lt_one_iff] at h0; rw [h0, Om_zero]; exact (Om_pos one_ne_zero).trans hΩQ
      · rw [h1]; exact hΩQ
    | @coll π e hπ _ _ _ ihe =>
      intro h
      rcases hπ with ⟨n, rfl⟩ | ⟨s, rfl⟩
      · exfalso
        have h2 : Om (1 + 1 : Ordinal.{0}) < S.psi e.1 (S.I n) :=
          lt_psi_of_mem (InR_I n) (mxOm2_mem _ _) (mxOm2_lt_I n)
        exact absurd (h2.trans h) (lt_irrefl _)
      rcases eq_or_ne s 0 with rfl | hs0
      · rw [zero_add]; exact (psi_lt Low.InR_Om_one _).trans hΩQ
      rcases eq_or_ne s 1 with rfl | hs1
      · obtain ⟨j, hj⟩ := (hlt _).1 (ihe e.2)
        have := hKQ (j + 1)
        rw [mxKs_succ] at this
        exact ((psi_mono (S := S) (InR_Om_succ 1) hj.le).1).trans_lt this
      · exfalso
        have h2s : 1 + 1 ≤ s := Order.add_one_le_of_lt (lt_of_le_of_ne
          (Order.one_le_iff_ne_zero.2 hs0) (Ne.symm hs1))
        have h2 := (Om_lt_psiS (S := S) e.1 s).2 h2s
        exact absurd (h2.trans h) (lt_irrefl _)
  exact (hlt x).1 (hx.trans_le hFQ)

theorem ldF_le_of {y : Ordinal.{0}} (h : ∀ j, mxKs S j ≤ y) : ldF S ≤ y := by
  by_contra h'
  push Not at h'
  obtain ⟨j, hj⟩ := ldF_sup h'
  exact absurd hj (not_lt.2 (h j))

/-- `ψ_{Ω₂}(a) ≥ F` for `a ≥ F`. -/
theorem ldPsi2_ge_F {a : Ordinal.{0}} (ha : ldF S ≤ a) : ldF S ≤ S.psi a (Om (1 + 1)) :=
  ldF_le_of fun j => (mxKs_lt_succ j).le.trans
    ((psi_mono (S := S) (InR_Om_succ 1) ((ldKs_le_F j).trans ha)).1)

theorem ldF_lt_Fp : ldF S < ldFp S :=
  psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_one _) (mxOm2_mem _ _)

/-- **`F⁺` is the least strongly critical ordinal above `F`.** -/
theorem ldFp_le {X : Ordinal.{0}} (hX : SC X) (hFX : ldF S < X) : ldFp S ≤ X := by
  rcases le_or_gt (Om (1 + 1)) X with h2 | h2
  · exact ldFp_lt_Om2.le.trans h2
  have hΩX : Om (1 : Ordinal.{0}) < X := ldOm1_lt_F.trans hFX
  refine psi_le_of_good (mxOm2_mem _ _) ?_
  intro y hy
  induction hy with
  | small h => exact fun _ => h
  | zero => exact fun _ => hX.1
  | inacc n => exact fun h => absurd (h.trans (mxOm2_lt_I n)) (lt_irrefl _)
  | inaccW => exact fun h => absurd (h.trans mxOm2_lt_Iw) (lt_irrefl _)
  | @add x y _ _ ihx ihy =>
    intro h
    exact hX.isPrincipal (ihx (lt_of_le_of_lt le_self_add h)) (ihy (lt_of_le_of_lt le_add_self h))
  | @phi x y _ _ ihx ihy =>
    intro h
    exact hX.2 _ (ihx (lt_of_le_of_lt (left_le_veblen x y) h)) _
      (ihy (lt_of_le_of_lt (right_le_veblen x y) h))
  | @om x _ _ =>
    intro h
    have h2 : x < 1 + 1 := Om_lt_Om.1 h
    rcases (Order.lt_add_one_iff.1 h2).lt_or_eq with h0 | h1
    · rw [Order.lt_one_iff] at h0; rw [h0, Om_zero]; exact hX.1
    · rw [h1]; exact hΩX
  | @coll π e hπ _ _ _ _ =>
    intro h
    rcases hπ with ⟨n, rfl⟩ | ⟨s, rfl⟩
    · exfalso
      have h2 : Om (1 + 1 : Ordinal.{0}) < S.psi e.1 (S.I n) :=
        lt_psi_of_mem (InR_I n) (mxOm2_mem _ _) (mxOm2_lt_I n)
      exact absurd (h2.trans h) (lt_irrefl _)
    rcases eq_or_ne s 0 with rfl | hs0
    · rw [zero_add]; exact (psi_lt Low.InR_Om_one _).trans hΩX
    rcases eq_or_ne s 1 with rfl | hs1
    · have he : e.1 ≤ Om (1 + 1) := Order.lt_add_one_iff.1 e.2
      exact ((psi_mono (S := S) (InR_Om_succ 1) he).1).trans_lt hFX
    · exfalso
      have h2s : 1 + 1 ≤ s := Order.add_one_le_of_lt (lt_of_le_of_ne
        (Order.one_le_iff_ne_zero.2 hs0) (Ne.symm hs1))
      have h2 := (Om_lt_psiS (S := S) e.1 s).2 h2s
      exact absurd (h2.trans h) (lt_irrefl _)

/-- `F⁺ < θ`. -/
theorem ldFp_lt_th : ldFp S < ConjT.th S :=
  psi_lt_psi_of_mem (InR_Om_succ 1) ((Om_isPrincipal omega0_ne_zero) ldOm2_lt_OmW
    (one_lt_omega0.trans (omega0_lt_Om omega0_ne_zero))) (CSet.succ_mem (mxOm2_mem _ _))

/-- An atom below `F⁺` is at most `F`. -/
theorem ldAt_le_F {At : Set Ordinal.{0}} (hAt : GxAt At) {s : Ordinal.{0}} (hs : s ∈ At)
    (hsF : s < ldFp S) : s ≤ ldF S := by
  by_contra h
  push Not at h
  exact absurd hsF (not_lt.2 (ldFp_le (hAt s hs).1 h))

/-! ## The atoms below `F` and the reading of `F` -/

/-- **An atom of the hull below `F` is an atom of a layer.** -/
theorem ldAtR_lt_F {l ηx s : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hs : s ∈ ldAtR S l) (hsF : s < ldF S) :
    ∃ j a, GxCl (upsilon l) (mxAtL S (upsilon l) j) a ∧ a < mxKs S j ∧ s = S.psi a (Om (1 + 1)) := by
  obtain ⟨a, ha, -, rfl⟩ := hs
  have haF : a < ldF S := by
    by_contra h
    push Not at h
    exact absurd hsF (not_lt.2 (ldPsi2_ge_F h))
  obtain ⟨j, hj⟩ := ldF_sup haF
  exact ⟨j, a, (mxHullL_iff hl hX j a hj).1 ha, hj, rfl⟩

/-- The reading of a layer atom in the full hull: `Θ(ψ_{Ω₂}(a)) = ψ_{Ω₁}(A + 1 + Θ(a))`. -/
theorem ldTh_layAtom {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) {j : ℕ} {a : Ordinal.{0}}
    (ha : GxCl (upsilon l) (mxAtL S (upsilon l) j) a) (haK : a < mxKs S j) :
    gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1))) =
      S.psi (A + 1 + gxTh (upsilon l) (ldAtR S l) a) (Om 1) := by
  have htK : S.psi a (Om (1 + 1)) < mxKs S (j + 1) := mxPsi2_ltL haK (mxKs_lt_succ j)
  rw [ldLay_th hl hX (j + 1) htK.le, ldLay_th hl hX (j + 1) (haK.le.trans (mxKs_lt_succ j).le)]
  exact mxThL_atom hA hρ j a ha haK

theorem ldF_mem {l : Ordinal.{0}} : ldF S ∈ ldAtR S l :=
  ⟨Om (1 + 1), mxOm2_mem _ _, ldOm2_lt_OmW.trans_le le_self_add, rfl⟩

/-- **`Θ_λ(F) = ψ_{Ω₁}(A + Ω₁)`** for every own `A` with `ψ_{Ω₁}(A) = ρ_λ`. -/
theorem ldTh_F {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    gxTh (upsilon l) (ldAtR S l) (ldF S) = S.psi (A + Om 1) (Om 1) := by
  have hρSC : SC (upsilon l) := hρ ▸ SC_psi Low.InR_Om_one A
  have hρ1 : upsilon l < Om 1 := hρ ▸ psi_lt Low.InR_Om_one A
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hXSC : SC (S.psi (A + Om 1) (Om 1)) := SC_psi Low.InR_Om_one _
  have hAX : A ∈ S.CSet (A + Om 1) (S.psi (A + Om 1) (Om 1)) :=
    (psi_mono (S := S) Low.InR_Om_one (le_self_add : A ≤ A + Om 1)).2 hA
  have hρX : upsilon l < S.psi (A + Om 1) (Om 1) := by
    rw [← hρ]
    exact psi_lt_psi_of_mem Low.InR_Om_one (lt_add_of_pos_right A (Om_pos one_ne_zero)) hAX
  have hlay : ∀ t ∈ ldAtR S l, t < ldF S → gxTh (upsilon l) (ldAtR S l) t < S.psi (A + Om 1) (Om 1) := by
    intro t ht htF
    obtain ⟨j, a, ha, haK, rfl⟩ := ldAtR_lt_F hl hX ht htF
    have ha' : GxCl (upsilon l) (ldAtR S l) a := (ldLay_iff hl hX j haK).2 ha
    rw [ldTh_layAtom hl hX hA hρ ha haK]
    have hγ : gxTh (upsilon l) (ldAtR S l) a <
        S.psi (A + 1 + gxTh (upsilon l) (ldAtR S l) a) (Om 1) := by
      rw [← ldTh_layAtom hl hX hA hρ ha haK]; exact gxTh_lt ha' (mxPsi2_gt j a haK)
    have hγ1 := hγ.trans (psi_lt Low.InR_Om_one _)
    have hlt : A + 1 + gxTh (upsilon l) (ldAtR S l) a < A + Om 1 := by
      rw [add_assoc]; exact (add_lt_add_iff_left A).2 (ldOm1_prin one_lt_Om1 hγ1)
    have hγX := hγ.trans_le (psi_mono (S := S) Low.InR_Om_one hlt.le).1
    exact psi_lt_psi_of_mem Low.InR_Om_one hlt
      (CSet.add_mem (CSet.add_mem hAX (CSet.one_mem _ _)) (CSet.of_lt hγX))
  have hle := ldAtom_le hρSC hρ1 hAt hXSC hρX hlay
  obtain ⟨hTSC, hρT, hTs⟩ := ldAtom_ge hρSC hρ1 hAt (ldF_mem (S := S) (l := l))
  refine le_antisymm hle (ldPsi1_le hTSC ?_)
  intro e he hmod
  rcases le_or_gt e A with heA | heA
  · exact lt_of_le_of_lt (hρ ▸ (psi_mono (S := S) Low.InR_Om_one heA).1) hρT
  · obtain ⟨d, rfl⟩ := exists_add_of_le heA.le
    have hd1 : d < Om 1 := (add_lt_add_iff_left A).1 he
    have hdT : d < gxTh (upsilon l) (ldAtR S l) (ldF S) := by
      rw [ldMod_add_lt A hd1] at hmod; exact le_add_self.trans_lt hmod
    obtain ⟨c, hc, hcF, hcd⟩ := gxTh_onto hdT
    obtain ⟨j, hj⟩ := ldF_sup hcF
    have hcj : GxCl (upsilon l) (mxAtL S (upsilon l) j) c := (ldLay_iff hl hX j hj).1 hc
    have hc2 : c < Om (1 + 1) := hcF.trans ldF_lt_Om2
    have htat : S.psi c (Om (1 + 1)) ∈ ldAtR S l :=
      ⟨c, (ldHull_iff hl hX hc2).2 hc, (hc2.trans ldOm2_lt_OmW).trans_le le_self_add, rfl⟩
    have htF : S.psi c (Om (1 + 1)) < ldF S :=
      (mxPsi2_ltL hj (mxKs_lt_succ j)).trans (ldKs_lt_F (j + 1))
    have h1 := hTs _ htat htF
    rw [ldTh_layAtom hl hX hA hρ hcj hj, hcd] at h1
    refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one ?_).1 h1
    rw [add_assoc]; exact (add_le_add_iff_left A).2 le_add_self

/-! ## `B_n` on `Ω₂`, `F` and `ψ_{Ω₁}(A_η + d)` -/

/-- The term `Ω₂ = om (1 + 1)`. -/
def ldTwoT : Term := om (add tOne tOne)

theorem ldTwoT_val : val S ldTwoT = Om (1 + 1) := by
  show Om (val S tOne + val S tOne) = _
  rw [val_tOne]

theorem ldTwoT_D : bcD S ldTwoT := by
  refine bcD_free ⟨⟨NF_tOne, NF_tOne, rfl, tOne_ne_zero, ?_⟩, by simp, rfl⟩ ⟨bcFree_tOne, bcFree_tOne⟩
  show cmp tOne tOne ≠ .gt
  rw [cmp_self]; simp

/-- **`Ω₂ ∈ MvD` and `B_n Ω₂ = Ω₂`.** -/
theorem ldOm2_D {k : ℕ} : MvD S (Om (1 + 1)) ∧ bcB S k (Om (1 + 1)) = Om (1 + 1) := by
  have h := ldTwoT_D (S := S)
  rw [← ldTwoT_val (S := S)]
  exact ⟨mvD_of_term h, by rw [mvB_term h, bcSig_free (show bcFree ldTwoT from ⟨bcFree_tOne, bcFree_tOne⟩)]⟩

/-- **`B_n F = F`**, and `F ∈ MvD`. -/
theorem ldB_F {k : ℕ} : MvD S (ldF S) ∧ bcB S k (ldF S) = ldF S := by
  obtain ⟨hD, hB⟩ := ldOm2_D (S := S) (k := k)
  obtain ⟨hD', hB'⟩ := mxB_atom (n := k) hD (mxOm2_mem (S := S) _ _)
  exact ⟨hD', by unfold ldF; rw [hB', hB]⟩

/-- **`B_n(ψ_{Ω₁}(A_η + d)) = ψ_{Ω₁}(A' + B_n d)`** for every `d ∈ MvD` with `A_η + d` own. -/
theorem ldB_psi_add {n : ℕ} {η d : Ordinal.{0}} (hg : Bt.Good S η) (hlo : Bc.bcC S n ≤ Pv S η)
    (hDd : MvD S d)
    (hown1 : ConjT.Aη S η + d ∈ S.CSet (ConjT.Aη S η + d) (S.psi (ConjT.Aη S η + d) (Om 1)))
    (hhi : S.psi (ConjT.Aη S η + d) (Om 1) < Bc.bcC S (n + 1)) :
    ∃ A', A' ∈ S.CSet A' (S.psi A' (Om 1)) ∧ Bc.bcB S n (Pv S η) = S.psi A' (Om 1) ∧
      Bc.bcB S n (S.psi (ConjT.Aη S η + d) (Om 1)) = S.psi (A' + Bc.bcB S n d) (Om 1) := by
  have hP1 : Pv S η ≤ S.psi (ConjT.Aη S η + d) (Om 1) :=
    (psi_mono (S := S) Low.InR_Om_one (le_self_add : ConjT.Aη S η ≤ ConjT.Aη S η + d)).1
  have hAL : ConjT.Aη S η < S.Lam := (sfA_lt (hP1.trans_lt hhi)).2
  have hown := sfOwn hg hAL
  have hαA : bcAlpha S (n + 1) ≤ ConjT.Aη S η := sfArg_le (sfOwn_alpha S n) hown hlo
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Qq.qqL_lt_omega S (n + 1 + 1)
  have hx0 : Pv S η < Nc.ncL S ω := (hP1.trans_lt hhi).trans hLw
  have hx1 : S.psi (ConjT.Aη S η + d) (Om 1) < Nc.ncL S ω := hhi.trans hLw
  have hDe : bcD S (bcNf S d) := hDd.2
  have hve : val S (bcNf S d) = d := mvD_val hDd
  obtain ⟨a, ha, hva⟩ := sfNf_psi hown (bcD_nf S hx0).1 (val_nf S hx0)
  obtain ⟨a1, ha1, hva1⟩ := sfNf_psi hown1 (bcD_nf S hx1).1 (val_nf S hx1)
  have hD : bcD S (psiS Term.zero a) := ha ▸ bcD_nf S hx0
  have hD1 : bcD S (psiS Term.zero a1) := ha1 ▸ bcD_nf S hx1
  have hN := hD.1
  have hN1 := hD1.1
  have hAW : val S a < bcAlphaW S := hD.2.2.2 rfl
  have hA1W : val S a1 < bcAlphaW S := hD1.2.2.2 rfl
  have hlo0 : bcAlpha S (n + 1) ≤ val S a := hva ▸ hαA
  have hlo1 : bcAlpha S (n + 1) ≤ val S a1 := by rw [hva1]; exact hαA.trans le_self_add
  have hB0 := sfB_psi (n := n) hN hlo0 hAW
  have hB1 := sfB_psi (n := n) hN1 hlo1 hA1W
  rw [hva] at hB0
  rw [hva1] at hB1
  have hpre := (bc_pre_iff S hN.2.1 hAW).2 hlo0
  have hpre1 := (bc_pre_iff S hN1.2.1 hA1W).2 hlo1
  have hvρ : val S a = bcAlpha S (n + 1) + val S (bcDrop (n + 3) a) := by
    have := val_of_pre S hN.2.1 hpre; rwa [sfPre_len] at this
  have hvρ1 : val S a1 = bcAlpha S (n + 1) + val S (bcDrop (n + 3) a1) := by
    have := val_of_pre S hN1.2.1 hpre1; rwa [sfPre_len] at this
  have hDa : bcD S a := bcD_sub hD (sub_psiS_a _ _)
  have hDρ : bcD S (bcDrop (n + 3) a) := bcD_drop hDa (n + 3)
  have hvr1 : val S (bcDrop (n + 3) a1) = val S (bcDrop (n + 3) a) + d := by
    have e1 : bcAlpha S (n + 1) + val S (bcDrop (n + 3) a1) =
        bcAlpha S (n + 1) + (val S (bcDrop (n + 3) a) + d) := by
      rw [← hvρ1, hva1, ← hva, hvρ, add_assoc]
    exact add_left_cancel e1
  have hNρ1 : NF (bcDrop (n + 3) a1) := NF_bcDrop _ hN1.2.1
  obtain ⟨hNadd, hvadd, -⟩ := addNF_spec (S := S) hDρ.1 hDe.1
  have hρ1 : bcDrop (n + 3) a1 = addNF (bcDrop (n + 3) a) (bcNf S d) :=
    eq_of_val_eq S hNρ1 hNadd (by rw [hvadd, hve, hvr1])
  have hσ1 : val S (bcSig (bcPre (n + 1)) bcPreW (bcDrop (n + 3) a1)) =
      val S (bcSig (bcPre (n + 1)) bcPreW (bcDrop (n + 3) a)) + Bc.bcB S n d := by
    rw [hρ1, bcSig_addNF (k := n) hDρ hDe,
      (addNF_spec (S := S) (bc_NF (k := n) hDρ) (bc_NF (k := n) hDe)).2.1]
    rfl
  refine ⟨bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW (bcDrop (n + 3) a)), ?_, hB0, ?_⟩
  · have hσN : NF (bcSig (bcPre (n + 1)) bcPreW (psiS Term.zero a)) := bc_NF (k := n) hD
    rw [bcSig_psiS_zero, bcArg_of_pre hpre, sfPre_len] at hσN
    have hsem : Sem S (psiS Term.zero (bcApp bcPreW
        (bcSig (bcPre (n + 1)) bcPreW (bcDrop (n + 3) a)))) := sem_of_NF hσN
    have h2 := hsem.2.2
    rw [show Om (val S Term.zero + 1) = Om 1 by rw [show val S Term.zero = 0 from rfl, zero_add],
      val_bcApp_preW] at h2
    exact h2
  · rw [hB1, hσ1, add_assoc]

end Googology.Trans.PoR.InaccPsi.R2.Ld

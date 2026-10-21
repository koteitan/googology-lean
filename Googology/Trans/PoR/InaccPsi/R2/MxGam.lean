import Googology.Trans.PoR.InaccPsi.R2.MxLhT
import Googology.Trans.PoR.InaccPsi.R2.SfPv

/-!
# `MwEQtop` at the first strongly critical atom: the long codes `m_λ = Γ_{Ω₁+1}`

`B_n = Bc.bcB S n`, `ψ = S.psi`, `A_η = Ω_ω + θ·η`, `P(η) = ψ_{Ω₁}(A_η)` (`Nm.Pv`), `ρ_λ = υ_λ = P(η_λ)`,
`δ_λ = υ_{λ+ω+1}`, `Θ_λ` the reading (`Cd.cdTheta`), `k_λ = Cd.cdk λ`, `r(λ) = k_λ(Θ_λ(m_λ))`, `ggGam = Γ_{Ω₁+1}`.
An argument `A` is *own* when `A ∈ Cl(A, ψ_{Ω₁}(A))`.

* `mxPsi_succ_le` (**`ψ_{Ω₁}(A + 1)` is below every strongly critical `s > ψ_{Ω₁}(A)`**: by induction on
  `Cl(A + 1, s)`, the members below `Ω₁` are `< s`, as every `ψ_{Ω₁}(e)`, `e ≤ A`, is `≤ ψ_{Ω₁}(A)`), `mxPsi_succ_gt`
  (`ψ_{Ω₁}(A) < ψ_{Ω₁}(A + 1)` for own `A`): **`ψ_{Ω₁}(A + 1) = Γ_{ψ_{Ω₁}(A)+1}`**, the least strongly critical
  ordinal above `ψ_{Ω₁}(A)`;
* `mxGam_psi` (**`Γ_{Ω₁+1} = ψ_{Ω₂}(0)`**), `mxGam_nf` (its normal form is `ψ^S_1(0)`), `mxB_gam` (**`B_n` fixes
  `Γ_{Ω₁+1}`**), `mxGam_lt_th` (`Γ_{Ω₁+1} < θ`);
* `mxGgTh_lt` (a code over `ρ` below `Γ_{Ω₁+1}` is read below every strongly critical `X > ρ`), `mxTheta_gam`
  (**`Θ_λ(Γ_{Ω₁+1})` is the least strongly critical ordinal above `ρ_λ`** at every named restart);
* `mxB_psi1` (**`B_n(P(η)) = ψ_{Ω₁}(A')` and `B_n(ψ_{Ω₁}(A_η + 1)) = ψ_{Ω₁}(A' + 1)`**, `A'` own, at a good `η` in the
  window: as `Sf.sfB_add` with the free summand `1`), so **`B_n(Γ_{ρ+1}) = Γ_{B_n ρ + 1}`** at `ρ = P(η)`;
* `mxEQ_gam` (**`B_n r(λ) = r(λ')` at every long code with `e(η_λ) = Γ_{Ω₁+1}`**, given `L(ω+1) ≤ ν_C`);
* `MxEQtop S` (a hypothesis name): `MwEQtop` at the long codes with `Γ_{Ω₁+1} < e(η_λ)`; `mxEQtop_mw`
  (**`L(ω+1) ≤ ν_C` and `MxEQtop` give `MwEQtop`**), `mxEQtop_of_mw`, `mxRoad2` (the road with `MxLhTopG` and
  `L(ω+1) ≤ ν_C → MxEQtop`).

No new axiom.  New definition: the hypothesis name `MxEQtop`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Mx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Bc Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Sf

variable {S : InaccSeq.{0}}

/-! ## `ψ_{Ω₁}(A + 1)` is the next strongly critical ordinal -/

/-- A collapse at a subscript other than `Ω₁` is at least `Ω₁`. -/
theorem mxOm1_le_psi {π e : Ordinal.{0}} (hπ : S.InR π) (hne : π ≠ Om 1) : Om 1 ≤ S.psi e π := by
  rcases hπ with ⟨n, rfl⟩ | ⟨s, rfl⟩
  · exact (Om_one_lt_psiI e n).le
  · have hs : s ≠ 0 := fun h => hne (by rw [h, zero_add])
    exact ((Om_lt_psiS e s).2 (one_le_iff_ne_zero.2 hs)).le

theorem mxOm_lt_one {x : Ordinal.{0}} (h : Om x < Om 1) : x = 0 := by
  have := Om_lt_Om.1 h
  exact Order.lt_one_iff.1 this

/-- **`ψ_{Ω₁}(A + 1)` is below every strongly critical `s > ψ_{Ω₁}(A)`.** -/
theorem mxPsi_succ_le {A s : Ordinal.{0}} (hs : SC s) (hρs : S.psi A (Om 1) < s) :
    S.psi (A + 1) (Om 1) ≤ s := by
  rcases le_or_gt (Om 1) s with h1 | h1
  · exact (psi_lt Low.InR_Om_one _).le.trans h1
  refine psi_le_of_good (CSet.Om_mem (CSet.one_mem _ _)) ?_
  intro x hx
  induction hx with
  | @small x hxb => exact fun _ => hxb
  | zero => exact fun _ => hs.1
  | inacc n => exact fun h => absurd h (not_lt.2 (gg_Om1_lt_I S n).le)
  | inaccW => exact fun h => absurd h (not_lt.2 (gg_Om1_lt_Iw S).le)
  | @add x y _ _ ihx ihy =>
    intro h
    have hx1 : x < Om 1 := lt_of_le_of_lt le_self_add h
    have hy1 : y < Om 1 := lt_of_le_of_lt le_add_self h
    exact hs.isPrincipal (ihx hx1) (ihy hy1)
  | @phi x y _ _ ihx ihy =>
    intro h
    have hx1 : x < Om 1 := lt_of_le_of_lt (left_le_veblen x y) h
    have hy1 : y < Om 1 := lt_of_le_of_lt (right_le_veblen x y) h
    exact hs.2 x (ihx hx1) y (ihy hy1)
  | @om x _ _ =>
    intro h
    rw [mxOm_lt_one h, Om_zero]
    exact hs.1
  | @coll π e hπ _ _ _ _ =>
    intro h
    have hπ1 : π = Om 1 := by
      by_contra hne
      exact absurd h (not_lt.2 (mxOm1_le_psi hπ hne))
    subst hπ1
    exact lt_of_le_of_lt (psi_mono Low.InR_Om_one (Order.lt_add_one_iff.1 e.2)).1 hρs

/-- `ψ_{Ω₁}(A) < ψ_{Ω₁}(A + 1)` for an own `A`. -/
theorem mxPsi_succ_gt {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) :
    S.psi A (Om 1) < S.psi (A + 1) (Om 1) :=
  psi_lt_psi_of_mem Low.InR_Om_one (lt_add_one A)
    ((psi_mono (S := S) Low.InR_Om_one (le_self_add : A ≤ A + 1)).2 hA)

/-! ## `Γ_{Ω₁+1} = ψ_{Ω₂}(0)`, its normal form, and `B_n` on it -/

theorem mxOm2_lt_I (n : ℕ) : Om (1 + 1 : Ordinal.{0}) < S.I n := by
  have h2 : (1 + 1 : Ordinal.{0}) < S.I n := by
    have hω : (1 + 1 : Ordinal.{0}) < ω := by
      rw [one_add_one_eq_two]; exact_mod_cast natCast_lt_omega0 2
    refine hω.trans_le (le_trans (omega0_le_omega 1) ?_)
    have := Low.Om_one_le_I (S := S) n
    rwa [Om_of_ne_zero one_ne_zero] at this
  have h : Om (1 + 1 : Ordinal.{0}) < Om (S.I n) := Om_lt_Om.2 h2
  rwa [S.fix n] at h

theorem mxOm2_lt_Iw : Om (1 + 1 : Ordinal.{0}) < S.Iw :=
  (mxOm2_lt_I (S := S) 0).trans_le (Ordinal.le_iSup (fun n => S.I n) 0)

/-- **`Γ_{Ω₁+1} = ψ_{Ω₂}(0)`.** -/
theorem mxGam_psi : ggGam = S.psi 0 (Om (1 + 1)) := by
  refine le_antisymm (ggGam_le (SC_psi (InR_Om_succ 1) 0) (psiS_bounds (S := S) 0 1).1) ?_
  refine psi_le_of_good (CSet.Om_mem (CSet.add_mem (CSet.one_mem _ _) (CSet.one_mem _ _))) ?_
  obtain ⟨hGs, hG1⟩ := ggGam_spec
  intro x hx
  induction hx with
  | @small x hxb => exact fun _ => hxb
  | zero => exact fun _ => hGs.1
  | inacc n => exact fun h => absurd h (not_lt.2 (mxOm2_lt_I n).le)
  | inaccW => exact fun h => absurd h (not_lt.2 mxOm2_lt_Iw.le)
  | @add x y _ _ ihx ihy =>
    intro h
    exact hGs.isPrincipal (ihx (lt_of_le_of_lt le_self_add h)) (ihy (lt_of_le_of_lt le_add_self h))
  | @phi x y _ _ ihx ihy =>
    intro h
    exact hGs.2 x (ihx (lt_of_le_of_lt (left_le_veblen x y) h)) y
      (ihy (lt_of_le_of_lt (right_le_veblen x y) h))
  | @om x _ _ =>
    intro h
    have hx2 : x < 1 + 1 := Om_lt_Om.1 h
    rcases lt_or_ge x 1 with hx1 | hx1
    · rw [Order.lt_one_iff.1 hx1, Om_zero]; exact hGs.1
    · have : x = 1 := le_antisymm (Order.lt_add_one_iff.1 hx2) hx1
      rw [this]; exact hG1
  | @coll π e _ _ _ _ _ => exact absurd (show e.1 < 0 from e.2) (not_lt.2 zero_le)

/-- The term `ψ^S_1(0)` of `Γ_{Ω₁+1}`. -/
def mxGamT : Term := psiS Bc.tOne zero

theorem mxGamT_NF : NF mxGamT := ⟨NF_tOne, trivial, trivial⟩

theorem mxGamT_free : bcFree mxGamT := ⟨tOne_ne_zero, bcFree_tOne, trivial⟩

theorem mxGamT_val (S : InaccSeq.{0}) : val S mxGamT = ggGam := by
  show S.psi (val S zero) (Om (val S Bc.tOne + 1)) = ggGam
  rw [val_tOne, mxGam_psi]; rfl

/-- **`B_n` fixes `Γ_{Ω₁+1}`.** -/
theorem mxB_gam (n : ℕ) : Bc.bcB S n ggGam = ggGam := by
  unfold Bc.bcB
  rw [← mxGamT_val S, bcNf_val S mxGamT_NF, bcSig_free mxGamT_free]

theorem mxGam_mem : ggGam ∈ ⋃ a, S.CSet a 0 :=
  Set.mem_iUnion.2 ⟨1, by
    rw [mxGam_psi]
    exact CSet.psi_mem zero_lt_one (InR_Om_succ 1)
      (CSet.Om_mem (CSet.add_mem (CSet.one_mem _ _) (CSet.one_mem _ _))) (CSet.zero_mem _ _)⟩

theorem mxGam_lt_th : ggGam < ConjT.th S := by
  rw [mxGam_psi]
  exact psi_lt_psi_of_mem (InR_Om_succ 1) (Om_pos omega0_ne_zero) (CSet.zero_mem _ _)

/-! ## The reading of `Γ_{Ω₁+1}` -/

/-- A code over `ρ` below `Γ_{Ω₁+1}` is read below every strongly critical `X > ρ`. -/
theorem mxGgTh_lt {ρ X : Ordinal.{0}} (hρ : SC ρ) (hρ1 : ρ < Om 1) (hX : SC X) (hρX : ρ < X) :
    ∀ x, GgCl ρ x → x < ggGam → ggTh ρ x < X := by
  have hXp : IsPrincipal (· + ·) X := hX.isPrincipal
  have hXo : ∀ a < X, ω ^ a < X := fun a ha => by
    have := hX.2 0 hX.1 a ha; rwa [veblen_zero_apply] at this
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx hxG
  rcases lt_trichotomy x (Om 1) with hx1 | hx1 | hx1
  · have hxρ : x < ρ := hx.lt_of_lt_Om1 hρ hx1
    rw [ggTh_small hxρ.le]; exact hxρ.trans hρX
  · subst hx1; rw [ggTh_Om1 hρ hρ1]; exact hρX
  · have hx0 : x ≠ 0 := (lt_of_le_of_lt zero_le hx1).ne'
    by_cases hE : ω ^ x = x
    · obtain ⟨hdec, hax, hbx⟩ := mwDec hE hx1 hxG
      set a := invVeblen₁ x with ha_def
      set b := invVeblen₂ x with hb_def
      obtain ⟨hga, hgb⟩ := Ph.phDec hρ.1 hx a b hdec hbx
      have hta := IH a hax hga (hax.trans hxG)
      have htb := IH b hbx hgb (hbx.trans hxG)
      rw [← hdec, Ph.phTh_phi hρ a hga b hgb]
      exact hX.2 _ hta _ htb
    · obtain ⟨a, ha⟩ : ∃ a, a = log ω x := ⟨_, rfl⟩
      have hlead : ω ^ a ≤ x := by rw [ha]; exact opow_log_le_self ω hx0
      have hxlt : x < ω ^ a * ω := by
        rw [← opow_succ, ha]; exact lt_opow_succ_log_self one_lt_omega0 x
      have hga : GgCl ρ a := by rw [ha]; exact (ggDec hρ x hx).2
      have hgl : GgCl ρ (ω ^ a) := GgCl.opow hρ.1 hga
      have hgr : GgCl ρ (x - ω ^ a) := (ggDec hρ x hx).1 _ hgl hlead
      have hdec : ω ^ a + (x - ω ^ a) = x := Ordinal.add_sub_cancel_of_le hlead
      by_cases hr : x - ω ^ a = 0
      · have hxa : ω ^ a = x := by rw [hr, add_zero] at hdec; exact hdec
        have hax : a < x := by
          rcases (right_le_opow a one_lt_omega0).lt_or_eq with h | h
          · rwa [hxa] at h
          · exfalso; apply hE; rw [← hxa]; exact congrArg (ω ^ ·) h.symm
        have hta := IH a hax hga (hax.trans hxG)
        rw [← hxa, ggTh_opow hρ hga]
        exact hXo _ hta
      · obtain ⟨r, hr'⟩ : ∃ r, r = x - ω ^ a := ⟨_, rfl⟩
        rw [← hr'] at hgr hdec hr
        have hlx : ω ^ a < x := by
          rw [← hdec]; exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 hr)
        have hrx : r < x := by
          refine lt_of_le_of_ne (by rw [← hdec]; exact le_add_self) fun e => ?_
          have h' : ω ^ a + x = x := by
            calc ω ^ a + x = ω ^ a + r := by rw [e]
              _ = x := hdec
          have := Ordinal.add_eq_right_iff_mul_omega0_le.1 h'
          exact absurd (lt_of_lt_of_le hxlt this) (lt_irrefl _)
        have htl := IH _ hlx hgl (hlx.trans hxG)
        have htr := IH r hrx hgr (hrx.trans hxG)
        rw [← hdec, ggTh_add hρ hgl r]
        exact hXp htl htr

/-- **`Θ_λ(Γ_{Ω₁+1})` is the least strongly critical ordinal above `ρ_λ`** (at a named restart). -/
theorem mxTheta_gam {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) :
    SC (cdTheta S l ggGam) ∧ upsilon l < cdTheta S l ggGam ∧
      ∀ X, SC X → upsilon l < X → cdTheta S l ggGam ≤ X := by
  obtain ⟨hρ, hρ1⟩ := mvNamed_SC hl hX
  rw [mvTheta_eq hl hX le_rfl]
  set ρ := upsilon l with hρdef
  have hOm : Om 1 < ggGam := ggGam_spec.2
  have hρζ : ρ < ggTh ρ ggGam := by
    have := ggTh_lt (y := ρ) GgCl.om hOm
    rwa [ggTh_Om1 hρ hρ1] at this
  refine ⟨⟨lt_of_le_of_lt zero_le hρζ, fun a ha b hb => ?_⟩, hρζ, fun X hXs hρX => ?_⟩
  · obtain ⟨ca, hca, hcaG, hea⟩ := ggOtp_onto (ggSet ρ) ggGam a ha
    obtain ⟨cb, hcb, hcbG, heb⟩ := ggOtp_onto (ggSet ρ) ggGam b hb
    have hea' : ggTh ρ ca = a := hea
    have heb' : ggTh ρ cb = b := heb
    have hph : GgCl ρ (veblen ca cb) := GgCl.phi hca hcb
    have hlt : veblen ca cb < ggGam := ggGam_spec.1.2 _ hcaG _ hcbG
    have := ggTh_lt hph hlt
    rwa [Ph.phTh_phi hρ ca hca cb hcb, hea', heb'] at this
  · unfold ggTh
    rw [cdOtp_eq]
    refine ciSup_le' fun c => ?_
    split_ifs with hc
    · exact Order.add_one_le_of_lt (mxGgTh_lt hρ hρ1 hXs hρX c.1 hc c.2)
    · exact zero_le

/-! ## `B_n` on `ψ_{Ω₁}(A_η + 1)` -/

/-- **`B_n(P(η)) = ψ_{Ω₁}(A')`, `B_n(ψ_{Ω₁}(A_η + 1)) = ψ_{Ω₁}(A' + 1)`**, `A'` own, at a good `η` in the window. -/
theorem mxB_psi1 {n : ℕ} {η : Ordinal.{0}} (hg : Bt.Good S η) (hlo : Bc.bcC S n ≤ Pv S η)
    (hhi : S.psi (ConjT.Aη S η + 1) (Om 1) < Bc.bcC S (n + 1)) :
    ∃ A', A' ∈ S.CSet A' (S.psi A' (Om 1)) ∧ Bc.bcB S n (Pv S η) = S.psi A' (Om 1) ∧
      Bc.bcB S n (S.psi (ConjT.Aη S η + 1) (Om 1)) = S.psi (A' + 1) (Om 1) := by
  have hP1 : Pv S η ≤ S.psi (ConjT.Aη S η + 1) (Om 1) :=
    (psi_mono (S := S) Low.InR_Om_one (le_self_add : ConjT.Aη S η ≤ ConjT.Aη S η + 1)).1
  have hAL : ConjT.Aη S η < S.Lam := (sfA_lt (hP1.trans_lt hhi)).2
  have hown := sfOwn hg hAL
  have hαA : bcAlpha S (n + 1) ≤ ConjT.Aη S η := sfArg_le (sfOwn_alpha S n) hown hlo
  have hown1 : ConjT.Aη S η + 1 ∈ S.CSet (ConjT.Aη S η + 1) (S.psi (ConjT.Aη S η + 1) (Om 1)) := by
    have h1 := (psi_mono (S := S) Low.InR_Om_one
      (le_self_add : ConjT.Aη S η ≤ ConjT.Aη S η + 1)).2 hown
    exact CSet.succ_mem h1
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Qq.qqL_lt_omega S (n + 1 + 1)
  have hx0 : Pv S η < Nc.ncL S ω := (hP1.trans_lt hhi).trans hLw
  have hx1 : S.psi (ConjT.Aη S η + 1) (Om 1) < Nc.ncL S ω := hhi.trans hLw
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
  have hvr1 : val S (bcDrop (n + 3) a1) = val S (bcDrop (n + 3) a) + 1 := by
    have e1 : bcAlpha S (n + 1) + val S (bcDrop (n + 3) a1) =
        bcAlpha S (n + 1) + (val S (bcDrop (n + 3) a) + 1) := by
      rw [← hvρ1, hva1, ← hva, hvρ, add_assoc]
    exact add_left_cancel e1
  have hNρ1 : NF (bcDrop (n + 3) a1) := NF_bcDrop _ hN1.2.1
  obtain ⟨hNadd, hvadd, -⟩ := addNF_spec (S := S) hDρ.1 NF_tOne
  have hρ1 : bcDrop (n + 3) a1 = addNF (bcDrop (n + 3) a) Bc.tOne :=
    eq_of_val_eq S hNρ1 hNadd (by rw [hvadd, val_tOne, hvr1])
  have hσ1 : val S (bcSig (bcPre (n + 1)) bcPreW (bcDrop (n + 3) a1)) =
      val S (bcSig (bcPre (n + 1)) bcPreW (bcDrop (n + 3) a)) + 1 := by
    rw [hρ1, bcSig_addNF (k := n) hDρ (bcD_free NF_tOne bcFree_tOne), bcSig_free bcFree_tOne,
      (addNF_spec (S := S) (bc_NF (k := n) hDρ) NF_tOne).2.1, val_tOne]
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

/-! ## `B_n r(λ) = r(λ')` at the first atom -/

/-- **`B_n r(λ) = r(λ')` at every long code with `e(η_λ) = Γ_{Ω₁+1}`**, given `L(ω+1) ≤ ν_C`. -/
theorem mxEQ_gam (hν : Nc.ncL S (ω + 1) ≤ nuC) {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l)
    (h1 : Bc.bcC S n < upsilon l) (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l')
    (hB : Bc.bcB S n (upsilon l) = upsilon l') (he : cdExp (cdEta S l) = ggGam) :
    Bc.bcB S n (cdR S l) = cdR S l' := by
  have hl := hR.1
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans hδr
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hX : upsilon l < Nm.Pv S (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0})) := by
    rw [← Lw.lw_L_eq S]; exact h2
  have hX' : upsilon l' < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq S, ← hB]; exact Bc.bcB_bound' S n _ h2
  -- the codes
  have hωG : (ω : Ordinal.{0}) ≤ ggGam := (Lw.lw_omega_lt_SC ggGam_spec.1).le
  have hcode : cdCode S l = ggGam := by
    show cdCodeOf S (cdEta S l) = ggGam
    rw [cdCodeOf_of_lt (he ▸ ggGam_lt_Om2 S), he]
    unfold cdOff; rw [if_neg (not_lt.2 hωG)]
  obtain ⟨η', -, hBη', hη', hexp'⟩ := mvExp_move hl.1 h1 h2 (he ▸ mxGam_lt_th) (he ▸ mxGam_mem)
  rw [he, mxB_gam] at hexp'
  have hl'eq : l' = Bt.iota S η' := Tp.tpUps_inj (hB.symm.trans hBη')
  have hcode' : cdCode S l' = ggGam := by
    rw [hl'eq]
    show cdCodeOf S (cdEta S (Bt.iota S η')) = _
    rw [hη', cdCodeOf_of_lt (hexp' ▸ ggGam_lt_Om2 S), hexp']
    unfold cdOff; rw [if_neg (not_lt.2 hωG)]
  -- the reading at `λ`: `Θ_λ(Γ_{Ω₁+1}) = ψ_{Ω₁}(A_η + 1)`
  obtain ⟨hg, -, -, hpv⟩ := cdEta_pv_spec (S := S) hl.1 hX
  set η := cdEta S l with hη_def
  have hρpv : Pv S η = upsilon l := hpv
  obtain ⟨hΘS, hρΘ, hΘle⟩ := mxTheta_gam hl hX
  have hΘeq : cdTheta S l ggGam = S.psi (ConjT.Aη S η + 1) (Om 1) := by
    have hPl : S.psi (ConjT.Aη S η) (Om 1) = upsilon l := hρpv
    refine le_antisymm (hΘle _ (SC_psi Low.InR_Om_one _) ?_) (mxPsi_succ_le hΘS (hPl ▸ hρΘ))
    have hAL : ConjT.Aη S η < S.Lam := (sfA_lt (S := S) (n := n) (hρpv ▸ h2)).2
    rw [← hPl]; exact mxPsi_succ_gt (sfOwn hg hAL)
  -- `Θ_λ(Γ_{Ω₁+1}) < δ_λ`
  have hu1 : upsilon (l + 1) < cdDelta l :=
    upsilon_normal.strictMono (by
      calc l + 1 < l + ω := (add_lt_add_iff_left l).2 one_lt_omega0
        _ < l + ω + 1 := lt_add_one _)
  have hu1SC : SC (upsilon (l + 1)) := by
    refine mvUps_SC (Order.succ_ne_bot _) (show upsilon (l + 1) < Nm.Pv S (Om ω + Nc.ncPp S * ω) by
      rw [← Lw.lw_L_eq S]; exact (hu1.trans hδr).trans hLw)
  have hρu1 : upsilon l < upsilon (l + 1) := upsilon_normal.strictMono (lt_add_one l)
  have hΘδ : cdTheta S l ggGam < cdDelta l := (hΘle _ hu1SC hρu1).trans_lt hu1
  -- `B_n(Θ_λ(Γ_{Ω₁+1})) = Θ_{λ'}(Γ_{Ω₁+1})`
  have hhi : S.psi (ConjT.Aη S η + 1) (Om 1) < Bc.bcC S (n + 1) := hΘeq ▸ hΘδ.trans hδr
  obtain ⟨A', hA', hBP, hBG⟩ := mxB_psi1 hg (hρpv ▸ h1.le) hhi
  have hρ'A : S.psi A' (Om 1) = upsilon l' := by rw [← hBP]; exact hρpv ▸ hB
  obtain ⟨hΘS', hρΘ', hΘle'⟩ := mxTheta_gam hl' hX'
  have hΘeq' : cdTheta S l' ggGam = S.psi (A' + 1) (Om 1) :=
    le_antisymm (hΘle' _ (SC_psi Low.InR_Om_one _) (hρ'A ▸ mxPsi_succ_gt hA'))
      (mxPsi_succ_le hΘS' (hρ'A ▸ hρΘ'))
  show Bc.bcB S n (cdk l (cdTheta S l (cdCode S l))) = cdk l' (cdTheta S l' (cdCode S l'))
  rw [hcode, hcode', ← mvk_move hν hl hl' h1 hδr hB hΘδ, hΘeq, hBG, hΘeq']

/-! ## The hypothesis beyond the first atom, and the road -/

/-- `MwEQtop` at the long codes with `Γ_{Ω₁+1} < e(η_λ)` (beyond the first strongly critical atom). -/
def MxEQtop (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    ggGam < cdExp (cdEta S l) → Bc.bcB S n (cdR S l) = cdR S l'

/-- **`L(ω+1) ≤ ν_C` and `MxEQtop` give `MwEQtop`.** -/
theorem mxEQtop_mw (hν : Nc.ncL S (ω + 1) ≤ nuC) (h : MxEQtop S) : MwEQtop S := by
  intro n l l' hR h1 hr hl' hB hm he
  rcases he.lt_or_eq with he | he
  · exact h n l l' hR h1 hr hl' hB hm he
  · exact mxEQ_gam hν hR h1 hr hl' hB he.symm

/-- `MwEQtop` gives `MxEQtop` (so `MxEQtop` is the weaker hypothesis). -/
theorem mxEQtop_of_mw (h : MwEQtop S) : MxEQtop S :=
  fun n l l' hR h1 hr hl' hB hm he => h n l l' hR h1 hr hl' hB hm he.le

/-- **The road with `MxLhTopG` and `L(ω+1) ≤ ν_C → MxEQtop`.** -/
theorem mxRoad2 (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (htop : Nc.ncL S (ω + 1) ≤ nuC → MxEQtop S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  mxRoad hU hO hL hV hN hlh fun hν => mxEQtop_mw hν (htop hν)

end Googology.Trans.PoR.InaccPsi.R2.Mx

import Googology.Trans.PoR.InaccPsi.R2.MvGg

/-!
# `SfLhTMove` below the first fixed point of `ε` above `υ_ξ`

[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `τ = υ_ξ`, `ε_j = veblen 1 j`, `evZ τ` the least fixed point of `ε` above `τ`
(`R2.EvZ`), `lhᵗ = lhT τ` ([W07b] Def 4.1, a repo constant).  Between `τ` and `evZ τ` the ε-numbers are
`ε_{τ+c}` (`τ` is strongly critical, so `ε_τ = τ`), and the cited computation of `lhᵗ` gives
`lh(ε_{τ+c}) = ε_{τ+c}·2 + logend(c)` for `c ≥ 2` (`R2.EvZ.lh_evAZ` for `c ≥ ω`, and `mvLh_evA` below for finite `c`,
from `CitedEv.lhT_Om1_add` with `η = c - 1`).

* `mvB_eps` (**`B_n(ε_j) = ε_{B_n j}`** for `j ∈ MvD` with `ε_j ≠ j`, and `ε_j ∈ MvD`);
* `mvB_iter`, `mvB_evZ` (**`B_n(ε^m(τ+1)) = ε^m(τ'+1)`**, so `c < evZ τ` gives `B_n c < evZ τ'`);
* `mvLg_nat`, `mvLh_evA` (**`lh(ε_{τ+c}) = ε_{τ+c}·2 + logend(c)`** for `2 ≤ c < evZ τ`);
* `mvLhT_low` (**`SfLhTMove` at every ε-number `x` with `υ_ξ < x < evZ(υ_ξ)`, `x ≠ ε_{υ_ξ+1}`**: both sides are
  `B_n(ε_{τ+c})·2 + logend(B_n c)`);
* `MvLhTop S` (a hypothesis name): `SfLhTMove` at the remaining `x`: `evZ(υ_ξ) ≤ x` or `x = ε_{υ_ξ+1}`;
  `mvLhT`: `MvLhTop` gives `SfLhTMove`;
* `mvRoad_lh`: the road with the hypotheses `MvLhTop` and `L(ω+1) ≤ ν_C → MvEQtop`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Mv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Bc

variable {S : InaccSeq.{0}}

/-! ## `B_n` on `ε` -/

/-- **`B_n(ε_j) = ε_{B_n j}`** for `j ∈ MvD` with `ε_j ≠ j`. -/
theorem mvB_eps {k : ℕ} {j : Ordinal.{0}} (hj : MvD S j) (hne : veblen 1 j ≠ j) :
    MvD S (veblen 1 j) ∧ bcB S k (veblen 1 j) = veblen 1 (bcB S k j) := by
  have hmem : veblen 1 j ∈ ⋃ b, S.CSet b 0 := by
    obtain ⟨b, hb⟩ := Set.mem_iUnion.1 hj.1
    exact Set.mem_iUnion.2 ⟨b, CSet.phi_mem (S := S) (CSet.one_mem b 0) hb⟩
  obtain ⟨hN, hv⟩ := bcNf_spec S hmem
  have hfix : ω ^ veblen 1 j = veblen 1 j := Tp.tpVeblen_fix zero_lt_one
  have hI : Indec (veblen 1 j) := by
    refine indec_iff.2 ⟨(lt_of_lt_of_le (opow_pos _ omega0_pos) hfix.le).ne', ?_⟩
    have := isPrincipal_add_omega0_opow (veblen 1 j)
    rwa [hfix] at this
  have hP : (bcNf S (veblen 1 j)).isPrin = true := isPrin_of_indec hN (by rw [hv]; exact hI)
  have hinj : ∀ y, veblen 1 y = veblen 1 j → y = j := fun y h =>
    (isNormal_veblen 1).strictMono.injective h
  have hnE : veblen 1 (veblen 1 j) ≠ veblen 1 j := fun h => hne (hinj _ h)
  generalize ht : bcNf S (veblen 1 j) = t at hN hv hP
  cases t with
  | zero => simp [isPrin, isSC] at hP
  | add _ _ => simp [isPrin, isSC] at hP
  | phi c d =>
    have hdlt : val S d < val S (phi c d) := (cmp_lt_iff S hN.2.1 hN).1 hN.2.2.2
    rcases lt_trichotomy (val S c) 1 with hc | hc | hc
    · exfalso
      have hc0 : val S c = 0 := Order.lt_one_iff.1 hc
      have hval : val S (phi c d) = ω ^ val S d := by simp only [val, hc0, veblen_zero]
      have h1 : ω ^ val S d = veblen 1 j := hval.symm.trans hv
      have h2 : ω ^ (ω ^ val S d) = ω ^ val S d := by rw [h1]; exact hfix
      have h3 : ω ^ val S d = val S d := (opow_right_inj one_lt_omega0).1 h2
      rw [hval, h3] at hdlt
      exact lt_irrefl _ hdlt
    · have hcT : c = tOne := eq_of_val_eq S hN.1 NF_tOne (by rw [hc]; simp [val, tOne])
      subst hcT
      have hvd : val S d = j := hinj _ (by rw [← hv]; simp [val, tOne])
      have hnd : bcNf S j = d := by rw [← hvd]; exact bcNf_val S hN.2.1
      have hAd : bcArgsLt S (bcAlphaW S) d := by rw [← hnd]; exact hj.2.2
      have hD : bcD S (phi tOne d) := ⟨hN, bcArgsLt_of_free bcFree_tOne, hAd⟩
      refine ⟨⟨hmem, by rw [ht]; exact hD⟩, ?_⟩
      unfold bcB
      rw [ht, hnd, bcSig_phi, bcSig_free bcFree_tOne]
      simp [val, tOne]
    · exfalso; apply hnE
      rw [← hv]; simp only [val]; exact veblen_veblen_of_lt hc _
  | _ =>
    exfalso; apply hnE
    have hsc := SC_val S hN (by simpa [isPrin] using hP)
    rw [hv] at hsc
    exact hsc.veblen_right (Gg.gg_one_lt_of_SC hsc)

/-! ## The iterates of `ε` up to `evZ` -/

theorem mvIter_lt (τ : Ordinal.{0}) :
    ∀ m : ℕ, Ordinal.epsilon^[m] (τ + 1) < evZ τ
  | 0 => (ev_isSuccLimit_of_inE (evZ_E τ)).add_one_lt (lt_evZ τ)
  | m + 1 => by
    rw [Function.iterate_succ_apply']
    have h := (isNormal_veblen 1).strictMono (mvIter_lt τ m)
    rwa [show veblen 1 (evZ τ) = evZ τ from epsilon_evZ τ] at h

theorem mvIter_ge (τ : Ordinal.{0}) : ∀ m : ℕ, τ + 1 ≤ Ordinal.epsilon^[m] (τ + 1)
  | 0 => le_rfl
  | m + 1 => by
    rw [Function.iterate_succ_apply']
    exact (mvIter_ge τ m).trans (right_le_veblen 1 _)

/-- **`B_n(ε^m(τ+1)) = ε^m(τ'+1)`** when `B_n τ = τ'` and `evZ τ < L(ω)`. -/
theorem mvB_iter {k : ℕ} {τ τ' : Ordinal.{0}} (hB : bcB S k τ = τ') (h1 : (1 : Ordinal.{0}) < bcC S k)
    (hZL : evZ τ < Nc.ncL S ω) :
    ∀ m : ℕ, bcB S k (Ordinal.epsilon^[m] (τ + 1)) = Ordinal.epsilon^[m] (τ' + 1)
  | 0 => by
    have hτL : τ < Nc.ncL S ω := (lt_evZ τ).trans hZL
    have h1L : (1 : Ordinal.{0}) < Nc.ncL S ω := h1.trans (bcC_lt S k)
    simp only [Function.iterate_zero, id]
    rw [bcB_add hτL h1L, hB, bcB_fix h1]
  | m + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    set y := Ordinal.epsilon^[m] (τ + 1) with hy
    have hyZ : y < evZ τ := mvIter_lt τ m
    have hτy : τ < y := lt_of_lt_of_le (lt_add_one τ) (mvIter_ge τ m)
    have hne : veblen 1 y ≠ y := fun h => absurd (evZ_le hτy h) (not_le.2 hyZ)
    rw [(mvB_eps (k := k) (mvD_of_lt (hyZ.trans hZL)) hne).2, mvB_iter hB h1 hZL m]

/-- **`c < evZ τ` gives `B_n c < evZ τ'`.** -/
theorem mvB_evZ {k : ℕ} {τ τ' c : Ordinal.{0}} (hB : bcB S k τ = τ') (h1 : (1 : Ordinal.{0}) < bcC S k)
    (hZL : evZ τ < Nc.ncL S ω) (hc : c < evZ τ) : bcB S k c < evZ τ' := by
  obtain ⟨m, hm⟩ := (lt_nfp_iff (f := Ordinal.epsilon)).1 (show c < nfp Ordinal.epsilon (τ + 1) from hc)
  have hmL : Ordinal.epsilon^[m] (τ + 1) < Nc.ncL S ω := (mvIter_lt τ m).trans hZL
  have := (bcB_lt_iff (k := k) (hm.trans hmL) hmL).2 hm
  rw [mvB_iter hB h1 hZL m] at this
  exact this.trans_le (iterate_le_nfp _ _ _)

/-! ## The reach of `ε_{τ+c}` -/

theorem mvLg_nat (m : ℕ) (hm : m ≠ 0) : lg (m : Ordinal.{0}) = 0 := by
  have e : (m : Ordinal.{0}) = ((m - 1 : ℕ) : Ordinal.{0}) + ω ^ (0 : Ordinal.{0}) := by
    rw [opow_zero, ← Nat.cast_succ]; congr 1; omega
  rw [e]
  exact Tp.tpLg_add (by rw [opow_zero]; exact one_dvd _)

/-- **`lh(ε_{τ+c}) = ε_{τ+c}·2 + logend(c)`** for `2 ≤ c < evZ τ` (`ω ≤ τ`). -/
theorem mvLh_evA {τ c : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hωτ : (ω : Ordinal.{0}) ≤ τ)
    (hc0 : c ≠ 0) (hc1 : c ≠ 1) (hcZ : c < evZ τ) :
    IsLh1 (evA τ c) (evA τ c * 2 + lg c) := by
  by_cases hωc : (ω : Ordinal.{0}) ≤ c
  · exact lh_evAZ hτ hτ1 hωc hcZ
  · obtain ⟨m, rfl⟩ := lt_omega0.1 (not_le.1 hωc)
    have hm0 : m ≠ 0 := fun h => hc0 (by simp [h])
    have hm1 : m ≠ 1 := fun h => hc1 (by simp [h])
    obtain ⟨η, hη⟩ : ∃ η : Ordinal.{0}, η = ((m - 1 : ℕ) : Ordinal.{0}) := ⟨_, rfl⟩
    have h1η : 1 + η = (m : Ordinal.{0}) := by
      rw [hη, ← Nat.cast_one, ← Nat.cast_add]; congr 1; omega
    have hη0 : η ≠ 0 := by
      rw [hη]; exact_mod_cast (show m - 1 ≠ 0 by omega)
    have hηω : η < ω := by rw [hη]; exact natCast_lt_omega0 _
    have hηZ : η < evZ τ := hηω.trans_le (hωτ.trans (lt_evZ τ).le)
    obtain ⟨hcT, hc1'⟩ := mem_T_of_lt_evZ hτ hτ1 hηZ
    have hv : vt τ (Om1 + η) = evA τ m := by rw [vt_Om1_add_evZ hτ hτ1 hηZ, h1η]
    obtain ⟨hγT, -⟩ := Om1_add_T hτ hτ1 hcT hc1'
    obtain ⟨hvT, -, hv1, hvP, -⟩ := vt_memTwo hτ hτ1 hγT (Om1_add_lt_OmTwo hc1')
    have hτv' : τ < vt τ (Om1 + η) :=
      ((vt_E_iff hτ hτ1 hγT (Om1_add_lt_OmTwo hc1')).2 le_self_add).1
    have hlim : ∃ σ, σ < η ∧ η < vt τ (Om1 + σ) := by
      refine ⟨0, pos_iff_ne_zero.2 hη0, ?_⟩
      rw [vt_Om1_add_evZ hτ hτ1 (lt_of_le_of_lt zero_le hηZ), add_zero]
      exact (hηω.trans_le hωτ).trans (lt_evA hτ one_ne_zero)
    have := lh_eq_lhT (Or.inr hτ) hτ1 hvT hτv' hv1 hvP
    rw [lhT_Om1_add hτ hτ1 hcT hc1' hη0 hlim, hv] at this
    have hlgη : lg η = 0 := by rw [hη]; exact mvLg_nat _ (by omega)
    rwa [hlgη, ← mvLg_nat m hm0] at this

/-! ## `SfLhTMove` below `evZ(υ_ξ)` -/

theorem mvMul_two (a : Ordinal.{0}) : a * 2 = a + a := by
  rw [show (2 : Ordinal.{0}) = 1 + 1 from one_add_one_eq_two.symm, mul_add, mul_one]

theorem mvEps_fix_of_SC {τ : Ordinal.{0}} (h : SC τ) : Ordinal.epsilon τ = τ :=
  h.veblen_right (Gg.gg_one_lt_of_SC h)

theorem mvEvIx_of_SC {τ : Ordinal.{0}} (h : SC τ) : evIx τ = τ := by
  have := evIx_epsilon τ
  rwa [mvEps_fix_of_SC h] at this

/-- A named `υ`-point is strongly critical. -/
theorem mvUps_SC {ξ ηx : Ordinal.{0}} (hξ : ξ ≠ 0) (hX : upsilon ξ < Nm.Pv S ηx) : SC (upsilon ξ) := by
  have hpv := Cd.cdEta_pv (S := S) hξ hX
  rw [← hpv]; exact Nm.Pv_SC S _

/-- **`SfLhTMove` at the ε-numbers `x` with `υ_ξ < x < evZ(υ_ξ)` and `x ≠ ε_{υ_ξ+1}`.** -/
theorem mvLhT_low {n : ℕ} {ξ ξ' x : Ordinal.{0}} (hc : Bc.bcC S n ≤ upsilon ξ) (hτx : upsilon ξ < x)
    (hx2 : x < upsilon (ξ + 1)) (hξ1lt : upsilon (ξ + 1) < Bc.bcC S (n + 1)) (hE : InE x)
    (hBξ : Bc.bcB S n (upsilon ξ) = upsilon ξ')
    (hBξ1 : Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1))
    (hZ : x < evZ (upsilon ξ)) (hx1 : x ≠ Ordinal.epsilon (upsilon ξ + 1)) :
    Bc.bcB S n (lhT (upsilon ξ) x) = lhT (upsilon ξ') (Bc.bcB S n x) := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Qq.qqL_lt_omega S (n + 1 + 1)
  have hxL : x < Nc.ncL S ω := hx2.trans (hξ1lt.trans hLw)
  have hτL : upsilon ξ < Nc.ncL S ω := hτx.trans hxL
  have hτ1L : upsilon (ξ + 1) < Nc.ncL S ω := hξ1lt.trans hLw
  have hωC : (ω : Ordinal.{0}) < Bc.bcC S n := Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)
  have h1C : (1 : Ordinal.{0}) < Bc.bcC S n := one_lt_omega0.trans hωC
  have hOm : Nc.ncL S ω < Om1 := by rw [Br.Om1_eq]; exact InaccSeq.psi_lt Low.InR_Om_one _
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    rw [upsilon_zero] at hc
    exact absurd (lt_of_lt_of_le (zero_lt_one.trans h1C) hc) (lt_irrefl _)
  -- the image base
  have hLω : Nc.ncL S ω ≤ Bc.bcB S n (upsilon ξ) := by
    rw [← Bc.bcB_base (S := S) n]
    rcases eq_or_lt_of_le hc with e | hlt
    · rw [← e]; exact le_rfl
    · exact ((Bc.bcB_lt_iff (Qq.qqL_lt_omega S (n + 1)) hτL).2 hlt).le
  have hξ'0 : ξ' ≠ 0 := by
    rintro rfl
    rw [hBξ, upsilon_zero] at hLω
    exact absurd (lt_of_lt_of_le (Lw.lw_L_SC S ω).1 hLω) (lt_irrefl _)
  have hτ'L1 : upsilon ξ' < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq S, ← hBξ]; exact Bc.bcB_bound' S n _ (hτx.trans (hx2.trans hξ1lt))
  have hτSC : SC (upsilon ξ) := mvUps_SC hξ0 (show upsilon ξ < Nm.Pv S (Om ω + Nc.ncPp S * ω) by
    rw [← Lw.lw_L_eq S]; exact hτL)
  have hτ'SC : SC (upsilon ξ') := mvUps_SC hξ'0 hτ'L1
  have hτE : InE (upsilon ξ) := Low.opow_eq_self_of_SC hτSC
  have hτ'E : InE (upsilon ξ') := Low.opow_eq_self_of_SC hτ'SC
  have hτ1 : upsilon ξ < Om1 := hτL.trans hOm
  have hτ'1 : upsilon ξ' < Om1 := by rw [Br.Om1_eq]; exact hτ'L1.trans (Nm.Pv_lt_Om1 S _)
  have hωτ : (ω : Ordinal.{0}) ≤ upsilon ξ := (hωC.trans_le hc).le
  have hωτ' : (ω : Ordinal.{0}) ≤ upsilon ξ' := by
    rw [← hBξ]; exact ((hωC.trans (Bc.bcC_lt S n)).trans_le hLω).le
  -- the index `c` of `x = ε_{τ+c}`
  have hi := epsilon_evIx hE
  have hτfix : veblen 1 (upsilon ξ) = upsilon ξ := mvEps_fix_of_SC hτSC
  have hτi : upsilon ξ < evIx x := by
    by_contra h
    have h' := (isNormal_veblen 1).strictMono.monotone (not_lt.1 h)
    rw [show veblen 1 (evIx x) = x from hi, hτfix] at h'
    exact absurd hτx (not_lt.2 h')
  obtain ⟨c, hic⟩ : ∃ c, upsilon ξ + c = evIx x := ⟨_, Ordinal.add_sub_cancel_of_le hτi.le⟩
  have hxeq : x = veblen 1 (upsilon ξ + c) := by rw [hic]; exact hi.symm
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [add_zero, hτfix] at hxeq
    rw [hxeq] at hτx
    exact lt_irrefl _ hτx
  have hc1 : c ≠ 1 := by rintro rfl; exact hx1 hxeq
  have hcZ : c < evZ (upsilon ξ) :=
    lt_of_le_of_lt (le_add_self.trans ((right_le_veblen 1 _).trans hxeq.symm.le)) hZ
  have hevA : x = evA (upsilon ξ) c := by unfold evA; rw [mvEvIx_of_SC hτSC]; exact hxeq
  have hZL : evZ (upsilon ξ) < Nc.ncL S ω := by
    have hle : evZ (upsilon ξ) ≤ Bc.bcC S (n + 1) :=
      evZ_le (hτx.trans (hx2.trans hξ1lt)) (mvEps_fix_of_SC (Lw.lw_L_SC S _))
    exact hle.trans_lt hLw
  have hcL : c < Nc.ncL S ω := hcZ.trans hZL
  have htcL : upsilon ξ + c < Nc.ncL S ω :=
    lt_of_le_of_lt ((right_le_veblen 1 _).trans hxeq.symm.le) hxL
  -- `B_n x = ε_{τ' + B_n c}`
  have hnf : veblen 1 (upsilon ξ + c) ≠ upsilon ξ + c := by
    intro h
    have hxfix : Ordinal.epsilon x = x := by
      show veblen 1 x = x
      rw [hxeq, h, h]
    exact absurd (evZ_le hτx hxfix) (not_le.2 hZ)
  have hBx : Bc.bcB S n x = evA (upsilon ξ') (Bc.bcB S n c) := by
    rw [hxeq, (mvB_eps (k := n) (mvD_of_lt htcL) hnf).2, Bc.bcB_add hτL hcL, hBξ]
    unfold evA; rw [mvEvIx_of_SC hτ'SC]
  -- the image index `B_n c`
  have hBc01 : Bc.bcB S n c ≠ 0 ∧ Bc.bcB S n c ≠ 1 := by
    rcases lt_or_ge c ω with hcw | hcw
    · rw [Bc.bcB_fix (hcw.trans hωC)]; exact ⟨hc0, hc1⟩
    · have h := Tp.tpB_le (n := n) hcL hcw
      rw [Bc.bcB_fix hωC] at h
      exact ⟨(lt_of_lt_of_le omega0_pos h).ne', (lt_of_lt_of_le one_lt_omega0 h).ne'⟩
  have hBcZ : Bc.bcB S n c < evZ (upsilon ξ') := mvB_evZ hBξ h1C hZL hcZ
  -- the two reaches
  have hlhx : IsLh1 x (x * 2 + lg c) := by
    rw [hevA]; exact mvLh_evA hτE hτ1 hωτ hc0 hc1 hcZ
  have hlhBx : IsLh1 (Bc.bcB S n x) (Bc.bcB S n x * 2 + lg (Bc.bcB S n c)) := by
    rw [hBx]; exact mvLh_evA hτ'E hτ'1 hωτ' hBc01.1 hBc01.2 hBcZ
  have hU : ¬ UpsPt x := by
    intro hu
    obtain ⟨j, -, hj⟩ := upsPt_iff_upsilon.1 hu
    rw [hj] at hτx hx2
    exact absurd (Order.lt_add_one_iff.1 (Tp.tpUps_lt_iff.1 hx2)) (not_le.2 (Tp.tpUps_lt_iff.1 hτx))
  have hlo' : upsilon ξ' < Bc.bcB S n x := by
    rw [← hBξ]; exact (Bc.bcB_lt_iff hτL hxL).2 hτx
  have hhi' : Bc.bcB S n x < upsilon (ξ' + 1) := by
    rw [← hBξ1]; exact (Bc.bcB_lt_iff hxL hτ1L).2 hx2
  have hU' : ¬ UpsPt (Bc.bcB S n x) := by
    intro hu
    obtain ⟨j, -, hj⟩ := upsPt_iff_upsilon.1 hu
    rw [hj] at hlo' hhi'
    exact absurd (Order.lt_add_one_iff.1 (Tp.tpUps_lt_iff.1 hhi')) (not_le.2 (Tp.tpUps_lt_iff.1 hlo'))
  have hE' : InE (Bc.bcB S n x) := by rw [hBx]; exact evA_E _ _
  have hBx1 : Bc.bcB S n x < Om1 := by
    rw [Br.Om1_eq]
    exact (Bc.bcB_bound n x (hx2.trans hξ1lt)).trans (InaccSeq.psi_lt Low.InR_Om_one _)
  obtain ⟨hlh, -, -⟩ := Lh.lhEps (hxL.trans hOm) hτx.le hx2 hE hU
  rw [if_neg hξ0] at hlh
  obtain ⟨hlh', -, -⟩ := Lh.lhEps hBx1 hlo'.le hhi' hE' hU'
  rw [if_neg hξ'0] at hlh'
  rw [Lh.lhUnique hlh hlhx, Lh.lhUnique hlh' hlhBx]
  have hlgc : lg c < Nc.ncL S ω := (lg_le hc0).trans_lt hcL
  have hx2L : x * 2 < Nc.ncL S ω := by rw [mvMul_two]; exact ncL_add_lt hxL hxL
  rw [Bc.bcB_add hx2L hlgc, mvMul_two, Bc.bcB_add hxL hxL, Tp.tpLgB hc0 hcL, mvMul_two]

/-- `SfLhTMove` at the ε-numbers `x` with `evZ(υ_ξ) ≤ x` or `x = ε_{υ_ξ+1}`. -/
def MvLhTop (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ ξ ξ' x : Ordinal.{0}, Bc.bcC S n ≤ upsilon ξ → upsilon ξ < x → x < upsilon (ξ + 1) →
    upsilon (ξ + 1) < Bc.bcC S (n + 1) → InE x → Bc.bcB S n (upsilon ξ) = upsilon ξ' →
    Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1) →
    (evZ (upsilon ξ) ≤ x ∨ x = Ordinal.epsilon (upsilon ξ + 1)) →
    Bc.bcB S n (lhT (upsilon ξ) x) = lhT (upsilon ξ') (Bc.bcB S n x)

/-- **`MvLhTop` gives `SfLhTMove`.** -/
theorem mvLhT (h : MvLhTop S) : Sf.SfLhTMove S := by
  intro n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1
  by_cases hlo : x < evZ (upsilon ξ) ∧ x ≠ Ordinal.epsilon (upsilon ξ + 1)
  · exact mvLhT_low hc hτx hx2 hξ1lt hE hBξ hBξ1 hlo.1 hlo.2
  · refine h n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 ?_
    rcases not_and_or.1 hlo with h1 | h1
    · exact Or.inl (not_lt.1 h1)
    · exact Or.inr (not_not.1 h1)

/-- **The road with `MvLhTop` and `L(ω+1) ≤ ν_C → MvEQtop`.** -/
theorem mvRoad_lh (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MvLhTop S) (htop : Nc.ncL S (ω + 1) ≤ nuC → MvEQtop S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  mvRoad_top hU hO hL hV hN (mvLhT hlh) htop

end Googology.Trans.PoR.InaccPsi.R2.Mv

import Googology.Trans.PoR.InaccPsi.R2.YtMove

/-!
# Every offset below `W^{Ω₂}` above a base `a` with `ψ_{Ω₃}(0) ∣ a`: readings and moves

`W^e = Le.leWe e = ω^{Ω₂·e}`, `G₃ = ψ_{Ω₃}(0)`, `EL^a_0 = Ω₁`, `EL^a_{j+1} = ψ₂(a + W^{EL^a_j})` (`ytEL`),
`F^a_W = ψ₂(a + W^{Ω₂})` (`ytFW`).  This is `Le.leEL` / `leFWW_gt` / `leBaseE_zero` / `leTh_FWW` / `leAtMove_FWW`
(base `0`, image `A + 1`) at a base `a` with `G₃ ∣ a` and image `Â = A + D` (a `Yj.YjBase`).

* `ytEL_sup` (**`F^a_W = sup_j EL^a_j`**), `ytFW_gt` (**`x < ψ₂(a + W^x)` for every `x < F^a_W`**), `ytFW_ge`;
* `ytBaseE` (**`a` is a base of every exponent `e < F^a_W`** in the sense of `Le.LeBaseE`);
* `ytRep` (**every atom `ψ₂(a) ≤ t < F^a_W` is `ψ₂(a + c)` with `(e, c, v)` own over `a`** (`Le.LeOwnH`), `e < F^a_W`),
  `ytRead` (its reading `ψ₁(Â + v)`, by `Le.leOwnRead`);
* `ytLeMove` (**EVERY ATOM `ψ₂(a) ≤ s < F^a_W` MOVES** at a window, given `Yj.YjBase λ λ' A' a D`, `G₃ ∣ a`,
  `G₃ ∣ B_n a` and the moves of the codes below `s`);
* `ytTopMoveW` (**EVERY ATOM `ψ₂(t) ≤ s < ψ₂(t + W^{Ω₂})` ABOVE EVERY TOP ATOM `t = β + W^{Ω_{k+3}+e}` MOVES** under the
  premise of WallBelow at `s`).

No new axiom.  New definitions: `ytEL`, `ytFW` (ordinal terms).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yt

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Rx
  Googology.Trans.PoR.InaccPsi.R2.Yj

variable {S : InaccSeq.{0}}

/-- `EL^a_0 = Ω₁`, `EL^a_{j+1} = ψ₂(a + W^{EL^a_j})`. -/
noncomputable def ytEL (S : InaccSeq.{0}) (a : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => Om 1
  | j + 1 => S.psi (a + leWe (ytEL S a j)) (Om (1 + 1))

/-- `F^a_W = ψ₂(a + W^{Ω₂})`. -/
noncomputable def ytFW (S : InaccSeq.{0}) (a : Ordinal.{0}) : Ordinal.{0} :=
  S.psi (a + leWe (Om (1 + 1))) (Om (1 + 1))

theorem ytFW_SC (a : Ordinal.{0}) : SC (ytFW S a) := SC_psi (InR_Om_succ 1) _
theorem ytFW_lt_Om2 (a : Ordinal.{0}) : ytFW S a < Om (1 + 1) := psi_lt (InR_Om_succ 1) _

theorem ytEL_lt_Om2 (a : Ordinal.{0}) : ∀ j, ytEL S a j < Om (1 + 1)
  | 0 => gg_Om1_lt_Om2
  | _ + 1 => psi_lt (InR_Om_succ 1) _

theorem ytEL_SC (a : Ordinal.{0}) : ∀ j, SC (ytEL S a j)
  | 0 => Ph.ph_SC_Om1
  | _ + 1 => SC_psi (InR_Om_succ 1) _

/-! ## `G₃ = ψ_{Ω₃}(0)` -/

theorem ytG3_SC : SC (S.psi 0 (Om (1 + 1 + 1))) := SC_psi (InR_Om_succ (1 + 1)) 0
theorem ytOm2_lt_G3 : Om (1 + 1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1 + 1)) := (psiS_bounds (S := S) 0 (1 + 1)).1
theorem ytWW_lt_G3 : leWe (Om (1 + 1 : Ordinal.{0})) < S.psi 0 (Om (1 + 1 + 1)) :=
  (leWe_lt_SC ytG3_SC ytOm2_lt_G3 ytOm2_lt_G3).1

/-- `W^e ∣ G₃` for `e < Ω₂`... in fact for every `e ≤ Ω₂`. -/
theorem ytWe_dvd_G3 {e : Ordinal.{0}} (he : e ≤ Om (1 + 1)) : leWe e ∣ S.psi 0 (Om (1 + 1 + 1)) := by
  unfold leWe
  conv_rhs => rw [← gg_SC_eps (ytG3_SC (S := S))]
  refine opow_dvd_opow ω ?_
  exact ((mul_le_mul_right he _).trans_lt (ldMul_lt_SC ytG3_SC ytOm2_lt_G3 ytOm2_lt_G3)).le

theorem ytOm3_le_X (k : ℕ) : Om (1 + 1 + 1 : Ordinal.{0}) ≤ Om ((k : Ordinal.{0}) + 1 + 1 + 1) :=
  Om_le_Om.2 (add_le_add_left (add_le_add_left (le_add_self : (1 : Ordinal.{0}) ≤ (k : Ordinal.{0}) + 1) 1) 1)

/-- `G₃ ∣ W^{Ω_{k+3}+e}`. -/
theorem ytG3_dvd_We (k : ℕ) (e : Ordinal.{0}) :
    S.psi 0 (Om (1 + 1 + 1)) ∣ leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) := by
  unfold leWe
  conv_lhs => rw [← gg_SC_eps (ytG3_SC (S := S))]
  refine opow_dvd_opow ω ?_
  have h1 : S.psi 0 (Om (1 + 1 + 1 : Ordinal.{0})) < Om (1 + 1 + 1) := psi_lt (InR_Om_succ (1 + 1)) 0
  exact (h1.le.trans (ytOm3_le_X k)).trans (le_self_add.trans (Ordinal.le_mul_right _ ldOm2_SC.1))

section Lay

variable {a : Ordinal.{0}}
  (hown : ∀ d, d ≤ Om (1 + 1) → a ∈ S.CSet (a + d) (S.psi (a + d) (Om (1 + 1))))

include hown

theorem ytEL_lt_succ : ∀ j, ytEL S a j < ytEL S a (j + 1)
  | 0 => (psiS_bounds (S := S) _ 1).1
  | j + 1 => by
    have IH := ytEL_lt_succ j
    have hle : ytEL S a (j + 1) ≤ ytEL S a (j + 2) :=
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left a).2 (leWe_mono IH.le))).1
    exact psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left a).2 (leWe_lt IH))
      (CSet.add_mem (ytOwnAll hown _) (leWe_mem (CSet.of_lt (IH.trans_le hle))))

theorem ytEL_mono {j j' : ℕ} (h : j ≤ j') : ytEL S a j ≤ ytEL S a j' :=
  (strictMono_nat_of_lt_succ (fun i => ytEL_lt_succ hown i)).monotone h

omit hown in
theorem ytEL_gt : ∀ j x, x < ytEL S a j → x < S.psi (a + leWe x) (Om (1 + 1))
  | 0, x, h => h.trans (psiS_bounds (S := S) _ 1).1
  | j + 1, x, h => by
    rcases lt_or_ge x (ytEL S a j) with h' | h'
    · exact ytEL_gt j x h'
    · exact h.trans_le (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left a).2 (leWe_mono h'))).1

omit hown in
theorem ytEL_le_top : ∀ j, ytEL S a j ≤ ytFW S a
  | 0 => (psiS_bounds (S := S) _ 1).1.le
  | j + 1 => (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left a).2 (leWe_mono (ytEL_lt_Om2 a j).le))).1

/-- **`F^a_W = sup_j EL^a_j`** (for `G₃ ∣ a`). -/
theorem ytEL_sup (hG3 : S.psi 0 (Om (1 + 1 + 1)) ∣ a) {x : Ordinal.{0}} (hx : x < ytFW S a) :
    ∃ j, x < ytEL S a j := by
  have hbdd : BddAbove (Set.range (ytEL S a)) := Ordinal.bddAbove_of_small
  have hlt : ∀ y, y < ⨆ j, ytEL S a j ↔ ∃ j, y < ytEL S a j := fun y => lt_ciSup_iff hbdd
  have hKQ : ∀ j, ytEL S a j < ⨆ j, ytEL S a j := fun j => (hlt _).2 ⟨j + 1, ytEL_lt_succ hown j⟩
  have hΩQ : Om (1 : Ordinal.{0}) < ⨆ j, ytEL S a j := hKQ 0
  have hQSC : SC (⨆ j, ytEL S a j) := by
    refine ⟨(Om_pos one_ne_zero).trans hΩQ, fun x hx y hy => ?_⟩
    obtain ⟨i, hi⟩ := (hlt _).1 hx
    obtain ⟨j, hj⟩ := (hlt _).1 hy
    have hi' := hi.trans_le (ytEL_mono hown (le_max_left i j))
    have hj' := hj.trans_le (ytEL_mono hown (le_max_right i j))
    exact ((ytEL_SC a (max i j)).2 _ hi' _ hj').trans (hKQ _)
  set Q := ⨆ j, ytEL S a j with hQ
  obtain ⟨r, hr⟩ := hG3
  have hFQ : ytFW S a ≤ Q := by
    refine lePsi2_le hQSC hΩQ fun x hx hc => ?_
    rcases lt_or_ge x a with hxa | hxa
    · exact ((psi_mono (S := S) (InR_Om_succ 1) (hxa.le.trans le_self_add)).1).trans_lt (hKQ 1)
    obtain ⟨x', rfl⟩ := exists_add_of_le hxa
    have hx' : x' < leWe (Om (1 + 1)) := (add_lt_add_iff_left a).1 hx
    have hmod : (a + x') % S.psi 0 (Om (1 + 1 + 1)) = x' := by
      rw [hr, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt (hx'.trans ytWW_lt_G3)]
    rw [hmod] at hc
    rcases eq_or_ne x' 0 with rfl | hx0
    · exact ((psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left a).2 zero_le)).1).trans_lt (hKQ 1)
    obtain ⟨-, hlog⟩ := leClDec hQSC ldOm2_SC x' hc
    have hla : log ω x' < Om (1 + 1) * Om (1 + 1) :=
      (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hx0).trans_lt hx')
    have hb := leCl_boundK hQSC ldOm2_SC _ hlog hla
    have hq : log ω x' / Om (1 + 1) < Q := (Ordinal.lt_mul_iff_div_lt ldOm2_SC.1.ne').1 hb
    obtain ⟨j, hj⟩ := (hlt _).1 hq
    have h1 : log ω x' + 1 ≤ Om (1 + 1) * ytEL S a j := by
      refine Order.add_one_le_of_lt ?_
      calc log ω x' < Om (1 + 1) * (log ω x' / Om (1 + 1)) + Om (1 + 1) :=
            Ordinal.lt_mul_div_add _ ldOm2_SC.1.ne'
        _ = Om (1 + 1) * (log ω x' / Om (1 + 1) + 1) := (mul_add_one _ _).symm
        _ ≤ Om (1 + 1) * ytEL S a j := mul_le_mul_right (Order.add_one_le_of_lt hj) _
    have hxW : x' < leWe (ytEL S a j) := by
      unfold leWe
      calc x' < ω ^ (log ω x' + 1) := by
            rw [← Order.succ_eq_add_one]; exact lt_opow_succ_log_self one_lt_omega0 x'
        _ ≤ ω ^ (Om (1 + 1) * ytEL S a j) := opow_le_opow_right omega0_pos h1
    have := hKQ (j + 1)
    exact ((psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left a).2 hxW.le)).1).trans_lt this
  exact (hlt x).1 (hx.trans_le hFQ)

/-- `ψ₂(a + W^x) ≥ F^a_W` for `x ≥ F^a_W`. -/
theorem ytFW_ge (hG3 : S.psi 0 (Om (1 + 1 + 1)) ∣ a) {x : Ordinal.{0}} (hx : ytFW S a ≤ x) :
    ytFW S a ≤ S.psi (a + leWe x) (Om (1 + 1)) := by
  by_contra h
  push Not at h
  obtain ⟨j, hj⟩ := ytEL_sup hown hG3 h
  have h1 : ytEL S a (j + 1) ≤ S.psi (a + leWe x) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left a).2 (leWe_mono ((ytEL_le_top j).trans hx)))).1
  exact absurd (hj.trans_le ((ytEL_lt_succ hown j).le.trans h1)) (lt_irrefl _)

/-- **Every `x < F^a_W` is an own exponent at `a`.** -/
theorem ytFW_gt (hG3 : S.psi 0 (Om (1 + 1 + 1)) ∣ a) {x : Ordinal.{0}} (hx : x < ytFW S a) :
    x < S.psi (a + leWe x) (Om (1 + 1)) := by
  obtain ⟨j, hj⟩ := ytEL_sup hown hG3 hx
  exact ytEL_gt j x hj

/-- **`a` is a base of every exponent `e < F^a_W`.** -/
theorem ytBaseE {l : Ordinal.{0}} (hG3 : S.psi 0 (Om (1 + 1 + 1)) ∣ a) (haH : a ∈ cdHull S l)
    (haA : a + leWe (Om (1 + 1)) < ConjT.Aη S (cdEta S l)) {e : Ordinal.{0}} (he : e < ytFW S a) :
    LeBaseE S l e a := by
  have heW : e < Om (1 + 1) := he.trans (ytFW_lt_Om2 a)
  refine ⟨(ytWe_dvd_G3 heW.le).trans hG3, haH, lt_of_le_of_lt ((add_le_add_iff_left a).2 (leWe_mono heW.le)) haA,
    fun d _ => ytOwnAll hown d, fun e' _ h' => ytFW_gt hown hG3 (h'.trans_lt he)⟩

end Lay

/-! ## The atoms in `[ψ₂(a), F^a_W)` -/

section Atoms

variable {l ηx a : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hown : ∀ d, d ≤ Om (1 + 1) → a ∈ S.CSet (a + d) (S.psi (a + d) (Om (1 + 1))))
  (hG3 : S.psi 0 (Om (1 + 1 + 1)) ∣ a) (haH : a ∈ cdHull S l)
  (haA : a + leWe (Om (1 + 1)) < ConjT.Aη S (cdEta S l))

include hl hX hown hG3 haH haA

/-- **Every atom `ψ₂(a) ≤ t < F^a_W` is `ψ₂(a + c)` with `(e, c, v)` own over `a`, `e < F^a_W`.** -/
theorem ytRep {t : Ordinal.{0}} (ht : t ∈ ldAtR S l) (hta : S.psi a (Om (1 + 1)) ≤ t) (htF : t < ytFW S a) :
    ∃ e c v, e < ytFW S a ∧ LeOwnH S l e a c v ∧ t = S.psi (a + c) (Om (1 + 1)) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hF0 : (0 : Ordinal.{0}) < ytFW S a := (Om_pos one_ne_zero).trans (psiS_bounds (S := S) _ 1).1
  have hz : t = S.psi a (Om (1 + 1)) → ∃ e c v, e < ytFW S a ∧ LeOwnH S l e a c v ∧
      t = S.psi (a + c) (Om (1 + 1)) := fun h => ⟨0, 0, 0, hF0, LeOwnH.zero, by rw [add_zero]; exact h⟩
  obtain ⟨x, hxH, hxA, rfl⟩ := ht
  rcases lt_or_ge x a with hxa | hxa
  · exact hz (le_antisymm (psi_mono (S := S) (InR_Om_succ 1) hxa.le).1 hta)
  obtain ⟨x', rfl⟩ := exists_add_of_le hxa
  rcases eq_or_ne x' 0 with rfl | hx0
  · exact hz (by rw [add_zero])
  have hx'W : x' < leWe (Om (1 + 1)) := by
    by_contra h
    push Not at h
    exact absurd htF (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left a).2 h)).1)
  obtain ⟨r, hr⟩ := hG3
  have hx'H : x' ∈ cdHull S l := by
    have h := ldModK_mem (S := S) (κ := S.psi 0 (Om (1 + 1 + 1))) ytG3_SC hxH
    rwa [hr, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt (hx'W.trans ytWW_lt_G3)] at h
  have hloga : log ω x' < Om (1 + 1) * Om (1 + 1) :=
    (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hx0).trans_lt hx'W)
  have hgW : log ω x' / Om (1 + 1) < Om (1 + 1) := (Ordinal.lt_mul_iff_div_lt hW0).1 hloga
  have hgH : log ω x' / Om (1 + 1) ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hx'H)
  have hgF : log ω x' / Om (1 + 1) < ytFW S a := by
    by_contra h
    push Not at h
    have h1 := ytFW_ge hown ⟨r, hr⟩ h
    have h2 : leWe (log ω x' / Om (1 + 1)) ≤ x' := by
      unfold leWe
      exact (opow_le_opow_right omega0_pos (Ordinal.mul_div_le _ _)).trans (opow_log_le_self ω hx0)
    exact absurd (h1.trans (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left a).2 h2)).1) (not_le.2 htF)
  set E := log ω x' / Om (1 + 1) + 1 with hE_def
  have hEF : E < ytFW S a := (ytFW_SC a).isSuccLimit.succ_lt hgF
  have hEW : E < Om (1 + 1) := hEF.trans (ytFW_lt_Om2 a)
  have hEc : GxCl (upsilon l) (ldAtR S l) E := (ldHull_iff hl hX hEW).1 (CSet.succ_mem hgH)
  have hxE : x' < leWe E := by
    unfold leWe
    calc x' < ω ^ (log ω x' + 1) := by
          rw [← Order.succ_eq_add_one]; exact lt_opow_succ_log_self one_lt_omega0 x'
      _ ≤ ω ^ (Om (1 + 1) * E) := by
          refine opow_le_opow_right omega0_pos (Order.add_one_le_of_lt ?_)
          rw [hE_def, mul_add_one]; exact Ordinal.lt_mul_div_add _ hW0
  have hle : S.psi (a + x') (Om (1 + 1)) ≤ leTe S E a := by
    unfold leTe; exact (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left a).2 hxE.le)).1
  have hbE := ytBaseE hown ⟨r, hr⟩ haH haA hEF
  rcases hle.lt_or_eq with hlt | heq
  · rcases leClsE hl hX E hEc le_add_self a hbE _ ⟨a + x', hxH, hxA, rfl⟩ hlt with
      h0 | ⟨e', c, v, he', hownc, e⟩
    · exact hz (le_antisymm h0 hta)
    · exact ⟨e', c, v, he'.trans_lt hEF, hownc, e⟩
  · have hc1 : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small (gg_one_lt_of_SC hρSC)
    have h1T : (1 : Ordinal.{0}) < leTe S (E + 1) a :=
      (one_lt_omega0.trans (Lw.lw_omega_lt_SC Ph.ph_SC_Om1)).trans (leOm1_lt_Te _ _)
    refine ⟨E + 1, leWe E * 1 + 0, _, (ytFW_SC a).isSuccLimit.succ_lt hEF,
      LeOwnH.succ hEc le_add_self hc1 one_ne_zero h1T zero_le LeOwnH.zero, ?_⟩
    rw [heq, mul_one, add_zero]; rfl

end Atoms

/-! ## The moves -/

/-- `B_n(W^{Ω₂}) = W^{Ω₂}`. -/
theorem ytWW_D {n : ℕ} : MvD S (leWe (Om (1 + 1))) ∧ Bc.bcB S n (leWe (Om (1 + 1))) = leWe (Om (1 + 1)) := by
  obtain ⟨hWD, hWB⟩ := ytOm2sq_D (S := S) (n := n)
  obtain ⟨hDW, hBW⟩ := ldB_opow (n := n) hWD
  rw [hWB] at hBW
  exact ⟨hDW, hBW⟩

/-- `B_n F^a_W = F^{B_n a}_W`. -/
theorem ytB_FW {n : ℕ} {a : Ordinal.{0}} (hDa : MvD S a)
    (hown : ∀ d, d ≤ Om (1 + 1) → a ∈ S.CSet (a + d) (S.psi (a + d) (Om (1 + 1)))) :
    MvD S (ytFW S a) ∧ Bc.bcB S n (ytFW S a) = ytFW S (Bc.bcB S n a) := by
  obtain ⟨hDW, hBW⟩ := ytWW_D (S := S) (n := n)
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDa hDW
  obtain ⟨hDF, hBF⟩ := mxB_atom (n := n) hDs (CSet.add_mem (ytOwnAll hown _) (leWe_mem (mxOm2_mem _ _)))
  refine ⟨hDF, ?_⟩
  unfold ytFW; rw [hBF, hBs, hBW]

section Win

variable {n : ℕ} {l l' A' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
  (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
  (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1))) (hρ' : S.psi A' (Om 1) = upsilon l')

include hR h1 hr hl' hB hA' hρ'

/-- **EVERY ATOM `ψ₂(a) ≤ s < F^a_W` MOVES** above a base with a law at both ends with `G₃ ∣ a`, `G₃ ∣ B_n a`. -/
theorem ytLeMove {a D : Ordinal.{0}} (hb : YjBase S n l l' A' a D) (hG3 : S.psi 0 (Om (1 + 1 + 1)) ∣ a)
    (hG3' : S.psi 0 (Om (1 + 1 + 1)) ∣ Bc.bcB S n a) {s : Ordinal.{0}} (hs : s ∈ ldAtR S l)
    (hsa : S.psi a (Om (1 + 1)) ≤ s) (hsF : s < ytFW S a)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  obtain ⟨hX, -, -, hX', -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  have hl := hR.1
  set A := ConjT.Aη S (cdEta S l) with hAdef
  have haA : a + leWe (Om (1 + 1)) < A :=
    (vkOmW.1.isPrincipal hb.D_a.2.2 leWW_lt_OmW).trans_le (ConjT.OmW_le_A S _)
  have haA' : Bc.bcB S n a + leWe (Om (1 + 1)) < ConjT.Aη S (cdEta S l') :=
    (vkOmW.1.isPrincipal hb.D_a'.2.2 leWW_lt_OmW).trans_le (ConjT.OmW_le_A S _)
  obtain ⟨e, c, v, heF, hownc, rfl⟩ := ytRep hl hX hb.own hG3 hb.D_a.1 haA hs hsa hsF
  have hbE := ytBaseE hb.own hG3 hb.D_a.1 haA heF
  obtain ⟨hDe, hDc, hDac, hBac, hDv, hBown⟩ := leDigMoveE (n := n) (l' := l') hl hX hownc hbE hb.mv_a
    (fun x hx hxs => by
      obtain ⟨h1, h2, -, h4, h5⟩ := IH x hx hxs
      exact ⟨h1, h2, h4, h5⟩)
  have hownac := leOwnH_own hl hX hownc hbE
  obtain ⟨hDs, hBs⟩ := mxB_atom (n := n) hDac hownac
  obtain ⟨hDF, hBF⟩ := ytB_FW (n := n) hb.mv_a hb.own
  have hBeF : Bc.bcB S n e < ytFW S (Bc.bcB S n a) := by
    have := (mvB_lt_iff (k := n) hDe hDF).2 heF; rwa [hBF] at this
  have hbE' := ytBaseE hb.own' hG3' hb.D_a'.1 haA' hBeF
  obtain ⟨hBH, hBA⟩ := leOwnH_mem hl' hX' hBown hbE'
  obtain ⟨hth', -, -, -⟩ := leOwnRead hl' hX' hBown (A' + Bc.bcB S n D) hbE' hb.hat' hb.law'
  obtain ⟨hth, hownv, -, -⟩ := leOwnRead hl hX hownc (A + D) hbE hb.hat hb.law
  obtain ⟨hDd, hBd⟩ := mvB_add (k := n) hb.mv_D hDv
  have hFth : ytFW S a ≤ Lj.ljThP S := yjPsi2_leW (vkOmW.1.isPrincipal hb.D_a.2.2 leWW_lt_OmW)
  have hhi : S.psi (A + (D + v)) (Om 1) < Bc.bcC S (n + 1) := by
    rw [← add_assoc, ← hth]; exact yjTh_hi hR h1 hr hl' hB (hsF.le.trans hFth)
  have hownd : A + (D + v) ∈ S.CSet (A + (D + v)) (S.psi (A + (D + v)) (Om 1)) := by
    rw [← add_assoc]; exact hownv
  have hψ := yjPsi1 hR h1 hr hl' hB hA' hρ' hDd hownd hhi
  refine ⟨hDs, ?_, ?_⟩
  · rw [hBs, hBac]; exact ⟨_, hBH, hBA, rfl⟩
  · rw [hBs, hBac, hth', hth, add_assoc A, hψ, hBd, add_assoc]

/-- **EVERY ATOM `ψ₂(t) ≤ s < ψ₂(t + W^{Ω₂})` ABOVE EVERY TOP ATOM `t = β + W^{Ω_{k+3}+e}` MOVES** under the premise
of WallBelow at `s`. -/
theorem ytTopMoveW (k : ℕ) {e β : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (hβD : VbD S l β)
    (hbe : Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e β) {s : Ordinal.{0}} (hs : s ∈ ldAtR S l)
    (hst : S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)) ≤ s)
    (hsF : s < ytFW S (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  have IHt := fun x hx (hxs : x < S.psi (β + leWe (X + e)) (Om (1 + 1))) => IH x hx (hxs.trans_le hst)
  obtain ⟨hbt, hBt⟩ := yjTopBase hR h1 hr hl' hB hA' hρ' k hec hβD hbe IHt
  obtain ⟨hdv', -⟩ := yjBaseFacts hR h1 hr hl' hB k hec hβD hbe IHt
  have hd : S.psi 0 (Om (1 + 1 + 1)) ∣ β + leWe (X + e) :=
    dvd_add ((ytG3_dvd_We k e).trans hbe.1) (ytG3_dvd_We k e)
  have hd' : S.psi 0 (Om (1 + 1 + 1)) ∣ Bc.bcB S n (β + leWe (X + e)) := by
    rw [hBt]
    exact dvd_add ((ytG3_dvd_We k _).trans hdv') (ytG3_dvd_We k _)
  exact ytLeMove hR h1 hr hl' hB hA' hρ' hbt hd hd' hs hst hsF IH

end Win

end Googology.Trans.PoR.InaccPsi.R2.Yt

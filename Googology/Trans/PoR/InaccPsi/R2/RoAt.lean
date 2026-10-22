import Googology.Trans.PoR.InaccPsi.R2.RoMove

/-!
# The atoms below `ψ_{Ω₂}(Ω₂^{Ω₂·ω})` move, and the road with the atoms in `[ψ_{Ω₂}(Ω₂^{Ω₂·ω}), θ]`

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ_{Ω₂}(β + W^E)`,
`F_K = ψ_{Ω₂}(W^{Ω₂·K})` (`F_1 = ψ_{Ω₂}(Ω₂^{Ω₂})`, `F_2 = ψ_{Ω₂}(Ω₂^{Ω₂·2})`), `T₁ = ψ_{Ω₂}(Ω₂^{Ω₂+1})` (`Rn.rnT1`).

* `roShK` (the family `{(Ω₂·k, Ω₁·k) | k ≥ 1}`), `roShK_sh` (its shifts and top laws), `roShK_B` (fixed by `B_n`);
* `roClsK` (**`RoClsAt (Ω₂·K) 0` at every base**, `K ≥ 1`: `Ro.roCls_one`, then `Ro.roClsE` and `Ro.roClsW`),
  `roRep0` (**every atom `ψ_{Ω₂}(0) < s ≤ F_K` is `ψ_{Ω₂}(c)` with `c` own over `0`**);
* `roRead0` (**`Θ_λ(ψ_{Ω₂}(c)) = ψ_{Ω₁}(A + 1 + v)`** for every own `(X, e, c, v)` over `0`);
* `roAtMoveK` (**every atom `ψ_{Ω₂}(0) < s ≤ F_K` moves** once the codes below it move);
* `RoAtMove3 S` (a hypothesis name): `Lj.LjAtMove` for the atoms `s ≤ θ` with `F_K < s` for every `K`;
  `roAtMove2_of3` (**`RoAtMove3` gives `Rn.RnAtMove2`**), `roAtMove3_of` (the converse), `roRoadE` (**the road** with
  `RoAtMove3`, `Rn.RnThMoveM`, `Rn.RnEQhi2`), `roRoadE_hyps` (its hypotheses follow from those of `Lj.ljRoadA`).

No new axiom.  New definitions: `roShK`, the hypothesis name `RoAtMove3`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ro

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Lj Googology.Trans.PoR.InaccPsi.R2.Rn

variable {S : InaccSeq.{0}}

/-- **The family of shifts `{(Ω₂·k, Ω₁·k) | k ≥ 1}`.** -/
def roShK (X Xh : Ordinal.{0}) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ X = Om (1 + 1) * (k : Ordinal.{0}) ∧ Xh = Om 1 * (k : Ordinal.{0})

theorem roShK_sh {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) :
    ∀ X Xh, roShK X Xh → RoSh S X Xh ∧
      ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → RoTop S l X Xh e := by
  rintro X Xh ⟨k, hk, rfl, rfl⟩
  exact ⟨roSh_k hk, roTopKE hl hX hk⟩

theorem roShK_B : ∀ X Xh, roShK X Xh → RoShB S X Xh := by
  rintro X Xh ⟨k, hk, rfl, rfl⟩
  have hk0 : (k : Ordinal.{0}) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hk)
  refine ⟨mul_ne_zero (Om_pos one_ne_zero).ne' hk0, fun n => ?_⟩
  obtain ⟨hDW, hBW⟩ := roB_W2 (S := S) (n := n)
  obtain ⟨hDO, hBO⟩ := rnB_O2 (S := S) (n := n)
  obtain ⟨h1, h2⟩ := ldB_mulNat (n := n) hDW hBW k
  obtain ⟨h3, h4⟩ := ldB_mulNat (n := n) hDO hBO k
  rw [← mul_assoc, ← mul_assoc]
  exact ⟨h1, h2, h3, h4⟩

theorem roShK_X {X Xh : Ordinal.{0}} (h : roShK X Xh) : X + Om (1 + 1) < Om ω := by
  obtain ⟨k, -, rfl, rfl⟩ := h
  rw [← mul_add_one]
  have := ldMulNat_lt (Om_isPrincipal omega0_ne_zero) ldOm2_lt_OmW (k + 1)
  rwa [Nat.cast_succ] at this

theorem roShK_mem {X : Ordinal.{0}} (h : X = 0 ∨ ∃ Xh', roShK X Xh') (a b : Ordinal.{0}) :
    X ∈ S.CSet a b := by
  rcases h with rfl | ⟨Xh', k, -, rfl, -⟩
  · exact CSet.zero_mem _ _
  · exact mul_nat_mem (mxOm2_mem a b) k

/-- A base of shift `X` (`0` or in the family) and exponent `e < T_{X+W}(0)` at `0`. -/
theorem roBase0 {l X e : Ordinal.{0}} (hXs : X = 0 ∨ ∃ Xh, RoSh S X Xh) (hXW : X + Om (1 + 1) < Om ω)
    (he : e < leTe S (X + Om (1 + 1)) 0) : RoBaseE S l X e 0 := by
  have hb0 : RoBaseE S l (X + Om (1 + 1)) 0 0 := by
    refine ⟨dvd_zero _, CSet.zero_mem _ _, ?_, fun d _ => CSet.zero_mem _ _, fun e' _ h' => ?_⟩
    · rw [zero_add, add_zero]; exact (roWe_lt_OmW hXW).trans_le le_self_add
    · obtain rfl : e' = 0 := le_antisymm h' zero_le
      exact (SC_psi (InR_Om_succ 1) _).1
  exact roBase_lower hXs hb0 le_rfl he

/-- The exponent index of an own argument is a code. -/
theorem roOwn_code {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    {Sh : Ordinal.{0} → Ordinal.{0} → Prop} {X e β c v : Ordinal.{0}} (h : RoOwn S l Sh X e β c v) :
    GxCl (upsilon l) (ldAtR S l) e := by
  obtain ⟨-, hρ1⟩ := leRho hl hX
  cases h with
  | low hown => exact leOwnH_code hl hX hown (roLeOwn_lt hρ1 hown)
  | succ _ hec _ _ _ _ _ =>
    have heW := roGx_lt_Om2 hρ1 hec
    exact (ldHull_iff hl hX (ldOm2_SC.isSuccLimit.succ_lt heW)).1
      (CSet.succ_mem ((ldHull_iff hl hX heW).2 hec))

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **`RoClsAt (Ω₂·K) 0` at every base**, `K ≥ 1`. -/
theorem roClsK : ∀ K : ℕ, 1 ≤ K → ∀ β, RoBaseE S l (Om (1 + 1) * (K : Ordinal.{0})) 0 β →
    RoClsAt S l roShK (Om (1 + 1) * (K : Ordinal.{0})) 0 β
  | 0, h => absurd h (by norm_num)
  | 1, _ => fun β hb => roCls_one hl hX hb
  | K + 2, _ => by
    have hsh : roShK (Om (1 + 1) * ((K + 1 : ℕ) : Ordinal.{0})) (Om 1 * ((K + 1 : ℕ) : Ordinal.{0})) :=
      ⟨K + 1, by omega, rfl, rfl⟩
    have h := roClsW hl hX (roShK_sh hl hX) hsh
      (roClsE hl hX (roShK_sh hl hX) hsh (roClsK (K + 1) (by omega)))
    rw [← mul_add_one] at h
    have e : ((K + 1 : ℕ) : Ordinal.{0}) + 1 = ((K + 2 : ℕ) : Ordinal.{0}) := (Nat.cast_succ (K + 1)).symm
    rw [e] at h
    exact h

/-- **Every atom `s ≤ F_K` is `≤ ψ_{Ω₂}(0)` or `ψ_{Ω₂}(c)` with `c` own over `0`.** -/
theorem roRep0 {K : ℕ} (hK : 1 ≤ K) (s : Ordinal.{0}) (hs : s ∈ ldAtR S l)
    (hsK : s ≤ S.psi (leWe (Om (1 + 1) * (K : Ordinal.{0}))) (Om (1 + 1))) :
    s ≤ S.psi 0 (Om (1 + 1)) ∨ ∃ X e c v, (X = 0 ∨ ∃ Xh, roShK X Xh) ∧ RoOwn S l roShK X e 0 c v ∧
      RoBaseE S l X e 0 ∧ s = S.psi c (Om (1 + 1)) := by
  have hKW : Om (1 + 1) * (K : Ordinal.{0}) < Om ω := ldMulNat_lt (Om_isPrincipal omega0_ne_zero) ldOm2_lt_OmW K
  have hsh : roShK (Om (1 + 1) * (K : Ordinal.{0})) (Om 1 * (K : Ordinal.{0})) := ⟨K, hK, rfl, rfl⟩
  rcases hsK.lt_or_eq with hlt | rfl
  · have hb : RoBaseE S l (Om (1 + 1) * (K : Ordinal.{0})) 0 0 := by
      refine ⟨dvd_zero _, CSet.zero_mem _ _, ?_, fun d _ => CSet.zero_mem _ _, fun e' _ h' => ?_⟩
      · rw [zero_add, add_zero]; exact (roWe_lt_OmW hKW).trans_le le_self_add
      · obtain rfl : e' = 0 := le_antisymm h' zero_le
        exact (SC_psi (InR_Om_succ 1) _).1
    have hlt' : s < leTe S (Om (1 + 1) * (K : Ordinal.{0}) + 0) 0 := by
      unfold leTe; rwa [add_zero, zero_add]
    rcases roClsK hl hX K hK 0 hb s hs hlt' with h | ⟨X', e', c, v, -, hown, hbo, e1⟩
    · exact Or.inl h
    · rw [zero_add] at e1
      exact Or.inr ⟨X', e', c, v, roOwn_sh hown, hown, hbo, e1⟩
  · obtain ⟨hρSC, -⟩ := leRho hl hX
    have hc0 : GxCl (upsilon l) (ldAtR S l) (0 : Ordinal.{0}) := GxCl.zero hρSC.1
    have hc1 : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small (gg_one_lt_of_SC hρSC)
    have h1T : (1 : Ordinal.{0}) < leTe S (Om (1 + 1) * (K : Ordinal.{0}) + 0 + 1) 0 := roOne_lt_Te _ _
    have hXW : Om (1 + 1) ≤ Om (1 + 1) * (K : Ordinal.{0}) := by
      have hk0 : (K : Ordinal.{0}) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hK)
      exact le_mul_left _ (pos_iff_ne_zero.2 hk0)
    have hown := roTop_own (l := l) (Sh := roShK) hsh hXW hc0 hc1 one_ne_zero h1T
    have hb : RoBaseE S l (Om (1 + 1) * (K : Ordinal.{0})) (0 + 1) 0 := by
      refine ⟨dvd_zero _, CSet.zero_mem _ _, ?_, fun d _ => CSet.zero_mem _ _, fun e' _ h' => ?_⟩
      · rw [zero_add, zero_add]
        refine (roWe_lt_OmW ((Om_isPrincipal omega0_ne_zero) hKW ?_)).trans_le le_self_add
        exact one_lt_omega0.trans (Lw.lw_omega_lt_SC (SC_Om omega0_ne_zero))
      · rw [zero_add] at h' ⊢
        exact (h'.trans_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC Ph.ph_SC_Om1))).trans
          (psiS_bounds (S := S) _ 1).1
    refine Or.inr ⟨_, _, _, _, Or.inr ⟨_, hsh⟩, hown, hb, ?_⟩
    rw [add_zero, mul_one, add_zero]

/-- **`Θ_λ(ψ_{Ω₂}(c)) = ψ_{Ω₁}(A + 1 + v)`** for every own `(X, e, c, v)` over `0`. -/
theorem roRead0 {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    {X e c v : Ordinal.{0}} (hown : RoOwn S l roShK X e 0 c v) (hb : RoBaseE S l X e 0) :
    gxTh (upsilon l) (ldAtR S l) (S.psi c (Om (1 + 1))) = S.psi (A + 1 + v) (Om 1) ∧
      A + 1 + v ∈ S.CSet (A + 1 + v) (S.psi (A + 1 + v) (Om 1)) ∧ v < S.psi 0 (Om (1 + 1)) := by
  have hA1 : A + 1 ∈ S.CSet (A + 1) (S.psi (A + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA) (CSet.one_mem _ _)
  obtain ⟨e1, own1, -, hv⟩ := roOwnRead hl hX (roShK_sh hl hX) hown (A + 1) hb hA1 (ldBlk_zero hA hρ)
  rw [zero_add] at e1
  exact ⟨e1, own1, hv⟩

end Main

/-- `B_n(F_K) = F_K`. -/
theorem roB_FK {n K : ℕ} (hK : 1 ≤ K) :
    MvD S (S.psi (leWe (Om (1 + 1) * (K : Ordinal.{0}))) (Om (1 + 1))) ∧
      Bc.bcB S n (S.psi (leWe (Om (1 + 1) * (K : Ordinal.{0}))) (Om (1 + 1))) =
        S.psi (leWe (Om (1 + 1) * (K : Ordinal.{0}))) (Om (1 + 1)) := by
  obtain ⟨-, hB⟩ := roShK_B (S := S) _ _ (⟨K, hK, rfl, rfl⟩ : roShK (Om (1 + 1) * (K : Ordinal.{0})) (Om 1 * K))
  obtain ⟨hDX, hBX, -, -⟩ := hB n
  obtain ⟨hDW, hBW⟩ := ldB_opow (n := n) hDX
  rw [hBX] at hBW
  have hown : leWe (Om (1 + 1) * (K : Ordinal.{0})) ∈ S.CSet (leWe (Om (1 + 1) * (K : Ordinal.{0})))
      (S.psi (leWe (Om (1 + 1) * (K : Ordinal.{0}))) (Om (1 + 1))) :=
    leWe_mem (mul_nat_mem (mxOm2_mem _ _) K)
  obtain ⟨hDT, hBT⟩ := mxB_atom (n := n) hDW hown
  refine ⟨hDT, ?_⟩
  unfold leWe
  rw [hBT, hBW]

theorem roFK_lt_th {K : ℕ} : S.psi (leWe (Om (1 + 1) * (K : Ordinal.{0}))) (Om (1 + 1)) < ConjT.th S :=
  psi_lt_psi_of_mem (InR_Om_succ 1)
    (roWe_lt_OmW (ldMulNat_lt (Om_isPrincipal omega0_ne_zero) ldOm2_lt_OmW K))
    (leWe_mem (mul_nat_mem (mxOm2_mem _ _) K))

/-- **Every atom `ψ_{Ω₂}(0) < s ≤ F_K` moves** once the codes below it move. -/
theorem roAtMoveK {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
    {K : ℕ} (hK : 1 ≤ K) (s : Ordinal.{0}) (hs : s ∈ ldAtR S l) (hs0 : S.psi 0 (Om (1 + 1)) < s)
    (hsK : s ≤ S.psi (leWe (Om (1 + 1) * (K : Ordinal.{0}))) (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  obtain ⟨A, A', ηx, ηx', hX, hX', hA, hA', hρ, hρ', hbX, hBψ⟩ := rnSetup hR h1 hr hB
  have hl := hR.1
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hG1 : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
  have hD0 : MvD S (0 : Ordinal.{0}) := mvD_of_lt (Lw.lw_L_SC S ω).1
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  rcases roRep0 hl hX hK s hs hsK with hle | ⟨X, e, c, v, hXs, hown, hb, rfl⟩
  · exact absurd hs0 (not_lt.2 hle)
  obtain ⟨e1, own1, hv⟩ := roRead0 hl hX hA hρ hown hb
  obtain ⟨hDe, hDc, -, -, hDv, hown'⟩ := roDigMove (n := n) (l' := l') hl hX (roShK_sh hl hX) roShK_B hown hb
    hD0 (fun x hx hxs => by
      obtain ⟨a, b, -, d, e⟩ := IH x hx (by rwa [zero_add] at hxs)
      exact ⟨a, b, d, e⟩)
  rw [Bc.bcB_zero] at hown'
  -- the base at `λ'`
  have hXs' : X = 0 ∨ ∃ Xh, RoSh S X Xh := by
    rcases hXs with h0 | ⟨Xh, k, hk, rfl, rfl⟩
    · exact Or.inl h0
    · exact Or.inr ⟨_, roSh_k hk⟩
  have hXW : X + Om (1 + 1) < Om ω := by
    rcases hXs with rfl | ⟨Xh, h⟩
    · rw [zero_add]; exact ldOm2_lt_OmW
    · exact roShK_X h
  have hXB : X = 0 ∨ ∃ Xh, RoShB S X Xh := by
    rcases hXs with h0 | ⟨Xh, h⟩
    · exact Or.inl h0
    · exact Or.inr ⟨Xh, roShK_B _ _ h⟩
  have hec := roOwn_code hl hX hown
  have heW := roGx_lt_Om2 hρ1 hec
  have heT : e < leTe S (X + Om (1 + 1)) 0 := by
    refine (hb.2.2.2.2 e hec le_rfl).trans_le ?_
    exact (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left 0).2
      (leWe_mono ((add_le_add_iff_left X).2 heW.le)))).1
  obtain ⟨hDWW, hBWW⟩ := roB_WeW (S := S) (n := n) hXB
  obtain ⟨hD0W, hB0W⟩ := mvB_add (k := n) hD0 hDWW
  rw [Bc.bcB_zero, hBWW] at hB0W
  have hTown : 0 + leWe (X + Om (1 + 1)) ∈ S.CSet (0 + leWe (X + Om (1 + 1)))
      (S.psi (0 + leWe (X + Om (1 + 1))) (Om (1 + 1))) :=
    CSet.add_mem (CSet.zero_mem _ _) (leWe_mem (CSet.add_mem (roShK_mem hXs _ _) (mxOm2_mem _ _)))
  obtain ⟨hDT, hBT⟩ := mxB_atom (n := n) hD0W hTown
  rw [hB0W] at hBT
  have hBeT : Bc.bcB S n e < leTe S (X + Om (1 + 1)) 0 := by
    have h := (mvB_lt_iff (k := n) hDe hDT).2 heT
    unfold leTe at h ⊢; rwa [hBT] at h
  have hb' : RoBaseE S l' X (Bc.bcB S n e) 0 := roBase0 hXs' hXW hBeT
  have hA'1 : A' + 1 ∈ S.CSet (A' + 1) (S.psi (A' + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA') (CSet.one_mem _ _)
  obtain ⟨e1', -, -, -⟩ := roOwnRead hl' hX' (roShK_sh hl' hX') hown' (A' + 1) hb' hA'1 (ldBlk_zero hA' hρ')
  rw [zero_add] at e1'
  -- the move of the atom
  have hcown := roOwn_own hl hX (roShK_sh hl hX) hown hb
  rw [zero_add] at hcown
  obtain ⟨hDs, hBs⟩ := mxB_atom (n := n) hDc hcown
  obtain ⟨hBH, hBA⟩ := roOwn_mem hl' hX' (roShK_sh hl' hX') hown' hb'
  rw [zero_add] at hBH hBA
  obtain ⟨hDF, hBF⟩ := roB_FK (S := S) (n := n) hK
  have hvθ : 1 + v ≤ ConjT.th S :=
    (hG1.isPrincipal (one_lt_omega0.trans (Lw.lw_omega_lt_SC hG1)) hv).le.trans rnG_le_th
  have hownd : A + (1 + v) ∈ S.CSet (A + (1 + v)) (S.psi (A + (1 + v)) (Om 1)) := by
    rw [← add_assoc]; exact own1
  obtain ⟨hD1v, hB1v⟩ := mvB_add (k := n) hD1 hDv
  rw [mwB_one] at hB1v
  refine ⟨hDs, by rw [hBs]; exact ⟨_, hBH, hBA, rfl⟩, ?_, by rw [e1, add_assoc]; exact hbX _ hvθ, ?_⟩
  · have h := leB_le (n := n) hDs hDF hsK
    rw [hBF] at h
    exact (h.trans_lt roFK_lt_th).trans ljTh_lt_ThP
  · rw [hBs, e1', e1, add_assoc A, hBψ _ hD1v hownd hvθ, hB1v, add_assoc]

/-- **`LjAtMove` for the atoms `s ≤ θ` above every `F_K = ψ_{Ω₂}(Ω₂^{Ω₂·K})`.** -/
def RoAtMove3 (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    leFWW S ≤ cdCode S l → cdCode S l < ljThP S →
    ∀ s ∈ ldAtR S l, (∀ K : ℕ, S.psi (leWe (Om (1 + 1) * (K : Ordinal.{0}))) (Om (1 + 1)) < s) →
      s ≤ ConjT.th S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)

theorem roT1_lt_F2 : rnT1 S < S.psi (leWe (Om (1 + 1) * ((2 : ℕ) : Ordinal.{0}))) (Om (1 + 1)) := by
  unfold rnT1
  rw [← leWe_succ]
  refine psi_lt_psi_of_mem (InR_Om_succ 1) (leWe_lt ?_) (leWe_mem (CSet.succ_mem (mxOm2_mem _ _)))
  have e : Om (1 + 1 : Ordinal.{0}) * ((2 : ℕ) : Ordinal.{0}) = Om (1 + 1) + Om (1 + 1) := by
    rw [show ((2 : ℕ) : Ordinal.{0}) = 1 + 1 by norm_num, mul_add, mul_one]
  rw [e]
  exact (add_lt_add_iff_left _).2 (one_lt_omega0.trans (Lw.lw_omega_lt_SC ldOm2_SC))

/-- **`RoAtMove3` gives `RnAtMove2`.** -/
theorem roAtMove2_of3 (h : RoAtMove3 S) : RnAtMove2 S := by
  intro n l l' hR h1 hr hl' hB hm hF hK s hs hs1 hsθ IH
  by_cases hex : ∃ K : ℕ, 1 ≤ K ∧ s ≤ S.psi (leWe (Om (1 + 1) * (K : Ordinal.{0}))) (Om (1 + 1))
  · obtain ⟨K, hK1, hsK⟩ := hex
    have hs0 : S.psi 0 (Om (1 + 1)) < s :=
      lt_of_le_of_lt (psi_mono (S := S) (InR_Om_succ 1) zero_le).1 hs1
    exact roAtMoveK hR h1 hr hl' hB hK1 s hs hs0 hsK IH
  · push Not at hex
    refine h n l l' hR h1 hr hl' hB hm hF hK s hs (fun K => ?_) hsθ IH
    rcases K with _ | K
    · refine lt_of_le_of_lt ?_ hs1
      unfold rnT1
      refine (psi_mono (S := S) (InR_Om_succ 1) ?_).1
      rw [Nat.cast_zero, mul_zero, leWe_zero]
      exact Order.one_le_iff_pos.2 (mul_pos (leWe_pos _) ldOm2_SC.1)
    · exact hex (K + 1) (by omega)

/-- **`RnAtMove2` gives `RoAtMove3`.** -/
theorem roAtMove3_of (h : RnAtMove2 S) : RoAtMove3 S :=
  fun n l l' hR h1 hr hl' hB hm hF hK s hs hsK hsθ IH =>
    h n l l' hR h1 hr hl' hB hm hF hK s hs (roT1_lt_F2.trans (hsK 2)) hsθ IH

/-- **The road with `RoAtMove3`, `RnThMoveM` and `RnEQhi2`** (each under `L(ω+1) ≤ ν_C`). -/
theorem roRoadE (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (hat : Nc.ncL S (ω + 1) ≤ nuC → RoAtMove3 S)
    (hM : Nc.ncL S (ω + 1) ≤ nuC → RnThMoveM S) (hhi : Nc.ncL S (ω + 1) ≤ nuC → RnEQhi2 S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  rnRoadD hU hO hL hV hN hlh (fun hν => roAtMove2_of3 (hat hν)) hM hhi

/-- **Satisfiability**: the hypotheses of `roRoadE` follow from those of `Rn.rnRoadD`. -/
theorem roRoadE_hyps (hat : Nc.ncL S (ω + 1) ≤ nuC → RnAtMove2 S) :
    Nc.ncL S (ω + 1) ≤ nuC → RoAtMove3 S :=
  fun hν => roAtMove3_of (hat hν)

end Googology.Trans.PoR.InaccPsi.R2.Ro

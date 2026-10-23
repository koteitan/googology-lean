import Googology.Trans.PoR.InaccPsi.R2.RwFMove

/-!
# The atoms below `ψ_{Ω₂}(Ω₂^{Ω₂^{Ω₁}})` move, and the road with the atoms in `[ψ_{Ω₂}(Ω₂^{Ω₂^{Ω₁}}), θ]`

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `T_E(β) = ψ_{Ω₂}(β + W^E)`,
`F_1 = ψ_{Ω₂}(Ω₂^{Ω₂^{Ω₁}}) = T_{W^{Ω₁}}(0)`, `F = ψ_{Ω₂}(Ω₂^{Ω₂²})` (the bound of `Rq.RqAtMove6`).

* `rwRd_zero` (the base `0` has the reading `ψ_{Ω₁}(A + 1)`), `rwG3_lt_OmW`;
* `rwRep` (**every atom `s < F_1` is `≤ ψ_{Ω₂}(0)` or `ψ_{Ω₂}(c)` with `c` own over `0`** for the family
  `Rw.rwShF`), `rwRead` (**`Θ_λ(ψ_{Ω₂}(c)) = ψ_{Ω₁}(A + 1 + v)`**);
* `rwAtMoveW` (**every atom `ψ_{Ω₂}(0) < s < F_1` moves** once the codes below it move: `B_n s` is an atom at
  `λ'`, `B_n s < θ⁺`, `Θ_λ s < c_{n+1}`, `Θ_{λ'}(B_n s) = B_n(Θ_λ s)`);
* `RwAtMove7 S` (a hypothesis name): `Lj.LjAtMove` for the atoms `F_1 ≤ s ≤ θ`; `rwAtMove6_of7` (**`RwAtMove7`
  gives `Rq.RqAtMove6`**), `rwAtMove7_of6` (the converse), `rwRoadI` (**the road**), `rwRoadI_hyps`.

No new axiom.  New definition: the hypothesis name `RwAtMove7`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Lj Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv

variable {S : InaccSeq.{0}}

theorem rwG3_lt_OmW : S.psi 0 (Om (1 + 1 + 1)) < Om (ω : Ordinal.{0}) := by
  have h3 : (1 + 1 + 1 : Ordinal.{0}) < ω := by
    rw [show (1 + 1 + 1 : Ordinal.{0}) = ((3 : ℕ) : Ordinal.{0}) by norm_num]; exact natCast_lt_omega0 3
  exact (psi_lt (InR_Om_succ (1 + 1)) 0).trans (Om_lt_Om.2 h3)

/-- `F = ψ_{Ω₂}(Ω₂^{Ω₂²}) ≤ F_1 = ψ_{Ω₂}(Ω₂^{Ω₂^{Ω₁}})`. -/
theorem rwF_le_F1 :
    S.psi (leWe (Om (1 + 1) * Om (1 + 1))) (Om (1 + 1)) ≤ S.psi (leWe (leWe (Om 1))) (Om (1 + 1)) := by
  have e : Om (1 + 1 : Ordinal.{0}) * Om (1 + 1) = leWe (1 + 1) := by rw [leWe_succ, leWe_one]
  refine (psi_mono (S := S) (InR_Om_succ 1) (leWe_mono ?_)).1
  rw [e]; exact leWe_mono (one_lt_omega0.trans (Lw.lw_omega_lt_SC Ph.ph_SC_Om1)).succ_le

theorem rwF1_lt_th : S.psi (leWe (leWe (Om 1))) (Om (1 + 1)) < ConjT.th S := by
  have hW1 : leWe (Om 1) < Om ω := roWe_lt_OmW (gg_Om1_lt_Om2.trans ldOm2_lt_OmW)
  exact psi_lt_psi_of_mem (InR_Om_succ 1) (roWe_lt_OmW hW1)
    (leWe_mem (leWe_mem (CSet.Om_mem (CSet.one_mem _ _))))

/-- The exponent index of an own argument is a code. -/
theorem rwOwn_code {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    {Sh : Ordinal.{0} → Ordinal.{0} → Ordinal.{0} → Prop} {X e β c v : Ordinal.{0}}
    (h : RwOwn S l Sh X e β c v) : GxCl (upsilon l) (ldAtR S l) e := by
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

omit hl hX in
/-- The base `0` has a reading. -/
theorem rwRd_zero {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    RwRd S l 0 :=
  ⟨A + 1, CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA) (CSet.one_mem _ _),
    ldBlk_zero hA hρ⟩

/-- **Every atom `s < F_1` is `≤ ψ_{Ω₂}(0)` or `ψ_{Ω₂}(c)` with `c` own over `0`.** -/
theorem rwRep (hrd : RwRd S l 0) (s : Ordinal.{0}) (hs : s ∈ ldAtR S l)
    (hsW : s < S.psi (leWe (leWe (Om 1))) (Om (1 + 1))) :
    s ≤ S.psi 0 (Om (1 + 1)) ∨ ∃ X e c v, (X = 0 ∨ ∃ Xh, rwShF S l 0 X Xh) ∧
      RwOwn S l (rwShF S l) X e 0 c v ∧ RoBaseE S l X e 0 ∧ s = S.psi c (Om (1 + 1)) := by
  have hT : s < leTe S (leWe (Om 1) + 0) 0 := by unfold leTe; rwa [add_zero, zero_add]
  rcases rwCls_top hl hX hrd s hs hT with h | ⟨X, e, c, v, -, hown, hb, e1⟩
  · exact Or.inl h
  · rw [zero_add] at e1
    exact Or.inr ⟨X, e, c, v, rwOwn_sh hown, hown, hb, e1⟩

/-- **`Θ_λ(ψ_{Ω₂}(c)) = ψ_{Ω₁}(A + 1 + v)`** for every own `(X, e, c, v)` over `0`. -/
theorem rwRead {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    {X e c v : Ordinal.{0}} (hown : RwOwn S l (rwShF S l) X e 0 c v) (hb : RoBaseE S l X e 0) :
    gxTh (upsilon l) (ldAtR S l) (S.psi c (Om (1 + 1))) = S.psi (A + 1 + v) (Om 1) ∧
      A + 1 + v ∈ S.CSet (A + 1 + v) (S.psi (A + 1 + v) (Om 1)) ∧ c < leWe (X + e) ∧
      v < S.psi 0 (Om (1 + 1)) := by
  have hA1 : A + 1 ∈ S.CSet (A + 1) (S.psi (A + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA) (CSet.one_mem _ _)
  obtain ⟨e1, own1, hc, hv⟩ := rwOwnRead hl hX (rwShF_sh hl hX) hown (A + 1) hb hA1 (ldBlk_zero hA hρ)
  rw [zero_add] at e1
  exact ⟨e1, own1, hc, hv⟩

end Main

/-- A base `0` of a shift `X` (`0` or own relative to `0`) and an exponent `e < T_{X+W}(0)`. -/
theorem rwBase0 {l X e : Ordinal.{0}} (hXs : X = 0 ∨ ∃ Xh, RvSh S l 0 X Xh) (hXW : X + Om (1 + 1) < Om ω)
    (he : e < leTe S (X + Om (1 + 1)) 0) : RoBaseE S l X e 0 := by
  have hb0 : RoBaseE S l (X + Om (1 + 1)) 0 0 := by
    refine ⟨dvd_zero _, CSet.zero_mem _ _, ?_, fun d _ => CSet.zero_mem _ _, fun e' _ h' => ?_⟩
    · rw [zero_add, add_zero]; exact (roWe_lt_OmW hXW).trans_le le_self_add
    · obtain rfl : e' = 0 := le_antisymm h' zero_le
      exact (SC_psi (InR_Om_succ 1) _).1
  exact rwBase_lower hXs le_rfl hb0 le_rfl he

theorem rwX_W {l X : Ordinal.{0}} (h : X = 0 ∨ ∃ Xh, RvSh S l 0 X Xh) : X + Om (1 + 1) < Om ω := by
  rcases h with rfl | ⟨Xh, h⟩
  · rw [zero_add]; exact ldOm2_lt_OmW
  · exact h.ltG3.trans rwG3_lt_OmW

/-- **Every atom `ψ_{Ω₂}(0) < s < F_1` moves** once the codes below it move. -/
theorem rwAtMoveW {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
    (s : Ordinal.{0}) (hs : s ∈ ldAtR S l) (hs0 : S.psi 0 (Om (1 + 1)) < s)
    (hsW : s < S.psi (leWe (leWe (Om 1))) (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  obtain ⟨A, A', ηx, ηx', hX, hX', hA, hA', hρ, hρ', hbX, hBψ⟩ := rnSetup hR h1 hr hB
  have hl := hR.1
  have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans ((cdR_ge S l).trans_lt hr)
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hG1 : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
  have hD0 : MvD S (0 : Ordinal.{0}) := mvD_of_lt (Lw.lw_L_SC S ω).1
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  have hSh := rwShF_sh (S := S) hl hX
  have hSh' := rwShF_sh (S := S) hl' hX'
  rcases rwRep hl hX (rwRd_zero hA hρ) s hs hsW with hle | ⟨X, e, c, v, hXs, hown, hb, rfl⟩
  · exact absurd hs0 (not_lt.2 hle)
  obtain ⟨e1, own1, -, hv⟩ := rwRead hl hX hA hρ hown hb
  obtain ⟨hDe, hDc, -, -, hDv, XB, hDX, hBX, hown'⟩ := rwDigMove (n := n) (l' := l') hl hX hSh
    (rwShF_B hl hX h2 hB) hown hb hD0 (fun x hx hxs => by
      obtain ⟨a, b, -, d, e⟩ := IH x hx (by rwa [zero_add] at hxs)
      exact ⟨a, b, d, e⟩)
  rw [Bc.bcB_zero] at hown'
  -- the shifts at `λ` and `λ'`
  have hXs' : X = 0 ∨ ∃ Xh, RvSh S l 0 X Xh := by
    rcases hXs with h0 | ⟨Xh, h⟩
    · exact Or.inl h0
    · exact Or.inr ⟨Xh, (hSh _ _ _ h).1⟩
  have hXBs : XB = 0 ∨ ∃ Xh, rwShF S l' 0 XB Xh := rwOwn_sh hown'
  have hXBs' : XB = 0 ∨ ∃ Xh, RvSh S l' 0 XB Xh := by
    rcases hXBs with h0 | ⟨Xh, h⟩
    · exact Or.inl h0
    · exact Or.inr ⟨Xh, (hSh' _ _ _ h).1⟩
  have hec := rwOwn_code hl hX hown
  have heW := roGx_lt_Om2 hρ1 hec
  have heT : e < leTe S (X + Om (1 + 1)) 0 := by
    refine (hb.2.2.2.2 e hec le_rfl).trans_le ?_
    exact (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left 0).2
      (leWe_mono ((add_le_add_iff_left X).2 heW.le)))).1
  obtain ⟨hDWW, hBWW⟩ := rqB_WeW (S := S) (n := n) hDX hBX
  obtain ⟨hD0W, hB0W⟩ := mvB_add (k := n) hD0 hDWW
  rw [Bc.bcB_zero, hBWW] at hB0W
  have hXC : X ∈ S.CSet (0 + leWe (X + Om (1 + 1))) (S.psi (0 + leWe (X + Om (1 + 1))) (Om (1 + 1))) := by
    rcases hXs' with rfl | ⟨Xh, hs'⟩
    · exact CSet.zero_mem _ _
    · exact rvMem hs' (rvWX_le le_rfl X _) le_rfl
  have hTown : 0 + leWe (X + Om (1 + 1)) ∈ S.CSet (0 + leWe (X + Om (1 + 1)))
      (S.psi (0 + leWe (X + Om (1 + 1))) (Om (1 + 1))) :=
    CSet.add_mem (CSet.zero_mem _ _) (leWe_mem (CSet.add_mem hXC (mxOm2_mem _ _)))
  obtain ⟨hDT, hBT⟩ := mxB_atom (n := n) hD0W hTown
  rw [hB0W] at hBT
  have hBeT : Bc.bcB S n e < leTe S (XB + Om (1 + 1)) 0 := by
    have h := (mvB_lt_iff (k := n) hDe hDT).2 heT
    unfold leTe at h ⊢; rwa [hBT] at h
  have hb' : RoBaseE S l' XB (Bc.bcB S n e) 0 := rwBase0 hXBs' (rwX_W hXBs') hBeT
  have hA'1 : A' + 1 ∈ S.CSet (A' + 1) (S.psi (A' + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA') (CSet.one_mem _ _)
  obtain ⟨e1', -, hc', -⟩ := rwOwnRead hl' hX' hSh' hown' (A' + 1) hb' hA'1 (ldBlk_zero hA' hρ')
  rw [zero_add] at e1'
  -- the move of the atom
  have hcown := rwOwn_own hl hX hSh hown hb
  rw [zero_add] at hcown
  obtain ⟨hDs, hBs⟩ := mxB_atom (n := n) hDc hcown
  obtain ⟨hBH, hBA⟩ := rwOwn_mem hl' hX' hSh' hown' hb'
  rw [zero_add] at hBH hBA
  have hvθ : 1 + v ≤ ConjT.th S :=
    (hG1.isPrincipal (one_lt_omega0.trans (Lw.lw_omega_lt_SC hG1)) hv).le.trans rnG_le_th
  have hownd : A + (1 + v) ∈ S.CSet (A + (1 + v)) (S.psi (A + (1 + v)) (Om 1)) := by
    rw [← add_assoc]; exact own1
  obtain ⟨hD1v, hB1v⟩ := mvB_add (k := n) hD1 hDv
  rw [mwB_one] at hB1v
  refine ⟨hDs, by rw [hBs]; exact ⟨_, hBH, hBA, rfl⟩, ?_, by rw [e1, add_assoc]; exact hbX _ hvθ, ?_⟩
  · -- `B_n s = ψ_{Ω₂}(B_n c) ≤ θ < θ⁺`
    have hEW : XB + Bc.bcB S n e < Om ω := by
      have hBeW : Bc.bcB S n e < Om (1 + 1) := hBeT.trans (leTe_lt_Om2 _ _)
      exact lt_of_le_of_lt ((add_le_add_iff_left XB).2 hBeW.le) (rwX_W hXBs')
    have hcW : Bc.bcB S n c ≤ Om ω := (hc'.trans (roWe_lt_OmW hEW)).le
    rw [hBs]
    exact ((psi_mono (S := S) (InR_Om_succ 1) hcW).1).trans_lt ljTh_lt_ThP
  · rw [hBs, e1', e1, add_assoc A, hBψ _ hD1v hownd hvθ, hB1v, add_assoc]

/-- **`LjAtMove` for the atoms `F_1 ≤ s ≤ θ`** (`F_1 = ψ_{Ω₂}(Ω₂^{Ω₂^{Ω₁}})`). -/
def RwAtMove7 (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    leFWW S ≤ cdCode S l → cdCode S l < ljThP S →
    ∀ s ∈ ldAtR S l, S.psi (leWe (leWe (Om 1))) (Om (1 + 1)) ≤ s → s ≤ ConjT.th S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)

/-- **`RwAtMove7` gives `Rq.RqAtMove6`.** -/
theorem rwAtMove6_of7 (h : RwAtMove7 S) : RqAtMove6 S := by
  intro n l l' hR h1 hr hl' hB hm hF hK s hs hsF hsθ IH
  rcases lt_or_ge s (S.psi (leWe (leWe (Om 1))) (Om (1 + 1))) with hlt | hge
  · have hs0 : S.psi 0 (Om (1 + 1)) < s := by
      refine lt_of_lt_of_le ?_ hsF
      refine psi_lt_psi_of_mem (InR_Om_succ 1) (leWe_pos _) ?_
      exact CSet.zero_mem _ _
    exact rwAtMoveW hR h1 hr hl' hB s hs hs0 hlt IH
  · exact h n l l' hR h1 hr hl' hB hm hF hK s hs hge hsθ IH

/-- **`Rq.RqAtMove6` gives `RwAtMove7`.** -/
theorem rwAtMove7_of6 (h : RqAtMove6 S) : RwAtMove7 S :=
  fun n l l' hR h1 hr hl' hB hm hF hK s hs hsF hsθ IH =>
    h n l l' hR h1 hr hl' hB hm hF hK s hs (rwF_le_F1.trans hsF) hsθ IH

/-- **The road with `RwAtMove7`, `Rn.RnThMoveM` and `Rn.RnEQhi2`** (each under `L(ω+1) ≤ ν_C`). -/
theorem rwRoadI (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (hat : Nc.ncL S (ω + 1) ≤ nuC → RwAtMove7 S)
    (hM : Nc.ncL S (ω + 1) ≤ nuC → RnThMoveM S) (hhi : Nc.ncL S (ω + 1) ≤ nuC → RnEQhi2 S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  rqRoadH hU hO hL hV hN hlh (fun hν => rwAtMove6_of7 (hat hν)) hM hhi

/-- **Satisfiability**: the hypothesis of `rwRoadI` follows from that of `Rq.rqRoadH`. -/
theorem rwRoadI_hyps (hat : Nc.ncL S (ω + 1) ≤ nuC → RqAtMove6 S) :
    Nc.ncL S (ω + 1) ≤ nuC → RwAtMove7 S :=
  fun hν => rwAtMove7_of6 (hat hν)

end Googology.Trans.PoR.InaccPsi.R2.Rw

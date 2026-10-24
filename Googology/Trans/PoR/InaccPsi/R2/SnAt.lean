import Googology.Trans.PoR.InaccPsi.R2.SnMove
import Googology.Trans.PoR.InaccPsi.R2.RwWW

/-!
# The atoms below `ψ_{Ω₂}(ε_{Ω₂+1})` move, and the road with the atoms in `[ψ_{Ω₂}(ε_{Ω₂+1}), θ]`

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `ε = ε_{Ω₂+1}`,
`F_ε = ψ_{Ω₂}(ε_{Ω₂+1}) = T_{W^ε}(0)`, `F_2 = ψ_{Ω₂}(Ω₂^{Ω₂^{Ω₂}})` (the bound of `Rw.RwAtMove10`), `θ⁺ = Lj.ljThP`.

* `snReadG` (**`Θ_λ(ψ_{Ω₂}(c)) = ψ_{Ω₁}(A + 1 + v)`** for every own `(X, e, c, v)` over `0`, family `snShG`);
* `snAtMoveG` (**every atom `ψ_{Ω₂}(0) < s < F_ε` moves** once the codes below it move: `B_n s` is an atom at
  `λ'`, `B_n s < θ⁺`, `Θ_λ s < c_{n+1}`, `Θ_{λ'}(B_n s) = B_n(Θ_λ s)`; no extra hypothesis);
* `SnAtMove11 S` (a hypothesis name): `Lj.LjAtMove` for the atoms `F_ε ≤ s ≤ θ`; `snF2_lt_Feps`,
  `snAtMove10_of11` (**`SnAtMove11` gives `Rw.RwAtMove10`**), `snAtMove11_of10` (the converse), `snRoadL`
  (**the road**), `snRoadL_hyps`.

No new axiom.  New definition: the hypothesis name `SnAtMove11`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Lj Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw

variable {S : InaccSeq.{0}}

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **`Θ_λ(ψ_{Ω₂}(c)) = ψ_{Ω₁}(A + 1 + v)`** for every own `(X, e, c, v)` over `0` (family `snShG`). -/
theorem snReadG {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    {X e c v : Ordinal.{0}} (hown : RwOwn S l (snShG S l) X e 0 c v) (hb : RoBaseE S l X e 0) :
    gxTh (upsilon l) (ldAtR S l) (S.psi c (Om (1 + 1))) = S.psi (A + 1 + v) (Om 1) ∧
      A + 1 + v ∈ S.CSet (A + 1 + v) (S.psi (A + 1 + v) (Om 1)) ∧ c < leWe (X + e) ∧
      v < S.psi 0 (Om (1 + 1)) := by
  have hA1 : A + 1 ∈ S.CSet (A + 1) (S.psi (A + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA) (CSet.one_mem _ _)
  obtain ⟨e1, own1, hc, hv⟩ := rwOwnRead hl hX (snShG_sh hl hX) hown (A + 1) hb hA1 (ldBlk_zero hA hρ)
  rw [zero_add] at e1
  exact ⟨e1, own1, hc, hv⟩

end Main

/-- **Every atom `ψ_{Ω₂}(0) < s < ψ_{Ω₂}(ε_{Ω₂+1})` moves** once the codes below it move. -/
theorem snAtMoveG {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
    (s : Ordinal.{0}) (hs : s ∈ ldAtR S l) (hs0 : S.psi 0 (Om (1 + 1)) < s)
    (hsε : s < S.psi (veblen 1 (Om (1 + 1) + 1)) (Om (1 + 1)))
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
  have hSh := snShG_sh (S := S) hl hX
  have hSh' := snShG_sh (S := S) hl' hX'
  rcases snRepG hl hX hA hρ s hs hsε with hle | ⟨X, e, c, v, hXs, hown, hb, rfl⟩
  · exact absurd hs0 (not_lt.2 hle)
  obtain ⟨e1, own1, -, hv⟩ := snReadG hl hX hA hρ hown hb
  obtain ⟨hDe, hDc, -, -, hDv, XB, hDX, hBX, hown'⟩ := rwDigMove (n := n) (l' := l') hl hX hSh
    (snShG_B hl hX hl' hX') hown hb hD0 (fun x hx hxs => by
      obtain ⟨a, b, -, d, e⟩ := IH x hx (by rwa [zero_add] at hxs)
      exact ⟨a, b, d, e⟩)
  rw [Bc.bcB_zero] at hown'
  -- the shifts at `λ` and `λ'`
  have hXs' : X = 0 ∨ ∃ Xh, RvSh S l 0 X Xh := by
    rcases hXs with h0 | ⟨Xh, h⟩
    · exact Or.inl h0
    · exact Or.inr ⟨Xh, (hSh _ _ _ h).1⟩
  have hXBs : XB = 0 ∨ ∃ Xh, snShG S l' 0 XB Xh := rwOwn_sh hown'
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
  · have hEW : XB + Bc.bcB S n e < Om ω := by
      have hBeW : Bc.bcB S n e < Om (1 + 1) := hBeT.trans (leTe_lt_Om2 _ _)
      exact lt_of_le_of_lt ((add_le_add_iff_left XB).2 hBeW.le) (rwX_W hXBs')
    have hcW : Bc.bcB S n c ≤ Om ω := (hc'.trans (roWe_lt_OmW hEW)).le
    rw [hBs]
    exact ((psi_mono (S := S) (InR_Om_succ 1) hcW).1).trans_lt ljTh_lt_ThP
  · rw [hBs, e1', e1, add_assoc A, hBψ _ hD1v hownd hvθ, hB1v, add_assoc]

/-- **`LjAtMove` for the atoms `ψ_{Ω₂}(ε_{Ω₂+1}) ≤ s ≤ θ`.** -/
def SnAtMove11 (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    leFWW S ≤ cdCode S l → cdCode S l < ljThP S →
    ∀ s ∈ ldAtR S l, S.psi (veblen 1 (Om (1 + 1) + 1)) (Om (1 + 1)) ≤ s → s ≤ ConjT.th S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)

/-- `F_2 = ψ_{Ω₂}(Ω₂^{Ω₂^{Ω₂}}) < ψ_{Ω₂}(ε_{Ω₂+1})`. -/
theorem snF2_lt_Feps :
    S.psi (leWe (leWe (Om (1 + 1)))) (Om (1 + 1)) < S.psi (veblen 1 (Om (1 + 1) + 1)) (Om (1 + 1)) := by
  have hW : Om (1 + 1 : Ordinal.{0}) < veblen 1 (Om (1 + 1) + 1) :=
    (lt_add_one _).trans_le (right_le_veblen 1 _)
  have hp := Ph.ph_veblen_prin (1 : Ordinal.{0}) (Om (1 + 1) + 1)
  have hfix : ∀ x, x < veblen 1 (Om (1 + 1) + 1) → leWe x < veblen 1 (Om (1 + 1) + 1) := by
    intro x hx
    have hE : ω ^ veblen 1 (Om (1 + 1) + 1) = veblen 1 (Om (1 + 1) + 1) := gg_veblen_eps one_ne_zero
    have hk : Om (1 + 1) * x < veblen 1 (Om (1 + 1) + 1) := by
      rcases eq_or_ne x 0 with rfl | hx0
      · rw [mul_zero]; exact lt_of_le_of_lt zero_le hW
      have hlt : Om (1 + 1) * x ≤ ω ^ (Om (1 + 1) + x) := by
        rw [opow_add, gg_SC_eps ldOm2_SC]
        exact mul_le_mul_right (right_le_opow x one_lt_omega0) _
      refine hlt.trans_lt ?_
      conv_rhs => rw [← hE]
      exact (opow_lt_opow_iff_right one_lt_omega0).2 (hp hW hx)
    unfold leWe
    conv_rhs => rw [← hE]
    exact (opow_lt_opow_iff_right one_lt_omega0).2 hk
  refine psi_lt_psi_of_mem (InR_Om_succ 1) (hfix _ (hfix _ hW)) ?_
  exact leWe_mem (leWe_mem (mxOm2_mem _ _))

/-- **`SnAtMove11` gives `Rw.RwAtMove10`.** -/
theorem snAtMove10_of11 (h : SnAtMove11 S) : RwAtMove10 S := by
  intro n l l' hR h1 hr hl' hB hm hF hK s hs hsF hsθ IH
  rcases lt_or_ge s (S.psi (veblen 1 (Om (1 + 1) + 1)) (Om (1 + 1))) with hlt | hge
  · have hs0 : S.psi 0 (Om (1 + 1)) < s :=
      lt_of_le_of_lt (psi_mono (S := S) (InR_Om_succ 1) zero_le).1 hsF
    exact snAtMoveG hR h1 hr hl' hB s hs hs0 hlt IH
  · exact h n l l' hR h1 hr hl' hB hm hF hK s hs hge hsθ IH

/-- **`Rw.RwAtMove10` gives `SnAtMove11`.** -/
theorem snAtMove11_of10 (h : RwAtMove10 S) : SnAtMove11 S :=
  fun n l l' hR h1 hr hl' hB hm hF hK s hs hsF hsθ IH =>
    h n l l' hR h1 hr hl' hB hm hF hK s hs (snF2_lt_Feps.trans_le hsF) hsθ IH

/-- **The road with `SnAtMove11`, `Rn.RnThMoveM` and `Rn.RnEQhi2`** (each under `L(ω+1) ≤ ν_C`). -/
theorem snRoadL (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (hat : Nc.ncL S (ω + 1) ≤ nuC → SnAtMove11 S)
    (hM : Nc.ncL S (ω + 1) ≤ nuC → RnThMoveM S) (hhi : Nc.ncL S (ω + 1) ≤ nuC → RnEQhi2 S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  rwRoadL hU hO hL hV hN hlh (fun hν => snAtMove10_of11 (hat hν)) hM hhi

/-- **Satisfiability**: the hypothesis of `snRoadL` follows from that of `Rw.rwRoadL`. -/
theorem snRoadL_hyps (hat : Nc.ncL S (ω + 1) ≤ nuC → RwAtMove10 S) :
    Nc.ncL S (ω + 1) ≤ nuC → SnAtMove11 S :=
  fun hν => snAtMove11_of10 (hat hν)

end Googology.Trans.PoR.InaccPsi.R2.Sn

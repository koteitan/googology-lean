import Googology.Trans.PoR.InaccPsi.R2.SqSh

/-!
# The atoms below `ψ_{Ω₂}(W^{ε+Ω₂})` move, and the road with the atoms in `[ψ_{Ω₂}(W^{ε+Ω₂}), θ]`

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `ε = ε_{Ω₂+1}`, `ε̂ = ε_{Ω₁+1}`,
`F_ε = ψ_{Ω₂}(ε)`, `T_{ε+Ω₂}(0) = ψ_{Ω₂}(W^{ε+Ω₂})`, `θ⁺ = Lj.ljThP`.

* `sqB_eps`, `sqB_epsH` (**`B_n ε = ε`, `B_n ε̂ = ε̂`**, by `Mw.mwB_phi`);
* `sqShE_B` (**the hypothesis `hShB` of `Rw.rwDigMove` for the family `sqShE`**);
* `sqAtMoveE` (**every atom `ψ_{Ω₂}(0) < s < T_{ε+Ω₂}(0)` moves** once the codes below it move: `B_n s` is an
  atom at `λ'`, `B_n s < θ⁺`, `Θ_λ s < c_{n+1}`, `Θ_{λ'}(B_n s) = B_n(Θ_λ s)`; no extra hypothesis; this
  contains `Sn.snAtMoveG` and the atom `F_ε` itself);
* `SqAtMove12 S` (a hypothesis name): `Lj.LjAtMove` for the atoms `T_{ε+Ω₂}(0) ≤ s ≤ θ`;
  `sqAtMove11_of12` (**`SqAtMove12` gives `Sn.SnAtMove11`**), `sqAtMove12_of11` (the converse), `sqRoadL`
  (**the road**), `sqRoadL_hyps`.

No new axiom.  New definition: the hypothesis name `SqAtMove12`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Lj Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sn

variable {S : InaccSeq.{0}}

theorem sqD_one : MvD S (1 : Ordinal.{0}) :=
  mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))

/-- **`B_n(ε_{κ+1}) = ε_{κ+1}`** for `κ` fixed by `B_n` in the domain, `SC κ`. -/
theorem sqB_epsK {n : ℕ} {κ : Ordinal.{0}} (hκ : SC κ) (hD : MvD S κ) (hB : Bc.bcB S n κ = κ) :
    MvD S (veblen 1 (κ + 1)) ∧ Bc.bcB S n (veblen 1 (κ + 1)) = veblen 1 (κ + 1) := by
  obtain ⟨hD21, hB21⟩ := mvB_add (k := n) hD (sqD_one (S := S))
  rw [hB, mwB_one] at hB21
  have h1ε : (1 : Ordinal.{0}) < veblen 1 (κ + 1) := (gg_one_lt_of_SC hκ).trans sqK_lt_eps
  obtain ⟨hDv, hBv⟩ := mwB_phi (k := n) (sqD_one (S := S)) hD21 h1ε (Ph.ph_veblen_prin 1 _ sqK_lt_eps h1ε)
  rw [mwB_one, hB21] at hBv
  exact ⟨hDv, hBv⟩

theorem sqB_eps {n : ℕ} : MvD S (veblen 1 (Om (1 + 1) + 1)) ∧
    Bc.bcB S n (veblen 1 (Om (1 + 1) + 1)) = veblen 1 (Om (1 + 1) + 1) :=
  sqB_epsK ldOm2_SC (ldOm2_D (k := n)).1 (ldOm2_D (k := n)).2

theorem sqB_epsH {n : ℕ} : MvD S (veblen 1 (Om 1 + 1)) ∧
    Bc.bcB S n (veblen 1 (Om 1 + 1)) = veblen 1 (Om 1 + 1) :=
  sqB_epsK Ph.ph_SC_Om1 (mvB_Om1 (k := n)).1 (mvB_Om1 (k := n)).2

section Main

variable {n : ℕ} {l l' ηx ηx' : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hl' : IsRestartIdx l') (hX' : upsilon l' < Pv S ηx')

include hl hX hl' hX'

/-- **The hypothesis `hShB` of `Rw.rwDigMove` for the family `sqShE`.** -/
theorem sqShE_B : ∀ b X Xh, sqShE S l b X Xh → MvD S b → b ∈ S.CSet b (S.psi b (Om (1 + 1))) →
    (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (b + leWe X) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
    Xh ≠ 0 ∧ ∃ XB XhB, sqShE S l' (Bc.bcB S n b) XB XhB ∧ MvD S (Om (1 + 1) * X) ∧
      Bc.bcB S n (Om (1 + 1) * X) = Om (1 + 1) * XB ∧
      MvD S (Om 1 * Xh) ∧ Bc.bcB S n (Om 1 * Xh) = Om 1 * XhB := by
  rintro b X Xh (h | ⟨rfl, rfl⟩) hDb hbo IH
  · obtain ⟨hne, XB, XhB, hF, h3, h4, h5, h6⟩ := snShG_B hl hX hl' hX' b X Xh h hDb hbo IH
    exact ⟨hne, XB, XhB, Or.inl hF, h3, h4, h5, h6⟩
  · refine ⟨veblen_pos.ne', _, _, Or.inr ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
    · rw [sqK_mul_eps ldOm2_SC]; exact (sqB_eps (n := n)).1
    · rw [sqK_mul_eps ldOm2_SC]; exact (sqB_eps (n := n)).2
    · rw [sqK_mul_eps Ph.ph_SC_Om1]; exact (sqB_epsH (n := n)).1
    · rw [sqK_mul_eps Ph.ph_SC_Om1]; exact (sqB_epsH (n := n)).2

end Main

/-- **Every atom `ψ_{Ω₂}(0) < s < ψ_{Ω₂}(W^{ε+Ω₂})` moves** once the codes below it move. -/
theorem sqAtMoveE {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
    (s : Ordinal.{0}) (hs : s ∈ ldAtR S l) (hs0 : S.psi 0 (Om (1 + 1)) < s)
    (hsT : s < leTe S (veblen 1 (Om (1 + 1) + 1) + Om (1 + 1)) 0)
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
  have hD1 : MvD S (1 : Ordinal.{0}) := sqD_one
  have hSh := sqShE_sh (S := S) hl hX
  have hSh' := sqShE_sh (S := S) hl' hX'
  rcases sqRepE hl hX hA hρ s hs hsT with hle | ⟨X, e, c, v, hXs, hown, hb, rfl⟩
  · exact absurd hs0 (not_lt.2 hle)
  obtain ⟨e1, own1, -, hv⟩ := sqReadE hl hX hA hρ hown hb
  obtain ⟨hDe, hDc, -, -, hDv, XB, hDX, hBX, hown'⟩ := rwDigMove (n := n) (l' := l') hl hX hSh
    (sqShE_B hl hX hl' hX') hown hb hD0 (fun x hx hxs => by
      obtain ⟨a, b, -, d, e⟩ := IH x hx (by rwa [zero_add] at hxs)
      exact ⟨a, b, d, e⟩)
  rw [Bc.bcB_zero] at hown'
  have hXs' : X = 0 ∨ ∃ Xh, RvSh S l 0 X Xh := by
    rcases hXs with h0 | ⟨Xh, h⟩
    · exact Or.inl h0
    · exact Or.inr ⟨Xh, (hSh _ _ _ h).1⟩
  have hXBs : XB = 0 ∨ ∃ Xh, sqShE S l' 0 XB Xh := rwOwn_sh hown'
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

/-- `ψ_{Ω₂}(ε) < ψ_{Ω₂}(W^{ε+Ω₂})`. -/
theorem sqFeps_lt_T :
    S.psi (veblen 1 (Om (1 + 1) + 1)) (Om (1 + 1)) < leTe S (veblen 1 (Om (1 + 1) + 1) + Om (1 + 1)) 0 := by
  unfold leTe
  rw [zero_add]
  refine psi_lt_psi_of_mem (InR_Om_succ 1) ?_ sqEps_mem
  conv_lhs => rw [← sqEps_We]
  exact leWe_lt (lt_add_of_pos_right _ ldOm2_SC.1)

/-- **`LjAtMove` for the atoms `ψ_{Ω₂}(W^{ε+Ω₂}) ≤ s ≤ θ`.** -/
def SqAtMove12 (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    leFWW S ≤ cdCode S l → cdCode S l < ljThP S →
    ∀ s ∈ ldAtR S l, leTe S (veblen 1 (Om (1 + 1) + 1) + Om (1 + 1)) 0 ≤ s → s ≤ ConjT.th S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)

/-- **`SqAtMove12` gives `Sn.SnAtMove11`.** -/
theorem sqAtMove11_of12 (h : SqAtMove12 S) : SnAtMove11 S := by
  intro n l l' hR h1 hr hl' hB hm hF hK s hs hsF hsθ IH
  rcases lt_or_ge s (leTe S (veblen 1 (Om (1 + 1) + 1) + Om (1 + 1)) 0) with hlt | hge
  · have hs0 : S.psi 0 (Om (1 + 1)) < s := by
      refine lt_of_lt_of_le ?_ hsF
      exact psi_lt_psi_of_mem (InR_Om_succ 1) (veblen_pos) (CSet.zero_mem _ _)
    exact sqAtMoveE hR h1 hr hl' hB s hs hs0 hlt IH
  · exact h n l l' hR h1 hr hl' hB hm hF hK s hs hge hsθ IH

/-- **`Sn.SnAtMove11` gives `SqAtMove12`.** -/
theorem sqAtMove12_of11 (h : SnAtMove11 S) : SqAtMove12 S :=
  fun n l l' hR h1 hr hl' hB hm hF hK s hs hsT hsθ IH =>
    h n l l' hR h1 hr hl' hB hm hF hK s hs (sqFeps_lt_T.le.trans hsT) hsθ IH

/-- **The road with `SqAtMove12`, `Rn.RnThMoveM` and `Rn.RnEQhi2`** (each under `L(ω+1) ≤ ν_C`). -/
theorem sqRoadL (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (hat : Nc.ncL S (ω + 1) ≤ nuC → SqAtMove12 S)
    (hM : Nc.ncL S (ω + 1) ≤ nuC → RnThMoveM S) (hhi : Nc.ncL S (ω + 1) ≤ nuC → RnEQhi2 S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  snRoadL hU hO hL hV hN hlh (fun hν => sqAtMove11_of12 (hat hν)) hM hhi

/-- **Satisfiability**: the hypothesis of `sqRoadL` follows from that of `Sn.snRoadL`. -/
theorem sqRoadL_hyps (hat : Nc.ncL S (ω + 1) ≤ nuC → SnAtMove11 S) :
    Nc.ncL S (ω + 1) ≤ nuC → SqAtMove12 S :=
  fun hν => sqAtMove12_of11 (hat hν)

end Googology.Trans.PoR.InaccPsi.R2.Sq

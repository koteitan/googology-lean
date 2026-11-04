import Googology.Trans.PoR.InaccPsi.R2.ZjRo
import Googology.Trans.PoR.InaccPsi.R2.RwAt2

/-!
# The code-level shifts over the base `Ω_ω`: the atoms below `F₂^ω = ψ_{Ω₂}(Ω_ω + Ω₂^{Ω₂^{Ω₂}})` move

`B_n = Bc.bcB S n`, `Θ = gxTh ρ_λ (ldAtR λ)`, `A = A_{η_λ}`, `θ = ψ_{Ω₂}(Ω_ω)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`,
`T_E(β) = ψ_{Ω₂}(β + W^E)`, `EX_j = Rw.rwEX S 0 Ω_ω j` (`EX_0 = Ω₁`, `EX_{j+1} = ψ_{Ω₂}(Ω_ω + W^{W^{EX_j}})`),
`F₂^ω = T_{W^W}(Ω_ω)`, the family `Rw.rwShG S λ Ω_ω` (shifts with code exponents, own relative to `Ω_ω`).

* `zjWW_eq` (`W^{W^W} = ω^{W^W}`), `zjB_WW`, `zjB_F2` (**`B_n` fixes `W^W`, `F₂^ω`**);
* `zjEX_code` (**every `EX_j` is a code with `Θ(EX_j) < Ω₁`**: `Rw.rwLevC_all` at the base `Ω_ω`),
  `zjClsG_top` (**the atoms below `F₂^ω` are own over `Ω_ω`** (`Rw.RwClsAt`): `Rw.rwEX_sup`,
  `Rw.rwClsLevG_all` at the base `Ω_ω`), `zjRepG`, `zjReadG` (**`Θ(ψ_{Ω₂}(Ω_ω + c)) = ψ_{Ω₁}(A + θ + v)`**);
* `zjAtMoveG` (**every atom `θ < s < F₂^ω` moves** once the codes below it move: `Rw.rwDigMove` with
  `Rw.rwShG_B`, the shift moving with `B_n`), `zjMoveG` (**THE READING MOVE AT THE CODES `θ⁺ ≤ m_λ < F₂^ω`**, from
  `Wr.WrWallCF`);
* `ZjTopG S` (**the reading move at every window code `m_λ ≥ F₂^ω`**, the new leaf), `zjTopK_ofG` (**`WrWallCF ∧
  ZjTopG ⇒ Xs.XsTopK`**), `zjTopG_of_xs`, `zjTopG_of_target` (**NON-VACUITY**), `zjTopK_iffG`.

No new axiom.  New definition: the statement name `ZjTopG`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Mv
  Googology.Trans.PoR.InaccPsi.R2.Lj Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rq
  Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw

variable {S : InaccSeq.{0}}

/-! ## `F₂^ω` and its fixed point -/

/-- `W^{W^W} = ω^{W^W}` (`Ω₂·W^W = W^W`). -/
theorem zjWW_eq : leWe (leWe (Om (1 + 1 : Ordinal.{0}))) = ω ^ leWe (Om (1 + 1 : Ordinal.{0})) := by
  have hW : Om (1 + 1 : Ordinal.{0}) = ω ^ Om (1 + 1) := (gg_SC_eps ldOm2_SC).symm
  have hωW : ω ≤ Om (1 + 1 : Ordinal.{0}) := (Lw.lw_omega_lt_SC ldOm2_SC).le
  have e : Om (1 + 1 : Ordinal.{0}) * leWe (Om (1 + 1)) = leWe (Om (1 + 1)) := by
    unfold leWe
    calc Om (1 + 1 : Ordinal.{0}) * ω ^ (Om (1 + 1) * Om (1 + 1))
        = ω ^ Om (1 + 1) * ω ^ (Om (1 + 1) * Om (1 + 1)) := by rw [← hW]
      _ = ω ^ (Om (1 + 1) + Om (1 + 1) * Om (1 + 1)) := (opow_add _ _ _).symm
      _ = ω ^ (Om (1 + 1) * Om (1 + 1)) := by rw [← mul_one_add, Ordinal.one_add_of_omega0_le hωW]
  show ω ^ (Om (1 + 1) * leWe (Om (1 + 1))) = _
  rw [e]

/-- `B_n(W^W) = W^W`. -/
theorem zjB_WW {n : ℕ} : MvD S (leWe (Om (1 + 1 : Ordinal.{0}))) ∧
    Bc.bcB S n (leWe (Om (1 + 1 : Ordinal.{0}))) = leWe (Om (1 + 1)) := by
  obtain ⟨hD2, hB2⟩ := zjB_W2 (S := S) (n := n)
  obtain ⟨hDo, hBo⟩ := ldB_opow (n := n) hD2
  rw [hB2] at hBo
  exact ⟨hDo, hBo⟩

/-- `B_n(F₂^ω) = F₂^ω`. -/
theorem zjB_F2 {n : ℕ} : MvD S (S.psi (Om ω + leWe (leWe (Om (1 + 1)))) (Om (1 + 1))) ∧
    Bc.bcB S n (S.psi (Om ω + leWe (leWe (Om (1 + 1)))) (Om (1 + 1))) =
      S.psi (Om ω + leWe (leWe (Om (1 + 1)))) (Om (1 + 1)) := by
  obtain ⟨hDW, hBW⟩ := Wr.wrB_OmW (S := S) (n := n)
  obtain ⟨hDWW, hBWW⟩ := zjB_WW (S := S) (n := n)
  have h3 : MvD S (leWe (leWe (Om (1 + 1 : Ordinal.{0})))) ∧
      Bc.bcB S n (leWe (leWe (Om (1 + 1 : Ordinal.{0})))) = leWe (leWe (Om (1 + 1))) := by
    rw [zjWW_eq]
    obtain ⟨hDo, hBo⟩ := ldB_opow (n := n) hDWW
    rw [hBWW] at hBo
    exact ⟨hDo, hBo⟩
  obtain ⟨hDa, hBa⟩ := mvB_add (k := n) hDW h3.1
  obtain ⟨hDs, hBs⟩ := mxB_atom (n := n) hDa
    (CSet.add_mem (zjOmW_own _) (leWe_mem (leWe_mem (mxOm2_mem _ _))))
  exact ⟨hDs, by rw [hBs, hBa, hBW, h3.2]⟩

theorem zjWW_lt_OmW : leWe (leWe (Om (1 + 1 : Ordinal.{0}))) < Om ω :=
  roWe_lt_OmW (roWe_lt_OmW ldOm2_lt_OmW)

theorem zjF2_le_Pp : S.psi (Om ω + leWe (leWe (Om (1 + 1)))) (Om (1 + 1)) ≤ Nc.ncPp S :=
  (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left _).2 zjWW_lt_OmW.le)).1

theorem zjT_le_F2 : rnTW S (Om ω) ≤ S.psi (Om ω + leWe (leWe (Om (1 + 1)))) (Om (1 + 1)) := by
  refine (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left _).2 (leWe_mono ?_))).1
  have h : Om (1 + 1 : Ordinal.{0}) ≤ ω ^ Om (1 + 1) := (gg_SC_eps ldOm2_SC).ge
  unfold leWe
  exact h.trans (opow_le_opow_right omega0_pos (le_mul_left _ ldOm2_SC.1))

theorem zjX_W {l b X : Ordinal.{0}} (h : X = 0 ∨ ∃ Xh, RvSh S l b X Xh) : X + Om (1 + 1) < Om ω := by
  rcases h with rfl | ⟨Xh, h⟩
  · rw [zero_add]; exact ldOm2_lt_OmW
  · exact h.ltG3.trans rwG3_lt_OmW

/-! ## The own atoms over `Ω_ω` -/

section Read

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hown : ConjT.Aη S (cdEta S l) ∈
    S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)))
  (hAW : Om ω + Om ω ≤ ConjT.Aη S (cdEta S l))

include hl hX hown hAW

theorem zjRd : RwRd S l (Om ω) := ⟨_, zjHat hl hX hown hAW, zjBase0 hl hX hown hAW⟩

/-- **`EX_j = rwEX S 0 Ω_ω j` is a code with `Θ(EX_j) < Ω₁`.** -/
theorem zjEX_code : ∀ j, GxCl (upsilon l) (ldAtR S l) (rwEX S 0 (Om ω) j) ∧
    gxTh (upsilon l) (ldAtR S l) (rwEX S 0 (Om ω) j) < Om 1 := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hG3 := rwG3_SC (S := S)
  have hWG3 := rwW_lt_G3 (S := S)
  have hG1 := rwG_SC (S := S)
  have hΩG1 := rwO_lt_G (S := S)
  have hown0 : ∀ d, d ≤ leWe ((0 : Ordinal.{0}) + leWe (Om (1 + 1))) →
      Om ω ∈ S.CSet (Om ω + d) (S.psi (Om ω + d) (Om (1 + 1))) := fun d _ => zjOmW_own d
  have hX0m : (0 : Ordinal.{0}) ∈ S.CSet 0 (S.psi (Om ω + leWe 0) (Om (1 + 1))) := CSet.zero_mem _ _
  intro j
  induction j with
  | zero =>
    refine ⟨GxCl.om, ?_⟩
    change gxTh (upsilon l) (ldAtR S l) (Om 1) < Om 1
    rw [gxTh_Om1 hρSC hρ1 hAt]; exact hρ1
  | succ j IHj =>
    obtain ⟨hc, hΘ⟩ := IHj
    have hjW : rwEX S 0 (Om ω) j < Om (1 + 1) := rwEX_lt_Om2 j
    have hjH : rwEX S 0 (Om ω) j ∈ cdHull S l := (ldHull_iff hl hX hjW).2 hc
    have hj1 : 1 ≤ rwEX S 0 (Om ω) j := Order.one_le_iff_pos.2 (rwEX_SC j).1
    have hWj : leWe (rwEX S 0 (Om ω) j) < Om ω := roWe_lt_OmW (hjW.trans ldOm2_lt_OmW)
    have hWj0 : (0 : Ordinal.{0}) + leWe (rwEX S 0 (Om ω) j) < Om ω := by rw [zero_add]; exact hWj
    have hat : rwEX S 0 (Om ω) (j + 1) ∈ ldAtR S l :=
      ⟨Om ω + leWe (0 + leWe (rwEX S 0 (Om ω) j)), CSet.add_mem (ConjT.OmW_mem (S := S) _ _)
        (leWe_mem (CSet.add_mem (CSet.zero_mem _ _) (leWe_mem hjH))),
        ((add_lt_add_iff_left _).2 (roWe_lt_OmW hWj0)).trans_le hAW, rfl⟩
    refine ⟨GxCl.atom hat, ?_⟩
    obtain ⟨-, t2, -, t4⟩ := rwTermC_lt (S := S) (ζ := 0) (z := 0) hjW ldOm2_SC.1 hΘ (Om_pos one_ne_zero)
    have ht := rwLevC_all hl hX _ hc hj1 hjW (Om ω) 0 0 (Or.inl ⟨rfl, rfl⟩) (dvd_zero _)
      (by rw [zero_add]; exact hG3.isPrincipal ((leWe_mono le_self_add).trans_lt t2) hWG3)
      (by rw [zero_add]; exact hG1.isPrincipal ((leOe_mono le_self_add).trans_lt t4) hΩG1)
      ⟨j + 1, rwEX_lt_succ hown0 hX0m j⟩
    have hb : RoBaseE S l (0 + leWe (rwEX S 0 (Om ω) j)) 0 (Om ω) := zjBaseX hAW hWj0
    have e1 := ht (Om ω) _ hb le_rfl (zjHat hl hX hown hAW) (zjBase0 hl hX hown hAW)
    have e2 : leTe S (0 + leWe (rwEX S 0 (Om ω) j) + 0) (Om ω) = rwEX S 0 (Om ω) (j + 1) := by
      rw [add_zero]; rfl
    rw [e2] at e1
    rw [e1]; exact psi_lt Low.InR_Om_one _

/-- **The atoms below `F₂^ω = T_{W^W}(Ω_ω)` are own over `Ω_ω`.** -/
theorem zjClsG_top : RwClsAt S l (rwShG S l) (leWe (Om (1 + 1))) 0 (Om ω) := by
  have hWW : leWe (Om (1 + 1 : Ordinal.{0})) < Om ω := roWe_lt_OmW ldOm2_lt_OmW
  have hG3 := rwG3_SC (S := S)
  have hWG3 := rwW_lt_G3 (S := S)
  have hb : RoBaseE S l (leWe (Om (1 + 1))) 0 (Om ω) := zjBaseX hAW hWW
  have hown0 : ∀ d, d ≤ leWe ((0 : Ordinal.{0}) + leWe (Om (1 + 1))) →
      Om ω ∈ S.CSet (Om ω + d) (S.psi (Om ω + d) (Om (1 + 1))) := fun d _ => zjOmW_own d
  have hX0m : (0 : Ordinal.{0}) ∈ S.CSet 0 (S.psi (Om ω + leWe 0) (Om (1 + 1))) := CSet.zero_mem _ _
  have hWWG3 : (0 : Ordinal.{0}) + leWe (Om (1 + 1)) < S.psi 0 (Om (1 + 1 + 1)) := by
    rw [zero_add]; exact (leWe_lt_SC hG3 hWG3 hWG3).1
  have hβd : leWe ((0 : Ordinal.{0}) + leWe (Om (1 + 1))) ∣ Om ω := by
    rw [zero_add]; exact zjWX_dvd hWW
  have hrd := zjRd hl hX hown hAW
  intro t ht htT
  rw [add_zero] at htT
  have htT0 : t < leTe S (0 + leWe (Om (1 + 1))) (Om ω) := by rwa [zero_add]
  obtain ⟨j, hj⟩ := rwEX_sup hown0 hX0m hβd (fun Q hQ _ => LeCl.zero hQ.1) hWWG3 htT0
  rcases j with _ | i
  · exact Or.inl (hj.trans (psiS_bounds (S := S) (Om ω) 1).1).le
  obtain ⟨hic, hiΘ⟩ := zjEX_code hl hX hown hAW i
  have hiW : rwEX S 0 (Om ω) i < Om (1 + 1) := rwEX_lt_Om2 i
  have hi1 : 1 ≤ rwEX S 0 (Om ω) i := Order.one_le_iff_pos.2 (rwEX_SC i).1
  have hcls := rwClsLevG_all hl hX _ hic hi1 hiW hiΘ (Om ω) 0 0 (Or.inl ⟨rfl, rfl⟩)
    ⟨i + 1, rwEX_lt_succ hown0 hX0m i⟩ (Om ω) le_rfl
  have hle : (0 : Ordinal.{0}) + leWe (rwEX S 0 (Om ω) i) + Om (1 + 1) ≤ leWe (Om (1 + 1)) := by
    rw [zero_add]
    calc leWe (rwEX S 0 (Om ω) i) + Om (1 + 1) ≤ leWe (rwEX S 0 (Om ω) i) * 1 + Om (1 + 1) := by rw [mul_one]
      _ ≤ leWe (rwEX S 0 (Om ω) i + 1) := rwStep_le hi1 (one_lt_omega0.trans (Lw.lw_omega_lt_SC ldOm2_SC))
      _ ≤ leWe (Om (1 + 1)) := leWe_mono (Order.add_one_le_of_lt hiW)
  have hsb : RoBaseE S l (0 + leWe (rwEX S 0 (Om ω) i)) 0 (Om ω) :=
    roBaseE_shift hb (by rw [add_zero]; exact le_self_add.trans hle) zero_le
  have htT' : t < leTe S (0 + leWe (rwEX S 0 (Om ω) i) + 0) (Om ω) := by rw [add_zero]; exact hj
  rcases hcls hsb hrd t ht htT' with h | ⟨X', e', c, v, hcond, hownc, hbo, e1⟩
  · exact Or.inl h
  · refine Or.inr ⟨X', e', c, v, Or.inr ?_, hownc, hbo, e1⟩
    rcases hcond with ⟨rfl, h2⟩ | ⟨h1, h2⟩
    · exact ⟨hle, (h2.trans zero_le.ge).trans_lt ((Om_pos one_ne_zero).trans (leOm1_lt_Te _ _))⟩
    · exact ⟨h1.trans (le_self_add.trans hle), h2⟩

/-- **Every atom `θ < s < F₂^ω` is `ψ_{Ω₂}(Ω_ω + c)` with `(X, e, c, v)` own over `Ω_ω` (family `rwShG`).** -/
theorem zjRepG (s : Ordinal.{0}) (hs : s ∈ ldAtR S l) (hθs : ConjT.th S < s)
    (hsW : s < S.psi (Om ω + leWe (leWe (Om (1 + 1)))) (Om (1 + 1))) :
    ∃ X e c v, (X = 0 ∨ ∃ Xh, rwShG S l (Om ω) X Xh) ∧
      RwOwn S l (rwShG S l) X e (Om ω) c v ∧ RoBaseE S l X e (Om ω) ∧ s = S.psi (Om ω + c) (Om (1 + 1)) := by
  have hT : s < leTe S (leWe (Om (1 + 1)) + 0) (Om ω) := by unfold leTe; rwa [add_zero]
  rcases zjClsG_top hl hX hown hAW s hs hT with h | ⟨X, e, c, v, -, hownc, hb, e1⟩
  · exact absurd hθs (not_lt.2 h)
  · exact ⟨X, e, c, v, rwOwn_sh hownc, hownc, hb, e1⟩

/-- **`Θ(ψ_{Ω₂}(Ω_ω + c)) = ψ_{Ω₁}(A + θ + v)`** for every own `(X, e, c, v)` over `Ω_ω` (family `rwShG`). -/
theorem zjReadG {X e c v : Ordinal.{0}} (hownc : RwOwn S l (rwShG S l) X e (Om ω) c v)
    (hb : RoBaseE S l X e (Om ω)) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (Om ω + c) (Om (1 + 1))) =
        S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + v) (Om 1) ∧
      ConjT.Aη S (cdEta S l) + ConjT.th S + v ∈ S.CSet (ConjT.Aη S (cdEta S l) + ConjT.th S + v)
        (S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + v) (Om 1)) ∧ c < leWe (X + e) ∧
      v < S.psi 0 (Om (1 + 1)) :=
  rwOwnRead hl hX (rwShG_sh hl hX) hownc _ hb (zjHat hl hX hown hAW) (zjBase0 hl hX hown hAW)

end Read

/-- **Every atom `θ < s < F₂^ω` moves** once the codes below it move. -/
theorem zjAtMoveG : ZjAtK S (S.psi (Om ω + leWe (leWe (Om (1 + 1)))) (Om (1 + 1))) := by
  intro n l l' hR h1 hr hl' hB s hs hθs hsK IH
  have hl := hR.1
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  obtain ⟨hX, hX', hown, hown', -, -, -, -, hBψ⟩ := Wr.wrWin hR h1 hr hl' hB
  obtain ⟨hAW, hAW'⟩ := zjWin_A hR h1 hr hl' hB
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hSh := rwShG_sh (S := S) hl hX
  have hSh' := rwShG_sh (S := S) hl' hX'
  rcases zjRepG hl hX hown hAW s hs hθs hsK with ⟨X, e, c, v, hXs, hownc, hb, rfl⟩
  obtain ⟨e1, own1, -, hv⟩ := zjReadG hl hX hown hAW hownc hb
  obtain ⟨hDW, hBW⟩ := Wr.wrB_OmW (S := S) (n := n)
  obtain ⟨hDe, hDc, hDs, hBs, hDv, XB, hDX, hBX, hBown⟩ := rwDigMove (n := n) (l' := l') hl hX hSh
    (rwShG_B hl hX) hownc hb hDW (fun x hx hxs => by
      obtain ⟨a, b, -, d, e⟩ := IH x hx hxs
      exact ⟨a, b, d, e⟩)
  rw [hBW] at hBown hBs
  have hXs' : X = 0 ∨ ∃ Xh, RvSh S l (Om ω) X Xh := by
    rcases hXs with h0 | ⟨Xh, h⟩
    · exact Or.inl h0
    · exact Or.inr ⟨Xh, (hSh _ _ _ h).1⟩
  have hXBs : XB = 0 ∨ ∃ Xh, rwShG S l' (Om ω) XB Xh := rwOwn_sh hBown
  have hXBs' : XB = 0 ∨ ∃ Xh, RvSh S l' (Om ω) XB Xh := by
    rcases hXBs with h0 | ⟨Xh, h⟩
    · exact Or.inl h0
    · exact Or.inr ⟨Xh, (hSh' _ _ _ h).1⟩
  have hec := rwOwn_code hl hX hownc
  have heW := roGx_lt_Om2 hρ1 hec
  have heT : e < leTe S (X + Om (1 + 1)) (Om ω) := by
    refine (hb.2.2.2.2 e hec le_rfl).trans_le ?_
    exact (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left _).2
      (leWe_mono ((add_le_add_iff_left X).2 heW.le)))).1
  obtain ⟨hDWW, hBWW⟩ := rqB_WeW (S := S) (n := n) hDX hBX
  obtain ⟨hDaW, hBaW⟩ := mvB_add (k := n) hDW hDWW
  rw [hBW, hBWW] at hBaW
  have hXC : X ∈ S.CSet (Om ω + leWe (X + Om (1 + 1))) (S.psi (Om ω + leWe (X + Om (1 + 1))) (Om (1 + 1))) := by
    rcases hXs' with rfl | ⟨Xh, hs'⟩
    · exact CSet.zero_mem _ _
    · exact rvMem hs' (rvWX_le le_rfl X _) le_rfl
  have hTown : Om ω + leWe (X + Om (1 + 1)) ∈ S.CSet (Om ω + leWe (X + Om (1 + 1)))
      (S.psi (Om ω + leWe (X + Om (1 + 1))) (Om (1 + 1))) :=
    CSet.add_mem (zjOmW_own _) (leWe_mem (CSet.add_mem hXC (mxOm2_mem _ _)))
  obtain ⟨hDT, hBT⟩ := mxB_atom (n := n) hDaW hTown
  rw [hBaW] at hBT
  have hBeT : Bc.bcB S n e < leTe S (XB + Om (1 + 1)) (Om ω) := by
    have h := (mvB_lt_iff (k := n) hDe hDT).2 heT
    unfold leTe at h ⊢; rwa [hBT] at h
  have hb' : RoBaseE S l' XB (Bc.bcB S n e) (Om ω) :=
    rwBase_lower hXBs' le_rfl (zjBaseX hAW' (zjX_W hXBs')) le_rfl hBeT
  obtain ⟨e1', -, -, -⟩ := zjReadG hl' hX' hown' hAW' hBown hb'
  have hcown := rwOwn_own hl hX hSh hownc hb
  obtain ⟨hDa, hBa⟩ := mxB_atom (n := n) hDs hcown
  obtain ⟨hBH, hBA⟩ := rwOwn_mem hl' hX' hSh' hBown hb'
  obtain ⟨hDF, hBF⟩ := zjB_F2 (S := S) (n := n)
  have hvθ : v < ConjT.th S := hv.trans_le rnG_le_th
  have hdθ := zjTh_add_le hvθ
  obtain ⟨hDθ, hBθ⟩ := ljB_th (S := S) (n := n)
  obtain ⟨hDd, hBd⟩ := mvB_add (k := n) hDθ hDv
  have hownd : ConjT.Aη S (cdEta S l) + (ConjT.th S + v) ∈ S.CSet (ConjT.Aη S (cdEta S l) + (ConjT.th S + v))
      (S.psi (ConjT.Aη S (cdEta S l) + (ConjT.th S + v)) (Om 1)) := by
    rw [← add_assoc]; exact own1
  have hbd : S.psi (ConjT.Aη S (cdEta S l) + (ConjT.th S + v)) (Om 1) < Bc.bcC S (n + 1) :=
    (Xs.xsLt_delta hl hX hdθ).trans hδr
  refine ⟨hDa, ?_, ?_, ?_, ?_⟩
  · rw [hBa, hBs]; exact ⟨_, hBH, hBA, rfl⟩
  · have h := (mvB_lt_iff (k := n) hDa hDF).2 hsK
    rwa [hBF] at h
  · rw [e1, add_assoc]; exact hbd
  · rw [hBa, hBs, e1', e1, add_assoc (ConjT.Aη S (cdEta S l)), hBψ _ hDd hownd hbd, hBd, hBθ, add_assoc]

/-- **THE READING MOVE AT THE CODES `θ⁺ ≤ m_λ < F₂^ω`**, from the code-free wall. -/
theorem zjMoveG (hW : Wr.WrWallCF S) : ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l →
    cdR S l < Bc.bcC S (n + 1) → IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
    ljThP S ≤ cdCode S l → cdCode S l < S.psi (Om ω + leWe (leWe (Om (1 + 1)))) (Om (1 + 1)) →
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l') :=
  zjMoveGen hW (SC_psi (InR_Om_succ 1) _) (zjThP_le_T.trans zjT_le_F2) zjF2_le_Pp zjAtMoveG

/-! ## The top: the codes `≥ F₂^ω` -/

/-- **The reading move at every window code `m_λ ≥ F₂^ω = ψ_{Ω₂}(Ω_ω + Ω₂^{Ω₂^{Ω₂}})`** (the new leaf). -/
def ZjTopG (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', R2Skel.SkEX.SkWin S n l l' →
    S.psi (Om ω + leWe (leWe (Om (1 + 1)))) (Om (1 + 1)) ≤ cdCode S l →
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l')

/-- **`WrWallCF ∧ ZjTopG ⇒ Xs.XsTopK`.** -/
theorem zjTopK_ofG (hW : Wr.WrWallCF S) (hT : ZjTopG S) : Xs.XsTopK S := by
  intro n l l' hW' hK
  by_cases hm : cdCode S l < S.psi (Om ω + leWe (leWe (Om (1 + 1)))) (Om (1 + 1))
  · obtain ⟨hR, h1, hr, hl', hB, -⟩ := hW'
    have hP : ljThP S ≤ cdCode S l := by
      refine rnThP_le_MW.trans ?_
      rw [← Xs.xsK_one]; exact hK 1
    exact zjMoveG hW n l l' hR h1 hr hl' hB hP hm
  · exact hT n l l' hW' (not_lt.1 hm)

/-- `XsTopK ⇒ ZjTopG` (`K_j < K_ω < T* ≤ F₂^ω`). -/
theorem zjTopG_of_xs (h : Xs.XsTopK S) : ZjTopG S := fun n l l' hW' hF =>
  h n l l' hW' fun j => ((zjK_lt_Kw j).trans zjKw_lt_T).le.trans (zjT_le_F2.trans hF)

/-- **NON-VACUITY**: `L(ω+1) ≤ ν_C ∧ CdEQ ∧ SkEX.SkKFar ⇒ ZjTopG` (the road's target gives the leaf). -/
theorem zjTopG_of_target (hν : Nc.ncL S (ω + 1) ≤ nuC) (hEQ : CdEQ S) (hK : R2Skel.SkEX.SkKFar S) :
    ZjTopG S :=
  zjTopG_of_xs (Xs.xsTopK_of_target hν hEQ hK)

/-- **`XsTopK ⇔ ZjTopG`** under the wall. -/
theorem zjTopK_iffG (hW : Wr.WrWallCF S) : Xs.XsTopK S ↔ ZjTopG S :=
  ⟨zjTopG_of_xs, zjTopK_ofG hW⟩

end Googology.Trans.PoR.InaccPsi.R2.Zj

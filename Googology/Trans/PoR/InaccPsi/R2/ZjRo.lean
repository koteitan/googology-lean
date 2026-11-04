import Googology.Trans.PoR.InaccPsi.R2.ZjMove
import Googology.Trans.PoR.InaccPsi.R2.RoO

/-!
# The shifts `X = Ω₂·α` (`1 ≤ α < ω^ω`) over the base `Ω_ω`: the atoms below `ψ_{Ω₂}(Ω_ω + Ω₂^{Ω₂·ω^ω})` move

`B_n = Bc.bcB S n`, `Θ = gxTh ρ_λ (ldAtR λ)`, `A = A_{η_λ}`, `θ = ψ_{Ω₂}(Ω_ω)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`,
`F^ω_α = ψ_{Ω₂}(Ω_ω + W^{Ω₂·α})` (`F^ω_1 = T*`), `P′ = ψ_{Ω₂}(Ω_ω·2)`.

* `zjXW_le`, `zjWX_dvd` (`W^X ∣ Ω_ω` for `X < Ω_ω`), `zjBaseX`, `zjBaseXE` (**`Ω_ω` is a base of every shift
  `X < Ω_ω`** (`Ro.RoBaseE`) in a window);
* `zjTopO_read` (**`Θ(F^ω_α) = ψ_{Ω₁}(A + θ + Ω₁^{Ω₁·α})`**: `Ro.roTopO` at the base `Ω_ω`), `zjRepO` (**every atom
  `θ < s ≤ F^ω_α` is `ψ_{Ω₂}(Ω_ω + c)` with `(X, e, c, v)` own over `Ω_ω`**, `Ro.roClsO` at the base `Ω_ω`),
  `zjReadO` (**`Θ(ψ_{Ω₂}(Ω_ω + c)) = ψ_{Ω₁}(A + θ + v)`**, `v < ψ_{Ω₂}(0)`);
* `zjB_Fa` (`B_n F^ω_α = F^ω_α`), `zjAtMoveO` (**every atom `θ < s < F^ω_α` moves** once the codes below it move),
  `zjMoveO` (**THE READING MOVE AT THE CODES `θ⁺ ≤ m_λ < F^ω_α`**, every `1 ≤ α < ω^ω`, from `Wr.WrWallCF`);
* `ZjTopO S` (**the reading move at every window code `m_λ ≥ F^ω_α` for all `α < ω^ω`**, the new leaf),
  `zjTopK_ofO` (**`WrWallCF ∧ ZjTopO ⇒ Xs.XsTopK`**), `zjTopO_of_xs`, `zjTopO_of_target` (**NON-VACUITY**).

No new axiom.  New definition: the statement name `ZjTopO`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Mv
  Googology.Trans.PoR.InaccPsi.R2.Lj Googology.Trans.PoR.InaccPsi.R2.Ro

variable {S : InaccSeq.{0}}

/-- `W^X ∣ Ω_ω` for `X < Ω_ω`. -/
theorem zjWX_dvd {X : Ordinal.{0}} (hX : X < Om ω) : leWe X ∣ Om ω := by
  have h := roWe_lt_OmW hX
  unfold leWe at h ⊢
  conv_rhs => rw [← zjOmW_eq]
  conv_rhs at h => rw [← zjOmW_eq]
  exact opow_dvd_opow ω ((opow_lt_opow_iff_right one_lt_omega0).1 h).le

theorem zjOa_lt {α : Ordinal.{0}} (h1 : 1 ≤ α) (hα : α < ω ^ ω) : Om (1 + 1) * α + Om (1 + 1) < Om ω :=
  roShO_X ⟨α, h1, hα, rfl, rfl⟩

theorem zjOa_lt' {α : Ordinal.{0}} (h1 : 1 ≤ α) (hα : α < ω ^ ω) : Om (1 + 1) * α < Om ω :=
  (lt_add_of_pos_right _ ldOm2_SC.1).trans (zjOa_lt h1 hα)

section Read

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hown : ConjT.Aη S (cdEta S l) ∈
    S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)))
  (hAW : Om ω + Om ω ≤ ConjT.Aη S (cdEta S l))

include hAW

/-- **`Ω_ω` is a base of the shift `X` at the exponent `0`** for every `X < Ω_ω`. -/
theorem zjBaseX {X : Ordinal.{0}} (hXW : X < Om ω) : RoBaseE S l X 0 (Om ω) := by
  refine ⟨by rw [add_zero]; exact zjWX_dvd hXW, ConjT.OmW_mem (S := S) _ _, ?_, fun d _ => zjOmW_own d,
    fun e' _ h' => ?_⟩
  · rw [add_zero]; exact ((add_lt_add_iff_left _).2 (roWe_lt_OmW hXW)).trans_le hAW
  · obtain rfl : e' = 0 := le_antisymm h' zero_le
    exact (SC_psi (InR_Om_succ 1) _).1

/-- **`Ω_ω` is a base of the shift `X` at every exponent `e < T_{X+Ω₂}(Ω_ω)`.** -/
theorem zjBaseXE {X e : Ordinal.{0}} (hXs : X = 0 ∨ ∃ Xh, RoSh S X Xh) (hXW : X + Om (1 + 1) < Om ω)
    (he : e < leTe S (X + Om (1 + 1)) (Om ω)) : RoBaseE S l X e (Om ω) :=
  roBase_lower hXs (zjBaseX hAW hXW) le_rfl he

include hl hX hown

/-- **`Θ(F^ω_α) = ψ_{Ω₁}(A + θ + Ω₁^{Ω₁·α})`** for every `1 ≤ α < ω^ω`. -/
theorem zjTopO_read {α : Ordinal.{0}} (h1 : 1 ≤ α) (hα : α < ω ^ ω) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (Om ω + leWe (Om (1 + 1) * α)) (Om (1 + 1))) =
      S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + leOe (Om 1 * α)) (Om 1) := by
  have h := roTopO hl hX α h1 hα (Om ω) _ (zjBaseX hAW (zjOa_lt' h1 hα)) (zjHat hl hX hown hAW)
    (zjBase0 hl hX hown hAW)
  unfold leTe at h
  rwa [add_zero, gxTh_zero, add_zero] at h

/-- **Every atom `θ < s ≤ F^ω_α` is `ψ_{Ω₂}(Ω_ω + c)` with `(X, e, c, v)` own over `Ω_ω`.** -/
theorem zjRepO {α : Ordinal.{0}} (h1 : 1 ≤ α) (hα : α < ω ^ ω) (s : Ordinal.{0}) (hs : s ∈ ldAtR S l)
    (hθs : ConjT.th S < s) (hsα : s ≤ S.psi (Om ω + leWe (Om (1 + 1) * α)) (Om (1 + 1))) :
    ∃ X e c v, (X = 0 ∨ ∃ Xh, roShO X Xh) ∧ RoOwn S l roShO X e (Om ω) c v ∧
      RoBaseE S l X e (Om ω) ∧ s = S.psi (Om ω + c) (Om (1 + 1)) := by
  have hsh : roShO (Om (1 + 1) * α) (Om 1 * α) := ⟨α, h1, hα, rfl, rfl⟩
  have hαW := zjOa_lt' h1 hα
  rcases hsα.lt_or_eq with hlt | rfl
  · have hb := zjBaseX (l := l) hAW hαW
    have hlt' : s < leTe S (Om (1 + 1) * α + 0) (Om ω) := by
      unfold leTe; rwa [add_zero]
    rcases roClsO hl hX α h1 hα (Om ω) hb s hs hlt' with h | ⟨X', e', c, v, -, hownc, hbo, e1⟩
    · exact absurd hθs (not_lt.2 h)
    · exact ⟨X', e', c, v, roOwn_sh hownc, hownc, hbo, e1⟩
  · obtain ⟨hρSC, -⟩ := leRho hl hX
    have hc0 : GxCl (upsilon l) (ldAtR S l) (0 : Ordinal.{0}) := GxCl.zero hρSC.1
    have hc1 : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small (gg_one_lt_of_SC hρSC)
    have h1T : (1 : Ordinal.{0}) < leTe S (Om (1 + 1) * α + 0 + 1) (Om ω) := roOne_lt_Te _ _
    have hXW : Om (1 + 1) ≤ Om (1 + 1) * α := le_mul_left _ (Order.one_le_iff_pos.1 h1)
    have hownc := roTop_own (l := l) (Sh := roShO) hsh hXW hc0 hc1 one_ne_zero h1T
    have hb : RoBaseE S l (Om (1 + 1) * α) (0 + 1) (Om ω) := by
      refine zjBaseXE hAW (Or.inr ⟨_, roSh_o h1 hα⟩) (zjOa_lt h1 hα) ?_
      rw [zero_add]; exact roOne_lt_Te _ _
    refine ⟨_, _, _, _, Or.inr ⟨_, hsh⟩, hownc, hb, ?_⟩
    rw [add_zero, mul_one, add_zero]

/-- **`Θ(ψ_{Ω₂}(Ω_ω + c)) = ψ_{Ω₁}(A + θ + v)`** for every own `(X, e, c, v)` over `Ω_ω`. -/
theorem zjReadO {X e c v : Ordinal.{0}} (hownc : RoOwn S l roShO X e (Om ω) c v)
    (hb : RoBaseE S l X e (Om ω)) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (Om ω + c) (Om (1 + 1))) =
        S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + v) (Om 1) ∧
      ConjT.Aη S (cdEta S l) + ConjT.th S + v ∈ S.CSet (ConjT.Aη S (cdEta S l) + ConjT.th S + v)
        (S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + v) (Om 1)) ∧ v < S.psi 0 (Om (1 + 1)) := by
  obtain ⟨e1, own1, -, hv⟩ := roOwnRead hl hX (roShO_sh hl hX) hownc _ hb (zjHat hl hX hown hAW)
    (zjBase0 hl hX hown hAW)
  exact ⟨e1, own1, hv⟩

end Read

/-- `B_n(F^ω_α) = F^ω_α`. -/
theorem zjB_Fa {n : ℕ} {α : Ordinal.{0}} (h1 : 1 ≤ α) (hα : α < ω ^ ω) :
    MvD S (S.psi (Om ω + leWe (Om (1 + 1) * α)) (Om (1 + 1))) ∧
      Bc.bcB S n (S.psi (Om ω + leWe (Om (1 + 1) * α)) (Om (1 + 1))) =
        S.psi (Om ω + leWe (Om (1 + 1) * α)) (Om (1 + 1)) := by
  obtain ⟨-, hBsh⟩ := roShO_B (S := S) _ _ (⟨α, h1, hα, rfl, rfl⟩ : roShO (Om (1 + 1) * α) (Om 1 * α))
  obtain ⟨hDX, hBX, -, -⟩ := hBsh n
  have hWe : MvD S (leWe (Om (1 + 1) * α)) ∧
      Bc.bcB S n (leWe (Om (1 + 1) * α)) = leWe (Om (1 + 1) * α) := by
    obtain ⟨hDWe, hBWe⟩ := ldB_opow (n := n) hDX
    rw [hBX] at hBWe
    exact ⟨hDWe, hBWe⟩
  obtain ⟨hDWe, hBWe⟩ := hWe
  obtain ⟨hDW, hBW⟩ := Wr.wrB_OmW (S := S) (n := n)
  obtain ⟨hDa, hBa⟩ := mvB_add (k := n) hDW hDWe
  have hown : Om ω + leWe (Om (1 + 1) * α) ∈ S.CSet (Om ω + leWe (Om (1 + 1) * α))
      (S.psi (Om ω + leWe (Om (1 + 1) * α)) (Om (1 + 1))) :=
    CSet.add_mem (zjOmW_own _) (leWe_mem (roMulK_mem ldOm2_SC mxOm2_mem hα _ _))
  obtain ⟨hDT, hBT⟩ := mxB_atom (n := n) hDa hown
  refine ⟨hDT, ?_⟩
  rw [hBT, hBa, hBW, hBWe]

theorem zjFa_le_Pp {α : Ordinal.{0}} (h1 : 1 ≤ α) (hα : α < ω ^ ω) :
    S.psi (Om ω + leWe (Om (1 + 1) * α)) (Om (1 + 1)) ≤ Nc.ncPp S :=
  (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left _).2 (roWe_lt_OmW (zjOa_lt' h1 hα)).le)).1

theorem zjT_le_Fa {α : Ordinal.{0}} (h1 : 1 ≤ α) :
    rnTW S (Om ω) ≤ S.psi (Om ω + leWe (Om (1 + 1) * α)) (Om (1 + 1)) :=
  (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left _).2
    (leWe_mono (le_mul_left _ (Order.one_le_iff_pos.1 h1))))).1

theorem zjT_eq_F1 : rnTW S (Om ω) = S.psi (Om ω + leWe (Om (1 + 1) * 1)) (Om (1 + 1)) := by
  rw [mul_one]; rfl

/-- **Every atom `θ < s < F^ω_α` moves** once the codes below it move. -/
theorem zjAtMoveO {α : Ordinal.{0}} (hα1 : 1 ≤ α) (hα : α < ω ^ ω) :
    ZjAtK S (S.psi (Om ω + leWe (Om (1 + 1) * α)) (Om (1 + 1))) := by
  intro n l l' hR h1 hr hl' hB s hs hθs hsK IH
  have hl := hR.1
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  obtain ⟨hX, hX', hown, hown', -, -, -, -, hBψ⟩ := Wr.wrWin hR h1 hr hl' hB
  obtain ⟨hAW, hAW'⟩ := zjWin_A hR h1 hr hl' hB
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  rcases zjRepO hl hX hown hAW hα1 hα s hs hθs hsK.le with ⟨X, e, c, v, hXs, hownc, hb, rfl⟩
  obtain ⟨e1, own1, hv⟩ := zjReadO hl hX hown hAW hownc hb
  obtain ⟨hDW, hBW⟩ := Wr.wrB_OmW (S := S) (n := n)
  obtain ⟨hDe, hDc, hDs, hBs, hDv, hBown⟩ := roDigMove (n := n) (l' := l') hl hX (roShO_sh hl hX) roShO_B
    hownc hb hDW (fun x hx hxs => by
      obtain ⟨a, b, -, d, e⟩ := IH x hx hxs
      exact ⟨a, b, d, e⟩)
  rw [hBW] at hBown hBs
  have hXs' : X = 0 ∨ ∃ Xh, RoSh S X Xh := by
    rcases hXs with h0 | ⟨Xh, β, hβ1, hβ, rfl, rfl⟩
    · exact Or.inl h0
    · exact Or.inr ⟨_, roSh_o hβ1 hβ⟩
  have hXW : X + Om (1 + 1) < Om ω := by
    rcases hXs with rfl | ⟨Xh, h⟩
    · rw [zero_add]; exact ldOm2_lt_OmW
    · exact roShO_X h
  have hXB : X = 0 ∨ ∃ Xh, RoShB S X Xh := by
    rcases hXs with h0 | ⟨Xh, h⟩
    · exact Or.inl h0
    · exact Or.inr ⟨Xh, roShO_B _ _ h⟩
  have hec := roOwn_code hl hX hownc
  have heW := roGx_lt_Om2 hρ1 hec
  have heT : e < leTe S (X + Om (1 + 1)) (Om ω) := by
    refine (hb.2.2.2.2 e hec le_rfl).trans_le ?_
    exact (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left _).2
      (leWe_mono ((add_le_add_iff_left X).2 heW.le)))).1
  obtain ⟨hDWW, hBWW⟩ := roB_WeW (S := S) (n := n) hXB
  obtain ⟨hDaW, hBaW⟩ := mvB_add (k := n) hDW hDWW
  rw [hBW, hBWW] at hBaW
  have hTown : Om ω + leWe (X + Om (1 + 1)) ∈ S.CSet (Om ω + leWe (X + Om (1 + 1)))
      (S.psi (Om ω + leWe (X + Om (1 + 1))) (Om (1 + 1))) :=
    CSet.add_mem (zjOmW_own _) (leWe_mem (CSet.add_mem (roShO_mem hXs _ _) (mxOm2_mem _ _)))
  obtain ⟨hDT, hBT⟩ := mxB_atom (n := n) hDaW hTown
  rw [hBaW] at hBT
  have hBeT : Bc.bcB S n e < leTe S (X + Om (1 + 1)) (Om ω) := by
    have h := (mvB_lt_iff (k := n) hDe hDT).2 heT
    unfold leTe at h ⊢; rwa [hBT] at h
  have hb' : RoBaseE S l' X (Bc.bcB S n e) (Om ω) := zjBaseXE hAW' hXs' hXW hBeT
  obtain ⟨e1', -, -⟩ := zjReadO hl' hX' hown' hAW' hBown hb'
  have hcown := roOwn_own hl hX (roShO_sh hl hX) hownc hb
  obtain ⟨hDa, hBa⟩ := mxB_atom (n := n) hDs hcown
  obtain ⟨hBH, hBA⟩ := roOwn_mem hl' hX' (roShO_sh hl' hX') hBown hb'
  obtain ⟨hDF, hBF⟩ := zjB_Fa (S := S) (n := n) hα1 hα
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

/-- **THE READING MOVE AT THE CODES `θ⁺ ≤ m_λ < F^ω_α`** (every `1 ≤ α < ω^ω`), from the code-free wall. -/
theorem zjMoveO (hW : Wr.WrWallCF S) {α : Ordinal.{0}} (h1 : 1 ≤ α) (hα : α < ω ^ ω) :
    ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l →
    cdR S l < Bc.bcC S (n + 1) → IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
    ljThP S ≤ cdCode S l → cdCode S l < S.psi (Om ω + leWe (Om (1 + 1) * α)) (Om (1 + 1)) →
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l') :=
  zjMoveGen hW (SC_psi (InR_Om_succ 1) _) (zjThP_le_T.trans (zjT_le_Fa h1)) (zjFa_le_Pp h1 hα)
    (zjAtMoveO h1 hα)

/-! ## The top: the codes above every `F^ω_α` -/

/-- **The reading move at every window code `m_λ ≥ F^ω_α` for all `1 ≤ α < ω^ω`** (the new leaf;
`sup_α F^ω_α = ψ_{Ω₂}(Ω_ω + Ω₂^{Ω₂·ω^ω})`). -/
def ZjTopO (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', R2Skel.SkEX.SkWin S n l l' →
    (∀ α : Ordinal.{0}, 1 ≤ α → α < ω ^ ω → S.psi (Om ω + leWe (Om (1 + 1) * α)) (Om (1 + 1)) ≤ cdCode S l) →
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l')

/-- **`WrWallCF ∧ ZjTopO ⇒ Xs.XsTopK`.** -/
theorem zjTopK_ofO (hW : Wr.WrWallCF S) (hT : ZjTopO S) : Xs.XsTopK S := by
  intro n l l' hW' hK
  by_cases hex : ∃ α : Ordinal.{0}, 1 ≤ α ∧ α < ω ^ ω ∧
      cdCode S l < S.psi (Om ω + leWe (Om (1 + 1) * α)) (Om (1 + 1))
  · obtain ⟨α, h1, hα, hm⟩ := hex
    obtain ⟨hR, h1', hr, hl', hB, -⟩ := hW'
    have hP : ljThP S ≤ cdCode S l := by
      refine rnThP_le_MW.trans ?_
      rw [← Xs.xsK_one]; exact hK 1
    exact zjMoveO hW h1 hα n l l' hR h1' hr hl' hB hP hm
  · push Not at hex
    exact hT n l l' hW' fun α h1 hα => hex α h1 hα

/-- `ZjTopO ⇒ ZjTopW`-free direction: `XsTopK ⇒ ZjTopO` (`K_j < K_ω < T* ≤ F^ω_α`). -/
theorem zjTopO_of_xs (h : Xs.XsTopK S) : ZjTopO S := fun n l l' hW' hF =>
  h n l l' hW' fun j => ((zjK_lt_Kw j).trans zjKw_lt_T).le.trans
    (zjT_eq_F1.symm ▸ hF 1 le_rfl (one_lt_omega0.trans (by
      simpa using (opow_lt_opow_iff_right one_lt_omega0).2 one_lt_omega0)))

/-- **NON-VACUITY**: `L(ω+1) ≤ ν_C ∧ CdEQ ∧ SkEX.SkKFar ⇒ ZjTopO` (the road's target gives the leaf). -/
theorem zjTopO_of_target (hν : Nc.ncL S (ω + 1) ≤ nuC) (hEQ : CdEQ S) (hK : R2Skel.SkEX.SkKFar S) :
    ZjTopO S :=
  zjTopO_of_xs (Xs.xsTopK_of_target hν hEQ hK)

/-- **`XsTopK ⇔ ZjTopO`** under the wall. -/
theorem zjTopK_iffO (hW : Wr.WrWallCF S) : Xs.XsTopK S ↔ ZjTopO S :=
  ⟨zjTopO_of_xs, zjTopK_ofO hW⟩

end Googology.Trans.PoR.InaccPsi.R2.Zj

import Googology.Trans.PoR.InaccPsi.R2.ZdChain
import Googology.Trans.PoR.InaccPsi.R2.YjTop

/-!
# THE MOVE OF THE TOP ATOMS, GENERIC IN THE SHIFT

`W^x = leWe x`, `t = β + W^{X+e}`, `B_n = Bc.bcB S n`, "window" (`CdRange λ`, `c_n < ρ_λ`, `r(λ) < c_{n+1}`, `λ'`
a restart, `B_n ρ_λ = ρ_λ'`), "IH(s)" (every code `x < s` of `λ` moves: the premise of WallBelow) as in
`Yj.yjBaseFacts`.  `Yd.ydFixB`, `Yd.ydOwnMoveB`, `Yd.ydBaseMoveB`, `Yj.yjDvd`, `Yj.yjD`, `Yj.yjTopBase` are written for
the shift `X = Ω_{k+3}`; here `X` is any shift with the data `ZdMv S X` (`X` in every closure, `X < Ω_ω`, `X ≠ 0`,
`B_n` fixes `Ω₂·X`), and the top law at the codes of `X` is the hypothesis `ZdHL S X` (at every restart):

* `zdTopD`, `zdTopAt`, `zdBaseE_lt`, `zdFixB` (`B_n e^β_m = e^{B_n β}_m`), `zdOwnMoveB` (the own clause moves);
* `zdDvd`, `zdD`, `zdBaseFacts` (**THE TWO BASE FACTS at `λ'`**), `zdBaseMoveB` (**THE BASE-DATA MOVE**);
* `zdTopBase` (**THE TOP ATOM IS A BASE WITH A LAW AT BOTH ENDS**, `Yj.YjBase λ λ' A' t (1 + ψ₂(T t))`);
* `zdTopMove` (**EVERY TOP ATOM `ψ₂(β + W^{X+e})` MOVES** under IH, no further hypothesis);
* `zdB_opowMul` (`B_n(ω^p·ξ) = ω^p·ξ` for `ξ < ε₀`, `p` fixed), `zdMv_chain` (**`X_ξ = Ω_{k+3} + Ω₂·ξ` has the data
  `ZdMv`** for `ξ < ε₀`), `zdHL_chain` (**`ZdHL S X_ξ`**, from `Zd.zdChain`).

No new axiom.  New definitions: `ZdMv` (the shift data for the move), `ZdHL` (the statement of the law family).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Rx
  Googology.Trans.PoR.InaccPsi.R2.Yd Googology.Trans.PoR.InaccPsi.R2.Yj

variable {S : InaccSeq.{0}}

/-- **The shift data for the move**: `X` in every closure, `X < Ω_ω`, `X ≠ 0`, `B_n` fixes `Ω₂·X`. -/
structure ZdMv (S : InaccSeq.{0}) (X : Ordinal.{0}) : Prop where
  mem : ∀ a c : Ordinal.{0}, X ∈ S.CSet a c
  lt : X < Om ω
  ne : X ≠ 0
  shB : Ro.RoShB S X 1

/-- **The top law at every code exponent of the shift `X`, at every restart.** -/
def ZdHL (S : InaccSeq.{0}) (X : Ordinal.{0}) : Prop :=
  ∀ (l ηx A : Ordinal.{0}), IsRestartIdx l → upsilon l < Pv S ηx → A ∈ S.CSet A (S.psi A (Om 1)) →
    S.psi A (Om 1) = upsilon l → ∀ e β, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → VbD S l β →
      Ro.RoBaseE S l X e β → ZdLaw S l A X e β

section Data

variable {X : Ordinal.{0}} (hm : ZdMv S X)
include hm

/-- **The data of a top base** `t = β + W^{X+e}`. -/
theorem zdTopD {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    {e β : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (he2 : e < Om (1 + 1))
    (hβD : VbD S l β) (hB : Ro.RoBaseE S l X e β) :
    VbD S l (β + leWe (X + e)) ∧ Om (1 + 1) ∣ β + leWe (X + e) ∧
      ∀ d, d ≤ Om (1 + 1) → β + leWe (X + e) ∈ S.CSet (β + leWe (X + e) + d)
        (S.psi (β + leWe (X + e) + d) (Om (1 + 1))) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hXmem : ∀ a c : Ordinal.{0}, X ∈ S.CSet a c := hm.mem
  have hXW : X < Om ω := hm.lt
  obtain ⟨hβd, hβH, -, hβown, hexpA⟩ := hB
  have hexp : e < S.psi (β + leWe (X + e)) (Om (1 + 1)) := hexpA e hec le_rfl
  have hβW : β < Om ω := hβD.2.2
  have hgW : X + e < Om ω := vkOmW.1.isPrincipal hXW (he2.trans ldOm2_lt_OmW)
  have hwW : leWe (X + e) < Om ω := (leWe_lt_SC vkOmW.1 vkOmW.2 hgW).1
  have heθ : e < ConjT.th S := hexp.trans_le (psi_mono hκ2 (vkOmW.1.isPrincipal hβW hwW).le).1
  have hD : VbD S l (β + leWe (X + e)) :=
    ⟨CSet.add_mem hβH (leWe_mem (CSet.add_mem (hXmem _ _) ((ldHull_iff hl hX he2).2 hec))),
      CSet.add_mem hβD.2.1 (leWe_mem (CSet.add_mem (hXmem _ _) (CSet.of_lt heθ))),
      vkOmW.1.isPrincipal hβW hwW⟩
  have h1g : (1 : Ordinal.{0}) ≤ X + e :=
    (Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 hm.ne)).trans le_self_add
  have hW2 : Om (1 + 1) ∣ leWe (X + e) := by
    have h := leWe_dvd h1g; rwa [leWe_one] at h
  refine ⟨hD, dvd_add (hW2.trans hβd) hW2, fun d _ => ?_⟩
  have hle : β + leWe (X + e) ≤ β + leWe (X + e) + d := le_self_add
  have hβm := (psi_mono (S := S) hκ2 hle).2 (hβown _ le_rfl)
  have hem : e ∈ S.CSet (β + leWe (X + e) + d) (S.psi (β + leWe (X + e) + d) (Om (1 + 1))) :=
    CSet.of_lt (hexp.trans_le (psi_mono hκ2 hle).1)
  exact CSet.add_mem hβm (leWe_mem (CSet.add_mem (hXmem _ _) hem))

/-- **`ψ₂(β + W^{X+Ω₂})` is an atom of `λ` for every `β ∈ D`.** -/
theorem zdTopAt {l β : Ordinal.{0}} (hβD : VbD S l β) :
    S.psi (β + leWe (X + Om (1 + 1))) (Om (1 + 1)) ∈ ldAtR S l :=
  ⟨_, CSet.add_mem hβD.1 (leWe_mem (CSet.add_mem (hm.mem _ _) (mxOm2_mem _ _))),
    (zdBW_lt hm.lt hβD.2.2 le_rfl).trans_le (ConjT.OmW_le_A S _), rfl⟩

/-- **`Ro.RoBaseE λ X e β`, `β ∈ D` ⇒ `e < ψ₂(β + W^{X+Ω₂})`.** -/
theorem zdBaseE_lt {l e β : Ordinal.{0}} (hβD : VbD S l β) (hb : Ro.RoBaseE S l X e β) :
    e < S.psi (β + leWe (X + Om (1 + 1))) (Om (1 + 1)) := by
  by_contra hc
  push Not at hc
  have h1 := hb.2.2.2.2 _ (GxCl.atom (zdTopAt hm hβD)) hc
  exact absurd (h1.trans_le (ydTopFailB _ _)) (lt_irrefl _)

/-- **`B_n e^β_m = e^{B_n β}_m`** (`β` normal in the domain). -/
theorem zdFixB (n : ℕ) {β : Ordinal.{0}} (hDβ : MvD S β) (hβ : β ∈ S.CSet β (S.psi β (Om (1 + 1)))) :
    ∀ m, MvD S (ydEB S X β m) ∧ Bc.bcB S n (ydEB S X β m) = ydEB S X (Bc.bcB S n β) m
  | 0 => by
    rw [ydEB_zero, ydEB_zero]
    have hc : (0 : Ordinal.{0}) < Bc.bcC S n := (Lw.lw_L_SC S _).1
    exact ⟨mvD_of_lt (Lw.lw_L_SC S ω).1, Bc.bcB_fix' S n 0 hc⟩
  | m + 1 => by
    obtain ⟨hDm, hBm⟩ := zdFixB n hDβ hβ m
    set P : Ordinal.{0} → Prop := fun x => x = 0 ∨ (x = ydEB S X β m ∧ SC x) with hP
    have hPD : ∀ x, P x → MvD S x := by
      rintro x (rfl | ⟨rfl, -⟩)
      · exact mvD_of_lt (Lw.lw_L_SC S ω).1
      · exact hDm
    have hPdec : ∀ x, P x → x ≠ 0 → P (log ω x) ∧ P (x - ω ^ log ω x) := by
      rintro x (rfl | ⟨hx, hxS⟩) hx0
      · exact absurd rfl hx0
      · have hl : log ω x = x := by
          conv_lhs => rw [← gg_SC_eps hxS]
          exact log_opow one_lt_omega0 x
        rw [hl, gg_SC_eps hxS, Ordinal.sub_self]
        exact ⟨Or.inr ⟨hx, hxS⟩, Or.inl rfl⟩
    have hPW : ∀ x, P x → x < Om (1 + 1) := by
      rintro x (rfl | ⟨rfl, -⟩)
      · exact ldOm2_SC.1
      · exact ydEB_lt_Om2 X β m
    have hPm : P (ydEB S X β m) := by
      cases m with
      | zero => exact Or.inl rfl
      | succ j => exact Or.inr ⟨rfl, ydEB_SC X β j⟩
    obtain ⟨hDW, hBW, -, -⟩ := Ro.roB_We (n := n) hm.ne hm.shB P hPD hPdec hPW hPm hPm
    rw [hBm] at hBW
    obtain ⟨hDa, hBa⟩ := mvB_add (k := n) hDβ hDW
    rw [hBW] at hBa
    have hown : β + leWe (X + ydEB S X β m) ∈ S.CSet (β + leWe (X + ydEB S X β m))
        (S.psi (β + leWe (X + ydEB S X β m)) (Om (1 + 1))) := by
      refine CSet.add_mem (ydNormD (fun a b _ => hm.mem a b) hβ _) (leWe_mem (CSet.add_mem (hm.mem _ _) (CSet.of_lt ?_)))
      rw [← ydEB_succ]; exact ydEB_lt_succ (fun a b _ => hm.mem a b) hβ m
    obtain ⟨hDs, hBs⟩ := mxB_atom (n := n) hDa hown
    rw [hBa] at hBs
    rw [ydEB_succ, ydEB_succ]
    exact ⟨hDs, hBs⟩

/-- **THE OWN CLAUSE MOVES** (`β` normal in the domain, `e ∈ MvD` below `ψ₂(β + W^{X+Ω₂})`). -/
theorem zdOwnMoveB (n : ℕ) {β e : Ordinal.{0}} (hDβ : MvD S β) (hβ : β ∈ S.CSet β (S.psi β (Om (1 + 1))))
    (hDe : MvD S e) (he : e < S.psi (β + leWe (X + Om (1 + 1))) (Om (1 + 1))) :
    Bc.bcB S n e < S.psi (Bc.bcB S n β + leWe (X + Om (1 + 1))) (Om (1 + 1)) ∧
      ∀ e'', e'' ≤ Bc.bcB S n e → e'' < S.psi (Bc.bcB S n β + leWe (X + e'')) (Om (1 + 1)) := by
  obtain ⟨m, hm'⟩ := ydLtTopB (fun a b _ => hm.mem a b) hβ he
  obtain ⟨hDm, hBm⟩ := zdFixB hm n hDβ hβ m
  have h := (mvB_lt_iff (k := n) hDe hDm).2 hm'
  rw [hBm] at h
  have hB' : Bc.bcB S n e < S.psi (Bc.bcB S n β + leWe (X + Om (1 + 1))) (Om (1 + 1)) :=
    h.trans_le (ydEB_le_top _ _ m)
  exact ⟨hB', (ydOwnB_iff (fun a b _ => hm.mem a b) (ydNormB n hDβ hβ) _).2 hB'⟩

end Data

section Win

variable {X : Ordinal.{0}} (hm : ZdMv S X)
  {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
  (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')

include hm hR h1 hr hl' hB

/-- **THE DIVISIBILITY MOVES**: `W^{X+e} ∣ x ⇒ W^{X+B_n e} ∣ B_n x` for every `x ∈ D ∩ Cl(t, ψ₂ t)`. -/
theorem zdDvd {e β : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (hβD : VbD S l β)
    (hb : Ro.RoBaseE S l X e β)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (β + leWe (X + e)) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    ∀ x, VbD S l x → x ∈ S.CSet (β + leWe (X + e)) (S.psi (β + leWe (X + e)) (Om (1 + 1))) →
      leWe (X + e) ∣ x → leWe (X + Bc.bcB S n e) ∣ Bc.bcB S n x := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hl := hR.1
  obtain ⟨hX, hown, hρA, hX', -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  have he : e < S.psi (β + leWe (X + Om (1 + 1))) (Om (1 + 1)) := zdBaseE_lt hm hβD hb
  have he2 : e < Om (1 + 1) := he.trans (psi_lt hκ2 _)
  have hes : e < S.psi (β + leWe (X + e)) (Om (1 + 1)) := hb.2.2.2.2 e hec le_rfl
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  set P : Ordinal.{0} → Prop := fun x => GxCl (upsilon l) (ldAtR S l) x ∧
    x < S.psi (β + leWe (X + e)) (Om (1 + 1)) ∧ x < Om (1 + 1) with hP_def
  have hPD : ∀ x, P x → MvD S x := fun x hx => (IH x hx.1 hx.2.1).1
  have hPdec : ∀ x, P x → x ≠ 0 → P (log ω x) ∧ P (x - ω ^ log ω x) := fun x hx hx0 => by
    obtain ⟨hsub, hlog⟩ := gxDec hρSC hAt x hx.1
    have hlx : log ω x ≤ x := log_le_self ω x
    have hlead : ω ^ log ω x ≤ x := opow_log_le_self ω hx0
    exact ⟨⟨hlog, hlx.trans_lt hx.2.1, hlx.trans_lt hx.2.2⟩,
      ⟨hsub _ (GxCl.opow hρSC.1 hlog) hlead, (Ordinal.sub_le_self _ _).trans_lt hx.2.1,
        (Ordinal.sub_le_self _ _).trans_lt hx.2.2⟩⟩
  have hPW : ∀ x, P x → x < Om (1 + 1) := fun x hx => hx.2.2
  obtain ⟨hDW, hBW, -, -⟩ := Ro.roB_We (n := n) hm.ne hm.shB P hPD hPdec hPW
    ⟨hec, hes, he2⟩ ⟨hec, hes, he2⟩
  have hTM := fun x (hx : VbD S l x) (hxC : x ∈ S.CSet (β + leWe (X + e)) (S.psi (β + leWe (X + e)) (Om (1 + 1)))) =>
    Xq.xqTMove (n := n) hl hX hl' hX' hown hρA IH x hx hxC
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IHx =>
  intro hxD hxC hdv
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [Bc.bcB_zero]; exact dvd_zero _
  obtain ⟨⟨hLD, hLC⟩, ⟨hrD, hrC⟩⟩ := yjParts hxD hxC
  obtain ⟨hDL, -, -⟩ := hTM _ hLD hLC
  obtain ⟨hDr, -, -⟩ := hTM _ hrD hrC
  obtain ⟨m, hm'⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
  have hdm : x = ω ^ log ω x * m + x % ω ^ log ω x := by
    rw [← hm']; exact (Ordinal.div_add_mod x _).symm
  obtain ⟨hDo, hBo⟩ := ldB_opow (n := n) hDL
  obtain ⟨hDom, hBom⟩ := vbB_mulNat (n := n) hDo m
  obtain ⟨-, hBx⟩ := mvB_add (k := n) hDom hDr
  rw [← hdm] at hBx
  rw [hBx, hBom, hBo]
  have hWle : ω ^ (Om (1 + 1) * (X + e)) ≤ x := Ordinal.le_of_dvd hx0 hdv
  have hpL : Om (1 + 1) * (X + e) ≤ log ω x := (Ordinal.opow_le_iff_le_log one_lt_omega0 hx0).1 hWle
  have hWo : leWe (X + e) ≤ ω ^ log ω x := opow_le_opow_right omega0_pos hpL
  have hBWo : Bc.bcB S n (leWe (X + e)) ≤ Bc.bcB S n (ω ^ log ω x) := by
    rcases hWo.lt_or_eq with h | h
    · exact ((mvB_lt_iff hDW hDo).2 h).le
    · rw [h]
  rw [hBW, hBo] at hBWo
  have hp' : Om (1 + 1) * (X + Bc.bcB S n e) ≤ Bc.bcB S n (log ω x) :=
    (opow_le_opow_iff_right one_lt_omega0).1 hBWo
  refine dvd_add (Dvd.dvd.mul_right (opow_dvd_opow ω hp') _) ?_
  have hrlt : x % ω ^ log ω x < x :=
    (Ordinal.mod_lt x (opow_ne_zero _ omega0_ne_zero)).trans_le (opow_log_le_self ω hx0)
  refine IHx _ hrlt hrD hrC ?_
  have h2 : leWe (X + e) ∣ ω ^ log ω x * m := Dvd.dvd.mul_right (opow_dvd_opow ω hpL) _
  rw [hdm] at hdv
  exact (Ordinal.dvd_add_iff h2).1 hdv

omit hm in
/-- **`B_n β ∈ D_{λ'}`** for every top base `(e, β)`, `β ∈ D`, at a window, under IH. -/
theorem zdD {e β : Ordinal.{0}} (hβD : VbD S l β) (hb : Ro.RoBaseE S l X e β)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (β + leWe (X + e)) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    VbD S l' (Bc.bcB S n β) := by
  set a := β + leWe (X + e) with hadef
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hl := hR.1
  obtain ⟨hX, hown, hρA, hX', -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hβC : β ∈ S.CSet a (S.psi a (Om (1 + 1))) := hb.2.2.2.1 _ le_rfl
  have hTW : gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1))) ≤ vbW S l := by
    rw [vbW_eq hl hX]; exact gxTh_mono (psi_lt hκ2 a).le
  have hSC : SC (gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1)))) :=
    gxTh_SC hρSC (ldAt_GxAt _ _) (SC_psi hκ2 a) (hρ1.trans (psiS_bounds (S := S) a 1).1)
  obtain ⟨hDβ, -, hBE, hK, -⟩ := vbT_move (n := n) hl hX hl' hX' hSC hTW (Xq.xqLeaf hl hX hl' hX' IH) hβD
    (Xq.xqTE hl hX hown hρA β hβD hβC)
  obtain ⟨hZ', hZ1'⟩ := vbZ hl' hX'
  have hlt : Bc.bcB S n β < Om ω := by
    rw [← hK]; exact rxL_lt_OmW hZ' hZ1' (ldAt_GxAt _ _) hBE
  have hH : Bc.bcB S n β ∈ cdHull S l' := by
    rw [← hK]
    show _ ∈ S.CSet (ConjT.Aη S (cdEta S l')) (upsilon l')
    refine rxL_memH hZ' hZ1' (ldAt_GxAt _ _) (vbW_SC hl' hX') le_rfl (ConjT.OmW_le_A S _)
      (fun g hg => ?_) _ hBE
    have hg' : g < gxTh (upsilon l') (ldAtR S l') (Om (1 + 1)) := by rw [← vbW_eq hl' hX']; exact hg
    obtain ⟨hc, hc2, -⟩ := Ru.ruInv_spec hg'
    exact (ldHull_iff hl' hX' hc2).2 hc
  have hβn : β ∈ S.CSet β (S.psi β (Om (1 + 1))) := by
    have h := hb.2.2.2.1 0 zero_le; rwa [add_zero] at h
  have hn' := ydNormB n hDβ hβn
  exact ⟨hH, (psi_mono hκ2 hlt.le).2 hn', hlt⟩

/-- **THE TWO BASE FACTS** at `λ'`: `W^{X+B_n e} ∣ B_n β` and `B_n β ∈ D_{λ'}`. -/
theorem zdBaseFacts {e β : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (hβD : VbD S l β)
    (hb : Ro.RoBaseE S l X e β)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (β + leWe (X + e)) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    leWe (X + Bc.bcB S n e) ∣ Bc.bcB S n β ∧ VbD S l' (Bc.bcB S n β) :=
  ⟨zdDvd hm hR h1 hr hl' hB hec hβD hb IH β hβD (hb.2.2.2.1 _ le_rfl) hb.1, zdD hR h1 hr hl' hB hβD hb IH⟩

/-- **THE BASE-DATA MOVE over every top base `(e, β)`** of the shift `X`. -/
theorem zdBaseMoveB {e β : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (hβD : VbD S l β)
    (hb : Ro.RoBaseE S l X e β)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (β + leWe (X + e)) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S β ∧ MvD S e ∧ GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n e) ∧ Bc.bcB S n e < Om (1 + 1) ∧
      Ro.RoBaseE S l' X (Bc.bcB S n e) (Bc.bcB S n β) ∧
      Bc.bcB S n (β + leWe (X + e)) = Bc.bcB S n β + leWe (X + Bc.bcB S n e) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hl := hR.1
  obtain ⟨hdiv', hD'⟩ := zdBaseFacts hm hR h1 hr hl' hB hec hβD hb IH
  obtain ⟨hX, hown, hρA, hX', -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  have hβn : β ∈ S.CSet β (S.psi β (Om (1 + 1))) := by
    have h := hb.2.2.2.1 0 zero_le; rwa [add_zero] at h
  have hβC : β ∈ S.CSet (β + leWe (X + e)) (S.psi (β + leWe (X + e)) (Om (1 + 1))) := hb.2.2.2.1 _ le_rfl
  have he : e < S.psi (β + leWe (X + Om (1 + 1))) (Om (1 + 1)) := zdBaseE_lt hm hβD hb
  have he2 : e < Om (1 + 1) := he.trans (psi_lt hκ2 _)
  have hes : e < S.psi (β + leWe (X + e)) (Om (1 + 1)) := hb.2.2.2.2 e hec le_rfl
  obtain ⟨hDe, hBec, hBeP, -, -⟩ := IH e hec hes
  obtain ⟨hDβ, -, -⟩ := Xq.xqTMove (n := n) hl hX hl' hX' hown hρA IH β hβD hβC
  obtain ⟨-, hown'⟩ := zdOwnMoveB hm n hDβ hβn hDe he
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  set P : Ordinal.{0} → Prop := fun x => GxCl (upsilon l) (ldAtR S l) x ∧
    x < S.psi (β + leWe (X + e)) (Om (1 + 1)) ∧ x < Om (1 + 1) with hP_def
  have hPD : ∀ x, P x → MvD S x := fun x hx => (IH x hx.1 hx.2.1).1
  have hPdec : ∀ x, P x → x ≠ 0 → P (log ω x) ∧ P (x - ω ^ log ω x) := fun x hx hx0 => by
    obtain ⟨hsub, hlog⟩ := gxDec hρSC hAt x hx.1
    have hlx : log ω x ≤ x := log_le_self ω x
    have hlead : ω ^ log ω x ≤ x := opow_log_le_self ω hx0
    exact ⟨⟨hlog, hlx.trans_lt hx.2.1, hlx.trans_lt hx.2.2⟩,
      ⟨hsub _ (GxCl.opow hρSC.1 hlog) hlead, (Ordinal.sub_le_self _ _).trans_lt hx.2.1,
        (Ordinal.sub_le_self _ _).trans_lt hx.2.2⟩⟩
  have hPW : ∀ x, P x → x < Om (1 + 1) := fun x hx => hx.2.2
  obtain ⟨hDW, hBW, -, -⟩ := Ro.roB_We (n := n) hm.ne hm.shB P hPD hPdec hPW
    ⟨hec, hes, he2⟩ ⟨hec, hes, he2⟩
  obtain ⟨-, hBt⟩ := mvB_add (k := n) hDβ hDW
  rw [hBW] at hBt
  have hBe2 : Bc.bcB S n e < Om (1 + 1) := hBeP.trans Lj.ljThP_lt_Om2
  have hβn' := ydNormB n hDβ hβn
  refine ⟨hDβ, hDe, hBec, hBe2, ⟨hdiv', hD'.1, ?_, fun d _ => (psi_mono hκ2 le_self_add).2 hβn',
    fun e'' _ he'' => hown' e'' he''⟩, hBt⟩
  exact (zdBW_lt hm.lt hD'.2.2 hBe2.le).trans_le (ConjT.OmW_le_A S _)

/-- **EVERY TOP ATOM `ψ₂(β + W^{X+e})` MOVES** at a window under IH, given the law at the codes of `X`. -/
theorem zdTopMove (HL : ZdHL S X) {e β : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e)
    (hβD : VbD S l β) (hb : Ro.RoBaseE S l X e β)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (β + leWe (X + e)) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S (S.psi (β + leWe (X + e)) (Om (1 + 1))) ∧
      Bc.bcB S n (S.psi (β + leWe (X + e)) (Om (1 + 1))) =
        S.psi (Bc.bcB S n β + leWe (X + Bc.bcB S n e)) (Om (1 + 1)) ∧
      Bc.bcB S n (S.psi (β + leWe (X + e)) (Om (1 + 1))) ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n (S.psi (β + leWe (X + e)) (Om (1 + 1)))) =
        Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe (X + e)) (Om (1 + 1)))) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hl := hR.1
  obtain ⟨hX, hown, hρA, hX', A', hA', hρA'⟩ := Xv.xvWin hR h1 hr hl' hB
  obtain ⟨-, hD'⟩ := zdBaseFacts hm hR h1 hr hl' hB hec hβD hb IH
  obtain ⟨-, -, hBec, hBe2, hb', hmv⟩ := zdBaseMoveB hm hR h1 hr hl' hB hec hβD hb IH
  have he2 : e < Om (1 + 1) := (zdBaseE_lt hm hβD hb).trans (psi_lt hκ2 _)
  obtain ⟨hD, -, htown⟩ := zdTopD hm hl hX hec he2 hβD hb
  have han := htown 0 zero_le
  rw [add_zero] at han
  have hlaw := HL l _ _ hl hX hown hρA e β hec he2 hβD hb
  have hlaw' := HL l' _ _ hl' hX' hA' hρA' (Bc.bcB S n e) (Bc.bcB S n β) hBec hBe2 hD' hb'
  unfold ZdLaw leTe at hlaw hlaw'
  rw [← hmv] at hlaw'
  have hhi := yjTh_hi hR h1 hr hl' hB (yjPsi2_leW (S := S) hD.2.2)
  rw [hlaw] at hhi
  obtain ⟨hDs, hBs, hmove⟩ := Xq.xqLawMove hl hX hl' hX' hown hρA hA' hρA' h1.le hB hD han IH hlaw hhi hlaw'
  have hBeH : Bc.bcB S n e ∈ cdHull S l' := (ldHull_iff hl' hX' hBe2).2 hBec
  have hatom : S.psi (Bc.bcB S n β + leWe (X + Bc.bcB S n e)) (Om (1 + 1)) ∈ ldAtR S l' :=
    ⟨_, CSet.add_mem hD'.1 (leWe_mem (CSet.add_mem (hm.mem _ _) hBeH)),
      (zdBW_lt hm.lt hD'.2.2 hBe2.le).trans_le (ConjT.OmW_le_A S _), rfl⟩
  rw [hmv] at hBs
  exact ⟨hDs, hBs, hBs ▸ hatom, hmove⟩

/-- **THE TOP ATOM IS A BASE WITH A LAW AT BOTH ENDS**, for every shift with `ZdMv` and `ZdHL`. -/
theorem zdTopBase (HL : ZdHL S X) {A' : Ordinal.{0}} (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1)))
    (hρ' : S.psi A' (Om 1) = upsilon l') {e β : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e)
    (hβD : VbD S l β) (hb : Ro.RoBaseE S l X e β)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (β + leWe (X + e)) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    YjBase S n l l' A' (β + leWe (X + e)) (1 + S.psi (vbT S l (β + leWe (X + e))) (Om (1 + 1))) ∧
      Bc.bcB S n (β + leWe (X + e)) = Bc.bcB S n β + leWe (X + Bc.bcB S n e) := by
  set t := β + leWe (X + e) with htdef
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hl := hR.1
  obtain ⟨hX, hown, hρA, hX', -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  have he2 : e < Om (1 + 1) := (zdBaseE_lt hm hβD hb).trans (psi_lt hκ2 _)
  obtain ⟨htD, htd, htown⟩ := zdTopD hm hl hX hec he2 hβD hb
  have htn : t ∈ S.CSet t (S.psi t (Om (1 + 1))) := by have h := htown 0 zero_le; rwa [add_zero] at h
  obtain ⟨hDt, hDT, hTmv⟩ := Xq.xqTMove (n := n) hl hX hl' hX' hown hρA IH t htD htn
  have hlaw := HL l _ _ hl hX hown hρA e β hec he2 hβD hb
  unfold ZdLaw leTe at hlaw
  have hhi : S.psi (ConjT.Aη S (cdEta S l) + 1 + S.psi (vbT S l t) (Om (1 + 1))) (Om 1) < Bc.bcC S (n + 1) := by
    rw [← hlaw]; exact yjTh_hi hR h1 hr hl' hB (yjPsi2_leW htD.2.2)
  obtain ⟨hDψ, hBψ, -⟩ := Xq.xqSigMove hl hX hown hρA hA' hρ' h1.le hB htD htn hDT hhi
  have h1L : (1 : Ordinal.{0}) < Nc.ncL S ω := one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S ω))
  have hB1 : Bc.bcB S n 1 = 1 := Bc.bcB_fixN n 1 (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  obtain ⟨hDD, hBD⟩ := mvB_add (k := n) (mvD_of_lt h1L) hDψ
  rw [hB1, hBψ] at hBD
  have hat := Xq.xqOwn hl hX hown hρA htD htn
  obtain ⟨hdv', hD'⟩ := zdBaseFacts hm hR h1 hr hl' hB hec hβD hb IH
  obtain ⟨-, -, hBec, hBe2, hb', hBt⟩ := zdBaseMoveB hm hR h1 hr hl' hB hec hβD hb IH
  obtain ⟨htD', htd', htown'⟩ := zdTopD hm hl' hX' hBec hBe2 hD' hb'
  have htn' : Bc.bcB S n β + leWe (X + Bc.bcB S n e) ∈ S.CSet (Bc.bcB S n β + leWe (X + Bc.bcB S n e))
      (S.psi (Bc.bcB S n β + leWe (X + Bc.bcB S n e)) (Om (1 + 1))) := by
    have h := htown' 0 zero_le; rwa [add_zero] at h
  have hlaw' := HL l' _ _ hl' hX' hA' hρ' (Bc.bcB S n e) (Bc.bcB S n β) hBec hBe2 hD' hb'
  unfold ZdLaw leTe at hlaw'
  have hat' := Xq.xqOwn hl' hX' hA' hρ' htD' htn'
  rw [← hBt, hTmv] at hlaw' hat'
  refine ⟨⟨htD, htd, htown, hDt, hDD, by rw [← add_assoc]; exact hat, by rw [← add_assoc]; exact hlaw,
    hBt ▸ htD', hBt ▸ htd', hBt ▸ htown', by rw [hBD, ← add_assoc]; exact hat',
    by rw [hBD, ← add_assoc]; exact hlaw'⟩, hBt⟩

end Win

/-! ## The shifts `X_ξ = Ω_{k+3} + Ω₂·ξ`, `ξ < ε₀` -/

/-- **`B_n(ω^p·ξ) = ω^p·ξ`** for every `ξ < ε₀` and every `p` fixed by `B_n`. -/
theorem zdB_opowMul {n : ℕ} {p : Ordinal.{0}} (hpD : MvD S p) (hpB : Bc.bcB S n p = p) :
    ∀ ξ, ξ < ε₀ → MvD S (ω ^ p * ξ) ∧ Bc.bcB S n (ω ^ p * ξ) = ω ^ p * ξ := by
  have hεL : (ε₀ : Ordinal.{0}) ≤ Nc.ncL S ω :=
    epsilon_zero_le_of_omega0_opow_le (gg_SC_eps (Lw.lw_L_SC S ω)).le
  have hεc : (ε₀ : Ordinal.{0}) ≤ Bc.bcC S n :=
    epsilon_zero_le_of_omega0_opow_le (gg_SC_eps (Lw.lw_L_SC S _)).le
  intro ξ
  induction ξ using WellFoundedLT.induction with
  | ind ξ IH =>
  intro hξ
  rcases eq_or_ne ξ 0 with rfl | h0
  · rw [mul_zero]; exact ⟨vbD0, Bc.bcB_zero n⟩
  have hL := Gc.gc_log_lt h0 hξ
  set a := log ω ξ with ha
  obtain ⟨m, hm⟩ := lt_omega0.1 (div_opow_log_lt ξ one_lt_omega0)
  have hdm : ξ = ω ^ a * m + ξ % ω ^ a := by rw [← hm]; exact (Ordinal.div_add_mod ξ _).symm
  have hrlt : ξ % ω ^ a < ξ :=
    (Ordinal.mod_lt ξ (opow_ne_zero _ omega0_ne_zero)).trans_le (opow_log_le_self ω h0)
  obtain ⟨hDr, hBr⟩ := IH _ hrlt (hrlt.trans hξ)
  have haD : MvD S a := mvD_of_lt ((hL.trans hξ).trans_le hεL)
  have haB : Bc.bcB S n a = a := Bc.bcB_fix' S n a ((hL.trans hξ).trans_le hεc)
  obtain ⟨hDpa, hBpa⟩ := mvB_add (k := n) hpD haD
  rw [hpB, haB] at hBpa
  obtain ⟨hDo, hBo⟩ := ldB_opow (n := n) hDpa
  rw [hBpa] at hBo
  obtain ⟨hDom, hBom⟩ := vbB_mulNat (n := n) hDo m
  rw [hBo] at hBom
  have e1 : ω ^ p * ξ = ω ^ (p + a) * m + ω ^ p * (ξ % ω ^ a) := by
    conv_lhs => rw [hdm]
    rw [mul_add, ← mul_assoc, ← opow_add]
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDom hDr
  rw [hBom, hBr] at hBs
  rw [e1]
  exact ⟨hDs, hBs⟩

/-- **`X_ξ = Ω_{k+3} + Ω₂·ξ` has the move data `ZdMv`** for every `ξ < ε₀`. -/
theorem zdMv_chain (k : ℕ) {ξ : Ordinal.{0}} (hξ : ξ < ε₀) : ZdMv S (zdX k ξ) := by
  have hξ2 : ξ < Om (1 + 1) := (hξ.trans_le Gc.gc_eps0_le_Om1).trans (Om_lt_Om.2 (lt_add_one 1))
  refine ⟨fun a c => CSet.add_mem (Vn.vnOmK3_mem k a c) (ldMulK_mem ldOm2_SC (mxOm2_mem _ _)
      (Gc.gc_cst_mem a c ξ hξ)), vkOmW.1.isPrincipal (Wv.wvOmK_lt_W k) (zdMul2_lt hξ2), ?_, one_ne_zero,
    fun n => ?_⟩
  · unfold zdX
    exact (add_pos_of_pos_of_nonneg (Om_pos (add_pos_of_right zero_lt_one _).ne') zero_le).ne'
  obtain ⟨hD3, hB3, hD1, hB1⟩ := (Xv.xvShB (S := S) k).2 n
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hDp, hBp⟩ := mvB_add (k := n) hD2 hD2
  rw [hB2] at hBp
  obtain ⟨hDq, hBq⟩ := zdB_opowMul (n := n) hDp hBp ξ hξ
  have e1 : Om (1 + 1) * zdX k ξ = Om (1 + 1) * Om ((k : Ordinal.{0}) + 1 + 1 + 1) +
      ω ^ (Om (1 + 1) + Om (1 + 1)) * ξ := by
    unfold zdX
    rw [mul_add, opow_add, gg_SC_eps ldOm2_SC, mul_assoc]
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hD3 hDq
  rw [hB3, hBq] at hBs
  rw [e1]
  exact ⟨hDs, hBs, hD1, hB1⟩

/-- **`ZdHL S X_ξ`**: the top law at every code exponent of `X_ξ`, at every restart (`Zd.zdChain`). -/
theorem zdHL_chain (k : ℕ) {ξ : Ordinal.{0}} (hξ : ξ < ε₀) : ZdHL S (zdX k ξ) :=
  fun _ _ _ hl hX hA hρ e β hec he2 hβD hb => zdChain hl hX hA hρ k ξ hξ e hec he2 β hβD hb

end Googology.Trans.PoR.InaccPsi.R2.Zd

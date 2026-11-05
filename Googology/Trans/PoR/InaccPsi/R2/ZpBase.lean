import Googology.Trans.PoR.InaccPsi.R2.ZpPre
import Googology.Trans.PoR.InaccPsi.R2.YjTop
import Googology.Trans.PoR.InaccPsi.R2.VbReach
import Googology.Trans.PoR.InaccPsi.R2.VnWall
import Googology.Trans.PoR.InaccPsi.R2.VsBase

/-!
# Every `Ω₃`-divisible normal base is a base with a law at both ends, given the law at each end

`B_n = Bc.bcB S n`, "window" as in `Yj.yjBlkMove` (`CdRange λ`, `c_n < ρ_λ`, `r(λ) < c_{n+1}`, `λ'` a restart,
`B_n ρ_λ = ρ_λ'`, `A'` own with `ψ₁(A') = ρ_λ'`), `D_λ = Vb.VbD S λ`, `T = Vb.vbT S λ`, `Θ = gxTh ρ_λ (ldAtR λ)`,
"IH(s)" every code `x < s` of `λ` moves (the premise of the wall).

* `ZpTopLawAll S` (**THE TOP LAW AT EVERY EXPONENT**, a statement, one restart at a time): at every restart `λ` with
  `A` own, `ψ₁(A) = ρ_λ`, every `b ∈ D_λ`, `ψ₂`-normal, `Ω₃ ∣ b`, `Ω₃ ≤ b` has
  `Θ(ψ₂ b) = ψ₁(A + 1 + ψ₂(T b))` (the bound `Xd.xdUpU` attained; `Xi.XiTopUp` is the case of the top atoms
  `β + W^{Ω_{k+3}+e}`, `e` a code);
* `zpBaseD` (**the base data move, for every normal `b ∈ D`**: `MvD b`, `MvD (T b)`, `T'(B_n b) = B_n(T b)`,
  `B_n b ∈ D_{λ'}`, `B_n b` normal; the proof of `Yj.yjD` with the base `b` itself);
* `zpDvd3` (**`Ω₃ ∣ b ⇒ Ω₃ ∣ B_n b`** for normal `b ∈ D` under IH(ψ₂ b); one induction on the Cantor normal form,
  `B_n Ω₃ = Ω₃`);
* `zpB3_le` (`Ω₃ ≤ b ⇒ Ω₃ ≤ B_n b`);
* `zpYjBase` (**THE BASE**: under `ZpTopLawAll`, at a window, every normal `Ω₃`-divisible `b ∈ D` with `Ω₃ ≤ b` and
  IH(ψ₂ b) is a `Yj.YjBase` with image `1 + ψ₂(T b)`, and `Ω₃ ∣ B_n b`; the proof of `Yj.yjTopBase` with the
  law taken from `ZpTopLawAll` at `λ` and at `λ'`).

No new axiom.  New definition: `ZpTopLawAll` (a statement name, no repo statement depends on it).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Rx

variable {S : InaccSeq.{0}}

/-- **THE TOP LAW AT EVERY EXPONENT** (one restart at a time): every `ψ₂`-normal `Ω₃`-divisible `b ∈ D_λ`,
`b ≥ Ω₃`, has `Θ(ψ₂ b) = ψ₁(A + 1 + ψ₂(T b))`. -/
def ZpTopLawAll (S : InaccSeq.{0}) : Prop :=
  ∀ (l ηx A : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
    A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l →
    ∀ b, VbD S l b → b ∈ S.CSet b (S.psi b (Om (1 + 1))) → Om (1 + 1 + 1) ∣ b → Om (1 + 1 + 1) ≤ b →
      gxTh (upsilon l) (ldAtR S l) (S.psi b (Om (1 + 1))) =
        S.psi (A + 1 + S.psi (vbT S l b) (Om (1 + 1))) (Om 1)

theorem zp_two_lt : (1 + 1 : Ordinal.{0}) < ω := by
  rw [one_add_one_eq_two]; exact Ordinal.nat_lt_omega0 2

/-- `B_n Ω₃ = Ω₃`, `Ω₃ ∈ MvD`. -/
theorem zpB3 (n : ℕ) : MvD S (Om (1 + 1 + 1)) ∧ Bc.bcB S n (Om (1 + 1 + 1)) = Om (1 + 1 + 1) :=
  Vs.vsW_D (s := 1 + 1) zp_two_lt

theorem zpOm3_opow (S : InaccSeq.{0}) : ω ^ Om (1 + 1 + 1 : Ordinal.{0}) = Om (1 + 1 + 1) :=
  Low.opow_eq_self_of_SC (zpOm3_SC S)

theorem zpOm2_dvd3 (S : InaccSeq.{0}) : Om (1 + 1 : Ordinal.{0}) ∣ Om (1 + 1 + 1) := by
  have h2 : ω ^ Om (1 + 1 : Ordinal.{0}) = Om (1 + 1) :=
    Low.opow_eq_self_of_SC ((InR_Om_succ (S := S) 1).SC S)
  rw [← h2, ← zpOm3_opow S]
  exact opow_dvd_opow ω (Om_le_Om.2 le_self_add)

section Win

variable {n : ℕ} {l l' A' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
  (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')

include hR h1 hr hl' hB

/-- **The base data move, for every normal `b ∈ D`.** -/
theorem zpBaseD {b : Ordinal.{0}} (hbD : VbD S l b) (hbn : b ∈ S.CSet b (S.psi b (Om (1 + 1))))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi b (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S b ∧ MvD S (vbT S l b) ∧ vbT S l' (Bc.bcB S n b) = Bc.bcB S n (vbT S l b) ∧
      VbD S l' (Bc.bcB S n b) ∧
      Bc.bcB S n b ∈ S.CSet (Bc.bcB S n b) (S.psi (Bc.bcB S n b) (Om (1 + 1))) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hl := hR.1
  obtain ⟨hX, hown, hρA, hX', -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  obtain ⟨hDb, hDT, hTmv⟩ := Xq.xqTMove (n := n) hl hX hl' hX' hown hρA IH b hbD hbn
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hTW : gxTh (upsilon l) (ldAtR S l) (S.psi b (Om (1 + 1))) ≤ vbW S l := by
    rw [vbW_eq hl hX]; exact gxTh_mono (psi_lt hκ2 b).le
  have hSC : SC (gxTh (upsilon l) (ldAtR S l) (S.psi b (Om (1 + 1)))) :=
    gxTh_SC hρSC (ldAt_GxAt _ _) (SC_psi hκ2 b) (hρ1.trans (psiS_bounds (S := S) b 1).1)
  obtain ⟨-, -, hBE, hK, -⟩ := vbT_move (n := n) hl hX hl' hX' hSC hTW (Xq.xqLeaf hl hX hl' hX' IH) hbD
    (Xq.xqTE hl hX hown hρA b hbD hbn)
  obtain ⟨hZ', hZ1'⟩ := vbZ hl' hX'
  have hlt : Bc.bcB S n b < Om ω := by
    rw [← hK]; exact rxL_lt_OmW hZ' hZ1' (ldAt_GxAt _ _) hBE
  have hH : Bc.bcB S n b ∈ cdHull S l' := by
    rw [← hK]
    show _ ∈ S.CSet (ConjT.Aη S (cdEta S l')) (upsilon l')
    refine rxL_memH hZ' hZ1' (ldAt_GxAt _ _) (vbW_SC hl' hX') le_rfl (ConjT.OmW_le_A S _)
      (fun g hg => ?_) _ hBE
    have hg' : g < gxTh (upsilon l') (ldAtR S l') (Om (1 + 1)) := by rw [← vbW_eq hl' hX']; exact hg
    obtain ⟨hc, hc2, -⟩ := Ru.ruInv_spec hg'
    exact (ldHull_iff hl' hX' hc2).2 hc
  have hn' := Yd.ydNormB n hDb hbn
  exact ⟨hDb, hDT, hTmv, ⟨hH, (psi_mono hκ2 hlt.le).2 hn', hlt⟩, hn'⟩

/-- **`Ω₃ ∣ b ⇒ Ω₃ ∣ B_n b`** for every normal `b ∈ D` under IH(ψ₂ b) (the members of `D ∩ Cl(b, ψ₂ b)`). -/
theorem zpDvd3 {b : Ordinal.{0}} (hbD : VbD S l b) (hbn : b ∈ S.CSet b (S.psi b (Om (1 + 1))))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi b (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    ∀ x, VbD S l x → x ∈ S.CSet b (S.psi b (Om (1 + 1))) → Om (1 + 1 + 1) ∣ x →
      Om (1 + 1 + 1) ∣ Bc.bcB S n x := by
  have hl := hR.1
  obtain ⟨hX, hown, hρA, hX', -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  have hTM := fun x (hx : VbD S l x) (hxC : x ∈ S.CSet b (S.psi b (Om (1 + 1)))) =>
    Xq.xqTMove (n := n) hl hX hl' hX' hown hρA IH x hx hxC
  obtain ⟨hD3, hB3⟩ := zpB3 (S := S) n
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IHx =>
  intro hxD hxC hdv
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [Bc.bcB_zero]; exact dvd_zero _
  obtain ⟨⟨hLD, hLC⟩, ⟨hrD, hrC⟩⟩ := Yj.yjParts hxD hxC
  obtain ⟨hDL, -, -⟩ := hTM _ hLD hLC
  obtain ⟨hDr, -, -⟩ := hTM _ hrD hrC
  obtain ⟨m, hm⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
  have hdm : x = ω ^ log ω x * m + x % ω ^ log ω x := by
    rw [← hm]; exact (Ordinal.div_add_mod x _).symm
  obtain ⟨hDo, hBo⟩ := ldB_opow (n := n) hDL
  obtain ⟨hDom, hBom⟩ := vbB_mulNat (n := n) hDo m
  obtain ⟨-, hBx⟩ := mvB_add (k := n) hDom hDr
  rw [← hdm] at hBx
  rw [hBx, hBom, hBo]
  have hWle : ω ^ Om (1 + 1 + 1 : Ordinal.{0}) ≤ x := by
    rw [zpOm3_opow S]; exact Ordinal.le_of_dvd hx0 hdv
  have hpL : Om (1 + 1 + 1 : Ordinal.{0}) ≤ log ω x := (Ordinal.opow_le_iff_le_log one_lt_omega0 hx0).1 hWle
  have hp' : Om (1 + 1 + 1 : Ordinal.{0}) ≤ Bc.bcB S n (log ω x) := by
    rcases hpL.lt_or_eq with h | h
    · have := ((mvB_lt_iff (k := n) hD3 hDL).2 h).le; rwa [hB3] at this
    · rw [← h, hB3]
  have hd3 : ∀ {L : Ordinal.{0}}, Om (1 + 1 + 1 : Ordinal.{0}) ≤ L → Om (1 + 1 + 1 : Ordinal.{0}) ∣ ω ^ L :=
    fun hL => by rw [← zpOm3_opow S]; exact opow_dvd_opow ω hL
  refine dvd_add (Dvd.dvd.mul_right (hd3 hp') _) ?_
  have hrlt : x % ω ^ log ω x < x :=
    (Ordinal.mod_lt x (opow_ne_zero _ omega0_ne_zero)).trans_le (opow_log_le_self ω hx0)
  refine IHx _ hrlt hrD hrC ?_
  have h2 : Om (1 + 1 + 1 : Ordinal.{0}) ∣ ω ^ log ω x * m := Dvd.dvd.mul_right (hd3 hpL) _
  rw [hdm] at hdv
  exact (Ordinal.dvd_add_iff h2).1 hdv

omit hR h1 hr hl' hB in
/-- `Ω₃ ≤ b ⇒ Ω₃ ≤ B_n b` on `MvD`. -/
theorem zpB3_le {b : Ordinal.{0}} (hDb : MvD S b) (h3 : Om (1 + 1 + 1) ≤ b) :
    Om (1 + 1 + 1) ≤ Bc.bcB S n b := by
  obtain ⟨hD3, hB3⟩ := zpB3 (S := S) n
  rcases h3.lt_or_eq with h | h
  · have := ((mvB_lt_iff (k := n) hD3 hDb).2 h).le; rwa [hB3] at this
  · rw [← h, hB3]

variable (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1))) (hρ' : S.psi A' (Om 1) = upsilon l')

include hA' hρ'

/-- **THE BASE**: every normal `Ω₃`-divisible `b ∈ D`, `b ≥ Ω₃`, is a base with a law at both ends
(image `1 + ψ₂(T b)`), given `ZpTopLawAll`; and `Ω₃ ∣ B_n b`. -/
theorem zpYjBase (hLaw : ZpTopLawAll S) {b : Ordinal.{0}} (hbD : VbD S l b)
    (hbn : b ∈ S.CSet b (S.psi b (Om (1 + 1)))) (hdv : Om (1 + 1 + 1) ∣ b) (h3 : Om (1 + 1 + 1) ≤ b)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi b (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    Yj.YjBase S n l l' A' b (1 + S.psi (vbT S l b) (Om (1 + 1))) ∧ Om (1 + 1 + 1) ∣ Bc.bcB S n b := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hl := hR.1
  obtain ⟨hX, hown, hρA, hX', -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  obtain ⟨hDb, hDT, hTmv, hbD', hbn'⟩ := zpBaseD hR h1 hr hl' hB hbD hbn IH
  have hdv' : Om (1 + 1 + 1) ∣ Bc.bcB S n b := zpDvd3 hR h1 hr hl' hB hbD hbn IH b hbD hbn hdv
  have h3' : Om (1 + 1 + 1) ≤ Bc.bcB S n b := zpB3_le hDb h3
  have hown2 : ∀ {c : Ordinal.{0}}, c ∈ S.CSet c (S.psi c (Om (1 + 1))) →
      ∀ d, d ≤ Om (1 + 1) → c ∈ S.CSet (c + d) (S.psi (c + d) (Om (1 + 1))) := fun hc d _ =>
    (psi_mono hκ2 (le_self_add : _ ≤ _ + d)).2 hc
  have hd2 : ∀ {c : Ordinal.{0}}, Om (1 + 1 + 1) ∣ c → Om (1 + 1) ∣ c := fun hc =>
    (zpOm2_dvd3 S).trans hc
  -- the `λ` side
  have hlaw := hLaw l _ _ hl hX hown hρA b hbD hbn hdv h3
  have hhi : S.psi (ConjT.Aη S (cdEta S l) + 1 + S.psi (vbT S l b) (Om (1 + 1))) (Om 1) < Bc.bcC S (n + 1) := by
    rw [← hlaw]; exact Yj.yjTh_hi hR h1 hr hl' hB (Yj.yjPsi2_leW hbD.2.2)
  obtain ⟨hDψ, hBψ, -⟩ := Xq.xqSigMove hl hX hown hρA hA' hρ' h1.le hB hbD hbn hDT hhi
  have h1L : (1 : Ordinal.{0}) < Nc.ncL S ω := one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S ω))
  have hB1 : Bc.bcB S n 1 = 1 := Bc.bcB_fixN n 1 (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  obtain ⟨hDD, hBD⟩ := mvB_add (k := n) (mvD_of_lt h1L) hDψ
  rw [hB1, hBψ] at hBD
  have hat := Xq.xqOwn hl hX hown hρA hbD hbn
  -- the `λ'` side
  have hlaw' := hLaw l' _ _ hl' hX' hA' hρ' _ hbD' hbn' hdv' h3'
  have hat' := Xq.xqOwn hl' hX' hA' hρ' hbD' hbn'
  rw [hTmv] at hlaw' hat'
  refine ⟨⟨hbD, hd2 hdv, hown2 hbn, hDb, hDD, by rw [← add_assoc]; exact hat, by rw [← add_assoc]; exact hlaw,
    hbD', hd2 hdv', hown2 hbn', by rw [hBD, ← add_assoc]; exact hat', by rw [hBD, ← add_assoc]; exact hlaw'⟩, hdv'⟩

end Win

end Googology.Trans.PoR.InaccPsi.R2.Zp

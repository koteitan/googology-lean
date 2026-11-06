import Googology.Trans.PoR.InaccPsi.R2.KzBlk

/-!
# Kz: THE BAND LEMMAS FOR THE MOVE (`Ky.kyDvd`, `Ky.kyD` on `D_K`, the band bound `Ω_ω·2`)

`B_n = Bc.bcB S n`, "window", `T_K`, `D_K` as before, `IH(s)` with the band bound `B_n x < P′`.

* `kzW2` (`x < Ω_ω·2`, `y < Ω_ω ⇒ x + y < Ω_ω·2`), `kzB_W2` (`B_n x < Ω_ω·2` for `x ∈ MvD`, `x < Ω_ω·2`);
* `kzParts` (`Yj.yjParts` on `D_K`);
* `kzReach` (**every atom `s < P′` of the hull is `ψ₂(d)`, `d ∈ D_K` normal, `d < Ω_ω·2`**);
* `kzDvd` (**`P ∣ x ⇒ P ∣ B_n x`** for `x ∈ D_K ∩ Cl(a₀, ψ₂ a₀)`, `a₀ ≤ A`, every `ε`-number `P ∈ MvD` fixed by `B_n`,
  under IH(ψ₂ a₀));
* `kzD` (**`B_n x ∈ D_{K,λ'}`** for a normal `x ∈ D_K ∩ Cl(a₀, ψ₂ a₀)`, `x < Ω_ω·2`, under IH(ψ₂ a₀)).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kz

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Rx

variable {S : InaccSeq.{0}}

theorem kzW2 {x y : Ordinal.{0}} (hx : x < Om ω + Om ω) (hy : y < Om ω) : x + y < Om ω + Om ω := by
  rcases lt_or_ge x (Om ω) with h | h
  · exact (vkOmW.1.isPrincipal h hy).trans_le le_self_add
  · obtain ⟨z, rfl⟩ := exists_add_of_le h
    have hz : z < Om ω := (add_lt_add_iff_left _).1 hx
    rw [add_assoc]; exact (add_lt_add_iff_left _).2 (vkOmW.1.isPrincipal hz hy)

theorem kzB_W2D {n : ℕ} : MvD S (Om ω + Om ω) ∧ Bc.bcB S n (Om ω + Om ω) = Om ω + Om ω := by
  obtain ⟨hDW, hBW⟩ := Wr.wrB_OmW (S := S) (n := n)
  obtain ⟨hDa, hBa⟩ := mvB_add (k := n) hDW hDW
  exact ⟨hDa, by rw [hBa, hBW]⟩

theorem kzB_W2 {n : ℕ} {x : Ordinal.{0}} (hx : MvD S x) (hxW : x < Om ω + Om ω) :
    Bc.bcB S n x < Om ω + Om ω := by
  obtain ⟨hD, hB⟩ := kzB_W2D (S := S) (n := n)
  have h := (mvB_lt_iff (k := n) hx hD).2 hxW
  rwa [hB] at h

theorem kzParts {l K a b x : Ordinal.{0}} (hx : VbDK S l K x) (hxC : x ∈ S.CSet a b) :
    (VbDK S l K (log ω x) ∧ log ω x ∈ S.CSet a b) ∧
      (VbDK S l K (x % ω ^ log ω x) ∧ x % ω ^ log ω x ∈ S.CSet a b) :=
  ⟨⟨⟨(rxCDec x hx.1).2, (rxCDec x hx.2.1).2, (log_le_self ω x).trans_lt hx.2.2⟩, (rxCDec x hxC).2⟩,
    ⟨⟨vbC_rem hx.1, vbC_rem hx.2.1, (Ordinal.mod_le _ _).trans_lt hx.2.2⟩, vbC_rem hxC⟩⟩

/-- **Every atom `s < P′` of the hull is `ψ₂(d)`, `d ∈ D_K` normal, `d < Ω_ω·2`.** -/
theorem kzReach {l ηx K : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hW2K : Om ω + Om ω < K) {s : Ordinal.{0}} (hs : s ∈ ldAtR S l) (hsP : s < Nc.ncPp S) :
    ∃ d, VbDK S l K d ∧ S.psi d (Om (1 + 1)) = s ∧ d ∈ S.CSet d (S.psi d (Om (1 + 1))) ∧
      d < Om ω + Om ω := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hZ, hZ1⟩ := vbZ hl hX
  obtain ⟨a0, ha0C, ha0A, rfl⟩ := hs
  set g := S.psi a0 (Om (1 + 1)) with hgdef
  have hρL : upsilon l ≤ S.Lam := (hZ1.trans (Om_lt_Om.2 (lt_add_one 1))).le.trans Xd.xdOm2_le_Lam
  have ha0L : a0 < S.Lam := lt_Lam_of_mem hρL ha0C
  set d := S.M a0 g a0 with hddef
  have hψ : S.psi d (Om (1 + 1)) = g := psi_M_eq hκ2 ha0L
  have hn : d ∈ S.CSet d (S.psi d (Om (1 + 1))) := M_mem_self hκ2 ha0L
  have hρg : upsilon l ≤ g := (hZ1.trans (psiS_bounds (S := S) a0 1).1).le
  have hdH : d ∈ cdHull S l :=
    M_mem_of_Good (closed_CSet ha0A.le hρL) a0 ha0L (MQ_of_mem_CSet ha0A.le hρg hρL ha0C).1.1
  have hdW : d < Om ω + Om ω := by
    by_contra hc
    push Not at hc
    exact absurd hsP (not_lt.2 (hψ ▸ (psi_mono hκ2 hc).1))
  have hdK : d < K := hdW.trans hW2K
  exact ⟨d, ⟨hdH, (psi_mono hκ2 hdK.le).2 hn, hdK⟩, hψ, hn, hdW⟩

section Win

variable {n : ℕ} {l l' K : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
  (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
  (hKB : KzB S K)

include hR h1 hr hl' hB hKB

/-- **`P ∣ x ⇒ P ∣ B_n x`** for every `x ∈ D_K ∩ Cl(a₀, ψ₂ a₀)`, under IH(ψ₂ a₀). -/
theorem kzDvd {a₀ P : Ordinal.{0}} (haA : a₀ ≤ ConjT.Aη S (cdEta S l)) (hPe : ω ^ P = P)
    (hDP : MvD S P) (hBP : Bc.bcB S n P = P)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi a₀ (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Nc.ncPp S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    ∀ x, VbDK S l K x → x ∈ S.CSet a₀ (S.psi a₀ (Om (1 + 1))) → P ∣ x → P ∣ Bc.bcB S n x := by
  have hl := hR.1
  obtain ⟨hX, hown, hρA, hX', -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  have hTM := fun x (hx : VbDK S l K x) (hxC : x ∈ S.CSet a₀ (S.psi a₀ (Om (1 + 1)))) =>
    kzTMove (n := n) hl hX hl' hX' hKB hown hρA haA IH x hx hxC
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IHx =>
  intro hxD hxC hdv
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [Bc.bcB_zero]; exact dvd_zero _
  obtain ⟨⟨hLD, hLC⟩, ⟨hrD, hrC⟩⟩ := kzParts hxD hxC
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
  have hWle : P ≤ x := Ordinal.le_of_dvd hx0 hdv
  have hpL : P ≤ log ω x :=
    (Ordinal.opow_le_iff_le_log one_lt_omega0 hx0).1 (by rw [hPe]; exact hWle)
  have hWo : P ≤ ω ^ log ω x := by
    have h := opow_le_opow_right (a := ω) omega0_pos hpL; rwa [hPe] at h
  have hBWo : Bc.bcB S n P ≤ Bc.bcB S n (ω ^ log ω x) := by
    rcases hWo.lt_or_eq with h | h
    · exact ((mvB_lt_iff hDP hDo).2 h).le
    · rw [h]
  rw [hBP, hBo] at hBWo
  have hp' : P ≤ Bc.bcB S n (log ω x) :=
    (opow_le_opow_iff_right one_lt_omega0).1 (by rw [hPe]; exact hBWo)
  have hd1 : P ∣ ω ^ Bc.bcB S n (log ω x) := by
    have h := opow_dvd_opow ω hp'; rwa [hPe] at h
  refine dvd_add (Dvd.dvd.mul_right hd1 _) ?_
  have hrlt : x % ω ^ log ω x < x :=
    (Ordinal.mod_lt x (opow_ne_zero _ omega0_ne_zero)).trans_le (opow_log_le_self ω hx0)
  refine IHx _ hrlt hrD hrC ?_
  have hd2 : P ∣ ω ^ log ω x := by
    have h := opow_dvd_opow ω hpL; rwa [hPe] at h
  have h2 : P ∣ ω ^ log ω x * m := Dvd.dvd.mul_right hd2 _
  rw [hdm] at hdv
  exact (Ordinal.dvd_add_iff h2).1 hdv

/-- **`B_n x ∈ D_{K,λ'}`** for a normal `x ∈ D_K ∩ Cl(a₀, ψ₂ a₀)`, `x < Ω_ω·2`, under IH(ψ₂ a₀). -/
theorem kzD {a₀ x : Ordinal.{0}} (hW2K : Om ω + Om ω < K) (haA : a₀ ≤ ConjT.Aη S (cdEta S l))
    (hx : VbDK S l K x) (hxC : x ∈ S.CSet a₀ (S.psi a₀ (Om (1 + 1))))
    (hxn : x ∈ S.CSet x (S.psi x (Om (1 + 1)))) (hxW : x < Om ω + Om ω)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi a₀ (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Nc.ncPp S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    VbDK S l' K (Bc.bcB S n x) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hl := hR.1
  obtain ⟨hX, hown, hρA, hX', -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  obtain ⟨-, hAW'⟩ := Zj.zjWin_A hR h1 hr hl' hB
  obtain ⟨hDx, hDT, hBE, hκ', -⟩ := kzTMove (n := n) hl hX hl' hX' hKB hown hρA haA IH x hx hxC
  obtain ⟨hZ', hZ1'⟩ := vbZ hl' hX'
  have hBxW : Bc.bcB S n x < Om ω + Om ω := kzB_W2 hDx hxW
  have hBxK : Bc.bcB S n x < K := hBxW.trans hW2K
  have hTn := kzTr hl hX hKB hx hx hxn
  have hyn := Yd.ydNormB n hDT hTn
  have hH : Bc.bcB S n x ∈ cdHull S l' := by
    rw [← hκ']
    show _ ∈ S.CSet (ConjT.Aη S (cdEta S l')) (upsilon l')
    refine kzL_memL hZ' hZ1' (ldAt_GxAt _ _) hKB (vbW_SC hl' hX') le_rfl hBE
      ((le_of_eq hκ').trans (hBxW.le.trans hAW')) (fun g hg => ?_) _ hBE ⟨_, le_rfl, hyn⟩
    have hg' : g < gxTh (upsilon l') (ldAtR S l') (Om (1 + 1)) := by rw [← vbW_eq hl' hX']; exact hg
    obtain ⟨hc, hc2, -⟩ := Ru.ruInv_spec hg'
    exact (ldHull_iff hl' hX' hc2).2 hc
  exact ⟨hH, (psi_mono hκ2 hBxK.le).2 (Yd.ydNormB n hDx hxn), hBxK⟩

end Win

end Googology.Trans.PoR.InaccPsi.R2.Kz

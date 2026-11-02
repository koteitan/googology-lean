import Googology.Trans.PoR.InaccPsi.R2.YjBase

/-!
# The block move above any base with a law at both ends

`B_n = Bc.bcB S n`, "window" as in `Yd.ydBaseMove`, `A = A_{η_λ}`, `A'` own with `ψ₁(A') = ρ_{λ'}`,
`Θ = gxTh ρ_λ (ldAtR λ)`, `F^a = ψ₂(a + Ω₂)` (`Ld.ldTop`).  A **base with a law at both ends** is `a ∈ D_λ`,
`Ω₂ ∣ a`, own for the offsets `d ≤ Ω₂`, `a ∈ MvD`, with `Θ(ψ₂ a) = ψ₁(A + D)` (`A + D` own, `D ∈ MvD`), and the same
data at `λ'` for `B_n a` with `Θ'(ψ₂(B_n a)) = ψ₁(A' + B_n D)`.

* `yjBlkMove` (**EVERY ATOM OF THE BLOCK MOVES**: for every code `c < F^a` of `λ`, under the moves of the codes below
  `ψ₂(a + c)`: `MvD ψ₂(a+c)`, `B_n ψ₂(a+c) = ψ₂(B_n a + B_n c) ∈ At_{λ'}`, `Θ'(B_n ψ₂(a+c)) = B_n Θ(ψ₂(a+c))`);
* `yjBlkNext` (**THE NEXT BASE**: `F^a` moves (no move of lower codes needed), and `a + Ω₂` is again a base
  with a law at both ends, image `D + Ω₁`);
* `yjBlkFin` (**every atom `ψ₂(a + Ω₂·m + c)`, `m < ω`, `c < F^{a+Ω₂·m}`, moves**, by induction on `m`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Rx

variable {S : InaccSeq.{0}}

/-- **A base with a law at both ends** (data at `λ` and at `λ'`). -/
structure YjBase (S : InaccSeq.{0}) (n : ℕ) (l l' A' a D : Ordinal.{0}) : Prop where
  D_a : VbD S l a
  dvd : Om (1 + 1) ∣ a
  own : ∀ d, d ≤ Om (1 + 1) → a ∈ S.CSet (a + d) (S.psi (a + d) (Om (1 + 1)))
  mv_a : MvD S a
  mv_D : MvD S D
  hat : ConjT.Aη S (cdEta S l) + D ∈
    S.CSet (ConjT.Aη S (cdEta S l) + D) (S.psi (ConjT.Aη S (cdEta S l) + D) (Om 1))
  law : gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1))) = S.psi (ConjT.Aη S (cdEta S l) + D) (Om 1)
  D_a' : VbD S l' (Bc.bcB S n a)
  dvd' : Om (1 + 1) ∣ Bc.bcB S n a
  own' : ∀ d, d ≤ Om (1 + 1) → Bc.bcB S n a ∈
    S.CSet (Bc.bcB S n a + d) (S.psi (Bc.bcB S n a + d) (Om (1 + 1)))
  hat' : A' + Bc.bcB S n D ∈ S.CSet (A' + Bc.bcB S n D) (S.psi (A' + Bc.bcB S n D) (Om 1))
  law' : gxTh (upsilon l') (ldAtR S l') (S.psi (Bc.bcB S n a) (Om (1 + 1))) =
    S.psi (A' + Bc.bcB S n D) (Om 1)

theorem yjBA {l a : Ordinal.{0}} (ha : VbD S l a) : a + Om (1 + 1) < ConjT.Aη S (cdEta S l) :=
  (vkOmW.1.isPrincipal ha.2.2 ldOm2_lt_OmW).trans_le (ConjT.OmW_le_A S _)

theorem yjPsi2_leW {x : Ordinal.{0}} (hx : x < Om ω) : S.psi x (Om (1 + 1)) ≤ Lj.ljThP S :=
  ((psi_mono (InR_Om_succ 1) hx.le).1).trans Lj.ljTh_lt_ThP.le

theorem yjPsi2_le {a c : Ordinal.{0}} (ha : a < Om ω) (hc : c < Om (1 + 1)) :
    S.psi (a + c) (Om (1 + 1)) ≤ Lj.ljThP S :=
  yjPsi2_leW (vkOmW.1.isPrincipal ha (hc.trans ldOm2_lt_OmW))

/-- `a + Ω₂·m`. -/
theorem yjMulOm2 {a : Ordinal.{0}} (m : ℕ) : a + Om (1 + 1) * ((m + 1 : ℕ) : Ordinal.{0}) =
    a + Om (1 + 1) * (m : Ordinal.{0}) + Om (1 + 1) := by
  rw [Nat.cast_succ, mul_add_one, add_assoc]

section Win

variable {n : ℕ} {l l' A' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
  (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
  (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1))) (hρ' : S.psi A' (Om 1) = upsilon l')

include hR h1 hr hl' hB hA' hρ'

/-- `B_n ψ₁(A + d) = ψ₁(A' + B_n d)` for own `A + d` with `ψ₁(A + d) < c_{n+1}`. -/
theorem yjPsi1 {d : Ordinal.{0}} (hDd : MvD S d)
    (hown : ConjT.Aη S (cdEta S l) + d ∈
      S.CSet (ConjT.Aη S (cdEta S l) + d) (S.psi (ConjT.Aη S (cdEta S l) + d) (Om 1)))
    (hhi : S.psi (ConjT.Aη S (cdEta S l) + d) (Om 1) < Bc.bcC S (n + 1)) :
    Bc.bcB S n (S.psi (ConjT.Aη S (cdEta S l) + d) (Om 1)) = S.psi (A' + Bc.bcB S n d) (Om 1) := by
  obtain ⟨hX, -, -, -, -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  obtain ⟨hg, -, -, hpv⟩ := cdEta_pv_spec (S := S) hR.1.1 hX
  obtain ⟨A'', hA'', hBρ, hBσ⟩ := ldB_psi_add hg (by rw [hpv]; exact h1.le) hDd hown hhi
  have e : A'' = A' := mxPsi_inj hA'' hA' (by rw [← hBρ, hpv, hB, hρ'])
  rw [hBσ, e]

omit hA' hρ' in
/-- `Θ(s) < c_{n+1}` for every `s ≤ θ⁺`. -/
theorem yjTh_hi {s : Ordinal.{0}} (hs : s ≤ Lj.ljThP S) :
    gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) := by
  obtain ⟨hX, hown, -, -, -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  rw [← ldTheta hR.1 hX (hs.trans Lj.ljThP_lt_Om2.le)]
  exact ((Lj.ljTheta_lt_delta hR.1 hX hown hs).trans_le (cdR_ge S l)).trans hr

/-- **EVERY ATOM OF THE BLOCK MOVES** above a base with a law at both ends. -/
theorem yjBlkMove {a D : Ordinal.{0}} (hb : YjBase S n l l' A' a D) {c : Ordinal.{0}}
    (hc : GxCl (upsilon l) (ldAtR S l) c) (hcF : c < ldTop S a)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (a + c) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S (S.psi (a + c) (Om (1 + 1))) ∧
      Bc.bcB S n (S.psi (a + c) (Om (1 + 1))) = S.psi (Bc.bcB S n a + Bc.bcB S n c) (Om (1 + 1)) ∧
      Bc.bcB S n (S.psi (a + c) (Om (1 + 1))) ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n (S.psi (a + c) (Om (1 + 1)))) =
        Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) (S.psi (a + c) (Om (1 + 1)))) := by
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  obtain ⟨hX, -, -, hX', -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  have hl := hR.1
  set A := ConjT.Aη S (cdEta S l) with hAdef
  have hc2 : c < Om (1 + 1) := hcF.trans (ldTop_lt_Om2 a)
  have hcs : c < S.psi (a + c) (Om (1 + 1)) := ldTop_gt hb.own hb.dvd hcF
  obtain ⟨hDc, hBc, -, hΘc, hmvc⟩ := IH c hc hcs
  -- the reading at `λ`
  have hstep := ldBlk_step hl hX hb.own hb.dvd hb.D_a.1 (yjBA hb.D_a) hb.hat hb.law c hc hcF
  have hΘlt : gxTh (upsilon l) (ldAtR S l) c < S.psi (A + D + gxTh (upsilon l) (ldAtR S l) c) (Om 1) := by
    rw [← hstep]; exact gxTh_lt hc hcs
  have hown : A + (D + gxTh (upsilon l) (ldAtR S l) c) ∈ S.CSet (A + (D + gxTh (upsilon l) (ldAtR S l) c))
      (S.psi (A + (D + gxTh (upsilon l) (ldAtR S l) c)) (Om 1)) := by
    rw [← add_assoc]
    exact CSet.add_mem ((psi_mono hκ1 le_self_add).2 hb.hat) (CSet.of_lt hΘlt)
  -- `B_n` on the atom
  have h1L : (1 : Ordinal.{0}) < Nc.ncL S ω := one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S ω))
  have hB1 : Bc.bcB S n 1 = 1 := Bc.bcB_fixN n 1 (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  obtain ⟨hDac, hBac⟩ := mvB_add (k := n) hb.mv_a hDc
  obtain ⟨hDs, hBs, -⟩ := Ug.ugB_psiS (n := n) (s := 1) one_ne_zero (mvD_of_lt h1L) hDac (ldOwn hb.own hb.dvd hcF)
  rw [hB1, hBac] at hBs
  -- `B_n c < F^{B_n a}`
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hDa2, hBa2⟩ := mvB_add (k := n) hb.mv_a hD2
  obtain ⟨hDF, hBF, -⟩ := Ug.ugB_psiS (n := n) (s := 1) one_ne_zero (mvD_of_lt h1L) hDa2
    (CSet.add_mem (hb.own _ le_rfl) (mxOm2_mem _ _))
  rw [hB1, hBa2, hB2] at hBF
  have hBcF : Bc.bcB S n c < ldTop S (Bc.bcB S n a) := by
    have h := (mvB_lt_iff (k := n) hDc hDF).2 hcF
    rw [hBF] at h; exact h
  -- the reading at `λ'`
  have hstep' := ldBlk_step hl' hX' hb.own' hb.dvd' hb.D_a'.1 (yjBA hb.D_a') hb.hat' hb.law' _ hBc hBcF
  have hat' := ldBlk_atom hl' hX' hb.D_a'.1 (yjBA hb.D_a') hBc hBcF
  -- `B_n` on the reading
  have hDΘ : MvD S (gxTh (upsilon l) (ldAtR S l) c) := mvD_of_lt (hΘc.trans (Bc.bcC_lt S (n + 1)))
  obtain ⟨hDd, hBd⟩ := mvB_add (k := n) hb.mv_D hDΘ
  have hhi : S.psi (A + (D + gxTh (upsilon l) (ldAtR S l) c)) (Om 1) < Bc.bcC S (n + 1) := by
    rw [← add_assoc, ← hstep]; exact yjTh_hi hR h1 hr hl' hB (yjPsi2_le hb.D_a.2.2 hc2)
  have hψ := yjPsi1 hR h1 hr hl' hB hA' hρ' hDd hown hhi
  refine ⟨hDs, hBs, hBs ▸ hat', ?_⟩
  rw [hBs, hstep', hmvc, hstep, add_assoc (ConjT.Aη S (cdEta S l)), hψ, hBd, ← add_assoc]

/-- **THE NEXT BASE**: `F^a` moves, and `a + Ω₂` is a base with a law at both ends with image `D + Ω₁`. -/
theorem yjBlkNext {a D : Ordinal.{0}} (hb : YjBase S n l l' A' a D)
    (hW : a + Om (1 + 1) < Om ω) :
    MvD S (ldTop S a) ∧ Bc.bcB S n (ldTop S a) = ldTop S (Bc.bcB S n a) ∧
      Bc.bcB S n (ldTop S a) ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n (ldTop S a)) =
        Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) (ldTop S a)) ∧
      YjBase S n l l' A' (a + Om (1 + 1)) (D + Om 1) ∧
      Bc.bcB S n (a + Om (1 + 1)) = Bc.bcB S n a + Om (1 + 1) := by
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hX, -, -, hX', -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  have hl := hR.1
  set A := ConjT.Aη S (cdEta S l) with hAdef
  have h1L : (1 : Ordinal.{0}) < Nc.ncL S ω := one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S ω))
  have hB1 : Bc.bcB S n 1 = 1 := Bc.bcB_fixN n 1 (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hDa2, hBa2⟩ := mvB_add (k := n) hb.mv_a hD2
  rw [hB2] at hBa2
  obtain ⟨hDF, hBF, hnF'⟩ := Ug.ugB_psiS (n := n) (s := 1) one_ne_zero (mvD_of_lt h1L) hDa2
    (CSet.add_mem (hb.own _ le_rfl) (mxOm2_mem _ _))
  rw [hB1, hBa2] at hBF hnF'
  have hnext := ldBlk_next hl hX hb.own hb.dvd hb.D_a.1 (yjBA hb.D_a) hb.hat hb.law
  have hnext' := ldBlk_next hl' hX' hb.own' hb.dvd' hb.D_a'.1 (yjBA hb.D_a') hb.hat' hb.law'
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  obtain ⟨hDd, hBd⟩ := mvB_add (k := n) hb.mv_D hDO
  rw [hBO] at hBd
  have hOm1 : ∀ x, Om 1 ∈ S.CSet x (S.psi x (Om 1)) := fun x => CSet.Om_mem (CSet.one_mem _ _)
  have hown : A + (D + Om 1) ∈ S.CSet (A + (D + Om 1)) (S.psi (A + (D + Om 1)) (Om 1)) := by
    rw [← add_assoc]; exact CSet.add_mem ((psi_mono hκ1 le_self_add).2 hb.hat) (hOm1 _)
  have hown' : A' + Bc.bcB S n (D + Om 1) ∈ S.CSet (A' + Bc.bcB S n (D + Om 1))
      (S.psi (A' + Bc.bcB S n (D + Om 1)) (Om 1)) := by
    rw [hBd, ← add_assoc]; exact CSet.add_mem ((psi_mono hκ1 le_self_add).2 hb.hat') (hOm1 _)
  have hFle : ldTop S a ≤ Lj.ljThP S := yjPsi2_leW hW
  have hhi : S.psi (A + (D + Om 1)) (Om 1) < Bc.bcC S (n + 1) := by
    have h := yjTh_hi hR h1 hr hl' hB hFle
    rwa [hnext, add_assoc] at h
  have hψ := yjPsi1 hR h1 hr hl' hB hA' hρ' hDd hown hhi
  have hWa' : Bc.bcB S n a + Om (1 + 1) < Om ω := vkOmW.1.isPrincipal hb.D_a'.2.2 ldOm2_lt_OmW
  have hlawN : gxTh (upsilon l) (ldAtR S l) (S.psi (a + Om (1 + 1)) (Om (1 + 1))) =
      S.psi (A + (D + Om 1)) (Om 1) := by
    rw [← add_assoc]; exact hnext
  have hlawN' : gxTh (upsilon l') (ldAtR S l') (S.psi (Bc.bcB S n (a + Om (1 + 1))) (Om (1 + 1))) =
      S.psi (A' + Bc.bcB S n (D + Om 1)) (Om 1) := by
    rw [hBa2, hBd, ← add_assoc]; exact hnext'
  have hBFt : Bc.bcB S n (ldTop S a) = ldTop S (Bc.bcB S n a) := hBF
  refine ⟨hDF, hBFt, hBFt ▸ ldBlk_top_atom hb.D_a'.1 (yjBA hb.D_a'), ?_, ⟨?_, dvd_add hb.dvd (dvd_refl _),
    fun d _ => ?_, hDa2, hDd, hown, hlawN, ?_, ?_, fun d _ => ?_, hown', hlawN'⟩, hBa2⟩
  · rw [hBFt]
    show gxTh (upsilon l') (ldAtR S l') (S.psi (Bc.bcB S n a + Om (1 + 1)) (Om (1 + 1))) =
      Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) (S.psi (a + Om (1 + 1)) (Om (1 + 1))))
    rw [hlawN, hψ, hBd, ← add_assoc]; exact hnext'
  · exact ⟨CSet.add_mem hb.D_a.1 (mxOm2_mem _ _), CSet.add_mem hb.D_a.2.1 (mxOm2_mem _ _), hW⟩
  · exact CSet.add_mem ((psi_mono hκ2 le_self_add).2 (hb.own _ le_rfl)) (mxOm2_mem _ _)
  · rw [hBa2]; exact ⟨CSet.add_mem hb.D_a'.1 (mxOm2_mem _ _), CSet.add_mem hb.D_a'.2.1 (mxOm2_mem _ _), hWa'⟩
  · rw [hBa2]; exact dvd_add hb.dvd' (dvd_refl _)
  · rw [hBa2]; exact CSet.add_mem ((psi_mono hκ2 le_self_add).2 (hb.own' _ le_rfl)) (mxOm2_mem _ _)

/-- **EVERY BASE `a + Ω₂·m` IS A BASE WITH A LAW AT BOTH ENDS** (image `D + Ω₁·m`), under the moves of the codes below
`ψ₂(a + Ω₂·m)`, and `B_n(a + Ω₂·m) = B_n a + Ω₂·m`. -/
theorem yjBlkBase {a D : Ordinal.{0}} (hb : YjBase S n l l' A' a D) (hW : a + Om (1 + 1) * ω < Om ω) :
    ∀ m : ℕ, (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (a + Om (1 + 1) * (m : Ordinal.{0})) (Om (1 + 1)) →
      MvD S x ∧ GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      YjBase S n l l' A' (a + Om (1 + 1) * (m : Ordinal.{0})) (D + Om 1 * (m : Ordinal.{0})) ∧
      Bc.bcB S n (a + Om (1 + 1) * (m : Ordinal.{0})) = Bc.bcB S n a + Om (1 + 1) * (m : Ordinal.{0})
  | 0 => fun _ => by
    simp only [Nat.cast_zero, mul_zero, add_zero, and_true]; exact hb
  | m + 1 => fun IH => by
    have hlt : a + Om (1 + 1) * ((m + 1 : ℕ) : Ordinal.{0}) < a + Om (1 + 1) * ω :=
      (add_lt_add_iff_left a).2 ((mul_lt_mul_iff_right₀ ldOm2_SC.1).2 (natCast_lt_omega0 _))
    have hle : S.psi (a + Om (1 + 1) * (m : Ordinal.{0})) (Om (1 + 1)) ≤
        S.psi (a + Om (1 + 1) * ((m + 1 : ℕ) : Ordinal.{0})) (Om (1 + 1)) :=
      (psi_mono (InR_Om_succ 1) ((add_le_add_iff_left a).2
        (mul_le_mul_right (by exact_mod_cast Nat.le_succ m) _))).1
    obtain ⟨hbm, hBm⟩ := yjBlkBase hb hW m fun x hx hxs => IH x hx (hxs.trans_le hle)
    have hWm : a + Om (1 + 1) * (m : Ordinal.{0}) + Om (1 + 1) < Om ω := by
      rw [← yjMulOm2]; exact hlt.trans hW
    obtain ⟨-, -, -, -, hbn, hBn⟩ := yjBlkNext hR h1 hr hl' hB hA' hρ' hbm hWm
    rw [yjMulOm2, Nat.cast_succ, mul_add_one, ← add_assoc]
    refine ⟨hbn, ?_⟩
    rw [hBn, hBm, add_assoc, mul_add_one]

/-- **EVERY ATOM `ψ₂(a + Ω₂·m + c)` MOVES** (`m < ω`, `c < F^{a+Ω₂·m}` a code), under the moves of the codes below it. -/
theorem yjBlkFin {a D : Ordinal.{0}} (hb : YjBase S n l l' A' a D) (hW : a + Om (1 + 1) * ω < Om ω) (m : ℕ)
    {c : Ordinal.{0}} (hc : GxCl (upsilon l) (ldAtR S l) c)
    (hcF : c < ldTop S (a + Om (1 + 1) * (m : Ordinal.{0})))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x →
      x < S.psi (a + Om (1 + 1) * (m : Ordinal.{0}) + c) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S (S.psi (a + Om (1 + 1) * (m : Ordinal.{0}) + c) (Om (1 + 1))) ∧
      Bc.bcB S n (S.psi (a + Om (1 + 1) * (m : Ordinal.{0}) + c) (Om (1 + 1))) ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n (S.psi (a + Om (1 + 1) * (m : Ordinal.{0}) + c) (Om (1 + 1)))) =
        Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) (S.psi (a + Om (1 + 1) * (m : Ordinal.{0}) + c) (Om (1 + 1)))) := by
  have hle : S.psi (a + Om (1 + 1) * (m : Ordinal.{0})) (Om (1 + 1)) ≤
      S.psi (a + Om (1 + 1) * (m : Ordinal.{0}) + c) (Om (1 + 1)) :=
    (psi_mono (InR_Om_succ 1) le_self_add).1
  obtain ⟨hbm, -⟩ := yjBlkBase hR h1 hr hl' hB hA' hρ' hb hW m fun x hx hxs => IH x hx (hxs.trans_le hle)
  obtain ⟨hD, -, hat, hmv⟩ := yjBlkMove hR h1 hr hl' hB hA' hρ' hbm hc hcF IH
  exact ⟨hD, hat, hmv⟩

end Win

end Googology.Trans.PoR.InaccPsi.R2.Yj

#print axioms Googology.Trans.PoR.InaccPsi.R2.Yj.yjPsi1
#print axioms Googology.Trans.PoR.InaccPsi.R2.Yj.yjBlkMove
#print axioms Googology.Trans.PoR.InaccPsi.R2.Yj.yjBlkNext
#print axioms Googology.Trans.PoR.InaccPsi.R2.Yj.yjBlkBase
#print axioms Googology.Trans.PoR.InaccPsi.R2.Yj.yjBlkFin

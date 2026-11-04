import Googology.Trans.PoR.InaccPsi.R2.YtTest
import Googology.Trans.PoR.InaccPsi.R2.VqY3
import Googology.Trans.PoR.InaccPsi.R2.VnWall

/-!
# The first ψ₃-offsets: every atom `ψ₂(a) ≤ s < ψ₂(a + Y₃·ω)` above a base `a ≥ Ω₃` moves

`Y₃ = ψ_{Ω₃}(Ω₃)` (`Ug.ugY`), `Y₂ = ψ_{Ω₂}(Ω₂)`, `B_n = Bc.bcB S n`, "window" as in `Yj.yjBlkMove`, `A'` own with
`ψ₁(A') = ρ_{λ'}`, `Yj.YjBase λ λ' A' a D` a base with a law at both ends (`Θ(ψ₂ a) = ψ₁(A + D)`), "IH(s)" the premise
of WallBelow at `s`.  The leaf `skPsi3Off` asks the atoms `ψ₂(a + Y₃) ≤ s < ψ₂(a + Ω₃)`; this module gives

* `yyY3_D`, `yyY2_D` (`B_n` fixes `Y₃` and `Y₂`);
* `yyY3Step` (**`a + Y₃` IS AGAIN A BASE WITH A LAW AT BOTH ENDS**, image `D + Y₂`, and `B_n(a + Y₃) = B_n a + Y₃`,
  for every base `a ≥ Ω₃` with `Y₃ ∣ a`, `Y₃ ∣ B_n a`; from the base-relative top `Vq.vqTopY3` at `λ` and at `λ'`;
  no IH needed);
* `yyY3Fin` (the same for `a + Y₃·m`, image `D + Y₂·m`, every `m < ω`);
* `yyY3Move` (**EVERY ATOM `ψ₂(a) ≤ s < ψ₂(a + Y₃·ω)` MOVES** under IH(s): the offsets `δ < Y₃·ω`, i.e. the part
  `[Y₃, Y₃·ω)` of `skPsi3Off`);
* `yyBaseSmall` (**a base `a < Ω₃` with `Y₃ ∣ a` is `0`**: `Vn.vnNoSelf`), `yyPsi3OffLow` (**`skPsi3Off` holds for
  every base `a < Ω₃`**: there the region `[ψ₂(a + Y₃), ψ₂(a + Ω₃))` is empty, `Vn.vnPsi2_eq`);
* `yyTopMoveY3` (**EVERY ATOM `ψ₂(t) ≤ s < ψ₂(t + Y₃·ω)` ABOVE EVERY TOP ATOM `t = β + W^{Ω_{k+3}+e}` MOVES**;
  supersedes `Yt.ytTopMoveY`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yy

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Ug
  Googology.Trans.PoR.InaccPsi.R2.Uq Googology.Trans.PoR.InaccPsi.R2.Yj

variable {S : InaccSeq.{0}}

theorem yyTwo_lt_L : (1 + 1 : Ordinal.{0}) < Nc.ncL S ω :=
  (show (1 + 1 : Ordinal.{0}) < ω by
    rw [show (1 + 1 : Ordinal.{0}) = ((2 : ℕ) : Ordinal.{0}) by norm_num]; exact natCast_lt_omega0 2).trans
    (Lw.lw_omega_lt_SC (Lw.lw_L_SC S ω))

/-- `B_n` fixes `Y₃ = ψ_{Ω₃}(Ω₃)`. -/
theorem yyY3_D {n : ℕ} : MvD S (ugY S) ∧ Bc.bcB S n (ugY S) = ugY S := by
  have hs : (1 + 1 : Ordinal.{0}) < ω := by
    rw [show (1 + 1 : Ordinal.{0}) = ((2 : ℕ) : Ordinal.{0}) by norm_num]; exact natCast_lt_omega0 2
  obtain ⟨hD3, hB3⟩ := Vs.vsW_D (S := S) hs (n := n)
  have hB2 : Bc.bcB S n (1 + 1) = 1 + 1 :=
    Bc.bcB_fixN n _ ((show (1 + 1 : Ordinal.{0}) < ω by exact hs).trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  obtain ⟨hD, hBe, -⟩ := Ug.ugB_fix (n := n) (s := 1 + 1) (add_pos_of_right zero_lt_one 1).ne'
    (mvD_of_lt yyTwo_lt_L) hB2 hD3 (Ry.ryOm3_mem _ _)
  rw [hB3] at hBe
  exact ⟨hD, hBe⟩

/-- `B_n` fixes `Y₂ = ψ_{Ω₂}(Ω₂)`. -/
theorem yyY2_D {n : ℕ} : MvD S (S.psi (Om (1 + 1)) (Om (1 + 1))) ∧
    Bc.bcB S n (S.psi (Om (1 + 1)) (Om (1 + 1))) = S.psi (Om (1 + 1)) (Om (1 + 1)) := by
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  have h1L : (1 : Ordinal.{0}) < Nc.ncL S ω := one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S ω))
  have hB1 : Bc.bcB S n 1 = 1 := Bc.bcB_fixN n 1 (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  obtain ⟨hD, hBe, -⟩ := Ug.ugB_fix (n := n) (s := 1) one_ne_zero (mvD_of_lt h1L) hB1 hD2 (mxOm2_mem _ _)
  rw [hB2] at hBe
  exact ⟨hD, hBe⟩

/-- `Ω₂ ∣ Y₃`. -/
theorem yyOm2_dvd_Y : Om (1 + 1) ∣ ugY S := by
  have h := Yt.ytWe_dvd_Y (S := S) (x := 1) ((gg_one_lt_of_SC ldOm2_SC).trans uqW_lt_Y)
  rwa [leWe_one] at h

/-- `ψ₂(a + Y₃·ω) = sup_m`, in the form: below it, below some `ψ₂(a + Y₃·m)`. -/
theorem yyBelowFin {a c : Ordinal.{0}} (hc : S.psi c (Om (1 + 1)) < S.psi (a + ugY S * ω) (Om (1 + 1))) :
    ∃ m : ℕ, c ≤ a + ugY S * m := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hca : c < a + ugY S * ω := by
    by_contra h; push Not at h
    exact absurd ((psi_mono hκ2 h).1.trans_lt hc) (lt_irrefl _)
  rcases lt_or_ge c a with h1 | h1
  · exact ⟨0, by rw [Nat.cast_zero, mul_zero, add_zero]; exact h1.le⟩
  have hsub : c - a < ugY S * ω := Ry.rySub_lt h1 hca
  have hY0 : ugY S ≠ 0 := uqY_SC.1.ne'
  have hq : (c - a) / ugY S < ω := (Ordinal.lt_mul_iff_div_lt hY0).1 hsub
  obtain ⟨m, hm⟩ := lt_omega0.1 hq
  refine ⟨m + 1, ?_⟩
  have h2 : c - a < ugY S * ((c - a) / ugY S + 1) := by
    have := Ordinal.lt_mul_succ_div (c - a) hY0
    rwa [Order.succ_eq_add_one] at this
  rw [hm] at h2
  have e1 : c = a + (c - a) := (Ordinal.add_sub_cancel_of_le h1).symm
  rw [e1, Nat.cast_succ]
  exact (add_le_add_iff_left a).2 h2.le

section Win

variable {n : ℕ} {l l' A' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
  (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
  (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1))) (hρ' : S.psi A' (Om 1) = upsilon l')

include hR h1 hr hl' hB hA' hρ'

/-- **`a + Y₃` IS AGAIN A BASE WITH A LAW AT BOTH ENDS** (image `D + Y₂`) for every base `a ≥ Ω₃` with `Y₃ ∣ a`,
`Y₃ ∣ B_n a`. -/
theorem yyY3Step {a D : Ordinal.{0}} (hb : YjBase S n l l' A' a D) (hY : ugY S ∣ a)
    (hY' : ugY S ∣ Bc.bcB S n a) (ha3 : Om (1 + 1 + 1) ≤ a) :
    YjBase S n l l' A' (a + ugY S) (D + S.psi (Om (1 + 1)) (Om (1 + 1))) ∧
      Bc.bcB S n (a + ugY S) = Bc.bcB S n a + ugY S ∧ Om (1 + 1 + 1) ≤ Bc.bcB S n a := by
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hX, hown, hρA, hX', -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  have hl := hR.1
  set A := ConjT.Aη S (cdEta S l) with hAdef
  set Y2 := S.psi (Om (1 + 1)) (Om (1 + 1)) with hY2def
  obtain ⟨hDY, hBY⟩ := yyY3_D (S := S) (n := n)
  obtain ⟨hDY2, hBY2⟩ := yyY2_D (S := S) (n := n)
  obtain ⟨hDa, hBa⟩ := mvB_add (k := n) hb.mv_a hDY
  rw [hBY] at hBa
  obtain ⟨hDD, hBD⟩ := mvB_add (k := n) hb.mv_D hDY2
  rw [hBY2] at hBD
  -- `Ω₃ ≤ B_n a`
  obtain ⟨hD3, hB3⟩ := Vs.vsW_D (S := S) (s := 1 + 1) (by
    rw [show (1 + 1 : Ordinal.{0}) = ((2 : ℕ) : Ordinal.{0}) by norm_num]; exact natCast_lt_omega0 2) (n := n)
  have ha3' : Om (1 + 1 + 1) ≤ Bc.bcB S n a := by
    rcases ha3.lt_or_eq with h | h
    · have := (mvB_lt_iff (k := n) hD3 hb.mv_a).2 h; rw [hB3] at this; exact this.le
    · rw [← h, hB3]
  have hYW : ugY S < Om ω := ugY_lt_Om3.trans Ry.ryOm3_lt
  have han : a ∈ S.CSet a (S.psi a (Om (1 + 1))) := by have h := hb.own 0 zero_le; rwa [add_zero] at h
  have han' : Bc.bcB S n a ∈ S.CSet (Bc.bcB S n a) (S.psi (Bc.bcB S n a) (Om (1 + 1))) := by
    have h := hb.own' 0 zero_le; rwa [add_zero] at h
  -- the base of the shift `Y₃` at `λ` and at `λ'`
  have hbase : ∀ {l0 x : Ordinal.{0}}, VbD S l0 x → ugY S ∣ x → x ∈ S.CSet x (S.psi x (Om (1 + 1))) →
      Ro.RoBaseE S l0 (ugY S) 0 x := by
    intro l0 x hxD hxY hxn
    unfold Ro.RoBaseE
    rw [add_zero, Vq.vqWeY3]
    refine ⟨hxY, hxD.1, (vkOmW.1.isPrincipal hxD.2.2 hYW).trans_le (ConjT.OmW_le_A S _),
      fun d _ => (psi_mono hκ2 le_self_add).2 hxn, fun e' _ he' => ?_⟩
    rw [nonpos_iff_eq_zero.1 he']
    exact (SC_psi hκ2 _).1
  have hAω := Vn.vnA_ge hl hX hown hρA
  have hAω' := Vn.vnA_ge hl' hX' hA' hρ'
  have hlaw0 := Vq.vqTopY3 hl hX hown hρA (le_refl (Om (1 + 1 + 1))) a (A + D) (hbase hb.D_a hY han) ha3 hb.hat
    hb.law
  have hlaw0' := Vq.vqTopY3 hl' hX' hA' hρ' (le_refl (Om (1 + 1 + 1))) (Bc.bcB S n a) (A' + Bc.bcB S n D)
    (hbase hb.D_a' hY' han') ha3' hb.hat' hb.law'
  have hfix : leOe (Y2 + gxTh (upsilon l) (ldAtR S l) 0) = Y2 := by
    rw [gxTh_zero, add_zero]; exact Ua.uaOe_fix (gg_SC_eps Vq.vqY2_SC) (psiS_bounds (S := S) _ 1).1
  have hfix' : leOe (Y2 + gxTh (upsilon l') (ldAtR S l') 0) = Y2 := by
    rw [gxTh_zero, add_zero]; exact Ua.uaOe_fix (gg_SC_eps Vq.vqY2_SC) (psiS_bounds (S := S) _ 1).1
  rw [hfix] at hlaw0
  rw [hfix'] at hlaw0'
  unfold leTe at hlaw0 hlaw0'
  rw [add_zero, Vq.vqWeY3] at hlaw0 hlaw0'
  -- memberships
  have hY3mem : ∀ {x c : Ordinal.{0}}, Om (1 + 1 + 1) < x → ugY S ∈ S.CSet x c := fun h => Vq.vqY3_mem h
  have h3A : Om (1 + 1 + 1) < A := Ry.ryOm3_lt.trans_le hAω
  have h3A' : Om (1 + 1 + 1) < ConjT.Aη S (cdEta S l') := Ry.ryOm3_lt.trans_le (ConjT.OmW_le_A S _)
  have hdvd : Om (1 + 1) ∣ ugY S := yyOm2_dvd_Y
  have h3Y : ∀ {x : Ordinal.{0}}, Om (1 + 1 + 1) ≤ x → ∀ d, Om (1 + 1 + 1) < x + ugY S + d := fun hx d =>
    (hx.trans_lt (lt_add_of_pos_right _ uqY_SC.1)).trans_le le_self_add
  have hownY : ∀ {x : Ordinal.{0}}, Om (1 + 1 + 1) ≤ x → x ∈ S.CSet x (S.psi x (Om (1 + 1))) →
      ∀ d, d ≤ Om (1 + 1) → x + ugY S ∈ S.CSet (x + ugY S + d) (S.psi (x + ugY S + d) (Om (1 + 1))) :=
    fun hx hxn d _ => CSet.add_mem ((psi_mono hκ2 (le_self_add.trans le_self_add)).2 hxn) (hY3mem (h3Y hx d))
  have hhat : ∀ {B0 : Ordinal.{0}}, Om ω ≤ B0 → B0 ∈ S.CSet B0 (S.psi B0 (Om 1)) →
      B0 + Y2 ∈ S.CSet (B0 + Y2) (S.psi (B0 + Y2) (Om 1)) := fun hB0 hB0n =>
    CSet.add_mem ((psi_mono hκ1 le_self_add).2 hB0n)
      (Vq.vqY2_mem ((vkOmW.2.trans_le hB0).trans_le le_self_add))
  refine ⟨⟨⟨CSet.add_mem hb.D_a.1 (hY3mem h3A), CSet.add_mem hb.D_a.2.1 (hY3mem Ry.ryOm3_lt),
      vkOmW.1.isPrincipal hb.D_a.2.2 hYW⟩, dvd_add hb.dvd hdvd, hownY ha3 han, hDa, hDD, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩, hBa, ha3'⟩
  · rw [← add_assoc]; exact hhat (hAω.trans le_self_add) hb.hat
  · rw [← add_assoc]; exact hlaw0
  · rw [hBa]
    exact ⟨CSet.add_mem hb.D_a'.1 (hY3mem h3A'), CSet.add_mem hb.D_a'.2.1 (hY3mem Ry.ryOm3_lt),
      vkOmW.1.isPrincipal hb.D_a'.2.2 hYW⟩
  · rw [hBa]; exact dvd_add hb.dvd' hdvd
  · rw [hBa]; exact hownY ha3' han'
  · rw [hBD, ← add_assoc]; exact hhat (hAω'.trans le_self_add) hb.hat'
  · rw [hBa, hBD, ← add_assoc]; exact hlaw0'

/-- **`a + Y₃·m` is a base with a law at both ends** (image `D + Y₂·m`) for every `m < ω`. -/
theorem yyY3Fin {a D : Ordinal.{0}} (hb : YjBase S n l l' A' a D) (hY : ugY S ∣ a)
    (hY' : ugY S ∣ Bc.bcB S n a) (ha3 : Om (1 + 1 + 1) ≤ a) :
    ∀ m : ℕ, YjBase S n l l' A' (a + ugY S * m) (D + S.psi (Om (1 + 1)) (Om (1 + 1)) * m) ∧
      Bc.bcB S n (a + ugY S * m) = Bc.bcB S n a + ugY S * m := by
  intro m
  induction m with
  | zero =>
    simp only [Nat.cast_zero, mul_zero, add_zero]
    exact ⟨hb, trivial⟩
  | succ m ih =>
    obtain ⟨hbm, hBm⟩ := ih
    have hYm : ugY S ∣ a + ugY S * m := dvd_add hY (dvd_mul_right _ _)
    have hYm' : ugY S ∣ Bc.bcB S n (a + ugY S * m) := by rw [hBm]; exact dvd_add hY' (dvd_mul_right _ _)
    obtain ⟨hb1, hB1, -⟩ := yyY3Step hR h1 hr hl' hB hA' hρ' hbm hYm hYm' (ha3.trans le_self_add)
    have e1 : a + ugY S * ((m + 1 : ℕ) : Ordinal.{0}) = a + ugY S * m + ugY S := by
      rw [Nat.cast_succ, mul_add_one, add_assoc]
    have e2 : D + S.psi (Om (1 + 1)) (Om (1 + 1)) * ((m + 1 : ℕ) : Ordinal.{0}) =
        D + S.psi (Om (1 + 1)) (Om (1 + 1)) * m + S.psi (Om (1 + 1)) (Om (1 + 1)) := by
      rw [Nat.cast_succ, mul_add_one, add_assoc]
    rw [e1, e2]
    refine ⟨hb1, ?_⟩
    rw [hB1, hBm, add_assoc, Nat.cast_succ, mul_add_one]

/-- **EVERY ATOM `ψ₂(a) ≤ s < ψ₂(a + Y₃·ω)` MOVES** above a base `a ≥ Ω₃` with a law at both ends, `Y₃ ∣ a`,
`Y₃ ∣ B_n a`, under IH(s). -/
theorem yyY3Move {a D : Ordinal.{0}} (hb : YjBase S n l l' A' a D) (hY : ugY S ∣ a)
    (hY' : ugY S ∣ Bc.bcB S n a) (ha3 : Om (1 + 1 + 1) ≤ a) {s : Ordinal.{0}} (hs : s ∈ ldAtR S l)
    (hsa : S.psi a (Om (1 + 1)) ≤ s) (hsω : s < S.psi (a + ugY S * ω) (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hfin := yyY3Fin hR h1 hr hl' hB hA' hρ' hb hY hY' ha3
  -- strict increase of the block tops
  have hinc : ∀ m : ℕ, S.psi (a + ugY S * m) (Om (1 + 1)) < S.psi (a + ugY S * ((m + 1 : ℕ) : Ordinal.{0}))
      (Om (1 + 1)) := by
    intro m
    have e1 : a + ugY S * ((m + 1 : ℕ) : Ordinal.{0}) = a + ugY S * m + ugY S := by
      rw [Nat.cast_succ, mul_add_one, add_assoc]
    rw [e1]
    have hown := (hfin m).1.own 0 zero_le
    rw [add_zero] at hown
    exact psi_lt_psi_of_mem hκ2 (lt_add_of_pos_right _ uqY_SC.1)
      ((psi_mono hκ2 le_self_add).2 hown)
  -- some block contains `s`
  obtain ⟨c, hcH, hcA, rfl⟩ := hs
  obtain ⟨m0, hm0⟩ := yyBelowFin hsω
  have hex : ∃ m : ℕ, S.psi c (Om (1 + 1)) < S.psi (a + ugY S * m) (Om (1 + 1)) :=
    ⟨m0 + 1, ((psi_mono hκ2 hm0).1).trans_lt (hinc m0)⟩
  classical
  set m := Nat.find hex with hmdef
  have hm : S.psi c (Om (1 + 1)) < S.psi (a + ugY S * m) (Om (1 + 1)) := Nat.find_spec hex
  have hm0' : m ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero, mul_zero, add_zero] at hm
    exact absurd hsa (not_le.2 hm)
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hm0'
  have hjle : S.psi (a + ugY S * j) (Om (1 + 1)) ≤ S.psi c (Om (1 + 1)) := by
    have := Nat.find_min hex (show j < m by omega)
    exact not_lt.1 this
  obtain ⟨hbj, hBj⟩ := hfin j
  have hYj : ugY S ∣ a + ugY S * j := dvd_add hY (dvd_mul_right _ _)
  have hYj' : ugY S ∣ Bc.bcB S n (a + ugY S * j) := by rw [hBj]; exact dvd_add hY' (dvd_mul_right _ _)
  have hsY : S.psi c (Om (1 + 1)) < S.psi (a + ugY S * j + ugY S) (Om (1 + 1)) := by
    have e1 : a + ugY S * j + ugY S = a + ugY S * ((j + 1 : ℕ) : Ordinal.{0}) := by
      rw [Nat.cast_succ, mul_add_one, add_assoc]
    rw [e1, show (j + 1 : ℕ) = m from hj.symm]; exact hm
  exact Yt.ytUxMove hR h1 hr hl' hB hA' hρ' hbj hYj hYj' ⟨c, hcH, hcA, rfl⟩ hjle hsY IH

/-- **EVERY ATOM `ψ₂(t) ≤ s < ψ₂(t + Y₃·ω)` ABOVE EVERY TOP ATOM `t = β + W^{Ω_{k+3}+e}` MOVES** under the premise of
WallBelow at `s` (supersedes `Yt.ytTopMoveY`). -/
theorem yyTopMoveY3 (k : ℕ) {e β : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (hβD : VbD S l β)
    (hbe : Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e β) {s : Ordinal.{0}} (hs : s ∈ ldAtR S l)
    (hst : S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)) ≤ s)
    (hsω : s < S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) + ugY S * ω) (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  have IHt := fun x hx (hxs : x < S.psi (β + leWe (X + e)) (Om (1 + 1))) => IH x hx (hxs.trans_le hst)
  obtain ⟨hbt, hBt⟩ := yjTopBase hR h1 hr hl' hB hA' hρ' k hec hβD hbe IHt
  obtain ⟨hdv', -⟩ := yjBaseFacts hR h1 hr hl' hB k hec hβD hbe IHt
  have hd : ugY S ∣ β + leWe (X + e) := dvd_add ((Yt.ytY_dvd_We k e).trans hbe.1) (Yt.ytY_dvd_We k e)
  have hd' : ugY S ∣ Bc.bcB S n (β + leWe (X + e)) := by
    rw [hBt]
    exact dvd_add ((Yt.ytY_dvd_We k _).trans hdv') (Yt.ytY_dvd_We k _)
  have h3 : Om (1 + 1 + 1) ≤ β + leWe (X + e) := by
    have hXle : X ≤ leWe (X + e) := by
      calc X = leWe X := (Vn.vnWe_OmK k).symm
        _ ≤ leWe (X + e) := leWe_mono le_self_add
    exact (Yt.ytOm3_le_X k).trans (hXle.trans le_add_self)
  exact yyY3Move hR h1 hr hl' hB hA' hρ' hbt hd hd' h3 hs hst hsω IH

end Win

/-- **A base `a < Ω₃` with `Y₃ ∣ a` (normal at `Ω₂`) is `0`** (`Vn.vnNoSelf`: no `X ∈ [Y₃, Ω₃)` is in `Cl(X, ψ₂ X)`). -/
theorem yyBaseSmall {a : Ordinal.{0}} (ha : a ∈ S.CSet a (S.psi a (Om (1 + 1)))) (hY : ugY S ∣ a)
    (ha3 : a < Om (1 + 1 + 1)) : a = 0 := by
  by_contra h0
  have hYa : ugY S ≤ a := Ordinal.le_of_dvd h0 hY
  have hle : S.psi a (Om (1 + 1)) ≤ S.psi a (Om (1 + 1 + 1)) :=
    ((psi_lt (InR_Om_succ 1) a).trans (ugOm2_lt_psi3 a)).le
  have h1 : ugY S = S.psi (Om ((1 + 1 : Ordinal.{0}) + 1)) (Om ((1 + 1 : Ordinal.{0}) + 1)) := rfl
  exact Vn.vnNoSelf (s := 1 + 1) (by rw [← h1]; exact hYa) ha3 hle ha

/-- **`skPsi3Off` for every base `a < Ω₃`**: such a base is `0` and the region `[ψ₂(Y₃), ψ₂(Ω₃))` is empty. -/
theorem yyPsi3OffLow {a s : Ordinal.{0}} (ha : a ∈ S.CSet a (S.psi a (Om (1 + 1)))) (hY : ugY S ∣ a)
    (ha3 : a < Om (1 + 1 + 1)) (hs1 : S.psi (a + ugY S) (Om (1 + 1)) ≤ s)
    (hs2 : s < S.psi (a + Om (1 + 1 + 1)) (Om (1 + 1))) : False := by
  obtain rfl := yyBaseSmall ha hY ha3
  rw [zero_add] at hs1 hs2
  have h2 : Om (1 + 1 : Ordinal.{0}) < ugY S := uqW_lt_Y
  have e : S.psi (Om (1 + 1 + 1)) (Om (1 + 1)) = S.psi (ugY S) (Om (1 + 1)) :=
    Vn.vnPsi2_eq (s := 1 + 1) h2 ugY_lt_Om3.le le_rfl
  rw [e] at hs2
  exact absurd (hs1.trans_lt hs2) (lt_irrefl _)

end Googology.Trans.PoR.InaccPsi.R2.Yy

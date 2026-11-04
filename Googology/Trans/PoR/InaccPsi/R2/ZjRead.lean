import Googology.Trans.PoR.InaccPsi.R2.XsMv
import Googology.Trans.PoR.InaccPsi.R2.RnSup
import Googology.Trans.PoR.InaccPsi.R2.LeEMove

/-!
# The readings at the base `Ω_ω`: the plateau `K_ω` and every atom below `T* = ψ_{Ω₂}(Ω_ω + Ω₂^{Ω₂})`

`Θ = gxTh ρ_λ (ldAtR λ)` (`= Θ_λ` below `Ω₂`), `A = A_{η_λ}`, `θ = ψ_{Ω₂}(Ω_ω)`, `W^e = Ω₂^e` (`Le.leWe`),
`Ω^x = Ω₁^x` (`Le.leOe`), `T_e(β) = ψ_{Ω₂}(β + W^e)` (`Le.leTe`), `T* = T_W(Ω_ω) = ψ_{Ω₂}(Ω_ω + W^W)`
(`Rn.rnTW S Ω_ω`), `K_0 = 1`, `K_{j+1} = ψ_{Ω₂}(Ω_ω + Ω₂·K_j)` (`Xs.xsK`).

* `zjW_dvd`, `zjWW_lt` (`W^W ∣ Ω_ω`, `Ω_ω + W^W < Ω_ω + Ω_ω`);
* `zjBase` (**`Ω_ω` is a base** (`Rn.RnBase`) at every restart with `Ω_ω + Ω_ω ≤ A`), `zjBaseE` (**`Ω_ω` is a base of
  exponent `e` (`Le.LeBaseE`) for every `e < T*`**), `zjHat` (`A + θ` is own), `zjBase0` (`Θ(ψ_{Ω₂}(Ω_ω)) =
  ψ_{Ω₁}(A + θ)`, `Wl.wlThVal`);
* `zjKw_sup` (**THE PLATEAU: `ψ_{Ω₂}(Ω_ω + Ω₂·Ω₂) = sup_j K_j`**, i.e. `x < ψ_{Ω₂}(Ω_ω + Ω₂²) ⇔ ∃ j, x < K_j`, no
  hypothesis), `zjKw_read` (**`Θ(K_ω) = ψ_{Ω₁}(A + θ + Ω₁²)`**, `Ω₁² = Ω^2`), `zjTop_read` (**`Θ(T_e(Ω_ω)) =
  ψ_{Ω₁}(A + θ + Ω^{Θ e})`** for every code `1 ≤ e < T*`: the bases `Ω_ω + W^e·δ`, `Le.leTopE` at the base `Ω_ω`),
  `zjOwn_read` (the block law over `Ω_ω`);
* `zjTh` (**every atom `θ < t < T*` is `ψ_{Ω₂}(Ω_ω + c)` with `(e, c, v)` own over `Ω_ω` (`Le.LeOwnH`), `e < T*`,
  and `Θ(t) = ψ_{Ω₁}(A + θ + v)`**);
* `zjKw_wit` (**REFUTE-FIRST record: the expected plateau value holds at the restart of `m* = L(0)`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn

variable {S : InaccSeq.{0}}

/-! ## The base `Ω_ω` -/

theorem zjOmW_eq : ω ^ (Om ω : Ordinal.{0}) = Om ω :=
  gg_SC_eps (SC_Om (omega0_ne_zero : (ω : Ordinal.{0}) ≠ 0))

/-- `W^W ∣ Ω_ω`. -/
theorem zjW_dvd : leWe (Om (1 + 1 : Ordinal.{0})) ∣ Om ω := by
  conv_rhs => rw [← zjOmW_eq]
  exact opow_dvd_opow ω ldOm2sq_lt_OmW.le

/-- `W^e ∣ Ω_ω` for every `e ≤ Ω₂`. -/
theorem zjWe_dvd {e : Ordinal.{0}} (he : e ≤ Om (1 + 1)) : leWe e ∣ Om ω :=
  (leWe_dvd he).trans zjW_dvd

theorem zjWW_lt : Om ω + leWe (Om (1 + 1 : Ordinal.{0})) < Om ω + Om ω :=
  (add_lt_add_iff_left _).2 leWW_lt_OmW

theorem zjOmW_own (d : Ordinal.{0}) : Om ω ∈ S.CSet (Om ω + d) (S.psi (Om ω + d) (Om (1 + 1))) :=
  ConjT.OmW_mem (S := S) _ _

/-- `θ = ψ_{Ω₂}(Ω_ω) < T* = ψ_{Ω₂}(Ω_ω + W^W)`. -/
theorem zjTh_lt_T : ConjT.th S < rnTW S (Om ω) :=
  psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right _ (leWe_pos _)) (zjOmW_own _)

theorem zjT_lt_Om2 : rnTW S (Om ω) < Om (1 + 1) := rnTW_lt_Om2 _

/-- `θ⁺ ≤ T*`. -/
theorem zjThP_le_T : Lj.ljThP S ≤ rnTW S (Om ω) := by
  refine rnThP_le_MW.trans ?_
  show S.psi (Om ω + Om (1 + 1)) (Om (1 + 1)) ≤ S.psi (Om ω + leWe (Om (1 + 1))) (Om (1 + 1))
  refine (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left _).2 ?_)).1
  calc Om (1 + 1 : Ordinal.{0}) = leWe 1 := leWe_one.symm
    _ ≤ leWe (Om (1 + 1)) := leWe_mono (gg_one_lt_of_SC ldOm2_SC).le

/-! ## The plateau `K_ω = ψ_{Ω₂}(Ω_ω + Ω₂²)` (no hypothesis) -/

theorem zjW2_eq : leWe (1 + 1 : Ordinal.{0}) = Om (1 + 1) * Om (1 + 1) := by
  rw [leWe_succ, leWe_one]

theorem zjKe_ge : ∀ j, Xs.xsK S j ≤ leKe S 1 (Om ω) j
  | 0 => (one_lt_omega0.trans (Lw.lw_omega_lt_SC Ph.ph_SC_Om1)).le
  | j + 1 => by
    show S.psi (Om ω + Om (1 + 1) * Xs.xsK S j) (Om (1 + 1)) ≤
      S.psi (Om ω + leWe 1 * leKe S 1 (Om ω) j) (Om (1 + 1))
    rw [leWe_one]
    exact (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left _).2 (mul_le_mul_right (zjKe_ge j) _))).1

theorem zjKe_le : ∀ j, leKe S 1 (Om ω) j ≤ Xs.xsK S (j + 1)
  | 0 => (psiS_bounds (S := S) _ 1).1.le
  | j + 1 => by
    show S.psi (Om ω + leWe 1 * leKe S 1 (Om ω) j) (Om (1 + 1)) ≤
      S.psi (Om ω + Om (1 + 1) * Xs.xsK S (j + 1)) (Om (1 + 1))
    rw [leWe_one]
    exact (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left _).2 (mul_le_mul_right (zjKe_le j) _))).1

theorem zjOne_exp : (1 : Ordinal.{0}) < S.psi (Om ω + leWe 1) (Om (1 + 1)) :=
  (one_lt_omega0.trans (Lw.lw_omega_lt_SC Ph.ph_SC_Om1)).trans (psiS_bounds (S := S) _ 1).1

/-- **THE PLATEAU**: `x < ψ_{Ω₂}(Ω_ω + Ω₂·Ω₂) ⇔ ∃ j, x < K_j` (so `K_ω = sup_j K_j = ψ_{Ω₂}(Ω_ω + Ω₂²)`). -/
theorem zjKw_sup (x : Ordinal.{0}) :
    x < S.psi (Om ω + Om (1 + 1) * Om (1 + 1)) (Om (1 + 1)) ↔ ∃ j, x < Xs.xsK S j := by
  have h2 : (1 + 1 : Ordinal.{0}) ≤ Om (1 + 1) := by
    have h := (natCast_lt_omega0 2).trans (Lw.lw_omega_lt_SC ldOm2_SC)
    rw [one_add_one_eq_two]; exact_mod_cast h.le
  have hβd : leWe (1 + 1 : Ordinal.{0}) ∣ Om ω := zjWe_dvd h2
  constructor
  · intro hx
    have hx' : x < leTe S (1 + 1) (Om ω) := by unfold leTe; rw [zjW2_eq]; exact hx
    obtain ⟨j, hj⟩ := leKe_sup (S := S) (e := 1) (β := Om ω) (fun d _ => zjOmW_own d) zjOne_exp hβd hx'
    exact ⟨j + 1, hj.trans_le (zjKe_le j)⟩
  · rintro ⟨j, hj⟩
    have h := leKe_le_top (S := S) 1 (Om ω) j
    unfold leTe at h; rw [zjW2_eq] at h
    exact (hj.trans_le (zjKe_ge j)).trans_le h

/-- `K_j < K_ω` for every `j`. -/
theorem zjK_lt_Kw (j : ℕ) : Xs.xsK S j < S.psi (Om ω + Om (1 + 1) * Om (1 + 1)) (Om (1 + 1)) :=
  (zjKw_sup _).2 ⟨j + 1, Xs.xsK_lt_succ j⟩

/-- `K_ω ≤ m ⇔ ∀ j, K_j ≤ m`. -/
theorem zjKw_le_iff (m : Ordinal.{0}) :
    S.psi (Om ω + Om (1 + 1) * Om (1 + 1)) (Om (1 + 1)) ≤ m ↔ ∀ j, Xs.xsK S j ≤ m := by
  constructor
  · intro h j; exact (zjK_lt_Kw j).le.trans h
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨j, hj⟩ := (zjKw_sup m).1 hc
    exact absurd (h j) (not_le.2 hj)

theorem zjKw_lt_T : S.psi (Om ω + Om (1 + 1) * Om (1 + 1)) (Om (1 + 1)) < rnTW S (Om ω) := by
  have h2W : Om (1 + 1 : Ordinal.{0}) * Om (1 + 1) < leWe (Om (1 + 1)) := by
    have h := (natCast_lt_omega0 2).trans (Lw.lw_omega_lt_SC ldOm2_SC)
    have h2 : (1 + 1 : Ordinal.{0}) < Om (1 + 1) := by rw [one_add_one_eq_two]; exact_mod_cast h
    rw [← zjW2_eq]; exact leWe_lt h2
  exact psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left _).2 h2W)
    (CSet.add_mem (zjOmW_own _) (ldMulK_mem ldOm2_SC (mxOm2_mem _ _) (mxOm2_mem _ _)))

theorem zjOe2_eq : leOe (1 + 1 : Ordinal.{0}) = Om 1 * Om 1 := by rw [leOe_succ, leOe_one]

/-! ## The readings over the base `Ω_ω` -/

section Read

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hown : ConjT.Aη S (cdEta S l) ∈
    S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)))
  (hAW : Om ω + Om ω ≤ ConjT.Aη S (cdEta S l))

include hl hX hown hAW

/-- **`Ω_ω` is a base** (`Rn.RnBase`). -/
theorem zjBase : RnBase S l (Om ω) :=
  ⟨zjW_dvd, ConjT.OmW_mem (S := S) _ _, zjWW_lt.trans_le hAW, fun d _ => zjOmW_own d⟩

/-- **`Ω_ω` is a base of exponent `e` for every `e < T*`.** -/
theorem zjBaseE {e : Ordinal.{0}} (he : e < rnTW S (Om ω)) : LeBaseE S l e (Om ω) :=
  rnBaseE (zjBase hl hX hown hAW) he

/-- `A + θ` is own. -/
theorem zjHat : ConjT.Aη S (cdEta S l) + ConjT.th S ∈
    S.CSet (ConjT.Aη S (cdEta S l) + ConjT.th S) (S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S) (Om 1)) := by
  have h := Xs.xsAθ_mem hl hX hown (Xs.xsAb_of hAW) 0
  rwa [add_zero] at h

/-- `Θ(ψ_{Ω₂}(Ω_ω)) = ψ_{Ω₁}(A + θ)`. -/
theorem zjBase0 : gxTh (upsilon l) (ldAtR S l) (S.psi (Om ω) (Om (1 + 1))) =
    S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S) (Om 1) :=
  Wl.wlThVal hl hX hown (cdEta_pv (S := S) hl.1 hX)

/-- **The tops over `Ω_ω`**: `Θ(ψ_{Ω₂}(Ω_ω + W^e)) = ψ_{Ω₁}(A + θ + Ω^{Θ e})` for every code `1 ≤ e < T*`. -/
theorem zjTop_read {e : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (he1 : 1 ≤ e)
    (he : e < rnTW S (Om ω)) :
    gxTh (upsilon l) (ldAtR S l) (leTe S e (Om ω)) =
      S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + leOe (gxTh (upsilon l) (ldAtR S l) e)) (Om 1) :=
  leTopE hl hX e hec he1 (Om ω) _ (zjBaseE hl hX hown hAW he) (zjHat hl hX hown hAW)
    (zjBase0 hl hX hown hAW)

/-- **THE PLATEAU READING**: `Θ(K_ω) = Θ(ψ_{Ω₂}(Ω_ω + Ω₂²)) = ψ_{Ω₁}(A + θ + Ω^2)`, `Ω^2 = Ω₁·Ω₁`. -/
theorem zjKw_read : gxTh (upsilon l) (ldAtR S l) (S.psi (Om ω + Om (1 + 1) * Om (1 + 1)) (Om (1 + 1))) =
    S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + leOe (1 + 1)) (Om 1) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have h2ρ : (1 + 1 : Ordinal.{0}) < upsilon l := by
    rw [one_add_one_eq_two]; exact (natCast_lt_omega0 2).trans (Lw.lw_omega_lt_SC hρSC)
  have h2c : GxCl (upsilon l) (ldAtR S l) (1 + 1) := GxCl.small h2ρ
  have h2T : (1 + 1 : Ordinal.{0}) < rnTW S (Om ω) := by
    rw [one_add_one_eq_two]; exact (natCast_lt_omega0 2).trans
      ((Lw.lw_omega_lt_SC Ph.ph_SC_Om1).trans (rnOm1_lt_TW _))
  have h := zjTop_read hl hX hown hAW h2c le_add_self h2T
  rw [gxTh_small h2ρ.le] at h
  unfold leTe at h; rw [zjW2_eq] at h
  exact h

/-- **The block law over `Ω_ω`**: `Θ(ψ_{Ω₂}(Ω_ω + c)) = ψ_{Ω₁}(A + θ + v)` for every own `(e, c, v)`, `e < T*`. -/
theorem zjOwn_read {e c v : Ordinal.{0}} (h : LeOwnH S l e (Om ω) c v) (he : e < rnTW S (Om ω)) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (Om ω + c) (Om (1 + 1))) =
      S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + v) (Om 1) ∧
    ConjT.Aη S (cdEta S l) + ConjT.th S + v ∈ S.CSet (ConjT.Aη S (cdEta S l) + ConjT.th S + v)
      (S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + v) (Om 1)) ∧
    v < leOe (gxTh (upsilon l) (ldAtR S l) e) ∧ c < leWe e :=
  leOwnRead hl hX h _ (zjBaseE hl hX hown hAW he) (zjHat hl hX hown hAW) (zjBase0 hl hX hown hAW)

/-- **Every atom `θ < t < T*` is `ψ_{Ω₂}(Ω_ω + c)` with `(e, c, v)` own over `Ω_ω`, `e < T*`, and
`Θ(t) = ψ_{Ω₁}(A + θ + v)`.** -/
theorem zjTh : ∀ t ∈ ldAtR S l, ConjT.th S < t → t < rnTW S (Om ω) →
    ∃ e c v, e < rnTW S (Om ω) ∧ LeOwnH S l e (Om ω) c v ∧ t = S.psi (Om ω + c) (Om (1 + 1)) ∧
      gxTh (upsilon l) (ldAtR S l) t = S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + v) (Om 1) ∧
      ConjT.Aη S (cdEta S l) + ConjT.th S + v ∈ S.CSet (ConjT.Aη S (cdEta S l) + ConjT.th S + v)
        (S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + v) (Om 1)) ∧
      v < leOe (gxTh (upsilon l) (ldAtR S l) e) ∧ c < leWe e := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hTSC : SC (rnTW S (Om ω)) := rnTW_SC _
  intro t ht hθt htT
  have hrep : ∃ e c v, e < rnTW S (Om ω) ∧ LeOwnH S l e (Om ω) c v ∧
      t = S.psi (Om ω + c) (Om (1 + 1)) := by
    obtain ⟨a, haH, haA, rfl⟩ := ht
    rcases lt_or_ge a (Om ω) with haW | haW
    · exact absurd hθt (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) haW.le).1)
    obtain ⟨d, rfl⟩ := exists_add_of_le haW
    have hdW : d < leWe (Om (1 + 1)) := by
      by_contra h
      push Not at h
      exact absurd htT (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left _).2 h)).1)
    rcases eq_or_ne d 0 with rfl | hd0
    · rw [add_zero] at hθt; exact absurd hθt (lt_irrefl _)
    have hdH : d ∈ cdHull S l := by
      have h1 := leModP_mem (S := S) (Om (1 + 1) * Om (1 + 1)) haH
      have hm : (Om ω + d) % ω ^ (Om (1 + 1) * Om (1 + 1)) = d := by
        obtain ⟨q, hq⟩ := zjW_dvd
        change (Om ω + d) % leWe (Om (1 + 1)) = d
        rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hdW]
      rwa [hm] at h1
    have hlogd : log ω d < Om (1 + 1) * Om (1 + 1) :=
      (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hd0).trans_lt hdW)
    have hgW : log ω d / Om (1 + 1) < Om (1 + 1) := (Ordinal.lt_mul_iff_div_lt hW0).1 hlogd
    have hgH : log ω d / Om (1 + 1) ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hdH)
    have hgT : log ω d / Om (1 + 1) < rnTW S (Om ω) := by
      by_contra h
      push Not at h
      have h1 := rnTW_ge (fun d' _ => zjOmW_own (S := S) d') zjW_dvd h
      have h2 : leWe (log ω d / Om (1 + 1)) ≤ d := by
        unfold leWe
        exact (opow_le_opow_right omega0_pos (Ordinal.mul_div_le _ _)).trans (opow_log_le_self ω hd0)
      exact absurd (h1.trans (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left _).2 h2)).1)
        (not_le.2 htT)
    set E := log ω d / Om (1 + 1) + 1 with hE_def
    have hET : E < rnTW S (Om ω) := hTSC.isSuccLimit.succ_lt hgT
    have hEW : E < Om (1 + 1) := hET.trans zjT_lt_Om2
    have hEc : GxCl (upsilon l) (ldAtR S l) E := (ldHull_iff hl hX hEW).1 (CSet.succ_mem hgH)
    have hdE : d < leWe E := by
      unfold leWe
      calc d < ω ^ (log ω d + 1) := by
            rw [← Order.succ_eq_add_one]; exact lt_opow_succ_log_self one_lt_omega0 d
        _ ≤ ω ^ (Om (1 + 1) * E) := by
            refine opow_le_opow_right omega0_pos (Order.add_one_le_of_lt ?_)
            rw [hE_def, mul_add_one]; exact Ordinal.lt_mul_div_add _ hW0
    have hle : S.psi (Om ω + d) (Om (1 + 1)) ≤ leTe S E (Om ω) := by
      unfold leTe; exact (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left _).2 hdE.le)).1
    rcases hle.lt_or_eq with hlt | heq
    · rcases leClsE hl hX E hEc le_add_self (Om ω) (zjBaseE hl hX hown hAW hET) _ ⟨Om ω + d, haH, haA, rfl⟩
        hlt with h0 | ⟨e', c, v, he', hownc, e⟩
      · exact absurd hθt (not_lt.2 h0)
      · exact ⟨e', c, v, he'.trans_lt hET, hownc, e⟩
    · have hc1 : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small (gg_one_lt_of_SC hρSC)
      have h1T : (1 : Ordinal.{0}) < leTe S (E + 1) (Om ω) :=
        (one_lt_omega0.trans (Lw.lw_omega_lt_SC Ph.ph_SC_Om1)).trans (leOm1_lt_Te _ _)
      refine ⟨E + 1, leWe E * 1 + 0, _, hTSC.isSuccLimit.succ_lt hET,
        LeOwnH.succ hEc le_add_self hc1 one_ne_zero h1T zero_le LeOwnH.zero, ?_⟩
      rw [heq, mul_one, add_zero]; rfl
  obtain ⟨e, c, v, heT, hownc, he⟩ := hrep
  obtain ⟨e1, own, hv, hc⟩ := zjOwn_read hl hX hown hAW hownc heT
  exact ⟨e, c, v, heT, hownc, he, by rw [he]; exact e1, own, hv, hc⟩

end Read

/-- **REFUTE-FIRST record (the plateau)**: at the restart of `m* = L(0)` (no hypothesis) the expected plateau value
holds: `Θ(K_ω) = ψ_{Ω₁}(A + θ + Ω₁·Ω₁)`, `K_ω = ψ_{Ω₂}(Ω_ω + Ω₂·Ω₂) = sup_j K_j`. -/
theorem zjKw_wit (S : InaccSeq.{0}) :
    ∃ l : Ordinal.{0}, IsRestartIdx l ∧ upsilon l = Nc.ncL S 0 ∧
      gxTh (upsilon l) (ldAtR S l) (S.psi (Om ω + Om (1 + 1) * Om (1 + 1)) (Om (1 + 1))) =
        S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + Om 1 * Om 1) (Om 1) := by
  obtain ⟨l, hl, e⟩ := Cv.cvM_restart (S := S)
  have hX : upsilon l < Pv S (Om ω + Nc.ncPp S * 1) := by
    rw [← e, ← Lw.lw_L_eq]; exact Rl.rlM_lt_L1
  have hL1 : Nc.ncL S 1 = Bc.bcC S 0 := by simp [Bc.bcC]
  have hn : upsilon l < Bc.bcC S (0 + 1) := by
    rw [← e]
    exact (Rl.rlM_lt_L1 (S := S)).trans_le (hL1 ▸ Bc.bcC_mono (S := S) (Nat.zero_le _))
  obtain ⟨hA, -⟩ := Vq.vqA_spec hl hX (n := 0) hn
  have h0 : Pv S (Om ω) ≤ upsilon l := by
    rw [← e, Lw.lw_L_eq, mul_zero, add_zero]
  have hAW := Xs.xsA_ge hl hX hA h0
  refine ⟨l, hl, e.symm, ?_⟩
  rw [zjKw_read hl hX hA hAW, zjOe2_eq]

end Googology.Trans.PoR.InaccPsi.R2.Zj

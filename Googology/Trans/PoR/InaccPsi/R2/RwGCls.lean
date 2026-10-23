import Googology.Trans.PoR.InaccPsi.R2.RwG

/-!
# The own atoms for the code-level family `RwG`: every atom below `ψ_{Ω₂}(Ω₂^{Ω₂^{Ω₂}})` is own

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `T_E(β) = ψ_{Ω₂}(β + W^E)`, `EE_j(X₀, β, E) = Rv.rvEE S X₀ β E j`,
`EX_j(X₀, β) = Rw.rwEX S X₀ β j`, `Sh = Rw.rwShG S λ`, closures at the bases with a reading (`Rw.RwRd`).

`RwClsOffG S λ b X₀ X̂₀ E`: `X₀ = X̂₀ = 0`, or `RwG b X₀ X̂₀ E₀` with `E ≤ E₀` and the atoms below `T_{X₀}(β)` own
at every base `β ≥ b`.  `RwClsLevG S λ E`: for every such offset over which `E` is own (`E < EX_j(X₀, b)`), the
atoms below `T_{X₀ + W^E}(β)` are own at every base `β ≥ b`.  `RwFamClsG S λ E`: the same at `X₀ + W^E·ζ`,
`1 ≤ ζ < EE_j(X₀, b, E)` a code with `Θ ζ < Ω₁`.

* `rwG_ext`, `rwOffG_data`, `rwOffG_bounds`;
* `rwFamClsG_of` (**`RwClsLevG E ⇒ RwFamClsG E`**), `rwClsLevG_one`, `rwClsLevG_succ` (**`RwFamClsG E₀ ⇒
  RwClsLevG (E₀+1)`**, by `Rw.rwEEc_sup`, `Rw.rwEEc_code`), `rwClsLevG_lim` (**limit codes**), `rwClsLevG_all`
  (**every code `1 ≤ E < Ω₂` with `Θ E < Ω₁`**);
* `rwEX_code0` (**`EX_j(0, 0)` is a code with `Θ(EX_j) < Ω₁`**, by `Rw.rwLevC_all`);
* `rwClsG_top` (**the atoms below `T_{W^{Ω₂}}(0) = ψ_{Ω₂}(Ω₂^{Ω₂^{Ω₂}})` are own over `0`**, by `Rw.rwEX_sup`).

No new axiom.  New definitions: the hypothesis names `RwClsOffG`, `RwClsLevG`, `RwFamClsG`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv

variable {S : InaccSeq.{0}}

/-- **An offset with its own atoms** at level `≥ E`. -/
def RwClsOffG (S : InaccSeq.{0}) (l b X0 Xh0 E : Ordinal.{0}) : Prop :=
  (X0 = 0 ∧ Xh0 = 0) ∨ ∃ E0, RwG S l b X0 Xh0 E0 ∧ E ≤ E0 ∧
    ∀ β, b ≤ β → RoBaseE S l X0 0 β → RwRd S l β → RwClsAt S l (rwShG S l) X0 0 β

/-- **The code-level closure statement.** -/
def RwClsLevG (S : InaccSeq.{0}) (l E : Ordinal.{0}) : Prop :=
  ∀ b X0 Xh0, RwClsOffG S l b X0 Xh0 E → (∃ j, E < rwEX S X0 b j) →
    ∀ β, b ≤ β → RoBaseE S l (X0 + leWe E) 0 β → RwRd S l β → RwClsAt S l (rwShG S l) (X0 + leWe E) 0 β

/-- **The code-level family closure statement.** -/
def RwFamClsG (S : InaccSeq.{0}) (l E : Ordinal.{0}) : Prop :=
  ∀ b X0 Xh0, RwClsOffG S l b X0 Xh0 (E + 1) → (∃ j, E < rwEX S X0 b j) →
    ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → 1 ≤ ζ →
    gxTh (upsilon l) (ldAtR S l) ζ < Om 1 → (∃ j, ζ < rvEE S X0 b E j) →
    ∀ β, b ≤ β → RoBaseE S l (X0 + leWe E * ζ) 0 β → RwRd S l β →
      RwClsAt S l (rwShG S l) (X0 + leWe E * ζ) 0 β

/-- **Extending an offset by one term.** -/
theorem rwG_ext {l b X0 Xh0 E E' ζ : Ordinal.{0}}
    (hoff : (X0 = 0 ∧ Xh0 = 0) ∨ ∃ E0, RwG S l b X0 Xh0 E0 ∧ E ≤ E0) (he' : 1 ≤ E') (he'e : E' < E)
    (hE' : GxCl (upsilon l) (ldAtR S l) E') (hΘE' : gxTh (upsilon l) (ldAtR S l) E' < Om 1)
    (hEX : ∃ j, E' < rwEX S X0 b j) (hζ : GxCl (upsilon l) (ldAtR S l) ζ) (hζ0 : ζ ≠ 0)
    (hΘ : gxTh (upsilon l) (ldAtR S l) ζ < Om 1) (hj : ∃ j, ζ < rvEE S X0 b E' j) :
    RwG S l b (X0 + leWe E' * ζ)
      (Xh0 + leOe (gxTh (upsilon l) (ldAtR S l) E') * gxTh (upsilon l) (ldAtR S l) ζ) E' := by
  rcases hoff with ⟨rfl, rfl⟩ | ⟨E0, hE0, hEE⟩
  · rw [zero_add, zero_add]; exact RwG.one he' hE' hΘE' hEX hζ hζ0 hΘ hj
  · exact RwG.add hE0 he' (he'e.trans_le hEE) hE' hΘE' hEX hζ hζ0 hΘ hj

theorem rwClsOffG_mono {l b β X0 Xh0 E : Ordinal.{0}} (hbβ : b ≤ β) (h : RwClsOffG S l b X0 Xh0 E) :
    RwClsOffG S l β X0 Xh0 E := by
  rcases h with h0 | ⟨E0, hE0, hEE, hcl⟩
  · exact Or.inl h0
  · exact Or.inr ⟨E0, rwG_mono hbβ hE0, hEE, fun β' hβ' => hcl β' (hbβ.trans hβ')⟩

theorem rwClsOffG_le {l b X0 Xh0 E E' : Ordinal.{0}} (hee : E' ≤ E) (h : RwClsOffG S l b X0 Xh0 E) :
    RwClsOffG S l b X0 Xh0 E' := by
  rcases h with h0 | ⟨E0, hE0, hEE, hcl⟩
  · exact Or.inl h0
  · exact Or.inr ⟨E0, hE0, hee.trans hEE, hcl⟩

theorem rwClsOffG_fam {l b X0 Xh0 E : Ordinal.{0}} (h : RwClsOffG S l b X0 Xh0 E) :
    (X0 = 0 ∧ Xh0 = 0) ∨ ∃ E0, RwG S l b X0 Xh0 E0 ∧ E ≤ E0 := by
  rcases h with h0 | ⟨E0, hE0, hEE, -⟩
  · exact Or.inl h0
  · exact Or.inr ⟨E0, hE0, hEE⟩

theorem rwEX_ex_mono {X0 b β E : Ordinal.{0}} (hbβ : b ≤ β) (h : ∃ j, E < rwEX S X0 b j) :
    ∃ j, E < rwEX S X0 β j := by
  obtain ⟨j, hj⟩ := h; exact ⟨j, hj.trans_le (rwEX_mono_base hbβ j)⟩

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The data of an offset** at level `≥ E`. -/
theorem rwOffG_data {b X0 Xh0 E : Ordinal.{0}}
    (h : (X0 = 0 ∧ Xh0 = 0) ∨ ∃ E0, RwG S l b X0 Xh0 E0 ∧ E ≤ E0) :
    leWe E ∣ X0 ∧ X0 < S.psi 0 (Om (1 + 1 + 1)) ∧ Xh0 < S.psi 0 (Om (1 + 1)) ∧
      ∀ β, b ≤ β → RvOff S l β X0 Xh0 := by
  rcases h with ⟨rfl, rfl⟩ | ⟨E0, hE0, hEE⟩
  · exact ⟨dvd_zero _, rwG3_SC.1, rwG_SC.1, fun _ _ => Or.inl ⟨rfl, rfl⟩⟩
  · obtain ⟨-, -, -, -, hd, -, hX0, hXh0⟩ := rwG_data hl hX hE0
    exact ⟨(leWe_dvd hEE).trans hd, hX0, hXh0, fun β hbβ => Or.inr (rwG_sh hl hX (rwG_mono hbβ hE0))⟩

omit hl hX in
/-- The bounds of a code-level step over an offset. -/
theorem rwOffG_bounds {X0 Xh0 E : Ordinal.{0}} (hEW : E < Om (1 + 1))
    (hΘE : gxTh (upsilon l) (ldAtR S l) E < Om 1) (hX0 : X0 < S.psi 0 (Om (1 + 1 + 1)))
    (hXh0 : Xh0 < S.psi 0 (Om (1 + 1))) :
    X0 + leWe (E + 1) + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)) ∧
      Xh0 + leOe (gxTh (upsilon l) (ldAtR S l) E + 1) + Om 1 < S.psi 0 (Om (1 + 1)) ∧
      X0 + leWe (E + 1) < S.psi 0 (Om (1 + 1 + 1)) ∧
      X0 + leWe E + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)) ∧
      Xh0 + leOe (gxTh (upsilon l) (ldAtR S l) E) + Om 1 < S.psi 0 (Om (1 + 1)) := by
  have hG3 := rwG3_SC (S := S)
  have hWG3 := rwW_lt_G3 (S := S)
  have hG1 := rwG_SC (S := S)
  have hΩG1 := rwO_lt_G (S := S)
  obtain ⟨-, t2, -, t4⟩ := rwTermC_lt (S := S) (ζ := 0) (z := 0) hEW ldOm2_SC.1 hΘE (Om_pos one_ne_zero)
  have t5 : leWe E < S.psi 0 (Om (1 + 1 + 1)) := (leWe_mono le_self_add).trans_lt t2
  have t6 : leOe (gxTh (upsilon l) (ldAtR S l) E) < S.psi 0 (Om (1 + 1)) := (leOe_mono le_self_add).trans_lt t4
  exact ⟨hG3.isPrincipal (hG3.isPrincipal hX0 t2) hWG3, hG1.isPrincipal (hG1.isPrincipal hXh0 t4) hΩG1,
    hG3.isPrincipal hX0 t2, hG3.isPrincipal (hG3.isPrincipal hX0 t5) hWG3,
    hG1.isPrincipal (hG1.isPrincipal hXh0 t6) hΩG1⟩

/-- **`RwClsLevG E ⇒ RwFamClsG E`.** -/
theorem rwFamClsG_of {E : Ordinal.{0}} (he1 : 1 ≤ E) (hE : GxCl (upsilon l) (ldAtR S l) E)
    (hΘE : gxTh (upsilon l) (ldAtR S l) E < Om 1) (hL : RwClsLevG S l E) : RwFamClsG S l E := by
  have hSh := rwShG_sh (S := S) hl hX
  have hk0 : leWe E ≠ 0 := (leWe_pos E).ne'
  have hWe := rwW_le_We he1
  intro b X0 Xh0 hoff hEX ζ
  induction ζ using WellFoundedLT.induction with
  | ind ζ IHz =>
  intro hζ h1 hΘ1 hζT β hbβ hb hrd
  have hζW : ζ < Om (1 + 1) := by obtain ⟨j, hj⟩ := hζT; exact hj.trans (rvEE_lt_Om2 j)
  rcases zero_or_succ_or_isSuccLimit ζ with h0 | ⟨ζ0, hζ0⟩ | hlim
  · subst h0; exact absurd h1 (by simp)
  · rw [succ_eq_add_one] at hζ0
    subst hζ0
    rcases eq_or_ne ζ0 0 with rfl | h00
    · rw [zero_add, mul_one] at hb ⊢
      exact hL b X0 Xh0 (rwClsOffG_le le_self_add hoff) hEX β hbβ hb hrd
    · have hζ0c := rqCode_pred hl hX hζ hζW
      have hΘ0 : gxTh (upsilon l) (ldAtR S l) ζ0 < Om 1 := (gxTh_mono (lt_add_one ζ0).le).trans_lt hΘ1
      have hT0 : ∃ j, ζ0 < rvEE S X0 b E j := by
        obtain ⟨j, hj⟩ := hζT; exact ⟨j, (lt_add_one ζ0).trans hj⟩
      have hF0 := rwG_ext (rwClsOffG_fam hoff) he1 (lt_add_one E) hE hΘE hEX hζ0c h00 hΘ0 hT0
      have hoff' : RwClsOffG S l b (X0 + leWe E * ζ0)
          (Xh0 + leOe (gxTh (upsilon l) (ldAtR S l) E) * gxTh (upsilon l) (ldAtR S l) ζ0) E :=
        Or.inr ⟨E, hF0, le_rfl, fun β' hβ' hb' hrd' =>
          IHz ζ0 (lt_add_one ζ0) hζ0c (Order.one_le_iff_ne_zero.2 h00) hΘ0 hT0 β' hβ' hb' hrd'⟩
      have hEX' : ∃ j, E < rwEX S (X0 + leWe E * ζ0) b j := by
        obtain ⟨j, hj⟩ := hEX; exact ⟨j, hj.trans_le (rwEX_mono_off le_self_add j)⟩
      have e1 : X0 + leWe E * (ζ0 + 1) = X0 + leWe E * ζ0 + leWe E := by rw [mul_add_one, add_assoc]
      rw [e1] at hb ⊢
      exact hL b _ _ hoff' hEX' β hbβ hb hrd
  · have hζ0 : ζ ≠ 0 := hlim.ne_bot
    refine rwClsLimSh hl hX hSh (fun x hxH hx => ?_) hb hrd
    rcases lt_or_ge x X0 with hxX | hxX
    · rcases hoff with ⟨rfl, -⟩ | ⟨E0, hE0, hEE, hcl⟩
      · exact absurd hxX (not_lt.2 zero_le)
      refine ⟨X0, Xh0, ⟨E0, rwG_mono hbβ hE0⟩, ?_, hxX, fun hb' hrd' => hcl β hbβ hb' hrd'⟩
      exact (add_le_add_iff_left X0).2 (hWe.trans (le_mul_left _ (pos_iff_ne_zero.2 hζ0)))
    · obtain ⟨r, rfl⟩ := exists_add_of_le hxX
      have hr : r < leWe E * ζ := (add_lt_add_iff_left X0).1 hx
      have hrW : r < leWe (E + 1) := hr.trans (rvWe_lt_succ hζW)
      obtain ⟨hd, -, -, -⟩ := rwOffG_data hl hX (rwClsOffG_fam hoff)
      have hrH : r ∈ cdHull S l := by
        have h1 := leModP_mem (S := S) (Om (1 + 1) * (E + 1)) hxH
        have hm : (X0 + r) % ω ^ (Om (1 + 1) * (E + 1)) = r := by
          obtain ⟨q, hq⟩ := hd
          change (X0 + r) % leWe (E + 1) = r
          rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hrW]
        rwa [hm] at h1
      have hq : r / leWe E < ζ := (Ordinal.lt_mul_iff_div_lt hk0).1 hr
      have hqc := (ldHull_iff hl hX (hq.trans hζW)).1
        (leDivOp_mem (dvd_mul_right _ _) hrH (by rw [← mul_add_one]; exact hrW))
      have hq1 := hlim.succ_lt hq
      have hq1c := rqCode_succ hl hX hqc (hq1.trans hζW)
      have hΘq : gxTh (upsilon l) (ldAtR S l) (r / leWe E + 1) < Om 1 := (gxTh_mono hq1.le).trans_lt hΘ1
      have hTq : ∃ j, r / leWe E + 1 < rvEE S X0 b E j := by
        obtain ⟨j, hj⟩ := hζT; exact ⟨j, hq1.trans hj⟩
      have hTqβ : ∃ j, r / leWe E + 1 < rvEE S X0 β E j := by
        obtain ⟨j, hj⟩ := hTq; exact ⟨j, hj.trans_le (rvEE_mono_base hbβ j)⟩
      have hF := rwG_ext (rwClsOffG_fam (rwClsOffG_mono hbβ hoff)) he1 (lt_add_one E) hE hΘE
        (rwEX_ex_mono hbβ hEX) hq1c (by simp) hΘq hTqβ
      refine ⟨_, _, ⟨E, hF⟩, ?_, ?_, fun hb' hrd' =>
        IHz _ hq1 hq1c le_add_self hΘq hTq β hbβ hb' hrd'⟩
      · rw [add_assoc]
        refine (add_le_add_iff_left X0).2 ?_
        calc leWe E * (r / leWe E + 1) + Om (1 + 1) ≤ leWe E * (r / leWe E + 1) + leWe E :=
              (add_le_add_iff_left _).2 hWe
          _ = leWe E * (r / leWe E + 1 + 1) := (mul_add_one _ _).symm
          _ ≤ leWe E * ζ := leMulWe_mono (Order.add_one_le_of_lt (hlim.succ_lt hq))
      · refine (add_lt_add_iff_left X0).2 ?_
        rw [mul_add_one]; exact Ordinal.lt_mul_div_add r hk0

/-- **Level `1`.** -/
theorem rwClsLevG_one : RwClsLevG S l 1 := by
  have hSh := rwShG_sh (S := S) hl hX
  have hShM : ∀ b b' X Xh, b ≤ b' → rwShG S l b X Xh → rwShG S l b' X Xh :=
    fun _ _ _ _ h hx => rwShG_mono h hx
  intro b X0 Xh0 hoff _ β hbβ hb hrd
  rw [leWe_one] at hb ⊢
  rcases hoff with ⟨rfl, rfl⟩ | ⟨E0, hE0, -, hcl⟩
  · rw [zero_add] at hb ⊢
    have hb1 : RoBaseE S l (Om (1 + 1) * ((1 : ℕ) : Ordinal.{0})) 0 β := by rwa [Nat.cast_one, mul_one]
    have h := rwCls_one (Sh := rwShG S l) hl hX hb1
    rwa [Nat.cast_one, mul_one] at h
  · have hsh : rwShG S l b X0 Xh0 := ⟨E0, hE0⟩
    exact rwClsW hl hX hSh hShM hsh (rwClsE hl hX hSh hShM hsh hcl) β hbβ hb hrd

/-- **`RwFamClsG E₀ ⇒ RwClsLevG (E₀+1)`.** -/
theorem rwClsLevG_succ {E0 : Ordinal.{0}} (he1 : 1 ≤ E0) (hE0 : GxCl (upsilon l) (ldAtR S l) E0)
    (hE1W : E0 + 1 < Om (1 + 1)) (hΘE1 : gxTh (upsilon l) (ldAtR S l) (E0 + 1) < Om 1)
    (hF : RwFamClsG S l E0) : RwClsLevG S l (E0 + 1) := by
  have hE0W : E0 < Om (1 + 1) := (lt_add_one E0).trans hE1W
  have hΘE0 : gxTh (upsilon l) (ldAtR S l) E0 < Om 1 := (gxTh_mono (lt_add_one E0).le).trans_lt hΘE1
  have hLevC := rwLevC_all hl hX E0 hE0 he1 hE0W
  intro b X0 Xh0 hoff hEX β hbβ hb hrd t ht htT
  obtain ⟨Â, hÂ, hbase⟩ := hrd
  have hb' := hb
  obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hb
  rw [add_zero] at hβd hβA hβown htT
  obtain ⟨hd, hX0G, hXh0G, hoffR⟩ := rwOffG_data hl hX (rwClsOffG_fam hoff)
  have hoffβ := hoffR β hbβ
  obtain ⟨hG3, hG, hX0G3, -, -⟩ := rwOffG_bounds (l := l) hE0W hΘE0 hX0G hXh0G
  obtain ⟨-, -, hX0m, -, hX0cl, -⟩ := rvOff_data hoffβ
  have hEXβ0 : ∃ j, E0 < rwEX S X0 β j := by
    obtain ⟨j, hj⟩ := rwEX_ex_mono hbβ hEX; exact ⟨j, (lt_add_one E0).trans hj⟩
  have heo : E0 < S.psi (β + leWe (X0 + leWe E0)) (Om (1 + 1)) := by
    obtain ⟨j, hj⟩ := hEXβ0; exact rwEX_gt j E0 hj
  obtain ⟨j, hj⟩ := rwEEc_sup hβown hX0m heo hβd hX0cl hX0G3 htT
  rcases j with _ | i
  · exact Or.inl (hj.trans (psiS_bounds (S := S) β 1).1).le
  -- the member `X₀ + W^{E₀}·EE_i` at `β`
  obtain ⟨hic, hiΘ⟩ := rwEEc_code hl hX he1 hE0 hE0W hLevC hoffβ hd hG3 hG hEXβ0 hb' hÂ hbase i
  have hiW : rvEE S X0 β E0 i < Om (1 + 1) := rvEE_lt_Om2 i
  have hi0 : rvEE S X0 β E0 i ≠ 0 := (rvEE_SC i).1.ne'
  have hiT : ∃ j, rvEE S X0 β E0 i < rvEE S X0 β E0 j := ⟨i + 1, rwEEc_lt_succ hβown hX0m heo i⟩
  have hoff1 := rwClsOffG_mono hbβ hoff
  have hcls := hF β X0 Xh0 hoff1 hEXβ0 _ hic (Order.one_le_iff_ne_zero.2 hi0) hiΘ hiT β le_rfl
  have hle : X0 + leWe E0 * rvEE S X0 β E0 i + Om (1 + 1) ≤ X0 + leWe (E0 + 1) := by
    rw [add_assoc]; exact (add_le_add_iff_left X0).2 (rwStep_le he1 hiW)
  have hsb : RoBaseE S l (X0 + leWe E0 * rvEE S X0 β E0 i) 0 β :=
    roBaseE_shift hb' (by rw [add_zero]; exact le_self_add.trans hle) zero_le
  have htT' : t < leTe S (X0 + leWe E0 * rvEE S X0 β E0 i + 0) β := by rw [add_zero]; exact hj
  rcases hcls hsb ⟨Â, hÂ, hbase⟩ t ht htT' with h | ⟨X', e', c, v, hcond, hown, hbo, e1⟩
  · exact Or.inl h
  · refine Or.inr ⟨X', e', c, v, Or.inr ?_, hown, hbo, e1⟩
    rcases hcond with ⟨rfl, h2⟩ | ⟨h1, h2⟩
    · exact ⟨hle, (h2.trans zero_le.ge).trans_lt ((Om_pos one_ne_zero).trans (leOm1_lt_Te _ _))⟩
    · exact ⟨h1.trans (le_self_add.trans hle), h2⟩

/-- **Limit codes.** -/
theorem rwClsLevG_lim {E : Ordinal.{0}} (hlim : IsSuccLimit E)
    (hEW : E < Om (1 + 1)) (hΘE : gxTh (upsilon l) (ldAtR S l) E < Om 1)
    (IH : ∀ c, GxCl (upsilon l) (ldAtR S l) c → 1 ≤ c → c < E → RwClsLevG S l c) : RwClsLevG S l E := by
  have hSh := rwShG_sh (S := S) hl hX
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have he1 : 1 ≤ E := (rvLim_one_lt hlim).le
  have h1Ω : (1 : Ordinal.{0}) < Om 1 := one_lt_omega0.trans (Lw.lw_omega_lt_SC Ph.ph_SC_Om1)
  intro b X0 Xh0 hoff hEX β hbβ hb hrd
  obtain ⟨hd, -, -, -⟩ := rwOffG_data hl hX (rwClsOffG_fam hoff)
  refine rwClsLimSh hl hX hSh (fun x hxH hx => ?_) hb hrd
  rcases lt_or_ge x X0 with hxX | hxX
  · rcases hoff with ⟨rfl, -⟩ | ⟨E0, hE0, hEE, hcl⟩
    · exact absurd hxX (not_lt.2 zero_le)
    exact ⟨X0, Xh0, ⟨E0, rwG_mono hbβ hE0⟩, (add_le_add_iff_left X0).2 (rwW_le_We he1), hxX,
      fun hb' hrd' => hcl β hbβ hb' hrd'⟩
  · obtain ⟨r, rfl⟩ := exists_add_of_le hxX
    have hr : r < leWe E := (add_lt_add_iff_left X0).1 hx
    have hrH : r ∈ cdHull S l := by
      have h1 := leModP_mem (S := S) (Om (1 + 1) * E) hxH
      have hm : (X0 + r) % ω ^ (Om (1 + 1) * E) = r := by
        obtain ⟨q, hq⟩ := hd
        change (X0 + r) % leWe E = r
        rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr]
      rwa [hm] at h1
    set c := log ω r / Om (1 + 1) with hc_def
    have hcH : c ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hrH)
    have hcE : c < E := by
      rcases eq_or_ne r 0 with h0 | hr0
      · rw [hc_def, h0, log_zero_right, Ordinal.zero_div]; exact pos_iff_ne_zero.2 hlim.ne_bot
      have hlogr : log ω r < Om (1 + 1) * E :=
        (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hr0).trans_lt hr)
      exact (Ordinal.lt_mul_iff_div_lt hW0).1 hlogr
    have hcc := (ldHull_iff hl hX (hcE.trans hEW)).1 hcH
    have hc1 := hlim.succ_lt hcE
    have hc1c := rqCode_succ hl hX hcc (hc1.trans hEW)
    have hΘc1 : gxTh (upsilon l) (ldAtR S l) (c + 1) < Om 1 :=
      (gxTh_lt (Z := upsilon l) (At := ldAtR S l) hc1c hc1).trans hΘE
    have hEXc : ∃ j, c + 1 < rwEX S X0 β j := by
      obtain ⟨j, hj⟩ := rwEX_ex_mono hbβ hEX; exact ⟨j, hc1.trans hj⟩
    have hF := rwG_ext (ζ := 1) (rwClsOffG_fam (rwClsOffG_mono hbβ hoff)) le_add_self hc1 hc1c hΘc1 hEXc
      (GxCl.small (gg_one_lt_of_SC hρSC)) one_ne_zero
      (by rw [gxTh_small (gg_one_lt_of_SC hρSC).le]; exact h1Ω) ⟨0, h1Ω⟩
    rw [mul_one] at hF
    refine ⟨_, _, ⟨c + 1, hF⟩, ?_, (add_lt_add_iff_left X0).2 (roLt_We_log r), fun hb' hrd' =>
      IH (c + 1) hc1c le_add_self hc1 β X0 Xh0 (rwClsOffG_le hc1.le (rwClsOffG_mono hbβ hoff)) hEXc β le_rfl
        hb' hrd'⟩
    rw [add_assoc]
    refine (add_le_add_iff_left X0).2 ?_
    calc leWe (c + 1) + Om (1 + 1) ≤ leWe (c + 1) * 1 + Om (1 + 1) := by rw [mul_one]
      _ ≤ leWe (c + 1 + 1) := rwStep_le le_add_self (one_lt_omega0.trans (Lw.lw_omega_lt_SC ldOm2_SC))
      _ ≤ leWe E := leWe_mono (Order.add_one_le_of_lt hc1)

/-- **`RwClsLevG E` for every code `1 ≤ E < Ω₂` with `Θ E < Ω₁`.** -/
theorem rwClsLevG_all : ∀ E, GxCl (upsilon l) (ldAtR S l) E → 1 ≤ E → E < Om (1 + 1) →
    gxTh (upsilon l) (ldAtR S l) E < Om 1 → RwClsLevG S l E := by
  intro E
  induction E using WellFoundedLT.induction with
  | ind E IH =>
  intro hE he1 hEW hΘE
  rcases zero_or_succ_or_isSuccLimit E with h0 | ⟨E0, hE0⟩ | hlim
  · subst h0; exact absurd he1 (by simp)
  · rw [succ_eq_add_one] at hE0
    subst hE0
    have hE0c := rqCode_pred hl hX hE hEW
    rcases eq_or_ne E0 0 with rfl | h00
    · rw [zero_add]; exact rwClsLevG_one hl hX
    · have h10 : 1 ≤ E0 := Order.one_le_iff_ne_zero.2 h00
      have hE0W : E0 < Om (1 + 1) := (lt_add_one E0).trans hEW
      have hΘE0 : gxTh (upsilon l) (ldAtR S l) E0 < Om 1 := (gxTh_mono (lt_add_one E0).le).trans_lt hΘE
      exact rwClsLevG_succ hl hX h10 hE0c hEW hΘE
        (rwFamClsG_of hl hX h10 hE0c hΘE0 (IH E0 (lt_add_one E0) hE0c h10 hE0W hΘE0))
  · exact rwClsLevG_lim hl hX hlim hEW hΘE (fun c hc h1 hcE =>
      IH c hcE hc h1 (hcE.trans hEW) ((gxTh_lt (Z := upsilon l) (At := ldAtR S l) hc hcE).trans hΘE))

/-- **`EX_j(0, 0)` is a code with `Θ(EX_j) < Ω₁`.** -/
theorem rwEX_code0 {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    ∀ j, GxCl (upsilon l) (ldAtR S l) (rwEX S 0 0 j) ∧ gxTh (upsilon l) (ldAtR S l) (rwEX S 0 0 j) < Om 1 := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hG3 := rwG3_SC (S := S)
  have hWG3 := rwW_lt_G3 (S := S)
  have hG1 := rwG_SC (S := S)
  have hΩG1 := rwO_lt_G (S := S)
  have hA1 : A + 1 ∈ S.CSet (A + 1) (S.psi (A + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA) (CSet.one_mem _ _)
  have hown0 : ∀ d, d ≤ leWe ((0 : Ordinal.{0}) + leWe (Om (1 + 1))) →
      (0 : Ordinal.{0}) ∈ S.CSet (0 + d) (S.psi (0 + d) (Om (1 + 1))) := fun _ _ => CSet.zero_mem _ _
  have hX0m : (0 : Ordinal.{0}) ∈ S.CSet 0 (S.psi (0 + leWe 0) (Om (1 + 1))) := CSet.zero_mem _ _
  intro j
  induction j with
  | zero =>
    refine ⟨GxCl.om, ?_⟩
    change gxTh (upsilon l) (ldAtR S l) (Om 1) < Om 1
    rw [gxTh_Om1 hρSC hρ1 hAt]; exact hρ1
  | succ j IHj =>
    obtain ⟨hc, hΘ⟩ := IHj
    have hjW : rwEX S 0 0 j < Om (1 + 1) := rwEX_lt_Om2 j
    have hjH : rwEX S 0 0 j ∈ cdHull S l := (ldHull_iff hl hX hjW).2 hc
    have hj1 : 1 ≤ rwEX S 0 0 j := Order.one_le_iff_pos.2 (rwEX_SC j).1
    have hWj : leWe (rwEX S 0 0 j) < Om ω := roWe_lt_OmW (hjW.trans ldOm2_lt_OmW)
    have hat : rwEX S 0 0 (j + 1) ∈ ldAtR S l :=
      ⟨0 + leWe (0 + leWe (rwEX S 0 0 j)), CSet.add_mem (CSet.zero_mem _ _)
        (leWe_mem (CSet.add_mem (CSet.zero_mem _ _) (leWe_mem hjH))),
        by rw [zero_add, zero_add]; exact (roWe_lt_OmW hWj).trans_le le_self_add, rfl⟩
    refine ⟨GxCl.atom hat, ?_⟩
    obtain ⟨-, t2, -, t4⟩ := rwTermC_lt (S := S) (ζ := 0) (z := 0) hjW ldOm2_SC.1 hΘ (Om_pos one_ne_zero)
    have ht := rwLevC_all hl hX _ hc hj1 hjW 0 0 0 (Or.inl ⟨rfl, rfl⟩) (dvd_zero _)
      (by rw [zero_add]; exact hG3.isPrincipal ((leWe_mono le_self_add).trans_lt t2) hWG3)
      (by rw [zero_add]; exact hG1.isPrincipal ((leOe_mono le_self_add).trans_lt t4) hΩG1)
      ⟨j + 1, rwEX_lt_succ hown0 hX0m j⟩
    have hb : RoBaseE S l (0 + leWe (rwEX S 0 0 j)) 0 0 := by
      refine ⟨dvd_zero _, CSet.zero_mem _ _, ?_, fun d _ => CSet.zero_mem _ _, fun e' _ h' => ?_⟩
      · rw [zero_add, add_zero, zero_add]; exact (roWe_lt_OmW hWj).trans_le le_self_add
      · obtain rfl : e' = 0 := le_antisymm h' zero_le
        exact (SC_psi (InR_Om_succ 1) _).1
    have e1 := ht 0 (A + 1) hb le_rfl hA1 (ldBlk_zero hA hρ)
    have e2 : leTe S (0 + leWe (rwEX S 0 0 j) + 0) 0 = rwEX S 0 0 (j + 1) := by rw [add_zero]; rfl
    rw [e2] at e1
    rw [e1]; exact psi_lt Low.InR_Om_one _

/-- **The atoms below `T_{W^{Ω₂}}(0) = ψ_{Ω₂}(Ω₂^{Ω₂^{Ω₂}})` are own over `0`.** -/
theorem rwClsG_top {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    RwClsAt S l (rwShG S l) (leWe (Om (1 + 1))) 0 0 := by
  have hG3 := rwG3_SC (S := S)
  have hWG3 := rwW_lt_G3 (S := S)
  have hWW : leWe (Om (1 + 1)) < Om ω := roWe_lt_OmW ldOm2_lt_OmW
  have hb : RoBaseE S l (leWe (Om (1 + 1))) 0 0 := by
    refine ⟨dvd_zero _, CSet.zero_mem _ _, ?_, fun d _ => CSet.zero_mem _ _, fun e' _ h' => ?_⟩
    · rw [zero_add, add_zero]; exact (roWe_lt_OmW hWW).trans_le le_self_add
    · obtain rfl : e' = 0 := le_antisymm h' zero_le
      exact (SC_psi (InR_Om_succ 1) _).1
  have hown0 : ∀ d, d ≤ leWe ((0 : Ordinal.{0}) + leWe (Om (1 + 1))) →
      (0 : Ordinal.{0}) ∈ S.CSet (0 + d) (S.psi (0 + d) (Om (1 + 1))) := fun _ _ => CSet.zero_mem _ _
  have hX0m : (0 : Ordinal.{0}) ∈ S.CSet 0 (S.psi (0 + leWe 0) (Om (1 + 1))) := CSet.zero_mem _ _
  have hWWG3 : (0 : Ordinal.{0}) + leWe (Om (1 + 1)) < S.psi 0 (Om (1 + 1 + 1)) := by
    rw [zero_add]; exact (leWe_lt_SC hG3 hWG3 hWG3).1
  have hrd := rwRd_zero (S := S) (l := l) hA hρ
  intro t ht htT
  rw [add_zero] at htT
  have htT0 : t < leTe S (0 + leWe (Om (1 + 1))) 0 := by rwa [zero_add]
  obtain ⟨j, hj⟩ := rwEX_sup hown0 hX0m (dvd_zero _) (fun Q hQ _ => LeCl.zero hQ.1) hWWG3 htT0
  rcases j with _ | i
  · exact Or.inl (hj.trans (psiS_bounds (S := S) 0 1).1).le
  obtain ⟨hic, hiΘ⟩ := rwEX_code0 hl hX hA hρ i
  have hiW : rwEX S 0 0 i < Om (1 + 1) := rwEX_lt_Om2 i
  have hi1 : 1 ≤ rwEX S 0 0 i := Order.one_le_iff_pos.2 (rwEX_SC i).1
  have hcls := rwClsLevG_all hl hX _ hic hi1 hiW hiΘ 0 0 0 (Or.inl ⟨rfl, rfl⟩)
    ⟨i + 1, rwEX_lt_succ hown0 hX0m i⟩ 0 le_rfl
  have hle : (0 : Ordinal.{0}) + leWe (rwEX S 0 0 i) + Om (1 + 1) ≤ leWe (Om (1 + 1)) := by
    rw [zero_add]
    calc leWe (rwEX S 0 0 i) + Om (1 + 1) ≤ leWe (rwEX S 0 0 i) * 1 + Om (1 + 1) := by rw [mul_one]
      _ ≤ leWe (rwEX S 0 0 i + 1) := rwStep_le hi1 (one_lt_omega0.trans (Lw.lw_omega_lt_SC ldOm2_SC))
      _ ≤ leWe (Om (1 + 1)) := leWe_mono (Order.add_one_le_of_lt hiW)
  have hsb : RoBaseE S l (0 + leWe (rwEX S 0 0 i)) 0 0 :=
    roBaseE_shift hb (by rw [add_zero]; exact le_self_add.trans hle) zero_le
  have htT' : t < leTe S (0 + leWe (rwEX S 0 0 i) + 0) 0 := by rw [add_zero]; exact hj
  rcases hcls hsb hrd t ht htT' with h | ⟨X', e', c, v, hcond, hown, hbo, e1⟩
  · exact Or.inl h
  · refine Or.inr ⟨X', e', c, v, Or.inr ?_, hown, hbo, e1⟩
    rcases hcond with ⟨rfl, h2⟩ | ⟨h1, h2⟩
    · exact ⟨hle, (h2.trans zero_le.ge).trans_lt ((Om_pos one_ne_zero).trans (leOm1_lt_Te _ _))⟩
    · exact ⟨h1.trans (le_self_add.trans hle), h2⟩

end Main

end Googology.Trans.PoR.InaccPsi.R2.Rw

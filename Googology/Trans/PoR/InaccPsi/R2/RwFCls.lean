import Googology.Trans.PoR.InaccPsi.R2.RwFam

/-!
# The own atoms for the base-indexed family `RwF`: every atom below `ψ_{Ω₂}(Ω₂^{Ω₂^{Ω₁}})` is own

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `T_E(β) = ψ_{Ω₂}(β + W^E)`, `EE_j(X₀, β, e) = Rv.rvEE S X₀ β e j`,
`Sh = Rw.rwShF S λ` (the family of `Rw.RwF`), closures asked at the bases with a reading (`Rw.RwRd`).

`RwClsOff S λ b X₀ X̂₀ e`: `X₀ = X̂₀ = 0`, or `RwF b X₀ X̂₀ f₀` with `e ≤ f₀` and the atoms below `T_{X₀}(β)` own at
every base `β ≥ b`.  `RwClsLev S λ e`: for every such offset, the atoms below `T_{X₀ + W^e}(β)` are own at every
base `β ≥ b`.  `RwFamCls S λ e`: the same at `X₀ + W^e·ζ` for every code `1 ≤ ζ < EE_j(X₀, b, e)` with `Θ ζ < Ω₁`
(offset with `e < f₀`).

* `rwF_ext` (extending an offset by one term), `rwStep_le`, `rwOff_data`;
* `rwFamCls_of` (**`RwClsLev e ⇒ RwFamCls e`**: one induction on `ζ`: `ζ = 1`, the step `ζ₀ + 1` from the offset
  `X₀ + W^e·ζ₀`, the limits by `Rw.rwClsLimSh`);
* `rwClsLev_one` (the pull-back `Rw.rwClsW`, or `Rw.rwCls_one`), `rwClsLev_succ` (**`RwFamCls e₀ ⇒
  RwClsLev (e₀+1)`**: an atom below `T_{X₀+W^{e₀+1}}(β)` is below some `EE_{i+1} = T_{X₀ + W^{e₀}·EE_i}(β)`,
  `Rv.rvEE_sup`, and `EE_i` is a code with `Θ(EE_i) < Ω₁`, `Rv.rvEE_code`), `rwClsLev_lim`, `rwClsLev_all`
  (**every level `1 ≤ e < ρ_λ`**);
* `rwCls_top` (**the atoms below `T_{W^{Ω₁}}(0) = ψ_{Ω₂}(Ω₂^{Ω₂^{Ω₁}})` are own over `0`**).

No new axiom.  New definitions: the hypothesis names `RwClsOff`, `RwClsLev`, `RwFamCls`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv

variable {S : InaccSeq.{0}}

/-- **An offset with its own atoms** at level `≥ e`. -/
def RwClsOff (S : InaccSeq.{0}) (l b X0 Xh0 e : Ordinal.{0}) : Prop :=
  (X0 = 0 ∧ Xh0 = 0) ∨ ∃ f0, RwF S l b X0 Xh0 f0 ∧ e ≤ f0 ∧
    ∀ β, b ≤ β → RoBaseE S l X0 0 β → RwRd S l β → RwClsAt S l (rwShF S l) X0 0 β

/-- **The level-`e` closure statement.** -/
def RwClsLev (S : InaccSeq.{0}) (l e : Ordinal.{0}) : Prop :=
  ∀ b X0 Xh0, RwClsOff S l b X0 Xh0 e → ∀ β, b ≤ β → RoBaseE S l (X0 + leWe e) 0 β → RwRd S l β →
    RwClsAt S l (rwShF S l) (X0 + leWe e) 0 β

/-- **The level-`e` family closure statement.** -/
def RwFamCls (S : InaccSeq.{0}) (l e : Ordinal.{0}) : Prop :=
  ∀ b X0 Xh0, RwClsOff S l b X0 Xh0 (e + 1) → ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → 1 ≤ ζ →
    gxTh (upsilon l) (ldAtR S l) ζ < Om 1 → (∃ j, ζ < rvEE S X0 b e j) →
    ∀ β, b ≤ β → RoBaseE S l (X0 + leWe e * ζ) 0 β → RwRd S l β →
      RwClsAt S l (rwShF S l) (X0 + leWe e * ζ) 0 β

theorem rwW_le_We {e : Ordinal.{0}} (he : 1 ≤ e) : Om (1 + 1 : Ordinal.{0}) ≤ leWe e := by
  have := leWe_mono he; rwa [leWe_one] at this

/-- `W^e·x + Ω₂ ≤ W^{e+1}` for `1 ≤ e`, `x < Ω₂`. -/
theorem rwStep_le {e x : Ordinal.{0}} (he : 1 ≤ e) (hx : x < Om (1 + 1)) :
    leWe e * x + Om (1 + 1) ≤ leWe (e + 1) := by
  calc leWe e * x + Om (1 + 1) ≤ leWe e * x + leWe e := (add_le_add_iff_left _).2 (rwW_le_We he)
    _ = leWe e * (x + 1) := (mul_add_one _ _).symm
    _ ≤ leWe e * Om (1 + 1) := leMulWe_mono (Order.add_one_le_of_lt hx)
    _ = leWe (e + 1) := (leWe_succ e).symm

/-- **Extending an offset by one term.** -/
theorem rwF_ext {l b X0 Xh0 e e' ζ : Ordinal.{0}}
    (hoff : (X0 = 0 ∧ Xh0 = 0) ∨ ∃ f0, RwF S l b X0 Xh0 f0 ∧ e ≤ f0) (he' : 1 ≤ e') (he'e : e' < e)
    (heρ : e' < upsilon l) (hζ : GxCl (upsilon l) (ldAtR S l) ζ) (hζ0 : ζ ≠ 0)
    (hΘ : gxTh (upsilon l) (ldAtR S l) ζ < Om 1) (hj : ∃ j, ζ < rvEE S X0 b e' j) :
    RwF S l b (X0 + leWe e' * ζ) (Xh0 + leOe e' * gxTh (upsilon l) (ldAtR S l) ζ) e' := by
  rcases hoff with ⟨rfl, rfl⟩ | ⟨f0, hf0, hef⟩
  · rw [zero_add, zero_add]; exact RwF.one he' heρ hζ hζ0 hΘ hj
  · exact RwF.add hf0 he' (he'e.trans_le hef) hζ hζ0 hΘ hj

theorem rwClsOff_mono {l b β X0 Xh0 e : Ordinal.{0}} (hbβ : b ≤ β) (h : RwClsOff S l b X0 Xh0 e) :
    RwClsOff S l β X0 Xh0 e := by
  rcases h with h0 | ⟨f0, hf0, hef, hcl⟩
  · exact Or.inl h0
  · exact Or.inr ⟨f0, rwF_mono hbβ hf0, hef, fun β' hβ' => hcl β' (hbβ.trans hβ')⟩

theorem rwClsOff_le {l b X0 Xh0 e e' : Ordinal.{0}} (hee : e' ≤ e) (h : RwClsOff S l b X0 Xh0 e) :
    RwClsOff S l b X0 Xh0 e' := by
  rcases h with h0 | ⟨f0, hf0, hef, hcl⟩
  · exact Or.inl h0
  · exact Or.inr ⟨f0, hf0, hee.trans hef, hcl⟩

theorem rwClsOff_fam {l b X0 Xh0 e : Ordinal.{0}} (h : RwClsOff S l b X0 Xh0 e) :
    (X0 = 0 ∧ Xh0 = 0) ∨ ∃ f0, RwF S l b X0 Xh0 f0 ∧ e ≤ f0 := by
  rcases h with h0 | ⟨f0, hf0, hef, -⟩
  · exact Or.inl h0
  · exact Or.inr ⟨f0, hf0, hef⟩

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **A code below `Ω₁` is below `ρ_λ`.** -/
theorem rwCode_lt_rho {f : Ordinal.{0}} (hfc : GxCl (upsilon l) (ldAtR S l) f) (hfΩ : f < Om 1) :
    f < upsilon l := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  by_contra h
  push Not at h
  have h1 := gxTh_lt (Z := upsilon l) (At := ldAtR S l) hfc hfΩ
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  rw [gxTh_Om1 hρSC hρ1 hAt] at h1
  have h2 := gxTh_lt (Z := upsilon l) (At := ldAtR S l) (GxCl.small h1) (h1.trans_le h)
  rw [gxTh_small h1.le] at h2
  exact lt_irrefl _ h2

/-- **The data of an offset** at level `≥ e`. -/
theorem rwOff_data {b X0 Xh0 e : Ordinal.{0}} (h : (X0 = 0 ∧ Xh0 = 0) ∨ ∃ f0, RwF S l b X0 Xh0 f0 ∧ e ≤ f0) :
    leWe e ∣ X0 ∧ X0 < S.psi 0 (Om (1 + 1 + 1)) ∧ Xh0 < S.psi 0 (Om (1 + 1)) ∧
      ∀ β, b ≤ β → RvOff S l β X0 Xh0 := by
  rcases h with ⟨rfl, rfl⟩ | ⟨f0, hf0, hef⟩
  · exact ⟨dvd_zero _, rwG3_SC.1, rwG_SC.1, fun _ _ => Or.inl ⟨rfl, rfl⟩⟩
  · obtain ⟨-, -, hd, -, hX0, hXh0⟩ := rwF_data hl hX hf0
    exact ⟨(leWe_dvd hef).trans hd, hX0, hXh0, fun β hbβ => Or.inr (rwF_sh hl hX (rwF_mono hbβ hf0))⟩

/-- The bounds of a level step over an offset. -/
theorem rwOff_bounds {X0 Xh0 e : Ordinal.{0}} (heρ : e < upsilon l) (hX0 : X0 < S.psi 0 (Om (1 + 1 + 1)))
    (hXh0 : Xh0 < S.psi 0 (Om (1 + 1))) :
    X0 + leWe (e + 1) + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)) ∧
      Xh0 + leOe (e + 1) + Om 1 < S.psi 0 (Om (1 + 1)) ∧ X0 + leWe (e + 1) < S.psi 0 (Om (1 + 1 + 1)) ∧
      X0 + leWe e + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)) ∧ Xh0 + leOe e + Om 1 < S.psi 0 (Om (1 + 1)) := by
  obtain ⟨-, hρ1⟩ := leRho hl hX
  have hG3 := rwG3_SC (S := S)
  have hWG3 := rwW_lt_G3 (S := S)
  have hG1 := rwG_SC (S := S)
  have hΩG1 := rwO_lt_G (S := S)
  have heΩ : e < Om 1 := heρ.trans hρ1
  obtain ⟨-, t2, -, t4⟩ := rwTerm_lt (S := S) (y := 0) heΩ gg_Om1_lt_Om2 (Om_pos one_ne_zero)
  have t5 : leWe e < S.psi 0 (Om (1 + 1 + 1)) := (leWe_mono le_self_add).trans_lt t2
  have t6 : leOe e < S.psi 0 (Om (1 + 1)) := (leOe_mono le_self_add).trans_lt t4
  exact ⟨hG3.isPrincipal (hG3.isPrincipal hX0 t2) hWG3, hG1.isPrincipal (hG1.isPrincipal hXh0 t4) hΩG1,
    hG3.isPrincipal hX0 t2, hG3.isPrincipal (hG3.isPrincipal hX0 t5) hWG3,
    hG1.isPrincipal (hG1.isPrincipal hXh0 t6) hΩG1⟩

/-- **`RwClsLev e ⇒ RwFamCls e`.** -/
theorem rwFamCls_of {e : Ordinal.{0}} (he1 : 1 ≤ e) (heρ : e < upsilon l) (hL : RwClsLev S l e) :
    RwFamCls S l e := by
  have hSh := rwShF_sh (S := S) hl hX
  have hk0 : leWe e ≠ 0 := (leWe_pos e).ne'
  have hWe := rwW_le_We he1
  intro b X0 Xh0 hoff ζ
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
      exact hL b X0 Xh0 (rwClsOff_le le_self_add hoff) β hbβ hb hrd
    · have hζ0c := rqCode_pred hl hX hζ hζW
      have hΘ0 : gxTh (upsilon l) (ldAtR S l) ζ0 < Om 1 := (gxTh_mono (lt_add_one ζ0).le).trans_lt hΘ1
      have hT0 : ∃ j, ζ0 < rvEE S X0 b e j := by
        obtain ⟨j, hj⟩ := hζT; exact ⟨j, (lt_add_one ζ0).trans hj⟩
      have hF0 := rwF_ext (rwClsOff_fam hoff) he1 (lt_add_one e) heρ hζ0c h00 hΘ0 hT0
      have hoff' : RwClsOff S l b (X0 + leWe e * ζ0) (Xh0 + leOe e * gxTh (upsilon l) (ldAtR S l) ζ0) e :=
        Or.inr ⟨e, hF0, le_rfl, fun β' hβ' hb' hrd' =>
          IHz ζ0 (lt_add_one ζ0) hζ0c (Order.one_le_iff_ne_zero.2 h00) hΘ0 hT0 β' hβ' hb' hrd'⟩
      have e1 : X0 + leWe e * (ζ0 + 1) = X0 + leWe e * ζ0 + leWe e := by rw [mul_add_one, add_assoc]
      rw [e1] at hb ⊢
      exact hL b _ _ hoff' β hbβ hb hrd
  · have hζ0 : ζ ≠ 0 := hlim.ne_bot
    refine rwClsLimSh hl hX hSh (fun x hxH hx => ?_) hb hrd
    rcases lt_or_ge x X0 with hxX | hxX
    · rcases hoff with ⟨rfl, -⟩ | ⟨f0, hf0, hef, hcl⟩
      · exact absurd hxX (not_lt.2 zero_le)
      refine ⟨X0, Xh0, ⟨f0, rwF_mono hbβ hf0⟩, ?_, hxX, fun hb' hrd' => hcl β hbβ hb' hrd'⟩
      exact (add_le_add_iff_left X0).2 (hWe.trans (le_mul_left _ (pos_iff_ne_zero.2 hζ0)))
    · obtain ⟨r, rfl⟩ := exists_add_of_le hxX
      have hr : r < leWe e * ζ := (add_lt_add_iff_left X0).1 hx
      have hrW : r < leWe (e + 1) := hr.trans (rvWe_lt_succ hζW)
      obtain ⟨hd, -, -, -⟩ := rwOff_data hl hX (rwClsOff_fam hoff)
      have hrH : r ∈ cdHull S l := by
        have h1 := leModP_mem (S := S) (Om (1 + 1) * (e + 1)) hxH
        have hm : (X0 + r) % ω ^ (Om (1 + 1) * (e + 1)) = r := by
          obtain ⟨q, hq⟩ := hd
          change (X0 + r) % leWe (e + 1) = r
          rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hrW]
        rwa [hm] at h1
      have hq : r / leWe e < ζ := (Ordinal.lt_mul_iff_div_lt hk0).1 hr
      have hqc := (ldHull_iff hl hX (hq.trans hζW)).1
        (leDivOp_mem (dvd_mul_right _ _) hrH (by rw [← mul_add_one]; exact hrW))
      have hq1 := hlim.succ_lt hq
      have hq1c := rqCode_succ hl hX hqc (hq1.trans hζW)
      have hΘq : gxTh (upsilon l) (ldAtR S l) (r / leWe e + 1) < Om 1 := (gxTh_mono hq1.le).trans_lt hΘ1
      have hTq : ∃ j, r / leWe e + 1 < rvEE S X0 b e j := by
        obtain ⟨j, hj⟩ := hζT; exact ⟨j, hq1.trans hj⟩
      have hTqβ : ∃ j, r / leWe e + 1 < rvEE S X0 β e j := by
        obtain ⟨j, hj⟩ := hTq; exact ⟨j, hj.trans_le (rvEE_mono_base hbβ j)⟩
      have hF := rwF_ext (rwClsOff_fam (rwClsOff_mono hbβ hoff)) he1 (lt_add_one e) heρ hq1c
        (by simp) hΘq hTqβ
      refine ⟨_, _, ⟨e, hF⟩, ?_, ?_, fun hb' hrd' =>
        IHz _ hq1 hq1c le_add_self hΘq hTq β hbβ hb' hrd'⟩
      · rw [add_assoc]
        refine (add_le_add_iff_left X0).2 ?_
        calc leWe e * (r / leWe e + 1) + Om (1 + 1) ≤ leWe e * (r / leWe e + 1) + leWe e :=
              (add_le_add_iff_left _).2 hWe
          _ = leWe e * (r / leWe e + 1 + 1) := (mul_add_one _ _).symm
          _ ≤ leWe e * ζ := leMulWe_mono (Order.add_one_le_of_lt (hlim.succ_lt hq))
      · refine (add_lt_add_iff_left X0).2 ?_
        rw [mul_add_one]; exact Ordinal.lt_mul_div_add r hk0

/-- **Level `1`.** -/
theorem rwClsLev_one : RwClsLev S l 1 := by
  have hSh := rwShF_sh (S := S) hl hX
  have hShM : ∀ b b' X Xh, b ≤ b' → rwShF S l b X Xh → rwShF S l b' X Xh :=
    fun _ _ _ _ h hx => rwShF_mono h hx
  intro b X0 Xh0 hoff β hbβ hb hrd
  rw [leWe_one] at hb ⊢
  rcases hoff with ⟨rfl, rfl⟩ | ⟨f0, hf0, -, hcl⟩
  · rw [zero_add] at hb ⊢
    have hb1 : RoBaseE S l (Om (1 + 1) * ((1 : ℕ) : Ordinal.{0})) 0 β := by rwa [Nat.cast_one, mul_one]
    have h := rwCls_one (Sh := rwShF S l) hl hX hb1
    rwa [Nat.cast_one, mul_one] at h
  · have hsh : rwShF S l b X0 Xh0 := ⟨f0, hf0⟩
    exact rwClsW hl hX hSh hShM hsh (rwClsE hl hX hSh hShM hsh hcl) β hbβ hb hrd

/-- **`RwFamCls e₀ ⇒ RwClsLev (e₀+1)`.** -/
theorem rwClsLev_succ {e0 : Ordinal.{0}} (he1 : 1 ≤ e0) (heρ : e0 + 1 < upsilon l) (hF : RwFamCls S l e0) :
    RwClsLev S l (e0 + 1) := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have he0ρ : e0 < upsilon l := (lt_add_one e0).trans heρ
  have he0Ω : e0 < Om 1 := he0ρ.trans hρ1
  have hLevE := rvLevE_all hl hX e0 he1 he0ρ
  intro b X0 Xh0 hoff β hbβ hb hrd t ht htT
  obtain ⟨Â, hÂ, hbase⟩ := hrd
  have hb' := hb
  obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hb
  rw [add_zero] at hβd hβA hβown htT
  obtain ⟨hd, hX0G, hXh0G, hoffR⟩ := rwOff_data hl hX (rwClsOff_fam hoff)
  have hoffβ := hoffR β hbβ
  obtain ⟨hG3, hG, hX0G3, -, -⟩ := rwOff_bounds hl hX he0ρ hX0G hXh0G
  obtain ⟨-, -, hX0m, -, hX0cl, -⟩ := rvOff_data hoffβ
  obtain ⟨j, hj⟩ := rvEE_sup hβown hX0m he0Ω hβd hX0cl hX0G3 htT
  rcases j with _ | i
  · exact Or.inl (hj.trans (psiS_bounds (S := S) β 1).1).le
  -- the member `X₀ + W^{e₀}·EE_i` at `β`
  obtain ⟨hic, hiΘ⟩ := rvEE_code hl hX he1 he0ρ hLevE hoffβ hd hG3 hG hb' hÂ hbase i
  have hiW : rvEE S X0 β e0 i < Om (1 + 1) := rvEE_lt_Om2 i
  have hi0 : rvEE S X0 β e0 i ≠ 0 := (rvEE_SC i).1.ne'
  have hiT : ∃ j, rvEE S X0 β e0 i < rvEE S X0 β e0 j := ⟨i + 1, rvEE_lt_succ hβown hX0m he0Ω i⟩
  have hoff1 := rwClsOff_mono hbβ hoff
  have hcls := hF β X0 Xh0 hoff1 _ hic (Order.one_le_iff_ne_zero.2 hi0) hiΘ hiT β le_rfl
  have hle : X0 + leWe e0 * rvEE S X0 β e0 i + Om (1 + 1) ≤ X0 + leWe (e0 + 1) := by
    rw [add_assoc]; exact (add_le_add_iff_left X0).2 (rwStep_le he1 hiW)
  have hsb : RoBaseE S l (X0 + leWe e0 * rvEE S X0 β e0 i) 0 β :=
    roBaseE_shift hb' (by rw [add_zero]; exact le_self_add.trans hle) zero_le
  have htT' : t < leTe S (X0 + leWe e0 * rvEE S X0 β e0 i + 0) β := by rw [add_zero]; exact hj
  rcases hcls hsb ⟨Â, hÂ, hbase⟩ t ht htT' with h | ⟨X', e', c, v, hcond, hown, hbo, e1⟩
  · exact Or.inl h
  · refine Or.inr ⟨X', e', c, v, Or.inr ?_, hown, hbo, e1⟩
    rcases hcond with ⟨rfl, h2⟩ | ⟨h1, h2⟩
    · exact ⟨hle, (h2.trans zero_le.ge).trans_lt ((Om_pos one_ne_zero).trans (leOm1_lt_Te _ _))⟩
    · exact ⟨h1.trans (le_self_add.trans hle), h2⟩

/-- **Limit levels.** -/
theorem rwClsLev_lim {e : Ordinal.{0}} (hlim : IsSuccLimit e) (heρ : e < upsilon l)
    (IH : ∀ e', 1 ≤ e' → e' < e → RwClsLev S l e') : RwClsLev S l e := by
  have hSh := rwShF_sh (S := S) hl hX
  have he1 : 1 ≤ e := (rvLim_one_lt hlim).le
  intro b X0 Xh0 hoff β hbβ hb hrd
  refine rwClsLimSh hl hX hSh (fun x hxH hx => ?_) hb hrd
  rcases lt_or_ge x X0 with hxX | hxX
  · rcases hoff with ⟨rfl, -⟩ | ⟨f0, hf0, hef, hcl⟩
    · exact absurd hxX (not_lt.2 zero_le)
    exact ⟨X0, Xh0, ⟨f0, rwF_mono hbβ hf0⟩, (add_le_add_iff_left X0).2 (rwW_le_We he1), hxX,
      fun hb' hrd' => hcl β hbβ hb' hrd'⟩
  · obtain ⟨r, rfl⟩ := exists_add_of_le hxX
    have hr : r < leWe e := (add_lt_add_iff_left X0).1 hx
    obtain ⟨e', h1, he', hre'⟩ := rvLt_We_lim hlim hr
    have hF := rwF_ext (ζ := 1) (rwClsOff_fam (rwClsOff_mono hbβ hoff)) h1 he' (he'.trans heρ)
      (GxCl.small (gg_one_lt_of_SC (leRho hl hX).1)) one_ne_zero
      (by rw [gxTh_small (gg_one_lt_of_SC (leRho hl hX).1).le]
          exact one_lt_omega0.trans (Lw.lw_omega_lt_SC Ph.ph_SC_Om1))
      ⟨0, one_lt_omega0.trans (Lw.lw_omega_lt_SC Ph.ph_SC_Om1)⟩
    rw [mul_one] at hF
    refine ⟨_, _, ⟨e', hF⟩, ?_, (add_lt_add_iff_left X0).2 hre', fun hb' hrd' =>
      IH e' h1 he' β X0 Xh0 (rwClsOff_le he'.le (rwClsOff_mono hbβ hoff)) β le_rfl hb' hrd'⟩
    rw [add_assoc]
    refine (add_le_add_iff_left X0).2 ?_
    calc leWe e' + Om (1 + 1) ≤ leWe e' * 1 + Om (1 + 1) := by rw [mul_one]
      _ ≤ leWe (e' + 1) := rwStep_le h1 (one_lt_omega0.trans (Lw.lw_omega_lt_SC ldOm2_SC))
      _ ≤ leWe e := leWe_mono (Order.add_one_le_of_lt he')

/-- **`RwClsLev e` for every level `1 ≤ e < ρ_λ`.** -/
theorem rwClsLev_all : ∀ e, 1 ≤ e → e < upsilon l → RwClsLev S l e := by
  intro e
  induction e using WellFoundedLT.induction with
  | ind e IH =>
  intro he1 heρ
  rcases zero_or_succ_or_isSuccLimit e with h0 | ⟨e0, he0⟩ | hlim
  · subst h0; exact absurd he1 (by simp)
  · rw [succ_eq_add_one] at he0
    subst he0
    rcases eq_or_ne e0 0 with rfl | h00
    · rw [zero_add]; exact rwClsLev_one hl hX
    · have h10 : 1 ≤ e0 := Order.one_le_iff_ne_zero.2 h00
      have he0ρ : e0 < upsilon l := (lt_add_one e0).trans heρ
      exact rwClsLev_succ hl hX h10 heρ (rwFamCls_of hl hX h10 he0ρ (IH e0 (lt_add_one e0) h10 he0ρ))
  · exact rwClsLev_lim hl hX hlim heρ (fun e' h1 he' => IH e' he' h1 (he'.trans heρ))

/-- **The atoms below `T_{W^{Ω₁}}(0) = ψ_{Ω₂}(Ω₂^{Ω₂^{Ω₁}})` are own over `0`.** -/
theorem rwCls_top (hrd : RwRd S l 0) : RwClsAt S l (rwShF S l) (leWe (Om 1)) 0 0 := by
  have hSh := rwShF_sh (S := S) hl hX
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hΩW : leWe (Om 1) < Om ω := roWe_lt_OmW (gg_Om1_lt_Om2.trans ldOm2_lt_OmW)
  have hb : RoBaseE S l (leWe (Om 1)) 0 0 := by
    refine ⟨dvd_zero _, CSet.zero_mem _ _, ?_, fun d _ => CSet.zero_mem _ _, fun e' _ h' => ?_⟩
    · rw [zero_add, add_zero]; exact (roWe_lt_OmW hΩW).trans_le le_self_add
    · obtain rfl : e' = 0 := le_antisymm h' zero_le
      exact (SC_psi (InR_Om_succ 1) _).1
  refine rwClsLimSh hl hX hSh (fun x hxH hx => ?_) hb hrd
  set f := log ω x / Om (1 + 1) with hf_def
  have hfH : f ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hxH)
  have hfΩ : f < Om 1 := by
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [hf_def, log_zero_right, Ordinal.zero_div]; exact Om_pos one_ne_zero
    have hlogx : log ω x < Om (1 + 1) * Om 1 :=
      (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hx0).trans_lt hx)
    exact (Ordinal.lt_mul_iff_div_lt hW0).1 hlogx
  have hfc := (ldHull_iff hl hX (hfΩ.trans gg_Om1_lt_Om2)).1 hfH
  have hfρ : f < upsilon l := rwCode_lt_rho hl hX hfc hfΩ
  have hf1ρ : f + 1 < upsilon l := hρSC.isSuccLimit.succ_lt hfρ
  have h1Ω : (1 : Ordinal.{0}) < Om 1 := one_lt_omega0.trans (Lw.lw_omega_lt_SC Ph.ph_SC_Om1)
  have hF := rwF_ext (S := S) (b := 0) (e := f + 1 + 1) (ζ := 1) (Or.inl ⟨rfl, rfl⟩) le_add_self (lt_add_one _) hf1ρ
    (GxCl.small (gg_one_lt_of_SC hρSC)) one_ne_zero
    (by rw [gxTh_small (gg_one_lt_of_SC hρSC).le]; exact h1Ω) ⟨0, h1Ω⟩
  rw [zero_add, zero_add, mul_one] at hF
  refine ⟨_, _, ⟨f + 1, hF⟩, ?_, roLt_We_log x, fun hb' hrd' => ?_⟩
  · calc leWe (f + 1) + Om (1 + 1) ≤ leWe (f + 1) * 1 + Om (1 + 1) := by rw [mul_one]
      _ ≤ leWe (f + 1 + 1) := rwStep_le le_add_self (one_lt_omega0.trans (Lw.lw_omega_lt_SC ldOm2_SC))
      _ ≤ leWe (Om 1) := leWe_mono (Order.add_one_le_of_lt (Ph.ph_SC_Om1.isSuccLimit.succ_lt hfΩ))
  · have h := rwClsLev_all hl hX (f + 1) le_add_self hf1ρ 0 0 0 (Or.inl ⟨rfl, rfl⟩) 0 le_rfl
      (by rw [zero_add]; exact hb') hrd'
    rwa [zero_add] at h

end Main

end Googology.Trans.PoR.InaccPsi.R2.Rw

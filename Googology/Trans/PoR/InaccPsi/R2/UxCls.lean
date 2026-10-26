import Googology.Trans.PoR.InaccPsi.R2.UxEX

/-!
# The own atoms of the level system past `Γ₂`: every atom below `ψ_{Ω₂}(W^{W^{E_b}})` is own

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `T_E(β) = ψ_{Ω₂}(β + W^E)`, `EE_j(X₀, β, E) = Rv.rvEE S X₀ β E j`,
`EX_j = Rw.rwEX`, `Y₃ = ψ_{Ω₃}(Ω₃)`, `C₂(Q) = Ug.UgC S 2 Q`, `CL₃ = Ug.UgCL`, `Ow = Uu.uuOw` (`∃ j, E < EX_j`
at a code level `E < Ω₂`, `CL₃ E` at `E ≥ Ω₂`), `Sh = Uu.uuShG S λ E_b Th Ow` (the family of a level system
`Uu.UuLS S λ E_b Th Ow`, `E_b ≤ Y₃`).

The closure argument of `St.stClsLev_all` / `St.stRepG` past `Γ₂`: `UxClsOff` (an offset with its own atoms),
`UxClsLev` (the atoms below `T_{X₀ + W^E}(β)`), `UxFamCls` (the same at `X₀ + W^E·ζ`).

* `uxOw_mono`, `uxG_ext`, `uxOffG_data`, `uxOff_bounds`;
* `uxFamCls_of`, `uxClsLev_one`, `uxClsLev_succ` (**the own predicate of `E₀` from that of `E₀+1`**: at a code
  level by `EX_j`, at a level `≥ Ω₂` by the collapse `Um.umCollD` and `Uq.uqC_pred`; then `Uj.ujEE_sup`,
  `Uj.ujEE_code`), `uxClsLev_lim` (**the normal form of an atom gives an own level `c + 1 < E`**: the `C₂` code
  `c + 1` by `uxExtrRem`, `uxLogW`; at a code level `c + 1 < Ω₂` below a level `E ≥ Ω₂` the own predicate
  `∃ j, c + 1 < EX_j` by `uxEX_own`), `uxClsLev_all` (**every level `1 ≤ E < E_b` of the hull**);
* `uxRepG` (**every atom `s < ψ_{Ω₂}(W^{W^{E_b}})` is `≤ ψ_{Ω₂}(0)` or `ψ_{Ω₂}(c)` with `c` own over `0`**).

No new axiom.  New definitions: the hypothesis names `UxClsOff`, `UxClsLev`, `UxFamCls`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ux

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rq
  Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sj Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Ug
  Googology.Trans.PoR.InaccPsi.R2.Uj Googology.Trans.PoR.InaccPsi.R2.Um Googology.Trans.PoR.InaccPsi.R2.Uq
  Googology.Trans.PoR.InaccPsi.R2.Uu

variable {S : InaccSeq.{0}} {Eb : Ordinal.{0}} {Th : Ordinal.{0} → Ordinal.{0} → Ordinal.{0}}

/-- **The own predicate is monotone** in the base and the offset. -/
theorem uxOw_mono {E b β X0 X0' : Ordinal.{0}} (h : uuOw S E b X0) (hb : b ≤ β) (hX : X0 ≤ X0') :
    uuOw S E β X0' := by
  rcases h with ⟨hW, j, hj⟩ | ⟨hW, h⟩
  · exact Or.inl ⟨hW, j, (hj.trans_le (rwEX_mono_base hb j)).trans_le (rwEX_mono_off hX j)⟩
  · exact Or.inr ⟨hW, ugCL_mono h hb hX⟩

/-! ## The closure statements -/

/-- **An offset with its own atoms** at level `≥ E`. -/
def UxClsOff (S : InaccSeq.{0}) (l Eb : Ordinal.{0}) (Th : Ordinal.{0} → Ordinal.{0} → Ordinal.{0})
    (b X0 Xh0 E : Ordinal.{0}) : Prop :=
  (X0 = 0 ∧ Xh0 = 0) ∨ ∃ E0, UuG S l Eb Th (uuOw S) b X0 Xh0 E0 ∧ E ≤ E0 ∧
    ∀ β, b ≤ β → RoBaseE S l X0 0 β → RwRd S l β → RwClsAt S l (uuShG S l Eb Th (uuOw S)) X0 0 β

/-- **The level closure statement.** -/
def UxClsLev (S : InaccSeq.{0}) (l Eb : Ordinal.{0}) (Th : Ordinal.{0} → Ordinal.{0} → Ordinal.{0})
    (E : Ordinal.{0}) : Prop :=
  ∀ b X0 Xh0, UxClsOff S l Eb Th b X0 Xh0 E → uuOw S E b X0 →
    ∀ β, b ≤ β → RoBaseE S l (X0 + leWe E) 0 β → RwRd S l β →
      RwClsAt S l (uuShG S l Eb Th (uuOw S)) (X0 + leWe E) 0 β

/-- **The level family closure statement.** -/
def UxFamCls (S : InaccSeq.{0}) (l Eb : Ordinal.{0}) (Th : Ordinal.{0} → Ordinal.{0} → Ordinal.{0})
    (E : Ordinal.{0}) : Prop :=
  ∀ b X0 Xh0, UxClsOff S l Eb Th b X0 Xh0 (E + 1) → uuOw S E b X0 →
    ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → 1 ≤ ζ → (∃ j, ζ < rvEE S X0 b E j) →
    ∀ β, b ≤ β → RoBaseE S l (X0 + leWe E * ζ) 0 β → RwRd S l β →
      RwClsAt S l (uuShG S l Eb Th (uuOw S)) (X0 + leWe E * ζ) 0 β

/-- **Extending an offset by one term.** -/
theorem uxG_ext {l b X0 Xh0 E E' ζ : Ordinal.{0}}
    (hoff : (X0 = 0 ∧ Xh0 = 0) ∨ ∃ E0, UuG S l Eb Th (uuOw S) b X0 Xh0 E0 ∧ E ≤ E0) (he' : 1 ≤ E')
    (he'e : E' < E) (hEH : E' ∈ cdHull S l) (hE : E' < Eb) (hcl : uuOw S E' b X0)
    (hζ : GxCl (upsilon l) (ldAtR S l) ζ) (hζ0 : ζ ≠ 0) (hj : ∃ j, ζ < rvEE S X0 b E' j) :
    UuG S l Eb Th (uuOw S) b (X0 + leWe E' * ζ) (Xh0 + leOe (Th l E') * gxTh (upsilon l) (ldAtR S l) ζ) E' := by
  rcases hoff with ⟨rfl, rfl⟩ | ⟨E0, hE0, hEE⟩
  · rw [zero_add, zero_add]; exact UuG.one he' hEH hE hcl hζ hζ0 hj
  · exact UuG.add hE0 he' (he'e.trans_le hEE) hEH hE hcl hζ hζ0 hj

theorem uxClsOff_mono {l b β X0 Xh0 E : Ordinal.{0}} (hS : UuLS S l Eb Th (uuOw S)) (hbβ : b ≤ β)
    (h : UxClsOff S l Eb Th b X0 Xh0 E) : UxClsOff S l Eb Th β X0 Xh0 E := by
  rcases h with h0 | ⟨E0, hE0, hEE, hcl⟩
  · exact Or.inl h0
  · exact Or.inr ⟨E0, uuG_mono hS hbβ hE0, hEE, fun β' hβ' => hcl β' (hbβ.trans hβ')⟩

theorem uxClsOff_le {l b X0 Xh0 E E' : Ordinal.{0}} (hee : E' ≤ E) (h : UxClsOff S l Eb Th b X0 Xh0 E) :
    UxClsOff S l Eb Th b X0 Xh0 E' := by
  rcases h with h0 | ⟨E0, hE0, hEE, hcl⟩
  · exact Or.inl h0
  · exact Or.inr ⟨E0, hE0, hee.trans hEE, hcl⟩

theorem uxClsOff_fam {l b X0 Xh0 E : Ordinal.{0}} (h : UxClsOff S l Eb Th b X0 Xh0 E) :
    (X0 = 0 ∧ Xh0 = 0) ∨ ∃ E0, UuG S l Eb Th (uuOw S) b X0 Xh0 E0 ∧ E ≤ E0 := by
  rcases h with h0 | ⟨E0, hE0, hEE, -⟩
  · exact Or.inl h0
  · exact Or.inr ⟨E0, hE0, hEE⟩

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) (hS : UuLS S l Eb Th (uuOw S))

include hl hX hS

/-- **The data of an offset** at level `≥ E`. -/
theorem uxOffG_data {b X0 Xh0 E : Ordinal.{0}}
    (h : (X0 = 0 ∧ Xh0 = 0) ∨ ∃ E0, UuG S l Eb Th (uuOw S) b X0 Xh0 E0 ∧ E ≤ E0) :
    leWe E ∣ X0 ∧ X0 < ugY S ∧ Xh0 < ujY S 0 ∧ ∀ β, b ≤ β → UjOff S l β X0 Xh0 := by
  rcases h with ⟨rfl, rfl⟩ | ⟨E0, hE0, hEE⟩
  · exact ⟨dvd_zero _, uqY_SC.1, uuY2_SC.1, fun _ _ => Or.inl ⟨rfl, rfl⟩⟩
  · obtain ⟨-, -, -, hd, -, hX0, hXh0⟩ := uuG_data hl hX hS hE0
    exact ⟨(leWe_dvd hEE).trans hd, hX0, hXh0, fun β hbβ => Or.inr (uuG_sh hl hX hS (uuG_mono hS hbβ hE0))⟩

omit hl hX in
/-- The bounds of a step over an offset. -/
theorem uxOff_bounds {X0 Xh0 E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (he1 : 1 ≤ E) (hE : E < Eb)
    (hX0 : X0 < ugY S) (hXh0 : Xh0 < ujY S 0) :
    X0 + leWe (E + 1) + Om (1 + 1) < ugY S ∧
      Xh0 + leOe (Th l E + 1) + Om 1 < ujY S 0 ∧
      X0 + leWe (E + 1) < ugY S ∧ X0 + leWe E < ugY S := by
  have hY := uqY_SC (S := S)
  have hWY := uqW_lt_Y (S := S)
  have hY2 := uuY2_SC (S := S)
  have hΩY2 := uuOm1_lt_Y2 (S := S)
  have t2 := uuWe_lt_Y (S := S) (hE.trans_le hS.leY)
  have t4 := uuOe_lt_Y2 (hS.ltY E hEH he1 hE)
  have t5 : leWe E < ugY S := (leWe_mono le_self_add).trans_lt t2
  exact ⟨hY.isPrincipal (hY.isPrincipal hX0 t2) hWY, hY2.isPrincipal (hY2.isPrincipal hXh0 t4) hΩY2,
    hY.isPrincipal hX0 t2, hY.isPrincipal hX0 t5⟩

/-- **`UxClsLev E ⇒ UxFamCls E`.** -/
theorem uxFamCls_of {E : Ordinal.{0}} (he1 : 1 ≤ E) (hEH : E ∈ cdHull S l) (hE : E < Eb)
    (hL : UxClsLev S l Eb Th E) : UxFamCls S l Eb Th E := by
  have hSh := uuShG_sh hl hX hS
  have hk0 : leWe E ≠ 0 := (leWe_pos E).ne'
  have hWe := rwW_le_We he1
  intro b X0 Xh0 hoff hEX ζ
  induction ζ using WellFoundedLT.induction with
  | ind ζ IHz =>
  intro hζ h1 hζT β hbβ hb hrd
  have hζW : ζ < Om (1 + 1) := by obtain ⟨j, hj⟩ := hζT; exact hj.trans (rvEE_lt_Om2 j)
  rcases zero_or_succ_or_isSuccLimit ζ with h0 | ⟨ζ0, hζ0⟩ | hlim
  · subst h0; exact absurd h1 (by simp)
  · rw [succ_eq_add_one] at hζ0
    subst hζ0
    rcases eq_or_ne ζ0 0 with rfl | h00
    · rw [zero_add, mul_one] at hb ⊢
      exact hL b X0 Xh0 (uxClsOff_le le_self_add hoff) hEX β hbβ hb hrd
    · have hζ0c := rqCode_pred hl hX hζ hζW
      have hT0 : ∃ j, ζ0 < rvEE S X0 b E j := by
        obtain ⟨j, hj⟩ := hζT; exact ⟨j, (lt_add_one ζ0).trans hj⟩
      have hF0 := uxG_ext (uxClsOff_fam hoff) he1 (lt_add_one E) hEH hE hEX hζ0c h00 hT0
      have hoff' : UxClsOff S l Eb Th b (X0 + leWe E * ζ0)
          (Xh0 + leOe (Th l E) * gxTh (upsilon l) (ldAtR S l) ζ0) E :=
        Or.inr ⟨E, hF0, le_rfl, fun β' hβ' hb' hrd' =>
          IHz ζ0 (lt_add_one ζ0) hζ0c (Order.one_le_iff_ne_zero.2 h00) hT0 β' hβ' hb' hrd'⟩
      have hEX' : uuOw S E b (X0 + leWe E * ζ0) := uxOw_mono hEX le_rfl le_self_add
      have e1 : X0 + leWe E * (ζ0 + 1) = X0 + leWe E * ζ0 + leWe E := by rw [mul_add_one, add_assoc]
      rw [e1] at hb ⊢
      exact hL b _ _ hoff' hEX' β hbβ hb hrd
  · have hζ0 : ζ ≠ 0 := hlim.ne_bot
    refine uuClsLimSh hl hX hSh (fun x hxH hx => ?_) hb hrd
    rcases lt_or_ge x X0 with hxX | hxX
    · rcases hoff with ⟨rfl, -⟩ | ⟨E0, hE0, hEE, hcl⟩
      · exact absurd hxX (not_lt.2 zero_le)
      refine ⟨X0, Xh0, ⟨E0, uuG_mono hS hbβ hE0⟩, ?_, hxX, fun hb' hrd' => hcl β hbβ hb' hrd'⟩
      exact (add_le_add_iff_left X0).2 (hWe.trans (le_mul_left _ (pos_iff_ne_zero.2 hζ0)))
    · obtain ⟨r, rfl⟩ := exists_add_of_le hxX
      have hr : r < leWe E * ζ := (add_lt_add_iff_left X0).1 hx
      have hrW : r < leWe (E + 1) := hr.trans (rvWe_lt_succ hζW)
      obtain ⟨hd, -, -, -⟩ := uxOffG_data hl hX hS (uxClsOff_fam hoff)
      have hrH : r ∈ cdHull S l := snHullRem hxH hd hrW
      have hq : r / leWe E < ζ := (Ordinal.lt_mul_iff_div_lt hk0).1 hr
      have hqc := (ldHull_iff hl hX (hq.trans hζW)).1
        (leDivOp_mem (dvd_mul_right _ _) hrH (by rw [← mul_add_one]; exact hrW))
      have hq1 := hlim.succ_lt hq
      have hq1c := rqCode_succ hl hX hqc (hq1.trans hζW)
      have hTq : ∃ j, r / leWe E + 1 < rvEE S X0 b E j := by
        obtain ⟨j, hj⟩ := hζT; exact ⟨j, hq1.trans hj⟩
      have hTqβ : ∃ j, r / leWe E + 1 < rvEE S X0 β E j := by
        obtain ⟨j, hj⟩ := hTq; exact ⟨j, hj.trans_le (rvEE_mono_base hbβ j)⟩
      have hF := uxG_ext (uxClsOff_fam (uxClsOff_mono hS hbβ hoff)) he1 (lt_add_one E) hEH hE
        (uxOw_mono hEX hbβ le_rfl) hq1c (by simp) hTqβ
      refine ⟨_, _, ⟨E, hF⟩, ?_, ?_, fun hb' hrd' =>
        IHz _ hq1 hq1c le_add_self hTq β hbβ hb' hrd'⟩
      · rw [add_assoc]
        refine (add_le_add_iff_left X0).2 ?_
        calc leWe E * (r / leWe E + 1) + Om (1 + 1) ≤ leWe E * (r / leWe E + 1) + leWe E :=
              (add_le_add_iff_left _).2 hWe
          _ = leWe E * (r / leWe E + 1 + 1) := (mul_add_one _ _).symm
          _ ≤ leWe E * ζ := leMulWe_mono (Order.add_one_le_of_lt (hlim.succ_lt hq))
      · refine (add_lt_add_iff_left X0).2 ?_
        rw [mul_add_one]; exact Ordinal.lt_mul_div_add r hk0

/-- **Level `1`.** -/
theorem uxClsLev_one : UxClsLev S l Eb Th 1 := by
  have hSh := uuShG_sh hl hX hS
  have hShM : ∀ b b' X Xh, b ≤ b' → uuShG S l Eb Th (uuOw S) b X Xh → uuShG S l Eb Th (uuOw S) b' X Xh :=
    fun _ _ _ _ h hx => uuShG_mono hS h hx
  intro b X0 Xh0 hoff _ β hbβ hb hrd
  rw [leWe_one] at hb ⊢
  rcases hoff with ⟨rfl, rfl⟩ | ⟨E0, hE0, -, hcl⟩
  · rw [zero_add] at hb ⊢
    have hb1 : RoBaseE S l (Om (1 + 1) * ((1 : ℕ) : Ordinal.{0})) 0 β := by rwa [Nat.cast_one, mul_one]
    have h := rwCls_one (Sh := uuShG S l Eb Th (uuOw S)) hl hX hb1
    rwa [Nat.cast_one, mul_one] at h
  · have hsh : uuShG S l Eb Th (uuOw S) b X0 Xh0 := ⟨E0, hE0⟩
    exact uuClsW hl hX hSh hShM hsh (uuClsE hl hX hSh hShM hsh hcl) β hbβ hb hrd

/-- **`UxFamCls E₀ ⇒ UxClsLev (E₀+1)`.** -/
theorem uxClsLev_succ {E0 : Ordinal.{0}} (he1 : 1 ≤ E0) (hE0H : E0 ∈ cdHull S l)
    (hE1 : E0 + 1 < Eb) (hF : UxFamCls S l Eb Th E0) : UxClsLev S l Eb Th (E0 + 1) := by
  have hE0 : E0 < Eb := (lt_add_one E0).trans hE1
  intro b X0 Xh0 hoff hcl β hbβ hb hrd t ht htT
  obtain ⟨Â, hÂ, hbase⟩ := hrd
  have hb' := hb
  obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hb
  rw [add_zero] at hβd hβA hβown htT
  obtain ⟨hd, hX0G, hXh0G, hoffR⟩ := uxOffG_data hl hX hS (uxClsOff_fam hoff)
  have hoffβ := hoffR β hbβ
  obtain ⟨hG3, hG, hX0G3, -⟩ := uxOff_bounds hS hE0H he1 hE0 hX0G hXh0G
  obtain ⟨-, -, hX0m, -, hX0cl, -⟩ := ujOff_data hoffβ
  -- the own predicate of `E₀` at `β`
  have hclβ : uuOw S (E0 + 1) β X0 := uxOw_mono hcl hbβ le_rfl
  have hclE0 : uuOw S E0 β X0 := by
    rcases hclβ with ⟨hW, j, hj⟩ | ⟨hW, h3⟩
    · exact Or.inl ⟨(lt_add_one E0).trans hW, j, (lt_add_one E0).trans hj⟩
    · have hW0 : Om (1 + 1 : Ordinal.{0}) ≤ E0 := by
        by_contra h
        push Not at h
        exact absurd (ldOm2_SC.isSuccLimit.succ_lt h) (not_lt.2 hW)
      obtain ⟨z, hz1, hz2, hz⟩ := umCollD hoffβ hX0G3 hb' h3 (y := E0) le_self_add
      refine Or.inr ⟨hW0, fun Q hQ hQ' => ?_⟩
      rcases hz2.lt_or_eq with hlt | rfl
      · have : z = E0 := le_antisymm (Order.lt_add_one_iff.1 hlt) hz1
        rw [← this]; exact hz Q hQ hQ'
      · exact uqC_pred hQ uxTwo_ne E0 (hz Q hQ hQ')
  have hP := hS.own E0 hE0H he1 hE0
  have hEo := hP.dat β X0 hclE0
  obtain ⟨j, hj⟩ := ujEE_sup hβown hX0m hEo.mem hEo.cl hβd hX0cl hX0G3 htT
  rcases j with _ | i
  · exact Or.inl (hj.trans (psiS_bounds (S := S) β 1).1).le
  obtain ⟨hic, -⟩ := ujEE_code hl hX hP (hS.lev E0 hE0H he1 hE0) hoffβ hd hG3 hG hclE0 hb' hÂ hbase i
  have hiW : rvEE S X0 β E0 i < Om (1 + 1) := rvEE_lt_Om2 i
  have hi0 : rvEE S X0 β E0 i ≠ 0 := (rvEE_SC i).1.ne'
  have hiT : ∃ j, rvEE S X0 β E0 i < rvEE S X0 β E0 j := ⟨i + 1, ujEE_lt_succ hβown hX0m hEo.mem i⟩
  have hoff1 := uxClsOff_mono hS hbβ hoff
  have hcls := hF β X0 Xh0 hoff1 hclE0 _ hic (Order.one_le_iff_ne_zero.2 hi0) hiT β le_rfl
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

/-- **Limit levels**: the normal form of an atom below `T_{X₀ + W^E}(β)` gives an own level `c + 1 < E`. -/
theorem uxClsLev_lim {E : Ordinal.{0}} (hlim : IsSuccLimit E) (hEH : E ∈ cdHull S l)
    (hE : E < Eb)
    (IH : ∀ c, c ∈ cdHull S l → 1 ≤ c → c < E → UxClsLev S l Eb Th c) : UxClsLev S l Eb Th E := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have he1 : 1 ≤ E := (rvLim_one_lt hlim).le
  intro b X0 Xh0 hoff hcl β hbβ hb hrd t ht htT
  have hb' := hb
  obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hb
  rw [add_zero] at hβd hβA hβown htT
  obtain ⟨hdX0, hX0G, hXh0G, hoffR⟩ := uxOffG_data hl hX hS (uxClsOff_fam hoff)
  have hoffβ := hoffR β hbβ
  obtain ⟨-, -, -, hX0G3⟩ := uxOff_bounds hS hEH he1 hE hX0G hXh0G
  obtain ⟨-, -, hX0m, -, hX0cl, -⟩ := ujOff_data hoffβ
  obtain ⟨d, rfl, hnf, hdH, -⟩ := snNf ht hρ1.le
  have hdlt : d < β + leWe (X0 + leWe E) := by
    by_contra h
    push Not at h
    exact absurd htT (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) h).1)
  rcases le_or_gt d β with hdβ | hβd'
  · exact Or.inl (psi_mono (S := S) (InR_Om_succ 1) hdβ).1
  obtain ⟨d', rfl⟩ := exists_add_of_le hβd'.le
  have hd'W : d' < leWe (X0 + leWe E) := (add_lt_add_iff_left β).1 hdlt
  have hd'0 : d' ≠ 0 := fun h => by rw [h, add_zero] at hβd'; exact lt_irrefl _ hβd'
  rcases lt_or_ge d' (leWe X0) with hdX | hdX
  · -- an atom of the offset
    rcases hoff with ⟨rfl, -⟩ | ⟨E0, hE0, hEE, hclo⟩
    · rw [leWe_zero] at hdX
      exact absurd (Order.lt_one_iff.1 hdX) hd'0
    have hbX0 : RoBaseE S l X0 0 β :=
      roBaseE_shift hb' (by rw [add_zero]; exact le_self_add) zero_le
    have htX : S.psi (β + d') (Om (1 + 1)) < leTe S (X0 + 0) β := by
      rw [add_zero]; exact psi_lt_psi (InR_Om_succ 1) ((add_lt_add_iff_left β).2 hdX) hnf
    rcases hclo β hbβ hbX0 hrd _ ht htX with h | ⟨X', e', c, v, hcond, hown, hbo, e1⟩
    · exact Or.inl h
    · refine Or.inr ⟨X', e', c, v, Or.inr ?_, hown, hbo, e1⟩
      rcases hcond with ⟨rfl, h2⟩ | ⟨h1, h2⟩
      · refine ⟨(add_le_add_iff_left X').2 (rwW_le_We he1), ?_⟩
        exact (h2.trans zero_le.ge).trans_lt ((Om_pos one_ne_zero).trans (leOm1_lt_Te _ _))
      · exact ⟨h1.trans le_self_add, h2⟩
  -- the level `c + 1` of the atom
  obtain ⟨Y, hY_def⟩ : ∃ Y, Y = log ω d' / Om (1 + 1) := ⟨_, rfl⟩
  obtain ⟨hXY, hYE⟩ := sjLogW hdX hd'W
  rw [← hY_def] at hXY hYE
  obtain ⟨r, hr⟩ := exists_add_of_le hXY
  have hrE : r < leWe E := (add_lt_add_iff_left X0).1 (hr ▸ hYE)
  obtain ⟨c, hc_def⟩ : ∃ c, c = log ω r / Om (1 + 1) := ⟨_, rfl⟩
  have hcE : c < E := by
    rcases eq_or_ne r 0 with h0 | hr0
    · rw [hc_def, h0, log_zero_right, Ordinal.zero_div]; exact pos_iff_ne_zero.2 hlim.ne_bot
    have h1 : leWe 0 ≤ r := by rw [leWe_zero]; exact Order.one_le_iff_ne_zero.2 hr0
    rw [hc_def]; exact (sjLogW h1 hrE).2
  have hc1 := hlim.succ_lt hcE
  have hrc : r < leWe (c + 1) := by rw [hc_def]; exact roLt_We_log r
  have hd'c : d' < leWe (X0 + leWe (c + 1)) := by
    refine (roLt_We_log d').trans_le (leWe_mono ?_)
    rw [← hY_def, hr, add_assoc]
    exact (add_le_add_iff_left X0).2 (Order.add_one_le_of_lt hrc)
  have htc : S.psi (β + d') (Om (1 + 1)) < S.psi (β + leWe (X0 + leWe (c + 1))) (Om (1 + 1)) :=
    psi_lt_psi (InR_Om_succ 1) ((add_lt_add_iff_left β).2 hd'c) hnf
  -- the closure condition `CL₃ (c + 1)`, from the normal form
  have hcl3 : UgCL S (c + 1) β X0 := by
    intro Q hQ hQ'
    have htQ := htc.le.trans hQ'
    have hd'Q := uxExtrRem hnf hβd hd'W hX0G3 hQ htQ
    have hYQ : UgC S (1 + 1) Q Y := by rw [hY_def]; exact uxLogW hQ hd'Q
    have hX0Q : UgC S (1 + 1) Q X0 :=
      hX0cl Q hQ (((psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
        (leWe_mono le_self_add))).1).trans hQ')
    have hrQ : UgC S (1 + 1) Q r := by
      have h := (ugCDec hQ uxTwo_ne Y hYQ).1 X0 hX0Q hXY
      rwa [hr, Ordinal.add_sub_cancel] at h
    rw [hc_def]; exact UgC.add (uxLogW hQ hrQ) (UgC.small (gg_one_lt_of_SC hQ))
  -- the own predicate of `c + 1`
  have hcl1 : uuOw S (c + 1) β X0 := by
    rcases lt_or_ge (c + 1) (Om (1 + 1)) with hcW | hcW
    · refine Or.inl ⟨hcW, ?_⟩
      rcases hcl with ⟨hEW, j, hj⟩ | ⟨hEW, -⟩
      · exact ⟨j, (hc1.trans hj).trans_le (rwEX_mono_base hbβ j)⟩
      · have hWE : X0 + leWe (Om (1 + 1)) ≤ X0 + leWe E := (add_le_add_iff_left X0).2 (leWe_mono hEW)
        have hTc : c + 1 < S.psi (β + leWe (X0 + leWe (c + 1))) (Om (1 + 1)) :=
          uxCode_lt (SC_psi (InR_Om_succ 1) _) (hcl3 _ (SC_psi (InR_Om_succ 1) _) le_rfl) hcW
        exact uxEX_own (fun d hd => hβown d (hd.trans (leWe_mono hWE))) hX0m ((leWe_dvd hWE).trans hβd)
          hX0cl (hWE.trans_lt hX0G3) hcW hTc
    · exact Or.inr ⟨hcW, hcl3⟩
  -- the hull
  have hd'H : d' ∈ cdHull S l := snHullRem hdH hβd hd'W
  have hYH : Y ∈ cdHull S l := by rw [hY_def]; exact ldDivK_mem ldOm2_SC (leLog_mem hd'H)
  have hrH : r ∈ cdHull S l := by
    have h := snHullRem (A := ConjT.Aη S (cdEta S l)) (ρ := upsilon l) (β := X0) (d' := r) (K := E)
      (by rw [← hr]; exact hYH) hdX0 hrE
    exact h
  have hcH : c + 1 ∈ cdHull S l := by
    rw [hc_def]; exact CSet.succ_mem (ldDivK_mem ldOm2_SC (leLog_mem hrH))
  have hle : X0 + leWe (c + 1) + Om (1 + 1) ≤ X0 + leWe E := by
    rw [add_assoc]
    refine (add_le_add_iff_left X0).2 ?_
    calc leWe (c + 1) + Om (1 + 1) ≤ leWe (c + 1) * 1 + Om (1 + 1) := by rw [mul_one]
      _ ≤ leWe (c + 1 + 1) := rwStep_le le_add_self (one_lt_omega0.trans (Lw.lw_omega_lt_SC ldOm2_SC))
      _ ≤ leWe E := leWe_mono (Order.add_one_le_of_lt hc1)
  have hbc : RoBaseE S l (X0 + leWe (c + 1)) 0 β :=
    roBaseE_shift hb' (by rw [add_zero]; exact le_self_add.trans hle) zero_le
  have htT' : S.psi (β + d') (Om (1 + 1)) < leTe S (X0 + leWe (c + 1) + 0) β := by
    rw [add_zero]; exact htc
  rcases IH (c + 1) hcH le_add_self hc1 β X0 Xh0 (uxClsOff_le hc1.le (uxClsOff_mono hS hbβ hoff)) hcl1 β
    le_rfl hbc hrd _ ht htT' with h | ⟨X', e', c', v, hcond, hown, hbo, e1⟩
  · exact Or.inl h
  · refine Or.inr ⟨X', e', c', v, Or.inr ?_, hown, hbo, e1⟩
    rcases hcond with ⟨rfl, h2⟩ | ⟨h1, h2⟩
    · exact ⟨hle, (h2.trans zero_le.ge).trans_lt ((Om_pos one_ne_zero).trans (leOm1_lt_Te _ _))⟩
    · exact ⟨h1.trans (le_self_add.trans hle), h2⟩

/-- **`UxClsLev E` for every level `1 ≤ E < E_b` of the hull.** -/
theorem uxClsLev_all : ∀ E, E ∈ cdHull S l → 1 ≤ E → E < Eb → UxClsLev S l Eb Th E := by
  intro E
  induction E using WellFoundedLT.induction with
  | ind E IH =>
  intro hEH he1 hE
  rcases zero_or_succ_or_isSuccLimit E with h0 | ⟨E0, hE0⟩ | hlim
  · subst h0; exact absurd he1 (by simp)
  · rw [succ_eq_add_one] at hE0
    subst hE0
    have hE0H : E0 ∈ cdHull S l := mem_of_add_one_mem hEH
    rcases eq_or_ne E0 0 with rfl | h00
    · rw [zero_add]; exact uxClsLev_one hl hX hS
    · have h10 : 1 ≤ E0 := Order.one_le_iff_ne_zero.2 h00
      have hE0 : E0 < Eb := (lt_add_one E0).trans hE
      exact uxClsLev_succ hl hX hS h10 hE0H hE
        (uxFamCls_of hl hX hS h10 hE0H hE0 (IH E0 (lt_add_one E0) hE0H h10 hE0))
  · exact uxClsLev_lim hl hX hS hlim hEH hE (fun c hcH h1 hcE => IH c hcE hcH h1 (hcE.trans hE))

/-- **Every atom `s < ψ_{Ω₂}(W^{W^{E_b}})` is `≤ ψ_{Ω₂}(0)` or `ψ_{Ω₂}(c)` with `c` own over `0`** for the family
`uuShG` of a level system past `Γ₂`. -/
theorem uxRepG {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    (s : Ordinal.{0}) (hs : s ∈ ldAtR S l) (hsε : s < S.psi (leWe (leWe Eb)) (Om (1 + 1))) :
    s ≤ S.psi 0 (Om (1 + 1)) ∨ ∃ X e c v, (X = 0 ∨ ∃ Xh, uuShG S l Eb Th (uuOw S) 0 X Xh) ∧
      RwOwn S l (uuShG S l Eb Th (uuOw S)) X e 0 c v ∧ RoBaseE S l X e 0 ∧ s = S.psi c (Om (1 + 1)) := by
  obtain ⟨-, hρ1⟩ := leRho hl hX
  have hY := uqY_SC (S := S)
  have hWY := uqW_lt_Y (S := S)
  obtain ⟨d, rfl, hnf, hdH, -⟩ := snNf hs hρ1.le
  have hdε : d < leWe (leWe Eb) := by
    by_contra h
    push Not at h
    exact absurd hsε (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) h).1)
  rcases eq_or_ne d 0 with rfl | hd0
  · exact Or.inl le_rfl
  set Y := log ω d / Om (1 + 1) with hY_def
  set E := log ω Y / Om (1 + 1) + 1 with hE_def
  have hYlt : Y < leWe Eb := by
    have h1 : leWe 0 ≤ d := by rw [leWe_zero]; exact Order.one_le_iff_ne_zero.2 hd0
    exact (sjLogW h1 hdε).2
  have hlY : log ω Y / Om (1 + 1) < Eb := by
    rcases eq_or_ne Y 0 with h0 | hY0
    · rw [h0, log_zero_right, Ordinal.zero_div]; exact pos_iff_ne_zero.2 hS.lim.ne_bot
    · have h1 : leWe 0 ≤ Y := by rw [leWe_zero]; exact Order.one_le_iff_ne_zero.2 hY0
      exact (sjLogW h1 hYlt).2
  have hE : E < Eb := hS.lim.succ_lt hlY
  have hEY : E < ugY S := hE.trans_le hS.leY
  have he1 : 1 ≤ E := le_add_self
  have hdW : d < leWe (leWe E) := by
    refine (roLt_We_log d).trans_le (leWe_mono ?_)
    exact Order.add_one_le_of_lt (roLt_We_log Y)
  have hdY : d < ugY S := hdW.trans (leWe_lt_SC hY hWY (leWe_lt_SC hY hWY hEY).1).1
  have hst : S.psi d (Om (1 + 1)) < S.psi (0 + leWe (0 + leWe E)) (Om (1 + 1)) := by
    rw [zero_add, zero_add]; exact psi_lt_psi (InR_Om_succ 1) hdW hnf
  have hcl3 : UgCL S E 0 0 := by
    intro Q hQ hQ'
    have htQ := hst.le.trans hQ'
    have hdQ : UgC S (1 + 1) Q d := uqC_mem hQ htQ (CSet_mono le_rfl htQ hnf) hdY
    exact UgC.add (uxLogW hQ (uxLogW hQ hdQ)) (UgC.small (gg_one_lt_of_SC hQ))
  have hcl : uuOw S E 0 0 := by
    rcases lt_or_ge E (Om (1 + 1)) with hEW | hEW
    · refine Or.inl ⟨hEW, ?_⟩
      have hTE : E < S.psi (0 + leWe (0 + leWe E)) (Om (1 + 1)) :=
        uxCode_lt (SC_psi (InR_Om_succ 1) _) (hcl3 _ (SC_psi (InR_Om_succ 1) _) le_rfl) hEW
      exact uxEX_own (fun _ _ => CSet.zero_mem _ _) (CSet.zero_mem _ _) (dvd_zero _)
        (fun Q hQ _ => UgC.zero hQ.1) (by rw [zero_add]; exact (leWe_lt_SC hY hWY hWY).1) hEW hTE
    · exact Or.inr ⟨hEW, hcl3⟩
  have hEH : E ∈ cdHull S l :=
    CSet.succ_mem (ldDivK_mem ldOm2_SC (leLog_mem (ldDivK_mem ldOm2_SC (leLog_mem hdH))))
  have hEW : E < Om ω := hEY.trans (ugY_lt_Om3.trans Ry.ryOm3_lt)
  have hb : RoBaseE S l (0 + leWe E) 0 0 := by
    refine ⟨dvd_zero _, CSet.zero_mem _ _, ?_, fun d _ => CSet.zero_mem _ _, fun e' _ h' => ?_⟩
    · rw [zero_add, add_zero, zero_add]
      exact (roWe_lt_OmW (roWe_lt_OmW hEW)).trans_le le_self_add
    · obtain rfl : e' = 0 := le_antisymm h' zero_le
      exact (SC_psi (InR_Om_succ 1) _).1
  have hcls := uxClsLev_all hl hX hS E hEH he1 hE 0 0 0 (Or.inl ⟨rfl, rfl⟩) hcl 0 le_rfl hb
    (rwRd_zero (S := S) (l := l) hA hρ)
  have htT : S.psi d (Om (1 + 1)) < leTe S (0 + leWe E + 0) 0 := by rw [add_zero]; exact hst
  rcases hcls _ hs htT with h | ⟨X', e', c, v, -, hown, hbo, e1⟩
  · exact Or.inl h
  · rw [zero_add] at e1
    exact Or.inr ⟨X', e', c, v, rwOwn_sh hown, hown, hbo, e1⟩

end Main

end Googology.Trans.PoR.InaccPsi.R2.Ux

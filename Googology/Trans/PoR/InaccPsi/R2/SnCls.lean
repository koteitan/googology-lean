import Googology.Trans.PoR.InaccPsi.R2.SnG

/-!
# The own atoms for the family `SnG`: every atom below `ψ_{Ω₂}(ε_{Ω₂+1})` is own

`Θ = gxTh ρ_λ (ldAtR λ)`, `Θ̂ = Sg.sgThH S λ`, `W^E = Ω₂^E`, `T_E(β) = ψ_{Ω₂}(β + W^E)`,
`EE_j(X₀, β, E) = Rv.rvEE S X₀ β E j`, `Sh = Sn.snShG S λ`, `ε = ε_{Ω₂+1}`, `CL = Sn.SnCL`.

`SnClsOff S λ b X₀ X̂₀ E`: `X₀ = X̂₀ = 0`, or `SnG b X₀ X̂₀ E₀` with `E ≤ E₀` and the atoms below `T_{X₀}(β)` own at
every base `β ≥ b` with a reading.  `SnClsLev S λ E`: for every such offset with the closure condition of `E`, the
atoms below `T_{X₀ + W^E}(β)` are own at every base `β ≥ b` with a reading.  `SnFamCls S λ E`: the same at
`X₀ + W^E·ζ`, `1 ≤ ζ < EE_j(X₀, b, E)` a code.

* `snNf` (**every atom of the hull is `ψ_{Ω₂}(d)` with `d` in normal form, in the hull, below `A`**; no bound by
  `θ`), `snExtrRem` (the digit part `d' < W^K` of a normal-form argument `β + d'` with `W^K ∣ β` is a code over
  every strongly critical `Q ≥ ψ_{Ω₂}(β + d')`), `snLogW`, `snLeCl_mono`;
* `snFamCls_of` (`SnClsLev E ⇒ SnFamCls E`), `snClsLev_one`, `snClsLev_succ` (**`SnFamCls E₀ ⇒
  SnClsLev (E₀+1)`**: the closure condition of `E₀` from that of `E₀+1` by `Sj.sjCode`), `snClsLev_lim`
  (**limit exponents**: the normal form of the atom gives an own level `c + 1 < E` above it), `snClsLev_all`
  (**every `1 ≤ E < ε` in the hull**);
* `snRepG` (**every atom `s < ψ_{Ω₂}(ε_{Ω₂+1})` is `≤ ψ_{Ω₂}(0)` or `ψ_{Ω₂}(c)` with `c` own over `0`** for the
  family `snShG`: the analogue of `Rw.rwRepG`; the closure condition of the level is read off the normal form).

No new axiom.  New definitions: the hypothesis names `SnClsOff`, `SnClsLev`, `SnFamCls`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rq
  Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj

variable {S : InaccSeq.{0}}

/-! ## Normal forms and codes -/

/-- **Every atom of `ldAt S A ρ` is `ψ_{Ω₂}(d)` with `d` in normal form, `d ∈ Cl(A, ρ)`, `d < A`.** -/
theorem snNf {A ρ t : Ordinal.{0}} (ht : t ∈ ldAt S A ρ) (hρ : ρ ≤ Om 1) :
    ∃ d, t = S.psi d (Om (1 + 1)) ∧ d ∈ S.CSet d (S.psi d (Om (1 + 1))) ∧ d ∈ S.CSet A ρ ∧ d < A := by
  obtain ⟨a, haH, haA, rfl⟩ := ht
  have hκ : S.InR (Om (1 + 1)) := InR_Om_succ 1
  have hκL : Om (1 + 1 : Ordinal.{0}) ≤ S.Lam := (lt_Lam_of_mem zero_le (mxOm2_mem (S := S) 0 0)).le
  have hρL : ρ ≤ S.Lam := hρ.trans ((Om_le_Om.2 (le_add_self : (1 : Ordinal.{0}) ≤ 1 + 1)).trans hκL)
  have haL : a < S.Lam := lt_Lam_of_mem hρL haH
  have heq := psi_M_eq hκ haL
  have hself := M_mem_self hκ haL
  have hmem : S.psi a (Om (1 + 1)) ∈ S.CSet A ρ := CSet.psi_mem haA hκ (mxOm2_mem _ _) haH
  have hρt : ρ ≤ S.psi a (Om (1 + 1)) := hρ.trans (psiS_bounds (S := S) a 1).1.le
  rw [← heq] at hmem hρt
  obtain ⟨h1, h2⟩ := arg_mem_of_psi_mem hκ hmem hρt hρL hself
  exact ⟨_, heq.symm, hself, h1, h2⟩

/-- Codes over `Q` are codes over every `Q' ≥ Q`. -/
theorem snLeCl_mono {κ Q Q' x : Ordinal.{0}} (h : LeCl κ Q x) (hQ : Q ≤ Q') : LeCl κ Q' x := by
  induction h with
  | small h => exact LeCl.small (h.trans_le hQ)
  | om => exact LeCl.om
  | add _ _ ihx ihy => exact LeCl.add ihx ihy
  | phi _ _ ihx ihy => exact LeCl.phi ihx ihy

/-- A code `x` gives the code `log_W x = log_ω x / Ω₂`. -/
theorem snLogW {Q x : Ordinal.{0}} (hQ : SC Q) (h : LeCl (Om (1 + 1)) Q x) :
    LeCl (Om (1 + 1)) Q (log ω x / Om (1 + 1)) :=
  sjCl_div hQ ldOm2_SC _ (leClDec hQ ldOm2_SC x h).2

/-- **The digit part of a normal-form argument is a code**: `β + d'` in normal form, `W^K ∣ β`, `d' < W^K`,
`K < ψ_{Ω₃}(0)` give that `d'` is a code over every strongly critical `Q ≥ ψ_{Ω₂}(β + d')`. -/
theorem snExtrRem {β d' K Q : Ordinal.{0}}
    (hnf : β + d' ∈ S.CSet (β + d') (S.psi (β + d') (Om (1 + 1))))
    (hKd : leWe K ∣ β) (hd' : d' < leWe K) (hKG : K < S.psi 0 (Om (1 + 1 + 1)))
    (hQ : SC Q) (htQ : S.psi (β + d') (Om (1 + 1)) ≤ Q) : LeCl (Om (1 + 1)) Q d' := by
  have hG3 : SC (S.psi 0 (Om (1 + 1 + 1))) := SC_psi (InR_Om_succ (1 + 1)) 0
  have hWG3 : Om (1 + 1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1 + 1)) := (psiS_bounds (S := S) 0 (1 + 1)).1
  have hΩQ : Om 1 < Q := (psiS_bounds (S := S) _ 1).1.trans_le htQ
  have h0 := snKey hQ hΩQ (snColl htQ) _ (CSet_mono le_rfl htQ hnf)
  have hc2 := LeCl.mod hQ.1 ldOm2_SC.isPrincipal (Om (1 + 1) * K) h0
  change LeCl (Om (1 + 1)) Q ((β + d') % S.psi 0 (Om (1 + 1 + 1)) % leWe K) at hc2
  rw [Ordinal.mod_mod_of_dvd _ (leWe_lt_SC hG3 hWG3 hKG).2] at hc2
  have hm : (β + d') % leWe K = d' := by
    obtain ⟨q, hq⟩ := hKd
    rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hd']
  rwa [hm] at hc2

/-- The hull digit part: `(β + d') % W^K = d'`. -/
theorem snHullRem {A ρ β d' K : Ordinal.{0}} (h : β + d' ∈ S.CSet A ρ) (hKd : leWe K ∣ β) (hd' : d' < leWe K) :
    d' ∈ S.CSet A ρ := by
  have h1 := leModP_mem (S := S) (Om (1 + 1) * K) h
  have hm : (β + d') % ω ^ (Om (1 + 1) * K) = d' := by
    obtain ⟨q, hq⟩ := hKd
    change (β + d') % leWe K = d'
    rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hd']
  rwa [hm] at h1

/-- `ε_{Ω₂+1}` is a limit. -/
theorem snEps_succ_lt {x : Ordinal.{0}} (hx : x < veblen 1 (Om (1 + 1) + 1)) :
    x + 1 < veblen 1 (Om (1 + 1) + 1) := by
  have hp := Ph.ph_veblen_prin (1 : Ordinal.{0}) (Om (1 + 1) + 1)
  have h1 : (1 : Ordinal.{0}) < veblen 1 (Om (1 + 1) + 1) :=
    (gg_one_lt_of_SC ldOm2_SC).trans_le (le_self_add.trans (right_le_veblen 1 _))
  exact hp hx h1

/-! ## The closure statements -/

/-- **An offset with its own atoms** at level `≥ E`. -/
def SnClsOff (S : InaccSeq.{0}) (l b X0 Xh0 E : Ordinal.{0}) : Prop :=
  (X0 = 0 ∧ Xh0 = 0) ∨ ∃ E0, SnG S l b X0 Xh0 E0 ∧ E ≤ E0 ∧
    ∀ β, b ≤ β → RoBaseE S l X0 0 β → RwRd S l β → RwClsAt S l (snShG S l) X0 0 β

/-- **The level closure statement.** -/
def SnClsLev (S : InaccSeq.{0}) (l E : Ordinal.{0}) : Prop :=
  ∀ b X0 Xh0, SnClsOff S l b X0 Xh0 E → SnCL S E b X0 →
    ∀ β, b ≤ β → RoBaseE S l (X0 + leWe E) 0 β → RwRd S l β → RwClsAt S l (snShG S l) (X0 + leWe E) 0 β

/-- **The level family closure statement.** -/
def SnFamCls (S : InaccSeq.{0}) (l E : Ordinal.{0}) : Prop :=
  ∀ b X0 Xh0, SnClsOff S l b X0 Xh0 (E + 1) → SnCL S E b X0 →
    ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → 1 ≤ ζ → (∃ j, ζ < rvEE S X0 b E j) →
    ∀ β, b ≤ β → RoBaseE S l (X0 + leWe E * ζ) 0 β → RwRd S l β →
      RwClsAt S l (snShG S l) (X0 + leWe E * ζ) 0 β

/-- **Extending an offset by one term.** -/
theorem snG_ext {l b X0 Xh0 E E' ζ : Ordinal.{0}}
    (hoff : (X0 = 0 ∧ Xh0 = 0) ∨ ∃ E0, SnG S l b X0 Xh0 E0 ∧ E ≤ E0) (he' : 1 ≤ E') (he'e : E' < E)
    (hEH : E' ∈ cdHull S l) (hE : E' < veblen 1 (Om (1 + 1) + 1)) (hcl : SnCL S E' b X0)
    (hζ : GxCl (upsilon l) (ldAtR S l) ζ) (hζ0 : ζ ≠ 0) (hj : ∃ j, ζ < rvEE S X0 b E' j) :
    SnG S l b (X0 + leWe E' * ζ) (Xh0 + leOe (sgThH S l E') * gxTh (upsilon l) (ldAtR S l) ζ) E' := by
  rcases hoff with ⟨rfl, rfl⟩ | ⟨E0, hE0, hEE⟩
  · rw [zero_add, zero_add]; exact SnG.one he' hEH hE hcl hζ hζ0 hj
  · exact SnG.add hE0 he' (he'e.trans_le hEE) hEH hE hcl hζ hζ0 hj

theorem snClsOff_mono {l b β X0 Xh0 E : Ordinal.{0}} (hbβ : b ≤ β) (h : SnClsOff S l b X0 Xh0 E) :
    SnClsOff S l β X0 Xh0 E := by
  rcases h with h0 | ⟨E0, hE0, hEE, hcl⟩
  · exact Or.inl h0
  · exact Or.inr ⟨E0, snG_mono hbβ hE0, hEE, fun β' hβ' => hcl β' (hbβ.trans hβ')⟩

theorem snClsOff_le {l b X0 Xh0 E E' : Ordinal.{0}} (hee : E' ≤ E) (h : SnClsOff S l b X0 Xh0 E) :
    SnClsOff S l b X0 Xh0 E' := by
  rcases h with h0 | ⟨E0, hE0, hEE, hcl⟩
  · exact Or.inl h0
  · exact Or.inr ⟨E0, hE0, hee.trans hEE, hcl⟩

theorem snClsOff_fam {l b X0 Xh0 E : Ordinal.{0}} (h : SnClsOff S l b X0 Xh0 E) :
    (X0 = 0 ∧ Xh0 = 0) ∨ ∃ E0, SnG S l b X0 Xh0 E0 ∧ E ≤ E0 := by
  rcases h with h0 | ⟨E0, hE0, hEE, -⟩
  · exact Or.inl h0
  · exact Or.inr ⟨E0, hE0, hEE⟩

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The data of an offset** at level `≥ E`. -/
theorem snOffG_data {b X0 Xh0 E : Ordinal.{0}}
    (h : (X0 = 0 ∧ Xh0 = 0) ∨ ∃ E0, SnG S l b X0 Xh0 E0 ∧ E ≤ E0) :
    leWe E ∣ X0 ∧ X0 < S.psi 0 (Om (1 + 1 + 1)) ∧ Xh0 < S.psi 0 (Om (1 + 1)) ∧
      ∀ β, b ≤ β → RvOff S l β X0 Xh0 := by
  rcases h with ⟨rfl, rfl⟩ | ⟨E0, hE0, hEE⟩
  · exact ⟨dvd_zero _, rwG3_SC.1, rwG_SC.1, fun _ _ => Or.inl ⟨rfl, rfl⟩⟩
  · obtain ⟨-, -, -, hd, -, hX0, hXh0⟩ := snG_data hl hX hE0
    exact ⟨(leWe_dvd hEE).trans hd, hX0, hXh0, fun β hbβ => Or.inr (snG_sh hl hX (snG_mono hbβ hE0))⟩

/-- The bounds of a step over an offset. -/
theorem snOff_bounds {X0 Xh0 E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hE : E < veblen 1 (Om (1 + 1) + 1))
    (hX0 : X0 < S.psi 0 (Om (1 + 1 + 1))) (hXh0 : Xh0 < S.psi 0 (Om (1 + 1))) :
    X0 + leWe (E + 1) + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)) ∧
      Xh0 + leOe (sgThH S l E + 1) + Om 1 < S.psi 0 (Om (1 + 1)) ∧
      X0 + leWe (E + 1) < S.psi 0 (Om (1 + 1 + 1)) ∧
      X0 + leWe E < S.psi 0 (Om (1 + 1 + 1)) := by
  have hG3 := rwG3_SC (S := S)
  have hWG3 := rwW_lt_G3 (S := S)
  have hG1 := rwG_SC (S := S)
  have hΩG1 := rwO_lt_G (S := S)
  have t2 := snWe_lt_G3 (S := S) hE
  have t4 := snOe_lt_G hl hX hEH hE
  have t5 : leWe E < S.psi 0 (Om (1 + 1 + 1)) := (leWe_mono le_self_add).trans_lt t2
  exact ⟨hG3.isPrincipal (hG3.isPrincipal hX0 t2) hWG3, hG1.isPrincipal (hG1.isPrincipal hXh0 t4) hΩG1,
    hG3.isPrincipal hX0 t2, hG3.isPrincipal hX0 t5⟩

/-- **`SnClsLev E ⇒ SnFamCls E`.** -/
theorem snFamCls_of {E : Ordinal.{0}} (he1 : 1 ≤ E) (hEH : E ∈ cdHull S l) (hE : E < veblen 1 (Om (1 + 1) + 1))
    (hL : SnClsLev S l E) : SnFamCls S l E := by
  have hSh := snShG_sh (S := S) hl hX
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
      exact hL b X0 Xh0 (snClsOff_le le_self_add hoff) hEX β hbβ hb hrd
    · have hζ0c := rqCode_pred hl hX hζ hζW
      have hT0 : ∃ j, ζ0 < rvEE S X0 b E j := by
        obtain ⟨j, hj⟩ := hζT; exact ⟨j, (lt_add_one ζ0).trans hj⟩
      have hF0 := snG_ext (snClsOff_fam hoff) he1 (lt_add_one E) hEH hE hEX hζ0c h00 hT0
      have hoff' : SnClsOff S l b (X0 + leWe E * ζ0)
          (Xh0 + leOe (sgThH S l E) * gxTh (upsilon l) (ldAtR S l) ζ0) E :=
        Or.inr ⟨E, hF0, le_rfl, fun β' hβ' hb' hrd' =>
          IHz ζ0 (lt_add_one ζ0) hζ0c (Order.one_le_iff_ne_zero.2 h00) hT0 β' hβ' hb' hrd'⟩
      have hEX' : SnCL S E b (X0 + leWe E * ζ0) := snCL_mono hEX le_rfl le_self_add
      have e1 : X0 + leWe E * (ζ0 + 1) = X0 + leWe E * ζ0 + leWe E := by rw [mul_add_one, add_assoc]
      rw [e1] at hb ⊢
      exact hL b _ _ hoff' hEX' β hbβ hb hrd
  · have hζ0 : ζ ≠ 0 := hlim.ne_bot
    refine rwClsLimSh hl hX hSh (fun x hxH hx => ?_) hb hrd
    rcases lt_or_ge x X0 with hxX | hxX
    · rcases hoff with ⟨rfl, -⟩ | ⟨E0, hE0, hEE, hcl⟩
      · exact absurd hxX (not_lt.2 zero_le)
      refine ⟨X0, Xh0, ⟨E0, snG_mono hbβ hE0⟩, ?_, hxX, fun hb' hrd' => hcl β hbβ hb' hrd'⟩
      exact (add_le_add_iff_left X0).2 (hWe.trans (le_mul_left _ (pos_iff_ne_zero.2 hζ0)))
    · obtain ⟨r, rfl⟩ := exists_add_of_le hxX
      have hr : r < leWe E * ζ := (add_lt_add_iff_left X0).1 hx
      have hrW : r < leWe (E + 1) := hr.trans (rvWe_lt_succ hζW)
      obtain ⟨hd, -, -, -⟩ := snOffG_data hl hX (snClsOff_fam hoff)
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
      have hF := snG_ext (snClsOff_fam (snClsOff_mono hbβ hoff)) he1 (lt_add_one E) hEH hE
        (snCL_mono hEX hbβ le_rfl) hq1c (by simp) hTqβ
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
theorem snClsLev_one : SnClsLev S l 1 := by
  have hSh := snShG_sh (S := S) hl hX
  have hShM : ∀ b b' X Xh, b ≤ b' → snShG S l b X Xh → snShG S l b' X Xh :=
    fun _ _ _ _ h hx => snShG_mono h hx
  intro b X0 Xh0 hoff _ β hbβ hb hrd
  rw [leWe_one] at hb ⊢
  rcases hoff with ⟨rfl, rfl⟩ | ⟨E0, hE0, -, hcl⟩
  · rw [zero_add] at hb ⊢
    have hb1 : RoBaseE S l (Om (1 + 1) * ((1 : ℕ) : Ordinal.{0})) 0 β := by rwa [Nat.cast_one, mul_one]
    have h := rwCls_one (Sh := snShG S l) hl hX hb1
    rwa [Nat.cast_one, mul_one] at h
  · have hsh : snShG S l b X0 Xh0 := ⟨E0, hE0⟩
    exact rwClsW hl hX hSh hShM hsh (rwClsE hl hX hSh hShM hsh hcl) β hbβ hb hrd

/-- **`SnFamCls E₀ ⇒ SnClsLev (E₀+1)`.** -/
theorem snClsLev_succ {E0 : Ordinal.{0}} (he1 : 1 ≤ E0) (hE0H : E0 ∈ cdHull S l)
    (hE1 : E0 + 1 < veblen 1 (Om (1 + 1) + 1)) (hF : SnFamCls S l E0) : SnClsLev S l (E0 + 1) := by
  have hE0 : E0 < veblen 1 (Om (1 + 1) + 1) := (lt_add_one E0).trans hE1
  intro b X0 Xh0 hoff hcl β hbβ hb hrd t ht htT
  obtain ⟨Â, hÂ, hbase⟩ := hrd
  have hb' := hb
  obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hb
  rw [add_zero] at hβd hβA hβown htT
  obtain ⟨hd, hX0G, hXh0G, hoffR⟩ := snOffG_data hl hX (snClsOff_fam hoff)
  have hoffβ := hoffR β hbβ
  obtain ⟨hG3, hG, hX0G3, -⟩ := snOff_bounds hl hX hE0H hE0 hX0G hXh0G
  obtain ⟨-, -, hX0m, -, hX0cl, -⟩ := rvOff_data hoffβ
  -- the closure condition of `E₀` at `β`, by the collapse lemma
  have hclβ : SnCL S (E0 + 1) β X0 := snCL_mono hcl hbβ le_rfl
  have hTSC : SC (S.psi (β + leWe (X0 + leWe E0)) (Om (1 + 1))) := SC_psi (InR_Om_succ 1) _
  have hE0T : LeCl (Om (1 + 1)) (S.psi (β + leWe (X0 + leWe E0)) (Om (1 + 1))) E0 := by
    obtain ⟨z, hz1, hz2, hz⟩ := sjCode (S := S) hβd hβown hX0cl hX0G3 hclβ (y := E0) le_self_add
    rcases hz2.lt_or_eq with hlt | rfl
    · have : z = E0 := le_antisymm (Order.lt_add_one_iff.1 hlt) hz1
      rwa [this] at hz
    · exact snPred hTSC ldOm2_SC E0 hz
  have hclE0 : SnCL S E0 β X0 := fun Q hQ hQ' => snLeCl_mono hE0T hQ'
  have hem : E0 ∈ S.CSet 0 (S.psi (β + leWe (X0 + leWe E0)) (Om (1 + 1))) := sjCl_mem hE0T
  obtain ⟨j, hj⟩ := scEE_sup hβown hX0m hem hclE0 hβd hX0cl hX0G3 htT
  rcases j with _ | i
  · exact Or.inl (hj.trans (psiS_bounds (S := S) β 1).1).le
  obtain ⟨hic, -⟩ := scEE_code hl hX (snOwP hl hX hE0H he1 hE0) (snLev hl hX hE0H he1 hE0) hoffβ hd hG3 hG
    hclE0 hb' hÂ hbase i
  have hiW : rvEE S X0 β E0 i < Om (1 + 1) := rvEE_lt_Om2 i
  have hi0 : rvEE S X0 β E0 i ≠ 0 := (rvEE_SC i).1.ne'
  have hiT : ∃ j, rvEE S X0 β E0 i < rvEE S X0 β E0 j := ⟨i + 1, scEE_lt_succ hβown hX0m hem i⟩
  have hoff1 := snClsOff_mono hbβ hoff
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

/-- **Limit exponents**: the normal form of an atom below `T_{X₀ + W^E}(β)` gives an own level `c + 1 < E`. -/
theorem snClsLev_lim {E : Ordinal.{0}} (hlim : IsSuccLimit E) (hEH : E ∈ cdHull S l)
    (hE : E < veblen 1 (Om (1 + 1) + 1))
    (IH : ∀ c, c ∈ cdHull S l → 1 ≤ c → c < E → SnClsLev S l c) : SnClsLev S l E := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have he1 : 1 ≤ E := (rvLim_one_lt hlim).le
  intro b X0 Xh0 hoff hcl β hbβ hb hrd t ht htT
  have hb' := hb
  obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hb
  rw [add_zero] at hβd hβA hβown htT
  obtain ⟨hdX0, hX0G, hXh0G, hoffR⟩ := snOffG_data hl hX (snClsOff_fam hoff)
  have hoffβ := hoffR β hbβ
  obtain ⟨-, -, -, hX0G3⟩ := snOff_bounds hl hX hEH hE hX0G hXh0G
  obtain ⟨-, -, -, -, hX0cl, -⟩ := rvOff_data hoffβ
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
  -- the closure condition of `c + 1`, from the normal form
  have hcl1 : SnCL S (c + 1) β X0 := by
    intro Q hQ hQ'
    have htQ := htc.le.trans hQ'
    have hd'Q := snExtrRem hnf hβd hd'W hX0G3 hQ htQ
    have hYQ : LeCl (Om (1 + 1)) Q Y := by rw [hY_def]; exact snLogW hQ hd'Q
    have hX0Q : LeCl (Om (1 + 1)) Q X0 :=
      hX0cl Q hQ (((psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
        (leWe_mono le_self_add))).1).trans hQ')
    have hrQ : LeCl (Om (1 + 1)) Q r := by
      have h := (leClDec hQ ldOm2_SC Y hYQ).1 X0 hX0Q hXY
      rwa [hr, Ordinal.add_sub_cancel] at h
    rw [hc_def]; exact LeCl.add (snLogW hQ hrQ) (LeCl.small (gg_one_lt_of_SC hQ))
  -- the hull
  have hd'H : d' ∈ cdHull S l := snHullRem hdH hβd hd'W
  have hYH : Y ∈ cdHull S l := by rw [hY_def]; exact ldDivK_mem ldOm2_SC (leLog_mem hd'H)
  have hrH : r ∈ cdHull S l := by
    have h := snHullRem (A := ConjT.Aη S (cdEta S l)) (ρ := upsilon l) (β := X0) (d' := r) (K := E)
      (by rw [← hr]; exact hYH) hdX0 hrE
    exact h
  have hcH : c + 1 ∈ cdHull S l := by
    rw [hc_def]; exact CSet.succ_mem (ldDivK_mem ldOm2_SC (leLog_mem hrH))
  have hc1ε : c + 1 < veblen 1 (Om (1 + 1) + 1) := hc1.trans hE
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
  rcases IH (c + 1) hcH le_add_self hc1 β X0 Xh0 (snClsOff_le hc1.le (snClsOff_mono hbβ hoff)) hcl1 β le_rfl
    hbc hrd _ ht htT' with h | ⟨X', e', c', v, hcond, hown, hbo, e1⟩
  · exact Or.inl h
  · refine Or.inr ⟨X', e', c', v, Or.inr ?_, hown, hbo, e1⟩
    rcases hcond with ⟨rfl, h2⟩ | ⟨h1, h2⟩
    · exact ⟨hle, (h2.trans zero_le.ge).trans_lt ((Om_pos one_ne_zero).trans (leOm1_lt_Te _ _))⟩
    · exact ⟨h1.trans (le_self_add.trans hle), h2⟩

/-- **`SnClsLev E` for every `1 ≤ E < ε_{Ω₂+1}` in the hull.** -/
theorem snClsLev_all : ∀ E, E ∈ cdHull S l → 1 ≤ E → E < veblen 1 (Om (1 + 1) + 1) → SnClsLev S l E := by
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
    · rw [zero_add]; exact snClsLev_one hl hX
    · have h10 : 1 ≤ E0 := Order.one_le_iff_ne_zero.2 h00
      have hE0 : E0 < veblen 1 (Om (1 + 1) + 1) := (lt_add_one E0).trans hE
      exact snClsLev_succ hl hX h10 hE0H hE
        (snFamCls_of hl hX h10 hE0H hE0 (IH E0 (lt_add_one E0) hE0H h10 hE0))
  · exact snClsLev_lim hl hX hlim hEH hE (fun c hcH h1 hcE => IH c hcE hcH h1 (hcE.trans hE))

/-- **Every atom `s < ψ_{Ω₂}(ε_{Ω₂+1})` is `≤ ψ_{Ω₂}(0)` or `ψ_{Ω₂}(c)` with `c` own over `0`** (family `snShG`). -/
theorem snRepG {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    (s : Ordinal.{0}) (hs : s ∈ ldAtR S l) (hsε : s < S.psi (veblen 1 (Om (1 + 1) + 1)) (Om (1 + 1))) :
    s ≤ S.psi 0 (Om (1 + 1)) ∨ ∃ X e c v, (X = 0 ∨ ∃ Xh, snShG S l 0 X Xh) ∧
      RwOwn S l (snShG S l) X e 0 c v ∧ RoBaseE S l X e 0 ∧ s = S.psi c (Om (1 + 1)) := by
  obtain ⟨-, hρ1⟩ := leRho hl hX
  have hG3 := rwG3_SC (S := S)
  obtain ⟨d, rfl, hnf, hdH, -⟩ := snNf hs hρ1.le
  have hdε : d < veblen 1 (Om (1 + 1) + 1) := by
    by_contra h
    push Not at h
    exact absurd hsε (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) h).1)
  rcases eq_or_ne d 0 with rfl | hd0
  · exact Or.inl le_rfl
  set Y := log ω d / Om (1 + 1) with hY_def
  have hYd : Y ≤ d := (Ordinal.div_le_of_le_mul (Ordinal.le_mul_right _ ldOm2_SC.1)).trans (log_le_self ω d)
  set E := log ω Y / Om (1 + 1) + 1 with hE_def
  have hEY : log ω Y / Om (1 + 1) ≤ Y :=
    (Ordinal.div_le_of_le_mul (Ordinal.le_mul_right _ ldOm2_SC.1)).trans (log_le_self ω Y)
  have hE : E < veblen 1 (Om (1 + 1) + 1) := snEps_succ_lt (hEY.trans_lt (hYd.trans_lt hdε))
  have he1 : 1 ≤ E := le_add_self
  have hdW : d < leWe (leWe E) := by
    refine (roLt_We_log d).trans_le (leWe_mono ?_)
    exact Order.add_one_le_of_lt (roLt_We_log Y)
  have hst : S.psi d (Om (1 + 1)) < S.psi (0 + leWe (0 + leWe E)) (Om (1 + 1)) := by
    rw [zero_add, zero_add]; exact psi_lt_psi (InR_Om_succ 1) hdW hnf
  have hcl : SnCL S E 0 0 := by
    intro Q hQ hQ'
    have htQ := hst.le.trans hQ'
    have hdQ : LeCl (Om (1 + 1)) Q d :=
      snLeCl_mem hQ htQ (CSet_mono le_rfl htQ hnf) (hdε.trans snEps_lt_G3)
    exact LeCl.add (snLogW hQ (snLogW hQ hdQ)) (LeCl.small (gg_one_lt_of_SC hQ))
  have hEH : E ∈ cdHull S l :=
    CSet.succ_mem (ldDivK_mem ldOm2_SC (leLog_mem (ldDivK_mem ldOm2_SC (leLog_mem hdH))))
  have hEW : E < Om ω := hE.trans sjEps_lt_OmW
  have hb : RoBaseE S l (0 + leWe E) 0 0 := by
    refine ⟨dvd_zero _, CSet.zero_mem _ _, ?_, fun d _ => CSet.zero_mem _ _, fun e' _ h' => ?_⟩
    · rw [zero_add, add_zero, zero_add]
      exact (roWe_lt_OmW (roWe_lt_OmW hEW)).trans_le le_self_add
    · obtain rfl : e' = 0 := le_antisymm h' zero_le
      exact (SC_psi (InR_Om_succ 1) _).1
  have hcls := snClsLev_all hl hX E hEH he1 hE 0 0 0 (Or.inl ⟨rfl, rfl⟩) hcl 0 le_rfl hb
    (rwRd_zero (S := S) (l := l) hA hρ)
  have htT : S.psi d (Om (1 + 1)) < leTe S (0 + leWe E + 0) 0 := by rw [add_zero]; exact hst
  rcases hcls _ hs htT with h | ⟨X', e', c, v, -, hown, hbo, e1⟩
  · exact Or.inl h
  · rw [zero_add] at e1
    exact Or.inr ⟨X', e', c, v, rwOwn_sh hown, hown, hbo, e1⟩

end Main

end Googology.Trans.PoR.InaccPsi.R2.Sn

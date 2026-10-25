import Googology.Trans.PoR.InaccPsi.R2.UmGamL

/-!
# Prefixes past `Γ₂` with the bound `Y₃`: level-2 codes, the image condition in level-1 codes

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β, X₀) = ψ_{Ω₂}(β + W^{X₀ + W^E})`,
`C_k(Q) = Ug.UgC S k Q` (codes of level `k` with `ψ_{Ω_{k+1}}`-atoms), `CL₃ E = Ug.UgCL S E` (the closure condition
with `ψ₃`-atoms), `T = Ug.ugTh` (the image past `Γ₂`), `Γ₂ = ψ_{Ω₃}(0)`, `Y₃ = ψ_{Ω₃}(Ω₃)`, `Y₂ = ψ_{Ω₂}(Ω₂)`.

**The image condition** `UqImg S λ P P̂`: whenever `P ∈ C_2(Q)` for every strongly critical `Q ≥ T`, `P̂ ∈ C_1(Q)`
for every strongly critical `Q ≥ Θ T`.  **A prefix past `Γ₂` with the bound `Y₃`** `UqPD S λ P P̂`: `Ω₂ ∣ P`,
`P` in the hull, `1 ≤ P < Y₃`, the image condition and the level statement past `Γ₂` `Uj.UjLev (CL₃ P) P P̂`.
No bound `P < Γ₂`, `P̂ < ψ_{Ω₂}(0)` and no `Sc` level statement is asked (compare `St.StPD`, `Um.UmPD`).

* `uqCl2_mem`, `uqCl1_mem` (**a code `x ≤ a` over `Q` lies in `Cl(a, Q)`**), `uqC_mem` (**every member of `Cl(a, Q)`
  below `Y₃` is a level-2 code over every strongly critical `Q ≥ ψ_{Ω₂}(a)`**), `uqC_pred` (`x + 1` a code gives
  `x` a code), `uqHead`, `uqHeadW` (a code `P + c`, `c < Ω₂`, or `P + Ω₂` with `Ω₂ ∣ P` gives the code `P`);
* `UqImg`, `UqPD`, `uqTh_SC`, `uqOwP_img` (**the image condition gives the own data** `Uj.UjOwP (CL₃ P) P P̂`),
  `uqImg_add`, `uqImg_W`, `uqImg_ugTh` (**`P̂ = T P` satisfies the image condition**, from `Ug.ugOwn`).

No new axiom.  New definitions: `UqImg`, `UqPD`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Uq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rq
  Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw Googology.Trans.PoR.InaccPsi.R2.Sc
  Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj Googology.Trans.PoR.InaccPsi.R2.Sn
  Googology.Trans.PoR.InaccPsi.R2.Sq Googology.Trans.PoR.InaccPsi.R2.St Googology.Trans.PoR.InaccPsi.R2.Ua
  Googology.Trans.PoR.InaccPsi.R2.Ud Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj
  Googology.Trans.PoR.InaccPsi.R2.Um

variable {S : InaccSeq.{0}}

/-- **A level-2 code `x ≤ a` over `Q` lies in `Cl(a, Q)`.** -/
theorem uqCl2_mem {Q a x : Ordinal.{0}} (hx : UgC S (1 + 1) Q x) : x ≤ a → x ∈ S.CSet a Q := by
  induction hx with
  | small h => exact fun _ => CSet.of_lt h
  | om => exact fun _ => mxOm2_mem _ _
  | @add x y _ _ ihx ihy =>
    exact fun h => CSet.add_mem (ihx (le_self_add.trans h)) (ihy (le_add_self.trans h))
  | @phi x y _ _ ihx ihy =>
    exact fun h => CSet.phi_mem (ihx ((left_le_veblen x y).trans h)) (ihy ((right_le_veblen x y).trans h))
  | @psi d _ hdl ihd =>
    intro h
    have hda : d < a := hdl.trans_le h
    exact CSet.psi_mem hda (InR_Om_succ (1 + 1))
      (CSet.Om_mem (CSet.succ_mem (CSet.succ_mem (CSet.one_mem _ _)))) (ihd hda.le)

/-- **A level-1 code `x ≤ a` over `Q` lies in `Cl(a, Q)`.** -/
theorem uqCl1_mem {Q a x : Ordinal.{0}} (hx : UgC S 1 Q x) : x ≤ a → x ∈ S.CSet a Q := by
  induction hx with
  | small h => exact fun _ => CSet.of_lt h
  | om => exact fun _ => CSet.Om_mem (CSet.one_mem _ _)
  | @add x y _ _ ihx ihy =>
    exact fun h => CSet.add_mem (ihx (le_self_add.trans h)) (ihy (le_add_self.trans h))
  | @phi x y _ _ ihx ihy =>
    exact fun h => CSet.phi_mem (ihx ((left_le_veblen x y).trans h)) (ihy ((right_le_veblen x y).trans h))
  | @psi d _ hdl ihd =>
    intro h
    have hda : d < a := hdl.trans_le h
    exact CSet.psi_mem hda (InR_Om_succ 1) (mxOm2_mem _ _) (ihd hda.le)

/-- **Every member of `Cl(a, Q)` below `Y₃` is a level-2 code over every strongly critical `Q ≥ ψ_{Ω₂}(a)`.** -/
theorem uqC_mem {a Q x : Ordinal.{0}} (hQ : SC Q) (haQ : S.psi a (Om (1 + 1)) ≤ Q)
    (hx : x ∈ S.CSet a Q) (hxY : x < ugY S) : UgC S (1 + 1) Q x := by
  have hΩQ : Om 1 < Q := (psiS_bounds (S := S) a 1).1.trans_le haQ
  have h := umKeyC (S := S) (s := 1) hQ hΩQ (fun a b => CSet.one_mem a b) leOm3_lt_I (snColl haQ) x hx
  rwa [ujY_one, Ordinal.mod_eq_of_lt hxY] at h

/-- **A code `x + 1` gives the code `x`** (every level `k ≠ 0`). -/
theorem uqC_pred {k Q : Ordinal.{0}} (hQ : SC Q) (hk : k ≠ 0) : ∀ x, UgC S k Q (x + 1) → UgC S k Q x := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx
  rcases eq_or_ne x 0 with rfl | hx0
  · exact UgC.zero hQ.1
  have hlog : log ω (x + 1) = log ω x := by
    have h1 : (1 : Ordinal.{0}) < ω ^ log ω x * ω := by
      have := opow_pos (log ω x) omega0_pos
      calc (1 : Ordinal.{0}) < ω := one_lt_omega0
        _ ≤ ω ^ log ω x * ω := Ordinal.le_mul_right _ this
    refine le_antisymm ?_ (log_mono_right _ le_self_add)
    have hlt : x + 1 < ω ^ (log ω x + 1) := by
      rw [opow_add, opow_one]
      have hx1 : x < ω ^ log ω x * ω := by
        rw [← opow_succ]; exact lt_opow_succ_log_self one_lt_omega0 x
      have hpr : IsPrincipal (· + ·) (ω ^ log ω x * ω) := by
        rw [← opow_succ]; exact isPrincipal_add_omega0_opow _
      exact hpr hx1 h1
    exact Order.lt_add_one_iff.1 ((lt_opow_iff_log_lt one_lt_omega0 (by simp)).1 hlt)
  obtain ⟨hsub, hl1⟩ := ugCDec hQ hk (x + 1) hx
  have hlead : ω ^ log ω x ≤ x := opow_log_le_self ω hx0
  have hlc : UgC S k Q (ω ^ log ω x) := by rw [← hlog]; exact UgC.opow hQ.1 hl1
  have hr := hsub _ hlc (hlead.trans le_self_add)
  have e : x + 1 - ω ^ log ω x = x - ω ^ log ω x + 1 := by
    refine Ordinal.sub_eq_of_add_eq ?_
    rw [← add_assoc, Ordinal.add_sub_cancel_of_le hlead]
  rw [e] at hr
  have h2 := IH _ (leRest_lt hx0) hr
  have e2 : ω ^ log ω x + (x - ω ^ log ω x) = x := Ordinal.add_sub_cancel_of_le hlead
  rw [← e2]; exact UgC.add hlc h2

/-- **A level-2 code `P + c`** (`Ω₂ ∣ P`, `c < Ω₂`) **gives the code `P`, the code `c` and `c < Q`.** -/
theorem uqHead {Q P c : Ordinal.{0}} (hQ : SC Q) (hd : Om (1 + 1) ∣ P) (hc : c < Om (1 + 1))
    (h : UgC S (1 + 1) Q (P + c)) : UgC S (1 + 1) Q P ∧ UgC S (1 + 1) Q c ∧ c < Q := by
  have hk := ugTwo_ne
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  obtain ⟨q, rfl⟩ := hd
  have e1 : (Om (1 + 1) * q + c) / Om (1 + 1) = q := by
    rw [Ordinal.mul_add_div _ hW0, Ordinal.div_eq_zero_of_lt hc, add_zero]
  have h1 := ugC_div hQ hk _ h
  rw [e1] at h1
  have h2 := ugC_mod hQ hk (Om (1 + 1)) h
  rw [stW_opow, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hc] at h2
  exact ⟨ugC_mulK hQ hk _ h1, h2, ugC_lt_om hQ h2 hc⟩

/-- **A level-2 code `P + Ω₂`** (`Ω₂ ∣ P`) **gives the code `P`.** -/
theorem uqHeadW {Q P : Ordinal.{0}} (hQ : SC Q) (hd : Om (1 + 1) ∣ P)
    (h : UgC S (1 + 1) Q (P + Om (1 + 1))) : UgC S (1 + 1) Q P := by
  have hk := ugTwo_ne
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  obtain ⟨q, rfl⟩ := hd
  have e1 : (Om (1 + 1) * q + Om (1 + 1)) / Om (1 + 1) = q + 1 := by
    rw [Ordinal.mul_add_div _ hW0, Ordinal.div_self hW0]
  have h1 := ugC_div hQ hk _ h
  rw [e1] at h1
  exact ugC_mulK hQ hk _ (uqC_pred hQ hk q h1)

/-- **The image condition past `Γ₂`** of a level `P` with the image `P̂`, in the level codes. -/
def UqImg (S : InaccSeq.{0}) (l P Ph : Ordinal.{0}) : Prop :=
  ∀ T, SC T → (∀ Q, SC Q → T ≤ Q → UgC S (1 + 1) Q P) →
    ∀ Q, SC Q → gxTh (upsilon l) (ldAtR S l) T ≤ Q → UgC S 1 Q Ph

/-- **A prefix past `Γ₂` with the bound `Y₃`**: a level `P` divisible by `Ω₂`, `1 ≤ P < Y₃`, in the hull, with the
image condition and the level statement past `Γ₂`. -/
structure UqPD (S : InaccSeq.{0}) (l P Ph : Ordinal.{0}) : Prop where
  dvd : Om (1 + 1) ∣ P
  hull : P ∈ cdHull S l
  one : 1 ≤ P
  ltY : P < ugY S
  img : UqImg S l P Ph
  lev : UjLev S l (UgCL S P) P Ph

/-- The image condition of `P + c`, `c < Ω₂` a code. -/
theorem uqImg_add {l P Ph c : Ordinal.{0}} (himg : UqImg S l P Ph) (hd : Om (1 + 1) ∣ P)
    (hc : GxCl (upsilon l) (ldAtR S l) c) (hcW : c < Om (1 + 1)) :
    UqImg S l (P + c) (Ph + gxTh (upsilon l) (ldAtR S l) c) := by
  intro T hT hcl Q hQ hΘQ
  have hP : ∀ Q, SC Q → T ≤ Q → UgC S (1 + 1) Q P := fun Q hQ hTQ => (uqHead hQ hd hcW (hcl Q hQ hTQ)).1
  have hcT : c < T := (uqHead hT hd hcW (hcl T hT le_rfl)).2.2
  have hΘ := gxTh_lt (Z := upsilon l) (At := ldAtR S l) hc hcT
  exact UgC.add (himg T hT hP Q hQ hΘQ) (UgC.small (hΘ.trans_le hΘQ))

/-- The image condition of `P + Ω₂` with the image `P̂ + Ω₁`. -/
theorem uqImg_W {l P Ph : Ordinal.{0}} (himg : UqImg S l P Ph) (hd : Om (1 + 1) ∣ P) :
    UqImg S l (P + Om (1 + 1)) (Ph + Om 1) :=
  fun T hT hcl Q hQ hΘQ => UgC.add (himg T hT (fun Q hQ hTQ => uqHeadW hQ hd (hcl Q hQ hTQ)) Q hQ hΘQ) UgC.om

/-- `Y₃` is strongly critical, `Ω₂ < Y₃`. -/
theorem uqY_SC : SC (ugY S) := ujY_SC (S := S) 1

theorem uqW_lt_Y : Om (1 + 1 : Ordinal.{0}) < ugY S := ujY_gt (S := S) 1

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **`Θ T` is strongly critical** for every strongly critical `T > Ω₁`. -/
theorem uqTh_SC {T : Ordinal.{0}} (hT : SC T) (h1 : Om 1 < T) : SC (gxTh (upsilon l) (ldAtR S l) T) := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  exact gxTh_SC hρSC (ldAt_GxAt _ _) hT (hρ1.trans h1)

/-- **The image condition gives the own data** past `Γ₂`. -/
theorem uqOwP_img {P Ph : Ordinal.{0}} (himg : UqImg S l P Ph) (hPH : P ∈ cdHull S l) (hP1 : 1 ≤ P) :
    UjOwP S l (UgCL S P) P Ph := by
  refine ⟨fun b X0 hcl => ?_, fun _ _ _ _ h hb hX0 => ugCL_mono h hb hX0⟩
  have hT : SC (S.psi (b + leWe (X0 + leWe P)) (Om (1 + 1))) := SC_psi (InR_Om_succ 1) _
  have hT1 : Om 1 < S.psi (b + leWe (X0 + leWe P)) (Om (1 + 1)) := (psiS_bounds (S := S) _ 1).1
  have hΘ := uqTh_SC hl hX hT hT1
  have h2 := himg _ hT hcl
  exact ⟨hP1, hPH, uqCl2_mem (hcl _ hT le_rfl) le_rfl, uqCl1_mem (h2 _ hΘ le_rfl) le_rfl, hcl, h2⟩

/-- **`P̂ = T P` satisfies the image condition** (`Ug.ugOwn`). -/
theorem uqImg_ugTh {P : Ordinal.{0}} (hPH : P ∈ cdHull S l) (hPY : P < ugY S) : UqImg S l P (ugTh S l P) :=
  fun T hT hcl => ugOwn hl hX P hPH hPY T hT hcl

/-- The own data of `P + c` over a prefix past `Γ₂`. -/
theorem uqPreOwP {P Ph c : Ordinal.{0}} (hD : UqPD S l P Ph) (hc : GxCl (upsilon l) (ldAtR S l) c)
    (hcW : c < Om (1 + 1)) :
    UjOwP S l (UgCL S (P + c)) (P + c) (Ph + gxTh (upsilon l) (ldAtR S l) c) :=
  uqOwP_img hl hX (uqImg_add hD.img hD.dvd hc hcW) (CSet.add_mem hD.hull ((ldHull_iff hl hX hcW).2 hc))
    (hD.one.trans le_self_add)

end Main

end Googology.Trans.PoR.InaccPsi.R2.Uq

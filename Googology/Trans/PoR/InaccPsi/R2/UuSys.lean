import Googology.Trans.PoR.InaccPsi.R2.UuCls

/-!
# A level system with the bound `Y₃`, its base-indexed family of shifts, and the system of all levels below `Y₃`

`Θ = gxTh ρ_λ (ldAtR λ)`, `T = Ug.ugTh`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `EE_j(X₀, β, E) = Rv.rvEE S X₀ β E j`,
`EX_j = Rw.rwEX`, `CL₃ = Ug.UgCL`, `Y₂ = ψ₂(Ω₂)`, `Y₃ = ψ₃(Ω₃)`.

**A level system past `Γ₂`** `UuLS S λ E_b Th Ow` (in place of `St.StLS`, whose bound is `E_b < ψ₃(0)`): `E_b ≤ Y₃` a
limit, and every level `1 ≤ E < E_b` of the hull has `Th λ E < Y₂`, the own data `Uj.UjOwP (Ow E) E (Th λ E)` and
the level statement `Uj.UjLev (Ow E) E (Th λ E)`; the own predicate `Ow E` may depend on the level and gives
`CL₃ E`.  `UuG` (the family over the base `β`, as `St.StG` with `Ow E` in place of `Sn.SnCL`).

* `uuOw` (**the own predicate of the levels below `Y₃`**: `∃ j, E < EX_j(X₀, b)` at a code `E < Ω₂`
  (`Uj.ujLev_code`), `CL₃ E` at `E ≥ Ω₂` (`Uu.uuLevY`)), `uuOw_cl` (it gives `CL₃ E`);
* `uuLSY` (**`UuLS S λ Y₃ T uuOw`: THE LEVEL SYSTEM OF ALL LEVELS `1 ≤ E < Y₃` OF THE HULL**, from
  `Uj.ujOwP_code`, `Uj.ujLev_code`, `Uu.uuLevY`, `Uu.uuTh_lt_Y2`);
* `uuG_data`, `uuG_mono`, `uuG_sh` (**every member is a shift past `Γ₂` (`Uj.UjSh`) with the top law at the bases
  `≥ β`**, from `Uj.ujFam`), `uuShG_sh` (**the family meets the hypotheses of the own-atom layer**
  `Uu.uuOwnRead`, `Uu.uuDigMove`, `Uu.uuClsE`).

No new axiom.  New definitions (auxiliary): `UuLS`, `UuG`, `uuShG`, `uuOw`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Uu

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj
  Googology.Trans.PoR.InaccPsi.R2.Uq

variable {S : InaccSeq.{0}}

/-- **A level system past `Γ₂`** (bound `E_b ≤ Y₃`, images below `Y₂`, own predicates `Ow E` giving `CL₃ E`). -/
structure UuLS (S : InaccSeq.{0}) (l Eb : Ordinal.{0}) (Th : Ordinal.{0} → Ordinal.{0} → Ordinal.{0})
    (Ow : Ordinal.{0} → Ordinal.{0} → Ordinal.{0} → Prop) : Prop where
  lim : IsSuccLimit Eb
  leY : Eb ≤ ugY S
  ltY : ∀ E, E ∈ cdHull S l → 1 ≤ E → E < Eb → Th l E < ujY S 0
  own : ∀ E, E ∈ cdHull S l → 1 ≤ E → E < Eb → UjOwP S l (Ow E) E (Th l E)
  lev : ∀ E, E ∈ cdHull S l → 1 ≤ E → E < Eb → UjLev S l (Ow E) E (Th l E)
  cl : ∀ E b X0, Ow E b X0 → UgCL S E b X0

/-- **The family of the shifts of a level system past `Γ₂` over the base `β`** (last level `E`). -/
inductive UuG (S : InaccSeq.{0}) (l Eb : Ordinal.{0}) (Th : Ordinal.{0} → Ordinal.{0} → Ordinal.{0})
    (Ow : Ordinal.{0} → Ordinal.{0} → Ordinal.{0} → Prop) :
    Ordinal.{0} → Ordinal.{0} → Ordinal.{0} → Ordinal.{0} → Prop
  | one {β E ζ : Ordinal.{0}} : 1 ≤ E → E ∈ cdHull S l → E < Eb → Ow E β 0 →
      GxCl (upsilon l) (ldAtR S l) ζ → ζ ≠ 0 → (∃ j, ζ < rvEE S 0 β E j) →
      UuG S l Eb Th Ow β (leWe E * ζ) (leOe (Th l E) * gxTh (upsilon l) (ldAtR S l) ζ) E
  | add {β X0 Xh0 E0 E ζ : Ordinal.{0}} : UuG S l Eb Th Ow β X0 Xh0 E0 → 1 ≤ E → E < E0 → E ∈ cdHull S l →
      E < Eb → Ow E β X0 →
      GxCl (upsilon l) (ldAtR S l) ζ → ζ ≠ 0 → (∃ j, ζ < rvEE S X0 β E j) →
      UuG S l Eb Th Ow β (X0 + leWe E * ζ) (Xh0 + leOe (Th l E) * gxTh (upsilon l) (ldAtR S l) ζ) E

/-- The family `∃ E, UuG β X X̂ E`. -/
def uuShG (S : InaccSeq.{0}) (l Eb : Ordinal.{0}) (Th : Ordinal.{0} → Ordinal.{0} → Ordinal.{0})
    (Ow : Ordinal.{0} → Ordinal.{0} → Ordinal.{0} → Prop) (b X Xh : Ordinal.{0}) : Prop :=
  ∃ E, UuG S l Eb Th Ow b X Xh E

/-- **The own predicate of the levels below `Y₃`**: `∃ j, E < EX_j(X₀, b)` at a code level `E < Ω₂`, `CL₃ E` at a
level `E ≥ Ω₂`. -/
def uuOw (S : InaccSeq.{0}) (E b X0 : Ordinal.{0}) : Prop :=
  (E < Om (1 + 1) ∧ ∃ j, E < rwEX S X0 b j) ∨ (Om (1 + 1) ≤ E ∧ UgCL S E b X0)

theorem uuOw_code {E : Ordinal.{0}} (hE : E < Om (1 + 1)) :
    uuOw S E = fun b X0 => ∃ j, E < rwEX S X0 b j := by
  funext b X0
  apply propext
  exact ⟨fun h => h.elim (fun h => h.2) (fun h => absurd h.1 (not_le.2 hE)), fun h => Or.inl ⟨hE, h⟩⟩

theorem uuOw_hi {E : Ordinal.{0}} (hE : Om (1 + 1) ≤ E) : uuOw S E = UgCL S E := by
  funext b X0
  apply propext
  exact ⟨fun h => h.elim (fun h => absurd h.1 (not_lt.2 hE)) (fun h => h.2), fun h => Or.inr ⟨hE, h⟩⟩

/-- **The own predicate gives the closure condition `CL₃ E`.** -/
theorem uuOw_cl {E b X0 : Ordinal.{0}} (h : uuOw S E b X0) : UgCL S E b X0 := by
  rcases h with ⟨-, j, hj⟩ | ⟨-, h⟩
  · exact fun Q _ hQ => UgC.small ((rwEX_gt j E hj).trans_le hQ)
  · exact h

theorem uuWe_lt_Y {E : Ordinal.{0}} (hE : E < ugY S) : leWe (E + 1) < ugY S :=
  (leWe_lt_SC uqY_SC uqW_lt_Y (uqY_SC.isSuccLimit.succ_lt hE)).1

theorem uuY2_SC : SC (ujY S 0) := ujY_SC 0

theorem uuOm1_lt_Y2 : Om (1 : Ordinal.{0}) < ujY S 0 := by
  rw [ujY_zero]; exact (psiS_bounds (S := S) _ 1).1

theorem uuOe_lt_Y2 {x : Ordinal.{0}} (hx : x < ujY S 0) : leOe (x + 1) < ujY S 0 :=
  (leOe_lt_SC uuY2_SC uuOm1_lt_Y2 (uuY2_SC.isSuccLimit.succ_lt hx)).1

section Inst

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **THE LEVEL SYSTEM OF ALL LEVELS `1 ≤ E < Y₃` OF THE HULL** (image `T`, own predicates `uuOw`). -/
theorem uuLSY : UuLS S l (ugY S) (ugTh S) (uuOw S) := by
  refine ⟨uqY_SC.isSuccLimit, le_rfl, fun E hEH _ hE => by rw [ujY_zero]; exact uuTh_lt_Y2 hl hX hEH hE, ?_, ?_,
    fun E b X0 h => uuOw_cl h⟩
  · intro E hEH h1 hE
    rcases lt_or_ge E (Om (1 + 1)) with hW | hW
    · rw [uuOw_code hW, uqThCode hl hX hW]
      exact ujOwP_code hl hX h1 ((ldHull_iff hl hX hW).1 hEH) hW
    · rw [uuOw_hi hW]; exact (uuLevY hl hX hEH hW hE).1
  · intro E hEH h1 hE
    rcases lt_or_ge E (Om (1 + 1)) with hW | hW
    · rw [uuOw_code hW, uqThCode hl hX hW]
      exact ujLev_code hl hX E ((ldHull_iff hl hX hW).1 hEH) h1 hW
    · rw [uuOw_hi hW]; exact (uuLevY hl hX hEH hW hE).2

end Inst

section Main

variable {l ηx Eb : Ordinal.{0}} {Th : Ordinal.{0} → Ordinal.{0} → Ordinal.{0}}
  {Ow : Ordinal.{0} → Ordinal.{0} → Ordinal.{0} → Prop}
  (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) (hS : UuLS S l Eb Th Ow)

include hl hX hS

/-- **The data of a member.** -/
theorem uuG_data {β X Xh E : Ordinal.{0}} (h : UuG S l Eb Th Ow β X Xh E) :
    1 ≤ E ∧ E ∈ cdHull S l ∧ E < Eb ∧ leWe E ∣ X ∧ X ≠ 0 ∧ X < ugY S ∧ Xh < ujY S 0 := by
  have hterm : ∀ {E' X0 ζ : Ordinal.{0}}, E' ∈ cdHull S l → 1 ≤ E' → E' < Eb →
      GxCl (upsilon l) (ldAtR S l) ζ → (∃ j, ζ < rvEE S X0 β E' j) →
      leWe E' * ζ < ugY S ∧ leOe (Th l E') * gxTh (upsilon l) (ldAtR S l) ζ < ujY S 0 := by
    intro E' X0 ζ hEH h1 hE _ hj
    obtain ⟨j, hj⟩ := hj
    have hζW : ζ < Om (1 + 1) := hj.trans (rvEE_lt_Om2 j)
    have hΘζ := snTh_lt_Om1 hl hX hζW.le
    refine ⟨(rvWe_lt_succ hζW).trans (uuWe_lt_Y (hE.trans_le hS.leY)), ?_⟩
    exact (rvOe_lt_succ hΘζ).trans (uuOe_lt_Y2 (hS.ltY E' hEH h1 hE))
  induction h with
  | @one E ζ h1 hEH hE _ hζ hζ0 hj =>
    obtain ⟨t1, t2⟩ := hterm hEH h1 hE hζ hj
    exact ⟨h1, hEH, hE, dvd_mul_right _ _, mul_ne_zero (leWe_pos E).ne' hζ0, t1, t2⟩
  | @add X0 Xh0 E0 E ζ _ h1 hEE hEH hE _ hζ hζ0 hj ih =>
    obtain ⟨-, -, -, hd0, -, hX0, hXh0⟩ := ih
    obtain ⟨t1, t2⟩ := hterm hEH h1 hE hζ hj
    refine ⟨h1, hEH, hE, dvd_add ((leWe_dvd hEE.le).trans hd0) (dvd_mul_right _ _), ?_,
      uqY_SC.isPrincipal hX0 t1, uuY2_SC.isPrincipal hXh0 t2⟩
    intro h'
    have := le_antisymm (h' ▸ le_add_self : leWe E * ζ ≤ 0) zero_le
    exact mul_ne_zero (leWe_pos E).ne' hζ0 this

omit hl hX in
/-- **The family is hereditary.** -/
theorem uuG_mono {β β' X Xh E : Ordinal.{0}} (hββ : β ≤ β') (h : UuG S l Eb Th Ow β X Xh E) :
    UuG S l Eb Th Ow β' X Xh E := by
  induction h with
  | @one E ζ h1 hEH hE hcl hζ hζ0 hj =>
    obtain ⟨j, hj⟩ := hj
    exact UuG.one h1 hEH hE ((hS.own E hEH h1 hE).mono _ _ _ _ hcl hββ le_rfl) hζ hζ0
      ⟨j, hj.trans_le (rvEE_mono_base hββ j)⟩
  | @add X0 Xh0 E0 E ζ _ h1 hEE hEH hE hcl hζ hζ0 hj ih =>
    obtain ⟨j, hj⟩ := hj
    exact UuG.add ih h1 hEE hEH hE ((hS.own E hEH h1 hE).mono _ _ _ _ hcl hββ le_rfl) hζ hζ0
      ⟨j, hj.trans_le (rvEE_mono_base hββ j)⟩

omit hl hX in
theorem uuShG_mono {b b' X Xh : Ordinal.{0}} (hbb : b ≤ b') (h : uuShG S l Eb Th Ow b X Xh) :
    uuShG S l Eb Th Ow b' X Xh := by
  obtain ⟨E, hE⟩ := h
  exact ⟨E, uuG_mono hS hbb hE⟩

/-- **Every member is a shift past `Γ₂` own relative to `β` with the top law at the bases `≥ β`.** -/
theorem uuG_sh {β X Xh E : Ordinal.{0}} (h : UuG S l Eb Th Ow β X Xh E) :
    UjSh S l β X Xh ∧ RvTop S l β X Xh 0 := by
  have hY := uqY_SC (S := S)
  have hWY := uqW_lt_Y (S := S)
  have hY2 := uuY2_SC (S := S)
  have hΩY2 := uuOm1_lt_Y2 (S := S)
  have hne := (uuG_data hl hX hS h).2.2.2.2.1
  induction h with
  | @one E ζ h1 hEH hE hcl hζ hζ0 hj =>
    obtain ⟨j0, hj0⟩ := hj
    have hζW : ζ < Om (1 + 1) := hj0.trans (rvEE_lt_Om2 j0)
    have h := ujFam hl hX (hS.own E hEH h1 hE) (hS.lev E hEH h1 hE) (X0 := 0) (Xh0 := 0) (β := β)
      (Or.inl ⟨rfl, rfl⟩) (dvd_zero _)
      (by rw [zero_add]; exact hY.isPrincipal (uuWe_lt_Y (hE.trans_le hS.leY)) hWY)
      (by rw [zero_add]; exact hY2.isPrincipal (uuOe_lt_Y2 (hS.ltY E hEH h1 hE)) hΩY2) hcl ζ hζ ⟨j0, hj0⟩
      (snTh_lt_Om1 hl hX hζW.le)
    rw [zero_add, zero_add] at h
    exact ujOff_ne h hne
  | @add X0 Xh0 E0 E ζ h0 h1 hEE hEH hE hcl hζ hζ0 hj ih =>
    obtain ⟨-, -, -, hd0, hne0, hX0, hXh0⟩ := uuG_data hl hX hS h0
    obtain ⟨j0, hj0⟩ := hj
    have hζW : ζ < Om (1 + 1) := hj0.trans (rvEE_lt_Om2 j0)
    have h := ujFam hl hX (hS.own E hEH h1 hE) (hS.lev E hEH h1 hE) (β := β)
      (Or.inr (ih hne0)) ((leWe_dvd (Order.add_one_le_of_lt hEE)).trans hd0)
      (hY.isPrincipal (hY.isPrincipal hX0 (uuWe_lt_Y (hE.trans_le hS.leY))) hWY)
      (hY2.isPrincipal (hY2.isPrincipal hXh0 (uuOe_lt_Y2 (hS.ltY E hEH h1 hE))) hΩY2) hcl ζ hζ ⟨j0, hj0⟩
      (snTh_lt_Om1 hl hX hζW.le)
    exact ujOff_ne h hne

/-- **The family meets the hypotheses of the own-atom layer past `Γ₂`** (`hSh` of `Uu.uuOwnRead`,
`Uu.uuDigMove`, `Uu.uuClsE`). -/
theorem uuShG_sh : ∀ b X Xh, uuShG S l Eb Th Ow b X Xh → UjSh S l b X Xh ∧
    ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → RvTop S l b X Xh e := by
  rintro b X Xh ⟨E, hE⟩
  obtain ⟨hs, ht⟩ := uuG_sh hl hX hS hE
  exact ⟨hs, ujTopE hs hl hX ht⟩

end Main

end Googology.Trans.PoR.InaccPsi.R2.Uu

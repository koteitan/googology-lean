import Googology.Trans.PoR.InaccPsi.R2.UjLim

/-!
# The first shifts past `Γ₂`: `Γ₂ + Ω₂·n + e`, `Γ₂ + Ω₂·ω`, and the ladder `X + Ω₂·n` over any shift

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ_{Ω₂}(β + W^E)`, `Γ₂ = Ua.uaGam = ψ_{Ω₃}(0)`
(`Ud.udGam_eq`), `G₁ = ψ_{Ω₂}(0)`, `T = Ug.ugTh` (`T Γ₂ = G₁`, `Ug.ugGam`).

* `ujBase_down` (a base of a shift is a base of every smaller shift), `ujBase0` (`β = 0` is a base of every
  shift below `Y₃`);
* `ujSh_addW` (**`UjSh X X̂ ⇒ UjSh (X + Ω₂) (X̂ + Ω₁)`**, no extra hypothesis), `ujShN`, `ujTopN`
  (**`RvTop X 0 ⇒ RvTop (X + Ω₂·n) (X̂ + Ω₁·n) e` for every `n` and every code `e`**), `ujLt_omega`, `ujShW`,
  `ujTopW_om` (**the limit `X + Ω₂·ω`**);
* `ujShG` (**`(Γ₂, G₁)` is a shift past `Γ₂` at every base**), `ujTopG` (**`RvTop Γ₂ 0`** from `Ug.ugReadT`),
  `ujGamTopN`, `ujGamTopW`;
* `ujRead0` (the reading at the base `0` of a restart), `ujGamRead` (**`Θ_λ(ψ_{Ω₂}(W^{Γ₂ + Ω₂·n})) =
  ψ_{Ω₁}(A + 1 + Ω^{G₁ + Ω₁·n})`**), `ujGamReadW` (the same at `Γ₂ + Ω₂·ω`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Uj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rq
  Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Ua
  Googology.Trans.PoR.InaccPsi.R2.Ud

variable {S : InaccSeq.{0}}

/-- **A base of a shift is a base of every smaller shift** (exponent `0`). -/
theorem ujBase_down {l X X' β : Ordinal.{0}} (hb : RoBaseE S l X 0 β) (h : X' ≤ X) : RoBaseE S l X' 0 β := by
  obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hb
  simp only [add_zero] at hβd hβA hβown
  have e : X' + 0 = X' := add_zero X'
  refine ⟨by rw [e]; exact (leWe_dvd h).trans hβd, hβH,
    by rw [e]; exact lt_of_le_of_lt ((add_le_add_iff_left β).2 (leWe_mono h)) hβA,
    fun d hd => by rw [e] at hd; exact hβown d (hd.trans (leWe_mono h)), fun e' _ h' => ?_⟩
  obtain rfl : e' = 0 := le_antisymm h' zero_le
  exact (SC_psi (InR_Om_succ 1) _).1

/-- **`β = 0` is a base of every shift below `Y₃`.** -/
theorem ujBase0 (l : Ordinal.{0}) {X : Ordinal.{0}} (hX : X < ugY S) : RoBaseE S l X 0 0 := by
  refine ⟨dvd_zero _, CSet.zero_mem _ _, ?_, fun d _ => CSet.zero_mem _ _, fun e' _ h' => ?_⟩
  · rw [zero_add, add_zero]
    have hW : leWe X < ugY S := (leWe_lt_SC (ujY_SC (S := S) 1) (ujY_gt (S := S) 1) hX).1
    exact (hW.trans ugY_lt_Om3).trans (Ry.ryOm3_lt.trans_le (ConjT.OmW_le_A S _))
  · obtain rfl : e' = 0 := le_antisymm h' zero_le
    exact (SC_psi (InR_Om_succ 1) _).1

/-- **The next shift**: `UjSh X X̂ ⇒ UjSh (X + Ω₂) (X̂ + Ω₁)`. -/
theorem ujSh_addW {l b X Xh : Ordinal.{0}} (hs : UjSh S l b X Xh) : UjSh S l b (X + Om (1 + 1)) (Xh + Om 1) := by
  have hY : SC (ugY S) := ujY_SC (S := S) 1
  have hWY : Om (1 + 1 : Ordinal.{0}) < ugY S := ujY_gt (S := S) 1
  have hY2 : SC (ujY S 0) := ujY_SC 0
  have hΩY2 : Om (1 : Ordinal.{0}) < ujY S 0 := by have := ujY_gt (S := S) 0; rwa [zero_add] at this
  have hle : S.psi (b + leWe X) (Om (1 + 1)) ≤ S.psi (b + leWe (X + Om (1 + 1))) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left b).2 (leWe_mono le_self_add))).1
  have hXY : X + Om (1 + 1) < ugY S := hs.ltY
  have hXhY : Xh + Om 1 < ujY S 0 := hs.ltYh
  refine ⟨fun h => hs.ne (le_antisymm (h ▸ le_self_add) zero_le), dvd_add hs.dvd dvd_rfl,
    CSet.add_mem hs.hull (mxOm2_mem _ _),
    CSet.add_mem (CSet_mono le_self_add hle hs.mem) (mxOm2_mem _ _),
    CSet.add_mem (CSet_mono le_self_add (gxTh_mono hle) hs.memh) (CSet.Om_mem (CSet.one_mem _ _)),
    hY.isPrincipal hXY hWY, hY2.isPrincipal hXhY hΩY2,
    fun Q hQ hb => UgC.add (hs.cl Q hQ (hle.trans hb)) UgC.om,
    fun Q hQ hb => UgC.add (hs.clh Q hQ ((gxTh_mono hle).trans hb)) UgC.om⟩

/-- The shifts `X + Ω₂·n`. -/
theorem ujShN {l b X Xh : Ordinal.{0}} (hs : UjSh S l b X Xh) :
    ∀ n : ℕ, UjSh S l b (X + Om (1 + 1) * (n : Ordinal.{0})) (Xh + Om 1 * (n : Ordinal.{0}))
  | 0 => by simpa only [Nat.cast_zero, mul_zero, add_zero] using hs
  | n + 1 => by
    have h := ujSh_addW (ujShN hs n)
    rw [Nat.cast_succ, mul_add_one, mul_add_one, ← add_assoc, ← add_assoc]; exact h

/-- **`X + Ω₂·ω` is a shift.** -/
theorem ujShW {l b X Xh : Ordinal.{0}} (hs : UjSh S l b X Xh) :
    UjSh S l b (X + Om (1 + 1) * ω) (Xh + Om 1 * ω) := by
  have hY : SC (ugY S) := ujY_SC (S := S) 1
  have hWY : Om (1 + 1 : Ordinal.{0}) < ugY S := ujY_gt (S := S) 1
  have hY2 : SC (ujY S 0) := ujY_SC 0
  have hΩY2 : Om (1 : Ordinal.{0}) < ujY S 0 := by have := ujY_gt (S := S) 0; rwa [zero_add] at this
  have h2 : (1 + 1 : Ordinal.{0}) ≠ 0 := by rw [one_add_one_eq_two]; exact two_ne_zero
  have hle : S.psi (b + leWe X) (Om (1 + 1)) ≤ S.psi (b + leWe (X + Om (1 + 1) * ω)) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left b).2 (leWe_mono le_self_add))).1
  have hX : X < ugY S := lt_of_le_of_lt le_self_add hs.ltY
  have hXh : Xh < ujY S 0 := lt_of_le_of_lt le_self_add hs.ltYh
  have hωY : (ω : Ordinal.{0}) < ugY S := Lw.lw_omega_lt_SC hY
  have hωY2 : (ω : Ordinal.{0}) < ujY S 0 := Lw.lw_omega_lt_SC hY2
  have hWω : Om (1 + 1) * ω < ugY S := ldMul_lt_SC hY hWY hωY
  have hΩω : Om 1 * ω < ujY S 0 := ldMul_lt_SC hY2 hΩY2 hωY2
  have hΩC : ∀ a c, Om (1 : Ordinal.{0}) ∈ S.CSet a c := fun a c => CSet.Om_mem (CSet.one_mem a c)
  refine ⟨fun h => hs.ne (le_antisymm (h ▸ le_self_add) zero_le), dvd_add hs.dvd (dvd_mul_right _ _),
    CSet.add_mem hs.hull (rqMulK_mem ldOm2_SC (mxOm2_mem _ _) (ConjT.omega_mem S _ _)),
    CSet.add_mem (CSet_mono le_self_add hle hs.mem) (rqMulK_mem ldOm2_SC (mxOm2_mem _ _) (ConjT.omega_mem S _ _)),
    CSet.add_mem (CSet_mono le_self_add (gxTh_mono hle) hs.memh)
      (rqMulK_mem Ph.ph_SC_Om1 (hΩC _ _) (ConjT.omega_mem S _ _)),
    hY.isPrincipal (hY.isPrincipal hX hWω) hWY, hY2.isPrincipal (hY2.isPrincipal hXh hΩω) hΩY2,
    fun Q hQ hb => UgC.add (hs.cl Q hQ (hle.trans hb)) (ugC_mulK hQ h2 ω (UgC.small (Lw.lw_omega_lt_SC hQ))),
    fun Q hQ hb => UgC.add (hs.clh Q hQ ((gxTh_mono hle).trans hb))
      (ugC_mulK hQ one_ne_zero ω (UgC.small (Lw.lw_omega_lt_SC hQ)))⟩

/-- Below `A + κ·ω` every ordinal is below some `A + κ·n`. -/
theorem ujLt_omega {A κ z : Ordinal.{0}} (hκ : κ ≠ 0) (h : z < A + κ * ω) :
    ∃ n : ℕ, 1 ≤ n ∧ z < A + κ * (n : Ordinal.{0}) := by
  rcases lt_or_ge z A with hz | hz
  · refine ⟨1, le_rfl, hz.trans_le le_self_add⟩
  obtain ⟨y, rfl⟩ := exists_add_of_le hz
  have hy : y < κ * ω := (add_lt_add_iff_left A).1 h
  have hq : y / κ < ω := (Ordinal.lt_mul_iff_div_lt hκ).1 hy
  obtain ⟨m, hm⟩ := lt_omega0.1 hq
  refine ⟨m + 1, Nat.le_add_left 1 m, (add_lt_add_iff_left A).2 ?_⟩
  rw [Nat.cast_succ, mul_add_one, ← hm]
  exact Ordinal.lt_mul_div_add y hκ

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The ladder over any shift past `Γ₂`**: `RvTop X 0 ⇒ RvTop (X + Ω₂·n) (X̂ + Ω₁·n) 0` for every `n`. -/
theorem ujTopN {b X Xh : Ordinal.{0}} (hs : UjSh S l b X Xh) (h0 : RvTop S l b X Xh 0) :
    ∀ n : ℕ, RvTop S l b (X + Om (1 + 1) * (n : Ordinal.{0})) (Xh + Om 1 * (n : Ordinal.{0})) 0
  | 0 => by simpa only [Nat.cast_zero, mul_zero, add_zero] using h0
  | n + 1 => by
    have hsn := ujShN hs n
    have h := ujTopW hsn hl hX (ujTopE hsn hl hX (ujTopN hs h0 n))
    rw [Nat.cast_succ, mul_add_one, mul_add_one, ← add_assoc, ← add_assoc]; exact h

/-- **Every code exponent on the ladder**: `RvTop (X + Ω₂·n) (X̂ + Ω₁·n) e` for every code `e`. -/
theorem ujTopNE {b X Xh : Ordinal.{0}} (hs : UjSh S l b X Xh) (h0 : RvTop S l b X Xh 0) (n : ℕ) :
    ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) →
      RvTop S l b (X + Om (1 + 1) * (n : Ordinal.{0})) (Xh + Om 1 * (n : Ordinal.{0})) e :=
  ujTopE (ujShN hs n) hl hX (ujTopN hl hX hs h0 n)

/-- **The limit of the ladder**: `RvTop X 0 ⇒ RvTop (X + Ω₂·ω) (X̂ + Ω₁·ω) 0`. -/
theorem ujTopW_om {b X Xh : Ordinal.{0}} (hs : UjSh S l b X Xh) (h0 : RvTop S l b X Xh 0) :
    RvTop S l b (X + Om (1 + 1) * ω) (Xh + Om 1 * ω) 0 := by
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  have hnω : ∀ n : ℕ, ((n : ℕ) : Ordinal.{0}) < ω := fun n => natCast_lt_omega0 n
  refine ujTopLimSh hl hX (ujShW hs) (fun x _ hx => ?_) (fun z hz => ?_)
  · obtain ⟨n, -, hn⟩ := ujLt_omega hW0 hx
    refine ⟨_, _, (add_le_add_iff_left X).2 (mul_le_mul_right (hnω n).le _), hn,
      (add_lt_add_iff_left Xh).2 ((mul_lt_mul_iff_right₀ (Om_pos one_ne_zero)).2 (hnω n)),
      ujShN hs n, ujTopN hl hX hs h0 n⟩
  · obtain ⟨n, -, hn⟩ := ujLt_omega hΩ0 hz
    exact ⟨_, _, (add_lt_add_iff_left X).2 ((mul_lt_mul_iff_right₀ ldOm2_SC.1).2 (hnω n)), hn,
      ujShN hs n, ujTopN hl hX hs h0 n⟩

end Main

/-- `Γ₂ < Y₃`. -/
theorem ujGam_lt_Y : uaGam < ugY S := by rw [udGam_eq (S := S)]; exact ujG3_lt_Y

/-- **`(Γ₂, ψ_{Ω₂}(0))` is a shift past `Γ₂` at every base.** -/
theorem ujShG (l b : Ordinal.{0}) : UjSh S l b uaGam (S.psi 0 (Om (1 + 1))) := by
  have hY : SC (ugY S) := ujY_SC (S := S) 1
  have hWY : Om (1 + 1 : Ordinal.{0}) < ugY S := ujY_gt (S := S) 1
  have hY2 : SC (ujY S 0) := ujY_SC 0
  have hΩY2 : Om (1 : Ordinal.{0}) < ujY S 0 := by have := ujY_gt (S := S) 0; rwa [zero_add] at this
  have hG1 : (0 : Ordinal.{0}) < S.psi 0 (Om (1 + 1)) := (SC_psi (InR_Om_succ 1) 0).1
  have hdvd : Om (1 + 1) ∣ uaGam := by
    have h := (leWe_lt_SC uaGam_spec.1 uaGam_spec.2 (gg_one_lt_of_SC uaGam_spec.1)).2
    rwa [leWe_one] at h
  have hmem : ∀ c, uaGam ∈ S.CSet uaGam c := fun c => by
    rw [udGam_eq (S := S)]
    exact CSet.psi_mem (SC_psi ugInR3 0).1 ugInR3 (Ry.ryOm3_mem _ _) (CSet.zero_mem _ _)
  refine ⟨ugGam_pos.ne', hdvd, ugGam_mem l, hmem _,
    CSet.psi_mem hG1 (InR_Om_succ 1) (mxOm2_mem _ _) (CSet.zero_mem _ _),
    hY.isPrincipal ujGam_lt_Y hWY, hY2.isPrincipal ujY2_gt_G1 hΩY2,
    fun Q hQ _ => ugC_gam hQ.1, fun Q hQ _ => UgC.psi (UgC.zero hQ.1) hG1⟩

section Gam

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The top at `Γ₂` at every base**: `RvTop Γ₂ G₁ 0` (`Ug.ugReadT` through `ujBase_down`). -/
theorem ujTopG (b : Ordinal.{0}) : RvTop S l b uaGam (S.psi 0 (Om (1 + 1))) 0 := by
  intro β Â hb _ hÂ hbase
  rw [add_zero, gxTh_zero, add_zero]
  have h := ugReadT hl hX (fun k => ujBase_down hb (leWe_lt_SC uaGam_spec.1 uaGam_spec.2 (udX_lt k)).1.le)
    hÂ hbase
  rwa [ugGam] at h

/-- **`RvTop (Γ₂ + Ω₂·n) (G₁ + Ω₁·n) e`** for every `n` and every code `e`, at every base. -/
theorem ujGamTopN (b : Ordinal.{0}) (n : ℕ) : ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) →
    RvTop S l b (uaGam + Om (1 + 1) * (n : Ordinal.{0})) (S.psi 0 (Om (1 + 1)) + Om 1 * (n : Ordinal.{0})) e :=
  ujTopNE hl hX (ujShG l b) (ujTopG hl hX b) n

/-- **`RvTop (Γ₂ + Ω₂·ω) (G₁ + Ω₁·ω) 0`** at every base. -/
theorem ujGamTopW (b : Ordinal.{0}) :
    RvTop S l b (uaGam + Om (1 + 1) * ω) (S.psi 0 (Om (1 + 1)) + Om 1 * ω) 0 :=
  ujTopW_om hl hX (ujShG l b) (ujTopG hl hX b)

omit hl hX in
/-- **The reading at the base `0` of a restart**: `Θ_λ(ψ_{Ω₂}(W^X)) = ψ_{Ω₁}(A + 1 + Ω^{X̂})`. -/
theorem ujRead0 {X Xh A : Ordinal.{0}} (hT : RvTop S l 0 X Xh 0) (hXY : X < ugY S)
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (leWe X) (Om (1 + 1))) = S.psi (A + 1 + leOe Xh) (Om 1) := by
  have hÂ : A + 1 ∈ S.CSet (A + 1) (S.psi (A + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA) (CSet.one_mem _ _)
  have h := hT 0 (A + 1) (ujBase0 l hXY) le_rfl hÂ (ldBlk_zero hA hρ)
  rw [add_zero, gxTh_zero, add_zero] at h
  unfold leTe at h
  rwa [zero_add] at h

/-- **THE READINGS ON THE FIRST LADDER PAST `Γ₂`**: `Θ_λ(ψ_{Ω₂}(W^{Γ₂ + Ω₂·n})) = ψ_{Ω₁}(A + 1 + Ω^{G₁ + Ω₁·n})`. -/
theorem ujGamRead {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    (n : ℕ) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (leWe (uaGam + Om (1 + 1) * (n : Ordinal.{0}))) (Om (1 + 1))) =
      S.psi (A + 1 + leOe (S.psi 0 (Om (1 + 1)) + Om 1 * (n : Ordinal.{0}))) (Om 1) := by
  have hs := ujShN (ujShG (S := S) l 0) n
  exact ujRead0 (ujTopN hl hX (ujShG l 0) (ujTopG hl hX 0) n) (lt_of_le_of_lt le_self_add hs.ltY) hA hρ

/-- **The reading at `Γ₂ + Ω₂·ω`**: `Θ_λ(ψ_{Ω₂}(W^{Γ₂ + Ω₂·ω})) = ψ_{Ω₁}(A + 1 + Ω^{G₁ + Ω₁·ω})`. -/
theorem ujGamReadW {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (leWe (uaGam + Om (1 + 1) * ω)) (Om (1 + 1))) =
      S.psi (A + 1 + leOe (S.psi 0 (Om (1 + 1)) + Om 1 * ω)) (Om 1) := by
  have hs := ujShW (ujShG (S := S) l 0)
  exact ujRead0 (ujGamTopW hl hX 0) (lt_of_le_of_lt le_self_add hs.ltY) hA hρ

end Gam

end Googology.Trans.PoR.InaccPsi.R2.Uj

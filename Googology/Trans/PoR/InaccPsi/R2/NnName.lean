import Googology.Trans.PoR.InaccPsi.R2.NnInst

/-!
# The link `O ↔ η` past `Φ_Γ`: the offset at the names `η₁ + Ω₁^γ`, `η₀ + Ω₁^γ·β`, `η₁ + W`, `η₀ + W·β`

`P(η) = ψ_{Ω₁}(Ω_ω + θ·η)` (`Nm.Pv`), `ι` the index of Theorem GEN (`υ_{ι(η)} = P(η)`), `W = Ω₁^{Ω₁}`.  Theorems
START and SEG (`R2.NmS`, `R2.NmG`) hold from every good base `η₁`, at every height; with Theorems LEVEL and GG
(`R2.NnLev`, `R2.NnGG`) the recursive offset at the named indices is read off the last `Ω₁`-digit of the name, for
every term system `X` with linear (and square) terms, in particular for `VzOrec` and the layers `xtLL k`:

* `nn_nxt_succ`: the least value of a normal `f` above `x` has a successor index (so its `logend` is `0`);
* `nnStart` (**at `η₁ + Ω₁^γ`**): `η₁` good, `Ω₁^γ ∣ η₁`, `1 ≤ γ`, START's hypothesis, `γ < P(η₁ + Ω₁^γ)`
  ⟹ `O(ι(η₁ + Ω₁^γ)) = P(η₁ + Ω₁^γ)·γ`;
* `nnSeg` (**at `η₀ + Ω₁^γ·β`**): `η₀` good, `Ω₁^γ ∣ η₀`, `1 ≤ γ < P(η₀) = V_γ(c₀)`, `0 < β < Zu(η₀, Ω₁^γ)`
  ⟹ `O(ι(η₀ + Ω₁^γ·β)) = P(η₀ + Ω₁^γ·β)·γ + logend(β)`;
* `nnStartW` (**at `η₁ + W`**): `η₁` good, `W ∣ η₁` ⟹ `O(ι(η₁ + W)) = P(η₁ + W)²`;
* `nnSegW` (**at `η₀ + W·β`**): `η₀` good, `W ∣ η₀`, `P(η₀) = GG(c₀)`, `0 < β < Zu(η₀, W)`
  ⟹ `O(ι(η₀ + W·β)) = P(η₀ + W·β)² + logend(β)`;
* `nnPhiW` (**the end of a `W`-segment**): `η₀` good, `W ∣ η₀`, `P(η₀) = GG(c₀)` ⟹ `ρ = P(η₀ + W·Zu(η₀, W))` is
  a fixed point of `GG` and `ρ² + ρ ≤ O(ι(η₀ + W·Zu(η₀, W)))`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Nn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Br
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Cp

variable {S : InaccSeq.{0}} {X : XtSys}

theorem nn_Pv_lt (S : InaccSeq.{0}) (η : Ordinal.{0}) : Pv S η < Om1 := by
  rw [Om1_eq]; exact Pv_lt_Om1 S η

/-- The least value of a normal `f` above `x` is `f(c + 1)` for some `c`. -/
theorem nn_nxt_succ {f : Ordinal.{0} → Ordinal.{0}} (hf : IsNormal f) (hf0 : f 0 = 0) (x : Ordinal.{0}) :
    ∃ c, nxt f x = f (c + 1) := by
  set T := {c | x < f c} with hT
  have hne : T.Nonempty := ⟨x + 1, (lt_add_one x).trans_le (hf.strictMono.le_apply)⟩
  have hmem : x < f (sInf T) := csInf_mem hne
  have hmin : ∀ c < sInf T, f c ≤ x := fun c hc => not_lt.1 (notMem_of_lt_csInf' (s := T) hc)
  rcases zero_or_succ_or_isSuccLimit (sInf T) with h0 | ⟨c, hc⟩ | hlim
  · rw [h0, hf0] at hmem; exact absurd hmem (not_lt.2 zero_le)
  · refine ⟨c, ?_⟩
    show f (sInf T) = _
    rw [← hc, succ_eq_add_one]
  · exfalso
    have := (hf.lt_iff_exists_lt hlim).1 hmem
    obtain ⟨c, hc, hxc⟩ := this
    exact absurd (hmin c hc) (not_le.2 hxc)

theorem nn_succ_ne (c : Ordinal.{0}) : c + 1 ≠ 0 := (add_pos_of_right zero_lt_one c).ne'

theorem nn_not_prelim (c : Ordinal.{0}) : ¬ IsSuccPrelimit (c + 1) := fun hp =>
  hp c (by rw [← succ_eq_add_one]; exact Order.covBy_succ c)

theorem nn_lg_succ (c : Ordinal.{0}) : lg (c + 1) = 0 := by
  refine cdExp_eq (nn_succ_ne c) (by rw [opow_zero]; exact one_dvd _) ?_
  rw [zero_add, opow_one]
  intro h
  exact nn_not_prelim c (isSuccPrelimit_iff_omega0_dvd.2 h)

/-- A successor ordinal is not additive principal unless it is `1`; it is never a fixed point of `υ`. -/
theorem nn_succ_not_fix (c : Ordinal.{0}) : upsilon (c + 1) ≠ c + 1 := by
  intro h
  have hE : InE (c + 1) := inE_of_fp (lt_of_le_of_lt zero_le (lt_add_one c)) h
  have hω : ω ∣ c + 1 := by
    have := opow_dvd_opow ω (Order.one_le_iff_ne_zero.2 (nn_succ_ne c))
    rw [opow_one] at this; rwa [show ω ^ (c + 1) = c + 1 from hE] at this
  exact nn_not_prelim c (isSuccPrelimit_iff_omega0_dvd.2 hω)

/-- Data of a value `F = V_γ(a)` of exact level `γ` with `γ < F`, `a` not a fixed point of `V_γ`. -/
theorem nn_V_exact {γ a : Ordinal.{0}} (hγ0 : γ ≠ 0) (ha0 : a ≠ 0) (hna : VG γ a ≠ a)
    (hγF : γ < VG γ a) :
    upsilon (VG γ a) = VG γ a ∧ IsRestartIdx (VG γ a) ∧ ¬ IsGP (VG γ a) ∧ levG (VG γ a) = γ ∧
      invG γ (VG γ a) = a := by
  have hfix : upsilon (VG γ a) = VG γ a := ups_fix_of_VG hγ0 ⟨a, rfl⟩
  have hpos : 0 < VG γ a := VG_pos (pos_iff_ne_zero.2 ha0)
  have hne : VG γ (VG γ a) ≠ VG γ a := fun h => hna ((VG_strictMono γ).injective h)
  refine ⟨hfix, ri_of_fp hpos hfix, fun h => hne (h.2 γ hγF), ?_, invG_VG γ a⟩
  exact le_antisymm ((levG_spec ⟨γ, hne⟩).2.2 γ hne) (levG_ge ⟨γ, hne⟩ hγ0 ⟨a, rfl⟩)

/-- **The offset at `η₁ + Ω₁^γ`** (Theorem START): `O(ι(η₁ + Ω₁^γ)) = P(η₁ + Ω₁^γ)·γ`. -/
theorem nnStart (hX : NnLin X) {γ η1 : Ordinal.{0}} (hγ0 : γ ≠ 0) (hg : Bt.Good S η1)
    (hd : Om (1 : Ordinal.{0}) ^ γ ∣ η1) (hC : ∀ δ < γ, δ < nxt (VG δ) (Pv S η1))
    (hγP : γ < Pv S (η1 + Om 1 ^ γ)) :
    xtOrec X (iota S (η1 + Om 1 ^ γ)) = Pv S (η1 + Om 1 ^ γ) * γ := by
  have hP := start_all S γ η1 hg hd hC
  obtain ⟨c, hc⟩ := nn_nxt_succ (VG_normal γ) (VG_at_zero γ) (Pv S η1)
  rw [hc] at hP
  have hna : VG γ (c + 1) ≠ c + 1 := by
    intro h
    exact nn_succ_not_fix c (ups_fix_of_VG hγ0 ⟨c + 1, h⟩)
  rw [hP] at hγP ⊢
  obtain ⟨hfix, hri, hG, hlev, hinv⟩ := nn_V_exact hγ0 (nn_succ_ne c) hna hγP
  rw [iota_of_fix hP hfix, nnLev hX _ hri (hP ▸ nn_Pv_lt S _) hfix hG, hlev, hinv, nn_lg_succ,
    add_zero]

/-- **The offset at `η₀ + Ω₁^γ·β`** (Theorem SEG): `O(ι(η₀ + Ω₁^γ·β)) = P(η₀ + Ω₁^γ·β)·γ + logend(β)` for
`0 < β < Zu(η₀, Ω₁^γ)`. -/
theorem nnSeg (hX : NnLin X) {γ η0 c0 β : Ordinal.{0}} (hγ0 : γ ≠ 0) (hg : Bt.Good S η0)
    (hd : Om (1 : Ordinal.{0}) ^ γ ∣ η0) (hγP : γ < Pv S η0) (h0 : Pv S η0 = VG γ c0) (hβ0 : β ≠ 0)
    (hβ : β < Zu S η0 (Om 1 ^ γ)) :
    xtOrec X (iota S (η0 + Om 1 ^ γ * β)) = Pv S (η0 + Om 1 ^ γ * β) * γ + lg β := by
  have hP := seg_all S γ η0 c0 hg hd hγP h0 β hβ.le
  have hcβ0 : c0 + β ≠ 0 := fun h => hβ0 (by
    have hle : β ≤ c0 + β := le_add_self
    rw [h] at hle; exact le_antisymm hle zero_le)
  have hna : VG γ (c0 + β) ≠ c0 + β := by
    intro h
    have hu : upsilon (c0 + β) = c0 + β := ups_fix_of_VG hγ0 ⟨c0 + β, h⟩
    have hp := (cp_fix_facts (ri_of_fp (pos_iff_ne_zero.2 hcβ0) hu) hu).2.1
    -- `c₀ + β` additive principal with `β > 0` forces `c₀ + β = β`, and then `P(η₀ + Ω₁^γ·β) = β`
    have hβeq : c0 + β = β := by
      rcases lt_or_eq_of_le (le_add_self : β ≤ c0 + β) with hlt | heq
      · rcases eq_or_ne c0 0 with hc0 | hc0
        · rw [hc0, zero_add]
        · exact absurd (hp (lt_add_of_pos_right c0 (pos_iff_ne_zero.2 hβ0)) hlt) (lt_irrefl _)
      · exact heq.symm
    have hPβ : Pv S (η0 + Om 1 ^ γ * β) ≤ β := by rw [hP, h, hβeq]
    exact absurd (csInf_le' hPβ : Zu S η0 (Om 1 ^ γ) ≤ β) (not_le.2 hβ)
  have hγF : γ < VG γ (c0 + β) := hγP.trans_le (by rw [← hP]; exact Pv_mono le_self_add)
  obtain ⟨hfix, hri, hG, hlev, hinv⟩ := nn_V_exact hγ0 hcβ0 hna hγF
  rw [hP, iota_of_fix hP hfix, nnLev hX _ hri (hP ▸ nn_Pv_lt S _) hfix hG, hlev, hinv]
  have hlg : lg (c0 + β) = lg β := cpExp_add c0 hβ0
  rw [hlg]

/-- Data of a `Γ`-point `F = GG(a)` with `GG(F) ≠ F`. -/
theorem nn_GG_exact {a : Ordinal.{0}} (ha0 : a ≠ 0) (hna : GG a ≠ a) :
    IsGP (GG a) ∧ upsilon (GG a) = GG a ∧ IsRestartIdx (GG a) ∧ GG (GG a) ≠ GG a ∧ invGG (GG a) = a := by
  have hG := isGP_GG (pos_iff_ne_zero.2 ha0)
  have hfix := nn_gp_fix hG
  exact ⟨hG, hfix, ri_of_fp hG.1 hfix, fun h => hna (GG_strictMono.injective h), invGG_GG a⟩

/-- **The offset at `η₁ + W`**: `O(ι(η₁ + W)) = P(η₁ + W)²`. -/
theorem nnStartW (hX : NnLin X) (hS : NnSq X) {η1 : Ordinal.{0}} (hg : Bt.Good S η1) (hd : W ∣ η1) :
    xtOrec X (iota S (η1 + W)) = Pv S (η1 + W) * Pv S (η1 + W) := by
  have hP := start_GG hg hd
  obtain ⟨c, hc⟩ := nn_nxt_succ GG_normal GG_zero (Pv S η1)
  rw [hc] at hP
  have hna : GG (c + 1) ≠ c + 1 := by
    intro h
    have hG : IsGP (c + 1) := by rw [← h]; exact isGP_GG (lt_of_le_of_lt zero_le (lt_add_one c))
    exact nn_succ_not_fix c (nn_gp_fix hG)
  obtain ⟨hG, hfix, hri, hGF, hinv⟩ := nn_GG_exact (nn_succ_ne c) hna
  rw [hP, iota_of_fix hP hfix, nnGG hX hS _ hri (hP ▸ nn_Pv_lt S _) hG hGF, hinv, nn_lg_succ, add_zero]

/-- **The offset at `η₀ + W·β`**: `O(ι(η₀ + W·β)) = P(η₀ + W·β)² + logend(β)` for `0 < β < Zu(η₀, W)`. -/
theorem nnSegW (hX : NnLin X) (hS : NnSq X) {η0 c0 β : Ordinal.{0}} (hg : Bt.Good S η0) (hd : W ∣ η0)
    (h0 : Pv S η0 = GG c0) (hβ0 : β ≠ 0) (hβ : β < Zu S η0 W) :
    xtOrec X (iota S (η0 + W * β)) = Pv S (η0 + W * β) * Pv S (η0 + W * β) + lg β := by
  have hP := seg_GG hg hd h0 β hβ.le
  have hcβ0 : c0 + β ≠ 0 := fun h => hβ0 (by
    have hle : β ≤ c0 + β := le_add_self
    rw [h] at hle; exact le_antisymm hle zero_le)
  have hna : GG (c0 + β) ≠ c0 + β := by
    intro h
    have hG : IsGP (c0 + β) := by rw [← h]; exact isGP_GG (pos_iff_ne_zero.2 hcβ0)
    have hu := nn_gp_fix hG
    have hp := (cp_fix_facts (ri_of_fp hG.1 hu) hu).2.1
    have hβeq : c0 + β = β := by
      rcases lt_or_eq_of_le (le_add_self : β ≤ c0 + β) with hlt | heq
      · rcases eq_or_ne c0 0 with hc0 | hc0
        · rw [hc0, zero_add]
        · exact absurd (hp (lt_add_of_pos_right c0 (pos_iff_ne_zero.2 hβ0)) hlt) (lt_irrefl _)
      · exact heq.symm
    have hPβ : Pv S (η0 + W * β) ≤ β := by rw [hP, h, hβeq]
    exact absurd (csInf_le' hPβ : Zu S η0 W ≤ β) (not_le.2 hβ)
  obtain ⟨hG, hfix, hri, hGF, hinv⟩ := nn_GG_exact hcβ0 hna
  rw [hP, iota_of_fix hP hfix, nnGG hX hS _ hri (hP ▸ nn_Pv_lt S _) hG hGF, hinv]
  have hlg : lg (c0 + β) = lg β := cpExp_add c0 hβ0
  rw [hlg]

/-- **The end of a `W`-segment**: `ρ = P(η₀ + W·Zu(η₀, W))` is a fixed point of `GG`, and
`ρ² + ρ ≤ O(ι(η₀ + W·Zu(η₀, W)))`. -/
theorem nnPhiW (hX : NnLin X) (hS : NnSq X) {η0 c0 : Ordinal.{0}} (hg : Bt.Good S η0) (hd : W ∣ η0)
    (h0 : Pv S η0 = GG c0) :
    GG (Pv S (η0 + W * Zu S η0 W)) = Pv S (η0 + W * Zu S η0 W) ∧
      Pv S (η0 + W * Zu S η0 W) * Pv S (η0 + W * Zu S η0 W) + Pv S (η0 + W * Zu S η0 W) ≤
        xtOrec X (iota S (η0 + W * Zu S η0 W)) := by
  set Z := Zu S η0 W with hZ
  have hP := seg_GG hg hd h0 Z le_rfl
  have hfixZ : Pv S (η0 + W * Z) = Z := Zu_fix S η0 W
  have hZpos : 0 < Z := by
    rw [← hfixZ]
    exact lt_of_lt_of_le (upsPt_upsilon one_pos).1 (by rw [← Pv_zero S]; exact Pv_mono zero_le)
  have hGZ : GG (c0 + Z) = Z := hP.symm.trans hfixZ
  have hc0Z : c0 + Z = Z := by
    have hle : c0 + Z ≤ Z := by
      calc c0 + Z ≤ GG (c0 + Z) := GG_strictMono.id_le _
        _ = Z := hGZ
    exact le_antisymm hle le_add_self
  have hGF : GG Z = Z := by have := hGZ; rwa [hc0Z] at this
  have hfix : upsilon Z = Z := nn_gp_fix (by rw [← hGF]; exact isGP_GG hZpos)
  rw [hfixZ, iota_of_fix hfixZ hfix]
  exact ⟨hGF, nnPhi hX hS (ri_of_fp hZpos hfix) (hfixZ ▸ nn_Pv_lt S _) hGF⟩

end Googology.Trans.PoR.InaccPsi.R2.Nn

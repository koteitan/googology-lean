import Googology.Trans.PoR.InaccPsi.R2.SkFXRegB
import Googology.Trans.PoR.InaccPsi.R2.TeCode
import Googology.Trans.PoR.InaccPsi.R2.ShNu
import Googology.Trans.PoR.InaccPsi.R2.GcFrM
import Googology.Trans.PoR.InaccPsi.R2.PpIdx

/-!
# Wj: the exact split of the range restarts of the frontier part by the windows `[L(k), L(k+1))`

`L(ξ) = P(b_ξ)` with the name base `b_ξ = Ω_ω + P′·ξ`.  For a range restart `λ` (`CdRange S λ`):

* `υ_λ < L(ξ) ⇔ η_λ < b_ξ` (`wjLt_L_iff`), and `υ_λ` is never an `L(k)` or `L(ω)` (`wjRange_iff`);
* above `L(0)` every name is `Ω_ω + β` with `0 < β < P′·(ω+1) < Ω₂`, so its last exponent is `< Ω₂`
  (`wjExp_lt`) and its code is the offset code `-1 + e(η_λ)`; hence a name with `e(η_λ) ≥ Ω₂` has
  `υ_λ < L(0)` (`wjExpHi_low`): the region "`e ≥ Ω₂` above `L(0)`" is EMPTY;
* the needed restarts are exactly the disjoint union of: region (A) (below a frontier `ι(Γ(B)·ω)`,
  `B < Γ(1)`), (B-lo) `υ_λ < L(0)`, `e < Ω₂`, `λ < ι(Ω₂)`, past (A), (B-hi) the same with `ι(Ω₂) ≤ λ`,
  (C) `υ_λ < L(0)`, `e ≥ Ω₂`, the windows (W_k) `L(k) < υ_λ < L(k+1)`, `k < ω`, and (W_ω)
  `L(ω) < υ_λ < L(ω+1)` (`wjSplit`, `wjSplit_disj`, `wjAbove`); every window lies past (A) and has `e < Ω₂`;
* every window `W_k` contains range restarts (`wjWin_nonempty`); a piece holding `ν_C` fails LOWER there
  (`wjUV_ne_nuC`).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2

variable {S : InaccSeq.{0}}

/-- The name base of the window `ξ`: `b_ξ = Ω_ω + P′·ξ`, so `L(ξ) = P(b_ξ)`. -/
noncomputable def wjBase (S : InaccSeq.{0}) (ξ : Ordinal.{0}) : Ordinal.{0} := Om ω + Nc.ncPp S * ξ

theorem wjL_eq (ξ : Ordinal.{0}) : Nc.ncL S ξ = Nm.Pv S (wjBase S ξ) := Lw.lw_L_eq S ξ

/-- The name of a restart below `L(ω+1)`. -/
theorem wjEta_spec {l : Ordinal.{0}} (hl0 : l ≠ 0) (hlt : upsilon l < Nc.ncL S (ω + 1)) :
    Bt.Good S (Cd.cdEta S l) ∧ Bt.iota S (Cd.cdEta S l) = l ∧ Nm.Pv S (Cd.cdEta S l) = upsilon l := by
  obtain ⟨hg, hι, -, hpv⟩ := Cd.cdEta_pv_spec (S := S) hl0 (hlt.trans_eq (wjL_eq _))
  exact ⟨hg, hι, hpv⟩

/-- **`υ_λ < L(ξ) ⇔ η_λ < b_ξ`.** -/
theorem wjLt_L_iff {l : Ordinal.{0}} (hl0 : l ≠ 0) (hlt : upsilon l < Nc.ncL S (ω + 1)) (ξ : Ordinal.{0}) :
    upsilon l < Nc.ncL S ξ ↔ Cd.cdEta S l < wjBase S ξ := by
  obtain ⟨hg, hι, hpv⟩ := wjEta_spec hl0 hlt
  constructor
  · intro h
    by_contra hge
    push Not at hge
    have h1 := Nm.Pv_mono (S := S) hge
    rw [hpv, ← wjL_eq] at h1
    exact absurd h (not_lt.2 h1)
  · intro h
    have h1 : Bt.iota S (Cd.cdEta S l) < Bt.iota S (wjBase S ξ) := Cd.cd_iota_lt_of_good hg h
    have h2 := upsilon_normal.strictMono h1
    rw [hι] at h2
    rw [wjL_eq, Fx.fx_Pv_eq]
    exact h2

theorem wjLe_L_iff {l : Ordinal.{0}} (hl0 : l ≠ 0) (hlt : upsilon l < Nc.ncL S (ω + 1)) (ξ : Ordinal.{0}) :
    Nc.ncL S ξ ≤ upsilon l ↔ wjBase S ξ ≤ Cd.cdEta S l := by
  rw [← not_lt, ← not_lt, wjLt_L_iff hl0 hlt]

/-- **The range restarts are exactly the restarts `≥ B₀` below `L(ω+1)` off the points `L(k)`, `L(ω)`.** -/
theorem wjRange_iff {l : Ordinal.{0}} : Cd.CdRange S l ↔
    IsRestartIdx l ∧ Cd.cdB0 ≤ l ∧ upsilon l < Nc.ncL S (ω + 1) ∧
      (∀ k : ℕ, upsilon l ≠ Nc.ncL S (k : Ordinal.{0})) ∧ upsilon l ≠ Nc.ncL S ω := by
  constructor
  · rintro ⟨hl, hB, hlt, hc⟩
    have hiff := Te.teCode_hi_iff (S := S) hl.1 hlt
    refine ⟨hl, hB, hlt, fun k hk => ?_, fun hk => ?_⟩
    · exact absurd (hiff.2 (Or.inl ⟨k, hk⟩)) (not_le.2 hc)
    · exact absurd (hiff.2 (Or.inr hk)) (not_le.2 hc)
  · rintro ⟨hl, hB, hlt, hk, hw⟩
    refine ⟨hl, hB, hlt, not_le.1 fun hP => ?_⟩
    rcases (Te.teCode_hi_iff (S := S) hl.1 hlt).1 hP with ⟨k, h⟩ | h
    · exact hk k h
    · exact hw h

theorem wjOm2_inE : InE (Om (1 + 1 : Ordinal.{0})) := Low.opow_eq_self_of_SC Gg.gg_SC_Om2

theorem wjPp_lt_Om2 : Nc.ncPp S < Om (1 + 1) := psi_lt (InR_Om_succ 1) _

/-- `P′·(ω+1) < Ω₂`. -/
theorem wjPpw1_lt_Om2 : Nc.ncPp S * (ω + 1) < Om (1 + 1) := by
  have hE := wjOm2_inE
  have hw : ω < Om (1 + 1 : Ordinal.{0}) := omega0_lt_inE hE
  have h1 : (1 : Ordinal.{0}) < Om (1 + 1) := one_lt_omega0.trans hw
  exact InE.mul_lt hE wjPp_lt_Om2 ((inE_indec hE).add_lt hw h1)

theorem wjOm2_dvd_Omw : Om (1 + 1 : Ordinal.{0}) ∣ Om ω := by
  have hWE : ω ^ Om ω = Om ω := Low.opow_eq_self_of_SC (SC_Om omega0_ne_zero)
  have h12 : (1 + 1 : Ordinal.{0}) ≤ ω := by
    rw [one_add_one_eq_two]; exact (natCast_lt_omega0 2).le
  have h := opow_dvd_opow ω (Om_le_Om.2 h12)
  rwa [wjOm2_inE, hWE] at h

/-- **Above `L(0)` the last exponent of the name is below `Ω₂`.** -/
theorem wjExp_lt {l : Ordinal.{0}} (hl0 : l ≠ 0) (hlt : upsilon l < Nc.ncL S (ω + 1))
    (h0 : Nc.ncL S 0 < upsilon l) : Cd.cdExp (Cd.cdEta S l) < Om (1 + 1) := by
  obtain ⟨-, -, hpv⟩ := wjEta_spec hl0 hlt
  have hb0 : wjBase S 0 = Om ω := by simp [wjBase]
  have hge : Om ω ≤ Cd.cdEta S l := hb0 ▸ (wjLe_L_iff hl0 hlt 0).1 h0.le
  have hne : Cd.cdEta S l ≠ Om ω := by
    intro he
    rw [he, ← hb0, ← wjL_eq] at hpv
    exact absurd hpv (ne_of_lt h0)
  have hlt' : Cd.cdEta S l < wjBase S (ω + 1) := (wjLt_L_iff hl0 hlt _).1 hlt
  have hηβ : Om ω + (Cd.cdEta S l - Om ω) = Cd.cdEta S l := Ordinal.add_sub_cancel_of_le hge
  set β := Cd.cdEta S l - Om ω with hβ
  have hβ0 : β ≠ 0 := by
    intro h; rw [h, add_zero] at hηβ; exact hne hηβ.symm
  have hβlt : β < Nc.ncPp S * (ω + 1) := by
    have : Om ω + β < Om ω + Nc.ncPp S * (ω + 1) := by rw [hηβ]; exact hlt'
    exact (add_lt_add_iff_left _).1 this
  have hβ2 : β < Om (1 + 1) := hβlt.trans wjPpw1_lt_Om2
  have hη0 : Cd.cdEta S l ≠ 0 := by
    intro h; rw [h] at hge; exact absurd (Om_pos omega0_ne_zero) (not_lt.2 hge)
  by_contra hge2
  push Not at hge2
  have hd : Om (1 + 1 : Ordinal.{0}) ∣ Cd.cdEta S l := by
    have h1 : ω ^ Om (1 + 1 : Ordinal.{0}) ∣ ω ^ Cd.cdExp (Cd.cdEta S l) := opow_dvd_opow _ hge2
    rw [wjOm2_inE] at h1
    exact h1.trans (Cd.cdExp_dvd hη0)
  rw [← hηβ] at hd
  have hdβ := (Ordinal.dvd_add_iff wjOm2_dvd_Omw).1 hd
  exact absurd (Ordinal.le_of_dvd hβ0 hdβ) (not_le.2 hβ2)

/-- Above `L(0)` the code is the offset code `-1 + e(η_λ)`. -/
theorem wjCode_off {l : Ordinal.{0}} (hl0 : l ≠ 0) (hlt : upsilon l < Nc.ncL S (ω + 1))
    (h0 : Nc.ncL S 0 < upsilon l) : Cd.cdCode S l = Cd.cdOff (Cd.cdExp (Cd.cdEta S l)) := by
  show Cd.cdCodeOf S (Cd.cdEta S l) = _
  unfold Cd.cdCodeOf
  rw [if_pos (wjExp_lt hl0 hlt h0)]

/-- **A range restart whose name has last exponent `≥ Ω₂` lies below `L(0)`.** -/
theorem wjExpHi_low {l : Ordinal.{0}} (hr : Cd.CdRange S l) (he : Om (1 + 1) ≤ Cd.cdExp (Cd.cdEta S l)) :
    upsilon l < Nc.ncL S 0 := by
  obtain ⟨hl, -, hlt, hk, -⟩ := wjRange_iff.1 hr
  by_contra h
  push Not at h
  have h0 : Nc.ncL S 0 < upsilon l := lt_of_le_of_ne h (fun e => hk 0 (by simpa using e.symm))
  exact absurd he (not_le.2 (wjExp_lt hl.1 hlt h0))

/-- A name with last exponent `≥ Ω₂` is `≥ Ω₂`, so `ι(Ω₂) ≤ λ`. -/
theorem wjExpHi_iota {l : Ordinal.{0}} (hr : Cd.CdRange S l) (he : Om (1 + 1) ≤ Cd.cdExp (Cd.cdEta S l)) :
    Bt.iota S (Om (1 + 1)) ≤ l := by
  obtain ⟨hl, -, hlt, -⟩ := hr
  obtain ⟨-, hι, -⟩ := wjEta_spec hl.1 hlt
  have hη0 : Cd.cdEta S l ≠ 0 := by
    intro h
    rw [h, Bt.iota_zero] at hι
    have h1 : ω ^ 2 ≤ (1 : Ordinal.{0}) := Ordinal.le_of_dvd one_ne_zero (hι ▸ hl.2)
    exact absurd h1 (not_le.2 (one_lt_omega0.trans_le (by rw [pow_two]; exact Ordinal.le_mul_left ω omega0_pos)))
  have h1 : Om (1 + 1 : Ordinal.{0}) ≤ Cd.cdEta S l := by
    have h2 : ω ^ Om (1 + 1 : Ordinal.{0}) ∣ Cd.cdEta S l :=
      (opow_dvd_opow _ he).trans (Cd.cdExp_dvd hη0)
    rw [wjOm2_inE] at h2
    exact Ordinal.le_of_dvd hη0 h2
  rw [← hι]
  exact Bt.iota_mono (S := S) _ _ h1

/-! ## The windows and the pieces -/

/-- The window `k`: `L(k) < υ_λ < L(k+1)`. -/
def WjWin (S : InaccSeq.{0}) (k : ℕ) (l : Ordinal.{0}) : Prop :=
  Nc.ncL S (k : Ordinal.{0}) < upsilon l ∧ upsilon l < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})

/-- The top window: `L(ω) < υ_λ < L(ω+1)`. -/
def WjTop (S : InaccSeq.{0}) (l : Ordinal.{0}) : Prop :=
  Nc.ncL S ω < upsilon l ∧ upsilon l < Nc.ncL S (ω + 1)

/-- Past region (A): past every frontier `ι(Γ(B)·ω)`, `B < Γ(1)`. -/
def WjNotA (S : InaccSeq.{0}) (l : Ordinal.{0}) : Prop :=
  ∀ B, B < Gc.gcG 1 → Bt.iota S (Gc.gcG B * ω) ≤ l

/-- **Cover**: a range restart is below `L(0)`, in a window `W_k`, or in the top window. -/
theorem wjCover {l : Ordinal.{0}} (hr : Cd.CdRange S l) :
    upsilon l < Nc.ncL S 0 ∨ (∃ k : ℕ, WjWin S k l) ∨ WjTop S l := by
  obtain ⟨hl, -, hlt, hk, hw⟩ := wjRange_iff.1 hr
  by_cases hω : upsilon l < Nc.ncL S ω
  · have hex : ∃ n : ℕ, upsilon l < Nc.ncL S (n : Ordinal.{0}) := by
      have hη := (wjLt_L_iff hl.1 hlt ω).1 hω
      by_cases h0 : Cd.cdEta S l < Om ω
      · exact ⟨0, (wjLt_L_iff hl.1 hlt _).2 (by simpa [wjBase] using h0)⟩
      · push Not at h0
        have hηβ := Ordinal.add_sub_cancel_of_le h0
        have hβ : Cd.cdEta S l - Om ω < Nc.ncPp S * ω := by
          have : Om ω + (Cd.cdEta S l - Om ω) < Om ω + Nc.ncPp S * ω := by rw [hηβ]; exact hη
          exact (add_lt_add_iff_left _).1 this
        obtain ⟨c, hc, hβc⟩ := (Ordinal.lt_mul_iff_of_isSuccLimit isSuccLimit_omega0).1 hβ
        obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.1 hc
        refine ⟨n, (wjLt_L_iff hl.1 hlt _).2 ?_⟩
        show _ < Om ω + _
        rw [← hηβ]
        exact (add_lt_add_iff_left _).2 hβc
    classical
    rcases hn : Nat.find hex with _ | k
    · left
      have := Nat.find_spec hex
      rw [hn] at this
      simpa using this
    · right; left
      refine ⟨k, ?_, ?_⟩
      · have hnot := Nat.find_min hex (show k < Nat.find hex by omega)
        exact lt_of_le_of_ne (not_lt.1 hnot) (fun e => hk k e.symm)
      · have := Nat.find_spec hex
        rw [hn] at this
        exact this
  · right; right
    exact ⟨lt_of_le_of_ne (not_lt.1 hω) (fun e => hw e.symm), hlt⟩

/-- **Disjointness** of the pieces `υ < L(0)`, `W_k`, top. -/
theorem wjWin_disj :
    (∀ l (k : ℕ), upsilon l < Nc.ncL S 0 → ¬ WjWin S k l) ∧
    (∀ l (k j : ℕ), WjWin S k l → WjWin S j l → k = j) ∧
    (∀ l (k : ℕ), WjWin S k l → ¬ WjTop S l) ∧
    (∀ l, upsilon l < Nc.ncL S 0 → ¬ WjTop S l) := by
  have hmono := fun {a b : Ordinal.{0}} (h : a ≤ b) => Pp.ppL_mono (S := S) h
  refine ⟨fun l k h0 hw => ?_, fun l k j hk hj => ?_, fun l k hk ht => ?_, fun l h0 ht => ?_⟩
  · exact absurd (hw.1.trans h0) (not_lt.2 (hmono zero_le))
  · by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have : ((k + 1 : ℕ) : Ordinal.{0}) ≤ (j : Ordinal.{0}) := by exact_mod_cast h
      exact absurd (hj.1.trans hk.2) (not_lt.2 (hmono this))
    · have : ((j + 1 : ℕ) : Ordinal.{0}) ≤ (k : Ordinal.{0}) := by exact_mod_cast h
      exact absurd (hk.1.trans hj.2) (not_lt.2 (hmono this))
  · exact absurd (ht.1.trans hk.2) (not_lt.2 (hmono (natCast_lt_omega0 _).le))
  · exact absurd (ht.1.trans h0) (not_lt.2 (hmono zero_le))

/-- `Γ(B)·ω < Ω₂` gives `ι(Γ(B)·ω) ≤ ι(Ω₂)`. -/
theorem wjFrA_le_Om2 {B : Ordinal.{0}} (hB : B < Gc.gcG 1) :
    Bt.iota S (Gc.gcG B * ω) ≤ Bt.iota S (Om (1 + 1)) :=
  Bt.iota_mono (S := S) _ _ (R2Skel.SkFX.skfxG_lt_Om2 hB).le

/-- **Everything from `L(0)` on lies past region (A).** -/
theorem wjNotA_of_L0 {l : Ordinal.{0}} (h : Nc.ncL S 0 ≤ upsilon l) : WjNotA S l := by
  intro B hB
  by_contra hno
  push Not at hno
  have h1 : upsilon l ≤ upsilon (Bt.iota S (Gc.gcG B * ω)) := Bt.ups_mono hno.le
  rw [← Fx.fx_Pv_eq] at h1
  exact absurd (h1.trans_lt (Ga.ga_Pv_lt_L0 S (R2Skel.SkFX.skfxG_lt_Om2 hB).le)) (not_lt.2 h)

/-- **Region (C)**: `ι(Ω₂) ≤ λ`, past region (A), `υ_λ < L(0)`, code `π_η`. -/
theorem wjC_props {l : Ordinal.{0}} (hr : Cd.CdRange S l) (he : Om (1 + 1) ≤ Cd.cdExp (Cd.cdEta S l)) :
    WjNotA S l ∧ Bt.iota S (Om (1 + 1)) ≤ l ∧ upsilon l < Nc.ncL S 0 ∧
      Cd.cdCode S l = Cd.cdPi S (Cd.cdEta S l) := by
  have hι := wjExpHi_iota hr he
  refine ⟨fun B hB => (wjFrA_le_Om2 hB).trans hι, hι, wjExpHi_low hr he, ?_⟩
  show Cd.cdCodeOf S (Cd.cdEta S l) = _
  unfold Cd.cdCodeOf
  rw [if_neg (not_lt.2 he)]

/-- **The windows**: past region (A), last exponent `< Ω₂`, offset code. -/
theorem wjWin_props {l : Ordinal.{0}} (hr : Cd.CdRange S l) (hw : (∃ k : ℕ, WjWin S k l) ∨ WjTop S l) :
    WjNotA S l ∧ Cd.cdExp (Cd.cdEta S l) < Om (1 + 1) ∧
      Cd.cdCode S l = Cd.cdOff (Cd.cdExp (Cd.cdEta S l)) := by
  obtain ⟨hl, -, hlt, -⟩ := hr
  have h0 : Nc.ncL S 0 < upsilon l := by
    rcases hw with ⟨k, hk⟩ | ht
    · exact (Pp.ppL_mono (S := S) zero_le).trans_lt hk.1
    · exact (Pp.ppL_mono (S := S) zero_le).trans_lt ht.1
  exact ⟨wjNotA_of_L0 h0.le, wjExp_lt hl.1 hlt h0, wjCode_off hl.1 hlt h0⟩

/-- **THE SPLIT**: every range restart is in exactly one of (A), (B-lo), (B-hi), (C), `W_k`, `W_ω`
(exclusivity: `wjSplit_excl`). -/
theorem wjSplit {l : Ordinal.{0}} (hr : Cd.CdRange S l) :
    (∃ B, B < Gc.gcG 1 ∧ l < Bt.iota S (Gc.gcG B * ω)) ∨
    (WjNotA S l ∧ upsilon l < Nc.ncL S 0 ∧ Cd.cdExp (Cd.cdEta S l) < Om (1 + 1) ∧
      l < Bt.iota S (Om (1 + 1))) ∨
    (WjNotA S l ∧ upsilon l < Nc.ncL S 0 ∧ Cd.cdExp (Cd.cdEta S l) < Om (1 + 1) ∧
      Bt.iota S (Om (1 + 1)) ≤ l) ∨
    (upsilon l < Nc.ncL S 0 ∧ Om (1 + 1) ≤ Cd.cdExp (Cd.cdEta S l)) ∨
    (∃ k : ℕ, WjWin S k l) ∨ WjTop S l := by
  rcases wjCover hr with h0 | hw | ht
  · by_cases hA : ∃ B, B < Gc.gcG 1 ∧ l < Bt.iota S (Gc.gcG B * ω)
    · exact Or.inl hA
    have hNA : WjNotA S l := fun B hB => by
      by_contra h; exact hA ⟨B, hB, not_le.1 h⟩
    rcases lt_or_ge (Cd.cdExp (Cd.cdEta S l)) (Om (1 + 1)) with he | he
    · rcases lt_or_ge l (Bt.iota S (Om (1 + 1))) with hι | hι
      · exact Or.inr (Or.inl ⟨hNA, h0, he, hι⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨hNA, h0, he, hι⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h0, he⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hw))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ht))))

/-- **Exclusivity** of (A) against the rest, and of (B-lo), (B-hi), (C) against each other and the windows. -/
theorem wjSplit_excl {l : Ordinal.{0}} (hr : Cd.CdRange S l) :
    ((∃ B, B < Gc.gcG 1 ∧ l < Bt.iota S (Gc.gcG B * ω)) → ¬ WjNotA S l) ∧
    (Om (1 + 1) ≤ Cd.cdExp (Cd.cdEta S l) → WjNotA S l) ∧
    (((∃ k : ℕ, WjWin S k l) ∨ WjTop S l) → WjNotA S l ∧ Nc.ncL S 0 < upsilon l ∧
      Cd.cdExp (Cd.cdEta S l) < Om (1 + 1)) := by
  refine ⟨fun ⟨B, hB, hl⟩ hN => absurd (hN B hB) (not_le.2 hl), fun he => (wjC_props hr he).1,
    fun hw => ⟨(wjWin_props hr hw).1, ?_, (wjWin_props hr hw).2.1⟩⟩
  rcases hw with ⟨k, hk⟩ | ht
  · exact (Pp.ppL_mono (S := S) zero_le).trans_lt hk.1
  · exact (Pp.ppL_mono (S := S) zero_le).trans_lt ht.1

/-- **The reduction**: the six pieces give the property at every range restart. -/
theorem wjAbove (P : Ordinal.{0} → Prop)
    (hA : ∀ l, Cd.CdRange S l → (∃ B, B < Gc.gcG 1 ∧ l < Bt.iota S (Gc.gcG B * ω)) → P l)
    (hBlo : ∀ l, Cd.CdRange S l → WjNotA S l → upsilon l < Nc.ncL S 0 →
      Cd.cdExp (Cd.cdEta S l) < Om (1 + 1) → l < Bt.iota S (Om (1 + 1)) → P l)
    (hBhi : ∀ l, Cd.CdRange S l → WjNotA S l → upsilon l < Nc.ncL S 0 →
      Cd.cdExp (Cd.cdEta S l) < Om (1 + 1) → Bt.iota S (Om (1 + 1)) ≤ l → P l)
    (hC : ∀ l, Cd.CdRange S l → Om (1 + 1) ≤ Cd.cdExp (Cd.cdEta S l) → upsilon l < Nc.ncL S 0 → P l)
    (hW : ∀ k : ℕ, ∀ l, Cd.CdRange S l → WjWin S k l → P l)
    (hT : ∀ l, Cd.CdRange S l → WjTop S l → P l) :
    ∀ l, Cd.CdRange S l → P l := by
  intro l hr
  rcases wjSplit hr with h | h | h | h | ⟨k, h⟩ | h
  · exact hA l hr h
  · exact hBlo l hr h.1 h.2.1 h.2.2.1 h.2.2.2
  · exact hBhi l hr h.1 h.2.1 h.2.2.1 h.2.2.2
  · exact hC l hr h.2 h.1
  · exact hW k l hr h
  · exact hT l hr h

/-- **The old region (B) (`R2Skel.SkF.skRegB`) is exactly (B-lo) ∧ (B-hi) ∧ every window ∧ the top window.** -/
theorem wjRegB_iff (P : Ordinal.{0} → Prop) :
    (∀ l, Cd.CdRange S l → WjNotA S l → Cd.cdExp (Cd.cdEta S l) < Om (1 + 1) → P l) ↔
    ((∀ l, Cd.CdRange S l → WjNotA S l → upsilon l < Nc.ncL S 0 →
        Cd.cdExp (Cd.cdEta S l) < Om (1 + 1) → l < Bt.iota S (Om (1 + 1)) → P l) ∧
      (∀ l, Cd.CdRange S l → WjNotA S l → upsilon l < Nc.ncL S 0 →
        Cd.cdExp (Cd.cdEta S l) < Om (1 + 1) → Bt.iota S (Om (1 + 1)) ≤ l → P l) ∧
      (∀ k : ℕ, ∀ l, Cd.CdRange S l → WjWin S k l → P l) ∧
      (∀ l, Cd.CdRange S l → WjTop S l → P l)) := by
  constructor
  · intro h
    refine ⟨fun l hr hN _ he _ => h l hr hN he, fun l hr hN _ he _ => h l hr hN he,
      fun k l hr hw => ?_, fun l hr ht => ?_⟩
    · obtain ⟨hN, he, -⟩ := wjWin_props hr (Or.inl ⟨k, hw⟩); exact h l hr hN he
    · obtain ⟨hN, he, -⟩ := wjWin_props hr (Or.inr ht); exact h l hr hN he
  · rintro ⟨hlo, hhi, hW, hT⟩ l hr hN he
    rcases wjCover hr with h0 | ⟨k, hw⟩ | ht
    · rcases lt_or_ge l (Bt.iota S (Om (1 + 1))) with hι | hι
      · exact hlo l hr hN h0 he hι
      · exact hhi l hr hN h0 he hι
    · exact hW k l hr hw
    · exact hT l hr ht

/-- **The old region (C) (`R2Skel.SkF.skRegC`) is exactly its part below `L(0)` (`skLongPre`).** -/
theorem wjRegC_iff (P : Ordinal.{0} → Prop) :
    (∀ l, Cd.CdRange S l → Om (1 + 1) ≤ Cd.cdExp (Cd.cdEta S l) → P l) ↔
    (∀ l, Cd.CdRange S l → Om (1 + 1) ≤ Cd.cdExp (Cd.cdEta S l) → upsilon l < Nc.ncL S 0 → P l) :=
  ⟨fun h l hr he _ => h l hr he, fun h l hr he => h l hr he (wjExpHi_low hr he)⟩

/-- **`skLongMid` is vacuous**: no range restart with `e(η) ≥ Ω₂` has `L(0) ≤ υ_λ`. -/
theorem wjLongMid (P : Ordinal.{0} → Prop) : ∀ l, Cd.CdRange S l → Om (1 + 1) ≤ Cd.cdExp (Cd.cdEta S l) →
    Nc.ncL S 0 ≤ upsilon l → upsilon l ≤ Nc.ncL S ω → P l :=
  fun _ hr he h0 _ => absurd (wjExpHi_low hr he) (not_lt.2 h0)

/-- **`skLongTop` is vacuous.** -/
theorem wjLongTop (P : Ordinal.{0} → Prop) : ∀ l, Cd.CdRange S l → Om (1 + 1) ≤ Cd.cdExp (Cd.cdEta S l) →
    Nc.ncL S ω < upsilon l → P l :=
  fun _ hr he hw => absurd (wjExpHi_low hr he)
    (not_lt.2 ((Pp.ppL_mono (S := S) zero_le).trans hw.le))

/-- **Non-vacuity: every window `W_k` contains range restarts** (above any `γ < L(k+1)`). -/
theorem wjWin_nonempty (k : ℕ) : ∃ l, Cd.CdRange S l ∧ WjWin S k l := by
  have hlt : Nc.ncL S (k : Ordinal.{0}) < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) := by
    rcases k with _ | m
    · simpa using Rl.rlM_lt_L1 (S := S)
    · exact Pp.ppL_lt_succ (S := S) m
  obtain ⟨μ, hr, hγ, hμ, -⟩ := Ls.lsNames_L (S := S) k 0 _ hlt
  exact ⟨μ, hr, hγ, hμ⟩

/-- A restart where LOWER holds is not `ν_C` (`Sh.shNotLower`): each piece is as strong as "`ν_C` is not
in the piece". -/
theorem wjUV_ne_nuC {l : Ordinal.{0}} (h : Cd.CdLower S l) : upsilon l ≠ nuC :=
  fun e => Sh.shNotLower (S := S) e h

end Googology.Trans.PoR.InaccPsi.R2.Wj

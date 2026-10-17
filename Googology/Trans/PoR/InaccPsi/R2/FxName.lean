import Googology.Trans.PoR.InaccPsi.R2.FxPlat
import Googology.Trans.PoR.InaccPsi.R2.CpRoad

/-!
# The name of a fixed point of `υ`: `e(η_F) ≥ F`, so `F ≤ m_F`

`P(η) = ψ_{Ω₁}(Ω_ω + θ·η)` (`Nm.Pv`), `ι` the index of Theorem GEN (`υ_{ι(η)} = P(η)`), `η_λ` the good name
of a restart index (`Cd.cdEta`), `e(η)` the last exponent (`Cd.cdExp`), `m_λ` the code (`Cd.cdCode`).

* `fx_iota_add_le` (**the index grows at most by the distance**): `ι(η₀ + y) ≤ ι(η₀) + y`;
* `fxExp_fix` (**the name lemma**): at a restart index `F = υ_F` with a name (`ρ_F < P(η*)`),
  `F ≤ e(η_F)`.  Write `η_F = η₀ + ω^e`.  If `ω^e < F`: either `ι(η₀) < F`, and then
  `F = ι(η_F) ≤ ι(η₀) + ω^e < F` (`F` is additive principal); or `ι(η₀) = F`, and then `η₀` is good (two
  good names with the same index are equal, impossible) or bad (then `η₀ + ω^e = η_F` is bad by the plateau
  `Fx.fxPlat`, impossible);
* `fxCode_fix`: then `F ≤ m_F` (`m_F = e` for `e < Ω₂`, else the π-code `> Ω₁`);
* `fxCODEfix` (**`Cp.CpCODEfix` holds**, so UPPER at the isolated fixed points below `cpB1` of the range is
  proved, `fxUPPER2`).

No new axiom, no new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Fx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Br Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp

variable {S : InaccSeq.{0}}

/-- **`ι(η₀ + y) ≤ ι(η₀) + y`.** -/
theorem fx_iota_add_le (η0 : Ordinal.{0}) : ∀ y, iota S (η0 + y) ≤ iota S η0 + y := by
  intro y
  induction y using Ordinal.limitRecOn with
  | zero => simp
  | add_one y ih =>
    rw [← add_assoc]
    calc iota S (η0 + y + 1) ≤ iota S (η0 + y) + 1 := (iota_succ_le _).2
      _ ≤ iota S η0 + y + 1 := add_le_add ih le_rfl
      _ = iota S η0 + (y + 1) := add_assoc _ _ _
  | limit y hy ih =>
    rw [iota_limit (isSuccLimit_add η0 hy)]
    refine ciSup_le' fun e => ?_
    rcases lt_or_ge e.1 η0 with h | h
    · exact (iota_mono η0 e.1 h.le).trans le_self_add
    · obtain ⟨c, hc⟩ := exists_add_of_le h
      have hcy : c < y := by
        have := e.2
        rw [hc] at this
        exact (add_lt_add_iff_left η0).1 this
      rw [hc]
      exact (ih c hcy).trans (add_le_add le_rfl hcy.le)

/-- A fixed point of `υ` with a name is countable. -/
theorem fx_fix_lt_Om1 {F ηx : Ordinal.{0}} (hfix : upsilon F = F) (hX : upsilon F < Pv S ηx) :
    F < Om 1 := by
  rw [← hfix]; exact hX.trans (Pv_lt_Om1 S ηx)

/-- **The name lemma**: `F ≤ e(η_F)` at a restart index `F = υ_F` with a name. -/
theorem fxExp_fix {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F)
    (hX : upsilon F < Pv S ηx) : F ≤ cdExp (cdEta S F) := by
  obtain ⟨hg, hι, -, -⟩ := cdEta_pv_spec (S := S) hF.1 hX
  obtain ⟨hE, hp, hww⟩ := cp_fix_facts hF hfix
  have hF1 : F < Om 1 := fx_fix_lt_Om1 hfix hX
  have h1F : (1 : Ordinal.{0}) < F :=
    lt_of_le_of_lt (Order.one_le_iff_pos.2 (mul_pos omega0_pos omega0_pos)) hww
  have hη0 : cdEta S F ≠ 0 := by
    intro h0
    rw [h0, iota_zero] at hι
    exact h1F.ne hι
  obtain ⟨η0, hdec, -⟩ := cdExp_decomp hη0
  by_contra hlt
  rw [not_le] at hlt
  have hζF : ω ^ cdExp (cdEta S F) < F :=
    calc ω ^ cdExp (cdEta S F) < ω ^ F := (opow_lt_opow_iff_right one_lt_omega0).2 hlt
      _ = F := hE
  have hι0 : iota S η0 ≤ F := by
    rw [← hι]; exact iota_mono _ _ (by rw [hdec]; exact le_self_add)
  rcases hι0.lt_or_eq with hlt0 | heq0
  · have h := fx_iota_add_le (S := S) η0 (ω ^ cdExp (cdEta S F))
    rw [← hdec, hι] at h
    exact absurd (h.trans_lt (hp hlt0 hζF)) (lt_irrefl _)
  · have hη0lt : η0 < cdEta S F := by
      rw [hdec]; exact lt_add_of_pos_right _ (opow_pos _ omega0_pos)
    by_cases hg0 : Bt.Good S η0
    · exact absurd (cd_good_inj hg0 hg (heq0.trans hι.symm)) hη0lt.ne
    · have h := (fxPlat hg0 (hζF.trans hF1)).2
      rw [← hdec] at h
      exact h hg

/-- **`F ≤ m_F`** at a restart index `F = υ_F` with a name. -/
theorem fxCode_fix {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F)
    (hX : upsilon F < Pv S ηx) : F ≤ cdCode S F := by
  have he := fxExp_fix hF hfix hX
  obtain ⟨-, -, hww⟩ := cp_fix_facts hF hfix
  have hωF : ω ≤ F := (le_mul_left _ omega0_pos).trans hww.le
  unfold cdCode cdCodeOf
  split_ifs with h
  · rw [cpOff_of_ge (hωF.trans he)]; exact he
  · exact ((fx_fix_lt_Om1 hfix hX).trans (psiS_bounds (S := S) _ 1).1).le

/-- **`Cp.CpCODEfix` holds.** -/
theorem fxCODEfix : CpCODEfix S := fun _ hr _ hfix _ =>
  fxCode_fix hr.1 hfix (cp_name_L hr.2.2.1)

/-- **UPPER on the range from UPPER at `λ ≥ cpB1` and at the fixed points of `υ` that are limits of fixed
points.** -/
theorem fxUPPER2 (hU : CpUPPERout2 S) : CdUPPER S := cpUPPER2 hU fxCODEfix

end Googology.Trans.PoR.InaccPsi.R2.Fx

import Googology.Trans.PoR.InaccPsi.R2.TyRng

/-!
# The realizer package of the long region without UPPER and LOWER

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.

`Tv.TvGen S λ β` (the package of `Tv.tvReal_gen`) asks UPPER at the inner restarts `λ+g` and, inside `SrCarry`,
LOWER at the supply images `μ + f(g)`.  At `υ_λ = L(k)` with `υ_{λ+β} ≤ L(k+1)` the inner restarts are Range
restarts with `RzRest` (`Ty.tyInner_rng`), and if the supply restarts `μ` are taken above a window `w` of `L(k)`
(`Ty.TyWin`) so are the images `μ + f(g)` (`Ty.tyWin_rng`): both are road hypotheses (`hU`, `hL`).  What is left
per block is exactly the three forms of the inner reaches and the supply with EQ (`TyGen`).

* `TyCarry` (**`Tv.TvCarry` without the LOWER clause**), `TyGen S λ β w` (**the forms and the supply above `w`**);
* `tyGen_tv` (**`hU`, `hL`, a window ⇒ (`TyGen ⇒ Tv.TvGen`)**), `tyGen_of_tv` (**`Tv.TvGen ⇒ TyGen`**);
* `TyVisGen`, `tyVis_iff` (**`Tv.TvVisGen ⇔ TyVisGen` at `L(k)` under `hU`, `hL`**);
* `tyRoad` (**the road of `Tv.tvRoadGen` from `TyVisGen` at `m*` (window `υ(Λ_B⁺)`) and at every `L(n+1)` (window
  `L(n)`)**).

No new axiom.  New definitions: `TyCarry`, `TyGen`, `TyVisGen` (statements).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ty

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **EQ for an offset map** (`Tv.TvCarry` without LOWER at `μ + f(g)`): the large reaches, the reaches
`υ_{λ+h} + c` carried to `υ_{μ+f(h)} + π_{υ_μ,υ_λ}(c)`, the low points carried by the segment move. -/
def TyCarry (S : InaccSeq.{0}) (l β μ : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) (B : Ordinal.{0})
    (Os : Finset Ordinal.{0}) : Prop :=
  (∀ g ∈ Os, 0 < g → ω ^ 2 ∣ g →
    (upsilon (l + β) ≤ cdR S (l + g) → upsilon (μ + B) ≤ cdR S (μ + f g)) ∧
    ∀ h ∈ Os, ∀ c : Ordinal.{0}, 0 < h → c < upsilon (succ l) →
      cdR S (l + g) = upsilon (l + h) + c →
      upsilon (μ + f h) + pi (upsilon μ) (upsilon l) c ≤ cdR S (μ + f g)) ∧
  ∀ g ∈ Os, 0 < g → ω ^ 2 ∣ g → ∀ h ∈ Os, 0 < h → Tv.TvLowAt S l g h →
    mv (upsilon (l + h)) (upsilon (μ + f h)) (cdR S (l + g)) ≤ cdR S (μ + f g)

/-- **The block package at `(λ, β)` above the window `w`**: the three forms of the inner reaches and, for every
`γ ∈ [w, υ_λ)` and finite offset set, a restart `μ` above `γ` with supply `υ_{μ+B} ≤ r(μ)`, an offset map and
`TyCarry`. -/
def TyGen (S : InaccSeq.{0}) (l β w : Ordinal.{0}) : Prop :=
  (∀ g, 0 < g → g < β → ω ^ 2 ∣ g → upsilon (l + β) ≤ cdR S (l + g) ∨
      (∃ h c, 0 < h ∧ h < β ∧ c < upsilon (succ l) ∧ cdR S (l + g) = upsilon (l + h) + c) ∨
      ∃ h, 0 < h ∧ h < β ∧ Tv.TvLowAt S l g h) ∧
  (∀ γ, w ≤ γ → γ < upsilon l → ∀ Os : Finset Ordinal.{0}, (∀ d ∈ Os, d < β) →
      ∃ μ f B, IsRestartIdx μ ∧ γ < upsilon μ ∧ upsilon μ < upsilon l ∧ μ + B ≤ l ∧ ω ^ 2 ∣ B ∧
        upsilon (μ + B) ≤ cdR S μ ∧ Sl.SlOff f Os B ∧ TyCarry S l β μ f B Os)

/-- **`Tv.TvGen` gives `TyGen`** (for any `w`): the new package is not stronger. -/
theorem tyGen_of_tv {l β w : Ordinal.{0}} (h : Tv.TvGen S l β) : TyGen S l β w := by
  refine ⟨h.2.1, fun γ _ hγ Os hOs => ?_⟩
  obtain ⟨μ, f, B, hr, h1, h2, h3, h4, h5, h6, hsr, hc2⟩ := h.2.2 γ hγ Os hOs
  exact ⟨μ, f, B, hr.1, h1, h2, h3, h4, h5, h6,
    fun g hg hg0 hgd => ⟨(hsr g hg hg0 hgd).2.1, (hsr g hg hg0 hgd).2.2⟩, hc2⟩

/-- **`TyGen` gives `Tv.TvGen` at `L(k)`** under UPPER and LOWER at the Range restarts with `RzRest`: the inner
restarts of `[L(k), υ_{λ+β})` and the supply images above the window are such restarts. -/
theorem tyGen_tv (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) {k : ℕ} {w l β : Ordinal.{0}} (hw : TyWin S k w)
    (hla : upsilon l = Nc.ncL S (k : Ordinal.{0}))
    (hβ : upsilon (l + β) ≤ Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (h : TyGen S l β w) : Tv.TvGen S l β := by
  have hm := upsilon_normal.strictMono
  have hlk : l = Nc.ncL S (k : Ordinal.{0}) := hm.injective (hla.trans (Te.teUps_L (S := S) k).symm)
  have hl : IsRestartIdx l := hlk ▸ Te.teRst_L (S := S) k
  -- every restart index strictly between `w` (in the sense `w < υ`) and `L(k)` is a Range restart with `RzRest`
  have hwin : ∀ ν, IsRestartIdx ν → w < upsilon ν → upsilon ν < upsilon l → CdRange S ν ∧ Rz.RzRest ν :=
    fun ν hν h1 h2 => tyWin_rng hw hν h1 (hla ▸ h2)
  refine ⟨fun g hg0 hgβ hgd => ?_, h.1, fun γ hγ Os hOs => ?_⟩
  · have hν : IsRestartIdx (l + g) :=
      ⟨(lt_of_lt_of_le (pos_iff_ne_zero.2 hl.1) le_self_add).ne', dvd_add hl.2 hgd⟩
    have h1 : Nc.ncL S (k : Ordinal.{0}) < upsilon (l + g) := hla ▸ hm (lt_add_of_pos_right l hg0)
    have h2 : upsilon (l + g) < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) :=
      (hm (add_lt_add_right hgβ l)).trans_le hβ
    obtain ⟨hr, hz⟩ := tyInner_rng hν h1 h2
    exact hU _ hr hz
  · have hwl : w < upsilon l := hla ▸ hw.2.1
    obtain ⟨μ, f, B, hμ, hγμ, hμl, hμB, hBd, hsupB, hoff, hc1, hc2⟩ :=
      h.2 (max γ w) (le_max_right _ _) (max_lt hγ hwl) Os hOs
    have hwμ : w < upsilon μ := (le_max_right γ w).trans_lt hγμ
    refine ⟨μ, f, B, (hwin μ hμ hwμ hμl).1, (le_max_left γ w).trans_lt hγμ, hμl, hμB, hBd, hsupB, hoff,
      fun g hg hg0 hgd => ⟨?_, (hc1 g hg hg0 hgd).1, (hc1 g hg hg0 hgd).2⟩, hc2⟩
    obtain ⟨q, hq⟩ := hgd
    have hν : IsRestartIdx (μ + f g) :=
      ⟨(lt_of_lt_of_le (pos_iff_ne_zero.2 hμ.1) le_self_add).ne', dvd_add hμ.2 (hq ▸ hoff.dvd q)⟩
    have h1 : w < upsilon (μ + f g) := hwμ.trans_le (hm.monotone le_self_add)
    have h2 : upsilon (μ + f g) < upsilon l :=
      hm ((add_lt_add_right (hoff.bd g hg) μ).trans_le hμB)
    obtain ⟨hr, hz⟩ := hwin _ hν h1 h2
    exact hL _ hr hz

/-- **At every isolated uncovered Range restart `ν` of `[c, b)` some `β` with `ρ_ν < υ_{λ+β} ≤ b` and
`TyGen S λ β w`.** -/
def TyVisGen (S : InaccSeq.{0}) (l b c w : Ordinal.{0}) : Prop :=
  ∀ ν, CdRange S ν → c ≤ upsilon ν → upsilon ν < b → upsilon l < upsilon ν → ¬ Tk.TkCov S (upsilon l) ν →
    Tk.TkIso S (upsilon l) ν → ∃ β, upsilon ν < upsilon (l + β) ∧ upsilon (l + β) ≤ b ∧ TyGen S l β w

/-- **`Tv.TvVisGen ⇔ TyVisGen` at `L(k)`** (`b ≤ L(k+1)`, `w` a window) under UPPER and LOWER at the Range restarts
with `RzRest`. -/
theorem tyVis_iff (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) {k : ℕ} {w l b c : Ordinal.{0}} (hw : TyWin S k w)
    (hla : upsilon l = Nc.ncL S (k : Ordinal.{0})) (hb : b ≤ Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) :
    Tv.TvVisGen S l b c ↔ TyVisGen S l b c w := by
  constructor
  · intro h ν h1 h2 h3 h4 h5 h6
    obtain ⟨β, hνβ, hβb, hG⟩ := h ν h1 h2 h3 h4 h5 h6
    exact ⟨β, hνβ, hβb, tyGen_of_tv hG⟩
  · intro h ν h1 h2 h3 h4 h5 h6
    obtain ⟨β, hνβ, hβb, hG⟩ := h ν h1 h2 h3 h4 h5 h6
    exact ⟨β, hνβ, hβb, tyGen_tv hU hL hw hla (hβb.trans hb) hG⟩

section Road

variable (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
  (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
  (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
  (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
  (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
  (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S) (hmove : Cx.CxStdMoveTop S)
include hU hO hL hV hVt hEQ htop hmove

/-- **The road from `TyVisGen` at `m*` (window `υ(Λ_B⁺)`) and at every `L(n+1)` (window `L(n)`)**: the conclusion
of `Tv.tvRoadGen` with neither UPPER at the inner restarts nor LOWER at the supply images asked per block. -/
theorem tyRoad
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      TyVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))) (upsilon Rz.rzLam))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      TyVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
        (Nc.ncL S (n : Ordinal.{0}))) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  refine Tv.tvRoadGen hU hO hL hV hVt hEQ htop hmove (fun l hl e => ?_) (fun n l hl e => ?_)
  · have hla : upsilon l = Nc.ncL S ((0 : ℕ) : Ordinal.{0}) := by rw [Nat.cast_zero]; exact e.symm
    have hb : Nc.ncL S 1 ≤ Nc.ncL S ((0 + 1 : ℕ) : Ordinal.{0}) := by simp
    exact (tyVis_iff hU hL tyWin_M hla hb).2 (h0 l hl e)
  · have hb : Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) ≤ Nc.ncL S ((n + 1 + 1 : ℕ) : Ordinal.{0}) := le_rfl
    exact (tyVis_iff hU hL (tyWin_L n) e.symm hb).2 (hn n l hl e)

end Road

end Googology.Trans.PoR.InaccPsi.R2.Ty

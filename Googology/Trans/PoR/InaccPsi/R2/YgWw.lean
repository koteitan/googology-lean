import Googology.Trans.PoR.InaccPsi.R2.YbSup
import Googology.Trans.PoR.InaccPsi.R2.XoTest

/-!
# Refute first: the moving-leaf carry at the gap witness `wwX = ϑ^{u₁}(Ω₁·B₂ + λ)`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`λ = L(k) = υ_λ`, `u₁ = υ_{λ+1}`, `W = Ww.wwX S k` (an `ε`-number in `(u₁, u₂)`, `Ww.wwX_spec`), `h_W = W + ω + 1`.
The reach is `r(λ+W) = υ_{λ+h_W} + W` (`Wu.wuR_X`).  Its moving-leaf decomposition is `E_W = sg h_W υ_{λ+h_W} +
th 1 (lc B₂) (lo λ)` (`Yb.ybWwXE` for the second summand).

* `ygWwE`, `ygWw_val`, `ygWw_WF` (**`E_W` is a well-formed moving-leaf form of `r(λ+W)`**), `ygWw_R` (**`E_W` is
  restricted at every `μ` with `0 < μ`, `υ_μ < υ_λ`**);
* `ygWwMu` (`W_μ = ϑ^{υ_{μ+f(1)}}(Ω₁·B₂ + υ_μ)`, the twin of `W` at `μ`), `ygWw_img` (**the image of `E_W` is
  `υ_{μ+f(h_W)} + W_μ`**), `ygCarry_ww` (**the carry at `W` asks `υ_{μ+f(h_W)} + W_μ ≤ r(μ+f(W))`**), `ygWw_obl`
  (**with the reach formula at `μ` the obligation is exactly `W_μ ≤ f(W)`**: no contradiction; the offset map sends
  `W` at least to its twin, as at `X′`, `Xo.xoXj_obl`).

No new axiom.  New definitions: `ygWwE` (a term), `ygWwMu` (one ordinal).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yg

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **The moving-leaf decomposition of `r(λ+W)`.** -/
noncomputable def ygWwE (S : InaccSeq.{0}) (k : ℕ) : Xo.XoE :=
  .add (.old (.sg (Ww.wwX S k + ω + 1) (upsilon (Nc.ncL S (k : Ordinal.{0}) + (Ww.wwX S k + ω + 1)))))
    (Yb.ybWwXE S k)

theorem ygWw_val (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) :
    Xo.xoVal S (Nc.ncL S (k : Ordinal.{0})) (ygWwE S k) = cdR S (Nc.ncL S (k : Ordinal.{0}) + Ww.wwX S k) := by
  obtain ⟨-, hXE, -, hXu2, -⟩ := Ww.wwX_spec (S := S) k
  rw [Wu.wuR_X k hν hXE hXu2]
  show upsilon (Nc.ncL S (k : Ordinal.{0}) + (Ww.wwX S k + ω + 1)) +
    Xo.xoVal S (Nc.ncL S (k : Ordinal.{0})) (Yb.ybWwXE S k) = _
  rw [Yb.ybWwXE_val]

/-- **`E_W` is well formed** (`W + ω + 1 < β`, `υ_{λ+β} ≤ Ω₁`). -/
theorem ygWw_WF (k : ℕ) {β : Ordinal.{0}} (hβ : Ww.wwX S k + ω + 1 < β)
    (hb1 : upsilon (Nc.ncL S (k : Ordinal.{0}) + β) ≤ Om1) :
    Xo.XoWF S (Nc.ncL S (k : Ordinal.{0})) β (ygWwE S k) := by
  obtain ⟨hl0, -, -, -, -, -, -, -, -⟩ := Vr.vr_facts (S := S) k
  obtain ⟨hP, hu1O, hlu1, -, -, -⟩ := Ww.ww_seg (S := S) k
  obtain ⟨hξT, hξ2, -, -⟩ := Ww.ww_arg (S := S) k
  obtain ⟨-, hXE, hu1X, hXu2, -⟩ := Ww.wwX_spec (S := S) k
  set l := Nc.ncL S (k : Ordinal.{0}) with hldef
  set X := Ww.wwX S k with hXdef
  have hm := upsilon_normal.strictMono
  set h1 := X + ω + 1 with hh1
  set τ := upsilon (l + h1) with hτdef
  have hτO : τ < Om1 := (hm ((add_lt_add_iff_left l).2 hβ)).trans_le hb1
  have hτP : UpsPt τ := upsPt_upsilon (hl0.trans_le le_self_add)
  have hlE : InE (upsilon l) := upsPt_inE (upsPt_upsilon hl0)
  have hlτ : upsilon l < τ := hm (lt_add_of_pos_right l (lt_of_le_of_lt zero_le (lt_add_one _)))
  have h1β : (1 : Ordinal.{0}) < β :=
    lt_of_le_of_lt ((one_le_iff_pos.2 (InE.pos hXE)).trans (le_self_add.trans le_self_add)) hβ
  have hll : l < upsilon (succ l) := by rw [succ_eq_add_one]; exact hlu1
  refine ⟨⟨lt_of_le_of_lt zero_le (lt_add_one _), hβ, le_rfl, hm (lt_succ _),
    Ww.ww_par_self hlE hlτ (upsPt_inE hτP) hτO⟩, ?_⟩
  refine ⟨zero_lt_one, h1β, trivial, hll, ?_⟩
  show l < Om1 ∧ Om1 * Uc.ucB + l ∈ Tset (upsilon (l + 1)) ∧ Om1 * Uc.ucB + l < OmTwo ∧
    upsilon (l + 1) ≤ vt (upsilon (l + 1)) (Om1 * Uc.ucB + l) ∧
    vt (upsilon (l + 1)) (Om1 * Uc.ucB + l) < upsilon (succ (l + 1))
  rw [Uf.uf_Om1_mul_B]
  refine ⟨hlu1.trans hu1O, hξT, hξ2, hu1X.le, ?_⟩
  rw [succ_eq_add_one, add_assoc, one_add_one_eq_two]; exact hXu2

/-- **`E_W` passes the restriction** at every `μ > 0` with `υ_μ < υ_λ`. -/
theorem ygWw_R (k : ℕ) {μ : Ordinal.{0}} (hμ0 : 0 < μ)
    (hμl : upsilon μ < upsilon (Nc.ncL S (k : Ordinal.{0})))
    (hτO : upsilon (Nc.ncL S (k : Ordinal.{0}) + (Ww.wwX S k + ω + 1)) < Om1) :
    Xo.XoR S (Nc.ncL S (k : Ordinal.{0})) μ (ygWwE S k) := by
  obtain ⟨hl0, -, -, -, -, -, -, -, -⟩ := Vr.vr_facts (S := S) k
  set l := Nc.ncL S (k : Ordinal.{0}) with hldef
  have hm := upsilon_normal.strictMono
  have hμE : InE (upsilon μ) := upsPt_inE (upsPt_upsilon hμ0)
  set τ := upsilon (l + (Ww.wwX S k + ω + 1)) with hτdef
  have hτE : InE τ := upsPt_inE (upsPt_upsilon (hl0.trans_le le_self_add))
  have hlτ : upsilon l < τ := hm (lt_add_of_pos_right l (lt_of_le_of_lt zero_le (lt_add_one _)))
  have hBτ : Bases (upsilon μ) τ := ⟨hμE, hτE, hμl.trans hlτ, hτO⟩
  exact ⟨fun p hp => (pi_base hBτ).1.2 (Finset.mem_coe.2 hp),
    ⟨Yb.yb_B_low S hμ0, Xo.xo_lo_R k hμ0 hμl⟩, fun h => h.1.elim⟩

/-- **The twin of `W` at `μ`**: `W_μ = ϑ^{υ_{μ+f(1)}}(Ω₁·B₂ + υ_μ)`. -/
noncomputable def ygWwMu (μ : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) : Ordinal.{0} :=
  vt (upsilon (μ + f 1)) (Om1 * Uc.ucB + upsilon μ)

/-- **The image of `E_W`**: `υ_{μ+f(h_W)} + W_μ` (the leaf `λ` goes to `π(λ) = υ_μ`, the constant `B₂` stays). -/
theorem ygWw_img (k : ℕ) {μ : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (hμ0 : 0 < μ)
    (hμl : upsilon μ < upsilon (Nc.ncL S (k : Ordinal.{0})))
    (hτO : upsilon (Nc.ncL S (k : Ordinal.{0}) + (Ww.wwX S k + ω + 1)) < Om1)
    (hτ'O : upsilon (μ + f (Ww.wwX S k + ω + 1)) < Om1) :
    Xo.xoImg S (Nc.ncL S (k : Ordinal.{0})) μ f (ygWwE S k) =
      upsilon (μ + f (Ww.wwX S k + ω + 1)) + ygWwMu μ f := by
  obtain ⟨hl0, -, -, -, -, -, -, -, -⟩ := Vr.vr_facts (S := S) k
  obtain ⟨-, hu1O, hlu1, hlfix, -, -⟩ := Ww.ww_seg (S := S) k
  set l := Nc.ncL S (k : Ordinal.{0}) with hldef
  have hμE : InE (upsilon μ) := upsPt_inE (upsPt_upsilon hμ0)
  have hlE : InE (upsilon l) := upsPt_inE (upsPt_upsilon hl0)
  have hlO : upsilon l < Om1 := by rw [hlfix]; exact hlu1.trans hu1O
  have hBl : Bases (upsilon μ) (upsilon l) := ⟨hμE, hlE, hμl, hlO⟩
  have hpi : pi (upsilon μ) (upsilon l) l = upsilon μ := by
    have h := (pi_base hBl).2
    rwa [hlfix] at h ⊢
  have hτE : InE (upsilon (l + (Ww.wwX S k + ω + 1))) :=
    upsPt_inE (upsPt_upsilon (hl0.trans_le le_self_add))
  have hτ'E : InE (upsilon (μ + f (Ww.wwX S k + ω + 1))) := upsPt_inE (upsPt_upsilon (hμ0.trans_le le_self_add))
  show mv (upsilon (l + (Ww.wwX S k + ω + 1))) (upsilon (μ + f (Ww.wwX S k + ω + 1)))
      (upsilon (l + (Ww.wwX S k + ω + 1))) +
    vt (upsilon (μ + f 1)) (Om1 * Uc.ucB + pi (upsilon μ) (upsilon l) l) = _
  rw [Xo.xo_mv_base hτE hτ'E hτO hτ'O, hpi]; rfl

theorem yg_ww_dvd (k : ℕ) : ω ^ 2 ∣ Ww.wwX S k := by
  obtain ⟨-, hXE, -, -, -⟩ := Ww.wwX_spec (S := S) k
  have hωX : ω ≤ Ww.wwX S k := Vo.vo_omega_le hXE (InE.pos hXE)
  have h2c : (2 : Ordinal.{0}) ≤ Ww.wwX S k := ((natCast_lt_omega0 2).trans_le hωX).le
  have h := Vo.vo_e2 ▸ opow_dvd_opow ω h2c
  rwa [hXE] at h

/-- **The moving-leaf carry at `W`**: `υ_{μ+f(h_W)} + W_μ ≤ r(μ+f(W))`. -/
theorem ygCarry_ww (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) {β μ B : Ordinal.{0}}
    {f : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}}
    (hC : Xo.XoCarry S (Nc.ncL S (k : Ordinal.{0})) β μ f B Os) (hX : Ww.wwX S k ∈ Os)
    (h1 : Ww.wwX S k + ω + 1 ∈ Os) (hone : (1 : Ordinal.{0}) ∈ Os)
    (hβ : Ww.wwX S k + ω + 1 < β) (hb1 : upsilon (Nc.ncL S (k : Ordinal.{0}) + β) ≤ Om1)
    (hμ0 : 0 < μ) (hμl : upsilon μ < upsilon (Nc.ncL S (k : Ordinal.{0})))
    (hτ'O : upsilon (μ + f (Ww.wwX S k + ω + 1)) < Om1) :
    upsilon (μ + f (Ww.wwX S k + ω + 1)) + ygWwMu μ f ≤ cdR S (μ + f (Ww.wwX S k)) := by
  obtain ⟨-, hXE, -, -, -⟩ := Ww.wwX_spec (S := S) k
  have hm := upsilon_normal.strictMono
  have hτO : upsilon (Nc.ncL S (k : Ordinal.{0}) + (Ww.wwX S k + ω + 1)) < Om1 :=
    (hm ((add_lt_add_iff_left _).2 hβ)).trans_le hb1
  have h := (hC _ hX (InE.pos hXE) (yg_ww_dvd k)).2.2 (ygWwE S k) (ygWw_WF k hβ hb1) (ygWw_val k hν)
    ⟨h1, hone, trivial, trivial⟩ (ygWw_R k hμ0 hμl hτO)
  rwa [ygWw_img k hμ0 hμl hτO hτ'O] at h

/-- **The obligation at `W` is `W_μ ≤ f(W)`** (`Sl.SlOff` gives `f(h_W) = f(W) + ω + 1`; the reach formula at `μ`
is the hypothesis `hr`). -/
theorem ygWw_obl (k : ℕ) {μ B : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}}
    (hO : Sl.SlOff f Os B)
    (hr : cdR S (μ + f (Ww.wwX S k)) = upsilon (μ + (f (Ww.wwX S k) + ω + 1)) + f (Ww.wwX S k)) :
    upsilon (μ + f (Ww.wwX S k + ω + 1)) + ygWwMu μ f ≤ cdR S (μ + f (Ww.wwX S k)) ↔
      ygWwMu μ f ≤ f (Ww.wwX S k) := by
  obtain ⟨q, hq⟩ := yg_ww_dvd (S := S) k
  have hω : ω + 1 < ω ^ 2 :=
    lt_of_lt_of_le ((add_lt_add_iff_left ω).2 (by exact_mod_cast (show (1 : ℕ) < 2 by norm_num)))
      Vo.vo_om2.le
  have hf : f (Ww.wwX S k + ω + 1) = f (Ww.wwX S k) + ω + 1 := by
    have h := hO.res q (ω + 1) hω
    rw [← hq, ← add_assoc, ← add_assoc] at h
    exact h
  exact Xo.xoCarry_tail_iff hf hr

end Googology.Trans.PoR.InaccPsi.R2.Yg

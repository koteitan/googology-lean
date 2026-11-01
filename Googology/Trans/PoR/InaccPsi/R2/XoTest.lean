import Googology.Trans.PoR.InaccPsi.R2.XoForm
import Googology.Trans.PoR.InaccPsi.R2.GqLoc
import Googology.Trans.PoR.InaccPsi.R2.XaRep

/-!
# Refute first: the moving-leaf carry at the witness `X′ = ϑ^{u₁}(Ω₁·(B₂ + λ) + λ)` and at the next candidates

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`λ = L(k) = υ_λ`, `u₁ = υ_{λ+1}`, `X′ = Xj.xjX S k`, `h₁ = X′ + ω + 1`.  The reach is `r(λ+X′) = υ_{λ+h₁} + X′`
(`Wu.wuR_X`).  Its moving-leaf decomposition is `E′ = sg h₁ υ_{λ+h₁} + th 1 (lc B₂ + lo λ) (lo λ)`.

* `xo_mv_base` (`mv b c b = c`), `xoXjE`, `xoXj_val`, `xoXj_WF` (**`X′` has a moving-leaf form**), `xoForm_gap`
  (**at every window of `Xj.xjVis_ref` the forms clause of `XoGen` holds at `X′`**);
* `xoXj_R` (**`E′` passes the restriction `XoR` at every `μ` with `0 < μ`, `υ_μ < υ_λ`**), `xoXj_notWwR` (its
  constant-level version is excluded by `Ww.WwR`: the old carry said nothing about `X′`);
* `xoXjMu` (`X′_μ = ϑ^{υ_{μ+f(1)}}(Ω₁·(B₂ + υ_μ) + υ_μ)`, the twin of `X′` at `μ`), `xoXj_img` (**the image of `E′`
  is `υ_{μ+f(h₁)} + X′_μ`**), `xoCarry_xj` (**the new carry at `X′` asks `υ_{μ+f(h₁)} + X′_μ ≤ r(μ+f(X′))`**),
  `xoCarry_tail_iff` / `xoXj_obl` (**with `f(h₁) = f(X′) + ω + 1` (`Sl.SlOff`) and the reach formula `r(μ+f(X′)) =
  υ_{μ+(f(X′)+ω+1)} + f(X′)` at `μ`, the obligation is exactly `X′_μ ≤ f(X′)`**: no contradiction, the offset map
  must send `X′` at least to its twin);
* `xoU1E`, `xoNestE`, `xoNext_img` (**the next candidates**: a level containing `u₁` and a level containing the
  nested node `X′`; their images replace `u₁` by `υ_{μ+f(1)}`, resp. `X′` by `X′_μ`);
* `xoCover`, `xoCover_lev` (**every level `M` with `d_S(M) < υ_{λ+β} ≤ Ω₁` is the value of a well-formed level
  term**, from `Vd.VdK` and `Xa.xaRep`), `XoLevLt`, `xoRewrite` (**every well-formed `Ww.WwE` decomposition whose
  levels have data below `υ_{λ+β}` has a moving-leaf decomposition with the same value in which every level is a
  term**), `xoForms_all` (**the forms clause of `XoGen` always holds**, from `Xa.xaRep`).

No new axiom.  New definitions: `xoXjE`, `xoXjMu`, `xoU1E`, `xoNestE` (terms / one ordinal), `XoLevLt` (a predicate).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xo

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- `mv b c b = c` for countable `ε`-bases. -/
theorem xo_mv_base {b c : Ordinal.{0}} (hb : InE b) (hc : InE c) (hb1 : b < Om1) (hc1 : c < Om1) :
    mv b c b = c := by
  unfold mv
  by_cases h1 : c < b
  · rw [if_pos h1]; exact (pi_base ⟨hc, hb, h1, hb1⟩).2
  · rw [if_neg h1]
    by_cases h2 : b < c
    · rw [if_pos h2]; exact up_base ⟨hb, hc, h2, hc1⟩
    · rw [if_neg h2]; exact le_antisymm (not_lt.1 h1) (not_lt.1 h2)

/-- **The moving-leaf decomposition of `r(λ+X′)`.** -/
noncomputable def xoXjE (S : InaccSeq.{0}) (k : ℕ) : XoE :=
  .add (.old (.sg (Xj.xjX S k + ω + 1) (upsilon (Nc.ncL S (k : Ordinal.{0}) + (Xj.xjX S k + ω + 1)))))
    (.th 1 (.add (.lc Uc.ucB) (.old (.lo (Nc.ncL S (k : Ordinal.{0}))))) (.old (.lo (Nc.ncL S (k : Ordinal.{0})))))

theorem xoXj_val (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) :
    xoVal S (Nc.ncL S (k : Ordinal.{0})) (xoXjE S k) = cdR S (Nc.ncL S (k : Ordinal.{0}) + Xj.xjX S k) := by
  obtain ⟨-, hXE, -, hXu2, -⟩ := Xj.xjX_spec (S := S) k
  rw [Wu.wuR_X k hν hXE hXu2]; rfl

/-- **`E′` is well formed** (`X′ + ω + 1 < β`, `υ_{λ+β} ≤ Ω₁`). -/
theorem xoXj_WF (k : ℕ) {β : Ordinal.{0}} (hβ : Xj.xjX S k + ω + 1 < β)
    (hb1 : upsilon (Nc.ncL S (k : Ordinal.{0}) + β) ≤ Om1) :
    XoWF S (Nc.ncL S (k : Ordinal.{0})) β (xoXjE S k) := by
  obtain ⟨hl0, -, -, -, -, -, -, -, -⟩ := Vr.vr_facts (S := S) k
  obtain ⟨hP, hu1O, hlu1, -, -, -⟩ := Ww.ww_seg (S := S) k
  obtain ⟨hξT, hξ2, -, -, -⟩ := Xj.xj_arg (S := S) k
  obtain ⟨-, hXE, hu1X, hXu2, -⟩ := Xj.xjX_spec (S := S) k
  set l := Nc.ncL S (k : Ordinal.{0}) with hldef
  set X := Xj.xjX S k with hXdef
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
  refine ⟨zero_lt_one, h1β, ⟨trivial, hll⟩, hll, ?_⟩
  show l < Om1 ∧ Om1 * (Uc.ucB + l) + l ∈ Tset (upsilon (l + 1)) ∧ Om1 * (Uc.ucB + l) + l < OmTwo ∧
    upsilon (l + 1) ≤ vt (upsilon (l + 1)) (Om1 * (Uc.ucB + l) + l) ∧
    vt (upsilon (l + 1)) (Om1 * (Uc.ucB + l) + l) < upsilon (succ (l + 1))
  refine ⟨hlu1.trans hu1O, hξT, hξ2, hu1X.le, ?_⟩
  rw [succ_eq_add_one, add_assoc, one_add_one_eq_two]; exact hXu2

/-- **The refutation `Xj.xjVis_ref` does not reach the moving-leaf forms**: at every window `υ_{λ+β} ∈
(υ_{λ+X′+ω²}, L(k+1)]` the forms clause of `XoGen` holds at `X′`. -/
theorem xoForm_gap (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) {β : Ordinal.{0}}
    (hβ1 : upsilon (Nc.ncL S (k : Ordinal.{0}) + Xj.xjX S k + ω ^ 2) <
      upsilon (Nc.ncL S (k : Ordinal.{0}) + β))
    (hβ2 : upsilon (Nc.ncL S (k : Ordinal.{0}) + β) ≤ Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) :
    upsilon (Nc.ncL S (k : Ordinal.{0}) + β) ≤ cdR S (Nc.ncL S (k : Ordinal.{0}) + Xj.xjX S k) ∨
      XoForm S (Nc.ncL S (k : Ordinal.{0})) β (Xj.xjX S k) := by
  right
  obtain ⟨-, -, -, -, -, -, hL1O, -, -⟩ := Vr.vr_facts (S := S) k
  have hm := upsilon_normal.strictMono
  have hνβ := hm.lt_iff_lt.1 hβ1
  rw [add_assoc] at hνβ
  have hXβ : Xj.xjX S k + ω ^ 2 < β := (add_lt_add_iff_left _).1 hνβ
  have hω : ω + 1 < ω ^ 2 :=
    lt_of_lt_of_le ((add_lt_add_iff_left ω).2 (by exact_mod_cast (show (1 : ℕ) < 2 by norm_num)))
      Vo.vo_om2.le
  have hβ' : Xj.xjX S k + ω + 1 < β := by
    rw [add_assoc]; exact ((add_lt_add_iff_left _).2 hω).trans hXβ
  exact ⟨xoXjE S k, xoXj_WF k hβ' (hβ2.trans hL1O.le), xoXj_val k hν⟩

/-! ## The restriction and the image at a target `μ` -/

/-- **`E′` passes the restriction** at every `μ > 0` with `υ_μ < υ_λ` (`h₁` large enough for `υ_{λ+h₁} < Ω₁`). -/
theorem xoXj_R (k : ℕ) {μ : Ordinal.{0}} (hμ0 : 0 < μ)
    (hμl : upsilon μ < upsilon (Nc.ncL S (k : Ordinal.{0})))
    (hτO : upsilon (Nc.ncL S (k : Ordinal.{0}) + (Xj.xjX S k + ω + 1)) < Om1) :
    XoR S (Nc.ncL S (k : Ordinal.{0})) μ (xoXjE S k) := by
  obtain ⟨hl0, -, -, -, -, -, -, -, -⟩ := Vr.vr_facts (S := S) k
  obtain ⟨-, hu1O, hlu1, hlfix, -, -⟩ := Ww.ww_seg (S := S) k
  set l := Nc.ncL S (k : Ordinal.{0}) with hldef
  have hm := upsilon_normal.strictMono
  have hμE : InE (upsilon μ) := upsPt_inE (upsPt_upsilon hμ0)
  have hlE : InE (upsilon l) := upsPt_inE (upsPt_upsilon hl0)
  have hlO : upsilon l < Om1 := by rw [hlfix]; exact hlu1.trans hu1O
  have hBl : Bases (upsilon μ) (upsilon l) := ⟨hμE, hlE, hμl, hlO⟩
  set τ := upsilon (l + (Xj.xjX S k + ω + 1)) with hτdef
  have hτE : InE τ := upsPt_inE (upsPt_upsilon (hl0.trans_le le_self_add))
  have hlτ : upsilon l < τ := hm (lt_add_of_pos_right l (lt_of_le_of_lt zero_le (lt_add_one _)))
  have hBτ : Bases (upsilon μ) τ := ⟨hμE, hτE, hμl.trans hlτ, hτO⟩
  refine ⟨fun p hp => (pi_base hBτ).1.2 (Finset.mem_coe.2 hp), ⟨⟨?_, ?_, fun h => h.2.elim⟩, ?_⟩, fun h => h.1.elim⟩
  · exact Or.inr ⟨S, le_rfl, Vd.vd_B_lt_th, gamma 0, Lq.lq_gamma_SC 0,
      Gq.gq_gam_le_ups S (upsPt_upsilon hμ0), Ww.ww_B_dat (S := S) (Lq.lq_gamma_SC 0)⟩
  · show l ∈ TB (upsilon l) (upsilon μ)
    exact (congrArg (· ∈ TB (upsilon l) (upsilon μ)) hlfix).mp (pi_base hBl).1
  · show l ∈ TB (upsilon l) (upsilon μ)
    exact (congrArg (· ∈ TB (upsilon l) (upsilon μ)) hlfix).mp (pi_base hBl).1

/-- **The constant-level version is excluded by the old restriction**: the level `B₂ + λ` has no data reading below
`υ_μ ≤ λ` (`Xj.xj_M0_noLt`), so `Ww.WwCarry` asks nothing about `X′`. -/
theorem xoXj_notWwR (k : ℕ) {μ : Ordinal.{0}} (hμl : upsilon μ ≤ Nc.ncL S (k : Ordinal.{0})) :
    ¬ Vd.VdLtIn (Uc.ucB + Nc.ncL S (k : Ordinal.{0})) (upsilon μ) :=
  Xj.xj_M0_noLt k hμl

/-- **The twin of `X′` at `μ`**: `X′_μ = ϑ^{υ_{μ+f(1)}}(Ω₁·(B₂ + υ_μ) + υ_μ)`. -/
noncomputable def xoXjMu (μ : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) : Ordinal.{0} :=
  vt (upsilon (μ + f 1)) (Om1 * (Uc.ucB + upsilon μ) + upsilon μ)

/-- **The image of `E′`**: `υ_{μ+f(h₁)} + X′_μ` (the leaf `λ` of the level goes to `π(λ) = υ_μ`). -/
theorem xoXj_img (k : ℕ) {μ : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (hμ0 : 0 < μ)
    (hμl : upsilon μ < upsilon (Nc.ncL S (k : Ordinal.{0})))
    (hτO : upsilon (Nc.ncL S (k : Ordinal.{0}) + (Xj.xjX S k + ω + 1)) < Om1)
    (hτ'O : upsilon (μ + f (Xj.xjX S k + ω + 1)) < Om1) :
    xoImg S (Nc.ncL S (k : Ordinal.{0})) μ f (xoXjE S k) =
      upsilon (μ + f (Xj.xjX S k + ω + 1)) + xoXjMu μ f := by
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
  have hτE : InE (upsilon (l + (Xj.xjX S k + ω + 1))) :=
    upsPt_inE (upsPt_upsilon (hl0.trans_le le_self_add))
  have hτ'E : InE (upsilon (μ + f (Xj.xjX S k + ω + 1))) := upsPt_inE (upsPt_upsilon (hμ0.trans_le le_self_add))
  show mv (upsilon (l + (Xj.xjX S k + ω + 1))) (upsilon (μ + f (Xj.xjX S k + ω + 1)))
      (upsilon (l + (Xj.xjX S k + ω + 1))) +
    vt (upsilon (μ + f 1)) (Om1 * (Uc.ucB + pi (upsilon μ) (upsilon l) l) + pi (upsilon μ) (upsilon l) l) = _
  rw [xo_mv_base hτE hτ'E hτO hτ'O, hpi]; rfl

/-- **The new carry at `X′`**: `υ_{μ+f(h₁)} + X′_μ ≤ r(μ+f(X′))`. -/
theorem xoCarry_xj (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) {β μ B : Ordinal.{0}}
    {f : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}}
    (hC : XoCarry S (Nc.ncL S (k : Ordinal.{0})) β μ f B Os) (hX : Xj.xjX S k ∈ Os)
    (h1 : Xj.xjX S k + ω + 1 ∈ Os) (hone : (1 : Ordinal.{0}) ∈ Os)
    (hβ : Xj.xjX S k + ω + 1 < β) (hb1 : upsilon (Nc.ncL S (k : Ordinal.{0}) + β) ≤ Om1)
    (hμ0 : 0 < μ) (hμl : upsilon μ < upsilon (Nc.ncL S (k : Ordinal.{0})))
    (hτ'O : upsilon (μ + f (Xj.xjX S k + ω + 1)) < Om1) :
    upsilon (μ + f (Xj.xjX S k + ω + 1)) + xoXjMu μ f ≤ cdR S (μ + f (Xj.xjX S k)) := by
  obtain ⟨-, hXE, -, -, -⟩ := Xj.xjX_spec (S := S) k
  have hm := upsilon_normal.strictMono
  have hτO : upsilon (Nc.ncL S (k : Ordinal.{0}) + (Xj.xjX S k + ω + 1)) < Om1 :=
    (hm ((add_lt_add_iff_left _).2 hβ)).trans_le hb1
  have hωX : ω ≤ Xj.xjX S k := Vo.vo_omega_le hXE (InE.pos hXE)
  have h2c : (2 : Ordinal.{0}) ≤ Xj.xjX S k := ((natCast_lt_omega0 2).trans_le hωX).le
  have hω2g : ω ^ 2 ∣ Xj.xjX S k := by
    have h := Vo.vo_e2 ▸ opow_dvd_opow ω h2c
    rwa [hXE] at h
  have h := (hC _ hX (InE.pos hXE) hω2g).2.2 (xoXjE S k) (xoXj_WF k hβ hb1) (xoXj_val k hν)
    ⟨h1, hone, ⟨trivial, trivial⟩, trivial⟩ (xoXj_R k hμ0 hμl hτO)
  rwa [xoXj_img k hμ0 hμl hτO hτ'O] at h

/-- **The carry obligation at an offset whose reach ends in the offset**: with `f(g+ω+1) = f(g)+ω+1` and `r(μ+f(g))
= υ_{μ+(f(g)+ω+1)} + f(g)`, `υ_{μ+f(g+ω+1)} + Y ≤ r(μ+f(g)) ⇔ Y ≤ f(g)`. -/
theorem xoCarry_tail_iff {μ g Y : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}}
    (hf : f (g + ω + 1) = f g + ω + 1)
    (hr : cdR S (μ + f g) = upsilon (μ + (f g + ω + 1)) + f g) :
    upsilon (μ + f (g + ω + 1)) + Y ≤ cdR S (μ + f g) ↔ Y ≤ f g := by
  rw [hr, hf]; exact add_le_add_iff_left _

/-- **The obligation at `X′` is `X′_μ ≤ f(X′)`** (`Sl.SlOff` gives `f(h₁) = f(X′) + ω + 1`; the reach formula at
`μ` is the hypothesis `hr`). -/
theorem xoXj_obl (k : ℕ) {μ B : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}}
    (hO : Sl.SlOff f Os B)
    (hr : cdR S (μ + f (Xj.xjX S k)) = upsilon (μ + (f (Xj.xjX S k) + ω + 1)) + f (Xj.xjX S k)) :
    upsilon (μ + f (Xj.xjX S k + ω + 1)) + xoXjMu μ f ≤ cdR S (μ + f (Xj.xjX S k)) ↔
      xoXjMu μ f ≤ f (Xj.xjX S k) := by
  obtain ⟨-, hXE, -, -, -⟩ := Xj.xjX_spec (S := S) k
  have hωX : ω ≤ Xj.xjX S k := Vo.vo_omega_le hXE (InE.pos hXE)
  have h2c : (2 : Ordinal.{0}) ≤ Xj.xjX S k := ((natCast_lt_omega0 2).trans_le hωX).le
  have hω2g : ω ^ 2 ∣ Xj.xjX S k := by
    have h := Vo.vo_e2 ▸ opow_dvd_opow ω h2c
    rwa [hXE] at h
  obtain ⟨q, hq⟩ := hω2g
  have hω : ω + 1 < ω ^ 2 :=
    lt_of_lt_of_le ((add_lt_add_iff_left ω).2 (by exact_mod_cast (show (1 : ℕ) < 2 by norm_num)))
      Vo.vo_om2.le
  have hf : f (Xj.xjX S k + ω + 1) = f (Xj.xjX S k) + ω + 1 := by
    have h := hO.res q (ω + 1) hω
    rw [← hq, ← add_assoc, ← add_assoc] at h
    exact h
  exact xoCarry_tail_iff hf hr

/-! ## The next candidates: a level containing `u₁`, a level containing the nested node `X′` -/

/-- `ϑ^{u₂}(Ω₁·(B₂ + u₁) + λ)`: the level carries the leaf `u₁ = υ_{λ+1}` (an `sg`-node). -/
noncomputable def xoU1E (S : InaccSeq.{0}) (k : ℕ) : XoE :=
  .th 2 (.add (.lc Uc.ucB) (.old (.sg 1 (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)))))
    (.old (.lo (Nc.ncL S (k : Ordinal.{0}))))

/-- `ϑ^{u₂}(Ω₁·(B₂ + X′) + λ)`: the level carries the nested node `X′`. -/
noncomputable def xoNestE (S : InaccSeq.{0}) (k : ℕ) : XoE :=
  .th 2 (.add (.lc Uc.ucB) (.th 1 (.add (.lc Uc.ucB) (.old (.lo (Nc.ncL S (k : Ordinal.{0})))))
      (.old (.lo (Nc.ncL S (k : Ordinal.{0}))))))
    (.old (.lo (Nc.ncL S (k : Ordinal.{0}))))

/-- **Values and images of the next candidates**: `u₁ ↦ υ_{μ+f(1)}`, `X′ ↦ X′_μ`, `λ ↦ υ_μ`. -/
theorem xoNext_img (k : ℕ) {μ : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (hμ0 : 0 < μ)
    (hμl : upsilon μ < upsilon (Nc.ncL S (k : Ordinal.{0}))) (hu1' : upsilon (μ + f 1) < Om1) :
    xoVal S (Nc.ncL S (k : Ordinal.{0})) (xoU1E S k) =
        vt (upsilon (Nc.ncL S (k : Ordinal.{0}) + 2))
          (Om1 * (Uc.ucB + upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) + Nc.ncL S (k : Ordinal.{0})) ∧
      xoImg S (Nc.ncL S (k : Ordinal.{0})) μ f (xoU1E S k) =
        vt (upsilon (μ + f 2)) (Om1 * (Uc.ucB + upsilon (μ + f 1)) + upsilon μ) ∧
      xoVal S (Nc.ncL S (k : Ordinal.{0})) (xoNestE S k) =
        vt (upsilon (Nc.ncL S (k : Ordinal.{0}) + 2))
          (Om1 * (Uc.ucB + Xj.xjX S k) + Nc.ncL S (k : Ordinal.{0})) ∧
      xoImg S (Nc.ncL S (k : Ordinal.{0})) μ f (xoNestE S k) =
        vt (upsilon (μ + f 2)) (Om1 * (Uc.ucB + xoXjMu μ f) + upsilon μ) := by
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
  have hu1E : InE (upsilon (l + 1)) := upsPt_inE (upsPt_upsilon (hl0.trans_le le_self_add))
  have hu1'E : InE (upsilon (μ + f 1)) := upsPt_inE (upsPt_upsilon (hμ0.trans_le le_self_add))
  refine ⟨rfl, ?_, rfl, ?_⟩
  · show vt (upsilon (μ + f 2)) (Om1 * (Uc.ucB + mv (upsilon (l + 1)) (upsilon (μ + f 1)) (upsilon (l + 1))) +
      pi (upsilon μ) (upsilon l) l) = _
    rw [xo_mv_base hu1E hu1'E hu1O hu1', hpi]
  · show vt (upsilon (μ + f 2)) (Om1 * (Uc.ucB + vt (upsilon (μ + f 1))
      (Om1 * (Uc.ucB + pi (upsilon μ) (upsilon l) l) + pi (upsilon μ) (upsilon l) l)) +
      pi (upsilon μ) (upsilon l) l) = _
    rw [hpi]; rfl

/-! ## The covering argument -/

/-- **Every member of the visibility closure `K⁽⁰⁾_q`, `q ≤ υ_{λ+β} ≤ Ω₁`, is the value of a well-formed level term**
(leaves by `Xa.xaRep`, the operations of `Vd.VdK` by the level constructors). -/
theorem xoCover (S : InaccSeq.{0}) {l β q : Ordinal.{0}} (hl0 : 0 < l) (hq : q ≤ upsilon (l + β))
    (hq1 : q ≤ Om1) : ∀ x, Vd.VdK S 0 q x → ∃ L : XoE, XoWF S l β L ∧ xoVal S l L = x := by
  intro x hx
  induction hx with
  | small h =>
    obtain ⟨E, hW, hv⟩ := Xa.xaRep S hl0 _ (h.trans_le hq) (h.trans_le hq1)
    exact ⟨xoOfWw E, xoOfWw_WF l β E hW, (xoOfWw_val l E).trans hv⟩
  | zero => exact ⟨.lc 0, trivial, rfl⟩
  | inacc n => exact ⟨.lc (S.I n), trivial, rfl⟩
  | inaccW => exact ⟨.lc S.Iw, trivial, rfl⟩
  | add _ _ ih1 ih2 =>
    obtain ⟨L1, h1, e1⟩ := ih1
    obtain ⟨L2, h2, e2⟩ := ih2
    exact ⟨.add L1 L2, ⟨h1, h2⟩, by show xoVal S l L1 + xoVal S l L2 = _; rw [e1, e2]⟩
  | phi _ _ ih1 ih2 =>
    obtain ⟨L1, h1, e1⟩ := ih1
    obtain ⟨L2, h2, e2⟩ := ih2
    exact ⟨.phi L1 L2, ⟨h1, h2⟩, by show veblen (xoVal S l L1) (xoVal S l L2) = _; rw [e1, e2]⟩
  | om _ ih =>
    obtain ⟨L1, h1, e1⟩ := ih
    exact ⟨.om L1, h1, by show Om (xoVal S l L1) = _; rw [e1]⟩
  | coll _ _ _ _ ihp ihe =>
    obtain ⟨Lp, hp, ep⟩ := ihp
    obtain ⟨Le, he, ee⟩ := ihe
    exact ⟨.coll Lp Le, ⟨hp, he⟩, by show S.psi (xoVal S l Le) (xoVal S l Lp) = _; rw [ep, ee]⟩

/-- **Every level whose `K⁽⁰⁾`-datum lies below `υ_{λ+β} ≤ Ω₁` is the value of a well-formed level term.** -/
theorem xoCover_lev (S : InaccSeq.{0}) {l β M : Ordinal.{0}} (hl0 : 0 < l)
    (hd : Vd.vdD S 0 M < upsilon (l + β)) (hb1 : upsilon (l + β) ≤ Om1) :
    ∃ L : XoE, XoWF S l β L ∧ xoVal S l L = M := by
  have hK : Vd.VdK S 0 (Vd.vdD S 0 M + 1) M := Vd.vdK_ofUl (by rw [Vd.vdD_eq]; exact Ul.ulD_spec M)
  have hq : Vd.vdD S 0 M + 1 ≤ upsilon (l + β) := Order.add_one_le_of_lt hd
  exact xoCover S hl0 hq (hq.trans hb1) M hK

/-- The levels of a `Ww.WwE` decomposition have their `K⁽⁰⁾`-data below `b`. -/
def XoLevLt (S : InaccSeq.{0}) (b : Ordinal.{0}) : Ww.WwE → Prop
  | .old _ => True
  | .th _ M e => Vd.vdD S 0 M < b ∧ XoLevLt S b e
  | .add s t => XoLevLt S b s ∧ XoLevLt S b t

/-- **The covering argument for the forms**: every well-formed `Ww.WwE` decomposition whose levels have data below
`υ_{λ+β} ≤ Ω₁` has a well-formed moving-leaf decomposition with the same value in which every level is a term. -/
theorem xoRewrite (S : InaccSeq.{0}) {l β : Ordinal.{0}} (hl0 : 0 < l) (hb1 : upsilon (l + β) ≤ Om1) :
    ∀ E : Ww.WwE, Ww.WwWF l β E → XoLevLt S (upsilon (l + β)) E →
      ∃ E' : XoE, XoWF S l β E' ∧ xoVal S l E' = Ww.wwVal l E
  | .old E, hW, _ => ⟨.old E, hW, rfl⟩
  | .th h M e, ⟨h0, hβ, he, hv, hT, h2, hlo, hhi⟩, ⟨hd, hde⟩ => by
    obtain ⟨L, hL, eL⟩ := xoCover_lev S hl0 hd hb1
    obtain ⟨e', he', ee'⟩ := xoRewrite S hl0 hb1 e he hde
    refine ⟨.th h L e', ⟨h0, hβ, hL, he', ?_⟩, ?_⟩
    · rw [eL, ee']; exact ⟨hv, hT, h2, hlo, hhi⟩
    · show vt (upsilon (l + h)) (Om1 * xoVal S l L + xoVal S l e') = vt (upsilon (l + h)) (Om1 * M + Ww.wwVal l e)
      rw [eL, ee']
  | .add s t, ⟨hs, ht⟩, ⟨hds, hdt⟩ => by
    obtain ⟨s', hs', es⟩ := xoRewrite S hl0 hb1 s hs hds
    obtain ⟨t', ht', et⟩ := xoRewrite S hl0 hb1 t ht hdt
    exact ⟨.add s' t', ⟨hs', ht'⟩, by show xoVal S l s' + xoVal S l t' = _; rw [es, et]; rfl⟩

/-- **The forms clause of `XoGen` always holds** (every countable value below `υ_{λ+β} ≤ Ω₁` has a decomposition,
`Xa.xaRep`, and old decompositions are moving-leaf decompositions). -/
theorem xoForms_all (S : InaccSeq.{0}) {l β : Ordinal.{0}} (hl0 : 0 < l) (hb1 : upsilon (l + β) ≤ Om1) :
    ∀ g, upsilon (l + β) ≤ cdR S (l + g) ∨ XoForm S l β g := by
  intro g
  rcases le_or_gt (upsilon (l + β)) (cdR S (l + g)) with h | h
  · exact Or.inl h
  · obtain ⟨E, hW, hv⟩ := Xa.xaRep S hl0 _ h (h.trans_le hb1)
    exact Or.inr ⟨xoOfWw E, xoOfWw_WF l β E hW, (xoOfWw_val l E).trans hv⟩

end Googology.Trans.PoR.InaccPsi.R2.Xo

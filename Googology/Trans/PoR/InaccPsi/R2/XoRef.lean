import Googology.Trans.PoR.InaccPsi.R2.XoTest
import Googology.Trans.PoR.InaccPsi.R2.SkSXPi

/-!
# The repaired restriction `Xo.XoR`: the fixed spellings of `L(k)` are excluded

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`λ = L(k) = ψ_{Ω₁}(Ω_ω + Ω_ω + P′·k)`, `P′ = ψ_{Ω₂}(Ω_ω + Ω_ω)`, `X′ = Xj.xjX S k`, `h₁ = X′ + ω + 1`.
The restriction of round 124 asked data only of the constants `lc M`; the level operations gave **fixed spellings**
(image = value) of countable points `≥ υ_μ`, e.g. `F_k = ψ_{Ω₁}(Ω_ω + Ω_ω + P′·k)` with value `λ`.

* `xoCl_img` / `xoCl_WF` / `xoCl_Os` (closed terms: image = value, always well formed), `xoLow_lt`, `xoVd_lt`,
  `xoVd_small` (a low countable value is below `υ_μ`);
* `xoR_fixed` (**every closed spelling of a countable point `≥ υ_μ` violates `XoR`**), `xoR_coll_lt` (**a countable
  collapse inside a restricted term is below `υ_μ`**);
* `xoW`, `xoPp`, `xoPk`, `xoFk` (the audit's `F_k`), `xoFk_val` (`val F_k = L(k)`), `xoFk_notR`;
  `xoFkA` (**the absorbed spelling** `ψ_{Ω₁}(λ + Ω_ω + Ω_ω + P′·k)`: it carries the moving leaf `λ`, absorbed by
  `Ω_ω`, value `λ`), `xoFkA_val`, `xoFkA_notR`;
* `xoE2` (the audit's `E″ = sg h₁ + th 1 (lc B₂ + F_k) (lo λ)`), `xoE3` (`E‴ = (F′_k + sg h₁) + th 1 (lc B₂ + lo λ)
  (lo λ)`): both well formed with value `r(λ+X′)` (`xoE2_WF`, `xoE2_val`, `xoE3_WF`, `xoE3_val`, `xoE3_Os`), both
  excluded (`xoE2_notR`, `xoE3_notR`);
* `XoRn` (**the purely syntactic repair**: closed sub-terms with a countable value below `υ_μ`, nothing on collapses),
  `xoR_Rn` (the repair implies it), `XoCarryN`, `xoE3_Rn`, `xoE3_img_ge` and **`xoNaive_ref`: the syntactic repair is
  REFUTED** — `E‴` passes `XoRn`, its image is `≥ λ`, and under the reach formula at `μ + f(X′)` the carry asks
  `λ ≤ r(μ + f(X′)) < λ`;
* `xoU1_R`, `xoNest_R` (**the next candidates pass the repaired restriction**; `E′` itself: `Xo.xoXj_R`),
  `xoOff_wit` (**the offset obligation at `X′` is consistent with `Sl.SlOff`**: for every `ε`-number `Y > 1` there is
  an offset map on `{1, X′, h₁}` with `f(X′) = Y`, bound `Y + ω²`).

No new axiom.  New definitions: the terms `xoW`, `xoPp`, `xoPk`, `xoFk`, `xoFkA`, `xoSgX`, `xoThX`, `xoE2`, `xoE3`,
the statements `XoRn`, `XoCarryN`, the offset map `xoOffF`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xo

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-! ## Closed terms -/

theorem xoCl_img (l μ : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) :
    ∀ E : XoE, XoCl E → xoImg S l μ f E = xoVal S l E
  | .old _, h => h.elim
  | .th _ _ _, h => h.elim
  | .add s t, h => by
    show xoImg S l μ f s + xoImg S l μ f t = xoVal S l s + xoVal S l t
    rw [xoCl_img l μ f s h.1, xoCl_img l μ f t h.2]
  | .lc _, _ => rfl
  | .phi a b, h => by
    show veblen (xoImg S l μ f a) (xoImg S l μ f b) = veblen (xoVal S l a) (xoVal S l b)
    rw [xoCl_img l μ f a h.1, xoCl_img l μ f b h.2]
  | .om a, h => by
    show Om (xoImg S l μ f a) = Om (xoVal S l a)
    rw [xoCl_img l μ f a h]
  | .coll p e, h => by
    show S.psi (xoImg S l μ f e) (xoImg S l μ f p) = S.psi (xoVal S l e) (xoVal S l p)
    rw [xoCl_img l μ f p h.1, xoCl_img l μ f e h.2]

theorem xoCl_WF (l β : Ordinal.{0}) : ∀ E : XoE, XoCl E → XoWF S l β E
  | .old _, h => h.elim
  | .th _ _ _, h => h.elim
  | .add s t, h => ⟨xoCl_WF l β s h.1, xoCl_WF l β t h.2⟩
  | .lc _, _ => trivial
  | .phi a b, h => ⟨xoCl_WF l β a h.1, xoCl_WF l β b h.2⟩
  | .om a, h => xoCl_WF l β a h
  | .coll p e, h => ⟨xoCl_WF l β p h.1, xoCl_WF l β e h.2⟩

theorem xoCl_Os (l : Ordinal.{0}) (Os : Finset Ordinal.{0}) : ∀ E : XoE, XoCl E → XoOs l Os E
  | .old _, h => h.elim
  | .th _ _ _, h => h.elim
  | .add s t, h => ⟨xoCl_Os l Os s h.1, xoCl_Os l Os t h.2⟩
  | .lc _, _ => trivial
  | .phi a b, h => ⟨xoCl_Os l Os a h.1, xoCl_Os l Os b h.2⟩
  | .om a, h => xoCl_Os l Os a h
  | .coll p e, h => ⟨xoCl_Os l Os p h.1, xoCl_Os l Os e h.2⟩

/-- A countable value with a data reading below `v` is below `v` (`Uc.ucDat_small`). -/
theorem xoVd_lt {M v : Ordinal.{0}} (hM : M < Om1) (h : Vd.VdLtIn M v) : M < v := by
  rcases h with ⟨-, hd⟩ | ⟨_, hB, -⟩
  · rwa [Uc.ucDat_small hM] at hd
  · exact absurd (hM.trans Uc.ucB_gt) (not_lt.2 hB)

theorem xoVd_small {c v : Ordinal.{0}} (hc : c < Om1) (hv : c < v) : Vd.VdLtIn c v :=
  Or.inl ⟨hc.trans Uc.ucB_gt, by rw [Uc.ucDat_small hc]; exact hv⟩

/-- **A low countable value lies below `υ_μ`.** -/
theorem xoLow_lt {μ v : Ordinal.{0}} (hv : v < Om1) (h : XoLow S μ v) : v < upsilon μ :=
  xoVd_lt hv (h (hv.trans_le (by rw [Br.Om1_eq]; exact (Bt.Om1_lt_th (S := S)).le)))

/-- **Every closed spelling of a countable point `≥ υ_μ` violates the repaired restriction.** -/
theorem xoR_fixed {l μ : Ordinal.{0}} : ∀ E : XoE, XoCl E → upsilon μ ≤ xoVal S l E → xoVal S l E < Om1 →
    ¬ XoR S l μ E
  | .old _, h, _, _, _ => h
  | .th _ _ _, h, _, _, _ => h
  | .add _ _, hc, hle, hv, hR => (not_lt.2 hle) (xoLow_lt hv (hR.2.2 hc))
  | .lc _, _, hle, hv, hR => (not_lt.2 hle) (xoVd_lt hv hR)
  | .phi _ _, hc, hle, hv, hR => (not_lt.2 hle) (xoLow_lt hv (hR.2.2 hc))
  | .om _, hc, hle, hv, hR => (not_lt.2 hle) (xoLow_lt hv (hR.2 hc))
  | .coll _ _, hc, hle, hv, hR => (not_lt.2 hle) (xoLow_lt hv (hR.2.2.1 hc))

/-- **A countable collapse inside a restricted term is below `υ_μ`** (closed or not). -/
theorem xoR_coll_lt {l μ : Ordinal.{0}} {p e : XoE} (hR : XoR S l μ (.coll p e))
    (hv : S.psi (xoVal S l e) (xoVal S l p) < Om1) : S.psi (xoVal S l e) (xoVal S l p) < upsilon μ :=
  (hR.2.2.2 hv).2.2

/-! ## The fixed spelling `F_k` and the absorbed spelling `F′_k` of `L(k)` -/

/-- `ω = φ(0, 1)`. -/
def xoW : XoE := .phi (.lc 0) (.lc 1)

/-- `P′ = ψ_{Ω₂}(Ω_ω + Ω_ω)`. -/
def xoPp : XoE := .coll (.om (.lc (1 + 1))) (.add (.om xoW) (.om xoW))

/-- `P′·n`. -/
def xoPk : ℕ → XoE
  | 0 => .lc 0
  | n + 1 => .add (xoPk n) xoPp

/-- **The audit's fixed spelling** `F_k = ψ_{Ω₁}(Ω_ω + Ω_ω + P′·k)`. -/
def xoFk (k : ℕ) : XoE := .coll (.om (.lc 1)) (.add (.add (.om xoW) (.om xoW)) (xoPk k))

/-- **The absorbed spelling** `F′_k = ψ_{Ω₁}(λ + Ω_ω + Ω_ω + P′·k)` (the moving leaf `lo λ` is absorbed by `Ω_ω`). -/
noncomputable def xoFkA (S : InaccSeq.{0}) (k : ℕ) : XoE :=
  .coll (.om (.lc 1))
    (.add (.add (.add (.old (.lo (Nc.ncL S (k : Ordinal.{0})))) (.om xoW)) (.om xoW)) (xoPk k))

theorem xoW_cl : XoCl xoW := ⟨trivial, trivial⟩
theorem xoPp_cl : XoCl xoPp := ⟨trivial, xoW_cl, xoW_cl⟩
theorem xoPk_cl : ∀ n : ℕ, XoCl (xoPk n)
  | 0 => trivial
  | n + 1 => ⟨xoPk_cl n, xoPp_cl⟩
theorem xoFk_cl (k : ℕ) : XoCl (xoFk k) := ⟨trivial, ⟨xoW_cl, xoW_cl⟩, xoPk_cl k⟩

theorem xoW_val (l : Ordinal.{0}) : xoVal S l xoW = ω := by
  show veblen 0 1 = ω
  rw [veblen_zero_apply, opow_one]

theorem xoPp_val (l : Ordinal.{0}) : xoVal S l xoPp = Nc.ncPp S := by
  show S.psi (Om (xoVal S l xoW) + Om (xoVal S l xoW)) (Om (1 + 1)) = _
  rw [xoW_val]; rfl

theorem xoPk_val (l : Ordinal.{0}) : ∀ n : ℕ, xoVal S l (xoPk n) = Nc.ncPp S * (n : Ordinal.{0})
  | 0 => by show (0 : Ordinal.{0}) = _; simp
  | n + 1 => by
    show xoVal S l (xoPk n) + xoVal S l xoPp = _
    rw [xoPk_val l n, xoPp_val, Nat.cast_succ, mul_add_one]

theorem xoFk_val (l : Ordinal.{0}) (k : ℕ) : xoVal S l (xoFk k) = Nc.ncL S (k : Ordinal.{0}) := by
  show S.psi (Om (xoVal S l xoW) + Om (xoVal S l xoW) + xoVal S l (xoPk k)) (Om 1) = _
  rw [xoW_val, xoPk_val]; rfl

/-- A countable ordinal is absorbed by `Ω_ω`. -/
theorem xo_absorb {x : Ordinal.{0}} (hx : x < Om1) : x + Om ω = Om ω := by
  have hW : ω ^ Om ω = Om ω := Low.opow_eq_self_of_SC (SC_Om omega0_ne_zero)
  have h1 : Om1 ≤ Om ω := by rw [Br.Om1_eq]; exact Om_le_Om.2 one_lt_omega0.le
  exact add_absorp (by rw [hW]; exact hx.trans_le h1) hW.le

theorem xo_lam_lt (k : ℕ) : Nc.ncL S (k : Ordinal.{0}) < Om1 := by
  obtain ⟨-, hu1O, hlu1, -, -, -⟩ := Ww.ww_seg (S := S) k
  exact hlu1.trans hu1O

theorem xoFkA_val (l : Ordinal.{0}) (k : ℕ) : xoVal S l (xoFkA S k) = Nc.ncL S (k : Ordinal.{0}) := by
  show S.psi (Nc.ncL S (k : Ordinal.{0}) + Om (xoVal S l xoW) + Om (xoVal S l xoW) + xoVal S l (xoPk k))
    (Om 1) = _
  rw [xoW_val, xoPk_val, xo_absorb (xo_lam_lt k)]; rfl

/-- **`F_k` violates the repaired restriction** at every `μ` with `υ_μ ≤ λ`. -/
theorem xoFk_notR (k : ℕ) {l μ : Ordinal.{0}} (hμ : upsilon μ ≤ Nc.ncL S (k : Ordinal.{0})) :
    ¬ XoR S l μ (xoFk k) :=
  xoR_fixed _ (xoFk_cl k) (by rw [xoFk_val]; exact hμ) (by rw [xoFk_val]; exact xo_lam_lt k)

/-- **The absorbed spelling violates the repaired restriction** (a countable collapse `≥ υ_μ`). -/
theorem xoFkA_notR (k : ℕ) {l μ : Ordinal.{0}} (hμ : upsilon μ ≤ Nc.ncL S (k : Ordinal.{0})) :
    ¬ XoR S l μ (xoFkA S k) := fun hR => by
  have h := xoR_coll_lt hR (by
    show xoVal S l (xoFkA S k) < Om1
    rw [xoFkA_val]; exact xo_lam_lt k)
  have h' : xoVal S l (xoFkA S k) < upsilon μ := h
  rw [xoFkA_val] at h'
  exact (not_lt.2 hμ) h'

/-! ## The audit's `E″` and the absorbed `E‴`: well formed, value `r(λ+X′)`, excluded -/

/-- `sg h₁ υ_{λ+h₁}`. -/
noncomputable def xoSgX (S : InaccSeq.{0}) (k : ℕ) : XoE :=
  .old (.sg (Xj.xjX S k + ω + 1) (upsilon (Nc.ncL S (k : Ordinal.{0}) + (Xj.xjX S k + ω + 1))))

/-- `th 1 (lc B₂ + lo λ) (lo λ)` (value `X′`). -/
noncomputable def xoThX (S : InaccSeq.{0}) (k : ℕ) : XoE :=
  .th 1 (.add (.lc Uc.ucB) (.old (.lo (Nc.ncL S (k : Ordinal.{0}))))) (.old (.lo (Nc.ncL S (k : Ordinal.{0}))))

theorem xoXjE_eq (k : ℕ) : xoXjE S k = .add (xoSgX S k) (xoThX S k) := rfl

/-- **The audit's `E″`**: the level leaf `lo λ` replaced by `F_k`. -/
noncomputable def xoE2 (S : InaccSeq.{0}) (k : ℕ) : XoE :=
  .add (xoSgX S k) (.th 1 (.add (.lc Uc.ucB) (xoFk k)) (.old (.lo (Nc.ncL S (k : Ordinal.{0})))))

/-- **The absorbed `E‴`**: `F′_k + E′` (the summand `F′_k` is absorbed by `υ_{λ+h₁}`). -/
noncomputable def xoE3 (S : InaccSeq.{0}) (k : ℕ) : XoE :=
  .add (.add (xoFkA S k) (xoSgX S k)) (xoThX S k)

theorem xoE2_val (k : ℕ) : xoVal S (Nc.ncL S (k : Ordinal.{0})) (xoE2 S k) =
    xoVal S (Nc.ncL S (k : Ordinal.{0})) (xoXjE S k) := by
  show xoVal S _ (xoSgX S k) + vt (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1))
      (Om1 * (Uc.ucB + xoVal S _ (xoFk k)) + Nc.ncL S (k : Ordinal.{0})) =
    xoVal S _ (xoSgX S k) + vt (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1))
      (Om1 * (Uc.ucB + Nc.ncL S (k : Ordinal.{0})) + Nc.ncL S (k : Ordinal.{0}))
  rw [xoFk_val]

theorem xoE2_WF (k : ℕ) {β : Ordinal.{0}} (hβ : Xj.xjX S k + ω + 1 < β)
    (hb1 : upsilon (Nc.ncL S (k : Ordinal.{0}) + β) ≤ Om1) :
    XoWF S (Nc.ncL S (k : Ordinal.{0})) β (xoE2 S k) := by
  obtain ⟨hsg, h0, h1, -, he, hrest⟩ := xoXj_WF (S := S) k hβ hb1
  refine ⟨hsg, h0, h1, ⟨trivial, xoCl_WF _ _ _ (xoFk_cl k)⟩, he, ?_⟩
  have hv : xoVal S (Nc.ncL S (k : Ordinal.{0})) (.add (.lc Uc.ucB) (xoFk k)) =
      xoVal S (Nc.ncL S (k : Ordinal.{0})) (.add (.lc Uc.ucB) (.old (.lo (Nc.ncL S (k : Ordinal.{0}))))) := by
    show Uc.ucB + xoVal S _ (xoFk k) = Uc.ucB + Nc.ncL S (k : Ordinal.{0})
    rw [xoFk_val]
  rw [hv]; exact hrest

/-- **`E″` is excluded** (its level contains `F_k`). -/
theorem xoE2_notR (k : ℕ) {μ : Ordinal.{0}} (hμ : upsilon μ ≤ Nc.ncL S (k : Ordinal.{0})) :
    ¬ XoR S (Nc.ncL S (k : Ordinal.{0})) μ (xoE2 S k) := fun hR => xoFk_notR k hμ hR.2.1.1.2.1

theorem xo_lam_absorb (k : ℕ) {h : Ordinal.{0}} (h0 : 0 < h) :
    Nc.ncL S (k : Ordinal.{0}) + upsilon (Nc.ncL S (k : Ordinal.{0}) + h) =
      upsilon (Nc.ncL S (k : Ordinal.{0}) + h) := by
  obtain ⟨hl0, -, -, -, -, -, -, -, -⟩ := Vr.vr_facts (S := S) k
  obtain ⟨-, -, -, hlfix, -, -⟩ := Ww.ww_seg (S := S) k
  have hE : InE (upsilon (Nc.ncL S (k : Ordinal.{0}) + h)) :=
    upsPt_inE (upsPt_upsilon (hl0.trans_le le_self_add))
  have hlt : Nc.ncL S (k : Ordinal.{0}) < upsilon (Nc.ncL S (k : Ordinal.{0}) + h) := by
    conv_lhs => rw [← hlfix]
    exact upsilon_normal.strictMono (lt_add_of_pos_right _ h0)
  exact add_absorp (by rw [hE]; exact hlt) hE.le

theorem xoE3_val (k : ℕ) : xoVal S (Nc.ncL S (k : Ordinal.{0})) (xoE3 S k) =
    xoVal S (Nc.ncL S (k : Ordinal.{0})) (xoXjE S k) := by
  show xoVal S _ (xoFkA S k) + upsilon (Nc.ncL S (k : Ordinal.{0}) + (Xj.xjX S k + ω + 1)) +
      xoVal S _ (xoThX S k) =
    upsilon (Nc.ncL S (k : Ordinal.{0}) + (Xj.xjX S k + ω + 1)) + xoVal S _ (xoThX S k)
  rw [xoFkA_val, xo_lam_absorb k (lt_of_le_of_lt zero_le (lt_add_one _))]

theorem xoE3_WF (k : ℕ) {β : Ordinal.{0}} (hβ : Xj.xjX S k + ω + 1 < β)
    (hb1 : upsilon (Nc.ncL S (k : Ordinal.{0}) + β) ≤ Om1) :
    XoWF S (Nc.ncL S (k : Ordinal.{0})) β (xoE3 S k) := by
  obtain ⟨hsg, hth⟩ := xoXj_WF (S := S) k hβ hb1
  obtain ⟨-, -, -, hlo, -⟩ := hth
  refine ⟨⟨⟨trivial, ⟨⟨hlo, xoCl_WF _ _ _ xoW_cl⟩, xoCl_WF _ _ _ xoW_cl⟩, xoCl_WF _ _ _ (xoPk_cl k)⟩, hsg⟩,
    xoXj_WF (S := S) k hβ hb1 |>.2⟩

theorem xoE3_Os (k : ℕ) {Os : Finset Ordinal.{0}} (h1 : Xj.xjX S k + ω + 1 ∈ Os) (hone : (1 : Ordinal.{0}) ∈ Os) :
    XoOs (Nc.ncL S (k : Ordinal.{0})) Os (xoE3 S k) :=
  ⟨⟨⟨trivial, ⟨⟨trivial, xoCl_Os _ _ _ xoW_cl⟩, xoCl_Os _ _ _ xoW_cl⟩, xoCl_Os _ _ _ (xoPk_cl k)⟩, h1⟩,
    hone, ⟨trivial, trivial⟩, trivial⟩

/-- **`E‴` is excluded** (its countable collapse `F′_k` has value `λ ≥ υ_μ`). -/
theorem xoE3_notR (k : ℕ) {μ : Ordinal.{0}} (hμ : upsilon μ ≤ Nc.ncL S (k : Ordinal.{0})) :
    ¬ XoR S (Nc.ncL S (k : Ordinal.{0})) μ (xoE3 S k) := fun hR => xoFkA_notR k hμ hR.1.1

/-! ## The purely syntactic repair is refuted -/

/-- **The syntactic repair**: the restriction of round 124 plus "every closed sub-term with a countable value is below
`υ_μ`" (nothing on collapses with moving leaves). -/
def XoRn (S : InaccSeq.{0}) (l μ : Ordinal.{0}) : XoE → Prop
  | .old E => Wf.WfR l μ E
  | .th _ L e => XoRn S l μ L ∧ XoRn S l μ e
  | .add s t => XoRn S l μ s ∧ XoRn S l μ t ∧
      (XoCl s ∧ XoCl t → xoVal S l s + xoVal S l t < Om1 → xoVal S l s + xoVal S l t < upsilon μ)
  | .lc M => Vd.VdLtIn M (upsilon μ)
  | .phi a b => XoRn S l μ a ∧ XoRn S l μ b ∧
      (XoCl a ∧ XoCl b → veblen (xoVal S l a) (xoVal S l b) < Om1 →
        veblen (xoVal S l a) (xoVal S l b) < upsilon μ)
  | .om a => XoRn S l μ a ∧ (XoCl a → Om (xoVal S l a) < Om1 → Om (xoVal S l a) < upsilon μ)
  | .coll p e => XoRn S l μ p ∧ XoRn S l μ e ∧
      (XoCl p ∧ XoCl e → S.psi (xoVal S l e) (xoVal S l p) < Om1 →
        S.psi (xoVal S l e) (xoVal S l p) < upsilon μ)

/-- The repaired restriction implies the syntactic one. -/
theorem xoR_Rn {l μ : Ordinal.{0}} : ∀ E : XoE, XoR S l μ E → XoRn S l μ E
  | .old _, h => h
  | .th _ L e, h => ⟨xoR_Rn L h.1, xoR_Rn e h.2⟩
  | .add s t, h => ⟨xoR_Rn s h.1, xoR_Rn t h.2.1, fun hc hv => xoLow_lt hv (h.2.2 hc)⟩
  | .lc _, h => h
  | .phi a b, h => ⟨xoR_Rn a h.1, xoR_Rn b h.2.1, fun hc hv => xoLow_lt hv (h.2.2 hc)⟩
  | .om a, h => ⟨xoR_Rn a h.1, fun hc hv => xoLow_lt hv (h.2 hc)⟩
  | .coll p e, h => ⟨xoR_Rn p h.1, xoR_Rn e h.2.1, fun hc hv => xoLow_lt hv (h.2.2.1 hc)⟩

/-- The carry over the syntactic repair. -/
def XoCarryN (S : InaccSeq.{0}) (l β μ : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) (B : Ordinal.{0})
    (Os : Finset Ordinal.{0}) : Prop :=
  ∀ g ∈ Os, 0 < g → ω ^ 2 ∣ g → CdLower S (μ + f g) ∧
    (upsilon (l + β) ≤ cdR S (l + g) → upsilon (μ + B) ≤ cdR S (μ + f g)) ∧
    ∀ E : XoE, XoWF S l β E → xoVal S l E = cdR S (l + g) → XoOs l Os E → XoRn S l μ E →
      xoImg S l μ f E ≤ cdR S (μ + f g)

theorem xo_nat_vd {μ : Ordinal.{0}} (hμ0 : 0 < μ) (n : ℕ) : Vd.VdLtIn (n : Ordinal.{0}) (upsilon μ) := by
  have hE : InE (upsilon μ) := upsPt_inE (upsPt_upsilon hμ0)
  have hn : (n : Ordinal.{0}) < ω := natCast_lt_omega0 n
  have hω1 : ω < Om1 := Gf.omega_lt_Om1
  exact xoVd_small (hn.trans hω1) (hn.trans (omega0_lt_inE hE))


theorem xo_fin_vd {μ c : Ordinal.{0}} (hμ0 : 0 < μ) (hc : c < ω) : Vd.VdLtIn c (upsilon μ) := by
  have hE : InE (upsilon μ) := upsPt_inE (upsPt_upsilon hμ0)
  exact xoVd_small (hc.trans Gf.omega_lt_Om1) (hc.trans (omega0_lt_inE hE))

theorem xo_Om1_le_Om {a : Ordinal.{0}} (ha : 1 ≤ a) : Om1 ≤ Om a := by
  rw [Br.Om1_eq]; exact Om_le_Om.2 ha

theorem xo_Pp_gt : Om1 < Nc.ncPp S := by
  rw [Br.Om1_eq]; exact (InaccSeq.psiS_bounds (S := S) _ 1).1

theorem xoW_Rn {l μ : Ordinal.{0}} (hμ0 : 0 < μ) : XoRn S l μ xoW := by
  have hE : InE (upsilon μ) := upsPt_inE (upsPt_upsilon hμ0)
  refine ⟨xo_fin_vd hμ0 (by simpa using natCast_lt_omega0 0), xo_fin_vd hμ0 (by simpa using natCast_lt_omega0 1),
    fun _ _ => ?_⟩
  show veblen 0 1 < upsilon μ
  rw [veblen_zero_apply, opow_one]; exact omega0_lt_inE hE

theorem xoOmW_Rn {l μ : Ordinal.{0}} (hμ0 : 0 < μ) : XoRn S l μ (.om xoW) :=
  ⟨xoW_Rn hμ0, fun _ hv => absurd hv (not_lt.2 (by
    rw [xoW_val]; exact xo_Om1_le_Om one_lt_omega0.le))⟩

theorem xoPp_Rn {l μ : Ordinal.{0}} (hμ0 : 0 < μ) : XoRn S l μ xoPp := by
  refine ⟨⟨xo_fin_vd hμ0 (Ordinal.lt_omega0.2 ⟨2, by norm_num⟩), fun _ hv => absurd hv (not_lt.2
      (xo_Om1_le_Om (le_add_self)))⟩, ⟨xoOmW_Rn hμ0, xoOmW_Rn hμ0, fun _ hv => absurd hv (not_lt.2 ?_)⟩,
    fun _ hv => absurd hv (not_lt.2 ?_)⟩
  · show Om1 ≤ Om (xoVal S l xoW) + Om (xoVal S l xoW)
    rw [xoW_val]; exact (xo_Om1_le_Om one_lt_omega0.le).trans le_self_add
  · show Om1 ≤ xoVal S l xoPp
    rw [xoPp_val]; exact xo_Pp_gt.le

theorem xoPk_Rn {l μ : Ordinal.{0}} (hμ0 : 0 < μ) : ∀ n : ℕ, XoRn S l μ (xoPk n)
  | 0 => xo_fin_vd hμ0 (by simpa using natCast_lt_omega0 0)
  | n + 1 => ⟨xoPk_Rn hμ0 n, xoPp_Rn hμ0, fun _ hv => absurd hv (not_lt.2 (by
      show Om1 ≤ xoVal S l (xoPk n) + xoVal S l xoPp
      rw [xoPp_val]; exact xo_Pp_gt.le.trans le_add_self))⟩

/-- **`E‴` passes the syntactic repair** (at every `μ` with `0 < μ`, `υ_μ < υ_λ`). -/
theorem xoE3_Rn (k : ℕ) {μ : Ordinal.{0}} (hμ0 : 0 < μ)
    (hμl : upsilon μ < upsilon (Nc.ncL S (k : Ordinal.{0})))
    (hτO : upsilon (Nc.ncL S (k : Ordinal.{0}) + (Xj.xjX S k + ω + 1)) < Om1) :
    XoRn S (Nc.ncL S (k : Ordinal.{0})) μ (xoE3 S k) := by
  have hR := xoXj_R (S := S) k hμ0 hμl hτO
  rw [xoXjE_eq] at hR
  have hlo : Wf.WfR (Nc.ncL S (k : Ordinal.{0})) μ (.lo (Nc.ncL S (k : Ordinal.{0}))) := hR.2.1.2
  refine ⟨⟨⟨⟨xo_fin_vd hμ0 (by simpa using natCast_lt_omega0 1), fun _ hv => absurd hv (not_lt.2
        (xo_Om1_le_Om le_rfl))⟩,
      ⟨⟨⟨hlo, xoOmW_Rn hμ0, fun h => h.1.elim⟩, xoOmW_Rn hμ0, fun h => h.1.1.elim⟩, xoPk_Rn hμ0 k,
        fun h => h.1.1.1.elim⟩, fun h => h.2.1.1.1.elim⟩,
    xoR_Rn _ hR.1, fun h => h.2.elim⟩, xoR_Rn _ hR.2.1, fun h => h.1.2.elim⟩

/-- **The image of `E‴` is at least `λ`** (`F′_k` keeps its fixed parts; `π(λ) = υ_μ` is absorbed by `Ω_ω`). -/
theorem xoE3_img_ge (k : ℕ) {μ : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (hμ0 : 0 < μ)
    (hμl : upsilon μ < upsilon (Nc.ncL S (k : Ordinal.{0}))) :
    Nc.ncL S (k : Ordinal.{0}) ≤ xoImg S (Nc.ncL S (k : Ordinal.{0})) μ f (xoE3 S k) := by
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
  have hA : xoImg S l μ f (xoFkA S k) = l := by
    show S.psi (pi (upsilon μ) (upsilon l) l + Om (xoImg S l μ f xoW) + Om (xoImg S l μ f xoW) +
      xoImg S l μ f (xoPk k)) (Om 1) = _
    rw [xoCl_img l μ f xoW xoW_cl, xoCl_img l μ f (xoPk k) (xoPk_cl k), xoW_val, xoPk_val, hpi,
      xo_absorb (hμl.trans hlO)]
    rfl
  show l ≤ xoImg S l μ f (xoFkA S k) + xoImg S l μ f (xoSgX S k) + xoImg S l μ f (xoThX S k)
  rw [hA]; exact le_self_add.trans le_self_add

/-- **The syntactic repair is REFUTED**: wherever the reach formula `r(μ+f(X′)) = υ_{μ+(f(X′)+ω+1)} + f(X′)` holds at
a supply restart (`Sl.SlOff f Os B`, `μ + B ≤ λ`, `X′, h₁, 1 ∈ Os`), its carry fails at `E‴`. -/
theorem xoNaive_ref (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) {β μ B : Ordinal.{0}}
    {f : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}}
    (hβ : Xj.xjX S k + ω + 1 < β) (hb1 : upsilon (Nc.ncL S (k : Ordinal.{0}) + β) ≤ Om1)
    (hμ0 : 0 < μ) (hμl : upsilon μ < upsilon (Nc.ncL S (k : Ordinal.{0})))
    (hO : Sl.SlOff f Os B) (hμB : μ + B ≤ Nc.ncL S (k : Ordinal.{0}))
    (hX : Xj.xjX S k ∈ Os) (h1 : Xj.xjX S k + ω + 1 ∈ Os) (hone : (1 : Ordinal.{0}) ∈ Os)
    (hr : cdR S (μ + f (Xj.xjX S k)) = upsilon (μ + (f (Xj.xjX S k) + ω + 1)) + f (Xj.xjX S k)) :
    ¬ XoCarryN S (Nc.ncL S (k : Ordinal.{0})) β μ f B Os := by
  intro hC
  obtain ⟨hl0, -, -, -, -, -, -, -, -⟩ := Vr.vr_facts (S := S) k
  obtain ⟨-, -, -, hlfix, -, -⟩ := Ww.ww_seg (S := S) k
  obtain ⟨-, hXE, -, -, -⟩ := Xj.xjX_spec (S := S) k
  set l := Nc.ncL S (k : Ordinal.{0}) with hldef
  set X := Xj.xjX S k with hXdef
  have hm := upsilon_normal.strictMono
  have hωX : ω ≤ X := Vo.vo_omega_le hXE (InE.pos hXE)
  have h2c : (2 : Ordinal.{0}) ≤ X := ((natCast_lt_omega0 2).trans_le hωX).le
  have hω2g : ω ^ 2 ∣ X := by
    have h := Vo.vo_e2 ▸ opow_dvd_opow ω h2c
    rwa [hXE] at h
  have hτO : upsilon (l + (X + ω + 1)) < Om1 := (hm ((add_lt_add_iff_left _).2 hβ)).trans_le hb1
  have hle := (hC X hX (InE.pos hXE) hω2g).2.2 (xoE3 S k) (xoE3_WF k hβ hb1)
    ((xoE3_val k).trans (xoXj_val k hν)) (xoE3_Os k h1 hone) (xoE3_Rn k hμ0 hμl hτO)
  have hge := xoE3_img_ge (f := f) k hμ0 hμl
  obtain ⟨q, hq⟩ := hω2g
  have hω : ω + 1 < ω ^ 2 :=
    lt_of_lt_of_le ((add_lt_add_iff_left ω).2 (by exact_mod_cast (show (1 : ℕ) < 2 by norm_num)))
      Vo.vo_om2.le
  have hf : f (X + ω + 1) = f X + ω + 1 := by
    have h := hO.res q (ω + 1) hω
    rw [← hq, ← add_assoc, ← add_assoc] at h
    exact h
  have hlE : InE l := by
    have h := upsPt_inE (upsPt_upsilon hl0)
    rwa [hlfix] at h
  have hlt : cdR S (μ + f X) < l := by
    rw [hr, add_assoc (f X), ← add_assoc (f X) ω 1, ← hf]
    have hB : B ≤ l := (Ordinal.le_add_left B μ).trans hμB
    have h1' : upsilon (μ + f (X + ω + 1)) < l := by
      rw [← hlfix]; exact hm (lt_of_lt_of_le ((add_lt_add_iff_left μ).2 (hO.bd _ h1)) hμB)
    exact hlE.add_lt h1' ((hO.bd _ hX).trans_le hB)
  exact absurd (hge.trans hle) (not_le.2 hlt)

/-! ## The next candidates pass the repaired restriction -/

theorem xo_B2_vd (S : InaccSeq.{0}) {μ : Ordinal.{0}} (hμ0 : 0 < μ) : Vd.VdLtIn Uc.ucB (upsilon μ) :=
  Or.inr ⟨S, le_rfl, Vd.vd_B_lt_th, gamma 0, Lq.lq_gamma_SC 0,
    Gq.gq_gam_le_ups S (upsPt_upsilon hμ0), Ww.ww_B_dat (S := S) (Lq.lq_gamma_SC 0)⟩

theorem xo_lo_R (k : ℕ) {μ : Ordinal.{0}} (hμ0 : 0 < μ) (hμl : upsilon μ < upsilon (Nc.ncL S (k : Ordinal.{0}))) :
    Wf.WfR (Nc.ncL S (k : Ordinal.{0})) μ (.lo (Nc.ncL S (k : Ordinal.{0}))) := by
  have hR := xoXj_R (S := S) k hμ0 hμl
  obtain ⟨hl0, -, -, -, -, -, -, -, -⟩ := Vr.vr_facts (S := S) k
  obtain ⟨-, hu1O, hlu1, hlfix, -, -⟩ := Ww.ww_seg (S := S) k
  set l := Nc.ncL S (k : Ordinal.{0}) with hldef
  have hμE : InE (upsilon μ) := upsPt_inE (upsPt_upsilon hμ0)
  have hlE : InE (upsilon l) := upsPt_inE (upsPt_upsilon hl0)
  have hlO : upsilon l < Om1 := by rw [hlfix]; exact hlu1.trans hu1O
  have hBl : Bases (upsilon μ) (upsilon l) := ⟨hμE, hlE, hμl, hlO⟩
  show l ∈ TB (upsilon l) (upsilon μ)
  exact (congrArg (· ∈ TB (upsilon l) (upsilon μ)) hlfix).mp (pi_base hBl).1

/-- **`ϑ^{u₂}(Ω₁·(B₂ + u₁) + λ)` passes the repaired restriction.** -/
theorem xoU1_R (k : ℕ) {μ : Ordinal.{0}} (hμ0 : 0 < μ)
    (hμl : upsilon μ < upsilon (Nc.ncL S (k : Ordinal.{0}))) :
    XoR S (Nc.ncL S (k : Ordinal.{0})) μ (xoU1E S k) := by
  obtain ⟨hl0, -, -, -, -, -, -, -, -⟩ := Vr.vr_facts (S := S) k
  obtain ⟨-, hu1O, hlu1, hlfix, -, -⟩ := Ww.ww_seg (S := S) k
  set l := Nc.ncL S (k : Ordinal.{0}) with hldef
  have hm := upsilon_normal.strictMono
  have hμE : InE (upsilon μ) := upsPt_inE (upsPt_upsilon hμ0)
  have hu1E : InE (upsilon (l + 1)) := upsPt_inE (upsPt_upsilon (hl0.trans_le le_self_add))
  have hlu : upsilon l < upsilon (l + 1) := hm (lt_add_one l)
  have hB1 : Bases (upsilon μ) (upsilon (l + 1)) := ⟨hμE, hu1E, hμl.trans hlu, hu1O⟩
  exact ⟨⟨xo_B2_vd S hμ0, fun p hp => (pi_base hB1).1.2 (Finset.mem_coe.2 hp), fun h => h.2.elim⟩,
    xo_lo_R k hμ0 hμl⟩

/-- **`ϑ^{u₂}(Ω₁·(B₂ + X′) + λ)` passes the repaired restriction.** -/
theorem xoNest_R (k : ℕ) {μ : Ordinal.{0}} (hμ0 : 0 < μ)
    (hμl : upsilon μ < upsilon (Nc.ncL S (k : Ordinal.{0}))) :
    XoR S (Nc.ncL S (k : Ordinal.{0})) μ (xoNestE S k) :=
  ⟨⟨xo_B2_vd S hμ0, ⟨⟨xo_B2_vd S hμ0, xo_lo_R k hμ0 hμl, fun h => h.2.elim⟩, xo_lo_R k hμ0 hμl⟩,
    fun h => h.2.elim⟩, xo_lo_R k hμ0 hμl⟩

/-! ## The offset obligation at `X′` is consistent with `Sl.SlOff` -/

/-- The offset map `x ↦ x` below `X`, `X + d ↦ Y + d`. -/
noncomputable def xoOffF (X Y : Ordinal.{0}) (x : Ordinal.{0}) : Ordinal.{0} :=
  if x < X then x else Y + (x - X)

theorem xo_dvd2 {X : Ordinal.{0}} (hX : InE X) : ω ^ 2 ∣ X := by
  have hωX : ω ≤ X := Vo.vo_omega_le hX (InE.pos hX)
  have h2c : (2 : Ordinal.{0}) ≤ X := ((natCast_lt_omega0 2).trans_le hωX).le
  have h := Vo.vo_e2 ▸ opow_dvd_opow ω h2c
  rwa [hX] at h

/-- **An offset map on `{1, X, X+ω+1}` with `f(X) = Y`** for all `ε`-numbers `X, Y > 1` (bound `Y + ω²`): the carry
obligation `X′_μ ≤ f(X′)` at `X′` (`Xo.xoXj_obl`) does not contradict `Sl.SlOff`. -/
theorem xoOff_wit {X Y : Ordinal.{0}} (hX : InE X) (hY : InE Y) (hX1 : 1 < X) (hY1 : 1 < Y) :
    Sl.SlOff (xoOffF X Y) {1, X, X + ω + 1} (Y + ω ^ 2) ∧ xoOffF X Y X = Y ∧ xoOffF X Y 1 = 1 := by
  obtain ⟨p, hp⟩ := xo_dvd2 hX
  have hω : ω + 1 < ω ^ 2 :=
    lt_of_lt_of_le ((add_lt_add_iff_left ω).2 (by exact_mod_cast (show (1 : ℕ) < 2 by norm_num)))
      Vo.vo_om2.le
  have hω0 : (0 : Ordinal.{0}) < ω ^ 2 := lt_of_le_of_lt zero_le hω
  have hf0 : xoOffF X Y 0 = 0 := if_pos (InE.pos hX)
  have hf1 : xoOffF X Y 1 = 1 := if_pos hX1
  have hfX : xoOffF X Y X = Y := by
    unfold xoOffF; rw [if_neg (lt_irrefl X), Ordinal.sub_self, add_zero]
  have hXh : X < X + ω + 1 := by
    rw [add_assoc]; exact lt_add_of_pos_right X (lt_of_le_of_lt zero_le (lt_add_one ω))
  have hfh : xoOffF X Y (X + ω + 1) = Y + (ω + 1) := by
    unfold xoOffF; rw [if_neg (not_lt.2 hXh.le), add_assoc, Ordinal.add_sub_cancel]
  have hYh : Y < Y + (ω + 1) := lt_add_of_pos_right Y (lt_of_le_of_lt zero_le (lt_add_one ω))
  refine ⟨⟨hf0, fun q r hr => ?_, fun q => ?_, ?_, ?_⟩, hfX, hf1⟩
  · by_cases hq : ω ^ 2 * q < X
    · have hqp : q < p := by rw [hp] at hq; exact lt_of_mul_lt_mul_left' hq
      have hlt : ω ^ 2 * q + r < X := by
        rw [hp]
        calc ω ^ 2 * q + r < ω ^ 2 * q + ω ^ 2 := (add_lt_add_iff_left _).2 hr
          _ = ω ^ 2 * (q + 1) := by rw [mul_add_one]
          _ ≤ ω ^ 2 * p := mul_le_mul_right (Order.add_one_le_of_lt hqp) _
      unfold xoOffF; rw [if_pos hlt, if_pos hq]
    · have hq' : X ≤ ω ^ 2 * q := not_lt.1 hq
      have hqr : ¬ ω ^ 2 * q + r < X := not_lt.2 (hq'.trans le_self_add)
      unfold xoOffF; rw [if_neg hqr, if_neg hq, add_assoc]
      congr 1
      apply Ordinal.sub_eq_of_add_eq
      rw [← add_assoc, Ordinal.add_sub_cancel_of_le hq']
  · by_cases hq : ω ^ 2 * q < X
    · unfold xoOffF; rw [if_pos hq]; exact dvd_mul_right _ _
    · unfold xoOffF; rw [if_neg hq, hp, ← Ordinal.mul_sub]
      exact Ge.dvd_add' (xo_dvd2 hY) (dvd_mul_right _ _)
  · have o01 : (0 : Ordinal.{0}) < 1 := zero_lt_one
    have o0X : (0 : Ordinal.{0}) < X := InE.pos hX
    have o0h : (0 : Ordinal.{0}) < X + ω + 1 := o0X.trans hXh
    have o1h : (1 : Ordinal.{0}) < X + ω + 1 := hX1.trans hXh
    have i0Y : (0 : Ordinal.{0}) < Y := InE.pos hY
    have i0h : (0 : Ordinal.{0}) < Y + (ω + 1) := i0Y.trans hYh
    have i1h : (1 : Ordinal.{0}) < Y + (ω + 1) := hY1.trans hYh
    intro a ha b hb hab
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      simp only [hf0, hf1, hfX, hfh] <;>
      first
        | assumption
        | exact absurd hab (lt_irrefl _)
        | exact absurd hab (lt_asymm o01)
        | exact absurd hab (lt_asymm o0X)
        | exact absurd hab (lt_asymm o0h)
        | exact absurd hab (lt_asymm hX1)
        | exact absurd hab (lt_asymm o1h)
        | exact absurd hab (lt_asymm hXh)
  · intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · rw [hf1]; exact hY1.trans (lt_add_of_pos_right Y hω0)
    · rw [hfX]; exact lt_add_of_pos_right Y hω0
    · rw [hfh]; exact (add_lt_add_iff_left Y).2 hω


/-- **Which points lose their leaves**: a point `p ∈ [υ_μ, υ_λ)` is never a moving leaf `lo p` of a restricted term
(`R2Skel.SkSX.skSX_notTB`), and never a fixed part (`xoR_fixed`); such points had no correct image (`π` is free there). -/
theorem xo_gap_noLeaf {l μ p : Ordinal.{0}} (hB : Bases (upsilon μ) (upsilon l)) (h1 : upsilon μ ≤ p)
    (h2 : p < upsilon l) : ¬ XoR S l μ (.old (.lo p)) :=
  R2Skel.SkSX.skSX_notTB hB h1 h2

end Googology.Trans.PoR.InaccPsi.R2.Xo

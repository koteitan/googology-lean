import Googology.Trans.PoR.InaccPsi.R2.VoNoGo

/-!
# The term road hypotheses fail at every `L(k)` as well

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

The term forms `Uy.UyForm` and `Vl.VlForm` write the inner reach as the value of a countable term of `Un.UnT` over
the single base `τ = υ_{λ+h}`.  As for `Vl.VlGd` (`Vo.voGd_inv`), its parts below `τ` are sums of leaves and every
`ϑᵗ`-head is `≥ τ` and additive principal (`R2.vt_memTwo`, with the argument in `Tᵗ` from `Uy.uy_arg_T`,
`Uy.uyMem`, `Vi.Nz`, `Ur.Ngr`).  So at the witness of `Vo.voWit` the forms `UbF3 ∨ UbForm ∨ UyForm ∨ VlForm` of
`Vl.VlTyGen` and `Vl.VlGen` all fail.

* `vo_vt_inv` (the claim at a `ϑᵗ`-head), `voUy_inv` (**values of terms with `Uy.QsY`**), `voVi_inv` (**values of
  terms with `Vi.ZW`**);
* `voFormsTy_fail` (**no `UyForm`, no `VlForm` at the reach `τ + c`**);
* `voNoGoTy` (**`¬ Vl.VlTyVis` at `L(k)`**), `voNoGoVis` (**`¬ Vl.VlVisGen` at `L(k)`**), `voNoGoTy_road`,
  `voNoGoVis_road` (**`Vl.vlTyRoad` and `Vl.vlRoadGen` are vacuous under `hU, hV, hVt, hL`**);
* `voNoGoTy_uy`, `voNoGoTy_ur`, `voNoGoTy_un`, `voNoGoTy_uk`, `voNoGoTy_uh`, `voNoGoTy_ue`, `voNoGoTy_ub`,
  `voNoGoTy_ty` (**the same for `Uy.UyTyVis`, `Ur.UrTyVis`, `Un.UnTyVis`, `Uk.UkTyVis`, `Uh.UhTyVis`,
  `Ue.UeTyVis`, `Ub.UbTyVis`, `Ty.TyVisGen`**, through the existing implications).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vo

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Tk Googology.Trans.PoR.InaccPsi.R2.Ub
  Googology.Trans.PoR.InaccPsi.R2.Vl Googology.Trans.PoR.InaccPsi.R2.Un Googology.Trans.PoR.InaccPsi.R2.Ur
  Googology.Trans.PoR.InaccPsi.R2.Uy Googology.Trans.PoR.InaccPsi.R2.Vi

/-- **The claim at a `ϑᵗ`-head**: `ϑᵗ(ξ)`, `ξ ∈ Tᵗ ∩ Ω₂`, is `≥ τ` and additive principal, so it is not below `τ`
and not `τ + c` (`0 < c < τ`). -/
theorem vo_vt_inv {τ ξ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hξ : ξ ∈ Tset τ) (hξ2 : ξ < OmTwo)
    (P : Ordinal.{0} → Prop) :
    (vt τ ξ < τ → Indec (vt τ ξ) → P (vt τ ξ)) ∧ ∀ c, 0 < c → c < τ → Indec c → ¬ P c → vt τ ξ ≠ τ + c := by
  obtain ⟨-, hge, -, hI, -⟩ := vt_memTwo hτ hτ1 hξ hξ2
  exact ⟨fun h => absurd h (not_lt.2 hge), fun c hc0 hcτ _ _ e => vo_not_indec_add hc0 hcτ (e ▸ hI)⟩

/-- The claim at a leaf below `τ` or additive principal. -/
theorem vo_leaf_inv {τ p : Ordinal.{0}} {P : Ordinal.{0} → Prop} (hp : P p) (hP : p < τ ∨ Indec p) :
    (p < τ → Indec p → P p) ∧ ∀ c, 0 < c → c < τ → Indec c → ¬ P c → p ≠ τ + c := by
  refine ⟨fun _ _ => hp, fun c hc0 hcτ _ _ e => ?_⟩
  rcases hP with h | h
  · exact absurd (e ▸ h) (not_lt.2 le_self_add)
  · exact vo_not_indec_add hc0 hcτ (e ▸ h)

/-- The claim at `τ` itself. -/
theorem vo_base_inv {τ : Ordinal.{0}} (P : Ordinal.{0} → Prop) :
    (τ < τ → Indec τ → P τ) ∧ ∀ c, 0 < c → c < τ → Indec c → ¬ P c → τ ≠ τ + c := by
  refine ⟨fun h => absurd h (lt_irrefl _), fun c hc0 _ _ _ e => ?_⟩
  have e' : τ + 0 = τ + c := by rw [add_zero]; exact e
  exact hc0.ne (add_left_cancel e')

/-- The claim at a sum from the claims at the summands. -/
theorem vo_add_inv {τ a b : Ordinal.{0}} (hτ : InE τ) {P : Ordinal.{0} → Prop}
    (ha : (a < τ → Indec a → P a) ∧ ∀ c, 0 < c → c < τ → Indec c → ¬ P c → a ≠ τ + c)
    (hb : (b < τ → Indec b → P b) ∧ ∀ c, 0 < c → c < τ → Indec c → ¬ P c → b ≠ τ + c) :
    (a + b < τ → Indec (a + b) → P (a + b)) ∧
      ∀ c, 0 < c → c < τ → Indec c → ¬ P c → a + b ≠ τ + c := by
  refine ⟨fun hy hI => ?_, fun c hc0 hcτ hcI hPc e => ?_⟩
  · rcases vo_prin_sum hI (rfl : a + b = _) with h0 | hb'
    · subst h0; rw [add_zero] at hy hI ⊢; exact ha.1 hy hI
    · rw [← hb'] at hy hI ⊢; exact hb.1 hy hI
  · rcases vo_sum_cases hτ hcI e with ⟨ha', -⟩ | hb' | hb'
    · exact ha.2 c hc0 hcτ hcI hPc ha'
    · exact hPc (hb' ▸ hb.1 (hb' ▸ hcτ) (hb' ▸ hcI))
    · exact hb.2 c hc0 hcτ hcI hPc hb'

/-- **The values of countable terms with `Uy.QsY κ`** over `τ` (leaves `P`, below `τ` or additive principal, in
`Tᵗ`). -/
theorem voUy_inv {κ τ : Ordinal.{0}} (hB : Bases κ τ) {P : Ordinal.{0} → Prop}
    (hP : ∀ p, P p → p < τ ∨ Indec p) (hPT : ∀ p, P p → p ∈ Tset τ) :
    ∀ t : UnT false, UnT.Lv P t → WFr τ t → QsY κ t →
      (UnT.ev τ t < τ → Indec (UnT.ev τ t) → P (UnT.ev τ t)) ∧
        ∀ c, 0 < c → c < τ → Indec c → ¬ P c → UnT.ev τ t ≠ τ + c
  | .par p, hl, _, _ => vo_leaf_inv hl (hP p hl)
  | .add s t, hl, hw, hq =>
    vo_add_inv hB.2.1 (voUy_inv hB hP hPT s hl.1 hw.1 hq.1) (voUy_inv hB hP hPT t hl.2 hw.2 hq.2)
  | .base, _, _, _ => vo_base_inv P
  | .th1 s, hl, hw, hq => by
    have hτ1 := hB.2.2.2
    have h1 : (1 : Ordinal.{0}) ∈ Tset τ := Uh.uh_T_le hB.2.1 hτ1 (Ub.ub_one_lt hB.2.1).le
    have hO : (1 : Ordinal.{0}) < Om1 := (Ub.ub_one_lt hB.2.1).trans hτ1
    exact vo_vt_inv hB.2.1 hτ1 (vzT_add hB.2.1 hτ1 h1 (uyMem hB s (UnT.Lv_mono hPT s hl) hw.1 hq))
      ((Om1_add_lt hO hw.2).trans Uc.uc_Om1_lt_Om2) P
  | .thc _ r, hl, hw, hq => by
    obtain ⟨h1, h2⟩ := uy_arg_T hB hq.1 (uyMem hB r (UnT.Lv_mono hPT r hl) hw.1 hq.2) hw.2
    exact vo_vt_inv hB.2.1 hB.2.2.2 h1 h2 P
  | .thg _ G _, _, hw, _ =>
    vo_vt_inv hB.2.1 hB.2.2.2 hw.2.2.mem (Uk.arg_lt2 (ev_lt_Er G hw.1) hw.2.2.r1) P

/-- **The values of countable terms with `Vi.ZW τ`** over `τ` (leaves `P`, below `τ` or additive principal, in
`Tᵗ`). -/
theorem voVi_inv {κ τ : Ordinal.{0}} (hB : Bases κ τ) {P : Ordinal.{0} → Prop}
    (hP : ∀ p, P p → p < τ ∨ Indec p) (hPT : ∀ p, P p → p ∈ Tset τ) :
    ∀ t : UnT false, UnT.Lv P t → WFr τ t → ZW τ t →
      (UnT.ev τ t < τ → Indec (UnT.ev τ t) → P (UnT.ev τ t)) ∧
        ∀ c, 0 < c → c < τ → Indec c → ¬ P c → UnT.ev τ t ≠ τ + c
  | .par p, hl, _, _ => vo_leaf_inv hl (hP p hl)
  | .add s t, hl, hw, hz =>
    vo_add_inv hB.2.1 (voVi_inv hB hP hPT s hl.1 hw.1 hz.1) (voVi_inv hB hP hPT t hl.2 hw.2 hz.2)
  | .base, _, _, _ => vo_base_inv P
  | .th1 s, hl, hw, hz => by
    have hτ1 := hB.2.2.2
    have h1 : (1 : Ordinal.{0}) ∈ Tset τ := Uh.uh_T_le hB.2.1 hτ1 (Ub.ub_one_lt hB.2.1).le
    have hO : (1 : Ordinal.{0}) < Om1 := (Ub.ub_one_lt hB.2.1).trans hτ1
    exact vo_vt_inv hB.2.1 hτ1 (vzT_add hB.2.1 hτ1 h1 (viMem hB s (UnT.Lv_mono hPT s hl) hw.1 hz))
      ((Om1_add_lt hO hw.2).trans Uc.uc_Om1_lt_Om2) P
  | .thc _ _, _, hw, hz => vo_vt_inv hB.2.1 hB.2.2.2 hz.1.mem (nz_arg_lt hz.1 hw.2) P
  | .thg _ G _, _, hw, _ =>
    vo_vt_inv hB.2.1 hB.2.2.2 hw.2.2.mem (Uk.arg_lt2 (ev_lt_Er G hw.1) hw.2.2.r1) P

variable {S : InaccSeq.{0}}

/-- **No term form at the reach `τ + c`** (the hypotheses of `Vo.voForms_fail`): neither `Uy.UyForm` nor
`Vl.VlForm` holds at `g`. -/
theorem voFormsTy_fail {l β g e : Ordinal.{0}} (hl0 : 0 < l)
    (hr : cdR S (l + g) = upsilon (l + (g + ω + 1)) + ω ^ e)
    (hcN : ω ^ e ∈ NonEAP) (hc1 : upsilon (succ l) ≤ ω ^ e) (hcτ : ω ^ e < upsilon (l + (g + ω + 1)))
    (hτ1 : upsilon (l + (g + ω + 1)) < Om1) :
    ¬ UyForm S l β g ∧ ¬ VlForm S l β g := by
  have hm := upsilon_normal.strictMono
  set X := l + (g + ω + 1) with hX
  have hX0 : 0 < X := hl0.trans_le le_self_add
  have hτE : InE (upsilon X) := upsPt_inE (upsPt_upsilon hX0)
  have hlτ : upsilon l < upsilon (succ l) := hm (lt_succ l)
  have hc0 : 0 < ω ^ e := opow_pos e omega0_pos
  have hseg := vo_segX (l := l) hX0 hr hcτ
  have hB : Bases (upsilon l) (upsilon X) := ⟨upsPt_inE (upsPt_upsilon hl0), hτE, hlτ.trans_le hc1 |>.trans hcτ, hτ1⟩
  -- the leaf predicate of both forms, at `h` with `l + h = X`
  have hleaf : ∀ h, l + h = X →
      (∀ p, (p < upsilon l ∨ ∃ h', h' ≤ h ∧ p = upsilon (l + h')) → p < upsilon X ∨ Indec p) ∧
      (∀ p, (p < upsilon l ∨ ∃ h', h' ≤ h ∧ p = upsilon (l + h')) → p ∈ Tset (upsilon X)) ∧
      ¬ (ω ^ e < upsilon l ∨ ∃ h', h' ≤ h ∧ ω ^ e = upsilon (l + h')) := by
    intro h hXe
    refine ⟨?_, ?_, vo_notLeaf hl0 hcN hc1 _ fun p (hp : p < upsilon l ∨ ∃ h', h' ≤ h ∧ p = upsilon (l + h')) =>
      hp.imp id fun ⟨h', _, e'⟩ => ⟨h', e'⟩⟩
    · rintro p (hp | ⟨h', -, rfl⟩)
      · exact Or.inl (hp.trans (hlτ.trans_le hc1 |>.trans hcτ))
      · exact Or.inr (inE_indec (upsPt_inE (upsPt_upsilon (hl0.trans_le le_self_add))))
    · rintro p (hp | ⟨h', hh', rfl⟩)
      · exact Uh.uh_T_le hτE hτ1 (hp.trans (hlτ.trans_le hc1 |>.trans hcτ)).le
      · exact Uh.uh_T_le hτE hτ1 (hm.monotone (hXe ▸ (add_le_add_iff_left l).2 hh'))
  refine ⟨fun hF => ?_, fun hF => ?_⟩
  · obtain ⟨h, t, -, -, hq, hW, hL, h1, h2, hev⟩ := hF
    have hXe := hseg h h1 h2
    obtain ⟨hP, hPT, hnP⟩ := hleaf h hXe
    rw [hXe] at hW hev
    rw [hr] at hev
    exact (voUy_inv hB hP hPT t hL hW hq).2 _ hc0 hcτ hcN.1 hnP hev
  · obtain ⟨h, t, -, -, -, -, -, hZ, hW, hL, -, -, h1, h2, hev⟩ := hF
    have hXe := hseg h h1 h2
    obtain ⟨hP, hPT, hnP⟩ := hleaf h hXe
    rw [hXe] at hW hev hZ
    rw [hr] at hev
    exact (voVi_inv hB hP hPT t hL hW hZ).2 _ hc0 hcτ hcN.1 hnP hev

/-- **The four forms of `Vl.VlTyGen` / `Vl.VlGen` all fail at the witness offset.** -/
theorem voAllForms_fail {l β g e : Ordinal.{0}} (hl0 : 0 < l)
    (hr : cdR S (l + g) = upsilon (l + (g + ω + 1)) + ω ^ e)
    (hcN : ω ^ e ∈ NonEAP) (hc1 : upsilon (succ l) ≤ ω ^ e) (hcτ : ω ^ e < upsilon (l + (g + ω + 1)))
    (hτ1 : upsilon (l + (g + ω + 1)) < Om1) (hβ : g + ω + 2 ≤ β) :
    ¬ (UbF3 S l β g ∨ UbForm S l β g ∨ UyForm S l β g ∨ VlForm S l β g) := by
  have h1 := voForms_fail (S := S) hl0 hr hcN hc1 hcτ hτ1 hβ
  have h2 := voFormsTy_fail (S := S) (β := β) hl0 hr hcN hc1 hcτ hτ1
  rintro (h | h | h | h)
  · exact h1.1 h
  · exact h1.2.1 h
  · exact h2.1 h
  · exact h2.2 h

/-- **The term road hypothesis `Vl.VlTyVis` is false at `L(k)`** (given `L(k+1) ≤ ν_C`), for every window `w`. -/
theorem voNoGoTy (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) (w : Ordinal.{0}) :
    ¬ VlTyVis S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S (k : Ordinal.{0}) + Te.teW (Nc.ncL S (k : Ordinal.{0})))) w := by
  intro hvis
  obtain ⟨ν, g, e, hCR, hcw, hb, hlν, hcov, hiso, hg0, hgd, hβ, hr, hN, hc1, hcτ, hτ1, hl0⟩ := voWit k hν
  obtain ⟨β, hνβ, -, hG⟩ := hvis ν hCR hcw hb hlν hcov hiso
  obtain ⟨hgβ, hβ2⟩ := hβ β hνβ
  exact voAllForms_fail (S := S) hl0 hr hN hc1 hcτ hτ1 hβ2 (hG.1 g hg0 hgβ hgd)

/-- **The realizer road hypothesis `Vl.VlVisGen` is false at `L(k)`** (given `L(k+1) ≤ ν_C`). -/
theorem voNoGoVis (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) :
    ¬ VlVisGen S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S (k : Ordinal.{0}) + Te.teW (Nc.ncL S (k : Ordinal.{0})))) := by
  intro hvis
  obtain ⟨ν, g, e, hCR, hcw, hb, hlν, hcov, hiso, hg0, hgd, hβ, hr, hN, hc1, hcτ, hτ1, hl0⟩ := voWit k hν
  obtain ⟨β, hνβ, -, hG⟩ := hvis ν hCR hcw hb hlν hcov hiso
  obtain ⟨hgβ, hβ2⟩ := hβ β hνβ
  exact voAllForms_fail (S := S) hl0 hr hN hc1 hcτ hτ1 hβ2 (hG.2.1 g hg0 hgβ hgd)

section Road

variable (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
  (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
  (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
  (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
include hU hV hVt hL

/-- **`Vl.vlTyRoad` is vacuous**: under `hU, hV, hVt, hL` its hypothesis `hn n` is false for every `n` (and `h0`
too). -/
theorem voNoGoTy_road :
    (¬ ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      VlTyVis S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))) (upsilon Rz.rzLam)) ∧
    ∀ n : ℕ, ¬ ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      VlTyVis S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
        (Nc.ncL S (n : Ordinal.{0})) := by
  refine ⟨fun h => ?_, fun n h =>
    voNoGoTy (n + 1) (vo_L_le_nu hU hV hVt hL (n + 1)) _ (h _ (Te.teRst_L (n + 1)) (Te.teUps_L (n + 1)).symm)⟩
  have h0 := voNoGoTy (S := S) 0 (vo_L_le_nu hU hV hVt hL 0) (upsilon Rz.rzLam)
  have hl := Te.teRst_L (S := S) 0
  have he := (Te.teUps_L (S := S) 0).symm
  simp only [Nat.cast_zero, zero_add, Nat.cast_one] at h0 hl he
  exact h0 (h _ hl he)

/-- **`Vl.vlRoadGen` is vacuous**: under `hU, hV, hVt, hL` its hypotheses `h0` and `hn n` are false. -/
theorem voNoGoVis_road :
    (¬ ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      VlVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0)))) ∧
    ∀ n : ℕ, ¬ ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      VlVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))) := by
  refine ⟨fun h => ?_, fun n h =>
    voNoGoVis (n + 1) (vo_L_le_nu hU hV hVt hL (n + 1)) (h _ (Te.teRst_L (n + 1)) (Te.teUps_L (n + 1)).symm)⟩
  have h0 := voNoGoVis (S := S) 0 (vo_L_le_nu hU hV hVt hL 0)
  have hl := Te.teRst_L (S := S) 0
  have he := (Te.teUps_L (S := S) 0).symm
  simp only [Nat.cast_zero, zero_add, Nat.cast_one] at h0 hl he
  exact h0 (h _ hl he)

end Road

/-! ## The earlier term roads, through the existing implications -/

variable (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) (w : Ordinal.{0})
include hν

theorem voNoGoTy_uy : ¬ Uy.UyTyVis S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))
    (upsilon (Nc.ncL S (k : Ordinal.{0}) + Te.teW (Nc.ncL S (k : Ordinal.{0})))) w := fun h =>
  voNoGoTy k hν w (vlTyVis_of_uy h)

theorem voNoGoTy_ur : ¬ Ur.UrTyVis S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))
    (upsilon (Nc.ncL S (k : Ordinal.{0}) + Te.teW (Nc.ncL S (k : Ordinal.{0})))) w := fun h =>
  voNoGoTy_uy k hν w (Uy.uyTyVis_of_ur h)

theorem voNoGoTy_un : ¬ Un.UnTyVis S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))
    (upsilon (Nc.ncL S (k : Ordinal.{0}) + Te.teW (Nc.ncL S (k : Ordinal.{0})))) w := fun h =>
  voNoGoTy_uy k hν w (Uy.uyTyVis_of_un h)

theorem voNoGoTy_uk : ¬ Uk.UkTyVis S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))
    (upsilon (Nc.ncL S (k : Ordinal.{0}) + Te.teW (Nc.ncL S (k : Ordinal.{0})))) w := fun h =>
  voNoGoTy_un k hν w (Un.unTyVis_of_uk h)

theorem voNoGoTy_uh : ¬ Uh.UhTyVis S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))
    (upsilon (Nc.ncL S (k : Ordinal.{0}) + Te.teW (Nc.ncL S (k : Ordinal.{0})))) w := fun h =>
  voNoGoTy_uk k hν w (Uk.ukTyVis_of_uh h)

theorem voNoGoTy_ue : ¬ Ue.UeTyVis S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))
    (upsilon (Nc.ncL S (k : Ordinal.{0}) + Te.teW (Nc.ncL S (k : Ordinal.{0})))) w := fun h => by
  have hO : upsilon (Nc.ncL S (k : Ordinal.{0})) < Om1 := by
    rw [Te.teUps_L, Lw.lw_L_eq, Br.Om1_eq]; exact Nm.Pv_lt_Om1 S _
  exact voNoGoTy_uh k hν w (Uh.uhTyVis_of_ue hO h)

theorem voNoGoTy_ub : ¬ Ub.UbTyVis S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))
    (upsilon (Nc.ncL S (k : Ordinal.{0}) + Te.teW (Nc.ncL S (k : Ordinal.{0})))) w := fun h =>
  voNoGoTy_ue k hν w (Ue.ueTyVis_of_ub h)

theorem voNoGoTy_ty : ¬ Ty.TyVisGen S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))
    (upsilon (Nc.ncL S (k : Ordinal.{0}) + Te.teW (Nc.ncL S (k : Ordinal.{0})))) w := fun h =>
  voNoGoTy_ub k hν w (Ub.ubTyVis_of_ty h)

end Googology.Trans.PoR.InaccPsi.R2.Vo

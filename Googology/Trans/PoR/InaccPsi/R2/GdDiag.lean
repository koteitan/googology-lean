import Googology.Trans.PoR.InaccPsi.R2.GdTow
import Googology.Trans.PoR.InaccPsi.R2.GcTowLoc

/-!
# THE LAYER OF `Γ_{x+x} = ϑˣ(Ω₁·Ω₁ + x)`: the union of the gated tower below the base

The sublayers `Γ_{x+1+ν}` of the diagonal top exist only above `ν` (`R2.GdTow`, gate `ν`).  A term of the diagonal
layer is a pair `(ν, t)` with `t` a term of `gdB ν`; its constants are `ν` and those of `t`, so its side condition
`ν < x` opens the gate.  The union is an ordinary (ungated) term system and layer:

* `gd_gq_lt_D` (**`ϑˣ(Ω₁·Ω₁ + j) < ϑˣ(Ω₁·Ω₁ + x)` for every `j < x`**);
* `gdDSys : XtSys` (rep by `Gc.gcD_lt_iff`, IMG / RS / EXACT from the gated layers above their gates), `gdDL : XtLay`
  (**the layer with top `Γ_{x+x}`**: EXACT of the top `Gc.gcD_pi`, the top witness `Gc.GcDK.gcDiagWit`), `gdDB : LpB`
  (the new base package: the ladder `Lp.lpSys gdDB n` and everything generic over a base apply);
* `gdD_topPkg`, `gdD_blk` (**Theorem BLK^O below `υ_{Λ⁺(gdDSys)}`**), `gdD_reach` (**the exact reach
  `lh(ρ_λ) = δ_λ + O_D(λ)` at every restart below `Λ⁺(gdDSys)`**), `gdD_spec` (the offset is a general specification
  up to `Λ⁺`);
* `gdD_topIn_gc` (the top of every `Gc.gcB α`, `1 + α < ε₀`, is a term of the diagonal), `gdD_gt_gc`
  (**`Λ⁺(gcB α) < Λ(gdDSys)`**), `gdD_past_gc` (**`ι(Γ_{Ω₁+ε₀}) ≤ Λ(gdDSys) < Λ⁺(gdDSys)`**: the diagonal layer
  lies past every frontier of round 75), `gdD_eq_gc` (`O_D = O_{gcB α}` below `Λ⁺(gcB α)`);
* `gdD_ladder` (**`Λ⁺(gdDSys) < Λ(lpSys gdDB 1)`** and `Λ⁺(lpSys gdDB n) < Λ(lpSys gdDB (n+1))`: the ladder over the
  diagonal).

No new axiom.  New definitions: `gdDSys`, `gdDL`, `gdDB`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Ly Lu
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Nm

/-- **`ϑˣ(Ω₁·Ω₁ + j) < ϑˣ(Ω₁·Ω₁ + x)`** for every `j < x`. -/
theorem gd_gq_lt_D {x j : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (h : j < x) : gq j x < gq x x := by
  have h1T : (1 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 (lu_one_lt_E hx).le
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  have h1Ω : (1 : Ordinal.{0}) < Om1 := (lu_one_lt_E hx).trans hx1
  have h0Ω : (0 : Ordinal.{0}) < Om1 := hx.pos.trans hx1
  obtain ⟨hjT, hj1⟩ := gq_cst hx hx1 h
  have hkT : x ∈ Tset x := mem_T_of_le hx hx1 le_rfl
  obtain ⟨-, hxv, -, -, -⟩ := gcq_facts hx hx1 le_rfl
  have e1 : ∀ z, Om1 * (Om1 * 1 + 0) + z = Om1 * Om1 + z := fun z => by rw [mul_one, add_zero]
  have := lqVt_lt hx hx1 h1T h1Ω h0T h0Ω hjT hj1 le_rfl h1T h1Ω h0T h0Ω hkT hx1
    (by rw [e1, e1]; exact (add_lt_add_iff_left _).2 h)
    (by rw [e1]; exact (lu_one_lt_E hx).trans hxv) (by rw [e1]; exact hx.pos.trans hxv)
    (by rw [e1]; exact h.trans hxv)
  rw [e1, e1] at this
  exact this

theorem gdD_top_lt {x ν : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hν : ν < x) :
    (gdB ν).K.sys.top x < gq x x := by
  rw [gdB_top hx hx1 hν]; exact gd_gq_lt_D hx hx1 (gd_one_add_lt' hx hν)

theorem gdD_val_lt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (p : Σ ν : Ordinal.{0}, (gdB ν).K.sys.Tm)
    (h : p.1 < x ∧ (gdB p.1).K.sys.CB p.2 x) : (gdB p.1).K.sys.val p.2 x < gq x x :=
  ((gdB p.1).K.lt_top_E x hx hx1 (gdB_gate h.1) p.2 h.2).trans (gdD_top_lt hx hx1 h.1)

/-- **The diagonal term system**: the pairs `(ν, t)`, `t` a term of `gdB ν`, side condition `ν < x`; top `Γ_{x+x}`. -/
noncomputable def gdDSys : XtSys where
  Tm := Σ ν : Ordinal.{0}, (gdB ν).K.sys.Tm
  val := fun p x => (gdB p.1).K.sys.val p.2 x
  CB := fun p x => p.1 < x ∧ (gdB p.1).K.sys.CB p.2 x
  cs := fun p => p.1 :: (gdB p.1).K.sys.cs p.2
  cst := fun c => ⟨0, (gdB 0).K.sys.cst c⟩
  top := fun x => gq x x
  cb_cst := fun p s h c hc => by
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · exact (gdB p.1).K.sys.cb_cst p.2 s h.2 c hc
  cb_iff := fun p s s' h h' => ⟨h' p.1 List.mem_cons_self,
    (gdB p.1).K.sys.cb_iff p.2 s s' h.2 (fun c hc => h' c (List.mem_cons_of_mem _ hc))⟩
  val_cst := fun c x => (gdB 0).K.sys.val_cst c x
  cb_cstI := fun c x h => ⟨lt_of_le_of_lt zero_le h, (gdB 0).K.sys.cb_cstI c x h⟩
  lt_top := fun l hl hl1 p h => gdD_val_lt (ups_inE hl) (ups_lt_Om1 l hl1) p h
  one_le_top := fun l hl hl1 =>
    one_le_iff_pos.2 (gcq_facts (ups_inE hl) (ups_lt_Om1 l hl1) le_rfl).2.2.2.1.pos
  rep := fun l hl hl1 v hv => by
    have hxE := ups_inE hl
    have hx1 := ups_lt_Om1 l hl1
    obtain ⟨ν, hν, hvν⟩ := gcD_lt_iff hxE hx1 v hv
    have hlt : v < (gdB ν).K.sys.top (upsilon l) := by
      rw [gdB_top hxE hx1 hν]
      exact hvν.trans_le (gq_mono hxE hx1 (gd_one_add_lt' hxE hν) le_add_self)
    obtain ⟨t, ht, et⟩ := (gdB ν).K.sys.rep l hl hl1 (gdB_gate hν) v hlt
    exact ⟨⟨ν, t⟩, ⟨hν, ht⟩, et⟩
  top_lt := fun l hl hl1 => by
    have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
    have h1 : l < l + ω := lt_add_of_pos_right l omega0_pos
    have hτU := upsPt_upsilon (hl0.trans h1)
    exact (gcq_lt_next (ups_inE hl) (ups_lt_Om1 l hl1) le_rfl (upsilon_normal.strictMono h1) hτU.2).trans
      (upsilon_normal.strictMono (lt_add_one _))
  pkg := fun l hl hl1 p h h1 R => (gdB p.1).K.sys.pkg l hl hl1 (gdB_gate h.1) p.2 h.2 h1 R
  rs := fun l hl hl1 p h => (gdB p.1).K.sys.rs l hl hl1 (gdB_gate h.1) p.2 h.2
  uni_le := fun σ ρ hσ hρ hB p q hp hq =>
    xt_uni_of_exact hB ((gdB p.1).K.exact σ ρ hσ hρ hB (gdB_gate hp.1) p.2 hp.2)
      ((gdB q.1).K.exact σ ρ hσ hρ hB (gdB_gate hq.1) q.2 hq.2)
  small := fun p => ((gdB p.1).K.sys.small p.2).imp id fun h x hx hx1 hc => h x hx hx1 (gdB_gate hc.1) hc.2

theorem gdDSys_top (x : Ordinal.{0}) : gdDSys.top x = gq x x := rfl

/-- **THE LAYER OF `Γ_{x+x}`**: top `ω^{Γ_{x+x}} = Γ_{x+x}`. -/
noncomputable def gdDL : XtLay where
  sys := gdDSys
  E := fun x => gq x x
  top_eq := fun x hx hx1 => (gcq_facts hx hx1 le_rfl).2.2.2.1.symm
  exp_dvd := fun x hx hx1 =>
    opow_dvd_of_inE (gcq_facts hx hx1 le_rfl).2.2.2.1 (gcq_facts hx hx1 le_rfl).2.1.le
  exp_lt := fun x hx hx1 => (gcq_facts hx hx1 le_rfl).2.2.1
  top_gt := fun x hx hx1 => (gcq_facts hx hx1 le_rfl).2.1
  top_lt_ups := fun x u hx hx1 hxu hu => gcq_lt_next hx hx1 le_rfl hxu hu.2
  lt_top_E := fun x hx hx1 p h => gdD_val_lt hx hx1 p h
  exact := fun σ ρ hσ hρ hB p hp => (gdB p.1).K.exact σ ρ hσ hρ hB (gdB_gate hp.1) p.2 hp.2
  exp_pi := fun _ _ _ _ hB => gcD_pi hB
  top_wit := fun _ _ _ h => GcDK.gcDiagWit h

/-- **The new base package**: the diagonal layer. -/
noncomputable def gdDB : Lp.LpB where
  K := gdDL
  ek := fun x hx hx1 => (gcq_facts hx hx1 le_rfl).2.2.2.1
  mem := fun x hx hx1 => (gcq_facts hx hx1 le_rfl).1

theorem gdDB_E (x : Ordinal.{0}) : gdDB.K.E x = gq x x := rfl

theorem gdDB_sys : gdDB.K.sys = gdDSys := rfl

/-! ## Generic consequences: BLK^O and the exact reaches below `Λ⁺` -/

theorem gdD_topPkg : XtTopPkg gdDSys := XtLay.topPkg gdDL

/-- **The offset is a general specification up to `Λ⁺(gdDSys)`.** -/
theorem gdD_spec : OffSpecGen (xtOrec gdDSys) (xtB1 gdDSys) := xtSpec1 gdD_topPkg

/-- **Theorem BLK^O below `υ_{Λ⁺(gdDSys)}`.** -/
theorem gdD_blk :
    (∀ c d, c < d → d < upsilon (xtB1 gdDSys) → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 gdDSys ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 gdDSys →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec gdDSys l)) ∧
    (∀ α < upsilon (xtB1 gdDSys), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  xtBlk1 gdD_topPkg

/-- **The exact reach at every restart below `Λ⁺(gdDSys)`**: `lh(ρ_λ) = δ_λ + O_D(λ)`. -/
theorem gdD_reach {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < xtB1 gdDSys) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec gdDSys l) :=
  xtReach1 gdD_topPkg hl hlB

theorem gdD_B1_lt_Om1 : xtB1 gdDSys < Om1 := xtB1_lt_Om1 gdD_topPkg

/-! ## Past every constant offset: the tower `Gc.gcB` lies inside the diagonal -/

/-- **The top of `gcB α` is a term of the diagonal** (`1 + α < ε₀`), with gap `> 1`. -/
theorem gdD_topIn_gc {α : Ordinal.{0}} (h : 1 + α < ε₀) : LyTopIn gdDSys (gcB α).K.sys := by
  have hα : α < ε₀ := le_add_self.trans_lt h
  have hα1 : α + 1 < ε₀ := gc_eps0_lim.add_one_lt hα
  obtain ⟨t, ht⟩ := gdB_topIn (lt_add_one α)
  refine ⟨⟨α + 1, t⟩, fun x hx hx1 => ?_, fun l hl hl1 => ?_⟩
  · have hxE := upsPt_inE hx
    have hαx : α + 1 < x := gc_cst hα1 x hxE
    refine ⟨⟨hαx, (ht x).1⟩, ?_⟩
    show (gdB (α + 1)).K.sys.val t x = (gcB α).K.sys.top x
    rw [(ht x).2 hxE hx1 ((lt_add_one α).trans hαx), gcB_top h hxE hx1]
  · have hxE := ups_inE hl
    have hx1 := ups_lt_Om1 l hl1
    rw [gcB_top h hxE hx1, gdDSys_top]
    have hD := (gcq_facts hxE hx1 le_rfl).2.2.2.1
    exact (inE_indec hD).add_lt (gd_gq_lt_D hxE hx1 (gc_cst h _ hxE)) (lu_one_lt_E hD)

/-- **`Λ⁺(gcB α) < Λ(gdDSys)`** for every `α` with `1 + α < ε₀`. -/
theorem gdD_gt_gc {α : Ordinal.{0}} (h : 1 + α < ε₀) : xtB1 (gcB α).K.sys < xtLam gdDSys :=
  lyLamGt (XtLay.topPkg (gcB α).K) (gdD_topIn_gc h)

/-- **`O_D = O_{gcB α}` below `Λ⁺(gcB α)`.** -/
theorem gdD_eq_gc {α : Ordinal.{0}} (h : 1 + α < ε₀) {μ : Ordinal.{0}} (hμ : IsRestartIdx μ)
    (hμα : μ < xtB1 (gcB α).K.sys) : xtOrec gdDSys μ = xtOrec (gcB α).K.sys μ :=
  lyEq (XtLay.topPkg (gcB α).K) (gdD_topIn_gc h) hμ hμα

/-- **The diagonal layer lies past every frontier of the constant offsets**: `ι(Γ_{Ω₁+ε₀}) ≤ Λ(gdDSys) <
Λ⁺(gdDSys)`, and `P(Γ_{Ω₁+ε₀}) ≤ υ_{Λ(gdDSys)}`. -/
theorem gdD_past_gc (S : InaccSeq.{0}) :
    iota S gcV ≤ xtLam gdDSys ∧ xtLam gdDSys < xtB1 gdDSys ∧ Pv S gcV ≤ upsilon (xtLam gdDSys) := by
  have h1 : gcFam.famSup ≤ xtLam gdDSys :=
    Ordinal.iSup_le fun n => (gdD_gt_gc (gcSeq_one_add n)).le
  obtain ⟨he, hu, -⟩ := gcFamSup (S := S)
  refine ⟨he ▸ h1, lyLamLtB1 gdD_topPkg, ?_⟩
  rw [← hu]
  exact upsilon_normal.strictMono.monotone h1

/-! ## The ladder over the diagonal -/

/-- **The ladder over the diagonal**: `Λ⁺(gdDSys) < Λ(lpSys gdDB 1)`, `Λ⁺(lpSys gdDB n) < Λ(lpSys gdDB (n+1))`,
`Λ⁺(gdDSys) < Λ⁺(lpSys gdDB (n+1))`. -/
theorem gdD_ladder (n : ℕ) :
    xtB1 gdDB.K.sys < xtLam (Lp.lpSys gdDB 1) ∧
    xtB1 (Lp.lpSys gdDB n) < xtLam (Lp.lpSys gdDB (n + 1)) ∧
    xtB1 gdDB.K.sys < xtB1 (Lp.lpSys gdDB (n + 1)) :=
  ⟨Lp.lpLam_gt_K (B := gdDB), Lp.lpLam_gt (B := gdDB) n, Lp.lpB1_gt_K (B := gdDB) n⟩

end Googology.Trans.PoR.InaccPsi.R2.Gd

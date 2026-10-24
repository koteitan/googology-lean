import Googology.Trans.PoR.InaccPsi.R2.GmQ0

/-!
# THE CODE SYSTEM BELOW `Γ_{Ω₁+1}²`: hulls, gates, countability

* `mq_G0_mul_mem`, `mq_mem` (**every code `Γ_{Ω₁+1}·γ + c'` lies in every hull `Cl(a, b)` with `c < a` and gate below
  `b`**: `Γ_{Ω₁+1}·γ = ω^{Γ_{Ω₁+1}}·γ`, `Gl.gl_mem`), `mqB_mem`, `mqB_V`, `mq_count`;
* `mq_code_gate` (**a code `c < Γ_{Ω₁+1}²` over `Z` with the atoms `Γ_{Ω₁+1+c''}` (gate below `Z`) has its gate below
  `Z`**: by induction on `c`: below `Γ_{Ω₁+1}` it is atom-free (`mg_noAt`, `Gl.gl_code_gate`); above, the leading
  exponent `e = log_ω c = Γ_{Ω₁+1} + e'` and the rest `r = c − ω^e·k` are codes (`gxDec`), `e' < Γ_{Ω₁+1}` is
  atom-free, and `γ(c) = ω^{e'}·k + γ(r)` (`Gl.gl_add`, `Gl.gl_opow_gate`));
* `mqCS` (**THE CODE SYSTEM** below `Γ_{Ω₁+1}²`).

No new axiom.  New definition: `mqCS`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gm

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **A code lies in every hull `Cl(a, b)` with `c < a` and its gate below `b`.** -/
theorem mq_mem {S : InaccSeq.{0}} {a b c : Ordinal.{0}} (hc : c < mqB) (hca : c < a) (hg : mqG c < b) :
    c ∈ S.CSet a b := by
  obtain ⟨γ, c', hγ, hc', rfl⟩ := mq_split hc
  rw [mqG_split γ hc'] at hg
  have ha : 0 < a := lt_of_le_of_lt zero_le hca
  have hc'm := (gl_mem (S := S) (a := a) (b := b) c' hc' (lt_of_le_of_lt (le_max_right _ _) hg)).1
  refine CSet.add_mem ?_ hc'm
  rcases lt_or_ge γ ω with hω | hω
  · obtain ⟨n, rfl⟩ := lt_omega0.1 hω
    exact mg_G0_mul_mem ha n
  · have hQ : glQ γ = glG γ := by unfold glQ; rw [if_neg (not_lt.2 hω)]
    have hgγ : glG γ < b := by rw [← hQ]; exact lt_of_le_of_lt (le_max_left _ _) hg
    have h := (gl_mem (S := S) (a := a) (b := b) γ hγ hgγ).2 (gcG 0) (gmS_G0_mem S ha)
    rwa [geG_E] at h

theorem mqB_mem {S : InaccSeq.{0}} {a b : Ordinal.{0}} (ha : mqB < a) : mqB ∈ S.CSet a b := by
  have e : mqB = veblen 0 (gcG 0 + gcG 0) := by rw [veblen_zero_apply, mqB_eq]
  have hG := gmS_G0_mem S (b := b) (lt_of_le_of_lt zero_le ha)
  rw [e]
  exact CSet.phi_mem (CSet.zero_mem _ _) (CSet.add_mem hG hG)

theorem mqB_V : mqB < gcG mqB := by
  have hE : InE (gcG 1) := Low.opow_eq_self_of_SC (gcG_SC 1)
  have h1 : mqB < gcG 1 := InE.mul_lt hE (gcG_lt zero_lt_one) (gcG_lt zero_lt_one)
  exact h1.trans_le (gcG_le (Order.one_le_iff_pos.2 (lt_of_le_of_lt zero_le mq_G0_lt_B)))

/-- The codes below `c ≤ Γ_{Ω₁+1}²` with gate below a countable `y` are countably many. -/
theorem mq_count {c y : Ordinal.{0}} (hc : c ≤ mqB) (hy : InE y) (hy1 : y < Om1) :
    Countable {b : Iio c // mqG b.1 < y} := by
  haveI := gl_count (c := gcG 0) le_rfl hy hy1
  have hωy := omega0_lt_inE hy
  let f : {b : Iio c // mqG b.1 < y} → {b : Iio (gcG 0) // glG b.1 < y} × {b : Iio (gcG 0) // glG b.1 < y} :=
    fun b => (⟨⟨b.1.1 / gcG 0, (Ordinal.div_lt mg_G0_ne).2 (lt_of_lt_of_le b.1.2 hc)⟩,
      glG_of_Q hωy (lt_of_le_of_lt (le_max_left _ _) b.2)⟩,
      ⟨⟨b.1.1 % gcG 0, Ordinal.mod_lt _ mg_G0_ne⟩, lt_of_le_of_lt (le_max_right _ _) b.2⟩)
  have hinj : Function.Injective f := by
    intro b b' hbb
    have h1 : b.1.1 / gcG 0 = b'.1.1 / gcG 0 := congrArg (fun p => p.1.1.1) hbb
    have h2 : b.1.1 % gcG 0 = b'.1.1 % gcG 0 := congrArg (fun p => p.2.1.1) hbb
    have e : b.1.1 = b'.1.1 := by rw [← Ordinal.div_add_mod b.1.1 (gcG 0), h1, h2, Ordinal.div_add_mod]
    exact Subtype.ext (Subtype.ext e)
  exact hinj.countable

/-! ## The gate of a code -/

theorem mq_nat_mul_cl {Z : Ordinal.{0}} {At : Set Ordinal.{0}} (hZ : 0 < Z) {t : Ordinal.{0}} (ht : GxCl Z At t) :
    ∀ k : ℕ, GxCl Z At (t * k)
  | 0 => by rw [Nat.cast_zero, mul_zero]; exact GxCl.zero hZ
  | k + 1 => by rw [Nat.cast_succ, mul_add_one]; exact GxCl.add (mq_nat_mul_cl hZ ht k) ht

theorem mq_glG_nat_mul {Z : Ordinal.{0}} (hZa : ∀ u v, u < Z → v < Z → u + v < Z) (hωZ : ω < Z) {t : Ordinal.{0}}
    (htG : t < gcG 0) (hgt : glG t < Z) : ∀ k : ℕ, glG (t * k) < Z
  | 0 => by rw [Nat.cast_zero, mul_zero, glG_zero]; exact (lt_of_le_of_lt zero_le hωZ)
  | k + 1 => by
    have hE := gl_G0_E
    have hk : t * ((k + 1 : ℕ) : Ordinal.{0}) < gcG 0 :=
      hE.mul_lt htG ((natCast_lt_omega0 _).trans (omega0_lt_inE hE))
    rw [Nat.cast_succ, mul_add_one] at hk ⊢
    exact gl_add hZa hωZ _ _ hk (mq_glG_nat_mul hZa hωZ htG hgt k) hgt

/-- **The gate of a code over `Z` (with the atoms `Γ_{Ω₁+1+c''}`, `c'' < Γ_{Ω₁+1}²`, gate below `Z`) is below `Z`.** -/
theorem mq_code_gate {Z : Ordinal.{0}} (hZ1 : Z ≤ Om1) (hZ0 : 0 < Z) (hZa : ∀ u v, u < Z → v < Z → u + v < Z)
    (hZp : ∀ u v, u < Z → v < Z → veblen u v < Z) :
    ∀ c, GxCl Z {s | ∃ c', c' < mqB ∧ mqG c' < Z ∧ s = gcG c'} c → c < mqB → mqG c < Z := by
  set At := {s | ∃ c', c' < mqB ∧ mqG c' < Z ∧ s = gcG c'} with hAtdef
  have hSC : SC Z := ⟨hZ0, fun u hu v hv => hZp u v hu hv⟩
  have hGx : GxAt At := by
    rintro s ⟨c', -, -, rfl⟩
    exact ⟨gcG_SC c', gcG_Om1_lt c'⟩
  have hG0 : gcG 0 ∈ At := ⟨0, (lt_of_le_of_lt zero_le mq_G0_lt_B), by rw [mqG_zero]; exact hZ0, rfl⟩
  have hAtG : ∀ s ∈ At, gcG 0 ≤ s := by rintro s ⟨c'', -, -, rfl⟩; exact gcG_le zero_le
  have hZw : ∀ u, u < Z → ω ^ u < Z := fun u hu => by have := hZp 0 u hZ0 hu; rwa [veblen_zero_apply] at this
  have hωZ : ω < Z := by
    have h1 : (1 : Ordinal.{0}) < Z := by have := hZw 0 hZ0; rwa [opow_zero] at this
    have := hZw 1 h1; rwa [opow_one] at this
  -- an atom-free code below `Γ_{Ω₁+1}` has its gate below `Z`
  have hlow : ∀ v, GxCl Z At v → v < gcG 0 → glG v < Z := fun v hv hvG =>
    gl_code_gate le_rfl hZ1 hZ0 hZa hZp (fun s hs => absurd hs (Set.notMem_empty s)) gfE_lt_G0.le
      (mg_noAt hAtG hv hvG) hvG
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hcB
  rcases lt_or_ge c (gcG 0) with hcG | hcG
  · rw [mqG_low hcG]; exact hlow c hc hcG
  -- the leading term `ω^e·k` with `e = Γ_{Ω₁+1} + e'`
  have hc0 : c ≠ 0 := (lt_of_lt_of_le gl_G0_E.pos hcG).ne'
  set e := log ω c with he
  have heC : GxCl Z At e := (gxDec hSC hGx c hc).2
  have hG0e : gcG 0 ≤ e := by
    rw [he]; exact le_log_of_opow_le one_lt_omega0 (by rw [geG_E]; exact hcG)
  have hecB : e < gcG 0 + gcG 0 := by
    rw [he]; exact lt_log_of_lt_opow (gl_G0_E.pos.trans_le le_self_add).ne' (by rw [← mqB_eq]; exact hcB)
  set e' := e - gcG 0 with he'
  have hee : gcG 0 + e' = e := Ordinal.add_sub_cancel_of_le hG0e
  have he'G : e' < gcG 0 := (add_lt_add_iff_left _).1 (by rw [hee]; exact hecB)
  have he'C : GxCl Z At e' := (gxDec hSC hGx e heC).1 _ (GxCl.atom hG0) hG0e
  have hge' : glG e' < Z := hlow e' he'C he'G
  set k := c / ω ^ e with hk
  have hkω : k < ω := div_opow_log_lt c one_lt_omega0
  obtain ⟨n, hn⟩ := lt_omega0.1 hkω
  set r := c % ω ^ e with hr
  have hdec : ω ^ e * k + r = c := Ordinal.div_add_mod c (ω ^ e)
  have hk0 : k ≠ 0 := (div_opow_log_pos ω hc0).ne'
  have hrlt : r < ω ^ e := Ordinal.mod_lt c (opow_pos e omega0_pos).ne'
  have hrc : r < c := hrlt.trans_le (by
    conv_rhs => rw [← hdec]
    exact (le_mul_of_one_le_right' (Order.one_le_iff_ne_zero.2 hk0)).trans le_self_add)
  have htC : GxCl Z At (ω ^ e * k) := by rw [hn]; exact mq_nat_mul_cl hZ0 (GxCl.opow hZ0 heC) n
  have hrC : GxCl Z At r := by
    have h := (gxDec hSC hGx c hc).1 _ htC (by rw [← hdec]; exact le_self_add)
    rwa [← hdec, Ordinal.add_sub_cancel] at h
  have hgr := IH r hrc hrC (hrc.trans hcB)
  -- `c = Γ_{Ω₁+1}·(ω^{e'}·n + γ(r)) + c'(r)`
  have hωe : ω ^ e = gcG 0 * ω ^ e' := by rw [← hee, opow_add, geG_E]
  have hcform : c = gcG 0 * (ω ^ e' * k + r / gcG 0) + r % gcG 0 := by
    rw [mul_add, ← mul_assoc, ← hωe, add_assoc, Ordinal.div_add_mod, hdec]
  have hγlt : ω ^ e' * k + r / gcG 0 < gcG 0 := by
    have h1 := (mq_split hcB)
    have := (Ordinal.div_lt mg_G0_ne).2 hcB
    rwa [hcform, (mq_split_eq _ (Ordinal.mod_lt r mg_G0_ne)).1] at this
  rw [hcform, mqG_split _ (Ordinal.mod_lt r mg_G0_ne)]
  unfold mqG at hgr
  refine max_lt ((glQ_le _).trans_lt ?_) (lt_of_le_of_lt (le_max_right _ _) hgr)
  have hwG : ω ^ e' < gcG 0 := by
    rw [← geG_E 0]; exact (opow_lt_opow_iff_right one_lt_omega0).2 he'G
  have hwk : ω ^ e' * k < gcG 0 := lt_of_le_of_lt le_self_add hγlt
  have hgw : glG (ω ^ e') < Z := gl_opow_gate hZw hωZ e' hwG hge'
  have hgwk : glG (ω ^ e' * k) < Z := by rw [hn] at hwk ⊢; exact mq_glG_nat_mul hZa hωZ hwG hgw n
  exact gl_add hZa hωZ _ _ hγlt hgwk (glG_of_Q hωZ (lt_of_le_of_lt (le_max_left _ _) hgr))

/-- **THE CODE SYSTEM below `Γ_{Ω₁+1}²`** (atoms `Γ_{Ω₁+1+c}`, the atom `Γ_{Ω₁+1}` among the codes). -/
noncomputable def mqCS : GmCS where
  B := mqB
  gt := mqG
  B_V := mqB_V
  gt_zero := mqG_zero
  gt_lt := fun c _ => mqG_lt_Om1 c
  gt_succ := fun b _ hZ _ hg => mqG_succ hZ b hg
  mem := fun _ _ _ _ hc hca hg => mq_mem hc hca hg
  B_mem := fun _ _ _ ha => mqB_mem ha
  code_gate := fun _ hZ1 hZ0 hZa hZp c hc hcB => mq_code_gate hZ1 hZ0 hZa hZp c hc hcB
  count := fun _ _ hc hy hy1 => mq_count hc hy hy1

end Googology.Trans.PoR.InaccPsi.R2.Gm

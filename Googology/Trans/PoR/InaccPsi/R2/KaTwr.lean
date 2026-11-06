import Googology.Trans.PoR.InaccPsi.R2.ZxPlat

/-!
# Ka: TOWERS OF ANY DEPTH `c₁ + ω^{c₂ + ω^{… + ω^{c_n + ω^m·x}}}`, their gap, step and plateau

A tower `t : KaT` is `base c m` (`x ↦ c + ω^m·x`) or `up c t` (`x ↦ c + ω^{t(x)}`); `t.ev` is its value.  The
arguments of the plateau lemma `Zx.zxPlat` at the jumps of the top law are such towers over `Tβ`
(`Ω^{K + Ω^{H}·x} = ω^{Ω₁·K + ω^{Ω₁ + Ω₁·H}·x}`, `Zx.zxOe_conv`; one more level for every nesting of `W` in the exponent).

* `ev_mono`, `ev_le_evE`, `evE_lt`, `evE_mem` (the bound `t.evE q`: the bottom `ω^m·(q+1)` raised to
  `ω^{m + (q+1)}`; above `t(q + 1)`, below `t(x)` for `q < x` strongly critical, a member once the constants and
  `q + 1` are);
* `gap` (**THE GAP OF EVERY TOWER** at `Cl(a, ψ₁ a)` once its bottom exponent `m` is a member: `Zx.zxGap_mul`, then
  `Zx.zxGap_opow` at every level), `step` (**THE STEP OF EVERY TOWER `b + ω^{t(x)}`** over a normal `b`, the constants
  of `t` in the closures `Cl(a, ψ₂ a)` over `b + ω^{t(0)}`), `plat` (**THE PLATEAU OF EVERY TOWER**);
* `addC` (add a constant on the top level: `(addC a t)(x) = a + t(x)`).

No new axiom.  New definitions: `KaT` (towers), `KaT.ev`, `KaT.evE`, `KaT.bm`, `KaT.InC`, `KaT.addC`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ka

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Zx

variable {S : InaccSeq.{0}}

/-- **A tower**: `base c m` is `x ↦ c + ω^m·x`, `up c t` is `x ↦ c + ω^{t(x)}`. -/
inductive KaT : Type 1
  | base (c m : Ordinal.{0}) : KaT
  | up (c : Ordinal.{0}) (t : KaT) : KaT

namespace KaT

/-- The value of a tower. -/
noncomputable def ev : KaT → Ordinal.{0} → Ordinal.{0}
  | base c m, x => c + ω ^ m * x
  | up c t, x => c + ω ^ ev t x

/-- The bound of the step: the bottom `ω^m·(q+1)` raised to `ω^{m + (q+1)}`. -/
noncomputable def evE : KaT → Ordinal.{0} → Ordinal.{0}
  | base c m, q => c + ω ^ (m + (q + 1))
  | up c t, q => c + ω ^ evE t q

/-- The bottom exponent `m`. -/
def bm : KaT → Ordinal.{0}
  | base _ m => m
  | up _ t => bm t

/-- Every constant of the tower has the property `P`. -/
def InC (P : Ordinal.{0} → Prop) : KaT → Prop
  | base c m => P c ∧ P m
  | up c t => P c ∧ InC P t

/-- Add a constant on the top level. -/
noncomputable def addC (a : Ordinal.{0}) : KaT → KaT
  | base c m => base (a + c) m
  | up c t => up (a + c) t

theorem ev_base (c m x : Ordinal.{0}) : (base c m).ev x = c + ω ^ m * x := rfl

theorem ev_up (c : Ordinal.{0}) (t : KaT) (x : Ordinal.{0}) : (up c t).ev x = c + ω ^ t.ev x := rfl

theorem addC_ev (a : Ordinal.{0}) (t : KaT) (x : Ordinal.{0}) : (addC a t).ev x = a + t.ev x := by
  cases t <;> simp only [addC, ev, add_assoc]

theorem InC.imp {P P' : Ordinal.{0} → Prop} (h : ∀ y, P y → P' y) : ∀ t : KaT, InC P t → InC P' t
  | base _ _, hC => ⟨h _ hC.1, h _ hC.2⟩
  | up _ t, hC => ⟨h _ hC.1, InC.imp h t hC.2⟩

theorem ev_mono : ∀ t : KaT, Monotone t.ev
  | base _ _ => fun _ _ h => add_le_add le_rfl (mul_le_mul_right h _)
  | up _ t => fun _ _ h => add_le_add le_rfl (opow_le_opow_right omega0_pos (ev_mono t h))

theorem ev_le_evE : ∀ (t : KaT) (q : Ordinal.{0}), t.ev (q + 1) ≤ t.evE q
  | base c m, q => by
    show c + ω ^ m * (q + 1) ≤ c + ω ^ (m + (q + 1))
    rw [opow_add]
    exact add_le_add le_rfl (mul_le_mul_right (Ordinal.right_le_opow _ one_lt_omega0) _)
  | up c t, q => add_le_add le_rfl (opow_le_opow_right omega0_pos (ev_le_evE t q))

theorem evE_lt {q x : Ordinal.{0}} (hx : SC x) (hq : q < x) : ∀ t : KaT, t.evE q < t.ev x
  | base c m => by
    have hxε : ω ^ x = x := gg_SC_eps hx
    have hq1x : q + 1 < x := hx.isSuccLimit.add_one_lt hq
    show c + ω ^ (m + (q + 1)) < c + ω ^ m * x
    conv_rhs => rw [← hxε, ← opow_add]
    exact (add_lt_add_iff_left c).2 ((opow_lt_opow_iff_right one_lt_omega0).2 ((add_lt_add_iff_left m).2 hq1x))
  | up c t => (add_lt_add_iff_left c).2 ((opow_lt_opow_iff_right one_lt_omega0).2 (evE_lt hx hq t))

theorem evE_mem {a b q : Ordinal.{0}} (hq : q + 1 ∈ S.CSet a b) :
    ∀ t : KaT, t.InC (· ∈ S.CSet a b) → t.evE q ∈ S.CSet a b
  | base c m, hC => by
    show c + ω ^ (m + (q + 1)) ∈ S.CSet a b
    have h := CSet.phi_mem (CSet.zero_mem (S := S) a b) (CSet.add_mem hC.2 hq)
    rw [veblen_zero_apply] at h
    exact CSet.add_mem hC.1 h
  | up c t, hC => by
    show c + ω ^ t.evE q ∈ S.CSet a b
    have h := CSet.phi_mem (CSet.zero_mem (S := S) a b) (evE_mem hq t hC.2)
    rw [veblen_zero_apply] at h
    exact CSet.add_mem hC.1 h

/-- **THE GAP OF EVERY TOWER** at `Cl(a, ψ₁ a)` once its bottom exponent is a member. -/
theorem gap {a : Ordinal.{0}} : ∀ t : KaT, t.bm ∈ S.CSet a (S.psi a (Om 1)) →
    ZxGap t.ev (S.CSet a (S.psi a (Om 1))) (S.psi a (Om 1))
  | base c _, hm => zxGap_mul (b := c) hm
  | up c t, hm => zxGap_opow (b := c) (L := t.ev) (gap t hm)

/-- **THE STEP OF EVERY TOWER `b + ω^{t(x)}`** over a normal `b`. -/
theorem step {b : Ordinal.{0}} (hb : b ∈ S.CSet b (S.psi b (Om (1 + 1)))) (t : KaT)
    (hC : t.InC fun y => ∀ a, (up b t).ev 0 ≤ a → y ∈ S.CSet a (S.psi a (Om (1 + 1)))) :
    ZxStep S (up b t).ev := by
  intro q x hx hx1 hq
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hq1x : q + 1 < x := hx.isSuccLimit.add_one_lt hq
  set Lx := (up b t).ev x with hLx
  set E := b + ω ^ t.evE q with hE
  have hle : (up b t).ev (q + 1) ≤ E := add_le_add le_rfl (opow_le_opow_right omega0_pos (ev_le_evE t q))
  have hEx : E < Lx := (add_lt_add_iff_left b).2 ((opow_lt_opow_iff_right one_lt_omega0).2 (evE_lt hx hq t))
  have hL0 : (up b t).ev 0 ≤ Lx := ev_mono (up b t) zero_le
  have hC' : t.InC (· ∈ S.CSet Lx (S.psi Lx (Om (1 + 1)))) := InC.imp (fun y hy => hy Lx hL0) t hC
  have hq1 : q + 1 ∈ S.CSet Lx (S.psi Lx (Om (1 + 1))) :=
    CSet.of_lt ((hq1x.trans hx1).trans (psiS_bounds (S := S) _ 1).1)
  have hEC : E ∈ S.CSet Lx (S.psi Lx (Om (1 + 1))) := by
    have h := CSet.phi_mem (CSet.zero_mem (S := S) Lx (S.psi Lx (Om (1 + 1)))) (evE_mem hq1 t hC')
    rw [veblen_zero_apply] at h
    exact CSet.add_mem ((psi_mono hκ2 le_self_add).2 hb) h
  exact (psi_mono hκ2 hle).1.trans_lt (psi_lt_psi_of_mem hκ2 hEx hEC)

/-- **THE PLATEAU OF EVERY TOWER**: `ψ₁(B + ψ₂(b + ω^{t(Ω₁)})) ≤ sup_n x_n`, `x_{n+1} = ψ₁(B + ψ₂(b + ω^{t(x_n)}))`,
once the bottom exponent of `t` is a member of every stage. -/
theorem plat {B b x0 : Ordinal.{0}} (hb : b ∈ S.CSet b (S.psi b (Om (1 + 1)))) (t : KaT)
    (hC : t.InC fun y => ∀ a, (up b t).ev 0 ≤ a → y ∈ S.CSet a (S.psi a (Om (1 + 1))))
    (h0 : x0 ≤ zxX S B (up b t).ev x0 1) (hx0 : x0 < Om 1)
    (hm : ∀ n, t.bm ∈ S.CSet (zxA S B (up b t).ev x0 n) (zxX S B (up b t).ev x0 (n + 1))) :
    S.psi (B + S.psi ((up b t).ev (Om 1)) (Om (1 + 1))) (Om 1) ≤ ⨆ n : ℕ, zxX S B (up b t).ev x0 n := by
  refine zxPlat (ev_mono (up b t)) h0 hx0 (fun n => ?_) (step hb t hC)
  have hmn := hm n
  rw [zxX_succ] at hmn ⊢
  exact gap (up b t) hmn

end KaT

end Googology.Trans.PoR.InaccPsi.R2.Ka

#print axioms Googology.Trans.PoR.InaccPsi.R2.Ka.KaT.plat

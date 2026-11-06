import Googology.Trans.PoR.InaccPsi.R2.KjCoef

/-!
# Kk: THE OWNERSHIP OF EVERY CONTEXT (the plateau at the level `Ω₂` along a context of any depth)

`W^x = leWe x = ω^{Ω₂·x}`.  A context `C` has a `D`-level tower `t₂` when `Ω₂·C(v) = t₂(v)` (`KkTw`); then
`β + W^{C(v)} = β + ω^{t₂(v)}` is a tower over `β`, and the plateau `Kg.kgPlat` at the level `Ω₂` gives:

* `kkOwn` (**THE OWNERSHIP OF THE CONTEXT `C`**: if the threshold of `t₂` lies below `ψ₂(β + W^{C(1)})`, every
  ordinal `u' < ψ₂(β + W^{C(Ω₂)})` has `u' < ψ₂(β + W^{C(u')})`),
* `kkTw_base` (`v ↦ g₀ + W^j·v`, `t₂ = Ω₂·g₀ + ω^{Ω₂ + Ω₂·j}·v`), `kkTw_nest` (`v ↦ g₁ + W^{C'(v)}`,
  `t₂ = Ω₂·g₁ + ω^{Ω₂ + t₂'(v)}`), so every context of `Ke.KeCtx` built by `Ke.keCtx_base` / `Ke.keCtx_nest` has a
  `D`-level tower; `Kg.kgOwnBase` and `Kg.kgOwnExp` are the base and the nest of the identity.

No new axiom.  New definition: `KkTw` (the `D`-level tower of a context).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Zx
  Googology.Trans.PoR.InaccPsi.R2.Ka Googology.Trans.PoR.InaccPsi.R2.Kb Googology.Trans.PoR.InaccPsi.R2.Kg
  Googology.Trans.PoR.InaccPsi.R2.Ke

variable {S : InaccSeq.{0}}

/-- **The `D`-level tower of a context**: `Ω₂·C(v) = t₂(v)`, its bottom exponent a member once the threshold `q` is
below the bound. -/
structure KkTw (S : InaccSeq.{0}) (C : Ordinal.{0} → Ordinal.{0}) (t₂ : KaT) (q : Ordinal.{0}) : Prop where
  ev2 : ∀ v, Om (1 + 1) * C v = t₂.ev v
  bm2 : ∀ a c : Ordinal.{0}, Om 1 ≤ c → q < c → t₂.bm ∈ S.CSet a c

/-- **The base context** `v ↦ g₀ + W^j·v` has the tower `Ω₂·g₀ + ω^{Ω₂ + Ω₂·j}·v`. -/
theorem kkTw_base {g₀ j qj : Ordinal.{0}} (hjm : ∀ a c : Ordinal.{0}, Om 1 ≤ c → qj < c → j ∈ S.CSet a c) :
    KkTw S (fun v => g₀ + leWe j * v) (KaT.base (Om (1 + 1) * g₀) (Om (1 + 1) + Om (1 + 1) * j)) qj :=
  ⟨fun v => by
    rw [KaT.ev_base]
    unfold leWe
    rw [mul_add, ← mul_assoc, kg_Om2_mul_opow],
    fun a c h hq => CSet.add_mem (mxOm2_mem _ _) (ldMulK_mem ldOm2_SC (mxOm2_mem _ _) (hjm a c h hq))⟩

/-- **The nested context** `v ↦ g₁ + W^{C'(v)}` has the tower `Ω₂·g₁ + ω^{Ω₂ + t₂'(v)}`. -/
theorem kkTw_nest {g₁ q' : Ordinal.{0}} {C' : Ordinal.{0} → Ordinal.{0}} {t₂' : KaT} (h : KkTw S C' t₂' q') :
    KkTw S (fun v => g₁ + leWe (C' v)) (KaT.up (Om (1 + 1) * g₁) (KaT.addC (Om (1 + 1)) t₂')) q' :=
  ⟨fun v => by
    rw [KaT.ev_up, KaT.addC_ev, ← h.ev2 v]
    unfold leWe
    rw [mul_add, kg_Om2_mul_opow],
    fun a c hc hq => by rw [KaT.bm, KaT.addC_bm]; exact h.bm2 a c hc hq⟩

/-- **THE OWNERSHIP OF THE CONTEXT `C`**: below `ψ₂(β + W^{C(Ω₂)})` every `u'` has `u' < ψ₂(β + W^{C(u')})`, once
the threshold of the `D`-level tower lies below `ψ₂(β + W^{C(1)})`. -/
theorem kkOwn {β q : Ordinal.{0}} {C : Ordinal.{0} → Ordinal.{0}} {t₂ : KaT} (hC : Monotone C) (htw : KkTw S C t₂ q)
    (hq : q < S.psi (β + leWe (C 1)) (Om (1 + 1))) :
    ∀ u', u' < S.psi (β + leWe (C (Om (1 + 1)))) (Om (1 + 1)) → u' < S.psi (β + leWe (C u')) (Om (1 + 1)) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  set G : Ordinal.{0} → Ordinal.{0} := fun v => β + leWe (C v) with hGdef
  have hGmono : Monotone G := fun _ _ h => add_le_add le_rfl (leWe_mono (hC h))
  have hfun : G = (KaT.up β t₂).ev := by
    funext v; rw [KaT.ev_up, ← htw.ev2 v]; rfl
  -- start the plateau at `v_1 = ψ₂(β + W^{C 0})`
  set x0 := S.psi (β + leWe (C 0)) (Om (1 + 1)) with hx0def
  have hx01 : (1 : Ordinal.{0}) ≤ x0 := Order.one_le_iff_pos.2 (SC_psi hκ2 _).1
  have hx0 : x0 < Om (1 + 1) := psi_lt hκ2 _
  have h0 : x0 ≤ kgX S (Om (1 + 1)) G x0 1 := by
    rw [kgX_succ, kgX_zero]
    exact (psi_mono hκ2 (hGmono zero_le)).1
  have hmono : Monotone (kgX S (Om (1 + 1)) G x0) := monotone_nat_of_le_succ (kgX_mono hκ2 hGmono h0)
  have hx1 : ∀ n, S.psi (β + leWe (C 1)) (Om (1 + 1)) ≤ kgX S (Om (1 + 1)) G x0 (n + 1) := fun n => by
    refine le_trans ?_ (hmono (Nat.le_add_left 1 n))
    rw [kgX_succ, kgX_zero]
    exact (psi_mono hκ2 (hGmono hx01)).1
  have hplat := kgPlat (S := S) (κ := Om (1 + 1)) (G := G) (x0 := x0) hκ2 hGmono h0 hx0
    (fun a b => mxOm2_mem a b) (fun n => by
      have hbm : (KaT.up β t₂).bm ∈ S.CSet (G (kgX S (Om (1 + 1)) G x0 n))
          (S.psi (G (kgX S (Om (1 + 1)) G x0 n)) (Om (1 + 1))) := by
        rw [← kgX_succ]
        exact htw.bm2 _ _ ((psiS_bounds (S := S) _ 1).1.le.trans_eq (by rw [kgX_succ])) (hq.trans_le (hx1 n))
      have h := KaT.gapK (S := S) hκ2 _ hbm
      rw [← hfun, ← kgX_succ] at h
      exact h)
  -- the iterates are those of `Kb.kbV`
  have hxeq : ∀ n, kgX S (Om (1 + 1)) G x0 n = kbV S β C (n + 1) := by
    intro n
    induction n with
    | zero => rw [kgX_zero, kbV_succ, kbV_zero]
    | succ n ih => rw [kgX_succ, ih, kbV_succ (n + 1)]
  intro u' hu'
  have hlt : ∀ n, kgX S (Om (1 + 1)) G x0 n < Om (1 + 1) := fun n => by
    cases n with
    | zero => exact hx0
    | succ n => rw [kgX_succ]; exact psi_lt hκ2 _
  have hbdd : BddAbove (range (kgX S (Om (1 + 1)) G x0)) := ⟨Om (1 + 1), by rintro _ ⟨n, rfl⟩; exact (hlt n).le⟩
  obtain ⟨n, hn⟩ := (lt_ciSup_iff hbdd).1 (hu'.trans_le hplat)
  rw [hxeq n] at hn
  exact kbV_own hC (n + 1) u' hn

end Googology.Trans.PoR.InaccPsi.R2.Kk

#print axioms Googology.Trans.PoR.InaccPsi.R2.Kk.kkOwn

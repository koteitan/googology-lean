import Googology.Trans.PoR.InaccPsi.R2.KtLvl

/-!
# Kt: THE OWNERSHIP OF EVERY CONTEXT, WITH NO THRESHOLD

`W^x = leWe x`.  The plateau `Kg.kgPlat` at a level `κ` asks the gap of `G` at the closures of its iterates; by
`Kt.ktG_KaT` every tower has that gap with no hypothesis on its constants.  So the ownership needs no threshold:

* `ktOwn` (**THE OWNERSHIP AT LEVEL `κ`**: for a monotone `G` with the gap at every `Cl(a, ψ_κ a)`, every
  `u < ψ_κ(G(κ))` has `u < ψ_κ(G(u))`),
* `ktOwnTw` (every tower `Ka.KaT`, level `Ω₂`), `ktOwnCtx` (**`Kk.kkOwn` with no threshold**: every context `C`
  with a `D`-level tower), `ktOwnBase` (`Kg.kgOwnBase` with no threshold).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kt

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ka Googology.Trans.PoR.InaccPsi.R2.Kg
  Googology.Trans.PoR.InaccPsi.R2.Kk

variable {S : InaccSeq.{0}}

/-- **THE OWNERSHIP AT LEVEL `κ`**: every `u < ψ_κ(G(κ))` has `u < ψ_κ(G(u))`. -/
theorem ktOwn {κ : Ordinal.{0}} (hκ : S.InR κ) (hκC : ∀ a b : Ordinal.{0}, κ ∈ S.CSet a b)
    {G : Ordinal.{0} → Ordinal.{0}} (hG : Monotone G)
    (hgap : ∀ a, KgGap κ G (S.CSet a (S.psi a κ)) (S.psi a κ)) :
    ∀ u, u < S.psi (G κ) κ → u < S.psi (G u) κ := by
  set x0 := S.psi (G 0) κ with hx0def
  have h0 : x0 ≤ kgX S κ G x0 1 := by
    rw [kgX_succ, kgX_zero]; exact (psi_mono hκ (hG zero_le)).1
  have hx0 : x0 < κ := psi_lt hκ _
  have hplat := kgPlat (S := S) (κ := κ) (G := G) (x0 := x0) hκ hG h0 hx0 hκC (fun n => hgap _)
  have hown : ∀ n, ∀ u, u < kgX S κ G x0 n → u < S.psi (G u) κ := by
    intro n
    induction n with
    | zero =>
      intro u hu
      rw [kgX_zero] at hu
      exact hu.trans_le (psi_mono hκ (hG zero_le)).1
    | succ n ih =>
      intro u hu
      rcases lt_or_ge u (kgX S κ G x0 n) with h | h
      · exact ih u h
      · rw [kgX_succ] at hu
        exact hu.trans_le (psi_mono hκ (hG h)).1
  have hlt : ∀ n, kgX S κ G x0 n < κ := fun n => by
    cases n with
    | zero => exact hx0
    | succ n => rw [kgX_succ]; exact psi_lt hκ _
  have hbdd : BddAbove (range (kgX S κ G x0)) := ⟨κ, by rintro _ ⟨n, rfl⟩; exact (hlt n).le⟩
  intro u hu
  obtain ⟨n, hn⟩ := (lt_ciSup_iff hbdd).1 (hu.trans_le hplat)
  exact hown n u hn

/-- **The ownership of every tower** at the level `Ω₂`. -/
theorem ktOwnTw (t : KaT) :
    ∀ u, u < S.psi (t.ev (Om (1 + 1))) (Om (1 + 1)) → u < S.psi (t.ev u) (Om (1 + 1)) :=
  ktOwn (InR_Om_succ 1) (fun a b => mxOm2_mem a b) (KaT.ev_mono t)
    (fun a => ktG_KaT (ktCl_CSet (InR_Om_succ 1) a) t)

/-- **`Kk.kkOwn` with no threshold**: every context `C` with a `D`-level tower. -/
theorem ktOwnCtx {β : Ordinal.{0}} {C : Ordinal.{0} → Ordinal.{0}} {t₂ : KaT}
    (hev : ∀ v, Om (1 + 1) * C v = t₂.ev v) :
    ∀ u, u < S.psi (β + leWe (C (Om (1 + 1)))) (Om (1 + 1)) → u < S.psi (β + leWe (C u)) (Om (1 + 1)) := by
  have hG : ∀ v, β + leWe (C v) = (KaT.up β t₂).ev v := fun v => by
    rw [KaT.ev_up, ← hev v]; rfl
  intro u hu
  rw [hG] at hu ⊢
  exact ktOwnTw (KaT.up β t₂) u hu

/-- **`Kg.kgOwnBase` with no threshold**: below `ψ₂(β + W^{g₀ + W^{j+1}})` every `u` has
`u < ψ₂(β + W^{g₀ + W^j·u})`. -/
theorem ktOwnBase {β g₀ j : Ordinal.{0}} :
    ∀ u, u < S.psi (β + leWe (g₀ + leWe (j + 1))) (Om (1 + 1)) →
      u < S.psi (β + leWe (g₀ + leWe j * u)) (Om (1 + 1)) := by
  have h := ktOwnCtx (S := S) (β := β) (C := fun v => g₀ + leWe j * v)
    (t₂ := KaT.base (Om (1 + 1) * g₀) (Om (1 + 1) + Om (1 + 1) * j))
    (fun v => by
      show Om (1 + 1) * (g₀ + leWe j * v) = _
      rw [KaT.ev_base]
      unfold leWe
      rw [mul_add, ← mul_assoc, kg_Om2_mul_opow])
  intro u hu
  refine h u ?_
  show u < S.psi (β + leWe (g₀ + leWe j * Om (1 + 1))) (Om (1 + 1))
  rw [← leWe_succ]; exact hu

end Googology.Trans.PoR.InaccPsi.R2.Kt

#print axioms Googology.Trans.PoR.InaccPsi.R2.Kt.ktOwn
#print axioms Googology.Trans.PoR.InaccPsi.R2.Kt.ktOwnCtx
#print axioms Googology.Trans.PoR.InaccPsi.R2.Kt.ktOwnBase

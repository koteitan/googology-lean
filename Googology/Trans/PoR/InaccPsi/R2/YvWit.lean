import Googology.Trans.PoR.InaccPsi.R2.YvLev
import Googology.Trans.PoR.InaccPsi.R2.XjFrag

/-!
# The hull clause with moving levels below `θ` (statement), its constant-level case, and the one-moving-leaf node

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

FRAG (`Xj.xjFragV`) gives the hull clause `Xj.XjCl L` at top `ϑ`-nodes whose level `Ω₁·q` is a constant (`Xe.XeLev`:
data below the bottom `κ`).  The clause the shift `Yq.XoShift2` needs moves the leaves of the level.  With the leaf
substitution `Yv.yvSub` below `θ` it reads `YvCl` below.

* `yv_sub_fix` (**`yvSub Ψ z = z` when `Ψ` fixes every ordinal below `q > d_S(z)`**);
* `YvCl` (**the hull clause at top `ϑ`-nodes with moving levels below `θ`**, a statement: `Ψ(ϑ^{b_k}(Ω₁·q +
  r[b_k])) = ϑ^{c_k}(yvSub Ψ (Ω₁·q) + (vmap Ψ r)[c_k])`), `yv_cl_const` (**at constant levels `B₂ ≤ q < θ` it is the
  proved clause `Xj.XjCl Xe.XeLev`**: non-vacuity, and the new statement extends the old one), `yv_cl_frag`
  (**the FRAG map of `Xj.xjFragXe` satisfies `YvCl` at every constant level**);
* the node with one moving leaf, the base itself (`ϑᵗ(Ω₁·(B₂ + τ) + ρ)`, REFUTE FIRST): `yv_wit_level` (`Ω₁·(B₂ + τ)
  = B₂ + Ω₁·τ`), `yv_wit_pi` (**compression: `π(ϑᵗ(Ω₁·(B₂ + τ) + ρ)) = ϑ^σ(Ω₁·(B₂ + σ) + π ρ)`**, the leaf substitution
  `τ ↦ σ`), `yv_wit_hi` (**the translation keeps the argument there**: the leaf `α` of `B₂ + α` is not below `α`, so
  the subcase is `Γ^* ≥ α`, `R2.xoVt_trH`; the leaf `α` is then moved by the next map, as the substitution says).

No new axiom.  New definition: `YvCl` (a statement).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul Googology.Trans.PoR.InaccPsi.R2.Uc
  Googology.Trans.PoR.InaccPsi.R2.Un Googology.Trans.PoR.InaccPsi.R2.Ur Googology.Trans.PoR.InaccPsi.R2.Vi

variable {S : InaccSeq.{0}}

/-- **`yvSub Ψ z = z`** when `Ψ` fixes every ordinal below a strongly critical `q > d_S(z)` (`z < θ`, `q ≤ Ω₁`). -/
theorem yv_sub_fix {Ψ : Ordinal.{0} → Ordinal.{0}} {q z : Ordinal.{0}} (hz : z < ConjT.th S) (hq : SC q)
    (hq1 : q ≤ Om1) (hd : Vd.vdD S 0 z < q) (hΨ : ∀ x, x < q → Ψ x = x) : yvSub S Ψ z = z := by
  have hL := (yv_dat_iff hq hq1 hz).1 hd
  obtain ⟨r, hG, hr⟩ := yv_bound (S := S) hz
  have hid : YvR S id z z := yv_sub_id r z hL hG hr
  exact yvSub_eq (yvR_congr (hL.mono fun x hx => (hΨ x hx).symm) hid)

/-- **The hull clause at top `ϑ`-nodes with moving levels below `θ`** (open in general): for every `k < m`, a level
`Ω₁·q` (`1 ≤ q`, `Ω₁·q < θ`) whose leaves lie in `(F ∪ κ) ∩ T^{b_k}`, and a term `r` of `Un.UnC` with the node
conditions over `b_k`, parameters in `F ∩ T^{b_k}`, level leaves in `(F ∪ κ) ∩ T^{b_k}`, `r[b_k] < Ω₁`, if the node
`ϑ^{b_k}(Ω₁·q + r[b_k])` lies in `F ∩ seg(b_k)` then `Ψ` maps it to `ϑ^{c_k}(yvSub Ψ (Ω₁·q) + (vmap Ψ r)[c_k])`, and
the image term has the node conditions over `c_k`. -/
def YvCl (S : InaccSeq.{0}) (κ : Ordinal.{0}) (b c : ℕ → Ordinal.{0}) (m : ℕ) (F : Finset Ordinal.{0})
    (Ψ : Ordinal.{0} → Ordinal.{0}) : Prop :=
  ∀ k, k < m → ∀ (q : Ordinal.{0}) (r : UnC), 1 ≤ q → Om1 * q < ConjT.th S →
    YvLv S (fun p => p ∈ F ∨ p < κ) (Om1 * q) → YvLv S (· ∈ Tset (b k)) (Om1 * q) →
    ZW (b k) r → WFr (b k) r → UnT.ev (b k) r < Om1 →
    UnT.Lv (· ∈ F) r → ZL (fun p => p ∈ F ∨ p < κ) r → UnT.Lv (· ∈ Tset (b k)) r → ZL (· ∈ Tset (b k)) r →
    vt (b k) (Om1 * q + UnT.ev (b k) r) ∈ F → InSeg (b k) (vt (b k) (Om1 * q + UnT.ev (b k) r)) →
      Ψ (vt (b k) (Om1 * q + UnT.ev (b k) r)) = vt (c k) (yvSub S Ψ (Om1 * q) + UnT.ev (c k) (vmap Ψ r)) ∧
        WFr (c k) (vmap Ψ r) ∧ ZW (c k) (vmap Ψ r) ∧ UnT.ev (c k) (vmap Ψ r) < Om1

/-- **At constant levels `B₂ ≤ q < θ` (datum below a strongly critical `q₀ ≤ κ`) `YvCl` is the proved clause
`Xj.XjCl Xe.XeLev`**, for every map `Ψ` that fixes the ordinals below `κ`. -/
theorem yv_cl_const {κ : Ordinal.{0}} {b c : ℕ → Ordinal.{0}} {m : ℕ} {F : Finset Ordinal.{0}}
    {Ψ : Ordinal.{0} → Ordinal.{0}} (hX : Xj.XjCl Xe.XeLev κ b c m F Ψ) (hid : ∀ x, x < κ → Ψ x = x)
    (hκ1 : κ ≤ Om1) :
    ∀ k, k < m → ∀ (q q₀ : Ordinal.{0}) (r : UnC), ucB ≤ q → q < ConjT.th S → SC q₀ → q₀ ≤ κ →
      Vd.vdD S 0 q < q₀ →
      ZW (b k) r → WFr (b k) r → UnT.ev (b k) r < Om1 →
      UnT.Lv (· ∈ F) r → ZL (fun p => p ∈ F ∨ p < κ) r → UnT.Lv (· ∈ Tset (b k)) r → ZL (· ∈ Tset (b k)) r →
      vt (b k) (Om1 * q + UnT.ev (b k) r) ∈ F → InSeg (b k) (vt (b k) (Om1 * q + UnT.ev (b k) r)) →
        Ψ (vt (b k) (Om1 * q + UnT.ev (b k) r)) = vt (c k) (yvSub S Ψ (Om1 * q) + UnT.ev (c k) (vmap Ψ r)) ∧
          WFr (c k) (vmap Ψ r) ∧ ZW (c k) (vmap Ψ r) ∧ UnT.ev (c k) (vmap Ψ r) < Om1 := by
  intro k hk q q₀ r hB hθ hq₀ hq₀κ hd hz hw hρ1 hl hzl hlT hzT hxF hs
  have hlev : Xe.XeLev κ q := Or.inr ⟨hB, S, hθ, q₀, hq₀, hq₀κ, hd⟩
  obtain ⟨e, h2, h3, h4⟩ := hX k hk q r hlev hz hw hρ1 hl hzl hlT hzT hxF hs
  have hfix : yvSub S Ψ (Om1 * q) = Om1 * q :=
    yv_sub_fix (Xe.xe_mul_lt_th hθ) hq₀ (hq₀κ.trans hκ1) (Xe.xe_Om1_mul_dat hq₀ hd)
      fun x hx => hid x (hx.trans_le hq₀κ)
  exact ⟨by rw [hfix]; exact e, h2, h3, h4⟩

/-- **The FRAG map satisfies the moving-level clause at every constant level** (`Xj.xjFragXe`): non-vacuity of
`YvCl` on its constant part. -/
theorem yv_cl_frag {m : ℕ} {κ : Ordinal.{0}} {b c : ℕ → Ordinal.{0}} (hb : Chain κ b m) (hc : Chain κ c m)
    (F : Finset Ordinal.{0}) (hF : ↑F ⊆ DD κ b m) :
    ∃ Ψ, Vl.VlFragConcl κ b c m F Ψ ∧ Xj.XjCl Xe.XeLev κ b c m F Ψ ∧
      ∀ k, k < m → ∀ (q q₀ : Ordinal.{0}) (r : UnC), ucB ≤ q → q < ConjT.th S → SC q₀ → q₀ ≤ κ →
        Vd.vdD S 0 q < q₀ →
        ZW (b k) r → WFr (b k) r → UnT.ev (b k) r < Om1 →
        UnT.Lv (· ∈ F) r → ZL (fun p => p ∈ F ∨ p < κ) r → UnT.Lv (· ∈ Tset (b k)) r →
        ZL (· ∈ Tset (b k)) r →
        vt (b k) (Om1 * q + UnT.ev (b k) r) ∈ F → InSeg (b k) (vt (b k) (Om1 * q + UnT.ev (b k) r)) →
          Ψ (vt (b k) (Om1 * q + UnT.ev (b k) r)) = vt (c k) (yvSub S Ψ (Om1 * q) + UnT.ev (c k) (vmap Ψ r)) ∧
            WFr (c k) (vmap Ψ r) ∧ ZW (c k) (vmap Ψ r) ∧ UnT.ev (c k) (vmap Ψ r) < Om1 := by
  obtain ⟨Ψ, hV, hX⟩ := Xj.xjFragXe hb hc F hF
  exact ⟨Ψ, hV, hX, yv_cl_const hX hV.2.2.2 hb.kap1.le⟩

/-! ## The node with one moving leaf: the base `τ` inside the level `B₂ + τ` -/

theorem yv_B_eps : ω ^ (ucB : Ordinal.{0}) = ucB := Gg.gg_SC_eps ucB_SC

/-- `Ω₁·(B₂ + τ) = B₂ + Ω₁·τ`. -/
theorem yv_wit_level (τ : Ordinal.{0}) : Om1 * (ucB + τ) = ucB + Om1 * τ := by
  have hadd : Om1 + ucB = ucB :=
    Ordinal.add_of_omega0_opow_le (by rw [yv_B_eps]; exact ucB_gt) (by rw [yv_B_eps])
  have hmul : Om1 * ucB = ucB := by
    calc Om1 * ucB = Om1 * ω ^ ucB := by rw [yv_B_eps]
      _ = ω ^ (Om1 + ucB) := Si.si_Om1_opow_eq ucB
      _ = ucB := by rw [hadd, yv_B_eps]
  rw [mul_add, hmul]

/-- **Compression at the one-moving-leaf node**: `π_{σ,τ}(ϑᵗ(Ω₁·(B₂ + τ) + ρ)) = ϑ^σ(Ω₁·(B₂ + σ) + π ρ)` (bases with
`Γ₀ ≤ σ`, `ρ ∈ Tᵗ[σ] ∩ Ω₁`): the leaf substitution `τ ↦ σ` of the level. -/
theorem yv_wit_pi (S : InaccSeq.{0}) {σ τ ρ : Ordinal.{0}} (h : Bases σ τ) (hσ : gamma 0 ≤ σ)
    (hρ : ρ ∈ TB τ σ) (hρ1 : ρ < Om1) :
    Om1 * (ucB + τ) + ρ ∈ TB τ σ ∧
      pi σ τ (vt τ (Om1 * (ucB + τ) + ρ)) = vt σ (Om1 * (ucB + σ) + pi σ τ ρ) := by
  obtain ⟨hBT, hBπ⟩ := yv_B_fix S h hσ
  obtain ⟨hτT, hτπ⟩ := pi_base h
  obtain ⟨hmT, hmπ⟩ := lvPi_mul h hτT le_rfl h.2.2.2
  obtain ⟨a1, a2⟩ := pi_add h hBT hmT
  obtain ⟨b1, b2⟩ := pi_add h a1 hρ
  rw [← yv_wit_level] at a1 a2 b1 b2
  refine ⟨b1, ?_⟩
  have h2 : Om1 * (ucB + τ) + ρ < OmTwo := by
    have hθ : Om1 * (ucB + τ) < ConjT.th S := by
      rw [yv_wit_level]
      exact (Xe.xe_th S).1.add_lt Vd.vd_B_lt_th
        (Xe.xe_mul_lt_th ((h.2.2.2).trans (Xe.xe_th S).2.1))
    exact ((Xe.xe_th S).1.add_lt hθ (hρ1.trans (Xe.xe_th S).2.1)).trans (Xe.xe_th S).2.2
  rw [pi_vt_two h b1 h2, b2, a2, hBπ, hmπ, hτπ, ← yv_wit_level]

/-- **The translation keeps the argument at the one-moving-leaf node**: for a strongly critical `α < Ω₁`, the leaf
`α` of `B₂ + α` is not below `α` (`Xo.xo_dat_ge`), so the subcase of [W07a] Def 6.2 is `Γ^* ≥ α` (`R2.xoVt_trH`). -/
theorem yv_wit_hi {α : Ordinal.{0}} (hα : SC α) (hα1 : α < Om1) : ¬ YvLv S (· < α) (ucB + α) := by
  intro hL
  have hθ : ucB + α < ConjT.th S := (Xe.xe_th S).1.add_lt Vd.vd_B_lt_th (hα1.trans (Xe.xe_th S).2.1)
  have hd := (yv_dat_iff hα hα1.le hθ).2 hL
  exact absurd (Xo.xo_dat_ge (S := S) hα hα1) (not_le.2 hd)

end Googology.Trans.PoR.InaccPsi.R2.Yv

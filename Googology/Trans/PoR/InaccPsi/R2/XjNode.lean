import Googology.Trans.PoR.InaccPsi.R2.XeShift

/-!
# A `ϑ`-node at a constant level with the level bound as a parameter: the node lemmas and the hull clause

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

The FRAG term language `Un.UnC` with the node conditions `Vi.ZW` has the node `thc q r` only at levels `Ω₁·q < B₂`
(`Vi.Nz.qB`).  Here a **top node** `ϑ^τ(Ω₁·q + r[τ])` over a term `r` of `Un.UnC` (with `Vi.ZW`) is allowed at
every level `q` of a **level predicate** `L κ q` (`κ` the bottom of the chain), for which the node lemmas hold
(`XjNodeSys L`): the base change at the node, membership of the argument, `ρ < ϑ(Ω₁·q + ρ)`, the two translations
of [W07a] Def 6.2.  The predicate is a parameter: `XjLv Λ κ q` (a constant level `q < Λ`, `Xe.XeLev`) for any bound
`Λ`; `Λ = B₂` is the old case (`xjLv_B_iff`: exactly `Uy.UyLev`), `Λ = θ` the new one (`xjLv_th_B`: `q = B₂` is
a level).  The level `Ω₁·q` is a constant: its leaves lie below `κ`, every map of the chain fixes them.

* `xjNodeUy`, `xjNodeLvB` (**the old instance, levels below `B₂`, from `R2.uvVt_trL` only**);
* `XjNodeSys`, `xjNodeXe` (**the node lemmas at every constant level `Ω₁·q < θ`**, from `Xe.xeDown`, `Xe.xe_arg_T`,
  `Xe.xeLt_vt_self`, `Xe.xeVt_tr`), `XjLv`, `xjNodeLv`, `xjLv_B_iff`, `xjLv_th_B`;
* `XjNodeSys.nodeUp` (**`π⁻¹` at the node**), `XjNodeSys.nodeMv` (**the segment move at the node**);
* `XjCl` (**the hull clause at a top node of level `L`**: `Ψ(ϑ^{b_k}(Ω₁·q + r[b_k])) = ϑ^{c_k}(Ω₁·q + (vmap Ψ
  r)[c_k])`).

No new axiom.  New definitions: `XjNodeSys` (a structure of statements), `XjLv`, `XjCl` (Props).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xj

open Ordinal Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Un
  Googology.Trans.PoR.InaccPsi.R2.Ur Googology.Trans.PoR.InaccPsi.R2.Vi Googology.Trans.PoR.InaccPsi.R2.Xe

/-- **The node lemmas for a level predicate `L κ q`** (`κ` the bottom): base change, argument membership, the
countable part below the value, both translations of [W07a] Def 6.2 (`α = Dl τ n`, `α⁺ = Dp τ n`). -/
structure XjNodeSys (L : Ordinal.{0} → Ordinal.{0} → Prop) : Prop where
  down : ∀ {κ σ τ q ρ : Ordinal.{0}}, Bases σ τ → κ ≤ σ → L κ q → ρ ∈ TB τ σ → ρ < Om1 →
    vt τ (Om1 * q + ρ) ∈ TB τ σ ∧ pi σ τ (vt τ (Om1 * q + ρ)) = vt σ (Om1 * q + pi σ τ ρ)
  argT : ∀ {κ τ q x : Ordinal.{0}}, Bases κ τ → L κ q → x ∈ Tset τ → x < Om1 → Om1 * q + x ∈ Tset τ
  ltvt : ∀ {κ τ q x : Ordinal.{0}}, Bases κ τ → L κ q → x ∈ Tset τ → x < Om1 → x < vt τ (Om1 * q + x)
  trA : ∀ {κ τ q ρ : Ordinal.{0}} {n : ℕ}, Bases κ τ → 1 ≤ n → L κ q → ρ < Om1 →
    Om1 * q + ρ ∈ Tset (Dl τ n) → vt (Dl τ n) (Om1 * q + ρ) < Dp τ n →
    Om1 * q + (Dl τ n + ρ) ∈ Tset τ ∧ vt (Dl τ n) (Om1 * q + ρ) = vt τ (Om1 * q + (Dl τ n + ρ))
  trB : ∀ {κ τ q ρ : Ordinal.{0}} {n : ℕ}, Bases κ τ → 1 ≤ n → L κ q → ρ < Om1 →
    Om1 * q + (Dl τ n + ρ) ∈ Tset τ → vt τ (Om1 * q + (Dl τ n + ρ)) < Dp τ n →
    Om1 * q + ρ ∈ Tset (Dl τ n) ∧ vt τ (Om1 * q + (Dl τ n + ρ)) = vt (Dl τ n) (Om1 * q + ρ)

/-- **The node lemmas at every constant level `Ω₁·q < θ`** (`Xe.XeLev`). -/
theorem xjNodeXe : XjNodeSys XeLev where
  down h hκσ hq hρ hρ1 := xeDown h hκσ hq hρ hρ1
  argT hB hq hx hx1 := (xe_arg_T hB hq hx hx1).1
  ltvt hB hq hx hx1 := xeLt_vt_self hB hq hx hx1
  trA hB hn hq hρ1 h1 h2 := (xeVt_tr hB hn hq hρ1).1 h1 h2
  trB hB hn hq hρ1 h1 h2 := (xeVt_tr hB hn hq hρ1).2 h1 h2

/-- A smaller level predicate keeps the node lemmas. -/
theorem XjNodeSys.mono {L L' : Ordinal.{0} → Ordinal.{0} → Prop} (hL : ∀ κ q, L' κ q → L κ q)
    (h : XjNodeSys L) : XjNodeSys L' where
  down hB hκσ hq := h.down hB hκσ (hL _ _ hq)
  argT hB hq := h.argT hB (hL _ _ hq)
  ltvt hB hq := h.ltvt hB (hL _ _ hq)
  trA hB hn hq := h.trA hB hn (hL _ _ hq)
  trB hB hn hq := h.trB hB hn (hL _ _ hq)

/-- **The constant levels below the bound `Λ`**: `Xe.XeLev κ q` and `q < Λ`. -/
def XjLv (Λ κ q : Ordinal.{0}) : Prop := XeLev κ q ∧ q < Λ

/-- The node lemmas for every bound `Λ`. -/
theorem xjNodeLv (Λ : Ordinal.{0}) : XjNodeSys (XjLv Λ) := xjNodeXe.mono fun _ _ h => h.1

/-- **The old instance**: the levels below `B₂` are exactly the constant levels `Uy.UyLev` of `R2.UyTerm`. -/
theorem xjLv_B_iff {κ q : Ordinal.{0}} : XjLv Uc.ucB κ q ↔ Uy.UyLev κ q := by
  constructor
  · rintro ⟨h | ⟨hB, -⟩, hqB⟩
    · exact h
    · exact absurd hqB (not_lt.2 hB)
  · intro h
    exact ⟨Or.inl h, (xe_le_mul q).trans_lt h.2.1⟩

/-- **The new instance is larger**: `q = B₂` is a level below `θ` over every strongly critical `κ`, not a level below
`B₂`. -/
theorem xjLv_th_B (S : InaccSeq.{0}) {κ : Ordinal.{0}} (hκ : SC κ) :
    XjLv (ConjT.th S) κ Uc.ucB ∧ ¬ XjLv Uc.ucB κ Uc.ucB :=
  ⟨⟨(xeLev_B S hκ).1, Vd.vd_B_lt_th⟩, fun h => lt_irrefl _ h.2⟩

/-- **The old instance without the new citation**: the node lemmas at the levels `Uy.UyLev` (below `B₂`) from
`R2.uvVt_trL` only (`R2.xeVt_trL` is not used). -/
theorem xjNodeUy : XjNodeSys Uy.UyLev where
  down h hκσ hq hρ hρ1 := xeDown h hκσ (Or.inl hq) hρ hρ1
  argT hB hq hx hx1 := (xe_arg_T hB (Or.inl hq) hx hx1).1
  ltvt hB hq hx hx1 := xeLt_vt_self hB (Or.inl hq) hx hx1
  trA hB hn hq hρ1 h1 h2 := uvVt_trL hB.2.1 hB.2.2.2 hn hq.1 hq.2.1
    (hq.2.2.2.trans_le (hB.2.2.1.trans (Dl_E hB.2.1 hB.2.2.2 hn).1).le) hρ1 |>.1 h1 h2
  trB hB hn hq hρ1 h1 h2 := uvVt_trL hB.2.1 hB.2.2.2 hn hq.1 hq.2.1
    (hq.2.2.2.trans_le (hB.2.2.1.trans (Dl_E hB.2.1 hB.2.2.2 hn).1).le) hρ1 |>.2 h1 h2

/-- The bound-`B₂` instance `XjLv B₂` without the new citation. -/
theorem xjNodeLvB : XjNodeSys (XjLv Uc.ucB) := xjNodeUy.mono fun _ _ h => xjLv_B_iff.1 h

theorem xj_TB_mono {τ σ σ' x : Ordinal.{0}} (hx : x ∈ TB τ σ) (h : σ ≤ σ') : x ∈ TB τ σ' :=
  ⟨hx.1, fun _ hp => lt_of_lt_of_le (hx.2 hp) h⟩

/-- **`π⁻¹` at the node**: `up σ τ (ϑ^σ(Ω₁·q + ρ)) = ϑᵗ(Ω₁·q + up σ τ ρ)`. -/
theorem XjNodeSys.nodeUp {L : Ordinal.{0} → Ordinal.{0} → Prop} (hL : XjNodeSys L) {κ σ τ q ρ : Ordinal.{0}}
    (h : Bases σ τ) (hκσ : κ ≤ σ) (hq : L κ q) (hρ : ρ ∈ Tset σ) (hρ1 : ρ < Om1) :
    up σ τ (vt σ (Om1 * q + ρ)) = vt τ (Om1 * q + up σ τ ρ) ∧ vt τ (Om1 * q + up σ τ ρ) ∈ TB τ σ := by
  obtain ⟨u1, u2⟩ := up_spec h hρ
  have hu1 : up σ τ ρ < Om1 := up_lt_Om1 h hρ hρ1
  obtain ⟨d1, d2⟩ := hL.down h hκσ hq u1 hu1
  rw [u2] at d2
  rw [← d2, up_pi h d1]
  exact ⟨rfl, d1⟩

/-- **The segment move at the node**: for `ε`-bases `b, c < Ω₁` above `κ` and `ρ ∈ T^b[κ] ∩ Ω₁`:
`mv b c (ϑ^b(Ω₁·q + ρ)) = ϑ^c(Ω₁·q + mv b c ρ)`. -/
theorem XjNodeSys.nodeMv {L : Ordinal.{0} → Ordinal.{0} → Prop} (hL : XjNodeSys L) {κ b c q ρ : Ordinal.{0}}
    (hb : InE b) (hb1 : b < Om1) (hc : InE c) (hc1 : c < Om1) (hκb : κ ≤ b) (hκc : κ ≤ c) (hq : L κ q)
    (hρ : ρ ∈ TB b κ) (hρ1 : ρ < Om1) :
    mv b c (vt b (Om1 * q + ρ)) = vt c (Om1 * q + mv b c ρ) := by
  unfold mv
  rcases lt_trichotomy c b with hcb | hcb | hbc
  · rw [if_pos hcb]
    exact (hL.down ⟨hc, hb, hcb, hb1⟩ hκc hq (xj_TB_mono hρ hκc) hρ1).2
  · subst hcb; rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _)]; rfl
  · rw [if_neg (not_lt.2 hbc.le), if_pos hbc]
    exact (hL.nodeUp ⟨hb, hc, hbc, hc1⟩ hκb hq hρ.1 hρ1).1

/-- **The hull clause at a top node of level `L`**: for every `k < m`, a level `L κ q` and a term `r` of `Un.UnC`
with the node conditions over `b_k`, parameters in `F ∩ T^{b_k}`, level leaves in `(F ∪ κ) ∩ T^{b_k}` and
`r[b_k] < Ω₁`, if `ϑ^{b_k}(Ω₁·q + r[b_k]) ∈ F ∩ seg(b_k)` then `Ψ` maps it to `ϑ^{c_k}(Ω₁·q + (vmap Ψ r)[c_k])`,
and the image term has the argument bounds and node conditions over `c_k`, value below `Ω₁`.  (`Vl.VlCl` for the
term `thc q r` with the node condition `Vi.Nz` at the top replaced by `L κ q`.) -/
def XjCl (L : Ordinal.{0} → Ordinal.{0} → Prop) (κ : Ordinal.{0}) (b c : ℕ → Ordinal.{0}) (m : ℕ)
    (F : Finset Ordinal.{0}) (Ψ : Ordinal.{0} → Ordinal.{0}) : Prop :=
  ∀ k, k < m → ∀ (q : Ordinal.{0}) (r : UnC), L κ q → ZW (b k) r → WFr (b k) r → UnT.ev (b k) r < Om1 →
    UnT.Lv (· ∈ F) r → ZL (fun p => p ∈ F ∨ p < κ) r → UnT.Lv (· ∈ Tset (b k)) r → ZL (· ∈ Tset (b k)) r →
    vt (b k) (Om1 * q + UnT.ev (b k) r) ∈ F → InSeg (b k) (vt (b k) (Om1 * q + UnT.ev (b k) r)) →
      Ψ (vt (b k) (Om1 * q + UnT.ev (b k) r)) = vt (c k) (Om1 * q + UnT.ev (c k) (vmap Ψ r)) ∧
        WFr (c k) (vmap Ψ r) ∧ ZW (c k) (vmap Ψ r) ∧ UnT.ev (c k) (vmap Ψ r) < Om1

/-- `XjCl` is antitone in the level predicate. -/
theorem XjCl.mono {L L' : Ordinal.{0} → Ordinal.{0} → Prop} (hL : ∀ κ q, L' κ q → L κ q)
    {κ : Ordinal.{0}} {b c : ℕ → Ordinal.{0}} {m : ℕ} {F : Finset Ordinal.{0}} {Ψ : Ordinal.{0} → Ordinal.{0}}
    (h : XjCl L κ b c m F Ψ) : XjCl L' κ b c m F Ψ :=
  fun k hk q r hq => h k hk q r (hL _ _ hq)

end Googology.Trans.PoR.InaccPsi.R2.Xj

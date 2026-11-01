import Googology.Trans.PoR.InaccPsi.R2.XhCell

/-!
# Xh: the levels of the layer `c` (the frontier after (A3) is (A) again over the base `Γ(c)`)

In region (A) the systems over the base `G = Γ(0)` have bounds `φ(ℓ, G+1)` at levels `ℓ < Γ(1)`; the levels
`ℓ < G` reach exactly `φ(G, 1)` (`Wj.wjA2Cof`), the levels `G ≤ ℓ < Γ(1)` the rest (`Wj.wjA3Cof`).  The same holds
for EVERY atom index `c` with the base `Γ(c)`:

* `xhG_fix` (`φ(Γ(c), 0) = Γ(c)`), `xhLevCof` (**every `B < φ(Γ(c), 1)` is below `φ(ℓ, Γ(c)+1)` for some
  `ℓ < Γ(c)`**, generic in `c`, no cofinal sequence needed), `xhLevLo_lt` (`φ(ℓ, Γ(c)+1) < φ(Γ(c), 1)` for `ℓ < Γ(c)`);
* `xhLay_red` (**the layer `c` from its two level parts**: the old levels `ℓ < Γ(c)` over the base `Γ(c)`, and the
  new levels `Γ(c) ≤ ℓ < Γ(c+1)` that contain the atom `Γ(c)`), `xhLevLo_iff`;
* `xhHg_none` (no system `Hg.HgVD` over `G` reaches past region (A)).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xh

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2

variable {S : InaccSeq.{0}}

theorem xhG_fix (c : Ordinal.{0}) : veblen (Gc.gcG c) 0 = Gc.gcG c := by
  rw [Tf.tf_gcG]; exact veblen_gamma_zero _

theorem xhG_inE (c : Ordinal.{0}) : InE (Gc.gcG c) := Low.opow_eq_self_of_SC (Gc.gcG_SC c)

theorem xhG_add_one_lt (c : Ordinal.{0}) {a : Ordinal.{0}} (ha : a < Gc.gcG c) : a + 1 < Gc.gcG c :=
  (inE_indec (xhG_inE c)).add_lt ha (one_lt_omega0.trans (omega0_lt_inE (xhG_inE c)))

/-- `Γ(c) + 1 < φ(Γ(c), 1)`. -/
theorem xhG1_lt_vG1 (c : Ordinal.{0}) : Gc.gcG c + 1 < veblen (Gc.gcG c) 1 := by
  have hE := Wj.wjVeb_inE (a := Gc.gcG c) (b := 1) (Gc.gcG_SC c).1
  have hG : Gc.gcG c < veblen (Gc.gcG c) 1 := by
    conv_lhs => rw [← xhG_fix c]
    exact veblen_lt_veblen_iff_right.2 one_pos
  exact (inE_indec hE).add_lt hG (one_lt_omega0.trans (omega0_lt_inE hE))

/-- `φ(ℓ, Γ(c)+1) < φ(Γ(c), 1)` for `ℓ < Γ(c)`. -/
theorem xhLevLo_lt (c : Ordinal.{0}) {ℓ : Ordinal.{0}} (hℓ : ℓ < Gc.gcG c) :
    veblen ℓ (Gc.gcG c + 1) < veblen (Gc.gcG c) 1 :=
  calc veblen ℓ (Gc.gcG c + 1) < veblen ℓ (veblen (Gc.gcG c) 1) := veblen_lt_veblen_iff_right.2 (xhG1_lt_vG1 c)
    _ = veblen (Gc.gcG c) 1 := veblen_veblen_of_lt hℓ 1

/-- **The levels below `Γ(c)` reach exactly `φ(Γ(c), 1)`** (generic in `c`). -/
theorem xhLevCof (c : Ordinal.{0}) {B : Ordinal.{0}} (hB : B < veblen (Gc.gcG c) 1) :
    ∃ ℓ, ℓ < Gc.gcG c ∧ B < veblen ℓ (Gc.gcG c + 1) := by
  by_contra hcon
  push Not at hcon
  have hpos : 0 < Gc.gcG c := (Gc.gcG_SC c).1
  haveI : Nonempty (Iio (Gc.gcG c)) := ⟨⟨0, hpos⟩⟩
  set f : Iio (Gc.gcG c) → Ordinal.{0} := fun ℓ => veblen ℓ.1 (Gc.gcG c + 1) with hf
  have hbdd : BddAbove (Set.range f) := ⟨B, by rintro _ ⟨ℓ, rfl⟩; exact hcon ℓ.1 ℓ.2⟩
  set t := ⨆ ℓ, f ℓ with ht
  have htB : t ≤ B := ciSup_le fun ℓ => hcon ℓ.1 ℓ.2
  have hfix : ∀ b < Gc.gcG c, veblen b t = t := by
    intro b hb
    refine le_antisymm ?_ (right_le_veblen _ _)
    rw [(isNormal_veblen b).map_iSup hbdd]
    refine ciSup_le fun ℓ => ?_
    have hm : max b ℓ.1 + 1 < Gc.gcG c := xhG_add_one_lt c (max_lt hb ℓ.2)
    have h1 : veblen b (f ℓ) ≤ veblen b (f ⟨_, hm⟩) :=
      veblen_le_veblen_iff_right.2 (veblen_left_monotone _
        ((le_max_right b ℓ.1).trans (le_add_right le_rfl)))
    have h2 : veblen b (f ⟨_, hm⟩) = f ⟨_, hm⟩ :=
      veblen_veblen_of_lt ((le_max_left b ℓ.1).trans_lt (Order.lt_add_one_iff.2 le_rfl)) _
    exact (h1.trans h2.le).trans (le_ciSup hbdd _)
  obtain ⟨a, ha⟩ := (mem_range_veblen hpos.ne').2 hfix
  rcases eq_or_ne a 0 with h0 | h0
  · rw [h0, xhG_fix] at ha
    have h1 : Gc.gcG c + 1 ≤ f ⟨0, hpos⟩ := right_le_veblen _ _
    have h2 : f ⟨0, hpos⟩ ≤ t := le_ciSup hbdd _
    rw [← ha] at h2
    exact absurd (lt_add_one (Gc.gcG c)) (not_lt.2 (h1.trans h2))
  · have h1 : veblen (Gc.gcG c) 1 ≤ t := by
      rw [← ha]; exact veblen_le_veblen_iff_right.2 (Order.one_le_iff_ne_zero.2 h0)
    exact absurd (hB.trans_le (h1.trans htB)) (lt_irrefl B)

/-- **The layer `c` from its two level parts.** -/
theorem xhLay_red (P : Ordinal.{0} → Prop) (c : Ordinal.{0})
    (hLo : ∀ l, Cd.CdRange S l → XhPast S c l →
      (∃ ℓ, ℓ < Gc.gcG c ∧ l < Bt.iota S (Gc.gcG (veblen ℓ (Gc.gcG c + 1)) * ω)) → P l)
    (hHi : ∀ l, Cd.CdRange S l → XhPast S c l →
      (∀ ℓ, ℓ < Gc.gcG c → Bt.iota S (Gc.gcG (veblen ℓ (Gc.gcG c + 1)) * ω) ≤ l) →
      (∃ ℓ, Gc.gcG c ≤ ℓ ∧ ℓ < Gc.gcG (c + 1) ∧ l < Bt.iota S (Gc.gcG (veblen ℓ (Gc.gcG c + 1)) * ω)) → P l) :
    ∀ l, Cd.CdRange S l → XhLay S c l → P l := by
  intro l hr hL
  obtain ⟨B, hB, hlB⟩ := xhLay_bound hL
  by_cases hlo : ∃ ℓ, ℓ < Gc.gcG c ∧ l < Bt.iota S (Gc.gcG (veblen ℓ (Gc.gcG c + 1)) * ω)
  · exact hLo l hr hL.1 hlo
  push Not at hlo
  refine hHi l hr hL.1 hlo ⟨max B (Gc.gcG c), le_max_right _ _,
    max_lt hB (Gc.gcG_lt (Order.lt_add_one_iff.2 le_rfl)), hlB.trans_le ?_⟩
  refine Bt.iota_mono (S := S) _ _ ?_
  have h1 : B ≤ veblen (max B (Gc.gcG c)) (Gc.gcG c + 1) :=
    (le_max_left _ _).trans (left_le_veblen _ _)
  have h2 := Gc.gcG_le h1
  have hE : InE (Gc.gcG B) := xhG_inE B
  have hE' : InE (Gc.gcG (veblen (max B (Gc.gcG c)) (Gc.gcG c + 1))) := xhG_inE _
  calc Gc.gcG B * ω = ω ^ (Gc.gcG B + 1) := by
        conv_lhs => rw [← hE]
        rw [opow_add, opow_one]
    _ ≤ ω ^ (Gc.gcG (veblen (max B (Gc.gcG c)) (Gc.gcG c + 1)) + 1) :=
        opow_le_opow_right omega0_pos (add_le_add h2 le_rfl)
    _ = Gc.gcG (veblen (max B (Gc.gcG c)) (Gc.gcG c + 1)) * ω := by
        conv_rhs => rw [← hE']
        rw [opow_add, opow_one]

/-- **The lower levels of the layer `c` are the restarts below `ι(Γ(B)·ω)` with `B < φ(Γ(c), 1)`.** -/
theorem xhLevLo_iff (c l : Ordinal.{0}) :
    (∃ ℓ, ℓ < Gc.gcG c ∧ l < Bt.iota S (Gc.gcG (veblen ℓ (Gc.gcG c + 1)) * ω)) ↔
      ∃ B, B < veblen (Gc.gcG c) 1 ∧ l < Bt.iota S (Gc.gcG B * ω) := by
  constructor
  · rintro ⟨ℓ, hℓ, hl⟩; exact ⟨_, xhLevLo_lt c hℓ, hl⟩
  · rintro ⟨B, hB, hl⟩
    obtain ⟨ℓ, hℓ, hBℓ⟩ := xhLevCof c hB
    refine ⟨ℓ, hℓ, hl.trans_le (Bt.iota_mono (S := S) _ _ ?_)⟩
    have hE : InE (Gc.gcG B) := xhG_inE B
    have hE' : InE (Gc.gcG (veblen ℓ (Gc.gcG c + 1))) := xhG_inE _
    calc Gc.gcG B * ω = ω ^ (Gc.gcG B + 1) := by
          conv_lhs => rw [← hE]
          rw [opow_add, opow_one]
      _ ≤ ω ^ (Gc.gcG (veblen ℓ (Gc.gcG c + 1)) + 1) :=
          opow_le_opow_right omega0_pos (add_le_add (Gc.gcG_le hBℓ.le) le_rfl)
      _ = Gc.gcG (veblen ℓ (Gc.gcG c + 1)) * ω := by
          conv_rhs => rw [← hE']
          rw [opow_add, opow_one]

/-- **No system over `G` reaches region (B)**: every `Hg.HgVD` (the systems of `Ws.wsFam`, `Wo`, `Wx`, `Xc`) has
`B < Γ(1)`, so its frontier `ι(Γ(B)·ω)` is at most every restart past (A). -/
theorem xhHg_none (V : Hg.HgVD) {l : Ordinal.{0}} (hN : Wj.WjNotA S l) : Bt.iota S (Gc.gcG V.B * ω) ≤ l :=
  hN V.B V.B_lt1

end Googology.Trans.PoR.InaccPsi.R2.Xh

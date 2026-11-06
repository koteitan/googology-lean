import Googology.Trans.PoR.InaccPsi.R2.KtHCl

/-!
# Kt: THE GAP OF A CONTEXT OVER AN ABSTRACT CLOSURE (products, powers, `φ(d, ·)`), once for `Cl(a, ψ_κ a)` and `HCl`

`KgGap κ L C z` (`Kg.KgGap`): every member `e ∈ C` below `L(κ)` lies below `L(q + 1)` for some `q < z`.  An abstract
closure `KtCl C κ z` asks the closure facts used by the gaps: differences, the parts `ω^p·(x/ω^p)`, logarithms, the
`φ(d, ·)`-index of a member, and that the members below `κ` lie below the strongly critical `z`.

* `ktIdx` (**the `φ(d, ·)`-index of a member of `Cl(a, b)` is a member, every level `d`**; `Ta.taHull_idx` had
  `d < Γ₀`), `ktIdxH` (the same for `HCl`);
* `KtCl`, `ktCl_CSet` (`Cl(a, ψ_κ a)` with the bound `ψ_κ a`), `ktCl_HCl` (`HCl(a, Z)` with the bound `Z`);
* `ktG_mul` (**`b + ω^m·x`, no hypothesis on `m`**: the coefficient is bounded through its logarithm),
  `ktG_opow`, `ktG_phiR` (**`b + φ(d, L x)`**), `ktG_KaT` (**every tower `Ka.KaT`, no hypothesis**).

No new axiom.  New definition: `KtCl`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kt

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Ze Googology.Trans.PoR.InaccPsi.R2.Zx Googology.Trans.PoR.InaccPsi.R2.Ka
  Googology.Trans.PoR.InaccPsi.R2.Kg Googology.Trans.PoR.InaccPsi.R2.Ta

variable {S : InaccSeq.{0}}

/-- The index at a strongly critical `z` with `φ(d, 0) ≤ z`. -/
theorem ktIdxSC {d z : Ordinal.{0}} (hz : SC z) (h0 : veblen d 0 ≤ z) :
    ∃ u, (u = 0 ∨ u = z) ∧ veblen d u ≤ z ∧ z < veblen d (u + 1) := by
  rcases lt_trichotomy d z with hdz | rfl | hdz
  · exact ⟨z, Or.inr rfl, (hz.veblen_right hdz).le, by
      calc z = veblen d z := (hz.veblen_right hdz).symm
        _ < veblen d (z + 1) := (veblen_lt_veblen_iff_right).2 (lt_add_one z)⟩
  · refine ⟨0, Or.inl rfl, h0, ?_⟩
    rw [zero_add]
    calc d = veblen d 0 := hz.veblen_zero.symm
      _ < veblen d 1 := (veblen_lt_veblen_iff_right).2 zero_lt_one
  · exfalso
    have : z < veblen d 0 := by
      calc z = veblen z 0 := hz.veblen_zero.symm
        _ < veblen z (veblen d 0) := (veblen_lt_veblen_iff_right).2 veblen_pos
        _ = veblen d 0 := veblen_veblen_of_lt hdz 0
    exact absurd h0 (not_le.2 this)

/-- **The `φ(d, ·)`-index of a member of `Cl(a, b)` is a member**, every level `d`. -/
theorem ktIdx {A B d c : Ordinal.{0}} (hc : c ∈ S.CSet A B) (h0 : veblen d 0 ≤ c) :
    ∃ u ∈ S.CSet A B, veblen d u ≤ c ∧ c < veblen d (u + 1) := by
  have hSC : ∀ z, SC z → z ∈ S.CSet A B → veblen d 0 ≤ z →
      ∃ u ∈ S.CSet A B, veblen d u ≤ z ∧ z < veblen d (u + 1) := fun z hz hzm h0 => by
    obtain ⟨u, hu, h1, h2⟩ := ktIdxSC hz h0
    refine ⟨u, ?_, h1, h2⟩
    rcases hu with rfl | rfl
    · exact CSet.zero_mem _ _
    · exact hzm
  revert h0
  induction hc with
  | @small x hx =>
    intro h0
    obtain ⟨u, h1, h2⟩ := taIdx_ex h0
    exact ⟨u, CSet.of_lt (((right_le_veblen d u).trans h1).trans_lt hx), h1, h2⟩
  | zero => intro h0; exact absurd h0 (not_le.2 veblen_pos)
  | inacc n => exact hSC _ (SC_I n) (Clos.inacc n)
  | inaccW => exact hSC _ SC_Iw Clos.inaccW
  | @add x y hx hy ihx ihy =>
    intro h0
    have hP := Ph.ph_veblen_prin d 0
    by_cases hxa : veblen d 0 ≤ x
    · obtain ⟨u1, hc1, hu1, hx1⟩ := ihx hxa
      by_cases hya : veblen d 0 ≤ y
      · obtain ⟨u2, hc2, hu2, hy2⟩ := ihy hya
        refine ⟨max u1 u2, ?_, ?_, Ph.ph_veblen_prin d _ (hx1.trans_le ?_) (hy2.trans_le ?_)⟩
        · rcases le_total u1 u2 with h | h
          · rw [max_eq_right h]; exact hc2
          · rw [max_eq_left h]; exact hc1
        · rcases le_total u1 u2 with h | h
          · rw [max_eq_right h]; exact hu2.trans le_add_self
          · rw [max_eq_left h]; exact hu1.trans le_self_add
        · exact (veblen_le_veblen_iff_right).2 (add_le_add (le_max_left _ _) le_rfl)
        · exact (veblen_le_veblen_iff_right).2 (add_le_add (le_max_right _ _) le_rfl)
      · push Not at hya
        refine ⟨u1, hc1, hu1.trans le_self_add, Ph.ph_veblen_prin d _ hx1 (hya.trans_le ?_)⟩
        exact (veblen_le_veblen_iff_right).2 zero_le
    · push Not at hxa
      by_cases hya : veblen d 0 ≤ y
      · obtain ⟨u2, hc2, hu2, hy2⟩ := ihy hya
        refine ⟨u2, hc2, hu2.trans le_add_self, Ph.ph_veblen_prin d _ (hxa.trans_le ?_) hy2⟩
        exact (veblen_le_veblen_iff_right).2 zero_le
      · push Not at hya
        exact absurd h0 (not_le.2 (hP hxa hya))
  | @phi p q hp hq _ ihq =>
    intro h0
    rcases lt_trichotomy p d with hpa | rfl | hpa
    · have hq0 : veblen d 0 ≤ q := by
        by_contra hq
        push Not at hq
        have : veblen p q < veblen d 0 := by
          calc veblen p q < veblen p (veblen d 0) := (veblen_lt_veblen_iff_right).2 hq
            _ = veblen d 0 := veblen_veblen_of_lt hpa 0
        exact absurd h0 (not_le.2 this)
      obtain ⟨u, hu, h1, h2⟩ := ihq hq0
      refine ⟨u, hu, h1.trans (right_le_veblen p q), ?_⟩
      calc veblen p q < veblen p (veblen d (u + 1)) := (veblen_lt_veblen_iff_right).2 h2
        _ = veblen d (u + 1) := veblen_veblen_of_lt hpa _
    · exact ⟨q, hq, le_rfl, (veblen_lt_veblen_iff_right).2 (lt_add_one q)⟩
    · have hfix : veblen d (veblen p q) = veblen p q := veblen_veblen_of_lt hpa q
      refine ⟨veblen p q, Clos.phi hp hq, hfix.le, ?_⟩
      calc veblen p q = veblen d (veblen p q) := hfix.symm
        _ < veblen d (veblen p q + 1) := (veblen_lt_veblen_iff_right).2 (lt_add_one _)
  | @om x hx _ =>
    intro h0
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero] at h0; exact absurd h0 (not_le.2 veblen_pos)
    · exact hSC _ (SC_Om hx0) (Clos.om hx) h0
  | @coll π e hπ hπC heC _ _ =>
    exact hSC _ (SC_psi hπ e.1) (Clos.coll hπ hπC heC)

/-- **The `φ(d, ·)`-index of a member of `HCl(a, Z)` is a member.** -/
theorem ktIdxH {a Z d c : Ordinal.{0}} (hc : HCl S a Z c) (h0 : veblen d 0 ≤ c) :
    ∃ u, HCl S a Z u ∧ veblen d u ≤ c ∧ c < veblen d (u + 1) := by
  have hSC : ∀ z, SC z → HCl S a Z z → veblen d 0 ≤ z →
      ∃ u, HCl S a Z u ∧ veblen d u ≤ z ∧ z < veblen d (u + 1) := fun z hz hzm h0 => by
    obtain ⟨u, hu, h1, h2⟩ := ktIdxSC hz h0
    refine ⟨u, ?_, h1, h2⟩
    rcases hu with rfl | rfl
    · exact HCl.zero
    · exact hzm
  revert h0
  induction hc with
  | @small x hx =>
    intro h0
    obtain ⟨u, h1, h2⟩ := taIdx_ex h0
    exact ⟨u, HCl.small (((right_le_veblen d u).trans h1).trans_lt hx), h1, h2⟩
  | zero => intro h0; exact absurd h0 (not_le.2 veblen_pos)
  | inacc n => exact hSC _ (SC_I n) (HCl.inacc n)
  | inaccW => exact hSC _ SC_Iw HCl.inaccW
  | @add x y hx hy ihx ihy =>
    intro h0
    have hP := Ph.ph_veblen_prin d 0
    by_cases hxa : veblen d 0 ≤ x
    · obtain ⟨u1, hc1, hu1, hx1⟩ := ihx hxa
      by_cases hya : veblen d 0 ≤ y
      · obtain ⟨u2, hc2, hu2, hy2⟩ := ihy hya
        refine ⟨max u1 u2, ?_, ?_, Ph.ph_veblen_prin d _ (hx1.trans_le ?_) (hy2.trans_le ?_)⟩
        · rcases le_total u1 u2 with h | h
          · rw [max_eq_right h]; exact hc2
          · rw [max_eq_left h]; exact hc1
        · rcases le_total u1 u2 with h | h
          · rw [max_eq_right h]; exact hu2.trans le_add_self
          · rw [max_eq_left h]; exact hu1.trans le_self_add
        · exact (veblen_le_veblen_iff_right).2 (add_le_add (le_max_left _ _) le_rfl)
        · exact (veblen_le_veblen_iff_right).2 (add_le_add (le_max_right _ _) le_rfl)
      · push Not at hya
        refine ⟨u1, hc1, hu1.trans le_self_add, Ph.ph_veblen_prin d _ hx1 (hya.trans_le ?_)⟩
        exact (veblen_le_veblen_iff_right).2 zero_le
    · push Not at hxa
      by_cases hya : veblen d 0 ≤ y
      · obtain ⟨u2, hc2, hu2, hy2⟩ := ihy hya
        refine ⟨u2, hc2, hu2.trans le_add_self, Ph.ph_veblen_prin d _ (hxa.trans_le ?_) hy2⟩
        exact (veblen_le_veblen_iff_right).2 zero_le
      · push Not at hya
        exact absurd h0 (not_le.2 (hP hxa hya))
  | @phi p q hp hq _ ihq =>
    intro h0
    rcases lt_trichotomy p d with hpa | rfl | hpa
    · have hq0 : veblen d 0 ≤ q := by
        by_contra hq
        push Not at hq
        have : veblen p q < veblen d 0 := by
          calc veblen p q < veblen p (veblen d 0) := (veblen_lt_veblen_iff_right).2 hq
            _ = veblen d 0 := veblen_veblen_of_lt hpa 0
        exact absurd h0 (not_le.2 this)
      obtain ⟨u, hu, h1, h2⟩ := ihq hq0
      refine ⟨u, hu, h1.trans (right_le_veblen p q), ?_⟩
      calc veblen p q < veblen p (veblen d (u + 1)) := (veblen_lt_veblen_iff_right).2 h2
        _ = veblen d (u + 1) := veblen_veblen_of_lt hpa _
    · exact ⟨q, hq, le_rfl, (veblen_lt_veblen_iff_right).2 (lt_add_one q)⟩
    · have hfix : veblen d (veblen p q) = veblen p q := veblen_veblen_of_lt hpa q
      refine ⟨veblen p q, HCl.phi hp hq, hfix.le, ?_⟩
      calc veblen p q = veblen d (veblen p q) := hfix.symm
        _ < veblen d (veblen p q + 1) := (veblen_lt_veblen_iff_right).2 (lt_add_one _)
  | @om x hx _ =>
    intro h0
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero] at h0; exact absurd h0 (not_le.2 veblen_pos)
    · exact hSC _ (SC_Om hx0) (HCl.om hx) h0
  | @coll π e hπ hπ1 hπC heC he _ _ =>
    exact hSC _ (SC_psi hπ e) (HCl.coll hπ hπ1 hπC heC he)

/-- **An abstract closure for the gaps**: differences, the parts `ω^p·(x/ω^p)`, logarithms, `φ(d, ·)`-indices, and
the members below `κ` lie below the strongly critical `z`. -/
structure KtCl (C : Set Ordinal.{0}) (κ z : Ordinal.{0}) : Prop where
  sub : ∀ x ∈ C, ∀ y, x - y ∈ C
  part : ∀ x ∈ C, ∀ p : Ordinal.{0}, ω ^ p * (x / ω ^ p) ∈ C
  log : ∀ x ∈ C, log ω x ∈ C
  idx : ∀ d, ∀ x ∈ C, veblen d 0 ≤ x → ∃ u ∈ C, veblen d u ≤ x ∧ x < veblen d (u + 1)
  bnd : ∀ q ∈ C, q < κ → q < z
  zSC : SC z

/-- `Cl(a, ψ_κ a)` with the bound `ψ_κ a`. -/
theorem ktCl_CSet {κ : Ordinal.{0}} (hκ : S.InR κ) (a : Ordinal.{0}) :
    KtCl (S.CSet a (S.psi a κ)) κ (S.psi a κ) :=
  ⟨fun x hx y => taSub_mem x hx y, fun x hx p => (Vh.vhC_div x hx p).1, fun _ hx => Le.leLog_mem hx,
    fun _ _ hx h0 => ktIdx hx h0, fun _ hq hqκ => lt_psi_of_mem hκ hq hqκ, SC_psi hκ a⟩

/-- `HCl(a, Z)` with the bound `Z`. -/
theorem ktCl_HCl {a Z : Ordinal.{0}} (hZ : SC Z) : KtCl {x | HCl S a Z x} (Om 1) Z :=
  ⟨fun x hx y => ktHCl_sub x hx y, fun x hx p => (ktHCl_div x hx p).1, fun _ hx => ktHCl_log hx,
    fun _ _ hx h0 => ktIdxH hx h0, fun _ hq hq1 => HCl_lt hZ hq hq1, hZ⟩

section Gap

variable {C : Set Ordinal.{0}} {κ z : Ordinal.{0}}

/-- A member `q < κ` of the form `q = x / ω^m` with `ω^m·q ∈ C` lies below `z`. -/
theorem ktQ_lt (hC : KtCl C κ z) {m q : Ordinal.{0}} (hq : ω ^ m * q ∈ C) (hqκ : q < κ) : q < z := by
  rcases eq_or_ne q 0 with rfl | hq0
  · exact hC.zSC.1
  have hlog : log ω (ω ^ m * q) = m + log ω q := by
    have := log_opow_mul_add (b := ω) (u := m) (v := q) (w := 0) one_lt_omega0 hq0 (opow_pos _ omega0_pos)
    rwa [add_zero] at this
  have hl : log ω q ∈ C := by
    have h := hC.sub _ (hC.log _ hq) m
    rwa [hlog, Ordinal.add_sub_cancel] at h
  have hlz : log ω q < z := hC.bnd _ hl ((log_le_self ω q).trans_lt hqκ)
  calc q < ω ^ (log ω q + 1) := lt_opow_succ_log_self one_lt_omega0 q
    _ < z := by
      have h1 : log ω q + 1 < z := hC.zSC.isSuccLimit.add_one_lt hlz
      rw [← Low.opow_eq_self_of_SC hC.zSC]
      exact (opow_lt_opow_iff_right one_lt_omega0).2 h1

/-- **The gap of `b + ω^m·x`**, no hypothesis on `m`. -/
theorem ktG_mul (hC : KtCl C κ z) (b m : Ordinal.{0}) : KgGap κ (fun x => b + ω ^ m * x) C z := by
  intro e he hlt
  have hM0 : ω ^ m ≠ 0 := (opow_pos _ omega0_pos).ne'
  rcases lt_or_ge e b with h1 | h1
  · refine ⟨0, hC.zSC.1, ?_⟩
    show e < b + ω ^ m * (0 + 1)
    rw [zero_add, mul_one]; exact h1.trans_le le_self_add
  · have hsub : e - b < ω ^ m * κ := Ry.rySub_lt h1 hlt
    set q := (e - b) / ω ^ m with hq
    have hqκ : q < κ := (Ordinal.lt_mul_iff_div_lt hM0).1 hsub
    refine ⟨q, ktQ_lt hC (hC.part _ (hC.sub e he b) m) hqκ, ?_⟩
    have e1 : e = b + (e - b) := (Ordinal.add_sub_cancel_of_le h1).symm
    show e < b + ω ^ m * (q + 1)
    rw [e1]
    have := Ordinal.lt_mul_succ_div (e - b) hM0
    rw [Order.succ_eq_add_one] at this
    exact (add_lt_add_iff_left b).2 this

/-- **The gap passes to `b + ω^{L(x)}`.** -/
theorem ktG_opow (hC : KtCl C κ z) {b : Ordinal.{0}} {L : Ordinal.{0} → Ordinal.{0}} (hg : KgGap κ L C z) :
    KgGap κ (fun x => b + ω ^ L x) C z := by
  intro e he hlt
  rcases lt_or_ge e b with h1 | h1
  · exact ⟨0, hC.zSC.1, h1.trans_le le_self_add⟩
  · have hd : e - b < ω ^ L κ := Ry.rySub_lt h1 hlt
    have hdC : e - b ∈ C := hC.sub e he b
    have e1 : e = b + (e - b) := (Ordinal.add_sub_cancel_of_le h1).symm
    rcases eq_or_ne (e - b) 0 with h0 | h0
    · refine ⟨0, hC.zSC.1, ?_⟩
      show e < b + ω ^ L (0 + 1)
      rw [e1, h0, add_zero]
      exact lt_add_of_pos_right b (opow_pos _ omega0_pos)
    · have hlog : log ω (e - b) < L κ := (lt_opow_iff_log_lt one_lt_omega0 h0).1 hd
      obtain ⟨q, hq, hqe⟩ := hg _ (hC.log _ hdC) hlog
      refine ⟨q, hq, ?_⟩
      show e < b + ω ^ L (q + 1)
      rw [e1]
      exact (add_lt_add_iff_left b).2 ((lt_opow_iff_log_lt one_lt_omega0 h0).2 hqe)

/-- **The gap passes to `b + φ(d, L(x))`.** -/
theorem ktG_phiR (hC : KtCl C κ z) {b d : Ordinal.{0}} {L : Ordinal.{0} → Ordinal.{0}}
    (hg : KgGap κ L C z) : KgGap κ (fun x => b + veblen d (L x)) C z := by
  intro e he hlt
  rcases lt_or_ge e b with h1 | h1
  · exact ⟨0, hC.zSC.1, h1.trans_le le_self_add⟩
  · have hd : e - b < veblen d (L κ) := Ry.rySub_lt h1 hlt
    have hdC : e - b ∈ C := hC.sub e he b
    have e1 : e = b + (e - b) := (Ordinal.add_sub_cancel_of_le h1).symm
    rcases lt_or_ge (e - b) (veblen d 0) with h0 | h0
    · refine ⟨0, hC.zSC.1, ?_⟩
      show e < b + veblen d (L (0 + 1))
      rw [e1]
      exact (add_lt_add_iff_left b).2 (h0.trans_le ((veblen_le_veblen_iff_right).2 zero_le))
    · obtain ⟨u, huC, hu1, hu2⟩ := hC.idx d _ hdC h0
      have huL : u < L κ := (veblen_lt_veblen_iff_right).1 (hu1.trans_lt hd)
      obtain ⟨q, hq, hqu⟩ := hg u huC huL
      refine ⟨q, hq, ?_⟩
      show e < b + veblen d (L (q + 1))
      rw [e1]
      exact (add_lt_add_iff_left b).2 (hu2.trans_le ((veblen_le_veblen_iff_right).2
        (Order.add_one_le_of_lt hqu)))

/-- **THE GAP OF EVERY TOWER**, no hypothesis. -/
theorem ktG_KaT (hC : KtCl C κ z) : ∀ t : KaT, KgGap κ t.ev C z
  | KaT.base c m => ktG_mul hC c m
  | KaT.up _ t => ktG_opow hC (ktG_KaT hC t)

end Gap

end Googology.Trans.PoR.InaccPsi.R2.Kt

#print axioms Googology.Trans.PoR.InaccPsi.R2.Kt.ktIdx
#print axioms Googology.Trans.PoR.InaccPsi.R2.Kt.ktG_phiR
#print axioms Googology.Trans.PoR.InaccPsi.R2.Kt.ktG_KaT

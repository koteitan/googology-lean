import Googology.Trans.PoR.InaccPsi.R2.KfDec

/-!
# Kg: THE PLATEAU AT ANY LEVEL `κ` (`ψ_κ(G(κ)) = sup_n x_n`), and the OWNERSHIP of the contexts

For an inaccessible-range `κ` (here `κ = Ω₂`) and a monotone `G`, the iterates `x_{n+1} = ψ_κ(G(x_n))` (`kgX`) reach
`ψ_κ(G(κ))` once `G` has the gap at level `κ` at every stage `Cl(G(x_n), x_{n+1})` (`kgPlat`; `Yd.ydTopB_eq` is the case
`G(e) = β + W^{X+e}`).  The gap at level `κ` holds for every tower (`kgGap_mul`, `kgGap_opow`, `Ka.KaT.gapK`).

Over a base `β` the argument of the top law along a context is the tower `β + W^{F(v)} = β + ω^{Ω₂·F(v)}`, so:

* `kgOwnBase` (**THE OWNERSHIP OF THE COEFFICIENT CONTEXT** `v ↦ g₀ + W^j·v`: if the threshold of `j` lies below
  `ψ₂(β + W^{g₀ + W^j})`, every ordinal `u' < ψ₂(β + W^{g₀ + W^{j+1}})` has `u' < ψ₂(β + W^{g₀ + W^j·u'})`),
* `kgOwnExp` (**THE OWNERSHIP OF THE EXPONENT CONTEXT** `v ↦ X₀ + W^v`: every ordinal `u' < ψ₂(β + W^{X₀ + W^{Ω₂}})`
  has `u' < ψ₂(β + W^{X₀ + W^{u'}})`, no threshold).

These give the base conditions `Zy.ZyQ` (cumulative coefficient) and `Kc.KcE` (cumulative exponent) from the
inequalities `ζ, h < ψ₂(b)` of a normal base `b`.  No normality of `β` is used.

No new axiom.  New definitions: `KgGap` (the gap at level `κ`), `kgX` (the iterates).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kg

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Zx
  Googology.Trans.PoR.InaccPsi.R2.Ka
  Googology.Trans.PoR.InaccPsi.R2.Kb

variable {S : InaccSeq.{0}}

/-- **The gap of `L` at level `κ`** on `C` with bound `x`. -/
def KgGap (κ : Ordinal.{0}) (L : Ordinal.{0} → Ordinal.{0}) (C : Set Ordinal.{0}) (x : Ordinal.{0}) : Prop :=
  ∀ e ∈ C, e < L κ → ∃ q, q < x ∧ e < L (q + 1)

/-- **The gap of `b + ω^m·x` at level `κ`** at `Cl(a, ψ_κ a)` once `m` is a member. -/
theorem kgGap_mul {κ a b m : Ordinal.{0}} (hκ : S.InR κ) (hm : m ∈ S.CSet a (S.psi a κ)) :
    KgGap κ (fun x => b + ω ^ m * x) (S.CSet a (S.psi a κ)) (S.psi a κ) := by
  intro e he hlt
  have hM0 : ω ^ m ≠ 0 := (opow_pos _ omega0_pos).ne'
  rcases lt_or_ge e b with h1 | h1
  · refine ⟨0, (SC_psi hκ a).1, ?_⟩
    show e < b + ω ^ m * (0 + 1)
    rw [zero_add, mul_one]; exact h1.trans_le le_self_add
  · have hsub : e - b < ω ^ m * κ := Ry.rySub_lt h1 hlt
    set q := (e - b) / ω ^ m with hq
    have hqC : q ∈ S.CSet a (S.psi a κ) := (Vh.vhC_div _ (Ta.taSub_mem e he b) m).2.2 hm
    have hqκ : q < κ := (Ordinal.lt_mul_iff_div_lt hM0).1 hsub
    refine ⟨q, lt_psi_of_mem hκ hqC hqκ, ?_⟩
    have e1 : e = b + (e - b) := (Ordinal.add_sub_cancel_of_le h1).symm
    show e < b + ω ^ m * (q + 1)
    rw [e1]
    have := Ordinal.lt_mul_succ_div (e - b) hM0
    rw [Order.succ_eq_add_one] at this
    exact (add_lt_add_iff_left b).2 this

/-- **The gap at level `κ` passes to `b + ω^{L(x)}`.** -/
theorem kgGap_opow {κ a b : Ordinal.{0}} {L : Ordinal.{0} → Ordinal.{0}} (hκ : S.InR κ)
    (hg : KgGap κ L (S.CSet a (S.psi a κ)) (S.psi a κ)) :
    KgGap κ (fun x => b + ω ^ L x) (S.CSet a (S.psi a κ)) (S.psi a κ) := by
  intro e he hlt
  have hpos : (0 : Ordinal.{0}) < S.psi a κ := (SC_psi hκ a).1
  rcases lt_or_ge e b with h1 | h1
  · exact ⟨0, hpos, h1.trans_le le_self_add⟩
  · have hd : e - b < ω ^ L κ := Ry.rySub_lt h1 hlt
    have hdC : e - b ∈ S.CSet a (S.psi a κ) := Ta.taSub_mem e he b
    have e1 : e = b + (e - b) := (Ordinal.add_sub_cancel_of_le h1).symm
    rcases eq_or_ne (e - b) 0 with h0 | h0
    · refine ⟨0, hpos, ?_⟩
      show e < b + ω ^ L (0 + 1)
      rw [e1, h0, add_zero]
      exact lt_add_of_pos_right b (opow_pos _ omega0_pos)
    · have hlog : log ω (e - b) < L κ := (lt_opow_iff_log_lt one_lt_omega0 h0).1 hd
      obtain ⟨q, hq, hqe⟩ := hg _ (Le.leLog_mem hdC) hlog
      refine ⟨q, hq, ?_⟩
      show e < b + ω ^ L (q + 1)
      rw [e1]
      exact (add_lt_add_iff_left b).2 ((lt_opow_iff_log_lt one_lt_omega0 h0).2 hqe)

/-- **The gap of every tower at level `κ`** once its bottom exponent is a member. -/
theorem KaT.gapK {κ a : Ordinal.{0}} (hκ : S.InR κ) : ∀ t : KaT, t.bm ∈ S.CSet a (S.psi a κ) →
    KgGap κ t.ev (S.CSet a (S.psi a κ)) (S.psi a κ)
  | KaT.base c _, hm => kgGap_mul (b := c) hκ hm
  | KaT.up c t, hm => kgGap_opow (b := c) (L := t.ev) hκ (KaT.gapK hκ t hm)

/-- The iterates `x_0` (a start), `x_{n+1} = ψ_κ(G(x_n))`. -/
noncomputable def kgX (S : InaccSeq.{0}) (κ : Ordinal.{0}) (G : Ordinal.{0} → Ordinal.{0}) (x0 : Ordinal.{0}) :
    ℕ → Ordinal.{0}
  | 0 => x0
  | n + 1 => S.psi (G (kgX S κ G x0 n)) κ

section Plat

variable {κ x0 : Ordinal.{0}} {G : Ordinal.{0} → Ordinal.{0}}

theorem kgX_zero : kgX S κ G x0 0 = x0 := rfl

theorem kgX_succ (n : ℕ) : kgX S κ G x0 (n + 1) = S.psi (G (kgX S κ G x0 n)) κ := rfl

variable (hκ : S.InR κ) (hG : Monotone G) (h0 : x0 ≤ kgX S κ G x0 1) (hx0 : x0 < κ)
include hκ hG h0

theorem kgX_mono : ∀ n, kgX S κ G x0 n ≤ kgX S κ G x0 (n + 1)
  | 0 => h0
  | n + 1 => by
    rw [kgX_succ, kgX_succ (n + 1)]
    exact (psi_mono hκ (hG (kgX_mono n))).1

theorem kgStage_mono {i j : ℕ} (h : i ≤ j) :
    S.CSet (G (kgX S κ G x0 i)) (kgX S κ G x0 (i + 1)) ⊆ S.CSet (G (kgX S κ G x0 j)) (kgX S κ G x0 (j + 1)) := by
  have hmono : Monotone (kgX S κ G x0) := monotone_nat_of_le_succ (kgX_mono hκ hG h0)
  rw [kgX_succ, kgX_succ]
  exact (psi_mono hκ (hG (hmono h))).2

include hx0

/-- **Every member of `Cl(G(κ), sup_n x_n)` lies in a stage.** -/
theorem kgKey
    (hg : ∀ n, KgGap κ G (S.CSet (G (kgX S κ G x0 n)) (kgX S κ G x0 (n + 1))) (kgX S κ G x0 (n + 1))) :
    ∀ y ∈ S.CSet (G κ) (⨆ n : ℕ, kgX S κ G x0 n),
      ∃ n, y ∈ S.CSet (G (kgX S κ G x0 n)) (kgX S κ G x0 (n + 1)) := by
  have hlt : ∀ n, kgX S κ G x0 n < κ := fun n => by
    cases n with
    | zero => exact hx0
    | succ n => rw [kgX_succ]; exact psi_lt hκ _
  have hbdd : BddAbove (range (kgX S κ G x0)) := ⟨κ, by rintro _ ⟨n, rfl⟩; exact (hlt n).le⟩
  intro y hy
  induction hy with
  | small h =>
    obtain ⟨n, hn⟩ := (lt_ciSup_iff hbdd).1 h
    exact ⟨n, CSet.of_lt (hn.trans_le (kgX_mono hκ hG h0 n))⟩
  | zero => exact ⟨0, CSet.zero_mem _ _⟩
  | inacc n => exact ⟨0, Clos.inacc n⟩
  | inaccW => exact ⟨0, Clos.inaccW⟩
  | add _ _ ihp ihq =>
    obtain ⟨i, hi⟩ := ihp
    obtain ⟨j, hj⟩ := ihq
    exact ⟨max i j, CSet.add_mem (kgStage_mono hκ hG h0 (le_max_left i j) hi)
      (kgStage_mono hκ hG h0 (le_max_right i j) hj)⟩
  | phi _ _ ihp ihq =>
    obtain ⟨i, hi⟩ := ihp
    obtain ⟨j, hj⟩ := ihq
    exact ⟨max i j, Clos.phi (kgStage_mono hκ hG h0 (le_max_left i j) hi)
      (kgStage_mono hκ hG h0 (le_max_right i j) hj)⟩
  | om _ ih =>
    obtain ⟨i, hi⟩ := ih
    exact ⟨i, CSet.Om_mem hi⟩
  | @coll π e hπ _ _ ihπ ihe =>
    obtain ⟨i, hi⟩ := ihπ
    obtain ⟨k, hk⟩ := ihe
    obtain ⟨q, hq, hqe⟩ := hg k _ hk e.2
    have hmono : Monotone (kgX S κ G x0) := monotone_nat_of_le_succ (kgX_mono hκ hG h0)
    set N := max (k + 1) i with hN
    have hltN : e.1 < G (kgX S κ G x0 N) :=
      hqe.trans_le (hG ((Order.add_one_le_of_lt hq).trans (hmono (le_max_left (k + 1) i))))
    have heN := kgStage_mono (S := S) (κ := κ) (G := G) (x0 := x0) hκ hG h0
      ((Nat.le_succ k).trans (le_max_left (k + 1) i)) hk
    have hπN := kgStage_mono (S := S) (κ := κ) (G := G) (x0 := x0) hκ hG h0 (le_max_right (k + 1) i) hi
    exact ⟨N, Clos.coll (e := ⟨e.1, hltN⟩) hπ hπN heN⟩

/-- **THE PLATEAU AT LEVEL `κ`**: `ψ_κ(G(κ)) ≤ sup_n x_n`. -/
theorem kgPlat (hκC : ∀ a b : Ordinal.{0}, κ ∈ S.CSet a b)
    (hg : ∀ n, KgGap κ G (S.CSet (G (kgX S κ G x0 n)) (kgX S κ G x0 (n + 1))) (kgX S κ G x0 (n + 1))) :
    S.psi (G κ) κ ≤ ⨆ n : ℕ, kgX S κ G x0 n := by
  have hlt : ∀ n, kgX S κ G x0 n < κ := fun n => by
    cases n with
    | zero => exact hx0
    | succ n => rw [kgX_succ]; exact psi_lt hκ _
  have hbdd : BddAbove (range (kgX S κ G x0)) := ⟨κ, by rintro _ ⟨n, rfl⟩; exact (hlt n).le⟩
  refine psi_le_of_good (hκC _ _) fun y hy hyκ => ?_
  obtain ⟨n, hn⟩ := kgKey hκ hG h0 hx0 hg y hy
  rw [kgX_succ] at hn
  have h := lt_psi_of_mem hκ hn hyκ
  rw [← kgX_succ] at h
  exact h.trans_le (le_ciSup hbdd (n + 1))

end Plat

/-- `Ω₂·ω^y = ω^{Ω₂ + y}`. -/
theorem kg_Om2_mul_opow (y : Ordinal.{0}) : Om (1 + 1) * ω ^ y = ω ^ (Om (1 + 1) + y) := by
  rw [opow_add, gg_SC_eps ldOm2_SC]

/-- The base argument along the coefficient context is a tower: `β + W^{g₀ + W^j·v} =
`β + ω^{Ω₂·g₀ + ω^{Ω₂ + Ω₂·j}·v}`. -/
theorem kg_tower_base (β g₀ j v : Ordinal.{0}) :
    β + leWe (g₀ + leWe j * v) = (KaT.up β (KaT.base (Om (1 + 1) * g₀) (Om (1 + 1) + Om (1 + 1) * j))).ev v := by
  rw [KaT.ev_up, KaT.ev_base]
  unfold leWe
  rw [mul_add, ← mul_assoc, kg_Om2_mul_opow]

/-- The base argument along the exponent context is a tower: `β + W^{X₀ + W^v} =
`β + ω^{Ω₂·X₀ + ω^{Ω₂ + ω^{Ω₂}·v}}`. -/
theorem kg_tower_exp (β X₀ v : Ordinal.{0}) :
    β + leWe (X₀ + leWe v) =
      (KaT.up β (KaT.up (Om (1 + 1) * X₀) (KaT.base (Om (1 + 1)) (Om (1 + 1))))).ev v := by
  rw [KaT.ev_up, KaT.ev_up, KaT.ev_base]
  unfold leWe
  rw [mul_add, kg_Om2_mul_opow, gg_SC_eps ldOm2_SC]

/-- **THE OWNERSHIP OF THE COEFFICIENT CONTEXT `v ↦ g₀ + W^j·v`.** -/
theorem kgOwnBase {β g₀ j qj : Ordinal.{0}} (hjm : ∀ a c : Ordinal.{0}, Om 1 ≤ c → qj < c → j ∈ S.CSet a c)
    (hqj : qj < S.psi (β + leWe (g₀ + leWe j)) (Om (1 + 1))) :
    ∀ u', u' < S.psi (β + leWe (g₀ + leWe (j + 1))) (Om (1 + 1)) →
      u' < S.psi (β + leWe (g₀ + leWe j * u')) (Om (1 + 1)) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  set G : Ordinal.{0} → Ordinal.{0} := fun v => β + leWe (g₀ + leWe j * v) with hGdef
  set F : Ordinal.{0} → Ordinal.{0} := fun v => g₀ + leWe j * v with hFdef
  have hGmono : Monotone G := fun _ _ h =>
    add_le_add le_rfl (leWe_mono (add_le_add le_rfl (leMulWe_mono h)))
  have hFmono : Monotone F := fun _ _ h => add_le_add le_rfl (leMulWe_mono h)
  -- start the plateau at `v_1 = ψ₂(β + W^{g₀})`
  set x0 := S.psi (β + leWe g₀) (Om (1 + 1)) with hx0def
  have hx01 : (1 : Ordinal.{0}) ≤ x0 := Order.one_le_iff_pos.2 (SC_psi hκ2 _).1
  have hx0 : x0 < Om (1 + 1) := psi_lt hκ2 _
  have h0 : x0 ≤ kgX S (Om (1 + 1)) G x0 1 := by
    rw [kgX_succ, kgX_zero]
    exact (psi_mono hκ2 (add_le_add le_rfl (leWe_mono le_self_add))).1
  have hx1 : ∀ n, S.psi (β + leWe (g₀ + leWe j)) (Om (1 + 1)) ≤ kgX S (Om (1 + 1)) G x0 (n + 1) := fun n => by
    have hmono : Monotone (kgX S (Om (1 + 1)) G x0) := monotone_nat_of_le_succ (kgX_mono hκ2 hGmono h0)
    refine le_trans ?_ (hmono (Nat.le_add_left 1 n))
    rw [kgX_succ, kgX_zero]
    exact (psi_mono hκ2 (add_le_add le_rfl (leWe_mono (add_le_add le_rfl
      (Ordinal.le_mul_left _ (Order.one_le_iff_pos.1 hx01)))))).1
  have hplat := kgPlat (S := S) (κ := Om (1 + 1)) (G := G) (x0 := x0) hκ2 hGmono h0 hx0
    (fun a b => mxOm2_mem a b) (fun n => by
      have hfun : G = (KaT.up β (KaT.base (Om (1 + 1) * g₀) (Om (1 + 1) + Om (1 + 1) * j))).ev := by
        funext v; exact kg_tower_base β g₀ j v
      have hjn : j ∈ S.CSet (G (kgX S (Om (1 + 1)) G x0 n)) (kgX S (Om (1 + 1)) G x0 (n + 1)) :=
        hjm _ _ ((psiS_bounds (S := S) _ 1).1.le.trans_eq (by rw [kgX_succ])) (hqj.trans_le (hx1 n))
      have hbm : (KaT.up β (KaT.base (Om (1 + 1) * g₀) (Om (1 + 1) + Om (1 + 1) * j))).bm ∈
          S.CSet (G (kgX S (Om (1 + 1)) G x0 n)) (S.psi (G (kgX S (Om (1 + 1)) G x0 n)) (Om (1 + 1))) := by
        rw [← kgX_succ]
        exact CSet.add_mem (mxOm2_mem _ _) (ldMulK_mem ldOm2_SC (mxOm2_mem _ _) hjn)
      have h := KaT.gapK (S := S) hκ2 _ hbm
      rw [← hfun, ← kgX_succ] at h
      exact h)
  -- the iterates are those of `Kb.kbV`
  have hxeq : ∀ n, kgX S (Om (1 + 1)) G x0 n = kbV S β F (n + 1) := by
    intro n
    induction n with
    | zero => rw [kgX_zero, kbV_succ, kbV_zero]; show x0 = _; rw [hx0def]; simp only [hFdef, mul_zero, add_zero]
    | succ n ih => rw [kgX_succ, ih, kbV_succ (n + 1)]
  intro u' hu'
  have hlt : ∀ n, kgX S (Om (1 + 1)) G x0 n < Om (1 + 1) := fun n => by
    cases n with
    | zero => exact hx0
    | succ n => rw [kgX_succ]; exact psi_lt hκ2 _
  have hbdd : BddAbove (range (kgX S (Om (1 + 1)) G x0)) := ⟨Om (1 + 1), by rintro _ ⟨n, rfl⟩; exact (hlt n).le⟩
  have hGΩ : G (Om (1 + 1)) = β + leWe (g₀ + leWe (j + 1)) := by
    simp only [hGdef]; rw [leWe_succ]
  rw [← hGΩ] at hu'
  obtain ⟨n, hn⟩ := (lt_ciSup_iff hbdd).1 (hu'.trans_le hplat)
  rw [hxeq n] at hn
  exact kbV_own hFmono (n + 1) u' hn

/-- **THE OWNERSHIP OF THE EXPONENT CONTEXT `v ↦ X₀ + W^v`.** -/
theorem kgOwnExp {β X₀ : Ordinal.{0}} :
    ∀ u', u' < S.psi (β + leWe (X₀ + leWe (Om (1 + 1)))) (Om (1 + 1)) →
      u' < S.psi (β + leWe (X₀ + leWe u')) (Om (1 + 1)) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  set G : Ordinal.{0} → Ordinal.{0} := fun v => β + leWe (X₀ + leWe v) with hGdef
  set F : Ordinal.{0} → Ordinal.{0} := fun v => X₀ + leWe v with hFdef
  have hGmono : Monotone G := fun _ _ h => add_le_add le_rfl (leWe_mono (add_le_add le_rfl (leWe_mono h)))
  have hFmono : Monotone F := fun _ _ h => add_le_add le_rfl (leWe_mono h)
  have h0 : (0 : Ordinal.{0}) ≤ kgX S (Om (1 + 1)) G 0 1 := zero_le
  have hx0 : (0 : Ordinal.{0}) < Om (1 + 1) := ldOm2_SC.1
  have hfun : G = (KaT.up β (KaT.up (Om (1 + 1) * X₀) (KaT.base (Om (1 + 1)) (Om (1 + 1))))).ev := by
    funext v; exact kg_tower_exp β X₀ v
  have hplat := kgPlat (S := S) (κ := Om (1 + 1)) (G := G) (x0 := 0) hκ2 hGmono h0 hx0
    (fun a b => mxOm2_mem a b) (fun n => by
      have h := KaT.gapK (S := S) (a := G (kgX S (Om (1 + 1)) G 0 n)) hκ2
        (KaT.up β (KaT.up (Om (1 + 1) * X₀) (KaT.base (Om (1 + 1)) (Om (1 + 1))))) (mxOm2_mem _ _)
      rw [← hfun, ← kgX_succ] at h
      exact h)
  have hxeq : ∀ n, kgX S (Om (1 + 1)) G 0 n = kbV S β F n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [kgX_succ, ih, kbV_succ]
  intro u' hu'
  have hlt : ∀ n, kgX S (Om (1 + 1)) G 0 n < Om (1 + 1) := fun n => by
    cases n with
    | zero => exact hx0
    | succ n => rw [kgX_succ]; exact psi_lt hκ2 _
  have hbdd : BddAbove (range (kgX S (Om (1 + 1)) G 0)) := ⟨Om (1 + 1), by rintro _ ⟨n, rfl⟩; exact (hlt n).le⟩
  obtain ⟨n, hn⟩ := (lt_ciSup_iff hbdd).1 (hu'.trans_le hplat)
  rw [hxeq n] at hn
  exact kbV_own hFmono n u' hn

end Googology.Trans.PoR.InaccPsi.R2.Kg

#print axioms Googology.Trans.PoR.InaccPsi.R2.Kg.kgOwnBase
#print axioms Googology.Trans.PoR.InaccPsi.R2.Kg.kgOwnExp

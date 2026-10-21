import Googology.Trans.PoR.InaccPsi.R2.MxAtom
import Googology.Trans.PoR.InaccPsi.R2.LcCap

/-!
# The next collapse above a strongly critical bound: `ψ_{Ω₁}(A + D) ≤ β` from the values below

`ψ = S.psi`, `Cl = S.CSet` (Buchholz's hull with the constants of an `InaccSeq`), `θ = ψ_{Ω₂}(Ω_ω)`
(`ConjT.th`), `A_η = Ω_ω + θ·η`, `H(η) = P(η) = ψ_{Ω₁}(A_η)` (`Nm.Pv`), `G(ζ) = ψ_{Ω₂}(Ω_ω + θ₂·ζ)`
(`Lc.lcG`), `θ_k = ψ_{Ω_{k+1}}(Ω_ω)` (`Lc.lcTh`).

* `lsTail` (**the tail of a member**): `y + ε ∈ Cl(a, b)`, `ω^g ∣ y`, `ε < ω^g` give `ε ∈ Cl(a, b)`;
* `lsPsi_le_core` (**the minimality of `ψ` read at a strongly critical `β`**): if `β` is strongly critical,
  `ψ_{Ω₁}(A) < β`, and `ψ_{Ω₁}(e) < β` for every `e ∈ Cl(A + D, β) ∩ [A, A + D)`, then
  `ψ_{Ω₁}(A + D) ≤ β` (`InaccSeq.psi_le_of_good`: the countable members of `Cl(A + D, β)` are sums,
  Veblen values and `ψ_{Ω₁}`-values, so only the collapses with arguments in `[A, A + D)` need a check);
  `lsPsi_le` (all `ζ < D`), `lsPsi_le_mem` (only the `ζ ∈ Cl(A + D, β)`, when `ω^g ∣ A`, `D ≤ ω^g`);
* `lsMul_SC` (`x·G = G` for a strongly critical `G` and `0 < x < G`), `lsG_SC`, `lsTh_lt_G`
  (`θ < G(ζ)` for `ζ ≠ 0`), `lsH_eq` (**`H(η + G) = ψ_{Ω₁}(A_η + G)`** when `θ·G = G`), `lsH_G`
  (**`H(η + G(θ_k·ω²)) = ψ_{Ω₁}(A_η + G(θ_k·ω²))`**).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ls

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **The tail of a member**: `y + ε ∈ Cl(a, b)`, `ω^g ∣ y`, `ε < ω^g` give `ε ∈ Cl(a, b)`. -/
theorem lsTail {a b g : Ordinal.{0}} (x : Ordinal.{0}) : x ∈ S.CSet a b → ∀ y ε : Ordinal.{0},
    ω ^ g ∣ y → ε < ω ^ g → x = y + ε → ε ∈ S.CSet a b := by
  induction x using WellFoundedLT.induction with
  | _ x ih =>
  intro hx y ε hy hε e
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [zero_add] at e; rw [← e]; exact hx
  rcases eq_or_ne ε 0 with rfl | hε0
  · exact CSet.zero_mem a b
  have hgy : ω ^ g ≤ y := Ordinal.le_of_dvd hy0 hy
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hy0 (le_antisymm (e ▸ le_self_add) zero_le)
  rcases lead_tail_add hy0 hε0 with habs | ⟨-, ht⟩
  · exfalso
    have h1 : y ≤ ε := by
      calc y ≤ y + ε := le_self_add
        _ = ε := habs
    exact absurd (hε.trans_le hgy) (not_lt.2 h1)
  have htx : tail x ∈ S.CSet a b := (lead_tail_mem hx hx0).2
  have hlog : g ≤ Ordinal.log ω y := Ordinal.le_log_of_opow_le Ordinal.one_lt_omega0 hgy
  have hdl : ω ^ g ∣ lead y := opow_dvd_opow ω hlog
  have hdt : ω ^ g ∣ tail y := by
    have h2 := lead_add_tail hy0
    rw [← h2] at hy
    exact (dvd_add_iff hdl).1 hy
  have hte : tail x = tail y + ε := by rw [e]; exact ht
  exact ih (tail x) (tail_lt hx0) htx (tail y) ε hdt hε hte

theorem lsOm1_lt_I (n : ℕ) : Om (1 : Ordinal.{0}) < S.I n :=
  (Om_lt_Om.2 (lt_add_one (1 : Ordinal.{0}))).trans (Mx.mxOm2_lt_I n)

theorem lsOm1_lt_Iw : Om (1 : Ordinal.{0}) < S.Iw :=
  (Om_lt_Om.2 (lt_add_one (1 : Ordinal.{0}))).trans Mx.mxOm2_lt_Iw

/-- **The minimality of `ψ_{Ω₁}` read at a strongly critical `β`.** -/
theorem lsPsi_le_core {A D β : Ordinal.{0}} (hβ : SC β) (hρ : S.psi A (Om 1) < β)
    (h : ∀ e ∈ S.CSet (A + D) β, A ≤ e → e < A + D → S.psi e (Om 1) < β) :
    S.psi (A + D) (Om 1) ≤ β := by
  refine psi_le_of_good (CSet.Om_mem (CSet.one_mem _ _)) ?_
  intro x hx
  induction hx with
  | small h' => exact fun _ => h'
  | zero => exact fun _ => hβ.1
  | inacc n => exact fun h1 => absurd (h1.trans (lsOm1_lt_I n)) (lt_irrefl _)
  | inaccW => exact fun h1 => absurd (h1.trans lsOm1_lt_Iw) (lt_irrefl _)
  | @add x y _ _ ihx ihy =>
    intro h1
    exact hβ.isPrincipal (ihx (lt_of_le_of_lt le_self_add h1)) (ihy (lt_of_le_of_lt le_add_self h1))
  | @phi x y _ _ ihx ihy =>
    intro h1
    exact hβ.2 _ (ihx (lt_of_le_of_lt (left_le_veblen x y) h1)) _
      (ihy (lt_of_le_of_lt (right_le_veblen x y) h1))
  | @om x _ _ =>
    intro h1
    have hx1 : x < 1 := Om_lt_Om.1 h1
    rw [Order.lt_one_iff] at hx1
    rw [hx1, Om_zero]; exact hβ.1
  | @coll π e hπ _ he1 _ _ =>
    intro h1
    rcases hπ with ⟨n, rfl⟩ | ⟨s, rfl⟩
    · exact absurd ((Om_one_lt_psiI (S := S) e.1 n).trans h1) (lt_irrefl _)
    rcases eq_or_ne s 0 with rfl | hs0
    · rw [zero_add] at h1 ⊢
      rcases lt_or_ge e.1 A with heA | heA
      · exact ((psi_mono (S := S) Low.InR_Om_one heA.le).1).trans_lt hρ
      · exact h e.1 he1 heA e.2
    · exfalso
      have h2 : Om (1 : Ordinal.{0}) ≤ Om s := Om_le_Om.2 (Order.one_le_iff_ne_zero.2 hs0)
      exact absurd ((h2.trans_lt (psiS_bounds (S := S) e.1 s).1).trans h1) (lt_irrefl _)

/-- **`ψ_{Ω₁}(A + D) ≤ β`** for a strongly critical `β` above `ψ_{Ω₁}(A)` and every `ψ_{Ω₁}(A + ζ)`,
`ζ < D`. -/
theorem lsPsi_le {A D β : Ordinal.{0}} (hβ : SC β) (hρ : S.psi A (Om 1) < β)
    (h : ∀ ζ < D, S.psi (A + ζ) (Om 1) < β) : S.psi (A + D) (Om 1) ≤ β := by
  refine lsPsi_le_core hβ hρ fun e _ heA heD => ?_
  have e1 : A + (e - A) = e := Ordinal.add_sub_cancel_of_le heA
  have hz : e - A < D := by
    rw [← e1] at heD; exact (add_lt_add_iff_left A).1 heD
  rw [← e1]; exact h _ hz

/-- **`ψ_{Ω₁}(A + D) ≤ β`**, asking only at the `ζ ∈ Cl(A + D, β)` (when `ω^g ∣ A` and `D ≤ ω^g`). -/
theorem lsPsi_le_mem {A D β g : Ordinal.{0}} (hβ : SC β) (hρ : S.psi A (Om 1) < β)
    (hg : ω ^ g ∣ A) (hD : D ≤ ω ^ g)
    (h : ∀ ζ ∈ S.CSet (A + D) β, ζ < D → S.psi (A + ζ) (Om 1) < β) : S.psi (A + D) (Om 1) ≤ β := by
  refine lsPsi_le_core hβ hρ fun e he heA heD => ?_
  have e1 : A + (e - A) = e := Ordinal.add_sub_cancel_of_le heA
  have hz : e - A < D := by
    rw [← e1] at heD; exact (add_lt_add_iff_left A).1 heD
  have hmem : e - A ∈ S.CSet (A + D) β := lsTail e he A (e - A) hg (hz.trans_le hD) e1.symm
  rw [← e1]; exact h _ hmem hz

/-! ## `H(η + G) = ψ_{Ω₁}(A_η + G)` -/

/-- `x·G = G` for a strongly critical `G` and `0 < x < G`. -/
theorem lsMul_SC {G x : Ordinal.{0}} (hG : SC G) (hx0 : 0 < x) (hx : x < G) : x * G = G := by
  have hGo : ω ^ G = G := by
    have := hG.veblen_right hG.1; rwa [veblen_zero_apply] at this
  refine le_antisymm ?_ (Ordinal.le_mul_right G hx0)
  have hlog : Ordinal.log ω x + 1 < G := by
    have h1 : Ordinal.log ω x ≤ x := Ordinal.log_le_self ω x
    exact hG.add_one_lt (h1.trans_lt hx)
  calc x * G ≤ ω ^ (Ordinal.log ω x + 1) * G :=
        mul_le_mul_of_nonneg_right (lt_opow_log_add_one x).le zero_le
    _ = ω ^ (Ordinal.log ω x + 1) * ω ^ G := by rw [hGo]
    _ = ω ^ (Ordinal.log ω x + 1 + G) := (opow_add _ _ _).symm
    _ = ω ^ G := by
        rw [Ordinal.add_of_omega0_opow_le (by rwa [hGo]) (by rw [hGo])]
    _ = G := hGo

theorem lsG_SC (ζ : Ordinal.{0}) : SC (Lc.lcG S ζ) := SC_psi (InR_Om_succ 1) _

theorem lsTh_pos (k : ℕ) : 0 < Lc.lcTh S k := (SC_psi (InR_Om_succ _) _).1

/-- `θ < G(ζ)` for `ζ ≠ 0`. -/
theorem lsTh_lt_G {ζ : Ordinal.{0}} (hζ : ζ ≠ 0) : ConjT.th S < Lc.lcG S ζ := by
  have h1 : Om ω < Om ω + Lc.lcTh S 2 * ζ :=
    lt_add_of_pos_right _ (mul_pos (lsTh_pos 2) (pos_iff_ne_zero.2 hζ))
  exact psi_lt_psi (InR_Om_succ 1) h1 (ConjT.OmW_mem S _ _)

/-- **`H(η + G) = ψ_{Ω₁}(A_η + G)`** when `θ·G = G`. -/
theorem lsH_eq {η G : Ordinal.{0}} (h : ConjT.th S * G = G) :
    Nm.Pv S (η + G) = S.psi (ConjT.Aη S η + G) (Om 1) := by
  unfold Nm.Pv ConjT.Aη
  rw [mul_add, h, add_assoc]

theorem lsThG_eq {ζ : Ordinal.{0}} (hζ : ζ ≠ 0) : ConjT.th S * Lc.lcG S ζ = Lc.lcG S ζ :=
  lsMul_SC (lsG_SC ζ) (SC_psi (InR_Om_succ 1) _).1 (lsTh_lt_G hζ)

theorem lsThw_ne (k : ℕ) : Lc.lcTh S k * ω ^ 2 ≠ 0 :=
  (mul_pos (lsTh_pos k) (pow_pos omega0_pos 2)).ne'

/-- **`H(η + G(θ_k·ω²)) = ψ_{Ω₁}(A_η + G(θ_k·ω²))`.** -/
theorem lsH_G (η : Ordinal.{0}) (k : ℕ) :
    Nm.Pv S (η + Lc.lcG S (Lc.lcTh S k * ω ^ 2)) =
      S.psi (ConjT.Aη S η + Lc.lcG S (Lc.lcTh S k * ω ^ 2)) (Om 1) :=
  lsH_eq (lsThG_eq (lsThw_ne k))

end Googology.Trans.PoR.InaccPsi.R2.Ls

import Googology.Trans.PoR.InaccPsi.R2.GjImg
import Googology.Trans.PoR.InaccPsi.R2.LhEx

/-!
# TERMS WITH THE PSEUDO-BASES `ε_{x+t}`: values, Lemma EXACT

The terms `GkT` have constants, the base `x`, sums, `ω^t` and the new atom `ε_{x+t}` (`evA x t`, the `t`-th
`ε`-number from `x` on, `t` itself a term).  Every term with constants below an `ε`-number `y` has its value below
`evZ y`, the least `ε`-fixed point above `y` (`gkT_lt_evZ`), and Lemma EXACT holds for every term by one induction on
the term (`gkT_pi`: `π_{σ,ρ}(t(ρ)) = t(σ)` for `υ`-points `σ < ρ` and constants below `σ`; the new atom through
`pi_evAZ`).

* `GkT`, `GkT.ev`, `GkT.cs`, `GkT.CB`, `gkT_lt_evZ`, `gkT_lt_Om1`, `gkT_pi`, `gkT_ex` (Lemma EXACT as `GjEx`);
* arithmetic helpers `gk_dvd_next` (`g < γ`, `ω^w ∣ γ` give `g + ω^w ≤ γ`), `gk_lh_evA` (the `R₁⁺`-reach
  `lh(ε_{τ+c}) = ε_{τ+c}·2 + logend(c)` for every `1 ≤ c < evZ τ`, finite `c` included).

No new axiom.  New definitions: `GkT`, `GkT.ev`, `GkT.cs`, `GkT.CB`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gk

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gd Googology.Trans.PoR.InaccPsi.R2.Gj

/-- **The terms**: constants, the base `x`, sums, `ω^t`, and the pseudo-base atom `ε_{x+t}`. -/
inductive GkT : Type 1
  | k : Ordinal.{0} → GkT
  | x : GkT
  | add : GkT → GkT → GkT
  | opow : GkT → GkT
  | ea : GkT → GkT

namespace GkT

/-- The value at the base `y`. -/
noncomputable def ev : GkT → Ordinal.{0} → Ordinal.{0}
  | k a, _ => a
  | x, y => y
  | add t u, y => ev t y + ev u y
  | opow t, y => ω ^ ev t y
  | ea t, y => evA y (ev t y)

/-- The constants. -/
def cs : GkT → List Ordinal.{0}
  | k a => [a]
  | x => []
  | add t u => cs t ++ cs u
  | opow t => cs t
  | ea t => cs t

/-- All constants below `s`. -/
def CB (t : GkT) (s : Ordinal.{0}) : Prop := ∀ c ∈ cs t, c < s

@[simp] theorem ev_k (a y : Ordinal.{0}) : ev (k a) y = a := rfl
@[simp] theorem ev_x (y : Ordinal.{0}) : ev x y = y := rfl
@[simp] theorem ev_add (t u : GkT) (y : Ordinal.{0}) : ev (add t u) y = ev t y + ev u y := rfl
@[simp] theorem ev_opow (t : GkT) (y : Ordinal.{0}) : ev (opow t) y = ω ^ ev t y := rfl
@[simp] theorem ev_ea (t : GkT) (y : Ordinal.{0}) : ev (ea t) y = evA y (ev t y) := rfl

@[simp] theorem cs_k (a : Ordinal.{0}) : cs (k a) = [a] := rfl
@[simp] theorem cs_x : cs x = [] := rfl
@[simp] theorem cs_add (t u : GkT) : cs (add t u) = cs t ++ cs u := rfl
@[simp] theorem cs_opow (t : GkT) : cs (opow t) = cs t := rfl
@[simp] theorem cs_ea (t : GkT) : cs (ea t) = cs t := rfl

theorem CB_add {t u : GkT} {s : Ordinal.{0}} : CB (add t u) s ↔ CB t s ∧ CB u s := by
  simp only [CB, cs, List.mem_append]
  constructor
  · intro h; exact ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩
  · rintro ⟨h1, h2⟩ c (hc | hc)
    · exact h1 c hc
    · exact h2 c hc

theorem CB_mono {t : GkT} {s s' : Ordinal.{0}} (h : CB t s) (hs : s ≤ s') : CB t s' :=
  fun c hc => (h c hc).trans_le hs

end GkT

open GkT

/-- **Every value is below the next `ε`-fixed point**: constants below the `ε`-number `y` give `t(y) < evZ y`. -/
theorem gkT_lt_evZ {y : Ordinal.{0}} (hy : InE y) : ∀ t : GkT, CB t y → ev t y < evZ y
  | GkT.k a, h => (h a (by simp)).trans (lt_evZ y)
  | GkT.x, _ => lt_evZ y
  | GkT.add t u, h => (inE_indec (evZ_E y)).add_lt (gkT_lt_evZ hy t (CB_add.1 h).1)
      (gkT_lt_evZ hy u (CB_add.1 h).2)
  | GkT.opow t, h => (evZ_E y).opow_lt (gkT_lt_evZ hy t h)
  | GkT.ea t, h => evA_lt_evZ hy (gkT_lt_evZ hy t h)

theorem gkT_lt_Om1 {y : Ordinal.{0}} (hy : InE y) (hy1 : y < Om1) (t : GkT) (h : CB t y) : ev t y < Om1 :=
  (gkT_lt_evZ hy t h).trans (evZ_lt_Om1 hy hy1)

/-- **LEMMA EXACT FOR EVERY TERM, by one induction on the term**: for `υ`-points `σ < ρ` (bases) and constants below
`σ`, `t(ρ) ∈ Tᵖ[σ]` and `π_{σ,ρ}(t(ρ)) = t(σ)`; the atom `ε_{x+t}` by `pi_evAZ`. -/
theorem gkT_pi {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) :
    ∀ t : GkT, CB t σ → ev t ρ ∈ TB ρ σ ∧ pi σ ρ (ev t ρ) = ev t σ
  | GkT.k a, h => by
    have ha : a < σ := h a (by simp)
    exact ⟨mem_TB_of_lt hB ha, pi_lt hB ha⟩
  | GkT.x, _ => pi_base hB
  | GkT.add t u, h => by
    obtain ⟨h1, h2⟩ := gkT_pi hσ hρ hB t (CB_add.1 h).1
    obtain ⟨h3, h4⟩ := gkT_pi hσ hρ hB u (CB_add.1 h).2
    obtain ⟨h5, h6⟩ := pi_add hB h1 h3
    exact ⟨h5, by rw [ev_add, h6, h2, h4, ev_add]⟩
  | GkT.opow t, h => by
    obtain ⟨h1, h2⟩ := gkT_pi hσ hρ hB t h
    have hlt : ev t ρ < Om1 := gkT_lt_Om1 hB.2.1 hB.2.2.2 t (CB_mono h hB.2.2.1.le)
    obtain ⟨h3, h4⟩ := pi_opowZ hσ hρ hB h1 hlt
    exact ⟨h3, by rw [ev_opow, h4, h2, ev_opow]⟩
  | GkT.ea t, h => by
    obtain ⟨h1, h2⟩ := gkT_pi hσ hρ hB t h
    have hZρ : ev t ρ < evZ ρ := gkT_lt_evZ hB.2.1 t (CB_mono h hB.2.2.1.le)
    have hZσ : pi σ ρ (ev t ρ) < evZ σ := by rw [h2]; exact gkT_lt_evZ hB.1 t h
    obtain ⟨h3, h4⟩ := pi_evAZ hB h1 hZρ hZσ
    exact ⟨h3, by rw [ev_ea, h4, h2, ev_ea]⟩

/-- **Lemma EXACT for a term as a function** (`GjEx` with the constants of the term). -/
theorem gkT_ex (g : Ordinal.{0}) (t : GkT) : GjEx g (cs t).toFinset (ev t) := fun σ ρ hσ hρ hB _ hC =>
  gkT_pi hσ hρ hB t (fun c hc => hC c (List.mem_toFinset.2 hc))

/-! ## Arithmetic and `R₁⁺` helpers -/

/-- `g < γ` and `ω^w ∣ γ` give `g + ω^w ≤ γ` (no divisibility of `g` needed). -/
theorem gk_dvd_next {w g γ : Ordinal.{0}} (hd : ω ^ w ∣ γ) (hgγ : g < γ) : g + ω ^ w ≤ γ := by
  obtain ⟨p, rfl⟩ := hd
  have hb : 0 < ω ^ w := opow_pos w omega0_pos
  have hq : g / ω ^ w < p := by
    by_contra hc
    push Not at hc
    have : ω ^ w * p ≤ g := (mul_le_mul_right hc _).trans (mul_div_le g (ω ^ w))
    exact absurd hgγ (not_lt.2 this)
  have hr : g % ω ^ w < ω ^ w := mod_lt g hb.ne'
  calc g + ω ^ w = ω ^ w * (g / ω ^ w) + (g % ω ^ w + ω ^ w) := by rw [← add_assoc, div_add_mod]
    _ = ω ^ w * (g / ω ^ w) + ω ^ w := by rw [add_omega0_opow hr]
    _ = ω ^ w * (g / ω ^ w + 1) := by rw [mul_add_one]
    _ ≤ ω ^ w * p := mul_le_mul_right (add_one_le_of_lt hq) _

/-- **The `R₁⁺`-reach of `ε_{τ+c}` for every `1 ≤ c < evZ τ`**: `ε_{τ+c}·2 + logend(c)` (`lh_evAZ` for `c ≥ ω`,
`Lh.lhT_eK` with [W07b] Theorem 5.3 (`lh_eq_lhT`) for finite `c`, where `logend(c) = 0`). -/
theorem gk_lh_evA {τ c : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hc0 : c ≠ 0) (hc : c < evZ τ) :
    IsLh1 (evA τ c) (evA τ c * 2 + lg c) := by
  rcases lt_or_ge c ω with hcω | hωc
  · obtain ⟨n, rfl⟩ := lt_omega0.1 hcω
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 1 := Nat.exists_eq_succ_of_ne_zero (by exact_mod_cast hc0)
    have hlg : lg ((k + 1 : ℕ) : Ordinal.{0}) = 0 := lg_nat (Nat.succ_ne_zero k)
    rw [hlg, add_zero, evA_eK hτ]
    have hT := (eK_T hτ hτ1 k).1
    have h1 : τ < eK (k + 1) τ := eK_lt (Nat.succ_pos k) τ
    have h2 : eK (k + 1) τ < Om1 := eK_lt_Om1 hτ1 _
    have h := lh_eq_lhT (Or.inr hτ) hτ1 hT h1 h2 (inE_indec (eK_E_succ k τ))
    rwa [Lh.lhT_eK hτ hτ1 k] at h
  · exact lh_evAZ hτ hτ1 hωc hc

end Googology.Trans.PoR.InaccPsi.R2.Gk

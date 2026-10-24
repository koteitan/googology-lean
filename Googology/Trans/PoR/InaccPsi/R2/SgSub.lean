import Googology.Trans.PoR.InaccPsi.R2.ScNat

/-!
# Subtraction in the closures, and the prefix shape without a divisibility condition

`W^E = Ω₂^E`, `Ω^x = Ω₁^x`.

* `sgSub_mem` (**`Cl(a, b)` is closed under `x ↦ x - y`** for `y ∈ Cl(a, b)`, `y ≤ x`: by the Cantor normal
  form, with `log`, `mod` and finite multiples);
* `sgShp_preG` (**the prefix `ζ ↦ E₀ + g ζ` of a shape for EVERY constant `E₀` own above the bottom**: the
  divisibility `g* ∣ E₀` and the form `g* = ω^k` of `Sc.scShp_pre` are not needed; the index of `E₀ + g` comes from
  the index of `g` at `c - E₀`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sg

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc

variable {S : InaccSeq.{0}}

theorem sgOpowNat_mem {a b α : Ordinal.{0}} (hα : α ∈ S.CSet a b) :
    ∀ k : ℕ, ω ^ α * ((k : ℕ) : Ordinal.{0}) ∈ S.CSet a b
  | 0 => by rw [Nat.cast_zero, mul_zero]; exact CSet.zero_mem a b
  | k + 1 => by
    rw [Nat.cast_succ, mul_add_one]
    have h := CSet.phi_mem (S := S) (CSet.zero_mem a b) hα
    rw [veblen_zero_apply] at h
    exact CSet.add_mem (sgOpowNat_mem hα k) h

/-- **`Cl(a, b)` is closed under subtraction.** -/
theorem sgSub_mem {a b : Ordinal.{0}} : ∀ x, x ∈ S.CSet a b → ∀ y, y ∈ S.CSet a b → y ≤ x →
    x - y ∈ S.CSet a b := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx y hy hyx
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [Ordinal.sub_zero]; exact hx
  set α := log ω y with hα
  have hyl : ω ^ α ≤ y := opow_log_le_self ω hy0
  have hyu : y < ω ^ (α + 1) := by
    have := lt_opow_succ_log_self one_lt_omega0 y; rwa [Order.succ_eq_add_one] at this
  have hP : ω ^ α ≠ 0 := (opow_pos α omega0_pos).ne'
  rcases lt_or_ge x (ω ^ (α + 1)) with hxu | hxu
  · -- `x = ω^α·n + x_lo`, `y = ω^α·m + y_lo`
    have hxl : ω ^ α ≤ x := hyl.trans hyx
    have hαC : α ∈ S.CSet a b := leLog_mem hy
    have hn : x / ω ^ α < ω := by
      apply (Ordinal.lt_mul_iff_div_lt hP).1; rw [← opow_succ, Order.succ_eq_add_one]; exact hxu
    have hm : y / ω ^ α < ω := by
      apply (Ordinal.lt_mul_iff_div_lt hP).1; rw [← opow_succ, Order.succ_eq_add_one]; exact hyu
    obtain ⟨n, hn'⟩ := Ordinal.lt_omega0.1 hn
    obtain ⟨m, hm'⟩ := Ordinal.lt_omega0.1 hm
    have ex : x = ω ^ α * (n : Ordinal.{0}) + x % ω ^ α := by rw [← hn']; exact (Ordinal.div_add_mod x _).symm
    have ey : y = ω ^ α * (m : Ordinal.{0}) + y % ω ^ α := by rw [← hm']; exact (Ordinal.div_add_mod y _).symm
    have hxlC : x % ω ^ α ∈ S.CSet a b := leModP_mem α hx
    have hylC : y % ω ^ α ∈ S.CSet a b := leModP_mem α hy
    have hxlt : x % ω ^ α < ω ^ α := Ordinal.mod_lt x hP
    have hylt : y % ω ^ α < ω ^ α := Ordinal.mod_lt y hP
    have hxlx : x % ω ^ α < x := hxlt.trans_le hxl
    generalize x % ω ^ α = xl at ex hxlC hxlt hxlx
    generalize y % ω ^ α = yl at ey hylC hylt
    have hmn : m ≤ n := by
      by_contra h
      push Not at h
      have : ω ^ α * (n : Ordinal.{0}) + ω ^ α ≤ y := by
        rw [ey, ← mul_add_one]
        exact (mul_le_mul_right (by exact_mod_cast Nat.succ_le_of_lt h) _).trans le_self_add
      have hx2 : x < ω ^ α * (n : Ordinal.{0}) + ω ^ α := by
        rw [ex]; exact (add_lt_add_iff_left _).2 hxlt
      exact absurd (hyx.trans_lt (hx2.trans_le this)) (lt_irrefl _)
    rcases hmn.lt_or_eq with hlt | heq
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
      have hab : yl + ω ^ α * ((k + 1 : ℕ) : Ordinal.{0}) = ω ^ α * ((k + 1 : ℕ) : Ordinal.{0}) :=
        Ordinal.add_of_omega0_opow_le hylt
          (Ordinal.le_mul_left (ω ^ α) (by exact_mod_cast Nat.succ_pos k))
      have e : x - y = ω ^ α * ((k + 1 : ℕ) : Ordinal.{0}) + xl := by
        apply Ordinal.sub_eq_of_add_eq
        rw [ex, ey, add_assoc, ← add_assoc yl, hab, ← add_assoc, ← mul_add]
        congr 2
        push_cast; rw [add_assoc]
      rw [e]
      exact CSet.add_mem (sgOpowNat_mem hαC _) hxlC
    · subst heq
      have hle : yl ≤ xl := by
        by_contra h
        push Not at h
        have : x < y := by rw [ex, ey]; exact (add_lt_add_iff_left _).2 h
        exact absurd (hyx.trans_lt this) (lt_irrefl _)
      have e : x - y = xl - yl := by
        apply Ordinal.sub_eq_of_add_eq
        rw [ex, ey, add_assoc, Ordinal.add_sub_cancel_of_le hle]
      rw [e]
      exact IH _ hxlx hxlC _ hylC hle
  · -- absorption: `y + x = x`
    have hdiv0 : x / ω ^ (α + 1) ≠ 0 := by
      exact ((Ordinal.div_pos (opow_pos _ omega0_pos).ne').2 hxu).ne'
    have habs : y + x = x := by
      conv_lhs => rw [← Ordinal.div_add_mod x (ω ^ (α + 1))]
      rw [← add_assoc, Ordinal.add_of_omega0_opow_le hyu (Ordinal.le_mul_left _ (pos_iff_ne_zero.2 hdiv0)),
        Ordinal.div_add_mod]
    rw [Ordinal.sub_eq_of_add_eq habs]; exact hx

section Pre

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  {g gh : Ordinal.{0} → Ordinal.{0}} {gs ghs E0 Eh0 bot both : Ordinal.{0}}

include hl hX in
/-- **The prefix `ζ ↦ E₀ + g ζ` for every constant `E₀`** own above the bottom (no divisibility). -/
theorem sgShp_preG (h : ScShp S l g gh gs ghs bot both) (hE0H : E0 ∈ cdHull S l)
    (hE0m : E0 ∈ S.CSet 0 bot) (hEh0m : Eh0 ∈ S.CSet 0 both)
    (hE0cl : ∀ Q, SC Q → bot ≤ Q → LeCl (Om (1 + 1)) Q E0) (hEh0cl : ∀ Q, SC Q → both ≤ Q → LeCl (Om 1) Q Eh0) :
    ScShp S l (fun z => E0 + g z) (fun v => Eh0 + gh v) (E0 + gs) (Eh0 + ghs) bot both := by
  refine ⟨fun a b hab => (add_lt_add_iff_left E0).2 (h.st hab),
    fun ζ hζ => (add_lt_add_iff_left E0).2 (h.lt ζ hζ), fun v hv => (add_lt_add_iff_left Eh0).2 (h.lth v hv),
    h.inf.trans le_add_self, h.infh.trans le_add_self,
    fun ζ hζ hζW => CSet.add_mem hE0H (h.hull ζ hζ hζW), CSet.add_mem hE0H h.hullS,
    fun x c hx hc => CSet.add_mem (CSet_mono le_rfl hc hE0m) (h.mem x c hx hc),
    fun v c hv hc => CSet.add_mem (CSet_mono le_rfl hc hEh0m) (h.memh v c hv hc),
    fun Q hQ hc => scShCl_pre hQ (hE0cl Q hQ hc) (h.cl Q hQ hc),
    fun Q hQ hc => scImCl_pre hQ (hEh0cl Q hQ hc) (h.clh Q hQ hc), ?_,
    fun Q hQ hc ζ hζ => LeCl.add (hE0cl Q hQ hc) (h.clm Q hQ hc ζ hζ),
    fun Q hQ hc v hv => LeCl.add (hEh0cl Q hQ hc) (h.clmh Q hQ hc v hv),
    fun a b hab => (add_lt_add_iff_left Eh0).2 (h.sth hab), fun v hv u hu => ?_,
    fun c hc => CSet.add_mem (CSet_mono le_rfl hc hE0m) (h.memS c hc),
    fun c hc => CSet.add_mem (CSet_mono le_rfl hc hEh0m) (h.memhS c hc),
    fun Q hQ hc => LeCl.add (hE0cl Q hQ hc) (h.clS Q hQ hc), fun Q hQ hc => LeCl.add (hEh0cl Q hQ hc) (h.clhS Q hQ hc)⟩
  swap
  · rcases lt_or_ge u Eh0 with h1 | h1
    · exact ⟨0, pos_iff_ne_zero.2 hv.ne_bot, h1.trans_le le_self_add⟩
    obtain ⟨u', rfl⟩ := exists_add_of_le h1
    obtain ⟨v', hv', hu'⟩ := h.cont v hv u' ((add_lt_add_iff_left Eh0).1 hu)
    exact ⟨v', hv', (add_lt_add_iff_left Eh0).2 hu'⟩
  intro c hcH hc
  rcases lt_or_ge c E0 with h1 | h1
  · exact ⟨0, GxCl.zero (leRho hl hX).1.1, ldOm2_SC.1, h1.trans_le le_self_add, fun h0 => absurd rfl h0⟩
  obtain ⟨c', rfl⟩ := exists_add_of_le h1
  have hc' : c' < gs := (add_lt_add_iff_left E0).1 hc
  have hc'H : c' ∈ cdHull S l := by
    have h2 := sgSub_mem _ hcH _ hE0H h1
    rwa [Ordinal.add_sub_cancel] at h2
  obtain ⟨q, hq, hqW, hcq, hgq⟩ := h.idx c' hc'H hc'
  exact ⟨q, hq, hqW, (add_lt_add_iff_left E0).2 hcq, fun h0 => (add_le_add_iff_left E0).2 (hgq h0)⟩

end Pre

end Googology.Trans.PoR.InaccPsi.R2.Sg

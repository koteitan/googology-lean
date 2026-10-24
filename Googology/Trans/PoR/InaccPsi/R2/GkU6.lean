import Googology.Trans.PoR.InaccPsi.R2.GkU5

/-!
# CODES BELOW `ζ_{Ω₁+1}`: gates of codes over `Z`, hulls, the code system

* `gu_code_gate` (**a code `c < ζ_{Ω₁+1}` in the closure of `Z` and atoms above `ζ_{Ω₁+1}` has its gate below `Z`**:
  sums by `gu_add`, `ω^y` by `gu_opow_gate`, `φ(1, Ω₁+ν) = ε_{Ω₁+ν}` has the gate of `ν` (`gtc_le_Om1_add` when
  `ν < Ω₁·ω`), and `φ(x, y)` with `x ≥ 2` below `ζ_{Ω₁+1} = φ(2, Ω₁+1)` is at most `Ω₁`);
* `gu_mem` (**every code lies in every hull containing its gate**, together with `ω^e·c` for every `e` in the hull);
* `guK : GiCS` (**THE CODE SYSTEM below `ζ_{Ω₁+1}`**).

No new axiom.  New definition: `guK`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gk

open Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh Googology.Trans.PoR.InaccPsi.R2.Gi
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi
  Googology.Notation.InaccPsi.InaccSeq

/-- **The gate of a code below `ζ_{Ω₁+1}` over `Z`** (atoms above `ζ_{Ω₁+1}`) is below `Z`. -/
theorem gu_code_gate {Z : Ordinal.{0}} {At : Set Ordinal.{0}} (hZ1 : Z ≤ Om1) (hZ0 : 0 < Z)
    (hZa : ∀ u v, u < Z → v < Z → u + v < Z) (hZp : ∀ u v, u < Z → v < Z → veblen u v < Z)
    (hAt : ∀ s ∈ At, guB < s) {c : Ordinal.{0}} (hc : GxCl Z At c) : c < guB → guG c < Z := by
  have hAt' : ∀ s ∈ At, gfE < s := fun s hs => gfE_lt_guB.trans (hAt s hs)
  have hZw : ∀ u, u < Z → ω ^ u < Z := fun u hu => by
    have := hZp 0 u hZ0 hu; rwa [veblen_zero_apply] at this
  have h1Z : (1 : Ordinal.{0}) < Z := by
    have := hZw 0 hZ0; rwa [opow_zero] at this
  have hωZ : ω < Z := by
    have := hZw 1 h1Z; rwa [opow_one] at this
  have hsmall : ∀ x, GxCl Z At x → x < gfE → guG x < Z := fun x hx h => by
    rw [guG_low h]; exact gfCode_gate hZ1 hZ0 hZa hZp hAt' hx h
  induction hc with
  | @small x h => exact fun _ => hsmall _ (GxCl.small h) ((h.trans_le hZ1).trans Om1_lt_eW)
  | om => exact fun _ => hsmall _ GxCl.om (by rw [← Br.Om1_eq]; exact Om1_lt_eW)
  | @atom s hs => exact fun h => absurd (hAt s hs) (not_lt.2 h.le)
  | @add x y hx hy ihx ihy =>
    intro h
    exact gu_add hZa hωZ x y h (ihx (lt_of_le_of_lt le_self_add h)) (ihy (lt_of_le_of_lt le_add_self h))
  | @phi x y hx hy ihx ihy =>
    intro h
    rcases lt_or_ge (veblen x y) gfE with hlt | hge
    · exact hsmall _ (GxCl.phi hx hy) hlt
    have hyB : y < guB := lt_of_le_of_lt (right_le_veblen x y) h
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [veblen_zero_apply] at h ⊢
      exact gu_opow_gate hZw hωZ y h (ihy hyB)
    rcases eq_or_ne x 1 with rfl | hx1
    · -- `φ(1, y) = ε_{Ω₁+ν}`, `y = Ω₁ + ν`
      have hOy : Om1 + 1 ≤ y := by
        rw [eW_eq] at hge; exact (veblen_le_veblen_iff_right).1 hge
      have hOy' : Om1 ≤ y := le_self_add.trans hOy
      set ν := y - Om1 with hνdef
      have hν : Om1 + ν = y := Ordinal.add_sub_cancel_of_le hOy'
      have hν1 : 1 ≤ ν := by
        rw [← hν] at hOy; exact (add_le_add_iff_left _).1 hOy
      have hνy : ν ≤ y := by rw [← hν]; exact le_add_self
      have hνB : ν < guB := hνy.trans_lt hyB
      have he : veblen 1 y = evA Om1 ν := by rw [gu_evA_eq, hν]
      rw [he, guG_base hν1 hνB]
      refine (guQ_le ν).trans_lt ?_
      have hgy := ihy hyB
      rcases lt_or_ge ν (Om1 * ω) with hνω | hνω
      · have hOω : Om1 * ω < gfE := eW_E.mul_lt Om1_lt_eW ((omega_lt_Om1).trans Om1_lt_eW)
        have hyW : y < gfE := by
          rw [← hν]
          calc Om1 + ν < Om1 + Om1 * ω := (add_lt_add_iff_left _).2 hνω
            _ = Om1 * ω := by
                rw [← mul_one_add, one_add_of_omega0_le le_rfl]
            _ < gfE := hOω
        rw [guG_low (hνω.trans hOω)]
        rw [guG_low hyW] at hgy
        exact (gtc_le_Om1_add hνω).trans_lt (by rw [hν]; exact hgy)
      · have e : Om1 + ν = ν := add_eq_right_iff_mul_omega0_le.2 hνω
        rw [← e, hν]; exact hgy
    · -- `x ≥ 2`: below `φ(2, Ω₁+1)` such a point is at most `Ω₁`
      exfalso
      have hx2 : 2 ≤ x := by
        rcases lt_or_ge x 2 with h2 | h2
        · exfalso
          have : x < 1 + 1 := by rw [one_add_one_eq_two]; exact h2
          rcases (Order.lt_add_one_iff.1 this).lt_or_eq with h3 | h3
          · exact hx0 (lt_one_iff_zero.1 h3)
          · exact hx1 h3
        · exact h2
      obtain ⟨w', hw'⟩ : ∃ w', veblen 2 w' = veblen x y := by
        rcases hx2.lt_or_eq with h3 | h3
        · exact ⟨veblen x y, veblen_veblen_of_lt h3 y⟩
        · exact ⟨y, by rw [h3]⟩
      rw [guB_eq, ← hw'] at h
      have h1 : w' < Om1 + 1 := veblen_lt_veblen_iff_right.1 h
      have h2 : veblen 2 w' ≤ Om1 := by
        rw [← gu_veb2_Om1]; exact veblen_le_veblen_iff_right.2 (Order.lt_add_one_iff.1 h1)
      rw [← hw'] at hge
      exact absurd (hge.trans h2) (not_le.2 Om1_lt_eW)

theorem gu_nat_mem {S : InaccSeq.{0}} {a b : Ordinal.{0}} (n : ℕ) : (n : Ordinal.{0}) ∈ S.CSet a b := by
  have := lg_cset_mul_nat (CSet.one_mem (S := S) a b) n
  rwa [one_mul] at this

/-- **Every code `c < ζ_{Ω₁+1}` lies in every hull containing its gate**, and so does `ω^e·c` for every `e` in the
hull. -/
theorem gu_mem {S : InaccSeq.{0}} {a b : Ordinal.{0}} : ∀ c, c < guB → guG c < b →
    c ∈ S.CSet a b ∧ ∀ e ∈ S.CSet a b, ω ^ e * c ∈ S.CSet a b := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg
  rcases lt_or_ge c gfE with hcE | hcE
  · rw [guG_low hcE] at hg
    exact ⟨gfW_mem' hcE hg, fun e he => gw_mulOm_mem he c hcE hg⟩
  obtain ⟨hn1, -, -, hnB, hnc⟩ := guN_spec hcE hc
  obtain ⟨hk, hd0, hdE, hr, hdec, hkc, hrc, hdc⟩ := gu_parts hcE hc
  obtain ⟨q0n, q0k, q0d, g0r⟩ := gu_parts_Q hcE hc hg
  have hEc : guE c = evA Om1 (guN c) := rfl
  rw [hEc] at hk hd0 hdE hr hdec hkc hrc hdc q0k q0d g0r
  set n := guN c with hndef
  set E := evA Om1 n with hEdef
  have hE : InE E := evA_E _ _
  set k := log E c with hkdef
  set d := c / E ^ k with hddef
  set r := c % E ^ k with hrdef
  have hO : Om1 ∈ S.CSet a b := by rw [Br.Om1_eq]; exact CSet.Om_mem (CSet.one_mem _ _)
  -- a part `p < c` with gate (as a part) below `b`
  have hpart : ∀ p, p < c → guQ p < b → (p ∈ S.CSet a b ∧ ∀ e ∈ S.CSet a b, ω ^ e * p ∈ S.CSet a b) := by
    intro p hpc hq
    by_cases hω : p < ω
    · obtain ⟨m, rfl⟩ := lt_omega0.1 hω
      exact ⟨gu_nat_mem m, fun e he => lg_cset_mul_nat (by
        have := CSet.phi_mem (CSet.zero_mem (S := S) a b) he; rwa [veblen_zero_apply] at this) m⟩
    · have hQ : guQ p = guG p := by unfold guQ; rw [if_neg hω]
      exact IH p hpc (hpc.trans hc) (hQ ▸ hq)
  have hn := (hpart n hnc q0n).1
  have hEm : E ∈ S.CSet a b := by
    rw [hEdef, gu_evA_eq]; exact CSet.phi_mem (CSet.one_mem _ _) (CSet.add_mem hO hn)
  have hEk : E * k ∈ S.CSet a b := by
    have := (hpart k hkc q0k).2 E hEm
    rwa [show ω ^ E = E from hE] at this
  have hd := hpart d hdc q0d
  have hrr := IH r hrc (hrc.trans hc) g0r
  have hpow : E ^ k = ω ^ (E * k) := gu_pow_eq hE k
  refine ⟨?_, fun e he => ?_⟩
  · rw [← hdec, hpow]
    exact CSet.add_mem (hd.2 _ hEk) hrr.1
  · rw [← hdec, hpow, mul_add, ← mul_assoc, ← opow_add]
    exact CSet.add_mem (hd.2 _ (CSet.add_mem he hEk)) (hrr.2 e he)

/-- **THE CODE SYSTEM below `ζ_{Ω₁+1}`** (every pseudo-base `ε_{Ω₁+ν}`). -/
noncomputable def guK : GiCS where
  B := guB
  gt := guG
  B_lt := guB_lt_G0
  gt_zero := guG_zero
  gt_lt := guG_lt_Om1
  gt_succ := fun b _ hZ hb hg => guG_succ hZ b hb hg
  mem := fun _ _ _ c hc hg => (gu_mem c hc hg).1
  B_mem := fun _ _ _ => guB_mem
  code_gate := fun _ _ hZ1 hZ0 hZa hZp hAt _ hc hcB => gu_code_gate hZ1 hZ0 hZa hZp hAt hc hcB
  count := fun _ _ hc hy hy1 => gu_count hc hy hy1

theorem guK_B : guK.B = guB := rfl

theorem guK_gt : guK.gt = guG := rfl

end Googology.Trans.PoR.InaccPsi.R2.Gk

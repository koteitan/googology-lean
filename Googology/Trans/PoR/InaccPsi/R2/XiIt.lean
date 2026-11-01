import Googology.Trans.PoR.InaccPsi.R2.XdLaw1

/-!
# Iterates of `ψ_κ` over a base at every level `κ = Ω_{s+1}`, and the base-relative cofinality of `ψ_{Ω₂}`

`κ = Ω_{s+1}` (`s + 1 < Ω₁`), `z_0 = 0`, `z_{n+1} = ψ_κ(b + z_n)` (`xiZ S κ b`).

* `xiZ_lt` (the iterates increase strictly when `b ∈ Cl(b, ψ_κ(b))`), `xiZ_mem` (they lie in every closure
  `Cl(a, c)` that contains `b` and `κ` with `b + z_n ≤ a`);
* `xiMod_add` (`(p + q) % κ ≤ p % κ + q % κ` for strongly critical `κ`), `xiModLt` (**every
  `x ∈ Cl(c, ψ_κ(c))` has `x % κ < ψ_κ(c)`**);
* `xiCof` (**THE BASE-RELATIVE COFINALITY**: for `b ∈ Cl(b, ψ_κ(b))`, `b % κ = 0`, `Ω₂ ≤ Ω_s`:
  `ψ_{Ω₂}(b + κ) ≤ sup_n ψ_{Ω₂}(b + z_n)`; the base-relative form of `Vn.vnPsi2_eq` with `Uu.uuY_le_sup`),
  `xiCof_lt` (`ζ < ψ₂(b + κ) ⇒ ζ < ψ₂(b + z_n)` for some `n`).

No new axiom.  New definition: `xiZ` (the iterates; auxiliary, no repo statement depends on it).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xi

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Uu Googology.Trans.PoR.InaccPsi.R2.Ld

variable {S : InaccSeq.{0}}

/-- The iterates over the base `b` at the level `κ`: `z_0 = 0`, `z_{n+1} = ψ_κ(b + z_n)`. -/
noncomputable def xiZ (S : InaccSeq.{0}) (κ b : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => 0
  | n + 1 => S.psi (b + xiZ S κ b n) κ

theorem xiZ_zero (κ b : Ordinal.{0}) : xiZ S κ b 0 = 0 := rfl

theorem xiZ_succ (κ b : Ordinal.{0}) (n : ℕ) : xiZ S κ b (n + 1) = S.psi (b + xiZ S κ b n) κ := rfl

/-- A power `ω^c ≥ κ` with `ω^κ = κ` is a multiple of `κ`. -/
theorem xiMod_opow {κ c : Ordinal.{0}} (hκ : ω ^ κ = κ) (h : κ ≤ ω ^ c) : ω ^ c % κ = 0 := by
  have hc : κ ≤ c := by
    rw [← hκ] at h; exact (opow_le_opow_iff_right one_lt_omega0).1 h
  rw [← Ordinal.add_sub_cancel_of_le hc, opow_add, hκ]
  exact Ordinal.mul_mod _ _

/-- `(p + q) % κ ≤ p % κ + q % κ` for strongly critical `κ`. -/
theorem xiMod_add {κ : Ordinal.{0}} (hP : SC κ) (p q : Ordinal.{0}) : (p + q) % κ ≤ p % κ + q % κ := by
  have hP0 : κ ≠ 0 := hP.1.ne'
  rcases lt_or_ge q κ with hq | hq
  · rw [ldModK_add_lt hP p hq, Ordinal.mod_eq_of_lt hq]
  · have hm : 1 ≤ q / κ := by
      rw [Order.one_le_iff_ne_zero]
      intro h0
      have := Ordinal.div_add_mod q κ
      rw [h0, mul_zero, zero_add] at this
      exact absurd (this ▸ Ordinal.mod_lt q hP0) (not_lt.2 hq)
    have hab : p % κ + κ * (q / κ) = κ * (q / κ) := by
      have h2 : ω ^ κ = κ := gg_SC_eps hP
      refine Ordinal.add_absorp (by rw [h2]; exact Ordinal.mod_lt p hP0) ?_
      rw [h2]; exact Ordinal.le_mul_left _ (zero_lt_one.trans_le hm)
    have e : p + q = κ * (p / κ + q / κ) + q % κ := by
      conv_lhs => rw [← Ordinal.div_add_mod p κ, ← Ordinal.div_add_mod q κ]
      rw [mul_add, add_assoc, ← add_assoc (p % κ), hab, add_assoc]
    rw [e, Ordinal.mul_add_mod_self, Ordinal.mod_mod]
    exact le_add_self

section Lev

variable {s : Ordinal.{0}} (hs : s + 1 < Om 1)

include hs

/-- **Every `x ∈ Cl(c, ψ_κ(c))` has `x % κ < ψ_κ(c)`** (`κ = Ω_{s+1}`). -/
theorem xiModLt (c : Ordinal.{0}) :
    ∀ x ∈ S.CSet c (S.psi c (Om (s + 1))), x % Om (s + 1) < S.psi c (Om (s + 1)) := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  have hκS : SC (Om (s + 1)) := SC_Om (add_pos_of_right zero_lt_one s).ne'
  have hκε : ω ^ Om (s + 1) = Om (s + 1) := gg_SC_eps hκS
  have hP : SC (S.psi c (Om (s + 1))) := SC_psi hκ _
  have hsP : Om s < S.psi c (Om (s + 1)) := (psiS_bounds (S := S) c s).1
  intro x hx
  induction hx with
  | small h => exact (Ordinal.mod_le _ _).trans_lt h
  | zero => rw [Ordinal.zero_mod]; exact hP.1
  | inacc n => rw [Xd.xdModG hκε (SC_I n) (uuOm_le_I hs n)]; exact hP.1
  | inaccW => rw [Xd.xdModG hκε SC_Iw ((uuOm_le_I hs 0).trans (S.I_le_Iw 0))]; exact hP.1
  | @add p q _ _ ihp ihq => exact (xiMod_add hκS p q).trans_lt (hP.isPrincipal ihp ihq)
  | @phi p q _ _ ihp ihq =>
    rcases lt_or_ge (veblen p q) (Om (s + 1)) with hlt | hge
    · have hp : p < Om (s + 1) := (left_le_veblen p q).trans_lt hlt
      have hq : q < Om (s + 1) := (right_le_veblen p q).trans_lt hlt
      rw [Ordinal.mod_eq_of_lt hp] at ihp
      rw [Ordinal.mod_eq_of_lt hq] at ihq
      rw [Ordinal.mod_eq_of_lt hlt]; exact hP.2 _ ihp _ ihq
    · obtain ⟨d, hd⟩ := Ordinal.veblen_mem_range_opow p q
      rw [← hd] at hge ⊢
      rw [xiMod_opow hκε hge]; exact hP.1
  | @om a _ _ =>
    rcases lt_or_ge (Om a) (Om (s + 1)) with hlt | hge
    · have ha : a ≤ s := Order.lt_add_one_iff.1 (Om_lt_Om.1 hlt)
      rw [Ordinal.mod_eq_of_lt hlt]; exact (Om_le_Om.2 ha).trans_lt hsP
    · have ha0 : a ≠ 0 := by
        rintro rfl
        rw [Om_zero] at hge
        exact absurd hge (not_le.2 hκS.1)
      rw [Xd.xdModG hκε (SC_Om ha0) hge]; exact hP.1
  | @coll π e hπ _ heC _ _ =>
    rcases lt_trichotomy π (Om (s + 1)) with hlt | heq | hgt
    · exact (Ordinal.mod_le _ _).trans_lt (((psi_lt hπ _).trans_le (uuInR_lt hs hπ hlt)).trans hsP)
    · subst heq
      have h1 : S.psi e.1 (Om (s + 1)) < S.psi c (Om (s + 1)) := psi_lt_psi_of_mem hκ e.2 heC
      exact (Ordinal.mod_le _ _).trans_lt h1
    · rw [Xd.xdModG hκε (SC_psi hπ e.1) (uuInR_gt hs hπ hgt e.1)]; exact hP.1

end Lev

section Base

variable {s b : Ordinal.{0}}

theorem xiZ_lt_K (n : ℕ) : xiZ S (Om (s + 1)) b n < Om (s + 1) := by
  cases n with
  | zero => exact Om_pos (add_pos_of_right zero_lt_one s).ne'
  | succ n => rw [xiZ_succ]; exact psi_lt (InR_Om_succ s) _

theorem xiZ_SC (n : ℕ) : SC (xiZ S (Om (s + 1)) b (n + 1)) := by rw [xiZ_succ]; exact SC_psi (InR_Om_succ s) _

variable (hbn : b ∈ S.CSet b (S.psi b (Om (s + 1))))
include hbn

/-- **The iterates increase strictly** (`b` normal at the level `κ`). -/
theorem xiZ_lt : ∀ n : ℕ, xiZ S (Om (s + 1)) b n < xiZ S (Om (s + 1)) b (n + 1) := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  intro n
  induction n with
  | zero => rw [xiZ_succ, xiZ_zero]; exact (SC_psi hκ _).1
  | succ n ih =>
    rw [xiZ_succ (Om (s + 1)) b (n + 1), xiZ_succ (Om (s + 1)) b n]
    refine psi_lt_psi_of_mem hκ ((add_lt_add_iff_left b).2 ih) (CSet.add_mem ?_ (CSet.of_lt ?_))
    · exact (psi_mono (S := S) hκ le_self_add).2 hbn
    · exact ih.trans_le (by rw [xiZ_succ]; exact (psi_mono hκ (add_le_add le_rfl ih.le)).1)

theorem xiZ_mono : Monotone (xiZ S (Om (s + 1)) b) := (strictMono_nat_of_lt_succ (xiZ_lt hbn)).monotone

/-- **The iterates lie in every closure containing `b`** (with `b + z_n ≤ a`). -/
theorem xiZ_mem (hK : ∀ a c : Ordinal.{0}, Om (s + 1) ∈ S.CSet a c) :
    ∀ (n : ℕ) (a c : Ordinal.{0}), b ∈ S.CSet a c → b + xiZ S (Om (s + 1)) b n ≤ a →
    xiZ S (Om (s + 1)) b n ∈ S.CSet a c := by
  intro n
  induction n with
  | zero => intro a c _ _; exact CSet.zero_mem a c
  | succ n ih =>
    intro a c hb ha
    have hlt : b + xiZ S (Om (s + 1)) b n < a :=
      ((add_lt_add_iff_left b).2 (xiZ_lt hbn n)).trans_le ha
    rw [xiZ_succ]
    exact CSet.psi_mem hlt (InR_Om_succ s) (hK a c) (CSet.add_mem hb (ih a c hb hlt.le))

variable (hs : s + 1 < Om 1) (hs2 : Om (1 + 1) ≤ Om s) (hbm : b % Om (s + 1) = 0)
include hs hs2 hbm

/-- **THE BASE-RELATIVE COFINALITY**: `ψ_{Ω₂}(b + κ) ≤ sup_n ψ_{Ω₂}(b + z_n)`. -/
theorem xiCof : S.psi (b + Om (s + 1)) (Om (1 + 1)) ≤
    ⨆ n : ℕ, S.psi (b + xiZ S (Om (s + 1)) b n) (Om (1 + 1)) := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hκS : SC (Om (s + 1)) := SC_Om (add_pos_of_right zero_lt_one s).ne'
  set z := xiZ S (Om (s + 1)) b with hz
  set Q := ⨆ n : ℕ, S.psi (b + z n) (Om (1 + 1)) with hQ
  have hbdd : BddAbove (range fun n : ℕ => S.psi (b + z n) (Om (1 + 1))) :=
    ⟨Om (1 + 1), by rintro _ ⟨n, rfl⟩; exact (psi_lt hκ2 _).le⟩
  have hmono := xiZ_mono hbn
  have hsub : ∀ i j : ℕ, i ≤ j → S.CSet (b + z i) (S.psi (b + z i) (Om (1 + 1))) ⊆
      S.CSet (b + z j) (S.psi (b + z j) (Om (1 + 1))) := fun i j hij =>
    (psi_mono hκ2 (add_le_add le_rfl (hmono hij))).2
  have h2κ : ∀ c, S.psi c (Om (1 + 1)) ≤ S.psi c (Om (s + 1)) := fun c =>
    ((psi_lt hκ2 c).le.trans hs2).trans (psiS_bounds (S := S) c s).1.le
  have key : ∀ x ∈ S.CSet (b + Om (s + 1)) Q, ∃ n, x ∈ S.CSet (b + z n) (S.psi (b + z n) (Om (1 + 1))) := by
    intro x hx
    induction hx with
    | small h =>
      obtain ⟨n, hn⟩ := (lt_ciSup_iff hbdd).1 h
      exact ⟨n, CSet.of_lt hn⟩
    | zero => exact ⟨0, CSet.zero_mem _ _⟩
    | inacc n => exact ⟨0, Clos.inacc n⟩
    | inaccW => exact ⟨0, Clos.inaccW⟩
    | add _ _ ihp ihq =>
      obtain ⟨i, hi⟩ := ihp
      obtain ⟨j, hj⟩ := ihq
      exact ⟨max i j, CSet.add_mem (hsub i _ (le_max_left i j) hi) (hsub j _ (le_max_right i j) hj)⟩
    | phi _ _ ihp ihq =>
      obtain ⟨i, hi⟩ := ihp
      obtain ⟨j, hj⟩ := ihq
      exact ⟨max i j, Clos.phi (hsub i _ (le_max_left i j) hi) (hsub j _ (le_max_right i j) hj)⟩
    | om _ ih =>
      obtain ⟨i, hi⟩ := ih
      exact ⟨i, CSet.Om_mem hi⟩
    | @coll π e hπ _ _ ihπ ihe =>
      obtain ⟨i, hi⟩ := ihπ
      obtain ⟨m, hm⟩ := ihe
      have hlt : e.1 < b + z (m + 1) := by
        rcases lt_or_ge e.1 b with h1 | h1
        · exact h1.trans_le le_self_add
        · have hw : e.1 - b < Om (s + 1) := Ry.rySub_lt h1 e.2
          have ee : e.1 = b + (e.1 - b) := (Ordinal.add_sub_cancel_of_le h1).symm
          have hmod : e.1 % Om (s + 1) = e.1 - b := by
            conv_lhs => rw [ee]
            rw [ldModK_add_lt hκS b hw, hbm, zero_add]
          have h3 := xiModLt hs (b + z m) e.1 (CSet_mono le_rfl (h2κ _) hm)
          rw [hmod, ← xiZ_succ] at h3
          rw [ee]; exact (add_lt_add_iff_left b).2 h3
      set N := max (m + 1) i with hN
      have hltN : e.1 < b + z N := hlt.trans_le (add_le_add le_rfl (hmono (le_max_left _ _)))
      have heN := hsub m N ((Nat.le_succ m).trans (le_max_left _ _)) hm
      have hπN := hsub i N (le_max_right _ _) hi
      exact ⟨N, Clos.coll (e := ⟨e.1, hltN⟩) hπ hπN heN⟩
  refine psi_le_of_good (mxOm2_mem _ _) fun x hx hx2 => ?_
  obtain ⟨n, hn⟩ := key x hx
  exact (lt_psi_of_mem hκ2 hn hx2).trans_le (le_ciSup hbdd n)

/-- `ζ < ψ₂(b + κ) ⇒ ζ < ψ₂(b + z_n)` for some `n`. -/
theorem xiCof_lt {ζ : Ordinal.{0}} (hζ : ζ < S.psi (b + Om (s + 1)) (Om (1 + 1))) :
    ∃ n : ℕ, ζ < S.psi (b + xiZ S (Om (s + 1)) b n) (Om (1 + 1)) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hbdd : BddAbove (range fun n : ℕ => S.psi (b + xiZ S (Om (s + 1)) b n) (Om (1 + 1))) :=
    ⟨Om (1 + 1), by rintro _ ⟨n, rfl⟩; exact (psi_lt hκ2 _).le⟩
  exact (lt_ciSup_iff hbdd).1 (hζ.trans_le (xiCof hbn hs hs2 hbm))

end Base

end Googology.Trans.PoR.InaccPsi.R2.Xi

#print axioms Googology.Trans.PoR.InaccPsi.R2.Xi.xiModLt
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xi.xiZ_lt
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xi.xiZ_mem
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xi.xiCof
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xi.xiCof_lt

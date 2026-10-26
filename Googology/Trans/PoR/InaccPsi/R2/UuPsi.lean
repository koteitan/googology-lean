import Googology.Trans.PoR.InaccPsi.R2.UqFix

/-!
# Generic facts on `ψ_{Ω_{s+1}}` for a finite level `s`: normal arguments below `ψ(Ω_{s+1})`, the successor step

`κ = Ω_{s+1}` with `s + 1 < Ω₁`, `ψ = ψ_κ`, `f(a) = φ(a, 0)`.

* `uuInR_lt`, `uuInR_gt` (a subscript `π ∈ InR` below `κ` is `≤ Ω_s`; above `κ`, `ψ_π(e) ≥ κ`);
* `uuIt_lt` (the iterates `y_0 = 0`, `y_{n+1} = ψ(y_n)` increase), `uuY_le_sup` (**`ψ(κ) ≤ sup_n y_n`**),
  `uuLtPsi` (**EVERY `α < ψ(κ)` IS A NORMAL ARGUMENT: `α < ψ(α)`**);
* `uuSucc_le` (`ψ(α + 1) ≤ nfp f (ψ(α) + 1)`, no hypothesis), `uuSucc_ge`, `uuSucc_eq` (**at a normal argument
  `α < ψ(α)`: `ψ(α + 1) = nfp f (ψ(α) + 1)`, the least strongly critical ordinal above `ψ(α)`**), `uuSucc_next`.

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Uu

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2

variable {S : InaccSeq.{0}}

section Gen

variable {s : Ordinal.{0}} (hs : s + 1 < Om 1)

include hs

/-- `Ω_{s+1} ≤ I_n`. -/
theorem uuOm_le_I (n : ℕ) : Om (s + 1) ≤ S.I n := by
  rw [← S.fix n]; exact Om_le_Om.2 (hs.le.trans (Low.Om_one_le_I n))

/-- A subscript `π` below `Ω_{s+1}` is at most `Ω_s`. -/
theorem uuInR_lt {π : Ordinal.{0}} (hπ : S.InR π) (h : π < Om (s + 1)) : π ≤ Om s := by
  rcases hπ with ⟨m, rfl⟩ | ⟨t, rfl⟩
  · exact absurd h (not_lt.2 (uuOm_le_I hs m))
  · exact Om_le_Om.2 (Order.lt_add_one_iff.1 (Om_lt_Om.1 h))

/-- A subscript `π` above `Ω_{s+1}` gives `ψ_π(e) ≥ Ω_{s+1}`. -/
theorem uuInR_gt {π : Ordinal.{0}} (hπ : S.InR π) (h : Om (s + 1) < π) (e : Ordinal.{0}) :
    Om (s + 1) ≤ S.psi e π := by
  rcases hπ with ⟨m, rfl⟩ | ⟨t, rfl⟩
  · calc Om (s + 1) ≤ Om (S.psi e (S.I m)) := Om_le_Om.2 (hs.trans (Om_one_lt_psiI e m)).le
      _ = S.psi e (S.I m) := Om_psiI e m
  · have hst : s + 1 ≤ t := Order.lt_add_one_iff.1 (Om_lt_Om.1 h)
    exact (Om_le_Om.2 hst).trans (psiS_bounds e t).1.le

omit hs in
/-- The iterates `y_n` of `ψ_{Ω_{s+1}}` from `0` increase strictly. -/
theorem uuIt_lt (s : Ordinal.{0}) : ∀ n : ℕ,
    (fun a => S.psi a (Om (s + 1)))^[n] 0 < (fun a => S.psi a (Om (s + 1)))^[n + 1] 0 := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  intro n
  induction n with
  | zero => exact (SC_psi hκ 0).1
  | succ n ih =>
    rw [Function.iterate_succ_apply' _ (n + 1), Function.iterate_succ_apply' _ n]
    rw [Function.iterate_succ_apply' _ n] at ih
    exact psi_lt_psi_of_mem hκ ih (CSet.of_lt (ih.trans_le (psi_mono hκ ih.le).1))

omit hs in
theorem uuIt_mono (s : Ordinal.{0}) : Monotone fun n : ℕ => (fun a => S.psi a (Om (s + 1)))^[n] 0 :=
  (strictMono_nat_of_lt_succ (uuIt_lt s)).monotone

omit hs in
theorem uuIt_bdd (s : Ordinal.{0}) :
    BddAbove (range fun n : ℕ => (fun a => S.psi a (Om (s + 1)))^[n] 0) := by
  refine ⟨Om (s + 1), ?_⟩
  rintro _ ⟨n, rfl⟩
  rcases n with _ | n
  · exact zero_le
  · show (fun a => S.psi a (Om (s + 1)))^[n + 1] 0 ≤ Om (s + 1)
    rw [Function.iterate_succ_apply']; exact (psi_lt (InR_Om_succ s) _).le

/-- **`ψ_{Ω_{s+1}}(Ω_{s+1}) ≤ sup_n y_n`.** -/
theorem uuY_le_sup : S.psi (Om (s + 1)) (Om (s + 1)) ≤ ⨆ n : ℕ, (fun a => S.psi a (Om (s + 1)))^[n] 0 := by
  set y : ℕ → Ordinal.{0} := fun n => (fun a => S.psi a (Om (s + 1)))^[n] 0 with hy_def
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  have hbdd := uuIt_bdd (S := S) s
  have hmono := uuIt_mono (S := S) s
  have hsucc : ∀ n, y (n + 1) = S.psi (y n) (Om (s + 1)) := fun n => Function.iterate_succ_apply' _ n 0
  have hy1 : Om s < y 1 := by rw [hsucc 0]; exact (psiS_bounds 0 s).1
  have hle : ∀ n, y n ≤ ⨆ n, y n := fun n => le_ciSup hbdd n
  have hSC : ∀ n, SC (y (n + 1)) := fun n => by rw [hsucc n]; exact SC_psi hκ _
  have key : ∀ x ∈ S.CSet (Om (s + 1)) (⨆ n, y n), x < Om (s + 1) → ∃ n, x < y n := by
    intro x hx
    induction hx with
    | small h => exact fun _ => (lt_ciSup_iff hbdd).1 h
    | zero => exact fun _ => ⟨1, (uuIt_lt s 0)⟩
    | inacc n => exact fun h => absurd h (not_lt.2 (uuOm_le_I hs n))
    | inaccW => exact fun h => absurd h (not_lt.2 ((uuOm_le_I hs 0).trans (S.I_le_Iw 0)))
    | @add a b _ _ iha ihb =>
      intro h
      obtain ⟨i, hi⟩ := iha (le_self_add.trans_lt h)
      obtain ⟨j, hj⟩ := ihb (le_add_self.trans_lt h)
      refine ⟨max i j + 1, (hSC (max i j)).isPrincipal (hi.trans_le (hmono ?_)) (hj.trans_le (hmono ?_))⟩
      · exact (le_max_left i j).trans (Nat.le_succ _)
      · exact (le_max_right i j).trans (Nat.le_succ _)
    | @phi a b _ _ iha ihb =>
      intro h
      obtain ⟨i, hi⟩ := iha ((left_le_veblen a b).trans_lt h)
      obtain ⟨j, hj⟩ := ihb ((right_le_veblen a b).trans_lt h)
      refine ⟨max i j + 1, (hSC (max i j)).2 _ (hi.trans_le (hmono ?_)) _ (hj.trans_le (hmono ?_))⟩
      · exact (le_max_left i j).trans (Nat.le_succ _)
      · exact (le_max_right i j).trans (Nat.le_succ _)
    | @om a _ _ =>
      intro h
      have ha : a ≤ s := Order.lt_add_one_iff.1 (Om_lt_Om.1 h)
      exact ⟨1, (Om_le_Om.2 ha).trans_lt hy1⟩
    | @coll π e hπ _ _ _ ihe =>
      intro h
      rcases lt_trichotomy π (Om (s + 1)) with hlt | heq | hgt
      · exact ⟨1, ((psi_lt hπ _).trans_le (uuInR_lt hs hπ hlt)).trans hy1⟩
      · subst heq
        obtain ⟨n, hn⟩ := ihe e.2
        refine ⟨n + 1 + 1, ?_⟩
        calc S.psi e.1 (Om (s + 1)) ≤ S.psi (y n) (Om (s + 1)) := (psi_mono hκ hn.le).1
          _ = y (n + 1) := (hsucc n).symm
          _ < y (n + 1 + 1) := uuIt_lt s (n + 1)
      · exact absurd h (not_lt.2 (uuInR_gt hs hπ hgt _))
  refine psi_le_of_good ?_ fun x hx hxκ => ?_
  · refine CSet.Om_mem (CSet.succ_mem (CSet.of_lt ?_))
    exact ((le_Om s).trans_lt hy1).trans_le (hle 1)
  · obtain ⟨n, hn⟩ := key x hx hxκ
    exact hn.trans_le (hle n)

/-- **EVERY `α < ψ_{Ω_{s+1}}(Ω_{s+1})` IS A NORMAL ARGUMENT**: `α < ψ_{Ω_{s+1}}(α)`. -/
theorem uuLtPsi {α : Ordinal.{0}} (hα : α < S.psi (Om (s + 1)) (Om (s + 1))) : α < S.psi α (Om (s + 1)) := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  obtain ⟨n, hn⟩ := (lt_ciSup_iff (uuIt_bdd (S := S) s)).1 (hα.trans_le (uuY_le_sup hs))
  induction n generalizing α with
  | zero => exact absurd hn (not_lt.2 zero_le)
  | succ n ih =>
    by_cases h : α < (fun a => S.psi a (Om (s + 1)))^[n] 0
    · exact ih hα h
    · push Not at h
      rw [Function.iterate_succ_apply'] at hn
      exact hn.trans_le (psi_mono hκ h).1

omit hs in
/-- **`ψ(α + 1) ≤ nfp f (ψ(α) + 1)`** (`f(a) = φ(a, 0)`). -/
theorem uuSucc_le (hs : s + 1 < Om 1) (α : Ordinal.{0}) :
    S.psi (α + 1) (Om (s + 1)) ≤ nfp (fun a => veblen a 0) (S.psi α (Om (s + 1)) + 1) := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  set P := S.psi α (Om (s + 1)) with hP_def
  set N := nfp (fun a : Ordinal.{0} => veblen a 0) (P + 1) with hN_def
  have hfp : veblen N 0 = N := nfp_fp isNormal_veblen_zero (P + 1)
  have hPN : P < N := (lt_add_one P).trans_le (le_nfp _ _)
  have hNSC : SC N := Ru.ruSC_of_veblen (zero_le.trans_lt hPN) hfp
  have hsP : Om s < P := (psiS_bounds α s).1
  refine psi_le_of_good ?_ fun x hx => ?_
  · exact CSet.Om_mem (CSet.succ_mem (CSet.of_lt (((le_Om s).trans_lt hsP).trans hPN)))
  induction hx with
  | small h => exact fun _ => h
  | zero => exact fun _ => hNSC.1
  | inacc n => exact fun h => absurd h (not_lt.2 (uuOm_le_I hs n))
  | inaccW => exact fun h => absurd h (not_lt.2 ((uuOm_le_I hs 0).trans (S.I_le_Iw 0)))
  | @add a b _ _ iha ihb =>
    exact fun h => hNSC.isPrincipal (iha (le_self_add.trans_lt h)) (ihb (le_add_self.trans_lt h))
  | @phi a b _ _ iha ihb =>
    exact fun h => hNSC.2 _ (iha ((left_le_veblen a b).trans_lt h)) _ (ihb ((right_le_veblen a b).trans_lt h))
  | @om a _ _ =>
    intro h
    exact ((Om_le_Om.2 (Order.lt_add_one_iff.1 (Om_lt_Om.1 h))).trans_lt hsP).trans hPN
  | @coll π e hπ _ _ _ _ =>
    intro h
    rcases lt_trichotomy π (Om (s + 1)) with hlt | heq | hgt
    · exact (((psi_lt hπ _).trans_le (uuInR_lt hs hπ hlt)).trans hsP).trans hPN
    · subst heq
      exact (psi_mono hκ (Order.lt_add_one_iff.1 e.2)).1.trans_lt hPN
    · exact absurd h (not_lt.2 (uuInR_gt hs hπ hgt _))

omit hs in
/-- At a normal argument `α < ψ(α)`: `nfp f (ψ(α) + 1) ≤ ψ(α + 1)`. -/
theorem uuSucc_ge (s : Ordinal.{0}) {α : Ordinal.{0}} (hα : α < S.psi α (Om (s + 1))) :
    nfp (fun a => veblen a 0) (S.psi α (Om (s + 1)) + 1) ≤ S.psi (α + 1) (Om (s + 1)) := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  have hlt : S.psi α (Om (s + 1)) < S.psi (α + 1) (Om (s + 1)) :=
    psi_lt_psi_of_mem hκ (lt_add_one α) (CSet.of_lt (hα.trans_le (psi_mono hκ le_self_add).1))
  exact nfp_le_fp veblen_zero_strictMono.monotone (Order.add_one_le_of_lt hlt) (SC_psi hκ _).veblen_zero.le

/-- **AT A NORMAL ARGUMENT `α < ψ(α)`: `ψ(α + 1) = nfp f (ψ(α) + 1)`.** -/
theorem uuSucc_eq {α : Ordinal.{0}} (hα : α < S.psi α (Om (s + 1))) :
    S.psi (α + 1) (Om (s + 1)) = nfp (fun a => veblen a 0) (S.psi α (Om (s + 1)) + 1) :=
  le_antisymm (uuSucc_le hs α) (uuSucc_ge s hα)

/-- **No strongly critical ordinal lies strictly between `ψ(α)` and `ψ(α + 1)`** (normal `α`). -/
theorem uuSucc_next {α Q : Ordinal.{0}} (hα : α < S.psi α (Om (s + 1))) (hQ : SC Q)
    (hPQ : S.psi α (Om (s + 1)) < Q) : S.psi (α + 1) (Om (s + 1)) ≤ Q := by
  rw [uuSucc_eq hs hα]
  exact nfp_le_fp veblen_zero_strictMono.monotone (Order.add_one_le_of_lt hPQ) hQ.veblen_zero.le

end Gen

/-- `1 + 1 < Ω₁`. -/
theorem uuTwo_lt : (1 + 1 : Ordinal.{0}) < Om 1 := by
  have h1 : (1 : Ordinal.{0}) < Om 1 := Gg.gg_one_lt_of_SC Ph.ph_SC_Om1
  exact Ph.ph_SC_Om1.isPrincipal h1 h1

/-- `1 + 1 + 1 < Ω₁`. -/
theorem uuThree_lt : (1 + 1 + 1 : Ordinal.{0}) < Om 1 := by
  have h1 : (1 : Ordinal.{0}) < Om 1 := Gg.gg_one_lt_of_SC Ph.ph_SC_Om1
  exact Ph.ph_SC_Om1.isPrincipal uuTwo_lt h1

/-- **Every `α < Y₃` is a normal argument of `ψ₃`.** -/
theorem uuLt3 {α : Ordinal.{0}} (hα : α < Ug.ugY S) : α < S.psi α (Om (1 + 1 + 1)) :=
  uuLtPsi uuThree_lt hα

/-- **Every `α < Y₂ = ψ₂(Ω₂)` is a normal argument of `ψ₂`.** -/
theorem uuLt2 {α : Ordinal.{0}} (hα : α < S.psi (Om (1 + 1)) (Om (1 + 1))) : α < S.psi α (Om (1 + 1)) :=
  uuLtPsi uuTwo_lt hα

end Googology.Trans.PoR.InaccPsi.R2.Uu

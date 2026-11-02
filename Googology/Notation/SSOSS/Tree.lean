import Mathlib.SetTheory.Ordinal.Veblen
import Mathlib.SetTheory.Ordinal.Principal

/-!
# The (0,0)-fragment of the strong second-order searching sequence as trees

A sequence `(0,0) ⌢ Y` with entries of `Y` in `{0,1}` is read as a list of units:
an entry `0` outside a block (`U.z`), or a block `U.b u` whose `T` (every maximal run
`1^a` shortened to `1^(a-1)`) is the list `u`.  Lists of units are stored with the
LAST unit first.

* value: `o((0,0) ⌢ Y) = 2 + vs Y`, `val z = 1`, `val (b u) = ω ^ (1 + vs u)`.
* expansion (the recursive cut): `E (b u :: P) k = H u k ++ P`.

Main results: `E_lt` (every term of the expansion is smaller) and `E_cof` (the terms
are cofinal), and `tower_lt_epsilon`, `tower_cof_epsilon` (the sequences `(0,0,1^k)`,
that is `(0,0,2)[k]`, have supremum `ε₀`).
-/

open Ordinal Order

namespace Googology.Notation.SSOSS

/-- A unit: `z` is an entry `0` outside a block, `b u` is a block whose `T` is `u`. -/
inductive U where
  | z : U
  | b : List U → U

mutual
/-- value of a unit -/
noncomputable def val : U → Ordinal.{0}
  | .z => 1
  | .b u => ω ^ (1 + vs u)
/-- value of a list of units (last unit first) -/
noncomputable def vs : List U → Ordinal.{0}
  | [] => 0
  | x :: rest => vs rest + val x
end

@[simp] theorem val_z : val .z = 1 := by simp [val]
@[simp] theorem val_b (u : List U) : val (.b u) = ω ^ (1 + vs u) := by simp [val]
@[simp] theorem vs_nil : vs [] = 0 := by simp [vs]
@[simp] theorem vs_cons (x : U) (l : List U) : vs (x :: l) = vs l + val x := by simp [vs]

/-- the units that replace the last block `b u` in the expansion with `k` copies -/
def H : List U → ℕ → List U
  | [], k => List.replicate k .z
  | .z :: rest, k => (List.replicate k [U.z, U.z, U.b rest]).flatten
  | .b w :: rest, k => [U.z, U.b ((H w k).tail ++ rest)]
termination_by u => sizeOf u
decreasing_by simp_wf; omega

/-- the expansion of a list whose last unit is a block -/
def E : List U → ℕ → List U
  | .b u :: P, k => H u k ++ P
  | l, _ => l

theorem vs_append (l m : List U) : vs (l ++ m) = vs m + vs l := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih, add_assoc]

theorem vs_replicate_z (k : ℕ) : vs (List.replicate k .z) = k := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, ih]

theorem vs_flatten_replicate (L : List U) (k : ℕ) :
    vs (List.replicate k L).flatten = vs L * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, vs_append, ih]
    push_cast
    rw [mul_add_one]

/-- for `k ≥ 1` the replacement starts (at its last unit) with an entry `0` -/
theorem H_head (u : List U) (k : ℕ) (hk : 1 ≤ k) : ∃ t, H u k = .z :: t := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  match u with
  | [] => exact ⟨List.replicate k .z, by simp [H, List.replicate_succ]⟩
  | .z :: rest =>
    exact ⟨U.z :: U.b rest :: (List.replicate k [U.z, U.z, U.b rest]).flatten,
      by simp [H, List.replicate_succ]⟩
  | .b w :: rest => exact ⟨[U.b ((H w (k + 1)).tail ++ rest)], by simp [H]⟩

theorem one_add_ne_zero (x : Ordinal.{0}) : 1 + x ≠ 0 :=
  (lt_of_lt_of_le zero_lt_one le_self_add).ne'

theorem one_lt_omega0_opow {c : Ordinal.{0}} (hc : c ≠ 0) : 1 < ω ^ c :=
  one_lt_opow.2 ⟨one_lt_omega0, hc⟩

/-- **Main lemma.** The replacement `H u k` of a block `b u` is below its value
`ω ^ (1 + vs u)`, and the replacements are cofinal in it. -/
theorem H_spec : ∀ (u : List U),
    (∀ k, 1 ≤ k → vs (H u k) < ω ^ (1 + vs u)) ∧
    (∀ β < ω ^ (1 + vs u), ∃ k, 1 ≤ k ∧ β < vs (H u k))
  | [] => by
    refine ⟨fun k _ => ?_, fun β hβ => ?_⟩
    · simp [H, vs_replicate_z]
    · simp only [vs_nil, add_zero, opow_one] at hβ
      obtain ⟨n, rfl⟩ := lt_omega0.1 hβ
      refine ⟨n + 1, by omega, ?_⟩
      simp only [H, vs_replicate_z]
      exact_mod_cast Nat.lt_succ_self n
  | .z :: rest => by
    set a := ω ^ (1 + vs rest) with ha
    have hvsH : ∀ k, vs (H (U.z :: rest) k) = (a + 1 + 1) * k := by
      intro k; simp [H, vs_flatten_replicate, ha]
    have hlt : 1 + vs rest < 1 + vs (U.z :: rest) := by
      simp only [vs_cons, val_z]
      exact (add_lt_add_iff_left 1).2 (lt_add_one (vs rest))
    have hω : ω ^ (1 + vs (U.z :: rest)) = a * ω := by
      simp only [vs_cons, val_z, ha]
      rw [← add_assoc, ← Order.succ_eq_add_one, opow_succ]
    refine ⟨fun k _ => ?_, fun β hβ => ?_⟩
    · rw [hvsH]
      have hp := isPrincipal_add_omega0_opow (1 + vs (U.z :: rest))
      have h1 : (1 : Ordinal) < ω ^ (1 + vs (U.z :: rest)) :=
        one_lt_omega0_opow (one_add_ne_zero _)
      have haω : a < ω ^ (1 + vs (U.z :: rest)) :=
        (opow_lt_opow_iff_right one_lt_omega0).2 hlt
      exact mul_lt_omega0_opow (pos_iff_ne_zero.2 (one_add_ne_zero _))
        (hp (hp haω h1) h1) (natCast_lt_omega0 k)
    · rw [hω] at hβ
      obtain ⟨c', hc', hβ'⟩ := (lt_mul_iff_of_isSuccLimit isSuccLimit_omega0).1 hβ
      obtain ⟨m, rfl⟩ := lt_omega0.1 hc'
      refine ⟨m + 1, by omega, ?_⟩
      rw [hvsH]
      calc β < a * m := hβ'
        _ ≤ a * ((m + 1 : ℕ) : Ordinal) := by gcongr; exact_mod_cast Nat.le_succ m
        _ ≤ (a + 1 + 1) * ((m + 1 : ℕ) : Ordinal) := by
            gcongr; exact le_self_add.trans le_self_add
  | .b w :: rest => by
    obtain ⟨ihlt, ihcof⟩ := H_spec w
    have hvsH : ∀ k, vs (H (U.b w :: rest) k) =
        ω ^ (1 + (vs rest + vs (H w k).tail)) + 1 := by
      intro k; simp [H, vs_append]
    have tail_lt : ∀ k, 1 ≤ k → vs (H w k).tail < ω ^ (1 + vs w) := by
      intro k hk
      obtain ⟨t, ht⟩ := H_head w k hk
      have h := ihlt k hk
      rw [ht] at h ⊢
      simp only [vs_cons, val_z, List.tail_cons] at h ⊢
      exact lt_of_le_of_lt le_self_add h
    refine ⟨fun k hk => ?_, fun β hβ => ?_⟩
    · rw [hvsH]
      have hp := isPrincipal_add_omega0_opow (1 + vs (U.b w :: rest))
      have h1 : (1 : Ordinal) < ω ^ (1 + vs (U.b w :: rest)) :=
        one_lt_omega0_opow (one_add_ne_zero _)
      have hexp : 1 + (vs rest + vs (H w k).tail) < 1 + vs (U.b w :: rest) := by
        simp only [vs_cons, val_b]
        exact (add_lt_add_iff_left 1).2 ((add_lt_add_iff_left (vs rest)).2 (tail_lt k hk))
      exact hp ((opow_lt_opow_iff_right one_lt_omega0).2 hexp) h1
    · have hlim : IsSuccLimit (1 + vs (U.b w :: rest)) := by
        simp only [vs_cons, val_b]
        rw [← add_assoc]
        exact isSuccLimit_add _ (isSuccLimit_opow_left isSuccLimit_omega0 (one_add_ne_zero _))
      obtain ⟨γ, hγ, hβγ⟩ := (lt_opow_of_isSuccLimit omega0_ne_zero hlim).1 hβ
      have hγ' : γ < (1 + vs rest) + ω ^ (1 + vs w) := by
        simpa [add_assoc] using hγ
      obtain ⟨δ, hδ, hγδ⟩ := (lt_add_iff (opow_ne_zero _ omega0_ne_zero)).1 hγ'
      obtain ⟨k, hk, hδk⟩ := ihcof δ hδ
      obtain ⟨t, ht⟩ := H_head w k hk
      have hδt : δ ≤ vs t := by
        rw [ht] at hδk
        simpa [Order.lt_add_one_iff] using hδk
      refine ⟨k, hk, ?_⟩
      rw [hvsH, ht, List.tail_cons]
      calc β < ω ^ γ := hβγ
        _ ≤ ω ^ (1 + (vs rest + vs t)) := by
            apply opow_le_opow_right omega0_pos
            calc γ ≤ 1 + vs rest + δ := hγδ
              _ ≤ 1 + vs rest + vs t := by gcongr
              _ = 1 + (vs rest + vs t) := add_assoc _ _ _
        _ ≤ _ := le_self_add
termination_by u => sizeOf u
decreasing_by simp_wf; omega

/-- every term of the expansion is smaller -/
theorem E_lt (u P : List U) (k : ℕ) (hk : 1 ≤ k) :
    vs (E (U.b u :: P) k) < vs (U.b u :: P) := by
  simp only [E, vs_append, vs_cons, val_b]
  exact (add_lt_add_iff_left (vs P)).2 ((H_spec u).1 k hk)

/-- the terms of the expansion are cofinal -/
theorem E_cof (u P : List U) :
    ∀ β < vs (U.b u :: P), ∃ k, 1 ≤ k ∧ β < vs (E (U.b u :: P) k) := by
  intro β hβ
  simp only [vs_cons, val_b] at hβ
  obtain ⟨δ, hδ, hβδ⟩ := (lt_add_iff (opow_ne_zero _ omega0_ne_zero)).1 hβ
  obtain ⟨k, hk, h⟩ := (H_spec u).2 δ hδ
  refine ⟨k, hk, ?_⟩
  simp only [E, vs_append]
  exact lt_of_le_of_lt hβδ ((add_lt_add_iff_left (vs P)).2 h)

/-- `tower n` is the tree of `(0,0,1^n)`, the `n`-th term of `(0,0,2)[n]`. -/
def tower : ℕ → List U
  | 0 => []
  | n + 1 => [U.b (tower n)]

theorem isPrincipal_add_epsilon0 : IsPrincipal (· + ·) (ε₀ : Ordinal.{0}) := by
  rw [← omega0_opow_epsilon 0]
  exact isPrincipal_add_omega0_opow _

theorem vs_tower_lt (n : ℕ) : vs (tower n) < ε₀ := by
  induction n with
  | zero => simp [tower]
  | succ n ih =>
    simp only [tower, vs_cons, vs_nil, val_b, zero_add]
    rw [← omega0_opow_epsilon 0]
    apply (opow_lt_opow_iff_right one_lt_omega0).2
    exact isPrincipal_add_epsilon0 (by simpa using natCast_lt_epsilon 1 0) ih

/-- `o((0,0,1^n)) = 2 + vs (tower n)` is below `ε₀` -/
theorem tower_lt_epsilon (n : ℕ) : 2 + vs (tower n) < ε₀ :=
  isPrincipal_add_epsilon0 (by simpa using natCast_lt_epsilon 2 0) (vs_tower_lt n)

theorem iterate_le_vs_tower (n : ℕ) : (fun a : Ordinal.{0} ↦ ω ^ a)^[n] 0 ≤ vs (tower n) := by
  induction n with
  | zero => simp [tower]
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    simp only [tower, vs_cons, vs_nil, val_b, zero_add]
    exact opow_le_opow_right omega0_pos (ih.trans le_add_self)

/-- `o((0,0,1^n))` is cofinal in `ε₀`: together with `tower_lt_epsilon`,
`sup_n o((0,0,1^n)) = ε₀`. -/
theorem tower_cof_epsilon (β : Ordinal.{0}) (hβ : β < ε₀) : ∃ n, β < 2 + vs (tower n) := by
  obtain ⟨n, hn⟩ := lt_epsilon_zero.1 hβ
  exact ⟨n, lt_of_lt_of_le hn ((iterate_le_vs_tower n).trans le_add_self)⟩

end Googology.Notation.SSOSS

/-
The chain `cC` follows `lamChain` of koteitan, bms-elem-pattern, `lean/Pattern/Chain.lean`
(https://github.com/koteitan/bms-elem-pattern, CC BY-SA 4.0; released here under Apache-2.0 as well by the same author). Changes: ported to
Lean 4.33.1; `sat_abs`, `top_abs` and `chain_R` are new and replace `lab_lam`.
Taken from koteitan, 1y-wo-por, `Por/Chain.lean` (https://github.com/koteitan/1y-wo-por,
revision db86f2d13c2e18a8e2c2fae5e083d00fc4d48a78, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`.
-/
import Googology.Notation.Y.WellOrder.Por.Closure
import Googology.Notation.Y.WellOrder.OneY.RootIndexed.Representation

/-!
# The chain and initial representations (obligation O7)

At a good `α < ω₁`, the top predicates of height `α` agree with those of `ω₁`
below `α` (`top_abs`). The proof is an induction on `(layer, index)`.

The chain `cC 0 < cC 1 < ⋯` is made of closure points, so all of them are good.
Any two members are related at every layer and every root index up to the
smaller one (`chain_R`). So the chain represents every finite diagram
(`initial_all`), which is stronger than obligation O7.
-/

open Classical Cardinal Ordinal

namespace Por

open OneY.RootIndexed (Diagram Representation)

/-- One step of the absoluteness induction. -/
theorem sat_abs {α : Ord} (hα : Good α) {j : ℕ} {ζ : Ord}
    (ih : ∀ q : ℕ × Ord, Prod.Lex (· < ·) (· < ·) q (j, ζ) → q.2 < α →
      ∀ x < α, (R q.1 q.2 x α ↔ R q.1 q.2 x Om))
    {m n : ℕ} {D : Set (Diag m n)} {bb r : ℕ} {S : Set ℕ} {p : ℕ → Ord}
    (hn : n ≤ r + bb) (hp : ∀ i < r, p i < α) (hS : ∀ s ∈ S, s < r ∧ p s < ζ) :
    Sat relR (topR α) (allowL j S) α m n D bb r p ↔
      Sat relR (topR Om) (allowL j S) Om m n D bb r p := by
  have h1 : Sat relR (topR α) (allowL j S) α m n D bb r p ↔
      Sat relR (topR Om) (allowL j S) α m n D bb r p := by
    refine sat_congr fun y hy => diagM_congr (fun _ _ _ _ _ _ _ _ => Iff.rfl) ?_
    intro i _ a ha b hb hallow
    have hva := cat_bound hn hp hy a ha
    have hvb := cat_bound hn hp hy b hb
    rcases hallow with hi | ⟨rfl, haS⟩
    · exact ih (i, _) (Prod.Lex.left _ _ hi) hva _ hvb
    · obtain ⟨har, hpa⟩ := hS a haS
      have hva' : cat r p y a < ζ := by rw [cat_left har]; exact hpa
      exact ih (i, _) (Prod.Lex.right _ hva') hva _ hvb
  rw [h1]
  exact sat_mask.trans ((hα m n _ bb r p hn hp).trans sat_mask.symm)

/-- Absoluteness of the top predicates at a good `α`: `Top^α = Top^{ω₁}` below `α`. -/
theorem top_abs {α : Ord} (hα : Good α) (hαΩ : α < Om) (q : ℕ × Ord) :
    q.2 < α → ∀ x < α, (R q.1 q.2 x α ↔ R q.1 q.2 x Om) := by
  refine (WellFounded.prod_lex (wellFounded_lt (α := ℕ)) (wellFounded_lt (α := Ord))).induction
    (C := fun q : ℕ × Ord => q.2 < α → ∀ x < α, (R q.1 q.2 x α ↔ R q.1 q.2 x Om)) q ?_
  rintro ⟨j, ζ⟩ ih _ x hx
  rw [R_iff, R_iff]
  refine and_congr_right fun _ => ⟨fun ⟨_, e⟩ => ⟨hx.trans hαΩ, ?_⟩, fun ⟨_, e⟩ => ⟨hx, ?_⟩⟩
  · intro m n D bb r S p hn hp hS
    rw [← sat_abs hα ih hn (fun i hi => (hp i hi).trans hx) hS]
    exact e m n D bb r S p hn hp hS
  · intro m n D bb r S p hn hp hS
    rw [sat_abs hα ih hn (fun i hi => (hp i hi).trans hx) hS]
    exact e m n D bb r S p hn hp hS

/-- `lam 0 < lam (lam 0) < ⋯`, all good. -/
noncomputable def cC : ℕ → Ord
  | 0 => lam 0
  | t + 1 => lam (cC t)

theorem cC_lt : ∀ t, cC t < Om
  | 0 => lam_lt om_pos
  | t + 1 => lam_lt (cC_lt t)

theorem cC_strictMono : StrictMono cC :=
  strictMono_nat_of_lt_succ fun t => lt_lam (cC t)

theorem cC_good : ∀ t, Good (cC t)
  | 0 => lam_good om_pos
  | t + 1 => lam_good (cC_lt t)

/-- Members of the chain are related at every layer and every root index `η ≤` the smaller. -/
theorem chain_R {i j : ℕ} (hij : i < j) (k : ℕ) {η : Ord} (hη : η ≤ cC i) :
    R k η (cC i) (cC j) := by
  have hlt : cC i < cC j := cC_strictMono hij
  refine R_iff.mpr ⟨hη, hlt, ?_⟩
  intro m n D bb r S p hn hp _
  have hA : ∀ {γ : Ord}, Good γ → γ < Om → ∀ {q : ℕ → Ord}, (∀ i < r, q i < γ) →
      (Sat relR (topR γ) (allowL k S) γ m n D bb r q ↔
        Sat relR (topR Om) full Om m n (maskD (allowL k S) ⁻¹' D) bb r q) := by
    intro γ hγ hγΩ q hq
    rw [← hγ m n _ bb r q hn hq, ← sat_mask]
    refine sat_congr fun y hy => diagM_congr (fun _ _ _ _ _ _ _ _ => Iff.rfl) ?_
    intro i' _ a ha b hb _
    exact top_abs hγ hγΩ (i', _) (cat_bound hn hq hy a ha) _ (cat_bound hn hq hy b hb)
  rw [hA (cC_good i) (cC_lt i) hp, hA (cC_good j) (cC_lt j) fun i' hi' => (hp i' hi').trans hlt]

/-- O7 (stronger): every finite diagram has a representation. -/
theorem initial_all (G : Diagram) :
    ∃ f, Representation (α := Ord) (· < ·) (fun _ => True) R G f := by
  refine ⟨cC, ⟨fun _ _ => trivial, fun i j hij _ => cC_strictMono hij, fun e he => ?_⟩⟩
  obtain ⟨h1, h2, _⟩ := G.valid e he
  exact chain_R h2 e.layer (cC_strictMono.monotone h1)

end Por

import Googology.Trans.PoR.InaccPsi.R2.BrLs2

/-!
# LOW-STEP, part 3: the map `E` over a parameter base `σ`, with the `A`-clause

For a base `σ` and `k_A` (the number of summands of `A`), the map of the paper proof of Theorem LOW-STEP:
* `E(t) = t` (a parameter) when `t < σ`;
* `E(a + b)`, `E(Ωₖ)`, `E(φ(x, y))`, `E(ψ_{Ω_{k+1}}(a))` (`k ≥ 1`) as for `τ = 1`;
* the `A`-clause: `E(ψ_{Ω₁}(A + ζ)) = ϑ̄₀(G(pmax ζ) + E ζ)`, `ζ = dropT k_A c` for the argument `c`, with
  `G(none) = P₁` and `G(ψ_{Ω₂}(d)) = ϑ̄_{M+1}(Ω_{M+1}·2 + E d)`, `M = max(lvl d, 1)`.
`ELf` is defined by recursion on a fuel bound (the recursion enters `dropT k_A c` and the argument of
`pmax`, which are not immediate subterms); `EL t = ELf (size t) t`, and `EL_*` are its equations.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Br

open Ordinal Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq Tm

variable (S : InaccSeq.{0}) (σ : Ordinal.{0}) (kA : ℕ)

/-- `G` from the recursive map `f`. -/
noncomputable def GcT (f : Term → Tm) : Option Term → Tm
  | some (.psiS _ d) => th (max (lvl (Term.val S d)) 1 + 1) (gFarg σ (max (lvl (Term.val S d)) 1) (f d))
  | _ => Pk 1

open Classical in
/-- `E` with fuel. -/
noncomputable def ELf : ℕ → Term → Tm
  | 0, _ => par 0
  | n + 1, t =>
    if Term.val S t < σ then par (Term.val S t) else
    match t with
    | .add a b => plus σ (ELf n a) (ELf n b)
    | .phi a b => th (lvl (Term.val S (.phi a b)))
        (plus σ (th (lvl (Term.val S (.phi a b)) + 1) (ELf n a)) (ELf n b))
    | .om b => Omk (natOf (Term.val S b))
    | .psiS s c =>
        if natOf (Term.val S s) = 0 then
          th 0 (plus σ (GcT S σ (ELf n) (pmax S (dropT kA c))) (ELf n (dropT kA c)))
        else th (natOf (Term.val S s)) (plus σ (Pk (natOf (Term.val S s))) (gFc σ (ELf n c)))
    | _ => par 0

/-- `E`. -/
noncomputable def EL (t : Term) : Tm := ELf S σ kA t.size t

variable {S σ kA}

/-! ## Sizes -/

theorem topAtoms_size : ∀ {t a : Term}, a ∈ topAtoms t → a.size ≤ t.size
  | .zero, a, h => by simp [topAtoms] at h
  | .add x y, a, h => by
    simp only [topAtoms, List.mem_append] at h
    rcases h with h | h
    · have := topAtoms_size h; simp [Term.size]; omega
    · have := topAtoms_size h; simp [Term.size]; omega
  | .phi x y, a, h => by
    simp only [topAtoms, List.mem_append] at h
    rcases h with h | h
    · have := topAtoms_size h; simp [Term.size]; omega
    · have := topAtoms_size h; simp [Term.size]; omega
  | .om _, a, h => by simp [topAtoms] at h; subst h; exact le_rfl
  | .psiS _ _, a, h => by simp [topAtoms] at h; subst h; exact le_rfl
  | .inacc _, a, h => by simp [topAtoms] at h; subst h; exact le_rfl
  | .inaccW, a, h => by simp [topAtoms] at h; subst h; exact le_rfl
  | .psiI _ _, a, h => by simp [topAtoms] at h; subst h; exact le_rfl

theorem pmax_mem {ζ u : Term} (h : pmax S ζ = some u) : u ∈ topAtoms ζ ∧ IsP2 S u :=
  ⟨((pmaxL_spec (S := S) (topAtoms ζ)).2 u h).1, ((pmaxL_spec (S := S) (topAtoms ζ)).2 u h).2.1⟩

theorem pmax_arg_size {ζ s' d : Term} (h : pmax S ζ = some (.psiS s' d)) : d.size < ζ.size := by
  have := topAtoms_size (pmax_mem h).1
  simp [Term.size] at this; omega

/-! ## Fuel independence -/

theorem GcT_congr {f g : Term → Tm} {o : Option Term}
    (h : ∀ s' d, o = some (.psiS s' d) → f d = g d) : GcT S σ f o = GcT S σ g o := by
  rcases o with _ | u
  · rfl
  · cases u <;> simp only [GcT]
    rw [h _ _ rfl]

theorem ELf_fuel : ∀ (n : ℕ) (t : Term) (n' : ℕ), t.size ≤ n → t.size ≤ n' →
    ELf S σ kA n t = ELf S σ kA n' t := by
  intro n
  induction n with
  | zero => intro t n' h; exact absurd (Term.size_pos t) (by omega)
  | succ n ih =>
    intro t n' h h'
    obtain ⟨n'', rfl⟩ : ∃ n'', n' = n'' + 1 := ⟨n' - 1, by have := Term.size_pos t; omega⟩
    simp only [ELf]
    split_ifs with hv
    · rfl
    · cases t with
      | add a b =>
        simp only [Term.size] at h h'
        dsimp only
        rw [ih a n'' (by omega) (by omega), ih b n'' (by omega) (by omega)]
      | phi a b =>
        simp only [Term.size] at h h'
        dsimp only
        rw [ih a n'' (by omega) (by omega), ih b n'' (by omega) (by omega)]
      | psiS s c =>
        have hds := dropT_size kA c
        simp only [Term.size] at h h'
        dsimp only
        split_ifs
        · rw [ih (dropT kA c) n'' (by omega) (by omega)]
          congr 2
          exact GcT_congr fun s' d hp => by
            have := pmax_arg_size hp
            exact ih d n'' (by omega) (by omega)
        · rw [ih c n'' (by omega) (by omega)]
      | _ => rfl

theorem EL_eq (t : Term) (n : ℕ) (h : t.size ≤ n) : EL S σ kA t = ELf S σ kA n t :=
  ELf_fuel _ t n le_rfl h

/-! ## The equations of `E` -/

theorem EL_par {t : Term} (h : Term.val S t < σ) : EL S σ kA t = par (Term.val S t) := by
  unfold EL
  obtain ⟨n, hn⟩ : ∃ n, t.size = n + 1 := ⟨t.size - 1, by have := Term.size_pos t; omega⟩
  rw [hn]; simp only [ELf, if_pos h]

theorem EL_add {a b : Term} (h : ¬ Term.val S (.add a b) < σ) :
    EL S σ kA (.add a b) = plus σ (EL S σ kA a) (EL S σ kA b) := by
  unfold EL
  simp only [Term.size, ELf, if_neg h]
  rw [← EL_eq a _ (by omega), ← EL_eq b _ (by omega)]; rfl

theorem EL_phi {a b : Term} (h : ¬ Term.val S (.phi a b) < σ) :
    EL S σ kA (.phi a b) = th (lvl (Term.val S (.phi a b)))
      (plus σ (th (lvl (Term.val S (.phi a b)) + 1) (EL S σ kA a)) (EL S σ kA b)) := by
  unfold EL
  simp only [Term.size, ELf, if_neg h]
  rw [← EL_eq a _ (by omega), ← EL_eq b _ (by omega)]; rfl

theorem EL_om {b : Term} (h : ¬ Term.val S (.om b) < σ) :
    EL S σ kA (.om b) = Omk (natOf (Term.val S b)) := by
  unfold EL
  simp only [Term.size, ELf, if_neg h]

theorem GcT_EL {ζ : Term} (n : ℕ) (hn : ζ.size ≤ n) :
    GcT S σ (ELf S σ kA n) (pmax S ζ) = GcT S σ (EL S σ kA) (pmax S ζ) :=
  GcT_congr fun s' d hp => (EL_eq d n (by have := pmax_arg_size hp; omega)).symm

/-- **The `A`-clause.** -/
theorem EL_psi0 {s c : Term} (h : ¬ Term.val S (.psiS s c) < σ) (hs : natOf (Term.val S s) = 0) :
    EL S σ kA (.psiS s c) = th 0 (plus σ (GcT S σ (EL S σ kA) (pmax S (dropT kA c)))
      (EL S σ kA (dropT kA c))) := by
  unfold EL
  have hds := dropT_size kA c
  simp only [Term.size, ELf, if_neg h, if_pos hs]
  rw [GcT_EL _ (by omega), ← EL_eq (dropT kA c) _ (by omega)]
  rfl

theorem EL_psiS {s c : Term} (h : ¬ Term.val S (.psiS s c) < σ) (hs : natOf (Term.val S s) ≠ 0) :
    EL S σ kA (.psiS s c) = th (natOf (Term.val S s))
      (plus σ (Pk (natOf (Term.val S s))) (gFc σ (EL S σ kA c))) := by
  unfold EL
  simp only [Term.size, ELf, if_neg h, if_neg hs]
  rw [← EL_eq c _ (by omega)]
  rfl

theorem EL_zero (hσ : 0 < σ) : EL S σ kA .zero = par 0 := by
  rw [EL_par (by simp only [Term.val]; exact hσ)]; rfl

theorem GcT_some {f : Term → Tm} {s' d : Term} :
    GcT S σ f (some (.psiS s' d)) =
      th (max (lvl (Term.val S d)) 1 + 1) (gFarg σ (max (lvl (Term.val S d)) 1) (f d)) := rfl

theorem GcT_none {f : Term → Tm} : GcT S σ f none = Pk 1 := rfl

end Googology.Trans.PoR.InaccPsi.R2.Br

import Googology.Notation.ExBuchholz.FS

/-!
# Towards the closure of `OT` under the fundamental sequence

`step_lt` says one expansion step decreases.  The last thing `exb.WF` needs is
that it keeps a term standard — Buchholz's Lemma 3.3 for the extended system.

Buchholz proves 3.3 through a relation written `b ⊲_z a`, which says that `b`
is below `a` and that everything `G` sees in `b` is bounded by what it sees in
any `c` between them, together with `z`.  The chain is

| | statement | here |
|---|---|---|
| 3.4 | `b ⊲_z a`, `G_u a < a`, `G_u z < b` ⟹ `G_u b < b` | **done** |
| 3.5 | `b₀ ⊲_z b` ⟹ `a + b₀ ⊲_z a + b`, `ψ_u(b₀) ⊲_z ψ_u(b)`, `ψ_{b₀}(0) ⊲_z ψ_b(0)` | **done** |
| 3.2(b) | on a term-indexed domain, `z₁ < z₂` ⟹ `a[z₁] < a[z₂]` | **done** (`fs_mono`) |
| 3.6 | `z ∈ dom a` ⟹ `a[z] ⊲_z a` | **done**, from 3.3 |
| 3.3 | `a, z ∈ OT`, `z ∈ dom a` ⟹ `a[z] ∈ OT` | not yet |

3.4 is the one that does the work: it turns "bounded relative to `z`" into the
standard-form condition outright.  Buchholz argues by taking a subterm of `b`
of minimal length that violates the condition; here it is an induction on
`size`, whose conclusion is a disjunction — either the goal already holds, or
the condition holds at this subterm — which avoids needing a choice of minimal
element.

Each half of 3.5 rests on a decomposition lemma saying what a term strictly
between two others has to look like: `addT_between` for sums, `psi_between`
for the argument of a collapse and `psi_sub_between` for its subscript.

`Trian_fs` is 3.6, and it takes 3.3 — `OTFS` here — as its only hypothesis.
Its proof is an induction on `size`, one case per branch of `fs`, and six of
the seven branches close from 3.5 and the small lemmas `Trian_nil`,
`Trian_self`, `Trian.of_nil` and `Trian.repeatPrin`.  The seventh is
Buchholz's case 4, where `dom X₂ = ψ_Z(0)` is not below `ψ_{X₁}(X₂)` and the
index has to be rebuilt from `Z`.  Expanding at the numeral `n` then runs a
tower

```
W₀ = ψ_{Z[0]}(0)        W_{i+1} = ψ_{Z[0]}(X₂[W_i])
(ψ_{X₁}(X₂))[n̲] = ψ_{X₁}(X₂[W_n])
```

`FS.lean` defines that tower as `tower`, identifies it with the branch in
`fs_numeral`, and shows it climbs (`tower_lt`, `tower_val_lt`) and stays an
admissible index (`tower_lt_dom`).  Climbing needs 3.2(b), which is `fs_mono`
there.

`Trian_case4` proves the branch from a bound on the tower.  `tower_G_le`
reduces that to a bound on `Z[0]`, `sub_G_le` reduces it further to a bound on
`Z` itself, and `subBound_of_OTFS` derives that from 3.3:

```
X[ψ_{Z[0]}(0)] ≤ c ≤ X  ⟹  G_u(Z) ≼ G_u(c) ∪ {0}     (Z = subOf (dom X))
```

That last step is an induction on `X` with one case per branch of `dom`, and
3.3 enters in exactly one of them: where `dom X = X = ψ_A(0)` with `A` a
successor.  There `G_u(A) = G_u(A[0]) ++ G_u(1)` has to be bounded against an
empty list when `u` is large, and `G_eq_nil_of_le` gives that only for a
standard `A[0]`.

Two shapes had to be got right, and `test/ExBuchholzCheck.lean` carries a term
for each.  The bound has to be relative to `c`: Buchholz's own invariant is
the absolute `G_u(W_i) < X₂[W_i]`, which works in his system because his
subscripts are numbers and `G` never enters them, and which is false once they
are terms.  And the index has to be `ψ_{Z[0]}(0)` rather than an arbitrary
`W < dom X`.

So 3.6 rests on 3.3 and on nothing else.

3.3 itself is `OTFS_aux`, an induction on `size` that carries 3.6 with it.
Each branch of `fs` is settled by `OT_cons_fs`, `OT_psi_nil`, `OT_psi_fs` — 3.4
in the shape 3.3 needs — and `OT_repeatPrin`, with `G_eq_nil_of_lt_psi` and
`G_numeral_eq_nil` to show that `G` at the level of the collapse sees nothing
in the index.  One branch is left: Buchholz's case 4, where the index is a
rung of the tower.  What that branch needs is his second tower invariant,

```
OT W_i   and   ∀ x ∈ G_A(W_i), x < B[W_i]
```

for `ψ_A(B)` in the configuration of case 4, at the level of the collapse.
The level matters: at level `0` the same statement is false, and
`test/ExBuchholzCheck.lean` carries the term that shows it.

`towerOT_of_Bachmann` proves that invariant by induction on the rung, from
one statement about `B` alone, `Bachmann`:

```
∀ x ∈ G_A(B), x < B[ψ_{Z[0]}(0)]
```

The fundamental sequence of `B` at the tower's first index overshoots
everything `G` sees in `B` at the level of the collapse.  That is the
Bachmann property, and it is the only thing the library still assumes.

`System.lean` carries that through to the end: `exbOT` is the expansion system
restricted to the countable standard forms, and `exbOT_wf` and
`exbOT_terminates` are proved from `Bachmann` and nothing else.

The route to `Bachmann` itself is an induction on `B`, one case per branch of
`dom`, and the cases are not uniform.  Writing `P(V)` for `ψ_V(0)`:

| branch of `dom B` | what the case needs |
|---|---|
| `B = p + t` | the head by a size argument; the tail by the same statement at `t`, with `p` kept in front |
| `B = ψ_a(0)`, `dom a = 1` | `a` is a successor, so `le_pred_of_lt` and a size argument |
| `B = ψ_a(0)`, `dom a ∉ {0,1}` | the same statement at `a`, but stated for `P` — hypothesis `G_u(a) < P(a)`, conclusion `G_u(a) < P(a[W])` |
| `B = ψ_a(b)`, `dom b < B` | the same statement at `b`, and the closure of `G` under its own members |

So the induction has to carry the statement in two shapes, both with a prefix
in front: the plain one and the one for `P`.  `bach_sum` is the sum branch of
the plain shape, proved: the head lands by a size argument through
`lt_of_size_lt_addT`, and the tail by the same statement at `t` with the head
appended to the prefix.

Of the three principal branches, `ψ_a(0)` with `dom a = 1` is `bach_succ`,
proved: it splits on where `x` sits relative to the prefix — below it, equal
to it, or above it — and the third case closes through `le_pred_of_lt` and a
size argument.

The other two reduce, but to statements in other contexts.  `ψ_a(0)` with
`dom a ∉ {0,1}` is the `P` shape at `a` under the same prefix, because
`G_u(ψ_a(0))` is `{0}` together with `G_u(a)` and the conclusion is about
`ψ_{a[W]}(0)`.  `ψ_a(b)` with `dom b < V` splits three ways: `G_u(a)` by a
size argument, `G_u(b)` by the shape whose context is `p + ψ_a(−)`, and the
argument `b` itself by the plain shape at `b` **at level `a`**, whose
hypothesis is exactly `OT_G_lt` on `OT (ψ_a(b))`.  That last step is why the
induction has to quantify over the level rather than fix it.

The contexts do not close up.  The sum branch of the `P` shape asks for
`ψ_{p + ψ_α(β) + (−)}(0)`, and so on, so the induction wants a general context
rather than the three shapes.  Finding the right closure condition on contexts
is what is left.

The prefix cannot be dropped. For `V = ψ_Ω(0) + ψ_1(ψ_Ω(0))`, which is
standard with a term-indexed domain, `G_1` sees `ψ_Ω(0)` in the tail — the
head of `V` itself. So neither "below the head" nor "below the tail" holds
there, while the conclusion does. `test/ExBuchholzCheck.lean` carries that
term, and checks all three shapes.
-/

namespace Googology.Notation.ExBuchholz.Term

/-- Concatenation of terms, which is `+` on the ordinals they name. -/
def addT : Term → Term → Term
  | nil, y => y
  | cons a b t, y => cons a b (addT t y)

@[simp] theorem addT_nil_left (y : Term) : addT nil y = y := rfl
@[simp] theorem addT_cons (a b t y : Term) :
    addT (cons a b t) y = cons a b (addT t y) := rfl
@[simp] theorem addT_nil_right : ∀ x : Term, addT x nil = x
  | nil => rfl
  | cons a b t => by rw [addT_cons, addT_nil_right t]

theorem cons_eq_addT (a b t : Term) : cons a b t = addT (psi a b) t := rfl

theorem G_addT (u x y : Term) : G u (addT x y) = G u x ++ G u y := by
  induction x with
  | nil => simp [G]
  | cons a b t _ _ iht =>
    rw [addT_cons, G_cons, G_cons, iht, List.append_assoc]

/-- `G° u t` is `G u t` with `0` thrown in, as Buchholz writes it. -/
def G0 (u t : Term) : List Term := nil :: G u t

/-- `M ≼ M'`: every member of `M` is at most some member of `M'`. -/
def listLe (M M' : List Term) : Prop := ∀ x ∈ M, ∃ y ∈ M', x ≤ y

theorem listLe_refl (M : List Term) : listLe M M :=
  fun x hx => ⟨x, hx, le_refl x⟩

theorem listLe_append_left {M M' N : List Term} (h : listLe M M') :
    listLe M (M' ++ N) :=
  fun x hx => let ⟨y, hy, hle⟩ := h x hx; ⟨y, List.mem_append_left _ hy, hle⟩

theorem listLe_append_right {M N N' : List Term} (h : listLe M N') :
    listLe M (N ++ N') :=
  fun x hx => let ⟨y, hy, hle⟩ := h x hx; ⟨y, List.mem_append_right _ hy, hle⟩

theorem listLe_of_append {M M' N : List Term} (h₁ : listLe M N) (h₂ : listLe M' N) :
    listLe (M ++ M') N := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact h₁ x hx
  · exact h₂ x hx

/-- Buchholz's `b ⊲_z a`: `b` is below `a`, and everything `G` sees in `b` is
bounded by what it sees in any `c` between them, together with `z`. -/
def Trian (z b a : Term) : Prop :=
  b < a ∧ ∀ u c : Term, b < c → c ≤ a → listLe (G u b) (G u c ++ G0 u z)

theorem Trian.lt {z b a : Term} (h : Trian z b a) : b < a := h.1

theorem addT_lt (a : Term) {x y : Term} (h : x < y) : addT a x < addT a y := by
  induction a with
  | nil => exact h
  | cons p q a' _ _ iha =>
    exact cons_lt_cons_iff.mpr (Or.inr ⟨rfl, iha⟩)

/-- Anything strictly between `a + b₀` and `a + b` is `a + c₀` for some `c₀`
strictly between. -/
theorem addT_between : ∀ a : Term, ∀ {b₀ b c : Term}, addT a b₀ < c → c ≤ addT a b →
    ∃ c₀, c = addT a c₀ ∧ b₀ < c₀ ∧ c₀ ≤ b := by
  intro a
  induction a with
  | nil => intro b₀ b c h₁ h₂; exact ⟨c, rfl, h₁, h₂⟩
  | cons p q a' _ _ iha =>
    intro b₀ b c h₁ h₂
    cases c with
    | nil => exact absurd h₁ (not_lt_nil _)
    | cons r s c' =>
      rcases cons_lt_cons_iff.mp h₁ with hlt | ⟨heq, hrest⟩
      · exfalso
        rcases le_iff_lt_or_eq.mp h₂ with h | h
        · rcases cons_lt_cons_iff.mp h with h' | ⟨h', _⟩
          · exact lt_irrefl _ (lt_trans hlt h')
          · rw [h'] at hlt; exact lt_irrefl _ hlt
        · injection h with h1 h2 _
          rw [h1, h2] at hlt
          exact lt_irrefl _ hlt
      · injection heq with e1 e2 _
        subst e1; subst e2
        have hc' : c' ≤ addT a' b := by
          rcases le_iff_lt_or_eq.mp h₂ with h | h
          · rcases cons_lt_cons_iff.mp h with h' | ⟨_, h'⟩
            · exact absurd h' (lt_irrefl _)
            · exact le_of_lt h'
          · injection h with _ _ e3
            exact e3 ▸ le_refl _
        obtain ⟨c₀, rfl, hb, hb'⟩ := iha hrest hc'
        exact ⟨c₀, rfl, hb, hb'⟩

/-- **Buchholz 3.5, the sum half.** -/
theorem Trian.addT_left (a : Term) {z b₀ b : Term} (h : Trian z b₀ b) :
    Trian z (addT a b₀) (addT a b) := by
  refine ⟨addT_lt a h.1, ?_⟩
  intro u c hlt hle
  obtain ⟨c₀, rfl, h1, h2⟩ := addT_between a hlt hle
  rw [G_addT, G_addT]
  refine listLe_of_append (listLe_append_left (listLe_append_left (listLe_refl _))) ?_
  intro x hx
  obtain ⟨y, hy, hle'⟩ := h.2 u c₀ h1 h2 x hx
  rcases List.mem_append.mp hy with hy | hy
  · exact ⟨y, List.mem_append_left _ (List.mem_append_right _ hy), hle'⟩
  · exact ⟨y, List.mem_append_right _ hy, hle'⟩

/-- Anything strictly between `ψ_u(b₀)` and `ψ_u(b)` has `ψ_u` at its head,
with an argument between. -/
theorem psi_between {u b₀ b c : Term} (h₁ : psi u b₀ < c) (h₂ : c ≤ psi u b) :
    ∃ c₀ c₁, c = cons u c₀ c₁ ∧ b₀ ≤ c₀ ∧ c₀ ≤ b := by
  cases c with
  | nil => exact absurd h₁ (not_lt_nil _)
  | cons r s c₁ =>
    have hle_rs : psi r s ≤ psi u b := by
      rcases le_iff_lt_or_eq.mp h₂ with hB | hB
      · rcases cons_lt_cons_iff.mp hB with hB' | ⟨_, hB''⟩
        · exact le_of_lt hB'
        · exact absurd hB'' (not_lt_nil _)
      · injection hB with e1 e2 _
        exact e1 ▸ e2 ▸ le_refl _
    rcases cons_lt_cons_iff.mp h₁ with hA | ⟨hA, _⟩
    · rcases psi_lt_psi_iff.mp hA with hlt1 | ⟨e1, hlt1⟩
      · exfalso
        rcases le_iff_lt_or_eq.mp hle_rs with h' | h'
        · rcases psi_lt_psi_iff.mp h' with h'' | ⟨e', _⟩
          · exact lt_irrefl u (lt_trans hlt1 h'')
          · exact lt_irrefl u (e' ▸ hlt1)
        · injection h' with e' _ _
          exact lt_irrefl u (e' ▸ hlt1)
      · subst e1
        refine ⟨s, c₁, rfl, le_of_lt hlt1, ?_⟩
        rcases le_iff_lt_or_eq.mp hle_rs with h' | h'
        · rcases psi_lt_psi_iff.mp h' with h'' | ⟨_, h''⟩
          · exact absurd h'' (lt_irrefl u)
          · exact le_of_lt h''
        · injection h' with _ e2 _
          exact e2 ▸ le_refl _
    · injection hA with e1 e2 _
      subst e1
      refine ⟨s, c₁, rfl, e2 ▸ le_refl _, ?_⟩
      rcases le_iff_lt_or_eq.mp hle_rs with h' | h'
      · rcases psi_lt_psi_iff.mp h' with h'' | ⟨_, h''⟩
        · exact absurd h'' (lt_irrefl u)
        · exact le_of_lt h''
      · injection h' with _ e2 _
        exact e2 ▸ le_refl _

theorem G_psi_of_le {v u b : Term} (h : v ≤ u) :
    G v (psi u b) = b :: (G v u ++ G v b) := by
  rw [psi, G_cons, if_pos h]
  simp [G]

theorem G_psi_of_not_le {v u b : Term} (h : ¬ v ≤ u) : G v (psi u b) = [] := by
  rw [psi, G_cons, if_neg h]
  simp [G]

/-- **Buchholz 3.5, the collapse half.** -/
theorem Trian.psi_left (u : Term) {z b₀ b : Term} (h : Trian z b₀ b) :
    Trian z (psi u b₀) (psi u b) := by
  refine ⟨psi_lt_psi_iff.mpr (Or.inr ⟨rfl, h.1⟩), ?_⟩
  intro v c hlt hle
  obtain ⟨c₀, c₁, rfl, hb0, hb1⟩ := psi_between hlt hle
  by_cases hvu : v ≤ u
  · rw [G_psi_of_le hvu, G_cons, if_pos hvu]
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨c₀, List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_self ..)), hb0⟩
    rcases List.mem_append.mp hx with hx | hx
    · exact ⟨x, List.mem_append_left _ (List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_append_left _ hx))), le_refl x⟩
    · rcases le_iff_lt_or_eq.mp hb0 with hb | rfl
      · obtain ⟨y, hy, hle'⟩ := h.2 v c₀ hb hb1 x hx
        rcases List.mem_append.mp hy with hy | hy
        · exact ⟨y, List.mem_append_left _ (List.mem_append_left _
            (List.mem_cons_of_mem _ (List.mem_append_right _ hy))), hle'⟩
        · exact ⟨y, List.mem_append_right _ hy, hle'⟩
      · exact ⟨x, List.mem_append_left _ (List.mem_append_left _
          (List.mem_cons_of_mem _ (List.mem_append_right _ hx))), le_refl x⟩
  · rw [G_psi_of_not_le hvu]
    intro x hx; cases hx

theorem listLe_trans {M N P : List Term} (h₁ : listLe M N) (h₂ : listLe N P) :
    listLe M P := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := h₁ x hx
  obtain ⟨w, hw, hyw⟩ := h₂ y hy
  exact ⟨w, hw, le_trans hxy hyw⟩

theorem listLe_append_congr {M M' N N' : List Term}
    (h₁ : listLe M M') (h₂ : listLe N N') : listLe (M ++ N) (M' ++ N') := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨y, hy, hxy⟩ := h₁ x hx
    exact ⟨y, List.mem_append_left _ hy, hxy⟩
  · obtain ⟨y, hy, hxy⟩ := h₂ x hx
    exact ⟨y, List.mem_append_right _ hy, hxy⟩

/-- `⊲` may be re-based on a larger index, as long as `G°` grows with it. -/
theorem Trian.mono_z {z z' b a : Term} (h : Trian z b a)
    (hz : ∀ u, listLe (G0 u z) (G0 u z')) : Trian z' b a :=
  ⟨h.1, fun u c hc hca =>
    listLe_trans (h.2 u c hc hca)
      (listLe_append_congr (listLe_refl _) (hz u))⟩

/-! ## Buchholz 3.4 -/

theorem G0_lt {u z b : Term} (hz : ∀ x ∈ G u z, x < b) (hb : nil < b) :
    ∀ x ∈ G0 u z, x < b := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hb
  · exact hz x hx

/-- Step 1 of Buchholz 3.4: what `G` sees in `b` is bounded by `a`. -/
theorem G_lt_of_Trian {u z b a : Term} (hba : Trian z b a)
    (ha : ∀ x ∈ G u a, x < a) (hz : ∀ x ∈ G u z, x < b) :
    ∀ x ∈ G u b, x < a := by
  have hane : nil < a := by
    cases a with
    | nil => exact absurd hba.1 (not_lt_nil _)
    | cons _ _ _ => exact nil_lt_cons _ _ _
  have hbne : nil < b ∨ b = nil := by
    cases b with
    | nil => exact Or.inr rfl
    | cons _ _ _ => exact Or.inl (nil_lt_cons _ _ _)
  intro x hx
  obtain ⟨y, hy, hle⟩ := hba.2 u a hba.1 (le_refl a) x hx
  rcases List.mem_append.mp hy with hy | hy
  · exact lt_of_le_of_lt' hle (ha y hy)
  · rcases List.mem_cons.mp hy with rfl | hy
    · exact lt_of_le_of_lt' hle hane
    · rcases hbne with h | rfl
      · exact lt_of_le_of_lt' hle (lt_trans (hz y hy) hba.1)
      · exact absurd (hz y hy) (not_lt_nil _)

/-- **Buchholz 3.4.**  The relation `⊲` upgrades to the standard-form
condition outright. -/
theorem Trian.G_lt {u z b a : Term} (hba : Trian z b a)
    (ha : ∀ x ∈ G u a, x < a) (hz : ∀ x ∈ G u z, x < b) :
    ∀ x ∈ G u b, x < b := by
  have hstep1 := G_lt_of_Trian hba ha hz
  have key : ∀ n : Nat, ∀ d : Term, size d ≤ n → (∀ y ∈ G u d, y < a) →
      (∀ y ∈ G u b, y < b) ∨ (∀ y ∈ G u d, y < b) := by
    intro n
    induction n with
    | zero =>
      intro d hsz _
      cases d with
      | nil => exact Or.inr (fun y hy => absurd hy (List.not_mem_nil))
      | cons _ _ _ => simp only [size_cons] at hsz; omega
    | succ n ih =>
      intro d hsz hda
      cases d with
      | nil => exact Or.inr (fun y hy => absurd hy (List.not_mem_nil))
      | cons v c t =>
        simp only [size_cons] at hsz
        have hsub : ∀ w, (∀ y ∈ G u w, y ∈ G u (cons v c t)) → ∀ y ∈ G u w, y < a :=
          fun w hw y hy => hda y (hw y hy)
        have hGt : ∀ y ∈ G u t, y ∈ G u (cons v c t) := by
          intro y hy; rw [G_cons]; exact List.mem_append_right _ hy
        rcases ih t (by omega) (hsub t hGt) with h | ht
        · exact Or.inl h
        by_cases huv : u ≤ v
        · have hGv : ∀ y ∈ G u v, y ∈ G u (cons v c t) := by
            intro y hy; rw [G_cons, if_pos huv]
            exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_append_left _ hy))
          have hGc : ∀ y ∈ G u c, y ∈ G u (cons v c t) := by
            intro y hy; rw [G_cons, if_pos huv]
            exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_append_right _ hy))
          rcases ih v (by omega) (hsub v hGv) with h | hv
          · exact Or.inl h
          rcases ih c (by omega) (hsub c hGc) with h | hc
          · exact Or.inl h
          have hcmem : c ∈ G u (cons v c t) := by
            rw [G_cons, if_pos huv]; exact List.mem_append_left _ (List.mem_cons_self ..)
          have hca : c < a := hda c hcmem
          have hbne : nil < b ∨ b = nil := by
            cases b with
            | nil => exact Or.inr rfl
            | cons _ _ _ => exact Or.inl (nil_lt_cons _ _ _)
          rcases lt_trichotomy c b with hcb | rfl | hbc
          · refine Or.inr ?_
            intro y hy
            rw [G_cons, if_pos huv] at hy
            rcases List.mem_append.mp hy with hy | hy
            · rcases List.mem_cons.mp hy with rfl | hy
              · exact hcb
              rcases List.mem_append.mp hy with hy | hy
              · exact hv y hy
              · exact hc y hy
            · exact ht y hy
          · exact Or.inl hc
          · refine Or.inl ?_
            intro y hy
            obtain ⟨w, hw, hle⟩ := hba.2 u c hbc (le_of_lt hca) y hy
            rcases List.mem_append.mp hw with hw | hw
            · exact lt_of_le_of_lt' hle (hc w hw)
            · rcases hbne with hb0 | rfl
              · exact lt_of_le_of_lt' hle (G0_lt hz hb0 w hw)
              · exact absurd hy (List.not_mem_nil)
        · refine Or.inr ?_
          intro y hy
          rw [G_cons, if_neg huv] at hy
          exact ht y (by simpa using hy)
  rcases key (size b) b (Nat.le_refl _) hstep1 with h | h <;> exact h

/-! ## The pieces 3.6 is assembled from

3.6 follows `fs` branch by branch, and each branch needs one of these.

| branch of `fs` | what it needs |
|---|---|
| `X = 1`, the step is `0` | `Trian_nil` |
| `X = ψ_u(0)` with `u` a successor, the step is the index | `Trian_self` |
| `dom X₂ = 1`, the step is a repeated collapse | `Trian.of_nil`, `Trian.repeatPrin`, `Trian.psi_left` |
| `dom X₂` an `ω`-limit or below `X`, the step is inside the argument | `Trian.psi_left` |
| `X` a sum, the step is in the last summand | `Trian.addT_left` |

The branch not covered is the one where the index has to be rebuilt from the
subscript of `dom X₂`; Buchholz's case 4 computes `G` there by hand.
-/

/-- `0 ⊲_z a` for any nonzero `a`: `G` sees nothing in `0`. -/
theorem Trian_nil {z a : Term} (h : nil < a) : Trian z nil a :=
  ⟨h, fun _ _ _ _ _ hx => absurd hx (List.not_mem_nil)⟩

/-- `z ⊲_z a` whenever `z < a`: what `G` sees in `z` is in `G° z` already. -/
theorem Trian_self {z a : Term} (h : z < a) : Trian z z a :=
  ⟨h, fun _ _ _ _ x hx =>
    ⟨x, List.mem_append_right _ (List.mem_cons_of_mem _ hx), le_refl x⟩⟩

/-- `⊲_0` is the strongest of the family: `G° 0` sits inside every `G° z`. -/
theorem Trian.of_nil {z b a : Term} (h : Trian nil b a) : Trian z b a := by
  refine ⟨h.1, fun u c hlt hle x hx => ?_⟩
  obtain ⟨y, hy, hle'⟩ := h.2 u c hlt hle x hx
  rcases List.mem_append.mp hy with hy | hy
  · exact ⟨y, List.mem_append_left _ hy, hle'⟩
  · rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨nil, List.mem_append_right _ (List.mem_cons_self ..), hle'⟩
    · exact absurd hy (List.not_mem_nil)

theorem G_repeatPrin (u A B : Term) :
    ∀ k, ∀ y ∈ G u (repeatPrin A B k), y ∈ G u (psi A B)
  | 0 => fun y hy => absurd hy (List.not_mem_nil)
  | k + 1 => by
      intro y hy
      rw [show repeatPrin A B (k+1) = cons A B (repeatPrin A B k) from rfl, G_cons] at hy
      rcases List.mem_append.mp hy with hy | hy
      · rw [psi, G_cons]; exact List.mem_append_left _ hy
      · exact G_repeatPrin u A B k y hy

theorem cons_le_cons {a b t u : Term} (h : t ≤ u) : cons a b t ≤ cons a b u := by
  rcases le_iff_lt_or_eq.mp h with h | rfl
  · exact le_of_lt (cons_lt_cons_iff.mpr (Or.inr ⟨rfl, h⟩))
  · exact le_refl _

theorem psi_le_repeatPrin (A B : Term) :
    ∀ k, 0 < k → psi A B ≤ repeatPrin A B k
  | 0, h => absurd h (Nat.lt_irrefl 0)
  | _ + 1, _ => cons_le_cons (nil_le _)

/-- A repeated collapse inherits `⊲` from one copy. -/
theorem Trian.repeatPrin {z A B a : Term} (h : Trian z (psi A B) a) :
    ∀ k, repeatPrin A B k < a → Trian z (repeatPrin A B k) a := by
  intro k hlt
  refine ⟨hlt, fun u c hc hca x hx => ?_⟩
  cases k with
  | zero => exact absurd hx (List.not_mem_nil)
  | succ k =>
    have hple : psi A B < c :=
      lt_of_le_of_lt' (psi_le_repeatPrin A B (k+1) (Nat.succ_pos k)) hc
    exact h.2 u c hple hca x (G_repeatPrin u A B (k+1) x hx)

/-- Anything strictly between `ψ_{u₀}(0)` and `ψ_u(0)` has a subscript
between. -/
theorem psi_sub_between {u₀ u c : Term} (h₁ : psi u₀ nil < c) (h₂ : c ≤ psi u nil) :
    ∃ r s c₁, c = cons r s c₁ ∧ u₀ ≤ r ∧ r ≤ u := by
  cases c with
  | nil => exact absurd h₁ (not_lt_nil _)
  | cons r s c₁ =>
    have hrs_le : psi r s ≤ psi u nil := by
      rcases le_iff_lt_or_eq.mp h₂ with hB | hB
      · rcases cons_lt_cons_iff.mp hB with hB' | ⟨_, hB''⟩
        · exact le_of_lt hB'
        · exact absurd hB'' (not_lt_nil _)
      · injection hB with e1 e2 _
        exact e1 ▸ e2 ▸ le_refl _
    have hru : r ≤ u := by
      rcases le_iff_lt_or_eq.mp hrs_le with h | h
      · rcases psi_lt_psi_iff.mp h with h' | ⟨h', _⟩
        · exact le_of_lt h'
        · exact h' ▸ le_refl _
      · injection h with e1 _ _
        exact e1 ▸ le_refl _
    have hu0r : u₀ ≤ r := by
      rcases cons_lt_cons_iff.mp h₁ with hA | ⟨hA, _⟩
      · rcases psi_lt_psi_iff.mp hA with h' | ⟨h', _⟩
        · exact le_of_lt h'
        · exact h' ▸ le_refl _
      · injection hA with e1 _ _
        exact e1 ▸ le_refl _
    exact ⟨r, s, c₁, rfl, hu0r, hru⟩

/-- **The subscript form of 3.5**: `⊲` is carried into the subscript of a
collapse with argument `0`. -/
theorem Trian.psi_sub {z u₀ u : Term} (h : Trian z u₀ u) :
    Trian z (psi u₀ nil) (psi u nil) := by
  refine ⟨psi_lt_psi_iff.mpr (Or.inl h.1), ?_⟩
  intro v c hlt hle
  obtain ⟨r, s, c₁, rfl, hu0r, hru⟩ := psi_sub_between hlt hle
  by_cases hvu : v ≤ u₀
  · have hvr : v ≤ r := le_trans hvu hu0r
    rw [G_psi_of_le hvu, G_cons, if_pos hvr]
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨nil, List.mem_append_right _ (List.mem_cons_self ..), le_refl nil⟩
    rcases List.mem_append.mp hx with hx | hx
    · rcases le_iff_lt_or_eq.mp hu0r with hlt' | rfl
      · obtain ⟨y, hy, hle'⟩ := h.2 v r hlt' hru x hx
        rcases List.mem_append.mp hy with hy | hy
        · exact ⟨y, List.mem_append_left _ (List.mem_append_left _
            (List.mem_cons_of_mem _ (List.mem_append_left _ hy))), hle'⟩
        · exact ⟨y, List.mem_append_right _ hy, hle'⟩
      · exact ⟨x, List.mem_append_left _ (List.mem_append_left _
          (List.mem_cons_of_mem _ (List.mem_append_left _ hx))), le_refl x⟩
    · exact absurd hx (List.not_mem_nil)
  · rw [G_psi_of_not_le hvu]
    intro x hx; exact absurd hx (List.not_mem_nil)

/-- A standard form whose domain is `1` is its own predecessor plus one. -/
theorem eq_addT_one_of_dom_eq_one : ∀ X : Term, OT X → dom X = t1 →
    addT (fs X nil) t1 = X := by
  intro X
  induction X with
  | nil => intro _ h; exact absurd h (by decide)
  | cons X₁ X₂ t _ _ iht =>
    intro hOT hd
    cases t with
    | cons c d u =>
      have hdt : dom (cons c d u) = t1 := hd
      show addT (fs (cons X₁ X₂ (cons c d u)) nil) t1 = _
      rw [fs, addT_cons, iht (OT_tail hOT) hdt]
    | nil =>
      by_cases h1 : dom X₂ = nil
      · have hX₂ : X₂ = nil := dom_eq_nil_iff.mp h1
        subst hX₂
        by_cases g1 : dom X₁ = nil
        · have hX₁ : X₁ = nil := dom_eq_nil_iff.mp g1
          subst hX₁
          rw [show fs (cons nil nil nil) nil = nil from by rw [fs]; simp_all]
          rfl
        · by_cases g2 : dom X₁ = t1
          · rw [show dom (cons X₁ nil nil) = cons X₁ nil nil from by rw [dom]; simp_all] at hd
            injection hd with e1 _ _
            subst e1
            exact absurd rfl g1
          · rw [show dom (cons X₁ nil nil) = dom X₁ from by rw [dom]; simp_all] at hd
            exact absurd hd g2
      · by_cases h2 : dom X₂ = t1
        · rw [show dom (cons X₁ X₂ nil) = tw from by rw [dom]; simp_all] at hd
          exact absurd hd (by decide)
        · by_cases h3 : dom X₂ = tw
          · rw [show dom (cons X₁ X₂ nil) = tw from by rw [dom]; simp_all] at hd
            exact absurd hd (by decide)
          · by_cases h4 : dom X₂ < cons X₁ X₂ nil
            · rw [show dom (cons X₁ X₂ nil) = dom X₂ from by rw [dom]; simp_all] at hd
              exact absurd hd h2
            · rw [show dom (cons X₁ X₂ nil) = tw from by rw [dom]; simp_all] at hd
              exact absurd hd (by decide)

/-- Buchholz 3.4, applied where 3.3 needs it: a collapse of a value of the
fundamental sequence is standard. -/
theorem OT_psi_fs {A B Y : Term} (hOT : OT (psi A B))
    (hT : Trian Y (fs B Y) B) (hY : ∀ x ∈ G A Y, x < fs B Y)
    (hfs : OT (fs B Y)) : OT (psi A (fs B Y)) :=
  OT_psi_of (OT_fst hOT) hfs (hT.G_lt (OT_G_lt hOT) hY)

/-- Below a successor means at most its predecessor. -/
theorem le_pred_of_lt {A Z : Term} (hOT : OT Z) (hd : dom Z = t1) (h : A < Z) :
    A ≤ fs Z nil := by
  rcases lt_trichotomy (fs Z nil) A with hlt | heq | hgt
  · exfalso
    have hsplit : addT (fs Z nil) t1 = Z := eq_addT_one_of_dom_eq_one Z hOT hd
    obtain ⟨r, hr, hpos, hle⟩ := addT_between (fs Z nil)
      (show addT (fs Z nil) nil < A by rw [addT_nil_right]; exact hlt)
      (by rw [hsplit]; exact le_of_lt h)
    have hr1 : r = t1 := by
      rcases le_iff_lt_or_eq.mp hle with h' | h'
      · have hz := lt_one_iff.mp h'
        rw [hz] at hpos
        exact absurd hpos (lt_irrefl nil)
      · exact h'
    rw [hr1, hsplit] at hr
    rw [hr] at h
    exact absurd h (lt_irrefl Z)
  · exact heq ▸ le_refl _
  · exact le_of_lt hgt

/-- **Buchholz 3.3** for the extended system: the fundamental sequence keeps
a term standard. -/
def OTFS : Prop := ∀ X Y : Term, OT X → Y < dom X → OT Y → OT (fs X Y)

/-- Buchholz's tower invariant, reduced to a statement about one term: for a
standard form `X` whose domain is indexed by terms, what `G` sees in the
subscript `Z` of `dom X` is bounded by what it sees in anything between
`X[ψ_{Z[0]}(0)]` and `X`. -/
def SubBound : Prop :=
  ∀ X : Term, OT X → dom X ≠ nil → dom X ≠ t1 → dom X ≠ tw →
    ∀ u c : Term,
      fs X (psi (fs (subOf (dom X)) nil) nil) ≤ c → c ≤ X →
      listLe (G u (subOf (dom X))) (G u c ++ [nil])

theorem G_t1_le_nil (u : Term) : listLe (G u t1) [nil] := by
  intro x hx
  by_cases h : u ≤ nil
  · rw [G_psi_of_le h, G_nil] at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨nil, List.mem_cons_self .., le_refl _⟩
    · exact absurd hx List.not_mem_nil
  · rw [G_psi_of_not_le h] at hx; exact absurd hx List.not_mem_nil

theorem G_t1_eq_nil {u : Term} (h : nil < u) : G u t1 = [] :=
  G_psi_of_not_le (not_le_of_lt h)

/-- The subscript `Z` of `dom X` is bounded, relative to anything between
`X[ψ_{Z[0]}(0)]` and `X`, once Buchholz 3.3 is available. -/
theorem subBound_lt : ∀ X : Term,
    (∀ X' Y' : Term, size X' < size X → OT X' → Y' < dom X' → OT Y' → OT (fs X' Y')) →
    OT X → dom X ≠ nil → dom X ≠ t1 → dom X ≠ tw →
    ∀ u c : Term,
      fs X (psi (fs (subOf (dom X)) nil) nil) ≤ c → c ≤ X →
      listLe (G u (subOf (dom X))) (G u c ++ [nil]) := by
  intro X
  induction X with
  | nil => intro _ _ h0 _ _; exact absurd rfl h0
  | cons A B t ihA ihB iht =>
    intro H hOT h0 h1 hw u c hV hc
    have HA : ∀ X' Y' : Term, size X' < size A → OT X' → Y' < dom X' → OT Y' →
        OT (fs X' Y') := fun X' Y' hs => H X' Y' (by simp only [size_cons]; omega)
    have HB : ∀ X' Y' : Term, size X' < size B → OT X' → Y' < dom X' → OT Y' →
        OT (fs X' Y') := fun X' Y' hs => H X' Y' (by simp only [size_cons]; omega)
    have Ht : ∀ X' Y' : Term, size X' < size t → OT X' → Y' < dom X' → OT Y' →
        OT (fs X' Y') := fun X' Y' hs => H X' Y' (by simp only [size_cons]; omega)
    -- the standard data attached to `dom X`
    have hZne : subOf (dom (cons A B t)) ≠ nil := subOf_dom_ne_nil h0 h1 hw
    have hOTZ : OT (subOf (dom (cons A B t))) := OT_subOf_dom hOT h0 hw
    have hZdom : nil < dom (subOf (dom (cons A B t))) :=
      lt_of_le_of_ne (nil_le _) (fun h => dom_ne_nil hZne h.symm)
    have hOTW : OT (psi (fs (subOf (dom (cons A B t))) nil) nil) :=
      OT_psi_nil (H _ nil (size_subOf_dom_lt h0) hOTZ hZdom rfl)
    have hWlt : psi (fs (subOf (dom (cons A B t))) nil) nil < dom (cons A B t) :=
      W0_lt_dom h0 h1 hw
    cases t with
    | cons c' d' r' =>
      have hdt : dom (cons A B (cons c' d' r')) = dom (cons c' d' r') := rfl
      have hfsle : fs (cons c' d' r') (psi (fs (subOf (dom (cons c' d' r'))) nil) nil)
          ≤ cons c' d' r' := le_of_lt (fs_lt hWlt)
      have hIH := iht Ht (OT_tail hOT) h0 h1 hw u
      have hVeq : fs (cons A B (cons c' d' r'))
          (psi (fs (subOf (dom (cons A B (cons c' d' r')))) nil) nil)
          = addT (psi A B) (fs (cons c' d' r')
              (psi (fs (subOf (dom (cons c' d' r'))) nil) nil)) := by rw [fs]; rfl
      rw [hVeq] at hV
      rcases le_iff_lt_or_eq.mp hV with hlt | heq
      · obtain ⟨c₀, rfl, hc1, hc2⟩ := addT_between (psi A B) hlt hc
        rw [G_addT]
        intro x hx
        obtain ⟨y, hy, hxy⟩ := hIH c₀ (le_of_lt hc1) hc2 x hx
        rcases List.mem_append.mp hy with hy | hy
        · exact ⟨y, List.mem_append_left _ (List.mem_append_right _ hy), hxy⟩
        · exact ⟨y, List.mem_append_right _ hy, hxy⟩
      · rw [← heq, G_addT]
        intro x hx
        obtain ⟨y, hy, hxy⟩ := hIH _ (le_refl _) hfsle x hx
        rcases List.mem_append.mp hy with hy | hy
        · exact ⟨y, List.mem_append_left _ (List.mem_append_right _ hy), hxy⟩
        · exact ⟨y, List.mem_append_right _ hy, hxy⟩
    | nil =>
      by_cases e1 : dom B = nil
      · have hB : B = nil := dom_eq_nil_iff.mp e1
        subst hB
        by_cases g1 : dom A = nil
        · have hA : A = nil := dom_eq_nil_iff.mp g1
          subst hA
          exact absurd (show dom (cons nil nil nil) = t1 from rfl) h1
        · by_cases g2 : dom A = t1
          · -- the successor branch
            have hdX : dom (cons A nil nil) = cons A nil nil := by rw [dom]; simp_all
            have hZ : subOf (dom (cons A nil nil)) = A := by rw [hdX]; rfl
            have hOTA : OT A := OT_fst hOT
            have hOTA0 : OT (fs A nil) :=
              H A nil (by simp only [size_cons]; omega) hOTA
                (by rw [g2]; exact nil_lt_cons _ _ _) rfl
            have hAsplit : addT (fs A nil) t1 = A :=
              eq_addT_one_of_dom_eq_one A hOTA g2
            have hAlt : fs A nil < A := by
              have hx := addT_lt (fs A nil) (show (nil : Term) < t1 from nil_lt_cons _ _ _)
              rwa [addT_nil_right, hAsplit] at hx
            have hVeq : fs (cons A nil nil)
                (psi (fs (subOf (dom (cons A nil nil))) nil) nil)
                = psi (fs A nil) nil := by rw [fs]; simp_all
            rw [hVeq] at hV
            rw [hZ]
            have hGA : G u A = G u (fs A nil) ++ G u t1 := by
              have hx := G_addT u (fs A nil) t1
              rwa [hAsplit] at hx
            by_cases hu : u ≤ fs A nil
            · have hsub : listLe (G u (fs A nil)) (G u c) := by
                rcases le_iff_lt_or_eq.mp hV with hlt | heq
                · obtain ⟨r, s, c₁, hceq, hr1, hr2⟩ := psi_sub_between hlt hc
                  have hGr : listLe (G u (fs A nil)) (G u r) ∧ u ≤ r := by
                    rcases le_iff_lt_or_eq.mp hr1 with hlt' | heq'
                    · obtain ⟨r', hr', hpos, hle'⟩ :=
                        addT_between (fs A nil) (by rw [addT_nil_right]; exact hlt')
                          (by rw [hAsplit]; exact hr2)
                      have hr'1 : r' = t1 := by
                        rcases le_iff_lt_or_eq.mp hle' with h'' | h''
                        · have := lt_one_iff.mp h''
                          rw [this] at hpos
                          exact absurd hpos (lt_irrefl nil)
                        · exact h''
                      have hrA : r = A := by rw [hr', hr'1, hAsplit]
                      refine ⟨?_, ?_⟩
                      · rw [hrA, hGA]; exact listLe_append_left (listLe_refl _)
                      · rw [hrA]; exact le_trans hu (le_of_lt hAlt)
                    · rw [← heq']; exact ⟨listLe_refl _, hu⟩
                  rw [hceq, G_cons, if_pos hGr.2]
                  intro x hx
                  obtain ⟨y, hy, hxy⟩ := hGr.1 x hx
                  exact ⟨y, List.mem_append_left _ (List.mem_cons_of_mem _
                    (List.mem_append_left _ hy)), hxy⟩
                · rw [← heq, G_psi_of_le hu, G_nil, List.append_nil]
                  intro x hx
                  exact ⟨x, List.mem_cons_of_mem _ hx, le_refl x⟩
              rw [hGA]
              intro x hx
              rcases List.mem_append.mp hx with hx | hx
              · obtain ⟨y, hy, hxy⟩ := hsub x hx
                exact ⟨y, List.mem_append_left _ hy, hxy⟩
              · obtain ⟨y, hy, hxy⟩ := G_t1_le_nil u x hx
                rcases List.mem_cons.mp hy with hy' | hy'
                · exact ⟨nil, List.mem_append_right _ (List.mem_cons_self ..), hy' ▸ hxy⟩
                · exact absurd hy' List.not_mem_nil
            · have hlt' : fs A nil < u := lt_of_not_le hu
              rw [hGA, G_eq_nil_of_le _ u hOTA0 (le_of_lt hlt'),
                G_t1_eq_nil (lt_of_le_of_lt' (nil_le _) hlt')]
              intro x hx; exact absurd hx List.not_mem_nil
          · -- dom X = dom A
            have hdX : dom (cons A nil nil) = dom A := by rw [dom]; simp_all
            have hOTA : OT A := OT_fst hOT
            have hWA : psi (fs (subOf (dom A)) nil) nil < dom A := hdX ▸ hWlt
            have hOTfa : OT (fs A (psi (fs (subOf (dom A)) nil) nil)) :=
              H A _ (by simp only [size_cons]; omega) hOTA hWA (hdX ▸ hOTW)
            have hfale : fs A (psi (fs (subOf (dom A)) nil) nil) ≤ A := le_of_lt (fs_lt hWA)
            have hIH := ihA HA hOTA (hdX ▸ h0) (hdX ▸ h1) (hdX ▸ hw) u
            have hVeq : fs (cons A nil nil)
                (psi (fs (subOf (dom (cons A nil nil))) nil) nil)
                = psi (fs A (psi (fs (subOf (dom A)) nil) nil)) nil := by
              rw [fs]; simp_all
            rw [hVeq] at hV
            rw [hdX]
            rcases le_iff_lt_or_eq.mp hV with hlt | heq
            · obtain ⟨r, s, c₁, rfl, hr1, hr2⟩ := psi_sub_between hlt hc
              by_cases hur : u ≤ r
              · intro x hx
                obtain ⟨y, hy, hxy⟩ := hIH r hr1 hr2 x hx
                rcases List.mem_append.mp hy with hy | hy
                · refine ⟨y, List.mem_append_left _ ?_, hxy⟩
                  rw [G_cons, if_pos hur]
                  exact List.mem_append_left _ (List.mem_cons_of_mem _
                    (List.mem_append_left _ hy))
                · exact ⟨y, List.mem_append_right _ hy, hxy⟩
              · intro x hx
                obtain ⟨y, hy, hxy⟩ := hIH _ (le_refl _) hfale x hx
                rw [G_eq_nil_of_le _ u hOTfa (le_trans hr1 (le_of_lt (lt_of_not_le hur)))] at hy
                rcases List.mem_append.mp hy with hy | hy
                · exact absurd hy List.not_mem_nil
                · exact ⟨y, List.mem_append_right _ hy, hxy⟩
            · rw [← heq]
              by_cases hur : u ≤ fs A (psi (fs (subOf (dom A)) nil) nil)
              · intro x hx
                obtain ⟨y, hy, hxy⟩ := hIH _ (le_refl _) hfale x hx
                rcases List.mem_append.mp hy with hy | hy
                · refine ⟨y, List.mem_append_left _ ?_, hxy⟩
                  rw [G_psi_of_le hur]
                  exact List.mem_cons_of_mem _ (List.mem_append_left _ hy)
                · exact ⟨y, List.mem_append_right _ hy, hxy⟩
              · intro x hx
                obtain ⟨y, hy, hxy⟩ := hIH _ (le_refl _) hfale x hx
                rw [G_eq_nil_of_le _ u hOTfa (le_of_lt (lt_of_not_le hur))] at hy
                rcases List.mem_append.mp hy with hy | hy
                · exact absurd hy List.not_mem_nil
                · exact ⟨y, List.mem_append_right _ hy, hxy⟩
      · by_cases e2 : dom B = t1
        · exact absurd (show dom (cons A B nil) = tw from by rw [dom]; simp_all) hw
        · by_cases e3 : dom B = tw
          · exact absurd (show dom (cons A B nil) = tw from by rw [dom]; simp_all) hw
          · by_cases e4 : dom B < cons A B nil
            · have hdX : dom (cons A B nil) = dom B := by rw [dom]; simp_all
              have hOTB : OT B := OT_snd hOT
              have hWB : psi (fs (subOf (dom B)) nil) nil < dom B := hdX ▸ hWlt
              have hfble : fs B (psi (fs (subOf (dom B)) nil) nil) ≤ B := le_of_lt (fs_lt hWB)
              have hIH := ihB HB hOTB (hdX ▸ h0) (hdX ▸ h1) (hdX ▸ hw) u
              have hVeq : fs (cons A B nil)
                  (psi (fs (subOf (dom (cons A B nil))) nil) nil)
                  = psi A (fs B (psi (fs (subOf (dom B)) nil) nil)) := by
                rw [fs]; simp_all
              rw [hVeq] at hV
              rw [hdX]
              by_cases hu : u ≤ A
              · rcases le_iff_lt_or_eq.mp hV with hlt | heq
                · obtain ⟨c₀, c₁, rfl, hb0, hb1⟩ := psi_between hlt hc
                  intro x hx
                  obtain ⟨y, hy, hxy⟩ := hIH c₀ hb0 hb1 x hx
                  rcases List.mem_append.mp hy with hy | hy
                  · refine ⟨y, List.mem_append_left _ ?_, hxy⟩
                    rw [G_cons, if_pos hu]
                    exact List.mem_append_left _ (List.mem_cons_of_mem _
                      (List.mem_append_right _ hy))
                  · exact ⟨y, List.mem_append_right _ hy, hxy⟩
                · rw [← heq]
                  intro x hx
                  obtain ⟨y, hy, hxy⟩ := hIH _ (le_refl _) hfble x hx
                  rcases List.mem_append.mp hy with hy | hy
                  · refine ⟨y, List.mem_append_left _ ?_, hxy⟩
                    rw [G_psi_of_le hu]
                    exact List.mem_cons_of_mem _ (List.mem_append_right _ hy)
                  · exact ⟨y, List.mem_append_right _ hy, hxy⟩
              · have hZA : subOf (dom B) ≤ A := by
                  rcases dom_shape B with hd | hd | ⟨Z', hd⟩
                  · exact absurd hd e1
                  · exact absurd hd e3
                  · rw [hd] at e4 ⊢
                    simp only [subOf]
                    rcases psi_lt_psi_iff.mp (cons_lt_psi_iff.mp e4) with h | ⟨h, _⟩
                    · exact le_of_lt h
                    · exact h ▸ le_refl _
                rw [G_eq_nil_of_le _ u (by rw [← hdX]; exact hOTZ)
                  (le_trans hZA (le_of_lt (lt_of_not_le hu)))]
                intro x hx; exact absurd hx List.not_mem_nil
            · exact absurd (show dom (cons A B nil) = tw from by rw [dom]; simp_all) hw

theorem subBound_of_OTFS (H : OTFS) : SubBound :=
  fun X => subBound_lt X (fun X' Y' _ => H X' Y')

/-- The bound on `Z` carries to `Z[0]`, through 3.6 at `Z`. -/
theorem sub_G_le {X₂ : Term} (e1 : dom X₂ ≠ nil) (e2 : dom X₂ ≠ t1) (e3 : dom X₂ ≠ tw)
    (hTZ : Trian nil (fs (subOf (dom X₂)) nil) (subOf (dom X₂)))
    (hS : ∀ u c : Term,
      fs X₂ (tower (fs (subOf (dom X₂)) nil) X₂ 0) ≤ c → c ≤ X₂ →
      listLe (G u (subOf (dom X₂))) (G u c ++ [nil])) :
    ∀ u c : Term,
      fs X₂ (tower (fs (subOf (dom X₂)) nil) X₂ 0) ≤ c → c ≤ X₂ →
      listLe (G u (fs (subOf (dom X₂)) nil)) (c :: (G u c ++ [nil])) := by
  intro u c h1 h2 x hx
  obtain ⟨y, hy, hxy⟩ :=
    hTZ.2 u (subOf (dom X₂)) (subOf_fs_lt e1 e2 e3) (le_refl _) x hx
  rcases List.mem_append.mp hy with hy | hy
  · obtain ⟨z, hz, hyz⟩ := hS u c h1 h2 y hy
    exact ⟨z, List.mem_cons_of_mem _ hz, le_trans hxy hyz⟩
  · rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨nil, List.mem_cons_of_mem _ (List.mem_append_right _
        (List.mem_cons_self ..)), hxy⟩
    · rw [G_nil] at hy; exact absurd hy List.not_mem_nil

/-- The tower bound follows from the same bound on the tower's subscript
alone: no induction on the term, and none on the rung. -/
theorem tower_G_le {X₂ : Term}
    (e1 : dom X₂ ≠ nil) (e2 : dom X₂ ≠ t1) (e3 : dom X₂ ≠ tw)
    (hIH : ∀ W : Term, W < dom X₂ → Trian W (fs X₂ W) X₂)
    (hS : ∀ u c : Term,
      fs X₂ (tower (fs (subOf (dom X₂)) nil) X₂ 0) ≤ c → c ≤ X₂ →
      listLe (G u (fs (subOf (dom X₂)) nil)) (c :: (G u c ++ [nil]))) :
    ∀ (i : Nat) (u c : Term),
      fs X₂ (tower (fs (subOf (dom X₂)) nil) X₂ i) ≤ c → c ≤ X₂ →
      listLe (G u (tower (fs (subOf (dom X₂)) nil) X₂ i)) (c :: (G u c ++ [nil])) := by
  intro i
  induction i with
  | zero =>
    intro u c h1 h2
    by_cases hu : u ≤ fs (subOf (dom X₂)) nil
    · show listLe (G u (psi (fs (subOf (dom X₂)) nil) nil)) _
      rw [G_psi_of_le hu, G_nil, List.append_nil]
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨nil, List.mem_cons_of_mem _ (List.mem_append_right _
          (List.mem_cons_self ..)), le_refl nil⟩
      · exact hS u c h1 h2 x hx
    · show listLe (G u (psi (fs (subOf (dom X₂)) nil) nil)) _
      rw [G_psi_of_not_le hu]
      intro x hx; exact absurd hx List.not_mem_nil
  | succ k ihk =>
    intro u c h1 h2
    have hYk : fs X₂ (tower (fs (subOf (dom X₂)) nil) X₂ k) ≤ c :=
      le_trans (le_of_lt (tower_val_lt e1 e2 e3 k)) h1
    have h0 : fs X₂ (tower (fs (subOf (dom X₂)) nil) X₂ 0) ≤ c :=
      le_trans (tower_val_le_zero e1 e2 e3 (k + 1)) h1
    by_cases hu : u ≤ fs (subOf (dom X₂)) nil
    · show listLe (G u (psi (fs (subOf (dom X₂)) nil)
        (fs X₂ (tower (fs (subOf (dom X₂)) nil) X₂ k)))) _
      rw [G_psi_of_le hu]
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨c, List.mem_cons_self .., hYk⟩
      rcases List.mem_append.mp hx with hx | hx
      · exact hS u c h0 h2 x hx
      · rcases le_iff_lt_or_eq.mp hYk with hlt | heq
        · obtain ⟨y, hy, hxy⟩ :=
            (hIH _ (tower_lt_dom e1 e2 e3 k)).2 u c hlt h2 x hx
          rcases List.mem_append.mp hy with hy | hy
          · exact ⟨y, List.mem_cons_of_mem _ (List.mem_append_left _ hy), hxy⟩
          · rcases List.mem_cons.mp hy with rfl | hy
            · exact ⟨nil, List.mem_cons_of_mem _ (List.mem_append_right _
                (List.mem_cons_self ..)), hxy⟩
            · obtain ⟨z, hz, hyz⟩ := ihk u c hYk h2 y hy
              exact ⟨z, hz, le_trans hxy hyz⟩
        · rw [heq] at hx
          exact ⟨x, List.mem_cons_of_mem _ (List.mem_append_left _ hx), le_refl x⟩
    · show listLe (G u (psi (fs (subOf (dom X₂)) nil)
        (fs X₂ (tower (fs (subOf (dom X₂)) nil) X₂ k)))) _
      rw [G_psi_of_not_le hu]
      intro x hx; exact absurd hx List.not_mem_nil

theorem Trian_case4 {X₁ X₂ : Term}
    (e1 : dom X₂ ≠ nil) (e2 : dom X₂ ≠ t1) (e3 : dom X₂ ≠ tw)
    (e4 : ¬ (dom X₂ < cons X₁ X₂ nil))
    (hIH : ∀ W : Term, W < dom X₂ → Trian W (fs X₂ W) X₂)
    (hB : ∀ (i : Nat) (u c : Term),
        fs X₂ (tower (fs (subOf (dom X₂)) nil) X₂ i) ≤ c → c ≤ X₂ →
        listLe (G u (tower (fs (subOf (dom X₂)) nil) X₂ i)) (c :: (G u c ++ [nil])))
    (n : Nat) :
    Trian (numeral n) (fs (cons X₁ X₂ nil) (numeral n)) (cons X₁ X₂ nil) := by
  have hT : Trian (tower (fs (subOf (dom X₂)) nil) X₂ n)
      (fs X₂ (tower (fs (subOf (dom X₂)) nil) X₂ n)) X₂ :=
    hIH _ (tower_lt_dom e1 e2 e3 n)
  rw [fs_numeral e1 e2 e3 e4 n]
  refine ⟨psi_lt_psi_iff.mpr (Or.inr ⟨rfl, hT.1⟩), ?_⟩
  intro v c hlt hle
  obtain ⟨c₀, c₁, rfl, hb0, hb1⟩ := psi_between hlt hle
  by_cases hvu : v ≤ X₁
  · rw [G_psi_of_le hvu, G_cons, if_pos hvu]
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨c₀, List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_self ..)), hb0⟩
    rcases List.mem_append.mp hx with hx | hx
    · exact ⟨x, List.mem_append_left _ (List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_append_left _ hx))), le_refl x⟩
    · rcases le_iff_lt_or_eq.mp hb0 with hlt0 | heq0
      · obtain ⟨y, hy, hle'⟩ := hT.2 v c₀ hlt0 hb1 x hx
        rcases List.mem_append.mp hy with hy | hy
        · exact ⟨y, List.mem_append_left _ (List.mem_append_left _
            (List.mem_cons_of_mem _ (List.mem_append_right _ hy))), hle'⟩
        · rcases List.mem_cons.mp hy with rfl | hy
          · exact ⟨nil, List.mem_append_right _ (List.mem_cons_self ..), hle'⟩
          · obtain ⟨z, hz, hyz⟩ := hB n v c₀ hb0 hb1 y hy
            rcases List.mem_cons.mp hz with rfl | hz
            · exact ⟨z, List.mem_append_left _ (List.mem_append_left _
                (List.mem_cons_self ..)), le_trans hle' hyz⟩
            rcases List.mem_append.mp hz with hz | hz
            · exact ⟨z, List.mem_append_left _ (List.mem_append_left _
                (List.mem_cons_of_mem _ (List.mem_append_right _ hz))), le_trans hle' hyz⟩
            · rcases List.mem_cons.mp hz with rfl | hz
              · exact ⟨nil, List.mem_append_right _ (List.mem_cons_self ..),
                  le_trans hle' hyz⟩
              · exact absurd hz List.not_mem_nil
      · rw [heq0] at hx
        exact ⟨x, List.mem_append_left _ (List.mem_append_left _
          (List.mem_cons_of_mem _ (List.mem_append_right _ hx))), le_refl x⟩
  · rw [G_psi_of_not_le hvu]
    intro x hx; exact absurd hx List.not_mem_nil

theorem Trian_fs_aux : ∀ n : Nat,
    (∀ X' : Term, size X' < n → OT X' → dom X' ≠ nil → dom X' ≠ t1 → dom X' ≠ tw →
      ∀ u c : Term, fs X' (psi (fs (subOf (dom X')) nil) nil) ≤ c → c ≤ X' →
        listLe (G u (subOf (dom X'))) (G u c ++ [nil])) →
    ∀ X Y : Term, size X ≤ n → OT X → Y < dom X → Trian Y (fs X Y) X := by
  intro n
  induction n with
  | zero =>
    intro _ X Y hsz _ hY
    cases X with
    | nil => exact absurd hY (not_lt_nil Y)
    | cons a b t => simp only [size_cons] at hsz; omega
  | succ n ih =>
  intro H X Y hsz hOT hY
  have H' : ∀ X' : Term, size X' < n → OT X' → dom X' ≠ nil → dom X' ≠ t1 → dom X' ≠ tw →
      ∀ u c : Term, fs X' (psi (fs (subOf (dom X')) nil) nil) ≤ c → c ≤ X' →
        listLe (G u (subOf (dom X'))) (G u c ++ [nil]) :=
    fun X' hs => H X' (by omega)
  cases X with
  | nil => exact absurd hY (not_lt_nil Y)
  | cons X₁ X₂ t =>
    cases t with
    | cons c d u =>
      simp only [size_cons] at hsz
      have hd : dom (cons X₁ X₂ (cons c d u)) = dom (cons c d u) := rfl
      rw [hd] at hY
      have hT := ih H' (cons c d u) Y (by simp only [size_cons]; omega) (OT_tail hOT) hY
      show Trian Y (fs (cons X₁ X₂ (cons c d u)) Y) (cons X₁ X₂ (cons c d u))
      rw [fs]
      exact Trian.addT_left (psi X₁ X₂) hT
    | nil =>
      simp only [size_cons] at hsz
      have key : fs (cons X₁ X₂ nil) Y < cons X₁ X₂ nil := fs_lt hY
      by_cases h1 : dom X₂ = nil
      · have hX₂ : X₂ = nil := dom_eq_nil_iff.mp h1
        subst hX₂
        by_cases g1 : dom X₁ = nil
        · have he : fs (cons X₁ nil nil) Y = nil := by rw [fs]; simp_all
          rw [he]
          exact Trian_nil (nil_lt_cons _ _ _)
        · by_cases g2 : dom X₁ = t1
          · have he : fs (cons X₁ nil nil) Y = Y := by rw [fs]; simp_all
            have hd : dom (cons X₁ nil nil) = cons X₁ nil nil := by rw [dom]; simp_all
            rw [hd] at hY
            rw [he]
            exact Trian_self hY
          · have he : fs (cons X₁ nil nil) Y = psi (fs X₁ Y) nil := by rw [fs]; simp_all
            have hd : dom (cons X₁ nil nil) = dom X₁ := by rw [dom]; simp_all
            rw [hd] at hY
            rw [he]
            exact Trian.psi_sub (ih H' X₁ Y (by omega) (OT_fst hOT) hY)
      · by_cases h2 : dom X₂ = t1
        · have hfs : Trian nil (fs X₂ nil) X₂ := by
            refine ih H' X₂ nil (by omega) (OT_snd hOT) ?_
            rw [h2]; exact nil_lt_cons _ _ _
          have hpsi : Trian Y (psi X₁ (fs X₂ nil)) (psi X₁ X₂) :=
            Trian.of_nil (Trian.psi_left X₁ hfs)
          by_cases hn : isNum Y = true
          · have he : fs (cons X₁ X₂ nil) Y = repeatPrin X₁ (fs X₂ nil) (numVal Y) := by
              rw [fs]; simp_all
            rw [he] at key ⊢
            exact hpsi.repeatPrin _ key
          · have he : fs (cons X₁ X₂ nil) Y = nil := by rw [fs]; simp_all
            rw [he]
            exact Trian_nil (nil_lt_cons _ _ _)
        · by_cases h3 : dom X₂ = tw
          · have he : fs (cons X₁ X₂ nil) Y = psi X₁ (fs X₂ Y) := by rw [fs]; simp_all
            have hd : dom (cons X₁ X₂ nil) = tw := by rw [dom]; simp_all
            rw [hd, ← h3] at hY
            rw [he]
            exact Trian.psi_left X₁ (ih H' X₂ Y (by omega) (OT_snd hOT) hY)
          · by_cases h4 : dom X₂ < cons X₁ X₂ nil
            · have he : fs (cons X₁ X₂ nil) Y = psi X₁ (fs X₂ Y) := by rw [fs]; simp_all
              have hd : dom (cons X₁ X₂ nil) = dom X₂ := by rw [dom]; simp_all
              rw [hd] at hY
              rw [he]
              exact Trian.psi_left X₁ (ih H' X₂ Y (by omega) (OT_snd hOT) hY)
            · have hIH : ∀ W : Term, W < dom X₂ → Trian W (fs X₂ W) X₂ :=
                fun W hW => ih H' X₂ W (by omega) (OT_snd hOT) hW
              have hZne : subOf (dom X₂) ≠ nil := subOf_dom_ne_nil h1 h2 h3
              have hOTZ : OT (subOf (dom X₂)) := by
                rcases dom_shape X₂ with hd | hd | ⟨A, hd⟩
                · exact absurd hd h1
                · exact absurd hd h3
                · have hz := OT_dom (OT_snd hOT)
                  rw [hd] at hz ⊢
                  exact OT_fst hz
              have hTZ : Trian nil (fs (subOf (dom X₂)) nil) (subOf (dom X₂)) :=
                ih H' (subOf (dom X₂)) nil
                  (Nat.le_trans (Nat.le_trans (size_subOf_le _) (size_dom_le X₂))
                    (by omega)) hOTZ
                  (lt_of_le_of_ne (nil_le _) (fun hz => dom_ne_nil hZne hz.symm))
              have hBd := tower_G_le h1 h2 h3 hIH
                (sub_G_le h1 h2 h3 hTZ (H X₂ (by omega)
                  (OT_snd hOT) h1 h2 h3))
              by_cases hn : Y ≠ nil ∧ isNum Y = true
              · have hYn : Y = numeral (numVal Y) := eq_numeral_numVal Y hn.2
                rw [hYn]
                exact Trian_case4 h1 h2 h3 h4 hIH hBd (numVal Y)
              · have hL : fs (cons X₁ X₂ nil) Y
                    = cons X₁ (fs X₂ (cons (fs (subOf (dom X₂)) nil) nil nil)) nil := by
                  rw [fs]
                  simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
                  rw [dif_neg hn]
                have he : fs (cons X₁ X₂ nil) Y = fs (cons X₁ X₂ nil) (numeral 0) := by
                  rw [hL, fs_numeral h1 h2 h3 h4 0]
                  rfl
                rw [he]
                exact Trian.of_nil (Trian_case4 h1 h2 h3 h4 hIH hBd 0)

/-- **Buchholz 3.6** for the extended system, from 3.3. -/
theorem Trian_fs (H : OTFS) {X Y : Term} (hOT : OT X) (h : Y < dom X) :
    Trian Y (fs X Y) X :=
  Trian_fs_aux (size X) (fun X' _ => subBound_of_OTFS H X') X Y (Nat.le_refl _) hOT h

/-- What Buchholz's case 4 needs of the tower in the proof of 3.3: each rung
is a standard form, and `G` at the level of the collapse sees in it only
things below the value that rung produces. -/
def Bachmann : Prop :=
  ∀ A B : Term, OT (cons A B nil) →
    dom B ≠ nil → dom B ≠ t1 → dom B ≠ tw → ¬ (dom B < cons A B nil) →
    ∀ x ∈ G A B, x < fs B (psi (fs (subOf (dom B)) nil) nil)

@[simp] theorem size_addT : ∀ X Y : Term, size (addT X Y) = size X + size Y := by
  intro X
  induction X with
  | nil => intro Y; show size Y = 0 + size Y; omega
  | cons a b t _ _ iht =>
    intro Y
    rw [addT_cons]
    simp only [size_cons, iht]
    omega

/-- A term below a sum, but too small to reach its prefix, is below that
prefix. -/
theorem lt_of_size_lt_addT {x q t : Term} (h : x < addT q t) (hs : size x < size q) :
    x < q := by
  rcases lt_trichotomy x q with h' | h' | h'
  · exact h'
  · exfalso; rw [h'] at hs; omega
  · exfalso
    obtain ⟨x', hx, _, _⟩ := addT_between q
      (show addT q nil < x by rw [addT_nil_right]; exact h') (le_of_lt h)
    rw [hx, size_addT] at hs
    omega

/-- Appending on the right is strictly monotone, and reflects the order. -/
theorem addT_lt_iff {q x y : Term} : addT q x < addT q y ↔ x < y := by
  constructor
  · intro h
    rcases lt_trichotomy x y with h' | h' | h'
    · exact h'
    · exact absurd (h' ▸ h) (lt_irrefl _)
    · exact absurd (addT_lt q h') (lt_asymm h)
  · exact addT_lt q

/-- A term is at most anything appended to it. -/
theorem le_addT_right (q y : Term) : q ≤ addT q y := by
  cases y with
  | nil => rw [addT_nil_right]; exact le_refl _
  | cons c d r =>
    refine le_of_lt ?_
    have h := addT_lt q (show (nil : Term) < cons c d r from nil_lt_cons _ _ _)
    rwa [addT_nil_right] at h

theorem addT_assoc : ∀ X Y Z : Term, addT (addT X Y) Z = addT X (addT Y Z) := by
  intro X
  induction X with
  | nil => intro Y Z; rfl
  | cons a b t _ _ iht => intro Y Z; rw [addT_cons, addT_cons, addT_cons, iht]

theorem G_cons_eq (u a b t : Term) : G u (cons a b t) = G u (psi a b) ++ G u t := by
  rw [cons_eq_addT, G_addT]

/-- The first index of the tower of Buchholz's case 4, as a function of the
domain. -/
def W0 (V : Term) : Term := psi (fs (subOf (dom V)) nil) nil

/-- **The sum branch of the Bachmann induction.**  The statement has to be
carried with a prefix `p` in front, because the tail inherits the hypothesis
only in that form. -/
theorem bach_sum {a b c d r u p : Term}
    (hIH : ∀ q : Term, (∀ y ∈ G u (cons c d r), y < addT q (cons c d r)) →
            ∀ y ∈ G u (cons c d r), y < addT q (fs (cons c d r) (W0 (cons c d r))))
    (H : ∀ x ∈ G u (cons a b (cons c d r)), x < addT p (cons a b (cons c d r))) :
    ∀ x ∈ G u (cons a b (cons c d r)),
      x < addT p (fs (cons a b (cons c d r)) (W0 (cons a b (cons c d r)))) := by
  intro x hx
  have hVfs : fs (cons a b (cons c d r)) (W0 (cons a b (cons c d r)))
      = cons a b (fs (cons c d r) (W0 (cons c d r))) := by rw [fs]; rfl
  rw [hVfs, cons_eq_addT, ← addT_assoc]
  rw [G_cons_eq] at hx
  rcases List.mem_append.mp hx with hx | hx
  · refine lt_of_lt_of_le' ?_ (le_addT_right _ _)
    refine lt_of_size_lt_addT
      (show x < addT (addT p (psi a b)) (cons c d r) by
        rw [addT_assoc, ← cons_eq_addT]
        exact H x (by rw [G_cons_eq]; exact List.mem_append_left _ hx)) ?_
    have hs := size_lt_of_mem_G u (psi a b) x hx
    rw [size_addT]
    omega
  · refine hIH (addT p (psi a b)) (fun y hy => ?_) x hx
    rw [addT_assoc, ← cons_eq_addT]
    exact H y (by rw [G_cons_eq]; exact List.mem_append_right _ hy)

/-- **The successor branch of the Bachmann induction**: `V = ψ_a(0)` with `a`
a successor.  There `dom V = V`, the fundamental sequence hands back the index
itself, and the bound comes from `le_pred_of_lt` and a size argument. -/
theorem bach_succ {a u p : Term} (hOTa : OT a) (hda : dom a = t1)
    (H : ∀ x ∈ G u (psi a nil), x < addT p (psi a nil)) :
    ∀ x ∈ G u (psi a nil), x < addT p (fs (psi a nil) (W0 (psi a nil))) := by
  have hdV : dom (psi a nil) = psi a nil := by rw [psi, dom]; simp_all
  have hW : W0 (psi a nil) = psi (fs a nil) nil := by rw [W0, hdV]; rfl
  have hfsV : fs (psi a nil) (W0 (psi a nil)) = psi (fs a nil) nil := by
    rw [psi, fs]; simp_all
  have hsplit : addT (fs a nil) t1 = a := eq_addT_one_of_dom_eq_one a hOTa hda
  have hsza : size a = size (fs a nil) + 1 := by
    have h := size_addT (fs a nil) t1
    rw [hsplit] at h
    simpa using h
  rw [hfsV]
  intro x hx
  rcases lt_trichotomy x p with h | h | h
  · exact lt_of_lt_of_le' h (le_addT_right p _)
  · rw [h]
    have hp := addT_lt p (show (nil : Term) < psi (fs a nil) nil from nil_lt_cons _ _ _)
    rwa [addT_nil_right] at hp
  · -- `p < x`, so `x = p + x'` and the bound is about `x'`
    obtain ⟨x', hxe, hpos, _⟩ := addT_between p
      (show addT p nil < x by rw [addT_nil_right]; exact h) (le_of_lt (H x hx))
    have hszx : size x < size a := by
      by_cases hu : u ≤ a
      · rw [G_psi_of_le hu, G_nil, List.append_nil] at hx
        rcases List.mem_cons.mp hx with he | hx'
        · exfalso; rw [he] at h; exact absurd h (not_lt_nil p)
        · exact size_lt_of_mem_G u a x hx'
      · rw [G_psi_of_not_le hu] at hx
        exact absurd hx List.not_mem_nil
    have hszs : size p + size x' = size x := by rw [hxe, size_addT]
    rw [hxe, addT_lt_iff]
    cases x' with
    | nil => exact absurd hpos (lt_irrefl nil)
    | cons c d r =>
      have hlt : cons c d r < psi a nil := by
        have hH := H x hx
        rw [hxe] at hH
        exact addT_lt_iff.mp hH
      have hca : c < a := by
        rcases cons_lt_cons_iff.mp hlt with h' | ⟨_, h'⟩
        · rcases psi_lt_psi_iff.mp h' with h'' | ⟨_, h''⟩
          · exact h''
          · exact absurd h'' (not_lt_nil d)
        · exact absurd h' (not_lt_nil r)
      have hcle : c ≤ fs a nil := le_pred_of_lt hOTa hda hca
      refine cons_lt_cons_iff.mpr (Or.inl (psi_lt_psi_iff.mpr (Or.inl ?_)))
      rcases le_iff_lt_or_eq.mp hcle with h' | h'
      · exact h'
      · exfalso
        rw [← h'] at hsza
        simp only [size_cons] at hszs
        omega

/-- Buchholz's second tower invariant, from the Bachmann property. -/
theorem towerOT_of_Bachmann {A B : Term} (hOT : OT (cons A B nil))
    (e1 : dom B ≠ nil) (e2 : dom B ≠ t1) (e3 : dom B ≠ tw)
    (hAZ : A ≤ subOf (dom B)) (hAZ0 : A ≤ fs (subOf (dom B)) nil)
    (hBach : ∀ x ∈ G A B, x < fs B (psi (fs (subOf (dom B)) nil) nil))
    (hOTZ0 : OT (fs (subOf (dom B)) nil))
    (h33B : ∀ W : Term, W < dom B → OT W → OT (fs B W))
    (h36B : ∀ W : Term, W < dom B → Trian W (fs B W) B)
    (hTZ : Trian nil (fs (subOf (dom B)) nil) (subOf (dom B))) :
    ∀ i : Nat,
      OT (tower (fs (subOf (dom B)) nil) B i)
      ∧ ∀ x ∈ G A (tower (fs (subOf (dom B)) nil) B i),
          x < fs B (tower (fs (subOf (dom B)) nil) B i) := by
  have hdB : dom B = psi (subOf (dom B)) nil := by
    rcases dom_shape B with h | h | ⟨Z, h⟩
    · exact absurd h e1
    · exact absurd h e3
    · rw [h]; rfl
  have hGAB : ∀ y ∈ G A B, y < B := OT_G_lt hOT
  -- what `G` sees in the tower's subscript is below the first value
  have hZ0 : ∀ x ∈ G A (fs (subOf (dom B)) nil),
      x < fs B (psi (fs (subOf (dom B)) nil) nil) := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ :=
      hTZ.2 A (subOf (dom B)) (subOf_fs_lt e1 e2 e3) (le_refl _) x hx
    rcases List.mem_append.mp hy with hy | hy
    · refine lt_of_le_of_lt' hxy (hBach y ?_)
      refine G_dom_subset B (subOf (dom B)) A (OT_snd hOT) hdB hAZ y ?_
      rw [hdB, G_psi_of_le hAZ]
      exact List.mem_cons_of_mem _ (List.mem_append_left _ hy)
    · rcases List.mem_cons.mp hy with hy' | hy'
      · rw [hy'] at hxy
        refine lt_of_le_of_lt' hxy ?_
        exact lt_of_le_of_ne (nil_le _)
          (fun h => fs_ne_nil e1 e2 e3 (fun h' => Term.noConfusion h') h.symm)
      · rw [G_nil] at hy'; exact absurd hy' List.not_mem_nil
  intro i
  induction i with
  | zero =>
    refine ⟨OT_psi_nil hOTZ0, ?_⟩
    intro x hx
    rw [show tower (fs (subOf (dom B)) nil) B 0
        = psi (fs (subOf (dom B)) nil) nil from rfl] at hx
    show x < fs B (psi (fs (subOf (dom B)) nil) nil)
    by_cases hu : A ≤ fs (subOf (dom B)) nil
    · rw [G_psi_of_le hu, G_nil, List.append_nil] at hx
      rcases List.mem_cons.mp hx with hx' | hx
      · rw [hx']
        exact lt_of_le_of_ne (nil_le _)
          (fun h => fs_ne_nil e1 e2 e3 (fun h' => Term.noConfusion h') h.symm)
      · exact hZ0 x hx
    · rw [G_psi_of_not_le hu] at hx; exact absurd hx List.not_mem_nil
  | succ k ihk =>
    have hWlt : tower (fs (subOf (dom B)) nil) B k < dom B := tower_lt_dom e1 e2 e3 k
    have hOTY : OT (fs B (tower (fs (subOf (dom B)) nil) B k)) :=
      h33B _ hWlt ihk.1
    have hGY : ∀ u : Term, A ≤ u →
        ∀ y ∈ G u (fs B (tower (fs (subOf (dom B)) nil) B k)),
          y < fs B (tower (fs (subOf (dom B)) nil) B k) := by
      intro u hAu
      refine (h36B _ hWlt).G_lt ?_ ?_
      · exact fun y hy => hGAB y (G_subset_of_le hAu B y hy)
      · exact fun y hy => ihk.2 y (G_subset_of_le hAu _ y hy)
    refine ⟨OT_psi_of hOTZ0 hOTY (hGY _ hAZ0), ?_⟩
    intro x hx
    show x < fs B (tower (fs (subOf (dom B)) nil) B (k + 1))
    have hstep := tower_val_lt (Z₀ := fs (subOf (dom B)) nil) e1 e2 e3 k
    by_cases hu : A ≤ fs (subOf (dom B)) nil
    · rw [show tower (fs (subOf (dom B)) nil) B (k + 1)
          = psi (fs (subOf (dom B)) nil) (fs B (tower (fs (subOf (dom B)) nil) B k))
          from rfl, G_psi_of_le hu] at hx
      rcases List.mem_cons.mp hx with hx' | hx
      · rw [hx']; exact hstep
      rcases List.mem_append.mp hx with hx | hx
      · exact lt_trans (hZ0 x hx)
          (lt_of_le_of_lt' (tower_val_le_zero e1 e2 e3 k) hstep)
      · exact lt_trans (hGY A (le_refl _) x hx) hstep
    · rw [show tower (fs (subOf (dom B)) nil) B (k + 1)
          = psi (fs (subOf (dom B)) nil) (fs B (tower (fs (subOf (dom B)) nil) B k))
          from rfl, G_psi_of_not_le hu] at hx
      exact absurd hx List.not_mem_nil

theorem OTFS_aux (HB : Bachmann) : ∀ n : Nat, ∀ X : Term, size X ≤ n →
    (OT X → ∀ Y : Term, Y < dom X → Trian Y (fs X Y) X)
  ∧ (OT X → ∀ Y : Term, Y < dom X → OT Y → OT (fs X Y)) := by
  intro n
  induction n with
  | zero =>
    intro X hsz
    cases X with
    | nil => exact ⟨fun _ Y hY => absurd hY (not_lt_nil Y),
        fun _ Y hY _ => absurd hY (not_lt_nil Y)⟩
    | cons a b t => simp only [size_cons] at hsz; omega
  | succ n ih =>
    intro X hsz
    have T36 : ∀ X' : Term, size X' ≤ size X → OT X' → ∀ Y' : Term, Y' < dom X' →
        Trian Y' (fs X' Y') X' := fun X' hs hOT' Y' hY' =>
      Trian_fs_aux (size X')
        (fun X'' hs' => subBound_lt X''
          (fun a b hs'' h1 h2 h3 => (ih a (by omega)).2 h1 b h2 h3))
        X' Y' (Nat.le_refl _) hOT' hY'
    refine ⟨?_, ?_⟩
    · intro hOT Y hY
      exact T36 X (Nat.le_refl _) hOT Y hY
    intro hOT Y hY hOTY
    cases X with
    | nil => exact absurd hY (not_lt_nil Y)
    | cons A B t =>
      simp only [size_cons] at hsz
      cases t with
      | cons c d r =>
        show OT (fs (cons A B (cons c d r)) Y)
        rw [fs]
        exact OT_cons_fs hOT
          ((ih (cons c d r) (by omega)).2 (OT_tail hOT) Y hY hOTY) hY
      | nil =>
        have hOTA : OT A := OT_fst hOT
        have hOTB : OT B := OT_snd hOT
        by_cases e1 : dom B = nil
        · have hB : B = nil := dom_eq_nil_iff.mp e1
          subst hB
          by_cases g1 : dom A = nil
          · rw [show fs (cons A nil nil) Y = nil from by rw [fs]; simp_all]
            exact rfl
          · by_cases g2 : dom A = t1
            · rw [show fs (cons A nil nil) Y = Y from by rw [fs]; simp_all]
              exact hOTY
            · have hdX : dom (cons A nil nil) = dom A := by rw [dom]; simp_all
              rw [show fs (cons A nil nil) Y = psi (fs A Y) nil from by rw [fs]; simp_all]
              exact OT_psi_nil ((ih A (by omega)).2 hOTA Y (hdX ▸ hY) hOTY)
        · by_cases e2 : dom B = t1
          · have hnil : (nil : Term) < dom B := by rw [e2]; exact nil_lt_cons _ _ _
            have hOTb0 : OT (fs B nil) :=
              (ih B (by omega)).2 hOTB nil hnil rfl
            have hpsi : OT (psi A (fs B nil)) :=
              OT_psi_fs hOT (T36 B (by simp only [size_cons]; omega) hOTB nil hnil)
                (fun x hx => absurd hx (by rw [G_nil]; exact List.not_mem_nil)) hOTb0
            by_cases hn : isNum Y = true
            · rw [show fs (cons A B nil) Y = repeatPrin A (fs B nil) (numVal Y) from by
                rw [fs]; simp_all]
              exact OT_repeatPrin hpsi (numVal Y)
            · rw [show fs (cons A B nil) Y = nil from by rw [fs]; simp_all]
              exact rfl
          · by_cases e3 : dom B = tw
            · have hdX : dom (cons A B nil) = tw := by rw [dom]; simp_all
              rw [hdX] at hY
              obtain ⟨k, rfl⟩ := eq_numeral_of_lt_tw hOTY hY
              have hYB : numeral k < dom B := by rw [e3]; exact hY
              have hOTbY : OT (fs B (numeral k)) := (ih B (by omega)).2 hOTB _ hYB hOTY
              rw [show fs (cons A B nil) (numeral k) = psi A (fs B (numeral k)) from by
                rw [fs]; simp_all]
              by_cases hz : fs B (numeral k) = nil
              · rw [hz]; exact OT_psi_nil hOTA
              · refine OT_psi_fs hOT (T36 B (by simp only [size_cons]; omega) hOTB _ hYB) ?_ hOTbY
                intro x hx
                rw [G_numeral_eq_nil k A x hx]
                exact lt_of_le_of_ne (nil_le _) (fun h => hz h.symm)
            · by_cases e4 : dom B < cons A B nil
              · have hdX : dom (cons A B nil) = dom B := by rw [dom]; simp_all
                rw [hdX] at hY
                have hOTbY : OT (fs B Y) := (ih B (by omega)).2 hOTB Y hY hOTY
                have hZA : subOf (dom B) ≤ A := by
                  rcases dom_shape B with hd | hd | ⟨Z', hd⟩
                  · exact absurd hd e1
                  · exact absurd hd e3
                  · rw [hd] at e4 ⊢
                    simp only [subOf]
                    rcases psi_lt_psi_iff.mp (cons_lt_psi_iff.mp e4) with h | ⟨h, _⟩
                    · exact le_of_lt h
                    · exact h ▸ le_refl _
                have hYA : Y < psi A nil := by
                  refine lt_of_lt_of_le' hY ?_
                  rcases dom_shape B with hd | hd | ⟨Z', hd⟩
                  · exact absurd hd e1
                  · exact absurd hd e3
                  · rw [hd]
                    rw [hd] at hZA
                    simp only [subOf] at hZA
                    rcases le_iff_lt_or_eq.mp hZA with h | h
                    · exact le_of_lt (psi_lt_psi_iff.mpr (Or.inl h))
                    · exact h ▸ le_refl _
                rw [show fs (cons A B nil) Y = psi A (fs B Y) from by rw [fs]; simp_all]
                have hGA : G A Y = [] := G_eq_nil_of_lt_psi Y A hOTY hYA
                refine OT_psi_fs hOT (T36 B (by simp only [size_cons]; omega) hOTB Y hY) ?_ hOTbY
                intro x hx
                rw [hGA] at hx
                exact absurd hx List.not_mem_nil
              · have hdX : dom (cons A B nil) = tw := by rw [dom]; simp_all
                rw [hdX] at hY
                obtain ⟨k, rfl⟩ := eq_numeral_of_lt_tw hOTY hY
                have hdB : dom B = psi (subOf (dom B)) nil := by
                  rcases dom_shape B with h | h | ⟨Z, h⟩
                  · exact absurd h e1
                  · exact absurd h e3
                  · rw [h]; rfl
                have hZne : subOf (dom B) ≠ nil := subOf_dom_ne_nil e1 e2 e3
                have hOTZ : OT (subOf (dom B)) := OT_subOf_dom hOTB e1 e3
                have hZdom : nil < dom (subOf (dom B)) :=
                  lt_of_le_of_ne (nil_le _) (fun h => dom_ne_nil hZne h.symm)
                have hszZ : size (subOf (dom B)) < size B := size_subOf_dom_lt e1
                have hAZ : A ≤ subOf (dom B) := by
                  rcases lt_trichotomy (subOf (dom B)) A with h | h | h
                  · refine absurd ?_ e4
                    rw [hdB]
                    exact cons_lt_cons_iff.mpr (Or.inl (psi_lt_psi_iff.mpr (Or.inl h)))
                  · exact h ▸ le_refl _
                  · exact le_of_lt h
                have hAltZ : A < subOf (dom B) := by
                  rcases le_iff_lt_or_eq.mp hAZ with h | h
                  · exact h
                  · refine absurd ?_ e4
                    rw [hdB, ← h]
                    refine cons_lt_cons_iff.mpr (Or.inl (psi_lt_psi_iff.mpr (Or.inr ⟨rfl, ?_⟩)))
                    exact lt_of_le_of_ne (nil_le B) (fun hb => e1 (by rw [← hb]; rfl))
                have hdZ : dom (subOf (dom B)) = t1 :=
                  dom_sub_dom_eq_one B (subOf (dom B)) hdB e2
                have hOTZ0 : OT (fs (subOf (dom B)) nil) :=
                  (ih (subOf (dom B)) (by omega)).2 hOTZ nil hZdom rfl
                have hTZ : Trian nil (fs (subOf (dom B)) nil) (subOf (dom B)) :=
                  T36 (subOf (dom B)) (by simp only [size_cons]; omega) hOTZ nil hZdom
                have hW := towerOT_of_Bachmann hOT e1 e2 e3 hAZ
                  (le_pred_of_lt hOTZ hdZ hAltZ) (HB A B hOT e1 e2 e3 e4) hOTZ0
                  (fun W hW hOTW => (ih B (by omega)).2 hOTB W hW hOTW)
                  (fun W hW => T36 B (by simp only [size_cons]; omega) hOTB W hW)
                  hTZ k
                have hWlt := tower_lt_dom e1 e2 e3 k
                have hOTbW : OT (fs B (tower (fs (subOf (dom B)) nil) B k)) :=
                  (ih B (by omega)).2 hOTB _ hWlt hW.1
                rw [fs_numeral e1 e2 e3 e4 k]
                exact OT_psi_fs hOT
                  (T36 B (by simp only [size_cons]; omega) hOTB _ hWlt) hW.2 hOTbW

/-- **Buchholz 3.3** for the extended system, from the tower invariant of his
case 4. -/
theorem OTFS_of_Bachmann (HB : Bachmann) : OTFS :=
  fun X Y hOT hY hOTY => (OTFS_aux HB (size X) X (Nat.le_refl _)).2 hOT Y hY hOTY

/-- **Buchholz 3.6** for the extended system, from the same. -/
theorem Trian_fs_of_Bachmann (HB : Bachmann) {X Y : Term} (hOT : OT X) (h : Y < dom X) :
    Trian Y (fs X Y) X :=
  Trian_fs (OTFS_of_Bachmann HB) hOT h

end Googology.Notation.ExBuchholz.Term

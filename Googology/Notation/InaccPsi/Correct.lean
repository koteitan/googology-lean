import Googology.Notation.InaccPsi.Term

/-!
# Correctness of the comparison

For every `S : InaccSeq` and all normal forms `a, b`:

* `Term.cmp_eq_compare`: `cmp a b = compare |a| |b|`;
* `Term.eq_of_val_eq`: `|a| = |b| → a = b`;
* `Term.isWellOrder_cmp`: `cmp · · = .lt` is a well-order on normal forms.

The proof has three parts.

1. `Sem S t` collects the value facts that the normal form of `t` gives for its
   collapses: `|a| ∈ Cl(|a|, ψ_κ(|a|))` for every subterm `ψ_κ(a)`. These are the
   hypotheses of F12 (`InaccSeq.psi_lt_psi`).
2. `exact_of_sem`: `cmp` is exact on pairs of normal forms that satisfy `Sem`. Strong
   induction on the sum of the sizes, one case per clause of `cmp`. The Veblen clauses
   are identities of ordinals; the clauses for collapses use F9, F10 and F12.
3. `sem_of_NF`: every normal form satisfies `Sem`. Induction on the term; the normal
   form condition `K_μ(a) < a` gives `|a| ∈ Cl(|a|, |μ|)` by the soundness of `K`
   (`KLt_sound`). The bound `μ` is the collapse term itself (`ψ^S_s(a)` or `ψ^I_n(a)`),
   and only the direction `cmp x μ = .lt → |x| < |μ|` is needed (`lt_psiS_of_cmp`,
   `lt_psiI_of_cmp`).
-/

namespace Googology.Notation.InaccPsi

open Ordinal Set

universe u

/-! ## Ordinal lemmas -/

theorem compare_of_lt_iff {α β : Type*} [LinearOrder α] [LinearOrder β] {a b : α} {c d : β}
    (h1 : a < b ↔ c < d) (h2 : b < a ↔ d < c) :
    compare a b = compare c d := by
  rcases lt_trichotomy c d with h | h | h
  · rw [compare_lt_iff_lt.2 h, compare_lt_iff_lt.2 (h1.2 h)]
  · subst h
    rw [compare_eq_iff_eq.2 rfl, compare_eq_iff_eq.2
      (le_antisymm (not_lt.1 fun h' => lt_irrefl c (h2.1 h')) (not_lt.1 fun h' => lt_irrefl c (h1.1 h')))]
  · rw [compare_gt_iff_gt.2 h, compare_gt_iff_gt.2 (h2.2 h)]

theorem compare_strictMono {f : Ordinal.{u} → Ordinal.{u}} (hf : StrictMono f) (a b : Ordinal.{u}) :
    compare (f a) (f b) = compare a b :=
  compare_of_lt_iff hf.lt_iff_lt hf.lt_iff_lt

theorem SC.isSuccLimit {γ : Ordinal.{u}} (h : SC γ) : Order.IsSuccLimit γ :=
  Ordinal.isSuccLimit_iff.2 ⟨h.1.ne', Order.isSuccPrelimit_iff_succ_lt.2 fun x hx => by
    rw [Order.succ_eq_add_one]; exact h.add_one_lt hx⟩

/-- A strongly critical ordinal is additively principal. -/
theorem SC.isPrincipal {γ : Ordinal.{u}} (h : SC γ) : IsPrincipal (· + ·) γ := by
  intro x y hx hy
  have hm : max x y < γ := max_lt hx hy
  have hm1 := h.add_one_lt hm
  have hw : ω ^ (max x y + 1) < γ := by
    rw [← veblen_zero_apply]; exact h.2 0 h.1 _ hm1
  have hlt : ∀ z ≤ max x y, z < ω ^ (max x y + 1) := fun z hz =>
    lt_of_le_of_lt hz (lt_of_lt_of_le (by rw [← Order.succ_eq_add_one]; exact Order.lt_succ _)
      (right_le_opow _ one_lt_omega0))
  exact lt_trans (isPrincipal_add_omega0_opow _ (hlt x (le_max_left x y))
    (hlt y (le_max_right x y))) hw

/-- `φ(x, γ) = γ` for `x < γ` strongly critical. -/
theorem SC.veblen_right {γ x : Ordinal.{u}} (h : SC γ) (hx : x < γ) : veblen x γ = γ := by
  refine le_antisymm ?_ (right_le_veblen x γ)
  rw [(isNormal_veblen x).le_iff_forall_le h.isSuccLimit]
  intro y hy
  exact (h.2 x hx y hy).le

/-- `φ(γ, 0) = γ` for `γ` strongly critical. -/
theorem SC.veblen_zero {γ : Ordinal.{u}} (h : SC γ) : veblen γ 0 = γ := by
  obtain ⟨c, hc⟩ := (mem_range_veblen h.1.ne').2 fun b hb => h.veblen_right hb
  refine le_antisymm ?_ (left_le_veblen γ 0)
  calc veblen γ 0 ≤ veblen γ c := (veblen_right_strictMono γ).monotone zero_le
    _ = γ := hc

/-- The value of `φ` against a strongly critical `γ`, first argument below `γ`. -/
theorem SC.compare_veblen_of_lt {γ x y : Ordinal.{u}} (h : SC γ) (hx : x < γ) :
    compare (veblen x y) γ = compare y γ := by
  conv_lhs => rw [← h.veblen_right hx]
  exact compare_strictMono (veblen_right_strictMono x) y γ

theorem SC.compare_veblen_self {γ y : Ordinal.{u}} (h : SC γ) :
    compare (veblen γ y) γ = compare y 0 := by
  have := compare_strictMono (veblen_right_strictMono γ) y 0
  rwa [h.veblen_zero] at this

theorem Om_isPrincipal {v : Ordinal.{u}} (hv : v ≠ 0) : IsPrincipal (· + ·) (Om v) :=
  (SC_Om hv).isPrincipal

namespace InaccSeq

variable {S : InaccSeq.{u}}

theorem Om_psiS_lt_Om (a s : Ordinal.{u}) {τ : Ordinal.{u}} :
    S.psi a (Om (s + 1)) < Om τ ↔ s < τ :=
  lt_Om_iff_of_between (psiS_bounds a s).1 (psiS_bounds a s).2

theorem Om_lt_psiS (a s : Ordinal.{u}) {τ : Ordinal.{u}} :
    Om τ < S.psi a (Om (s + 1)) ↔ τ ≤ s :=
  Om_lt_iff_of_between (psiS_bounds a s).1 (psiS_bounds a s).2

theorem psiI_lt_I (a : Ordinal.{u}) {n m : ℕ} (h : n ≤ m) : S.psi a (S.I n) < S.I m :=
  lt_of_lt_of_le (psi_lt (InR_I n) a) (S.strictMono.monotone h)

theorem I_lt_psiI_of_lt (a : Ordinal.{u}) {n m : ℕ} (h : m < n) : S.I m < S.psi a (S.I n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact lt_of_le_of_lt (S.strictMono.monotone (by omega)) (InaccSeq.I_lt_psiI a k)

theorem psiI_lt_psiI (a b : Ordinal.{u}) {n m : ℕ} (h : n < m) :
    S.psi a (S.I n) < S.psi b (S.I m) :=
  lt_trans (psiI_lt_I a le_rfl) (I_lt_psiI_of_lt b h)

theorem psiI_lt_Iw (a : Ordinal.{u}) (n : ℕ) : S.psi a (S.I n) < S.Iw :=
  lt_trans (psi_lt (InR_I n) a) (S.I_lt_Iw n)

/-- F12 in the form of a comparison: at arguments in their own closures, `ψ_κ` is
strictly increasing. -/
theorem compare_psi {κ a b : Ordinal.{u}} (hκ : S.InR κ) (ha : a ∈ S.CSet a (S.psi a κ))
    (hb : b ∈ S.CSet b (S.psi b κ)) : compare (S.psi a κ) (S.psi b κ) = compare a b :=
  compare_of_lt_iff
    ⟨fun h => by
      by_contra h'
      rcases (not_lt.1 h').lt_or_eq with h'' | h''
      · exact lt_asymm h (psi_lt_psi hκ h'' hb)
      · rw [h''] at h; exact lt_irrefl _ h,
     fun h => psi_lt_psi hκ h ha⟩
    ⟨fun h => by
      by_contra h'
      rcases (not_lt.1 h').lt_or_eq with h'' | h''
      · exact lt_asymm h (psi_lt_psi hκ h'' ha)
      · rw [h''] at h; exact lt_irrefl _ h,
     fun h => psi_lt_psi hκ h hb⟩

end InaccSeq

namespace Term

/-! ## Syntactic lemmas about `cmp` -/

theorem cmp_self : ∀ t : Term, cmp t t = .eq
  | zero => by simp only [cmp]
  | inacc n => by simp [cmp]
  | inaccW => by simp [cmp]
  | add a b => by simp only [cmp, cmp_self a, cmp_self b]
  | phi a b => by simp only [cmp, cmp_self a, cmp_self b]
  | om a => by simp only [cmp, cmp_self a]
  | psiS s a => by simp only [cmp, cmp_self s, cmp_self a]
  | psiI n a => by simp [cmp, cmp_self a]

theorem cmp_zero_left {t : Term} (h : t ≠ zero) : cmp zero t = .lt := by
  cases t <;> simp_all [cmp]

theorem cmp_zero_right {t : Term} (h : t ≠ zero) : cmp t zero = .gt := by
  cases t <;> simp_all [cmp]

theorem cmp_add_add (a b c d : Term) :
    cmp (add a b) (add c d) = if cmp a c = .eq then cmp b d else cmp a c := by
  simp only [cmp]; split <;> simp_all

theorem cmp_add_left (a b : Term) {t : Term} (ht : t.isPrin = true) :
    cmp (add a b) t = if cmp a t = .lt then .lt else .gt := by
  cases t <;> simp [isPrin, isSC] at ht <;> simp only [cmp] <;> split <;> simp_all

theorem cmp_add_right (c d : Term) {t : Term} (ht : t.isPrin = true) :
    cmp t (add c d) = if cmp t c = .gt then .gt else .lt := by
  cases t <;> simp [isPrin, isSC] at ht <;> simp only [cmp] <;> split <;> simp_all

theorem cmp_phi_phi_lt {a b c d : Term} (h : cmp a c = .lt) :
    cmp (phi a b) (phi c d) = cmp b (phi c d) := by
  simp only [cmp, h]

theorem cmp_phi_phi_eq {a b c d : Term} (h : cmp a c = .eq) :
    cmp (phi a b) (phi c d) = cmp b d := by
  simp only [cmp, h]

theorem cmp_phi_phi_gt {a b c d : Term} (h : cmp a c = .gt) :
    cmp (phi a b) (phi c d) = cmp (phi a b) d := by
  simp only [cmp, h]

theorem cmp_phi_left_lt {a b t : Term} (ht : t.isSC = true) (h : cmp a t = .lt) :
    cmp (phi a b) t = cmp b t := by
  cases t <;> simp [isSC] at ht <;> simp only [cmp, h]

theorem cmp_phi_left_eq {a b t : Term} (ht : t.isSC = true) (h : cmp a t = .eq) :
    cmp (phi a b) t = cmp b zero := by
  cases t <;> simp [isSC] at ht <;> simp only [cmp, h]

theorem cmp_phi_left_gt {a b t : Term} (ht : t.isSC = true) (h : cmp a t = .gt) :
    cmp (phi a b) t = .gt := by
  cases t <;> simp [isSC] at ht <;> simp only [cmp, h]

theorem cmp_phi_right_gt {c d t : Term} (ht : t.isSC = true) (h : cmp t c = .gt) :
    cmp t (phi c d) = cmp t d := by
  cases t <;> simp [isSC] at ht <;> simp only [cmp, h]

theorem cmp_phi_right_eq {c d t : Term} (ht : t.isSC = true) (h : cmp t c = .eq) :
    cmp t (phi c d) = cmp zero d := by
  cases t <;> simp [isSC] at ht <;> simp only [cmp, h]

theorem cmp_phi_right_lt {c d t : Term} (ht : t.isSC = true) (h : cmp t c = .lt) :
    cmp t (phi c d) = .lt := by
  cases t <;> simp [isSC] at ht <;> simp only [cmp, h]

theorem cmp_om_F (a : Term) {f : Term} (hf : f.isF = true) : cmp (om a) f = cmp a f := by
  cases f <;> simp [isF] at hf <;> simp only [cmp]

theorem cmp_F_om (a : Term) {f : Term} (hf : f.isF = true) : cmp f (om a) = cmp f a := by
  cases f <;> simp [isF] at hf <;> simp only [cmp]

theorem cmp_psiS_psiS (s a t b : Term) :
    cmp (psiS s a) (psiS t b) = if cmp s t = .eq then cmp a b else cmp s t := by
  simp only [cmp]; split <;> simp_all

theorem cmp_psiS_K (s a : Term) {k : Term} (hk : k.isK = true) :
    cmp (psiS s a) k = if cmp (cardT s) k = .lt then .lt else .gt := by
  cases k <;> simp [isK, isF] at hk <;> simp only [cmp] <;> split <;> simp_all

theorem cmp_K_psiS (s a : Term) {k : Term} (hk : k.isK = true) :
    cmp k (psiS s a) = if cmp k (cardT s) = .gt then .gt else .lt := by
  cases k <;> simp [isK, isF] at hk <;> simp only [cmp] <;> split <;> simp_all

theorem cmp_psiI_psiI (n m : ℕ) (a b : Term) :
    cmp (psiI n a) (psiI m b) = if n = m then cmp a b else compare n m := by
  simp only [cmp]
  split_ifs with h
  · subst h; simp
  · split <;> simp_all

/-- `φ(t, 0)` is not normal for a strongly critical term `t`. -/
theorem cmp_phi_zero {t : Term} (ht : t.isSC = true) : cmp t (phi t zero) = .eq := by
  rw [cmp_phi_right_eq ht (cmp_self t)]; simp only [cmp]

/-- `φ(a, t)` is not normal for a strongly critical term `t > a`. -/
theorem cmp_phi_fix {a t : Term} (ht : t.isSC = true) (h : cmp t a = .gt) :
    cmp t (phi a t) = .eq := by
  rw [cmp_phi_right_gt ht h, cmp_self]

/-- `φ(a, φ(c, d))` is not normal for `a < c`. -/
theorem cmp_phi_phi_fix {a c d : Term} (h : cmp c a = .gt) :
    cmp (phi c d) (phi a (phi c d)) = .eq := by
  rw [cmp_phi_phi_gt h, cmp_self]

/-! ## Sizes, heads, `cardT` -/

theorem size_head_le (t : Term) : (head t).size ≤ t.size := by
  cases t <;> simp [head, size]
  omega

theorem NF.head {t : Term} (h : NF t) : NF (head t) := by
  cases t <;> simp only [Term.head] <;> first | exact h | exact h.1

theorem NF.ne_zero_of_isPrin {t : Term} (h : t.isPrin = true) : t ≠ zero := by
  rintro rfl; simp [isPrin, isSC] at h

theorem NF_cardT {s : Term} (h : NF s) : NF (cardT s) := by
  unfold cardT
  split_ifs with h0 hF
  · trivial
  · exact h
  · exact ⟨h, h0, by simpa using hF⟩

theorem size_cardT_lt (s a : Term) : (cardT s).size < (psiS s a).size := by
  have := size_cardT_le s; have := size_pos a; simp only [size]; omega

theorem isPrin_of_isSC {t : Term} (h : t.isSC = true) : t.isPrin = true := by
  cases t <;> simp_all [isPrin, isSC]

theorem isSC_of_isK {t : Term} (h : t.isK = true) : t.isSC = true := by
  cases t <;> simp_all [isK, isF, isSC]

theorem isK_of_isF {t : Term} (h : t.isF = true) : t.isK = true := by
  cases t <;> simp_all [isK, isF]

/-! ## Values -/

variable (S : InaccSeq.{u})

theorem Om_val_of_isF {t : Term} (h : t.isF = true) : Om (val S t) = val S t := by
  cases t <;> simp [isF] at h <;> simp only [val]
  · exact S.fix _
  · exact S.Om_Iw
  · exact InaccSeq.Om_psiI _ _

theorem val_cardT (s : Term) : val S (cardT s) = Om (val S s) := by
  unfold cardT
  split_ifs with h0 hF
  · subst h0; simp [val]
  · exact (Om_val_of_isF S hF).symm
  · rfl

theorem exists_Om_of_isK {t : Term} (h : t.isK = true) : ∃ κ, val S t = Om κ := by
  cases t <;> simp [isK, isF] at h
  · exact ⟨_, (Om_val_of_isF S (t := inacc _) rfl).symm⟩
  · exact ⟨_, (Om_val_of_isF S (t := inaccW) rfl).symm⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, (Om_val_of_isF S (t := psiI _ _) rfl).symm⟩

theorem val_ne_zero : ∀ {t : Term}, NF t → t ≠ zero → val S t ≠ 0
  | zero, _, h => absurd rfl h
  | inacc n, _, _ => S.I_ne_zero n
  | inaccW, _, _ => S.Iw_ne_zero
  | add a b, h, _ => by
    have ha := val_ne_zero h.1 (NF.ne_zero_of_isPrin h.2.2.1)
    simp only [val]
    exact fun e => ha (le_antisymm (e ▸ le_self_add) zero_le)
  | phi a b, _, _ => veblen_pos.ne'
  | om a, h, _ => (Om_pos (val_ne_zero h.1 h.2.1)).ne'
  | psiS s a, _, _ => (InaccSeq.SC_psi (InaccSeq.InR_Om_succ _) _).1.ne'
  | psiI n a, _, _ => (InaccSeq.SC_psi (InaccSeq.InR_I n) _).1.ne'

/-- **Strongly critical terms** have strongly critical values. -/
theorem SC_val {t : Term} (h : NF t) (ht : t.isSC = true) : SC (val S t) := by
  cases t <;> simp [isSC] at ht <;> simp only [val]
  · rw [← S.fix]; exact SC_Om (S.I_ne_zero _)
  · rw [← S.Om_Iw]; exact SC_Om S.Iw_ne_zero
  · exact SC_Om (val_ne_zero S h.1 h.2.1)
  · exact InaccSeq.SC_psi (InaccSeq.InR_Om_succ _) _
  · exact InaccSeq.SC_psi (InaccSeq.InR_I _) _

/-- **Principal terms** have additively principal values. -/
theorem isPrincipal_val {t : Term} (h : NF t) (ht : t.isPrin = true) :
    IsPrincipal (· + ·) (val S t) := by
  cases t with
  | phi a b =>
    obtain ⟨c, hc⟩ := veblen_mem_range_opow (val S a) (val S b)
    simp only [val]; rw [← hc]; exact isPrincipal_add_omega0_opow c
  | _ => exact (SC_val S h (by simpa [isPrin] using ht)).isPrincipal

/-- **Fixed-point terms** have values that are fixed points of `Ω`. -/
theorem Om_val_F {t : Term} (ht : t.isF = true) : Om (val S t) = val S t :=
  Om_val_of_isF S ht

/-- **F9** for `ψ^S`: `Ω_s < |ψ^S_s(a)| < Ω_{s+1}`. -/
theorem val_psiS_bounds (s a : Term) :
    Om (val S s) < val S (psiS s a) ∧ val S (psiS s a) < Om (val S s + 1) :=
  InaccSeq.psiS_bounds _ _

/-- **F10** for `ψ^I`: `|ψ^I_n(a)|` is a fixed point of `Ω` below `I_n`, above `Ω_1`, and
above `I_m` for `m < n`. -/
theorem val_psiI_bounds (n : ℕ) (a : Term) :
    Om (val S (psiI n a)) = val S (psiI n a) ∧ val S (psiI n a) < S.I n ∧
      Om 1 < val S (psiI n a) ∧ ∀ m < n, S.I m < val S (psiI n a) :=
  ⟨InaccSeq.Om_psiI _ _, InaccSeq.psi_lt (InaccSeq.InR_I n) _, InaccSeq.Om_one_lt_psiI _ _,
    fun _ hm => InaccSeq.I_lt_psiI_of_lt _ hm⟩

/-! ## The value facts of a normal form -/

/-- `Sem S t`: for every collapse `ψ_κ(a)` in `t`, `|a| ∈ Cl(|a|, ψ_κ(|a|))`. -/
def Sem : Term → Prop
  | zero => True
  | inacc _ => True
  | inaccW => True
  | add a b => Sem a ∧ Sem b
  | phi a b => Sem a ∧ Sem b
  | om a => Sem a
  | psiS s a => Sem s ∧ Sem a ∧
      val S a ∈ S.CSet (val S a) (S.psi (val S a) (Om (val S s + 1)))
  | psiI n a => Sem a ∧ val S a ∈ S.CSet (val S a) (S.psi (val S a) (S.I n))

variable {S}

theorem Sem.head {t : Term} (h : Sem S t) : Sem S (head t) := by
  cases t <;> simp only [Term.head] <;> first | exact h | exact h.1

theorem Sem_cardT {s : Term} (h : Sem S s) : Sem S (cardT s) := by
  unfold cardT
  split_ifs
  · trivial
  · exact h
  · exact h

/-! ## Exactness of `cmp` on pairs with `Sem` -/

/-- `cmp` is right on the pair `(x, y)`, and equal values mean equal terms. -/
def Ok (S : InaccSeq.{u}) (x y : Term) : Prop :=
  cmp x y = compare (val S x) (val S y) ∧ (val S x = val S y → x = y)

/-- `cmp` is right on all pairs of normal forms with `Sem` of total size `< N`. -/
def Exact (S : InaccSeq.{u}) (N : ℕ) : Prop :=
  ∀ x y : Term, x.size + y.size < N → NF x → NF y → Sem S x → Sem S y → Ok S x y

/-- Sizes of subterms. -/
local macro "sz" : tactic => `(tactic| (simp only [size] at *; omega))

theorem compare_swap_of_eq {a b c d : Ordinal.{u}} (h : compare a b = compare c d) :
    compare b a = compare d c :=
  compare_of_lt_iff
    ⟨fun h' => compare_gt_iff_gt.1 (h ▸ compare_gt_iff_gt.2 h'),
     fun h' => compare_gt_iff_gt.1 (h.symm ▸ compare_gt_iff_gt.2 h')⟩
    ⟨fun h' => compare_lt_iff_lt.1 (h ▸ compare_lt_iff_lt.2 h'),
     fun h' => compare_lt_iff_lt.1 (h.symm ▸ compare_lt_iff_lt.2 h')⟩

theorem ok_of {x y : Term} (hlt : val S x < val S y → cmp x y = .lt)
    (hgt : val S y < val S x → cmp x y = .gt)
    (heq : val S x = val S y → cmp x y = .eq ∧ x = y) : Ok S x y := by
  rcases lt_trichotomy (val S x) (val S y) with h | h | h
  · exact ⟨by rw [hlt h, compare_lt_iff_lt.2 h], fun e => absurd e h.ne⟩
  · exact ⟨by rw [(heq h).1, compare_eq_iff_eq.2 h], fun _ => (heq h).2⟩
  · exact ⟨by rw [hgt h, compare_gt_iff_gt.2 h], fun e => absurd e h.ne'⟩

/-- **The sum lemma.** A normal sum is below every additively principal ordinal above its
first summand. -/
theorem val_lt_of_head_lt {N : ℕ} (ih : Exact S N) :
    ∀ {t : Term}, t.size ≤ N → NF t → Sem S t → ∀ {P : Ordinal.{u}}, IsPrincipal (· + ·) P →
      val S (head t) < P → val S t < P
  | add c d, hN, h, hs, P, hP, hc => by
    obtain ⟨hc', hd, _, _, hh⟩ := h
    have e := (ih (head d) c (by have := size_head_le d; sz) hd.head hc' hs.2.head hs.1).1
    have hle : val S (head d) ≤ val S c := by
      rw [e] at hh; exact not_lt.1 fun h' => hh (compare_gt_iff_gt.2 h')
    simp only [Term.head] at hc
    simp only [val]
    exact hP hc (val_lt_of_head_lt ih (by sz) hd hs.2 hP (lt_of_le_of_lt hle hc))
  | zero, _, _, _, _, _, hc => hc
  | inacc _, _, _, _, _, _, hc => hc
  | inaccW, _, _, _, _, _, hc => hc
  | phi _ _, _, _, _, _, _, hc => hc
  | om _, _, _, _, _, _, hc => hc
  | psiS _ _, _, _, _, _, _, hc => hc
  | psiI _ _, _, _, _, _, _, hc => hc

variable {N : ℕ}

/-! ### `0` -/

theorem ok_zero_zero (_ih : Exact S N) (_hN : zero.size + zero.size ≤ N) (_hx : NF zero)
    (_hy : NF zero) (_sx : Sem S zero) (_sy : Sem S zero) : Ok S zero zero :=
  ⟨by simp only [cmp, val]; exact (compare_eq_iff_eq.2 rfl).symm, fun _ => rfl⟩

theorem ok_zero_left {t : Term} (_ih : Exact S N) (_hN : zero.size + t.size ≤ N)
    (_hx : NF zero) (hy : NF t) (_sx : Sem S zero) (_sy : Sem S t) (ht : t ≠ zero) :
    Ok S zero t := by
  have h := pos_iff_ne_zero.2 (val_ne_zero S hy ht)
  refine ⟨?_, fun e => absurd e h.ne⟩
  rw [cmp_zero_left ht]; exact (compare_lt_iff_lt.2 h).symm

theorem ok_zero_right {t : Term} (_ih : Exact S N) (_hN : t.size + zero.size ≤ N)
    (hx : NF t) (_hy : NF zero) (_sx : Sem S t) (_sy : Sem S zero) (ht : t ≠ zero) :
    Ok S t zero := by
  have h := pos_iff_ne_zero.2 (val_ne_zero S hx ht)
  refine ⟨?_, fun e => absurd e h.ne'⟩
  rw [cmp_zero_right ht]; exact (compare_gt_iff_gt.2 h).symm

/-! ### Sums -/

theorem ok_add_add (ih : Exact S N) {a b c d : Term}
    (hN : (add a b).size + (add c d).size ≤ N) (hx : NF (add a b)) (hy : NF (add c d))
    (sx : Sem S (add a b)) (sy : Sem S (add c d)) : Ok S (add a b) (add c d) := by
  have eac := ih a c (by sz) hx.1 hy.1 sx.1 sy.1
  have ebd := ih b d (by sz) hx.2.1 hy.2.1 sx.2 sy.2
  have h1 : val S a < val S c → val S (add a b) < val S (add c d) := fun h =>
    lt_of_lt_of_le (val_lt_of_head_lt ih (by sz) hx sx (isPrincipal_val S hy.1 hy.2.2.1) h)
      le_self_add
  have h2 : val S c < val S a → val S (add c d) < val S (add a b) := fun h =>
    lt_of_lt_of_le (val_lt_of_head_lt ih (by sz) hy sy (isPrincipal_val S hx.1 hx.2.2.1) h)
      le_self_add
  rw [Ok, cmp_add_add, eac.1]
  rcases lt_trichotomy (val S a) (val S c) with h | h | h
  · rw [compare_lt_iff_lt.2 h, if_neg (by decide), compare_lt_iff_lt.2 (h1 h)]
    exact ⟨rfl, fun e => absurd e (h1 h).ne⟩
  · obtain rfl := eac.2 h
    rw [compare_eq_iff_eq.2 rfl, if_pos rfl, ebd.1]
    refine ⟨compare_of_lt_iff (add_lt_add_iff_left _).symm (add_lt_add_iff_left _).symm,
      fun e => ?_⟩
    simp only [val] at e
    rw [ebd.2 (add_left_cancel e)]
  · rw [compare_gt_iff_gt.2 h, if_neg (by decide), compare_gt_iff_gt.2 (h2 h)]
    exact ⟨rfl, fun e => absurd e (h2 h).ne'⟩

theorem ok_add_prin (ih : Exact S N) {a b t : Term}
    (hN : (add a b).size + t.size ≤ N) (hx : NF (add a b)) (hy : NF t)
    (sx : Sem S (add a b)) (sy : Sem S t) (ht : t.isPrin = true) :
    Ok S (add a b) t ∧ Ok S t (add a b) := by
  have e1 := ih a t (by sz) hx.1 hy sx.1 sy
  have e2 := ih t a (by sz) hy hx.1 sy sx.1
  have hP : val S a < val S t → val S (add a b) < val S t := fun h =>
    val_lt_of_head_lt ih (by sz) hx sx (isPrincipal_val S hy ht) h
  have hQ : val S t ≤ val S a → val S t < val S (add a b) := fun h =>
    lt_of_le_of_lt h (lt_add_of_pos_right _ (pos_iff_ne_zero.2 (val_ne_zero S hx.2.1 hx.2.2.2.1)))
  constructor
  · rw [Ok, cmp_add_left a b ht, e1.1]
    by_cases h : val S a < val S t
    · rw [if_pos (compare_lt_iff_lt.2 h), compare_lt_iff_lt.2 (hP h)]
      exact ⟨rfl, fun e => absurd e (hP h).ne⟩
    · rw [if_neg (fun h' => h (compare_lt_iff_lt.1 h')), compare_gt_iff_gt.2 (hQ (not_lt.1 h))]
      exact ⟨rfl, fun e => absurd e (hQ (not_lt.1 h)).ne'⟩
  · rw [Ok, cmp_add_right a b ht, e2.1]
    by_cases h : val S a < val S t
    · rw [if_pos (compare_gt_iff_gt.2 h), compare_gt_iff_gt.2 (hP h)]
      exact ⟨rfl, fun e => absurd e (hP h).ne'⟩
    · rw [if_neg (fun h' => h (compare_gt_iff_gt.1 h')), compare_lt_iff_lt.2 (hQ (not_lt.1 h))]
      exact ⟨rfl, fun e => absurd e (hQ (not_lt.1 h)).ne⟩

theorem ok_add_prin_left (ih : Exact S N) {a b t : Term}
    (hN : (add a b).size + t.size ≤ N) (hx : NF (add a b)) (hy : NF t)
    (sx : Sem S (add a b)) (sy : Sem S t) (ht : t.isPrin = true) : Ok S (add a b) t :=
  (ok_add_prin ih hN hx hy sx sy ht).1

theorem ok_add_prin_right (ih : Exact S N) {a b t : Term}
    (hN : t.size + (add a b).size ≤ N) (hy : NF t) (hx : NF (add a b))
    (sy : Sem S t) (sx : Sem S (add a b)) (ht : t.isPrin = true) : Ok S t (add a b) :=
  (ok_add_prin ih (by omega) hx hy sx sy ht).2

/-! ### Veblen terms -/

theorem ok_phi_phi (ih : Exact S N) {a b c d : Term}
    (hN : (phi a b).size + (phi c d).size ≤ N) (hx : NF (phi a b)) (hy : NF (phi c d))
    (sx : Sem S (phi a b)) (sy : Sem S (phi c d)) : Ok S (phi a b) (phi c d) := by
  have eac := ih a c (by sz) hx.1 hy.1 sx.1 sy.1
  have eca := ih c a (by sz) hy.1 hx.1 sy.1 sx.1
  rcases lt_trichotomy (val S a) (val S c) with h | h | h
  · have hc : cmp a c = .lt := by rw [eac.1]; exact compare_lt_iff_lt.2 h
    have e := ih b (phi c d) (by sz) hx.2.1 hy sx.2 sy
    have hv := veblen_veblen_of_lt h (val S d)
    refine ⟨?_, fun ev => ?_⟩
    · rw [cmp_phi_phi_lt hc, e.1]
      show compare (val S b) (veblen (val S c) (val S d)) =
        compare (veblen (val S a) (val S b)) (veblen (val S c) (val S d))
      conv_rhs => rw [← hv]
      exact (compare_strictMono (veblen_right_strictMono _) _ _).symm
    · exfalso
      simp only [val] at ev
      rw [← hv] at ev
      have hb := e.2 (veblen_injective _ ev)
      have h2 := hx.2.2.2
      rw [hb, cmp_phi_phi_fix (by rw [eca.1]; exact compare_gt_iff_gt.2 h)] at h2
      exact absurd h2 (by decide)
  · obtain rfl := eac.2 h
    have e := ih b d (by sz) hx.2.1 hy.2.1 sx.2 sy.2
    refine ⟨?_, fun ev => ?_⟩
    · rw [cmp_phi_phi_eq (cmp_self a), e.1]
      exact (compare_strictMono (veblen_right_strictMono _) _ _).symm
    · simp only [val] at ev
      rw [e.2 (veblen_injective _ ev)]
  · have hc : cmp a c = .gt := by rw [eac.1]; exact compare_gt_iff_gt.2 h
    have e := ih (phi a b) d (by sz) hx hy.2.1 sx sy.2
    have hv := veblen_veblen_of_lt h (val S b)
    refine ⟨?_, fun ev => ?_⟩
    · rw [cmp_phi_phi_gt hc, e.1]
      show compare (veblen (val S a) (val S b)) (val S d) =
        compare (veblen (val S a) (val S b)) (veblen (val S c) (val S d))
      conv_rhs => rw [← hv]
      exact (compare_strictMono (veblen_right_strictMono _) _ _).symm
    · exfalso
      simp only [val] at ev
      rw [← hv] at ev
      have hd := e.2 (veblen_injective _ ev)
      have h2 := hy.2.2.2
      rw [← hd, cmp_phi_phi_fix hc] at h2
      exact absurd h2 (by decide)

theorem ok_phi_sc (ih : Exact S N) {a b t : Term}
    (hN : (phi a b).size + t.size ≤ N) (hx : NF (phi a b)) (hy : NF t)
    (sx : Sem S (phi a b)) (sy : Sem S t) (ht : t.isSC = true) :
    Ok S (phi a b) t ∧ Ok S t (phi a b) := by
  have hγ := SC_val S hy ht
  have := size_pos a
  have := size_pos t
  have eat := ih a t (by sz) hx.1 hy sx.1 sy
  have eta := ih t a (by sz) hy hx.1 sy sx.1
  have ebt := ih b t (by sz) hx.2.1 hy sx.2 sy
  have etb := ih t b (by sz) hy hx.2.1 sy sx.2
  have eb0 := ih b zero (by sz) hx.2.1 trivial sx.2 trivial
  have e0b := ih zero b (by sz) trivial hx.2.1 trivial sx.2
  have hv : val S (phi a b) = veblen (val S a) (val S b) := rfl
  rcases lt_trichotomy (val S a) (val S t) with h | h | h
  · have hc1 : cmp a t = .lt := by rw [eat.1]; exact compare_lt_iff_lt.2 h
    have hc2 : cmp t a = .gt := by rw [eta.1]; exact compare_gt_iff_gt.2 h
    have hcomp : compare (val S (phi a b)) (val S t) = compare (val S b) (val S t) :=
      hγ.compare_veblen_of_lt h
    have hinj : val S (phi a b) = val S t → False := fun ev => by
      have hb := ebt.2 (compare_eq_iff_eq.1 (hcomp ▸ compare_eq_iff_eq.2 ev))
      have h2 := hx.2.2.2
      rw [hb, cmp_phi_fix ht hc2] at h2
      exact absurd h2 (by decide)
    refine ⟨⟨by rw [cmp_phi_left_lt ht hc1, ebt.1, hcomp], fun ev => (hinj ev).elim⟩,
      ⟨by rw [cmp_phi_right_gt ht hc2, etb.1, compare_swap_of_eq hcomp],
        fun ev => (hinj ev.symm).elim⟩⟩
  · obtain rfl := eat.2 h
    have hcomp : compare (val S (phi a b)) (val S a) = compare (val S b) 0 :=
      hγ.compare_veblen_self
    have hinj : val S (phi a b) = val S a → False := fun ev => by
      have hb := eb0.2 (compare_eq_iff_eq.1 (hcomp ▸ compare_eq_iff_eq.2 ev))
      have h2 := hx.2.2.1
      rw [hb, cmp_phi_zero ht] at h2
      exact absurd h2 (by decide)
    refine ⟨⟨by rw [cmp_phi_left_eq ht (cmp_self a), eb0.1, hcomp]; rfl,
        fun ev => (hinj ev).elim⟩,
      ⟨by rw [cmp_phi_right_eq ht (cmp_self a), e0b.1, compare_swap_of_eq hcomp]; rfl,
        fun ev => (hinj ev.symm).elim⟩⟩
  · have hc1 : cmp a t = .gt := by rw [eat.1]; exact compare_gt_iff_gt.2 h
    have hc2 : cmp t a = .lt := by rw [eta.1]; exact compare_lt_iff_lt.2 h
    have hlt : val S t < val S (phi a b) := lt_of_lt_of_le h (left_le_veblen _ _)
    exact ⟨⟨by rw [cmp_phi_left_gt ht hc1, compare_gt_iff_gt.2 hlt],
        fun ev => absurd ev hlt.ne'⟩,
      ⟨by rw [cmp_phi_right_lt ht hc2, compare_lt_iff_lt.2 hlt], fun ev => absurd ev hlt.ne⟩⟩

theorem ok_phi_sc_left (ih : Exact S N) {a b t : Term}
    (hN : (phi a b).size + t.size ≤ N) (hx : NF (phi a b)) (hy : NF t)
    (sx : Sem S (phi a b)) (sy : Sem S t) (ht : t.isSC = true) : Ok S (phi a b) t :=
  (ok_phi_sc ih hN hx hy sx sy ht).1

theorem ok_phi_sc_right (ih : Exact S N) {a b t : Term}
    (hN : t.size + (phi a b).size ≤ N) (hy : NF t) (hx : NF (phi a b))
    (sy : Sem S t) (sx : Sem S (phi a b)) (ht : t.isSC = true) : Ok S t (phi a b) :=
  (ok_phi_sc ih (by omega) hx hy sx sy ht).2

/-! ### `Ω` -/

theorem ok_om_om (ih : Exact S N) {a c : Term}
    (hN : (om a).size + (om c).size ≤ N) (hx : NF (om a)) (hy : NF (om c))
    (sx : Sem S (om a)) (sy : Sem S (om c)) : Ok S (om a) (om c) := by
  have e := ih a c (by sz) hx.1 hy.1 sx sy
  refine ⟨?_, fun ev => ?_⟩
  · simp only [cmp, val]; rw [e.1]; exact (compare_strictMono Om_strictMono _ _).symm
  · simp only [val] at ev; rw [e.2 (Om_inj.1 ev)]

theorem ok_om_F (ih : Exact S N) {a f : Term}
    (hN : (om a).size + f.size ≤ N) (hx : NF (om a)) (hy : NF f)
    (sx : Sem S (om a)) (sy : Sem S f) (hf : f.isF = true) :
    Ok S (om a) f ∧ Ok S f (om a) := by
  have e1 := ih a f (by sz) hx.1 hy sx sy
  have e2 := ih f a (by sz) hy hx.1 sy sx
  have hv := Om_val_F S hf
  have hcomp : compare (val S (om a)) (val S f) = compare (val S a) (val S f) := by
    show compare (Om (val S a)) (val S f) = _
    conv_lhs => rw [← hv]
    exact compare_strictMono Om_strictMono _ _
  have hinj : val S (om a) = val S f → False := fun ev => by
    have ha := e1.2 (compare_eq_iff_eq.1 (hcomp ▸ compare_eq_iff_eq.2 ev))
    have h3 := hx.2.2
    rw [ha, hf] at h3
    exact absurd h3 (by decide)
  refine ⟨⟨by rw [cmp_om_F a hf, e1.1, hcomp], fun ev => (hinj ev).elim⟩,
    ⟨by rw [cmp_F_om a hf, e2.1, compare_swap_of_eq hcomp], fun ev => (hinj ev.symm).elim⟩⟩

theorem ok_om_F_left (ih : Exact S N) {a f : Term}
    (hN : (om a).size + f.size ≤ N) (hx : NF (om a)) (hy : NF f)
    (sx : Sem S (om a)) (sy : Sem S f) (hf : f.isF = true) : Ok S (om a) f :=
  (ok_om_F ih hN hx hy sx sy hf).1

theorem ok_om_F_right (ih : Exact S N) {a f : Term}
    (hN : f.size + (om a).size ≤ N) (hy : NF f) (hx : NF (om a))
    (sy : Sem S f) (sx : Sem S (om a)) (hf : f.isF = true) : Ok S f (om a) :=
  (ok_om_F ih (by omega) hx hy sx sy hf).2

/-! ### `ψ^S` -/

theorem ok_psiS_psiS (ih : Exact S N) {s a t b : Term}
    (hN : (psiS s a).size + (psiS t b).size ≤ N) (hx : NF (psiS s a)) (hy : NF (psiS t b))
    (sx : Sem S (psiS s a)) (sy : Sem S (psiS t b)) : Ok S (psiS s a) (psiS t b) := by
  have est := ih s t (by sz) hx.1 hy.1 sx.1 sy.1
  have eab := ih a b (by sz) hx.2.1 hy.2.1 sx.2.1 sy.2.1
  have h1 : val S s < val S t → val S (psiS s a) < val S (psiS t b) := fun h =>
    lt_trans ((InaccSeq.Om_psiS_lt_Om _ _).2 h) (InaccSeq.psiS_bounds _ _).1
  have h2 : val S t < val S s → val S (psiS t b) < val S (psiS s a) := fun h =>
    lt_trans ((InaccSeq.Om_psiS_lt_Om _ _).2 h) (InaccSeq.psiS_bounds _ _).1
  rw [Ok, cmp_psiS_psiS, est.1]
  rcases lt_trichotomy (val S s) (val S t) with h | h | h
  · rw [compare_lt_iff_lt.2 h, if_neg (by decide), compare_lt_iff_lt.2 (h1 h)]
    exact ⟨rfl, fun e => absurd e (h1 h).ne⟩
  · obtain rfl := est.2 h
    have hc := InaccSeq.compare_psi (InaccSeq.InR_Om_succ (val S s)) sx.2.2 sy.2.2
    rw [compare_eq_iff_eq.2 rfl, if_pos rfl, eab.1]
    refine ⟨hc.symm, fun e => ?_⟩
    have := compare_eq_iff_eq.2 e
    simp only [val] at this
    rw [hc] at this
    rw [eab.2 (compare_eq_iff_eq.1 this)]
  · rw [compare_gt_iff_gt.2 h, if_neg (by decide), compare_gt_iff_gt.2 (h2 h)]
    exact ⟨rfl, fun e => absurd e (h2 h).ne'⟩

theorem ok_psiS_K (ih : Exact S N) {s a k : Term}
    (hN : (psiS s a).size + k.size ≤ N) (hx : NF (psiS s a)) (hy : NF k)
    (sx : Sem S (psiS s a)) (sy : Sem S k) (hk : k.isK = true) :
    Ok S (psiS s a) k ∧ Ok S k (psiS s a) := by
  have hsz := size_cardT_lt s a
  have e1 := ih (cardT s) k (by omega) (NF_cardT hx.1) hy (Sem_cardT sx.1) sy
  have e2 := ih k (cardT s) (by omega) hy (NF_cardT hx.1) sy (Sem_cardT sx.1)
  obtain ⟨κ, hκ⟩ := exists_Om_of_isK S hk
  have e1c := e1.1
  have e2c := e2.1
  rw [val_cardT, hκ] at e1c e2c
  have hv : val S (psiS s a) = S.psi (val S a) (Om (val S s + 1)) := rfl
  rw [Ok, Ok, cmp_psiS_K s a hk, cmp_K_psiS s a hk, e1c, e2c, hκ, hv]
  by_cases h : val S s < κ
  · have hl := (InaccSeq.Om_psiS_lt_Om (S := S) (val S a) (val S s)).2 h
    rw [if_pos (compare_lt_iff_lt.2 (Om_lt_Om.2 h)), if_pos (compare_gt_iff_gt.2 (Om_lt_Om.2 h)),
      compare_lt_iff_lt.2 hl, compare_gt_iff_gt.2 hl]
    exact ⟨⟨rfl, fun e => absurd e hl.ne⟩, ⟨rfl, fun e => absurd e hl.ne'⟩⟩
  · have hl := (InaccSeq.Om_lt_psiS (S := S) (val S a) (val S s)).2 (not_lt.1 h)
    rw [if_neg (fun h' => h (Om_lt_Om.1 (compare_lt_iff_lt.1 h'))),
      if_neg (fun h' => h (Om_lt_Om.1 (compare_gt_iff_gt.1 h'))),
      compare_gt_iff_gt.2 hl, compare_lt_iff_lt.2 hl]
    exact ⟨⟨rfl, fun e => absurd e hl.ne'⟩, ⟨rfl, fun e => absurd e hl.ne⟩⟩

theorem ok_psiS_K_left (ih : Exact S N) {s a k : Term}
    (hN : (psiS s a).size + k.size ≤ N) (hx : NF (psiS s a)) (hy : NF k)
    (sx : Sem S (psiS s a)) (sy : Sem S k) (hk : k.isK = true) : Ok S (psiS s a) k :=
  (ok_psiS_K ih hN hx hy sx sy hk).1

theorem ok_psiS_K_right (ih : Exact S N) {s a k : Term}
    (hN : k.size + (psiS s a).size ≤ N) (hy : NF k) (hx : NF (psiS s a))
    (sy : Sem S k) (sx : Sem S (psiS s a)) (hk : k.isK = true) : Ok S k (psiS s a) :=
  (ok_psiS_K ih (by omega) hx hy sx sy hk).2

/-! ### Fixed-point terms among themselves -/

theorem ok_inacc_inacc (_ih : Exact S N) {n m : ℕ}
    (_hN : (inacc n).size + (inacc m).size ≤ N) (_hx : NF (inacc n)) (_hy : NF (inacc m))
    (_sx : Sem S (inacc n)) (_sy : Sem S (inacc m)) : Ok S (inacc n) (inacc m) := by
  refine ⟨?_, fun e => ?_⟩
  · simp only [cmp, val]
    exact (compare_of_lt_iff S.strictMono.lt_iff_lt S.strictMono.lt_iff_lt).symm
  · simp only [val] at e; rw [S.strictMono.injective e]

theorem ok_inacc_inaccW (_ih : Exact S N) {n : ℕ}
    (_hN : (inacc n).size + inaccW.size ≤ N) (_hx : NF (inacc n)) (_hy : NF inaccW)
    (_sx : Sem S (inacc n)) (_sy : Sem S inaccW) : Ok S (inacc n) inaccW :=
  ok_of (fun _ => by simp only [cmp]) (fun h => absurd h (not_lt.2 (S.I_lt_Iw n).le))
    (fun h => absurd h (S.I_lt_Iw n).ne)

theorem ok_inaccW_inacc (_ih : Exact S N) {n : ℕ}
    (_hN : inaccW.size + (inacc n).size ≤ N) (_hx : NF inaccW) (_hy : NF (inacc n))
    (_sx : Sem S inaccW) (_sy : Sem S (inacc n)) : Ok S inaccW (inacc n) :=
  ok_of (fun h => absurd h (not_lt.2 (S.I_lt_Iw n).le)) (fun _ => by simp only [cmp])
    (fun h => absurd h (S.I_lt_Iw n).ne')

theorem ok_inaccW_inaccW (_ih : Exact S N)
    (_hN : inaccW.size + inaccW.size ≤ N) (_hx : NF inaccW) (_hy : NF inaccW)
    (_sx : Sem S inaccW) (_sy : Sem S inaccW) : Ok S inaccW inaccW :=
  ⟨by simp only [cmp]; exact (compare_eq_iff_eq.2 rfl).symm, fun _ => rfl⟩

theorem ok_psiI_psiI (ih : Exact S N) {n m : ℕ} {a b : Term}
    (hN : (psiI n a).size + (psiI m b).size ≤ N) (hx : NF (psiI n a)) (hy : NF (psiI m b))
    (sx : Sem S (psiI n a)) (sy : Sem S (psiI m b)) : Ok S (psiI n a) (psiI m b) := by
  rw [Ok, cmp_psiI_psiI]
  rcases lt_trichotomy n m with h | rfl | h
  · have hl := InaccSeq.psiI_lt_psiI (S := S) (val S a) (val S b) h
    rw [if_neg h.ne, compare_lt_iff_lt.2 h]
    exact ⟨(compare_lt_iff_lt.2 hl).symm, fun e => absurd e hl.ne⟩
  · have eab := ih a b (by sz) hx.1 hy.1 sx.1 sy.1
    have hc := InaccSeq.compare_psi (InaccSeq.InR_I n) sx.2 sy.2
    rw [if_pos rfl, eab.1]
    refine ⟨hc.symm, fun e => ?_⟩
    have := compare_eq_iff_eq.2 e
    simp only [val] at this
    rw [hc] at this
    rw [eab.2 (compare_eq_iff_eq.1 this)]
  · have hl := InaccSeq.psiI_lt_psiI (S := S) (val S b) (val S a) h
    rw [if_neg h.ne', compare_gt_iff_gt.2 h]
    exact ⟨(compare_gt_iff_gt.2 hl).symm, fun e => absurd e hl.ne'⟩

theorem ok_psiI_inacc (_ih : Exact S N) {n m : ℕ} {a : Term}
    (_hN : (psiI n a).size + (inacc m).size ≤ N) (_hx : NF (psiI n a)) (_hy : NF (inacc m))
    (_sx : Sem S (psiI n a)) (_sy : Sem S (inacc m)) :
    Ok S (psiI n a) (inacc m) := by
  by_cases h : n ≤ m
  · have hl := InaccSeq.psiI_lt_I (S := S) (val S a) h
    exact ⟨by simp only [cmp, if_pos h]; exact (compare_lt_iff_lt.2 hl).symm,
      fun e => absurd e hl.ne⟩
  · have hl := InaccSeq.I_lt_psiI_of_lt (S := S) (val S a) (not_le.1 h)
    exact ⟨by simp only [cmp, if_neg h]; exact (compare_gt_iff_gt.2 hl).symm,
      fun e => absurd e hl.ne'⟩

theorem ok_inacc_psiI (_ih : Exact S N) {n m : ℕ} {a : Term}
    (_hN : (inacc m).size + (psiI n a).size ≤ N) (_hx : NF (inacc m)) (_hy : NF (psiI n a))
    (_sx : Sem S (inacc m)) (_sy : Sem S (psiI n a)) :
    Ok S (inacc m) (psiI n a) := by
  by_cases h : n ≤ m
  · have hl := InaccSeq.psiI_lt_I (S := S) (val S a) h
    exact ⟨by simp only [cmp, if_pos h]; exact (compare_gt_iff_gt.2 hl).symm,
      fun e => absurd e hl.ne'⟩
  · have hl := InaccSeq.I_lt_psiI_of_lt (S := S) (val S a) (not_le.1 h)
    exact ⟨by simp only [cmp, if_neg h]; exact (compare_lt_iff_lt.2 hl).symm,
      fun e => absurd e hl.ne⟩

theorem ok_psiI_inaccW (_ih : Exact S N) {n : ℕ} {a : Term}
    (_hN : (psiI n a).size + inaccW.size ≤ N) (_hx : NF (psiI n a)) (_hy : NF inaccW)
    (_sx : Sem S (psiI n a)) (_sy : Sem S inaccW) : Ok S (psiI n a) inaccW :=
  ok_of (fun _ => by simp only [cmp])
    (fun h => absurd h (not_lt.2 (InaccSeq.psiI_lt_Iw (S := S) (val S a) n).le))
    (fun h => absurd h (InaccSeq.psiI_lt_Iw (S := S) (val S a) n).ne)

theorem ok_inaccW_psiI (_ih : Exact S N) {n : ℕ} {a : Term}
    (_hN : inaccW.size + (psiI n a).size ≤ N) (_hx : NF inaccW) (_hy : NF (psiI n a))
    (_sx : Sem S inaccW) (_sy : Sem S (psiI n a)) : Ok S inaccW (psiI n a) :=
  ok_of (fun h => absurd h (not_lt.2 (InaccSeq.psiI_lt_Iw (S := S) (val S a) n).le))
    (fun _ => by simp only [cmp])
    (fun h => absurd h (InaccSeq.psiI_lt_Iw (S := S) (val S a) n).ne')

/-! ### The induction step -/

theorem exact_step (ih : Exact S N) :
    ∀ x y : Term, x.size + y.size ≤ N → NF x → NF y → Sem S x → Sem S y → Ok S x y
  | zero, zero, hN, hx, hy, sx, sy =>
    ok_zero_zero ih hN hx hy sx sy
  | zero, inacc n2, hN, hx, hy, sx, sy =>
    ok_zero_left ih hN hx hy sx sy (by simp)
  | zero, inaccW, hN, hx, hy, sx, sy =>
    ok_zero_left ih hN hx hy sx sy (by simp)
  | zero, add a2 b2, hN, hx, hy, sx, sy =>
    ok_zero_left ih hN hx hy sx sy (by simp)
  | zero, phi a2 b2, hN, hx, hy, sx, sy =>
    ok_zero_left ih hN hx hy sx sy (by simp)
  | zero, om a2, hN, hx, hy, sx, sy =>
    ok_zero_left ih hN hx hy sx sy (by simp)
  | zero, psiS s2 a2, hN, hx, hy, sx, sy =>
    ok_zero_left ih hN hx hy sx sy (by simp)
  | zero, psiI n2 a2, hN, hx, hy, sx, sy =>
    ok_zero_left ih hN hx hy sx sy (by simp)
  | inacc n1, zero, hN, hx, hy, sx, sy =>
    ok_zero_right ih hN hx hy sx sy (by simp)
  | inacc n1, inacc n2, hN, hx, hy, sx, sy =>
    ok_inacc_inacc ih hN hx hy sx sy
  | inacc n1, inaccW, hN, hx, hy, sx, sy =>
    ok_inacc_inaccW ih hN hx hy sx sy
  | inacc n1, add a2 b2, hN, hx, hy, sx, sy =>
    ok_add_prin_right ih hN hx hy sx sy rfl
  | inacc n1, phi a2 b2, hN, hx, hy, sx, sy =>
    ok_phi_sc_right ih hN hx hy sx sy rfl
  | inacc n1, om a2, hN, hx, hy, sx, sy =>
    ok_om_F_right ih hN hx hy sx sy rfl
  | inacc n1, psiS s2 a2, hN, hx, hy, sx, sy =>
    ok_psiS_K_right ih hN hx hy sx sy rfl
  | inacc n1, psiI n2 a2, hN, hx, hy, sx, sy =>
    ok_inacc_psiI ih hN hx hy sx sy
  | inaccW, zero, hN, hx, hy, sx, sy =>
    ok_zero_right ih hN hx hy sx sy (by simp)
  | inaccW, inacc n2, hN, hx, hy, sx, sy =>
    ok_inaccW_inacc ih hN hx hy sx sy
  | inaccW, inaccW, hN, hx, hy, sx, sy =>
    ok_inaccW_inaccW ih hN hx hy sx sy
  | inaccW, add a2 b2, hN, hx, hy, sx, sy =>
    ok_add_prin_right ih hN hx hy sx sy rfl
  | inaccW, phi a2 b2, hN, hx, hy, sx, sy =>
    ok_phi_sc_right ih hN hx hy sx sy rfl
  | inaccW, om a2, hN, hx, hy, sx, sy =>
    ok_om_F_right ih hN hx hy sx sy rfl
  | inaccW, psiS s2 a2, hN, hx, hy, sx, sy =>
    ok_psiS_K_right ih hN hx hy sx sy rfl
  | inaccW, psiI n2 a2, hN, hx, hy, sx, sy =>
    ok_inaccW_psiI ih hN hx hy sx sy
  | add a1 b1, zero, hN, hx, hy, sx, sy =>
    ok_zero_right ih hN hx hy sx sy (by simp)
  | add a1 b1, inacc n2, hN, hx, hy, sx, sy =>
    ok_add_prin_left ih hN hx hy sx sy rfl
  | add a1 b1, inaccW, hN, hx, hy, sx, sy =>
    ok_add_prin_left ih hN hx hy sx sy rfl
  | add a1 b1, add a2 b2, hN, hx, hy, sx, sy =>
    ok_add_add ih hN hx hy sx sy
  | add a1 b1, phi a2 b2, hN, hx, hy, sx, sy =>
    ok_add_prin_left ih hN hx hy sx sy rfl
  | add a1 b1, om a2, hN, hx, hy, sx, sy =>
    ok_add_prin_left ih hN hx hy sx sy rfl
  | add a1 b1, psiS s2 a2, hN, hx, hy, sx, sy =>
    ok_add_prin_left ih hN hx hy sx sy rfl
  | add a1 b1, psiI n2 a2, hN, hx, hy, sx, sy =>
    ok_add_prin_left ih hN hx hy sx sy rfl
  | phi a1 b1, zero, hN, hx, hy, sx, sy =>
    ok_zero_right ih hN hx hy sx sy (by simp)
  | phi a1 b1, inacc n2, hN, hx, hy, sx, sy =>
    ok_phi_sc_left ih hN hx hy sx sy rfl
  | phi a1 b1, inaccW, hN, hx, hy, sx, sy =>
    ok_phi_sc_left ih hN hx hy sx sy rfl
  | phi a1 b1, add a2 b2, hN, hx, hy, sx, sy =>
    ok_add_prin_right ih hN hx hy sx sy rfl
  | phi a1 b1, phi a2 b2, hN, hx, hy, sx, sy =>
    ok_phi_phi ih hN hx hy sx sy
  | phi a1 b1, om a2, hN, hx, hy, sx, sy =>
    ok_phi_sc_left ih hN hx hy sx sy rfl
  | phi a1 b1, psiS s2 a2, hN, hx, hy, sx, sy =>
    ok_phi_sc_left ih hN hx hy sx sy rfl
  | phi a1 b1, psiI n2 a2, hN, hx, hy, sx, sy =>
    ok_phi_sc_left ih hN hx hy sx sy rfl
  | om a1, zero, hN, hx, hy, sx, sy =>
    ok_zero_right ih hN hx hy sx sy (by simp)
  | om a1, inacc n2, hN, hx, hy, sx, sy =>
    ok_om_F_left ih hN hx hy sx sy rfl
  | om a1, inaccW, hN, hx, hy, sx, sy =>
    ok_om_F_left ih hN hx hy sx sy rfl
  | om a1, add a2 b2, hN, hx, hy, sx, sy =>
    ok_add_prin_right ih hN hx hy sx sy rfl
  | om a1, phi a2 b2, hN, hx, hy, sx, sy =>
    ok_phi_sc_right ih hN hx hy sx sy rfl
  | om a1, om a2, hN, hx, hy, sx, sy =>
    ok_om_om ih hN hx hy sx sy
  | om a1, psiS s2 a2, hN, hx, hy, sx, sy =>
    ok_psiS_K_right ih hN hx hy sx sy rfl
  | om a1, psiI n2 a2, hN, hx, hy, sx, sy =>
    ok_om_F_left ih hN hx hy sx sy rfl
  | psiS s1 a1, zero, hN, hx, hy, sx, sy =>
    ok_zero_right ih hN hx hy sx sy (by simp)
  | psiS s1 a1, inacc n2, hN, hx, hy, sx, sy =>
    ok_psiS_K_left ih hN hx hy sx sy rfl
  | psiS s1 a1, inaccW, hN, hx, hy, sx, sy =>
    ok_psiS_K_left ih hN hx hy sx sy rfl
  | psiS s1 a1, add a2 b2, hN, hx, hy, sx, sy =>
    ok_add_prin_right ih hN hx hy sx sy rfl
  | psiS s1 a1, phi a2 b2, hN, hx, hy, sx, sy =>
    ok_phi_sc_right ih hN hx hy sx sy rfl
  | psiS s1 a1, om a2, hN, hx, hy, sx, sy =>
    ok_psiS_K_left ih hN hx hy sx sy rfl
  | psiS s1 a1, psiS s2 a2, hN, hx, hy, sx, sy =>
    ok_psiS_psiS ih hN hx hy sx sy
  | psiS s1 a1, psiI n2 a2, hN, hx, hy, sx, sy =>
    ok_psiS_K_left ih hN hx hy sx sy rfl
  | psiI n1 a1, zero, hN, hx, hy, sx, sy =>
    ok_zero_right ih hN hx hy sx sy (by simp)
  | psiI n1 a1, inacc n2, hN, hx, hy, sx, sy =>
    ok_psiI_inacc ih hN hx hy sx sy
  | psiI n1 a1, inaccW, hN, hx, hy, sx, sy =>
    ok_psiI_inaccW ih hN hx hy sx sy
  | psiI n1 a1, add a2 b2, hN, hx, hy, sx, sy =>
    ok_add_prin_right ih hN hx hy sx sy rfl
  | psiI n1 a1, phi a2 b2, hN, hx, hy, sx, sy =>
    ok_phi_sc_right ih hN hx hy sx sy rfl
  | psiI n1 a1, om a2, hN, hx, hy, sx, sy =>
    ok_om_F_right ih hN hx hy sx sy rfl
  | psiI n1 a1, psiS s2 a2, hN, hx, hy, sx, sy =>
    ok_psiS_K_right ih hN hx hy sx sy rfl
  | psiI n1 a1, psiI n2 a2, hN, hx, hy, sx, sy =>
    ok_psiI_psiI ih hN hx hy sx sy

theorem exact_all : ∀ N, Exact S N
  | 0 => fun _ _ h => absurd h (Nat.not_lt_zero _)
  | N + 1 => fun x y h => exact_step (exact_all N) x y (by omega)

/-- `cmp` is exact on normal forms with `Sem`. -/
theorem ok_of_sem {x y : Term} (hx : NF x) (hy : NF y) (sx : Sem S x) (sy : Sem S y) :
    Ok S x y :=
  exact_all _ x y (Nat.lt_succ_self _) hx hy sx sy

/-! ## Soundness of `K` -/

theorem cmp_zero_right_ne_lt (t : Term) : cmp t zero ≠ .lt := by
  cases t <;> simp [cmp]

/-- **Soundness of `K`.** If every comparison with `μ` and with `α` that `KLt` performs is
right in the direction `.lt`, then `K_μ(t) < α` gives `|t| ∈ Cl(|α|, |μ|)`. -/
theorem KLt_sound {μ α : Term}
    (hμ : ∀ x, NF x → Sem S x → cmp x μ = .lt → val S x < val S μ)
    (hα : ∀ y, NF y → Sem S y → cmp y α = .lt → val S y < val S α) :
    ∀ {t : Term}, NF t → Sem S t → KLt μ t α → val S t ∈ S.CSet (val S α) (val S μ)
  | zero, _, _, _ => InaccSeq.CSet.zero_mem _ _
  | inacc n, _, _, _ => InaccSeq.CSet.I_mem _ _ n
  | inaccW, _, _, _ => InaccSeq.CSet.Iw_mem _ _
  | add _ _, h, s, k =>
    InaccSeq.CSet.add_mem (KLt_sound hμ hα h.1 s.1 k.1) (KLt_sound hμ hα h.2.1 s.2 k.2)
  | phi _ _, h, s, k =>
    InaccSeq.CSet.phi_mem (KLt_sound hμ hα h.1 s.1 k.1) (KLt_sound hμ hα h.2.1 s.2 k.2)
  | om _, h, s, k => by
    rcases k with k | k
    · exact InaccSeq.CSet.of_lt (hμ _ h s k)
    · exact InaccSeq.CSet.Om_mem (KLt_sound hμ hα h.1 s k)
  | psiS _ _, h, s, k => by
    rcases k with k | ⟨hb, ks, kb⟩
    · exact InaccSeq.CSet.of_lt (hμ _ h s k)
    · exact InaccSeq.CSet.psi_mem (hα _ h.2.1 s.2.1 hb) (InaccSeq.InR_Om_succ _)
        (InaccSeq.CSet.Om_mem (InaccSeq.CSet.succ_mem (KLt_sound hμ hα h.1 s.1 ks)))
        (KLt_sound hμ hα h.2.1 s.2.1 kb)
  | psiI n _, h, s, k => by
    rcases k with k | ⟨hb, kb⟩
    · exact InaccSeq.CSet.of_lt (hμ _ h s k)
    · exact InaccSeq.CSet.psi_mem (hα _ h.1 s.1 hb) (InaccSeq.InR_I n)
        (InaccSeq.CSet.I_mem _ _ n) (KLt_sound hμ hα h.1 s.1 kb)

theorem lt_of_cmp_lt {x y : Term} (hx : NF x) (hy : NF y) (sx : Sem S x) (sy : Sem S y)
    (h : cmp x y = .lt) : val S x < val S y := by
  rw [(ok_of_sem hx hy sx sy).1] at h; exact compare_lt_iff_lt.1 h

/-- The comparisons with the bound `μ = ψ^I_n(a)` of the normal form of `ψ^I_n(a)` are
right in the direction `.lt`, without `Sem` for `ψ^I_n(a)` itself. -/
theorem lt_psiI_of_cmp {n : ℕ} {a : Term} (ha : NF a) (sa : Sem S a) :
    ∀ {x : Term}, NF x → Sem S x → cmp x (psiI n a) = .lt → val S x < val S (psiI n a)
  | zero, _, _, _ => (InaccSeq.SC_psi (InaccSeq.InR_I n) _).1
  | inacc m, _, _, h => by
    have hnm : ¬ n ≤ m := fun hnm => by simp [cmp, hnm] at h
    exact InaccSeq.I_lt_psiI_of_lt _ (not_le.1 hnm)
  | inaccW, _, _, h => by simp [cmp] at h
  | add c d, hx, sx, h => by
    rw [cmp_add_left c d rfl] at h
    split_ifs at h with hc
    exact val_lt_of_head_lt (exact_all _) (Nat.le_succ _) hx sx
      (InaccSeq.SC_psi (InaccSeq.InR_I n) _).isPrincipal (lt_psiI_of_cmp ha sa hx.1 sx.1 hc)
  | phi c d, hx, sx, h => by
    rcases hcm : cmp c (psiI n a) with _ | _ | _
    · rw [cmp_phi_left_lt rfl hcm] at h
      exact (InaccSeq.SC_psi (InaccSeq.InR_I n) _).2 _ (lt_psiI_of_cmp ha sa hx.1 sx.1 hcm) _
        (lt_psiI_of_cmp ha sa hx.2.1 sx.2 h)
    · rw [cmp_phi_left_eq rfl hcm] at h
      exact absurd h (cmp_zero_right_ne_lt d)
    · rw [cmp_phi_left_gt rfl hcm] at h
      exact absurd h (by decide)
  | om c, hx, sx, h => by
    rw [cmp_om_F c rfl] at h
    have := Om_lt_Om.2 (lt_psiI_of_cmp ha sa hx.1 sx h)
    rwa [show Om (val S (psiI n a)) = val S (psiI n a) from InaccSeq.Om_psiI _ _] at this
  | psiS s c, hx, sx, h => by
    rw [cmp_psiS_K s c rfl] at h
    split_ifs at h with hc
    have hμ := InaccSeq.SC_psi (S := S) (InaccSeq.InR_I n) (val S a)
    have hs : val S s < val S (psiI n a) := by
      unfold cardT at hc
      split_ifs at hc with h0 hF
      · subst h0; exact hμ.1
      · exact lt_psiI_of_cmp ha sa hx.1 sx.1 hc
      · rw [cmp_om_F s rfl] at hc; exact lt_psiI_of_cmp ha sa hx.1 sx.1 hc
    have h1 : val S s + 1 < val S (psiI n a) := hμ.add_one_lt hs
    have h2 := Om_lt_Om.2 h1
    rw [show Om (val S (psiI n a)) = val S (psiI n a) from InaccSeq.Om_psiI _ _] at h2
    exact lt_trans (InaccSeq.psiS_bounds _ _).2 h2
  | psiI m c, hx, sx, h => by
    rw [cmp_psiI_psiI] at h
    split_ifs at h with hmn
    · subst hmn
      exact InaccSeq.psi_lt_psi (InaccSeq.InR_I m) (lt_of_cmp_lt hx.1 ha sx.1 sa h) sx.2
    · exact InaccSeq.psiI_lt_psiI _ _ (compare_lt_iff_lt.1 h)

/-- A cardinal term below `ψ^S_s(a)` in the sense of `cmp` is below it in value. -/
theorem lt_psiS_of_K {s a k : Term} (hs : NF s) (ss : Sem S s) (hk : NF k) (sk : Sem S k)
    (hK : k.isK = true) (h : cmp k (psiS s a) = .lt) : val S k < val S (psiS s a) := by
  rw [cmp_K_psiS s a hK] at h
  have e := ok_of_sem hk (NF_cardT hs) sk (Sem_cardT ss)
  have hle : val S k ≤ val S (cardT s) := by
    split_ifs at h with hc
    rw [e.1] at hc
    exact not_lt.1 fun h' => hc (compare_gt_iff_gt.2 h')
  rw [val_cardT] at hle
  exact lt_of_le_of_lt hle (InaccSeq.psiS_bounds _ _).1

/-- The comparisons with the bound `μ = ψ^S_s(a)` of the normal form of `ψ^S_s(a)` are
right in the direction `.lt`, without `Sem` for `ψ^S_s(a)` itself. -/
theorem lt_psiS_of_cmp {s a : Term} (hs : NF s) (ss : Sem S s) (ha : NF a) (sa : Sem S a) :
    ∀ {x : Term}, NF x → Sem S x → cmp x (psiS s a) = .lt → val S x < val S (psiS s a)
  | zero, _, _, _ => (InaccSeq.SC_psi (InaccSeq.InR_Om_succ _) _).1
  | inacc _, hx, sx, h => lt_psiS_of_K hs ss hx sx rfl h
  | inaccW, hx, sx, h => lt_psiS_of_K hs ss hx sx rfl h
  | om _, hx, sx, h => lt_psiS_of_K hs ss hx sx rfl h
  | psiI _ _, hx, sx, h => lt_psiS_of_K hs ss hx sx rfl h
  | add c d, hx, sx, h => by
    rw [cmp_add_left c d rfl] at h
    split_ifs at h with hc
    exact val_lt_of_head_lt (exact_all _) (Nat.le_succ _) hx sx
      (InaccSeq.SC_psi (InaccSeq.InR_Om_succ _) _).isPrincipal
      (lt_psiS_of_cmp hs ss ha sa hx.1 sx.1 hc)
  | phi c d, hx, sx, h => by
    rcases hcm : cmp c (psiS s a) with _ | _ | _
    · rw [cmp_phi_left_lt rfl hcm] at h
      exact (InaccSeq.SC_psi (InaccSeq.InR_Om_succ _) _).2 _
        (lt_psiS_of_cmp hs ss ha sa hx.1 sx.1 hcm) _ (lt_psiS_of_cmp hs ss ha sa hx.2.1 sx.2 h)
    · rw [cmp_phi_left_eq rfl hcm] at h
      exact absurd h (cmp_zero_right_ne_lt d)
    · rw [cmp_phi_left_gt rfl hcm] at h
      exact absurd h (by decide)
  | psiS t b, hx, sx, h => by
    rw [cmp_psiS_psiS] at h
    have est := ok_of_sem hx.1 hs sx.1 ss
    split_ifs at h with hts
    · rw [est.1] at hts
      obtain rfl := est.2 (compare_eq_iff_eq.1 hts)
      exact InaccSeq.psi_lt_psi (InaccSeq.InR_Om_succ _) (lt_of_cmp_lt hx.2.1 ha sx.2.1 sa h)
        sx.2.2
    · rw [est.1] at h
      exact lt_trans ((InaccSeq.Om_psiS_lt_Om _ _).2 (compare_lt_iff_lt.1 h))
        (InaccSeq.psiS_bounds _ _).1

/-- **Every normal form satisfies `Sem`.** -/
theorem sem_of_NF : ∀ {t : Term}, NF t → Sem S t
  | zero, _ => trivial
  | inacc _, _ => trivial
  | inaccW, _ => trivial
  | add _ _, h => ⟨sem_of_NF h.1, sem_of_NF h.2.1⟩
  | phi _ _, h => ⟨sem_of_NF h.1, sem_of_NF h.2.1⟩
  | om a, h => by show Sem S a; exact sem_of_NF h.1
  | psiS s a, h => by
    have ss : Sem S s := sem_of_NF h.1
    have sa : Sem S a := sem_of_NF h.2.1
    exact ⟨ss, sa, KLt_sound (S := S) (μ := psiS s a) (α := a)
      (fun x hx sx hc => lt_psiS_of_cmp h.1 ss h.2.1 sa hx sx hc)
      (fun y hy sy hc => lt_of_cmp_lt hy h.2.1 sy sa hc) h.2.1 sa h.2.2⟩
  | psiI n a, h => by
    have sa : Sem S a := sem_of_NF h.1
    exact ⟨sa, KLt_sound (S := S) (μ := psiI n a) (α := a)
      (fun x hx sx hc => lt_psiI_of_cmp h.1 sa hx sx hc)
      (fun y hy sy hc => lt_of_cmp_lt hy h.1 sy sa hc) h.1 sa h.2⟩

/-! ## The main theorem -/

variable (S)

/-- **Main theorem.** On normal forms, `cmp` is the comparison of the values. -/
theorem cmp_eq_compare {a b : Term} (ha : NF a) (hb : NF b) :
    cmp a b = compare (val S a) (val S b) :=
  (ok_of_sem ha hb (sem_of_NF ha) (sem_of_NF hb)).1

/-- **Main theorem.** On normal forms, the value determines the term. -/
theorem eq_of_val_eq {a b : Term} (ha : NF a) (hb : NF b) (h : val S a = val S b) : a = b :=
  (ok_of_sem ha hb (sem_of_NF ha) (sem_of_NF hb)).2 h

theorem cmp_lt_iff {a b : Term} (ha : NF a) (hb : NF b) :
    cmp a b = .lt ↔ val S a < val S b := by
  rw [cmp_eq_compare S ha hb]; exact compare_lt_iff_lt

/-- **Soundness of `K`** for normal forms: `K_μ(t) < α` gives `|t| ∈ Cl(|α|, |μ|)`. -/
theorem KLt_sound_NF {μ α t : Term} (hμ : NF μ) (hα : NF α) (ht : NF t) (h : KLt μ t α) :
    val S t ∈ S.CSet (val S α) (val S μ) :=
  KLt_sound (fun _ hx _ hc => (cmp_lt_iff S hx hμ).1 hc)
    (fun _ hy _ hc => (cmp_lt_iff S hy hα).1 hc) ht (sem_of_NF ht) h

/-- A normal form with a strongly critical value is a strongly critical term. -/
theorem isSC_of_SC : ∀ {t : Term}, NF t → SC (val S t) → t.isSC = true
  | zero, _, h => absurd h.1 (lt_irrefl _)
  | inacc _, _, _ => rfl
  | inaccW, _, _ => rfl
  | add a b, h, hγ => by
    exfalso
    have hP := hγ.isPrincipal
    have hab : val S a < val S (add a b) :=
      lt_add_of_pos_right _ (pos_iff_ne_zero.2 (val_ne_zero S h.2.1 h.2.2.2.1))
    have hle : val S (head b) ≤ val S a := by
      have hh := h.2.2.2.2
      rw [cmp_eq_compare S h.2.1.head h.1] at hh
      exact not_lt.1 fun h' => hh (compare_gt_iff_gt.2 h')
    have hb : val S b < val S (add a b) :=
      val_lt_of_head_lt (exact_all _) (Nat.le_succ _) h.2.1 (sem_of_NF h.2.1) hP
        (lt_of_le_of_lt hle hab)
    exact lt_irrefl _ (hP hab hb)
  | phi a b, h, hγ => by
    exfalso
    have hv : val S (phi a b) = veblen (val S a) (val S b) := rfl
    by_cases hva : val S a = val S (phi a b)
    · have ha := isSC_of_SC h.1 (hva ▸ hγ)
      have hc := hγ.compare_veblen_self (y := val S b)
      rw [← hva, ← hv, hva, compare_eq_iff_eq.2 rfl] at hc
      have hb : b = zero := by
        by_contra hb0; exact val_ne_zero S h.2.1 hb0 (compare_eq_iff_eq.1 hc.symm)
      have h2 := h.2.2.1
      rw [hb, cmp_phi_zero ha] at h2
      exact absurd h2 (by decide)
    · have hlt : val S a < val S (phi a b) := lt_of_le_of_ne (left_le_veblen _ _) hva
      rcases hγ.eq_of_veblen_eq hv.symm with e | e
      · exact hva e
      · have hb := isSC_of_SC h.2.1 (e ▸ hγ)
        have h2 := h.2.2.2
        rw [cmp_phi_fix hb (by rw [cmp_eq_compare S h.2.1 h.1, e]; exact compare_gt_iff_gt.2 hlt)]
          at h2
        exact absurd h2 (by decide)
  | om _, _, _ => rfl
  | psiS _ _, _, _ => rfl
  | psiI _ _, _, _ => rfl

/-- A normal `φ(a, b)` does not have a strongly critical value. -/
theorem not_SC_phi {a b : Term} (h : NF (phi a b)) : ¬ SC (val S (phi a b)) := fun h' => by
  have := isSC_of_SC S h h'; simp [isSC] at this

/-! ## The well-order -/

include S in
/-- The comparison `cmp · · = .lt` on normal forms is a well-order: `val S` embeds it into
the ordinals. -/
theorem isWellOrder_cmp : IsWellOrder {t : Term // NF t} (fun a b => cmp a.1 b.1 = .lt) :=
  (⟨⟨fun a => val S a.1, fun a b h => Subtype.ext (eq_of_val_eq S a.2 b.2 h)⟩,
    fun {a b} => (cmp_lt_iff S a.2 b.2).symm⟩ :
      (fun a b : {t : Term // NF t} => cmp a.1 b.1 = .lt) ↪r
        ((· < ·) : Ordinal.{u} → Ordinal.{u} → Prop)).isWellOrder

include S in
theorem wellFounded_cmp : WellFounded (fun a b : {t : Term // NF t} => cmp a.1 b.1 = .lt) :=
  haveI := isWellOrder_cmp S
  IsWellFounded.wf

end Term

end Googology.Notation.InaccPsi

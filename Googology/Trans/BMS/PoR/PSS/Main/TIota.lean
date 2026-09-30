import Googology.Trans.BMS.PoR.PSS.Main.Cited2
import Googology.Trans.BMS.PoR.PSS.Main.EpsRoots

/-!
# `t^α_τ ∘ ι_{τ,α}` on `T¹`, and `λ_α` as a sum in `T¹`

For `α = ϑ_0(Δ + η)` of `T¹` with `Δ > 0` (given by its term `a`), `jP a` is
`t^α_τ ∘ ι_{τ,α}` ([W07a] Def 7.1, Def 6.2) on the terms of `T^τ_α` that `ι` sends below
`ϑ^α(Δ) = α^+`, written as a map from `T¹` to `T¹`:

* `ϑ_0(b) ↦ ϑ_0(b)` (a parameter `< α`);
* `ϑ_{k+2}(b) ↦ ϑ_{k+1}(b^J)`;
* `ϑ_1(b) ↦ t^α_τ(ϑ^α(ι b))`, the case `(α, ϑ^α(Δ))` of Def 6.2: `α` if `b = 0`; otherwise,
  with `Γ` the summands of `b` of level `≥ 2` and `ρ` the rest,
  `ϑ_0(α + (−1 + ρ)^J)` if `Γ = 0`, `ϑ_0(Γ^J + α + ρ^J)` if `Γ` has no `ϑ_1`-subterm (outside
  `ϑ_0`), and `ϑ_0(Γ^J + ρ^J)` otherwise.

`tL_iotaS`: on a sum `x` of `T^τ_α` whose visible `ϑ_1`-subterms are at most `Δ`,
`t^α_τ(ι(x)) = x^J` (by [W07a] Cor 7.3 and Lemma 6.3, the case `(α, ϑ^α(Δ))` is the one
taken).  With [W07b] Theorem 5.3 and the remark after [W07a] Def 7.5 this gives
(`lam_eq_jS`)

```
λ_α = Δ^J + ζ_α.
```
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal

/-! ## The map `J = t^α_τ ∘ ι_{τ,α}` -/

/-- The case `ϑ_1(b)` of `J`, from `b` and the images `ys` of the summands of `b`. -/
def jTop (a : WP) (b : List WP) (ys : List (List WP)) : List WP :=
  if b.isEmpty then [a]
  else if (b.takeWhile (fun q => decide (2 ≤ q.lvl))).isEmpty then
    [.th 0 (a :: (if b.head? = some TR.one then (ys.drop 1).flatten else ys.flatten))]
  else
    let n := (b.takeWhile (fun q => decide (2 ≤ q.lvl))).length
    if (starS 1 (b.take n)).isEmpty then [.th 0 ((ys.take n).flatten ++ a :: (ys.drop n).flatten)]
    else [.th 0 ((ys.take n).flatten ++ (ys.drop n).flatten)]

mutual
/-- **`J = t^α_τ ∘ ι_{τ,α}`** on a principal term of `T¹`. -/
def jP (a : WP) : WP → List WP
  | .th 0 b => [.th 0 b]
  | .th 1 b => jTop a b (jL a b)
  | .th (k + 2) b => [.th (k + 1) (jL a b).flatten]

/-- The images of the summands of a sum. -/
def jL (a : WP) : List WP → List (List WP)
  | [] => []
  | q :: l => jP a q :: jL a l
end

/-- **`J`** on a sum. -/
def jS (a : WP) (x : List WP) : List WP := (jL a x).flatten

theorem jP_zero (a : WP) (b : List WP) : jP a (.th 0 b) = [.th 0 b] := by rw [jP]
theorem jP_one (a : WP) (b : List WP) : jP a (.th 1 b) = jTop a b (jL a b) := by rw [jP]
theorem jP_add_two (a : WP) (k : ℕ) (b : List WP) :
    jP a (.th (k + 2) b) = [.th (k + 1) (jL a b).flatten] := by rw [jP]
@[simp] theorem jL_nil (a : WP) : jL a [] = [] := by rw [jL]
@[simp] theorem jL_cons (a q : WP) (l : List WP) : jL a (q :: l) = jP a q :: jL a l := by
  rw [jL]

theorem jL_eq_map (a : WP) : ∀ x : List WP, jL a x = x.map (jP a)
  | [] => by simp
  | q :: l => by simp [jL_eq_map a l]

/-! ## Equations of `ι`, `t` -/

@[simp] theorem iotaS_nil : iotaS [] = [] := by rw [iotaS]
@[simp] theorem iotaS_cons (p : WP) (l : List WP) : iotaS (p :: l) = iotaP p :: iotaS l := by
  rw [iotaS]
theorem iotaP_zero (b : List WP) : iotaP (.th 0 b) = .prm (.th 0 b) := by rw [iotaP]
theorem iotaP_succ (k : ℕ) (b : List WP) : iotaP (.th (k + 1) b) = .th k (iotaS b) := by
  rw [iotaP]

theorem iotaS_eq_map : ∀ x : List WP, iotaS x = x.map iotaP
  | [] => by simp
  | q :: l => by simp [iotaS_eq_map l]

@[simp] theorem tL_nil (a : WP) : tL a [] = [] := by rw [tL]
@[simp] theorem tL_cons (a : WP) (q : AT) (l : List AT) : tL a (q :: l) = tP a q :: tL a l := by
  rw [tL]
theorem tP_prm (a p : WP) : tP a (.prm p) = [p] := by rw [tP]
theorem tP_succ (a : WP) (k : ℕ) (x : List AT) :
    tP a (.th (k + 1) x) = [.th (k + 1) (tL a x).flatten] := by rw [tP]
theorem tP_zero (a : WP) (x : List AT) : tP a (.th 0 x) = tTop a x (tL a x) := by rw [tP]

@[simp] theorem valRS_nil (τ : Ordinal.{0}) : AT.valRS τ [] = 0 := by rw [AT.valRS]
@[simp] theorem valRS_cons (τ : Ordinal.{0}) (p : AT) (l : List AT) :
    AT.valRS τ (p :: l) = AT.valR τ p + AT.valRS τ l := by rw [AT.valRS]

theorem iotaP_lvl (q : WP) : (iotaP q).lvl = q.lvl - 1 := by
  obtain ⟨m, b⟩ := q
  rcases m with _ | m
  · rw [iotaP_zero]; rfl
  · rw [iotaP_succ]; simp [AT.lvl]

theorem takeWhile_iotaS : ∀ x : List WP,
    (iotaS x).takeWhile (fun q => decide (1 ≤ q.lvl)) =
      iotaS (x.takeWhile (fun q => decide (2 ≤ q.lvl)))
  | [] => by simp
  | q :: l => by
    rw [iotaS_cons, List.takeWhile_cons, List.takeWhile_cons, iotaP_lvl]
    by_cases h : 2 ≤ q.lvl
    · have h' : 1 ≤ q.lvl - 1 := by omega
      simp [h, h', takeWhile_iotaS l]
    · have h' : ¬ 1 ≤ q.lvl - 1 := by omega
      simp [h, h']

theorem length_iotaS (x : List WP) : (iotaS x).length = x.length := by
  rw [iotaS_eq_map, List.length_map]

theorem iotaS_take (x : List WP) (n : ℕ) : iotaS (x.take n) = (iotaS x).take n := by
  rw [iotaS_eq_map, iotaS_eq_map, List.map_take]

mutual
theorem hasTh0_iotaP : ∀ p : WP, AT.hasTh0 (iotaP p) = !(starP 1 p).isEmpty
  | .th 0 b => by rw [iotaP_zero, AT.hasTh0, starP_th]; simp
  | .th 1 b => by rw [iotaP_succ, AT.hasTh0, starP_th]; simp
  | .th (k + 2) b => by
    rw [iotaP_succ, AT.hasTh0, starP_th, hasTh0_iotaS b]
    simp

theorem hasTh0_iotaS : ∀ x : List WP, AT.hasTh0S (iotaS x) = !(starS 1 x).isEmpty
  | [] => by rw [iotaS_nil, AT.hasTh0S]; simp
  | p :: l => by
    rw [iotaS_cons, AT.hasTh0S, hasTh0_iotaP p, hasTh0_iotaS l, starS_cons]
    cases (starP 1 p) <;> cases (starS 1 l) <;> simp
end

theorem head_isOne_iotaS (x : List WP) :
    ((iotaS x).head?.map AT.isOne = some true) ↔ x.head? = some TR.one := by
  cases x with
  | nil => simp
  | cons q l =>
    rw [iotaS_cons]
    simp only [List.head?_cons, Option.map_some, Option.some.injEq]
    obtain ⟨m, b⟩ := q
    rcases m with _ | m
    · rw [iotaP_zero]; simp [AT.isOne]
    · rw [iotaP_succ]; simp [AT.isOne, TR.one]

/-! ## `t^α_τ ∘ ι_{τ,α} = J` below `α^+` -/

/-- The visible `ϑ_1`-subterms of a principal term of `T¹` are at most the term. -/
theorem val_le_of_mem_starP1 {p : WP} (hp : NFP p) {s : WP} (hs : s ∈ starP 1 p) :
    s.val ≤ p.val := by
  obtain ⟨k, b⟩ := p
  have hs1 := (starP_spec 1 _ hp s hs).2.1
  have hsn := (starP_spec 1 _ hp s hs).1
  rw [starP_th] at hs
  rcases Nat.lt_or_ge k 1 with hk | hk
  · rw [if_pos hk] at hs; simp at hs
  · rw [if_neg (by omega)] at hs
    rcases Nat.eq_or_lt_of_le hk with rfl | hk2
    · rw [if_pos rfl] at hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact le_rfl
      · exact (star_lt_val hp s hs).le
    · have hlt : s.val < Om 2 := val_lt_Om_of_lvl_lt hsn (by omega)
      exact le_trans hlt.le (Om_le_val_of_le_lvl hp (by simp; omega))

theorem val_le_of_mem_starS1 {x : List WP} (hx : NFS x) {s : WP} (hs : s ∈ starS 1 x) :
    s.val ≤ WP.valS x := by
  induction x with
  | nil => simp at hs
  | cons p l ih =>
    rw [starS_cons, List.mem_append] at hs
    rcases hs with hs | hs
    · exact le_trans (val_le_of_mem_starP1 (hx.1 p (by simp)) hs)
        (val_le_valS_of_mem (by simp))
    · rw [WP.valS_cons]
      exact le_trans (ih (NFS.of_cons hx) hs) le_add_self

theorem mem_starS0_of_mem_starP {m : ℕ} {b : List WP} {s : WP} (hs : s ∈ starS 0 b) :
    s ∈ starP 0 (.th m b) := by
  rw [starP_th]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [hs]
  · rw [if_neg (by omega), if_neg (by omega)]; exact hs

theorem mem_starS1_of_mem_starP {m : ℕ} (hm : 1 ≤ m) {b : List WP} {s : WP}
    (hs : s ∈ starS 1 b) : s ∈ starP 1 (.th m b) := by
  rw [starP_th, if_neg (by omega)]
  rcases Nat.eq_or_lt_of_le hm with rfl | hm
  · simp [hs]
  · rw [if_neg (by omega)]; exact hs

section TIota

variable {a : WP} (ha : NFP a) (h0 : a.lvl = 0) (hΔ : argD a.arg ≠ [])
include ha h0 hΔ

theorem nfs_argD : NFS (argD a.arg) := by
  obtain ⟨m, b⟩ := a
  exact (NFP.nfs ha).takeWhile _

theorem starS0_argD_lt : ∀ s ∈ starS 0 (argD a.arg), s.val < a.val := by
  obtain ⟨m, b⟩ := a
  simp only [WP.lvl_th] at h0; subst h0
  intro s hs
  have : s ∈ starS 0 b := by
    have e : b = argD b ++ argE b := (List.takeWhile_append_dropWhile).symm
    rw [e, starS_append]; exact List.mem_append_left _ hs
  exact star_lt_val ha s this

/-- The branch `(α, ϑ^α(Δ))` of Def 6.2: `ϑ^α(ι(b)) < ϑ^α(Δ)` for `ϑ_1(b) ≤ Δ` in `T^τ_α`. -/
theorem valR_iota_lt {b : List WP} (hp : NFP (.th 1 b))
    (hp0 : ∀ s ∈ starP 0 (.th 1 b), s.val < a.val)
    (hpΔ : (WP.th 1 b).val ≤ WP.valS (argD a.arg)) :
    (AT.th 0 (iotaS b)).valR a.val < (AT.th 0 (embS (argD a.arg))).valR a.val := by
  have hx : NFS [WP.th 1 b] := NFS.single hp
  have hx0 : ∀ s ∈ starS 0 [WP.th 1 b], s.val < a.val := by
    intro s hs; rw [starS_cons, starS_nil, List.append_nil] at hs; exact hp0 s hs
  have hle : AT.valRS a.val (iotaS [WP.th 1 b]) ≤ AT.valRS a.val (iotaS (argD a.arg)) := by
    by_contra hlt
    push Not at hlt
    have := (cor73_lt ha h0 hΔ (nfs_argD ha h0 hΔ) hx (starS0_argD_lt ha h0 hΔ) hx0).mpr hlt
    rw [valS_single] at this
    exact absurd hpΔ (not_le.mpr this)
  have h1 : AT.valRS a.val (iotaS [WP.th 1 b]) = (AT.th 0 (iotaS b)).valR a.val := by
    rw [iotaS_cons, iotaS_nil, iotaP_succ, valRS_cons, valRS_nil, add_zero]
  rw [← h1, ← lemma63_plus ha h0 hΔ]
  exact lt_of_le_of_lt hle (cor73_delta ha h0 hΔ)

/-- **`t^α_τ ∘ ι_{τ,α} = J`** on a principal term of `T^τ_α` whose visible `ϑ_1`-subterms
are at most `Δ`. -/
theorem tP_iotaP : ∀ p : WP, NFP p → (∀ s ∈ starP 0 p, s.val < a.val) →
    (∀ s ∈ starP 1 p, s.val ≤ WP.valS (argD a.arg)) → tP a (iotaP p) = jP a p := by
  intro p
  induction p using WP.ind with
  | h m b ih =>
    intro hp hp0 hp1
    rcases m with _ | k
    · rw [iotaP_zero, tP_prm, jP_zero]
    have hsub : ∀ q ∈ b, ∀ s, (s ∈ starP 0 q → s ∈ starP 0 (.th (k + 1) b)) ∧
        (s ∈ starP 1 q → s ∈ starP 1 (.th (k + 1) b)) := by
      intro q hq s
      obtain ⟨l₁, l₂, e⟩ := List.append_of_mem hq
      refine ⟨fun hs => mem_starS0_of_mem_starP ?_, fun hs => mem_starS1_of_mem_starP (by omega) ?_⟩
      · rw [e, starS_append, starS_cons]; simp [hs]
      · rw [e, starS_append, starS_cons]; simp [hs]
    have hL : tL a (iotaS b) = jL a b := by
      have key : ∀ l : List WP, (∀ q ∈ l, q ∈ b) → tL a (iotaS l) = jL a l := by
        intro l
        induction l with
        | nil => intro _; simp
        | cons q l ihl =>
          intro hl
          rw [iotaS_cons, tL_cons, jL_cons, ihl (fun r hr => hl r (by simp [hr]))]
          have hqb := hl q (by simp)
          rw [ih q hqb (hp.of_mem hqb) (fun s hs => hp0 s ((hsub q hqb s).1 hs))
            (fun s hs => hp1 s ((hsub q hqb s).2 hs))]
      exact key b (fun q hq => hq)
    rcases k with _ | k
    · -- `ϑ_1(b)`: the case `(α, ϑ^α(Δ))` of Def 6.2
      rw [iotaP_succ, tP_zero, jP_one, hL]
      unfold tTop jTop
      by_cases hb : b = []
      · subst hb; simp
      have hbi : ¬ (iotaS b).isEmpty = true := by
        rw [List.isEmpty_iff, ← List.length_eq_zero_iff, length_iotaS, List.length_eq_zero_iff]
        exact hb
      have hb' : ¬ b.isEmpty = true := by rw [List.isEmpty_iff]; exact hb
      have hlt := valR_iota_lt ha h0 hΔ hp hp0
        (hp1 _ (by rw [starP_th]; simp))
      rw [if_neg hbi, if_pos hlt, if_neg hb', takeWhile_iotaS]
      have hemp : (iotaS (b.takeWhile (fun q => decide (2 ≤ q.lvl)))).isEmpty =
          (b.takeWhile (fun q => decide (2 ≤ q.lvl))).isEmpty := by
        rw [iotaS_eq_map]; simp
      simp only [hemp, length_iotaS, ← iotaS_take, hasTh0_iotaS, head_isOne_iotaS]
      split_ifs <;> simp_all
    · rw [iotaP_succ, tP_succ, jP_add_two, hL]

/-- **`t^α_τ ∘ ι_{τ,α} = J`** on a sum of `T^τ_α` whose visible `ϑ_1`-subterms are at most
`Δ`. -/
theorem tL_iotaS : ∀ x : List WP, NFS x → (∀ s ∈ starS 0 x, s.val < a.val) →
    (∀ s ∈ starS 1 x, s.val ≤ WP.valS (argD a.arg)) → tL a (iotaS x) = jL a x
  | [], _, _, _ => by simp
  | p :: l, hx, hx0, hx1 => by
    rw [iotaS_cons, tL_cons, jL_cons]
    rw [tP_iotaP ha h0 hΔ p (hx.1 p (by simp)) (fun s hs => hx0 s (by rw [starS_cons]; simp [hs]))
      (fun s hs => hx1 s (by rw [starS_cons]; simp [hs])),
      tL_iotaS l (NFS.of_cons hx) (fun s hs => hx0 s (by rw [starS_cons]; simp [hs]))
      (fun s hs => hx1 s (by rw [starS_cons]; simp [hs]))]

/-- **`λ_α = Δ^J + ζ_α`** for an epsilon number `α = ϑ_0(Δ + η)` of `T¹` above `1`
([W07b] Theorem 5.3, the remark after [W07a] Def 7.5, and `tL_iotaS`). -/
theorem lam_eq_jS (h1 : 1 < a.val) (hE : InE a.val) :
    lam a.val = WP.valS (jS a (argD a.arg)) + zetaT a := by
  rw [thm53_lam ha h0 h1, lamT, if_pos hE, iota_delta_t ha h0 hΔ, tS, jS,
    tL_iotaS ha h0 hΔ _ (nfs_argD ha h0 hΔ) (starS0_argD_lt ha h0 hΔ)
      (fun s hs => val_le_of_mem_starS1 (nfs_argD ha h0 hΔ) hs)]

end TIota

end Googology.Trans.PSS.Main

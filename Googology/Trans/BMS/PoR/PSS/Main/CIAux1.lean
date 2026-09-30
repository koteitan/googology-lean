import Googology.Trans.BMS.PoR.PSS.Main.TIota

/-!
# CI, part 1: the normal-form version `jN` of `J = t^α_τ ∘ ι_{τ,α}`

`jN a` is `J` (`Main/TIota.lean`) with the sums written in normal form: a summand `α` that is
absorbed by the next summand is dropped.  On a principal term:

* `ϑ_0(b) ↦ ϑ_0(b)`;
* `ϑ_{k+2}(b) ↦ ϑ_{k+1}(b^J)`, where `b^J` is `b` with `jN` applied to each summand;
* `ϑ_1(0) ↦ α`, and for `b ≠ 0`, with `Γ` the summands of `b` of level `≥ 2` and `ρ` the rest:
  `ϑ_0(α ⊕ (−1 + ρ)^J)` if `Γ = 0`, `ϑ_0(Γ^J + (α ⊕ ρ^J))` if `Γ` has no visible
  `ϑ_1`-subterm, and `ϑ_0(Γ^J + ρ^J)` otherwise (`⊕` is `addS`).

`valS_jP`: when `jN a p` is a term of `T¹`, the value of `J(p)` is the value of `jN a p`.
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal

set_option linter.unusedSectionVars false

/-- The case `ϑ_1(b)` of `jN`, from `b` and the images `ys` of the summands of `b`. -/
def jNTop (a : WP) (b : List WP) (ys : List WP) : WP :=
  if b.isEmpty then a
  else if (b.takeWhile (fun q => decide (2 ≤ q.lvl))).isEmpty then
    .th 0 (addS [a] (if b.head? = some TR.one then ys.drop 1 else ys))
  else if (starS 1 (b.take (b.takeWhile (fun q => decide (2 ≤ q.lvl))).length)).isEmpty then
    .th 0 (ys.take (b.takeWhile (fun q => decide (2 ≤ q.lvl))).length ++
      addS [a] (ys.drop (b.takeWhile (fun q => decide (2 ≤ q.lvl))).length))
  else .th 0 ys

mutual
/-- **`J` in normal form** on a principal term of `T¹`. -/
def jN (a : WP) : WP → WP
  | .th 0 b => .th 0 b
  | .th 1 b => jNTop a b (jNL a b)
  | .th (k + 2) b => .th (k + 1) (jNL a b)

/-- `jN` on each summand of a sum. -/
def jNL (a : WP) : List WP → List WP
  | [] => []
  | q :: l => jN a q :: jNL a l
end

theorem jN_zero (a : WP) (b : List WP) : jN a (.th 0 b) = .th 0 b := by rw [jN]
theorem jN_one (a : WP) (b : List WP) : jN a (.th 1 b) = jNTop a b (jNL a b) := by rw [jN]
theorem jN_add_two (a : WP) (k : ℕ) (b : List WP) :
    jN a (.th (k + 2) b) = .th (k + 1) (jNL a b) := by rw [jN]

theorem jNL_eq_map (a : WP) : ∀ x : List WP, jNL a x = x.map (jN a)
  | [] => by rw [jNL]; rfl
  | q :: l => by rw [jNL, jNL_eq_map a l, List.map_cons]

theorem jN_one_eq (a : WP) : jN a TR.one = TR.one := by rw [TR.one, jN_zero]

/-- The level of `jN a p`: `lvl p - 1` (and `0` at level `0`), when `a` has level `0`. -/
theorem jN_lvl {a : WP} (h0 : a.lvl = 0) (p : WP) : (jN a p).lvl = p.lvl - 1 := by
  obtain ⟨k, b⟩ := p
  rcases k with _ | _ | k
  · rw [jN_zero]; rfl
  · rw [jN_one, jNTop]
    split_ifs <;> simp [h0]
  · rw [jN_add_two]; simp

/-! ## Values: `J` and `jN` -/

theorem valS_flatten_map (f : WP → List WP) :
    ∀ l : List WP, WP.valS (l.map f).flatten = (l.map (fun q => WP.valS (f q))).sum
  | [] => by simp
  | q :: l => by simp [valS_append, valS_flatten_map f l]

theorem valS_eq_sum_map_val : ∀ l : List WP, WP.valS l = (l.map WP.val).sum
  | [] => by simp
  | q :: l => by simp [valS_eq_sum_map_val l]

theorem valS_drop_one_flatten (f : WP → List WP) (l : List WP) :
    WP.valS ((l.map f).drop 1).flatten = ((l.drop 1).map (fun q => WP.valS (f q))).sum := by
  rw [← List.map_drop, valS_flatten_map]

theorem sublist_addS_right (x y : List WP) : y.Sublist (addS x y) := by
  cases y with
  | nil => exact List.nil_sublist _
  | cons y0 y' => rw [addS]; exact List.sublist_append_right _ _

theorem nfs_of_addS_right {x y : List WP} (h : NFS (addS x y)) : NFS y :=
  h.sublist (sublist_addS_right x y)

theorem valS_addS_single {a : WP} (ha : NFP a) {y : List WP} (hy : NFS y) :
    WP.valS (addS [a] y) = a.val + WP.valS y := by
  rw [(addS_spec (NFS.single ha) hy).2, valS_single]

/-- **`val J(p) = val jN(p)`** when `jN a p` is a term of `T¹`. -/
theorem valS_jP {a : WP} (ha : NFP a) :
    ∀ p : WP, NFP (jN a p) → WP.valS (jP a p) = (jN a p).val := by
  intro p
  induction p using WP.ind with
  | h m b ih =>
    intro hp
    -- the summands of `b` whose images are summands of the argument
    have key : ∀ l : List WP, (∀ q ∈ l, q ∈ b) → NFS (l.map (jN a)) →
        WP.valS (l.map (jP a)).flatten = WP.valS (l.map (jN a)) := by
      intro l hl hn
      rw [valS_flatten_map, valS_eq_sum_map_val, List.map_map]
      congr 1
      refine List.map_congr_left (fun q hq => ?_)
      exact ih q (hl q hq) (hn.1 _ (List.mem_map_of_mem hq))
    have hdrop : ∀ k, ∀ q ∈ b.drop k, q ∈ b := fun k q hq => List.mem_of_mem_drop hq
    have htake : ∀ k, ∀ q ∈ b.take k, q ∈ b := fun k q hq => List.mem_of_mem_take hq
    rcases m with _ | _ | k
    · rw [jP_zero, jN_zero, valS_single]
    · rw [jP_one, jN_one, jTop, jNTop, jL_eq_map, jNL_eq_map]
      rw [jN_one, jNTop, jNL_eq_map] at hp
      by_cases hb : b.isEmpty = true
      · rw [if_pos hb, if_pos hb, valS_single]
      rw [if_neg hb, if_neg hb] at *
      simp only [] at hp ⊢
      split_ifs at hp ⊢ with h1 h2 h3 <;> rw [valS_single, WP.val_th, WP.val_th] <;> congr 1
      · have hn := nfs_of_addS_right hp.nfs
        rw [valS_addS_single ha hn, WP.valS_cons, ← List.map_drop, ← List.map_drop]
        rw [← List.map_drop] at hn
        rw [key _ (hdrop 1) hn]
      · have hn := nfs_of_addS_right hp.nfs
        rw [valS_addS_single ha hn, WP.valS_cons, key b (fun q hq => hq) hn]
      · obtain ⟨hA, hB, -⟩ := NFS.append_iff.mp hp.nfs
        have hB' := nfs_of_addS_right hB
        rw [valS_append, valS_append, valS_addS_single ha hB', WP.valS_cons,
          ← List.map_drop, ← List.map_take, ← List.map_drop, ← List.map_take]
        rw [← List.map_drop] at hB'
        rw [← List.map_take] at hA
        rw [key _ (hdrop _) hB', key _ (htake _) hA]
      · rw [← List.flatten_append, ← List.map_take, ← List.map_drop, ← List.map_append,
          List.take_append_drop, key b (fun q hq => hq) hp.nfs]
    · rw [jP_add_two, jN_add_two, jNL_eq_map, valS_single, WP.val_th, WP.val_th]
      rw [jN_add_two, jNL_eq_map] at hp
      congr 1
      rw [jL_eq_map]
      exact key b (fun q hq => hq) hp.nfs

/-! ## Subterms -/

theorem eq_th_of_lvl {a : WP} (h0 : a.lvl = 0) : a = .th 0 a.arg := by
  obtain ⟨k, c⟩ := a; simp only [WP.lvl_th] at h0; subst h0; rfl

theorem starP_lvl_lt {m : ℕ} {p : WP} (h : p.lvl < m) : starP m p = [] := by
  obtain ⟨k, c⟩ := p; rw [starP_th, if_pos (by simpa using h)]

theorem mem_starS_of_mem {m : ℕ} {x : List WP} {q s : WP} (hq : q ∈ x) (hs : s ∈ starP m q) :
    s ∈ starS m x := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hq
  rw [starS_append, starS_cons]; simp [hs]

theorem exists_of_mem_starS {m : ℕ} {x : List WP} {s : WP} (hs : s ∈ starS m x) :
    ∃ q ∈ x, s ∈ starP m q := by
  induction x with
  | nil => simp at hs
  | cons q l ih =>
    rw [starS_cons, List.mem_append] at hs
    rcases hs with hs | hs
    · exact ⟨q, by simp, hs⟩
    · obtain ⟨q', hq', hs'⟩ := ih hs; exact ⟨q', by simp [hq'], hs'⟩

theorem starS_map_iff {m : ℕ} {x : List WP} {s : WP} :
    s ∈ starS m x ↔ ∃ q ∈ x, s ∈ starP m q :=
  ⟨exists_of_mem_starS, fun ⟨_, hq, hs⟩ => mem_starS_of_mem hq hs⟩

/-- A visible subterm of a visible subterm is a visible subterm (for `ϑ_0`-subterms). -/
theorem mem_starP0_trans : ∀ {m : ℕ} {p s z : WP}, s ∈ starP m p → z ∈ starP 0 s →
    z ∈ starP 0 p := by
  intro m p
  induction p using WP.ind with
  | h k c ih =>
    intro s z hs hz
    rw [starP_th] at hs
    split_ifs at hs with h1 h2
    · simp at hs
    · rcases List.mem_cons.mp hs with rfl | hs
      · exact hz
      · obtain ⟨q, hq, hs'⟩ := exists_of_mem_starS hs
        have := ih q hq hs' hz
        rw [starP_th]
        split_ifs <;> first | omega | simp [mem_starS_of_mem hq this]
    · obtain ⟨q, hq, hs'⟩ := exists_of_mem_starS hs
      have := ih q hq hs' hz
      rw [starP_th]
      split_ifs <;> first | omega | simp [mem_starS_of_mem hq this]

theorem mem_starP0_of_mem_arg {k : ℕ} {c : List WP} {q z : WP} (hq : q ∈ c)
    (hz : z ∈ starP 0 q) : z ∈ starP 0 (.th k c) := by
  rw [starP_th]
  split_ifs <;> first | omega | simp [mem_starS_of_mem hq hz]

theorem mem_starP_of_mem_arg {m k : ℕ} (hk : m < k) {c : List WP} {q z : WP} (hq : q ∈ c)
    (hz : z ∈ starP m q) : z ∈ starP m (.th k c) := by
  rw [starP_th, if_neg (by omega), if_neg (by omega)]
  exact mem_starS_of_mem hq hz

theorem val_le_of_mem_starP {m : ℕ} {p s : WP} (hp : NFP p) (hs : s ∈ starP m p) :
    s.val ≤ p.val := by
  obtain ⟨k, c⟩ := p
  have hsn := starP_spec m _ hp s hs
  rw [starP_th] at hs
  split_ifs at hs with h1 h2
  · simp at hs
  · subst h2
    rcases List.mem_cons.mp hs with rfl | hs
    · exact le_rfl
    · exact (star_lt_val hp s hs).le
  · exact (val_lt_of_lvl_lt hsn.1 hp (by rw [hsn.2.1]; simp; omega)).le

/-! ## `jN` and visible subterms -/

section Star

variable {a : WP} (h0 : a.lvl = 0)
include h0

/-- **Visible `ϑ_m`-subterms** (`m ≥ 1`, [W07a] Lemma 7.2 (a)):
`P_m(jN u) = jN[P_{m+1}(u)]`. -/
theorem starP_jN {m : ℕ} (hm : 1 ≤ m) : ∀ u : WP, starP m (jN a u) = (starP (m + 1) u).map (jN a) := by
  intro u
  induction u using WP.ind with
  | h k c ih =>
    have hL : starS m (c.map (jN a)) = (starS (m + 1) c).map (jN a) := by
      have : ∀ l : List WP, (∀ q ∈ l, q ∈ c) →
          starS m (l.map (jN a)) = (starS (m + 1) l).map (jN a) := by
        intro l hl
        induction l with
        | nil => simp
        | cons q l ihl =>
          rw [List.map_cons, starS_cons, starS_cons, ih q (hl q (by simp)),
            ihl (fun r hr => hl r (by simp [hr])), List.map_append]
      exact this c (fun q hq => hq)
    rcases k with _ | _ | k
    · rw [jN_zero, starP_lvl_lt (by simp only [WP.lvl_th]; omega),
        starP_lvl_lt (by simp only [WP.lvl_th]; omega)]; rfl
    · rw [starP_lvl_lt (p := .th 1 c) (by simp only [WP.lvl_th]; omega), List.map_nil]
      exact starP_lvl_lt (by rw [jN_lvl h0]; simp only [WP.lvl_th]; try omega)
    · rw [jN_add_two, jNL_eq_map, starP_th, starP_th]
      split_ifs <;> first | omega | rfl | exact hL |
        (rw [hL, List.map_cons, jN_add_two, jNL_eq_map])

theorem starS_jN {m : ℕ} (hm : 1 ≤ m) (x : List WP) :
    starS m (x.map (jN a)) = (starS (m + 1) x).map (jN a) := by
  induction x with
  | nil => simp
  | cons q l ih => rw [List.map_cons, starS_cons, starS_cons, starP_jN h0 hm, ih, List.map_append]

theorem jN_one_th (c : List WP) : ∃ c', jN a (.th 1 c) = .th 0 c' := by
  have hl : (jN a (.th 1 c)).lvl = 0 := by rw [jN_lvl h0]; rfl
  exact ⟨_, (eq_th_of_lvl hl)⟩

/-- The summands of the argument of `jN(ϑ_1(b))`: `α` and the images of the summands of `b`,
except a first summand `1` of `b` when `Γ = 0`. -/
theorem mem_arg_jN_one {b : List WP} (hb : b ≠ []) {z : WP} (hz : z ∈ (jN a (.th 1 b)).arg) :
    z = a ∨ ∃ v ∈ b, z = jN a v := by
  have hb' : ¬ b.isEmpty = true := by simpa using hb
  rw [jN_one, jNTop, if_neg hb', jNL_eq_map] at hz
  have hmap : ∀ {l : List WP}, z ∈ l.map (jN a) → (∀ v ∈ l, v ∈ b) → ∃ v ∈ b, z = jN a v :=
    fun {l} h hl => by obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h; exact ⟨v, hl v hv, rfl⟩
  split_ifs at hz with h1 h2 h3
  · rcases mem_addS hz with h | h
    · exact Or.inl (List.mem_singleton.mp h)
    · rw [← List.map_drop] at h; exact Or.inr (hmap h (fun v hv => List.mem_of_mem_drop hv))
  · rcases mem_addS hz with h | h
    · exact Or.inl (List.mem_singleton.mp h)
    · exact Or.inr (hmap h (fun v hv => hv))
  · rcases List.mem_append.mp hz with h | h
    · rw [← List.map_take] at h; exact Or.inr (hmap h (fun v hv => List.mem_of_mem_take hv))
    · rcases mem_addS h with h | h
      · exact Or.inl (List.mem_singleton.mp h)
      · rw [← List.map_drop] at h; exact Or.inr (hmap h (fun v hv => List.mem_of_mem_drop hv))
  · exact Or.inr (hmap hz (fun v hv => hv))

/-- Every summand of `b` other than a first `1` has its image in the argument of `jN(ϑ_1(b))`. -/
theorem jN_mem_arg_one {b : List WP} (hb : b ≠ []) {v : WP} (hv : v ∈ b) (hv1 : v ≠ TR.one ∨
    b.head? ≠ some TR.one) : jN a v ∈ (jN a (.th 1 b)).arg := by
  have hb' : ¬ b.isEmpty = true := by simpa using hb
  rw [jN_one, jNTop, if_neg hb', jNL_eq_map]
  have hvm : jN a v ∈ b.map (jN a) := List.mem_map_of_mem hv
  split_ifs with h1 h2 h3
  · -- `b = 1 :: b'`
    obtain ⟨q, b', rfl⟩ := List.exists_cons_of_ne_nil hb
    simp only [List.head?_cons, Option.some.injEq] at h2
    subst h2
    rcases List.mem_cons.mp hv with rfl | hv'
    · simp at hv1
    · apply (sublist_addS_right _ _).subset
      simp [List.mem_map_of_mem hv']
  · exact (sublist_addS_right _ _).subset hvm
  · rw [← List.take_append_drop (b.takeWhile (fun q => decide (2 ≤ q.lvl))).length (b.map (jN a))]
      at hvm
    rcases List.mem_append.mp hvm with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ ((sublist_addS_right _ _).subset h)
  · exact hvm

/-- **`jN` sends a visible `ϑ_1`-subterm to a `ϑ_0`-subterm.** -/
theorem jN_mem_starP0 : ∀ u : WP, ∀ s ∈ starP 1 u, jN a s ∈ starP 0 (jN a u) := by
  intro u
  induction u using WP.ind with
  | h k c ih =>
    intro s hs
    rcases k with _ | _ | k
    · rw [starP_lvl_lt (by simp)] at hs; simp at hs
    · rw [starP_th, if_neg (by omega), if_pos rfl] at hs
      rcases List.mem_cons.mp hs with rfl | hs
      · -- `s = u`
        by_cases hc : c = []
        · subst hc
          have : jN a (.th 1 []) = a := by rw [jN_one, jNTop]; simp
          rw [this, eq_th_of_lvl h0, starP_th]; simp
        · obtain ⟨c', hc'⟩ := jN_one_th h0 c
          rw [hc', starP_th]; simp
      · obtain ⟨v, hv, hs'⟩ := exists_of_mem_starS hs
        have h1 := ih v hv s hs'
        have hc : c ≠ [] := List.ne_nil_of_mem hv
        have hmem := jN_mem_arg_one h0 hc hv (Or.inl (by
          rintro rfl; rw [TR.one, starP_lvl_lt (by simp)] at hs'; simp at hs'))
        obtain ⟨c', hc'⟩ := jN_one_th h0 c
        rw [hc'] at hmem ⊢
        exact mem_starP0_of_mem_arg hmem h1
    · rw [starP_th, if_neg (by omega), if_neg (by omega)] at hs
      obtain ⟨v, hv, hs'⟩ := exists_of_mem_starS hs
      rw [jN_add_two, jNL_eq_map]
      exact mem_starP0_of_mem_arg (List.mem_map_of_mem hv) (ih v hv s hs')

/-- **The `ϑ_0`-subterms of `jN u`** are below `w` when the constants of `u` are below
`α < w` and the images of the visible `ϑ_1`-subterms of `u` are below `w`. -/
theorem starP0_jN_lt (ha : NFP a) {w : Ordinal.{0}} (haw : a.val < w) :
    ∀ u : WP, (∀ z ∈ starP 0 u, z.val < a.val) → (∀ y ∈ starP 1 u, (jN a y).val < w) →
      ∀ z ∈ starP 0 (jN a u), z.val < w := by
  intro u
  induction u using WP.ind with
  | h k c ih =>
    intro hc0 hc1 z hz
    have hsub : ∀ v ∈ c, (∀ z ∈ starP 0 v, z.val < a.val) := fun v hv z hz =>
      hc0 z (mem_starP0_of_mem_arg hv hz)
    rcases k with _ | _ | k
    · rw [jN_zero] at hz; exact lt_trans (hc0 z hz) haw
    · have hself : WP.th 1 c ∈ starP 1 (.th 1 c) := by rw [starP_th]; simp
      by_cases hcn : c = []
      · subst hcn
        have : jN a (.th 1 []) = a := by rw [jN_one, jNTop]; simp
        rw [this] at hz
        rw [eq_th_of_lvl h0] at hz ha
        exact lt_of_le_of_lt (val_le_of_mem_sub0 ha hz) (by rw [← eq_th_of_lvl h0]; exact haw)
      have hmem : ∀ z' ∈ (jN a (.th 1 c)).arg, z' = a ∨ ∃ v ∈ c, z' = jN a v :=
        fun z' hz' => mem_arg_jN_one h0 hcn hz'
      have htop := hc1 _ hself
      obtain ⟨c', hc'⟩ := jN_one_th h0 c
      rw [hc'] at hz hmem htop
      rw [starP_th] at hz
      simp only [lt_irrefl, if_false, if_true] at hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact htop
      obtain ⟨q, hq, hzq⟩ := exists_of_mem_starS hz
      rcases hmem q hq with rfl | ⟨v, hv, rfl⟩
      · rw [eq_th_of_lvl h0] at hzq ha
        exact lt_of_le_of_lt (val_le_of_mem_sub0 ha hzq) (by rw [← eq_th_of_lvl h0]; exact haw)
      · refine ih v hv (hsub v hv) (fun y hy => hc1 y ?_) z hzq
        rw [starP_th, if_neg (by omega), if_pos rfl]
        exact List.mem_cons_of_mem _ (mem_starS_of_mem hv hy)
    · rw [jN_add_two, jNL_eq_map, starP_th, if_neg (by omega), if_neg (by omega)] at hz
      obtain ⟨q, hq, hzq⟩ := exists_of_mem_starS hz
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hq
      exact ih v hv (hsub v hv) (fun y hy => hc1 y (mem_starP_of_mem_arg (by omega) hv hy)) z hzq

end Star

end Googology.Trans.PSS.Main

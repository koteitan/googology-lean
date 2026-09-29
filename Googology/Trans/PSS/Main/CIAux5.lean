import Googology.Trans.PSS.Main.CIAux4

/-!
# CI, part 5: region terms

For a standard epsilon root `N = (0, H)` with last child `W`:

* `RegD H W ctx u`: `u` is a node below `W` reached through nodes with `y ≥ 1`, with the context
  `ctx` of its ancestors (`proof/PROOF-3.md` §14: the region).
* `IsRegT H hne s`: `s` is a truncation `(y(u), first i children of u)` of `W` or of such a
  node `u`.  `InReg W s` gives `IsRegT` (`isRegT_of_inReg`).
* Facts: valid, region terms of `proof/COMB.md` (`RG`), constants below `N`, `u ≤ W` for
  `y(u) = 1` (the `G*` chain, Claim Q), **P′** (`coll_lt_single`), **ND** (`addT_noDrop`),
  and **B3** (`b3`): the `ϑ_0`-subterms of `𝒯(s)` are below `α = 𝒯(N)`.
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Phi Forest
open Bijectivity (ltPS lePS)

set_option linter.unusedSectionVars false

/-- Nodes below `W` reached through nodes with `y ≥ 1`, with their ancestor contexts. -/
inductive RegD (H : List Tm) (W : Tm) : List (ℕ × PS) → Tm → Prop
  | top {c : Tm} : c ∈ W.cs → 1 ≤ c.y → RegD H W [(1, W.cols), (0, (Tm.node 0 H).cols)] c
  | child {ctx : List (ℕ × PS)} {s c : Tm} : RegD H W ctx s → c ∈ s.cs → 1 ≤ c.y →
      RegD H W ((s.y, s.cols) :: ctx) c

/-- The constants of a term: the `y = 0` nodes reached through nodes with `y ≥ 1`. -/
inductive Cst : Tm → Tm → Prop
  | here {s c : Tm} : c ∈ s.cs → c.y = 0 → Cst s c
  | deep {s c d : Tm} : c ∈ s.cs → 1 ≤ c.y → Cst c d → Cst s d

theorem Cst.mono {s s' d : Tm} (h : Cst s d) (hsub : ∀ c ∈ s.cs, c ∈ s'.cs) : Cst s' d := by
  cases h with
  | here hc h0 => exact .here (hsub _ hc) h0
  | deep hc h1 hd => exact .deep (hsub _ hc) h1 hd

theorem lt_append_cons : ∀ (l : List Tm) (d : Tm) (ds : List Tm), l < l ++ d :: ds
  | [], d, ds => List.nil_lt_cons _ _
  | x :: l, d, ds => by
    rw [List.cons_append, List.cons_lt_cons_iff]
    exact Or.inr ⟨rfl, lt_append_cons l d ds⟩

theorem node_take_le (y : ℕ) (cs : List Tm) (i : ℕ) : Tm.node y (cs.take i) ≤ .node y cs := by
  apply node_le_node_of
  by_cases h : i < cs.length
  · right
    have := List.take_append_drop i cs
    conv_rhs => rw [← this]
    obtain ⟨d, ds, hd⟩ := List.exists_cons_of_ne_nil (show cs.drop i ≠ [] by simp; omega)
    rw [hd]
    exact lt_append_cons _ d ds
  · left; exact List.take_of_length_le (by omega)

section Region

variable {H : List Tm} (hN : Std (.node 0 H)) (he : isEps (.node 0 H) = true) (hne : H ≠ [])
include hN he hne

theorem W_y : (H.getLast hne).y = 1 := by
  have := y_of_eps_child hN he (c := H.getLast hne) (by simpa using List.getLast_mem hne)
  exact this

theorem W_eq : H.getLast hne = .node 1 (H.getLast hne).cs := by
  conv_lhs => rw [← Tm.eta (H.getLast hne)]
  rw [W_y hN he hne]

theorem tgood_W : TGood [(0, (Tm.node 0 H).cols)] (H.getLast hne) :=
  tgood_child hN (by simpa using List.getLast_mem hne)

/-- The invariant of the contexts: the first ancestor with `y ≤ 1` is a node `≤ W`. -/
def CtxW (H : List Tm) (hne : H ≠ []) (ctx : List (ℕ × PS)) : Prop :=
  ∃ v, ctx.find? (fun e => decide (e.1 ≤ 1)) = some v ∧ v.1 = 1 ∧ lePS v.2 (H.getLast hne).cols

theorem regD_spec {ctx : List (ℕ × PS)} {u : Tm} (h : RegD H (H.getLast hne) ctx u) :
    TGood ctx u ∧ 1 ≤ u.y ∧ ZeroLe H ctx ∧ CtxW H hne ctx ∧ (u.y = 1 → u ≤ H.getLast hne) := by
  induction h with
  | @top c hc hc1 =>
    have hW := tgood_W hN he hne
    rw [W_eq hN he hne, tgood_iff] at hW
    have hct := hW.2.2.2 c (by rw [W_eq hN he hne] at hc; exact hc)
    rw [← W_eq hN he hne] at hct
    have hz : ZeroLe H [(1, (H.getLast hne).cols), (0, (Tm.node 0 H).cols)] :=
      zeroLe_cons ⟨(0, (Tm.node 0 H).cols), by simp, Or.inl rfl⟩ le_rfl _
    have hcw : CtxW H hne [(1, (H.getLast hne).cols), (0, (Tm.node 0 H).cols)] := by
      exact ⟨(1, (H.getLast hne).cols), by simp, rfl, Or.inl rfl⟩
    refine ⟨hct, hc1, hz, hcw, fun hc1' => ?_⟩
    have hg := (tgood_iff.mp (by rw [← Tm.eta c] at hct; exact hct)).1
    have := hg (1, (H.getLast hne).cols) (by simp) (by rw [hc1']) (1, (H.getLast hne).cols)
      (by simp [hc1'])
    exact (show c < H.getLast hne from by
      rw [Tm.lt_def]; rw [← Tm.eta c] at this ⊢; exact this).le
  | @child ctx s c hs hc hc1 ih =>
    obtain ⟨hst, hs1, hsz, hsw, hsW⟩ := ih
    have hs' := tgood_iff.mp (by rw [← Tm.eta s] at hst; exact hst)
    have hct : TGood ((s.y, s.cols) :: ctx) c := by
      have := hs'.2.2.2 c hc; rwa [Tm.eta] at this
    have hz : ZeroLe H ((s.y, s.cols) :: ctx) := zeroLe_cons hsz hs1 _
    have hcw : CtxW H hne ((s.y, s.cols) :: ctx) := by
      rw [CtxW, List.find?_cons]
      by_cases hsy : s.y ≤ 1
      · have : s.y = 1 := by omega
        exact ⟨(s.y, s.cols), by simp [hsy], this, (Tm.le_def _ _).mp (hsW this)⟩
      · simp only [hsy, decide_false]; exact hsw
    refine ⟨hct, hc1, hz, hcw, fun hc1' => ?_⟩
    have hg := (tgood_iff.mp (by rw [← Tm.eta c] at hct; exact hct)).1
    obtain ⟨v, hv, -, hvW⟩ := hcw
    have hlt := hg (s.y, s.cols) (by simp) (by rw [hc1']; exact hs1) v (by rw [hc1']; exact hv)
    have hlt' : ltPS c.cols v.2 := by simpa only [Tm.eta] using hlt
    have : c < H.getLast hne := by
      rw [Tm.lt_def]; exact ltPS_of_ltPS_of_lePS hlt' hvW
    exact this.le

/-- A region node: `W`, or a node below `W` reached through nodes with `y ≥ 1`. -/
def IsRegN (H : List Tm) (hne : H ≠ []) (u : Tm) : Prop :=
  u = H.getLast hne ∨ ∃ ctx, RegD H (H.getLast hne) ctx u

/-- A region term: a truncation of a region node. -/
def IsRegT (H : List Tm) (hne : H ≠ []) (s : Tm) : Prop :=
  ∃ u i, IsRegN H hne u ∧ s = .node u.y (u.cs.take i)

theorem regN_spec {u : Tm} (hu : IsRegN H hne u) :
    ∃ ctx, TGood ctx u ∧ ZeroLe H ctx ∧ 1 ≤ u.y ∧ (u.y = 1 → u ≤ H.getLast hne) := by
  rcases hu with rfl | ⟨ctx, hu⟩
  · exact ⟨_, tgood_W hN he hne, ⟨(0, (Tm.node 0 H).cols), by simp, Or.inl rfl⟩,
      by rw [W_y hN he hne], fun _ => le_rfl⟩
  · obtain ⟨h1, h2, h3, -, h5⟩ := regD_spec hN he hne hu
    exact ⟨ctx, h1, h3, h2, h5⟩

theorem regN_valid {u : Tm} (hu : IsRegN H hne u) : Valid u := by
  obtain ⟨ctx, h, -⟩ := regN_spec hN he hne hu; exact valid_of_tgood h

theorem regN_rg {u : Tm} (hu : IsRegN H hne u) : RG H u := by
  obtain ⟨ctx, h, hz, -⟩ := regN_spec hN he hne hu; exact rg_of_tgood u h hz

theorem regN_child {u c : Tm} (hu : IsRegN H hne u) (hc : c ∈ u.cs) (hc1 : 1 ≤ c.y) :
    IsRegN H hne c := by
  rcases hu with rfl | ⟨ctx, hu⟩
  · exact Or.inr ⟨_, .top hc hc1⟩
  · exact Or.inr ⟨_, .child hu hc hc1⟩

theorem regN_const {u c : Tm} (hu : IsRegN H hne u) (hc : c ∈ u.cs) (hc0 : c.y = 0) :
    Std c ∧ c < .node 0 H := by
  obtain ⟨ctx, h, hz, h1, -⟩ := regN_spec hN he hne hu
  have h' := tgood_iff.mp (by rw [← Tm.eta u] at h; exact h)
  have hct := h'.2.2.2 c hc
  exact ⟨std_of_tgood_y0 hct hc0, lt_of_tgood_y0 hct hc0 (zeroLe_cons hz h1 _)⟩

theorem regN_cst {u d : Tm} (hu : IsRegN H hne u) (hd : Cst u d) : Std d ∧ d < .node 0 H := by
  induction hd with
  | here hc h0 => exact regN_const hN he hne hu hc h0
  | deep hc h1 _ ih => exact ih (regN_child hN he hne hu hc h1)

theorem isRegT_of_regN {u : Tm} (hu : IsRegN H hne u) : IsRegT H hne u :=
  ⟨u, u.cs.length, hu, by rw [List.take_length, Tm.eta]⟩

theorem regT_take {s : Tm} (hs : IsRegT H hne s) (i : ℕ) :
    IsRegT H hne (.node s.y (s.cs.take i)) := by
  obtain ⟨u, j, hu, rfl⟩ := hs
  exact ⟨u, min j i, hu, by simp [List.take_take, Nat.min_comm]⟩

theorem regT_child {s c : Tm} (hs : IsRegT H hne s) (hc : c ∈ s.cs) (hc1 : 1 ≤ c.y) :
    IsRegT H hne c := by
  obtain ⟨u, j, hu, rfl⟩ := hs
  exact isRegT_of_regN hN he hne (regN_child hN he hne hu (List.mem_of_mem_take hc) hc1)

theorem regT_const {s c : Tm} (hs : IsRegT H hne s) (hc : c ∈ s.cs) (hc0 : c.y = 0) :
    Std c ∧ c < .node 0 H := by
  obtain ⟨u, j, hu, rfl⟩ := hs
  exact regN_const hN he hne hu (List.mem_of_mem_take hc) hc0

theorem regT_cst {s d : Tm} (hs : IsRegT H hne s) (hd : Cst s d) : Std d ∧ d < .node 0 H := by
  obtain ⟨u, j, hu, rfl⟩ := hs
  exact regN_cst hN he hne hu (hd.mono (fun c hc => List.mem_of_mem_take hc))

theorem regT_valid {s : Tm} (hs : IsRegT H hne s) : Valid s := by
  obtain ⟨u, j, hu, rfl⟩ := hs
  have hv := regN_valid hN he hne hu
  rw [← Tm.eta u] at hv
  exact hv.take j

theorem regT_y {s : Tm} (hs : IsRegT H hne s) : 1 ≤ s.y := by
  obtain ⟨u, j, hu, rfl⟩ := hs
  exact (regN_spec hN he hne hu).choose_spec.2.2.1

theorem regT_rg {s : Tm} (hs : IsRegT H hne s) : RG H s := by
  obtain ⟨u, j, hu, rfl⟩ := hs
  have hr := regN_rg hN he hne hu
  have hy := (regN_spec hN he hne hu).choose_spec.2.2.1
  obtain ⟨y, cs⟩ := u
  simp only [Tm.y_node, Tm.cs_node] at hy ⊢
  cases hr with
  | const _ => omega
  | high h1 hd hc =>
    exact .high h1 (hd.sublist (List.take_sublist _ _)) (fun c hc' => hc c (List.mem_of_mem_take hc'))

theorem regT_le_W {s : Tm} (hs : IsRegT H hne s) (h1 : s.y = 1) : s ≤ H.getLast hne := by
  obtain ⟨u, j, hu, rfl⟩ := hs
  have hle := (regN_spec hN he hne hu).choose_spec.2.2.2 h1
  have h2 := node_take_le u.y u.cs j
  rw [Tm.eta] at h2
  exact le_trans h2 hle

end Region

/-! ## P′ and ND -/

/-- **P′** (`proof/PROOF-3.md` §14.1): `Coll_A(x) < (m + 1, [x])` for a region term `x` with
`y(x) = m + 2`. -/
theorem coll_lt_single {A : List Tm} (hA : Desc A) : ∀ x : Tm, Valid x → RG A x → ∀ m : ℕ,
    x.y = m + 2 → coll A x < .node (m + 1) [x] := by
  intro x
  induction x using Tm.ind with
  | h y cs ih =>
    intro hv hr m hy
    simp only [Tm.y_node] at hy; subst hy
    cases hr with
    | high _ hd hcr =>
      rw [coll_high hA (by omega) hd hcr, if_neg (by omega)]
      simp only [show m + 2 - 1 = m + 1 by omega]
      rw [Tm.node_lt_node_iff]
      right; refine ⟨rfl, ?_⟩
      cases cs with
      | nil => exact List.nil_lt_cons _ _
      | cons x1 rest =>
        rw [List.map_cons, List.cons_lt_cons_iff]
        left
        have hx1 := hv.y_le (c := x1) (by simp)
        rcases Nat.lt_or_ge x1.y (m + 3) with hlt | hge
        · apply Tm.lt_of_y_lt
          rw [coll_y]; simp; omega
        · have hx1y : x1.y = (m + 1) + 2 := by omega
          have h1 := ih x1 (by simp) (hv.child (by simp)) (hcr x1 (by simp)) (m + 1) hx1y
          refine lt_of_lt_of_le h1 ?_
          have := node_take_le (m + 1 + 1) (x1 :: rest) 1
          simpa using this

section ND

variable {H : List Tm} (hN : Std (.node 0 H)) (he : isEps (.node 0 H) = true) (hne : H ≠ [])
include hN he hne

/-- `Coll_A` of the first child of a level-`1` region term is at most `W`
(`proof/PROOF-3.md` §14.1, from P′ and Claim Q). -/
theorem coll_first_le_W {s c : Tm} {rest : List Tm} (hs : IsRegT H hne s) (h1 : s.y = 1)
    (hcs : s.cs = c :: rest) : coll H c ≤ H.getLast hne := by
  have hv := regT_valid hN he hne hs
  have hcy : c.y ≤ 2 := by
    have := (show Valid (.node s.y s.cs) by rw [Tm.eta]; exact hv).y_le (c := c) (by rw [hcs]; simp)
    omega
  have hWy := W_y hN he hne
  rcases Nat.lt_or_ge c.y 2 with hlt | hge
  · apply le_of_lt; apply Tm.lt_of_y_lt; rw [coll_y, hWy]; omega
  have hc2 : c.y = 0 + 2 := by omega
  have hcR := regT_child hN he hne hs (c := c) (by rw [hcs]; simp) (by omega)
  have hHd : Desc H := desc_cs_of_std hN
  have hP := coll_lt_single hHd c (regT_valid hN he hne hcR)
    (regT_rg hN he hne hcR) 0 hc2
  refine le_of_lt (lt_of_lt_of_le hP ?_)
  have hsW := regT_le_W hN he hne hs h1
  have hWe := W_eq hN he hne
  have hse : s = .node 1 (c :: rest) := by rw [← Tm.eta s, h1, hcs]
  cases hWc : (H.getLast hne).cs with
  | nil =>
    exfalso
    rw [hse, hWe, hWc] at hsW
    have : Tm.node 1 [] < Tm.node 1 (c :: rest) :=
      (Tm.lt_iff_cs_lt (s := Tm.node 1 []) (t := Tm.node 1 (c :: rest)) rfl).mpr
        (List.nil_lt_cons _ _)
    exact absurd hsW (not_le.mpr this)
  | cons w1 ws =>
    have hcw : c ≤ w1 := by
      by_contra hcw
      push Not at hcw
      have : H.getLast hne < s := by
        rw [hse, hWe, hWc]
        exact (Tm.lt_iff_cs_lt (s := Tm.node 1 (w1 :: ws)) (t := Tm.node 1 (c :: rest)) rfl).mpr
          (List.cons_lt_cons_iff.mpr (Or.inl hcw))
      exact absurd hsW (not_le.mpr this)
    have h2 : Tm.node 1 [c] ≤ Tm.node 1 [w1] := by
      apply node_le_node_of
      rcases hcw.lt_or_eq with h | h
      · right; exact List.cons_lt_cons_iff.mpr (Or.inl h)
      · left; rw [h]
    refine le_trans h2 ?_
    rw [hWe, hWc]
    have := node_take_le 1 (w1 :: ws) 1
    simpa using this

/-- **ND** (`proof/PROOF-3.md` §14.1): `A + Coll_A(ch s)` drops no element of `A`. -/
theorem addT_noDrop {s : Tm} (hs : IsRegT H hne s) (h1 : s.y = 1) :
    addT H (s.cs.map (coll H)) = H ++ s.cs.map (coll H) := by
  cases hcs : s.cs with
  | nil => simp [addT]
  | cons c rest =>
    have hHd : Desc H := desc_cs_of_std hN
    rw [List.map_cons, addT_cons hHd]
    congr 1
    rw [List.takeWhile_eq_self_iff]
    intro x hx
    have hWx := getLast_le_of_desc hHd hne x hx
    have hcW := coll_first_le_W hN he hne hs h1 hcs
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_lt]
    exact le_trans hcW hWx

end ND

end Googology.Trans.PSS.Main

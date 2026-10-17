import Googology.Trans.PoR.InaccPsi.R2.SHTop

/-!
# LIFT-0 for every block `U_k(ξ)` of `R₂^C` below `T_ω`

For `ξ < T_ω` (`shTw`) and a level `k = m + 1`, `T(ξ) = T_k(ξ)` (`TkA ξ k`) is the least top of a `k`-nest
whose outer left end is above `ξ`, `x(ξ)` the outer left end of such a nest, and
`U(ξ) = U_k(ξ) = {u ∈ (ξ, T(ξ)] : u ≤₁ T(ξ)}`.  `R2.LiftR` and `R2.SHDeep` prove the shape of `U(ξ)`, the
reaches of its members, the one `<₂`-predecessor of `T(ξ)` and Theorem O^C for it.  Here, for every block:

* `lfS_spec` (`s(ξ) = min U(ξ)` exists, `s(ξ) ≤ x(ξ)`), `lfLh_closed` (**`(ξ, s(ξ))` is closed under
  `lh`**), `lfGap_reach` (a point of `(ξ, u)` that is `≤₁` a point `≥ u`, `u ∈ U(ξ)`, is in `U(ξ)`);
* `lfSame_way` (**a point below a member `u` of `U(ξ)` is related to all of `[u, T(ξ)]` in the same way**,
  for `≤₁` and `≤₂`, for every point `c < u`, not only those above `ξ`);
* `lfOnly_rel` (**`x(ξ) <₂ T(ξ)` is the only `<₂`-relation with an end in `U(ξ)`**);
* `lfNo_nest` (**no `k`-nest lies in a gap of `U(ξ)`**: a `k`-nest above `ξ` has its top `≥ T(ξ)`),
  `lfGap_nest` (**every gap of `U(ξ)` contains a `(k-1)`-nest**), `lfT_low` (**`T_{k-1}(ξ) < s_k(ξ)`**,
  `k ≥ 2`);
* `lfU_closed`, `lfU_indec` (`U(ξ)` is closed and its members are additively principal);
* `lfEnum_omega` (a set below `x`, cofinal in `x`, with finite proper initial segments, is enumerated by a
  strictly increasing `f : ℕ → Ord` with `sup f = x`), `lfBlock_omega` (**index `ω` at the left end**:
  `U(ξ) = {f n : n < ω} ∪ {x(ξ), T(ξ)}` with `f` strictly increasing and `sup f = x(ξ)`, so `x(ξ)` is the
  `ω`-th and `T(ξ)` the `(ω+1)`-th member of `U(ξ)`, the shape of Theorem O at every block);
* `lfSH_full`: all of these, for every `ξ < T_ω` and every level.

No new axiom.

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-- A point `α ∈ (ξ, u)` with `α ≤₁ g` for some `g ≥ u`, `u ≤₁ T`, is `≤₁ T`. -/
theorem lfGap_reach {T u α g : Ordinal.{0}} (hu : le1 u T) (hαu : α < u) (hg : u ≤ g)
    (h1 : le1 α g) : le1 α T :=
  le1_trans (le1_of_le_of_le1 hαu.le hg h1) hu

/-- **`(ξ, s)` is closed under `lh`** when `s` is the least `u > ξ` with `u ≤₁ T`. -/
theorem lfLh_closed {ξ T s : Ordinal.{0}} (hs : le1 s T)
    (hmin : ∀ u, ξ < u → u < s → ¬ le1 u T) : ∀ α, ξ < α → α < s → ∀ g, le1 α g → g < s := by
  intro α hξα hα g h1
  by_contra hg
  push Not at hg
  exact hmin α hξα hα (lfGap_reach hs hα hg h1)

/-- **`U(ξ)` is closed**: a point `u ∈ (0, T]` below which members of `U` are cofinal is in `U`. -/
theorem lfU_closed {T u : Ordinal.{0}} (huT : u ≤ T) (hu0 : 0 < u)
    (hcof : ∀ z < u, ∃ v, z < v ∧ v ≤ u ∧ le1 v T) : le1 u T :=
  le1_of_cof_left huT hu0 hcof

/-! ## Enumerations of order type `ω` -/

/-- **A set `S < x`, cofinal in `x`, whose proper initial segments are finite, has order type `ω`**: it is
the range of a strictly increasing `f : ℕ → Ord` with `sup f = x`. -/
theorem lfEnum_omega {S : Set Ordinal.{0}} {x : Ordinal.{0}} (hx : 0 < x) (hSx : ∀ u ∈ S, u < x)
    (hcof : ∀ z < x, ∃ u ∈ S, z < u) (hfin : ∀ s < x, (S ∩ Set.Iio s).Finite) :
    ∃ f : ℕ → Ordinal.{0}, StrictMono f ∧ (∀ u, u ∈ S ↔ ∃ n, f n = u) ∧ ⨆ n, f n = x := by
  classical
  obtain ⟨nx, hnx_spec, hnx_le⟩ : ∃ nx : Ordinal.{0} → Ordinal.{0},
      (∀ z < x, nx z ∈ S ∧ z < nx z) ∧ (∀ z u, u ∈ S → z < u → nx z ≤ u) := by
    refine ⟨fun z => sInf {u | u ∈ S ∧ z < u}, fun z hz => ?_, fun z u huS hzu =>
      csInf_le (OrderBot.bddBelow _) ⟨huS, hzu⟩⟩
    obtain ⟨u, huS, hzu⟩ := hcof z hz
    exact csInf_mem (s := {u | u ∈ S ∧ z < u}) ⟨u, huS, hzu⟩
  have hSne : S.Nonempty := by
    obtain ⟨u, huS, -⟩ := hcof 0 hx
    exact ⟨u, huS⟩
  obtain ⟨f, hf0, hfs⟩ : ∃ f : ℕ → Ordinal.{0}, f 0 = sInf S ∧ ∀ n, f (n + 1) = nx (f n) :=
    ⟨fun n => Nat.rec (motive := fun _ => Ordinal.{0}) (sInf S) (fun _ v => nx v) n, rfl,
      fun _ => rfl⟩
  have hfS : ∀ n, f n ∈ S := by
    intro n
    induction n with
    | zero => rw [hf0]; exact csInf_mem hSne
    | succ n ih => rw [hfs]; exact (hnx_spec _ (hSx _ ih)).1
  have hmono : StrictMono f := strictMono_nat_of_lt_succ fun n => by
    rw [hfs]; exact (hnx_spec _ (hSx _ (hfS n))).2
  have hsurj : ∀ u ∈ S, ∃ n, f n = u := by
    intro u
    induction u using WellFoundedLT.induction with
    | _ u IH =>
      intro huS
      set P := S ∩ Set.Iio u with hP
      rcases P.eq_empty_or_nonempty with he | hne
      · refine ⟨0, ?_⟩
        rw [hf0]
        refine le_antisymm (csInf_le (OrderBot.bddBelow S) huS) ?_
        by_contra hlt
        push Not at hlt
        have : sInf S ∈ P := ⟨csInf_mem hSne, hlt⟩
        rw [he] at this
        simp at this
      · have hPfin := hfin u (hSx u huS)
        set v := sSup P with hv
        have hvP : v ∈ P := hne.csSup_mem hPfin
        have hvmax : ∀ w ∈ P, w ≤ v := fun w hw => le_csSup hPfin.bddAbove hw
        obtain ⟨n, hn⟩ := IH v hvP.2 hvP.1
        refine ⟨n + 1, ?_⟩
        rw [hfs, hn]
        have hvx : v < x := hSx v hvP.1
        obtain ⟨hnS, hvn⟩ := hnx_spec v hvx
        refine le_antisymm (hnx_le v u huS hvP.2) ?_
        by_contra hlt
        push Not at hlt
        exact absurd (hvmax _ ⟨hnS, hlt⟩) (not_le.2 hvn)
  have hbdd : BddAbove (Set.range f) := ⟨x, by rintro _ ⟨n, rfl⟩; exact (hSx _ (hfS n)).le⟩
  refine ⟨f, hmono, fun u => ⟨hsurj u, ?_⟩, ?_⟩
  · rintro ⟨n, rfl⟩; exact hfS n
  · refine le_antisymm (ciSup_le fun n => (hSx _ (hfS n)).le) (le_of_forall_lt fun z hz => ?_)
    obtain ⟨u, huS, hzu⟩ := hcof z hz
    obtain ⟨n, rfl⟩ := hsurj u huS
    exact lt_of_lt_of_le hzu (le_ciSup hbdd n)

/-! ## The block clauses -/

section Blk

variable {m : ℕ} {ξ : Ordinal.{0}} {a b : ℕ → Ordinal.{0}} (hN : NestSeq (m + 1) a b)
  (hξ : ξ < a 0) (hT : b 0 = TkA ξ (m + 1))

include hN hξ in
/-- **`s(ξ) = min U(ξ)` exists**: a least `s > ξ` with `s ≤₁ T(ξ)`, and `s ≤ x(ξ)`. -/
theorem lfS_spec : ∃ s, ξ < s ∧ s ≤ a 0 ∧ le1 s (b 0) ∧ ∀ u, ξ < u → u < s → ¬ le1 u (b 0) := by
  have hx1 : le1 (a 0) (b 0) := le2_le1 (lv_x2 hN)
  set P : Set Ordinal.{0} := {u | ξ < u ∧ le1 u (b 0)} with hP
  have hne : P.Nonempty := ⟨a 0, hξ, hx1⟩
  have hmem := csInf_mem hne
  refine ⟨sInf P, hmem.1, csInf_le (OrderBot.bddBelow P) ⟨hξ, hx1⟩, hmem.2, fun u hξu hus hu1 => ?_⟩
  exact absurd (csInf_le (OrderBot.bddBelow P) ⟨hξu, hu1⟩) (not_le.2 hus)

include hN in
/-- **The members of `U(ξ)` are additively principal** (indecomposable). -/
theorem lfU_indec {u : Ordinal.{0}} (hu : u ≤ b 0) (hu1 : le1 u (b 0)) : Indec u := by
  rcases eq_or_lt_of_le hu with rfl | hlt
  · exact hN.indec (hN.b_mem (by omega))
  · exact indec_of_lt1 hu1 hlt

include hN hξ hT in
/-- **A point below a member `u` of `U(ξ)` is related to all of `[u, T(ξ)]` in the same way** (for `≤₁`
and for `≤₂`), for every point `c < u`, if `T(ξ) < T_ω`. -/
theorem lfSame_way (hW : b 0 < shTw) {u : Ordinal.{0}} (hu : le1 u (b 0)) :
    ∀ c < u, ∀ g, u ≤ g → g ≤ b 0 → ((le1 c g ↔ le1 c u) ∧ (le2 c g ↔ le2 c u)) := by
  intro c hcu g hug hgT
  refine ⟨⟨fun h => le1_of_le_of_le1 hcu.le hug h,
    fun h => le1_of_le_of_le1 (hcu.le.trans hug) hgT (le1_trans h hu)⟩, ?_⟩
  rcases eq_or_lt_of_le hug with rfl | hlt
  · exact Iff.rfl
  have huT : u < b 0 := hlt.trans_le hgT
  have hno : ∀ w, u ≤ w → w ≤ b 0 → ¬ le2 c w := by
    intro w huw hwT h2
    have hcw : c < w := hcu.trans_le huw
    have hc1 : le1 c (b 0) := le1_trans (le1_of_le_of_le1 hcu.le huw (le2_le1 h2)) hu
    have hr := shD_reach hcw h2 (lt_of_le_of_lt hwT hW)
    have hwe : w = b 0 := le_antisymm hwT (hr.2 _ hc1)
    rw [hwe] at h2 hcw
    have hca : a 0 = c := shD_oneLeft2 (lv_xT hN) hcw (lv_x2 hN) h2 hW
    exact gap_emptyA hN hξ hT (by rw [hca]; exact hcu) huT hu
  exact ⟨fun h => absurd h (hno g hug hgT), fun h => absurd h (hno u le_rfl huT.le)⟩

include hN hξ hT in
/-- **`x(ξ) <₂ T(ξ)` is the only `<₂`-relation with an end in `U(ξ)`** (if `T(ξ) < T_ω`): a pair
`c <₂ w` with `c ∈ U(ξ)` or with `w ≤ T(ξ)`, `w ≤₁ T(ξ)` is `(x(ξ), T(ξ))`. -/
theorem lfOnly_rel (hW : b 0 < shTw) {c w : Ordinal.{0}} (hcw : c < w) (h2 : le2 c w)
    (hend : (ξ < c ∧ c ≤ b 0 ∧ le1 c (b 0)) ∨ (w ≤ b 0 ∧ le1 w (b 0))) :
    c = a 0 ∧ w = b 0 := by
  rcases hend with ⟨hξc, hcT, hc1⟩ | ⟨hwT, hw1⟩
  · rcases lt_trichotomy c (a 0) with hlt | heq | hgt
    · exact absurd h2 (noLeft_belowA hN hξ hT hξc hlt hc1 w hcw)
    · subst heq
      exact ⟨rfl, succ_xA hN hξ hT w hcw h2⟩
    · rcases eq_or_lt_of_le hcT with he | hlt'
      · exact absurd (le2_le1 h2)
          (shD_noCross (lv_xT hN) (lv_x2 hN) hW c hgt hcT w (by rw [← he]; exact hcw))
      · exact absurd hc1 (gap_emptyA hN hξ hT hgt hlt')
  · rcases eq_or_lt_of_le hwT with he | hlt
    · rw [he] at h2 hcw
      exact ⟨(shD_oneLeft2 (lv_xT hN) hcw (lv_x2 hN) h2 hW).symm, he⟩
    · have hc1 : le1 c (b 0) := le1_trans (le2_le1 h2) hw1
      have hr := shD_reach hcw h2 (hlt.trans hW)
      exact absurd (hr.2 _ hc1) (not_le.2 hlt)

include hT in
/-- **No `k`-nest lies in a gap of `U(ξ)`**: every `k`-nest with outer left end above `ξ` has its top at
or above `T(ξ)`. -/
theorem lfNo_nest : ∀ a' b', NestSeq (m + 1) a' b' → ξ < a' 0 → b 0 ≤ b' 0 :=
  fun _ _ h h' => hT ▸ TkA_le h h'

include hN hξ hT in
/-- **Every gap of `U(ξ)` contains an `m`-nest** (`m = k - 1`): for consecutive members `u₁ < u₂` of
`{ξ} ∪ U(ξ)`, some `m`-nest lies in `(u₁, u₂)`. -/
theorem lfGap_nest {u1 u2 : Ordinal.{0}} (h1 : u1 = ξ ∨ (ξ < u1 ∧ le1 u1 (b 0))) (h12 : u1 < u2)
    (hu2T : u2 ≤ b 0) (hu2 : le1 u2 (b 0)) (hcons : ∀ u, u1 < u → u < u2 → ¬ le1 u (b 0)) :
    ∃ a' b', NestSeq m a' b' ∧ (0 < m → u1 < a' 0 ∧ b' 0 < u2) := by
  rcases le_or_gt u2 (a 0) with h | h
  · exact nests_belowA hN h hu2 u1 h12
  · have he2 : u2 = b 0 := by
      rcases eq_or_lt_of_le hu2T with e | e
      · exact e
      · exact absurd hu2 (gap_emptyA hN hξ hT h e)
    have hxu1 : a 0 ≤ u1 := by
      by_contra hc
      push Not at hc
      exact hcons (a 0) hc h (le2_le1 (lv_x2 hN))
    have he1 : u1 = a 0 := by
      rcases h1 with e | ⟨-, hu11⟩
      · rw [e] at hxu1; exact absurd hξ (not_lt.2 hxu1)
      · rcases eq_or_lt_of_le hxu1 with e | e
        · exact e.symm
        · exact absurd hu11 (gap_emptyA hN hξ hT e (h12.trans_le hu2T))
    refine ⟨fun i => a (i + 1), fun i => b (i + 1), hN.tail, fun hm => ⟨?_, ?_⟩⟩
    · rw [he1]; exact (hN.1 0 (by omega)).1
    · rw [he2]; exact (hN.1 0 (by omega)).2

include hN hξ hT in
/-- **Index `ω` at the left end of `U(ξ)`** (the shape of Theorem O, for every block): the members of
`U(ξ)` below `x(ξ)` are `f 0 < f 1 < ⋯` with `sup f = x(ξ)`, and `U(ξ) = {f n} ∪ {x(ξ), T(ξ)}`. -/
theorem lfBlock_omega (hcore : Set.Iic (b 0) ⊆ Core R2C) :
    ∃ f : ℕ → Ordinal.{0}, StrictMono f ∧
      (∀ u, (ξ < u ∧ u < a 0 ∧ le1 u (a 0)) ↔ ∃ n, f n = u) ∧ ⨆ n, f n = a 0 ∧
      (∀ u, ξ < u → ((u ≤ b 0 ∧ le1 u (b 0)) ↔ ((∃ n, f n = u) ∨ u = a 0 ∨ u = b 0))) := by
  set S : Set Ordinal.{0} := {u | ξ < u ∧ u < a 0 ∧ le1 u (a 0)} with hS
  have hx0 : 0 < a 0 := lt_of_le_of_lt zero_le hξ
  have hcof : ∀ z < a 0, ∃ u ∈ S, z < u := by
    intro z hz
    obtain ⟨y, hzy, hya, hy1⟩ := pred1_cof (lv_x2 hN) (lv_xT hN) (max z ξ) (max_lt hz hξ)
    exact ⟨y, ⟨lt_of_le_of_lt (le_max_right _ _) hzy, hya, hy1⟩,
      lt_of_le_of_lt (le_max_left _ _) hzy⟩
  have hfin : ∀ s < a 0, (S ∩ Set.Iio s).Finite := fun s hs =>
    (oCA hN hξ hT hcore s hs).subset fun u ⟨⟨h1, _, h3⟩, h4⟩ => ⟨h1, h4, h3⟩
  obtain ⟨f, hf, hfS, hsup⟩ := lfEnum_omega hx0 (fun u hu => hu.2.1) hcof hfin
  refine ⟨f, hf, hfS, hsup, fun u hξu => ?_⟩
  rw [U_shapeA hN hξ hT u, ← hfS u]
  exact ⟨fun h => h.elim (fun h' => Or.inl ⟨hξu, h'⟩) Or.inr,
    fun h => h.elim (fun h' => Or.inl ⟨h'.2.1, h'.2.2⟩) Or.inr⟩

end Blk

/-- **`T_{k-1}(ξ) < s_k(ξ)`** (`k = m + 2`, `ξ < T_ω`): every member `u` of `U_{m+2}(ξ)` is above
`T_{m+1}(ξ)` (it is a restart of level `m + 1`, so `(m+1)`-nests are cofinal below it). -/
theorem lfT_low (m : ℕ) {ξ u : Ordinal.{0}} (hξ : ξ < shTw) (hξu : ξ < u)
    (hu : u ≤ TkA ξ (m + 1 + 1)) (hu1 : le1 u (TkA ξ (m + 1 + 1))) : TkA ξ (m + 1) < u := by
  obtain ⟨-, -, hcof⟩ := (shRes_iff m).1 (shU_sub_res m hξ hξu hu hu1)
  obtain ⟨a, b, hN, hξa, hbu⟩ := hcof ξ hξu
  exact lt_of_le_of_lt (TkA_le hN hξa) hbu

/-- **LIFT-0 for the block `U_k(ξ)` of level `k = m + 1` above any `ξ < T_ω`** (Theorem SH, the
per-block clauses), with `T = T_k(ξ)`, `x = x_k(ξ)`, `U(ξ) = {u ∈ (ξ, T] : u ≤₁ T}`:
`U(ξ) = {f n : n < ω} ∪ {x, T}` with `f` strictly increasing, `sup f = x` (`x` has index `ω`, `T` index
`ω + 1`), `s = f 0 = min U(ξ)`; `T < T_ω`; `U(ξ)` is closed and its members are additively principal
with reach `T`; `(ξ, s)` is closed under `lh`; a point strictly between two consecutive members has its
reach below the upper one; `x <₂ T` is the only `<₂`-relation with an end in `U(ξ)`; a point below a
member `u` is related to all of `[u, T]` in the same way; every gap contains an `m`-nest and none
contains a `k`-nest; `T_{k-1}(ξ) < s` for `k ≥ 2`. -/
theorem lfSH_full {ξ : Ordinal.{0}} (hξ : ξ < shTw) (m : ℕ) :
    ∃ x : Ordinal.{0}, ∃ f : ℕ → Ordinal.{0}, ξ < x ∧ x < TkA ξ (m + 1) ∧ le2 x (TkA ξ (m + 1)) ∧
    TkA ξ (m + 1) < shTw ∧ StrictMono f ∧ ⨆ n, f n = x ∧ ξ < f 0 ∧
    (∀ u, ξ < u → ((u ≤ TkA ξ (m + 1) ∧ le1 u (TkA ξ (m + 1))) ↔
      ((∃ n, f n = u) ∨ u = x ∨ u = TkA ξ (m + 1)))) ∧
    (∀ u, ξ < u → u < f 0 → ¬ le1 u (TkA ξ (m + 1))) ∧
    (∀ u, ξ < u → u ≤ TkA ξ (m + 1) → (∀ z < u, ∃ v, z < v ∧ v ≤ u ∧ le1 v (TkA ξ (m + 1))) →
      le1 u (TkA ξ (m + 1))) ∧
    (∀ u, ξ < u → u ≤ TkA ξ (m + 1) → le1 u (TkA ξ (m + 1)) →
      Indec u ∧ IsReach R2C u (TkA ξ (m + 1))) ∧
    (∀ α, ξ < α → α < f 0 → ∀ g, le1 α g → g < f 0) ∧
    (∀ u1 u2, le1 u2 (TkA ξ (m + 1)) → (∀ u, u1 < u → u < u2 → ¬ le1 u (TkA ξ (m + 1))) →
      ∀ α, u1 < α → α < u2 → ∀ g, le1 α g → g < u2) ∧
    (∀ c w, c < w → le2 c w →
      ((ξ < c ∧ c ≤ TkA ξ (m + 1) ∧ le1 c (TkA ξ (m + 1))) ∨
        (w ≤ TkA ξ (m + 1) ∧ le1 w (TkA ξ (m + 1)))) → c = x ∧ w = TkA ξ (m + 1)) ∧
    (∀ u, le1 u (TkA ξ (m + 1)) → ∀ c < u, ∀ g, u ≤ g → g ≤ TkA ξ (m + 1) →
      ((le1 c g ↔ le1 c u) ∧ (le2 c g ↔ le2 c u))) ∧
    (∀ u1 u2, (u1 = ξ ∨ (ξ < u1 ∧ le1 u1 (TkA ξ (m + 1)))) → u1 < u2 → u2 ≤ TkA ξ (m + 1) →
      le1 u2 (TkA ξ (m + 1)) → (∀ u, u1 < u → u < u2 → ¬ le1 u (TkA ξ (m + 1))) →
      ∃ a' b', NestSeq m a' b' ∧ (0 < m → u1 < a' 0 ∧ b' 0 < u2)) ∧
    (∀ a' b', NestSeq (m + 1) a' b' → ξ < a' 0 → TkA ξ (m + 1) ≤ b' 0) ∧
    (∀ j, m = j + 1 → TkA ξ (j + 1) < f 0) := by
  have hTW := shTkA_lt_Tw hξ m
  obtain ⟨a, b, hN, hξa, hT⟩ := TkA_attained (hTW.trans shTw_lt_Om1)
  obtain ⟨-, -, -, -, -, hcore, -, -, -, -, -, hreach, -⟩ := shSH_block hξ m
  rw [← hT] at hcore hreach hTW ⊢
  obtain ⟨f, hf, hfS, hsup, hU⟩ := lfBlock_omega hN hξa hT hcore
  have hx1 : le1 (a 0) (b 0) := le2_le1 (lv_x2 hN)
  have hf0S : ξ < f 0 ∧ f 0 < a 0 ∧ le1 (f 0) (a 0) := (hfS (f 0)).2 ⟨0, rfl⟩
  have hf0U : le1 (f 0) (b 0) := le1_trans hf0S.2.2 hx1
  have hmin : ∀ u, ξ < u → u < f 0 → ¬ le1 u (b 0) := by
    intro u hξu hu hu1
    have huT : u ≤ b 0 := (hu.trans (hf0S.2.1.trans (lv_xT hN))).le
    rcases (hU u hξu).1 ⟨huT, hu1⟩ with ⟨n, rfl⟩ | rfl | rfl
    · exact absurd (hf.monotone (Nat.zero_le n)) (not_le.2 hu)
    · exact absurd (hu.trans hf0S.2.1) (lt_irrefl _)
    · exact absurd ((hu.trans hf0S.2.1).trans (lv_xT hN)) (lt_irrefl _)
  refine ⟨a 0, f, hξa, lv_xT hN, lv_x2 hN, hTW, hf, hsup, hf0S.1, hU, hmin,
    fun u hξu huT hcof => lfU_closed huT (lt_of_le_of_lt zero_le hξu) hcof,
    fun u hξu huT hu1 => ⟨lfU_indec hN huT hu1, hreach u hξu huT hu1⟩,
    lfLh_closed hf0U hmin, fun _ _ hu2 hcons => gap_lh hu2 hcons,
    fun c w hcw h2 hend => lfOnly_rel hN hξa hT hTW hcw h2 hend,
    fun u hu => lfSame_way hN hξa hT hTW hu,
    fun u1 u2 h1 h12 hu2T hu2 hcons => lfGap_nest hN hξa hT h1 h12 hu2T hu2 hcons,
    lfNo_nest hT, fun j hj => ?_⟩
  subst hj
  exact lfT_low j hξ hf0S.1 (by rw [← hT]; exact (hf0S.2.1.trans (lv_xT hN)).le)
    (by rw [← hT]; exact hf0U)

end Googology.Trans.PoR.InaccPsi.R2

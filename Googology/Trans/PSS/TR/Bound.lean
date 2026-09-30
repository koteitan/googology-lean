import Googology.Trans.PSS.TR.Eps

/-!
# Lemma M4 (Bound)

`proof/TR.md` §2, M4: let `s = (k, H)` be valid and epsilon, and let `E` be an
epsilon number above `Ω_k` with `𝒯_k(u) < E` for every witness `u` of `s`:

* the nodes `u` with `y = k` reached from `s` through nodes with `y ≥ k + 1`
  (`Reach k s u`), and
* the proper child-prefixes `(k, H_1..H_j)`, `j < r`.

Then every visible `ϑ_k`-subterm of the argument `Δ + η` of `𝒯_k(s)` is below
`E` (`bound`).  The proof is the invariant (I) (`inv`): for a reached inner node
`t` (level `≥ k + 1`) every visible `ϑ_k`-subterm of `𝒯(t)` is below `E`.

The first part collects how the visible subterms (`starS`) behave under the
operations of `tr.py`.
-/

namespace Googology.Trans.PSS.TR

open Forest Phi Ordinal

/-! ## Visible subterms under the operations -/

theorem starS_sublist (m : ℕ) {x y : List WP} (h : x.Sublist y) {z : WP} (hz : z ∈ starS m x) :
    z ∈ starS m y := by
  induction h with
  | slnil => exact hz
  | cons a _ ih => rw [starS_cons, List.mem_append]; exact Or.inr (ih hz)
  | cons_cons a _ ih =>
    rw [starS_cons, List.mem_append] at hz ⊢
    rcases hz with hz | hz
    · exact Or.inl hz
    · exact Or.inr (ih hz)

theorem addS_sublist (x y : List WP) : (addS x y).Sublist (x ++ y) := by
  cases y with
  | nil => simp [addS]
  | cons y0 y' =>
    rw [addS]
    refine List.Sublist.append ?_ (List.Sublist.refl _)
    rw [List.reverse_sublist.symm, List.reverse_reverse]
    exact List.dropWhile_sublist _

theorem foldl_addS_sublist : ∀ (xs : List (List WP)) (r : List WP),
    (xs.foldl addS r).Sublist (r ++ xs.flatten)
  | [], r => by simp
  | x :: xs, r => by
    rw [List.foldl_cons, List.flatten_cons, ← List.append_assoc]
    exact (foldl_addS_sublist xs _).trans (List.Sublist.append (addS_sublist r x)
      (List.Sublist.refl _))

theorem addAll_sublist (xs : List (List WP)) : (addAll xs).Sublist xs.flatten := by
  simpa using foldl_addS_sublist xs []

theorem mem_starS_single {m : ℕ} {p z : WP} (hz : z ∈ starS m [p]) :
    (p.lvl = m ∧ z = p) ∨ (m ≤ p.lvl ∧ z ∈ starS m p.arg) := by
  obtain ⟨k, a⟩ := p
  rw [starS_cons, starS_nil, List.append_nil, starP_th] at hz
  split_ifs at hz with h1 h2
  · simp at hz
  · rcases List.mem_cons.mp hz with rfl | hz
    · exact Or.inl ⟨h2, rfl⟩
    · exact Or.inr ⟨by simp; omega, hz⟩
  · exact Or.inr ⟨by simp; omega, hz⟩

theorem starS_single_of_lt {m : ℕ} {p : WP} (h : p.lvl < m) : starS m [p] = [] := by
  obtain ⟨k, a⟩ := p
  simp only [WP.lvl_th] at h
  rw [starS_cons, starS_nil, List.append_nil, starP_th, if_pos h]

theorem mem_starS_single_of_le {m : ℕ} {p z : WP} (h : m ≤ p.lvl) (hz : z ∈ starS m p.arg) :
    z ∈ starS m [p] := by
  obtain ⟨k, a⟩ := p
  simp only [WP.lvl_th, WP.arg_th] at h hz
  rw [starS_cons, starS_nil, List.append_nil, starP_th, if_neg (by omega)]
  split_ifs
  · exact List.mem_cons_of_mem _ hz
  · exact hz

theorem mem_starS_of_mem {m : ℕ} {x : List WP} {p : WP} (hp : p ∈ x) (hl : p.lvl = m) :
    p ∈ starS m x := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hp
  rw [starS_append, starS_cons]
  obtain ⟨k, a⟩ := p
  simp only [WP.lvl_th] at hl
  subst hl
  rw [starP_th, if_neg (lt_irrefl _), if_pos rfl]
  simp

/-- `ω^x` at level `m`: its visible `ϑ_k`-subterms are itself (if `m = k`) and
those of `x`. -/
theorem mem_starS_omegaExp {k m : ℕ} {x : List WP} {z : WP} (hz : z ∈ starS k [omegaExp x m]) :
    (m = k ∧ z = omegaExp x m) ∨ z ∈ starS k x := by
  cases x with
  | nil =>
    rw [omegaExp, starS_cons, starS_nil, List.append_nil, starP_th] at hz
    split_ifs at hz with h1 h2
    · simp at hz
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact Or.inl ⟨h2, by rw [omegaExp]⟩
      · simp at hz
    · simp at hz
  | cons p r =>
    have key : ∀ a : List WP, a.Sublist (p :: r) → z ∈ starS k [.th m a] →
        (m = k ∧ z = .th m a) ∨ z ∈ starS k (p :: r) := by
      intro a ha hz'
      rcases mem_starS_single hz' with ⟨h1, h2⟩ | ⟨-, h⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr (starS_sublist k ha h)
    rw [omegaExp] at hz ⊢
    split_ifs at hz ⊢ with h1 h2 h3
    · obtain ⟨rfl, -⟩ := h1
      exact Or.inr hz
    · exact key _ (List.dropLast_sublist _) hz
    · obtain ⟨-, rfl⟩ := h3
      exact key _ (List.sublist_cons_self _ _) hz
    · exact key _ (List.Sublist.refl _) hz

/-- `log_ω p` for `p` of level `> k`: its visible `ϑ_k`-subterms are those of `p`,
and possibly `1`. -/
theorem mem_starS_logOmega {k : ℕ} {p z : WP} (hk : k < p.lvl) (hz : z ∈ starS k (logOmega p)) :
    z ∈ starS k [p] ∨ z = one := by
  obtain ⟨m, a⟩ := p
  simp only [WP.lvl_th] at hk
  simp only [logOmega, WP.lvl_th, WP.arg_th] at hz
  have harg : ∀ {z}, z ∈ starS k a → z ∈ starS k [WP.th m a] := fun hz =>
    mem_starS_single_of_le (p := .th m a) (by simp; omega) hz
  split_ifs at hz with h1 h2 h3
  · exact Or.inl hz
  · rw [starS_append, List.mem_append] at hz
    rcases hz with hz | hz
    · exact Or.inl (harg hz)
    · rcases mem_starS_single hz with ⟨-, rfl⟩ | ⟨-, hz⟩
      · exact Or.inr rfl
      · simp [one] at hz
  · exact Or.inl (harg hz)
  · have hz' := starS_sublist k (addS_sublist _ _) hz
    rw [starS_append, List.mem_append] at hz'
    rcases hz' with hz' | hz'
    · rcases mem_starS_single hz' with ⟨h, -⟩ | ⟨-, hz'⟩
      · simp at h; omega
      · simp at hz'
    · exact Or.inl (harg hz')

theorem mem_starS_flatten {m : ℕ} :
    ∀ {xs : List (List WP)} {z : WP}, z ∈ starS m xs.flatten → ∃ x ∈ xs, z ∈ starS m x
  | [], z, hz => by simp at hz
  | x :: xs, z, hz => by
    rw [List.flatten_cons, starS_append, List.mem_append] at hz
    rcases hz with hz | hz
    · exact ⟨x, by simp, hz⟩
    · obtain ⟨x', hx', hz'⟩ := mem_starS_flatten hz
      exact ⟨x', by simp [hx'], hz'⟩

theorem isPrincipal_of_eps {E : Ordinal.{0}} (hE : ω ^ E = E) : IsPrincipal (· + ·) E := by
  rw [← hE]; exact isPrincipal_add_omega0_opow E

theorem one_lt_of_Om_lt {k : ℕ} {E : Ordinal.{0}} (h : Om k < E) : 1 < E :=
  lt_of_le_of_lt (one_le_Om k) h

theorem mem_starS_elim {m : ℕ} {z : WP} {x : List WP} (hx : NFS x) (hz : z ∈ starS m x) :
    NFP z ∧ z.lvl = m := by
  obtain ⟨h1, h2, -⟩ := starS_spec m x hx z hz
  exact ⟨h1, h2⟩

/-- A visible `ϑ_k`-subterm of a principal term of `T¹` is at most the term. -/
theorem val_le_of_mem_starS_single {k : ℕ} {p z : WP} (hp : NFP p) (hz : z ∈ starS k [p]) :
    z.val ≤ p.val := by
  rcases mem_starS_single hz with ⟨-, rfl⟩ | ⟨hk, hz'⟩
  · exact le_rfl
  · obtain ⟨m, a⟩ := p
    simp only [WP.lvl_th, WP.arg_th] at hk hz'
    obtain ⟨hz1, hz2, -⟩ := starS_spec k a hp.nfs z hz'
    rcases hk.lt_or_eq with hk | rfl
    · exact (val_lt_of_lvl_lt hz1 hp (by rw [hz2]; exact hk)).le
    · exact (star_lt_val hp z hz').le

/-! ## The argument of an epsilon image -/

theorem dOf_sublist (k : ℕ) (h : Tm) : (dOf k h).Sublist (logOmega (trTm h)) := by
  rw [(monOf_spec k h).1]; exact List.sublist_append_left _ _

theorem rhoOf_sublist (k : ℕ) (h : Tm) : (rhoOf k h).Sublist (logOmega (trTm h)) := by
  rw [(monOf_spec k h).1]; exact List.sublist_append_right _ _

/-- The visible `ϑ_k`-subterms of the argument of `𝒯_y((y, H))` (epsilon, `y ≥ k`)
are below an epsilon number `E > Ω_k`, if those of the images of the children and
of the inserted prefix image are. -/
theorem star_argOf_lt {k y : ℕ} {H : List Tm} {E : Ordinal.{0}} (hky : k ≤ y) (hne : H ≠ [])
    (hl : (H.getLast hne).y = y + 1) (hall : ∀ h ∈ H, h.y = y + 1) (hE : ω ^ E = E)
    (hΩ : Om k < E) (hep : insOf y H → ∀ z ∈ starS k [epOf y H], z.val < E)
    (hH : ∀ h ∈ H, ∀ z ∈ starS k [trTm h], z.val < E) :
    ∀ z ∈ starS k (argOf y H), z.val < E := by
  have h1E : 1 < E := one_lt_of_Om_lt hΩ
  -- through `log_ω` of a child
  have hlog : ∀ h ∈ H, ∀ z ∈ starS k (logOmega (trTm h)), z.val < E := by
    intro h hh z hz
    rcases mem_starS_logOmega (by rw [trTm_lvl, hall h hh]; omega) hz with hz | rfl
    · exact hH h hh z hz
    · rw [val_one]; exact h1E
  intro z hz
  rw [argOf_eq hne hl, starS_append, List.mem_append] at hz
  rcases hz with hz | hz
  · -- `Δ`
    have hd : deltaOf y H = dOf y (H.getLast hne) := by
      rw [deltaOf, List.getLast?_eq_some_getLast hne]; rfl
    rw [hd] at hz
    exact hlog _ (List.getLast_mem hne) z (starS_sublist k (dOf_sublist y _) hz)
  · -- `η'`
    have hη : ∀ z ∈ starS k (etaOf y H), z.val < E := by
      intro z hz
      have hz1 := starS_sublist k ((minusOnePlus_sublist _).trans (addAll_sublist _)) hz
      obtain ⟨x, hx, hzx⟩ := mem_starS_flatten hz1
      rw [List.mem_map] at hx
      obtain ⟨h, hh, rfl⟩ := hx
      have hh' : h ∈ H := List.mem_of_mem_drop hh
      rcases mem_starS_omegaExp hzx with ⟨hlv, rfl⟩ | hz2
      · -- `ω^ρ` of level `k`
        have hρn := (monOf_spec y h).2.2.1
        have hρlt : WP.valS (rhoOf y h) < E := by
          refine valS_lt_of_forall (isPrincipal_of_eps hE) (lt_trans zero_lt_one h1E)
            (fun q hq => ?_)
          have hqk : q.lvl ≤ k := by
            rw [← hlv]
            cases e : rhoOf y h with
            | nil => rw [e] at hq; simp at hq
            | cons q0 r =>
              rw [e] at hq hρn
              exact hρn.lvl_le_of_head (by simp [expLvl]) q hq
          rcases hqk.lt_or_eq with hqk | hqk
          · exact lt_trans (val_lt_Om_of_lvl_lt (hρn.1 q hq) hqk) hΩ
          · exact hlog h hh' q (starS_sublist k (rhoOf_sublist y h) (mem_starS_of_mem hq hqk))
        show (wOf y h).val < E
        rw [(wOf_spec y h).2.2.2, ← hE]
        exact (opow_lt_opow_iff_right one_lt_omega0).mpr hρlt
      · exact hlog h hh' z (starS_sublist k (rhoOf_sublist y h) hz2)
    unfold eta'Of at hz
    split_ifs at hz with hins
    · have hz1 := starS_sublist k (addS_sublist _ _) hz
      rw [starS_append, List.mem_append] at hz1
      rcases hz1 with hz1 | hz1
      · exact hep hins z hz1
      · exact hη z hz1
    · exact hη z hz

theorem Reach.mono {k y : ℕ} {l l' : List Tm} (hsub : ∀ c ∈ l, c ∈ l') {u : Tm}
    (h : Reach k (.node y l) u) : Reach k (.node y l') u := by
  cases h with
  | child hc hy => exact .child (hsub _ hc) hy
  | deep hc hcy hr => exact .deep (hsub _ hc) hcy hr

/-- **The invariant (I) of M4**: for a valid `t` of level `≥ k + 1` whose reached
nodes of level `k` have images below `E`, every visible `ϑ_k`-subterm of `𝒯(t)`
is below `E`. -/
theorem inv {k : ℕ} {E : Ordinal.{0}} (hE : ω ^ E = E) (hΩ : Om k < E) :
    ∀ (n : ℕ) (t : Tm), t.size ≤ n → Valid t → k + 1 ≤ t.y →
      (∀ u, Reach k t u → (trTm u).val < E) → ∀ z ∈ starS k [trTm t], z.val < E := by
  intro n
  induction n with
  | zero => intro t ht; exact absurd ht (by have := Tm.size_pos t; omega)
  | succ n ih =>
    intro t hsz hv hy hR z hz
    obtain ⟨y, ch⟩ := t
    simp only [Tm.y_node] at hy
    rcases eq_or_ne ch [] with rfl | hne
    · rw [trTm_leaf] at hz
      rcases mem_starS_single hz with ⟨h, -⟩ | ⟨-, hz⟩
      · simp at h; omega
      · simp at hz
    by_cases hl : (ch.getLast hne).y = y + 1
    · -- epsilon
      rw [trTm_eps' hne hl] at hz
      rcases mem_starS_single hz with ⟨h, -⟩ | ⟨-, hz⟩
      · simp at h; omega
      simp only [WP.arg_th] at hz
      refine star_argOf_lt (by omega) hne hl (hv.eps_all hne hl) hE hΩ (fun hins z hz => ?_)
        (fun h hh z hz => ?_) z hz
      · have hj := runStart_lt (ds := ch.map (dOf y)) (by simpa using hne)
        simp only [List.length_map] at hj
        refine ih _ ?_ (hv.take _) (by simpa using hy) (fun u hu => hR u (hu.mono
          (fun c hc => List.mem_of_mem_take hc))) z hz
        have := size_lt_of_sublist_dropLast (k := y) hne (take_sublist_dropLast hj)
        exact Nat.lt_succ_iff.mp (lt_of_lt_of_le this hsz)
      · refine ih h ?_ (hv.child hh) (by rw [hv.eps_all hne hl h hh]; omega)
          (fun u hu => hR u (.deep hh (by rw [hv.eps_all hne hl h hh]; omega) hu)) z hz
        have := Tm.size_lt_of_mem (y := y) hh
        omega
    · -- not epsilon
      rw [trTm_noneps hne hl] at hz
      rcases mem_starS_omegaExp hz with ⟨h, -⟩ | hz
      · omega
      have hz1 := starS_sublist k (addAll_sublist _) hz
      obtain ⟨x, hx, hzx⟩ := mem_starS_flatten hz1
      rcases List.mem_append.mp hx with hx | hx
      · unfold headPart at hx
        split_ifs at hx with h1 h2
        · rw [List.mem_singleton.mp hx] at hzx
          have hsub : (ch.filter (fun c => decide (c.y = y + 1))).Sublist ch.dropLast :=
            filter_sublist_dropLast hne _ (by simp [hl])
          have hvt : Valid (.node y (ch.filter (fun c => decide (c.y = y + 1)))) := by
            rw [hv.filter_hi]
            obtain ⟨m, hm⟩ := takeWhile_eq_take (fun c => decide (c.y = y + 1)) ch
            rw [hm]; exact hv.take m
          refine ih _ ?_ hvt (by simpa using hy)
            (fun u hu => hR u (hu.mono (fun c hc => (List.mem_filter.mp hc).1))) z hzx
          have := size_lt_of_sublist_dropLast (k := y) hne hsub
          omega
        · rw [List.mem_singleton.mp hx] at hzx
          rcases mem_starS_single hzx with ⟨h, -⟩ | ⟨-, hz⟩
          · simp at h; omega
          · simp at hz
        · simp at hx
      · rw [List.mem_map] at hx
        obtain ⟨c, hc, rfl⟩ := hx
        have hc' := (List.mem_filter.mp hc).1
        rcases lt_trichotomy c.y k with hck | hck | hck
        · rw [starS_single_of_lt (by rw [trTm_lvl]; exact hck)] at hzx
          simp at hzx
        · exact lt_of_le_of_lt (val_le_of_mem_starS_single (trTm_nfp c) hzx)
            (hR c (.child hc' hck))
        · refine ih c ?_ (hv.child hc') hck (fun u hu => hR u (.deep hc' hck hu)) z hzx
          have := Tm.size_lt_of_mem (y := y) hc'
          omega

/-- **Lemma M4 (Bound)**: for a valid epsilon `s = (k, H)` and an epsilon number
`E > Ω_k` above the images of all witnesses of `s`, every visible
`ϑ_k`-subterm of the argument `Δ + η` of `𝒯_k(s)` is below `E`. -/
theorem bound {k : ℕ} {H : List Tm} {E : Ordinal.{0}} (hv : Valid (.node k H)) (hne : H ≠ [])
    (hl : (H.getLast hne).y = k + 1) (hE : ω ^ E = E) (hΩ : Om k < E)
    (hw1 : ∀ u, Reach k (.node k H) u → (trTm u).val < E)
    (hw2 : ∀ j < H.length, (trTm (.node k (H.take j))).val < E) :
    ∀ z ∈ starS k (argOf k H), z.val < E := by
  refine star_argOf_lt le_rfl hne hl (hv.eps_all hne hl) hE hΩ (fun hins z hz => ?_)
    (fun h hh z hz => ?_)
  · have hj := runStart_lt (ds := H.map (dOf k)) (by simpa using hne)
    simp only [List.length_map] at hj
    exact lt_of_le_of_lt (val_le_of_mem_starS_single (trTm_nfp _) hz) (hw2 _ hj)
  · have hhy := hv.eps_all hne hl h hh
    exact inv hE hΩ _ h le_rfl (hv.child hh) (by omega)
      (fun u hu => hw1 u (.deep hh (by omega) hu)) z hz

end Googology.Trans.PSS.TR

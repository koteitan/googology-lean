import Googology.Trans.PSS.Main.EpsCore

/-!
# Epsilon roots and the `ϑ_0`-subterms of `𝒯(N)`

Tools for `Bar_T` (`proof/PROOF-3.md` §13.3, §14.2), proved from Mono\*, Lemma TR
and the comparison (C) of `TR/Cited.lean`:

* `val_trTm_root`, `exists_root`: a principal term of level `0` below `o(N)` is
  `𝒯(z)` for a standard root `z ≤ N`.
* **KEY** (`key_eps_root`): for a standard epsilon root `N = (0, H)` with last run
  starting at `j`, every standard epsilon root `z < N` has level
  `Δ(z) ≤ Δ(N)`, or `z ≤ (0, H_1 … H_j)`.  (This replaces the lemmas CL, FD, LV.)
* **EL** (`argV_lt_of_level_eq`): a proper `ϑ_0`-subterm of `ϑ_0(Δ + η)` of the same
  level `Δ` has a smaller argument.
* `level_gt_of_sufMax`: a suffix maximum below `ϑ_0(Δ + η)` has level `> Δ`.
* `mem_sub0_of_between` ([W07a] Lemma 6.4 (a), read on `T¹`): if
  `γ ≤ β < γ⁺ = ϑ_0(arg γ + 1)`, then `γ` is a `ϑ_0`-subterm of `β`.
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Order Phi Forest

/-! ## Terms of roots -/

theorem val_trTm_root {z : Tm} (hz : Std z) : (trTm z).val = ordOf [z] := by
  have := tr [z] (stdOrd_single hz)
  rw [valS_trNode] at this; simpa using this

theorem exists_root {r : WP} (hr : NFP r) {N : Tm} (hN : Std N) (hle : r.val ≤ ordOf [N]) :
    ∃ z, Std z ∧ trTm z = r ∧ z ≤ N := by
  obtain ⟨S, hS, hSr⟩ : ∃ S, StdOrd S ∧ ordOf S = r.val := by
    rcases hle.lt_or_eq with h | h
    · exact exists_ordOf_eq (stdOrd_single hN) h
    · exact ⟨[N], stdOrd_single hN, h.symm⟩
  rcases S with _ | ⟨z, _ | ⟨z', S'⟩⟩
  · rw [ordOf_nil] at hSr; exact absurd hSr.symm (val_pos hr).ne'
  · have hz : Std z := ((stdOrd_iff _).mp hS).2 z (by simp)
    refine ⟨z, hz, eq_of_val_eq (trTm_nfp z) hr (by rw [val_trTm_root hz, hSr]), ?_⟩
    by_contra hlt
    push Not at hlt
    have := ordOf_single_lt hN hz hlt
    rw [hSr] at this
    exact absurd hle (not_le.mpr this)
  · exact absurd (hSr ▸ pr_val hr) (not_pr_of_two hS)

/-! ## The epsilon case of `𝒯` at the root -/

theorem trTm_root_eps {H : List Tm} (hN : Std (.node 0 H)) (he : isEps (.node 0 H) = true) :
    H ≠ [] ∧ (∀ c ∈ H, c.y = 1) ∧
      trTm (.node 0 H) = .th 0 (deltaOf 0 H ++ eta'Of 0 H) := by
  have hne : H ≠ [] := by intro h; subst h; simp [isEps] at he
  have hall : ∀ c ∈ H, c.y = 1 := fun c hc => y_of_eps_child hN he hc
  have hl : (H.getLast hne).y = 0 + 1 := by rw [hall _ (List.getLast_mem hne)]
  refine ⟨hne, hall, ?_⟩
  rw [trTm_eps' hne hl, argOf_eq hne hl]

theorem argD_eps {H : List Tm} (hne : H ≠ []) (hl : (H.getLast hne).y = 0 + 1) :
    argD (deltaOf 0 H ++ eta'Of 0 H) = deltaOf 0 H ∧ argE (deltaOf 0 H ++ eta'Of 0 H) = eta'Of 0 H := by
  obtain ⟨-, h2, -⟩ := deltaOf_spec hne hl
  obtain ⟨-, h4⟩ := eta'Of_spec 0 H
  have hE : ∀ q ∈ eta'Of 0 H, q.lvl = 0 := fun q hq => by have := h4 q hq; omega
  constructor
  · unfold argD
    rw [List.takeWhile_append_of_pos (fun q hq => by simp [h2 q hq])]
    cases h : eta'Of 0 H with
    | nil => simp
    | cons q r => simp [hE q (by rw [h]; simp)]
  · unfold argE
    rw [List.dropWhile_append_of_pos (fun q hq => by simp [h2 q hq])]
    cases h : eta'Of 0 H with
    | nil => simp
    | cons q r => simp [hE q (by rw [h]; simp)]

/-! ## KEY -/

/-- Two lists in the lexicographic order: a proper prefix, or a first difference. -/
theorem list_lt_cases : ∀ {B H : List Tm}, B < H →
    (∃ P, H = B ++ P ∧ P ≠ []) ∨ ∃ C b h B' H', B = C ++ b :: B' ∧ H = C ++ h :: H' ∧ b < h
  | [], H, h => by
    left; refine ⟨H, rfl, fun e => ?_⟩; subst e; exact List.not_lt_nil _ h
  | b :: B, [], h => absurd h (List.not_lt_nil _)
  | b :: B, c :: H, h => by
    rcases List.cons_lt_cons_iff.mp h with h1 | ⟨e, h2⟩
    · right; exact ⟨[], b, c, B, H, rfl, rfl, h1⟩
    · subst e
      rcases list_lt_cases h2 with ⟨P, hP1, hP⟩ | ⟨C, b', h', B', H', hB1, hH1, hb⟩
      · left; exact ⟨P, by rw [hP1]; rfl, hP⟩
      · right; exact ⟨b :: C, b', h', B', H', by rw [hB1]; rfl, by rw [hH1]; rfl, hb⟩

theorem dOf_run {H : List Tm} (hne : H ≠ []) {h : Tm} (hh : h ∈ H.drop (jOf 0 H)) :
    dOf 0 h = deltaOf 0 H := by
  have hds : H.map (dOf 0) ≠ [] := by simpa using hne
  have := runStart_spec hds (dOf 0 h) (by
    rw [← List.map_drop]; exact List.mem_map.mpr ⟨h, hh, rfl⟩)
  rw [this, List.getLast_map, deltaOf, List.getLast?_eq_some_getLast hne]; rfl

theorem deltaOf_eq_last {B : List Tm} (hne : B ≠ []) : deltaOf 0 B = dOf 0 (B.getLast hne) := by
  rw [deltaOf, List.getLast?_eq_some_getLast hne]; rfl

/-- **KEY.**  An epsilon root below `N = (0, H)` has level at most `Δ(N)`, or lies
below `(0, H_1 … H_j)` (`j` the start of the last run). -/
theorem key_eps_root {H : List Tm} (hN : Std (.node 0 H)) (hNe : isEps (.node 0 H) = true)
    {z : Tm} (hz : Std z) (hze : isEps z = true) (hzN : z < .node 0 H) :
    WP.valS (deltaOf 0 z.cs) ≤ WP.valS (deltaOf 0 H) ∨ z ≤ .node 0 (H.take (jOf 0 H)) := by
  obtain ⟨hHne, hH1, -⟩ := trTm_root_eps hN hNe
  have hzeq := std_node_y hz
  set B := z.cs with hB
  have hBne : B ≠ [] := by intro h; rw [hzeq, h] at hze; simp [isEps] at hze
  have hBH : B < H := by
    rw [hzeq] at hzN
    exact (Tm.lt_iff_cs_lt (s := Tm.node 0 B) (t := Tm.node 0 H) rfl).mp hzN
  have hvN := valid_of_std hN
  have hvz : Valid (.node 0 B) := by rw [← hzeq]; exact valid_of_std hz
  have hdB : Desc B := hvz.desc
  set j := jOf 0 H with hj
  have hz_le_prefix : ∀ P, P <+: H.take j → B = P → z ≤ .node 0 (H.take j) := by
    intro P hP e
    rw [hzeq, e]; exact le_of_prefix_node hP
  rcases list_lt_cases hBH with ⟨P, hHBP, hP⟩ | ⟨C, b, h, B', H', hBC, hHC, hbh⟩
  · -- `B` is a proper prefix of `H`
    by_cases hlen : B.length ≤ j
    · right
      refine hz_le_prefix B ?_ rfl
      rw [hHBP, List.take_append, List.take_of_length_le hlen]
      exact List.prefix_append _ _
    · left
      have hmem : B.getLast hBne ∈ H.drop j := by
        rw [hHBP, List.drop_append_of_le_length (by omega)]
        apply List.mem_append_left
        have hdne : B.drop j ≠ [] := by simp; omega
        rw [← List.getLast_drop hdne]
        exact List.getLast_mem hdne
      rw [deltaOf_eq_last hBne, dOf_run hHne hmem]
  · -- a first difference `b < h`
    by_cases hlen : C.length < j
    · right
      apply le_of_lt
      rw [hzeq]
      refine (Tm.lt_iff_cs_lt (s := Tm.node 0 z.cs) (t := Tm.node 0 (H.take j)) rfl).mpr ?_
      rw [← hB, hBC, hHC, List.take_append, List.take_of_length_le (by omega)]
      obtain ⟨k, hk⟩ : ∃ k, j - C.length = k + 1 := ⟨j - C.length - 1, by omega⟩
      rw [hk, List.take_cons]
      exact List.append_left_lt (List.cons_lt_cons_iff.mpr (Or.inl hbh))
      omega
    · left
      have hhmem : h ∈ H.drop j := by
        rw [hHC, List.drop_append_of_le_length (by omega)]
        exact List.mem_append_right _ (List.mem_cons_self)
      rw [deltaOf_eq_last hBne, ← dOf_run hHne hhmem]
      -- the last child of `z` is at most `b < h`
      have hlastb : B.getLast hBne ≤ b := by
        have hd2 : Desc (b :: B') := by
          have := hdB; rw [hBC] at this; exact (List.pairwise_append.mp this).2.1
        have e : B.getLast hBne = (b :: B').getLast (by simp) := by
          simp only [hBC]; rw [List.getLast_append_of_ne_nil _ (by simp)]
        rw [e]
        have hm := List.getLast_mem (l := b :: B') (by simp)
        rcases List.mem_cons.mp hm with h' | h'
        · rw [h']
        · exact (List.pairwise_cons.mp hd2).1 _ h'
      have hmem_last : B.getLast hBne ∈ B := List.getLast_mem hBne
      have hhH : h ∈ H := by rw [hHC]; simp
      have hle := mono_le (hvz.child hmem_last) (hvN.child hhH) (le_trans hlastb hbh.le)
      exact (d_rho_mono hle).1

/-! ## EL -/

theorem argD_append_argE (a : List WP) : argD a ++ argE a = a := List.takeWhile_append_dropWhile

theorem argV_split (q : WP) : argV q = WP.valS (argD q.arg) + WP.valS (argE q.arg) := by
  rw [argV, ← valS_append, argD_append_argE]

theorem sizeS_prefix {a b : List WP} (h : a <+: b) : WP.sizeS a ≤ WP.sizeS b := by
  obtain ⟨c, rfl⟩ := h; rw [WP.sizeS_append]; omega

theorem argE_lvl {a : List WP} (ha : NFS a) : ∀ q ∈ argE a, q.lvl = 0 := by
  intro q hq
  have := (splitLevel_spec ha 1).2.2.2.2 q hq
  omega

theorem argD_lvl (a : List WP) : ∀ q ∈ argD a, 1 ≤ q.lvl := by
  intro q hq
  simpa using List.mem_takeWhile_imp hq

/-- The summands of `argE` (of level `0`) of a principal term are below it. -/
theorem valS_argE_lt {μ : WP} (hμ : NFP μ) (hμ0 : μ.lvl = 0) : WP.valS (argE μ.arg) < μ.val := by
  obtain ⟨m, a⟩ := μ
  simp only [WP.lvl_th] at hμ0; subst hμ0
  have hsub : (argE a).Sublist a := List.dropWhile_sublist _
  rw [valS_eq_sum_map]
  apply sum_lt_of_forall_lt (pr_val hμ)
  intro v hv
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv
  have hqa : q ∈ a := hsub.subset hq
  have hq0 : q.lvl = 0 := argE_lvl hμ.nfs q hq
  have hqn : NFP q := hμ.of_mem hqa
  refine star_lt_val hμ q (mem_starS_of hqa ?_)
  obtain ⟨m', a'⟩ := q
  simp only [WP.lvl_th] at hq0; subst hq0
  simp [starP_th]

theorem NFP.nfs' {q : WP} (h : NFP q) : NFS q.arg := by
  obtain ⟨m, a⟩ := q; exact h.nfs

theorem nfs_of_append_left {a b : List WP} (h : NFS (a ++ b)) : NFS a :=
  h.sublist (List.sublist_append_left _ _)

theorem val_le_valS_of_mem {x : List WP} {p : WP} (hp : p ∈ x) : p.val ≤ WP.valS x := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hp
  rw [valS_append, WP.valS_cons]
  exact le_trans le_self_add le_add_self

/-- **EL** (`proof/PROOF-3.md` §14.2): a proper `ϑ_0`-subterm of `ϑ_0(Δ + η)` of the same
level `Δ` has a smaller argument. -/
theorem argV_lt_of_level_eq {Δ η : List WP} (hα : NFP (.th 0 (Δ ++ η))) (hη : argE (Δ ++ η) = η)
    {μ : WP} (hμ : μ ∈ sub0 (.th 0 (Δ ++ η))) (hμα : μ ≠ .th 0 (Δ ++ η))
    (hlev : WP.valS (argD μ.arg) = WP.valS Δ) : argV μ < WP.valS (Δ ++ η) := by
  obtain ⟨hμn, hμ0⟩ := sub0_spec hα hμ
  have hΔn : NFS Δ := nfs_of_append_left hα.nfs
  have hDμ : argD μ.arg = Δ := eq_of_valS_eq ((NFP.nfs' hμn).takeWhile _) hΔn hlev
  rw [sub0_th] at hμ
  have hμ' : μ ∈ starS 0 (Δ ++ η) := by
    rcases List.mem_cons.mp hμ with h | h
    · exact absurd h hμα
    · exact h
  rw [starS_append, List.mem_append] at hμ'
  rcases hμ' with h | h
  · exfalso
    have h1 := (starS_spec 0 Δ hΔn μ h).2.2
    obtain ⟨m, a⟩ := μ
    simp only [WP.size_th] at h1
    have h2 := sizeS_prefix (List.takeWhile_prefix (fun q => decide (1 ≤ q.lvl)) (l := a))
    have : argD a = Δ := hDμ
    unfold argD at this
    rw [this] at h2
    omega
  · obtain ⟨p, hp, hμp⟩ := mem_starS h
    have hηn : NFS η := by rw [← hη]; exact hα.nfs.dropWhile _
    have hp0 : p.lvl = 0 := argE_lvl hα.nfs p (by rw [hη]; exact hp)
    have hle1 : μ.val ≤ p.val := val_le_of_mem_starP0 (hηn.1 p hp) hp0 hμp
    have hle2 : p.val ≤ WP.valS η := val_le_valS_of_mem hp
    rw [argV_split, hDμ, valS_append]
    exact (add_lt_add_iff_left _).mpr (lt_of_lt_of_le (valS_argE_lt hμn hμ0) (le_trans hle1 hle2))

/-- A suffix maximum below `ϑ_0(Δ + η)` has level above `Δ`. -/
theorem level_gt_of_sufMax {Δ η : List WP} (hα : NFP (.th 0 (Δ ++ η))) (hΔ : argD (Δ ++ η) = Δ)
    (hη : argE (Δ ++ η) = η) {r : WP} (hr : SufMax (.th 0 (Δ ++ η)) r)
    (hrα : r.val < (WP.th 0 (Δ ++ η)).val) : WP.valS Δ < WP.valS (argD r.arg) := by
  have h1 : argV (.th 0 (Δ ++ η)) < argV r := hr.2.2 _ self_mem_sub0 hrα
  rw [argV_th] at h1
  obtain ⟨hrn, hr0⟩ := sub0_spec hα hr.1
  have hΔn : NFS Δ := nfs_of_append_left hα.nfs
  by_contra hle
  push Not at hle
  rcases hle.lt_or_eq with hlt | heq
  · have hgap := gap_of_lt (m := 1) hΔn ((NFP.nfs' hrn).takeWhile _) (fun q hq => by
      rw [← hΔ] at hq; exact argD_lvl _ q hq) (argD_lvl _) hlt
    have hηr : WP.valS (argE r.arg) < Om 1 :=
      valS_lt_Om ((NFP.nfs' hrn).dropWhile _) (m := 0) (fun q hq => le_of_eq (argE_lvl (NFP.nfs' hrn) q hq))
    have : argV r < WP.valS (Δ ++ η) := by
      rw [argV_split, valS_append]
      calc WP.valS (argD r.arg) + WP.valS (argE r.arg) < WP.valS (argD r.arg) + Om 1 :=
            (add_lt_add_iff_left _).mpr hηr
        _ ≤ WP.valS Δ := hgap
        _ ≤ WP.valS Δ + WP.valS η := le_self_add
    exact absurd h1 (not_lt.mpr this.le)
  · have hne : r ≠ .th 0 (Δ ++ η) := fun e => by rw [e] at hrα; exact lt_irrefl _ hrα
    have := argV_lt_of_level_eq hα hη hr.1 hne heq
    exact absurd h1 (not_lt.mpr this.le)

/-! ## [W07a] Lemma 6.4 (a) on `T¹` -/

theorem nfp_succ {γ : WP} (hγ : NFP γ) (hγ0 : γ.lvl = 0) : NFP (.th 0 (γ.arg ++ [TR.one])) := by
  obtain ⟨m, a⟩ := γ
  simp only [WP.lvl_th] at hγ0; subst hγ0
  refine nfp_th ⟨fun p hp => ?_, ?_⟩ (fun p hp => ?_)
  · rcases List.mem_append.mp hp with hp | hp
    · exact hγ.of_mem hp
    · rw [List.mem_singleton.mp hp]; exact nfp_one
  · rw [List.pairwise_append]
    refine ⟨hγ.nfs.2, List.pairwise_singleton _ _, fun a' ha' b hb => ?_⟩
    rw [List.mem_singleton.mp hb, val_one]
    exact one_le_val (hγ.of_mem ha')
  · rcases List.mem_append.mp hp with hp | hp
    · exact hγ.lvl_le hp
    · rw [List.mem_singleton.mp hp]; simp [TR.one]

/-- **[W07a] Lemma 6.4 (a)**, read on `T¹`: if `γ ≤ β < γ⁺ = ϑ_0(arg γ + 1)`, then `γ` is a
`ϑ_0`-subterm of `β`.  Proved from the comparison (C). -/
theorem mem_sub0_of_between {γ : WP} (hγ : NFP γ) (hγ0 : γ.lvl = 0) :
    ∀ (n : ℕ) (β : WP), β.size ≤ n → NFP β → β.lvl = 0 → γ.val ≤ β.val →
      β.val < (WP.th 0 (γ.arg ++ [TR.one])).val → γ ∈ sub0 β := by
  have hγp := nfp_succ hγ hγ0
  obtain ⟨m, A⟩ := γ
  simp only [WP.lvl_th] at hγ0; subst hγ0
  intro n
  induction n with
  | zero => intro β hs; exact absurd hs (by have := WP.size_pos β; omega)
  | succ n ih =>
    intro β hs hβ hβ0 hle hlt
    obtain ⟨m', B⟩ := β
    simp only [WP.lvl_th] at hβ0; subst hβ0
    rcases hle.lt_or_eq with hγβ | heq
    · -- `β < γ⁺` forces `B ≤ A`
      have hBA : WP.valS B ≤ WP.valS A := by
        rcases (val_lt_val_iff hβ hγp).mp hlt with ⟨h, -⟩ | ⟨s, hs', hβs⟩
        · rw [valS_append, valS_single, val_one] at h
          exact Order.lt_add_one_iff.mp h
        · exfalso
          rw [starS_append, List.mem_append] at hs'
          rcases hs' with hs' | hs'
          · exact absurd (lt_of_le_of_lt hβs (star_lt_val hγ s hs')) (not_lt.mpr hγβ.le)
          · simp [starS_cons, starP_th, TR.one] at hs'
            subst hs'
            rw [show (WP.th 0 []).val = 1 from val_one] at hβs
            have := lt_of_lt_of_le hγβ hβs
            exact absurd this (not_lt.mpr (one_le_val hγ))
      -- `γ < β` then gives a subterm `s` of `B` with `γ ≤ s`
      rcases (val_lt_val_iff hγ hβ).mp hγβ with ⟨h, -⟩ | ⟨s, hs', hγs⟩
      · exact absurd h (not_lt.mpr hBA)
      · obtain ⟨hsn, hs0, hssz⟩ := starS_spec 0 B hβ.nfs s hs'
        have hsβ : s.val < (WP.th 0 B).val := star_lt_val hβ s hs'
        have := ih s (by simp at hs; omega) hsn hs0 hγs (lt_trans hsβ hlt)
        exact sub0_mono (by rw [sub0_th]; exact List.mem_cons_of_mem _ hs') _ this
    · have := eq_of_val_eq hγ hβ heq
      rw [this]; exact self_mem_sub0

end Googology.Trans.PSS.Main

import Googology.Trans.PSS.Main.FactBar

/-!
# Bar at `ω^ζ` with `ζ` additive principal (`proof/PROOF-2.md` §11.3 (b))

**Fact BAR₁** (`factBar1`): for `ζ ∈ P` not an epsilon number with
`ω^ζ ∈ (1, T¹ ∩ Ω_1)`, `bar(ω^ζ)` is the largest epsilon number `≤ ζ`, or `1` if
there is none.  (This is [CW12] Lemma 5.10 (2), (3) with `k = 1`; here it is
proved from [CW12] Def 5.1.)

The term of `ω^ζ` is `ϑ_0(q)` with `q` the term of `ζ`.  Def 5.1 takes
`α_{n-1}`, which is the largest epsilon `ϑ_0`-subterm of `q`
(a subterm `r` with a larger argument than `ϑ_0(q)` must be epsilon, since
`arg r < r` otherwise), and the largest epsilon subterm of `q` is the largest
epsilon number `≤ q` (`exists_eps_sub`: follow the leading summands).
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Order

theorem InE.one_lt {ε : Ordinal.{0}} (h : InE ε) : 1 < ε := by
  by_contra h1
  push Not at h1
  rcases h1.lt_or_eq with h0 | h1
  · rw [Order.lt_one_iff.mp h0] at h; simp [InE] at h
  · rw [h1] at h; simp [InE] at h; exact absurd h (ne_of_gt one_lt_omega0)

theorem InE.pr {ε : Ordinal.{0}} (h : InE ε) : Pr ε := by
  rw [← h]; exact pr_opow ε

theorem InE.isSuccLimit {ε : Ordinal.{0}} (h : InE ε) : Order.IsSuccLimit ε := by
  rw [← h]
  exact isSuccLimit_opow_left isSuccLimit_omega0 (by
    intro h0; have := h.one_lt; rw [h0] at this; exact absurd this (not_lt.mpr zero_le_one))

/-- An epsilon number at most `ω^y` is at most `y`. -/
theorem le_of_le_opow {ε y : Ordinal.{0}} (hε : InE ε) (h : ε ≤ ω ^ y) : ε ≤ y := by
  rw [← hε] at h
  exact (opow_le_opow_iff_right one_lt_omega0).mp h

theorem le_of_le_add_one {ε y : Ordinal.{0}} (hε : InE ε) (h : ε ≤ y + 1) : ε ≤ y := by
  rcases h.lt_or_eq with h | h
  · exact Order.lt_add_one_iff.mp h
  · exfalso
    have := hε.isSuccLimit
    rw [h, ← Order.succ_eq_add_one] at this
    exact Order.not_isSuccLimit_succ y this

/-- An epsilon number at most a sum of `T¹` is at most its first summand. -/
theorem le_head_of_eps {ε : Ordinal.{0}} (hε : InE ε) {p : WP} {x : List WP}
    (hx : NFS (p :: x)) (h : ε ≤ WP.valS (p :: x)) : ε ≤ p.val := by
  by_contra hlt
  push Not at hlt
  have : WP.valS (p :: x) < ε := by
    rw [valS_eq_sum_map]
    apply sum_lt_of_forall_lt hε.pr
    intro v hv
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hlt
    · exact lt_of_le_of_lt (hx.le_head r hr) hlt
  exact absurd h (not_le.mpr this)

theorem isEps_val {q : WP} (hq : NFP q) (_hq0 : q.lvl = 0) (he : isEpsLevel q 0 = true) :
    InE q.val := eps_fix hq he

theorem not_eps_of_val {q : WP} (hq : NFP q) (hq0 : q.lvl = 0) (he : InE q.val) :
    isEpsLevel q 0 = true := by
  obtain ⟨m, a⟩ := q
  simp only [WP.lvl_th] at hq0; subst hq0
  apply isEpsLevel_iff.mpr ⟨rfl, ?_⟩
  exact (eps_iff hq).mpr ⟨by rw [Om_zero]; exact he.one_lt, he⟩

/-- A non-epsilon principal term of level `0` has an argument below its value. -/
theorem argV_lt_val {r : WP} (hr : NFP r) (hr0 : r.lvl = 0) (he : isEpsLevel r 0 = false) :
    argV r < r.val := by
  obtain ⟨m, x⟩ := r
  simp only [WP.lvl_th] at hr0; subst hr0
  have hl := arg_lvl_le_of_not_eps hr he
  rw [argV_th]
  by_cases hA : isEpsPlusN x 0 = true
  · rw [val_exp_eps hr hA]
    exact lt_of_lt_of_le (Order.lt_add_one_iff.mpr le_rfl) (right_le_opow _ one_lt_omega0)
  · have hB : isEpsPlusN x 0 = false := by simpa using hA
    rw [val_exp hr hl hB]
    simp only [expBase, if_true, zero_add]
    refine lt_of_le_of_ne (right_le_opow _ one_lt_omega0) (fun e => ?_)
    -- `valS x` would be an epsilon number, so `x = [ε]`
    have hE : InE (WP.valS x) := e.symm
    have hx := hr.nfs
    have hul : x.map WP.val = [WP.valS x] :=
      anf_unique (anf_of_nfs hx) ⟨by simpa using hE.pr, List.pairwise_singleton _ _⟩
        (by rw [← valS_eq_sum_map]; simp)
    obtain ⟨q, rfl⟩ : ∃ q, x = [q] := by
      rcases x with _ | ⟨q, _ | ⟨q', x⟩⟩
      · simp at hul
      · exact ⟨q, rfl⟩
      · simp at hul
    have hq0 : q.lvl = 0 := by have := hl q (by simp); omega
    have hqe : isEpsLevel q 0 = true :=
      not_eps_of_val (hr.of_mem (by simp)) hq0 (by simpa using hE)
    exact hA (isEpsPlusN_cons.mpr ⟨hqe, by simp⟩)

theorem mem_starS_of {m : ℕ} {s y : WP} : ∀ {x : List WP}, y ∈ x → s ∈ starP m y → s ∈ starS m x
  | [], h, _ => by simp at h
  | z :: x, h, hs => by
    rw [starS_cons, List.mem_append]
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inl hs
    · exact Or.inr (mem_starS_of h hs)

theorem starP0_trans : ∀ (q : WP) {r s : WP}, r ∈ starP 0 q → s ∈ starP 0 r → s ∈ starP 0 q := by
  intro q
  induction q using WP.ind with
  | h k a ih =>
    intro r s hr hs
    rw [starP_th] at hr ⊢
    by_cases hk : k = 0
    · subst hk
      simp only [Nat.lt_irrefl, if_false, if_true] at hr ⊢
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [starP_th] at hs; simpa using hs
      · obtain ⟨y, hy, hry⟩ := mem_starS hr
        exact List.mem_cons_of_mem _ (mem_starS_of hy (ih y hy hry hs))
    · simp only [Nat.not_lt_zero, if_false, hk] at hr ⊢
      obtain ⟨y, hy, hry⟩ := mem_starS hr
      exact mem_starS_of hy (ih y hy hry hs)

theorem sub0_mono {q r : WP} (hr : r ∈ sub0 q) : ∀ s ∈ sub0 r, s ∈ sub0 q :=
  fun _ hs => starP0_trans q hr hs

/-- **The largest epsilon subterm**: an epsilon number `ε ≤ q` lies below an epsilon
`ϑ_0`-subterm of `q`. -/
theorem exists_eps_sub : ∀ (q : WP), NFP q → q.lvl = 0 → ∀ {ε : Ordinal.{0}}, InE ε → ε ≤ q.val →
    ∃ r ∈ sub0 q, isEpsLevel r 0 = true ∧ ε ≤ r.val := by
  intro q
  induction q using WP.ind with
  | h m a ih =>
    intro hq hq0 ε hε hεq
    simp only [WP.lvl_th] at hq0; subst hq0
    by_cases he : isEpsLevel (.th 0 a) 0 = true
    · exact ⟨_, self_mem_sub0, he, hεq⟩
    · have he' : isEpsLevel (.th 0 a) 0 = false := by simpa using he
      have hl := arg_lvl_le_of_not_eps hq he'
      have hεa : ε ≤ WP.valS a := by
        by_cases hA : isEpsPlusN a 0 = true
        · rw [val_exp_eps hq hA] at hεq
          exact le_of_le_add_one hε (le_of_le_opow hε hεq)
        · rw [val_exp hq hl (by simpa using hA)] at hεq
          simpa [expBase] using le_of_le_opow hε hεq
      rcases a with _ | ⟨p, x⟩
      · simp at hεa; exact absurd hεa (ne_of_gt (lt_trans zero_lt_one hε.one_lt))
      · have hpε := le_head_of_eps hε hq.nfs hεa
        have hp : NFP p := hq.of_mem (by simp)
        have hp0 : p.lvl = 0 := by have := hl p (by simp); omega
        obtain ⟨r, hr, hre, hεr⟩ := ih p (by simp) hp hp0 hε hpε
        refine ⟨r, ?_, hre, hεr⟩
        rw [sub0_th]
        exact List.mem_cons_of_mem _ (mem_starS_of (List.mem_cons_self) hr)

/-- The subterms of `ϑ_0(q)` are `ϑ_0(q)` and the subterms of `q`. -/
theorem sub0_th_single (q : WP) : sub0 (.th 0 [q]) = .th 0 [q] :: sub0 q := by
  rw [sub0_th, starS_cons, starS_nil, List.append_nil]; rfl

/-- **Fact BAR₁.** -/
theorem factBar1 {ζ : Ordinal.{0}} (hζ : Pr ζ) (hne : ¬ InE ζ) (hT : ω ^ ζ < T1bound) :
    (barO (ω ^ ζ) = 1 ∧ ∀ ε, InE ε → ¬ ε ≤ ζ) ∨
      (InE (barO (ω ^ ζ)) ∧ barO (ω ^ ζ) ≤ ζ ∧ ∀ ε, InE ε → ε ≤ ζ → ε ≤ barO (ω ^ ζ)) := by
  have hζT : ζ < T1bound := lt_of_le_of_lt (right_le_opow _ one_lt_omega0) hT
  obtain ⟨u, hu, hus, hu0⟩ := exists_nfs_of_lt_T1bound hζT
  have hul : u.map WP.val = [ζ] :=
    anf_unique (anf_of_nfs hu) ⟨by simpa using hζ, List.pairwise_singleton _ _⟩
      (by rw [← valS_eq_sum_map, hus]; simp)
  obtain ⟨q, rfl⟩ : ∃ q, u = [q] := by
    rcases u with _ | ⟨q, _ | ⟨q', u⟩⟩
    · simp at hul
    · exact ⟨q, rfl⟩
    · simp at hul
  have hqv : q.val = ζ := by simpa using hul
  have hq : NFP q := hu.1 q (by simp)
  have hq0 : q.lvl = 0 := hu0 q (by simp)
  have hqe : isEpsLevel q 0 = false := by
    by_contra h
    exact hne (hqv ▸ isEps_val hq hq0 (by simpa using h))
  have hpn : NFP (.th 0 [q]) := nfp_th (NFS.single hq) (fun r hr => by
    rw [List.mem_singleton.mp hr, hq0]; omega)
  have hB : isEpsPlusN [q] 0 = false := by simp [isEpsPlusN, hqe]
  have hpv : (WP.th 0 [q]).val = ω ^ ζ := by
    rw [val_exp hpn (fun r hr => by rw [List.mem_singleton.mp hr, hq0]) hB, valS_single, hqv]
    simp [expBase]
  rw [← hpv, barO_eq hpn rfl]
  have hE : argE (WP.th 0 [q]).arg = [q] := argE_of_lvl0 (fun r hr => by
    rw [List.mem_singleton.mp hr, hq0])
  have hD : argD (WP.th 0 [q]).arg = [] := argD_of_lvl0 (fun r hr => by
    rw [List.mem_singleton.mp hr, hq0])
  have hget : (argE (WP.th 0 [q]).arg).getLast? = some q := by rw [hE]; rfl
  by_cases h1 : q = TR.one
  · -- `ζ = 1`
    left
    rw [barT_pos hget (Or.inl h1), hD, hE]
    simp only [List.dropLast_singleton, List.nil_append]
    refine ⟨by rw [← val_one]; rfl, fun ε hε hεζ => ?_⟩
    rw [← hqv, h1, val_one] at hεζ
    exact absurd hεζ (not_le.mpr hε.one_lt)
  · rw [barT_neg hget (by rw [hE, hD]; simp [h1])]
    have hpgt : ∀ r ∈ sub0 q, r.val ≤ q.val := fun r hr => val_le_of_mem_starP0 hq hq0 hr
    have hargp : argV (.th 0 [q]) = q.val := by rw [argV_th, valS_single]
    -- a suffix maximum below `ϑ_0(q)` is an epsilon subterm of `q`
    have hsuf_eps : ∀ r, SufMax (.th 0 [q]) r → r.val < (WP.th 0 [q]).val →
        r ∈ sub0 q ∧ isEpsLevel r 0 = true := by
      intro r hr hrp
      have hr1 := hr.1
      rw [sub0_th_single] at hr1
      have hrmem : r ∈ sub0 q := by
        rcases List.mem_cons.mp hr1 with rfl | h
        · exact absurd hrp (lt_irrefl _)
        · exact h
      refine ⟨hrmem, ?_⟩
      by_contra hre
      have hre' : isEpsLevel r 0 = false := by simpa using hre
      obtain ⟨hrn, hr0⟩ := sub0_spec hq hrmem
      have h1' := hr.2.2 (.th 0 [q]) (by rw [sub0_th_single]; simp) hrp
      rw [hargp] at h1'
      have h2' := argV_lt_val hrn hr0 hre'
      exact absurd (lt_trans h1' h2') (not_lt.mpr (hpgt r hrmem))
    set Es := (sub0 q).filter (fun r => isEpsLevel r 0) with hEs
    rcases hEsn : Es with _ | ⟨e0, Es'⟩
    · -- no epsilon subterm: the bar is `1`
      left
      have hnone : ∀ r ∈ sub0 q, isEpsLevel r 0 = false := by
        intro r hr
        by_contra h
        have : r ∈ Es := List.mem_filter.mpr ⟨hr, by simpa using h⟩
        rw [hEsn] at this; simp at this
      refine ⟨?_, fun ε hε hεζ => ?_⟩
      · have hp1 : 1 < (WP.th 0 [q]).val := by
          rw [hpv]
          exact lt_of_lt_of_le one_lt_omega0 (by
            simpa using opow_le_opow_right omega0_pos (Order.one_le_iff_pos.mpr hζ.pos))
        rw [locPred_eq_one hpn rfl hp1 (fun q' hq' => ?_)]
        · rw [val_one]
        · by_contra hlt
          push Not at hlt
          obtain ⟨hm, he⟩ := hsuf_eps q' hq' hlt
          rw [hnone q' hm] at he; exact Bool.noConfusion he
      · obtain ⟨r, hr, hre, -⟩ := exists_eps_sub q hq hq0 hε (hqv ▸ hεζ)
        rw [hnone r hr] at hre; exact Bool.noConfusion hre
    · -- the largest epsilon subterm
      right
      have hEsne : Es ≠ [] := by rw [hEsn]; simp
      obtain ⟨e, he⟩ : ∃ e, e ∈ Es.argmax (fun r => r.val) := by
        cases h : Es.argmax (fun r => r.val) with
        | none => exact absurd (List.argmax_eq_none.mp h) hEsne
        | some e => exact ⟨e, rfl⟩
      have heEs := List.argmax_mem he
      have hemax : ∀ r ∈ Es, r.val ≤ e.val := fun r hr => List.le_of_mem_argmax hr he
      have hemem : e ∈ sub0 q := (List.mem_filter.mp heEs).1
      have hee : isEpsLevel e 0 = true := by simpa using (List.mem_filter.mp heEs).2
      obtain ⟨hen, he0⟩ := sub0_spec hq hemem
      have hqΩ : q.val < Om 1 := val_lt_Om_of_lvl_lt hq (by rw [hq0]; omega)
      have hΩe : Om 1 ≤ argV e := Om_le_argV_of_eps hen hee
      have hζlt : ζ < ω ^ ζ := lt_of_le_of_ne (right_le_opow _ one_lt_omega0) (fun e' => hne e'.symm)
      have hep : e.val < (WP.th 0 [q]).val := by
        rw [hpv]; exact lt_of_le_of_lt (hqv ▸ hpgt e hemem) hζlt
      have hsuf : SufMax (.th 0 [q]) e := by
        refine ⟨by rw [sub0_th_single]; exact List.mem_cons_of_mem _ hemem,
          eps_one_lt hen hee, fun r hr her => ?_⟩
        rw [sub0_th_single] at hr
        rcases List.mem_cons.mp hr with rfl | hr
        · rw [hargp]; exact lt_of_lt_of_le hqΩ hΩe
        · by_cases hre : isEpsLevel r 0 = true
          · exact absurd (hemax r (List.mem_filter.mpr ⟨hr, by simpa using hre⟩))
              (not_le.mpr her)
          · obtain ⟨hrn, hr0⟩ := sub0_spec hq hr
            have := argV_lt_val hrn hr0 (by simpa using hre)
            exact lt_of_lt_of_le (lt_of_lt_of_le this (hpgt r hr)) (le_trans hqΩ.le hΩe)
      rw [locPred_eq hpn rfl hsuf hep (fun q' hq' hq'p => by
        obtain ⟨hm, hq'e⟩ := hsuf_eps q' hq' hq'p
        exact hemax q' (List.mem_filter.mpr ⟨hm, by simpa using hq'e⟩))]
      refine ⟨isEps_val hen he0 hee, hqv ▸ hpgt e hemem, fun ε hε hεζ => ?_⟩
      obtain ⟨r, hr, hre, hεr⟩ := exists_eps_sub q hq hq0 hε (hqv ▸ hεζ)
      exact le_trans hεr (hemax r (List.mem_filter.mpr ⟨hr, by simpa using hre⟩))

end Googology.Trans.PSS.Main

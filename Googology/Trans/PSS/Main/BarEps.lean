import Googology.Trans.PSS.Main.EpsRoots

/-!
# `Bar_T`: bar at epsilon roots (`proof/PROOF-3.md` §13.3, §14.2)

**`Bar_T`** (`barEps`): for a standard epsilon root `N = (0, H_1 … H_k)`,
`bar(o(N)) = o(anchor N)` if `k ≥ 2`, and `bar(o(N)) = 1` if `k = 1`.

By Lemma TR, `o(N)` is the value of `𝒯(N) = ϑ_0(Δ + η')` (`TR/Eps.lean`), and
[CW12] Def 5.1 is read on this term.  Let `W = H_k`, `j` the start of the last run
and `e_p = 𝒯((0, H_1 … H_j))`.

* **NS** (`lemmaNS`, §13.1): if `η'` is a sup-point, then `ω^{ρ_W} = 1`.  An epsilon
  sup-point `η' = ε` comes from a `y = 0` child `E` of `W` with `𝒯(E) = ε`
  (`rho_mem`); by KEY, `E ≤ (0, H_1 … H_j)`, so `ε ≤ e_p`, which contradicts the
  shape of `η'`.
* **(a)** `W` shares its run with `H_{k-1}`: `η' = η'_a + ω^{ρ_W}` without absorption,
  where `η'_a` is the `η'` of the anchor `a`; Def 5.1 takes its first case (by NS for
  `a`), so `ᾱ = ϑ_0(Δ + η'_a) = 𝒯(a)`.
* **(b)** `W` alone in its run, `k ≥ 2`: Def 5.1 takes `α_{n-1}`.  All suffix maxima
  below `α` are at most `e_p` (KEY and EL); `α < e_p^+` (KEY again), so `e_p` is a
  subterm of `α` ([W07a] Lemma 6.4 (a), `mem_sub0_of_between`) and a suffix maximum.
  So `ᾱ = e_p = 𝒯(anchor N)`.
* **(c)** `k = 1`: there is no suffix maximum below `α`, so `ᾱ = τ = 1`.

The paper's proof uses LOC′, LOC″ with the structure lemmas CL, FD, LV and Lemma N⁺;
here KEY, EL and Lemma 6.4 (a) on `T¹` replace them.
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Order Phi Forest

/-! ## `ρ` of a level-1 term comes from its `y = 0` children -/

theorem rho_mem {W : Tm} (hW1 : W.y = 1) {q : WP} (hq : q ∈ rhoOf 0 W) :
    ∃ E ∈ W.cs, E.y = 0 ∧ trTm E = q := by
  obtain ⟨hsplit, -, -, -, hρl⟩ := monOf_spec 0 W
  have hq0 : q.lvl = 0 := by have := hρl q hq; omega
  have hqx : q ∈ logOmega (trTm W) := by rw [hsplit]; exact List.mem_append_right _ hq
  obtain ⟨hxn, hxv, -⟩ := logOmega_spec (trTm_nfp W)
  obtain ⟨y, ch⟩ := W
  simp only [Tm.y_node] at hW1; subst hW1
  by_cases hch : ch = []
  · subst hch
    exfalso
    have hv1 : (trTm (Tm.node 1 [])).val = ω ^ Om 1 := by
      rw [trTm_leaf, WP.val_th, WP.valS_nil, vartheta_zero, opow_Om_succ 0]
    have : WP.valS (logOmega (trTm (Tm.node 1 []))) = WP.valS [TR.om 1] := by
      rw [valS_single, val_om]; exact opow_inj (hxv.trans hv1)
    have e := eq_of_valS_eq hxn (NFS.single (nfp_th_nil 1)) this
    rw [e, List.mem_singleton] at hqx
    rw [hqx] at hq0; simp at hq0
  · by_cases hl : (ch.getLast hch).y = 1 + 1
    · exfalso
      have hfix := (trTm_eps_isEps hch hl).2
      have : WP.valS (logOmega (trTm (Tm.node 1 ch))) = WP.valS [trTm (Tm.node 1 ch)] := by
        rw [valS_single]; exact opow_inj (hxv.trans hfix.symm)
      have e := eq_of_valS_eq hxn (NFS.single (trTm_nfp _)) this
      rw [e, List.mem_singleton] at hqx
      rw [hqx, trTm_lvl] at hq0; simp at hq0
    · have hv := val_trTm_noneps hch hl
      obtain ⟨hzn, -, -⟩ := zOf_spec 1 ch
      have e := eq_of_valS_eq hxn hzn (opow_inj (hxv.trans hv))
      rw [e] at hqx
      obtain ⟨x, hx, hqx'⟩ := mem_addAll hqx
      rcases List.mem_append.mp hx with hx | hx
      · have := ((headPart_spec 1 ch).1 x hx).2 q hqx'
        omega
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
        rw [List.mem_singleton] at hqx'
        subst hqx'
        refine ⟨c, (List.mem_filter.mp hc).1, ?_, rfl⟩
        rw [trTm_lvl] at hq0; exact hq0

/-! ## NS -/

theorem addAll_getLast_single (xs : List (List WP)) (w : WP) :
    (TR.addAll (xs ++ [[w]])).getLast? = some w := by
  rw [addAll_append_single]
  simp [addS]

theorem cOf_getLast {H : List Tm} (hne : H ≠ []) :
    (cOf 0 H).getLast? = some (wOf 0 (H.getLast hne)) := by
  have hj : jOf 0 H < H.length := by
    have := runStart_lt (ds := H.map (dOf 0)) (by simpa using hne); simpa using this
  have hd : H.drop (jOf 0 H) = (H.drop (jOf 0 H)).dropLast ++ [H.getLast hne] := by
    have hdne : H.drop (jOf 0 H) ≠ [] := by simp; omega
    rw [← List.getLast_drop hdne, List.dropLast_append_getLast]
  unfold cOf
  rw [hd, List.map_append, List.map_singleton]
  exact addAll_getLast_single _ _

theorem eq_one_of_minusOnePlus_nil {c : List WP} (hc : c ≠ []) (h : minusOnePlus c = []) :
    c = [TR.one] := by
  obtain ⟨p, r, rfl⟩ := List.exists_cons_of_ne_nil hc
  by_cases hp : p = TR.one
  · simp only [minusOnePlus, hp, if_true] at h; rw [hp, h]
  · simp [minusOnePlus, hp] at h

theorem eq_single_of_minusOnePlus {c : List WP} (hc : NFS c) {e : WP} (he : 1 < e.val)
    (h : minusOnePlus c = [e]) : c = [e] := by
  rcases c with _ | ⟨p, r⟩
  · simp [minusOnePlus] at h
  · by_cases hp : p = TR.one
    · -- `c = [1, e]` is not non-increasing
      simp only [minusOnePlus, hp, if_true] at h
      subst h; subst hp
      exfalso
      have := hc.le_head e (by simp)
      rw [val_one] at this
      exact absurd he (not_lt.mpr this)
    · simpa [minusOnePlus, hp] using h

theorem isEps_of_argD {e : WP} (he0 : e.lvl = 0) (h : WP.valS [] < WP.valS (argD e.arg)) :
    isEpsLevel e 0 = true := by
  obtain ⟨m, a⟩ := e
  simp only [WP.lvl_th] at he0; subst he0
  cases a with
  | nil => simp [argD] at h
  | cons q a =>
    refine isEpsLevel_iff.mpr ⟨rfl, q, rfl, ?_⟩
    by_contra hq
    have : argD (q :: a) = [] := by simp [argD]; omega
    simp only [WP.arg_th] at h
    rw [this] at h; exact lt_irrefl _ h

theorem std_grandchild {H : List Tm} (hN : Std (.node 0 H)) {W E : Tm} (hW : W ∈ H)
    (hE : E ∈ W.cs) (hE0 : E.y = 0) : Std E := by
  have h1 := tgood_child hN hW
  obtain ⟨y, cs⟩ := W
  rw [tgood_iff] at h1
  exact std_of_tgood_y0 (h1.2.2.2 E hE) hE0

theorem grandchild_lt {H : List Tm} (hN : Std (.node 0 H)) {W E : Tm} (hW : W ∈ H) (hW1 : W.y = 1)
    (hE : E ∈ W.cs) (hE0 : E.y = 0) : E < .node 0 H := by
  have hv := valid_of_std hN
  obtain ⟨y, cs⟩ := W
  simp only [Tm.y_node] at hW1; subst hW1
  exact (hv.reach_lt (Reach.deep hW (by simp) (Reach.child hE hE0))).1

/-- **NS** (`proof/PROOF-3.md` §13.1): if `η'` is a sup-point, then `ω^{ρ_W} = 1`. -/
theorem lemmaNS {H : List Tm} (hN : Std (.node 0 H)) (he : isEps (.node 0 H) = true)
    (hne : H ≠ []) (hsup : supPt (deltaOf 0 H) (eta'Of 0 H)) : wOf 0 (H.getLast hne) = TR.one := by
  obtain ⟨e, hη', he0, hlev, hstar⟩ := hsup
  obtain ⟨-, hH1, hTN⟩ := trTm_root_eps hN he
  set W := H.getLast hne with hW
  have hWmem : W ∈ H := List.getLast_mem hne
  have hcne : cOf 0 H ≠ [] := cOf_ne_nil hne
  have hcn : NFS (cOf 0 H) := (cOf_spec 0 H).1
  have hclast := cOf_getLast hne
  have hen : NFP e := (eta'Of_spec 0 H).1.1 e (by rw [hη']; simp)
  have hee : isEpsLevel e 0 = true :=
    isEps_of_argD he0 (lt_of_le_of_lt (by simp) hlev)
  have he1 : 1 < e.val := eps_one_lt hen hee
  -- the shapes of `η'`
  have hcase : wOf 0 W = TR.one ∨
      (etaOf 0 H = [e] ∧ (insOf 0 H → (epOf 0 H).val < e.val)) := by
    by_cases hins : insOf 0 H
    · have hη'd : eta'Of 0 H = addS [epOf 0 H] (etaOf 0 H) := by unfold eta'Of; rw [if_pos hins]
      rcases hη : etaOf 0 H with _ | ⟨y0, ys⟩
      · left
        have := eq_one_of_minusOnePlus_nil hcne hη
        rw [this] at hclast
        simpa using hclast.symm
      · right
        rw [hη'd, hη] at hη'
        simp only [addS, List.reverse_singleton] at hη'
        by_cases hlt : cmpP (epOf 0 H) y0 = .lt
        · rw [List.dropWhile_cons_of_pos (by simpa using hlt)] at hη'
          simp only [List.dropWhile_nil, List.reverse_nil, List.nil_append,
            List.cons.injEq] at hη'
          obtain ⟨rfl, rfl⟩ := hη'
          refine ⟨rfl, fun _ => ?_⟩
          have hy0 : NFP y0 := (etaOf_spec 0 H).1.1 y0 (by rw [hη]; simp)
          exact (cmpP_lt_iff (trTm_nfp _) hy0).mp hlt
        · rw [List.dropWhile_cons_of_neg (by simpa using hlt)] at hη'
          simp at hη'
    · right
      have : eta'Of 0 H = etaOf 0 H := by unfold eta'Of; rw [if_neg hins]
      rw [← this, hη']
      exact ⟨rfl, fun h => absurd h hins⟩
  rcases hcase with h | ⟨hη, hepe⟩
  · exact h
  exfalso
  -- `c = [e]`, so `ω^{ρ_W} = e`
  have hc : cOf 0 H = [e] := eq_single_of_minusOnePlus hcn he1 hη
  rw [hc] at hclast
  have hwe : wOf 0 W = e := by simpa using hclast.symm
  have hρv : WP.valS (rhoOf 0 W) = e.val := by
    have h1 := (wOf_spec 0 W).2.2.2
    rw [hwe] at h1
    exact opow_inj (h1.symm.trans (eps_fix hen hee).symm)
  have hρ : rhoOf 0 W = [e] :=
    eq_of_valS_eq (monOf_spec 0 W).2.2.1 (NFS.single hen) (by rw [hρv, valS_single])
  obtain ⟨E, hEW, hE0, hTE⟩ := rho_mem (hH1 W hWmem) (q := e) (by rw [hρ]; simp)
  have hEs : Std E := std_grandchild hN hWmem hEW hE0
  have hEN : E < .node 0 H := grandchild_lt hN hWmem (hH1 W hWmem) hEW hE0
  have hEv : ordOf [E] = e.val := by rw [← val_trTm_root hEs, hTE]
  have hEe : isEps E = true := isEps_of_InE hEs (by rw [hEv]; exact eps_fix hen hee)
  -- KEY
  have hEeq := std_node_y hEs
  have hΔE : argD e.arg = deltaOf 0 E.cs := by
    have hEs' : Std (.node 0 E.cs) := by rw [← hEeq]; exact hEs
    have hEe' : isEps (.node 0 E.cs) = true := by rw [← hEeq]; exact hEe
    obtain ⟨hne', hall', hT⟩ := trTm_root_eps hEs' hEe'
    rw [← hTE, hEeq, hT, WP.arg_th]
    exact (argD_eps hne' (by rw [hall' _ (List.getLast_mem hne')])).1
  rcases key_eps_root hN he hEs hEe hEN with hk | hk
  · rw [← hΔE] at hk; exact absurd hlev (not_lt.mpr hk)
  · -- `E ≤ (0, H_1 … H_j)`
    have hj : 0 < jOf 0 H := by
      by_contra h0
      push Not at h0
      have : jOf 0 H = 0 := by omega
      rw [this, List.take_zero] at hk
      have hEcs : E.cs ≠ [] := by
        intro h; rw [hEeq, h] at hEe; simp [isEps] at hEe
      have := one_lt_ordOf_of_cs hEs hEcs
      rw [← ordOf_leaf'] at this
      exact absurd (ordOf_single_le hEs std_leaf hk) (not_le.mpr this)
    have hNs' : Std (.node 0 (H.take (jOf 0 H))) := std_take hN _
    have hle : e.val ≤ (epOf 0 H).val := by
      rw [← hEv, epOf, val_trTm_root hNs']
      exact ordOf_single_le hEs hNs' hk
    by_cases hins : insOf 0 H
    · exact absurd (hepe hins) (not_lt.mpr hle)
    · unfold insOf at hins
      push Not at hins
      obtain ⟨q, hq, hqe⟩ := hins hj
      exact absurd (hstar q hq) (not_lt.mpr (le_trans hle hqe))

/-! ## The run break and roots of epsilon subterms -/

theorem runStart_break {ds : List (List WP)} (hne : ds ≠ []) (hj : 0 < runStart ds) :
    ∃ h : runStart ds - 1 < ds.length, ds[runStart ds - 1] ≠ ds.getLast hne := by
  obtain ⟨l, d, hds⟩ : ∃ l d, ds = l ++ [d] :=
    ⟨ds.dropLast, ds.getLast hne, (List.dropLast_append_getLast hne).symm⟩
  subst hds
  have hjeq : runStart (l ++ [d]) = (l.rdropWhile (fun e => e == d)).length := by
    rw [runStart_eq, List.rdropWhile.eq_1, List.length_reverse]
  set R := l.rdropWhile (fun e => e == d) with hR
  have hRne : R ≠ [] := by intro h; rw [hjeq, h] at hj; simp at hj
  have hpre := List.rdropWhile_prefix (fun e => e == d) l
  have hRl : R.length ≤ l.length := hpre.length_le
  have hlast := List.rdropWhile_last_not (fun e => e == d) l hRne
  have hlt : runStart (l ++ [d]) - 1 < l.length := by rw [hjeq]; omega
  refine ⟨by simp; omega, ?_⟩
  rw [List.getLast_append_of_ne_nil _ (by simp), List.getLast_singleton,
    List.getElem_append_left hlt]
  have hRi : runStart (l ++ [d]) - 1 < R.length := by rw [hjeq]; have := List.length_pos_of_ne_nil hRne; omega
  have e1 : R.getLast hRne = R[runStart (l ++ [d]) - 1] := by
    rw [List.getLast_eq_getElem]; congr 1; rw [hjeq]
  have e2 : R[runStart (l ++ [d]) - 1] = l[runStart (l ++ [d]) - 1] := List.IsPrefix.getElem hpre hRi
  intro heq
  apply hlast
  rw [show (List.rdropWhile (fun e => e == d) l).getLast hRne = R.getLast hRne from rfl, e1, e2, heq]
  simp

/-- The prefix `(0, H_1 … H_j)` before the last run has a level above `Δ`. -/
theorem level_prefix_gt {H : List Tm} (hN : Std (.node 0 H)) (hne : H ≠ []) (hj : 0 < jOf 0 H) :
    WP.valS (deltaOf 0 H) < WP.valS (deltaOf 0 (H.take (jOf 0 H))) := by
  have hds : H.map (dOf 0) ≠ [] := by simpa using hne
  obtain ⟨hlt, hbreak⟩ := runStart_break hds hj
  have hlt' : jOf 0 H - 1 < H.length := by simpa using hlt
  have hbreak' : dOf 0 H[jOf 0 H - 1] ≠ dOf 0 (H.getLast hne) := by
    have := hbreak
    simp only [List.getElem_map, List.getLast_map] at this
    exact this
  have htake : H.take (jOf 0 H) ≠ [] := by
    intro h; rcases List.take_eq_nil_iff.mp h with h | h
    · omega
    · exact hne h
  have hd1 : deltaOf 0 (H.take (jOf 0 H)) = dOf 0 H[jOf 0 H - 1] := by
    rw [deltaOf_eq_last htake, List.getLast_take]
    simp [List.getElem?_eq_getElem hlt']
  have hΔ : deltaOf 0 H = dOf 0 (H.getLast hne) := deltaOf_eq_last hne
  -- `H_j ≥ W`
  have hge : H.getLast hne ≤ H[jOf 0 H - 1] := by
    have hd := (valid_of_std hN).desc
    have hjk : jOf 0 H < H.length := by
      have := runStart_lt (ds := H.map (dOf 0)) (by simpa using hne); simpa using this
    rw [List.getLast_eq_getElem]
    exact List.pairwise_iff_getElem.mp hd _ _ hlt' (by omega) (by omega)
  have hv := valid_of_std hN
  have hle := d_rho_mono (k := 0) (mono_le (hv.child (List.getLast_mem hne))
    (hv.child (List.getElem_mem hlt')) hge)
  rw [hd1, hΔ]
  refine lt_of_le_of_ne hle.1 (fun e => hbreak' ?_)
  exact (eq_of_valS_eq (monOf_spec 0 _).2.1 (monOf_spec 0 _).2.1 e).symm

/-- An epsilon `ϑ_0`-subterm below `o(N)` is `𝒯(z)` for an epsilon root `z ≤ N`, whose level
is `Δ(z)`. -/
theorem root_of_eps_term {r : WP} (hr : NFP r) (hre : isEpsLevel r 0 = true)
    {N : Tm} (hN : Std N) (hle : r.val ≤ ordOf [N]) :
    ∃ z, Std z ∧ isEps z = true ∧ trTm z = r ∧ z ≤ N ∧ argD r.arg = deltaOf 0 z.cs := by
  obtain ⟨z, hz, hTz, hzN⟩ := exists_root hr hN hle
  have hzv : ordOf [z] = r.val := by rw [← val_trTm_root hz, hTz]
  have hze : isEps z = true := isEps_of_InE hz (by rw [hzv]; exact eps_fix hr hre)
  refine ⟨z, hz, hze, hTz, hzN, ?_⟩
  have hzeq := std_node_y hz
  have hzs' : Std (.node 0 z.cs) := by rw [← hzeq]; exact hz
  have hze' : isEps (.node 0 z.cs) = true := by rw [← hzeq]; exact hze
  obtain ⟨hne', hall', hT⟩ := trTm_root_eps hzs' hze'
  rw [← hTz, hzeq, hT, WP.arg_th]
  exact (argD_eps hne' (by rw [hall' _ (List.getLast_mem hne')])).1

/-! ## The cases -/

theorem argD_append_one : ∀ x : List WP, argD (x ++ [TR.one]) = argD x
  | [] => by simp [argD, TR.one]
  | q :: x => by
    unfold argD
    rw [List.cons_append, List.takeWhile_cons, List.takeWhile_cons]
    split_ifs
    · congr 1; exact argD_append_one x
    · rfl

section Cases

variable {H : List Tm} (hN : Std (.node 0 H)) (he : isEps (.node 0 H) = true)
include hN he

theorem trTm_eps_val : (WP.th 0 (deltaOf 0 H ++ eta'Of 0 H)).val = ordOf [.node 0 H] := by
  rw [← (trTm_root_eps hN he).2.2, val_trTm_root hN]

theorem nfp_eps : NFP (WP.th 0 (deltaOf 0 H ++ eta'Of 0 H)) := by
  rw [← (trTm_root_eps hN he).2.2]; exact trTm_nfp _

theorem argDE_eps : argD (deltaOf 0 H ++ eta'Of 0 H) = deltaOf 0 H ∧
    argE (deltaOf 0 H ++ eta'Of 0 H) = eta'Of 0 H := by
  obtain ⟨hne, hall, -⟩ := trTm_root_eps hN he
  exact argD_eps hne (by rw [hall _ (List.getLast_mem hne)])

/-- Every suffix maximum below `𝒯(N)` is at most `o((0, H_1 … H_j))`, and `j > 0`. -/
theorem sufMax_bound {r : WP} (hr : SufMax (.th 0 (deltaOf 0 H ++ eta'Of 0 H)) r)
    (hrα : r.val < (WP.th 0 (deltaOf 0 H ++ eta'Of 0 H)).val) :
    0 < jOf 0 H ∧ r.val ≤ ordOf [.node 0 (H.take (jOf 0 H))] := by
  have hαn := nfp_eps hN he
  obtain ⟨hD, hE⟩ := argDE_eps hN he
  have hlev := level_gt_of_sufMax hαn hD hE hr hrα
  obtain ⟨hrn, hr0⟩ := sub0_spec hαn hr.1
  have hre := isEps_of_argD hr0 (lt_of_le_of_lt (by simp) hlev)
  have hle : r.val ≤ ordOf [.node 0 H] := by rw [← trTm_eps_val hN he]; exact hrα.le
  obtain ⟨z, hz, hze, hTz, hzN, hΔz⟩ := root_of_eps_term hrn hre hN hle
  have hzv : ordOf [z] = r.val := by rw [← val_trTm_root hz, hTz]
  have hzN' : z < .node 0 H := lt_of_le_of_ne hzN (fun e => by
    rw [e] at hzv
    have h1 := trTm_eps_val hN he
    rw [h1, hzv] at hrα; exact lt_irrefl _ hrα)
  rcases key_eps_root hN he hz hze hzN' with hk | hk
  · rw [← hΔz] at hk; exact absurd hlev (not_lt.mpr hk)
  · have hzcs : z.cs ≠ [] := by
      intro h; rw [std_node_y hz, h] at hze; simp [isEps] at hze
    refine ⟨?_, ?_⟩
    · by_contra h0
      push Not at h0
      have : jOf 0 H = 0 := by omega
      rw [this, List.take_zero] at hk
      have := one_lt_ordOf_of_cs hz hzcs
      rw [← ordOf_leaf'] at this
      exact absurd (ordOf_single_le hz std_leaf hk) (not_le.mpr this)
    · rw [← hzv]; exact ordOf_single_le hz (std_take hN _) hk

omit hN he in
theorem cOf_single (hj : jOf 0 H = H.length - 1) (hne : H ≠ []) :
    cOf 0 H = [wOf 0 (H.getLast hne)] := by
  have hd : H.drop (jOf 0 H) = [H.getLast hne] := by
    rw [hj, List.drop_length_sub_one hne]
  unfold cOf
  rw [hd]
  simp [TR.addAll, addS]

/-- **Def 5.1 takes its second case** when `W` is alone in its run. -/
theorem def51_second (hj : jOf 0 H = H.length - 1) :
    barT (.th 0 (deltaOf 0 H ++ eta'Of 0 H)) = locPred (.th 0 (deltaOf 0 H ++ eta'Of 0 H)) := by
  obtain ⟨hne, hall, -⟩ := trTm_root_eps hN he
  obtain ⟨hD, hE⟩ := argDE_eps hN he
  have hc := cOf_single hj hne
  have hwn : NFP (wOf 0 (H.getLast hne)) := (wOf_spec 0 _).1
  generalize wOf 0 (H.getLast hne) = w at hc hwn
  set ep := epOf 0 H with hep
  -- `e_p > 1` when inserted
  have hep1 : insOf 0 H → ep ≠ TR.one := by
    intro hins e
    have hjpos := hins.1
    have hcs : (H.take (jOf 0 H)) ≠ [] := by
      intro h; rcases List.take_eq_nil_iff.mp h with h | h
      · omega
      · exact hne h
    have := one_lt_ordOf_of_cs (std_take hN (jOf 0 H)) hcs
    rw [← val_trTm_root (std_take hN _)] at this
    rw [show trTm (.node 0 (H.take (jOf 0 H))) = ep from rfl, e, val_one] at this
    exact lt_irrefl _ this
  -- `e_p` is a sup-point
  have hsup : insOf 0 H → supPt (deltaOf 0 H) [ep] := by
    intro hins
    have hjpos := hins.1
    have hps : Std (.node 0 (H.take (jOf 0 H))) := std_take hN _
    have hpe : isEps (.node 0 (H.take (jOf 0 H))) = true := by
      have hcs : (H.take (jOf 0 H)) ≠ [] := by
        intro h; rcases List.take_eq_nil_iff.mp h with h | h
        · omega
        · exact hne h
      simp only [isEps, List.getLast?_eq_some_getLast hcs, decide_eq_true_eq]
      rw [hall _ (List.mem_of_mem_take (List.getLast_mem hcs))]
    obtain ⟨hne', hall', hT'⟩ := trTm_root_eps hps hpe
    refine ⟨ep, rfl, epOf_lvl 0 H, ?_, hins.2⟩
    rw [hep, epOf, hT', WP.arg_th,
      (argD_eps hne' (by rw [hall' _ (List.getLast_mem hne')])).1]
    exact level_prefix_gt hN hne hjpos
  have hw1 : w = TR.one ∨ etaOf 0 H = [w] := by
    unfold etaOf; rw [hc]
    by_cases h : w = TR.one
    · left; exact h
    · right; simp [minusOnePlus, h]
  have hEta : eta'Of 0 H = [] ∨
      (∃ η0 η'', eta'Of 0 H = η'' ++ [η0] ∧ η0 ≠ TR.one ∧ (η'' = [] ∨ supPt (deltaOf 0 H) η'')) := by
    by_cases hins : insOf 0 H
    · have e1 : eta'Of 0 H = addS [ep] (etaOf 0 H) := by unfold eta'Of; rw [if_pos hins]
      right
      rcases hw1 with h1 | h1
      · have : etaOf 0 H = [] := by unfold etaOf; rw [hc, h1]; simp [minusOnePlus]
        rw [e1, this]
        exact ⟨ep, [], by simp [addS], hep1 hins, Or.inl rfl⟩
      · rw [e1, h1]
        have hwne : w ≠ TR.one := by
          intro h; rw [h] at h1; unfold etaOf at h1; rw [hc, h] at h1; simp [minusOnePlus] at h1
        by_cases hlt : cmpP ep w = .lt
        · exact ⟨w, [], by simp [addS, hlt], hwne, Or.inl rfl⟩
        · exact ⟨w, [ep], by simp [addS, hlt], hwne, Or.inr (hsup hins)⟩
    · have e1 : eta'Of 0 H = etaOf 0 H := by unfold eta'Of; rw [if_neg hins]
      rcases hw1 with h1 | h1
      · left; rw [e1]; unfold etaOf; rw [hc, h1]; simp [minusOnePlus]
      · right
        have hwne : w ≠ TR.one := by
          intro h; rw [h] at h1; unfold etaOf at h1; rw [hc, h] at h1; simp [minusOnePlus] at h1
        exact ⟨w, [], by rw [e1, h1]; rfl, hwne, Or.inl rfl⟩
  rcases hEta with h0 | ⟨η0, η'', hη, hη0, hη''⟩
  · exact barT_none (by simp only [WP.arg_th]; rw [hE, h0]; rfl)
  · refine barT_neg (η0 := η0) (by simp only [WP.arg_th]; rw [hE, hη]; simp) ?_
    simp only [WP.arg_th]
    rw [hE, hD, hη, List.dropLast_concat]
    push Not
    refine ⟨hη0, fun h => ?_⟩
    rcases hη'' with h' | h'
    · exact absurd h' h
    · exact h'

omit hN he in
theorem jOf_lt (hne : H ≠ []) : jOf 0 H < H.length := by
  have := runStart_lt (ds := H.map (dOf 0)) (by simpa using hne); simpa using this

theorem one_lt_eps_val : 1 < (WP.th 0 (deltaOf 0 H ++ eta'Of 0 H)).val := by
  rw [trTm_eps_val hN he]
  exact one_lt_ordOf_of_cs hN (trTm_root_eps hN he).1

/-- **Case (c)**: one child, `ᾱ = 1`. -/
theorem case_c (h1 : H.length = 1) : barT (.th 0 (deltaOf 0 H ++ eta'Of 0 H)) = TR.one := by
  have hne := (trTm_root_eps hN he).1
  have hj : jOf 0 H = H.length - 1 := by have := jOf_lt hne; omega
  rw [def51_second hN he hj]
  refine locPred_eq_one (nfp_eps hN he) rfl (one_lt_eps_val hN he) (fun q hq => ?_)
  by_contra hlt
  push Not at hlt
  have := (sufMax_bound hN he hq hlt).1
  omega

/-- **Case (b)**: `W` alone in its run, `k ≥ 2`: `ᾱ = e_p = 𝒯(anchor N)`. -/
theorem case_b (h2 : 2 ≤ H.length) (hj : jOf 0 H = H.length - 1) :
    barT (.th 0 (deltaOf 0 H ++ eta'Of 0 H)) = trTm (.node 0 H.dropLast) := by
  obtain ⟨hne, hall, -⟩ := trTm_root_eps hN he
  obtain ⟨hD, hE⟩ := argDE_eps hN he
  have hαn := nfp_eps hN he
  set α := WP.th 0 (deltaOf 0 H ++ eta'Of 0 H) with hα
  rw [def51_second hN he hj]
  have htake : H.take (jOf 0 H) = H.dropLast := by rw [hj, List.dropLast_eq_take]
  set a := Tm.node 0 H.dropLast with ha
  have has : Std a := by rw [ha, ← htake]; exact std_take hN _
  have hane : H.dropLast ≠ [] := by
    intro h; have := congrArg List.length h; simp at this; omega
  have hae : isEps a = true := by
    simp only [ha, isEps, List.getLast?_eq_some_getLast hane, decide_eq_true_eq]
    rw [hall _ (List.mem_of_mem_dropLast (List.getLast_mem hane))]
  obtain ⟨-, hall', hTa⟩ := trTm_root_eps has hae
  set ep := trTm a with hep
  have hepn : NFP ep := trTm_nfp a
  have hep0 : ep.lvl = 0 := by rw [hep, trTm_lvl]; rfl
  have hepv : ep.val = ordOf [a] := val_trTm_root has
  -- the level of `e_p`
  have hDa : argD ep.arg = deltaOf 0 H.dropLast := by
    rw [hTa, WP.arg_th]
    exact (argD_eps hane (by rw [hall' _ (List.getLast_mem hane)])).1
  have hlev : WP.valS (deltaOf 0 H) < WP.valS (deltaOf 0 H.dropLast) := by
    have := level_prefix_gt hN hne (by omega)
    rwa [htake] at this
  -- `a < N`
  have haN : a < Tm.node 0 H := by
    rw [ha]
    refine (Tm.lt_iff_cs_lt (s := Tm.node 0 H.dropLast) (t := Tm.node 0 H) rfl).mpr ?_
    conv_rhs => rw [← List.dropLast_append_getLast hne]
    exact lt_append_of_ne_nil _ (by simp)
  have hepα : ep.val < α.val := by
    rw [hepv, hα, trTm_eps_val hN he]; exact ordOf_single_lt has hN haN
  have hep1 : 1 < ep.val := by rw [hepv]; exact one_lt_ordOf_of_cs has hane
  -- `α < e_p^+`
  set epp := WP.th 0 (ep.arg ++ [TR.one]) with hepp
  have hppn : NFP epp := nfp_succ hepn hep0
  have hDpp : argD epp.arg = argD ep.arg := by
    simp only [hepp, WP.arg_th]
    exact argD_append_one _
  have hep_lt : ep.val < epp.val := by
    obtain ⟨m, A⟩ := ep
    simp only [WP.lvl_th] at hep0; subst hep0
    refine (val_lt_val_iff hepn hppn).mpr (Or.inl ⟨?_, fun s hs => ?_⟩)
    · rw [WP.arg_th, valS_append, valS_single, val_one]; exact Order.lt_add_one_iff.mpr le_rfl
    · exact star_lt_val hppn s (by rw [WP.arg_th, starS_append]; exact List.mem_append_left _ hs)
  have hαepp : α.val < epp.val := by
    by_contra hge
    push Not at hge
    rcases hge.lt_or_eq with hlt | heq
    · have hppe : isEpsLevel epp 0 = true := isEps_of_argD rfl (by
        rw [hDpp, hDa]; exact lt_of_le_of_lt (by simp) hlev)
      obtain ⟨z, hz, hze, hTz, hzN, hΔz⟩ := root_of_eps_term hppn hppe hN (by
        rw [← trTm_eps_val hN he]; exact hlt.le)
      have hzv : ordOf [z] = epp.val := by rw [← val_trTm_root hz, hTz]
      have hzN' : z < .node 0 H := lt_of_le_of_ne hzN (fun e => by
        rw [e, ← trTm_eps_val hN he] at hzv; rw [hzv] at hlt; exact lt_irrefl _ hlt)
      rcases key_eps_root hN he hz hze hzN' with hk | hk
      · rw [← hΔz, hDpp, hDa] at hk; exact absurd hlev (not_lt.mpr hk)
      · rw [htake] at hk
        have := ordOf_single_le hz has hk
        rw [hzv, ← hepv] at this
        exact absurd hep_lt (not_lt.mpr this)
    · have := eq_of_val_eq hppn hαn heq
      have e2 : argD epp.arg = argD α.arg := by rw [this]
      rw [hDpp, hDa, hα, WP.arg_th, hD] at e2
      rw [e2] at hlev; exact lt_irrefl _ hlev
  -- `e_p` is a suffix maximum
  have hepsub : ep ∈ sub0 α :=
    mem_sub0_of_between hepn hep0 _ α le_rfl hαn rfl hepα.le hαepp
  have hΩa : Om 1 ≤ WP.valS (deltaOf 0 H.dropLast) := by
    obtain ⟨-, h2', h3'⟩ := deltaOf_spec hane (by rw [hall' _ (List.getLast_mem hane)])
    obtain ⟨q, qs, hq⟩ := List.exists_cons_of_ne_nil h3'
    exact Om_le_valS_of_mem (deltaOf_spec hane (by rw [hall' _ (List.getLast_mem hane)])).1
      (p := q) (by rw [hq]; simp) (by rw [h2' q (by rw [hq]; simp)])
  have hargep : WP.valS (deltaOf 0 H.dropLast) ≤ argV ep := by
    rw [argV_split, hDa]; exact le_self_add
  have hsuf : SufMax α ep := by
    refine ⟨hepsub, hep1, fun r hr hepr => ?_⟩
    have hgap := gap_of_lt (m := 1) ((deltaOf_spec hane (by
        rw [hall' _ (List.getLast_mem hane)])).1) ((deltaOf_spec hne (by
        rw [hall _ (List.getLast_mem hne)])).1)
      (fun q hq => by rw [(deltaOf_spec hane (by rw [hall' _ (List.getLast_mem hane)])).2.1 q hq])
      (fun q hq => by rw [(deltaOf_spec hne (by rw [hall _ (List.getLast_mem hne)])).2.1 q hq])
      hlev
    by_cases hrα : r = α
    · -- `arg α = Δ + η' < Δ_a`
      rw [hrα, hα, argV_th, valS_append]
      refine lt_of_lt_of_le ?_ (le_trans hgap hargep)
      refine (add_lt_add_iff_left _).mpr ?_
      exact valS_lt_Om (eta'Of_spec 0 H).1 (m := 0) (eta'Of_spec 0 H).2
    · obtain ⟨hrn, hr0⟩ := sub0_spec hαn hr
      have hrα' : r.val < α.val := lt_of_le_of_ne (val_le_of_mem_sub0 hαn hr)
        (fun e => hrα (eq_of_val_eq hrn hαn e))
      by_cases hre : isEpsLevel r 0 = true
      · obtain ⟨z, hz, hze, hTz, hzN, hΔz⟩ := root_of_eps_term hrn hre hN (by
          rw [← trTm_eps_val hN he]; exact hrα'.le)
        have hzv : ordOf [z] = r.val := by rw [← val_trTm_root hz, hTz]
        have hzN' : z < .node 0 H := lt_of_le_of_ne hzN (fun e => by
          rw [e, ← trTm_eps_val hN he] at hzv; rw [hzv] at hrα'; exact lt_irrefl _ hrα')
        rcases key_eps_root hN he hz hze hzN' with hk | hk
        · -- level of `r` at most `Δ`
          have hgap' := gap_of_lt (m := 1) ((deltaOf_spec hane (by
              rw [hall' _ (List.getLast_mem hane)])).1) (NFP.nfs' hrn |>.takeWhile _)
            (fun q hq => by rw [(deltaOf_spec hane (by rw [hall' _ (List.getLast_mem hane)])).2.1 q hq])
            (argD_lvl _) (by
              show WP.valS (argD r.arg) < _
              rw [hΔz]; exact lt_of_le_of_lt hk hlev)
          rw [argV_split]
          refine lt_of_lt_of_le ?_ (le_trans hgap' hargep)
          exact (add_lt_add_iff_left _).mpr (valS_lt_Om (NFP.nfs' hrn |>.dropWhile _) (m := 0)
            (fun q hq => le_of_eq (argE_lvl (NFP.nfs' hrn) q hq)))
        · rw [htake] at hk
          have := ordOf_single_le hz has hk
          rw [hzv, ← hepv] at this
          exact absurd hepr (not_lt.mpr this)
      · have hl := arg_lvl_le_of_not_eps (m := 0) (a := r.arg) (by
          obtain ⟨m, a⟩ := r; simp only [WP.lvl_th] at hr0; subst hr0; exact hrn)
          (by obtain ⟨m, a⟩ := r; simp only [WP.lvl_th] at hr0; subst hr0; simpa using hre)
        have : argV r < Om 1 := valS_lt_Om (NFP.nfs' hrn) (m := 0) hl
        exact lt_of_lt_of_le this (le_trans hΩa hargep)
  refine locPred_eq hαn rfl hsuf hepα (fun q hq hqα => ?_)
  have := (sufMax_bound hN he hq hqα).2
  rw [htake, ← hepv] at this
  exact this

/-- **Case (a)**: `W` shares its run with `H_{k-1}`: `ᾱ = 𝒯(anchor N)`. -/
theorem case_a (hj : jOf 0 H + 2 ≤ H.length) :
    barT (.th 0 (deltaOf 0 H ++ eta'Of 0 H)) = trTm (.node 0 H.dropLast) := by
  obtain ⟨hne, hall, -⟩ := trTm_root_eps hN he
  obtain ⟨hD, hE⟩ := argDE_eps hN he
  have hv := valid_of_std hN
  set A' := H.dropLast with hA'
  set W := H.getLast hne with hW
  have hH : H = A' ++ [W] := (List.dropLast_append_getLast hne).symm
  have hA'len : A'.length = H.length - 1 := by simp [hA']
  have hA'ne : A' ≠ [] := by intro h; rw [h] at hA'len; simp at hA'len; omega
  set j := jOf 0 H with hjdef
  have hjA' : j < A'.length := by omega
  have hdropH : H.drop j = A'.drop j ++ [W] := by
    conv_lhs => rw [hH]
    rw [List.drop_append_of_le_length (by omega)]
  have hdA'ne : A'.drop j ≠ [] := by simp; omega
  -- the members of `A'.drop j` are in the run
  have hrun : ∀ h ∈ A'.drop j, dOf 0 h = deltaOf 0 H := fun h hh =>
    dOf_run hne (by rw [hdropH]; exact List.mem_append_left _ hh)
  have hWrun : dOf 0 W = deltaOf 0 H := by rw [deltaOf_eq_last hne]
  -- (S1) `Δ` is unchanged
  have hΔ : deltaOf 0 A' = deltaOf 0 H := by
    rw [deltaOf_eq_last hA'ne, ← List.getLast_drop hdA'ne]
    exact hrun _ (List.getLast_mem hdA'ne)
  -- (S2) the run starts at the same place
  have hjA : jOf 0 A' = j := by
    have hds : A'.map (dOf 0) ≠ [] := by simpa using hA'ne
    have hlastA : (A'.map (dOf 0)).getLast hds = dOf 0 W := by
      rw [List.getLast_map, ← deltaOf_eq_last hA'ne, hΔ, hWrun]
    have e := runStart_append_last hds
    rw [hlastA] at e
    show runStart (A'.map (dOf 0)) = runStart (H.map (dOf 0))
    rw [← e, hH, List.map_append]; rfl
  -- (S3) the same `e_p`, and the same insertion
  have htakeA : A'.take j = H.take j := by
    rw [hA', List.dropLast_eq_take, List.take_take, min_eq_left (by omega)]
  have hepA : epOf 0 A' = epOf 0 H := by unfold epOf; rw [hjA, htakeA]
  have hinsA : insOf 0 A' ↔ insOf 0 H := by unfold insOf; rw [hjA, hΔ, hepA]
  -- `ω^{ρ_W}` is at most `ω^{ρ_h}` for `h` in the run
  have hwle : ∀ h ∈ A'.drop j, (wOf 0 W).val ≤ (wOf 0 h).val := by
    intro h hh
    have hhA : h ∈ A' := List.mem_of_mem_drop hh
    have hhH : h ∈ H := List.mem_of_mem_dropLast hhA
    have hWh : W ≤ h := by
      have hd := hv.desc
      rw [hH] at hd
      exact (List.pairwise_append.mp hd).2.2 h hhA W (by simp)
    have hm := d_rho_mono (k := 0) (mono_le (hv.child (List.getLast_mem hne)) (hv.child hhH) hWh)
    have hρ := hm.2 (by rw [hWrun, hrun h hh])
    rw [(wOf_spec 0 W).2.2.2, (wOf_spec 0 h).2.2.2]
    exact opow_le_opow_right omega0_pos hρ
  -- (S4) `c = c_a + ω^{ρ_W}` without absorption
  have hcA_mem : ∀ p ∈ cOf 0 A', (wOf 0 W).val ≤ p.val := by
    intro p hp
    obtain ⟨x, hx, hpx⟩ := mem_addAll hp
    rw [hjA] at hx
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hx
    rw [List.mem_singleton.mp hpx]; exact hwle h hh
  have hc : cOf 0 H = cOf 0 A' ++ [wOf 0 W] := by
    have e1 : cOf 0 H = TR.addAll ((A'.drop j).map (fun h => [wOf 0 h]) ++ [[wOf 0 W]]) := by
      unfold cOf; rw [hdropH, List.map_append]; rfl
    have e2 : cOf 0 A' = TR.addAll ((A'.drop j).map (fun h => [wOf 0 h])) := by
      unfold cOf; rw [hjA]
    rw [e1, addAll_append_single, ← e2]
    exact addS_eq_append (cOf_spec 0 A').1 (NFS.single (wOf_spec 0 W).1)
      (fun p hp q hq => by rw [List.head?_cons, Option.mem_def, Option.some.injEq] at hq; subst hq
                           exact hcA_mem p hp)
  -- (S5), (S6)
  have hcAne := cOf_ne_nil (k := 0) hA'ne
  have hη : etaOf 0 H = etaOf 0 A' ++ [wOf 0 W] := by
    unfold etaOf; rw [hc, minusOnePlus_append hcAne]
  have hw_one : etaOf 0 A' = [] → wOf 0 W = TR.one := by
    intro h0
    have hc1 := eq_one_of_minusOnePlus_nil hcAne h0
    have := hcA_mem TR.one (by rw [hc1]; simp)
    rw [val_one] at this
    exact eq_one_of_val (wOf_spec 0 W).1 (le_antisymm this (one_le_val (wOf_spec 0 W).1))
  have hη' : eta'Of 0 H = eta'Of 0 A' ++ [wOf 0 W] := by
    by_cases hins : insOf 0 H
    · have e1 : eta'Of 0 H = addS [epOf 0 H] (etaOf 0 H) := by unfold eta'Of; rw [if_pos hins]
      have e2 : eta'Of 0 A' = addS [epOf 0 H] (etaOf 0 A') := by
        unfold eta'Of; rw [if_pos (hinsA.mpr hins), hepA]
      rw [e1, e2, hη]
      by_cases h0 : etaOf 0 A' = []
      · rw [h0, hw_one h0]
        simp only [List.nil_append]
        have hepn : NFP (epOf 0 H) := by unfold epOf; exact trTm_nfp _
        rw [addS_eq_append (NFS.single hepn) (NFS.single nfp_one) (fun p hp q hq => by
          rw [List.mem_singleton.mp hp]
          rw [List.head?_cons, Option.mem_def, Option.some.injEq] at hq; subst hq
          rw [val_one]; exact one_le_val hepn)]
        simp [addS]
      · exact addS_append_right h0
    · have e1 : eta'Of 0 H = etaOf 0 H := by unfold eta'Of; rw [if_neg hins]
      have e2 : eta'Of 0 A' = etaOf 0 A' := by unfold eta'Of; rw [if_neg (fun h => hins (hinsA.mp h))]
      rw [e1, e2, hη]
  -- Def 5.1, first case
  have hlast : (argE (WP.th 0 (deltaOf 0 H ++ eta'Of 0 H)).arg).getLast? = some (wOf 0 W) := by
    simp only [WP.arg_th]; rw [hE, hη']; simp
  have hdrop : (argE (WP.th 0 (deltaOf 0 H ++ eta'Of 0 H)).arg).dropLast = eta'Of 0 A' := by
    simp only [WP.arg_th]; rw [hE, hη', List.dropLast_concat]
  -- the anchor `(0, A')`
  have hAs : Std (.node 0 A') := by rw [hA', List.dropLast_eq_take]; exact std_take hN _
  have hAe : isEps (.node 0 A') = true := by
    simp only [isEps, List.getLast?_eq_some_getLast hA'ne, decide_eq_true_eq]
    rw [hall _ (List.mem_of_mem_dropLast (List.getLast_mem hA'ne))]
  have hcond : wOf 0 W = TR.one ∨
      ((argE (WP.th 0 (deltaOf 0 H ++ eta'Of 0 H)).arg).dropLast ≠ [] ∧
        ¬ supPt (argD (WP.th 0 (deltaOf 0 H ++ eta'Of 0 H)).arg)
          (argE (WP.th 0 (deltaOf 0 H ++ eta'Of 0 H)).arg).dropLast) := by
    by_cases hw1 : wOf 0 W = TR.one
    · exact Or.inl hw1
    · right
      rw [hdrop]
      simp only [WP.arg_th]; rw [hD]
      refine ⟨fun h0 => ?_, fun hs => ?_⟩
      · by_cases hins : insOf 0 A'
        · have : eta'Of 0 A' = addS [epOf 0 A'] (etaOf 0 A') := by unfold eta'Of; rw [if_pos hins]
          rw [this] at h0
          rcases hηa : etaOf 0 A' with _ | ⟨y0, ys⟩
          · rw [hηa] at h0; simp [addS] at h0
          · rw [hηa] at h0; simp [addS] at h0
        · have : eta'Of 0 A' = etaOf 0 A' := by unfold eta'Of; rw [if_neg hins]
          rw [this] at h0
          exact hw1 (hw_one h0)
      · rw [← hΔ] at hs
        have hns := lemmaNS hAs hAe hA'ne hs
        have hmem : A'.getLast hA'ne ∈ A'.drop j := by
          rw [← List.getLast_drop hdA'ne]; exact List.getLast_mem hdA'ne
        have := hwle _ hmem
        rw [hns, val_one] at this
        exact hw1 (eq_one_of_val (wOf_spec 0 W).1 (le_antisymm this (one_le_val (wOf_spec 0 W).1)))
  rw [barT_pos hlast hcond, hdrop]
  simp only [WP.arg_th]
  rw [hD, ← hΔ, (trTm_root_eps hAs hAe).2.2]

end Cases

/-- **`Bar_T`** (`proof/PROOF-3.md` §13.3, §14.2). -/
theorem barEps {N : Tm} (hN : Std N) (he : isEps N = true) :
    (∀ a, anchor N = some a → barO (ordOf [N]) = ordOf [a]) ∧
      (anchor N = none → barO (ordOf [N]) = 1) := by
  have hNeq := std_node_y hN
  set H := N.cs with hH
  have hN' : Std (.node 0 H) := by rw [← hNeq]; exact hN
  have he' : isEps (.node 0 H) = true := by rw [← hNeq]; exact he
  obtain ⟨hne, -, -⟩ := trTm_root_eps hN' he'
  have hbar : barO (ordOf [N]) = (barT (.th 0 (deltaOf 0 H ++ eta'Of 0 H))).val := by
    rw [hNeq, ← trTm_eps_val hN' he', barO_eq (nfp_eps hN' he') rfl]
  refine ⟨fun a ha => ?_, fun ha => ?_⟩
  · rw [hNeq] at ha
    have h2 : 2 ≤ H.length := by
      simp only [anchor] at ha; split_ifs at ha with h
      exact h
    have haeq : a = Tm.node 0 H.dropLast := by
      rw [anchor_node h2] at ha; exact (Option.some.inj ha).symm
    have has : Std (Tm.node 0 H.dropLast) := by
      rw [List.dropLast_eq_take]; exact std_take hN' _
    rw [hbar, haeq, ← val_trTm_root has]
    have hjlt := jOf_lt hne
    by_cases hj : jOf 0 H + 2 ≤ H.length
    · rw [case_a hN' he' hj]
    · rw [case_b hN' he' h2 (by omega)]
  · rw [hNeq] at ha
    have h1 : H.length = 1 := by
      simp only [anchor] at ha; split_ifs at ha with h
      have := List.length_pos_of_ne_nil hne
      omega
    rw [hbar, case_c hN' he' h1, val_one]

end Googology.Trans.PSS.Main

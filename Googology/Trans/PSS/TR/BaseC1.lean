import Googology.Trans.PSS.TR.Bases

/-!
# The base `(B j₀)` when `ℓ` is a child of `j₀`

`proof/TR-2.md` §4b.3, the C1 sub-case of `(B j₀)`: `j₀ = (m, H ++ [ℓ])` with
`ℓ = (m+1, ())`, and the blocks `j₀⟨n⟩ = (m, H ++ [j₀⟨n-1⟩])`,
`j₀⟨1⟩ = (m, H)`.  The paper uses (Min) here; this proof instead uses the size
induction of the general case, so (Min) is not needed.

* `rhoOf_eq_nil_of_hi`: `ρ_c = 0` when every child of `c` has level `≥ k + 1`.
* `argOf_append_one`: appending a child in the final run with `ω^ρ = 1` appends
  `1` to the argument.
* `star_arg_hi_leaf`: the visible `ϑ_m`-subterms of the argument of `𝒯(j₀)` are
  at most `𝒯((m, H))`, or `1`.
* `val_le_exp`: `ϑ_m(β) ≤ ω^{Ω_m + β + 1}` for `β < Ω_{m+1}` (Exp).
* `base_C1`.
-/

namespace Googology.Trans.PSS.TR

open Forest Phi Ordinal

/-! ## `ρ = 0` -/

theorem logOmega_of_eps {p : WP} (h : isEpsLevel p p.lvl = true) : logOmega p = [p] := by
  simp [logOmega, h]

theorem splitLevel_of_ge {x : List WP} {m : ℕ} (h : ∀ q ∈ x, m ≤ q.lvl) :
    (splitLevel x m).2 = [] := by
  simp only [splitLevel]
  rw [List.dropWhile_eq_nil_iff]
  intro q hq
  simpa using h q hq

/-- **`ρ_c = 0`** when every child of `c` has level `≥ k + 1`. -/
theorem rhoOf_eq_nil_of_hi {k : ℕ} {cs : List Tm} {x : Tm}
    (hv : Valid (.node (k + 1) (cs ++ [x]))) (hx : k + 1 ≤ x.y) :
    rhoOf k (.node (k + 1) (cs ++ [x])) = [] := by
  have hne : cs ++ [x] ≠ [] := by simp
  have hxy : x.y ≤ k + 2 := hv.y_le (by simp)
  have hall : ∀ c ∈ cs ++ [x], k + 1 ≤ c.y := by
    intro c hc
    have := Tm.y_le_of_le (getLast_le_of_desc hv.desc hne c hc)
    simp at this; omega
  rcases (show x.y = k + 2 ∨ x.y = k + 1 by omega) with hx2 | hx1
  · -- epsilon: `log 𝒯(c) = [𝒯(c)]`
    have hl : ((cs ++ [x]).getLast hne).y = k + 1 + 1 := by simpa using hx2
    have he := trTm_eps' hne hl
    have hnf := nfp_trTm_eps hne hl
    have heps : isEpsLevel (WP.th (k + 1) (argOf (k + 1) (cs ++ [x]))) (k + 1) = true := by
      rw [isEpsLevel_iff, argOf_eq hne hl]
      obtain ⟨-, h2, h3⟩ := deltaOf_spec hne hl
      obtain ⟨q, r, hqr⟩ := List.exists_cons_of_ne_nil h3
      exact ⟨rfl, q, by simp [hqr], by rw [h2 q (by rw [hqr]; simp)]⟩
    rw [rhoOf, monOf, he, logOmega_of_eps heps]
    exact splitLevel_of_ge (fun q hq => by rw [List.mem_singleton.mp hq]; rfl)
  · -- not epsilon: all summands of `Z` have level `k + 1`
    have hW := zPre_nfs (k + 1) cs
    have hWl : ∀ q ∈ zPre (k + 1) cs, q.lvl = k + 1 := by
      intro q hq
      obtain ⟨y, hy, hqy⟩ := mem_addAll hq
      rcases List.mem_append.mp hy with hy | hy
      · exact ((headPart_spec (k + 1) cs).1 y hy).2 q hqy
      · rw [List.mem_map] at hy
        obtain ⟨c, hc, rfl⟩ := hy
        rw [List.mem_singleton.mp hqy, trTm_lvl]
        have h1 := (List.mem_filter.mp hc)
        have h2 := hall c (by simp [h1.1])
        simp at h1; omega
    obtain ⟨hYn, hYv⟩ := addS_spec hW (NFS.single (trTm_nfp x))
    have hYl : ∀ q ∈ addS (zPre (k + 1) cs) [trTm x], k + 1 ≤ q.lvl := by
      intro q hq
      rcases mem_addS hq with hq | hq
      · exact (hWl q hq).ge
      · rw [List.mem_singleton.mp hq, trTm_lvl, hx1]
    have hXY : logOmega (trTm (.node (k + 1) (cs ++ [x]))) = addS (zPre (k + 1) cs) [trTm x] := by
      refine eq_of_valS_eq (logOmega_spec (trTm_nfp _)).1 hYn ?_
      rw [val_log_append_lo (by omega), hYv, valS_single]
    rw [rhoOf, monOf, hXY]
    exact splitLevel_of_ge hYl

/-! ## Appending `1` to the run -/

/-- Appending a child in the final run with `ω^ρ = 1` appends `1` to the
argument. -/
theorem argOf_append_one {k : ℕ} {H : List Tm} {x : Tm} (hHne : H ≠ [])
    (hlH : (H.getLast hHne).y = k + 1) (hx : x.y = k + 1)
    (hD : dOf k x = dOf k (H.getLast hHne)) (hw : wOf k x = one) :
    argOf k (H ++ [x]) = argOf k H ++ [one] := by
  have hne' : H ++ [x] ≠ [] := by simp
  have hl' : ((H ++ [x]).getLast hne').y = k + 1 := by simpa using hx
  have hj : jOf k (H ++ [x]) = jOf k H := by
    rw [jOf, jOf, List.map_append, List.map_singleton, hD]
    have := runStart_append_last (ds := H.map (dOf k)) (by simpa using hHne)
    rw [List.getLast_map] at this
    exact this
  have hjle : jOf k H ≤ H.length := by
    have := runStart_le_length (H.map (dOf k)); simpa using this
  have hep : epOf k (H ++ [x]) = epOf k H := by
    rw [epOf, epOf, hj, List.take_append_of_le_length hjle]
  have hdH : deltaOf k H = dOf k (H.getLast hHne) := by
    rw [deltaOf, List.getLast?_eq_some_getLast hHne]; rfl
  have hΔ' : deltaOf k (H ++ [x]) = deltaOf k H := by
    rw [deltaOf, List.getLast?_append_of_ne_nil _ (by simp), hdH]
    simp [hD]
  have hins : insOf k (H ++ [x]) ↔ insOf k H := by
    unfold insOf; rw [hj, hΔ', hep]
  have hc : cOf k (H ++ [x]) = cOf k H ++ [one] := by
    rw [cOf, cOf, hj, List.drop_append_of_le_length hjle, List.map_append, List.map_singleton,
      addAll_append_single, hw]
    exact addS_eq_append (cOf_spec k H).1 (NFS.single nfp_one)
      (fun p hp q hq => by
        rw [Option.mem_def, List.head?_cons, Option.some.injEq] at hq
        rw [← hq, val_one]; exact one_le_val ((cOf_spec k H).1.1 p hp))
  have hη : etaOf k (H ++ [x]) = etaOf k H ++ [one] := by
    rw [etaOf, etaOf, hc, minusOnePlus_append (cOf_ne_nil hHne)]
  have hη' : eta'Of k (H ++ [x]) = eta'Of k H ++ [one] := by
    unfold eta'Of
    by_cases hi : insOf k H
    · rw [if_pos (hins.mpr hi), if_pos hi, hη, hep]
      rcases eq_or_ne (etaOf k H) [] with he | he
      · rw [he, List.nil_append]
        rw [addS_eq_append (x := [epOf k H]) (NFS.single (trTm_nfp _)) (NFS.single nfp_one)]
        · simp [addS]
        · intro p hp q hq
          rw [List.mem_singleton.mp hp]
          rw [Option.mem_def, List.head?_cons, Option.some.injEq] at hq
          rw [← hq, val_one]; exact one_le_val (trTm_nfp _)
      · exact addS_append_right he
    · rw [if_neg (fun h => hi (hins.mp h)), if_neg hi, hη]
  rw [argOf_eq hne' hl', argOf_eq hHne hlH, hΔ', hη', List.append_assoc]

/-! ## The visible subterms of `𝒯(j₀)` -/

theorem dOf_leaf_succ (m : ℕ) : dOf m (.node (m + 1) []) = [.th (m + 1) []] := by
  rw [dOf, monOf, trTm_leaf]
  simp [logOmega, isEpsLevel, isEpsPlusN, addS, splitLevel]

theorem rhoOf_leaf_succ (m : ℕ) : rhoOf m (.node (m + 1) []) = [] := by
  rw [rhoOf, monOf, trTm_leaf]
  simp [logOmega, isEpsLevel, isEpsPlusN, addS, splitLevel]

/-- The visible `ϑ_m`-subterms of the argument of `𝒯((m, H ++ [(m+1, ())]))` are
at most `𝒯((m, H))`, or `1`. -/
theorem star_arg_hi_leaf {m : ℕ} {H : List Tm} (hv : Valid (.node m (H ++ [.node (m + 1) []])))
    {z : WP} (hz : z ∈ starS m (argOf m (H ++ [.node (m + 1) []]))) :
    z.val ≤ (trTm (.node m H)).val ∨ z = one := by
  set ℓ : Tm := .node (m + 1) [] with hℓ
  have hne : H ++ [ℓ] ≠ [] := by simp
  have hl : ((H ++ [ℓ]).getLast hne).y = m + 1 := by simp [hℓ]
  have hall := hv.eps_all hne hl
  have hwℓ : wOf m ℓ = one := wOf_eq_one (rhoOf_leaf_succ m)
  have hΔℓ : deltaOf m (H ++ [ℓ]) = [.th (m + 1) []] := by
    rw [deltaOf, List.getLast?_append_of_ne_nil _ (by simp)]
    exact dOf_leaf_succ m
  rcases eq_or_ne H [] with rfl | hHne
  · -- `η' = ()`
    exfalso
    have hj0 : jOf m ([] ++ [ℓ]) = 0 := by simp [jOf, runStart]
    have : eta'Of m ([] ++ [ℓ]) = [] := by
      rw [eta'Of, if_neg (by unfold insOf; rw [hj0]; simp), etaOf, cOf, hj0]
      simp [hwℓ, addAll, addS, minusOnePlus]
    rw [argOf_eq hne hl, this, List.append_nil, hΔℓ] at hz
    rcases mem_starS_single hz with ⟨h, -⟩ | ⟨-, hz⟩
    · simp at h
    · simp at hz
  have hlH : (H.getLast hHne).y = m + 1 := hall _ (by simp [List.getLast_mem hHne])
  have hvH : Valid (.node m H) := by
    have := hv.take H.length; rwa [List.take_left] at this
  have hℓle : (trTm ℓ).val ≤ (trTm (H.getLast hHne)).val :=
    mono_le (hv.child (by simp)) (hv.child (by simp [List.getLast_mem hHne]))
      ((List.pairwise_append.mp hv.desc).2.2 _ (List.getLast_mem hHne) ℓ (by simp))
  obtain ⟨hDle, -⟩ := d_rho_mono (k := m) hℓle
  rcases hDle.lt_or_eq with hDlt | hDeq
  · -- a new run
    have hdne : dOf m ℓ ≠ dOf m (H.getLast hHne) := fun e' => by
      rw [e'] at hDlt; exact lt_irrefl _ hDlt
    have hj : jOf m (H ++ [ℓ]) = H.length := by
      rw [jOf, List.map_append, List.map_singleton,
        runStart_append_ne (fun hne2 => by rw [List.getLast_map]; exact hdne)]
      simp
    have hep : epOf m (H ++ [ℓ]) = trTm (.node m H) := by rw [epOf, hj, List.take_left]
    have hη0 : etaOf m (H ++ [ℓ]) = [] := by
      rw [etaOf, cOf, hj, List.drop_left, List.map_singleton, hwℓ]
      simp [addAll, addS, minusOnePlus]
    rw [argOf_eq hne hl, starS_append, List.mem_append] at hz
    rcases hz with hz | hz
    · rw [hΔℓ] at hz
      rcases mem_starS_single hz with ⟨h, -⟩ | ⟨-, hz⟩
      · simp at h
      · simp at hz
    · unfold eta'Of at hz
      split_ifs at hz
      · rw [hη0] at hz
        rw [show addS [epOf m (H ++ [ℓ])] [] = [epOf m (H ++ [ℓ])] from rfl] at hz
        left
        rw [← hep]
        exact val_le_of_mem_starS_single (trTm_nfp _) (by simpa using hz)
      · rw [hη0] at hz; simp at hz
  · -- the same run: the argument gains `1`
    have hD : dOf m ℓ = dOf m (H.getLast hHne) :=
      eq_of_valS_eq (monOf_spec m ℓ).2.1 (monOf_spec m _).2.1 hDeq
    rw [argOf_append_one hHne hlH (by simp [hℓ]) hD hwℓ, starS_append, List.mem_append] at hz
    rcases hz with hz | hz
    · left
      have hn := nfp_trTm_eps hHne hlH
      rw [trTm_eps' hHne hlH]
      exact (star_lt_val hn z hz).le
    · right
      rcases mem_starS_single hz with ⟨-, rfl⟩ | ⟨-, hz⟩
      · rfl
      · simp [one] at hz

/-! ## A bound from (Exp) -/

/-- For `β < Ω_{m+1}`: `ϑ_m(β) ≤ ω^{Ω_m + β + 1}` (from (Exp)). -/
theorem val_le_exp {m : ℕ} {β : List WP} (h : NFP (.th m β)) (hl : ∀ q ∈ β, q.lvl ≤ m) :
    (WP.th m β).val ≤ ω ^ (expBase m + WP.valS β + 1) := by
  cases he : isEpsPlusN β m
  · rw [val_exp h hl he]
    exact (opow_le_opow_iff_right one_lt_omega0).mpr le_self_add
  · rw [val_exp_eps h he]
    exact (opow_le_opow_iff_right one_lt_omega0).mpr
      (add_le_add_left le_add_self _)

theorem expBase_le (m : ℕ) : expBase m ≤ Om m := by
  unfold expBase; split_ifs <;> simp

/-! ## The base -/

/-- The blocks of `j₀ = (m, H ++ [(m+1, ())])`: `(m, H)`, then `(m, H ++ [previous])`. -/
def c1seq (m : ℕ) (H : List Tm) : ℕ → Tm
  | 0 => .node m H
  | n + 1 => .node m (H ++ [c1seq m H n])

theorem c1seq_y (m : ℕ) (H : List Tm) (n : ℕ) : (c1seq m H n).y = m := by
  cases n <;> rfl

/-- **(B j₀), the case `p(ℓ) = j₀`** (`proof/TR-2.md` §4b.3), without (Min). -/
theorem base_C1 {m : ℕ} {H : List Tm} (hv : Valid (.node m (H ++ [.node (m + 1) []])))
    (hvs : ∀ n, Valid (c1seq m H n)) :
    LC 0 (fun _ => True) (.node m (H ++ [.node (m + 1) []])) (fun n => c1seq m H (n + 1)) := by
  set ℓ : Tm := .node (m + 1) [] with hℓ
  have hne : H ++ [ℓ] ≠ [] := by simp
  have hl : ((H ++ [ℓ]).getLast hne).y = m + 1 := by simp [hℓ]
  have hall := hv.eps_all hne hl
  have hna := nfp_trTm_eps hne hl
  have hΔℓ : deltaOf m (H ++ [ℓ]) = [.th (m + 1) []] := by
    rw [deltaOf, List.getLast?_append_of_ne_nil _ (by simp)]
    exact dOf_leaf_succ m
  set E : ℕ → Ordinal.{0} := fun n => (trTm (c1seq m H (n + 1))).val with hE
  have hEp : ∀ n, IsPrincipal (· + ·) (E n) := fun n => val_isPrincipal (trTm_nfp _)
  have hEΩ : ∀ n, Om m < E n := fun n => by
    have := Om_lt_val_trTm (hvs (n + 1)) (show H ++ [c1seq m H n] ≠ [] by simp)
    exact this
  have hanc : ∀ n, (trTm (.node m H)).val < E n := by
    intro n
    refine mono (hvs 0) (hvs (n + 1)) ?_
    show Tm.node m H < Tm.node m (H ++ [c1seq m H n])
    exact (Tm.node_lt_node_iff _ _ _ _).mpr (Or.inr ⟨rfl, lt_of_prefix (by simp)⟩)
  intro γ hγ hlt hB
  rw [trTm_eps' hne hl] at hlt
  refine lc_skeleton (Nat.zero_le m) hna hEp hEΩ (fun n z hz => ?_) (fun β hβn hβlt _ hsIH => ?_)
    γ hγ hlt hB
  · rcases star_arg_hi_leaf hv hz with h | rfl
    · exact lt_of_le_of_lt h (hanc n)
    · rw [val_one]; exact lt_of_le_of_lt (one_le_Om m) (hEΩ n)
  -- the step: `β < Δ + η'`
  obtain ⟨hsplit, hΓn, hσn, hΓl, hσl⟩ := splitLevel_spec hβn.nfs (m + 1)
  set Γ := (splitLevel β (m + 1)).1
  set σ := (splitLevel β (m + 1)).2
  have hσl' : ∀ q ∈ σ, q.lvl ≤ m := fun q hq => Nat.lt_succ_iff.mp (hσl q hq)
  have hβv : WP.valS β = WP.valS Γ + WP.valS σ := by rw [hsplit, valS_append]
  obtain ⟨hΔn', hΔl', -⟩ := deltaOf_spec hne hl
  have hargA := (argOf_spec hne hl).2.2
  have hΓle : WP.valS Γ ≤ WP.valS (deltaOf m (H ++ [ℓ])) := by
    refine (split_mono (ρ := σ) hΓn hΔn' hΓl (fun q hq => (hΔl' q hq).ge)
      (val_eps_lt_Om (H := H ++ [ℓ])) ?_).1
    rw [← hβv, ← hargA]; exact hβlt.le
  rcases hΓle.lt_or_eq with hΓlt | hΓeq
  · -- `Γ = ()`: `β < Ω_{m+1}`
    have hΓ0 : Γ = [] := by
      have hgap := gap_of_lt hΔn' hΓn (fun q hq => (hΔl' q hq).ge) hΓl hΓlt
      rw [hΔℓ, valS_single, WP.val_th, WP.valS_nil, vartheta_zero] at hgap
      cases hΓe : Γ with
      | nil => rfl
      | cons q r =>
        exfalso
        rw [hΓe] at hgap hΓn hΓl
        have h1 : Om (m + 1) ≤ WP.valS (q :: r) :=
          le_trans (Om_le_val_of_le_lvl hΓn.head (hΓl q (by simp))) le_valS_head
        have h2 : Om (m + 1) < Om (m + 1) + Om (m + 1) := lt_add_of_pos_right _ (Om_pos _)
        exact absurd hgap (not_le.mpr (lt_of_lt_of_le h2 (add_le_add_left h1 _)))
    have hβσ : β = σ := by rw [hsplit, hΓ0, List.nil_append]
    have hβl : ∀ q ∈ β, q.lvl ≤ m := by rw [hβσ]; exact hσl'
    have hq : ∀ q ∈ β, ∃ n0, ∀ n ≥ n0, q.val < E n := by
      intro q hq
      rcases (hβl q hq).lt_or_eq with hql | hql
      · exact ⟨0, fun n _ => lt_trans (val_lt_Om_of_lvl_lt (hβn.of_mem hq) hql) (hEΩ n)⟩
      · exact hsIH q (mem_starS_of_mem hq hql)
    obtain ⟨n0, h0⟩ := eventually_forall β hq
    refine ⟨n0 + 1, fun n hn => ?_⟩
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have hβE : WP.valS β < E n' := valS_lt_of_forall (hEp n') (lt_of_le_of_lt zero_le (hEΩ n'))
      (fun q hq => h0 n' (by omega) q hq)
    have hsum : expBase m + WP.valS β + 1 < E n' :=
      hEp n' (hEp n' (lt_of_le_of_lt (expBase_le m) (hEΩ n')) hβE)
        (lt_of_le_of_lt (one_le_Om m) (hEΩ n'))
    refine lt_of_le_of_lt (val_le_exp hβn hβl) (lt_of_lt_of_le
      ((opow_lt_opow_iff_right one_lt_omega0).mpr hsum) ?_)
    show ω ^ E n' ≤ (trTm (.node m (H ++ [c1seq m H (n' + 1)]))).val
    rw [val_trTm_append_lo (by rw [c1seq_y])]
    exact (opow_le_opow_iff_right one_lt_omega0).mpr le_add_self
  · -- `Γ = Δ`: the anchor
    have hΓΔ : Γ = deltaOf m (H ++ [ℓ]) := eq_of_valS_eq hΓn hΔn' hΓeq
    have hση : WP.valS σ < WP.valS (eta'Of m (H ++ [ℓ])) := by
      rw [hβv, hΓeq, hargA] at hβlt
      exact (add_lt_add_iff_left _).mp hβlt
    have hβe : β = deltaOf m (H ++ [ℓ]) ++ σ := by rw [hsplit, hΓΔ]
    have hrc : ∀ hne : H ≠ [], (trTm ℓ).val ≤ (trTm (H.getLast hne)).val := fun hHne =>
      mono_le (hv.child (by simp)) (hv.child (by simp [List.getLast_mem hHne]))
        ((List.pairwise_append.mp hv.desc).2.2 _ (List.getLast_mem hHne) ℓ (by simp))
    obtain ⟨-, hle⟩ := anchor_bound (fun h hh => hall h (by simp [hh])) (rhoOf_leaf_succ m) hrc
      hσn hσl' (by rw [← hβe]; exact hβn) hση
    rw [← hβe] at hle
    exact ⟨0, fun n _ => lt_of_le_of_lt hle (hanc n)⟩

end Googology.Trans.PSS.TR

import Googology.Trans.PSS.TR.FundSeq

/-!
# The bases of cofinality

`proof/TR-2.md` §4b.3.

* `lc_skeleton`: the induction on the size of `γ` shared by P-hi and the bases:
  reduce to the first summand `ϑ_k(β)`, case (ii) of (C) by a bound on the
  visible subterms of the argument, case (i) by a given step.
* `base_ell` (**(Bℓ)**): `LC_{B_m}(ℓ)` for the leaf `ℓ = (m+1, ())`, whose
  blocks are the blocks of `j₀` (of level `m`).
* `anchor_bound`: the anchor case of P-hi (`ρ_c = 0`): `ϑ_k(Δ + σ) ≤ 𝒯((k, H))`.
* `d_eq_of_split`, `dOf_lo_eq`, `rhoOf_eq_nil_of_hi`: the `D`-part of `log 𝒯(c)`
  when the last child of `c` changes below level `k + 1`, and `ρ_c = 0` when all
  children of `c` have level `≥ k + 1`.
-/

namespace Googology.Trans.PSS.TR

open Forest Phi Ordinal

/-! ## The skeleton of the size induction -/

theorem lc_skeleton {k mγ : ℕ} {Pγ : WP → Prop} (hmγ : mγ ≤ k) {argA : List WP}
    (hna : NFP (.th k argA)) {E : ℕ → Ordinal.{0}} (hEp : ∀ n, IsPrincipal (· + ·) (E n))
    (hEΩ : ∀ n, Om k < E n) (hwit : ∀ n, ∀ z ∈ starS k argA, z.val < E n)
    (hstep : ∀ β : List WP, NFP (.th k β) → WP.valS β < WP.valS argA → Bm mγ Pγ [.th k β] →
      (∀ s ∈ starS k β, ∃ n0, ∀ n ≥ n0, s.val < E n) → ∃ n0, ∀ n ≥ n0, (WP.th k β).val < E n) :
    ∀ γ : List WP, NFS γ → WP.valS γ < (WP.th k argA).val → Bm mγ Pγ γ →
      ∃ n0, ∀ n ≥ n0, WP.valS γ < E n := by
  have hE0 : ∀ n, 0 < E n := fun n => lt_of_le_of_lt zero_le (hEΩ n)
  suffices H' : ∀ N, ∀ γ : List WP, WP.sizeS γ ≤ N → NFS γ →
      WP.valS γ < (WP.th k argA).val → Bm mγ Pγ γ → ∃ n0, ∀ n ≥ n0, WP.valS γ < E n from
    fun γ hγ hlt' hB' => H' _ γ le_rfl hγ hlt' hB'
  intro N
  induction N with
  | zero =>
    intro γ hsz hγ _ _
    cases γ with
    | nil => exact ⟨0, fun n _ => by simpa using hE0 n⟩
    | cons g γ' => exact absurd hsz (by simp; have := WP.size_pos g; omega)
  | succ N ih =>
    intro γ hsz hγ hlt' hB'
    cases γ with
    | nil => exact ⟨0, fun n _ => by simpa using hE0 n⟩
    | cons g γ' =>
      have hg := hγ.head
      suffices hsg : ∃ n0, ∀ n ≥ n0, g.val < E n by
        obtain ⟨n0, h0⟩ := hsg
        exact ⟨n0, fun n hn => valS_lt_of_head hγ (hEp n) (hE0 n) (fun p hp => by
          rw [Option.mem_def, List.head?_cons, Option.some.injEq] at hp
          rw [← hp]; exact h0 n hn)⟩
      have hgle : g.val < (WP.th k argA).val := lt_of_le_of_lt le_valS_head hlt'
      have hgl : g.lvl ≤ k := by
        have := lvl_le_of_val_le hg hna hgle.le
        simpa using this
      rcases hgl.lt_or_eq with hgl | hgl
      · exact ⟨0, fun n _ => lt_trans (val_lt_Om_of_lvl_lt hg hgl) (hEΩ n)⟩
      obtain ⟨k', β⟩ := g
      simp only [WP.lvl_th] at hgl
      subst hgl
      rcases (val_lt_val_iff hg hna).mp hgle with ⟨hβlt, hβs⟩ | ⟨s, hs, hgs⟩
      · have hBg : Bm mγ Pγ [WP.th k' β] := hB'.single_of_mem (by simp)
        refine hstep β hg hβlt hBg (fun s hs => ?_)
        obtain ⟨hs1, -, hs3⟩ := starS_spec k' β hg.nfs s hs
        have hsz' : WP.sizeS [s] ≤ N := by
          simp only [WP.sizeS_cons, WP.sizeS_nil, add_zero, WP.size_th] at hsz ⊢
          omega
        obtain ⟨n0, h0⟩ := ih [s] hsz' (NFS.single hs1) (by rw [valS_single]; exact hβs s hs)
          (Bm.star hmγ hs (Bm.arg (by simp; omega) hBg))
        exact ⟨n0, fun n hn => by simpa using h0 n hn⟩
      · exact ⟨0, fun n _ => lt_of_le_of_lt hgs (hwit n s hs)⟩

/-! ## (Bℓ) -/

theorem monotone_of_succ {f : ℕ → Ordinal.{0}} (h : ∀ n, f n ≤ f (n + 1)) {a b : ℕ} (hab : a ≤ b) :
    f a ≤ f b := monotone_nat_of_le_succ h hab

/-- **(Bℓ)**: for the leaf `ℓ = (m+1, ())` with blocks `X n` of level `m`,
`LC_{B_m}(ℓ)` with `B_m(s) : ∃ n, s < 𝒯(X n)`. -/
theorem base_ell {m : ℕ} {X : ℕ → Tm} (hXy : ∀ n, (X n).y = m)
    (hmono : ∀ n, (trTm (X n)).val ≤ (trTm (X (n + 1))).val) :
    LC m (fun s => ∃ n, s.val < (trTm (X n)).val) (.node (m + 1) []) X := by
  intro γ hγ hlt hB
  rw [val_trTm_leaf] at hlt
  have hq : ∀ q ∈ γ, ∃ n0, ∀ n ≥ n0, q.val < (trTm (X n)).val := by
    intro q hq
    have hqn := hγ.1 q hq
    have hql : q.lvl ≤ m := by
      by_contra hc
      exact absurd (lt_of_le_of_lt (Om_le_valS_of_mem hγ hq (m := m + 1) (by omega)) hlt)
        (lt_irrefl _)
    rcases hql.lt_or_eq with hql | hql
    · exact ⟨0, fun n _ => lt_of_lt_of_le (val_lt_Om_of_lvl_lt hqn hql)
        (by have := Om_le_val_trTm (X n); rwa [hXy] at this)⟩
    · obtain ⟨n0, h0⟩ := hB q (mem_starS_of_mem hq hql)
      exact ⟨n0, fun n hn => lt_of_lt_of_le h0 (monotone_of_succ hmono hn)⟩
  obtain ⟨n0, h0⟩ := eventually_forall γ hq
  exact ⟨n0, fun n hn => valS_lt_of_forall (val_isPrincipal (trTm_nfp _))
    (val_pos (trTm_nfp _)) (fun q hq => h0 n hn q hq)⟩

/-! ## The anchor case -/

/-- **The anchor case** of P-hi: if `ρ_c = 0`, `β = Δ ++ σ` and `σ < η'`, then
`ϑ_k(β) ≤ 𝒯((k, H))`. -/
theorem anchor_bound {k : ℕ} {H : List Tm} {c : Tm}
    (hHl : ∀ h ∈ H, h.y = k + 1) (hρ0 : rhoOf k c = [])
    (hrc : ∀ hne : H ≠ [], (trTm c).val ≤ (trTm (H.getLast hne)).val)
    {σ : List WP} (hσn : NFS σ) (hσl' : ∀ q ∈ σ, q.lvl ≤ k)
    (hβn : NFP (.th k (deltaOf k (H ++ [c]) ++ σ)))
    (hση : WP.valS σ < WP.valS (eta'Of k (H ++ [c]))) :
    H ≠ [] ∧ (WP.th k (deltaOf k (H ++ [c]) ++ σ)).val ≤ (trTm (.node k H)).val := by
  have hwc : wOf k c = one := wOf_eq_one hρ0
  have hΔ : deltaOf k (H ++ [c]) = dOf k c := by
    rw [deltaOf, List.getLast?_append_of_ne_nil _ (by simp)]; rfl
  rcases eq_or_ne H [] with rfl | hHne
  · exfalso
    have hj0 : jOf k ([] ++ [c]) = 0 := by simp [jOf, runStart]
    have : WP.valS (eta'Of k ([] ++ [c])) = 0 := by
      rw [val_eta'Of, if_neg (by unfold insOf; rw [hj0]; simp), zero_add, etaOf, cOf, hj0]
      simp [hwc, addAll, addS, minusOnePlus]
    rw [this] at hση
    exact absurd hση (not_lt.mpr zero_le)
  refine ⟨hHne, ?_⟩
  have hlH : (H.getLast hHne).y = k + 1 := hHl _ (List.getLast_mem hHne)
  obtain ⟨hDle, -⟩ := d_rho_mono (k := k) (hrc hHne)
  have hdH : deltaOf k H = dOf k (H.getLast hHne) := by
    rw [deltaOf, List.getLast?_eq_some_getLast hHne]; rfl
  have hanchor : trTm (.node k H) = .th k (argOf k H) := trTm_eps' hHne hlH
  have hnanc : NFP (WP.th k (argOf k H)) := nfp_trTm_eps hHne hlH
  rw [hanchor]
  rcases hDle.lt_or_eq with hDlt | hDeq
  · -- a new run: `e_p = 𝒯(k, H)`
    have hdne : dOf k c ≠ dOf k (H.getLast hHne) := fun e' => by
      rw [e'] at hDlt; exact lt_irrefl _ hDlt
    have hj : jOf k (H ++ [c]) = H.length := by
      rw [jOf, List.map_append, List.map_singleton,
        runStart_append_ne (fun hne2 => by rw [List.getLast_map]; exact hdne)]
      simp
    have hep : epOf k (H ++ [c]) = trTm (.node k H) := by
      rw [epOf, hj, List.take_left]
    have hc1 : cOf k (H ++ [c]) = [one] := by
      rw [cOf, hj, List.drop_left, List.map_singleton, hwc]; rfl
    have hη0 : etaOf k (H ++ [c]) = [] := by rw [etaOf, hc1]; simp [minusOnePlus]
    by_cases hins : insOf k (H ++ [c])
    · have hσep : WP.valS σ < (trTm (.node k H)).val := by
        rw [val_eta'Of, if_pos hins, hη0, WP.valS_nil, add_zero, hep] at hση
        exact hση
      rw [hanchor] at hσep
      refine (le_of_lt ((val_lt_val_iff hβn hnanc).mpr (Or.inl ⟨?_, fun z hz => ?_⟩)))
      · rw [valS_append, hΔ, (argOf_spec hHne hlH).2.2, hdH]
        refine lt_of_lt_of_le ((add_lt_add_iff_left _).mpr (valS_lt_Om hσn hσl'))
          (le_trans ?_ le_self_add)
        exact gap_of_lt (monOf_spec k _).2.1 (monOf_spec k c).2.1
          (fun q hq => ((monOf_spec k _).2.2.2.1 q hq).1)
          (fun q hq => ((monOf_spec k c).2.2.2.1 q hq).1) hDlt
      · rw [starS_append, List.mem_append] at hz
        rcases hz with hz | hz
        · have := hins.2 z hz
          rw [hep, hanchor] at this
          exact this
        · obtain ⟨p, r, hpr, hzp⟩ := star_le_head hσn hσl' hz
          refine lt_of_le_of_lt hzp (lt_of_le_of_lt ?_ hσep)
          rw [hpr]; exact le_valS_head
    · exfalso
      rw [val_eta'Of, if_neg hins, hη0] at hση
      simp at hση
  · -- the same run: `η_a = η_{(k,H)} + 1`
    have hD : dOf k c = dOf k (H.getLast hHne) :=
      eq_of_valS_eq (monOf_spec k c).2.1 (monOf_spec k _).2.1 hDeq
    have hj : jOf k (H ++ [c]) = jOf k H := by
      rw [jOf, jOf, List.map_append, List.map_singleton, hD]
      have := runStart_append_last (ds := H.map (dOf k)) (by simpa using hHne)
      rw [List.getLast_map] at this
      exact this
    have hjle : jOf k H ≤ H.length := by
      have := runStart_le_length (H.map (dOf k)); simpa using this
    have hep : epOf k (H ++ [c]) = epOf k H := by
      rw [epOf, epOf, hj, List.take_append_of_le_length hjle]
    have hΔ' : deltaOf k (H ++ [c]) = deltaOf k H := by rw [hΔ, hdH, hD]
    have hins : insOf k (H ++ [c]) ↔ insOf k H := by
      unfold insOf; rw [hj, hΔ', hep]
    have hcc : cOf k (H ++ [c]) = addS (cOf k H) [one] := by
      rw [cOf, cOf, hj, List.drop_append_of_le_length hjle, List.map_append,
        List.map_singleton, addAll_append_single, hwc]
    have hη1 : WP.valS (etaOf k (H ++ [c])) = WP.valS (etaOf k H) + 1 := by
      rw [etaOf, etaOf, hcc, minusOnePlus_addS_eq_of_ne (cOf_spec k H).1 (cOf_ne_nil hHne)
        nfp_one, val_one]
    have hη'1 : WP.valS (eta'Of k (H ++ [c])) = WP.valS (eta'Of k H) + 1 := by
      rw [val_eta'Of, val_eta'Of, hη1, ← add_assoc]
      by_cases hi : insOf k H
      · rw [if_pos (hins.mpr hi), if_pos hi, hep]
      · rw [if_neg (fun h => hi (hins.mp h)), if_neg hi]
    have hσle : WP.valS σ ≤ WP.valS (eta'Of k H) := by
      rw [hη'1] at hση; exact Order.lt_add_one_iff.mp hση
    have hn2 : NFP (WP.th k (deltaOf k H ++ eta'Of k H)) := by
      rw [← argOf_eq hHne hlH]; exact hnanc
    rw [hΔ'] at hβn ⊢
    rw [argOf_eq hHne hlH]
    exact inc_le hβn hn2 hσl' (eta'Of_spec k H).2 hσle

/-! ## The `D`-part of the log -/

/-- The part of level `≥ m` is determined by the value, when the rest is below
`Ω_m`. -/
theorem d_eq_of_split {m : ℕ} {D D' : List WP} (hD : NFS D) (hD' : NFS D')
    (hl : ∀ q ∈ D, m ≤ q.lvl) (hl' : ∀ q ∈ D', m ≤ q.lvl) {r r' : Ordinal.{0}}
    (hr : r < Om m) (hr' : r' < Om m) (h : WP.valS D + r = WP.valS D' + r') : D = D' := by
  refine eq_of_valS_eq hD hD' (le_antisymm ?_ ?_)
  · by_contra hc
    have := gap_of_lt hD hD' hl hl' (not_le.mp hc)
    have h2 : WP.valS D' + r' < WP.valS D' + Om m := (add_lt_add_iff_left _).mpr hr'
    exact absurd h (ne_of_gt (lt_of_lt_of_le h2 (le_trans this le_self_add)))
  · by_contra hc
    have := gap_of_lt hD' hD hl' hl (not_le.mp hc)
    have h2 : WP.valS D + r < WP.valS D + Om m := (add_lt_add_iff_left _).mpr hr
    exact absurd h.symm (ne_of_gt (lt_of_lt_of_le h2 (le_trans this le_self_add)))

theorem val_log_append_lo {k : ℕ} {cs : List Tm} {x : Tm} (hx : x.y ≤ k + 1) :
    WP.valS (logOmega (trTm (.node (k + 1) (cs ++ [x])))) = WP.valS (zPre (k + 1) cs) + (trTm x).val := by
  have h1 := val_log_trTm (.node (k + 1) (cs ++ [x]))
  rw [val_trTm_append_lo hx] at h1
  exact le_antisymm ((opow_le_opow_iff_right one_lt_omega0).mp h1.le)
    ((opow_le_opow_iff_right one_lt_omega0).mp h1.ge)

/-- **The `D`-part does not see a change of the last child below level
`k + 1`.** -/
theorem dOf_lo_eq {k : ℕ} {cs : List Tm} {x x' : Tm} (hx : x.y ≤ k) (hx' : x'.y ≤ k) :
    dOf k (.node (k + 1) (cs ++ [x])) = dOf k (.node (k + 1) (cs ++ [x'])) := by
  have hW := zPre_nfs (k + 1) cs
  obtain ⟨hWs, hWD, hWρ, hWDl, hWρl⟩ := splitLevel_spec hW (k + 1)
  have key : ∀ y : Tm, y.y ≤ k → dOf k (.node (k + 1) (cs ++ [y])) = (splitLevel (zPre (k + 1) cs) (k + 1)).1 := by
    intro y hy
    obtain ⟨-, h2, -, h4, -⟩ := monOf_spec k (.node (k + 1) (cs ++ [y]))
    have hv := val_log_append_lo (k := k) (cs := cs) (x := y) (by omega)
    rw [valS_log_eq k, hWs, valS_append, add_assoc] at hv
    refine d_eq_of_split h2 hWD (fun q hq => (h4 q hq).1) hWDl (valS_rho_lt k _) ?_ hv
    exact (Om_isPrincipal (k + 1)) (valS_lt_Om hWρ (fun q hq => Nat.lt_succ_iff.mp (hWρl q hq)))
      (val_trTm_lt_Om y |> fun h => lt_of_lt_of_le h (Om_strictMono.monotone (by omega)))
  rw [key x hx, key x' hx']

end Googology.Trans.PSS.TR

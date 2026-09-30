import Googology.Trans.BMS.PoR.PSS.TR.Blocks

/-!
# Theorem Cof

`proof/TR-2.md` §4b: for a standard `M` whose last column is not `(0,0)`,
`sup_n val 𝒯(M[n]) = val 𝒯(M)`.  Here it is stated for a single root `t` with
children, which is the case the proof of TR uses (a sum reduces to its last
root by continuity of the ordinal sum).

The proof (§4b.4): write `t` as its rightmost path (`TR/Spine.lean`) and compute
`M[n]` on terms (`TR/FundSeq.lean`).  Start from a base, propagate `LC` up the
path by P-lo and P-hi (`path_step`), and at the root turn `LC_True(t)` into the
ordinal equality by (Seg) (`cof_of_lc`).

* Case `i₁ = 1` (`cof_case1`): (Bℓ), then the region between `j₀` and `ℓ` with
  the bound `B_m`, then (B j₀) (`base_C1`, or P-hi with `B_m` on the
  arguments), then up to the root with `B = True`.
* Case `i₁ = 0` (`cof_case0`): if `j₀` is the root, `𝒯(t) = 𝒯(t⁻)·ω` directly;
  otherwise (B dup) at the parent of `j₀`, then up to the root.

`nodeOf M` is the node (list of root terms) whose matrix is `M`.
-/

namespace Googology.Trans.PSS.TR

open Forest Phi Ordinal
open Bijectivity (CTPS ltPS)
open _root_.PSS (oper Lng)

open Classical in
/-- The node (list of root terms) of a standard matrix `M`: the `S` with
`mat S = M`. -/
noncomputable def nodeOf (M : PS) : List Tm :=
  if h : ∃ S, StdOrd S ∧ mat S = M then h.choose else []

/-- `mat` is injective. -/
theorem mat_inj {S S' : List Tm} (h : mat S = mat S') : S = S' := by
  rcases list_lt_trichotomy S S' with h' | h' | h'
  · exact absurd ((mat_lt_iff S S').mpr h') (by rw [h]; exact Bijectivity.ltPS_irrefl _)
  · exact h'
  · exact absurd ((mat_lt_iff S' S).mpr h') (by rw [h]; exact Bijectivity.ltPS_irrefl _)

theorem nodeOf_mat {S : List Tm} (hS : StdOrd S) : nodeOf (mat S) = S := by
  have h : ∃ S', StdOrd S' ∧ mat S' = mat S := ⟨S, hS, rfl⟩
  rw [nodeOf, dif_pos h]
  exact mat_inj h.choose_spec.2

theorem nodeOf_spec {M : PS} (hM : CTPS M) : StdOrd (nodeOf M) ∧ mat (nodeOf M) = M := by
  obtain ⟨S, hS, rfl⟩ := exists_mat_eq hM
  rw [nodeOf_mat hS]
  exact ⟨hS, rfl⟩

theorem mat_single' (t : Tm) : mat [t] = t.cols := by rw [mat_cons, mat_nil, List.append_nil]

theorem one_lt_Lng_of_cs {t : Tm} (hne : t.cs ≠ []) : 1 < Lng t.cols := by
  obtain ⟨c, cs, hc⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨y, cs'⟩ := t
  simp only [Tm.cs_node] at hc
  subst hc
  rw [Lng, Tm.cols_eq, mat_cons]
  obtain ⟨r, hr⟩ := c.cols_head
  simp [hr, shUp]

/-! ## From `LC_True` at the root to Cof -/

theorem cof_of_lc {t : Tm} (ht : Std t) (hne : t.cs ≠ []) (T : ℕ → Tm)
    (hT : ∀ n, oper t.cols (n + 2) = (T n).cols) (hLC : LC 0 (fun _ => True) t T) :
    (trTm t).val = ⨆ n : ℕ, WP.valS (trNode (nodeOf (oper t.cols (n + 1)))) := by
  have hL := one_lt_Lng_of_cs hne
  refine le_antisymm ?_ (Ordinal.iSup_le fun n => ?_)
  · refine le_of_forall_lt fun β hβ => ?_
    have ht0 : t.y = 0 := ((std_iff t).mp ht).1
    have h1 : WP.valS [trTm t] < Om 1 := by
      rw [valS_single]; have := val_trTm_lt_Om t; rwa [ht0] at this
    obtain ⟨u, hu, rfl⟩ := seg (NFS.single (trTm_nfp t)) h1 (by rw [valS_single]; exact hβ)
    obtain ⟨n0, h0⟩ := hLC u hu hβ (Bm.top 0 u)
    have hC : CTPS (T n0).cols := by rw [← hT n0]; exact Bijectivity.ctps_oper ht (by omega)
    have hSn : nodeOf (oper t.cols (n0 + 1 + 1)) = [T n0] := by
      rw [hT n0, ← mat_single']; exact nodeOf_mat (stdOrd_single hC)
    refine lt_of_lt_of_le (h0 n0 le_rfl) (le_trans ?_ (Ordinal.le_iSup _ (n0 + 1)))
    rw [hSn, valS_trNode]; simp
  · have hC : CTPS (oper t.cols (n + 1)) := Bijectivity.ctps_oper ht (by omega)
    obtain ⟨hS, hSm⟩ := nodeOf_spec hC
    have hlt : nodeOf (oper t.cols (n + 1)) < [t] := by
      rw [← mat_lt_iff, hSm, mat_single']
      exact Bijectivity.oper_ltPS hL (n + 1) (by omega)
    have := mono_node hS (stdOrd_single ht) hlt
    rw [valS_trNode [t]] at this
    simpa using this.le

/-! ## Path nodes -/

theorem rebuild_drop_eq {sp : Spine} {h : ℕ} (hh : h < sp.length) (u : Tm) :
    rebuild (sp.drop h) u = .node (sp[h]).1 ((sp[h]).2 ++ [rebuild (sp.drop (h + 1)) u]) := by
  rw [List.drop_eq_getElem_cons hh]; rfl

theorem valid_rebuild_drop {sp : Spine} {u : Tm} (hv : Valid (rebuild sp u)) :
    ∀ h ≤ sp.length, Valid (rebuild (sp.drop h) u) := by
  intro h
  induction h with
  | zero => intro _; simpa using hv
  | succ h ih =>
    intro hh
    have := ih (by omega)
    rw [rebuild_drop_eq (by omega)] at this
    exact this.child (by simp)

theorem rebuild_y {sp : Spine} {h : ℕ} (hh : h < sp.length) (u : Tm) :
    (rebuild (sp.drop h) u).y = (sp[h]).1 := by
  rw [rebuild_drop_eq hh]; rfl

theorem PosRel.of_cols {c cn : Tm} {R : PS} {q q' : ℕ × ℕ} {Q : PS} (hc : c.cols = R ++ [q])
    (hcn : cn.cols = R ++ q' :: Q) (h : PLt q' q) : PosRel c cn :=
  ⟨R, q, q' :: Q, hc, hcn, by simp, fun p hp => by
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hp; rw [← hp]; exact h⟩

/-- Replacing the bottom leaf `(y_ℓ)` by a term `u` with a smaller root. -/
theorem posRel_rebuild_leaf {yl : ℕ} {u : Tm} (hu : u.y < yl) (sp' : Spine) :
    PosRel (rebuild sp' (.node yl [])) (rebuild sp' u) := by
  have h0 : PosRel (.node yl []) u := by
    obtain ⟨r, hr⟩ := u.cols_head
    refine PosRel.of_cols (R := []) (q := (0, yl)) (q' := (0, u.y)) (Q := r) ?_ ?_ ?_
    · rw [leaf_cols]; rfl
    · rw [hr]; rfl
    · unfold PLt; simp; omega
  exact h0.rebuild sp'

theorem rmT_y {sp : Spine} (hne : sp ≠ []) : (rmT sp).y = (sp.head hne).1 := by
  match sp, hne with
  | [(y, cs)], _ => rfl
  | (y, cs) :: e :: sp, _ => rfl

theorem j0T_y {sp : Spine} {i : ℕ} (hi : i < sp.length) (n : ℕ) : (j0T sp i n).y = (sp[i]).1 := by
  cases n with
  | zero =>
    rw [j0T, rmT_y (by simp; omega)]
    simp [List.head_drop]
  | succ n => rw [j0T, rebuild_y hi]

theorem j0T_prefix (sp : Spine) (i : ℕ) (hi : i < sp.length) :
    ∀ n, (j0T sp i n).cols <+: (j0T sp i (n + 1)).cols
  | 0 => by
    rw [j0T, j0T, rebuild_cols, rmT_cols (by simp; omega)]
    exact List.prefix_append _ _
  | n + 1 => by
    rw [j0T, j0T, rebuild_cols, rebuild_cols]
    exact (List.prefix_append_right_inj _).mpr (List.IsPrefix.map _ (j0T_prefix sp i hi n))

/-- The case `i₁ = 1` of Theorem Cof. -/
theorem cof_case1 {sp : Spine} {yl : ℕ} (ht : Std (rebuild sp (.node yl []))) (hsp : sp ≠ [])
    (hyl : 0 < yl) (hne : (rebuild sp (.node yl [])).cs ≠ []) :
    (trTm (rebuild sp (.node yl []))).val =
      ⨆ n : ℕ, WP.valS (trNode (nodeOf (oper (rebuild sp (.node yl [])).cols (n + 1)))) := by
  obtain ⟨i, hi, hyi, hmin, hoper⟩ := oper_case1 ht hsp hyl
  set d := sp.length with hd
  set m := (sp[i]).1 with hm
  set X := j0T sp i with hX
  set a : ℕ → Tm := fun h => rebuild (sp.drop h) (.node yl []) with ha
  set an : ℕ → ℕ → Tm := fun h n => rebuild (sp.drop h) (X n) with han
  have ha0 : a 0 = rebuild sp (.node yl []) := by simp [ha]
  have had : a d = .node yl [] := by simp [ha, hd]
  have hand : ∀ n, an d n = X n := fun n => by simp [han, hd]
  have hT : ∀ n, oper (rebuild sp (.node yl [])).cols (n + 2) = (an 0 n).cols := by
    intro n
    rw [hoper (n + 1)]
    congr 1
    show rebuild (sp.take i) (rebuild (sp.drop i) (X n)) = rebuild (sp.drop 0) (X n)
    rw [← rebuild_append, List.take_append_drop, List.drop_zero]
  have hvT : ∀ n, Valid (an 0 n) := fun n => by
    have hC : CTPS (an 0 n).cols := by rw [← hT n]; exact Bijectivity.ctps_oper ht (by omega)
    exact valid_of_std hC
  have hva : ∀ h ≤ d, Valid (a h) := valid_rebuild_drop (valid_of_std ht)
  have hvan : ∀ n, ∀ h ≤ d, Valid (an h n) := fun n h hh => by
    have := valid_rebuild_drop (by simpa [han] using hvT n) h hh
    simpa [han] using this
  have hXy : ∀ n, (X n).y = m := fun n => j0T_y hi n
  have hXv : ∀ n, Valid (X n) := fun n => by rw [← hand]; exact hvan n d le_rfl
  have hXmono : ∀ n, (trTm (X n)).val ≤ (trTm (X (n + 1))).val := fun n =>
    mono_le (hXv n) (hXv (n + 1)) (lePS_of_prefix (j0T_prefix sp i hi n))
  have hshape : ∀ h (hh : h < d), a h = .node (sp[h]).1 ((sp[h]).2 ++ [a (h + 1)]) :=
    fun h hh => rebuild_drop_eq hh _
  have hshapen : ∀ h (hh : h < d) n, an h n = .node (sp[h]).1 ((sp[h]).2 ++ [an (h + 1) n]) :=
    fun h hh n => rebuild_drop_eq hh _
  have hay : ∀ h (hh : h < d), (a h).y = (sp[h]).1 := fun h hh => rebuild_y hh _
  have hany : ∀ h (hh : h < d) n, (an h n).y = (sp[h]).1 := fun h hh n => rebuild_y hh _
  -- the step-down: `y_ℓ = m + 1`
  have hym : yl = m + 1 := by
    have hvi := hva i hi.le
    rw [hshape i hi] at hvi
    have h1 := hvi.y_le (c := a (i + 1)) (by simp)
    rcases Nat.lt_or_ge (i + 1) d with hlt | hge
    · rw [hay (i + 1) hlt] at h1
      have := hmin (i + 1) hlt (by omega)
      omega
    · have : i + 1 = d := by omega
      rw [this, had] at h1
      simp at h1; omega
  have hyrel : ∀ h ≤ d, ∀ n, (an h n).y ≤ (a h).y := by
    intro h hh n
    rcases Nat.lt_or_ge h d with hlt | hge
    · rw [hany h hlt, hay h hlt]
    · have : h = d := by omega
      subst this
      rw [hand, had, hXy]; simp; omega
  have hpos : ∀ h ≤ d, ∀ n, PosRel (a h) (an h n) := fun h _ n =>
    posRel_rebuild_leaf (by rw [hXy]; omega) (sp.drop h)
  set Pm : WP → Prop := fun s => ∃ n, s.val < (trTm (X n)).val with hPm
  have hX1 : Om m < (trTm (X 1)).val := by
    have hv1 := hXv 1
    rw [show X 1 = rebuild (sp.drop i) (X 0) from rfl, rebuild_drop_eq hi] at hv1 ⊢
    exact Om_lt_val_trTm hv1 (by simp)
  have hP1 : Pm one := ⟨1, by rw [val_one]; exact lt_of_le_of_lt (one_le_Om m) hX1⟩
  have hPo : Pm (om m) := ⟨1, by rw [val_om]; exact hX1⟩
  -- the generic step at a path node `h < d`
  have step : ∀ (mm : ℕ) (P : WP → Prop), P one → P (om mm) → ∀ h (hh : h + 1 < d ∨ h + 1 = d),
      mm ≤ (sp[h]'(by omega)).1 →
      ((a (h + 1)).y = (sp[h]'(by omega)).1 + 1 → h + 1 < d) →
      LC mm P (a (h + 1)) (an (h + 1)) → LC mm P (a h) (an h) := by
    intro mm P hP1' hPo' h hh hmk hc1 hLC
    have hhd : h < d := by omega
    have e1 : a h = .node (sp[h]).1 ((sp[h]).2 ++ [a (h + 1)]) := hshape h hhd
    have e2 : an h = fun n => .node (sp[h]).1 ((sp[h]).2 ++ [an (h + 1) n]) :=
      funext (hshapen h hhd)
    rw [e1, e2]
    refine path_step hP1' hPo' hmk (by rw [← e1]; exact hva h hhd.le)
      (fun n => by rw [← hshapen h hhd n]; exact hvan n h hhd.le) (fun hc n => ?_) (fun hc n => ?_)
      (fun n => hpos (h + 1) (by omega) n) (fun hc => ?_) hLC
    · have h1 := hc1 hc
      rw [hany (h + 1) h1 n, ← hay (h + 1) h1, hc]
    · exact le_trans (hyrel (h + 1) (by omega) n) hc
    · have h1 := hc1 hc
      have ec : a (h + 1) = .node ((sp[h]).1 + 1) ((sp[h + 1]).2 ++ [a (h + 2)]) := by
        rw [hshape (h + 1) h1, ← hay (h + 1) h1, hc]
      have ecn : ∀ n, an (h + 1) n =
          .node ((sp[h]).1 + 1) ((sp[h + 1]).2 ++ [an (h + 2) n]) := fun n => by
        rw [hshapen (h + 1) h1 n, ← hay (h + 1) h1, hc]
      by_cases hy2 : (a (h + 2)).y ≤ (sp[h]).1
      · left
        intro n
        rw [ecn n, ec]
        exact dOf_lo_eq (le_trans (hyrel (h + 2) (by omega) n) hy2) hy2
      · right
        have hv1 := hva (h + 1) (by omega)
        rw [ec] at hv1 ⊢
        exact rhoOf_eq_nil_of_hi hv1 (by omega)
  -- the region between `j₀` and `ℓ`, with `B_m`
  have regS : ∀ e, e ≤ d - (i + 1) → LC m Pm (a (d - e)) (an (d - e)) := by
    intro e
    induction e with
    | zero =>
      intro _
      rw [Nat.sub_zero, had, hym, show an d = X from funext hand]
      exact base_ell hXy hXmono
    | succ e ih =>
      intro he
      have hh : d - (e + 1) + 1 = d - e := by omega
      have hlt : d - (e + 1) + 1 < d ∨ d - (e + 1) + 1 = d := by omega
      have hyh : yl ≤ (sp[d - (e + 1)]'(by omega)).1 := hmin _ (by omega) (by omega)
      refine step m Pm hP1 hPo (d - (e + 1)) hlt (by omega) (fun hc => ?_)
        (by rw [hh]; exact ih (by omega))
      by_contra hc'
      have : d - (e + 1) + 1 = d := by omega
      rw [this, had] at hc
      simp at hc; omega
  -- the base `(B j₀)`
  have base : LC 0 (fun _ => True) (a i) (an i) := by
    rcases Nat.lt_or_ge (i + 1) d with hlt | hge
    · -- `j₀`'s path child is not `ℓ`: P-hi with `B_m` on the arguments
      have hc : (a (i + 1)).y = m + 1 := by
        have hvi := hva i hi.le
        rw [hshape i hi] at hvi
        have h1 := hvi.y_le (c := a (i + 1)) (by simp)
        have h2 := hmin (i + 1) hlt (by omega)
        rw [hay (i + 1) hlt] at h1 ⊢
        omega
      have hcn : ∀ n, (an (i + 1) n).y = m + 1 := fun n => by
        rw [hany (i + 1) hlt n, ← hay (i + 1) hlt, hc]
      have e1 : a i = .node m ((sp[i]).2 ++ [a (i + 1)]) := hshape i hi
      have e2 : an i = fun n => .node m ((sp[i]).2 ++ [an (i + 1) n]) := funext (hshapen i hi)
      have hvi := hva i hi.le
      rw [e1] at hvi
      have hne' : (sp[i]).2 ++ [a (i + 1)] ≠ [] := by simp
      have hl' : (((sp[i]).2 ++ [a (i + 1)]).getLast hne').y = m + 1 := by simpa using hc
      have hall := hvi.eps_all hne' hl'
      have hvc := hva (i + 1) (by omega)
      have hvcn : ∀ n, Valid (an (i + 1) n) := fun n => hvan n (i + 1) (by omega)
      have hvn : ∀ n, Valid (.node m ((sp[i]).2 ++ [an (i + 1) n])) := fun n => by
        rw [← hshapen i hi n]; exact hvan n i hi.le
      rw [e1, e2]
      refine eps_lc hP1 hPo (Nat.zero_le m) hc hcn (fun h hh => hall h (by simp [hh]))
        (fun n => mono (hvcn n) hvc (hpos (i + 1) (by omega) n).lt) (Or.inr ?_) (fun hHne => ?_)
        (fun n => ?_) (lcx_of_lc le_rfl hc hcn (by
          have := regS (d - (i + 1)) le_rfl
          rwa [show d - (d - (i + 1)) = i + 1 by omega] at this))
        (fun n => wit_bound hvi hne' hl' (hvn n) (by simp) (by simpa using hcn n)
          ((hpos (i + 1) (by omega) n).up m _))
        (fun β _ _ hsIH s hs => ?_)
      · have ec : a (i + 1) = .node (m + 1) ((sp[i + 1]).2 ++ [a (i + 2)]) := by
          rw [hshape (i + 1) hlt, ← hay (i + 1) hlt, hc]
        have hv1 := hvc
        rw [ec] at hv1 ⊢
        refine rhoOf_eq_nil_of_hi hv1 ?_
        rcases Nat.lt_or_ge (i + 2) d with h2 | h2
        · rw [hay (i + 2) h2]; have := hmin (i + 2) h2 (by omega); omega
        · have : i + 2 = d := by omega
          rw [this, had]; simp; omega
      · exact mono_le hvc (hvi.child (by simp [List.getLast_mem hHne]))
          ((List.pairwise_append.mp hvi.desc).2.2 _ (List.getLast_mem hHne) _ (by simp))
      · have hvcs : Valid (.node m (sp[i]).2) := by
          have := (hvn n).take (sp[i]).2.length; rwa [List.take_left] at this
        exact mono hvcs (hvn n)
          ((Tm.node_lt_node_iff _ _ _ _).mpr (Or.inr ⟨rfl, lt_of_prefix (by simp)⟩))
      · obtain ⟨n0, h0⟩ := hsIH s hs
        refine ⟨n0 + 1, ?_⟩
        have := h0 n0 le_rfl
        rwa [← hshapen i hi n0] at this
    · -- `ℓ` is a child of `j₀`
      have hid : i + 1 = d := by omega
      have hdrop : sp.drop i = [sp[i]] := by
        rw [List.drop_eq_getElem_cons hi]
        simp [List.drop_eq_nil_of_le (show sp.length ≤ i + 1 by omega)]
      have hXc : ∀ n, X n = c1seq m (sp[i]).2 n := by
        intro n
        induction n with
        | zero => rw [hX, j0T, hdrop]; rfl
        | succ n ih => rw [hX, j0T, hdrop, ← hX, ih]; rfl
      have e1 : a i = .node m ((sp[i]).2 ++ [.node (m + 1) []]) := by
        rw [hshape i hi, hid, had, hym]
      have e2 : an i = fun n => c1seq m (sp[i]).2 (n + 1) := by
        funext n
        rw [hshapen i hi n, hid, hand, hXc]; rfl
      rw [e1, e2]
      exact base_C1 (by rw [← e1]; exact hva i hi.le) (fun n => by rw [← hXc]; exact hXv n)
  -- up to the root, with `B = True`
  have regA : ∀ e, e ≤ i → LC 0 (fun _ => True) (a (i - e)) (an (i - e)) := by
    intro e
    induction e with
    | zero => intro _; simpa using base
    | succ e ih =>
      intro he
      have hh : i - (e + 1) + 1 = i - e := by omega
      refine step 0 (fun _ => True) trivial trivial (i - (e + 1)) (by omega) (Nat.zero_le _)
        (fun _ => by omega) (by rw [hh]; exact ih (by omega))
  have hroot := regA i le_rfl
  rw [Nat.sub_self, ha0] at hroot
  exact cof_of_lc ht hne (an 0) hT (by simpa [han] using hroot)

/-! ## The case `i₁ = 0` -/

theorem val_log_rep {k : ℕ} {cs : List Tm} {x : Tm} (hx : x.y ≤ k + 1) {r : ℕ} (hr : 0 < r) :
    WP.valS (logOmega (trTm (.node (k + 1) (cs ++ List.replicate r x)))) =
      WP.valS (zPre (k + 1) cs) + (trTm x).val * r := by
  have h1 := val_log_trTm (.node (k + 1) (cs ++ List.replicate r x))
  rw [val_trTm_rep hx hr] at h1
  exact le_antisymm ((opow_le_opow_iff_right one_lt_omega0).mp h1.le)
    ((opow_le_opow_iff_right one_lt_omega0).mp h1.ge)

/-- The `D`-part does not see repeated last children below level `k + 1`. -/
theorem dOf_rep_eq {k : ℕ} {cs : List Tm} {x x' : Tm} (hx : x.y ≤ k) (hx' : x'.y ≤ k) {r : ℕ}
    (hr : 0 < r) :
    dOf k (.node (k + 1) (cs ++ List.replicate r x')) = dOf k (.node (k + 1) (cs ++ [x])) := by
  have hW := zPre_nfs (k + 1) cs
  obtain ⟨hWs, hWD, hWρ, hWDl, hWρl⟩ := splitLevel_spec hW (k + 1)
  have hρW : WP.valS (splitLevel (zPre (k + 1) cs) (k + 1)).2 < Om (k + 1) :=
    valS_lt_Om hWρ (fun q hq => Nat.lt_succ_iff.mp (hWρl q hq))
  have hvlt : ∀ y : Tm, y.y ≤ k → (trTm y).val < Om (k + 1) := fun y hy =>
    lt_of_lt_of_le (val_trTm_lt_Om y) (Om_strictMono.monotone (by omega))
  have key1 : dOf k (.node (k + 1) (cs ++ [x])) = (splitLevel (zPre (k + 1) cs) (k + 1)).1 := by
    obtain ⟨-, h2, -, h4, -⟩ := monOf_spec k (.node (k + 1) (cs ++ [x]))
    have hv := val_log_append_lo (k := k) (cs := cs) (x := x) (by omega)
    rw [valS_log_eq k, hWs, valS_append, add_assoc] at hv
    exact d_eq_of_split h2 hWD (fun q hq => (h4 q hq).1) hWDl (valS_rho_lt k _)
      ((Om_isPrincipal (k + 1)) hρW (hvlt x hx)) hv
  have key2 : dOf k (.node (k + 1) (cs ++ List.replicate r x')) =
      (splitLevel (zPre (k + 1) cs) (k + 1)).1 := by
    obtain ⟨-, h2, -, h4, -⟩ := monOf_spec k (.node (k + 1) (cs ++ List.replicate r x'))
    have hv := val_log_rep (k := k) (cs := cs) (x := x') (by omega) hr
    rw [valS_log_eq k, hWs, valS_append, add_assoc] at hv
    exact d_eq_of_split h2 hWD (fun q hq => (h4 q hq).1) hWDl (valS_rho_lt k _)
      ((Om_isPrincipal (k + 1)) hρW ((Om_isPrincipal (k + 1)).mul_natCast_lt (hvlt x' hx') r)) hv
  rw [key1, key2]

theorem posRel_dup {y yj : ℕ} {cs csj L : List Tm} (hL : L ≠ []) :
    PosRel (.node y (cs ++ [.node yj (csj ++ [.node 0 []])])) (.node y (cs ++ .node yj csj :: L)) := by
  obtain ⟨x, L', rfl⟩ := List.exists_cons_of_ne_nil hL
  obtain ⟨r, hr⟩ := x.cols_head
  refine PosRel.of_cols (R := (0, y) :: shUp 1 (mat cs ++ (Tm.node yj csj).cols)) (q := (2, 0))
    (q' := (1, x.y)) (Q := shUp 1 (r ++ mat L')) ?_ ?_ ?_
  · rw [Tm.cols_eq, Tm.cols_eq, mat_append, mat_cons, mat_nil, List.append_nil, Tm.cols_eq,
      mat_append, mat_cons, mat_nil, List.append_nil, leaf_cols]
    simp [shUp, List.map_append]
  · rw [Tm.cols_eq, mat_append, mat_cons, mat_cons, hr]
    simp [shUp, List.map_append]
  · unfold PLt; simp

theorem valS_trNode_replicate (x : Tm) (r : ℕ) :
    WP.valS (trNode (List.replicate r x)) = (trTm x).val * r := by
  rw [valS_trNode, List.map_replicate, sum_replicate_ord]

/-- The case `i₁ = 0` of Theorem Cof. -/
theorem cof_case0 {sp : Spine} (ht : Std (rebuild sp (.node 0 []))) (hsp : sp ≠ [])
    (hne : (rebuild sp (.node 0 [])).cs ≠ []) :
    (trTm (rebuild sp (.node 0 []))).val =
      ⨆ n : ℕ, WP.valS (trNode (nodeOf (oper (rebuild sp (.node 0 [])).cols (n + 1)))) := by
  have hoper := oper_case0 ht hsp rfl
  set d := sp.length with hd
  have hd1 : 1 ≤ d := List.length_pos_of_ne_nil hsp
  have hgl : sp.getLast? = some (sp[d - 1]'(by omega)) := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
  set j0m : Tm := .node (sp[d - 1]'(by omega)).1 (sp[d - 1]'(by omega)).2 with hj0m
  have hdup : ∀ n, dupNode sp n = if d = 1 then List.replicate n j0m else
      [rebuild (sp.take (d - 2)) (.node (sp[d - 2]'(by omega) |>.1)
        ((sp[d - 2]'(by omega)).2 ++ List.replicate n j0m))] := by
    intro n
    rw [dupNode]
    simp only [hgl, Option.map_some, Option.getD_some, ← hd]
    split_ifs with h1
    · rfl
    · rw [List.getElem?_eq_getElem (by omega)]; rfl
  have hva : ∀ h ≤ d, Valid (rebuild (sp.drop h) (.node 0 [])) :=
    valid_rebuild_drop (valid_of_std ht)
  have hj0 : rebuild (sp.drop (d - 1)) (.node 0 []) =
      .node (sp[d - 1]'(by omega)).1 ((sp[d - 1]'(by omega)).2 ++ [.node 0 []]) := by
    rw [rebuild_drop_eq (by omega), show d - 1 + 1 = d by omega]
    simp [hd]
  have hvj : Valid (.node (sp[d - 1]'(by omega)).1 ((sp[d - 1]'(by omega)).2 ++ [.node 0 []])) := by
    rw [← hj0]; exact hva (d - 1) (by omega)
  rcases Nat.lt_or_ge d 2 with hd2 | hd2
  · -- `j₀` is the root: `𝒯(t) = 𝒯(t⁻)·ω`
    have hd1' : d = 1 := by omega
    have ht' : rebuild sp (.node 0 []) = rebuild (sp.drop (d - 1)) (.node 0 []) := by
      rw [hd1', Nat.sub_self, List.drop_zero]
    have hS : ∀ n, nodeOf (oper (rebuild sp (.node 0 [])).cols (n + 1)) =
        List.replicate (n + 1) j0m := by
      intro n
      have hC := Bijectivity.ctps_oper ht (n := n + 1) (by omega)
      rw [hoper n, hdup, if_pos hd1'] at hC ⊢
      exact nodeOf_mat (Or.inr hC)
    simp only [hS, valS_trNode_replicate]
    rw [ht', hj0, val_trTm_dup hvj]
    set v := (trTm j0m).val
    refine le_antisymm (le_of_forall_lt fun b hb => ?_) (Ordinal.iSup_le fun n => ?_)
    · obtain ⟨N, hN⟩ := lt_mul_omega0' hb
      refine lt_of_lt_of_le hN (le_trans ?_ (Ordinal.le_iSup _ N))
      exact mul_le_mul_right (by exact_mod_cast Nat.le_succ N) _
    · exact mul_le_mul_right (Ordinal.natCast_lt_omega0 _).le _
  -- `j₀` has a parent `p`: (B dup), then up to the root
  set sp2 := sp.take (d - 2) with hsp2
  have hsp2l : sp2.length = d - 2 := by simp [hsp2]; omega
  set yp := (sp[d - 2]'(by omega)).1 with hyp
  set csp := (sp[d - 2]'(by omega)).2 with hcsp
  set yj := (sp[d - 1]'(by omega)).1 with hyj
  set csj := (sp[d - 1]'(by omega)).2 with hcsj
  set p : Tm := .node yp (csp ++ [.node yj (csj ++ [.node 0 []])]) with hp
  have hpeq : rebuild (sp.drop (d - 2)) (.node 0 []) = p := by
    rw [rebuild_drop_eq (by omega), show d - 2 + 1 = d - 1 by omega, hj0]
  set pn : ℕ → Tm := fun n => .node yp (csp ++ List.replicate (n + 2) j0m) with hpn
  set aa : ℕ → Tm := fun h => rebuild (sp2.drop h) p with haa
  set an : ℕ → ℕ → Tm := fun h n => rebuild (sp2.drop h) (pn n) with han
  have haa0 : aa 0 = rebuild sp (.node 0 []) := by
    simp only [haa, List.drop_zero, hsp2]
    rw [← hpeq, ← rebuild_append, List.take_append_drop]
  have haad : aa (d - 2) = p := by simp [haa, ← hsp2l]
  have hand : ∀ n, an (d - 2) n = pn n := fun n => by simp [han, ← hsp2l]
  have hT : ∀ n, oper (rebuild sp (.node 0 [])).cols (n + 2) = (an 0 n).cols := by
    intro n
    rw [hoper (n + 1), hdup, if_neg (by omega), mat_single']
    rfl
  have hvT : ∀ n, Valid (an 0 n) := fun n => by
    have hC : CTPS (an 0 n).cols := by rw [← hT n]; exact Bijectivity.ctps_oper ht (by omega)
    exact valid_of_std hC
  have hvaa : ∀ h ≤ d - 2, Valid (aa h) := fun h hh => by
    have := valid_rebuild_drop (sp := sp2) (u := p) (by
      rw [show rebuild sp2 p = aa 0 by simp [haa], haa0]; exact valid_of_std ht) h (by omega)
    simpa [haa] using this
  have hvan : ∀ n, ∀ h ≤ d - 2, Valid (an h n) := fun n h hh => by
    have := valid_rebuild_drop (sp := sp2) (u := pn n) (by simpa [han] using hvT n) h (by omega)
    simpa [han] using this
  have hshape : ∀ h (hh : h < d - 2), aa h = .node (sp[h]'(by omega)).1
      ((sp[h]'(by omega)).2 ++ [aa (h + 1)]) := fun h hh => by
    simp only [haa]; rw [rebuild_drop_eq (by omega)]; simp [hsp2]
  have hshapen : ∀ h (hh : h < d - 2) n, an h n = .node (sp[h]'(by omega)).1
      ((sp[h]'(by omega)).2 ++ [an (h + 1) n]) := fun h hh n => by
    simp only [han]; rw [rebuild_drop_eq (by omega)]; simp [hsp2]
  have hy : ∀ h ≤ d - 2, ∀ n, (an h n).y = (aa h).y := by
    intro h hh n
    rcases Nat.lt_or_ge h (d - 2) with hlt | hge
    · rw [hshape h hlt, hshapen h hlt n]; rfl
    · have : h = d - 2 := by omega
      subst this; rw [hand, haad]; rfl
  have hposp : ∀ n, PosRel p (pn n) := fun n => by
    simp only [hp, hpn]
    rw [show List.replicate (n + 2) j0m = j0m :: List.replicate (n + 1) j0m from rfl]
    exact posRel_dup (by simp)
  have hpos : ∀ h ≤ d - 2, ∀ n, PosRel (aa h) (an h n) := fun h _ n => (hposp n).rebuild _
  -- the base at `p`
  have hvp : Valid p := by rw [← haad]; exact hvaa (d - 2) le_rfl
  have hyjle : yj ≤ yp + 1 := hvp.y_le (c := .node yj (csj ++ [.node 0 []])) (by simp)
  have base : LC 0 (fun _ => True) (aa (d - 2)) (an (d - 2)) := by
    rw [haad, show an (d - 2) = pn from funext hand]
    rcases (show yj = yp + 1 ∨ yj ≤ yp by omega) with h1 | h1
    · have hp' : p = .node yp (csp ++ [.node (yp + 1) (csj ++ [.node 0 []])]) := by rw [hp, h1]
      have hpn' : pn = fun n => .node yp (csp ++ List.replicate (n + 2) (.node (yp + 1) csj)) := by
        rw [hpn, hj0m, h1]
      rw [hp', hpn']
      refine bdup_hi (by rw [← hp']; exact hvp) (fun n => ?_)
      have hvp' : Valid (.node yp (csp ++ [.node (yp + 1) (csj ++ [.node 0 []])])) := by
        rw [← hp']; exact hvp
      have hvn : Valid (.node yp (csp ++ List.replicate (n + 2) (.node (yp + 1) csj))) := by
        have := hvan n (d - 2) le_rfl
        rw [hand] at this
        simp only [hpn] at this
        rw [hj0m, h1] at this
        exact this
      refine wit_bound hvp' (by simp) (by simp) hvn (by simp) ?_ ?_
      · rw [List.getLast_append_of_ne_nil _ (by simp), List.getLast_replicate]; rfl
      · rw [show List.replicate (n + 2) (Tm.node (yp + 1) csj) =
          .node (yp + 1) csj :: List.replicate (n + 1) (.node (yp + 1) csj) from rfl]
        exact posRel_dup (by simp)
    · exact bdup_lo h1 hvj
  -- up to the root
  have regA : ∀ e, e ≤ d - 2 → LC 0 (fun _ => True) (aa (d - 2 - e)) (an (d - 2 - e)) := by
    intro e
    induction e with
    | zero => intro _; simpa using base
    | succ e ih =>
      intro he
      set h := d - 2 - (e + 1) with hh
      have hh1 : h + 1 = d - 2 - e := by omega
      have hhd : h < d - 2 := by omega
      have e1 : aa h = .node (sp[h]'(by omega)).1 ((sp[h]'(by omega)).2 ++ [aa (h + 1)]) :=
        hshape h hhd
      have e2 : an h = fun n => .node (sp[h]'(by omega)).1 ((sp[h]'(by omega)).2 ++ [an (h + 1) n]) :=
        funext (hshapen h hhd)
      rw [e1, e2]
      refine path_step trivial trivial (Nat.zero_le _) (by rw [← e1]; exact hvaa h hhd.le)
        (fun n => by rw [← hshapen h hhd n]; exact hvan n h hhd.le)
        (fun hc n => by rw [hy (h + 1) (by omega) n, hc]) (fun hc n => by rw [hy (h + 1) (by omega) n]; exact hc)
        (fun n => hpos (h + 1) (by omega) n) (fun hc => ?_) (by rw [hh1]; exact ih (by omega))
      set k := (sp[h]'(by omega)).1 with hk
      rcases Nat.lt_or_ge (h + 1) (d - 2) with h2 | h2
      · -- a path node above `p`
        have ec : aa (h + 1) = .node (k + 1) ((sp[h + 1]'(by omega)).2 ++ [aa (h + 2)]) := by
          rw [hshape (h + 1) h2]; congr 1; rw [← hc, hshape (h + 1) h2]; rfl
        have ecn : ∀ n, an (h + 1) n = .node (k + 1) ((sp[h + 1]'(by omega)).2 ++ [an (h + 2) n]) :=
          fun n => by
            rw [hshapen (h + 1) h2 n]; congr 1; rw [← hc, hshape (h + 1) h2]; rfl
        by_cases hy2 : (aa (h + 2)).y ≤ k
        · left
          intro n
          rw [ecn n, ec]
          exact dOf_lo_eq (by rw [hy (h + 2) (by omega) n]; exact hy2) hy2
        · right
          have hv1 := hvaa (h + 1) (by omega)
          rw [ec] at hv1 ⊢
          exact rhoOf_eq_nil_of_hi hv1 (by omega)
      · -- the parent `p` of `j₀`
        have hh2 : h + 1 = d - 2 := by omega
        rw [hh2, haad] at hc
        rw [hh2, haad, show an (d - 2) = pn from funext hand]
        have hypk : yp = k + 1 := hc
        by_cases hy2 : yj ≤ k
        · left
          intro n
          have := dOf_rep_eq (k := k) (cs := csp) (x := .node yj (csj ++ [.node 0 []]))
            (x' := j0m) (r := n + 2) hy2 (by rw [hj0m]; exact hy2) (by omega)
          rw [← hypk] at this
          exact this
        · right
          have hv1 : Valid (Tm.node (k + 1) (csp ++ [Tm.node yj (csj ++ [Tm.node 0 []])])) := by
            rw [← hypk]; exact hvp
          have := rhoOf_eq_nil_of_hi hv1 (by simp; omega)
          rw [← hypk] at this
          exact this
  have hroot := regA (d - 2) le_rfl
  rw [Nat.sub_self, haa0] at hroot
  exact cof_of_lc ht hne (an 0) hT (by simpa [han] using hroot)

/-- **Theorem Cof** (`proof/TR-2.md` §4b), for a standard root `t` with children:
`val 𝒯(t) = sup_n val 𝒯(t[n+1])`. -/
theorem cof {t : Tm} (ht : Std t) (hne : t.cs ≠ []) :
    (trTm t).val = ⨆ n : ℕ, WP.valS (trNode (nodeOf (_root_.PSS.oper t.cols (n + 1)))) := by
  obtain ⟨sp, yl, rfl⟩ := exists_spine t
  have hsp : sp ≠ [] := by rintro rfl; exact hne (by simp)
  rcases Nat.eq_zero_or_pos yl with rfl | hyl
  · exact cof_case0 ht hsp hne
  · exact cof_case1 ht hsp hyl hne

end Googology.Trans.PSS.TR

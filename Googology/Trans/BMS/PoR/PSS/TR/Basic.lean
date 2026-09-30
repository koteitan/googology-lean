import Googology.Trans.BMS.PoR.PSS.TR.Cited
import Googology.Trans.BMS.PoR.PSS.TR.Defs

/-!
# Values of `T¹`-terms

From the cited facts (`TR/Cited.lean`) this file proves what the syntactic
operations of `TR/Term.lean` mean on values.

* `Om`: `Ω_m < Ω_{m+1}`, `Ω_m` is additive principal, `ω^x < Ω_{m+1}` for
  `x < Ω_{m+1}`.
* `val_lt_of_lvl_lt`: a principal term of lower level is smaller.
* `eq_of_val_eq`: **terms of `T¹` with equal values are equal**.
* `cmpP_eq`: **the comparison `cmpP` of `tr.py` is the comparison of values**,
  and `cmpS_eq` for sums.
* `addS_spec`, `addAll_spec`: the sum with absorption is the ordinal sum.
* `omegaExp_spec`, `logOmega_spec`: `ω^x` and `log_ω`.
* `trF_nf`: every image of `𝒯` is a principal term of `T¹` of level `y(s)`.
-/

namespace Googology.Trans.PSS.TR

open Ordinal Cardinal Order

/-! ## `Ω` -/

theorem Om_zero : Om 0 = 1 := rfl

theorem Om_succ (m : ℕ) : Om (m + 1) = (ℵ_ ((m + 1 : ℕ) : Ordinal.{0})).ord := rfl

theorem aleph0_le_Om_card (m : ℕ) : ℵ₀ ≤ ℵ_ ((m + 1 : ℕ) : Ordinal.{0}) := aleph0_le_aleph _

theorem omega0_lt_Om_succ (m : ℕ) : ω < Om (m + 1) := by
  rw [Om_succ, omega0_lt_ord, aleph0_lt_aleph]
  exact_mod_cast Nat.succ_pos m

theorem one_lt_Om_succ (m : ℕ) : 1 < Om (m + 1) :=
  lt_trans one_lt_omega0 (omega0_lt_Om_succ m)

theorem Om_lt_Om_succ (m : ℕ) : Om m < Om (m + 1) := by
  cases m with
  | zero => exact one_lt_Om_succ 0
  | succ m =>
    rw [Om_succ, Om_succ, ord_lt_ord, aleph_lt_aleph]
    exact_mod_cast Nat.lt_succ_self (m + 1)

theorem Om_strictMono : StrictMono Om := strictMono_nat_of_lt_succ Om_lt_Om_succ

theorem Om_pos (m : ℕ) : 0 < Om m := by
  cases m with
  | zero => exact zero_lt_one
  | succ m => exact lt_trans zero_lt_one (one_lt_Om_succ m)

theorem one_le_Om (m : ℕ) : 1 ≤ Om m := by
  cases m with
  | zero => exact le_rfl
  | succ m => exact (one_lt_Om_succ m).le

theorem Om_isPrincipal (m : ℕ) : IsPrincipal (· + ·) (Om m) := by
  cases m with
  | zero => exact isPrincipal_add_one
  | succ m => exact isPrincipal_add_ord (aleph0_le_Om_card m)

theorem opow_lt_Om_succ {m : ℕ} {x : Ordinal.{0}} (hx : x < Om (m + 1)) : ω ^ x < Om (m + 1) :=
  isPrincipal_opow_ord (aleph0_le_Om_card m) (omega0_lt_Om_succ m) hx

theorem isSuccLimit_Om_succ (m : ℕ) : IsSuccLimit (Om (m + 1)) :=
  isSuccLimit_ord (aleph0_le_Om_card m)

/-- `Ω_m` is an epsilon number for `m ≥ 1`. -/
theorem opow_Om_succ (m : ℕ) : ω ^ Om (m + 1) = Om (m + 1) := by
  refine le_antisymm ?_ (right_le_opow _ one_lt_omega0)
  rw [opow_le_of_isSuccLimit omega0_ne_zero (isSuccLimit_Om_succ m)]
  exact fun b hb => (opow_lt_Om_succ hb).le

/-! ## Levels and values -/

theorem NFP.of_mem {m : ℕ} {a : List WP} (h : NFP (.th m a)) {q : WP} (hq : q ∈ a) : NFP q := by
  cases h with
  | th hn _ _ => exact hn q hq

theorem NFP.lvl_le {m : ℕ} {a : List WP} (h : NFP (.th m a)) {q : WP} (hq : q ∈ a) :
    q.lvl ≤ m + 1 := by
  cases h with
  | th _ hl _ => exact hl q hq

theorem NFP.desc {m : ℕ} {a : List WP} (h : NFP (.th m a)) :
    a.Pairwise (fun p q => q.val ≤ p.val) := by
  cases h with
  | th _ _ hd => exact hd

theorem NFP.nfs {m : ℕ} {a : List WP} (h : NFP (.th m a)) : NFS a :=
  ⟨fun _ hq => h.of_mem hq, h.desc⟩

theorem NFS.nil : NFS [] := ⟨by simp, List.Pairwise.nil⟩

theorem NFS.cons_iff {p : WP} {l : List WP} :
    NFS (p :: l) ↔ NFP p ∧ (∀ q ∈ l, q.val ≤ p.val) ∧ NFS l := by
  unfold NFS
  simp only [List.mem_cons, forall_eq_or_imp, List.pairwise_cons]
  tauto

theorem NFS.of_cons {p : WP} {l : List WP} (h : NFS (p :: l)) : NFS l :=
  (NFS.cons_iff.mp h).2.2

theorem NFS.head {p : WP} {l : List WP} (h : NFS (p :: l)) : NFP p :=
  (NFS.cons_iff.mp h).1

theorem NFS.le_head {p : WP} {l : List WP} (h : NFS (p :: l)) : ∀ q ∈ l, q.val ≤ p.val :=
  (NFS.cons_iff.mp h).2.1

theorem NFS.single {p : WP} (h : NFP p) : NFS [p] :=
  NFS.cons_iff.mpr ⟨h, by simp, NFS.nil⟩

theorem val_pos {p : WP} (hp : NFP p) : 0 < p.val :=
  lt_of_lt_of_le (Om_pos _) (val_level hp).1

theorem val_lt_of_lvl_lt {p q : WP} (hp : NFP p) (hq : NFP q) (h : p.lvl < q.lvl) :
    p.val < q.val :=
  calc p.val < Om (p.lvl + 1) := (val_level hp).2
    _ ≤ Om q.lvl := Om_strictMono.monotone h
    _ ≤ q.val := (val_level hq).1

theorem lvl_le_of_val_le {p q : WP} (hp : NFP p) (hq : NFP q) (h : p.val ≤ q.val) :
    p.lvl ≤ q.lvl := by
  by_contra h'
  exact absurd h (not_le.mpr (val_lt_of_lvl_lt hq hp (by omega)))

theorem lvl_eq_of_val_eq {p q : WP} (hp : NFP p) (hq : NFP q) (h : p.val = q.val) :
    p.lvl = q.lvl :=
  le_antisymm (lvl_le_of_val_le hp hq h.le) (lvl_le_of_val_le hq hp h.ge)

theorem val_lt_Om_of_lvl_lt {p : WP} (hp : NFP p) {m : ℕ} (h : p.lvl < m) : p.val < Om m :=
  lt_of_lt_of_le (val_level hp).2 (Om_strictMono.monotone h)

theorem Om_le_val_of_le_lvl {p : WP} (hp : NFP p) {m : ℕ} (h : m ≤ p.lvl) : Om m ≤ p.val :=
  le_trans (Om_strictMono.monotone h) (val_level hp).1

theorem val_one : one.val = 1 := by
  rw [one, WP.val_th, WP.valS_nil, vartheta_zero, Om_zero]

theorem val_om (m : ℕ) : (om m).val = Om m := by
  rw [om, WP.val_th, WP.valS_nil, vartheta_zero]

theorem nfp_th_nil (m : ℕ) : NFP (.th m []) := NFP.th (by simp) (by simp) List.Pairwise.nil

theorem nfp_one : NFP one := nfp_th_nil 0

theorem one_le_val {p : WP} (hp : NFP p) : 1 ≤ p.val :=
  le_trans (one_le_Om _) (val_level hp).1

/-! ## Sums -/

theorem valS_append (l l' : List WP) : WP.valS (l ++ l') = WP.valS l + WP.valS l' := by
  induction l with
  | nil => simp
  | cons p l ih => simp [ih, add_assoc]

theorem valS_single (p : WP) : WP.valS [p] = p.val := by simp

/-- A sum of terms below an additive principal `θ > 0` is below `θ`. -/
theorem valS_lt_of_forall {θ : Ordinal.{0}} (hθ : IsPrincipal (· + ·) θ) (h0 : 0 < θ) :
    ∀ {x : List WP}, (∀ q ∈ x, q.val < θ) → WP.valS x < θ
  | [], _ => by simpa using h0
  | p :: l, h => by
    rw [WP.valS_cons]
    exact hθ (h p (by simp)) (valS_lt_of_forall hθ h0 (fun q hq => h q (by simp [hq])))

/-- A non-empty sum of `T¹` is below any principal value above its first summand. -/
theorem valS_lt_of_head_lt {p : WP} {l : List WP} (h : NFS (p :: l)) {q : WP} (hq : NFP q)
    (hlt : p.val < q.val) : WP.valS (p :: l) < q.val := by
  refine valS_lt_of_forall (val_isPrincipal hq) (val_pos hq) (fun r hr => ?_)
  rcases List.mem_cons.mp hr with rfl | hr
  · exact hlt
  · exact lt_of_le_of_lt (h.le_head r hr) hlt

theorem le_valS_head {p : WP} {l : List WP} : p.val ≤ WP.valS (p :: l) := by
  rw [WP.valS_cons]; exact le_self_add

theorem valS_pos {p : WP} {l : List WP} (h : NFP p) : 0 < WP.valS (p :: l) :=
  lt_of_lt_of_le (val_pos h) le_valS_head

/-- The summands of a sum of `T¹` all have level `≤ m` if the first one has. -/
theorem NFS.lvl_le_of_head {p : WP} {l : List WP} (h : NFS (p :: l)) {m : ℕ} (hm : p.lvl ≤ m) :
    ∀ q ∈ p :: l, q.lvl ≤ m := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact hm
  · exact le_trans (lvl_le_of_val_le ((NFS.of_cons h).1 q hq) h.head (h.le_head q hq)) hm

/-- A sum of `T¹` with summands of level `≤ m` is below `Ω_{m+1}`. -/
theorem valS_lt_Om {x : List WP} (hx : NFS x) {m : ℕ} (h : ∀ q ∈ x, q.lvl ≤ m) :
    WP.valS x < Om (m + 1) :=
  valS_lt_of_forall (Om_isPrincipal _) (Om_pos _)
    (fun q hq => val_lt_Om_of_lvl_lt (hx.1 q hq) (Nat.lt_succ_of_le (h q hq)))

/-! ## Equal values, equal terms -/

/-- Sums with equal values are equal, if their summands are. -/
theorem eq_of_valS_eq_aux :
    ∀ {x y : List WP}, NFS x → NFS y →
      (∀ p ∈ x, ∀ q, NFP q → p.val = q.val → p = q) → WP.valS x = WP.valS y → x = y
  | [], [], _, _, _, _ => rfl
  | [], q :: y, _, hy, _, h => by
    exact absurd h (ne_of_lt (by simpa using valS_pos (l := y) hy.head))
  | p :: x, [], hx, _, _, h => by
    exact absurd h (ne_of_gt (by simpa using valS_pos (l := x) hx.head))
  | p :: x, q :: y, hx, hy, hinj, h => by
    rcases lt_trichotomy p.val q.val with hlt | heq | hgt
    · exact absurd h (ne_of_lt (lt_of_lt_of_le (valS_lt_of_head_lt hx hy.head hlt) le_valS_head))
    · have hpq := hinj p (by simp) q hy.head heq
      subst hpq
      rw [WP.valS_cons, WP.valS_cons, add_right_inj] at h
      rw [eq_of_valS_eq_aux hx.of_cons hy.of_cons (fun p' hp' => hinj p' (by simp [hp'])) h]
    · exact absurd h (ne_of_gt (lt_of_lt_of_le (valS_lt_of_head_lt hy hx.head hgt) le_valS_head))

/-- **Terms of `T¹` with equal values are equal** (from the injectivity of
`ϑ_m` and the levels). -/
theorem eq_of_val_eq : ∀ {p q : WP}, NFP p → NFP q → p.val = q.val → p = q := by
  intro p
  induction p using WP.ind with
  | h m a ih =>
    intro q hp hq h
    obtain ⟨m', c⟩ := q
    have hm : m = m' := lvl_eq_of_val_eq hp hq h
    subst hm
    have hac := vartheta_inj hp hq h
    rw [eq_of_valS_eq_aux hp.nfs hq.nfs (fun p' hp' q' hq' e => ih p' hp'
      (hp.of_mem hp') hq' e) hac]

theorem eq_of_valS_eq {x y : List WP} (hx : NFS x) (hy : NFS y) (h : WP.valS x = WP.valS y) :
    x = y :=
  eq_of_valS_eq_aux hx hy (fun _ hp _ hq e => eq_of_val_eq (hx.1 _ hp) hq e) h

/-! ## Visible subterms -/

mutual
theorem starP_spec (m : ℕ) : ∀ (p : WP), NFP p → ∀ s ∈ starP m p,
    NFP s ∧ s.lvl = m ∧ s.size ≤ p.size
  | .th k a, hp, s, hs => by
    rw [starP_th] at hs
    split_ifs at hs with h1 h2
    · simp at hs
    · subst h2
      rcases List.mem_cons.mp hs with rfl | hs
      · exact ⟨hp, rfl, le_rfl⟩
      · obtain ⟨h1, h2, h3⟩ := starS_spec k a hp.nfs s hs
        exact ⟨h1, h2, by simp; omega⟩
    · obtain ⟨h1, h2, h3⟩ := starS_spec m a hp.nfs s hs
      exact ⟨h1, h2, by simp; omega⟩

theorem starS_spec (m : ℕ) : ∀ (a : List WP), NFS a → ∀ s ∈ starS m a,
    NFP s ∧ s.lvl = m ∧ s.size ≤ WP.sizeS a
  | [], _, s, hs => by simp at hs
  | p :: l, ha, s, hs => by
    rw [starS_cons, List.mem_append] at hs
    rcases hs with hs | hs
    · obtain ⟨h1, h2, h3⟩ := starP_spec m p ha.head s hs
      exact ⟨h1, h2, by simp; omega⟩
    · obtain ⟨h1, h2, h3⟩ := starS_spec m l ha.of_cons s hs
      exact ⟨h1, h2, by simp; omega⟩
end

/-! ## The comparison -/

/-- The lexicographic comparison of sums of `T¹` is the comparison of values,
if the comparison of summands is. -/
theorem lexCmp_eq {c : WP → WP → Ordering} :
    ∀ {x y : List WP}, NFS x → NFS y →
      (∀ p ∈ x, ∀ q ∈ y, c p q = compare p.val q.val) →
      lexCmp c x y = compare (WP.valS x) (WP.valS y)
  | [], [], _, _, _ => by simp [lexCmp]
  | [], q :: y, _, hy, _ => by
    rw [lexCmp, eq_comm, compare_lt_iff_lt]
    simpa using valS_pos (l := y) hy.head
  | p :: x, [], hx, _, _ => by
    rw [lexCmp, eq_comm, compare_gt_iff_gt]
    simpa using valS_pos (l := x) hx.head
  | p :: x, q :: y, hx, hy, hc => by
    rw [lexCmp, hc p (by simp) q (by simp)]
    rcases lt_trichotomy p.val q.val with hlt | heq | hgt
    · rw [(compare_lt_iff_lt).mpr hlt, eq_comm, compare_lt_iff_lt]
      exact lt_of_lt_of_le (valS_lt_of_head_lt hx hy.head hlt) le_valS_head
    · have hpq := eq_of_val_eq hx.head hy.head heq
      subst hpq
      rw [(compare_eq_iff_eq).mpr rfl, WP.valS_cons, WP.valS_cons]
      simp only
      rw [lexCmp_eq hx.of_cons hy.of_cons (fun p' hp' q' hq' => hc p' (by simp [hp'])
        q' (by simp [hq']))]
      rcases lt_trichotomy (WP.valS x) (WP.valS y) with h | h | h
      · rw [(compare_lt_iff_lt).mpr h, (compare_lt_iff_lt).mpr ((add_lt_add_iff_left _).mpr h)]
      · rw [h, (compare_eq_iff_eq).mpr rfl, (compare_eq_iff_eq).mpr rfl]
      · rw [(compare_gt_iff_gt).mpr h, (compare_gt_iff_gt).mpr ((add_lt_add_iff_left _).mpr h)]
    · rw [(compare_gt_iff_gt).mpr hgt, eq_comm, compare_gt_iff_gt]
      exact lt_of_lt_of_le (valS_lt_of_head_lt hy hx.head hgt) le_valS_head

/-- **The comparison with enough fuel is the comparison of values.** -/
theorem cmpF_eq : ∀ (f : ℕ) {p q : WP}, NFP p → NFP q → p.size + q.size ≤ f →
    cmpF f p q = compare p.val q.val
  | 0, p, q, _, _, hf => absurd hf (by have := WP.size_pos p; omega)
  | f + 1, p, q, hp, hq, hf => by
    rw [cmpF]
    split_ifs with h1 h2 h3
    · rw [h1, (compare_eq_iff_eq).mpr rfl]
    · exact ((compare_lt_iff_lt).mpr (val_lt_of_lvl_lt hp hq h2)).symm
    · exact ((compare_gt_iff_gt).mpr (val_lt_of_lvl_lt hq hp h3)).symm
    · obtain ⟨m, a⟩ := p
      obtain ⟨m', c⟩ := q
      simp only [WP.lvl_th] at h2 h3
      have hm : m = m' := by omega
      subst hm
      -- `less u v` is `u < v` for the two orders of `p` and `q`
      have key : ∀ {a c : List WP}, NFP (.th m a) → NFP (.th m c) →
          (WP.th m a).size + (WP.th m c).size ≤ f + 1 →
          (((lexCmp (cmpF f) a c == .lt &&
            (starS m a).all (fun s => cmpF f s (.th m c) == .lt)) ||
            (starS m c).any (fun s => cmpF f (.th m a) s != .gt)) = true ↔
          (WP.th m a).val < (WP.th m c).val) := by
        intro a c ha hc hs
        simp only [WP.size_th] at hs
        rw [val_lt_val_iff ha hc]
        have hlex : lexCmp (cmpF f) a c = compare (WP.valS a) (WP.valS c) :=
          lexCmp_eq ha.nfs hc.nfs (fun p' hp' q' hq' => cmpF_eq f (ha.of_mem hp') (hc.of_mem hq')
            (by have := WP.size_le_sizeS hp'; have := WP.size_le_sizeS hq'; omega))
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
          List.any_eq_true, bne_iff_ne, ne_eq, hlex, compare_lt_iff_lt]
        refine or_congr (and_congr Iff.rfl (forall₂_congr fun s hs' => ?_))
          (exists_congr fun s => and_congr_right fun hs' => ?_)
        · obtain ⟨hs1, -, hs3⟩ := starS_spec m a ha.nfs s hs'
          rw [cmpF_eq f hs1 hc (by simp; omega), compare_lt_iff_lt]
        · obtain ⟨hs1, -, hs3⟩ := starS_spec m c hc.nfs s hs'
          rw [cmpF_eq f ha hs1 (by simp; omega), compare_gt_iff_gt, not_lt]
      simp only [WP.lvl_th, WP.arg_th]
      by_cases hlt : (WP.th m a).val < (WP.th m c).val
      · rw [if_pos ((key hp hq hf).mpr hlt), eq_comm, compare_lt_iff_lt]
        exact hlt
      · rw [if_neg (fun h => hlt ((key hp hq hf).mp h))]
        by_cases hgt : (WP.th m c).val < (WP.th m a).val
        · rw [if_pos ((key hq hp (by omega)).mpr hgt), eq_comm, compare_gt_iff_gt]
          exact hgt
        · exact absurd (eq_of_val_eq hp hq (le_antisymm (not_lt.mp hgt) (not_lt.mp hlt))) h1

/-- **The comparison `cmpP` of `tr.py` is the comparison of values** on `T¹`. -/
theorem cmpP_eq {p q : WP} (hp : NFP p) (hq : NFP q) : cmpP p q = compare p.val q.val :=
  cmpF_eq _ hp hq le_rfl

theorem cmpP_lt_iff {p q : WP} (hp : NFP p) (hq : NFP q) : cmpP p q = .lt ↔ p.val < q.val := by
  rw [cmpP_eq hp hq, compare_lt_iff_lt]

/-- The comparison of sums is the comparison of values. -/
theorem cmpS_eq {x y : List WP} (hx : NFS x) (hy : NFS y) :
    cmpS x y = compare (WP.valS x) (WP.valS y) :=
  lexCmp_eq hx hy (fun _ hp _ hq => cmpP_eq (hx.1 _ hp) (hy.1 _ hq))

end Googology.Trans.PSS.TR

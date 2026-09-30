import Googology.Trans.PSS.Main.CIAux1

/-!
# CI, part 2: `jN` is an order embedding on `T¹_α`

For `α = a` of level `0`, on the terms of `T¹` whose `ϑ_0`-subterms are below `α`
([W07a] `T^τ_α`, Def 6.1), `jN a` gives terms of `T¹` (`nfp_jN`) and is strictly increasing
(`jN_lt`); `ϑ_1`-terms go to `[α, …)`.  (This is [W07a] Lemma 7.2 (b) with Lemma 6.3, proved
here on `T¹` from the comparison (C).)
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal

set_option linter.unusedSectionVars false

/-! ## Lists -/

theorem size_add_le_sizeS : ∀ {l : List WP} {p q : WP}, p ∈ l → q ∈ l → p ≠ q →
    p.size + q.size ≤ WP.sizeS l
  | [], _, _, hp, _, _ => absurd hp List.not_mem_nil
  | r :: l, p, q, hp, hq, hne => by
    rw [WP.sizeS_cons]
    rcases List.mem_cons.mp hp with e1 | h1 <;> rcases List.mem_cons.mp hq with e2 | h2
    · exact absurd (e1.trans e2.symm) hne
    · have := WP.size_le_sizeS h2; rw [e1]; omega
    · have := WP.size_le_sizeS h1; rw [e2]; omega
    · have := size_add_le_sizeS h1 h2 hne
      have := WP.sizeS_cons r l
      omega

theorem nfs_map_of {f : WP → WP} {x : List WP} (hx : NFS x) (hn : ∀ p ∈ x, NFP (f p))
    (hm : ∀ p ∈ x, ∀ q ∈ x, p ≠ q → p.val < q.val → (f p).val < (f q).val) : NFS (x.map f) := by
  refine ⟨fun r hr => ?_, ?_⟩
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr; exact hn p hp
  · rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem (fun {p q} hp hq hpq => ?_) hx.2
    rcases hpq.lt_or_eq with h | h
    · exact (hm q hq p hp (fun e => by rw [e] at h; exact lt_irrefl _ h) h).le
    · rw [eq_of_val_eq (hx.1 q hq) (hx.1 p hp) h]

theorem valS_map_lt {f : WP → WP} : ∀ {x y : List WP}, NFS x → NFS y → NFS (x.map f) →
    NFS (y.map f) → (∀ p ∈ x, ∀ q ∈ y, p.val < q.val → (f p).val < (f q).val) →
    WP.valS x < WP.valS y → WP.valS (x.map f) < WP.valS (y.map f)
  | [], [], _, _, _, _, _, h => by simp at h
  | [], q :: y, _, _, _, hfy, _, _ => by
    rw [List.map_nil, WP.valS_nil, List.map_cons]
    exact valS_pos hfy.head
  | p :: x, [], _, _, _, _, _, h => by
    exact absurd h (by rw [WP.valS_nil]; exact not_lt.mpr (by simp))
  | p :: x, q :: y, hx, hy, hfx, hfy, hm, h => by
    rcases lt_trichotomy p.val q.val with hlt | heq | hgt
    · have := hm p (by simp) q (by simp) hlt
      rw [List.map_cons, List.map_cons]
      exact lt_of_lt_of_le (valS_lt_of_head_lt hfx hfy.head this) le_valS_head
    · have e := eq_of_val_eq hx.head hy.head heq
      subst e
      rw [WP.valS_cons, WP.valS_cons, add_lt_add_iff_left] at h
      rw [List.map_cons, List.map_cons, WP.valS_cons, WP.valS_cons, add_lt_add_iff_left]
      exact valS_map_lt hx.of_cons hy.of_cons hfx.of_cons hfy.of_cons
        (fun p' hp' q' hq' => hm p' (by simp [hp']) q' (by simp [hq'])) h
    · exfalso
      exact absurd h (not_lt.mpr (lt_of_lt_of_le (valS_lt_of_head_lt hy hx.head hgt)
        le_valS_head).le)

/-- A level-`0` term `a` and a sum `L`: `a ⊕ L` has a `ϑ_0`-summand at least `a`. -/
theorem exists_ge_addS {a : WP} (ha : NFP a) {L : List WP} (hL : ∀ z ∈ L, NFP z) :
    ∃ z ∈ addS [a] L, a.val ≤ z.val := by
  cases L with
  | nil => exact ⟨a, by simp [addS], le_rfl⟩
  | cons y0 L =>
    by_cases h : cmpP a y0 = .lt
    · refine ⟨y0, ?_, ((cmpP_lt_iff ha (hL y0 (by simp))).mp h).le⟩
      rw [addS]; simp
    · refine ⟨a, ?_, le_rfl⟩
      rw [addS]; simp [h]

theorem minusOnePlus_map (f : WP → WP) (b : List WP) :
    (if b.head? = some TR.one then (b.map f).drop 1 else b.map f) = (minusOnePlus b).map f := by
  cases b with
  | nil => simp [minusOnePlus]
  | cons q r =>
    simp only [List.head?_cons, Option.some.injEq, minusOnePlus]
    split_ifs <;> simp

/-! ## The order embedding -/

theorem takeWhile_eq_take' {α : Type*} (P : α → Bool) (l : List α) :
    l.takeWhile P = l.take (l.takeWhile P).length :=
  List.prefix_iff_eq_take.mp (List.takeWhile_prefix P)

theorem dropWhile_eq_drop' {α : Type*} (P : α → Bool) (l : List α) :
    l.dropWhile P = l.drop (l.takeWhile P).length := by
  have e1 := List.takeWhile_append_dropWhile (p := P) (l := l)
  have e2 := List.take_append_drop (l.takeWhile P).length l
  rw [← takeWhile_eq_take'] at e2
  exact List.append_cancel_left (e1.trans e2.symm)

theorem starS_take_subset {m n : ℕ} {b : List WP} {y : WP} (hy : y ∈ starS m (b.take n)) :
    y ∈ starS m b := by
  obtain ⟨v, hv, hy'⟩ := exists_of_mem_starS hy
  exact mem_starS_of_mem (List.mem_of_mem_take hv) hy'

theorem starS_drop_subset {m n : ℕ} {b : List WP} {y : WP} (hy : y ∈ starS m (b.drop n)) :
    y ∈ starS m b := by
  obtain ⟨v, hv, hy'⟩ := exists_of_mem_starS hy
  exact mem_starS_of_mem (List.mem_of_mem_drop hv) hy'

/-- The domain `T¹_α`: terms of `T¹` whose `ϑ_0`-subterms are below `α`. -/
def DomA (a p : WP) : Prop := NFP p ∧ ∀ z ∈ starP 0 p, z.val < a.val

theorem DomA.of_mem {a p q : WP} (hp : DomA a p) (hq : q ∈ p.arg) : DomA a q := by
  obtain ⟨k, c⟩ := p
  exact ⟨hp.1.of_mem hq, fun z hz => hp.2 z (mem_starP0_of_mem_arg hq hz)⟩

theorem DomA.of_star {a : WP} {m : ℕ} {p s : WP} (hp : DomA a p) (hs : s ∈ starP m p) :
    DomA a s :=
  ⟨(starP_spec m p hp.1 s hs).1, fun z hz => hp.2 z (mem_starP0_trans hs hz)⟩

/-- The properties of `jN` on one term. -/
def G1 (a p : WP) : Prop :=
  NFP (jN a p) ∧ (p.lvl = 1 → a.val ≤ (jN a p).val) ∧
    (p.lvl = 1 → p ≠ .th 1 [] → a.val < (jN a p).val)

def OEStep (a : WP) (n : ℕ) : Prop :=
  (∀ p, p.size ≤ n → DomA a p → G1 a p) ∧
    (∀ p q, p.size + q.size ≤ n → DomA a p → DomA a q → p.val < q.val →
      (jN a p).val < (jN a q).val)

theorem jN_one_nil (a : WP) : jN a (.th 1 []) = a := by rw [jN_one, jNTop]; simp

theorem jN_mem_starS0_map {a : WP} (h0 : a.lvl = 0) {x : List WP} {y : WP} (hy : y ∈ starS 1 x) :
    jN a y ∈ starS 0 (x.map (jN a)) := by
  obtain ⟨v, hv, hy'⟩ := exists_of_mem_starS hy
  exact mem_starS_of_mem (List.mem_map_of_mem hv) (jN_mem_starP0 h0 v y hy')

theorem mem_starS0_self {z : WP} {L : List WP} (hz : z ∈ L) (hz0 : z.lvl = 0) :
    z ∈ starS 0 L := by
  refine mem_starS_of_mem hz ?_
  obtain ⟨k, c⟩ := z
  simp only [WP.lvl_th] at hz0; subst hz0
  rw [starP_th]; simp

/-- The number of summands of level `≥ 2` at the start of `b` (`Γ` of the case `ϑ_1(b)`). -/
def nG (b : List WP) : ℕ := (b.takeWhile (fun q => decide (2 ≤ q.lvl))).length

theorem lvl_take_nG {b : List WP} (hl : ∀ q ∈ b, q.lvl ≤ 2) : ∀ q ∈ b.take (nG b), q.lvl = 2 := by
  intro q hq
  rw [nG, ← takeWhile_eq_take'] at hq
  have := List.mem_takeWhile_imp hq
  simp only [decide_eq_true_eq] at this
  have := hl q ((List.takeWhile_sublist _).subset hq); omega

theorem lvl_drop_nG {b : List WP} (hbn : NFS b) : ∀ q ∈ b.drop (nG b), q.lvl ≤ 1 := by
  rw [nG, ← dropWhile_eq_drop']
  intro q hq
  have hd := hbn.dropWhile (fun q => decide (2 ≤ q.lvl))
  cases hdl : b.dropWhile (fun q => decide (2 ≤ q.lvl)) with
  | nil => rw [hdl] at hq; simp at hq
  | cons q0 r =>
    have hq0' := List.head_dropWhile_not (fun q => decide (2 ≤ q.lvl)) (l := b) (by rw [hdl]; simp)
    have hq0 : q0.lvl < 2 := by simpa [hdl] using hq0'
    rw [hdl] at hd hq
    exact NFS.lvl_le_of_head hd (by omega) q hq

/-- The part of the argument of `jN(ϑ_1(b))` below `Ω_1`. -/
noncomputable def tailV (a : WP) (b : List WP) : Ordinal.{0} :=
  if nG b = 0 then a.val + WP.valS ((minusOnePlus b).map (jN a))
  else if (starS 1 (b.take (nG b))).isEmpty then a.val + WP.valS ((b.drop (nG b)).map (jN a))
  else WP.valS ((b.drop (nG b)).map (jN a))

theorem valS_arg_jN_one {a : WP} (ha : NFP a) {b : List WP} (hb : b ≠ [])
    (hM : NFS ((minusOnePlus b).map (jN a))) (hD : NFS ((b.drop (nG b)).map (jN a))) :
    WP.valS (jN a (.th 1 b)).arg = WP.valS ((b.take (nG b)).map (jN a)) + tailV a b := by
  have hb' : ¬ b.isEmpty = true := by simpa using hb
  rw [jN_one, jNTop, if_neg hb', jNL_eq_map, tailV]
  by_cases h1 : (b.takeWhile (fun q => decide (2 ≤ q.lvl))).isEmpty = true
  · have hn : nG b = 0 := by rw [nG]; simpa using h1
    rw [if_pos h1, if_pos hn, hn, minusOnePlus_map]
    rw [WP.arg_th, valS_addS_single ha hM, List.take_zero, List.map_nil, WP.valS_nil, zero_add]
  · have hn : nG b ≠ 0 := by rw [nG]; simpa using h1
    rw [if_neg h1, if_neg hn]
    rw [← nG]
    split_ifs with h2
    · rw [WP.arg_th, valS_append, ← List.map_take, ← List.map_drop, valS_addS_single ha hD]
    · rw [WP.arg_th]; conv_lhs => rw [← List.take_append_drop (nG b) b, List.map_append, valS_append]

theorem jN_mem_starS0_arg_one {a : WP} (h0 : a.lvl = 0) {c : List WP} (hc : c ≠ []) {s : WP}
    (hs : s ∈ starS 1 c) : jN a s ∈ starS 0 (jN a (.th 1 c)).arg := by
  obtain ⟨v, hv, hs'⟩ := exists_of_mem_starS hs
  have h1 := jN_mem_starP0 h0 v s hs'
  have hmem := jN_mem_arg_one h0 hc hv (Or.inl (by
    rintro rfl; rw [TR.one, starP_lvl_lt (by simp)] at hs'; simp at hs'))
  exact mem_starS_of_mem hmem h1

section OE

variable {a : WP} (ha : NFP a) (h0 : a.lvl = 0)
include ha h0

theorem g1_step {n : ℕ} (IH : OEStep a n) {p : WP} (hs : p.size ≤ n + 1) (hp : DomA a p) :
    G1 a p := by
  obtain ⟨k, b⟩ := p
  have hsb : WP.sizeS b ≤ n := by simp at hs; omega
  have hel : ∀ q ∈ b, DomA a q := fun q hq => hp.of_mem hq
  have hg : ∀ q ∈ b, G1 a q := fun q hq =>
    IH.1 q (le_trans (WP.size_le_sizeS hq) hsb) (hel q hq)
  have hmono : ∀ q ∈ b, ∀ r ∈ b, q ≠ r → q.val < r.val → (jN a q).val < (jN a r).val :=
    fun q hq r hr hne h => IH.2 q r (le_trans (size_add_le_sizeS hq hr hne) hsb) (hel q hq)
      (hel r hr) h
  have hbn : NFS b := hp.1.nfs
  have hnfs : ∀ l : List WP, l.Sublist b → NFS (l.map (jN a)) := fun l hl =>
    nfs_map_of (hbn.sublist hl) (fun q hq => (hg q (hl.subset hq)).1)
      (fun q hq r hr => hmono q (hl.subset hq) r (hl.subset hr))
  rcases k with _ | _ | k
  · rw [G1, jN_zero]; exact ⟨hp.1, by simp, by simp⟩
  · -- `ϑ_1(b)`
    by_cases hb : b = []
    · subst hb; rw [G1, jN_one_nil a]; exact ⟨ha, fun _ => le_rfl, fun _ h => absurd rfl h⟩
    have hb' : ¬ b.isEmpty = true := by simpa using hb
    have hlvl : ∀ q ∈ b, q.lvl ≤ 2 := fun q hq => hp.1.lvl_le hq
    have hjl : ∀ q ∈ b, q.lvl ≤ 1 → (jN a q).lvl = 0 := fun q _ h => by rw [jN_lvl h0]; omega
    -- `α <` the value, from a `ϑ_0`-summand `z ≥ α` of the argument
    have hstrict : ∀ c : List WP, NFP (.th 0 c) → (∃ z ∈ starS 0 c, a.val ≤ z.val) →
        a.val < (WP.th 0 c).val := fun c hc ⟨z, hz, hle⟩ =>
      lt_of_le_of_lt hle (star_lt_val hc z hz)
    suffices H : NFP (jN a (.th 1 b)) ∧ a.val < (jN a (.th 1 b)).val from
      ⟨H.1, fun _ => H.2.le, fun _ _ => H.2⟩
    rw [jN_one, jNTop, if_neg hb', jNL_eq_map]
    set P : WP → Bool := fun q => decide (2 ≤ q.lvl) with hP
    set n' := (b.takeWhile P).length with hn'
    have htake : b.takeWhile P = b.take n' := takeWhile_eq_take' P b
    have hdrop : b.dropWhile P = b.drop n' := dropWhile_eq_drop' P b
    have hΓ : ∀ q ∈ b.take n', q.lvl = 2 := fun q hq => by
      rw [← htake] at hq
      have := List.mem_takeWhile_imp hq
      simp only [hP, decide_eq_true_eq] at this
      have := hlvl q (List.mem_of_mem_take (htake ▸ hq)); omega
    have hρ : ∀ q ∈ b.drop n', q.lvl ≤ 1 := by
      rw [← hdrop]
      intro q hq
      have hd := hbn.dropWhile P
      cases hdl : b.dropWhile P with
      | nil => rw [hdl] at hq; simp at hq
      | cons q0 r =>
        have hq0 : ¬ P q0 = true := by
          have := List.head_dropWhile_not P (l := b) (by rw [hdl]; simp)
          simpa [hdl] using this
        simp only [hP, decide_eq_true_eq, not_le] at hq0
        rw [hdl] at hd hq
        exact NFS.lvl_le_of_head hd (by omega) q hq
    by_cases h1 : (b.takeWhile P).isEmpty = true
    · rw [if_pos h1, minusOnePlus_map]
      have hn0 : n' = 0 := by rw [hn']; simpa using h1
      have hsubl := minusOnePlus_sublist b
      have hL := hnfs _ hsubl
      have hLl : ∀ z ∈ (minusOnePlus b).map (jN a), z.lvl = 0 := fun z hz => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
        have hqb := hsubl.subset hq
        exact hjl q hqb (hρ q (by rw [hn0, List.drop_zero]; exact hqb))
      have hA := addS_spec (NFS.single ha) hL
      have hnf : NFP (.th 0 (addS [a] ((minusOnePlus b).map (jN a)))) :=
        NFP.th hA.1.1 (fun z hz => by
          rcases mem_addS hz with h | h
          · rw [List.mem_singleton.mp h, h0]; omega
          · rw [hLl z h]; omega) hA.1.2
      refine ⟨hnf, hstrict _ hnf ?_⟩
      obtain ⟨z, hz, hle⟩ := exists_ge_addS ha hL.1
      refine ⟨z, mem_starS0_self hz ?_, hle⟩
      rcases mem_addS hz with h | h
      · rw [List.mem_singleton.mp h, h0]
      · exact hLl z h
    rw [if_neg h1]
    have hdl : ∀ z ∈ (b.drop n').map (jN a), z.lvl = 0 := fun z hz => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
      exact hjl q (List.mem_of_mem_drop hq) (hρ q hq)
    have htl : ∀ z ∈ (b.take n').map (jN a), z.lvl = 1 := fun z hz => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
      rw [jN_lvl h0, hΓ q hq]
    have hTn := hnfs _ (List.take_sublist n' b)
    have hDn := hnfs _ (List.drop_sublist n' b)
    by_cases h2 : (starS 1 (b.take n')).isEmpty = true
    · rw [if_pos h2, ← List.map_take, ← List.map_drop]
      have hA := addS_spec (NFS.single ha) hDn
      have hAl : ∀ z ∈ addS [a] ((b.drop n').map (jN a)), z.lvl = 0 := fun z hz => by
        rcases mem_addS hz with h | h
        · rw [List.mem_singleton.mp h, h0]
        · exact hdl z h
      have hN : NFS ((b.take n').map (jN a) ++ addS [a] ((b.drop n').map (jN a))) :=
        NFS.append_iff.mpr ⟨hTn, hA.1, fun x hx y hy =>
          (val_lt_of_lvl_lt (hA.1.1 y hy) (hTn.1 x hx) (by rw [htl x hx, hAl y hy]; omega)).le⟩
      have hnf : NFP (.th 0 ((b.take n').map (jN a) ++ addS [a] ((b.drop n').map (jN a)))) :=
        NFP.th hN.1 (fun z hz => by
          rcases List.mem_append.mp hz with h | h
          · rw [htl z h]
          · rw [hAl z h]; omega) hN.2
      refine ⟨hnf, hstrict _ hnf ?_⟩
      obtain ⟨z, hz, hle⟩ := exists_ge_addS ha hDn.1
      exact ⟨z, mem_starS0_self (List.mem_append_right _ hz) (hAl z hz), hle⟩
    · rw [if_neg h2]
      have hN := hnfs b (List.Sublist.refl b)
      have hnf : NFP (.th 0 (b.map (jN a))) :=
        NFP.th hN.1 (fun z hz => by
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
          rw [jN_lvl h0]; have := hlvl q hq; omega) hN.2
      refine ⟨hnf, hstrict _ hnf ?_⟩
      obtain ⟨y, hy⟩ : ∃ y, y ∈ starS 1 (b.take n') := by
        cases hh : starS 1 (b.take n') with
        | nil => rw [hh] at h2; simp at h2
        | cons y _ => exact ⟨y, by simp⟩
      have hyb := starS_take_subset hy
      have hyP : y ∈ starP 1 (.th 1 b) := by rw [starP_th]; simp [hyb]
      have hyD := hp.of_star hyP
      have hys : y.size ≤ n := by
        have := (starS_spec 1 b hbn y hyb).2.2; omega
      have hy1 : y.lvl = 1 := (starS_spec 1 b hbn y hyb).2.1
      exact ⟨jN a y, jN_mem_starS0_map h0 hyb, (IH.1 y hys hyD).2.1 hy1⟩
  · rw [G1, jN_add_two, jNL_eq_map]
    have hN := hnfs b (List.Sublist.refl b)
    refine ⟨NFP.th hN.1 (fun z hz => ?_) hN.2, by simp, by simp⟩
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
    rw [jN_lvl h0]; have := hp.1.lvl_le hq; omega

theorem tailV_lt {b : List WP} (hbn : NFS b) (hl : ∀ q ∈ b, q.lvl ≤ 2)
    (hM : NFS ((minusOnePlus b).map (jN a))) (hD : NFS ((b.drop (nG b)).map (jN a))) :
    tailV a b < Om 1 := by
  have ha1 : a.val < Om 1 := val_lt_Om_of_lvl_lt ha (by rw [h0]; omega)
  have hlow : ∀ {x : List WP}, x.Sublist b → (∀ q ∈ x, q.lvl ≤ 1) → NFS (x.map (jN a)) →
      WP.valS (x.map (jN a)) < Om 1 := fun {x} _ hx hn => by
    have := valS_lt_Om hn (m := 0) (fun z hz => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz; rw [jN_lvl h0]; have := hx q hq; omega)
    simpa using this
  have hP := Om_isPrincipal 1
  have hd : WP.valS ((b.drop (nG b)).map (jN a)) < Om 1 :=
    hlow (List.drop_sublist _ _) (lvl_drop_nG hbn) hD
  unfold tailV
  split_ifs with h1 h2
  · refine hP ha1 (hlow (minusOnePlus_sublist b) (fun q hq => ?_) hM)
    have := lvl_drop_nG hbn q (by rw [h1, List.drop_zero]; exact (minusOnePlus_sublist b).subset hq)
    exact this
  · exact hP ha1 hd
  · exact hd

theorem p2_step {n : ℕ} (IH : OEStep a n) (hG : ∀ p, p.size ≤ n + 1 → DomA a p → G1 a p)
    {p q : WP} (hs : p.size + q.size ≤ n + 1) (hp : DomA a p) (hq : DomA a q)
    (hlt : p.val < q.val) : (jN a p).val < (jN a q).val := by
  have hps := WP.size_pos p
  have hqs := WP.size_pos q
  have hGp := hG p (by omega) hp
  have hGq := hG q (by omega) hq
  -- comparisons below
  have hIH : ∀ p' q', p'.size + q'.size < p.size + q.size → DomA a p' → DomA a q' →
      p'.val < q'.val → (jN a p').val < (jN a q').val := fun p' q' h => IH.2 p' q' (by omega)
  have hIHle : ∀ p' q', p'.size + q'.size < p.size + q.size → DomA a p' → DomA a q' →
      p'.val ≤ q'.val → (jN a p').val ≤ (jN a q').val := fun p' q' h hp' hq' hle => by
    rcases hle.lt_or_eq with h' | h'
    · exact (hIH p' q' h hp' hq' h').le
    · rw [eq_of_val_eq hp'.1 hq'.1 h']
  obtain ⟨k, b⟩ := p
  obtain ⟨l, c⟩ := q
  have hkl : k ≤ l := by
    by_contra h
    exact absurd hlt (not_lt.mpr (val_lt_of_lvl_lt hq.1 hp.1 (by simp; omega)).le)
  have hszb : ∀ v ∈ b, v.size < (WP.th k b).size := fun v hv => WP.size_lt_of_mem hv
  have hszc : ∀ v ∈ c, v.size < (WP.th l c).size := fun v hv => WP.size_lt_of_mem hv
  rcases hkl.lt_or_eq with hkl | rfl
  · -- different levels
    rcases l with _ | _ | l
    · omega
    · have hk0 : k = 0 := by omega
      subst hk0
      rw [jN_zero]
      have hpa : (WP.th 0 b).val < a.val := hp.2 _ (by rw [starP_th]; simp)
      exact lt_of_lt_of_le hpa (hGq.2.1 rfl)
    · refine val_lt_of_lvl_lt hGp.1 hGq.1 ?_
      rw [jN_lvl h0, jN_lvl h0]; simp; omega
  -- one level
  have hC := (val_lt_val_iff hp.1 hq.1).mp hlt
  rcases k with _ | _ | j
  · rw [jN_zero, jN_zero]; exact hlt
  · -- level `1`
    have e1 : (WP.th (0 + 1) b).size = WP.sizeS b + 1 := WP.size_th _ _
    have e2 : (WP.th 1 b).size = WP.sizeS b + 1 := WP.size_th _ _
    have e3 : (WP.th (0 + 1) c).size = WP.sizeS c + 1 := WP.size_th _ _
    have e4 : (WP.th 1 c).size = WP.sizeS c + 1 := WP.size_th _ _
    by_cases hc : c = []
    · subst hc
      exact absurd hlt (not_lt.mpr (by
        rw [WP.val_th, WP.valS_nil, vartheta_zero]; exact Om_le_val_of_le_lvl hp.1 (by simp)))
    by_cases hb : b = []
    · subst hb
      rw [jN_one_nil]
      exact hGq.2.2 rfl (by simpa using hc)
    obtain ⟨b', hb'⟩ := jN_one_th h0 b
    obtain ⟨c', hc'⟩ := jN_one_th h0 c
    have hnb := hGp.1
    have hnc := hGq.1
    rw [hb'] at hnb
    rw [hc'] at hnc
    have hαq : a.val < (jN a (.th 1 c)).val := hGq.2.2 rfl (by simpa using hc)
    rw [hb', hc']
    rw [hc'] at hαq
    refine (val_lt_val_iff hnb hnc).mpr ?_
    rcases hC with ⟨hbc, hstar⟩ | ⟨s, hs, hle⟩
    swap
    · -- `ϑ_1(b) ≤ s` for a visible `s` of `c`
      right
      have hsq : s ∈ starP 1 (.th 1 c) := by rw [starP_th]; simp [hs]
      have hsD := hq.of_star hsq
      have hssz : s.size < (WP.th 1 c).size := by
        have := (starS_spec 1 c hq.1.nfs s hs).2.2; simp; omega
      have h := jN_mem_starS0_arg_one h0 hc hs
      rw [hc', WP.arg_th] at h
      refine ⟨jN a s, h, ?_⟩
      rw [← hb']
      exact hIHle _ s (by omega) hp hsD hle
    left
    refine ⟨?_, fun z hz => ?_⟩
    swap
    · -- the `ϑ_0`-subterms of the argument
      obtain ⟨w, hw, hzw⟩ := exists_of_mem_starS hz
      have hw' : w ∈ (jN a (.th 1 b)).arg := by rw [hb']; exact hw
      rcases mem_arg_jN_one h0 hb hw' with rfl | ⟨v, hv, rfl⟩
      · exact lt_of_le_of_lt (val_le_of_mem_starP ha hzw) hαq
      · have hvD : DomA a v := hp.of_mem hv
        refine starP0_jN_lt h0 ha hαq v hvD.2 (fun y hy => ?_) z hzw
        have hyb : y ∈ starS 1 b := mem_starS_of_mem hv hy
        have hyD : DomA a y := hvD.of_star hy
        have hysz : y.size < (WP.th 1 b).size := by
          have := (starS_spec 1 b hp.1.nfs y hyb).2.2; simp; omega
        rw [← hc']
        exact hIH y _ (by omega) hyD hq (hstar y hyb)
    · -- the arguments
      have hbn : NFS b := hp.1.nfs
      have hcn : NFS c := hq.1.nfs
      have hlb : ∀ v ∈ b, v.lvl ≤ 2 := fun v hv => hp.1.lvl_le hv
      have hlc : ∀ v ∈ c, v.lvl ≤ 2 := fun v hv => hq.1.lvl_le hv
      have hsb : WP.sizeS b + 1 = (WP.th 1 b).size := by simp
      have hsc : WP.sizeS c + 1 = (WP.th 1 c).size := by simp
      -- `jN` on sublists
      have hnfsb : ∀ x : List WP, x.Sublist b → NFS (x.map (jN a)) := fun x hx =>
        nfs_map_of (hbn.sublist hx) (fun v hv => (hG v (by
            have := WP.size_le_sizeS (hx.subset hv); omega) (hp.of_mem (hx.subset hv))).1)
          (fun v hv w hw hne h => hIH v w (by
            have := size_add_le_sizeS (hx.subset hv) (hx.subset hw) hne; omega)
            (hp.of_mem (hx.subset hv)) (hp.of_mem (hx.subset hw)) h)
      have hnfsc : ∀ x : List WP, x.Sublist c → NFS (x.map (jN a)) := fun x hx =>
        nfs_map_of (hcn.sublist hx) (fun v hv => (hG v (by
            have := WP.size_le_sizeS (hx.subset hv); omega) (hq.of_mem (hx.subset hv))).1)
          (fun v hv w hw hne h => hIH v w (by
            have := size_add_le_sizeS (hx.subset hv) (hx.subset hw) hne; omega)
            (hq.of_mem (hx.subset hv)) (hq.of_mem (hx.subset hw)) h)
      have hmono : ∀ x y : List WP, x.Sublist b → y.Sublist c →
          WP.valS x < WP.valS y → WP.valS (x.map (jN a)) < WP.valS (y.map (jN a)) :=
        fun x y hx hy h => valS_map_lt (hbn.sublist hx) (hcn.sublist hy) (hnfsb x hx)
          (hnfsc y hy) (fun v hv w hw hvw => hIH v w (by
            have := WP.size_le_sizeS (hx.subset hv)
            have := WP.size_le_sizeS (hy.subset hw); omega)
            (hp.of_mem (hx.subset hv)) (hq.of_mem (hy.subset hw)) hvw) h
      have hvb := valS_arg_jN_one ha hb (hnfsb _ (minusOnePlus_sublist b))
        (hnfsb _ (List.drop_sublist _ _))
      have hvc := valS_arg_jN_one ha hc (hnfsc _ (minusOnePlus_sublist c))
        (hnfsc _ (List.drop_sublist _ _))
      rw [hb', WP.arg_th] at hvb
      rw [hc', WP.arg_th] at hvc
      rw [hvb, hvc]
      have htb := tailV_lt ha h0 hbn hlb (hnfsb _ (minusOnePlus_sublist b))
        (hnfsb _ (List.drop_sublist _ _))
      have htc := tailV_lt ha h0 hcn hlc (hnfsc _ (minusOnePlus_sublist c))
        (hnfsc _ (List.drop_sublist _ _))
      -- split `b = Γ_b + ρ_b`
      have eb : WP.valS b = WP.valS (b.take (nG b)) + WP.valS (b.drop (nG b)) := by
        rw [← valS_append, List.take_append_drop]
      have ec : WP.valS c = WP.valS (c.take (nG c)) + WP.valS (c.drop (nG c)) := by
        rw [← valS_append, List.take_append_drop]
      have hΓb := lvl_take_nG hlb
      have hΓc := lvl_take_nG hlc
      have hρc : WP.valS (c.drop (nG c)) < Om 2 :=
        valS_lt_Om (hcn.sublist (List.drop_sublist _ _)) (fun v hv => lvl_drop_nG hcn v hv)
      obtain ⟨hΓle, hρle⟩ := split_mono (m := 2) (hbn.sublist (List.take_sublist _ _))
        (hcn.sublist (List.take_sublist _ _)) (fun v hv => by rw [hΓb v hv])
        (fun v hv => by rw [hΓc v hv]) hρc (by rw [← eb, ← ec]; exact hbc.le)
      rcases hΓle.lt_or_eq with hΓlt | hΓeq
      · -- different `Γ`
        have h1 := hmono _ _ (List.take_sublist _ _) (List.take_sublist _ _) hΓlt
        have hg := gap_of_lt (m := 1) (hnfsc _ (List.take_sublist _ _))
          (hnfsb _ (List.take_sublist _ _))
          (fun z hz => by
            obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz; rw [jN_lvl h0, hΓc v hv])
          (fun z hz => by
            obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz; rw [jN_lvl h0, hΓb v hv]) h1
        calc _ < WP.valS ((b.take (nG b)).map (jN a)) + Om 1 := (add_lt_add_iff_left _).mpr htb
          _ ≤ WP.valS ((c.take (nG c)).map (jN a)) := hg
          _ ≤ _ := le_self_add
      · -- equal `Γ`
        have hΓ := eq_of_valS_eq (hbn.sublist (List.take_sublist _ _))
          (hcn.sublist (List.take_sublist _ _)) hΓeq
        have hlen : nG b = nG c := by
          have hb1 : nG b ≤ b.length := by
            rw [nG]; exact (List.takeWhile_sublist _).length_le
          have hc1 : nG c ≤ c.length := by
            rw [nG]; exact (List.takeWhile_sublist _).length_le
          have := congrArg List.length hΓ
          rw [List.length_take, List.length_take] at this; omega
        have hρlt : WP.valS (b.drop (nG b)) < WP.valS (c.drop (nG c)) := by
          rw [eb, ec, hΓeq] at hbc; exact (add_lt_add_iff_left _).mp hbc
        rw [hΓ, add_lt_add_iff_left]
        unfold tailV
        have hΓ' : c.take (nG b) = b.take (nG b) := by rw [hΓ, hlen]
        rw [← hlen] at hρlt
        have h1 := hmono _ _ (List.drop_sublist _ _) (List.drop_sublist _ _) hρlt
        rw [← hlen, hΓ']
        split_ifs with hn0 h2
        · refine (add_lt_add_iff_left _).mpr
            (hmono _ _ (minusOnePlus_sublist b) (minusOnePlus_sublist c) ?_)
          have e1 := one_add_minusOnePlus hbn hb
          have e2 := one_add_minusOnePlus hcn hc
          rw [← e1, ← e2] at hbc
          exact (add_lt_add_iff_left _).mp hbc
        · exact (add_lt_add_iff_left _).mpr h1
        · exact h1
  · -- level `≥ 2`
    have e1 : (WP.th (j + 1 + 1) b).size = WP.sizeS b + 1 := WP.size_th _ _
    have e2 : (WP.th (j + 2) b).size = WP.sizeS b + 1 := WP.size_th _ _
    have e3 : (WP.th (j + 1 + 1) c).size = WP.sizeS c + 1 := WP.size_th _ _
    have e4 : (WP.th (j + 2) c).size = WP.sizeS c + 1 := WP.size_th _ _
    rw [jN_add_two, jN_add_two, jNL_eq_map, jNL_eq_map]
    have hnb := hGp.1
    have hnc := hGq.1
    rw [jN_add_two, jNL_eq_map] at hnb hnc
    have hjq : (WP.th (j + 1) (c.map (jN a))).val = (jN a (.th (j + 2) c)).val := by
      rw [jN_add_two, jNL_eq_map]
    refine (val_lt_val_iff hnb hnc).mpr ?_
    rcases hC with ⟨hbc, hstar⟩ | ⟨s, hs, hle⟩
    · left
      refine ⟨valS_map_lt hp.1.nfs hq.1.nfs hnb.nfs hnc.nfs (fun v hv w hw hvw => hIH v w (by
          have := hszb v hv; have := hszc w hw; omega) (hp.of_mem hv) (hq.of_mem hw) hvw) hbc,
        fun z hz => ?_⟩
      rw [starS_jN h0 (m := j + 1) (by omega)] at hz
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hz
      have hsP : s ∈ starP (j + 2) (.th (j + 2) b) := by rw [starP_th]; simp [hs]
      have hssz : s.size < (WP.th (j + 2) b).size := by
        have := (starS_spec _ b hp.1.nfs s hs).2.2; simp; omega
      rw [hjq]
      exact hIH s _ (by omega) (hp.of_star hsP) hq (hstar s hs)
    · right
      have hsP : s ∈ starP (j + 2) (.th (j + 2) c) := by rw [starP_th]; simp [hs]
      have hssz : s.size < (WP.th (j + 2) c).size := by
        have := (starS_spec _ c hq.1.nfs s hs).2.2; simp; omega
      refine ⟨jN a s, ?_, ?_⟩
      · rw [starS_jN h0 (m := j + 1) (by omega)]; exact List.mem_map_of_mem hs
      · have := hIHle _ s (by omega) hp (hq.of_star hsP) hle
        rwa [jN_add_two, jNL_eq_map] at this

/-- **`jN` is an order embedding on `T¹_α`** (all sizes). -/
theorem oeStep : ∀ n, OEStep a n := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun p hp => absurd hp (by have := WP.size_pos p; omega),
      fun p q hs => absurd hs (by have := WP.size_pos p; omega)⟩
  | succ n ih =>
    have hG : ∀ p, p.size ≤ n + 1 → DomA a p → G1 a p := fun p hs hp => g1_step ha h0 ih hs hp
    exact ⟨hG, fun p q hs hp hq hlt => p2_step ha h0 ih hG hs hp hq hlt⟩

theorem g1 {p : WP} (hp : DomA a p) : G1 a p := (oeStep ha h0 p.size).1 p le_rfl hp

theorem nfp_jN {p : WP} (hp : DomA a p) : NFP (jN a p) := (g1 ha h0 hp).1

theorem jN_lt {p q : WP} (hp : DomA a p) (hq : DomA a q) (h : p.val < q.val) :
    (jN a p).val < (jN a q).val := (oeStep ha h0 (p.size + q.size)).2 p q le_rfl hp hq h

theorem jN_lt_iff {p q : WP} (hp : DomA a p) (hq : DomA a q) :
    (jN a p).val < (jN a q).val ↔ p.val < q.val := by
  refine ⟨fun h => ?_, jN_lt ha h0 hp hq⟩
  rcases lt_trichotomy p.val q.val with h' | h' | h'
  · exact h'
  · rw [eq_of_val_eq hp.1 hq.1 h'] at h; exact absurd h (lt_irrefl _)
  · exact absurd h (not_lt.mpr (jN_lt ha h0 hq hp h').le)

theorem jN_inj {p q : WP} (hp : DomA a p) (hq : DomA a q) (h : jN a p = jN a q) : p = q := by
  rcases lt_trichotomy p.val q.val with h' | h' | h'
  · have := jN_lt ha h0 hp hq h'; rw [h] at this; exact absurd this (lt_irrefl _)
  · exact eq_of_val_eq hp.1 hq.1 h'
  · have := jN_lt ha h0 hq hp h'; rw [h] at this; exact absurd this (lt_irrefl _)

end OE

end Googology.Trans.PSS.Main

import Googology.Trans.PSS.Main.Cited3
import Googology.Trans.PSS.Main.FactBar

/-!
# Theorem S⁺ (rigidity), for every base `σ ≥ 1`

Let `S` be a finite set of ordinals below `T¹ ∩ Ω_1` that contains `0` and a base `σ ≥ 1`,
is closed under additive decomposition, contains `lh(y)` for every principal `y ∈ S` above
`σ`, and has a **witness** `b ∈ S ∩ y` for every such `y` (`WitS`: for `y ∉ E` with
`y = ω^ζ`, `ζ =_ANF ζ' + ω^z`, `b ≥ ω^{ζ'}`; for `y ∈ E`, every epsilon `γ ∈ (b, y)` has
`π^{-1}_{γ,y}(λ_γ) < λ_y`).  Let `h` be strictly increasing on `S`, additive on `S`, with
`h(x) ≥ x` for `x ≤ σ`, and keeping `y ≤₁ w` for principal `y > σ` with `h(y) < T¹ ∩ Ω_1`.
Then `h(y) ≥ y` on `S` (`splus`).

This is Theorem S⁺ of the paper proof (not yet published), in a form that needs neither
the parameter split `X`/`Q` nor "`h` maps principals to principals": the absorption
`x + q = q ⇒ h(x)·ω ≤ h(q)` (for `x < q` principal in `S`) takes its place.  The induction
is on the number of elements of `S` above the base; the base change at an epsilon `q` uses
`π^{-1}_{h(q), q}` (`Main/Cited3.lean`).
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Order

/-! ## Ordinal lemmas -/

theorem exists_anf_of_lt {x : Ordinal.{0}} (hx : x < T1bound) : ∃ l, ANF l ∧ l.sum = x := by
  obtain ⟨u, hu, hus, -⟩ := exists_nfs_of_lt_T1bound hx
  exact ⟨u.map WP.val, anf_of_nfs hu, by rw [← valS_eq_sum_map, hus]⟩

theorem mem_le_sum : ∀ {l : List Ordinal.{0}} {x : Ordinal.{0}}, x ∈ l → x ≤ l.sum
  | [], _, h => by simp at h
  | a :: t, x, h => by
    rw [List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_self_add
    · exact le_trans (mem_le_sum h) le_add_self

theorem take_sum_le (l : List Ordinal.{0}) (i : ℕ) : (l.take i).sum ≤ l.sum := by
  conv_rhs => rw [← List.take_append_drop i l]
  rw [List.sum_append]; exact le_self_add

theorem ANF.sublist {l l' : List Ordinal.{0}} (hl : ANF l) (h : l'.Sublist l) : ANF l' :=
  ⟨fun x hx => hl.1 x (h.subset hx), hl.2.sublist h⟩

theorem anf_single {x : Ordinal.{0}} (hP : Pr x) : ANF [x] :=
  ⟨by simpa using hP, List.pairwise_singleton _ _⟩

theorem sum_le_sum_map {f : Ordinal.{0} → Ordinal.{0}} :
    ∀ {l : List Ordinal.{0}}, (∀ x ∈ l, x ≤ f x) → l.sum ≤ (l.map f).sum
  | [], _ => le_rfl
  | a :: t, h => by
    rw [List.sum_cons, List.map_cons, List.sum_cons]
    exact add_le_add (h a (by simp)) (sum_le_sum_map (fun x hx => h x (by simp [hx])))

/-- `a + b = b` forces `a·ω ≤ b`. -/
theorem mul_omega_le_of_add_eq {a b : Ordinal.{0}} (h : a + b = b) : a * ω ≤ b :=
  add_eq_right_iff_mul_omega0_le.mp h

/-- `ω^{logend α}` divides `α` (the supremum in the definition of `logend` is attained). -/
theorem opow_logend_dvd {α : Ordinal.{0}} (h : α ≠ 0) : ω ^ logend α ∣ α := by
  unfold logend
  rw [if_neg h]
  set D : Set Ordinal.{0} := {γ | ω ^ γ ∣ α} with hD
  have hbdd : BddAbove D :=
    ⟨α, fun γ hγ => le_trans (right_le_opow γ one_lt_omega0) (Ordinal.le_of_dvd h hγ)⟩
  have hne : D.Nonempty := ⟨0, by simp [hD]⟩
  have hdown : ∀ γ < sSup D, ω ^ γ ∣ α := fun γ hγ => by
    obtain ⟨d, hd, hγd⟩ := exists_lt_of_lt_csSup hne hγ
    exact dvd_trans (opow_dvd_opow ω hγd.le) hd
  by_contra hnd
  have hs0 : sSup D ≠ 0 := by
    intro e; apply hnd; rw [e, opow_zero]; exact one_dvd _
  have hlim : IsSuccLimit (sSup D) := by
    rcases zero_or_succ_or_isSuccLimit (sSup D) with e | ⟨t, e⟩ | hl
    · exact absurd e hs0
    · exfalso
      have ht : t < sSup D := by rw [← e]; exact Order.lt_succ t
      obtain ⟨d, hd, htd⟩ := exists_lt_of_lt_csSup hne ht
      have hds : d ≤ sSup D := le_csSup hbdd hd
      have : sSup D ≤ d := by rw [← e]; exact Order.succ_le_of_lt htd
      exact hnd (le_antisymm hds this ▸ hd)
    · exact hl
  have hpos : ω ^ sSup D ≠ 0 := (opow_pos _ omega0_pos).ne'
  have hr : α % ω ^ sSup D ≠ 0 := fun e => hnd ((Ordinal.dvd_iff_mod_eq_zero).mpr e)
  have hrlt : α % ω ^ sSup D < ω ^ sSup D := Ordinal.mod_lt α hpos
  obtain ⟨γ, hγ, hrγ⟩ := (lt_opow_of_isSuccLimit omega0_ne_zero hlim).mp hrlt
  have h1 : ω ^ γ ∣ ω ^ sSup D * (α / ω ^ sSup D) :=
    dvd_mul_of_dvd_left (opow_dvd_opow ω hγ.le) _
  have h2 : ω ^ γ ∣ ω ^ sSup D * (α / ω ^ sSup D) + α % ω ^ sSup D := by
    rw [Ordinal.div_add_mod]; exact hdown γ hγ
  have h3 := (dvd_add_iff h1).mp h2
  exact absurd (Ordinal.le_of_dvd hr h3) (not_le.mpr hrγ)

theorem opow_dvd_of_le_logend {α γ : Ordinal.{0}} (h : α ≠ 0) (hγ : γ ≤ logend α) :
    ω ^ γ ∣ α :=
  dvd_trans (opow_dvd_opow ω hγ) (opow_logend_dvd h)

theorem logend_le_self (α : Ordinal.{0}) : logend α ≤ α := by
  by_cases h : α = 0
  · unfold logend; rw [if_pos h, h]
  · exact le_trans (right_le_opow _ one_lt_omega0) (Ordinal.le_of_dvd h (opow_logend_dvd h))

theorem logend_zero : logend 0 = 0 := by unfold logend; rw [if_pos rfl]

/-- No multiple of `ω^z` lies strictly between two consecutive multiples. -/
theorem dvd_gap {z a b : Ordinal.{0}} (ha : ω ^ z ∣ a) (hb : ω ^ z ∣ b) (h1 : a < b)
    (h2 : b < a + ω ^ z) : False := by
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨t, rfl⟩ := hb
  have hp : 0 < ω ^ z := opow_pos z omega0_pos
  have hst : s < t := (mul_lt_mul_iff_right₀ hp).mp h1
  rw [← mul_add_one] at h2
  have := (mul_lt_mul_iff_right₀ hp).mp h2
  exact absurd (Order.lt_add_one_iff.mp this) (not_le.mpr hst)

/-- A sum of principals `≥ ω^z` is divisible by `ω^z`. -/
theorem opow_dvd_sum {z : Ordinal.{0}} :
    ∀ {l : List Ordinal.{0}}, (∀ x ∈ l, Pr x ∧ ω ^ z ≤ x) → ω ^ z ∣ l.sum
  | [], _ => by simp
  | a :: t, h => by
    rw [List.sum_cons]
    obtain ⟨hP, hle⟩ := h a (by simp)
    obtain ⟨e, rfl⟩ := pr_iff.mp hP
    have hze : z ≤ e := (opow_le_opow_iff_right one_lt_omega0).mp hle
    exact opow_dvd_add (opow_dvd_opow ω hze) (opow_dvd_sum (fun x hx => h x (by simp [hx])))

theorem opow_inj' {a b : Ordinal.{0}} (h : ω ^ a = ω ^ b) : a = b :=
  le_antisymm ((opow_le_opow_iff_right one_lt_omega0).mp h.le)
    ((opow_le_opow_iff_right one_lt_omega0).mp h.ge)

/-- `α ≤₁ x` for `α ∈ (1, T¹ ∩ Ω_1)` forces `x < T¹ ∩ Ω_1` ([W07b] Cor 5.10). -/
theorem lt_T1bound_of_le1 {α x : Ordinal.{0}} (h1 : 1 < α) (hα : α < T1bound) (h : le1 α x) :
    x < T1bound := by
  by_contra hx
  push Not at hx
  obtain ⟨β, hβ, hn⟩ := not_lt1_infty h1 hα
  have hαT : le1 α T1bound := le1_of_le hα.le hx h
  apply hn
  rcases le_or_gt T1bound β with hb | hb
  · exact le1_trans hαT (le1_T1bound hb)
  · exact le1_of_le hβ hb.le hαT

/-! ## The witness condition and the hypotheses -/

/-- **The witness condition** (condition (C2) of Theorem S⁺). -/
def WitS (y b : Ordinal.{0}) : Prop :=
  (¬ InE y → ∀ l, ANF l → y = ω ^ l.sum → ω ^ l.dropLast.sum ≤ b) ∧
    (InE y → ∀ γ, InE γ → b < γ → γ < y → piInv γ y (lam γ) < lam y)

theorem WitS.mono {y b b' : Ordinal.{0}} (h : WitS y b) (hb : b ≤ b') : WitS y b' :=
  ⟨fun hE l hl hy => le_trans (h.1 hE l hl hy) hb,
    fun hE γ hγ hbγ hγy => h.2 hE γ hγ (lt_of_le_of_lt hb hbγ) hγy⟩

/-- **The hypotheses of Theorem S⁺** at the base `σ`, for the set `S` and the map `h`. -/
structure SPHyp (σ : Ordinal.{0}) (S : Finset Ordinal.{0}) (h : Ordinal.{0} → Ordinal.{0}) :
    Prop where
  one_le : 1 ≤ σ
  base_mem : σ ∈ S
  zero_mem : (0 : Ordinal.{0}) ∈ S
  lt_T : ∀ x ∈ S, x < T1bound
  closed : ∀ l, ANF l → l.sum ∈ S → (∀ x ∈ l, x ∈ S) ∧ ∀ i, (l.take i).sum ∈ S
  lh_mem : ∀ y ∈ S, Pr y → σ < y → ∃ δ ∈ S, IsLh y δ
  wit : ∀ y ∈ S, Pr y → σ < y → ∃ b ∈ S, b < y ∧ WitS y b
  mono : StrictMonoOn h S
  add : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S → h (a + b) = h a + h b
  base : ∀ x ∈ S, x ≤ σ → x ≤ h x
  keep1 : ∀ y ∈ S, ∀ w ∈ S, Pr y → σ < y → le1 y w → h y < T1bound → le1 (h y) (h w)

namespace SPHyp

variable {σ : Ordinal.{0}} {S : Finset Ordinal.{0}} {h : Ordinal.{0} → Ordinal.{0}}

theorem h_zero (H : SPHyp σ S h) : h 0 = 0 := by
  have := H.add 0 H.zero_mem 0 H.zero_mem (by rw [add_zero]; exact H.zero_mem)
  rw [add_zero] at this
  exact (add_left_cancel (a := h 0) (b := 0) (c := h 0) (by rw [add_zero]; exact this)).symm

/-- `h` of an additive normal form is the sum of the values. -/
theorem h_sum (H : SPHyp σ S h) :
    ∀ l : List Ordinal.{0}, ANF l → l.sum ∈ S → h l.sum = (l.map h).sum := by
  intro l
  induction l using List.reverseRecOn with
  | nil => intro _ _; simp [H.h_zero]
  | append_singleton l' c ih =>
    intro hl hs
    have hl' : ANF l' := hl.sublist (List.sublist_append_left _ _)
    have hcl := H.closed _ hl hs
    have hl'S : l'.sum ∈ S := by
      have := hcl.2 l'.length
      rwa [List.take_left] at this
    have hcS : c ∈ S := hcl.1 c (by simp)
    rw [List.sum_append, List.sum_singleton] at hs ⊢
    rw [H.add _ hl'S _ hcS hs, ih hl' hl'S, List.map_append, List.sum_append]
    simp

/-- A non-principal element splits into two smaller elements of `S`. -/
theorem exists_split (H : SPHyp σ S h) {q : Ordinal.{0}} (hqS : q ∈ S) (hq0 : q ≠ 0)
    (hP : ¬ Pr q) : ∃ s ∈ S, ∃ c ∈ S, s < q ∧ c < q ∧ s + c = q := by
  obtain ⟨l, hl, hls⟩ := exists_anf_of_lt (H.lt_T q hqS)
  rcases List.eq_nil_or_concat l with rfl | ⟨l', c, rfl⟩
  · simp at hls; exact absurd hls.symm hq0
  rw [List.concat_eq_append] at hl hls
  rcases l' with _ | ⟨a, t⟩
  · simp at hls
    exact absurd (hls ▸ hl.1 c (by simp)) hP
  set l' := a :: t with hl'd
  have hcl := H.closed _ hl (hls ▸ hqS)
  have hsS : l'.sum ∈ S := by
    have := hcl.2 l'.length
    rwa [List.take_left] at this
  have hcS : c ∈ S := hcl.1 c (by simp)
  have hsum : l'.sum + c = q := by rw [← hls, List.sum_append, List.sum_singleton]
  have hc0 : 0 < c := (hl.1 c (by simp)).pos
  have hca : c ≤ a := (List.pairwise_append.mp hl.2).2.2 a (by simp [hl'd]) c (by simp)
  have has : a ≤ l'.sum := mem_le_sum (by simp [hl'd])
  refine ⟨l'.sum, hsS, c, hcS, ?_, ?_, hsum⟩
  · rw [← hsum]; exact lt_add_of_pos_right _ hc0
  · rw [← hsum]
    exact lt_of_lt_of_le (lt_add_of_pos_right c hc0) (add_le_add (le_trans hca has) le_rfl)

end SPHyp

/-! ## Step 3: a non-epsilon minimal counterexample is impossible -/

theorem sp_step3 {σ : Ordinal.{0}} {S : Finset Ordinal.{0}} {h : Ordinal.{0} → Ordinal.{0}}
    (H : SPHyp σ S h) {q : Ordinal.{0}} (hqS : q ∈ S) (hP : Pr q) (hσq : σ < q)
    (hlt : h q < q) (hmin : ∀ x ∈ S, x < q → x ≤ h x) (hE : ¬ InE q) : False := by
  obtain ⟨b, hbS, hbq, hW⟩ := H.wit q hqS hP hσq
  have hqT := H.lt_T q hqS
  have hbqs : b < h q := lt_of_le_of_lt (hmin b hbS hbq) (H.mono hbS hqS hbq)
  have habs : ∀ x ∈ S, x < q → h x * ω ≤ h q := by
    intro x hx hxq
    have e : x + q = q := hP.add_eq hxq
    have := H.add x hx q hqS (by rw [e]; exact hqS)
    rw [e] at this
    exact mul_omega_le_of_add_eq this.symm
  have h1q : 1 < q := lt_of_le_of_lt H.one_le hσq
  obtain ⟨ζ, rfl⟩ := pr_iff.mp hP
  have hζT : ζ < T1bound := lt_of_le_of_lt (right_le_opow ζ one_lt_omega0) hqT
  obtain ⟨l, hl, hls⟩ := exists_anf_of_lt hζT
  have hζ0 : ζ ≠ 0 := by rintro rfl; rw [opow_zero] at h1q; exact lt_irrefl _ h1q
  rcases List.eq_nil_or_concat l with rfl | ⟨l', c, rfl⟩
  · simp at hls; exact hζ0 hls.symm
  rw [List.concat_eq_append] at hl hls
  have hwit := hW.1 hE (l' ++ [c]) hl (by rw [hls])
  rw [List.dropLast_concat] at hwit
  have hcP : Pr c := hl.1 c (by simp)
  obtain ⟨z, rfl⟩ := pr_iff.mp hcP
  have hsum : ζ = l'.sum + ω ^ z := by rw [← hls, List.sum_append, List.sum_singleton]
  have hdvd : ω ^ z ∣ l'.sum := opow_dvd_sum (fun x hx =>
    ⟨hl.1 x (by simp [hx]), (List.pairwise_append.mp hl.2).2.2 x hx _ (by simp)⟩)
  by_cases hz : z = 0
  · subst hz
    rw [opow_zero] at hsum
    have hq : ω ^ ζ = ω ^ l'.sum * ω := by rw [hsum, opow_add, opow_one]
    have h1 := habs b hbS hbq
    have h2 : b * ω ≤ h b * ω := mul_le_mul_left (hmin b hbS hbq) ω
    have h3 : ω ^ l'.sum * ω ≤ b * ω := mul_le_mul_left hwit ω
    have h4 : ω ^ l'.sum * ω ≤ h (ω ^ ζ) := le_trans h3 (le_trans h2 h1)
    rw [← hq] at h4
    exact absurd hlt (not_lt.mpr h4)
  have hz0 : 0 < z := pos_iff_ne_zero.mpr hz
  have hlog : logend ζ = z := by rw [hsum]; exact logend_add_opow hdvd
  have hζq : ζ < ω ^ ζ :=
    lt_of_le_of_ne (right_le_opow ζ one_lt_omega0) (fun e => hE (by unfold InE; rw [← e]; exact e.symm))
  have hzζ : ω ^ z ≤ ζ := by rw [hsum]; exact le_add_self
  have hzq : z < ω ^ ζ :=
    lt_of_le_of_lt (le_trans (right_le_opow z one_lt_omega0) hzζ) hζq
  have hz1q : z + 1 < ω ^ ζ := hP.add_lt hzq h1q
  have hle1 : le1 (ω ^ ζ) (ω ^ ζ + z) := (le1_add_iff hz0 hzq.le).mpr ⟨ζ, rfl, hlog.ge⟩
  obtain ⟨δ, hδS, hδ⟩ := H.lh_mem _ hqS hP hσq
  have hδeq : δ = ω ^ ζ + z := by
    apply le_antisymm _ (hδ.2 _ hle1)
    by_contra hc
    push Not at hc
    have h' : ω ^ ζ + (z + 1) ≤ δ := by rw [← add_assoc]; exact Order.add_one_le_of_lt hc
    have hl1 : le1 (ω ^ ζ) (ω ^ ζ + (z + 1)) := le1_of_le le_self_add h' hδ.1
    obtain ⟨α', hα', hz1⟩ := (le1_add_iff (by simp) hz1q.le).mp hl1
    rw [← opow_inj' hα', hlog] at hz1
    exact absurd hz1 (not_le.mpr (Order.lt_add_one_iff.mpr le_rfl))
  -- the additive normal form of `δ = q + z`
  obtain ⟨lz, hlz, hlzs⟩ := exists_anf_of_lt (lt_trans hzq hqT)
  have hlzle : ∀ x ∈ lz, x < ω ^ ζ := fun x hx =>
    lt_of_le_of_lt (hlzs ▸ mem_le_sum hx) hzq
  have hanf : ANF (ω ^ ζ :: lz) :=
    ⟨fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hP
      · exact hlz.1 x hx,
     List.pairwise_cons.mpr ⟨fun x hx => (hlzle x hx).le, hlz.2⟩⟩
  have hsδ : (ω ^ ζ :: lz).sum = δ := by rw [List.sum_cons, hlzs, hδeq]
  have hcl := H.closed _ hanf (hsδ ▸ hδS)
  have hδh : h δ = h (ω ^ ζ) + (lz.map h).sum := by
    rw [← hsδ, H.h_sum _ hanf (hsδ ▸ hδS)]; simp
  have hlzS : ∀ x ∈ lz, x ∈ S := fun x hx => hcl.1 x (by simp [hx])
  have hzE : z ≤ (lz.map h).sum := by
    rw [← hlzs]; exact sum_le_sum_map (fun x hx => hmin x (hlzS x hx) (hlzle x hx))
  -- `h(q)` is in `L`
  have hqδ : ω ^ ζ < δ := by rw [hδeq]; exact lt_add_of_pos_right _ hz0
  have hk := H.keep1 _ hqS δ hδS hP hσq hδ.1 (lt_trans hlt hqT)
  have hqsL : InL (h (ω ^ ζ)) := (exists_le1_gt_iff _).mp ⟨h δ, H.mono hqS hδS hqδ, hk⟩
  have hEq : (lz.map h).sum < h (ω ^ ζ) := sum_lt_of_forall_lt hqsL.1 (fun y hy => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact H.mono (hlzS x hx) hqS (hlzle x hx))
  have hl1 : le1 (h (ω ^ ζ)) (h (ω ^ ζ) + z) :=
    le1_of_le le_self_add (by rw [hδh]; exact (add_le_add_iff_left _).mpr hzE) hk
  obtain ⟨g', hg', hzg'⟩ := (le1_add_iff hz0 (le_trans hzE hEq.le)).mp hl1
  have hg'0 : g' ≠ 0 := by
    rintro rfl; rw [logend_zero] at hzg'; exact absurd hzg' (not_le.mpr hz0)
  have hdg := opow_dvd_of_le_logend hg'0 hzg'
  have hlo : l'.sum < g' := by
    have := lt_of_le_of_lt hwit (hg' ▸ hbqs)
    exact (opow_lt_opow_iff_right one_lt_omega0).mp this
  have hhi : g' < l'.sum + ω ^ z := by
    rw [← hsum]
    have := hg' ▸ hlt
    exact (opow_lt_opow_iff_right one_lt_omega0).mp this
  exact dvd_gap hdvd hdg hlo hhi

/-! ## Step 4: an epsilon minimal counterexample is impossible (base change) -/

theorem piInv_mono {γ α x y : Ordinal.{0}} (hγ : InE γ) (hα : InE α) (h1 : 1 < γ)
    (hγα : γ < α) (hαT : α < T1bound) (hxy : x ≤ y) (hy : y < T1bound) :
    piInv γ α x ≤ piInv γ α y := by
  rcases hxy.lt_or_eq with h | rfl
  · exact (piInv_strictMono hγ hα h1 hγα hαT h hy).le
  · exact le_rfl

theorem sp_step4 {n : ℕ}
    (IH : ∀ m < n, ∀ {σ : Ordinal.{0}} {S : Finset Ordinal.{0}} {h : Ordinal.{0} → Ordinal.{0}},
      (S.filter (fun x => σ < x)).card = m → SPHyp σ S h → ∀ y ∈ S, y ≤ h y)
    {σ : Ordinal.{0}} {S : Finset Ordinal.{0}} {h : Ordinal.{0} → Ordinal.{0}}
    (hn : (S.filter (fun x => σ < x)).card = n) (H : SPHyp σ S h) {q : Ordinal.{0}}
    (hqS : q ∈ S) (hP : Pr q) (hσq : σ < q) (hlt : h q < q)
    (hmin : ∀ x ∈ S, x < q → x ≤ h x) (hE : InE q) : False := by
  have hqT := H.lt_T q hqS
  have h1q : 1 < q := lt_of_le_of_lt H.one_le hσq
  have hqsT : h q < T1bound := lt_trans hlt hqT
  have h1qs : 1 < h q := lt_of_le_of_lt H.one_le
    (lt_of_le_of_lt (H.base σ H.base_mem le_rfl) (H.mono H.base_mem hqS hσq))
  have hq0 : 0 < q := lt_trans zero_lt_one h1q
  have hqs0 : 0 < h q := lt_trans zero_lt_one h1qs
  -- `q ≤₁ q + q`
  have hlogq : logend q = q := by
    have := logend_add_opow (β := 0) (γ := q) (dvd_zero _)
    rwa [zero_add, hE] at this
  have hqq : le1 q (q + q) := (le1_add_iff hq0 le_rfl).mpr ⟨q, hE.symm, hlogq.ge⟩
  obtain ⟨L, hLS, hL⟩ := H.lh_mem q hqS hP hσq
  have hqqL : q + q ≤ L := hL.2 _ hqq
  have hqL : q ≤ L := le_trans le_self_add hqqL
  have hLT := H.lt_T L hLS
  -- `h(L) ≥ h(q) + h(q)`
  have hLbig : h q + h q ≤ h L := by
    obtain ⟨l, hl, hls⟩ := exists_anf_of_lt hLT
    have hlS := H.closed _ hl (hls ▸ hLS)
    have hhL := H.h_sum l hl (hls ▸ hLS)
    rw [hls] at hhL
    rcases l with _ | ⟨c1, rest⟩
    · simp at hls
      rw [← hls] at hqqL
      exact absurd hqqL (not_le.mpr (lt_of_lt_of_le hq0 le_self_add))
    have hc1S : c1 ∈ S := hlS.1 c1 (by simp)
    have hc1P : Pr c1 := hl.1 c1 (by simp)
    have hrest : ∀ x ∈ rest, x ≤ c1 := fun x hx => (List.pairwise_cons.mp hl.2).1 x hx
    have hc1q : q ≤ c1 := by
      by_contra hc
      push Not at hc
      have : L < q := by
        rw [← hls]
        exact sum_lt_of_forall_lt hP (fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hc
          · exact lt_of_le_of_lt (hrest x hx) hc)
      exact absurd hqL (not_le.mpr this)
    rw [hhL, List.map_cons, List.sum_cons]
    rcases hc1q.lt_or_eq with hc1q | rfl
    · -- `c1 > q`: absorption
      have e : q + c1 = c1 := hc1P.add_eq hc1q
      have := H.add q hqS c1 hc1S (by rw [e]; exact hc1S)
      rw [e] at this
      have h1 := mul_omega_le_of_add_eq this.symm
      have h2 : h q + h q ≤ h q * ω := by
        calc h q + h q ≤ h q + h q * ω :=
              (add_le_add_iff_left _).mpr (Ordinal.le_mul_left _ omega0_pos)
          _ = h q * ω := by rw [← mul_one_add, one_add_omega0]
      exact le_trans h2 (le_trans h1 le_self_add)
    · -- `c1 = q`: the second summand is `q`
      rcases rest with _ | ⟨c2, rest'⟩
      · simp at hls
        rw [← hls] at hqqL
        exact absurd hqqL (not_le.mpr (lt_add_of_pos_right _ hq0))
      have hc2S : c2 ∈ S := hlS.1 c2 (by simp)
      have hc2q : c2 = q := by
        apply le_antisymm (hrest c2 (by simp))
        by_contra hc
        push Not at hc
        have hr2 : ∀ x ∈ rest', x ≤ c2 :=
          fun x hx => (List.pairwise_cons.mp (List.pairwise_cons.mp hl.2).2).1 x hx
        have : (c2 :: rest').sum < q := sum_lt_of_forall_lt hP (fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hc
          · exact lt_of_le_of_lt (hr2 x hx) hc)
        rw [← hls, List.sum_cons] at hqqL
        exact absurd hqqL (not_le.mpr ((add_lt_add_iff_left _).mpr this))
      subst hc2q
      rw [List.map_cons, List.sum_cons]
      exact (add_le_add_iff_left _).mpr le_self_add
  have hle1L : le1 (h q) (h L) := H.keep1 q hqS L hLS hP hσq hL.1 hqsT
  -- `h(q)` is an epsilon number
  have hqsE : InE (h q) := by
    obtain ⟨g', hg', hqg'⟩ := (le1_add_iff hqs0 le_rfl).mp (le1_of_le le_self_add hLbig hle1L)
    have hg'0 : g' ≠ 0 := by
      rintro rfl; rw [logend_zero] at hqg'; exact absurd hqg' (not_le.mpr hqs0)
    have h1 : h q ≤ g' := le_trans hqg' (logend_le_self g')
    have h2 : g' ≤ h q := hg' ▸ right_le_opow g' one_lt_omega0
    have e : g' = h q := le_antisymm h2 h1
    unfold InE; rw [← e]; exact hg'.symm.trans e.symm
  obtain ⟨b, hbS, hbq, hW⟩ := H.wit q hqS hP hσq
  have hbqs : b < h q := lt_of_le_of_lt (hmin b hbS hbq) (H.mono hbS hqS hbq)
  have hwit : piInv (h q) q (lam (h q)) < lam q := hW.2 hE (h q) hqsE hbqs hlt
  -- notation for the base change
  set qs := h q with hqs_def
  have hπ := And.intro hqsE (And.intro hE (And.intro h1qs (And.intro hlt hqT)))
  have hbs := bddAbove_minSet hqsT
  have hbq' := bddAbove_minSet hqT
  obtain ⟨hmk, hkqs, -⟩ := kap_small hbs hqs0 (lt_nextL qs)
  have hqs2 : le1 qs (qs + qs) := (le1_add_iff hqs0 le_rfl).mpr ⟨qs, hqsE.symm, by
    have := logend_add_opow (β := 0) (γ := qs) (dvd_zero _)
    rw [zero_add, hqsE] at this; exact this.ge⟩
  have hqslam : qs ≤ lam qs := le_lam (le_theta_of_minT hbs hmk) (by rw [hkqs]; exact hqs2)
  obtain ⟨-, hle1lam, hlhiff⟩ := lam_spec hbs
  obtain ⟨Ls, hLs⟩ := exists_isLh hqsT
  have hLsT : Ls < T1bound := lt_T1bound_of_le1 h1qs hqsT hLs.1
  have hKs : IsLh (kap qs (lam qs)) Ls := (hlhiff Ls).mp hLs
  have hKsT : kap qs (lam qs) < T1bound := lt_T1bound_of_le1 h1qs hqsT hle1lam
  have hlamT : lam qs < T1bound := lt_of_le_of_lt (le_kap _ _) hKsT
  have hKsgt : qs < kap qs (lam qs) := by
    have := (kap_strictMono qs).monotone hqslam
    rw [hkqs] at this
    exact lt_of_lt_of_le (lt_add_of_pos_right _ hqs0) this
  set μ := piInv qs q (lam qs) with hμ
  have hkey : piInv qs q (kap qs (lam qs)) = kap q μ := by
    rcases hqslam.lt_or_eq with hgt | heq
    · exact (piInv_kap hqsE hE h1qs hlt hqT hgt hlamT).symm
    · rw [hμ, ← heq, hkqs, piInv_base hqsE hE h1qs hlt hqT]
      have hsT : qs + qs < T1bound := lt_of_le_of_lt (hLs.2 _ hqs2) hLsT
      rw [piInv_add hqsE hE h1qs hlt hqT hsT, piInv_base hqsE hE h1qs hlt hqT]
      exact ((kap_small hbq' hq0 (lt_nextL q)).2.1).symm
  have hlhx : IsLh (kap q μ) (piInv qs q Ls) := by
    rw [← hkey]; exact piInv_lh hqsE hE h1qs hlt hqT hKsgt hKsT hKs
  have hqμ : q ≤ μ := by
    have := piInv_mono hqsE hE h1qs hlt hqT hqslam hlamT
    rwa [piInv_base hqsE hE h1qs hlt hqT] at this
  obtain ⟨hlamθ, -, hlhq⟩ := lam_spec hbq'
  obtain ⟨δ, hδ, hall⟩ := kap_add hbq' (lt_of_lt_of_le hq0 hqμ)
    (lt_of_lt_of_le hwit hlamθ)
  have hδ1 : 1 < δ := lt_of_lt_of_le h1q (le_trans hqμ (le_trans (le_kap q μ) hδ.le))
  have hsucc := (hall 1 zero_lt_one (lt_trans hδ1 (lt_nextL δ))).2.1
  have hLsδ : piInv qs q Ls = δ := hlhx.unique hδ
  have hKL : kap q (lam q) ≤ L := ((hlhq L).mp hL).le
  have hstep : piInv qs q Ls < L := by
    rw [hLsδ]
    calc δ < δ + 1 := Order.lt_add_one_iff.mpr le_rfl
      _ = kap q (μ + 1) := hsucc.symm
      _ ≤ kap q (lam q) := (kap_strictMono q).monotone (Order.add_one_le_of_lt hwit)
      _ ≤ L := hKL
  have hhLLs : h L ≤ Ls := hLs.2 _ hle1L
  have hfinal : piInv qs q (h L) < L :=
    lt_of_le_of_lt (piInv_mono hqsE hE h1qs hlt hqT hhLLs hLsT) hstep
  -- the base change
  set S' := S.filter (fun x => x ≤ L) with hS'
  set h' : Ordinal.{0} → Ordinal.{0} := fun x => piInv qs q (h x) with hh'
  have memS' : ∀ {x}, x ∈ S' ↔ x ∈ S ∧ x ≤ L := by intro x; simp [hS']
  have hvalLe : ∀ x ∈ S', h x ≤ Ls := by
    intro x hx
    obtain ⟨hxS, hxL⟩ := memS'.mp hx
    rcases le_or_gt x q with hxq | hxq
    · rcases hxq.lt_or_eq with hxq | rfl
      · exact le_trans (H.mono hxS hqS hxq).le (hLs.1 |> le1_le)
      · exact le1_le hLs.1
    · exact hLs.2 _ (H.keep1 q hqS x hxS hP hσq (le1_of_le hxq.le hxL hL.1) hqsT)
  have hvalT : ∀ x ∈ S', h x < T1bound := fun x hx => lt_of_le_of_lt (hvalLe x hx) hLsT
  have H' : SPHyp q S' h' := by
    refine ⟨h1q.le, memS'.mpr ⟨hqS, hqL⟩, memS'.mpr ⟨H.zero_mem, zero_le⟩,
      fun x hx => H.lt_T x (memS'.mp hx).1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro l hl hs
      obtain ⟨hsS, hsL⟩ := memS'.mp hs
      obtain ⟨h1, h2⟩ := H.closed l hl hsS
      exact ⟨fun x hx => memS'.mpr ⟨h1 x hx, le_trans (mem_le_sum hx) hsL⟩,
        fun i => memS'.mpr ⟨h2 i, le_trans (take_sum_le l i) hsL⟩⟩
    · intro y hy hyP hqy
      obtain ⟨hyS, hyL⟩ := memS'.mp hy
      obtain ⟨δy, hδyS, hδy⟩ := H.lh_mem y hyS hyP (lt_trans hσq hqy)
      have hqy1 : le1 q y := le1_of_le hqy.le hyL hL.1
      exact ⟨δy, memS'.mpr ⟨hδyS, hL.2 _ (le1_trans hqy1 hδy.1)⟩, hδy⟩
    · intro y hy hyP hqy
      obtain ⟨hyS, hyL⟩ := memS'.mp hy
      obtain ⟨b', hb'S, hb'y, hW'⟩ := H.wit y hyS hyP (lt_trans hσq hqy)
      refine ⟨max b' q, ?_, max_lt hb'y hqy, hW'.mono (le_max_left _ _)⟩
      rcases le_total b' q with hb | hb
      · rw [max_eq_right hb]; exact memS'.mpr ⟨hqS, hqL⟩
      · rw [max_eq_left hb]; exact memS'.mpr ⟨hb'S, le_trans hb'y.le hyL⟩
    · intro x hx y hy hxy
      exact piInv_strictMono hqsE hE h1qs hlt hqT
        (H.mono (memS'.mp hx).1 (memS'.mp hy).1 hxy) (hvalT y hy)
    · intro a ha c hc hac
      show piInv qs q (h (a + c)) = piInv qs q (h a) + piInv qs q (h c)
      rw [H.add a (memS'.mp ha).1 c (memS'.mp hc).1 (memS'.mp hac).1]
      exact piInv_add hqsE hE h1qs hlt hqT
        (by rw [← H.add a (memS'.mp ha).1 c (memS'.mp hc).1 (memS'.mp hac).1]; exact hvalT _ hac)
    · intro x hx hxq
      obtain ⟨hxS, -⟩ := memS'.mp hx
      show x ≤ piInv qs q (h x)
      rcases hxq.lt_or_eq with hxq | rfl
      · rw [piInv_fix hqsE hE h1qs hlt hqT (H.mono hxS hqS hxq)]
        exact hmin x hxS hxq
      · rw [piInv_base hqsE hE h1qs hlt hqT]
    · intro y hy w hw hyP hqy hyw _
      obtain ⟨hyS, hyL⟩ := memS'.mp hy
      obtain ⟨hwS, -⟩ := memS'.mp hw
      have hk := H.keep1 y hyS w hwS hyP (lt_trans hσq hqy) hyw (hvalT y hy)
      have hqsu : qs < h y := H.mono hqS hyS hqy
      have huT := hvalT y hy
      obtain ⟨δu, hδu⟩ := exists_isLh huT
      have hδuT : δu < T1bound := lt_T1bound_of_le1 (lt_trans h1qs hqsu) huT hδu.1
      have hlh := piInv_lh hqsE hE h1qs hlt hqT hqsu huT hδu
      have hw1 : h w ≤ δu := hδu.2 _ hk
      exact le1_of_le (piInv_mono hqsE hE h1qs hlt hqT (le1_le hk) (lt_of_le_of_lt hw1 hδuT))
        (piInv_mono hqsE hE h1qs hlt hqT hw1 hδuT) hlh.1
  -- fewer elements above the base
  have hsub : S'.filter (fun x => q < x) ⊂ S.filter (fun x => σ < x) := by
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨q, Finset.mem_filter.mpr ⟨hqS, hσq⟩, fun hm =>
        lt_irrefl q (Finset.mem_filter.mp hm).2⟩
    · intro x hx
      obtain ⟨hxS', hqx⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨(memS'.mp hxS').1, lt_trans hσq hqx⟩
  have hcard := Finset.card_lt_card hsub
  rw [hn] at hcard
  have := IH _ hcard rfl H' L (memS'.mpr ⟨hLS, le_rfl⟩)
  exact absurd hfinal (not_lt.mpr this)

/-! ## Theorem S⁺ -/

/-- **Theorem S⁺**: under `SPHyp σ S h`, `h(y) ≥ y` on `S`. -/
theorem splus_aux : ∀ (n : ℕ) {σ : Ordinal.{0}} {S : Finset Ordinal.{0}}
    {h : Ordinal.{0} → Ordinal.{0}},
    (S.filter (fun x => σ < x)).card = n → SPHyp σ S h → ∀ y ∈ S, y ≤ h y := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro σ S h hn H
  by_contra hcon
  push Not at hcon
  obtain ⟨y0, hy0S, hy0⟩ := hcon
  set T := S.filter (fun y => h y < y) with hT
  have hTne : T.Nonempty := ⟨y0, Finset.mem_filter.mpr ⟨hy0S, hy0⟩⟩
  obtain ⟨hqS, hlt⟩ := Finset.mem_filter.mp (T.min'_mem hTne)
  set q := T.min' hTne with hq
  have hmin : ∀ x ∈ S, x < q → x ≤ h x := by
    intro x hx hxq
    by_contra hc
    push Not at hc
    exact absurd (T.min'_le x (Finset.mem_filter.mpr ⟨hx, hc⟩)) (not_le.mpr hxq)
  have hq0 : q ≠ 0 := by
    intro e; rw [e] at hlt; exact absurd hlt (not_lt.mpr zero_le)
  have hσq : σ < q := by
    by_contra hc; push Not at hc
    exact absurd (H.base q hqS hc) (not_le.mpr hlt)
  by_cases hP : Pr q
  · by_cases hE : InE q
    · exact sp_step4 (fun m hm => IH m hm) hn H hqS hP hσq hlt hmin hE
    · exact sp_step3 H hqS hP hσq hlt hmin hE
  · obtain ⟨s, hsS, c, hcS, hsq, hcq, hsc⟩ := H.exists_split hqS hq0 hP
    have := H.add s hsS c hcS (hsc ▸ hqS)
    rw [hsc] at this
    have hge : q ≤ h q := by
      rw [this, ← hsc]; exact add_le_add (hmin s hsS hsq) (hmin c hcS hcq)
    exact absurd hlt (not_lt.mpr hge)

theorem splus {σ : Ordinal.{0}} {S : Finset Ordinal.{0}} {h : Ordinal.{0} → Ordinal.{0}}
    (H : SPHyp σ S h) : ∀ y ∈ S, y ≤ h y :=
  splus_aux _ rfl H

end Googology.Trans.PSS.Main

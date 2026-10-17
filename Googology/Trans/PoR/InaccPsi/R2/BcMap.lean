import Googology.Trans.PoR.InaccPsi.R2.BcNF
import Googology.Trans.PoR.InaccPsi.R2.QqName

/-!
# The base change `B_k` on ordinals and its arithmetic

`L(ξ) = ψ_{Ω₁}(Ω_ω·2 + P'·ξ)` (`ncL`), `L(ω) = ψ_{Ω₁}(α_ω)`.  Every `x < L(ω)` is the value of a
unique normal form `bcNf S x` (Lemma L, `CSet_inter_Om1`, and `existsUnique_NF`).

* `bcB S k x = |σ(nf x)|` with `σ = bcSig (bcPre (k+1)) bcPreW` (**the base change `B_k`**: the
  η-base change from `L(k+1)` to `L(ω)`; it rewrites every `ψ_{Ω₁}`-argument
  `Ω_ω·2 + P'·(k+1) + ρ` to `Ω_ω·2 + P'·ω + B_k(ρ)` and commutes with all other constructors);
* `bcB_lt_iff` (strictly increasing on `[0, L(ω))`), `bcB_add` (`B(x + y) = B x + B y`),
  `bcB_indec` (keeps indecomposables), `bcB_fix` (`B = id` on `[0, L(k+1))`),
  `bcB_base` (`B(L(k+1)) = L(ω)`), `bcB_base1` (`B(L(k+2)) = L(ω+1)`);
* on `[0, L(k+2))`: `bcB_mono`, `bcB_bound` (`B x < L(ω+1)`), `bcB_addIff` (keeps and reflects the
  graph of `+`), `bcB_closed` (closed range, [C09] Def 2.3).

No axiom.

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Bc

open Googology.Notation.InaccPsi Googology.Notation.InaccPsi.Term

section Map

variable (S : InaccSeq.{0})

open Classical in
/-- The normal form of `x` (`zero` outside `⋃_a Cl(a, 0)`). -/
noncomputable def bcNf (x : Ordinal.{0}) : Term :=
  if h : x ∈ ⋃ a, S.CSet a 0 then Classical.choose (exists_NF S h) else zero

theorem bcNf_spec {x : Ordinal.{0}} (h : x ∈ ⋃ a, S.CSet a 0) :
    NF (bcNf S x) ∧ val S (bcNf S x) = x := by
  unfold bcNf; rw [dif_pos h]; exact Classical.choose_spec (exists_NF S h)

theorem bcNf_val {t : Term} (ht : NF t) : bcNf S (val S t) = t := by
  have hmem : val S t ∈ ⋃ a, S.CSet a 0 := Set.mem_iUnion.2 (exists_mem_CSet S t)
  exact eq_of_val_eq S (bcNf_spec S hmem).1 ht (bcNf_spec S hmem).2

theorem mem_of_lt_psi {A x : Ordinal.{0}} (h : x < S.psi A (Om 1)) : x ∈ ⋃ a, S.CSet a 0 := by
  have : x ∈ S.CSet A 0 ∩ Set.Iio (Om 1) := by
    rw [InaccSeq.CSet_inter_Om1]; exact h
  exact Set.mem_iUnion.2 ⟨A, this.1⟩

/-- **The base change `B_k`.** -/
noncomputable def bcB (k : ℕ) (x : Ordinal.{0}) : Ordinal.{0} :=
  val S (bcSig (bcPre (k + 1)) bcPreW (bcNf S x))

theorem ncPp_mul_omega : Nc.ncPp S * Ordinal.omega0 = Ordinal.omega0 ^ (Nc.ncPp S + 1) := by
  rw [Ordinal.opow_add, Ordinal.opow_one, Low.opow_eq_self_of_SC (Nc.ncPp_SC S)]

theorem ncL_omega_eq : Nc.ncL S Ordinal.omega0 = S.psi (bcAlphaW S) (Om 1) := by
  unfold Nc.ncL bcAlphaW; rw [ncPp_mul_omega]

theorem ncL_nat_eq (j : ℕ) : Nc.ncL S (j : Ordinal.{0}) = S.psi (bcAlpha S j) (Om 1) := rfl

theorem bcD_nf {x : Ordinal.{0}} (hx : x < Nc.ncL S Ordinal.omega0) : bcD S (bcNf S x) := by
  rw [ncL_omega_eq] at hx
  have h := bcNf_spec S (mem_of_lt_psi S hx)
  exact ⟨h.1, bcArgsLt_of_lt S h.1 (by rw [h.2]; exact hx)⟩

theorem val_nf {x : Ordinal.{0}} (hx : x < Nc.ncL S Ordinal.omega0) : val S (bcNf S x) = x := by
  rw [ncL_omega_eq] at hx
  exact (bcNf_spec S (mem_of_lt_psi S hx)).2

variable {S}

theorem bcB_lt_iff {k : ℕ} {x y : Ordinal.{0}} (hx : x < Nc.ncL S Ordinal.omega0)
    (hy : y < Nc.ncL S Ordinal.omega0) : bcB S k x < bcB S k y ↔ x < y := by
  unfold bcB
  rw [bc_lt_iff (bcD_nf S hx) (bcD_nf S hy), val_nf S hx, val_nf S hy]

theorem bcB_zero (k : ℕ) : bcB S k 0 = 0 := by
  unfold bcB
  rw [show (0 : Ordinal.{0}) = val S zero from rfl, bcNf_val S (t := zero) trivial, bcSig_zero]

/-- `σ` fixes the terms whose `ψ_{Ω₁}`-arguments are `< α_{k+1}`. -/
theorem bcSig_id {k : ℕ} : ∀ {t : Term}, NF t → bcArgsLt S (bcAlpha S (k + 1)) t →
    bcSig (bcPre (k + 1)) bcPreW t = t
  | zero, _, _ => by simp
  | inacc _, _, _ => by simp
  | inaccW, _, _ => by simp
  | add a b, h, hA => by rw [bcSig_add, bcSig_id h.1 hA.1, bcSig_id h.2.1 hA.2]
  | phi a b, h, hA => by rw [bcSig_phi, bcSig_id h.1 hA.1, bcSig_id h.2.1 hA.2]
  | om a, h, hA => by rw [bcSig_om, bcSig_id h.1 hA]
  | psiI n a, h, hA => by rw [bcSig_psiI, bcSig_id h.1 hA]
  | psiS s a, h, hA => by
    by_cases hs : s = zero
    · subst hs
      have ha := hA.2.2 rfl
      have hnp : ¬ (bcPre (k + 1)).isPrefixOf (bcSl a) = true := by
        intro hp
        have := (bc_pre_iff S h.2.1 (ha.trans (bcAlpha_lt_W S (k + 1)))).1 hp
        exact absurd ha (not_lt.2 this)
      rw [bcSig_psiS_zero, bcArg_of_not hnp, bcSig_id h.2.1 hA.2.1]
    · rw [bcSig_psiS_ne hs, bcSig_id h.1 hA.1, bcSig_id h.2.1 hA.2.1]

/-- **`B_k = id` on `[0, L(k+1))`.** -/
theorem bcB_fix {k : ℕ} {x : Ordinal.{0}} (hx : x < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) :
    bcB S k x = x := by
  have hxw : x < Nc.ncL S Ordinal.omega0 := hx.trans (Qq.qqL_lt_omega S (k + 1))
  have hD := bcD_nf S hxw
  have hA : bcArgsLt S (bcAlpha S (k + 1)) (bcNf S x) :=
    bcArgsLt_of_lt S hD.1 (by rw [val_nf S hxw]; exact hx)
  unfold bcB
  rw [bcSig_id hD.1 hA, val_nf S hxw]

/-- The term of `L(j)`. -/
def bcLt (j : ℕ) : Term := psiS zero (bcApp (bcPre j) zero)

theorem cmp_WW_pre (S : InaccSeq.{0}) (j : ℕ) : cmp (add tW tW) (bcApp (bcPre (j + 1)) zero) = .lt := by
  refine cmp_lt_of_val S NF_add_tW_tW (NF_pre (j + 1)) ?_
  rw [val_pre]
  show val S tW + val S tW < bcAlpha S (j + 1)
  rw [val_tW]; unfold bcAlpha
  exact lt_add_of_pos_right _ (mul_pos (Qq.qqPp_pos S) (by exact_mod_cast Nat.succ_pos j))

theorem NF_bcLt (S : InaccSeq.{0}) (j : ℕ) : NF (bcLt (j + 1)) := by
  refine ⟨trivial, NF_pre (j + 1), KLt_bcApp (fun p hp => ?_) trivial⟩
  simp only [bcPre, List.mem_cons, List.mem_replicate] at hp
  rcases hp with rfl | rfl | ⟨-, rfl⟩
  · exact KLt_tW _ _
  · exact KLt_tW _ _
  · exact KLt_tPp (cmp_WW_pre S j)

variable (S) in
theorem val_bcLt (j : ℕ) : val S (bcLt j) = Nc.ncL S (j : Ordinal.{0}) := by
  unfold bcLt; rw [val_psiS_zero, val_pre]; rfl

theorem bcApp_snoc {x : Term} (hx : x ≠ zero) : ∀ (P : List Term),
    bcApp (P ++ [x]) zero = bcApp P x
  | [] => by rw [List.nil_append, bcApp_single, if_pos rfl]; rfl
  | [p] => by
    show bcApp [p, x] zero = bcApp [p] x
    rw [bcApp_cons_cons, bcApp_single, bcApp_single, if_pos rfl, if_neg hx]
  | p :: q :: qs => by
    rw [List.cons_append, List.cons_append, bcApp_cons_cons, ← List.cons_append,
      bcApp_snoc hx (q :: qs), bcApp_cons_cons]

/-- **`B_k(L(k+1)) = L(ω)`.** -/
theorem bcB_base (k : ℕ) :
    bcB S k (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) = Nc.ncL S Ordinal.omega0 := by
  unfold bcB
  rw [← val_bcLt S (k + 1), bcNf_val S (NF_bcLt S k)]
  unfold bcLt
  rw [bcSig_psiS_zero, bcArg_of_pre (isPrefixOf_bcApp (prin_pre (k + 1)) zero),
    bcDrop_bcApp (prin_pre (k + 1)), bcSig_zero, val_psiS_zero, val_preW, ncL_omega_eq]

/-- **`B_k(L(k+2)) = L(ω+1)`.** -/
theorem bcB_base1 (k : ℕ) :
    bcB S k (Nc.ncL S ((k + 2 : ℕ) : Ordinal.{0})) = Nc.ncL S (Ordinal.omega0 + 1) := by
  unfold bcB
  rw [← val_bcLt S (k + 2), bcNf_val S (NF_bcLt S (k + 1))]
  unfold bcLt
  have e : bcPre (k + 2) = bcPre (k + 1) ++ [tPp] := by
    simp [bcPre, List.replicate_succ']
  rw [e, bcApp_snoc (by simp [tPp]), bcSig_psiS_zero,
    bcArg_of_pre (isPrefixOf_bcApp (prin_pre (k + 1)) tPp), bcDrop_bcApp (prin_pre (k + 1)),
    bcSig_free bcFree_tPp, val_psiS_zero, val_bcApp_preW, val_tPp, Nc.ncL_succ_omega]
  rfl

/-- `σ` commutes with the addition of normal forms. -/
theorem bcSig_addNF {k : ℕ} : ∀ {s : Term}, bcD S s → ∀ {t : Term}, bcD S t →
    bcSig (bcPre (k + 1)) bcPreW (addNF s t) =
      addNF (bcSig (bcPre (k + 1)) bcPreW s) (bcSig (bcPre (k + 1)) bcPreW t)
  | zero, _, t, _ => by rw [bcSig_zero]; rfl
  | add a b, hs, t, ht => by
    have hb : bcD S b := bcD_sub hs (sub_add_r a b)
    have ha : bcD S a := bcD_sub hs (sub_add_l a b)
    rw [addNF_add, bcSig_add, addNF_add]
    by_cases ht0 : t = zero
    · subst ht0; rw [bcSig_zero, if_pos rfl, if_pos rfl, bcSig_add]
    · rw [if_neg ht0, if_neg (bcSig_ne_zero ht0), head_bcSig,
        bc_cmp' ha (bcD_sub ht (head_sub t))]
      split_ifs
      · rfl
      · rw [bcSig_add, bcSig_addNF hb ht]
  | inacc n, hs, t, ht => bcSig_addNF_prin hs ht rfl
  | inaccW, hs, t, ht => bcSig_addNF_prin hs ht rfl
  | phi a b, hs, t, ht => bcSig_addNF_prin hs ht rfl
  | om a, hs, t, ht => bcSig_addNF_prin hs ht rfl
  | psiS s a, hs, t, ht => bcSig_addNF_prin hs ht rfl
  | psiI n a, hs, t, ht => bcSig_addNF_prin hs ht rfl
where
  bcSig_addNF_prin {x t : Term} (hs : bcD S x) (ht : bcD S t) (hP : x.isPrin = true) :
      bcSig (bcPre (k + 1)) bcPreW (addNF x t) =
        addNF (bcSig (bcPre (k + 1)) bcPreW x) (bcSig (bcPre (k + 1)) bcPreW t) := by
    rw [addNF_prin hP, addNF_prin (by rw [isPrin_bcSig]; exact hP)]
    by_cases ht0 : t = zero
    · subst ht0; rw [bcSig_zero, if_pos rfl, if_pos rfl]
    · rw [if_neg ht0, if_neg (bcSig_ne_zero ht0), head_bcSig,
        bc_cmp' hs (bcD_sub ht (head_sub t))]
      split_ifs
      · rfl
      · rw [bcSig_add]

theorem psi_isPrincipal {A : Ordinal.{0}} : Ordinal.IsPrincipal (· + ·) (S.psi A (Om 1)) :=
  SC.isPrincipal (InaccSeq.SC_psi InaccSeq.InR_Om1 A)

theorem ncL_add_lt {ξ x y : Ordinal.{0}} (hx : x < Nc.ncL S ξ) (hy : y < Nc.ncL S ξ) :
    x + y < Nc.ncL S ξ := psi_isPrincipal hx hy

/-- **`B(x + y) = B x + B y`** on `[0, L(ω))`. -/
theorem bcB_add {k : ℕ} {x y : Ordinal.{0}} (hx : x < Nc.ncL S Ordinal.omega0)
    (hy : y < Nc.ncL S Ordinal.omega0) : bcB S k (x + y) = bcB S k x + bcB S k y := by
  have hDx := bcD_nf S hx
  have hDy := bcD_nf S hy
  obtain ⟨hN, hv, -⟩ := addNF_spec (S := S) hDx.1 hDy.1
  rw [val_nf S hx, val_nf S hy] at hv
  have e : bcNf S (x + y) = addNF (bcNf S x) (bcNf S y) := by
    rw [← hv]; exact bcNf_val S hN
  unfold bcB
  rw [e, bcSig_addNF hDx hDy]
  exact (addNF_spec (S := S) (bc_NF hDx) (bc_NF hDy)).2.1

theorem val_lt_head_mul : ∀ {b : Term}, NF b → b ≠ zero →
    val S b < val S (head b) * Ordinal.omega0
  | add u v, h, _ => by
    have hv := val_lt_head_mul h.2.1 h.2.2.2.1
    have hle : val S (head v) ≤ val S u := by
      have e := cmp_eq_compare S h.2.1.head h.1
      rcases hc : compare (val S (head v)) (val S u) with _ | _ | _
      · exact (compare_lt_iff_lt.1 hc).le
      · exact (compare_eq_iff_eq.1 hc).le
      · rw [hc] at e; exact absurd e h.2.2.2.2
    have h1 : val S v < val S u * Ordinal.omega0 :=
      lt_of_lt_of_le hv (mul_le_mul_left hle _)
    show val S u + val S v < val S u * Ordinal.omega0
    calc val S u + val S v < val S u + val S u * Ordinal.omega0 := (add_lt_add_iff_left _).2 h1
      _ = val S u * Ordinal.omega0 := by
        rw [← mul_one_add, Ordinal.one_add_omega0]
  | zero, _, h0 => absurd rfl h0
  | inacc n, h, h0 => val_lt_mul_prin h h0
  | inaccW, h, h0 => val_lt_mul_prin h h0
  | phi a b, h, h0 => val_lt_mul_prin h h0
  | om a, h, h0 => val_lt_mul_prin h h0
  | psiS s a, h, h0 => val_lt_mul_prin h h0
  | psiI n a, h, h0 => val_lt_mul_prin h h0
where
  val_lt_mul_prin {b : Term} (h : NF b) (h0 : b ≠ zero) :
      val S b < val S b * Ordinal.omega0 := by
    have hpos : 0 < val S b := pos_iff_ne_zero.2 (val_ne_zero S h h0)
    calc val S b = val S b * 1 := (mul_one _).symm
      _ < val S b * Ordinal.omega0 := (mul_lt_mul_iff_right₀ hpos).2 Ordinal.one_lt_omega0

/-- A normal form with an indecomposable value is principal. -/
theorem isPrin_of_indec {t : Term} (ht : NF t) (hI : Indec (val S t)) : t.isPrin = true := by
  cases t with
  | zero => exact absurd rfl hI.ne_zero
  | add a b =>
    exfalso
    have ha0 : val S a ≠ 0 := val_ne_zero S ht.1 (NF.ne_zero_of_isPrin ht.2.2.1)
    have hb0 : val S b ≠ 0 := val_ne_zero S ht.2.1 ht.2.2.2.1
    have h1 : val S a < val S a + val S b :=
      lt_add_of_pos_right _ (pos_iff_ne_zero.2 hb0)
    have hbh := val_lt_head_mul (S := S) ht.2.1 ht.2.2.2.1
    have hle : val S (head b) ≤ val S a := by
      have e := cmp_eq_compare S ht.2.1.head ht.1
      rcases hc : compare (val S (head b)) (val S a) with _ | _ | _
      · exact (compare_lt_iff_lt.1 hc).le
      · exact (compare_eq_iff_eq.1 hc).le
      · rw [hc] at e; exact absurd e ht.2.2.2.2
    have h2 : val S b < val S a + val S b := by
      refine lt_of_le_of_ne le_add_self (fun e => ?_)
      have := Ordinal.add_eq_right_iff_mul_omega0_le.1 e.symm
      exact absurd (lt_of_lt_of_le hbh (mul_le_mul_left hle _)) (not_lt.2 this)
    exact absurd (hI.add_lt h1 h2) (lt_irrefl _)
  | _ => rfl

/-- **`B` keeps indecomposables.** -/
theorem bcB_indec {k : ℕ} {x : Ordinal.{0}} (hx : x < Nc.ncL S Ordinal.omega0) (hI : Indec x) :
    Indec (bcB S k x) := by
  have hD := bcD_nf S hx
  have hv := val_nf S hx
  have hP : (bcNf S x).isPrin = true := isPrin_of_indec hD.1 (hv ▸ hI)
  have hN := bc_NF (k := k) hD
  have h0 : bcNf S x ≠ zero := fun e => hI.ne_zero (by rw [← hv, e]; rfl)
  refine indec_iff.2 ⟨val_ne_zero S hN (bcSig_ne_zero h0), ?_⟩
  exact isPrincipal_val S hN (by rw [isPrin_bcSig]; exact hP)

/-! ## The data of SHIFT on `[0, L(k+2))` -/

theorem ncL_k2_lt (k : ℕ) : Nc.ncL S ((k + 2 : ℕ) : Ordinal.{0}) < Nc.ncL S Ordinal.omega0 :=
  Qq.qqL_lt_omega S (k + 2)

theorem bcB_mono (k : ℕ) :
    StrictMonoOn (bcB S k) (Set.Iio (Nc.ncL S ((k + 2 : ℕ) : Ordinal.{0}))) := by
  intro x hx y hy hxy
  exact (bcB_lt_iff ((Set.mem_Iio.1 hx).trans (ncL_k2_lt k))
    ((Set.mem_Iio.1 hy).trans (ncL_k2_lt k))).2 hxy

theorem bcB_bound (k : ℕ) : ∀ x < Nc.ncL S ((k + 2 : ℕ) : Ordinal.{0}),
    bcB S k x < Nc.ncL S (Ordinal.omega0 + 1) := by
  intro x hx
  rw [← bcB_base1 k]
  exact (bcB_lt_iff (hx.trans (ncL_k2_lt k)) (ncL_k2_lt k)).2 hx

theorem bcB_addIff (k : ℕ) : ∀ x < Nc.ncL S ((k + 2 : ℕ) : Ordinal.{0}),
    ∀ y < Nc.ncL S ((k + 2 : ℕ) : Ordinal.{0}), ∀ z < Nc.ncL S ((k + 2 : ℕ) : Ordinal.{0}),
      (x + y = z ↔ bcB S k x + bcB S k y = bcB S k z) := by
  intro x hx y hy z hz
  have hx' := hx.trans (ncL_k2_lt k)
  have hy' := hy.trans (ncL_k2_lt k)
  have hz' := hz.trans (ncL_k2_lt k)
  have hxy : x + y < Nc.ncL S ((k + 2 : ℕ) : Ordinal.{0}) := ncL_add_lt hx hy
  rw [← bcB_add hx' hy']
  constructor
  · rintro rfl; rfl
  · intro e
    rcases lt_trichotomy (x + y) z with h | h | h
    · exact absurd e ((bcB_lt_iff (hxy.trans (ncL_k2_lt k)) hz').2 h).ne
    · exact h
    · exact absurd e.symm ((bcB_lt_iff hz' (hxy.trans (ncL_k2_lt k))).2 h).ne

theorem bcB_closed (k : ℕ) : Closed (bcB S k '' Set.Iio (Nc.ncL S ((k + 2 : ℕ) : Ordinal.{0}))) := by
  rintro z ⟨x, hx, rfl⟩ hdz
  have hx' : x < Nc.ncL S Ordinal.omega0 := (Set.mem_Iio.1 hx).trans (ncL_k2_lt k)
  by_cases hI : Indec x
  · exact absurd hdz (bcB_indec hx' hI)
  rcases (not_not.1 hI : DecompR0 x) with h0 | ⟨u, v, hu, hv, huv⟩
  · subst h0; left; exact bcB_zero k
  · right
    have hu' := hu.trans hx'
    have hv' := hv.trans hx'
    refine ⟨bcB S k u, ⟨u, (hu.trans hx : u < _), rfl⟩, bcB S k v, ⟨v, (hv.trans hx : v < _), rfl⟩,
      (bcB_lt_iff hu' hx').2 hu, (bcB_lt_iff hv' hx').2 hv, ?_⟩
    rw [← bcB_add hu' hv', huv]

theorem bcB_fixN (k : ℕ) : ∀ x < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}), bcB S k x = x :=
  fun _ hx => bcB_fix hx

end Map

end Googology.Trans.PoR.InaccPsi.R2.Bc

import Googology.Trans.PoR.InaccPsi.R2.UcDat

/-!
# `H_γ` maps `Ω₂` into itself, and `B₂ < Ω₂`

`Ω₂ = OmTwo = (ℵ₂).ord`, `E₂ = ucE = ε_{Ω₂+1}`, `H_γ = Uc.ucH γ`, `ucC γ` the largest component of `γ`,
`B₂ = Uc.ucB`.  The levels `γ < E₂` whose components are all `≤ a` are generated from the ordinals `≤ a` by
`(e, d, r) ↦ Ω₂^e·d + r` (`ucSt a n`), so there are at most `max(|a|, ℵ₀)` of them; for `a < Ω₂` fewer than `ℵ₂`.

* `ucSt`, `ucSt_mono`, `uc_mk_St` (**the stages are small**), `uc_mem_St` (**every level `γ < E₂` with `ucC γ ≤ a` is
  in a stage**), `uc_mk_levels` (**fewer than `ℵ₂` such levels for `a < Ω₂`**);
* `uc_close` (**the closure argument**: for a set `I` of levels below `E₂` whose `H_j` map `Ω₂` into itself, every
  `b < Ω₂` lies below a strongly critical `v < Ω₂` fixed by every `H_j`, `j ∈ I`, with `ucC j < v`);
* `ucH_lt_Om2` (**`H_γ(y) < Ω₂` for `γ < E₂`, `y < Ω₂`**), `ucB_lt_Om2` (**`B₂ < Ω₂`**).

No new axiom.  New definition: `ucSt`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uc

open Ordinal Order Set Cardinal Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2

/-- The stages: the ordinals `≤ a`, closed `n` times under `(e, d, r) ↦ Ω₂^e·d + r`. -/
def ucSt (a : Ordinal.{0}) : ℕ → Set Ordinal.{0}
  | 0 => Iio (a + 1)
  | n + 1 => ucSt a n ∪
      (fun p : Ordinal.{0} × Ordinal.{0} × Ordinal.{0} => OmTwo ^ p.1 * p.2.1 + p.2.2) ''
        (ucSt a n ×ˢ (ucSt a n ×ˢ ucSt a n))

theorem ucSt_mono (a : Ordinal.{0}) {n m : ℕ} (h : n ≤ m) : ucSt a n ⊆ ucSt a m := by
  induction m with
  | zero => rw [Nat.le_zero.1 h]
  | succ m ih =>
    rcases Nat.of_le_succ h with h' | h'
    · exact (ih h').trans subset_union_left
    · rw [h']

/-- The bound `max |a + 1| ℵ₀`. -/
noncomputable abbrev ucBnd (a : Ordinal.{0}) : Cardinal.{1} := max (Cardinal.lift.{1} (a + 1).card) ℵ₀

theorem uc_mk_St (a : Ordinal.{0}) (n : ℕ) : #(ucSt a n) ≤ ucBnd a := by
  have hinf : (ℵ₀ : Cardinal.{1}) ≤ ucBnd a := le_max_right _ _
  induction n with
  | zero =>
    show #(Iio (a + 1)) ≤ ucBnd a
    rw [Cardinal.mk_Iio_ordinal]; exact le_max_left _ _
  | succ n ih =>
    have hprod : #((ucSt a n ×ˢ (ucSt a n ×ˢ ucSt a n) : Set (Ordinal.{0} × Ordinal.{0} × Ordinal.{0})))
        ≤ ucBnd a := by
      rw [mk_setProd, mk_setProd]
      exact (mul_le_mul' ih (mul_le_mul' ih ih)).trans_eq (by rw [mul_eq_self hinf, mul_eq_self hinf])
    refine (mk_union_le _ _).trans ?_
    refine (add_le_add ih (mk_image_le.trans hprod)).trans_eq ?_
    rw [add_eq_self hinf]

/-- **Every level `γ < E₂` with all components `≤ a` is in a stage.** -/
theorem uc_mem_St (a : Ordinal.{0}) : ∀ γ : Ordinal.{0}, γ < ucE → ucC γ ≤ a → ∃ n, γ ∈ ucSt a n := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγ hc
  by_cases h1 : γ < OmTwo
  · rw [ucC_small h1] at hc
    exact ⟨0, show γ < a + 1 from Order.lt_add_one_iff.2 hc⟩
  have h1' := not_lt.1 h1
  have hcomp := ucComps_big h1' hγ
  have hsub : ∀ δ, (∀ y ∈ ucComps δ, y ∈ ucComps γ) → ucC δ ≤ ucC γ := by
    intro δ hδ
    have h := (ucC_lt_iff (q := ucC γ + 1) (Order.lt_add_one_iff.2 zero_le |>.trans_le le_rfl) δ).2
      fun y hy => Order.lt_add_one_iff.2 (le_ucC (hδ y hy))
    exact Order.lt_add_one_iff.1 h
  have hl := uc_log_lt h1' hγ
  have hm := uc_mod_lt h1'
  have hcl : ucC (log OmTwo γ) ≤ a :=
    (hsub _ fun y hy => by rw [hcomp]; exact Or.inl hy).trans hc
  have hcm : ucC (γ % OmTwo ^ log OmTwo γ) ≤ a :=
    (hsub _ fun y hy => by rw [hcomp]; exact Or.inr (Or.inr hy)).trans hc
  have hcd : γ / OmTwo ^ log OmTwo γ ≤ a :=
    (le_ucC (show γ / OmTwo ^ log OmTwo γ ∈ ucComps γ by rw [hcomp]; exact Or.inr (Or.inl rfl))).trans hc
  obtain ⟨n1, hn1⟩ := IH _ hl (hl.trans hγ) hcl
  obtain ⟨n2, hn2⟩ := IH _ hm (hm.trans hγ) hcm
  refine ⟨max n1 n2 + 1, Or.inr ⟨(log OmTwo γ, γ / OmTwo ^ log OmTwo γ, γ % OmTwo ^ log OmTwo γ),
    ⟨ucSt_mono a (le_max_left n1 n2) hn1, ucSt_mono a (Nat.zero_le _) ?_,
      ucSt_mono a (le_max_right n1 n2) hn2⟩, uc_cnf_eq γ⟩⟩
  exact show γ / OmTwo ^ log OmTwo γ < a + 1 from Order.lt_add_one_iff.2 hcd

/-- `ℵ₂` and `Ω₂`. -/
theorem uc_aleph2_reg : (ℵ_ (1 + 1 : Ordinal.{0})).IsRegular := isRegular_aleph_add_one 1

theorem uc_aleph2_ord : (ℵ_ (1 + 1 : Ordinal.{0})).ord = OmTwo := by
  rw [ord_aleph, one_add_one_eq_two]; rfl

theorem uc_aleph0_lt : ℵ₀ < ℵ_ (1 + 1 : Ordinal.{0}) := by
  rw [← aleph_zero]; exact aleph_lt_aleph.2 (by rw [one_add_one_eq_two]; exact two_pos)

theorem uc_card_lt {a : Ordinal.{0}} (ha : a < OmTwo) :
    Cardinal.lift.{1} a.card < Cardinal.lift.{1} (ℵ_ (1 + 1 : Ordinal.{0})) :=
  Cardinal.lift_lt.2 (lt_ord.1 (by rw [uc_aleph2_ord]; exact ha))

/-- **Fewer than `ℵ₂` levels below `E₂` have all their components `≤ a`, for `a < Ω₂`.** -/
theorem uc_mk_levels {a : Ordinal.{0}} (ha : a < OmTwo) (P : Ordinal.{0} → Prop) :
    #{j : Ordinal.{0} // (j < ucE ∧ P j) ∧ ucC j ≤ a} < Cardinal.lift.{1} (ℵ_ (1 + 1 : Ordinal.{0})) := by
  have hsub : #{j : Ordinal.{0} // (j < ucE ∧ P j) ∧ ucC j ≤ a} ≤ #(⋃ n : ULift.{1} ℕ, ucSt a n.down) := by
    refine mk_subtype_mono fun j hj => ?_
    obtain ⟨n, hn⟩ := uc_mem_St a j hj.1.1 hj.2
    exact mem_iUnion.2 ⟨⟨n⟩, hn⟩
  refine hsub.trans_lt ((mk_iUnion_le _).trans_lt ?_)
  have hcard : #(ULift.{1} ℕ) = ℵ₀ := by simp
  rw [hcard]
  have hsup : (⨆ n : ULift.{1} ℕ, #(ucSt a n.down)) ≤ ucBnd a := ciSup_le fun n => uc_mk_St a n.down
  refine (mul_le_mul' (le_max_right _ _) hsup).trans_eq (mul_eq_self (le_max_right _ _)) |>.trans_lt ?_
  refine max_lt (uc_card_lt (uc_SC_Om2.add_one_lt ha)) ?_
  rw [← Cardinal.lift_aleph0.{1, 0}]; exact Cardinal.lift_lt.2 uc_aleph0_lt

theorem uc_gamma_lt {x : Ordinal.{0}} (hx : x < OmTwo) : gamma x < OmTwo := by
  rw [← uc_aleph2_ord] at hx ⊢; exact Tf.tf_gamma_lt uc_aleph2_reg uc_aleph0_lt x hx

/-- **The closure argument.** -/
theorem uc_close (I : Ordinal.{0} → Prop) (hH : ∀ j, j < ucE → I j → ∀ y < OmTwo, ucH j y < OmTwo)
    {b : Ordinal.{0}} (hb : b < OmTwo) :
    ∃ v, b < v ∧ v < OmTwo ∧ SC v ∧ ∀ j, j < ucE → I j → ucC j < v → ucH j v = v := by
  have hreg := uc_aleph2_reg
  have hO := uc_aleph2_ord
  have hSC := uc_SC_Om2
  -- one step
  let S : Ordinal.{0} → Ordinal.{0} := fun a =>
    ⨆ j : {j : Ordinal.{0} // (j < ucE ∧ I j) ∧ ucC j ≤ a}, ucH j.1 (a + 1)
  have hS : ∀ a < OmTwo, S a < OmTwo := fun a ha => by
    have h := iSup_lt_ord_big hreg (uc_mk_levels ha I)
      (f := fun j : {j : Ordinal.{0} // (j < ucE ∧ I j) ∧ ucC j ≤ a} => ucH j.1 (a + 1))
      (fun j => by rw [hO]; exact hH j.1 j.2.1.1 j.2.1.2 _ (hSC.add_one_lt ha))
    rwa [hO] at h
  have hSle : ∀ a < OmTwo, ∀ j, j < ucE → I j → ucC j ≤ a → ucH j (a + 1) ≤ S a := fun a ha j hj hI hc => by
    have hbdd : BddAbove (range fun j : {j : Ordinal.{0} // (j < ucE ∧ I j) ∧ ucC j ≤ a} => ucH j.1 (a + 1)) :=
      ⟨OmTwo, by rintro _ ⟨i, rfl⟩; exact (hH i.1 i.2.1.1 i.2.1.2 _ (hSC.add_one_lt ha)).le⟩
    exact le_ciSup hbdd (⟨j, ⟨hj, hI⟩, hc⟩ : {j : Ordinal.{0} // (j < ucE ∧ I j) ∧ ucC j ≤ a})
  let T : Ordinal.{0} → Ordinal.{0} := fun a => gamma (S a + a + 1)
  have hT : ∀ a < OmTwo, T a < OmTwo := fun a ha =>
    uc_gamma_lt (hSC.add_one_lt (Lq.lq_SC_indec hSC |>.add_lt (hS a ha) ha))
  have hTa : ∀ a, a < T a := fun a =>
    show a < gamma (S a + a + 1) from (le_add_self.trans_lt (lt_add_one _)).trans_le (Lq.lq_le_gamma _)
  have hTS : ∀ a, S a < T a := fun a =>
    show S a < gamma (S a + a + 1) from (le_self_add.trans_lt (lt_add_one _)).trans_le (Lq.lq_le_gamma _)
  -- the sequence
  let bs : ℕ → Ordinal.{0} := fun n => Nat.rec b (fun _ x => T x) n
  have hbs0 : bs 0 = b := rfl
  have hbsS : ∀ n, bs (n + 1) = T (bs n) := fun n => rfl
  have hbsO : ∀ n, bs n < OmTwo := by
    intro n; induction n with
    | zero => exact hb
    | succ n ih => rw [hbsS]; exact hT _ ih
  have hmono : ∀ n m, n ≤ m → bs n ≤ bs m := by
    intro n m h
    induction m with
    | zero => rw [Nat.le_zero.1 h]
    | succ m ih =>
      rcases Nat.of_le_succ h with h' | h'
      · exact (ih h').trans (by rw [hbsS]; exact (hTa _).le)
      · rw [h']
  let v : Ordinal.{0} := ⨆ n : ULift.{1} ℕ, bs n.down
  have hbdd : BddAbove (range fun n : ULift.{1} ℕ => bs n.down) :=
    ⟨OmTwo, by rintro _ ⟨i, rfl⟩; exact (hbsO i.down).le⟩
  have hle : ∀ n, bs n ≤ v := fun n => le_ciSup hbdd (⟨n⟩ : ULift.{1} ℕ)
  have hvO : v < OmTwo := by
    have h := iSup_lt_ord_big hreg (f := fun n : ULift.{1} ℕ => bs n.down)
      (by rw [show #(ULift.{1} ℕ) = ℵ₀ by simp, ← Cardinal.lift_aleph0.{1, 0}]
          exact Cardinal.lift_lt.2 uc_aleph0_lt)
      (fun n => by rw [hO]; exact hbsO n.down)
    rwa [hO] at h
  have hlt_ex : ∀ x < v, ∃ n, x < bs n := fun x hx => by
    obtain ⟨i, hi⟩ := (lt_ciSup_iff hbdd).1 hx
    exact ⟨i.down, hi⟩
  have hvSC : SC v := by
    refine ⟨(zero_le.trans_lt (hTa b)).trans_le (hle 1), fun x hx y hy => ?_⟩
    obtain ⟨i, hi⟩ := hlt_ex x hx
    obtain ⟨k, hk⟩ := hlt_ex y hy
    have hSCm : SC (bs (max i k + 1)) := by rw [hbsS]; exact Lq.lq_gamma_SC _
    have hxm : x < bs (max i k + 1) :=
      (hi.trans_le (hmono _ _ (le_max_left i k))).trans (by rw [hbsS]; exact hTa _)
    have hym : y < bs (max i k + 1) :=
      (hk.trans_le (hmono _ _ (le_max_right i k))).trans (by rw [hbsS]; exact hTa _)
    exact (hSCm.2 x hxm y hym).trans_le (hle (max i k + 1))
  refine ⟨v, (hTa b).trans_le (hle 1), hvO, hvSC, fun j hj hI hc => ?_⟩
  obtain ⟨i, hi⟩ := hlt_ex _ hc
  refine le_antisymm ?_ (ucH_le_self j v)
  refine ((ucH_normal j).le_iff_forall_le hvSC.isSuccLimit).2 fun x hx => ?_
  obtain ⟨k, hk⟩ := hlt_ex x hx
  set m := max i k
  have hxm : x ≤ bs m + 1 := (hk.trans_le (hmono _ _ (le_max_right i k))).le.trans le_self_add
  have hcm : ucC j ≤ bs m := (hi.trans_le (hmono _ _ (le_max_left i k))).le
  calc ucH j x ≤ ucH j (bs m + 1) := (ucG_le_iff (d := ucC) (L := Om1) j).2 hxm
    _ ≤ S (bs m) := hSle _ (hbsO m) j hj hI hcm
    _ ≤ T (bs m) := (hTS _).le
    _ = bs (m + 1) := (hbsS m).symm
    _ ≤ v := hle (m + 1)

/-- **`H_γ(y) < Ω₂` for `γ < E₂`, `y < Ω₂`.** -/
theorem ucH_lt_Om2 : ∀ γ : Ordinal.{0}, γ < ucE → ∀ y < OmTwo, ucH γ y < OmTwo := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγ
  -- values of `H_γ` above every `b < Ω₂`
  have hU : ∀ b < OmTwo, ∃ e, b < ucH γ e ∧ ucH γ e < OmTwo := by
    intro b hb
    have hb' : b + ucC γ + Om1 < OmTwo :=
      (Lq.lq_SC_indec uc_SC_Om2).add_lt ((Lq.lq_SC_indec uc_SC_Om2).add_lt hb (ucC_lt_Om2 γ)) uc_Om1_lt_Om2
    obtain ⟨v, hbv, hvO, hvSC, hfix⟩ :=
      uc_close (fun j => j < γ) (fun j _ hj => IH j hj (hj.trans hγ)) hb'
    have hm : ∃ e, ucH γ e = v := ucG_range hvSC
      ((le_add_self.trans_lt hbv)) ((le_add_self.trans le_self_add).trans_lt hbv |>.trans_le' le_rfl)
      fun j hj hc => hfix j (hj.trans hγ) hj hc
    obtain ⟨e, he⟩ := hm
    exact ⟨e, by rw [he]; exact (le_self_add.trans le_self_add).trans_lt hbv, by rw [he]; exact hvO⟩
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IHy =>
  intro hy
  rcases zero_or_succ_or_isSuccLimit y with rfl | ⟨y', rfl⟩ | hlim
  · obtain ⟨e, -, he⟩ := hU 0 uc_SC_Om2.1
    exact ((ucG_le_iff (d := ucC) (L := Om1) γ).2 zero_le).trans_lt he
  · have hy' : y' < Order.succ y' := Order.lt_succ y'
    obtain ⟨e, hlt, he⟩ := hU _ (IHy y' hy' (hy'.trans hy))
    have : y' < e := (ucH_lt_iff γ).1 hlt
    exact ((ucG_le_iff (d := ucC) (L := Om1) γ).2 (Order.succ_le_of_lt this)).trans_lt he
  · have hreg := uc_aleph2_reg
    have hO := uc_aleph2_ord
    have hbdd : BddAbove (range fun x : Iio y => ucH γ x.1) :=
      ⟨OmTwo, by rintro _ ⟨i, rfl⟩; exact (IHy i.1 i.2 (i.2.trans hy)).le⟩
    have hs : (⨆ x : Iio y, ucH γ x.1) < OmTwo := by
      have h := iSup_lt_ord_big hreg (f := fun x : Iio y => ucH γ x.1)
        (by rw [Cardinal.mk_Iio_ordinal]; exact uc_card_lt hy)
        (fun x => by rw [hO]; exact IHy x.1 x.2 (x.2.trans hy))
      rwa [hO] at h
    refine lt_of_le_of_lt ?_ hs
    refine ((ucH_normal γ).le_iff_forall_le hlim).2 fun x hx => ?_
    exact le_ciSup hbdd (⟨x, hx⟩ : Iio y)

/-- **`B₂ < Ω₂`.** -/
theorem ucB_lt_Om2 : ucB < OmTwo := by
  obtain ⟨v, hbv, hvO, hvSC, hfix⟩ := uc_close (fun _ => True) (fun j hj _ => ucH_lt_Om2 j hj) uc_Om1_lt_Om2
  refine (ucB_le ⟨hvSC, hbv, ?_⟩).trans_lt hvO
  rintro ⟨γ, hγ, hc, hne⟩
  exact hne (hfix γ hγ trivial hc)

end Googology.Trans.PoR.InaccPsi.R2.Uc

import Googology.Trans.PoR.InaccPsi.R2.UiDat

/-!
# `H^s_γ` maps `Ω_{s+1}` into itself, and `B_{s+1} < Ω_{s+1}`, for every `s`

`W = Ω_{s+1} = (ℵ_{s+1}).ord`, `E = uiE s`, `H_γ = uiH s γ`, `uiC s γ` the largest component, `B = uiB s`.  This is
`R2.UcBd` (`s = 1`) for every `s`: the levels `γ < E` whose components are all `≤ a` are generated from the ordinals
`≤ a` by `(e, d, r) ↦ W^e·d + r` (`uiSt s a n`), so there are fewer than `ℵ_{s+1}` of them for `a < W`.

* `uiSt`, `uiSt_mono`, `ui_mk_St`, `ui_mem_St`, `ui_aleph2_reg`, `ui_aleph2_ord`, `ui_aleph0_lt`, `ui_card_lt`,
  `ui_mk_levels`, `ui_gamma_lt`;
* `ui_close` (**the closure argument**), `uiH_lt_W` (**`H_γ(y) < W` for `γ < E`, `y < W`**), `uiB_lt_W`
  (**`B < W`**).

No new axiom.  New definitions: `uiSt`, `uiBnd`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ui

open Ordinal Order Set Cardinal Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc

variable {s : Ordinal.{0}}

/-- The stages: the ordinals `≤ a`, closed `n` times under `(e, d, r) ↦ W^e·d + r`. -/
def uiSt (s : Ordinal.{0}) (a : Ordinal.{0}) : ℕ → Set Ordinal.{0}
  | 0 => Iio (a + 1)
  | n + 1 => uiSt s a n ∪
      (fun p : Ordinal.{0} × Ordinal.{0} × Ordinal.{0} => Om (s + 1) ^ p.1 * p.2.1 + p.2.2) ''
        (uiSt s a n ×ˢ (uiSt s a n ×ˢ (uiSt s) a n))

theorem uiSt_mono (a : Ordinal.{0}) {n m : ℕ} (h : n ≤ m) : uiSt s a n ⊆ uiSt s a m := by
  induction m with
  | zero => rw [Nat.le_zero.1 h]
  | succ m ih =>
    rcases Nat.of_le_succ h with h' | h'
    · exact (ih h').trans subset_union_left
    · rw [h']

/-- The bound `max |a + 1| ℵ₀`. -/
noncomputable abbrev uiBnd (s : Ordinal.{0}) (a : Ordinal.{0}) : Cardinal.{1} := max (Cardinal.lift.{1} (a + 1).card) ℵ₀

theorem ui_mk_St (a : Ordinal.{0}) (n : ℕ) : #(uiSt s a n) ≤ uiBnd s a := by
  have hinf : (ℵ₀ : Cardinal.{1}) ≤ uiBnd s a := le_max_right _ _
  induction n with
  | zero =>
    show #(Iio (a + 1)) ≤ uiBnd s a
    rw [Cardinal.mk_Iio_ordinal]; exact le_max_left _ _
  | succ n ih =>
    have hprod : #((uiSt s a n ×ˢ (uiSt s a n ×ˢ (uiSt s) a n) : Set (Ordinal.{0} × Ordinal.{0} × Ordinal.{0})))
        ≤ uiBnd s a := by
      rw [mk_setProd, mk_setProd]
      exact (mul_le_mul' ih (mul_le_mul' ih ih)).trans_eq (by rw [mul_eq_self hinf, mul_eq_self hinf])
    refine (mk_union_le _ _).trans ?_
    refine (add_le_add ih (mk_image_le.trans hprod)).trans_eq ?_
    rw [add_eq_self hinf]

/-- **Every level `γ < E` with all components `≤ a` is in a stage.** -/
theorem ui_mem_St (a : Ordinal.{0}) : ∀ γ : Ordinal.{0}, γ < uiE s → uiC s γ ≤ a → ∃ n, γ ∈ uiSt s a n := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγ hc
  by_cases h1 : γ < Om (s + 1)
  · rw [uiC_small h1] at hc
    exact ⟨0, show γ < a + 1 from Order.lt_add_one_iff.2 hc⟩
  have h1' := not_lt.1 h1
  have hcomp := uiComps_big h1' hγ
  have hsub : ∀ δ, (∀ y ∈ uiComps s δ, y ∈ uiComps s γ) → uiC s δ ≤ uiC s γ := by
    intro δ hδ
    have h := (uiC_lt_iff (q := uiC s γ + 1) (Order.lt_add_one_iff.2 zero_le |>.trans_le le_rfl) δ).2
      fun y hy => Order.lt_add_one_iff.2 (le_uiC (hδ y hy))
    exact Order.lt_add_one_iff.1 h
  have hl := ui_log_lt h1' hγ
  have hm := ui_mod_lt h1'
  have hcl : uiC s (log (Om (s + 1)) γ) ≤ a :=
    (hsub _ fun y hy => by rw [hcomp]; exact Or.inl hy).trans hc
  have hcm : uiC s (γ % Om (s + 1) ^ log (Om (s + 1)) γ) ≤ a :=
    (hsub _ fun y hy => by rw [hcomp]; exact Or.inr (Or.inr hy)).trans hc
  have hcd : γ / Om (s + 1) ^ log (Om (s + 1)) γ ≤ a :=
    (le_uiC (show γ / Om (s + 1) ^ log (Om (s + 1)) γ ∈ uiComps s γ by rw [hcomp]; exact Or.inr (Or.inl rfl))).trans hc
  obtain ⟨n1, hn1⟩ := IH _ hl (hl.trans hγ) hcl
  obtain ⟨n2, hn2⟩ := IH _ hm (hm.trans hγ) hcm
  refine ⟨max n1 n2 + 1, Or.inr ⟨(log (Om (s + 1)) γ, γ / Om (s + 1) ^ log (Om (s + 1)) γ,
      γ % Om (s + 1) ^ log (Om (s + 1)) γ),
    ⟨uiSt_mono a (le_max_left n1 n2) hn1, uiSt_mono a (Nat.zero_le _) ?_,
      uiSt_mono a (le_max_right n1 n2) hn2⟩, (ui_cnf_eq s) γ⟩⟩
  exact show γ / Om (s + 1) ^ log (Om (s + 1)) γ < a + 1 from Order.lt_add_one_iff.2 hcd

/-- `ℵ_{s+1}` and `W`. -/
theorem ui_aleph2_reg (s : Ordinal.{0}) : (ℵ_ (s + 1 : Ordinal.{0})).IsRegular := isRegular_aleph_add_one s

theorem ui_aleph2_ord (s : Ordinal.{0}) : (ℵ_ (s + 1 : Ordinal.{0})).ord = Om (s + 1) := by
  rw [ord_aleph, Om_of_ne_zero (by simp)]

theorem ui_aleph0_lt (s : Ordinal.{0}) : ℵ₀ < ℵ_ (s + 1 : Ordinal.{0}) := by
  rw [← aleph_zero]; exact aleph_lt_aleph.2 (by simp)

theorem ui_card_lt {a : Ordinal.{0}} (ha : a < Om (s + 1)) :
    Cardinal.lift.{1} a.card < Cardinal.lift.{1} (ℵ_ (s + 1 : Ordinal.{0})) :=
  Cardinal.lift_lt.2 (lt_ord.1 (by rw [(ui_aleph2_ord s)]; exact ha))

/-- **Fewer than `ℵ_{s+1}` levels below `E` have all their components `≤ a`, for `a < W`.** -/
theorem ui_mk_levels {a : Ordinal.{0}} (ha : a < Om (s + 1)) (P : Ordinal.{0} → Prop) :
    #{j : Ordinal.{0} // (j < uiE s ∧ P j) ∧ uiC s j ≤ a} < Cardinal.lift.{1} (ℵ_ (s + 1 : Ordinal.{0})) := by
  have hsub : #{j : Ordinal.{0} // (j < uiE s ∧ P j) ∧ uiC s j ≤ a} ≤ #(⋃ n : ULift.{1} ℕ, uiSt s a n.down) := by
    refine mk_subtype_mono fun j hj => ?_
    obtain ⟨n, hn⟩ := ui_mem_St a j hj.1.1 hj.2
    exact mem_iUnion.2 ⟨⟨n⟩, hn⟩
  refine hsub.trans_lt ((mk_iUnion_le _).trans_lt ?_)
  have hcard : #(ULift.{1} ℕ) = ℵ₀ := by simp
  rw [hcard]
  have hsup : (⨆ n : ULift.{1} ℕ, #(uiSt s a n.down)) ≤ uiBnd s a := ciSup_le fun n => ui_mk_St a n.down
  refine (mul_le_mul' (le_max_right _ _) hsup).trans_eq (mul_eq_self (le_max_right _ _)) |>.trans_lt ?_
  refine max_lt (ui_card_lt ((ui_SC_W s).add_one_lt ha)) ?_
  rw [← Cardinal.lift_aleph0.{1, 0}]; exact Cardinal.lift_lt.2 (ui_aleph0_lt s)

theorem ui_gamma_lt {x : Ordinal.{0}} (hx : x < Om (s + 1)) : gamma x < Om (s + 1) := by
  rw [← (ui_aleph2_ord s)] at hx ⊢; exact Tf.tf_gamma_lt (ui_aleph2_reg s) (ui_aleph0_lt s) x hx

/-- **The closure argument.** -/
theorem ui_close (I : Ordinal.{0} → Prop) (hH : ∀ j, j < uiE s → I j → ∀ y < Om (s + 1), uiH s j y < Om (s + 1))
    {b : Ordinal.{0}} (hb : b < Om (s + 1)) :
    ∃ v, b < v ∧ v < Om (s + 1) ∧ SC v ∧ ∀ j, j < uiE s → I j → uiC s j < v → uiH s j v = v := by
  have hreg := (ui_aleph2_reg s)
  have hO := (ui_aleph2_ord s)
  have hSC := (ui_SC_W s)
  -- one step
  let S : Ordinal.{0} → Ordinal.{0} := fun a =>
    ⨆ j : {j : Ordinal.{0} // (j < uiE s ∧ I j) ∧ uiC s j ≤ a}, uiH s j.1 (a + 1)
  have hS : ∀ a < Om (s + 1), S a < Om (s + 1) := fun a ha => by
    have h := iSup_lt_ord_big hreg (ui_mk_levels ha I)
      (f := fun j : {j : Ordinal.{0} // (j < uiE s ∧ I j) ∧ uiC s j ≤ a} => uiH s j.1 (a + 1))
      (fun j => by rw [hO]; exact hH j.1 j.2.1.1 j.2.1.2 _ (hSC.add_one_lt ha))
    rwa [hO] at h
  have hSle : ∀ a < Om (s + 1), ∀ j, j < uiE s → I j → uiC s j ≤ a → uiH s j (a + 1) ≤ S a := fun a ha j hj hI hc => by
    have hbdd : BddAbove (range fun j : {j : Ordinal.{0} // (j < uiE s ∧ I j) ∧ uiC s j ≤ a} => uiH s j.1 (a + 1)) :=
      ⟨(Om (s + 1)), by rintro _ ⟨i, rfl⟩; exact (hH i.1 i.2.1.1 i.2.1.2 _ (hSC.add_one_lt ha)).le⟩
    exact le_ciSup hbdd (⟨j, ⟨hj, hI⟩, hc⟩ : {j : Ordinal.{0} // (j < uiE s ∧ I j) ∧ uiC s j ≤ a})
  let T : Ordinal.{0} → Ordinal.{0} := fun a => gamma (S a + a + 1)
  have hT : ∀ a < Om (s + 1), T a < Om (s + 1) := fun a ha =>
    ui_gamma_lt (hSC.add_one_lt (Lq.lq_SC_indec hSC |>.add_lt (hS a ha) ha))
  have hTa : ∀ a, a < T a := fun a =>
    show a < gamma (S a + a + 1) from (le_add_self.trans_lt (lt_add_one _)).trans_le (Lq.lq_le_gamma _)
  have hTS : ∀ a, S a < T a := fun a =>
    show S a < gamma (S a + a + 1) from (le_self_add.trans_lt (lt_add_one _)).trans_le (Lq.lq_le_gamma _)
  -- the sequence
  let bs : ℕ → Ordinal.{0} := fun n => Nat.rec b (fun _ x => T x) n
  have hbs0 : bs 0 = b := rfl
  have hbsS : ∀ n, bs (n + 1) = T (bs n) := fun n => rfl
  have hbsO : ∀ n, bs n < Om (s + 1) := by
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
    ⟨(Om (s + 1)), by rintro _ ⟨i, rfl⟩; exact (hbsO i.down).le⟩
  have hle : ∀ n, bs n ≤ v := fun n => le_ciSup hbdd (⟨n⟩ : ULift.{1} ℕ)
  have hvO : v < Om (s + 1) := by
    have h := iSup_lt_ord_big hreg (f := fun n : ULift.{1} ℕ => bs n.down)
      (by rw [show #(ULift.{1} ℕ) = ℵ₀ by simp, ← Cardinal.lift_aleph0.{1, 0}]
          exact Cardinal.lift_lt.2 (ui_aleph0_lt s))
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
  refine le_antisymm ?_ (uiH_le_self (s := s) j v)
  refine ((uiH_normal (s := s) j).le_iff_forall_le hvSC.isSuccLimit).2 fun x hx => ?_
  obtain ⟨k, hk⟩ := hlt_ex x hx
  set m := max i k
  have hxm : x ≤ bs m + 1 := (hk.trans_le (hmono _ _ (le_max_right i k))).le.trans le_self_add
  have hcm : uiC s j ≤ bs m := (hi.trans_le (hmono _ _ (le_max_left i k))).le
  calc (uiH s) j x ≤ uiH s j (bs m + 1) := (ucG_le_iff (d := uiC s) (L := Om s) j).2 hxm
    _ ≤ S (bs m) := hSle _ (hbsO m) j hj hI hcm
    _ ≤ T (bs m) := (hTS _).le
    _ = bs (m + 1) := (hbsS m).symm
    _ ≤ v := hle (m + 1)

/-- **`H_γ(y) < W` for `γ < E`, `y < W`.** -/
theorem uiH_lt_W : ∀ γ : Ordinal.{0}, γ < uiE s → ∀ y < Om (s + 1), uiH s γ y < Om (s + 1) := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγ
  -- values of `H_γ` above every `b < W`
  have hU : ∀ b < Om (s + 1), ∃ e, b < uiH s γ e ∧ uiH s γ e < Om (s + 1) := by
    intro b hb
    have hb' : b + uiC s γ + (Om s) < Om (s + 1) :=
      (Lq.lq_SC_indec (ui_SC_W s)).add_lt ((Lq.lq_SC_indec (ui_SC_W s)).add_lt hb ((uiC_lt_W s) γ)) (ui_L_lt_W s)
    obtain ⟨v, hbv, hvO, hvSC, hfix⟩ :=
      ui_close (fun j => j < γ) (fun j _ hj => IH j hj (hj.trans hγ)) hb'
    have hm : ∃ e, uiH s γ e = v := ucG_range hvSC
      ((le_add_self.trans_lt hbv)) ((le_add_self.trans le_self_add).trans_lt hbv |>.trans_le' le_rfl)
      fun j hj hc => hfix j (hj.trans hγ) hj hc
    obtain ⟨e, he⟩ := hm
    exact ⟨e, by rw [he]; exact (le_self_add.trans le_self_add).trans_lt hbv, by rw [he]; exact hvO⟩
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IHy =>
  intro hy
  rcases zero_or_succ_or_isSuccLimit y with rfl | ⟨y', rfl⟩ | hlim
  · obtain ⟨e, -, he⟩ := hU 0 (ui_SC_W s).1
    exact ((ucG_le_iff (d := uiC s) (L := Om s) γ).2 zero_le).trans_lt he
  · have hy' : y' < Order.succ y' := Order.lt_succ y'
    obtain ⟨e, hlt, he⟩ := hU _ (IHy y' hy' (hy'.trans hy))
    have : y' < e := (uiH_lt_iff (s := s) γ).1 hlt
    exact ((ucG_le_iff (d := uiC s) (L := Om s) γ).2 (Order.succ_le_of_lt this)).trans_lt he
  · have hreg := (ui_aleph2_reg s)
    have hO := (ui_aleph2_ord s)
    have hbdd : BddAbove (range fun x : Iio y => uiH s γ x.1) :=
      ⟨(Om (s + 1)), by rintro _ ⟨i, rfl⟩; exact (IHy i.1 i.2 (i.2.trans hy)).le⟩
    have hs : (⨆ x : Iio y, uiH s γ x.1) < Om (s + 1) := by
      have h := iSup_lt_ord_big hreg (f := fun x : Iio y => uiH s γ x.1)
        (by rw [Cardinal.mk_Iio_ordinal]; exact ui_card_lt hy)
        (fun x => by rw [hO]; exact IHy x.1 x.2 (x.2.trans hy))
      rwa [hO] at h
    refine lt_of_le_of_lt ?_ hs
    refine ((uiH_normal (s := s) γ).le_iff_forall_le hlim).2 fun x hx => ?_
    exact le_ciSup hbdd (⟨x, hx⟩ : Iio y)

/-- **`B < W`.** -/
theorem uiB_lt_W (s : Ordinal.{0}) : uiB s < Om (s + 1) := by
  obtain ⟨v, hbv, hvO, hvSC, hfix⟩ := ui_close (fun _ => True) (fun j hj _ => uiH_lt_W j hj) (ui_L_lt_W s)
  refine (uiB_le ⟨hvSC, hbv, ?_⟩).trans_lt hvO
  rintro ⟨γ, hγ, hc, hne⟩
  exact hne (hfix γ hγ trivial hc)

end Googology.Trans.PoR.InaccPsi.R2.Ui

import Googology.Trans.PoR.InaccPsi.R2.BrLs13

/-!
# Theorem T up to the first fixed point

`θ = ψ_{Ω₂}(Ω_ω)`, `A_η = Ω_ω + θ·η` (`ConjT.Aη`).  For every InaccPsi sequence `S : InaccSeq.{0}`:

* `psi_limit` (**Lemma CONT** at every limit argument): `ψ_{Ω₁}(a) = sup_{e<a} ψ_{Ω₁}(e)` for a limit `a`;
* `exists_prin_list`: every `η` is the sum of a weakly decreasing list of nonzero additive principal
  ordinals `≤ η` (its Cantor normal form, each `ω^b` written `c` times);
* `goodL_A`, `AA_A`: for `η < Ω_ω` the list `[Ω_ω, θ·x₁, …, θ·xₖ]` (with `η = x₁ + ⋯ + xₖ` as above) is a
  `GoodL` list with sum `A_η`, so Theorem LOW-STEP (`ups_low_step`) applies to `A_η`;
* `HA_of_lt`: (HA) for `A_η` when `η < ψ_{Ω₁}(A_η)`, so Theorem STEP (`Br.ups_step`) applies to `A_η`;
* `ups_upper_gen` (**Theorem T-UP**): `υ_{1+η} ≤ ψ_{Ω₁}(A_η)` when `η' < ψ_{Ω₁}(A_η')` for every `η' < η`;
* `ups_lower_gen` (**Theorem T-LOW**): `ψ_{Ω₁}(A_η) ≤ υ_{1+η}` for every `η < Ω_ω`;
* `ups_eq_gen` (**Theorem T**): `υ_{1+η} = ψ_{Ω₁}(A_η)` when `η' < ψ_{Ω₁}(A_η')` for every `η' < η`;
  `ups_eq_lt_psi`: for every `η < ψ_{Ω₁}(Ω_ω)`; `ups_eq_lt_gamma0`: for every `η < Γ₀`;
* `etaS` (`η* `, the least `η` with `ψ_{Ω₁}(A_η) ≤ η`): `etaS_fix` (`ψ_{Ω₁}(A_{η*}) = η*`), `ups_eq_le_etaS`
  (Theorem T for every `η ≤ η*`), `ups_etaS` (`υ_{η*} = η*`), `etaS_least_fix` (`η*` is the least nonzero
  fixed point of `υ`), `etaS_lt_Om1`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Bt

open Googology.Trans.PoR.InaccPsi.R2.Br

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq

/-! ## Lemma CONT at every limit -/

/-- **Lemma CONT** at every limit argument: `ψ_{Ω₁}(a) = sup_{e<a} ψ_{Ω₁}(e)`. -/
theorem psi_limit (S : InaccSeq.{0}) {a : Ordinal.{0}} (ha : IsSuccLimit a) :
    S.psi a (Om 1) = ⨆ e : Iio a, S.psi e.1 (Om 1) := by
  have hInR : S.InR (Om (1 : Ordinal.{0})) := Low.InR_Om_one
  have hbdd : BddAbove (range fun e : Iio a => S.psi e.1 (Om 1)) :=
    ⟨Om 1, by rintro _ ⟨e, rfl⟩; exact (psi_lt hInR _).le⟩
  have ha0 : (0 : Ordinal.{0}) < a := ha.bot_lt
  haveI : Nonempty (Iio a) := ⟨⟨0, ha0⟩⟩
  set σ := ⨆ e : Iio a, S.psi e.1 (Om 1) with hσ
  have up : ∀ {y e e' : Ordinal.{0}}, e ≤ e' →
      y ∈ S.CSet e (S.psi e (Om 1)) → y ∈ S.CSet e' (S.psi e' (Om 1)) :=
    fun h hy => (psi_mono hInR h).2 hy
  have key : ∀ x ∈ S.CSet a σ, ∃ e < a, x ∈ S.CSet e (S.psi e (Om 1)) := by
    intro x hx
    induction hx with
    | small h =>
      obtain ⟨e, he⟩ := (lt_ciSup_iff hbdd).1 h
      exact ⟨e.1, e.2, CSet.of_lt he⟩
    | zero => exact ⟨0, ha0, CSet.zero_mem _ _⟩
    | inacc n => exact ⟨0, ha0, CSet.I_mem _ _ n⟩
    | inaccW => exact ⟨0, ha0, CSet.Iw_mem _ _⟩
    | add _ _ ihx ihy =>
      obtain ⟨e1, h1, k1⟩ := ihx
      obtain ⟨e2, h2, k2⟩ := ihy
      exact ⟨max e1 e2, max_lt h1 h2,
        CSet.add_mem (up (le_max_left _ _) k1) (up (le_max_right _ _) k2)⟩
    | phi _ _ ihx ihy =>
      obtain ⟨e1, h1, k1⟩ := ihx
      obtain ⟨e2, h2, k2⟩ := ihy
      exact ⟨max e1 e2, max_lt h1 h2,
        CSet.phi_mem (up (le_max_left _ _) k1) (up (le_max_right _ _) k2)⟩
    | om _ ih =>
      obtain ⟨e1, h1, k1⟩ := ih
      exact ⟨e1, h1, CSet.Om_mem k1⟩
    | @coll π e hπ _ _ ihπ ihe =>
      obtain ⟨e1, h1, k1⟩ := ihπ
      obtain ⟨e2, h2, k2⟩ := ihe
      have hs : e.1 + 1 < a := ha.add_one_lt e.2
      refine ⟨max (e.1 + 1) (max e1 e2), max_lt hs (max_lt h1 h2), ?_⟩
      have he : e.1 < max (e.1 + 1) (max e1 e2) := lt_of_lt_of_le (lt_add_one _) (le_max_left _ _)
      exact CSet.psi_mem he hπ
        (up (le_trans (le_max_left _ _) (le_max_right _ _)) k1)
        (up (le_trans (le_max_right _ _) (le_max_right _ _)) k2)
  apply le_antisymm
  · refine psi_le_of_good (CSet.Om_mem (CSet.one_mem _ _)) ?_
    intro x hx hxΩ
    obtain ⟨e, he, hN⟩ := key x hx
    exact lt_of_lt_of_le (lt_psi_of_mem hInR hN hxΩ) (le_ciSup hbdd ⟨e, he⟩)
  · exact ciSup_le fun e => (psi_mono hInR e.2.le).1

/-- **Lemma CONT**, as a bound. -/
theorem psi_limit_le (S : InaccSeq.{0}) {a B : Ordinal.{0}} (ha : IsSuccLimit a)
    (hB : ∀ e < a, S.psi e (Om 1) ≤ B) : S.psi a (Om 1) ≤ B := by
  rw [psi_limit S ha]
  haveI : Nonempty (Iio a) := ⟨⟨0, ha.bot_lt⟩⟩
  exact ciSup_le fun e => hB e.1 e.2

/-! ## Additive normal forms -/

theorem prin_eq_opow {x : Ordinal.{0}} (hp : IsPrincipal (· + ·) x) (h0 : x ≠ 0) :
    ∃ b : Ordinal.{0}, x = ω ^ b := by
  rcases isPrincipal_add_iff_zero_or_omega0_opow.1 hp with h | ⟨b, hb⟩
  · exact absurd h h0
  · exact ⟨b, hb.symm⟩

/-- Every `η` is the sum of a weakly decreasing list of nonzero additive principal ordinals `≤ η`. -/
theorem exists_prin_list : ∀ η : Ordinal.{0}, ∃ L : List Ordinal.{0},
    (∀ x ∈ L, IsPrincipal (· + ·) x ∧ x ≠ 0 ∧ x ≤ η) ∧ L.Pairwise (· ≥ ·) ∧
      L.foldr (· + ·) 0 = η := by
  intro η
  induction η using WellFoundedLT.induction with
  | _ η IH =>
    rcases eq_or_ne η 0 with rfl | hη
    · exact ⟨[], by simp, List.Pairwise.nil, rfl⟩
    set x := ω ^ Ordinal.log ω η with hx
    have hxη : x ≤ η := opow_log_le_self ω hη
    have hxp : IsPrincipal (· + ·) x := isPrincipal_add_omega0_opow _
    have hx0 : x ≠ 0 := (opow_pos _ omega0_pos).ne'
    have hηlt : η < ω ^ (Ordinal.log ω η + 1) := lt_opow_succ_log_self one_lt_omega0 η
    set r := η - x with hr
    have hxr : x + r = η := Ordinal.add_sub_cancel_of_le hxη
    have hrη : r < η := by
      rcases lt_or_eq_of_le (show r ≤ η from by rw [← hxr]; exact le_add_self) with h | h
      · exact h
      · exfalso
        have h1 : x + η = η := by rw [← h] at hxr ⊢; exact hxr
        have h2 := add_eq_right_iff_mul_omega0_le.1 h1
        rw [hx, ← opow_succ, succ_eq_add_one] at h2
        exact absurd hηlt (not_lt.2 h2)
    obtain ⟨L, hL1, hL2, hL3⟩ := IH r hrη
    refine ⟨x :: L, fun y hy => ?_, ?_, ?_⟩
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact ⟨hxp, hx0, hxη⟩
      · obtain ⟨a, b, c⟩ := hL1 y hy
        exact ⟨a, b, c.trans hrη.le⟩
    · refine List.pairwise_cons.2 ⟨fun y hy => ?_, hL2⟩
      obtain ⟨hyp, hy0, hyr⟩ := hL1 y hy
      obtain ⟨b, rfl⟩ := prin_eq_opow hyp hy0
      have h1 : ω ^ b < ω ^ (Ordinal.log ω η + 1) := lt_of_le_of_lt (hyr.trans hrη.le) hηlt
      have h2 : b < Ordinal.log ω η + 1 := (opow_lt_opow_iff_right one_lt_omega0).1 h1
      exact opow_le_opow_right omega0_pos (Order.lt_add_one_iff.1 h2)
    · rw [List.foldr_cons, hL3, hxr]

/-! ## The list of `A_η` -/

/-- The summands of `A_η`: `Ω_ω` followed by `θ·x` for the summands `x` of `η`. -/
noncomputable def listA (S : InaccSeq.{0}) (L : List Ordinal.{0}) : List Ordinal.{0} :=
  Om (ω : Ordinal.{0}) :: L.map (ConjT.th S * ·)

theorem foldr_map_mul (c : Ordinal.{0}) : ∀ L : List Ordinal.{0},
    (L.map (c * ·)).foldr (· + ·) 0 = c * L.foldr (· + ·) 0
  | [] => by simp
  | x :: L => by
    rw [List.map_cons, List.foldr_cons, List.foldr_cons, foldr_map_mul c L, mul_add]

theorem AA_listA (S : InaccSeq.{0}) {η : Ordinal.{0}} {L : List Ordinal.{0}}
    (hL : L.foldr (· + ·) 0 = η) : AA S (listA S L) = ConjT.Aη S η := by
  show (listA S L).foldr (· + ·) 0 = _
  rw [listA, List.foldr_cons, foldr_map_mul, hL]; rfl

theorem th_mul_opow (S : InaccSeq.{0}) (b : Ordinal.{0}) :
    ConjT.th S * ω ^ b = ω ^ (ConjT.th S + b) := by
  rw [opow_add, Low.opow_eq_self_of_SC (ConjT.SC_th S)]

theorem th_lt_Om_omega (S : InaccSeq.{0}) : ConjT.th S < Om (ω : Ordinal.{0}) :=
  th_lt_Om2.trans Om2_lt_Om_omega

/-- `[Ω_ω, θ·x₁, …, θ·xₖ]` is a `GoodL` list when `xᵢ < Ω_ω`. -/
theorem goodL_listA (S : InaccSeq.{0}) {η : Ordinal.{0}} (hη : η < Om (ω : Ordinal.{0}))
    {L : List Ordinal.{0}} (hL1 : ∀ x ∈ L, IsPrincipal (· + ·) x ∧ x ≠ 0 ∧ x ≤ η)
    (hL2 : L.Pairwise (· ≥ ·)) : GoodL S (listA S L) := by
  have hSCw : SC (Om (ω : Ordinal.{0})) := SC_Om omega0_ne_zero
  have hθ := th_lt_Om_omega S
  have hsmall : ∀ x ∈ L, ConjT.th S * x < Om (ω : Ordinal.{0}) := by
    intro x hx
    obtain ⟨hp, h0, hle⟩ := hL1 x hx
    obtain ⟨b, rfl⟩ := prin_eq_opow hp h0
    rw [th_mul_opow]
    have hb : b < Om (ω : Ordinal.{0}) :=
      lt_of_le_of_lt ((Ordinal.right_le_opow b one_lt_omega0).trans hle) hη
    have := hSCw.2 0 hSCw.1 _ (hSCw.isPrincipal hθ hb)
    rwa [veblen_zero_apply] at this
  refine ⟨fun l hl => ?_, ?_⟩
  · rcases List.mem_cons.1 hl with rfl | hl
    · exact ⟨Om_omega_principal, (Om_pos omega0_ne_zero).ne', hθ.le⟩
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hl
      obtain ⟨hp, h0, _⟩ := hL1 x hx
      obtain ⟨b, rfl⟩ := prin_eq_opow hp h0
      refine ⟨?_, ?_, ?_⟩
      · show IsPrincipal (· + ·) (ConjT.th S * ω ^ b)
        rw [th_mul_opow]; exact isPrincipal_add_omega0_opow _
      · exact (mul_pos th_pos (opow_pos _ omega0_pos)).ne'
      · show ConjT.th S ≤ ConjT.th S * ω ^ b
        exact le_mul_left _ (opow_pos _ omega0_pos)
  · refine List.pairwise_cons.2 ⟨fun y hy => ?_, ?_⟩
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      exact (hsmall x hx).le
    · refine List.pairwise_map.2 (hL2.imp fun h => ?_)
      exact mul_le_mul_right h _

/-- For `η < Ω_ω`, `A_η` is the sum of a `GoodL` list. -/
theorem exists_goodL (S : InaccSeq.{0}) {η : Ordinal.{0}} (hη : η < Om (ω : Ordinal.{0})) :
    ∃ L', GoodL S L' ∧ AA S L' = ConjT.Aη S η := by
  obtain ⟨L, hL1, hL2, hL3⟩ := exists_prin_list η
  exact ⟨listA S L, goodL_listA S hη hL1 hL2, AA_listA S hL3⟩

/-! ## (HA) for `A_η` -/

theorem foldr_mem {S : InaccSeq.{0}} {a b : Ordinal.{0}} :
    ∀ L : List Ordinal.{0}, (∀ x ∈ L, x ∈ S.CSet a b) → L.foldr (· + ·) 0 ∈ S.CSet a b
  | [], _ => CSet.zero_mem a b
  | x :: L, h => by
    rw [List.foldr_cons]
    exact CSet.add_mem (h x List.mem_cons_self) (foldr_mem L fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- **(HA)** for `A_η` when `η < ψ_{Ω₁}(A_η)`. -/
theorem HA_of_lt (S : InaccSeq.{0}) {η : Ordinal.{0}}
    (hη : η < S.psi (ConjT.Aη S η) (Om 1)) : ConjT.HA S (ConjT.Aη S η) := by
  obtain ⟨L, hL1, -, hL3⟩ := exists_prin_list η
  have hlt : Om (ω : Ordinal.{0}) < ConjT.Aη S η + 1 :=
    lt_of_le_of_lt (ConjT.OmW_le_A S η) (lt_add_one _)
  have hθ : ConjT.th S ∈ S.CSet (ConjT.Aη S η + 1) (S.psi (ConjT.Aη S η) (Om 1)) := ConjT.th_mem S hlt
  have e : (listA S L).foldr (· + ·) 0 = ConjT.Aη S η := AA_listA S hL3
  unfold ConjT.HA
  suffices h : (listA S L).foldr (· + ·) 0 ∈
      S.CSet (ConjT.Aη S η + 1) (S.psi (ConjT.Aη S η) (Om 1)) by rwa [e] at h
  refine foldr_mem _ fun l hl => ?_
  rcases List.mem_cons.1 hl with rfl | hl
  · exact ConjT.OmW_mem S _ _
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hl
    obtain ⟨hp, h0, hle⟩ := hL1 x hx
    obtain ⟨b, rfl⟩ := prin_eq_opow hp h0
    show ConjT.th S * ω ^ b ∈ _
    rw [th_mul_opow, ← veblen_zero_apply]
    refine CSet.phi_mem (CSet.zero_mem _ _) (CSet.add_mem hθ (CSet.of_lt ?_))
    exact lt_of_le_of_lt ((Ordinal.right_le_opow b one_lt_omega0).trans hle) hη

/-! ## Theorem T-UP -/

theorem A_zero (S : InaccSeq.{0}) : ConjT.Aη S 0 = Om (ω : Ordinal.{0}) := by
  simp [ConjT.Aη]

theorem psi_A_mono (S : InaccSeq.{0}) {η η' : Ordinal.{0}} (h : η ≤ η') :
    S.psi (ConjT.Aη S η) (Om 1) ≤ S.psi (ConjT.Aη S η') (Om 1) :=
  (psi_mono Low.InR_Om_one (ConjT.A_mono S h)).1

/-- **Theorem T-UP**: `υ_{1+η} ≤ ψ_{Ω₁}(Ω_ω + θ·η)` when `η' < ψ_{Ω₁}(A_η')` for every `η' < η`. -/
theorem ups_upper_gen (S : InaccSeq.{0}) : ∀ η : Ordinal.{0},
    (∀ η' < η, η' < S.psi (ConjT.Aη S η') (Om 1)) →
      upsilon (1 + η) ≤ S.psi (ConjT.Aη S η) (Om 1) := by
  intro η
  induction η using Ordinal.limitRecOn with
  | zero =>
    intro _
    rw [add_zero, A_zero]; exact ups_one_le S
  | add_one η ih =>
    intro h
    have h1 := ih (fun η' hη' => h η' (hη'.trans (lt_add_one η)))
    have hHA := HA_of_lt S (h η (lt_add_one η))
    have := ups_step S (1 + η) (ConjT.Aη S η) (ConjT.OmW_le_A S η) hHA h1
    rw [← add_assoc, ← ConjT.A_succ]
    exact this
  | limit l hl ih =>
    intro h
    rw [one_add_of_omega0_le (omega0_le_of_isSuccLimit hl)]
    refine ups_lim l _ hl fun ι hι1 hιl => ?_
    have hsub : 1 + (ι - 1) = ι := Ordinal.add_sub_cancel_of_le hι1
    have hlt : ι - 1 < l := lt_of_le_of_lt (le_add_self.trans_eq hsub) hιl
    calc upsilon ι = upsilon (1 + (ι - 1)) := by rw [hsub]
      _ ≤ S.psi (ConjT.Aη S (ι - 1)) (Om 1) :=
          ih (ι - 1) hlt (fun η' hη' => h η' (hη'.trans hlt))
      _ ≤ S.psi (ConjT.Aη S l) (Om 1) := psi_A_mono S hlt.le

/-! ## Theorem T-LOW -/

theorem ups_mono : Monotone upsilon := upsilon_normal.strictMono.monotone

/-- **Theorem T-LOW**: `ψ_{Ω₁}(Ω_ω + θ·η) ≤ υ_{1+η}` for every `η < Ω_ω`. -/
theorem ups_lower_gen (S : InaccSeq.{0}) : ∀ η : Ordinal.{0}, η < Om (ω : Ordinal.{0}) →
    S.psi (ConjT.Aη S η) (Om 1) ≤ upsilon (1 + η) := by
  intro η
  induction η using Ordinal.limitRecOn with
  | zero =>
    intro _
    rw [add_zero, A_zero]; exact psi_le_ups_one S
  | add_one η ih =>
    intro h
    have hη : η < Om (ω : Ordinal.{0}) := (lt_add_one η).trans h
    obtain ⟨L, hL, hAL⟩ := exists_goodL S hη
    have h1 := ih hη
    rw [← hAL] at h1
    have := ups_low_step S (1 + η) L hL h1
    rw [hAL, ConjT.A_succ] at this
    rw [← add_assoc]
    exact this
  | limit l hl ih =>
    intro h
    rw [one_add_of_omega0_le (omega0_le_of_isSuccLimit hl)]
    have hθ0 : (0 : Ordinal.{0}) < ConjT.th S := th_pos
    have hlim : IsSuccLimit (ConjT.Aη S l) :=
      isSuccLimit_add _ (isSuccLimit_mul_right hθ0 hl)
    refine psi_limit_le S hlim fun e he => ?_
    have hl0 : (0 : Ordinal.{0}) < l := hl.bot_lt
    -- `e < A_{η'}` for some `η' < l`
    obtain ⟨η', hη'l, heη'⟩ : ∃ η' < l, e ≤ ConjT.Aη S η' := by
      rcases lt_or_ge e (Om (ω : Ordinal.{0})) with h1 | h1
      · exact ⟨0, hl0, by rw [A_zero]; exact h1.le⟩
      · obtain ⟨d, rfl⟩ := exists_add_of_le h1
        have hd : d < ConjT.th S * l := (add_lt_add_iff_left _).1 he
        obtain ⟨c, hc, hdc⟩ := (lt_mul_iff_of_isSuccLimit hl).1 hd
        exact ⟨c, hc, by unfold ConjT.Aη; gcongr⟩
    have hη'ω : η' < Om (ω : Ordinal.{0}) := hη'l.trans h
    calc S.psi e (Om 1) ≤ S.psi (ConjT.Aη S η') (Om 1) := (psi_mono Low.InR_Om_one heη').1
      _ ≤ upsilon (1 + η') := ih η' hη'l hη'ω
      _ ≤ upsilon l := ups_mono (by
          rw [← one_add_of_omega0_le (omega0_le_of_isSuccLimit hl)]
          gcongr)

/-! ## Theorem T -/

/-- Under the hypothesis of T-UP, `η ≤ ψ_{Ω₁}(A_η)`. -/
theorem le_psi_of_forall (S : InaccSeq.{0}) {η : Ordinal.{0}}
    (h : ∀ η' < η, η' < S.psi (ConjT.Aη S η') (Om 1)) : η ≤ S.psi (ConjT.Aη S η) (Om 1) := by
  by_contra hlt
  rw [not_le] at hlt
  have h1 := h _ hlt
  exact absurd (h1.trans_le (psi_A_mono S hlt.le)) (lt_irrefl _)

/-- **Theorem T**: `υ_{1+η} = ψ_{Ω₁}(Ω_ω + θ·η)` when `η' < ψ_{Ω₁}(A_η')` for every `η' < η`. -/
theorem ups_eq_gen (S : InaccSeq.{0}) {η : Ordinal.{0}}
    (h : ∀ η' < η, η' < S.psi (ConjT.Aη S η') (Om 1)) :
    upsilon (1 + η) = S.psi (ConjT.Aη S η) (Om 1) := by
  refine le_antisymm (ups_upper_gen S η h) (ups_lower_gen S η ?_)
  have h1 := le_psi_of_forall S h
  have h2 : S.psi (ConjT.Aη S η) (Om 1) < Om (1 : Ordinal.{0}) := psi_lt Low.InR_Om_one _
  exact lt_of_le_of_lt (h1.trans h2.le) (Om_lt_Om.2 one_lt_omega0)

/-- **Theorem T** for every `η < ψ_{Ω₁}(Ω_ω)` (`= υ₁`). -/
theorem ups_eq_lt_psi (S : InaccSeq.{0}) {η : Ordinal.{0}}
    (hη : η < S.psi (Om (ω : Ordinal.{0})) (Om 1)) :
    upsilon (1 + η) = S.psi (ConjT.Aη S η) (Om 1) := by
  refine ups_eq_gen S fun η' hη' => ?_
  have := psi_A_mono S (zero_le : (0 : Ordinal.{0}) ≤ η')
  rw [A_zero] at this
  exact (hη'.trans hη).trans_le this

/-- `Γ₀ ≤ ψ_{Ω₁}(Ω_ω)`: an `SC` ordinal is a fixed point of `a ↦ φ(a, 0)`. -/
theorem gamma0_le_psi (S : InaccSeq.{0}) : Γ₀ ≤ S.psi (Om (ω : Ordinal.{0})) (Om 1) :=
  gamma_zero_le_of_veblen_le (SC_psi Low.InR_Om_one _).veblen_zero.le

/-- **Theorem T** for every `η < Γ₀`. -/
theorem ups_eq_lt_gamma0 (S : InaccSeq.{0}) {η : Ordinal.{0}} (hη : η < Γ₀) :
    upsilon (1 + η) = S.psi (ConjT.Aη S η) (Om 1) :=
  ups_eq_lt_psi S (hη.trans_le (gamma0_le_psi S))

/-! ## The first fixed point `η*` -/

/-- `η*`: the least `η` with `ψ_{Ω₁}(Ω_ω + θ·η) ≤ η`. -/
noncomputable def etaS (S : InaccSeq.{0}) : Ordinal.{0} :=
  sInf {η | S.psi (ConjT.Aη S η) (Om 1) ≤ η}

theorem etaS_mem (S : InaccSeq.{0}) : S.psi (ConjT.Aη S (etaS S)) (Om 1) ≤ etaS S :=
  csInf_mem (s := {η | S.psi (ConjT.Aη S η) (Om 1) ≤ η})
    ⟨Om 1, (psi_lt Low.InR_Om_one _).le⟩

/-- Below `η*`: `η < ψ_{Ω₁}(A_η)`. -/
theorem lt_psi_of_lt_etaS (S : InaccSeq.{0}) {η : Ordinal.{0}} (h : η < etaS S) :
    η < S.psi (ConjT.Aη S η) (Om 1) := by
  by_contra hle
  rw [not_lt] at hle
  exact absurd (csInf_le' (s := {η | S.psi (ConjT.Aη S η) (Om 1) ≤ η}) hle) (not_le.2 h)

/-- `ψ_{Ω₁}(Ω_ω + θ·η*) = η*`. -/
theorem etaS_fix (S : InaccSeq.{0}) : S.psi (ConjT.Aη S (etaS S)) (Om 1) = etaS S :=
  le_antisymm (etaS_mem S) (le_psi_of_forall S fun _ h => lt_psi_of_lt_etaS S h)

/-- **Theorem T** for every `η ≤ η*`. -/
theorem ups_eq_le_etaS (S : InaccSeq.{0}) {η : Ordinal.{0}} (h : η ≤ etaS S) :
    upsilon (1 + η) = S.psi (ConjT.Aη S η) (Om 1) :=
  ups_eq_gen S fun _ h' => lt_psi_of_lt_etaS S (h'.trans_le h)

theorem omega0_lt_etaS (S : InaccSeq.{0}) : ω < etaS S := by
  have hSC := SC_psi Low.InR_Om_one (ConjT.Aη S (etaS S)) (S := S)
  rw [etaS_fix] at hSC
  have := hSC.2 0 hSC.1 1 (by simpa using hSC.add_one_lt hSC.1)
  rw [veblen_zero_apply, opow_one] at this
  exact this

/-- `υ_{η*} = η* = ψ_{Ω₁}(Ω_ω + θ·η*)`. -/
theorem ups_etaS (S : InaccSeq.{0}) :
    upsilon (etaS S) = etaS S ∧ etaS S = S.psi (ConjT.Aη S (etaS S)) (Om 1) := by
  have h := ups_eq_le_etaS S (le_refl (etaS S))
  rw [one_add_of_omega0_le (omega0_lt_etaS S).le, etaS_fix] at h
  exact ⟨h, (etaS_fix S).symm⟩

/-- Below `η*` no nonzero index is a fixed point of `υ`: `0 < ξ < η* ⇒ ξ < υ_ξ`. -/
theorem lt_ups_of_lt_etaS (S : InaccSeq.{0}) {ξ : Ordinal.{0}} (h0 : 0 < ξ) (h : ξ < etaS S) :
    ξ < upsilon ξ := by
  rcases lt_or_ge ξ ω with hω | hω
  · have h1 : upsilon 1 ≤ upsilon ξ := ups_mono (Order.one_le_iff_pos.2 h0)
    have h2 := ups_eq_le_etaS S (zero_le : (0 : Ordinal.{0}) ≤ etaS S)
    rw [add_zero, A_zero] at h2
    have h3 : ω < S.psi (Om (ω : Ordinal.{0})) (Om 1) := by
      have hSC := SC_psi Low.InR_Om_one (Om (ω : Ordinal.{0})) (S := S)
      have := hSC.2 0 hSC.1 1 (by simpa using hSC.add_one_lt hSC.1)
      rwa [veblen_zero_apply, opow_one] at this
    exact hω.trans (h3.trans_le (h2 ▸ h1))
  · have h1 := ups_eq_le_etaS S h.le
    rw [one_add_of_omega0_le hω] at h1
    rw [h1]; exact lt_psi_of_lt_etaS S h

/-- **`η*` is the least nonzero fixed point of `υ`.** -/
theorem etaS_least_fix (S : InaccSeq.{0}) :
    etaS S = sInf {ξ : Ordinal.{0} | 0 < ξ ∧ upsilon ξ = ξ} := by
  have hmem : etaS S ∈ {ξ : Ordinal.{0} | 0 < ξ ∧ upsilon ξ = ξ} :=
    ⟨lt_of_le_of_lt zero_le (omega0_lt_etaS S), (ups_etaS S).1⟩
  refine le_antisymm ?_ (csInf_le' hmem)
  refine le_csInf ⟨_, hmem⟩ fun ξ ⟨h0, hξ⟩ => ?_
  by_contra hlt
  rw [not_le] at hlt
  exact absurd hξ (lt_ups_of_lt_etaS S h0 hlt).ne'

/-- `η* < Ω₁`. -/
theorem etaS_lt_Om1 (S : InaccSeq.{0}) : etaS S < Om1 := by
  rw [← etaS_fix, Om1_eq]; exact psi_lt Low.InR_Om_one _

end Googology.Trans.PoR.InaccPsi.R2.Bt

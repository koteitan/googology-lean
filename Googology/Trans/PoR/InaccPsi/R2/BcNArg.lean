import Googology.Trans.PoR.InaccPsi.R2.BcINF

/-!
# The arguments of the collapses other than `ψ_{Ω₁}` are below `α_ω`

`bcNArgs S B t`: every collapse `ψ_π(b)` of `t` with `π ≠ Ω₁` (`ψ^S_s`, `s ≠ 0`, and `ψ^I_n`)
has `|b| < B`.

* `bc_nargs` (**the bound**): a normal form `t` with `|t| < P'·ω` whose `ψ_{Ω₁}`-arguments are all
  `< α_ω + P'·ω` has `bcNArgs S α_ω t`.  Simultaneous induction on the size for
  (A) `ψ_{Ω₁}(a)`: for `a < α_ω` every collapse argument inside `a` is `< a` (the `K`-set of
  `ψ_{Ω₁}(a)`; collapses other than `ψ_{Ω₁}` are `> Ω₁`), for `a ≥ α_ω` the argument is
  `α_ω + ρ` with `ρ < P'·ω` (prefix test) and (C) applies to `ρ`;
  (C) `|x| < P'·ω`: sums, Veblen terms and `Ω` by induction, a collapse `ψ_{Ω₂}(b) ≤ P'` has
  `b ≤ Ω_ω·2` (`ψ` is increasing at normal arguments), and (B) applies to it;
  (B) `ψ_{Ω₂}(e)` with `e ≤ Ω_ω·2`: every collapse argument reached by its `K`-set is `< e`, and
  a collapse below `ψ_{Ω₂}(e)` is `< P'·ω`, so (C) applies.

No axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Bc

open Googology.Notation.InaccPsi Googology.Notation.InaccPsi.Term

section NArg

variable (S : InaccSeq.{0})

/-- Every collapse other than `ψ_{Ω₁}` in `t` has its argument `< B`. -/
def bcNArgs (B : Ordinal.{0}) : Term → Prop
  | zero => True
  | inacc _ => True
  | inaccW => True
  | add a b => bcNArgs B a ∧ bcNArgs B b
  | phi a b => bcNArgs B a ∧ bcNArgs B b
  | om a => bcNArgs B a
  | psiS s a => bcNArgs B s ∧ bcNArgs B a ∧ (s ≠ zero → val S a < B)
  | psiI _ a => bcNArgs B a ∧ val S a < B

theorem bcNArgs_bcApp {B : Ordinal.{0}} {P : List Term} (hP : ∀ p ∈ P, bcNArgs S B p)
    {r : Term} (hr : bcNArgs S B r) : bcNArgs S B (bcApp P r) := by
  induction P with
  | nil => exact hr
  | cons x xs ih =>
    cases xs with
    | nil =>
      rw [bcApp_single]; split_ifs
      · exact hP x (by simp)
      · exact ⟨hP x (by simp), hr⟩
    | cons y ys =>
      rw [bcApp_cons_cons]
      exact ⟨hP x (by simp), ih (fun p hp => hP p (List.mem_cons_of_mem _ hp))⟩

theorem WW_lt_W : val S (add tW tW) < bcAlphaW S := by
  rw [val_WW]; unfold bcAlphaW
  exact lt_add_of_pos_right _ (Ordinal.opow_pos _ Ordinal.omega0_pos)

theorem bcNArgs_tW {B : Ordinal.{0}} : bcNArgs S B tW := by simp [tW, tOm, tOne, bcNArgs]
theorem bcNArgs_tOne {B : Ordinal.{0}} : bcNArgs S B tOne := by simp [tOne, bcNArgs]

theorem bcNArgs_tPp : bcNArgs S (bcAlphaW S) tPp :=
  ⟨bcNArgs_tOne S, ⟨bcNArgs_tW S, bcNArgs_tW S⟩, fun _ => WW_lt_W S⟩

theorem bcNArgs_tWp : bcNArgs S (bcAlphaW S) tWp :=
  ⟨trivial, bcNArgs_tPp S, bcNArgs_tOne S⟩

theorem Om_two_le_psiI (n : ℕ) (b : Term) : Om 2 ≤ val S (psiI n b) := by
  obtain ⟨h1, -, h3, -⟩ := val_psiI_bounds S n b
  rw [← h1]
  refine Om_le_Om.2 ?_
  have : (2 : Ordinal.{0}) < Om 1 := by
    rw [Om_of_ne_zero one_ne_zero]
    exact lt_of_lt_of_le (Ordinal.natCast_lt_omega0 2) (Ordinal.omega0_le_omega _)
  exact (this.trans h3).le

theorem Wp_lt_Om2 : Ordinal.omega0 ^ (Nc.ncPp S + 1) < Om 2 := by
  have hSC : SC (Om (2 : Ordinal.{0})) := SC_Om (by norm_num)
  have hP : Nc.ncPp S < Om 2 := by
    have h : Nc.ncPp S < Om (1 + 1) := InaccSeq.psi_lt (InaccSeq.InR_Om_succ 1) _
    exact h.trans_eq (congrArg Om (by norm_num))
  rw [← Ordinal.veblen_zero_apply]
  exact hSC.2 0 hSC.1 _ (hSC.add_one_lt hP)

/-- A `ψ^S_s`-value below `Ω₂` with `s ≠ 0` is a `ψ_{Ω₂}`-value. -/
theorem sub_eq_one {s b : Term} (hs : NF s) (hs0 : s ≠ zero) (h : val S (psiS s b) < Om 2) :
    s = tOne := by
  have h1 := (val_psiS_bounds S s b).1
  have h2 : val S s < 2 := Om_lt_Om.1 (h1.trans h)
  have h0 : val S s ≠ 0 := val_ne_zero S hs hs0
  have e : val S s = 1 := by
    have : val S s ≤ 1 := Order.lt_add_one_iff.1 (by rw [show (1 : Ordinal.{0}) + 1 = 2 by norm_num]; exact h2)
    exact le_antisymm this (Order.one_le_iff_ne_zero.2 h0)
  exact eq_of_val_eq S hs NF_tOne (by rw [e, val_tOne])

/-- `ψ_{Ω₂}(b) ≤ P'` gives `b ≤ Ω_ω·2`. -/
theorem arg_le_of_le_Pp {b : Term} (h : val S (psiS tOne b) ≤ Nc.ncPp S) :
    val S b ≤ val S (add tW tW) := by
  by_contra hc
  rw [not_le] at hc
  have hmem : val S (add tW tW) ∈
      S.CSet (val S (add tW tW)) (S.psi (val S (add tW tW)) (Om (1 + 1))) := by
    rw [val_WW]
    exact InaccSeq.CSet.add_mem (ConjT.OmW_mem S _ _) (ConjT.OmW_mem S _ _)
  have := InaccSeq.psi_lt_psi (InaccSeq.InR_Om_succ 1) hc hmem
  have e1 : val S (psiS tOne b) = S.psi (val S b) (Om (1 + 1)) := by
    simp only [val, val_tOne]
  have e2 : Nc.ncPp S = S.psi (val S (add tW tW)) (Om (1 + 1)) := by
    rw [val_WW]; rfl
  rw [← e1, ← e2] at this
  exact absurd h (not_le.2 this)

/-- A principal normal form below `P'·ω` is `≤ P'`. -/
theorem prin_le_Pp {x : Term} (hx : NF x) (hP : x.isPrin = true)
    (h : val S x < Ordinal.omega0 ^ (Nc.ncPp S + 1)) : val S x ≤ Nc.ncPp S := by
  by_contra hc
  rw [not_le] at hc
  exact not_between_Pp S hx hP (cmp_gt_of_val S hx NF_tPp (by rw [val_tPp]; exact hc))
    (cmp_lt_of_val S hx NF_tWp (by rw [val_tWp]; exact h))

/-- The statements (A) and (C) at size `≤ N`. -/
def NArgStage (N : ℕ) : Prop :=
  ∀ x : Term, x.size ≤ N → NF x → bcArgsLt S (bcAlphaWW S) x →
    (∀ a, x = psiS zero a → bcNArgs S (bcAlphaW S) a) ∧
    (val S x < Ordinal.omega0 ^ (Nc.ncPp S + 1) → bcNArgs S (bcAlphaW S) x)

/-- (B): inside `ψ_{Ω₂}(e)` with `e ≤ Ω_ω·2`, given (A), (C) for the smaller terms. -/
theorem narg_B {N : ℕ} (ih : NArgStage S N) {e : Term} (hμ : NF (psiS tOne e))
    (hμA : bcArgsLt S (bcAlphaWW S) (psiS tOne e)) (he : val S e ≤ val S (add tW tW))
    (hsz : (psiS tOne e).size ≤ N + 1) :
    ∀ (M : ℕ) (x : Term), x.size ≤ M → bcSub x e → KLt (psiS tOne e) x e →
      bcNArgs S (bcAlphaW S) x := by
  have hμP : val S (psiS tOne e) ≤ Nc.ncPp S := by
    have := (InaccSeq.psi_mono (S := S) (InaccSeq.InR_Om_succ 1) he).1
    simp only [val, val_tOne]
    rw [show Nc.ncPp S = S.psi (val S (add tW tW)) (Om (1 + 1)) by rw [val_WW]; rfl]
    exact this
  have heW : val S e < bcAlphaW S := lt_of_le_of_lt he (WW_lt_W S)
  have heD : NF e := hμ.2.1
  have heA : bcArgsLt S (bcAlphaWW S) e := hμA.2.1
  have hPW : Nc.ncPp S < Ordinal.omega0 ^ (Nc.ncPp S + 1) := by
    have := (cmp_lt_iff S NF_tPp NF_tWp).1 cmp_tPp_tWp; rwa [val_tPp, val_tWp] at this
  have hsub_size : ∀ {x}, bcSub x e → x.size ≤ N := fun hx => by
    have := bcSub_size hx; simp only [size] at hsz; omega
  intro M
  induction M with
  | zero => intro x hx; exact absurd hx (by have := size_pos x; omega)
  | succ M ihM =>
    intro x hx hxe hK
    have hxN : NF x := NF_of_sub hxe heD
    have hxA : bcArgsLt S (bcAlphaWW S) x := bcArgsLt_of_sub S hxe heA
    -- a term below `ψ_{Ω₂}(e)` is below `P'·ω`
    have hC : cmp x (psiS tOne e) = .lt → bcNArgs S (bcAlphaW S) x := fun h =>
      (ih x (hsub_size hxe) hxN hxA).2
        (lt_of_lt_of_le ((cmp_lt_iff S hxN hμ).1 h) (hμP.trans hPW.le))
    cases x with
    | zero => trivial
    | inacc _ => trivial
    | inaccW => trivial
    | add a b =>
      simp only [size] at hx
      exact ⟨ihM a (by omega) (bcSub_trans (sub_add_l a b) hxe) hK.1,
        ihM b (by omega) (bcSub_trans (sub_add_r a b) hxe) hK.2⟩
    | phi a b =>
      simp only [size] at hx
      exact ⟨ihM a (by omega) (bcSub_trans (sub_phi_l a b) hxe) hK.1,
        ihM b (by omega) (bcSub_trans (sub_phi_r a b) hxe) hK.2⟩
    | om b =>
      simp only [size] at hx
      rcases hK with hK | hK
      · exact hC hK
      · exact ihM b (by omega) (bcSub_trans (sub_om b) hxe) hK
    | psiI n b =>
      simp only [size] at hx
      rcases hK with hK | ⟨hb, hKb⟩
      · exact hC hK
      · exact ⟨ihM b (by omega) (bcSub_trans (sub_psiI n b) hxe) hKb,
          lt_of_lt_of_le ((cmp_lt_iff S hxN.1 heD).1 hb) (le_of_lt heW)⟩
    | psiS s b =>
      simp only [size] at hx
      by_cases hs0 : s = zero
      · subst hs0
        exact ⟨trivial, (ih _ (hsub_size hxe) hxN hxA).1 b rfl, fun h => absurd rfl h⟩
      rcases hK with hK | ⟨hb, hKs, hKb⟩
      · exact hC hK
      · exact ⟨ihM s (by omega) (bcSub_trans (sub_psiS_s s b) hxe) hKs,
          ihM b (by omega) (bcSub_trans (sub_psiS_a s b) hxe) hKb,
          fun _ => lt_of_lt_of_le ((cmp_lt_iff S hxN.2.1 heD).1 hb) (le_of_lt heW)⟩

/-- (A): inside `ψ_{Ω₁}(a)` with `a < α_ω`, given (A) for the smaller terms. -/
theorem narg_A {N : ℕ} (ih : NArgStage S N) {a : Term} (hμ : NF (psiS zero a))
    (hμA : bcArgsLt S (bcAlphaWW S) (psiS zero a)) (ha : val S a < bcAlphaW S)
    (hsz : (psiS zero a).size ≤ N + 1) :
    ∀ (M : ℕ) (x : Term), x.size ≤ M → bcSub x a → KLt (psiS zero a) x a →
      bcNArgs S (bcAlphaW S) x := by
  have haN : NF a := hμ.2.1
  have haA : bcArgsLt S (bcAlphaWW S) a := hμA.2.1
  have hsub_size : ∀ {x}, bcSub x a → x.size ≤ N := fun hx => by
    have := bcSub_size hx; simp only [size] at hsz; omega
  have hμ1 : val S (psiS zero a) < Om 1 := by
    rw [val_psiS_zero]; exact InaccSeq.psi_lt (S := S) InaccSeq.InR_Om1 _
  intro M
  induction M with
  | zero => intro x hx; exact absurd hx (by have := size_pos x; omega)
  | succ M ihM =>
    intro x hx hxa hK
    have hxN : NF x := NF_of_sub hxa haN
    have hxA : bcArgsLt S (bcAlphaWW S) x := bcArgsLt_of_sub S hxa haA
    have hbig : Om 1 ≤ val S x → ¬ cmp x (psiS zero a) = .lt := fun h h' =>
      absurd (lt_of_le_of_lt h ((cmp_lt_iff S hxN hμ).1 h' |>.trans hμ1)) (lt_irrefl _)
    cases x with
    | zero => trivial
    | inacc _ => trivial
    | inaccW => trivial
    | add a' b =>
      simp only [size] at hx
      exact ⟨ihM a' (by omega) (bcSub_trans (sub_add_l a' b) hxa) hK.1,
        ihM b (by omega) (bcSub_trans (sub_add_r a' b) hxa) hK.2⟩
    | phi a' b =>
      simp only [size] at hx
      exact ⟨ihM a' (by omega) (bcSub_trans (sub_phi_l a' b) hxa) hK.1,
        ihM b (by omega) (bcSub_trans (sub_phi_r a' b) hxa) hK.2⟩
    | om b =>
      simp only [size] at hx
      rcases hK with hK | hK
      · exact absurd hK (hbig (Om_one_le_val_om S hxN))
      · exact ihM b (by omega) (bcSub_trans (sub_om b) hxa) hK
    | psiI n b =>
      simp only [size] at hx
      rcases hK with hK | ⟨hb, hKb⟩
      · exact absurd hK (hbig (val_psiI_bounds S n b).2.2.1.le)
      · exact ⟨ihM b (by omega) (bcSub_trans (sub_psiI n b) hxa) hKb,
          ((cmp_lt_iff S hxN.1 haN).1 hb).trans ha⟩
    | psiS s b =>
      simp only [size] at hx
      by_cases hs0 : s = zero
      · subst hs0
        exact ⟨trivial, (ih _ (hsub_size hxa) hxN hxA).1 b rfl, fun h => absurd rfl h⟩
      rcases hK with hK | ⟨hb, hKs, hKb⟩
      · exact absurd hK (hbig (Om_one_lt_val_psiS S hxN.1 hs0).le)
      · exact ⟨ihM s (by omega) (bcSub_trans (sub_psiS_s s b) hxa) hKs,
          ihM b (by omega) (bcSub_trans (sub_psiS_a s b) hxa) hKb,
          fun _ => ((cmp_lt_iff S hxN.2.1 haN).1 hb).trans ha⟩

theorem narg_stage : ∀ N : ℕ, NArgStage S N
  | 0 => fun x hx => absurd hx (by have := size_pos x; omega)
  | N + 1 => by
    have ih := narg_stage N
    intro x hx hxN hxA
    -- (A)
    have hA : ∀ a, x = psiS zero a → bcNArgs S (bcAlphaW S) a := by
      intro a e
      subst e
      have haN : NF a := hxN.2.1
      have haA : val S a < bcAlphaWW S := hxA.2.2 rfl
      by_cases ha : val S a < bcAlphaW S
      · exact narg_A S ih hxN hxA ha hx a.size a le_rfl (bcSub_refl a) hxN.2.2
      · have pa := (bci_pre_iff S haN haA).2 (not_lt.1 ha)
        have e := bcApp_of_prefix prin_preW haN pa
        rw [e]
        refine bcNArgs_bcApp S (fun p hp => ?_) ?_
        · simp only [bcPreW, List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl | rfl
          · exact bcNArgs_tW S
          · exact bcNArgs_tW S
          · exact bcNArgs_tWp S
        · have hr := bci_rest_lt S haN haA pa
          have hrs : (bcDrop bcPreW.length a).size ≤ N := by
            have := bcDrop_size_le bcPreW.length a; simp only [size] at hx; omega
          exact (ih _ hrs (NF_bcDrop _ haN)
            (by rcases bcSub_bcDrop bcPreW.length a with h | h
                · rw [h]; trivial
                · exact bcArgsLt_of_sub S h hxA.2.1)).2 hr
    refine ⟨hA, fun hv => ?_⟩
    cases x with
    | zero => trivial
    | inacc _ => trivial
    | inaccW => trivial
    | add a b =>
      simp only [size] at hx
      exact ⟨(ih a (by omega) hxN.1 hxA.1).2 (lt_of_le_of_lt le_self_add hv),
        (ih b (by omega) hxN.2.1 hxA.2).2 (lt_of_le_of_lt le_add_self hv)⟩
    | phi a b =>
      simp only [size] at hx
      exact ⟨(ih a (by omega) hxN.1 hxA.1).2 (((cmp_lt_iff S hxN.1 hxN).1 hxN.2.2.1).trans hv),
        (ih b (by omega) hxN.2.1 hxA.2).2 (((cmp_lt_iff S hxN.2.1 hxN).1 hxN.2.2.2).trans hv)⟩
    | om b =>
      simp only [size] at hx
      exact (ih b (by omega) hxN.1 hxA).2 (lt_of_le_of_lt (le_Om _) hv)
    | psiI n b =>
      exact absurd (lt_of_lt_of_le (hv.trans (Wp_lt_Om2 S)) (Om_two_le_psiI S n b)) (lt_irrefl _)
    | psiS s b =>
      by_cases hs0 : s = zero
      · subst hs0
        exact ⟨trivial, hA b rfl, fun h => absurd rfl h⟩
      have hs1 := sub_eq_one S hxN.1 hs0 (hv.trans (Wp_lt_Om2 S))
      subst hs1
      have hle := prin_le_Pp S hxN rfl hv
      have hb := arg_le_of_le_Pp S hle
      refine ⟨bcNArgs_tOne S, ?_, fun _ => lt_of_le_of_lt hb (WW_lt_W S)⟩
      exact narg_B S ih hxN hxA hb hx b.size b le_rfl (bcSub_refl b) hxN.2.2

/-- **The arguments of the collapses other than `ψ_{Ω₁}` are below `α_ω`.** -/
theorem bc_nargs {t : Term} (ht : NF t) (hA : bcArgsLt S (bcAlphaWW S) t)
    (hv : val S t < Ordinal.omega0 ^ (Nc.ncPp S + 1)) : bcNArgs S (bcAlphaW S) t :=
  (narg_stage S t.size t le_rfl ht hA).2 hv

end NArg

end Googology.Trans.PoR.InaccPsi.R2.Bc

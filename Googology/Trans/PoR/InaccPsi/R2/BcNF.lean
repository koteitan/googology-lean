import Googology.Trans.PoR.InaccPsi.R2.BcCmp

/-!
# The base change keeps normal forms

`σ = bcSig (bcPre (k+1)) bcPreW`, `σ_A = bcArg (bcPre (k+1)) bcPreW`.

* `bc_NF` (**σ keeps normal forms**): `bcD S t → NF (σ t)`; with it `bcG k t` holds for every
  `bcD`-term (`bcG_of_D`), and `bc_cmp'` is `bc_cmp` without that hypothesis;
* the step: sums and Veblen terms by `bc_cmp`; a prefixed `ψ_{Ω₁}`-argument `α_{k+1} + ρ`
  goes to the normal chain `α_ω + σ(ρ)` (`ρ`'s head is `≤ P' < ω^{P'+1}`); the `K`-condition of a
  collapse is transferred clause by clause (`bc_KLt`): the clause `cmp ψ μ = lt` by `bc_cmp`, the
  clause `cmp b α = lt` by `bc_cmp` on the arguments, or, for `α` prefixed and `b` the argument
  of a collapse other than `ψ_{Ω₁}`, by values (`|σ b| < α_ω ≤ |σ_A α|`).

No axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Bc

open Googology.Notation.InaccPsi Googology.Notation.InaccPsi.Term

section Aux

theorem KLt_bcApp {μ α : Term} : ∀ {P : List Term}, (∀ p ∈ P, KLt μ p α) → ∀ {r : Term},
    KLt μ r α → KLt μ (bcApp P r) α
  | [], _, _, hr => hr
  | [x], hP, r, hr => by
    rw [bcApp_single]; split_ifs
    · exact hP x (by simp)
    · exact ⟨hP x (by simp), hr⟩
  | x :: y :: ys, hP, r, hr => by
    rw [bcApp_cons_cons]
    exact ⟨hP x (by simp), KLt_bcApp (fun p hp => hP p (List.mem_cons_of_mem _ hp)) hr⟩

theorem KLt_bcDrop {μ α : Term} : ∀ (j : ℕ) {b : Term}, KLt μ b α → KLt μ (bcDrop j b) α
  | 0, _, h => h
  | j + 1, add _ _, h => KLt_bcDrop j h.2
  | _ + 1, zero, _ => trivial
  | _ + 1, inacc _, _ => trivial
  | _ + 1, inaccW, _ => trivial
  | _ + 1, phi _ _, _ => trivial
  | _ + 1, om _, _ => trivial
  | _ + 1, psiS _ _, _ => trivial
  | _ + 1, psiI _ _, _ => trivial

theorem bcSig_bcApp {Ps Pt : List Term} : ∀ {P : List Term}, (∀ p ∈ P, bcFree p) → ∀ r : Term,
    bcSig Ps Pt (bcApp P r) = bcApp P (bcSig Ps Pt r)
  | [], _, r => rfl
  | [x], hP, r => by
    rw [bcApp_single, bcApp_single]
    by_cases h : r = zero
    · subst h; simp [bcSig_free (hP x (by simp))]
    · rw [if_neg h, if_neg (bcSig_ne_zero h), bcSig_add, bcSig_free (hP x (by simp))]
  | x :: y :: ys, hP, r => by
    rw [bcApp_cons_cons, bcApp_cons_cons, bcSig_add, bcSig_free (hP x (by simp)),
      bcSig_bcApp (fun p hp => hP p (List.mem_cons_of_mem _ hp)) r]

theorem free_pre (j : ℕ) : ∀ p ∈ bcPre j, bcFree p := by
  intro p hp
  simp only [bcPre, List.mem_cons, List.mem_replicate] at hp
  rcases hp with rfl | rfl | ⟨-, rfl⟩
  · exact bcFree_tW
  · exact bcFree_tW
  · exact bcFree_tPp

theorem head_sub : ∀ (b : Term), bcSub (head b) b
  | add _ _ => Or.inr (Or.inl (Or.inl rfl))
  | zero => Or.inl rfl
  | inacc _ => Or.inl rfl
  | inaccW => Or.inl rfl
  | phi _ _ => Or.inl rfl
  | om _ => Or.inl rfl
  | psiS _ _ => Or.inl rfl
  | psiI _ _ => Or.inl rfl

end Aux

section NFStep

variable (S : InaccSeq.{0}) (k : ℕ)

theorem cmp_rest_lt_Wp (S : InaccSeq.{0}) {r : Term} (hr : NF r) (h : r = zero ∨ cmp (head r) tPp ≠ .gt) :
    cmp r tWp = .lt := by
  by_cases h0 : r = zero
  · subst h0; exact cmp_zero_left (by simp [tWp])
  · have hc := h.resolve_left h0
    rw [cmp_chain hr NF_tWp, bcSl_prin prin_tWp]
    obtain ⟨ys, hys⟩ := head_bcSl h0
    rw [hys]
    have hl := cmp_lt_tWp_of_le S hr.head hc
    simp only [bcLcmp, hl]
    simp

theorem alpha_add_Wp : bcAlpha S (k + 1) + Ordinal.omega0 ^ (Nc.ncPp S + 1) = bcAlphaW S := by
  unfold bcAlpha bcAlphaW
  rw [add_assoc]
  congr 1
  have e : Nc.ncPp S = Ordinal.omega0 ^ Nc.ncPp S := (Low.opow_eq_self_of_SC (Nc.ncPp_SC S)).symm
  refine Ordinal.add_of_omega0_opow_le ?_ le_rfl
  calc Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}) =
        Ordinal.omega0 ^ Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}) := by rw [← e]
    _ < Ordinal.omega0 ^ (Nc.ncPp S + 1) :=
        Ordinal.omega0_opow_mul_nat_lt (Order.lt_add_one_iff.2 le_rfl) _

/-- The image of the proper subterms gives `bcG` for every proper subterm. -/
theorem bcG_of_IH {t : Term} (ih : ∀ w, bcPSub w t → NF (bcSig (bcPre (k + 1)) bcPreW w))
    {z : Term} (hz : bcPSub z t) : bcG k z := by
  refine ⟨fun w hw => ih w (bcPSub_trans t hw (Or.inr hz)), fun a ha => ?_⟩
  subst ha
  have := ih _ hz
  rw [bcSig_psiS_zero] at this
  exact this.2.1

variable {S k}

/-- The image of a `ψ_{Ω₁}`-argument is a normal form. -/
theorem bc_NF_arg {a : Term} (ht : bcD S (psiS zero a))
    (ih : ∀ w, bcPSub w (psiS zero a) → NF (bcSig (bcPre (k + 1)) bcPreW w)) :
    NF (bcArg (bcPre (k + 1)) bcPreW a) := by
  have haN : NF a := ht.1.2.1
  by_cases pa : (bcPre (k + 1)).isPrefixOf (bcSl a) = true
  · rw [bcArg_of_pre pa]
    refine NF_bcApp bcNFL_preW (by simp [bcPreW]) ?_
    set r := bcDrop (bcPre (k + 1)).length a with hr
    by_cases hr0 : r = zero
    · left; rw [hr0, bcSig_zero]
    right
    have hrsub : bcPSub r (psiS zero a) := by
      rcases bcPSub_bcDrop_succ (k + 2) a with h | h
      · exact absurd (by rw [hr, show (bcPre (k + 1)).length = k + 2 + 1 by simp [bcPre]]; exact h) hr0
      · rw [hr, show (bcPre (k + 1)).length = k + 2 + 1 by simp [bcPre]]
        exact Or.inr (Or.inr h)
    have hσr : NF (bcSig (bcPre (k + 1)) bcPreW r) := ih r hrsub
    refine ⟨hσr, ?_⟩
    rw [head_bcSig, bcLast_preW]
    have hrest := (bc_rest_le haN pa).resolve_left hr0
    have hhsub : bcPSub (head r) (psiS zero a) := bcPSub_of_sub_psub (head_sub r) hrsub
    have hc := bc_cmp S k (bcD_sub ht (Or.inr hhsub)) (bcD_free NF_tPp bcFree_tPp)
      (bcG_of_IH k ih hhsub) (bcG_free NF_tPp bcFree_tPp)
    rw [bcSig_free bcFree_tPp] at hc
    rw [cmp_lt_tWp_of_le S (ih _ hhsub) (by rw [hc]; exact hrest.2)]
    simp
  · rw [bcArg_of_not pa]; exact ih a (Or.inr (Or.inl rfl))

/-- `bcG` for a term from the images of its proper subterms. -/
theorem bcG_self {t : Term} (ht : bcD S t)
    (ih : ∀ w, bcPSub w t → NF (bcSig (bcPre (k + 1)) bcPreW w)) : bcG k t := by
  refine ⟨ih, fun a ha => ?_⟩
  subst ha
  exact bc_NF_arg ht ih

/-- The value of the image of a prefixed term. -/
theorem val_sig_pre {b : Term} (hb : NF b) (pb : (bcPre (k + 1)).isPrefixOf (bcSl b) = true) :
    val S (bcSig (bcPre (k + 1)) bcPreW b) = bcAlpha S (k + 1) +
      val S (bcSig (bcPre (k + 1)) bcPreW (bcDrop (bcPre (k + 1)).length b)) := by
  conv_lhs => rw [bcApp_of_prefix (prin_pre (k + 1)) hb pb]
  rw [bcSig_bcApp (free_pre (k + 1)), val_bcApp, ← val_pre S (k + 1), val_bcApp]
  simp only [val, add_zero]

/-- `ψ_{Ω₁}(b)` is below every collapse that is not a `ψ_{Ω₁}`-collapse. -/
theorem cmp_psiS0_lt (S : InaccSeq.{0}) {b μ α : Term} (hb : NF (psiS zero b)) (hμ : NF μ)
    (h : (∃ s, s ≠ zero ∧ μ = psiS s α) ∨ (∃ n, μ = psiI n α)) : cmp (psiS zero b) μ = .lt := by
  rw [cmp_lt_iff S hb hμ, val_psiS_zero]
  refine lt_trans (InaccSeq.psi_lt (S := S) InaccSeq.InR_Om1 _) ?_
  rcases h with ⟨s, hs, rfl⟩ | ⟨n, rfl⟩
  · exact Om_one_lt_val_psiS S hμ.1 hs
  · exact (val_psiI_bounds S n α).2.2.1

/-- The mixed comparison: the argument `b` of a collapse other than `ψ_{Ω₁}` inside `α`. -/
theorem bc_mixed {μ α b α' : Term} (hμ : bcD S μ) (gμ : bcG k μ) (hαsub : bcPSub α μ)
    (hbsub : bcSub b α) (hα' : (μ = psiS zero α → α' = bcArg (bcPre (k + 1)) bcPreW α) ∧
      (μ ≠ psiS zero α → α' = bcSig (bcPre (k + 1)) bcPreW α))
    (hb : cmp b α = .lt) : cmp (bcSig (bcPre (k + 1)) bcPreW b) α' = .lt := by
  have hαD : bcD S α := bcD_sub hμ (Or.inr hαsub)
  have hαG : bcG k α := bcG_sub gμ (Or.inr hαsub)
  have hbD : bcD S b := bcD_sub hαD hbsub
  have hbG : bcG k b := bcG_sub hαG hbsub
  have hbP : bcPSub b μ := bcPSub_of_sub_psub hbsub hαsub
  by_cases hμ0 : μ = psiS zero α
  · rw [hα'.1 hμ0]
    by_cases pα : (bcPre (k + 1)).isPrefixOf (bcSl α) = true
    · have hAα : NF (bcArg (bcPre (k + 1)) bcPreW α) := gμ.2 α hμ0
      have hσb : NF (bcSig (bcPre (k + 1)) bcPreW b) := gμ.1 b hbP
      have hαW : val S α < bcAlphaW S := by
        have := hμ.2; rw [hμ0] at this; exact this.2.2 rfl
      have hbα : val S b < val S α := (cmp_lt_iff S hbD.1 hαD.1).1 hb
      have hge : bcAlphaW S ≤ val S (bcArg (bcPre (k + 1)) bcPreW α) := by
        rw [bcArg_of_pre pα, val_bcApp_preW]; exact le_self_add
      refine cmp_lt_of_val S hσb hAα (lt_of_lt_of_le ?_ hge)
      by_cases pb : (bcPre (k + 1)).isPrefixOf (bcSl b) = true
      · rw [val_sig_pre hbD.1 pb, ← alpha_add_Wp S k]
        refine (add_lt_add_iff_left _).2 ?_
        have hrbD := bcD_drop hbD (bcPre (k + 1)).length
        have hrbG := bcG_drop hbG (bcPre (k + 1)).length
        have h1 := bc_cmp S k hrbD (bcD_free NF_tWp bcFree_tWp) hrbG (bcG_free NF_tWp bcFree_tWp)
        rw [bcSig_free bcFree_tWp] at h1
        have h2 : cmp (bcDrop (bcPre (k + 1)).length b) tWp = .lt := by
          rcases bc_rest_le hbD.1 pb with h | h
          · rw [h]; exact cmp_zero_left (by simp [tWp])
          · exact cmp_rest_lt_Wp S h.1 (Or.inr h.2)
        rw [h2] at h1
        have hσrb : NF (bcSig (bcPre (k + 1)) bcPreW (bcDrop (bcPre (k + 1)).length b)) := by
          have hL : (bcPre (k + 1)).length = k + 2 + 1 := by simp [bcPre]
          rw [hL]
          rcases bcPSub_bcDrop_succ (k + 2) b with h | h
          · rw [h, bcSig_zero]; trivial
          · exact gμ.1 _ (bcPSub_trans μ h (Or.inr hbP))
        have := (cmp_lt_iff S hσrb NF_tWp).1 h1
        rwa [val_tWp] at this
      · have hb1 : val S b < bcAlpha S (k + 1) := by
          by_contra hh
          exact pb ((bc_pre_iff S hbD.1 (hbα.trans hαW)).2 (not_lt.1 hh))
        have h1 := bc_cmp S k hbD (bcD_free (NF_pre (k + 1)) (NF_free_pre (k + 1))) hbG
          (bcG_free (NF_pre (k + 1)) (NF_free_pre (k + 1)))
        rw [bcSig_free (NF_free_pre (k + 1)),
          cmp_lt_of_val S hbD.1 (NF_pre (k + 1)) (by rw [val_pre]; exact hb1)] at h1
        have := (cmp_lt_iff S hσb (NF_pre (k + 1))).1 h1
        rw [val_pre] at this
        exact this.trans (bcAlpha_lt_W S (k + 1))
    · rw [bcArg_of_not pα, bc_cmp S k hbD hαD hbG hαG]; exact hb
  · rw [hα'.2 hμ0, bc_cmp S k hbD hαD hbG hαG]; exact hb

/-- **The `K`-condition is transferred.** -/
theorem bc_KLt {μ α α' : Term} (hμ : bcD S μ) (gμ : bcG k μ)
    (hshape : μ = psiS zero α ∨ (∃ s, s ≠ zero ∧ μ = psiS s α) ∨ (∃ n, μ = psiI n α))
    (hα' : (μ = psiS zero α → α' = bcArg (bcPre (k + 1)) bcPreW α) ∧
      (μ ≠ psiS zero α → α' = bcSig (bcPre (k + 1)) bcPreW α)) :
    ∀ (M : ℕ) (x : Term), x.size ≤ M → bcSub x α → KLt μ x α →
      KLt (bcSig (bcPre (k + 1)) bcPreW μ) (bcSig (bcPre (k + 1)) bcPreW x) α' := by
  have hαsub : bcPSub α μ := by
    rcases hshape with rfl | ⟨s, -, rfl⟩ | ⟨n, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
  have hαD : bcD S α := bcD_sub hμ (Or.inr hαsub)
  intro M
  induction M with
  | zero => intro x hx; exact absurd hx (by have := size_pos x; omega)
  | succ M ih =>
    intro x hx hxα hK
    have hxD : bcD S x := bcD_sub hαD hxα
    have hxP : bcPSub x μ := bcPSub_of_sub_psub hxα hαsub
    have hxG : bcG k x := bcG_sub gμ (Or.inr hxP)
    cases x with
    | zero => rw [bcSig_zero]; trivial
    | inacc _ => rw [bcSig_inacc]; trivial
    | inaccW => rw [bcSig_inaccW]; trivial
    | add a b =>
      simp only [size] at hx
      rw [bcSig_add]
      exact ⟨ih a (by omega) (bcSub_trans (sub_add_l a b) hxα) hK.1,
        ih b (by omega) (bcSub_trans (sub_add_r a b) hxα) hK.2⟩
    | phi a b =>
      simp only [size] at hx
      rw [bcSig_phi]
      exact ⟨ih a (by omega) (bcSub_trans (sub_phi_l a b) hxα) hK.1,
        ih b (by omega) (bcSub_trans (sub_phi_r a b) hxα) hK.2⟩
    | om b =>
      simp only [size] at hx
      rw [bcSig_om]
      rcases hK with hK | hK
      · have hc := bc_cmp S k hxD hμ hxG gμ
        rw [bcSig_om, hK] at hc
        exact Or.inl hc
      · exact Or.inr (ih b (by omega) (bcSub_trans (sub_om b) hxα) hK)
    | psiI n1 b =>
      simp only [size] at hx
      rw [bcSig_psiI]
      by_cases hlt : cmp (psiI n1 b) μ = .lt
      · have hc := bc_cmp S k hxD hμ hxG gμ
        rw [bcSig_psiI, hlt] at hc
        exact Or.inl hc
      · obtain ⟨hb, hKb⟩ := hK.resolve_left hlt
        exact Or.inr ⟨bc_mixed hμ gμ hαsub (bcSub_trans (sub_psiI n1 b) hxα) hα' hb,
          ih b (by omega) (bcSub_trans (sub_psiI n1 b) hxα) hKb⟩
    | psiS s1 b =>
      simp only [size] at hx
      by_cases hlt : cmp (psiS s1 b) μ = .lt
      · have hc := bc_cmp S k hxD hμ hxG gμ
        rw [hlt] at hc
        rw [bcSig_psiS] at hc ⊢
        exact Or.inl hc
      obtain ⟨hb, hKs, hKb⟩ := hK.resolve_left hlt
      rw [bcSig_psiS]
      have hbsub : bcSub b α := bcSub_trans (sub_psiS_a s1 b) hxα
      refine Or.inr ⟨?_, ih s1 (by omega) (bcSub_trans (sub_psiS_s s1 b) hxα) hKs, ?_⟩
      · by_cases hs1 : s1 = zero
        · subst hs1
          rw [if_pos rfl]
          have hμ0 : μ = psiS zero α := by
            rcases hshape with h | h
            · exact h
            · exact absurd (cmp_psiS0_lt S hxD.1 hμ.1 h) hlt
          rw [hα'.1 hμ0]
          have hc := bc_cmp S k hxD hμ hxG gμ
          rw [hμ0, bcSig_psiS_zero, bcSig_psiS_zero, cmp_psiS_psiS, cmp_psiS_psiS, cmp_self,
            if_pos rfl, if_pos rfl] at hc
          rw [hc]; exact hb
        · rw [if_neg hs1]
          exact bc_mixed hμ gμ hαsub hbsub hα' hb
      · by_cases hs1 : s1 = zero
        · subst hs1
          rw [if_pos rfl]
          have hμ0 : μ = psiS zero α := by
            rcases hshape with h | h
            · exact h
            · exact absurd (cmp_psiS0_lt S hxD.1 hμ.1 h) hlt
          have hbD : bcD S b := bcD_sub hαD hbsub
          by_cases pb : (bcPre (k + 1)).isPrefixOf (bcSl b) = true
          · rw [bcArg_of_pre pb]
            -- `α` is prefixed too, so `α' ≥ α_ω > Ω_ω·2`
            have hαW : val S α < bcAlphaW S := by
              have := hμ.2; rw [hμ0] at this; exact this.2.2 rfl
            have hbα : val S b < val S α := (cmp_lt_iff S hbD.1 hαD.1).1 hb
            have pα : (bcPre (k + 1)).isPrefixOf (bcSl α) = true :=
              (bc_pre_iff S hαD.1 hαW).2 (le_trans ((bc_pre_iff S hbD.1 (hbα.trans hαW)).1 pb)
                hbα.le)
            have hAα : NF (bcArg (bcPre (k + 1)) bcPreW α) := gμ.2 α hμ0
            have hWW : cmp (add tW tW) α' = .lt := by
              rw [hα'.1 hμ0]
              refine cmp_lt_of_val S NF_add_tW_tW hAα ?_
              rw [bcArg_of_pre pα, val_bcApp_preW]
              refine lt_of_lt_of_le ?_ le_self_add
              show val S tW + val S tW < bcAlphaW S
              rw [val_tW]; unfold bcAlphaW
              exact lt_add_of_pos_right _ (Ordinal.opow_pos _ Ordinal.omega0_pos)
            refine KLt_bcApp (fun p hp => ?_) ?_
            · simp only [bcPreW, List.mem_cons, List.not_mem_nil, or_false] at hp
              rcases hp with rfl | rfl | rfl
              · exact KLt_tW _ _
              · exact KLt_tW _ _
              · exact KLt_tWp hWW
            · set rb := bcDrop (bcPre (k + 1)).length b with hrb
              rcases bcSub_bcDrop (bcPre (k + 1)).length b with h | h
              · rw [← hrb] at h; rw [h, bcSig_zero]; trivial
              · exact ih rb (by have := bcDrop_size_le (bcPre (k + 1)).length b; rw [← hrb] at this; omega)
                  (bcSub_trans h hbsub) (KLt_bcDrop _ hKb)
          · rw [bcArg_of_not pb]
            exact ih b (by omega) hbsub hKb
        · rw [if_neg hs1]
          exact ih b (by omega) hbsub hKb


theorem bc_NF_all : ∀ (N : ℕ) (t : Term), t.size ≤ N → bcD S t →
    NF (bcSig (bcPre (k + 1)) bcPreW t)
  | 0, t, h, _ => absurd h (by have := size_pos t; omega)
  | N + 1, t, hN, hD => by
    have IHsub : ∀ w, bcPSub w t → NF (bcSig (bcPre (k + 1)) bcPreW w) := fun w hw =>
      bc_NF_all N w (by have := bcPSub_size hw; omega) (bcD_sub hD (Or.inr hw))
    have gt : bcG k t := bcG_self hD IHsub
    have hG : ∀ {w}, bcPSub w t → bcG k w := fun hw => bcG_of_IH k IHsub hw
    have hDs : ∀ {w}, bcPSub w t → bcD S w := fun hw => bcD_sub hD (Or.inr hw)
    cases t with
    | zero => rw [bcSig_zero]; trivial
    | inacc _ => rw [bcSig_inacc]; trivial
    | inaccW => rw [bcSig_inaccW]; trivial
    | add a b =>
      have ha : bcPSub a (add a b) := Or.inl (Or.inl rfl)
      have hb : bcPSub b (add a b) := Or.inr (Or.inl rfl)
      have hhb : bcPSub (head b) (add a b) := bcPSub_of_sub_psub (head_sub b) hb
      rw [bcSig_add]
      refine ⟨IHsub a ha, IHsub b hb, by rw [isPrin_bcSig]; exact hD.1.2.2.1,
        bcSig_ne_zero hD.1.2.2.2.1, ?_⟩
      rw [head_bcSig, bc_cmp S k (hDs hhb) (hDs ha) (hG hhb) (hG ha)]
      exact hD.1.2.2.2.2
    | phi a b =>
      have ha : bcPSub a (phi a b) := Or.inl (Or.inl rfl)
      have hb : bcPSub b (phi a b) := Or.inr (Or.inl rfl)
      rw [bcSig_phi]
      refine ⟨IHsub a ha, IHsub b hb, ?_, ?_⟩
      · rw [← bcSig_phi, bc_cmp S k (hDs ha) hD (hG ha) gt]; exact hD.1.2.2.1
      · rw [← bcSig_phi, bc_cmp S k (hDs hb) hD (hG hb) gt]; exact hD.1.2.2.2
    | om a =>
      rw [bcSig_om]
      exact ⟨IHsub a (Or.inl rfl), bcSig_ne_zero hD.1.2.1, by rw [isF_bcSig]; exact hD.1.2.2⟩
    | psiI n a =>
      have h := bc_KLt hD gt (Or.inr (Or.inr ⟨n, rfl⟩)) (α' := bcSig (bcPre (k + 1)) bcPreW a)
        ⟨fun h => Term.noConfusion h, fun _ => rfl⟩ a.size a le_rfl (bcSub_refl a) hD.1.2
      rw [bcSig_psiI] at h ⊢
      exact ⟨IHsub a (Or.inl rfl), h⟩
    | psiS s a =>
      by_cases hs0 : s = zero
      · subst hs0
        have hA : NF (bcArg (bcPre (k + 1)) bcPreW a) := bc_NF_arg hD IHsub
        rw [bcSig_psiS_zero]
        refine ⟨trivial, hA, ?_⟩
        have hK := hD.1.2.2
        have key : ∀ x, bcSub x a → KLt (psiS zero a) x a →
            KLt (psiS zero (bcArg (bcPre (k + 1)) bcPreW a)) (bcSig (bcPre (k + 1)) bcPreW x)
              (bcArg (bcPre (k + 1)) bcPreW a) := by
          intro x hx hKx
          have h := bc_KLt hD gt (Or.inl rfl) (α' := bcArg (bcPre (k + 1)) bcPreW a)
            ⟨fun _ => rfl, fun h => absurd rfl h⟩ x.size x le_rfl hx hKx
          rwa [bcSig_psiS_zero] at h
        by_cases pa : (bcPre (k + 1)).isPrefixOf (bcSl a) = true
        · have hαW : val S a < bcAlphaW S := hD.2.2.2 rfl
          have hWW : cmp (add tW tW) (bcArg (bcPre (k + 1)) bcPreW a) = .lt := by
            refine cmp_lt_of_val S NF_add_tW_tW hA ?_
            rw [bcArg_of_pre pa, val_bcApp_preW]
            refine lt_of_lt_of_le ?_ le_self_add
            show val S tW + val S tW < bcAlphaW S
            rw [val_tW]; unfold bcAlphaW
            exact lt_add_of_pos_right _ (Ordinal.opow_pos _ Ordinal.omega0_pos)
          conv => enter [2]; rw [bcArg_of_pre pa]
          refine KLt_bcApp (fun p hp => ?_) ?_
          · simp only [bcPreW, List.mem_cons, List.not_mem_nil, or_false] at hp
            rcases hp with rfl | rfl | rfl
            · exact KLt_tW _ _
            · exact KLt_tW _ _
            · exact KLt_tWp hWW
          · rcases bcSub_bcDrop (bcPre (k + 1)).length a with h | h
            · rw [h, bcSig_zero]; trivial
            · exact key _ h (KLt_bcDrop _ hK)
        · conv => enter [2]; rw [bcArg_of_not pa]
          exact key a (bcSub_refl a) hK
      · have h := bc_KLt hD gt (Or.inr (Or.inl ⟨s, hs0, rfl⟩))
          (α' := bcSig (bcPre (k + 1)) bcPreW a)
          ⟨fun h => absurd (Term.psiS.inj h).1 hs0, fun _ => rfl⟩ a.size a le_rfl
          (bcSub_refl a) hD.1.2.2
        rw [bcSig_psiS_ne hs0] at h ⊢
        exact ⟨IHsub s (Or.inl (Or.inl rfl)), IHsub a (Or.inr (Or.inl rfl)), h⟩

/-- **The base change keeps normal forms.** -/
theorem bc_NF {t : Term} (hD : bcD S t) : NF (bcSig (bcPre (k + 1)) bcPreW t) :=
  bc_NF_all _ t le_rfl hD

theorem bcG_of_D {t : Term} (hD : bcD S t) : bcG k t :=
  bcG_self hD (fun _ hw => bc_NF (bcD_sub hD (Or.inr hw)))

/-- **The base change keeps `cmp` on the domain.** -/
theorem bc_cmp' {s t : Term} (hs : bcD S s) (ht : bcD S t) :
    cmp (bcSig (bcPre (k + 1)) bcPreW s) (bcSig (bcPre (k + 1)) bcPreW t) = cmp s t :=
  bc_cmp S k hs ht (bcG_of_D hs) (bcG_of_D ht)

/-- The base change keeps and reflects `<` of values on the domain. -/
theorem bc_lt_iff {s t : Term} (hs : bcD S s) (ht : bcD S t) :
    val S (bcSig (bcPre (k + 1)) bcPreW s) < val S (bcSig (bcPre (k + 1)) bcPreW t) ↔
      val S s < val S t := by
  rw [← cmp_lt_iff S (bc_NF hs) (bc_NF ht), bc_cmp' hs ht, cmp_lt_iff S hs.1 ht.1]

end NFStep

end Googology.Trans.PoR.InaccPsi.R2.Bc

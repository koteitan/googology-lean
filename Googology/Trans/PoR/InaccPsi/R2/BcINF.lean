import Googology.Trans.PoR.InaccPsi.R2.BcICmp
import Googology.Trans.PoR.InaccPsi.R2.BcNF

/-!
# The inverse base change keeps normal forms

`τ = bcSig bcPreW (bcPre (m+1))`, `τ_A = bcArg bcPreW (bcPre (m+1))`.

* `bci_NF` (**τ keeps normal forms** on `bciD`), `bci_cmp'`, `bci_lt_iff`: as `BcNF` for `σ`;
  a prefixed argument `α_ω + ρ` (`ρ < P'`) goes to the normal chain `α_{m+1} + τ(ρ)`; in the
  `K`-condition, the argument `b` of a collapse other than `ψ_{Ω₁}` is `< α_{m+1}` (domain), so
  `τ(b) < α_{m+1} ≤ τ_A(α)` (`bci_img_lt`).

No axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Bc

open Googology.Notation.InaccPsi Googology.Notation.InaccPsi.Term

section INF

variable (S : InaccSeq.{0}) (m : ℕ)

theorem bciG_of_IH {t : Term} (ih : ∀ w, bcPSub w t → NF (bcSig bcPreW (bcPre (m + 1)) w))
    {z : Term} (hz : bcPSub z t) : bciG m z := by
  refine ⟨fun w hw => ih w (bcPSub_trans t hw (Or.inr hz)), fun a ha => ?_⟩
  subst ha
  have := ih _ hz
  rw [bcSig_psiS_zero] at this
  exact this.2.1

variable {S m}

theorem bci_NF_arg {a : Term} (ht : bciD S m (psiS zero a))
    (ih : ∀ w, bcPSub w (psiS zero a) → NF (bcSig bcPreW (bcPre (m + 1)) w)) :
    NF (bcArg bcPreW (bcPre (m + 1)) a) := by
  have haN : NF a := ht.1.2.1
  by_cases pa : bcPreW.isPrefixOf (bcSl a) = true
  · rw [bcArg_of_pre pa]
    refine NF_bcApp (bcNFL_pre (m + 1)) (by simp [bcPre]) ?_
    have hrlt : val S (bcDrop bcPreW.length a) < Ordinal.omega0 ^ (Nc.ncPp S + 1) :=
      bci_rest_lt S haN (bci_arg_lt S m ht) pa
    set r := bcDrop bcPreW.length a with hr
    by_cases hr0 : r = zero
    · left; rw [hr0, bcSig_zero]
    right
    have hrsub : bcPSub r (psiS zero a) := by
      rcases bcPSub_bcDrop_succ 2 a with h | h
      · exact absurd (by rw [hr, show bcPreW.length = 2 + 1 from rfl]; exact h) hr0
      · rw [hr, show bcPreW.length = 2 + 1 from rfl]; exact Or.inr (Or.inr h)
    have hσr := ih r hrsub
    refine ⟨hσr, ?_⟩
    rw [head_bcSig, bcLast_pre m]
    have hrN : NF r := NF_bcDrop _ haN
    have hhsub : bcPSub (head r) (psiS zero a) := bcPSub_of_sub_psub (head_sub r) hrsub
    have hc := bci_cmp S m (bciD_sub ht (Or.inr hhsub)) (bciD_tPp S m)
      (bciG_of_IH m ih hhsub) (bciG_tPp m)
    rw [bcSig_free bcFree_tPp] at hc
    have hle : cmp (head r) tPp ≠ .gt := by
      intro hg
      exact not_between_Pp S hrN.head (isPrin_head hrN hr0) hg
        (cmp_lt_of_val S hrN.head NF_tWp (by rw [val_tWp]; exact lt_of_le_of_lt (val_head_le S hrN) hrlt))
    rw [hc]; exact hle
  · rw [bcArg_of_not pa]; exact ih a (Or.inr (Or.inl rfl))

theorem bciG_self {t : Term} (ht : bciD S m t)
    (ih : ∀ w, bcPSub w t → NF (bcSig bcPreW (bcPre (m + 1)) w)) : bciG m t := by
  refine ⟨ih, fun a ha => ?_⟩
  subst ha
  exact bci_NF_arg ht ih

/-- The mixed comparison: the argument `b < α_{m+1}` of a collapse other than `ψ_{Ω₁}`. -/
theorem bci_mixed {μ α b α' : Term} (hμ : bciD S m μ) (gμ : bciG m μ) (hαsub : bcPSub α μ)
    (hbsub : bcSub b α) (hα' : (μ = psiS zero α → α' = bcArg bcPreW (bcPre (m + 1)) α) ∧
      (μ ≠ psiS zero α → α' = bcSig bcPreW (bcPre (m + 1)) α))
    (hb : cmp b α = .lt) (hbB : val S b < bcAlpha S (m + 1)) :
    cmp (bcSig bcPreW (bcPre (m + 1)) b) α' = .lt := by
  have hαD : bciD S m α := bciD_sub hμ (Or.inr hαsub)
  have hαG : bciG m α := bciG_sub gμ (Or.inr hαsub)
  have hbD : bciD S m b := bciD_sub hαD hbsub
  have hbG : bciG m b := bciG_sub hαG hbsub
  have hbP : bcPSub b μ := bcPSub_of_sub_psub hbsub hαsub
  by_cases hμ0 : μ = psiS zero α
  · rw [hα'.1 hμ0]
    by_cases pα : bcPreW.isPrefixOf (bcSl α) = true
    · have hAα : NF (bcArg bcPreW (bcPre (m + 1)) α) := gμ.2 α hμ0
      have hσb : NF (bcSig bcPreW (bcPre (m + 1)) b) := gμ.1 b hbP
      have hb1 := bci_img_lt S m hbD.1 hσb hbB (fun x hx => by
        have hxs := mem_bcSl_sub hx
        have e1 := bci_cmp S m (bciD_sub hbD hxs) (bciD_tW S m) (bciG_sub hbG hxs) (bciG_tW m)
        have e2 := bci_cmp S m (bciD_sub hbD hxs) (bciD_tPp S m) (bciG_sub hbG hxs) (bciG_tPp m)
        rw [bcSig_free bcFree_tW] at e1
        rw [bcSig_free bcFree_tPp] at e2
        exact ⟨e1, e2⟩)
      exact cmp_lt_of_val S hσb hAα (lt_of_lt_of_le hb1 (val_tauA_ge S m pα))
    · rw [bcArg_of_not pα, bci_cmp S m hbD hαD hbG hαG]; exact hb
  · rw [hα'.2 hμ0, bci_cmp S m hbD hαD hbG hαG]; exact hb

/-- **The `K`-condition is transferred.** -/
theorem bci_KLt {μ α α' : Term} (hμ : bciD S m μ) (gμ : bciG m μ)
    (hshape : μ = psiS zero α ∨ (∃ s, s ≠ zero ∧ μ = psiS s α) ∨ (∃ n, μ = psiI n α))
    (hα' : (μ = psiS zero α → α' = bcArg bcPreW (bcPre (m + 1)) α) ∧
      (μ ≠ psiS zero α → α' = bcSig bcPreW (bcPre (m + 1)) α)) :
    ∀ (M : ℕ) (x : Term), x.size ≤ M → bcSub x α → KLt μ x α →
      KLt (bcSig bcPreW (bcPre (m + 1)) μ) (bcSig bcPreW (bcPre (m + 1)) x) α' := by
  have hαsub : bcPSub α μ := by
    rcases hshape with rfl | ⟨s, -, rfl⟩ | ⟨n, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
  have hαD : bciD S m α := bciD_sub hμ (Or.inr hαsub)
  intro M
  induction M with
  | zero => intro x hx; exact absurd hx (by have := size_pos x; omega)
  | succ M ih =>
    intro x hx hxα hK
    have hxD : bciD S m x := bciD_sub hαD hxα
    have hxP : bcPSub x μ := bcPSub_of_sub_psub hxα hαsub
    have hxG : bciG m x := bciG_sub gμ (Or.inr hxP)
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
      · have hc := bci_cmp S m hxD hμ hxG gμ
        rw [bcSig_om, hK] at hc
        exact Or.inl hc
      · exact Or.inr (ih b (by omega) (bcSub_trans (sub_om b) hxα) hK)
    | psiI n1 b =>
      simp only [size] at hx
      rw [bcSig_psiI]
      by_cases hlt : cmp (psiI n1 b) μ = .lt
      · have hc := bci_cmp S m hxD hμ hxG gμ
        rw [bcSig_psiI, hlt] at hc
        exact Or.inl hc
      · obtain ⟨hb, hKb⟩ := hK.resolve_left hlt
        exact Or.inr ⟨bci_mixed hμ gμ hαsub (bcSub_trans (sub_psiI n1 b) hxα) hα' hb hxD.2.2,
          ih b (by omega) (bcSub_trans (sub_psiI n1 b) hxα) hKb⟩
    | psiS s1 b =>
      simp only [size] at hx
      by_cases hlt : cmp (psiS s1 b) μ = .lt
      · have hc := bci_cmp S m hxD hμ hxG gμ
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
          have hc := bci_cmp S m hxD hμ hxG gμ
          rw [hμ0, bcSig_psiS_zero, bcSig_psiS_zero, cmp_psiS_psiS, cmp_psiS_psiS, cmp_self,
            if_pos rfl, if_pos rfl] at hc
          rw [hc]; exact hb
        · rw [if_neg hs1]
          exact bci_mixed hμ gμ hαsub hbsub hα' hb (hxD.2.2.2.2 hs1)
      · by_cases hs1 : s1 = zero
        · subst hs1
          rw [if_pos rfl]
          have hμ0 : μ = psiS zero α := by
            rcases hshape with h | h
            · exact h
            · exact absurd (cmp_psiS0_lt S hxD.1 hμ.1 h) hlt
          have hbD : bciD S m b := bciD_sub hαD hbsub
          by_cases pb : bcPreW.isPrefixOf (bcSl b) = true
          · rw [bcArg_of_pre pb]
            -- `α` is prefixed too, so `α' ≥ α_{m+1} > Ω_ω·2`
            have hbW : val S b < bcAlphaWW S := bci_arg_lt S m hxD
            have hαW : val S α < bcAlphaWW S := by
              have := hμ; rw [hμ0] at this; exact bci_arg_lt S m this
            have hbα : val S b < val S α := (cmp_lt_iff S hbD.1 hαD.1).1 hb
            have pα : bcPreW.isPrefixOf (bcSl α) = true :=
              (bci_pre_iff S hαD.1 hαW).2 (le_trans ((bci_pre_iff S hbD.1 hbW).1 pb) hbα.le)
            have hAα : NF (bcArg bcPreW (bcPre (m + 1)) α) := gμ.2 α hμ0
            have hWW : cmp (add tW tW) α' = .lt := by
              rw [hα'.1 hμ0]
              exact cmp_lt_of_val S NF_add_tW_tW hAα
                (lt_of_lt_of_le (WW_lt_alpha S m) (val_tauA_ge S m pα))
            refine KLt_bcApp (fun p hp => ?_) ?_
            · simp only [bcPre, List.mem_cons, List.mem_replicate] at hp
              rcases hp with rfl | rfl | ⟨-, rfl⟩
              · exact KLt_tW _ _
              · exact KLt_tW _ _
              · exact KLt_tPp hWW
            · set rb := bcDrop bcPreW.length b with hrb
              rcases bcSub_bcDrop bcPreW.length b with h | h
              · rw [← hrb] at h; rw [h, bcSig_zero]; trivial
              · exact ih rb (by have := bcDrop_size_le bcPreW.length b; rw [← hrb] at this; omega)
                  (bcSub_trans h hbsub) (KLt_bcDrop _ hKb)
          · rw [bcArg_of_not pb]
            exact ih b (by omega) hbsub hKb
        · rw [if_neg hs1]
          exact ih b (by omega) hbsub hKb


theorem bci_NF_all : ∀ (N : ℕ) (t : Term), t.size ≤ N → bciD S m t →
    NF (bcSig bcPreW (bcPre (m + 1)) t)
  | 0, t, h, _ => absurd h (by have := size_pos t; omega)
  | N + 1, t, hN, hD => by
    have IHsub : ∀ w, bcPSub w t → NF (bcSig bcPreW (bcPre (m + 1)) w) := fun w hw =>
      bci_NF_all N w (by have := bcPSub_size hw; omega) (bciD_sub hD (Or.inr hw))
    have gt : bciG m t := bciG_self hD IHsub
    have hG : ∀ {w}, bcPSub w t → bciG m w := fun hw => bciG_of_IH m IHsub hw
    have hDs : ∀ {w}, bcPSub w t → bciD S m w := fun hw => bciD_sub hD (Or.inr hw)
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
      rw [head_bcSig, bci_cmp S m (hDs hhb) (hDs ha) (hG hhb) (hG ha)]
      exact hD.1.2.2.2.2
    | phi a b =>
      have ha : bcPSub a (phi a b) := Or.inl (Or.inl rfl)
      have hb : bcPSub b (phi a b) := Or.inr (Or.inl rfl)
      rw [bcSig_phi]
      refine ⟨IHsub a ha, IHsub b hb, ?_, ?_⟩
      · rw [← bcSig_phi, bci_cmp S m (hDs ha) hD (hG ha) gt]; exact hD.1.2.2.1
      · rw [← bcSig_phi, bci_cmp S m (hDs hb) hD (hG hb) gt]; exact hD.1.2.2.2
    | om a =>
      rw [bcSig_om]
      exact ⟨IHsub a (Or.inl rfl), bcSig_ne_zero hD.1.2.1, by rw [isF_bcSig]; exact hD.1.2.2⟩
    | psiI n a =>
      have h := bci_KLt hD gt (Or.inr (Or.inr ⟨n, rfl⟩)) (α' := bcSig bcPreW (bcPre (m + 1)) a)
        ⟨fun h => Term.noConfusion h, fun _ => rfl⟩ a.size a le_rfl (bcSub_refl a) hD.1.2
      rw [bcSig_psiI] at h ⊢
      exact ⟨IHsub a (Or.inl rfl), h⟩
    | psiS s a =>
      by_cases hs0 : s = zero
      · subst hs0
        have hA : NF (bcArg bcPreW (bcPre (m + 1)) a) := bci_NF_arg hD IHsub
        rw [bcSig_psiS_zero]
        refine ⟨trivial, hA, ?_⟩
        have hK := hD.1.2.2
        have key : ∀ x, bcSub x a → KLt (psiS zero a) x a →
            KLt (psiS zero (bcArg bcPreW (bcPre (m + 1)) a)) (bcSig bcPreW (bcPre (m + 1)) x)
              (bcArg bcPreW (bcPre (m + 1)) a) := by
          intro x hx hKx
          have h := bci_KLt hD gt (Or.inl rfl) (α' := bcArg bcPreW (bcPre (m + 1)) a)
            ⟨fun _ => rfl, fun h => absurd rfl h⟩ x.size x le_rfl hx hKx
          rwa [bcSig_psiS_zero] at h
        by_cases pa : bcPreW.isPrefixOf (bcSl a) = true
        · have hWW : cmp (add tW tW) (bcArg bcPreW (bcPre (m + 1)) a) = .lt :=
            cmp_lt_of_val S NF_add_tW_tW hA (lt_of_lt_of_le (WW_lt_alpha S m) (val_tauA_ge S m pa))
          conv => enter [2]; rw [bcArg_of_pre pa]
          refine KLt_bcApp (fun p hp => ?_) ?_
          · simp only [bcPre, List.mem_cons, List.mem_replicate] at hp
            rcases hp with rfl | rfl | ⟨-, rfl⟩
            · exact KLt_tW _ _
            · exact KLt_tW _ _
            · exact KLt_tPp hWW
          · rcases bcSub_bcDrop bcPreW.length a with h | h
            · rw [h, bcSig_zero]; trivial
            · exact key _ h (KLt_bcDrop _ hK)
        · conv => enter [2]; rw [bcArg_of_not pa]
          exact key a (bcSub_refl a) hK
      · have h := bci_KLt hD gt (Or.inr (Or.inl ⟨s, hs0, rfl⟩))
          (α' := bcSig bcPreW (bcPre (m + 1)) a)
          ⟨fun h => absurd (Term.psiS.inj h).1 hs0, fun _ => rfl⟩ a.size a le_rfl
          (bcSub_refl a) hD.1.2.2
        rw [bcSig_psiS_ne hs0] at h ⊢
        exact ⟨IHsub s (Or.inl (Or.inl rfl)), IHsub a (Or.inr (Or.inl rfl)), h⟩

/-- **The inverse base change keeps normal forms.** -/
theorem bci_NF {t : Term} (hD : bciD S m t) : NF (bcSig bcPreW (bcPre (m + 1)) t) :=
  bci_NF_all _ t le_rfl hD

theorem bciG_of_D {t : Term} (hD : bciD S m t) : bciG m t :=
  bciG_self hD (fun _ hw => bci_NF (bciD_sub hD (Or.inr hw)))

/-- **The inverse base change keeps `cmp` on its domain.** -/
theorem bci_cmp' {s t : Term} (hs : bciD S m s) (ht : bciD S m t) :
    cmp (bcSig bcPreW (bcPre (m + 1)) s) (bcSig bcPreW (bcPre (m + 1)) t) = cmp s t :=
  bci_cmp S m hs ht (bciG_of_D hs) (bciG_of_D ht)

end INF

end Googology.Trans.PoR.InaccPsi.R2.Bc

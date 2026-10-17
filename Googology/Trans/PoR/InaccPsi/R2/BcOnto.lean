import Googology.Trans.PoR.InaccPsi.R2.BcNArg
import Googology.Trans.PoR.InaccPsi.R2.BcMap

/-!
# ONTO-FIN for the base changes `B_n`

* `bci_eventually`: a normal form whose `ψ_{Ω₁}`-arguments are `< α_ω + P'·ω` and whose other
  collapse arguments are `< α_ω` lies in the domain of `τ_m` for every large `m`;
* `bc_sig_tau` (**σ_m ∘ τ_m = id** on the domain of `τ_m`): a prefixed argument `α_ω + ρ` goes to
  `α_{m+1} + τ(ρ)` and back; an argument `a < α_{m+1}` is not prefixed, nor is its image (the
  summands `Ω_ω`, `P'` are fixed and only come from themselves);
* `bcOnto` (**ONTO-FIN**): every finite `Y ⊆ [L(ω), L(ω+1))` lies in `B_n[[0, L(n+2))]` for
  every large `n`: the preimage of `y` is `|τ_n(nf y)|`, which is `< L(n+2) = |τ_n(nf L(ω+1))|`.

No axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Bc

open Googology.Notation.InaccPsi Googology.Notation.InaccPsi.Term

section Onto

variable (S : InaccSeq.{0})

theorem bciArgs_mono {m m' : ℕ} (hm : m ≤ m') : ∀ {t : Term}, bciArgs S m t → bciArgs S m' t := by
  have hα : bcAlpha S (m + 1) ≤ bcAlpha S (m' + 1) := by
    rcases (show m + 1 ≤ m' + 1 by omega).lt_or_eq with h | h
    · exact (alpha_lt_alpha S h).le
    · rw [h]
  intro t h
  induction t with
  | zero => trivial
  | inacc _ => trivial
  | inaccW => trivial
  | add a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | phi a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | om a iha => exact iha h
  | psiS s a ihs iha =>
    refine ⟨ihs h.1, iha h.2.1, fun hs => ?_, fun hs => (h.2.2.2 hs).trans_le hα⟩
    rcases h.2.2.1 hs with h' | h'
    · exact Or.inl (h'.trans_le hα)
    · exact Or.inr h'
  | psiI _ a iha => exact ⟨iha h.1, h.2.trans_le hα⟩

theorem lt_alphaW_exists {v : Ordinal.{0}} (h : v < bcAlphaW S) : ∃ j : ℕ, v < bcAlpha S j := by
  by_cases h0 : v < Om Ordinal.omega0 + Om Ordinal.omega0
  · exact ⟨0, by unfold bcAlpha; simpa using h0⟩
  obtain ⟨d, hd⟩ := exists_add_of_le (not_lt.1 h0)
  have hd' : d < Nc.ncPp S * Ordinal.omega0 := by
    rw [ncPp_mul_omega]
    unfold bcAlphaW at h
    rw [hd] at h
    exact (add_lt_add_iff_left _).1 h
  obtain ⟨c, hc, hdc⟩ := (Ordinal.lt_mul_iff_of_isSuccLimit Ordinal.isSuccLimit_omega0).1 hd'
  obtain ⟨j, rfl⟩ := Ordinal.lt_omega0.1 hc
  exact ⟨j, by unfold bcAlpha; rw [hd]; exact (add_lt_add_iff_left _).2 hdc⟩

/-- **Eventually in the domain of `τ_m`.** -/
theorem bci_eventually : ∀ {t : Term}, NF t → bcArgsLt S (bcAlphaWW S) t →
    bcNArgs S (bcAlphaW S) t → ∃ M : ℕ, ∀ m, M ≤ m → bciArgs S m t
  | zero, _, _, _ => ⟨0, fun _ _ => trivial⟩
  | inacc _, _, _, _ => ⟨0, fun _ _ => trivial⟩
  | inaccW, _, _, _ => ⟨0, fun _ _ => trivial⟩
  | add a b, h, hA, hN => by
    obtain ⟨M1, h1⟩ := bci_eventually h.1 hA.1 hN.1
    obtain ⟨M2, h2⟩ := bci_eventually h.2.1 hA.2 hN.2
    exact ⟨max M1 M2, fun m hm => ⟨h1 m (le_of_max_le_left hm), h2 m (le_of_max_le_right hm)⟩⟩
  | phi a b, h, hA, hN => by
    obtain ⟨M1, h1⟩ := bci_eventually h.1 hA.1 hN.1
    obtain ⟨M2, h2⟩ := bci_eventually h.2.1 hA.2 hN.2
    exact ⟨max M1 M2, fun m hm => ⟨h1 m (le_of_max_le_left hm), h2 m (le_of_max_le_right hm)⟩⟩
  | om a, h, hA, hN => by
    obtain ⟨M, h1⟩ := bci_eventually h.1 hA hN
    exact ⟨M, h1⟩
  | psiI n a, h, hA, hN => by
    obtain ⟨M1, h1⟩ := bci_eventually h.1 hA hN.1
    obtain ⟨j, hj⟩ := lt_alphaW_exists S hN.2
    refine ⟨max M1 j, fun m hm => ⟨h1 m (le_of_max_le_left hm), ?_⟩⟩
    refine hj.trans_le ?_
    rcases (show j ≤ m + 1 by have := le_of_max_le_right hm; omega).lt_or_eq with h' | h'
    · exact (alpha_lt_alpha S h').le
    · rw [h']
  | psiS s a, h, hA, hN => by
    obtain ⟨M1, h1⟩ := bci_eventually h.1 hA.1 hN.1
    obtain ⟨M2, h2⟩ := bci_eventually h.2.1 hA.2.1 hN.2.1
    have key : ∃ M3 : ℕ, ∀ m, M3 ≤ m →
        (s = zero → (val S a < bcAlpha S (m + 1) ∨
          (bcAlphaW S ≤ val S a ∧ val S a < bcAlphaWW S))) ∧
        (s ≠ zero → val S a < bcAlpha S (m + 1)) := by
      have hle : ∀ {j m : ℕ}, j ≤ m → bcAlpha S j ≤ bcAlpha S (m + 1) := fun {j m} hjm => by
        rcases (show j ≤ m + 1 by omega).lt_or_eq with h' | h'
        · exact (alpha_lt_alpha S h').le
        · rw [h']
      by_cases hs : s = zero
      · by_cases ha : val S a < bcAlphaW S
        · obtain ⟨j, hj⟩ := lt_alphaW_exists S ha
          exact ⟨j, fun m hm => ⟨fun _ => Or.inl (hj.trans_le (hle hm)), fun h' => absurd hs h'⟩⟩
        · exact ⟨0, fun m _ => ⟨fun hs' => Or.inr ⟨not_lt.1 ha, hA.2.2 hs'⟩, fun h' => absurd hs h'⟩⟩
      · obtain ⟨j, hj⟩ := lt_alphaW_exists S (hN.2.2 hs)
        exact ⟨j, fun m hm => ⟨fun h' => absurd h' hs, fun _ => hj.trans_le (hle hm)⟩⟩
    obtain ⟨M3, h3⟩ := key
    refine ⟨max M1 (max M2 M3), fun m hm => ?_⟩
    have hm1 := le_of_max_le_left hm
    have hm2 := le_of_max_le_left (le_of_max_le_right hm)
    have hm3 := le_of_max_le_right (le_of_max_le_right hm)
    exact ⟨h1 m hm1, h2 m hm2, (h3 m hm3).1, (h3 m hm3).2⟩

theorem bcFree_of_sig {Ps Pt : List Term} : ∀ {x : Term}, bcFree (bcSig Ps Pt x) → bcFree x
  | zero, _ => trivial
  | inacc _, _ => trivial
  | inaccW, _ => trivial
  | add a b, h => by rw [bcSig_add] at h; exact ⟨bcFree_of_sig h.1, bcFree_of_sig h.2⟩
  | phi a b, h => by rw [bcSig_phi] at h; exact ⟨bcFree_of_sig h.1, bcFree_of_sig h.2⟩
  | om a, h => by rw [bcSig_om] at h; exact bcFree_of_sig (x := a) (show bcFree (bcSig Ps Pt a) from h)
  | psiI _ a, h => by
    rw [bcSig_psiI] at h; exact bcFree_of_sig (x := a) (show bcFree (bcSig Ps Pt a) from h)
  | psiS s a, h => by
    rw [bcSig_psiS] at h
    have hs : s ≠ zero := fun e => h.1 (by rw [e, bcSig_zero])
    rw [if_neg hs] at h
    exact ⟨hs, bcFree_of_sig h.2.1, bcFree_of_sig h.2.2⟩

theorem isPrefixOf_map_free {Ps Pt : List Term} : ∀ (P X : List Term), (∀ q ∈ P, bcFree q) →
    P.isPrefixOf (X.map (bcSig Ps Pt)) = true → P.isPrefixOf X = true
  | [], _, _, _ => rfl
  | _ :: _, [], _, h => by simp at h
  | q :: P', x :: X', hP, h => by
    simp only [List.map_cons, List.isPrefixOf, Bool.and_eq_true, beq_iff_eq] at h ⊢
    obtain ⟨e, h'⟩ := h
    have hfx : bcFree (bcSig Ps Pt x) := e ▸ hP q (by simp)
    have hx : x = q := by rw [e, bcSig_free (bcFree_of_sig hfx)]
    exact ⟨hx.symm, isPrefixOf_map_free P' X' (fun q' hq' => hP q' (List.mem_cons_of_mem _ hq')) h'⟩

/-- **`σ_m ∘ τ_m = id`** on the domain of `τ_m`. -/
theorem bc_sig_tau (m : ℕ) : ∀ (N : ℕ) (t : Term), t.size ≤ N → bciD S m t →
    bcSig (bcPre (m + 1)) bcPreW (bcSig bcPreW (bcPre (m + 1)) t) = t
  | 0, t, h, _ => absurd h (by have := size_pos t; omega)
  | N + 1, t, hN, hD => by
    have IH : ∀ w, bcSub w t → w.size < t.size → bcSig (bcPre (m + 1)) bcPreW
        (bcSig bcPreW (bcPre (m + 1)) w) = w := fun w hw hsz =>
      bc_sig_tau m N w (by omega) (bciD_sub hD hw)
    cases t with
    | zero => simp
    | inacc _ => simp
    | inaccW => simp
    | add a b =>
      rw [bcSig_add, bcSig_add, IH a (sub_add_l a b) (by simp only [size]; omega),
        IH b (sub_add_r a b) (by simp only [size]; omega)]
    | phi a b =>
      rw [bcSig_phi, bcSig_phi, IH a (sub_phi_l a b) (by simp only [size]; omega),
        IH b (sub_phi_r a b) (by simp only [size]; omega)]
    | om a => rw [bcSig_om, bcSig_om, IH a (sub_om a) (by simp only [size]; omega)]
    | psiI n a => rw [bcSig_psiI, bcSig_psiI, IH a (sub_psiI n a) (by simp only [size]; omega)]
    | psiS s a =>
      by_cases hs : s = zero
      · subst hs
        have haN : NF a := hD.1.2.1
        by_cases pa : bcPreW.isPrefixOf (bcSl a) = true
        · have hr := IH (bcDrop bcPreW.length a)
            (by rcases bcSub_bcDrop bcPreW.length a with h | h
                · rw [h]; exact bcSub_trans (Or.inr (by
                    show bcPSub zero (psiS zero a); exact Or.inl (Or.inl rfl))) (bcSub_refl _)
                · exact bcSub_trans h (sub_psiS_a zero a))
            (by have := bcDrop_size_le bcPreW.length a; simp only [size]; omega)
          rw [bcSig_psiS_zero, bcArg_of_pre pa, bcSig_psiS_zero,
            bcArg_of_pre (isPrefixOf_bcApp (prin_pre (m + 1)) _), bcDrop_bcApp (prin_pre (m + 1)),
            hr, ← bcApp_of_prefix prin_preW haN pa]
        · have hlt := bci_notpre_lt S m hD pa
          have hnp : ¬ (bcPre (m + 1)).isPrefixOf (bcSl (bcSig bcPreW (bcPre (m + 1)) a)) = true := by
            intro h
            rw [bcSl_bcSig] at h
            have h' := isPrefixOf_map_free _ _ (free_pre (m + 1)) h
            have := (bc_pre_iff S haN (hlt.trans (bcAlpha_lt_W S (m + 1)))).1 h'
            exact absurd hlt (not_lt.2 this)
          rw [bcSig_psiS_zero, bcArg_of_not pa, bcSig_psiS_zero, bcArg_of_not hnp,
            IH a (sub_psiS_a zero a) (by simp only [size]; omega)]
      · rw [bcSig_psiS_ne hs, bcSig_psiS_ne (bcSig_ne_zero hs),
          IH s (sub_psiS_s s a) (by simp only [size]; omega),
          IH a (sub_psiS_a s a) (by simp only [size]; omega)]

/-- The term of `L(ω+1) = ψ_{Ω₁}(α_ω + P')`. -/
def bcLtW1 : Term := psiS zero (bcApp bcPreW tPp)

theorem WW_lt_preW_Pp (S : InaccSeq.{0}) : cmp (add tW tW) (bcApp bcPreW tPp) = .lt := by
  refine cmp_lt_of_val S NF_add_tW_tW NF_preW_Pp ?_
  rw [val_preW_Pp]
  exact lt_of_lt_of_le (WW_lt_W S) le_self_add

theorem NF_bcLtW1 (S : InaccSeq.{0}) : NF bcLtW1 := by
  refine ⟨trivial, NF_preW_Pp, KLt_bcApp (fun p hp => ?_) (KLt_tPp (WW_lt_preW_Pp S))⟩
  simp only [bcPreW, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact KLt_tW _ _
  · exact KLt_tW _ _
  · exact KLt_tWp (WW_lt_preW_Pp S)

theorem val_bcLtW1 : val S bcLtW1 = Nc.ncL S (Ordinal.omega0 + 1) := by
  unfold bcLtW1
  rw [val_psiS_zero, val_preW_Pp, Nc.ncL_succ_omega]; rfl

theorem bciD_bcLtW1 (m : ℕ) : bciD S m bcLtW1 := by
  refine ⟨NF_bcLtW1 S, trivial, bciArgs_bcApp S m (fun p hp => ?_) (bciArgs_tPp S m), fun _ => ?_,
    fun h => absurd rfl h⟩
  · simp only [bcPreW, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact bciArgs_tW S m
    · exact bciArgs_tW S m
    · exact bciArgs_tWp S m
  · right
    rw [val_preW_Pp]
    refine ⟨le_self_add, ?_⟩
    unfold bcAlphaWW
    refine (add_lt_add_iff_left _).2 ?_
    have := (cmp_lt_iff S NF_tPp NF_tWp).1 cmp_tPp_tWp
    rwa [val_tPp, val_tWp] at this

theorem tau_bcLtW1 (m : ℕ) : bcSig bcPreW (bcPre (m + 1)) bcLtW1 = bcLt (m + 2) := by
  unfold bcLtW1 bcLt
  have e : bcPre (m + 2) = bcPre (m + 1) ++ [tPp] := by
    simp [bcPre, List.replicate_succ']
  rw [bcSig_psiS_zero, bcArg_of_pre (isPrefixOf_bcApp prin_preW tPp), bcDrop_bcApp prin_preW,
    bcSig_free bcFree_tPp, e, bcApp_snoc (by simp [tPp])]

theorem Om1_lt_Wp : Om 1 < Ordinal.omega0 ^ (Nc.ncPp S + 1) := by
  have h1 : Om 1 < Nc.ncPp S := by
    have := InaccSeq.Om_lt_psiS (S := S) (Om Ordinal.omega0 + Om Ordinal.omega0) 1 (τ := 1)
    exact this.2 le_rfl
  refine h1.trans ?_
  have := (cmp_lt_iff S NF_tPp NF_tWp).1 cmp_tPp_tWp
  rwa [val_tPp, val_tWp] at this

/-- One `y ∈ [L(ω), L(ω+1))` is eventually in the image of `B_n` on `[0, L(n+2))`. -/
theorem bc_onto_one {y : Ordinal.{0}} (hy : y < Nc.ncL S (Ordinal.omega0 + 1)) :
    ∃ M : ℕ, ∀ n, M ≤ n → ∃ y' < Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}), bcB S n y' = y := by
  have hy' : y < S.psi (bcAlphaW S + Nc.ncPp S) (Om 1) := by
    rw [Nc.ncL_succ_omega] at hy; exact hy
  obtain ⟨hN, hv⟩ := bcNf_spec S (mem_of_lt_psi S hy')
  have hA : bcArgsLt S (bcAlphaWW S) (bcNf S y) := by
    refine bcArgsLt_mono S ?_ (bcArgsLt_of_lt S hN (by rw [hv]; exact hy'))
    unfold bcAlphaWW
    refine (add_le_add_iff_left _).2 ?_
    have := (cmp_lt_iff S NF_tPp NF_tWp).1 cmp_tPp_tWp
    rw [val_tPp, val_tWp] at this
    exact this.le
  have hy1 : y < Om 1 := hy.trans (InaccSeq.psi_lt (S := S) InaccSeq.InR_Om1 _)
  have hNA := bc_nargs S hN hA (by rw [hv]; exact hy1.trans (Om1_lt_Wp S))
  obtain ⟨M, hM⟩ := bci_eventually S hN hA hNA
  refine ⟨M, fun n hn => ?_⟩
  have hD : bciD S n (bcNf S y) := ⟨hN, hM n hn⟩
  set t' := bcSig bcPreW (bcPre (n + 1)) (bcNf S y) with ht'
  have ht'N : NF t' := bci_NF hD
  refine ⟨val S t', ?_, ?_⟩
  · have hc := bci_cmp' hD (bciD_bcLtW1 S n)
    rw [tau_bcLtW1, cmp_lt_of_val S hN (NF_bcLtW1 S) (by rw [hv, val_bcLtW1]; exact hy)] at hc
    have := (cmp_lt_iff S ht'N (NF_bcLt S (n + 1))).1 hc
    rwa [val_bcLt] at this
  · unfold bcB
    rw [bcNf_val S ht'N, ht', bc_sig_tau S n _ _ le_rfl hD, hv]

/-- **ONTO-FIN.** -/
theorem bcOnto : ∀ Y : Finset Ordinal.{0},
    (∀ y ∈ Y, Nc.ncL S Ordinal.omega0 ≤ y ∧ y < Nc.ncL S (Ordinal.omega0 + 1)) → ∀ N, ∃ n,
      N ≤ n ∧ ∀ y ∈ Y, ∃ y' < Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}), bcB S n y' = y := by
  classical
  intro Y hY N
  have key : ∃ M : ℕ, ∀ y ∈ Y, ∀ n, M ≤ n →
      ∃ y' < Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}), bcB S n y' = y := by
    induction Y using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert y Y _ ih =>
      obtain ⟨M1, h1⟩ := ih (fun z hz => hY z (Finset.mem_insert_of_mem hz))
      obtain ⟨M2, h2⟩ := bc_onto_one S (hY y (Finset.mem_insert_self y Y)).2
      refine ⟨max M1 M2, fun z hz n hn => ?_⟩
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact h2 n (le_of_max_le_right hn)
      · exact h1 z hz n (le_of_max_le_left hn)
  obtain ⟨M, hM⟩ := key
  exact ⟨max M N, le_max_right _ _, fun y hy => hM y hy _ (le_max_left _ _)⟩

end Onto

end Googology.Trans.PoR.InaccPsi.R2.Bc

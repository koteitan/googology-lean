import Googology.Trans.PoR.InaccPsi.R2.SfLim

/-!
# σ reflects the normal form of a prefixed collapse

`σ = bcSig (bcPre (n+1)) bcPreW`, `σ_A = bcArg (bcPre (n+1)) bcPreW` (the image of a `ψ_{Ω₁}`-argument),
`α_k = Ω_ω·2 + P'·k`, `α_ω = Ω_ω·2 + P'·ω`, `c = α_{n+1} + r` (the chain `bcApp (bcPre (n+1)) r`),
`c' = σ_A(c) = α_ω + σ(r)`.

* `sfArg_refl`: for a normal `ψ^S_0(d)` with `|d| < α_ω` (and its arguments `< α_ω`),
  `σ_A(d) < σ_A(c)` gives `d < c` (both prefixed: the prefixes cancel and `σ` keeps `cmp`; `d` not
  prefixed: `|d| < α_{n+1} ≤ |c|`);
* `sfRefl_C`, `sfRefl_B` (**the `K`-condition reflects**): for a normal `x` with `|x| < P'·ω` inside `r`,
  `K_{ψ(c')}(σ(x)) < c'` gives `K_{ψ(c)}(x) < c`.  A `ψ_{Ω₁}`-subterm `ψ(d)` is handled by `sfArg_refl`;
  `Ω_b` and `ψ^I` never lie below `ψ(c)`, and `ψ_{Ω₂}(b) ≤ P'` has `|b| ≤ Ω_ω·2 < |c|`; inside `b` the
  `K`-set of the normal `ψ_{Ω₂}(b)` bounds every argument by `|b|`, and a collapse below `ψ_{Ω₂}(b)` is
  below `P'`, so the induction goes back to the first case (as in the bound of `Bc.bc_nargs`);
* `sfRefl` (**σ reflects the normal form**): if `ψ^S_0(α_ω + σ(r))` is a normal form, `|r| < P'·ω`,
  `r` in the domain of `σ` and `α_{n+1} + r` a normal chain, then `ψ^S_0(α_{n+1} + r)` is a normal form.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Bc Googology.Trans.PoR.InaccPsi.R2.Nm

variable {S : InaccSeq.{0}}

/-! ## Comparisons with `ψ^S_0` -/

theorem sfCmp_om_psi0 (b a : Term) : cmp (om b) (psiS Term.zero a) = .gt := by
  rw [cmp_K_psiS Term.zero a (k := om b) rfl]
  simp [cardT, cmp_zero_right]

theorem sfCmp_psiI_psi0 (m : ℕ) (b a : Term) : cmp (psiI m b) (psiS Term.zero a) = .gt := by
  rw [cmp_K_psiS Term.zero a (k := psiI m b) rfl]
  simp [cardT, cmp_zero_right]

theorem sfCmp_psiS_psi0 {s : Term} (hs : s ≠ Term.zero) (b a : Term) :
    cmp (psiS s b) (psiS Term.zero a) = .gt := by
  rw [cmp_psiS_psiS, cmp_zero_right hs]; simp

theorem sfCmp_psi0_psi0 (d a : Term) :
    cmp (psiS Term.zero d) (psiS Term.zero a) = cmp d a := by
  rw [cmp_psiS_psiS, if_pos (cmp_self _)]

section Refl

variable {n : ℕ}

/-- **σ_A reflects `<`** from a normal collapse argument `d` to a prefixed chain `c`. -/
theorem sfArg_refl {d c : Term} (hd : bcD S (psiS Term.zero d)) (hc : NF c)
    (hcW : val S c < bcAlphaW S) (hcpre : (bcPre (n + 1)).isPrefixOf (bcSl c) = true)
    (hc'N : NF (bcArg (bcPre (n + 1)) bcPreW c)) (hDrc : bcD S (bcDrop (bcPre (n + 1)).length c))
    (h : cmp (bcArg (bcPre (n + 1)) bcPreW d) (bcArg (bcPre (n + 1)) bcPreW c) = .lt) :
    cmp d c = .lt := by
  have hdN : NF d := hd.1.2.1
  have hdW : val S d < bcAlphaW S := hd.2.2.2 rfl
  have hαc := (bc_pre_iff S hc hcW).1 hcpre
  by_cases pd : (bcPre (n + 1)).isPrefixOf (bcSl d) = true
  · have hDd : bcD S d := bcD_sub hd (sub_psiS_a _ _)
    have hσd : NF (bcArg (bcPre (n + 1)) bcPreW d) := by
      have := bc_NF (k := n) hd
      rw [bcSig_psiS_zero] at this
      exact this.2.1
    have hDrd : bcD S (bcDrop (bcPre (n + 1)).length d) := bcD_drop hDd _
    have hσrd := bc_NF (k := n) hDrd
    have hσrc := bc_NF (k := n) hDrc
    have ed := bcApp_of_prefix (prin_pre (n + 1)) hdN pd
    have ec := bcApp_of_prefix (prin_pre (n + 1)) hc hcpre
    have lhs : cmp (bcArg (bcPre (n + 1)) bcPreW d) (bcArg (bcPre (n + 1)) bcPreW c) =
        cmp (bcSig (bcPre (n + 1)) bcPreW (bcDrop (bcPre (n + 1)).length d))
          (bcSig (bcPre (n + 1)) bcPreW (bcDrop (bcPre (n + 1)).length c)) := by
      have h1 := hσd; have h2 := hc'N
      rw [bcArg_of_pre pd] at h1 ⊢
      rw [bcArg_of_pre hcpre] at h2 ⊢
      rw [cmp_chain h1 h2, bcSl_bcApp prin_preW, bcSl_bcApp prin_preW, bcLcmp_append_left,
        ← cmp_chain hσrd hσrc]
    have rhs : cmp d c = cmp (bcDrop (bcPre (n + 1)).length d) (bcDrop (bcPre (n + 1)).length c) := by
      rw [cmp_chain hdN hc]
      have sd : bcSl d = bcPre (n + 1) ++ bcSl (bcDrop (bcPre (n + 1)).length d) := by
        conv_lhs => rw [ed]
        exact bcSl_bcApp (prin_pre (n + 1)) _
      have sc : bcSl c = bcPre (n + 1) ++ bcSl (bcDrop (bcPre (n + 1)).length c) := by
        conv_lhs => rw [ec]
        exact bcSl_bcApp (prin_pre (n + 1)) _
      rw [sd, sc, bcLcmp_append_left, ← cmp_chain hDrd.1 hDrc.1]
    rw [rhs, ← bc_cmp' (k := n) hDrd hDrc, ← lhs, h]
  · have h1 : val S d < bcAlpha S (n + 1) := by
      by_contra hh; exact pd ((bc_pre_iff S hdN hdW).2 (not_lt.1 hh))
    exact cmp_lt_of_val S hdN hc (lt_of_lt_of_le h1 hαc)

/-- The data of a prefixed chain `c` for the reflection. -/
structure SfCtx (S : InaccSeq.{0}) (n : ℕ) (c : Term) : Prop where
  nf : NF c
  ltW : val S c < bcAlphaW S
  pre : (bcPre (n + 1)).isPrefixOf (bcSl c) = true
  nfA : NF (bcArg (bcPre (n + 1)) bcPreW c)
  dr : bcD S (bcDrop (bcPre (n + 1)).length c)

theorem SfCtx.WW_lt {c : Term} (H : SfCtx S n c) : val S (add tW tW) < val S c :=
  lt_of_lt_of_le (WW_lt_alpha S n) ((bc_pre_iff S H.nf H.ltW).1 H.pre)

/-- The `ψ_{Ω₁}`-subterm case. -/
theorem sfRefl_psi0 {c d : Term} (H : SfCtx S n c) (hd : bcD S (psiS Term.zero d))
    (hT : KLt (psiS Term.zero (bcArg (bcPre (n + 1)) bcPreW c))
      (bcSig (bcPre (n + 1)) bcPreW (psiS Term.zero d)) (bcArg (bcPre (n + 1)) bcPreW c)) :
    KLt (psiS Term.zero c) (psiS Term.zero d) c := by
  rw [bcSig_psiS_zero] at hT
  have h : cmp (bcArg (bcPre (n + 1)) bcPreW d) (bcArg (bcPre (n + 1)) bcPreW c) = .lt := by
    rcases hT with hT | ⟨hT, -⟩
    · rwa [sfCmp_psi0_psi0] at hT
    · exact hT
  left
  rw [sfCmp_psi0_psi0]
  exact sfArg_refl hd H.nf H.ltW H.pre H.nfA H.dr h

/-- (B): inside `ψ_{Ω₂}(e)` with `e ≤ Ω_ω·2`, given the main case for the smaller terms. -/
theorem sfRefl_B {c : Term} (H : SfCtx S n c) {N : ℕ}
    (ih : ∀ x : Term, x.size ≤ N → NF x → bcD S x → val S x < ω ^ (Nc.ncPp S + 1) →
      KLt (psiS Term.zero (bcArg (bcPre (n + 1)) bcPreW c)) (bcSig (bcPre (n + 1)) bcPreW x)
        (bcArg (bcPre (n + 1)) bcPreW c) → KLt (psiS Term.zero c) x c)
    {e : Term} (hμ : NF (psiS tOne e)) (hμD : bcD S (psiS tOne e))
    (he : val S e ≤ val S (add tW tW)) (hsz : (psiS tOne e).size ≤ N + 1) :
    ∀ (M : ℕ) (y : Term), y.size ≤ M → bcSub y e → KLt (psiS tOne e) y e →
      KLt (psiS Term.zero (bcArg (bcPre (n + 1)) bcPreW c)) (bcSig (bcPre (n + 1)) bcPreW y)
        (bcArg (bcPre (n + 1)) bcPreW c) → KLt (psiS Term.zero c) y c := by
  have hμP : val S (psiS tOne e) ≤ Nc.ncPp S := by
    have := (InaccSeq.psi_mono (S := S) (InaccSeq.InR_Om_succ 1) he).1
    simp only [val, val_tOne]
    rw [show Nc.ncPp S = S.psi (val S (add tW tW)) (Om (1 + 1)) by rw [val_WW]; rfl]
    exact this
  have hPW : Nc.ncPp S < ω ^ (Nc.ncPp S + 1) := by
    have := (cmp_lt_iff S NF_tPp NF_tWp).1 cmp_tPp_tWp; rwa [val_tPp, val_tWp] at this
  have heN : NF e := hμ.2.1
  have heD : bcD S e := bcD_sub hμD (sub_psiS_a _ _)
  have hsub_size : ∀ {x}, bcSub x e → x.size ≤ N := fun hx => by
    have := bcSub_size hx; simp only [size] at hsz; omega
  have hec : ∀ {b : Term}, NF b → cmp b e = .lt → cmp b c = .lt := fun hb h =>
    cmp_lt_of_val S hb H.nf (lt_of_lt_of_le ((cmp_lt_iff S hb heN).1 h) (he.trans H.WW_lt.le))
  intro M
  induction M with
  | zero => intro y hy; exact absurd hy (by have := size_pos y; omega)
  | succ M ihM =>
    intro y hy hye hK hT
    have hyN : NF y := NF_of_sub hye heN
    have hyD : bcD S y := bcD_sub heD hye
    have hC : cmp y (psiS tOne e) = .lt → KLt (psiS Term.zero c) y c := fun h =>
      ih y (hsub_size hye) hyN hyD
        (lt_of_lt_of_le ((cmp_lt_iff S hyN hμ).1 h) (hμP.trans hPW.le)) hT
    cases y with
    | zero => trivial
    | inacc _ => trivial
    | inaccW => trivial
    | add a b =>
      simp only [size] at hy
      rw [bcSig_add] at hT
      exact ⟨ihM a (by omega) (bcSub_trans (sub_add_l a b) hye) hK.1 hT.1,
        ihM b (by omega) (bcSub_trans (sub_add_r a b) hye) hK.2 hT.2⟩
    | phi a b =>
      simp only [size] at hy
      rw [bcSig_phi] at hT
      exact ⟨ihM a (by omega) (bcSub_trans (sub_phi_l a b) hye) hK.1 hT.1,
        ihM b (by omega) (bcSub_trans (sub_phi_r a b) hye) hK.2 hT.2⟩
    | om b =>
      simp only [size] at hy
      rcases hK with hK | hK
      · exact hC hK
      · have hT' := hT
        rw [bcSig_om] at hT'
        rcases hT' with hT' | hT'
        · rw [sfCmp_om_psi0] at hT'; exact absurd hT' (by simp)
        · exact Or.inr (ihM b (by omega) (bcSub_trans (sub_om b) hye) hK hT')
    | psiI m b =>
      simp only [size] at hy
      rcases hK with hK | ⟨hb, hKb⟩
      · exact hC hK
      · have hT' := hT
        rw [bcSig_psiI] at hT'
        rcases hT' with hT' | ⟨-, hT'⟩
        · rw [sfCmp_psiI_psi0] at hT'; exact absurd hT' (by simp)
        · have hbN : NF b := hyN.1
          exact Or.inr ⟨hec hbN hb,
            ihM b (by omega) (bcSub_trans (sub_psiI m b) hye) hKb hT'⟩
    | psiS s b =>
      simp only [size] at hy
      by_cases hs0 : s = Term.zero
      · subst hs0
        exact sfRefl_psi0 H hyD hT
      rcases hK with hK | ⟨hb, hKs, hKb⟩
      · exact hC hK
      · have hT' := hT
        rw [bcSig_psiS_ne hs0] at hT'
        rcases hT' with hT' | ⟨-, hTs, hTb⟩
        · rw [sfCmp_psiS_psi0 (bcSig_ne_zero hs0)] at hT'; exact absurd hT' (by simp)
        · exact Or.inr ⟨hec hyN.2.1 hb,
            ihM s (by omega) (bcSub_trans (sub_psiS_s s b) hye) hKs hTs,
            ihM b (by omega) (bcSub_trans (sub_psiS_a s b) hye) hKb hTb⟩

/-- (C): **the `K`-condition reflects** for normal terms below `P'·ω`. -/
theorem sfRefl_C {c : Term} (H : SfCtx S n c) : ∀ (N : ℕ) (x : Term), x.size ≤ N → NF x →
    bcD S x → val S x < ω ^ (Nc.ncPp S + 1) →
    KLt (psiS Term.zero (bcArg (bcPre (n + 1)) bcPreW c)) (bcSig (bcPre (n + 1)) bcPreW x)
      (bcArg (bcPre (n + 1)) bcPreW c) → KLt (psiS Term.zero c) x c
  | 0, x, hx, _, _, _, _ => absurd hx (by have := size_pos x; omega)
  | N + 1, x, hx, hxN, hxD, hv, hT => by
    have ih := sfRefl_C H N
    cases x with
    | zero => trivial
    | inacc _ => trivial
    | inaccW => trivial
    | add a b =>
      simp only [size] at hx
      rw [bcSig_add] at hT
      exact ⟨ih a (by omega) hxN.1 (bcD_sub hxD (sub_add_l a b))
          (lt_of_le_of_lt le_self_add hv) hT.1,
        ih b (by omega) hxN.2.1 (bcD_sub hxD (sub_add_r a b)) (lt_of_le_of_lt le_add_self hv) hT.2⟩
    | phi a b =>
      simp only [size] at hx
      rw [bcSig_phi] at hT
      exact ⟨ih a (by omega) hxN.1 (bcD_sub hxD (sub_phi_l a b))
          (((cmp_lt_iff S hxN.1 hxN).1 hxN.2.2.1).trans hv) hT.1,
        ih b (by omega) hxN.2.1 (bcD_sub hxD (sub_phi_r a b))
          (((cmp_lt_iff S hxN.2.1 hxN).1 hxN.2.2.2).trans hv) hT.2⟩
    | om b =>
      simp only [size] at hx
      rw [bcSig_om] at hT
      rcases hT with hT | hT
      · rw [sfCmp_om_psi0] at hT; exact absurd hT (by simp)
      · exact Or.inr (ih b (by omega) hxN.1 (bcD_sub hxD (sub_om b))
          (lt_of_le_of_lt (le_Om _) hv) hT)
    | psiI m b =>
      exact absurd (lt_of_lt_of_le (hv.trans (Wp_lt_Om2 S)) (Om_two_le_psiI S m b)) (lt_irrefl _)
    | psiS s b =>
      by_cases hs0 : s = Term.zero
      · subst hs0
        exact sfRefl_psi0 H hxD hT
      have hs1 := sub_eq_one S hxN.1 hs0 (hv.trans (Wp_lt_Om2 S))
      subst hs1
      have hle := prin_le_Pp S hxN rfl hv
      have hb := arg_le_of_le_Pp S hle
      have hT' := hT
      rw [bcSig_psiS_ne hs0] at hT'
      rcases hT' with hT' | ⟨-, -, hTb⟩
      · rw [sfCmp_psiS_psi0 (bcSig_ne_zero hs0)] at hT'; exact absurd hT' (by simp)
      refine Or.inr ⟨cmp_lt_of_val S hxN.2.1 H.nf (lt_of_le_of_lt hb H.WW_lt), KLt_tOne _ _, ?_⟩
      exact sfRefl_B H ih hxN hxD hb hx b.size b le_rfl (bcSub_refl b) hxN.2.2 hTb

/-- **σ reflects the normal form of a prefixed collapse.** -/
theorem sfRefl {r : Term} (hr : bcD S r) (hrv : val S r < ω ^ (Nc.ncPp S + 1))
    (hcN : NF (bcApp (bcPre (n + 1)) r))
    (hc' : NF (psiS Term.zero (bcApp bcPreW (bcSig (bcPre (n + 1)) bcPreW r)))) :
    NF (psiS Term.zero (bcApp (bcPre (n + 1)) r)) := by
  have hcpre := isPrefixOf_bcApp (prin_pre (n + 1)) r
  have hdrop : bcDrop (bcPre (n + 1)).length (bcApp (bcPre (n + 1)) r) = r :=
    bcDrop_bcApp (prin_pre (n + 1)) r
  have hA : bcArg (bcPre (n + 1)) bcPreW (bcApp (bcPre (n + 1)) r) =
      bcApp bcPreW (bcSig (bcPre (n + 1)) bcPreW r) := by
    rw [bcArg_of_pre hcpre, hdrop]
  have hcv : val S (bcApp (bcPre (n + 1)) r) = bcAlpha S (n + 1) + val S r := by
    have := val_of_pre S hcN hcpre
    rwa [hdrop] at this
  have hcW : val S (bcApp (bcPre (n + 1)) r) < bcAlphaW S := by
    rw [hcv]
    unfold bcAlpha bcAlphaW
    rw [add_assoc]
    refine (add_lt_add_iff_left _).2 ?_
    have hP : Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) < ω ^ (Nc.ncPp S + 1) := by
      rw [← Lw.lw_Pp_opow S]
      conv_rhs => rw [Lw.lw_Pp_opow S]
      exact Ordinal.omega0_opow_mul_nat_lt (Order.lt_add_one_iff.2 le_rfl) _
    exact isPrincipal_add_omega0_opow _ hP hrv
  have H : SfCtx S n (bcApp (bcPre (n + 1)) r) :=
    ⟨hcN, hcW, hcpre, by rw [hA]; exact hc'.2.1, by rw [hdrop]; exact hr⟩
  refine ⟨trivial, hcN, KLt_bcApp (fun p hp => ?_) ?_⟩
  · simp only [bcPre, List.mem_cons, List.mem_replicate] at hp
    rcases hp with rfl | rfl | ⟨-, rfl⟩
    · exact KLt_tW _ _
    · exact KLt_tW _ _
    · exact KLt_tPp (cmp_lt_of_val S NF_add_tW_tW hcN H.WW_lt)
  · have hK := hc'.2.2
    have hK' := KLt_bcDrop bcPreW.length hK
    rw [bcDrop_bcApp prin_preW, ← hA] at hK'
    exact sfRefl_C H r.size r le_rfl hr.1 hr hrv hK'

end Refl

end Googology.Trans.PoR.InaccPsi.R2.Sf

import Googology.Trans.PoR.InaccPsi.R2.BcIDom

/-!
# The inverse base change keeps the comparison

`τ = bcSig bcPreW (bcPre (m+1))`, `τ_A = bcArg bcPreW (bcPre (m+1))`.

* `bci_arg_cmp` (two `ψ_{Ω₁}`-arguments): common prefixes `α_ω` cancel; an argument that is not
  prefixed is `< α_{m+1}`, and so is its image (`bci_img_lt`), while a prefixed one goes to
  `α_{m+1} + τ(ρ) ≥ α_{m+1}`;
* `bci_cmp` (**τ keeps `cmp`** on the `bciD`-terms with `bciG`), by the general induction
  `gen_cmp`.

No axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Bc

open Googology.Notation.InaccPsi Googology.Notation.InaccPsi.Term

section ICmp

variable (S : InaccSeq.{0}) (m : ℕ)

theorem val_tauA_ge {a : Term} (pa : bcPreW.isPrefixOf (bcSl a) = true) :
    bcAlpha S (m + 1) ≤ val S (bcArg bcPreW (bcPre (m + 1)) a) := by
  rw [bcArg_of_pre pa, val_bcApp, ← val_pre S (m + 1), val_bcApp]
  simp only [val, add_zero]
  exact le_self_add

theorem bci_arg_bound {a : Term} (ha : bciD S m (psiS zero a)) :
    val S a < bcAlpha S (m + 1) ∨ (bcAlphaW S ≤ val S a ∧ val S a < bcAlphaWW S) :=
  ha.2.2.2.1 rfl

theorem bci_arg_lt {a : Term} (ha : bciD S m (psiS zero a)) :
    val S a < bcAlphaWW S := by
  rcases bci_arg_bound S m ha with h | h
  · exact lt_of_lt_of_le (h.trans (bcAlpha_lt_W S (m + 1))) le_self_add
  · exact h.2

theorem bci_notpre_lt {a : Term} (ha : bciD S m (psiS zero a))
    (pa : ¬ bcPreW.isPrefixOf (bcSl a) = true) : val S a < bcAlpha S (m + 1) := by
  rcases bci_arg_bound S m ha with h | h
  · exact h
  · exact absurd ((bci_pre_iff S ha.1.2.1 h.2).2 h.1) pa

/-- **Two `ψ_{Ω₁}`-arguments under `τ`.** -/
theorem bci_arg_cmp {a b : Term} (ha : bciD S m (psiS zero a)) (hb : bciD S m (psiS zero b))
    (ga : bciG m (psiS zero a)) (gb : bciG m (psiS zero b))
    (hrr : bcPreW.isPrefixOf (bcSl a) = true → bcPreW.isPrefixOf (bcSl b) = true →
      cmp (bcSig bcPreW (bcPre (m + 1)) (bcDrop bcPreW.length a))
        (bcSig bcPreW (bcPre (m + 1)) (bcDrop bcPreW.length b)) =
      cmp (bcDrop bcPreW.length a) (bcDrop bcPreW.length b))
    (hxa : bcPreW.isPrefixOf (bcSl b) = true → ∀ x ∈ bcSl a,
      cmp (bcSig bcPreW (bcPre (m + 1)) x) tW = cmp x tW ∧
        cmp (bcSig bcPreW (bcPre (m + 1)) x) tPp = cmp x tPp)
    (hxb : bcPreW.isPrefixOf (bcSl a) = true → ∀ x ∈ bcSl b,
      cmp (bcSig bcPreW (bcPre (m + 1)) x) tW = cmp x tW ∧
        cmp (bcSig bcPreW (bcPre (m + 1)) x) tPp = cmp x tPp)
    (hab : ¬ bcPreW.isPrefixOf (bcSl a) = true → ¬ bcPreW.isPrefixOf (bcSl b) = true →
      cmp (bcSig bcPreW (bcPre (m + 1)) a) (bcSig bcPreW (bcPre (m + 1)) b) = cmp a b) :
    cmp (bcArg bcPreW (bcPre (m + 1)) a) (bcArg bcPreW (bcPre (m + 1)) b) = cmp a b := by
  have haN : NF a := ha.1.2.1
  have hbN : NF b := hb.1.2.1
  have hAa : NF (bcArg bcPreW (bcPre (m + 1)) a) := ga.2 a rfl
  have hAb : NF (bcArg bcPreW (bcPre (m + 1)) b) := gb.2 b rfl
  have hσa : NF (bcSig bcPreW (bcPre (m + 1)) a) := ga.1 a (Or.inr (Or.inl rfl))
  have hσb : NF (bcSig bcPreW (bcPre (m + 1)) b) := gb.1 b (Or.inr (Or.inl rfl))
  have hαW : bcAlpha S (m + 1) < bcAlphaW S := bcAlpha_lt_W S (m + 1)
  by_cases pa : bcPreW.isPrefixOf (bcSl a) = true <;>
    by_cases pb : bcPreW.isPrefixOf (bcSl b) = true
  · have ea := bcApp_of_prefix prin_preW haN pa
    have eb := bcApp_of_prefix prin_preW hbN pb
    set ra := bcDrop bcPreW.length a with hra
    set rb := bcDrop bcPreW.length b with hrb
    have hra' : NF ra := NF_bcDrop _ haN
    have hrb' : NF rb := NF_bcDrop _ hbN
    have hσra : NF (bcSig bcPreW (bcPre (m + 1)) ra) := by
      rcases bcPSub_bcDrop_succ 2 a with h | h
      · rw [hra, show bcPreW.length = 2 + 1 from rfl, h, bcSig_zero]; trivial
      · rw [hra, show bcPreW.length = 2 + 1 from rfl]; exact ga.1 _ (Or.inr (Or.inr h))
    have hσrb : NF (bcSig bcPreW (bcPre (m + 1)) rb) := by
      rcases bcPSub_bcDrop_succ 2 b with h | h
      · rw [hrb, show bcPreW.length = 2 + 1 from rfl, h, bcSig_zero]; trivial
      · rw [hrb, show bcPreW.length = 2 + 1 from rfl]; exact gb.1 _ (Or.inr (Or.inr h))
    have lhs : cmp (bcArg bcPreW (bcPre (m + 1)) a) (bcArg bcPreW (bcPre (m + 1)) b) =
        cmp (bcSig bcPreW (bcPre (m + 1)) ra) (bcSig bcPreW (bcPre (m + 1)) rb) := by
      have h1 := hAa; have h2 := hAb
      rw [bcArg_of_pre pa] at h1 ⊢
      rw [bcArg_of_pre pb] at h2 ⊢
      rw [cmp_chain h1 h2, bcSl_bcApp (prin_pre (m + 1)), bcSl_bcApp (prin_pre (m + 1)),
        bcLcmp_append_left, ← cmp_chain hσra hσrb]
    have rhs : cmp a b = cmp ra rb := by
      rw [cmp_chain haN hbN]
      have sa : bcSl a = bcPreW ++ bcSl ra := by
        conv_lhs => rw [ea]
        exact bcSl_bcApp prin_preW _
      have sb : bcSl b = bcPreW ++ bcSl rb := by
        conv_lhs => rw [eb]
        exact bcSl_bcApp prin_preW _
      rw [sa, sb, bcLcmp_append_left, ← cmp_chain hra' hrb']
    rw [lhs, rhs]; exact hrr pa pb
  · have hb1 := bci_notpre_lt S m hb pb
    have hb2 := bci_img_lt S m hbN hσb hb1 (hxb pa)
    have hva := (bci_pre_iff S haN (bci_arg_lt S m ha)).1 pa
    rw [bcArg_of_not pb, cmp_gt_of_val S haN hbN (lt_of_lt_of_le (hb1.trans hαW) hva)]
    rw [bcArg_of_not pb] at hAb
    exact cmp_gt_of_val S hAa hAb (lt_of_lt_of_le hb2 (val_tauA_ge S m pa))
  · have ha1 := bci_notpre_lt S m ha pa
    have ha2 := bci_img_lt S m haN hσa ha1 (hxa pb)
    have hvb := (bci_pre_iff S hbN (bci_arg_lt S m hb)).1 pb
    rw [bcArg_of_not pa, cmp_lt_of_val S haN hbN (lt_of_lt_of_le (ha1.trans hαW) hvb)]
    rw [bcArg_of_not pa] at hAa
    exact cmp_lt_of_val S hAa hAb (lt_of_lt_of_le ha2 (val_tauA_ge S m pb))
  · rw [bcArg_of_not pa, bcArg_of_not pb]; exact hab pa pb

theorem sub_tW_of_pre {a : Term} (pa : bcPreW.isPrefixOf (bcSl a) = true) (ha : NF a) :
    bcSub tW a ∧ bcSub tPp a := by
  have e := bcApp_of_prefix prin_preW ha pa
  have hsl : bcSl a = bcPreW ++ bcSl (bcDrop bcPreW.length a) := by
    conv_lhs => rw [e]
    exact bcSl_bcApp prin_preW _
  have h1 : tW ∈ bcSl a := by rw [hsl]; simp [bcPreW]
  have h2 : tWp ∈ bcSl a := by rw [hsl]; simp [bcPreW]
  refine ⟨mem_bcSl_sub h1, ?_⟩
  have : bcPSub tPp tWp := Or.inr (Or.inr (Or.inl (Or.inl rfl)))
  exact Or.inr (bcPSub_of_sub_psub (Or.inl rfl) (bcPSub_trans a this (mem_bcSl_sub h2)))

theorem bciG_tW : bciG m tW := bciG_free NF_tW bcFree_tW
theorem bciG_tPp : bciG m tPp := bciG_free NF_tPp bcFree_tPp

/-- Two `ψ_{Ω₁}`-arguments, from the smaller pairs. -/
theorem bci_argOK : ArgOK (bciX S m) := by
  intro N ih a1 a2 hN hs ht gs gt
  have da1 := bciD_sub hs (sub_psiS_a zero a1)
  have da2 := bciD_sub ht (sub_psiS_a zero a2)
  have ga1 := bciG_sub gs (sub_psiS_a zero a1)
  have ga2 := bciG_sub gt (sub_psiS_a zero a2)
  have hN' := hN
  simp only [size] at hN'
  have hWs : tW.size ≤ tPp.size := by
    show tW.size ≤ (psiS tOne (add tW tW)).size; simp only [size]; omega
  refine bci_arg_cmp S m hs ht gs gt (fun _ _ => ?_) (fun pb x hx => ?_) (fun pa x hx => ?_)
    (fun _ _ => ih a1 a2 (by omega) da1 da2 ga1 ga2)
  · exact ih _ _ (by have := bcDrop_size_le bcPreW.length a1
                     have := bcDrop_size_le bcPreW.length a2; omega)
      (bciD_drop da1 _) (bciD_drop da2 _) (bciG_drop ga1 _) (bciG_drop ga2 _)
  · have hxs := mem_bcSl_sub hx
    have hsz1 := bcSub_size hxs
    have hsz2 := bcSub_size (sub_tW_of_pre pb da2.1).2
    have e1 := ih x tW (by omega) (bciD_sub da1 hxs) (bciD_tW S m) (bciG_sub ga1 hxs) (bciG_tW m)
    have e2 := ih x tPp (by omega) (bciD_sub da1 hxs) (bciD_tPp S m) (bciG_sub ga1 hxs) (bciG_tPp m)
    rw [bcSig_free bcFree_tW] at e1
    rw [bcSig_free bcFree_tPp] at e2
    exact ⟨e1, e2⟩
  · have hxs := mem_bcSl_sub hx
    have hsz1 := bcSub_size hxs
    have hsz2 := bcSub_size (sub_tW_of_pre pa da1.1).2
    have e1 := ih x tW (by omega) (bciD_sub da2 hxs) (bciD_tW S m) (bciG_sub ga2 hxs) (bciG_tW m)
    have e2 := ih x tPp (by omega) (bciD_sub da2 hxs) (bciD_tPp S m) (bciG_sub ga2 hxs) (bciG_tPp m)
    rw [bcSig_free bcFree_tW] at e1
    rw [bcSig_free bcFree_tPp] at e2
    exact ⟨e1, e2⟩

/-- **The inverse base change keeps `cmp`** on its domain. -/
theorem bci_cmp {s t : Term} (hs : bciD S m s) (ht : bciD S m t) (gs : bciG m s)
    (gt : bciG m t) :
    cmp (bcSig bcPreW (bcPre (m + 1)) s) (bcSig bcPreW (bcPre (m + 1)) t) = cmp s t :=
  gen_cmp (bciX S m) (bci_argOK S m) hs ht gs gt

end ICmp

end Googology.Trans.PoR.InaccPsi.R2.Bc

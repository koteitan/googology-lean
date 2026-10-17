import Googology.Trans.PoR.InaccPsi.R2.BcDom
import Googology.Trans.PoR.InaccPsi.R2.BcGen

/-!
# The base change keeps the comparison

Fix `k`; the base is `bcPre (k+1)` (`α_{k+1} = Ω_ω·2 + P'·(k+1)`), the target `bcPreW` (`α_ω`), and
`σ = bcSig (bcPre (k+1)) bcPreW`, `σ_A = bcArg (bcPre (k+1)) bcPreW`.

* `bcD S t`: `t` is a normal form whose `ψ_{Ω₁}`-arguments are all `< α_ω`;
* `bcG k t`: the images of the proper subterms of `t` are normal forms (and, for `t = ψ^S_0(a)`,
  so is `σ_A(a)`) — the induction hypothesis of the next module;
* `bc_cmp` (**σ keeps `cmp`**): for `bcD`-terms `s, t` with `bcG k s`, `bcG k t`,
  `cmp (σ s) (σ t) = cmp s t`, by the general induction `gen_cmp` (`BcGen`); the clauses commute
  with `σ` except the comparison of two `ψ_{Ω₁}`-arguments, where a prefixed
  argument `α_{k+1} + ρ` goes to `α_ω + σ(ρ)` (`bc_arg_cmp`: common prefixes cancel; an argument
  that is not prefixed is `< α_{k+1}`, and so is its image).

No axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Bc

open Googology.Notation.InaccPsi Googology.Notation.InaccPsi.Term

/-- The domain: normal forms with all `ψ_{Ω₁}`-arguments `< α_ω`. -/
def bcD (S : InaccSeq.{0}) (t : Term) : Prop := NF t ∧ bcArgsLt S (bcAlphaW S) t

/-- The images of the proper subterms are normal forms. -/
def bcG (k : ℕ) (t : Term) : Prop :=
  (∀ z, bcPSub z t → NF (bcSig (bcPre (k + 1)) bcPreW z)) ∧
    (∀ a, t = psiS zero a → NF (bcArg (bcPre (k + 1)) bcPreW a))

section Basic

variable {S : InaccSeq.{0}} {k : ℕ}

theorem bcArgsLt_of_free {A : Ordinal.{0}} {t : Term} (h : bcFree t) : bcArgsLt S A t := by
  induction t with
  | zero => trivial
  | inacc _ => trivial
  | inaccW => trivial
  | add a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | phi a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | om a iha => exact iha h
  | psiS s a ihs iha => exact ⟨ihs h.2.1, iha h.2.2, fun hs => absurd hs h.1⟩
  | psiI _ a iha => exact iha h

theorem bcD_sub {x t : Term} (h : bcD S t) (hs : bcSub x t) : bcD S x :=
  ⟨NF_of_sub hs h.1, bcArgsLt_of_sub S hs h.2⟩

theorem bcD_free {c : Term} (h : NF c) (hf : bcFree c) : bcD S c := ⟨h, bcArgsLt_of_free hf⟩

theorem bcG_sub {x t : Term} (h : bcG k t) (hs : bcSub x t) : bcG k x := by
  rcases hs with rfl | hs
  · exact h
  refine ⟨fun z hz => h.1 z (bcPSub_trans t hz (Or.inr hs)), fun a ha => ?_⟩
  subst ha
  have := h.1 _ hs
  rw [bcSig_psiS_zero] at this
  exact this.2.1

theorem bcG_free {c : Term} (h : NF c) (hf : bcFree c) : bcG k c := by
  refine ⟨fun z hz => ?_, fun a ha => ?_⟩
  · have hfz := bcFree_of_sub (Or.inr hz) hf
    rw [bcSig_free hfz]; exact NF_of_sub (Or.inr hz) h
  · subst ha; exact absurd rfl hf.1

theorem bcG_zero : bcG k zero := ⟨fun _ h => h.elim, fun _ h => by cases h⟩
theorem bcD_zero : bcD S zero := ⟨trivial, trivial⟩

theorem bcD_cardT {s a : Term} (h : bcD S (psiS s a)) : bcD S (cardT s) := by
  unfold cardT
  split_ifs
  · exact bcD_zero
  · exact bcD_sub h (Or.inr (Or.inl (Or.inl rfl)))
  · have hs := bcD_sub h (Or.inr (Or.inl (Or.inl rfl)))
    refine ⟨⟨hs.1, by assumption, by simpa using (by assumption : ¬ s.isF = true)⟩, hs.2⟩

theorem bcG_cardT {s a : Term} (h : bcG k (psiS s a)) : bcG k (cardT s) := by
  unfold cardT
  split_ifs
  · exact bcG_zero
  · exact bcG_sub h (Or.inr (Or.inl (Or.inl rfl)))
  · refine ⟨fun z hz => ?_, fun a' ha' => by cases ha'⟩
    rcases hz with rfl | hz
    · exact h.1 z (Or.inl (Or.inl rfl))
    · exact h.1 z (Or.inl (Or.inr hz))

theorem NF_free_pre (j : ℕ) : bcFree (bcApp (bcPre j) zero) := by
  refine bcFree_bcApp (fun p hp => ?_) trivial
  simp only [bcPre, List.mem_cons, List.mem_replicate] at hp
  rcases hp with rfl | rfl | ⟨-, rfl⟩
  · exact bcFree_tW
  · exact bcFree_tW
  · exact bcFree_tPp

theorem size_bcApp_zero_le : ∀ (P : List Term) (r : Term), (bcApp P zero).size ≤ (bcApp P r).size
  | [], r => by simp only [bcApp, size]; exact size_pos r
  | [x], r => by
    rw [bcApp_single, bcApp_single, if_pos rfl]; split_ifs
    · exact le_rfl
    · simp only [size]; omega
  | x :: y :: ys, r => by
    rw [bcApp_cons_cons, bcApp_cons_cons]
    have := size_bcApp_zero_le (y :: ys) r
    simp only [size]; omega

end Basic

section Cmp

variable (S : InaccSeq.{0}) (k : ℕ)

theorem cmp_gt_of_val {x y : Term} (hx : NF x) (hy : NF y) (h : val S y < val S x) :
    cmp x y = .gt := by
  rw [cmp_eq_compare S hx hy]; exact compare_gt_iff_gt.2 h

theorem cmp_lt_of_val {x y : Term} (hx : NF x) (hy : NF y) (h : val S x < val S y) :
    cmp x y = .lt := (cmp_lt_iff S hx hy).2 h

theorem NF_sig_drop {a : Term} (ga : bcG k (psiS zero a)) :
    NF (bcSig (bcPre (k + 1)) bcPreW (bcDrop (bcPre (k + 1)).length a)) := by
  rcases bcPSub_bcDrop_succ (k + 2) a with h | h
  · rw [show (bcPre (k + 1)).length = k + 3 by simp [bcPre], h, bcSig_zero]; trivial
  · rw [show (bcPre (k + 1)).length = k + 3 by simp [bcPre]]
    exact ga.1 _ (Or.inr (Or.inr h))

/-- **Two `ψ_{Ω₁}`-arguments.** -/
theorem bc_arg_cmp {a b : Term} (ha : bcD S (psiS zero a)) (hb : bcD S (psiS zero b))
    (ga : bcG k (psiS zero a)) (gb : bcG k (psiS zero b))
    (hrr : (bcPre (k + 1)).isPrefixOf (bcSl a) = true → (bcPre (k + 1)).isPrefixOf (bcSl b) = true →
      cmp (bcSig (bcPre (k + 1)) bcPreW (bcDrop (bcPre (k + 1)).length a))
        (bcSig (bcPre (k + 1)) bcPreW (bcDrop (bcPre (k + 1)).length b)) =
      cmp (bcDrop (bcPre (k + 1)).length a) (bcDrop (bcPre (k + 1)).length b))
    (haP : (bcPre (k + 1)).isPrefixOf (bcSl b) = true → cmp (bcSig (bcPre (k + 1)) bcPreW a) (bcSig (bcPre (k + 1)) bcPreW
      (bcApp (bcPre (k + 1)) zero)) = cmp a (bcApp (bcPre (k + 1)) zero))
    (hbP : (bcPre (k + 1)).isPrefixOf (bcSl a) = true → cmp (bcSig (bcPre (k + 1)) bcPreW b) (bcSig (bcPre (k + 1)) bcPreW
      (bcApp (bcPre (k + 1)) zero)) = cmp b (bcApp (bcPre (k + 1)) zero))
    (hab : ¬ (bcPre (k + 1)).isPrefixOf (bcSl a) = true → ¬ (bcPre (k + 1)).isPrefixOf (bcSl b) = true →
      cmp (bcSig (bcPre (k + 1)) bcPreW a) (bcSig (bcPre (k + 1)) bcPreW b) = cmp a b) :
    cmp (bcArg (bcPre (k + 1)) bcPreW a) (bcArg (bcPre (k + 1)) bcPreW b) = cmp a b := by
  set Ps := bcPre (k + 1) with hPs
  set σ := bcSig Ps bcPreW with hσ
  have haN : NF a := ha.1.2.1
  have hbN : NF b := hb.1.2.1
  have haW : val S a < bcAlphaW S := ha.2.2.2 rfl
  have hbW : val S b < bcAlphaW S := hb.2.2.2 rfl
  have hAa : NF (bcArg Ps bcPreW a) := ga.2 a rfl
  have hAb : NF (bcArg Ps bcPreW b) := gb.2 b rfl
  have hσa : NF (σ a) := ga.1 a (Or.inr (Or.inl rfl))
  have hσb : NF (σ b) := gb.1 b (Or.inr (Or.inl rfl))
  have hP0 : σ (bcApp Ps zero) = bcApp Ps zero := bcSig_free (NF_free_pre (k + 1))
  have hαW : bcAlpha S (k + 1) < bcAlphaW S := bcAlpha_lt_W S (k + 1)
  -- the image of a prefixed argument is `≥ α_ω`
  have hge : ∀ {c : Term}, Ps.isPrefixOf (bcSl c) = true →
      bcAlphaW S ≤ val S (bcArg Ps bcPreW c) := by
    intro c hc
    rw [bcArg_of_pre hc, val_bcApp_preW]; exact le_self_add
  -- the image of a non-prefixed argument is `< α_{k+1}`
  have hlt : ∀ {c : Term}, NF c → NF (σ c) → val S c < bcAlphaW S →
      ¬ Ps.isPrefixOf (bcSl c) = true →
      cmp (σ c) (σ (bcApp Ps zero)) = cmp c (bcApp Ps zero) →
      val S c < bcAlpha S (k + 1) ∧ val S (bcArg Ps bcPreW c) < bcAlpha S (k + 1) := by
    intro c hc hσc hcW hpc hcP
    have h1 : val S c < bcAlpha S (k + 1) := by
      by_contra hh; exact hpc ((bc_pre_iff S hc hcW).2 (not_lt.1 hh))
    refine ⟨h1, ?_⟩
    rw [bcArg_of_not hpc]
    have h2 : cmp c (bcApp Ps zero) = .lt := cmp_lt_of_val S hc (NF_pre (k + 1))
      (by rw [val_pre]; exact h1)
    rw [hP0, h2] at hcP
    have := (cmp_lt_iff S hσc (NF_pre (k + 1))).1 hcP
    rwa [val_pre] at this
  by_cases pa : Ps.isPrefixOf (bcSl a) = true <;> by_cases pb : Ps.isPrefixOf (bcSl b) = true
  · -- both prefixed: the common prefixes cancel
    have ea := bcApp_of_prefix (prin_pre (k + 1)) haN pa
    have eb := bcApp_of_prefix (prin_pre (k + 1)) hbN pb
    set ra := bcDrop Ps.length a with hra
    set rb := bcDrop Ps.length b with hrb
    have hra' : NF ra := NF_bcDrop _ haN
    have hrb' : NF rb := NF_bcDrop _ hbN
    have hσra : NF (σ ra) := NF_sig_drop k ga
    have hσrb : NF (σ rb) := NF_sig_drop k gb
    have lhs : cmp (bcArg Ps bcPreW a) (bcArg Ps bcPreW b) = cmp (σ ra) (σ rb) := by
      have h1 := hAa; have h2 := hAb
      rw [bcArg_of_pre pa] at h1 ⊢
      rw [bcArg_of_pre pb] at h2 ⊢
      rw [cmp_chain h1 h2, bcSl_bcApp prin_preW, bcSl_bcApp prin_preW, bcLcmp_append_left,
        ← cmp_chain hσra hσrb]
    have rhs : cmp a b = cmp ra rb := by
      rw [cmp_chain haN hbN]
      have sa : bcSl a = Ps ++ bcSl ra := by
        conv_lhs => rw [ea]
        exact bcSl_bcApp (prin_pre (k + 1)) _
      have sb : bcSl b = Ps ++ bcSl rb := by
        conv_lhs => rw [eb]
        exact bcSl_bcApp (prin_pre (k + 1)) _
      rw [sa, sb, bcLcmp_append_left, ← cmp_chain hra' hrb']
    rw [lhs, rhs]; exact hrr pa pb
  · -- `a` prefixed, `b` not
    obtain ⟨hb1, hb2⟩ := hlt hbN hσb hbW pb (hbP pa)
    have hva := (bc_pre_iff S haN haW).1 pa
    rw [cmp_gt_of_val S haN hbN (lt_of_lt_of_le hb1 hva)]
    exact cmp_gt_of_val S hAa hAb (lt_of_lt_of_le (hb2.trans hαW) (hge pa))
  · -- `b` prefixed, `a` not
    obtain ⟨ha1, ha2⟩ := hlt haN hσa haW pa (haP pb)
    have hvb := (bc_pre_iff S hbN hbW).1 pb
    rw [cmp_lt_of_val S haN hbN (lt_of_lt_of_le ha1 hvb)]
    exact cmp_lt_of_val S hAa hAb (lt_of_lt_of_le (ha2.trans hαW) (hge pb))
  · rw [bcArg_of_not pa, bcArg_of_not pb]; exact hab pa pb

end Cmp

section Step

variable {S : InaccSeq.{0}} {k : ℕ}

theorem bcD_drop {a : Term} (ha : bcD S a) (j : ℕ) : bcD S (bcDrop j a) := by
  rcases bcSub_bcDrop j a with h | h
  · rw [h]; exact bcD_zero
  · exact bcD_sub ha h

theorem bcG_drop {a : Term} (ga : bcG k a) (j : ℕ) : bcG k (bcDrop j a) := by
  rcases bcSub_bcDrop j a with h | h
  · rw [h]; exact bcG_zero
  · exact bcG_sub ga h

variable (S k)

/-- The domain of `σ`, for the general induction. -/
def bcX : GenDom (bcPre (k + 1)) bcPreW :=
  ⟨bcD S, bcG k, bcD_sub, bcG_sub, bcD_cardT, bcG_cardT⟩

/-- Two `ψ_{Ω₁}`-arguments, from the smaller pairs. -/
theorem bc_argOK : ArgOK (bcX S k) := by
  intro N ih a1 a2 hN hs ht gs gt
  have da1 := bcD_sub hs (sub_psiS_a zero a1)
  have da2 := bcD_sub ht (sub_psiS_a zero a2)
  have ga1 := bcG_sub gs (sub_psiS_a zero a1)
  have ga2 := bcG_sub gt (sub_psiS_a zero a2)
  have hN' := hN
  simp only [size] at hN'
  refine bc_arg_cmp S k hs ht gs gt (fun _ _ => ?_) (fun pb => ?_) (fun pa => ?_)
    (fun _ _ => ih a1 a2 (by omega) da1 da2 ga1 ga2)
  · exact ih _ _ (by have := bcDrop_size_le (bcPre (k + 1)).length a1
                     have := bcDrop_size_le (bcPre (k + 1)).length a2; omega)
      (bcD_drop da1 _) (bcD_drop da2 _) (bcG_drop ga1 _) (bcG_drop ga2 _)
  · have e := bcApp_of_prefix (prin_pre (k + 1)) da2.1 pb
    have hsz : (bcApp (bcPre (k + 1)) zero).size ≤ a2.size := by
      conv_rhs => rw [e]
      exact size_bcApp_zero_le _ _
    exact ih _ _ (by omega) da1 (bcD_free (NF_pre (k + 1)) (NF_free_pre (k + 1))) ga1
      (bcG_free (NF_pre (k + 1)) (NF_free_pre (k + 1)))
  · have e := bcApp_of_prefix (prin_pre (k + 1)) da1.1 pa
    have hsz : (bcApp (bcPre (k + 1)) zero).size ≤ a1.size := by
      conv_rhs => rw [e]
      exact size_bcApp_zero_le _ _
    exact ih _ _ (by omega) da2 (bcD_free (NF_pre (k + 1)) (NF_free_pre (k + 1))) ga2
      (bcG_free (NF_pre (k + 1)) (NF_free_pre (k + 1)))

/-- **The base change keeps `cmp`** on the domain. -/
theorem bc_cmp {s t : Term} (hs : bcD S s) (ht : bcD S t) (gs : bcG k s) (gt : bcG k t) :
    cmp (bcSig (bcPre (k + 1)) bcPreW s) (bcSig (bcPre (k + 1)) bcPreW t) = cmp s t :=
  gen_cmp (bcX S k) (bc_argOK S k) hs ht gs gt

end Step

end Googology.Trans.PoR.InaccPsi.R2.Bc

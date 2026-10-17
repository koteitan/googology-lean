import Googology.Trans.PoR.InaccPsi.R2.BcCmp

/-!
# The inverse base change: its domain and the prefix test for `α_ω`

`τ = bcSig bcPreW (bcPre (m+1))`, `τ_A = bcArg bcPreW (bcPre (m+1))`: the base change from `L(ω)`
back to `L(m+1)` (`α_ω + ρ ↦ α_{m+1} + τ(ρ)` at `ψ_{Ω₁}`-arguments).

* `bciArgs S m t`: every `ψ_{Ω₁}`-argument of `t` is `< α_{m+1}` or in `[α_ω, α_ω + P'·ω)`, and every
  argument of another collapse is `< α_{m+1}`; `bciD S m t`: `t` is a normal form with
  `bciArgs`; `bciG m t`: the images of the proper subterms are normal forms;
* `bci_pre_iff` (**prefix test at `α_ω`**): for a normal form `a < α_ω + P'·ω`, the summands of `a`
  begin with `[Ω_ω, Ω_ω, ω^{P'+1}]` iff `α_ω ≤ |a|`; `bci_rest_lt`: the rest is then `< P'·ω`;
* `bcSl_bcSig`, `bcLcmp_map`: summand lists of images; `bci_img_lt`: an image `τ(c)` of a
  normal form `c < α_{m+1}` is `< α_{m+1}`, as soon as `τ` keeps `cmp` between the summands of `c`
  and `Ω_ω`, `P'`.

No axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Bc

open Googology.Notation.InaccPsi Googology.Notation.InaccPsi.Term

section IDom

variable (S : InaccSeq.{0}) (m : ℕ)

/-- `α_ω + P'·ω = Ω_ω·2 + ω^{P'+1}·2`. -/
noncomputable def bcAlphaWW : Ordinal.{0} := bcAlphaW S + Ordinal.omega0 ^ (Nc.ncPp S + 1)

/-- The argument conditions of the domain of `τ`. -/
def bciArgs : Term → Prop
  | zero => True
  | inacc _ => True
  | inaccW => True
  | add a b => bciArgs a ∧ bciArgs b
  | phi a b => bciArgs a ∧ bciArgs b
  | om a => bciArgs a
  | psiS s a => bciArgs s ∧ bciArgs a ∧
      (s = zero → (val S a < bcAlpha S (m + 1) ∨
        (bcAlphaW S ≤ val S a ∧ val S a < bcAlphaWW S))) ∧
      (s ≠ zero → val S a < bcAlpha S (m + 1))
  | psiI _ a => bciArgs a ∧ val S a < bcAlpha S (m + 1)

/-- The domain of `τ`. -/
def bciD (t : Term) : Prop := NF t ∧ bciArgs S m t

/-- The images under `τ` of the proper subterms are normal forms. -/
def bciG (t : Term) : Prop :=
  (∀ z, bcPSub z t → NF (bcSig bcPreW (bcPre (m + 1)) z)) ∧
    (∀ a, t = psiS zero a → NF (bcArg bcPreW (bcPre (m + 1)) a))

variable {S m}

theorem bciArgs_of_sub {x t : Term} (hs : bcSub x t) (h : bciArgs S m t) : bciArgs S m x := by
  rcases hs with rfl | hs
  · exact h
  induction t with
  | zero => exact hs.elim
  | inacc _ => exact hs.elim
  | inaccW => exact hs.elim
  | add a b iha ihb =>
    rcases hs with (rfl | hs) | (rfl | hs)
    · exact h.1
    · exact iha h.1 hs
    · exact h.2
    · exact ihb h.2 hs
  | phi a b iha ihb =>
    rcases hs with (rfl | hs) | (rfl | hs)
    · exact h.1
    · exact iha h.1 hs
    · exact h.2
    · exact ihb h.2 hs
  | om a iha =>
    rcases hs with rfl | hs
    · exact h
    · exact iha h hs
  | psiS s a ihs iha =>
    rcases hs with (rfl | hs) | (rfl | hs)
    · exact h.1
    · exact ihs h.1 hs
    · exact h.2.1
    · exact iha h.2.1 hs
  | psiI _ a iha =>
    rcases hs with rfl | hs
    · exact h.1
    · exact iha h.1 hs

theorem bciD_sub {x t : Term} (h : bciD S m t) (hs : bcSub x t) : bciD S m x :=
  ⟨NF_of_sub hs h.1, bciArgs_of_sub hs h.2⟩

theorem bciG_sub {x t : Term} (h : bciG m t) (hs : bcSub x t) : bciG m x := by
  rcases hs with rfl | hs
  · exact h
  refine ⟨fun z hz => h.1 z (bcPSub_trans t hz (Or.inr hs)), fun a ha => ?_⟩
  subst ha
  have := h.1 _ hs
  rw [bcSig_psiS_zero] at this
  exact this.2.1

theorem bciG_free {c : Term} (h : NF c) (hf : bcFree c) : bciG m c := by
  refine ⟨fun z hz => ?_, fun a ha => ?_⟩
  · have hfz := bcFree_of_sub (Or.inr hz) hf
    rw [bcSig_free hfz]; exact NF_of_sub (Or.inr hz) h
  · subst ha; exact absurd rfl hf.1

theorem bciG_zero : bciG m zero := ⟨fun _ h => h.elim, fun _ h => by cases h⟩
theorem bciD_zero : bciD S m zero := ⟨trivial, trivial⟩

theorem bciD_cardT {s a : Term} (h : bciD S m (psiS s a)) : bciD S m (cardT s) := by
  unfold cardT
  split_ifs
  · exact bciD_zero
  · exact bciD_sub h (Or.inr (Or.inl (Or.inl rfl)))
  · have hs := bciD_sub h (Or.inr (Or.inl (Or.inl rfl)))
    refine ⟨⟨hs.1, by assumption, by simpa using (by assumption : ¬ s.isF = true)⟩, hs.2⟩

theorem bciG_cardT {s a : Term} (h : bciG m (psiS s a)) : bciG m (cardT s) := by
  unfold cardT
  split_ifs
  · exact bciG_zero
  · exact bciG_sub h (Or.inr (Or.inl (Or.inl rfl)))
  · refine ⟨fun z hz => ?_, fun a' ha' => by cases ha'⟩
    rcases hz with rfl | hz
    · exact h.1 z (Or.inl (Or.inl rfl))
    · exact h.1 z (Or.inl (Or.inr hz))

theorem bciD_drop {a : Term} (ha : bciD S m a) (j : ℕ) : bciD S m (bcDrop j a) := by
  rcases bcSub_bcDrop j a with h | h
  · rw [h]; exact bciD_zero
  · exact bciD_sub ha h

theorem bciG_drop {a : Term} (ga : bciG m a) (j : ℕ) : bciG m (bcDrop j a) := by
  rcases bcSub_bcDrop j a with h | h
  · rw [h]; exact bciG_zero
  · exact bciG_sub ga h

variable (S m)

/-- The domain of `τ`, for the general induction. -/
def bciX : GenDom bcPreW (bcPre (m + 1)) :=
  ⟨bciD S m, bciG m, bciD_sub, bciG_sub, bciD_cardT, bciG_cardT⟩

/-! ## Values of the constants -/

theorem val_WW : val S (add tW tW) = Om Ordinal.omega0 + Om Ordinal.omega0 := by
  simp only [val, val_tW]

theorem WW_lt_alpha (j : ℕ) : val S (add tW tW) < bcAlpha S (j + 1) := by
  rw [val_WW]; unfold bcAlpha
  exact lt_add_of_pos_right _ (mul_pos ((Nc.ncPp_SC S).1) (by exact_mod_cast Nat.succ_pos j))

theorem alpha_lt_alpha {i j : ℕ} (h : i < j) : bcAlpha S i < bcAlpha S j := by
  unfold bcAlpha
  exact (add_lt_add_iff_left _).2 ((mul_lt_mul_iff_right₀ ((Nc.ncPp_SC S).1)).2 (by exact_mod_cast h))

theorem bciArgs_tW : bciArgs S m tW := by simp [tW, tOm, tOne, bciArgs]

theorem bciArgs_tPp : bciArgs S m tPp := by
  refine ⟨by simp [tOne, bciArgs], ⟨bciArgs_tW S m, bciArgs_tW S m⟩, fun h => absurd h tOne_ne_zero,
    fun _ => WW_lt_alpha S m⟩

theorem bciArgs_tWp : bciArgs S m tWp :=
  ⟨trivial, bciArgs_tPp S m, by simp [tOne, bciArgs]⟩

theorem bciD_tW : bciD S m tW := ⟨NF_tW, bciArgs_tW S m⟩
theorem bciD_tPp : bciD S m tPp := ⟨NF_tPp, bciArgs_tPp S m⟩

theorem bciArgs_bcApp {P : List Term} (hP : ∀ p ∈ P, bciArgs S m p) {r : Term}
    (hr : bciArgs S m r) : bciArgs S m (bcApp P r) := by
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

theorem bciArgs_pre (j : ℕ) : bciArgs S m (bcApp (bcPre j) zero) := by
  refine bciArgs_bcApp S m (fun p hp => ?_) trivial
  simp only [bcPre, List.mem_cons, List.mem_replicate] at hp
  rcases hp with rfl | rfl | ⟨-, rfl⟩
  · exact bciArgs_tW S m
  · exact bciArgs_tW S m
  · exact bciArgs_tPp S m

/-! ## The prefix test at `α_ω` -/

theorem NF_preW_Pp : NF (bcApp bcPreW tPp) :=
  NF_bcApp bcNFL_preW (by simp [bcPreW]) (Or.inr ⟨NF_tPp, by
    rw [bcLast_preW, show head tPp = tPp from rfl, cmp_tPp_tWp]; simp⟩)

theorem val_preW_Pp : val S (bcApp bcPreW tPp) = bcAlphaW S + Nc.ncPp S := by
  rw [val_bcApp_preW, val_tPp]

theorem NF_preW_Wp : NF (bcApp bcPreW tWp) :=
  NF_bcApp bcNFL_preW (by simp [bcPreW]) (Or.inr ⟨NF_tWp, by
    rw [bcLast_preW, show head tWp = tWp from rfl, cmp_self]; simp⟩)

theorem val_preW_Wp : val S (bcApp bcPreW tWp) = bcAlphaWW S := by
  rw [val_bcApp_preW, val_tWp]; rfl

/-- **The prefix test at `α_ω`.** -/
theorem bci_pre_iff {a : Term} (ha : NF a) (haW : val S a < bcAlphaWW S) :
    bcPreW.isPrefixOf (bcSl a) = true ↔ bcAlphaW S ≤ val S a := by
  constructor
  · intro h
    have e := bcApp_of_prefix prin_preW ha h
    rw [e, val_bcApp_preW]
    exact le_self_add
  · intro h
    have h1 : bcLcmp (bcSl a) bcPreW ≠ .lt := by
      have := cmp_val_ne_lt S ha NF_preW (by rw [val_preW]; exact h)
      rwa [cmp_chain ha NF_preW, bcSl_bcApp prin_preW, show bcSl zero = [] from rfl,
        List.append_nil] at this
    have h2 : bcLcmp (bcSl a) [tW, tW, tWp, tWp] = .lt := by
      have := (cmp_lt_iff S ha NF_preW_Wp).2 (by rw [val_preW_Wp]; exact haW)
      rwa [cmp_chain ha NF_preW_Wp, bcSl_bcApp prin_preW, bcSl_prin prin_tWp,
        show bcPreW ++ [tWp] = [tW, tW, tWp, tWp] from rfl] at this
    have hN := bcNFL_bcSl ha
    generalize bcSl a = X at h1 h2 hN
    rcases X with _ | ⟨x0, X1⟩
    · simp [bcPreW, bcLcmp] at h1
    have hx0 : NF x0 := bcNFL_NF hN x0 (by simp)
    obtain ⟨rfl, h1', h2'⟩ := step_W S hx0 h1 h2
    rcases X1 with _ | ⟨x1, X2⟩
    · simp [bcLcmp] at h1'
    have hN1 := bcNFL_tail hN
    have hx1 : NF x1 := bcNFL_NF hN1 x1 (by simp)
    obtain ⟨rfl, h1'', h2''⟩ := step_W S hx1 h1' h2'
    rcases X2 with _ | ⟨x2, X3⟩
    · simp [bcLcmp] at h1''
    have hx2 : NF x2 := bcNFL_NF (bcNFL_tail hN1) x2 (by simp)
    simp only [bcLcmp] at h1'' h2''
    rcases hc : cmp x2 tWp with _ | _ | _
    · rw [hc] at h1''; simp at h1''
    · have e := eq_of_cmp_eq S hx2 NF_tWp hc
      subst e
      simp [bcPreW, List.isPrefixOf]
    · rw [hc] at h2''; simp at h2''

theorem val_head_le {r : Term} (hr : NF r) : val S (head r) ≤ val S r := by
  cases r with
  | add u v => exact le_self_add
  | _ => exact le_rfl

/-- The rest of an argument in `[α_ω, α_ω + P'·ω)` is `< P'·ω`. -/
theorem bci_rest_lt {a : Term} (ha : NF a) (haW : val S a < bcAlphaWW S)
    (hpre : bcPreW.isPrefixOf (bcSl a) = true) :
    val S (bcDrop bcPreW.length a) < Ordinal.omega0 ^ (Nc.ncPp S + 1) := by
  have e := bcApp_of_prefix prin_preW ha hpre
  rw [e, val_bcApp_preW] at haW
  exact (add_lt_add_iff_left _).1 haW

/-! ## Summand lists of images -/

theorem bcSl_bcSig {Ps Pt : List Term} : ∀ c : Term,
    bcSl (bcSig Ps Pt c) = (bcSl c).map (bcSig Ps Pt)
  | zero => by simp [bcSl]
  | add a b => by
    rw [bcSig_add]; simp only [bcSl, List.map_cons]; rw [bcSl_bcSig b]
  | inacc n => by rw [bcSl_prin (by rw [isPrin_bcSig]; rfl)]; rfl
  | inaccW => by rw [bcSl_prin (by rw [isPrin_bcSig]; rfl)]; rfl
  | phi a b => by rw [bcSl_prin (by rw [isPrin_bcSig]; rfl)]; rfl
  | om a => by rw [bcSl_prin (by rw [isPrin_bcSig]; rfl)]; rfl
  | psiS s a => by rw [bcSl_prin (by rw [isPrin_bcSig]; rfl)]; rfl
  | psiI n a => by rw [bcSl_prin (by rw [isPrin_bcSig]; rfl)]; rfl

theorem bcLcmp_map (f : Term → Term) : ∀ (X Q : List Term),
    (∀ x ∈ X, ∀ q ∈ Q, cmp (f x) q = cmp x q) → bcLcmp (X.map f) Q = bcLcmp X Q
  | [], [], _ => rfl
  | [], _ :: _, _ => rfl
  | _ :: _, [], _ => rfl
  | x :: xs, q :: qs, h => by
    simp only [List.map_cons, bcLcmp]
    rw [h x (by simp) q (by simp),
      bcLcmp_map f xs qs (fun x' hx' q' hq' => h x' (List.mem_cons_of_mem _ hx') q'
        (List.mem_cons_of_mem _ hq'))]

theorem mem_bcSl_sub : ∀ {a x : Term}, x ∈ bcSl a → bcSub x a
  | zero, _, h => by simp [bcSl] at h
  | add u v, x, h => by
    simp only [bcSl, List.mem_cons] at h
    rcases h with rfl | h
    · exact sub_add_l _ _
    · exact bcSub_trans (mem_bcSl_sub h) (sub_add_r u v)
  | inacc _, x, h => by simp [bcSl] at h; subst h; exact bcSub_refl _
  | inaccW, x, h => by simp [bcSl] at h; subst h; exact bcSub_refl _
  | phi _ _, x, h => by simp [bcSl] at h; subst h; exact bcSub_refl _
  | om _, x, h => by simp [bcSl] at h; subst h; exact bcSub_refl _
  | psiS _ _, x, h => by simp [bcSl] at h; subst h; exact bcSub_refl _
  | psiI _ _, x, h => by simp [bcSl] at h; subst h; exact bcSub_refl _

/-- **An image of a normal form `< α_{m+1}` is `< α_{m+1}`**, if `τ` keeps `cmp` between its
summands and the summands `Ω_ω`, `P'` of `α_{m+1}`. -/
theorem bci_img_lt {Ps Pt : List Term} {c : Term} (hc : NF c) (hσc : NF (bcSig Ps Pt c))
    (hlt : val S c < bcAlpha S (m + 1))
    (hx : ∀ x ∈ bcSl c, cmp (bcSig Ps Pt x) tW = cmp x tW ∧
      cmp (bcSig Ps Pt x) tPp = cmp x tPp) :
    val S (bcSig Ps Pt c) < bcAlpha S (m + 1) := by
  have h1 : cmp c (bcApp (bcPre (m + 1)) zero) = .lt :=
    cmp_lt_of_val S hc (NF_pre (m + 1)) (by rw [val_pre]; exact hlt)
  rw [cmp_chain hc (NF_pre (m + 1)), bcSl_bcApp (prin_pre (m + 1)),
    show bcSl zero = [] from rfl, List.append_nil] at h1
  have h2 : cmp (bcSig Ps Pt c) (bcApp (bcPre (m + 1)) zero) = .lt := by
    rw [cmp_chain hσc (NF_pre (m + 1)), bcSl_bcApp (prin_pre (m + 1)),
      show bcSl zero = [] from rfl, List.append_nil, bcSl_bcSig, bcLcmp_map]
    · exact h1
    · intro x hx' q hq
      simp only [bcPre, List.mem_cons, List.mem_replicate] at hq
      rcases hq with rfl | rfl | ⟨-, rfl⟩
      · exact (hx x hx').1
      · exact (hx x hx').1
      · exact (hx x hx').2
  have := (cmp_lt_iff S hσc (NF_pre (m + 1))).1 h2
  rwa [val_pre] at this

end IDom

end Googology.Trans.PoR.InaccPsi.R2.Bc

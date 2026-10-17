import Googology.Trans.PoR.InaccPsi.R2.BcChain

/-!
# The clause-by-clause induction for a base change, in general

For lists `Ps`, `Pt` and a domain `X` (a predicate `D` closed under subterms and `cardT`, and an
auxiliary predicate `G` with the same closure), `CmpOKg X N` says that `σ = bcSig Ps Pt` keeps
`cmp` on the `D`-, `G`-pairs of total size `≤ N`.

* `gen_cmp` (**the induction**): if the comparison of two `ψ_{Ω₁}`-arguments is kept whenever the
  smaller pairs are (`ArgOK X`), then `σ` keeps `cmp` on all `D`-, `G`-pairs.  Strong induction on
  `|s| + |t|`, one case per clause of `cmp` (`gen_cmp_step`); every clause except the comparison of
  two `ψ_{Ω₁}`-arguments commutes with `σ`.

No axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Bc

open Googology.Notation.InaccPsi Googology.Notation.InaccPsi.Term

/-- A domain for the base change `bcSig Ps Pt`. -/
structure GenDom (Ps Pt : List Term) where
  /-- the domain -/
  D : Term → Prop
  /-- the auxiliary condition (images of proper subterms are normal forms) -/
  G : Term → Prop
  Dsub : ∀ {x t : Term}, D t → bcSub x t → D x
  Gsub : ∀ {x t : Term}, G t → bcSub x t → G x
  Dcard : ∀ {s a : Term}, D (psiS s a) → D (cardT s)
  Gcard : ∀ {s a : Term}, G (psiS s a) → G (cardT s)

section Gen

variable {Ps Pt : List Term} (X : GenDom Ps Pt)

/-- `σ` keeps `cmp` on the pairs of total size `≤ N`. -/
def CmpOKg (N : ℕ) : Prop :=
  ∀ x y : Term, x.size + y.size ≤ N → X.D x → X.D y → X.G x → X.G y →
    cmp (bcSig Ps Pt x) (bcSig Ps Pt y) = cmp x y

/-- The hypothesis on two `ψ_{Ω₁}`-arguments. -/
def ArgOK : Prop :=
  ∀ N : ℕ, CmpOKg X N → ∀ {a1 a2 : Term}, (psiS zero a1).size + (psiS zero a2).size ≤ N + 1 →
    X.D (psiS zero a1) → X.D (psiS zero a2) → X.G (psiS zero a1) → X.G (psiS zero a2) →
    cmp (bcArg Ps Pt a1) (bcArg Ps Pt a2) = cmp a1 a2

theorem sub_add_l (a b : Term) : bcSub a (add a b) := Or.inr (Or.inl (Or.inl rfl))
theorem sub_add_r (a b : Term) : bcSub b (add a b) := Or.inr (Or.inr (Or.inl rfl))
theorem sub_phi_l (a b : Term) : bcSub a (phi a b) := Or.inr (Or.inl (Or.inl rfl))
theorem sub_phi_r (a b : Term) : bcSub b (phi a b) := Or.inr (Or.inr (Or.inl rfl))
theorem sub_om (a : Term) : bcSub a (om a) := Or.inr (Or.inl rfl)
theorem sub_psiS_s (s a : Term) : bcSub s (psiS s a) := Or.inr (Or.inl (Or.inl rfl))
theorem sub_psiS_a (s a : Term) : bcSub a (psiS s a) := Or.inr (Or.inr (Or.inl rfl))
theorem sub_psiI (n : ℕ) (a : Term) : bcSub a (psiI n a) := Or.inr (Or.inl rfl)

theorem cmp_om_om (a c : Term) : cmp (om a) (om c) = cmp a c := by simp only [Term.cmp]

theorem gen_sig_zero_right (Ps Pt : List Term) (x : Term) :
    cmp (bcSig Ps Pt x) zero = cmp x zero := by
  by_cases h : x = zero
  · subst h; rw [bcSig_zero]
  · rw [cmp_zero_right h, cmp_zero_right (bcSig_ne_zero h)]

theorem gen_sig_zero_left (Ps Pt : List Term) (x : Term) :
    cmp zero (bcSig Ps Pt x) = cmp zero x := by
  by_cases h : x = zero
  · subst h; rw [bcSig_zero]
  · rw [cmp_zero_left h, cmp_zero_left (bcSig_ne_zero h)]

variable {X}

theorem gen_zl {N : ℕ} (_ih : CmpOKg X N) {t : Term} (_hN : zero.size + t.size ≤ N + 1)
    (_hs : X.D zero) (_ht : X.D t) (_gs : X.G zero) (_gt : X.G t) :
    cmp (bcSig Ps Pt zero) (bcSig Ps Pt t) = cmp zero t := by
  rw [bcSig_zero]; exact gen_sig_zero_left Ps Pt t

theorem gen_zr {N : ℕ} (_ih : CmpOKg X N) {t : Term} (_hN : t.size + zero.size ≤ N + 1)
    (_hs : X.D t) (_ht : X.D zero) (_gs : X.G t) (_gt : X.G zero) (_h0 : t ≠ zero) :
    cmp (bcSig Ps Pt t) (bcSig Ps Pt zero) = cmp t zero := by
  rw [bcSig_zero]; exact gen_sig_zero_right Ps Pt t

theorem gen_addadd {N : ℕ} (ih : CmpOKg X N) {a b c d : Term}
    (hN : (add a b).size + (add c d).size ≤ N + 1)
    (hs : X.D (add a b)) (ht : X.D (add c d)) (gs : X.G (add a b)) (gt : X.G (add c d)) :
    cmp (bcSig Ps Pt (add a b)) (bcSig Ps Pt (add c d)) =
      cmp (add a b) (add c d) := by
  simp only [size] at hN
  rw [bcSig_add, bcSig_add, cmp_add_add, cmp_add_add,
    ih a c (by omega) (X.Dsub hs (sub_add_l a b)) (X.Dsub ht (sub_add_l c d))
      (X.Gsub gs (sub_add_l a b)) (X.Gsub gt (sub_add_l c d)),
    ih b d (by omega) (X.Dsub hs (sub_add_r a b)) (X.Dsub ht (sub_add_r c d))
      (X.Gsub gs (sub_add_r a b)) (X.Gsub gt (sub_add_r c d))]

theorem gen_addprin {N : ℕ} (ih : CmpOKg X N) {a b t : Term}
    (hN : (add a b).size + t.size ≤ N + 1)
    (hs : X.D (add a b)) (ht : X.D t) (gs : X.G (add a b)) (gt : X.G t)
    (htP : t.isPrin = true) :
    cmp (bcSig Ps Pt (add a b)) (bcSig Ps Pt t) =
      cmp (add a b) t := by
  simp only [size] at hN
  rw [bcSig_add, cmp_add_left _ _ (by rw [isPrin_bcSig]; exact htP), cmp_add_left _ _ htP,
    ih a t (by omega) (X.Dsub hs (sub_add_l a b)) ht (X.Gsub gs (sub_add_l a b)) gt]

theorem gen_prinadd {N : ℕ} (ih : CmpOKg X N) {c d t : Term}
    (hN : t.size + (add c d).size ≤ N + 1)
    (hs : X.D t) (ht : X.D (add c d)) (gs : X.G t) (gt : X.G (add c d))
    (htP : t.isPrin = true) :
    cmp (bcSig Ps Pt t) (bcSig Ps Pt (add c d)) =
      cmp t (add c d) := by
  simp only [size] at hN
  rw [bcSig_add, cmp_add_right _ _ (by rw [isPrin_bcSig]; exact htP), cmp_add_right _ _ htP,
    ih t c (by omega) hs (X.Dsub ht (sub_add_l c d)) gs (X.Gsub gt (sub_add_l c d))]

theorem gen_phiphi {N : ℕ} (ih : CmpOKg X N) {a b c d : Term}
    (hN : (phi a b).size + (phi c d).size ≤ N + 1)
    (hs : X.D (phi a b)) (ht : X.D (phi c d)) (gs : X.G (phi a b)) (gt : X.G (phi c d)) :
    cmp (bcSig Ps Pt (phi a b)) (bcSig Ps Pt (phi c d)) =
      cmp (phi a b) (phi c d) := by
  have hN' := hN
  simp only [size] at hN'
  have hac := ih a c (by omega) (X.Dsub hs (sub_phi_l a b)) (X.Dsub ht (sub_phi_l c d))
    (X.Gsub gs (sub_phi_l a b)) (X.Gsub gt (sub_phi_l c d))
  rw [bcSig_phi, bcSig_phi]
  rcases h : cmp a c with _ | _ | _
  · rw [cmp_phi_phi_lt h, cmp_phi_phi_lt (hac.trans h), ← bcSig_phi]
    exact ih b (phi c d) (by simp only [size]; omega) (X.Dsub hs (sub_phi_r a b)) ht
      (X.Gsub gs (sub_phi_r a b)) gt
  · rw [cmp_phi_phi_eq h, cmp_phi_phi_eq (hac.trans h)]
    exact ih b d (by omega) (X.Dsub hs (sub_phi_r a b)) (X.Dsub ht (sub_phi_r c d))
      (X.Gsub gs (sub_phi_r a b)) (X.Gsub gt (sub_phi_r c d))
  · rw [cmp_phi_phi_gt h, cmp_phi_phi_gt (hac.trans h), ← bcSig_phi]
    exact ih (phi a b) d (by simp only [size]; omega) hs (X.Dsub ht (sub_phi_r c d))
      gs (X.Gsub gt (sub_phi_r c d))

theorem gen_phisc {N : ℕ} (ih : CmpOKg X N) {a b t : Term}
    (hN : (phi a b).size + t.size ≤ N + 1)
    (hs : X.D (phi a b)) (ht : X.D t) (gs : X.G (phi a b)) (gt : X.G t)
    (htS : t.isSC = true) :
    cmp (bcSig Ps Pt (phi a b)) (bcSig Ps Pt t) =
      cmp (phi a b) t := by
  simp only [size] at hN
  have hσt : (bcSig Ps Pt t).isSC = true := by rw [isSC_bcSig]; exact htS
  have hat := ih a t (by omega) (X.Dsub hs (sub_phi_l a b)) ht (X.Gsub gs (sub_phi_l a b)) gt
  rw [bcSig_phi]
  rcases h : cmp a t with _ | _ | _
  · rw [cmp_phi_left_lt htS h, cmp_phi_left_lt hσt (hat.trans h)]
    exact ih b t (by omega) (X.Dsub hs (sub_phi_r a b)) ht (X.Gsub gs (sub_phi_r a b)) gt
  · rw [cmp_phi_left_eq htS h, cmp_phi_left_eq hσt (hat.trans h)]
    exact gen_sig_zero_right Ps Pt b
  · rw [cmp_phi_left_gt htS h, cmp_phi_left_gt hσt (hat.trans h)]

theorem gen_scphi {N : ℕ} (ih : CmpOKg X N) {c d t : Term}
    (hN : t.size + (phi c d).size ≤ N + 1)
    (hs : X.D t) (ht : X.D (phi c d)) (gs : X.G t) (gt : X.G (phi c d))
    (htS : t.isSC = true) :
    cmp (bcSig Ps Pt t) (bcSig Ps Pt (phi c d)) =
      cmp t (phi c d) := by
  simp only [size] at hN
  have hσt : (bcSig Ps Pt t).isSC = true := by rw [isSC_bcSig]; exact htS
  have htc := ih t c (by omega) hs (X.Dsub ht (sub_phi_l c d)) gs (X.Gsub gt (sub_phi_l c d))
  rw [bcSig_phi]
  rcases h : cmp t c with _ | _ | _
  · rw [cmp_phi_right_lt htS h, cmp_phi_right_lt hσt (htc.trans h)]
  · rw [cmp_phi_right_eq htS h, cmp_phi_right_eq hσt (htc.trans h)]
    exact gen_sig_zero_left Ps Pt d
  · rw [cmp_phi_right_gt htS h, cmp_phi_right_gt hσt (htc.trans h)]
    exact ih t d (by omega) hs (X.Dsub ht (sub_phi_r c d)) gs (X.Gsub gt (sub_phi_r c d))

theorem gen_omom {N : ℕ} (ih : CmpOKg X N) {a c : Term}
    (hN : (om a).size + (om c).size ≤ N + 1)
    (hs : X.D (om a)) (ht : X.D (om c)) (gs : X.G (om a)) (gt : X.G (om c)) :
    cmp (bcSig Ps Pt (om a)) (bcSig Ps Pt (om c)) =
      cmp (om a) (om c) := by
  simp only [size] at hN
  rw [bcSig_om, bcSig_om, cmp_om_om, cmp_om_om]
  exact ih a c (by omega) (X.Dsub hs (sub_om a)) (X.Dsub ht (sub_om c))
    (X.Gsub gs (sub_om a)) (X.Gsub gt (sub_om c))

theorem gen_omF {N : ℕ} (ih : CmpOKg X N) {a f : Term}
    (hN : (om a).size + f.size ≤ N + 1)
    (hs : X.D (om a)) (ht : X.D f) (gs : X.G (om a)) (gt : X.G f) (hf : f.isF = true) :
    cmp (bcSig Ps Pt (om a)) (bcSig Ps Pt f) =
      cmp (om a) f := by
  simp only [size] at hN
  rw [bcSig_om, cmp_om_F _ (by rw [isF_bcSig]; exact hf), cmp_om_F _ hf]
  exact ih a f (by omega) (X.Dsub hs (sub_om a)) ht (X.Gsub gs (sub_om a)) gt

theorem gen_Fom {N : ℕ} (ih : CmpOKg X N) {c f : Term}
    (hN : f.size + (om c).size ≤ N + 1)
    (hs : X.D f) (ht : X.D (om c)) (gs : X.G f) (gt : X.G (om c)) (hf : f.isF = true) :
    cmp (bcSig Ps Pt f) (bcSig Ps Pt (om c)) =
      cmp f (om c) := by
  simp only [size] at hN
  rw [bcSig_om, cmp_F_om _ (by rw [isF_bcSig]; exact hf), cmp_F_om _ hf]
  exact ih f c (by omega) hs (X.Dsub ht (sub_om c)) gs (X.Gsub gt (sub_om c))

theorem gen_psiSK {N : ℕ} (ih : CmpOKg X N) {s a t : Term}
    (hN : (psiS s a).size + t.size ≤ N + 1)
    (hs : X.D (psiS s a)) (ht : X.D t) (gs : X.G (psiS s a)) (gt : X.G t)
    (hK : t.isK = true) :
    cmp (bcSig Ps Pt (psiS s a)) (bcSig Ps Pt t) =
      cmp (psiS s a) t := by
  have h1 := size_cardT_lt s a
  rw [bcSig_psiS, cmp_psiS_K _ _ (by rw [isK_bcSig]; exact hK), cmp_psiS_K _ _ hK, cardT_bcSig,
    ih (cardT s) t (by omega) (X.Dcard hs) ht (X.Gcard gs) gt]

theorem gen_KpsiS {N : ℕ} (ih : CmpOKg X N) {s a t : Term}
    (hN : t.size + (psiS s a).size ≤ N + 1)
    (hs : X.D t) (ht : X.D (psiS s a)) (gs : X.G t) (gt : X.G (psiS s a))
    (hK : t.isK = true) :
    cmp (bcSig Ps Pt t) (bcSig Ps Pt (psiS s a)) =
      cmp t (psiS s a) := by
  have h1 := size_cardT_lt s a
  rw [bcSig_psiS, cmp_K_psiS _ _ (by rw [isK_bcSig]; exact hK), cmp_K_psiS _ _ hK, cardT_bcSig,
    ih t (cardT s) (by omega) hs (X.Dcard ht) gs (X.Gcard gt)]

theorem gen_psiIpsiI {N : ℕ} (ih : CmpOKg X N) {n m : ℕ} {a b : Term}
    (hN : (psiI n a).size + (psiI m b).size ≤ N + 1)
    (hs : X.D (psiI n a)) (ht : X.D (psiI m b)) (gs : X.G (psiI n a)) (gt : X.G (psiI m b)) :
    cmp (bcSig Ps Pt (psiI n a)) (bcSig Ps Pt (psiI m b)) =
      cmp (psiI n a) (psiI m b) := by
  simp only [size] at hN
  rw [bcSig_psiI, bcSig_psiI, cmp_psiI_psiI, cmp_psiI_psiI,
    ih a b (by omega) (X.Dsub hs (sub_psiI n a)) (X.Dsub ht (sub_psiI m b))
      (X.Gsub gs (sub_psiI n a)) (X.Gsub gt (sub_psiI m b))]


theorem gen_psiSpsiS {N : ℕ} (ih : CmpOKg X N) (harg : ArgOK X) {s1 a1 s2 a2 : Term}
    (hN : (psiS s1 a1).size + (psiS s2 a2).size ≤ N + 1)
    (hs : X.D (psiS s1 a1)) (ht : X.D (psiS s2 a2))
    (gs : X.G (psiS s1 a1)) (gt : X.G (psiS s2 a2)) :
    cmp (bcSig Ps Pt (psiS s1 a1)) (bcSig Ps Pt (psiS s2 a2)) =
      cmp (psiS s1 a1) (psiS s2 a2) := by
  have hN' := hN
  simp only [size] at hN'
  have h12 := ih s1 s2 (by omega) (X.Dsub hs (sub_psiS_s s1 a1)) (X.Dsub ht (sub_psiS_s s2 a2))
    (X.Gsub gs (sub_psiS_s s1 a1)) (X.Gsub gt (sub_psiS_s s2 a2))
  have da1 := X.Dsub hs (sub_psiS_a s1 a1)
  have da2 := X.Dsub ht (sub_psiS_a s2 a2)
  have ga1 := X.Gsub gs (sub_psiS_a s1 a1)
  have ga2 := X.Gsub gt (sub_psiS_a s2 a2)
  rw [bcSig_psiS, bcSig_psiS, cmp_psiS_psiS, cmp_psiS_psiS, h12]
  split_ifs with heq h1 h2 h2
  · subst h1; subst h2
    exact harg N ih hN hs ht gs gt
  · subst h1; exact absurd heq (by rw [cmp_zero_left h2]; simp)
  · subst h2; exact absurd heq (by rw [cmp_zero_right h1]; simp)
  · exact ih a1 a2 (by omega) da1 da2 ga1 ga2
  · rfl

variable (X)

/-- One step of the induction: all `cmp`-clauses. -/
theorem gen_cmp_step {N : ℕ} (ih : CmpOKg X N) (harg : ArgOK X) :
    ∀ s t : Term, s.size + t.size ≤ N + 1 → X.D s → X.D t → X.G s → X.G t →
      cmp (bcSig Ps Pt s) (bcSig Ps Pt t) = cmp s t
  | zero, zero, hN, hs, ht, gs, gt => gen_zl ih hN hs ht gs gt
  | zero, inacc n2, hN, hs, ht, gs, gt => gen_zl ih hN hs ht gs gt
  | zero, inaccW, hN, hs, ht, gs, gt => gen_zl ih hN hs ht gs gt
  | zero, add a2 b2, hN, hs, ht, gs, gt => gen_zl ih hN hs ht gs gt
  | zero, phi a2 b2, hN, hs, ht, gs, gt => gen_zl ih hN hs ht gs gt
  | zero, om a2, hN, hs, ht, gs, gt => gen_zl ih hN hs ht gs gt
  | zero, psiS s2 a2, hN, hs, ht, gs, gt => gen_zl ih hN hs ht gs gt
  | zero, psiI n2 a2, hN, hs, ht, gs, gt => gen_zl ih hN hs ht gs gt
  | inacc n1, zero, hN, hs, ht, gs, gt => gen_zr ih hN hs ht gs gt (by simp)
  | inacc n1, inacc n2, hN, hs, ht, gs, gt => by simp only [bcSig_inacc]
  | inacc n1, inaccW, hN, hs, ht, gs, gt => by simp only [bcSig_inacc, bcSig_inaccW]
  | inacc n1, add a2 b2, hN, hs, ht, gs, gt => gen_prinadd ih hN hs ht gs gt rfl
  | inacc n1, phi a2 b2, hN, hs, ht, gs, gt => gen_scphi ih hN hs ht gs gt rfl
  | inacc n1, om a2, hN, hs, ht, gs, gt => gen_Fom ih hN hs ht gs gt rfl
  | inacc n1, psiS s2 a2, hN, hs, ht, gs, gt => gen_KpsiS ih hN hs ht gs gt rfl
  | inacc n1, psiI n2 a2, hN, hs, ht, gs, gt => by simp only [bcSig_inacc, bcSig_psiI]; simp only [Term.cmp]
  | inaccW, zero, hN, hs, ht, gs, gt => gen_zr ih hN hs ht gs gt (by simp)
  | inaccW, inacc n2, hN, hs, ht, gs, gt => by simp only [bcSig_inaccW, bcSig_inacc]
  | inaccW, inaccW, hN, hs, ht, gs, gt => by simp only [bcSig_inaccW]
  | inaccW, add a2 b2, hN, hs, ht, gs, gt => gen_prinadd ih hN hs ht gs gt rfl
  | inaccW, phi a2 b2, hN, hs, ht, gs, gt => gen_scphi ih hN hs ht gs gt rfl
  | inaccW, om a2, hN, hs, ht, gs, gt => gen_Fom ih hN hs ht gs gt rfl
  | inaccW, psiS s2 a2, hN, hs, ht, gs, gt => gen_KpsiS ih hN hs ht gs gt rfl
  | inaccW, psiI n2 a2, hN, hs, ht, gs, gt => by simp only [bcSig_inaccW, bcSig_psiI]; simp only [Term.cmp]
  | add a1 b1, zero, hN, hs, ht, gs, gt => gen_zr ih hN hs ht gs gt (by simp)
  | add a1 b1, inacc n2, hN, hs, ht, gs, gt => gen_addprin ih hN hs ht gs gt rfl
  | add a1 b1, inaccW, hN, hs, ht, gs, gt => gen_addprin ih hN hs ht gs gt rfl
  | add a1 b1, add a2 b2, hN, hs, ht, gs, gt => gen_addadd ih hN hs ht gs gt
  | add a1 b1, phi a2 b2, hN, hs, ht, gs, gt => gen_addprin ih hN hs ht gs gt rfl
  | add a1 b1, om a2, hN, hs, ht, gs, gt => gen_addprin ih hN hs ht gs gt rfl
  | add a1 b1, psiS s2 a2, hN, hs, ht, gs, gt => gen_addprin ih hN hs ht gs gt rfl
  | add a1 b1, psiI n2 a2, hN, hs, ht, gs, gt => gen_addprin ih hN hs ht gs gt rfl
  | phi a1 b1, zero, hN, hs, ht, gs, gt => gen_zr ih hN hs ht gs gt (by simp)
  | phi a1 b1, inacc n2, hN, hs, ht, gs, gt => gen_phisc ih hN hs ht gs gt rfl
  | phi a1 b1, inaccW, hN, hs, ht, gs, gt => gen_phisc ih hN hs ht gs gt rfl
  | phi a1 b1, add a2 b2, hN, hs, ht, gs, gt => gen_prinadd ih hN hs ht gs gt rfl
  | phi a1 b1, phi a2 b2, hN, hs, ht, gs, gt => gen_phiphi ih hN hs ht gs gt
  | phi a1 b1, om a2, hN, hs, ht, gs, gt => gen_phisc ih hN hs ht gs gt rfl
  | phi a1 b1, psiS s2 a2, hN, hs, ht, gs, gt => gen_phisc ih hN hs ht gs gt rfl
  | phi a1 b1, psiI n2 a2, hN, hs, ht, gs, gt => gen_phisc ih hN hs ht gs gt rfl
  | om a1, zero, hN, hs, ht, gs, gt => gen_zr ih hN hs ht gs gt (by simp)
  | om a1, inacc n2, hN, hs, ht, gs, gt => gen_omF ih hN hs ht gs gt rfl
  | om a1, inaccW, hN, hs, ht, gs, gt => gen_omF ih hN hs ht gs gt rfl
  | om a1, add a2 b2, hN, hs, ht, gs, gt => gen_prinadd ih hN hs ht gs gt rfl
  | om a1, phi a2 b2, hN, hs, ht, gs, gt => gen_scphi ih hN hs ht gs gt rfl
  | om a1, om a2, hN, hs, ht, gs, gt => gen_omom ih hN hs ht gs gt
  | om a1, psiS s2 a2, hN, hs, ht, gs, gt => gen_KpsiS ih hN hs ht gs gt rfl
  | om a1, psiI n2 a2, hN, hs, ht, gs, gt => gen_omF ih hN hs ht gs gt rfl
  | psiS s1 a1, zero, hN, hs, ht, gs, gt => gen_zr ih hN hs ht gs gt (by simp)
  | psiS s1 a1, inacc n2, hN, hs, ht, gs, gt => gen_psiSK ih hN hs ht gs gt rfl
  | psiS s1 a1, inaccW, hN, hs, ht, gs, gt => gen_psiSK ih hN hs ht gs gt rfl
  | psiS s1 a1, add a2 b2, hN, hs, ht, gs, gt => gen_prinadd ih hN hs ht gs gt rfl
  | psiS s1 a1, phi a2 b2, hN, hs, ht, gs, gt => gen_scphi ih hN hs ht gs gt rfl
  | psiS s1 a1, om a2, hN, hs, ht, gs, gt => gen_psiSK ih hN hs ht gs gt rfl
  | psiS s1 a1, psiS s2 a2, hN, hs, ht, gs, gt => gen_psiSpsiS ih harg hN hs ht gs gt
  | psiS s1 a1, psiI n2 a2, hN, hs, ht, gs, gt => gen_psiSK ih hN hs ht gs gt rfl
  | psiI n1 a1, zero, hN, hs, ht, gs, gt => gen_zr ih hN hs ht gs gt (by simp)
  | psiI n1 a1, inacc n2, hN, hs, ht, gs, gt => by simp only [bcSig_psiI, bcSig_inacc]; simp only [Term.cmp]
  | psiI n1 a1, inaccW, hN, hs, ht, gs, gt => by simp only [bcSig_psiI, bcSig_inaccW]; simp only [Term.cmp]
  | psiI n1 a1, add a2 b2, hN, hs, ht, gs, gt => gen_prinadd ih hN hs ht gs gt rfl
  | psiI n1 a1, phi a2 b2, hN, hs, ht, gs, gt => gen_scphi ih hN hs ht gs gt rfl
  | psiI n1 a1, om a2, hN, hs, ht, gs, gt => gen_Fom ih hN hs ht gs gt rfl
  | psiI n1 a1, psiS s2 a2, hN, hs, ht, gs, gt => gen_KpsiS ih hN hs ht gs gt rfl
  | psiI n1 a1, psiI n2 a2, hN, hs, ht, gs, gt => gen_psiIpsiI ih hN hs ht gs gt


theorem gen_cmp_all (harg : ArgOK X) : ∀ N : ℕ, CmpOKg X N
  | 0 => fun x y h => absurd h (by have := size_pos x; omega)
  | N + 1 => fun x y h => gen_cmp_step X (gen_cmp_all harg N) harg x y h

/-- **The induction**: `σ` keeps `cmp` on the domain, given `ArgOK`. -/
theorem gen_cmp (harg : ArgOK X) {s t : Term} (hs : X.D s) (ht : X.D t) (gs : X.G s)
    (gt : X.G t) : cmp (bcSig Ps Pt s) (bcSig Ps Pt t) = cmp s t :=
  gen_cmp_all X harg _ s t le_rfl hs ht gs gt

end Gen

end Googology.Trans.PoR.InaccPsi.R2.Bc

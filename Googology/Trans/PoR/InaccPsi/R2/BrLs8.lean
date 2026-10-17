import Googology.Trans.PoR.InaccPsi.R2.BrLs7

/-!
# LOW-STEP, part 8: Lemma D for the map `E` over `σ`

* `CL_topAtom`: a top atom `≥ σ` of a term of the class is in the class;
* `Zbound`: the `K*₁`-elements of `E(u)` for the parts `u` of `ζ` (through sums and `φ`) are below a bound
  `Y ≥ P₁` that is above the codes of the top atoms `ψ_{Ω₂}(d')`;
* `D_ls` (**Lemma D**): the invariants `DL` of `E(t)` for every `t` of the class, given them and Lemma M on
  smaller terms (the `A`-clause: the domain condition of `G(pmax ζ) + E ζ` by Lemma Q1 and Lemma PMAX).
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Br

open Ordinal Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq Tm

variable {S : InaccSeq.{0}} {σ : Ordinal.{0}} {m n : ℕ}

theorem CL_topAtom {ζ : Term} (hζ : CL S σ m n ζ) :
    ∀ {a : Term}, a ∈ topAtoms ζ → ¬ Term.val S a < σ → CL S σ m n a := by
  induction hζ with
  | par hn hv =>
    intro a ha hva
    exact absurd (lt_of_le_of_lt (topAtom_le hn ha) hv) hva
  | add _ _ _ _ iha ihb =>
    intro a ha hva
    simp only [topAtoms, List.mem_append] at ha
    rcases ha with ha | ha
    · exact iha ha hva
    · exact ihb ha hva
  | phi _ _ _ _ iha ihb =>
    intro a ha hva
    simp only [topAtoms, List.mem_append] at ha
    rcases ha with ha | ha
    · exact iha ha hva
    · exact ihb ha hva
  | om hn hv hk0 hk => intro a ha _; simp [topAtoms] at ha; subst ha; exact CL.om hn hv hk0 hk
  | psiS hn hv hk0 hk hcω hc _ =>
    intro a ha _; simp [topAtoms] at ha; subst ha; exact CL.psiS hn hv hk0 hk hcω hc
  | psiA hn hv hs0 h1 h2 h3 h4 _ =>
    intro a ha _; simp [topAtoms] at ha; subst ha; exact CL.psiA hn hv hs0 h1 h2 h3 h4

theorem lvl_of_bounds_σ (_hσ : Base σ) {j : ℕ} {v : Ordinal.{0}} (h1 : OmT σ j ≤ v)
    (h2 : v < OmT σ (j + 1)) : lvl v = j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have := lvl_le_of_lt (n := 0) (by rw [← OmT_succ_indep σ 0]; exact h2); omega
  · rw [OmT_pos_of_ne hj.ne'] at h1
    rw [OmT_succ_indep] at h2
    exact lvl_eq (by rw [OmT_pos_of_ne hj.ne']; exact h1) h2 hj.ne'

theorem OmT_zero_le (hσ : Base σ) (k : ℕ) : σ ≤ OmT σ k := by
  rw [← OmT_zero σ]; exact OmT_mono hσ (Nat.zero_le k)

/-- **The bound for the parts of `ζ`.** -/
theorem Zbound (hσ : Base σ) {ζ : Term} {Y : Ordinal.{0}} (hP1 : ev σ (Pk 1) ≤ Y)
    (hD : ∀ u : Term, u.size ≤ ζ.size → CL S σ m n u → DL S σ m n u)
    (hatom : ∀ s1 d', Term.psiS s1 d' ∈ topAtoms ζ → Term.val S s1 = 1 →
      ev σ (plus σ (Pk 1) (gFc σ (Ex S σ m n d'))) < Y ∧
        ∀ p ∈ Kst 1 (gFc σ (Ex S σ m n d')), ev σ p.2 < Y) :
    ∀ u : Term, CL S σ m n u → u.size ≤ ζ.size → (∀ a ∈ topAtoms u, a ∈ topAtoms ζ) →
      Term.val S u < Om ((1 : Ordinal.{0}) + 1) →
      ∀ p ∈ Kst 1 (Ex S σ m n u), ev σ p.2 < Y := by
  have hY0 : 0 < Y := lt_of_lt_of_le (lt_of_le_of_lt zero_le (gev_Pk_bounds hσ 1).1) hP1
  have hO2 : OmT σ 2 < Y := lt_of_lt_of_le (gev_Pk_bounds hσ 1).1 hP1
  have hOm2 : Om ((1 : Ordinal.{0}) + 1) = OmT σ 2 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, OmT_succ]; norm_num
  intro u hu
  induction hu with
  | par hn hv => intro _ _ _ p hp; rw [Ex_par hv] at hp; simp [Kst] at hp
  | @add a b hn hv ha hb iha ihb =>
    intro hs htop hlt p hp
    rw [(hD _ hs (CL.add hn hv ha hb)).add a b rfl hv] at hp
    simp only [Kst, List.mem_append] at hp
    simp only [topAtoms, List.mem_append] at htop
    rcases hp with hp | hp
    · exact iha (by simp [Term.size] at hs; omega) (fun x hx => htop x (Or.inl hx))
        (lt_of_le_of_lt (val_le_add_left a b) hlt) p hp
    · exact ihb (by simp [Term.size] at hs; omega) (fun x hx => htop x (Or.inr hx))
        (lt_of_le_of_lt (val_le_add_right a b) hlt) p hp
  | @om b j hn hv hj0 hj =>
    intro _ _ _ p hp
    rw [Ex, EL_om hv, hj, natOf_nat] at hp
    simp only [Omk, Kst] at hp
    split_ifs at hp
    · simp at hp
    · simp at hp; subst hp; exact hY0
  | @psiA s'' c'' hn hv hs0 _ _ _ _ _ =>
    intro _ _ _ p hp
    have h0 : natOf (Term.val S s'') = 0 := by rw [hs0]; exact natOf_nat 0
    rw [Ex, EL_psi0 hv h0] at hp
    simp [Kst] at hp
  | @phi x y hn hv hx hy ihx ihy =>
    intro hs htop hlt p hp
    have hDx := hD x (by simp [Term.size] at hs; omega) hx
    have hDy := hD y (by simp [Term.size] at hs; omega) hy
    obtain ⟨vx, vy⟩ := NF_phi_lt (S := S) hn
    set j := lvl (Term.val S (.phi x y)) with hjdef
    have hvω : Term.val S (.phi x y) < Om (ω : Ordinal.{0}) := hlt.trans Om2_lt_Om_omega
    have hj1 : j ≤ 1 := lvl_le_of_lt (by rw [OmT_succ]; simpa using hlt)
    have hxk : ev σ (Ex S σ m n x) < OmT σ (j + 1) :=
      lt_of_lt_of_le hDx.lt (OmT_mono hσ (by have := lvl_mono hvω vx.le; omega))
    have hyk : ev σ (Ex S σ m n y) < OmT σ (j + 1) :=
      lt_of_lt_of_le hDy.lt (OmT_mono hσ (by have := lvl_mono hvω vy.le; omega))
    simp only [topAtoms, List.mem_append] at htop
    rw [Ex, EL_phi hv, ← hjdef] at hp
    simp only [Kst] at hp
    split_ifs at hp with hjk
    · simp at hp
    have hj : j = 1 := by omega
    rcases List.mem_cons.1 hp with hp | hp
    · subst hp
      refine lt_of_lt_of_le ?_ hP1
      rw [hj] at hxk hyk ⊢
      exact gcodephi_lt_Pk hσ hDx.nf hDy.nf hxk hyk
    · rcases List.mem_cons.1 (gKst_codephi hσ (by omega) hp) with h | h
      · subst h; rw [hj] at hxk; exact hxk.trans hO2
      · rcases List.mem_append.1 h with h | h
        · exact ihx (by simp [Term.size] at hs; omega) (fun a ha => htop a (Or.inl ha)) (vx.trans hlt) p h
        · exact ihy (by simp [Term.size] at hs; omega) (fun a ha => htop a (Or.inr ha)) (vy.trans hlt) p h
  | @psiS s'' c'' j hn hv hj0 hj hcω' hcc _ =>
    intro hs htop hlt p hp
    have hj1 : j = 1 := by
      have h1 := (psiS_bounds_nat s'' c'' hj).1
      by_contra hne
      have h2 : 2 ≤ j := by omega
      have h3 : Om ((1 : Ordinal.{0}) + 1) ≤ Om (j : Ordinal.{0}) := by
        refine Om_le_Om.2 ?_; exact_mod_cast h2
      exact absurd (h3.trans_lt (h1.trans hlt)) (lt_irrefl _)
    subst hj1
    have hmem : Term.psiS s'' c'' ∈ topAtoms ζ := htop _ (by simp [topAtoms])
    have hs1 : Term.val S s'' = 1 := by rw [hj]; norm_num
    obtain ⟨ha1, ha2⟩ := hatom s'' c'' hmem hs1
    have hnat : natOf (Term.val S s'') ≠ 0 := by rw [hj, natOf_nat]; exact one_ne_zero
    rw [Ex, EL_psiS hv hnat, hj, natOf_nat] at hp
    simp only [Kst, show ¬ (1 < 1) by omega, if_false] at hp
    rcases List.mem_cons.1 hp with hp | hp
    · subst hp; exact ha1
    · rcases List.mem_append.1 (Kst_plus σ 1 _ _ hp) with h | h
      · rw [Kst_Pk (by omega)] at h
        simp at h
        rcases h with rfl | rfl
        · rw [gev_Omk hσ]; exact hO2
        · exact hY0
      · exact ha2 p h

theorem lvl_zero_of_lt_Om1 {v : Ordinal.{0}} (h : v < Om (1 : Ordinal.{0})) : lvl v = 0 := by
  have := lvl_le_of_lt (n := 0) (v := v) (by rw [OmT_succ]; simpa using h); omega

theorem CL_val_lt (hσ : Base σ) {t : Term} (h : CL S σ m n t) : Term.val S t < Om (ω : Ordinal.{0}) := by
  induction h with
  | par _ hv => exact hv.trans (hσ.lt_Om1.trans (by
      have := Om_lt_Om_omega 1; simpa using this))
  | add _ _ _ _ iha ihb => simp only [Term.val]; exact Om_omega_principal iha ihb
  | phi _ _ _ _ iha ihb => simp only [Term.val]; exact Om_omega_SC.2 _ iha _ ihb
  | om _ _ _ hk => simp only [Term.val]; rw [hk]; exact Om_lt_Om_omega _
  | @psiS s c k _ _ _ hk _ _ _ =>
    have := (psiS_bounds_nat s c hk).2
    exact this.trans (OmT_succ_lt_Om_omega 1 k)
  | @psiA s c _ _ hs0 _ _ _ _ _ =>
    have := (Term.val_psiS_bounds S s c).2
    rw [hs0, zero_add] at this
    exact this.trans (by have := Om_lt_Om_omega 1; simpa using this)

theorem CL_head {b : Term} (h : CL S σ m n b) (hb0 : b ≠ .zero) : CL S σ m n (Term.head b) := by
  cases h with
  | par hn hv => exact CL.par hn.head (lt_of_le_of_lt (val_head_le b) hv)
  | add _ _ ha _ => exact ha
  | phi hn hv ha hb => exact CL.phi hn hv ha hb
  | om hn hv hk0 hk => exact CL.om hn hv hk0 hk
  | psiS hn hv hk0 hk hcω hc => exact CL.psiS hn hv hk0 hk hcω hc
  | psiA hn hv hs0 h1 h2 h3 h4 => exact CL.psiA hn hv hs0 h1 h2 h3 h4

/-- **Lemma D** for the map over `σ`. -/
theorem D_ls (hσ : Base σ) {t : Term} (hc : CL S σ m n t)
    (hDs : ∀ u : Term, u.size < t.size → CL S σ m n u → DL S σ m n u)
    (hMs : ∀ x y : Term, x.size < t.size → y.size < t.size → CL S σ m n x → CL S σ m n y →
      Term.val S x < Term.val S y → ev σ (Ex S σ m n x) < ev σ (Ex S σ m n y)) : DL S σ m n t := by
  have hvω0 := CL_val_lt hσ hc
  cases hc with
  | par hn hv => exact DL_par hσ hv
  | @add a b hn hv ha hb =>
    have hDa := hDs a (by simp only [Term.size]; omega) ha
    have hDb := hDs b (by simp only [Term.size]; omega) hb
    obtain ⟨hna, hnb, hpa, hb0, _⟩ := id hn
    have hvω := hvω0
    -- the head is not a parameter
    have hva : ¬ Term.val S a < σ := by
      intro h; exact hv (val_lt_of_head hn hσ.principal h)
    obtain ⟨hla, ⟨ea, hea⟩⟩ := hDa.prin hpa hva
    have hvb : Term.val S b ≠ 0 := Term.val_ne_zero S hnb hb0
    have hEb0 : Ex S σ m n b ≠ par 0 := by
      intro e; have := hDb.ne hvb; rw [e] at this; exact this rfl
    have hle : hd σ (Ex S σ m n b) ≤ ev σ (Ex S σ m n a) := by
      by_cases hvb' : Term.val S b < σ
      · rw [Ex_par hvb']; exact hvb'.le.trans (hDa.ge hva)
      · rw [hDb.hd hvb' hb0]
        have hh := NF_add_head_le (S := S) hn
        rcases eq_or_lt_of_le hh with he | he
        · rw [Term.eq_of_val_eq S hnb.head hna he]
        · have hcb := CL_head hb hb0
          exact (hMs _ _ (by have := Term.size_head_le b; simp only [Term.size]; omega)
            (by simp only [Term.size]; omega) hcb ha he).le
    have hEt : Ex S σ m n (.add a b) = Tm.add (Ex S σ m n a) (Ex S σ m n b) := by
      have hea' : EL S σ (kA S m n) a = th (lvl (Term.val S a)) ea := hea
      have hEb0' : EL S σ (kA S m n) b ≠ par 0 := hEb0
      have hle' : hd σ (EL S σ (kA S m n) b) ≤ ev σ (EL S σ (kA S m n) a) := hle
      show EL S σ (kA S m n) (.add a b) = Tm.add (EL S σ (kA S m n) a) (EL S σ (kA S m n) b)
      rw [EL_add hv, hea']
      rw [hea'] at hle'
      simp only [plus, hEb0', if_false, if_pos hle']
    have hnfa : NF σ (th (lvl (Term.val S a)) ea) := hea ▸ hDa.nf
    have hnf : NF σ (Ex S σ m n (.add a b)) := by
      rw [hEt, hea]; exact NF.cadd hnfa hDb.nf hEb0 (hea ▸ hle)
    have hlt_a : Term.val S a < OmT 1 (lvl (Term.val S a) + 1) := lvl_lt (CL_val_lt hσ ha)
    have hlvt : lvl (Term.val S (.add a b)) = lvl (Term.val S a) := by
      refine le_antisymm (lvl_le_of_lt ?_) (lvl_mono hvω (val_le_add_left a b))
      exact val_lt_of_head hn (OmT_succ_principal 1 _) hlt_a
    have hev : ev σ (Ex S σ m n (.add a b)) = ev σ (Ex S σ m n a) + ev σ (Ex S σ m n b) := by
      rw [hEt]; rfl
    have hltE : ev σ (Ex S σ m n (.add a b)) < OmT σ (lvl (Term.val S (.add a b)) + 1) := by
      rw [hev, hlvt]
      refine OmT_succ_principal σ _ hDa.lt (lt_of_lt_of_le hDb.lt (OmT_mono hσ ?_))
      have := lvl_mono hvω (val_le_add_right a b); omega
    refine { nf := hnf, lt := hltE, ne := fun _ => ?_, ge := fun _ => ?_,
             prin := fun h => by simp [Term.isPrin, Term.isSC] at h,
             hd := fun _ _ => (by rw [hEt]; rfl), add := fun a' b' h _ => (by cases h; exact hEt),
             lv := ?_ }
    · rw [hev]
      exact (lt_of_lt_of_le (lt_of_lt_of_le hσ.pos (hDa.ge hva)) le_self_add).ne'
    · rw [hev]; exact (hDa.ge hva).trans le_self_add
    · rw [hlvt]
      refine le_antisymm ?_ ?_
      · rw [← hlvt]; exact lvl_le_of_lt (by rw [← OmT_succ_indep σ]; exact hltE)
      · rw [← hDa.lv]
        exact lvl_mono ((hltE.trans (OmT_succ_lt_Om_omega σ _))) (by rw [hev]; exact le_self_add)
  | @phi x y hn hv hx hy =>
    have hDx := hDs x (by simp only [Term.size]; omega) hx
    have hDy := hDs y (by simp only [Term.size]; omega) hy
    obtain ⟨vx, vy⟩ := NF_phi_lt (S := S) hn
    set k := lvl (Term.val S (.phi x y)) with hkdef
    have hvω := hvω0
    have hxk : ev σ (Ex S σ m n x) < OmT σ (k + 1) :=
      lt_of_lt_of_le hDx.lt (OmT_mono hσ (by have := lvl_mono hvω vx.le; omega))
    have hyk : ev σ (Ex S σ m n y) < OmT σ (k + 1) :=
      lt_of_lt_of_le hDy.lt (OmT_mono hσ (by have := lvl_mono hvω vy.le; omega))
    have hcode := gNF_codephi hσ hDx.nf hDy.nf hxk
    have hdom : Dom σ k (ev σ (plus σ (th (k + 1) (Ex S σ m n x)) (Ex S σ m n y))) := by
      refine (W25_lem213 hσ hcode k).2 fun p hp => ?_
      have := gKst_codephi_top hσ hDx.nf hDy.nf hxk hyk hp
      simp at this; subst this
      rw [gev_codephi hσ hDx.nf hDy.nf hxk]
      have hd' : Dom σ (k + 1) (ev σ (Ex S σ m n x)) :=
        dom_of_lt hσ (hxk.trans (OmT_lt_succ hσ _))
      exact lt_of_lt_of_le (lt_of_lt_of_le hxk (OmT_le_thb hσ hd')) le_self_add
    have e : Ex S σ m n (.phi x y) = th k (plus σ (th (k + 1) (Ex S σ m n x)) (Ex S σ m n y)) := by
      rw [Ex, EL_phi hv]
    have hnf : NF σ (Ex S σ m n (.phi x y)) := by rw [e]; exact NF.cth hcode hdom
    have hb := NF.th_bounds hσ (e ▸ hnf)
    refine { nf := hnf, lt := (by rw [e]; exact hb.2), ne := fun _ => (by rw [e]; exact (thb_pos hσ hdom).ne'),
             ge := fun _ => (by rw [e]; exact (OmT_zero_le hσ k).trans hb.1),
             prin := fun _ _ => ⟨(by rw [e]; exact hb.1), _, e⟩,
             hd := fun _ _ => (by show hd σ (Ex S σ m n (.phi x y)) = ev σ (Ex S σ m n (.phi x y)); rw [e]; rfl),
             add := fun a b h => (by cases h), lv := (by rw [e]; exact lvl_of_bounds_σ hσ hb.1 hb.2) }
  | @om b k hn hv hk0 hk =>
    have e : Ex S σ m n (.om b) = Omk k := by rw [Ex, EL_om hv, hk, natOf_nat]
    have hv' : Term.val S (.om b) = OmT σ k := by rw [val_om_of_Cw hk, OmT_pos_of_ne hk0]
    have hl : lvl (Term.val S (.om b)) = k := by
      rw [hv']; exact lvl_of_bounds_σ hσ le_rfl (OmT_lt_succ hσ k)
    refine { nf := (by rw [e]; exact gNF_Omk hσ k),
             lt := (by rw [e, gev_Omk hσ, hl]; exact OmT_lt_succ hσ k),
             ne := fun _ => (by rw [e, gev_Omk hσ]; exact (OmT_pos hσ k).ne'),
             ge := fun _ => (by rw [e, gev_Omk hσ]; exact OmT_zero_le hσ k),
             prin := fun _ _ => ⟨(by rw [e, gev_Omk hσ, hl]), par 0, (by rw [e, hl]; rfl)⟩,
             hd := fun _ _ => (by show hd σ (Ex S σ m n (.om b)) = ev σ (Ex S σ m n (.om b)); rw [e]; rfl),
             add := fun a b h => (by cases h),
             lv := (by rw [e, gev_Omk hσ, hl]; exact lvl_of_bounds_σ hσ le_rfl (OmT_lt_succ hσ k)) }
  | @psiS s c k hn hv hk0 hk hcω hcc =>
    have hl : lvl (Term.val S (.psiS s c)) = k := lvl_psiS s c hk
    have hsc : c.size < (Term.psiS s c).size := by simp only [Term.size]; omega
    have hDc := hDs c hsc hcc
    have hEcω : ev σ (Ex S σ m n c) < Om (ω : Ordinal.{0}) := hDc.lt.trans (OmT_succ_lt_Om_omega σ _)
    have hcode := gNF_codepsi (k := k) hσ hDc.nf hEcω
    have hcpos : ev σ (Pk k) ≤ ev σ (plus σ (Pk k) (gFc σ (Ex S σ m n c))) := by
      rw [gev_codepsi hσ hDc.nf hEcω]; exact le_self_add
    have hFle : ev σ (gFc σ (Ex S σ m n c)) ≤ ev σ (plus σ (Pk k) (gFc σ (Ex S σ m n c))) := by
      rw [gev_codepsi hσ hDc.nf hEcω]; exact le_add_self
    have hPpos : 0 < ev σ (Pk k) := lt_of_le_of_lt zero_le (gev_Pk_bounds hσ k).1
    have hdom : Dom σ k (ev σ (plus σ (Pk k) (gFc σ (Ex S σ m n c)))) := by
      refine (W25_lem213 hσ hcode k).2 fun p hp => ?_
      rcases List.mem_append.1 (Kst_plus σ (k + 1) _ _ hp) with h | h
      · rw [Kst_Pk le_rfl] at h
        simp at h
        rcases h with rfl | rfl
        · rw [gev_Omk hσ]; exact lt_of_lt_of_le (gev_Pk_bounds hσ k).1 hcpos
        · exact lt_of_lt_of_le hPpos hcpos
      · by_cases hc0 : ev σ (Ex S σ m n c) = 0
        · rw [gFc_zero hσ hc0] at h; simp [Kst] at h
        have h' := gKst_Fc hσ hc0 h
        split_ifs at h' with g
        · simp at h'
        rcases List.mem_cons.1 h' with h' | h'
        · subst h'; exact lt_of_lt_of_le (gev_Fc_pos hσ hDc.nf hEcω hc0).1 hFle
        · rcases List.mem_append.1 h' with h' | h'
          · rw [Kst_Omk (by omega)] at h'; simp at h'; subst h'; exact lt_of_lt_of_le hPpos hcpos
          · rcases List.mem_append.1 h' with h' | h'
            · rw [Kst_Omk (by omega)] at h'; simp at h'; subst h'; exact lt_of_lt_of_le hPpos hcpos
            · refine lt_of_lt_of_le ?_ hFle
              exact QBs hσ hn hk0 hk hcω (fun u hu hcu => hDs u (lt_of_le_of_lt hu hsc) hcu)
                (fun x hx hcx hlt => hMs x c (hx.trans hsc) hsc hcx hcc hlt) hcc hc0
                c hcc le_rfl hn.2.2 le_rfl p h'
    have hnat : natOf (Term.val S s) ≠ 0 := by rw [hk, natOf_nat]; exact hk0
    have e : Ex S σ m n (.psiS s c) = th k (plus σ (Pk k) (gFc σ (Ex S σ m n c))) := by
      rw [Ex, EL_psiS hv hnat, hk, natOf_nat]
    have hnf : NF σ (Ex S σ m n (.psiS s c)) := by rw [e]; exact NF.cth hcode hdom
    have hb := NF.th_bounds hσ (e ▸ hnf)
    refine { nf := hnf, lt := (by rw [e, hl]; exact hb.2),
             ne := fun _ => (by rw [e]; exact (thb_pos hσ hdom).ne'),
             ge := fun _ => (by rw [e]; exact (OmT_zero_le hσ k).trans hb.1),
             prin := fun _ _ => ⟨(by rw [e, hl]; exact hb.1), _, (by rw [e, hl])⟩,
             hd := fun _ _ => (by show hd σ (Ex S σ m n (.psiS s c)) = ev σ (Ex S σ m n (.psiS s c)); rw [e]; rfl),
             add := fun a b h => (by cases h),
             lv := (by rw [e, hl]; exact lvl_of_bounds_σ hσ hb.1 hb.2) }
  | @psiA s c hn hv hs0 hnz hcv hzθ hcz =>
    set ζ := dropT (kA S m n) c with hζdef
    have hsz : ζ.size < (Term.psiS s c).size := by
      have := dropT_size (kA S m n) c; rw [← hζdef] at this; simp only [Term.size]; omega
    have hDz := hDs ζ hsz hcz
    have hEzω : ev σ (Ex S σ m n ζ) < Om (ω : Ordinal.{0}) := hDz.lt.trans (OmT_succ_lt_Om_omega σ _)
    have hzΩ2 : Term.val S ζ < Om ((1 : Ordinal.{0}) + 1) := hzθ.trans th_lt_Om2
    have hval0 : Term.val S (.psiS s c) < Om (1 : Ordinal.{0}) := by
      have := (Term.val_psiS_bounds S s c).2; rwa [hs0, zero_add] at this
    have hl0 : lvl (Term.val S (.psiS s c)) = 0 := lvl_zero_of_lt_Om1 hval0
    -- the anchor of `G` and the class of its argument
    have anchor : ∀ {s1 d : Term}, Term.psiS s1 d ∈ topAtoms ζ → Term.val S s1 = 1 →
        CL S σ m n d ∧ Term.NF (.psiS s1 d) ∧ Term.val S d < Om (ω : Ordinal.{0}) ∧
          (Term.psiS s1 d).size ≤ ζ.size := by
      intro s1 d hm hs1
      have hge : ¬ Term.val S (.psiS s1 d) < σ := by
        intro h
        have := (Term.val_psiS_bounds S s1 d).1
        rw [hs1] at this
        exact absurd (this.trans h) (not_lt.2 (hσ.lt_Om1.le))
      have hca := CL_topAtom hcz hm hge
      cases hca with
      | par _ h => exact absurd h hge
      | psiS hn' _ _ _ hdω hdc => exact ⟨hdc, hn', hdω, topAtoms_size hm⟩
      | psiA _ _ h0 _ _ _ _ => rw [hs1] at h0; exact absurd h0 one_ne_zero
    -- `G`
    set G := GcT S σ (EL S σ (kA S m n)) (pmax S ζ) with hGdef
    have hG : NF σ G ∧ ev σ (Pk 1) ≤ ev σ G ∧
        (∀ p ∈ Kst 1 G, ev σ p.2 < ev σ G) ∧
        (∀ s1 d', Term.psiS s1 d' ∈ topAtoms ζ → Term.val S s1 = 1 →
          ev σ (gFc σ (Ex S σ m n d')) ≤ ev σ G ∧
          ∀ p ∈ Kst 1 (Ex S σ m n d'), ev σ p.2 < ev σ G) := by
      rcases hpm : pmax S ζ with _ | u
      · have hG1 : G = Pk 1 := by rw [hGdef, hpm]; rfl
        refine ⟨by rw [hG1]; exact gNF_Pk hσ 1, by rw [hG1], fun p hp => ?_, fun s1 d' hm hs1 => ?_⟩
        · rw [hG1, Kst_Pk (by omega)] at hp
          simp at hp
          rcases hp with rfl | rfl
          · rw [gev_Omk hσ, hG1]; exact (gev_Pk_bounds hσ 1).1
          · rw [hG1]; exact lt_of_le_of_lt zero_le (gev_Pk_bounds hσ 1).1
        · exact absurd ⟨s1, d', rfl, hs1⟩ ((pmaxL_spec (S := S) (topAtoms ζ)).1 hpm _ hm)
      · obtain ⟨hu1, ⟨s1, d, rfl, hs1⟩, hmax⟩ := (pmaxL_spec (S := S) (topAtoms ζ)).2 _ hpm
        obtain ⟨hdc, hnu, hdω, hus⟩ := anchor hu1 hs1
        have hdsz : d.size < ζ.size := by simp [Term.size] at hus; omega
        have hDd := hDs d (hdsz.trans hsz) hdc
        have hEdω : ev σ (Ex S σ m n d) < Om (ω : Ordinal.{0}) := hDd.lt.trans (OmT_succ_lt_Om_omega σ _)
        have hGe : G = GT σ (Ex S σ m n d) := by
          rw [hGdef, hpm, GcT_some]; rw [← Gd_eq hDd]; rfl
        have hQ1 : ∀ p ∈ Kst 1 (Ex S σ m n d), ev σ p.2 < ev σ (GT σ (Ex S σ m n d)) :=
          Q1s hσ _ s1 d le_rfl hnu hs1 hdω (fun u hu hcu => hDs u (lt_of_le_of_lt hu (hdsz.trans hsz)) hcu)
            (fun x y hx hy hcx hcy hxy => hMs x y (lt_of_le_of_lt hx (hdsz.trans hsz))
              (lt_of_le_of_lt hy (hdsz.trans hsz)) hcx hcy hxy) hdc d hdc le_rfl hnu.2.2 le_rfl
        rw [hGe]
        refine ⟨GT_NF hσ hDd.nf hEdω, (Pk_lt_GT hσ hDd.nf hEdω (le_max_right _ _)).le, fun p hp => ?_,
          fun s1' d' hm hs1' => ?_⟩
        · unfold GT at hp
          simp only [Kst, show ¬ (max (lvl (ev σ (Ex S σ m n d))) 1 + 1 < 1) by omega, if_false] at hp
          rcases List.mem_cons.1 hp with hp | hp
          · subst hp; exact (GT_bounds hσ hDd.nf hEdω).1
          · unfold gFarg at hp
            rcases List.mem_append.1 (Kst_plus σ 1 _ _ hp) with h | h
            · rw [Kst_Omk (by omega)] at h; simp at h; subst h; exact GT_pos hσ hDd.nf hEdω
            · rcases List.mem_append.1 (Kst_plus σ 1 _ _ h) with h | h
              · rw [Kst_Omk (by omega)] at h; simp at h; subst h; exact GT_pos hσ hDd.nf hEdω
              · exact hQ1 p h
        · obtain ⟨hdc', hnu', hdω', hus'⟩ := anchor hm hs1'
          have hdsz' : d'.size < ζ.size := by simp [Term.size] at hus'; omega
          have hDd' := hDs d' (hdsz'.trans hsz) hdc'
          have hEdω' : ev σ (Ex S σ m n d') < Om (ω : Ordinal.{0}) :=
            hDd'.lt.trans (OmT_succ_lt_Om_omega σ _)
          -- `d' ≤ d`
          have hvd : Term.val S d' ≤ Term.val S d := by
            have h1 := hmax _ hm ⟨s1', d', rfl, hs1'⟩
            by_contra hlt; rw [not_le] at hlt
            have hsem := (Term.sem_of_NF (S := S) hnu).2.2
            have := psi_lt_psi (S := S) (InR_Om_succ (Term.val S s1)) hlt hsem
            simp only [Term.val] at h1
            rw [hs1, hs1'] at h1
            rw [hs1] at this
            exact absurd h1 (not_le.2 this)
          have hGle : ev σ (GT σ (Ex S σ m n d')) ≤ ev σ (GT σ (Ex S σ m n d)) := by
            rcases eq_or_lt_of_le hvd with he | he
            · rw [Term.eq_of_val_eq S hnu'.2.1 hnu.2.1 he]
            · exact (GT_lt hσ hDd'.nf hDd.nf hEdω (hMs d' d (hdsz'.trans hsz) (hdsz.trans hsz) hdc' hdc he)).le
          refine ⟨(Fc_le_GT hσ hDd'.nf hEdω').trans hGle, fun p hp => ?_⟩
          have := Q1s hσ _ s1' d' le_rfl hnu' hs1' hdω'
            (fun u hu hcu => hDs u (lt_of_le_of_lt hu (hdsz'.trans hsz)) hcu)
            (fun x y hx hy hcx hcy hxy => hMs x y (lt_of_le_of_lt hx (hdsz'.trans hsz))
              (lt_of_le_of_lt hy (hdsz'.trans hsz)) hcx hcy hxy) hdc' d' hdc' le_rfl hnu'.2.2 le_rfl p hp
          exact this.trans_le hGle
    obtain ⟨hGnf, hGP1, hGK, hGat⟩ := hG
    have hcode : NF σ (plus σ G (Ex S σ m n ζ)) := NF_plus hσ hGnf hDz.nf
    have hY : ev σ (plus σ G (Ex S σ m n ζ)) = ev σ G + ev σ (Ex S σ m n ζ) := ev_plus hσ hGnf hDz.nf
    have hGpos : 0 < ev σ G := lt_of_lt_of_le (lt_of_le_of_lt zero_le (gev_Pk_bounds hσ 1).1) hGP1
    have hGth : ∃ j e, G = th j e := by
      rw [hGdef]; rcases pmax S ζ with _ | u
      · exact ⟨2, Omk 2, rfl⟩
      · cases u <;> first | exact ⟨_, _, rfl⟩
    obtain ⟨jG, eG, hGe⟩ := hGth
    have hGP : IsPrincipal (· + ·) (ev σ G) := by
      rw [hGe] at hGnf ⊢; exact NF.th_principal hσ hGnf
    have hdom : Dom σ 0 (ev σ (plus σ G (Ex S σ m n ζ))) := by
      refine (W25_lem213 hσ hcode 0).2 fun p hp => ?_
      rw [hY]
      rcases List.mem_append.1 (Kst_plus σ 1 _ _ hp) with h | h
      · exact lt_of_lt_of_le (hGK p h) le_self_add
      · refine Zbound (ζ := ζ) hσ (hGP1.trans le_self_add) (fun u hu hcu => hDs u (lt_of_le_of_lt hu hsz) hcu)
          (fun s1 d' hm hs1 => ?_) ζ hcz le_rfl (fun a ha => ha) hzΩ2 p h
        obtain ⟨hle, hK⟩ := hGat s1 d' hm hs1
        have hpos : 0 < ev σ (Ex S σ m n ζ) := by
          have hv0 : Term.val S ζ ≠ 0 := by
            have := topAtom_le (S := S) hnz hm
            have h2 := (Term.val_psiS_bounds S s1 d').1
            exact (lt_of_lt_of_le (lt_of_le_of_lt zero_le h2) this).ne'
          exact pos_iff_ne_zero.2 (hDz.ne hv0)
        obtain ⟨hdc', hnu', hdω', hus'⟩ := anchor hm hs1
        have hDd' := hDs d' (lt_of_le_of_lt (by simp [Term.size] at hus'; omega) hsz) hdc'
        have hEdω' : ev σ (Ex S σ m n d') < Om (ω : Ordinal.{0}) :=
          hDd'.lt.trans (OmT_succ_lt_Om_omega σ _)
        have hP1G : ev σ (Pk 1) < ev σ G := by
          rcases eq_or_lt_of_le hGP1 with he | he
          · -- `G = P₁` only for `pmax = none`, impossible here
            exfalso
            rcases hpm : pmax S ζ with _ | u
            · exact absurd ⟨s1, d', rfl, hs1⟩ ((pmaxL_spec (S := S) (topAtoms ζ)).1 hpm _ hm)
            · obtain ⟨hu1, ⟨s2, d2, rfl, hs2⟩, _⟩ := (pmaxL_spec (S := S) (topAtoms ζ)).2 _ hpm
              obtain ⟨hdc2, hnu2, hdω2, hus2⟩ := anchor hu1 hs2
              have hD2 := hDs d2 (lt_of_le_of_lt (by simp [Term.size] at hus2; omega) hsz) hdc2
              have hE2 : ev σ (Ex S σ m n d2) < Om (ω : Ordinal.{0}) := hD2.lt.trans (OmT_succ_lt_Om_omega σ _)
              have hGe : G = GT σ (Ex S σ m n d2) := by rw [hGdef, hpm, GcT_some]; rw [← Gd_eq hD2]; rfl
              rw [hGe] at he
              exact absurd he (Pk_lt_GT hσ hD2.nf hE2 (le_max_right _ _)).ne
          · exact he
        refine ⟨?_, fun p hp => ?_⟩
        · rw [ev_plus hσ (gNF_Pk hσ 1) (gNF_Fc hσ hDd'.nf hEdω')]
          rcases eq_or_lt_of_le hle with he | he
          · rw [he, hGP.add_eq_right hP1G]; exact lt_add_of_pos_right _ hpos
          · exact lt_of_lt_of_le (hGP hP1G he) le_self_add
        · by_cases hc0 : ev σ (Ex S σ m n d') = 0
          · rw [gFc_zero hσ hc0] at hp; simp [Kst] at hp
          have h' := gKst_Fc hσ hc0 hp
          split_ifs at h' with g
          · simp at h'
          rcases List.mem_cons.1 h' with h' | h'
          · subst h'
            exact lt_of_lt_of_le ((gev_Fc_pos hσ hDd'.nf hEdω' hc0).1.trans_le hle) le_self_add
          · rcases List.mem_append.1 h' with h' | h'
            · rw [Kst_Omk (by omega)] at h'; simp at h'; subst h'
              exact lt_of_lt_of_le hGpos le_self_add
            · rcases List.mem_append.1 h' with h' | h'
              · rw [Kst_Omk (by omega)] at h'; simp at h'; subst h'
                exact lt_of_lt_of_le hGpos le_self_add
              · exact lt_of_lt_of_le (hK p h') le_self_add
    have hnat : natOf (Term.val S s) = 0 := by rw [hs0]; exact natOf_nat 0
    have e : Ex S σ m n (.psiS s c) = th 0 (plus σ G (Ex S σ m n ζ)) := by
      rw [Ex, EL_psi0 hv hnat]
    have hnf : NF σ (Ex S σ m n (.psiS s c)) := by rw [e]; exact NF.cth hcode hdom
    have hb := NF.th_bounds hσ (e ▸ hnf)
    refine { nf := hnf, lt := (by rw [e, hl0]; exact hb.2),
             ne := fun _ => (by rw [e]; exact (thb_pos hσ hdom).ne'),
             ge := fun _ => (by rw [e]; exact (OmT_zero_le hσ 0).trans hb.1),
             prin := fun _ _ => ⟨(by rw [e, hl0]; exact hb.1), _, (by rw [e, hl0])⟩,
             hd := fun _ _ => (by show hd σ (Ex S σ m n (.psiS s c)) = ev σ (Ex S σ m n (.psiS s c)); rw [e]; rfl),
             add := fun a b h => (by cases h),
             lv := (by rw [e, hl0]; exact lvl_of_bounds_σ hσ hb.1 hb.2) }

end Googology.Trans.PoR.InaccPsi.R2.Br

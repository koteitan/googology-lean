import Googology.Trans.PoR.InaccPsi.R2.BrLow3

/-!
# Lower bound, part 4: Lemma D and Lemma M for `E`, and Theorem LOW-0

* `KB`: the level-`k` parts of `E(a)` for a normal `ψ_{Ω_{k+1}}(a)` are below a bound `Y`, given the bound
  for the images of the level-`k` principal terms below `ψ_{Ω_{k+1}}(a)` and for the level-`k` codes `F`;
* `D_step` (Lemma D): `E(t)` is a normal term of `T̄¹` with the right level, given Lemma M on smaller terms;
* `PM_low`, `M_step_low` (Lemma M): `E` is strictly increasing on the normal forms of the class;
* `E_main`: both, for all sizes;
* `psi_le_ups_one` (**Theorem LOW-0**): `ψ_{Ω₁}(Ω_ω) ≤ υ₁`, and `ups_one_eq`: `υ₁ = ψ_{Ω₁}(Ω_ω)`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Br

open Ordinal Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq Tm

variable {S : InaccSeq.{0}}

theorem Ki_Pk_of_lt {k j : ℕ} (h : k < j + 1) : Ki k (Pk j) = [] := by
  simp [Pk, Omk, Ki, show ¬ j + 1 < k by omega, show j + 1 ≠ k by omega]

theorem ev_par0 : ev 1 (par 0) = 0 := rfl

theorem E_ne_par0 {t : Term} (hD : DI S t) (hv : Term.val S t ≠ 0) : E S t ≠ par 0 := by
  intro e; have := hD.ne hv; rw [e] at this; exact this rfl

/-! ## Lemma KB -/

/-- **The level-`k` parts of `E(a)`** for a normal `μ = ψ_{Ω_{k+1}}(a)`, visited from `μ`, are below `Y`. -/
theorem KB {s a : Term} (hμ : Term.NF (.psiS s a)) {k : ℕ} (hk : Term.val S s = k) (Y : Ordinal.{0})
    (hD : ∀ u : Term, u.size ≤ a.size → Cw S u → Term.NF u → DI S u)
    (hO1 : ∀ r : Term, r.size ≤ a.size → Term.NF r → Cw S r → r.isPrin = true →
      lvl (Term.val S r) = k → Term.val S r < Term.val S (.psiS s a) → ev 1 (E S r) < Y)
    (hO2 : ∀ x : Tm, NF 1 x → ev 1 x < Om (ω : Ordinal.{0}) → ev 1 x ≠ 0 → lvl (ev 1 x) + 1 = k →
      ev 1 (Fc x) < Y) :
    ∀ u : Term, u.size ≤ a.size → Term.NF u → Cw S u → Term.KLt (.psiS s a) u a →
      ∀ v ∈ Ki k (E S u), ev 1 v < Y := by
  have hpb : ∀ r : Term, Term.NF r → Cw S r → r.isPrin = true → lvl (Term.val S r) = k →
      Term.KLt (.psiS s a) r a → Term.val S r < Term.val S (.psiS s a) :=
    fun r hr hc hp hl hK => parts_b hμ hk r.size r le_rfl hr hc hp hl hK
  intro u
  induction u with
  | zero => intro _ _ _ _ v hv; simp [E, Ki] at hv
  | inacc _ => intro _ _ hc; exact absurd hc (by simp [Cw])
  | inaccW => intro _ _ hc; exact absurd hc (by simp [Cw])
  | psiI _ _ _ => intro _ _ hc; exact absurd hc (by simp [Cw])
  | add x y ihx ihy =>
    intro hs hn hc hK v hv
    rcases List.mem_append.1 (Ki_plus 1 k _ _ hv) with h | h
    · exact ihx (by simp [Term.size] at hs; omega) hn.1 hc.1 hK.1 v h
    · exact ihy (by simp [Term.size] at hs; omega) hn.2.1 hc.2 hK.2 v h
  | om b _ =>
    intro hs hn hc hK v hv
    have hl : natOf (Term.val S b) = lvl (Term.val S (.om b)) := natOf_om hc
    simp only [E, Omk, Ki] at hv
    split_ifs at hv with h1 h2
    · simp at hv
    · simp at hv; subst hv
      have e : E S (.om b) = th (natOf (Term.val S b)) (par 0) := rfl
      rw [← e]
      exact hO1 _ hs hn hc rfl (hl ▸ h2) (hpb _ hn hc rfl (hl ▸ h2) hK)
    · simp at hv
  | phi x y ihx ihy =>
    intro hs hn hc hK v hv
    have hDx := hD x (by simp [Term.size] at hs; omega) hc.1 hn.1
    have hDy := hD y (by simp [Term.size] at hs; omega) hc.2 hn.2.1
    obtain ⟨hx, hy⟩ := NF_phi_lt (S := S) hn
    set j := lvl (Term.val S (.phi x y)) with hjdef
    have hvω := Cw_val_lt hc hn
    have hxk : ev 1 (E S x) < OmT 1 (j + 1) :=
      lt_of_lt_of_le hDx.lt (OmT_mono base_one (by have := lvl_mono hvω hx.le; omega))
    have hyk : ev 1 (E S y) < OmT 1 (j + 1) :=
      lt_of_lt_of_le hDy.lt (OmT_mono base_one (by have := lvl_mono hvω hy.le; omega))
    have e : E S (.phi x y) = th j (plus 1 (th (j + 1) (E S x)) (E S y)) := rfl
    rw [e] at hv
    simp only [Ki] at hv
    split_ifs at hv with h1 h2
    · simp at hv
    · simp at hv; subst hv
      rw [← e]
      exact hO1 _ hs hn hc rfl h2 (hpb _ hn hc rfl h2 hK)
    · rcases List.mem_append.1 (Ki_plus 1 k _ _ hv) with h | h
      · simp only [Ki, show ¬ j + 1 < k by omega, show j + 1 ≠ k by omega, if_false] at h
        exact ihx (by simp [Term.size] at hs; omega) hn.1 hc.1 hK.1 v h
      · exact ihy (by simp [Term.size] at hs; omega) hn.2.1 hc.2 hK.2 v h
  | psiS s' c _ ihc =>
    intro hs hn hc hK v hv
    have hl : natOf (Term.val S s') = lvl (Term.val S (.psiS s' c)) := natOf_psiS hc
    obtain ⟨⟨j, hj⟩, hcω, hcc⟩ := hc
    have hc' : Cw S (.psiS s' c) := ⟨⟨j, hj⟩, hcω, hcc⟩
    have e : E S (.psiS s' c) = th j (plus 1 (Pk j) (Fc (E S c))) := by
      simp only [E]; rw [hj, natOf_nat]
    rw [hj, natOf_nat] at hl
    rw [e] at hv
    simp only [Ki] at hv
    split_ifs at hv with h1 h2
    · simp at hv
    · simp at hv; subst hv
      rw [← e]
      exact hO1 _ hs hn hc' rfl (hl ▸ h2) (hpb _ hn hc' rfl (hl ▸ h2) hK)
    · have hjk : k < j := by omega
      rcases hK with hK | ⟨hca, _, hKc⟩
      · exfalso
        have h1' := (Term.cmp_lt_iff S hn hμ).1 hK
        have h2' := (psiS_bounds_nat s' c hj).1
        have h3' := (psiS_bounds_nat s a hk).2
        have h4' : OmT 1 (k + 1) ≤ Om (j : Ordinal.{0}) := by
          rw [Om_nat_eq_OmT (by omega)]; exact OmT_mono base_one (by omega)
        exact absurd h1' (not_lt.2 (h3'.le.trans (h4'.trans h2'.le)))
      have hsc : c.size ≤ a.size := by simp [Term.size] at hs; omega
      have hDc := hD c hsc hcc hn.2.1
      have hEcω : ev 1 (E S c) < Om (ω : Ordinal.{0}) := hDc.lt.trans (OmT_succ_lt_Om_omega 1 _)
      rcases List.mem_append.1 (Ki_plus 1 k _ _ hv) with h | h
      · rw [Ki_Pk_of_lt (by omega)] at h; simp at h
      · by_cases hc0 : ev 1 (E S c) = 0
        · rw [Fc_zero hc0] at h; simp [Ki] at h
        have h' := Ki_Fc hc0 h
        split_ifs at h' with g1 g2
        · simp at h'
        · simp at h'; subst h'; exact hO2 _ hDc.nf hEcω hc0 g2
        · exact ihc (by simp [Term.size] at hs; omega) hn.2.1 hcc hKc v h'

/-! ## Lemma D -/

theorem lvl_of_th_bounds {j : ℕ} {v : Ordinal.{0}} (h1 : OmT 1 j ≤ v) (h2 : v < OmT 1 (j + 1)) :
    lvl v = j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have := lvl_le_of_lt h2; omega
  · exact lvl_eq h1 h2 hj.ne'

/-- **Lemma D**: the invariants of `E(t)`, given them and Lemma M on smaller terms. -/
theorem D_step {t : Term} (ht : Term.NF t) (hc : Cw S t)
    (hDs : ∀ u : Term, u.size < t.size → Cw S u → Term.NF u → DI S u)
    (hMs : ∀ x y : Term, x.size < t.size → y.size < t.size → Cw S x → Cw S y → Term.NF x →
      Term.NF y → Term.val S x < Term.val S y → ev 1 (E S x) < ev 1 (E S y)) : DI S t := by
  cases t with
  | zero =>
    exact { nf := NF_par0, lt := OmT_succ_pos 1 _, ne := fun h => absurd rfl h,
            prin := fun h => (by simp [Term.isPrin, Term.isSC] at h),
            hd := fun h => absurd rfl h, add := fun a b h => (by cases h), lv := rfl }
  | inacc _ => exact absurd hc (by simp [Cw])
  | inaccW => exact absurd hc (by simp [Cw])
  | psiI _ _ => exact absurd hc (by simp [Cw])
  | add a b =>
    obtain ⟨hna, hnb, hpa, hb0, _⟩ := ht
    have hDa := hDs a (by simp only [Term.size]; omega) hc.1 hna
    have hDb := hDs b (by simp only [Term.size]; omega) hc.2 hnb
    obtain ⟨hla, ⟨ea, hea⟩⟩ := hDa.prin hpa
    have hvb : Term.val S b ≠ 0 := Term.val_ne_zero S hnb hb0
    have hEb0 : E S b ≠ par 0 := E_ne_par0 hDb hvb
    have hle : hd 1 (E S b) ≤ ev 1 (E S a) := by
      rw [hDb.hd hb0]
      have hh := NF_add_head_le (S := S) (show Term.NF (.add a b) from ⟨hna, hnb, hpa, hb0, ‹_›⟩)
      rcases eq_or_lt_of_le hh with he | he
      · rw [Term.eq_of_val_eq S hnb.head hna he]
      · exact (hMs _ _ (by have := Term.size_head_le b; simp [Term.size]; omega)
          (by simp only [Term.size]; omega) (Cw_head hc.2) hc.1 hnb.head hna he).le
    have hEt : E S (.add a b) = Tm.add (E S a) (E S b) := by
      show plus 1 (E S a) (E S b) = _
      rw [hea]
      simp only [plus, hEb0, if_false]
      rw [← hea, if_pos hle]
    have hnfa : NF 1 (th (lvl (Term.val S a)) ea) := hea ▸ hDa.nf
    have hnf : NF 1 (E S (.add a b)) := by
      rw [hEt, hea]; exact NF.cadd hnfa hDb.nf hEb0 (hea ▸ hle)
    have hn : Term.NF (.add a b) := ⟨hna, hnb, hpa, hb0, ‹_›⟩
    have hvω := Cw_val_lt hc hn
    have hlt_a : Term.val S a < OmT 1 (lvl (Term.val S a) + 1) := lvl_lt (Cw_val_lt hc.1 hna)
    have hlvt : lvl (Term.val S (.add a b)) = lvl (Term.val S a) := by
      refine le_antisymm (lvl_le_of_lt ?_) (lvl_mono hvω (val_le_add_left a b))
      exact val_lt_of_head hn (OmT_succ_principal 1 _) hlt_a
    have hev : ev 1 (E S (.add a b)) = ev 1 (E S a) + ev 1 (E S b) := by rw [hEt]; rfl
    have hltE : ev 1 (E S (.add a b)) < OmT 1 (lvl (Term.val S (.add a b)) + 1) := by
      rw [hev, hlvt]
      refine OmT_succ_principal 1 _ hDa.lt (lt_of_lt_of_le hDb.lt (OmT_mono base_one ?_))
      have := lvl_mono hvω (val_le_add_right a b); omega
    refine { nf := hnf, lt := hltE, ne := fun _ => ?_, prin := fun h => (by simp [Term.isPrin, Term.isSC] at h),
             hd := fun _ => (by rw [hEt]; rfl), add := fun a' b' h => (by cases h; exact hEt), lv := ?_ }
    · rw [hev]
      exact (lt_of_lt_of_le (pos_iff_ne_zero.2 (hDa.ne (Term.val_ne_zero S hna
        (Term.NF.ne_zero_of_isPrin hpa)))) le_self_add).ne'
    · rw [hlvt]
      refine le_antisymm ?_ ?_
      · rw [← hlvt]; exact lvl_le_of_lt hltE
      · rw [← hDa.lv]
        exact lvl_mono (hltE.trans (OmT_succ_lt_Om_omega 1 _)) (by rw [hev]; exact le_self_add)
  | phi x y =>
    have hDx := hDs x (by simp only [Term.size]; omega) hc.1 ht.1
    have hDy := hDs y (by simp only [Term.size]; omega) hc.2 ht.2.1
    obtain ⟨hx, hy⟩ := NF_phi_lt (S := S) ht
    set k := lvl (Term.val S (.phi x y)) with hkdef
    have hvω := Cw_val_lt hc ht
    have hxk : ev 1 (E S x) < OmT 1 (k + 1) :=
      lt_of_lt_of_le hDx.lt (OmT_mono base_one (by have := lvl_mono hvω hx.le; omega))
    have hyk : ev 1 (E S y) < OmT 1 (k + 1) :=
      lt_of_lt_of_le hDy.lt (OmT_mono base_one (by have := lvl_mono hvω hy.le; omega))
    have hcode := NF_codephi hDx.nf hDy.nf hxk
    have hdom : Dom 1 k (ev 1 (plus 1 (th (k + 1) (E S x)) (E S y))) := by
      refine (W25_lem213 base_one hcode k).2 fun p hp => ?_
      have := Kst_codephi_top hDx.nf hDy.nf hxk hyk hp
      simp at this; subst this
      rw [ev_codephi hDx.nf hDy.nf hxk]
      have hd' : Dom 1 (k + 1) (ev 1 (E S x)) :=
        dom_of_lt base_one (hxk.trans (OmT_lt_succ base_one _))
      exact lt_of_lt_of_le (lt_of_lt_of_le hxk (OmT_le_thb base_one hd')) le_self_add
    have e : E S (.phi x y) = th k (plus 1 (th (k + 1) (E S x)) (E S y)) := rfl
    have hnf : NF 1 (E S (.phi x y)) := by rw [e]; exact NF.cth hcode hdom
    have hb := NF.th_bounds base_one (e ▸ hnf)
    refine { nf := hnf, lt := (by rw [e]; exact hb.2), ne := fun _ => (by rw [e]; exact (thb_pos base_one hdom).ne'),
             prin := fun _ => ⟨(by rw [e]; exact hb.1), _, e⟩,
             hd := fun _ => (by show hd 1 (E S (.phi x y)) = ev 1 (E S (.phi x y)); rw [e]; rfl),
             add := fun a b h => (by cases h), lv := (by rw [e]; exact lvl_of_th_bounds hb.1 hb.2) }
  | om b =>
    obtain ⟨k, hk0, hk⟩ := hc
    have e : E S (.om b) = Omk k := by simp only [E]; rw [hk, natOf_nat]
    have hv : Term.val S (.om b) = OmT 1 k := by rw [val_om_of_Cw hk, Om_nat_eq_OmT hk0]
    have hl : lvl (Term.val S (.om b)) = k := by rw [hv]; exact lvl_of_th_bounds le_rfl (OmT_lt_succ base_one k)
    refine { nf := (by rw [e]; exact NF_Omk k), lt := (by rw [e, ev_Omk, hl]; exact OmT_lt_succ base_one k),
             ne := fun _ => (by rw [e, ev_Omk]; exact (OmT_pos base_one k).ne'),
             prin := fun _ => ⟨(by rw [e, ev_Omk, hl]), par 0, (by rw [e, hl]; rfl)⟩,
             hd := fun _ => (by show hd 1 (E S (.om b)) = ev 1 (E S (.om b)); rw [e]; rfl),
             add := fun a b h => (by cases h),
             lv := (by rw [e, ev_Omk, hl]; exact lvl_of_th_bounds le_rfl (OmT_lt_succ base_one k)) }
  | psiS s a =>
    obtain ⟨⟨k, hk⟩, haω, hca⟩ := hc
    have hc' : Cw S (.psiS s a) := ⟨⟨k, hk⟩, haω, hca⟩
    have hl : lvl (Term.val S (.psiS s a)) = k := lvl_psiS s a hk
    have hsa : a.size < (Term.psiS s a).size := by simp [Term.size]
    have hDa := hDs a hsa hca ht.2.1
    have hEaω : ev 1 (E S a) < Om (ω : Ordinal.{0}) := hDa.lt.trans (OmT_succ_lt_Om_omega 1 _)
    have hcode := NF_codepsi (k := k) hDa.nf hEaω
    have hcpos : ev 1 (Pk k) ≤ ev 1 (plus 1 (Pk k) (Fc (E S a))) := by
      rw [ev_codepsi hDa.nf hEaω]; exact le_self_add
    have hFle : ev 1 (Fc (E S a)) ≤ ev 1 (plus 1 (Pk k) (Fc (E S a))) := by
      rw [ev_codepsi hDa.nf hEaω]; exact le_add_self
    have hPpos : 0 < ev 1 (Pk k) := lt_of_le_of_lt zero_le (ev_Pk_bounds k).1
    have hdom : Dom 1 k (ev 1 (plus 1 (Pk k) (Fc (E S a)))) := by
      refine (W25_lem213 base_one hcode k).2 fun p hp => ?_
      rcases List.mem_append.1 (Kst_plus 1 (k + 1) _ _ hp) with h | h
      · rw [Kst_Pk le_rfl] at h
        simp at h
        rcases h with rfl | rfl
        · rw [ev_Omk]; exact lt_of_lt_of_le (ev_Pk_bounds k).1 hcpos
        · exact lt_of_lt_of_le hPpos hcpos
      · by_cases ha0 : ev 1 (E S a) = 0
        · rw [Fc_zero ha0] at h; simp [Kst] at h
        have h' := Kst_Fc ha0 h
        split_ifs at h' with g
        · simp at h'
        rcases List.mem_cons.1 h' with h' | h'
        · subst h'; exact lt_of_lt_of_le (ev_Fc_pos hDa.nf hEaω ha0).1 hFle
        · rcases List.mem_append.1 h' with h' | h'
          · rw [Kst_Omk (by omega)] at h'; simp at h'; subst h'; exact lt_of_lt_of_le hPpos hcpos
          · rcases List.mem_append.1 h' with h' | h'
            · rw [Kst_Omk (by omega)] at h'; simp at h'; subst h'; exact lt_of_lt_of_le hPpos hcpos
            · refine lt_of_lt_of_le ?_ hFle
              exact QB ht hk hca haω (fun u hu hcu hnu => hDs u (lt_of_le_of_lt hu hsa) hcu hnu)
                (fun c hc hcc hnc hlt => hMs c a (hc.trans hsa) hsa hcc hca hnc ht.2.1 hlt) ha0
                a le_rfl ht.2.1 hca ht.2.2 le_rfl p h'
    have e : E S (.psiS s a) = th k (plus 1 (Pk k) (Fc (E S a))) := by
      simp only [E]; rw [hk, natOf_nat]
    have hnf : NF 1 (E S (.psiS s a)) := by rw [e]; exact NF.cth hcode hdom
    have hb := NF.th_bounds base_one (e ▸ hnf)
    refine { nf := hnf, lt := (by rw [e, hl]; exact hb.2),
             ne := fun _ => (by rw [e]; exact (thb_pos base_one hdom).ne'),
             prin := fun _ => ⟨(by rw [e, hl]; exact hb.1), _, (by rw [e, hl])⟩,
             hd := fun _ => (by show hd 1 (E S (.psiS s a)) = ev 1 (E S (.psiS s a)); rw [e]; rfl),
             add := fun a b h => (by cases h),
             lv := (by rw [e, hl]; exact lvl_of_th_bounds hb.1 hb.2) }

end Googology.Trans.PoR.InaccPsi.R2.Br

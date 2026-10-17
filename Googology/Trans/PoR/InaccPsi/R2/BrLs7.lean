import Googology.Trans.PoR.InaccPsi.R2.BrLs6

/-!
# LOW-STEP, part 7: the code `G`, Lemma Q1, and the bound for the `A`-clause code

* `GT x = ϑ̄_{M+1}(Ω_{M+1}·2 + x)`, `M = max(lvl x, 1)`: normal form, value, `F(x) ≤ G(x)`, `G`
  strictly increasing (`GT_lt`), `P_j < G(x)` for `j ≤ M`;
* `Q1s` (**Lemma Q1**): for an anchor `ψ_{Ω₂}(d)` of the class, the `K*₁`-elements of `E(u)` for the parts
  `u` of `d` visited from the anchor are below `G(E d)` (a level-1 stop is a new anchor).
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Br

open Ordinal Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq Tm

variable {S : InaccSeq.{0}} {σ : Ordinal.{0}} {m n : ℕ}

/-- `G(x) = ϑ̄_{M+1}(Ω_{M+1}·2 + x)`, `M = max(lvl x, 1)`. -/
noncomputable def GT (σ : Ordinal.{0}) (x : Tm) : Tm :=
  th (max (lvl (ev σ x)) 1 + 1) (gFarg σ (max (lvl (ev σ x)) 1) x)

theorem GT_NF (hσ : Base σ) {x : Tm} (hx : NF σ x) (hxω : ev σ x < Om (ω : Ordinal.{0})) :
    NF σ (GT σ x) := by
  refine NF.cth (gNF_Farg hσ hx) (dom_of_lt hσ (gFarg_lt hσ hx ?_))
  exact (glvl_lt σ hxω).trans_le (OmT_mono hσ (by omega))

theorem GT_bounds (hσ : Base σ) {x : Tm} (hx : NF σ x) (hxω : ev σ x < Om (ω : Ordinal.{0})) :
    ev σ (gFarg σ (max (lvl (ev σ x)) 1) x) < ev σ (GT σ x) ∧
      OmT σ (max (lvl (ev σ x)) 1 + 1) ≤ ev σ (GT σ x) ∧
      ev σ (GT σ x) < OmT σ (max (lvl (ev σ x)) 1 + 2) ∧ IsPrincipal (· + ·) (ev σ (GT σ x)) := by
  have hn := GT_NF hσ hx hxω
  have hb := NF.th_bounds hσ hn
  refine ⟨thb_gt_arg hσ (NF.th_dom hn) (gFarg_lt hσ hx ?_), hb.1, hb.2, NF.th_principal hσ hn⟩
  exact (glvl_lt σ hxω).trans_le (OmT_mono hσ (by omega))

theorem OmT_lt_GT (hσ : Base σ) {x : Tm} (hx : NF σ x) (hxω : ev σ x < Om (ω : Ordinal.{0})) {j : ℕ}
    (hj : j ≤ max (lvl (ev σ x)) 1) : OmT σ (j + 1) < ev σ (GT σ x) :=
  lt_of_lt_of_le (lt_of_le_of_lt (OmT_mono hσ (by omega)) (gFarg_ge hσ hx))
    (GT_bounds hσ hx hxω).1.le

theorem Pk_lt_GT (hσ : Base σ) {x : Tm} (hx : NF σ x) (hxω : ev σ x < Om (ω : Ordinal.{0})) {j : ℕ}
    (hj : j ≤ max (lvl (ev σ x)) 1) : ev σ (Pk j) < ev σ (GT σ x) := by
  rcases lt_or_eq_of_le hj with hlt | heq
  · exact lt_of_lt_of_le (gev_Pk_bounds hσ j).2 ((OmT_mono hσ (by omega)).trans (GT_bounds hσ hx hxω).2.1)
  · have hn := GT_NF hσ hx hxω
    unfold GT at hn ⊢
    rw [← heq] at hn ⊢
    refine thb_lt_of_I hσ (gNF_Pk hσ _) hn ?_ ?_
    · rw [gev_Omk hσ]; exact gFarg_ge hσ hx
    · refine star_le_of σ (fun u hu => ?_) (thb_pos hσ (NF.th_dom hn))
      rw [Omk, Ki] at hu
      simp at hu
      subst hu
      have := (gFarg_ge (m := j) hσ hx).trans
        (thb_gt_arg hσ (NF.th_dom hn) (gFarg_lt hσ hx (by
          rw [heq]; exact (glvl_lt σ hxω).trans_le (OmT_mono hσ (by omega)))))
      rwa [← gev_Omk hσ] at this

/-- `F(x) ≤ G(x)`. -/
theorem Fc_le_GT (hσ : Base σ) {x : Tm} (hx : NF σ x) (hxω : ev σ x < Om (ω : Ordinal.{0})) :
    ev σ (gFc σ x) ≤ ev σ (GT σ x) := by
  by_cases h0 : ev σ x = 0
  · rw [gFc_zero hσ h0]; exact zero_le
  by_cases hl : 1 ≤ lvl (ev σ x)
  · have e : max (lvl (ev σ x)) 1 = lvl (ev σ x) := max_eq_left hl
    rw [gFc_pos hσ h0]; unfold GT; rw [e]
  · have hl0 : lvl (ev σ x) = 0 := by omega
    have := (gev_Fc_pos hσ hx hxω h0).2.2
    rw [hl0] at this
    exact (this.trans_le (by
      have := (GT_bounds hσ hx hxω).2.1
      rw [hl0] at this; simpa using this)).le

/-- **`G` is strictly increasing.** -/
theorem GT_lt (hσ : Base σ) {x y : Tm} (hx : NF σ x) (hy : NF σ y) (hyω : ev σ y < Om (ω : Ordinal.{0}))
    (hxy : ev σ x < ev σ y) : ev σ (GT σ x) < ev σ (GT σ y) := by
  have hxω := hxy.trans hyω
  have hm : max (lvl (ev σ x)) 1 ≤ max (lvl (ev σ y)) 1 := max_le_max (lvl_mono hyω hxy.le) le_rfl
  rcases lt_or_eq_of_le hm with hlt | heq
  · exact lt_of_lt_of_le (GT_bounds hσ hx hxω).2.2.1
      ((OmT_mono hσ (by omega)).trans (GT_bounds hσ hy hyω).2.1)
  · have hnx := GT_NF hσ hx hxω
    have hny := GT_NF hσ hy hyω
    unfold GT at hnx hny ⊢
    rw [heq] at hnx ⊢
    refine thb_lt_of_I hσ hnx hny ?_ ?_
    · rw [gev_Farg hσ hx, gev_Farg hσ hy]; exact add_lt_add_right hxy _
    · refine star_le_of σ (fun u hu => ?_) (thb_pos hσ (NF.th_dom hny))
      have hxl : ev σ x < OmT σ (max (lvl (ev σ y)) 1 + 1) := by
        rw [← heq]; exact (glvl_lt σ hxω).trans_le (OmT_mono hσ (by omega))
      exact lt_of_le_of_lt (gstar_Farg hσ hx hxl u hu) ((gFarg_ge hσ hy).trans
        (thb_gt_arg hσ (NF.th_dom hny) (gFarg_lt hσ hy (by
          exact (glvl_lt σ hyω).trans_le (OmT_mono hσ (by omega))))))

theorem GT_pos (hσ : Base σ) {x : Tm} (hx : NF σ x) (hxω : ev σ x < Om (ω : Ordinal.{0})) :
    0 < ev σ (GT σ x) := lt_of_le_of_lt zero_le (OmT_lt_GT hσ hx hxω (Nat.zero_le _))

/-- `Gd d = G(E d)` (`lvl` of `E d` is `lvl d`). -/
theorem Gd_eq {d : Term} (hD : DL S σ m n d) : Gd S σ m n d = GT σ (Ex S σ m n d) := by
  unfold Gd GT; rw [hD.lv]

/-! ## Lemma Q1 -/

/-- **Lemma Q1.** -/
theorem Q1s (hσ : Base σ) : ∀ (N : ℕ) (s' d : Term), (Term.psiS s' d).size ≤ N →
    Term.NF (.psiS s' d) → Term.val S s' = 1 → Term.val S d < Om (ω : Ordinal.{0}) →
    (∀ u : Term, u.size ≤ d.size → CL S σ m n u → DL S σ m n u) →
    (∀ x y : Term, x.size ≤ d.size → y.size ≤ d.size → CL S σ m n x → CL S σ m n y →
      Term.val S x < Term.val S y → ev σ (Ex S σ m n x) < ev σ (Ex S σ m n y)) →
    CL S σ m n d →
    ∀ u : Term, CL S σ m n u → u.size ≤ d.size → Term.KLt (.psiS s' d) u d →
      Term.val S u ≤ Term.val S d →
      ∀ p ∈ Kst 1 (Ex S σ m n u), ev σ p.2 < ev σ (GT σ (Ex S σ m n d)) := by
  intro N
  induction N with
  | zero => intro s' d h; exact absurd (Term.size_pos (.psiS s' d)) (by omega)
  | succ N ihN =>
    intro s' d hsz hμ hs1 hdω hD hM hd
    have hDd := hD d le_rfl hd
    have hEdω : ev σ (Ex S σ m n d) < Om (ω : Ordinal.{0}) := hDd.lt.trans (OmT_succ_lt_Om_omega σ _)
    set X := ev σ (GT σ (Ex S σ m n d)) with hX
    have hX0 : 0 < X := GT_pos hσ hDd.nf hEdω
    have hXP : IsPrincipal (· + ·) X := (GT_bounds hσ hDd.nf hEdω).2.2.2
    have hlvX : ∀ j : ℕ, j ≤ lvl (Term.val S d) → ev σ (Pk j) < X ∧ OmT σ (j + 1) < X := by
      intro j hj
      rw [← hDd.lv] at hj
      exact ⟨Pk_lt_GT hσ hDd.nf hEdω (le_max_of_le_left hj), OmT_lt_GT hσ hDd.nf hEdω (le_max_of_le_left hj)⟩
    have hP1X : ev σ (Pk 1) < X ∧ OmT σ 2 < X :=
      ⟨Pk_lt_GT hσ hDd.nf hEdω (le_max_right _ _), OmT_lt_GT hσ hDd.nf hEdω (le_max_right _ _)⟩
    -- `F` and `G` of a smaller argument
    have hFG : ∀ c : Term, c.size < d.size → CL S σ m n c → Term.val S c < Term.val S d →
        ev σ (gFc σ (Ex S σ m n c)) < X ∧ ev σ (GT σ (Ex S σ m n c)) < X := by
      intro c hsc hcc hlt
      have hDc := hD c hsc.le hcc
      have hE := hM c d hsc.le le_rfl hcc hd hlt
      have hG := GT_lt hσ hDc.nf hDd.nf hEdω hE
      exact ⟨lt_of_le_of_lt (Fc_le_GT hσ hDc.nf (hE.trans hEdω)) hG, hG⟩
    intro u hu
    induction hu with
    | par hn hv =>
      intro _ _ _ p hp
      rw [Ex_par hv] at hp; simp [Kst] at hp
    | @add a b hn hv ha hb iha ihb =>
      intro hs hK hle p hp
      rw [(hD _ hs (CL.add hn hv ha hb)).add a b rfl hv] at hp
      simp only [Kst, List.mem_append] at hp
      rcases hp with hp | hp
      · exact iha (by simp [Term.size] at hs; omega) hK.1 ((val_le_add_left a b).trans hle) p hp
      · exact ihb (by simp [Term.size] at hs; omega) hK.2 ((val_le_add_right a b).trans hle) p hp
    | @om b j hn hv hj0 hj =>
      intro _ _ _ p hp
      rw [Ex, EL_om hv, hj, natOf_nat] at hp
      simp only [Omk, Kst] at hp
      split_ifs at hp
      · simp at hp
      · simp at hp; subst hp; exact hX0
    | @psiA s'' c'' hn hv hs0 _ _ _ _ _ =>
      intro _ _ _ p hp
      have h0 : natOf (Term.val S s'') = 0 := by rw [hs0]; exact natOf_nat 0
      rw [Ex, EL_psi0 hv h0] at hp
      simp [Kst] at hp
    | @phi x y hn hv hx hy ihx ihy =>
      intro hs hK hle p hp
      have hDx := hD x (by simp [Term.size] at hs; omega) hx
      have hDy := hD y (by simp [Term.size] at hs; omega) hy
      obtain ⟨vx, vy⟩ := NF_phi_lt (S := S) hn
      set j := lvl (Term.val S (.phi x y)) with hjdef
      have hvω : Term.val S (.phi x y) < Om (ω : Ordinal.{0}) := lt_of_le_of_lt hle hdω
      have hxk : ev σ (Ex S σ m n x) < OmT σ (j + 1) :=
        lt_of_lt_of_le hDx.lt (OmT_mono hσ (by have := lvl_mono hvω vx.le; omega))
      have hyk : ev σ (Ex S σ m n y) < OmT σ (j + 1) :=
        lt_of_lt_of_le hDy.lt (OmT_mono hσ (by have := lvl_mono hvω vy.le; omega))
      have hjm : j ≤ lvl (Term.val S d) := lvl_mono hdω hle
      rw [Ex, EL_phi hv, ← hjdef] at hp
      simp only [Kst] at hp
      split_ifs at hp with hjk
      · simp at hp
      rcases List.mem_cons.1 hp with hp | hp
      · subst hp
        exact (gcodephi_lt_Pk hσ hDx.nf hDy.nf hxk hyk).trans (hlvX j hjm).1
      · rcases List.mem_cons.1 (gKst_codephi hσ (by omega) hp) with h | h
        · subst h; exact hxk.trans_le ((hlvX j hjm).2.le)
        · rcases List.mem_append.1 h with h | h
          · exact ihx (by simp [Term.size] at hs; omega) hK.1 (vx.le.trans hle) p h
          · exact ihy (by simp [Term.size] at hs; omega) hK.2 (vy.le.trans hle) p h
    | @psiS s'' c'' j hn hv hj0 hj hcω' hcc ihc =>
      intro hs hK hle p hp
      have hnat : natOf (Term.val S s'') ≠ 0 := by rw [hj, natOf_nat]; exact hj0
      rw [Ex, EL_psiS hv hnat, hj, natOf_nat] at hp
      simp only [Kst] at hp
      split_ifs at hp with hjk
      · omega
      have hjm : j ≤ lvl (Term.val S d) := by
        have := lvl_mono hdω hle; rw [lvl_psiS s'' c'' hj] at this; exact this
      have hsc : c''.size < d.size := by simp [Term.size] at hs; omega
      -- the argument is below `d`, visited or as a level-1 stop
      have hcd : Term.val S c'' < Term.val S d ∧
          (Term.KLt (.psiS s' d) c'' d ∨ (j = 1 ∧ Term.val S (.psiS s'' c'') < Term.val S (.psiS s' d))) := by
        rcases hK with hK | ⟨hca, _, hKc⟩
        · have hlt := (Term.cmp_lt_iff S hn hμ).1 hK
          have hj1 : j = 1 := by
            by_contra hne
            have h2 : 2 ≤ j := by omega
            have h3 : Om ((1 : Ordinal.{0}) + 1) ≤ Om (Term.val S s'') := by
              refine Om_le_Om.2 ?_; rw [hj]; exact_mod_cast h2
            have h4 := (Term.val_psiS_bounds S s' d).2
            rw [hs1] at h4
            exact absurd (hlt.trans h4) (not_lt.2 (h3.trans (Term.val_psiS_bounds S s'' c'').1.le))
          refine ⟨lt_of_psi_lt (InR_Om_succ (S := S) 1) ?_, Or.inr ⟨hj1, hlt⟩⟩
          simp only [Term.val] at hlt; rw [hj, hs1, hj1] at hlt; simpa using hlt
        · exact ⟨(Term.cmp_lt_iff S hn.2.1 hμ.2.1).1 hca, Or.inl hKc⟩
      obtain ⟨hFc, hGc⟩ := hFG c'' hsc hcc hcd.1
      have hDc := hD c'' hsc.le hcc
      have hEcω : ev σ (Ex S σ m n c'') < Om (ω : Ordinal.{0}) := hDc.lt.trans (OmT_succ_lt_Om_omega σ _)
      rcases List.mem_cons.1 hp with hp | hp
      · subst hp
        rw [gev_codepsi hσ hDc.nf hEcω]
        exact hXP (hlvX j hjm).1 hFc
      · rcases List.mem_append.1 (Kst_plus σ 1 _ _ hp) with h | h
        · rw [Kst_Pk (by omega)] at h
          simp at h
          rcases h with rfl | rfl
          · rw [gev_Omk hσ]; exact (hlvX j hjm).2
          · exact hX0
        · by_cases hc0' : ev σ (Ex S σ m n c'') = 0
          · rw [gFc_zero hσ hc0'] at h; simp [Kst] at h
          have h' := gKst_Fc hσ hc0' h
          split_ifs at h' with hl
          · simp at h'
          rcases List.mem_cons.1 h' with h' | h'
          · subst h'; exact (gev_Fc_pos hσ hDc.nf hEcω hc0').1.trans hFc
          · rcases List.mem_append.1 h' with h' | h'
            · rw [Kst_Omk (by omega)] at h'; simp at h'; subst h'; exact hX0
            · rcases List.mem_append.1 h' with h' | h'
              · rw [Kst_Omk (by omega)] at h'; simp at h'; subst h'; exact hX0
              · rcases hcd.2 with hKc | ⟨hj1, _⟩
                · exact ihc hsc.le hKc hcd.1.le p h'
                · -- a level-1 stop: a new anchor `ψ_{Ω₂}(c'')`
                  subst hj1
                  have hs1' : Term.val S s'' = 1 := by rw [hj]; norm_num
                  have := ihN s'' c'' (by simp [Term.size] at hsz hs ⊢; omega) hn hs1' hcω'
                    (fun u hu hcu => hD u (hu.trans hsc.le) hcu)
                    (fun x y hx hy hcx hcy hxy => hM x y (hx.trans hsc.le) (hy.trans hsc.le) hcx hcy hxy)
                    hcc c'' hcc le_rfl hn.2.2 le_rfl p h'
                  exact this.trans hGc

end Googology.Trans.PoR.InaccPsi.R2.Br

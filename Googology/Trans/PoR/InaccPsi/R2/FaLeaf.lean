import Googology.Trans.PoR.InaccPsi.R2.FaCan

/-!
# Fa: THE LEAVES OF A LEVEL ARE READINGS OF CODES OF BOTH HULLS, AND THERE ARE FINITELY MANY

`T = Kz.vbTK S λ K`, `Θ` the reading at `λ`.  `FaLeafP u`: `u = Θ e` for a code `e < Ω₂` in both hulls.

* `fa_ucComps_fin` (the components of a level are finitely many), `fa_ucParts_fin`;
* `fa_comps_code` (**the components of `T w` are values of `T` on `D_K`**), `fa_parts_code` (**the parts of an atom `T x` below `B₂` are values of `T`**);
* `faLeafLow`, `faLeafR` (**every leaf of `T x` is a reading of a code of both hulls**);
* `fa_vc_fin`, `fa_yv_fin` (**a decomposed code has finitely many leaves**).

No new axiom.  New definition: `FaLeafP`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Fa

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rx Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Kz Googology.Trans.PoR.InaccPsi.R2.Ul
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Tl
  Googology.Trans.PoR.InaccPsi.R2.Vc Googology.Trans.PoR.InaccPsi.R2.Yv

variable {S : InaccSeq.{0}}

/-- The components of a level are finitely many. -/
theorem fa_ucComps_fin : ∀ γ : Ordinal.{0}, (ucComps γ).Finite := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  by_cases h1 : γ < OmTwo
  · rw [ucComps_small h1]; exact Set.finite_singleton _
  by_cases h2 : γ < ucE
  · rw [ucComps_big (not_lt.1 h1) h2]
    exact (IH _ (uc_log_lt (not_lt.1 h1) h2)).union ((Set.finite_singleton _).union (IH _ (uc_mod_lt (not_lt.1 h1))))
  · rw [ucComps_out (not_lt.1 h2)]; exact Set.finite_empty

theorem fa_ucParts_fin (z : Ordinal.{0}) : (ucParts z).Finite := by
  unfold ucParts
  split_ifs
  · exact (Set.finite_singleton _).insert _
  · exact (fa_ucComps_fin _).union (Set.finite_singleton _)

/-- **A code below `B₂` has finitely many leaves.** -/
theorem fa_vc_fin {P : Ordinal.{0} → Prop} : ∀ z, VcLv P z →
    ∃ L : Finset Ordinal.{0}, (∀ u ∈ L, P u) ∧ VcLv (· ∈ L) z := by
  classical
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hL
  have hunion : ∀ {a b : Ordinal.{0}}, a < z → b < z → VcLv P a → VcLv P b →
      ∃ L : Finset Ordinal.{0}, (∀ u ∈ L, P u) ∧ VcLv (· ∈ L) a ∧ VcLv (· ∈ L) b := fun ha hb hLa hLb => by
    obtain ⟨L1, h1, h2⟩ := IH _ ha hLa
    obtain ⟨L2, h3, h4⟩ := IH _ hb hLb
    refine ⟨L1 ∪ L2, fun u hu => ?_, VcLv_mono (fun x _ hx => Finset.mem_union_left _ hx) _ h2,
      VcLv_mono (fun x _ hx => Finset.mem_union_right _ hx) _ h4⟩
    rcases Finset.mem_union.1 hu with hu | hu
    · exact h1 u hu
    · exact h3 u hu
  rcases lt_trichotomy z Om1 with hz1 | rfl | hz1
  · have hp := (VcLv_small P hz1).1 hL
    exact ⟨{z}, by simpa using hp, (VcLv_small _ hz1).2 (by simp)⟩
  · exact ⟨∅, by simp, VcLv_Om1 _⟩
  by_cases hB : z < ucB
  swap
  · exact ⟨∅, by simp, VcLv_big _ (not_lt.1 hB)⟩
  by_cases hE : ω ^ z = z
  · by_cases hI : invVeblen₁ z < z
    · obtain ⟨h1, h2⟩ := (VcLv_phi _ hz1 hB hE hI).1 hL
      obtain ⟨L, hP, h3, h4⟩ := hunion hI (Tf.tf_inv2_lt hE) h1 h2
      exact ⟨L, hP, (VcLv_phi _ hz1 hB hE hI).2 ⟨h3, h4⟩⟩
    · have hparts := (VcLv_atom _ hz1 hB hE hI).1 hL
      have hfin := fa_ucParts_fin z
      have key : ∀ s : Set Ordinal.{0}, s.Finite → s ⊆ ucParts z →
          ∃ L : Finset Ordinal.{0}, (∀ u ∈ L, P u) ∧ ∀ x ∈ s, x < z → VcLv (· ∈ L) x := by
        intro s hs
        induction s, hs using Set.Finite.induction_on with
        | empty => exact fun _ => ⟨∅, by simp, by simp⟩
        | @insert a s _ _ ih =>
          intro hsub
          obtain ⟨L1, h1, h2⟩ := ih (fun x hx => hsub (Set.mem_insert_of_mem _ hx))
          by_cases haz : a < z
          · obtain ⟨L2, h3, h4⟩ := IH a haz (hparts a (hsub (Set.mem_insert _ _)) haz)
            refine ⟨L1 ∪ L2, fun u hu => ?_, fun x hx hxz => ?_⟩
            · rcases Finset.mem_union.1 hu with hu | hu
              · exact h1 u hu
              · exact h3 u hu
            · rcases hx with rfl | hx
              · exact VcLv_mono (fun _ _ hy => Finset.mem_union_right _ hy) _ h4
              · exact VcLv_mono (fun _ _ hy => Finset.mem_union_left _ hy) _ (h2 x hx hxz)
          · refine ⟨L1, h1, fun x hx hxz => ?_⟩
            rcases hx with rfl | hx
            · exact absurd hxz haz
            · exact h2 x hx hxz
      obtain ⟨L, hP, hL'⟩ := key _ hfin subset_rfl
      exact ⟨L, hP, (VcLv_atom _ hz1 hB hE hI).2 hL'⟩
  · obtain ⟨h1, h2⟩ := (VcLv_cnf _ hz1 hB hE).1 hL
    have hl : log ω z < z := Tf.tf_log_lt hz1 hE
    have hr : z % ω ^ log ω z < z := Rj.rj_mod_lt (Rj.rj_Om1_pos.trans hz1).ne'
    by_cases hε : ω ^ log ω z = log ω z
    · rw [if_pos hε] at h1
      obtain ⟨L, hP, h3, h4⟩ := hunion hl hr h1 h2
      exact ⟨L, hP, (VcLv_cnf _ hz1 hB hE).2 ⟨by rw [if_pos hε]; exact h3, h4⟩⟩
    · rw [if_neg hε] at h1
      obtain ⟨L, hP, h3, h4⟩ := hunion ((Ordinal.sub_le_self _ _).trans_lt hl) hr h1 h2
      exact ⟨L, hP, (VcLv_cnf _ hz1 hB hE).2 ⟨by rw [if_neg hε]; exact h3, h4⟩⟩

/-- **A decomposed code has finitely many leaves.** -/
theorem fa_yv_fin {P : Ordinal.{0} → Prop} {z : Ordinal.{0}} (h : YvLv S P z) :
    ∃ L : Finset Ordinal.{0}, (∀ u ∈ L, P u) ∧ YvLv S (· ∈ L) z := by
  classical
  have hunion : ∀ {a b : Ordinal.{0}}, (∃ L : Finset Ordinal.{0}, (∀ u ∈ L, P u) ∧ YvLv S (· ∈ L) a) →
      (∃ L : Finset Ordinal.{0}, (∀ u ∈ L, P u) ∧ YvLv S (· ∈ L) b) →
      ∃ L : Finset Ordinal.{0}, (∀ u ∈ L, P u) ∧ YvLv S (· ∈ L) a ∧ YvLv S (· ∈ L) b := fun ⟨L1, h1, h2⟩ ⟨L2, h3, h4⟩ => by
    refine ⟨L1 ∪ L2, fun u hu => ?_, h2.mono fun x hx => Finset.mem_union_left _ hx,
      h4.mono fun x hx => Finset.mem_union_right _ hx⟩
    rcases Finset.mem_union.1 hu with hu | hu
    · exact h1 u hu
    · exact h3 u hu
  induction h with
  | low hz hL =>
    obtain ⟨L, h1, h2⟩ := fa_vc_fin _ hL
    exact ⟨L, h1, YvLv.low hz h2⟩
  | om h1 h2 h3 => exact ⟨∅, by simp, YvLv.om h1 h2 h3⟩
  | cnf h1 h2 h3 h4 h5 h6 _ _ ih1 ih2 =>
    obtain ⟨L, hP, a, b⟩ := hunion ih1 ih2
    exact ⟨L, hP, YvLv.cnf h1 h2 h3 h4 h5 h6 a b⟩
  | veb h1 h2 h3 h4 h5 h6 h7 _ _ ih1 ih2 =>
    obtain ⟨L, hP, a, b⟩ := hunion ih1 ih2
    exact ⟨L, hP, YvLv.veb h1 h2 h3 h4 h5 h6 h7 a b⟩
  | atom h1 h2 h3 h4 h5 h6 _ _ ih1 ih2 =>
    obtain ⟨L, hP, a, b⟩ := hunion ih1 ih2
    exact ⟨L, hP, YvLv.atom h1 h2 h3 h4 h5 h6 a b⟩

/-- A leaf that is the reading of a code of both hulls. -/
def FaLeafP (S : InaccSeq.{0}) (l l' u : Ordinal.{0}) : Prop :=
  ∃ e, e < Om (1 + 1) ∧ GxCl (upsilon l) (ldAtR S l) e ∧ GxCl (upsilon l') (ldAtR S l') e ∧
    gxTh (upsilon l) (ldAtR S l) e = u

section Two

variable {l l' ηx ηx' K : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hl' : IsRestartIdx l') (hX' : upsilon l' < Pv S ηx') (hKB : KzB S K)

include hl hX hl' hX' hKB

/-- **The components of `T w` are values of `T` on `D_K`.** -/
theorem fa_comps_code :
    ∀ u, u < ucE → ∀ w, VbDK S l K w → VbDK S l' K w → vbTK S l K w = u →
      ∀ v ∈ ucComps u, ∃ x, VbDK S l K x ∧ VbDK S l' K x ∧ vbTK S l K x = v := by
  have hO2 : (OmTwo : Ordinal.{0}) = Om (1 + 1) := Uc.uc_Om2_eq
  have hPC := faPC_D (S := S) (l := l) hKB
  have hPC' := faPC_D (S := S) (l := l') hKB
  have h3 := fa_O3_D (S := S) (l := l) hKB
  have h3' := fa_O3_D (S := S) (l := l') hKB
  intro u
  induction u using WellFoundedLT.induction with
  | ind u IH =>
  intro huE w hw hw' hTw v hv
  by_cases hu2 : u < OmTwo
  · rw [ucComps_small hu2] at hv
    exact ⟨w, hw, hw', hTw.trans hv.symm⟩
  have hu2' : OmTwo ≤ u := not_lt.1 hu2
  have hw3 : Om (1 + 1 + 1) ≤ w := not_lt.1 fun hc => by
    have := fa_T_lt_O2 hl hX hKB hw hc
    rw [hTw, ← hO2] at this
    exact hu2 this
  have h1W : (1 : Ordinal.{0}) < Om (1 + 1 + 1) := Ui.ui_one_lt_SC (Ui.ui_SC_W _)
  have hw0 : w ≠ 0 := ((Kx.kx3SC.1).trans_le hw3).ne'
  set e := Ordinal.log (Om (1 + 1 + 1)) w with hedef
  set d := w / Om (1 + 1 + 1) ^ e with hddef
  set r := w % Om (1 + 1 + 1) ^ e with hrdef
  have hWe0 : Om (1 + 1 + 1) ^ e ≠ 0 := (Ui.ui_W_pos _ e).ne'
  have hdec : Om (1 + 1 + 1) ^ e * d + r = w := Ordinal.div_add_mod w _
  have hd3 : d < Om (1 + 1 + 1) := div_opow_log_lt w h1W
  have hd0 : d ≠ 0 := ((Ordinal.div_pos hWe0).2 (opow_log_le_self _ hw0)).ne'
  have hrlt : r < Om (1 + 1 + 1) ^ e := Ordinal.mod_lt w hWe0
  have hdig : w / Om (1 + 1 + 1) ^ e % Om (1 + 1 + 1) ≠ 0 := by
    show d % Om (1 + 1 + 1) ≠ 0
    rwa [Ordinal.mod_eq_of_lt hd3]
  have hparts : ∀ {P : Ordinal.{0} → Prop}, FaPC P → P (Om (1 + 1 + 1)) → P w →
      P e ∧ P d ∧ P r ∧ P (Om (1 + 1 + 1) ^ e) ∧ P (Om (1 + 1 + 1) ^ e * d) := fun {P} hP hP3 hPw => by
    have hPe := hP.dig_exp (r := 1 + 1) hP3 hPw e hdig
    have hPm : P (Om (1 + 1 + 1) * e) := by
      have := hP.opow_mul hP3 e hPe; rwa [Ui.ui_W_opow (1 + 1)] at this
    have hPd : P d := by
      show P (w / Om (1 + 1 + 1) ^ e)
      rw [Ui.ui_W_eq (1 + 1) e]; exact hP.div w hPw _ hPm
    have hPr : P r := by
      show P (w % Om (1 + 1 + 1) ^ e)
      rw [Ui.ui_W_eq (1 + 1) e]; exact hP.mod w hPw _
    have hPW : P (Om (1 + 1 + 1) ^ e) := by
      rw [Ui.ui_W_eq (1 + 1) e]
      have := hP.opow_mul hPm _ hP.one
      rwa [mul_one] at this
    have hPWd : P (Om (1 + 1 + 1) ^ e * d) := by
      rw [Ui.ui_W_eq (1 + 1) e]; exact hP.opow_mul hPm _ hPd
    exact ⟨hPe, hPd, hPr, hPW, hPWd⟩
  obtain ⟨heD, hdD, hrD, hWeD, hWdD⟩ := hparts hPC h3 hw
  obtain ⟨heD', hdD', hrD', -, -⟩ := hparts hPC' h3' hw'
  have hT : vbTK S l K w = Om (1 + 1) ^ vbTK S l K e * vbTK S l K d + vbTK S l K r := by
    conv_lhs => rw [← hdec]
    have h := faT_Wmul hl hX hKB (k := 1) heD hdD
    simp only [Nat.cast_one] at h
    rw [kzT_add hl hX hKB hWdD hrD, h]
  have hTW : vbTK S l K (Om (1 + 1 + 1) ^ e) = Om (1 + 1) ^ vbTK S l K e := by
    have h := faT_Wmul hl hX hKB (k := 1) heD hPC.one
    simp only [Nat.cast_one] at h
    rwa [mul_one, fa_T_one hl hX hKB, mul_one] at h
  have hTd2 := fa_T_lt_O2 hl hX hKB hdD hd3
  have hTd0 : vbTK S l K d ≠ 0 := by
    have h := vbTK_mono hl hX hKB hPC.zero hdD (pos_iff_ne_zero.2 hd0)
    rw [vbTK_zero hl hX hKB] at h
    exact h.ne'
  have hTrlt : vbTK S l K r < Om (1 + 1) ^ vbTK S l K e := by
    rw [← hTW]; exact vbTK_mono hl hX hKB hrD hWeD hrlt
  have hTd2' : vbTK S l K d < OmTwo := by rw [hO2]; exact hTd2
  have hTrlt' : vbTK S l K r < OmTwo ^ vbTK S l K e := by rw [hO2]; exact hTrlt
  have hu : u = OmTwo ^ vbTK S l K e * vbTK S l K d + vbTK S l K r := by rw [← hTw, hT, hO2]
  obtain ⟨hlog, hdiv, hmod⟩ := uc_cnf_parts hTd0 hTd2' hTrlt'
  rw [← hu] at hlog hdiv hmod
  have hcomps := ucComps_big hu2' huE
  rw [hlog] at hcomps
  rw [hlog] at hdiv hmod
  rw [hdiv, hmod] at hcomps
  have heu : vbTK S l K e < u := by
    have := uc_log_lt hu2' huE; rwa [hlog] at this
  have hru : vbTK S l K r < u := by
    have := uc_mod_lt hu2'; rwa [hlog, hmod] at this
  rw [hcomps] at hv
  rcases hv with hv | hv | hv
  · exact IH _ heu (heu.trans huE) e heD heD' rfl v hv
  · exact ⟨d, hdD, hdD', hv.symm⟩
  · exact IH _ hru (hru.trans huE) r hrD hrD' rfl v hv

/-- **Every leaf of `T x` below `B₂` is a reading of a code of both hulls.** -/
theorem faLeafLow (hAW : Om ω ≤ ConjT.Aη S (cdEta S l)) (hAW' : Om ω ≤ ConjT.Aη S (cdEta S l')) :
    ∀ z, z < ucB → ∀ x, VbDK S l K x → VbDK S l' K x → vbTK S l K x = z → VcLv (FaLeafP S l l') z := by
  have hO1 : (Om1 : Ordinal.{0}) = Om 1 := Rj.rj_Om1
  have hPC := faPC_D (S := S) (l := l) hKB
  have hPC' := faPC_D (S := S) (l := l') hKB
  have hB2 : (ucB : Ordinal.{0}) < Om (1 + 1) := Yv.yv_B_lt_Om2
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hzB x hx hx' hTx
  rcases lt_trichotomy z Om1 with hz1 | rfl | hz1
  · have hTx1 : vbTK S l K x < Om 1 := by rw [hTx, ← hO1]; exact hz1
    have hx2 := fa_lt_O2 hl hX hKB hx hTx1
    refine (VcLv_small _ hz1).2 ⟨x, hx2, (ldHull_iff hl hX hx2).1 hx.1, (ldHull_iff hl' hX' hx2).1 hx'.1, ?_⟩
    rw [← vbTK_code hl hX hKB hx2 hx.1]; exact hTx
  · exact VcLv_Om1 _
  have hz1' : Om 1 < z := by rw [← hO1]; exact hz1
  have hx2le : Om (1 + 1) ≤ x := not_lt.1 fun hc => by
    have := fa_T_lt_O1 hl hX hKB hx hc
    rw [hTx] at this
    exact absurd this (not_lt.2 hz1'.le)
  have hx2 : Om (1 + 1) < x := lt_of_le_of_ne hx2le fun e => by
    rw [← e, fa_T_O2 hl hX hKB] at hTx
    exact absurd hz1' (by rw [← hTx]; exact lt_irrefl _)
  have hx0 : x ≠ 0 := ((Ui.ui_SC_W 1).1.trans hx2).ne'
  by_cases hE : ω ^ z = z
  · have hxε : ω ^ x = x := (fa_T_eps_iff hl hX hKB hx hx2le).2 (by rw [hTx]; exact hE)
    by_cases hI : invVeblen₁ z < z
    · have hb2 : invVeblen₂ z < z := Tf.tf_inv2_lt hE
      have hvz : veblen (invVeblen₁ z) (invVeblen₂ z) = z := by rw [veblen_invVeblen₁_invVeblen₂, hE]
      have hzS : ¬ SC z := fun h => by
        have := h.2 _ hI _ hb2
        rw [hvz] at this
        exact lt_irrefl _ this
      have hxS : ¬ SC x := fun h => hzS (hTx ▸ (fa_T_SC_iff hl hX hKB hx hx2).1 h)
      obtain ⟨haD, hbD, -, -, -, -, e1, e2, -⟩ := fa_shape_veb hl hX hKB hx hx2 hxε hxS
      obtain ⟨haD', hbD', -, -, -, -, -, -, -⟩ := fa_shape_veb hl' hX' hKB hx' hx2 hxε hxS
      rw [hTx] at e1 e2
      exact (VcLv_phi _ hz1 hzB hE hI).2 ⟨IH _ hI (hI.trans hzB) _ haD haD' e1.symm,
        IH _ hb2 (hb2.trans hzB) _ hbD hbD' e2.symm⟩
    · have hzS : SC z := Tl.tl_SC_of hz1 hI
      have hxS : SC x := (fa_T_SC_iff hl hX hKB hx hx2).2 (by rw [hTx]; exact hzS)
      have hzΩ2 : z < Om (1 + 1) := hzB.trans hB2
      have hΩ : ¬ ∃ j : ℕ, x = Om (j : Ordinal.{0}) := by
        rintro ⟨j, rfl⟩
        have hj : 2 ≤ j := by
          have h := Om_le_Om.1 hx2le
          rw [one_add_one_eq_two] at h
          have h' : ((2 : ℕ) : Ordinal.{0}) ≤ j := by rw [Nat.cast_ofNat]; exact h
          exact_mod_cast h'
        obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        have e := vbTK_Om (S := S) hl hX hKB (k := i) (by omega)
        rw [Nat.cast_succ] at hTx
        rw [e] at hTx
        have hi : (1 : Ordinal.{0}) ≤ i := by
          have : 1 ≤ i := by omega
          exact_mod_cast this
        rcases hi.lt_or_eq with h | h
        · exact absurd ((Om_le_Om.2 (Order.add_one_le_of_lt h)).trans_lt (hTx ▸ hzΩ2)) (lt_irrefl _)
        · rw [← h] at hTx; exact absurd hz1' (by rw [← hTx]; exact lt_irrefl _)
      have hW : x ≠ Om ω := fun e => by
        rw [e, vbTK_OmW hl hX hKB (e ▸ hx.2.2)] at hTx
        exact absurd (hTx ▸ hzΩ2) (not_lt.2 (Om_le_Om.2 (Ui.ui_s1_lt_omega one_lt_omega0).le))
      obtain ⟨k, hk, hk1, hk2, γ, y, hγ, hy, hxe⟩ := fa_shape_atom hl hX hKB hx hx2 hxS hΩ hW
      obtain rfl : k = 1 := by
        by_contra hne
        have hk2' : 2 ≤ k := by omega
        have hk3 : Om (1 + 1 + 1) ≤ x := by
          refine (Om_le_Om.2 ?_).trans hk1.le
          have h' : ((2 : ℕ) : Ordinal.{0}) ≤ k := by exact_mod_cast hk2'
          have e : ((2 : ℕ) : Ordinal.{0}) = 1 + 1 := by norm_num
          rw [e] at h'
          exact add_le_add h' le_rfl
        have := vbTK_ge_lev hl hX hKB hx 1 (by simpa using hk3)
        rw [hTx] at this
        exact absurd (by simpa using this) (not_le.2 hzΩ2)
      simp only [Nat.cast_one] at hγ hk1 hk2 hxe
      subst hxe
      have hA1 := faAtom hl hX hKB (k := 1) le_rfl (by simpa using hγ) (by simpa using hy) (by simpa using hk2) (by simpa using hx)
      have hA2 := faAtom hl' hX' hKB (k := 1) le_rfl (by simpa using hγ) (by simpa using hy) (by simpa using hk2) (by simpa using hx')
      simp only [Nat.cast_one] at hA1 hA2
      obtain ⟨hγD, hyD, hμV, hTz⟩ := hA1
      obtain ⟨hγD', hyD', -, -⟩ := hA2
      rw [hTz] at hTx
      set μ := vbTK S l K γ with hμdef
      set v := vbTK S l K y with hvdef
      have hvz : v < z := by
        rw [← hTx]
        have := vbTK_mono hl hX hKB hyD hx hy
        rwa [hTz] at this
      have hvz0 : v < ulH S 1 μ v := by rw [hTx]; exact hvz
      obtain ⟨hLev, hIdx⟩ := Vp.vpLev_H (S := S) (s := 1) hμV hvz0
      obtain ⟨hUL, hUI⟩ := Vd.vdLev_eq_uc (S := S) hzS hz1' hzB
      rw [Vp.vpLev_one, hTx] at hLev
      rw [hLev] at hUL
      have hne := uc_nf_of_lt hzS hz1 hzB
      obtain ⟨hlE, -, -, -, -⟩ := ucLev_spec hzS hz1 hne
      have hμE : μ < ucE := by rw [hUL]; exact hlE
      have hzH : ucH μ v = z := by
        have := (Vd.vd_lev_uc (S := S) hμE hzS hz1').1
        rw [← this]; exact hTx
      have hvz1 : v < ucH μ v := by rw [hzH]; exact hvz
      refine (VcLv_atom _ hz1 hzB hE hI).2 fun u hu huz => ?_
      by_cases hXz : z < tlX
      · obtain ⟨hβz, hβne, -⟩ := tlLev_spec hzS hz1 hXz
        have hμβ : μ = tlLev z := by
          rw [hUL]
          have hβO2 : tlLev z < OmTwo := (hβz.trans hXz).trans tlX_lt_OmTwo
          have hi := (tl_nf hzS hz1 hXz).1
          have hmax : max Om1 (tlLev z) < z := max_lt hz1 hβz
          obtain ⟨y', hy'⟩ := (uc_range_F hβO2 hmax).2 ⟨_, hi⟩
          have hy'z : y' < ucH (tlLev z) y' := by
            rw [hy']
            refine lt_of_le_of_ne ?_ fun e => ?_
            · rw [← hy']; exact (ucH_normal _).strictMono.le_apply
            · rw [e] at hy'
              exact hβne ((ucH_fix_iff_F hβO2 hmax).1 hy')
          have := (ucLev_H (hβO2.trans ucE_gt) hy'z).1
          rw [hy'] at this
          exact this
        have hμz : μ < z := by rw [hμβ]; exact hβz
        have hμX : μ < tlX := hμz.trans hXz
        have hμ2 : μ < OmTwo := hμX.trans tlX_lt_OmTwo
        set i := ucS μ + v with hidef
        have hzF : ucH μ v = rhF μ i := ucH_eq_F hμ2 v
        have hmaxμ : max Om1 μ < z := max_lt hz1 hμz
        have hiz : i < z := hzS.isPrincipal (ucS_lt hmaxμ hzS) hvz
        have hFz : rhF μ i = z := hzF.symm.trans hzH
        have hiF : i < rhF μ i := by rw [hFz]; exact hiz
        have hXF : rhF μ i < tlX := by rw [hFz]; exact hXz
        have hpF : ucParts z = {μ, i} := by rw [← hFz]; exact ucParts_F hXF hiF
        rw [hpF] at hu
        rcases hu with rfl | hu
        · exact IH _ huz (huz.trans hzB) γ hγD hγD' rfl
        · have hui : u = i := hu
          subst hui
          rcases lt_trichotomy μ Om1 with hμ1 | hμ1 | hμ1
          · have h1D := hPC.one
            have h1D' := hPC'.one
            have hx₁ : VbDK S l K (Om (1 + 1) + 1 + y) := hPC.add (hPC.add (fa_O2_D hKB) h1D) hyD
            have hx₁' : VbDK S l' K (Om (1 + 1) + 1 + y) := hPC'.add (hPC'.add (fa_O2_D hKB) h1D') hyD'
            have hTx₁ : vbTK S l K (Om (1 + 1) + 1 + y) = i := by
              rw [kzT_add hl hX hKB (hPC.add (fa_O2_D hKB) h1D) hyD, kzT_add hl hX hKB (fa_O2_D hKB) h1D,
                fa_T_O2 hl hX hKB, fa_T_one hl hX hKB, hidef, Qc.qc_ucS_low hμX, Gl.glY0_lt hμ1, hO1]
            exact IH _ hiz (hiz.trans hzB) _ hx₁ hx₁' hTx₁
          · have hx₁ : VbDK S l K (1 + y) := hPC.add hPC.one hyD
            have hx₁' : VbDK S l' K (1 + y) := hPC'.add hPC'.one hyD'
            have hTx₁ : vbTK S l K (1 + y) = i := by
              rw [kzT_add hl hX hKB hPC.one hyD, fa_T_one hl hX hKB, hidef, Qc.qc_ucS_low hμX, hμ1, Gl.glY0_eq]
            exact IH _ hiz (hiz.trans hzB) _ hx₁ hx₁' hTx₁
          · have hiv : i = v := by rw [hidef, Qc.qc_ucS_low hμX, Gl.glY0_gt hμ1, zero_add]
            exact IH _ hiz (hiz.trans hzB) y hyD hyD' hiv.symm
      · have hX1 : tlX ≤ ucH μ v := by rw [hzH]; exact not_lt.1 hXz
        have hpH : ucParts z = ucComps μ ∪ {v} := by rw [← hzH]; exact ucParts_H hμE hvz1 hX1
        rw [hpH] at hu
        rcases hu with hu | hu
        · obtain ⟨x', h1, h2, h3⟩ := fa_comps_code hl hX hl' hX' hKB μ hμE γ hγD hγD' rfl u hu
          exact IH _ huz (huz.trans hzB) x' h1 h2 h3
        · have huv : u = v := hu
          subst huv
          exact IH _ huz (huz.trans hzB) y hyD hyD' rfl
  · have hxε : ω ^ x ≠ x := fun h => hE (by rw [← hTx]; exact (fa_T_eps_iff hl hX hKB hx hx2le).1 h)
    obtain ⟨n, -, hdec, hlD, hrD, -, -, hTr, hlog, hmod, hdiv⟩ := fa_shape_cnf hl hX hKB hx hx0
    obtain ⟨n', -, hdec', hlD', hrD', -, -, -, -, -, -⟩ := fa_shape_cnf hl' hX' hKB hx' hx0
    have hx1' : Om 1 < x := (Om_lt_Om.2 (lt_add_one 1)).trans hx2
    have hlx : log ω x < x := ruLog_lt hx1' hxε
    have hrx : x % ω ^ log ω x < x := mod_opow_log_lt_self ω hx0
    have hl2 : Om (1 + 1) ≤ log ω x := le_log_of_opow_le one_lt_omega0 (by rw [gg_SC_eps ldOm2_SC]; exact hx2le)
    subst hTx
    have hTlz : vbTK S l K (log ω x) < vbTK S l K x := vbTK_mono hl hX hKB hlD hx hlx
    have hTrz : vbTK S l K (x % ω ^ log ω x) < vbTK S l K x := vbTK_mono hl hX hKB hrD hx hrx
    refine (VcLv_cnf _ hz1 hzB hE).2 ⟨?_, ?_⟩
    · rw [hlog]
      by_cases hε : ω ^ vbTK S l K (log ω x) = vbTK S l K (log ω x)
      · rw [if_pos hε]
        exact IH _ hTlz (hTlz.trans hzB) _ hlD hlD' rfl
      · rw [if_neg hε]
        have hbD : VbDK S l K (log ω x - Om (1 + 1)) := hPC.sub hlD (fa_O2_D hKB) hl2
        have hbD' : VbDK S l' K (log ω x - Om (1 + 1)) := hPC'.sub hlD' (fa_O2_D hKB) hl2
        have he : Om (1 + 1) + (log ω x - Om (1 + 1)) = log ω x := Ordinal.add_sub_cancel_of_le hl2
        have hTℓ : vbTK S l K (log ω x) = Om1 + vbTK S l K (log ω x - Om (1 + 1)) := by
          conv_lhs => rw [← he]
          rw [kzT_add hl hX hKB (fa_O2_D hKB) hbD, fa_T_O2 hl hX hKB, hO1]
        have hsub : vbTK S l K (log ω x) - Om1 = vbTK S l K (log ω x - Om (1 + 1)) := by
          rw [hTℓ, Ordinal.add_sub_cancel]
        rw [hsub]
        have hTbz : vbTK S l K (log ω x - Om (1 + 1)) < vbTK S l K x :=
          vbTK_mono hl hX hKB hbD hx ((Ordinal.sub_le_self _ _).trans_lt hlx)
        exact IH _ hTbz (hTbz.trans hzB) _ hbD hbD' rfl
    · rw [hlog, hmod]
      exact IH _ hTrz (hTrz.trans hzB) _ hrD hrD' rfl

/-- **Every leaf of `T x` is a reading of a code of both hulls.** -/
theorem faLeafR {Q : Ordinal.{0} → Prop} (hAW : Om ω ≤ ConjT.Aη S (cdEta S l))
    (hAW' : Om ω ≤ ConjT.Aη S (cdEta S l')) :
    ∀ z, YvLv S Q z → ∀ x, VbDK S l K x → VbDK S l' K x → vbTK S l K x = z → YvLv S (FaLeafP S l l') z := by
  intro z hz
  induction hz with
  | low hB _ =>
    intro x hx hx' hT
    exact YvLv.low hB (faLeafLow hl hX hl' hX' hKB hAW hAW' _ hB x hx hx' hT)
  | om h1s hs hzs => intro _ _ _ _; exact YvLv.om h1s hs hzs
  | @cnf s z h1s hs hz1 hz2 hzB hE _ _ ihl ihr =>
    intro x hx hx' hT
    have hO1z : Om 1 < z := (Om_le_Om.2 h1s).trans_lt hz1
    have hx2le : Om (1 + 1) ≤ x := not_lt.1 fun hc => by
      have := fa_T_lt_O1 hl hX hKB hx hc
      rw [hT] at this
      exact absurd this (not_lt.2 hO1z.le)
    have hx0 : x ≠ 0 := ((Ui.ui_SC_W 1).1.trans_le hx2le).ne'
    obtain ⟨n, -, -, hlD, hrD, -, -, -, hlog, hmod, -⟩ := fa_shape_cnf hl hX hKB hx hx0
    obtain ⟨n', -, -, hlD', hrD', -, -, -, -, -, -⟩ := fa_shape_cnf hl' hX' hKB hx' hx0
    subst hT
    exact YvLv.cnf h1s hs hz1 hz2 hzB hE (ihl _ hlD hlD' hlog.symm) (ihr _ hrD hrD' (by rw [hlog, hmod]))
  | @veb s z h1s hs hz1 hz2 hzB hE hS _ _ iha ihb =>
    intro x hx hx' hT
    have hO1z : Om 1 < z := (Om_le_Om.2 h1s).trans_lt hz1
    have hx2le : Om (1 + 1) ≤ x := not_lt.1 fun hc => by
      have := fa_T_lt_O1 hl hX hKB hx hc
      rw [hT] at this
      exact absurd this (not_lt.2 hO1z.le)
    have hx2 : Om (1 + 1) < x := lt_of_le_of_ne hx2le fun e => by
      rw [← e, fa_T_O2 hl hX hKB] at hT
      exact absurd hO1z (by rw [← hT]; exact lt_irrefl _)
    have hxε : ω ^ x = x := (fa_T_eps_iff hl hX hKB hx hx2le).2 (by rw [hT]; exact hE)
    have hxS : ¬ SC x := fun h => hS (hT ▸ (fa_T_SC_iff hl hX hKB hx hx2).1 h)
    obtain ⟨haD, hbD, -, -, -, -, e1, e2, -⟩ := fa_shape_veb hl hX hKB hx hx2 hxε hxS
    obtain ⟨haD', hbD', -, -, -, -, -, -, -⟩ := fa_shape_veb hl' hX' hKB hx' hx2 hxε hxS
    rw [hT] at e1 e2
    exact YvLv.veb h1s hs hz1 hz2 hzB hE hS (iha _ haD haD' e1.symm) (ihb _ hbD hbD' e2.symm)
  | @atom s z h1s hs hz1 hz2 hzB hS _ _ ihγ ihy =>
    intro x hx hx' hT
    have hO1z : Om 1 < z := (Om_le_Om.2 h1s).trans_lt hz1
    have hx2le : Om (1 + 1) ≤ x := not_lt.1 fun hc => by
      have := fa_T_lt_O1 hl hX hKB hx hc
      rw [hT] at this
      exact absurd this (not_lt.2 hO1z.le)
    have hx2 : Om (1 + 1) < x := lt_of_le_of_ne hx2le fun e => by
      rw [← e, fa_T_O2 hl hX hKB] at hT
      exact absurd hO1z (by rw [← hT]; exact lt_irrefl _)
    have hxS : SC x := (fa_T_SC_iff hl hX hKB hx hx2).2 (by rw [hT]; exact hS)
    have hΩ : ¬ ∃ j : ℕ, x = Om (j : Ordinal.{0}) := by
      rintro ⟨j, rfl⟩
      have hj : 2 ≤ j := by
        have h := Om_le_Om.1 hx2le
        rw [one_add_one_eq_two] at h
        have h' : ((2 : ℕ) : Ordinal.{0}) ≤ j := by rw [Nat.cast_ofNat]; exact h
        exact_mod_cast h'
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have e := vbTK_Om (S := S) hl hX hKB (k := i) (by omega)
      rw [Nat.cast_succ, e] at hT
      rw [← hT] at hz1 hz2
      exact Yv.yv_Om_not_in hz1 hz2
    have hW : x ≠ Om ω := fun e => by
      rw [e, vbTK_OmW hl hX hKB (e ▸ hx.2.2)] at hT
      rw [← hT] at hz1 hz2
      exact Yv.yv_Om_not_in hz1 hz2
    obtain ⟨k, hk, hk1, hk2, γ, y, hγ, hy, hxe⟩ := fa_shape_atom hl hX hKB hx hx2 hxS hΩ hW
    subst hxe
    obtain ⟨hγD, hyD, hμV, hTz⟩ := faAtom hl hX hKB hk hγ hy hk2 hx
    obtain ⟨hγD', hyD', -, -⟩ := faAtom hl' hX' hKB hk hγ hy hk2 hx'
    have hTz1 : Om (k : Ordinal.{0}) < ulH S (k : Ordinal.{0}) (vbTK S l K γ) (vbTK S l K y) := ulH_gt _ _
    have hTz2 : ulH S (k : Ordinal.{0}) (vbTK S l K γ) (vbTK S l K y) < Om ((k : Ordinal.{0}) + 1) := by
      rw [← hTz]; exact vbTK_lt_lev hl hX hKB hx k hk2
    rw [hTz] at hT
    have hsk : (k : Ordinal.{0}) = s := by
      rw [← hT] at hz1 hz2
      exact Yv.yv_lev_unique hTz1 hTz2 hz1 hz2
    subst hsk
    have hTy : vbTK S l K y < ulH S (k : Ordinal.{0}) (vbTK S l K γ) (vbTK S l K y) := by
      rw [← hTz]; exact vbTK_mono hl hX hKB hyD hx hy
    obtain ⟨hLev, hIdx⟩ := Vp.vpLev_H (S := S) (s := (k : Ordinal.{0})) hμV hTy
    rw [hT] at hLev hIdx
    have hR1 := ihγ γ hγD hγD' hLev.symm
    have hR2 := ihy y hyD hyD' (by rw [hLev, hIdx])
    exact YvLv.atom h1s hs hz1 hz2 hzB hS hR1 hR2

end Two

end Googology.Trans.PoR.InaccPsi.R2.Fa

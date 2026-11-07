import Googology.Trans.PoR.InaccPsi.R2.FaLeaf

/-!
# Fa: FINITE SETS OF CODES CLOSED UNDER THE PARTS

* `FaStep.mono`, `fa_zkEx_and`, `faClose` (**a code of both hulls lies in a finite set of codes of both hulls, closed under the parts**), `faClose_fin`.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Fa

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Zb
  Googology.Trans.PoR.InaccPsi.R2.Zr Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Xi
  Googology.Trans.PoR.InaccPsi.R2.Qf Googology.Trans.PoR.InaccPsi.R2.Zk Googology.Trans.PoR.InaccPsi.R2.Un
  Googology.Trans.PoR.InaccPsi.R2.Vi Googology.Trans.PoR.InaccPsi.R2.Vl Googology.Trans.PoR.InaccPsi.R2.Xj
  Googology.Trans.PoR.InaccPsi.R2.Aw Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Yv
  Googology.Trans.PoR.InaccPsi.R2.Vc Googology.Trans.PoR.InaccPsi.R2.Vd Googology.Trans.PoR.InaccPsi.R2.Kz
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Ul

variable {S : InaccSeq.{0}}

theorem FaStep.mono {l K : Ordinal.{0}} {H H' : Finset Ordinal.{0}} (h : H ⊆ H') {z : Ordinal.{0}}
    (hz : FaStep S l K H z) : FaStep S l K H' z := by
  rcases hz with hz | ⟨w, hw, h1, h2, h3, h4⟩
  · exact Or.inl hz
  refine Or.inr ⟨w, h hw, h1, h2, h3, ?_⟩
  rcases h4 with h4 | ⟨u, v, a1, a2, a3⟩ | ⟨a, a1, a2, a3⟩ | ⟨a, d, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ |
    ⟨γ, B, c, D, ηc, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩
  · exact Or.inl h4
  · exact Or.inr (Or.inl ⟨u, v, h a1, h a2, a3⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨a, h a1, h a2, a3⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, d, h a1, h a2, h a3, a4, a5, a6, a7, a8,
      zkEx_mono (fun e he => ⟨h he.1, he.2⟩) a a9⟩)))
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨γ, B, c, D, ηc, h a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, ?_⟩)))
    refine a12.mono fun x hx => ?_
    obtain ⟨e, he, h5, h6⟩ := hx
    exact ⟨e, h he, h5, h6⟩

theorem fa_zkEx_and {P Q : Ordinal.{0} → Prop} : ∀ a, ZkEx P a → ZkEx Q a → ZkEx (fun e => P e ∧ Q e) a := by
  refine zk_ind (fun _ _ => zkEx_zero _) ?_
  intro c k r hk0 hk hr IH h1 h2
  rw [zkEx_step _ hk0 hk hr] at h1 h2 ⊢
  exact ⟨⟨h1.1, h2.1⟩, IH h1.2 h2.2⟩

section Two

variable {l l' ηx ηx' K : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Nm.Pv S ηx)
  (hl' : IsRestartIdx l') (hX' : upsilon l' < Nm.Pv S ηx') (hKB : KzB S K)
  (hown : ConjT.Aη S (cdEta S l) ∈ S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)))
  (hρ : S.psi (ConjT.Aη S (cdEta S l)) (Om 1) = upsilon l)
  (hown' : ConjT.Aη S (cdEta S l') ∈ S.CSet (ConjT.Aη S (cdEta S l')) (S.psi (ConjT.Aη S (cdEta S l')) (Om 1)))
  (hρ' : S.psi (ConjT.Aη S (cdEta S l')) (Om 1) = upsilon l') (hWK : Om ω < K)
  (hAK : ConjT.Aη S (cdEta S l) < K) (hAK' : ConjT.Aη S (cdEta S l') < K)

include hl hX hl' hX' hKB hown hρ hown' hρ' hWK hAK hAK'

/-- **A code of both hulls lies in a finite set of codes of both hulls, closed under the parts.** -/
theorem faClose : ∀ c, GxCl (upsilon l) (ldAtR S l) c → GxCl (upsilon l') (ldAtR S l') c → c < Om (1 + 1) →
    ∃ H : Finset Ordinal.{0}, c ∈ H ∧ ∀ z ∈ H, (GxCl (upsilon l) (ldAtR S l) z ∧ GxCl (upsilon l') (ldAtR S l') z ∧ z ≤ c) ∧
      FaStep S l K H z := by
  classical
  obtain ⟨hZ, hZ1⟩ := Vb.vbZ hl hX
  obtain ⟨hZ', hZ1'⟩ := Vb.vbZ hl' hX'
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hAt' : GxAt (ldAtR S l') := ldAt_GxAt _ _
  have hO1 : (Om1 : Ordinal.{0}) = Om 1 := Rj.rj_Om1
  have hκ : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have h1θ : Om 1 < ConjT.th S := Ui.ui_L_lt_psi (s := 1) (Om ω)
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hc' hc2
  rcases lt_or_ge c (ConjT.th S) with hθ | hθ
  · exact ⟨{c}, by simp, fun z hz => by
      rw [Finset.mem_singleton.1 hz]
      exact ⟨⟨hc, hc', le_rfl⟩, Or.inl hθ⟩⟩
  -- finitely many smaller codes
  have hnew : ∀ (L : Finset Ordinal.{0}),
      (∀ w ∈ L, GxCl (upsilon l) (ldAtR S l) w ∧ GxCl (upsilon l') (ldAtR S l') w ∧ w < c) →
      ∃ H : Finset Ordinal.{0}, L ⊆ H ∧ ∀ z ∈ H, (GxCl (upsilon l) (ldAtR S l) z ∧
        GxCl (upsilon l') (ldAtR S l') z ∧ z < c) ∧ FaStep S l K H z := by
    intro L
    induction L using Finset.induction_on with
    | empty => exact fun _ => ⟨∅, by simp, by simp⟩
    | @insert w L _ ih =>
      intro hL
      obtain ⟨H0, hs0, h0⟩ := ih fun u hu => hL u (Finset.mem_insert_of_mem hu)
      obtain ⟨hwc, hwc', hwlt⟩ := hL w (Finset.mem_insert_self _ _)
      obtain ⟨H1, hw1, h1⟩ := IH w hwlt hwc hwc' (hwlt.trans hc2)
      refine ⟨H0 ∪ H1, ?_, ?_⟩
      · intro u hu
        rcases Finset.mem_insert.1 hu with rfl | hu
        · exact Finset.mem_union_right _ hw1
        · exact Finset.mem_union_left _ (hs0 hu)
      · intro z hz
        rcases Finset.mem_union.1 hz with hz | hz
        · exact ⟨(h0 z hz).1, (h0 z hz).2.mono Finset.subset_union_left⟩
        · obtain ⟨⟨a1, a1', a2⟩, a3⟩ := h1 z hz
          exact ⟨⟨a1, a1', a2.trans_lt hwlt⟩, a3.mono Finset.subset_union_right⟩
  have hfin : ∀ (L : Finset Ordinal.{0}),
      (∀ w ∈ L, GxCl (upsilon l) (ldAtR S l) w ∧ GxCl (upsilon l') (ldAtR S l') w ∧ w < c) →
      (∀ H : Finset Ordinal.{0}, L ⊆ H → FaStep S l K (insert c H) c) →
      ∃ H : Finset Ordinal.{0}, c ∈ H ∧ ∀ z ∈ H, (GxCl (upsilon l) (ldAtR S l) z ∧
        GxCl (upsilon l') (ldAtR S l') z ∧ z ≤ c) ∧ FaStep S l K H z := by
    intro L hL hst
    obtain ⟨H, hLH, hH⟩ := hnew L hL
    refine ⟨insert c H, Finset.mem_insert_self _ _, fun z hz => ?_⟩
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact ⟨⟨hc, hc', le_rfl⟩, hst H hLH⟩
    · obtain ⟨⟨a1, a1', a2⟩, a3⟩ := hH z hz
      exact ⟨⟨a1, a1', a2.le⟩, a3.mono (Finset.subset_insert _ _)⟩
  -- the largest closed atom
  have hcD := fa_hull_D hl hX hKB hown hρ hWK hAK hc hc2
  have hcD' := fa_hull_D hl' hX' hKB hown' hρ' hWK hAK' hc' hc2
  obtain ⟨w, hwD, hwL, hwc, hmax⟩ := faZB hl hX hKB hown hρ hWK c hc2 hcD hθ
  obtain ⟨w', hwD', hwL', hwc', hmax'⟩ := faZB hl' hX' hKB hown' hρ' hWK c hc2 hcD' hθ
  obtain rfl : w = w' := le_antisymm (hmax' w hwL hwc) (hmax w' hwL' hwc')
  have hw2 : w < Om (1 + 1) := hwc.trans_lt hc2
  have hwρ : GxCl (upsilon l) (ldAtR S l) w := (ldHull_iff hl hX hw2).1 hwD.1
  have hwσ : GxCl (upsilon l') (ldAtR S l') w := (ldHull_iff hl' hX' hw2).1 hwD'.1
  have hBρ := fa_base_of hl hX hKB hown hρ hWK hAK hwL hwρ hw2
  have hBσ := fa_base_of hl' hX' hKB hown' hρ' hWK hAK' hwL hwσ hw2
  have hwS : SC w := fa_Lv_SC hwL
  rcases hwc.lt_or_eq with hwlt | heq
  swap
  · exact ⟨{c}, by simp, fun z hz => by
      rw [Finset.mem_singleton.1 hz]
      exact ⟨⟨hc, hc', le_rfl⟩, Or.inr ⟨c, by simp, heq ▸ hwL, le_rfl, fun u _ h => h, Or.inl rfl⟩⟩⟩
  have hsw : ∀ H : Finset Ordinal.{0}, w ∈ H → w ∈ insert c H := fun H h => Finset.mem_insert_of_mem h
  have hc0 : c ≠ 0 := ((hwS.1).trans hwlt).ne'
  by_cases hP : IsPrincipal (· + ·) c
  · by_cases hE : ω ^ c = c
    · by_cases hI : invVeblen₁ c < c
      · -- `φ`
        have e : veblen (invVeblen₁ c) (invVeblen₂ c) = c := by rw [veblen_invVeblen₁_invVeblen₂, hE]
        have h2 : invVeblen₂ c < c := Tf.tf_inv2_lt hE
        obtain ⟨hac, hbc⟩ := gxDecV hZ.1 hAt hc _ _ e h2
        obtain ⟨hac', hbc'⟩ := gxDecV hZ'.1 hAt' hc' _ _ e h2
        set a := invVeblen₁ c with ha
        set b := invVeblen₂ c with hb
        have hab : a < veblen a b := by rw [e]; exact hI
        have hbb : b < veblen a b := by rw [e]; exact h2
        have hwφ : w < veblen a b := by rw [e]; exact hwlt
        obtain ⟨hic, hib, -⟩ := fa_Rd_ind hBρ hac hbc hab hbb hwφ
        obtain ⟨hic', -, -⟩ := fa_Rd_ind hBσ hac' hbc' hab hbb hwφ
        have ha1 : 1 ≤ a := by
          refine one_le_iff_ne_zero.2 fun h0 => ?_
          rw [h0, veblen_zero_apply] at e
          exact absurd (opow_inj (e.trans hE.symm)) h2.ne
        obtain ⟨E1, hE1, hE2⟩ := fc_exps_code hZ hAt (by rw [hO1]; exact hZ1) a hac
        obtain ⟨E1', hE1', hE2'⟩ := fc_exps_code hZ' hAt' (by rw [hO1]; exact hZ1') a hac'
        refine hfin (insert w (insert a (insert b (insert (qfInd a w b) (E1 ∩ E1'))))) ?_ fun H hL => ?_
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_inter] at hx
          rcases hx with rfl | rfl | rfl | rfl | ⟨h3, h4⟩
          · exact ⟨hwρ, hwσ, hwlt⟩
          · exact ⟨hac, hac', hI⟩
          · exact ⟨hbc, hbc', h2⟩
          · exact ⟨hic, hic', hib.trans_lt h2⟩
          · exact ⟨(hE1 x h3).1, (hE1' x h4).1, (hE1 x h3).2.trans_lt hI⟩
        · have hsub : ∀ x ∈ insert w (insert a (insert b (insert (qfInd a w b) (E1 ∩ E1')))),
              x ∈ insert c H := fun x hx => Finset.mem_insert_of_mem (hL hx)
          refine Or.inr ⟨w, hsub _ (by simp), hwL, hwc, hmax, Or.inr (Or.inr (Or.inr (Or.inl
            ⟨a, b, hsub _ (by simp), hsub _ (by simp), hsub _ (by simp), ha1, e.symm, hI, h2, hib.trans_lt h2, ?_⟩)))⟩
          refine zkEx_mono (fun x hx => ⟨hsub x ?_, (hE1 x hx.1).2.trans_lt hI⟩) a (fa_zkEx_and a hE2 hE2')
          simp [hx.1, hx.2]
      · -- an atom
        have hOc : (Om1 : Ordinal.{0}) < c := by rw [hO1]; exact h1θ.trans_le hθ
        have hSC : SC c := by
          rw [← Tf.tf_SC_gamma hOc hI]; exact Lq.lq_gamma_SC _
        have hc1 : Om 1 < c := by rw [← hO1]; exact hOc
        have hs : (1 : Ordinal.{0}) < ω := one_lt_omega0
        have hA : c < S.psi K (Om (1 + 1)) := lt_psi_of_mem hκ hcD.2.1 hc2
        obtain ⟨E, hownE, hEe⟩ := Ui.ui_own_of_SC (s := 1) hs hSC hc1 hA
        have hWE : Om ω ≤ E := not_lt.1 fun h => by
          have h1 := Ui.ui_psi_lt_of_own (s := 1) hownE h
          rw [hEe] at h1
          exact absurd h1 (not_lt.2 hθ)
        have hdE : ¬ S.psi (Om ω) (Om (1 + 1 + 1)) ∣ E := fun hd =>
          absurd (hmax c ⟨E, hownE, hWE, hd, hEe⟩ le_rfl) (not_le.2 hwlt)
        have hne := Vp.vp_nf_ex (S := S) (s := 1) hs hSC hc1 hA
        obtain ⟨hlV, -, -, -, -⟩ := Vp.vpLev_spec hSC hc1 hne
        obtain ⟨hI', hIlt⟩ := Vp.vp_nf hSC hc1 hne
        set γ := Vp.vpLev S 1 c with hγdef
        set y := Vp.vpI S 1 γ c with hydef
        have hγθ : γ < S.psi (Om ω) (Om (1 + 1 + 1)) := by
          by_contra hcc
          have hd := Us.us_dvd_val hs hownE (hI'.trans hEe.symm)
          have h1 : Om (1 + 1) ^ S.psi (Om ω) (Om (1 + 1 + 1)) ∣ Om (1 + 1) ^ γ := opow_dvd_opow _ (not_lt.1 hcc)
          rw [fa_O2_pow_θ2] at h1
          exact hdE (h1.trans hd)
        have hθlt : ConjT.th S < c := (fa_θ_le_Lv hwL).trans_lt hwlt
        have hyz : y < ulH S 1 γ y := by rw [hI']; exact hIlt
        have hzW : ulH S 1 γ y < Om (1 + 1) := by rw [hI']; exact hc2
        have hzD : VbDK S l K (ulH S 1 γ y) := by rw [hI']; exact hcD
        have hzD' : VbDK S l' K (ulH S 1 γ y) := by rw [hI']; exact hcD'
        have hA' : ulH S 1 γ y < S.psi K (Om (1 + 1)) := by rw [hI']; exact hA
        have hθz : ConjT.th S < ulH S 1 γ y := by rw [hI']; exact hθlt
        obtain ⟨B, c', D, hownB, hcB, hcD0, hcond, hcase⟩ := Vp.vp_dec (S := S) (s := 1) hs hyz hA'
        obtain ⟨hγD, -, hDD, hcDD, hTγ, -⟩ :=
          faALc hl hX hKB hown hρ hWK hγθ hyz hzW hzD hθz hownB hcB hcD0 hcond hcase
        obtain ⟨hγD', -, hDD', hcDD', -⟩ :=
          faALc hl' hX' hKB hown' hρ' hWK hγθ hyz hzW hzD' hθz hownB hcB hcD0 hcond hcase
        have hDy : D ≤ y := by rw [← hcD0]; exact le_add_self
        have hcy : c' ≤ y := by rw [← hcD0]; exact le_self_add
        -- `η`
        have hPC := faPC_D (S := S) (l := l) hKB
        have hPC' := faPC_D (S := S) (l := l') hKB
        have hoff : ∀ {P : Ordinal.{0} → Prop}, FaPC P → P D → P (cdOff D) := fun {P} hP hd => by
          unfold cdOff
          split_ifs with h
          · rcases eq_or_ne D 0 with h0 | h0
            · rw [h0, Ordinal.zero_sub]; exact hP.zero
            · exact hP.sub hd hP.one (one_le_iff_ne_zero.2 h0)
          · exact hd
        obtain ⟨ηc, hηc, hηD, hηD', hηy⟩ : ∃ ηc, ((c' = 0 ∧ ηc = D) ∨ (c' ≠ 0 ∧ c' = w ∧ ηc = cdOff D) ∨
            (c' ≠ 0 ∧ c' ≠ w ∧ ηc = c' + cdOff D)) ∧ VbDK S l K ηc ∧ VbDK S l' K ηc ∧ ηc ≤ y := by
          by_cases h0 : c' = 0
          · exact ⟨D, Or.inl ⟨h0, rfl⟩, hDD, hDD', hDy⟩
          by_cases h1 : c' = w
          · exact ⟨cdOff D, Or.inr (Or.inl ⟨h0, h1, rfl⟩), hoff hPC hDD, hoff hPC' hDD', (cdOff_le D).trans hDy⟩
          · refine ⟨c' + cdOff D, Or.inr (Or.inr ⟨h0, h1, rfl⟩), hPC.add hcDD (hoff hPC hDD),
              hPC'.add hcDD' (hoff hPC' hDD'), ?_⟩
            rw [← hcD0]
            exact add_le_add le_rfl (cdOff_le D)
        have hηlt : ηc < c := hηy.trans_lt hIlt
        have hη2 : ηc < Om (1 + 1) := hηlt.trans hc2
        have hηρ : GxCl (upsilon l) (ldAtR S l) ηc := (ldHull_iff hl hX hη2).1 hηD.1
        have hησ : GxCl (upsilon l') (ldAtR S l') ηc := (ldHull_iff hl' hX' hη2).1 hηD'.1
        -- the leaves of the level
        have hO2 := fa_O2_D (S := S) (l := l) hKB
        have hO2' := fa_O2_D (S := S) (l := l') hKB
        have hx2 : VbDK S l K (Om (1 + 1) * (Om (1 + 1) + γ)) := by
          have h := hPC.opow_mul hO2 _ (hPC.add hO2 hγD); rwa [Ky.ky2e] at h
        have hx2' : VbDK S l' K (Om (1 + 1) * (Om (1 + 1) + γ)) := by
          have h := hPC'.opow_mul hO2' _ (hPC'.add hO2' hγD'); rwa [Ky.ky2e] at h
        have hTx2 : vbTK S l K (Om (1 + 1) * (Om (1 + 1) + γ)) = Om1 * (Om1 + vbTK S l K γ) := by
          have h := faT_omul hl hX hKB hO2 (hPC.add hO2 hγD)
          rw [Ky.ky2e, kzT_add hl hX hKB hO2 hγD, fa_T_O2 hl hX hKB, Bt.Om1_opow] at h
          rw [h, hO1]
        have hθS : SC (ConjT.th S) := ConjT.SC_th S
        have hOθ : (Om1 : Ordinal.{0}) < ConjT.th S := by rw [hO1]; exact h1θ
        have hmulθ : IsPrincipal (· * ·) (ConjT.th S) := by
          have h := isPrincipal_mul_omega0_opow_opow (ConjT.th S)
          rwa [Gg.gg_SC_eps hθS, Gg.gg_SC_eps hθS] at h
        have hθq : Om1 * (Om1 + vbTK S l K γ) < ConjT.th S := hmulθ hOθ (hθS.isPrincipal hOθ hTγ)
        have hLex : YvLv S (FaLeafP S l l') (Om1 * (Om1 + vbTK S l K γ)) :=
          faLeafR hl hX hl' hX' hKB le_self_add le_self_add _ (yv_lv_ex hθq) _ hx2 hx2' hTx2
        -- the leaves are below the reading of `c`
        have hΘc : gxTh (upsilon l) (ldAtR S l) c = ulH S 0 (vbTK S l K γ) (vbTK S l K y) := by
          obtain ⟨-, -, -, -, -, -, -, -, h4, -⟩ :=
            faALc hl hX hKB hown hρ hWK hγθ hyz hzW hzD hθz hownB hcB hcD0 hcond hcase
          rw [← hI', ← vbTK_code hl hX hKB hzW hzD.1]
          exact h4
        have hxS : SC (gxTh (upsilon l) (ldAtR S l) c) := by rw [hΘc]; exact ulH_SC _ _
        have hx1 : gxTh (upsilon l) (ldAtR S l) c ≤ Om1 := by
          have h := fa_Θ_lt hl hX hKB hown hρ hWK hAK c hc
          rw [hO1]; exact (h.trans (fa0_lt _)).le
        have hLlt : YvLv S (· < gxTh (upsilon l) (ldAtR S l) c) (Om1 * (Om1 + vbTK S l K γ)) := by
          refine (yv_dat_iff hxS hx1 hθq).1 ?_
          refine (Vg.vg_code_iffK hxS).2 ?_
          have hd : ulD S 0 (vbTK S l K γ) < gxTh (upsilon l) (ldAtR S l) c := by rw [hΘc]; exact ulH_D_lt _ _
          have hK := (ul_vis hxS).1 hd
          have hOK : UlK S 0 (gxTh (upsilon l) (ldAtR S l) c) (Om1) := by
            rw [hO1]; exact UlK.om UlK.one
          have h := ulK_opow_mul hxS (a := Om1) hOK (Om1 + vbTK S l K γ) (UlK.add hOK hK)
          rwa [Rj.rj_Om1_opow] at h
        obtain ⟨L, hLP, hLv⟩ := fa_yv_fin (yvLv_and hLex hLlt)
        choose! g hg using fun u (hu : u ∈ L) => (hLP u hu).1
        have hgprop : ∀ u ∈ L, g u < c := fun u hu => by
          obtain ⟨h1, h2, h3, h4⟩ := hg u hu
          by_contra hcc
          have := gxTh_mono (Z := upsilon l) (At := ldAtR S l) (not_lt.1 hcc)
          rw [h4] at this
          exact absurd (hLP u hu).2 (not_lt.2 this)
        refine hfin (insert w (insert ηc (L.image g))) ?_ fun H hL => ?_
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_image] at hx
          rcases hx with rfl | rfl | ⟨u, hu, rfl⟩
          · exact ⟨hwρ, hwσ, hwlt⟩
          · exact ⟨hηρ, hησ, hηlt⟩
          · obtain ⟨h1, h2, h3, h4⟩ := hg u hu
            exact ⟨h2, h3, hgprop u hu⟩
        · have hsub : ∀ x ∈ insert w (insert ηc (L.image g)), x ∈ insert c H := fun x hx =>
            Finset.mem_insert_of_mem (hL hx)
          have hLeaf : YvLv S (fun u => ∃ e, e ∈ insert c H ∧ e < c ∧ gxTh (upsilon l) (ldAtR S l) e = u)
              (Om1 * (Om1 + vbTK S l K γ)) := hLv.mono fun u hu => by
            obtain ⟨-, -, -, h4⟩ := hg u hu
            exact ⟨g u, hsub _ (by simp only [Finset.mem_insert, Finset.mem_image]; exact Or.inr (Or.inr ⟨u, hu, rfl⟩)),
              hgprop u hu, h4⟩
          have hcz : c = ulH S 1 γ (c' + D) := by rw [hcD0]; exact hI'.symm
          have hyc : c' + D < c := by rw [hcD0]; exact hIlt
          refine Or.inr ⟨w, hsub _ (by simp), hwL, hwc, hmax, Or.inr (Or.inr (Or.inr (Or.inr
            ⟨γ, B, c', D, ηc, hsub _ (by simp), hηlt, hγθ, hcz, hyc, hθlt, hownB, hcB, hcond, ?_, hηc, hLeaf⟩)))⟩
          rw [hcD0]; exact hcase
    · -- `c = ω^a`
      obtain ⟨a, rfl⟩ := indec_eq_opow (indec_iff.2 ⟨hc0, hP⟩)
      have hEa : ω ^ a ≠ a := by
        intro h
        apply hE
        rw [h]; exact h
      have haT : a < ω ^ a := lt_of_le_of_ne (right_le_opow a one_lt_omega0) (Ne.symm hEa)
      have hac : GxCl (upsilon l) (ldAtR S l) a := by
        have := (gxDec hZ hAt _ hc).2
        rwa [log_opow one_lt_omega0] at this
      have hac' : GxCl (upsilon l') (ldAtR S l') a := by
        have := (gxDec hZ' hAt' _ hc').2
        rwa [log_opow one_lt_omega0] at this
      have hwa : w ≤ a := by
        by_contra hlt
        push Not at hlt
        have : ω ^ a < w := by
          conv_rhs => rw [← Gg.gg_SC_eps hwS]
          exact (opow_lt_opow_iff_right one_lt_omega0).2 hlt
        exact absurd hwlt (not_lt.2 this.le)
      obtain ⟨hsc, hsa, -⟩ := fa_Rd_opow hBρ hac hwa hEa
      obtain ⟨hsc', -, -⟩ := fa_Rd_opow hBσ hac' hwa hEa
      refine hfin {w, a, faS0 w a} ?_ fun H hL => ?_
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact ⟨hwρ, hwσ, hwlt⟩
        · exact ⟨hac, hac', haT⟩
        · exact ⟨hsc, hsc', hsa.trans_lt haT⟩
      · exact Or.inr ⟨w, Finset.mem_insert_of_mem (hL (by simp)), hwL, hwc, hmax, Or.inr (Or.inr (Or.inl
          ⟨a, Finset.mem_insert_of_mem (hL (by simp)), Finset.mem_insert_of_mem (hL (by simp)), rfl, hEa, hwa, haT,
            hsa.trans_lt haT⟩))⟩
  · -- a sum
    have hlc : lead c < c := lt_of_le_of_ne (lead_le hc0) fun e =>
      hP (by rw [← e]; exact isPrincipal_add_omega0_opow _)
    have htc : tail c < c := tail_lt hc0
    have hlcode : GxCl (upsilon l) (ldAtR S l) (lead c) := (gxDec hZ hAt c hc).2.opow hZ.1
    have htcode : GxCl (upsilon l) (ldAtR S l) (tail c) := (gxDec hZ hAt c hc).1 _ hlcode (lead_le hc0)
    have hlcode' : GxCl (upsilon l') (ldAtR S l') (lead c) := (gxDec hZ' hAt' c hc').2.opow hZ'.1
    have htcode' : GxCl (upsilon l') (ldAtR S l') (tail c) := (gxDec hZ' hAt' c hc').1 _ hlcode' (lead_le hc0)
    refine hfin {w, lead c, tail c} ?_ fun H hL => ?_
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨hwρ, hwσ, hwlt⟩
      · exact ⟨hlcode, hlcode', hlc⟩
      · exact ⟨htcode, htcode', htc⟩
    · exact Or.inr ⟨w, Finset.mem_insert_of_mem (hL (by simp)), hwL, hwc, hmax, Or.inr (Or.inl
        ⟨lead c, tail c, Finset.mem_insert_of_mem (hL (by simp)), Finset.mem_insert_of_mem (hL (by simp)),
          (lead_add_tail hc0).symm, hlc, htc⟩)⟩

/-- **Finitely many codes of both hulls lie in one finite set of codes of both hulls, closed under the
parts.** -/
theorem faClose_fin (s : Finset Ordinal.{0})
    (hs : ∀ c ∈ s, GxCl (upsilon l) (ldAtR S l) c ∧ GxCl (upsilon l') (ldAtR S l') c ∧ c < Om (1 + 1)) :
    ∃ H : Finset Ordinal.{0}, s ⊆ H ∧ ∀ z ∈ H, (GxCl (upsilon l) (ldAtR S l) z ∧ GxCl (upsilon l') (ldAtR S l') z ∧
      z < Om (1 + 1)) ∧ FaStep S l K H z := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp⟩
  | @insert a s _ IH =>
    obtain ⟨H1, hs1, h1⟩ := IH fun c hc => hs c (Finset.mem_insert_of_mem hc)
    obtain ⟨hac, hac', ha2⟩ := hs a (Finset.mem_insert_self a s)
    obtain ⟨H2, ha, h2⟩ := faClose hl hX hl' hX' hKB hown hρ hown' hρ' hWK hAK hAK' a hac hac' ha2
    refine ⟨H1 ∪ H2, ?_, fun z hz => ?_⟩
    · intro w hw
      rcases Finset.mem_insert.1 hw with rfl | hw
      · exact Finset.mem_union_right _ ha
      · exact Finset.mem_union_left _ (hs1 hw)
    · rcases Finset.mem_union.1 hz with hz | hz
      · exact ⟨(h1 z hz).1, (h1 z hz).2.mono Finset.subset_union_left⟩
      · obtain ⟨⟨a1, a2, a3⟩, a4⟩ := h2 z hz
        exact ⟨⟨a1, a2, a3.trans_lt ha2⟩, a4.mono Finset.subset_union_right⟩

end Two


end Googology.Trans.PoR.InaccPsi.R2.Fa

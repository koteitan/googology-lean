import Googology.Trans.PoR.InaccPsi.R2.MxLay

/-!
# The reading moves below `sup_j K_j`: the hull transport through every layer

`B_n = Bc.bcB S n`, `K_0 = Ω₁`, `K_{j+1} = ψ_{Ω₂}(K_j)` (`mxKs`), `GxCl ρ (mxAtL S ρ j)` the codes of layer `j`
(`R2.MxLay`), `Θ = gxTh`, `r(λ) = k_λ(Θ_λ(m_λ))`.

* `mxGxStep` (**one layer**: if every atom below a strongly critical bound `K ≥ Ω₁` moves — `B_n s` an atom,
  `Θ'(B_n s) = B_n(Θ s)`, `Θ s < X` — then every code below `K` moves, by induction on the code as `Mx.mxAt_move`);
* `mxAtL_move` (**the hull transport through every layer**, by induction on `j`: the atom `ψ_{Ω₂}(α)` of layer
  `j + 1` has `Θ = ψ_{Ω₁}(A + 1 + Θ(α))` (`Mx.mxThL_atom`), `B_n` maps it to `ψ_{Ω₂}(B_n α)` (`Mx.mxB_atom`) and
  `ψ_{Ω₁}(A + 1 + Θ(α))` to `ψ_{Ω₁}(A' + 1 + B_n(Θ(α)))` (`Mx.mxB_psi_add`), and `α` moves by the previous layer);
* `mxThMove_L` (**`MxThMove` at every long code `m_λ < K_j` for some `j`**, no hypothesis);
* `MxThMoveW S` (a hypothesis name): `MxThMove` at the codes with `K_j ≤ m_λ ≤ θ` for every `j`; `mxThMove_of_W`
  (**`MxThMoveW` gives `MxThMove`**), `mxThMoveW_of` (`MxThMove` gives `MxThMoveW`), `mxRoad5`.

No new axiom.  New definition: the hypothesis name `MxThMoveW`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Mx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Sf

variable {S : InaccSeq.{0}}

/-- **One layer of the hull transport**: if every atom below `K` moves, every code below `K` moves. -/
theorem mxGxStep {n : ℕ} {ρ ρ' X K : Ordinal.{0}} {At At' : Set Ordinal.{0}} (hρSC : SC ρ) (hρ1 : ρ < Om 1)
    (hρ'SC : SC ρ') (hρ'1 : ρ' < Om 1) (hAt : GxAt At) (hAt' : GxAt At') (hB : Bc.bcB S n ρ = ρ')
    (hX : SC X) (hρX : ρ < X) (hXL : X < Nc.ncL S ω) (hK : SC K) (hK1 : Om 1 ≤ K)
    (hatom : ∀ s ∈ At, s < K → MvD S s ∧ Bc.bcB S n s ∈ At' ∧ Bc.bcB S n s < K ∧ gxTh ρ At s < X ∧
      gxTh ρ' At' (Bc.bcB S n s) = Bc.bcB S n (gxTh ρ At s)) :
    ∀ x, GxCl ρ At x → x < K → MvD S x ∧ GxCl ρ' At' (Bc.bcB S n x) ∧
      Bc.bcB S n x < K ∧ gxTh ρ At x < X ∧ gxTh ρ' At' (Bc.bcB S n x) = Bc.bcB S n (gxTh ρ At x) := by
  have hρL : ρ < Nc.ncL S ω := hρX.trans hXL
  have hXp : IsPrincipal (· + ·) X := hX.isPrincipal
  have hKp : IsPrincipal (· + ·) K := hK.isPrincipal
  have hKo : ∀ a < K, ω ^ a < K := fun a ha => by
    have := hK.2 0 hK.1 a ha; rwa [veblen_zero_apply] at this
  have hXo : ∀ a < X, ω ^ a < X := fun a ha => by
    have := hX.2 0 hX.1 a ha; rwa [veblen_zero_apply] at this
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx hxK
  rcases lt_trichotomy x (Om 1) with hx1 | hx1 | hx1
  · have hxρ : x < ρ := GxCl.lt_of_lt_Om1 hρSC hAt hx hx1
    have hxL : x < Nc.ncL S ω := hxρ.trans hρL
    have hBx : Bc.bcB S n x < ρ' := by rw [← hB]; exact (Bc.bcB_lt_iff hxL hρL).2 hxρ
    refine ⟨mvD_of_lt hxL, GxCl.small hBx, (hBx.trans hρ'1).trans_le hK1, ?_, ?_⟩
    · rw [gxTh_small hxρ.le]; exact hxρ.trans hρX
    · rw [gxTh_small hxρ.le, gxTh_small hBx.le]
  · subst hx1
    obtain ⟨hD, hBO⟩ := mvB_Om1 (S := S) (k := n)
    refine ⟨hD, by rw [hBO]; exact GxCl.om, by rw [hBO]; exact hxK, ?_, ?_⟩
    · rw [gxTh_Om1 hρSC hρ1 hAt]; exact hρX
    · rw [hBO, gxTh_Om1 hρSC hρ1 hAt, gxTh_Om1 hρ'SC hρ'1 hAt', hB]
  · have hx0 : x ≠ 0 := (lt_of_le_of_lt zero_le hx1).ne'
    by_cases hSCx : SC x
    · have hs := gxSC_atom hρ1 hx hSCx hx1
      obtain ⟨hD, hBs, hBK, hth, he⟩ := hatom x hs hxK
      exact ⟨hD, GxCl.atom hBs, hBK, hth, he⟩
    by_cases hE : ω ^ x = x
    · obtain ⟨hdec, hax, hbx, -⟩ := mxDec hE (pos_iff_ne_zero.2 hx0) hSCx
      generalize invVeblen₁ x = a at hdec hax
      generalize invVeblen₂ x = b at hdec hbx
      obtain ⟨hga, hgb⟩ := gxDecV hρSC.1 hAt hx a b hdec hbx
      obtain ⟨hDa, hga', haK, hta, hea⟩ := IH a hax hga (hax.trans hxK)
      obtain ⟨hDb, hgb', hbK, htb, heb⟩ := IH b hbx hgb (hbx.trans hxK)
      have hax' : a < veblen a b := by rw [hdec]; exact hax
      have hbx' : b < veblen a b := by rw [hdec]; exact hbx
      obtain ⟨hDx, hBx⟩ := mwB_phi (k := n) hDa hDb hax' hbx'
      have hth : gxTh ρ At (veblen a b) = veblen (gxTh ρ At a) (gxTh ρ At b) := gxTh_phi hρSC hAt a hga b hgb
      have hta' : gxTh ρ At a < veblen (gxTh ρ At a) (gxTh ρ At b) := by
        rw [← hth]; exact gxTh_lt hga hax'
      have htb' : gxTh ρ At b < veblen (gxTh ρ At a) (gxTh ρ At b) := by
        rw [← hth]; exact gxTh_lt hgb hbx'
      obtain ⟨-, hBt⟩ := mwB_phi (k := n) (mvD_of_lt (hta.trans hXL)) (mvD_of_lt (htb.trans hXL)) hta' htb'
      rw [← hdec]
      refine ⟨hDx, ?_, ?_, ?_, ?_⟩
      · rw [hBx]; exact GxCl.phi hga' hgb'
      · rw [hBx]; exact hK.2 _ haK _ hbK
      · rw [hth]; exact hX.2 _ hta _ htb
      · rw [hBx, gxTh_phi hρ'SC hAt' _ hga' _ hgb', hea, heb, hth, hBt]
    · obtain ⟨a, ha⟩ : ∃ a, a = log ω x := ⟨_, rfl⟩
      have hlead : ω ^ a ≤ x := by rw [ha]; exact opow_log_le_self ω hx0
      have hxlt : x < ω ^ a * ω := by
        rw [← opow_succ, ha]; exact lt_opow_succ_log_self one_lt_omega0 x
      have hga : GxCl ρ At a := by rw [ha]; exact (gxDec hρSC hAt x hx).2
      have hgl : GxCl ρ At (ω ^ a) := GxCl.opow hρSC.1 hga
      have hgr : GxCl ρ At (x - ω ^ a) := (gxDec hρSC hAt x hx).1 _ hgl hlead
      have hdec : ω ^ a + (x - ω ^ a) = x := Ordinal.add_sub_cancel_of_le hlead
      by_cases hr : x - ω ^ a = 0
      · have hxa : ω ^ a = x := by rw [hr, add_zero] at hdec; exact hdec
        have hax : a < x := by
          rcases (right_le_opow a one_lt_omega0).lt_or_eq with h | h
          · rwa [hxa] at h
          · exfalso; apply hE; rw [← hxa]; exact congrArg (ω ^ ·) h.symm
        obtain ⟨hDa, hga', haK, hta, hea⟩ := IH a hax hga (hax.trans hxK)
        have hne : ω ^ a ≠ a := fun h => hax.ne (h.symm.trans hxa)
        obtain ⟨hDx, hBx⟩ := mvB_opow (k := n) hDa hne
        subst hxa
        have hta' : ω ^ gxTh ρ At a < X := hXo _ hta
        refine ⟨hDx, ?_, ?_, ?_, ?_⟩
        · rw [hBx]; exact GxCl.opow hρ'SC.1 hga'
        · rw [hBx]; exact hKo _ haK
        · rw [gxTh_opow hρSC hAt hga]; exact hta'
        · rw [hBx, gxTh_opow hρ'SC hAt' hga', hea, gxTh_opow hρSC hAt hga, Tp.tpOpowB (hta'.trans hXL)]
      · obtain ⟨r, hr'⟩ : ∃ r, r = x - ω ^ a := ⟨_, rfl⟩
        rw [← hr'] at hgr hdec hr
        have hlx : ω ^ a < x := by
          rw [← hdec]; exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 hr)
        have hrx : r < x := by
          refine lt_of_le_of_ne (by rw [← hdec]; exact le_add_self) fun e => ?_
          have h' : ω ^ a + x = x := by
            calc ω ^ a + x = ω ^ a + r := by rw [e]
              _ = x := hdec
          have := Ordinal.add_eq_right_iff_mul_omega0_le.1 h'
          exact absurd (lt_of_lt_of_le hxlt this) (lt_irrefl _)
        obtain ⟨hDl, hgl', hlK, htl, hel⟩ := IH _ hlx hgl (hlx.trans hxK)
        obtain ⟨hDr, hgr', hrK, htr, her⟩ := IH r hrx hgr (hrx.trans hxK)
        obtain ⟨hDx, hBx⟩ := mvB_add (k := n) hDl hDr
        have hts : gxTh ρ At (ω ^ a + r) = gxTh ρ At (ω ^ a) + gxTh ρ At r := gxTh_add hρSC hAt hgl r
        rw [← hdec]
        refine ⟨hDx, ?_, ?_, ?_, ?_⟩
        · rw [hBx]; exact GxCl.add hgl' hgr'
        · rw [hBx]; exact hKp hlK hrK
        · rw [hts]; exact hXp htl htr
        · rw [hBx, gxTh_add hρ'SC hAt' hgl', hel, her, hts, Bc.bcB_add (htl.trans hXL) (htr.trans hXL)]

/-- **The hull transport through every layer.** -/
theorem mxAtL_move {n : ℕ} {ρ ρ' A A' X : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1)))
    (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1))) (hρ : S.psi A (Om 1) = ρ) (hρ' : S.psi A' (Om 1) = ρ')
    (hB : Bc.bcB S n ρ = ρ') (hX : SC X) (hρX : ρ < X) (hXL : X < Nc.ncL S ω)
    (hbX : ∀ d, d < Om 1 → S.psi (A + d) (Om 1) < X)
    (hBψ : ∀ d, d < Om 1 → d < S.psi (A + d) (Om 1) →
      Bc.bcB S n (S.psi (A + d) (Om 1)) = S.psi (A' + Bc.bcB S n d) (Om 1)) :
    ∀ j x, GxCl ρ (mxAtL S ρ j) x → x < mxKs S j → MvD S x ∧
      GxCl ρ' (mxAtL S ρ' j) (Bc.bcB S n x) ∧ Bc.bcB S n x < mxKs S j ∧ gxTh ρ (mxAtL S ρ j) x < X ∧
      gxTh ρ' (mxAtL S ρ' j) (Bc.bcB S n x) = Bc.bcB S n (gxTh ρ (mxAtL S ρ j) x) := by
  have hρSC : SC ρ := hρ ▸ SC_psi Low.InR_Om_one A
  have hρ1 : ρ < Om 1 := hρ ▸ psi_lt Low.InR_Om_one A
  have hρ'SC : SC ρ' := hρ' ▸ SC_psi Low.InR_Om_one A'
  have hρ'1 : ρ' < Om 1 := hρ' ▸ psi_lt Low.InR_Om_one A'
  have hX1 : X < Om 1 := hXL.trans (InaccSeq.psi_lt Low.InR_Om_one _)
  have h1L : (1 : Ordinal.{0}) < Nc.ncL S ω := one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S ω))
  intro j
  induction j with
  | zero =>
    refine mxGxStep hρSC hρ1 hρ'SC hρ'1 (mxAtL_GxAt ρ 0) (mxAtL_GxAt ρ' 0) hB hX hρX hXL (mxKs_SC 0)
      (mxOm1_le_Ks 0) ?_
    intro s hs; exact absurd hs (Set.notMem_empty _)
  | succ j IHj =>
    refine mxGxStep hρSC hρ1 hρ'SC hρ'1 (mxAtL_GxAt ρ (j + 1)) (mxAtL_GxAt ρ' (j + 1)) hB hX hρX hXL
      (mxKs_SC (j + 1)) (mxOm1_le_Ks (j + 1)) ?_
    rintro s ⟨α, hα, hαK, rfl⟩ -
    obtain ⟨hDα, hBα, hBαK, hθα, heα⟩ := IHj α hα hαK
    have hown : α ∈ S.CSet α (S.psi α (Om (1 + 1))) := CSet.of_lt (mxPsi2_gt j α hαK)
    obtain ⟨hD, hBa⟩ := mxB_atom (n := n) hDα hown
    have hθ1 : gxTh ρ (mxAtL S ρ j) α < Om 1 := hθα.trans hX1
    have hθL : gxTh ρ (mxAtL S ρ j) α < Nc.ncL S ω := hθα.trans hXL
    -- the readings of `ψ_{Ω₂}(α)` and of its image
    have hTh : gxTh ρ (mxAtL S ρ (j + 1)) (S.psi α (Om (1 + 1))) =
        S.psi (A + (1 + gxTh ρ (mxAtL S ρ j) α)) (Om 1) := by
      rw [mxThL_atom hA hρ j α hα hαK, ← mxThL_congr ρ j hαK.le, add_assoc]
    have hTh' : gxTh ρ' (mxAtL S ρ' (j + 1)) (S.psi (Bc.bcB S n α) (Om (1 + 1))) =
        S.psi (A' + (1 + gxTh ρ' (mxAtL S ρ' j) (Bc.bcB S n α))) (Om 1) := by
      rw [mxThL_atom hA' hρ' j _ hBα hBαK, ← mxThL_congr ρ' j hBαK.le, add_assoc]
    have h1θ : 1 + gxTh ρ (mxAtL S ρ j) α < Om 1 := Ph.ph_SC_Om1.isPrincipal one_lt_Om1 hθ1
    have hθT : gxTh ρ (mxAtL S ρ j) α < gxTh ρ (mxAtL S ρ (j + 1)) (S.psi α (Om (1 + 1))) := by
      rw [mxThL_congr ρ j hαK.le]
      exact gxTh_lt (hα.mono le_rfl (mxAtL_mono ρ j)) (mxPsi2_gt j α hαK)
    have hTSC : SC (gxTh ρ (mxAtL S ρ (j + 1)) (S.psi α (Om (1 + 1)))) :=
      gxTh_SC hρSC (mxAtL_GxAt ρ (j + 1)) (SC_psi (InR_Om_succ 1) α) (hρ1.trans (psiS_bounds (S := S) α 1).1)
    have hdlt : 1 + gxTh ρ (mxAtL S ρ j) α < S.psi (A + (1 + gxTh ρ (mxAtL S ρ j) α)) (Om 1) := by
      rw [← hTh]; exact hTSC.isPrincipal (gg_one_lt_of_SC hTSC) hθT
    refine ⟨hD, by rw [hBa]; exact ⟨_, hBα, hBαK, rfl⟩, by rw [hBa]; exact mxPsi2_ltL hBαK (mxKs_lt_succ j),
      by rw [hTh]; exact hbX _ h1θ, ?_⟩
    rw [hBa, hTh', hTh, hBψ _ h1θ hdlt, Bc.bcB_add h1L hθL, mwB_one, heα]

/-! ## `MxThMove` below every `K_j` -/

/-- **`MxThMove` at every long code `m_λ < K_j`** (for some `j`). -/
theorem mxThMove_L {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
    (he : ggGam < cdExp (cdEta S l)) {j : ℕ} (hK : cdCode S l < mxKs S j) :
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l') := by
  have hl := hR.1
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans hδr
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hX : upsilon l < Nm.Pv S (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0})) := by
    rw [← Lw.lw_L_eq S]; exact h2
  have hX' : upsilon l' < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq S, ← hB]; exact Bc.bcB_bound' S n _ h2
  obtain ⟨hg, -, -, hpv⟩ := cdEta_pv_spec (S := S) hl.1 hX
  set η := cdEta S l with hη_def
  set A := ConjT.Aη S η with hA_def
  have hρA : S.psi A (Om 1) = upsilon l := hpv
  have hAL : A < S.Lam := (sfA_lt (S := S) (n := n) (hpv ▸ h2)).2
  have hown : A ∈ S.CSet A (S.psi A (Om 1)) := sfOwn hg hAL
  set e := cdExp η with he_def
  have hωe : (ω : Ordinal.{0}) ≤ e := (Lw.lw_omega_lt_SC ggGam_spec.1).le.trans he.le
  have hWA : Om ω ≤ A := le_self_add
  have h2W : Om (1 + 1 : Ordinal.{0}) < Om ω := Om_lt_Om.2 (by
    rw [one_add_one_eq_two]; exact natCast_lt_omega0 2)
  -- the code is `e`
  have he2 : e < Om (1 + 1) := by
    by_contra h
    have hc : cdCode S l = cdPi S η := by
      show cdCodeOf S η = _; unfold cdCodeOf; rw [if_neg h]
    have hle : mxKs S j ≤ cdPi S η := by
      cases j with
      | zero => exact (psiS_bounds (S := S) _ 1).1.le
      | succ j =>
        exact (psi_mono (S := S) (InR_Om_succ 1) (((mxKs_lt_Om2 j).trans h2W).le.trans hWA)).1
    exact absurd (hc ▸ hK) (not_lt.2 hle)
  have hcode : cdCode S l = e := by
    show cdCodeOf S η = e
    rw [cdCodeOf_of_lt he2]; unfold cdOff; rw [if_neg (not_lt.2 hωe)]
  have heK : e < mxKs S j := hcode ▸ hK
  -- `e` is a code of layer `j`
  have hH := ggExp_HCl (Nn.nnGood_HCl hg)
  have hmemH : e ∈ cdHull S l := by unfold cdHull; rw [← hpv]; exact hH.mem_CSet
  have hge : GxCl (upsilon l) (mxAtL S (upsilon l) j) e := (mxHullL_iff hl hX j e heK).1 hmemH
  have hmem0 : e ∈ ⋃ a, S.CSet a 0 := by
    refine Set.mem_iUnion.2 ⟨A, mxHull_sub0 ?_⟩
    have : e ∈ S.CSet A (upsilon l) := hmemH
    rwa [← hρA] at this
  obtain ⟨η', -, hBη', hη', hexp'⟩ := mvExp_move hl.1 h1 h2 (heK.trans_le (mxKs_le_th j)) hmem0
  have hl'eq : l' = Bt.iota S η' := Tp.tpUps_inj (hB.symm.trans hBη')
  -- the bounds `ψ_{Ω₁}(A + d) < L(n+2)` for `d < Ω₁`
  have hu1 : upsilon (l + 1) < cdDelta l :=
    upsilon_normal.strictMono (by
      calc l + 1 < l + ω := (add_lt_add_iff_left l).2 one_lt_omega0
        _ < l + ω + 1 := lt_add_one _)
  have hsucc := mxUps_succ hl hX
  have hθ1 : Om (1 : Ordinal.{0}) < ConjT.th S := (psiS_bounds (S := S) _ 1).1
  have hdθ : ∀ d, d < Om 1 → S.psi (A + d) (Om 1) < Bc.bcC S (n + 1) := by
    intro d hd
    have h3 : S.psi (A + d) (Om 1) ≤ upsilon (l + 1) := by
      rw [hsucc]; exact (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left A).2 (hd.trans hθ1).le)).1
    exact (h3.trans_lt hu1).trans hδr
  have hρ0 : (0 : Ordinal.{0}) < Pv S η := hpv ▸ mvUps_pos hl
  obtain ⟨A', hA', hBP, -⟩ := mxB_psi_add (n := n) hg (hpv ▸ h1.le) (by rw [add_zero]; exact hρ0)
    (by rw [add_zero]; show Pv S η < Bc.bcC S (n + 1); rw [hpv]; exact h2)
  have hρA' : S.psi A' (Om 1) = upsilon l' := by rw [← hBP, hpv, hB]
  have hBψ : ∀ d, d < Om 1 → d < S.psi (A + d) (Om 1) →
      Bc.bcB S n (S.psi (A + d) (Om 1)) = S.psi (A' + Bc.bcB S n d) (Om 1) := by
    intro d hd1 hdA
    obtain ⟨A'', hA'', hBP'', hBd⟩ := mxB_psi_add (n := n) hg (hpv ▸ h1.le) hdA (hdθ d hd1)
    have : A'' = A' := mxPsi_inj hA'' hA' (by rw [← hBP'', hBP])
    rw [hBd, this]
  obtain ⟨hDe, -, hBeK, -, hEq⟩ := mxAtL_move (n := n) hown hA' hρA hρA' hB (Lw.lw_L_SC S _) h2 hLw hdθ hBψ
    j e hge heK
  -- the image code is `B_n e`
  have hΩe : Om (1 : Ordinal.{0}) < Bc.bcB S n e := by
    obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
    have h3 := (mvB_lt_iff (k := n) hDO hDe).2 (ggGam_spec.2.trans he)
    rwa [hBO] at h3
  have hωBe : (ω : Ordinal.{0}) ≤ Bc.bcB S n e := (Lw.lw_omega_lt_SC Ph.ph_SC_Om1).le.trans hΩe.le
  have hcode' : cdCode S l' = Bc.bcB S n e := by
    rw [hl'eq]
    show cdCodeOf S (cdEta S (Bt.iota S η')) = _
    rw [hη', cdCodeOf_of_lt (hexp' ▸ hBeK.trans (mxKs_lt_Om2 j)), hexp']
    unfold cdOff; rw [if_neg (not_lt.2 hωBe)]
  rw [hcode, hcode', mxThetaL hl hX j heK.le, mxThetaL hl' hX' j hBeK.le, hEq]

/-- `MxThMove` at the long codes with `K_j ≤ m_λ ≤ θ` for every `j`. -/
def MxThMoveW (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    ggGam < cdExp (cdEta S l) → cdCode S l ≤ ConjT.th S → (∀ j : ℕ, mxKs S j ≤ cdCode S l) →
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l')

/-- **`MxThMoveW` gives `MxThMove`.** -/
theorem mxThMove_of_W (h : MxThMoveW S) : MxThMove S := by
  intro n l l' hR h1 hr hl' hB hm he hθ
  by_cases hK : ∃ j : ℕ, cdCode S l < mxKs S j
  · obtain ⟨j, hj⟩ := hK
    exact mxThMove_L hR h1 hr hl' hB he hj
  · push Not at hK
    exact h n l l' hR h1 hr hl' hB hm he hθ hK

/-- `MxThMove` gives `MxThMoveW` (so `MxThMoveW` is the weaker hypothesis). -/
theorem mxThMoveW_of (h : MxThMove S) : MxThMoveW S :=
  fun n l l' hR h1 hr hl' hB hm he hθ _ => h n l l' hR h1 hr hl' hB hm he hθ

/-- **The road with `MxLhTopG`, `L(ω+1) ≤ ν_C → MxThMoveW` and `L(ω+1) ≤ ν_C → MxEQth`.** -/
theorem mxRoad5 (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (hth : Nc.ncL S (ω + 1) ≤ nuC → MxThMoveW S)
    (hhi : Nc.ncL S (ω + 1) ≤ nuC → MxEQth S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  mxRoad3 hU hO hL hV hN hlh (fun hν => mxThMove_of_W (hth hν)) hhi

end Googology.Trans.PoR.InaccPsi.R2.Mx

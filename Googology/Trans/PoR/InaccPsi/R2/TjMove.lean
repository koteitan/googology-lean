import Googology.Trans.PoR.InaccPsi.R2.TjSys

/-!
# The move of the level system up to `G = φ(Ω₂, 1)` under `B_n`, code levels included

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `Θ' = gxTh ρ_{λ'} (ldAtR λ')`, `W^E = Ω₂^E`,
`Ω^x = Ω₁^x`, `Θ̂_L = Td.tdThL`, `G = φ(Ω₂, 1)`.  The move hypothesis `IHm` as in `St.StLSB` (every code
`x < B` of `λ` moves with its reading).

* `tjB_fix` (**`B_n` keeps the fixed points of `φ(a, ·)` with a moving level**: `φ(a, y) = y` gives
  `φ(B_n a, B_n y) = B_n y`; `Mw.mwB_fixA` without `B_n a = a`), `tjB_veb` (**`B_n(φ(a, y)) = φ(B_n a, B_n y)` for
  every `a < y` in `MvD`, fixed points included**), `tjB_G` (`B_n G = G`), `tjThL_zero`;
* `tjB_node` (**THE MOVE OF A NODE WITH A CODE LEVEL** with the image side by `tjB_veb`, so no hypothesis that the
  image node is off its fixed points);
* `tjB_thH` (**THE MOVE OF THE EXPONENTS BELOW `G`**, including **`Θ̂'_L(B_n E) = B_n(Θ̂_L E)`**: at a node the
  level `a` is a code below `B` (`Td.tdCl_lev_lt`), moved by `IHm`);
* `tjLSB` (**`St.StLSB S n λ λ' G Θ̂_L`**).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj
  Googology.Trans.PoR.InaccPsi.R2.St
  Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td Googology.Trans.PoR.InaccPsi.R2.Tg

variable {S : InaccSeq.{0}}

open Googology.Notation.InaccPsi.Term in
/-- **`B_n` keeps the fixed points of `φ(a, ·)` with a moving level**: `φ(a, y) = y` gives
`φ(B_n a, B_n y) = B_n y`. -/
theorem tjB_fix {k : ℕ} {a y : Ordinal.{0}} (hDa : MvD S a) (hy : MvD S y) (hfix : veblen a y = y) :
    veblen (Bc.bcB S k a) (Bc.bcB S k y) = Bc.bcB S k y := by
  obtain ⟨hN, hv⟩ := Bc.bcNf_spec S hy.1
  have hI : Indec y := by rw [← hfix]; exact mw_veblen_indec _ _
  have hP : (Bc.bcNf S y).isPrin = true := Bc.isPrin_of_indec hN (by rw [hv]; exact hI)
  have hay : a < y := by
    have h1 : a ≤ y := by have := left_le_veblen a y; rwa [hfix] at this
    refine lt_of_le_of_ne h1 fun e => ?_
    have h2 : a < veblen a a := lt_veblen a
    have h3 : veblen a y = y := hfix
    rw [← e] at h3
    rw [h3] at h2
    exact lt_irrefl _ h2
  have hBay : Bc.bcB S k a < Bc.bcB S k y := (mvB_lt_iff (k := k) hDa hy).2 hay
  have key : ∀ t : Term, NF t → Bc.bcD S t → Term.val S t = y → t.isPrin = true →
      veblen (Bc.bcB S k a) (Term.val S (Bc.bcSig (Bc.bcPre (k + 1)) Bc.bcPreW t)) =
        Term.val S (Bc.bcSig (Bc.bcPre (k + 1)) Bc.bcPreW t) := by
    intro t hN hD hv hP
    have hBt : Bc.bcB S k y = Term.val S (Bc.bcSig (Bc.bcPre (k + 1)) Bc.bcPreW t) := by
      unfold Bc.bcB; rw [← hv, Bc.bcNf_val S hN]
    cases t with
    | zero => simp [Term.isPrin, Term.isSC] at hP
    | add _ _ => simp [Term.isPrin, Term.isSC] at hP
    | phi c d =>
      have hdlt : Term.val S d < Term.val S (Term.phi c d) := (cmp_lt_iff S hN.2.1 hN).1 hN.2.2.2
      have hv' : veblen (Term.val S c) (Term.val S d) = y := hv
      have hmc : a < Term.val S c := by
        have e : veblen a (veblen (Term.val S c) (Term.val S d)) = veblen (Term.val S c) (Term.val S d) := by
          rw [hv']; exact hfix
        rcases veblen_eq_veblen_iff.1 e with ⟨_, h2⟩ | ⟨h1, _⟩ | ⟨_, h2⟩
        · exfalso
          have : Term.val S d = Term.val S (Term.phi c d) := by rw [← h2]; rfl
          exact absurd this hdlt.ne
        · exact h1
        · exfalso
          have : Term.val S d = Term.val S (Term.phi c d) := by rw [← h2, e]; rfl
          exact absurd this hdlt.ne
      have hDc : Bc.bcD S c := ⟨hN.1, hD.2.1⟩
      have hlt := (mvB_lt_iff (k := k) hDa (mvD_of_term hDc)).2 hmc
      rw [mvB_term hDc] at hlt
      simp only [Bc.bcSig_phi, Term.val]
      exact veblen_veblen_of_lt hlt _
    | _ =>
      have hsc := SC_val S (Bc.bc_NF (k := k) hD) (by rw [Bc.isSC_bcSig]; simpa [Term.isPrin] using hP)
      exact hsc.veblen_right (hBt ▸ hBay)
  unfold Bc.bcB
  exact key _ hN hy.2 hv hP

/-- **`B_n(φ(a, y)) = φ(B_n a, B_n y)`** for every `a < y` in `MvD`, fixed points of `φ(a, ·)` included. -/
theorem tjB_veb {k : ℕ} {a y : Ordinal.{0}} (hDa : MvD S a) (hy : MvD S y) (hay : a < y) :
    MvD S (veblen a y) ∧ Bc.bcB S k (veblen a y) = veblen (Bc.bcB S k a) (Bc.bcB S k y) := by
  by_cases hfix : veblen a y = y
  · rw [hfix]; exact ⟨hy, (tjB_fix hDa hy hfix).symm⟩
  · have hy' : y < veblen a y := lt_of_le_of_ne (right_le_veblen _ _) (Ne.symm hfix)
    exact mwB_phi (k := k) hDa hy (hay.trans hy') hy'

theorem tjB_G {n : ℕ} : MvD S (veblen (Om (1 + 1)) 1) ∧ Bc.bcB S n (veblen (Om (1 + 1)) 1) = veblen (Om (1 + 1)) 1 := by
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  have h1G : (1 : Ordinal.{0}) < veblen (Om (1 + 1)) 1 := (gg_one_lt_of_SC ldOm2_SC).trans tgOm_lt_G
  obtain ⟨hD, hB⟩ := mwB_phi (k := n) hD2 hD1 tgOm_lt_G h1G
  rw [hB2, mwB_one] at hB
  exact ⟨hD, hB⟩

theorem tjThL_zero (l : Ordinal.{0}) : tdThL S l 0 = 0 := by unfold tdThL; rw [taTm_zero]; rfl

/-- **THE MOVE OF A NODE WITH A CODE LEVEL**: `B_n φ(a, Ω₂ + z) = φ(B_n a, Ω₂ + B_n z)` (off the fixed points) and
`Θ̂'_L(B_n E) = B_n(Θ̂_L E)`, the image side by `tjB_veb`. -/
theorem tjB_node {n : ℕ} {l l' a z : Ordinal.{0}} (hDa : MvD S a) (hDz : MvD S z) (ha1 : 1 ≤ a)
    (haW : a < Om (1 + 1)) (hz1 : 1 ≤ z) (hlt : Om (1 + 1) + z < veblen a (Om (1 + 1) + z))
    (hDΘa : MvD S (gxTh (upsilon l) (ldAtR S l) a)) (hΘaO : gxTh (upsilon l) (ldAtR S l) a < Om 1)
    (hDΘz : MvD S (tdThL S l z))
    (hBa : gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n a) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) a))
    (hBz : tdThL S l' (Bc.bcB S n z) = Bc.bcB S n (tdThL S l z)) :
    MvD S (veblen a (Om (1 + 1) + z)) ∧
      Bc.bcB S n (veblen a (Om (1 + 1) + z)) = veblen (Bc.bcB S n a) (Om (1 + 1) + Bc.bcB S n z) ∧
      Om (1 + 1) + Bc.bcB S n z < veblen (Bc.bcB S n a) (Om (1 + 1) + Bc.bcB S n z) ∧
      MvD S (tdThL S l (veblen a (Om (1 + 1) + z))) ∧
      Bc.bcB S n (tdThL S l (veblen a (Om (1 + 1) + z))) =
        veblen (Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) a)) (Om 1 + Bc.bcB S n (tdThL S l z)) ∧
      tdThL S l' (Bc.bcB S n (veblen a (Om (1 + 1) + z))) =
        Bc.bcB S n (tdThL S l (veblen a (Om (1 + 1) + z))) := by
  have ha0 : a ≠ 0 := (zero_lt_one.trans_le ha1).ne'
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  obtain ⟨hDy, hBy⟩ := mvB_add (k := n) hD2 hDz
  rw [hB2] at hBy
  have hay : a < Om (1 + 1) + z := haW.trans_le le_self_add
  obtain ⟨hDE, hBE⟩ := mwB_phi (k := n) hDa hDy (hay.trans hlt) hlt
  rw [hBy] at hBE
  have hBlt : Om (1 + 1) + Bc.bcB S n z < veblen (Bc.bcB S n a) (Om (1 + 1) + Bc.bcB S n z) := by
    have := (mvB_lt_iff (k := n) hDy hDE).2 hlt
    rwa [hBy, hBE] at this
  have hBa1 : 1 ≤ Bc.bcB S n a := by have := leB_le (n := n) hD1 hDa ha1; rwa [mwB_one] at this
  have hBz1 : 1 ≤ Bc.bcB S n z := by have := leB_le (n := n) hD1 hDz hz1; rwa [mwB_one] at this
  -- the image side
  obtain ⟨hDb, hBb⟩ := mvB_add (k := n) hDO hDΘz
  rw [hBO] at hBb
  have hΘab : gxTh (upsilon l) (ldAtR S l) a < Om 1 + tdThL S l z := hΘaO.trans_le le_self_add
  obtain ⟨hDΘE, hBΘE⟩ := tjB_veb (k := n) hDΘa hDb hΘab
  rw [hBb] at hBΘE
  rw [← tdThL_veb ha0 hz1 hlt] at hDΘE hBΘE
  refine ⟨hDE, hBE, hBlt, hDΘE, hBΘE, ?_⟩
  rw [hBE, tdThL_veb (l := l') (zero_lt_one.trans_le hBa1).ne' hBz1 hBlt, hBa, hBz, hBΘE]

section Thh

variable {n : ℕ} {l l' ηx ηx' : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hl' : IsRestartIdx l') (hX' : upsilon l' < Pv S ηx')
  {B : Ordinal.{0}} (hBSC : SC B)
  (IHm : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < B → MvD S x ∧
    GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
    gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x))

include hl hX hl' hX' hBSC IHm

/-- **THE MOVE OF THE EXPONENTS BELOW `G = φ(Ω₂, 1)`**, code levels included. -/
theorem tjB_thH : ∀ E, E ∈ cdHull S l → E < veblen (Om (1 + 1)) 1 → LeCl (Om (1 + 1)) B E →
    MvD S E ∧ MvD S (Om (1 + 1) * E) ∧ Bc.bcB S n (Om (1 + 1) * E) = Om (1 + 1) * Bc.bcB S n E ∧
      Bc.bcB S n E < veblen (Om (1 + 1)) 1 ∧ Bc.bcB S n E ∈ cdHull S l' ∧
      (MvD S B → ∀ Q, SC Q → Bc.bcB S n B ≤ Q → LeCl (Om (1 + 1)) Q (Bc.bcB S n E)) ∧
      MvD S (tdThL S l E) ∧ MvD S (Om 1 * tdThL S l E) ∧
      Bc.bcB S n (Om 1 * tdThL S l E) = Om 1 * Bc.bcB S n (tdThL S l E) ∧
      tdThL S l' (Bc.bcB S n E) = Bc.bcB S n (tdThL S l E) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have h1ρ : (1 : Ordinal.{0}) ≤ upsilon l := (gg_one_lt_of_SC hρSC).le
  have h1ρ' : (1 : Ordinal.{0}) ≤ upsilon l' := (gg_one_lt_of_SC (leRho hl' hX').1).le
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hc1 : Bc.bcC S (n + 1) < Om 1 := hLw.trans (psi_lt Low.InR_Om_one _)
  have hD0 : MvD S (0 : Ordinal.{0}) := mvD_of_lt (Lw.lw_L_SC S ω).1
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  obtain ⟨hDtop, hBtop⟩ := tjB_G (S := S) (n := n)
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  set Pc : Ordinal.{0} → Prop := fun x => GxCl (upsilon l) (ldAtR S l) x ∧ x < B with hPc
  have hPcD : ∀ x, Pc x → MvD S x := fun x hx => (IHm x hx.1 hx.2).1
  have hD0' : (0 : Ordinal.{0}) ∈ cdHull S l' := CSet.zero_mem _ _
  have hPcdec : ∀ x, Pc x → x ≠ 0 → Pc (log ω x) ∧ Pc (x - ω ^ log ω x) := fun x hx hx0 => by
    obtain ⟨hsub, hlog⟩ := gxDec hρSC hAt x hx.1
    exact ⟨⟨hlog, (log_le_self ω x).trans_lt hx.2⟩,
      ⟨hsub _ (GxCl.opow hρSC.1 hlog) (opow_log_le_self ω hx0), (Ordinal.sub_le_self _ _).trans_lt hx.2⟩⟩
  set P1 : Ordinal.{0} → Prop := fun x => x < Om 1 ∧ x < Bc.bcC S (n + 1) with hP1
  have hP1D : ∀ x, P1 x → MvD S x := fun x hx => mvD_of_lt (hx.2.trans hLw)
  have hP1dec : ∀ x, P1 x → x ≠ 0 → P1 (log ω x) ∧ P1 (x - ω ^ log ω x) := fun x hx _ =>
    ⟨⟨(log_le_self ω x).trans_lt hx.1, (log_le_self ω x).trans_lt hx.2⟩,
      ⟨(Ordinal.sub_le_self _ _).trans_lt hx.1, (Ordinal.sub_le_self _ _).trans_lt hx.2⟩⟩
  have eW : ∀ z w : Ordinal.{0}, Om (1 + 1) * (leWe z * w) = ω ^ (Om (1 + 1) + Om (1 + 1) * z) * w :=
    fun z w => by rw [← mul_assoc]; unfold leWe; rw [opow_add, gg_SC_eps ldOm2_SC]
  have eO : ∀ z w : Ordinal.{0}, Om 1 * (leOe z * w) = ω ^ (Om 1 + Om 1 * z) * w :=
    fun z w => by rw [← mul_assoc]; unfold leOe; rw [opow_add, gg_SC_eps Ph.ph_SC_Om1]
  intro E
  induction E using WellFoundedLT.induction with
  | ind E IH =>
  intro hEH hE hEB
  rcases eq_or_ne E 0 with rfl | hE0
  · refine ⟨hD0, by rw [mul_zero]; exact hD0, by rw [mul_zero, Bc.bcB_zero, mul_zero], ?_,
      by rw [Bc.bcB_zero]; exact hD0', fun _ Q hQ _ => by rw [Bc.bcB_zero]; exact LeCl.zero hQ.1, ?_, ?_, ?_, ?_⟩
    · rw [Bc.bcB_zero]; exact veblen_pos
    · rw [tjThL_zero]; exact hD0
    · rw [tjThL_zero, mul_zero]; exact hD0
    · rw [tjThL_zero, mul_zero, Bc.bcB_zero, mul_zero]
    · rw [Bc.bcB_zero, tjThL_zero, tjThL_zero, Bc.bcB_zero]
  have hE1 : 1 ≤ E := Order.one_le_iff_ne_zero.2 hE0
  have hpos : 0 < E := pos_iff_ne_zero.2 hE0
  by_cases hc : 0 < E ∧ sgLW E < E
  swap
  · -- a node `E = φ(a, Ω₂ + y')` with a code level `a`
    obtain ⟨ha1, haW, hΩy, hyE, hval⟩ := tdNode_nfW hE1 hE (fun h => hc ⟨hpos, h⟩)
    set a := invVeblen₁ E with ha_def
    set y' := invVeblen₂ E - Om (1 + 1) with hy'_def
    have ha0 : a ≠ 0 := (zero_lt_one.trans_le ha1).ne'
    have hyadd : Om (1 + 1) + y' = invVeblen₂ E := taNode_add hΩy
    have hy'1 : 1 ≤ y' := taNode_one hΩy
    have hEv : E = veblen a (Om (1 + 1) + y') := by rw [hyadd, hval]
    have haE : a < E := haW.trans (hΩy.trans hyE)
    have hmem := mem_of_veblen_mem (by rw [hval]; exact hEH) (by rw [hval]; exact haE) (by rw [hval]; exact hyE)
    have hac : GxCl (upsilon l) (ldAtR S l) a := (ldHull_iff hl hX haW).1 hmem.1
    have hyH : invVeblen₂ E ∈ cdHull S l := hmem.2
    have hy'H : y' ∈ cdHull S l := taSub_mem _ hyH _
    have hy'E : y' < E := (Ordinal.sub_le_self _ _).trans_lt hyE
    have hEB' : LeCl (Om (1 + 1)) B (veblen a (invVeblen₂ E)) := by rw [hval]; exact hEB
    have haB : a < B := tdCl_lev_lt hBSC ldOm2_SC hEB' (by rw [hval]; exact hyE) haW
    have hy'B : LeCl (Om (1 + 1)) B y' :=
      (leClDec hBSC ldOm2_SC _ (taCl_inv hBSC ldOm2_SC haW hEB')).1 _ LeCl.om hΩy.le
    obtain ⟨hDy', -, -, -, hBy'H, hcly', hDΘy', -, -, hΘ'y'⟩ := IH y' hy'E hy'H (hy'E.trans hE) hy'B
    obtain ⟨hDa, hBac, hΘac, hΘ'a⟩ := IHm a hac haB
    have hyEv : Om (1 + 1) + y' < E := by rw [hyadd]; exact hyE
    have hlt : Om (1 + 1) + y' < veblen a (Om (1 + 1) + y') := by rw [← hEv]; exact hyEv
    have hΘaO : gxTh (upsilon l) (ldAtR S l) a < Om 1 := Sn.snTh_lt_Om1 hl hX haW.le
    have hDΘa : MvD S (gxTh (upsilon l) (ldAtR S l) a) := mvD_of_lt (hΘac.trans hLw)
    obtain ⟨hDE, hBE, hBlt, hDΘE, hBΘE, hΘ'E⟩ :=
      tjB_node (n := n) (l' := l') hDa hDy' ha1 haW hy'1 hlt hDΘa hΘaO hDΘy' hΘ'a hΘ'y'
    rw [← hEv] at hDE hBE hDΘE hBΘE hΘ'E
    have hBa1 : 1 ≤ Bc.bcB S n a := by have := leB_le (n := n) hD1 hDa ha1; rwa [mwB_one] at this
    have hBa0 : Bc.bcB S n a ≠ 0 := (zero_lt_one.trans_le hBa1).ne'
    have hBy'1 : 1 ≤ Bc.bcB S n y' := by have := leB_le (n := n) hD1 hDy' hy'1; rwa [mwB_one] at this
    have hBaW : Bc.bcB S n a < Om (1 + 1) := by
      have := (mvB_lt_iff (k := n) hDa hD2).2 haW; rwa [hB2] at this
    -- the image `Θ̂_L E = φ(Θ a, Ω₁ + Θ̂_L y')`
    have hΘE := tdThL_veb (S := S) (l := l) ha0 hy'1 hlt
    rw [← hEv] at hΘE
    obtain ⟨hy'w, -, hy'v⟩ := tgTm_spec hl hX y' hy'H (hy'E.trans hE)
    have hne : taTm y' ≠ TaT.zero := fun h0 => by
      rw [h0] at hy'v; exact absurd hy'1 (by rw [← hy'v]; exact not_le.2 zero_lt_one)
    have hΘ1 : 1 ≤ tdThL S l y' := (tgV_pos h1ρ _ hy'w hne).2
    have hΘa1 : 1 ≤ gxTh (upsilon l) (ldAtR S l) a := tgTh_one h1ρ ha1
    have hΘa0 : gxTh (upsilon l) (ldAtR S l) a ≠ 0 := (zero_lt_one.trans_le hΘa1).ne'
    have hDΘa' : MvD S (gxTh (upsilon l) (ldAtR S l) a) := hDΘa
    have hBΘa1 : 1 ≤ Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) a) := by
      have := leB_le (n := n) hD1 hDΘa' hΘa1; rwa [mwB_one] at this
    have hBΘ1 : 1 ≤ Bc.bcB S n (tdThL S l y') := by
      have := leB_le (n := n) hD1 hDΘy' hΘ1; rwa [mwB_one] at this
    have hWE : Om (1 + 1) * E = E := by rw [hEv]; exact taK_mul_veb ldOm2_SC ha0 (taKy_lt hy'1)
    have hOE : Om 1 * tdThL S l E = tdThL S l E := by
      rw [hΘE]; exact taK_mul_veb Ph.ph_SC_Om1 hΘa0 (taKy_lt hΘ1)
    refine ⟨hDE, by rw [hWE]; exact hDE, ?_, ?_, ?_, ?_, hDΘE, by rw [hOE]; exact hDΘE, ?_, hΘ'E⟩
    · rw [hWE, hBE, taK_mul_veb ldOm2_SC hBa0 (taKy_lt hBy'1)]
    · have := (mvB_lt_iff (k := n) hDE hDtop).2 hE; rwa [hBtop] at this
    · rw [hBE]; exact CSet.phi_mem ((ldHull_iff hl' hX' hBaW).2 hBac) (CSet.add_mem (mxOm2_mem _ _) hBy'H)
    · intro hDB Q hQ hQB
      rw [hBE]
      have hBaQ : Bc.bcB S n a < Q := ((mvB_lt_iff (k := n) hDa hDB).2 haB).trans_le hQB
      exact LeCl.phi (LeCl.small hBaQ) (LeCl.add LeCl.om (hcly' hDB Q hQ hQB))
    · rw [hOE, hBΘE, taK_mul_veb Ph.ph_SC_Om1 (zero_lt_one.trans_le hBΘa1).ne' (taKy_lt hBΘ1)]
  set e := sgLW E with he
  set q := E / leWe e with hq
  set r := E % leWe e with hr_def
  have hel : e < E := hc.2
  have hWe : leWe e ≤ E := sgLW_le hpos
  have hWe0 : leWe e ≠ 0 := (leWe_pos e).ne'
  have heH : e ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hEH)
  have hrW : r < leWe e := Ordinal.mod_lt _ hWe0
  have hr : r < E := hrW.trans_le hWe
  have hrH : r ∈ cdHull S l := leModP_mem (Om (1 + 1) * e) hEH
  have hE2 : E < leWe e * Om (1 + 1) := by rw [← leWe_succ]; exact sgLW_lt E
  have hqW : q < Om (1 + 1) := (Ordinal.lt_mul_iff_div_lt hWe0).1 hE2
  have hqH : q ∈ cdHull S l := by
    refine leDivOp_mem (K := Om (1 + 1) * e) (dvd_mul_right _ _) hEH ?_
    have : leWe (e + 1) = ω ^ (Om (1 + 1) * e + Om (1 + 1)) := by unfold leWe; rw [mul_add_one]
    rw [← this]; exact sgLW_lt E
  have hq1 : 1 ≤ q := Order.one_le_iff_pos.2 ((Ordinal.div_pos hWe0).2 hWe)
  have hqc : GxCl (upsilon l) (ldAtR S l) q := (ldHull_iff hl hX hqW).1 hqH
  have hEdec : leWe e * q + r = E := Ordinal.div_add_mod E (leWe e)
  obtain ⟨heB, hrB, hqB⟩ := Sw.swCl_cnf hBSC hEB
  obtain ⟨hDq, hBqc, hΘq, hΘ'q⟩ := IHm q hqc hqB
  obtain ⟨hDe, hDWe, hBWe, hBetop, hBeH, hcle, hDΘe, hDOΘe, hBOΘe, hΘ'e⟩ := IH e hel heH (hel.trans hE) heB
  obtain ⟨hDr, hDWr, hBWr, hBrtop, hBrH, hclr, hDΘr, hDOΘr, hBOΘr, hΘ'r⟩ := IH r hr hrH (hr.trans hE) hrB
  obtain ⟨hDWe0, hBWe'⟩ := ldB_opow (n := n) hDWe
  have hDWe' : MvD S (leWe e) := hDWe0
  rw [hBWe] at hBWe'
  have hBWe'' : Bc.bcB S n (leWe e) = leWe (Bc.bcB S n e) := hBWe'
  obtain ⟨hDWq0, hBWq⟩ := sjB_mulOp (n := n) hDWe Pc hPcD hPcdec q ⟨hqc, hqB⟩
  have hDWq : MvD S (leWe e * q) := hDWq0
  rw [hBWe] at hBWq
  have hBWq' : Bc.bcB S n (leWe e * q) = leWe (Bc.bcB S n e) * Bc.bcB S n q := hBWq
  obtain ⟨hDE, hBE⟩ := mvB_add (k := n) hDWq hDr
  rw [hEdec, hBWq'] at hBE
  rw [hEdec] at hDE
  obtain ⟨hDK, hBK⟩ := mvB_add (k := n) hD2 hDWe
  rw [hB2, hBWe] at hBK
  obtain ⟨hDKq, hBKq⟩ := sjB_mulOp (n := n) hDK Pc hPcD hPcdec q ⟨hqc, hqB⟩
  rw [hBK] at hBKq
  obtain ⟨hDΩE, hBΩE⟩ := mvB_add (k := n) hDKq hDWr
  have eΩE : Om (1 + 1) * E = ω ^ (Om (1 + 1) + Om (1 + 1) * e) * q + Om (1 + 1) * r := by
    conv_lhs => rw [← hEdec]
    rw [mul_add, eW]
  have hBq1 : 1 ≤ Bc.bcB S n q := by
    have := leB_le (n := n) hD1 hDq hq1; rwa [mwB_one] at this
  have hBqW : Bc.bcB S n q < Om (1 + 1) := by
    have := (mvB_lt_iff (k := n) hDq hD2).2 hqW; rwa [hB2] at this
  have hBrW : Bc.bcB S n r < leWe (Bc.bcB S n e) := by
    have := (mvB_lt_iff (k := n) hDr hDWe').2 hrW; rwa [hBWe''] at this
  obtain ⟨hlogB, hdivB, hmodB⟩ := sjCnf_W hBq1 hBqW hBrW
  rw [← hBE] at hlogB hdivB hmodB
  have hBE1 : 1 ≤ Bc.bcB S n E := by
    have := leB_le (n := n) hD1 hDE hE1; rwa [mwB_one] at this
  have hBEtop : Bc.bcB S n E < veblen (Om (1 + 1)) 1 := by
    have := (mvB_lt_iff (k := n) hDE hDtop).2 hE; rwa [hBtop] at this
  have hcB : 0 < Bc.bcB S n E ∧ sgLW (Bc.bcB S n E) < Bc.bcB S n E := by
    refine ⟨zero_lt_one.trans_le hBE1, ?_⟩
    rw [hlogB]; exact (mvB_lt_iff (k := n) hDe hDE).2 hel
  have hΘqP1 : P1 (gxTh (upsilon l) (ldAtR S l) q) := ⟨hΘq.trans hc1, hΘq⟩
  obtain ⟨hDOq0, hBOq⟩ := sjB_mulOp (n := n) hDOΘe P1 hP1D hP1dec _ hΘqP1
  have hDOq : MvD S (leOe (tdThL S l e) * gxTh (upsilon l) (ldAtR S l) q) := hDOq0
  rw [hBOΘe] at hBOq
  have hBOq' : Bc.bcB S n (leOe (tdThL S l e) * gxTh (upsilon l) (ldAtR S l) q) =
      leOe (Bc.bcB S n (tdThL S l e)) * Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) q) := hBOq
  have hΘE := tjThL_cnf (S := S) h1ρ hc (tgTm_spec hl hX _ hrH (hr.trans hE)).1
  rw [← he, ← hq, ← hr_def] at hΘE
  obtain ⟨hDΘE, hBΘE⟩ := mvB_add (k := n) hDOq hDΘr
  rw [← hΘE, hBOq'] at hBΘE
  rw [← hΘE] at hDΘE
  obtain ⟨hDK1, hBK1⟩ := mvB_add (k := n) hDO hDOΘe
  rw [hBO, hBOΘe] at hBK1
  obtain ⟨hDK1q, hBK1q⟩ := sjB_mulOp (n := n) hDK1 P1 hP1D hP1dec _ hΘqP1
  rw [hBK1] at hBK1q
  obtain ⟨hDOΘE, hBOΘE⟩ := mvB_add (k := n) hDK1q hDOΘr
  have eOΘE : Om 1 * tdThL S l E = ω ^ (Om 1 + Om 1 * tdThL S l e) * gxTh (upsilon l) (ldAtR S l) q +
      Om 1 * tdThL S l r := by
    rw [hΘE, mul_add, eO]
  refine ⟨hDE, by rw [eΩE]; exact hDΩE, ?_, hBEtop, ?_, ?_, hDΘE, by rw [eOΘE]; exact hDOΘE, ?_, ?_⟩
  · rw [eΩE, hBΩE, hBKq, hBWr, hBE, mul_add, eW]
  · rw [hBE]
    exact CSet.add_mem (leMulWe_mem hBeH ((ldHull_iff hl' hX' hBqW).2 hBqc)) hBrH
  · intro hDB Q hQ hQB
    rw [hBE]
    have hBqQ : Bc.bcB S n q < Q := ((mvB_lt_iff (k := n) hDq hDB).2 hqB).trans_le hQB
    exact LeCl.add (rvCl_mulOp hQ (LeCl.mulK hQ ldOm2_SC _ (hcle hDB Q hQ hQB)) ldOm2_SC _ (LeCl.small hBqQ))
      (hclr hDB Q hQ hQB)
  · rw [eOΘE, hBOΘE, hBK1q, hBOΘr, hBΘE, mul_add, eO]
  · rw [tjThL_cnf (S := S) h1ρ' hcB (by rw [hlogB, hmodB]; exact (tgTm_spec hl' hX' _ hBrH hBrtop).1),
      hlogB, hdivB, hmodB, hΘ'e, hΘ'q, hΘ'r, hBΘE]

end Thh

section Sys

variable {n : ℕ} {l l' ηx ηx' : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hl' : IsRestartIdx l') (hX' : upsilon l' < Pv S ηx')

include hl hX hl' hX'

/-- **THE MOVE OF THE LEVEL SYSTEM UP TO `G = φ(Ω₂, 1)`**: `St.StLSB S n λ λ' G Θ̂_L`. -/
theorem tjLSB : StLSB S n l l' (veblen (Om (1 + 1)) 1) (tdThL S) :=
  fun _ hBSC _ IHm E hEH _ hE hEB => tjB_thH hl hX hl' hX' hBSC IHm E hEH hE hEB

end Sys

end Googology.Trans.PoR.InaccPsi.R2.Tj

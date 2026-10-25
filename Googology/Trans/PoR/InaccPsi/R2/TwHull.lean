import Googology.Trans.PoR.InaccPsi.R2.TwBase
import Googology.Trans.PoR.InaccPsi.R2.LeEBlk

/-!
# Codes below `X` in the hulls `Cl(a, b)`, and the support of a hull member

`ψ = ψ_{Ω₂}`, `F_β = Rh.rhF β`, `w_β = Ω₂^β`, `X = Tl.tlX`, `TlCl Z` the codes over `Z` with the atoms `F_β(y)`.  An
atom past `B_Γ` is `ψ(e)` with `Ω₂ < e` (`Ts.ts_atom_ge`), and it enters `Cl(a, b)` through `e < a`; here a code lies
in `Cl(a, b)` when the own arguments of its atoms are below `a`:

* `TwArgs S a x` (**every strongly critical `s ∈ (Ω₁, x]` has its own argument below `a`**), `TwArgs.mono`;
* `tw_SC_code` (**every strongly critical `s ∈ (Ω₁, y]` lies below an atom `t ≤ y` that is a code**), `twArgs_of`;
* `tw_mem_CSet` (**the hull converse**: a code `x` over `Z ≤ b` (`Z` strongly critical, countable) with `TwArgs S a
  x` lies in `Cl(a, b)`, and so does the own argument of `x` when `x` is an atom; the own argument is the run
  `B + w_β·D` of `Tw.twRun`, built from `w_β`, `D` and the own argument of a smaller atom);
* `tw_top` (**the top atom**: for a code `μ` with `TwArgs S B μ` there is `A < B` with `TwArgs S a μ` for every
  `a > A`, and `A ∈ Cl(a, b)` for every `a > A`, every countable strongly critical `b` over which `μ` is a code);
* `tw_supp` (**the support of a hull member**: `x ∈ Cl(B, q)` with `B` and `q` limits gives `x ∈ Cl(a, r)` for some
  `a < B`, `r < q`).

No new axiom.  New definition: `TwArgs`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Ts

variable {S : InaccSeq.{0}}

/-- **The own arguments of the atoms up to `x` are below `a`.** -/
def TwArgs (S : InaccSeq.{0}) (a x : Ordinal.{0}) : Prop :=
  ∀ s e, SC s → Om1 < s → s ≤ x → e ∈ S.CSet e (S.psi e (Om (1 + 1))) → S.psi e (Om (1 + 1)) = s → e < a

theorem TwArgs.mono {a a' x y : Ordinal.{0}} (h : TwArgs S a x) (ha : a ≤ a') (hy : y ≤ x) : TwArgs S a' y :=
  fun s e h1 h2 h3 h4 h5 => (h s e h1 h2 (h3.trans hy) h4 h5).trans_le ha

/-- **Every strongly critical `s ∈ (Ω₁, y]` lies below an atom `t ≤ y` that is a code.** -/
theorem tw_SC_code {Z : Ordinal.{0}} (hZ : Z ≤ Om1) :
    ∀ y, TlCl Z y → ∀ s, SC s → Om1 < s → s ≤ y → ∃ t, TlCl Z t ∧ SC t ∧ s ≤ t ∧ t ≤ y := by
  intro y hy
  induction hy with
  | small h => exact fun s _ hs hsy => absurd ((hsy.trans_lt h).trans_le hZ) (not_lt.2 hs.le)
  | om => exact fun s _ hs hsy => absurd hs (not_lt.2 hsy)
  | @add x y _ _ ihx ihy =>
    intro s hS hs hsy
    by_cases hxs : s ≤ x
    · obtain ⟨t, a, b, c, d⟩ := ihx s hS hs hxs; exact ⟨t, a, b, c, d.trans le_self_add⟩
    by_cases hys : s ≤ y
    · obtain ⟨t, a, b, c, d⟩ := ihy s hS hs hys; exact ⟨t, a, b, c, d.trans le_add_self⟩
    exact absurd (tl_SC_prin hS (not_le.1 hxs) (not_le.1 hys)) (not_lt.2 hsy)
  | @phi x y _ _ ihx ihy =>
    intro s hS hs hsy
    by_cases hxs : s ≤ x
    · obtain ⟨t, a, b, c, d⟩ := ihx s hS hs hxs; exact ⟨t, a, b, c, d.trans (left_le_veblen x y)⟩
    by_cases hys : s ≤ y
    · obtain ⟨t, a, b, c, d⟩ := ihy s hS hs hys; exact ⟨t, a, b, c, d.trans (right_le_veblen x y)⟩
    exact absurd (hS.2 _ (not_le.1 hxs) _ (not_le.1 hys)) (not_lt.2 hsy)
  | @atom β' y' hβ' hy' h1 _ _ =>
    exact fun s _ _ hsy => ⟨_, TlCl.atom hβ' hy' h1, rhF_SC β' y', hsy, le_rfl⟩

/-- `TwArgs` from the atoms that are codes. -/
theorem twArgs_of {Z a x : Ordinal.{0}} (hZ : Z ≤ Om1) (hx : TlCl Z x)
    (h : ∀ t e, TlCl Z t → SC t → Om1 < t → t ≤ x → e ∈ S.CSet e (S.psi e (Om (1 + 1))) →
      S.psi e (Om (1 + 1)) = t → e < a) : TwArgs S a x := by
  intro s e hS hs hsx hown hψ
  obtain ⟨t, htc, htS, hst, htx⟩ := tw_SC_code hZ x hx s hS hs hsx
  have hts : Om1 < t := hs.trans_le hst
  have htX : t < tlX := htx.trans_lt (tw_cl_lt hZ hx)
  obtain ⟨et, hownt, hψt⟩ := ts_own_of_SC (S := S) htS (by rw [← tw_Om1_eq]; exact hts) (tw_lt_psiW htX)
  have het := h t et htc htS hts htx hownt hψt
  refine lt_of_le_of_lt (not_lt.1 fun hlt => ?_) het
  have := (ts_own_lt_iff hownt hown).2 hlt
  rw [hψt, hψ] at this
  exact absurd hst (not_le.2 this)

/-- **The hull converse**: a code `x` over a countable strongly critical `Z ≤ b` whose atoms have their own arguments
below `a` lies in `Cl(a, b)`; when `x` is an atom, so does its own argument. -/
theorem tw_mem_CSet {Z a b : Ordinal.{0}} (hZS : SC Z) (hZ : Z ≤ Om1) (hZb : Z ≤ b) :
    ∀ x, TlCl Z x → TwArgs S a x → x ∈ S.CSet a b ∧
      (SC x → Om1 < x → ∀ e, e ∈ S.CSet e (S.psi e (Om (1 + 1))) → S.psi e (Om (1 + 1)) = x →
        e ∈ S.CSet a b) := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx hargs
  rcases lt_trichotomy x Om1 with h | rfl | h
  · exact ⟨CSet.of_lt ((hx.lt_of_lt_Om1 hZS h).trans_le hZb), fun _ h1 => absurd h1 (not_lt.2 h.le)⟩
  · exact ⟨by rw [tw_Om1_eq]; exact CSet.Om_mem (CSet.one_mem _ _), fun _ h1 => absurd h1 (lt_irrefl _)⟩
  have hzX := tw_cl_lt hZ hx
  by_cases hE : ω ^ x = x
  · by_cases hI : invVeblen₁ x < x
    · obtain ⟨h1, h2⟩ := tl_cl_inv hZ x hx h hE hI
      have h2l := Tf.tf_inv2_lt hE
      have e : veblen (invVeblen₁ x) (invVeblen₂ x) = x := by rw [veblen_invVeblen₁_invVeblen₂, hE]
      refine ⟨?_, fun hSC _ => absurd hI (tl_SC_facts hSC).2⟩
      rw [← e]
      exact CSet.phi_mem (IH _ hI h1 (hargs.mono le_rfl hI.le)).1 (IH _ h2l h2 (hargs.mono le_rfl h2l.le)).1
    · -- an atom `F_β(y)`: its own argument is the run `B + w_β·D`
      have hSC := tl_SC_of h hI
      obtain ⟨hnf, hyz, hlz⟩ := tl_nf hSC h hzX
      obtain ⟨hcβ, hcy⟩ := tl_cl_atom hZ x hx hSC h
      generalize hβdef : tlLev x = β at hnf hyz hlz hcβ hcy
      generalize hydef : tlI β x = y at hnf hyz hcy
      have hβX : β < tlX := hlz.trans hzX
      have h1' : Om 1 < rhF β y := by rw [hnf, ← tw_Om1_eq]; exact h
      have hyz' : y < rhF β y := by rw [hnf]; exact hyz
      have hzX' : rhF β y < tlX := by rw [hnf]; exact hzX
      obtain ⟨B, c, D, hown, hdvd, hc, hcD, hD2, hval, hcc, hDc, hcase⟩ :=
        twRun (S := S) hZS hZ hcy hβX hyz' h1' hzX'
      have hcz : c < x := (le_self_add.trans_eq hcD).trans_lt hyz
      have hDz : D < x := (le_add_self.trans_eq hcD).trans_lt hyz
      have hβz : β < rhF β (c + D) := by rw [hcD, hnf]; exact hlz
      obtain ⟨hψe, howne⟩ := twRun_eq hown hdvd hc hD2 hval hβz
      rw [hcD, hnf] at hψe
      have hβC := (IH β hlz hcβ (hargs.mono le_rfl hlz.le)).1
      have hDC := (IH D hDz hDc (hargs.mono le_rfl hDz.le)).1
      have hBC : B ∈ S.CSet a b := by
        rcases hcase with ⟨-, hB0, -⟩ | ⟨-, hBw, -⟩ | ⟨hc1, hcf, -⟩
        · rw [hB0]; exact CSet.zero_mem _ _
        · rw [hBw]; exact leWe_mem hβC
        · have hcSC : SC c := by rw [← hcf]; exact rhF_SC β c
          exact (IH c hcz hcc (hargs.mono le_rfl hcz.le)).2 hcSC (by rw [tw_Om1_eq]; exact hc1) B hown
            (by rw [← hc, hcf])
      have heC : B + leWe β * D ∈ S.CSet a b := CSet.add_mem hBC (leMulWe_mem hβC hDC)
      have hea : B + leWe β * D < a := hargs x _ hSC h le_rfl howne hψe
      have hxC : x ∈ S.CSet a b := by
        rw [← hψe]; exact CSet.psi_mem hea (InR_Om_succ 1) (Mx.mxOm2_mem a b) heC
      refine ⟨hxC, fun _ _ e hown' hψ' => ?_⟩
      have := ts_own_unique hown' howne (by rw [hψ', hψe])
      rw [this]; exact heC
  · have hz0 : x ≠ 0 := (Rj.rj_Om1_pos.trans h).ne'
    obtain ⟨hsub, hlog⟩ := tlDec hZS x hx
    set g := log ω x with hg
    obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
    have hdec : ω ^ g * k + x % ω ^ g = x := by
      have := Ordinal.div_add_mod x (ω ^ g); rwa [hk] at this
    have hwk : TlCl Z (ω ^ g * k) := TlCl.mul_nat hZS.1 (TlCl.opow hZS.1 hlog) k
    have hle : ω ^ g * k ≤ x := by
      conv_rhs => rw [← hdec]
      exact le_self_add
    have hr : TlCl Z (x % ω ^ g) := by
      have e : x - ω ^ g * k = x % ω ^ g := by
        nth_rewrite 1 [← hdec]; exact Ordinal.add_sub_cancel _ _
      rw [← e]; exact hsub _ hwk hle
    have hgl := Tf.tf_log_lt h hE
    have hml := Rj.rj_mod_lt hz0
    have hgC := (IH _ hgl hlog (hargs.mono le_rfl hgl.le)).1
    have hmC := (IH _ hml hr (hargs.mono le_rfl hml.le)).1
    have hwC : ω ^ g ∈ S.CSet a b := by
      have := CSet.phi_mem (CSet.zero_mem a b) hgC; rwa [veblen_zero_apply] at this
    refine ⟨?_, fun hSC _ => absurd (tl_SC_facts hSC).1 hE⟩
    rw [← hdec]
    exact CSet.add_mem (mul_nat_mem hwC k) hmC

/-- **The top atom**: for a code `μ` over a countable strongly critical `Z` with `TwArgs S B μ`, `0 < B`, there is
`A < B` with `TwArgs S a μ` for every `a > A`, and `A ∈ Cl(a, b)` for every `a > A` and every countable strongly
critical `b` over which `μ` is a code. -/
theorem tw_top {Z B μ : Ordinal.{0}} (hZ : Z ≤ Om1) (hμ : TlCl Z μ) (h : TwArgs S B μ) (hB : 0 < B) :
    ∃ A, A < B ∧ (∀ a, A < a → TwArgs S a μ) ∧
      (∀ a b, A < a → SC b → b ≤ Om1 → TlCl b μ → A ∈ S.CSet a b) := by
  by_cases hex : ∃ s, SC s ∧ Om1 < s ∧ s ≤ μ
  · set T : Set Ordinal.{0} := {s | SC s ∧ Om1 < s ∧ s ≤ μ} with hT
    have hne : T.Nonempty := hex
    have hbd : BddAbove T := ⟨μ, fun s hs => hs.2.2⟩
    have htS : SC (sSup T) := Rk.rk_SC_sSup (fun v hv => hv.1) hne hbd
    obtain ⟨s0, hs0⟩ := hex
    have ht1 : Om1 < sSup T := hs0.2.1.trans_le (le_csSup hbd hs0)
    have htμ : sSup T ≤ μ := csSup_le hne fun s hs => hs.2.2
    have hmax : ∀ s, SC s → Om1 < s → s ≤ μ → s ≤ sSup T := fun s h1 h2 h3 => le_csSup hbd ⟨h1, h2, h3⟩
    have htX : sSup T < tlX := htμ.trans_lt (tw_cl_lt hZ hμ)
    obtain ⟨A, hownA, hψA⟩ := ts_own_of_SC (S := S) htS (by rw [← tw_Om1_eq]; exact ht1) (tw_lt_psiW htX)
    have hAB : A < B := h _ A htS ht1 htμ hownA hψA
    have hargs : ∀ a, A < a → TwArgs S a μ := by
      intro a ha s e hS hs hsμ hown hψ
      refine lt_of_le_of_lt (not_lt.1 fun hlt => ?_) ha
      have := (ts_own_lt_iff hownA hown).2 hlt
      rw [hψA, hψ] at this
      exact absurd (hmax s hS hs hsμ) (not_le.2 this)
    refine ⟨A, hAB, hargs, fun a b ha hb hb1 hμb => ?_⟩
    obtain ⟨t, htc, htS', htt, htμ'⟩ := tw_SC_code hb1 μ hμb (sSup T) htS ht1 htμ
    have hteq : t = sSup T := le_antisymm (hmax t htS' (ht1.trans_le htt) htμ') htt
    rw [← hteq] at hψA htS ht1
    exact (tw_mem_CSet hb hb1 le_rfl t htc ((hargs a ha).mono le_rfl htμ')).2 htS ht1 A hownA hψA
  · push Not at hex
    refine ⟨0, hB, fun a _ s e hS hs hsμ => absurd (hex s hS hs) (not_lt.2 hsμ), fun a b _ _ _ _ =>
      CSet.zero_mem _ _⟩

/-- **The support of a hull member**: `x ∈ Cl(B, q)` with `B` and `q` successor-limit ordinals gives `x ∈ Cl(a, r)`
for some `a < B` and `r < q`. -/
theorem tw_supp {B q : Ordinal.{0}} (hB : IsSuccLimit B) (hq : IsSuccLimit q) :
    ∀ x ∈ S.CSet B q, ∃ a r, a < B ∧ r < q ∧ x ∈ S.CSet a r := by
  have hB0 : 0 < B := hB.bot_lt
  have hq0 : 0 < q := hq.bot_lt
  have hjoin : ∀ {x y a r a' r' : Ordinal.{0}}, x ∈ S.CSet a r → y ∈ S.CSet a' r' →
      x ∈ S.CSet (max a a') (max r r') ∧ y ∈ S.CSet (max a a') (max r r') := fun hx hy =>
    ⟨CSet_mono (le_max_left _ _) (le_max_left _ _) hx, CSet_mono (le_max_right _ _) (le_max_right _ _) hy⟩
  intro x hx
  induction hx with
  | @small v hv => exact ⟨0, v + 1, hB0, hq.add_one_lt hv, CSet.of_lt (lt_add_one v)⟩
  | zero => exact ⟨0, 0, hB0, hq0, CSet.zero_mem _ _⟩
  | inacc n => exact ⟨0, 0, hB0, hq0, CSet.I_mem _ _ n⟩
  | inaccW => exact ⟨0, 0, hB0, hq0, CSet.Iw_mem _ _⟩
  | add _ _ ihx ihy =>
    obtain ⟨a, r, ha, hr, hx'⟩ := ihx
    obtain ⟨a', r', ha', hr', hy'⟩ := ihy
    obtain ⟨h1, h2⟩ := hjoin hx' hy'
    exact ⟨_, _, max_lt ha ha', max_lt hr hr', CSet.add_mem h1 h2⟩
  | phi _ _ ihx ihy =>
    obtain ⟨a, r, ha, hr, hx'⟩ := ihx
    obtain ⟨a', r', ha', hr', hy'⟩ := ihy
    obtain ⟨h1, h2⟩ := hjoin hx' hy'
    exact ⟨_, _, max_lt ha ha', max_lt hr hr', CSet.phi_mem h1 h2⟩
  | om _ ih =>
    obtain ⟨a, r, ha, hr, hx'⟩ := ih
    exact ⟨a, r, ha, hr, CSet.Om_mem hx'⟩
  | @coll π e hπ _ _ ihπ ihe =>
    obtain ⟨a, r, ha, hr, hπ'⟩ := ihπ
    obtain ⟨a', r', ha', hr', he'⟩ := ihe
    obtain ⟨h1, h2⟩ := hjoin hπ' he'
    have he1 : e.1 + 1 < B := hB.add_one_lt e.2
    refine ⟨max (max a a') (e.1 + 1), max r r', max_lt (max_lt ha ha') he1, max_lt hr hr', ?_⟩
    exact CSet.psi_mem ((lt_add_one _).trans_le (le_max_right _ _)) hπ
      (CSet_mono (le_max_left _ _) le_rfl h1) (CSet_mono (le_max_left _ _) le_rfl h2)

end Googology.Trans.PoR.InaccPsi.R2.Tw

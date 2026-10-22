import Googology.Trans.PoR.InaccPsi.R2.RdKPsi
import Googology.Trans.PoR.InaccPsi.R2.RhFn

/-!
# `ψ_{Ω₁}(B + Ω₁^β·D) = F_β(c + D)`, the fixed points of `F_β` among the collapses, and `B_n` there, at every `β`

`ψ = S.psi`, `F_β = Rh.rhF β`, `u_β = Ω₁^β = Le.leOe β`, `B_n = Bc.bcB S n`, `σ = bcSig (bcPre (n+1)) bcPreW`.  An
argument `B` is *own* when `B ∈ Cl(B, ψ_{Ω₁}(B))`.

* `rh_base_below` (for any normal `f`: the largest point below `x` that is `τ` or a fixed point of `f` above `τ`),
  `rh_dvd_of_indec`, `rh_mod_mem` (`Cl(a, b)` contains `u_m·(x / u_m)` with `x`, `m ≥ 1`);
* `rh_eq` (**`ψ_{Ω₁}(B + u_β·D) = F_β(c + D)` and `D` is valid** when `d < F_β(c+d)` for every `d ≤ D`, `B` own,
  `u_β ∣ B`, `F_β(c) = ψ_{Ω₁}(B)`, given the fixed-point lemma below `β`), `rh_valid`;
* `rh_fwd_conv` (by induction on `β`): **`ψ_{Ω₁}(B)` is a fixed point of `F_β` for every own `B ≠ 0` with
  `u_{β+1} ∣ B` and `β < ψ_{Ω₁}(B)`** (FWD; no base point: for `z < ψ_{Ω₁}(B)` the collapses
  `ψ_{Ω₁}(e + u_β·d)`, `d ≤ z + 1`, `e = u_β·(B_p/u_β + 1)` for a strongly critical `p = ψ_{Ω₁}(B_p) > β, z`, are
  `z + 2` increasing values of `F_β` below `ψ_{Ω₁}(B)`, so `F_β(z) < ψ_{Ω₁}(B)`), and **conversely `u_{β+1} ∣ B` for
  every own `B` with `ψ_{Ω₁}(B)` a fixed point of `F_β`** (CONV); `rh_fwd`, `rh_conv`;
* `rhkB_psi` (**`B_n(ψ_{Ω₁}(B + u_β·D)) = ψ_{Ω₁}(B' + u_{B_n β}·B_n D)`**, `B' = α_ω + |σ r|`), `rh_dvd_sig`, `rhkB_dvd`
  (**`u_β ∣ B` gives `u_{B_n β} ∣ B'`**), `rh_dvd_A` (**`u_β ∣ A_η`** for `β < Ω₁`), `rh_fix_A` (**`ψ_{Ω₁}(A_η)` is a
  fixed point of every `F_β`, `β < ψ_{Ω₁}(A_η)`**).

No new axiom.  New definitions: the statement names `RhFWD`, `RhCONV`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rh

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Bc Googology.Trans.PoR.InaccPsi.R2.Sf Googology.Trans.PoR.InaccPsi.R2.Lq
  Googology.Trans.PoR.InaccPsi.R2.Rb Googology.Trans.PoR.InaccPsi.R2.Rd

variable {S : InaccSeq.{0}}

/-- **Below a point `x > τ` that is not a fixed point of a normal `f` there is a largest `p < x` that is `τ` or a fixed
point of `f` above `τ`.** -/
theorem rh_base_below {f : Ordinal.{0} → Ordinal.{0}} (hf : Order.IsNormal f) {τ x : Ordinal.{0}} (hτx : τ < x)
    (hnf : f x ≠ x) :
    ∃ p, (p = τ ∨ (τ < p ∧ f p = p)) ∧ p < x ∧ ∀ q, f q = q → τ < q → q < x → q ≤ p := by
  set P : Set Ordinal.{0} := {q | q < x ∧ (q = τ ∨ (τ < q ∧ f q = q))} with hPdef
  have hτP : τ ∈ P := ⟨hτx, Or.inl rfl⟩
  have hPne : P.Nonempty := ⟨τ, hτP⟩
  have hPb : BddAbove P := ⟨x, fun q hq => hq.1.le⟩
  set p := sSup P with hpdef
  have hpx : p ≤ x := csSup_le hPne fun q hq => hq.1.le
  have hτp : τ ≤ p := le_csSup hPb hτP
  have hmax : ∀ q, f q = q → τ < q → q < x → q ≤ p := fun q hq hτq hqx =>
    le_csSup hPb ⟨hqx, Or.inr ⟨hτq, hq⟩⟩
  have hbase : p = τ ∨ (τ < p ∧ f p = p) := by
    by_cases hmem : p ∈ P
    · exact hmem.2
    right
    have hτp' : τ < p := lt_of_le_of_ne hτp fun e => hmem (e ▸ hτP)
    refine ⟨hτp', ?_⟩
    have hcof : ∀ a < p, ∃ g, a < g ∧ g < p ∧ τ < g ∧ f g = g := by
      intro a ha
      obtain ⟨g, hgP, hg⟩ := exists_lt_of_lt_csSup hPne (max_lt ha hτp')
      have hgp : g < p := lt_of_le_of_ne (le_csSup hPb hgP) fun e => hmem (e ▸ hgP)
      have hτg : τ < g := (le_max_right a τ).trans_lt hg
      rcases hgP.2 with e | ⟨-, hgg⟩
      · exact absurd e hτg.ne'
      · exact ⟨g, (le_max_left a τ).trans_lt hg, hgp, hτg, hgg⟩
    have hlim : IsSuccLimit p := by
      refine Ordinal.isSuccLimit_iff.2 ⟨(lt_of_le_of_lt zero_le hτp').ne', ?_⟩
      refine isSuccPrelimit_of_succ_lt fun a ha => ?_
      obtain ⟨g, hag, hgp, -⟩ := hcof a ha
      exact (Order.succ_le_of_lt hag).trans_lt hgp
    refine le_antisymm (not_lt.1 fun hlt => ?_) hf.strictMono.le_apply
    obtain ⟨b, hb, hpb⟩ := (hf.lt_iff_exists_lt hlim).1 hlt
    obtain ⟨g, hbg, hgp, -, hgg⟩ := hcof b hb
    have : f b < g := by rw [← hgg]; exact hf.strictMono hbg
    exact absurd (hpb.trans (this.trans hgp)) (lt_irrefl _)
  have hpx' : p < x := by
    refine lt_of_le_of_ne hpx fun e => ?_
    rcases hbase with h | ⟨-, h⟩
    · exact hτx.ne (h ▸ e)
    · exact hnf (e ▸ h)
  exact ⟨p, hbase, hpx', hmax⟩

/-- An additive principal `p ≥ u_m` is a multiple of `u_m`. -/
theorem rh_dvd_of_indec (m : Ordinal.{0}) {p : Ordinal.{0}} (hp : Indec p) (h : Le.leOe m ≤ p) :
    Le.leOe m ∣ p := by
  obtain ⟨e, rfl⟩ := indec_eq_opow hp
  unfold Le.leOe at h ⊢
  have he : Om 1 * m ≤ e := (opow_le_opow_iff_right one_lt_omega0).1 h
  exact ⟨ω ^ (e - Om 1 * m), by rw [← opow_add, Ordinal.add_sub_cancel_of_le he]⟩

/-- **`Cl(a, b)` contains `u_m·(x / u_m)` with `x`** (`m ≥ 1`). -/
theorem rh_mod_mem {m : Ordinal.{0}} (hm : 1 ≤ m) {a b : Ordinal.{0}} :
    ∀ x, x ∈ S.CSet a b → Le.leOe m * (x / Le.leOe m) ∈ S.CSet a b := by
  set u := Le.leOe m with hudef
  have h0 : u ≠ 0 := rhU_ne m
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [Ordinal.zero_div, mul_zero]
    exact CSet.zero_mem _ _
  obtain ⟨hl, ht⟩ := lead_tail_mem hx hx0
  have hlt := lead_add_tail hx0
  rcases le_or_gt u (lead x) with h1 | h1
  · have hI : Indec (lead x) := indec_iff.2 ⟨(opow_pos _ omega0_pos).ne', isPrincipal_add_omega0_opow _⟩
    obtain ⟨k', hk'⟩ := rh_dvd_of_indec m hI h1
    have ih := IH (tail x) (tail_lt hx0) ht
    have e2 : u * (x / u) = lead x + u * (tail x / u) := by
      conv_lhs => rw [← hlt, hk']
      rw [Ordinal.mul_add_div _ h0, mul_add, hk']
    rw [e2]
    exact CSet.add_mem hl ih
  · have hlim : IsSuccLimit (Om 1 * m) :=
      isSuccLimit_mul_left (Om_isSuccLimit one_ne_zero) (lt_of_lt_of_le zero_lt_one hm)
    have hlog : Ordinal.log ω x < Om 1 * m := by
      have := h1
      unfold lead at this
      rw [hudef] at this
      unfold Le.leOe at this
      exact (opow_lt_opow_iff_right one_lt_omega0).1 this
    have hxu : x < u := by
      refine (lt_opow_log_add_one x).trans ?_
      rw [hudef]; unfold Le.leOe
      exact (opow_lt_opow_iff_right one_lt_omega0).2 (hlim.add_one_lt hlog)
    rw [Ordinal.div_eq_zero_of_lt hxu, mul_zero]
    exact CSet.zero_mem _ _

/-! ## The fixed-point lemmas -/

/-- **FWD(β)**: `ψ_{Ω₁}(B)` is a fixed point of `F_β` for every own `B ≠ 0` with `u_{β+1} ∣ B` and
`β < ψ_{Ω₁}(B)`. -/
def RhFWD (S : InaccSeq.{0}) (β : Ordinal.{0}) : Prop :=
  ∀ B : Ordinal.{0}, B ∈ S.CSet B (S.psi B (Om 1)) → Le.leOe (β + 1) ∣ B → B ≠ 0 → β < S.psi B (Om 1) →
    rhF β (S.psi B (Om 1)) = S.psi B (Om 1)

/-- **CONV(β)**: `u_{β+1} ∣ B` for every own `B` with `ψ_{Ω₁}(B)` a fixed point of `F_β`. -/
def RhCONV (S : InaccSeq.{0}) (β : Ordinal.{0}) : Prop :=
  ∀ B : Ordinal.{0}, B ∈ S.CSet B (S.psi B (Om 1)) → rhF β (S.psi B (Om 1)) = S.psi B (Om 1) →
    Le.leOe (β + 1) ∣ B

/-- `ψ_{Ω₁}(B) < ψ_{Ω₁}(B')` for an own `B < B'`. -/
theorem rh_psi_lt_of_own {B B' : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om 1))) (h : B < B') :
    S.psi B (Om 1) < S.psi B' (Om 1) :=
  psi_lt_psi_of_mem Low.InR_Om_one h ((psi_mono (S := S) Low.InR_Om_one h.le).2 hown)

/-! ## The bridge at level `β` -/

/-- **`ψ_{Ω₁}(B + u_β·D) = F_β(c + D)`, and `D < ψ_{Ω₁}(B + u_β·D)`**, when `d < F_β(c+d)` for every `d ≤ D`, for an
own `B` with `u_β ∣ B` and `F_β(c) = ψ_{Ω₁}(B)`, given FWD below `β`. -/
theorem rh_eq {β : Ordinal.{0}} (hF : ∀ j < β, RhFWD S j)
    {B c : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om 1))) (hB : Le.leOe β ∣ B)
    (hc : rhF β c = S.psi B (Om 1)) :
    ∀ D, D < Om 1 → (∀ d, d ≤ D → d < rhF β (c + d)) →
      D < S.psi (B + Le.leOe β * D) (Om 1) ∧ S.psi (B + Le.leOe β * D) (Om 1) = rhF β (c + D) := by
  set u := Le.leOe β with hudef
  have hupos : 0 < u := rhU_pos β
  intro D
  induction D using WellFoundedLT.induction with
  | ind D IH =>
  intro hDΩ hcond
  have hIH : ∀ d, d < D → S.psi (B + u * d) (Om 1) = rhF β (c + d) :=
    fun d hd => (IH d hd (hd.trans hDΩ) fun d' hd' => hcond d' (hd'.trans hd.le)).2
  have heq : S.psi (B + u * D) (Om 1) = rhF β (c + D) := by
    rcases eq_or_ne D 0 with rfl | hD0
    · rw [mul_zero, add_zero, add_zero, hc]
    set v := S.psi (B + u * D) (Om 1) with hv
    have hvSC : SC v := SC_psi Low.InR_Om_one _
    have hBv : S.psi B (Om 1) < v :=
      rh_psi_lt_of_own hown (lt_add_of_pos_right _ (mul_pos hupos (pos_iff_ne_zero.2 hD0)))
    have hβv : β < v := (rhF_left_le β c).trans_lt (hc ▸ hBv)
    have hlt : ∀ d, d < D → rhF β (c + d) < v := by
      intro d hd
      have hle : S.psi (B + u * d) (Om 1) ≤ v :=
        (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left B).2 (mul_le_mul_right hd.le _))).1
      have hdv : d < v := (hcond d hd.le).trans_le (by rw [← hIH d hd]; exact hle)
      have hmem : B + u * d ∈ S.CSet (B + u * D) v :=
        CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one (le_self_add : B ≤ B + u * D)).2 hown)
          (rhU_mul_mem hβv hdv)
      rw [← hIH d hd]
      exact psi_lt_psi_of_mem Low.InR_Om_one
        ((add_lt_add_iff_left B).2 ((mul_lt_mul_iff_right₀ hupos).2 hd)) hmem
    apply le_antisymm
    · exact rhk_UB β B c D hB hc.ge hDΩ.le
    · rcases zero_or_succ_or_isSuccLimit D with h0 | ⟨d0, rfl⟩ | hlim
      · exact absurd h0 hD0
      · rw [Order.succ_eq_add_one] at hlt hDΩ ⊢
        have hd0v : d0 < v := (hcond d0 (Order.le_succ d0)).trans (hlt d0 (lt_add_one d0))
        have hDv : d0 + 1 < v := hvSC.add_one_lt hd0v
        have hown1 : B + u * (d0 + 1) ∈ S.CSet (B + u * (d0 + 1)) v :=
          CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one (le_self_add : B ≤ B + u * (d0 + 1))).2 hown)
            (rhU_mul_mem hβv hDv)
        have hne : B + u * (d0 + 1) ≠ 0 :=
          (lt_of_lt_of_le (mul_pos hupos (lt_of_le_of_lt zero_le (lt_add_one d0))) le_add_self).ne'
        have hfix : ∀ j < β, rhF j v = v := fun j hj =>
          hF j hj _ hown1 ((rhU_dvd_succ hj).trans (dvd_add hB (dvd_mul_right _ _))) hne (hj.trans hβv)
        obtain ⟨e, he⟩ := rhF_range hvSC hfix
        rw [← he]
        refine (rhF_le β).2 (not_lt.1 fun hlt' => ?_)
        have hle : e ≤ c + d0 := by
          rw [← add_assoc] at hlt'; exact Order.lt_add_one_iff.1 hlt'
        have := ((rhF_le β).2 hle).trans_lt (hlt d0 (lt_add_one d0))
        rw [he] at this
        exact lt_irrefl _ this
      · refine not_lt.1 fun hlt' => ?_
        obtain ⟨e, he, hve⟩ := ((rhF_normal β).lt_iff_exists_lt (isSuccLimit_add c hlim)).1 hlt'
        rcases lt_or_ge e c with hec | hce
        · have : rhF β e < v := ((rhF_lt β).2 hec).trans_le (by rw [hc]; exact hBv.le)
          exact absurd hve (not_lt.2 this.le)
        · have hσe : c + (e - c) = e := Ordinal.add_sub_cancel_of_le hce
          have hσ : e - c < D := by rw [← hσe] at he; exact (add_lt_add_iff_left c).1 he
          have := hlt _ hσ
          rw [hσe] at this
          exact absurd hve (not_lt.2 this.le)
  exact ⟨by rw [heq]; exact hcond D le_rfl, heq⟩

/-- **A valid `D` has `d < F_β(c+d)` for every `d ≤ D`** (`u_β ∣ B`, `F_β(c) = ψ_{Ω₁}(B)`). -/
theorem rh_valid {β B c D : Ordinal.{0}} (hB : Le.leOe β ∣ B) (hc : rhF β c = S.psi B (Om 1))
    (hv : D < S.psi (B + Le.leOe β * D) (Om 1)) : ∀ d, d ≤ D → d < rhF β (c + d) := by
  intro d hd
  by_contra hle
  push Not at hle
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact absurd hle (not_le.2 (rhF_SC _ _).1)
  have hDΩ : D ≤ Om 1 := hv.le.trans (psi_lt Low.InR_Om_one _).le
  have hcl : ∀ j < β, ∀ z < rhF β (c + d), rhF j z < rhF β (c + d) := fun j hj z hz => by
    have := (rhF_lt j).2 hz
    rwa [rhF_fix_lower hj] at this
  have hprev : ∀ d'', d'' < D → d'' < rhF β (c + d) →
      S.psi (B + Le.leOe β * d'') (Om 1) < rhF β (c + d) := fun d'' hd'' hq =>
    (rhk_UB β B c d'' hB hc.ge (hd''.le.trans hDΩ)).trans_lt
      ((rhF_lt β).2 ((add_lt_add_iff_left c).2 (hq.trans_le hle)))
  have h := rhk_inv (S := S) hB (rhF_SC β (c + d)) hcl
    (by rw [← hc]; exact (rhF_lt β).2 (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hd0))) hDΩ hprev
  exact absurd ((h.trans hle).trans hd) (not_le.2 hv)

/-! ## The fixed points of `F_β` among the collapses -/

/-- `a < Ω₁·m`, `c < Ω₁` give `a + c < Ω₁·m`. -/
theorem rh_add_lt_Om1_mul {a c m : Ordinal.{0}} (ha : a < Om 1 * m) (hc : c < Om 1) : a + c < Om 1 * m :=
  rd_add_lt_of_dvd rb_Om1_indec (dvd_mul_right _ _) ha hc

/-- **At every level `β`: FWD(β) and CONV(β).** -/
theorem rh_fwd_conv (β : Ordinal.{0}) : RhFWD S β ∧ RhCONV S β := by
  induction β using WellFoundedLT.induction with
  | ind β IH =>
  have h0 := rd_Om1_ne
  constructor
  · -- FWD
    intro B hown hB hB0 hβx
    rcases eq_or_ne β 0 with rfl | hβ0
    · rw [rhF_zero]
      rw [zero_add, Le.leOe_one] at hB
      have hown0 : (0 : Ordinal.{0}) ∈ S.CSet 0 (S.psi 0 (Om 1)) := CSet.zero_mem _ _
      exact rbFix_of_dvd hown0 hown hB (psi_lt_psi Low.InR_Om_one (pos_iff_ne_zero.2 hB0) hown0)
    set x := S.psi B (Om 1) with hxdef
    have hx1 : x < Om 1 := psi_lt Low.InR_Om_one B
    have hxSC : SC x := SC_psi Low.InR_Om_one B
    have hxΓ : gamma x = x := by
      have h1 : Le.leOe (0 + 1) ∣ B := (rhU_dvd (by rw [zero_add]; exact le_add_self)).trans hB
      have := (IH 0 (pos_iff_ne_zero.2 hβ0)).1 B hown h1 hB0 hxSC.1
      rwa [rhF_zero] at this
    have hlimx : IsSuccLimit x := ev_isSuccLimit_of_inE (Gg.gg_SC_eps hxSC)
    set u := Le.leOe β with hudef
    have hu0 : u ≠ 0 := rhU_ne β
    have hupos : 0 < u := rhU_pos β
    obtain ⟨m, hm⟩ := hB
    rw [Le.leOe_succ, ← hudef, mul_assoc] at hm
    have key : ∀ z < x, rhF β z < x := by
      intro z hz
      set a := β + z + 1 with hadef
      have hax : a < x := hxSC.add_one_lt ((lq_SC_indec hxSC).add_lt hβx hz)
      set p := gamma a with hpdef
      have hpx : p < x := by rw [← hxΓ]; exact gamma_lt_gamma.2 hax
      have hpSC : SC p := lq_gamma_SC a
      have hap : a < p := lt_of_le_of_ne (lq_le_gamma a) fun e => SC.ne_add_one hpSC (β + z) e.symm
      have hβp : β < p := (le_self_add.trans_lt (lt_add_one (β + z))).trans hap
      have hz1p : z + 1 < p := by
        refine lt_of_le_of_lt ?_ hap
        rw [hadef, add_assoc]; exact le_add_self
      obtain ⟨Bp, hownp, hBp⟩ := rb_own_of_SC hpSC hpx
      have hBpB : Bp < B := by
        have h := compare_psi Low.InR_Om_one hownp hown
        rw [hBp, compare_lt_iff_lt.2 hpx] at h
        exact compare_lt_iff_lt.1 h.symm
      set e := u * (Bp / u) + u with hedef
      have hBpe : Bp ≤ e := by
        calc Bp = u * (Bp / u) + Bp % u := (Ordinal.div_add_mod Bp u).symm
          _ ≤ e := add_le_add_right (Ordinal.mod_lt Bp hu0).le _
      have hpe : p ≤ S.psi e (Om 1) := by rw [← hBp]; exact (psi_mono Low.InR_Om_one hBpe).1
      have hβe : β < S.psi e (Om 1) := hβp.trans_le hpe
      have hBpmem : Bp ∈ S.CSet e (S.psi e (Om 1)) := (psi_mono Low.InR_Om_one hBpe).2 hownp
      have howne : e ∈ S.CSet e (S.psi e (Om 1)) :=
        CSet.add_mem (rh_mod_mem (one_le_iff_ne_zero.2 hβ0) Bp hBpmem) (rhU_mem hβe)
      have hue : u ∣ e := ⟨Bp / u + 1, by rw [hedef, mul_add, mul_one]⟩
      have hue0 : 0 < e := lt_of_lt_of_le hupos le_add_self
      have hed : ∀ d, d < S.psi e (Om 1) →
          e + u * d ∈ S.CSet (e + u * d) (S.psi (e + u * d) (Om 1)) ∧
            ∃ w, rhF β w = S.psi (e + u * d) (Om 1) := by
        intro d hd
        have hle : S.psi e (Om 1) ≤ S.psi (e + u * d) (Om 1) := (psi_mono Low.InR_Om_one le_self_add).1
        have hownd : e + u * d ∈ S.CSet (e + u * d) (S.psi (e + u * d) (Om 1)) :=
          CSet.add_mem ((psi_mono Low.InR_Om_one le_self_add).2 howne)
            (rhU_mul_mem (hβe.trans_le hle) (hd.trans_le hle))
        refine ⟨hownd, rhF_range (SC_psi Low.InR_Om_one _) fun j hj => ?_⟩
        exact (IH j hj).1 _ hownd ((rhU_dvd_succ hj).trans (dvd_add hue (dvd_mul_right _ _)))
          (lt_of_lt_of_le hue0 le_self_add).ne' (hj.trans (hβe.trans_le hle))
      have hmono : ∀ d d', d < d' → d' < S.psi e (Om 1) →
          S.psi (e + u * d) (Om 1) < S.psi (e + u * d') (Om 1) := fun d d' hdd hd' =>
        rh_psi_lt_of_own (hed d (hdd.trans hd')).1
          ((add_lt_add_iff_left e).2 ((mul_lt_mul_iff_right₀ hupos).2 hdd))
      have hcount : ∀ d, d < S.psi e (Om 1) → ∀ w, rhF β w = S.psi (e + u * d) (Om 1) → d ≤ w := by
        intro d
        induction d using WellFoundedLT.induction with
        | ind d IHd =>
        intro hd w hw
        by_contra hwd
        push Not at hwd
        obtain ⟨w', hw'⟩ := (hed w (hwd.trans hd)).2
        have h1 := IHd w hwd (hwd.trans hd) w' hw'
        have h2 : rhF β w' < rhF β w := by rw [hw', hw]; exact hmono w d hwd hd
        exact absurd ((rhF_lt β).1 h2) (not_lt.2 h1)
      have hz1e : z + 1 < S.psi e (Om 1) := hz1p.trans_le hpe
      obtain ⟨w, hw⟩ := (hed (z + 1) hz1e).2
      have hzw : z < w := (lt_add_one z).trans_le (hcount (z + 1) hz1e w hw)
      have hlt : e + u * (z + 1) < B := by
        have hq : Bp / u < Om 1 * m := by
          rw [hm] at hBpB; exact (Ordinal.lt_mul_iff_div_lt hu0).1 hBpB
        have hc1 : 1 + (z + 1) < Om 1 :=
          rb_Om1_indec.add_lt (one_lt_omega0.trans_le (omega0_le_of_isSuccLimit (Om_isSuccLimit one_ne_zero)))
            ((Om_isSuccLimit one_ne_zero).add_one_lt (hz.trans hx1))
        have e1 : e + u * (z + 1) = u * (Bp / u + (1 + (z + 1))) := by
          simp only [hedef, mul_add, mul_one, add_assoc]
        rw [e1, hm]
        exact (mul_lt_mul_iff_right₀ hupos).2 (rh_add_lt_Om1_mul hq hc1)
      have hψlt : S.psi (e + u * (z + 1)) (Om 1) < x :=
        psi_lt_psi_of_mem Low.InR_Om_one hlt ((psi_mono Low.InR_Om_one hlt.le).2 (hed (z + 1) hz1e).1)
      calc rhF β z < rhF β w := (rhF_lt β).2 hzw
        _ = _ := hw
        _ < x := hψlt
    exact le_antisymm (((rhF_normal β).le_iff_forall_le hlimx).2 fun z hz => (key z hz).le)
      (rhF_le_self β x)
  · -- CONV
    intro B hown hfix
    set p := S.psi B (Om 1) with hpdef
    have hpSC : SC p := SC_psi Low.InR_Om_one B
    have hu : Le.leOe β ∣ B := by
      rcases zero_or_succ_or_isSuccLimit β with hz | ⟨j, rfl⟩ | hl
      · rw [hz, Le.leOe_zero]; exact one_dvd B
      · rw [Order.succ_eq_add_one] at IH hfix ⊢
        exact (IH j (lt_add_one j)).2 B hown (rhF_fix_mono le_self_add hfix)
      · exact rhU_dvd_lim hl fun j hj =>
          (rhU_dvd le_self_add).trans ((IH j hj).2 B hown (rhF_fix_mono hj.le hfix))
    set u := Le.leOe β with hudef
    set u2 := Le.leOe (β + 1) with hu2def
    have hu2 : u2 = u * Om 1 := Le.leOe_succ β
    have huu2 : u ∣ u2 := rhU_dvd le_self_add
    have hupos : 0 < u := rhU_pos β
    obtain ⟨m, hm⟩ := hu
    by_contra hnd
    set D0 := m % Om 1 with hD0
    set B0 := u2 * (m / Om 1) with hB0
    have hBe : B0 + u * D0 = B := by
      rw [hm, hB0, hD0, hu2, mul_assoc, ← mul_add, Ordinal.div_add_mod]
    have hD0lt : D0 < Om 1 := Ordinal.mod_lt m h0
    have hD00 : D0 ≠ 0 := by
      intro e
      apply hnd
      rw [← hBe, e, mul_zero, add_zero, hB0]
      exact dvd_mul_right _ _
    have hcoll : ∀ e, e < B → e ∈ S.CSet B p →
        (∀ j : Ordinal.{0}, e / Le.leOe j % Om 1 < p) → S.psi e (Om 1) < p :=
      fun e he heC _ => lt_psi_of_mem Low.InR_Om_one
        (CSet.psi_mem he Low.InR_Om_one (mem_CSet_psi Low.InR_Om_one B) heC) (psi_lt Low.InR_Om_one _)
    have hdig := rhk_digits (S := S) hpSC hcoll B hown β
    have hmdiv : B / u = m := by rw [hm, Ordinal.mul_div_cancel _ (rhU_ne _)]
    rw [← hudef, hmdiv] at hdig
    have hD0p : D0 < p := hdig
    have hlt' : u * D0 < u2 := by rw [hu2]; exact (mul_lt_mul_iff_right₀ hupos).2 hD0lt
    have hBdiv : B / u2 = m / Om 1 := by
      calc B / u2 = (u2 * (m / Om 1) + u * D0) / u2 := by rw [← hB0, hBe]
        _ = m / Om 1 := by
          rw [Ordinal.mul_add_div _ (rhU_ne (β + 1)), Ordinal.div_eq_zero_of_lt hlt', add_zero]
    have hB0m : B0 ∈ S.CSet B p := by
      have := rh_mod_mem (S := S) (m := β + 1) le_add_self B hown
      rwa [← hu2def, hBdiv] at this
    have hB0B : B0 < B := by
      rw [← hBe]; exact lt_add_of_pos_right _ (mul_pos hupos (pos_iff_ne_zero.2 hD00))
    have hB0p : S.psi B0 (Om 1) < p := psi_lt_psi_of_mem Low.InR_Om_one hB0B hB0m
    have hle := rhk_UB (S := S) β B0 (S.psi B0 (Om 1)) D0
      (by rw [hB0]; exact huu2.trans (dvd_mul_right _ _)) (rhF_le_self _ _) hD0lt.le
    rw [hBe] at hle
    have hlt : S.psi B0 (Om 1) + D0 < p := (lq_SC_indec hpSC).add_lt hB0p hD0p
    have h2 : rhF β (S.psi B0 (Om 1) + D0) < p := by
      conv_rhs => rw [← hfix]
      exact (rhF_lt β).2 hlt
    exact absurd (hle.trans_lt h2) (lt_irrefl _)

/-- **`ψ_{Ω₁}(B)` is a fixed point of `F_β`** for every own `B ≠ 0` with `u_{β+1} ∣ B` and `β < ψ_{Ω₁}(B)`. -/
theorem rh_fwd (β : Ordinal.{0}) : RhFWD S β := (rh_fwd_conv β).1

/-- **`u_{β+1} ∣ B`** for every own `B` with `ψ_{Ω₁}(B)` a fixed point of `F_β`. -/
theorem rh_conv (β : Ordinal.{0}) : RhCONV S β := (rh_fwd_conv β).2

/-! ## `B_n` and `σ` at level `β` -/

/-- **`B_n(ψ_{Ω₁}(B + u_β·D)) = ψ_{Ω₁}(B' + u_{B_n β}·B_n D)`** (`1 ≤ β < Ω₁`, `β < L(n+2)`) for an own `B` in the
window and an own `B + u_β·D` with a countable `D < L(n+2)`, with `B = α_{n+1} + |r|`, `B' = α_ω + |σ r|` own and
`B_n(ψ_{Ω₁}(B)) = ψ_{Ω₁}(B')`. -/
theorem rhkB_psi {n : ℕ} {β : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβΩ : β < Om 1) (hβc : β < Bc.bcC S (n + 1))
    {B D : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om 1)))
    (hlo : Bc.bcC S n ≤ S.psi B (Om 1))
    (hown1 : B + Le.leOe β * D ∈ S.CSet (B + Le.leOe β * D) (S.psi (B + Le.leOe β * D) (Om 1)))
    (hhi : S.psi (B + Le.leOe β * D) (Om 1) < Bc.bcC S (n + 1)) (hD1 : D < Om 1)
    (hDc : D < Bc.bcC S (n + 1)) :
    ∃ r : Term, bcD S r ∧ B = bcAlpha S (n + 1) + val S r ∧
      bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) ∈
        S.CSet (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r))
          (S.psi (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r)) (Om 1)) ∧
      Bc.bcB S n (S.psi B (Om 1)) = S.psi (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r)) (Om 1) ∧
      Bc.bcB S n (S.psi (B + Le.leOe β * D) (Om 1)) =
        S.psi (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) + Le.leOe (Bc.bcB S n β) *
          Bc.bcB S n D) (Om 1) := by
  obtain ⟨hDm, hBm⟩ := Le.leB_Oe (S := S) (n := n) hβΩ hβc hβ1 hD1 hDc
  obtain ⟨r, h1, h2, h3, h4, h5⟩ := rdB_psi_baseD hown hlo hown1 hhi hDm
  exact ⟨r, h1, h2, h3, h4, by rw [h5, hBm]⟩

/-- **`σ` maps `u_β ≤ |v|` to `u_{B_n β} ≤ |σ v|`** on its domain. -/
theorem rh_u_le_sig {n : ℕ} {β : Ordinal.{0}} (hβΩ : β < Om 1) (hβc : β < Bc.bcC S (n + 1)) {v : Term}
    (hv : bcD S v) (h : Le.leOe β ≤ val S v) :
    Le.leOe (Bc.bcB S n β) ≤ val S (bcSig (bcPre (n + 1)) bcPreW v) := by
  obtain ⟨hDu, hBu⟩ := Le.leB_Oe1 (S := S) (n := n) hβΩ hβc
  have hDv := Mv.mvD_of_term hv
  rw [← Mv.mvB_term (k := n) hv, ← hBu]
  exact not_lt.1 fun hlt => absurd ((Mv.mvB_lt_iff hDv hDu).1 hlt) (not_lt.2 h)

/-- **`σ` maps `u_β ∣ |r|` to `u_{B_n β} ∣ |σ r|`** on its domain. -/
theorem rh_dvd_sig {n : ℕ} {β : Ordinal.{0}} (hβΩ : β < Om 1) (hβc : β < Bc.bcC S (n + 1)) {r : Term}
    (hr : bcD S r) (h : Le.leOe β ∣ val S r) :
    Le.leOe (Bc.bcB S n β) ∣ val S (bcSig (bcPre (n + 1)) bcPreW r) := by
  by_cases h0 : r = Term.zero
  · subst h0; rw [bcSig_zero]; exact dvd_zero _
  have hN' := bc_NF (k := n) hr
  have h0' : bcSig (bcPre (n + 1)) bcPreW r ≠ Term.zero := bcSig_ne_zero h0
  rw [rd_dvd_iff_last (rhU_indec _) hN' h0', rbLast_sig]
  exact rh_u_le_sig hβΩ hβc (rbLast_D hr) ((rd_dvd_iff_last (rhU_indec β) hr.1 h0).1 h)

/-- An `ε`-number above `Ω₁` is a multiple of every `u_β`, `β < Ω₁`. -/
theorem rh_dvd_eps {β p : Ordinal.{0}} (hβΩ : β < Om 1) (hp : ω ^ p = p) (h : Om 1 < p) : Le.leOe β ∣ p := by
  have hI : Indec p := inE_indec hp
  have h2 : Om 1 + Om 1 < p := hI.add_lt h h
  have hk : Om 1 * β < p := by
    calc Om 1 * β < Om 1 * Om 1 := (mul_lt_mul_iff_right₀ rb_Om1_indec.pos).2 hβΩ
      _ = ω ^ (Om 1 + Om 1) := rd_u_eq
      _ < ω ^ p := (opow_lt_opow_iff_right one_lt_omega0).2 h2
      _ = p := hp
  refine rh_dvd_of_indec β hI ?_
  unfold Le.leOe
  rw [← hp]
  exact opow_le_opow_right omega0_pos hk.le

theorem rh_dvd_OmW {β : Ordinal.{0}} (hβΩ : β < Om 1) : Le.leOe β ∣ Om (ω : Ordinal.{0}) :=
  rh_dvd_eps hβΩ (Low.opow_eq_self_of_SC (SC_Om omega0_pos.ne')) (Om_lt_Om.2 one_lt_omega0)

theorem rh_dvd_Pp {β : Ordinal.{0}} (hβΩ : β < Om 1) : Le.leOe β ∣ Nc.ncPp S :=
  rh_dvd_eps hβΩ (Low.opow_eq_self_of_SC (Nc.ncPp_SC S)) rb_Om1_lt_Pp

theorem rh_dvd_alpha {β : Ordinal.{0}} (hβΩ : β < Om 1) (j : ℕ) : Le.leOe β ∣ bcAlpha S j :=
  dvd_add (dvd_add (rh_dvd_OmW hβΩ) (rh_dvd_OmW hβΩ)) (dvd_mul_of_dvd_left (rh_dvd_Pp hβΩ) _)

theorem rh_dvd_alphaW {β : Ordinal.{0}} (hβΩ : β < Om 1) : Le.leOe β ∣ bcAlphaW S := by
  refine dvd_add (dvd_add (rh_dvd_OmW hβΩ) (rh_dvd_OmW hβΩ)) ?_
  have hE : ω ^ Nc.ncPp S = Nc.ncPp S := Low.opow_eq_self_of_SC (Nc.ncPp_SC S)
  have h1 := rh_dvd_Pp (S := S) hβΩ
  have hI : Indec (ω ^ (Nc.ncPp S + 1)) :=
    indec_iff.2 ⟨(opow_pos _ omega0_pos).ne', isPrincipal_add_omega0_opow _⟩
  refine rh_dvd_of_indec β hI ((Ordinal.le_of_dvd (inE_indec hE).ne_zero h1).trans ?_)
  conv_lhs => rw [← hE]
  exact opow_le_opow_right omega0_pos le_self_add

/-- `B_n β < Ω₁` for `β < L(n+2)`. -/
theorem rhB_lt_Om1 {n : ℕ} {β : Ordinal.{0}} (hβc : β < Bc.bcC S (n + 1)) : Bc.bcB S n β < Om 1 :=
  (Bc.bcB_bound n _ hβc).trans (InaccSeq.psi_lt Low.InR_Om_one _)

/-- **`u_β ∣ B` gives `u_{B_n β} ∣ B'`** for `B = α_{n+1} + |r|`, `B' = α_ω + |σ r|` (`β < Ω₁`, `β < L(n+2)`). -/
theorem rhkB_dvd {n : ℕ} {β : Ordinal.{0}} (hβΩ : β < Om 1) (hβc : β < Bc.bcC S (n + 1)) {B : Ordinal.{0}}
    {r : Term} (hr : bcD S r) (hB : B = bcAlpha S (n + 1) + val S r) (h : Le.leOe β ∣ B) :
    Le.leOe (Bc.bcB S n β) ∣ bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) := by
  rw [hB, rd_dvd_add_left (rh_dvd_alpha hβΩ _)] at h
  rw [rd_dvd_add_left (rh_dvd_alphaW (rhB_lt_Om1 hβc))]
  exact rh_dvd_sig hβΩ hβc hr h

/-- **`u_β ∣ A_η`** for `β < Ω₁`. -/
theorem rh_dvd_A {β : Ordinal.{0}} (hβΩ : β < Om 1) (η : Ordinal.{0}) : Le.leOe β ∣ ConjT.Aη S η := by
  have h2 : Le.leOe β ∣ ConjT.th S :=
    rh_dvd_eps hβΩ (Low.opow_eq_self_of_SC (ConjT.SC_th S)) Bt.Om1_lt_th
  exact dvd_add (rh_dvd_OmW hβΩ) (h2.mul_right η)

/-- **The `υ`-point `ψ_{Ω₁}(A_η)` is a fixed point of every `F_β`, `β < ψ_{Ω₁}(A_η)`** (`A_η` own). -/
theorem rh_fix_A {β η : Ordinal.{0}} (hown : ConjT.Aη S η ∈ S.CSet (ConjT.Aη S η) (S.psi (ConjT.Aη S η) (Om 1)))
    (hβ : β < S.psi (ConjT.Aη S η) (Om 1)) :
    rhF β (S.psi (ConjT.Aη S η) (Om 1)) = S.psi (ConjT.Aη S η) (Om 1) := by
  have hβΩ : β < Om 1 := hβ.trans (psi_lt Low.InR_Om_one _)
  refine rh_fwd β _ hown (rh_dvd_A ((Om_isSuccLimit one_ne_zero).add_one_lt hβΩ) η) ?_ hβ
  unfold ConjT.Aη; exact (lt_of_lt_of_le (SC_Om omega0_pos.ne').1 le_self_add).ne'

end Googology.Trans.PoR.InaccPsi.R2.Rh

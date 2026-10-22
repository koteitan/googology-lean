import Googology.Trans.PoR.InaccPsi.R2.RdKFn

/-!
# `ψ_{Ω₁}(B + Ω₁^k·D) = F_k(c + D)`, the fixed points of `F_k` among the collapses, and `B_n` there, at every level

`ψ = S.psi`, `F_k = rdFk k` (`F_0 = Γ_`, `F_{k+1} = deriv F_k`), `u_k = Ω₁^k = Le.leOe k`, `B_n = Bc.bcB S n`,
`σ = bcSig (bcPre (n+1)) bcPreW`.  An argument `B` is *own* when `B ∈ Cl(B, ψ_{Ω₁}(B))`.

* `rdk_base_below` (the largest point below `x` that is `τ` or a fixed point of `F_k` above `τ`), `rdk_dvd_of_indec`,
  `rdk_mod_mem` (`Cl(a, b)` contains `u_m·(x / u_m)` with `x`, `m ≥ 1`);
* `rdk_eq` (**`ψ_{Ω₁}(B + u_{k+1}·D) = F_{k+1}(c + D)` and `D` is valid** when `d < F_{k+1}(c+d)` for every `d ≤ D`,
  `B` own, `u_{k+1} ∣ B`, `F_{k+1}(c) = ψ_{Ω₁}(B)`, given the fixed-point lemma at level `k`), `rdk_valid` (**a valid
  `D` has `d < F_{k+1}(c+d)` for every `d ≤ D`**);
* `rdk_fwd_conv` (by induction on `k`): **`ψ_{Ω₁}(B)` is a fixed point of `F_k` for every own `B ≠ 0` with
  `u_{k+1} ∣ B`**, and **conversely `u_{k+1} ∣ B` for every own `B` with `ψ_{Ω₁}(B)` a fixed point of `F_k`**;
  `rdk_fwd`, `rdk_conv`;
* `rdkB_psi` (**`B_n(ψ_{Ω₁}(B + u_k·D)) = ψ_{Ω₁}(B' + u_k·B_n D)`**, `B' = α_ω + |σ r|`), `rdkB_u` (`B_n u_k = u_k`),
  `rdk_dvd_sig`, `rdkB_dvd` (**`σ` keeps `u_k ∣ ·`**), `rdk_dvd_A` (**`u_k ∣ A_η`**).

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Bc Googology.Trans.PoR.InaccPsi.R2.Sf Googology.Trans.PoR.InaccPsi.R2.Lq
  Googology.Trans.PoR.InaccPsi.R2.Rb

variable {S : InaccSeq.{0}}

/-- **Below a point `x > τ` that is not a fixed point of `F_k` there is a largest `p < x` that is `τ` or a fixed point
of `F_k` above `τ`.** -/
theorem rdk_base_below (k : ℕ) {τ x : Ordinal.{0}} (hτx : τ < x) (hnf : rdFk k x ≠ x) :
    ∃ p, (p = τ ∨ (τ < p ∧ rdFk k p = p)) ∧ p < x ∧ ∀ q, rdFk k q = q → τ < q → q < x → q ≤ p := by
  set P : Set Ordinal.{0} := {q | q < x ∧ (q = τ ∨ (τ < q ∧ rdFk k q = q))} with hPdef
  have hτP : τ ∈ P := ⟨hτx, Or.inl rfl⟩
  have hPne : P.Nonempty := ⟨τ, hτP⟩
  have hPb : BddAbove P := ⟨x, fun q hq => hq.1.le⟩
  set p := sSup P with hpdef
  have hpx : p ≤ x := csSup_le hPne fun q hq => hq.1.le
  have hτp : τ ≤ p := le_csSup hPb hτP
  have hmax : ∀ q, rdFk k q = q → τ < q → q < x → q ≤ p := fun q hq hτq hqx =>
    le_csSup hPb ⟨hqx, Or.inr ⟨hτq, hq⟩⟩
  have hbase : p = τ ∨ (τ < p ∧ rdFk k p = p) := by
    by_cases hmem : p ∈ P
    · exact hmem.2
    right
    have hτp' : τ < p := lt_of_le_of_ne hτp fun e => hmem (e ▸ hτP)
    refine ⟨hτp', ?_⟩
    have hcof : ∀ a < p, ∃ f, a < f ∧ f < p ∧ τ < f ∧ rdFk k f = f := by
      intro a ha
      obtain ⟨f, hfP, hf⟩ := exists_lt_of_lt_csSup hPne (max_lt ha hτp')
      have hfp : f < p := lt_of_le_of_ne (le_csSup hPb hfP) fun e => hmem (e ▸ hfP)
      have hτf : τ < f := (le_max_right a τ).trans_lt hf
      rcases hfP.2 with e | ⟨-, hff⟩
      · exact absurd e hτf.ne'
      · exact ⟨f, (le_max_left a τ).trans_lt hf, hfp, hτf, hff⟩
    have hlim : IsSuccLimit p := by
      refine Ordinal.isSuccLimit_iff.2 ⟨(lt_of_le_of_lt zero_le hτp').ne', ?_⟩
      refine isSuccPrelimit_of_succ_lt fun a ha => ?_
      obtain ⟨f, haf, hfp, -⟩ := hcof a ha
      exact (Order.succ_le_of_lt haf).trans_lt hfp
    refine le_antisymm (not_lt.1 fun hlt => ?_) (rdFk_le_self k p)
    obtain ⟨b, hb, hpb⟩ := ((rdFk_normal k).lt_iff_exists_lt hlim).1 hlt
    obtain ⟨f, hbf, hfp, -, hff⟩ := hcof b hb
    have : rdFk k b < f := by rw [← hff]; exact (rdFk_lt k).2 hbf
    exact absurd (hpb.trans (this.trans hfp)) (lt_irrefl _)
  have hpx' : p < x := by
    refine lt_of_le_of_ne hpx fun e => ?_
    rcases hbase with h | ⟨-, h⟩
    · exact hτx.ne (h ▸ e)
    · exact hnf (e ▸ h)
  exact ⟨p, hbase, hpx', hmax⟩

/-- An additive principal `p ≥ u_m` is a multiple of `u_m`. -/
theorem rdk_dvd_of_indec (m : ℕ) {p : Ordinal.{0}} (hp : Indec p) (h : Le.leOe (m : Ordinal.{0}) ≤ p) :
    Le.leOe (m : Ordinal.{0}) ∣ p := by
  obtain ⟨e, rfl⟩ := indec_eq_opow hp
  unfold Le.leOe at h ⊢
  have he : Om 1 * (m : Ordinal.{0}) ≤ e := (opow_le_opow_iff_right one_lt_omega0).1 h
  exact ⟨ω ^ (e - Om 1 * (m : Ordinal.{0})), by rw [← opow_add, Ordinal.add_sub_cancel_of_le he]⟩

/-- **`Cl(a, b)` contains `u_m·(x / u_m)` with `x`** (`m ≥ 1`). -/
theorem rdk_mod_mem {m : ℕ} (hm : 1 ≤ m) {a b : Ordinal.{0}} :
    ∀ x, x ∈ S.CSet a b → Le.leOe (m : Ordinal.{0}) * (x / Le.leOe (m : Ordinal.{0})) ∈ S.CSet a b := by
  set u := Le.leOe (m : Ordinal.{0}) with hudef
  have h0 : u ≠ 0 := rdU_ne m
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
    obtain ⟨k', hk'⟩ := rdk_dvd_of_indec m hI h1
    have ih := IH (tail x) (tail_lt hx0) ht
    have e2 : u * (x / u) = lead x + u * (tail x / u) := by
      conv_lhs => rw [← hlt, hk']
      rw [Ordinal.mul_add_div _ h0, mul_add, hk']
    rw [e2]
    exact CSet.add_mem hl ih
  · have hlim : IsSuccLimit (Om 1 * (m : Ordinal.{0})) := by
      obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le hm
      rw [Nat.add_comm, Nat.cast_succ, mul_add_one]
      exact isSuccLimit_add _ (Om_isSuccLimit one_ne_zero)
    have hlog : Ordinal.log ω x < Om 1 * (m : Ordinal.{0}) := by
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


/-! ## The bridge at level `k + 1` -/

/-- **`ψ_{Ω₁}(B + u_{k+1}·D) = F_{k+1}(c + D)`, and `D < ψ_{Ω₁}(B + u_{k+1}·D)`**, when `d < F_{k+1}(c+d)` for every
`d ≤ D`, for an own `B` with `u_{k+1} ∣ B` and `F_{k+1}(c) = ψ_{Ω₁}(B)`, given the fixed-point lemma at level `k`. -/
theorem rdk_eq {k : ℕ}
    (hF : ∀ B : Ordinal.{0}, B ∈ S.CSet B (S.psi B (Om 1)) → Le.leOe ((k + 1 : ℕ) : Ordinal.{0}) ∣ B → B ≠ 0 →
      rdFk k (S.psi B (Om 1)) = S.psi B (Om 1))
    {B c : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om 1))) (hB : Le.leOe ((k + 1 : ℕ) : Ordinal.{0}) ∣ B)
    (hc : rdFk (k + 1) c = S.psi B (Om 1)) :
    ∀ D, D < Om 1 → (∀ d, d ≤ D → d < rdFk (k + 1) (c + d)) →
      D < S.psi (B + Le.leOe ((k + 1 : ℕ) : Ordinal.{0}) * D) (Om 1) ∧
        S.psi (B + Le.leOe ((k + 1 : ℕ) : Ordinal.{0}) * D) (Om 1) = rdFk (k + 1) (c + D) := by
  set u := Le.leOe ((k + 1 : ℕ) : Ordinal.{0}) with hudef
  have hupos : 0 < u := rdU_pos (k + 1)
  intro D
  induction D using WellFoundedLT.induction with
  | ind D IH =>
  intro hDΩ hcond
  have hIH : ∀ d, d < D → S.psi (B + u * d) (Om 1) = rdFk (k + 1) (c + d) :=
    fun d hd => (IH d hd (hd.trans hDΩ) fun d' hd' => hcond d' (hd'.trans hd.le)).2
  have heq : S.psi (B + u * D) (Om 1) = rdFk (k + 1) (c + D) := by
    rcases eq_or_ne D 0 with rfl | hD0
    · rw [mul_zero, add_zero, add_zero, hc]
    set v := S.psi (B + u * D) (Om 1) with hv
    have hvSC : SC v := SC_psi Low.InR_Om_one _
    have hBv : S.psi B (Om 1) ≤ v := (psi_mono (S := S) Low.InR_Om_one le_self_add).1
    have hlt : ∀ d, d < D → rdFk (k + 1) (c + d) < v := by
      intro d hd
      have hle : S.psi (B + u * d) (Om 1) ≤ v :=
        (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left B).2 (mul_le_mul_right hd.le _))).1
      have hdv : d < v := (hcond d hd.le).trans_le (by rw [← hIH d hd]; exact hle)
      have hmem : B + u * d ∈ S.CSet (B + u * D) v :=
        CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one (le_self_add : B ≤ B + u * D)).2 hown)
          (rdU_mul_mem (k + 1) hdv)
      rw [← hIH d hd]
      exact psi_lt_psi_of_mem Low.InR_Om_one
        ((add_lt_add_iff_left B).2 ((mul_lt_mul_iff_right₀ hupos).2 hd)) hmem
    apply le_antisymm
    · exact rdk_UB (k + 1) B c D hB hc.ge hDΩ.le
    · rcases zero_or_succ_or_isSuccLimit D with h0 | ⟨d0, rfl⟩ | hlim
      · exact absurd h0 hD0
      · rw [Order.succ_eq_add_one] at hlt hDΩ ⊢
        have hd0v : d0 < v := (hcond d0 (Order.le_succ d0)).trans (hlt d0 (lt_add_one d0))
        have hDv : d0 + 1 < v := hvSC.add_one_lt hd0v
        have hown1 : B + u * (d0 + 1) ∈ S.CSet (B + u * (d0 + 1)) v :=
          CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one (le_self_add : B ≤ B + u * (d0 + 1))).2 hown)
            (rdU_mul_mem (k + 1) hDv)
        have hne : B + u * (d0 + 1) ≠ 0 :=
          (lt_of_lt_of_le (mul_pos hupos (lt_of_le_of_lt zero_le (lt_add_one d0))) le_add_self).ne'
        have hfix : rdFk k v = v := hF _ hown1 (dvd_add hB (dvd_mul_right _ _)) hne
        obtain ⟨e, he⟩ := rdFk_of_fix hfix
        rw [← he]
        refine (rdFk_le (k + 1)).2 (not_lt.1 fun hlt' => ?_)
        have hle : e ≤ c + d0 := by
          rw [← add_assoc] at hlt'; exact Order.lt_add_one_iff.1 hlt'
        have := ((rdFk_le (k + 1)).2 hle).trans_lt (hlt d0 (lt_add_one d0))
        rw [he] at this
        exact lt_irrefl _ this
      · refine not_lt.1 fun hlt' => ?_
        obtain ⟨e, he, hve⟩ := ((rdFk_normal (k + 1)).lt_iff_exists_lt (isSuccLimit_add c hlim)).1 hlt'
        rcases lt_or_ge e c with hec | hce
        · have : rdFk (k + 1) e < v := ((rdFk_lt (k + 1)).2 hec).trans_le (by rw [hc]; exact hBv)
          exact absurd hve (not_lt.2 this.le)
        · have hσe : c + (e - c) = e := Ordinal.add_sub_cancel_of_le hce
          have hσ : e - c < D := by rw [← hσe] at he; exact (add_lt_add_iff_left c).1 he
          have := hlt _ hσ
          rw [hσe] at this
          exact absurd hve (not_lt.2 this.le)
  exact ⟨by rw [heq]; exact hcond D le_rfl, heq⟩

/-- **A valid `D` has `d < F_{k+1}(c+d)` for every `d ≤ D`** (`u_{k+1} ∣ B`, `F_{k+1}(c) = ψ_{Ω₁}(B)`). -/
theorem rdk_valid {k : ℕ} {B c D : Ordinal.{0}} (hB : Le.leOe ((k + 1 : ℕ) : Ordinal.{0}) ∣ B)
    (hc : rdFk (k + 1) c = S.psi B (Om 1))
    (hv : D < S.psi (B + Le.leOe ((k + 1 : ℕ) : Ordinal.{0}) * D) (Om 1)) :
    ∀ d, d ≤ D → d < rdFk (k + 1) (c + d) := by
  intro d hd
  by_contra hle
  push Not at hle
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact absurd hle (not_le.2 (rdFk_SC _ _).1)
  have hDΩ : D ≤ Om 1 := hv.le.trans (psi_lt Low.InR_Om_one _).le
  have hcl : ∀ j < k + 1, ∀ z < rdFk (k + 1) (c + d), rdFk j z < rdFk (k + 1) (c + d) := fun j hj z hz => by
    have := (rdFk_lt j).2 hz
    rwa [rdFk_fix_lower hj] at this
  have hprev : ∀ d'', d'' < D → d'' < rdFk (k + 1) (c + d) →
      S.psi (B + Le.leOe ((k + 1 : ℕ) : Ordinal.{0}) * d'') (Om 1) < rdFk (k + 1) (c + d) := fun d'' hd'' hq =>
    (rdk_UB (k + 1) B c d'' hB hc.ge (hd''.le.trans hDΩ)).trans_lt
      ((rdFk_lt (k + 1)).2 ((add_lt_add_iff_left c).2 (hq.trans_le hle)))
  have h := rdk_inv (S := S) hB (rdFk_SC (k + 1) (c + d)) hcl
    (by rw [← hc]; exact (rdFk_lt (k + 1)).2 (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hd0))) hDΩ hprev
  exact absurd ((h.trans hle).trans hd) (not_le.2 hv)

/-! ## The fixed points of `F_k` among the collapses -/

/-- **At every level `k`: `ψ_{Ω₁}(B)` is a fixed point of `F_k` for every own `B ≠ 0` with `u_{k+1} ∣ B`, and
`u_{k+1} ∣ B` for every own `B` with `ψ_{Ω₁}(B)` a fixed point of `F_k`.** -/
theorem rdk_fwd_conv : ∀ k : ℕ,
    (∀ B : Ordinal.{0}, B ∈ S.CSet B (S.psi B (Om 1)) → Le.leOe ((k + 1 : ℕ) : Ordinal.{0}) ∣ B → B ≠ 0 →
      rdFk k (S.psi B (Om 1)) = S.psi B (Om 1)) ∧
    (∀ B : Ordinal.{0}, B ∈ S.CSet B (S.psi B (Om 1)) → rdFk k (S.psi B (Om 1)) = S.psi B (Om 1) →
      Le.leOe ((k + 1 : ℕ) : Ordinal.{0}) ∣ B)
  | 0 => by
    refine ⟨fun B hown hB hB0 => ?_, fun B hown hfix => ?_⟩
    · rw [rdU_one] at hB
      have hown0 : (0 : Ordinal.{0}) ∈ S.CSet 0 (S.psi 0 (Om 1)) := CSet.zero_mem _ _
      exact rbFix_of_dvd hown0 hown hB (psi_lt_psi Low.InR_Om_one (pos_iff_ne_zero.2 hB0) hown0)
    · rw [rdU_one]; exact rbDvd_of_fix hown hfix
  | k + 1 => by
    obtain ⟨hF, hC⟩ := rdk_fwd_conv k
    set u := Le.leOe ((k + 1 : ℕ) : Ordinal.{0}) with hudef
    set u2 := Le.leOe ((k + 1 + 1 : ℕ) : Ordinal.{0}) with hu2def
    have hu2 : u2 = u * Om 1 := rdU_succ (k + 1)
    have huu2 : u ∣ u2 := rdU_dvd (Nat.le_succ _)
    have hupos : 0 < u := rdU_pos (k + 1)
    constructor
    · -- the fixed points
      intro B hown hB hB0
      set x := S.psi B (Om 1) with hxdef
      have hx1 : x < Om 1 := psi_lt Low.InR_Om_one B
      have hFk : rdFk k x = x := hF B hown (huu2.trans hB) hB0
      by_contra hnf
      obtain ⟨y, hy⟩ := rdFk_of_fix hFk
      have hyx : y < x := by
        refine lt_of_le_of_ne (hy ▸ rdFk_le_self (k + 1) y) fun e => hnf ?_
        rw [← e] at hy ⊢; rw [hy]
      have huB : u < B := (rdU_lt (Nat.lt_succ_self (k + 1))).trans_le (Ordinal.le_of_dvd hB0 hB)
      have hown0 : u ∈ S.CSet u (S.psi u (Om 1)) := rdU_own (k + 1)
      have hlt0 : S.psi u (Om 1) < x := psi_lt_psi_of_mem Low.InR_Om_one huB (rdU_mem (k + 1) _ _)
      have hfix0 : rdFk k (S.psi u (Om 1)) = S.psi u (Om 1) := hF u hown0 (dvd_refl _) (rdU_ne _)
      obtain ⟨p, hbase, hpx, hmax⟩ := rdk_base_below (k + 1) hlt0 hnf
      have hpk : rdFk k p = p := by
        rcases hbase with e | ⟨-, h⟩
        · rw [e]; exact hfix0
        · exact rdFk_fix_mono (Nat.le_succ k) h
      obtain ⟨c, hc⟩ := rdFk_of_fix hpk
      obtain ⟨Bp, hownp, hBp, hdvdp⟩ : ∃ Bp, Bp ∈ S.CSet Bp (S.psi Bp (Om 1)) ∧ S.psi Bp (Om 1) = p ∧
          u ∣ Bp := by
        rcases hbase with e | -
        · exact ⟨u, hown0, e.symm, dvd_refl _⟩
        · obtain ⟨Bp, hownp, hBp⟩ := rb_own_of_SC (hc ▸ rdFk_SC (k + 1) c) hpx
          exact ⟨Bp, hownp, hBp, hC Bp hownp (by rw [hBp]; exact hpk)⟩
      have hcy : c < y := (rdFk_lt (k + 1)).1 (by rw [hc, hy]; exact hpx)
      set D := y - c with hDdef
      have hcD : c + D = y := Ordinal.add_sub_cancel_of_le hcy.le
      have hcond : ∀ d, d ≤ D → d < rdFk (k + 1) (c + d) := by
        intro d hd
        by_contra hle
        push Not at hle
        have hz : rdFk (k + 1) (c + d) = c + d :=
          le_antisymm (hle.trans le_add_self) (rdFk_le_self _ _)
        have hzy : c + d ≤ y := by rw [← hcD]; exact (add_le_add_iff_left c).2 hd
        have hpz : p ≤ c + d := by rw [← hc, ← hz]; exact (rdFk_le (k + 1)).2 le_self_add
        rcases hpz.lt_or_eq with hpz | hpz
        · have hτz : S.psi u (Om 1) < c + d := by
            rcases hbase with e | ⟨h, -⟩
            · rw [← e]; exact hpz
            · exact h.trans hpz
          exact absurd (hmax _ hz hτz (hzy.trans_lt hyx)) (not_le.2 hpz)
        · have hpp : rdFk (k + 1) p = p := by rw [hpz]; exact hz
          have hcp : c = p := (rdFk_normal (k + 1)).strictMono.injective (hc.trans hpp.symm)
          have hd0 : d = 0 := by
            have : c + d = c + 0 := by rw [add_zero, ← hpz, hcp]
            exact add_left_cancel this
          rw [hd0, add_zero] at hle
          exact absurd hle (not_le.2 (rdFk_SC _ _).1)
      have hDx : D < x := (Ordinal.sub_le_self y c).trans_lt hyx
      obtain ⟨-, hψ⟩ := rdk_eq hF hownp hdvdp (hc.trans hBp.symm) D (hDx.trans hx1) hcond
      have hψx : S.psi (Bp + u * D) (Om 1) = x := by rw [hψ, hcD, hy]
      have hBpB : Bp < B := by
        have h := compare_psi Low.InR_Om_one hownp hown
        rw [hBp, compare_lt_iff_lt.2 hpx] at h
        exact compare_lt_iff_lt.1 h.symm
      have hlt2 : Bp + u * D < B :=
        rd_add_lt_of_dvd (rdU_indec _) hB hBpB
          (by rw [rdU_succ (k + 1)]; exact (mul_lt_mul_iff_right₀ hupos).2 (hDx.trans hx1))
      have hmem : Bp + u * D ∈ S.CSet B x :=
        CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one hBpB.le).2 hownp) (rdU_mul_mem (k + 1) hDx)
      have hψmem : S.psi (Bp + u * D) (Om 1) ∈ S.CSet B x :=
        CSet.psi_mem hlt2 Low.InR_Om_one (mem_CSet_psi Low.InR_Om_one B) hmem
      have := lt_psi_of_mem Low.InR_Om_one hψmem (psi_lt Low.InR_Om_one _)
      rw [hψx] at this
      exact lt_irrefl _ this
    · -- the converse
      intro B hown hfix
      have h0 := rd_Om1_ne
      set p := S.psi B (Om 1) with hpdef
      have hpSC : SC p := SC_psi Low.InR_Om_one B
      obtain ⟨m, hm⟩ := hC B hown (rdFk_fix_mono (Nat.le_succ k) hfix)
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
          (∀ j : ℕ, e / Le.leOe (j : Ordinal.{0}) % Om 1 < p) → S.psi e (Om 1) < p :=
        fun e he heC _ => lt_psi_of_mem Low.InR_Om_one
          (CSet.psi_mem he Low.InR_Om_one (mem_CSet_psi Low.InR_Om_one B) heC) (psi_lt Low.InR_Om_one _)
      have hdig := rdk_digits (S := S) hpSC hcoll B hown (k + 1)
      have hmdiv : B / u = m := by rw [hm, Ordinal.mul_div_cancel _ (rdU_ne _)]
      rw [hmdiv] at hdig
      have hD0p : D0 < p := hdig
      have hlt' : u * D0 < u2 := by rw [hu2]; exact (mul_lt_mul_iff_right₀ hupos).2 hD0lt
      have hBdiv : B / u2 = m / Om 1 := by
        calc B / u2 = (u2 * (m / Om 1) + u * D0) / u2 := by rw [← hB0, hBe]
          _ = m / Om 1 := by
            rw [Ordinal.mul_add_div _ (rdU_ne (k + 1 + 1)), Ordinal.div_eq_zero_of_lt hlt', add_zero]
      have hB0m : B0 ∈ S.CSet B p := by
        have := rdk_mod_mem (S := S) (m := k + 1 + 1) (by omega) B hown
        rwa [hBdiv] at this
      have hB0B : B0 < B := by
        rw [← hBe]; exact lt_add_of_pos_right _ (mul_pos hupos (pos_iff_ne_zero.2 hD00))
      have hB0p : S.psi B0 (Om 1) < p := psi_lt_psi_of_mem Low.InR_Om_one hB0B hB0m
      have hle := rdk_UB (S := S) (k + 1) B0 (S.psi B0 (Om 1)) D0
        (by rw [hB0]; exact huu2.trans (dvd_mul_right _ _)) (rdFk_le_self _ _) hD0lt.le
      rw [hBe] at hle
      have hlt : S.psi B0 (Om 1) + D0 < p := (lq_SC_indec hpSC).add_lt hB0p hD0p
      have h2 : rdFk (k + 1) (S.psi B0 (Om 1) + D0) < p := by
        conv_rhs => rw [← hfix]
        exact (rdFk_lt (k + 1)).2 hlt
      exact absurd (hle.trans_lt h2) (lt_irrefl _)

/-- **`ψ_{Ω₁}(B)` is a fixed point of `F_k`** for every own `B ≠ 0` with `u_{k+1} ∣ B`. -/
theorem rdk_fwd (k : ℕ) {B : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om 1)))
    (hB : Le.leOe ((k + 1 : ℕ) : Ordinal.{0}) ∣ B) (hB0 : B ≠ 0) : rdFk k (S.psi B (Om 1)) = S.psi B (Om 1) :=
  (rdk_fwd_conv k).1 B hown hB hB0

/-- **`u_{k+1} ∣ B`** for every own `B` with `ψ_{Ω₁}(B)` a fixed point of `F_k`. -/
theorem rdk_conv (k : ℕ) {B : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om 1)))
    (hfix : rdFk k (S.psi B (Om 1)) = S.psi B (Om 1)) : Le.leOe ((k + 1 : ℕ) : Ordinal.{0}) ∣ B :=
  (rdk_fwd_conv k).2 B hown hfix

/-! ## `B_n` and `σ` at level `k` -/

theorem rdk_nat_lt_Om1 (k : ℕ) : (k : Ordinal.{0}) < Om 1 :=
  (natCast_lt_omega0 k).trans_le (omega0_le_of_isSuccLimit (Om_isSuccLimit one_ne_zero))

theorem rdk_nat_lt_C (k n : ℕ) : (k : Ordinal.{0}) < Bc.bcC S n :=
  (natCast_lt_omega0 k).trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _))

/-- `u_k` is in the domain of `B_n` and fixed by it. -/
theorem rdkB_u (k : ℕ) {n : ℕ} : Mv.MvD S (Le.leOe (k : Ordinal.{0})) ∧
    Bc.bcB S n (Le.leOe (k : Ordinal.{0})) = Le.leOe (k : Ordinal.{0}) := by
  obtain ⟨hD, hB⟩ := Le.leB_Oe1 (S := S) (n := n) (rdk_nat_lt_Om1 k) (rdk_nat_lt_C k (n + 1))
  rw [Mw.mwB_nat] at hB
  exact ⟨hD, hB⟩

/-- **`B_n(ψ_{Ω₁}(B + u_k·D)) = ψ_{Ω₁}(B' + u_k·B_n D)`** (`k ≥ 1`) for an own `B` in the window and an own
`B + u_k·D` with a countable `D < L(n+2)`, with `B = α_{n+1} + |r|`, `B' = α_ω + |σ r|` own and
`B_n(ψ_{Ω₁}(B)) = ψ_{Ω₁}(B')`. -/
theorem rdkB_psi {n k : ℕ} (hk : 1 ≤ k) {B D : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om 1)))
    (hlo : Bc.bcC S n ≤ S.psi B (Om 1))
    (hown1 : B + Le.leOe (k : Ordinal.{0}) * D ∈
      S.CSet (B + Le.leOe (k : Ordinal.{0}) * D) (S.psi (B + Le.leOe (k : Ordinal.{0}) * D) (Om 1)))
    (hhi : S.psi (B + Le.leOe (k : Ordinal.{0}) * D) (Om 1) < Bc.bcC S (n + 1)) (hD1 : D < Om 1)
    (hDc : D < Bc.bcC S (n + 1)) :
    ∃ r : Term, bcD S r ∧ B = bcAlpha S (n + 1) + val S r ∧
      bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) ∈
        S.CSet (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r))
          (S.psi (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r)) (Om 1)) ∧
      Bc.bcB S n (S.psi B (Om 1)) = S.psi (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r)) (Om 1) ∧
      Bc.bcB S n (S.psi (B + Le.leOe (k : Ordinal.{0}) * D) (Om 1)) =
        S.psi (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) + Le.leOe (k : Ordinal.{0}) *
          Bc.bcB S n D) (Om 1) := by
  obtain ⟨hDm, hBm⟩ := Le.leB_Oe (S := S) (n := n) (rdk_nat_lt_Om1 k) (rdk_nat_lt_C k (n + 1))
    (by exact_mod_cast hk) hD1 hDc
  rw [Mw.mwB_nat] at hBm
  obtain ⟨r, h1, h2, h3, h4, h5⟩ := rdB_psi_baseD hown hlo hown1 hhi hDm
  exact ⟨r, h1, h2, h3, h4, by rw [h5, hBm]⟩

/-- **`σ` keeps `u_k ≤ |v|`** on its domain. -/
theorem rdk_u_le_sig {n k : ℕ} {v : Term} (hv : bcD S v) (h : Le.leOe (k : Ordinal.{0}) ≤ val S v) :
    Le.leOe (k : Ordinal.{0}) ≤ val S (bcSig (bcPre (n + 1)) bcPreW v) := by
  obtain ⟨hDu, hBu⟩ := rdkB_u (S := S) k (n := n)
  have hDv := Mv.mvD_of_term hv
  rw [← Mv.mvB_term (k := n) hv, ← hBu]
  exact not_lt.1 fun hlt => absurd ((Mv.mvB_lt_iff hDv hDu).1 hlt) (not_lt.2 h)

/-- **`σ` keeps `u_k ∣ |r|`** on its domain. -/
theorem rdk_dvd_sig {n k : ℕ} {r : Term} (hr : bcD S r) (h : Le.leOe (k : Ordinal.{0}) ∣ val S r) :
    Le.leOe (k : Ordinal.{0}) ∣ val S (bcSig (bcPre (n + 1)) bcPreW r) := by
  by_cases h0 : r = Term.zero
  · subst h0; rw [bcSig_zero]; exact dvd_zero _
  have hN' := bc_NF (k := n) hr
  have h0' : bcSig (bcPre (n + 1)) bcPreW r ≠ Term.zero := bcSig_ne_zero h0
  rw [rd_dvd_iff_last (rdU_indec k) hN' h0', rbLast_sig]
  exact rdk_u_le_sig (rbLast_D hr) ((rd_dvd_iff_last (rdU_indec k) hr.1 h0).1 h)

/-- An `ε`-number above `Ω₁` is a multiple of every `u_k`. -/
theorem rdk_dvd_eps (k : ℕ) {p : Ordinal.{0}} (hp : ω ^ p = p) (h : Om 1 < p) : Le.leOe (k : Ordinal.{0}) ∣ p := by
  have hI : Indec p := inE_indec hp
  have hk : Om 1 * (k : Ordinal.{0}) < p := by
    induction k with
    | zero => rw [Nat.cast_zero, mul_zero]; exact hI.pos
    | succ k ih => rw [Nat.cast_succ, mul_add_one]; exact hI.add_lt ih h
  refine rdk_dvd_of_indec k hI ?_
  unfold Le.leOe
  rw [← hp]
  exact opow_le_opow_right omega0_pos hk.le

theorem rdk_dvd_OmW (k : ℕ) : Le.leOe (k : Ordinal.{0}) ∣ Om (ω : Ordinal.{0}) :=
  rdk_dvd_eps k (Low.opow_eq_self_of_SC (SC_Om omega0_pos.ne')) (Om_lt_Om.2 one_lt_omega0)

theorem rdk_dvd_Pp (k : ℕ) : Le.leOe (k : Ordinal.{0}) ∣ Nc.ncPp S :=
  rdk_dvd_eps k (Low.opow_eq_self_of_SC (Nc.ncPp_SC S)) rb_Om1_lt_Pp

theorem rdk_dvd_alpha (k j : ℕ) : Le.leOe (k : Ordinal.{0}) ∣ bcAlpha S j :=
  dvd_add (dvd_add (rdk_dvd_OmW k) (rdk_dvd_OmW k)) (dvd_mul_of_dvd_left (rdk_dvd_Pp k) _)

theorem rdk_dvd_alphaW (k : ℕ) : Le.leOe (k : Ordinal.{0}) ∣ bcAlphaW S := by
  refine dvd_add (dvd_add (rdk_dvd_OmW k) (rdk_dvd_OmW k)) ?_
  have hE : ω ^ Nc.ncPp S = Nc.ncPp S := Low.opow_eq_self_of_SC (Nc.ncPp_SC S)
  have h1 := rdk_dvd_Pp (S := S) k
  have hI : Indec (ω ^ (Nc.ncPp S + 1)) :=
    indec_iff.2 ⟨(opow_pos _ omega0_pos).ne', isPrincipal_add_omega0_opow _⟩
  refine rdk_dvd_of_indec k hI ((Ordinal.le_of_dvd (inE_indec hE).ne_zero h1).trans ?_)
  conv_lhs => rw [← hE]
  exact opow_le_opow_right omega0_pos le_self_add

/-- **`u_k ∣ B` gives `u_k ∣ B'`** for `B = α_{n+1} + |r|`, `B' = α_ω + |σ r|`. -/
theorem rdkB_dvd {n k : ℕ} {B : Ordinal.{0}} {r : Term} (hr : bcD S r) (hB : B = bcAlpha S (n + 1) + val S r)
    (h : Le.leOe (k : Ordinal.{0}) ∣ B) :
    Le.leOe (k : Ordinal.{0}) ∣ bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) := by
  rw [hB, rd_dvd_add_left (rdk_dvd_alpha k _)] at h
  rw [rd_dvd_add_left (rdk_dvd_alphaW k)]
  exact rdk_dvd_sig hr h

/-- **`u_k ∣ A_η`.** -/
theorem rdk_dvd_A (k : ℕ) (η : Ordinal.{0}) : Le.leOe (k : Ordinal.{0}) ∣ ConjT.Aη S η := by
  have h2 : Le.leOe (k : Ordinal.{0}) ∣ ConjT.th S :=
    rdk_dvd_eps k (Low.opow_eq_self_of_SC (ConjT.SC_th S)) Bt.Om1_lt_th
  exact dvd_add (rdk_dvd_OmW k) (h2.mul_right η)

/-- **The `υ`-point `ψ_{Ω₁}(A_η)` is a fixed point of every `F_k`** (`A_η` own, `A_η ≠ 0`). -/
theorem rdk_fix_A (k : ℕ) {η : Ordinal.{0}} (hown : ConjT.Aη S η ∈ S.CSet (ConjT.Aη S η) (S.psi (ConjT.Aη S η) (Om 1)))
    : rdFk k (S.psi (ConjT.Aη S η) (Om 1)) = S.psi (ConjT.Aη S η) (Om 1) := by
  refine rdk_fwd k hown (rdk_dvd_A (k + 1) η) ?_
  unfold ConjT.Aη; exact (lt_of_lt_of_le (SC_Om omega0_pos.ne').1 le_self_add).ne'

end Googology.Trans.PoR.InaccPsi.R2.Rd

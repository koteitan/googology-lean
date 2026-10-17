import Googology.Trans.PoR.InaccPsi.R2.CpRel
import Googology.Trans.PoR.InaccPsi.R2.XtChain

/-!
# The limit of a sequence of layers: the terms of all `L.iter n`, top `T(x)·x^ω`

For a layer `L` (`R2.XtLay`) with top `T`, `L.iter n` is the `n`-th next layer (top `T(x)·x^n`, `iter_top`).  The
**limit layer** `L.xtLim` has as terms the terms of every `L.iter n` (a sigma type), the same values, and the top
`T(x)·x^ω = ω^{E(x)+x·ω}`:

* the representation below `T(ρ)·ρ^ω` (every value lies below some `T(ρ)·ρ^n`), the comparison from Lemma EXACT
  (`xt_uni_of_exact`), IMG and RS from the layers;
* **EXACT for the exponent**: `π(E(ρ) + ρ·ω) = E(σ) + σ·ω` (`ρ·ω = ω^{ρ+1}`, `pi_opowZ`);
* **the witness pair of the new top**: the atom `p ≤₁ p + (ρ+1)` of `R₁⁺` for `p = T(ρ)·ρ^ω` ([W07b] Theorem 2.2:
  `ω^{ρ+1} ∣ E(ρ) + ρ·ω`) is kept by the copy, so `f(p) = ω^a` with `ω^{f(ρ)+1} ∣ a` and `a > e'`
  (`f(T(ρ)) = ω^{e'}`), hence `a ≥ e' + ω^{f(ρ)+1}` (`xt_dvd_next'`) and `f(p) ≥ f(T(ρ))·f(ρ)^ω`.

The chain (`R2.XtChain`) for `L.iter n`: `Λ⁺_n(L) = xtB1 (L.iter n).sys`, `xtLimW L = sup_n Λ⁺_n(L)`; and:

* `lim_gt` (**`Λ⁺_n(L) < Λ(L.xtLim)`** for every `n`, so `xtLimW L ≤ Λ(L.xtLim)`), `lim_eq` (`O_lim = O_n` below
  `Λ⁺_n(L)`), `lim_W_le`.

No new axiom beyond `R2.CitedXt`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Xt

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2

/-- `ω^k ∣ a` and `b < a` give `b + ω^k ≤ a` (no divisibility of `b` needed). -/
theorem xt_dvd_next' {k a b : Ordinal.{0}} (ha : ω ^ k ∣ a) (hba : b < a) : b + ω ^ k ≤ a := by
  obtain ⟨a', rfl⟩ := ha
  have hp : 0 < ω ^ k := opow_pos k omega0_pos
  rw [Cp.cpAdd_opow]
  refine mul_le_mul_right (Order.add_one_le_of_lt ?_) _
  rcases lt_or_ge (b / ω ^ k) a' with h | h
  · exact h
  · exact absurd ((mul_le_mul_right h _).trans (Ordinal.mul_div_le b _)) (not_le.2 hba)

/-- `x^ω < u` for `ε`-numbers `x < u`. -/
theorem xt_pow_omega_lt {x u : Ordinal.{0}} (hx : InE x) (hu : InE u) (hxu : x < u) : x ^ ω < u := by
  have hxr : ω ^ x = x := hx
  have hur : ω ^ u = u := hu
  rw [← hxr, ← opow_mul]
  conv_rhs => rw [← hur]
  exact (opow_lt_opow_iff_right one_lt_omega0).2 (hu.mul_lt hxu (omega0_lt_inE hu))

theorem xt_one_lt_E {x : Ordinal.{0}} (hx : InE x) : 1 < x := one_lt_omega0.trans (omega0_lt_inE hx)

/-- **The comparison of two values from Lemma EXACT.** -/
theorem xt_uni_of_exact {σ ρ a b a' b' : Ordinal.{0}} (hB : Bases σ ρ) (ha : a ∈ TB ρ σ ∧ pi σ ρ a = a')
    (hb : b ∈ TB ρ σ ∧ pi σ ρ b = b') : a ≤ b ↔ a' ≤ b' := by
  rw [← ha.2, ← hb.2]
  exact ((pi_bijOn hB).2.le_iff_le ha.1 hb.1).symm

namespace XtLay

variable (L : XtLay)

/-- The `n`-th next layer. -/
noncomputable def iter : ℕ → XtLay
  | 0 => L
  | n + 1 => (iter n).xtNext

theorem iter_top (n : ℕ) (x : Ordinal.{0}) :
    (L.iter n).sys.top x = L.sys.top x * x ^ (n : Ordinal.{0}) := by
  induction n with
  | zero => show L.sys.top x = _; rw [Nat.cast_zero, opow_zero, mul_one]
  | succ n ih =>
    show (L.iter n).sys.top x * x = _
    rw [ih, Nat.cast_succ, ← succ_eq_add_one, opow_succ, mul_assoc]

/-- The values of the limit layer. -/
noncomputable def limVal (p : Σ n : ℕ, (L.iter n).sys.Tm) (x : Ordinal.{0}) : Ordinal.{0} :=
  (L.iter p.1).sys.val p.2 x

theorem iter_lt_lim {n : ℕ} {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    (L.iter n).sys.top x < L.sys.top x * x ^ ω := by
  rw [iter_top]
  exact (mul_lt_mul_iff_right₀ (hx.pos.trans (L.top_gt x hx hx1))).2
    ((opow_lt_opow_iff_right (xt_one_lt_E hx)).2 (natCast_lt_omega0 n))

theorem lim_lt_top_E {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (p : Σ n : ℕ, (L.iter n).sys.Tm)
    (h : (L.iter p.1).sys.CB p.2 x) : L.limVal p x < L.sys.top x * x ^ ω :=
  ((L.iter p.1).lt_top_E x hx hx1 p.2 h).trans (L.iter_lt_lim hx hx1)

theorem lim_top_lt_ups {x u : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hxu : x < u) (hu : UpsPt u) :
    L.sys.top x * x ^ ω < u :=
  (upsPt_inE hu).mul_lt (L.top_lt_ups x u hx hx1 hxu hu) (xt_pow_omega_lt hx (upsPt_inE hu) hxu)

/-- **The term system of the limit layer.** -/
noncomputable def limSys : XtSys where
  Tm := Σ n : ℕ, (L.iter n).sys.Tm
  val := L.limVal
  CB := fun p x => (L.iter p.1).sys.CB p.2 x
  cs := fun p => (L.iter p.1).sys.cs p.2
  cst := fun c => ⟨0, L.sys.cst c⟩
  top := fun x => L.sys.top x * x ^ ω
  cb_cst := fun p s h => (L.iter p.1).sys.cb_cst p.2 s h
  cb_iff := fun p s s' h h' => (L.iter p.1).sys.cb_iff p.2 s s' h h'
  val_cst := fun c x => L.sys.val_cst c x
  cb_cstI := fun c x h => L.sys.cb_cstI c x h
  lt_top := fun l hl hl1 p h => L.lim_lt_top_E (ups_inE hl) (ups_lt_Om1 l hl1) p h
  one_le_top := fun l hl hl1 => by
    have hρE := ups_inE hl
    have hρ1 := ups_lt_Om1 l hl1
    exact (one_le_iff_pos.2 hρE.pos).trans ((L.top_gt _ hρE hρ1).le.trans
      (le_mul_left _ (opow_pos _ hρE.pos)))
  rep := fun l hl hl1 v hv => by
    have hρE := ups_inE hl
    have hρ1 := ups_lt_Om1 l hl1
    have hT0 : L.sys.top (upsilon l) ≠ 0 := (hρE.pos.trans (L.top_gt _ hρE hρ1)).ne'
    have hq : v / L.sys.top (upsilon l) < upsilon l ^ ω := (Ordinal.lt_mul_iff_div_lt hT0).1 hv
    obtain ⟨c, hc, hqc⟩ := (lt_opow_of_isSuccLimit hρE.pos.ne' isSuccLimit_omega0).1 hq
    obtain ⟨n, rfl⟩ := lt_omega0.1 hc
    have hvn : v < (L.iter n).sys.top (upsilon l) := by
      rw [iter_top]
      calc v = L.sys.top (upsilon l) * (v / L.sys.top (upsilon l)) + v % L.sys.top (upsilon l) :=
            (div_add_mod v _).symm
        _ < L.sys.top (upsilon l) * (v / L.sys.top (upsilon l)) + L.sys.top (upsilon l) :=
            (add_lt_add_iff_left _).2 (mod_lt v hT0)
        _ = L.sys.top (upsilon l) * (v / L.sys.top (upsilon l) + 1) := (mul_add_one _ _).symm
        _ ≤ L.sys.top (upsilon l) * upsilon l ^ (n : Ordinal.{0}) :=
            mul_le_mul_right (Order.add_one_le_of_lt hqc) _
    obtain ⟨t, ht, et⟩ := (L.iter n).sys.rep l hl hl1 v hvn
    exact ⟨⟨n, t⟩, ht, et⟩
  top_lt := fun l hl hl1 => by
    have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
    have h1 : l < l + ω := lt_add_of_pos_right l omega0_pos
    exact (L.lim_top_lt_ups (ups_inE hl) (ups_lt_Om1 l hl1) (upsilon_normal.strictMono h1)
      (upsPt_upsilon (hl0.trans h1))).trans (upsilon_normal.strictMono (lt_add_one _))
  pkg := fun l hl hl1 p h h1 R => (L.iter p.1).sys.pkg l hl hl1 p.2 h h1 R
  rs := fun l hl hl1 p h => (L.iter p.1).sys.rs l hl hl1 p.2 h
  uni_le := fun σ ρ hσ hρ hB p q hp hq =>
    xt_uni_of_exact hB ((L.iter p.1).exact σ ρ hσ hρ hB p.2 hp) ((L.iter q.1).exact σ ρ hσ hρ hB q.2 hq)
  small := fun p => (L.iter p.1).sys.small p.2

/-- **The witness pair of the limit top `T(ρ)·ρ^ω`.** -/
theorem lim_top_wit {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ) :
    ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ L.sys.top ρ * ρ ^ ω ∈ W ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
        (∃ e', f (L.sys.top ρ * ρ ^ ω) = ω ^ e' ∧ ω ^ f ρ ∣ e') ∧
          L.sys.top (f ρ) * f ρ ^ ω ≤ f (L.sys.top ρ * ρ ^ ω) := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hδE := h.δE
  have hδI := inE_indec hδE
  have hρδ := h.ρδ
  have hρr : ω ^ ρ = ρ := hρE
  have h1ρ : (1 : Ordinal.{0}) < ρ := one_lt_of_upsPt h.ρU
  obtain ⟨Wt, Zt, hwt, htW, hIt⟩ := L.top_wit ρ τ δ h
  set T := L.sys.top ρ with hT
  have hTe : T = ω ^ L.E ρ := L.top_eq ρ hρE hρ1
  have hρT : ρ < T := L.top_gt ρ hρE hρ1
  have hTδ : T < δ := L.top_lt_ups ρ δ hρE hρ1 hρδ h.next.2.1
  have hρw : ρ ^ ω = ω ^ (ρ * ω) := by rw [opow_mul, hρr]
  have hρω1 : ρ * ω = ω ^ (ρ + 1) := by rw [opow_add, opow_one, hρr]
  set p := T * ρ ^ ω with hp
  have hpe : p = ω ^ (L.E ρ + ρ * ω) := by rw [hp, hTe, hρw, ← opow_add]
  have hpδ : p < δ := hδE.mul_lt hTδ (xt_pow_omega_lt hρE hδE hρδ)
  have h1w : (1 : Ordinal.{0}) < ρ ^ ω := by
    have := (opow_lt_opow_iff_right h1ρ).2 omega0_pos; rwa [opow_zero] at this
  have hTp : T < p := lt_mul_of_one_lt_right (hρE.pos.trans hρT) h1w
  have hρp : ρ < p := hρT.trans hTp
  have hρ1δ : ρ + 1 < δ := hδI.add_lt hρδ (one_lt_omega0.trans (omega0_lt_inE hδE))
  have hpI : Indec p := by rw [hpe]; exact indec_opow _
  have hρ1p : ρ + 1 < p := hpI.add_lt hρp (h1ρ.trans hρp)
  have hpq : p + (ρ + 1) < δ := hδI.add_lt hpδ hρ1δ
  have hq0 : (0 : Ordinal.{0}) < ρ + 1 := lt_of_le_of_lt zero_le (lt_add_one ρ)
  have hw : WZ ρ δ (insert (p + (ρ + 1)) (insert p (insert (ρ + 1) (insert ρ Wt)))) (insert 1 Zt) := by
    have w0 := (hwt.insZ h1ρ).insW le_rfl hρδ (Or.inl (inE_indec hρE))
    have w1 := w0.insW le_self_add hρ1δ
      (Or.inr ⟨ρ, by simp, 1, by simp, lt_add_one ρ, h1ρ.trans (lt_add_one ρ), rfl⟩)
    have w2 := w1.insW hρp.le hpδ (Or.inl hpI)
    exact w2.insW (hρp.le.trans le_self_add) hpq
      (Or.inr ⟨p, by simp, ρ + 1, by simp, lt_add_of_pos_right _ hq0, hρ1p.trans_le le_self_add, rfl⟩)
  refine ⟨_, _, hw, by simp, fun A f hW hZ C => ?_⟩
  have hpA : p ∈ A := hW (by simp)
  have hpqA : p + (ρ + 1) ∈ A := hW (by simp)
  have hq1A : ρ + 1 ∈ A := hW (by simp)
  have h1A : (1 : Ordinal.{0}) ∈ A := hZ (by simp)
  have hTA : T ∈ A := hW (by simp [htW])
  have hρA : ρ ∈ A := C.rho
  obtain ⟨⟨e', hfe', -⟩, hle⟩ := hIt A f (fun x hx => hW (by simp [Finset.mem_coe.1 hx]))
    (fun x hx => hZ (by simp [Finset.mem_coe.1 hx])) C
  have hfρE : InE (f ρ) := upsPt_inE C.ups
  have hfρr : ω ^ f ρ = f ρ := hfρE
  have hf1 : f 1 = 1 := C.fix 1 h1A h1ρ
  have hfq : f (ρ + 1) = f ρ + 1 := by
    have := C.add ρ hρA 1 h1A (ρ + 1) hq1A rfl
    rw [hf1] at this; exact this.symm
  have hfTp : f T < f p := C.mono hTA hpA hTp
  have hfρT : f ρ ≤ f T := C.mono.monotoneOn hρA hTA hρT.le
  have hfρp : f ρ < f p := hfρT.trans_lt hfTp
  have hsrc : le1 p (p + (ρ + 1)) := by
    have hne : L.E ρ + ρ * ω ≠ 0 := by
      rw [hρω1]; exact (lt_of_lt_of_le (opow_pos _ omega0_pos) le_add_self).ne'
    refine (h.lowδ _ _ hρp hpq.le).2 ?_
    refine (le1R_thm22 hq0 hρ1p.le).2 ⟨L.E ρ + ρ * ω, hne, hpe, ?_⟩
    refine (le_lg_iff hne (ρ + 1)).2 ?_
    rw [hρω1, Cp.cpAdd_opow]; exact dvd_mul_right _ _
  have himg : le1 (f p) (f p + (f ρ + 1)) := by
    have := C.cov1 _ hpA _ hpqA hsrc
    rwa [← C.add _ hpA _ hq1A _ hpqA rfl, hfq] at this
  have e1 : f ρ * ω = ω ^ (f ρ + 1) := by rw [opow_add, opow_one, hfρr]
  have hfw : f T * f ρ ^ ω = ω ^ (e' + ω ^ (f ρ + 1)) :=
    calc f T * f ρ ^ ω = ω ^ e' * (ω ^ f ρ) ^ ω := by rw [hfe', hfρr]
      _ = ω ^ e' * ω ^ (f ρ * ω) := by rw [opow_mul]
      _ = ω ^ e' * ω ^ (ω ^ (f ρ + 1)) := by rw [e1]
      _ = ω ^ (e' + ω ^ (f ρ + 1)) := (opow_add _ _ _).symm
  have key : (∃ a, f p = ω ^ a ∧ ω ^ f ρ ∣ a) ∧ f T * f ρ ^ ω ≤ f p := by
    by_cases hU : UpsPt (f p)
    · have hE := upsPt_inE hU
      exact ⟨⟨f p, hE.symm, opow_dvd_of_inE hE hfρp.le⟩,
        (hE.mul_lt hfTp (xt_pow_omega_lt hfρE hE hfρp)).le⟩
    · have hR := (C.sk _ (C.low _ hpA) hU _).1 himg
      have hq0' : 0 < f ρ + 1 := lt_of_le_of_lt zero_le (lt_add_one _)
      obtain ⟨a, ha0, hfa, hza⟩ := (le1R_thm22 hq0' (Order.add_one_le_of_lt hfρp)).1 hR
      have hdiv : ω ^ (f ρ + 1) ∣ a := (le_lg_iff ha0 _).1 hza
      have h3 : e' < a := by
        have := hfTp; rw [hfa, hfe'] at this
        exact (opow_lt_opow_iff_right one_lt_omega0).1 this
      refine ⟨⟨a, hfa, (opow_dvd_opow ω le_self_add).trans hdiv⟩, ?_⟩
      rw [hfw, hfa]
      exact opow_le_opow_right omega0_pos (xt_dvd_next' hdiv h3)
  exact ⟨key.1, (mul_le_mul_left hle _).trans key.2⟩

/-- **The limit layer**: the terms of every `L.iter n`, top `T(x)·x^ω = ω^{E(x)+x·ω}`. -/
noncomputable def xtLim : XtLay where
  sys := L.limSys
  E := fun x => L.E x + x * ω
  top_eq := fun x hx hx1 => by
    show L.sys.top x * x ^ ω = ω ^ (L.E x + x * ω)
    rw [L.top_eq x hx hx1, opow_add, opow_mul, show ω ^ x = x from hx]
  exp_dvd := fun x hx _ => dvd_add (L.exp_dvd x hx ‹_›) ⟨ω, by rw [show ω ^ x = x from hx]⟩
  exp_lt := fun x hx hx1 => Om1_add_lt (L.exp_lt x hx hx1) (Om1_mul_lt hx1 omega0_lt_omega_one)
  top_gt := fun x hx hx1 => (L.top_gt x hx hx1).trans_le (le_mul_left _ (opow_pos _ hx.pos))
  top_lt_ups := fun _ _ hx hx1 hxu hu => L.lim_top_lt_ups hx hx1 hxu hu
  lt_top_E := fun _ hx hx1 p hp => L.lim_lt_top_E hx hx1 p hp
  exact := fun σ ρ hσ hρ hB p hp => (L.iter p.1).exact σ ρ hσ hρ hB p.2 hp
  exp_pi := fun σ ρ hσ hρ hB => by
    show L.E ρ + ρ * ω ∈ TB ρ σ ∧ pi σ ρ (L.E ρ + ρ * ω) = L.E σ + σ * ω
    obtain ⟨h1, h2⟩ := L.exp_pi σ ρ hσ hρ hB
    obtain ⟨h3, h4⟩ := pi_base hB
    have h1σ : (1 : Ordinal.{0}) < σ := xt_one_lt_E hB.1
    obtain ⟨h5, h6⟩ := pi_add hB h3 (mem_TB_of_lt hB h1σ)
    rw [h4, pi_lt hB h1σ] at h6
    have hρ11 : ρ + 1 < Om1 := Om1_add_lt hB.2.2.2 (one_lt_omega0.trans omega0_lt_omega_one)
    obtain ⟨h7, h8⟩ := pi_opowZ hσ hρ hB h5 hρ11
    rw [h6] at h8
    have eρ : ρ * ω = ω ^ (ρ + 1) := by rw [opow_add, opow_one, show ω ^ ρ = ρ from hB.2.1]
    have eσ : σ * ω = ω ^ (σ + 1) := by rw [opow_add, opow_one, show ω ^ σ = σ from hB.1]
    rw [eρ, eσ]
    obtain ⟨h9, h10⟩ := pi_add hB h1 h7
    exact ⟨h9, by rw [h10, h2, h8]⟩
  top_wit := fun _ _ _ h => L.lim_top_wit h

/-! ## The limit layer above the chain of `L.iter n` -/

/-- The term `T_n(x)` (the top of `L.iter n`) in the limit layer. -/
noncomputable def limT (n : ℕ) : L.xtLim.sys.Tm := ⟨n + 1, (L.iter n).xtTTop⟩

theorem val_limT (n : ℕ) (x : Ordinal.{0}) : L.xtLim.sys.val (L.limT n) x = (L.iter n).sys.top x :=
  (L.iter n).val_xtTTop x

theorem cb_limT (n : ℕ) {x : Ordinal.{0}} (hx : UpsPt x) : L.xtLim.sys.CB (L.limT n) x :=
  (L.iter n).cb_xtTTop hx

theorem lim_le_succ (n : ℕ) {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1)
    (hbd : ∀ μ, IsRestartIdx μ → μ < l → xtOrec L.xtLim.sys μ ≤ (L.iter n).sys.top (upsilon μ)) :
    xtOrec L.xtLim.sys l ≤ (L.iter n).sys.top (upsilon l) + 1 := by
  refine xtOrec_le_of le_add_self (fun s hCB hc => ?_)
  obtain ⟨μ, hμ, -, hμl, hCBμ, hsμ⟩ := hc 0 (pos_iff_ne_zero.2 hl.1)
  have h1 : L.xtLim.sys.val s (upsilon μ) ≤ L.xtLim.sys.val (L.limT n) (upsilon μ) := by
    rw [val_limT]; exact hsμ.trans (hbd μ hμ hμl)
  have h2 := (L.xtLim.sys.uni_le _ _ (ups_ri hμ) (ups_ri hl) (bases_ri hμ hl hμl hl1) s (L.limT n) hCBμ
    (L.cb_limT n (ups_ri hμ))).2 h1
  rw [val_limT] at h2
  exact Order.lt_add_one_iff.2 h2

theorem lim_eq_min (n : ℕ) {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h1 : μ < xtB1 (L.iter n).sys)
    (h2 : μ < xtLam L.xtLim.sys) : xtOrec L.xtLim.sys μ = xtOrec (L.iter n).sys μ :=
  xt_off_eq xtSpecLam (xtSpec1 (L.iter n).topPkg) hμ h2 h1

/-- **`Λ⁺_n(L) < Λ(L.xtLim)`** for every `n`. -/
theorem lim_gt (n : ℕ) : xtB1 (L.iter n).sys < xtLam L.xtLim.sys := by
  by_contra hle
  push Not at hle
  have hL := xtLam_ri (X := L.xtLim.sys)
  have hL1 := xtLam_lt_Om1 (X := L.xtLim.sys)
  set Λ' := xtLam L.xtLim.sys with hΛ'
  have hbd : ∀ μ, IsRestartIdx μ → μ < Λ' → xtOrec L.xtLim.sys μ ≤ (L.iter n).sys.top (upsilon μ) :=
    fun μ hμ hμL => by
      rw [L.lim_eq_min n hμ (hμL.trans_le hle) hμL]
      exact xtOrec_le_top hμ (hμL.trans hL1)
  have h1 := L.lim_le_succ n hL hL1 hbd
  have h2 : xtOrec L.xtLim.sys Λ' = L.sys.top (upsilon Λ') * upsilon Λ' ^ ω := xtOrec_Lam
  have hρE := ups_inE hL
  have hρ1 := ups_lt_Om1 Λ' hL1
  set Tn := (L.iter n).sys.top (upsilon Λ') with hTn
  have hρT := (L.iter n).top_gt _ hρE hρ1
  have h1T : (1 : Ordinal.{0}) < Tn := (one_lt_of_upsPt (ups_ri hL)).trans hρT
  have h2ρ : (2 : Ordinal.{0}) ≤ upsilon Λ' := by
    have := Order.add_one_le_of_lt (one_lt_of_upsPt (ups_ri hL)); rwa [one_add_one_eq_two] at this
  have hnext : Tn * upsilon Λ' = (L.iter (n + 1)).sys.top (upsilon Λ') := rfl
  have h3 : Tn + 1 < L.sys.top (upsilon Λ') * upsilon Λ' ^ ω :=
    calc Tn + 1 < Tn + Tn := (add_lt_add_iff_left _).2 h1T
      _ = Tn * 2 := (Ordinal.mul_two _).symm
      _ ≤ Tn * upsilon Λ' := mul_le_mul_right h2ρ _
      _ = (L.iter (n + 1)).sys.top (upsilon Λ') := hnext
      _ < L.sys.top (upsilon Λ') * upsilon Λ' ^ ω := L.iter_lt_lim hρE hρ1
  rw [h2] at h1
  exact absurd h1 (not_le.2 h3)

/-- **`O_lim = O_n` below `Λ⁺_n(L)`.** -/
theorem lim_eq (n : ℕ) {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h1 : μ < xtB1 (L.iter n).sys) :
    xtOrec L.xtLim.sys μ = xtOrec (L.iter n).sys μ :=
  L.lim_eq_min n hμ h1 (h1.trans (L.lim_gt n))

end XtLay

end Googology.Trans.PoR.InaccPsi.R2.Xt

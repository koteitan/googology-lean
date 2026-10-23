import Googology.Trans.PoR.InaccPsi.R2.GeLad

/-!
# THE LIMIT STEP FOR TERM OFFSETS: the union of the layers of all smaller codes, gated at the code's gate

For a limit code `a < Ω₁^ω` (`R2.GeSub`) and a family of gated layers `K_b`, `b < a`, with tops
`ϑˣ(Ω₁·Ω₁ + 1 + sbc b x)` above `gate b`, the union of all `K_b` (the pair `(b, t)` with the side condition
`gate b < x`, which opens the gate of `K_b`) is a gated layer with top `ϑˣ(Ω₁·Ω₁ + sbc a x)` above `gate a`:

* `ge_lt_lim_iff` (**`v < ϑˣ(Ω₁·Ω₁ + λ)` iff `v < ϑˣ(Ω₁·Ω₁ + ν)` for some `ν < λ`**, every limit `λ < ε_{x+1}`),
  `ge_not_le1R_lim` (**no `ε`-number in `(ϑˣ(Ω₁·Ω₁ + λ'), ϑˣ(Ω₁·Ω₁ + λ))` is `≤₁ a·a + a + logend(λ)` in `R₁⁺`**,
  `λ = λ' + ω^{logend λ}`, `ω^{logend λ} ∣ λ'`);
* `ge_lin` (**the copy of a linear term**: `f(ρ·k + d) = fρ·k + d` for the copies, `d < ρ`);
* `GeLimF a`, `geUSys` (the union), `GeLK.geTopWit` (**THE TOP WITNESS for a term offset**: `logend(sbc a ρ) =
  ρ·k + d` is linear in the base, so the copy of `G ≤₁ G·G + G + ρ·k + d` is `f(G) ≤₁ f(G)·f(G) + f(G) + fρ·k + d`;
  with the witness of the predecessor layer `K_{a'}`, `a = a' + (last term)`, and `ge_not_le1R_lim`), `geLimL`,
  `geLimB`.

No new axiom.  New definitions: `GeLimF`, `geUSys`, `geLimL`, `geLimB`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ge

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Ly Lu
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The reaches of the tops and the separation, for term offsets -/

section GQL

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **`v < ϑˣ(Ω₁·Ω₁ + λ)` iff `v < ϑˣ(Ω₁·Ω₁ + ν)` for some `ν < λ`** (`λ` a limit below `x`). -/
theorem ge_lt_lim_iff {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlE : l < eN x) :
    ∀ v, v < gq l x → ∃ ν < l, v < gq ν x := by
  obtain ⟨hlT, hl1⟩ := eN_T hx hx1 hlE
  obtain ⟨hGT, -, hG1, -, -⟩ := geq_facts hx hx1 hlT hl1
  have h0T := mem_T_of_le hx hx1 (zero_le : (0 : Ordinal.{0}) ≤ x)
  have h01 : (0 : Ordinal.{0}) < Om1 := hx.pos.trans hx1
  have hG0 : l < gq 0 x := hlE.trans_le (geq_eN_le hx hx1 h0T h01)
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  rcases le_or_gt v (max x l) with hvx | hxv0
  · exact ⟨0, hl.bot_lt, hvx.trans_lt (max_lt (geq_facts hx hx1 h0T h01).2.1 hG0)⟩
  have hxv : x < v := (le_max_left _ _).trans_lt hxv0
  have hlv : l < v := (le_max_right _ _).trans_lt hxv0
  have hv1 : v < Om1 := hv.trans hG1
  have hvT : v ∈ Tset x := vz_T_down hx hx1 hGT hG1 hv.le
  by_cases hI : Indec v
  · by_cases hvE' : InE v
    · obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hx hx1 hvT hxv.le hv1 hI
      have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξv]; exact hxv, by rw [hξv]; exact hvE'⟩
      have hξk : ξ < Om1 * Om1 + l :=
        lgLt_of_vt_lt hx hx1 hξT hξ2 hlT hl1 (by rw [hξv]; exact hlv) (by rw [hξv]; exact hv)
      rcases lt_or_ge ξ (Om1 * Om1) with hξs | hξs
      · obtain ⟨hq1, hrT, hr1, hdec⟩ := lu_split hx hx1 hξT hξ2 hΩξ
        have hqT : ξ / Om1 ∈ Tset x := lgQuot_mem hx hx1 hξT hξs
        have hqΩ : ξ / Om1 < Om1 := (Ordinal.lt_mul_iff_div_lt (Ordinal.omega_pos 1).ne').1 hξs
        have hqr : ξ / Om1 < v ∧ ξ % Om1 < v := by
          rcases lt_or_ge (ξ / Om1) x with hqx | hxq
          · have h := luLt_vt_self hx hx1 hq1 hqx hrT hr1
            rw [hdec, hξv] at h
            exact ⟨hqx.trans hxv, h⟩
          · have h := lvLevel_lt_vt hx hx1 hqT hxq hqΩ hrT hr1
            rw [hdec, hξv] at h
            exact h
        obtain ⟨n1, hn1l, hn1⟩ := IH _ hqr.1 (hqr.1.trans hv)
        obtain ⟨n2, hn2l, hn2⟩ := IH _ hqr.2 (hqr.2.trans hv)
        have hml : max n1 n2 < l := max_lt hn1l hn2l
        refine ⟨max n1 n2, hml, ?_⟩
        have hq' : ξ / Om1 < gq (max n1 n2) x := hn1.trans_le (geq_mono hx hx1 (hml.trans hlE) (le_max_left _ _))
        have hr' : ξ % Om1 < gq (max n1 n2) x := hn2.trans_le (geq_mono hx hx1 (hml.trans hlE) (le_max_right _ _))
        obtain ⟨hmT, hm1⟩ := eN_T hx hx1 (hml.trans hlE)
        have h := lgVt_lt_low hx hx1 hqT hqΩ hrT hr1 hmT hm1 hq' hr'
        rw [hdec, hξv] at h
        exact h
      · have hje : Om1 * Om1 + (ξ - Om1 * Om1) = ξ := Ordinal.add_sub_cancel_of_le hξs
        obtain ⟨j, hj⟩ : ∃ j, ξ - Om1 * Om1 = j := ⟨_, rfl⟩
        rw [hj] at hje
        have hjk : j < l := (add_lt_add_iff_left _).1 (by rw [hje]; exact hξk)
        refine ⟨j + 1, hl.add_one_lt hjk, ?_⟩
        have hvj : v = gq j x := by rw [← hξv, ← hje]; rfl
        rw [hvj]
        exact geq_lt hx hx1 ((hl.add_one_lt hjk).trans hlE) (lt_add_one _)
    · obtain ⟨L, rfl⟩ := indec_eq_opow hI
      have hL : L < ω ^ L := lt_of_le_of_ne (right_le_opow _ one_lt_omega0)
        (fun h => hvE' (by unfold InE; rw [← h]; exact h.symm))
      obtain ⟨n, hnl, hn⟩ := IH L hL (hL.trans hv)
      exact ⟨n, hnl, (geq_facts hx hx1 (eN_T hx hx1 (hnl.trans hlE)).1 (eN_T hx hx1
          (hnl.trans hlE)).2).2.2.2.1.opow_lt hn⟩
  · have hD : DecompR0 v := not_not.1 hI
    rcases hD with h0 | ⟨u1, u2, hu1, hu2, hsum⟩
    · exact absurd h0 (lt_of_le_of_lt zero_le hxv).ne'
    obtain ⟨n1, hn1l, h1⟩ := IH u1 hu1 (hu1.trans hv)
    obtain ⟨n2, hn2l, h2⟩ := IH u2 hu2 (hu2.trans hv)
    have hml : max n1 n2 < l := max_lt hn1l hn2l
    refine ⟨max n1 n2, hml, ?_⟩
    rw [← hsum]
    exact (inE_indec (geq_facts hx hx1 (eN_T hx hx1 (hml.trans hlE)).1 (eN_T hx hx1 (hml.trans hlE)).2).2.2.2.1).add_lt
      (h1.trans_le (geq_mono hx hx1 (hml.trans hlE) (le_max_left _ _)))
      (h2.trans_le (geq_mono hx hx1 (hml.trans hlE) (le_max_right _ _)))

/-- **No `ε`-number `a ∈ (ϑˣ(Ω₁·Ω₁ + λ'), ϑˣ(Ω₁·Ω₁ + λ))` has `a ≤₁ a·a + a + e` in `R₁⁺`**, for a constant limit
`λ = λ' + ω^e`, `e = logend(λ)`, `ω^e ∣ λ'`. -/
theorem ge_not_le1R_lim {l l' : Ordinal.{0}} (hlE : l < eN x) (hdec : l = l' + ω ^ lg l) (hdvd : ω ^ lg l ∣ l')
    (hl'l : l' < l) {a : Ordinal.{0}} (haE : InE a) (h1 : gq l' x < a) (h2 : a < gq l x) :
    ¬ le1R a (a * a + a + lg l) := by
  intro hR
  obtain ⟨hlT, hl1⟩ := eN_T hx hx1 hlE
  obtain ⟨hGT, -, hG1, -, -⟩ := geq_facts hx hx1 hlT hl1
  obtain ⟨hl'T, hl'1⟩ := eN_T hx hx1 (hl'l.trans hlE)
  have hxa : x < a := (geq_facts hx hx1 hl'T hl'1).2.1.trans h1
  have hla : l < a := hlE.trans_le ((geq_eN_le hx hx1 hl'T hl'1).trans h1.le)
  have ha1 : a < Om1 := h2.trans hG1
  have haT : a ∈ Tset x := vz_T_down hx hx1 hGT hG1 h2.le
  obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hx hx1 haT hxa.le ha1 (inE_indec haE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξv]; exact hxa, by rw [hξv]; exact haE⟩
  have hξk : ξ < Om1 * Om1 + l :=
    lgLt_of_vt_lt hx hx1 hξT hξ2 hlT hl1 (by rw [hξv]; exact hla) (by rw [hξv]; exact h2)
  have haa : a * a ≤ a * a + a + lg l := le_self_add.trans le_self_add
  rcases lt_or_ge ξ (Om1 * Om1) with hξs | hξs
  · obtain ⟨hq1, hrT, hr1, hdec'⟩ := lu_split hx hx1 hξT hξ2 hΩξ
    have hqT : ξ / Om1 ∈ Tset x := lgQuot_mem hx hx1 hξT hξs
    have hqΩ : ξ / Om1 < Om1 := (Ordinal.lt_mul_iff_div_lt (Ordinal.omega_pos 1).ne').1 hξs
    set q := ξ / Om1 with hq
    set r := ξ % Om1 with hr
    have hv : vt x (Om1 * q + r) = a := by rw [hdec', hξv]
    have hζr : luZeta x q r < a := by
      refine lu_zeta_le.trans_lt ?_
      rcases lt_or_ge q x with hqx | hxq
      · have := (lu_th_facts hx hx1 hq1 hqx hrT hr1).2.2.2.2.2.2.2
        rwa [hv] at this
      · have := (Lv.gen_facts hx hx1 hqT hxq hqΩ hrT hr1).2.2.2.2.2.2.2.2
        rwa [hv] at this
    have hL : IsLh1 a (luL a q + luZeta x q r) ∧ q < a := by
      rcases lt_or_ge q x with hqx | hxq
      · have h := lu_lh_th hx hx1 hq1 hqx hrT hr1
        rw [hv] at h
        exact ⟨h, hqx.trans hxa⟩
      · have h := Lv.lv_lh_gen hx hx1 hqT hxq hqΩ hrT hr1
        have hqv := (Lv.gen_facts hx hx1 hqT hxq hqΩ hrT hr1).2.2.2.2.2.2.2.1
        rw [hv] at h hqv
        exact ⟨h, hqv⟩
    have hle := hL.1.2 _ hR
    exact absurd ((haa.trans hle).trans_lt (lg_luL_lt_sq haE hL.2 hζr)) (lt_irrefl _)
  · have hje : Om1 * Om1 + (ξ - Om1 * Om1) = ξ := Ordinal.add_sub_cancel_of_le hξs
    obtain ⟨ν, hν⟩ : ∃ ν, ξ - Om1 * Om1 = ν := ⟨_, rfl⟩
    rw [hν] at hje
    have hνl : ν < l := (add_lt_add_iff_left _).1 (by rw [hje]; exact hξk)
    have hva : a = gq ν x := by rw [← hξv, ← hje]; rfl
    have hl'ν : l' < ν := by
      by_contra hle
      push Not at hle
      have h3 : gq ν x ≤ gq l' x := geq_mono hx hx1 (hl'l.trans hlE) hle
      rw [← hva] at h3
      exact absurd (h1.trans_le h3) (lt_irrefl _)
    have hν0 : 0 < ν := lt_of_le_of_lt zero_le hl'ν
    have hL := geq_lh hx hx1 (hνl.trans hlE) hν0
    rw [← hva] at hL
    have hle := (add_le_add_iff_left (a * a + a)).1 (hL.2 _ hR)
    exact absurd hle (not_le.2 (gc_lg_lt hdec hdvd hl'ν hνl))

end GQL

/-! ## The copy of a linear term -/

theorem ge_lin_chain {ρ δ : Ordinal.{0}} (hρE : InE ρ) (hδE : InE δ) (hρδ : ρ < δ) : ∀ k : ℕ, 1 ≤ k →
    ∃ W : Finset Ordinal.{0}, WZ ρ δ W ∅ ∧ ρ ∈ W ∧ ρ * (k : Ordinal.{0}) ∈ W ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ImgCtx ρ A f →
        f (ρ * (k : Ordinal.{0})) = f ρ * (k : Ordinal.{0})
  | 0, h => absurd h (by norm_num)
  | 1, _ => by
      refine ⟨{ρ}, ?_, by simp, by simp, fun A f _ _ => by simp⟩
      have := (WZ.empty (ρ := ρ) (δ := δ)).insW le_rfl hρδ (Or.inl (inE_indec hρE))
      simpa using this
  | k + 2, _ => by
      obtain ⟨W, hW, hρW, hkW, hf⟩ := ge_lin_chain hρE hδE hρδ (k + 1) (by omega)
      have hρ0 : 0 < ρ := hρE.pos
      have hk1 : (1 : Ordinal.{0}) ≤ ((k + 1 : ℕ) : Ordinal.{0}) := by exact_mod_cast Nat.le_add_left 1 k
      have e3 : ∀ y : Ordinal.{0}, y * ((k + 2 : ℕ) : Ordinal.{0}) = y * ((k + 1 : ℕ) : Ordinal.{0}) + y :=
        fun y => by rw [show (k + 2 : ℕ) = (k + 1) + 1 from rfl, Nat.cast_succ (k + 1), mul_add_one]
      have e2 := e3 ρ
      have hρk : ρ ≤ ρ * ((k + 1 : ℕ) : Ordinal.{0}) := le_mul_of_one_le_right' hk1
      have hlt : ρ * ((k + 2 : ℕ) : Ordinal.{0}) < δ := by
        rw [e2]
        exact (inE_indec hδE).add_lt (hδE.mul_lt hρδ ((natCast_lt_omega0 _).trans (omega0_lt_inE hδE))) hρδ
      have hW' := hW.insW (hρk.trans (by rw [e2]; exact le_self_add)) hlt
        (Or.inr ⟨ρ * ((k + 1 : ℕ) : Ordinal.{0}), Finset.mem_union_left _ hkW, ρ, Finset.mem_union_left _ hρW,
          by rw [e2]; exact lt_add_of_pos_right _ hρ0,
          by rw [e2]; exact hρk.trans_lt (lt_add_of_pos_right _ hρ0), e2.symm⟩)
      refine ⟨insert (ρ * ((k + 2 : ℕ) : Ordinal.{0})) W, hW', by simp [hρW], by simp,
        fun A f hA C => ?_⟩
      have hA' : ↑W ⊆ A := fun z hz => hA (by simp [Finset.mem_coe.1 hz])
      have hkA : ρ * ((k + 1 : ℕ) : Ordinal.{0}) ∈ A := hA' (Finset.mem_coe.2 hkW)
      have hρA : ρ ∈ A := hA' (Finset.mem_coe.2 hρW)
      have hk2A : ρ * ((k + 2 : ℕ) : Ordinal.{0}) ∈ A := hA (by simp)
      have hadd := C.add _ hkA ρ hρA _ hk2A e2.symm
      rw [← hadd, hf A f hA' C, e3 (f ρ)]

/-- **The copy of a linear term**: `ρ·k + d` (`d < ρ`) lies in the witness sets, and the copies keep it:
`f(ρ·k + d) = fρ·k + d`. -/
theorem ge_lin {ρ δ : Ordinal.{0}} (hρE : InE ρ) (hδE : InE δ) (hρδ : ρ < δ) (k : ℕ) {d : Ordinal.{0}}
    (hd : d < ρ) : ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ ρ * (k : Ordinal.{0}) + d ∈ W ∪ Z ∧ ρ ∈ W ∪ Z ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
        f (ρ * (k : Ordinal.{0}) + d) = f ρ * (k : Ordinal.{0}) + d := by
  classical
  have hρ0 : 0 < ρ := hρE.pos
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨{ρ}, {d}, ?_, by simp, by simp, fun A f _ hZ C => ?_⟩
    · have := ((WZ.empty (ρ := ρ) (δ := δ)).insW le_rfl hρδ (Or.inl (inE_indec hρE))).insZ hd
      simpa using this
    · simp only [Nat.cast_zero, mul_zero, zero_add]
      exact C.fix d (hZ (by simp)) hd
  obtain ⟨W, hW, hρW, hkW, hf⟩ := ge_lin_chain hρE hδE hρδ k hk
  have hk1 : (1 : Ordinal.{0}) ≤ (k : Ordinal.{0}) := by exact_mod_cast hk
  have hρk : ρ ≤ ρ * (k : Ordinal.{0}) := le_mul_of_one_le_right' hk1
  rcases eq_or_ne d 0 with rfl | hd0
  · refine ⟨W, ∅, hW, by simp [hkW], by simp [hρW], fun A f hA _ C => ?_⟩
    rw [add_zero, add_zero]; exact hf A f hA C
  have hlt : ρ * (k : Ordinal.{0}) + d < δ :=
    (inE_indec hδE).add_lt (hδE.mul_lt hρδ ((natCast_lt_omega0 _).trans (omega0_lt_inE hδE))) (hd.trans hρδ)
  have hW' := (hW.insZ hd).insW (hρk.trans le_self_add) hlt
    (Or.inr ⟨ρ * (k : Ordinal.{0}), Finset.mem_union_left _ hkW, d, Finset.mem_union_right _
        (Finset.mem_insert_self _ _),
      lt_add_of_pos_right _ (pos_iff_ne_zero.2 hd0), hd.trans_le (hρk.trans le_self_add), rfl⟩)
  refine ⟨insert (ρ * (k : Ordinal.{0}) + d) W, {d}, by simpa using hW', by simp, by simp [hρW],
    fun A f hA hZ C => ?_⟩
  have hA' : ↑W ⊆ A := fun z hz => hA (by simp [Finset.mem_coe.1 hz])
  have hkA : ρ * (k : Ordinal.{0}) ∈ A := hA' (Finset.mem_coe.2 hkW)
  have hdA : d ∈ A := hZ (by simp)
  have hsA : ρ * (k : Ordinal.{0}) + d ∈ A := hA (by simp)
  rw [← C.add _ hkA d hdA _ hsA rfl, hf A f hA' C, C.fix d hdA hd]

/-! ## The family of the layers of the smaller codes, and its union -/

/-- **A family of gated layers below a limit code `a`**: for every code `b < a` a gated layer, gate at most `gate b`,
with top `ϑˣ(Ω₁·Ω₁ + 1 + sbc b x)` at every base above `gate b`. -/
structure GeLimF (a : Ordinal.{0}) where
  K : Iio a → GdB
  g_le : ∀ b, (K b).g ≤ gate b.1
  E_eq : ∀ b x, InE x → x < Om1 → gate b.1 < x → (K b).K.E x = gq (1 + sbc b.1 x) x

section Fam

variable {a : Ordinal.{0}} (F : GeLimF a)

theorem geO_lt {b x : Ordinal.{0}} (hb : b < geW) (hx : InE x) (hg : gate b < x) : 1 + sbc b x < eN x :=
  (inE_indec (eN_E x)).add_lt (one_lt_omega0.trans (omega0_lt_inE (eN_E x))) (sb_lt_eN hb hx hg)

theorem geF_top (ha : a < geW) (b : Iio a) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hgx : gate b.1 < x) :
    (F.K b).K.sys.top x = gq (1 + sbc b.1 x) x := by
  rw [(F.K b).K.top_eq x hx hx1 ((F.g_le b).trans_lt hgx), F.E_eq b x hx hx1 hgx]
  obtain ⟨hT, h1⟩ := eN_T hx hx1 (geO_lt (b.2.trans ha) hx hgx)
  exact (geq_facts hx hx1 hT h1).2.2.2.1

theorem one_add_le_succ (u : Ordinal.{0}) : 1 + u ≤ u + 1 := by
  rcases le_or_gt ω u with h | h
  · rw [one_add_of_omega0_le h]; exact le_self_add
  · obtain ⟨n, rfl⟩ := lt_omega0.1 h
    have e : (1 : Ordinal.{0}) + n = n + 1 := by
      calc (1 : Ordinal.{0}) + n = ((1 + n : ℕ) : Ordinal.{0}) := by norm_cast
        _ = ((n + 1 : ℕ) : Ordinal.{0}) := by rw [Nat.add_comm]
        _ = n + 1 := by norm_cast
    rw [e]

theorem geF_lt (hl : IsSuccLimit a) (ha : a < geW) {b : Iio a} {x : Ordinal.{0}} (hx : InE x) (hga : gate a < x)
    (hgb : gate b.1 < x) :
    1 + sbc b.1 x < sbc a x :=
  (one_add_le_succ _).trans_lt ((sb_lim_facts hl ha).elim fun _ h => h.elim fun _ h => h.elim fun _ h =>
    (h.2.2.2 x hx hga).2.2.2.2.2.add_one_lt (sb_lt_mono ha hx b.2 hga hgb))

end Fam

theorem geO_facts {b x : Ordinal.{0}} (hb : b < geW) (hx : InE x) (hx1 : x < Om1) (hg : gate b < x) :
    gq (1 + sbc b x) x ∈ Tset x ∧ x < gq (1 + sbc b x) x ∧ gq (1 + sbc b x) x < Om1 ∧ InE (gq (1 + sbc b x) x) ∧
      Indec (gq (1 + sbc b x) x) :=
  geq_facts hx hx1 (eN_T hx hx1 (geO_lt hb hx hg)).1 (eN_T hx hx1 (geO_lt hb hx hg)).2

theorem geO_lt_next {b x : Ordinal.{0}} (hb : b < geW) (hx : InE x) (hx1 : x < Om1) (hg : gate b < x)
    {u : Ordinal.{0}} (hxu : x < u) (hu : LtInf1 u) : gq (1 + sbc b x) x < u :=
  geq_lt_next hx hx1 (eN_T hx hx1 (geO_lt hb hx hg)).1 (eN_T hx hx1 (geO_lt hb hx hg)).2 hxu hu

/-- **EXACT for the offset `1 + sbc b x`.** -/
theorem geO_pi {σ ρ b : Ordinal.{0}} (hB : Bases σ ρ) (hb : b < geW) (hg : gate b < σ) :
    1 + sbc b ρ ∈ TB ρ σ ∧ pi σ ρ (1 + sbc b ρ) = 1 + sbc b σ := by
  have h1σ : (1 : Ordinal.{0}) < σ := Lu.lu_one_lt_E hB.1
  obtain ⟨h1, h2⟩ := sb_pi hB hb hg
  obtain ⟨h3, h4⟩ := pi_add hB (mem_TB_of_lt hB h1σ) h1
  exact ⟨h3, by rw [h4, pi_lt hB h1σ, h2]⟩

theorem geU_val_lt {a : Ordinal.{0}} (hl : IsSuccLimit a) (ha : a < geW) (F : GeLimF a) {x : Ordinal.{0}}
    (hx : InE x) (hx1 : x < Om1) (hg : gate a < x) (p : Σ b : Iio a, (F.K b).K.sys.Tm)
    (h : gate p.1.1 < x ∧ (F.K p.1).K.sys.CB p.2 x) : (F.K p.1).K.sys.val p.2 x < gq (1 + sbc a x) x := by
  have h1 := (F.K p.1).K.lt_top_E x hx hx1 ((F.g_le p.1).trans_lt h.1) p.2 h.2
  rw [geF_top F ha p.1 hx hx1 h.1] at h1
  exact h1.trans (geq_lt hx hx1 (geO_lt ha hx hg) ((geF_lt hl ha hx hg h.1).trans_le le_add_self))

/-- **The union of the family**: the pairs `(b, t)`, `t` a term of `K_b`, with the side condition `gate b < x`; top
`ϑˣ(Ω₁·Ω₁ + 1 + sbc a x)`, gated at `gate a`. -/
noncomputable def geUSys (a : Ordinal.{0}) (hl : IsSuccLimit a) (ha : a < geW) (F : GeLimF a) : GdSys (gate a) where
  Tm := Σ b : Iio a, (F.K b).K.sys.Tm
  val := fun p x => (F.K p.1).K.sys.val p.2 x
  CB := fun p x => gate p.1.1 < x ∧ (F.K p.1).K.sys.CB p.2 x
  cs := fun p => gate p.1.1 :: (F.K p.1).K.sys.cs p.2
  cst := fun c => ⟨⟨0, hl.bot_lt⟩, (F.K ⟨0, hl.bot_lt⟩).K.sys.cst c⟩
  top := fun x => gq (1 + sbc a x) x
  cb_cst := fun p s h c hc => by
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · exact (F.K p.1).K.sys.cb_cst p.2 s h.2 c hc
  cb_iff := fun p s s' h h' => ⟨h' _ List.mem_cons_self,
    (F.K p.1).K.sys.cb_iff p.2 s s' h.2 (fun c hc => h' c (List.mem_cons_of_mem _ hc))⟩
  val_cst := fun c x => (F.K ⟨0, hl.bot_lt⟩).K.sys.val_cst c x
  cb_cstI := fun c x h => ⟨by rw [gate_zero]; exact lt_of_le_of_lt zero_le h,
    (F.K ⟨0, hl.bot_lt⟩).K.sys.cb_cstI c x h⟩
  lt_top := fun _ hr hr1 hg p h => geU_val_lt hl ha F (ups_inE hr) (ups_lt_Om1 _ hr1) hg p h
  one_le_top := fun _ hr hr1 hg => one_le_iff_pos.2 (geO_facts ha (ups_inE hr) (ups_lt_Om1 _ hr1) hg).2.2.2.1.pos
  rep := fun r hr hr1 hg v hv => by
    have hx := ups_inE hr
    have hx1 := ups_lt_Om1 r hr1
    obtain ⟨a', k, d, -, -, -, hF⟩ := sb_lim_facts hl ha
    obtain ⟨-, -, -, -, e5, e6⟩ := hF _ hx hg
    rw [e5] at hv
    obtain ⟨ν, hν, hvν⟩ := ge_lt_lim_iff hx hx1 e6 (sb_lt_eN ha hx hg) v hv
    obtain ⟨b, hb, hgb, hsb⟩ := sb_surj ha hx hx1 hg hν
    have hlt : v < (F.K ⟨b, hb⟩).K.sys.top (upsilon r) := by
      rw [geF_top F ha ⟨b, hb⟩ hx hx1 hgb]
      refine hvν.trans_le (geq_mono hx hx1 (geO_lt (hb.trans ha) hx hgb) ?_)
      rw [hsb]; exact le_add_self
    obtain ⟨t, ht, et⟩ := (F.K ⟨b, hb⟩).K.sys.rep r hr hr1 ((F.g_le _).trans_lt hgb) v hlt
    exact ⟨⟨⟨b, hb⟩, t⟩, ⟨hgb, ht⟩, et⟩
  top_lt := fun r hr hr1 hg => by
    have hl0 : 0 < r := pos_iff_ne_zero.2 hr.1
    have h1 : r < r + ω := lt_add_of_pos_right r omega0_pos
    have hτU := upsPt_upsilon (hl0.trans h1)
    exact (geO_lt_next ha (ups_inE hr) (ups_lt_Om1 r hr1) hg (upsilon_normal.strictMono h1) hτU.2).trans
      (upsilon_normal.strictMono (lt_add_one _))
  pkg := fun r hr hr1 _ p h h1 R => (F.K p.1).K.sys.pkg r hr hr1 ((F.g_le p.1).trans_lt h.1) p.2 h.2 h1 R
  rs := fun r hr hr1 _ p h => (F.K p.1).K.sys.rs r hr hr1 ((F.g_le p.1).trans_lt h.1) p.2 h.2
  uni_le := fun σ ρ hσ hρ hB _ p q hp hq =>
    xt_uni_of_exact hB ((F.K p.1).K.exact σ ρ hσ hρ hB ((F.g_le p.1).trans_lt hp.1) p.2 hp.2)
      ((F.K q.1).K.exact σ ρ hσ hρ hB ((F.g_le q.1).trans_lt hq.1) q.2 hq.2)
  small := fun p => ((F.K p.1).K.sys.small p.2).imp id fun h x hx hx1 _ hc =>
    h x hx hx1 ((F.g_le p.1).trans_lt hc.1) hc.2

theorem geUSys_top (a : Ordinal.{0}) (hl : IsSuccLimit a) (ha : a < geW) (F : GeLimF a) (x : Ordinal.{0}) :
    (geUSys a hl ha F).top x = gq (1 + sbc a x) x := rfl

namespace GeLK

variable {a : Ordinal.{0}} (hl : IsSuccLimit a) (ha : a < geW) (F : GeLimF a) {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
  (hgρ : gate a < ρ)
include hl ha F h hgρ

/-- **THE TOP WITNESS for a term offset** above `gate a`: `f(G) ∈ E` and `ϑ^{fρ}(Ω₁·Ω₁ + 1 + sbc a (fρ)) ≤ f(G)`,
`G = ϑ^ρ(Ω₁·Ω₁ + 1 + sbc a ρ)`, for the copies that keep `gate a`; from the copy of `G ≤₁ G·G + G + (ρ·k + d)`
(`logend(sbc a ρ) = ρ·k + d`, `ge_lin`), the witness of the predecessor layer `K_{a'}` and `ge_not_le1R_lim`. -/
theorem geTopWit : ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ gq (1 + sbc a ρ) ρ ∈ W ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → GdCtx (gate a) ρ A f →
      (∃ e', f (gq (1 + sbc a ρ) ρ) = ω ^ e' ∧ ω ^ f ρ ∣ e') ∧
        gq (1 + sbc a (f ρ)) (f ρ) ≤ f (gq (1 + sbc a ρ) ρ) := by
  classical
  have hρE := upsPt_inE h.ρU
  obtain ⟨a', k, d, ha'a, hg', hd, hF⟩ := sb_lim_facts hl ha
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hF ρ hρE hgρ
  rw [e5]
  have hlE := sb_lt_eN ha hρE hgρ
  obtain ⟨hlT, hl1⟩ := eN_T hρE h.ρ1 hlE
  obtain ⟨-, hρG, -, hGE, hGI⟩ := geq_facts hρE h.ρ1 hlT hl1
  have hl0 : 0 < sbc a ρ := lt_of_lt_of_le omega0_pos e4
  have hLG := geq_lh hρE h.ρ1 hlE hl0
  rw [e3] at hLG
  have hdρ : d < ρ := hd.trans_lt hgρ
  set G := gq (sbc a ρ) ρ with hG
  set ζ := ρ * (k : Ordinal.{0}) + d with hζ
  have hζ0 : 0 < ζ := by have := Gc.gc_lg_pos e6; rw [e3] at this; exact this
  have hGδ : G < δ := (geq_lt_next hρE h.ρ1 hlT hl1 h.ρτ h.τU.2).trans h.τδ
  have hρδ : ρ < δ := hρG.trans hGδ
  have hζG : ζ < G := by
    have hE := hGE
    refine (inE_indec hE).add_lt (hE.mul_lt hρG ((natCast_lt_omega0 _).trans (omega0_lt_inE hE))) (hdρ.trans hρG)
  have hPδ : G * G < δ := h.δE.mul_lt hGδ hGδ
  have hGGδ : G + G < δ := (inE_indec h.δE).add_lt hGδ hGδ
  have hPGδ : G * G + G < δ := (inE_indec h.δE).add_lt hPδ hGδ
  have hPGζδ : G * G + G + ζ < δ := (inE_indec h.δE).add_lt hPGδ (hζG.trans hGδ)
  have hG0 : 0 < G := hGE.pos
  have hGP : G < G * G := lt_mul_of_one_lt_right hG0 (lu_one_lt_E hGE)
  have hPe : G * G = ω ^ (G + G) := by
    conv_lhs => rw [← show ω ^ G = G from hGE]
    rw [← opow_add]
  have hρPG : ρ ≤ G * G + G := (hρG.le.trans hGP.le).trans le_self_add
  have w1 : WZ ρ δ {G} ∅ := by
    have := (WZ.empty (ρ := ρ) (δ := δ)).insW hρG.le hGδ (Or.inl hGI)
    simpa using this
  have w2 : WZ ρ δ {G + G, G} ∅ := by
    have := w1.insW (hρG.le.trans le_self_add) hGGδ
      (Or.inr ⟨G, by simp, G, by simp, lt_add_of_pos_right _ hG0, lt_add_of_pos_right _ hG0, rfl⟩)
    simpa using this
  have w3 : WZ ρ δ {G * G, G + G, G} ∅ := by
    have := w2.insW (hρG.le.trans hGP.le) hPδ (Or.inl (by rw [hPe]; exact indec_opow _))
    simpa using this
  have w4 : WZ ρ δ {G * G + G, G * G, G + G, G} ∅ := by
    have := w3.insW hρPG hPGδ
      (Or.inr ⟨G * G, by simp, G, by simp, lt_add_of_pos_right _ hG0, hGP.trans_le le_self_add, rfl⟩)
    simpa using this
  obtain ⟨WL, ZL, wL, hζWZ, -, hfL⟩ := ge_lin hρE h.δE hρδ k hdρ
  have w45 := w4.union wL
  have w5 := w45.insW (hρPG.trans le_self_add) hPGζδ
    (Or.inr ⟨G * G + G, Finset.mem_union_left _ (Finset.mem_union_left _ (by simp)), ζ,
      (by
        rcases Finset.mem_union.1 hζWZ with h' | h'
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ h')
        · exact Finset.mem_union_right _ (Finset.mem_union_right _ h')),
      lt_add_of_pos_right _ hζ0, hζG.trans_le ((le_mul_left _ hG0).trans le_self_add |>.trans le_self_add),
      rfl⟩)
  set K' := F.K ⟨a', ha'a⟩ with hK'
  have hga'ρ : gate a' < ρ := hg'.trans_lt hgρ
  have hgK : K'.g < ρ := (F.g_le _).trans_lt hga'ρ
  obtain ⟨WE, ZE, wE, hTE, hIE⟩ := K'.K.top_wit ρ τ δ h hgK
  have w6 := (w5.union wE).insZ hgK
  refine ⟨insert (G * G + G + ζ) ({G * G + G, G * G, G + G, G} ∪ WL) ∪ WE, insert K'.g ((∅ ∪ ZL) ∪ ZE), w6,
    by simp, fun A f hW hZ C => ?_⟩
  have hGA : G ∈ A := hW (by simp)
  have hGGA : G + G ∈ A := hW (by simp)
  have hPA : G * G ∈ A := hW (by simp)
  have hPGA : G * G + G ∈ A := hW (by simp)
  have hPGζA : G * G + G + ζ ∈ A := hW (by simp)
  have hWL : ↑WL ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hZL : ↑ZL ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
  have hζA : ζ ∈ A := by
    rcases Finset.mem_union.1 hζWZ with h' | h'
    · exact hWL (Finset.mem_coe.2 h')
    · exact hZL (Finset.mem_coe.2 h')
  have hgA : K'.g ∈ A := hZ (by simp)
  have hWE : ↑WE ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hZE : ↑ZE ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
  have hTA : K'.K.sys.top ρ ∈ A := hWE (Finset.mem_coe.2 hTE)
  obtain ⟨hfE, hPge⟩ := GbK.gbImg h hGE hρG hGδ C.1 hGA hGGA hPA hPGA
  have hyG : f ρ < f G := C.mono C.rho hGA hρG
  refine ⟨⟨f G, hfE.symm, opow_dvd_of_inE hfE hyG.le⟩, ?_⟩
  obtain ⟨hyE, hy1, -⟩ := h.vz_img_base C.1
  have hgy : gate a < f ρ := C.lt hgρ
  have hga'y : gate a' < f ρ := hg'.trans_lt hgy
  obtain ⟨f1, f2, f3, -, f5, -⟩ := hF (f ρ) hyE hgy
  rw [f5]
  have hTρ : K'.K.sys.top ρ = gq (1 + sbc a' ρ) ρ := geF_top F ha ⟨a', ha'a⟩ hρE h.ρ1 hga'ρ
  have hTy : K'.K.sys.top (f ρ) = gq (1 + sbc a' (f ρ)) (f ρ) := geF_top F ha ⟨a', ha'a⟩ hyE hy1 hga'y
  have hEG : gq (1 + sbc a' ρ) ρ < G :=
    geq_lt hρE h.ρ1 hlE (geF_lt hl ha (b := ⟨a', ha'a⟩) hρE hgρ hga'ρ)
  have hfEG : f (K'.K.sys.top ρ) < f G := C.mono hTA hGA (by rw [hTρ]; exact hEG)
  have hEy : gq (sbc a' (f ρ)) (f ρ) < f G := by
    have h1 := (hIE A f hWE hZE ⟨C.1, hgA⟩).2
    rw [hTy] at h1
    exact (geq_mono hyE hy1 (geO_lt (ha'a.trans ha) hyE hga'y) le_add_self).trans_lt (h1.trans_lt hfEG)
  have hyl := sb_lt_eN ha hyE hgy
  by_cases hU : UpsPt (f G)
  · exact (geq_lt_next hyE hy1 (eN_T hyE hy1 hyl).1 (eN_T hyE hy1 hyl).2 hyG hU.2).le
  · by_contra hlt
    push Not at hlt
    have hsrc : le1 G (G * G + G + ζ) := (h.lowδ _ _ hρG hPGζδ.le).2 hLG.1
    have himg := C.cov1 G hGA _ hPGζA hsrc
    have hR := (C.sk _ (C.low _ hGA) hU _).1 himg
    have hfζ : f ζ = f ρ * (k : Ordinal.{0}) + d := hfL A f hWL hZL C.1
    have hadd1 : f (G * G + G) + f ζ = f (G * G + G + ζ) := C.add (G * G + G) hPGA ζ hζA _ hPGζA rfl
    have hadd2 : f (G * G) + f G = f (G * G + G) := C.add (G * G) hPA G hGA _ hPGA rfl
    have hle : f G * f G + f G + (f ρ * (k : Ordinal.{0}) + d) ≤ f (G * G + G + ζ) := by
      rw [← hadd1, hfζ, ← hadd2]
      exact add_le_add (add_le_add hPge le_rfl) le_rfl
    have hlo : f G ≤ f G * f G + f G + (f ρ * (k : Ordinal.{0}) + d) :=
      ((le_mul_left _ hfE.pos).trans le_self_add).trans le_self_add
    have ha'l : sbc a' (f ρ) < sbc a (f ρ) := sb_lt_mono ha hyE ha'a hgy hga'y
    refine ge_not_le1R_lim hyE hy1 hyl f1 f2 ha'l hfE hEy hlt ?_
    rw [f3]
    exact le1R_of_le hlo hle hR

end GeLK

/-- **The gated limit layer for a limit code `a`**: the union with top `ϑˣ(Ω₁·Ω₁ + 1 + sbc a x)`, gated at `gate a`. -/
noncomputable def geLimL (a : Ordinal.{0}) (hl : IsSuccLimit a) (ha : a < geW) (F : GeLimF a) : GdLay (gate a) where
  sys := geUSys a hl ha F
  E := fun x => gq (1 + sbc a x) x
  top_eq := fun x hx hx1 hg => (geO_facts ha hx hx1 hg).2.2.2.1.symm
  exp_dvd := fun x hx hx1 hg => opow_dvd_of_inE (geO_facts ha hx hx1 hg).2.2.2.1 (geO_facts ha hx hx1 hg).2.1.le
  exp_lt := fun x hx hx1 hg => (geO_facts ha hx hx1 hg).2.2.1
  top_gt := fun x hx hx1 hg => (geO_facts ha hx hx1 hg).2.1
  top_lt_ups := fun x u hx hx1 hg hxu hu => geO_lt_next ha hx hx1 hg hxu hu.2
  lt_top_E := fun x hx hx1 hg p h => geU_val_lt hl ha F hx hx1 hg p h
  exact := fun σ ρ hσ hρ hB _ p hp => (F.K p.1).K.exact σ ρ hσ hρ hB ((F.g_le p.1).trans_lt hp.1) p.2 hp.2
  exp_pi := fun _ ρ _ _ hB hg => geq_pi hB (geO_pi hB ha hg)
    (eN_T hB.2.1 hB.2.2.2 (geO_lt ha hB.2.1 (hg.trans hB.2.2.1))).2
  top_wit := fun _ _ _ h hg => GeLK.geTopWit hl ha F h hg

/-- **The gated limit base package** (gate `gate a`). -/
noncomputable def geLimB (a : Ordinal.{0}) (hl : IsSuccLimit a) (ha : a < geW) (F : GeLimF a) : GdB where
  g := gate a
  K := geLimL a hl ha F
  ek := fun x hx hx1 hg => (geO_facts ha hx hx1 hg).2.2.2.1
  mem := fun x hx hx1 hg => (geO_facts ha hx hx1 hg).1

theorem geLimB_E (a : Ordinal.{0}) (hl : IsSuccLimit a) (ha : a < geW) (F : GeLimF a) (x : Ordinal.{0}) :
    (geLimB a hl ha F).K.E x = gq (1 + sbc a x) x := rfl

theorem geLimB_g (a : Ordinal.{0}) (hl : IsSuccLimit a) (ha : a < geW) (F : GeLimF a) :
    (geLimB a hl ha F).g = gate a := rfl

end Googology.Trans.PoR.InaccPsi.R2.Ge

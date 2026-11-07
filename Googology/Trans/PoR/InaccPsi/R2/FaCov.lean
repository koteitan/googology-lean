import Googology.Trans.PoR.InaccPsi.R2.FaGx
import Googology.Trans.PoR.InaccPsi.R2.AwImg

/-!
# Fa: LEMMA IMG ON ALL READINGS, THE FRAME AND THE ARITHMETIC CASES

`FaCov ρ A h`: a map `h` of `A` below `ρ` keeping `<`, `+`, indecomposables, `≤₁`, `≤₂`, with `x ≤ h x` below `ρ`; `sk` and `pu` are what is
known about its image.  `FaUp ρ t`: the structure above `ρ` below `t` (non-`υ` points are read in `R₁⁺`, every `υ`-point is pinned by a pair).
`FaI S l t c` (**Lemma IMG at the code `c`**): witness sets containing `Θ_λ(c)` such that every such `h` with `h(ρ_λ) = ρ_μ` has
`Θ_μ(c) ≤ h(Θ_λ(c))`.  `c` need not be a code at `μ` (`Fa.fa_gx_add_le`, `Fa.fa_gx_opow`).

* `faI_small`, `faI_Om1`, `faI_add`, `faI_succ`, `faI_lim`, `faI_fin`.

No new axiom.  New definitions: `FaCov`, `FaUp`, `FaI`, `FaBig`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Fa

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm

variable {S : InaccSeq.{0}}

/-- **The covering maps of Lemma IMG.** -/
structure FaCov (ρ : Ordinal.{0}) (A : Set Ordinal.{0}) (h : Ordinal.{0} → Ordinal.{0}) : Prop where
  mono : StrictMonoOn h A
  add : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y = z → h x + h y = h z
  indec : ∀ x ∈ A, Indec x → Indec (h x)
  cov1 : ∀ x ∈ A, ∀ y ∈ A, le1 x y → le1 (h x) (h y)
  cov2 : ∀ x ∈ A, ∀ y ∈ A, le2 x y → le2 (h x) (h y)
  pw : ∀ x ∈ A, x < ρ → x ≤ h x
  low : ∀ x ∈ A, h x < ρ
  rho : ρ ∈ A
  sk : ∀ a ∈ A, ρ ≤ a → ¬ UpsPt (h a) → ∀ g, le1 (h a) g ↔ le1R (h a) g
  pu : ∀ a ∈ A, ∀ b ∈ A, ρ ≤ a → a < b → le2 (h a) (h b) → UpsPt (h a) ∧ UpsPt (h b)

/-- **The structure above `ρ` below `t`.** -/
structure FaUp (ρ t : Ordinal.{0}) : Prop where
  sk : ∀ α, ρ < α → α < t → ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ
  pin : ∀ u, ρ < u → u < t → UpsPt u → ∃ τ' δ', ρ < τ' ∧ τ' < δ' ∧ δ' < t ∧ le2 τ' δ' ∧ UpsPt τ' ∧ UpsPt δ' ∧
    ((u ≤ τ' ∧ le1 u τ') ∨ u = δ')

/-- **Lemma IMG at the code `c`.** -/
def FaI (S : InaccSeq.{0}) (l t c : Ordinal.{0}) : Prop :=
  ∃ W Z : Finset Ordinal.{0}, WZ (upsilon l) t W Z ∧ gxTh (upsilon l) (ldAtR S l) c ∈ W ∪ Z ∧
    ∀ (A : Set Ordinal.{0}) (h : Ordinal.{0} → Ordinal.{0}) (μ : Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → FaCov (upsilon l) A h →
      IsRestartIdx μ → h (upsilon l) = upsilon μ → gxTh (upsilon μ) (ldAtR S μ) c ≤ h (gxTh (upsilon l) (ldAtR S l) c)

/-- A `υ`-point image of `v` is at least the reading of `c`. -/
def FaBig (S : InaccSeq.{0}) (l t v c : Ordinal.{0}) : Prop :=
  ∃ W Z : Finset Ordinal.{0}, WZ (upsilon l) t W Z ∧
    ∀ (A : Set Ordinal.{0}) (h : Ordinal.{0} → Ordinal.{0}) (μ : Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → FaCov (upsilon l) A h →
      IsRestartIdx μ → h (upsilon l) = upsilon μ → v ∈ A → UpsPt (h v) → gxTh (upsilon μ) (ldAtR S μ) c ≤ h v

/-- `ω^z ∣ a` for codes gives `ω^{Θ z} ∣ Θ a`. -/
theorem fc_dvd {y : Ordinal.{0}} {At : Set Ordinal.{0}} (hy : SC y) (hAt : GxAt At) {z : Ordinal.{0}} (hz : GxCl y At z) :
    ∀ a, GxCl y At a → ω ^ z ∣ a → ω ^ gxTh y At z ∣ gxTh y At a := by
  refine Zk.zk_ind (fun _ _ => by rw [gxTh_zero]; exact dvd_zero _) ?_
  intro c k r hk0 hk hr IH ha hd
  obtain ⟨hcc, hrc⟩ := fc_parts_code hy hAt hk0 hk hr ha
  obtain ⟨e1, e2⟩ := fc_Rd_cnf hy hAt hk hcc hrc hr
  have hzc : z ≤ c := by
    by_contra hlt
    push Not at hlt
    have hne : ω ^ c * k + r ≠ 0 := (Zk.zk_parts hk0 hk hr).1
    have h1 : ω ^ z ≤ ω ^ c * k + r := Ordinal.le_of_dvd hne hd
    have h2 : ω ^ c * k + r < ω ^ (c + 1) := by
      rw [opow_add, opow_one]
      obtain ⟨n, rfl⟩ := lt_omega0.1 hk
      calc ω ^ c * (n : Ordinal.{0}) + r < ω ^ c * (n : Ordinal.{0}) + ω ^ c := (add_lt_add_iff_left _).2 hr
        _ = ω ^ c * ((n : Ordinal.{0}) + 1) := (mul_add_one _ _).symm
        _ ≤ ω ^ c * ω := mul_le_mul_right (by exact_mod_cast (natCast_lt_omega0 (n + 1)).le) _
    exact absurd (h1.trans_lt h2) (not_lt.2 ((opow_le_opow_iff_right one_lt_omega0).2 (Order.add_one_le_of_lt hlt)))
  have hdk : ω ^ z ∣ ω ^ c * k := (opow_dvd_opow ω hzc).trans (dvd_mul_right _ _)
  have hdr : ω ^ z ∣ r := (Ordinal.dvd_add_iff hdk).1 hd
  rw [e1]
  have h3 : ω ^ gxTh y At z ∣ ω ^ gxTh y At c * k :=
    (opow_dvd_opow ω (gxTh_mono hzc)).trans (dvd_mul_right _ _)
  exact dvd_add h3 (IH hrc hdr)

/-- **The image of a pinned `υ`-point is a `υ`-point.** -/
theorem fa_pin_wz {ρ t u : Ordinal.{0}} (hUp : FaUp ρ t) (h1 : ρ < u) (h2 : u < t) (hu : UpsPt u) :
    ∃ W : Finset Ordinal.{0}, WZ ρ t W ∅ ∧ ∀ (A : Set Ordinal.{0}) (h : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → u ∈ A →
      FaCov ρ A h → UpsPt (h u) := by
  classical
  obtain ⟨τ', δ', h0, hτδ, hδt, h2p, hτU, hδU, hc⟩ := hUp.pin u h1 h2 hu
  refine ⟨{τ', δ'}, ?_, fun A h hW huA C => ?_⟩
  · have w1 := (WZ.empty (ρ := ρ) (δ := t)).insW (w := δ') (h0.le.trans hτδ.le) hδt (Or.inl (indec_of_upsPt hδU))
    have w2 := w1.insW (w := τ') h0.le (hτδ.trans hδt) (Or.inl (indec_of_upsPt hτU))
    simpa using w2
  have hτA : τ' ∈ A := hW (by simp)
  have hδA : δ' ∈ A := hW (by simp)
  obtain ⟨hfτ, hfδ⟩ := C.pu τ' hτA δ' hδA h0.le hτδ (C.cov2 _ hτA _ hδA h2p)
  rcases hc with ⟨hle, h1'⟩ | rfl
  · rcases hle.lt_or_eq with hlt | rfl
    · by_contra hU
      have hR := (C.sk u huA h1.le hU _).1 (C.cov1 _ huA _ hτA h1')
      have hlt' := C.mono huA hτA hlt
      have hpos : 0 < h u := by
        have hρu := C.mono C.rho huA h1
        exact lt_of_le_of_lt zero_le hρu
      exact hU ⟨hpos, (le1R_lt_ups hfτ hlt' le_rfl).1 hR⟩
    · exact hfτ
  · exact hfδ

section Arith

variable {l ηx t : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

theorem fa_mu {A : Set Ordinal.{0}} {h : Ordinal.{0} → Ordinal.{0}} {μ : Ordinal.{0}} (C : FaCov (upsilon l) A h)
    (hμ : IsRestartIdx μ) (he : h (upsilon l) = upsilon μ) :
    upsilon μ < upsilon l ∧ SC (upsilon μ) ∧ upsilon μ < Om 1 ∧ GxAt (ldAtR S μ) ∧ UpsPt (upsilon μ) := by
  have h1 : upsilon μ < upsilon l := by rw [← he]; exact C.low _ C.rho
  obtain ⟨hZ, hZ1⟩ := Vb.vbZ hμ (h1.trans hX)
  exact ⟨h1, hZ, hZ1, ldAt_GxAt _ _, upsPt_upsilon (pos_iff_ne_zero.2 hμ.1)⟩

/-- **A code below `ρ`.** -/
theorem faI_small {c : Ordinal.{0}} (hc : c < upsilon l) : FaI S l t c := by
  classical
  refine ⟨∅, {c}, WZ.empty.insZ hc |> fun w => by simpa using w, ?_, fun A h μ _ hZ C _ _ => ?_⟩
  · rw [gxTh_small hc.le]; simp
  · rw [gxTh_small hc.le]
    have hcA : c ∈ A := hZ (by simp)
    exact (cdOtp_le_self _ c).trans (C.pw c hcA hc)

/-- **`Ω₁`.** -/
theorem faI_Om1 (ht : upsilon l < t) : FaI S l t (Om 1) := by
  classical
  obtain ⟨hZ, hZ1⟩ := Vb.vbZ hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hI : Indec (upsilon l) := indec_of_upsPt (upsPt_upsilon hl0)
  refine ⟨{upsilon l}, ∅, ?_, ?_, fun A h μ hW _ C hμ he => ?_⟩
  · have := (WZ.empty (ρ := upsilon l) (δ := t)).insW le_rfl ht (Or.inl hI)
    simpa using this
  · rw [gxTh_Om1 hZ hZ1 hAt]; simp
  · obtain ⟨-, hS, h1, hAtμ, -⟩ := fa_mu hl hX C hμ he
    rw [gxTh_Om1 hZ hZ1 hAt, gxTh_Om1 hS h1 hAtμ, he]

/-- **A sum.** -/
theorem faI_add {u z : Ordinal.{0}} (hu : GxCl (upsilon l) (ldAtR S l) u) (hzc : GxCl (upsilon l) (ldAtR S l) (ω ^ z))
    (hd : ω ^ z ∣ u) (hu0 : u ≠ 0) (h1 : FaI S l t u) (h2 : FaI S l t (ω ^ z))
    (hρv : upsilon l ≤ gxTh (upsilon l) (ldAtR S l) (u + ω ^ z))
    (htv : gxTh (upsilon l) (ldAtR S l) (u + ω ^ z) < t) : FaI S l t (u + ω ^ z) := by
  classical
  obtain ⟨hZ, -⟩ := Vb.vbZ hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  obtain ⟨W1, Z1, w1, m1, b1⟩ := h1
  obtain ⟨W2, Z2, w2, m2, b2⟩ := h2
  have e := gxTh_add hZ hAt hu (ω ^ z)
  have hu1 : u < u + ω ^ z := lt_add_of_pos_right _ (opow_pos _ omega0_pos)
  have hv2 : ω ^ z < u + ω ^ z := by
    have hle : ω ^ z ≤ u := Ordinal.le_of_dvd hu0 hd
    exact (lt_add_of_pos_right _ (opow_pos _ omega0_pos)).trans_le (add_le_add hle le_rfl)
  have hlt1 := gxTh_lt hu hu1
  have hlt2 := gxTh_lt hzc hv2
  have hm : ∀ x, x ∈ W1 ∪ Z1 ∨ x ∈ W2 ∪ Z2 → x ∈ W1 ∪ W2 ∪ (Z1 ∪ Z2) := by
    intro x hx
    rcases hx with hx | hx <;> rcases Finset.mem_union.1 hx with hx | hx <;> simp [hx]
  refine ⟨_, _, (w1.union w2).insW hρv htv (Or.inr ⟨_, hm _ (Or.inl m1), _, hm _ (Or.inr m2), hlt1, hlt2, e.symm⟩),
    by simp, fun A h μ hW hZ' C hμ he => ?_⟩
  have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hW2 : ↑W2 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ' (by simp [Finset.mem_coe.1 hx])
  have hZ2 : ↑Z2 ⊆ A := fun x hx => hZ' (by simp [Finset.mem_coe.1 hx])
  have a1 := mem_A m1 hW1 hZ1
  have a2 := mem_A m2 hW2 hZ2
  have p1 := b1 A h μ hW1 hZ1 C hμ he
  have p2 := b2 A h μ hW2 hZ2 C hμ he
  have hvA : gxTh (upsilon l) (ldAtR S l) (u + ω ^ z) ∈ A := hW (by simp)
  obtain ⟨-, hσS, -, hAtμ, -⟩ := fa_mu hl hX C hμ he
  have := C.add _ a1 _ a2 _ hvA e.symm
  rw [← this]
  exact (fa_gx_add_le hσS hAtμ hd le_rfl).trans (add_le_add p1 p2)

/-- **`ω^{a+1}`** from `ω^a`. -/
theorem faI_succ {a : Ordinal.{0}} (ha : GxCl (upsilon l) (ldAtR S l) a) (hw : FaI S l t (ω ^ a))
    (hρv : upsilon l ≤ gxTh (upsilon l) (ldAtR S l) (ω ^ (a + 1)))
    (htv : gxTh (upsilon l) (ldAtR S l) (ω ^ (a + 1)) < t) : FaI S l t (ω ^ (a + 1)) := by
  classical
  obtain ⟨hZ, -⟩ := Vb.vbZ hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have h1Z : (1 : Ordinal.{0}) < upsilon l := Gg.gg_one_lt_of_SC hZ
  have hS1 : GxCl (upsilon l) (ldAtR S l) 1 := GxCl.small h1Z
  obtain ⟨W1, Z1, w1, m1, b1⟩ := hw
  have e1 : gxTh (upsilon l) (ldAtR S l) (ω ^ (a + 1)) = ω ^ (gxTh (upsilon l) (ldAtR S l) a + 1) := by
    rw [gxTh_opow hZ hAt (GxCl.add ha hS1), gxTh_add hZ hAt ha, gxTh_small h1Z.le]
  have hind : Indec (gxTh (upsilon l) (ldAtR S l) (ω ^ (a + 1))) := by rw [e1]; exact indec_opow _
  refine ⟨_, _, w1.insW hρv htv (Or.inl hind), by simp, fun A h μ hW hZ' C hμ he => ?_⟩
  have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have aw := mem_A m1 hW1 hZ'
  have pw := b1 A h μ hW1 hZ' C hμ he
  obtain ⟨-, hσS, -, hAtμ, -⟩ := fa_mu hl hX C hμ he
  have hvA : gxTh (upsilon l) (ldAtR S l) (ω ^ (a + 1)) ∈ A := hW (by simp)
  have hlt : h (gxTh (upsilon l) (ldAtR S l) (ω ^ a)) < h (gxTh (upsilon l) (ldAtR S l) (ω ^ (a + 1))) :=
    C.mono aw hvA (gxTh_lt (ha.opow hZ.1) ((opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_one a)))
  obtain ⟨a0, ha0⟩ := indec_eq_opow (C.indec _ hvA hind)
  rw [ha0] at hlt ⊢
  rw [fa_gx_opow hσS hAtμ] at pw ⊢
  have hlt' : gxTh (upsilon μ) (ldAtR S μ) a < a0 := (opow_lt_opow_iff_right one_lt_omega0).1 (lt_of_le_of_lt pw hlt)
  refine (opow_le_opow_iff_right one_lt_omega0).2 ?_
  have h2 : gxTh (upsilon μ) (ldAtR S μ) (a + 1) ≤ gxTh (upsilon μ) (ldAtR S μ) a + gxTh (upsilon μ) (ldAtR S μ) 1 :=
    fa_gx_add_le hσS hAtμ (z := 0) (by simp) (by simp)
  have h3 : gxTh (upsilon μ) (ldAtR S μ) 1 ≤ 1 := cdOtp_le_self _ 1
  exact h2.trans ((add_le_add le_rfl h3).trans (Order.add_one_le_of_lt hlt'))

omit hl hX in
/-- The copy of a source atom. -/
theorem fa_src_img {A : Set Ordinal.{0}} {h : Ordinal.{0} → Ordinal.{0}} (C : FaCov (upsilon l) A h) {Y z : Ordinal.{0}}
    (hsrc : le1 (ω ^ Y) (ω ^ Y + z)) (hvA : ω ^ Y ∈ A) (hzA : z ∈ A) (hvzA : ω ^ Y + z ∈ A) (hzv : z ≤ ω ^ Y)
    (hz0 : z ≠ 0) (h0A : (0 : Ordinal.{0}) ∈ A) (hρv : upsilon l ≤ ω ^ Y) (hU : ¬ UpsPt (h (ω ^ Y))) :
    ∃ a, a ≠ 0 ∧ h (ω ^ Y) = ω ^ a ∧ ω ^ h z ∣ a := by
  have himg : le1 (h (ω ^ Y)) (h (ω ^ Y) + h z) := by
    have := C.cov1 _ hvA _ hvzA hsrc
    rwa [← C.add _ hvA z hzA _ hvzA rfl] at this
  have hfz0 : 0 < h z := lt_of_le_of_lt zero_le (C.mono h0A hzA (pos_iff_ne_zero.2 hz0))
  have hR := (C.sk _ hvA hρv hU _).1 himg
  have hfzv : h z ≤ h (ω ^ Y) := by
    rcases hzv.lt_or_eq with hlt | heq
    · exact (C.mono hzA hvA hlt).le
    · rw [heq]
  obtain ⟨a, ha0, hfa, hza⟩ := (le1R_thm22 hfz0 hfzv).1 hR
  exact ⟨a, ha0, hfa, (le_lg_iff ha0 _).1 hza⟩

/-- **`ω^{a+ω^z}`** (`z > 0`, `ω^z ∣ a`) from `z`, for `a ≠ 0` from `ω^a`, and from the bound at a `υ`-point image. -/
theorem faI_lim (hUp : FaUp (upsilon l) t) (hti : Indec t) {a z : Ordinal.{0}} (haC : GxCl (upsilon l) (ldAtR S l) a)
    (hzC : GxCl (upsilon l) (ldAtR S l) z) (hz0 : z ≠ 0) (hd : ω ^ z ∣ a)
    (hzI : FaI S l t z) (hwI : a ≠ 0 → FaI S l t (ω ^ a)) (hne : a + ω ^ z < ω ^ (a + ω ^ z))
    (hρv0 : upsilon l < gxTh (upsilon l) (ldAtR S l) (ω ^ (a + ω ^ z)))
    (hvt0 : gxTh (upsilon l) (ldAtR S l) (ω ^ (a + ω ^ z)) < t)
    (hbig : FaBig S l t (gxTh (upsilon l) (ldAtR S l) (ω ^ (a + ω ^ z))) (ω ^ (a + ω ^ z))) :
    FaI S l t (ω ^ (a + ω ^ z)) := by
  classical
  obtain ⟨hZ, hZ1⟩ := Vb.vbZ hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hρE : InE (upsilon l) := Low.opow_eq_self_of_SC hZ
  have hzp : GxCl (upsilon l) (ldAtR S l) (ω ^ z) := hzC.opow hZ.1
  have hXc : GxCl (upsilon l) (ldAtR S l) (a + ω ^ z) := GxCl.add haC hzp
  set X' := gxTh (upsilon l) (ldAtR S l) a with hX'def
  set z' := gxTh (upsilon l) (ldAtR S l) z with hz'def
  have eX : gxTh (upsilon l) (ldAtR S l) (a + ω ^ z) = X' + ω ^ z' := by
    rw [gxTh_add hZ hAt haC, gxTh_opow hZ hAt hzC]
  have ev : gxTh (upsilon l) (ldAtR S l) (ω ^ (a + ω ^ z)) = ω ^ (X' + ω ^ z') := by
    rw [gxTh_opow hZ hAt hXc, eX]
  have hz'0 : z' ≠ 0 := by
    have := gxTh_lt (Z := upsilon l) (At := ldAtR S l) (GxCl.zero hZ.1) (pos_iff_ne_zero.2 hz0)
    rw [gxTh_zero] at this
    exact this.ne'
  have hd' : ω ^ z' ∣ X' := fc_dvd hZ hAt hzC a haC hd
  have hX'0 : a ≠ 0 → X' ≠ 0 := fun ha0 => by
    have := gxTh_lt (Z := upsilon l) (At := ldAtR S l) (GxCl.zero hZ.1) (pos_iff_ne_zero.2 ha0)
    rw [gxTh_zero] at this
    exact this.ne'
  set X := X' + ω ^ z' with hXdef
  set v := ω ^ X with hvdef
  have hρv : upsilon l < v := by rw [← ev]; exact hρv0
  have hvt : v < t := by rw [← ev]; exact hvt0
  have hXv : X < v := by
    have := gxTh_lt hXc hne
    rwa [eX, ev] at this
  have hX0 : X ≠ 0 := (lt_of_lt_of_le (opow_pos z' omega0_pos) le_add_self).ne'
  have hlgX : lg X = z' := Ge.lg_add_opow hd'
  have hzX : z' ≤ X := by rw [← hlgX]; exact lg_le hX0
  have hzv : z' < v := lt_of_le_of_lt hzX hXv
  have hvz : v + z' < t := hti.add_lt hvt (hzv.trans hvt)
  have hdX : ω ^ z' ∣ X := by rw [hXdef]; exact dvd_add hd' (dvd_refl _)
  have hnonU : ∀ {Y : Ordinal.{0}}, Y < ω ^ Y → ¬ UpsPt (ω ^ Y) := fun {Y} hY hU => by
    have hE := (inE_opow_iff Y).1 (upsPt_inE hU)
    exact absurd hE.symm hY.ne
  have hsrc : le1 v (v + z') := (hUp.sk v hρv hvt (hnonU hXv) _).2
    ((le1R_thm22 (pos_iff_ne_zero.2 hz'0) hzv.le).2 ⟨X, hX0, rfl, (le_lg_iff hX0 z').2 hdX⟩)
  -- `X' ≥ ρ` when `a ≠ 0`
  have hX'v' : a ≠ 0 → upsilon l ≤ ω ^ X' ∧ z' ≤ ω ^ X' ∧ ω ^ X' < v := by
    intro ha0
    have hX'n := hX'0 ha0
    have hzX' : z' ≤ X' := (le_lg_iff hX'n z').2 hd' |>.trans (lg_le hX'n)
    have hρX' : upsilon l ≤ X' := by
      by_contra hlt
      push Not at hlt
      have hwz : ω ^ z' ≤ X' := Ordinal.le_of_dvd hX'n hd'
      have hXρ : X < upsilon l := (inE_indec hρE).add_lt hlt (hwz.trans_lt hlt)
      have : v < upsilon l := by
        rw [hvdef, ← show ω ^ upsilon l = upsilon l from hρE]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hXρ
      exact absurd hρv (not_lt.2 this.le)
    refine ⟨?_, hzX'.trans (right_le_opow _ one_lt_omega0), ?_⟩
    · rw [← show ω ^ upsilon l = upsilon l from hρE]; exact (opow_le_opow_iff_right one_lt_omega0).2 hρX'
    · exact (opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_of_pos_right X' (opow_pos z' omega0_pos))
  obtain ⟨W3, Z3, w3, m3, b3⟩ := hzI
  replace m3 : z' ∈ W3 ∪ Z3 := m3
  -- the witness sets
  have hwz : ∃ W Z : Finset Ordinal.{0}, WZ (upsilon l) t W Z ∧ (a ≠ 0 → ω ^ X' ∈ W ∪ Z ∧ ω ^ X' + z' ∈ W) ∧
      ∀ (A : Set Ordinal.{0}) (h : Ordinal.{0} → Ordinal.{0}) (μ : Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → FaCov (upsilon l) A h →
        IsRestartIdx μ → h (upsilon l) = upsilon μ →
        a ≠ 0 → ω ^ gxTh (upsilon μ) (ldAtR S μ) a ≤ h (ω ^ X') ∧
          (upsilon l < ω ^ X' → UpsPt (ω ^ X') → UpsPt (h (ω ^ X'))) := by
    by_cases ha0 : a = 0
    · exact ⟨∅, ∅, WZ.empty, fun h' => absurd ha0 h', fun _ _ _ _ _ _ _ _ h' => absurd ha0 h'⟩
    obtain ⟨W5, w5, b5⟩ : ∃ W5 : Finset Ordinal.{0}, WZ (upsilon l) t W5 ∅ ∧ ∀ (A : Set Ordinal.{0})
        (h : Ordinal.{0} → Ordinal.{0}), ↑W5 ⊆ A → ω ^ X' ∈ A → FaCov (upsilon l) A h →
        upsilon l < ω ^ X' → UpsPt (ω ^ X') → UpsPt (h (ω ^ X')) := by
      by_cases hc1 : upsilon l < ω ^ X' ∧ UpsPt (ω ^ X')
      · obtain ⟨W5, w5, b5⟩ := fa_pin_wz hUp hc1.1 ((hX'v' ha0).2.2.trans hvt) hc1.2
        exact ⟨W5, w5, fun A h hW hu C _ _ => b5 A h hW hu C⟩
      · exact ⟨∅, WZ.empty, fun _ _ _ _ _ h1 h2 => absurd ⟨h1, h2⟩ hc1⟩
    obtain ⟨W2, Z2, w2, m2, b2⟩ := hwI ha0
    have ew : gxTh (upsilon l) (ldAtR S l) (ω ^ a) = ω ^ X' := gxTh_opow hZ hAt haC
    rw [ew] at m2
    obtain ⟨hρv', hzv', hv'v⟩ := hX'v' ha0
    have hv't : ω ^ X' < t := hv'v.trans hvt
    have hm3 : z' ∈ W2 ∪ W3 ∪ (Z2 ∪ Z3) := by
      rcases Finset.mem_union.1 m3 with hm | hm <;> simp [hm]
    have hm2 : ω ^ X' ∈ W2 ∪ W3 ∪ (Z2 ∪ Z3) := by
      rcases Finset.mem_union.1 m2 with hm | hm <;> simp [hm]
    have hpos : ω ^ X' < ω ^ X' + z' := lt_add_of_pos_right _ (pos_iff_ne_zero.2 hz'0)
    have w6 := ((w2.union w3).union w5)
    have hm3' : z' ∈ W2 ∪ W3 ∪ W5 ∪ (Z2 ∪ Z3 ∪ ∅) := by
      rcases Finset.mem_union.1 m3 with hm | hm <;> simp [hm]
    have hm2' : ω ^ X' ∈ W2 ∪ W3 ∪ W5 ∪ (Z2 ∪ Z3 ∪ ∅) := by
      rcases Finset.mem_union.1 m2 with hm | hm <;> simp [hm]
    refine ⟨insert (ω ^ X' + z') (W2 ∪ W3 ∪ W5), Z2 ∪ Z3 ∪ ∅,
      w6.insW (hρv'.trans le_self_add) (hti.add_lt hv't (hzv.trans hvt))
        (Or.inr ⟨ω ^ X', hm2', z', hm3', hpos, lt_of_le_of_lt hzv' hpos, rfl⟩),
      fun _ => ⟨by
        rcases Finset.mem_union.1 m2 with hm | hm <;> simp [hm], by simp⟩, ?_⟩
    intro A h μ hW hZ' C hμ he _
    have hW2 : ↑W2 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hZ2 : ↑Z2 ⊆ A := fun x hx => hZ' (by simp [Finset.mem_coe.1 hx])
    have hW5 : ↑W5 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have p2 := b2 A h μ hW2 hZ2 C hμ he
    obtain ⟨-, hσS, -, hAtμ, -⟩ := fa_mu hl hX C hμ he
    have hvA' : ω ^ X' ∈ A := by
      rw [ew] at p2
      have := mem_A m2 hW2 hZ2
      exact this
    refine ⟨?_, fun h1 h2 => b5 A h hW5 hvA' C h1 h2⟩
    rwa [ew, fa_gx_opow hσS hAtμ] at p2
  obtain ⟨W0, Z0, w0, hm0, b0⟩ := hwz
  obtain ⟨W4, Z4, w4, b4⟩ := hbig
  have hzvz : z' < v + z' := lt_of_lt_of_le hzv le_self_add
  have hvvz : v < v + z' := lt_add_of_pos_right v (pos_iff_ne_zero.2 hz'0)
  have wb : WZ (upsilon l) t (W0 ∪ W3 ∪ W4) (insert 0 (Z0 ∪ Z3 ∪ Z4)) := ((w0.union w3).union w4).insZ hρE.pos
  refine ⟨_, _, (wb.insW hρv.le hvt (Or.inl (indec_opow _))).insW (hρv.le.trans le_self_add) hvz
      (Or.inr ⟨v, by simp, z', by
        rcases Finset.mem_union.1 m3 with hm | hm <;> simp [hm], hvvz, hzvz, rfl⟩),
    by rw [ev]; simp, fun A h μ hW hZ' C hμ he => ?_⟩
  -- the copy
  have hsub : ∀ x, x ∈ W0 ∨ x ∈ W3 ∨ x ∈ W4 → x ∈ (A : Set Ordinal.{0}) := fun x hx => hW (by
    rcases hx with hx | hx | hx <;> simp [hx])
  have hsubZ : ∀ x, x ∈ Z0 ∨ x ∈ Z3 ∨ x ∈ Z4 ∨ x = 0 → x ∈ A := fun x hx => hZ' (by
    rcases hx with hx | hx | hx | hx <;> simp [hx])
  have hW0 : ↑W0 ⊆ A := fun x hx => hsub x (Or.inl (Finset.mem_coe.1 hx))
  have hW3 : ↑W3 ⊆ A := fun x hx => hsub x (Or.inr (Or.inl (Finset.mem_coe.1 hx)))
  have hW4 : ↑W4 ⊆ A := fun x hx => hsub x (Or.inr (Or.inr (Finset.mem_coe.1 hx)))
  have hZ0 : ↑Z0 ⊆ A := fun x hx => hsubZ x (Or.inl (Finset.mem_coe.1 hx))
  have hZ3 : ↑Z3 ⊆ A := fun x hx => hsubZ x (Or.inr (Or.inl (Finset.mem_coe.1 hx)))
  have hZ4 : ↑Z4 ⊆ A := fun x hx => hsubZ x (Or.inr (Or.inr (Or.inl (Finset.mem_coe.1 hx))))
  have h0A : (0 : Ordinal.{0}) ∈ A := hsubZ 0 (Or.inr (Or.inr (Or.inr rfl)))
  have hvA : v ∈ A := hW (by simp)
  have hvzA : v + z' ∈ A := hW (by simp)
  have hzA : z' ∈ A := mem_A m3 hW3 hZ3
  have pz := b3 A h μ hW3 hZ3 C hμ he
  obtain ⟨hσρ, hσS, hσ1, hAtμ, hσU⟩ := fa_mu hl hX C hμ he
  have hσE : InE (upsilon μ) := upsPt_inE hσU
  rw [ev]
  by_cases hU : UpsPt (h v)
  · have := b4 A h μ hW4 hZ4 C hμ he (by rw [ev]; exact hvA) (by rw [ev]; exact hU)
    rwa [ev] at this
  have e1 : gxTh (upsilon μ) (ldAtR S μ) (ω ^ (a + ω ^ z)) ≤
      ω ^ (gxTh (upsilon μ) (ldAtR S μ) a + ω ^ gxTh (upsilon μ) (ldAtR S μ) z) := by
    rw [fa_gx_opow hσS hAtμ]
    refine opow_le_opow_right omega0_pos ?_
    have := fa_gx_add_le hσS hAtμ hd le_rfl
    rwa [fa_gx_opow hσS hAtμ z] at this
  refine e1.trans ?_
  obtain ⟨a0, ha0, hfa, hdiv⟩ := fa_src_img C hsrc hvA hzA hvzA hzv.le hz'0 h0A hρv.le hU
  rw [hfa]
  refine (opow_le_opow_iff_right one_lt_omega0).2 ?_
  have hπz : ω ^ gxTh (upsilon μ) (ldAtR S μ) z ≤ ω ^ h z' := (opow_le_opow_iff_right one_lt_omega0).2 pz
  by_cases haz : a = 0
  · rw [haz, gxTh_zero, zero_add]
    exact hπz.trans (Ordinal.le_of_dvd ha0 hdiv)
  obtain ⟨hm2, hm2'⟩ := hm0 haz
  obtain ⟨hρv', hzv', hv'v⟩ := hX'v' haz
  have hv'A : ω ^ X' ∈ A := mem_A hm2 hW0 hZ0
  have hv'zA : ω ^ X' + z' ∈ A := hW0 (Finset.mem_coe.2 hm2')
  obtain ⟨p2, hpinX⟩ := b0 A h μ hW0 hZ0 C hμ he haz
  obtain ⟨c, hc⟩ := indec_eq_opow (C.indec _ hv'A (indec_opow _))
  have hbc : gxTh (upsilon μ) (ldAtR S μ) a ≤ c := by
    rw [hc] at p2; exact (opow_le_opow_iff_right one_lt_omega0).1 p2
  have hca : c < a0 := by
    have := C.mono hv'A hvA hv'v
    rw [hc, hfa] at this; exact (opow_lt_opow_iff_right one_lt_omega0).1 this
  have hX'n := hX'0 haz
  have hcdiv : ω ^ h z' ∣ c ∨ (InE c ∧ c < ω ^ h z') := by
    by_cases hU' : UpsPt (h (ω ^ X'))
    · have hcE : InE c := by
        have := upsPt_inE hU'
        rw [hc] at this
        exact (inE_opow_iff c).1 this
      rcases le_or_gt (h z') c with hzc | hcz
      · exact Or.inl (opow_dvd_of_inE hcE hzc)
      · exact Or.inr ⟨hcE, by
          rw [← show ω ^ c = c from hcE]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hcz⟩
    · have hρv'' : upsilon l < ω ^ X' := by
        rcases hρv'.lt_or_eq with hlt | heq
        · exact hlt
        · exfalso; rw [← heq, he] at hU'; exact hU' hσU
      have hVn : ¬ UpsPt (ω ^ X') := fun hV => hU' (hpinX hρv'' hV)
      have hsrc' : le1 (ω ^ X') (ω ^ X' + z') :=
        (hUp.sk _ hρv'' (hv'v.trans hvt) hVn _).2
          ((le1R_thm22 (pos_iff_ne_zero.2 hz'0) hzv').2 ⟨X', hX'n, rfl, (le_lg_iff hX'n z').2 hd'⟩)
      obtain ⟨c', -, hfc', hdc'⟩ := fa_src_img C hsrc' hv'A hzA hv'zA hzv' hz'0 h0A hρv' hU'
      have hcc : c' = c := opow_inj (hfc'.symm.trans hc)
      exact Or.inl (hcc ▸ hdc')
  rcases hcdiv with hcd | ⟨hcE, hcz⟩
  · calc gxTh (upsilon μ) (ldAtR S μ) a + ω ^ gxTh (upsilon μ) (ldAtR S μ) z ≤ c + ω ^ h z' := add_le_add hbc hπz
      _ ≤ a0 := dvd_next hdiv hcd hca
  · calc gxTh (upsilon μ) (ldAtR S μ) a + ω ^ gxTh (upsilon μ) (ldAtR S μ) z ≤ c + ω ^ h z' := add_le_add hbc hπz
      _ = ω ^ h z' := add_of_omega0_opow_le (by rw [← show ω ^ c = c from hcE] at hcz ⊢; exact hcz) le_rfl
      _ ≤ a0 := Ordinal.le_of_dvd ha0 hdiv

omit hl hX in
/-- Witness sets for finitely many codes. -/
theorem faI_fin : ∀ s : Finset Ordinal.{0}, (∀ c ∈ s, FaI S l t c) →
    ∃ W Z : Finset Ordinal.{0}, WZ (upsilon l) t W Z ∧ ∀ (A : Set Ordinal.{0}) (h : Ordinal.{0} → Ordinal.{0}) (μ : Ordinal.{0}),
      ↑W ⊆ A → ↑Z ⊆ A → FaCov (upsilon l) A h → IsRestartIdx μ → h (upsilon l) = upsilon μ →
      ∀ c ∈ s, gxTh (upsilon l) (ldAtR S l) c ∈ A ∧ gxTh (upsilon μ) (ldAtR S μ) c ≤ h (gxTh (upsilon l) (ldAtR S l) c) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => exact fun _ => ⟨∅, ∅, WZ.empty, fun _ _ _ _ _ _ _ _ x hx => absurd hx (Finset.notMem_empty x)⟩
  | @insert a s _ IH =>
    intro hs
    obtain ⟨W, Z, w, b⟩ := IH fun x hx => hs x (Finset.mem_insert_of_mem hx)
    obtain ⟨Wa, Za, wa, ma, ba⟩ := hs a (Finset.mem_insert_self a s)
    refine ⟨W ∪ Wa, Z ∪ Za, w.union wa, fun A h μ hW hZ C hμ he x hx => ?_⟩
    have hW1 : ↑W ⊆ A := fun y hy => hW (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 hy)))
    have hZ1 : ↑Z ⊆ A := fun y hy => hZ (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 hy)))
    have hW2 : ↑Wa ⊆ A := fun y hy => hW (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_coe.1 hy)))
    have hZ2 : ↑Za ⊆ A := fun y hy => hZ (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_coe.1 hy)))
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact ⟨mem_A ma hW2 hZ2, ba A h μ hW2 hZ2 C hμ he⟩
    · exact b A h μ hW1 hZ1 C hμ he x hx

end Arith

end Googology.Trans.PoR.InaccPsi.R2.Fa

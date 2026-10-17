import Googology.Trans.PoR.InaccPsi.R2.CdNu

/-!
# The CROSS-LIM relations from the base changes: `L(ω) ≤₁ L(ω+1)`, (CL), CROSS, (C1)

`L(ξ) = ψ_{Ω₁}(Ω_ω·2 + P'·ξ)` (`Nc.ncL`), `P' = ψ_{Ω₂}(Ω_ω·2)` (`Nc.ncPp`), `c_n = L(n+1)`
(`Bc.bcC`), `B_n = Bc.bcB S n` (the η-base change `L(n+1) ↦ L(ω)` on `[0, L(n+2))`).
`T` denotes the relation `L(ω) ≤₁ L(ω+1)`.

* `cxLe1_of_cof` (**closure of the `≤₁`-predecessors**): `0 < a ≤ Y` and cofinally many `α < a` with
  `α ≤₁ Y` give `a ≤₁ Y`;
* `cxShift_le1` (**the first clause of SHIFT without (C1)**): a monotone sequence `c` cofinal in `a`,
  maps `B_n` on `[0, c_{n+1})` that are strictly increasing, keep and reflect `+`, `≤₁`, `≤₂`, fix
  `[0, c_n)`, and ONTO-FIN give `a ≤₁ b` (pull every finite `Y ⊆ [a, b)` back by `B_n`);
* `cxT` (**`T` from (TC) and (EMB₂)**, no (C1)): `L(ω) ≤₁ L(ω+1)`;
* `cxTCAt_L_iff`: given `T`, the (TC) clause of `R2.BcName` at the named point `x = L(n+1)` holds iff
  `L(n+1) ≤₁ L(n+2)`;
* `cxCL_of_T`, `cxCL` (**(CL) from (TC) and (EMB₂)**): `L(n+1) ≤₁ L(n+2)` for every `n`;
* `cxCROSS_of_CL`, `cxCROSS_iff`: the crossing step `CdCROSS` is equivalent to (CL);
  `cxC1`: (C1) `L(n+2) ≤₁ L(ω)` and `L(1) ≤₁ L(2)` from (TC) and (EMB₂);
* `cxT_of_lower`, `cxCL_of_lower`: `T` from LOWER at the restart `L(ω)` with `L(ω+1) ≤ r(λ)`, and (CL)
  from LOWER at the restarts `L(n+1)` with `L(n+2) ≤ r(λ)` (the reaches at named restarts);
  `cxCROSS_of_read`: the crossing step from LOWER at codes `c''` of the restart `L(n+1)` whose reading
  `Θ_λ(c'')` lies above the target (`k_λ(p) ≥ p`, `cxk_ge_self`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Cx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cd

/-- **Closure of the `≤₁`-predecessors**: if `0 < a ≤ Y` and cofinally many `α < a` have `α ≤₁ Y`,
then `a ≤₁ Y`. -/
theorem cxLe1_of_cof {a Y : Ordinal.{0}} (ha0 : 0 < a) (haY : a ≤ Y)
    (h : ∀ g < a, ∃ α, g < α ∧ α < a ∧ le1 α Y) : le1 a Y := by
  classical
  refine le1_iff.2 ⟨haY, fun X Z hX hZ hXZ => ?_⟩
  obtain ⟨g, hga, hXg⟩ : ∃ g < a, ∀ x ∈ X, x ≤ g := by
    rcases X.eq_empty_or_nonempty with he | hne
    · exact ⟨0, ha0, by simp [he]⟩
    · exact ⟨X.max' hne, hX _ (X.max'_mem hne), fun x hx => X.le_max' x hx⟩
  obtain ⟨α, hgα, hαa, hαY⟩ := h g hga
  obtain ⟨Yt, h1, h2, h3, f, hf⟩ := (le1_iff.1 hαY).2 X Z
    (fun x hx => (hXg x hx).trans_lt hgα)
    (fun z hz => ⟨hαa.le.trans (hZ z hz).1, (hZ z hz).2⟩) hXZ
  exact ⟨Yt, fun y hy => (h1 y hy).trans hαa, h2, h3, f, hf⟩

/-- **The first clause of SHIFT, without (C1)**: the data of SHIFT other than (C1), the bound and the
closed range give `a ≤₁ b`. -/
theorem cxShift_le1 {a b : Ordinal.{0}} {c : ℕ → Ordinal.{0}} {B : ℕ → Ordinal.{0} → Ordinal.{0}}
    (hmono : Monotone c) (hca : ∀ n, c n < a) (hcof : ∀ γ < a, ∃ n, γ < c n) (hab : a ≤ b)
    (hBm : ∀ n, StrictMonoOn (B n) (Set.Iio (c (n + 1))))
    (hBadd : ∀ n, ∀ x < c (n + 1), ∀ y < c (n + 1), ∀ z < c (n + 1),
      (x + y = z ↔ B n x + B n y = B n z))
    (hB1 : ∀ n, ∀ x < c (n + 1), ∀ y < c (n + 1), (le1 x y ↔ le1 (B n x) (B n y)))
    (hB2 : ∀ n, ∀ x < c (n + 1), ∀ y < c (n + 1), (le2 x y ↔ le2 (B n x) (B n y)))
    (hfix : ∀ n, ∀ x < c n, B n x = x)
    (honto : ∀ Y : Finset Ordinal.{0}, (∀ y ∈ Y, a ≤ y ∧ y < b) → ∀ N, ∃ n, N ≤ n ∧
      ∀ y ∈ Y, ∃ y' < c (n + 1), B n y' = y) :
    le1 a b := by
  classical
  refine le1_iff.2 ⟨hab, fun X Y hX hY hXY => ?_⟩
  obtain ⟨N, hN⟩ := Qq.qqFin_below hmono hcof X hX
  obtain ⟨n, hNn, hYn⟩ := honto Y hY N
  set d := c (n + 1) with hd
  have hcn : c n ≤ d := hmono (Nat.le_succ n)
  have hda : d < a := hca (n + 1)
  let g : Ordinal.{0} → Ordinal.{0} := fun y =>
    if hy : ∃ y' < d, B n y' = y then Classical.choose hy else 0
  have hg : ∀ y ∈ Y, g y < d ∧ B n (g y) = y := by
    intro y hy
    have hex : ∃ y' < d, B n y' = y := hYn y hy
    have hsp := Classical.choose_spec hex
    simp only [g, dif_pos hex]
    exact hsp
  let h : Ordinal.{0} → Ordinal.{0} := fun z => if z < a then z else g z
  have hXa : ∀ x ∈ X, x < c n := fun x hx => (hN x hx).trans_le (hmono hNn)
  have hhX : ∀ x ∈ X, h x = x := fun x hx => by simp only [h, if_pos (hX x hx)]
  have hhY : ∀ y ∈ Y, h y = g y := fun y hy => by
    simp only [h, if_neg (not_lt.2 (hY y hy).1)]
  have hA : ∀ u ∈ (↑(X ∪ Y) : Set Ordinal.{0}), h u < d ∧ B n (h u) = u := by
    intro u hu
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hu) with hu | hu
    · rw [hhX u hu]; exact ⟨(hXa u hu).trans_le hcn, hfix n u (hXa u hu)⟩
    · rw [hhY u hu]; exact hg u hu
  have hgc : ∀ y ∈ Y, c n ≤ g y := by
    intro y hy
    by_contra hlt
    rw [not_le] at hlt
    have e := hfix n (g y) hlt
    rw [(hg y hy).2] at e
    exact absurd (e ▸ hlt.trans (hca n)) (not_lt.2 (hY y hy).1)
  have himg := Qq.qqImage_fix (Y := Y) hhX
  refine ⟨Y.image h, ?_, ?_, ?_, h, ?_⟩
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
    rw [hhY y hy]; exact (hg y hy).1.trans hda
  · intro x hx z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
    rw [hhY y hy]; exact (hXa x hx).trans_le (hgc y hy)
  · rw [himg]; exact Qq.qqInv_closed (hBm n) (hBadd n) hA hXY
  · rw [himg]; exact Qq.qqInv_cov (hBm n) (hBadd n) (hB1 n) (hB2 n) hA

variable {S : InaccSeq.{0}}

/-- `T`: the relation `L(ω) ≤₁ L(ω+1)`. -/
def CxT (S : InaccSeq.{0}) : Prop := le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1))

theorem cxB_base (n : ℕ) : Bc.bcB S n (Bc.bcC S n) = Nc.ncL S ω := Bc.bcB_base (S := S) n

theorem cxC_lt (n : ℕ) : Bc.bcC S n < Bc.bcC S (n + 1) := Pp.ppL_lt_succ n

theorem cxC_lt_L1 (n : ℕ) : Bc.bcC S (n + 1) < Nc.ncL S (ω + 1) :=
  (Bc.bcC_lt S (n + 1)).trans (Qq.qqL_lt_succ S)

theorem cxC_lim (n : ℕ) : IsSuccLimit (Bc.bcC S n) := (Lw.lw_L_SC S _).isSuccLimit

/-- `B_n` maps `[L(n+1), L(n+2))` into `[L(ω), L(ω+1))`. -/
theorem cxB_window {n : ℕ} {z : Ordinal.{0}} (h1 : Bc.bcC S n ≤ z) (h2 : z < Bc.bcC S (n + 1)) :
    Nc.ncL S ω ≤ Bc.bcB S n z ∧ Bc.bcB S n z < Nc.ncL S (ω + 1) := by
  refine ⟨?_, Bc.bcB_bound' S n z h2⟩
  rw [← cxB_base (S := S) n]
  exact (Bc.bcB_mono' S n).monotoneOn (cxC_lt n) h2 h1

/-- **`T` from (TC) and (EMB₂)** (no (C1)): `L(ω) ≤₁ L(ω+1)`. -/
theorem cxT (hTC : CdTC S) (hB2 : CdEMB2 S) : CxT S :=
  cxShift_le1 (Bc.bcC_mono S) (Bc.bcC_lt S) (Bc.bcC_cof S) (Qq.qqL_lt_succ S).le
    (Bc.bcB_mono' S) (Bc.bcB_addIff' S) (Bc.bcB1 S hTC) hB2 (Bc.bcB_fix' S) (Bc.bcOnto' S)

/-- **(TC) at the named point `L(n+1)`, given `T`**: the (TC) clause at `x = L(n+1)` holds iff
`L(n+1) ≤₁ L(n+2)`. -/
theorem cxTCAt_L_iff (hT : CxT S) (n : ℕ) :
    CdTCAt S n (Bc.bcC S n) ↔ le1 (Bc.bcC S n) (Bc.bcC S (n + 1)) := by
  constructor
  · rintro (⟨r, hr, -, hBr⟩ | hall)
    · exfalso
      rw [cxB_base] at hBr
      exact absurd (Bc.bcB_bound' S n r hr) (not_lt.2 (hBr.2 _ hT))
    · exact le1_limit (cxC_lim (n + 1)) (cxC_lt n) fun z h1 h2 => (hall z h1 h2).1
  · intro h
    refine Or.inr fun z h1 h2 => ⟨le1_of_le_of_le1 h1 h2.le h, ?_⟩
    rw [cxB_base]
    obtain ⟨hz1, hz2⟩ := cxB_window (S := S) h1 h2
    exact le1_of_le_of_le1 hz1 hz2.le hT

/-- **(CL) from (TC) and `T`.** -/
theorem cxCL_of_T (hTC : CdTC S) (hT : CxT S) : CdCL S := fun n =>
  (cxTCAt_L_iff hT n).1 (hTC n _ (cxC_lt n))

/-- **(CL) from (TC) and (EMB₂).** -/
theorem cxCL (hTC : CdTC S) (hB2 : CdEMB2 S) : CdCL S := cxCL_of_T hTC (cxT hTC hB2)

/-- **The crossing step from (CL)** (with `c' = c`; `P(Ω_ω + P'·(n+1) + c) ≤ L(n+2)`). -/
theorem cxCROSS_of_CL (hC : CdCL S) : CdCROSS S := by
  intro n c hc
  refine ⟨c, le_rfl, hc, le1_of_le_of_le1 ?_ ?_ (hC n)⟩
  · rw [Lw.lw_L_eq S]; exact Pv_mono le_self_add
  · have e : ((n + 2 : ℕ) : Ordinal.{0}) = ((n + 1 : ℕ) : Ordinal.{0}) + 1 := Nat.cast_succ (n + 1)
    rw [e, Pp.ppL_succ_eq]
    exact Pv_mono (add_le_add_right hc.le _)

/-- **The crossing step is equivalent to (CL).** -/
theorem cxCROSS_iff : CdCROSS S ↔ CdCL S := ⟨cdCL_of_cross, cxCROSS_of_CL⟩

/-- **(C1) and `L(1) ≤₁ L(2)` from (TC) and (EMB₂).** -/
theorem cxC1 (hTC : CdTC S) (hB2 : CdEMB2 S) :
    CdC1 S ∧ le1 (Nc.ncL S ((1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((2 : ℕ) : Ordinal.{0})) :=
  ⟨cdC1_of_CL (cxCL hTC hB2), cdL12_of_CL (cxCL hTC hB2)⟩

/-- **`T` from LOWER at the restart `L(ω)`**, when its predicted value is at least `L(ω+1)` (`L(ω)` lies
outside the range of ENUM-REACH, code `P'+1`; the hypothesis can hold only if `r(λ) ≤ L(ω+1)` as well,
since (Q) excludes `L(ω) ≤₁ L(ω+1)+1`). -/
theorem cxT_of_lower {l : Ordinal.{0}} (hl : upsilon l = Nc.ncL S ω) (hL : CdLower S l)
    (hr : Nc.ncL S (ω + 1) ≤ cdR S l) : CxT S := by
  have h : le1 (upsilon l) (cdR S l) := hL
  rw [hl] at h
  exact le1_of_le_of_le1 (Pp.ppL_mono le_self_add) hr h

/-- **(CL) from LOWER at the restarts `L(n+1)`**, when their predicted values are at least `L(n+2)`. -/
theorem cxCL_of_lower
    (h : ∀ n : ℕ, ∃ l, upsilon l = Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ∧ CdLower S l ∧
      Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) ≤ cdR S l) : CdCL S := by
  intro n
  obtain ⟨l, hl, hL, hr⟩ := h n
  have h1 : le1 (upsilon l) (cdR S l) := hL
  rw [hl] at h1
  exact le1_of_le_of_le1 (Pp.ppL_lt_succ (S := S) n).le hr h1

/-- `k_λ(p) ≥ p`. -/
theorem cxk_ge_self (l p : Ordinal.{0}) : p ≤ cdk l p := (cdk_strictMono l).le_apply

/-- **The crossing step from LOWER at codes of the restart `L(n+1)`**: if for every `c < P'` there are
`c' ∈ [c, P')` and a code `c''` with `ρ_λ ≤₁ k_λ(Θ_λ(c''))` and `P(Ω_ω + P'·(n+1) + c') ≤ Θ_λ(c'')`,
then CROSS holds (and so (CL)). -/
theorem cxCROSS_of_read
    (h : ∀ n : ℕ, ∃ l, upsilon l = Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ∧
      ∀ c < Nc.ncPp S, ∃ c', c ≤ c' ∧ c' < Nc.ncPp S ∧ ∃ c'', le1 (upsilon l) (cdRc S l c'') ∧
        Pv S (Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) + c') ≤ cdTheta S l c'') :
    CdCROSS S := by
  intro n c hc
  obtain ⟨l, hl, hl'⟩ := h n
  obtain ⟨c', hcc', hc'P, c'', hle, hθ⟩ := hl' c hc
  refine ⟨c', hcc', hc'P, ?_⟩
  rw [hl] at hle
  refine le1_of_le_of_le1 ?_ (hθ.trans (cxk_ge_self _ _)) hle
  rw [Lw.lw_L_eq S]; exact Pv_mono le_self_add

end Googology.Trans.PoR.InaccPsi.R2.Cx

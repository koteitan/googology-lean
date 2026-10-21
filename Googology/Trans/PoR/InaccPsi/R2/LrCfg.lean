import Googology.Trans.PoR.InaccPsi.R2.LcRoad

/-!
# Realizer maps for one configuration at a time

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.

`Rl.RlReal` asks that every map `D_i` keep `+` on the infinite set `[0, c_i) ∪ E_i`.  The proof of
the copying principle (`Rl.rlLe1_of_maps`) only reads `+`, the order and the relations on the finite
configuration `X ∪ Y` itself; that is all [C09] Def 5.3–5.4 asks of a copy.  Here a realizer is a map
for one configuration, with every clause stated on `X ∪ Y` only:

* `LrMap S a X Y D μ` (**a realizer map for the configuration `X ∪ Y`**, `X < a ≤ Y`): `D` fixes `X`, is
  increasing on `X ∪ Y`, keeps and reflects the graph of `+` on `X ∪ Y`, keeps indecomposability on `Y`,
  sends `Y` into `(X, a)`, `μ` is a restart of the Range with `D(a) = ρ_μ` (when `a ∈ Y`), `D ≤ r(μ)` on
  `Y`, and `D` keeps `≤₁`, `≤₂` on the pairs `a < y < y'` of `Y`;
* `LrReal S a b`: every finite closed configuration `X ∪ Y` (`X < a ≤ Y < b`) has a realizer map;
  `lrReal_of_rl` (**`Rl.RlReal → LrReal`**, so `LrReal` is weaker), `lrReal_mono`;
* `lrLe1_of_real` (**LOWER, `CvNoPair a b` and `LrReal S a b` give `a ≤₁ b`**), `LrRealCof`,
  `lrLe1_of_realCof`;
* `lrNamed_of_real` (`Cx.CxNamed` from realizers at `m*`, `L(n+1)`, `L(ω)`), `lrRoad_rz` (**the road
  `Cx.cxRoad_rz` with `CxNamed` replaced by these realizers**); `lrRoad_hyp_of_rl`: the hypotheses of
  `Rl.rlRoad_rz` give those of `lrRoad_rz`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lr

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rl
  Googology.Trans.PoR.InaccPsi.R2.Cx Googology.Trans.PoR.InaccPsi.R2.Cv

/-- **A realizer map for one configuration** `X ∪ Y` (`X < a ≤ Y`). -/
structure LrMap (S : InaccSeq.{0}) (a : Ordinal.{0}) (X Y : Finset Ordinal.{0})
    (D : Ordinal.{0} → Ordinal.{0}) (μ : Ordinal.{0}) : Prop where
  fix : ∀ x ∈ X, D x = x
  mono : StrictMonoOn D ↑(X ∪ Y)
  add : ∀ x ∈ X ∪ Y, ∀ y ∈ X ∪ Y, ∀ z ∈ X ∪ Y, (x + y = z ↔ D x + D y = D z)
  indec : ∀ y ∈ Y, Indec y → Indec (D y)
  above : ∀ y ∈ Y, ∀ x ∈ X, x < D y
  below : ∀ y ∈ Y, D y < a
  rng : CdRange S μ
  base : a ∈ Y → D a = upsilon μ
  bd : ∀ y ∈ Y, D y ≤ cdR S μ
  pair1 : ∀ y ∈ Y, ∀ y' ∈ Y, a < y → y < y' → le1 y y' → le1 (D y) (D y')
  pair2 : ∀ y ∈ Y, ∀ y' ∈ Y, a < y → y < y' → le2 y y' → le2 (D y) (D y')

/-- **Realizer maps, one configuration at a time**, for `a ≤₁ b`. -/
def LrReal (S : InaccSeq.{0}) (a b : Ordinal.{0}) : Prop :=
  ∀ X Y : Finset Ordinal.{0}, (∀ x ∈ X, x < a) → (∀ y ∈ Y, a ≤ y ∧ y < b) → Closed ↑(X ∪ Y) →
    ∃ D μ, LrMap S a X Y D μ

variable {S : InaccSeq.{0}}

theorem lrReal_mono {a b b' : Ordinal.{0}} (h : LrReal S a b) (hb : b' ≤ b) : LrReal S a b' :=
  fun X Y hX hY hXY => h X Y hX (fun y hy => ⟨(hY y hy).1, lt_of_lt_of_le (hY y hy).2 hb⟩) hXY

/-- **`RlReal` gives `LrReal`.** -/
theorem lrReal_of_rl {a b : Ordinal.{0}} (h : RlReal S a b) : LrReal S a b := by
  obtain ⟨ι, c, E, D, μ, hca, hE, hex, hDm, hDadd, hDdec, hDfix, hDwin, hDμ, hin⟩ := h
  intro X Y hX hY hXY
  obtain ⟨i, hXi, hYi⟩ := hex X Y hX hY hXY
  have hW : ∀ u ∈ X ∪ Y, u ∈ RlDom (c i) (E i) := by
    intro u hu
    rcases Finset.mem_union.1 hu with hu | hu
    · exact Or.inl (hXi u hu)
    · exact Or.inr (hYi u hu)
  refine ⟨D i, μ i, ⟨fun x hx => hDfix i x (hXi x hx), ?_, ?_, ?_, ?_, ?_, (hDμ i).1,
    fun haY => (hDμ i).2.1 (hYi a haY), fun y hy => (hDμ i).2.2 y (hYi y hy), ?_, ?_⟩⟩
  · intro u hu v hv huv
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hu) with hu | hu <;>
      rcases Finset.mem_union.1 (Finset.mem_coe.1 hv) with hv | hv
    · rw [hDfix i u (hXi u hu), hDfix i v (hXi v hv)]; exact huv
    · rw [hDfix i u (hXi u hu)]; exact (hXi u hu).trans_le (hDwin i v (hYi v hv)).1
    · exact absurd (huv.trans (hX v hv)) (not_lt.2 (hY u hu).1)
    · exact hDm i (hYi u hu) (hYi v hv) huv
  · intro x hx y hy z hz
    exact hDadd i x (hW x hx) y (hW y hy) z (hW z hz)
  · intro y hy hI hD
    exact hI (hDdec i y (hYi y hy) hD)
  · intro y hy x hx
    exact (hXi x hx).trans_le (hDwin i y (hYi y hy)).1
  · intro y hy
    exact (hDwin i y (hYi y hy)).2
  · intro y hy y' hy' hay hyy
    exact (hin i y (hYi y hy) y' (hYi y' hy') hay hyy).1
  · intro y hy y' hy' hay hyy
    exact (hin i y (hYi y hy) y' (hYi y' hy') hay hyy).2

/-- **`a ≤₁ b` from realizer maps for each configuration**, LOWER and `CvNoPair a b`. -/
theorem lrLe1_of_real (hL : CdLOWER S) {a b : Ordinal.{0}} (hab : a ≤ b) (hP : CvNoPair a b)
    (hR : LrReal S a b) : le1 a b := by
  classical
  refine le1_iff.2 ⟨hab, fun X Y hX hY hXY => ?_⟩
  obtain ⟨D, μ, hD⟩ := hR X Y hX hY hXY
  have himg := Qq.qqImage_fix (Y := Y) hD.fix
  have hiso : ArithIso ↑(X ∪ Y) (D '' ↑(X ∪ Y)) D :=
    ⟨hD.mono.injOn.bijOn_image, hD.mono, fun x hx y hy z hz => hD.add x hx y hy z hz⟩
  have hcl : Closed (D '' ↑(X ∪ Y)) := by
    rintro z ⟨s, hs, rfl⟩ hdz
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hs) with hsX | hsY
    · rw [hD.fix s hsX] at hdz ⊢
      rcases hXY s hs hdz with h0 | ⟨p, hp, q, hq, hps, hqs, hpq⟩
      · exact Or.inl h0
      · have hlow : ∀ u ∈ (↑(X ∪ Y) : Set Ordinal.{0}), u < s → u ∈ X := by
          intro u hu hus
          rcases Finset.mem_union.1 (Finset.mem_coe.1 hu) with hu | hu
          · exact hu
          · exact absurd (hus.trans (hX s hsX)) (not_lt.2 (hY u hu).1)
        exact Or.inr ⟨p, ⟨p, hp, hD.fix p (hlow p hp hps)⟩, q, ⟨q, hq, hD.fix q (hlow q hq hqs)⟩,
          hps, hqs, hpq⟩
    · have hdec : DecompR0 s := by
        by_contra hnd
        exact hD.indec s hsY hnd hdz
      have ha0 : (0 : Ordinal.{0}) < a := lt_of_le_of_lt zero_le (hD.below s hsY)
      rcases hXY s hs hdec with h0 | ⟨p, hp, q, hq, hps, hqs, hpq⟩
      · exact absurd (h0 ▸ (hY s hsY).1) (not_le.2 ha0)
      · exact Or.inr ⟨D p, ⟨p, hp, rfl⟩, D q, ⟨q, hq, rfl⟩, hD.mono hp hs hps, hD.mono hq hs hqs,
          (hD.add p hp q hq s hs).1 hpq⟩
  have hYt : ∀ y ∈ Y.image D, y < a := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
    exact hD.below y hy
  have hXYt : ∀ x ∈ X, ∀ y ∈ Y.image D, x < y := by
    intro x hx z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
    exact hD.above y hy x hx
  refine ⟨Y.image D, hYt, hXYt, by rw [himg]; exact hcl, D, ?_⟩
  rw [← himg] at hiso
  have hYmem : ∀ y ∈ Y, y ∈ (↑(X ∪ Y) : Set Ordinal.{0}) := fun y hy =>
    Finset.mem_coe.2 (Finset.mem_union_right _ hy)
  refine cvCov_inner hX (fun y hy => (hY y hy).1) hYt hXYt hiso ?_ ?_ ?_
  · intro y hy y' hy' h1
    rcases lt_trichotomy y y' with hlt | rfl | hgt
    · rcases eq_or_lt_of_le (hY y hy).1 with hya | hay
      · subst hya
        have hlow : le1 (upsilon μ) (cdR S μ) := hL _ hD.rng
        have hmono : D a < D y' := hD.mono (hYmem a hy) (hYmem y' hy') hlt
        rw [hD.base hy] at hmono ⊢
        exact le1_of_le_of_le1 hmono.le (hD.bd y' hy') hlow
      · exact hD.pair1 y hy y' hy' hay hlt h1
    · exact le1_refl _
    · exact absurd (le1_le h1) (not_le.2 hgt)
  · intro y hy y' hy' h2
    rcases lt_trichotomy y y' with hlt | rfl | hgt
    · rcases eq_or_lt_of_le (hY y hy).1 with hya | hay
      · subst hya
        exact absurd h2 (hP.2 y' hlt (hY y' hy').2)
      · exact hD.pair2 y hy y' hy' hay hlt h2
    · exact le2_refl _
    · exact absurd (le2_le h2) (not_le.2 hgt)
  · intro x hx y hy h2
    exact absurd h2 (hP.1 x y (hX x hx) (hY y hy).1 (hY y hy).2)

/-- Realizer maps (per configuration) for cofinally many targets `t ≤ b`. -/
def LrRealCof (S : InaccSeq.{0}) (a b : Ordinal.{0}) : Prop :=
  ∀ y, a ≤ y → y < b → ∃ t, y < t ∧ t ≤ b ∧ LrReal S a t

theorem lrRealCof_of_rl {a b : Ordinal.{0}} (h : RlRealCof S a b) : LrRealCof S a b :=
  fun y hy hyb => by
    obtain ⟨t, h1, h2, h3⟩ := h y hy hyb
    exact ⟨t, h1, h2, lrReal_of_rl h3⟩

/-- **`a ≤₁ b` from realizer maps for cofinal targets.** -/
theorem lrLe1_of_realCof (hL : CdLOWER S) {a b : Ordinal.{0}} (hab : a ≤ b) (hP : CvNoPair a b)
    (hR : LrRealCof S a b) : le1 a b :=
  le1_of_cofinal hab fun y hay hyb => by
    obtain ⟨t, hyt, htb, hRt⟩ := hR y hay hyb
    exact ⟨t, hyt, lrLe1_of_real hL (hay.trans hyt.le) (cvNoPair_mono hP htb) hRt⟩

/-- **The crossing relations at the named restarts from the realizer maps.** -/
theorem lrNamed_of_real (hL : CdLOWER S) (hlow : Nc.ncL S ω ≤ nuC)
    (h0 : LrRealCof S (Nc.ncL S 0) (Nc.ncL S 1))
    (hn : ∀ n : ℕ, LrRealCof S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})))
    (hP : CvNoPair (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hw : LrRealCof S (Nc.ncL S ω) (Nc.ncL S (ω + 1))) : CxNamed S := by
  refine ⟨?_, fun n => ?_, lrLe1_of_realCof hL (Qq.qqL_lt_succ S).le hP hw⟩
  · obtain ⟨l, hl, e⟩ := cvM_restart (S := S)
    exact lrLe1_of_realCof hL (Pp.ppL_mono zero_le)
      (cvNoPair_of_nu hl e ((Pp.ppL_mono one_lt_omega0.le).trans hlow)) h0
  · obtain ⟨l, hl, e⟩ := Pp.ppL_succ_restart (S := S) n
    exact lrLe1_of_realCof hL (Pp.ppL_lt_succ n).le
      (cvNoPair_of_nu hl e ((Pp.ppL_lt_omega (n + 1)).le.trans hlow)) (hn n)

/-- **The reduced road (`Cx.cxRoad_rz`) with `CxNamed` replaced by per-configuration realizers.** -/
theorem lrRoad_rz (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hEQ : CxEQtop S) (htop : CxTCtopOff S) (hups : CxUpsRestTop S)
    (h0 : LrRealCof S (Nc.ncL S 0) (Nc.ncL S 1))
    (hn : ∀ n : ℕ, LrRealCof S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})))
    (hP : CvNoPair (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hw : LrRealCof S (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hmove : CxStdMoveTop S) (hstd : CxStdPairTop S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hU' := Rz.rzUPPER_of_rest hU hO
  have hL' := Rz.rzLOWER_of_rest hL
  have hV' := Rz.rzCapV_of_rest hV
  exact cxRoad_rz hU hO hL hV hEQ htop hups
    (lrNamed_of_real hL' (cdLow_enum hU' hV') h0 hn hP hw) hmove hstd

/-- **The hypotheses of `Rl.rlRoad_rz` give those of `lrRoad_rz`.** -/
theorem lrRoad_hyp_of_rl (h0 : RlRealCof S (Nc.ncL S 0) (Nc.ncL S 1))
    (hn : ∀ n : ℕ, RlRealCof S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})))
    (hw : RlRealCof S (Nc.ncL S ω) (Nc.ncL S (ω + 1))) :
    LrRealCof S (Nc.ncL S 0) (Nc.ncL S 1) ∧
      (∀ n : ℕ, LrRealCof S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
        (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))) ∧
      LrRealCof S (Nc.ncL S ω) (Nc.ncL S (ω + 1)) :=
  ⟨lrRealCof_of_rl h0, fun n => lrRealCof_of_rl (hn n), lrRealCof_of_rl hw⟩

end Googology.Trans.PoR.InaccPsi.R2.Lr

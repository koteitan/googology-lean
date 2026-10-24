import Googology.Trans.PoR.InaccPsi.R2.GhLd

/-!
# THE UNIFORMITY THEOREM FOR EVERY CODE `ε_{Ω₁+1}·(n+1) + a`: the top of `ghB n a` reads the atom
`Γ_{Ω₁+1+ε_{Ω₁+1}·(n+1)+a}`

`R2.GfUnif` for the layers of `R2.GhTow`, with the atoms `ghAt` of `R2.GhAt`:

* `ghLim_top`, `ghLim_poly` (the term-offset ladder limit reads `cQs c`, with terms below it), `GhPolyG.mono`;
* `ghU_codes` (**THE UNION READS THE LIMIT ATOM**, for every union step `GhUF`: if the members read atoms
  `Γ_{Ω₁+1+C_i}` below `Γ_{Ω₁+1+c_L}` (`c_L` a limit) and every smaller atom code with gate below `Z` is at most some
  `C_i` with side gate below `Z`, then the union top reads `Γ_{Ω₁+1+c_L}` and the union has terms for every code below
  it);
* `ghC n a = ε_{Ω₁+1}·(n+1) + a`, `ghC_split`, the unfolding lemmas `ghB_zero`, `ghB_succ`, `ghB_lim`;
* `ghEB_codes` (the code `ε_{Ω₁+1}`: from `Gf.gfB_codes`, `ghTh_eq_gfTh`), `ghTow_codes` (the codes of one shift),
  `ghStart_succ_codes`, `ghS_codes`, `ghB_codes` (**THE UNIFORMITY THEOREM**: `E_{ghB n a}(y) =
  Θ_y(Γ_{Ω₁+1+ε_{Ω₁+1}·(n+1)+a})` at every strongly critical `y` above `gtc a`, and every code below it over a base
  above `gtc a` is read by a term of `ghB n a`).

No new axiom.  New definitions: `ghC`, `GhStCodes`, `GhLCodes`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gh

open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph Googology.Trans.PoR.InaccPsi.R2.Xt Lu
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd

section Lim

variable {B : GdB} {c : Ordinal.{0}} (hc : ∀ Z, SC Z → B.g < Z → GxCl Z (ghAt Z) c) (hcO : Om 1 ≤ c)
  (hKE : ∀ y, SC y → y < Om 1 → B.g < y → B.K.E y = gxTh y (ghAt y) c) {e : Ordinal.{0} → Ordinal.{0}}
  (H : GeqH B e)
include hc hKE H

/-- **The term-offset limit top reads the code `cQs c`**: `ϑʸ(Ω₁·Ω₁ + e(y)) = Θ_y(cQs c)` above the gate. -/
theorem ghLim_top {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) (hg : B.g < y) :
    gq (e y) y = gxTh y (ghAt y) (cQs c) := by
  rw [geq_sup H (gg_SC_eps hy) (lp_y1 hy1) hg, cQs, gcTh_iSup]
  exact iSup_congr fun n => ghTop_th hc hKE n y hy hy1 hg

include hcO in
/-- **The term-offset limit layer has terms for every code below `cQs c`.** -/
theorem ghLim_poly (hKP : GhPolyG B.K.sys c) : GhPolyG (geqUSys B e H) (cQs c) := by
  intro Z d hg hd hdE
  obtain ⟨n, hn⟩ := cQs_lt hdE
  obtain ⟨s, hs⟩ := ghPoly hc hcO hKE hKP n Z d hg hd hn
  exact ⟨s, fun y hy hy1 hZy => ⟨(hs y hy hy1 hZy).1.1, (hs y hy hy1 hZy).2⟩⟩

end Lim

theorem GhPolyG.mono {g g' E : Ordinal.{0}} {X : GdSys g} (hP : GhPolyG X E) (h : g ≤ g') :
    GhPolyG (X.mono h) E := fun Z d hg hd hdE => hP Z d (h.trans_lt hg) hd hdE

/-! ## The union reads the limit atom -/

/-- **THE UNION READS THE LIMIT ATOM**: for a union step `F` whose members read the atoms `Γ_{Ω₁+1+C_i}` (with terms
below them), `C_i < c_L` (`c_L` a limit), and every atom code `b < c_L` with gate below a strongly critical `Z` above
`g` lies below some `C_i` with side gate below `Z`: the union top reads `Γ_{Ω₁+1+c_L}`, with terms below it. -/
theorem ghU_codes {g : Ordinal.{0}} (F : GhUF g) (C : F.I → Ordinal.{0}) {cL : Ordinal.{0}} (hcL : IsSuccLimit cL)
    (hK : ∀ i y, SC y → y < Om 1 → F.gi i < y → (F.K i).K.E y = gxTh y (ghAt y) (gcG (C i)))
    (hKP : ∀ i, GhPolyG (F.K i).K.sys (gcG (C i))) (hCle : ∀ i, C i ≤ cL)
    (hcov : ∀ b, b < cL → ∀ Z, SC Z → g < Z → ghg b < Z → ∃ i, F.gi i < Z ∧ b ≤ C i) :
    (∀ y, SC y → y < Om 1 → g < y → (ghLimB F).K.E y = gxTh y (ghAt y) (gcG cL)) ∧
      GhPolyG (ghLimB F).K.sys (gcG cL) := by
  refine ⟨fun y hy hy1 hgy => ?_, ?_⟩
  · have hyE := gg_SC_eps hy
    have hy1' := lp_y1 hy1
    show gq (F.l y) y = _
    refine le_antisymm (le_of_forall_lt fun v hv => ?_) (gxTh_le_of fun d hd hdlt => ?_)
    · obtain ⟨ν, hν, hvν⟩ := gf_lt_lim_iff hyE hy1' (F.lim y hyE hy1' hgy) (F.l_lt y hyE hy1' hgy) v hv
      obtain ⟨i, hi, hνi⟩ := F.cof y hyE hy1' hgy ν hν
      calc v < gq ν y := hvν
        _ ≤ gq (F.o i y) y := gfq_mono hyE hy1' (F.o_lt0 hyE hy1' hgy hi) hνi
        _ = (F.K i).K.E y := (F.E_eq i y hyE hy1' hi).symm
        _ = gxTh y (ghAt y) (gcG (C i)) := hK i y hy hy1 hi
        _ ≤ gxTh y (ghAt y) (gcG cL) := gxTh_mono (gcG_le (hCle i))
    · obtain ⟨b, hb, hgb, hdb⟩ := ghCl_lt_G hy hy1.le hcL hd hdlt
      obtain ⟨i, hi, hbi⟩ := hcov b hb y hy hgy hgb
      calc gxTh y (ghAt y) d < gxTh y (ghAt y) (gcG b) := gxTh_lt hd hdb
        _ ≤ gxTh y (ghAt y) (gcG (C i)) := gxTh_mono (gcG_le hbi)
        _ = (F.K i).K.E y := (hK i y hy hy1 hi).symm
        _ = gq (F.o i y) y := F.E_eq i y hyE hy1' hi
        _ < gq (F.l y) y := gfq_lt hyE hy1' (F.l_lt y hyE hy1' hgy) (F.o_lt i y hyE hy1' hgy hi)
  · refine ghPoly_of_SC _ _ ((ghUSys F).cst 0) fun Z hZ hZ1 hgZ d hd hdE => ?_
    obtain ⟨b, hb, hgb, hdb⟩ := ghCl_lt_G hZ hZ1.le hcL hd hdE
    obtain ⟨i, hi, hbi⟩ := hcov b hb Z hZ hgZ hgb
    obtain ⟨s, hs⟩ := hKP i Z d ((F.g_le i).trans_lt hi) hd (hdb.trans_le (gcG_le hbi))
    exact ⟨⟨i, s⟩, fun y hy hy1 hZy => ⟨⟨hi.trans_le hZy, (hs y hy hy1 hZy).1⟩, (hs y hy hy1 hZy).2⟩⟩

/-! ## The codes `ε_{Ω₁+1}·(n+1) + a` -/

/-- **The code** `ε_{Ω₁+1}·(n+1) + a`. -/
noncomputable def ghC (n : ℕ) (a : Ordinal.{0}) : Ordinal.{0} := gfE * ((n + 1 : ℕ) : Ordinal.{0}) + a

theorem ghC_lt (n : ℕ) {a : Ordinal.{0}} (ha : a < gfE) : ghC n a < ghE := gh_shift_lt n ha

theorem ghC_g (n : ℕ) {a : Ordinal.{0}} (ha : a < gfE) : ghg (ghC n a) = gtc a := (gh_shift n ha).2

theorem ghC_le (n : ℕ) {a b : Ordinal.{0}} (h : a ≤ b) : ghC n a ≤ ghC n b := add_le_add le_rfl h

theorem ghC_lt' (n : ℕ) {a b : Ordinal.{0}} (h : a < b) : ghC n a < ghC n b := (add_lt_add_iff_left _).2 h

theorem ghC_next (n : ℕ) : ghC (n + 1) 0 = ghC n gfE := by
  unfold ghC; rw [add_zero, Nat.cast_succ (n + 1), mul_add_one]

theorem ghC_lim (n : ℕ) {a : Ordinal.{0}} (ha : IsSuccLimit a) : IsSuccLimit (ghC n a) := isSuccLimit_add _ ha

theorem ghC_atom (n : ℕ) {a Z : Ordinal.{0}} (ha : a < gfE) (hg : gtc a < Z) : GxCl Z (ghAt Z) (gcG (ghC n a)) :=
  GxCl.atom (ghG_atom (ghC_lt n ha) (by rw [ghC_g n ha]; exact hg))

/-- **The split of a smaller code**: below `ε_{Ω₁+1}·(n+1)`, or `ε_{Ω₁+1}·(n+1) + b` with `b < a`. -/
theorem ghC_split (n : ℕ) {a b' : Ordinal.{0}} (h : b' < ghC n a) : b' < ghC n 0 ∨ ∃ b < a, b' = ghC n b := by
  rcases lt_or_ge b' (ghC n 0) with h0 | h0
  · exact Or.inl h0
  · right
    have h0' : gfE * ((n + 1 : ℕ) : Ordinal.{0}) ≤ b' := by rw [← add_zero (gfE * _)]; exact h0
    refine ⟨b' - gfE * ((n + 1 : ℕ) : Ordinal.{0}), ?_, ?_⟩
    · have e := Ordinal.add_sub_cancel_of_le h0'
      rw [← e] at h
      exact (add_lt_add_iff_left _).1 h
    · exact (Ordinal.add_sub_cancel_of_le h0').symm

/-- **The cover** at a code `ghC n a` (`a ≤ ε_{Ω₁+1}`): every smaller atom code with gate below `Z` is at most
`ghC n 0` or `ghC n b` with `b < a`, `gtc b < Z`. -/
theorem ghC_cov (n : ℕ) {a b' Z : Ordinal.{0}} (ha0 : 0 < a) (haE : a ≤ gfE) (h : b' < ghC n a) (hZ : 0 < Z)
    (hg : ghg b' < Z) : ∃ b, b < a ∧ gtc b < Z ∧ b' ≤ ghC n b := by
  rcases ghC_split n h with h0 | ⟨b, hb, rfl⟩
  · exact ⟨0, ha0, by rw [gtc_zero]; exact hZ, h0.le⟩
  · exact ⟨b, hb, by rw [← ghC_g n (hb.trans_le haE)]; exact hg, le_rfl⟩

/-! ## Unfolding the recursion -/

theorem ghRec_zero (n : ℕ) (s : GhStart n) (h : (0 : Ordinal.{0}) < gfE) : ghRec n s 0 h = ghSt0 s := by
  unfold ghRec; rw [Ordinal.limitRecOn_zero]

theorem ghRec_succ (n : ℕ) (s : GhStart n) (a : Ordinal.{0}) (ha : a + 1 < gfE) :
    ghRec n s (a + 1) ha = ghStSucc n a (ghRec n s a ((lt_add_one a).trans ha)) ha := by
  unfold ghRec; rw [Ordinal.limitRecOn_add_one]

theorem ghRec_lim (n : ℕ) (s : GhStart n) {a : Ordinal.{0}} (hl : IsSuccLimit a) (ha : a < gfE) :
    ghRec n s a ha = ghStLim n a hl ha (fun b hb => ghRec n s b (hb.trans ha)) := by
  unfold ghRec; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem ghB_zero (n : ℕ) (h : (0 : Ordinal.{0}) < gfE) : ghB n 0 h = (ghS n).1 := by
  show (ghRec n (ghS n) 0 h).1 = _
  rw [ghRec_zero]; rfl

theorem ghB_succ (n : ℕ) (a : Ordinal.{0}) (ha : a + 1 < gfE) :
    ghB n (a + 1) ha = (geqLimB (ghB n a ((lt_add_one a).trans ha)) (fun x => ghBs n x + rdc a x + 1)
      (ghH_succ (ghRec n (ghS n) a ((lt_add_one a).trans ha)) ha)).mono
        (gh_g_succ (ghRec n (ghS n) a ((lt_add_one a).trans ha)) ha) := by
  show (ghRec n (ghS n) (a + 1) ha).1 = _
  rw [ghRec_succ]; rfl

theorem ghB_lim (n : ℕ) {a : Ordinal.{0}} (hl : IsSuccLimit a) (ha : a < gfE) :
    ghB n a ha = ghLimB (ghFL n a hl ha fun b hb => ghRec n (ghS n) b (hb.trans ha)) := by
  show (ghRec n (ghS n) a ha).1 = _
  rw [ghRec_lim n (ghS n) hl ha]; rfl

/-! ## The readings -/

/-- The reading statement at the start of the shift `n` (the code `ε_{Ω₁+1}·(n+1)`). -/
def GhStCodes (n : ℕ) : Prop :=
  (∀ y, SC y → y < Om 1 → (ghS n).1.K.E y = gxTh y (ghAt y) (gcG (ghC n 0))) ∧
    GhPolyG (ghS n).1.K.sys (gcG (ghC n 0))

/-- The reading statement at the code `ε_{Ω₁+1}·(n+1) + a`. -/
def GhLCodes (n : ℕ) (a : Ordinal.{0}) (ha : a < gfE) : Prop :=
  (∀ y, SC y → y < Om 1 → gtc a < y → (ghB n a ha).K.E y = gxTh y (ghAt y) (gcG (ghC n a))) ∧
    GhPolyG (ghB n a ha).K.sys (gcG (ghC n a))

/-- **The code `ε_{Ω₁+1}`** reads `Γ_{Ω₁+1+ε_{Ω₁+1}}` (the union of all `gfB c`, `c < ε_{Ω₁+1}`). -/
theorem ghEB_codes (S : InaccSeq.{0}) :
    (∀ y, SC y → y < Om 1 → ghEB.K.E y = gxTh y (ghAt y) (gcG gfE)) ∧ GhPolyG ghEB.K.sys (gcG gfE) := by
  have hK : ∀ (i : ghF0.I) y, SC y → y < Om 1 → ghF0.gi i < y →
      (ghF0.K i).K.E y = gxTh y (ghAt y) (gcG (1 + i.1)) := fun i y hy hy1 hi => by
    rw [ghTh_eq_gfTh (gfT_le i.2)]
    exact (gfB_codes S i.1 i.2).1 y hy hy1 hi
  have hKP : ∀ i : ghF0.I, GhPolyG (ghF0.K i).K.sys (gcG (1 + i.1)) := fun i Z d hg hd hdE => by
    have hdV : d < gfV := hdE.trans_le (gfT_le i.2)
    obtain ⟨s, hs⟩ := (gfB_codes S i.1 i.2).2 Z d hg (gfCl_of_ghCl hd hdV) hdE
    refine ⟨s, fun y hy hy1 hZy => ⟨(hs y hy hy1 hZy).1, ?_⟩⟩
    have e2 := (hs y hy hy1 hZy).2
    rw [← ghTh_eq_gfTh hdV.le] at e2
    exact e2
  have h := ghU_codes ghF0 (fun i => 1 + i.1) eW_lim hK hKP (fun i => (gfT_lt i.2).le)
    fun b hb Z _ _ hgb => ⟨⟨b, hb⟩, by show gtc b < Z; rw [← ghg_of_lt hb]; exact hgb, le_add_self⟩
  exact ⟨fun y hy hy1 => h.1 y hy hy1 hy.1, h.2⟩

theorem ghS0_codes (S : InaccSeq.{0}) : GhStCodes 0 := by
  have e : ghC 0 0 = gfE := by simp [ghC]
  rw [GhStCodes, e]
  exact ghEB_codes S

/-- **The codes of one shift**: from the start of the shift `n`, every `ghB n a` reads `Γ_{Ω₁+1+ε_{Ω₁+1}·(n+1)+a}`. -/
theorem ghTow_codes (n : ℕ) (hs : GhStCodes n) : ∀ a : Ordinal.{0}, ∀ ha : a < gfE, GhLCodes n a ha := by
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IH0 =>
  rcases zero_or_succ_or_isSuccLimit a with rfl | ⟨δ, rfl⟩ | hα
  · intro ha
    rw [GhLCodes, ghB_zero]
    exact ⟨fun y hy hy1 _ => hs.1 y hy hy1, hs.2⟩
  · rw [succ_eq_add_one] at IH0 ⊢
    intro ha
    have hδ : δ < gfE := (lt_add_one δ).trans ha
    obtain ⟨ihE, ihP⟩ := IH0 δ (lt_add_one δ) hδ
    have hg0 : (ghB n δ hδ).g = gtc δ := ghB_g n hδ
    have hc : ∀ Z, SC Z → (ghB n δ hδ).g < Z → GxCl Z (ghAt Z) (gcG (ghC n δ)) := fun Z _ hg => by
      rw [hg0] at hg; exact ghC_atom n hδ hg
    have hcO : Om 1 ≤ gcG (ghC n δ) := (gcG_Om1_lt _).le
    have hKE : ∀ y, SC y → y < Om 1 → (ghB n δ hδ).g < y →
        (ghB n δ hδ).K.E y = gxTh y (ghAt y) (gcG (ghC n δ)) :=
      fun y hy hy1 hg => ihE y hy hy1 (hg0 ▸ hg)
    have hQ : cQs (gcG (ghC n δ)) = gcG (ghC n (δ + 1)) := by rw [gc_cQs, ghC, ghC, add_assoc]
    have H := ghH_succ (ghRec n (ghS n) δ hδ) ha
    rw [GhLCodes, ghB_succ n δ ha]
    refine ⟨fun y hy hy1 hδy => ?_, fun Z d hg hd hdE => ?_⟩
    · show gq (ghBs n y + rdc δ y + 1) y = _
      have hgy : (ghB n δ hδ).g < y := by rw [hg0]; exact (rdc_succ δ hδ 0).2.1.trans_lt hδy
      rw [ghLim_top (e := fun x => ghBs n x + rdc δ x + 1) hc hKE H hy hy1 hgy, hQ]
    · have hP := (ghLim_poly hc hcO hKE H ihP).mono (gh_g_succ (ghRec n (ghS n) δ hδ) ha)
      rw [hQ] at hP
      exact hP Z d hg hd hdE
  · intro ha
    have IH : ∀ b, ∀ hb : b < a, GhLCodes n b (hb.trans ha) := fun b hb => IH0 b hb (hb.trans ha)
    rw [GhLCodes, ghB_lim n hα ha]
    set F := ghFL n a hα ha fun b hb => ghRec n (ghS n) b (hb.trans ha) with hF
    have hK : ∀ (i : F.I) y, SC y → y < Om 1 → F.gi i < y →
        (F.K i).K.E y = gxTh y (ghAt y) (gcG (ghC n i.1)) := fun i y hy hy1 hi => (IH i.1 i.2).1 y hy hy1 hi
    have hKP : ∀ i : F.I, GhPolyG (F.K i).K.sys (gcG (ghC n i.1)) := fun i => (IH i.1 i.2).2
    have h := ghU_codes F (fun i => ghC n i.1) (ghC_lim n hα) hK hKP (fun i => ghC_le n i.2.le)
      fun b' hb' Z hZ _ hgb' => by
        obtain ⟨b, hb, hgb, hle⟩ := ghC_cov n hα.bot_lt ha.le hb' hZ.1 hgb'
        exact ⟨⟨b, hb⟩, hgb, hle⟩
    exact ⟨fun y hy hy1 hαy => h.1 y hy hy1 hαy, h.2⟩

/-- **The start of the shift `n + 1`** reads `Γ_{Ω₁+1+ε_{Ω₁+1}·(n+2)}`. -/
theorem ghStart_succ_codes (n : ℕ) (hB : ∀ a : Ordinal.{0}, ∀ ha : a < gfE, GhLCodes n a ha) :
    GhStCodes (n + 1) := by
  rw [GhStCodes, ghC_next]
  set F := ghFN n (ghS n) with hF
  have hK : ∀ (i : F.I) y, SC y → y < Om 1 → F.gi i < y →
      (F.K i).K.E y = gxTh y (ghAt y) (gcG (ghC n i.1)) := fun i y hy hy1 hi => (hB i.1 i.2).1 y hy hy1 hi
  have hKP : ∀ i : F.I, GhPolyG (F.K i).K.sys (gcG (ghC n i.1)) := fun i => (hB i.1 i.2).2
  have h := ghU_codes F (fun i => ghC n i.1) (ghC_lim n eW_lim) hK hKP (fun i => ghC_le n i.2.le)
    fun b' hb' Z hZ _ hgb' => by
      obtain ⟨b, hb, hgb, hle⟩ := ghC_cov n eW_E.pos le_rfl hb' hZ.1 hgb'
      exact ⟨⟨b, hb⟩, hgb, hle⟩
  exact ⟨fun y hy hy1 => h.1 y hy hy1 hy.1, h.2⟩

/-- **The readings of all starts.** -/
theorem ghS_codes (S : InaccSeq.{0}) : ∀ n : ℕ, GhStCodes n
  | 0 => ghS0_codes S
  | n + 1 => ghStart_succ_codes n (ghTow_codes n (ghS_codes S n))

/-- **THE UNIFORMITY THEOREM** for every code `ε_{Ω₁+1}·(n+1) + a` (`n < ω`, `a < ε_{Ω₁+1}`): the top of `ghB n a`
reads `Γ_{Ω₁+1+ε_{Ω₁+1}·(n+1)+a}` at every strongly critical `y` above `gtc a`, and `ghB n a` has terms for every
code below it over every base above `gtc a`. -/
theorem ghB_codes (S : InaccSeq.{0}) (n : ℕ) (a : Ordinal.{0}) (ha : a < gfE) :
    (∀ y, SC y → y < Om 1 → gtc a < y → (ghB n a ha).K.E y = gxTh y (ghAt y) (gcG (ghC n a))) ∧
      GhPolyG (ghB n a ha).K.sys (gcG (ghC n a)) :=
  ghTow_codes n (ghS_codes S n) a ha

end Googology.Trans.PoR.InaccPsi.R2.Gh

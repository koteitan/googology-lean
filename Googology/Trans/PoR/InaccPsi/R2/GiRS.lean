import Googology.Trans.PoR.InaccPsi.R2.GiRdg

/-!
# A READING SYSTEM AND ONE RECURSION FOR ITS CODES: gated layers with top `Γ_{x+1+c(x)}` for every code
`c ∈ [ε_{Ω₁+1}, B)`

A reading system `RS : GiRS` is a code system `RS.K` (`R2.GiAt`) with a reading `RS.R c x` of its codes at the bases
(`Ω₁ ↦ x`) and the facts the layer construction uses: the reading of `ε_{Ω₁+1}` is `ε_{x+1}`, every reading is below
`Γ_{x+1}`, the reading is strictly increasing and moves by `+1` along `+1`, the readings of the codes below a limit code
are cofinal in its reading, Lemma EXACT at every pair of bases, and at every limit code the last term with Lemma IMG
for its logend (`GiLD`); plus a cofinal sequence of codes with gates below `ε₀` (for the frontiers).

One recursion on the code `c ∈ [ε_{Ω₁+1}, B)`:

* `c = ε_{Ω₁+1}`: the layer `Gh.ghEB`;
* `c = b + 1`: the gated ladder over the layer of `b` with the term offset `b(x) + 1` (`Ge.geqLimB`);
* `c` a limit above `ε_{Ω₁+1}`: the union step (`Gh.ghLimB`) over all layers of the codes `b ∈ [ε_{Ω₁+1}, c)` with the
  offset `c(x)`.

* `GiLD` (the data of the union at a limit code), `GiRS`, `GiRS.GiSt`, `giSt0`, `giH_succ`, `giStSucc`, `giFL`,
  `giStLim`, `giRec`, `GiRS.giL c` (**THE GATED LAYER OF THE CODE `c`**: gate `RS.K.gt c`, top
  `ϑˣ(Ω₁·Ω₁ + c(x)) = Γ_{x+1+c(x)}` at every `ε`-number base above the gate), the unfolding lemmas.

No new axiom.  New definitions: `GiLD`, `GiRS`, `GiRS.GiSt`, `GiRS.giSt0`, `GiRS.giStSucc`, `GiRS.giFL`,
`GiRS.giStLim`, `GiRS.giRec`, `GiRS.giL`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gi

open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
open Ordinal Order Set Googology.Notation.InaccPsi
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Gb

/-- **The data of the union at a limit code `c`** for a code system `K` with the reading `R`: the predecessor code `c'`
and the last term `R c x = l'(x) + ω^{logend(R c x)}`, with Lemma IMG for the logend. -/
structure GiLD (K : GiCS) (R : Ordinal.{0} → Ordinal.{0} → Ordinal.{0}) (c : Ordinal.{0}) where
  cp : Ordinal.{0}
  lp : Ordinal.{0} → Ordinal.{0}
  cp_ge : gfE ≤ cp
  cp_lt : cp < c
  cp_g : K.gt cp ≤ K.gt c
  dec : ∀ x, InE x → x < Om1 → K.gt c < x →
    R c x = lp x + ω ^ lg (R c x) ∧ ω ^ lg (R c x) ∣ lp x ∧ lg (R c x) ≠ 0 ∧ lp x ≤ R cp x
  pkg : ∀ ρ τ δ, RstK ρ τ δ → K.gt c < ρ → GhPkg (K.gt c) ρ δ (fun y => lg (R c y))

/-- **A reading system**: a code system with a reading of its codes and the facts of the layer construction. -/
structure GiRS where
  K : GiCS
  R : Ordinal.{0} → Ordinal.{0} → Ordinal.{0}
  E_lt : gfE < K.B
  B_lim : IsSuccLimit K.B
  gt_E : K.gt gfE = 0
  gt_lowE : ∀ c, c < gfE → K.gt c = gtc c
  R_E : ∀ x, R gfE x = eN x
  lt0 : ∀ c x, InE x → x < Om1 → c < K.B → K.gt c < x → R c x < gq 0 x
  mono : ∀ b c x, InE x → c < K.B → b < c → K.gt b < x → K.gt c < x → R b x < R c x
  succ : ∀ b x, R (b + 1) x = R b x + 1
  gt_le_succ : ∀ b, K.gt b ≤ K.gt (b + 1)
  cof : ∀ c x, InE x → x < Om1 → c < K.B → gfE < c → K.gt c < x → ∀ ν < R c x,
    ∃ b, gfE ≤ b ∧ b < c ∧ K.gt b < x ∧ ν ≤ R b x
  ex : ∀ σ ρ c, Bases σ ρ → c < K.B → K.gt c < σ →
    R c ρ ∈ TB ρ σ ∧ Googology.Trans.PoR.InaccPsi.R2.pi σ ρ (R c ρ) = R c σ
  ld : ∀ c, IsSuccLimit c → gfE < c → c < K.B → Nonempty (GiLD K R c)
  cf : ℕ → Ordinal.{0}
  cf_ge : ∀ k, gfE ≤ cf k
  cf_lt : ∀ k, cf k < K.B
  cf_g : ∀ k, K.gt (cf k) < ε₀
  cf_mono : ∀ k, cf k < cf (k + 1)
  cf_cof : ∀ c, c < K.B → ∃ k, c < cf k

theorem gi_not_E_le_succ {b : Ordinal.{0}} (h : gfE ≤ b + 1) (hb : ¬ gfE ≤ b) : False := by
  push Not at hb
  exact absurd h (not_le.2 (succ_lt_eW hb))

namespace GiRS

variable (RS : GiRS)

theorem R_lt0' {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {c : Ordinal.{0}} (hc : c < RS.K.B)
    (hg : RS.K.gt c < x) : RS.R c x < gq 0 x := RS.lt0 c x hx hx1 hc hg

theorem R_lt1' {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {c : Ordinal.{0}} (hc : c < RS.K.B)
    (hg : RS.K.gt c < x) : RS.R c x + 1 < gq 0 x := by
  have hE := (gfq0_facts hx hx1).2.2.2
  exact (inE_indec hE).add_lt (RS.R_lt0' hx hx1 hc hg) (one_lt_omega0.trans (omega0_lt_inE hE))

theorem R_mono' {x : Ordinal.{0}} (hx : InE x) {b c : Ordinal.{0}} (hc : c < RS.K.B) (hbc : b < c)
    (hgb : RS.K.gt b < x) (hgc : RS.K.gt c < x) : RS.R b x < RS.R c x := RS.mono b c x hx hc hbc hgb hgc

theorem R_cof' {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {c : Ordinal.{0}} (hc : c < RS.K.B) (hEc : gfE < c)
    (hg : RS.K.gt c < x) {ν : Ordinal.{0}} (hν : ν < RS.R c x) :
    ∃ b, gfE ≤ b ∧ b < c ∧ RS.K.gt b < x ∧ ν ≤ RS.R b x := RS.cof c x hx hx1 hc hEc hg ν hν

theorem R_pi' {σ ρ c : Ordinal.{0}} (hB : Bases σ ρ) (hc : c < RS.K.B) (hg : RS.K.gt c < σ) :
    RS.R c ρ ∈ TB ρ σ ∧ Googology.Trans.PoR.InaccPsi.R2.pi σ ρ (RS.R c ρ) = RS.R c σ := RS.ex σ ρ c hB hc hg

/-- **The value at the code `c`**: a gated layer with gate `RS.K.gt c` and top `ϑˣ(Ω₁·Ω₁ + c(x))` above the gate. -/
def GiSt (c : Ordinal.{0}) : Type 2 :=
  {B : GdB // B.g = RS.K.gt c ∧ ∀ x, InE x → x < Om1 → RS.K.gt c < x → B.K.E x = gq (RS.R c x) x}

/-- The base: the layer of the code `ε_{Ω₁+1}`. -/
noncomputable def giSt0 (c : Ordinal.{0}) (h : c = gfE) : RS.GiSt c :=
  ⟨ghEB, by rw [ghEB_g, h, RS.gt_E], fun x _ _ _ => by rw [ghEB_E, h, RS.R_E]⟩

/-- **The term-offset limit hypothesis for the successor** `b + 1`. -/
theorem giH_succ {b : Ordinal.{0}} (s : RS.GiSt b) (hb : b + 1 < RS.K.B) : GeqH s.1 (fun x => RS.R b x + 1) := by
  have hbB : b < RS.K.B := (lt_add_one b).trans hb
  refine ⟨fun x hx hx1 hg => ?_, fun x hx hx1 hg => ?_, fun x hx hx1 hg j _ hj => ?_, fun x hx hx1 hg => ?_,
    fun σ ρ hB hg => ?_⟩
  · rw [s.2.1] at hg; exact gfq_T hx hx1 (RS.R_lt1' hx hx1 hbB hg)
  · rw [s.2.1] at hg
    rw [s.2.2 x hx hx1 hg]
    obtain ⟨hT, h1⟩ := gfq_T hx hx1 (RS.R_lt0' hx hx1 hbB hg)
    exact (RS.R_lt1' hx hx1 hbB hg).trans_le (gfq0_le hx hx1 hT h1)
  · rw [s.2.1] at hg
    rw [s.2.2 x hx hx1 hg]
    exact gfq_mono hx hx1 (RS.R_lt0' hx hx1 hbB hg) (Order.lt_add_one_iff.1 hj)
  · rw [s.2.1] at hg
    rw [s.2.2 x hx hx1 hg]
    exact gfq_lt hx hx1 (RS.R_lt1' hx hx1 hbB hg) (lt_add_one _)
  · rw [s.2.1] at hg
    have h1σ : (1 : Ordinal.{0}) < σ := Lu.lu_one_lt_E hB.1
    obtain ⟨h1, h2⟩ := RS.R_pi' hB hbB hg
    obtain ⟨h3, h4⟩ := pi_add hB h1 (mem_TB_of_lt hB h1σ)
    exact ⟨h3, by rw [h4, h2, pi_lt hB h1σ]⟩

theorem gi_g_succ {b : Ordinal.{0}} (s : RS.GiSt b) (hb : b + 1 < RS.K.B) :
    (geqLimB s.1 (fun x => RS.R b x + 1) (RS.giH_succ s hb)).g ≤ RS.K.gt (b + 1) := by
  rw [geqLimB_g, s.2.1]; exact RS.gt_le_succ b

/-- The successor step: the limit of the gated ladder over the layer of `b`. -/
noncomputable def giStSucc (b : Ordinal.{0}) (s : RS.GiSt b) (hb : b + 1 < RS.K.B) : RS.GiSt (b + 1) :=
  ⟨(geqLimB s.1 (fun x => RS.R b x + 1) (RS.giH_succ s hb)).mono (RS.gi_g_succ s hb), rfl, fun x _ _ _ => by
    show gq (RS.R b x + 1) x = gq (RS.R (b + 1) x) x
    rw [RS.succ]⟩

/-- **The data of the union at a limit code `c > ε_{Ω₁+1}`**: all layers of the codes `b ∈ [ε_{Ω₁+1}, c)`. -/
noncomputable def giFL (c : Ordinal.{0}) (hl : IsSuccLimit c) (hEc : gfE < c) (hc : c < RS.K.B)
    (IH : ∀ b, gfE ≤ b → b < c → RS.GiSt b) : GhUF (RS.K.gt c) where
  I := {b : Ordinal.{0} // gfE ≤ b ∧ b < c}
  K := fun b => (IH b.1 b.2.1 b.2.2).1
  gi := fun b => RS.K.gt b.1
  o := fun b x => RS.R b.1 x
  l := fun x => RS.R c x
  lp := (Classical.choice (RS.ld c hl hEc hc)).lp
  i0 := ⟨gfE, le_rfl, hEc⟩
  ip := ⟨(Classical.choice (RS.ld c hl hEc hc)).cp, (Classical.choice (RS.ld c hl hEc hc)).cp_ge,
    (Classical.choice (RS.ld c hl hEc hc)).cp_lt⟩
  g_le := fun b => (IH b.1 b.2.1 b.2.2).2.1.le
  gi0 := RS.gt_E
  gip := (Classical.choice (RS.ld c hl hEc hc)).cp_g
  E_eq := fun b x hx hx1 hg => (IH b.1 b.2.1 b.2.2).2.2 x hx hx1 hg
  o_lt := fun b x hx _ hg hgb => RS.R_mono' hx hc b.2.2 hgb hg
  l_lt := fun x hx hx1 hg => RS.R_lt0' hx hx1 hc hg
  lim := fun x hx hx1 hg => by
    obtain ⟨e1, -, e3, -⟩ := (Classical.choice (RS.ld c hl hEc hc)).dec x hx hx1 hg
    show IsSuccLimit (RS.R c x)
    rw [e1]; exact isSuccLimit_add _ (Ph.ph_opow_lim e3)
  cof := fun x hx hx1 hg ν hν => by
    obtain ⟨b, h1, h2, h3, h4⟩ := RS.R_cof' hx hx1 hc hEc hg hν
    exact ⟨⟨b, h1, h2⟩, h3, h4⟩
  pi := fun _ _ _ _ hB hg => RS.R_pi' hB hc hg
  dec := fun x hx hx1 hg => by
    obtain ⟨e1, e2, e3, -⟩ := (Classical.choice (RS.ld c hl hEc hc)).dec x hx hx1 hg
    refine ⟨e1, e2, ?_⟩
    show (Classical.choice (RS.ld c hl hEc hc)).lp x < RS.R c x
    conv_rhs => rw [e1]
    exact lt_add_of_pos_right _ (opow_pos _ omega0_pos)
  lp_le := fun x hx hx1 hg => ((Classical.choice (RS.ld c hl hEc hc)).dec x hx hx1 hg).2.2.2
  pkg := (Classical.choice (RS.ld c hl hEc hc)).pkg

/-- The limit step: the union. -/
noncomputable def giStLim (c : Ordinal.{0}) (hl : IsSuccLimit c) (hEc : gfE < c) (hc : c < RS.K.B)
    (IH : ∀ b, gfE ≤ b → b < c → RS.GiSt b) : RS.GiSt c :=
  ⟨ghLimB (RS.giFL c hl hEc hc IH), rfl, fun _ _ _ _ => rfl⟩

/-- **The recursion over the codes `c ∈ [ε_{Ω₁+1}, ε_{Ω₁+1}²)`.** -/
noncomputable def giRec (c : Ordinal.{0}) : gfE ≤ c → c < RS.K.B → RS.GiSt c :=
  Ordinal.limitRecOn (motive := fun c => gfE ≤ c → c < RS.K.B → RS.GiSt c) c
    (fun h _ => absurd h (not_le.2 eW_E.pos))
    (fun b ih h hc => if hb : gfE ≤ b then RS.giStSucc b (ih hb ((lt_add_one b).trans hc)) hc
      else (gi_not_E_le_succ h hb).elim)
    (fun c hl ih h hc => if hE : c = gfE then RS.giSt0 c hE
      else RS.giStLim c hl (lt_of_le_of_ne h (Ne.symm hE)) hc (fun b hb1 hb2 => ih b hb2 hb1 (hb2.trans hc)))

theorem giRec_succ (b : Ordinal.{0}) (hb : gfE ≤ b) (h : gfE ≤ b + 1) (hc : b + 1 < RS.K.B) :
    RS.giRec (b + 1) h hc = RS.giStSucc b (RS.giRec b hb ((lt_add_one b).trans hc)) hc := by
  unfold GiRS.giRec; rw [Ordinal.limitRecOn_add_one, dif_pos hb]

theorem giRec_E (h : gfE ≤ gfE) (hc : gfE < RS.K.B) : RS.giRec gfE h hc = RS.giSt0 gfE rfl := by
  unfold GiRS.giRec; rw [Ordinal.limitRecOn_limit _ _ _ _ eW_lim, dif_pos rfl]

theorem giRec_lim {c : Ordinal.{0}} (hl : IsSuccLimit c) (hEc : gfE < c) (h : gfE ≤ c) (hc : c < RS.K.B) :
    RS.giRec c h hc = RS.giStLim c hl hEc hc (fun b hb1 hb2 => RS.giRec b hb1 (hb2.trans hc)) := by
  unfold GiRS.giRec; rw [Ordinal.limitRecOn_limit _ _ _ _ hl, dif_neg hEc.ne']

/-- **THE GATED LAYER OF THE CODE `c`** (`ε_{Ω₁+1} ≤ c < ε_{Ω₁+1}²`). -/
noncomputable def giL (c : Ordinal.{0}) (h : gfE ≤ c) (hc : c < RS.K.B) : GdB := (RS.giRec c h hc).1

theorem giL_g {c : Ordinal.{0}} (h : gfE ≤ c) (hc : c < RS.K.B) : (RS.giL c h hc).g = RS.K.gt c :=
  (RS.giRec c h hc).2.1

theorem giL_E {c x : Ordinal.{0}} (h : gfE ≤ c) (hc : c < RS.K.B) (hx : InE x) (hx1 : x < Om1) (hg : RS.K.gt c < x) :
    (RS.giL c h hc).K.E x = gq (RS.R c x) x := (RS.giRec c h hc).2.2 x hx hx1 hg

theorem giL_top {c x : Ordinal.{0}} (h : gfE ≤ c) (hc : c < RS.K.B) (hx : InE x) (hx1 : x < Om1) (hg : RS.K.gt c < x) :
    (RS.giL c h hc).K.sys.top x = gq (RS.R c x) x := by
  have hg' : (RS.giL c h hc).g < x := by rw [RS.giL_g]; exact hg
  rw [(RS.giL c h hc).K.top_eq x hx hx1 hg', ← RS.giL_E h hc hx hx1 hg]
  exact (RS.giL c h hc).ek x hx hx1 hg'


end GiRS

end Googology.Trans.PoR.InaccPsi.R2.Gi

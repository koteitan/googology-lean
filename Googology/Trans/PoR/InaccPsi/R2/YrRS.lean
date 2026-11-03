import Googology.Trans.PoR.InaccPsi.R2.YrU
import Googology.Trans.PoR.InaccPsi.R2.XxRS

/-!
# YrRS: THE GATED LAYER OF EVERY CODE OF A READING SYSTEM WITH ADMISSIBLE READINGS (NO CONSTANT BOUND)

`Xx.XxRS k` asks the readings below `Γ_{x+2+k} = ϑˣ(Ω₁·Ω₁ + (k+1))` with a CONSTANT `k + 1 < ε₀`.  The layer
construction (`Xx.XxRS.gqL`, the uniformity theorem `Xx.XxRS.gqL_codes`) only uses that every reading is an
admissible offset (`Yr.YrN`).  Here that is the field (`YrRS.lt0`), so a reading system may read its base atom with a
READ index (`Γ(c)` read `Γ_{x+1+c(x)}`); the proofs are those of `Xx.XxRS` with the facts of `Yr.YrGq` / `Yr.YrU`.
Every `Xx.XxRS k` is a `YrRS` (`YrRS.ofXx`).

* `yrU_codes` (**THE UNION READS THE LIMIT ATOM**, `Xx.xxU_codes` for `Yr.YrUF`);
* `YrRS`, `YrRS.ofXx`, `YrRS.GqSt`, `gqSt0`, `gqH_succ`, `gqStSucc`, `gqFL`, `gqStLim`, `gqRec`, `YrRS.gqL c`
  (**THE GATED LAYER OF THE CODE `c`**), `gqL_g`, `gqL_E`, `gqL_top`;
* `YrRS.GqLC`, `YrRS.gqL_codes` (**THE UNIFORMITY THEOREM**).

No new axiom.  New definitions: `YrRS`, `YrRS.ofXx`, `YrRS.GqSt`, `YrRS.gqSt0`, `YrRS.gqStSucc`, `YrRS.gqFL`,
`YrRS.gqStLim`, `YrRS.gqRec`, `YrRS.gqL`, `YrRS.GqLC`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yr

open Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq Googology.Trans.PoR.InaccPsi.R2.Gr
  Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Xk
open Googology.Trans.PoR.InaccPsi.R2.Gi
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph Googology.Trans.PoR.InaccPsi.R2.Xt Lu
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Xx

section Unif

variable {K : GsCS}

/-- **THE UNION READS THE LIMIT ATOM**: for a union step `F` whose members read the atoms `Γ_{Ω₁+1+C_i}` (with terms
below them), `C_i < c_L` (`c_L` a limit), and every atom code `b < c_L` with gate below a strongly critical `Z` above
`g` lies below some `C_i` with side gate below `Z`: the union top reads `Γ_{Ω₁+1+c_L}`, with terms below it. -/
theorem yrU_codes {g : Ordinal.{0}} (F : YrUF g) (C : F.I → Ordinal.{0}) {cL : Ordinal.{0}} (hcL : IsSuccLimit cL)
    (hcLB : cL ≤ K.B)
    (hK : ∀ i y, SC y → y < Om 1 → F.gi i < y → (F.K i).K.E y = gxTh y (K.At y) (gcG (C i)))
    (hKP : ∀ i, GsmPolyG K (F.K i).K.sys (gcG (C i))) (hCle : ∀ i, C i ≤ cL)
    (hcov : ∀ b, b < cL → ∀ Z, SC Z → g < Z → K.gt b < Z → ∃ i, F.gi i < Z ∧ b ≤ C i) :
    (∀ y, SC y → y < Om 1 → g < y → (yrLimB F).K.E y = gxTh y (K.At y) (gcG cL)) ∧
      GsmPolyG K (yrLimB F).K.sys (gcG cL) := by
  refine ⟨fun y hy hy1 hgy => ?_, ?_⟩
  · have hyE := gg_SC_eps hy
    have hy1' := lp_y1 hy1
    show gq (F.l y) y = _
    refine le_antisymm (le_of_forall_lt fun v hv => ?_) (gxTh_le_of fun d hd hdlt => ?_)
    · obtain ⟨ν, hν, hvν⟩ := yr_lt_lim_iff hyE hy1' (F.lim y hyE hy1' hgy) (F.l_N y hyE hy1' hgy) v hv
      obtain ⟨i, hi, hνi⟩ := F.cof y hyE hy1' hgy ν hν
      calc v < gq ν y := hvν
        _ ≤ gq (F.o i y) y := yr_mono hyE hy1' (F.o_N hyE hy1' hgy hi) hνi
        _ = (F.K i).K.E y := (F.E_eq i y hyE hy1' hi).symm
        _ = gxTh y (K.At y) (gcG (C i)) := hK i y hy hy1 hi
        _ ≤ gxTh y (K.At y) (gcG cL) := gxTh_mono (gcG_le (hCle i))
    · obtain ⟨b, hb, hgb, hdb⟩ := gsmCl_lt_G hy hy1.le hcL hcLB hd hdlt
      obtain ⟨i, hi, hbi⟩ := hcov b hb y hy hgy hgb
      calc gxTh y (K.At y) d < gxTh y (K.At y) (gcG b) := gxTh_lt hd hdb
        _ ≤ gxTh y (K.At y) (gcG (C i)) := gxTh_mono (gcG_le hbi)
        _ = (F.K i).K.E y := (hK i y hy hy1 hi).symm
        _ = gq (F.o i y) y := F.E_eq i y hyE hy1' hi
        _ < gq (F.l y) y := yr_lt hyE hy1' (F.l_N y hyE hy1' hgy) (F.o_lt i y hyE hy1' hgy hi)
  · refine gsmPoly_of_SC _ _ ((yrUSys F).cst 0) fun Z hZ hZ1 hgZ d hd hdE => ?_
    obtain ⟨b, hb, hgb, hdb⟩ := gsmCl_lt_G hZ hZ1.le hcL hcLB hd hdE
    obtain ⟨i, hi, hbi⟩ := hcov b hb Z hZ hgZ hgb
    obtain ⟨s, hs⟩ := hKP i Z d ((F.g_le i).trans_lt hi) hd (hdb.trans_le (gcG_le hbi))
    exact ⟨⟨i, s⟩, fun y hy hy1 hZy => ⟨⟨hi.trans_le hZy, (hs y hy hy1 hZy).1⟩, (hs y hy hy1 hZy).2⟩⟩

end Unif

/-- **A reading system with admissible readings**: the fields of `Xk.XkRS` with `lt0` asking every reading to be an
admissible offset (`Yr.YrN`) in place of a constant bound. -/
structure YrRS where
  K : GsCS
  R : Ordinal.{0} → Ordinal.{0} → Ordinal.{0}
  E_lt : gfE < K.B
  B_lim : IsSuccLimit K.B
  gt_E : K.gt gfE = 0
  gt_lowE : ∀ c, c < gfE → K.gt c = gtc c
  R_E : ∀ x, InE x → x < Om1 → R gfE x = eN x
  lt0 : ∀ c x, InE x → x < Om1 → c < K.B → K.gt c < x → YrN x (R c x)
  mono : ∀ b c x, InE x → x < Om1 → c < K.B → b < c → K.gt b < x → K.gt c < x → R b x < R c x
  succ : ∀ b x, x < Om1 → R (b + 1) x = R b x + 1
  gt_le_succ : ∀ b, K.gt b ≤ K.gt (b + 1)
  cof : ∀ c x, InE x → x < Om1 → c < K.B → gfE < c → K.gt c < x → ∀ ν < R c x,
    ∃ b, gfE ≤ b ∧ b < c ∧ K.gt b < x ∧ ν ≤ R b x
  ex : ∀ σ ρ c, Bases σ ρ → c < K.B → K.gt c < σ →
    R c ρ ∈ TB ρ σ ∧ Googology.Trans.PoR.InaccPsi.R2.pi σ ρ (R c ρ) = R c σ
  ld : ∀ c, IsSuccLimit c → gfE < c → c < K.B → Nonempty (GsmLD K R c)

/-- **Every constant-bound reading system is one** (`Xx.XxRS k` ⇒ `YrRS`). -/
noncomputable def YrRS.ofXx {k : Ordinal.{0}} (RS : XxRS k) : YrRS where
  K := RS.K
  R := RS.R
  E_lt := RS.E_lt
  B_lim := RS.B_lim
  gt_E := RS.gt_E
  gt_lowE := RS.gt_lowE
  R_E := RS.R_E
  lt0 := fun c x hx hx1 hc hg => yrN_of_cst hx hx1 RS.W_lt (RS.lt0 c x hx hx1 hc hg)
  mono := RS.mono
  succ := RS.succ
  gt_le_succ := RS.gt_le_succ
  cof := RS.cof
  ex := RS.ex
  ld := RS.ld

namespace YrRS

variable (RS : YrRS)

theorem R_lt0' {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {c : Ordinal.{0}} (hc : c < RS.K.B)
    (hg : RS.K.gt c < x) : YrN x (RS.R c x) := RS.lt0 c x hx hx1 hc hg

theorem R_lt1' {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {c : Ordinal.{0}} (hc : c < RS.K.B)
    (hg : RS.K.gt c < x) : YrN x (RS.R c x + 1) := yrN_succ hx hx1 (RS.R_lt0' hx hx1 hc hg)

theorem R_mono' {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {b c : Ordinal.{0}} (hc : c < RS.K.B) (hbc : b < c)
    (hgb : RS.K.gt b < x) (hgc : RS.K.gt c < x) : RS.R b x < RS.R c x := RS.mono b c x hx hx1 hc hbc hgb hgc

theorem R_cof' {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {c : Ordinal.{0}} (hc : c < RS.K.B) (hEc : gfE < c)
    (hg : RS.K.gt c < x) {ν : Ordinal.{0}} (hν : ν < RS.R c x) :
    ∃ b, gfE ≤ b ∧ b < c ∧ RS.K.gt b < x ∧ ν ≤ RS.R b x := RS.cof c x hx hx1 hc hEc hg ν hν

theorem R_pi' {σ ρ c : Ordinal.{0}} (hB : Bases σ ρ) (hc : c < RS.K.B) (hg : RS.K.gt c < σ) :
    RS.R c ρ ∈ TB ρ σ ∧ Googology.Trans.PoR.InaccPsi.R2.pi σ ρ (RS.R c ρ) = RS.R c σ := RS.ex σ ρ c hB hc hg

/-- **The value at the code `c`**: a gated layer with gate `RS.K.gt c` and top `ϑˣ(Ω₁·Ω₁ + c(x))` above the gate. -/
def GqSt (c : Ordinal.{0}) : Type 2 :=
  {B : GdB // B.g = RS.K.gt c ∧ ∀ x, InE x → x < Om1 → RS.K.gt c < x → B.K.E x = gq (RS.R c x) x}

/-- The base: the layer of the code `ε_{Ω₁+1}`. -/
noncomputable def gqSt0 (c : Ordinal.{0}) (h : c = gfE) : RS.GqSt c :=
  ⟨ghEB, by rw [ghEB_g, h, RS.gt_E], fun x hx hx1 _ => by rw [ghEB_E, h, RS.R_E x hx hx1]⟩

/-- **The term-offset limit hypothesis for the successor** `b + 1`. -/
theorem gqH_succ {b : Ordinal.{0}} (s : RS.GqSt b) (hb : b + 1 < RS.K.B) : GeqH s.1 (fun x => RS.R b x + 1) := by
  have hbB : b < RS.K.B := (lt_add_one b).trans hb
  refine ⟨fun x hx hx1 hg => ?_, fun x hx hx1 hg => ?_, fun x hx hx1 hg j _ hj => ?_, fun x hx hx1 hg => ?_,
    fun σ ρ hB hg => ?_⟩
  · rw [s.2.1] at hg; exact yr_T (RS.R_lt1' hx hx1 hbB hg)
  · rw [s.2.1] at hg
    rw [s.2.2 x hx hx1 hg]
    obtain ⟨hT, h1⟩ := yr_T (RS.R_lt0' hx hx1 hbB hg)
    exact (ev_isSuccLimit_of_inE (geq_facts hx hx1 hT h1).2.2.2.1).add_one_lt (gmq_gt hx hx1 hT h1)
  · rw [s.2.1] at hg
    rw [s.2.2 x hx hx1 hg]
    exact yr_mono hx hx1 (RS.R_lt0' hx hx1 hbB hg) (Order.lt_add_one_iff.1 hj)
  · rw [s.2.1] at hg
    rw [s.2.2 x hx hx1 hg]
    exact yr_lt hx hx1 (RS.R_lt1' hx hx1 hbB hg) (lt_add_one _)
  · rw [s.2.1] at hg
    have h1σ : (1 : Ordinal.{0}) < σ := Lu.lu_one_lt_E hB.1
    obtain ⟨h1, h2⟩ := RS.R_pi' hB hbB hg
    obtain ⟨h3, h4⟩ := pi_add hB h1 (mem_TB_of_lt hB h1σ)
    exact ⟨h3, by rw [h4, h2, pi_lt hB h1σ]⟩

theorem gq_g_succ {b : Ordinal.{0}} (s : RS.GqSt b) (hb : b + 1 < RS.K.B) :
    (geqLimB s.1 (fun x => RS.R b x + 1) (RS.gqH_succ s hb)).g ≤ RS.K.gt (b + 1) := by
  rw [geqLimB_g, s.2.1]; exact RS.gt_le_succ b

/-- The successor step: the limit of the gated ladder over the layer of `b`. -/
noncomputable def gqStSucc (b : Ordinal.{0}) (s : RS.GqSt b) (hb : b + 1 < RS.K.B) : RS.GqSt (b + 1) :=
  ⟨(geqLimB s.1 (fun x => RS.R b x + 1) (RS.gqH_succ s hb)).mono (RS.gq_g_succ s hb), rfl, fun x _ hx1 _ => by
    show gq (RS.R b x + 1) x = gq (RS.R (b + 1) x) x
    rw [RS.succ b x hx1]⟩

/-- **The data of the union at a limit code `c > ε_{Ω₁+1}`**: all layers of the codes `b ∈ [ε_{Ω₁+1}, c)`. -/
noncomputable def gqFL (c : Ordinal.{0}) (hl : IsSuccLimit c) (hEc : gfE < c) (hc : c < RS.K.B)
    (IH : ∀ b, gfE ≤ b → b < c → RS.GqSt b) : YrUF (RS.K.gt c) where
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
  o_lt := fun b x hx hx1 hg hgb => RS.R_mono' hx hx1 hc b.2.2 hgb hg
  l_N := fun x hx hx1 hg => RS.R_lt0' hx hx1 hc hg
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
noncomputable def gqStLim (c : Ordinal.{0}) (hl : IsSuccLimit c) (hEc : gfE < c) (hc : c < RS.K.B)
    (IH : ∀ b, gfE ≤ b → b < c → RS.GqSt b) : RS.GqSt c :=
  ⟨yrLimB (RS.gqFL c hl hEc hc IH), rfl, fun _ _ _ _ => rfl⟩

/-- **The recursion over the codes `c ∈ [ε_{Ω₁+1}, ε_{Ω₁+1}²)`.** -/
noncomputable def gqRec (c : Ordinal.{0}) : gfE ≤ c → c < RS.K.B → RS.GqSt c :=
  Ordinal.limitRecOn (motive := fun c => gfE ≤ c → c < RS.K.B → RS.GqSt c) c
    (fun h _ => absurd h (not_le.2 eW_E.pos))
    (fun b ih h hc => if hb : gfE ≤ b then RS.gqStSucc b (ih hb ((lt_add_one b).trans hc)) hc
      else (gsm_not_E_le_succ h hb).elim)
    (fun c hl ih h hc => if hE : c = gfE then RS.gqSt0 c hE
      else RS.gqStLim c hl (lt_of_le_of_ne h (Ne.symm hE)) hc (fun b hb1 hb2 => ih b hb2 hb1 (hb2.trans hc)))

theorem gqRec_succ (b : Ordinal.{0}) (hb : gfE ≤ b) (h : gfE ≤ b + 1) (hc : b + 1 < RS.K.B) :
    RS.gqRec (b + 1) h hc = RS.gqStSucc b (RS.gqRec b hb ((lt_add_one b).trans hc)) hc := by
  unfold YrRS.gqRec; rw [Ordinal.limitRecOn_add_one, dif_pos hb]

theorem gqRec_E (h : gfE ≤ gfE) (hc : gfE < RS.K.B) : RS.gqRec gfE h hc = RS.gqSt0 gfE rfl := by
  unfold YrRS.gqRec; rw [Ordinal.limitRecOn_limit _ _ _ _ eW_lim, dif_pos rfl]

theorem gqRec_lim {c : Ordinal.{0}} (hl : IsSuccLimit c) (hEc : gfE < c) (h : gfE ≤ c) (hc : c < RS.K.B) :
    RS.gqRec c h hc = RS.gqStLim c hl hEc hc (fun b hb1 hb2 => RS.gqRec b hb1 (hb2.trans hc)) := by
  unfold YrRS.gqRec; rw [Ordinal.limitRecOn_limit _ _ _ _ hl, dif_neg hEc.ne']

/-- **THE GATED LAYER OF THE CODE `c`** (`ε_{Ω₁+1} ≤ c < ε_{Ω₁+1}²`). -/
noncomputable def gqL (c : Ordinal.{0}) (h : gfE ≤ c) (hc : c < RS.K.B) : GdB := (RS.gqRec c h hc).1

theorem gqL_g {c : Ordinal.{0}} (h : gfE ≤ c) (hc : c < RS.K.B) : (RS.gqL c h hc).g = RS.K.gt c :=
  (RS.gqRec c h hc).2.1

theorem gqL_E {c x : Ordinal.{0}} (h : gfE ≤ c) (hc : c < RS.K.B) (hx : InE x) (hx1 : x < Om1) (hg : RS.K.gt c < x) :
    (RS.gqL c h hc).K.E x = gq (RS.R c x) x := (RS.gqRec c h hc).2.2 x hx hx1 hg

theorem gqL_top {c x : Ordinal.{0}} (h : gfE ≤ c) (hc : c < RS.K.B) (hx : InE x) (hx1 : x < Om1) (hg : RS.K.gt c < x) :
    (RS.gqL c h hc).K.sys.top x = gq (RS.R c x) x := by
  have hg' : (RS.gqL c h hc).g < x := by rw [RS.gqL_g]; exact hg
  rw [(RS.gqL c h hc).K.top_eq x hx hx1 hg', ← RS.gqL_E h hc hx hx1 hg]
  exact (RS.gqL c h hc).ek x hx hx1 hg'


/-! ## Below `Γ_{Ω₁+1+ε_{Ω₁+1}}` -/

theorem gqK_gfAt (Z : Ordinal.{0}) : gfAt Z ⊆ RS.K.At Z := by
  rintro s ⟨c, hc, hg, rfl⟩
  exact ⟨c, hc.trans RS.E_lt, by show RS.K.gt c < Z; rw [RS.gt_lowE c hc]; exact hg, rfl⟩

theorem gfCl_of_giK {Z x : Ordinal.{0}} (hx : GxCl Z (RS.K.At Z) x) : x < gfV → GxCl Z (gfAt Z) x := by
  induction hx with
  | small h => exact fun _ => GxCl.small h
  | om => exact fun _ => GxCl.om
  | @atom s hs =>
    intro h
    obtain ⟨c, -, hgc, rfl⟩ := hs
    have hcE : c < gfE := gcG_lt_iff.1 h
    have hgc' : RS.K.gt c < Z := hgc
    rw [RS.gt_lowE c hcE] at hgc'
    exact GxCl.atom (gfG_atom hcE hgc')
  | @add x y _ _ ihx ihy =>
    exact fun h => GxCl.add (ihx (lt_of_le_of_lt le_self_add h)) (ihy (lt_of_le_of_lt le_add_self h))
  | @phi x y _ _ ihx ihy =>
    exact fun h => GxCl.phi (ihx (lt_of_le_of_lt (left_le_veblen x y) h))
      (ihy (lt_of_le_of_lt (right_le_veblen x y) h))

/-- **`Θ_y` with the atoms of `RS.K` is `Θ_y` with `Gf.gfAt` up to `Γ_{Ω₁+1+ε_{Ω₁+1}}`.** -/
theorem gqTh_eq_gf {y c : Ordinal.{0}} (hc : c ≤ gfV) : gxTh y (RS.K.At y) c = gxTh y (gfAt y) c :=
  ggOtp_congr c fun _ hx => ⟨fun h => RS.gfCl_of_giK h (hx.trans_le hc), fun h => h.mono le_rfl (RS.gqK_gfAt y)⟩

/-- **The code `ε_{Ω₁+1}`** reads `Γ_{Ω₁+1+ε_{Ω₁+1}}` with the atoms of `RS.K`. -/
theorem gqEB_codes (S : InaccSeq.{0}) :
    (∀ y, SC y → y < Om 1 → ghEB.K.E y = gxTh y (RS.K.At y) (gcG gfE)) ∧ GsmPolyG RS.K ghEB.K.sys (gcG gfE) := by
  have hK : ∀ (i : ghF0.I) y, SC y → y < Om 1 → ghF0.gi i < y →
      (ghF0.K i).K.E y = gxTh y (RS.K.At y) (gcG (1 + i.1)) := fun i y hy hy1 hi => by
    rw [RS.gqTh_eq_gf (gfT_le i.2)]
    exact (gfB_codes S i.1 i.2).1 y hy hy1 hi
  have hKP : ∀ i : ghF0.I, GsmPolyG RS.K (ghF0.K i).K.sys (gcG (1 + i.1)) := fun i Z d hg hd hdE => by
    have hdV : d < gfV := hdE.trans_le (gfT_le i.2)
    obtain ⟨s, hs⟩ := (gfB_codes S i.1 i.2).2 Z d hg (RS.gfCl_of_giK hd hdV) hdE
    refine ⟨s, fun y hy hy1 hZy => ⟨(hs y hy hy1 hZy).1, ?_⟩⟩
    have e2 := (hs y hy hy1 hZy).2
    rw [← RS.gqTh_eq_gf hdV.le] at e2
    exact e2
  have h := gsmU_codesH (K := RS.K) ghF0 (fun i => 1 + i.1) eW_lim RS.E_lt.le hK hKP (fun i => (gfT_lt i.2).le)
    fun b hb Z _ _ hgb => ⟨⟨b, hb⟩, by
      show gtc b < Z
      have hgb' : RS.K.gt b < Z := hgb
      rwa [RS.gt_lowE b hb] at hgb', le_add_self⟩
  exact ⟨fun y hy hy1 => h.1 y hy hy1 hy.1, h.2⟩

/-! ## The readings of all layers -/

/-- The reading statement at the code `c`. -/
def GqLC (c : Ordinal.{0}) (h : gfE ≤ c) (hc : c < RS.K.B) : Prop :=
  (∀ y, SC y → y < Om 1 → RS.K.gt c < y → (RS.gqL c h hc).K.E y = gxTh y (RS.K.At y) (gcG c)) ∧
    GsmPolyG RS.K (RS.gqL c h hc).K.sys (gcG c)

theorem gqL_atom {c Z : Ordinal.{0}} (hc : c < RS.K.B) (hg : RS.K.gt c < Z) : GxCl Z (RS.K.At Z) (gcG c) :=
  GxCl.atom (gsmG_atom (K := RS.K) hc hg)

/-- **THE UNIFORMITY THEOREM** for every code `c ∈ [ε_{Ω₁+1}, ε_{Ω₁+1}²)`: the top of `RS.gqL c` reads `Γ_{Ω₁+1+c}` at
every strongly critical `y` above `RS.K.gt c`, and `RS.gqL c` has terms for every code below it over every base above
`RS.K.gt c`. -/
theorem gqL_codes (S : InaccSeq.{0}) : ∀ c (h : gfE ≤ c) (hc : c < RS.K.B), RS.GqLC c h hc := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH0 =>
  intro h hc
  rcases zero_or_succ_or_isSuccLimit c with rfl | ⟨b, hsb⟩ | hl
  · exact absurd h (not_le.2 eW_E.pos)
  · rw [succ_eq_add_one] at hsb
    subst hsb
    have hb : gfE ≤ b := by
      by_contra hb
      exact gsm_not_E_le_succ h hb
    have hbB : b < RS.K.B := (lt_add_one b).trans hc
    obtain ⟨ihE, ihP⟩ := IH0 b (lt_add_one b) hb hbB
    have hg0 : (RS.gqL b hb hbB).g = RS.K.gt b := RS.gqL_g hb hbB
    have hcl : ∀ Z, SC Z → (RS.gqL b hb hbB).g < Z → GxCl Z (RS.K.At Z) (gcG b) := fun Z _ hg => by
      rw [hg0] at hg; exact RS.gqL_atom hbB hg
    have hcO : Om 1 ≤ gcG b := (gcG_Om1_lt _).le
    have hKE : ∀ y, SC y → y < Om 1 → (RS.gqL b hb hbB).g < y →
        (RS.gqL b hb hbB).K.E y = gxTh y (RS.K.At y) (gcG b) :=
      fun y hy hy1 hg => ihE y hy hy1 (hg0 ▸ hg)
    have hQ : cQs (gcG b) = gcG (b + 1) := gc_cQs b
    have H := RS.gqH_succ (RS.gqRec b hb hbB) hc
    have eL : RS.gqL (b + 1) h hc = (geqLimB (RS.gqL b hb hbB) (fun x => RS.R b x + 1) H).mono
        (RS.gq_g_succ (RS.gqRec b hb hbB) hc) := by
      show (RS.gqRec (b + 1) h hc).1 = _
      rw [RS.gqRec_succ b hb h hc]; rfl
    rw [YrRS.GqLC, eL]
    refine ⟨fun y hy hy1 hby => ?_, fun Z d hg hd hdE => ?_⟩
    · show gq (RS.R b y + 1) y = _
      have hgy : (RS.gqL b hb hbB).g < y := by rw [hg0]; exact (RS.gt_le_succ b).trans_lt hby
      rw [gsmLim_top (e := fun x => RS.R b x + 1) hcl hKE H hy hy1 hgy, hQ]
    · have hP := (gsmLim_poly hcl hcO hKE H ihP).mono (RS.gq_g_succ (RS.gqRec b hb hbB) hc)
      rw [hQ] at hP
      exact hP Z d hg hd hdE
  · by_cases hE : c = gfE
    · subst hE
      have eL : RS.gqL gfE h hc = ghEB := by
        show (RS.gqRec gfE h hc).1 = _
        rw [RS.gqRec_E h hc]; rfl
      rw [YrRS.GqLC, eL, RS.gt_E]
      obtain ⟨h1, h2⟩ := RS.gqEB_codes S
      exact ⟨fun y hy hy1 _ => h1 y hy hy1, h2⟩
    have hEc : gfE < c := lt_of_le_of_ne h (Ne.symm hE)
    set F := RS.gqFL c hl hEc hc (fun b hb1 hb2 => RS.gqRec b hb1 (hb2.trans hc)) with hF
    have eL : RS.gqL c h hc = yrLimB F := by
      show (RS.gqRec c h hc).1 = _
      rw [RS.gqRec_lim hl hEc h hc]; rfl
    have IH : ∀ i : F.I, RS.GqLC i.1 i.2.1 (i.2.2.trans hc) := fun i => IH0 i.1 i.2.2 i.2.1 (i.2.2.trans hc)
    have hK : ∀ (i : F.I) y, SC y → y < Om 1 → F.gi i < y →
        (F.K i).K.E y = gxTh y (RS.K.At y) (gcG i.1) := fun i y hy hy1 hi => (IH i).1 y hy hy1 hi
    have hKP : ∀ i : F.I, GsmPolyG RS.K (F.K i).K.sys (gcG i.1) := fun i => (IH i).2
    have hcov : ∀ b, b < c → ∀ Z, SC Z → RS.K.gt c < Z → RS.K.gt b < Z → ∃ i : F.I, F.gi i < Z ∧ b ≤ i.1 := by
      intro b hb Z hZ _ hgb
      rcases lt_or_ge b gfE with hbE | hbE
      · exact ⟨⟨gfE, le_rfl, hEc⟩, by show RS.K.gt gfE < Z; rw [RS.gt_E]; exact hZ.1, hbE.le⟩
      · exact ⟨⟨b, hbE, hb⟩, hgb, le_rfl⟩
    have hres := yrU_codes (K := RS.K) F (fun i => i.1) hl hc.le hK hKP (fun i => i.2.2.le) hcov
    rw [YrRS.GqLC, eL]
    exact hres

end YrRS

end Googology.Trans.PoR.InaccPsi.R2.Yr

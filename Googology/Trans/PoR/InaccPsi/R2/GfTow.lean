import Googology.Trans.PoR.InaccPsi.R2.GfLim

/-!
# ONE GENERIC THEOREM: a gated layer for EVERY code `a < ε_{Ω₁+1}`, with top `Γ_{x+2+a(x)}`

By transfinite recursion on the code `a < ε_{Ω₁+1}` (`R2.GfSub`, hereditary Cantor normal forms in `Ω₁`, read with
`Ω₁ ↦ x`): `gfB 0` is the base of `R2.GdTow` (top `Γ_{x+2}`), the successor `a + 1` is the limit of the gated ladder
over `gfB a` with the term offset `1 + rdc a x + 1` (`R2.GeLad`, generic in the offset), and a limit code `a` is the
union of all `gfB b`, `b < a` (`R2.GfLim`, the witness from Lemma IMG for the logend term).  This extends `R2.GeTow`
(codes below `Ω₁^ω`) past `Ω₁^ω`: e.g. the codes `Ω₁^ω` (top `Γ_{x+x^ω}`), `Ω₁^{Ω₁}` (top `Γ_{x+x^x}`).

* `GfSt a`, `gfSt0`, `gfH_succ`, `gfStSucc`, `gfF`, `gfStLim`, `gfRec`;
* `gfB a ha` (**THE GATED LAYER OF THE CODE `a`**), `gfB_g`, `gfB_E` / `gfB_top`, `gfB_spec` (**the generic theorem
  in one statement**), `gfB_succ`, `gfB_lim`;
* instances: `rdc_pow` (`Ω₁^l` reads `x^{l(x)}`), `gfB_const`, `gfB_pow` (**top `Γ_{x + x^{l(x)}}`**), `gfB_Wom`
  (`Ω₁^ω`, the code where `R2.GeTow` stops: top `Γ_{x+x^ω}`), `gfB_WW` (`Ω₁^{Ω₁}`: top `Γ_{x+x^x}`).

No new axiom.  New definitions: `GfSt`, `gfSt0`, `gfStSucc`, `gfF`, `gfStLim`, `gfRec`, `gfB`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Ly Lu
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Ge

/-- The value of the recursion at a code `a`: a gated base with gtc `gtc a` and top `ϑˣ(Ω₁·Ω₁ + 1 + rdc a x)`
above the gate. -/
def GfSt (a : Ordinal.{0}) : Type 2 :=
  {B : GdB // B.g = gtc a ∧ ∀ x, InE x → x < Om1 → gtc a < x → B.K.E x = gq (1 + rdc a x) x}

/-- The start: `lpTB 1`, top `ϑˣ(Ω₁·Ω₁ + 1)`, gated at `0`. -/
noncomputable def gfSt0 : GfSt 0 :=
  ⟨GdB.ofLp (Lp.lpTB 1) 0, gtc_zero.symm, fun x _ _ _ => by
    show Lp.gk (0 + 1) x = gq (1 + rdc 0 x) x
    rw [rdc_zero, add_zero, zero_add, ← gq_nat, Nat.cast_one]⟩

theorem gfS_lt {a x : Ordinal.{0}} (ha : a < gfE) (hx : InE x) (hg : gtc a < x) : 1 + rdc a x + 1 < eN x :=
  (inE_indec (eN_E x)).add_lt (gfO_lt ha hx hg) (one_lt_omega0.trans (omega0_lt_inE (eN_E x)))

/-- **The term-offset limit hypothesis holds for every code**: over `gfB a`, the offset `1 + rdc a x + 1`. -/
theorem gfH_succ {a : Ordinal.{0}} (s : GfSt a) (ha : a + 1 < gfE) : GeqH s.1 (fun x => 1 + rdc a x + 1) := by
  have ha' : a < gfE := (lt_add_one a).trans ha
  refine ⟨fun x hx hx1 hg => ?_, fun x hx hx1 hg => ?_, fun x hx hx1 hg j _ hj => ?_, fun x hx hx1 hg => ?_,
    fun σ ρ hB hg => ?_⟩
  · rw [s.2.1] at hg; exact eN_T hx hx1 (gfS_lt ha' hx hg)
  · rw [s.2.1] at hg
    rw [s.2.2 x hx hx1 hg]
    obtain ⟨hT, h1⟩ := eN_T hx hx1 (gfO_lt ha' hx hg)
    exact (gfS_lt ha' hx hg).trans_le (geq_eN_le hx hx1 hT h1)
  · rw [s.2.1] at hg
    rw [s.2.2 x hx hx1 hg]
    exact geq_mono hx hx1 (gfO_lt ha' hx hg) (Order.lt_add_one_iff.1 hj)
  · rw [s.2.1] at hg
    rw [s.2.2 x hx hx1 hg]
    exact geq_lt hx hx1 (gfS_lt ha' hx hg) (lt_add_one _)
  · rw [s.2.1] at hg
    have h1σ : (1 : Ordinal.{0}) < σ := Lu.lu_one_lt_E hB.1
    obtain ⟨h1, h2⟩ := gfO_pi hB ha' hg
    obtain ⟨h3, h4⟩ := pi_add hB h1 (mem_TB_of_lt hB h1σ)
    exact ⟨h3, by show pi σ ρ (1 + rdc a ρ + 1) = 1 + rdc a σ + 1; rw [h4, h2, pi_lt hB h1σ]⟩

theorem gf_g_succ {a : Ordinal.{0}} (s : GfSt a) (ha : a + 1 < gfE) :
    (geqLimB s.1 (fun x => 1 + rdc a x + 1) (gfH_succ s ha)).g ≤ gtc (a + 1) := by
  rw [geqLimB_g, s.2.1]; exact (rdc_succ a ((lt_add_one a).trans ha) 0).2.1

/-- The successor step: the limit of the gated ladder over the base with the term offset `1 + rdc a x + 1`, gate
raised to `gtc (a + 1)`. -/
noncomputable def gfStSucc (a : Ordinal.{0}) (s : GfSt a) (ha : a + 1 < gfE) : GfSt (a + 1) :=
  ⟨(geqLimB s.1 (fun x => 1 + rdc a x + 1) (gfH_succ s ha)).mono (gf_g_succ s ha), rfl, fun x _ _ _ => by
    show gq (1 + rdc a x + 1) x = gq (1 + rdc (a + 1) x) x
    rw [(rdc_succ a ((lt_add_one a).trans ha) x).1, add_assoc]⟩

/-- The family of the layers of the smaller codes at a limit code. -/
noncomputable def gfF {a : Ordinal.{0}} (IH : ∀ b < a, GfSt b) : GfLimF a where
  K := fun b => (IH b.1 b.2).1
  g_le := fun b => (IH b.1 b.2).2.1.le
  E_eq := fun b x hx hx1 hbx => (IH b.1 b.2).2.2 x hx hx1 hbx

/-- The limit step: the gated union with the term-offset witness. -/
noncomputable def gfStLim (a : Ordinal.{0}) (hl : IsSuccLimit a) (ha : a < gfE) (IH : ∀ b < a, GfSt b) : GfSt a :=
  ⟨gfLimB a hl ha (gfF IH), rfl, fun _ _ _ _ => rfl⟩

/-- **The recursion** on the codes below `Ω₁^ω`. -/
noncomputable def gfRec (a : Ordinal.{0}) : a < gfE → GfSt a :=
  Ordinal.limitRecOn (motive := fun a => a < gfE → GfSt a) a (fun _ => gfSt0)
    (fun b ih h => gfStSucc b (ih ((lt_add_one b).trans h)) h)
    (fun b hb ih h => gfStLim b hb h (fun c hc => ih c hc (hc.trans h)))

/-- **THE GATED LAYER OF THE CODE `a`** (`a < Ω₁^ω`). -/
noncomputable def gfB (a : Ordinal.{0}) (ha : a < gfE) : GdB := (gfRec a ha).1

theorem gfB_g {a : Ordinal.{0}} (ha : a < gfE) : (gfB a ha).g = gtc a := (gfRec a ha).2.1

theorem gfB_E {a x : Ordinal.{0}} (ha : a < gfE) (hx : InE x) (hx1 : x < Om1) (hg : gtc a < x) :
    (gfB a ha).K.E x = gq (1 + rdc a x) x := (gfRec a ha).2.2 x hx hx1 hg

theorem gfB_top {a x : Ordinal.{0}} (ha : a < gfE) (hx : InE x) (hx1 : x < Om1) (hg : gtc a < x) :
    (gfB a ha).K.sys.top x = gq (1 + rdc a x) x := by
  rw [(gfB a ha).K.top_eq x hx hx1 (by rw [gfB_g]; exact hg), gfB_E ha hx hx1 hg]
  exact (gfO_facts ha hx hx1 hg).2.2.2.1

/-- **ONE GENERIC THEOREM** (the layers): for every code `a < Ω₁^ω` there is a gated base package (a gated layer with
EXACT, IMG, RS and the top witness as fields) with gtc `gtc a` (the largest `Ω₁`-digit of `a`) whose top is
`ϑˣ(Ω₁·Ω₁ + 1 + rdc a x) = Γ_{x+2+a[Ω₁:=x]}` at every base `x > gtc a`. -/
theorem gfB_spec : ∀ a : Ordinal.{0}, a < gfE → ∃ B : GdB, B.g = gtc a ∧
    ∀ x, InE x → x < Om1 → gtc a < x → B.K.E x = gq (1 + rdc a x) x ∧ B.K.sys.top x = gq (1 + rdc a x) x :=
  fun a ha => ⟨gfB a ha, gfB_g ha, fun x hx hx1 hg => ⟨gfB_E ha hx hx1 hg, gfB_top ha hx hx1 hg⟩⟩

theorem gfRec_succ (a : Ordinal.{0}) (ha : a + 1 < gfE) :
    gfRec (a + 1) ha = gfStSucc a (gfRec a ((lt_add_one a).trans ha)) ha := by
  unfold gfRec
  rw [Ordinal.limitRecOn_add_one]

theorem gfB_succ (a : Ordinal.{0}) (ha : a + 1 < gfE) :
    gfB (a + 1) ha = (geqLimB (gfB a ((lt_add_one a).trans ha)) (fun x => 1 + rdc a x + 1)
      (gfH_succ (gfRec a ((lt_add_one a).trans ha)) ha)).mono (gf_g_succ (gfRec a ((lt_add_one a).trans ha)) ha) := by
  show (gfRec (a + 1) ha).1 = _
  rw [gfRec_succ]
  rfl

theorem gfRec_lim {a : Ordinal.{0}} (hl : IsSuccLimit a) (ha : a < gfE) :
    gfRec a ha = gfStLim a hl ha (fun b hb => gfRec b (hb.trans ha)) := by
  unfold gfRec
  rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem gfB_lim {a : Ordinal.{0}} (hl : IsSuccLimit a) (ha : a < gfE) :
    gfB a ha = gfLimB a hl ha (gfF fun b hb => gfRec b (hb.trans ha)) := by
  show (gfRec a ha).1 = _
  rw [gfRec_lim hl ha]
  rfl

/-! ## Instances -/

theorem const_lt_eW {α : Ordinal.{0}} (hα : α < Om1) : α < gfE := hα.trans Om1_lt_eW

/-- **The tower of `R2.GdTow` is the constant part**: `gfB α` has top `ϑˣ(Ω₁·Ω₁ + 1 + α)` above `α`. -/
theorem gfB_const {α x : Ordinal.{0}} (hα : α < Om1) (hx : InE x) (hx1 : x < Om1) (hαx : α < x) :
    (gfB α (const_lt_eW hα)).K.sys.top x = gq (1 + α) x := by
  rw [gfB_top (const_lt_eW hα) hx hx1 (by rw [(rdc_const hα 0).2]; exact hαx), (rdc_const hα x).1]

/-- **`Ω₁^l` reads `x^{l(x)}`**, gate `max (gtc l) 1`. -/
theorem rdc_pow {l : Ordinal.{0}} (hl : l < gfE) (x : Ordinal.{0}) :
    rdc (Om1 ^ l) x = x ^ rdc l x ∧ gtc (Om1 ^ l) = max (gtc l) 1 := by
  obtain ⟨e1, e2⟩ := rdc_cnf hl one_ne_zero gf_one_lt_Om1 (opow_pos l (zero_lt_one.trans gf_one_lt_Om1)) x
  rw [mul_one, add_zero, rdc_zero, add_zero, mul_one] at e1
  rw [mul_one, add_zero, gtc_zero, max_eq_left zero_le] at e2
  exact ⟨e1, e2⟩

theorem one_add_pow {x L : Ordinal.{0}} (hx : InE x) (hL : L ≠ 0) : 1 + x ^ L = x ^ L := by
  refine one_add_of_omega0_le ((omega0_lt_inE hx).le.trans ?_)
  calc x = x ^ (1 : Ordinal.{0}) := (opow_one x).symm
    _ ≤ x ^ L := opow_le_opow_right hx.pos (one_le_iff_ne_zero.2 hL)

/-- **The code `Ω₁^l`** (`0 < l < ε_{Ω₁+1}`): top `ϑˣ(Ω₁·Ω₁ + x^{l(x)}) = Γ_{x + x^{l(x)}}` above the gate. -/
theorem gfB_pow {l x : Ordinal.{0}} (hl : l < gfE) (hl0 : l ≠ 0) (hx : InE x) (hx1 : x < Om1)
    (hg : max (gtc l) 1 < x) :
    (gfB (Om1 ^ l) (Om1_pow_lt_eW hl)).K.sys.top x = gq (x ^ rdc l x) x := by
  rw [gfB_top (Om1_pow_lt_eW hl) hx hx1 (by rw [(rdc_pow hl 0).2]; exact hg), (rdc_pow hl x).1,
    one_add_pow hx (rdc_pos hx hl0 hl).ne']

theorem omega_lt_eW : ω < gfE := omega_lt_Om1.trans Om1_lt_eW

/-- **The code `Ω₁^ω`** (where `R2.GeTow` stops): top `Γ_{x + x^ω}` at every `ε`-number base. -/
theorem gfB_Wom {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    (gfB (Om1 ^ ω) (Om1_pow_lt_eW omega_lt_eW)).K.sys.top x = gq (x ^ ω) x := by
  have hc := rdc_const omega_lt_Om1 x
  have h := gfB_pow omega_lt_eW omega0_ne_zero hx hx1
    (by rw [(rdc_const omega_lt_Om1 0).2]; exact max_lt (omega0_lt_inE hx) (Lu.lu_one_lt_E hx))
  rwa [hc.1] at h

/-- **The code `Ω₁^{Ω₁}`**: top `Γ_{x + x^x}` at every `ε`-number base. -/
theorem gfB_WW {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    (gfB (Om1 ^ Om1) (Om1_pow_lt_eW Om1_lt_eW)).K.sys.top x = gq (x ^ x) x := by
  have hc : rdc Om1 x = x ∧ gtc Om1 = 1 := by
    have h := rdc_pow (l := 1) (gf_one_lt_Om1.trans Om1_lt_eW) x
    rw [opow_one, (rdc_const gf_one_lt_Om1 x).1, (rdc_const gf_one_lt_Om1 0).2, max_self, opow_one] at h
    exact h
  have h := gfB_pow Om1_lt_eW Om1_ne' hx hx1 (by rw [hc.2, max_self]; exact Lu.lu_one_lt_E hx)
  rwa [hc.1] at h

end Googology.Trans.PoR.InaccPsi.R2.Gf

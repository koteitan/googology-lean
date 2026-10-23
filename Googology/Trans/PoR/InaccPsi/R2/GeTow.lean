import Googology.Trans.PoR.InaccPsi.R2.GeLim

/-!
# ONE GENERIC THEOREM: a gated layer for EVERY code `a < Ω₁^ω`, with top `ϑˣ(Ω₁·Ω₁ + 1 + a[Ω₁ := x]) = Γ_{x+2+a(x)}`

By transfinite recursion on the code `a < Ω₁^ω` (`R2.GeSub`): `geB 0` is the base of `R2.GdTow` (top `Γ_{x+2}`), the
successor `a + 1` is the limit of the gated ladder over `geB a` with the TERM offset `1 + sbc a x + 1` (`R2.GeLad`), and
a limit code `a` is the union of all `geB b`, `b < a` (`R2.GeLim`, the witness from the linear logend of `sbc a x`).
Every field of a layer (EXACT, IMG, RS, the top witness) comes with the structure `GdB`.

* `GeSt a` (a gated base with gate `gate a` and top `ϑˣ(Ω₁·Ω₁ + 1 + sbc a x)` above the gate), `geSt0`, `geH_succ`
  (**the term-offset limit hypothesis holds for every code**), `geStSucc`, `geF`, `geStLim`, `geRec`;
* `geB a ha` (**THE GATED LAYER OF THE CODE `a`**), `geB_g` (gate `gate a`), `geB_E` / `geB_top` (**top
  `ϑˣ(Ω₁·Ω₁ + 1 + sbc a x)` at every base above the gate**), `geB_spec` (the generic theorem in one statement),
  `geB_succ`, `geB_lim` (the recursion equations);
* the instances: `geB_const` (a code `α < Ω₁` reads `α`: the tower of `R2.GdTow`), `geB_diag` (the code `Ω₁` reads
  `x`: `Γ_{x+x}`), `geB_diag1` (the code `Ω₁ + 1` reads `x + 1`: **`Γ_{x+x+1}`**).

No new axiom.  New definitions: `GeSt`, `geSt0`, `geStSucc`, `geF`, `geStLim`, `geRec`, `geB`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ge

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Ly Lu
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd

/-- The value of the recursion at a code `a`: a gated base with gate `gate a` and top `ϑˣ(Ω₁·Ω₁ + 1 + sbc a x)`
above the gate. -/
def GeSt (a : Ordinal.{0}) : Type 2 :=
  {B : GdB // B.g = gate a ∧ ∀ x, InE x → x < Om1 → gate a < x → B.K.E x = gq (1 + sbc a x) x}

/-- The start: `lpTB 1`, top `ϑˣ(Ω₁·Ω₁ + 1)`, gated at `0`. -/
noncomputable def geSt0 : GeSt 0 :=
  ⟨GdB.ofLp (Lp.lpTB 1) 0, gate_zero.symm, fun x _ _ _ => by
    show Lp.gk (0 + 1) x = gq (1 + sbc 0 x) x
    rw [sb_zero, add_zero, zero_add, ← gq_nat, Nat.cast_one]⟩

theorem geS_lt {a x : Ordinal.{0}} (ha : a < geW) (hx : InE x) (hg : gate a < x) : 1 + sbc a x + 1 < eN x :=
  (inE_indec (eN_E x)).add_lt (geO_lt ha hx hg) (one_lt_omega0.trans (omega0_lt_inE (eN_E x)))

/-- **The term-offset limit hypothesis holds for every code**: over `geB a`, the offset `1 + sbc a x + 1`. -/
theorem geH_succ {a : Ordinal.{0}} (s : GeSt a) (ha : a + 1 < geW) : GeqH s.1 (fun x => 1 + sbc a x + 1) := by
  have ha' : a < geW := (lt_add_one a).trans ha
  refine ⟨fun x hx hx1 hg => ?_, fun x hx hx1 hg => ?_, fun x hx hx1 hg j _ hj => ?_, fun x hx hx1 hg => ?_,
    fun σ ρ hB hg => ?_⟩
  · rw [s.2.1] at hg; exact eN_T hx hx1 (geS_lt ha' hx hg)
  · rw [s.2.1] at hg
    rw [s.2.2 x hx hx1 hg]
    obtain ⟨hT, h1⟩ := eN_T hx hx1 (geO_lt ha' hx hg)
    exact (geS_lt ha' hx hg).trans_le (geq_eN_le hx hx1 hT h1)
  · rw [s.2.1] at hg
    rw [s.2.2 x hx hx1 hg]
    exact geq_mono hx hx1 (geO_lt ha' hx hg) (Order.lt_add_one_iff.1 hj)
  · rw [s.2.1] at hg
    rw [s.2.2 x hx hx1 hg]
    exact geq_lt hx hx1 (geS_lt ha' hx hg) (lt_add_one _)
  · rw [s.2.1] at hg
    have h1σ : (1 : Ordinal.{0}) < σ := Lu.lu_one_lt_E hB.1
    obtain ⟨h1, h2⟩ := geO_pi hB ha' hg
    obtain ⟨h3, h4⟩ := pi_add hB h1 (mem_TB_of_lt hB h1σ)
    exact ⟨h3, by show pi σ ρ (1 + sbc a ρ + 1) = 1 + sbc a σ + 1; rw [h4, h2, pi_lt hB h1σ]⟩

theorem ge_g_succ {a : Ordinal.{0}} (s : GeSt a) (ha : a + 1 < geW) :
    (geqLimB s.1 (fun x => 1 + sbc a x + 1) (geH_succ s ha)).g ≤ gate (a + 1) := by
  rw [geqLimB_g, s.2.1]; exact (sb_succ ha 0).2.1

/-- The successor step: the limit of the gated ladder over the base with the term offset `1 + sbc a x + 1`, gate
raised to `gate (a + 1)`. -/
noncomputable def geStSucc (a : Ordinal.{0}) (s : GeSt a) (ha : a + 1 < geW) : GeSt (a + 1) :=
  ⟨(geqLimB s.1 (fun x => 1 + sbc a x + 1) (geH_succ s ha)).mono (ge_g_succ s ha), rfl, fun x _ _ _ => by
    show gq (1 + sbc a x + 1) x = gq (1 + sbc (a + 1) x) x
    rw [(sb_succ ha x).1, add_assoc]⟩

/-- The family of the layers of the smaller codes at a limit code. -/
noncomputable def geF {a : Ordinal.{0}} (IH : ∀ b < a, GeSt b) : GeLimF a where
  K := fun b => (IH b.1 b.2).1
  g_le := fun b => (IH b.1 b.2).2.1.le
  E_eq := fun b x hx hx1 hbx => (IH b.1 b.2).2.2 x hx hx1 hbx

/-- The limit step: the gated union with the term-offset witness. -/
noncomputable def geStLim (a : Ordinal.{0}) (hl : IsSuccLimit a) (ha : a < geW) (IH : ∀ b < a, GeSt b) : GeSt a :=
  ⟨geLimB a hl ha (geF IH), rfl, fun _ _ _ _ => rfl⟩

/-- **The recursion** on the codes below `Ω₁^ω`. -/
noncomputable def geRec (a : Ordinal.{0}) : a < geW → GeSt a :=
  Ordinal.limitRecOn (motive := fun a => a < geW → GeSt a) a (fun _ => geSt0)
    (fun b ih h => geStSucc b (ih ((lt_add_one b).trans h)) h)
    (fun b hb ih h => geStLim b hb h (fun c hc => ih c hc (hc.trans h)))

/-- **THE GATED LAYER OF THE CODE `a`** (`a < Ω₁^ω`). -/
noncomputable def geB (a : Ordinal.{0}) (ha : a < geW) : GdB := (geRec a ha).1

theorem geB_g {a : Ordinal.{0}} (ha : a < geW) : (geB a ha).g = gate a := (geRec a ha).2.1

theorem geB_E {a x : Ordinal.{0}} (ha : a < geW) (hx : InE x) (hx1 : x < Om1) (hg : gate a < x) :
    (geB a ha).K.E x = gq (1 + sbc a x) x := (geRec a ha).2.2 x hx hx1 hg

theorem geB_top {a x : Ordinal.{0}} (ha : a < geW) (hx : InE x) (hx1 : x < Om1) (hg : gate a < x) :
    (geB a ha).K.sys.top x = gq (1 + sbc a x) x := by
  rw [(geB a ha).K.top_eq x hx hx1 (by rw [geB_g]; exact hg), geB_E ha hx hx1 hg]
  exact (geO_facts ha hx hx1 hg).2.2.2.1

/-- **ONE GENERIC THEOREM** (the layers): for every code `a < Ω₁^ω` there is a gated base package (a gated layer with
EXACT, IMG, RS and the top witness as fields) with gate `gate a` (the largest `Ω₁`-digit of `a`) whose top is
`ϑˣ(Ω₁·Ω₁ + 1 + sbc a x) = Γ_{x+2+a[Ω₁:=x]}` at every base `x > gate a`. -/
theorem geB_spec : ∀ a : Ordinal.{0}, a < geW → ∃ B : GdB, B.g = gate a ∧
    ∀ x, InE x → x < Om1 → gate a < x → B.K.E x = gq (1 + sbc a x) x ∧ B.K.sys.top x = gq (1 + sbc a x) x :=
  fun a ha => ⟨geB a ha, geB_g ha, fun x hx hx1 hg => ⟨geB_E ha hx hx1 hg, geB_top ha hx hx1 hg⟩⟩

theorem geRec_succ (a : Ordinal.{0}) (ha : a + 1 < geW) :
    geRec (a + 1) ha = geStSucc a (geRec a ((lt_add_one a).trans ha)) ha := by
  unfold geRec
  rw [Ordinal.limitRecOn_add_one]

theorem geB_succ (a : Ordinal.{0}) (ha : a + 1 < geW) :
    geB (a + 1) ha = (geqLimB (geB a ((lt_add_one a).trans ha)) (fun x => 1 + sbc a x + 1)
      (geH_succ (geRec a ((lt_add_one a).trans ha)) ha)).mono (ge_g_succ (geRec a ((lt_add_one a).trans ha)) ha) := by
  show (geRec (a + 1) ha).1 = _
  rw [geRec_succ]
  rfl

theorem geRec_lim {a : Ordinal.{0}} (hl : IsSuccLimit a) (ha : a < geW) :
    geRec a ha = geStLim a hl ha (fun b hb => geRec b (hb.trans ha)) := by
  unfold geRec
  rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem geB_lim {a : Ordinal.{0}} (hl : IsSuccLimit a) (ha : a < geW) :
    geB a ha = geLimB a hl ha (geF fun b hb => geRec b (hb.trans ha)) := by
  show (geRec a ha).1 = _
  rw [geRec_lim hl ha]
  rfl

/-! ## Instances -/

theorem Om1_lt_W : Om1 < geW := by
  rw [lt_W_iff]
  refine ⟨2, ?_⟩
  unfold oP
  rw [show ((2 : ℕ) : Ordinal.{0}) = 1 + 1 by norm_num, opow_add, opow_one]
  exact lt_mul_of_one_lt_right (Ordinal.omega_pos 1) (Lu.lu_one_lt_E Rj.rj_Om1_inE)

theorem const_lt_W {α : Ordinal.{0}} (hα : α < Om1) : α < geW := hα.trans Om1_lt_W

/-- A constant code `α < Ω₁` reads `α` and has gate `α`. -/
theorem sb_const {α : Ordinal.{0}} (hα : α < Om1) (x : Ordinal.{0}) : sbc α x = α ∧ gate α = α := by
  have h : α < oP 1 := by unfold oP; simpa using hα
  rw [(sbc_eq h x).1, (sbc_eq h x).2]
  exact sbN_one α x

/-- **The tower of `R2.GdTow` is the constant part**: `geB α` has top `ϑˣ(Ω₁·Ω₁ + 1 + α)` above `α`. -/
theorem geB_const {α x : Ordinal.{0}} (hα : α < Om1) (hx : InE x) (hx1 : x < Om1) (hαx : α < x) :
    (geB α (const_lt_W hα)).K.sys.top x = gq (1 + α) x := by
  rw [geB_top (const_lt_W hα) hx hx1 (by rw [(sb_const hα 0).2]; exact hαx), (sb_const hα x).1]

theorem sb_Om1 (x : Ordinal.{0}) : sbc Om1 x = x ∧ gate Om1 = 1 := by
  have h : Om1 < oP 2 := by
    unfold oP
    rw [show ((2 : ℕ) : Ordinal.{0}) = 1 + 1 by norm_num, opow_add, opow_one]
    exact lt_mul_of_one_lt_right (Ordinal.omega_pos 1) (Lu.lu_one_lt_E Rj.rj_Om1_inE)
  have hd : Om1 / oP 1 = 1 := by
    unfold oP; rw [Nat.cast_one, opow_one]; exact Ordinal.div_self Om1_ne
  have hm : Om1 % oP 1 = 0 := by
    unfold oP; rw [Nat.cast_one, opow_one]; exact Ordinal.mod_self Om1
  rw [(sbc_eq h x).1, (sbc_eq h x).2]
  refine ⟨?_, ?_⟩
  · show x ^ ((1 : ℕ) : Ordinal.{0}) * (Om1 / oP 1) + sbN 1 (Om1 % oP 1) x = x
    rw [hd, hm, (sbN_one 0 x).1, Nat.cast_one, opow_one, mul_one, add_zero]
  · show max (Om1 / oP 1) (gtN 1 (Om1 % oP 1)) = 1
    rw [hd, hm, (sbN_one 0 x).2]; exact max_eq_left zero_le

/-- **The code `Ω₁` reads `x`**: `geB Ω₁` has top `Γ_{x+x} = ϑˣ(Ω₁·Ω₁ + x)` above `1`. -/
theorem geB_diag {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    (geB Om1 Om1_lt_W).K.sys.top x = gq x x := by
  rw [geB_top Om1_lt_W hx hx1 (by rw [(sb_Om1 0).2]; exact Lu.lu_one_lt_E hx), (sb_Om1 x).1,
    one_add_of_omega0_le (omega0_lt_inE hx).le]

theorem geW_indec : Indec geW := by
  unfold geW
  conv => arg 1; rw [← show ω ^ Om1 = Om1 from Rj.rj_Om1_inE]
  rw [← opow_mul]; exact indec_opow _

theorem Om1_succ_lt_W : Om1 + 1 < geW :=
  geW_indec.add_lt Om1_lt_W ((Lu.lu_one_lt_E Rj.rj_Om1_inE).trans Om1_lt_W)

/-- **The code `Ω₁ + 1` reads `x + 1`**: `geB (Ω₁+1)` has top `Γ_{x+x+1} = ϑˣ(Ω₁·Ω₁ + x + 1)` above `2`. -/
theorem geB_diag1 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    (geB (Om1 + 1) Om1_succ_lt_W).K.sys.top x = gq (x + 1) x := by
  obtain ⟨e1, -, e3⟩ := sb_succ Om1_succ_lt_W x
  have hg : gate (Om1 + 1) < x := by
    refine ((sb_succ Om1_succ_lt_W 0).2.2.trans_lt ?_)
    rw [(sb_Om1 0).2]
    exact (inE_indec hx).add_lt (Lu.lu_one_lt_E hx) (Lu.lu_one_lt_E hx)
  rw [geB_top Om1_succ_lt_W hx hx1 hg, e1, (sb_Om1 x).1, ← add_assoc,
    one_add_of_omega0_le (omega0_lt_inE hx).le]

end Googology.Trans.PoR.InaccPsi.R2.Ge

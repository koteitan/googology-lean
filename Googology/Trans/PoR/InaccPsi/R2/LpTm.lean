import Googology.Trans.PoR.InaccPsi.R2.LvGSys
import Googology.Trans.PoR.InaccPsi.R2.LxTm

/-!
# The ladder over a new base: the grammar of the staged tower over a base layer `K`, the tops, EXACT, representation

Every construction of the earlier rounds starts from the base `x` (a `υ`-point) and builds tops `f(x)`.  Here the
base is **any layer `K`** (`R2.XtLay`) whose top `E_K(x) = ω^{E_K(x)}` is an `ε`-number in `Tˣ` (`LpB`): the terms of
`K` become atoms, and the staged tower of levels of `R2.LvGTm` is rebuilt over them.

* `LpB` (**the base package**: a layer `K`, `E_K(x) ∈ E`, `E_K(x) ∈ Tˣ`);
* `gP B n x` (**the tops over the base**: `gP 0 x = E_K(x)`, `gP (n+1) x = ϑˣ(Ω₁·gP n x)`), `gP_facts`, `gP_lt_succ`,
  `lp_lt_top`;
* `LpT B` (**the terms**: constants, the base `x`, the terms `ak k` of `K`, the atom `tp` with value `E_K(x)`,
  `ϑˣ(Ω₁·b + t)` for a constant level `1 ≤ b < x`, `ϑˣ(Ω₁·l(x) + t)` for a level term `l` that is not base-free, sums,
  `ω`-powers), the stage, `gTm n` (the term of `gP n`, stage `n+1`);
* `LpT.lp_TB` (**a value lies in `Tˣ` below the top of its stage**), `LpT.noB_lt` (**at a `υ`-point a base-free term
  has value below the base**: for a constant term of `K` by Lemma EXACT of `K` and `Tᵗ[σ] ∩ τ = σ`);
* `lp_quot`, `lp_rep` (**every ordinal below `gP n x` is the value of a term of stage `≤ n`**, at a `υ`-point where
  every value below `E_K(x)` is a value of `K`);
* `LpT.pi` (**Lemma EXACT**: from the EXACT of `K` and of `E_K` and the cited `ϑ`-steps), `LpT.uni_le`, `lp_small`;
* `LpT.ofLx` (the terms of `R2.LxTm` over `K` are terms here, with the same values).

No new axiom.

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Lp

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Lx

/-- **The base package**: a layer `K` whose top exponent `E_K(x)` is an `ε`-number in `Tˣ`. -/
structure LpB where
  K : XtLay
  ek : LxEK K
  mem : ∀ x, InE x → x < Om1 → K.E x ∈ Tset x

/-- **The tops over the base**: `gP 0 x = E_K(x)`, `gP (n+1) x = ϑˣ(Ω₁·gP n x)`. -/
noncomputable def gP (B : LpB) : ℕ → Ordinal.{0} → Ordinal.{0}
  | 0, x => B.K.E x
  | n + 1, x => vt x (Om1 * gP B n x)

/-- **The terms over the base layer.** -/
inductive LpT (B : LpB) : Type 1
  | cst : Ordinal.{0} → LpT B
  | bs : LpT B
  | ak : B.K.sys.Tm → LpT B
  | tp : LpT B
  | th0 : Ordinal.{0} → LpT B → LpT B
  | tl : LpT B → LpT B → LpT B
  | sm : LpT B → LpT B → LpT B
  | pw : LpT B → LpT B

namespace LpT

variable {B : LpB}

/-- The value at the base `x`. -/
noncomputable def val : LpT B → Ordinal.{0} → Ordinal.{0}
  | cst a, _ => a
  | bs, x => x
  | ak k, x => B.K.sys.val k x
  | tp, x => B.K.E x
  | th0 b t, x => vt x (Om1 * b + val t x)
  | tl l t, x => vt x (Om1 * val l x + val t x)
  | sm a b, x => val a x + val b x
  | pw t, x => ω ^ val t x

/-- The constants. -/
def cs : LpT B → List Ordinal.{0}
  | cst a => [a]
  | bs => []
  | ak k => B.K.sys.cs k
  | tp => []
  | th0 b t => b :: cs t
  | tl l t => cs l ++ cs t
  | sm a b => cs a ++ cs b
  | pw t => cs t

/-- Base-free: built from constants and constant terms of `K` by sums and powers. -/
def noB : LpT B → Prop
  | cst _ => True
  | bs => False
  | ak k => ∀ y z, B.K.sys.val k y = B.K.sys.val k z
  | tp => False
  | th0 _ _ => False
  | tl _ _ => False
  | sm a b => noB a ∧ noB b
  | pw t => noB t

/-- The side condition: constants below the base, constant levels at least `1`, level terms not base-free. -/
def CBt : LpT B → Ordinal.{0} → Prop
  | cst a, x => a < x
  | bs, _ => True
  | ak k, x => B.K.sys.CB k x
  | tp, _ => True
  | th0 b t, x => 1 ≤ b ∧ b < x ∧ CBt t x
  | tl l t, x => ¬ noB l ∧ CBt l x ∧ CBt t x
  | sm a b, x => CBt a x ∧ CBt b x
  | pw t, x => CBt t x

/-- The stage: the nesting depth of the levels (`tp` has stage `1`). -/
def stage : LpT B → ℕ
  | cst _ => 0
  | bs => 0
  | ak _ => 0
  | tp => 1
  | th0 _ t => max 1 (stage t)
  | tl l t => max (stage l + 1) (stage t)
  | sm a b => max (stage a) (stage b)
  | pw t => stage t

@[simp] theorem val_cst (a x : Ordinal.{0}) : val (cst a : LpT B) x = a := rfl
@[simp] theorem val_bs (x : Ordinal.{0}) : val (bs : LpT B) x = x := rfl
@[simp] theorem val_ak (k : B.K.sys.Tm) (x : Ordinal.{0}) : val (ak k) x = B.K.sys.val k x := rfl
@[simp] theorem val_tp (x : Ordinal.{0}) : val (tp : LpT B) x = B.K.E x := rfl
@[simp] theorem val_th0 (b : Ordinal.{0}) (t : LpT B) (x : Ordinal.{0}) :
    val (th0 b t) x = vt x (Om1 * b + val t x) := rfl
@[simp] theorem val_tl (l t : LpT B) (x : Ordinal.{0}) :
    val (tl l t) x = vt x (Om1 * val l x + val t x) := rfl
@[simp] theorem val_sm (a b : LpT B) (x : Ordinal.{0}) : val (sm a b) x = val a x + val b x := rfl
@[simp] theorem val_pw (t : LpT B) (x : Ordinal.{0}) : val (pw t) x = ω ^ val t x := rfl

/-- A base-free term has constant value. -/
theorem noB_val : ∀ t : LpT B, noB t → ∀ x y, val t x = val t y
  | .cst _, _, _, _ => rfl
  | .bs, h, _, _ => absurd h id
  | .ak k, h, x, y => h x y
  | .tp, h, _, _ => absurd h id
  | .th0 _ _, h, _, _ => absurd h id
  | .tl _ _, h, _, _ => absurd h id
  | .sm a b, h, x, y => by simp only [val_sm, noB_val a h.1 x y, noB_val b h.2 x y]
  | .pw t, h, x, y => by simp only [val_pw, noB_val t h x y]

/-- The side condition depends only on the listed constants. -/
theorem cbt_iff {t : LpT B} {x y : Ordinal.{0}} (h : CBt t x)
    (hy : ∀ c ∈ cs t, c < y) : CBt t y := by
  induction t with
  | cst a => exact hy a (by simp [cs])
  | bs => trivial
  | ak k => exact B.K.sys.cb_iff k x y h hy
  | tp => trivial
  | th0 b t ih =>
      refine ⟨h.1, hy b (by simp [cs]), ?_⟩
      exact ih h.2.2 (fun c hc => hy c (by simp [cs, hc]))
  | tl l t ihl iht =>
      exact ⟨h.1, ihl h.2.1 (fun c hc => hy c (by simp [cs, hc])),
        iht h.2.2 (fun c hc => hy c (by simp [cs, hc]))⟩
  | sm a b iha ihb =>
      exact ⟨iha h.1 (fun c hc => hy c (by simp [cs, hc])),
        ihb h.2 (fun c hc => hy c (by simp [cs, hc]))⟩
  | pw t ih => exact ih h (fun c hc => hy c (by simpa [cs] using hc))

/-- All explicit constants and level parameters are below the base. -/
theorem cbt_cst {ρ : Ordinal.{0}} {s : LpT B} (hs : CBt s ρ) : ∀ c ∈ cs s, c < ρ := by
  induction s with
  | cst a => intro c hc; simp [cs] at hc; subst c; exact hs
  | bs => intro c hc; simp [cs] at hc
  | ak k => exact B.K.sys.cb_cst k ρ hs
  | tp => intro c hc; simp [cs] at hc
  | th0 b t ih =>
      intro c hc
      simp only [cs, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact hs.2.1
      · exact ih hs.2.2 c hc
  | tl l t ihl iht =>
      intro c hc
      simp only [cs, List.mem_append] at hc
      rcases hc with hc | hc
      · exact ihl hs.2.1 c hc
      · exact iht hs.2.2 c hc
  | sm a b iha ihb =>
      intro c hc
      simp only [cs, List.mem_append] at hc
      rcases hc with hc | hc
      · exact iha hs.1 c hc
      · exact ihb hs.2 c hc
  | pw t ih => intro c hc; exact ih hs c (by simpa [cs] using hc)

/-- The side condition is monotone in the base. -/
theorem CBt.mono {s : LpT B} {x y : Ordinal.{0}} (hxy : x ≤ y) (hs : CBt s x) : CBt s y :=
  cbt_iff hs (fun c hc => (cbt_cst hs c hc).trans_le hxy)

/-- **At a `υ`-point a constant term of `K` has value below the base**: Lemma EXACT of `K` at the bases `x < ρ'`
(`ρ'` a `υ`-point above the value) and `Tᵗ[σ] ∩ τ = σ`. -/
theorem ak_const_lt {x : Ordinal.{0}} (hx : UpsPt x) (hx1 : x < Om1) {k : B.K.sys.Tm}
    (hn : ∀ y z, B.K.sys.val k y = B.K.sys.val k z) (hk : B.K.sys.CB k x) : B.K.sys.val k x < x := by
  have hxE := upsPt_inE hx
  set C := B.K.sys.val k x with hC
  have hC1 : C < Om1 := by
    have h1 := B.K.lt_top_E x hxE hx1 k hk
    rw [lx_top B.ek hxE hx1] at h1
    exact h1.trans (B.K.exp_lt x hxE hx1)
  have h11 : (1 : Ordinal.{0}) < Om1 := lt_of_le_of_lt (one_le_iff_pos.2 hxE.pos) hx1
  have hlt : x + C + 1 < Om1 := Om1_add_lt (Om1_add_lt hx1 hC1) h11
  have hpos : 0 < x + C + 1 := lt_of_le_of_lt zero_le (lt_add_one _)
  have hU := upsPt_upsilon hpos
  have hU1 : upsilon (x + C + 1) < Om1 := ups_lt_Om1 _ hlt
  have hle : x + C + 1 ≤ upsilon (x + C + 1) := upsilon_normal.strictMono.le_apply
  have hxu : x < upsilon (x + C + 1) :=
    lt_of_le_of_lt le_self_add (lt_of_lt_of_le (lt_add_one (x + C)) hle)
  have hCu : C < upsilon (x + C + 1) :=
    lt_of_le_of_lt le_add_self (lt_of_lt_of_le (lt_add_one (x + C)) hle)
  have hB : Bases x (upsilon (x + C + 1)) := ⟨hxE, upsPt_inE hU, hxu, hU1⟩
  have hex := (B.K.exact x _ hx hU hB k hk).1
  rw [hn (upsilon (x + C + 1)) x] at hex
  exact (TB_inter_lt hB hCu).1 hex

/-- A base-free term with constants below a `υ`-point `x` has value below `x`. -/
theorem noB_lt {x : Ordinal.{0}} (hx : UpsPt x) (hx1 : x < Om1) : ∀ t : LpT B, noB t → CBt t x → val t x < x
  | .cst _, _, h => h
  | .bs, h, _ => absurd h id
  | .ak _, hn, h => ak_const_lt hx hx1 hn h
  | .tp, h, _ => absurd h id
  | .th0 _ _, h, _ => absurd h id
  | .tl _ _, h, _ => absurd h id
  | .sm a b, hn, h => (inE_indec (upsPt_inE hx)).add_lt (noB_lt hx hx1 a hn.1 h.1) (noB_lt hx hx1 b hn.2 h.2)
  | .pw t, hn, h => (upsPt_inE hx).opow_lt (noB_lt hx hx1 t hn h)

end LpT

/-- The term of the top `gP n`: `gTm 0 = tp`, `gTm (n+1) = ϑ(Ω₁·gTm n + 0)`. -/
def gTm {B : LpB} : ℕ → LpT B
  | 0 => .tp
  | n + 1 => .tl (gTm n) (.cst 0)

theorem gTm_stage {B : LpB} : ∀ n : ℕ, LpT.stage (gTm n : LpT B) = n + 1
  | 0 => rfl
  | n + 1 => by
      show max (LpT.stage (gTm n : LpT B) + 1) 0 = n + 1 + 1
      rw [gTm_stage n]; simp

section Base

variable (B : LpB) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- The facts on the tops. -/
theorem gP_facts : ∀ n : ℕ, gP B n x ∈ Tset x ∧ x < gP B n x ∧ gP B n x < Om1 ∧ InE (gP B n x)
  | 0 => ⟨B.mem x hx hx1, lx_E_gt B.ek hx hx1, B.K.exp_lt x hx hx1, B.ek x hx hx1⟩
  | n + 1 => by
      obtain ⟨hT, hxg, hg1, -⟩ := gP_facts n
      obtain ⟨-, -, c, d, e, f, -, -, -⟩ :=
        Lv.gen_facts hx hx1 hT hxg.le hg1 (mem_T_of_le hx hx1 zero_le) (Ordinal.omega_pos 1)
      simp only [add_zero] at c d e f
      exact ⟨c, d, e, f⟩

theorem gP_lt_succ (n : ℕ) : gP B n x < gP B (n + 1) x := by
  obtain ⟨hT, hxg, hg1, -⟩ := gP_facts B hx hx1 n
  have := (Lv.gen_facts hx hx1 hT hxg.le hg1 (mem_T_of_le hx hx1 zero_le) (Ordinal.omega_pos 1)).2.2.2.2.2.2.2.1
  simpa using this

theorem gP_mono {m n : ℕ} (h : m ≤ n) : gP B m x ≤ gP B n x := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (gP_lt_succ B hx hx1 _).le

theorem E_le_gP (n : ℕ) : B.K.E x ≤ gP B n x := gP_mono B hx hx1 (Nat.zero_le n)

/-- Below the top of the next stage: `ϑˣ(Ω₁·β + η) < gP (m+1) x` for `β ∈ Tˣ`, `β < gP m x`, `η < gP (m+1) x`. -/
theorem lp_lt_top {m : ℕ} {β η : Ordinal.{0}} (hβT : β ∈ Tset x) (hβ : β < gP B m x) (hη : η ∈ Tset x)
    (hη1 : η < Om1) (h : η < gP B (m + 1) x) : vt x (Om1 * β + η) < gP B (m + 1) x := by
  obtain ⟨hgT, hxg, hg1, -⟩ := gP_facts B hx hx1 m
  have hgt : gP B m x < gP B (m + 1) x := gP_lt_succ B hx hx1 m
  have e : gP B (m + 1) x = vt x (Om1 * gP B m x + 0) := by rw [add_zero]; rfl
  rw [e] at h hgt ⊢
  refine lvVt_lt_gen hx hx1 hβT (hβ.trans hg1) hgT hxg.le hg1 hη hη1
    (mem_T_of_le hx hx1 zero_le) (Ordinal.omega_pos 1) ?_ (hβ.trans hgt) h
  rw [add_zero]
  calc Om1 * β + η < Om1 * β + Om1 := (add_lt_add_iff_left _).2 hη1
    _ = Om1 * (β + 1) := by rw [mul_add_one]
    _ ≤ Om1 * gP B m x := mul_le_mul_right (add_one_le_of_lt hβ) Om1

end Base

namespace LpT

variable {B : LpB}

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **A term denotes a member of `Tˣ` below the top of its stage**, and a term that is not base-free has value at
least the base. -/
theorem lp_TB : ∀ t : LpT B, CBt t x →
    (val t x ∈ Tset x ∧ val t x < gP B (stage t) x) ∧ (¬ noB t → x ≤ val t x)
  | .cst a, h => by
      obtain ⟨hT, hxg, hg1, -⟩ := gP_facts B hx hx1 0
      exact ⟨⟨vz_T_down hx hx1 hT hg1 (h.trans hxg).le, h.trans hxg⟩, fun hn => absurd trivial hn⟩
  | .bs, _ => ⟨⟨mem_T_of_le hx hx1 le_rfl, (gP_facts B hx hx1 0).2.1⟩, fun _ => le_rfl⟩
  | .ak k, h => by
      obtain ⟨hT, -, hg1, -⟩ := gP_facts B hx hx1 0
      have hlt : B.K.sys.val k x < B.K.E x := by
        have := B.K.lt_top_E x hx hx1 k h
        rwa [lx_top B.ek hx hx1] at this
      refine ⟨⟨vz_T_down hx hx1 hT hg1 hlt.le, hlt⟩, fun hn => ?_⟩
      rcases B.K.sys.small k with hc | hc
      · exact absurd hc hn
      · exact hc x hx hx1 h
  | .tp, _ => by
      obtain ⟨hT, hxg, hg1, -⟩ := gP_facts B hx hx1 0
      exact ⟨⟨hT, gP_lt_succ B hx hx1 0⟩, fun _ => hxg.le⟩
  | .th0 b t, h => by
      obtain ⟨⟨htT, htLt⟩, -⟩ := lp_TB t h.2.2
      have hst : stage t ≤ max 1 (stage t) := le_max_right _ _
      obtain ⟨m, hm⟩ : ∃ m, max 1 (stage t) = m + 1 := ⟨max 1 (stage t) - 1, by omega⟩
      have ht' : val t x < gP B (m + 1) x := htLt.trans_le (gP_mono B hx hx1 (hm ▸ hst))
      have ht1 : val t x < Om1 := ht'.trans (gP_facts B hx hx1 _).2.2.1
      have hargT := Lu.luOm1_mul_add_T hx hx1 h.2.1.le htT
      have harg2 := Lu.luOm1_mul_lt (h.2.1.trans hx1) ht1
      have hb : b < gP B m x := h.2.1.trans (gP_facts B hx hx1 m).2.1
      obtain ⟨hvT, hxv, -⟩ := vt_memTwo hx hx1 hargT harg2
      refine ⟨⟨hvT, ?_⟩, fun _ => hxv⟩
      show vt x (Om1 * b + val t x) < gP B (max 1 (stage t)) x
      rw [hm]
      exact lp_lt_top B hx hx1 (mem_T_of_le hx hx1 h.2.1.le) hb htT ht1 ht'
  | .tl l t, h => by
      obtain ⟨⟨hlT, hlLt⟩, hlx⟩ := lp_TB l h.2.1
      obtain ⟨⟨htT, htLt⟩, -⟩ := lp_TB t h.2.2
      obtain ⟨m, hm'⟩ : ∃ m, max (stage l + 1) (stage t) = m + 1 :=
        ⟨max (stage l + 1) (stage t) - 1, by omega⟩
      have hlm : stage l ≤ m := by omega
      have htm : stage t ≤ m + 1 := by omega
      have hl' : val l x < gP B m x := hlLt.trans_le (gP_mono B hx hx1 hlm)
      have ht' : val t x < gP B (m + 1) x := htLt.trans_le (gP_mono B hx hx1 htm)
      have hl1 : val l x < Om1 := hl'.trans (gP_facts B hx hx1 m).2.2.1
      have ht1 : val t x < Om1 := ht'.trans (gP_facts B hx hx1 _).2.2.1
      have hxl : x ≤ val l x := hlx h.1
      obtain ⟨hvT, hxv, -⟩ := vt_memTwo hx hx1 (lvArg_mem hx hx1 hlT hxl hl1 htT ht1) (Lu.luOm1_mul_lt hl1 ht1)
      refine ⟨⟨hvT, ?_⟩, fun _ => hxv⟩
      show vt x (Om1 * val l x + val t x) < gP B (max (stage l + 1) (stage t)) x
      rw [hm']
      exact lp_lt_top B hx hx1 hlT hl' htT ht1 ht'
  | .sm a b, h => by
      obtain ⟨⟨haT, haLt⟩, hax⟩ := lp_TB a h.1
      obtain ⟨⟨hbT, hbLt⟩, hbx⟩ := lp_TB b h.2
      have hE := (gP_facts B hx hx1 (max (stage a) (stage b))).2.2.2
      refine ⟨⟨vzT_add hx hx1 haT hbT, (inE_indec hE).add_lt
        (haLt.trans_le (gP_mono B hx hx1 (le_max_left _ _)))
        (hbLt.trans_le (gP_mono B hx hx1 (le_max_right _ _)))⟩, fun hn => ?_⟩
      simp only [noB, not_and_or] at hn
      rcases hn with hn | hn
      · exact (hax hn).trans le_self_add
      · exact (hbx hn).trans le_add_self
  | .pw t, h => by
      obtain ⟨⟨htT, htLt⟩, htx⟩ := lp_TB t h
      obtain ⟨hgT, -, hg1, hgE⟩ := gP_facts B hx hx1 (stage t)
      have hw : ω ^ val t x < gP B (stage t) x := hgE.opow_lt htLt
      exact ⟨⟨vz_T_down hx hx1 hgT hg1 hw.le, hw⟩, fun hn => (htx hn).trans (right_le_opow _ one_lt_omega0)⟩

theorem lp_T (t : LpT B) (h : CBt t x) : val t x ∈ Tset x ∧ val t x < gP B (stage t) x :=
  (lp_TB hx hx1 t h).1

theorem le_of_not_noB (t : LpT B) (h : CBt t x) (hn : ¬ noB t) : x ≤ val t x :=
  (lp_TB hx hx1 t h).2 hn

theorem lp_lt_Om1 (t : LpT B) (h : CBt t x) : val t x < Om1 :=
  (lp_T hx hx1 t h).2.trans (gP_facts B hx hx1 _).2.2.1

end Base

end LpT

section Base2

variable {B : LpB} {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

omit hx1 in
theorem gTm_val : ∀ n : ℕ, LpT.CBt (gTm n : LpT B) x ∧ LpT.val (gTm n : LpT B) x = gP B n x
  | 0 => ⟨trivial, rfl⟩
  | n + 1 => by
      obtain ⟨hc, hv⟩ := gTm_val n
      refine ⟨⟨?_, hc, hx.pos⟩, ?_⟩
      · cases n <;> exact id
      · show vt x (Om1 * LpT.val (gTm n : LpT B) x + 0) = gP B (n + 1) x
        rw [hv, add_zero]; rfl

/-- **An `ε`-number above `E_K(x)` and below `gP (m+1) x` has an argument quotient below `gP m x`.** -/
theorem lp_quot : ∀ m : ℕ, ∀ ξ, ξ ∈ Tset x → ξ < OmTwo → x < vt x ξ → InE (vt x ξ) →
    B.K.E x < vt x ξ → vt x ξ < gP B (m + 1) x → ξ / Om1 < gP B m x := by
  have h0T := mem_T_of_le hx hx1 (zero_le : (0 : Ordinal.{0}) ≤ x)
  have h1x : (1 : Ordinal.{0}) < x := Lu.lu_one_lt_E hx
  have h1T : (1 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 h1x.le
  have h11 : (1 : Ordinal.{0}) < Om1 := h1x.trans hx1
  intro m
  induction m with
  | zero =>
    intro ξ hξT hξ2 hxξ hE hEξ h
    obtain ⟨hgT, hxg, hg1, -⟩ := gP_facts B hx hx1 0
    have hlt : gP B 0 x < vt x ξ := hEξ
    have := lvLt_of_vt_lt hx hx1 hξT hξ2 hgT hxg.le hg1 h0T (Ordinal.omega_pos 1)
      (hx.pos.trans hxξ) hlt (by rw [add_zero]; exact h)
    have h1 : Om1 * (ξ / Om1) < Om1 * gP B 0 x :=
      lt_of_le_of_lt (mul_div_le ξ Om1) (by simpa using this)
    exact (mul_lt_mul_iff_right₀ (Ordinal.omega_pos 1)).1 h1
  | succ k ih =>
    intro ξ hξT hξ2 hxξ hE hEξ h
    obtain ⟨hgT, hxg, hg1, hgE⟩ := gP_facts B hx hx1 (k + 1)
    rcases lt_trichotomy (gP B (k + 1) x) (vt x ξ) with hlt | heq | hgt
    · have := lvLt_of_vt_lt hx hx1 hξT hξ2 hgT hxg.le hg1 h0T (Ordinal.omega_pos 1)
        (hx.pos.trans hxξ) hlt (by rw [add_zero]; exact h)
      have h1 : Om1 * (ξ / Om1) < Om1 * gP B (k + 1) x :=
        lt_of_le_of_lt (mul_div_le ξ Om1) (by simpa using this)
      exact (mul_lt_mul_iff_right₀ (Ordinal.omega_pos 1)).1 h1
    · -- `ϑˣ(ξ) = gP (k+1) x = ϑˣ(Ω₁·gP k x)`: compare with `ϑˣ(Ω₁·gP k x + 1)`
      obtain ⟨hkT, hxk, hk1, -⟩ := gP_facts B hx hx1 k
      have hk : gP B k x < gP B (k + 1) x := gP_lt_succ B hx hx1 k
      have h2 : vt x (Om1 * gP B k x + 0) < vt x (Om1 * gP B k x + 1) :=
        lvVt_eta_lt hx hx1 hkT hxk.le hk1 h0T (Ordinal.omega_pos 1) h1T h11 zero_lt_one
          (hx.pos.trans (Lv.gen_facts hx hx1 hkT hxk.le hk1 h1T h11).2.2.2.1)
      have h3 : ξ < Om1 * gP B k x + 1 :=
        lvLt_of_vt_lt hx hx1 hξT hξ2 hkT hxk.le hk1 h1T h11 (by rw [← heq]; exact Lu.lu_one_lt_E hgE)
          (by rw [← heq]; exact hk) (by rw [← heq]; simpa using h2)
      have h4 : Om1 * (ξ / Om1) < Om1 * (gP B k x + 1) := by
        calc Om1 * (ξ / Om1) ≤ ξ := mul_div_le ξ Om1
          _ < Om1 * gP B k x + 1 := h3
          _ ≤ Om1 * gP B k x + Om1 := add_le_add_right h11.le _
          _ = Om1 * (gP B k x + 1) := by rw [mul_add_one]
      have h5 : ξ / Om1 < gP B k x + 1 := (mul_lt_mul_iff_right₀ (Ordinal.omega_pos 1)).1 h4
      exact (Order.lt_add_one_iff.1 h5).trans_lt hk
    · exact (ih ξ hξT hξ2 hxξ hE hEξ hgt).trans (gP_lt_succ B hx hx1 k)

end Base2

/-- Every value below `E_K(x)` is a value of `K` (at `x`). -/
theorem lp_rep0 {B : LpB} {x : Ordinal.{0}} (hr : LxRep B.K x) :
    ∀ v, v < B.K.E x → ∃ t : LpT B, LpT.CBt t x ∧ LpT.stage t ≤ 0 ∧ LpT.val t x = v := fun v hv => by
  obtain ⟨k, hk, hkv⟩ := hr v hv
  exact ⟨.ak k, hk, le_rfl, hkv⟩

/-- **Every ordinal below `gP n x` is the value of a term of stage `≤ n`**, at a `υ`-point `x` where every value
below `E_K(x)` is a value of `K`. -/
theorem lp_rep {B : LpB} {x : Ordinal.{0}} (hxU : UpsPt x) (hx1 : x < Om1) (hr : LxRep B.K x) :
    ∀ n : ℕ, ∀ v, v < gP B n x → ∃ t : LpT B, LpT.CBt t x ∧ LpT.stage t ≤ n ∧ LpT.val t x = v := by
  have hx := upsPt_inE hxU
  intro n
  induction n with
  | zero => exact lp_rep0 hr
  | succ m ihm =>
    obtain ⟨hgT, -, hg1, -⟩ := gP_facts B hx hx1 (m + 1)
    obtain ⟨hmT, -, hm1, -⟩ := gP_facts B hx hx1 m
    have hxE := lx_E_gt B.ek hx hx1
    intro v
    induction v using WellFoundedLT.induction with
    | ind v IH =>
    intro hv
    have hv1 : v < Om1 := hv.trans hg1
    have hvT : v ∈ Tset x := vz_T_down hx hx1 hgT hg1 hv.le
    rcases lt_trichotomy v (B.K.E x) with hvE | rfl | hEv
    · obtain ⟨t, ht, hs, he⟩ := lp_rep0 hr v hvE
      exact ⟨t, ht, hs.trans (Nat.zero_le _), he⟩
    · exact ⟨.tp, trivial, by simp [LpT.stage], rfl⟩
    have hxv : x ≤ v := (hxE.trans hEv).le
    by_cases hI : Indec v
    · by_cases hE : InE v
      · have hxv' : x < v := hxE.trans hEv
        obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hx hx1 hvT hxv hv1 (inE_indec hE)
        have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξv]; exact hxv', by rw [hξv]; exact hE⟩
        obtain ⟨hq1, hrT, hr1, hdec⟩ := Lu.lu_split hx hx1 hξT hξ2 hΩξ
        have hqm : ξ / Om1 < gP B m x :=
          lp_quot hx hx1 m ξ hξT hξ2 (by rw [hξv]; exact hxv') (by rw [hξv]; exact hE) (by rw [hξv]; exact hEv)
            (by rw [hξv]; exact hv)
        rcases lt_or_ge (ξ / Om1) x with hqx | hqx
        · have hrv : ξ % Om1 < v := by
            have h := luLt_vt_self hx hx1 hq1 hqx hrT hr1
            rwa [hdec, hξv] at h
          obtain ⟨t, ht, hst, he⟩ := IH _ hrv (hrv.trans hv)
          exact ⟨.th0 (ξ / Om1) t, ⟨hq1, hqx, ht⟩, by simp only [LpT.stage]; omega,
            by rw [LpT.val_th0, he, hdec, hξv]⟩
        · obtain ⟨l, hlc, hls, hle⟩ := ihm (ξ / Om1) hqm
          have hqT : ξ / Om1 ∈ Tset x := vz_T_down hx hx1 hmT hm1 hqm.le
          have hrv : ξ % Om1 < v := by
            have h := (lvLevel_lt_vt hx hx1 hqT hqx (hqm.trans hm1) hrT hr1).2
            rwa [hdec, hξv] at h
          obtain ⟨t, ht, hst, he⟩ := IH _ hrv (hrv.trans hv)
          have hlB : ¬ LpT.noB l := fun hn =>
            absurd (LpT.noB_lt hxU hx1 l hn hlc) (not_lt.2 (hle ▸ hqx))
          exact ⟨.tl l t, ⟨hlB, hlc, ht⟩, by simp only [LpT.stage]; omega,
            by rw [LpT.val_tl, he, hle, hdec, hξv]⟩
      · obtain ⟨L, rfl⟩ := indec_eq_opow hI
        have hL : L < ω ^ L := lt_of_le_of_ne (right_le_opow _ one_lt_omega0)
          (fun h => hE (by unfold InE; rw [← h]; exact h.symm))
        obtain ⟨t, ht, hst, e⟩ := IH L hL (hL.trans hv)
        exact ⟨.pw t, ht, hst, by rw [LpT.val_pw, e]⟩
    · have hD : DecompR0 v := not_not.1 hI
      rcases hD with h0 | ⟨u1, u2, hu1, hu2, hsum⟩
      · exact absurd h0 (lt_of_lt_of_le hx.pos hxv).ne'
      obtain ⟨s1, h1, st1, e1⟩ := IH u1 hu1 (hu1.trans hv)
      obtain ⟨s2, h2, st2, e2⟩ := IH u2 hu2 (hu2.trans hv)
      exact ⟨.sm s1 s2, ⟨h1, h2⟩, by simp only [LpT.stage]; omega, by rw [LpT.val_sm, e1, e2, hsum]⟩

namespace LpT

variable {B : LpB}

/-- The tops lie below every next point above the base. -/
theorem lp_top_lt_next {x u : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (n : ℕ) (hxu : x < u)
    (hu : LtInf1 u) : gP B n x < u := by
  obtain ⟨m, -, -, hmin, hTm, -⟩ := T_next (Or.inr hx) hx1
  obtain ⟨hT, -, htop1, -⟩ := gP_facts B hx hx1 n
  exact lt_of_lt_of_le ((hTm _ htop1).1 hT) (hmin u hxu hu)

theorem lp_lt_next {x u : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {t : LpT B}
    (ht : CBt t x) (hxu : x < u) (hu : LtInf1 u) : val t x < u :=
  (lp_T hx hx1 t ht).2.trans (lp_top_lt_next hx hx1 _ hxu hu)

theorem lp_lt_ups {x u : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {t : LpT B}
    (ht : CBt t x) (hxu : x < u) (hu : UpsPt u) : val t x < u :=
  lp_lt_next hx hx1 ht hxu hu.2

/-- **Lemma EXACT** for `LpT`: the value maps to the same term at the smaller base. -/
theorem pi {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) :
    ∀ t : LpT B, CBt t σ → val t ρ ∈ TB ρ σ ∧ pi σ ρ (val t ρ) = val t σ
  | .cst a, h => ⟨mem_TB_of_lt hB h, pi_lt hB h⟩
  | .bs, _ => pi_base hB
  | .ak k, h => B.K.exact σ ρ hσ hρ hB k h
  | .tp, _ => B.K.exp_pi σ ρ hσ hρ hB
  | .th0 b t, h => by
      obtain ⟨h1, h2⟩ := pi hσ hρ hB t h.2.2
      have ht1 : val t ρ < Om1 := lp_lt_Om1 hB.2.1 hB.2.2.2 t (CBt.mono hB.2.2.1.le h.2.2)
      obtain ⟨h3, h4⟩ := LvT.pi_vt_low hB h.2.1 h1 ht1
      simp only [val_th0]
      exact ⟨h3, by rw [h4, h2]⟩
  | .tl l t, h => by
      obtain ⟨hl1, hl2⟩ := pi hσ hρ hB l h.2.1
      obtain ⟨h1, h2⟩ := pi hσ hρ hB t h.2.2
      have hcρ : CBt l ρ := CBt.mono hB.2.2.1.le h.2.1
      have hρL : ρ ≤ val l ρ := le_of_not_noB hB.2.1 hB.2.2.2 l hcρ h.1
      have hL1 : val l ρ < Om1 := lp_lt_Om1 hB.2.1 hB.2.2.2 l hcρ
      have ht1 : val t ρ < Om1 := lp_lt_Om1 hB.2.1 hB.2.2.2 t (CBt.mono hB.2.2.1.le h.2.2)
      obtain ⟨h3, h4⟩ := LvET.pi_vt_tl hB hl1 hρL hL1 h1 ht1
      simp only [val_tl]
      exact ⟨h3, by rw [h4, h2, hl2]⟩
  | .sm a b, h => by
      obtain ⟨h1, h2⟩ := pi hσ hρ hB a h.1
      obtain ⟨h3, h4⟩ := pi hσ hρ hB b h.2
      obtain ⟨h5, h6⟩ := pi_add hB h1 h3
      simp only [val_sm]
      exact ⟨h5, by rw [h6, h2, h4]⟩
  | .pw t, h => by
      obtain ⟨h1, h2⟩ := pi hσ hρ hB t h
      have ht1 : val t ρ < Om1 := lp_lt_Om1 hB.2.1 hB.2.2.2 t (CBt.mono hB.2.2.1.le h)
      obtain ⟨h3, h4⟩ := pi_opowZ hσ hρ hB h1 ht1
      simp only [val_pw]
      exact ⟨h3, by rw [h4, h2]⟩

/-- **Lemma EXACT** in order form. -/
theorem uni_le {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ)
    {t u : LpT B} (ht : CBt t σ) (hu : CBt u σ) :
    val t ρ ≤ val u ρ ↔ val t σ ≤ val u σ := by
  obtain ⟨h1, h2⟩ := pi hσ hρ hB t ht
  obtain ⟨h3, h4⟩ := pi hσ hρ hB u hu
  rw [← h2, ← h4]
  exact ((pi_bijOn hB).2.le_iff_le h1 h3).symm

theorem uni_lt {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ)
    {t u : LpT B} (ht : CBt t σ) (hu : CBt u σ) :
    val t ρ < val u ρ ↔ val t σ < val u σ := by
  rw [← not_le, ← not_le, uni_le hσ hρ hB hu ht]

theorem uni_eq {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ)
    {t u : LpT B} (ht : CBt t σ) (hu : CBt u σ) :
    val t ρ = val u ρ ↔ val t σ = val u σ := by
  rw [le_antisymm_iff, le_antisymm_iff, uni_le hσ hρ hB ht hu, uni_le hσ hρ hB hu ht]

/-- The terms of `R2.LxTm` over `K` read as terms here. -/
def ofLx : LxTm B.K → LpT B
  | .bs t => ak t
  | .tp => tp
  | .sm a b => sm (ofLx a) (ofLx b)
  | .pw a => pw (ofLx a)

theorem ofLx_val : ∀ (t : LxTm B.K) (x : Ordinal.{0}), val (ofLx t) x = LxTm.val t x
  | .bs _, _ => rfl
  | .tp, _ => rfl
  | .sm a b, x => by simp only [ofLx, val_sm, LxTm.val_sm, ofLx_val a x, ofLx_val b x]
  | .pw a, x => by simp only [ofLx, val_pw, LxTm.val_pw, ofLx_val a x]

theorem ofLx_cs : ∀ t : LxTm B.K, cs (ofLx t) = LxTm.cs t
  | .bs _ => rfl
  | .tp => rfl
  | .sm a b => by simp only [ofLx, cs, LxTm.cs, ofLx_cs a, ofLx_cs b]
  | .pw a => by simp only [ofLx, cs, LxTm.cs, ofLx_cs a]

theorem ofLx_cbt : ∀ (t : LxTm B.K) (s : Ordinal.{0}), LxTm.CBt t s → CBt (ofLx t) s
  | .bs _, _, h => h
  | .tp, _, _ => trivial
  | .sm a b, s, h => ⟨ofLx_cbt a s h.1, ofLx_cbt b s h.2⟩
  | .pw a, s, h => ofLx_cbt a s h

end LpT

/-- The `small` field: a term is base-independent or at least the base. -/
theorem lp_small {B : LpB} : ∀ t : LpT B,
    (∀ x y, LpT.val t x = LpT.val t y) ∨
      (∀ x, InE x → x < Om1 → LpT.CBt t x → x ≤ LpT.val t x) := by
  intro t
  by_cases h : LpT.noB t
  · exact Or.inl (LpT.noB_val t h)
  · exact Or.inr (fun x hx hx1 hc => LpT.le_of_not_noB hx hx1 t hc h)

end Googology.Trans.PoR.InaccPsi.R2.Lp

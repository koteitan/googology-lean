import Googology.Trans.PoR.InaccPsi.R2.LvELoc

/-!
# The staged tower of levels: grammar, the tops `gT n`, EXACT

`LvGT`: constants, the base, `ϑˣ(Ω₁·b + t)` for a constant level `1 ≤ b < x` (`th0`), `ϑˣ(Ω₁·l(x) + t)` for a level
term `l` that is not base-free (`tl l t`; `l` may itself contain thetas), sums, `ω^t`.  The **stage** of a term counts
the nesting of levels (`stage (tl l t) = max (stage l + 1) (stage t)`, `stage (th0 b t) = max 1 (stage t)`); the tops
are `gT 0 x = ε_{x+1}`, `gT (n+1) x = ϑˣ(Ω₁·gT n x)`, and `gTm n` is the term of `gT n` (stage `n+1`).  From the axioms
of `R2.CitedLu` and `R2.CitedLv`:

* `gT_facts`, `gT_lt_succ`; `LvGT.lvg_T` (**a term denotes a member of `Tˣ` below `gT (stage t) x`**),
  `LvGT.le_of_not_noB`;
* `lvg_quot` (an `ε`-number below `gT (m+1) x` has an argument quotient below `gT m x`), `LvGT.lvg_rep` (**every
  ordinal below `gT n x` is the value of a term of stage `≤ n`**);
* `LvGT.pi` (**Lemma EXACT**), `LvGT.uni_le`, `lvg_small`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-- The tops of the tower: `gT 0 x = ε_{x+1}`, `gT (n+1) x = ϑˣ(Ω₁·gT n x)`. -/
noncomputable def gT : ℕ → Ordinal.{0} → Ordinal.{0}
  | 0, x => eN x
  | n + 1, x => vt x (Om1 * gT n x)

/-- Terms with levels given by terms of lower stage. -/
inductive LvGT : Type 1
  | cst : Ordinal.{0} → LvGT
  | bs : LvGT
  | th0 : Ordinal.{0} → LvGT → LvGT
  | tl : LvGT → LvGT → LvGT
  | sm : LvGT → LvGT → LvGT
  | pw : LvGT → LvGT

namespace LvGT

/-- Value of a term at base `x`. -/
noncomputable def val : LvGT → Ordinal.{0} → Ordinal.{0}
  | cst a, _ => a
  | bs, x => x
  | th0 b t, x => vt x (Om1 * b + val t x)
  | tl l t, x => vt x (Om1 * val l x + val t x)
  | sm a b, x => val a x + val b x
  | pw t, x => ω ^ val t x

/-- Constants in the term. -/
def cs : LvGT → List Ordinal.{0}
  | cst a => [a]
  | bs => []
  | th0 b t => b :: cs t
  | tl l t => cs l ++ cs t
  | sm a b => cs a ++ cs b
  | pw t => cs t

/-- A term is base-independent only when it contains no theta or base constructor. -/
def noB : LvGT → Prop
  | cst _ => True
  | bs => False
  | th0 _ _ => False
  | tl _ _ => False
  | sm a b => noB a ∧ noB b
  | pw t => noB t

/-- The side condition: constants below the base, constant levels at least `1`, level terms not base-free. -/
def CBt : LvGT → Ordinal.{0} → Prop
  | cst a, x => a < x
  | bs, _ => True
  | th0 b t, x => 1 ≤ b ∧ b < x ∧ CBt t x
  | tl l t, x => ¬ noB l ∧ CBt l x ∧ CBt t x
  | sm a b, x => CBt a x ∧ CBt b x
  | pw t, x => CBt t x

/-- The stage: the nesting depth of the levels. -/
def stage : LvGT → ℕ
  | cst _ => 0
  | bs => 0
  | th0 _ t => max 1 (stage t)
  | tl l t => max (stage l + 1) (stage t)
  | sm a b => max (stage a) (stage b)
  | pw t => stage t

@[simp] theorem val_cst (a x : Ordinal.{0}) : val (cst a) x = a := rfl
@[simp] theorem val_bs (x : Ordinal.{0}) : val bs x = x := rfl
@[simp] theorem val_th0 (b : Ordinal.{0}) (t : LvGT) (x : Ordinal.{0}) :
    val (th0 b t) x = vt x (Om1 * b + val t x) := rfl
@[simp] theorem val_tl (l t : LvGT) (x : Ordinal.{0}) :
    val (tl l t) x = vt x (Om1 * val l x + val t x) := rfl
@[simp] theorem val_sm (a b : LvGT) (x : Ordinal.{0}) : val (sm a b) x = val a x + val b x := rfl
@[simp] theorem val_pw (t : LvGT) (x : Ordinal.{0}) : val (pw t) x = ω ^ val t x := rfl

/-- A base-free term with constants below an `ε`-number `x` has value below `x`. -/
theorem noB_lt {x : Ordinal.{0}} (hx : InE x) : ∀ t : LvGT, noB t → CBt t x → val t x < x
  | .cst _, _, h => h
  | .bs, h, _ => absurd h id
  | .th0 _ _, h, _ => absurd h id
  | .tl _ _, h, _ => absurd h id
  | .sm a b, hn, h => (inE_indec hx).add_lt (noB_lt hx a hn.1 h.1) (noB_lt hx b hn.2 h.2)
  | .pw t, hn, h => hx.opow_lt (noB_lt hx t hn h)

/-- A term without a base or theta constructor has constant value. -/
theorem noB_val : ∀ t : LvGT, noB t → ∀ x y, val t x = val t y
  | .cst _, _, _, _ => rfl
  | .bs, h, _, _ => absurd h id
  | .th0 _ _, h, _, _ => absurd h id
  | .tl _ _, h, _, _ => absurd h id
  | .sm a b, h, x, y => by simp only [val_sm, noB_val a h.1 x y, noB_val b h.2 x y]
  | .pw t, h, x, y => by simp only [val_pw, noB_val t h x y]

/-- The side condition depends only on the listed constants. -/
theorem cbt_iff {t : LvGT} {x y : Ordinal.{0}} (h : CBt t x)
    (hy : ∀ c ∈ cs t, c < y) : CBt t y := by
  induction t with
  | cst a => exact hy a (by simp [cs])
  | bs => trivial
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
theorem cbt_cst {ρ : Ordinal.{0}} {s : LvGT} (hs : CBt s ρ) : ∀ c ∈ cs s, c < ρ := by
  induction s with
  | cst a => intro c hc; simp [cs] at hc; subst c; exact hs
  | bs => intro c hc; simp [cs] at hc
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
theorem CBt.mono {s : LvGT} {x y : Ordinal.{0}} (hxy : x ≤ y) (hs : CBt s x) : CBt s y :=
  cbt_iff hs (fun c hc => (cbt_cst hs c hc).trans_le hxy)

end LvGT

/-- The term of the top `gT n`: `gTm 0 = ϑ(Ω₁·1 + 0)`, `gTm (n+1) = ϑ(Ω₁·gTm n + 0)`. -/
def gTm : ℕ → LvGT
  | 0 => .th0 1 (.cst 0)
  | n + 1 => .tl (gTm n) (.cst 0)

theorem gTm_stage : ∀ n : ℕ, LvGT.stage (gTm n) = n + 1
  | 0 => rfl
  | n + 1 => by
      show max (LvGT.stage (gTm n) + 1) 0 = n + 1 + 1
      rw [gTm_stage n]; simp

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- The facts on the tops. -/
theorem gT_facts : ∀ n : ℕ, gT n x ∈ Tset x ∧ x < gT n x ∧ gT n x < Om1 ∧ InE (gT n x)
  | 0 => by
      obtain ⟨heT, he1⟩ := lve_eN_T hx hx1
      exact ⟨heT, lt_eN x, he1, eN_E x⟩
  | n + 1 => by
      obtain ⟨hT, hxg, hg1, -⟩ := gT_facts n
      obtain ⟨-, -, c, d, e, f, -, -, -⟩ :=
        Lv.gen_facts hx hx1 hT hxg.le hg1 (mem_T_of_le hx hx1 zero_le) (Ordinal.omega_pos 1)
      simp only [add_zero] at c d e f
      exact ⟨c, d, e, f⟩

theorem gT_lt_succ (n : ℕ) : gT n x < gT (n + 1) x := by
  obtain ⟨hT, hxg, hg1, -⟩ := gT_facts hx hx1 n
  have := (Lv.gen_facts hx hx1 hT hxg.le hg1 (mem_T_of_le hx hx1 zero_le) (Ordinal.omega_pos 1)).2.2.2.2.2.2.2.1
  simpa using this

theorem gT_mono {m n : ℕ} (h : m ≤ n) : gT m x ≤ gT n x := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (gT_lt_succ hx hx1 _).le

theorem eN_le_gT (n : ℕ) : eN x ≤ gT n x := gT_mono hx hx1 (Nat.zero_le n)

/-- Below the top of the next stage: `ϑˣ(Ω₁·β + η) < gT (m+1) x` for `β ∈ Tˣ`, `β < gT m x`, `η < gT (m+1) x`. -/
theorem lvg_lt_top {m : ℕ} {β η : Ordinal.{0}} (hβT : β ∈ Tset x) (hβ : β < gT m x) (hη : η ∈ Tset x)
    (hη1 : η < Om1) (h : η < gT (m + 1) x) : vt x (Om1 * β + η) < gT (m + 1) x := by
  obtain ⟨hgT, hxg, hg1, -⟩ := gT_facts hx hx1 m
  have hgt : gT m x < gT (m + 1) x := gT_lt_succ hx hx1 m
  have e : gT (m + 1) x = vt x (Om1 * gT m x + 0) := by rw [add_zero]; rfl
  rw [e] at h hgt ⊢
  refine lvVt_lt_gen hx hx1 hβT (hβ.trans hg1) hgT hxg.le hg1 hη hη1
    (mem_T_of_le hx hx1 zero_le) (Ordinal.omega_pos 1) ?_ (hβ.trans hgt) h
  rw [add_zero]
  calc Om1 * β + η < Om1 * β + Om1 := (add_lt_add_iff_left _).2 hη1
    _ = Om1 * (β + 1) := by rw [mul_add_one]
    _ ≤ Om1 * gT m x := mul_le_mul_right (add_one_le_of_lt hβ) Om1

end Base

namespace LvGT

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **A term denotes a member of `Tˣ` below the top of its stage**, and a term that is not base-free has value at
least the base. -/
theorem lvg_TB : ∀ t : LvGT, CBt t x →
    (val t x ∈ Tset x ∧ val t x < gT (stage t) x) ∧ (¬ noB t → x ≤ val t x)
  | .cst a, h => by
      obtain ⟨hT, hxg, hg1, -⟩ := gT_facts hx hx1 0
      exact ⟨⟨vz_T_down hx hx1 hT hg1 (h.trans hxg).le, h.trans hxg⟩, fun hn => absurd trivial hn⟩
  | .bs, _ => ⟨⟨mem_T_of_le hx hx1 le_rfl, (gT_facts hx hx1 0).2.1⟩, fun _ => le_rfl⟩
  | .th0 b t, h => by
      obtain ⟨⟨htT, htLt⟩, -⟩ := lvg_TB t h.2.2
      have hst : stage t ≤ max 1 (stage t) := le_max_right _ _
      obtain ⟨m, hm⟩ : ∃ m, max 1 (stage t) = m + 1 := ⟨max 1 (stage t) - 1, by omega⟩
      have ht' : val t x < gT (m + 1) x := htLt.trans_le (gT_mono hx hx1 (hm ▸ hst))
      have ht1 : val t x < Om1 := ht'.trans (gT_facts hx hx1 _).2.2.1
      have hargT := Lu.luOm1_mul_add_T hx hx1 h.2.1.le htT
      have harg2 := Lu.luOm1_mul_lt (h.2.1.trans hx1) ht1
      have hb : b < gT m x := h.2.1.trans (gT_facts hx hx1 m).2.1
      obtain ⟨hvT, hxv, -⟩ := vt_memTwo hx hx1 hargT harg2
      refine ⟨⟨hvT, ?_⟩, fun _ => hxv⟩
      show vt x (Om1 * b + val t x) < gT (max 1 (stage t)) x
      rw [hm]
      exact lvg_lt_top hx hx1 (mem_T_of_le hx hx1 h.2.1.le) hb htT ht1 ht'
  | .tl l t, h => by
      obtain ⟨⟨hlT, hlLt⟩, hlx⟩ := lvg_TB l h.2.1
      obtain ⟨⟨htT, htLt⟩, -⟩ := lvg_TB t h.2.2
      obtain ⟨m, hm'⟩ : ∃ m, max (stage l + 1) (stage t) = m + 1 :=
        ⟨max (stage l + 1) (stage t) - 1, by omega⟩
      have hlm : stage l ≤ m := by omega
      have htm : stage t ≤ m + 1 := by omega
      have hl' : val l x < gT m x := hlLt.trans_le (gT_mono hx hx1 hlm)
      have ht' : val t x < gT (m + 1) x := htLt.trans_le (gT_mono hx hx1 htm)
      have hl1 : val l x < Om1 := hl'.trans (gT_facts hx hx1 m).2.2.1
      have ht1 : val t x < Om1 := ht'.trans (gT_facts hx hx1 _).2.2.1
      have hxl : x ≤ val l x := hlx h.1
      obtain ⟨hvT, hxv, -⟩ := vt_memTwo hx hx1 (lvArg_mem hx hx1 hlT hxl hl1 htT ht1) (Lu.luOm1_mul_lt hl1 ht1)
      refine ⟨⟨hvT, ?_⟩, fun _ => hxv⟩
      show vt x (Om1 * val l x + val t x) < gT (max (stage l + 1) (stage t)) x
      rw [hm']
      exact lvg_lt_top hx hx1 hlT hl' htT ht1 ht'
  | .sm a b, h => by
      obtain ⟨⟨haT, haLt⟩, hax⟩ := lvg_TB a h.1
      obtain ⟨⟨hbT, hbLt⟩, hbx⟩ := lvg_TB b h.2
      have hE := (gT_facts hx hx1 (max (stage a) (stage b))).2.2.2
      refine ⟨⟨vzT_add hx hx1 haT hbT, (inE_indec hE).add_lt
        (haLt.trans_le (gT_mono hx hx1 (le_max_left _ _))) (hbLt.trans_le (gT_mono hx hx1 (le_max_right _ _)))⟩,
        fun hn => ?_⟩
      simp only [noB, not_and_or] at hn
      rcases hn with hn | hn
      · exact (hax hn).trans le_self_add
      · exact (hbx hn).trans le_add_self
  | .pw t, h => by
      obtain ⟨⟨htT, htLt⟩, htx⟩ := lvg_TB t h
      obtain ⟨hgT, -, hg1, hgE⟩ := gT_facts hx hx1 (stage t)
      have hw : ω ^ val t x < gT (stage t) x := hgE.opow_lt htLt
      exact ⟨⟨vz_T_down hx hx1 hgT hg1 hw.le, hw⟩, fun hn => (htx hn).trans (right_le_opow _ one_lt_omega0)⟩

theorem lvg_T (t : LvGT) (h : CBt t x) : val t x ∈ Tset x ∧ val t x < gT (stage t) x :=
  (lvg_TB hx hx1 t h).1

theorem le_of_not_noB (t : LvGT) (h : CBt t x) (hn : ¬ noB t) : x ≤ val t x :=
  (lvg_TB hx hx1 t h).2 hn

theorem lvg_lt_Om1 (t : LvGT) (h : CBt t x) : val t x < Om1 :=
  (lvg_T hx hx1 t h).2.trans (gT_facts hx hx1 _).2.2.1

end Base

end LvGT

section Base2

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- `ε_{x+1} = ϑˣ(Ω₁·1 + 0)`. -/
theorem lvg_eN_eq : vt x (Om1 * 1 + 0) = eN x := by
  have h1x : (1 : Ordinal.{0}) < x := Lu.lu_one_lt_E hx
  have h0T := mem_T_of_le hx hx1 (zero_le : (0 : Ordinal.{0}) ≤ x)
  obtain ⟨-, -, -, hxa, -, haE, -, -⟩ := Lu.lu_th_facts hx hx1 le_rfl h1x h0T (Ordinal.omega_pos 1)
  refine le_antisymm ?_ (eN_le hxa haE)
  have hP : Lu.LuP 1 (eN x) := by
    have := (Lu.luP_succ (β := 0) (a := eN x)).2 (by rw [veblen_zero_apply]; exact eN_E x)
    simpa using this
  exact Lu.lu_th_min hx hx1 le_rfl h1x h0T (Ordinal.omega_pos 1) hP (lt_eN x) (eN_E x).pos
    (fun σ hσ => absurd hσ (not_lt.2 zero_le))

theorem gTm_val : ∀ n : ℕ, LvGT.CBt (gTm n) x ∧ LvGT.val (gTm n) x = gT n x
  | 0 => ⟨⟨le_rfl, Lu.lu_one_lt_E hx, hx.pos⟩, lvg_eN_eq hx hx1⟩
  | n + 1 => by
      obtain ⟨hc, hv⟩ := gTm_val n
      refine ⟨⟨?_, hc, hx.pos⟩, ?_⟩
      · cases n <;> exact id
      · show vt x (Om1 * LvGT.val (gTm n) x + 0) = gT (n + 1) x
        rw [hv, add_zero]; rfl

/-- An `ε`-number below `gT (m+1) x` has an argument quotient below `gT m x`. -/
theorem lvg_quot : ∀ m : ℕ, ∀ ξ, ξ ∈ Tset x → ξ < OmTwo → x < vt x ξ → InE (vt x ξ) →
    vt x ξ < gT (m + 1) x → ξ / Om1 < gT m x := by
  have h0T := mem_T_of_le hx hx1 (zero_le : (0 : Ordinal.{0}) ≤ x)
  have h1x : (1 : Ordinal.{0}) < x := Lu.lu_one_lt_E hx
  have h1T : (1 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 h1x.le
  have h11 : (1 : Ordinal.{0}) < Om1 := h1x.trans hx1
  intro m
  induction m with
  | zero =>
    intro ξ hξT hξ2 hxξ hE h
    have := lve_quot_top hx hx1 hξT hξ2 hxξ hE h
    exact this
  | succ k ih =>
    intro ξ hξT hξ2 hxξ hE h
    obtain ⟨hgT, hxg, hg1, hgE⟩ := gT_facts hx hx1 (k + 1)
    rcases lt_trichotomy (gT (k + 1) x) (vt x ξ) with hlt | heq | hgt
    · have := lvLt_of_vt_lt hx hx1 hξT hξ2 hgT hxg.le hg1 h0T (Ordinal.omega_pos 1)
        (hx.pos.trans hxξ) hlt (by rw [add_zero]; exact h)
      have h1 : Om1 * (ξ / Om1) < Om1 * gT (k + 1) x :=
        lt_of_le_of_lt (mul_div_le ξ Om1) (by simpa using this)
      exact (mul_lt_mul_iff_right₀ (Ordinal.omega_pos 1)).1 h1
    · -- `ϑˣ(ξ) = gT (k+1) x = ϑˣ(Ω₁·gT k x)`: compare with `ϑˣ(Ω₁·gT k x + 1)`
      obtain ⟨hkT, hxk, hk1, -⟩ := gT_facts hx hx1 k
      have hk : gT k x < gT (k + 1) x := gT_lt_succ hx hx1 k
      have h2 : vt x (Om1 * gT k x + 0) < vt x (Om1 * gT k x + 1) :=
        lvVt_eta_lt hx hx1 hkT hxk.le hk1 h0T (Ordinal.omega_pos 1) h1T h11 zero_lt_one
          (hx.pos.trans (Lv.gen_facts hx hx1 hkT hxk.le hk1 h1T h11).2.2.2.1)
      have h3 : ξ < Om1 * gT k x + 1 :=
        lvLt_of_vt_lt hx hx1 hξT hξ2 hkT hxk.le hk1 h1T h11 (by rw [← heq]; exact Lu.lu_one_lt_E hgE)
          (by rw [← heq]; exact hk) (by rw [← heq]; simpa using h2)
      have h4 : Om1 * (ξ / Om1) < Om1 * (gT k x + 1) := by
        calc Om1 * (ξ / Om1) ≤ ξ := mul_div_le ξ Om1
          _ < Om1 * gT k x + 1 := h3
          _ ≤ Om1 * gT k x + Om1 := add_le_add_right h11.le _
          _ = Om1 * (gT k x + 1) := by rw [mul_add_one]
      have h5 : ξ / Om1 < gT k x + 1 := (mul_lt_mul_iff_right₀ (Ordinal.omega_pos 1)).1 h4
      exact (Order.lt_add_one_iff.1 h5).trans_lt hk
    · exact (ih ξ hξT hξ2 hxξ hE hgt).trans (gT_lt_succ hx hx1 k)

/-- **Every ordinal below `gT n x` is the value of a term of stage `≤ n`.** -/
theorem lvg_rep : ∀ n : ℕ, ∀ v, v < gT n x → ∃ t : LvGT, LvGT.CBt t x ∧ LvGT.stage t ≤ n ∧ LvGT.val t x = v := by
  intro n
  induction n with
  | zero =>
    intro v hv
    obtain ⟨l, hl, hc, he, -⟩ := LvET.lev_rep hx v hv
    -- translate the theta-free term
    have : ∀ l : LvET, LvET.isLev l → LvET.CBt l x →
        ∃ t : LvGT, LvGT.CBt t x ∧ LvGT.stage t ≤ 0 ∧ LvGT.val t x = LvET.val l x := by
      intro l
      induction l with
      | cst a => intro _ h; exact ⟨.cst a, h, le_rfl, rfl⟩
      | bs => intro _ _; exact ⟨.bs, trivial, le_rfl, rfl⟩
      | th0 _ _ _ => intro hl; exact absurd hl id
      | tl _ _ _ _ => intro hl; exact absurd hl id
      | sm a b iha ihb =>
          intro hl h
          obtain ⟨t1, c1, s1, e1⟩ := iha hl.1 h.1
          obtain ⟨t2, c2, s2, e2⟩ := ihb hl.2 h.2
          exact ⟨.sm t1 t2, ⟨c1, c2⟩, max_le s1 s2, by simp [e1, e2]⟩
      | pw a ih =>
          intro hl h
          obtain ⟨t1, c1, s1, e1⟩ := ih hl h
          exact ⟨.pw t1, c1, s1, by simp [e1]⟩
    obtain ⟨t, ht, hs, hv'⟩ := this l hl hc
    exact ⟨t, ht, hs, hv'.trans he⟩
  | succ m ihm =>
    obtain ⟨hgT, -, hg1, -⟩ := gT_facts hx hx1 (m + 1)
    obtain ⟨hmT, -, hm1, -⟩ := gT_facts hx hx1 m
    intro v
    induction v using WellFoundedLT.induction with
    | ind v IH =>
    intro hv
    have hv1 : v < Om1 := hv.trans hg1
    have hvT : v ∈ Tset x := vz_T_down hx hx1 hgT hg1 hv.le
    rcases lt_or_ge v x with hvx | hxv
    · exact ⟨.cst v, hvx, Nat.zero_le _, rfl⟩
    by_cases hI : Indec v
    · by_cases hE : InE v
      · rcases eq_or_lt_of_le hxv with rfl | hxv'
        · exact ⟨.bs, trivial, Nat.zero_le _, rfl⟩
        obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hx hx1 hvT hxv hv1 (inE_indec hE)
        have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξv]; exact hxv', by rw [hξv]; exact hE⟩
        obtain ⟨hq1, hrT, hr1, hdec⟩ := Lu.lu_split hx hx1 hξT hξ2 hΩξ
        have hqm : ξ / Om1 < gT m x :=
          lvg_quot hx hx1 m ξ hξT hξ2 (by rw [hξv]; exact hxv') (by rw [hξv]; exact hE) (by rw [hξv]; exact hv)
        rcases lt_or_ge (ξ / Om1) x with hqx | hqx
        · have hrv : ξ % Om1 < v := by
            have h := luLt_vt_self hx hx1 hq1 hqx hrT hr1
            rwa [hdec, hξv] at h
          obtain ⟨t, ht, hst, he⟩ := IH _ hrv (hrv.trans hv)
          exact ⟨.th0 (ξ / Om1) t, ⟨hq1, hqx, ht⟩, by simp only [LvGT.stage]; omega,
            by rw [LvGT.val_th0, he, hdec, hξv]⟩
        · obtain ⟨l, hlc, hls, hle⟩ := ihm (ξ / Om1) hqm
          have hqT : ξ / Om1 ∈ Tset x := vz_T_down hx hx1 hmT hm1 hqm.le
          have hrv : ξ % Om1 < v := by
            have h := (lvLevel_lt_vt hx hx1 hqT hqx (hqm.trans hm1) hrT hr1).2
            rwa [hdec, hξv] at h
          obtain ⟨t, ht, hst, he⟩ := IH _ hrv (hrv.trans hv)
          have hlB : ¬ LvGT.noB l := fun hn =>
            absurd (LvGT.noB_lt hx l hn hlc) (not_lt.2 (hle ▸ hqx))
          exact ⟨.tl l t, ⟨hlB, hlc, ht⟩, by simp only [LvGT.stage]; omega,
            by rw [LvGT.val_tl, he, hle, hdec, hξv]⟩
      · obtain ⟨L, rfl⟩ := indec_eq_opow hI
        have hL : L < ω ^ L := lt_of_le_of_ne (right_le_opow _ one_lt_omega0)
          (fun h => hE (by unfold InE; rw [← h]; exact h.symm))
        obtain ⟨t, ht, hst, e⟩ := IH L hL (hL.trans hv)
        exact ⟨.pw t, ht, hst, by rw [LvGT.val_pw, e]⟩
    · have hD : DecompR0 v := not_not.1 hI
      rcases hD with h0 | ⟨u1, u2, hu1, hu2, hsum⟩
      · exact absurd h0 (lt_of_lt_of_le hx.pos hxv).ne'
      obtain ⟨s1, h1, st1, e1⟩ := IH u1 hu1 (hu1.trans hv)
      obtain ⟨s2, h2, st2, e2⟩ := IH u2 hu2 (hu2.trans hv)
      exact ⟨.sm s1 s2, ⟨h1, h2⟩, by simp only [LvGT.stage]; omega, by rw [LvGT.val_sm, e1, e2, hsum]⟩

end Base2

namespace LvGT

/-- The tops lie below every next point above the base. -/
theorem lvg_top_lt_next {x u : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (n : ℕ) (hxu : x < u)
    (hu : LtInf1 u) : gT n x < u := by
  obtain ⟨m, -, -, hmin, hTm, -⟩ := T_next (Or.inr hx) hx1
  obtain ⟨hT, -, htop1, -⟩ := gT_facts hx hx1 n
  exact lt_of_lt_of_le ((hTm _ htop1).1 hT) (hmin u hxu hu)

theorem lvg_lt_next {x u : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {t : LvGT}
    (ht : CBt t x) (hxu : x < u) (hu : LtInf1 u) : val t x < u :=
  (lvg_T hx hx1 t ht).2.trans (lvg_top_lt_next hx hx1 _ hxu hu)

theorem lvg_lt_ups {x u : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {t : LvGT}
    (ht : CBt t x) (hxu : x < u) (hu : UpsPt u) : val t x < u :=
  lvg_lt_next hx hx1 ht hxu hu.2

/-- **Lemma EXACT** for `LvGT`: the value maps to the same term at the smaller base. -/
theorem pi {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) :
    ∀ t : LvGT, CBt t σ → val t ρ ∈ TB ρ σ ∧ pi σ ρ (val t ρ) = val t σ
  | .cst a, h => ⟨mem_TB_of_lt hB h, pi_lt hB h⟩
  | .bs, _ => pi_base hB
  | .th0 b t, h => by
      obtain ⟨h1, h2⟩ := pi hσ hρ hB t h.2.2
      have ht1 : val t ρ < Om1 := lvg_lt_Om1 hB.2.1 hB.2.2.2 t (CBt.mono hB.2.2.1.le h.2.2)
      obtain ⟨h3, h4⟩ := LvT.pi_vt_low hB h.2.1 h1 ht1
      simp only [val_th0]
      exact ⟨h3, by rw [h4, h2]⟩
  | .tl l t, h => by
      obtain ⟨hl1, hl2⟩ := pi hσ hρ hB l h.2.1
      obtain ⟨h1, h2⟩ := pi hσ hρ hB t h.2.2
      have hcρ : CBt l ρ := CBt.mono hB.2.2.1.le h.2.1
      have hρL : ρ ≤ val l ρ := le_of_not_noB hB.2.1 hB.2.2.2 l hcρ h.1
      have hL1 : val l ρ < Om1 := lvg_lt_Om1 hB.2.1 hB.2.2.2 l hcρ
      have ht1 : val t ρ < Om1 := lvg_lt_Om1 hB.2.1 hB.2.2.2 t (CBt.mono hB.2.2.1.le h.2.2)
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
      have ht1 : val t ρ < Om1 := lvg_lt_Om1 hB.2.1 hB.2.2.2 t (CBt.mono hB.2.2.1.le h)
      obtain ⟨h3, h4⟩ := pi_opowZ hσ hρ hB h1 ht1
      simp only [val_pw]
      exact ⟨h3, by rw [h4, h2]⟩

/-- **Lemma EXACT** in order form. -/
theorem uni_le {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ)
    {t u : LvGT} (ht : CBt t σ) (hu : CBt u σ) :
    val t ρ ≤ val u ρ ↔ val t σ ≤ val u σ := by
  obtain ⟨h1, h2⟩ := pi hσ hρ hB t ht
  obtain ⟨h3, h4⟩ := pi hσ hρ hB u hu
  rw [← h2, ← h4]
  exact ((pi_bijOn hB).2.le_iff_le h1 h3).symm

theorem uni_lt {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ)
    {t u : LvGT} (ht : CBt t σ) (hu : CBt u σ) :
    val t ρ < val u ρ ↔ val t σ < val u σ := by
  rw [← not_le, ← not_le, uni_le hσ hρ hB hu ht]

theorem uni_eq {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ)
    {t u : LvGT} (ht : CBt t σ) (hu : CBt u σ) :
    val t ρ = val u ρ ↔ val t σ = val u σ := by
  rw [le_antisymm_iff, le_antisymm_iff, uni_le hσ hρ hB ht hu, uni_le hσ hρ hB hu ht]

end LvGT

/-- The `small` field: a term is base-independent or at least the base. -/
theorem lvg_small : ∀ t : LvGT,
    (∀ x y, LvGT.val t x = LvGT.val t y) ∨
      (∀ x, InE x → x < Om1 → LvGT.CBt t x → x ≤ LvGT.val t x) := by
  intro t
  by_cases h : LvGT.noB t
  · exact Or.inl (LvGT.noB_val t h)
  · exact Or.inr (fun x hx hx1 hc => LvGT.le_of_not_noB hx hx1 t hc h)

end Googology.Trans.PoR.InaccPsi.R2

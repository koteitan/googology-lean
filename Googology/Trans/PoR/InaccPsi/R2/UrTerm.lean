import Googology.Trans.PoR.InaccPsi.R2.UrTr
import Googology.Trans.PoR.InaccPsi.R2.UnExist

/-!
# Gap levels: `ϑ`-nodes at every level, the translation decided by the leaves

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

The term type is `Un.UnT` (countable terms and level terms, nested to any depth).  In `Un` a node `thg m G r`
(`ϑᵗ(G[τ] + r[τ])`) needed a HIGH leaf (`HdM`: data `≥ τ`), so a level whose leaves are lower points (data in
`[υ_λ, υ_{λ+h})` at the base `υ_{λ+h}`, e.g. `ϑ^{υ_{λ+h}}(Ω₁·υ_{λ+h'})`) had no node.  Here the node condition
`Ngr` asks `HdD m τ G`: the leaves are high (`HdM`, as in `Un`) **or** the level is in full Cantor normal form and
every leaf is a parameter below the base (`LoL τ G`, a **low level**).  The translation `trr a` decides by the
leaves: at a low level it inserts `a` (`ϑ^a(Γ + ρ) ↦ ϑᵗ(Γ + a + ρ)`, [W07a] Def 6.2 subcase `Γ^* < α`, from
`R2.urVt_tr2`), otherwise it keeps the argument (subcase `Γ^* ≥ α`, `R2.ukVt_tr3`).  A low level over `α` becomes,
after the translation to `τ`, high or low over `τ` (`LoL_split`): a gap leaf in `[τ, α)` is high over `τ`.

* `urVt_trS` (**both subcases `Γ > 0` of [W07a] Def 6.2 in one statement**);
* `urDat_om` (`rjDat(Ω₁·ω^B) ≤ rjDat B`), `urDat_om_add` (`rjDat(Ω₁·ω^B + Y) ≤ max(rjDat B, rjDat Y)` for
  `0 < Y < Ω₁·ω^{B+1}`), `urDatUp`, `urDatLo` (**a low level has data `< τ`**);
* `urMem`, `urHiC_le`, `urDatM`, `urLe`, `urDown`, `urUp`, `urUp_eq`, `urMv` (**the `Un` lemmas for `WFr`**);
* `urTrA`, `urTrB` (**the translations `t^α_τ`, `t^τ_α` at every level**, high or low; `urTrB` asks the decision
  `HdD` over `α` at every node (`HdDA α`) and the leaves in `T^α`);
* `trr_map` (the translation commutes with a parameter map keeping the order to `a`), `ofUn_WF`
  (**`Un.UnT.WF ⇒ WFr`**).

New definitions: `LoL`, `HdD`, `Ngr`, `WFr`, `trr`, `HdDA`.  No new axiom (uses `R2.urVt_tr2`, `R2.ukVt_tr3`).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ur

open Ordinal Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Uh Googology.Trans.PoR.InaccPsi.R2.Un
  Googology.Trans.PoR.InaccPsi.R2.Un.UnT

/-- **Both subcases `Γ > 0` of [W07a] Def 6.2 / Lemma 6.3 at every level `Γ = Ω₁·M < ε_{Ω₁+1}`**, `1 ≤ M`: the
translation `t^α_τ` inserts `α` iff `rjDat Γ < α` (`R2.urVt_tr2`), and keeps the argument iff `α ≤ rjDat Γ`
(`R2.ukVt_tr3`). -/
theorem urVt_trS {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {n : ℕ} (hn : 1 ≤ n) {M ρ : Ordinal.{0}}
    (hM1 : 1 ≤ M) (hME : Om1 * M < Gg.ggE) (hρ1 : ρ < Om1) (hmem : Om1 * M + ρ ∈ Tset (Dl τ n))
    (hlt : vt (Dl τ n) (Om1 * M + ρ) < Dp τ n) :
    (Rj.rjDat (Om1 * M) < Dl τ n ∧ Om1 * M + (Dl τ n + ρ) ∈ Tset τ ∧
        vt (Dl τ n) (Om1 * M + ρ) = vt τ (Om1 * M + (Dl τ n + ρ))) ∨
      (Dl τ n ≤ Rj.rjDat (Om1 * M) ∧ Om1 * M + ρ ∈ Tset τ ∧
        vt (Dl τ n) (Om1 * M + ρ) = vt τ (Om1 * M + ρ)) := by
  rcases lt_or_ge (Rj.rjDat (Om1 * M)) (Dl τ n) with h | h
  · exact Or.inl ⟨h, (urVt_tr2 hτ hτ1 hn hM1 hME h hρ1).1 hmem hlt⟩
  · exact Or.inr ⟨h, (ukVt_tr3 hτ hτ1 hn hM1 hME h hρ1).1 hmem hlt⟩

/-! ## Low levels, the decision, the node conditions -/

/-- **A low level over `τ`**: every leaf is a parameter `< τ`. -/
def LoL (τ : Ordinal.{0}) : {k : Bool} → UnT k → Prop
  | _, .lf (.par p) => p < τ
  | _, .om b => LoL τ b
  | _, .ad x y => LoL τ x ∧ LoL τ y
  | _, _ => False

/-- **The decision at a node**: high leaves (`HdM`, as in `Un`) or a low level in full normal form. -/
def HdD (m : Bool) (τ : Ordinal.{0}) (G : UnT true) : Prop := HdM m τ G ∨ (m = true ∧ LoL τ G)

/-- **The node conditions of `thg m G r` over `τ`** (`ρ = r[τ]`, `Γ = G[τ]`): those of `Un.Ng` with `HdD` in place
of `HdM`. -/
structure Ngr (m : Bool) (τ : Ordinal.{0}) (G : UnT true) (ρ : Ordinal.{0}) : Prop where
  r1 : ρ < Om1
  gs : Gs G
  nf : NfM m τ G
  hd : HdD m τ G
  mem : ev τ G + ρ ∈ Tset τ
  bd : Lf (fun c => ev τ c < vt τ (ev τ G + ρ)) G
  rb : ρ < vt τ (ev τ G + ρ)

/-- The argument bounds over `τ` and the node conditions `Ngr`. -/
def WFr (τ : Ordinal.{0}) : {k : Bool} → UnT k → Prop
  | _, .par _ => True
  | _, .add s t => WFr τ s ∧ WFr τ t
  | _, .base => True
  | _, .th1 s => WFr τ s ∧ ev τ s < Om1
  | _, .thc _ r => WFr τ r ∧ ev τ r < Om1
  | _, .thg m G r => WFr τ G ∧ WFr τ r ∧ Ngr m τ G (ev τ r)
  | _, .lf c => WFr τ c ∧ ev τ c < Om1
  | _, .om b => WFr τ b
  | _, .ad x y => WFr τ x ∧ WFr τ y

open Classical in
/-- **The translation `t^a_b` of [W07a] Def 6.2 at every level** (`ϑ^a(0) ↦ a`, `ϑ^a(1 + ξ) ↦ ϑ^b(1 + a + ξ)`,
`ϑ^a(Ω₁·q + ρ) ↦ ϑ^b(Ω₁·q + a + ρ)`; `ϑ^a(Γ + ρ) ↦ ϑ^b(Γ + a + ρ)` at a low level, `ϑ^a(Γ + ρ) ↦ ϑ^b(Γ + ρ)`
otherwise, the leaves of `Γ` translated). -/
noncomputable def trr (a : Ordinal.{0}) : {k : Bool} → UnT k → UnT k
  | _, .par p => .par p
  | _, .add s t => .add (trr a s) (trr a t)
  | _, .base => .par a
  | _, .th1 s => .th1 (.add (.par a) (trr a s))
  | _, .thc q r => .thc q (.add (.par a) (trr a r))
  | _, .thg m G r => if LoL a G then .thg m (trr a G) (.add (.par a) (trr a r)) else .thg m (trr a G) (trr a r)
  | _, .lf c => .lf (trr a c)
  | _, .om b => .om (trr a b)
  | _, .ad x y => .ad (trr a x) (trr a y)

/-- The decision `HdD` at every `thg`-node. -/
def HdDA (τ : Ordinal.{0}) : {k : Bool} → UnT k → Prop
  | _, .par _ => True
  | _, .add s t => HdDA τ s ∧ HdDA τ t
  | _, .base => True
  | _, .th1 s => HdDA τ s
  | _, .thc _ r => HdDA τ r
  | _, .thg m G r => HdD m τ G ∧ HdDA τ G ∧ HdDA τ r
  | _, .lf c => HdDA τ c
  | _, .om b => HdDA τ b
  | _, .ad x y => HdDA τ x ∧ HdDA τ y

/-! ### Structural lemmas -/

theorem trr_thg_lo {a : Ordinal.{0}} {m : Bool} {G : UnT true} {r : UnT false} (h : LoL a G) :
    trr a (.thg m G r) = .thg m (trr a G) (.add (.par a) (trr a r)) := by
  simp only [trr, if_pos h]

theorem trr_thg_hi {a : Ordinal.{0}} {m : Bool} {G : UnT true} {r : UnT false} (h : ¬ LoL a G) :
    trr a (.thg m G r) = .thg m (trr a G) (trr a r) := by
  simp only [trr, if_neg h]

/-- **A low level is not translated** (its leaves are parameters). -/
theorem trr_LoL {a b : Ordinal.{0}} : ∀ {k : Bool} (G : UnT k), LoL b G → trr a G = G
  | _, .lf (.par _), _ => rfl
  | _, .om b', h => by simp only [trr, trr_LoL b' h]
  | _, .ad x y, h => by simp only [trr, trr_LoL x h.1, trr_LoL y h.2]
  | _, .lf (.add _ _), h => h.elim
  | _, .lf .base, h => h.elim
  | _, .lf (.th1 _), h => h.elim
  | _, .lf (.thc _ _), h => h.elim
  | _, .lf (.thg _ _ _), h => h.elim
  | _, .par _, h => h.elim
  | _, .add _ _, h => h.elim
  | _, .base, h => h.elim
  | _, .th1 _, h => h.elim
  | _, .thc _ _, h => h.elim
  | _, .thg _ _ _, h => h.elim

/-- **A low level over `a` is, over any `τ`, high in the normal-form mode or low** (a gap leaf `p ∈ [τ, a)` is a
high leaf over `τ`). -/
theorem LoL_split {a τ : Ordinal.{0}} : ∀ (G : UnT true), LoL a G → HdE τ G ∨ LoL τ G
  | .lf (.par p), _ => by
    rcases le_or_gt τ p with h | h
    · exact Or.inl h
    · exact Or.inr h
  | .om b, h => LoL_split b h
  | .ad x y, h => by
    rcases LoL_split x h.1 with hx | hx
    · exact Or.inl (Or.inl hx)
    rcases LoL_split y h.2 with hy | hy
    · exact Or.inl (Or.inr hy)
    · exact Or.inr ⟨hx, hy⟩
  | .lf (.add _ _), h => h.elim
  | .lf .base, h => h.elim
  | .lf (.th1 _), h => h.elim
  | .lf (.thc _ _), h => h.elim
  | .lf (.thg _ _ _), h => h.elim

/-- A low level has no high leaf. -/
theorem LoL_not_HdE {τ : Ordinal.{0}} : ∀ (G : UnT true), LoL τ G → ¬ HdE τ G
  | .lf (.par p), h, h' => absurd h (not_lt.2 h')
  | .om b, h, h' => LoL_not_HdE b h h'
  | .ad x y, h, h' => h'.elim (LoL_not_HdE x h.1) (LoL_not_HdE y h.2)
  | .lf (.add _ _), h, _ => h.elim
  | .lf .base, h, _ => h.elim
  | .lf (.th1 _), h, _ => h.elim
  | .lf (.thc _ _), h, _ => h.elim
  | .lf (.thg _ _ _), h, _ => h.elim

/-- **At a low level the decision is the low one**: `m = true`. -/
theorem HdD_lo {m : Bool} {τ : Ordinal.{0}} {G : UnT true} (hd : HdD m τ G) (h : LoL τ G) : m = true := by
  rcases hd with hd | hd
  · cases m with
    | false => exact absurd (Hd_HdE G hd) (LoL_not_HdE G h)
    | true => rfl
  · exact hd.1

/-- **Away from a low level the decision is the high one.** -/
theorem HdD_hi {m : Bool} {τ : Ordinal.{0}} {G : UnT true} (hd : HdD m τ G) (h : ¬ LoL τ G) : HdM m τ G :=
  hd.elim id (fun h' => absurd h'.2 h)

theorem LoL_map {τ σ : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} :
    ∀ {k : Bool} (G : UnT k), Lv (fun p => p < τ → f p < σ) G → LoL τ G → LoL σ (G.map f)
  | _, .lf (.par _), hl, h => hl h
  | _, .om b, hl, h => LoL_map b hl h
  | _, .ad x y, hl, h => ⟨LoL_map x hl.1 h.1, LoL_map y hl.2 h.2⟩
  | _, .lf (.add _ _), _, h => h.elim
  | _, .lf .base, _, h => h.elim
  | _, .lf (.th1 _), _, h => h.elim
  | _, .lf (.thc _ _), _, h => h.elim
  | _, .lf (.thg _ _ _), _, h => h.elim
  | _, .par _, _, h => h.elim
  | _, .add _ _, _, h => h.elim
  | _, .base, _, h => h.elim
  | _, .th1 _, _, h => h.elim
  | _, .thc _ _, _, h => h.elim
  | _, .thg _ _ _, _, h => h.elim

/-- **The decision is carried by a parameter map keeping the order to the base.** -/
theorem HdD_map {τ σ : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (m : Bool) (G : UnT true)
    (hl : Lv (fun p => (τ ≤ p → σ ≤ f p) ∧ (p < τ → f p < σ)) G) (h : HdD m τ G) : HdD m σ (G.map f) :=
  h.imp (HdM_map m G (Lv_mono (fun _ hp => hp.1) G hl))
    (fun h' => ⟨h'.1, LoL_map G (Lv_mono (fun _ hp => hp.2) G hl) h'.2⟩)

theorem HdDA_map {τ σ : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} :
    ∀ {k : Bool} (t : UnT k), Lv (fun p => (τ ≤ p → σ ≤ f p) ∧ (p < τ → f p < σ)) t → HdDA τ t →
      HdDA σ (t.map f)
  | _, .par _, _, _ => trivial
  | _, .add s t, hl, h => ⟨HdDA_map s hl.1 h.1, HdDA_map t hl.2 h.2⟩
  | _, .base, _, _ => trivial
  | _, .th1 s, hl, h => HdDA_map s hl h
  | _, .thc _ r, hl, h => HdDA_map r hl h
  | _, .thg m G r, hl, h => ⟨HdD_map m G hl.1 h.1, HdDA_map G hl.1 h.2.1, HdDA_map r hl.2 h.2.2⟩
  | _, .lf c, hl, h => HdDA_map c hl h
  | _, .om b, hl, h => HdDA_map b hl h
  | _, .ad x y, hl, h => ⟨HdDA_map x hl.1 h.1, HdDA_map y hl.2 h.2⟩

theorem WFr_HdDA {τ : Ordinal.{0}} : ∀ {k : Bool} (t : UnT k), WFr τ t → HdDA τ t
  | _, .par _, _ => trivial
  | _, .add s t, h => ⟨WFr_HdDA s h.1, WFr_HdDA t h.2⟩
  | _, .base, _ => trivial
  | _, .th1 s, h => WFr_HdDA s h.1
  | _, .thc _ r, h => WFr_HdDA r h.1
  | _, .thg _ G r, h => ⟨h.2.2.hd, WFr_HdDA G h.1, WFr_HdDA r h.2.1⟩
  | _, .lf c, h => WFr_HdDA c h.1
  | _, .om b, h => WFr_HdDA b h
  | _, .ad x y, h => ⟨WFr_HdDA x h.1, WFr_HdDA y h.2⟩

theorem LoL_back (a : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) :
    ∀ {k : Bool} (G : UnT k), Lv (fun p => p < a ↔ f p < f a) G → LoL (f a) (G.map f) → LoL a G
  | _, .lf (.par _), hl, h' => hl.2 h'
  | _, .om b, hl, h' => LoL_back a f b hl h'
  | _, .ad x y, hl, h' => ⟨LoL_back a f x hl.1 h'.1, LoL_back a f y hl.2 h'.2⟩
  | _, .lf (.add _ _), _, h' => h'.elim
  | _, .lf .base, _, h' => h'.elim
  | _, .lf (.th1 _), _, h' => h'.elim
  | _, .lf (.thc _ _), _, h' => h'.elim
  | _, .lf (.thg _ _ _), _, h' => h'.elim
  | _, .par _, _, h' => h'.elim
  | _, .add _ _, _, h' => h'.elim
  | _, .base, _, h' => h'.elim
  | _, .th1 _, _, h' => h'.elim
  | _, .thc _ _, _, h' => h'.elim
  | _, .thg _ _ _, _, h' => h'.elim


/-- **The translation commutes with a parameter map keeping the order to `a`** (so that the decision is the same
at `a` and at `f a`). -/
theorem trr_map (a : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) :
    ∀ {k : Bool} (t : UnT k), Lv (fun p => p < a ↔ f p < f a) t → (trr a t).map f = trr (f a) (t.map f)
  | _, .par _, _ => rfl
  | _, .add s t, h => by simp only [trr, map, trr_map a f s h.1, trr_map a f t h.2]
  | _, .base, _ => rfl
  | _, .th1 s, h => by simp only [trr, map, trr_map a f s h]
  | _, .thc _ r, h => by simp only [trr, map, trr_map a f r h]
  | _, .thg m G r, h => by
    have hiff : LoL a G ↔ LoL (f a) (G.map f) :=
      ⟨LoL_map G (Lv_mono (fun _ hp => hp.1) G h.1), fun h' => LoL_back a f G h.1 h'⟩
    by_cases hG : LoL a G
    · rw [trr_thg_lo hG, show (UnT.thg m G r).map f = UnT.thg m (G.map f) (r.map f) from rfl,
        trr_thg_lo (hiff.1 hG)]
      simp only [map, trr_map a f G h.1, trr_map a f r h.2]
    · rw [trr_thg_hi hG, show (UnT.thg m G r).map f = UnT.thg m (G.map f) (r.map f) from rfl,
        trr_thg_hi (fun h' => hG (hiff.2 h'))]
      simp only [map, trr_map a f G h.1, trr_map a f r h.2]
  | _, .lf c, h => by simp only [trr, map, trr_map a f c h]
  | _, .om b, h => by simp only [trr, map, trr_map a f b h]
  | _, .ad x y, h => by simp only [trr, map, trr_map a f x h.1, trr_map a f y h.2]

theorem Qs_trr {κ : Ordinal.{0}} (a : Ordinal.{0}) : ∀ {k : Bool} (t : UnT k), Qs κ t → Qs κ (trr a t)
  | _, .par _, _ => trivial
  | _, .add s t, h => ⟨Qs_trr a s h.1, Qs_trr a t h.2⟩
  | _, .base, _ => trivial
  | _, .th1 s, h => ⟨trivial, Qs_trr a s h⟩
  | _, .thc _ r, h => ⟨h.1, trivial, Qs_trr a r h.2⟩
  | _, .thg _ G r, h => by
    by_cases hG : LoL a G
    · rw [trr_thg_lo hG]; exact ⟨Qs_trr a G h.1, trivial, Qs_trr a r h.2⟩
    · rw [trr_thg_hi hG]; exact ⟨Qs_trr a G h.1, Qs_trr a r h.2⟩
  | _, .lf c, h => Qs_trr a c h
  | _, .om b, h => Qs_trr a b h
  | _, .ad x y, h => ⟨Qs_trr a x h.1, Qs_trr a y h.2⟩

theorem Lv_trr {P : Ordinal.{0} → Prop} {a : Ordinal.{0}} (ha : P a) :
    ∀ {k : Bool} (t : UnT k), Lv P t → Lv P (trr a t)
  | _, .par _, h => h
  | _, .add s t, h => ⟨Lv_trr ha s h.1, Lv_trr ha t h.2⟩
  | _, .base, _ => ha
  | _, .th1 s, h => ⟨ha, Lv_trr ha s h⟩
  | _, .thc _ r, h => ⟨ha, Lv_trr ha r h⟩
  | _, .thg _ G r, h => by
    by_cases hG : LoL a G
    · rw [trr_thg_lo hG]; exact ⟨Lv_trr ha G h.1, ha, Lv_trr ha r h.2⟩
    · rw [trr_thg_hi hG]; exact ⟨Lv_trr ha G h.1, Lv_trr ha r h.2⟩
  | _, .lf c, h => Lv_trr ha c h
  | _, .om b, h => Lv_trr ha b h
  | _, .ad x y, h => ⟨Lv_trr ha x h.1, Lv_trr ha y h.2⟩

theorem Gs_trr (a : Ordinal.{0}) : ∀ {k : Bool} (t : UnT k), Gs (trr a t) ↔ Gs t
  | _, .par _ => Iff.rfl
  | _, .add _ _ => Iff.rfl
  | _, .base => Iff.rfl
  | _, .th1 _ => Iff.rfl
  | _, .thc _ _ => Iff.rfl
  | _, .thg _ G _ => by
    by_cases hG : LoL a G
    · rw [trr_thg_lo hG]; exact Iff.rfl
    · rw [trr_thg_hi hG]; exact Iff.rfl
  | _, .lf _ => Iff.rfl
  | _, .om _ => Iff.rfl
  | _, .ad x y => and_congr (Gs_trr a x) (Gs_trr a y)

theorem IsOm_trr (a : Ordinal.{0}) : ∀ (t : UnT true), IsOm (trr a t) ↔ IsOm t
  | .lf _ => Iff.rfl
  | .om _ => Iff.rfl
  | .ad _ _ => Iff.rfl

theorem HiC_trr {τ a : Ordinal.{0}} (hτa : τ ≤ a) : ∀ (c : UnT false), HiC a c → HiC τ (trr a c)
  | .par _, h => hτa.trans h
  | .add s _, h => HiC_trr hτa s h
  | .base, _ => hτa
  | .th1 _, _ => trivial
  | .thc _ _, _ => trivial
  | .thg _ G _, _ => by
    by_cases hG : LoL a G
    · rw [trr_thg_lo hG]; trivial
    · rw [trr_thg_hi hG]; trivial

theorem Hd_trr {τ a : Ordinal.{0}} (hτa : τ ≤ a) : ∀ (G : UnT true), Hd a G → Hd τ (trr a G)
  | .lf c, h => HiC_trr hτa c h
  | .om b, h => Hd_trr hτa b h
  | .ad x _, h => Hd_trr hτa x h

theorem HdE_trr {τ a : Ordinal.{0}} (hτa : τ ≤ a) : ∀ (G : UnT true), HdE a G → HdE τ (trr a G)
  | .lf c, h => HiC_trr hτa c h
  | .om b, h => HdE_trr hτa b h
  | .ad x y, h => h.imp (HdE_trr hτa x) (HdE_trr hτa y)

theorem HdM_trr {τ a : Ordinal.{0}} (hτa : τ ≤ a) : ∀ (m : Bool) (G : UnT true), HdM m a G → HdM m τ (trr a G)
  | false, G, h => Hd_trr hτa G h
  | true, G, h => HdE_trr hτa G h

/-- **`Un.UnT.WF ⇒ WFr`** (every `Un` node is high). -/
theorem ofUn_WF {τ : Ordinal.{0}} : ∀ {k : Bool} (t : UnT k), UnT.WF τ t → WFr τ t
  | _, .par _, _ => trivial
  | _, .add s t, h => ⟨ofUn_WF s h.1, ofUn_WF t h.2⟩
  | _, .base, _ => trivial
  | _, .th1 s, h => ⟨ofUn_WF s h.1, h.2⟩
  | _, .thc _ r, h => ⟨ofUn_WF r h.1, h.2⟩
  | _, .thg _ G r, h => ⟨ofUn_WF G h.1, ofUn_WF r h.2.1,
      ⟨h.2.2.r1, h.2.2.gs, h.2.2.nf, Or.inl h.2.2.hd, h.2.2.mem, h.2.2.bd, h.2.2.rb⟩⟩
  | _, .lf c, h => ⟨ofUn_WF c h.1, h.2⟩
  | _, .om b, h => ofUn_WF b h
  | _, .ad x y, h => ⟨ofUn_WF x h.1, ofUn_WF y h.2⟩

/-- On terms without `thg`-nodes (`Un.ofUhN`), `WFr` is `Un.UnT.WF`. -/
theorem WFr_ofUhN {τ : Ordinal.{0}} : ∀ t : UhT, WFr τ (ofUhN t) ↔ UnT.WF τ (ofUhN t)
  | .par _ => Iff.rfl
  | .add s t => and_congr (WFr_ofUhN s) (WFr_ofUhN t)
  | .base => Iff.rfl
  | .th1 s => and_congr (WFr_ofUhN s) Iff.rfl
  | .thc _ r => and_congr (WFr_ofUhN r) Iff.rfl

/-- On the terms of `Ub.UbT` (`Un.ofUbn`), `WFr` is `Un.UnT.WF`. -/
theorem WFr_ofUbn {τ : Ordinal.{0}} (t : Ub.UbT) : WFr τ (ofUbn t) ↔ UnT.WF τ (ofUbn t) := WFr_ofUhN _

/-! ### Values and data of level terms -/

/-- Countable leaves give a value below `ε_{Ω₁+1}`. -/
theorem ev_lt_Er {τ : Ordinal.{0}} : ∀ (G : UnT true), WFr τ G → ev τ G < Gg.ggE
  | .lf _, h => h.2.trans Rj.rj_Om1_lt_E
  | .om b, h => by
    have hb := ev_lt_Er b h
    simp only [ev]
    rw [Si.si_Om1_opow_eq]
    have h1 : Om1 + ev τ b < Gg.ggE := Si.si_E_inE.add_lt Rj.rj_Om1_lt_E hb
    have h2 : ω ^ (Om1 + ev τ b) < ω ^ (Gg.ggE : Ordinal.{0}) := (opow_lt_opow_iff_right one_lt_omega0).2 h1
    have h3 : ω ^ (Gg.ggE : Ordinal.{0}) = Gg.ggE := Si.si_E_inE
    rwa [h3] at h2
  | .ad x y, h => Si.si_E_inE.add_lt (ev_lt_Er x h.1) (ev_lt_Er y h.2)

/-- `rjDat(Ω₁·ω^B) ≤ rjDat B`. -/
theorem urDat_om {B : Ordinal.{0}} (hBE : B < Gg.ggE) : Rj.rjDat (Om1 * ω ^ B) ≤ Rj.rjDat B := by
  rcases eq_or_ne B 0 with rfl | hB0
  · rw [opow_zero, mul_one, Rj.rjDat_Om1]; exact zero_le
  have hg : Om1 * ω ^ B = ω ^ (Om1 + B) := Si.si_Om1_opow_eq B
  have hgE : Om1 + B < Gg.ggE := Si.si_E_inE.add_lt Rj.rj_Om1_lt_E hBE
  have h2 : ω ^ (Om1 + B) < Gg.ggE := by
    have := (opow_lt_opow_iff_right one_lt_omega0).2 hgE
    rwa [show ω ^ (Gg.ggE : Ordinal.{0}) = Gg.ggE from Si.si_E_inE] at this
  have h1 : Om1 < ω ^ (Om1 + B) := by
    rw [← hg]
    conv_lhs => rw [← mul_one Om1]
    have h01 : (1 : Ordinal.{0}) < ω ^ B := by
      simpa using (opow_lt_opow_iff_right one_lt_omega0).2 (pos_iff_ne_zero.2 hB0)
    exact (mul_lt_mul_iff_right₀ Rj.rj_Om1_pos).2 h01
  rw [hg, Si.si_rjDat_opow h1 h2, unDat_Om1_add hBE]

/-- **`rjDat(Ω₁·ω^B + Y) ≤ max(rjDat B, rjDat Y)`** for `B < ε_{Ω₁+1}`, `0 < Y < Ω₁·ω^{B+1}`. -/
theorem urDat_om_add {B Y : Ordinal.{0}} (hBE : B < Gg.ggE) (hy0 : Y ≠ 0) (hy : Y < Om1 * ω ^ (B + 1)) :
    Rj.rjDat (Om1 * ω ^ B + Y) ≤ max (Rj.rjDat B) (Rj.rjDat Y) := by
  obtain ⟨g, hg⟩ : ∃ g, g = Om1 + B := ⟨_, rfl⟩
  have hgE : g < Gg.ggE := hg ▸ Si.si_E_inE.add_lt Rj.rj_Om1_lt_E hBE
  have hwg : Om1 * ω ^ B = ω ^ g := by rw [hg]; exact Si.si_Om1_opow_eq B
  have hy' : Y < ω ^ g * ω := by rw [← hwg, Uk.UkL.om_mul_omega]; exact hy
  have hw0 : ω ^ g ≠ 0 := (opow_pos _ omega0_pos).ne'
  have hdecy := Ordinal.div_add_mod Y (ω ^ g)
  have hq : Y / ω ^ g < ω := (Ordinal.lt_mul_iff_div_lt hw0).1 hy'
  have hrem : Y % ω ^ g < ω ^ g := Ordinal.mod_lt Y hw0
  have hsum : Om1 * ω ^ B + Y = ω ^ g * (1 + Y / ω ^ g) + Y % ω ^ g := by
    rw [hwg, mul_add, mul_one, add_assoc, hdecy]
  have hv0 : 1 + Y / ω ^ g ≠ 0 := (lt_of_lt_of_le zero_lt_one le_self_add).ne'
  have hvω : 1 + Y / ω ^ g < ω := by
    obtain ⟨m, hm⟩ := lt_omega0.1 hq
    rw [hm]; exact_mod_cast natCast_lt_omega0 (1 + m)
  have hOg : Om1 ≤ ω ^ g := by
    rw [← Rj.rj_Om1_opow]
    exact (opow_le_opow_iff_right one_lt_omega0).2 (hg ▸ le_self_add)
  have h1 : Om1 < ω ^ g * (1 + Y / ω ^ g) + Y % ω ^ g := by
    rw [← hsum, hwg]
    exact lt_of_le_of_lt hOg (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hy0))
  have hwE : ω ^ (g + 1) < Gg.ggE := by
    have h3 : ω ^ (Gg.ggE : Ordinal.{0}) = Gg.ggE := Si.si_E_inE
    have hg1 : g + 1 < Gg.ggE := Si.si_E_inE.add_lt hgE (Ub.ub_one_lt Si.si_E_inE)
    have := (opow_lt_opow_iff_right one_lt_omega0).2 hg1
    rwa [h3] at this
  have hle : ∀ v : Ordinal.{0}, v < ω → ω ^ g * v + Y % ω ^ g < ω ^ (g + 1) := by
    intro v hv
    rw [opow_add, opow_one]
    calc ω ^ g * v + Y % ω ^ g < ω ^ g * v + ω ^ g := (add_lt_add_iff_left _).2 hrem
      _ = ω ^ g * (v + 1) := by rw [mul_add_one]
      _ ≤ ω ^ g * ω := mul_le_mul_right (Order.add_one_le_of_lt hv) _
  have hlt : ω ^ g * (1 + Y / ω ^ g) + Y % ω ^ g < Gg.ggE := (hle _ hvω).trans hwE
  have hgB : Rj.rjDat g ≤ Rj.rjDat B := by rw [hg, unDat_Om1_add hBE]
  rw [hsum, Si.si_rjDat_form hv0 hvω hrem h1 hlt]
  refine max_le (hgB.trans (le_max_left _ _)) ?_
  by_cases hq0 : Y / ω ^ g = 0
  · have hyr : Y % ω ^ g = Y := by
      have e := hdecy
      rw [hq0, mul_zero, zero_add] at e
      exact e
    rw [hyr]; exact le_max_right _ _
  · rcases lt_or_ge Om1 Y with hO | hO
    · have hyq : Y = ω ^ g * (Y / ω ^ g) + Y % ω ^ g := hdecy.symm
      have h1' : Om1 < ω ^ g * (Y / ω ^ g) + Y % ω ^ g := by rw [← hyq]; exact hO
      have hlt' : ω ^ g * (Y / ω ^ g) + Y % ω ^ g < Gg.ggE := (hle _ hq).trans hwE
      have e : Rj.rjDat Y = max (Rj.rjDat g) (Rj.rjDat (Y % ω ^ g)) := by
        conv_lhs => rw [← hdecy]
        exact Si.si_rjDat_form hq0 hq hrem h1' hlt'
      rw [e]; exact (le_max_right _ _).trans (le_max_right _ _)
    · have hy1 : ω ^ g ≤ Y := by
        rw [← hdecy]
        exact le_trans (le_mul_left _ (pos_iff_ne_zero.2 hq0)) le_self_add
      have hYO : Y = Om1 := le_antisymm hO (hOg.trans hy1)
      have hgO : ω ^ g = Om1 := le_antisymm (hy1.trans hYO.le) hOg
      have : Y % ω ^ g = 0 := by rw [hYO, hgO, Ordinal.mod_self]
      rw [this, Rj.rjDat_small Rj.rj_Om1_pos]; exact zero_le

/-- **The data of a level in full Cantor normal form are below every bound of its leaves** (`0 < V`). -/
theorem urDatUp {τ V : Ordinal.{0}} (hV : 0 < V) :
    ∀ (G : UnT true), WFr τ G → FNF τ G → Lf (fun c => ev τ c < V) G → Rj.rjDat (ev τ G) < V
  | .lf c, hw, _, hc => by
    show Rj.rjDat (ev τ c) < V
    rw [Rj.rjDat_small hw.2]; exact hc
  | .om b, hw, hf, hc => by
    simp only [ev]
    exact lt_of_le_of_lt (urDat_om (ev_lt_Er b hw)) (urDatUp hV b hw hf hc)
  | .ad (.om b) y, hw, hf, hc => by
    have hbE := ev_lt_Er b hw.1
    have hb := urDatUp hV b hw.1 hf.1 hc.1
    have hy := urDatUp hV y hw.2 hf.2.1 hc.2
    simp only [ev]
    rcases eq_or_ne (ev τ y) 0 with h0 | h0
    · rw [h0, add_zero]; exact lt_of_le_of_lt (urDat_om hbE) hb
    · have hyl : ev τ y < Om1 * ω ^ (ev τ b + 1) := by rw [← Uk.UkL.om_mul_omega]; exact hf.2.2.2
      exact lt_of_le_of_lt (urDat_om_add hbE h0 hyl) (max_lt hb hy)
  | .ad (.lf _) _, _, hf, _ => hf.2.2.1.elim
  | .ad (.ad _ _) _, _, hf, _ => hf.2.2.1.elim

/-- The leaves of a low level are parameters below the base. -/
theorem LoL_Lf {τ : Ordinal.{0}} : ∀ {k : Bool} (G : UnT k), LoL τ G → Lf (fun c => ev τ c < τ) G
  | _, .lf (.par _), h => h
  | _, .om b, h => LoL_Lf b h
  | _, .ad x y, h => ⟨LoL_Lf x h.1, LoL_Lf y h.2⟩
  | _, .lf (.add _ _), h => h.elim
  | _, .lf .base, h => h.elim
  | _, .lf (.th1 _), h => h.elim
  | _, .lf (.thc _ _), h => h.elim
  | _, .lf (.thg _ _ _), h => h.elim
  | _, .par _, h => h.elim
  | _, .add _ _, h => h.elim
  | _, .base, h => h.elim
  | _, .th1 _, h => h.elim
  | _, .thc _ _, h => h.elim
  | _, .thg _ _ _, h => h.elim

/-- **A low level in full Cantor normal form has data `< τ`** (`Γ^{*τ} < τ`, the condition of `R2.urVt_tr2`). -/
theorem urDatLo {τ : Ordinal.{0}} (hτ0 : 0 < τ) (G : UnT true) (hw : WFr τ G) (hf : FNF τ G) (hl : LoL τ G) :
    Rj.rjDat (ev τ G) < τ :=
  urDatUp hτ0 G hw hf (LoL_Lf G hl)

/-! ## Membership, order, base change -/

theorem urMem {κ τ : Ordinal.{0}} (hB : Bases κ τ) :
    ∀ (t : UnT false), Lv (· ∈ Tset τ) t → WFr τ t → Qs κ t → ev τ t ∈ Tset τ
  | .par _, hl, _, _ => hl
  | .add s t, hl, hw, hq => vzT_add hB.2.1 hB.2.2.2 (urMem hB s hl.1 hw.1 hq.1) (urMem hB t hl.2 hw.2 hq.2)
  | .base, _, _, _ => uh_T_le hB.2.1 hB.2.2.2 le_rfl
  | .th1 s, hl, hw, hq => by
    have hτ1 := hB.2.2.2
    have h1 : (1 : Ordinal.{0}) ∈ Tset τ := uh_T_le hB.2.1 hτ1 (Ub.ub_one_lt hB.2.1).le
    have hO : (1 : Ordinal.{0}) < Om1 := (Ub.ub_one_lt hB.2.1).trans hτ1
    exact (vt_mem hB.2.1 hτ1 (vzT_add hB.2.1 hτ1 h1 (urMem hB s hl hw.1 hq)) (Om1_add_lt hO hw.2)).1
  | .thc _ r, hl, hw, hq => by
    obtain ⟨h1, h2⟩ := uh_arg_T hB hq.1 (urMem hB r hl hw.1 hq.2) hw.2
    exact (vt_memTwo hB.2.1 hB.2.2.2 h1 h2).1
  | .thg _ G _, _, hw, _ =>
    (vt_memTwo hB.2.1 hB.2.2.2 hw.2.2.mem (Uk.arg_lt2 (ev_lt_Er G hw.1) hw.2.2.r1)).1

/-- **A high countable term is `≥ τ`** ([W07a] Lemma 3.30 through `R2.vt_memTwo` at the `ϑ`-heads, Lemma 4.2
through `R2.vt_wbar` at `ϑᵗ(1 + ξ)`). -/
theorem urHiC_le {κ τ : Ordinal.{0}} (hB : Bases κ τ) :
    ∀ (c : UnT false), Lv (· ∈ Tset τ) c → WFr τ c → Qs κ c → HiC τ c → τ ≤ ev τ c
  | .par _, _, _, _, h => h
  | .add s _, hl, hw, hq, h => by
    simp only [ev]; exact (urHiC_le hB s hl.1 hw.1 hq.1 h).trans le_self_add
  | .base, _, _, _, _ => le_rfl
  | .th1 s, _, hw, _, _ => by
    simp only [ev]; rw [vt_wbar hB.2.1 hB.2.2.2 hw.2]
    exact le_self_add.trans (Se.se_wbar_gt _).le
  | .thc _ r, hl, hw, hq, _ => by
    obtain ⟨h1, h2⟩ := uh_arg_T hB hq.1 (urMem hB r hl hw.1 hq.2) hw.2
    exact (vt_memTwo hB.2.1 hB.2.2.2 h1 h2).2.1
  | .thg _ G _, _, hw, _, _ =>
    (vt_memTwo hB.2.1 hB.2.2.2 hw.2.2.mem (Uk.arg_lt2 (ev_lt_Er G hw.1) hw.2.2.r1)).2.1

/-- **The decision `Γ^{*τ} ≥ τ` in the head mode**: no absorption of the head and a high head leaf give
`τ ≤ rjDat Γ` (`Γ = G[τ]`). -/
theorem urDatHb {κ τ : Ordinal.{0}} (hB : Bases κ τ) :
    ∀ (G : UnT true), Lv (· ∈ Tset τ) G → WFr τ G → Qs κ G → HbS τ G → Hd τ G →
      τ ≤ Rj.rjDat (ev τ G) ∧ ev τ G ≠ 0
  | .lf c, hl, hw, hq, _, hd => by
    have h1 : τ ≤ ev τ c := urHiC_le hB c hl hw.1 hq hd
    simp only [ev]
    rw [Rj.rjDat_small hw.2]
    exact ⟨h1, ((InE.pos hB.2.1).trans_le h1).ne'⟩
  | .om b, hl, hw, hq, hb, hd => by
    obtain ⟨h1, h2⟩ := urDatHb hB b hl hw hq hb hd
    have hbE := ev_lt_Er b hw
    have := Uk.UkL.dat_om_add (y := 0) h2 hbE (mul_pos Rj.rj_Om1_pos (opow_pos _ omega0_pos))
    rw [add_zero] at this
    simp only [ev]
    exact ⟨h1.trans this, (mul_pos Rj.rj_Om1_pos (opow_pos _ omega0_pos)).ne'⟩
  | .ad (.om b) y, hl, hw, hq, hb, hd => by
    obtain ⟨h1, h2⟩ := urDatHb hB b hl.1 hw.1 hq.1 hb.1 hd
    have hbE := ev_lt_Er b hw.1
    have hy : ev τ y < Om1 * ω ^ (ev τ b + 1) := by rw [← Uk.UkL.om_mul_omega]; exact hb.2.2
    have := Uk.UkL.dat_om_add h2 hbE hy
    simp only [ev]
    exact ⟨h1.trans this,
      (lt_of_lt_of_le (mul_pos Rj.rj_Om1_pos (opow_pos _ omega0_pos)) le_self_add).ne'⟩
  | .ad (.lf _) _, _, _, _, hb, _ => hb.2.1.elim
  | .ad (.ad _ _) _, _, _, _, hb, _ => hb.2.1.elim

/-- **The decision `Γ^{*τ} ≥ τ` in the normal-form mode**: full Cantor normal form and SOME high leaf (also in a
non-head summand) give `τ ≤ rjDat Γ`. -/
theorem urDatFN {κ τ : Ordinal.{0}} (hB : Bases κ τ) :
    ∀ (G : UnT true), Lv (· ∈ Tset τ) G → WFr τ G → Qs κ G → FNF τ G → HdE τ G →
      τ ≤ Rj.rjDat (ev τ G) ∧ ev τ G ≠ 0
  | .lf c, hl, hw, hq, _, hd => by
    have h1 : τ ≤ ev τ c := urHiC_le hB c hl hw.1 hq hd
    simp only [ev]
    rw [Rj.rjDat_small hw.2]
    exact ⟨h1, ((InE.pos hB.2.1).trans_le h1).ne'⟩
  | .om b, hl, hw, hq, hb, hd => by
    obtain ⟨h1, h2⟩ := urDatFN hB b hl hw hq hb hd
    have hbE := ev_lt_Er b hw
    have := Uk.UkL.dat_om_add (y := 0) h2 hbE (mul_pos Rj.rj_Om1_pos (opow_pos _ omega0_pos))
    rw [add_zero] at this
    simp only [ev]
    exact ⟨h1.trans this, (mul_pos Rj.rj_Om1_pos (opow_pos _ omega0_pos)).ne'⟩
  | .ad (.om b) y, hl, hw, hq, hb, hd => by
    have hbE := ev_lt_Er b hw.1
    have hy : ev τ y < Om1 * ω ^ (ev τ b + 1) := by rw [← Uk.UkL.om_mul_omega]; exact hb.2.2.2
    have hne : ev τ (UnT.ad (UnT.om b) y) ≠ 0 := by
      simp only [ev]
      exact (lt_of_lt_of_le (mul_pos Rj.rj_Om1_pos (opow_pos _ omega0_pos)) le_self_add).ne'
    rcases hd with hd | hd
    · obtain ⟨h1, h2⟩ := urDatFN hB b hl.1 hw.1 hq.1 hb.1 hd
      have := Uk.UkL.dat_om_add h2 hbE hy
      exact ⟨by simp only [ev]; exact h1.trans this, hne⟩
    · obtain ⟨h1, h2⟩ := urDatFN hB y hl.2 hw.2 hq.2 hb.2.1 hd
      have := dat_om_add_r hbE h2 hy
      exact ⟨by simp only [ev]; exact h1.trans this, hne⟩
  | .ad (.lf _) _, _, _, _, hb, _ => hb.2.2.1.elim
  | .ad (.ad _ _) _, _, _, _, hb, _ => hb.2.2.1.elim

/-- **The decision `Γ^{*τ} ≥ τ` in either mode.** -/
theorem urDatM {κ τ : Ordinal.{0}} (hB : Bases κ τ) :
    ∀ (m : Bool) (G : UnT true), Lv (· ∈ Tset τ) G → WFr τ G → Qs κ G → NfM m τ G → HdM m τ G →
      τ ≤ Rj.rjDat (ev τ G) ∧ ev τ G ≠ 0
  | false, G, hl, hw, hq, hn, hd => urDatHb hB G hl hw hq hn hd
  | true, G, hl, hw, hq, hn, hd => urDatFN hB G hl hw hq hn hd

/-! ## Order of the parts -/

/-- **Every parameter and every node value is `≤` the value** (for level terms: `≤` every bound `V` of the
leaves). -/
theorem urLeB {κ τ : Ordinal.{0}} (hB : Bases κ τ) :
    ∀ {k : Bool} (t : UnT k), Lv (· ∈ Tset τ) t → WFr τ t → Qs κ t → ∀ V : Ordinal.{0},
      (k = false → ev τ t ≤ V) → Lf (fun c => ev τ c ≤ V) t → Lv (· ≤ V) t ∧ Nd τ (· ≤ V) t
  | _, .par _, _, _, _, _, hv, _ => ⟨hv rfl, trivial⟩
  | _, .add s t, hl, hw, hq, V, hv, _ => by
    have hs : ev τ s ≤ V := le_self_add.trans (hv rfl)
    have ht : ev τ t ≤ V := le_add_self.trans (hv rfl)
    obtain ⟨a1, a2⟩ := urLeB hB s hl.1 hw.1 hq.1 V (fun _ => hs) (Lf_cnt _ s)
    obtain ⟨b1, b2⟩ := urLeB hB t hl.2 hw.2 hq.2 V (fun _ => ht) (Lf_cnt _ t)
    exact ⟨⟨a1, b1⟩, ⟨a2, b2⟩⟩
  | _, .base, _, _, _, _, _, _ => ⟨trivial, trivial⟩
  | _, .th1 s, hl, hw, hq, V, hv, _ => by
    have hle : ev τ s ≤ ev τ (.th1 s) := by
      simp only [ev]; rw [vt_wbar hB.2.1 hB.2.2.2 hw.2]
      exact le_add_self.trans (Se.se_wbar_gt _).le
    exact urLeB hB s hl hw.1 hq V (fun _ => hle.trans (hv rfl)) (Lf_cnt _ s)
  | _, .thc q r, hl, hw, hq, V, hv, _ => by
    have hrT := urMem hB r hl hw.1 hq.2
    have hlt : ev τ r < ev τ (.thc q r) := uhLt_vt_self hB hq.1 hrT hw.2
    obtain ⟨a1, a2⟩ := urLeB hB r hl hw.1 hq.2 V (fun _ => hlt.le.trans (hv rfl)) (Lf_cnt _ r)
    exact ⟨a1, hv rfl, a2⟩
  | _, .thg m G r, hl, hw, hq, V, hv, _ => by
    have hvV : ev τ (UnT.thg m G r) ≤ V := hv rfl
    obtain ⟨a1, a2⟩ := urLeB hB r hl.2 hw.2.1 hq.2 V (fun _ => hw.2.2.rb.le.trans hvV) (Lf_cnt _ r)
    obtain ⟨l1, l2⟩ := urLeB hB G hl.1 hw.1 hq.1 V (fun h => nomatch h)
      (Lf_mono (fun c hc => hc.le.trans hvV) G hw.2.2.bd)
    exact ⟨⟨l1, a1⟩, ⟨hvV, l2, a2⟩⟩
  | _, .lf c, hl, hw, hq, V, _, hc => urLeB hB c hl hw.1 hq V (fun _ => hc) (Lf_cnt _ c)
  | _, .om b, hl, hw, hq, V, _, hc => urLeB hB b hl hw hq V (fun h => nomatch h) hc
  | _, .ad x y, hl, hw, hq, V, _, hc => by
    obtain ⟨a1, a2⟩ := urLeB hB x hl.1 hw.1 hq.1 V (fun h => nomatch h) hc.1
    obtain ⟨b1, b2⟩ := urLeB hB y hl.2 hw.2 hq.2 V (fun h => nomatch h) hc.2
    exact ⟨⟨a1, b1⟩, ⟨a2, b2⟩⟩

/-- **Every parameter and every node value is `≤` the value.** -/
theorem urLe {κ τ : Ordinal.{0}} (hB : Bases κ τ) (t : UnT false) (hl : Lv (· ∈ Tset τ) t) (hw : WFr τ t)
    (hq : Qs κ t) : Lv (· ≤ ev τ t) t ∧ Nd τ (· ≤ ev τ t) t :=
  urLeB hB t hl hw hq _ (fun _ => le_rfl) (UnT.Lf_cnt _ t)

/-! ## The base change -/

/-- **The base change on terms of both sorts** ([W07a] Def 5.1, Lemma 5.3 through `R2.pi_vt`, `R2.pi_vt_two`,
`R2.pi_add`, `Uh.uh_Om1_mul_TB`, `R2.siOm1_opow_TB`): values, argument bounds, node conditions (both modes), the
`·ω`-bounds of the sums and the leaf bounds are carried by `π_{σ,τ}`. -/
theorem urDownB {κ σ τ : Ordinal.{0}} (h : Bases σ τ) (hκσ : κ ≤ σ) :
    ∀ {k : Bool} (t : UnT k), WFr τ t → Lv (· ∈ TB τ σ) t → Qs κ t →
      ev τ t ∈ TB τ σ ∧ pi σ τ (ev τ t) = ev σ (t.map (pi σ τ)) ∧ WFr σ (t.map (pi σ τ)) ∧
      (HbS τ t → HbS σ (t.map (pi σ τ))) ∧ (FNF τ t → FNF σ (t.map (pi σ τ))) ∧
      (∀ V ∈ TB τ σ, Lf (fun c => ev τ c < V) t → Lf (fun c => ev σ c < pi σ τ V) (t.map (pi σ τ)))
  | _, .par p, _, hp, _ => ⟨hp, rfl, trivial, fun _ => trivial, fun _ => trivial, fun _ _ _ => trivial⟩
  | _, .add s t, hw, hl, hq => by
    obtain ⟨a1, a2, a3, -⟩ := urDownB h hκσ s hw.1 hl.1 hq.1
    obtain ⟨b1, b2, b3, -⟩ := urDownB h hκσ t hw.2 hl.2 hq.2
    obtain ⟨c1, c2⟩ := pi_add h a1 b1
    refine ⟨c1, ?_, ⟨a3, b3⟩, fun _ => trivial, fun _ => trivial, fun _ _ _ => trivial⟩
    simp only [ev, map]; rw [c2, a2, b2]
  | _, .base, _, _, _ =>
    ⟨(pi_base h).1, (pi_base h).2, trivial, fun _ => trivial, fun _ => trivial, fun _ _ _ => trivial⟩
  | _, .th1 s, hw, hl, hq => by
    obtain ⟨a1, a2, a3, -⟩ := urDownB h hκσ s hw.1 hl hq
    have hσ1 : (1 : Ordinal.{0}) < σ := Ub.ub_one_lt h.1
    have h1T : (1 : Ordinal.{0}) ∈ TB τ σ := (TB_inter_lt h (hσ1.trans h.2.2.1)).2 hσ1
    obtain ⟨c1, c2⟩ := pi_add h h1T a1
    have hO : (1 : Ordinal.{0}) < Om1 := hσ1.trans (h.2.2.1.trans h.2.2.2)
    have hlt1 : 1 + ev τ s < Om1 := Om1_add_lt hO hw.2
    obtain ⟨d1, d2⟩ := vt_mem h.2.1 h.2.2.2 c1.1 hlt1
    refine ⟨⟨d1, by
      show ((Par τ (vt τ (1 + ev τ s)) : Set Ordinal.{0})) ⊆ Set.Iio σ; rw [d2]; exact c1.2⟩, ?_, ⟨a3, ?_⟩,
      fun _ => trivial, fun _ => trivial, fun _ _ _ => trivial⟩
    · simp only [ev, map]; rw [pi_vt h c1 hlt1, c2, pi_lt h hσ1, a2]
    · rw [← a2]; exact down_lt_Om1 h a1 hw.2
  | _, .thc q r, hw, hl, hq => by
    obtain ⟨a1, a2, a3, -⟩ := urDownB h hκσ r hw.1 hl hq.2
    obtain ⟨g1, g2⟩ := uh_Om1_mul_TB h q hq.1.2.1 (hq.1.2.2.trans_le hκσ)
    obtain ⟨c1, c2⟩ := pi_add h g1 a1
    have hlt2 : Om1 * q + ev τ r < OmTwo := Rj.rj_arg_lt hq.1.2.1 hw.2
    obtain ⟨d1, -, -, -, d2⟩ := vt_memTwo h.2.1 h.2.2.2 c1.1 hlt2
    refine ⟨⟨d1, by
      show ((Par τ (vt τ (Om1 * q + ev τ r)) : Set Ordinal.{0})) ⊆ Set.Iio σ; rw [d2]; exact c1.2⟩, ?_, ⟨a3, ?_⟩,
      fun _ => trivial, fun _ => trivial, fun _ _ _ => trivial⟩
    · simp only [ev, map]; rw [pi_vt_two h c1 hlt2, c2, g2, a2]
    · rw [← a2]; exact down_lt_Om1 h a1 hw.2
  | _, .thg m G r, hw, hl, hq => by
    obtain ⟨a1, a2, a3, -⟩ := urDownB h hκσ r hw.2.1 hl.2 hq.2
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := urDownB h hκσ G hw.1 hl.1 hq.1
    obtain ⟨c1, c2⟩ := pi_add h g1 a1
    have hlt2 := Uk.arg_lt2 (ev_lt_Er G hw.1) hw.2.2.r1
    obtain ⟨d1, -, -, -, d2⟩ := vt_memTwo h.2.1 h.2.2.2 c1.1 hlt2
    have hVT : vt τ (ev τ G + ev τ r) ∈ TB τ σ := ⟨d1, by
      show ((Par τ (vt τ (ev τ G + ev τ r)) : Set Ordinal.{0})) ⊆ Set.Iio σ; rw [d2]; exact c1.2⟩
    have hpv : pi σ τ (vt τ (ev τ G + ev τ r)) = vt σ (ev σ (G.map (pi σ τ)) + ev σ (r.map (pi σ τ))) := by
      rw [pi_vt_two h c1 hlt2, c2, g2, a2]
    refine ⟨hVT, by simp only [ev, map]; exact hpv, ⟨g3, a3, ?_⟩, fun _ => trivial, fun _ => trivial,
      fun _ _ _ => trivial⟩
    refine ⟨by rw [← a2]; exact down_lt_Om1 h a1 hw.2.2.r1, (Gs_map _ G).2 hw.2.2.gs,
      NfM_imp g4 g5 m hw.2.2.nf,
      HdD_map m G (Lv_mono (fun p hp => ⟨fun hτp => down_ge h hp hτp, fun hpτ => by
        have hpσ := (TB_inter_lt h hpτ).1 hp
        rw [pi_lt h hpσ]; exact hpσ⟩) G hl.1) hw.2.2.hd,
      by rw [← g2, ← a2, ← c2]; exact (pi_bijOn h).1.mapsTo c1, ?_, ?_⟩
    · rw [← hpv]; exact g6 _ hVT hw.2.2.bd
    · rw [← hpv, ← a2]; exact (pi_bijOn h).2 a1 hVT hw.2.2.rb
  | _, .lf c, hw, hl, hq => by
    obtain ⟨a1, a2, a3, -⟩ := urDownB h hκσ c hw.1 hl hq
    refine ⟨a1, a2, ⟨a3, by rw [← a2]; exact down_lt_Om1 h a1 hw.2⟩, fun _ => trivial, fun _ => trivial,
      fun V hV hc => ?_⟩
    show ev σ (c.map (pi σ τ)) < pi σ τ V
    rw [← a2]; exact (pi_bijOn h).2 a1 hV hc
  | _, .om b, hw, hl, hq => by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := urDownB h hκσ b hw hl hq
    have hbE := ev_lt_Er b hw
    obtain ⟨o1, o2⟩ := siOm1_opow_TB h hbE
    refine ⟨o1.2 a1, ?_, a3, a4, a5, a6⟩
    simp only [ev, map]; rw [o2 a1, a2]
  | _, .ad x y, hw, hl, hq => by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := urDownB h hκσ x hw.1 hl.1 hq.1
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := urDownB h hκσ y hw.2 hl.2 hq.2
    obtain ⟨c1, c2⟩ := pi_add h a1 b1
    have hω : ev τ y < ev τ x * ω → ev σ (y.map (pi σ τ)) < ev σ (x.map (pi σ τ)) * ω := by
      intro hlt; rw [← a2, ← b2]; exact (unPi_lt_mul_omega_iff h a1 b1).1 hlt
    refine ⟨c1, ?_, ⟨a3, b3⟩, fun hb => ⟨a4 hb.1, (IsOm_map _ x).2 hb.2.1, hω hb.2.2⟩,
      fun hb => ⟨a5 hb.1, b5 hb.2.1, (IsOm_map _ x).2 hb.2.2.1, hω hb.2.2.2⟩,
      fun V hV hc => ⟨a6 V hV hc.1, b6 V hV hc.2⟩⟩
    simp only [ev, map]; rw [c2, a2, b2]

/-- **The base change on terms**: `π_{σ,τ}(t[τ; p]) = t[σ; π p]`, the image has the argument bounds and the node
conditions over `σ`. -/
theorem urDown {κ σ τ : Ordinal.{0}} (h : Bases σ τ) (hκσ : κ ≤ σ) (t : UnT false) (hw : WFr τ t)
    (hl : Lv (· ∈ TB τ σ) t) (hq : Qs κ t) :
    ev τ t ∈ TB τ σ ∧ pi σ τ (ev τ t) = ev σ (t.map (pi σ τ)) ∧ WFr σ (t.map (pi σ τ)) := by
  obtain ⟨a1, a2, a3, -⟩ := urDownB h hκσ t hw hl hq
  exact ⟨a1, a2, a3⟩

/-- **The inverse base change on terms of both sorts.** -/
theorem urUpB {κ σ τ : Ordinal.{0}} (h : Bases σ τ) (hκσ : κ ≤ σ) :
    ∀ {k : Bool} (t : UnT k), WFr σ t → Lv (· ∈ Tset σ) t → Qs κ t →
      ev τ (t.map (up σ τ)) ∈ TB τ σ ∧ pi σ τ (ev τ (t.map (up σ τ))) = ev σ t ∧ WFr τ (t.map (up σ τ)) ∧
      (HbS σ t → HbS τ (t.map (up σ τ))) ∧ (FNF σ t → FNF τ (t.map (up σ τ))) ∧
      (∀ V ∈ TB τ σ, Lf (fun c => ev σ c < pi σ τ V) t → Lf (fun c => ev τ c < V) (t.map (up σ τ)))
  | _, .par p, _, hp, _ =>
    ⟨(up_spec h hp).1, (up_spec h hp).2, trivial, fun _ => trivial, fun _ => trivial, fun _ _ _ => trivial⟩
  | _, .add s t, hw, hl, hq => by
    obtain ⟨a1, a2, a3, -⟩ := urUpB h hκσ s hw.1 hl.1 hq.1
    obtain ⟨b1, b2, b3, -⟩ := urUpB h hκσ t hw.2 hl.2 hq.2
    obtain ⟨c1, c2⟩ := pi_add h a1 b1
    refine ⟨c1, ?_, ⟨a3, b3⟩, fun _ => trivial, fun _ => trivial, fun _ _ _ => trivial⟩
    simp only [ev, map] at c2 ⊢; rw [c2, a2, b2]
  | _, .base, _, _, _ =>
    ⟨(pi_base h).1, (pi_base h).2, trivial, fun _ => trivial, fun _ => trivial, fun _ _ _ => trivial⟩
  | _, .th1 s, hw, hl, hq => by
    obtain ⟨a1, a2, a3, -⟩ := urUpB h hκσ s hw.1 hl hq
    have hσ1 : (1 : Ordinal.{0}) < σ := Ub.ub_one_lt h.1
    have h1T : (1 : Ordinal.{0}) ∈ TB τ σ := (TB_inter_lt h (hσ1.trans h.2.2.1)).2 hσ1
    have hO : (1 : Ordinal.{0}) < Om1 := hσ1.trans (h.2.2.1.trans h.2.2.2)
    have hy1 := unUp_lt_Om1 h a1 a2 hw.2
    obtain ⟨c1, c2⟩ := pi_add h h1T a1
    have hlt1 : 1 + ev τ (s.map (up σ τ)) < Om1 := Om1_add_lt hO hy1
    obtain ⟨d1, d2⟩ := vt_mem h.2.1 h.2.2.2 c1.1 hlt1
    refine ⟨⟨d1, by simp only [ev, map]; rw [d2]; exact c1.2⟩, ?_, ⟨a3, hy1⟩, fun _ => trivial,
      fun _ => trivial, fun _ _ _ => trivial⟩
    simp only [ev, map]; rw [pi_vt h c1 hlt1, c2, pi_lt h hσ1, a2]
  | _, .thc q r, hw, hl, hq => by
    obtain ⟨a1, a2, a3, -⟩ := urUpB h hκσ r hw.1 hl hq.2
    have hy1 := unUp_lt_Om1 h a1 a2 hw.2
    obtain ⟨g1, g2⟩ := uh_Om1_mul_TB h q hq.1.2.1 (hq.1.2.2.trans_le hκσ)
    obtain ⟨c1, c2⟩ := pi_add h g1 a1
    have hlt2 : Om1 * q + ev τ (r.map (up σ τ)) < OmTwo := Rj.rj_arg_lt hq.1.2.1 hy1
    obtain ⟨d1, -, -, -, d2⟩ := vt_memTwo h.2.1 h.2.2.2 c1.1 hlt2
    refine ⟨⟨d1, by simp only [ev, map]; rw [d2]; exact c1.2⟩, ?_, ⟨a3, hy1⟩, fun _ => trivial,
      fun _ => trivial, fun _ _ _ => trivial⟩
    simp only [ev, map]; rw [pi_vt_two h c1 hlt2, c2, g2, a2]
  | _, .thg m G r, hw, hl, hq => by
    obtain ⟨a1, a2, a3, -⟩ := urUpB h hκσ r hw.2.1 hl.2 hq.2
    have hy1 := unUp_lt_Om1 h a1 a2 hw.2.2.r1
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := urUpB h hκσ G hw.1 hl.1 hq.1
    obtain ⟨c1, c2⟩ := pi_add h g1 a1
    have hlt2 := Uk.arg_lt2 (ev_lt_Er _ g3) hy1
    obtain ⟨d1, -, -, -, d2⟩ := vt_memTwo h.2.1 h.2.2.2 c1.1 hlt2
    have hVT : vt τ (ev τ (G.map (up σ τ)) + ev τ (r.map (up σ τ))) ∈ TB τ σ := ⟨d1, by
      show ((Par τ (vt τ (ev τ (G.map (up σ τ)) + ev τ (r.map (up σ τ)))) : Set Ordinal.{0})) ⊆ Set.Iio σ
      rw [d2]; exact c1.2⟩
    have hpv : pi σ τ (vt τ (ev τ (G.map (up σ τ)) + ev τ (r.map (up σ τ)))) = vt σ (ev σ G + ev σ r) := by
      rw [pi_vt_two h c1 hlt2, c2, g2, a2]
    refine ⟨hVT, by simp only [ev, map]; exact hpv, ⟨g3, a3, ?_⟩, fun _ => trivial, fun _ => trivial,
      fun _ _ _ => trivial⟩
    refine ⟨hy1, (Gs_map _ G).2 hw.2.2.gs, NfM_imp g4 g5 m hw.2.2.nf,
      HdD_map m G (Lv_mono (fun p hp => ⟨fun hσp => up_ge h hp hσp, fun hpσ => by
        rw [up_lt h hpσ]; exact hpσ.trans h.2.2.1⟩) G hl.1) hw.2.2.hd, c1.1, ?_, ?_⟩
    · have hb := hw.2.2.bd
      rw [← hpv] at hb
      exact g6 _ hVT hb
    · have hb := hw.2.2.rb
      rw [← hpv, ← a2] at hb
      by_contra hge
      have := ((pi_bijOn h).2.le_iff_le hVT a1).2 (not_lt.1 hge)
      exact absurd hb (not_lt.2 this)
  | _, .lf c, hw, hl, hq => by
    obtain ⟨a1, a2, a3, -⟩ := urUpB h hκσ c hw.1 hl hq
    refine ⟨a1, a2, ⟨a3, unUp_lt_Om1 h a1 a2 hw.2⟩, fun _ => trivial, fun _ => trivial, fun V hV hc => ?_⟩
    show ev τ (c.map (up σ τ)) < V
    have hc' : ev σ c < pi σ τ V := hc
    rw [← a2] at hc'
    by_contra hge
    have := ((pi_bijOn h).2.le_iff_le hV a1).2 (not_lt.1 hge)
    exact absurd hc' (not_lt.2 this)
  | _, .om b, hw, hl, hq => by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := urUpB h hκσ b hw hl hq
    have hbE := ev_lt_Er _ a3
    obtain ⟨o1, o2⟩ := siOm1_opow_TB h hbE
    refine ⟨o1.2 a1, ?_, a3, a4, a5, a6⟩
    simp only [ev, map] at o2 ⊢; rw [o2 a1, a2]
  | _, .ad x y, hw, hl, hq => by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := urUpB h hκσ x hw.1 hl.1 hq.1
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := urUpB h hκσ y hw.2 hl.2 hq.2
    obtain ⟨c1, c2⟩ := pi_add h a1 b1
    have hω : ev σ y < ev σ x * ω → ev τ (y.map (up σ τ)) < ev τ (x.map (up σ τ)) * ω := by
      intro hlt; rw [← a2, ← b2] at hlt; exact (unPi_lt_mul_omega_iff h a1 b1).2 hlt
    refine ⟨c1, ?_, ⟨a3, b3⟩, fun hb => ⟨a4 hb.1, (IsOm_map _ x).2 hb.2.1, hω hb.2.2⟩,
      fun hb => ⟨a5 hb.1, b5 hb.2.1, (IsOm_map _ x).2 hb.2.2.1, hω hb.2.2.2⟩,
      fun V hV hc => ⟨a6 V hV hc.1, b6 V hV hc.2⟩⟩
    simp only [ev, map] at c2 ⊢; rw [c2, a2, b2]

/-- **The inverse base change on terms.** -/
theorem urUp {κ σ τ : Ordinal.{0}} (h : Bases σ τ) (hκσ : κ ≤ σ) (t : UnT false) (hw : WFr σ t)
    (hl : Lv (· ∈ Tset σ) t) (hq : Qs κ t) :
    ev τ (t.map (up σ τ)) ∈ TB τ σ ∧ pi σ τ (ev τ (t.map (up σ τ))) = ev σ t ∧ WFr τ (t.map (up σ τ)) := by
  obtain ⟨a1, a2, a3, -⟩ := urUpB h hκσ t hw hl hq
  exact ⟨a1, a2, a3⟩

/-- `π_{σ,τ}⁻¹(t[σ; p]) = t[τ; π⁻¹ p]`. -/
theorem urUp_eq {κ σ τ : Ordinal.{0}} (h : Bases σ τ) (hκσ : κ ≤ σ) (t : UnT false) (hw : WFr σ t)
    (hl : Lv (· ∈ Tset σ) t) (hq : Qs κ t) :
    up σ τ (ev σ t) = ev τ (t.map (up σ τ)) ∧ WFr τ (t.map (up σ τ)) := by
  obtain ⟨a1, a2, a3⟩ := urUp h hκσ t hw hl hq
  exact ⟨by rw [← a2]; exact up_pi h a1, a3⟩

/-- **The segment move on terms**: `mv b c (t[b; p]) = t[c; mv b c p]`. -/
theorem urMv {κ b c : Ordinal.{0}} (hb : InE b) (hb1 : b < Om1) (hc : InE c) (hc1 : c < Om1) (hκb : κ ≤ b)
    (hκc : κ ≤ c) (t : UnT false) (hq : Qs κ t) (hw : WFr b t) (hl : Lv (· ∈ TB b κ) t) :
    mv b c (ev b t) = ev c (t.map (mv b c)) ∧ WFr c (t.map (mv b c)) := by
  rcases lt_trichotomy c b with hcb | rfl | hbc
  · have hmv : mv b c = pi c b := by unfold mv; rw [if_pos hcb]
    have hB : Bases c b := ⟨hc, hb, hcb, hb1⟩
    obtain ⟨-, a2, a3⟩ := urDown hB hκc t hw (Lv_mono (fun p hp => Ub.ub_TB_mono hκc hp) t hl) hq
    rw [hmv]; exact ⟨a2, a3⟩
  · have hmv : mv c c = id := by unfold mv; simp
    rw [hmv, map_id]; exact ⟨rfl, hw⟩
  · have hmv : mv b c = up b c := by unfold mv; rw [if_neg (not_lt.2 hbc.le), if_pos hbc]
    have hB : Bases b c := ⟨hb, hc, hbc, hc1⟩
    rw [hmv]
    exact urUp_eq hB hκb t hw (Lv_mono (fun p hp => hp.1) t hl) hq

/-! ## The translations of [W07a] Def 6.2 -/


/-- **`t^α_τ` on terms of both sorts** ([W07a] Def 6.2, Lemma 6.3 through `R2.vt_wbar`, `R2.urVt_tr_uh` (i) and
`R2.ukVt_tr3` (i), whose condition `α ≤ rjDat Γ` is `urDatM` at `α`). -/
theorem urTrAB {κ τ : Ordinal.{0}} (hB : Bases κ τ) {n : ℕ} (hn : 1 ≤ n) :
    ∀ {k : Bool} (t : UnT k), Qs κ t → Lv (· ∈ Tset (Dl τ n)) t → WFr (Dl τ n) t → Nd (Dl τ n) (· < Dp τ n) t →
      WFr τ (trr (Dl τ n) t) ∧ ev τ (trr (Dl τ n) t) = ev (Dl τ n) t ∧
      (HbS (Dl τ n) t → HbS τ (trr (Dl τ n) t)) ∧ (FNF (Dl τ n) t → FNF τ (trr (Dl τ n) t)) ∧
      (∀ V, Lf (fun c => ev τ c < V) (trr (Dl τ n) t) ↔ Lf (fun c => ev (Dl τ n) c < V) t)
  | _, .par _, _, _, _, _ => ⟨trivial, rfl, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
  | _, .add s t, hq, hl, hw, hd => by
    obtain ⟨a1, a2, -⟩ := urTrAB hB hn s hq.1 hl.1 hw.1 hd.1
    obtain ⟨b1, b2, -⟩ := urTrAB hB hn t hq.2 hl.2 hw.2 hd.2
    refine ⟨⟨a1, b1⟩, ?_, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
    simp only [trr, ev]; rw [a2, b2]
  | _, .base, _, _, _, _ => ⟨trivial, rfl, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
  | _, .th1 s, hq, hl, hw, hd => by
    obtain ⟨a1, a2, -⟩ := urTrAB hB hn s hq hl hw.1 hd
    obtain ⟨hτα, hαE, -⟩ := Dl_E hB.2.1 hB.2.2.2 hn
    have hα1 : Dl τ n < Om1 := (Dl_spec hB.2.1 hB.2.2.2 n).2.1
    have hab : τ + Dl τ n = Dl τ n :=
      add_of_omega0_opow_le (show τ < ω ^ Dl τ n by rw [hαE]; exact hτα) (le_of_eq hαE)
    have hlt : Dl τ n + ev (Dl τ n) s < Om1 := Om1_add_lt hα1 hw.2
    refine ⟨⟨⟨trivial, a1⟩, ?_⟩, ?_, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
    · simp only [ev]; rw [a2]; exact hlt
    · simp only [trr, ev]
      rw [a2, vt_wbar hB.2.1 hB.2.2.2 hlt, vt_wbar hαE hα1 hw.2, ← add_assoc, hab]
  | _, .thc q r, hq, hl, hw, hd => by
    obtain ⟨a1, a2, -⟩ := urTrAB hB hn r hq.2 hl hw.1 hd.2
    obtain ⟨hτα, hαE, -⟩ := Dl_E hB.2.1 hB.2.2.2 hn
    have hα1 : Dl τ n < Om1 := (Dl_spec hB.2.1 hB.2.2.2 n).2.1
    have hBα : Bases κ (Dl τ n) := ⟨hB.1, hαE, hB.2.2.1.trans hτα, hα1⟩
    have hlt : Dl τ n + ev (Dl τ n) r < Om1 := Om1_add_lt hα1 hw.2
    have hrT := urMem hBα r hl hw.1 hq.2
    have hargT := (uh_arg_T hBα hq.1 hrT hw.2).1
    have e := (urVt_tr_uh hB.2.1 hB.2.2.2 hn hq.1.1 hq.1.2.1 (hq.1.2.2.trans hB.2.2.1) hw.2).1 hargT hd.1
    refine ⟨⟨⟨trivial, a1⟩, ?_⟩, ?_, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
    · simp only [ev]; rw [a2]; exact hlt
    · simp only [trr, ev]; rw [a2, e]
  | _, .thg m G r, hq, hl, hw, hd => by
    obtain ⟨a1, a2, -⟩ := urTrAB hB hn r hq.2 hl.2 hw.2.1 hd.2.2
    obtain ⟨l1, l2, l4, l5, l6⟩ := urTrAB hB hn G hq.1 hl.1 hw.1 hd.2.1
    obtain ⟨hτα, hαE, -⟩ := Dl_E hB.2.1 hB.2.2.2 hn
    have hα1 : Dl τ n < Om1 := (Dl_spec hB.2.1 hB.2.2.2 n).2.1
    have hBα : Bases κ (Dl τ n) := ⟨hB.1, hαE, hB.2.2.1.trans hτα, hα1⟩
    obtain ⟨M, hM, hM1⟩ := UnT.ev_dvd (τ := Dl τ n) G hw.2.2.gs
    have hME : Om1 * M < Gg.ggE := hM ▸ ev_lt_Er G hw.1
    have hmem := hw.2.2.mem
    have hlt : vt (Dl τ n) (ev (Dl τ n) G + ev (Dl τ n) r) < Dp τ n := hd.1
    rw [hM] at hmem hlt
    by_cases hLo : LoL (Dl τ n) G
    · -- a low level over `α`: the subcase `Γ^* < α`, `α` is inserted (`R2.urVt_tr2` (i))
      have hm : m = true := HdD_lo hw.2.2.hd hLo
      subst hm
      have hdat : Rj.rjDat (Om1 * M) < Dl τ n := by
        rw [← hM]; exact urDatLo (InE.pos hαE) G hw.1 hw.2.2.nf hLo
      obtain ⟨m1, e1⟩ := (urVt_tr2 hB.2.1 hB.2.2.2 hn hM1 hME hdat hw.2.2.r1).1 hmem hlt
      rw [trr_thg_lo hLo]
      have hev : ev τ (trr (Dl τ n) G) + ev τ (UnT.add (.par (Dl τ n)) (trr (Dl τ n) r)) =
          Om1 * M + (Dl τ n + ev (Dl τ n) r) := by
        simp only [ev]; rw [l2, a2, hM]
      have hρα : Dl τ n + ev (Dl τ n) r < Om1 := Om1_add_lt hα1 hw.2.2.r1
      have h1M : Om1 ≤ Om1 * M := by
        have := mul_le_mul_right hM1 Om1
        rwa [mul_one] at this
      have hlt2 : Om1 * M + ev (Dl τ n) r < OmTwo := Uk.arg_lt2 hME hw.2.2.r1
      obtain ⟨hαV, hVE⟩ := (vt_E_iff hαE hα1 hmem hlt2).2 (h1M.trans le_self_add)
      have hrb0 : ev (Dl τ n) r < vt (Dl τ n) (Om1 * M + ev (Dl τ n) r) := by
        have := hw.2.2.rb; rw [hM] at this; exact this
      have hrb : Dl τ n + ev (Dl τ n) r < vt (Dl τ n) (Om1 * M + ev (Dl τ n) r) := hVE.add_lt hαV hrb0
      refine ⟨⟨l1, ⟨trivial, a1⟩, ⟨?_, (Gs_trr _ G).2 hw.2.2.gs, l5 hw.2.2.nf, ?_, by rw [hev]; exact m1, ?_,
        ?_⟩⟩, ?_, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
      · show Dl τ n + ev τ (trr (Dl τ n) r) < Om1
        rw [a2]; exact hρα
      · rw [trr_LoL G hLo]
        rcases LoL_split (τ := τ) G hLo with h' | h'
        · exact Or.inl h'
        · exact Or.inr ⟨rfl, h'⟩
      · rw [hev, ← e1, l6, ← hM]; exact hw.2.2.bd
      · rw [hev, ← e1]
        show Dl τ n + ev τ (trr (Dl τ n) r) < _
        rw [a2]; exact hrb
      · simp only [ev]; rw [l2, a2, hM]; exact e1.symm
    · -- a high level over `α`: the subcase `Γ^* ≥ α` (`R2.ukVt_tr3` (i))
      have hHd : HdM m (Dl τ n) G := HdD_hi hw.2.2.hd hLo
      have hdat := (urDatM hBα m G hl.1 hw.1 hq.1 hw.2.2.nf hHd).1
      rw [hM] at hdat
      obtain ⟨m1, e1⟩ := (ukVt_tr3 hB.2.1 hB.2.2.2 hn hM1 hME hdat hw.2.2.r1).1 hmem hlt
      rw [trr_thg_hi hLo]
      have hev : ev τ (trr (Dl τ n) G) + ev τ (trr (Dl τ n) r) = Om1 * M + ev (Dl τ n) r := by
        rw [l2, a2, hM]
      refine ⟨⟨l1, a1, ⟨by rw [a2]; exact hw.2.2.r1, (Gs_trr _ G).2 hw.2.2.gs, NfM_imp l4 l5 m hw.2.2.nf,
        Or.inl (HdM_trr hτα.le m G hHd), by rw [hev]; exact m1, ?_, ?_⟩⟩, ?_, fun _ => trivial, fun _ => trivial,
        fun _ => Iff.rfl⟩
      · rw [hev, ← e1, l6, ← hM]; exact hw.2.2.bd
      · rw [hev, ← e1, a2, ← hM]; exact hw.2.2.rb
      · simp only [ev]; rw [hev, ← e1, hM]
  | _, .lf c, hq, hl, hw, hd => by
    obtain ⟨a1, a2, -⟩ := urTrAB hB hn c hq hl hw.1 hd
    refine ⟨⟨a1, by rw [a2]; exact hw.2⟩, a2, fun _ => trivial, fun _ => trivial, fun V => ?_⟩
    show ev τ (trr (Dl τ n) c) < V ↔ ev (Dl τ n) c < V
    rw [a2]
  | _, .om b, hq, hl, hw, hd => by
    obtain ⟨a1, a2, a4, a5, a6⟩ := urTrAB hB hn b hq hl hw hd
    refine ⟨a1, ?_, a4, a5, a6⟩
    simp only [trr, ev]; rw [a2]
  | _, .ad x y, hq, hl, hw, hd => by
    obtain ⟨a1, a2, a4, a5, a6⟩ := urTrAB hB hn x hq.1 hl.1 hw.1 hd.1
    obtain ⟨b1, b2, b4, b5, b6⟩ := urTrAB hB hn y hq.2 hl.2 hw.2 hd.2
    refine ⟨⟨a1, b1⟩, ?_, fun hb => ⟨a4 hb.1, (IsOm_trr _ x).2 hb.2.1, by rw [a2, b2]; exact hb.2.2⟩,
      fun hb => ⟨a5 hb.1, b5 hb.2.1, (IsOm_trr _ x).2 hb.2.2.1, by rw [a2, b2]; exact hb.2.2.2⟩,
      fun V => and_congr (a6 V) (b6 V)⟩
    simp only [trr, ev]; rw [a2, b2]

/-- **`t^α_τ` is correct** (`α = Dl τ n`, `n ≥ 1`): `trr α t` has the argument bounds and node conditions over `τ`
and `(trr α t)[τ] = t[α]`. -/
theorem urTrA {κ τ : Ordinal.{0}} (hB : Bases κ τ) {n : ℕ} (hn : 1 ≤ n) (t : UnT false) (hq : Qs κ t)
    (hl : Lv (· ∈ Tset (Dl τ n)) t) (hw : WFr (Dl τ n) t) (hd : Nd (Dl τ n) (· < Dp τ n) t) :
    WFr τ (trr (Dl τ n) t) ∧ ev τ (trr (Dl τ n) t) = ev (Dl τ n) t := by
  obtain ⟨a1, a2, -⟩ := urTrAB hB hn t hq hl hw hd
  exact ⟨a1, a2⟩

/-- **`t^τ_α` on terms of both sorts** ([W07a] Def 6.2, Lemma 6.3 through `R2.vt_wbar`, `R2.urVt_tr_uh` (ii) and
`R2.ukVt_tr3` (ii)); the syntactic mode conditions over `α` (`HdDA α t`) and the parameters in `T^α` give the
decision `Γ^{*α} ≥ α`. -/
theorem urTrBB {κ τ : Ordinal.{0}} (hB : Bases κ τ) {n : ℕ} (hn : 1 ≤ n) :
    ∀ {k : Bool} (t : UnT k), Qs κ t → Lv (· ∈ Tset τ) (trr (Dl τ n) t) → WFr τ (trr (Dl τ n) t) →
      Nd τ (· < Dp τ n) (trr (Dl τ n) t) → HdDA (Dl τ n) t → Lv (· ∈ Tset (Dl τ n)) t →
      WFr (Dl τ n) t ∧ ev τ (trr (Dl τ n) t) = ev (Dl τ n) t ∧
      (HbS τ (trr (Dl τ n) t) → HbS (Dl τ n) t) ∧ (FNF τ (trr (Dl τ n) t) → FNF (Dl τ n) t) ∧
      (∀ V, Lf (fun c => ev τ c < V) (trr (Dl τ n) t) ↔ Lf (fun c => ev (Dl τ n) c < V) t)
  | _, .par _, _, _, _, _, _, _ => ⟨trivial, rfl, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
  | _, .add s t, hq, hl, hw, hd, hh, hla => by
    obtain ⟨a1, a2, -⟩ := urTrBB hB hn s hq.1 hl.1 hw.1 hd.1 hh.1 hla.1
    obtain ⟨b1, b2, -⟩ := urTrBB hB hn t hq.2 hl.2 hw.2 hd.2 hh.2 hla.2
    refine ⟨⟨a1, b1⟩, ?_, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
    simp only [trr, ev]; rw [a2, b2]
  | _, .base, _, _, _, _, _, _ => ⟨trivial, rfl, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
  | _, .th1 s, hq, hl, hw, hd, hh, hla => by
    obtain ⟨a1, a2, -⟩ := urTrBB hB hn s hq hl.2 hw.1.2 hd.2 hh hla
    obtain ⟨hτα, hαE, -⟩ := Dl_E hB.2.1 hB.2.2.2 hn
    have hα1 : Dl τ n < Om1 := (Dl_spec hB.2.1 hB.2.2.2 n).2.1
    have hab : τ + Dl τ n = Dl τ n :=
      add_of_omega0_opow_le (show τ < ω ^ Dl τ n by rw [hαE]; exact hτα) (le_of_eq hαE)
    have h2 := hw.2
    simp only [ev] at h2; rw [a2] at h2
    have hs1 : ev (Dl τ n) s < Om1 := lt_of_le_of_lt le_add_self h2
    refine ⟨⟨a1, hs1⟩, ?_, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
    simp only [trr, ev]
    rw [a2, vt_wbar hB.2.1 hB.2.2.2 h2, vt_wbar hαE hα1 hs1, ← add_assoc, hab]
  | _, .thc q r, hq, hl, hw, hd, hh, hla => by
    obtain ⟨a1, a2, -⟩ := urTrBB hB hn r hq.2 hl.2 hw.1.2 hd.2.2 hh hla
    have h2 := hw.2
    simp only [ev] at h2
    have hr1 : ev (Dl τ n) r < Om1 := by rw [← a2]; exact lt_of_le_of_lt le_add_self h2
    have hαT : Dl τ n ∈ Tset τ := (Dl_spec hB.2.1 hB.2.2.2 n).1
    have hrT : ev τ (trr (Dl τ n) r) ∈ Tset τ := urMem hB _ hl.2 hw.1.2 (Qs_trr _ r hq.2)
    have hsT : Dl τ n + ev τ (trr (Dl τ n) r) ∈ Tset τ := vzT_add hB.2.1 hB.2.2.2 hαT hrT
    have hargT := (uh_arg_T hB hq.1 hsT h2).1
    have hd1 := hd.1
    simp only [ev] at hd1
    rw [a2] at hargT hd1
    have e := (urVt_tr_uh hB.2.1 hB.2.2.2 hn hq.1.1 hq.1.2.1 (hq.1.2.2.trans hB.2.2.1) hr1).2 hargT hd1
    refine ⟨⟨a1, hr1⟩, ?_, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
    simp only [trr, ev]; rw [a2, e]
  | _, .thg m G r, hq, hl, hw, hd, hh, hla => by
    obtain ⟨hτα, hαE, -⟩ := Dl_E hB.2.1 hB.2.2.2 hn
    have hα1 : Dl τ n < Om1 := (Dl_spec hB.2.1 hB.2.2.2 n).2.1
    have hBα : Bases κ (Dl τ n) := ⟨hB.1, hαE, hB.2.2.1.trans hτα, hα1⟩
    by_cases hLo : LoL (Dl τ n) G
    · -- a low level over `α`: `R2.urVt_tr2` (ii)
      have hm : m = true := HdD_lo hh.1 hLo
      subst hm
      rw [trr_thg_lo hLo] at hl hw hd ⊢
      obtain ⟨a1, a2, -⟩ := urTrBB hB hn r hq.2 hl.2.2 hw.2.1.2 hd.2.2.2 hh.2.2 hla.2
      obtain ⟨l1, l2, -, l5, l6⟩ := urTrBB hB hn G hq.1 hl.1 hw.1 hd.2.1 hh.2.1 hla.1
      have hgs : Gs G := (Gs_trr _ G).1 hw.2.2.gs
      have hnf : FNF (Dl τ n) G := l5 hw.2.2.nf
      obtain ⟨M, hM, hM1⟩ := UnT.ev_dvd (τ := Dl τ n) G hgs
      have hME : Om1 * M < Gg.ggE := hM ▸ ev_lt_Er G l1
      have hdat : Rj.rjDat (Om1 * M) < Dl τ n := by
        rw [← hM]; exact urDatLo (InE.pos hαE) G l1 hnf hLo
      have hr1' : Dl τ n + ev (Dl τ n) r < Om1 := by
        have := hw.2.2.r1
        simp only [ev] at this; rwa [a2] at this
      have hr1 : ev (Dl τ n) r < Om1 := lt_of_le_of_lt le_add_self hr1'
      have hev : ev τ (trr (Dl τ n) G) + ev τ (UnT.add (.par (Dl τ n)) (trr (Dl τ n) r)) =
          Om1 * M + (Dl τ n + ev (Dl τ n) r) := by
        simp only [ev]; rw [l2, a2, hM]
      have hmem := hw.2.2.mem
      have hlt : vt τ (ev τ (trr (Dl τ n) G) + ev τ (UnT.add (.par (Dl τ n)) (trr (Dl τ n) r))) < Dp τ n := hd.1
      rw [hev] at hmem hlt
      obtain ⟨m1, e1⟩ := (urVt_tr2 hB.2.1 hB.2.2.2 hn hM1 hME hdat hr1).2 hmem hlt
      refine ⟨⟨l1, a1, ⟨hr1, hgs, hnf, hh.1, by rw [hM]; exact m1, ?_, ?_⟩⟩, ?_, fun _ => trivial,
        fun _ => trivial, fun _ => Iff.rfl⟩
      · rw [hM, ← e1, ← hev, ← l6]; exact hw.2.2.bd
      · rw [hM, ← e1, ← hev]
        refine lt_of_le_of_lt ?_ hw.2.2.rb
        show ev (Dl τ n) r ≤ Dl τ n + ev τ (trr (Dl τ n) r)
        rw [a2]; exact le_add_self
      · simp only [ev]; rw [l2, a2, hM]; exact e1
    · -- a high level over `α`: `R2.ukVt_tr3` (ii)
      have hHd : HdM m (Dl τ n) G := HdD_hi hh.1 hLo
      rw [trr_thg_hi hLo] at hl hw hd ⊢
      obtain ⟨a1, a2, -⟩ := urTrBB hB hn r hq.2 hl.2 hw.2.1 hd.2.2 hh.2.2 hla.2
      obtain ⟨l1, l2, l4, l5, l6⟩ := urTrBB hB hn G hq.1 hl.1 hw.1 hd.2.1 hh.2.1 hla.1
      have hgs : Gs G := (Gs_trr _ G).1 hw.2.2.gs
      have hnf : NfM m (Dl τ n) G := NfM_imp l4 l5 m hw.2.2.nf
      obtain ⟨M, hM, hM1⟩ := UnT.ev_dvd (τ := Dl τ n) G hgs
      have hdat := (urDatM hBα m G hla.1 l1 hq.1 hnf hHd).1
      have hME : Om1 * M < Gg.ggE := hM ▸ ev_lt_Er G l1
      have hr1 : ev (Dl τ n) r < Om1 := by rw [← a2]; exact hw.2.2.r1
      have hev : ev τ (trr (Dl τ n) G) + ev τ (trr (Dl τ n) r) = Om1 * M + ev (Dl τ n) r := by
        rw [l2, a2, hM]
      have hmem := hw.2.2.mem
      have hlt : vt τ (ev τ (trr (Dl τ n) G) + ev τ (trr (Dl τ n) r)) < Dp τ n := hd.1
      rw [hev] at hmem hlt
      rw [hM] at hdat
      obtain ⟨m1, e1⟩ := (ukVt_tr3 hB.2.1 hB.2.2.2 hn hM1 hME hdat hr1).2 hmem hlt
      refine ⟨⟨l1, a1, ⟨hr1, hgs, hnf, hh.1, by rw [hM]; exact m1, ?_, ?_⟩⟩, ?_, fun _ => trivial,
        fun _ => trivial, fun _ => Iff.rfl⟩
      · rw [hM, ← e1, ← hev, ← l6]; exact hw.2.2.bd
      · rw [hM, ← e1, ← hev, ← a2]; exact hw.2.2.rb
      · simp only [ev]; rw [hev, e1, hM]
  | _, .lf c, hq, hl, hw, hd, hh, hla => by
    obtain ⟨a1, a2, -⟩ := urTrBB hB hn c hq hl hw.1 hd hh hla
    have h2 : ev τ (trr (Dl τ n) c) < Om1 := hw.2
    refine ⟨⟨a1, a2 ▸ h2⟩, a2, fun _ => trivial, fun _ => trivial, fun V => ?_⟩
    show ev τ (trr (Dl τ n) c) < V ↔ ev (Dl τ n) c < V
    rw [a2]
  | _, .om b, hq, hl, hw, hd, hh, hla => by
    obtain ⟨a1, a2, a4, a5, a6⟩ := urTrBB hB hn b hq hl hw hd hh hla
    refine ⟨a1, ?_, a4, a5, a6⟩
    simp only [trr, ev]; rw [a2]
  | _, .ad x y, hq, hl, hw, hd, hh, hla => by
    obtain ⟨a1, a2, a4, a5, a6⟩ := urTrBB hB hn x hq.1 hl.1 hw.1 hd.1 hh.1 hla.1
    obtain ⟨b1, b2, b4, b5, b6⟩ := urTrBB hB hn y hq.2 hl.2 hw.2 hd.2 hh.2 hla.2
    refine ⟨⟨a1, b1⟩, ?_, fun hb => ⟨a4 hb.1, (IsOm_trr _ x).1 hb.2.1, by rw [← a2, ← b2]; exact hb.2.2⟩,
      fun hb => ⟨a5 hb.1, b5 hb.2.1, (IsOm_trr _ x).1 hb.2.2.1, by rw [← a2, ← b2]; exact hb.2.2.2⟩,
      fun V => and_congr (a6 V) (b6 V)⟩
    simp only [trr, ev]; rw [a2, b2]

/-- **`t^τ_α` is correct** (`α = Dl τ n`, `n ≥ 1`): if `trr α t` has the argument bounds and node conditions over
`τ` with node values below `α⁺`, the syntactic mode conditions hold over `α` and the parameters of `t` lie in `T^α`,
then `t` has them over `α` and `(trr α t)[τ] = t[α]`. -/
theorem urTrB {κ τ : Ordinal.{0}} (hB : Bases κ τ) {n : ℕ} (hn : 1 ≤ n) (t : UnT false) (hq : Qs κ t)
    (hl : Lv (· ∈ Tset τ) (trr (Dl τ n) t)) (hw : WFr τ (trr (Dl τ n) t)) (hd : Nd τ (· < Dp τ n) (trr (Dl τ n) t))
    (hh : HdDA (Dl τ n) t) (hla : Lv (· ∈ Tset (Dl τ n)) t) :
    WFr (Dl τ n) t ∧ ev τ (trr (Dl τ n) t) = ev (Dl τ n) t := by
  obtain ⟨a1, a2, -⟩ := urTrBB hB hn t hq hl hw hd hh hla
  exact ⟨a1, a2⟩



end Googology.Trans.PoR.InaccPsi.R2.Ur

import Googology.Trans.BMS.TrioFixStripCalibEx
import Googology.Trans.BMS.TrioTreeRules

/-!
# The patched `blockF` writes the tree of the term

`blockFSt` (`TrioFixStripCalibSim.lean`) is the plain builder's `blockF` with the corrected
rule 1.  With no regime it never lays a storey, so it writes one column per summand
`ω^{e}` of its input and, below it, what `stripSt e` spells.  On the reading of a term of
the fragment `Rd` (`TrioFixStripCalibRead.lean`) the summand `ψ_a(b)` has the column
`(x, a, 0)` (`lvl_sx`, and `writeLevel` of `Ω_1` is the one column `(x, 1, 0)`,
`TrioTreeRules.writeLevel_one`), and its children spell the reading of `b`
(`stripSt_sx`).  So `blockFSt` writes the tree of the term, `TrioTreeRules.treeI`
(`blockFSt_tree`), when the fuel covers the nesting depth.
-/

namespace Googology.Trans.BMS.TrioFixStripCalib

open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term
open Googology.Trans.BMS (AllNil)
open Googology.Trans.BMS.TrioRules
open Googology.Trans.BMS.TrioFixOfTerm (ofTermFix)
open Googology.Trans.BMS.TrioTree (Sub01 TopNil allNilB allNilB_iff topNil_of_allNil subY)
open Googology.Trans.BMS.TrioTreeRules (sums expandG2 GDesc2 mem_expandG2 B2 writeLevel_one
  treeI treeI_sums cmpF_one_one)
open Googology.Trans.BMS.TrioRulesE0 (dep dep_eq_zero Spec spec_bind spec_mono spec_forIn
  spec_pure spec_get_bind spec_bind_last spent_none flatMap_range'_const spec_push_bind
  spec_pure_bind spec_modify0_bind spec_modify_bind)
open Googology.Trans.BMS.TrioFixStrip (stripSt uncollapses)

/-! ### The depth -/

theorem dep_le_rdT : ∀ x : Term, dep x ≤ rdT x
  | nil => le_rfl
  | cons a b t => by
    have h1 := dep_le_rdT b
    have h2 := dep_le_rdT t
    have h3 := rdT_arg_lt a b
    simp only [dep, rdT_cons]
    omega

theorem dep_arg_lt_of_mem : ∀ {γ : Term} {p : Term × Term}, p ∈ sums γ → dep p.2 + 1 ≤ dep γ
  | nil, _, h => by cases h
  | cons c e u, p, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp only [dep]; omega
    · have := dep_arg_lt_of_mem h; simp only [dep]; omega

/-! ### What `blockFSt` writes -/

/-- The columns `blockFSt` writes, cut at the fuel. -/
def treeS : Nat → Int → Od → List TrioRules.Col
  | 0, _, _ => []
  | n + 1, x, A => A.flatMap fun ec =>
      (List.range' 0 ec.2).flatMap fun _ =>
        ⟨x, if (lvl ec.1).isSome then 1 else 0, false⟩ :: treeS n (x + 1) (stripSt ec.1)

/-- What `blockFSt` needs of its input: a term of the fragment within the fuel; free of `Ω`
at the top unless it is an argument of a collapse or the children of an `Ω_1` column. -/
def CondS (γ : Term) (n : Nat) (arg : Bool) (d : Int) (plvl : Option Od) (py : Int) : Prop :=
  Rd γ ∧ dep γ ≤ n ∧ (arg = false → TopNil γ ∨ (plvl = some one ∧ py = 1)) ∧
    (arg = true → d = 0 ∨ d = 1)

theorem cmpOrd_one_one : cmpOrd one one = .eq := cmpF_one_one _

theorem mem_read_grp {γ : Term} {L : List ((Term × Term) × Nat)} (hG : GDesc2 L)
    (hO : ofTermFix γ = grpS L) (hE : expandG2 L = sums γ) {ec : Ex × Nat}
    (hec : ec ∈ ofTermFix γ) :
    ∃ a b k, ec = (sx a b, k) ∧ (a, b) ∈ sums γ := by
  rw [hO] at hec
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hec
  exact ⟨q.1.1, q.1.2, q.2, rfl, hE ▸ mem_expandG2 hG hq⟩

theorem sums_nil_of_topNil {γ : Term} (h : TopNil γ) : ∀ p ∈ sums γ, p.1 = nil := by
  induction γ with
  | nil => intro p hp; cases hp
  | cons a b t _ _ iht =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h.1
    · exact iht h.2 p hp

/-- **`blockFSt` writes `treeS`**, on the fragment. -/
theorem blockFSt_spec (Mf : Od → Cols) (h1 : Mf one = B2) : ∀ (n : Nat) (γ : Term) (x d : Int)
    (arg : Bool) (plvl : Option Od) (py : Int), CondS γ n arg d plvl py →
    Spec (blockFSt Mf n (ofTermFix γ) x d arg plvl py) (fun _ => True)
      (treeS n x (ofTermFix γ)).toArray := by
  intro n
  induction n with
  | zero =>
    intro γ x d arg plvl py _
    simpa [blockFSt, treeS] using spec_pure (Q := fun _ : Unit => True) trivial
  | succ n ih =>
    intro γ x d arg plvl py hc
    obtain ⟨hR, hdn, hTop, hdd⟩ := hc
    obtain ⟨L, hG, hO, hE⟩ := inv_all hR
    simp only [blockFSt]
    refine spec_bind (spec_mono (spec_forIn (ofTermFix γ) _ (fun r : MProd Int Int => r = ⟨d, x⟩)
      (fun ec => (List.range' 0 ec.2).flatMap fun _ =>
        (⟨x, if (lvl ec.1).isSome then 1 else 0, false⟩ : TrioRules.Col) ::
          treeS n (x + 1) (stripSt ec.1))
      ?_ (⟨d, x⟩ : MProd Int Int) rfl) (fun _ _ => trivial)) (fun _ _ => spec_pure trivial)
      (by simp [treeS])
    intro ec hec r hr
    subst hr
    obtain ⟨a, b, k, rfl, hab⟩ := mem_read_grp hG hO hE hec
    have hp : Rd (psi a b) := rd_of_mem_sums hab hR
    have hdb : dep b + 1 ≤ n + 1 := by
      have := dep_arg_lt_of_mem hab; simp only at this; omega
    simp only
    rw [lvl_sx hp, stripSt_sx hp, uncollapses_sx hp]
    have hcb : ∀ (arg' : Bool) (d' : Int) (pl : Option Od) (py' : Int),
        (arg' = false → TopNil b ∨ (pl = some one ∧ py' = 1)) → (arg' = true → d' = 0 ∨ d' = 1) →
        CondS b n arg' d' pl py' := fun arg' d' pl py' h1 h2 =>
      ⟨rd_arg hp, by omega, h1, h2⟩
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    by_cases ha : a = nil
    · -- a `ψ_0` node: the column `(x, 0, 0)`
      subst ha
      have hcol : (if (if nil = nil then (none : Option Od) else some one).isSome then (1 : Int)
          else 0) = 0 := rfl
      rw [hcol]
      refine spec_bind (w2 := #[]) (spec_forIn _ _ (fun r : MProd Int Int => r = ⟨d, x⟩)
        (fun _ => ⟨x, 0, false⟩ :: treeS n (x + 1) (ofTermFix b)) ?_ (⟨d, x⟩ : MProd Int Int) rfl)
        (fun r hr => ?_) ?_
      · intro i _ r hr
        subst hr
        refine spec_get_bind fun s1 _ => spec_get_bind fun s2 hs2 => ?_
        rw [spent_none Mf s2 hs2]
        simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        rw [show (({ x := x, y := 0, z := false } :: treeS n (x + 1) (ofTermFix b)).toArray :
            Array TrioRules.Col) = #[⟨x, 0, false⟩] ++ (treeS n (x + 1) (ofTermFix b)).toArray by
            simp]
        repeat trioE0_step
        rw [spent_none Mf _ ‹_›]
        simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        repeat trioE0_step
        refine spec_bind_last (ih b _ _ _ _ _ (hcb _ _ _ _ ?_ ?_)) (fun _ _ => ?_)
        · intro hf
          left
          have : allNilB b = true := by simpa using hf
          exact topNil_of_allNil b ((allNilB_iff b).mp this)
        · intro _; left; rfl
        · repeat trioE0_step
      · subst hr
        repeat trioE0_step
      · simp [Std.Legacy.Range.size]
    · -- a `ψ_1` node: the column `(x, 1, 0)`
      have ha1 : a = t1 := hp.2.1.1.resolve_left ha
      subst ha1
      have hl1 : (if t1 = nil then (none : Option Od) else some one) = some one := by
        simp [t1_ne_nil]
      simp only [hl1, Option.isSome_some, ↓reduceIte]
      have hwl := writeLevel_one Mf h1 x d
      cases arg
      rcases hTop rfl with hT | ⟨rfl, rfl⟩
      exact absurd (sums_nil_of_topNil hT (t1, b) hab) t1_ne_nil
      all_goals
        refine spec_bind (w2 := #[]) (spec_forIn _ _ (fun r : MProd Int Int => r = ⟨d, x⟩)
          (fun _ => ⟨x, 1, false⟩ :: treeS n (x + 1) (ofTermFix b)) ?_ (⟨d, x⟩ : MProd Int Int) rfl)
          (fun r hr => ?_) ?_
        · intro i _ r hr
          subst hr
          refine spec_get_bind fun s1 _ => spec_get_bind fun s2 hs2 => ?_
          rw [spent_none Mf s2 hs2]
          simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          first
          | simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
              hwl (hdd rfl)]
          | simp only [Bool.not_false, Bool.true_and, cmpOrd_one_one, beq_self_eq_true, ↓reduceIte]
          rw [show (({ x := x, y := 1, z := false } :: treeS n (x + 1) (ofTermFix b)).toArray :
              Array TrioRules.Col) = #[⟨x, 1, false⟩] ++ (treeS n (x + 1) (ofTermFix b)).toArray by
              simp]
          repeat trioE0_step
          rw [spent_none Mf _ ‹_›]
          simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          repeat trioE0_step
          refine spec_bind_last (ih b _ _ _ _ _ (hcb _ _ _ _ ?_ ?_)) (fun _ _ => ?_)
          · intro _; right; exact ⟨rfl, rfl⟩
          · intro _; right; rfl
          · repeat trioE0_step
        · subst hr
          repeat trioE0_step
        · simp [Std.Legacy.Range.size]

theorem grpS_flatMap {β : Type} (F : Ex → List β) : ∀ L : List ((Term × Term) × Nat),
    (grpS L).flatMap (fun ec => (List.range' 0 ec.2).flatMap (fun _ => F ec.1)) =
      (expandG2 L).flatMap (fun p => F (sx p.1 p.2)) := by
  intro L
  induction L with
  | nil => rfl
  | cons p L ih =>
    simp only [grpS, List.map_cons] at ih ⊢
    rw [List.flatMap_cons, ih, flatMap_range'_const]
    simp only [expandG2, List.flatMap_cons, List.flatMap_append]
    congr 1
    generalize p.2 = k
    induction k with
    | zero => rfl
    | succ k ihk => simp [List.replicate_succ, List.flatMap_cons, ihk]

/-- **`treeS` is the tree**, when the fuel covers the depth. -/
theorem treeS_read : ∀ (n : Nat) (γ : Term) (x : Int), Rd γ → dep γ ≤ n →
    treeS n x (ofTermFix γ) = treeI x γ := by
  intro n
  induction n with
  | zero =>
    intro γ x _ hd
    rw [dep_eq_zero (Nat.le_zero.mp hd)]; rfl
  | succ n ih =>
    intro γ x hR hd
    obtain ⟨L, hG, hO, hE⟩ := inv_all hR
    show (ofTermFix γ).flatMap _ = _
    rw [hO, grpS_flatMap (fun e => (⟨x, if (lvl e).isSome then 1 else 0, false⟩ : TrioRules.Col) ::
      treeS n (x + 1) (stripSt e)) L, hE, treeI_sums]
    apply List.flatMap_congr
    intro p hp
    have hpp : Rd (psi p.1 p.2) := rd_of_mem_sums hp hR
    have hdb : dep p.2 + 1 ≤ n + 1 := by
      have := dep_arg_lt_of_mem hp; simp only at this; omega
    obtain ⟨a, b⟩ := p
    simp only at hpp hdb ⊢
    rw [lvl_sx hpp, stripSt_sx hpp, ih b (x + 1) (rd_arg hpp) (by omega)]
    congr 2
    rcases hpp.2.1.1 with rfl | rfl
    · simp [subY]
    · simp [subY, t1_ne_nil]

/-- **`blockFSt` writes the tree of the term.** -/
theorem blockFSt_tree (Mf : Od → Cols) (h1 : Mf one = B2) (n : Nat) (γ : Term) (x d : Int)
    (arg : Bool) (plvl : Option Od) (py : Int) (hc : CondS γ n arg d plvl py) :
    Spec (blockFSt Mf n (ofTermFix γ) x d arg plvl py) (fun _ => True) (treeI x γ).toArray := by
  rw [← treeS_read n γ x hc.1 hc.2.1]
  exact blockFSt_spec Mf h1 n γ x d arg plvl py hc

end Googology.Trans.BMS.TrioFixStripCalib

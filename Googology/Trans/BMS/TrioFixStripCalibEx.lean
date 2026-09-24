import Googology.Trans.BMS.TrioFixStripCalibRead
import Googology.Trans.BMS.TrioFixStripCalibSim

/-!
# What the patched builder reads off the exponent of a summand

`TrioFixStripCalibRead.lean` writes the reading `ofTermFix` of a term of the fragment summand
by summand: the summand `ψ_a(b)` becomes `ω^{sx a b}`.  The builder with the corrected rule 1
(`TrioFixStrip`) reads four things off such an exponent `e = sx a b`:

* `lvl e`, the level of the column: `none` for `a = 0`, `Ω_1` for `a = 1` (`lvl_sx`);
* `stripSt e`, what the children spell: the reading of `b` itself (`stripSt_sx`);
* `uncollapses e`, whether the children are an argument of a collapse: `a = 0` and `b` has
  `Ω` in it (`uncollapses_sx`);
* `chainAtom e`, the atom at the end of the leading-exponent chain (`chainAtomF_sx`).

All on the fragment `Rd` of `TrioFixStripCalibRead.lean` (standard, subscripts `0`/`1`, the
reading at most `100` deep).
-/

namespace Googology.Trans.BMS.TrioFixStripCalib

open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term
open Googology.Trans.BMS (AllNil)
open Googology.Trans.BMS.TrioRules
open Googology.Trans.BMS.TrioFixOfTerm (ofTermFix add_nil_left add_nil_right add_ne_nil)
open Googology.Trans.BMS.TrioTree (Sub01 TopNil allNilB allNilB_iff topNil_of_allNil
  sub01_of_allNil)
open Googology.Trans.BMS.TrioTreeStd (appT appT_nil_right)
open Googology.Trans.BMS.TrioFixStripTree (hiPart loPart expoT TopS topS_of_sub01 Good
  appT_hi_lo loPart_cases lt_hiPart hiPart_t1 sub01_hiPart sub01_loPart OT_loPart
  allNil_lt_hiPart)
open Googology.Trans.BMS.TrioTreeRules (sums pcmp pcmp_def expandG2 GDesc2 GDesc2_head_pos
  GDesc2_pos mem_expandG2)
open Googology.Trans.BMS.TrioRulesE0 (add_gt add_eq)
open Googology.Trans.BMS.TrioFixFuel (exDep odDep)
open Googology.Trans.BMS.TrioFixStrip (stripSt uncollapses chainAtom chainAtomF chainArg)

/-! ### The reading of a sum, piece by piece -/

theorem read_head {a g w : Term} (hx : Rd (cons a g w)) :
    ∃ c L', 0 < c ∧ ofTermFix (cons a g w) = (sx a g, c) :: L' := by
  obtain ⟨L, hG, hO, hE⟩ := inv_all hx
  cases L with
  | nil => simp [expandG2, sums] at hE
  | cons q L' =>
    obtain ⟨d, c⟩ := q
    have hc : 0 < c := GDesc2_head_pos hG
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    have hd : d = (a, g) := by
      simp [expandG2, sums, List.replicate_succ] at hE; exact hE.1
    subst hd
    exact ⟨c' + 1, grpS L', by omega, hO⟩

theorem mem_read {x : Term} (hx : Rd x) {q : Ex × Nat} (hq : q ∈ ofTermFix x) :
    ∃ p ∈ sums x, q.1 = sx p.1 p.2 ∧ 0 < q.2 := by
  obtain ⟨L, hG, hO, hE⟩ := inv_all hx
  rw [hO] at hq
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
  exact ⟨r.1, hE ▸ mem_expandG2 hG hr, rfl, GDesc2_pos hG r hr⟩

theorem rd_lo {x : Term} (hx : Rd x) : Rd (loPart x) :=
  ⟨OT_loPart x hx.1, sub01_loPart x hx.2.1, le_trans (rdT_loPart_le x) hx.2.2⟩

theorem rd_hi {x : Term} (hx : Rd x) : Rd (hiPart x) :=
  ⟨OT_hiPart hx.1, sub01_hiPart x hx.2.1, le_trans (rdT_hiPart_le x) hx.2.2⟩

theorem sums_hiPart : ∀ (x : Term), Sub01 x → ∀ p ∈ sums (hiPart x), p.1 = t1 ∧ p ∈ sums x
  | nil, _, p, hp => by simp [hiPart, sums] at hp
  | cons a b t, hS, p, hp => by
    by_cases ha : a = nil
    · simp [hiPart, ha, sums] at hp
    · have ha1 : a = t1 := hS.1.resolve_left ha
      simp only [hiPart, ha, if_false, sums] at hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨ha1, List.mem_cons_self⟩
      · obtain ⟨h1, h2⟩ := sums_hiPart t hS.2.2 p hp
        exact ⟨h1, List.mem_cons_of_mem _ h2⟩

theorem sx_W : sx t1 nil = .W one := by
  rw [sx_t1 (d := nil) trivial, read_nil, sEx_t1_nil]

theorem cmp_gt_iff {x y : Term} : Term.cmp x y = .gt ↔ y < x := by
  constructor
  · intro h
    have := cmp_swap x y
    rw [h] at this
    exact this.symm
  · intro h
    have := cmp_swap y x
    rw [show Term.cmp y x = .lt from h] at this
    exact this.symm

theorem add_append (a : Od) : ∀ (A B : Od), A ≠ [] → add a (A ++ B) = add a A ++ B
  | [], _, h => absurd rfl h
  | (lead, cb) :: bt, B, _ => by
    simp only [List.cons_append, add]
    split <;> simp

theorem add_all_gt {a : Od} {lead : Ex} {cb : Nat} {bt : Od}
    (h : ∀ q ∈ a, cmpExp q.1 lead = .gt) : add a ((lead, cb) :: bt) = a ++ (lead, cb) :: bt := by
  have h1 : a.filter (fun t => cmpExp t.1 lead == .gt) = a :=
    List.filter_eq_self.mpr (fun q hq => by simp [h q hq])
  have h2 : a.filter (fun t => cmpExp t.1 lead == .eq) = [] :=
    List.filter_eq_nil_iff.mpr (fun q hq => by simp [h q hq])
  simp only [add, h1, h2]

/-- **The reading of an argument is its `Ω` part, then the rest.** -/
theorem read_hi_lo : ∀ b : Term, Rd b →
    ofTermFix b = ofTermFix (hiPart b) ++ ofTermFix (loPart b)
  | nil, _ => rfl
  | cons c e u, hb => by
    rcases hb.2.1.1 with rfl | rfl
    · simp [hiPart, loPart, read_nil]
    · have hu := rd_tail hb
      have ih := read_hi_lo u hu
      rw [hiPart_t1, show loPart (cons t1 e u) = loPart u by simp [loPart, t1_ne_nil],
        read_cons, read_cons, ih]
      by_cases hh : hiPart u = nil
      · rw [hh, read_nil, List.nil_append, add_nil_right]
        rcases loPart_cases u with hl | ⟨g, w, hl⟩
        · rw [hl, read_nil]; simp [add_nil_right]
        · have hlo := rd_lo hu
          rw [hl] at hlo ⊢
          obtain ⟨k, L', _, hL⟩ := read_head hlo
          rw [hL]
          have hpe : Rd (psi t1 e) := rd_of_mem_sums (x := cons t1 e u) (p := (t1, e))
            List.mem_cons_self hb
          have hpg : Rd (psi nil g) := rd_of_mem_sums (x := cons nil g w) (p := (nil, g))
            List.mem_cons_self hlo
          have hc : cmpExp (sx t1 e) (sx nil g) = .gt := by
            rw [cmpExp_sx hpe hpg, pcmp_def]; rfl
          rw [add_gt hc]; rfl
      · have hne : ofTermFix (hiPart u) ≠ [] := fun h => hh ((read_eq_nil_iff _).mp h)
        rw [add_append _ _ _ hne]

/-- **`add` puts the `Ω` part before the rest.** -/
theorem add_hi_lo {b : Term} (hb : Rd b) :
    add (ofTermFix (hiPart b)) (ofTermFix (loPart b)) = ofTermFix b := by
  rw [read_hi_lo b hb]
  rcases loPart_cases b with hl | ⟨g, w, hl⟩
  · rw [hl, read_nil, add_nil_right, List.append_nil]
  · have hlo := rd_lo hb
    rw [hl] at hlo ⊢
    obtain ⟨k, L', _, hL⟩ := read_head hlo
    rw [hL]
    have hpg : Rd (psi nil g) := rd_of_mem_sums (x := cons nil g w) (p := (nil, g))
      List.mem_cons_self hlo
    refine add_all_gt (fun q hq => ?_)
    obtain ⟨p, hp, hq1, _⟩ := mem_read (rd_hi hb) hq
    obtain ⟨hp1, hp2⟩ := sums_hiPart b hb.2.1 p hp
    have hpp : Rd (psi p.1 p.2) := rd_of_mem_sums hp2 hb
    rw [hq1, cmpExp_sx hpp hpg, pcmp_def, hp1]; rfl

/-! ### The shape of the exponent -/

/-- The two readings the program's `add` can give `Ω + b`, `b ≠ 0`. -/
theorem sx_t1_shape {b : Term} (hp : Rd (psi t1 b)) (hb : b ≠ nil) :
    ∃ c e1 u k L', b = cons c e1 u ∧ ofTermFix b = (sx c e1, k) :: L' ∧ 0 < k ∧
      Rd (psi c e1) ∧
      ((c = nil ∧ sx t1 b = .o ((.W one, 1) :: ofTermFix b)) ∨
       (c = t1 ∧ e1 = nil ∧ sx t1 b = .o ((.W one, 1 + k) :: L')) ∨
       (c = t1 ∧ e1 ≠ nil ∧ sx t1 b = .o (ofTermFix b))) := by
  have hs := sumF_of_rd hp
  rcases sx_cases hs.sub hs.S01 hs.lo hs.good with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ |
      ⟨_, h, _⟩ | ⟨_, _, e⟩
  · exact absurd h t1_ne_nil
  · exact absurd h t1_ne_nil
  · exact absurd h t1_ne_nil
  · exact absurd h t1_ne_nil
  · exact absurd h hb
  · have hrb := rd_arg hp
    cases b with
    | nil => exact absurd rfl hb
    | cons c e1 u =>
      obtain ⟨k, L', hk, hL⟩ := read_head hrb
      have hpe : Rd (psi c e1) := rd_of_mem_sums (x := cons c e1 u) (p := (c, e1))
        List.mem_cons_self hrb
      refine ⟨c, e1, u, k, L', rfl, hL, hk, hpe, ?_⟩
      rw [e, hL]
      have hc : cmpExp (.W one) (sx c e1) = pcmp (t1, nil) (c, e1) := by
        rw [← sx_W]; exact cmpExp_sx rd_psi_t1_nil hpe
      rcases hrb.2.1.1 with rfl | rfl
      · left
        refine ⟨rfl, ?_⟩
        rw [add_gt (by rw [hc, pcmp_def]; rfl)]
      · right
        by_cases he : e1 = nil
        · subst he
          left
          refine ⟨rfl, rfl, ?_⟩
          rw [add_eq (by rw [hc, pcmp_def]; rfl), sx_W]
        · right
          refine ⟨rfl, he, ?_⟩
          rw [add_lt' (by
            rw [hc, pcmp_def]
            cases e1 with
            | nil => exact absurd rfl he
            | cons _ _ _ => rfl)]

/-- An argument of the lower part of a good `b`, above the `Ω` part: it has the same `Ω`
part. -/
theorem hiPart_of_absorbed {b g1 w : Term} (hp : Rd (psi nil b)) (hA : ¬ AllNil b)
    (hl : loPart b = cons nil g1 w) (hlt : hiPart b < g1) (hg1 : Rd (psi nil g1)) :
    hiPart g1 = hiPart b ∧ ¬ AllNil g1 := by
  have hs := sumF_of_rd hp
  have hg := hs.good rfl
  refine ⟨?_, fun hA1 => Term.lt_asymm hlt (allNil_lt_hiPart hA1 hg hA)⟩
  have hgb : g1 < b := by
    cases hg with
    | allNil h => exact absurd h hA
    | omega _ _ _ _ hlt' => exact hlt' g1 (by rw [hl]; exact List.mem_cons_self ..)
  by_contra hne
  have := lt_hiPart g1 b (topS_of_sub01 _ hg1.2.1.2.1) (topS_of_sub01 _ hs.S01) hgb hne
  exact Term.lt_asymm hlt this

/-- The three readings `ψ_0(b) = ω^{ψ_0(h) + l}` can get, `b = h + l` with `l ≠ 0`. -/
theorem sx_nil_shape {b : Term} (hp : Rd (psi nil b)) (hA : ¬ AllNil b) {g1 w : Term}
    (hl : loPart b = cons nil g1 w) :
    ∃ k L', ofTermFix (loPart b) = (sx nil g1, k) :: L' ∧ 0 < k ∧ Rd (psi nil g1) ∧
      ((g1 < hiPart b ∧
          sx nil b = .o ((.psi [] (ofTermFix (hiPart b)), 1) :: ofTermFix (loPart b))) ∨
       (g1 = hiPart b ∧ sx nil g1 = .psi [] (ofTermFix (hiPart b)) ∧
          sx nil b = .o ((.psi [] (ofTermFix (hiPart b)), 1 + k) :: L')) ∨
       (hiPart b < g1 ∧ sx nil b = .o (ofTermFix (loPart b)))) := by
  have hs := sumF_of_rd hp
  have hg := hs.good rfl
  have hh := hiPart_ne_nil hg hA
  have hl0 : loPart b ≠ nil := by rw [hl]; exact fun h => Term.noConfusion h
  have hlo := rd_loPart hp
  rw [hl] at hlo
  obtain ⟨k, L', hk, hL⟩ := read_head hlo
  have hpg : Rd (psi nil g1) := rd_of_mem_sums (x := cons nil g1 w) (p := (nil, g1))
    List.mem_cons_self hlo
  have hph := rd_psi_hiPart hp hg hA
  have hEh := sx_hiPart hs.S01 hh
  rw [hl]
  refine ⟨k, L', hL, hk, hpg, ?_⟩
  rcases sx_cases hs.sub hs.S01 hs.lo hs.good with ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ |
      ⟨_, _, _, e⟩ | ⟨h, _⟩ | ⟨h, _⟩
  · exact absurd (h ▸ trivial) hA
  · exact absurd h hA
  · exact absurd h hl0
  · rw [e, hl, hL]
    have hc : cmpExp (.psi [] (ofTermFix (hiPart b))) (sx nil g1) = Term.cmp (hiPart b) g1 := by
      rw [← hEh, cmpExp_sx hph hpg, pcmp_def, cmp_self]; rfl
    cases hcm : Term.cmp (hiPart b) g1 with
    | gt =>
      left
      exact ⟨cmp_gt_iff.mp hcm, by rw [add_gt (hc.trans hcm)]⟩
    | eq =>
      right; left
      have he : hiPart b = g1 := cmp_eq_iff.mp hcm
      refine ⟨he.symm, by rw [← he, hEh], ?_⟩
      rw [add_eq (hc.trans hcm), ← he, hEh]
    | lt =>
      right; right
      exact ⟨hcm, by rw [add_lt' (hc.trans hcm)]⟩
  · exact absurd h (fun h => Term.noConfusion h)
  · exact absurd h (fun h => Term.noConfusion h)

/-- **The leading exponent of `sx a b`**, one level down. -/
theorem sx_head {a b : Term} (hp : Rd (psi a b)) :
    (a = nil ∧ b = nil ∧ sx a b = .o []) ∨
    (a = nil ∧ ¬ AllNil b ∧ sx a b = .psi [] (ofTermFix (hiPart b))) ∨
    (a = t1 ∧ b = nil ∧ sx a b = .W one) ∨
    (∃ h k L, sx a b = .o ((h, k) :: L) ∧
      ((a = nil ∧ ¬ AllNil b ∧ h = .psi [] (ofTermFix (hiPart b))) ∨
       (a = t1 ∧ h = .W one) ∨
       (∃ g, Rd (psi a g) ∧ h = sx a g ∧
          (a = nil → (AllNil g ↔ AllNil b) ∧ (¬ AllNil b → hiPart g = hiPart b))))) := by
  have hs := sumF_of_rd hp
  rcases sx_cases hs.sub hs.S01 hs.lo hs.good with ⟨ha, hb, e⟩ | ⟨ha, hb0, hA, e⟩ |
      ⟨ha, hA, hl0, e⟩ | ⟨ha, hA, hl0, e⟩ | ⟨ha, hb, e⟩ | ⟨ha, hb0, e⟩
  · exact Or.inl ⟨ha, hb, e⟩
  · subst ha
    right; right; right
    have hrb := rd_arg hp
    cases b with
    | nil => exact absurd rfl hb0
    | cons c g u =>
      have hA' := hA
      obtain ⟨rfl, hAg, _⟩ := hA'
      obtain ⟨k, L', _, hL⟩ := read_head hrb
      refine ⟨_, _, _, by rw [e, hL], Or.inr (Or.inr ⟨g, ?_, rfl, fun _ => ⟨?_, ?_⟩⟩)⟩
      · exact rd_of_mem_sums (x := cons nil g u) (p := (nil, g)) List.mem_cons_self hrb
      · exact ⟨fun _ => hA, fun _ => hAg⟩
      · intro h; exact absurd hA h
  · right; left
    exact ⟨ha, hA, by rw [e, hiPart_eq_of_loPart_nil hl0]⟩
  · subst ha
    obtain ⟨g1, w, hl⟩ : ∃ g1 w, loPart b = cons nil g1 w := by
      rcases loPart_cases b with h0 | h0
      · exact absurd h0 hl0
      · exact h0
    obtain ⟨k, L', hL, _, hpg, hc⟩ := sx_nil_shape hp hA hl
    right; right; right
    rcases hc with ⟨_, e'⟩ | ⟨_, _, e'⟩ | ⟨hlt, e'⟩
    · exact ⟨_, _, _, e', Or.inl ⟨rfl, hA, rfl⟩⟩
    · exact ⟨_, _, _, e', Or.inl ⟨rfl, hA, rfl⟩⟩
    · rw [hL] at e'
      obtain ⟨hh, hA1⟩ := hiPart_of_absorbed hp hA hl hlt hpg
      exact ⟨_, _, _, e', Or.inr (Or.inr ⟨g1, hpg, rfl, fun _ =>
        ⟨⟨fun h => absurd h hA1, fun h => absurd h hA⟩, fun _ => hh⟩⟩)⟩
  · exact Or.inr (Or.inr (Or.inl ⟨ha, hb, e⟩))
  · subst ha
    obtain ⟨c, e1, u, k, L', rfl, hL, _, hpe, hc⟩ := sx_t1_shape hp hb0
    right; right; right
    rcases hc with ⟨_, e'⟩ | ⟨_, _, e'⟩ | ⟨rfl, _, e'⟩
    · exact ⟨_, _, _, e', Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨_, _, _, e', Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · rw [hL] at e'
      exact ⟨_, _, _, e', Or.inr (Or.inr ⟨e1, hpe, rfl, fun h => absurd h t1_ne_nil⟩)⟩

theorem exDep_head {h : Ex} {k : Nat} {L : Od} : exDep h + 1 ≤ exDep (.o ((h, k) :: L)) := by
  rw [exDep_o, odDep_cons]; simp only; omega

/-! ### The level, the chain, the flag and the children -/

/-- The atom at the end of the leading-exponent chain of `sx a b`. -/
def cav (a b : Term) : Option Ex :=
  if a = nil then (if allNilB b then none else some (.psi [] (ofTermFix (hiPart b))))
  else some (.W one)

theorem cav_eq {a b g : Term} (h : a = nil → (AllNil g ↔ AllNil b) ∧ (¬ AllNil b → hiPart g = hiPart b)) :
    cav a g = cav a b := by
  unfold cav
  by_cases ha : a = nil
  · obtain ⟨h1, h2⟩ := h ha
    simp only [ha, if_true]
    by_cases hb : AllNil b
    · have hg : AllNil g := h1.mpr hb
      rw [(allNilB_iff b).mpr hb, (allNilB_iff g).mpr hg]; rfl
    · have hg : ¬ AllNil g := fun hg => hb (h1.mp hg)
      rw [TrioFixStripTree.allNilB_false hb, TrioFixStripTree.allNilB_false hg, h2 hb]
  · simp [ha]

/-- **The chain of leading exponents** of `sx a b` ends in `ψ_0(Ω part of b)` for `a = 0`
and `b` with `Ω`, in `Ω` for `a = 1`, and in `0` for `a = 0`, `b` free of `Ω`. -/
theorem chainAtomF_sx : ∀ (n : Nat) (a b : Term), Rd (psi a b) → exDep (sx a b) ≤ n →
    chainAtomF n (sx a b) = cav a b := by
  intro n
  induction n with
  | zero => intro a b _ hd; have := exDep_pos (sx a b); omega
  | succ n ih =>
    intro a b hp hd
    rcases sx_head hp with ⟨rfl, rfl, e⟩ | ⟨rfl, hA, e⟩ | ⟨rfl, rfl, e⟩ | ⟨h, k, L, e, hh⟩
    · rw [e]; rfl
    · rw [e]; simp [chainAtomF, cav, TrioFixStripTree.allNilB_false hA]
    · rw [e]; simp [chainAtomF, cav, t1_ne_nil]
    · rw [e]
      have hdh := exDep_head (h := h) (k := k) (L := L)
      rw [e] at hd
      show chainAtomF n h = _
      rcases hh with ⟨rfl, hA, rfl⟩ | ⟨rfl, rfl⟩ | ⟨g, hg, rfl, hc⟩
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by
          have := exDep_pos (.psi [] (ofTermFix (hiPart b)))
          simp [exDep_psi] at hdh; omega⟩
        simp [chainAtomF, cav, TrioFixStripTree.allNilB_false hA]
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by
          simp [exDep_W] at hdh; omega⟩
        simp [chainAtomF, cav, t1_ne_nil]
      · rw [ih a g hg (by omega)]
        exact cav_eq hc

theorem chainArg_sx {a b : Term} (hp : Rd (psi a b)) :
    chainArg (sx a b) =
      if a = nil then (if allNilB b then none else some (ofTermFix (hiPart b))) else none := by
  unfold chainArg chainAtom
  rw [chainAtomF_sx fuel a b hp (by have := exDep_sx_le100 hp; simp only [fuel]; omega)]
  unfold cav
  by_cases ha : a = nil
  · cases allNilB b <;> simp [ha]
  · simp [ha]

/-- **The level of the column of `ψ_a(b)`**: none for `a = 0`, `Ω_1` for `a = 1`. -/
theorem lvlF_sx : ∀ (n : Nat) (a b : Term), Rd (psi a b) → exDep (sx a b) ≤ n →
    lvlF n (sx a b) = if a = nil then none else some one := by
  intro n
  induction n with
  | zero => intro a b _ hd; have := exDep_pos (sx a b); omega
  | succ n ih =>
    intro a b hp hd
    rcases sx_head hp with ⟨rfl, rfl, e⟩ | ⟨rfl, hA, e⟩ | ⟨rfl, rfl, e⟩ | ⟨h, k, L, e, hh⟩
    · rw [e]; rfl
    · rw [e]; rfl
    · rw [e]; simp [lvlF, t1_ne_nil]
    · rw [e]
      have hdh := exDep_head (h := h) (k := k) (L := L)
      rw [e] at hd
      show lvlF n h = _
      rcases hh with ⟨rfl, hA, rfl⟩ | ⟨rfl, rfl⟩ | ⟨g, hg, rfl, hc⟩
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by
          have := exDep_pos (.psi [] (ofTermFix (hiPart b)))
          simp [exDep_psi] at hdh; omega⟩
        rfl
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by
          simp [exDep_W] at hdh; omega⟩
        simp [lvlF, t1_ne_nil]
      · exact ih a g hg (by omega)

theorem lvl_sx {a b : Term} (hp : Rd (psi a b)) :
    lvl (sx a b) = if a = nil then none else some one :=
  lvlF_sx fuel a b hp (by have := exDep_sx_le100 hp; simp only [fuel]; omega)

/-- `sx 0 g` for `g` free of `Ω` is an `ω`-power, not an atom. -/
theorem sx_nil_allNil {g : Term} (hp : Rd (psi nil g)) (hA : AllNil g) :
    ∃ X, sx nil g = .o X := by
  have hs := sumF_of_rd hp
  rcases sx_cases hs.sub hs.S01 hs.lo hs.good with ⟨_, _, e⟩ | ⟨_, _, _, e⟩ | ⟨_, h, _⟩ |
      ⟨_, h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
  · exact ⟨_, e⟩
  · exact ⟨_, e⟩
  · exact absurd hA h
  · exact absurd hA h
  · exact absurd h.symm t1_ne_nil
  · exact absurd h.symm t1_ne_nil

theorem sx_t1_o {e : Term} (hp : Rd (psi t1 e)) (he : e ≠ nil) : ∃ X, sx t1 e = .o X := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hc⟩ := sx_t1_shape hp he
  rcases hc with ⟨_, e'⟩ | ⟨_, _, e'⟩ | ⟨_, _, e'⟩ <;> exact ⟨_, e'⟩

theorem sx_nil_o_of_absorbed {g : Term} (hp : Rd (psi nil g)) (hA : ¬ AllNil g)
    (hl : loPart g ≠ nil) : ∃ X, sx nil g = .o X := by
  obtain ⟨g1, w, e⟩ : ∃ g1 w, loPart g = cons nil g1 w := by
    rcases loPart_cases g with h0 | h0
    · exact absurd h0 hl
    · exact h0
  obtain ⟨_, _, _, _, _, hc⟩ := sx_nil_shape hp hA e
  rcases hc with ⟨_, e'⟩ | ⟨_, _, e'⟩ | ⟨_, e'⟩ <;> exact ⟨_, e'⟩

theorem stripSt_o_nochain {X : Ex} {k : Nat} {L : Od} (hX : ∃ Y, X = .o Y)
    (hc : chainArg X = none) : stripSt (.o ((X, k) :: L)) = (X, k) :: L := by
  obtain ⟨Y, rfl⟩ := hX
  simp [stripSt, ato, hc]

theorem stripSt_o_chain {X : Ex} {k : Nat} {L : Od} {Z : Od} (hX : ∃ Y, X = .o Y)
    (hc : chainArg X = some Z) : stripSt (.o ((X, k) :: L)) = add Z ((X, k) :: L) := by
  obtain ⟨Y, rfl⟩ := hX
  simp [stripSt, ato, hc]

/-- **Rule 1, corrected, on the fragment: the children of `ψ_a(b)` spell `b`.** -/
theorem stripSt_sx {a b : Term} (hp : Rd (psi a b)) : stripSt (sx a b) = ofTermFix b := by
  have hs := sumF_of_rd hp
  rcases sx_cases hs.sub hs.S01 hs.lo hs.good with ⟨ha, hb, e⟩ | ⟨ha, hb0, hA, e⟩ |
      ⟨ha, hA, hl0, e⟩ | ⟨ha, hA, hl0, e⟩ | ⟨ha, hb, e⟩ | ⟨ha, hb0, e⟩
  · subst hb; rw [e]; rfl
  · subst ha
    have hrb := rd_arg hp
    cases b with
    | nil => exact absurd rfl hb0
    | cons c g u =>
      obtain ⟨rfl, hAg, _⟩ := hA
      obtain ⟨k, L', _, hL⟩ := read_head hrb
      have hpg : Rd (psi nil g) :=
        rd_of_mem_sums (x := cons nil g u) (p := (nil, g)) List.mem_cons_self hrb
      rw [e, hL]
      refine stripSt_o_nochain (sx_nil_allNil hpg hAg) ?_
      rw [chainArg_sx hpg]; simp [(allNilB_iff g).mpr hAg]
  · rw [e]; simp [stripSt, ato, add_nil_right]
  · subst ha
    obtain ⟨g1, w, hl⟩ : ∃ g1 w, loPart b = cons nil g1 w := by
      rcases loPart_cases b with h0 | h0
      · exact absurd h0 hl0
      · exact h0
    obtain ⟨k, L', hL, hk, hpg, hc⟩ := sx_nil_shape hp hA hl
    rw [← add_hi_lo (rd_arg hp)]
    rcases hc with ⟨_, e'⟩ | ⟨_, hsg, e'⟩ | ⟨hlt, e'⟩
    · rw [e']; simp [stripSt, ato]
    · rw [e', hL, ← hsg]
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp [stripSt, ato, hsg, show 1 + (k' + 1) - 1 = k' + 1 by omega]
    · rw [e', hL]
      obtain ⟨hh, hA1⟩ := hiPart_of_absorbed hp hA hl hlt hpg
      refine stripSt_o_chain (sx_nil_o_of_absorbed hpg hA1 ?_) ?_
      · intro h0
        have := hiPart_eq_of_loPart_nil h0
        rw [hh] at this
        exact Term.lt_irrefl _ (this ▸ hlt)
      · rw [chainArg_sx hpg]; simp [TrioFixStripTree.allNilB_false hA1, hh]
  · subst hb; rw [e]; rfl
  · subst ha
    obtain ⟨c, e1, u, k, L', rfl, hL, hk, hpe, hc⟩ := sx_t1_shape hp hb0
    rcases hc with ⟨_, e'⟩ | ⟨_, _, e'⟩ | ⟨rfl, he1, e'⟩
    · rw [e']; simp [stripSt, ato]
    · rw [e', hL]
      subst_vars
      rw [sx_W]
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp [stripSt, ato, show 1 + (k' + 1) - 1 = k' + 1 by omega]
    · rw [e', hL]
      refine stripSt_o_nochain (sx_t1_o hpe he1) ?_
      rw [chainArg_sx hpe]; simp [t1_ne_nil]

/-- **The flag of the children**: an argument of a collapse exactly when the summand is
`ψ_0(b)` with `Ω` in `b`. -/
theorem uncollapses_sx {a b : Term} (hp : Rd (psi a b)) :
    uncollapses (sx a b) = (decide (a = nil) && !allNilB b) := by
  have hs := sumF_of_rd hp
  rcases sx_cases hs.sub hs.S01 hs.lo hs.good with ⟨ha, hb, e⟩ | ⟨ha, hb0, hA, e⟩ |
      ⟨ha, hA, hl0, e⟩ | ⟨ha, hA, hl0, e⟩ | ⟨ha, hb, e⟩ | ⟨ha, hb0, e⟩
  · subst hb; rw [e]; simp [uncollapses, ato, allNilB]
  · subst ha
    have hrb := rd_arg hp
    cases b with
    | nil => exact absurd rfl hb0
    | cons c g u =>
      have hA' := hA
      obtain ⟨rfl, hAg, _⟩ := hA'
      obtain ⟨k, L', _, hL⟩ := read_head hrb
      have hpg : Rd (psi nil g) :=
        rd_of_mem_sums (x := cons nil g u) (p := (nil, g)) List.mem_cons_self hrb
      rw [e, hL]
      simp [uncollapses, ato, chainArg_sx hpg, (allNilB_iff g).mpr hAg, (allNilB_iff _).mpr hA]
  · rw [e]
    simp [uncollapses, ato, chainArg, chainAtom, fuel, chainAtomF, ha,
      TrioFixStripTree.allNilB_false hA]
  · subst ha
    obtain ⟨g1, w, hl⟩ : ∃ g1 w, loPart b = cons nil g1 w := by
      rcases loPart_cases b with h0 | h0
      · exact absurd h0 hl0
      · exact h0
    obtain ⟨k, L', hL, hk, hpg, hc⟩ := sx_nil_shape hp hA hl
    rcases hc with ⟨_, e'⟩ | ⟨_, hsg, e'⟩ | ⟨hlt, e'⟩
    · rw [e']; simp [uncollapses, ato, chainArg, chainAtom, fuel, chainAtomF,
        TrioFixStripTree.allNilB_false hA]
    · rw [e']; simp [uncollapses, ato, chainArg, chainAtom, fuel, chainAtomF,
        TrioFixStripTree.allNilB_false hA]
    · rw [e', hL]
      obtain ⟨hh, hA1⟩ := hiPart_of_absorbed hp hA hl hlt hpg
      simp [uncollapses, ato, chainArg_sx hpg, TrioFixStripTree.allNilB_false hA1,
        TrioFixStripTree.allNilB_false hA]
  · subst hb; subst ha; rw [e]; simp [uncollapses, ato, chainArg, chainAtom, fuel, chainAtomF, t1_ne_nil]
  · subst ha
    obtain ⟨c, e1, u, k, L', rfl, hL, hk, hpe, hc⟩ := sx_t1_shape hp hb0
    rcases hc with ⟨_, e'⟩ | ⟨_, _, e'⟩ | ⟨rfl, he1, e'⟩
    · rw [e']; simp [uncollapses, ato, chainArg, chainAtom, fuel, chainAtomF, t1_ne_nil]
    · rw [e']; simp [uncollapses, ato, chainArg, chainAtom, fuel, chainAtomF, t1_ne_nil]
    · rw [e', hL]
      simp [uncollapses, ato, chainArg_sx hpe, t1_ne_nil]

end Googology.Trans.BMS.TrioFixStripCalib

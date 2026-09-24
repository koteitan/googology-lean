import Googology.Trans.BMS.TrioFixStripCalibBlock

/-!
# The patched `placeUnits` lays the add units of `trioE2`

`placeUnitsSt` (`TrioFixStripCalibSim.lean`) lays the add units of `α` one after another.
On the reading of a countable term `α` of the fragment `Rd`, the unit of a summand `ψ_0(e)`
has the exponent `sx 0 e`, whose normal form is the reading of `expoT e`
(`TrioFixStripCalibRead.ki_all`).  So its digits are the summands `ψ_0(g)` of `P e`
(`expoT e`, or `e` less a final `1` when `e` has no `Ω`: `unit_digits`), and each digit's
tree is laid by `blockFSt` as the tree of `expoT g` (`TrioFixStripCalibBlock`), which is how
`trioE2` writes it (`mulUnitsE_peelE2`).  This gives `placeUnitsSt_read`.  The level the last
column names is `none` or `Ω_1` (`tailLevelSt_read`), and `Ω_1` has no suffix, so no mark is
appended.
-/

namespace Googology.Trans.BMS.TrioFixStripCalib

open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term
open Googology.Trans.BMS (AllNil peelOne)
open Googology.Trans.BMS.TrioRules
open Googology.Trans.BMS.TrioFixOfTerm (ofTermFix ofTermFix_allNil)
open Googology.Trans.BMS.TrioTree (Sub01 TopNil allNilB allNilB_iff topNil_of_allNil subY treeB
  mulUnitsE)
open Googology.Trans.BMS.TrioFixStripTree (hiPart loPart expoT Good expoT_allNil expoT_head
  topNil_expoT peelE2 peelE2_of_allNil peelE2_of_not argsOf_mapArgs addUnitsE2 bodyE2 trioE2)
open Googology.Trans.BMS.TrioTreeRules (sums expandG2 GDesc2 mem_expandG2 B2 treeI treeI_colsOf)
open Googology.Trans.BMS.TrioRulesE0 (dep exps ex Spec spec_bind spec_mono spec_forIn
  spec_pure spec_get_bind spec_bind_last spent_none spec_push_bind spec_pure_bind
  spec_modify0_bind spec_modify_bind Tup nrp nlx run_bind' run_modify_bind run_get_bind
  run_pure_bind run_pure' lastC_push lastC_append_two hf_of_spec colsOf toCol predBeta_ofTerm
  predBetaSpec exps_dropLastT)
open Googology.Trans.BMS.TrioFixStrip (stripSt uncollapses tailBlockFSt tailBlockSt
  unitTailLevelSt tailLevelSt)

/-! ### The units of the reading -/

theorem units_grpS (L : List ((Term × Term) × Nat)) :
    units (grpS L) = (expandG2 L).map (fun p => sx p.1 p.2) := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    simp only [units, grpS, List.map_cons, List.flatMap_cons, expandG2, List.map_append,
      List.map_replicate] at ih ⊢
    rw [ih]

theorem sums_map_topNil' : ∀ t : Term, TopNil t →
    (sums t).map (fun p => sx p.1 p.2) = (exps t).map (sx nil)
  | nil, _ => rfl
  | cons a b t, h => by
    obtain ⟨rfl, ht⟩ := h
    simp [sums, exps, sums_map_topNil' t ht]

theorem units_read {x : Term} (hR : Rd x) (hT : TopNil x) :
    units (ofTermFix x) = (exps x).map (sx nil) := by
  obtain ⟨L, _, hO, hE⟩ := inv_all hR
  rw [hO, units_grpS, hE, sums_map_topNil' x hT]

theorem mem_sums_of_mem_exps' : ∀ t : Term, TopNil t → ∀ e ∈ exps t, (nil, e) ∈ sums t
  | nil, _, _, h => by cases h
  | cons a b t, hT, e, he => by
    obtain ⟨rfl, hTt⟩ := hT
    rcases List.mem_cons.mp he with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_sums_of_mem_exps' t hTt e h)

theorem mem_exps_sums : ∀ t : Term, ∀ e ∈ exps t, ∃ a, (a, e) ∈ sums t
  | nil, _, h => by cases h
  | cons a b t, e, he => by
    rcases List.mem_cons.mp he with rfl | h
    · exact ⟨a, List.mem_cons_self⟩
    · obtain ⟨c, hc⟩ := mem_exps_sums t e h
      exact ⟨c, List.mem_cons_of_mem _ hc⟩

theorem sx_nil_nil : sx nil nil = .o [] := rfl

/-- On an argument free of `Ω`, `sx 0 g` is the old reading's `ex g`. -/
theorem sx_eq_ex {g : Term} (hp : Rd (psi nil g)) (hA : AllNil g) : sx nil g = ex g := by
  have hs := sumF_of_rd hp
  rcases sx_cases hs.sub hs.S01 hs.lo hs.good with ⟨_, rfl, e⟩ | ⟨_, _, _, e⟩ | ⟨_, h, _⟩ |
      ⟨_, h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
  · rw [e]; rfl
  · rw [e, ofTermFix_allNil g hA]; rfl
  · exact absurd hA h
  · exact absurd hA h
  · exact absurd h.symm t1_ne_nil
  · exact absurd h.symm t1_ne_nil

theorem ato_sx_nil {g : Term} (hp : Rd (psi nil g)) : ato (sx nil g) = ofTermFix (expoT g) := by
  rw [← ki_read (ki_all hp), ext_nil]

theorem sx_nil_ne_o_nil {f : Term} (hp : Rd (psi nil f)) (hf : f ≠ nil) : sx nil f ≠ .o [] := by
  intro h
  have := ato_sx_nil hp
  rw [h] at this
  have hA := (read_eq_nil_iff _).mp this.symm
  have hs := sumF_of_rd hp
  by_cases hAf : AllNil f
  · rw [expoT_allNil hAf] at hA; exact hf hA
  · obtain ⟨f', w, he, _, _⟩ := expoT_head (hs.good rfl) hAf
    rw [he] at hA; exact Term.noConfusion hA

theorem predBeta_of_ne {e : Ex} (he : e ≠ .o []) (k : Nat) (r : Od) :
    predBeta ((e, k) :: r) = (e, k) :: r := by
  cases e with
  | o X =>
    rw [predBetaSpec]
    cases X with
    | nil => exact absurd rfl he
    | cons _ _ => rfl
  | W _ => rfl
  | psi _ _ => rfl

theorem mem_predBeta {beta : Od} {q : Ex × Nat} (hq : q ∈ predBeta beta) :
    q ∈ beta ∨ q.1 = .o [] := by
  cases beta with
  | nil => simp [predBeta] at hq
  | cons p r =>
    obtain ⟨e, k⟩ := p
    by_cases he : e = .o []
    · subst he
      right
      simp only [predBeta, nat] at hq
      split at hq
      · simp at hq
      · simp at hq; rw [hq]
    · left; rwa [predBeta_of_ne he] at hq

/-- The summands whose trees are the digits of the unit `ψ_0(e)`. -/
def P (e : Term) : Term := if allNilB e then peelOne e else expoT e

theorem mulUnitsE_exps (x0 y : Nat) : ∀ t : Term,
    mulUnitsE x0 y t = (exps t).flatMap (fun g => [x0 + 1, y, 1] :: treeB (x0 + 2) g) := by
  intro t
  induction t with
  | nil => rfl
  | cons a g u _ _ ihu => simp [mulUnitsE, exps, ihu]

theorem exps_peelOne_sub {e g : Term} (hg : g ∈ exps (peelOne e)) : g ∈ exps e := by
  unfold peelOne at hg
  split at hg
  · rw [exps_dropLastT] at hg; exact List.mem_of_mem_dropLast hg
  · exact hg

/-- **The digits of the unit `ψ_0(e)`**, as the program lays them and as `trioE2` does. -/
theorem unit_digits {e : Term} (hp : Rd (psi nil e)) (he0 : e ≠ nil) :
    (ato (sx nil e)).isEmpty = false ∧
    units (predBeta (ato (sx nil e))) = (exps (P e)).map (sx nil) ∧
    (∀ g ∈ exps (P e), Rd (psi nil g)) := by
  have hs := sumF_of_rd hp
  have hg := hs.good rfl
  have hre := rd_ext hp
  rw [ext_nil] at hre
  have hato := ato_sx_nil hp
  refine ⟨by rw [hato]; cases h : ofTermFix (expoT e) with
    | nil =>
      exfalso
      have := (read_eq_nil_iff _).mp h
      by_cases hA : AllNil e
      · rw [expoT_allNil hA] at this; exact he0 this
      · obtain ⟨f', w, he, _, _⟩ := expoT_head hg hA
        rw [he] at this; exact Term.noConfusion this
    | cons _ _ => rfl, ?_⟩
  have hmem : ∀ g ∈ exps (expoT e), Rd (psi nil g) := fun g hg' =>
    rd_of_mem_sums (mem_sums_of_mem_exps' _ (topNil_expoT hg) g hg') hre
  by_cases hA : AllNil e
  · have hP : P e = peelOne e := by simp [P, (allNilB_iff e).mpr hA]
    rw [hP, hato, expoT_allNil hA, ofTermFix_allNil e hA]
    have hG : TrioRulesE0.Good e :=
      Googology.Trans.BMS.TrioTreeRules.good_of hA hs.OTb (by
        have := dep_le_rdT e; have := rdT_arg_lt nil e; have := hp.2.2; rw [rdT_psi] at this
        omega)
    obtain ⟨hunits, -, -⟩ := predBeta_ofTerm predBetaSpec hG he0
    rw [expoT_allNil hA] at hmem
    have hmem' : ∀ g ∈ exps (peelOne e), Rd (psi nil g) := fun g hg' =>
      hmem g (exps_peelOne_sub hg')
    refine ⟨?_, hmem'⟩
    rw [hunits]
    apply List.map_congr_left
    intro g hg'
    have hAg : AllNil g := by
      obtain ⟨a, ha⟩ := mem_exps_sums e g (exps_peelOne_sub hg')
      clear * - ha hA
      induction e with
      | nil => cases ha
      | cons c d u _ _ ihu =>
        rcases List.mem_cons.mp ha with h | h
        · injection h with _ h2; subst h2; exact hA.2.1
        · exact ihu hA.2.2 h
    exact (sx_eq_ex (hmem' g hg') hAg).symm
  · have hP : P e = expoT e := by simp [P, TrioFixStripTree.allNilB_false hA]
    rw [hP, hato]
    refine ⟨?_, hmem⟩
    obtain ⟨f, w, hew, hf1, _⟩ := expoT_head hg hA
    have hf : f ≠ nil := by
      intro h; subst h
      have := hiPart_ne_nil hg hA
      rcases Term.le_iff_lt_or_eq.mp hf1 with h | h
      · exact absurd h (not_lt_nil _)
      · exact this h
    have hre' := hre
    rw [hew] at hre'
    obtain ⟨k, L', _, hL⟩ := read_head hre'
    have hpf : Rd (psi nil f) := rd_of_mem_sums (x := cons nil f w) (p := (nil, f))
      List.mem_cons_self hre'
    rw [hew, hL, predBeta_of_ne (sx_nil_ne_o_nil hpf hf), ← hL, ← hew]
    exact units_read hre (topNil_expoT hg)

/-- **The multiply units of `trioE2`** for the unit `ψ_0(e)`: a digit and the tree of `expoT g`
for each summand `ψ_0(g)` of `P e`. -/
theorem mulUnitsE_peelE2 {e : Term} (hp : Rd (psi nil e)) (x0 y : Nat) :
    mulUnitsE x0 y (peelE2 e) =
      (exps (P e)).flatMap (fun g => [x0 + 1, y, 1] :: treeB (x0 + 2) (expoT g)) := by
  by_cases hA : AllNil e
  · rw [peelE2_of_allNil hA, mulUnitsE_exps, show P e = peelOne e by
      simp [P, (allNilB_iff e).mpr hA]]
    apply List.flatMap_congr
    intro g hg
    have hAg : AllNil g := by
      obtain ⟨a, ha⟩ := mem_exps_sums e g (exps_peelOne_sub hg)
      clear * - ha hA
      induction e with
      | nil => cases ha
      | cons c d u _ _ ihu =>
        rcases List.mem_cons.mp ha with h | h
        · injection h with _ h2; subst h2; exact hA.2.1
        · exact ihu hA.2.2 h
    rw [expoT_allNil hAg]
  · rw [peelE2_of_not hA, mulUnitsE_exps, show P e = expoT e by
      simp [P, TrioFixStripTree.allNilB_false hA]]
    have hm : ∀ s : Term, exps (TrioFixStripTree.mapArgs s) = (exps s).map expoT := by
      intro s
      induction s with
      | nil => rfl
      | cons a g t _ _ ih => simp [TrioFixStripTree.mapArgs, exps, ih]
    rw [hm, List.flatMap_map]

/-! ### The loop over the add units -/

theorem addUnitsE2_split (rp1 lastX : Nat) (pz : Bool) (i : Nat) (a e t : Term) :
    addUnitsE2 rp1 lastX pz i (cons a e t) =
      addUnitsE2 rp1 lastX pz i (cons a e nil) ++
        addUnitsE2 (nrp e rp1) (nlx e rp1 lastX pz) (e == nil) (i + 1) t := by
  by_cases he : e = nil
  · subst he
    cases pz <;> simp [addUnitsE2, nrp, nlx]
  · have : (e == nil) = false := by simp [he]
    simp [addUnitsE2, nrp, nlx, he, this]

/-- The hypothesis on one add unit. -/
def UnitHyp (f : Ex → Tup → StateM Ctx (ForInStep Tup)) : Prop :=
  ∀ e, Rd (psi nil e) → ∀ (first : Bool) (rp1 lastX : Nat) (pz : Bool) (i : Nat) (s : Ctx),
    1 ≤ i → s.regime = none → (pz = true → lastC s.cols = ⟨lastX, (i : Int) - 1, false⟩) →
    ∃ s', (f (sx nil e) ⟨first, (i : Int) - 1, pz, (rp1 : Int) - 1⟩).run s =
        (.yield ⟨false, ((i + 1 : Nat) : Int) - 1, e == nil, ((nrp e rp1 : Nat) : Int) - 1⟩, s') ∧
      s'.cols = s.cols ++ (colsOf (addUnitsE2 rp1 lastX pz i (cons nil e nil))).toArray ∧
      s'.regime = none ∧
      (e = nil → lastC s'.cols = ⟨nlx e rp1 lastX pz, ((i + 1 : Nat) : Int) - 1, false⟩)

theorem loop_unitsS (f : Ex → Tup → StateM Ctx (ForInStep Tup)) (hf : UnitHyp f) :
    ∀ t : Term, Rd t → TopNil t → ∀ (first : Bool) (rp1 lastX : Nat) (pz : Bool)
      (i : Nat) (s : Ctx),
      1 ≤ i → s.regime = none → (pz = true → lastC s.cols = ⟨lastX, (i : Int) - 1, false⟩) →
      ∃ r s', (forIn ((exps t).map (sx nil)) (⟨first, (i : Int) - 1, pz, (rp1 : Int) - 1⟩ : Tup)
          f).run s = (r, s') ∧
        s'.cols = s.cols ++ (colsOf (addUnitsE2 rp1 lastX pz i t)).toArray ∧ s'.regime = none := by
  intro t
  induction t with
  | nil =>
    intro _ _ first rp1 lastX pz i s _ hs _
    exact ⟨_, s, rfl, by simp [addUnitsE2, colsOf], hs⟩
  | cons a e t _ _ iht =>
    intro hR hT first rp1 lastX pz i s hi hs hl
    obtain ⟨rfl, hTt⟩ := hT
    have hU : Rd (psi nil e) :=
      rd_of_mem_sums (x := cons nil e t) (p := (nil, e)) List.mem_cons_self hR
    obtain ⟨s1, h1, hc1, hr1, hl1⟩ := hf e hU first rp1 lastX pz i s hi hs hl
    obtain ⟨r, s2, h2, hc2, hr2⟩ := iht (rd_tail hR) hTt false (nrp e rp1)
      (nlx e rp1 lastX pz) (e == nil) (i + 1) s1 (by omega) hr1 (fun h => hl1 (by simpa using h))
    refine ⟨r, s2, ?_, ?_, hr2⟩
    · simp only [exps, List.map_cons, List.forIn_cons]
      rw [run_bind', h1]
      push_cast at h2 ⊢
      exact h2
    · rw [hc2, hc1, addUnitsE2_split rp1 lastX pz i nil e t]
      simp [colsOf, Array.append_assoc]

theorem run_loopS (α : Term) (hR : Rd α) (hT : TopNil α)
    (f : Ex → Tup → StateM Ctx (ForInStep Tup)) (hf : UnitHyp f)
    (S : Ctx) (hS : S.regime = none) (hS0 : S.cols = #[]) :
    (StateT.run (pure PUnit.unit >>= fun _ =>
        forIn ((exps α).map (sx nil)) (⟨true, 0, false, -1⟩ : Tup) f >>= fun _ =>
          pure PUnit.unit) S).2.cols =
      (colsOf (addUnitsE2 0 0 false 1 α)).toArray := by
  obtain ⟨r, s', hrun, hc, -⟩ := loop_unitsS f hf α hR hT true 0 0 false 1 S le_rfl hS (by simp)
  have e1 : (⟨true, 0, false, -1⟩ : Tup) =
      ⟨true, ((1 : Nat) : Int) - 1, false, ((0 : Nat) : Int) - 1⟩ := rfl
  have key : (StateT.run (pure PUnit.unit >>= fun _ =>
        forIn ((exps α).map (sx nil)) (⟨true, 0, false, -1⟩ : Tup) f >>= fun _ =>
          pure PUnit.unit) S) = (PUnit.unit, s') := by
    rw [run_bind']
    show (forIn ((exps α).map (sx nil)) (⟨true, 0, false, -1⟩ : Tup) f >>= fun _ =>
      pure PUnit.unit).run S = _
    rw [run_bind', e1, hrun]
    rfl
  rw [key]
  show s'.cols = _
  rw [hc, hS0]; simp

/-! ### The add units -/

theorem rd_expoT {g : Term} (hp : Rd (psi nil g)) : Rd (expoT g) := by
  have := rd_ext hp; rwa [ext_nil] at this

theorem dep_expoT_le {g : Term} (hp : Rd (psi nil g)) : dep (expoT g) ≤ fuel := by
  have := dep_le_rdT (expoT g); have := (rd_expoT hp).2.2; simp only [fuel]; omega

/-- **`placeUnitsSt` lays `trioE2`'s add units**, on the fragment. -/
theorem placeUnitsSt_read (Mf : Od → Cols) (h1 : Mf one = B2) (α : Term) (hR : Rd α)
    (hT : TopNil α) :
    (placeUnitsSt Mf #[] (ofTermFix α) 0 (-1) none).cols =
      (colsOf (addUnitsE2 0 0 false 1 α)).toArray := by
  unfold placeUnitsSt
  simp only [Option.bind_none, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, List.drop_zero,
    units_read hR hT]
  refine run_loopS α hR hT _ ?_ _ rfl rfl
  intro e hU first rp1 lastX pz i s hi hs hl
  have hsp : ∀ c : Ctx, c.regime = s.regime → spent Mf c = false := fun c hc =>
    spent_none Mf c (hc.trans hs)
  by_cases he0 : e = nil
  · subst he0
    cases pz
    · simp (disch := exact rfl) only [run_modify_bind, run_get_bind, run_pure_bind, sx_nil_nil,
        ato, List.isEmpty_nil, hsp, Bool.and_false, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
      rw [run_pure']
      refine ⟨_, Prod.ext ?_ rfl, ?_, hs, ?_⟩
      · simp only [nrp, beq_self_eq_true, ↓reduceIte, ForInStep.yield.injEq, MProd.mk.injEq,
          true_and, and_true]
        omega
      · simp [addUnitsE2, colsOf, toCol]
        push_cast [Nat.cast_sub hi]
        ring_nf
      · intro _
        rw [lastC_append_two]
        simp [nlx]
        ring
    · have hl' := hl rfl
      simp (disch := exact rfl) only [run_modify_bind, run_get_bind, run_pure_bind, sx_nil_nil,
        ato, List.isEmpty_nil, hsp, Bool.and_false, Bool.false_eq_true, ↓reduceIte, Bool.not_true,
        Bool.and_self, hl']
      split
      · next p r h1 h2 => simp at h2
      simp only [run_pure_bind, run_pure']
      refine ⟨_, Prod.ext ?_ rfl, ?_, hs, ?_⟩
      · simp only [nrp, beq_self_eq_true, ↓reduceIte, ForInStep.yield.injEq, MProd.mk.injEq,
          true_and, and_true]
        omega
      · simp [addUnitsE2, colsOf, toCol]
      · intro _
        rw [lastC_push]
        simp [nlx]
  · obtain ⟨hE, hunits, hgood⟩ := unit_digits hU he0
    let w : Ex → List TrioRules.Col := fun a =>
      ⟨(rp1 : Int) - 1 + 1 + 1 + 1, (i : Int) - 1 + 1, true⟩ ::
        treeS fuel ((rp1 : Int) - 1 + 1 + 1 + 2) (ato a)
    have hW : (colsOf (addUnitsE2 rp1 lastX pz i (cons nil e nil))).toArray =
        #[⟨(rp1 : Int) - 1 + 1, (i : Int) - 1, false⟩,
          ⟨(rp1 : Int) - 1 + 1 + 1, (i : Int) - 1 + 1, true⟩] ++
          (((exps (P e)).map (sx nil)).flatMap w).toArray := by
      have hb : (e == nil) = false := by simp [he0]
      simp only [addUnitsE2, hb, Bool.false_eq_true, ↓reduceIte, bodyE2, mulUnitsE_peelE2 hU,
        List.append_nil]
      simp only [colsOf, List.map_cons, List.map_flatMap, List.flatMap_map]
      have hfl : (exps (P e)).flatMap
            (fun g => toCol [rp1 + 1 + 1, i, 1] :: List.map toCol (treeB (rp1 + 1 + 2) (expoT g))) =
          (exps (P e)).flatMap (fun g => w (sx nil g)) := by
        apply List.flatMap_congr
        intro g hg
        have hpg := hgood g hg
        have hx : ((rp1 : Int) - 1 + 1 + 1 + 2) = ((rp1 + 1 + 2 : Nat) : Int) := by
          push_cast; ring
        simp only [w]
        rw [ato_sx_nil hpg, hx, treeS_read fuel (expoT g) _ (rd_expoT hpg) (dep_expoT_le hpg),
          treeI_colsOf]
        simp only [colsOf, toCol, List.getD_cons_zero, List.getD_cons_succ, beq_self_eq_true]
        congr 2
        · push_cast; ring
        · ring
      rw [hfl]
      apply Array.ext'
      simp [toCol]
      omega
    refine hf_of_spec ?_ hs (fun _ h => absurd h he0)
    rw [hW]
    trioE0_step
    refine spec_get_bind fun s1 hs1 => ?_
    simp only [spent_none Mf s1 hs1, Bool.and_false, Bool.false_eq_true, ↓reduceIte, hE,
      Bool.false_and]
    repeat trioE0_step
    rw [hunits]
    refine spec_bind_last (spec_forIn _ _
      (fun r : MProd Nat (MProd Int Int) => r.snd = ⟨(rp1 : Int) - 1 + 1 + 1, (i : Int) - 1 + 1⟩) w
      ?_ _ rfl) (fun r hr => ?_)
    · intro a ha b hb
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp ha
      obtain ⟨j, x0', y'⟩ := b
      simp only [MProd.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      refine spec_get_bind fun s2 _ => spec_get_bind fun s3 hs3 => ?_
      simp only [spent_none Mf s3 hs3, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      show Spec _ _ (List.toArray (_ :: _))
      rw [List.toArray_cons]
      repeat trioE0_step
      have hpg := hgood g hg
      rw [ato_sx_nil hpg]
      refine spec_bind_last (blockFSt_spec Mf h1 fuel (expoT g) _ _ false none 0
        ⟨rd_expoT hpg, dep_expoT_le hpg, fun _ => Or.inl (topNil_expoT ((sumF_of_rd hpg).good rfl)),
          fun h => absurd h Bool.false_ne_true⟩) (fun _ _ => ?_)
      repeat trioE0_step
    · obtain ⟨j, x0', y'⟩ := r
      simp only [MProd.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      simp only [Bool.not_false, ↓reduceIte]
      repeat trioE0_step
      split
      · next p r h1 h2 => simp at h2
      repeat trioE0_step
      refine spec_pure ?_
      have hb : (e == nil) = false := by simp [he0]
      simp only [nrp, he0, ↓reduceIte, hb, ForInStep.yield.injEq, MProd.mk.injEq, true_and]
      omega

end Googology.Trans.BMS.TrioFixStripCalib

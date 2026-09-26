/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/CopyShapeChildren.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShapeItems

set_option backward.do.legacy false

/-!
# The children of an item (`CopyShape`)

`childItems_shape`: for an item of level `d + 2` in a block `i ≥ 1`, (1) what a child
guarantees about an emit (`EOK`) gives what the item guarantees, and (2) every row the
item is responsible for is a row some child is responsible for. The proof follows the four
cases of notes/03 §2.4, using (MA) in case 1, (MD) in case 2 and (MH) in case 4.
-/

set_option linter.unusedSimpArgs false

namespace OmegaY.Official.Classification.Proofs.CopyShape

open Canonical Reserve Official Descent Classification Proofs

/-- From a child's guarantee to the parent's. -/
theorem eok_parent {E : Env} {x d : Nat} {it ch : Item} {p : Emit × Origin} {j : Nat}
    (hsrc : ch.source = slot (d + 2) it.source j) (hp : EOK E x (d + 1) ch p)
    (h1 : ∀ C, it.clean = some C → ∀ c0 : Cell, cell? E.M p.2.src = some c0 →
      official c0.row ≤ C)
    (h2 : ∀ C, it.clean = some C → it.cutBottom = true → ChainCorr.cutOrigin p.2 = true)
    (h3 : it.clean = none → it.cutBottom = true → ChainCorr.cutOrigin p.2 = false →
      ∀ c0 : Cell, cell? E.M p.2.src = some c0 → ∀ ρr ρc,
        topIn E.M E.cr (d + 2) it.source = some (ρr, ρc) → official ρc.row < official c0.row)
    (h4 : ChainCorr.cutOrigin p.2 = false → ∀ c0 : Cell, cell? E.M p.2.src = some c0 →
      p.1.row = Φ E (it.cutBottom && it.clean.isNone) (d + 2) it.source it.target
        (official c0.row)) :
    EOK E x (d + 2) it p := by
  obtain ⟨hcol, hidx, c0, hc0, hreg, _⟩ := hp
  rw [hsrc] at hreg
  exact ⟨hcol, hidx, c0, hc0, Recon.RowLaw.inRegion_of_slot hreg, fun C hC => h1 C hC c0 hc0,
    h2, fun hn hb hk _ ρr ρc hρ => h3 hn hb hk c0 hc0 ρr ρc hρ, fun hk => h4 hk c0 hc0⟩

/-- The cell of an origin is determined. -/
theorem eok_cell {E : Env} {x d : Nat} {it : Item} {p : Emit × Origin} (hp : EOK E x d it p)
    {c0 : Cell} (hc0 : cell? E.M p.2.src = some c0) :
    inRegion d it.source (official c0.row) = true ∧
    (∀ C, it.clean = some C → official c0.row ≤ C) ∧
    (∀ C, it.clean = some C → it.cutBottom = true → ChainCorr.cutOrigin p.2 = true) ∧
    (it.clean = none → it.cutBottom = true → ChainCorr.cutOrigin p.2 = false → 2 ≤ d →
      ∀ ρr ρc, topIn E.M E.cr d it.source = some (ρr, ρc) → official ρc.row < official c0.row) ∧
    (ChainCorr.cutOrigin p.2 = false →
      p.1.row = Φ E (it.cutBottom && it.clean.isNone) d it.source it.target (official c0.row)) := by
  obtain ⟨_, _, c, hc, hreg, h1, h2, h3, h4⟩ := hp
  rw [hc0] at hc
  cases hc
  exact ⟨hreg, h1, h2, h3, h4⟩

theorem eok_col {E : Env} {x d : Nat} {it : Item} {p : Emit × Origin} (hp : EOK E x d it p) :
    p.2.src.column = x ∧ 1 ≤ p.2.src.index ∧ ∃ c, cell? E.M p.2.src = some c :=
  ⟨hp.1, hp.2.1, hp.2.2.choose, hp.2.2.choose_spec.1⟩

/-- The simp set for the mode `b && C.isNone` of an item. -/
theorem bmode_ff : (false && (none : Option Row).isNone) = false := rfl
theorem bmode_tf : (true && (none : Option Row).isNone) = true := rfl
theorem bmode_some (b : Bool) (C : Row) : (b && (some C).isNone) = false := by cases b <;> rfl

/-- A gap-copy item emits only gap copies. -/
theorem cut_of_cleanCut {E : Env} {x d : Nat} {S T C : Row} {o : Nat} {p : Emit × Origin}
    (hp : EOK E x d ⟨S, T, some C, o, true⟩ p) : ChainCorr.cutOrigin p.2 = true := by
  obtain ⟨_, _, _, _, _, _, h2, _⟩ := hp
  exact h2 C rfl rfl

/-- The origin row of an emit of a clean item is at most its copied row. -/
theorem le_of_clean {E : Env} {x d : Nat} {S T C : Row} {o : Nat} {b : Bool}
    {p : Emit × Origin} (hp : EOK E x d ⟨S, T, some C, o, b⟩ p) {c0 : Cell}
    (hc0 : cell? E.M p.2.src = some c0) : official c0.row ≤ C :=
  (eok_cell hp hc0).2.1 C rfl

/-- A node of the column in a region is at or below the top of the column there. -/
theorem le_top_of_node {M : Mountain} (hV : MountainValid M) {x d : Nat} {S : Row} {p : Ref}
    {c : Cell} (hpc : p.column = x) (hp1 : 1 ≤ p.index) (hc : cell? M p = some c)
    (hin : inRegion d S (official c.row) = true) {a : Ref × Cell} (ha : topIn M x d S = some a) :
    official c.row ≤ official a.2.row := by
  have hmem := mem_realNodes_of_cell' hc hp1
  rw [hpc] at hmem
  obtain ⟨hamem, _, hmax⟩ := Recon.RowLaw.topIn_spec ha
  exact Recon.official_mono (Recon.realNodes_row_one_le hV hmem)
    (Recon.realNodes_row_le hV hmem hamem (hmax _ hmem hin))

theorem topIn_ne_none_of_node {M : Mountain} {x d : Nat} {S : Row} {p : Ref} {c : Cell}
    (hpc : p.column = x) (hp1 : 1 ≤ p.index) (hc : cell? M p = some c)
    (hin : inRegion d S (official c.row) = true) : topIn M x d S ≠ none := by
  intro hn
  have hmem := mem_realNodes_of_cell' hc hp1
  rw [hpc] at hmem
  have := Recon.RowLaw.topIn_none hn _ hmem
  simp only at this
  rw [hin] at this
  cases this

theorem covRow_plain {E : Env} {d : Nat} {S T r : Row} (h : inRegion d S r = true) :
    CovRow E d ⟨S, T, none, 0, false⟩ r := by
  refine ⟨h, ?_, ?_⟩
  · intro C hC; cases hC
  · intro _ hb; cases hb

theorem covRow_clean {E : Env} {d : Nat} {S T C r : Row} {o : Nat} (h : inRegion d S r = true)
    (hC : r ≤ C) : CovRow E d ⟨S, T, some C, o, false⟩ r := by
  refine ⟨h, ?_, ?_⟩
  · intro C' hC'; cases hC'; exact ⟨rfl, hC⟩
  · intro hn; cases hn

theorem covRow_cut {E : Env} {d : Nat} {S T r : Row} (h : inRegion d S r = true)
    (hρ : ∀ ρr ρc, topIn E.M E.cr d S = some (ρr, ρc) → official ρc.row < r) :
    CovRow E d ⟨S, T, none, 0, true⟩ r := by
  refine ⟨h, ?_, ?_⟩
  · intro C hC; cases hC
  · intro _ _; exact hρ

/-- A row of a level-1 slot is the row of the slot. -/
theorem eq_of_slot_one {S r r' : Row} {j : Nat} (h : inRegion 1 (slot 2 S j) r = true)
    (h' : inRegion 1 (slot 2 S j) r' = true) : r = r' :=
  (inRegion_one h).trans (inRegion_one h').symm

theorem childItems_shape {ctx : Context} {R : Mountain} {B : Nat} {d : Nat} {it : Item}
    {cs : List Item} (hV : MountainValid ctx.source) (hi : 1 ≤ ctx.block)
    (hbnd : ∀ d T, topIn ctx.result ctx.boundary d T = topIn R B d T)
    (h : childItems ctx (d + 2) it = .ok cs)
    (hinv : ChainCorr.Inner.ItemInvC ctx.source ctx.rootColumn (d + 2) it)
    (hMA : ∀ ρr ρc, topIn ctx.source ctx.rootColumn (d + 2) it.source = some (ρr, ρc) →
      ascends ctx (some (ρr, ρc)) = .ok false →
      ∀ (q : Ref) (c : Cell), q.column = ctx.x → 1 ≤ q.index → cell? ctx.source q = some c →
        inRegion (d + 2) it.source (official c.row) = true → official c.row ≤ official ρc.row)
    (hMD : ∀ ρr ρc, topIn ctx.source ctx.rootColumn (d + 2) it.source = some (ρr, ρc) →
      ascends ctx (some (ρr, ρc)) = .ok true →
      heightOf (d + 2) (some (ρr, ρc)) <
        heightOf (d + 2) (topIn ctx.source ctx.lastColumn (d + 2) it.source))
    (hMH : ∀ C, it.clean = some C → it.cutBottom = false →
      ∀ csRef cs0 g, nodeAt ctx.source ctx.x C = some (csRef, cs0) →
        generations ctx.source ctx.rootColumn C (ctx.x + 1) csRef cs0 0 = .ok g →
        heightOf (d + 2) (topIn ctx.source ctx.rootColumn (d + 2) it.source) ≤
          heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target) + g) :
    (∀ c ∈ cs, ∀ p, EOK (Env.ofCtx ctx R B) ctx.x (d + 1) c p →
      EOK (Env.ofCtx ctx R B) ctx.x (d + 2) it p) ∧
    (∀ (p : Ref) (c : Cell), p.column = ctx.x → 1 ≤ p.index → cell? ctx.source p = some c →
      CovRow (Env.ofCtx ctx R B) (d + 2) it (official c.row) →
        ∃ ch ∈ cs, CovRow (Env.ofCtx ctx R B) (d + 1) ch (official c.row)) := by
  unfold childItems at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  generalize hrho : topIn ctx.source ctx.rootColumn (d + 2) it.source = rho at h
  split at h
  · -- the column has no node in the region
    rename_i _ hA
    obtain rfl := Except.ok.inj h
    refine ⟨by simp, ?_⟩
    intro p c hpc hp1 hc hcov
    exact absurd hA (topIn_ne_none_of_node hpc hp1 hc hcov.1)
  · rename_i _ aRef aCell hA
    -- every node of the region is at most at the height of the top of the column
    have hσtop : ∀ (p : Ref) (c : Cell), p.column = ctx.x → 1 ≤ p.index →
        cell? ctx.source p = some c → inRegion (d + 2) it.source (official c.row) = true →
        (official c.row).coeff d ≤ height (d + 2) (official aCell.row) := by
      intro p c hpc hp1 hc hin
      rw [Recon.RowLaw.height_eq]
      exact Recon.RowLaw.coeff_le_of_inRegion hin (topIn_inRegion hA)
        (le_top_of_node hV hpc hp1 hc hin hA)
    split at h
    · cases h
    · rename_i _ v hv
      split at h
      · -- case 1: the region does not ascend
        rename_i hnv
        have hv0 : v = false := by simpa using hnv
        subst hv0
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · rename_i hcond
          obtain rfl := Except.ok.inj h
          have hcl : it.clean = none := by
            cases hc : it.clean
            · rfl
            · exact absurd (Or.inl (by simp [hc])) hcond
          have hcb : it.cutBottom = false := by
            cases hb : it.cutBottom
            · rfl
            · exact absurd (Or.inr (Or.inr hb)) hcond
          refine ⟨?_, ?_⟩
          · intro ch hch p hp
            simp only [List.mem_map] at hch
            obtain ⟨j, _, rfl⟩ := hch
            refine eok_parent rfl hp ?_ ?_ ?_ ?_
            · intro C hC; rw [hcl] at hC; cases hC
            · intro C hC; rw [hcl] at hC; cases hC
            · intro _ hb; rw [hcb] at hb; cases hb
            · intro hk c0 hc0
              obtain ⟨hreg, _, _, _, hform⟩ := eok_cell hp hc0
              obtain ⟨hcolx, hidx, _⟩ := eok_col hp
              have hj : (official c0.row).coeff d = j := (Recon.RowLaw.inRegion_slot_iff.mp hreg).2
              rw [hform hk, hcb, hcl]
              simp only [Bool.false_and]
              subst hj
              cases hr : rho with
              | none =>
                  rw [hr] at hrho
                  rw [ΦF_none hrho]
              | some q =>
                  obtain ⟨ρr, ρc⟩ := q
                  rw [hr] at hrho hv
                  have hle := hMA ρr ρc hrho hv p.2.src c0 hcolx hidx hc0
                    (Recon.RowLaw.inRegion_of_slot hreg)
                  rw [ΦF_low hrho hle]
          · intro p c hpc hp1 hc hcov
            have hσ := hσtop p c hpc hp1 hc hcov.1
            refine ⟨_, List.mem_map.mpr ⟨(official c.row).coeff d,
              List.mem_range.mpr (by omega), rfl⟩, ?_⟩
            exact covRow_plain (slot_mem hcov.1)
      · -- the region ascends: the top of the root column exists
        rename_i hvt
        have hvt' : v = true := by simpa using hvt
        subst hvt'
        obtain ⟨ρr, ρc, rfl⟩ : ∃ a b, rho = some (a, b) := by
          cases rho with
          | none => simp [ascends, pure, Except.pure] at hv
          | some q => exact ⟨q.1, q.2, rfl⟩
        have hhR : heightOf (d + 2) (some (ρr, ρc)) = (official ρc.row).coeff d := by
          simp [heightOf, Recon.RowLaw.height_eq]
        have hsub := ChainCorr.Inner.topIn_slot hrho
        rw [← hhR] at hsub
        have hρreg := topIn_inRegion hrho
        have hρslot : inRegion (d + 1) (slot (d + 2) it.source (heightOf (d + 2) (some (ρr, ρc))))
            (official ρc.row) = true :=
          Recon.RowLaw.inRegion_slot_iff.mpr ⟨hρreg, hhR.symm⟩
        have hMD' := hMD ρr ρc hrho hv
        have hrhoE : topIn (Env.ofCtx ctx R B).M (Env.ofCtx ctx R B).cr (d + 2) it.source =
            some (ρr, ρc) := hrho
        have hEL : (Env.ofCtx ctx R B).lift (d + 2) it.source =
            (heightOf (d + 2) (topIn ctx.source ctx.lastColumn (d + 2) it.source) -
              heightOf (d + 2) (some (ρr, ρc))) * ctx.block := by
          unfold Env.lift
          simp only [Env.ofCtx_M, Env.ofCtx_x0, Env.ofCtx_cr, Env.ofCtx_i]
          rw [hrho]
          apply max_eq_left
          exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
        have hLint : ((heightOf (d + 2) (topIn ctx.source ctx.lastColumn (d + 2) it.source) : Int) -
            (heightOf (d + 2) (some (ρr, ρc)) : Int)) * (ctx.block : Int) =
            (((Env.ofCtx ctx R B).lift (d + 2) it.source : Nat) : Int) := by
          rw [hEL, Nat.cast_mul, Nat.cast_sub hMD'.le]
        have hL1 := (Env.ofCtx ctx R B).one_le_lift (d + 2) it.source
        have hEB : (Env.ofCtx ctx R B).hB (d + 2) it.target =
            heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target) := by
          unfold Env.hB
          rw [hbnd]
          rfl
        simp only at h
        -- the node at the height of the root top, in terms of `hR`
        have hCR : ∀ r, inRegion (d + 2) it.source r = true → r ≤ official ρc.row →
            r.coeff d ≤ heightOf (d + 2) (some (ρr, ρc)) := by
          intro r hr hle
          rw [hhR]
          exact Recon.RowLaw.coeff_le_of_inRegion hr hρreg hle
        have hRC : ∀ r, inRegion (d + 2) it.source r = true → official ρc.row < r →
            heightOf (d + 2) (some (ρr, ρc)) ≤ r.coeff d := by
          intro r hr hlt
          rw [hhR]
          exact Recon.RowLaw.coeff_le_of_inRegion hρreg hr hlt.le
        -- a row above the root top in the slot of the root top needs level `≥ 3`
        have hlev : ∀ r, inRegion (d + 1) (slot (d + 2) it.source (heightOf (d + 2) (some (ρr, ρc))))
            r = true → official ρc.row < r → 1 ≤ d := by
          intro r hr hlt
          by_contra hd
          have hd0 : d = 0 := by omega
          subst hd0
          rw [eq_of_slot_one hr hρslot] at hlt
          exact lt_irrefl _ hlt
        rw [hLint] at h
        generalize hLdef : (Env.ofCtx ctx R B).lift (d + 2) it.source = L at h hL1
        generalize hRdef : heightOf (d + 2) (some (ρr, ρc)) = hR at h hhR hsub hρslot hCR hRC hlev
        split at h
        · -- clean = none
          rename_i hcl
          split at h
          · -- case 2: lift
            rename_i hcb'
            have hcb : it.cutBottom = false := by simpa using hcb'
            have he : ((if d + 2 = 2 then (1 : Int) else 0) = 1 ∧ d = 0) ∨
                ((if d + 2 = 2 then (1 : Int) else 0) = 0 ∧ 1 ≤ d) := by
              by_cases hd : d = 0
              · left; simp [hd]
              · right; simp [hd]; omega
            generalize (if d + 2 = 2 then (1 : Int) else 0) = e at h he
            obtain rfl := Except.ok.inj h
            refine ⟨?_, ?_⟩
            · intro ch hch p hp
              simp only [List.mem_map] at hch
              obtain ⟨j, _, rfl⟩ := hch
              split_ifs at hp with h1 h2
              · -- below the root top
                refine eok_parent rfl hp (fun C hC => by rw [hcl] at hC; cases hC)
                  (fun C hC => by rw [hcl] at hC; cases hC) (fun _ hb => by rw [hcb] at hb; cases hb) ?_
                intro hk c0 hc0
                obtain ⟨hreg, -, -, -, hform⟩ := eok_cell hp hc0
                simp only at hreg hform
                have hj := (Recon.RowLaw.inRegion_slot_iff.mp hreg).2
                have hlt := ChainCorr.Inner.slot_rows_lt hreg hρslot h1
                rw [hform hk, hcb, hcl]
                simp only [bmode_ff, bmode_tf, bmode_some]
                rw [ΦF_low hrhoE hlt.le, hj]
              · -- a copy of the root row
                by_cases hjR : hR < j
                · have hdec : decide (hR < j) = true := decide_eq_true hjR
                  simp only [hdec] at hp
                  have hcut := cut_of_cleanCut hp
                  refine eok_parent rfl hp (fun C hC => by rw [hcl] at hC; cases hC)
                    (fun C hC => by rw [hcl] at hC; cases hC) (fun _ hb => by rw [hcb] at hb; cases hb) ?_
                  intro hk; rw [hcut] at hk; cases hk
                · have hjeq : j = hR := by omega
                  subst hjeq
                  have hdec : decide (j < j) = false := decide_eq_false (lt_irrefl _)
                  simp only [hdec] at hp
                  refine eok_parent rfl hp (fun C hC => by rw [hcl] at hC; cases hC)
                    (fun C hC => by rw [hcl] at hC; cases hC) (fun _ hb => by rw [hcb] at hb; cases hb) ?_
                  intro hk c0 hc0
                  obtain ⟨hreg, hcl0, -, -, hform⟩ := eok_cell hp hc0
                  simp only at hreg hform
                  have hle := hcl0 _ rfl
                  have hj := (Recon.RowLaw.inRegion_slot_iff.mp hreg).2
                  rw [hform hk, hcb, hcl]
                  simp only [bmode_ff, bmode_tf, bmode_some]
                  rw [ΦF_low hrhoE hle, hj]
              · -- a lifted slot
                by_cases hjc : (j : Int) = hR + L
                · have hσ : ((j : Int) - L).toNat = hR := by omega
                  have he0 : e = 0 ∧ 1 ≤ d := by
                    rcases he with ⟨_, _⟩ | ⟨he0, hd⟩
                    · exfalso; omega
                    · exact ⟨he0, hd⟩
                  have hdec : decide (ctx.block ≠ 0 ∧ (j : Int) = hR + L) = true :=
                    decide_eq_true ⟨by omega, hjc⟩
                  simp only [hσ, hdec] at hp
                  refine eok_parent rfl hp (fun C hC => by rw [hcl] at hC; cases hC)
                    (fun C hC => by rw [hcl] at hC; cases hC) (fun _ hb => by rw [hcb] at hb; cases hb) ?_
                  intro hk c0 hc0
                  obtain ⟨hreg, -, -, hup, hform⟩ := eok_cell hp hc0
                  simp only at hreg hform
                  have hlt := hup rfl rfl hk (by omega) ρr ρc hsub
                  have hj := (Recon.RowLaw.inRegion_slot_iff.mp hreg).2
                  have hjN : j = hR + L := by omega
                  rw [hform hk, hcb, hcl]
                  simp only [bmode_ff, bmode_tf, bmode_some]
                  rw [ΦF_mid hrhoE hlt (hj.trans hhR), hj, ← hhR, hLdef, ← hjN]
                · have hdec : decide (ctx.block ≠ 0 ∧ (j : Int) = hR + L) = false :=
                    decide_eq_false (fun h' => hjc h'.2)
                  simp only [hdec] at hp
                  have hσ : hR < ((j : Int) - L).toNat := by
                    rcases he with ⟨he1, _⟩ | ⟨he0, _⟩ <;> omega
                  refine eok_parent rfl hp (fun C hC => by rw [hcl] at hC; cases hC)
                    (fun C hC => by rw [hcl] at hC; cases hC) (fun _ hb => by rw [hcb] at hb; cases hb) ?_
                  intro hk c0 hc0
                  obtain ⟨hreg, -, -, -, hform⟩ := eok_cell hp hc0
                  simp only at hreg hform
                  have hlt := ChainCorr.Inner.slot_rows_lt hρslot hreg hσ
                  have hj := (Recon.RowLaw.inRegion_slot_iff.mp hreg).2
                  have hne : (official c0.row).coeff d ≠ (official ρc.row).coeff d := by omega
                  have hjN : j = ((j : Int) - L).toNat + L := by omega
                  rw [hform hk, hcb, hcl]
                  simp only [bmode_ff, bmode_tf, bmode_some]
                  rw [ΦF_high hrhoE hlt hne, hj, hLdef, ← hjN]
            · intro p c hpc hp1 hc hcov
              have hσ := hσtop p c hpc hp1 hc hcov.1
              have hsl := slot_mem hcov.1
              by_cases hle : official c.row ≤ official ρc.row
              · have hσR := hCR _ hcov.1 hle
                rcases Nat.lt_or_eq_of_le hσR with hlt | heq
                · refine ⟨_, List.mem_map.mpr ⟨(official c.row).coeff d,
                    List.mem_range.mpr (by omega), rfl⟩, ?_⟩
                  simp only [if_pos hlt]
                  exact covRow_plain hsl
                · refine ⟨_, List.mem_map.mpr ⟨hR, List.mem_range.mpr (by omega), rfl⟩, ?_⟩
                  have h1 : ¬ hR < hR := lt_irrefl _
                  have h2 : ((hR : Nat) : Int) < (hR : Int) + (L : Int) + e := by
                    rcases he with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
                  simp only [if_neg h1, if_pos h2, lt_self_iff_false, decide_false]
                  rw [← heq]
                  exact covRow_clean hsl hle
              · have hlt : official ρc.row < official c.row := lt_of_not_ge hle
                have hσR := hRC _ hcov.1 hlt
                rcases Nat.lt_or_eq_of_le hσR with hgt | heq
                · refine ⟨_, List.mem_map.mpr ⟨(official c.row).coeff d + L,
                    List.mem_range.mpr (by omega), rfl⟩, ?_⟩
                  have h1 : ¬ (official c.row).coeff d + L < hR := by omega
                  have h2 : ¬ (((official c.row).coeff d + L : Nat) : Int) < (hR : Int) + (L : Int) + e := by
                    rcases he with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
                  have h3 : ((((official c.row).coeff d + L : Nat) : Int) - (L : Int)).toNat =
                      (official c.row).coeff d := by omega
                  have h4 : decide (ctx.block ≠ 0 ∧ (((official c.row).coeff d + L : Nat) : Int) =
                      (hR : Int) + (L : Int)) = false := decide_eq_false (by omega)
                  simp only [if_neg h1, if_neg h2, h3, h4]
                  exact covRow_plain hsl
                · have hd1 : 1 ≤ d := hlev _ (by rw [heq]; exact hsl) hlt
                  have he0 : e = 0 := by
                    rcases he with ⟨_, _⟩ | ⟨he0, _⟩
                    · omega
                    · exact he0
                  refine ⟨_, List.mem_map.mpr ⟨hR + L, List.mem_range.mpr (by omega), rfl⟩, ?_⟩
                  have h1 : ¬ hR + L < hR := by omega
                  have h2 : ¬ ((hR + L : Nat) : Int) < (hR : Int) + (L : Int) + e := by omega
                  have h3 : (((hR + L : Nat) : Int) - (L : Int)).toNat = hR := by omega
                  have h4 : decide (ctx.block ≠ 0 ∧ ((hR + L : Nat) : Int) = (hR : Int) + (L : Int)) =
                      true := decide_eq_true ⟨by omega, by omega⟩
                  simp only [if_neg h1, if_neg h2, h3, h4]
                  rw [← heq] at hsl
                  refine covRow_cut hsl ?_
                  intro ρr' ρc' hρ'
                  simp only [Env.ofCtx_M, Env.ofCtx_cr] at hρ'
                  rw [hsub] at hρ'
                  cases hρ'
                  exact hlt
          · -- case 3: the bottom of the region is skipped
            rename_i hcb'
            have hcb : it.cutBottom = true := by simpa using hcb'
            have he : ((if d + 2 = 2 then (1 : Int) else 0) = 1 ∧ d = 0) ∨
                ((if d + 2 = 2 then (1 : Int) else 0) = 0 ∧ 1 ≤ d) := by
              by_cases hd : d = 0
              · left; simp [hd]
              · right; simp [hd]; omega
            generalize (if d + 2 = 2 then (1 : Int) else 0) = e at h he
            rw [← hEB] at h
            generalize hBdef : (Env.ofCtx ctx R B).hB (d + 2) it.target = hB at h
            have htgt : (if ctx.block = 0 then height (d + 2) (official aCell.row)
                else hB + height (d + 2) (official aCell.row)) =
                hB + height (d + 2) (official aCell.row) := if_neg (by omega)
            rw [htgt] at h
            obtain rfl := Except.ok.inj h
            refine ⟨?_, ?_⟩
            · intro ch hch p hp
              simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hch
              obtain ⟨j, ⟨_, hjR⟩, rfl⟩ := hch
              split_ifs at hp with h1
              · have hcut := cut_of_cleanCut hp
                exact eok_parent rfl hp (fun C hC => by rw [hcl] at hC; cases hC)
                  (fun C hC => by rw [hcl] at hC; cases hC)
                  (fun _ _ hk => by rw [hcut] at hk; cases hk) (fun hk => by rw [hcut] at hk; cases hk)
              · by_cases hjc : j = hB + hR
                · have hσ : j - hB = hR := by omega
                  have hσ' : j - hR = hB := by omega
                  have he0 : e = 0 ∧ 1 ≤ d := by
                    rcases he with ⟨_, _⟩ | ⟨he0, hd⟩
                    · exfalso; omega
                    · exact ⟨he0, hd⟩
                  have hdec : decide (j = hB + hR) = true := decide_eq_true hjc
                  simp only [hσ, hσ', hdec] at hp
                  refine eok_parent rfl hp (fun C hC => by rw [hcl] at hC; cases hC)
                    (fun C hC => by rw [hcl] at hC; cases hC) ?_ ?_
                  · intro _ _ hk c0 hc0 ρr' ρc' hρ'
                    obtain ⟨-, -, -, hup, -⟩ := eok_cell hp hc0
                    rw [hrhoE] at hρ'
                    cases hρ'
                    exact hup rfl rfl hk (by omega) ρr ρc hsub
                  · intro hk c0 hc0
                    obtain ⟨hreg, -, -, hup, hform⟩ := eok_cell hp hc0
                    simp only at hreg hform
                    have hj := (Recon.RowLaw.inRegion_slot_iff.mp hreg).2
                    rw [hform hk, hcb, hcl]
                    simp only [bmode_ff, bmode_tf, bmode_some]
                    rw [ΦG_mid hrhoE (hj.trans hhR), hj, hBdef]
                · have hdec : decide (j = hB + hR) = false := decide_eq_false hjc
                  simp only [hdec] at hp
                  have hσ : hR < j - hB := by
                    rcases he with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
                  refine eok_parent rfl hp (fun C hC => by rw [hcl] at hC; cases hC)
                    (fun C hC => by rw [hcl] at hC; cases hC) ?_ ?_
                  · intro _ _ hk c0 hc0 ρr' ρc' hρ'
                    obtain ⟨hreg, -, -, -, -⟩ := eok_cell hp hc0
                    rw [hrhoE] at hρ'
                    cases hρ'
                    exact ChainCorr.Inner.slot_rows_lt hρslot hreg hσ
                  · intro hk c0 hc0
                    obtain ⟨hreg, -, -, -, hform⟩ := eok_cell hp hc0
                    simp only at hreg hform
                    have hj := (Recon.RowLaw.inRegion_slot_iff.mp hreg).2
                    have hne : (official c0.row).coeff d ≠ (official ρc.row).coeff d := by omega
                    rw [hform hk, hcb, hcl]
                    simp only [bmode_ff, bmode_tf, bmode_some]
                    rw [ΦG_high hrhoE hne, hj, hBdef, ← hhR,
                      show j - hB + hB - hR = j - hR by omega]
            · intro p c hpc hp1 hc hcov
              have hσ := hσtop p c hpc hp1 hc hcov.1
              have hsl := slot_mem hcov.1
              have hlt : official ρc.row < official c.row := hcov.2.2 hcl hcb ρr ρc hrhoE
              have hσR := hRC _ hcov.1 hlt
              rcases Nat.lt_or_eq_of_le hσR with hgt | heq
              · refine ⟨_, List.mem_map.mpr ⟨(official c.row).coeff d + hB,
                  List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), by simp; omega⟩, rfl⟩, ?_⟩
                have h1 : ¬ (((official c.row).coeff d + hB : Nat) : Int) < (hB : Int) + (hR : Int) + e := by
                  rcases he with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
                have h3 : (official c.row).coeff d + hB - hB = (official c.row).coeff d := by omega
                have h4 : decide ((official c.row).coeff d + hB = hB + hR) = false :=
                  decide_eq_false (by omega)
                simp only [if_neg h1, h3, h4]
                exact covRow_plain hsl
              · have hd1 : 1 ≤ d := hlev _ (by rw [heq]; exact hsl) hlt
                have he0 : e = 0 := by
                  rcases he with ⟨_, _⟩ | ⟨he0, _⟩
                  · omega
                  · exact he0
                refine ⟨_, List.mem_map.mpr ⟨hB + hR,
                  List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), by simp⟩, rfl⟩, ?_⟩
                have h1 : ¬ ((hB + hR : Nat) : Int) < (hB : Int) + (hR : Int) + e := by omega
                have h3 : hB + hR - hB = hR := by omega
                have h4 : decide (hB + hR = hB + hR) = true := decide_eq_true rfl
                simp only [if_neg h1, h3, h4]
                rw [← heq] at hsl
                refine covRow_cut hsl ?_
                intro ρr' ρc' hρ'
                simp only [Env.ofCtx_M, Env.ofCtx_cr] at hρ'
                rw [hsub] at hρ'
                cases hρ'
                exact hlt
        · -- case 4: a copy of the root row
          rename_i C hclC
          obtain ⟨r0, ρ0, hρ0, hρ0C⟩ := hinv C hclC
          rw [hrho] at hρ0
          cases hρ0
          subst hρ0C
          split at h
          · simp [throw, throwThe, MonadExceptOf.throw] at h
          · rename_i nd hnd
            split at h
            · cases h
            · rename_i _ g hgen
              split at h
              · simp [throw, throwThe, MonadExceptOf.throw] at h
              · rename_i hcond
                have hMH' : it.cutBottom = false →
                    hR ≤ heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target) + g := by
                  intro hb
                  have := hMH _ hclC hb nd.1 nd.2 g hnd hgen
                  rw [hrho, hRdef] at this
                  exact this
                have hoff : it.cutBottom = false → it.offset = 0 := by
                  intro hb
                  by_contra hne
                  exact hcond ⟨by simp [hb], Or.inr hne⟩
                rw [← hEB] at h hMH'
                generalize hBdef : (Env.ofCtx ctx R B).hB (d + 2) it.target = hB at h hMH'
                have htgt : (if ctx.block = 0 then ((height (d + 2) (official aCell.row) : Nat) : Int)
                    else (hB : Int) + (g : Int) - (it.offset : Int)) =
                    (hB : Int) + (g : Int) - (it.offset : Int) := if_neg (by omega)
                rw [htgt] at h
                obtain rfl := Except.ok.inj h
                refine ⟨?_, ?_⟩
                · intro ch hch p hp
                  simp only [List.mem_map] at hch
                  obtain ⟨j, _, rfl⟩ := hch
                  split_ifs at hp with hb h1
                  · -- `b = 1`: gap copies only
                    have hcut := cut_of_cleanCut hp
                    refine eok_parent rfl hp ?_ (fun _ _ _ => hcut)
                      (fun hn => by rw [hclC] at hn; cases hn) (fun hk => by rw [hcut] at hk; cases hk)
                    intro C' hC' c0 hc0
                    rw [hclC] at hC'; cases hC'
                    exact le_of_clean hp hc0
                  · -- a slot below the root top
                    refine eok_parent rfl hp ?_ (fun _ _ hb' => absurd hb' hb)
                      (fun hn => by rw [hclC] at hn; cases hn) ?_
                    · intro C' hC' c0 hc0
                      rw [hclC] at hC'; cases hC'
                      obtain ⟨hreg, -⟩ := eok_cell hp hc0
                      exact (ChainCorr.Inner.slot_rows_lt hreg hρslot h1).le
                    · intro hk c0 hc0
                      obtain ⟨hreg, -, -, -, hform⟩ := eok_cell hp hc0
                      simp only at hreg hform
                      have hj := (Recon.RowLaw.inRegion_slot_iff.mp hreg).2
                      have hlt := ChainCorr.Inner.slot_rows_lt hreg hρslot h1
                      rw [hform hk, hclC]
                      simp only [bmode_ff, bmode_tf, bmode_some]
                      rw [ΦF_low hrhoE hlt.le, hj]
                  · by_cases hjR : hR < j
                    · have hdec : decide (hR < j) = true := decide_eq_true hjR
                      simp only [hdec] at hp
                      have hcut := cut_of_cleanCut hp
                      refine eok_parent rfl hp ?_ (fun _ _ hb' => absurd hb' hb)
                        (fun hn => by rw [hclC] at hn; cases hn) (fun hk => by rw [hcut] at hk; cases hk)
                      intro C' hC' c0 hc0
                      rw [hclC] at hC'; cases hC'
                      exact le_of_clean hp hc0
                    · have hjeq : j = hR := by omega
                      subst hjeq
                      have hdec : decide (j < j) = false := decide_eq_false (lt_irrefl _)
                      simp only [hdec] at hp
                      refine eok_parent rfl hp ?_ (fun _ _ hb' => absurd hb' hb)
                        (fun hn => by rw [hclC] at hn; cases hn) ?_
                      · intro C' hC' c0 hc0
                        rw [hclC] at hC'; cases hC'
                        exact le_of_clean hp hc0
                      · intro hk c0 hc0
                        obtain ⟨hreg, -, -, -, hform⟩ := eok_cell hp hc0
                        simp only at hreg hform
                        have hj := (Recon.RowLaw.inRegion_slot_iff.mp hreg).2
                        rw [hform hk, hclC]
                        simp only [bmode_ff, bmode_tf, bmode_some]
                        rw [ΦF_low hrhoE (le_of_clean hp hc0), hj]
                · intro p c hpc hp1 hc hcov
                  obtain ⟨hb, hle⟩ := hcov.2.1 _ hclC
                  have hMH2 := hMH' hb
                  have hoff0 := hoff hb
                  have hσR := hCR _ hcov.1 hle
                  have hsl := slot_mem hcov.1
                  rcases Nat.lt_or_eq_of_le hσR with hlt | heq
                  · refine ⟨_, List.mem_map.mpr ⟨(official c.row).coeff d,
                      List.mem_range.mpr (by omega), rfl⟩, ?_⟩
                    simp only [hb, Bool.false_eq_true, ↓reduceIte, if_pos hlt]
                    exact covRow_plain hsl
                  · refine ⟨_, List.mem_map.mpr ⟨hR, List.mem_range.mpr (by omega), rfl⟩, ?_⟩
                    simp only [hb, Bool.false_eq_true, ↓reduceIte, lt_self_iff_false, decide_false]
                    rw [heq] at hsl
                    exact covRow_clean hsl hle

end OmegaY.Official.Classification.Proofs.CopyShape

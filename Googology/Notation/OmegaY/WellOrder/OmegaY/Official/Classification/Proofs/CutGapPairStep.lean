/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/CutGapPairStep.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CutGapPair

set_option backward.do.legacy false

/-!
# The two columns side by side (`CutGap`)

The induction of `CutGapPair.lean` over paired items (`JPair`): `pair_run` shows that a gap
copy `p` of the column `x` (with the leg column `l`) and a non-cut emit `q` of the column `l`
are ordered by their origin rows (`POrd`), for paired items of every level.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace OmegaY.Official.Classification.Proofs.CutGap

open Canonical Reserve Official Descent Classification Proofs CopyShape

/-! ## The statements -/

/-- Paired items of the column `x` (context `cx`) and the column `l` (context `cl`). -/
def JPair (M : Mountain) (cr : Nat) (cx cl : Context) (d : Nat) (a b : Item) : Prop :=
  a = b ∨
  (∃ S T o ρr ρc, a = ⟨S, T, none, 0, false⟩ ∧ b = ⟨S, T, some (official ρc.row), o, false⟩ ∧
    topIn M cr d S = some (ρr, ρc) ∧ ascends cx (some (ρr, ρc)) = .ok false) ∨
  (∃ S T o ρr ρc, a = ⟨S, T, some (official ρc.row), o, false⟩ ∧ b = ⟨S, T, none, 0, false⟩ ∧
    topIn M cr d S = some (ρr, ρc) ∧ ascends cl (some (ρr, ρc)) = .ok false)

/-- A gap copy of the column `x` whose origin row passes the ascension test of `l`. -/
def PGood (M : Mountain) (cr : Nat) (cl : Context) (p : Emit × Origin) : Prop :=
  ChainCorr.cutOrigin p.2 = true ∧ CleanTopP M cr p ∧
  ∀ c0 : Cell, cell? M p.2.src = some c0 → ∀ ρr ρc, official ρc.row = official c0.row →
    ascends cl (some (ρr, ρc)) = .ok true

/-- The rows of `p` and `q` are ordered as their origin rows. -/
def POrd (M : Mountain) (p q : Emit × Origin) : Prop :=
  ∀ c0 c' : Cell, cell? M p.2.src = some c0 → cell? M q.2.src = some c' →
    (official c'.row ≤ official c0.row → q.1.row < p.1.row) ∧
      (official c0.row < official c'.row → p.1.row < q.1.row)

/-- The claim at the level `d`. -/
def JOK (M : Mountain) (cr : Nat) (cx cl : Context) (τ : Row) (d : Nat) : Prop :=
  ∀ a b psx psl, runItemT cx d a = .ok psx → runItemT cl d b = .ok psl →
    JPair M cr cx cl d a b → Reach cx τ d a → Reach cl τ d b →
    ChainCorr.Inner.ItemInvC M cr d a → ChainCorr.Inner.ItemInvC M cr d b →
    ∀ p ∈ psx, PGood M cr cl p → ∀ q ∈ psl, ChainCorr.cutOrigin q.2 = false → POrd M p q

/-! ## Finishing a comparison -/

theorem pord_lt {M : Mountain} {p q : Emit × Origin} {d : Nat} {T : Row} {kx kl : Nat}
    (hpT : inRegion (d + 1) (slot (d + 2) T kx) p.1.row = true)
    (hqT : inRegion (d + 1) (slot (d + 2) T kl) q.1.row = true) (hk : kx < kl)
    (hσ : ∀ c0 c' : Cell, cell? M p.2.src = some c0 → cell? M q.2.src = some c' →
      official c0.row < official c'.row) : POrd M p q := fun c0 c' h0 h1 =>
  ⟨fun h => absurd h (not_le.mpr (hσ c0 c' h0 h1)),
    fun _ => ChainCorr.Inner.slot_rows_lt hpT hqT hk⟩

theorem pord_gt {M : Mountain} {p q : Emit × Origin} {d : Nat} {T : Row} {kx kl : Nat}
    (hpT : inRegion (d + 1) (slot (d + 2) T kx) p.1.row = true)
    (hqT : inRegion (d + 1) (slot (d + 2) T kl) q.1.row = true) (hk : kl < kx)
    (hσ : ∀ c0 c' : Cell, cell? M p.2.src = some c0 → cell? M q.2.src = some c' →
      official c'.row ≤ official c0.row) : POrd M p q := fun c0 c' h0 h1 =>
  ⟨fun _ => ChainCorr.Inner.slot_rows_lt hqT hpT hk,
    fun h => absurd (hσ c0 c' h0 h1) (not_le.mpr h)⟩

/-- Origins in two different slots. -/
theorem slot_lt_of_emit {M : Mountain} {cr d : Nat} {S : Row} {a b : Item} {p q : Emit × Origin}
    {j j' : Nat} (hp : ChainCorr.Inner.EmitOK M cr (d + 1) a p)
    (hq : ChainCorr.Inner.EmitOK M cr (d + 1) b q) (ha : a.source = slot (d + 2) S j)
    (hb : b.source = slot (d + 2) S j') (hjj : j < j') :
    ∀ c0 c' : Cell, cell? M p.2.src = some c0 → cell? M q.2.src = some c' →
      official c0.row < official c'.row := by
  intro c0 c' h0 h1
  have r0 := emitOK_reg hp h0
  have r1 := emitOK_reg hq h1
  rw [ha] at r0
  rw [hb] at r1
  exact ChainCorr.Inner.slot_rows_lt r0 r1 hjj

/-- A sibling before another one: the origins are strictly ordered when `p` is a gap copy and
`q` is not. -/
theorem sep_cut_lt {M : Mountain} {cr d : Nat} {S : Row} {a b : Item}
    (hs : ChainCorr.Inner.ChildSep M cr d S a b) {p q : Emit × Origin}
    (hp : ChainCorr.Inner.EmitOK M cr (d + 1) a p) (hq : ChainCorr.Inner.EmitOK M cr (d + 1) b q)
    (hqib : b.clean.isSome = true → b.cutBottom = true → ChainCorr.cutOrigin q.2 = true)
    (hqnc : ChainCorr.cutOrigin q.2 = false)
    (hqcb : b.clean = none → b.cutBottom = true → 1 ≤ d → ∀ ρr ρc,
      topIn M cr (d + 1) b.source = some (ρr, ρc) → ∀ c, cell? M q.2.src = some c →
        official ρc.row < official c.row) :
    ∀ c0 c' : Cell, cell? M p.2.src = some c0 → cell? M q.2.src = some c' →
      official c0.row < official c'.row := by
  intro c0 c' h0 h1
  rcases hs with ⟨j, j', ha, hb, hjj⟩ | ⟨C, haC, hb⟩
  · exact slot_lt_of_emit hp hq ha hb hjj c0 c' h0 h1
  · rcases hb with ⟨hbC, hbcb⟩ | ⟨hbn, hbcb, hd1, r, ρc, htop, hrow⟩
    · rw [hqib (by simp [hbC]) hbcb] at hqnc
      cases hqnc
    · have h2 := hqcb hbn hbcb hd1 r ρc htop c' h1
      rw [hrow] at h2
      exact lt_of_le_of_lt (ChainCorr.Inner.emitOK_lower haC h0 hp).1 h2

/-- **Siblings of one list.** -/
theorem same_core {M : Mountain} {cr d : Nat} {S T : Row} {L : List Item}
    (hsep : L.Pairwise (ChainCorr.Inner.ChildSep M cr d S))
    (htgt : L.Pairwise (fun a b => ∃ k k', a.target = slot (d + 2) T k ∧
      b.target = slot (d + 2) T k' ∧ k < k'))
    {jx jl : Nat} (hjx : jx < L.length) (hjl : jl < L.length) {p q : Emit × Origin}
    (hpx : ChainCorr.Inner.EmitOK M cr (d + 1) L[jx] p)
    (hql : ChainCorr.Inner.EmitOK M cr (d + 1) L[jl] q)
    (hpT : inRegion (d + 1) L[jx].target p.1.row = true)
    (hqT : inRegion (d + 1) L[jl].target q.1.row = true)
    (hqnc : ChainCorr.cutOrigin q.2 = false)
    (hqib : L[jl].clean.isSome = true → L[jl].cutBottom = true → ChainCorr.cutOrigin q.2 = true)
    (hqcb : L[jl].clean = none → L[jl].cutBottom = true → 1 ≤ d → ∀ ρr ρc,
      topIn M cr (d + 1) L[jl].source = some (ρr, ρc) → ∀ c, cell? M q.2.src = some c →
        official ρc.row < official c.row)
    (heq : jx = jl → POrd M p q) : POrd M p q := by
  rcases Nat.lt_trichotomy jx jl with h | h | h
  · have hs := List.pairwise_iff_getElem.mp hsep jx jl hjx hjl h
    obtain ⟨k, k', hk, hk', hkk⟩ := List.pairwise_iff_getElem.mp htgt jx jl hjx hjl h
    rw [hk] at hpT
    rw [hk'] at hqT
    exact pord_lt hpT hqT hkk (sep_cut_lt hs hpx hql hqib hqnc hqcb)
  · exact heq h
  · have hs := List.pairwise_iff_getElem.mp hsep jl jx hjl hjx h
    obtain ⟨k, k', hk, hk', hkk⟩ := List.pairwise_iff_getElem.mp htgt jl jx hjl hjx h
    rw [hk'] at hpT
    rw [hk] at hqT
    refine pord_gt hpT hqT hkk ?_
    intro c0 c' h0 h1
    rcases ChainCorr.Inner.sep_rel hs hql hpx c' c0 h1 h0 with h2 | ⟨h2, _⟩
    · exact h2.le
    · exact h2.le

/-! ## The targets of the children -/

theorem kidList_tgt (M : Mountain) (cr x0 i : Nat) (R : Mountain) (B d : Nat) (it : Item)
    (asc : Bool) (n : Nat) :
    (kidList M cr x0 i R B (d + 2) it asc n).Pairwise (fun a b => ∃ k k',
      a.target = slot (d + 2) it.target k ∧ b.target = slot (d + 2) it.target k' ∧ k < k') := by
  unfold kidList
  split
  · rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp fun {j j'} h => ⟨j, j', rfl, rfl, h⟩
  · split
    · split
      · rw [List.pairwise_map]
        refine List.pairwise_lt_range.imp fun {j j'} h => ⟨j, j', ?_, ?_, h⟩ <;>
          (unfold kidC2 kidC1; split_ifs <;> rfl)
      · rw [List.pairwise_map, List.pairwise_filter]
        refine List.pairwise_lt_range.imp fun {j j'} h hj hj' => ?_
        simp only [decide_eq_true_eq] at hj hj'
        refine ⟨j - hRootOf M cr (d + 2) it, j' - hRootOf M cr (d + 2) it, ?_, ?_, by omega⟩ <;>
          (unfold kidC3; split_ifs <;> rfl)
    · rw [List.pairwise_map]
      refine List.pairwise_lt_range.imp fun {j j'} h => ⟨j, j', ?_, ?_, h⟩ <;>
        (unfold kidC4 kidC1; split_ifs <;> rfl)

/-! ## The elements of the lists -/

theorem kid_false {M : Mountain} {cr x0 i : Nat} {R : Mountain} {B d : Nat} {it : Item} {n j : Nat}
    (hj : j < (kidList M cr x0 i R B d it false n).length) :
    (kidList M cr x0 i R B d it false n)[j] = kidC1 d it j := by
  simp [kidList]

theorem kid_two {M : Mountain} {cr x0 i : Nat} {R : Mountain} {B d : Nat} {it : Item} {n j : Nat}
    (hcl : it.clean = none) (hcb : it.cutBottom = false)
    (hj : j < (kidList M cr x0 i R B d it true n).length) :
    (kidList M cr x0 i R B d it true n)[j] = kidC2 M cr x0 i d it j := by
  simp [kidList, hcl, hcb]

theorem kid_four {M : Mountain} {cr x0 i : Nat} {R : Mountain} {B d : Nat} {it : Item} {n j : Nat}
    {C : Row} (hcl : it.clean = some C)
    (hj : j < (kidList M cr x0 i R B d it true n).length) :
    (kidList M cr x0 i R B d it true n)[j] = kidC4 M cr R B d it C j := by
  simp [kidList, hcl]

/-! ## The induction -/

section Pair

variable {M R : Mountain} {x l i cr w x0 X Y B : Nat} {τ : Row}

/-- **Level 1.** A level-1 item of `x` emits a gap copy only if it is a gap-copy item; its
partner in `l` is then the same item, which emits no non-cut copy. -/
theorem pair_one
    (hbndl : ∀ d T, topIn (ctxAt M R l i cr w x0 Y).result (ctxAt M R l i cr w x0 Y).boundary d T =
      topIn R B d T) :
    JOK M cr (ctxAt M R x i cr w x0 X) (ctxAt M R l i cr w x0 Y) τ 1 := by
  intro a b psx psl hx hl hJ _ _ _ _ p hp hpg q hq hqn
  have hx' : levelOneT (ctxAt M R x i cr w x0 X) a = .ok psx := by simpa [runItemT] using hx
  obtain ⟨hacl, hacb⟩ := levelOneT_cut hx' p hp hpg.1
  rcases hJ with rfl | ⟨S, T, o, ρr, ρc, rfl, rfl, _, _⟩ | ⟨S, T, o, ρr, ρc, rfl, rfl, _, _⟩
  · have := runItemT_ibCut _ R B hbndl 0 a psl hl hacl hacb q hq
    rw [this] at hqn
    cases hqn
  · simp at hacl
  · simp at hacb

/-- The root top of a region where a column ascends exists. -/
theorem rho_of_asc {ctx : Context} {d : Nat} {S : Row}
    (h : ascends ctx (topIn ctx.source ctx.rootColumn d S) = .ok true) :
    ∃ ρr ρc, topIn ctx.source ctx.rootColumn d S = some (ρr, ρc) := by
  cases hh : topIn ctx.source ctx.rootColumn d S with
  | none => rw [hh] at h; simp [ascends, pure, Except.pure] at h
  | some q => exact ⟨q.1, q.2, rfl⟩

theorem hRoot_eq {d : Nat} {it : Item} {ρr : Ref} {ρc : Cell}
    (hρ : topIn M cr (d + 2) it.source = some (ρr, ρc)) :
    hRootOf M cr (d + 2) it = (official ρc.row).coeff d := by
  simp [hRootOf, hρ, heightOf, Recon.RowLaw.height_eq]

theorem rhoRow_eq {d : Nat} {it : Item} {ρr : Ref} {ρc : Cell}
    (hρ : topIn M cr (d + 2) it.source = some (ρr, ρc)) :
    rhoRowOf M cr (d + 2) it = official ρc.row := by
  simp [rhoRowOf, hρ]

/-- The slot of the origin of a gap copy is at most the slot of the root top. -/
theorem cut_slot_le (hV : MountainValid M) {d : Nat} {S : Row} {j : Nat} {p : Emit × Origin}
    {c0 : Cell} (hct : CleanTopP M cr p) (hcut : ChainCorr.cutOrigin p.2 = true)
    (hc0 : cell? M p.2.src = some c0)
    (hreg : inRegion (d + 1) (slot (d + 2) S j) (official c0.row) = true)
    {ρr : Ref} {ρc : Cell} (hρ : topIn M cr (d + 2) S = some (ρr, ρc)) :
    official c0.row ≤ official ρc.row ∧ j ≤ (official ρc.row).coeff d := by
  have hCle := cut_le_rootTop hV hct hcut hc0 (Recon.RowLaw.inRegion_of_slot hreg) hρ
  refine ⟨hCle, ?_⟩
  have := Recon.RowLaw.coeff_le_of_inRegion (Recon.RowLaw.inRegion_of_slot hreg)
    (topIn_inRegion hρ) hCle
  rwa [(Recon.RowLaw.inRegion_slot_iff.mp hreg).2] at this

/-- A gap copy of `row ρ` in the column `x` is impossible where `l` does not ascend at `ρ`. -/
theorem not_cut_rho {cl : Context} {p : Emit × Origin} (hpg : PGood M cr cl p) {c0 : Cell}
    (hc0 : cell? M p.2.src = some c0) {ρr : Ref} {ρc : Cell}
    (hrow : official c0.row = official ρc.row) (hn : ascends cl (some (ρr, ρc)) = .ok false) :
    False := by
  have := hpg.2.2 c0 hc0 ρr ρc hrow.symm
  rw [hn] at this
  cases this

/-- The row of the origin of an emit of a gap-copy item is its copied row. -/
theorem emitOK_ib {d : Nat} {it : Item} {C : Row} (hcl : it.clean = some C)
    (hcb : it.cutBottom = true) {p : Emit × Origin}
    (hp : ChainCorr.Inner.EmitOK M cr d it p) {c0 : Cell} (hc0 : cell? M p.2.src = some c0) :
    official c0.row = C := by
  obtain ⟨_, c, hc, _, _, h1, _⟩ := hp
  rw [hc0] at hc
  cases hc
  exact (h1 C hcl hcb).1

/-- The origin of an emit of an item that skips the bottom of its region is at or above the
root top. -/
theorem emitOK_cb {d : Nat} {it : Item} (hcl : it.clean = none) (hcb : it.cutBottom = true)
    (hd : 2 ≤ d) {p : Emit × Origin} (hp : ChainCorr.Inner.EmitOK M cr d it p) {c0 : Cell}
    (hc0 : cell? M p.2.src = some c0) {ρr : Ref} {ρc : Cell}
    (hρ : topIn M cr d it.source = some (ρr, ρc)) : official ρc.row ≤ official c0.row := by
  obtain ⟨_, c, hc, _, _, _, h2⟩ := hp
  rw [hc0] at hc
  cases hc
  exact (h2 hcl hcb hd ρr ρc hρ).1

/-- **The step of the induction.** -/
theorem pair_step (hV : MountainValid M) (hi : 1 ≤ i)
    (hbndx : ∀ d T, topIn (ctxAt M R x i cr w x0 X).result (ctxAt M R x i cr w x0 X).boundary d T =
      topIn R B d T)
    (hbndl : ∀ d T, topIn (ctxAt M R l i cr w x0 Y).result (ctxAt M R l i cr w x0 Y).boundary d T =
      topIn R B d T)
    (hMDx : FactMD (ctxAt M R x i cr w x0 X) τ) (hMDl : FactMD (ctxAt M R l i cr w x0 Y) τ)
    (d : Nat) (hIH : JOK M cr (ctxAt M R x i cr w x0 X) (ctxAt M R l i cr w x0 Y) τ (d + 1)) :
    JOK M cr (ctxAt M R x i cr w x0 X) (ctxAt M R l i cr w x0 Y) τ (d + 2) := by
  intro a b psx psl hx hl hJ hRa hRb hIa hIb p hp hpg q hq hqn
  simp only [runItemT, bind, Except.bind, pure, Except.pure] at hx hl
  split at hx
  · cases hx
  rename_i csx hchx
  split at hx
  · cases hx
  rename_i outsx houtsx
  cases hx
  split at hl
  · cases hl
  rename_i csl hchl
  split at hl
  · cases hl
  rename_i outsl houtsl
  cases hl
  obtain ⟨lx, hlx, hplx⟩ := List.mem_flatten.mp hp
  obtain ⟨jx, hjx, rfl⟩ := List.getElem_of_mem hlx
  obtain ⟨hlenx, hallx⟩ := mapM_except_spec _ _ _ houtsx
  obtain ⟨ll, hll, hqll⟩ := List.mem_flatten.mp hq
  obtain ⟨jl, hjl, rfl⟩ := List.getElem_of_mem hll
  obtain ⟨hlenl, halll⟩ := mapM_except_spec _ _ _ houtsl
  have hjxc : jx < csx.length := by omega
  have hjlc : jl < csl.length := by omega
  have hrunx := hallx jx hjxc hjx
  have hrunl := halll jl hjlc hjl
  obtain ⟨hinvx, hsepx, _⟩ := ChainCorr.Inner.childItems_order hchx hIa
  obtain ⟨hinvl, hsepl, _⟩ := ChainCorr.Inner.childItems_order hchl hIb
  have hIcx := hinvx _ (List.getElem_mem hjxc)
  have hIcl := hinvl _ (List.getElem_mem hjlc)
  have hRcx : Reach (ctxAt M R x i cr w x0 X) τ (d + 1) csx[jx] :=
    Reach.child hRa hchx (List.getElem_mem hjxc)
  have hRcl : Reach (ctxAt M R l i cr w x0 Y) τ (d + 1) csl[jl] :=
    Reach.child hRb hchl (List.getElem_mem hjlc)
  have hpx : ChainCorr.Inner.EmitOK M cr (d + 1) csx[jx] p :=
    (ChainCorr.Inner.runItemT_order _ (d + 1) _ _ hrunx hIcx).2 p hplx
  have hql : ChainCorr.Inner.EmitOK M cr (d + 1) csl[jl] q :=
    (ChainCorr.Inner.runItemT_order _ (d + 1) _ _ hrunl hIcl).2 q hqll
  have hpT := runItemT_inTarget _ d _ _ hrunx p hplx
  have hqT := runItemT_inTarget _ d _ _ hrunl q hqll
  have hqib : csl[jl].clean.isSome = true → csl[jl].cutBottom = true →
      ChainCorr.cutOrigin q.2 = true :=
    fun h1 h2 => runItemT_ibCut _ R B hbndl d _ _ hrunl h1 h2 q hqll
  have hqcb : csl[jl].clean = none → csl[jl].cutBottom = true → 1 ≤ d → ∀ ρr ρc,
      topIn M cr (d + 1) csl[jl].source = some (ρr, ρc) → ∀ c, cell? M q.2.src = some c →
        official ρc.row < official c.row := by
    intro h1 h2 hd ρr ρc hρ c hc
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    exact runItemT_cbAbove _ R B hbndl d' _ _ hrunl h1 h2 ρr ρc hρ q hqll hqn c hc
  have hIHc : JPair M cr (ctxAt M R x i cr w x0 X) (ctxAt M R l i cr w x0 Y) (d + 1)
      csx[jx] csl[jl] → POrd M p q := fun hJ' =>
    hIH _ _ _ _ hrunx hrunl hJ' hRcx hRcl hIcx hIcl p hplx hpg q hqll hqn
  obtain ⟨_, c0, hc0, _⟩ := id hpx
  rcases childItems_kid hbndx hchx with hnx | ⟨ascx, nx, hascx, heqx, hascx'⟩
  · subst hnx; simp at hjxc
  rcases childItems_kid hbndl hchl with hnl | ⟨ascl, nl, hascl, heql, hascl'⟩
  · subst hnl; simp at hjlc
  change ascends (ctxAt M R x i cr w x0 X) (topIn M cr (d + 2) a.source) = .ok ascx at hascx
  change ascends (ctxAt M R l i cr w x0 Y) (topIn M cr (d + 2) b.source) = .ok ascl at hascl
  change csx = kidList M cr x0 i R B (d + 2) a ascx nx at heqx
  change csl = kidList M cr x0 i R B (d + 2) b ascl nl at heql
  subst heqx heql
  rcases hJ with rfl | ⟨S, T, o, ρr, ρc, rfl, rfl, hρ, hnasc⟩ | ⟨S, T, o, ρr, ρc, rfl, rfl, hρ, hnasc⟩
  · -- equal items
    by_cases hsame : ascx = ascl
    · subst hsame
      rcases kidList_prefix_or (M := M) (cr := cr) (x0 := x0) (i := i) (R := R) (B := B)
          (d := d + 2) (it := a) (asc := ascx) nx nl with hpre | hpre
      · obtain ⟨hjx', hel⟩ := prefix_getElem hpre hjxc
        rw [hel] at hpx hpT hIHc
        exact same_core hsepl (kidList_tgt M cr x0 i R B d a ascx nl) hjx' hjlc hpx hql hpT hqT
          hqn hqib hqcb (fun h => by subst h; exact hIHc (Or.inl rfl))
      · obtain ⟨hjl', hel⟩ := prefix_getElem hpre hjlc
        rw [hel] at hql hqT hqib hqcb hIHc
        exact same_core hsepx (kidList_tgt M cr x0 i R B d a ascx nx) hjxc hjl' hpx hql hpT hqT
          hqn hqib hqcb (fun h => by subst h; exact hIHc (Or.inl rfl))
    · cases ascx <;> cases ascl
      · exact absurd rfl hsame
      · -- `x` does not ascend, `l` does
        obtain ⟨hacl, hacb⟩ := hascx' rfl
        obtain ⟨ρr, ρc, hρ⟩ := rho_of_asc hascl
        change topIn M cr (d + 2) a.source = some (ρr, ρc) at hρ
        have hMD := hMDl d a hRb ρr ρc hρ (by rw [← hρ]; exact hascl)
        have hnx : ascends (ctxAt M R x i cr w x0 X) (some (ρr, ρc)) = .ok false := by
          rw [← hρ]; exact hascx
        rw [kid_false hjxc] at hpx hpT hIHc
        rw [kid_two hacl hacb hjlc] at hql hqT hqib hqcb hIHc
        obtain ⟨hCle, hjxR⟩ := cut_slot_le hV hpg.2.1 hpg.1 hc0 (emitOK_reg hpx hc0) hρ
        have hL : 1 ≤ liftOf M cr x0 i (d + 2) a := by
          simp only [liftOf, hRootOf, hρ]
          simp only [ctxAt] at hMD
          have h1 : ((heightOf (d + 2) (some (ρr, ρc)) : Nat) : Int) + 1 ≤
              ((heightOf (d + 2) (topIn M x0 (d + 2) a.source) : Nat) : Int) := by
            exact_mod_cast hMD
          have h2 : (1 : Int) ≤ (i : Int) := by exact_mod_cast hi
          have h3 : (1 : Int) ≤ ((heightOf (d + 2) (topIn M x0 (d + 2) a.source) : Nat) : Int) -
              ((heightOf (d + 2) (some (ρr, ρc)) : Nat) : Int) := by omega
          have := Int.mul_le_mul h3 h2 (by decide) (by omega)
          simpa using this
        unfold kidC2 at hql hqT hqib hqcb hIHc
        rw [hRoot_eq hρ, rhoRow_eq hρ] at hql hqT hqib hqcb hIHc
        generalize liftOf M cr x0 i (d + 2) a = L at hql hqT hqib hqcb hIHc hL
        have he : ((if d + 2 = 2 then 1 else 0 : Int) = 1 ∧ d = 0) ∨
            ((if d + 2 = 2 then 1 else 0 : Int) = 0 ∧ 1 ≤ d) := by
          by_cases hd : d = 0
          · left; simp [hd]
          · right; simp [hd]; omega
        generalize (if d + 2 = 2 then 1 else 0 : Int) = e at hql hqT hqib hqcb hIHc he
        split_ifs at hql hqT hqib hqcb hIHc with h1 h2
        · rcases Nat.lt_trichotomy jx jl with h | h | h
          · exact pord_lt hpT hqT h (slot_lt_of_emit hpx hql rfl rfl h)
          · subst h; exact hIHc (Or.inl rfl)
          · exact pord_gt hpT hqT h fun c0 c' h0 h1 => (slot_lt_of_emit hql hpx rfl rfl h c' c0 h1 h0).le
        · by_cases h3 : (official ρc.row).coeff d < jl
          · exfalso
            have := hqib (by simp) (by simp [h3])
            rw [this] at hqn
            cases hqn
          · have hjl : jl = (official ρc.row).coeff d := by omega
            subst hjl
            by_cases hjx' : jx = (official ρc.row).coeff d
            · subst hjx'
              refine hIHc (Or.inr (Or.inl ⟨_, _, 0, ρr, ρc, rfl, ?_, ChainCorr.Inner.topIn_slot hρ, hnx⟩))
              simp
            · exact pord_lt hpT hqT (by omega) (slot_lt_of_emit hpx hql rfl rfl (by omega))
        · by_cases h4 : (official ρc.row).coeff d < ((jl : Int) - L).toNat
          · exact pord_lt hpT hqT (by omega) (slot_lt_of_emit hpx hql rfl rfl (by omega))
          · have hs : ((jl : Int) - L).toNat = (official ρc.row).coeff d := by omega
            have hd : 1 ≤ d := by rcases he with ⟨_, _⟩ | ⟨_, h⟩ <;> omega
            have hcb : decide (i ≠ 0 ∧ (jl : Int) = ((official ρc.row).coeff d : Int) + L) = true := by
              simp; omega
            refine pord_lt hpT hqT (by omega) ?_
            intro c0' c' h0 h1'
            have hc00 : c0' = c0 := Option.some.inj (h0.symm.trans hc0)
            subst hc00
            have := hqcb rfl hcb hd ρr ρc (by rw [hs]; exact ChainCorr.Inner.topIn_slot hρ) c' h1'
            exact lt_of_le_of_lt hCle this
      · -- `x` ascends, `l` does not
        obtain ⟨hacl, hacb⟩ := hascl' rfl
        obtain ⟨ρr, ρc, hρ⟩ := rho_of_asc hascx
        change topIn M cr (d + 2) a.source = some (ρr, ρc) at hρ
        have hMD := hMDx d a hRa ρr ρc hρ (by rw [← hρ]; exact hascx)
        have hnl : ascends (ctxAt M R l i cr w x0 Y) (some (ρr, ρc)) = .ok false := by
          rw [← hρ]; exact hascl
        rw [kid_two hacl hacb hjxc] at hpx hpT hIHc
        rw [kid_false hjlc] at hql hqT hqib hqcb hIHc
        have hL : 1 ≤ liftOf M cr x0 i (d + 2) a := by
          simp only [liftOf, hRootOf, hρ]
          simp only [ctxAt] at hMD
          have h1 : ((heightOf (d + 2) (some (ρr, ρc)) : Nat) : Int) + 1 ≤
              ((heightOf (d + 2) (topIn M x0 (d + 2) a.source) : Nat) : Int) := by
            exact_mod_cast hMD
          have h2 : (1 : Int) ≤ (i : Int) := by exact_mod_cast hi
          have h3 : (1 : Int) ≤ ((heightOf (d + 2) (topIn M x0 (d + 2) a.source) : Nat) : Int) -
              ((heightOf (d + 2) (some (ρr, ρc)) : Nat) : Int) := by omega
          have := Int.mul_le_mul h3 h2 (by decide) (by omega)
          simpa using this
        unfold kidC2 at hpx hpT hIHc
        rw [hRoot_eq hρ, rhoRow_eq hρ] at hpx hpT hIHc
        generalize liftOf M cr x0 i (d + 2) a = L at hpx hpT hIHc hL
        have he : ((if d + 2 = 2 then 1 else 0 : Int) = 1 ∧ d = 0) ∨
            ((if d + 2 = 2 then 1 else 0 : Int) = 0 ∧ 1 ≤ d) := by
          by_cases hd : d = 0
          · left; simp [hd]
          · right; simp [hd]; omega
        generalize (if d + 2 = 2 then 1 else 0 : Int) = e at hpx hpT hIHc he
        split_ifs at hpx hpT hIHc with h1 h2
        · rcases Nat.lt_trichotomy jx jl with h | h | h
          · exact pord_lt hpT hqT h (slot_lt_of_emit hpx hql rfl rfl h)
          · subst h; exact hIHc (Or.inl rfl)
          · exact pord_gt hpT hqT h fun c0 c' h0 h1 => (slot_lt_of_emit hql hpx rfl rfl h c' c0 h1 h0).le
        · by_cases h3 : (official ρc.row).coeff d < jx
          · exfalso
            exact not_cut_rho hpg hc0 (emitOK_ib rfl (by simp [h3]) hpx hc0) hnl
          · have hjx' : jx = (official ρc.row).coeff d := by omega
            subst hjx'
            rcases Nat.lt_trichotomy jl ((official ρc.row).coeff d) with h | h | h
            · exact pord_gt hpT hqT h fun c0 c' h0 h1 => (slot_lt_of_emit hql hpx rfl rfl h c' c0 h1 h0).le
            · subst h
              refine hIHc (Or.inr (Or.inr ⟨_, _, 0, ρr, ρc, ?_, rfl, ChainCorr.Inner.topIn_slot hρ, hnl⟩))
              simp
            · exact pord_lt hpT hqT h (slot_lt_of_emit hpx hql rfl rfl h)
        · exfalso
          have hreg := emitOK_reg hpx hc0
          obtain ⟨hCle, hsR⟩ := cut_slot_le hV hpg.2.1 hpg.1 hc0 hreg hρ
          have hs : ((jx : Int) - L).toNat = (official ρc.row).coeff d := by omega
          have hd : 1 ≤ d := by rcases he with ⟨_, _⟩ | ⟨_, h⟩ <;> omega
          have hcb : decide (i ≠ 0 ∧ (jx : Int) = ((official ρc.row).coeff d : Int) + L) = true := by
            simp; omega
          obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
          have hge := emitOK_cb rfl hcb (by omega) hpx hc0
            (by rw [hs]; exact ChainCorr.Inner.topIn_slot hρ)
          exact not_cut_rho hpg hc0 (le_antisymm hCle hge) hnl
      · exact absurd rfl hsame
  · -- a plain item of `x`, a clean item of `l`
    have hax : ascx = false := by
      rw [hρ, hnasc] at hascx; exact (Except.ok.inj hascx).symm
    subst hax
    cases ascl with
    | false => exact absurd (hascl' rfl).1 (by simp)
    | true =>
      rw [kid_false hjxc] at hpx hpT hIHc
      rw [kid_four rfl hjlc] at hql hqT hqib hqcb hIHc
      obtain ⟨hCle, hjxR⟩ := cut_slot_le hV hpg.2.1 hpg.1 hc0 (emitOK_reg hpx hc0) hρ
      unfold kidC4 at hql hqT hqib hqcb hIHc
      simp only [if_false, Bool.false_eq_true] at hql hqT hqib hqcb hIHc
      rw [hRoot_eq (it := ⟨S, T, some (official ρc.row), o, false⟩) hρ] at hql hqT hqib hqcb hIHc
      split_ifs at hql hqT hqib hqcb hIHc with h1
      · rcases Nat.lt_trichotomy jx jl with h | h | h
        · exact pord_lt hpT hqT h (slot_lt_of_emit hpx hql rfl rfl h)
        · subst h; exact hIHc (Or.inl rfl)
        · exact pord_gt hpT hqT h fun c0 c' h0 h1 => (slot_lt_of_emit hql hpx rfl rfl h c' c0 h1 h0).le
      · by_cases h3 : (official ρc.row).coeff d < jl
        · exfalso
          have := hqib (by simp) (by simp [h3])
          rw [this] at hqn
          cases hqn
        · have hjl : jl = (official ρc.row).coeff d := by omega
          subst hjl
          by_cases hjx' : jx = (official ρc.row).coeff d
          · subst hjx'
            refine hIHc (Or.inr (Or.inl ⟨_, _, ((((official ρc.row).coeff d : Nat) : Int) - (heightOf (d + 2) (topIn R B (d + 2) T) : Int) + (o : Int)).toNat, ρr, ρc, rfl, ?_,
              ChainCorr.Inner.topIn_slot hρ, hnasc⟩))
            simp
          · exact pord_lt hpT hqT (by omega) (slot_lt_of_emit hpx hql rfl rfl (by omega))
  · -- a clean item of `x`, a plain item of `l`
    have hal : ascl = false := by
      rw [hρ, hnasc] at hascl; exact (Except.ok.inj hascl).symm
    subst hal
    cases ascx with
    | false => exact absurd (hascx' rfl).1 (by simp)
    | true =>
      rw [kid_four rfl hjxc] at hpx hpT hIHc
      rw [kid_false hjlc] at hql hqT hqib hqcb hIHc
      unfold kidC4 at hpx hpT hIHc
      simp only [if_false, Bool.false_eq_true] at hpx hpT hIHc
      rw [hRoot_eq (it := ⟨S, T, some (official ρc.row), o, false⟩) hρ] at hpx hpT hIHc
      split_ifs at hpx hpT hIHc with h1
      · rcases Nat.lt_trichotomy jx jl with h | h | h
        · exact pord_lt hpT hqT h (slot_lt_of_emit hpx hql rfl rfl h)
        · subst h; exact hIHc (Or.inl rfl)
        · exact pord_gt hpT hqT h fun c0 c' h0 h1 => (slot_lt_of_emit hql hpx rfl rfl h c' c0 h1 h0).le
      · by_cases h3 : (official ρc.row).coeff d < jx
        · exfalso
          exact not_cut_rho hpg hc0 (emitOK_ib rfl (by simp [h3]) hpx hc0) hnasc
        · have hjx' : jx = (official ρc.row).coeff d := by omega
          subst hjx'
          rcases Nat.lt_trichotomy jl ((official ρc.row).coeff d) with h | h | h
          · exact pord_gt hpT hqT h fun c0 c' h0 h1 => (slot_lt_of_emit hql hpx rfl rfl h c' c0 h1 h0).le
          · subst h
            refine hIHc (Or.inr (Or.inr ⟨_, _, ((((official ρc.row).coeff d : Nat) : Int) - (heightOf (d + 2) (topIn R B (d + 2) T) : Int) + (o : Int)).toNat, ρr, ρc, ?_, rfl,
              ChainCorr.Inner.topIn_slot hρ, hnasc⟩))
            simp
          · exact pord_lt hpT hqT h (slot_lt_of_emit hpx hql rfl rfl h)

/-- **Paired items of every level.** -/
theorem pair_run (hV : MountainValid M) (hi : 1 ≤ i)
    (hbndx : ∀ d T, topIn (ctxAt M R x i cr w x0 X).result (ctxAt M R x i cr w x0 X).boundary d T =
      topIn R B d T)
    (hbndl : ∀ d T, topIn (ctxAt M R l i cr w x0 Y).result (ctxAt M R l i cr w x0 Y).boundary d T =
      topIn R B d T)
    (hMDx : FactMD (ctxAt M R x i cr w x0 X) τ) (hMDl : FactMD (ctxAt M R l i cr w x0 Y) τ) :
    ∀ d, JOK M cr (ctxAt M R x i cr w x0 X) (ctxAt M R l i cr w x0 Y) τ (d + 1)
  | 0 => pair_one hbndl
  | d + 1 => pair_step hV hi hbndx hbndl hMDx hMDl d (pair_run hV hi hbndx hbndl hMDx hMDl d)

end Pair

end OmegaY.Official.Classification.Proofs.CutGap

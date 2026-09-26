/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Splice/IteratedReservoirs.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Splice/IteratedReservoirs.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Splice.BlockIndices

set_option backward.do.legacy false

/-!
Finite iteration of the reservoir splice at the actual prefix widths.
Only finite atom classifications and demand key bounds are inputs at successor
steps; all label and relation invariants are constructed by reflection.
-/

namespace OmegaY.Splice

universe u
variable {Label : Type u} [LinearOrder Label]
variable {m n k : Nat}

theorem mapAtom_id (e : Atom (Label := Label) m n) :
    mapAtom id strictMono_id e = e := by
  cases e with
  | mk key parent child hpc =>
    simp only [mapAtom, id_eq]
    congr 1
    funext i
    simp [Keys.relabel]

theorem mapTop_id (e : TopAtom (Label := Label) m n) : mapTop id e = e := by
  cases e with
  | mk key parent =>
    simp only [mapTop, id_eq]
    congr 1
    funext i
    simp [Keys.relabel]

theorem fin_cast_strictMono (h : n = k) : StrictMono (Fin.cast h) := by
  intro i j hij
  exact hij

theorem ReservoirState.cast [WellFoundedLT Label]
    {G F : List (Atom (Label := Label) m n)}
    {T : List (TopAtom (Label := Label) m n)}
    {control : TopAtom (Label := Label) m n} {f : Fin n → Label} {beta : Label}
    (hState : ReservoirState G F T control f beta) (h : n = k) :
    ReservoirState
      (G.map (mapAtom (Fin.cast h) (fin_cast_strictMono h)))
      (F.map (mapAtom (Fin.cast h) (fin_cast_strictMono h)))
      (T.map (mapTop (Fin.cast h))) (mapTop (Fin.cast h) control)
      (fun i => f (Fin.cast h.symm i)) beta := by
  subst k
  have hAtom : mapAtom id strictMono_id =
      (id : Atom (Label := Label) m n → Atom (Label := Label) m n) := by
    funext e
    exact mapAtom_id e
  have hTop : mapTop id =
      (id : TopAtom (Label := Label) m n → TopAtom (Label := Label) m n) := by
    funext e
    exact mapTop_id e
  change ReservoirState (G.map (mapAtom id strictMono_id))
    (F.map (mapAtom id strictMono_id)) (T.map (mapTop id)) (mapTop id control) f beta
  rw [hAtom, hTop]
  simpa only [List.map_id, id_eq] using hState

theorem atoms_cast_roundtrip (h : n = k) (G : List (Atom (Label := Label) m k)) :
    (G.map (mapAtom (Fin.cast h.symm) (fin_cast_strictMono h.symm))).map
      (mapAtom (Fin.cast h) (fin_cast_strictMono h)) = G := by
  subst k
  have hAtom : mapAtom (Fin.cast (rfl : n = n)) (fin_cast_strictMono rfl) =
      (id : Atom (Label := Label) m n → Atom (Label := Label) m n) := by
    funext e
    exact mapAtom_id e
  simp only [hAtom, List.map_id]

/-- A cut-indexed version of the single reflection theorem. -/
theorem splice_reservoirs_at_cut [WellFoundedLT Label]
    (cut : Fin n) (G F : List (Atom (Label := Label) m n))
    (T N : List (TopAtom (Label := Label) m n))
    (control : TopAtom (Label := Label) m n)
    (H : List (Atom (Label := Label) m (width cut)))
    (f : Fin n → Label) (beta : Label)
    (hCut : control.parent = cut)
    (hState : ReservoirState G F T control f beta)
    (hCovered : DemandCovered T N)
    (hKeys : ∀ d ∈ N, Keys.templateKey d.key < Keys.templateKey control.key)
    (hClass : ∀ e ∈ H, ReservoirClassified cut G F N e) :
    ∃ h : Fin (width cut) → Label,
      (∀ i, h (moved cut i) = f i) ∧
      ReservoirState H (F.map (mapAtom (moved cut) (moved_strictMono cut)))
        (T.map (mapTop (moved cut))) (mapTop (moved cut) control) h beta := by
  subst cut
  obtain ⟨g, _hFix, _hLe, hMove, hNext⟩ :=
    splice_reservoirs G F T N control H f beta hState hCovered hKeys hClass
  exact ⟨_, hMove, hNext⟩

theorem block_cast_internal {x y : Nat} (hRoot : y < x) (b : Nat)
    (F : List (Atom (Label := Label) m (blockWidth x y b))) :
    (F.map (mapAtom (moved (blockCut hRoot b)) (moved_strictMono (blockCut hRoot b)))).map
      (mapAtom (Fin.cast (width_blockCut hRoot b)) (fin_cast_strictMono _)) =
      F.map (mapAtom (blockMoved hRoot b) (blockMoved_strictMono hRoot b)) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro e _he
  change mapAtom _ _ (mapAtom _ _ e) = _
  rw [mapAtom_comp]
  rfl

theorem block_cast_virtual {x y : Nat} (hRoot : y < x) (b : Nat)
    (T : List (TopAtom (Label := Label) m (blockWidth x y b))) :
    (T.map (mapTop (moved (blockCut hRoot b)))).map
      (mapTop (Fin.cast (width_blockCut hRoot b))) = T.map (mapTop (blockMoved hRoot b)) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro e _he
  change mapTop _ (mapTop _ e) = _
  rw [mapTop_comp]
  rfl

theorem block_cast_control {x y : Nat} (hRoot : y < x) (b : Nat)
    (control : TopAtom (Label := Label) m (blockWidth x y b)) :
    mapTop (Fin.cast (width_blockCut hRoot b))
        (mapTop (moved (blockCut hRoot b)) control) = mapTop (blockMoved hRoot b) control := by
  rw [mapTop_comp]
  rfl

/-- The next graph is reindexed only to express the local splice width.
This is a pure classification of finite atoms, independent of any labels. -/
def BlockReservoirGeometry {x y : Nat} (hRoot : y < x) (b : Nat)
    (G F : List (Atom (Label := Label) m (blockWidth x y b)))
    (N : List (TopAtom (Label := Label) m (blockWidth x y b)))
    (H : List (Atom (Label := Label) m (blockWidth x y (b + 1)))) : Prop :=
  ∀ e ∈ H.map (mapAtom (Fin.cast (width_blockCut hRoot b).symm)
      (fin_cast_strictMono _)), ReservoirClassified (blockCut hRoot b) G F N e

theorem block_reservoir_step [WellFoundedLT Label] {x y : Nat} (hRoot : y < x) (b : Nat)
    (G : List (Atom (Label := Label) m (blockWidth x y b)))
    (H : List (Atom (Label := Label) m (blockWidth x y (b + 1))))
    (F : List (Atom (Label := Label) m x))
    (T : List (TopAtom (Label := Label) m x)) (control : TopAtom (Label := Label) m x)
    (N : List (TopAtom (Label := Label) m (blockWidth x y b)))
    (f : Fin (blockWidth x y b) → Label) (beta : Label)
    (hRootControl : control.parent = ⟨y, hRoot⟩)
    (hState : ReservoirState G
      (F.map (mapAtom (blockSource hRoot b) (blockSource_strictMono hRoot b)))
      (T.map (mapTop (blockSource hRoot b))) (mapTop (blockSource hRoot b) control) f beta)
    (hCovered : DemandCovered (T.map (mapTop (blockSource hRoot b))) N)
    (hKeys : ∀ d ∈ N, Keys.templateKey d.key <
      Keys.templateKey (mapTop (blockSource hRoot b) control).key)
    (hClass : BlockReservoirGeometry hRoot b G
      (F.map (mapAtom (blockSource hRoot b) (blockSource_strictMono hRoot b))) N H) :
    ∃ h : Fin (blockWidth x y (b + 1)) → Label,
      (∀ i, h (blockMoved hRoot b i) = f i) ∧
      ReservoirState H
        (F.map (mapAtom (blockSource hRoot (b + 1)) (blockSource_strictMono hRoot (b + 1))))
        (T.map (mapTop (blockSource hRoot (b + 1))))
        (mapTop (blockSource hRoot (b + 1)) control) h beta := by
  have hCut : (mapTop (blockSource hRoot b) control).parent = blockCut hRoot b := by
    change blockSource hRoot b control.parent = _
    rw [hRootControl, blockSource_root]
  obtain ⟨g, hMove, hNext⟩ := splice_reservoirs_at_cut (blockCut hRoot b) _ _ _ N _ _ f beta
    hCut hState hCovered hKeys hClass
  let h : Fin (blockWidth x y (b + 1)) → Label :=
    fun i => g (Fin.cast (width_blockCut hRoot b).symm i)
  refine ⟨h, ?_, ?_⟩
  · intro i
    have hCast : Fin.cast (width_blockCut hRoot b).symm
        (Fin.cast (width_blockCut hRoot b) (moved (blockCut hRoot b) i)) =
        moved (blockCut hRoot b) i := Fin.ext rfl
    simpa only [h, blockMoved, hCast] using hMove i
  · have hCast := hNext.cast (width_blockCut hRoot b)
    simpa only [atoms_cast_roundtrip, block_cast_internal, block_cast_virtual,
      block_cast_control, block_internal_reserve_succ, block_virtual_reserve_succ,
      block_control_succ] using hCast

/-- Every finite number of splices has labels below the original external
bound and the full source reserves.  No successor representation is assumed. -/
theorem iterated_reservoirs [WellFoundedLT Label] {x y : Nat} (hRoot : y < x)
    (G : (b : Nat) → List (Atom (Label := Label) m (blockWidth x y b)))
    (F : List (Atom (Label := Label) m x))
    (T : List (TopAtom (Label := Label) m x)) (control : TopAtom (Label := Label) m x)
    (N : (b : Nat) → List (TopAtom (Label := Label) m (blockWidth x y b)))
    (f₀ : Fin (blockWidth x y 0) → Label) (beta : Label)
    (hRootControl : control.parent = ⟨y, hRoot⟩)
    (hInitial : ReservoirState (G 0)
      (F.map (mapAtom (blockSource hRoot 0) (blockSource_strictMono hRoot 0)))
      (T.map (mapTop (blockSource hRoot 0))) (mapTop (blockSource hRoot 0) control) f₀ beta)
    (hCovered : ∀ b, DemandCovered (T.map (mapTop (blockSource hRoot b))) (N b))
    (hKeys : ∀ b d, d ∈ N b → Keys.templateKey d.key <
      Keys.templateKey (mapTop (blockSource hRoot b) control).key)
    (hClass : ∀ b, BlockReservoirGeometry hRoot b (G b)
      (F.map (mapAtom (blockSource hRoot b) (blockSource_strictMono hRoot b))) (N b) (G (b + 1))) :
    ∀ b, ∃ f : Fin (blockWidth x y b) → Label,
      ReservoirState (G b)
        (F.map (mapAtom (blockSource hRoot b) (blockSource_strictMono hRoot b)))
        (T.map (mapTop (blockSource hRoot b))) (mapTop (blockSource hRoot b) control) f beta ∧
      (∀ i, f (blockSource hRoot b i) = f₀ (blockSource hRoot 0 i)) := by
  intro b
  induction b with
  | zero => exact ⟨f₀, hInitial, fun _ => rfl⟩
  | succ b ih =>
    obtain ⟨f, hf, hSource⟩ := ih
    obtain ⟨h, hReuse, hh⟩ := block_reservoir_step hRoot b (G b) (G (b + 1)) F T control
      (N b) f beta hRootControl hf (hCovered b) (hKeys b) (hClass b)
    refine ⟨h, hh, ?_⟩
    intro i
    rw [← blockMoved_source hRoot b i, hReuse, hSource]

end OmegaY.Splice

#print axioms OmegaY.Splice.block_reservoir_step
#print axioms OmegaY.Splice.iterated_reservoirs

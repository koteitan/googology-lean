/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/StartRootFixCmpChildren.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.StartRootFixCmpBase

set_option backward.do.legacy false

/-!
# `RootCmp`: the children of an item keep the invariant (see `StartRootFixCmpBase.lean`)

`childItems_cinv`: the children of an item keep the invariant `CInv`; `levelOneT_cmp`: the
emits of a level-`1` item compare with the root rows as their origins; `runItemT_cmp`,
`emitsT_cmp`: the same for all emits of a copied column; `rootCmp`: for every block.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.SRCmp

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr.CopyMonoProof

/-- **The children of an item keep the invariant.** -/
theorem childItems_cinv {s : List Nat} {ctx : Context} {d : Nat} {it : Item} {cs : List Item}
    (hb : Canonical.build s = .ok ctx.source)
    (hMD : 1 ≤ ctx.block → ∀ ρr ρc, topIn ctx.source ctx.rootColumn (d + 2) it.source = some (ρr, ρc) →
      ascends ctx (some (ρr, ρc)) = .ok true →
      heightOf (d + 2) (some (ρr, ρc)) <
        heightOf (d + 2) (topIn ctx.source ctx.lastColumn (d + 2) it.source))
    (hI : CInv ctx (d + 2) it) (h : childItems ctx (d + 2) it = .ok cs) :
    ∀ c ∈ cs, CInv ctx (d + 1) c := by
  unfold childItems at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  have hrt : ∀ r cl, topIn ctx.source ctx.rootColumn (d + 2) it.source = some (r, cl) →
      rootTop ctx (d + 2) it.source = some (official cl.row) := by
    intro r cl h'
    simp [rootTop, h']
  generalize hrho : topIn ctx.source ctx.rootColumn (d + 2) it.source = rho at h hrt
  split at h
  · obtain rfl := Except.ok.inj h
    simp
  · rename_i aRef aCell hA
    split at h
    · cases h
    · rename_i asc hasc
      split at h
      · -- case 1: not ascending
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · rename_i hflags
          have hcl : it.clean = none := by
            cases hc : it.clean with
            | none => rfl
            | some _ => exact absurd (Or.inl (by simp [hc])) hflags
          have hcb : it.cutBottom = false := by
            cases hb' : it.cutBottom with
            | false => rfl
            | true => exact absurd (Or.inr (Or.inr hb')) hflags
          obtain rfl := Except.ok.inj h
          intro c hc
          obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
          exact cinv_plain (sep_slot (hI.1 hcl hcb) j)
      · -- ascending
        rename_i hnasc
        have hasc_true : asc = true := by simpa using hnasc
        subst hasc_true
        obtain ⟨ρRef, ρCell, rfl⟩ : ∃ r c, rho = some (r, c) := by
          cases rho with
          | none => simp [ascends, pure, Except.pure] at hasc
          | some p => exact ⟨p.1, p.2, rfl⟩
        have hrt' := hrt ρRef ρCell rfl
        have hT := topInfo hb hrho
        have hinvC0 := rootTop_slot hrt'
        have hmd := fun h1 => hMD h1 ρRef ρCell hrho hasc
        have hHO : heightOf (d + 2) (some (ρRef, ρCell)) = (official ρCell.row).coeff d := rfl
        have hH : height (d + 2) (official ρCell.row) = (official ρCell.row).coeff d := rfl
        rw [hH] at hinvC0
        simp only [hHO] at h hmd
        generalize hhC : heightOf (d + 2) (topIn ctx.source ctx.lastColumn (d + 2) it.source) = hC
          at h hmd
        generalize heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target) = hB at h
        have he : ∀ (e : Int), (if d + 2 = 2 then (1 : Int) else 0) = e → e = 0 ∨ e = 1 := by
          intro e he
          split at he <;> omega
        have he0 : ∀ (e : Int), (if d + 2 = 2 then (1 : Int) else 0) = e → e = 0 → 1 ≤ d := by
          intro e he h0
          split at he
          · omega
          · rename_i hd; omega
        split at h
        · rename_i hcl
          split at h
          · -- case 2: lift
            rename_i hcb
            have hcb' : it.cutBottom = false := by simpa using hcb
            have hST := eq_of_sep hT (hI.1 hcl hcb')
            by_cases hblk0 : ctx.block = 0
            · have hL0 : ((hC : Int) - ((official ρCell.row).coeff d : Int)) * (ctx.block : Int)
                  = 0 := by rw [hblk0]; simp
              rw [hL0] at h
              generalize hedef : (if d + 2 = 2 then (1 : Int) else 0) = e at h
              obtain rfl := Except.ok.inj h
              rw [← hST, hblk0]
              exact case2_cinv0 hinvC0 (he e hedef) _
            · have hmd' := hmd (by omega)
              generalize hLdef : ((hC : Int) - ((official ρCell.row).coeff d : Int)) *
                (ctx.block : Int) = L at h
              have hL : 1 ≤ L := by
                rw [← hLdef]
                have h1 : (1 : Int) ≤ (hC : Int) - ((official ρCell.row).coeff d : Int) := by omega
                have h2 : (1 : Int) ≤ (ctx.block : Int) := by omega
                have := Int.mul_le_mul h1 h2 (by omega) (by omega)
                simpa using this
              generalize hedef : (if d + 2 = 2 then (1 : Int) else 0) = e at h
              obtain rfl := Except.ok.inj h
              rw [← hST]
              exact case2_cinv hT hinvC0 hL (he e hedef) (he0 e hedef) hblk0 _
          · -- case 3: cut bottom
            rename_i hcb
            have hcb' : it.cutBottom = true := by simpa using hcb
            generalize hedef : (if d + 2 = 2 then (1 : Int) else 0) = e at h
            obtain rfl := Except.ok.inj h
            exact case3_cinv hT (hI.2.1 hcl hcb').2 (he e hedef) (he0 e hedef) _
        · -- case 4: a copied root row
          rename_i C hcl
          have hCC : it.cutBottom = false → C = official ρCell.row := by
            intro hcb
            have := (hI.2.2.1 C hcl hcb).2
            rw [hrt'] at this
            exact (Option.some.inj this).symm
          split at h
          · simp [throw, throwThe, MonadExceptOf.throw] at h
          · split at h
            · cases h
            · split at h
              · simp [throw, throwThe, MonadExceptOf.throw] at h
              · obtain rfl := Except.ok.inj h
                exact case4_cinv hcl hT hinvC0 hI hCC _

end OmegaY.Official.Classification.Proofs.ChainCorr.SRCmp

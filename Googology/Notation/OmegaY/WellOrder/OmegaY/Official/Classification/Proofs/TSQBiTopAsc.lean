/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/TSQBiTopAsc.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TSQBiTopTree
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TSQRootValueParts
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.LegRowMatchInnerAsc

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# The root of `BiTopLow` and the ascension of `x` (`TSQ`, `BiTopLow`)

In the setting of `BiTopLow`: `o = (x, C)` below `τ` with its leg in the root column `c_r`,
`o⁺` below `τ`, and `pa = hAM(c_r, C)` with `pa⁺` at or above `τ`.

* `root_tau` (about `M(s)`): `pa` is the root `r = P(t⁻)` (both are the highest node of `c_r`
  below `τ`), so `τ = B(row t⁻, row pa)` with `row pa ≤ row t⁻`.
* `asc_root`: the column `x` ascends at `pa`. A node `y` of `x` has `P(y) = pa`: `y = o` when
  `row o = row pa` (`Q(o) = pa`, and `v(pa) < v(o)` by the barrier case of `RootValue`,
  `RVP.value_lt_of_barrier`, with the cap `τ`), `y = o⁻` otherwise (the father upper bound puts
  `P(o⁻)` at `pa`). The row shadow of `P(y) = pa` (`P_rowShadow`) gives the node of `x` at the
  reference row of `pa` with a path of numerical parents to the node of `c_r` there
  (`InnerRow.ascends_of_cone`).
-/

namespace OmegaY.Official.Recon.TSQ.BTL

open Canonical Classification Classification.Proofs.ChainCorr
open OmegaY.Geometry OmegaY.Geometry.Frame
open Recon.RowLaw Recon.JumpLaw Recon.TopChain

variable {M : Mountain}

/-- **The root is `pa`, and `τ = B(row t⁻, row pa)`.** -/
theorem root_tau {s : List Nat} {t : Cell} {root : Ref} (hTop : Recon.Top s M t root)
    {paN : (Frame.ofMountain M).Node} (hpac : paN.1.val = root.column)
    (hpaτ : (Frame.ofMountain M).height paN < t.row)
    (hpabar : ∀ up, (Frame.ofMountain M).upper paN = some up →
      t.row ≤ (Frame.ofMountain M).height up) :
    ∃ a : Row, (1 : Row) ≤ a ∧ (Frame.ofMountain M).height paN ≤ a ∧
      t.row = Row.B a ((Frame.ofMountain M).height paN) := by
  have hb := hTop.build
  have hN := build_normal_of_success hb
  have hO := hN.toOrdered
  have hrl := hTop.lt
  have hsz : M.size - 1 < M.size := by omega
  have htop := hTop.top
  rw [Array.getElem?_eq_getElem hsz] at htop
  simp only [Option.bind_some, Array.back?] at htop
  obtain ⟨hTi, hTt⟩ := Array.getElem?_eq_some_iff.mp htop
  let x0 : Fin (Frame.ofMountain M).width := ⟨M.size - 1, hsz⟩
  have hT3 : 3 ≤ M[M.size - 1].size := by
    by_contra hn
    have h2 : M[M.size - 1].size = 2 := by
      have := hO.length_ge_two x0
      change 2 ≤ M[M.size - 1].size at this
      omega
    have htrow : t.row = 1 := by
      rw [← hTt]
      simp only [h2]
      exact hO.bottom_row x0 (by show 1 < M[M.size - 1].size; omega)
    exact hTop.real (by rw [htrow]; exact Classification.official_one)
  have hyl : M[M.size - 1].size - 2 < (Frame.ofMountain M).length x0 := by
    show M[M.size - 1].size - 2 < M[M.size - 1].size
    omega
  let ny : (Frame.ofMountain M).Node := ⟨x0, ⟨M[M.size - 1].size - 2, hyl⟩⟩
  have hTl : M[M.size - 1].size - 1 < (Frame.ofMountain M).length x0 := by
    show M[M.size - 1].size - 1 < M[M.size - 1].size
    omega
  let nt : (Frame.ofMountain M).Node := ⟨x0, ⟨M[M.size - 1].size - 1, hTl⟩⟩
  have hyreal : Frame.Real ny := by show 0 < M[M.size - 1].size - 2; omega
  have hyt : (Frame.ofMountain M).upper ny = some nt :=
    ControlProof.upper_eq_of_index rfl
      (by show M[M.size - 1].size - 1 = M[M.size - 1].size - 2 + 1; omega)
  have hntcell : (Frame.ofMountain M).cell nt = t := hTt
  have hrawy0 : Reserve.rawParent M ⟨M.size - 1, M[M.size - 1].size - 2⟩ = some root := by
    unfold Reserve.rawParent
    rw [Array.getElem?_eq_getElem hsz]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [show M[M.size - 1].size - 2 + 1 = M[M.size - 1].size - 1 by omega, htop]
    simpa using hTop.left
  have hrawy : ((Frame.ofMountain M).upper ny).bind
      (fun v => ((Frame.ofMountain M).cell v).left) = some root :=
    (ControlProof.rawParent_ref ny).symm.trans hrawy0
  obtain ⟨nr, hPy, hnr⟩ : ∃ nr, (Frame.ofMountain M).P ny = some nr ∧ Frame.ref nr = root := by
    rw [hyt] at hrawy
    simp only [Option.bind_some] at hrawy
    obtain ⟨nr, hlk, _, _⟩ := hO.stored_valid nt root hrawy
    have hnr := Frame.lookup_spec hlk
    have hleft : ((Frame.ofMountain M).cell nt).left = some (Frame.ref nr) := by
      rw [hnr]; exact hrawy
    refine ⟨nr, ?_, hnr⟩
    rw [← hN.rawParent_eq_P hyreal]
    exact Frame.rawParent_eq_of_upper_left hyt hleft
  obtain ⟨p, hP, hrow, _, _⟩ := hN.upper_step ny nt hyreal hyt
  have hpnr : p = nr := Option.some.inj (hP.symm.trans hPy)
  subst hpnr
  have hnt : (Frame.ofMountain M).height nt = t.row := by
    show ((Frame.ofMountain M).cell nt).row = t.row; rw [hntcell]
  have hnyt : (Frame.ofMountain M).height ny < (Frame.ofMountain M).height nt :=
    ControlProof.height_lt_of_index hO rfl
      (by show M[M.size - 1].size - 2 < M[M.size - 1].size - 1; omega)
  have hph := P_height_le hO hPy
  -- `p` is `paN`
  have hcol : p.1 = paN.1 := by
    apply Fin.ext
    have := congrArg Ref.column hnr
    simp only [Frame.ref] at this
    rw [this, hpac]
  have hpτ : (Frame.ofMountain M).height p < t.row := by
    rw [← hnt]; exact lt_of_le_of_lt hph hnyt
  have hpbar : ∀ up, (Frame.ofMountain M).upper p = some up →
      t.row ≤ (Frame.ofMountain M).height up := by
    intro up hup
    rw [← hnt]
    exact father_upper_bound_nodes hN hPy hyt hup
  have hpeq : p = paN := by
    rcases Nat.lt_trichotomy p.2.val paN.2.val with h | h | h
    · exfalso
      have hlen : p.2.val + 1 < (Frame.ofMountain M).length p.1 := by
        have := paN.2.isLt
        have hl : (Frame.ofMountain M).length p.1 = (Frame.ofMountain M).length paN.1 := by
          rw [hcol]
        omega
      have hup := Recon.LowerPB.Cone.upper_of_lt hlen
      have h1 := hpbar _ hup
      have h2 : (Frame.ofMountain M).height ⟨p.1, ⟨p.2.val + 1, hlen⟩⟩ ≤
          (Frame.ofMountain M).height paN :=
        ControlProof.height_le_of_index hO hcol (by show p.2.val + 1 ≤ paN.2.val; omega)
      exact absurd (lt_of_le_of_lt (h1.trans h2) hpaτ) (lt_irrefl _)
    · exact ControlProof.node_eq_of_index hcol h
    · exfalso
      have hlen : paN.2.val + 1 < (Frame.ofMountain M).length paN.1 := by
        have := p.2.isLt
        have hl : (Frame.ofMountain M).length p.1 = (Frame.ofMountain M).length paN.1 := by
          rw [hcol]
        omega
      have hup := Recon.LowerPB.Cone.upper_of_lt hlen
      have h1 := hpabar _ hup
      have h2 : (Frame.ofMountain M).height ⟨paN.1, ⟨paN.2.val + 1, hlen⟩⟩ ≤
          (Frame.ofMountain M).height p :=
        ControlProof.height_le_of_index hO hcol.symm (by show paN.2.val + 1 ≤ p.2.val; omega)
      exact absurd (lt_of_le_of_lt (h1.trans h2) hpτ) (lt_irrefl _)
  subst hpeq
  refine ⟨(Frame.ofMountain M).height ny, one_le_height hO hyreal, hph, ?_⟩
  rw [← hnt, hrow]

/-- **`x` ascends at `pa`.** -/
theorem asc_root {s : List Nat} (hb : Canonical.build s = .ok M) {R : Mountain} {root : Ref}
    {i x : Nat} {τ : Row} {oN opN paN : (Frame.ofMountain M).Node}
    (hox : oN.1.val = x) (hoR : Real oN) (hup : (Frame.ofMountain M).upper oN = some opN)
    (hopτ : (Frame.ofMountain M).height opN < τ) {l : Ref}
    (hl : ((Frame.ofMountain M).cell oN).left = some l) (hlc : l.column = root.column)
    (hpa : Reserve.highestAtMost M l.column ((Frame.ofMountain M).height oN) =
      some (Frame.ref paN))
    (hpabar : ∀ up, (Frame.ofMountain M).upper paN = some up →
      τ ≤ (Frame.ofMountain M).height up) :
    ascends (colCtx M R root i x) (some (Frame.ref paN, (Frame.ofMountain M).cell paN)) =
      .ok true := by
  have hN := build_normal_of_success hb
  have hO := hN.toOrdered
  obtain ⟨paN', hpaN', hpac, hpaR, hpaH⟩ := highestIn_of_highestAtMost hpa
  have hpe : paN' = paN := TSQ.ref_inj' hpaN'
  subst hpe
  have hpac' : paN'.1.val = root.column := by rw [hpac, hlc]
  have hoop : (Frame.ofMountain M).height oN < (Frame.ofMountain M).height opN := by
    obtain ⟨hc1, hc2⟩ := upper_spec hup
    exact ControlProof.height_lt_of_index hO hc1.symm (by omega)
  -- a node `y` of `x` with `P(y) = pa`
  obtain ⟨y, hyR, hyc, hPy⟩ : ∃ y : (Frame.ofMountain M).Node, Real y ∧ y.1 = oN.1 ∧
      (Frame.ofMountain M).P y = some paN' := by
    rcases lt_or_eq_of_le hpaH.1 with hlt | heq
    · obtain ⟨v, hvR, hvu, hvc, _⟩ := real_lower_of_height_lt hO hpaR hlt
      obtain ⟨p, hP, _, _, hleft⟩ := hN.upper_step v oN hvR hvu
      have hlp : l = Frame.ref p := Option.some.inj (hl.symm.trans hleft)
      have hpc : p.1 = paN'.1 := by
        apply Fin.ext
        have := congrArg Ref.column hlp
        simp only [Frame.ref] at this
        rw [← this, ← hpac]
      have hvo : (Frame.ofMountain M).height v < (Frame.ofMountain M).height oN := by
        obtain ⟨hc1, hc2⟩ := upper_spec hvu
        exact ControlProof.height_lt_of_index hO hc1.symm (by omega)
      have hph : (Frame.ofMountain M).height p ≤ (Frame.ofMountain M).height oN :=
        (P_height_le hO hP).trans hvo.le
      have hple := hpaH.2 p hpc hph
      have hpeq : p = paN' := by
        rcases lt_or_eq_of_le hple with h | h
        · exfalso
          have hlen : p.2.val + 1 < (Frame.ofMountain M).length p.1 := by
            have := paN'.2.isLt
            have hl' : (Frame.ofMountain M).length p.1 = (Frame.ofMountain M).length paN'.1 := by
              rw [hpc]
            omega
          have hpp := Recon.LowerPB.Cone.upper_of_lt hlen
          have h1 := father_upper_bound_nodes hN hP hvu hpp
          have h2 : (Frame.ofMountain M).height ⟨p.1, ⟨p.2.val + 1, hlen⟩⟩ ≤
              (Frame.ofMountain M).height paN' :=
            ControlProof.height_le_of_index hO hpc (by show p.2.val + 1 ≤ paN'.2.val; omega)
          exact absurd (lt_of_le_of_lt (h1.trans h2) hlt) (lt_irrefl _)
        · exact ControlProof.node_eq_of_index hpc h
      subst hpeq
      exact ⟨v, hvR, hvc, hP⟩
    · -- `row o = row pa`: `Q(o) = pa`, and `v(pa) < v(o)` by the barrier case
      obtain ⟨q, hQ, hq⟩ := ControlProof.Q_of_highestAtMost hO hl hpa
      have hqe : q = paN' := TSQ.ref_inj' hq
      subst hqe
      obtain ⟨p, hP, _, _, _⟩ := hN.upper_step oN opN hoR hup
      have hcap : Row.bump ((Frame.ofMountain M).height q) 0 < τ := by
        rw [heq]
        exact lt_of_le_of_lt (Recon.LowerPB.LiftLegPf.bump0_le_of_lt hoop) hopτ
      have hval := RVP.value_lt_of_barrier hN hP hQ heq heq (.refl _) hpaR hpabar hcap
        (by rw [aboveHeight_of_upper hup]; exact hopτ)
      refine ⟨oN, hoR, rfl, (P_iff hO).mpr ⟨q, hQ, .here (hO.real_positive q hpaR) hval⟩⟩
  -- the node of `c_r` at the reference row of `pa`
  obtain ⟨z, hzR, hzc, hzh, hZ⟩ : ∃ z : (Frame.ofMountain M).Node, Real z ∧ z.1 = paN'.1 ∧
      (Frame.ofMountain M).height z ≤ (Frame.ofMountain M).height paN' ∧
      official ((Frame.ofMountain M).cell z).row =
        referenceRow (official ((Frame.ofMountain M).cell paN').row) := by
    by_cases h0 : 0 < (official ((Frame.ofMountain M).cell paN').row).coeff 0
    · -- the node below `pa`
      have hpa1 : (1 : Row) < (Frame.ofMountain M).height paN' := by
        rcases lt_or_eq_of_le (one_le_height hO hpaR) with h | h
        · exact h
        · exfalso
          have : ((Frame.ofMountain M).cell paN').row = 1 := h.symm
          rw [this, Classification.official_one] at h0
          simp at h0
      have hlen1 : 1 < (Frame.ofMountain M).length paN'.1 := by
        have := hO.length_ge_two paN'.1; omega
      let bN : (Frame.ofMountain M).Node := ⟨paN'.1, ⟨1, hlen1⟩⟩
      have hbR : Real bN := by show 0 < 1; omega
      have hbh : (Frame.ofMountain M).height bN = 1 := hO.bottom_row paN'.1 hlen1
      obtain ⟨z, hzR, hzu, hzc, _⟩ := real_lower_of_height_lt (u := paN') hO hbR
        (by rw [hbh]; exact hpa1)
      obtain ⟨p', hP', hrowB, _, _⟩ := hN.upper_step z paN' hzR hzu
      have hz1 : (1 : Row) ≤ (Frame.ofMountain M).height z := one_le_height hO hzR
      have hjump : Row.jump ((Frame.ofMountain M).height z) ((Frame.ofMountain M).height p') = 0 := by
        by_contra hne
        have hpos : 0 < Row.jump ((Frame.ofMountain M).height z)
            ((Frame.ofMountain M).height p') := Nat.pos_of_ne_zero hne
        change 0 < (official ((Frame.ofMountain M).height paN')).coeff 0 at h0
        rw [hrowB, Row.B, Recon.RowLaw.official_bump hz1, Recon.RowLaw.bump_coeff_low hpos] at h0
        exact lt_irrefl _ h0
      have hph : (Frame.ofMountain M).height p' = (Frame.ofMountain M).height z :=
        (Row.jump_eq_zero.mp hjump).symm
      have hrow0 : (Frame.ofMountain M).height paN' = Row.bump ((Frame.ofMountain M).height z) 0 := by
        rw [hrowB, hph, Row.B_self]
      refine ⟨z, hzR, hzc, ?_, ?_⟩
      · rw [hrow0]; exact (Row.lt_bump _ _).le
      · apply TSQ.bump0_inj
        rw [Recon.RowLaw.referenceRow_bump h0]
        show Row.bump (official ((Frame.ofMountain M).height z)) 0 =
          official ((Frame.ofMountain M).height paN')
        rw [hrow0, Recon.RowLaw.official_bump hz1]
    · refine ⟨paN', hpaR, rfl, le_rfl, ?_⟩
      unfold referenceRow; rw [if_neg h0]
  -- the row shadow of `P(y) = pa`
  obtain ⟨v, hvR, hvc, _, hvh, hvpath⟩ := P_rowShadow hN hPy z hzR hzc hzh
  refine Classification.Proofs.CopyShape.InnerRow.ascends_of_cone hb rfl rfl hvR ?_ hvpath
    hvh.symm ?_ ?_
  · show v.1.val = x
    rw [hvc, hyc, hox]
  · rw [hzc, hpac']; rfl
  · have : ((Frame.ofMountain M).cell v).row = ((Frame.ofMountain M).cell z).row := hvh
    rw [this, hZ]

end OmegaY.Official.Recon.TSQ.BTL

#print axioms OmegaY.Official.Recon.TSQ.BTL.root_tau
#print axioms OmegaY.Official.Recon.TSQ.BTL.asc_root

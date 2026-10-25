import Googology.Trans.PoR.InaccPsi.R2.TsRep
import Googology.Trans.PoR.InaccPsi.R2.LeEMove
import Googology.Trans.PoR.InaccPsi.R2.MxAtB

/-!
# `B_n` on the atoms `F_β(y)` of countable level and countable offset

`B_n = Bc.bcB S n`, `c_{n+1} = L(n+2) = Bc.bcC S (n + 1)`, `F_β = Rh.rhF β`, `w_β = Ω₂^β = Le.leWe β`,
`ψ_{Ω₂}(α) = S.psi α Ω₂`.  An atom `F_β(Ω₁ + 1 + D)` with `1 ≤ β < Ω₁`, `D < Ω₁` is the collapse
`ψ_{Ω₂}(Ω₂^β·(1 + D))` (`Ts.ts_psiU_mul`; every `d ≤ D` is countable, so below `F_β(Ω₁ + 1 + d)`); `B_n` moves the
collapse by `Mx.mxB_atom` and the argument by `Le.leB_We`:

* `ts_valid_ctbl` (validity of every countable `D` over `c = Ω₁ + 1`), `ts_atom_ctbl` (**`F_β(Ω₁ + 1 + D) =
  ψ_{Ω₂}(Ω₂^β·(1 + D))` for `1 ≤ β < Ω₁`, `D < Ω₁`**);
* `tsB_arg` (`B_n(Ω₂^β·(1 + D)) = Ω₂^{B_n β}·(1 + B_n D)` for `β, D < c_{n+1}`, `1 ≤ β`), `tsB_psiU`
  (**`B_n(ψ_{Ω₂}(Ω₂^β·(1 + D))) = ψ_{Ω₂}(Ω₂^{B_n β}·(1 + B_n D))`**);
* `tsB_atom` (**`B_n(F_β(Ω₁ + 1 + D)) = F_{B_n β}(Ω₁ + 1 + B_n D)`** for `1 ≤ β < c_{n+1}`, `D < c_{n+1}`; the atom is
  in the domain of `B_n`), `tsB_atom_lev` (`1 ≤ B_n β < Ω₁`);
* `tsB_atom_gen` (**every value `F_β(y)` in `(Ω₁, ψ_{Ω₂}(B))` is `ψ_{Ω₂}(e)` for its own argument `e` (`Ω₂^β ∣ e`), and
  `B_n(F_β(y)) = ψ_{Ω₂}(B_n e)` once `e` is in the domain of `B_n`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ts

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Mv

variable {S : InaccSeq.{0}}

/-- Every countable `D` is valid over `c = Ω₁ + 1`: `d < F_β(Ω₁ + 1 + d)` for `d ≤ D < Ω₁`. -/
theorem ts_valid_ctbl {β D : Ordinal.{0}} (hD : D < Om 1) : ∀ d, d ≤ D → d < rhF β (Om 1 + 1 + d) :=
  fun _ hd => (hd.trans_lt hD).trans_le ((le_self_add.trans le_self_add).trans (rhF_le_self β _))

/-- **`F_β(Ω₁ + 1 + D) = ψ_{Ω₂}(Ω₂^β·(1 + D))`** for `1 ≤ β < Ω₁`, `D < Ω₁`. -/
theorem ts_atom_ctbl {β D : Ordinal.{0}} (h1 : 1 ≤ β) (hβ : β < Om 1) (hD : D < Om 1) :
    rhF β (Om 1 + 1 + D) = S.psi (leWe β * (1 + D)) (Om (1 + 1)) :=
  ((ts_psiU_mul (S := S) (hβ.trans (ts_Om1_lt_psi _)) (ts_psiU_small h1 hβ).symm
    (hD.trans ts_Om1_lt_Om2) (ts_valid_ctbl hD)).2).symm

/-- The class `x < c_{n+1}`: in the domain of `B_n`, closed under `log` and the tail, below `Ω₂`. -/
theorem ts_ctbl_class (n : ℕ) :
    (∀ x, x < Bc.bcC S (n + 1) → MvD S x) ∧
      (∀ x, x < Bc.bcC S (n + 1) → x ≠ 0 →
        log ω x < Bc.bcC S (n + 1) ∧ x - ω ^ log ω x < Bc.bcC S (n + 1)) ∧
      (∀ x, x < Bc.bcC S (n + 1) → x < Om (1 + 1)) := by
  have hcL : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hc1 : Bc.bcC S (n + 1) < Om 1 := hcL.trans (InaccSeq.psi_lt Low.InR_Om_one _)
  refine ⟨fun x hx => mvD_of_lt (hx.trans hcL), fun x hx _ => ⟨(log_le_self _ _).trans_lt hx,
    (Ordinal.sub_le_self _ _).trans_lt hx⟩, fun x hx => (hx.trans hc1).trans ts_Om1_lt_Om2⟩

/-- **`B_n(Ω₂^β·(1 + D)) = Ω₂^{B_n β}·(1 + B_n D)`** for `1 ≤ β < c_{n+1}`, `D < c_{n+1}`. -/
theorem tsB_arg {n : ℕ} {β D : Ordinal.{0}} (h1 : 1 ≤ β) (hβc : β < Bc.bcC S (n + 1))
    (hDc : D < Bc.bcC S (n + 1)) :
    MvD S (leWe β * (1 + D)) ∧ Bc.bcB S n (leWe β * (1 + D)) = leWe (Bc.bcB S n β) * (1 + Bc.bcB S n D) := by
  obtain ⟨hPD, hPdec, hPW⟩ := ts_ctbl_class (S := S) n
  have hcS : SC (Bc.bcC S (n + 1)) := Lw.lw_L_SC S _
  have h1c : 1 + D < Bc.bcC S (n + 1) := (Lq.lq_SC_indec hcS).add_lt (Gg.gg_one_lt_of_SC hcS) hDc
  obtain ⟨-, -, hD, hB⟩ := leB_We (n := n) (fun x => x < Bc.bcC S (n + 1)) hPD hPdec hPW hβc h1 h1c
  obtain ⟨-, hB1⟩ := mvB_add (k := n) (hPD 1 (Gg.gg_one_lt_of_SC hcS)) (hPD D hDc)
  rw [hB1, Mw.mwB_one] at hB
  exact ⟨hD, hB⟩

/-- **`B_n(ψ_{Ω₂}(Ω₂^β·(1 + D))) = ψ_{Ω₂}(Ω₂^{B_n β}·(1 + B_n D))`** for `1 ≤ β < c_{n+1}`, `D < c_{n+1}`; the
collapse is in the domain of `B_n`. -/
theorem tsB_psiU {n : ℕ} {β D : Ordinal.{0}} (h1 : 1 ≤ β) (hβc : β < Bc.bcC S (n + 1))
    (hDc : D < Bc.bcC S (n + 1)) :
    MvD S (S.psi (leWe β * (1 + D)) (Om (1 + 1))) ∧
      Bc.bcB S n (S.psi (leWe β * (1 + D)) (Om (1 + 1))) =
        S.psi (leWe (Bc.bcB S n β) * (1 + Bc.bcB S n D)) (Om (1 + 1)) := by
  obtain ⟨hD, hB⟩ := tsB_arg (S := S) h1 hβc hDc
  have hcS : SC (Bc.bcC S (n + 1)) := Lw.lw_L_SC S _
  have hc1 : Bc.bcC S (n + 1) < Om 1 := (Bc.bcC_lt S (n + 1)).trans (InaccSeq.psi_lt Low.InR_Om_one _)
  set A := leWe β * (1 + D) with hA
  have hcψ : Bc.bcC S (n + 1) < S.psi A (Om (1 + 1)) := hc1.trans (ts_Om1_lt_psi _)
  have h1c : 1 + D < Bc.bcC S (n + 1) := (Lq.lq_SC_indec hcS).add_lt (Gg.gg_one_lt_of_SC hcS) hDc
  have hown : A ∈ S.CSet A (S.psi A (Om (1 + 1))) := tsU_mul_mem (hβc.trans hcψ) (h1c.trans hcψ)
  obtain ⟨hDψ, hBψ⟩ := Mx.mxB_atom (n := n) hD hown
  rw [hB] at hBψ
  exact ⟨hDψ, hBψ⟩

/-- `1 ≤ B_n β < Ω₁` for `1 ≤ β < c_{n+1}`. -/
theorem tsB_atom_lev {n : ℕ} {β : Ordinal.{0}} (h1 : 1 ≤ β) (hβc : β < Bc.bcC S (n + 1)) :
    1 ≤ Bc.bcB S n β ∧ Bc.bcB S n β < Om 1 := by
  obtain ⟨hPD, -, -⟩ := ts_ctbl_class (S := S) n
  have hcS : SC (Bc.bcC S (n + 1)) := Lw.lw_L_SC S _
  have h1D' : MvD S (1 : Ordinal.{0}) := hPD 1 (Gg.gg_one_lt_of_SC hcS)
  refine ⟨?_, rhB_lt_Om1 hβc⟩
  rcases h1.lt_or_eq with hlt | heq
  · rw [← Mw.mwB_one (S := S) n]; exact ((mvB_lt_iff h1D' (hPD β hβc)).2 hlt).le
  · rw [← heq, Mw.mwB_one]

/-- **`B_n(F_β(Ω₁ + 1 + D)) = F_{B_n β}(Ω₁ + 1 + B_n D)`** for `1 ≤ β < c_{n+1}`, `D < c_{n+1}`; the atom is in the
domain of `B_n`. -/
theorem tsB_atom {n : ℕ} {β D : Ordinal.{0}} (h1 : 1 ≤ β) (hβc : β < Bc.bcC S (n + 1))
    (hDc : D < Bc.bcC S (n + 1)) :
    MvD S (rhF β (Om 1 + 1 + D)) ∧
      Bc.bcB S n (rhF β (Om 1 + 1 + D)) = rhF (Bc.bcB S n β) (Om 1 + 1 + Bc.bcB S n D) := by
  have hc1 : Bc.bcC S (n + 1) < Om 1 := (Bc.bcC_lt S (n + 1)).trans (InaccSeq.psi_lt Low.InR_Om_one _)
  obtain ⟨hl1, hlΩ⟩ := tsB_atom_lev (S := S) h1 hβc
  rw [ts_atom_ctbl (S := S) h1 (hβc.trans hc1) (hDc.trans hc1),
    ts_atom_ctbl (S := S) hl1 hlΩ (rhB_lt_Om1 hDc)]
  exact tsB_psiU h1 hβc hDc

/-- **`B_n` at an arbitrary atom**: a value `F_β(y)` with `Ω₁ < F_β(y) < ψ_{Ω₂}(B)` is `ψ_{Ω₂}(e)` for an own `e`
with `Ω₂^β ∣ e`; when `e` is in the domain of `B_n`, so is the atom and `B_n(F_β(y)) = ψ_{Ω₂}(B_n e)`. -/
theorem tsB_atom_gen {n : ℕ} {β y B : Ordinal.{0}} (hv1 : Om 1 < rhF β y) (hvB : rhF β y < S.psi B (Om (1 + 1))) :
    ∃ e, e ∈ S.CSet e (S.psi e (Om (1 + 1))) ∧ S.psi e (Om (1 + 1)) = rhF β y ∧ leWe β ∣ e ∧
      (MvD S e → MvD S (rhF β y) ∧ Bc.bcB S n (rhF β y) = S.psi (Bc.bcB S n e) (Om (1 + 1))) := by
  obtain ⟨e, hown, he, hdvd⟩ := ts_atom_own hv1 hvB
  refine ⟨e, hown, he, hdvd, fun hD => ?_⟩
  rw [← he]
  exact Mx.mxB_atom hD hown

end Googology.Trans.PoR.InaccPsi.R2.Ts

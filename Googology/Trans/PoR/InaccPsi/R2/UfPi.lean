import Googology.Trans.PoR.InaccPsi.R2.UfTop
import Googology.Trans.PoR.InaccPsi.R2.UfMap
import Googology.Trans.PoR.InaccPsi.R2.TzPi

/-!
# `π` on the codes below `B₂` and the commutation `B_n ∘ π = π' ∘ B_n` there

`π = pi σ τ`, `B_n = Bc.bcB S n`, `Se.SeComm`, `E₁ = ε_{Ω₁+1}`, `X = Tl.tlX`, `B₂ = Uc.ucB`, `H_λ = Uc.ucH λ` (the
atoms `H_λ(y) ≥ X`, `y < H_λ(y)`, of the codes `Uc.UcCl`).  The proof of `R2.TzPi` with every atom below `B₂`, the
package `Uc.UcCitPi M` (`Uc.ucCitPi`: it holds at `M = B₂`, from `R2.CitedUc`) and the move `Uf.ufB_atom`; below `X`
it is `Tz.tzUncG`:

* `uf_eps_TB`, `uf_opow_TB` (the `ε`-numbers and the powers `ω^g` under `UcCitPi M`), `uf_dat_cnf`, `uf_dat_phi`;
* `uf_pi_X` (**`X ∈ Tᵗ[σ]` and `π X = X`**), `ufB_lev_cl` (`Uf.ufB_lev` on the codes over `c_{n+1}`);
* `ufUnc_atom` (**the atom step**: `π(H_λ(y)) = H_{ucMap π λ}(π y)` is a code `≥ X`, and `SeComm` at `H_λ(y)` from
  `SeComm` at the components of `λ` and at `y`: `π'(B_n(H_λ y)) = H_{ucMap π' (ucMap B_n λ)}(π'(B_n y))
  = H_{ucMap B_n (ucMap π λ)}(B_n(π y)) = B_n(π(H_λ y))` by `Uf.uf_map_comp`);
* `ufUncG` (**`Se.SeComm` at every code `ξ ∈ Tᵗ[σ] ∩ [Ω₁, M)`, `M ≤ B₂`**, from `SeComm` at the countable terms
  `≤ D`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uf

open Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Ti
  Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Tc
  Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Ss
  Googology.Trans.PoR.InaccPsi.R2.Si Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Ts

variable {S : InaccSeq.{0}}

section API

variable {M : Ordinal.{0}} (hP : UcCitPi M)
include hP

/-- **An `ε`-number `Ω₁ < φ(a, c) < M` in normal form** (below `Γ_{Ω₁+1}` from `Sy.syCitPi`). -/
theorem uf_eps_TB {σ τ a c : Ordinal.{0}} (h : Bases σ τ) (ha : 1 ≤ a) (hav : a < veblen a c)
    (hcv : c < veblen a c) (h1 : Om1 < veblen a c) (hM : veblen a c < M) :
    (veblen a c ∈ TB τ σ ↔ a ∈ TB τ σ ∧ c ∈ TB τ σ) ∧
      (a ∈ TB τ σ → c ∈ TB τ σ → pi σ τ (veblen a c) = veblen (pi σ τ a) (pi σ τ c)) := by
  rcases lt_trichotomy (veblen a c) ggGam with hl | he | hg
  · exact Sy.syCitPi.eps h ha hav hcv h1 hl
  · exfalso
    have := ggGam_spec.1.2 a (by rw [← he]; exact hav) c (by rw [← he]; exact hcv)
    rw [he] at this; exact lt_irrefl _ this
  · exact hP.eps h ha hav hcv hg hM

/-- **A power `ω^g < M`, `g ≥ E₁` not an `ε`-number** (below `Γ_{Ω₁+1}` from `Sy.syCitPi`). -/
theorem uf_opow_TB {σ τ g : Ordinal.{0}} (h : Bases σ τ) (hg : ggE ≤ g) (hne : ω ^ g ≠ g) (hM : ω ^ g < M) :
    (ω ^ g ∈ TB τ σ ↔ g ∈ TB τ σ) ∧ (g ∈ TB τ σ → pi σ τ (ω ^ g) = ω ^ pi σ τ g) := by
  rcases lt_trichotomy (ω ^ g) ggGam with hl | he | hg'
  · exact Sy.syCitPi.opow h hg hne hl
  · exfalso
    have hgl : g < ω ^ g := lt_of_le_of_ne (right_le_opow g one_lt_omega0) (Ne.symm hne)
    have h2 : ω ^ g < ggGam := Sv.sv_Gam_inE.opow_lt (by rw [← he]; exact hgl)
    rw [he] at h2; exact lt_irrefl _ h2
  · exact hP.opow h hg hne hg' hM

end API

/-- The data of a component of a non-`ε` `ξ ∈ [X, B₂)`. -/
theorem uf_dat_cnf {ξ : Ordinal.{0}} (h1 : tlX ≤ ξ) (h2 : ξ < ucB) (hE : ω ^ ξ ≠ ξ) :
    ucDat (log ω ξ) ≤ ucDat ξ ∧ ucDat (ξ % ω ^ log ω ξ) ≤ ucDat ξ := by
  rw [ucDat_cnf h1 h2 hE]; exact ⟨le_max_left _ _, le_max_right _ _⟩

/-- The data of the arguments of an `ε`-number `ξ = φ(a, c) ∈ [X, B₂)` that is not an atom. -/
theorem uf_dat_phi {ξ : Ordinal.{0}} (h1 : tlX ≤ ξ) (h2 : ξ < ucB) (hE : ω ^ ξ = ξ) (hI : invVeblen₁ ξ < ξ) :
    ucDat (invVeblen₁ ξ) ≤ ucDat ξ ∧ ucDat (invVeblen₂ ξ) ≤ ucDat ξ := by
  rw [ucDat_phi h1 h2 hE hI]; exact ⟨le_max_left _ _, le_max_right _ _⟩

theorem uf_one_lt_inE {σ : Ordinal.{0}} (h : InE σ) : (1 : Ordinal.{0}) < σ :=
  one_lt_omega0.trans_le (omega0_le_of_isSuccLimit (ev_isSuccLimit_of_inE h))

/-- **`X ∈ Tᵗ[σ]` and `π X = X`** (`X = H_{Ω₂}(0)`, its components `1`, `0` and its index `0` are below `σ`). -/
theorem uf_pi_X {M : Ordinal.{0}} (hP : UcCitPi M) (hXM : tlX < M) {σ τ : Ordinal.{0}} (h : Bases σ τ) :
    tlX ∈ TB τ σ ∧ pi σ τ tlX = tlX := by
  have h0σ : (0 : Ordinal.{0}) < σ := si_inE_pos h.1
  have h1σ : (1 : Ordinal.{0}) < σ := uf_one_lt_inE h.1
  have hy : (0 : Ordinal.{0}) < ucH OmTwo 0 := (ucH_SC _ _).1
  have hX : tlX ≤ ucH OmTwo 0 := by rw [ucH_Om2_zero]
  have hM : ucH OmTwo 0 < M := by rw [ucH_Om2_zero]; exact hXM
  obtain ⟨hA, hπ⟩ := ucCitPi_H hP h ucE_gt hy hX hM
  have hc : ∀ x ∈ ucComps (OmTwo : Ordinal.{0}), x ∈ TB τ σ := fun x hx => by
    rw [ucComps_Om2] at hx
    rcases hx with rfl | hx
    · exact mem_TB_of_lt h h1σ
    · rw [mem_singleton_iff] at hx; rw [hx]; exact mem_TB_of_lt h h0σ
  have h0T : (0 : Ordinal.{0}) ∈ TB τ σ := mem_TB_of_lt h h0σ
  have hmap : ucMap (pi σ τ) OmTwo = OmTwo := by
    have e : (OmTwo : Ordinal.{0}) = OmTwo ^ (1 : Ordinal.{0}) * 1 + 0 := by rw [opow_one, mul_one, add_zero]
    have h' := ucMap_cnf (pi σ τ) le_rfl one_ne_zero uc_one_lt_Om2 (uc_W_pos 1) (by rw [← e]; exact ucE_gt)
    rw [← e] at h'
    rw [h', ucMap_small _ uc_one_lt_Om2, ucMap_small _ uc_SC_Om2.1, pi_lt h h1σ, pi_lt h h0σ, opow_one,
      mul_one, add_zero]
  have hπX := hπ hc h0T
  rw [hmap, pi_lt h h0σ, ucH_Om2_zero] at hπX
  rw [ucH_Om2_zero] at hA
  exact ⟨hA.2 ⟨hc, h0T⟩, hπX⟩

/-- `Uf.ufB_lev` on the codes over `c_{n+1}`. -/
theorem ufB_lev_cl {n : ℕ} {γ : Ordinal.{0}} (hγ : γ < ucE) (hc : ∀ x ∈ ucComps γ, UcCl (Bc.bcC S (n + 1)) x) :
    Mv.MvD S γ ∧ Bc.bcB S n γ = ucMap (Bc.bcB S n) γ ∧ Bc.bcB S n γ < ucE ∧
      ucComps (Bc.bcB S n γ) = Bc.bcB S n '' ucComps γ := by
  have hcS : SC (Bc.bcC S (n + 1)) := Lw.lw_L_SC S _
  have hx1 := uf_c_le (S := S) n
  obtain ⟨a, b, -, -, -, -, c, d, -⟩ := ufB_lev (S := S) (n := n) (fun v => UcCl (Bc.bcC S (n + 1)) v)
    (fun v hv => (ufB_cl hv).1)
    (fun v hv hv0 => ⟨(ucDec hcS hx1 v hv).2,
      (ucDec hcS hx1 v hv).1 _ (UcCl.opow hcS.1 (ucDec hcS hx1 v hv).2) (opow_log_le_self ω hv0)⟩)
    (fun v hv => uf_cl_lt_Om2 hx1 hv) γ hγ hc
  exact ⟨a, b, c, d⟩

/-- **The atom step**: for an atom `ξ = H_λ(y)` (`y < ξ`, `X ≤ ξ < M`) in `Tᵗ[σ]` with every component of `λ`, `y`,
their images under `π` codes over `c_{n+1}`, and `SeComm` at the components of `λ` and at `y`:
`π ξ = H_{ucMap π λ}(π y)` is a code `≥ X` below `B₂`, and `SeComm` holds at `ξ`. -/
theorem ufUnc_atom {M : Ordinal.{0}} (hP : UcCitPi M) (hMB2 : M ≤ ucB) {n : ℕ} {σ τ l y : Ordinal.{0}}
    (h : Bases σ τ) (hτc : τ < Bc.bcC S (n + 1)) (hlE : l < ucE) (hyF : y < ucH l y) (hX : tlX ≤ ucH l y)
    (hM : ucH l y < M) (hBM : Bc.bcB S n (ucH l y) < M) (hlT : ∀ x ∈ ucComps l, x ∈ TB τ σ) (hyT : y ∈ TB τ σ)
    (hlcl : ∀ x ∈ ucComps l, UcCl (Bc.bcC S (n + 1)) x) (hycl : UcCl (Bc.bcC S (n + 1)) y)
    (hπlcl : ∀ x ∈ ucComps l, UcCl (Bc.bcC S (n + 1)) (pi σ τ x)) (hπycl : UcCl (Bc.bcC S (n + 1)) (pi σ τ y))
    (hlC : ∀ x ∈ ucComps l, Se.SeComm S n σ τ x) (hyC : Se.SeComm S n σ τ y) :
    pi σ τ (ucH l y) = ucH (ucMap (pi σ τ) l) (pi σ τ y) ∧ pi σ τ (ucH l y) < ucB ∧
      UcCl (Bc.bcC S (n + 1)) (pi σ τ (ucH l y)) ∧ Se.SeComm S n σ τ (ucH l y) := by
  have hc1 := uf_c_le (S := S) n
  have hXM : tlX < M := hX.trans_lt hM
  obtain ⟨hA1, hA2⟩ := ucCitPi_H hP h hlE hyF hX hM
  have hπξ := hA2 hlT hyT
  have hξT := hA1.2 ⟨hlT, hyT⟩
  have hmono := (pi_bijOn h).2
  have h0σ : (0 : Ordinal.{0}) < σ := si_inE_pos h.1
  have h1σ : (1 : Ordinal.{0}) < σ := uf_one_lt_inE h.1
  -- `ucMap π l` is a level in normal form
  set A : Set Ordinal.{0} := {c | c ∈ TB τ σ ∧ pi σ τ c < OmTwo} with hAdef
  have hAm : ∀ a ∈ A, ∀ b ∈ A, a < b → pi σ τ a < pi σ τ b := fun a ha b hb hab => hmono ha.1 hb.1 hab
  have hA0 : (0 : Ordinal.{0}) ∈ A := ⟨mem_TB_of_lt h h0σ, by rw [pi_lt h h0σ]; exact uc_SC_Om2.1⟩
  have hA1' : (1 : Ordinal.{0}) ∈ A := ⟨mem_TB_of_lt h h1σ, by rw [pi_lt h h1σ]; exact uc_one_lt_Om2⟩
  have hAW : ∀ a ∈ A, a < OmTwo → pi σ τ a < OmTwo := fun a ha _ => ha.2
  have hlA : UfP (· ∈ A) l := fun x hx => ⟨hlT x hx, uf_cl_lt_Om2 hc1 (hπlcl x hx)⟩
  obtain ⟨hlπE, hlπC, -⟩ := uf_map_cnf (pi σ τ) hAm hA0 hA1' (pi_lt h h0σ) (pi_lt h h1σ) hAW l hlE hlA
  set lπ := ucMap (pi σ τ) l with hlπdef
  have hlπcl : ∀ x ∈ ucComps lπ, UcCl (Bc.bcC S (n + 1)) x := fun x hx => by
    rw [hlπC] at hx; obtain ⟨c, hc, rfl⟩ := hx; exact hπlcl c hc
  have hπy : pi σ τ y < ucH lπ (pi σ τ y) := by rw [← hπξ]; exact hmono hyT hξT hyF
  obtain ⟨hXT, hπX⟩ := uf_pi_X hP hXM h
  have hXπ : tlX ≤ ucH lπ (pi σ τ y) := by
    rw [← hπξ, ← hπX]
    rcases hX.lt_or_eq with hlt | heq
    · exact (hmono hXT hξT hlt).le
    · rw [heq]
  have hπcl : UcCl (Bc.bcC S (n + 1)) (ucH lπ (pi σ τ y)) := UcCl.hatom hlπE hlπcl hπycl hXπ
  -- the moves of `ξ` and of `π ξ`
  obtain ⟨hDξ, hBξ, -, -⟩ := ufB_atom (n := n) hlE hlcl hycl hyF hX
  obtain ⟨-, hBπξ, -, -⟩ := ufB_atom (n := n) hlπE hlπcl hπycl hπy hXπ
  obtain ⟨hDl, hBlm, hBlE, hBlC⟩ := ufB_lev_cl (S := S) (n := n) hlE hlcl
  obtain ⟨-, hBlπm, -, -⟩ := ufB_lev_cl (S := S) (n := n) hlπE hlπcl
  have hDy := (ufB_cl (n := n) hycl).1
  have hBy : Bc.bcB S n y < Bc.bcB S n (ucH l y) := (Mv.mvB_lt_iff hDy hDξ).2 hyF
  obtain ⟨hDX, hBX⟩ := ufB_X (S := S) (n := n)
  have hXB : tlX ≤ Bc.bcB S n (ucH l y) := by rw [← hBX]; exact ufB_le hDX hDξ hX
  rw [hBξ] at hBy hXB hBM
  have hB' := Se.seBases_img h hτc
  obtain ⟨hB1, hB2⟩ := ucCitPi_H hP hB' hBlE hBy hXB hBM
  have hBlT : ∀ x ∈ ucComps (Bc.bcB S n l), x ∈ TB (Bc.bcB S n τ) (Bc.bcB S n σ) := fun x hx => by
    rw [hBlC] at hx; obtain ⟨c, hc, rfl⟩ := hx; exact (hlC c hc).1
  refine ⟨hπξ, by rw [hπξ]; exact uf_cl_lt_B hc1 hπcl, by rw [hπξ]; exact hπcl, ?_, ?_⟩
  · rw [hBξ]; exact hB1.2 ⟨hBlT, hyC.1⟩
  · -- `π'(B_n ξ) = B_n(π ξ)`
    set AB : Set Ordinal.{0} := {c | Mv.MvD S c ∧ Bc.bcB S n c < OmTwo} with hABdef
    have hABm : ∀ a ∈ AB, ∀ b ∈ AB, a < b → Bc.bcB S n a < Bc.bcB S n b :=
      fun a ha b hb hab => (Mv.mvB_lt_iff ha.1 hb.1).2 hab
    have hAB0 : (0 : Ordinal.{0}) ∈ AB := ⟨ufD_zero, by rw [Bc.bcB_zero]; exact uc_SC_Om2.1⟩
    have hAB1 : (1 : Ordinal.{0}) ∈ AB := ⟨Rk.rk_one_D, by rw [Mw.mwB_one]; exact uc_one_lt_Om2⟩
    have hlAB : UfP (· ∈ AB) l := fun x hx =>
      ⟨(ufB_cl (hlcl x hx)).1, uf_cl_lt_Om2 (by rw [uf_Om1]; exact Tc.tcB_c_le (S := S) n)
        (ufB_cl (hlcl x hx)).2.1⟩
    have hlπAB : UfP (· ∈ AB) lπ := fun x hx =>
      ⟨(ufB_cl (hlπcl x hx)).1, uf_cl_lt_Om2 (by rw [uf_Om1]; exact Tc.tcB_c_le (S := S) n) (ufB_cl (hlπcl x hx)).2.1⟩
    have hc1 := ufB_lev_cl (S := S) (n := n) hlπE hlπcl
    have e1 : ucMap (pi (Bc.bcB S n σ) (Bc.bcB S n τ)) (ucMap (Bc.bcB S n) l) =
        ucMap (fun x => pi (Bc.bcB S n σ) (Bc.bcB S n τ) (Bc.bcB S n x)) l :=
      uf_map_comp (Bc.bcB S n) hABm hAB0 hAB1 (Bc.bcB_zero n) (Mw.mwB_one n) (fun a ha _ => ha.2) _ l hlE hlAB
    have e2 : ucMap (Bc.bcB S n) (ucMap (pi σ τ) l) = ucMap (fun x => Bc.bcB S n (pi σ τ x)) l :=
      uf_map_comp (pi σ τ) hAm hA0 hA1' (pi_lt h h0σ) (pi_lt h h1σ) hAW _ l hlE hlA
    have e3 : ucMap (fun x => pi (Bc.bcB S n σ) (Bc.bcB S n τ) (Bc.bcB S n x)) l =
        ucMap (fun x => Bc.bcB S n (pi σ τ x)) l := uf_map_congr l fun c hc => (hlC c hc).2
    rw [hBξ, hB2 hBlT hyC.1, hyC.2, hBlm, e1, e3, ← e2, ← hlπdef, ← hBlπm, hπξ, hBπξ]

/-- **`SeComm` on the codes `[Ω₁, M)`, `M ≤ B₂`,** under `UcCitPi M`. -/
theorem ufUncG {M : Ordinal.{0}} (hP : UcCitPi M) (hMG : M ≤ ucB)
    (hMB : ∀ n : ℕ, ∀ ξ, ξ < M → UcCl (Bc.bcC S (n + 1)) ξ → Bc.bcB S n ξ < M)
    {n : ℕ} {σ τ D : Ordinal.{0}} (h : Bases σ τ) (hτc : τ < Bc.bcC S (n + 1))
    (hDc : D < Bc.bcC S (n + 1))
    (hH : ∀ w ∈ TB τ σ, w < Om1 → w ≤ D → Se.SeComm S n σ τ w) :
    ∀ ξ, ξ ∈ TB τ σ → Om1 ≤ ξ → ξ < M → ucDat ξ ≤ D →
      Bc.bcB S n ξ < ucB ∧ pi σ τ ξ < ucB ∧ UcCl (Bc.bcC S (n + 1)) (pi σ τ ξ) ∧
        Se.SeComm S n σ τ ξ := by
  have hcL : Bc.bcC S (n + 1) < Nc.ncL S ω := Se.seC_lt_L n
  have hc0 : (0 : Ordinal.{0}) < Bc.bcC S (n + 1) := lt_of_le_of_lt zero_le hDc
  have hσc : σ < Bc.bcC S (n + 1) := h.2.2.1.trans hτc
  have hB' := Se.seBases_img h hτc
  have hGs : SC (ucB : Ordinal.{0}) := ucB_SC
  have hc1 := uf_c_le (S := S) n
  -- the countable arguments
  have hcnt : ∀ w ∈ TB τ σ, w < Om1 → w ≤ D →
      Mv.MvD S w ∧ pi σ τ w < ucB ∧ UcCl (Bc.bcC S (n + 1)) (pi σ τ w) ∧
        Mv.MvD S (pi σ τ w) ∧ Se.SeComm S n σ τ w := by
    intro w hw hw1 hwD
    have hwc : w < Bc.bcC S (n + 1) := hwD.trans_lt hDc
    have hπ1 : pi σ τ w < Om1 := down_lt_Om1 h hw hw1
    have hπc : pi σ τ w < Bc.bcC S (n + 1) := si_T_lt_c h.1 hσc ((pi_bijOn h).1.mapsTo hw) hπ1
    exact ⟨Mv.mvD_of_lt (hwc.trans hcL), hπ1.trans ucB_gt, UcCl.small hπc,
      Mv.mvD_of_lt (hπc.trans hcL), hH w hw hw1 hwD⟩
  intro ξ
  induction ξ using WellFoundedLT.induction with
  | ind ξ IH =>
  intro hξ hξ1 hξM hξD
  have hξB : ξ < ucB := hξM.trans_le hMG
  rcases lt_or_ge ξ tlX with hξX | hXξ
  · -- below `X`: `Tz.tzUncG`
    obtain ⟨a1, a2, a3, a4⟩ := Tz.tzUncG Tl.tlCitPi le_rfl (fun n ξ _ h' => Tw.twB_lt_X h') h hτc hDc hH ξ hξ
      hξ1 hξX (by rw [← ucDat_lt_X hξX]; exact hξD)
    exact ⟨a1.trans uc_X_lt_B, a2.trans uc_X_lt_B, UcCl.tl a3, a4⟩
  have hξcl : UcCl (Bc.bcC S (n + 1)) ξ := uc_code hc0 ξ hξB (hξD.trans_lt hDc)
  have hBξG : Bc.bcB S n ξ < ucB := ufB_lt_B hξcl
  have hDξ := (ufB_cl (n := n) hξcl).1
  have hξ1' : Om1 < ξ := uc_Om1_lt_of_X hXξ
  -- facts at a smaller code `b ∈ Tᵗ[σ]` with `ucDat b ≤ D`
  have hsub : ∀ b, b < ξ → b ∈ TB τ σ → ucDat b ≤ D →
      Mv.MvD S b ∧ pi σ τ b < ucB ∧ UcCl (Bc.bcC S (n + 1)) (pi σ τ b) ∧ Mv.MvD S (pi σ τ b) ∧
        Se.SeComm S n σ τ b := by
    intro b hbξ hbT hbD
    rcases lt_or_ge b Om1 with hb1 | hb1
    · exact hcnt b hbT hb1 (by rw [← ucDat_small hb1]; exact hbD)
    · obtain ⟨-, a3, a4, a7⟩ := IH b hbξ hbT hb1 (hbξ.trans hξM) hbD
      have hbcl : UcCl (Bc.bcC S (n + 1)) b := uc_code hc0 b (hbξ.trans hξB) (hbD.trans_lt hDc)
      exact ⟨(ufB_cl (n := n) hbcl).1, a3, a4, (ufB_cl (n := n) a4).1, a7⟩
  have hξE : ggE ≤ ξ := (Ss.ss_E_lt_Gam.trans (Tz.tz_gg_lt_X)).le.trans hXξ
  by_cases hEps : ω ^ ξ = ξ
  · by_cases hI : invVeblen₁ ξ < ξ
    swap
    · -- an atom `ξ = H_λ(y)`, `y < ξ`
      have hSC : SC ξ := tl_SC_of hξ1' hI
      have hne := uc_nf_of_lt hSC hξ1' hξB
      obtain ⟨hlE, hlv, -, -, -⟩ := ucLev_spec hSC hξ1' hne
      obtain ⟨hnf, hyξ⟩ := uc_nf hSC hξ1' hne
      have hdat := ucDat_atom hXξ hξB hEps hI
      generalize hldef : ucLev ξ = l at hlE hlv hnf hyξ hdat
      generalize hydef : ucI l ξ = y at hnf hyξ hdat
      have hyF : y < ucH l y := by rw [hnf]; exact hyξ
      have hXF : tlX ≤ ucH l y := by rw [hnf]; exact hXξ
      have hMF : ucH l y < M := by rw [hnf]; exact hξM
      have hBMF : Bc.bcB S n (ucH l y) < M := by rw [hnf]; exact hMB n ξ hξM hξcl
      have hξT' : ucH l y ∈ TB τ σ := by rw [hnf]; exact hξ
      obtain ⟨hlT, hyT⟩ := ((ucCitPi_H hP h hlE hyF hXF hMF).1.1 hξT')
      have hlD : ∀ c ∈ ucComps l, ucDat c ≤ D := fun c hc =>
        ((ucFold_le_of_mem ucDat l c hc).trans (le_max_left _ _)).trans (hdat ▸ hξD)
      have hyD : ucDat y ≤ D := (le_max_right _ _).trans (hdat ▸ hξD)
      have hcξ : ∀ c ∈ ucComps l, c < ξ := fun c hc => (le_ucC hc).trans_lt hlv
      have hcode : ∀ b, b < ξ → ucDat b ≤ D → UcCl (Bc.bcC S (n + 1)) b := fun b hb hbD =>
        uc_code hc0 b (hb.trans hξB) (hbD.trans_lt hDc)
      obtain ⟨-, -, hπycl, -, hyC⟩ := hsub y hyξ hyT hyD
      obtain ⟨-, a2, a3, a4⟩ := ufUnc_atom hP hMG h hτc hlE hyF hXF hMF hBMF hlT hyT
        (fun c hc => hcode c (hcξ c hc) (hlD c hc)) (hcode y hyξ hyD)
        (fun c hc => (hsub c (hcξ c hc) (hlT c hc) (hlD c hc)).2.2.1) hπycl
        (fun c hc => (hsub c (hcξ c hc) (hlT c hc) (hlD c hc)).2.2.2.2) hyC
      rw [hnf] at a2 a3 a4
      exact ⟨hBξG, a2, a3, a4⟩
    -- an `ε`-number `ξ = φ(a, c)`
    set a := invVeblen₁ ξ with hadef
    set c := invVeblen₂ ξ with hcdef
    have haξ : a < ξ := hI
    have hcξ : c < ξ := ss_inv2_lt hEps
    have hev : veblen a c = ξ := by rw [hadef, hcdef, veblen_invVeblen₁_invVeblen₂, hEps]
    have ha0 : a ≠ 0 := by
      intro e
      rw [e, veblen_zero_apply] at hev
      have : ω ^ c = ω ^ ξ := by rw [hev, hEps]
      exact absurd ((opow_right_inj one_lt_omega0).1 this) hcξ.ne
    obtain ⟨haD, hcD⟩ := uf_dat_phi hXξ hξB hEps hI
    have hepsξ := uf_eps_TB hP h (one_le_iff_ne_zero.2 ha0) (by rw [hev]; exact haξ) (by rw [hev]; exact hcξ)
      (by rw [hev]; exact hξ1') (by rw [hev]; exact hξM)
    rw [hev] at hepsξ
    obtain ⟨haT, hcT⟩ := hepsξ.1.1 hξ
    have hπξ : pi σ τ ξ = veblen (pi σ τ a) (pi σ τ c) := hepsξ.2 haT hcT
    obtain ⟨hDa, hπaG, hπacl, hDπa, haC⟩ := hsub a haξ haT (haD.trans hξD)
    obtain ⟨hDc', hπcG, hπccl, hDπc, hcC⟩ := hsub c hcξ hcT (hcD.trans hξD)
    -- `B_n ξ = φ(B_n a, B_n c)`
    obtain ⟨-, hBξ⟩ := Mw.mwB_phi (k := n) hDa hDc' (by rw [hev]; exact haξ) (by rw [hev]; exact hcξ)
    rw [hev] at hBξ
    have hBa : Bc.bcB S n a < Bc.bcB S n ξ := (Mv.mvB_lt_iff hDa hDξ).2 haξ
    have hBc : Bc.bcB S n c < Bc.bcB S n ξ := (Mv.mvB_lt_iff hDc' hDξ).2 hcξ
    have hD0 : Mv.MvD S (0 : Ordinal.{0}) := Mv.mvD_of_lt (lt_of_le_of_lt zero_le hcL)
    have hBa0 : Bc.bcB S n a ≠ 0 := by
      intro e
      have h1 := (Mv.mvB_lt_iff (k := n) hD0 hDa).2 (pos_iff_ne_zero.2 ha0)
      rw [Bc.bcB_zero, e] at h1
      exact lt_irrefl _ h1
    obtain ⟨hDO, hBO⟩ := Mv.mvB_Om1 (S := S) (k := n)
    rw [← rj_Om1] at hDO hBO
    have hOB : Om1 < Bc.bcB S n ξ := by
      have := (Mv.mvB_lt_iff (k := n) hDO hDξ).2 hξ1'; rwa [hBO] at this
    have hBξM : Bc.bcB S n ξ < M := hMB n ξ hξM hξcl
    have heps' := uf_eps_TB hP hB' (one_le_iff_ne_zero.2 hBa0) (by rw [← hBξ]; exact hBa) (by rw [← hBξ]; exact hBc)
      (by rw [← hBξ]; exact hOB) (by rw [← hBξ]; exact hBξM)
    rw [← hBξ] at heps'
    -- `π ξ = φ(π a, π c)` in normal form (`π` is injective)
    have hπinj : ∀ y ∈ TB τ σ, pi σ τ y = pi σ τ ξ → y = ξ := fun y hy he => (pi_bijOn h).1.injOn hy hξ he
    have hπa : pi σ τ a < pi σ τ ξ := by
      refine lt_of_le_of_ne ?_ fun e => haξ.ne (hπinj a haT e)
      rw [hπξ]; exact left_le_veblen _ _
    have hπc : pi σ τ c < pi σ τ ξ := by
      refine lt_of_le_of_ne ?_ fun e => hcξ.ne (hπinj c hcT e)
      rw [hπξ]; exact right_le_veblen _ _
    rw [hπξ] at hπa hπc
    obtain ⟨-, hBπ⟩ := Mw.mwB_phi (k := n) hDπa hDπc hπa hπc
    refine ⟨hBξG, by rw [hπξ]; exact hGs.2 _ hπaG _ hπcG, by rw [hπξ]; exact UcCl.phi hπacl hπccl, ?_, ?_⟩
    · exact heps'.1.2 ⟨haC.1, hcC.1⟩
    · rw [heps'.2 haC.1 hcC.1, haC.2, hcC.2, hπξ, hBπ]
  · -- a non-`ε` code `ξ = ω^g·k + r`, `g ≥ E₁`
    have hξ0 : ξ ≠ 0 := (rj_Om1_pos.trans hξ1').ne'
    have hτξ : τ ≤ ξ := h.2.2.2.le.trans hξ1'.le
    obtain ⟨hdec, -, -, -⟩ := si_dec hξ0
    have hcξ := si_comps_cons hξ0
    set g := log ω ξ with hgdef
    set r := ξ % ω ^ g with hrdef
    have hgE : ggE ≤ g := le_log_of_opow_le one_lt_omega0 (by rw [Rk.rk_E_inE]; exact hξE)
    have hgξ : g < ξ := ss_log_lt hξ0 hEps
    obtain ⟨hgD, hrD⟩ := uf_dat_cnf hXξ hξB hEps
    have hrξ : r < ξ := rj_mod_lt hξ0
    have hpTB : ω ^ g ∈ TB τ σ := by
      refine siTB_of_comps h hξ hτξ fun p hp => ?_
      have hg0 : ω ^ g ≠ 0 := (opow_pos _ omega0_pos).ne'
      rw [si_comps_cons hg0, log_opow one_lt_omega0, Ordinal.mod_self, si_comps_zero] at hp
      rw [List.mem_singleton.1 hp, hcξ]; exact List.mem_cons_self
    have hrTB : r ∈ TB τ σ := siTB_of_comps h hξ hτξ fun p hp => by
      rw [hcξ]; exact List.mem_cons_of_mem _ hp
    have hpξ : ω ^ g ≤ ξ := opow_log_le_self ω hξ0
    -- the facts at `ω^g`
    have hpF : Mv.MvD S (ω ^ g) ∧ pi σ τ (ω ^ g) < ucB ∧ UcCl (Bc.bcC S (n + 1)) (pi σ τ (ω ^ g)) ∧
        Mv.MvD S (pi σ τ (ω ^ g)) ∧ Se.SeComm S n σ τ (ω ^ g) := by
      by_cases hgE' : ω ^ g = g
      · -- `ω^g = g` an `ε`-number below `ξ`
        have hgT : g ∈ TB τ σ := by rw [← hgE']; exact hpTB
        rw [hgE']
        exact hsub g hgξ hgT (hgD.trans hξD)
      · obtain ⟨hiff, hπp⟩ := uf_opow_TB hP h hgE hgE' (hpξ.trans_lt hξM)
        have hgT : g ∈ TB τ σ := hiff.1 hpTB
        obtain ⟨hDg, hπgG, hπgcl, hDπg, hgC⟩ := hsub g hgξ hgT (hgD.trans hξD)
        obtain ⟨hDp, hBp⟩ := Ld.ldB_opow (n := n) hDg
        obtain ⟨hDπp, hBπp⟩ := Ld.ldB_opow (n := n) hDπg
        have hgcl : UcCl (Bc.bcC S (n + 1)) g := uc_code hc0 g (hgξ.trans hξB) ((hgD.trans hξD).trans_lt hDc)
        have hpcl : UcCl (Bc.bcC S (n + 1)) (ω ^ g) := UcCl.opow hc0 hgcl
        have hBgE : ggE ≤ Bc.bcB S n g := Sv.sv_B_geE hDg hgE
        have hBgne : ω ^ Bc.bcB S n g ≠ Bc.bcB S n g := by
          intro e
          rw [← hBp] at e
          rcases lt_trichotomy (ω ^ g) g with hl | hl | hl
          · exact absurd e ((Mv.mvB_lt_iff hDp hDg).2 hl).ne
          · exact hgE' hl
          · exact absurd e ((Mv.mvB_lt_iff hDg hDp).2 hl).ne'
        have hBpM : ω ^ Bc.bcB S n g < M := by rw [← hBp]; exact hMB n _ (hpξ.trans_lt hξM) hpcl
        obtain ⟨hiff', hπp'⟩ := uf_opow_TB hP hB' hBgE hBgne hBpM
        refine ⟨hDp, by rw [hπp hgT]; exact uf_B_inE.opow_lt hπgG, by rw [hπp hgT]; exact UcCl.opow hc0 hπgcl,
          by rw [hπp hgT]; exact hDπp, ?_, ?_⟩
        · rw [hBp]; exact hiff'.2 hgC.1
        · rw [hBp, hπp' hgC.1, hgC.2, hπp hgT, hBπp]
    obtain ⟨hDp', hπpG, hπpcl, hDπp', hpC⟩ := hpF
    -- the multiples `ω^g·j`
    have h0σ : (0 : Ordinal.{0}) < σ := si_inE_pos h.1
    have hD0 : Mv.MvD S (0 : Ordinal.{0}) := Mv.mvD_of_lt (Lw.lw_L_SC S ω).1
    have hmul : ∀ j : ℕ, ω ^ g * j ∈ TB τ σ ∧ pi σ τ (ω ^ g * j) = pi σ τ (ω ^ g) * j ∧
        Mv.MvD S (ω ^ g * j) ∧ Mv.MvD S (pi σ τ (ω ^ g) * j) ∧ Se.SeComm S n σ τ (ω ^ g * j) := by
      intro j
      induction j with
      | zero =>
        simp only [Nat.cast_zero, mul_zero]
        have h0T := mem_TB_of_lt h h0σ
        exact ⟨h0T, pi_lt h h0σ, hD0, hD0, hH 0 h0T rj_Om1_pos zero_le⟩
      | succ j ih =>
        obtain ⟨hT, hπ, hD, hDπ, hC⟩ := ih
        rw [Nat.cast_succ, mul_add_one, mul_add_one]
        obtain ⟨hsT, hsπ⟩ := pi_add h hT hpTB
        refine ⟨hsT, by rw [hsπ, hπ], (Mv.mvB_add (k := n) hD hDp').1, (Mv.mvB_add (k := n) hDπ hDπp').1, ?_⟩
        exact siComm_add h hτc hT hpTB hD hDp' (by rw [hπ]; exact hDπ) hDπp' hC hpC
    -- the remainder
    obtain ⟨hDr, hπrG, hπrcl, hDπr, hrC⟩ := hsub r hrξ hrTB (hrD.trans hξD)
    obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt ξ one_lt_omega0)
    have hξk : ω ^ g * (k : Ordinal.{0}) + r = ξ := by rw [← hk]; exact hdec
    obtain ⟨hkT, hkπ, hkD, hkDπ, hkC⟩ := hmul k
    have hπξ : pi σ τ ξ = pi σ τ (ω ^ g) * k + pi σ τ r := by
      conv_lhs => rw [← hξk]
      rw [(pi_add h hkT hrTB).2, hkπ]
    have hωG : (ω : Ordinal.{0}) < ucB := omega0_lt_inE uf_B_inE
    refine ⟨hBξG, ?_, ?_, ?_⟩
    · rw [hπξ]
      exact uf_B_inE.add_lt (uf_B_inE.mul_lt hπpG ((natCast_lt_omega0 k).trans hωG)) hπrG
    · rw [hπξ]; exact UcCl.add (UcCl.mul_nat hc0 hπpcl k) hπrcl
    · rw [← hξk]
      exact siComm_add h hτc hkT hrTB hkD hDr (by rw [hkπ]; exact hkDπ) hDπr hkC hrC

end Googology.Trans.PoR.InaccPsi.R2.Uf

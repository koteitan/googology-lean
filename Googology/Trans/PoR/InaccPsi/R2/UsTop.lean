import Googology.Trans.PoR.InaccPsi.R2.UsBV
import Googology.Trans.PoR.InaccPsi.R2.LwFix
import Googology.Trans.PoR.InaccPsi.R2.RxLv

/-!
# The tops `θ_s = ψ_{Ω_{s+1}}(Ω_ω)` of every finite threshold, and the chain `ψ_{Ω_{s+1}}(ε_{Ω_n+1})` below them

`W = Ω_{s+1}`, `V = Ω_{s+2}` (`s` finite), `θ_s = S.psi (Om ω) W` (`θ_1 = ConjT.th S`), `Hˡ_γ = Ul.ulH S s γ`,
`K_q = Ul.UlK S s q`, `E_n = ε_{Ω_n+1} = φ(1, Ω_n + 1)` (`n` finite).  These are the `ψ`-side facts of the recursion
on the level `k` behind `θ₁ = θ` ([W07a] Def 3.13, Lemma 3.16, Thm 3.23: `θ_m = sup_n ϑ_m(⋯ϑ_n(0)⋯)`):

* `us_OmW_own`, `us_W_dvd_OmW` (`W^{γ+1} ∣ Ω_ω` for `γ < V`), `us_top_lt_W` (`Ω_s < θ_s < W`);
* `us_top_fix` (**`θ_s` is a fixed point of every level `γ < θ_{s+1}` visible at `θ_s`**: `γ ∈ K_{θ_s}`, `γ <
  θ_{s+1}` give `Hˡ_γ(θ_s) = θ_s`), `us_top_lt` (**`Hˡ_γ(y) < θ_s` for such `γ` and `y < θ_s`**), `us_top_phi`
  (`φ(a, y) < θ_s` for `a, y < θ_s`);
* `us_E_*` (`E_n` is own at every `ψ_π`, `W^{E_n} = E_n`), `us_top_E` (**the top of the chain**: `Hˡ_{E_{s+1}}(0) =
  ψ_W(E_{s+1})`), `us_step_E` (**the step of the chain**: `Hˡ_{ψ_V(E_n)}(0) = ψ_W(E_n)` for `n ≥ s + 2`);
* `us_top_sup` (**`θ_s = sup_n ψ_W(E_n)`**: every `z < θ_s` is below some `ψ_W(E_n)`, and every `ψ_W(E_n) < θ_s`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Us

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul Googology.Trans.PoR.InaccPsi.R2.Uo
  Googology.Trans.PoR.InaccPsi.R2.Uc

variable {S : InaccSeq.{0}} {s : Ordinal.{0}}

theorem us_OmW_own : Om ω ∈ S.CSet (Om ω) (S.psi (Om ω) (Om (s + 1))) := ConjT.OmW_mem S _ _

theorem us_OmW_SC : SC (Om (ω : Ordinal.{0})) := SC_Om omega0_ne_zero

theorem us_V_lt_OmW (hs : s < ω) : Om (s + 1 + 1) < Om (ω : Ordinal.{0}) :=
  Om_lt_Om.2 (Ui.ui_s1_lt_omega (Ui.ui_s1_lt_omega hs))

/-- `W^{γ+1} ∣ Ω_ω` for every level `γ < V`. -/
theorem us_W_dvd_OmW (hs : s < ω) {γ : Ordinal.{0}} (hγ : γ < Om (s + 1 + 1)) :
    Om (s + 1) ^ (γ + 1) ∣ Om ω := by
  have hV : Om (s + 1 + 1) ∣ Om (ω : Ordinal.{0}) := by
    have := opow_dvd_opow ω (us_V_lt_OmW hs).le
    rwa [Ui.ui_W_opow (s + 1), Gg.gg_SC_eps us_OmW_SC] at this
  exact (us_W_dvd_V s (Order.add_one_le_of_lt hγ)).trans hV

theorem us_top_lt_W : Om s < S.psi (Om ω) (Om (s + 1)) ∧ S.psi (Om ω) (Om (s + 1)) < Om (s + 1) :=
  psiS_bounds _ s

/-- **`θ_s` is a fixed point of every level `γ < θ_{s+1}` visible at `θ_s`.** -/
theorem us_top_fix (hs : s < ω) {γ : Ordinal.{0}} (hγ : γ < S.psi (Om ω) (Om (s + 1 + 1)))
    (hK : UlK S s (S.psi (Om ω) (Om (s + 1))) γ) :
    ulH S s γ (S.psi (Om ω) (Om (s + 1))) = S.psi (Om ω) (Om (s + 1)) := by
  have hγV : γ < Om (s + 1 + 1) := hγ.trans (Ui.ui_psi_lt _)
  exact uo_fwd hs γ hγV (Om ω) us_OmW_own (us_W_dvd_OmW hs hγV) us_OmW_SC.1.ne'
    (uoDV hs (Om ω) γ us_OmW_own hK hγ)

/-- **`Hˡ_γ(y) < θ_s`** for a level `γ < θ_{s+1}` visible at `θ_s` and `y < θ_s`. -/
theorem us_top_lt (hs : s < ω) {γ y : Ordinal.{0}} (hγ : γ < S.psi (Om ω) (Om (s + 1 + 1)))
    (hK : UlK S s (S.psi (Om ω) (Om (s + 1))) γ) (hy : y < S.psi (Om ω) (Om (s + 1))) :
    ulH S s γ y < S.psi (Om ω) (Om (s + 1)) := by
  have h := (ulH_lt_iff (S := S) (s := s) γ).2 hy
  rwa [us_top_fix hs hγ hK] at h

/-- `φ(a, y) < θ_s` for `a, y < θ_s`. -/
theorem us_top_phi {a y : Ordinal.{0}} (ha : a < S.psi (Om ω) (Om (s + 1)))
    (hy : y < S.psi (Om ω) (Om (s + 1))) : veblen a y < S.psi (Om ω) (Om (s + 1)) :=
  (Ui.ui_psi_SC (S := S) (s := s) (Om ω)).2 a ha y hy

/-! ## The chain `E_n = ε_{Ω_n+1}` -/

theorem us_nat_mem (a b : Ordinal.{0}) : ∀ n : ℕ, (n : Ordinal.{0}) ∈ S.CSet a b
  | 0 => by rw [Nat.cast_zero]; exact CSet.zero_mem a b
  | n + 1 => by rw [Nat.cast_succ]; exact CSet.succ_mem (us_nat_mem a b n)

/-- `E_n = φ(1, Ω_n + 1)` is in every hull `Cl(a, b)`. -/
theorem us_E_mem (n : ℕ) (a b : Ordinal.{0}) : veblen 1 (Om (n : Ordinal.{0}) + 1) ∈ S.CSet a b :=
  CSet.phi_mem (CSet.one_mem a b) (CSet.succ_mem (CSet.Om_mem (us_nat_mem a b n)))

theorem us_E_pos (n : ℕ) : veblen 1 (Om (n : Ordinal.{0}) + 1) ≠ 0 := veblen_pos.ne'

theorem us_E_eps (n : ℕ) : ω ^ veblen 1 (Om (n : Ordinal.{0}) + 1) = veblen 1 (Om (n : Ordinal.{0}) + 1) :=
  Gg.gg_veblen_eps one_ne_zero

theorem us_lt_E (n : ℕ) : Om (n : Ordinal.{0}) < veblen 1 (Om (n : Ordinal.{0}) + 1) :=
  (Order.lt_add_one_iff.2 le_rfl).trans_le (right_le_veblen 1 _)

/-- `E_n < Ω_m` for `n < m`. -/
theorem us_E_lt_Om {n : ℕ} {m : Ordinal.{0}} (h : (n : Ordinal.{0}) < m) :
    veblen 1 (Om (n : Ordinal.{0}) + 1) < Om m := by
  have hm0 : m ≠ 0 := (lt_of_le_of_lt zero_le h).ne'
  have hSC := SC_Om hm0
  have hn : Om (n : Ordinal.{0}) < Om m := Om_lt_Om.2 h
  exact hSC.2 1 (Ui.ui_one_lt_SC hSC) _ (hSC.add_one_lt hn)

theorem us_E_lt_OmW (n : ℕ) : veblen 1 (Om (n : Ordinal.{0}) + 1) < Om (ω : Ordinal.{0}) :=
  us_E_lt_Om (natCast_lt_omega0 n)

/-- `W^{E_n} = E_n` for `W ≤ Ω_n`. -/
theorem us_W_E {n : ℕ} (h : s + 1 ≤ (n : Ordinal.{0})) :
    Om (s + 1) ^ veblen 1 (Om (n : Ordinal.{0}) + 1) = veblen 1 (Om (n : Ordinal.{0}) + 1) := by
  rw [Ui.ui_W_eq s]
  have hWE : Om (s + 1) < veblen 1 (Om (n : Ordinal.{0}) + 1) := (Om_le_Om.2 h).trans_lt (us_lt_E n)
  have hmul : Om (s + 1) * veblen 1 (Om (n : Ordinal.{0}) + 1) = veblen 1 (Om (n : Ordinal.{0}) + 1) := by
    conv_lhs => rw [← Ui.ui_W_opow s, ← us_E_eps n]
    rw [← opow_add]
    have hab : Om (s + 1) + veblen 1 (Om (n : Ordinal.{0}) + 1) = veblen 1 (Om (n : Ordinal.{0}) + 1) :=
      Ordinal.add_of_omega0_opow_le (by rw [us_E_eps n]; exact hWE) (by rw [us_E_eps n])
    rw [hab, us_E_eps n]
  rw [hmul, us_E_eps n]

/-- **The top of the chain**: `Hˡ_{E_{s+1}}(0) = ψ_W(E_{s+1})` (`E_{s+1} = ε_{W+1}`). -/
theorem us_top_E (hs : s < ω) {n : ℕ} (hn : (n : Ordinal.{0}) = s + 1) :
    ulH S s (veblen 1 (Om (n : Ordinal.{0}) + 1)) 0 = S.psi (veblen 1 (Om (n : Ordinal.{0}) + 1)) (Om (s + 1)) := by
  set E := veblen 1 (Om (n : Ordinal.{0}) + 1) with hE
  have hκV : S.InR (Om (s + 1 + 1)) := InR_Om_succ (s + 1)
  have hown : E ∈ S.CSet E (S.psi E (Om (s + 1))) := us_E_mem n _ _
  have hEV : E < Om (s + 1 + 1) := us_E_lt_Om (by rw [hn]; exact Order.lt_add_one_iff.2 le_rfl)
  have hWE : Om (s + 1) ^ E = E := us_W_E hn.ge
  have hEψ : E < S.psi E (Om (s + 1 + 1)) := lt_psi_of_mem hκV (us_E_mem n _ _) hEV
  exact us_bv hs E hown (us_E_pos n) E (us_E_pos n) hEV (by rw [hWE]) hEψ.le (ul_K_of_mem hown)
    (Or.inr (by rw [hWE]))

/-- **The step of the chain**: `Hˡ_{ψ_V(E_n)}(0) = ψ_W(E_n)` for `n ≥ s + 2`. -/
theorem us_step_E (hs : s < ω) {n : ℕ} (hn : s + 1 + 1 ≤ (n : Ordinal.{0})) :
    ulH S s (S.psi (veblen 1 (Om (n : Ordinal.{0}) + 1)) (Om (s + 1 + 1))) 0 =
      S.psi (veblen 1 (Om (n : Ordinal.{0}) + 1)) (Om (s + 1)) := by
  have hVE : Om (s + 1 + 1) ∣ veblen 1 (Om (n : Ordinal.{0}) + 1) := by
    have := opow_dvd_opow ω ((Om_le_Om.2 hn).trans (us_lt_E n).le)
    rwa [Ui.ui_W_opow (s + 1), us_E_eps n] at this
  exact us_bv_atom hs (us_E_mem n _ _) (us_E_pos n) hVE

/-! ## `θ_s = sup_n ψ_W(E_n)` -/

/-- **`θ_s = sup_n ψ_W(E_n)`**: every `z < θ_s` is below some `ψ_W(E_n)`, and every `ψ_W(E_n)` is below `θ_s`. -/
theorem us_top_sup (s : Ordinal.{0}) :
    (∀ z, z < S.psi (Om ω) (Om (s + 1)) → ∃ n : ℕ, z < S.psi (veblen 1 (Om (n : Ordinal.{0}) + 1)) (Om (s + 1))) ∧
      ∀ n : ℕ, S.psi (veblen 1 (Om (n : Ordinal.{0}) + 1)) (Om (s + 1)) < S.psi (Om ω) (Om (s + 1)) := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  refine ⟨fun z hz => ?_, fun n => psi_lt_psi_of_mem hκ (us_E_lt_OmW n) (us_E_mem n _ _)⟩
  rw [Lw.lw_psi_limit S hκ us_OmW_SC.isSuccLimit] at hz
  haveI : Nonempty (Iio (Om (ω : Ordinal.{0}))) := ⟨⟨0, us_OmW_SC.1⟩⟩
  have hbdd : BddAbove (range fun e : Iio (Om (ω : Ordinal.{0})) => S.psi e.1 (Om (s + 1))) :=
    ⟨Om (s + 1), by rintro _ ⟨e, rfl⟩; exact (psi_lt hκ _).le⟩
  obtain ⟨⟨e, he⟩, hze⟩ := (lt_ciSup_iff hbdd).1 hz
  obtain ⟨n, hn⟩ := Rx.rxOmW_nat he
  exact ⟨n, hze.trans_le (psi_mono hκ (hn.le.trans (us_lt_E n).le)).1⟩

end Googology.Trans.PoR.InaccPsi.R2.Us

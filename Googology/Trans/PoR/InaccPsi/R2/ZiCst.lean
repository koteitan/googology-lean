import Googology.Trans.PoR.InaccPsi.R2.ZdChainR

/-!
# COUNTABLE CONSTANTS: the coefficients `ξ < ψ_{Ω₁}(a₀)` of a shift

`Cl(a₀, 0) ∩ Ω₁ = ψ_{Ω₁}(a₀)` (`InaccSeq.CSet_inter_Om1`, Lemma L), so every `ξ < ψ_{Ω₁}(a₀)` lies in every closure
`Cl(a, b)` with `a ≥ a₀`.  Two bounds are used:

* `ziG S = ψ_{Ω₁}(0)`: every `ξ < ziG S` is in EVERY closure (the coefficients of the shifts `Ω_{k+3} + Ω₂·ξ` of
  `Zd.ZdSh`, which ask membership in every closure);
* `ziK3 S = ψ_{Ω₁}(Ω₃ + 1)`: every `ξ < ziK3 S` is in every closure `Cl(c, b)` with `c > Ω₃` (the coefficients of
  the relative shifts `Y₃ + Ω₂·ξ` of `Zd.ZdRS`).

Both are below `K = ψ_{Ω₁}(Ω_ω) ≤ ρ_λ` and below every `c_n` (`ziCst_lt_C`), so `B_n` fixes them and `Θ_λ` reads
them as themselves.

* `ziCst_mem`, `ziG_mem`, `ziK3_mem` (membership),
* `ziCst_lt_C`, `ziCst_le_rho`, `ziG_le_K3`, `ziK3_lt_Om1`, `ziEps0_lt_G` (bounds),
* `ziB_opowMul` (**`B_n(ω^p·ξ) = ω^p·ξ` for every `ξ < c_n`**; `Zd.zdB_opowMul` is `ξ < ε₀`),
* `ziVkA_opowMul` (**`ω^p·ξ` is a code of level `k` over `Q` for every `ξ < Q`**; `Zd.zdVkA_opowMul` is `ξ < ε₀`).

No new axiom.  New definitions: `ziG`, `ziK3` (abbreviations of the two bounds).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zi

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv

variable {S : InaccSeq.{0}}

/-- The bound `ψ_{Ω₁}(0)` (every smaller ordinal lies in every closure). -/
noncomputable def ziG (S : InaccSeq.{0}) : Ordinal.{0} := S.psi 0 (Om 1)

/-- The bound `ψ_{Ω₁}(Ω₃ + 1)` (every smaller ordinal lies in every closure `Cl(c, b)`, `c > Ω₃`). -/
noncomputable def ziK3 (S : InaccSeq.{0}) : Ordinal.{0} := S.psi (Om (1 + 1 + 1) + 1) (Om 1)

/-- **`ξ < ψ_{Ω₁}(a₀)` lies in every closure `Cl(a, b)` with `a₀ ≤ a`.** -/
theorem ziCst_mem {a₀ ξ : Ordinal.{0}} (h : ξ < S.psi a₀ (Om 1)) :
    ∀ a b : Ordinal.{0}, a₀ ≤ a → ξ ∈ S.CSet a b := by
  intro a b ha
  have h' : ξ ∈ S.CSet a₀ 0 ∩ Iio (Om 1) := by rw [InaccSeq.CSet_inter_Om1]; exact h
  exact CSet_mono ha zero_le h'.1

theorem ziG_mem {ξ : Ordinal.{0}} (h : ξ < ziG S) : ∀ a b : Ordinal.{0}, ξ ∈ S.CSet a b :=
  fun a b => ziCst_mem h a b zero_le

theorem ziK3_mem {ξ : Ordinal.{0}} (h : ξ < ziK3 S) :
    ∀ c b : Ordinal.{0}, Om (1 + 1 + 1) < c → ξ ∈ S.CSet c b :=
  fun c b hc => ziCst_mem h c b (Order.add_one_le_of_lt hc)

theorem ziPsi_le_K {a₀ : Ordinal.{0}} (h : a₀ ≤ Om ω) : S.psi a₀ (Om 1) ≤ Td.tdK S :=
  (psi_mono (S := S) Low.InR_Om_one h).1

theorem ziK3_le_K : ziK3 S ≤ Td.tdK S :=
  ziPsi_le_K ((Order.add_one_le_of_lt Ry.ryOm3_lt))

theorem ziG_le_K3 : ziG S ≤ ziK3 S := (psi_mono (S := S) Low.InR_Om_one zero_le).1

/-- **The constants are below every `c_n`** (so `B_n` fixes them). -/
theorem ziCst_lt_C {a₀ : Ordinal.{0}} (h : a₀ ≤ Om ω) (n : ℕ) : S.psi a₀ (Om 1) < Bc.bcC S n :=
  (ziPsi_le_K h).trans_lt (Td.tdK_lt_L _)

/-- **The constants are below every `ρ_λ`** (so `Θ_λ` reads them as themselves). -/
theorem ziCst_le_rho {a₀ l ηx : Ordinal.{0}} (h : a₀ ≤ Om ω) (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) :
    S.psi a₀ (Om 1) ≤ upsilon l :=
  (ziPsi_le_K h).trans (Td.tdK_le_rho hl hX)

theorem ziK3_lt_C (n : ℕ) : ziK3 S < Bc.bcC S n := ziCst_lt_C (Order.add_one_le_of_lt Ry.ryOm3_lt) n

theorem ziG_lt_C (n : ℕ) : ziG S < Bc.bcC S n := ziCst_lt_C zero_le n

theorem ziK3_lt_Om1 : ziK3 S < Om 1 := psi_lt Low.InR_Om_one _

theorem ziG_lt_Om1 : ziG S < Om 1 := psi_lt Low.InR_Om_one _

theorem ziK3_lt_Om2 : ziK3 S < Om (1 + 1) := ziK3_lt_Om1.trans (Om_lt_Om.2 (lt_add_one 1))

/-- `ε₀ < ψ_{Ω₁}(0)`: `ε₀ = φ(1, 0)` is in `Cl(0, 0)`, below `Ω₁`. -/
theorem ziEps0_lt_G : (ε₀ : Ordinal.{0}) < ziG S := by
  have hSC := Ph.ph_SC_Om1
  have hlt : (ε₀ : Ordinal.{0}) < Om 1 := by
    show veblen 1 0 < Om 1; exact hSC.2 1 (gg_one_lt_of_SC hSC) 0 hSC.1
  exact lt_psi_of_mem Low.InR_Om_one (CSet_mono le_rfl zero_le (Gc.gc_eps0_mem 0 0)) hlt

/-- **`B_n(ω^p·ξ) = ω^p·ξ` for every `ξ < c_n`** (`p` with `B_n p = p`). -/
theorem ziB_opowMul {n : ℕ} {p : Ordinal.{0}} (hpD : MvD S p) (hpB : Bc.bcB S n p = p) :
    ∀ ξ, ξ < Bc.bcC S n → MvD S (ω ^ p * ξ) ∧ Bc.bcB S n (ω ^ p * ξ) = ω ^ p * ξ := by
  have hcL : Bc.bcC S n < Nc.ncL S ω := Bc.bcC_lt S n
  intro ξ
  induction ξ using WellFoundedLT.induction with
  | ind ξ IH =>
  intro hξ
  rcases eq_or_ne ξ 0 with rfl | h0
  · rw [mul_zero]; exact ⟨vbD0, Bc.bcB_zero n⟩
  have hL : log ω ξ ≤ ξ := log_le_self ω ξ
  set a := log ω ξ with ha
  obtain ⟨m, hm⟩ := lt_omega0.1 (div_opow_log_lt ξ one_lt_omega0)
  have hdm : ξ = ω ^ a * m + ξ % ω ^ a := by rw [← hm]; exact (Ordinal.div_add_mod ξ _).symm
  have hrlt : ξ % ω ^ a < ξ :=
    (Ordinal.mod_lt ξ (opow_ne_zero _ omega0_ne_zero)).trans_le (opow_log_le_self ω h0)
  obtain ⟨hDr, hBr⟩ := IH _ hrlt (hrlt.trans hξ)
  have haD : MvD S a := mvD_of_lt ((hL.trans_lt hξ).trans hcL)
  have haB : Bc.bcB S n a = a := Bc.bcB_fix' S n a (hL.trans_lt hξ)
  obtain ⟨hDpa, hBpa⟩ := mvB_add (k := n) hpD haD
  rw [hpB, haB] at hBpa
  obtain ⟨hDo, hBo⟩ := ldB_opow (n := n) hDpa
  rw [hBpa] at hBo
  obtain ⟨hDom, hBom⟩ := vbB_mulNat (n := n) hDo m
  rw [hBo] at hBom
  have e1 : ω ^ p * ξ = ω ^ (p + a) * m + ω ^ p * (ξ % ω ^ a) := by
    conv_lhs => rw [hdm]
    rw [mul_add, ← mul_assoc, ← opow_add]
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDom hDr
  rw [hBom, hBr] at hBs
  rw [e1]
  exact ⟨hDs, hBs⟩

/-- **`ω^p·ξ` is a code of level `k` over `Q` for every `ξ < Q`** (`p` such a code). -/
theorem ziVkA_opowMul {k Q p : Ordinal.{0}} (hQ0 : 0 < Q) (hp : VkA k Q p) :
    ∀ ξ, ξ < Q → VkA k Q (ω ^ p * ξ) := by
  have hnat : ∀ x, VkA k Q x → ∀ m : ℕ, VkA k Q (x * m) := by
    intro x hx m
    induction m with
    | zero => rw [Nat.cast_zero, mul_zero]; exact VkA.small hQ0
    | succ m ih => rw [Nat.cast_succ, mul_add_one]; exact VkA.add ih hx
  intro ξ
  induction ξ using WellFoundedLT.induction with
  | ind ξ IH =>
  intro hξ
  rcases eq_or_ne ξ 0 with rfl | h0
  · rw [mul_zero]; exact VkA.small hQ0
  have hL : log ω ξ ≤ ξ := log_le_self ω ξ
  set a := log ω ξ with ha
  obtain ⟨m, hm⟩ := lt_omega0.1 (div_opow_log_lt ξ one_lt_omega0)
  have hdm : ξ = ω ^ a * m + ξ % ω ^ a := by rw [← hm]; exact (Ordinal.div_add_mod ξ _).symm
  have hrlt : ξ % ω ^ a < ξ :=
    (Ordinal.mod_lt ξ (opow_ne_zero _ omega0_ne_zero)).trans_le (opow_log_le_self ω h0)
  have e1 : ω ^ p * ξ = ω ^ (p + a) * m + ω ^ p * (ξ % ω ^ a) := by
    conv_lhs => rw [hdm]
    rw [mul_add, ← mul_assoc, ← opow_add]
  rw [e1]
  have hpa : VkA k Q (ω ^ (p + a)) := by
    rw [← veblen_zero_apply]
    exact VkA.phi (VkA.small hQ0) (VkA.add hp (VkA.small (hL.trans_lt hξ)))
  exact VkA.add (hnat _ hpa m) (IH _ hrlt (hrlt.trans hξ))

end Googology.Trans.PoR.InaccPsi.R2.Zi

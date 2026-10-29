import Googology.Trans.PoR.InaccPsi.R2.VpRun
import Googology.Trans.PoR.InaccPsi.R2.UzFV
import Googology.Trans.PoR.InaccPsi.R2.UwFC

/-!
# The atom move at `Ω₂` on `[Ω₁, θ)` from the move of the first values; first values from certificates

`W = Ω₂`, `V = Ω₃`, `ψ = ψ_{Ω₂}`, `Hˡ_γ = Ul.ulH S 1 γ`, `B_n = Bc.bcB S n`, `c' = c_{n+1} = Bc.bcC S (n + 1)`,
`K_q = Ul.UlK S 0 q`, `X = Tl.tlX`, `B₂ = Uc.ucB`, `θ = ConjT.th S`, `m(γ) = ulDat S Ω₂ γ`.  An atom
`z = Hˡ_γ(y) ∈ K_{c'} ∩ θ` (`y < z`) is `ψ(B + W^γ·D)` with `y = c + D` (`Vp.vp_dec`, `Vp.vp_run`), where `c = 0` or
`c = ψ(B)` is the largest fixed point of `Hˡ_γ` that is `≤ y`.  `B_n` moves the argument term by term
(`Ug.ugB_psi2`, `Vp.vpB_W`); a fixed point `ψ(B)` of `Hˡ_γ` goes to a fixed point of `Hˡ_{B_n γ}` by FWD and its
converse (`Us.us_fix_iff`) with the moves of divisibility, of `ψ_V` and of `K⁽¹⁾` (`Vp.vp_dvd_B`, `Ug.ugB_psi3`,
`Vp.vpK1_B`); the run of the image is computed again (`Vp.vp_valid`, `Us.us_run`).  Only the first value `Hˡ_γ(0)`
needs an extra fact:

* `VpFirst S` (**the first values move**: `B_n(Hˡ_γ(0)) = Hˡ_{B_n γ}(0)` for `0 < γ < V`, `Hˡ_γ(0) ∈ K_{c'} ∩ θ` with
  `Hˡ_γ(0) ∉ [X, B₂)`), `vpFirstMove` (**the first values move everywhere**: `γ = 0`, and `[X, B₂)` by
  `Vm.vmMoveLow`, from `VpFirst S`);
* `vpMove` (**the atom move on `[Ω₁, θ)`**: `B_n γ < V` and `B_n(Hˡ_γ(y)) = Hˡ_{B_n γ}(B_n y)` from `VpFirst S`),
  `vmAtom_of_first` (**`VpFirst S ⇒ Vm.VmAtomMove S`**);
* `VpCert S` (**every first value outside `[X, B₂)` has an own argument `B₀` with a certificate `Vp.VpCertCore`**, and
  a certificate `K` has its countable data within those of `γ`; a statement about `ψ` and `Hˡ` only, no `B_n`),
  `vpFirst_of_cert` (**`VpCert S ⇒ VpFirst S`**: the certificate moves with `B_n`, `Vp.vp_first_of_cert`).

No new axiom.  New definitions: `VpFirst`, `VpCert` (Props).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul Googology.Trans.PoR.InaccPsi.R2.Uo
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Mv

variable {S : InaccSeq.{0}}

theorem vp_hs1 : (1 : Ordinal.{0}) < ω := one_lt_omega0

theorem vp_c01 (n : ℕ) : Bc.bcC S (n + 1) ≤ Om (0 + 1) := by rw [zero_add]; exact Vm.vm_c_le n

theorem vp_cL (n : ℕ) : Bc.bcC S (n + 1) ≤ S.Lam := Us.us_qΛ (S := S) (i := 0) omega0_pos (vp_c01 n)

theorem vp_c_psi (n : ℕ) (x : Ordinal.{0}) : Bc.bcC S (n + 1) ≤ S.psi x (Om (1 + 1)) :=
  (Vm.vm_c_le n).trans (Ui.ui_L_lt_psi (s := 1) x).le

/-- **The first values move** (a hypothesis name): `B_n(Hˡ_γ(0)) = Hˡ_{B_n γ}(0)` for `0 < γ < V` with
`Hˡ_γ(0) ∈ K_{c_{n+1}} ∩ θ` outside `[X, B₂)`. -/
def VpFirst (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ γ, γ ≠ 0 → γ < Om (1 + 1 + 1) → ulH S 1 γ 0 < ConjT.th S →
    (ulH S 1 γ 0 < Tl.tlX ∨ ucB ≤ ulH S 1 γ 0) → UlK S 0 (Bc.bcC S (n + 1)) (ulH S 1 γ 0) →
      Bc.bcB S n (ulH S 1 γ 0) = ulH S 1 (Bc.bcB S n γ) 0

/-- **The first values move everywhere on `K_{c_{n+1}} ∩ θ`**, from `VpFirst S` (`γ = 0` and `[X, B₂)` need no
hypothesis). -/
theorem vpFirstMove (hF : VpFirst S) {n : ℕ} {γ : Ordinal.{0}} (hγ : γ < Om (1 + 1 + 1))
    (hθ : ulH S 1 γ 0 < ConjT.th S) (hK : UlK S 0 (Bc.bcC S (n + 1)) (ulH S 1 γ 0)) :
    Bc.bcB S n (ulH S 1 γ 0) = ulH S 1 (Bc.bcB S n γ) 0 := by
  rcases eq_or_ne γ 0 with rfl | hγ0
  · have hD0 : MvD S (0 : Ordinal.{0}) := Uf.ufD_zero
    obtain ⟨-, hB, -⟩ := Ug.ugB_psi2 (n := n) hD0 (CSet.zero_mem _ _)
    rw [Bc.bcB_zero, Us.us_psi0 vp_hs1, hB, Bc.bcB_zero]
  rcases lt_or_ge (ulH S 1 γ 0) Tl.tlX with hX | hX
  · exact hF n γ hγ0 hγ hθ (Or.inl hX) hK
  rcases lt_or_ge (ulH S 1 γ 0) ucB with hB | hB
  · have h := (Vm.vmMoveLow (n := n) hγ (ulH_SC γ 0).1 hX hB hK).2
    rw [Bc.bcB_zero] at h
    exact h
  · exact hF n γ hγ0 hγ hθ (Or.inr hB) hK

/-- **The atom move on `[Ω₁, θ)`** from `VpFirst S`: for `γ < V`, `y < Hˡ_γ(y) < θ`, `Hˡ_γ(y) ∈ K_{c_{n+1}}`:
`B_n γ < V` and `B_n(Hˡ_γ(y)) = Hˡ_{B_n γ}(B_n y)`. -/
theorem vpMove (hF : VpFirst S) {n : ℕ} {γ y : Ordinal.{0}} (hγ : γ < Om (1 + 1 + 1)) (hy : y < ulH S 1 γ y)
    (hθ : ulH S 1 γ y < ConjT.th S) (hK : UlK S 0 (Bc.bcC S (n + 1)) (ulH S 1 γ y)) :
    Bc.bcB S n γ < Om (1 + 1 + 1) ∧ Bc.bcB S n (ulH S 1 γ y) = ulH S 1 (Bc.bcB S n γ) (Bc.bcB S n y) := by
  have hs1 := vp_hs1
  have hq := Vm.vm_c_SC (S := S) n
  have hq1 := Vm.vm_c_le (S := S) n
  have hq01 := vp_c01 (S := S) n
  have hqL := vp_cL (S := S) n
  have hzW : ulH S 1 γ y < Om (1 + 1) := hθ.trans Vd.vd_th_lt_W
  obtain ⟨hγK, hyK⟩ := (Vd.vd_atom_K hγ hy hzW hq hq1).1 hK
  have hDγ := Vm.vm_D_of_K hγK
  have hDz := Vm.vm_D_of_K hK
  have hθA : ConjT.th S = S.psi (Om ω) (Om (1 + 1)) := rfl
  obtain ⟨B, c, D, hown, hc, hcD, hcond, hcase⟩ := vp_dec (S := S) (s := 1) hs1 hy (by rw [← hθA]; exact hθ)
  have hDy : D ≤ y := by rw [← hcD]; exact le_add_self
  have hcy : c ≤ y := by rw [← hcD]; exact le_self_add
  have hDW : D < Om (1 + 1) := (hDy.trans_lt hy).trans hzW
  obtain ⟨hψe, howne⟩ := vp_run (S := S) (s := 1) hs1 hγ hown hc hDW hcond
  rw [hcD] at hψe
  have heK : UlK S 0 (Bc.bcC S (n + 1)) (B + Om (1 + 1) ^ γ * D) :=
    uoArg hqL (InR_Om_succ 1) howne (by rw [hψe]; exact hK) (vp_c_psi n _)
  have h0θ : ulH S 1 γ 0 < ConjT.th S := ((ulH_le_iff γ).2 zero_le).trans_lt hθ
  have h0K : UlK S 0 (Bc.bcC S (n + 1)) (ulH S 1 γ 0) := Uz.uz_fv_K hs1 zero_lt_one hq hq01 hγ hγK
  -- the parts are in `K_{c'}`
  have hparts : UlK S 0 (Bc.bcC S (n + 1)) B ∧ UlK S 0 (Bc.bcC S (n + 1)) D ∧ UlK S 0 (Bc.bcC S (n + 1)) c := by
    rcases hcase with hc0 | ⟨hcf, hmax⟩
    · rw [hc0] at hc hcD
      rw [zero_add] at hcD
      refine ⟨uoArg hqL (InR_Om_succ 1) hown (by rw [← hc]; exact h0K) (vp_c_psi n B), by rw [hcD]; exact hyK,
        by rw [hc0]; exact UlK.zero⟩
    · have hcK : UlK S 0 (Bc.bcC S (n + 1)) c :=
        Uw.uw_fc_max hs1 zero_lt_one hq hq01 hγ hyK (hy.trans hzW) hcf hcy hmax
      refine ⟨uoArg hqL (InR_Om_succ 1) hown (by rw [← hc, hcf]; exact hcK) (vp_c_psi n B), ?_, hcK⟩
      have e : D = y - c := by rw [← hcD, Ordinal.add_sub_cancel]
      rw [e]; exact (ulK_dec hq y hyK).1 c hcK hcy
  obtain ⟨hBK, hDK, hcK⟩ := hparts
  have hDB := Vm.vm_D_of_K hBK
  have hDD := Vm.vm_D_of_K hDK
  have hDc := Vm.vm_D_of_K hcK
  have hDe := Vm.vm_D_of_K heK
  -- the image of the argument
  obtain ⟨hDWD, hBWD⟩ := vpB_W (n := n) hDγ hDD
  obtain ⟨-, hBe⟩ := mvB_add (k := n) hDB hDWD
  rw [hBWD] at hBe
  obtain ⟨-, hBz, hownBe⟩ := Ug.ugB_psi2 (n := n) hDe howne
  rw [hψe] at hBz
  rw [hBe] at hBz hownBe
  obtain ⟨hDψ, hBψB, hownB'⟩ := Ug.ugB_psi2 (n := n) hDB hown
  obtain ⟨hDψV, hBψV, -⟩ := Ug.ugB_psi3 (n := n) hDB (vp_ownV hown)
  -- `B_n γ < V`
  have hγψ : γ ≤ S.psi B (Om (1 + 1 + 1)) := Us.us_val_le hs1 hown hc
  have hγ'ψ : Bc.bcB S n γ ≤ S.psi (Bc.bcB S n B) (Om (1 + 1 + 1)) := by
    rw [← hBψV]; exact vpB_le hDγ hDψV hγψ
  have hγ'V : Bc.bcB S n γ < Om (1 + 1 + 1) := hγ'ψ.trans_lt (Ui.ui_psi_lt (s := 1 + 1) _)
  -- the image base
  have hbase : ulH S 1 (Bc.bcB S n γ) (Bc.bcB S n c) = S.psi (Bc.bcB S n B) (Om (1 + 1)) := by
    rcases hcase with hc0 | ⟨hcf, -⟩
    · rw [hc0] at hc ⊢
      rw [Bc.bcB_zero, ← vpFirstMove hF hγ h0θ h0K, hc, hBψB]
    · have hψc : S.psi B (Om (1 + 1)) = c := hc.symm.trans hcf
      have hfixB : ulH S 1 γ (S.psi B (Om (1 + 1))) = S.psi B (Om (1 + 1)) := by rw [hψc, hcf]
      have hB0 : B ≠ 0 := by
        rintro rfl
        have hp0 : S.psi 0 (Om (1 + 1)) = ulH S 1 0 0 := (Us.us_psi0 hs1).symm
        have hf0 : ulH S 1 0 (S.psi 0 (Om (1 + 1))) = S.psi 0 (Om (1 + 1)) :=
          ucG_fix_mono zero_le hfixB ((ulD_le_self 0).trans_lt (Ui.ui_psi_SC (s := 1) 0).1)
        rw [hp0] at hf0
        exact Us.us_val0_ne hf0
      obtain ⟨hdiv, hlt, hKγ⟩ := (Us.us_fix_iff hs1 hown hB0 hγ).1 hfixB
      have hDγ1 : MvD S (γ + 1) := (mvB_add (k := n) hDγ (Rk.rk_one_D (S := S))).1
      obtain ⟨hDW1, hBW1⟩ := vpB_Wpow (n := n) hDγ1
      have hdiv' : Om (1 + 1) ^ (Bc.bcB S n γ + 1) ∣ Bc.bcB S n B := by
        have h := vp_dvd_B (n := n) hDW1 (vp_W_indec _) (by rw [hBW1]; exact vp_W_indec _) hDB hdiv
        rwa [hBW1, Rk.rkB_succ hDγ] at h
      have hlt' : Bc.bcB S n γ < S.psi (Bc.bcB S n B) (Om (1 + 1 + 1)) := by
        rw [← hBψV]; exact (mvB_lt_iff hDγ hDψV).2 hlt
      have hK' : UlK S 1 (S.psi (Bc.bcB S n B) (Om (1 + 1))) (Bc.bcB S n γ) := by
        have h := vpK1_B (n := n) hDγ hDψ (Ui.ui_psi_SC (s := 1) B) (Ui.ui_L_lt_psi (s := 1) B)
          (Ui.ui_psi_lt (s := 1) B).le (by rw [hBψB]; exact Ui.ui_psi_SC (s := 1) _)
          (by rw [hBψB]; exact Ui.ui_L_lt_psi (s := 1) _) (by rw [hBψB]; exact (Ui.ui_psi_lt (s := 1) _).le)
        rw [hBψB] at h
        exact h.2 hKγ
      have hB'0 : Bc.bcB S n B ≠ 0 := by
        have h := (mvB_lt_iff (k := n) Uf.ufD_zero hDB).2 (pos_iff_ne_zero.2 hB0)
        rw [Bc.bcB_zero] at h
        exact h.ne'
      have hfix' := (Us.us_fix_iff hs1 hownB' hB'0 hγ'V).2 ⟨hdiv', hlt', hK'⟩
      have hBc : Bc.bcB S n c = S.psi (Bc.bcB S n B) (Om (1 + 1)) := by rw [← hψc, hBψB]
      rw [hBc, hfix']
  -- the run of the image
  have hdvd' : Om (1 + 1) ^ Bc.bcB S n γ ∣ Bc.bcB S n B := Us.us_dvd_val hs1 hownB' hbase
  have hv' : Bc.bcB S n D <
      S.psi (Bc.bcB S n B + Om (1 + 1) ^ Bc.bcB S n γ * Bc.bcB S n D) (Om (1 + 1)) := by
    rw [← hBz]; exact (mvB_lt_iff hDD hDz).2 (hDy.trans_lt hy)
  have hcond' := vp_valid (S := S) (s := 1) hs1 hdvd' hbase hv'
  have hD'W : Bc.bcB S n D < Om (1 + 1) := hv'.trans (Ui.ui_psi_lt (s := 1) _)
  have hrun := Us.us_run hs1 hγ'V hownB' hbase hD'W hcond'
  have hBy : Bc.bcB S n y = Bc.bcB S n c + Bc.bcB S n D := by rw [← hcD]; exact (mvB_add hDc hDD).2
  refine ⟨hγ'V, ?_⟩
  rw [hBz, hrun, hBy]

/-- **`VpFirst S ⇒ Vm.VmAtomMove S`** (the hypothesis (b) of `Vm.vmRoad`). -/
theorem vmAtom_of_first (hF : VpFirst S) : Vm.VmAtomMove S :=
  fun _ _ _ hγ hy _ hθ hK => vpMove hF hγ hy hθ hK

/-! ## First values from certificates -/

/-- **Certificates of the first values** (a hypothesis name, about `ψ` and `Hˡ` only): every first value
`Hˡ_γ(0) < θ` outside `[X, B₂)` (`0 < γ < V`, `γ` of the notation) is `ψ(B₀)` for an own `B₀` with `γ = ψ_V(B₀)`, or `B₀ = K + W^γ` for an
own `K` whose countable data are within those of `γ` and with `K = 0`, `ψ(K) ≤ m(γ)`, `ψ_V(K) < γ`, or `ψ_V(K) ≤ γ`
with `W^γ ∤ K`. -/
def VpCert (S : InaccSeq.{0}) : Prop :=
  ∀ γ, γ ≠ 0 → γ < Om (1 + 1 + 1) → γ ∈ ⋃ a, S.CSet a 0 → ulH S 1 γ 0 < ConjT.th S →
    (ulH S 1 γ 0 < Tl.tlX ∨ ucB ≤ ulH S 1 γ 0) → ∃ B0, B0 ∈ S.CSet B0 (S.psi B0 (Om (1 + 1))) ∧ S.psi B0 (Om (1 + 1)) = ulH S 1 γ 0 ∧
      (γ = S.psi B0 (Om (1 + 1 + 1)) ∨ ∃ K, B0 = K + Om (1 + 1) ^ γ ∧ K ∈ S.CSet K (S.psi K (Om (1 + 1))) ∧
        (∀ q, SC q → q ≤ Om 1 → UlK S 0 q γ → UlK S 0 q K) ∧
        (K = 0 ∨ S.psi K (Om (1 + 1)) ≤ ulDat S (Om (1 + 1)) γ ∨ S.psi K (Om (1 + 1 + 1)) < γ ∨
          (S.psi K (Om (1 + 1 + 1)) ≤ γ ∧ ¬ Om (1 + 1) ^ γ ∣ K)))

/-- **`VpCert S ⇒ VpFirst S`**: `B_n` moves the own argument `B₀` of a first value with its certificate, so its image
is the first value of `Hˡ_{B_n γ}` (`Vp.vp_val_of`, `Vp.vp_first_of_cert`). -/
theorem vpFirst_of_cert (hC : VpCert S) : VpFirst S := by
  intro n γ hγ0 hγV hθ hwin hK0
  have hs1 := vp_hs1
  have hq := Vm.vm_c_SC (S := S) n
  have hq1 := Vm.vm_c_le (S := S) n
  have hqL := vp_cL (S := S) n
  have hzW : ulH S 1 γ 0 < Om (1 + 1) := hθ.trans Vd.vd_th_lt_W
  have hγK : UlK S 0 (Bc.bcC S (n + 1)) γ := ((Vd.vd_atom_K hγV (ulH_SC γ 0).1 hzW hq hq1).1 hK0).1
  have hDγ := Vm.vm_D_of_K hγK
  obtain ⟨B0, hown, hB0, hcert⟩ := hC γ hγ0 hγV hDγ.1 hθ hwin
  have hB0K : UlK S 0 (Bc.bcC S (n + 1)) B0 :=
    uoArg hqL (InR_Om_succ 1) hown (by rw [hB0]; exact hK0) (vp_c_psi n B0)
  have hDB0 := Vm.vm_D_of_K hB0K
  obtain ⟨hDψ, hBψ, hown'⟩ := Ug.ugB_psi2 (n := n) hDB0 hown
  obtain ⟨hDψV, hBψV, -⟩ := Ug.ugB_psi3 (n := n) hDB0 (vp_ownV hown)
  have hvB : ulH S 1 γ 0 = S.psi B0 (Om (1 + 1)) := hB0.symm
  have hdvd : Om (1 + 1) ^ γ ∣ B0 := Us.us_dvd_val hs1 hown hvB
  have hγψ : γ ≤ S.psi B0 (Om (1 + 1 + 1)) := Us.us_val_le hs1 hown hvB
  have hKγ : UlK S 1 (S.psi B0 (Om (1 + 1))) γ :=
    (ul_vis (Ui.ui_psi_SC (s := 1) B0)).1 (by rw [← hvB]; exact ulH_D_lt γ 0)
  obtain ⟨hDWγ, hBWγ⟩ := vpB_Wpow (n := n) hDγ
  have hdvd' : Om (1 + 1) ^ Bc.bcB S n γ ∣ Bc.bcB S n B0 := by
    have h := vp_dvd_B (n := n) hDWγ (vp_W_indec _) (by rw [hBWγ]; exact vp_W_indec _) hDB0 hdvd
    rwa [hBWγ] at h
  have hγψ' : Bc.bcB S n γ ≤ S.psi (Bc.bcB S n B0) (Om (1 + 1 + 1)) := by
    rw [← hBψV]; exact vpB_le hDγ hDψV hγψ
  have hK' : UlK S 1 (S.psi (Bc.bcB S n B0) (Om (1 + 1))) (Bc.bcB S n γ) := by
    have h := vpK1_B (n := n) hDγ hDψ (Ui.ui_psi_SC (s := 1) B0) (Ui.ui_L_lt_psi (s := 1) B0)
      (Ui.ui_psi_lt (s := 1) B0).le (by rw [hBψ]; exact Ui.ui_psi_SC (s := 1) _)
      (by rw [hBψ]; exact Ui.ui_L_lt_psi (s := 1) _) (by rw [hBψ]; exact (Ui.ui_psi_lt (s := 1) _).le)
    rw [hBψ] at h
    exact h.2 hKγ
  have hpos : ∀ {x : Ordinal.{0}}, MvD S x → x ≠ 0 → Bc.bcB S n x ≠ 0 := fun hx hx0 => by
    have h := (mvB_lt_iff (k := n) Uf.ufD_zero hx).2 (pos_iff_ne_zero.2 hx0)
    rw [Bc.bcB_zero] at h
    exact h.ne'
  have hB'0 := hpos hDB0 (vp_B0_ne hs1 hγ0 hvB)
  have hγ'0 := hpos hDγ hγ0
  have hγ'V : Bc.bcB S n γ < Om (1 + 1 + 1) := hγψ'.trans_lt (Ui.ui_psi_lt (s := 1 + 1) _)
  have hval' := vp_val_of hs1 hown' hB'0 hγ'0 hγ'V hdvd' hγψ' hK'
  have hγ'N : Bc.bcB S n γ ∈ ⋃ a, S.CSet a 0 := by
    unfold Bc.bcB; exact mem_iUnion.2 (Term.exists_mem_CSet S _)
  have hcert' : VpCertCore S 1 (Bc.bcB S n γ) (Bc.bcB S n B0) := by
    rcases hcert with heq | ⟨K, hBK, hownK, hsupp, hK⟩
    · left
      rw [← hBψV, ← heq]
    · have hDK := Vm.vm_D_of_K (hsupp _ hq hq1 hγK)
      have hBB : Bc.bcB S n B0 = Bc.bcB S n K + Om (1 + 1) ^ Bc.bcB S n γ := by
        rw [hBK, (mvB_add (k := n) hDK hDWγ).2, hBWγ]
      obtain ⟨-, -, hownK'⟩ := Ug.ugB_psi2 (n := n) hDK hownK
      right
      refine ⟨Bc.bcB S n K, hBB, hownK', ?_⟩
      rcases hK with hK0 | hKm | hKV | ⟨hKV, hKd⟩
      · left; rw [hK0, Bc.bcB_zero]
      · right; left
        obtain ⟨hDψK, hBψK, -⟩ := Ug.ugB_psi2 (n := n) hDK hownK
        obtain ⟨hDd, hBd⟩ := vpDatW_B (n := n) hDγ
        rw [← hBψK, hBd]
        exact vpB_le hDψK hDd hKm
      · right; right; left
        obtain ⟨hDψK, hBψK, -⟩ := Ug.ugB_psi3 (n := n) hDK (vp_ownV hownK)
        rw [← hBψK]
        exact (mvB_lt_iff hDψK hDγ).2 hKV
      · right; right; right
        obtain ⟨hDψK, hBψK, -⟩ := Ug.ugB_psi3 (n := n) hDK (vp_ownV hownK)
        refine ⟨by rw [← hBψK]; exact vpB_le hDψK hDγ hKV, fun hd => hKd ?_⟩
        rw [← hBWγ] at hd
        exact (vp_dvd_B_iff (n := n) hDWγ (vp_W_indec _) (by rw [hBWγ]; exact vp_W_indec _) hDK).1 hd
  rw [hvB, hBψ]
  exact (vp_first_of_cert vp_hs1 hγ'0 hγ'N hown' hval' hcert').symm

end Googology.Trans.PoR.InaccPsi.R2.Vp

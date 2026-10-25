import Googology.Trans.PoR.InaccPsi.R2.UoDV

/-!
# The first value of a lifted level: `Hˡ_γ(0) = ψ_W(x)` for `γ = ψ_V(x)` (`V ∣ x`) and for `x = W^γ`

`W = Ω_{s+1}`, `V = Ω_{s+2}` (`s` finite), `ψ_π = S.psi · π`, `Hˡ_γ = Ul.ulH S s γ` (the lifted hierarchy, every
level `γ`), `K_q = Ul.UlK S s q`, *own at `W`*: `x ∈ Cl(x, ψ_W x)`.  The lifted levels `γ ≥ ε_{W+1}` are atoms
`ψ_V(x)`; their first value is read off the argument `x` of the atom:

* `us_K_Om` (`Ω_{r+1} ∈ K_q` at every threshold, `r` finite), `us_dig_exp` (**the exponent of a nonzero base-`Ω_{r+1}`
  digit of a member of `K_q` is in `K_q`**, at every threshold `t`, every finite `r`), `us_last` (**the last nonzero
  digit**: `W^k ∣ e`, `¬ W^{k+1} ∣ e` for some `k`), `us_dig_ne`, `us_W_V` (`W^V = V`), `us_W_dvd_V` (`W^j ∣ V` for
  `j ≤ V`), `us_psi0` (**`Hˡ_0(0) = ψ_W(0)`**);
* `us_bv` (**the first value**: for an own `x ≠ 0` and a level `0 < γ < V` with `W^γ ∣ x`, `γ ≤ ψ_V(x)`, `γ ∈
  K_{ψ_W x}`, and either `γ = ψ_V(x)` or `x ≤ W^γ`: `Hˡ_γ(0) = ψ_W(x)`), `us_bv_atom` (**`Hˡ_{ψ_V(x)}(0) = ψ_W(x)`**
  for an own `x ≠ 0` with `V ∣ x`), `us_bv_pow` (**`Hˡ_γ(0) = ψ_W(W^γ)`** for `0 < γ < V` with `γ ∈ Cl(W^γ,
  ψ_W(W^γ))` and `γ ≤ ψ_V(W^γ)`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Us

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul Googology.Trans.PoR.InaccPsi.R2.Uo
  Googology.Trans.PoR.InaccPsi.R2.Uc

variable {S : InaccSeq.{0}} {s : Ordinal.{0}}

/-! ## Digits -/

/-- `Ω_{r+1} ∈ K_q` at every threshold `t`, for a finite `r`. -/
theorem us_K_Om {t q r : Ordinal.{0}} (hr : r < ω) : UlK S t q (Om (r + 1)) := by
  obtain ⟨n, rfl⟩ := lt_omega0.1 hr
  have h : UlK S t q ((n : Ordinal.{0}) + 1) := by
    have := UlK.nat (S := S) (s := t) (q := q) (n + 1); rwa [Nat.cast_succ] at this
  exact UlK.om h

/-- **The exponent of a nonzero base-`Ω_{r+1}` digit of a member of `K_q` is in `K_q`** (any threshold `t`). -/
theorem us_dig_exp {t q r : Ordinal.{0}} (hr : r < ω) (hq : SC q) {x : Ordinal.{0}} (hx : UlK S t q x)
    (j : Ordinal.{0}) (hd : x / Om (r + 1) ^ j % Om (r + 1) ≠ 0) : UlK S t q j := by
  have hW0 : (Om (r + 1) : Ordinal.{0}) ≠ 0 := (Ui.ui_SC_W r).1.ne'
  have hWj0 : Om (r + 1) ^ j ≠ 0 := (Ui.ui_W_pos r j).ne'
  set y := x % Om (r + 1) ^ (j + 1) with hydef
  have hy : UlK S t q y := by rw [hydef, Ui.ui_W_eq r]; exact ulK_mod hq x hx _
  have hylt : y < Om (r + 1) ^ j * Om (r + 1) := by
    rw [← Ui.ui_W_succ r]; exact Ordinal.mod_lt _ (Ui.ui_W_pos r _).ne'
  have hyd : y / Om (r + 1) ^ j < Om (r + 1) := (Ordinal.lt_mul_iff_div_lt hWj0).1 hylt
  have hid : x / Om (r + 1) ^ j % Om (r + 1) = y / Om (r + 1) ^ j := by
    have e1 : x = Om (r + 1) ^ j * (Om (r + 1) * (x / Om (r + 1) ^ (j + 1))) + y := by
      rw [← mul_assoc, ← Ui.ui_W_succ r, hydef, Ordinal.div_add_mod]
    have e2 : x / Om (r + 1) ^ j = Om (r + 1) * (x / Om (r + 1) ^ (j + 1)) + y / Om (r + 1) ^ j := by
      conv_lhs => rw [e1]
      exact Ordinal.mul_add_div _ hWj0 _
    rw [e2, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hyd]
  rw [hid] at hd
  have hjy : Om (r + 1) ^ j ≤ y := by
    by_contra h; exact hd (Ordinal.div_eq_zero_of_lt (not_le.1 h))
  have hlog := (ulK_dec hq y hy).2
  have h1 : Om (r + 1) * j ≤ log ω y :=
    le_log_of_opow_le one_lt_omega0 (by rw [← Ui.ui_W_eq r]; exact hjy)
  have h2 : log ω y < Om (r + 1) * (j + 1) := by
    by_contra h
    have hc : Om (r + 1) * (j + 1) ≠ 0 := (mul_pos (Ui.ui_SC_W r).1 (lt_add_one_iff.2 zero_le)).ne'
    have := opow_le_of_le_log hc (not_lt.1 h)
    rw [← Ui.ui_W_eq r, Ui.ui_W_succ r] at this
    exact absurd hylt (not_lt.2 this)
  have hgj : log ω y / Om (r + 1) = j := by
    apply le_antisymm
    · have := (Ordinal.lt_mul_iff_div_lt hW0).1 h2
      exact Order.lt_add_one_iff.1 this
    · exact (Ordinal.mul_le_iff_le_div hW0).1 h1
  have := ulK_div hq _ hlog _ (us_K_Om (S := S) (t := t) (q := q) hr)
  rwa [Ui.ui_W_opow r, hgj] at this

/-- **The last nonzero digit**: a nonzero `e` has some `k` with `W^k ∣ e` and `¬ W^{k+1} ∣ e` (`1 < W`). -/
theorem us_last {W e : Ordinal.{0}} (hW : 1 < W) (he : e ≠ 0) :
    ∃ k : Ordinal.{0}, W ^ k ∣ e ∧ ¬ W ^ (k + 1) ∣ e := by
  set P : Set Ordinal.{0} := {k | ¬ W ^ k ∣ e} with hPdef
  have hne : P.Nonempty := by
    refine ⟨log W e + 1, fun hd => ?_⟩
    exact absurd (Ordinal.le_of_dvd he hd) (not_le.2 (lt_opow_succ_log_self hW e))
  set k0 := sInf P with hk0
  have hk0P : k0 ∈ P := csInf_mem hne
  have hbelow : ∀ k < k0, W ^ k ∣ e := fun k hk => by
    by_contra h; exact absurd (csInf_le' h : k0 ≤ k) (not_le.2 hk)
  rcases zero_or_succ_or_isSuccLimit k0 with h0 | ⟨k, hk⟩ | hlim
  · exact absurd (by rw [h0, opow_zero]; exact one_dvd e) hk0P
  · refine ⟨k, hbelow k ?_, ?_⟩
    · rw [← hk]; exact Order.lt_succ k
    · rw [← Order.succ_eq_add_one, hk]; exact hk0P
  · exfalso
    apply hk0P
    have hW0 : W ≠ 0 := (zero_lt_one.trans hW).ne'
    have hpos : W ^ k0 ≠ 0 := (opow_pos k0 (zero_lt_one.trans hW)).ne'
    have hm : e % W ^ k0 < W ^ k0 := Ordinal.mod_lt _ hpos
    obtain ⟨k, hk, hmk⟩ := (lt_opow_of_isSuccLimit hW0 hlim).1 hm
    have hdk : W ^ k ∣ e := hbelow k hk
    have hdk2 : W ^ k ∣ W ^ k0 * (e / W ^ k0) := (opow_dvd_opow W hk.le).trans (dvd_mul_right _ _)
    have hdm : W ^ k ∣ e % W ^ k0 := by
      have := hdk
      rw [← Ordinal.div_add_mod e (W ^ k0)] at this
      exact (Ordinal.dvd_add_iff hdk2).1 this
    have hm0 : e % W ^ k0 = 0 := by
      by_contra hne'
      exact absurd (Ordinal.le_of_dvd hne' hdm) (not_le.2 hmk)
    have e1 := Ordinal.div_add_mod e (W ^ k0)
    rw [hm0, add_zero] at e1
    rw [← e1]; exact dvd_mul_right _ _

/-- The digit at the last exponent is nonzero. -/
theorem us_dig_ne {W e k : Ordinal.{0}} (hk : W ^ k ∣ e) (hk1 : ¬ W ^ (k + 1) ∣ e) :
    e / W ^ k % W ≠ 0 := by
  intro h0
  apply hk1
  obtain ⟨c, hc⟩ := hk
  have hWk : W ^ k ≠ 0 := by
    intro h; rw [h, zero_mul] at hc
    exact hk1 (by rw [hc]; exact dvd_zero _)
  have hce : e / W ^ k = c := by rw [hc]; exact Ordinal.mul_div_cancel c hWk
  have e2 := Ordinal.div_add_mod c W
  rw [← hce, h0, add_zero, hce] at e2
  rw [hc, ← e2, ← mul_assoc, ← opow_succ]
  exact dvd_mul_right _ _

theorem us_W_V (s : Ordinal.{0}) : Om (s + 1) ^ Om (s + 1 + 1) = Om (s + 1 + 1) := by
  rw [Ui.ui_W_eq s]
  have hWV : Om (s + 1) < Om (s + 1 + 1) := Om_lt_Om.2 (Order.lt_add_one_iff.2 le_rfl)
  have hSC := Ui.ui_SC_W (s + 1)
  have hmul : Om (s + 1) * Om (s + 1 + 1) = Om (s + 1 + 1) := by
    conv_lhs => rw [← Ui.ui_W_opow s, ← Ui.ui_W_opow (s + 1)]
    have : Om (s + 1) + Om (s + 1 + 1) = Om (s + 1 + 1) :=
      Ordinal.add_of_omega0_opow_le (by rw [Ui.ui_W_opow (s + 1)]; exact hWV) (by rw [Ui.ui_W_opow (s + 1)])
    rw [← opow_add, this, Ui.ui_W_opow (s + 1)]
  rw [hmul, Ui.ui_W_opow (s + 1)]

theorem us_W_dvd_V (s : Ordinal.{0}) {j : Ordinal.{0}} (hj : j ≤ Om (s + 1 + 1)) :
    Om (s + 1) ^ j ∣ Om (s + 1 + 1) := by
  have := opow_dvd_opow (Om (s + 1)) hj
  rwa [us_W_V s] at this

/-- **`Hˡ_0(0) = ψ_W(0)`**: the least strongly critical ordinal above `Ω_s`. -/
theorem us_psi0 (hs : s < ω) : ulH S s 0 0 = S.psi 0 (Om (s + 1)) := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  have hSC0 : SC (S.psi 0 (Om (s + 1))) := Ui.ui_psi_SC 0
  have hL0 : Om s < S.psi 0 (Om (s + 1)) := Ui.ui_L_lt_psi 0
  apply le_antisymm
  · obtain ⟨o, ho⟩ := ucG_range (d := ulD S s) (L := Om s) (μ := 0) hSC0 hL0
      ((ulD_le_self 0).trans_lt hSC0.1) fun j hj => absurd hj (not_lt.2 zero_le)
    rw [← ho]; exact (ulH_le_iff (S := S) (s := s) 0).2 zero_le
  · have hv := ulH_SC (S := S) (s := s) 0 0
    have hLv := ulH_gt (S := S) (s := s) 0 0
    refine psi_le_of_good (Ui.ui_W_mem hs 0 _) fun y hy hyW => ?_
    have hK : UlK S s (ulH S s 0 0) y :=
      ulK_hull (a := 0) (fun e he => absurd he (not_lt.2 zero_le)) y hy
    exact ulK_lt_W hs hv hLv hK hyW

/-! ## The first value -/

/-- **The first value of a level from an own argument**: for an own `x ≠ 0` and a level `0 < γ < V` with `W^γ ∣ x`,
`γ ≤ ψ_V(x)`, `γ ∈ K_{ψ_W x}`, and either `γ = ψ_V(x)` or `x ≤ W^γ`: `Hˡ_γ(0) = ψ_W(x)`. -/
theorem us_bv (hs : s < ω) : ∀ x : Ordinal.{0}, x ∈ S.CSet x (S.psi x (Om (s + 1))) → x ≠ 0 →
    ∀ γ : Ordinal.{0}, γ ≠ 0 → γ < Om (s + 1 + 1) → Om (s + 1) ^ γ ∣ x → γ ≤ S.psi x (Om (s + 1 + 1)) →
      UlK S s (S.psi x (Om (s + 1))) γ → (γ = S.psi x (Om (s + 1 + 1)) ∨ x ≤ Om (s + 1) ^ γ) →
        ulH S s γ 0 = S.psi x (Om (s + 1)) := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  have hκV : S.InR (Om (s + 1 + 1)) := InR_Om_succ (s + 1)
  have hs1 : s + 1 < ω := Ui.ui_s1_lt_omega hs
  have hW1 : (1 : Ordinal.{0}) < Om (s + 1) := Ui.ui_one_lt_SC (Ui.ui_SC_W s)
  have hWV : Om (s + 1) < Om (s + 1 + 1) := Om_lt_Om.2 (Order.lt_add_one_iff.2 le_rfl)
  have hVR : Om (s + 1 + 1) ≠ Om (s + 1) := hWV.ne'
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hown hx0 γ hγ0 hγV hdvd hγψ hγK halt
  set b := S.psi x (Om (s + 1)) with hbdef
  have hbSC : SC b := Ui.ui_psi_SC x
  have hbL : Om s < b := Ui.ui_L_lt_psi x
  -- (i) `ψ_W(x)` is a value of `Hˡ_γ`
  have hrange : b ∈ range (ulH S s γ) := by
    refine ucG_range (d := ulD S s) (L := Om s) (μ := γ) hbSC hbL ((ul_vis hbSC).2 hγK) fun j hj hdj => ?_
    have hjK : UlK S s b j := (ul_vis hbSC).1 hdj
    have hjC : j ∈ S.CSet x b := uoDV hs x j hown hjK (hj.trans_le hγψ)
    have hdj : Om (s + 1) ^ (j + 1) ∣ x := (opow_dvd_opow _ (Order.add_one_le_of_lt hj)).trans hdvd
    exact uo_fwd hs j (hj.trans hγV) x hown hdj hx0 hjC
  have hle : ulH S s γ 0 ≤ b := by
    obtain ⟨o, ho⟩ := hrange
    rw [← ho]; exact (ulH_le_iff (S := S) (s := s) γ).2 zero_le
  refine le_antisymm hle (not_lt.1 fun hub => ?_)
  -- (ii) no smaller value
  set u := ulH S s γ 0 with hudef
  have huR : u ∈ range (ulH S s γ) := ⟨0, rfl⟩
  have huSC : SC u := ulH_SC γ 0
  have huL : Om s < u := ulH_gt γ 0
  have hfix : ∀ j < γ, ulD S s j < u → ulH S s j u = u := fun j hj hd => ucG_fix_lower hj huR hd
  have hinj : ∀ l, ulH S s l 0 = u → ulD S s l < u → l < γ → False := fun l h0 hd hl => by
    have h1 := hfix l hl hd
    rw [← h0] at h1
    have h2 : ulH S s l 0 < ulH S s l (ulH S s l 0) :=
      (ulH_lt_iff (S := S) (s := s) l).2 (ulH_SC l 0).1
    rw [h1] at h2
    exact lt_irrefl _ h2
  obtain ⟨e, hown_e, he⟩ := Ui.ui_own_of_SC hs huSC huL hub
  have hex : e < x := (Ui.ui_own_lt_iff hown_e hown).1 (by rw [he]; exact hub)
  have heK : UlK S s u e := by rw [← he]; exact ul_K_of_mem hown_e
  rcases eq_or_ne e 0 with he0 | he0
  · -- `u = ψ_W(0) = Hˡ_0(0)`, a value of `Hˡ_0` that is not a fixed point
    rw [he0] at he
    have h0 : ulH S s 0 0 = u := by rw [us_psi0 hs, he]
    exact hinj 0 h0 ((ulD_le_self 0).trans_lt huSC.1) (pos_iff_ne_zero.2 hγ0)
  obtain ⟨k, hk, hk1⟩ := us_last hW1 he0
  have hdig := us_dig_ne hk hk1
  have hkK : UlK S s u k := us_dig_exp hs huSC heK k hdig
  rcases lt_or_ge k γ with hkγ | hγk
  · -- a visible lower level `k` fixes `ψ_W(e)`: CONV gives `W^{k+1} ∣ e`
    have hf : ulH S s k (S.psi e (Om (s + 1))) = S.psi e (Om (s + 1)) := by
      rw [he]; exact hfix k hkγ ((ul_vis huSC).2 hkK)
    exact hk1 (ul_conv hs k e hown_e hf)
  rcases halt with hγeq | hxW
  · have hownV : e ∈ S.CSet e (S.psi e (Om (s + 1 + 1))) :=
      CSet_mono le_rfl (Ui.ui_psi_lt e |>.le.trans (psiS_bounds e (s + 1)).1.le) hown_e
    have hownxV : x ∈ S.CSet x (S.psi x (Om (s + 1 + 1))) :=
      CSet_mono le_rfl (Ui.ui_psi_lt x |>.le.trans (psiS_bounds x (s + 1)).1.le) hown
    have hVlt : S.psi e (Om (s + 1 + 1)) < S.psi x (Om (s + 1 + 1)) :=
      (Ui.ui_own_lt_iff hownV hownxV).2 hex
    rcases lt_or_ge k (Om (s + 1 + 1)) with hkV | hVk
    · -- `γ ≤ k < V`: the digit exponent `k` is visible one threshold up, so `k < ψ_V(e) < ψ_V(x) = γ`
      have heK1 : UlK S (s + 1) (S.psi e (Om (s + 1 + 1))) e := ul_K_of_mem hownV
      have hkK1 : UlK S (s + 1) (S.psi e (Om (s + 1 + 1))) k :=
        us_dig_exp hs (Ui.ui_psi_SC e) heK1 k hdig
      have hklt : k < S.psi e (Om (s + 1 + 1)) :=
        ulK_lt_W hs1 (Ui.ui_psi_SC e) (Ui.ui_L_lt_psi e) hkK1 hkV
      exact absurd ((hklt.trans hVlt).trans_eq hγeq.symm) (not_lt.2 hγk)
    · -- `V ≤ k`: `V ∣ e`, and the induction hypothesis makes `ψ_W(e) = Hˡ_{ψ_V(e)}(0)` a non-fixed value
      have hVe : Om (s + 1 + 1) ∣ e := by
        have := (opow_dvd_opow (Om (s + 1)) hVk).trans hk
        rwa [us_W_V s] at this
      have hlV : S.psi e (Om (s + 1 + 1)) < Om (s + 1 + 1) := Ui.ui_psi_lt e
      have hlK : UlK S s u (S.psi e (Om (s + 1 + 1))) :=
        UlK.coll hκV hVR (us_K_Om hs1) heK
      have hIH := IH e hex hown_e he0 _ (Ui.ui_psi_SC e).1.ne' hlV ((us_W_dvd_V s hlV.le).trans hVe) le_rfl
        (by rw [he]; exact hlK) (Or.inl rfl)
      rw [he] at hIH
      exact hinj _ hIH ((ul_vis huSC).2 hlK) (hVlt.trans_eq hγeq.symm)
  · -- `x ≤ W^γ`: then `k < γ`
    have hWk : Om (s + 1) ^ k ≤ e := Ordinal.le_of_dvd he0 hk
    have : Om (s + 1) ^ γ ≤ Om (s + 1) ^ k := opow_le_opow_right (Ui.ui_SC_W s).1 hγk
    exact absurd ((this.trans hWk).trans_lt (hex.trans_le hxW)) (lt_irrefl _)

/-- **`Hˡ_{ψ_V(x)}(0) = ψ_W(x)`** for an own `x ≠ 0` with `V ∣ x`: the first value of an atom level. -/
theorem us_bv_atom (hs : s < ω) {x : Ordinal.{0}} (hown : x ∈ S.CSet x (S.psi x (Om (s + 1)))) (hx0 : x ≠ 0)
    (hVx : Om (s + 1 + 1) ∣ x) : ulH S s (S.psi x (Om (s + 1 + 1))) 0 = S.psi x (Om (s + 1)) := by
  have hlV : S.psi x (Om (s + 1 + 1)) < Om (s + 1 + 1) := Ui.ui_psi_lt x
  have hK : UlK S s (S.psi x (Om (s + 1))) (S.psi x (Om (s + 1 + 1))) :=
    UlK.coll (InR_Om_succ (s + 1)) (Om_lt_Om.2 (Order.lt_add_one_iff.2 le_rfl)).ne'
      (us_K_Om (Ui.ui_s1_lt_omega hs)) (ul_K_of_mem hown)
  exact us_bv hs x hown hx0 _ (Ui.ui_psi_SC x).1.ne' hlV ((us_W_dvd_V s hlV.le).trans hVx) le_rfl hK
    (Or.inl rfl)

/-- **`Hˡ_γ(0) = ψ_W(W^γ)`** for a level `0 < γ < V` with `γ ∈ Cl(W^γ, ψ_W(W^γ))` and `γ ≤ ψ_V(W^γ)`. -/
theorem us_bv_pow (hs : s < ω) {γ : Ordinal.{0}} (hγ0 : γ ≠ 0) (hγV : γ < Om (s + 1 + 1))
    (hγC : γ ∈ S.CSet (Om (s + 1) ^ γ) (S.psi (Om (s + 1) ^ γ) (Om (s + 1))))
    (hγψ : γ ≤ S.psi (Om (s + 1) ^ γ) (Om (s + 1 + 1))) :
    ulH S s γ 0 = S.psi (Om (s + 1) ^ γ) (Om (s + 1)) := by
  have hown : Om (s + 1) ^ γ ∈ S.CSet (Om (s + 1) ^ γ) (S.psi (Om (s + 1) ^ γ) (Om (s + 1))) := by
    have := ul_Wpow_mem (S := S) hs hγC (CSet.one_mem _ _)
    rwa [mul_one] at this
  exact us_bv hs _ hown (Ui.ui_W_pos s γ).ne' γ hγ0 hγV dvd_rfl hγψ (ul_K_of_mem hγC) (Or.inr le_rfl)

end Googology.Trans.PoR.InaccPsi.R2.Us

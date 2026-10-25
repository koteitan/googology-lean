import Googology.Trans.PoR.InaccPsi.R2.UoK
import Googology.Trans.PoR.InaccPsi.R2.UlConv
import Googology.Trans.PoR.InaccPsi.R2.UlArgs
import Googology.Trans.PoR.InaccPsi.R2.TiDat

/-!
# The visibility closure read on normal forms, and its `B_n` move at `s = 0`

`W = Ω_{s+1}`, `L = Ω_s`, `K_q = Ul.UlK S s q`, `val = Term.val S`, `nf = Bc.bcNf S`, `ulDatT S W t` (the largest leaf
of `t` below `W`, subscripts included, `R2.UlCode`), `ulDat S W x = ulDatT S W (nf x)`; at `s = 0` it is `Ui.uiDat`.
`B_n = Bc.bcB S n = val ∘ σ ∘ nf`, `MvD` its normal-form domain.  For a member of the notation, membership in `K_q`
is read off the normal form (the K-version of `Ul.ul_code_iff`, with no argument condition), and at `s = 0` the datum
moves with `B_n` (the port of `Ti.tiDatT_sig` to the datum with subscripts):

* `uoK_veb` (**`φ(a, b) ∈ K_q` with `a, b < φ(a, b)` gives `a, b ∈ K_q`**), `uoK_Om` (**`Ω_σ ∈ K_q` gives `σ ∈ K_q`**),
  `uoK_lead_tail` (the leading summand and the rest of a member are members);
* `uo_K_code_mem` (**a term with all leaves below `W` below `q` denotes a member of `K_q`**), `uo_K_code_dat` (**a
  normal form denoting a member of `K_q` has all its leaves below `W` below `q`**), `uo_K_iff_dat` (**for `x` of the
  notation: `x ∈ K_q ↔ ulDat W x < q`**, `q` strongly critical, `L < q ≤ W`), `uo_vis_dat` (**`ulD x < v ↔ ulDat W x <
  v`**);
* `uoDatT_sig` (**`uiDatT (σ t) = B_n (uiDatT t)`** on the domain of `σ`), `uoDat_B` (**`uiDat (B_n x) = B_n (uiDat
  x)`** for `x ∈ MvD`), `uo_K_B` (**`B_n x ∈ K_{B_n q} ↔ x ∈ K_q`** at `s = 0`, for `x, q ∈ MvD`, `q`, `B_n q`
  countable strongly critical).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uo

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul
  Googology.Trans.PoR.InaccPsi.R2.Bc Googology.Trans.PoR.InaccPsi.R2.Mv

variable {S : InaccSeq.{0}} {s q : Ordinal.{0}}

/-! ## Reading members of `K_q` -/

/-- **`φ(a, b) ∈ K_q` with `a, b < φ(a, b)` gives `a, b ∈ K_q`.** -/
theorem uoK_veb {a b : Ordinal.{0}} (h : UlK S s q (veblen a b)) (ha : a < veblen a b) (hb : b < veblen a b) :
    UlK S s q a ∧ UlK S s q b := by
  suffices H : ∀ z, UlK S s q z → ∀ x y, z = veblen x y → x < z → y < z → UlK S s q x ∧ UlK S s q y from
    H _ h a b rfl ha hb
  intro z hz
  induction hz with
  | small h => intro x y _ hx hy; exact ⟨UlK.small (hx.trans h), UlK.small (hy.trans h)⟩
  | zero => intro x y e _ _; exact absurd e veblen_pos.ne
  | inacc n => intro x y e hx hy; exact absurd e.symm ((SC_I n).not_veblen_lt hx hy)
  | inaccW => intro x y e hx hy; exact absurd e.symm (SC_Iw.not_veblen_lt hx hy)
  | @add p r _ _ ihp ihr =>
    intro x y e hx hy
    have hP : IsPrincipal (· + ·) (p + r) := by rw [e]; exact veblen_isPrincipal x y
    by_cases hr0 : r = 0
    · subst hr0
      simp only [add_zero] at e hx hy
      exact ihp x y e hx hy
    · have hpz : p < p + r := lt_add_of_pos_right p (pos_iff_ne_zero.2 hr0)
      have hrz : r = p + r := le_antisymm le_add_self (not_lt.1 fun h => lt_irrefl _ (hP hpz h))
      rw [← hrz] at e hx hy
      exact ihr x y e hx hy
  | @phi p r hp hr ihp ihr =>
    intro x y e hx hy
    by_cases hpz : p = veblen p r
    · rw [← hpz] at e hx hy; exact ihp x y e hx hy
    by_cases hrz : r = veblen p r
    · rw [← hrz] at e hx hy; exact ihr x y e hx hy
    have hrl : r < veblen p r := lt_of_le_of_ne (right_le_veblen p r) hrz
    rcases veblen_eq_veblen_iff.1 e with ⟨rfl, rfl⟩ | ⟨_, h⟩ | ⟨_, h⟩
    · exact ⟨hp, hr⟩
    · rw [e, ← h] at hrl; exact absurd hrl (lt_irrefl _)
    · rw [h] at hy; exact absurd hy (lt_irrefl _)
  | @om p _ _ =>
    intro x y e hx hy
    by_cases hp0 : p = 0
    · rw [hp0, Om_zero] at e; exact absurd e veblen_pos.ne
    · exact absurd e.symm ((SC_Om hp0).not_veblen_lt hx hy)
  | @coll π e hπ _ _ _ _ _ =>
    intro x y ex hx hy
    exact absurd ex.symm ((SC_psi hπ e).not_veblen_lt hx hy)

/-- **`Ω_σ ∈ K_q` gives `σ ∈ K_q`.** -/
theorem uoK_Om {σ : Ordinal.{0}} (h : UlK S s q (Om σ)) : UlK S s q σ := by
  by_cases hσ0 : σ = 0
  · rw [hσ0]; exact UlK.zero
  suffices H : ∀ x, UlK S s q x → x = Om σ → UlK S s q σ from H _ h rfl
  intro x hx
  induction hx with
  | @small x hxb => intro e; exact UlK.small (lt_of_le_of_lt (le_Om σ) (e ▸ hxb))
  | zero => intro e; exact absurd e.symm (Om_pos hσ0).ne'
  | inacc n =>
    intro e
    rw [← Om_I n, Om_inj] at e
    rw [← e]; exact UlK.inacc n
  | inaccW =>
    intro e
    rw [← S.Om_Iw, Om_inj] at e
    rw [← e]; exact UlK.inaccW
  | @add x y _ _ ihx ihy =>
    intro e
    by_cases hy0 : y = 0
    · rw [hy0, add_zero] at e; exact ihx e
    · have hxlt : x < Om σ := by
        by_contra hxge
        have : x < x + y := lt_add_of_pos_right x (pos_iff_ne_zero.2 hy0)
        exact absurd e (lt_of_le_of_lt (not_lt.1 hxge) this).ne'
      rcases lt_or_ge y (Om σ) with hylt | hyge
      · exact absurd e ((SC_Om hσ0).isPrincipal hxlt hylt).ne
      · exact ihy (le_antisymm (e ▸ (le_add_left (le_refl y) : y ≤ x + y)) hyge)
  | @phi x y _ _ ihx ihy =>
    intro e
    rcases (SC_Om hσ0).eq_of_veblen_eq e with h' | h'
    · exact ihx h'
    · exact ihy h'
  | @om x hx _ =>
    intro e
    rw [← Om_inj.1 e]; exact hx
  | @coll π e hπ hπW hπK heK _ _ =>
    intro ex
    rcases hπ with ⟨m, rfl⟩ | ⟨t, rfl⟩
    · have h1 : Om (S.psi e (S.I m)) = Om σ := by rw [Om_psiI]; exact ex
      rw [← Om_inj.1 h1]; exact UlK.coll (InR_I m) hπW hπK heK
    · exact absurd ex (not_Om_of_between (psiS_bounds e t).1 (psiS_bounds e t).2 σ)

/-- **The leading summand and the rest of a member of `K_q` are members** (`q` strongly critical). -/
theorem uoK_lead_tail (hq : SC q) {x : Ordinal.{0}} (hx : UlK S s q x) (hx0 : x ≠ 0) :
    UlK S s q (lead x) ∧ UlK S s q (tail x) := by
  obtain ⟨hsub, hlog⟩ := ulK_dec hq x hx
  have hl : UlK S s q (lead x) := UlK.opow hlog
  exact ⟨hl, hsub _ hl (lead_le hx0)⟩

/-! ## The code test of `K_q` on normal forms -/

/-- **A term whose leaves below `W` (subscripts included) are below `q` denotes a member of `K_q`.** -/
theorem uo_K_code_mem : ∀ t : Term, ulDatT S (Om (s + 1)) t < q → UlK S s q (val S t) := by
  have hW : ∀ {σ a : Ordinal.{0}}, ¬ S.psi a (Om (σ + 1)) < Om (s + 1) → Om (σ + 1) ≠ Om (s + 1) :=
    fun h e => h (by rw [← e]; exact psi_lt (InR_Om_succ _) _)
  intro t
  induction t with
  | zero => intro _; exact UlK.zero
  | inacc n => intro _; exact UlK.inacc n
  | inaccW => intro _; exact UlK.inaccW
  | add a b iha ihb =>
    intro hd
    by_cases h : val S (add a b) < Om (s + 1)
    · rw [ulDatT_small h] at hd; exact UlK.small hd
    simp only [ulDatT, if_neg h] at hd
    exact UlK.add (iha (lt_of_le_of_lt (le_max_left _ _) hd)) (ihb (lt_of_le_of_lt (le_max_right _ _) hd))
  | phi a b iha ihb =>
    intro hd
    by_cases h : val S (phi a b) < Om (s + 1)
    · rw [ulDatT_small h] at hd; exact UlK.small hd
    simp only [ulDatT, if_neg h] at hd
    exact UlK.phi (iha (lt_of_le_of_lt (le_max_left _ _) hd)) (ihb (lt_of_le_of_lt (le_max_right _ _) hd))
  | om a iha =>
    intro hd
    by_cases h : val S (om a) < Om (s + 1)
    · rw [ulDatT_small h] at hd; exact UlK.small hd
    simp only [ulDatT, if_neg h] at hd
    exact UlK.om (iha hd)
  | psiS σ a ihs iha =>
    intro hd
    by_cases h : val S (psiS σ a) < Om (s + 1)
    · rw [ulDatT_small h] at hd; exact UlK.small hd
    simp only [ulDatT, if_neg h] at hd
    exact UlK.coll (InR_Om_succ _) (hW h) (UlK.om (UlK.add (ihs (lt_of_le_of_lt (le_max_left _ _) hd)) UlK.one))
      (iha (lt_of_le_of_lt (le_max_right _ _) hd))
  | psiI n a iha =>
    intro hd
    by_cases h : val S (psiI n a) < Om (s + 1)
    · rw [ulDatT_small h] at hd; exact UlK.small hd
    simp only [ulDatT, if_neg h] at hd
    exact UlK.coll (InR_I n) (uo_I_ne_W n) (UlK.inacc n) (iha hd)

/-- **A normal form denoting a member of `K_q` has all its leaves below `W` (subscripts included) below `q`**, for a
strongly critical `q` with `L < q ≤ W`. -/
theorem uo_K_code_dat (hs : s < ω) (hq : SC q) (hLq : Om s < q) (hqW : q ≤ Om (s + 1)) :
    ∀ t : Term, NF t → UlK S s q (val S t) → ulDatT S (Om (s + 1)) t < q := by
  have hqL : q ≤ S.Lam := hqW.trans (lt_Lam_of_mem zero_le (Ui.ui_W_mem (S := S) hs 0 0)).le
  have hcl : ∀ x, UlK S s q x → x < Om (s + 1) → x < q := fun x hx => ulK_lt_W hs hq hLq hx
  intro t
  induction t with
  | zero => intro _ _; exact hq.1
  | inacc n =>
    intro _ hm
    by_cases h : val S (inacc n) < Om (s + 1)
    · rw [ulDatT_small h]; exact hcl _ hm h
    · simp only [ulDatT, if_neg h]; exact hq.1
  | inaccW =>
    intro _ hm
    by_cases h : val S inaccW < Om (s + 1)
    · rw [ulDatT_small h]; exact hcl _ hm h
    · simp only [ulDatT, if_neg h]; exact hq.1
  | add a b iha ihb =>
    intro hN hm
    by_cases h : val S (add a b) < Om (s + 1)
    · rw [ulDatT_small h]; exact hcl _ hm h
    have h0 : val S (add a b) ≠ 0 := fun e => h (by rw [e]; exact (Ui.ui_SC_W s).1)
    obtain ⟨hl, ht⟩ := uoK_lead_tail hq hm h0
    obtain ⟨hla, htb⟩ := Ui.ui_add_parts (S := S) hN
    rw [hla] at hl; rw [htb] at ht
    simp only [ulDatT, if_neg h]
    exact max_lt (iha hN.1 hl) (ihb hN.2.1 ht)
  | phi a b iha ihb =>
    intro hN hm
    by_cases h : val S (phi a b) < Om (s + 1)
    · rw [ulDatT_small h]; exact hcl _ hm h
    have hN' := hN
    obtain ⟨hNa, hNb, hca, hcb⟩ := hN
    have hav : val S a < val S (phi a b) := by
      have e := Term.cmp_eq_compare S hNa hN'
      rw [e] at hca; exact compare_lt_iff_lt.1 hca
    have hbv : val S b < val S (phi a b) := by
      have e := Term.cmp_eq_compare S hNb hN'
      rw [e] at hcb; exact compare_lt_iff_lt.1 hcb
    obtain ⟨hma, hmb⟩ := uoK_veb hm hav hbv
    simp only [ulDatT, if_neg h]
    exact max_lt (iha hNa hma) (ihb hNb hmb)
  | om a iha =>
    intro hN hm
    by_cases h : val S (om a) < Om (s + 1)
    · rw [ulDatT_small h]; exact hcl _ hm h
    simp only [ulDatT, if_neg h]
    exact iha hN.1 (uoK_Om hm)
  | psiS σ a ihs iha =>
    intro hN hm
    by_cases h : val S (psiS σ a) < Om (s + 1)
    · rw [ulDatT_small h]; exact hcl _ hm h
    have hβz : q ≤ S.psi (val S a) (Om (val S σ + 1)) := hqW.trans (not_lt.1 h)
    have hsem := Term.sem_of_NF (S := S) hN
    have hma := uoArg hqL (InR_Om_succ _) hsem.2.2 hm hβz
    have hms := ulK_of_succ hq (uoK_Om (uoSub hqL (InR_Om_succ _) hsem.2.2 hm hβz))
    simp only [ulDatT, if_neg h]
    exact max_lt (ihs hN.1 hms) (iha hN.2.1 hma)
  | psiI n a iha =>
    intro hN hm
    by_cases h : val S (psiI n a) < Om (s + 1)
    · rw [ulDatT_small h]; exact hcl _ hm h
    have hβz : q ≤ S.psi (val S a) (S.I n) := hqW.trans (not_lt.1 h)
    have hsem := Term.sem_of_NF (S := S) hN
    simp only [ulDatT, if_neg h]
    exact iha hN.1 (uoArg hqL (InR_I n) hsem.2 hm hβz)

/-- **The code test of `K_q` at the threshold `W`**: for `x` of the notation, `q` strongly critical, `L < q ≤ W`:
`x ∈ K_q ↔ ulDat W x < q`. -/
theorem uo_K_iff_dat (hs : s < ω) (hq : SC q) (hLq : Om s < q) (hqW : q ≤ Om (s + 1)) {x : Ordinal.{0}}
    (hx : x ∈ ⋃ a, S.CSet a 0) : UlK S s q x ↔ ulDat S (Om (s + 1)) x < q := by
  obtain ⟨hN, hv⟩ := bcNf_spec S hx
  unfold ulDat
  constructor
  · intro h; rw [← hv] at h; exact uo_K_code_dat hs hq hLq hqW _ hN h
  · intro h; have := uo_K_code_mem (S := S) _ h; rwa [hv] at this

/-- **`ulD x < v ↔ ulDat W x < v`** for `x` of the notation and a strongly critical `v`, `L < v ≤ W`. -/
theorem uo_vis_dat (hs : s < ω) {v x : Ordinal.{0}} (hv : SC v) (hLv : Om s < v) (hvW : v ≤ Om (s + 1))
    (hx : x ∈ ⋃ a, S.CSet a 0) : ulD S s x < v ↔ ulDat S (Om (s + 1)) x < v := by
  rw [ul_vis hv]; exact uo_K_iff_dat hs hv hLv hvW hx

/-! ## The `B_n` move of the datum at `s = 0` -/

/-- **`uiDatT (σ t) = B_n (uiDatT t)`** on the domain `bcD` of `σ`, and the datum is in `MvD`. -/
theorem uoDatT_sig {n : ℕ} : ∀ t : Term, bcD S t →
    MvD S (Ui.uiDatT S t) ∧ Ui.uiDatT S (bcSig (bcPre (n + 1)) bcPreW t) = Bc.bcB S n (Ui.uiDatT S t) := by
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  have hD0 : MvD S 0 := mvD_of_term (S := S) bcD_zero
  have hsmall : ∀ t : Term, bcD S t → (val S (bcSig (bcPre (n + 1)) bcPreW t) < Om 1 ↔ val S t < Om 1) :=
    fun t hD => by
      have h := mvB_lt_iff (k := n) (mvD_of_term hD) hDO
      rw [hBO, mvB_term hD] at h
      exact h
  have hsm : ∀ t : Term, bcD S t → val S t < Om 1 →
      MvD S (Ui.uiDatT S t) ∧ Ui.uiDatT S (bcSig (bcPre (n + 1)) bcPreW t) = Bc.bcB S n (Ui.uiDatT S t) :=
    fun t hD h => by
      have h' := (hsmall _ hD).2 h
      rw [Ui.uiDatT_small h, Ui.uiDatT_small h', ← mvB_term (k := n) hD]; exact ⟨mvD_of_term hD, rfl⟩
  intro t
  induction t with
  | zero => intro _; exact ⟨hD0, by rw [bcSig_zero]; exact (Bc.bcB_zero n).symm⟩
  | inacc m =>
    intro hD
    by_cases h : val S (inacc m) < Om 1
    · exact hsm _ hD h
    · have e : Ui.uiDatT S (inacc m) = 0 := by simp only [Ui.uiDatT, if_neg h]
      rw [bcSig_inacc, e, Bc.bcB_zero]; exact ⟨hD0, rfl⟩
  | inaccW =>
    intro hD
    by_cases h : val S inaccW < Om 1
    · exact hsm _ hD h
    · have e : Ui.uiDatT S inaccW = 0 := by simp only [Ui.uiDatT, if_neg h]
      rw [bcSig_inaccW, e, Bc.bcB_zero]; exact ⟨hD0, rfl⟩
  | add a b iha ihb =>
    intro hD
    by_cases h : val S (add a b) < Om 1
    · exact hsm _ hD h
    · have h' : ¬ val S (bcSig (bcPre (n + 1)) bcPreW (add a b)) < Om 1 := fun h'' => h ((hsmall _ hD).1 h'')
      rw [bcSig_add] at h' ⊢
      obtain ⟨hDa, hσa⟩ := iha ⟨hD.1.1, hD.2.1⟩
      obtain ⟨hDb, hσb⟩ := ihb ⟨hD.1.2.1, hD.2.2⟩
      simp only [Ui.uiDatT, if_neg h, if_neg h']
      rw [hσa, hσb, Ti.tiB_max hDa hDb]
      exact ⟨Ti.tiMvD_max hDa hDb, rfl⟩
  | phi a b iha ihb =>
    intro hD
    by_cases h : val S (phi a b) < Om 1
    · exact hsm _ hD h
    · have h' : ¬ val S (bcSig (bcPre (n + 1)) bcPreW (phi a b)) < Om 1 := fun h'' => h ((hsmall _ hD).1 h'')
      rw [bcSig_phi] at h' ⊢
      obtain ⟨hDa, hσa⟩ := iha ⟨hD.1.1, hD.2.1⟩
      obtain ⟨hDb, hσb⟩ := ihb ⟨hD.1.2.1, hD.2.2⟩
      simp only [Ui.uiDatT, if_neg h, if_neg h']
      rw [hσa, hσb, Ti.tiB_max hDa hDb]
      exact ⟨Ti.tiMvD_max hDa hDb, rfl⟩
  | om a iha =>
    intro hD
    by_cases h : val S (om a) < Om 1
    · exact hsm _ hD h
    · have h' : ¬ val S (bcSig (bcPre (n + 1)) bcPreW (om a)) < Om 1 := fun h'' => h ((hsmall _ hD).1 h'')
      rw [bcSig_om] at h' ⊢
      obtain ⟨hDa, hσa⟩ := iha ⟨hD.1.1, hD.2⟩
      simp only [Ui.uiDatT, if_neg h, if_neg h']
      exact ⟨hDa, hσa⟩
  | psiS σ a ihs iha =>
    intro hD
    by_cases h : val S (psiS σ a) < Om 1
    · exact hsm _ hD h
    · have hs : σ ≠ Term.zero := by
        rintro rfl
        apply h
        show S.psi (val S a) (Om (val S Term.zero + 1)) < Om 1
        have e : val S Term.zero + 1 = 1 := by simp [val]
        rw [e]; exact psi_lt Low.InR_Om_one _
      have h' : ¬ val S (bcSig (bcPre (n + 1)) bcPreW (psiS σ a)) < Om 1 := fun h'' => h ((hsmall _ hD).1 h'')
      rw [bcSig_psiS_ne hs] at h' ⊢
      obtain ⟨hDs, hσs⟩ := ihs ⟨hD.1.1, hD.2.1⟩
      obtain ⟨hDa, hσa⟩ := iha ⟨hD.1.2.1, hD.2.2.1⟩
      simp only [Ui.uiDatT, if_neg h, if_neg h']
      rw [hσs, hσa, Ti.tiB_max hDs hDa]
      exact ⟨Ti.tiMvD_max hDs hDa, rfl⟩
  | psiI m a iha =>
    intro hD
    by_cases h : val S (psiI m a) < Om 1
    · exact hsm _ hD h
    · have h' : ¬ val S (bcSig (bcPre (n + 1)) bcPreW (psiI m a)) < Om 1 := fun h'' => h ((hsmall _ hD).1 h'')
      rw [bcSig_psiI] at h' ⊢
      obtain ⟨hDa, hσa⟩ := iha ⟨hD.1.1, hD.2⟩
      simp only [Ui.uiDatT, if_neg h, if_neg h']
      exact ⟨hDa, hσa⟩

/-- **`uiDat (B_n x) = B_n (uiDat x)`** for every `x ∈ MvD` (the visibility datum at `s = 0` moves with `B_n`). -/
theorem uoDat_B {n : ℕ} {x : Ordinal.{0}} (hx : MvD S x) :
    MvD S (Ui.uiDat S x) ∧ Ui.uiDat S (Bc.bcB S n x) = Bc.bcB S n (Ui.uiDat S x) := by
  have hN : NF (bcSig (bcPre (n + 1)) bcPreW (bcNf S x)) := bc_NF hx.2
  have e : bcNf S (Bc.bcB S n x) = bcSig (bcPre (n + 1)) bcPreW (bcNf S x) := by
    unfold Bc.bcB; exact bcNf_val S hN
  unfold Ui.uiDat
  rw [e]
  exact uoDatT_sig _ hx.2

/-- **`B_n x ∈ K_{B_n q} ↔ x ∈ K_q`** at `s = 0`, for `x, q ∈ MvD` with `q` and `B_n q` strongly critical and
`≤ Ω₁`. -/
theorem uo_K_B {n : ℕ} {x q : Ordinal.{0}} (hx : MvD S x) (hqD : MvD S q) (hq : SC q) (hq1 : q ≤ Om 1)
    (hBq : SC (Bc.bcB S n q)) (hBq1 : Bc.bcB S n q ≤ Om 1) :
    UlK S 0 (Bc.bcB S n q) (Bc.bcB S n x) ↔ UlK S 0 q x := by
  have hBx : Bc.bcB S n x ∈ ⋃ a, S.CSet a 0 := by
    unfold Bc.bcB; exact mem_iUnion.2 (Term.exists_mem_CSet S _)
  have h0 : Om (0 : Ordinal.{0}) < q := by rw [Om_zero]; exact hq.1
  have h0' : Om (0 : Ordinal.{0}) < Bc.bcB S n q := by rw [Om_zero]; exact hBq.1
  have hW : Om ((0 : Ordinal.{0}) + 1) = Om 1 := by rw [zero_add]
  rw [uo_K_iff_dat omega0_pos hBq h0' (hW ▸ hBq1) hBx, uo_K_iff_dat omega0_pos hq h0 (hW ▸ hq1) hx.1, hW,
    ul_one_ulDat, ul_one_ulDat]
  obtain ⟨hDd, hB⟩ := uoDat_B (n := n) hx
  rw [hB]
  exact mvB_lt_iff hDd hqD

end Googology.Trans.PoR.InaccPsi.R2.Uo

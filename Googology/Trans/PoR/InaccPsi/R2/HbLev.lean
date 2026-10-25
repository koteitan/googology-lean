import Googology.Trans.PoR.InaccPsi.R2.HaImg3
import Googology.Trans.PoR.InaccPsi.R2.HaWall

/-!
# HbLev: THE LEVEL FACTS WITH THE VEBLEN LEVEL A VARIABLE

`Ha.HaImgP` and `Ha.HaImg3` state the level facts for the Veblen levels `2` and `3` only.  Here every level
`k + 1` (`k : ℕ`) is a variable:

* `hb_evZ_lt_fix2`, `hb_evZ_notfix` (`evZ(u)` is never a fixed point of `φ(2,·)`);
* `hbN k Q` (**the least fixed point of `φ(k, ·)` above `Q`**), `hbN_fix`, `hbN_gt`, `hbN_le`, `hbN_mono`, `hbN1_eq`,
    `hbN2_eq`
  (`hbN 2 = Ha.haN`), `hb_fix_down`, `hb_LuP_of_fix`, `hb_fix_of_LuP`, `hbN_veb` (**`N_k(φ(k+1, a)) = φ(k+1, a+1)`**),
  `hb_floor` (**floor at every level**);
* at an `ε`-number base `x`: `hb_glA_succ` (**`ϑˣ(Ω₁·(k+1) + t + 1) = N_k(ϑˣ(Ω₁·(k+1) + t))`**), `hb_glA_base`
  (`ϑˣ(Ω₁·(k+1) + P) = N_k(P)` when every `ϑˣ(Ω₁·(k+1) + σ)`, `σ < P`, lies below `P`), `hb_low`, `hb_glA_fixP`
  (at a fixed point `P` of `φ(k+1, ·)`), `hb_glA_G` (at `P = Γ_{x+1}`), `hb_glAV` (**the closed form
  `ϑˣ(Ω₁·(k+1) + P + ν) = φ(k+1, i + ν)`**), `hb_nofixV` (**no fixed point of `φ(k+1,·)` in `[i, N_{k+1}(P))`**);
* `hb_cl_lev` (**a code in `[φ(k, j), φ(k, j+1))` has its index `j` as a code**, every level `k ≥ 1`).

No new axiom.  New definition: `hbN`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hb

open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The next fixed point at every level -/

/-- **`evZ(u) < Z`** for `u < Z`, `Z` a fixed point of `φ(2, ·)`. -/
theorem hb_evZ_lt_fix2 {u Z : Ordinal.{0}} (hZ : veblen 2 Z = Z) (hu : u < Z) : evZ u < Z := by
  have hZE : InE Z := ha_inE_of_fix2 hZ
  have h3 : evZ u ≤ veblen 2 (u + 1) :=
    evZ_le ((lt_add_one u).trans_le (right_le_veblen 2 _)) (veblen_veblen_of_lt one_lt_two _)
  have h4 := (isNormal_veblen 2).strictMono ((ev_isSuccLimit_of_inE hZE).add_one_lt hu)
  rw [hZ] at h4
  exact h3.trans_lt h4

/-- **`evZ(u)` is never a fixed point of `φ(2, ·)`.** -/
theorem hb_evZ_notfix (u : Ordinal.{0}) : veblen 2 (evZ u) ≠ evZ u := by
  intro e
  have hl : IsSuccLimit (evZ u) := ev_isSuccLimit_of_inE (evZ_E u)
  have hu : u < veblen 2 (evZ u) := by rw [e]; exact lt_evZ u
  obtain ⟨k, hk, huk⟩ := ((isNormal_veblen 2).lt_iff_exists_lt hl).1 hu
  have h1 := evZ_le huk (veblen_veblen_of_lt one_lt_two k)
  have h2 : veblen 2 k < veblen 2 (evZ u) := (isNormal_veblen 2).strictMono hk
  rw [e] at h2
  exact absurd (h1.trans_lt h2) (lt_irrefl _)



/-- **The least fixed point of `φ(k, ·)` above `Q`.** -/
noncomputable def hbN (k : ℕ) (Q : Ordinal.{0}) : Ordinal.{0} := nfp (veblen (k : Ordinal.{0})) (Q + 1)

theorem hbN_fix (k : ℕ) (Q : Ordinal.{0}) : veblen (k : Ordinal.{0}) (hbN k Q) = hbN k Q :=
  nfp_fp (isNormal_veblen _) _

theorem hbN_gt (k : ℕ) (Q : Ordinal.{0}) : Q < hbN k Q := (lt_add_one Q).trans_le (le_nfp _ _)

theorem hbN_le (k : ℕ) {Q j : Ordinal.{0}} (hj : veblen (k : Ordinal.{0}) j = j) (hQj : Q < j) : hbN k Q ≤ j :=
  nfp_le_fp (isNormal_veblen _).strictMono.monotone (Order.add_one_le_of_lt hQj) hj.le

theorem hbN_E (k : ℕ) (Q : Ordinal.{0}) : InE (hbN k Q) := by
  have h : veblen ((0 : ℕ) : Ordinal.{0}) (hbN k Q) = hbN k Q := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact hbN_fix 0 Q
    · have := veblen_veblen_of_lt (Nat.cast_lt.2 hk : ((0 : ℕ) : Ordinal.{0}) < (k : Ordinal.{0})) (hbN k Q)
      rwa [hbN_fix] at this
  rw [Nat.cast_zero, veblen_zero_apply] at h
  exact h

/-- **`N_j(Q) ≤ N_k(Q)`** for `j ≤ k`. -/
theorem hbN_mono {j k : ℕ} (hjk : j ≤ k) (Q : Ordinal.{0}) : hbN j Q ≤ hbN k Q := by
  refine hbN_le j ?_ (hbN_gt k Q)
  rcases hjk.lt_or_eq with h | rfl
  · have := veblen_veblen_of_lt (Nat.cast_lt.2 h : (j : Ordinal.{0}) < (k : Ordinal.{0})) (hbN k Q)
    rwa [hbN_fix] at this
  · exact hbN_fix j Q

/-- **`N_k(Q) < N_{k+1}(Q)`.** -/
theorem hbN_lt_succ (k : ℕ) (Q : Ordinal.{0}) : hbN k Q < hbN (k + 1) Q := by
  have h1 : hbN k Q ≤ veblen ((k + 1 : ℕ) : Ordinal.{0}) (Q + 1) :=
    hbN_le k (veblen_veblen_of_lt (Nat.cast_lt.2 (Nat.lt_succ_self k)) (Q + 1))
      ((lt_add_one Q).trans_le (right_le_veblen _ _))
  have h2 : Q + 1 < hbN (k + 1) Q := (ev_isSuccLimit_of_inE (hbN_E (k + 1) Q)).add_one_lt (hbN_gt _ Q)
  have h3 := (isNormal_veblen ((k + 1 : ℕ) : Ordinal.{0})).strictMono h2
  rw [hbN_fix] at h3
  exact h1.trans_lt h3

/-- **`N_1 = evZ`.** -/
theorem hbN1_eq (Q : Ordinal.{0}) : hbN 1 Q = evZ Q := by
  unfold hbN evZ; rw [Nat.cast_one]

theorem hb_nat_lt {j k : ℕ} (h : j < k) : (j : Ordinal.{0}) < (k : Ordinal.{0}) := Nat.cast_lt.2 h

theorem hb_cast_succ (k : ℕ) : ((k + 1 : ℕ) : Ordinal.{0}) = (k : Ordinal.{0}) + 1 := by push_cast; rfl

/-- **A fixed point of `φ(k, ·)` is a fixed point of every `φ(j, ·)`, `j ≤ k`.** -/
theorem hb_fix_down {j k : ℕ} (hjk : j ≤ k) {P : Ordinal.{0}} (hP : veblen (k : Ordinal.{0}) P = P) :
    veblen (j : Ordinal.{0}) P = P := by
  rcases hjk.lt_or_eq with h | rfl
  · have := veblen_veblen_of_lt (hb_nat_lt h) P; rwa [hP] at this
  · exact hP

theorem hb_LuP_of_fix (k : ℕ) {P : Ordinal.{0}} (hP : veblen (k : Ordinal.{0}) P = P) :
    LuP ((k + 1 : ℕ) : Ordinal.{0}) P := by
  unfold LuP
  rw [mem_range_veblen (by exact_mod_cast Nat.succ_ne_zero k)]
  intro b hb
  rcases lt_or_ge b (k : Ordinal.{0}) with hbk | hbk
  · have := veblen_veblen_of_lt hbk P; rwa [hP] at this
  · have : b = k := le_antisymm (Order.lt_add_one_iff.1 (by rw [← hb_cast_succ]; exact hb)) hbk
    rw [this]; exact hP

theorem hb_fix_of_LuP (k : ℕ) {P : Ordinal.{0}} (h : LuP ((k + 1 : ℕ) : Ordinal.{0}) P) :
    veblen (k : Ordinal.{0}) P = P := by
  obtain ⟨a, rfl⟩ := h
  exact veblen_veblen_of_lt (hb_nat_lt (Nat.lt_succ_self k)) a

theorem hb_fix_veb (k : ℕ) (a : Ordinal.{0}) :
    veblen (k : Ordinal.{0}) (veblen ((k + 1 : ℕ) : Ordinal.{0}) a) = veblen ((k + 1 : ℕ) : Ordinal.{0}) a :=
  veblen_veblen_of_lt (hb_nat_lt (Nat.lt_succ_self k)) a

/-- **`N_k(φ(k+1, a)) = φ(k+1, a+1)`.** -/
theorem hbN_veb (k : ℕ) (a : Ordinal.{0}) :
    hbN k (veblen ((k + 1 : ℕ) : Ordinal.{0}) a) = veblen ((k + 1 : ℕ) : Ordinal.{0}) (a + 1) := by
  have hlt : veblen ((k + 1 : ℕ) : Ordinal.{0}) a < veblen ((k + 1 : ℕ) : Ordinal.{0}) (a + 1) :=
    (isNormal_veblen _).strictMono (lt_add_one a)
  refine le_antisymm (hbN_le k (hb_fix_veb k (a + 1)) hlt) ?_
  obtain ⟨b, hb⟩ := hb_LuP_of_fix k (hbN_fix k (veblen ((k + 1 : ℕ) : Ordinal.{0}) a))
  have hab : veblen ((k + 1 : ℕ) : Ordinal.{0}) a < veblen ((k + 1 : ℕ) : Ordinal.{0}) b := by
    rw [hb]; exact hbN_gt k _
  rw [← hb]
  exact (isNormal_veblen _).monotone (Order.add_one_le_of_lt ((isNormal_veblen _).strictMono.lt_iff_lt.1 hab))

/-- **`N_2 = Ha.haN`.** -/
theorem hbN2_eq (Q : Ordinal.{0}) : hbN 2 Q = haN Q := by
  have e2 : ((2 : ℕ) : Ordinal.{0}) = 2 := by norm_num
  refine le_antisymm ?_ ?_
  · refine hbN_le 2 (by rw [e2]; exact haN_fix Q) ((lt_evZ Q).trans (haN_gt Q))
  · have hf : veblen 2 (hbN 2 Q) = hbN 2 Q := by have := hbN_fix 2 Q; rwa [e2] at this
    refine ha_fix_ge_N hf ?_
    have h1 : evZ Q ≤ hbN 2 Q := evZ_le (hbN_gt 2 Q) (ha_fix1_of_fix2 hf)
    refine lt_of_le_of_ne h1 fun e => ?_
    exact hb_evZ_notfix Q (by rw [e]; exact hf)

/-- **Every ordinal above a point of level `k` lies in some `[φ(k, j), φ(k, j+1))`.** -/
theorem hb_floor (k : Ordinal.{0}) {u j0 : Ordinal.{0}} (h0 : veblen k j0 ≤ u) :
    ∃ j, veblen k j ≤ u ∧ u < veblen k (j + 1) := by
  have hne : ({j | u < veblen k j} : Set Ordinal.{0}).Nonempty :=
    ⟨u + 1, (lt_add_one u).trans_le (right_le_veblen k _)⟩
  have hmS : u < veblen k (sInf {j | u < veblen k j}) := csInf_mem hne
  have hmin : ∀ j, j < sInf {j | u < veblen k j} → veblen k j ≤ u := fun j hj =>
    not_lt.1 (fun h => absurd (csInf_le' (s := {j | u < veblen k j}) h) (not_le.2 hj))
  rcases zero_or_succ_or_isSuccLimit (sInf {j | u < veblen k j}) with h0' | ⟨j, hj⟩ | hlim
  · exfalso
    rw [h0'] at hmS
    exact absurd (((isNormal_veblen k).monotone zero_le).trans h0) (not_le.2 hmS)
  · have hj' : sInf {j | u < veblen k j} = j + 1 := by rw [← hj, Order.succ_eq_add_one]
    exact ⟨j, hmin j (by rw [hj']; exact lt_add_one j), by rw [← hj']; exact hmS⟩
  · exfalso
    obtain ⟨a, ha, hua⟩ := ((isNormal_veblen k).lt_iff_exists_lt hlim).1 hmS
    exact absurd (hmin a ha) (not_le.2 hua)

/-! ## The `ϑ`-terms at every level -/

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem hb_lev_T (k : ℕ) : ((k : ℕ) : Ordinal.{0}) ∈ Tset x ∧ ((k : ℕ) : Ordinal.{0}) < Om1 :=
  gm1_T hx hx1 ((natCast_lt_omega0 k).trans (omega0_lt_inE (gm1_facts hx hx1).2.2.2))

omit hx hx1 in
theorem hb_one_le (k : ℕ) : (1 : Ordinal.{0}) ≤ ((k + 1 : ℕ) : Ordinal.{0}) := by
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)

/-- **`ϑˣ(Ω₁·(k+1) + t + 1) = N_k(ϑˣ(Ω₁·(k+1) + t))`**: the next point of Veblen level `k+1`. -/
theorem hb_glA_succ (k : ℕ) {t : Ordinal.{0}} (ht : t + 1 < gq 1 x) :
    glA ((k + 1 : ℕ) : Ordinal.{0}) (t + 1) x = hbN k (glA ((k + 1 : ℕ) : Ordinal.{0}) t x) := by
  have ht' : t < gq 1 x := (lt_add_one t).trans ht
  obtain ⟨htT, ht1⟩ := gm1_T hx hx1 ht'
  obtain ⟨hsT, hs1⟩ := gm1_T hx hx1 ht
  obtain ⟨hkT, hk1⟩ := hb_lev_T hx hx1 (k + 1)
  have h1k := hb_one_le k
  obtain ⟨-, hxa, -, -, hka, hta⟩ := glA_facts hx hx1 h1k hkT hk1 htT ht1
  set Q := glA ((k + 1 : ℕ) : Ordinal.{0}) t x with hQ
  have hNlim : IsSuccLimit (hbN k Q) := ev_isSuccLimit_of_inE (hbN_E k Q)
  have hQN : Q < hbN k Q := hbN_gt k Q
  refine le_antisymm ?_ ?_
  · refine glA_min hx hx1 h1k hkT hk1 hsT hs1 (hb_LuP_of_fix k (hbN_fix k Q)) (hxa.trans hQN)
      (hNlim.add_one_lt (hta.trans hQN)) (hka.trans hQN) (fun σ hσ => ?_)
    have hσt : σ ≤ t := Order.lt_add_one_iff.1 hσ
    obtain ⟨hσT, hσ1⟩ := gm1_T hx hx1 (lt_of_le_of_lt hσt ht')
    exact lt_of_le_of_lt ((glA_le_iff hx hx1 h1k hkT hk1 hσT hσ1 htT ht1).2 hσt) hQN
  · have hP := glA_P hx hx1 h1k hkT hk1 hsT hs1
    have hlt : Q < glA ((k + 1 : ℕ) : Ordinal.{0}) (t + 1) x :=
      glA_lt_of hx hx1 h1k hkT hk1 htT hsT hs1 (lt_add_one t)
    exact hbN_le k (hb_fix_of_LuP k hP) hlt

/-- **`ϑˣ(Ω₁·(k+1) + P) = N_k(P)`** when every `ϑˣ(Ω₁·(k+1) + σ)`, `σ < P`, lies below `P`. -/
theorem hb_glA_base (k : ℕ) {P : Ordinal.{0}} (hlow : ∀ σ, σ < P → glA ((k + 1 : ℕ) : Ordinal.{0}) σ x < P)
    (hxP : x < P) (hPq : P < gq 1 x) (hkP : ((k + 1 : ℕ) : Ordinal.{0}) < P) :
    glA ((k + 1 : ℕ) : Ordinal.{0}) P x = hbN k P := by
  obtain ⟨hPT, hP1⟩ := gm1_T hx hx1 hPq
  obtain ⟨hkT, hk1⟩ := hb_lev_T hx hx1 (k + 1)
  have h1k := hb_one_le k
  have hPN : P < hbN k P := hbN_gt k P
  refine le_antisymm ?_ ?_
  · exact glA_min hx hx1 h1k hkT hk1 hPT hP1 (hb_LuP_of_fix k (hbN_fix k P)) (hxP.trans hPN) hPN
      (hkP.trans hPN) (fun σ hσ => (hlow σ hσ).trans hPN)
  · obtain ⟨-, -, -, -, -, hta⟩ := glA_facts hx hx1 h1k hkT hk1 hPT hP1
    exact hbN_le k (hb_fix_of_LuP k (glA_P hx hx1 h1k hkT hk1 hPT hP1)) hta

/-- **`ϑˣ(Ω₁·(k+1) + σ) < P` for every `σ < P`**, `P ∈ (x, Γ_{x+2})` a fixed point of `φ(k+1, ·)`. -/
theorem hb_low (k : ℕ) {P : Ordinal.{0}} (hP : veblen ((k + 1 : ℕ) : Ordinal.{0}) P = P) (hxP : x < P)
    (hPq : P < gq 1 x) : ∀ σ, σ < P → glA ((k + 1 : ℕ) : Ordinal.{0}) σ x < P := by
  obtain ⟨hkT, hk1⟩ := hb_lev_T hx hx1 (k + 1)
  have h1k := hb_one_le k
  have hPE : InE P := by
    have h := hb_fix_down (Nat.zero_le (k + 1)) hP
    rw [Nat.cast_zero, veblen_zero_apply] at h; exact h
  have hP3 : LuP (((k + 1 : ℕ) : Ordinal.{0}) + 1) P := by rw [← hb_cast_succ]; exact hb_LuP_of_fix (k + 1) hP
  have hP2 : LuP ((k + 1 : ℕ) : Ordinal.{0}) P := hb_LuP_of_fix k (hb_fix_down (Nat.le_succ k) hP)
  have hkP : ((k + 1 : ℕ) : Ordinal.{0}) < P := (natCast_lt_omega0 _).trans (omega0_lt_inE hPE)
  intro σ
  induction σ using WellFoundedLT.induction with
  | ind σ IH =>
  intro hσ
  obtain ⟨hσT, hσ1⟩ := gm1_T hx hx1 (hσ.trans hPq)
  have hle : glA ((k + 1 : ℕ) : Ordinal.{0}) σ x ≤ P := glA_min hx hx1 h1k hkT hk1 hσT hσ1 hP2 hxP hσ hkP
    (fun σ' h' => IH σ' h' (h'.trans hσ))
  exact lt_of_le_of_ne hle (fun e => glA_notP hx hx1 h1k hkT hk1 hσT hσ1 (by rw [e]; exact hP3))

/-- **`ϑˣ(Ω₁·(k+1) + P) = N_k(P)`** at every fixed point `P ∈ (x, Γ_{x+2})` of `φ(k+1, ·)`. -/
theorem hb_glA_fixP (k : ℕ) {P : Ordinal.{0}} (hP : veblen ((k + 1 : ℕ) : Ordinal.{0}) P = P) (hxP : x < P)
    (hPq : P < gq 1 x) : glA ((k + 1 : ℕ) : Ordinal.{0}) P x = hbN k P := by
  have hPE : InE P := by
    have h := hb_fix_down (Nat.zero_le (k + 1)) hP
    rw [Nat.cast_zero, veblen_zero_apply] at h; exact h
  exact hb_glA_base hx hx1 k (hb_low hx hx1 k hP hxP hPq) hxP hPq ((natCast_lt_omega0 _).trans (omega0_lt_inE hPE))

/-- **`ϑˣ(Ω₁·(k+1) + Γ_{x+1}) = N_k(Γ_{x+1})`.** -/
theorem hb_glA_G (k : ℕ) : glA ((k + 1 : ℕ) : Ordinal.{0}) (lgG x) x = hbN k (lgG x) := by
  obtain ⟨-, hxG, -, hGE, -⟩ := lgG_facts hx hx1
  have hkG : ((k + 1 : ℕ) : Ordinal.{0}) < lgG x := (natCast_lt_omega0 _).trans (omega0_lt_inE hGE)
  exact hb_glA_base hx hx1 k (fun σ hσ => glA_lt_G hx hx1 hkG hσ) hxG (mg_lgG_lt_G1 hx hx1) hkG

/-- **`ϑˣ(Ω₁·(k+1) + P + ν) = φ(k+1, i + ν)`** (`ϑˣ(Ω₁·(k+1) + P) = φ(k+1, i)`) for every `ν` with
`P + ν < Γ_{x+2}` and no fixed point `i + ν'`, `ν' ≤ ν` a limit, of `φ(k+1, ·)`. -/
theorem hb_glAV (k : ℕ) {P i : Ordinal.{0}} (hPq : P < gq 1 x)
    (hG0 : glA ((k + 1 : ℕ) : Ordinal.{0}) P x = veblen ((k + 1 : ℕ) : Ordinal.{0}) i) : ∀ ν, P + ν < gq 1 x →
    (∀ ν', ν' ≤ ν → IsSuccLimit ν' → i + ν' < veblen ((k + 1 : ℕ) : Ordinal.{0}) (i + ν')) →
    glA ((k + 1 : ℕ) : Ordinal.{0}) (P + ν) x = veblen ((k + 1 : ℕ) : Ordinal.{0}) (i + ν) := by
  obtain ⟨hkT, hk1⟩ := hb_lev_T hx hx1 (k + 1)
  have h1k := hb_one_le k
  obtain ⟨hGT, hG1⟩ := gm1_T hx hx1 hPq
  intro ν
  induction ν using WellFoundedLT.induction with
  | ind ν IH =>
  intro hq hfix
  obtain ⟨htT, ht1⟩ := gm1_T hx hx1 hq
  rcases Ordinal.zero_or_succ_or_isSuccLimit ν with h0 | ⟨d, hd⟩ | hlim
  · subst h0; rw [add_zero, add_zero]; exact hG0
  · have hd' : ν = d + 1 := by rw [← succ_eq_add_one]; first | exact hd | exact hd.symm
    subst hd'
    have hdq : P + d < gq 1 x := lt_of_le_of_lt (add_le_add le_rfl le_self_add) hq
    have IHd := IH d (lt_add_one d) hdq (fun ν' h hl => hfix ν' (h.trans le_self_add) hl)
    rw [← add_assoc] at hq ⊢
    rw [hb_glA_succ hx hx1 k hq, IHd, ← add_assoc, hbN_veb]
  · have hval : ∀ ν'', ν'' < ν → glA ((k + 1 : ℕ) : Ordinal.{0}) (P + ν'') x =
        veblen ((k + 1 : ℕ) : Ordinal.{0}) (i + ν'') := fun ν'' h =>
      IH ν'' h ((add_lt_add_iff_left _).2 h |>.trans hq) (fun ν' h' hl => hfix ν' (h'.trans h.le) hl)
    set u := veblen ((k + 1 : ℕ) : Ordinal.{0}) (i + ν) with hu
    have huE : InE u := gg_veblen_eps (by exact_mod_cast Nat.succ_ne_zero k)
    have hiu : veblen ((k + 1 : ℕ) : Ordinal.{0}) i < u :=
      (isNormal_veblen _).strictMono (lt_add_of_pos_right _ hlim.bot_lt)
    obtain ⟨-, hxa, -, -, h2a, hGa⟩ := glA_facts hx hx1 h1k hkT hk1 hGT hG1
    rw [hG0] at hxa h2a hGa
    have htu : P + ν < u := (inE_indec huE).add_lt (hGa.trans hiu)
      ((le_add_self : ν ≤ i + ν).trans_lt (hfix ν le_rfl hlim))
    refine le_antisymm ?_ ?_
    · refine glA_min hx hx1 h1k hkT hk1 htT ht1 ⟨_, rfl⟩ (hxa.trans hiu) htu (h2a.trans hiu) (fun σ hσ => ?_)
      rcases lt_or_ge σ P with hσP | hσP
      · obtain ⟨hσT, hσ1⟩ := gm1_T hx hx1 (hσP.trans hPq)
        have := glA_lt_of hx hx1 h1k hkT hk1 hσT hGT hG1 hσP
        rw [hG0] at this
        exact this.trans hiu
      · obtain ⟨ν'', rfl⟩ := exists_add_of_le hσP
        have hν'' : ν'' < ν := (add_lt_add_iff_left _).1 hσ
        rw [hval ν'' hν'']
        exact (isNormal_veblen _).strictMono ((add_lt_add_iff_left _).2 hν'')
    · refine ((isNormal_veblen _).le_iff_forall_le (isSuccLimit_add _ hlim)).2 fun c hc => ?_
      rcases lt_or_ge c i with hci | hci
      · refine ((isNormal_veblen _).strictMono hci).le.trans ?_
        rw [← hG0]
        exact (glA_le_iff hx hx1 h1k hkT hk1 hGT hG1 htT ht1).2 le_self_add
      · obtain ⟨c', rfl⟩ := exists_add_of_le hci
        have hc' : c' < ν := (add_lt_add_iff_left _).1 hc
        have hq' : P + c' < gq 1 x := ((add_lt_add_iff_left _).2 hc').trans hq
        obtain ⟨hcT, -⟩ := gm1_T hx hx1 hq'
        rw [← hval c' hc']
        exact (glA_lt_of hx hx1 h1k hkT hk1 hcT htT ht1 ((add_lt_add_iff_left _).2 hc')).le

end Base

/-- **No fixed point of `φ(k+1, ·)` in `[i, N_{k+1}(P))`** when `φ(k+1, i) = N_k(P)`. -/
theorem hb_nofixV (k : ℕ) {P i j : Ordinal.{0}} (hi : veblen ((k + 1 : ℕ) : Ordinal.{0}) i = hbN k P) (hij : i ≤ j)
    (hjB : veblen ((k + 1 : ℕ) : Ordinal.{0}) j < hbN (k + 1) P) : j < veblen ((k + 1 : ℕ) : Ordinal.{0}) j := by
  rcases (right_le_veblen _ j).lt_or_eq with h | h
  · exact h
  · exfalso
    have hPj : P < j := by
      have h1 : hbN k P ≤ veblen ((k + 1 : ℕ) : Ordinal.{0}) j := by rw [← hi]; exact (isNormal_veblen _).monotone hij
      rw [← h] at h1
      exact (hbN_gt k P).trans_le h1
    have := hbN_le (k + 1) h.symm hPj
    exact absurd hjB (not_lt.2 (this.trans h.le))

/-! ## Codes at every level -/

/-- **A code in `[φ(k, j), φ(k, j+1))` has its index `j` as a code** (`1 ≤ k`, `j < φ(k, j)`, `G < φ(k, j)`). -/
theorem hb_cl_lev {k : ℕ} (hk : 1 ≤ k) {Z j : Ordinal.{0}} (hZ1 : Z ≤ Om 1) (hj : j < veblen (k : Ordinal.{0}) j)
    (hGQ : gcG 0 < veblen (k : Ordinal.{0}) j) {y : Ordinal.{0}} (hy : GxCl Z {gcG 0} y)
    (hQy : veblen (k : Ordinal.{0}) j ≤ y) (hyZ : y < veblen (k : Ordinal.{0}) (j + 1)) : GxCl Z {gcG 0} j := by
  have hFE : InE (veblen (k : Ordinal.{0}) j) := gg_veblen_eps (by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hk))
  have hOF : Om 1 < veblen (k : Ordinal.{0}) j := (gcG_Om1_lt 0).trans hGQ
  induction hy with
  | small h => exact absurd (hQy.trans_lt (h.trans_le hZ1)) (not_lt.2 hOF.le)
  | om => exact absurd hQy (not_le.2 hOF)
  | atom h =>
    rw [Set.mem_singleton_iff] at h
    rw [h] at hQy; exact absurd hQy (not_le.2 hGQ)
  | @add u v hu hv ihu ihv =>
    rcases le_or_gt (veblen (k : Ordinal.{0}) j) u with hFu | huF
    · exact ihu hFu (lt_of_le_of_lt le_self_add hyZ)
    · rcases le_or_gt (veblen (k : Ordinal.{0}) j) v with hFv | hvF
      · exact ihv hFv (lt_of_le_of_lt le_add_self hyZ)
      · exact absurd hQy (not_le.2 ((inE_indec hFE).add_lt huF hvF))
  | @phi a b ha hb iha ihb =>
    have hbyZ : b < veblen (k : Ordinal.{0}) (j + 1) := lt_of_le_of_lt (right_le_veblen a b) hyZ
    rcases lt_or_ge a (k : Ordinal.{0}) with hak | hak
    · refine ihb ?_ hbyZ
      refine not_lt.1 fun hbF => ?_
      have hlt : veblen a b < veblen (k : Ordinal.{0}) j := by
        have h1 : veblen a b < veblen a (veblen (k : Ordinal.{0}) j) := (isNormal_veblen a).strictMono hbF
        rwa [veblen_veblen_of_lt hak] at h1
      exact absurd hQy (not_le.2 hlt)
    · rcases hak.lt_or_eq with hak' | hak'
      · exfalso
        have e3 : veblen (k : Ordinal.{0}) (veblen a b) = veblen a b := veblen_veblen_of_lt hak' b
        have h1 : j ≤ veblen a b := by
          have : veblen (k : Ordinal.{0}) j ≤ veblen (k : Ordinal.{0}) (veblen a b) := by rw [e3]; exact hQy
          exact (isNormal_veblen _).strictMono.le_iff_le.1 this
        have h2 : veblen a b < j + 1 := by
          have : veblen (k : Ordinal.{0}) (veblen a b) < veblen (k : Ordinal.{0}) (j + 1) := by rw [e3]; exact hyZ
          exact (isNormal_veblen _).strictMono.lt_iff_lt.1 this
        have e : veblen a b = j := le_antisymm (Order.lt_add_one_iff.1 h2) h1
        have : veblen (k : Ordinal.{0}) j = j := by rw [← e]; exact e3
        exact absurd this hj.ne'
      · subst hak'
        have h1 : j ≤ b := (isNormal_veblen _).strictMono.le_iff_le.1 hQy
        have h2 : b < j + 1 := (isNormal_veblen _).strictMono.lt_iff_lt.1 hyZ
        have : b = j := le_antisymm (Order.lt_add_one_iff.1 h2) h1
        rw [← this]; exact hb

end Googology.Trans.PoR.InaccPsi.R2.Hb

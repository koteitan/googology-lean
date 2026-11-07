import Googology.Trans.PoR.InaccPsi.R2.KzOff
import Googology.Trans.PoR.InaccPsi.R2.KzAdd
import Googology.Trans.PoR.InaccPsi.R2.QtK

/-!
# Fa: THE VISIBILITY CLOSURE ONE CARDINAL DOWN

`T = Kz.vbTK S λ K` on `D_K`, `K⁽ˢ⁾_q = Ul.UlK S s q`.

* `fa_Om_D`, `fa_T_Om`, `fa_q_facts` (`T q` is strongly critical in `(Ω_k, Ω_{k+1}]` for a strongly critical
  `q ∈ (Ω_{k+1}, Ω_{k+2}]`);
* `faK_iff` (**`x ∈ K⁽ᵏ⁺¹⁾_q ⇔ T x ∈ K⁽ᵏ⁾_{T q}`**, `k ≥ 1`, `x, q ∈ D_K`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Fa

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rx Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Kz Googology.Trans.PoR.InaccPsi.R2.Ul

variable {S : InaccSeq.{0}}

theorem fa_nat1_lt (k : ℕ) : (k : Ordinal.{0}) + 1 < ω := by
  have := natCast_lt_omega0 (k + 1); rwa [Nat.cast_succ] at this

theorem fa_nat2_lt (k : ℕ) : (k : Ordinal.{0}) + 1 + 1 < ω := by
  have := natCast_lt_omega0 (k + 1 + 1); rwa [Nat.cast_succ, Nat.cast_succ] at this

section Rst

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) {K : Ordinal.{0}} (hKB : KzB S K)

/-- `Ω_j ∈ D_K` for finite `j`. -/
theorem fa_Om_D (hKB : KzB S K) (j : ℕ) : VbDK S l K (Om (j : Ordinal.{0})) :=
  ⟨rxC_Om_nat _ _ j, rxC_Om_nat _ _ j, (Om_lt_Om.2 (natCast_lt_omega0 j)).trans_le hKB.ge⟩

theorem fa_Om1_D (hKB : KzB S K) (k : ℕ) : VbDK S l K (Om ((k : Ordinal.{0}) + 1)) := by
  have := fa_Om_D (S := S) (l := l) hKB (k + 1); rwa [Nat.cast_succ] at this

theorem fa_Om2_D (hKB : KzB S K) (k : ℕ) : VbDK S l K (Om ((k : Ordinal.{0}) + 1 + 1)) := by
  have := fa_Om1_D (S := S) (l := l) hKB (k + 1); rwa [Nat.cast_succ] at this

include hl hX hKB

theorem fa_T_Om2 {k : ℕ} : vbTK S l K (Om ((k : Ordinal.{0}) + 1 + 1)) = Om ((k : Ordinal.{0}) + 1) := by
  have h := vbTK_Om (S := S) hl hX hKB (k := k + 1) (by omega)
  rwa [Nat.cast_succ] at h

/-- **`T q` is strongly critical in `(Ω_k, Ω_{k+1}]`.** -/
theorem fa_q_facts {k : ℕ} (hk : 1 ≤ k) {q : Ordinal.{0}} (hqD : VbDK S l K q) (hqS : SC q)
    (h1 : Om ((k : Ordinal.{0}) + 1) < q) (h2 : q ≤ Om ((k : Ordinal.{0}) + 1 + 1)) :
    SC (vbTK S l K q) ∧ Om (k : Ordinal.{0}) < vbTK S l K q ∧ vbTK S l K q ≤ Om ((k : Ordinal.{0}) + 1) := by
  have hk1 : (1 : Ordinal.{0}) ≤ k := by exact_mod_cast hk
  have h20 : Om (1 + 1 : Ordinal.{0}) ≤ q :=
    (Om_le_Om.2 (add_le_add hk1 le_rfl)).trans h1.le
  refine ⟨vbTK_SC hl hX hKB hqD h20 hqS, ?_, ?_⟩
  · have h := vbTK_mono hl hX hKB (fa_Om1_D hKB k) hqD h1
    rwa [vbTK_Om hl hX hKB hk] at h
  · have h := (vbTK_le_iff hl hX hKB hqD (fa_Om2_D hKB k)).1 h2
    rwa [fa_T_Om2 hl hX hKB] at h

/-- **`x ∈ K⁽ᵏ⁺¹⁾_q ⇔ T x ∈ K⁽ᵏ⁾_{T q}`** (`k ≥ 1`). -/
theorem faK_iff {k : ℕ} (hk : 1 ≤ k) {q : Ordinal.{0}} (hqD : VbDK S l K q) (hqS : SC q)
    (h1 : Om ((k : Ordinal.{0}) + 1) < q) (h2 : q ≤ Om ((k : Ordinal.{0}) + 1 + 1)) :
    ∀ x, VbDK S l K x → (UlK S ((k : Ordinal.{0}) + 1) q x ↔ UlK S (k : Ordinal.{0}) (vbTK S l K q) (vbTK S l K x)) := by
  obtain ⟨hZ, hZ1⟩ := vbZ hl hX
  obtain ⟨hTS, hT1, hT2⟩ := fa_q_facts hl hX hKB hk hqD hqS h1 h2
  have hk1 : (1 : Ordinal.{0}) ≤ k := by exact_mod_cast hk
  have h20 : Om (1 + 1 : Ordinal.{0}) < q :=
    (Om_le_Om.2 (add_le_add hk1 le_rfl)).trans_lt h1
  have hqL : q ≤ S.Lam := (hqD.2.2.trans (kzK_lt_Lam hKB)).le
  have hTL : vbTK S l K q ≤ S.Lam := ((vbTK_mem hl hX hKB hqD).2.trans (kzK_lt_Lam hKB)).le
  have hsk : (k : Ordinal.{0}) < ω := natCast_lt_omega0 k
  have hsk1 := fa_nat1_lt k
  refine rxMs_ind (S := S) (T := upsilon l) fun x IH hx => ?_
  have hxE : RxEK S (upsilon l) K x := vbDK_E hl hX hx
  by_cases hxq : x < q
  · exact ⟨fun _ => UlK.small (vbTK_mono hl hX hKB hx hqD hxq), fun _ => UlK.small hxq⟩
  have hqx : q ≤ x := not_lt.1 hxq
  have hTqx : vbTK S l K q ≤ vbTK S l K x := (vbTK_le_iff hl hX hKB hqD hx).1 hqx
  have hx2 : Om (1 + 1) < x := h20.trans_le hqx
  have hx1 : Om 1 < x := (Om_lt_Om.2 (lt_add_one 1)).trans hx2
  have h0 : x ≠ 0 := ((Om_pos one_ne_zero).trans hx1).ne'
  by_cases hΩ : ∃ j : ℕ, x = Om (j : Ordinal.{0})
  · obtain ⟨j, rfl⟩ := hΩ
    have hj : 2 ≤ j := by
      have h := Om_le_Om.1 hx2.le
      rw [one_add_one_eq_two] at h
      have h' : ((2 : ℕ) : Ordinal.{0}) ≤ j := by rw [Nat.cast_ofNat]; exact h
      exact_mod_cast h'
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have e := vbTK_Om (S := S) hl hX hKB (k := i) (by omega)
    rw [Nat.cast_succ, e]
    have hn := fun s q' => (UlK.nat (S := S) (s := s) (q := q') i)
    have hn' := (UlK.nat (S := S) (s := (k : Ordinal.{0}) + 1) (q := q) (i + 1))
    rw [Nat.cast_succ] at hn'
    exact ⟨fun _ => UlK.om (hn _ _), fun _ => UlK.om hn'⟩
  by_cases hxW : x = Om ω
  · subst hxW
    rw [vbTK_OmW hl hX hKB hx.2.2]
    have hω : ∀ s q', UlK S s q' (ω : Ordinal.{0}) := fun s q' => by
      have := UlK.opow (UlK.one (S := S) (s := s) (q := q')); rwa [opow_one] at this
    exact ⟨fun _ => UlK.om (hω _ _), fun _ => UlK.om (hω _ _)⟩
  by_cases hSx : SC x
  · obtain ⟨j, hj, d, hdE, hdn, rfl, hst⟩ := kzE_atom hKB hZ1.le hxE hSx hx1 (kzNe hKB hxE hΩ hxW)
    have hj2 : 2 ≤ j := by
      by_contra hc
      have hj1 : j = 1 := by omega
      subst hj1
      have := (psiS_bounds (S := S) d ((1 : ℕ) : Ordinal.{0})).2
      rw [Nat.cast_one] at this hx2
      exact absurd (hx2.trans this) (lt_irrefl _)
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hj' : 1 ≤ j' := by omega
    have hdD : VbDK S l K d := vbDK_atom hl hX hx hdE hdn hj
    have hms := rxMs_lt_stage (kzE_lt_Lam hKB hdE) hst
    rw [Nat.cast_succ] at hdn hx hqx hxq hTqx hx2 hx1 h0 hxE hms ⊢
    obtain ⟨hTat, hTown⟩ := vbTK_atom hl hX hKB hj' hdD hdn
    rw [hTat] at hTqx ⊢
    have hπ : S.InR (Om ((j' : Ordinal.{0}) + 1 + 1)) := InR_Om_succ _
    have hπ' : S.InR (Om ((j' : Ordinal.{0}) + 1)) := InR_Om_succ _
    rcases lt_trichotomy j' k with hlt | heq | hgt
    · exfalso
      have hle : Om ((j' : Ordinal.{0}) + 1 + 1) ≤ Om ((k : Ordinal.{0}) + 1) := by
        refine Om_le_Om.2 ?_
        have : j' + 1 ≤ k := hlt
        have h' : ((j' + 1 : ℕ) : Ordinal.{0}) ≤ k := by exact_mod_cast this
        rw [Nat.cast_succ] at h'
        exact add_le_add h' le_rfl
      exact hxq (((psiS_bounds (S := S) d ((j' : Ordinal.{0}) + 1)).2.trans_le hle).trans h1)
    · subst heq
      constructor
      · intro hK
        exact absurd (ulK_lt_W hsk1 hqS h1 hK (psiS_bounds (S := S) d ((j' : Ordinal.{0}) + 1)).2) hxq
      · intro hK
        have := ulK_lt_W hsk hTS hT1 hK (psiS_bounds (S := S) (vbTK S l K d) (j' : Ordinal.{0})).2
        exact absurd hTqx (not_le.2 this)
    · have hne1 : Om ((j' : Ordinal.{0}) + 1 + 1) ≠ Om ((k : Ordinal.{0}) + 1 + 1) := by
        intro e
        have e1 : (j' : Ordinal.{0}) + 1 + 1 = (k : Ordinal.{0}) + 1 + 1 :=
          le_antisymm (Om_le_Om.1 e.le) (Om_le_Om.1 e.ge)
        have e3 : ((j' + 1 + 1 : ℕ) : Ordinal.{0}) = ((k + 1 + 1 : ℕ) : Ordinal.{0}) := by push_cast; exact e1
        have e4 := Nat.cast_inj.1 e3
        omega
      have hne2 : Om ((j' : Ordinal.{0}) + 1) ≠ Om ((k : Ordinal.{0}) + 1) := by
        intro e
        have e1 : (j' : Ordinal.{0}) + 1 = (k : Ordinal.{0}) + 1 :=
          le_antisymm (Om_le_Om.1 e.le) (Om_le_Om.1 e.ge)
        have e3 : ((j' + 1 : ℕ) : Ordinal.{0}) = ((k + 1 : ℕ) : Ordinal.{0}) := by push_cast; exact e1
        have e4 := Nat.cast_inj.1 e3
        omega
      have hiff := IH d hms hdD
      have hOm1 : ∀ s q' (i : ℕ), UlK S s q' (Om ((i : Ordinal.{0}) + 1)) := fun s q' i => by
        have := UlK.nat (S := S) (s := s) (q := q') (i + 1)
        rw [Nat.cast_succ] at this
        exact UlK.om this
      have hOm2 : ∀ s q' (i : ℕ), UlK S s q' (Om ((i : Ordinal.{0}) + 1 + 1)) := fun s q' i => by
        have := hOm1 s q' (i + 1)
        rwa [Nat.cast_succ] at this
      constructor
      · intro hK
        have hdK := Uo.uoArg hqL hπ hdn hK hqx
        exact UlK.coll hπ' hne2 (hOm1 _ _ _) (hiff.1 hdK)
      · intro hK
        have hdK := Uo.uoArg hTL hπ' hTown hK hTqx
        exact UlK.coll hπ hne1 (hOm2 _ _ _) (hiff.2 hdK)
  by_cases hε : ω ^ x = x
  · obtain ⟨hv, ha0, ha, hb⟩ := rxVeb hx1 hε hSx
    obtain ⟨haD, hbD, -, -, hha, hhb⟩ := vbDK_veb hx hxE hv hb
    have hIa := IH _ (rxMs_lt_val hha ha) haD
    have hIb := IH _ (rxMs_lt_val hhb hb) hbD
    have hT := vbTK_veb hl hX hKB hx hv ha0.ne' hb hx2.le
    have hTa : vbTK S l K (invVeblen₁ x) < vbTK S l K x := vbTK_mono hl hX hKB haD hx ha
    have hTb : vbTK S l K (invVeblen₂ x) < vbTK S l K x := vbTK_mono hl hX hKB hbD hx hb
    constructor
    · intro hK
      have hK' : UlK S ((k : Ordinal.{0}) + 1) q (veblen (invVeblen₁ x) (invVeblen₂ x)) := by rw [hv]; exact hK
      obtain ⟨h3, h4⟩ := Qt.ulK_veb_parts hK' (by rw [hv]; exact ha) (by rw [hv]; exact hb)
      rw [hT]
      exact UlK.phi (hIa.1 h3) (hIb.1 h4)
    · intro hK
      rw [hT] at hK hTa hTb
      obtain ⟨h3, h4⟩ := Qt.ulK_veb_parts hK hTa hTb
      rw [← hv]
      exact UlK.phi (hIa.2 h3) (hIb.2 h4)
  -- the Cantor normal form
  have hlx : log ω x < x := ruLog_lt hx1 hε
  obtain ⟨hlD, -, hlh⟩ := vbDK_log hx hxE
  obtain ⟨hrD, -, hrh⟩ := vbDK_rem hx hxE
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
  have hpos : (0 : Ordinal.{0}) < ω ^ log ω x := opow_pos _ omega0_pos
  have hdm : x = ω ^ log ω x * n + x % ω ^ log ω x := by
    rw [← hn]; exact (Ordinal.div_add_mod x _).symm
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      have hlt : x < ω ^ log ω x * 1 :=
        (Ordinal.lt_mul_iff_div_lt hpos.ne').2 (by rw [hn, h]; exact zero_lt_one)
      rw [mul_one] at hlt
      exact absurd (opow_log_le_self ω h0) (not_le.2 hlt)
    · exact h
  have hn0 : (n : Ordinal.{0}) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hIl := IH _ (rxMs_lt_val hlh hlx) hlD
  have hIr := IH _ (rxMs_lt_val hrh (mod_opow_log_lt_self ω h0)) hrD
  have hrlt : x % ω ^ log ω x < ω ^ log ω x := Ordinal.mod_lt x hpos.ne'
  have hT := kzT_cnf hl hX hKB n hn1 hlD hrD hrlt
  rw [← hdm] at hT
  -- `T r < ω^{T ℓ}`
  have hoD : VbDK S l K (ω ^ log ω x) := by
    have hoC : ∀ a b, log ω x ∈ S.CSet a b → ω ^ log ω x ∈ S.CSet a b := fun a b h => by
      have := CSet.phi_mem (S := S) (CSet.zero_mem _ _) h; rwa [veblen_zero_apply] at this
    exact ⟨hoC _ _ hlD.1, hoC _ _ hlD.2.1, (opow_log_le_self ω h0).trans_lt hx.2.2⟩
  have hTo : vbTK S l K (ω ^ log ω x) = ω ^ vbTK S l K (log ω x) := by
    have h := kzT_cnf hl hX hKB 1 le_rfl hlD (⟨CSet.zero_mem _ _, CSet.zero_mem _ _, hKB.sc.1⟩ : VbDK S l K 0) hpos
    rwa [Nat.cast_one, mul_one, add_zero, vbTK_zero hl hX hKB, mul_one, add_zero] at h
  have hTr : vbTK S l K (x % ω ^ log ω x) < ω ^ vbTK S l K (log ω x) := by
    rw [← hTo]; exact vbTK_mono hl hX hKB hrD hoD hrlt
  have hlogT : log ω (vbTK S l K x) = vbTK S l K (log ω x) := by
    rw [hT, log_opow_mul_add one_lt_omega0 hn0 hTr, log_eq_zero (natCast_lt_omega0 n), add_zero]
  have hmodT : vbTK S l K x % ω ^ vbTK S l K (log ω x) = vbTK S l K (x % ω ^ log ω x) := by
    rw [hT, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hTr]
  constructor
  · intro hK
    obtain ⟨-, -, h3, h4, -⟩ := ulK_split hqS hK h0
    rw [hT]
    exact UlK.add ((UlK.opow (hIl.1 h3)).mul_nat n) (hIr.1 h4)
  · intro hK
    have hT0 : vbTK S l K x ≠ 0 := by
      rw [hT]
      refine (lt_of_lt_of_le (mul_pos (opow_pos _ omega0_pos) (pos_iff_ne_zero.2 hn0)) le_self_add).ne'
    obtain ⟨-, -, h3, h4, -⟩ := ulK_split hTS hK hT0
    rw [hlogT] at h3 h4
    rw [hmodT] at h4
    rw [hdm]
    exact UlK.add ((UlK.opow (hIl.2 h3)).mul_nat n) (hIr.2 h4)

end Rst

end Googology.Trans.PoR.InaccPsi.R2.Fa

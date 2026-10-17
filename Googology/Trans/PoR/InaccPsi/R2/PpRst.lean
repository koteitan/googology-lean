import Googology.Trans.PoR.InaccPsi.R2.PpIdx

/-!
# Every `L(n+1)` is a restart

`P' = ψ_{Ω₂}(Ω_ω·2)`, `c_k = ψ_{Ω₂}(Ω_ω + Ω_{k+1})`, `L(ξ) = P(Ω_ω + P'·ξ) = υ_{ι(Ω_ω + P'·ξ)}`.

* `ppPsi2_limit` (**Lemma CONT for `ψ_{Ω₂}`**): `ψ_{Ω₂}(a) = sup_{e<a} ψ_{Ω₂}(e)` for a limit `a` (the proof of the
  repo's `psi_limit`, with `Ω₂` in place of `Ω₁`);
* `ppLt_Om_omega`: every `x < Ω_ω` is below some `Ω_{k+1}`;
* `ppC_lt`, `ppPp_cof`: `c_k < P'`, and the `c_k` are cofinal in `P'`;
* `ppGood_ck`: `Ω_ω + P'·n + c_k + y` is good for every `y < ω²`;
* `ppIota_succ_restart`, `ppL_succ_restart` (**`L(n+1)` is a restart**): `ι(Ω_ω + P'·(n+1))` is a restart index,
  so `L(n+1) = υ_l` with `l` a restart index; `ppL_succ_not_tau`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Pp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Nc

variable {S : InaccSeq.{0}}

/-- **Lemma CONT for `ψ_{Ω₂}`**: `ψ_{Ω₂}(a) = sup_{e<a} ψ_{Ω₂}(e)` for a limit `a`. -/
theorem ppPsi2_limit (S : InaccSeq.{0}) {a : Ordinal.{0}} (ha : IsSuccLimit a) :
    S.psi a (Om (1 + 1)) = ⨆ e : Iio a, S.psi e.1 (Om (1 + 1)) := by
  have hInR : S.InR (Om ((1 : Ordinal.{0}) + 1)) := InR_Om_succ 1
  have hbdd : BddAbove (range fun e : Iio a => S.psi e.1 (Om (1 + 1))) :=
    ⟨Om (1 + 1), by rintro _ ⟨e, rfl⟩; exact (psi_lt hInR _).le⟩
  have ha0 : (0 : Ordinal.{0}) < a := ha.bot_lt
  haveI : Nonempty (Iio a) := ⟨⟨0, ha0⟩⟩
  set σ := ⨆ e : Iio a, S.psi e.1 (Om (1 + 1)) with hσ
  have up : ∀ {y e e' : Ordinal.{0}}, e ≤ e' →
      y ∈ S.CSet e (S.psi e (Om (1 + 1))) → y ∈ S.CSet e' (S.psi e' (Om (1 + 1))) :=
    fun h hy => (psi_mono hInR h).2 hy
  have key : ∀ x ∈ S.CSet a σ, ∃ e < a, x ∈ S.CSet e (S.psi e (Om (1 + 1))) := by
    intro x hx
    induction hx with
    | small h =>
      obtain ⟨e, he⟩ := (lt_ciSup_iff hbdd).1 h
      exact ⟨e.1, e.2, CSet.of_lt he⟩
    | zero => exact ⟨0, ha0, CSet.zero_mem _ _⟩
    | inacc n => exact ⟨0, ha0, CSet.I_mem _ _ n⟩
    | inaccW => exact ⟨0, ha0, CSet.Iw_mem _ _⟩
    | add _ _ ihx ihy =>
      obtain ⟨e1, h1, k1⟩ := ihx
      obtain ⟨e2, h2, k2⟩ := ihy
      exact ⟨max e1 e2, max_lt h1 h2,
        CSet.add_mem (up (le_max_left _ _) k1) (up (le_max_right _ _) k2)⟩
    | phi _ _ ihx ihy =>
      obtain ⟨e1, h1, k1⟩ := ihx
      obtain ⟨e2, h2, k2⟩ := ihy
      exact ⟨max e1 e2, max_lt h1 h2,
        CSet.phi_mem (up (le_max_left _ _) k1) (up (le_max_right _ _) k2)⟩
    | om _ ih =>
      obtain ⟨e1, h1, k1⟩ := ih
      exact ⟨e1, h1, CSet.Om_mem k1⟩
    | @coll π e hπ _ _ ihπ ihe =>
      obtain ⟨e1, h1, k1⟩ := ihπ
      obtain ⟨e2, h2, k2⟩ := ihe
      have hs : e.1 + 1 < a := ha.add_one_lt e.2
      refine ⟨max (e.1 + 1) (max e1 e2), max_lt hs (max_lt h1 h2), ?_⟩
      have he : e.1 < max (e.1 + 1) (max e1 e2) := lt_of_lt_of_le (lt_add_one _) (le_max_left _ _)
      exact CSet.psi_mem he hπ
        (up (le_trans (le_max_left _ _) (le_max_right _ _)) k1)
        (up (le_trans (le_max_right _ _) (le_max_right _ _)) k2)
  apply le_antisymm
  · refine psi_le_of_good (CSet.Om_mem (CSet.add_mem (CSet.one_mem _ _) (CSet.one_mem _ _))) ?_
    intro x hx hxΩ
    obtain ⟨e, he, hN⟩ := key x hx
    exact lt_of_lt_of_le (lt_psi_of_mem hInR hN hxΩ) (le_ciSup hbdd ⟨e, he⟩)
  · exact ciSup_le fun e => (psi_mono hInR e.2.le).1

/-- Every `x < Ω_ω` is below some `Ω_{k+1}`. -/
theorem ppLt_Om_omega {x : Ordinal.{0}} (hx : x < Om ω) :
    ∃ k : ℕ, x < Om ((k + 1 : ℕ) : Ordinal.{0}) := by
  rw [Om_of_ne_zero omega0_ne_zero] at hx
  obtain ⟨_, ⟨c, hc, rfl⟩, hxc⟩ :=
    (lt_isLUB_iff (isNormal_omega.isLUB_image_Iio_of_isSuccLimit isSuccLimit_omega0)).1 hx
  obtain ⟨k, rfl⟩ := Ordinal.lt_omega0.1 hc
  refine ⟨k, lt_of_lt_of_le hxc ?_⟩
  rw [Om_of_ne_zero (by exact_mod_cast Nat.succ_ne_zero k)]
  exact isNormal_omega.monotone (by exact_mod_cast Nat.le_succ k)

/-- A natural number lies in every hull. -/
theorem ppNat_mem (a b : Ordinal.{0}) : ∀ k : ℕ, (k : Ordinal.{0}) ∈ S.CSet a b := by
  intro k
  induction k with
  | zero => simpa using CSet.zero_mem (S := S) a b
  | succ k ih => rw [Nat.cast_succ]; exact CSet.succ_mem ih

/-- `Ω_ω + Ω_{k+1}` lies in every hull with `ω` in it. -/
theorem ppOmk_mem {a b : Ordinal.{0}} (hw : (ω : Ordinal.{0}) < b) (k : ℕ) :
    Om ω + Om ((k + 1 : ℕ) : Ordinal.{0}) ∈ S.CSet a b :=
  CSet.add_mem (CSet.Om_mem (CSet.of_lt hw)) (CSet.Om_mem (ppNat_mem a b (k + 1)))

theorem ppOmega_lt_SC {γ : Ordinal.{0}} (h : SC γ) : (ω : Ordinal.{0}) < γ :=
  lt_of_le_of_lt (le_mul_left _ omega0_pos) (ppSC_ww h)

/-- `c_k = ψ_{Ω₂}(Ω_ω + Ω_{k+1}) < P'`. -/
theorem ppC_lt (k : ℕ) :
    S.psi (Om ω + Om ((k + 1 : ℕ) : Ordinal.{0})) (Om (1 + 1)) < ncPp S := by
  unfold ncPp
  refine psi_lt_psi (InR_Om_succ 1) ?_ (ppOmk_mem (ppOmega_lt_SC (SC_psi (InR_Om_succ 1) _)) k)
  gcongr
  exact Om_lt_Om.2 (Ordinal.natCast_lt_omega0 _)

/-- **The `c_k` are cofinal in `P'`.** -/
theorem ppPp_cof : ∀ c < ncPp S, ∃ k : ℕ, c < S.psi (Om ω + Om ((k + 1 : ℕ) : Ordinal.{0})) (Om (1 + 1)) := by
  intro c hc
  have hlim : IsSuccLimit (Om ω + Om (ω : Ordinal.{0})) :=
    isSuccLimit_add _ (SC_Om omega0_ne_zero).isSuccLimit
  have hc' := hc
  unfold ncPp at hc'
  rw [ppPsi2_limit S hlim] at hc'
  haveI : Nonempty (Iio (Om ω + Om (ω : Ordinal.{0}))) := ⟨⟨0, hlim.bot_lt⟩⟩
  have hbdd : BddAbove (range fun e : Iio (Om ω + Om (ω : Ordinal.{0})) => S.psi e.1 (Om (1 + 1))) :=
    ⟨Om (1 + 1), by rintro _ ⟨e, rfl⟩; exact (psi_lt (InR_Om_succ 1) _).le⟩
  obtain ⟨e, he⟩ := (lt_ciSup_iff hbdd).1 hc'
  have hk : ∃ k : ℕ, e.1 ≤ Om ω + Om ((k + 1 : ℕ) : Ordinal.{0}) := by
    rcases lt_or_ge e.1 (Om ω) with h | h
    · exact ⟨0, h.le.trans le_self_add⟩
    · obtain ⟨d, hd⟩ := exists_add_of_le h
      have hdw : d < Om ω := by
        have := e.2; rw [hd] at this; exact (add_lt_add_iff_left _).1 this
      obtain ⟨k, hk⟩ := ppLt_Om_omega hdw
      exact ⟨k, by rw [hd]; gcongr⟩
  obtain ⟨k, hk⟩ := hk
  exact ⟨k, lt_of_lt_of_le he (psi_mono (InR_Om_succ 1) hk).1⟩

/-- **`Ω_ω + P'·n + c_k + y` is good** for every `y < ω²`. -/
theorem ppGood_ck (n k : ℕ) {y : Ordinal.{0}} (hy : y < (ω : Ordinal.{0}) * ω) :
    Bt.Good S (Om ω + ncPp S * (n : Ordinal.{0}) +
      S.psi (Om ω + Om ((k + 1 : ℕ) : Ordinal.{0})) (Om (1 + 1)) + y) := by
  set ck := S.psi (Om ω + Om ((k + 1 : ℕ) : Ordinal.{0})) (Om (1 + 1)) with hck
  set η := Om ω + ncPp S * (n : Ordinal.{0}) + ck + y with hη
  set a := ConjT.Aη S η + 1
  set b := S.psi (ConjT.Aη S η) (Om 1)
  have hSC : SC b := SC_psi Low.InR_Om_one _
  have hw2 : (ω : Ordinal.{0}) * ω < b := ppSC_ww hSC
  have hw : (ω : Ordinal.{0}) < b := ppOmega_lt_SC hSC
  have hΩ : Om ω ∈ S.CSet a b := CSet.Om_mem (CSet.of_lt hw)
  have hA2 : Om ω + Om ω ≤ ConjT.Aη S η := by
    unfold ConjT.Aη
    gcongr
    calc Om (ω : Ordinal.{0}) = ConjT.th S * Om ω := (Bt.th_mul_Om_omega S).symm
      _ ≤ ConjT.th S * η := by gcongr; rw [hη, add_assoc, add_assoc]; exact le_self_add
  have hO2 : Om (1 + 1) ∈ S.CSet a b := CSet.Om_mem (CSet.add_mem (CSet.one_mem a b) (CSet.one_mem a b))
  have hck_mem : ck ∈ S.CSet a b := by
    refine CSet.psi_mem ?_ (InR_Om_succ 1) hO2 (ppOmk_mem hw k)
    refine lt_of_lt_of_le ?_ (hA2.trans le_self_add)
    gcongr
    exact Om_lt_Om.2 (Ordinal.natCast_lt_omega0 _)
  have hPn : ncPp S * (n : Ordinal.{0}) ∈ S.CSet a b := by
    rcases n with _ | m
    · simpa using CSet.zero_mem (S := S) a b
    · have hge : Om ω + Om ω + ncPp S ≤ ConjT.Aη S η := by
        have := ppA_ge (S := S) m (ck + y)
        rwa [← add_assoc] at this
      have hlt : Om ω + Om ω < a :=
        lt_of_lt_of_le (lt_add_of_pos_right _ (SC_psi (InR_Om_succ 1) _).1) (hge.trans le_self_add)
      have hP : ncPp S ∈ S.CSet a b := CSet.psi_mem hlt (InR_Om_succ 1) hO2 (CSet.add_mem hΩ hΩ)
      exact ppPp_mul_mem hP (m + 1)
  exact CSet.add_mem (CSet.add_mem (CSet.add_mem hΩ hPn) hck_mem) (CSet.of_lt (hy.trans hw2))

/-- **`ι(Ω_ω + P'·(n+1))` is a restart index.** -/
theorem ppIota_succ_restart (n : ℕ) :
    IsRestartIdx (iota S (Om ω + ncPp S * ((n + 1 : ℕ) : Ordinal.{0}))) := by
  set base := Om ω + ncPp S * (n : Ordinal.{0}) with hbase
  have e : Om ω + ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) = base + ncPp S := by
    rw [hbase, Nat.cast_succ, mul_add_one, add_assoc]
  rw [e]
  have hlim : IsSuccLimit (base + ncPp S) := isSuccLimit_add _ (ncPp_SC S).isSuccLimit
  refine ri_iff.2 ⟨(lt_of_lt_of_le zero_lt_one (one_le_iota _)).ne', ppDvd_of_add fun z hz => ?_⟩
  have hz' := hz
  rw [iota_limit hlim] at hz'
  haveI : Nonempty (Iio (base + ncPp S)) := ⟨⟨0, hlim.bot_lt⟩⟩
  obtain ⟨e', he'⟩ := (lt_ciSup_iff (iota_bdd _)).1 hz'
  -- `e' < base + c_k` for some `k`
  have hk : ∃ k : ℕ, e'.1 ≤ base + S.psi (Om ω + Om ((k + 1 : ℕ) : Ordinal.{0})) (Om (1 + 1)) := by
    rcases lt_or_ge e'.1 base with h | h
    · exact ⟨0, h.le.trans le_self_add⟩
    · obtain ⟨d, hd⟩ := exists_add_of_le h
      have hdP : d < ncPp S := by
        have := e'.2; rw [hd] at this; exact (add_lt_add_iff_left _).1 this
      obtain ⟨k, hk⟩ := ppPp_cof d hdP
      exact ⟨k, by rw [hd]; gcongr⟩
  obtain ⟨k, hk⟩ := hk
  set ck := S.psi (Om ω + Om ((k + 1 : ℕ) : Ordinal.{0})) (Om (1 + 1)) with hck
  have hstep : iota S (base + ck + (ω : Ordinal.{0}) * ω) = iota S (base + ck) + (ω : Ordinal.{0}) * ω :=
    ppIota_add _ _ (fun y hy => ppGood_ck n k hy)
  have hle : base + ck + (ω : Ordinal.{0}) * ω ≤ base + ncPp S := by
    rw [add_assoc]
    gcongr
    exact ((ncPp_SC S).isPrincipal (ppC_lt k) (ppSC_ww (ncPp_SC S))).le
  calc z + (ω : Ordinal.{0}) * ω ≤ iota S e'.1 + (ω : Ordinal.{0}) * ω := by gcongr
    _ ≤ iota S (base + ck) + (ω : Ordinal.{0}) * ω := by gcongr; exact iota_mono _ _ hk
    _ = iota S (base + ck + (ω : Ordinal.{0}) * ω) := hstep.symm
    _ ≤ iota S (base + ncPp S) := iota_mono _ _ hle

/-- **`L(n+1)` is a restart.** -/
theorem ppL_succ_restart (n : ℕ) :
    ∃ l, IsRestartIdx l ∧ ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l :=
  ⟨_, ppIota_succ_restart n, ppL_eq_ups _⟩

/-- `L(n+1)` is not a `τ`-point. -/
theorem ppL_succ_not_tau (n : ℕ) : ¬ NcTauPt (ncL S ((n + 1 : ℕ) : Ordinal.{0})) := by
  obtain ⟨l, hl, e⟩ := ppL_succ_restart (S := S) n
  rw [e]; exact ncRestart_not_tau hl

end Googology.Trans.PoR.InaccPsi.R2.Pp

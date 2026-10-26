import Googology.Trans.PoR.InaccPsi.R2.UuAtS

/-!
# The member systems at a limit `ψ₃`-atom `ψ₃(d)`, from those of `d`

`T = Ug.ugTh`, `Θ = gxTh ρ_λ (ldAtR λ)`, `H_λ = cdHull S λ`, `C_k(Q) = Ug.UgC S k Q`, `ψ_k = ψ_{Ω_k}`,
`Y₃ = ψ₃(Ω₃)`, `Y₂ = ψ₂(Ω₂)`.

* `uuHull_dec` (**THE HULL LEMMA**: for a limit `d < Y₃`, every `y ∈ H_λ` with `y < ψ₃(d)` is below `ψ₃(u)` for some
  `u ∈ H_λ`, `u < d`; the atoms of the hull by `Ug.ugAtomH` and the normal-argument comparison `Uu.uuNormLt`);
* `uuTh_lt_Y2` (**`T d < Y₂`** for `d ∈ H_λ ∩ Y₃`, so `Uu.uuCl_dec` applies at level 1 below `ψ₂(T d)`);
* `uuMA_lim` (**`UqMA d` GIVES `UqMA ψ₃(d)`** at a limit `d`: members `ψ₃(e + 1)`, `e` a member of `d`),
  `uuMB_lim` (**`UqMB d` GIVES `UqMB ψ₃(d)`**: `M' c = ψ₃(M c + 1)`, `M̂' v = ψ₂(M̂ v + 1)`; the cofinality among
  `C_2(Q)` codes at every strongly critical `Q > Ω₁` from `Uu.uuCl_dec` at level 2, among `C_1(Q)` codes from
  `Uu.uuCl_dec` at level 1; the own transfer from `Uu.uuC_atom`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Uu

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Ua Googology.Trans.PoR.InaccPsi.R2.Ud
  Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uq

variable {S : InaccSeq.{0}}

/-- The own transfer between two normal atoms: a `C_2(Q)` code `h` with `ψ₃(a) ≤ h ≤ ψ₃(d)` and `Q ≤ ψ₃(a)`
(`d` normal) contains an atom `ψ₃(e)`, `e` a code with `a ≤ e ≤ d`. -/
theorem uuAtom_between {a d Q h : Ordinal.{0}}
    (hd : d < S.psi d (Om (1 + 1 + 1))) (hQa : Q ≤ S.psi a (Om (1 + 1 + 1)))
    (h1 : S.psi a (Om (1 + 1 + 1)) ≤ h) (h2 : h ≤ S.psi d (Om (1 + 1 + 1))) (hh : UgC S (1 + 1) Q h) :
    ∃ e, UgC S (1 + 1) Q e ∧ a ≤ e ∧ e ≤ d := by
  obtain ⟨e, hec, hel, hae, heh⟩ := uuC_atom h hh _ (SC_psi ugInR3 a) hQa (ugOm2_lt_psi3 a) h1
  refine ⟨e, hec, ?_, ?_⟩
  · by_contra hc
    push Not at hc
    exact absurd hae (not_le.2 ((uuNormLt (1 + 1) hel).1 hc))
  · by_contra hc
    push Not at hc
    exact absurd (heh.trans h2) (not_le.2 ((uuNormLt (1 + 1) hd).1 hc))

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **THE HULL LEMMA**: for a limit `d < Y₃`, every `y ∈ H_λ`, `y < ψ₃(d)`, is below `ψ₃(u)` for some `u ∈ H_λ`,
`u < d`. -/
theorem uuHull_dec {d : Ordinal.{0}} (hdl : IsSuccLimit d) (hdY : S.psi d (Om (1 + 1 + 1)) < ugY S) :
    ∀ y, y ∈ cdHull S l → y < S.psi d (Om (1 + 1 + 1)) →
      ∃ u, u ∈ cdHull S l ∧ u < d ∧ y < S.psi u (Om (1 + 1 + 1)) := by
  have hκ := ugInR3 (S := S)
  have h0H : (0 : Ordinal.{0}) ∈ cdHull S l := CSet.zero_mem _ _
  have hd0 : (0 : Ordinal.{0}) < d := hdl.bot_lt
  have hW0 : Om (1 + 1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1 + 1)) := ugOm2_lt_psi3 0
  have hlow : ∀ y, y < Om (1 + 1) → ∃ u, u ∈ cdHull S l ∧ u < d ∧ y < S.psi u (Om (1 + 1 + 1)) :=
    fun y hy => ⟨0, h0H, hd0, hy.trans hW0⟩
  have hdO : S.psi d (Om (1 + 1 + 1)) < Om (1 + 1 + 1) := psi_lt hκ d
  have hmaxH : ∀ u1 u2, u1 ∈ cdHull S l → u2 ∈ cdHull S l → max u1 u2 ∈ cdHull S l := fun u1 u2 h1 h2 => by
    rcases le_total u1 u2 with h | h
    · rw [max_eq_right h]; exact h2
    · rw [max_eq_left h]; exact h1
  intro y hy
  have hy' : y ∈ S.CSet (ConjT.Aη S (cdEta S l)) (upsilon l) := hy
  induction hy' with
  | small h =>
    exact fun _ => hlow _ (h.trans ((leRho hl hX).2.trans (Om_lt_Om.2 (lt_add_one 1))))
  | zero => exact fun _ => hlow _ (Om_pos ugTwo_ne)
  | inacc n => exact fun h => absurd ((h.trans hdO).trans_le (uuOm_le_I uuThree_lt n)) (lt_irrefl _)
  | inaccW =>
    exact fun h => absurd ((h.trans hdO).trans_le ((uuOm_le_I uuThree_lt 0).trans (S.I_le_Iw 0)))
      (lt_irrefl _)
  | @add a b ha hb iha ihb =>
    intro h
    obtain ⟨u1, h1H, hu1, ha1⟩ := iha ha (le_self_add.trans_lt h)
    obtain ⟨u2, h2H, hu2, hb2⟩ := ihb hb (le_add_self.trans_lt h)
    refine ⟨max u1 u2, hmaxH _ _ h1H h2H, max_lt hu1 hu2, (SC_psi hκ _).isPrincipal ?_ ?_⟩
    · exact ha1.trans_le (psi_mono hκ (le_max_left _ _)).1
    · exact hb2.trans_le (psi_mono hκ (le_max_right _ _)).1
  | @phi a b ha hb iha ihb =>
    intro h
    obtain ⟨u1, h1H, hu1, ha1⟩ := iha ha ((left_le_veblen a b).trans_lt h)
    obtain ⟨u2, h2H, hu2, hb2⟩ := ihb hb ((right_le_veblen a b).trans_lt h)
    refine ⟨max u1 u2, hmaxH _ _ h1H h2H, max_lt hu1 hu2, (SC_psi hκ _).2 _ ?_ _ ?_⟩
    · exact ha1.trans_le (psi_mono hκ (le_max_left _ _)).1
    · exact hb2.trans_le (psi_mono hκ (le_max_right _ _)).1
  | @om a _ _ =>
    intro h
    have ha : a ≤ 1 + 1 := Order.lt_add_one_iff.1 (Om_lt_Om.1 (h.trans hdO))
    exact ⟨0, h0H, hd0, (Om_le_Om.2 ha).trans_lt hW0⟩
  | @coll π e hπ hπC heC _ _ =>
    intro h
    rcases lt_trichotomy π (Om (1 + 1 + 1)) with hlt | heq | hgt
    · exact hlow _ ((psi_lt hπ _).trans_le (uuInR_lt uuThree_lt hπ hlt))
    · subst heq
      have hzH : S.psi e.1 (Om (1 + 1 + 1)) ∈ cdHull S l := CSet.psi_mem e.2 hπ hπC heC
      obtain ⟨D, hDH, hD, -, hDe⟩ := ugAtomH hl hX hzH (SC_psi hκ _) (ugOm2_lt_psi3 _) (h.trans hdY)
      have hDd : D < d := (uuNormLt (1 + 1) hD).2 (by rw [hDe]; exact h)
      refine ⟨D + 1, CSet.succ_mem hDH, hdl.add_one_lt hDd, ?_⟩
      rw [← hDe]; exact uuPsi_lt_succ (1 + 1) hD
    · exact absurd ((h.trans hdO).trans_le (uuInR_gt uuThree_lt hπ hgt _)) (lt_irrefl _)

/-- **`T d < Y₂ = ψ₂(Ω₂)`** for `d ∈ H_λ ∩ Y₃`. -/
theorem uuTh_lt_Y2 {d : Ordinal.{0}} (hdH : d ∈ cdHull S l) (hdY : d < ugY S) :
    ugTh S l d < S.psi (Om (1 + 1)) (Om (1 + 1)) :=
  (ugNormAll hl hX hdH hdY).2.trans_le (psi_mono (InR_Om_succ 1) (ugLtOm2 hl hX d hdH hdY).le).1

/-- **`UqMA d` GIVES `UqMA ψ₃(d)`** at a limit `d ∈ H_λ` with `ψ₃(d) < Y₃`: the members `ψ₃(e + 1)`. -/
theorem uuMA_lim {d : Ordinal.{0}} (hdH : d ∈ cdHull S l) (hdl : IsSuccLimit d)
    (hd : d < S.psi d (Om (1 + 1 + 1))) (hY : S.psi d (Om (1 + 1 + 1)) < ugY S) (hA : UqMA S l d) :
    UqMA S l (S.psi d (Om (1 + 1 + 1))) := by
  obtain ⟨Mem, hdat, ⟨m0, hm0⟩, hA1, hA2, hA3⟩ := hA
  have hκ := ugInR3 (S := S)
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hdY : d < ugY S := hd.trans hY
  have he1 : ∀ e, Mem e → e + 1 < d := fun e he => hdl.add_one_lt (hdat e he).2.2
  have he1Y : ∀ e, Mem e → e + 1 < ugY S := fun e he => (he1 e he).trans hdY
  have he1n : ∀ e, Mem e → e + 1 < S.psi (e + 1) (Om (1 + 1 + 1)) := fun e he => uuLt3 (he1Y e he)
  have hlt : ∀ e, Mem e → S.psi (e + 1) (Om (1 + 1 + 1)) < S.psi d (Om (1 + 1 + 1)) := fun e he =>
    (uuNormLt (1 + 1) (he1n e he)).1 (he1 e he)
  have hTd : ugTh S l (S.psi d (Om (1 + 1 + 1))) = S.psi (ugTh S l d) (Om (1 + 1)) := ugTh_atom hd
  have hTe : ∀ e, Mem e → ugTh S l (S.psi (e + 1) (Om (1 + 1 + 1))) =
      S.psi (ugTh S l e + 1) (Om (1 + 1)) := fun e he => by
    rw [ugTh_atom (he1n e he), ugSucc hl hX (hdat e he).1 (he1Y e he)]
  refine ⟨fun m => ∃ e, Mem e ∧ m = S.psi (e + 1) (Om (1 + 1 + 1)), ?_, ⟨_, m0, hm0, rfl⟩, ?_, ?_, ?_⟩
  · rintro m ⟨e, he, rfl⟩
    exact ⟨uuPsi3_mem (CSet.succ_mem (hdat e he).1) (he1Y e he),
      Order.one_le_iff_pos.2 (SC_psi hκ _).1, hlt e he⟩
  · intro y hyH hy
    obtain ⟨u, huH, hud, hyu⟩ := uuHull_dec hl hX hdl hY y hyH hy
    obtain ⟨e, he, hue⟩ := hA1 u huH hud
    exact ⟨_, ⟨e, he, rfl⟩, hyu.trans_le (psi_mono hκ (hue.le.trans le_self_add)).1⟩
  · intro z hz
    rw [hTd] at hz
    have hTlim : IsSuccLimit (ugTh S l d) := uqLimT hl hX d hdH hdl hdY
    rw [Lw.lw_psi_limit S hκ2 hTlim] at hz
    have hbdd : BddAbove (range fun e : Iio (ugTh S l d) => S.psi e.1 (Om (1 + 1))) :=
      ⟨Om (1 + 1), by rintro _ ⟨e, rfl⟩; exact (psi_lt hκ2 _).le⟩
    haveI : Nonempty (Iio (ugTh S l d)) := ⟨⟨0, hTlim.bot_lt⟩⟩
    obtain ⟨⟨u, hu⟩, hzu⟩ := (lt_ciSup_iff hbdd).1 hz
    obtain ⟨e, he, hue⟩ := hA2 u hu
    refine ⟨_, ⟨e, he, rfl⟩, ?_⟩
    rw [hTe e he]
    exact hzu.trans_le (psi_mono hκ2 (hue.le.trans le_self_add)).1
  · rintro Q hQ m h ⟨e, he, rfl⟩ h1 h2 hh
    by_cases hmQ : S.psi (e + 1) (Om (1 + 1 + 1)) < Q
    · exact UgC.small hmQ
    push Not at hmQ
    obtain ⟨e', he'c, hee', he'd⟩ := uuAtom_between hd hmQ h1 h2 hh
    have hec : UgC S (1 + 1) Q e := hA3 Q hQ e e' he (le_self_add.trans hee') he'd he'c
    exact UgC.psi (UgC.add hec (UgC.small (gg_one_lt_of_SC hQ))) (he1n e he)

/-- **`UqMB d` GIVES `UqMB ψ₃(d)`** at a limit `d ∈ H_λ` with `ψ₃(d) < Y₃`: `M' c = ψ₃(M c + 1)`,
`M̂' v = ψ₂(M̂ v + 1)`. -/
theorem uuMB_lim {d : Ordinal.{0}} (hdH : d ∈ cdHull S l) (hdl : IsSuccLimit d)
    (hd : d < S.psi d (Om (1 + 1 + 1))) (hY : S.psi d (Om (1 + 1 + 1)) < ugY S) (hB : UqMB S l d) :
    UqMB S l (S.psi d (Om (1 + 1 + 1))) := by
  obtain ⟨M, Mh, hM, hMh, hB0, hB1, hB2, hB3⟩ := hB
  have hκ := ugInR3 (S := S)
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hdY : d < ugY S := hd.trans hY
  have hTd : ugTh S l (S.psi d (Om (1 + 1 + 1))) = S.psi (ugTh S l d) (Om (1 + 1)) := ugTh_atom hd
  have hTlim : IsSuccLimit (ugTh S l d) := uqLimT hl hX d hdH hdl hdY
  have hTdn : ugTh S l d < S.psi (ugTh S l d) (Om (1 + 1)) := (ugNormAll hl hX hdH hdY).2
  refine ⟨fun c => S.psi (M c + 1) (Om (1 + 1 + 1)), fun v => S.psi (Mh v + 1) (Om (1 + 1)),
    fun x z h => (psi_mono hκ (add_le_add (hM h) le_rfl)).1,
    fun x z h => (psi_mono hκ2 (add_le_add (hMh h) le_rfl)).1, ?_, ?_, ?_, ?_⟩
  · intro c hc hc1 hcW
    obtain ⟨hMH, -, hMd, hTM, hMhT⟩ := hB0 c hc hc1 hcW
    have hM1d : M c + 1 < d := hdl.add_one_lt hMd
    have hM1n : M c + 1 < S.psi (M c + 1) (Om (1 + 1 + 1)) := uuLt3 (hM1d.trans hdY)
    refine ⟨uuPsi3_mem (CSet.succ_mem hMH) (hM1d.trans hdY), Order.one_le_iff_pos.2 (SC_psi hκ _).1,
      (uuNormLt (1 + 1) hM1n).1 hM1d, ?_, ?_⟩
    · rw [ugTh_atom hM1n, ugSucc hl hX hMH (hM1d.trans hdY), hTM]
    · rw [hTd]
      have h1 : Mh (gxTh (upsilon l) (ldAtR S l) c) + 1 < ugTh S l d := hTlim.add_one_lt hMhT
      exact psi_lt_psi_of_mem hκ2 h1 (CSet.of_lt (h1.trans hTdn))
  · intro Q hQ _ w hw hwE
    obtain ⟨u, hu, hud, hwu⟩ := uuCl_dec hQ uuThree_lt hdl hdY w hw hwE
    obtain ⟨c', hc'Q, huc'⟩ := hB1 Q hQ ‹_› u hu hud
    exact ⟨c', hc'Q, hwu.trans_le (psi_mono hκ (huc'.le.trans le_self_add)).1⟩
  · intro Q hQ w hw hwE
    rw [hTd] at hwE
    obtain ⟨u, hu, hud, hwu⟩ := uuCl_dec hQ uuTwo_lt hTlim (uuTh_lt_Y2 hl hX hdH hdY) w hw hwE
    obtain ⟨c', hc'Q, huc'⟩ := hB2 Q hQ u hu hud
    exact ⟨c', hc'Q, hwu.trans_le (psi_mono hκ2 (huc'.le.trans le_self_add)).1⟩
  · intro Q hQ c h hc1 hcQ h1 h2 hh
    rcases h1.lt_or_eq with h1 | h1
    swap
    · rw [h1]; exact hh
    have hM1d : M c + 1 < d := by
      by_contra hc
      push Not at hc
      exact absurd ((h1.trans_le h2).trans_le (psi_mono hκ hc).1) (lt_irrefl _)
    have hM1n : M c + 1 < S.psi (M c + 1) (Om (1 + 1 + 1)) := uuLt3 (hM1d.trans hdY)
    by_cases hmQ : S.psi (M c + 1) (Om (1 + 1 + 1)) < Q
    · exact UgC.small hmQ
    push Not at hmQ
    obtain ⟨e', he'c, hee', he'd⟩ := uuAtom_between hd hmQ h1.le h2 hh
    have hMc : UgC S (1 + 1) Q (M c) := hB3 Q hQ c e' hc1 hcQ (le_self_add.trans hee') he'd he'c
    exact UgC.psi (UgC.add hMc (UgC.small (gg_one_lt_of_SC hQ))) hM1n

end Main

end Googology.Trans.PoR.InaccPsi.R2.Uu

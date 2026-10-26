import Googology.Trans.PoR.InaccPsi.R2.UuPsi

/-!
# Level codes below a `ψ_{Ω_{k+1}}`-atom: the atom lemma and the decomposition at a limit argument

`C_k(Q) = Ug.UgC S k Q` (codes of level `k` over `Q` with the atoms `ψ_{Ω_{k+1}}(d)`, `d` a code, `d < ψ(d)`),
`ψ = ψ_{Ω_{k+1}}`, `Y_k = ψ(Ω_{k+1})`.

* `uuC_atom` (**THE ATOM LEMMA**: a code `h ≥ P` with `P` strongly critical, `Q ≤ P`, `Ω_k < P` contains an atom
  `ψ(e)` with `P ≤ ψ(e) ≤ h`, `e` a code, `e < ψ(e)`);
* `uuCl_dec` (**THE DECOMPOSITION BELOW `ψ(X)`**: for a limit `X < Y_k`, every code `w < ψ(X)` is below `ψ(u)` for a
  code `u < X`; the small codes by the continuity `Lw.lw_psi_limit` and the normal arguments `Uu.uuLtPsi`);
* `uuNormLt` (**normal-argument comparison**: for a normal `e`, `e < d ↔ ψ(e) < ψ(d)`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Uu

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ug

variable {S : InaccSeq.{0}}

/-- **THE ATOM LEMMA**: a level-`k` code `h ≥ P` (`P` strongly critical, `Q ≤ P`, `Ω_k < P`) contains an atom
`ψ_{Ω_{k+1}}(e)`, `e` a code with `e < ψ(e)`, with `P ≤ ψ(e) ≤ h`. -/
theorem uuC_atom {k Q : Ordinal.{0}} : ∀ h, UgC S k Q h → ∀ P, SC P → Q ≤ P → Om k < P → P ≤ h →
    ∃ e, UgC S k Q e ∧ e < S.psi e (Om (k + 1)) ∧ P ≤ S.psi e (Om (k + 1)) ∧ S.psi e (Om (k + 1)) ≤ h := by
  intro h hh
  induction hh with
  | small hlt => exact fun P _ hQP _ hPh => absurd (hlt.trans_le hQP) (not_lt.2 hPh)
  | om => exact fun P _ _ hkP hPh => absurd hkP (not_lt.2 hPh)
  | @add x y _ _ ihx ihy =>
    intro P hP hQP hkP hPh
    by_cases hx : P ≤ x
    · obtain ⟨e, he, hel, h1, h2⟩ := ihx P hP hQP hkP hx
      exact ⟨e, he, hel, h1, h2.trans le_self_add⟩
    by_cases hy : P ≤ y
    · obtain ⟨e, he, hel, h1, h2⟩ := ihy P hP hQP hkP hy
      exact ⟨e, he, hel, h1, h2.trans le_add_self⟩
    push Not at hx hy
    exact absurd (hP.isPrincipal hx hy) (not_lt.2 hPh)
  | @phi x y _ _ ihx ihy =>
    intro P hP hQP hkP hPh
    by_cases hx : P ≤ x
    · obtain ⟨e, he, hel, h1, h2⟩ := ihx P hP hQP hkP hx
      exact ⟨e, he, hel, h1, h2.trans (left_le_veblen x y)⟩
    by_cases hy : P ≤ y
    · obtain ⟨e, he, hel, h1, h2⟩ := ihy P hP hQP hkP hy
      exact ⟨e, he, hel, h1, h2.trans (right_le_veblen x y)⟩
    push Not at hx hy
    exact absurd (hP.2 _ hx _ hy) (not_lt.2 hPh)
  | @psi d hd hdl _ => exact fun P _ _ _ hPh => ⟨d, hd, hdl, hPh, le_rfl⟩

/-- **Normal-argument comparison**: for `e < ψ(e)`, `e < d ↔ ψ(e) < ψ(d)`. -/
theorem uuNormLt (k : Ordinal.{0}) {e d : Ordinal.{0}} (he : e < S.psi e (Om (k + 1))) :
    e < d ↔ S.psi e (Om (k + 1)) < S.psi d (Om (k + 1)) := by
  have hκ : S.InR (Om (k + 1)) := InR_Om_succ k
  refine ⟨fun h => psi_lt_psi hκ h (CSet.of_lt he), fun h => ?_⟩
  by_contra hc
  push Not at hc
  exact absurd h (not_lt.2 (psi_mono hκ hc).1)

/-- `ψ(e) < ψ(e + 1)` at a normal `e`. -/
theorem uuPsi_lt_succ (k : Ordinal.{0}) {e : Ordinal.{0}} (he : e < S.psi e (Om (k + 1))) :
    S.psi e (Om (k + 1)) < S.psi (e + 1) (Om (k + 1)) :=
  (uuNormLt k he).1 (lt_add_one e)

/-- **THE DECOMPOSITION BELOW `ψ(X)`**: for a limit `X < Y_k = ψ(Ω_{k+1})`, a code `w < ψ(X)` is below `ψ(u)` for a
code `u < X`. -/
theorem uuCl_dec {k Q : Ordinal.{0}} (hQ : SC Q) (hks : k + 1 < Om 1) {X : Ordinal.{0}} (hXl : IsSuccLimit X)
    (hXY : X < S.psi (Om (k + 1)) (Om (k + 1))) :
    ∀ w, UgC S k Q w → w < S.psi X (Om (k + 1)) → ∃ u, UgC S k Q u ∧ u < X ∧ w < S.psi u (Om (k + 1)) := by
  have hκ : S.InR (Om (k + 1)) := InR_Om_succ k
  have h1Q : (1 : Ordinal.{0}) < Q := Gg.gg_one_lt_of_SC hQ
  have hmax : ∀ u1 u2, UgC S k Q u1 → UgC S k Q u2 → UgC S k Q (max u1 u2) := fun u1 u2 h1 h2 => by
    rcases le_total u1 u2 with h | h
    · rw [max_eq_right h]; exact h2
    · rw [max_eq_left h]; exact h1
  intro w hw
  induction hw with
  | @small w hwQ =>
    intro hlt
    by_cases hwX : w < X
    · refine ⟨w + 1, UgC.small (hQ.add_one_lt hwQ), hXl.add_one_lt hwX, ?_⟩
      exact (uuLtPsi hks (hwX.trans hXY)).trans_le (psi_mono hκ le_self_add).1
    · push Not at hwX
      rw [Lw.lw_psi_limit S hκ hXl] at hlt
      have hbdd : BddAbove (range fun e : Iio X => S.psi e.1 (Om (k + 1))) :=
        ⟨Om (k + 1), by rintro _ ⟨e, rfl⟩; exact (psi_lt hκ _).le⟩
      haveI : Nonempty (Iio X) := ⟨⟨0, hXl.bot_lt⟩⟩
      obtain ⟨⟨u, hu⟩, hwu⟩ := (lt_ciSup_iff hbdd).1 hlt
      exact ⟨u, UgC.small ((show u < X from hu).trans_le hwX |>.trans hwQ), hu, hwu⟩
  | om => exact fun _ => ⟨0, UgC.zero hQ.1, hXl.bot_lt, (psiS_bounds 0 k).1⟩
  | @add x y _ _ ihx ihy =>
    intro hlt
    obtain ⟨u1, h1, hu1, hx1⟩ := ihx (le_self_add.trans_lt hlt)
    obtain ⟨u2, h2, hu2, hy2⟩ := ihy (le_add_self.trans_lt hlt)
    refine ⟨max u1 u2, hmax u1 u2 h1 h2, max_lt hu1 hu2, (SC_psi hκ _).isPrincipal ?_ ?_⟩
    · exact hx1.trans_le (psi_mono hκ (le_max_left _ _)).1
    · exact hy2.trans_le (psi_mono hκ (le_max_right _ _)).1
  | @phi x y _ _ ihx ihy =>
    intro hlt
    obtain ⟨u1, h1, hu1, hx1⟩ := ihx ((left_le_veblen x y).trans_lt hlt)
    obtain ⟨u2, h2, hu2, hy2⟩ := ihy ((right_le_veblen x y).trans_lt hlt)
    refine ⟨max u1 u2, hmax u1 u2 h1 h2, max_lt hu1 hu2, (SC_psi hκ _).2 _ ?_ _ ?_⟩
    · exact hx1.trans_le (psi_mono hκ (le_max_left _ _)).1
    · exact hy2.trans_le (psi_mono hκ (le_max_right _ _)).1
  | @psi d hd hdl _ =>
    intro hlt
    have hdX : d < X := by
      by_contra hc
      push Not at hc
      exact absurd hlt (not_lt.2 (psi_mono hκ hc).1)
    exact ⟨d + 1, UgC.add hd (UgC.small h1Q), hXl.add_one_lt hdX, uuPsi_lt_succ k hdl⟩

end Googology.Trans.PoR.InaccPsi.R2.Uu

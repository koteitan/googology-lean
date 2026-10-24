import Googology.Trans.PoR.InaccPsi.R2.GiWI

/-!
# LEMMA IMG FOR A SPECIFIED FUNCTION: from Lemma EXACT and one existential witness

`RstK.pkg_atomT`, `RstK.pkgL` and `RstK.imgA` give Lemma IMG only for SOME term whose value at the restart `ρ` is the
given ordinal.  The union step (`Gh.GhUF.pkg`) asks Lemma IMG for a GIVEN function `T` (the logend of a reading).  Here
the two are joined by Lemma EXACT: a covering copy `f` sends `ρ` to a `υ`-point `f(ρ) < ρ` above the constants, so
`(f(ρ), ρ)` is a pair of bases; if `T` and the witness term `s` both satisfy `π_{f(ρ),ρ}(T ρ) = T(f ρ)` and
`π_{f(ρ),ρ}(s ρ) = s(f ρ)` and `T ρ = s ρ`, then `T(f ρ) = s(f ρ) ≤ f(s ρ) = f(T ρ)`.  The witness is the term of
`OTY` of `RstK.imgY` (every value below `ε_{ρ+2}`), its Lemma EXACT is `pi_evY` with `ε_{ρ+1} ∈ Tᵖ[σ]` from
`Gh.gh_eN_pi`.

* `GjEx` (Lemma EXACT for a function at the `υ`-point pairs above a gate, constants below the smaller base),
  `gjPkg_of_ex` (**Lemma IMG (gated) for every function with Lemma EXACT and value below `ε_{ρ+2}`**),
  `gjImgPkg_of_ex` (the ungated package `ImgPkg`);
* the terms `GjT` (constants, the base `x`, `+`, `ω^·`, `ε_{·+1}`, `·n`), `GjT.ev`, `GjT.CB`, `GjT.WF` (the argument
  of `ε_{·+1}` lies in `[y, ε_{y+n})` for some finite `n`), `GjT.ev_lt_Om1`, `gjT_pi` (**Lemma EXACT for every term, by
  one induction on the term**: `pi_add`, `pi_opowZ`, the brackets `[ε_{ρ+c}, ε_{ρ+c+1})` and `pi_evAZ`),
  `gjT_pkg` (**Lemma IMG for every term itself**, value below `ε_{ρ+2}`), `gjT_imgPkg`;
* `gjAtom_pkg` (**`imgA` for a specified term**: the atom `ω^{ε_{y+1}+t(y)}` for every term `t`), `gj_pkg_Ew` (the
  logend `ω^{ε_{y+1}+1}` of the reading `ε_{y+1}^ω` of the code `ε_{Ω₁+1}^ω`, where round 80 stopped).

No new axiom.  New definitions: `GjEx`, `GjT`, `GjT.ev`, `GjT.cs`, `GjT.CB`, `GjT.WF`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gj

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gd OTY

/-- **Lemma EXACT for a function `T` above the gate `g` with constants `C`**: at every pair of `υ`-points `σ < ρ` with
`g < σ` and all constants below `σ`, `T ρ ∈ Tᵖ[σ]` and `π_{σ,ρ}(T ρ) = T σ`. -/
def GjEx (g : Ordinal.{0}) (C : Finset Ordinal.{0}) (T : Ordinal.{0} → Ordinal.{0}) : Prop :=
  ∀ σ ρ, UpsPt σ → UpsPt ρ → Bases σ ρ → g < σ → (∀ c ∈ C, c < σ) → T ρ ∈ TB ρ σ ∧ pi σ ρ (T ρ) = T σ

theorem GjEx.mono {g g' : Ordinal.{0}} {C : Finset Ordinal.{0}} {T : Ordinal.{0} → Ordinal.{0}} (h : GjEx g C T)
    (hg : g ≤ g') : GjEx g' C T := fun σ ρ hσ hρ hB hgσ hC => h σ ρ hσ hρ hB (hg.trans_lt hgσ) hC

/-- A function with Lemma EXACT at every pair of bases above the gate has it at the `υ`-point pairs. -/
theorem GjEx.of_bases {g : Ordinal.{0}} {T : Ordinal.{0} → Ordinal.{0}}
    (h : ∀ σ ρ, Bases σ ρ → g < σ → T ρ ∈ TB ρ σ ∧ pi σ ρ (T ρ) = T σ) : GjEx g ∅ T :=
  fun σ ρ _ _ hB hg _ => h σ ρ hB hg

theorem wz_consts {ρ δ : Ordinal.{0}} {C : Finset Ordinal.{0}} (hC : ∀ c ∈ C, c < ρ) : WZ ρ δ ∅ C :=
  ⟨by simp, hC, by simp⟩

section Pkg

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **LEMMA IMG FOR A SPECIFIED FUNCTION (gated)**: if `T` has Lemma EXACT above the gate `g < ρ` with constants
`C < ρ`, and `T ρ < ε_{ρ+2}`, then every covering copy `f` that keeps `g` (and contains `C` and the witness sets) has
`T(f ρ) ≤ f(T ρ)`. -/
theorem gjPkg_of_ex {g : Ordinal.{0}} {C : Finset Ordinal.{0}} {T : Ordinal.{0} → Ordinal.{0}} (hgρ : g < ρ)
    (hC : ∀ c ∈ C, c < ρ) (hT : T ρ < eN (eN ρ)) (hex : GjEx g C T) : GhPkg g ρ δ T := by
  classical
  obtain ⟨W, Z, s, ⟨w, cb, cs, e, m, b⟩, -⟩ := h.imgY (T ρ) hT
  have w' := w.union (wz_consts (δ := δ) hC)
  rw [Finset.union_empty] at w'
  refine ⟨W, Z ∪ C, w', ?_, fun A f hW hZ Cx => ?_⟩
  · rcases Finset.mem_union.1 m with hm | hm
    · exact Finset.mem_union_left _ hm
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ hm)
  have hZ' : ↑Z ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
  have hCA : ∀ c ∈ C, c ∈ A := fun c hc => hZ (by simp [hc])
  have I := Cx.toImgCtx
  have hσU : UpsPt (f ρ) := I.ups
  have hB : Bases (f ρ) ρ := h.img_bases I
  have hCσ : ∀ c ∈ C, c < f ρ := fun c hc => I.above c (hCA c hc) (hC c hc)
  have hs : CBY s (f ρ) := img_cbY I cb (fun c hc => hZ' (Finset.mem_coe.2 (cs c hc)))
  obtain ⟨-, hps⟩ := pi_evY hσU h.ρU hB (gh_eN_pi hB).1 s hs
  obtain ⟨-, hpT⟩ := hex (f ρ) ρ hσU h.ρU hB (Cx.lt hgρ) hCσ
  have hTs : T (f ρ) = ev2 s (f ρ) := by rw [← hpT, ← e, hps]
  rw [hTs]
  exact b A f hW hZ' I

/-- **LEMMA IMG FOR A SPECIFIED FUNCTION (ungated package)**: `1 ≤ T ρ < ε_{ρ+2}` and Lemma EXACT at every `υ`-point
pair with the constants below the smaller base give `ImgPkg ρ δ T`. -/
theorem gjImgPkg_of_ex {C : Finset Ordinal.{0}} {T : Ordinal.{0} → Ordinal.{0}} (hC : ∀ c ∈ C, c < ρ)
    (h1 : 1 ≤ T ρ) (hT : T ρ < eN (eN ρ))
    (hex : ∀ σ, UpsPt σ → Bases σ ρ → (∀ c ∈ C, c < σ) → T ρ ∈ TB ρ σ ∧ pi σ ρ (T ρ) = T σ) :
    ImgPkg ρ δ T := by
  classical
  obtain ⟨W, Z, s, ⟨w, cb, cs, e, m, b⟩, -⟩ := h.imgY (T ρ) hT
  have w' := w.union (wz_consts (δ := δ) hC)
  rw [Finset.union_empty] at w'
  refine ⟨h1, hT.trans h.eNN_lt_δ, W, Z ∪ C, w', ?_, fun A f hW hZ I => ?_⟩
  · rcases Finset.mem_union.1 m with hm | hm
    · exact Finset.mem_union_left _ hm
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ hm)
  have hZ' : ↑Z ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
  have hCA : ∀ c ∈ C, c ∈ A := fun c hc => hZ (by simp [hc])
  have hσU : UpsPt (f ρ) := I.ups
  have hB : Bases (f ρ) ρ := h.img_bases I
  have hCσ : ∀ c ∈ C, c < f ρ := fun c hc => I.above c (hCA c hc) (hC c hc)
  have hs : CBY s (f ρ) := img_cbY I cb (fun c hc => hZ' (Finset.mem_coe.2 (cs c hc)))
  obtain ⟨-, hps⟩ := pi_evY hσU h.ρU hB (gh_eN_pi hB).1 s hs
  obtain ⟨-, hpT⟩ := hex (f ρ) hσU hB hCσ
  have hTs : T (f ρ) = ev2 s (f ρ) := by rw [← hpT, ← e, hps]
  rw [hTs]
  exact b A f hW hZ' I

end Pkg

/-! ## The terms -/

/-- **The terms**: constants, the base `x`, sums, `ω^t`, `ε_{t+1}` (the least `ε`-number above `t`), `t·n`. -/
inductive GjT : Type 1
  | k : Ordinal.{0} → GjT
  | x : GjT
  | add : GjT → GjT → GjT
  | opow : GjT → GjT
  | eps : GjT → GjT
  | nmul : GjT → ℕ → GjT

namespace GjT

/-- The value at the base `y`. -/
noncomputable def ev : GjT → Ordinal.{0} → Ordinal.{0}
  | k a, _ => a
  | x, y => y
  | add t u, y => ev t y + ev u y
  | opow t, y => ω ^ ev t y
  | eps t, y => eN (ev t y)
  | nmul t n, y => ev t y * (n : Ordinal.{0})

/-- The constants. -/
def cs : GjT → List Ordinal.{0}
  | k a => [a]
  | x => []
  | add t u => cs t ++ cs u
  | opow t => cs t
  | eps t => cs t
  | nmul t _ => cs t

/-- All constants below `s`. -/
def CB (t : GjT) (s : Ordinal.{0}) : Prop := ∀ c ∈ cs t, c < s

/-- **Well-formed at the base `y`**: the argument of every `ε_{·+1}` lies in `[y, ε_{y+n})` for a finite `n`. -/
def WF : GjT → Ordinal.{0} → Prop
  | k _, _ => True
  | x, _ => True
  | add t u, y => WF t y ∧ WF u y
  | opow t, y => WF t y
  | eps t, y => WF t y ∧ y ≤ ev t y ∧ ∃ n : ℕ, ev t y < evA y n
  | nmul t _, y => WF t y

@[simp] theorem ev_k (a y : Ordinal.{0}) : ev (k a) y = a := rfl
@[simp] theorem ev_x (y : Ordinal.{0}) : ev x y = y := rfl
@[simp] theorem ev_add (t u : GjT) (y : Ordinal.{0}) : ev (add t u) y = ev t y + ev u y := rfl
@[simp] theorem ev_opow (t : GjT) (y : Ordinal.{0}) : ev (opow t) y = ω ^ ev t y := rfl
@[simp] theorem ev_eps (t : GjT) (y : Ordinal.{0}) : ev (eps t) y = eN (ev t y) := rfl
@[simp] theorem ev_nmul (t : GjT) (n : ℕ) (y : Ordinal.{0}) : ev (nmul t n) y = ev t y * (n : Ordinal.{0}) := rfl

theorem CB_add {t u : GjT} {s : Ordinal.{0}} : CB (add t u) s ↔ CB t s ∧ CB u s := by
  simp only [CB, cs, List.mem_append]
  constructor
  · intro h; exact ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩
  · rintro ⟨h1, h2⟩ c (hc | hc)
    · exact h1 c hc
    · exact h2 c hc

theorem CB_mono {t : GjT} {s s' : Ordinal.{0}} (h : CB t s) (hs : s ≤ s') : CB t s' :=
  fun c hc => (h c hc).trans_le hs

/-- **Every value at a countable base is countable** (constants countable). -/
theorem ev_lt_Om1 {y : Ordinal.{0}} (hy : y < Om1) : ∀ t : GjT, CB t Om1 → ev t y < Om1
  | k a, h => h a (by simp [cs])
  | x, _ => hy
  | add t u, h => Om1_add_lt (ev_lt_Om1 hy t (CB_add.1 h).1) (ev_lt_Om1 hy u (CB_add.1 h).2)
  | opow t, h => Om1_opow_lt (ev_lt_Om1 hy t h)
  | eps t, h => eN_lt_Om1K (ev_lt_Om1 hy t h)
  | nmul t n, h => by
    rw [ev_nmul]
    exact (Rj.rj_Om1_inE).mul_lt (ev_lt_Om1 hy t h) ((natCast_lt_omega0 n).trans Gf.omega_lt_Om1)

end GjT

open GjT

/-- The least `ε`-number above a point of the bracket `[ε_{y+c}, ε_{y+c+1})` is `ε_{y+c+1}`. -/
theorem gj_eN_bracket {y c L : Ordinal.{0}} (h1 : evA y c ≤ L) (h2 : L < evA y (c + 1)) : eN L = evA y (c + 1) :=
  le_antisymm (eN_le h2 (evA_E _ _)) (by rw [evA_add_one]; exact eN_le (h1.trans_lt (lt_eN L)) (eN_E L))

/-- **Lemma EXACT for `ε_{u+1}`** once it holds for `u` and `u(ρ)` lies in `[ρ, ε_{ρ+n})`, `n` finite. -/
theorem gj_pi_eN {σ ρ u u' : Ordinal.{0}} (hB : Bases σ ρ) (huT : u ∈ TB ρ σ) (hpu : pi σ ρ u = u')
    (hρu : ρ ≤ u) {n : ℕ} (hun : u < evA ρ n) : eN u ∈ TB ρ σ ∧ pi σ ρ (eN u) = eN u' := by
  obtain ⟨c, hcn, hc1, hc2⟩ := evA_bracket hB.2.1 hρu hun
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, c = m := lt_omega0.1 (hcn.trans (natCast_lt_omega0 n))
  have hσω : ω < σ := omega0_lt_inE hB.1
  have hmσ : (m : Ordinal.{0}) < σ := (natCast_lt_omega0 m).trans hσω
  have hm1σ : (m : Ordinal.{0}) + 1 < σ := by
    have := (natCast_lt_omega0 (m + 1)).trans hσω; push_cast at this; exact this
  have hevZ : ∀ z : Ordinal.{0}, InE z → ∀ j : Ordinal.{0}, j < z → j < evZ z := fun z _ j hj =>
    hj.trans (lt_evZ z)
  have hmT := mem_TB_of_lt hB hmσ
  have hm1T := mem_TB_of_lt hB hm1σ
  obtain ⟨a1, a2⟩ := pi_evAZ hB hmT (hevZ ρ hB.2.1 _ (hmσ.trans hB.2.2.1))
    (by rw [pi_lt hB hmσ]; exact hevZ σ hB.1 _ hmσ)
  obtain ⟨b1, b2⟩ := pi_evAZ hB hm1T (hevZ ρ hB.2.1 _ (hm1σ.trans hB.2.2.1))
    (by rw [pi_lt hB hm1σ]; exact hevZ σ hB.1 _ hm1σ)
  rw [pi_lt hB hmσ] at a2
  rw [pi_lt hB hm1σ] at b2
  have hmono := (pi_bijOn hB).2
  have k1 : evA σ m ≤ u' := by rw [← a2, ← hpu]; exact (hmono.le_iff_le a1 huT).2 hc1
  have k2 : u' < evA σ (m + 1) := by rw [← b2, ← hpu]; exact hmono huT b1 hc2
  rw [gj_eN_bracket hc1 hc2, gj_eN_bracket k1 k2]
  exact ⟨b1, b2⟩

/-- **LEMMA EXACT FOR EVERY TERM, by one induction on the term**: for `υ`-points `σ < ρ` (bases), constants below `σ`
and the term well-formed at `ρ`, `t(ρ) ∈ Tᵖ[σ]` and `π_{σ,ρ}(t(ρ)) = t(σ)`. -/
theorem gjT_pi {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) :
    ∀ t : GjT, CB t σ → WF t ρ → ev t ρ ∈ TB ρ σ ∧ pi σ ρ (ev t ρ) = ev t σ
  | GjT.k a, h, _ => by
    have ha : a < σ := h a (by simp [cs])
    exact ⟨mem_TB_of_lt hB ha, pi_lt hB ha⟩
  | GjT.x, _, _ => pi_base hB
  | GjT.add t u, h, hw => by
    obtain ⟨h1, h2⟩ := gjT_pi hσ hρ hB t (CB_add.1 h).1 hw.1
    obtain ⟨h3, h4⟩ := gjT_pi hσ hρ hB u (CB_add.1 h).2 hw.2
    obtain ⟨h5, h6⟩ := pi_add hB h1 h3
    exact ⟨h5, by rw [ev_add, h6, h2, h4, ev_add]⟩
  | GjT.opow t, h, hw => by
    obtain ⟨h1, h2⟩ := gjT_pi hσ hρ hB t h hw
    have hlt : ev t ρ < Om1 := GjT.ev_lt_Om1 hB.2.2.2 t (CB_mono h (hB.2.2.1.trans hB.2.2.2).le)
    obtain ⟨h3, h4⟩ := pi_opowZ hσ hρ hB h1 hlt
    exact ⟨h3, by rw [ev_opow, h4, h2, ev_opow]⟩
  | GjT.eps t, h, hw => by
    obtain ⟨h1, h2⟩ := gjT_pi hσ hρ hB t h hw.1
    obtain ⟨n, hn⟩ := hw.2.2
    exact gj_pi_eN hB h1 h2 hw.2.1 hn
  | GjT.nmul t n, h, hw => by
    obtain ⟨h1, h2⟩ := gjT_pi hσ hρ hB t h hw
    have key : ∀ j : ℕ, ev t ρ * (j : Ordinal.{0}) ∈ TB ρ σ ∧
        pi σ ρ (ev t ρ * (j : Ordinal.{0})) = ev t σ * (j : Ordinal.{0}) := by
      intro j
      induction j with
      | zero =>
        simp only [Nat.cast_zero, mul_zero]
        exact ⟨mem_TB_of_lt hB hB.1.pos, pi_lt hB hB.1.pos⟩
      | succ j ih =>
        obtain ⟨k1, k2⟩ := ih
        obtain ⟨k3, k4⟩ := pi_add hB k1 h1
        simp only [Nat.cast_succ, mul_add_one]
        exact ⟨k3, by rw [k4, k2, h2]⟩
    exact key n

/-- **Lemma EXACT for a term as a function** (`GjEx` with the constants of the term), when the term is well-formed at
every `ε`-number base above the gate. -/
theorem gjT_ex {g : Ordinal.{0}} (t : GjT) (hw : ∀ y, InE y → y < Om1 → g < y → WF t y) :
    GjEx g (cs t).toFinset (ev t) := fun σ ρ hσ hρ hB hg hC =>
  gjT_pi hσ hρ hB t (fun c hc => hC c (List.mem_toFinset.2 hc))
    (hw ρ hB.2.1 hB.2.2.2 (hg.trans hB.2.2.1))

section TermPkg

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **LEMMA IMG FOR EVERY TERM ITSELF (gated)**: constants below `ρ`, well-formed above the gate, value at `ρ` below
`ε_{ρ+2}`. -/
theorem gjT_pkg {g : Ordinal.{0}} (t : GjT) (hgρ : g < ρ) (hcb : CB t ρ)
    (hw : ∀ y, InE y → y < Om1 → g < y → WF t y) (hv : ev t ρ < eN (eN ρ)) : GhPkg g ρ δ (ev t) :=
  gjPkg_of_ex h hgρ (fun c hc => hcb c (List.mem_toFinset.1 hc)) hv (gjT_ex t hw)

/-- **LEMMA IMG FOR EVERY TERM ITSELF (package)**: `1 ≤ t(ρ) < ε_{ρ+2}`, constants below `ρ`, well-formed at the
bases below `ρ`. -/
theorem gjT_imgPkg (t : GjT) (hcb : CB t ρ) (hw : ∀ y, InE y → y ≤ ρ → WF t y) (h1 : 1 ≤ ev t ρ)
    (hv : ev t ρ < eN (eN ρ)) : ImgPkg ρ δ (ev t) :=
  gjImgPkg_of_ex h (fun c hc => hcb c (List.mem_toFinset.1 hc)) h1 hv fun σ hσ hB hC =>
    gjT_pi hσ h.ρU hB t (fun c hc => hC c (List.mem_toFinset.2 hc)) (hw ρ hB.2.1 le_rfl)

/-- **`imgA` FOR A SPECIFIED TERM**: Lemma IMG for the atom `y ↦ ω^{ε_{y+1}+t(y)}` itself, for every term `t` with
constants below `ρ`, well-formed above the gate, and `ω^{ε_{ρ+1}+t(ρ)} < ε_{ρ+2}` (e.g. `t(ρ) < ε_{ρ+2}`). -/
theorem gjAtom_pkg {g : Ordinal.{0}} (t : GjT) (hgρ : g < ρ) (hcb : CB t ρ)
    (hw : ∀ y, InE y → y < Om1 → g < y → WF t y) (hv : ω ^ (eN ρ + ev t ρ) < eN (eN ρ)) :
    GhPkg g ρ δ (fun y => ω ^ (eN y + ev t y)) := by
  have e : (fun y => ω ^ (eN y + ev t y)) = ev (opow (add (eps x) t)) := rfl
  rw [e]
  refine gjT_pkg h _ hgρ (fun c hc => hcb c (by simpa [cs] using hc)) (fun y hy hy1 hgy => ?_) hv
  have e1 : evA y ((1 : ℕ) : Ordinal.{0}) = eN y := by
    rw [Nat.cast_one, show (1 : Ordinal.{0}) = 0 + 1 by simp, evA_add_one, evA_zero hy]
  exact ⟨⟨trivial, le_rfl, 1, by rw [e1]; exact lt_eN y⟩, hw y hy hy1 hgy⟩

/-- **The logend at the code `ε_{Ω₁+1}^ω`** (where round 80 stopped): the reading `ε_{y+1}^ω = ω^{ω^{ε_{y+1}+1}}` has
logend `ω^{ε_{y+1}+1}`, and Lemma IMG holds for `y ↦ ω^{ε_{y+1}+1}` itself, above every gate. -/
theorem gj_pkg_Ew {g : Ordinal.{0}} (hgρ : g < ρ) : GhPkg g ρ δ (fun y => ω ^ (eN y + 1)) := by
  have h1ρ : (1 : Ordinal.{0}) < ρ := one_lt_of_upsPt h.ρU
  have e : (fun y => ω ^ (eN y + 1)) = fun y => ω ^ (eN y + ev (k 1) y) := rfl
  rw [e]
  refine gjAtom_pkg h (k 1) hgρ (fun c hc => by simp [cs] at hc; rw [hc]; exact h1ρ) (fun _ _ _ _ => trivial) ?_
  have hE := eN_E (eN ρ)
  have hlt : eN ρ + 1 < eN (eN ρ) :=
    (inE_indec hE).add_lt (lt_eN _) (one_lt_omega0.trans (omega0_lt_inE hE))
  exact hE.opow_lt hlt

end TermPkg

end Googology.Trans.PoR.InaccPsi.R2.Gj

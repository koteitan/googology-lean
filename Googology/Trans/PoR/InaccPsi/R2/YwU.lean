import Googology.Trans.PoR.InaccPsi.R2.YwLev
import Googology.Trans.PoR.InaccPsi.R2.YrDir

/-!
# YwU: THE TOP WITNESS FROM LEMMA IMG, AND THE UNION STEP AT EVERY TOP BELOW `X^x` (CLOSED TOPS INCLUDED)

Every layer construction so far proves its top witness by a reach computation at its own top (`Yr.YrUK.yrTopWit`:
`G ≤₁ G·G + G + logend(l)` and the separation `Yr.yr_not_le1R_lim`), which needs an admissible offset; so no union
could have a top that is a fixed point of `ν ↦ Γ_{x+1+ν}` (`Yw.ywNoGo_GqSt`).  Here the top witness comes from Lemma
IMG at the top (`Yw.ywImg`, every value below `X^ρ`), with no reach computation:

* `ywTopWit_of_GnI` (**THE TOP WITNESS OF ANY `ε`-NUMBER WITH LEMMA IMG**), `ywTopWit` (**of every `ε`-number
  `T(ρ) ∈ (ρ, X^ρ)` with Lemma EXACT for `T`**);
* `YwUF g` (a family of gated layers `K_i`, a target `T(x)`: an `ε`-number in `Tˣ ∩ (x, X^x)` above the member tops
  and cofinal over them, Lemma EXACT for `T`), `ywUSys` (the union), `ywLimL`, `ywLimB` (**THE GATED UNION LAYER WITH
  TOP `T(x)`**);
* the instance at the first fixed point of `Γ`: `ywS` (the tower readings `s_n(x) = yrR(a_n)(x)`, `a_0 = G`,
  `a_{n+1} = Γ(a_n)`), `ywS_lt_D`, `ywS_cof` (**`sup_n s_n(x) = ϑˣ(Ω₁·Ω₁ + Ω₁)`**), `ywBGF`, `ywBGB`
  (**THE LAYER OF THE CODE `B_Γ`**: a gated layer, gate `0`, top `ϑˣ(Ω₁·Ω₁ + Ω₁)` at every base, the union of the
  layers `Yr.YrRS.gqL a_n` of the tower), `ywBGB_E`.

No new axiom.  New definitions: `YwUF`, `ywUSys`, `ywLimL`, `ywLimB`, `ywS`, `ywTwL`, `ywBGF`, `ywBGB`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Gk
  Googology.Trans.PoR.InaccPsi.R2.Xx Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Gl

section Top

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **THE TOP WITNESS OF AN `ε`-NUMBER `E > ρ` WITH LEMMA IMG**: `f(E) ∈ E` and `π(E) ≤ f(E)` for the copies. -/
theorem ywTopWit_of_GnI {E : Ordinal.{0}} (hE : InE E) (hρE : ρ < E) (hI : GnI ρ δ E) :
    ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ E ∈ W ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
        (∃ e', f E = ω ^ e' ∧ ω ^ f ρ ∣ e') ∧ pi (f ρ) ρ E ≤ f E := by
  classical
  obtain ⟨W, Z, w, -, hET, hE1, b⟩ := gnI_use h hI
  have hEδ : E < δ := gn_lt_δ h hET hE1
  have hEEδ : E + E < δ := (inE_indec h.δE).add_lt hEδ hEδ
  have w1 : WZ ρ δ (insert E W) Z := w.insW hρE.le hEδ (Or.inl (inE_indec hE))
  have w2 : WZ ρ δ (insert (E + E) (insert E W)) Z := w1.insW (hρE.le.trans le_self_add) hEEδ
    (Or.inr ⟨E, Finset.mem_union_left _ (Finset.mem_insert_self _ _), E,
      Finset.mem_union_left _ (Finset.mem_insert_self _ _), lt_add_of_pos_right _ hE.pos,
      lt_add_of_pos_right _ hE.pos, rfl⟩)
  refine ⟨_, Z, w2, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), fun A f hW hZ C => ?_⟩
  have hWA : ↑W ⊆ A := fun a ha =>
    hW (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_coe.1 ha))))
  obtain ⟨hEA, -, hle⟩ := b A f hWA hZ C
  have hEEA : E + E ∈ A := hW (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
  have hfρE : f ρ < f E := C.mono C.rho hEA hρE
  have hfE : InE (f E) := gk_img_inE C hEA hEEA (gk_src2 h hE hρE hEEδ.le) (lt_of_le_of_lt zero_le hfρE)
  exact ⟨⟨f E, hfE.symm, opow_dvd_of_inE hfE hfρE.le⟩, hle⟩

/-- **THE TOP WITNESS OF EVERY `ε`-NUMBER TOP `T(ρ) ∈ (ρ, X^ρ)` WITH LEMMA EXACT** (for the copies that keep a gate
`g < ρ`, `T` exact above `g`). -/
theorem ywTopWit {g : Ordinal.{0}} {T : Ordinal.{0} → Ordinal.{0}} (hgρ : g < ρ) (hE : InE (T ρ)) (hρE : ρ < T ρ)
    (hX : T ρ < ywX ρ) (hpi : ∀ σ, UpsPt σ → Bases σ ρ → g < σ → pi σ ρ (T ρ) = T σ) :
    ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ T ρ ∈ W ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → GdCtx g ρ A f →
        (∃ e', f (T ρ) = ω ^ e' ∧ ω ^ f ρ ∣ e') ∧ T (f ρ) ≤ f (T ρ) := by
  obtain ⟨W, Z, w, hTW, hI⟩ := ywTopWit_of_GnI h hE hρE (ywImg h _ hX)
  refine ⟨W, Z, w, hTW, fun A f hW hZ C => ?_⟩
  obtain ⟨h1, h2⟩ := hI A f hW hZ C.1
  refine ⟨h1, ?_⟩
  rw [← hpi (f ρ) C.ups (h.img_bases C.1) (C.lt hgρ)]
  exact h2

end Top

/-- **The data of a union step with an arbitrary top**: a family `K_i` of gated layers (side gates `g_i`), a target
`T(x)`: an `ε`-number of `Tˣ ∩ (x, X^x)` above every member top `E_i(x)` and cofinal over them, Lemma EXACT for `T`;
a member `i₀` with side gate `0` (for the constants). -/
structure YwUF (g : Ordinal.{0}) where
  I : Type 1
  K : I → GdB
  gi : I → Ordinal.{0}
  i0 : I
  g_le : ∀ i, (K i).g ≤ gi i
  gi0 : gi i0 = 0
  T : Ordinal.{0} → Ordinal.{0}
  T_E : ∀ x, InE x → x < Om1 → g < x → InE (T x)
  T_mem : ∀ x, InE x → x < Om1 → g < x → T x ∈ Tset x
  T_gt : ∀ x, InE x → x < Om1 → g < x → x < T x
  T_X : ∀ x, InE x → x < Om1 → g < x → T x < ywX x
  E_lt : ∀ i x, InE x → x < Om1 → g < x → gi i < x → (K i).K.E x < T x
  cof : ∀ x, InE x → x < Om1 → g < x → ∀ v < T x, ∃ i, gi i < x ∧ v < (K i).K.E x
  pi : ∀ σ ρ, UpsPt σ → UpsPt ρ → Bases σ ρ → g < σ → T ρ ∈ TB ρ σ ∧ pi σ ρ (T ρ) = T σ

namespace YwUF

variable {g : Ordinal.{0}} (F : YwUF g)

theorem T_lt1 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : g < x) : F.T x < Om1 :=
  (F.T_X x hx hx1 hg).trans (ywX_facts hx hx1).2.2.1

theorem top_i (i : F.I) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hi : F.gi i < x) :
    (F.K i).K.sys.top x = (F.K i).K.E x := by
  have hg' : (F.K i).g < x := (F.g_le i).trans_lt hi
  rw [(F.K i).K.top_eq x hx hx1 hg']
  exact (F.K i).ek x hx hx1 hg'

theorem val_lt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : g < x)
    (p : Σ i : F.I, (F.K i).K.sys.Tm) (h : F.gi p.1 < x ∧ (F.K p.1).K.sys.CB p.2 x) :
    (F.K p.1).K.sys.val p.2 x < F.T x := by
  have h1 := (F.K p.1).K.lt_top_E x hx hx1 ((F.g_le p.1).trans_lt h.1) p.2 h.2
  rw [F.top_i p.1 hx hx1 h.1] at h1
  exact h1.trans (F.E_lt p.1 x hx hx1 hg h.1)

theorem T_lt_ups {x u : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : g < x) (hxu : x < u) (hu : UpsPt u) :
    F.T x < u :=
  gn_lt_ups hx hx1 (F.T_mem x hx hx1 hg) (F.T_lt1 hx hx1 hg) hu hxu

end YwUF

/-- **The union of the family**, top `T(x)`, gated at `g`. -/
noncomputable def ywUSys {g : Ordinal.{0}} (F : YwUF g) : GdSys g where
  Tm := Σ i : F.I, (F.K i).K.sys.Tm
  val := fun p x => (F.K p.1).K.sys.val p.2 x
  CB := fun p x => F.gi p.1 < x ∧ (F.K p.1).K.sys.CB p.2 x
  cs := fun p => F.gi p.1 :: (F.K p.1).K.sys.cs p.2
  cst := fun c => ⟨F.i0, (F.K F.i0).K.sys.cst c⟩
  top := F.T
  cb_cst := fun p s h c hc => by
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · exact (F.K p.1).K.sys.cb_cst p.2 s h.2 c hc
  cb_iff := fun p s s' h h' => ⟨h' _ List.mem_cons_self,
    (F.K p.1).K.sys.cb_iff p.2 s s' h.2 (fun c hc => h' c (List.mem_cons_of_mem _ hc))⟩
  val_cst := fun c x => (F.K F.i0).K.sys.val_cst c x
  cb_cstI := fun c x h => ⟨by rw [F.gi0]; exact lt_of_le_of_lt zero_le h, (F.K F.i0).K.sys.cb_cstI c x h⟩
  lt_top := fun _ hr hr1 hg p h => F.val_lt (ups_inE hr) (ups_lt_Om1 _ hr1) hg p h
  one_le_top := fun _ hr hr1 hg =>
    one_le_iff_pos.2 (lt_of_le_of_lt zero_le (F.T_gt _ (ups_inE hr) (ups_lt_Om1 _ hr1) hg))
  rep := fun r hr hr1 hg v hv => by
    have hx := ups_inE hr
    have hx1 := ups_lt_Om1 r hr1
    obtain ⟨i, hi, hvi⟩ := F.cof _ hx hx1 hg v hv
    have hlt : v < (F.K i).K.sys.top (upsilon r) := by rw [F.top_i i hx hx1 hi]; exact hvi
    obtain ⟨t, ht, et⟩ := (F.K i).K.sys.rep r hr hr1 ((F.g_le i).trans_lt hi) v hlt
    exact ⟨⟨i, t⟩, ⟨hi, ht⟩, et⟩
  top_lt := fun r hr hr1 hg => by
    have hl0 : 0 < r := pos_iff_ne_zero.2 hr.1
    have h1 : r < r + ω := lt_add_of_pos_right r omega0_pos
    have hτU := upsPt_upsilon (hl0.trans h1)
    exact (F.T_lt_ups (ups_inE hr) (ups_lt_Om1 r hr1) hg (upsilon_normal.strictMono h1) hτU).trans
      (upsilon_normal.strictMono (lt_add_one _))
  pkg := fun r hr hr1 _ p h h1 R => (F.K p.1).K.sys.pkg r hr hr1 ((F.g_le p.1).trans_lt h.1) p.2 h.2 h1 R
  rs := fun r hr hr1 _ p h => (F.K p.1).K.sys.rs r hr hr1 ((F.g_le p.1).trans_lt h.1) p.2 h.2
  uni_le := fun σ ρ hσ hρ hB _ p q hp hq =>
    xt_uni_of_exact hB ((F.K p.1).K.exact σ ρ hσ hρ hB ((F.g_le p.1).trans_lt hp.1) p.2 hp.2)
      ((F.K q.1).K.exact σ ρ hσ hρ hB ((F.g_le q.1).trans_lt hq.1) q.2 hq.2)
  small := fun p => ((F.K p.1).K.sys.small p.2).imp id fun h x hx hx1 _ hc =>
    h x hx hx1 ((F.g_le p.1).trans_lt hc.1) hc.2

/-- **The gated union layer**: top `T(x)` (an `ε`-number, so `T(x) = ω^{T(x)}`), the top witness from Lemma IMG. -/
noncomputable def ywLimL {g : Ordinal.{0}} (F : YwUF g) : GdLay g where
  sys := ywUSys F
  E := F.T
  top_eq := fun x hx hx1 hg => (F.T_E x hx hx1 hg).symm
  exp_dvd := fun x hx hx1 hg => opow_dvd_of_inE (F.T_E x hx hx1 hg) (F.T_gt x hx hx1 hg).le
  exp_lt := fun x hx hx1 hg => F.T_lt1 hx hx1 hg
  top_gt := fun x hx hx1 hg => F.T_gt x hx hx1 hg
  top_lt_ups := fun x u hx hx1 hg hxu hu => F.T_lt_ups hx hx1 hg hxu hu
  lt_top_E := fun x hx hx1 hg p h => F.val_lt hx hx1 hg p h
  exact := fun σ ρ hσ hρ hB _ p hp => (F.K p.1).K.exact σ ρ hσ hρ hB ((F.g_le p.1).trans_lt hp.1) p.2 hp.2
  exp_pi := fun σ ρ hσ hρ hB hg => F.pi σ ρ hσ hρ hB hg
  top_wit := fun _ _ _ h hg => by
    have hρE := upsPt_inE h.ρU
    exact ywTopWit h (T := F.T) hg (F.T_E _ hρE h.ρ1 hg) (F.T_gt _ hρE h.ρ1 hg) (F.T_X _ hρE h.ρ1 hg)
      (fun σ hσ hB hgσ => (F.pi σ _ hσ h.ρU hB hgσ).2)

/-- **The gated union base package**: gate `g`, top `T(x)`. -/
noncomputable def ywLimB {g : Ordinal.{0}} (F : YwUF g) : GdB where
  g := g
  K := ywLimL F
  ek := fun x hx hx1 hg => F.T_E x hx hx1 hg
  mem := fun x hx hx1 hg => F.T_mem x hx hx1 hg

theorem ywLimB_E {g : Ordinal.{0}} (F : YwUF g) (x : Ordinal.{0}) : (ywLimB F).K.E x = F.T x := rfl

theorem ywLimB_g {g : Ordinal.{0}} (F : YwUF g) : (ywLimB F).g = g := rfl

/-! ## The instance: the layer of the code `B_Γ` -/

/-- **The tower readings** `s_n(x) = yrR(a_n)(x)`: `s_0 = Γ_{x+1}`, `s_{n+1} = Γ_{x+1+s_n}`. -/
noncomputable def ywS (n : ℕ) (x : Ordinal.{0}) : Ordinal.{0} := yrR (yrTw n) x

theorem ywS_zero (x : Ordinal.{0}) : ywS 0 x = gq 0 x := by
  show yrR (gcG 0) x = gq 0 x
  rw [yrR_atom (gcG_SC 0).1, yrR_zero]

theorem ywS_succ (n : ℕ) (x : Ordinal.{0}) : ywS (n + 1) x = gq (ywS n x) x := by
  show yrR (gcG (yrTw n)) x = gq (yrR (yrTw n) x) x
  exact yrR_atom (yr_idx_BG (yrTw_lt_BG n)) x

section Tw

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **Every tower reading lies below `D = ϑˣ(Ω₁·Ω₁ + Ω₁)`** (and in `Tˣ`). -/
theorem ywS_lt_D : ∀ n : ℕ, ywS n x < ywV 1 0 x ∧ ywS n x ∈ Tset x := by
  obtain ⟨hxD, hDT, hD⟩ := ywD_closed hx hx1
  obtain ⟨h1T, h1Ω⟩ := yw_one hx hx1
  obtain ⟨-, -, hD1, -, -, -, -⟩ := ywV_facts hx hx1 h1T h1Ω (mem_T_of_le hx hx1 zero_le) (hx.pos.trans hx1)
  intro n
  induction n with
  | zero =>
    rw [ywS_zero]
    have h := hD 0 (mem_T_of_le hx hx1 zero_le) (lt_of_le_of_lt zero_le hxD)
    exact ⟨h, vz_T_down hx hx1 hDT hD1 h.le⟩
  | succ n ih =>
    rw [ywS_succ]
    have h := hD _ ih.2 ih.1
    exact ⟨h, vz_T_down hx hx1 hDT hD1 h.le⟩

theorem ywS_lt_succ (n : ℕ) : ywS n x < ywS (n + 1) x := by
  rw [ywS_succ]
  obtain ⟨hlt, hT⟩ := ywS_lt_D hx hx1 n
  exact gmq_gt hx hx1 hT (hlt.trans (ywV_facts hx hx1 (yw_one hx hx1).1 (yw_one hx hx1).2
    (mem_T_of_le hx hx1 zero_le) (hx.pos.trans hx1)).2.2.1)

/-- **The tower readings are cofinal in `D = ϑˣ(Ω₁·Ω₁ + Ω₁)`**: their supremum is closed, so it is `D` (`Yw.ywBG`). -/
theorem ywS_cof : ∀ v, v < ywV 1 0 x → ∃ n : ℕ, v < ywS n x := by
  intro v hv
  by_contra hno
  push Not at hno
  obtain ⟨hxD, hDT, -⟩ := ywD_closed hx hx1
  obtain ⟨h1T, h1Ω⟩ := yw_one hx hx1
  obtain ⟨-, -, hD1, -, -, -, -⟩ := ywV_facts hx hx1 h1T h1Ω (mem_T_of_le hx hx1 zero_le) (hx.pos.trans hx1)
  have hbdd : BddAbove (Set.range fun n : ℕ => ywS n x) := ⟨v, by rintro _ ⟨n, rfl⟩; exact hno n⟩
  set s := ⨆ n : ℕ, ywS n x with hs
  have hsv : s ≤ v := ciSup_le hno
  have hsD : s < ywV 1 0 x := hsv.trans_lt hv
  have hxs : x < s := by
    have h0 : x < ywS 0 x := by rw [ywS_zero]; exact (gfq0_facts hx hx1).2.1
    exact h0.trans_le (le_ciSup hbdd 0)
  have hcl : YwClosed x s := by
    intro σ hσT hσ
    obtain ⟨n, hn⟩ := (lt_ciSup_iff hbdd).1 hσ
    obtain ⟨hnD, hnT⟩ := ywS_lt_D hx hx1 n
    have h1 : gq σ x < gq (ywS n x) x := gmq_lt hx hx1 hnT (hnD.trans hD1) hn
    rw [← ywS_succ] at h1
    exact h1.trans_le (le_ciSup hbdd (n + 1))
  exact absurd ((ywBG hx hx1).2.2 s hxs hcl) (not_le.2 hsD)

end Tw

/-- **The layer of the tower code `a_n`** (`Yr.YrRS.gqL` in the reading system below `a_{n+1}`), gate `0`, top
`ϑˣ(Ω₁·Ω₁ + s_n(x)) = s_{n+1}(x)`. -/
noncomputable def ywTwL (n : ℕ) : GdB :=
  (yrRSN (yrTw (n + 1)) (yrTw_E (n + 1)) ((yrTw_ge n).trans_lt (yrTw_lt_succ n)) (yrTw_lt_BG (n + 1))).gqL
    (yrTw n) (gfE_lt_G0.trans_le (yrTw_ge n)).le (yrTw_lt_succ n)

theorem ywTwL_g (n : ℕ) : (ywTwL n).g = 0 := by
  unfold ywTwL
  rw [YrRS.gqL_g]
  exact yrTw_g n

theorem ywTwL_E (n : ℕ) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : (ywTwL n).K.E x = ywS (n + 1) x := by
  unfold ywTwL
  rw [YrRS.gqL_E _ _ _ hx hx1 (by show yrG (yrTw n) < x; rw [yrTw_g]; exact hx.pos)]
  rw [ywS_succ]
  rfl

/-- **The union data at `B_Γ`**: the layers of the tower, target `ϑˣ(Ω₁·Ω₁ + Ω₁)`, gate `0`. -/
noncomputable def ywBGF : YwUF 0 where
  I := ULift.{1} ℕ
  K := fun n => ywTwL n.down
  gi := fun _ => 0
  i0 := ⟨0⟩
  g_le := fun n => (ywTwL_g n.down).le
  gi0 := rfl
  T := fun x => ywV 1 0 x
  T_E := fun x hx hx1 _ => (ywV_facts hx hx1 (yw_one hx hx1).1 (yw_one hx hx1).2 (mem_T_of_le hx hx1 zero_le)
    (hx.pos.trans hx1)).2.2.2.1
  T_mem := fun x hx hx1 _ => (ywD_closed hx hx1).2.1
  T_gt := fun x hx hx1 _ => (ywD_closed hx hx1).1
  T_X := fun x hx hx1 _ => ywD_lt_X hx hx1
  E_lt := fun n x hx hx1 _ _ => by
    show (ywTwL n.down).K.E x < ywV 1 0 x
    rw [ywTwL_E n.down hx hx1]
    exact (ywS_lt_D hx hx1 (n.down + 1)).1
  cof := fun x hx hx1 _ v hv => by
    obtain ⟨n, hn⟩ := ywS_cof hx hx1 v hv
    refine ⟨⟨n⟩, hx.pos, ?_⟩
    show v < (ywTwL n).K.E x
    rw [ywTwL_E n hx hx1]
    exact hn.trans (ywS_lt_succ hx hx1 n)
  pi := fun σ ρ _ _ hB _ => by
    have h1σ : (1 : Ordinal.{0}) < σ := lu_one_lt_E hB.1
    have h0σ : (0 : Ordinal.{0}) < σ := hB.1.pos
    have h1 := ywV_pi hB (mem_TB_of_lt hB h1σ) ((lu_one_lt_E hB.2.1).trans hB.2.2.2) (mem_TB_of_lt hB h0σ)
      (hB.2.1.pos.trans hB.2.2.2)
    rw [pi_lt hB h1σ, pi_lt hB h0σ] at h1
    exact h1

/-- **THE LAYER OF THE CODE `B_Γ`**: gate `0`, top `ϑˣ(Ω₁·Ω₁ + Ω₁)` (the least fixed point of `ν ↦ Γ_{x+1+ν}`
above `x`, `Yw.ywBG`) at every `ε`-number base `x < Ω₁`. -/
noncomputable def ywBGB : GdB := ywLimB ywBGF

theorem ywBGB_g : ywBGB.g = 0 := rfl

theorem ywBGB_E (x : Ordinal.{0}) : ywBGB.K.E x = ywV 1 0 x := rfl

end Googology.Trans.PoR.InaccPsi.R2.Yw

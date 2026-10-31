import Googology.Trans.PoR.InaccPsi.R2.WsTop

/-!
# WsZeta: THE `ε`-NUMBER BASES OF VEBLEN LEVEL 1 — EVERY `ε_{Ω₁+1+η}` BELOW `ζ_{Ω₁+1}`; THE FRONTIER AT `ζ_{Ω₁+1}`

Below `Z = ζ_{Ω₁+1} = glPsi 2 0 = φ(2, Ω₁+1)` every `ε`-number code is `glPsi 1 η = φ(1, Ω₁+1+η)` (`ws_eps_one`;
the fixed points of `φ(1, ·)` above `Ω₁` start at `Z`, `ws_Z_le`).  Its sequence of levels (`ws_base_one`), from the
sequence of the SMALLER code `η` (the induction hypothesis of `Ws.ws_br`):

* `η = 0`: `ε_{Ω₁+1}` (`Ws.ws_base_E`);
* `η = η' + 1`: the tower over `glPsi 1 η'` (`Ws.ws_base_succ`; `ε_{e+1} = glPsi 1 (η'+1)`, `ws_psi1_succ`);
* `η` a limit: `glPsi 1 η_k` / `glPsi 1 (s μ)` (continuity `ws_psi1_cont`; GATE-COFINALITY: a code `b < glPsi 1 η`
  with `gh b < σ` lies in the bracket of some `glPsi 1 η_b`, `η_b < η`, `gh η_b < σ`, so below `glPsi 1 (s μ)`);
* `Z` itself: the iterates `wsZs k = φ(1, ·)^{k+1}(Ω₁+1)` (`ws_base_Z`).

`ws_baseI_Z` (**`WsBaseI (Z + 1)`, UNCONDITIONAL**), `wsCls_Z` (**THE (A2) CLASSIFICATION UP TO `ζ_{Ω₁+1}`**), the
system `wsVz` at `φ(ζ_{Ω₁+1}, G+1)` (gate `≤ 1`), `wsZ_loc` / `wsZ_enum` / `wsZ_capV` (**THE FRONTIER
`F_Z = ι(Γ(φ(ζ_{Ω₁+1}, G+1))·ω)`**), `wsRoadZ`, `wsRoadZ_hyp_iff` (equivalent to `Ws.wsRoad`'s hypotheses).

No new axiom.  New definitions: `wsZ`, `wsZs`, `wsVz`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ws

open Googology.Trans.PoR.InaccPsi.R2.Wm Googology.Trans.PoR.InaccPsi.R2.Wh Googology.Trans.PoR.InaccPsi.R2.Ho
open Googology.Trans.PoR.InaccPsi.R2.Hn Googology.Trans.PoR.InaccPsi.R2.Hl
open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk
open Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Gf
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt
open Googology.Trans.PoR.InaccPsi.R2.Wo Googology.Trans.PoR.InaccPsi.R2.Wn Googology.Trans.PoR.InaccPsi.R2.Wp WsC
open Googology.Trans.PoR.InaccPsi.R2.Gk

theorem ws_two_lt_Om1 : (2 : Ordinal.{0}) < Om1 := by exact_mod_cast ws_nat_lt_Om1 2

theorem ws_two_lt_G : (2 : Ordinal.{0}) < gcG 0 := ws_two_lt_Om1.trans gl_Om1_lt_G0

/-- `ζ_{Ω₁+1} = glPsi 2 0`. -/
noncomputable def wsZ : Ordinal.{0} := glPsi 2 0

theorem wsZ_eq : wsZ = veblen 2 (Om1 + 1) := by
  unfold wsZ glPsi; rw [glLam_of_not (glFw_zero 2), glY0_lt ws_two_lt_Om1, add_zero]

theorem wsZ_lt_G : wsZ < gcG 0 := glPsi_lt_G ws_two_lt_G gl_G0_E.pos

theorem wsZ_fix : veblen 1 wsZ = wsZ := by
  rw [wsZ_eq]; exact veblen_veblen_of_lt one_lt_two _

theorem ws_lt_two {b : Ordinal.{0}} (hb : b < 2) : b = 0 ∨ b = 1 := by
  rcases lt_or_ge b 1 with h | h
  · exact Or.inl (lt_one_iff_zero.1 h)
  · refine Or.inr (le_antisymm ?_ h)
    exact Order.lt_add_one_iff.1 (by rw [one_add_one_eq_two]; exact hb)

/-- **Every fixed point of `φ(1, ·)` above `Ω₁` is `≥ ζ_{Ω₁+1}`.** -/
theorem ws_Z_le {s : Ordinal.{0}} (hs : veblen 1 s = s) (hOs : Om1 < s) : wsZ ≤ s := by
  have hr1 : s ∈ Set.range (veblen 1) := ⟨s, hs⟩
  have h2 : s ∈ Set.range (veblen 2) := (mem_range_veblen two_ne_zero).2 fun b hb => by
    rcases ws_lt_two hb with rfl | rfl
    · exact (mem_range_veblen one_ne_zero).1 hr1 0 zero_lt_one
    · exact hs
  obtain ⟨z, rfl⟩ := h2
  have hz : Om1 < z := by
    by_contra hz
    push Not at hz
    exact absurd hOs (not_lt.2 (((veblen_le_veblen_iff_right).2 hz).trans (gl_veb_Om1 ws_two_lt_Om1).le))
  rw [wsZ_eq]; exact (veblen_le_veblen_iff_right).2 (Order.add_one_le_of_lt hz)

/-- **Below `ζ_{Ω₁+1}` every `ε`-number code above `Ω₁` is `glPsi 1 η`.** -/
theorem ws_eps_one {e : Ordinal.{0}} (he : InE e) (hOe : Om1 < e) (heZ : e < wsZ) :
    ∃ η, η < e ∧ glPsi 1 η = e := by
  obtain ⟨α, h1, -, η, hη, hpsi⟩ := glPsi_surj he hOe (heZ.trans wsZ_lt_G)
  rcases h1.lt_or_eq with h | h
  · exfalso
    have hfix : veblen 1 e = e := by rw [← hpsi]; unfold glPsi; exact veblen_veblen_of_lt h _
    exact absurd (ws_Z_le hfix hOe) (not_le.2 heZ)
  · subst h; exact ⟨η, hη, hpsi⟩

theorem ws_not_glFw_Z {η : Ordinal.{0}} (hη : η < wsZ) : ¬ glFw 1 η := by
  rintro ⟨f, hf, n, rfl⟩
  obtain ⟨z, hz⟩ := hf.1
  have hfix : veblen 1 f = f := by rw [← hz]; exact veblen_veblen_of_lt (lt_add_one 1) _
  exact absurd ((ws_Z_le hfix hf.2).trans le_self_add) (not_le.2 hη)

theorem ws_psi1 {η : Ordinal.{0}} (hη : η < wsZ) : glPsi 1 η = veblen 1 (Om1 + 1 + η) := by
  unfold glPsi; rw [glLam_of_not (ws_not_glFw_Z hη), glY0_lt wh_one_lt_Om1]

theorem ws_psi1_succ {η : Ordinal.{0}} (hη : η + 1 < wsZ) : eN (glPsi 1 η) = glPsi 1 (η + 1) := by
  rw [ws_psi1 ((lt_add_one η).trans hη), ws_psi1 hη, go_eN_veb, add_assoc]

/-- **Continuity at a limit index.** -/
theorem ws_psi1_cont {η t : Ordinal.{0}} (hl : IsSuccLimit η) (hηZ : η < wsZ) (ht : t < glPsi 1 η) :
    ∃ η', η' < η ∧ t < glPsi 1 η' := by
  rw [ws_psi1 hηZ] at ht
  have hlim : IsSuccLimit (Om1 + 1 + η) := Ordinal.isSuccLimit_add _ hl
  obtain ⟨y, hy, hty⟩ := ((isNormal_veblen 1).lt_iff_exists_lt hlim).1 ht
  have hη0 : (0 : Ordinal.{0}) < η := pos_iff_ne_zero.2 hl.ne_bot
  rcases lt_or_ge y (Om1 + 1) with hy1 | hy1
  · refine ⟨0, hη0, ?_⟩
    rw [ws_psi1 (hη0.trans hηZ), add_zero]; exact hty.trans ((veblen_lt_veblen_iff_right).2 hy1)
  · obtain ⟨u, rfl⟩ := exists_add_of_le hy1
    have hu : u < η := (add_lt_add_iff_left _).1 hy
    exact ⟨u, hu, by rw [ws_psi1 (hu.trans hηZ)]; exact hty⟩

theorem ws_gh_psi1 {η : Ordinal.{0}} (hηG : η < gcG 0) : gh (glPsi 1 η) = max 1 (glQ η) := by
  unfold gh; rw [glG_psi le_rfl gl_one_lt_G0 hηG, glQ_one, max_eq_right zero_le]

theorem ws_glQE_psi1 {η : Ordinal.{0}} (hηG : η < gcG 0) : glQE (glPsi 1 η) = glQ η := by
  unfold glQE
  rw [(glData_eq le_rfl gl_one_lt_G0 hηG).1, (glData_eq le_rfl gl_one_lt_G0 hηG).2, glQ_one, max_eq_right zero_le]

theorem ws_ML_E {e : Ordinal.{0}} (he : InE e) (hOe : Om1 < e) : ML e := ⟨hOe.le, wp_Om1_dvd_E he hOe⟩

/-- **THE BASES OF VEBLEN LEVEL 1**: every `ε`-number code `e ∈ [ε_{Ω₁+1}, ζ_{Ω₁+1})` has a sequence of levels,
given the sequences of the smaller limit codes. -/
theorem ws_base_one {e : Ordinal.{0}} (he : InE e) (hEe : gfE ≤ e) (heZ : e < wsZ)
    (IH : ∀ c, c < e → IsSuccLimit c → BCls (fun _ => True) c) : BCls ML e := by
  have hOe : Om1 < e := Om1_lt_eW.trans_le hEe
  have heG : e < gcG 0 := heZ.trans wsZ_lt_G
  obtain ⟨η, hηe, rfl⟩ := ws_eps_one he hOe heZ
  have hηZ : η < wsZ := hηe.trans heZ
  have hηG : η < gcG 0 := hηZ.trans wsZ_lt_G
  have hgE : ∀ η', gfE ≤ glPsi 1 η' := fun η' => gfE_le_glPsi le_rfl gl_one_lt_G0 η'
  have hML : ∀ η', ML (glPsi 1 η') := fun η' =>
    ws_ML_E (glPsi_E le_rfl η') (glPsi_gt le_rfl gl_one_lt_G0 η').1
  rcases zero_or_succ_or_isSuccLimit η with h0 | ⟨η', hη'⟩ | hl
  · rw [h0, gl_E_eq]; exact ws_base_E
  · rw [← Ordinal.add_one_eq_succ] at hη'
    subst hη'
    have hη'Z : η' < wsZ := (lt_add_one η').trans hηZ
    rw [← ws_psi1_succ hηZ]
    refine ws_base_succ (glPsi_E le_rfl η') (glPsi_gt le_rfl gl_one_lt_G0 η').1
      (by rw [ws_psi1_succ hηZ]; exact heG) ?_
    rw [ws_psi1_succ hηZ, ws_gh_psi1 hηG, ws_glQE_psi1 (hη'Z.trans wsZ_lt_G)]
    exact max_le_max le_rfl (ws_glQ_succ η')
  · rcases IH η hηe hl with ⟨cs, -, h2, h3, h4, h5⟩ | ⟨s, ⟨s1, s2, s3, s4⟩, -⟩
    · refine Or.inl ⟨fun k => glPsi 1 (cs k), fun k => hML _, fun k => glPsi_strictMono 1 (h2 k),
        fun k => glPsi_strictMono 1 (h3 k), fun t ht => ?_, fun k => ?_⟩
      · obtain ⟨η', hη', ht'⟩ := ws_psi1_cont hl hηZ ht
        obtain ⟨k, hk⟩ := h4 η' hη'
        exact ⟨k, ht'.trans (glPsi_strictMono 1 hk)⟩
      · rw [ws_gh_psi1 ((h3 k).trans hηG), ws_gh_psi1 hηG]
        have hQ : glQ (cs k) ≤ max 1 (glQ η) := (ws_glQ_le_gh _).trans ((h5 k).trans (ws_gh_lim hl).le)
        exact max_le (le_max_left _ _) hQ
    · refine Or.inr ⟨fun μ => glPsi 1 (s μ), ⟨fun μ hμ => ⟨(wh_one_lt_Om1.trans (glPsi_gt le_rfl gl_one_lt_G0 _).1).le,
        glPsi_strictMono 1 (s1 μ hμ).2⟩, fun μ' μ h hμ => glPsi_strictMono 1 (s2 μ' μ h hμ),
        fun x hx hx1 hgx μ hμ => ?_, fun σ hσ hσ1 b hb hgb => ?_⟩, fun μ _ => hML _⟩
      · have hgη : gh η < x := by
          rw [ws_gh_lim hl]; change gh (glPsi 1 η) < x at hgx; rwa [ws_gh_psi1 hηG] at hgx
        show gh (glPsi 1 (s μ)) < x
        rw [ws_gh_psi1 ((s1 μ (hμ.trans hx1)).2.trans hηG)]
        exact max_lt (one_lt_inE hx) ((ws_glQ_le_gh _).trans_lt (s3 x hx hx1 hgη μ hμ))
      · rcases lt_or_ge b gfE with hbE | hbE
        · exact ⟨0, hσ.pos, hbE.trans_le (hgE _)⟩
        have hbG : b < gcG 0 := hb.trans heG
        have heb := gl_E_le hbE
        obtain ⟨ηb, -, hpb⟩ := ws_eps_one (guE_E b) (gl_Om1_lt_E hbE) ((heb.trans_lt hb).trans heZ)
        have hηb : ηb < η := glPsi_lt_iff.1 (by rw [hpb]; exact heb.trans_lt hb)
        have hgηb : gh ηb < σ := by
          refine ws_gh_part hσ ?_ hgb
          rw [← ws_glQE_psi1 (hηb.trans hηG), hpb, glG_dec hbE hbG]
          exact le_max_of_le_left (le_max_left _ _)
        obtain ⟨μ, hμ, hlt⟩ := s4 σ hσ hσ1 ηb hηb hgηb
        refine ⟨μ, hμ, (gl_lt_eN hbE).trans_le ?_⟩
        have hb1 : ηb + 1 < wsZ := (Order.add_one_le_of_lt hlt).trans_lt ((s1 μ (hμ.trans hσ1)).2.trans hηZ)
        rw [← hpb, ws_psi1_succ hb1]
        exact glPsi_le_iff.2 (Order.add_one_le_of_lt hlt)

/-! ## `ζ_{Ω₁+1}` itself -/

/-- The iterates `φ(1, ·)^{k+1}(Ω₁+1)`: `ε_{Ω₁+1}, φ(1, ε_{Ω₁+1}), …`, cofinal in `ζ_{Ω₁+1}`. -/
noncomputable def wsZs (k : ℕ) : Ordinal.{0} := (veblen 1)^[k + 1] (Om1 + 1)

theorem wsZs_succ (k : ℕ) : wsZs (k + 1) = veblen 1 (wsZs k) := Function.iterate_succ_apply' _ _ _

theorem wsZs_zero : wsZs 0 = gfE := by rw [wsZs, Function.iterate_one, eW_eq]

theorem wsZs_veb (k : ℕ) : ∃ y, wsZs k = veblen 1 y := ⟨_, Function.iterate_succ_apply' _ _ _⟩

theorem wsZs_E (k : ℕ) : InE (wsZs k) := by
  obtain ⟨y, hy⟩ := wsZs_veb k; rw [hy]; exact luP_E le_rfl (luP_veblen 1 _)

theorem wsZs_Om1 (k : ℕ) : Om1 < wsZs k := by
  induction k with
  | zero => rw [wsZs_zero]; exact Om1_lt_eW
  | succ k ih => rw [wsZs_succ]; exact ih.trans_le (right_le_veblen _ _)

theorem wsZ_E : InE wsZ := glPsi_E one_le_two 0

theorem wsZs_lt_Z : ∀ k : ℕ, wsZs k < wsZ
  | 0 => by
    rw [wsZs_zero, eW_eq, ← wsZ_fix]
    exact (veblen_lt_veblen_iff_right).2
      ((ev_isSuccLimit_of_inE wsZ_E).add_one_lt (glPsi_gt one_le_two ws_two_lt_G 0).1)
  | k + 1 => by rw [wsZs_succ, ← wsZ_fix]; exact (veblen_lt_veblen_iff_right).2 (wsZs_lt_Z k)

theorem wsZs_psi (k : ℕ) : wsZs (k + 1) = glPsi 1 (wsZs k) := by
  rw [wsZs_succ, ws_psi1 (wsZs_lt_Z k), gl_absorb (wsZs_E k) (wsZs_Om1 k)]

theorem wsZs_gate : ∀ k : ℕ, glG (wsZs k) = 0
  | 0 => by rw [wsZs_zero, glG_E]
  | k + 1 => by
    have hG : wsZs k < gcG 0 := (wsZs_lt_Z k).trans wsZ_lt_G
    have hω : ¬ wsZs k < ω := not_lt.2 (omega0_lt_inE (wsZs_E k)).le
    rw [wsZs_psi, glG_psi le_rfl gl_one_lt_G0 hG, glQ_one, show glQ (wsZs k) = glG (wsZs k) from if_neg hω,
      wsZs_gate k, max_self]

theorem wsZ_le_nfp : wsZ ≤ nfp (veblen 1) (Om1 + 1) :=
  ws_Z_le (nfp_fp (isNormal_veblen 1) _) ((lt_add_one Om1).trans_le (le_nfp _ _))

theorem ws_iter_le (n : ℕ) : (veblen 1)^[n] (Om1 + 1) ≤ wsZs n := by
  show _ ≤ (veblen 1)^[n + 1] (Om1 + 1)
  rw [Function.iterate_succ_apply']
  exact right_le_veblen _ _

/-- **THE BASE `ζ_{Ω₁+1}`**: the iterates `wsZs k`, gate `gh = 1`. -/
theorem ws_base_Z : BCls ML wsZ := by
  refine Or.inl ⟨wsZs, fun k => ws_ML_E (wsZs_E k) (wsZs_Om1 k), fun k => ?_, wsZs_lt_Z, fun t ht => ?_,
    fun k => ?_⟩
  · rw [wsZs_succ]
    refine (right_le_veblen _ _).lt_of_ne (fun h => ?_)
    exact absurd (ws_Z_le h.symm (wsZs_Om1 k)) (not_le.2 (wsZs_lt_Z k))
  · obtain ⟨n, hn⟩ := lt_nfp_iff.1 (ht.trans_le wsZ_le_nfp)
    exact ⟨n, hn.trans_le (ws_iter_le n)⟩
  · show max 1 (glG (wsZs k)) ≤ gh wsZ
    rw [wsZs_gate, max_eq_left zero_le]; exact one_le_gh _

/-- **EVERY `ε`-NUMBER CODE IN `[ε_{Ω₁+1}, ζ_{Ω₁+1}]` HAS A SEQUENCE OF LEVELS** (given the smaller codes). -/
theorem ws_baseI_Z : WsBaseI (wsZ + 1) := by
  intro e he hEe hel IH
  rcases (Order.lt_add_one_iff.1 hel).lt_or_eq with h | rfl
  · exact ws_base_one he hEe h IH
  · exact ws_base_Z

/-- **THE (A2) CLASSIFICATION UP TO `ζ_{Ω₁+1}`** (UNCONDITIONAL). -/
theorem wsCls_Z : WsCls wsA2 (wsZ + 1) := wsCls_of_baseI (Order.add_one_le_of_lt wsZ_lt_G) ws_baseI_Z

/-! ## The system at `φ(ζ_{Ω₁+1}, G+1)` and the frontier -/

theorem wsZ_Om1 : Om1 < wsZ := (glPsi_gt one_le_two ws_two_lt_G 0).1

theorem wsZ_lev : wsA2.Lev wsZ := ⟨wsZ_Om1.le, wp_Om1_dvd_E wsZ_E wsZ_Om1, wsZ_lt_G⟩

theorem wsZ_gh : gh wsZ = 1 := by
  unfold gh wsZ; rw [glG_psi one_le_two ws_two_lt_G gl_G0_E.pos, glQ_zero,
    show glQ (2 : Ordinal.{0}) = 0 from by exact_mod_cast glQ_nat 2, max_self, max_eq_left zero_le]

/-- **THE SYSTEM OVER `G` AT THE LEVEL `ζ_{Ω₁+1}`.** -/
noncomputable def wsVz : HgVD := wsV wsCls_Z wsZ

theorem wsVz_B : wsVz.B = veblen wsZ (gcG 0 + 1) := wsV_B wsA2_G wsCls_Z wsZ_lev (lt_add_one _)

theorem wsVz_γ : wsVz.γ ≤ 1 := by
  have := wsV_γ wsA2_G wsCls_Z wsZ_lev (lt_add_one _)
  change wsVz.γ ≤ gh wsZ at this
  rwa [wsZ_gh] at this

theorem wsLw_lt_Z : wsLw < wsZ := by
  rw [wsLw, ← wsZ_fix]
  refine (veblen_lt_veblen_iff_right).2 ?_
  exact (inE_indec wsZ_E).add_lt wsZ_Om1 (omega0_lt_inE wsZ_E)

section Fr

variable (S : InaccSeq.{0})

theorem wsVz_γK : wsVz.γ < Td.tdK S :=
  wsVz_γ.trans_lt (((one_lt_omega0.trans (omega0_lt_epsilon 0)).trans gq_eps0_lt_gam).trans_le
    (Td.tdGam_le_K (S := S)))

/-- **`φ(ζ_{Ω₁+1}, G+1)` IS LOCATED** (UNCONDITIONAL). -/
theorem wsZ_loc : ∃ X : Xt.XtSys, Xt.XtTopPkg X ∧ Xt.xtB1 X = iota S (gcG wsVz.B * ω) ∧
    upsilon (Xt.xtB1 X) = Nm.Pv S (gcG wsVz.B * ω) ∧ Nm.Pv S (gcG wsVz.B * ω) < Nc.ncL S 0 :=
  hgV_locD wsVz S (wsVz_γK S)

/-- **ENUM-REACH at every range restart below `ι(Γ(φ(ζ_{Ω₁+1}, G+1))·ω)`** (UNCONDITIONAL). -/
theorem wsZ_enum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG wsVz.B * ω)) :
    CdUpper S l ∧ CdLower S l := hgV_locD_enum wsVz S (wsVz_γK S) hr hl

/-- **CapV at every range restart below `ι(Γ(φ(ζ_{Ω₁+1}, G+1))·ω)`** (UNCONDITIONAL). -/
theorem wsZ_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG wsVz.B * ω)) : CdCapV S l :=
  hgV_locD_capV wsVz S (wsVz_γK S) hr hl

/-- **The frontiers in order**: `F_W ≤ F_Z = ι(Γ(φ(ζ_{Ω₁+1}, G+1))·ω)`. -/
theorem wsZ_fr_order : iota S (gcG wsVw.B * ω) ≤ iota S (gcG wsVz.B * ω) := by
  have h : wsVw.B ≤ wsVz.B := by rw [wsVw_B, wsVz_B]; exact (hd_veb_left_lt wsLw_lt_Z _).le
  exact iota_mono _ _ (mul_le_mul_right' (gcG_le h) ω)

/-- **THE ROAD WITH UPPER / LOWER / CapV ASKED ONLY ABOVE `ι(Γ(φ(ζ_{Ω₁+1}, G+1))·ω)`.** -/
theorem wsRoadZ
    (hUH : ∀ l, CdRange S l → iota S (gcG wsVz.B * ω) ≤ l → CdUpper S l)
    (hLH : ∀ l, CdRange S l → iota S (gcG wsVz.B * ω) ≤ l → CdLower S l)
    (hVH : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG wsVz.B * ω) ≤ l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → iota S (gcG wsVz.B * ω) ≤ l → CdCapV S l)
    (hT : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S)
    (hF : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdEQfar S)
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      Wf.WfVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      Wf.WfVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S (k + 1)) (Nc.ncL S (ω + 1)) := by
  refine wsRoad S (fun l hr _ => ?_) (fun l hr _ => ?_) (fun l hr hu _ => ?_) (fun l hr hu _ => ?_) hT hF h0 hn
  · rcases lt_or_ge l (iota S (gcG wsVz.B * ω)) with h | h
    · exact (wsZ_enum S hr h).1
    · exact hUH l hr h
  · rcases lt_or_ge l (iota S (gcG wsVz.B * ω)) with h | h
    · exact (wsZ_enum S hr h).2
    · exact hLH l hr h
  · rcases lt_or_ge l (iota S (gcG wsVz.B * ω)) with h | h
    · exact wsZ_capV S hr h
    · exact hVH l hr hu h
  · rcases lt_or_ge l (iota S (gcG wsVz.B * ω)) with h | h
    · exact wsZ_capV S hr h
    · exact hVt l hr hu h

/-- **NON-VACUITY (relative)**: the four hypotheses of `wsRoadZ` are EQUIVALENT to those of `Ws.wsRoad`. -/
theorem wsRoadZ_hyp_iff :
    ((∀ l, CdRange S l → iota S (gcG wsVw.B * ω) ≤ l → CdUpper S l) ↔
      (∀ l, CdRange S l → iota S (gcG wsVz.B * ω) ≤ l → CdUpper S l)) ∧
    ((∀ l, CdRange S l → iota S (gcG wsVw.B * ω) ≤ l → CdLower S l) ↔
      (∀ l, CdRange S l → iota S (gcG wsVz.B * ω) ≤ l → CdLower S l)) ∧
    ((∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG wsVw.B * ω) ≤ l → CdCapV S l) ↔
      (∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG wsVz.B * ω) ≤ l → CdCapV S l)) ∧
    ((∀ l, CdRange S l → Nc.ncL S ω < upsilon l → iota S (gcG wsVw.B * ω) ≤ l → CdCapV S l) ↔
      (∀ l, CdRange S l → Nc.ncL S ω < upsilon l → iota S (gcG wsVz.B * ω) ≤ l → CdCapV S l)) := by
  have hle := wsZ_fr_order S
  refine ⟨⟨fun h l hr hl => h l hr (hle.trans hl), fun h l hr hl => ?_⟩,
    ⟨fun h l hr hl => h l hr (hle.trans hl), fun h l hr hl => ?_⟩,
    ⟨fun h l hr hu hl => h l hr hu (hle.trans hl), fun h l hr hu hl => ?_⟩,
    ⟨fun h l hr hu hl => h l hr hu (hle.trans hl), fun h l hr hu hl => ?_⟩⟩
  · rcases lt_or_ge l (iota S (gcG wsVz.B * ω)) with h' | h'
    · exact (wsZ_enum S hr h').1
    · exact h l hr h'
  · rcases lt_or_ge l (iota S (gcG wsVz.B * ω)) with h' | h'
    · exact (wsZ_enum S hr h').2
    · exact h l hr h'
  · rcases lt_or_ge l (iota S (gcG wsVz.B * ω)) with h' | h'
    · exact wsZ_capV S hr h'
    · exact h l hr hu h'
  · rcases lt_or_ge l (iota S (gcG wsVz.B * ω)) with h' | h'
    · exact wsZ_capV S hr h'
    · exact h l hr hu h'

end Fr

/-- **REGION (A2) BELOW `φ(ζ_{Ω₁+1}, G+1)`, UNCONDITIONAL**: every (A2) level `ℓ ≤ ζ_{Ω₁+1}` has a system over
`G` with `B = φ(ℓ, G+1)` and gate `≤ gh ℓ`. -/
theorem wsSysZ : ∀ ℓ, WpLev ℓ → ℓ ≤ wsZ → ∃ V : HgVD, V.B = veblen ℓ (gcG 0 + 1) ∧ V.γ ≤ gh ℓ :=
  fun ℓ hℓ hle => wsSysAll wsA2_G wsCls_Z ℓ hℓ (Order.lt_add_one_iff.2 hle)

/-- **REGION (A2) FROM THE BASES ABOVE `ζ_{Ω₁+1}`**: the bases below `ζ_{Ω₁+1}` are proved, so `WsBaseI G` reduces
to the `ε`-number codes `e ∈ (ζ_{Ω₁+1}, G)` (Veblen level `≥ 2`). -/
theorem wsBaseI_of_hi (h : ∀ e, InE e → wsZ < e → e < gcG 0 →
    (∀ c, c < e → IsSuccLimit c → BCls (fun _ => True) c) → BCls ML e) : WsBaseI (gcG 0) := by
  intro e he hEe heG IH
  rcases le_or_gt e wsZ with h' | h'
  · exact ws_baseI_Z e he hEe (Order.lt_add_one_iff.2 h') IH
  · exact h e he h' heG IH

/-- **REGION (A2) FROM `WsBaseI G`**: every `B < φ(G, 1)` is `≤` the bound of a system over `G` with gate `< K`. -/
theorem wsSysA2_baseI (S : InaccSeq.{0}) (hb : WsBaseI (gcG 0)) :
    ∀ B, B < veblen (gcG 0) 1 → ∃ V : HgVD, B ≤ V.B ∧ V.γ < Td.tdK S :=
  wsA2_sysA2 (wsCls_of_baseI le_rfl hb) S

/-- **The systems at the cofinal levels `glBn n`** from `WsBaseI G`. -/
theorem wsSysA2Lev_baseI (S : InaccSeq.{0}) (hb : WsBaseI (gcG 0)) (n : ℕ) :
    ∃ V : HgVD, V.B = veblen (glBn n) (gcG 0 + 1) ∧ V.γ < Td.tdK S := by
  obtain ⟨V, hVB, hγ⟩ := wsA2_sysAll (wsCls_of_baseI le_rfl hb) _ (wpLev_Bn n)
  exact ⟨V, hVB, (hγ.trans_lt (gh_lt_SC (Lq.lq_gamma_SC 0) (wnGateBn n))).trans_le (Td.tdGam_le_K (S := S))⟩

end Googology.Trans.PoR.InaccPsi.R2.Ws

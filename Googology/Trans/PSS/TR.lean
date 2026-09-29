import Googology.Trans.PSS.TR.Cof

/-!
# Lemma TR: `val ∘ 𝒯 = o`

`proof/TR.md` and `proof/TR-2.md` prove that the translation `𝒯` of
`proof/PROOF-2.md` §12.1 (`por/tr.py`) from standard pair sequences into
Wilken's `T¹` is exact: the value of `𝒯(M)` is the ordinal `o(M)` of `M`.

## Contents

* `TR/Term.lean`: the terms of `T¹` (`WP`: `ϑ_m(ξ)` with `ξ` a list of
  summands) and the operations of `tr.py`: the visible subterms `starS`, the
  comparison `cmpP` (with fuel), the sum with absorption `addS`/`addAll`,
  `omegaExp`, `logOmega`.
* `TR/Defs.lean`: **the translation** `trTm` (`𝒯_{y(s)}(s)`) and `trNode`
  (the sum over the roots), with checks against `tr.py` by `decide`, e.g.
  `(0,0)(1,1)(2,2) ↦ ϑ_0(ϑ_1(Ω_2))`.
* `TR/Cited.lean`: **the cited facts on Wilken's `ϑ` as axioms** — (L), (C),
  (E), (Exp), (Seg), (Min) of `proof/TR.md` §1.  They are the only axioms.
* `TR/Basic.lean`, `TR/Ops.lean`: the syntactic comparison is the comparison
  of values (`cmpP_eq`), terms of `T¹` with equal values are equal
  (`eq_of_val_eq`), `addS`/`addAll` are the ordinal sum, `ω^x` and `log_ω`
  are right (`omegaExp_spec`, `logOmega_spec`), and every image of `𝒯` is a
  term of `T¹` of the right level (`trTm_nf`).
* `TR/Cof.lean`: **Theorem Cof**, `val 𝒯(t) = sup_n val 𝒯(t[n])`.
* This file: **Lemma TR** (`tr`), by induction on `o`: a sum is the sum of
  its roots, and a root with children is the limit of its fundamental
  sequence on both sides (Theorem Cof, and COMB Lemma 5 (b) `ordOf_eq_iSup`).
-/

namespace Googology.Trans.PSS.TR

open Forest Phi Ordinal Order
open Bijectivity (CTPS ltPS lePS)
open Googology.Notation.ExBuchholz

/-! ## Sums -/

theorem valS_trNode (S : List Tm) : WP.valS (trNode S) = (S.map (fun t => (trTm t).val)).sum := by
  rw [trNode, (addAll_spec (fun x hx => by
    rw [List.mem_map] at hx
    obtain ⟨t, -, rfl⟩ := hx
    exact NFS.single (trTm_nf t).1)).2, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  simp

/-- A node is the sum of its roots, on both sides. -/
theorem valS_trNode_eq_of_roots : ∀ {S : List Tm}, StdOrd S →
    (∀ t ∈ S, (trTm t).val = ordOf [t]) → WP.valS (trNode S) = ordOf S
  | [], _, _ => by rw [valS_trNode, ordOf_nil]; rfl
  | t :: S, hS, h => by
    have hS' : StdOrd S := stdOrd_of_append_right (A := [t]) hS
    have ih := valS_trNode_eq_of_roots hS' (fun r hr => h r (by simp [hr]))
    rw [valS_trNode] at ih ⊢
    rw [List.map_cons, List.sum_cons, ih, ordOf_cons hS, h t (by simp)]

/-! ## `o` at a limit root -/

theorem cols_leaf : (Tm.node 0 []).cols = [(0, 0)] := by decide

theorem ordOf_leaf : ordOf [Tm.node 0 []] = 1 := by
  rw [ordOf_single, cols_leaf, pairOrdL_of_ne (by simp), pairTerm_single,
    Googology.Notation.ExBuchholz.Term.val_nil, add_zero]

theorem trTm_leaf : trTm (Tm.node 0 []) = one := by decide

/-- For a standard root with children, `o` is a limit ordinal. -/
theorem isSuccLimit_ordOf {t : Tm} (ht : Std t) (hne : t.cs ≠ []) : IsSuccLimit (ordOf [t]) := by
  rw [ordOf_single, lemmaR ht]
  refine isSuccLimit_opow_left isSuccLimit_omega0 (fun h0 => ?_)
  have h1 : pairOrdL t.cols = 1 := by rw [lemmaR ht, h0, opow_zero]
  rw [← ordOf_single, ← ordOf_leaf] at h1
  have hl : Std (Tm.node 0 []) := by
    show CTPS (Tm.node 0 []).cols
    rw [cols_leaf]; exact (ctps_iff_SC _).mpr (by decide)
  have := mat_inj (show mat [t] = mat [Tm.node 0 []] by
    have e := (ordOf_le_iff (stdOrd_single ht) (stdOrd_single hl)).mpr h1.le
    have e' := (ordOf_le_iff (stdOrd_single hl) (stdOrd_single ht)).mpr h1.ge
    rcases e with e | e
    · rw [e]
    · rcases e' with e' | e'
      · rw [e']
      · exact absurd (lt_trans e e') (lt_irrefl _))
  cases this
  exact hne rfl

/-- **COMB Lemma 5 (b)** for a root: `o(t) = sup_n o(t[n+1])`. -/
theorem ordOf_eq_iSup {t : Tm} (ht : Std t) (hne : t.cs ≠ []) :
    ordOf [t] = ⨆ n : ℕ, pairOrdL (_root_.PSS.oper t.cols (n + 1)) := by
  have hL : 1 < _root_.PSS.Lng t.cols := by
    obtain ⟨c, cs, hc⟩ := List.exists_cons_of_ne_nil hne
    obtain ⟨y, cs'⟩ := t
    simp only [Tm.cs_node] at hc
    subst hc
    rw [_root_.PSS.Lng, Tm.cols_eq, mat_cons]
    obtain ⟨r, hr⟩ := c.cols_head
    simp [hr, shUp]
  have hlt : ∀ n : ℕ, pairOrdL (_root_.PSS.oper t.cols (n + 1)) < ordOf [t] := by
    intro n
    rw [ordOf_single]
    exact (ltPS_iff_pairOrdL_lt (isPair_of_ctps (Bijectivity.ctps_oper ht (by omega)))
      (isPair_of_ctps ht)).mp (Bijectivity.oper_ltPS hL (n + 1) (by omega))
  refine le_antisymm ?_ (Ordinal.iSup_le fun n => (hlt n).le)
  refine le_of_forall_lt fun β hβ => ?_
  have hsβ : succ β < ordOf [t] := (isSuccLimit_ordOf ht hne).succ_lt hβ
  obtain ⟨S', hS', hS'v⟩ := exists_ordOf_eq (stdOrd_single ht) hsβ
  have hS'lt : S' < [t] := (ordOf_lt_iff hS' (stdOrd_single ht)).mpr (hS'v ▸ hsβ)
  have hS'ne : S' ≠ [] := by
    rintro rfl
    rw [ordOf_nil] at hS'v
    exact absurd hS'v.symm (lt_of_le_of_lt (bot_le (a := β)) (Order.lt_succ β)).ne'
  have hC : CTPS (mat S') := hS'.resolve_left hS'ne
  have hmt : mat [t] = t.cols := by rw [mat_cons, mat_nil, List.append_nil]
  have hlt' : ltPS (mat S') t.cols := hmt ▸ (mat_lt_iff S' [t]).mpr hS'lt
  obtain ⟨n, hn, hle⟩ := exists_le_oper hC ht hlt'
  have hle' : succ β ≤ pairOrdL (_root_.PSS.oper t.cols n) := by
    rw [← hS'v, ordOf]
    rcases hle with h | h
    · rw [h]
    · exact ((ltPS_iff_pairOrdL_lt (isPair_of_ctps hC)
        (isPair_of_ctps (Bijectivity.ctps_oper ht hn))).mp h).le
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact lt_of_lt_of_le (lt_succ β) (le_trans hle' (Ordinal.le_iSup _ m))

/-! ## Lemma TR -/

/-- **Lemma TR from Theorem Cof.** -/
theorem tr_of_cof
    (hcof : ∀ t : Tm, Std t → t.cs ≠ [] → (trTm t).val =
      ⨆ n : ℕ, WP.valS (trNode (nodeOf (_root_.PSS.oper t.cols (n + 1))))) :
    ∀ S : List Tm, StdOrd S → WP.valS (trNode S) = ordOf S := by
  suffices H : ∀ β : Ordinal.{0}, ∀ S : List Tm, StdOrd S → ordOf S = β →
      WP.valS (trNode S) = ordOf S from fun S hS => H _ S hS rfl
  intro β
  induction β using WellFoundedLT.induction with
  | _ β IH =>
    intro S hS hSβ
    -- a root
    have hroot : ∀ t : Tm, Std t → ordOf [t] ≤ β → (trTm t).val = ordOf [t] := by
      intro t ht htβ
      rcases eq_or_ne t.cs [] with hc | hne
      · have ht0 : t = Tm.node 0 [] := by rw [std_node_y ht, hc]
        subst ht0
        rw [trTm_leaf, val_one, ordOf_leaf]
      · rw [hcof t ht hne, ordOf_eq_iSup ht hne]
        congr 1
        funext n
        have hC : CTPS (_root_.PSS.oper t.cols (n + 1)) := Bijectivity.ctps_oper ht (by omega)
        obtain ⟨hSn, hSnm⟩ := nodeOf_spec hC
        have hL : 1 < _root_.PSS.Lng t.cols := by
          obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil hne
          obtain ⟨y, cs'⟩ := t
          simp only [Tm.cs_node] at hcs
          subst hcs
          rw [_root_.PSS.Lng, Tm.cols_eq, mat_cons]
          obtain ⟨r, hr⟩ := c.cols_head
          simp [hr, shUp]
        have hlt : ordOf (nodeOf (_root_.PSS.oper t.cols (n + 1))) < β := by
          refine lt_of_lt_of_le ?_ htβ
          rw [ordOf, hSnm, ordOf_single]
          exact (ltPS_iff_pairOrdL_lt (isPair_of_ctps hC) (isPair_of_ctps ht)).mp
            (Bijectivity.oper_ltPS hL (n + 1) (by omega))
        rw [IH _ hlt _ hSn rfl, ordOf, hSnm]
    rcases S with _ | ⟨t, S'⟩
    · rw [valS_trNode, ordOf_nil]; rfl
    · have hd := (stdOrd_iff _).mp hS
      rcases S' with _ | ⟨t', S''⟩
      · exact valS_trNode_eq_of_roots hS (fun r hr => by
          rw [List.mem_singleton.mp hr]
          exact hroot t (hd.2 t (by simp)) (hSβ ▸ le_rfl))
      · -- several roots: each root is below the node
        have hpos : 0 < ordOf (t' :: S'') := by
          have := (ordOf_lt_iff stdOrd_nil (stdOrd_of_append_right (A := [t]) hS)).mp
            (by simp)
          rwa [ordOf_nil] at this
        have htlt : ordOf [t] < β := by
          rw [← hSβ, ordOf_cons hS]
          exact lt_add_of_pos_right _ hpos
        refine valS_trNode_eq_of_roots hS (fun r hr => ?_)
        have hr' : Std r := hd.2 r hr
        have hrt : ordOf [r] ≤ ordOf [t] := by
          refine (ordOf_le_iff (stdOrd_single hr') (stdOrd_single (hd.2 t (by simp)))).mp ?_
          rcases List.mem_cons.mp hr with rfl | hr
          · exact Or.inl rfl
          · have hle : r ≤ t := by
              have := hd.1
              rw [Desc, List.pairwise_cons] at this
              exact this.1 r hr
            rcases hle.lt_or_eq with h | h
            · exact Or.inr (single_lt_single h)
            · exact Or.inl (by rw [h])
        exact hroot r hr' (le_trans hrt htlt.le) |>.trans rfl

/-- **Lemma TR** (`proof/TR-2.md` §4b): for every node `S` (a standard pair
sequence, as its list of root terms), `val 𝒯(S) = o(S)`. -/
theorem tr : ∀ S : List Tm, StdOrd S → WP.valS (trNode S) = ordOf S :=
  tr_of_cof (fun _ ht hne => cof ht hne)

/-- **Lemma TR on matrices**: for a standard pair sequence `M`,
`val 𝒯(M) = o(M) = 1 + val (pairTerm M)`. -/
theorem tr_mat {M : PS} (hM : CTPS M) : WP.valS (trNode (nodeOf M)) = pairOrdL M := by
  obtain ⟨hS, hSm⟩ := nodeOf_spec hM
  rw [tr _ hS, ordOf, hSm]

end Googology.Trans.PSS.TR

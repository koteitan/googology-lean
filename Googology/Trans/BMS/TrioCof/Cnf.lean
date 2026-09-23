/-
Ported verbatim from koteitan/trio, `lean/Cnf.lean`:
https://github.com/koteitan/trio/blob/74ef7af49eefaef06ce4c9b57c02ecdcb9975606/lean/Cnf.lean
Only the module names of the imports and the namespace (`TRIO` →
`Googology.Trans.BMS.TrioCof`) were changed. The bridge to this library's
Bashicu matrices is `Googology/Trans/BMS/TrioCofinal.lean`.
-/
/-
**Cantor 標準形条件**（トリオ数列）。

述語 `cnf`: 主要項の和が lead 対（添字対）で広義単調減少していること。
対角列の cnf、末尾除去・前部分列への閉包、同一ブロックの反復の cnf。

2 行の Cnf.lean と同じ骨格。比較 `P a b Z <o P e f Z` が
`P a1 a2 b Z <o P e1 e2 f Z` の対比較になる。
-/
import Googology.Trans.BMS.TrioCof.Decrease
import Googology.Trans.BMS.TrioCof.Seqlex

namespace Googology.Trans.BMS.TrioCof

open Three
open Classical

/-! ## 対角列の構造 -/

theorem fst_in_diagSeqT {q : ℕ × ℕ × ℕ} {a b : ℕ} (h : q ∈ diagSeqT a b) :
    a ≤ q.1 := by
  unfold diagSeqT at h
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 h
  obtain ⟨i, _, rfl⟩ := List.mem_range'.1 hj
  simp

theorem translate_diagSeqT {u v : ℕ} (h : u ≤ v) :
    translate (diagSeqT u v)
      = P u (min u 1) (translate (diagSeqT (u + 1) v)) Z := by
  rw [diagSeqT_cons h]
  exact translate_single_tree fun q hq => by
    have := fst_in_diagSeqT hq
    simp only []
    omega

/-! ## The Cantor normal form condition -/

/-- `cnf`: the sum of principal terms is weakly decreasing in the lead pair
(the trailing sums cut to `Z` for the comparison), recursively at every
position. -/
def cnf : Three → Prop
  | Z => True
  | P _ _ b Z => cnf b
  | P a1 a2 b (P e1 e2 f g) =>
      cnf b ∧ ¬ (P a1 a2 b Z <o P e1 e2 f Z) ∧ cnf (P e1 e2 f g)

@[simp] theorem cnf_Z : cnf Z := trivial

@[simp] theorem cnf_P_Z {a1 a2 : ℕ} {b : Three} : cnf (P a1 a2 b Z) ↔ cnf b :=
  Iff.rfl

@[simp] theorem cnf_P_P {a1 a2 e1 e2 : ℕ} {b f g : Three} :
    cnf (P a1 a2 b (P e1 e2 f g)) ↔
      cnf b ∧ ¬ (P a1 a2 b Z <o P e1 e2 f Z) ∧ cnf (P e1 e2 f g) := Iff.rfl

theorem cnf_translate_diagSeqT_aux (n u : ℕ) :
    cnf (translate (diagSeqT u (u + n))) := by
  induction n generalizing u with
  | zero =>
    rw [translate_diagSeqT (by omega)]
    have e : diagSeqT (u + 1) (u + 0) = [] := by
      unfold diagSeqT
      rw [show u + 0 + 1 - (u + 1) = 0 by omega]
      rfl
    rw [e]
    show cnf (P u (min u 1) (translate []) Z)
    rw [cnf_P_Z]
    show cnf (translate [])
    simp [translate]
  | succ n ih =>
    rw [translate_diagSeqT (by omega)]
    rw [cnf_P_Z]
    have := ih (u + 1)
    rwa [show u + 1 + n = u + (n + 1) by omega] at this

theorem cnf_diag (v : ℕ) : cnf (translate (diagSeqT 0 v)) := by
  have := cnf_translate_diagSeqT_aux v 0
  rwa [Nat.zero_add] at this

/-! ## Appending can only grow a leading block -/

/-- Appending a column can only *increase* (weakly) the translation of a
leading same-level block. -/
theorem translate_takeWhile_snoc_le (a : ℕ) (C : TrioSeq) (m : ℕ × ℕ × ℕ) :
    translate (C.takeWhile fun x => a < x.1)
      ≤o translate ((C ++ [m]).takeWhile fun x => a < x.1) := by
  by_cases hall : ∀ x ∈ C, a < x.1
  · have hall' : ∀ x ∈ C, (fun q : ℕ × ℕ × ℕ => decide (a < q.1)) x = true := by
      intro x hx; simpa using hall x hx
    have twC : C.takeWhile (fun x => a < x.1) = C := List.takeWhile_eq_self_iff.2 hall'
    by_cases hm : a < m.1
    · have e : (C ++ [m]).takeWhile (fun x => a < x.1) = C ++ [m] := by
        apply List.takeWhile_eq_self_iff.2
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact hall' x hx
        · simp at hx
          simpa [hx] using hm
      rw [twC, e]
      exact Or.inl (translate_snoc_increase _ _)
    · have e : (C ++ [m]).takeWhile (fun x => a < x.1) = C := by
        rw [takeWhile_append_all hall']
        simp [hm]
      rw [twC, e]
      exact Or.inr rfl
  · push Not at hall
    obtain ⟨x, hx, hnx⟩ := hall
    have hnx' : ¬ (fun q : ℕ × ℕ × ℕ => decide (a < q.1)) x = true := by
      simpa using hnx
    rw [takeWhile_append_not hx hnx']
    exact Or.inr rfl

/-! ## Closure under dropping the last column and taking prefixes -/

/-- `cnf` is preserved by dropping the last column. -/
theorem cnf_snoc {D : TrioSeq} {m : ℕ × ℕ × ℕ}
    (h : cnf (translate (D ++ [m]))) : cnf (translate D) := by
  induction D using translate.induct with
  | case1 => simp [translate]
  | case2 p rest ih1 ih2 =>
    by_cases allp : ∀ x ∈ rest, p.1 < x.1
    · have allp' : ∀ x ∈ rest, (fun q : ℕ × ℕ × ℕ => decide (p.1 < q.1)) x = true := by
        intro x hx; simpa using allp x hx
      have tw : rest.takeWhile (fun q => p.1 < q.1) = rest :=
        List.takeWhile_eq_self_iff.2 allp'
      have dw : rest.dropWhile (fun q => p.1 < q.1) = [] :=
        List.dropWhile_eq_nil_iff.2 allp'
      have eq0 : translate (p :: rest) = P p.2.1 p.2.2 (translate rest) Z := by
        rw [translate, tw, dw, translate]
      by_cases hm : p.1 < m.1
      · have all' : ∀ x ∈ rest ++ [m],
            (fun q : ℕ × ℕ × ℕ => decide (p.1 < q.1)) x = true := by
          intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · exact allp' x hx
          · simp at hx
            simpa [hx] using hm
        have tw' : (rest ++ [m]).takeWhile (fun q => p.1 < q.1) = rest ++ [m] :=
          List.takeWhile_eq_self_iff.2 all'
        have dw' : (rest ++ [m]).dropWhile (fun q => p.1 < q.1) = [] :=
          List.dropWhile_eq_nil_iff.2 all'
        have hsnoc : cnf (translate (rest ++ [m])) := by
          have e : translate ((p :: rest) ++ [m])
              = P p.2.1 p.2.2 (translate (rest ++ [m])) Z := by
            rw [List.cons_append, translate, tw', dw', translate]
          rw [e] at h
          exact (cnf_P_Z).1 h
        have : cnf (translate rest) := by
          have := ih1 (by rw [tw]; exact hsnoc)
          rwa [tw] at this
        rw [eq0]
        exact (cnf_P_Z).2 this
      · have tw' : (rest ++ [m]).takeWhile (fun q => p.1 < q.1) = rest := by
          rw [takeWhile_append_all allp']
          simp [hm]
        have dw' : (rest ++ [m]).dropWhile (fun q => p.1 < q.1) = [m] := by
          rw [dropWhile_append_all allp']
          simp [hm]
        have e : translate ((p :: rest) ++ [m])
            = P p.2.1 p.2.2 (translate rest) (translate [m]) := by
          rw [List.cons_append, translate, tw', dw']
        have e2 : translate ([m] : TrioSeq) = P m.2.1 m.2.2 Z Z := by
          rw [translate]
          simp [translate]
        rw [e, e2] at h
        rw [eq0]
        exact (cnf_P_Z).2 h.1
    · push Not at allp
      obtain ⟨x, hx, hnx⟩ := allp
      have hnx' : ¬ (fun q : ℕ × ℕ × ℕ => decide (p.1 < q.1)) x = true := by
        simpa using hnx
      have tw' : (rest ++ [m]).takeWhile (fun q => p.1 < q.1)
          = rest.takeWhile (fun q => p.1 < q.1) := takeWhile_append_not hx hnx'
      have dw' : (rest ++ [m]).dropWhile (fun q => p.1 < q.1)
          = rest.dropWhile (fun q => p.1 < q.1) ++ [m] := dropWhile_append_not hx hnx'
      have dwne : rest.dropWhile (fun q => p.1 < q.1) ≠ [] := by
        intro he
        exact hnx' (List.dropWhile_eq_nil_iff.1 he x hx)
      obtain ⟨q, rest2, dwq⟩ : ∃ q rest2,
          rest.dropWhile (fun q => p.1 < q.1) = q :: rest2 := by
        rcases hdw : rest.dropWhile (fun q => p.1 < q.1) with - | ⟨q, rest2⟩
        · exact absurd hdw dwne
        · exact ⟨q, rest2, hdw⟩
      have td : translate (rest.dropWhile fun q => p.1 < q.1)
          = P q.2.1 q.2.2 (translate (rest2.takeWhile fun y => q.1 < y.1))
              (translate (rest2.dropWhile fun y => q.1 < y.1)) := by
        rw [dwq, translate]
      have td' : translate ((rest.dropWhile fun q => p.1 < q.1) ++ [m])
          = P q.2.1 q.2.2 (translate ((rest2 ++ [m]).takeWhile fun y => q.1 < y.1))
              (translate ((rest2 ++ [m]).dropWhile fun y => q.1 < y.1)) := by
        rw [dwq, List.cons_append, translate]
      have fle : translate (rest2.takeWhile fun y => q.1 < y.1)
          ≤o translate ((rest2 ++ [m]).takeWhile fun y => q.1 < y.1) :=
        translate_takeWhile_snoc_le q.1 rest2 m
      have e : translate ((p :: rest) ++ [m])
          = P p.2.1 p.2.2 (translate (rest.takeWhile fun q => p.1 < q.1))
              (translate ((rest.dropWhile fun q => p.1 < q.1) ++ [m])) := by
        rw [List.cons_append, translate, tw', dw']
      rw [e, td'] at h
      obtain ⟨cb, sib', cnf'⟩ := cnf_P_P.1 h
      have cdw : cnf (translate (rest.dropWhile fun q => p.1 < q.1)) := by
        apply ih2
        rw [td']
        exact cnf'
      have leP : P q.2.1 q.2.2 (translate (rest2.takeWhile fun y => q.1 < y.1)) Z
          ≤o P q.2.1 q.2.2
              (translate ((rest2 ++ [m]).takeWhile fun y => q.1 < y.1)) Z := by
        rcases fle with hlt | heq
        · exact Or.inl (olt_P_b _ _ _ _ hlt)
        · rw [heq]
          exact Or.inr rfl
      have sib : ¬ (P p.2.1 p.2.2 (translate (rest.takeWhile fun q => p.1 < q.1)) Z
          <o P q.2.1 q.2.2 (translate (rest2.takeWhile fun y => q.1 < y.1)) Z) := by
        intro hlt
        exact sib' (olt_ole_trans hlt leP)
      rw [translate, td]
      exact cnf_P_P.2 ⟨cb, sib, td ▸ cdw⟩

theorem cnf_dropLast {C : TrioSeq} (ne : C ≠ []) (h : cnf (translate C)) :
    cnf (translate C.dropLast) := by
  apply cnf_snoc (m := C.getLast ne)
  rwa [List.dropLast_append_getLast ne]

/-- `cnf` is preserved by any prefix `take k`. -/
theorem cnf_take {M : TrioSeq} (h : cnf (translate M)) (k : ℕ) :
    cnf (translate (M.take k)) := by
  suffices H : ∀ d k, M.length - k = d → cnf (translate (M.take k)) from H _ k rfl
  intro d
  induction d with
  | zero =>
    intro k hk
    rw [List.take_of_length_le (by omega)]
    exact h
  | succ d ih =>
    intro k hk
    have klt : k < M.length := by omega
    have ihk : cnf (translate (M.take (k + 1))) := ih (k + 1) (by omega)
    have ne : M.take (k + 1) ≠ [] := by
      have hlen : (M.take (k + 1)).length = k + 1 := by
        rw [List.length_take]
        omega
      intro he
      rw [he] at hlen
      simp at hlen
    have e : (M.take (k + 1)).dropLast = M.take k := by
      rw [List.dropLast_eq_take, List.take_take]
      congr 1
      simp
      omega
    rw [← e]
    exact cnf_dropLast ne ihk

/-- `n` identical copies of a block `(v0, w1, w2) :: R` translate to a CNF
term. -/
theorem cnf_replicate_block {v0 w1 w2 : ℕ} {R : TrioSeq}
    (hR : ∀ x ∈ R, v0 < x.1) (cR : cnf (translate R)) (n : ℕ) :
    cnf (translate (List.replicate n ((v0, w1, w2) :: R)).flatten) := by
  induction n with
  | zero => simp [translate]
  | succ m ih =>
    have hd : (List.replicate (m + 1) ((v0, w1, w2) :: R)).flatten
        = ((v0, w1, w2) :: R) ++ (List.replicate m ((v0, w1, w2) :: R)).flatten := by
      rw [List.replicate_succ, List.flatten_cons]
    have Tcond : (List.replicate m ((v0, w1, w2) :: R)).flatten = []
        ∨ ¬ v0 < (((List.replicate m ((v0, w1, w2) :: R)).flatten).headI).1 := by
      cases m with
      | zero => left; rfl
      | succ m' =>
        right
        rw [List.replicate_succ, List.flatten_cons]
        simp
    have tb : translate (((v0, w1, w2) :: R)
          ++ (List.replicate m ((v0, w1, w2) :: R)).flatten)
        = P w1 w2 (translate R)
            (translate (List.replicate m ((v0, w1, w2) :: R)).flatten) :=
      translate_block_append hR Tcond
    cases m with
    | zero =>
      rw [hd, tb,
        show translate (List.replicate 0 ((v0, w1, w2) :: R)).flatten = Z from by
          simp [translate]]
      exact cnf_P_Z.2 cR
    | succ m' =>
      have e : (List.replicate (m' + 1) ((v0, w1, w2) :: R)).flatten
          = ((v0, w1, w2) :: R) ++ (List.replicate m' ((v0, w1, w2) :: R)).flatten := by
        rw [List.replicate_succ, List.flatten_cons]
      have c : (List.replicate m' ((v0, w1, w2) :: R)).flatten = []
          ∨ ¬ v0 < (((List.replicate m' ((v0, w1, w2) :: R)).flatten).headI).1 := by
        cases m' with
        | zero => left; rfl
        | succ m'' =>
          right
          rw [List.replicate_succ, List.flatten_cons]
          simp
      have tT : translate (List.replicate (m' + 1) ((v0, w1, w2) :: R)).flatten
          = P w1 w2 (translate R)
              (translate (List.replicate m' ((v0, w1, w2) :: R)).flatten) := by
        rw [e]
        exact translate_block_append hR c
      rw [hd, tb, tT]
      refine cnf_P_P.2 ⟨cR, fun hlt => olt_irrefl _ hlt, ?_⟩
      rw [← tT]
      exact ih

/-! ## CNF context congruence -/

/-- **CNF context congruence.**  If `Z1 = z1 :: T1`, `Z2 = z2 :: T2` share
their leading row-0 (`z1.1 = z2.1`), `translate Z1 <o translate Z2`, and
`translate Z1` is CNF, then a common good part `G` preserves CNF. -/
theorem cnf_ctx_cong {z1 z2 : ℕ × ℕ × ℕ} {T1 T2 : TrioSeq}
    (cZ1 : cnf (translate (z1 :: T1)))
    (decr : translate (z1 :: T1) <o translate (z2 :: T2))
    (root : z1.1 = z2.1)
    (leadle : ∃ p1 p2 b1 c1 q1 q2 b2 c2, translate (z1 :: T1) = P p1 p2 b1 c1
        ∧ translate (z2 :: T2) = P q1 q2 b2 c2 ∧ P p1 p2 b1 Z ≤o P q1 q2 b2 Z)
    (r1 : ∀ x ∈ T1, z1.1 ≤ x.1) (r2 : ∀ x ∈ T2, z2.1 ≤ x.1)
    (G : TrioSeq) (hG2 : cnf (translate (G ++ z2 :: T2))) :
    cnf (translate (G ++ z1 :: T1)) := by
  obtain ⟨p1, p2, b1, c1, q1, q2, b2, c2, lZ1, lZ2, lle⟩ := leadle
  match G with
  | [] => simpa using cZ1
  | g :: G' =>
    by_cases allG : ∀ x ∈ G', g.1 < x.1
    · have allG' : ∀ x ∈ G', (fun q : ℕ × ℕ × ℕ => decide (g.1 < q.1)) x = true := by
        intro x hx; simpa using allG x hx
      by_cases hPg : g.1 < z1.1
      · -- the whole tail nests under `g`; pass to `G'`
        have aZ1 : ∀ x ∈ z1 :: T1, g.1 < x.1 := by
          intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact hPg
          · exact lt_of_lt_of_le hPg (r1 _ hx)
        have aZ2 : ∀ x ∈ z2 :: T2, g.1 < x.1 := by
          intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact root ▸ hPg
          · exact lt_of_lt_of_le (root ▸ hPg) (r2 _ hx)
        have all1 : ∀ x ∈ G' ++ z1 :: T1, g.1 < x.1 := by
          intro x hx; rcases List.mem_append.1 hx with h | h
          exacts [allG x h, aZ1 x h]
        have all2 : ∀ x ∈ G' ++ z2 :: T2, g.1 < x.1 := by
          intro x hx; rcases List.mem_append.1 hx with h | h
          exacts [allG x h, aZ2 x h]
        have e1 : translate (g :: (G' ++ z1 :: T1))
            = P g.2.1 g.2.2 (translate (G' ++ z1 :: T1)) Z := by
          rw [translate, List.takeWhile_eq_self_iff.2 (by simpa using all1),
            List.dropWhile_eq_nil_iff.2 (by simpa using all1), translate]
        have e2 : translate (g :: (G' ++ z2 :: T2))
            = P g.2.1 g.2.2 (translate (G' ++ z2 :: T2)) Z := by
          rw [translate, List.takeWhile_eq_self_iff.2 (by simpa using all2),
            List.dropWhile_eq_nil_iff.2 (by simpa using all2), translate]
        rw [List.cons_append] at hG2 ⊢
        rw [e2] at hG2
        rw [e1]
        exact cnf_P_Z.2 (cnf_ctx_cong cZ1 decr root
          ⟨p1, p2, b1, c1, q1, q2, b2, c2, lZ1, lZ2, lle⟩ r1 r2 G' (cnf_P_Z.1 hG2))
      · -- the tail is a sibling after `g`'s subtree
        have hPg2 : ¬ g.1 < z2.1 := root ▸ hPg
        have tw1 : (G' ++ z1 :: T1).takeWhile (fun q => g.1 < q.1) = G' := by
          rw [takeWhile_append_all allG']
          simp [hPg]
        have dw1 : (G' ++ z1 :: T1).dropWhile (fun q => g.1 < q.1) = z1 :: T1 := by
          rw [dropWhile_append_all allG']
          simp [hPg]
        have tw2 : (G' ++ z2 :: T2).takeWhile (fun q => g.1 < q.1) = G' := by
          rw [takeWhile_append_all allG']
          simp [hPg2]
        have dw2 : (G' ++ z2 :: T2).dropWhile (fun q => g.1 < q.1) = z2 :: T2 := by
          rw [dropWhile_append_all allG']
          simp [hPg2]
        have e1 : translate (g :: (G' ++ z1 :: T1))
            = P g.2.1 g.2.2 (translate G') (P p1 p2 b1 c1) := by
          rw [translate, tw1, dw1, lZ1]
        have e2 : translate (g :: (G' ++ z2 :: T2))
            = P g.2.1 g.2.2 (translate G') (P q1 q2 b2 c2) := by
          rw [translate, tw2, dw2, lZ2]
        rw [List.cons_append] at hG2 ⊢
        rw [e2] at hG2
        obtain ⟨ctg, bnd2, -⟩ := cnf_P_P.1 hG2
        have bnd1 : ¬ (P g.2.1 g.2.2 (translate G') Z <o P p1 p2 b1 Z) := by
          intro hlt
          exact bnd2 (olt_ole_trans hlt lle)
        rw [e1]
        exact cnf_P_P.2 ⟨ctg, bnd1, lZ1 ▸ cZ1⟩
    · -- `G'` already drops to/below `g`; recurse on the shorter tail
      push Not at allG
      obtain ⟨x, hx, hnx⟩ := allG
      have hnx' : ¬ (fun q : ℕ × ℕ × ℕ => decide (g.1 < q.1)) x = true := by
        simpa using hnx
      have tw1 : (G' ++ z1 :: T1).takeWhile (fun q => g.1 < q.1)
          = G'.takeWhile (fun q => g.1 < q.1) := takeWhile_append_not hx hnx'
      have dw1 : (G' ++ z1 :: T1).dropWhile (fun q => g.1 < q.1)
          = G'.dropWhile (fun q => g.1 < q.1) ++ z1 :: T1 := dropWhile_append_not hx hnx'
      have tw2 : (G' ++ z2 :: T2).takeWhile (fun q => g.1 < q.1)
          = G'.takeWhile (fun q => g.1 < q.1) := takeWhile_append_not hx hnx'
      have dw2 : (G' ++ z2 :: T2).dropWhile (fun q => g.1 < q.1)
          = G'.dropWhile (fun q => g.1 < q.1) ++ z2 :: T2 := dropWhile_append_not hx hnx'
      have Dne : G'.dropWhile (fun q => g.1 < q.1) ≠ [] := by
        intro he
        exact hnx' (List.dropWhile_eq_nil_iff.1 he x hx)
      obtain ⟨d, D', hD⟩ : ∃ d D', G'.dropWhile (fun q => g.1 < q.1) = d :: D' := by
        rcases hD : G'.dropWhile (fun q => g.1 < q.1) with - | ⟨d, D'⟩
        · exact absurd hD Dne
        · exact ⟨d, D', hD⟩
      have e1 : translate (g :: (G' ++ z1 :: T1))
          = P g.2.1 g.2.2 (translate (G'.takeWhile fun q => g.1 < q.1))
              (translate ((d :: D') ++ z1 :: T1)) := by
        rw [translate, tw1, dw1, hD]
      have e2 : translate (g :: (G' ++ z2 :: T2))
          = P g.2.1 g.2.2 (translate (G'.takeWhile fun q => g.1 < q.1))
              (translate ((d :: D') ++ z2 :: T2)) := by
        rw [translate, tw2, dw2, hD]
      have p1' : translate ((d :: D') ++ z1 :: T1)
          = P d.2.1 d.2.2 (translate ((D' ++ z1 :: T1).takeWhile fun y => d.1 < y.1))
              (translate ((D' ++ z1 :: T1).dropWhile fun y => d.1 < y.1)) := by
        rw [List.cons_append, translate]
      have p2' : translate ((d :: D') ++ z2 :: T2)
          = P d.2.1 d.2.2 (translate ((D' ++ z2 :: T2).takeWhile fun y => d.1 < y.1))
              (translate ((D' ++ z2 :: T2).dropWhile fun y => d.1 < y.1)) := by
        rw [List.cons_append, translate]
      have decrD : translate ((d :: D') ++ z1 :: T1)
          <o translate ((d :: D') ++ z2 :: T2) :=
        translate_ctx_cong decr root r1 r2 (d :: D')
      have argle : translate ((D' ++ z1 :: T1).takeWhile fun y => d.1 < y.1)
            <o translate ((D' ++ z2 :: T2).takeWhile fun y => d.1 < y.1)
          ∨ translate ((D' ++ z1 :: T1).takeWhile fun y => d.1 < y.1)
            = translate ((D' ++ z2 :: T2).takeWhile fun y => d.1 < y.1) := by
        rw [p1', p2', olt_P_P] at decrD
        rcases decrD with h | ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h, -⟩
        · omega
        · omega
        · exact Or.inl h
        · exact Or.inr h
      rw [List.cons_append] at hG2 ⊢
      rw [e2, p2'] at hG2
      obtain ⟨ctw, bnd2, cD2⟩ := cnf_P_P.1 hG2
      have cD2' : cnf (translate ((d :: D') ++ z2 :: T2)) := by
        rw [p2']
        exact cD2
      have cD1 : cnf (translate ((d :: D') ++ z1 :: T1)) :=
        cnf_ctx_cong cZ1 decr root
          ⟨p1, p2, b1, c1, q1, q2, b2, c2, lZ1, lZ2, lle⟩ r1 r2 (d :: D') cD2'
      -- the boundary transfers from the appended argument
      have bnd1 : ¬ (P g.2.1 g.2.2 (translate (G'.takeWhile fun q => g.1 < q.1)) Z
          <o P d.2.1 d.2.2
              (translate ((D' ++ z1 :: T1).takeWhile fun y => d.1 < y.1)) Z) := by
        intro hlt
        rw [olt_P_P] at hlt
        rcases hlt with h | ⟨heq, h⟩ | ⟨heq1, heq2, h⟩ | ⟨-, -, -, h⟩
        · exact bnd2 (olt_P_P.2 (Or.inl h))
        · exact bnd2 (olt_P_P.2 (Or.inr (Or.inl ⟨heq, h⟩)))
        · rcases argle with ha | ha
          · exact bnd2 (olt_P_P.2 (Or.inr (Or.inr (Or.inl ⟨heq1, heq2, olt_trans h ha⟩))))
          · exact bnd2 (olt_P_P.2 (Or.inr (Or.inr (Or.inl ⟨heq1, heq2, ha ▸ h⟩))))
        · exact not_olt_Z Z h
      rw [e1, p1']
      refine cnf_P_P.2 ⟨ctw, bnd1, ?_⟩
      rw [← p1']
      exact cD1
  termination_by G.length
  decreasing_by
  · simp only [List.length_cons]
    omega
  · have hle : (d :: D').length ≤ G'.length := by
      rw [← hD]
      exact List.length_dropWhile_le _ G'
    simp only [List.length_cons] at hle ⊢
    omega

/-- CNF is inherited by a re-opening tail. -/
theorem cnf_tail {t : ℕ × ℕ × ℕ} {T' : TrioSeq}
    (rT : ∀ x ∈ T', t.1 ≤ x.1)
    (G : TrioSeq) (hGT : cnf (translate (G ++ t :: T'))) :
    cnf (translate (t :: T')) := by
  match G with
  | [] => simpa using hGT
  | g :: G' =>
    by_cases allG : ∀ x ∈ G', g.1 < x.1
    · have allG' : ∀ x ∈ G', (fun q : ℕ × ℕ × ℕ => decide (g.1 < q.1)) x = true := by
        intro x hx; simpa using allG x hx
      by_cases hPg : g.1 < t.1
      · have aT : ∀ x ∈ t :: T', g.1 < x.1 := by
          intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact hPg
          · exact lt_of_lt_of_le hPg (rT _ hx)
        have all : ∀ x ∈ G' ++ t :: T', g.1 < x.1 := by
          intro x hx; rcases List.mem_append.1 hx with h | h
          exacts [allG x h, aT x h]
        have e : translate (g :: (G' ++ t :: T'))
            = P g.2.1 g.2.2 (translate (G' ++ t :: T')) Z := by
          rw [translate, List.takeWhile_eq_self_iff.2 (by simpa using all),
            List.dropWhile_eq_nil_iff.2 (by simpa using all), translate]
        rw [List.cons_append] at hGT
        rw [e] at hGT
        exact cnf_tail rT G' (cnf_P_Z.1 hGT)
      · have tw : (G' ++ t :: T').takeWhile (fun q => g.1 < q.1) = G' := by
          rw [takeWhile_append_all allG']
          simp [hPg]
        have dw : (G' ++ t :: T').dropWhile (fun q => g.1 < q.1) = t :: T' := by
          rw [dropWhile_append_all allG']
          simp [hPg]
        have e : translate (g :: (G' ++ t :: T'))
            = P g.2.1 g.2.2 (translate G') (translate (t :: T')) := by
          rw [translate, tw, dw]
        rw [List.cons_append] at hGT
        rw [e, translate] at hGT
        rw [translate]
        exact (cnf_P_P.1 hGT).2.2
    · push Not at allG
      obtain ⟨x, hx, hnx⟩ := allG
      have hnx' : ¬ (fun q : ℕ × ℕ × ℕ => decide (g.1 < q.1)) x = true := by
        simpa using hnx
      have tw : (G' ++ t :: T').takeWhile (fun q => g.1 < q.1)
          = G'.takeWhile (fun q => g.1 < q.1) := takeWhile_append_not hx hnx'
      have dw : (G' ++ t :: T').dropWhile (fun q => g.1 < q.1)
          = G'.dropWhile (fun q => g.1 < q.1) ++ t :: T' := dropWhile_append_not hx hnx'
      have Dne : G'.dropWhile (fun q => g.1 < q.1) ≠ [] := by
        intro he
        exact hnx' (List.dropWhile_eq_nil_iff.1 he x hx)
      obtain ⟨d, D', hD⟩ : ∃ d D', G'.dropWhile (fun q => g.1 < q.1) = d :: D' := by
        rcases hD : G'.dropWhile (fun q => g.1 < q.1) with - | ⟨d, D'⟩
        · exact absurd hD Dne
        · exact ⟨d, D', hD⟩
      have e : translate (g :: (G' ++ t :: T'))
          = P g.2.1 g.2.2 (translate (G'.takeWhile fun q => g.1 < q.1))
              (translate ((d :: D') ++ t :: T')) := by
        rw [translate, tw, dw, hD]
      have p : translate ((d :: D') ++ t :: T')
          = P d.2.1 d.2.2 (translate ((D' ++ t :: T').takeWhile fun y => d.1 < y.1))
              (translate ((D' ++ t :: T').dropWhile fun y => d.1 < y.1)) := by
        rw [List.cons_append, translate]
      rw [List.cons_append] at hGT
      rw [e, p] at hGT
      have hD1 : cnf (translate ((d :: D') ++ t :: T')) := by
        rw [p]
        exact (cnf_P_P.1 hGT).2.2
      exact cnf_tail rT (d :: D') hD1
  termination_by G.length
  decreasing_by
  · simp only [List.length_cons]
    omega
  · have hle : (d :: D').length ≤ G'.length := by
      rw [← hD]
      exact List.length_dropWhile_le _ G'
    simp only [List.length_cons] at hle ⊢
    omega

/-! ## The subscript-1 shift on terms

`shiftr01 d0 d1` shifts row 0 and row 1 of a sequence.  On terms this becomes
a uniform shift `tshift1 d1` of every first subscript, under which both the
order and `cnf` are invariant.  This is what replaces the two-row fact
"row-0 shifts do not change the translation". -/

def tshift1 (d : ℕ) : Three → Three
  | Z => Z
  | P a1 a2 b c => P (a1 + d) a2 (tshift1 d b) (tshift1 d c)

@[simp] theorem tshift1_Z (d : ℕ) : tshift1 d Z = Z := rfl
@[simp] theorem tshift1_P (d a1 a2 : ℕ) (b c : Three) :
    tshift1 d (P a1 a2 b c) = P (a1 + d) a2 (tshift1 d b) (tshift1 d c) := rfl

theorem tshift1_inj {d : ℕ} : ∀ {x y : Three}, tshift1 d x = tshift1 d y → x = y := by
  intro x
  induction x with
  | Z =>
    intro y h
    cases y with
    | Z => rfl
    | P e1 e2 f g => exact absurd h (by simp)
  | P a1 a2 b c ihb ihc =>
    intro y h
    cases y with
    | Z => exact absurd h (by simp)
    | P e1 e2 f g =>
      simp only [tshift1_P, P.injEq] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      simp only [P.injEq]
      exact ⟨by omega, h2, ihb h3, ihc h4⟩

theorem olt_tshift1 {d : ℕ} : ∀ {x y : Three},
    (tshift1 d x <o tshift1 d y) ↔ x <o y := by
  intro x
  induction x with
  | Z =>
    intro y
    cases y with
    | Z => simp
    | P e1 e2 f g => simp
  | P a1 a2 b c ihb ihc =>
    intro y
    cases y with
    | Z => simp
    | P e1 e2 f g =>
      simp only [tshift1_P, olt_P_P]
      constructor
      · rintro (h | ⟨h, h2⟩ | ⟨h, h2, h3⟩ | ⟨h, h2, h3, h4⟩)
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl ⟨by omega, h2⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨by omega, h2, ihb.1 h3⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨by omega, h2, tshift1_inj h3, ihc.1 h4⟩))
      · rintro (h | ⟨h, h2⟩ | ⟨h, h2, h3⟩ | ⟨h, h2, h3, h4⟩)
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl ⟨by omega, h2⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨by omega, h2, ihb.2 h3⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨by omega, h2, by rw [h3], ihc.2 h4⟩))

theorem cnf_tshift1 (d : ℕ) : ∀ {t : Three}, cnf t → cnf (tshift1 d t) := by
  intro t
  induction t with
  | Z => intro _; trivial
  | P a1 a2 b c ihb ihc =>
    intro h
    cases c with
    | Z => exact cnf_P_Z.2 (ihb (cnf_P_Z.1 h))
    | P e1 e2 f g =>
      obtain ⟨cb, sib, cc⟩ := cnf_P_P.1 h
      refine cnf_P_P.2 ⟨ihb cb, ?_, ihc cc⟩
      intro hlt
      exact sib (olt_tshift1.1 hlt)

/-! ## The double shift and the copy towers -/

/-- Shift row 0 by `d0` and row 1 by `d1`. -/
def shiftr01 (d0 d1 : ℕ) : TrioSeq → TrioSeq :=
  List.map fun p => (p.1 + d0, p.2.1 + d1, p.2.2)

@[simp] theorem shiftr01_zero (M : TrioSeq) : shiftr01 0 0 M = M := by
  unfold shiftr01
  simp

@[simp] theorem shiftr01_nil (d0 d1 : ℕ) : shiftr01 d0 d1 [] = [] := rfl

theorem shiftr01_cons (d0 d1 : ℕ) (p : ℕ × ℕ × ℕ) (M : TrioSeq) :
    shiftr01 d0 d1 (p :: M) = (p.1 + d0, p.2.1 + d1, p.2.2) :: shiftr01 d0 d1 M := rfl

theorem mem_shiftr01 {d0 d1 : ℕ} {M : TrioSeq} {x : ℕ × ℕ × ℕ} :
    x ∈ shiftr01 d0 d1 M ↔ ∃ p ∈ M, (p.1 + d0, p.2.1 + d1, p.2.2) = x := by
  unfold shiftr01
  simp

/-- The translation of a double shift is the subscript-1 shift of the
translation. -/
theorem translate_shiftr01 (d0 d1 : ℕ) (M : TrioSeq) :
    translate (shiftr01 d0 d1 M) = tshift1 d1 (translate M) := by
  induction M using translate.induct with
  | case1 => simp [translate, shiftr01]
  | case2 p rest ih1 ih2 =>
    have hpred : ((fun q : ℕ × ℕ × ℕ => decide (p.1 + d0 < q.1))
          ∘ fun r : ℕ × ℕ × ℕ => (r.1 + d0, r.2.1 + d1, r.2.2))
        = fun r : ℕ × ℕ × ℕ => decide (p.1 < r.1) := by
      funext r
      simp only [Function.comp_apply]
      rw [decide_eq_decide]
      omega
    show translate ((p.1 + d0, p.2.1 + d1, p.2.2)
        :: (rest.map fun r => (r.1 + d0, r.2.1 + d1, r.2.2))) = _
    rw [translate]
    show P (p.2.1 + d1) p.2.2
        (translate ((rest.map fun r => (r.1 + d0, r.2.1 + d1, r.2.2)).takeWhile
          fun q => p.1 + d0 < q.1))
        (translate ((rest.map fun r => (r.1 + d0, r.2.1 + d1, r.2.2)).dropWhile
          fun q => p.1 + d0 < q.1)) = _
    rw [List.takeWhile_map, List.dropWhile_map, hpred]
    show P (p.2.1 + d1) p.2.2
        (translate (shiftr01 d0 d1 (rest.takeWhile fun q => p.1 < q.1)))
        (translate (shiftr01 d0 d1 (rest.dropWhile fun q => p.1 < q.1))) = _
    rw [ih1, ih2, translate]
    rfl

/-- Ascending copies with lifts `d0` (row 0) and `d1` (row 1). -/
def copies (d0 d1 : ℕ) (blk : TrioSeq) (n : ℕ) : TrioSeq :=
  (List.range n).flatMap fun k => shiftr01 (k * d0) (k * d1) blk

@[simp] theorem copies_zero (d0 d1 : ℕ) (blk : TrioSeq) : copies d0 d1 blk 0 = [] := rfl

theorem copies_succ_front (d0 d1 : ℕ) (blk : TrioSeq) (n : ℕ) :
    copies d0 d1 blk (n + 1) = blk ++ shiftr01 d0 d1 (copies d0 d1 blk n) := by
  unfold copies
  rw [List.range_succ_eq_map, List.flatMap_cons, Nat.zero_mul, Nat.zero_mul,
    shiftr01_zero]
  congr 1
  rw [List.flatMap_map]
  unfold shiftr01
  rw [List.map_flatMap]
  congr 1
  funext k
  rw [List.map_map]
  congr 1
  funext p
  simp only [Function.comp_apply, Nat.succ_mul, Prod.mk.injEq, and_true]
  omega

@[simp] theorem copies_one (d0 d1 : ℕ) (blk : TrioSeq) : copies d0 d1 blk 1 = blk := by
  rw [copies_succ_front]
  simp

theorem copies_succ_cons (d0 d1 v0 w1 w2 : ℕ) (R : TrioSeq) (n : ℕ) :
    copies d0 d1 ((v0, w1, w2) :: R) (n + 1)
      = (v0, w1, w2) :: (R ++ shiftr01 d0 d1 (copies d0 d1 ((v0, w1, w2) :: R) n)) := by
  rw [copies_succ_front, List.cons_append]

theorem copies_v0_le {v0 w1 w2 : ℕ} {R : TrioSeq}
    (Rle : ∀ x ∈ R, v0 ≤ x.1) (d0 d1 n : ℕ) :
    ∀ x ∈ copies d0 d1 ((v0, w1, w2) :: R) n, v0 ≤ x.1 := by
  intro x hx
  unfold copies at hx
  obtain ⟨k, -, hk⟩ := List.mem_flatMap.1 hx
  obtain ⟨p, hp, rfl⟩ := mem_shiftr01.1 hk
  have hvp : v0 ≤ p.1 := by
    rcases List.mem_cons.1 hp with rfl | hp'
    · simp
    · exact Rle p hp'
  simp only []
  omega

theorem copies_tl_gt {v0 w1 w2 : ℕ} {R : TrioSeq}
    (hR : ∀ x ∈ R, v0 < x.1) {d0 : ℕ} (dpos : 0 < d0) (d1 : ℕ) {n : ℕ} (_n1 : 1 ≤ n) :
    ∀ x ∈ R ++ shiftr01 d0 d1 (copies d0 d1 ((v0, w1, w2) :: R) (n - 1)), v0 < x.1 := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact hR x hx
  · obtain ⟨p, hp, rfl⟩ := mem_shiftr01.1 hx
    have hvp : v0 ≤ p.1 :=
      copies_v0_le (fun x hx => (hR x hx).le) d0 d1 (n - 1) p hp
    simp only []
    omega

/-- `n` ascending copies of a CNF block translate to a CNF term.  The lead
condition covers both ascending branches: `i1 = 1` gives the first
disjunct (`d1 = 0`, row 1 decides) and `i1 = 2` the second (rows 1 meet,
row 2 decides). -/
theorem cnf_copies {v0 w1 w2 d0 d1 : ℕ} {R : TrioSeq} {lp : ℕ × ℕ × ℕ}
    (hR : ∀ x ∈ R, v0 < x.1)
    (d0pos : 0 < d0)
    (lead_lt : w1 + d1 < lp.2.1 ∨ (w1 + d1 = lp.2.1 ∧ w2 < lp.2.2))
    (lphd : lp.1 = v0 + d0)
    (cBlp : cnf (translate (((v0, w1, w2) :: R) ++ [lp])))
    (n : ℕ) :
    cnf (translate (copies d0 d1 ((v0, w1, w2) :: R) n)) := by
  induction n with
  | zero => simp [translate]
  | succ n ih =>
    cases n with
    | zero =>
      rw [copies_one]
      have h0 : translate ((v0, w1, w2) :: R)
          = translate ((((v0, w1, w2) :: R) ++ [lp]).dropLast) := by
        rw [List.dropLast_concat]
      rw [h0]
      exact cnf_dropLast (by simp) cBlp
    | succ m =>
      have cpcons := copies_succ_cons d0 d1 v0 w1 w2 R m
      have z1cons : shiftr01 d0 d1 (copies d0 d1 ((v0, w1, w2) :: R) (m + 1))
          = (v0 + d0, w1 + d1, w2)
            :: shiftr01 d0 d1
                (R ++ shiftr01 d0 d1 (copies d0 d1 ((v0, w1, w2) :: R) m)) := by
        rw [copies_succ_cons, shiftr01_cons]
      have tlgt : ∀ x ∈ R ++ shiftr01 d0 d1 (copies d0 d1 ((v0, w1, w2) :: R) m),
          v0 < x.1 := by
        have h := copies_tl_gt (w1 := w1) (w2 := w2) hR d0pos d1 (n := m + 1) (by omega)
        simpa using h
      have st1 : translate (copies d0 d1 ((v0, w1, w2) :: R) (m + 1))
          = P w1 w2
              (translate (R ++ shiftr01 d0 d1 (copies d0 d1 ((v0, w1, w2) :: R) m)))
              Z := by
        rw [cpcons]
        exact translate_single_tree tlgt
      have tZ1 : translate ((v0 + d0, w1 + d1, w2)
            :: shiftr01 d0 d1
                (R ++ shiftr01 d0 d1 (copies d0 d1 ((v0, w1, w2) :: R) m)))
          = P (w1 + d1) w2
              (tshift1 d1
                (translate (R ++ shiftr01 d0 d1 (copies d0 d1 ((v0, w1, w2) :: R) m))))
              Z := by
        rw [← z1cons, translate_shiftr01, st1]
        rfl
      have tlp : translate ([lp] : TrioSeq) = P lp.2.1 lp.2.2 Z Z := by
        rw [translate]
        simp [translate]
      have decr : translate ((v0 + d0, w1 + d1, w2)
            :: shiftr01 d0 d1
                (R ++ shiftr01 d0 d1 (copies d0 d1 ((v0, w1, w2) :: R) m)))
          <o translate ([lp] : TrioSeq) := by
        rw [tZ1, tlp, olt_P_P]
        rcases lead_lt with h | ⟨h1, h2⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨h1, h2⟩)
      have cZ1 : cnf (translate ((v0 + d0, w1 + d1, w2)
          :: shiftr01 d0 d1
              (R ++ shiftr01 d0 d1 (copies d0 d1 ((v0, w1, w2) :: R) m)))) := by
        rw [← z1cons, translate_shiftr01]
        exact cnf_tshift1 d1 ih
      have r1 : ∀ x ∈ shiftr01 d0 d1
            (R ++ shiftr01 d0 d1 (copies d0 d1 ((v0, w1, w2) :: R) m)),
          ((v0 + d0, w1 + d1, w2) : ℕ × ℕ × ℕ).1 ≤ x.1 := by
        intro x hx
        obtain ⟨p, hp, rfl⟩ := mem_shiftr01.1 hx
        have : v0 ≤ p.1 := (tlgt p hp).le
        simp only []
        omega
      have root : ((v0 + d0, w1 + d1, w2) : ℕ × ℕ × ℕ).1 = lp.1 := lphd.symm
      have leadle : ∃ p1 p2 b1 c1 q1 q2 b2 c2,
          translate ((v0 + d0, w1 + d1, w2)
            :: shiftr01 d0 d1
                (R ++ shiftr01 d0 d1 (copies d0 d1 ((v0, w1, w2) :: R) m)))
            = P p1 p2 b1 c1
          ∧ translate ([lp] : TrioSeq) = P q1 q2 b2 c2
          ∧ P p1 p2 b1 Z ≤o P q1 q2 b2 Z := by
        refine ⟨w1 + d1, w2,
          tshift1 d1
            (translate (R ++ shiftr01 d0 d1 (copies d0 d1 ((v0, w1, w2) :: R) m))),
          Z, lp.2.1, lp.2.2, Z, Z, tZ1, tlp, Or.inl (olt_P_P.2 ?_)⟩
        rcases lead_lt with h | ⟨h1, h2⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨h1, h2⟩)
      have key := cnf_ctx_cong cZ1 decr root leadle r1 (by simp)
        ((v0, w1, w2) :: R) (by simpa using cBlp)
      rw [copies_succ_front, z1cons]
      exact key

/-! ## CNF preservation by one expansion step -/

/-- **CNF preservation, the exact-copy (`i1 = 0`) case.** -/
theorem cnf_oper_i1eq0 {v0 w1 w2 : ℕ} {R : TrioSeq} {lp : ℕ × ℕ × ℕ} {G : TrioSeq}
    {n : ℕ}
    (hR : ∀ x ∈ R, v0 < x.1) (lpv : v0 < lp.1) (n1 : 1 ≤ n)
    (cM : cnf (translate (G ++ ((v0, w1, w2) :: R) ++ [lp]))) :
    cnf (translate (G ++ (List.replicate n ((v0, w1, w2) :: R)).flatten)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have RlpV : ∀ x ∈ R ++ [lp], v0 < x.1 := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hR x hx
    · simp at hx
      simpa [hx] using lpv
  have tZ2 : translate ((v0, w1, w2) :: (R ++ [lp]))
      = P w1 w2 (translate (R ++ [lp])) Z := translate_single_tree RlpV
  have Tcond : (List.replicate m ((v0, w1, w2) :: R)).flatten = []
      ∨ ¬ v0 < (((List.replicate m ((v0, w1, w2) :: R)).flatten).headI).1 := by
    cases m with
    | zero => left; rfl
    | succ m' =>
      right
      rw [List.replicate_succ, List.flatten_cons]
      simp
  have e1n : (List.replicate (m + 1) ((v0, w1, w2) :: R)).flatten
      = (v0, w1, w2) :: (R ++ (List.replicate m ((v0, w1, w2) :: R)).flatten) := by
    rw [List.replicate_succ, List.flatten_cons, List.cons_append]
  have tZ1 : translate ((v0, w1, w2)
        :: (R ++ (List.replicate m ((v0, w1, w2) :: R)).flatten))
      = P w1 w2 (translate R)
          (translate (List.replicate m ((v0, w1, w2) :: R)).flatten) := by
    rw [← List.cons_append]
    exact translate_block_append hR Tcond
  have rT : ∀ x ∈ R ++ [lp], ((v0, w1, w2) : ℕ × ℕ × ℕ).1 ≤ x.1 :=
    fun x hx => (RlpV x hx).le
  have cM' : cnf (translate (G ++ (v0, w1, w2) :: (R ++ [lp]))) := by
    have h : G ++ ((v0, w1, w2) :: R) ++ [lp] = G ++ (v0, w1, w2) :: (R ++ [lp]) := by
      simp
    rwa [h] at cM
  have cblk : cnf (translate ((v0, w1, w2) :: (R ++ [lp]))) := cnf_tail rT G cM'
  have cRlp : cnf (translate (R ++ [lp])) := by
    rw [tZ2] at cblk
    exact cnf_P_Z.1 cblk
  have cR : cnf (translate R) := cnf_snoc cRlp
  have cZ1 : cnf (translate (List.replicate (m + 1) ((v0, w1, w2) :: R)).flatten) :=
    cnf_replicate_block hR cR (m + 1)
  have RltRlp : translate R <o translate (R ++ [lp]) := translate_snoc_increase R lp
  have decr : translate ((v0, w1, w2)
        :: (R ++ (List.replicate m ((v0, w1, w2) :: R)).flatten))
      <o translate ((v0, w1, w2) :: (R ++ [lp])) := by
    rw [tZ1, tZ2]
    exact olt_P_b _ _ _ _ RltRlp
  have sub : ∀ x ∈ (List.replicate m ((v0, w1, w2) :: R)).flatten,
      x ∈ (v0, w1, w2) :: R := by
    intro x hx
    obtain ⟨l, hl, hxl⟩ := List.mem_flatten.1 hx
    rwa [List.eq_of_mem_replicate hl] at hxl
  have r1 : ∀ x ∈ R ++ (List.replicate m ((v0, w1, w2) :: R)).flatten,
      ((v0, w1, w2) : ℕ × ℕ × ℕ).1 ≤ x.1 := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact (hR x hx).le
    · rcases List.mem_cons.1 (sub x hx) with rfl | hx'
      · exact le_rfl
      · exact (hR x hx').le
  have key : cnf (translate (G ++ (v0, w1, w2)
      :: (R ++ (List.replicate m ((v0, w1, w2) :: R)).flatten))) := by
    refine cnf_ctx_cong ?_ decr rfl ?_ r1 rT G cM'
    · rw [← e1n]
      exact cZ1
    · exact ⟨w1, w2, translate R,
        translate (List.replicate m ((v0, w1, w2) :: R)).flatten,
        w1, w2, translate (R ++ [lp]), Z, tZ1, tZ2,
        Or.inl (olt_P_b _ _ _ _ RltRlp)⟩
  rw [e1n]
  exact key

theorem copies_replicate (blk : TrioSeq) (n : ℕ) :
    copies 0 0 blk n = (List.replicate n blk).flatten := by
  unfold copies
  have h : (fun k : ℕ => shiftr01 (k * 0) (k * 0) blk) = fun _ : ℕ => blk := by
    funext k
    rw [Nat.mul_zero, shiftr01_zero]
  rw [h, List.flatMap_def, List.map_const', List.length_range]

/-- **CNF preservation, the ascending cases (`i1 ∈ {1, 2}`).**  Wraps
`cnf_copies` in the good part via the context congruence. -/
theorem cnf_oper_asc {v0 w1 w2 d0 d1 : ℕ} {R : TrioSeq} {lp : ℕ × ℕ × ℕ}
    {G : TrioSeq} {n : ℕ}
    (hR : ∀ x ∈ R, v0 < x.1)
    (d0pos : 0 < d0)
    (lead_lt : w1 + d1 < lp.2.1 ∨ (w1 + d1 = lp.2.1 ∧ w2 < lp.2.2))
    (lphd : lp.1 = v0 + d0)
    (n1 : 1 ≤ n)
    (cM : cnf (translate (G ++ ((v0, w1, w2) :: R) ++ [lp]))) :
    cnf (translate (G ++ copies d0 d1 ((v0, w1, w2) :: R) n)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have lpv : v0 < lp.1 := by omega
  have Rlp_gt : ∀ x ∈ R ++ [lp], v0 < x.1 := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hR x hx
    · simp at hx
      simp [hx]
      omega
  -- the decrease of the copies against the original tail
  have decr : translate (copies d0 d1 ((v0, w1, w2) :: R) (m + 1))
      <o translate (((v0, w1, w2) :: R) ++ [lp]) := by
    cases m with
    | zero =>
      rw [copies_one]
      exact translate_snoc_increase _ _
    | succ m' =>
      have z1cons : shiftr01 d0 d1 (copies d0 d1 ((v0, w1, w2) :: R) (m' + 1))
          = (v0 + d0, w1 + d1, w2)
            :: shiftr01 d0 d1
                (R ++ shiftr01 d0 d1 (copies d0 d1 ((v0, w1, w2) :: R) m')) := by
        rw [copies_succ_cons, shiftr01_cons]
      have tlgt' : ∀ x ∈ R ++ shiftr01 d0 d1 (copies d0 d1 ((v0, w1, w2) :: R) m'),
          v0 < x.1 := by
        have h := copies_tl_gt (w1 := w1) (w2 := w2) hR d0pos d1 (n := m' + 1) (by omega)
        simpa using h
      have Cge : ∀ x ∈ shiftr01 d0 d1
            (R ++ shiftr01 d0 d1 (copies d0 d1 ((v0, w1, w2) :: R) m')),
          ((v0 + d0, w1 + d1, w2) : ℕ × ℕ × ℕ).1 ≤ x.1 := by
        intro x hx
        obtain ⟨p, hp, rfl⟩ := mem_shiftr01.1 hx
        have : v0 ≤ p.1 := (tlgt' p hp).le
        simp only []
        omega
      have Croot : ((v0 + d0, w1 + d1, w2) : ℕ × ℕ × ℕ).1 = lp.1 := lphd.symm
      have core := core_asc (w1 := w1) (w2 := w2) hR Cge Croot lpv
        (by simpa using lead_lt)
      have e : copies d0 d1 ((v0, w1, w2) :: R) (m' + 1 + 1)
          = ((v0, w1, w2) :: R) ++ ((v0 + d0, w1 + d1, w2)
              :: shiftr01 d0 d1
                  (R ++ shiftr01 d0 d1 (copies d0 d1 ((v0, w1, w2) :: R) m'))) := by
        rw [copies_succ_front, z1cons]
      rw [e]
      exact core
  -- cons form and single-tree shapes
  have cpcons := copies_succ_cons d0 d1 v0 w1 w2 R m
  have tlgt : ∀ x ∈ R ++ shiftr01 d0 d1 (copies d0 d1 ((v0, w1, w2) :: R) m),
      v0 < x.1 := by
    have h := copies_tl_gt (w1 := w1) (w2 := w2) hR d0pos d1 (n := m + 1) (by omega)
    simpa using h
  have st1 : translate (copies d0 d1 ((v0, w1, w2) :: R) (m + 1))
      = P w1 w2
          (translate (R ++ shiftr01 d0 d1 (copies d0 d1 ((v0, w1, w2) :: R) m))) Z := by
    rw [cpcons]
    exact translate_single_tree tlgt
  have st2 : translate (((v0, w1, w2) :: R) ++ [lp])
      = P w1 w2 (translate (R ++ [lp])) Z := by
    rw [List.cons_append]
    exact translate_single_tree Rlp_gt
  have rT : ∀ x ∈ R ++ [lp], ((v0, w1, w2) : ℕ × ℕ × ℕ).1 ≤ x.1 :=
    fun x hx => (Rlp_gt x hx).le
  have cM' : cnf (translate (G ++ (v0, w1, w2) :: (R ++ [lp]))) := by
    have h : G ++ ((v0, w1, w2) :: R) ++ [lp] = G ++ (v0, w1, w2) :: (R ++ [lp]) := by
      simp
    rwa [h] at cM
  have cBlp : cnf (translate (((v0, w1, w2) :: R) ++ [lp])) := by
    rw [List.cons_append]
    exact cnf_tail rT G cM'
  have cCopies : cnf (translate (copies d0 d1 ((v0, w1, w2) :: R) (m + 1))) :=
    cnf_copies hR d0pos lead_lt lphd cBlp (m + 1)
  have argA : translate (R ++ shiftr01 d0 d1 (copies d0 d1 ((v0, w1, w2) :: R) m))
      <o translate (R ++ [lp]) := by
    have d := decr
    rw [st1, st2, olt_P_P] at d
    rcases d with h | ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, -, -, h⟩
    · omega
    · omega
    · exact h
    · exact absurd h (not_olt_Z Z)
  have leadle : ∃ p1 p2 b1 c1 q1 q2 b2 c2,
      translate ((v0, w1, w2)
        :: (R ++ shiftr01 d0 d1 (copies d0 d1 ((v0, w1, w2) :: R) m)))
        = P p1 p2 b1 c1
      ∧ translate ((v0, w1, w2) :: (R ++ [lp])) = P q1 q2 b2 c2
      ∧ P p1 p2 b1 Z ≤o P q1 q2 b2 Z := by
    refine ⟨w1, w2,
      translate (R ++ shiftr01 d0 d1 (copies d0 d1 ((v0, w1, w2) :: R) m)), Z,
      w1, w2, translate (R ++ [lp]), Z, ?_, ?_, Or.inl (olt_P_b _ _ _ _ argA)⟩
    · rw [← cpcons]
      exact st1
    · rw [← List.cons_append]
      exact st2
  have decr' : translate ((v0, w1, w2)
      :: (R ++ shiftr01 d0 d1 (copies d0 d1 ((v0, w1, w2) :: R) m)))
      <o translate ((v0, w1, w2) :: (R ++ [lp])) := by
    rw [← cpcons, ← List.cons_append]
    exact decr
  have cCopies' : cnf (translate ((v0, w1, w2)
      :: (R ++ shiftr01 d0 d1 (copies d0 d1 ((v0, w1, w2) :: R) m)))) := by
    rw [← cpcons]
    exact cCopies
  have r1 : ∀ x ∈ R ++ shiftr01 d0 d1 (copies d0 d1 ((v0, w1, w2) :: R) m),
      ((v0, w1, w2) : ℕ × ℕ × ℕ).1 ≤ x.1 := fun x hx => (tlgt x hx).le
  have key := cnf_ctx_cong cCopies' decr' rfl leadle r1 rT G cM'
  rw [cpcons]
  exact key

/-- **The uniform bad-branch decomposition.**  Under the row-1 descendance
hypothesis, `M` splits as `G ++ blk ++ [lp]` and `M⟦n⟧` as `G ++ copies`,
with the shift data of the three branches. -/
theorem oper_bad_blocks {M : TrioSeq} {n : ℕ} (L : 1 < M.length)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0))
    (hp : hasParent M (srow M (M.length - 1)) (M.length - 1))
    (_hn : 1 ≤ n)
    (hA : ∀ j, parent M (srow M (M.length - 1)) (M.length - 1) ≤ j →
      j < M.length - 1 →
      le1 M (parent M (srow M (M.length - 1)) (M.length - 1)) j ∨
      (if 1 < srow M (M.length - 1)
        then entry M 1 (M.length - 1)
          - entry M 1 (parent M (srow M (M.length - 1)) (M.length - 1))
        else 0) = 0) :
    ∃ (G : TrioSeq) (v0 w1 w2 : ℕ) (R : TrioSeq) (d0 d1 : ℕ) (lp : ℕ × ℕ × ℕ),
      M = G ++ ((v0, w1, w2) :: R) ++ [lp] ∧
      M⟦n⟧ = G ++ copies d0 d1 ((v0, w1, w2) :: R) n ∧
      (∀ x ∈ R, v0 < x.1) ∧
      v0 < lp.1 ∧
      ((d0 = 0 ∧ d1 = 0)
        ∨ (0 < d0 ∧ lp.1 = v0 + d0 ∧
            (w1 + d1 < lp.2.1 ∨ (w1 + d1 = lp.2.1 ∧ w2 < lp.2.2)))) := by
  have np : nextR M (srow M (M.length - 1))
      (parent M (srow M (M.length - 1)) (M.length - 1)) (M.length - 1) :=
    parent_nextR hp
  set j1 := M.length - 1 with hj1
  set i1 := srow M j1 with hi1
  set j0 := parent M i1 j1 with hj0
  have j0lt : j0 < j1 := nextR_index_lt np
  have chain : Relation.ReflTransGen (nextrel0 M) j0 j1 := nextR_chain0 np
  have iv : ∀ k, j0 < k → k ≤ j1 → entry M 0 j0 < entry M 0 k :=
    fun k h1 h2 => le0_interval_gt chain k ⟨h1, h2⟩
  set d0 := (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0) with hd0
  set d1 := (if 1 < i1 then entry M 1 j1 - entry M 1 j0 else 0) with hd1
  set R := (List.range' (j0 + 1) (j1 - (j0 + 1))).map (fun j => M.getD j (0, 0, 0))
    with hRdef
  set lp := M.getD j1 (0, 0, 0) with hlp
  have hsplit : List.range' j0 (j1 - j0) = j0 :: List.range' (j0 + 1) (j1 - (j0 + 1)) := by
    have h : j1 - j0 = (j1 - (j0 + 1)) + 1 := by omega
    rw [h, List.range'_succ]
  -- `M = take j0 ++ blk ++ [lp]`
  have hM' : M = M.take j0 ++ (((entry M 0 j0, entry M 1 j0, entry M 2 j0) :: R)
      ++ [lp]) := by
    have dropM : M.drop j0 = (((entry M 0 j0, entry M 1 j0, entry M 2 j0) :: R)
        ++ [lp]) := by
      rw [drop_eq_map_getD M j0 (0, 0, 0)]
      have hlen' : M.length - j0 = (j1 - j0) + 1 := by omega
      have hras : List.range' j0 ((j1 - j0) + 1)
          = List.range' j0 (j1 - j0) ++ [j1] := by
        have h := List.range'_append (s := j0) (m := j1 - j0) (n := 1) (step := 1)
        rw [List.range'_one] at h
        rw [show j0 + 1 * (j1 - j0) = j1 by omega] at h
        exact h.symm
      rw [hlen', hras, List.map_append, hsplit, List.map_cons, hRdef, hlp,
        getD_eq_entries]
      simp
    conv_lhs => rw [← List.take_append_drop j0 M]
    rw [dropM]
  -- `M⟦n⟧ = take j0 ++ copies`
  have hMn : M⟦n⟧ = M.take j0
      ++ copies d0 d1 ((entry M 0 j0, entry M 1 j0, entry M 2 j0) :: R) n := by
    rw [oper_bad_uniform n (by omega) hz hp hi1 hj0 hd0 hd1 (by
      intro j h1 h2
      exact hA j h1 h2)]
    congr 1
    unfold copies
    congr 1
    funext k
    show (List.range' j0 (j1 - j0)).map (fun j =>
        (entry M 0 j + k * d0, entry M 1 j + k * d1, entry M 2 j))
      = shiftr01 (k * d0) (k * d1)
          ((entry M 0 j0, entry M 1 j0, entry M 2 j0) :: R)
    rw [hsplit, List.map_cons, hRdef]
    unfold shiftr01
    rw [List.map_cons, List.map_map]
    rfl
  have R_gt : ∀ x ∈ R, entry M 0 j0 < x.1 := by
    intro x hx
    rw [hRdef] at hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i, hi, rfl⟩ := List.mem_range'.1 hj
    rw [getD_eq_entries]
    exact iv _ (by omega) (by omega)
  have lp_gt : entry M 0 j0 < lp.1 := by
    rw [hlp, getD_eq_entries]
    exact iv j1 j0lt le_rfl
  refine ⟨M.take j0, entry M 0 j0, entry M 1 j0, entry M 2 j0, R, d0, d1, lp,
    by conv_lhs => rw [hM']
       simp, hMn, R_gt, lp_gt, ?_⟩
  -- the shift disjunction
  by_cases hi : 0 < i1
  · right
    have d0pos : 0 < d0 := by
      rw [hd0, if_pos hi]
      have := iv j1 j0lt le_rfl
      omega
    have hd0eq : entry M 0 j1 = entry M 0 j0 + d0 := by
      rw [hd0, if_pos hi]
      have := iv j1 j0lt le_rfl
      omega
    refine ⟨d0pos, by rw [hlp, getD_eq_entries]; simpa using hd0eq, ?_⟩
    rw [hlp, getD_eq_entries]
    by_cases hi2 : 1 < i1
    · right
      have np2 : nextrel2 M j0 j1 := by
        have np' := np
        unfold nextR at np'
        rw [if_neg (by omega : ¬ i1 = 0), if_neg (by omega : ¬ i1 = 1)] at np'
        exact np'
      have h1lt : entry M 1 j0 < entry M 1 j1 :=
        rtg1_entry1_lt np2.2.2.2.2.1.2.2 (by omega)
      have hd1eq : d1 = entry M 1 j1 - entry M 1 j0 := by
        rw [hd1, if_pos hi2]
      constructor
      · simp only []
        omega
      · simpa using np2.2.2.2.1
    · left
      have i1eq : i1 = 1 := by omega
      have np1 : nextrel1 M j0 j1 := by
        have np' := np
        unfold nextR at np'
        rw [if_neg (by omega : ¬ i1 = 0), if_pos i1eq] at np'
        exact np'
      have hd1z : d1 = 0 := by
        rw [hd1, if_neg hi2]
      simp only [hd1z, Nat.add_zero]
      simpa using np1.2.2.2.1
  · left
    constructor
    · rw [hd0, if_neg hi]
    · rw [hd1, if_neg (by omega : ¬ 1 < i1)]

/-- **CNF is preserved by one expansion step, under the row-1 window bound**
(discharged on standard forms in the Column chapter). -/
theorem cnf_oper_of_window {M : TrioSeq} {n : ℕ} (hn : 1 ≤ n)
    (cM : cnf (translate M))
    (hwin : hasParent M (srow M (M.length - 1)) (M.length - 1) →
      1 < srow M (M.length - 1) →
      ∀ j, parent M (srow M (M.length - 1)) (M.length - 1) < j → j < M.length - 1 →
        entry M 1 (parent M (srow M (M.length - 1)) (M.length - 1)) < entry M 1 j) :
    cnf (translate (M⟦n⟧)) := by
  by_cases hL : M.length - 1 = 0
  · rw [oper_eq_self_of_short n hL]
    exact cM
  · have L1 : 1 < M.length := by omega
    have Mne : M ≠ [] := by
      intro he
      rw [he] at L1
      simp at L1
    have hPred : Pred M = M.dropLast := by
      unfold Pred
      rw [if_neg (by omega)]
    by_cases hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
        entry M 2 (M.length - 1) = 0
    · rw [oper_eq_pred_of_zero n hL hz, hPred]
      exact cnf_dropLast Mne cM
    · by_cases hp : hasParent M (srow M (M.length - 1)) (M.length - 1)
      · -- the row-1 descendance from the window bound
        have np := parent_nextR hp
        have j0lt : parent M (srow M (M.length - 1)) (M.length - 1) < M.length - 1 :=
          nextR_index_lt np
        have chain := nextR_chain0 np
        have hA : ∀ j, parent M (srow M (M.length - 1)) (M.length - 1) ≤ j →
            j < M.length - 1 →
            le1 M (parent M (srow M (M.length - 1)) (M.length - 1)) j ∨
            (if 1 < srow M (M.length - 1)
              then entry M 1 (M.length - 1)
                - entry M 1 (parent M (srow M (M.length - 1)) (M.length - 1))
              else 0) = 0 := by
          intro j h1 h2
          by_cases hi2 : 1 < srow M (M.length - 1)
          · left
            exact ⟨by omega, by omega,
              le1_window_desc (by omega) chain (hwin hp hi2) j h1 h2⟩
          · right
            rw [if_neg hi2]
        obtain ⟨G, v0, w1, w2, R, d0, d1, lp, Meq, Mneq, hR, lpv, disj⟩ :=
          oper_bad_blocks L1 hz hp hn hA
        have cM' : cnf (translate (G ++ ((v0, w1, w2) :: R) ++ [lp])) := Meq ▸ cM
        rw [Mneq]
        rcases disj with ⟨d0z, d1z⟩ | ⟨d0pos, lphd, lead_lt⟩
        · subst d0z
          subst d1z
          rw [copies_replicate]
          exact cnf_oper_i1eq0 hR lpv hn cM'
        · exact cnf_oper_asc hR d0pos lead_lt lphd hn cM'
      · rw [oper_eq_pred_of_noParent n hL hz hp, hPred]
        exact cnf_dropLast Mne cM

end Googology.Trans.BMS.TrioCof

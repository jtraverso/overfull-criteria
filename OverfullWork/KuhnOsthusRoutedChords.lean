module

public import OverfullWork.KuhnOsthusChordScheduling
public import OverfullWork.KuhnOsthusChordCandidates

@[expose] public section


/-! Realize the indexed positions of the chosen routes in physical
chord pairs, using the endpoint count of (8.2). -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V I J : Type*} [Fintype V] [Fintype J]

theorem chordSources_length (s : Equiv.Perm I) (a : I) (l : List I) :
    (chordSources s a l).length = l.length := by
  simp [chordSources]

theorem sum_positions_eq_count (l : List I) (i : I) :
    (∑ k : Fin l.length, if l[k.val] = i then (1:ℕ) else 0) = l.count i := by
  classical
  induction l with
  | nil => simp
  | cons v l ih =>
    simp only [List.length_cons]
    rw [Fin.sum_univ_succ]
    simp only [List.getElem_cons_succ,Fin.val_succ,List.count_cons,
      beq_iff_eq,ih,Nat.add_comm]
    rfl

/-- Count both endpoints of the physical arc requests carried by the
indexed positions in all reduced routes. -/
theorem chord_position_incidence_count (s : Equiv.Perm I) (a : J → I)
    (l : J → List I) (i : I) :
    let P := Σ j, Fin (l j).length
    let src (p : P) := s.symm ((a p.1 :: l p.1)[p.2.val]'(Nat.lt_succ_of_lt p.2.isLt))
    let dst (p : P) := (l p.1)[p.2.val]
    (univ.filter (fun p : P => src p = i)).card +
      (univ.filter (fun p : P => dst p = i)).card =
      ∑ j, ((chordSources s (a j) (l j)).count i + (l j).count i) := by
  classical
  dsimp only
  let P := Σ j, Fin (l j).length
  let src (p : P) := s.symm ((a p.1 :: l p.1)[p.2.val]'(Nat.lt_succ_of_lt p.2.isLt))
  let dst (p : P) := (l p.1)[p.2.val]
  simp only [card_filter]
  change ((∑ p : P, if src p = i then (1:ℕ) else 0) +
    (∑ p : P, if dst p = i then (1:ℕ) else 0)) = _
  rw [Fintype.sum_sigma,Fintype.sum_sigma]
  have hout (j : J) : (∑ k : Fin (l j).length, if src ⟨j,k⟩ = i then (1:ℕ) else 0) =
      (chordSources s (a j) (l j)).count i := by
    rw [←sum_positions_eq_count]
    let e := finCongr (chordSources_length s (a j) (l j)).symm
    apply Fintype.sum_equiv e
    intro k
    simp only [src,e,chordSources,List.getElem_map,List.getElem_dropLast]
    rfl
  have hin (j : J) : (∑ k : Fin (l j).length, if dst ⟨j,k⟩ = i then (1:ℕ) else 0) =
      (l j).count i := sum_positions_eq_count _ _
  simp only [hout,hin,←sum_add_distrib]

/-- After scheduling the cluster routes, obtain their physical arcs in
one pass through the restricted extender pairs. -/
theorem exists_physical_chords_for_routes [Fintype I] (R : Digraph I) (D : Digraph V)
    (s : Equiv.Perm I) (cluster : V → I) (a b : J → I) (l : J → List I)
    (hR : ∀ i, ¬ R.Adj i i)
    (hRoute : ∀ j, DirectedListRoutes.Route (reindexSources R s.symm) (a j) (b j) (l j))
    (A : I → Finset V) (m e : ℕ) (hm : 0 < m) (he : 50*e ≤ m)
    (hSize : ∀ i, 50*(A i).card = 24*m)
    (hClass : ∀ i x, x ∈ A i → cluster x = i)
    (hRect : ∀ i j, R.Adj i j → ∀ S ⊆ A i, ∀ T ⊆ A j,
      e < S.card → e < T.card → 0 < incidences D S T)
    (hInt : ∀ i, 100*(∑ j, chordInteriorLoad s (l j) i) ≤ m)
    (hFrom : ∀ i, 10*(∑ j, if s.symm (a j) = i then (1:ℕ) else 0) ≤ m)
    (hTo : ∀ i, 10*(∑ j, if b j = i then (1:ℕ) else 0) ≤ m) :
    ∃ f : (Σ j, Fin (l j).length) → V × V,
      (∀ p, (f p).1 ∈ A (s.symm ((a p.1 :: l p.1)[p.2.val]'(Nat.lt_succ_of_lt p.2.isLt))) ∧
        (f p).2 ∈ A ((l p.1)[p.2.val]) ∧ D.Adj (f p).1 (f p).2 ∧ (f p).1 ≠ (f p).2) ∧
      ∀ p q, p ≠ q → (f p).1 ≠ (f q).1 ∧ (f p).1 ≠ (f q).2 ∧
        (f p).2 ≠ (f q).1 ∧ (f p).2 ≠ (f q).2 := by
  classical
  let P := Σ j, Fin (l j).length
  have hIdx (p : P) : p.2.val < (a p.1 :: l p.1).length := by
    have := p.2.isLt
    simp only [List.length_cons]
    omega
  let src (p : P) := s.symm ((a p.1 :: l p.1)[p.2.val]'(hIdx p))
  let dst (p : P) := (l p.1)[p.2.val]
  have hEdge (p : P) : R.Adj (src p) (dst p) := by
    have hh := List.isChain_iff_getElem.mp (hRoute p.1).1 p.2.val
      (by simpa only [List.length_cons,Nat.add_lt_add_iff_right] using p.2.isLt)
    exact hh
  have hLoad (i : I) : 100*((univ.filter (fun p : P => src p = i)).card +
      (univ.filter (fun p : P => dst p = i)).card) ≤ 21*m := by
    rw [chord_position_incidence_count s a l i]
    exact chord_endpoint_budget R s a b l m hRoute hInt hFrom hTo i
  refine exists_physical_chords_of_restricted_pairs D cluster src dst A m e hm he
    (fun p => by have := hSize (src p); have := hSize (dst p); omega)
    (fun p => (hSize (src p)).ge) hClass ?_ (fun p => hRect _ _ (hEdge p)) hLoad
  intro p
  rw [disjoint_left]
  intro v hv hw
  have h := (hClass _ _ hv).symm.trans (hClass _ _ hw)
  exact hR _ (h.symm ▸ hEdge p)

end OverfullWork.DirectedRobustExpansion

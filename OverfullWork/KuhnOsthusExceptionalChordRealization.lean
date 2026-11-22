module

public import OverfullWork.KuhnOsthusRoutedChords

@[expose] public section


/-! Realization of the reduced chords while avoiding the previously
chosen exceptional endpoints, as in Kühn–Osthus Lemma 7.5(iii). -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical

/-- Chords on one style can be realized disjointly whenever the
available width pays for the rectangle cutoff and the load at both
ends. The fixed forbidden set contains the exceptional endpoints. -/
theorem exists_disjoint_exceptional_chord_edges {V I J : Type*} [Fintype V] [Fintype J]
    (G : Digraph V) (cluster : V → I) (source target : J → I)
    (A : I → Finset V) (F : Finset V) (load : I → ℕ) (w e : ℕ)
    (hClass : ∀ i v, v ∈ A i → cluster v = i)
    (hApart : ∀ j, source j ≠ target j)
    (hWidth : ∀ i, w ≤ ((A i) \ F).card)
    (hLoad : ∀ i, (univ.filter (fun j => source j = i)).card +
      (univ.filter (fun j => target j = i)).card ≤ load i)
    (hRoom : ∀ j, load (source j)+load (target j)+e < w)
    (hRect : ∀ j, ∀ S ⊆ A (source j), ∀ T ⊆ A (target j),
      e < S.card → e < T.card → 0 < incidences G S T) :
    ∃ f : J → V × V,
      (∀ j, (f j).1 ∈ A (source j) \ F ∧ (f j).2 ∈ A (target j) \ F ∧
        G.Adj (f j).1 (f j).2 ∧ (f j).1 ≠ (f j).2) ∧
      ∀ j k, j ≠ k →
        (f j).1 ≠ (f k).1 ∧ (f j).1 ≠ (f k).2 ∧
        (f j).2 ≠ (f k).1 ∧ (f j).2 ≠ (f k).2 := by
  classical
  choose B hB hCard using fun i => exists_subset_card_eq (hWidth i)
  have hCell (i : I) (v : V) (hv : v ∈ B i) : cluster v = i :=
    hClass i v (mem_sdiff.mp (hB i hv)).1
  have hD (j : J) : Disjoint (B (source j)) (B (target j)) :=
    disjoint_left.mpr fun _ hp hq => hApart j ((hCell _ _ hp).symm.trans (hCell _ _ hq))
  have hLocal (j : J) :=
    exists_physical_matching_of_rectangle_deficit G (B (source j)) (B (target j)) e
      ((hCard _).trans (hCard _).symm) (hD j) (fun X hX Y hY hx hy =>
        hRect j X (hX.trans ((hB _).trans sdiff_subset)) Y
          (hY.trans ((hB _).trans sdiff_subset)) hx hy)
  choose M hM hArcs hInj hOutj using hLocal
  obtain ⟨f,hf,hDis⟩ := exists_disjoint_chord_realization cluster source target M load
    (fun j z hz => ⟨hCell _ _ (hArcs j z hz).1,hCell _ _ (hArcs j z hz).2.1⟩)
    (fun j z hz => (hArcs j z hz).2.2.2) (fun j => ⟨hInj j,hOutj j⟩) hLoad (by
      intro j
      have h := hM j
      rw [hCard] at h
      have hr := hRoom j
      omega)
  refine ⟨f,fun j => ?_,hDis⟩
  obtain ⟨h₁,h₂,h₃,h₄⟩ := hArcs j (f j) (hf j).1
  exact ⟨hB _ h₁,hB _ h₂,h₃,h₄⟩

/-- The route incidence bound supplies the load for the actual chord
edges. Every realization avoids the prescribed exceptional endpoints. -/
theorem exists_exceptional_chord_edges_for_routes {V I J : Type*}
    [Fintype V] [Fintype I] [Fintype J]
    (R : Digraph I) (G : Digraph V) (s : Equiv.Perm I) (cluster : V → I)
    (a b : J → I) (l : J → List I) (A : I → Finset V) (F : Finset V)
    (w e interior endpoints : ℕ)
    (hR : ∀ i, ¬R.Adj i i)
    (hRoute : ∀ j, DirectedListRoutes.Route (reindexSources R s.symm) (a j) (b j) (l j))
    (hInt : ∀ i, (∑ j, chordInteriorLoad s (l j) i) ≤ interior)
    (hEnd : ∀ i, (∑ j, if s.symm (a j) = i then (1:ℕ) else 0) +
      (∑ j, if b j = i then (1:ℕ) else 0) ≤ endpoints)
    (hClass : ∀ i v, v ∈ A i → cluster v = i)
    (hWidth : ∀ i, w ≤ ((A i) \ F).card)
    (hRoom : 2*(interior+endpoints)+e < w)
    (hRect : ∀ i j, R.Adj i j → ∀ S ⊆ A i, ∀ T ⊆ A j,
      e < S.card → e < T.card → 0 < incidences G S T) :
    let P := Σ j, Fin (l j).length
    let src (p : P) := s.symm ((a p.1 :: l p.1)[p.2.val]'(Nat.lt_succ_of_lt p.2.isLt))
    let dst (p : P) := (l p.1)[p.2.val]
    ∃ f : P → V × V,
      (∀ p, (f p).1 ∈ A (src p) \ F ∧ (f p).2 ∈ A (dst p) \ F ∧
        G.Adj (f p).1 (f p).2 ∧ (f p).1 ≠ (f p).2) ∧
      ∀ p q, p ≠ q →
        (f p).1 ≠ (f q).1 ∧ (f p).1 ≠ (f q).2 ∧
        (f p).2 ≠ (f q).1 ∧ (f p).2 ≠ (f q).2 := by
  classical
  dsimp only
  let P := Σ j, Fin (l j).length
  let src (p : P) := s.symm ((a p.1 :: l p.1)[p.2.val]'(Nat.lt_succ_of_lt p.2.isLt))
  let dst (p : P) := (l p.1)[p.2.val]
  have hEdge (p : P) : R.Adj (src p) (dst p) := by
    have h := List.isChain_iff_getElem.mp (hRoute p.1).1 p.2.val
      (by simpa only [List.length_cons,Nat.add_lt_add_iff_right] using p.2.isLt)
    exact h
  have hLoad (i : I) : (univ.filter (fun p : P => src p = i)).card +
      (univ.filter (fun p : P => dst p = i)).card ≤ interior+endpoints := by
    rw [chord_position_incidence_count s a l i]
    have h := sum_le_sum (s := univ) (fun j _ =>
      chord_endpoint_load_le R s (a j) (b j) (l j) (hRoute j) i)
    simp only [sum_add_distrib] at h ⊢
    have hi := hInt i
    have he := hEnd i
    omega
  exact exists_disjoint_exceptional_chord_edges G cluster src dst A F
    (fun _ => interior+endpoints) w e hClass (fun p h => hR _ (h ▸ hEdge p))
    hWidth hLoad (fun _ => by omega) (fun p => hRect _ _ (hEdge p))

end OverfullWork.DirectedRobustExpansion

module

public import OverfullWork.ChenShanCoverDownRoundComposition
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

variable {V : Type*}

/-- Iterate the local transition while recording exactly the triangles
used before each level. The invariant can encode (4.22). -/
theorem iterate_cover_down_triangles
    (initial : Finset (V × V)) (l : ℕ) (Inv : ℕ → Finset (V × V) → Prop)
    (hInit : Inv 0 initial)
    (hStep : ∀ i < l, ∀ G, Inv i G →
      ∃ H : Finset (V × V), ∃ T : Finset (Finset (V × V)),
        H ⊆ G ∧ Inv (i+1) H ∧
        (↑T : Set (Finset (V × V))).PairwiseDisjoint id ∧
        (∀ t ∈ T, IsCoverDownTriangle t) ∧ coveredEdges T = G \ H) :
    ∃ L : Finset (V × V), ∃ T : Finset (Finset (V × V)),
      L ⊆ initial ∧ Inv l L ∧
      (↑T : Set (Finset (V × V))).PairwiseDisjoint id ∧
      (∀ t ∈ T, IsCoverDownTriangle t) ∧ coveredEdges T = initial \ L := by
  have hAt (i) (hi : i ≤ l) :
      ∃ G : Finset (V × V), ∃ T : Finset (Finset (V × V)),
        G ⊆ initial ∧ Inv i G ∧
        (↑T : Set (Finset (V × V))).PairwiseDisjoint id ∧
        (∀ t ∈ T, IsCoverDownTriangle t) ∧ coveredEdges T = initial \ G := by
    induction i with
    | zero =>
      exact ⟨initial,∅,Subset.rfl,hInit,by simp,by simp,by simp [coveredEdges]⟩
    | succ i ih =>
      obtain ⟨G,T,hG,hInv,hT,hCert,hCov⟩ := ih (by omega)
      obtain ⟨H,S,hH,hInv',hS,hCert',hCov'⟩ := hStep i (by omega) G hInv
      have hDisj : Disjoint (coveredEdges T) (coveredEdges S) := by
        rw [hCov,hCov']
        exact disjoint_left.mpr fun e he he' => (mem_sdiff.mp he).2 (mem_sdiff.mp he').1
      refine ⟨H,T ∪ S,hH.trans hG,hInv',packing_union_of_disjoint_covered hT hS hDisj,?_,?_⟩
      · intro t ht
        exact (mem_union.mp ht).elim (hCert t) (hCert' t)
      · rw [coveredEdges_union,hCov,hCov']
        ext e
        simp only [mem_union,mem_sdiff]
        constructor
        · rintro (⟨h₁,h₂⟩ | ⟨h₁,h₂⟩)
          · exact ⟨h₁,fun h => h₂ (hH h)⟩
          · exact ⟨hG h₁,h₂⟩
        · rintro ⟨hi,h⟩
          by_cases he : e ∈ G
          · exact Or.inr ⟨he,h⟩
          · exact Or.inl ⟨hi,he⟩
  exact hAt l le_rfl

/-- Attach the terminal absorber to the packing accumulated by the
iteration. The absorber is disjoint from the starting graph of Step 2. -/
theorem finish_cover_down_directed_absorption
    (initial absorber L : Finset (V × V))
    (hDisjoint : Disjoint absorber initial) (hL : L ⊆ initial)
    (T S : Finset (Finset (V × V)))
    (hT : (↑T : Set (Finset (V × V))).PairwiseDisjoint id)
    (hS : (↑S : Set (Finset (V × V))).PairwiseDisjoint id)
    (hCert : ∀ t ∈ T, IsCoverDownTriangle t) (hCert' : ∀ t ∈ S, IsCoverDownTriangle t)
    (hCov : coveredEdges T = initial \ L) (hCov' : coveredEdges S = absorber ∪ L) :
    let packed := T ∪ S
    (↑packed : Set (Finset (V × V))).PairwiseDisjoint id ∧
      (∀ t ∈ packed, IsCoverDownTriangle t) ∧ coveredEdges packed = initial ∪ absorber := by
  have hSep : Disjoint (coveredEdges T) (coveredEdges S) := by
    rw [hCov,hCov']
    apply disjoint_left.mpr
    intro e he he'
    have ⟨he₁,he₂⟩ := mem_sdiff.mp he
    exact (mem_union.mp he').elim (fun ha => disjoint_left.mp hDisjoint ha he₁) he₂
  intro packed
  refine ⟨packing_union_of_disjoint_covered hT hS hSep,?_,?_⟩
  · intro t ht
    exact (mem_union.mp ht).elim (hCert t) (hCert' t)
  · change coveredEdges (T ∪ S) = _
    rw [coveredEdges_union,hCov,hCov']
    ext e
    simp only [mem_union,mem_sdiff]
    constructor
    · rintro (⟨h,_⟩ | (h | h))
      · exact Or.inl h
      · exact Or.inr h
      · exact Or.inl (hL h)
    · rintro (h | h)
      · by_cases he : e ∈ L
        · exact Or.inr (Or.inr he)
        · exact Or.inl ⟨h,he⟩
      · exact Or.inr (Or.inl h)

/-- The transition preserves the full induced graph of the protected
level and transfers the matching degree bound to the loss in (4.22). -/
theorem cover_down_transition_degree_invariant
    (original current M : Finset (V × V)) (U K : Finset V)
    (hK : K ⊆ U) (hFull : current ∩ (U ×ˢ U) = original ∩ (U ×ˢ U))
    (hM : M ⊆ (current ∩ (U ×ˢ U)) \ (K ×ˢ K))
    (bound : ℝ) (hDegree : ∀ v, (incidentDegree M v : ℝ) ≤ bound) :
    let next := (current ∩ (U ×ˢ U)) \ M
    next ⊆ current ∧ next ⊆ original ∩ (U ×ˢ U) ∧
    next ∩ (K ×ˢ K) = original ∩ (K ×ˢ K) ∧
    ∀ v, (incidentDegree (prefixLostArcs original next U) v : ℝ) ≤ bound := by
  intro next
  have hM' : M ⊆ current ∩ (U ×ˢ U) := hM.trans sdiff_subset
  have hSep : Disjoint M (K ×ˢ K) :=
    disjoint_left.mpr fun e he hk => (mem_sdiff.mp (hM he)).2 hk
  have ⟨hKeep,hLost⟩ := protected_iteration_update original current M U K hK hFull hM' hSep
  have hSub : next ⊆ current ∩ (U ×ˢ U) := sdiff_subset
  refine ⟨hSub.trans inter_subset_left,?_,hKeep,?_⟩
  · rw [← hFull]
    exact hSub
  · intro v
    unfold prefixLostArcs
    change (incidentDegree ((original ∩ (U ×ˢ U)) \ next) v : ℝ) ≤ _
    rw [hLost]
    exact hDegree v

/- The decomposition returned by the absorber uses the same directed
triangle certificates as the packing used by Step 2. -/
theorem cover_down_packing_of_decomposition
    {A B W : Type*} [Fintype A] [Fintype B] [Fintype W]
    {E : A → B → Prop} {P : A → W → Prop} {Q : B → W → Prop}
    (D : TripartiteTriangleDecomposition E P Q) :
    ∃ T : Finset (Finset (OrientedTripartiteEdge A B W)),
      (↑T : Set (Finset (OrientedTripartiteEdge A B W))).PairwiseDisjoint id ∧
      (∀ t ∈ T, IsCoverDownTriangle t) ∧ coveredEdges T = tripartiteArcs E P Q := by
  let S : Finset (A × B × W) := univ.filter (fun t => D.triangle t.1 t.2.1 t.2.2)
  have hMem (a : A) (b : B) (w : W) : (a,b,w) ∈ S ↔ D.triangle a b w := by
    simp only [S,mem_filter,mem_univ,true_and]
  let T := triangleHypergraph S
  refine ⟨T,?_,triangleHypergraph_cover_down_certificate S,?_⟩
  · intro t ht t' ht' hne
    obtain ⟨⟨a,b,w⟩,ha,rfl⟩ := mem_map.mp ht
    obtain ⟨⟨a',b',w'⟩,hb,rfl⟩ := mem_map.mp ht'
    change triangleEdges (a,b,w) ≠ triangleEdges (a',b',w') at hne
    apply disjoint_left.mpr
    intro e he he'
    change e ∈ triangleEdges (a,b,w) at he
    change e ∈ triangleEdges (a',b',w') at he'
    simp only [triangleEdges,mem_insert,mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · have heq : a = a' ∧ b = b' := by
        simpa [triangleEdges,Prod.mk.injEq] using he'
      obtain ⟨rfl,rfl⟩ := heq
      obtain ⟨c,_,hc⟩ := D.coversBase a b (D.supported a b w ((hMem a b w).mp ha)).1
      have hww := (hc w ((hMem a b w).mp ha)).trans (hc w' ((hMem a b w').mp hb)).symm
      exact hne (by rw [hww])
    · have heq : b = b' ∧ w = w' := by
        simpa [triangleEdges,Prod.mk.injEq] using he'
      obtain ⟨rfl,rfl⟩ := heq
      obtain ⟨c,_,hc⟩ := D.coversRight b w (D.supported a b w ((hMem a b w).mp ha)).2.2
      have haa := (hc a ((hMem a b w).mp ha)).trans (hc a' ((hMem a' b w).mp hb)).symm
      exact hne (by rw [haa])
    · have heq : w = w' ∧ a = a' := by
        simpa [triangleEdges,Prod.mk.injEq] using he'
      obtain ⟨rfl,rfl⟩ := heq
      obtain ⟨c,_,hc⟩ := D.coversLeft a w (D.supported a b w ((hMem a b w).mp ha)).2.1
      have hbb := (hc b ((hMem a b w).mp ha)).trans (hc b' ((hMem a b' w).mp hb)).symm
      exact hne (by rw [hbb])
  · ext ⟨x,y⟩
    constructor
    · intro he
      obtain ⟨t,ht,he⟩ := mem_coveredEdges.mp he
      obtain ⟨⟨a,b,w⟩,ha,rfl⟩ := mem_map.mp ht
      exact triangleEdges_subset_tripartiteArcs (D.supported a b w ((hMem a b w).mp ha)) he
    · intro he
      have h := (mem_filter.mp he).2
      have hTri (a : A) (b : B) (w : W) (h : D.triangle a b w) :
          triangleEdges (a,b,w) ∈ T := mem_map.mpr ⟨_,(hMem a b w).mpr h,rfl⟩
      rcases x with a | (b | w) <;> rcases y with a' | (b' | w') <;>
        first | exact False.elim h |
          (obtain ⟨w,hw,_⟩ := D.coversBase a b' h
           exact mem_coveredEdges.mpr ⟨_,hTri a b' w hw,by simp [triangleEdges]⟩) |
          (obtain ⟨a,ha,_⟩ := D.coversRight b w' h
           exact mem_coveredEdges.mpr ⟨_,hTri a b w' ha,by simp [triangleEdges]⟩) |
          (obtain ⟨b,hb,_⟩ := D.coversLeft a' w h
           exact mem_coveredEdges.mpr ⟨_,hTri a' b w hb,by simp [triangleEdges]⟩)

end OverfullWork.ChenShan

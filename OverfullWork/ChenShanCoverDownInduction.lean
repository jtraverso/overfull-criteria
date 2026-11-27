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

end OverfullWork.ChenShan

module

public import OverfullWork.CMSOperation41ProjectionSplit

@[expose] public section


/-! Realize the degree and colouring demands of a prescribed round
using its part of the simultaneous core packing. Its parity can be
checked before the flexible paths are chosen. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph DirectedSpanningConfiguration DirectedRobustExpansion
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge

variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C]

set_option maxHeartbeats 1600000 in
theorem realized_prescription_is_two_colour_layer_with_gap_balance (G : SimpleGraph V) {n : ℕ}
    (e : C ↪ V) (hn : 2 ≤ n+1) (w : Fin (n+1) ↪ C)
    (fixed : Finset (Fin (n+1))) (isolated : Finset C)
    {J : SimpleGraph C} {D : Digraph C} (hOr : IsOrientationOf D J)
    (P : Realization D (cyclicLayout hn w fixed isolated)) (hIso : ∀ i,w i ∉ isolated)
    (hHost : ∀ u v,D.Adj u v → G.Adj (e u) (e v))
    (external : Fin (n+1) → List V) (gaps : Finset (Sym2 V)) (F : SimpleGraph V)
    (hF : ∀ a b,F.Adj a b ↔ s(a,b) ∉ gaps ∧
      ∃ i ∈ fixed,List.IsInfix [a,b] (e (w i) :: external i ++ [e (w (finRotate (n+1) i))]) ∨
        List.IsInfix [b,a] (e (w i) :: external i ++ [e (w (finRotate (n+1) i))]))
    (hFixedPath : ∀ i ∈ fixed,(e (w i) :: external i ++ [e (w (finRotate (n+1) i))]).IsChain
      (fun a b => G.Adj a b ∨ s(a,b) ∈ gaps))
    (hFixedSimple : ∀ i ∈ fixed,(e (w i) :: external i).Nodup)
    (hFixedOutside : ∀ i ∈ fixed,∀ v,v ∈ external i → v ∉ Set.range e)
    (hFixedDisjoint : ∀ i ∈ fixed,∀ j ∈ fixed,i ≠ j → List.Disjoint (external i) (external j)) :
    let length := Fintype.card C-isolated.card+(∑ i ∈ fixed,(external i).length)
    let L := ((hostEdges J P.used).map e).deleteEdges (gaps : Set (Sym2 V))
    let Q := F ⊔ L
    3 ≤ length →
    (Even length ∨ ∃ i ∈ fixed,∃ a b,s(a,b) ∈ gaps ∧
      List.IsInfix [a,b] (e (w i) :: external i ++ [e (w (finRotate (n+1) i))])) →
    Q ≤ G ∧ Q.EdgeColorable 2 ∧ (∀ v,Q.degree v ≤ 2) ∧
      (∀ v,v ∉ isolated → (∀ u,s(e v,u) ∉ gaps) → Q.degree (e v) = 2) ∧
      (∀ v ∈ isolated,Q.degree (e v) = 0) ∧
      ((∀ edge ∈ gaps,∃ i ∈ fixed,∃ a b,edge = s(a,b) ∧
        List.IsInfix [a,b] (e (w i) :: external i ++ [e (w (finRotate (n+1) i))])) →
      ∀ v,Q.degree v+(trimmingGapGraph gaps).degree v =
        if (∃ u ∉ isolated,e u = v) ∨ (∃ i ∈ fixed,v ∈ external i) then 2 else 0) := by
  intro length L Q hLength hParity
  have hEq := realized_replacement_length e hn w fixed isolated P hIso external
  have hSize : 3 ≤ n+1+(∑ i,(realizedReplacementInterior e fixed P.interior external i).length) := by
    rw [hEq]
    exact hLength
  have hParity' : Even (n+1+∑ i,(realizedReplacementInterior e fixed P.interior external i).length) ∨
      ∃ i ∈ fixed,∃ a b,s(a,b) ∈ gaps ∧
        List.IsInfix [a,b] (e (w i) :: external i ++ [e (w (finRotate (n+1) i))]) := by
    rw [hEq]
    exact hParity
  obtain ⟨Q',hLe,hTwo,hDeg,hOrd,hZero,hEdge,hBalance⟩ :=
    physical_layer_of_realized_replacements G e hn w fixed isolated P hIso hHost external gaps
      hFixedPath hFixedSimple hFixedOutside hFixedDisjoint hSize hParity'
  have hShape : Q' = Q :=
    physical_layer_eq_prescribed_sup_host e hn w fixed isolated hOr P external gaps F Q' hF hEdge
  subst Q'
  refine ⟨hLe,hTwo,hDeg,hOrd,hZero,?_⟩
  intro hGap v
  by_cases h : (∃ u ∉ isolated,e u = v) ∨ (∃ i ∈ fixed,v ∈ external i)
  · simpa only [if_pos h] using hBalance hGap v
  · simpa only [if_neg h] using hBalance hGap v

theorem realized_prescription_is_two_colour_layer (G : SimpleGraph V) {n : ℕ}
    (e : C ↪ V) (hn : 2 ≤ n+1) (w : Fin (n+1) ↪ C)
    (fixed : Finset (Fin (n+1))) (isolated : Finset C)
    {J : SimpleGraph C} {D : Digraph C} (hOr : IsOrientationOf D J)
    (P : Realization D (cyclicLayout hn w fixed isolated)) (hIso : ∀ i,w i ∉ isolated)
    (hHost : ∀ u v,D.Adj u v → G.Adj (e u) (e v))
    (external : Fin (n+1) → List V) (gaps : Finset (Sym2 V)) (F : SimpleGraph V)
    (hF : ∀ a b,F.Adj a b ↔ s(a,b) ∉ gaps ∧
      ∃ i ∈ fixed,List.IsInfix [a,b] (e (w i) :: external i ++ [e (w (finRotate (n+1) i))]) ∨
        List.IsInfix [b,a] (e (w i) :: external i ++ [e (w (finRotate (n+1) i))]))
    (hFixedPath : ∀ i ∈ fixed,(e (w i) :: external i ++ [e (w (finRotate (n+1) i))]).IsChain
      (fun a b => G.Adj a b ∨ s(a,b) ∈ gaps))
    (hFixedSimple : ∀ i ∈ fixed,(e (w i) :: external i).Nodup)
    (hFixedOutside : ∀ i ∈ fixed,∀ v,v ∈ external i → v ∉ Set.range e)
    (hFixedDisjoint : ∀ i ∈ fixed,∀ j ∈ fixed,i ≠ j → List.Disjoint (external i) (external j)) :
    let length := Fintype.card C-isolated.card+(∑ i ∈ fixed,(external i).length)
    let L := ((hostEdges J P.used).map e).deleteEdges (gaps : Set (Sym2 V))
    let Q := F ⊔ L
    3 ≤ length →
    (Even length ∨ ∃ i ∈ fixed,∃ a b,s(a,b) ∈ gaps ∧
      List.IsInfix [a,b] (e (w i) :: external i ++ [e (w (finRotate (n+1) i))])) →
    Q ≤ G ∧ Q.EdgeColorable 2 ∧ (∀ v,Q.degree v ≤ 2) ∧
      (∀ v,v ∉ isolated → (∀ u,s(e v,u) ∉ gaps) → Q.degree (e v) = 2) ∧
      ∀ v ∈ isolated,Q.degree (e v) = 0 := by
  intro length L Q hLength hParity
  obtain ⟨hLe,hTwo,hDeg,hOrd,hZero,_⟩ :=
    realized_prescription_is_two_colour_layer_with_gap_balance G e hn w fixed isolated hOr P hIso
      hHost external gaps F hF hFixedPath hFixedSimple hFixedOutside hFixedDisjoint hLength hParity
  exact ⟨hLe,hTwo,hDeg,hOrd,hZero⟩

theorem packed_core_edges_le_global_usage {K : Type*} {I : K → Type*} {J : SimpleGraph C}
    {L : ∀ k,Layout C (I k)} (P : CMSPacking I J L) (k : K) :
    hostEdges J (P.configuration k).used ≤ hostEdges J P.used := by
  intro u v h
  exact ⟨h.1,h.2.elim (fun he => Or.inl (Digraph.iSup_adj.mpr ⟨k,he⟩))
    (fun he => Or.inr (Digraph.iSup_adj.mpr ⟨k,he⟩))⟩

end OverfullWork.CMSTrimmingRound

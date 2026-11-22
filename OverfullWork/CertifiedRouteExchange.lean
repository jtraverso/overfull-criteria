module

public import OverfullWork.CrossingIncidenceAccounting

@[expose] public section


/-! # Actual recoloring of either certified CMS alternating path

The resulting partial coloring is constructed by the existing legal
copy exchange, with removed/added copy graphs derived from the route.
All displayed bookkeeping conclusions are proved for that same result.
-/
namespace SimpleGraph.MultiGraph.PartialColouring
open SimpleGraph Finset OverfullWork.PairedRoutes
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}
set_option maxHeartbeats 24000000

theorem exchange_alternating_certificate (P : M.PartialColouring k) (A E : Finset V) (h : ℕ) (i : Fin k)
    (a b : V) (hab : a ≠ b) (ha : (P.colouring.colourGraph i).degree a=0)
    (hb : (P.colouring.colourGraph i).degree b=0) (q : M.supportGraph.Walk a b) (hq : q.IsPath)
    (hc : AlternatingCertificate
      ((P.colouring.colourGraph i).matchingPartner (P.colouring.colourGraph_degree_le_one i))
      (P.available.crossingSupport A) ((P.colouring.colourGraph i).goodMatching (P.available.internalPart A) A h).supportGraph
      (univ\(P.colouring.colourGraph i).residueForbidden (P.colouring.colourGraph_degree_le_one i)
        (P.available.internalPart A) A E h) a b q.support) :
    ∃ Q : M.PartialColouring k, ∃ T : MultiGraph V,
      Q.graph.edgeCount=P.graph.edgeCount+1 ∧
      (∀ v, Q.graph.degree v=P.graph.degree v+(if v=a then 1 else 0)+(if v=b then 1 else 0)) ∧
      (∀ v, (Q.colouring.colourGraph i).degree v=(P.colouring.colourGraph i).degree v+
        (if v=a then 1 else 0)+(if v=b then 1 else 0)) ∧
      (∀ j, j ≠ i → Q.colouring.colourGraph j=P.colouring.colourGraph j) ∧
      Q.colouring.missingSet univ i=((P.colouring.missingSet univ i).erase a).erase b ∧
      (P.colouring.missingSet univ i).card=(Q.colouring.missingSet univ i).card+2 ∧
      (∑ v, (P.colouring.missingPalette v).card)=(∑ v, (Q.colouring.missingPalette v).card)+2 ∧
      T.edgeCount=q.length/2 ∧ (∀ v, T.degree v ≤ 1) ∧
      (∀ e, T.mult e ≤ ((P.colouring.colourGraph i).goodMatching (P.available.internalPart A) A h).mult e) ∧
      Q.available.internalPart A=(P.available.internalPart A).addCopies T ∧
      (∀ v ∈ E, (Q.available.internalPart A).degree v=(P.available.internalPart A).degree v) ∧
      ((∀ v, (P.available.internalPart A).degree v ≤ h) → ∀ v, (Q.available.internalPart A).degree v ≤ h) ∧
      ∀ v, Q.graph.crossDegree A v+(Q.colouring.missingPalette v).card+(P.available.internalPart A).degree v=
        P.graph.crossDegree A v+(P.colouring.missingPalette v).card+(Q.available.internalPart A).degree v := by
  obtain ⟨s,hGood,hAdded,hProtected,hLength⟩ :=
    P.route_input_of_certificate A E h i a b hab ha hb q hq hc
  have hRemoved : ∀ x y, ¬(x ∈ A ↔ y ∈ A) → s.removed.mult s(x,y)=0 := by
    intro x y hxy
    have hh := hGood s(x,y)
    rw [goodMatching_internal _ _ _ _ x y hxy] at hh
    omega
  refine ⟨s.result,s.removed,s.size_change,s.degree_change,s.selected_degree_change,s.other_colour,s.missingSet_exact,
    s.missing_drop_two,s.total_missing_drop,?_,s.removed_matching,hGood,
    s.internal_residue A hRemoved hAdded,?_,?_,s.crossing_residue_telescope A hRemoved hAdded⟩
  · have hh := s.removed_count
    omega
  · intro v hv
    exact s.internal_residue_protected A hRemoved hAdded v (hProtected v hv)
  · exact s.internal_residue_cap A h hGood hAdded

end SimpleGraph.MultiGraph.PartialColouring

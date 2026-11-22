module

public import OverfullWork.CaseTwoProtectedGeometry
public import OverfullWork.AnchoredCentreRun
public import OverfullWork.LowSetEdgePreprocessing

@[expose] public section


/-! # Actual ordinary-neighbor reserve at the second anchor

The degree/support profile and the constructed cut discrepancy pay for
ordinary crossing neighbors. The first protected run colors no such
copy. The numerical nonheavy-pair gap is stated explicitly, rather than
postulating available choices or a second-anchor coloring.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun PrunedCore
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T : ℕ} {η : ℝ} {b w : Fin (p.pairIndex+1) × Bool}
variable {s : p.CaseTwoPartition P T η b}
set_option maxHeartbeats 16000000

theorem Candidate.CaseTwoPartition.second_ordinary_neighbour_bound
    (s : p.CaseTwoPartition P T η b) :
    (G.maxDegree:ℝ) <
      2*((p.completed.neighboursInto (s.part.erase p.centre) b).card:ℝ)+
        (p.completed.mult s(p.centre,b):ℝ)+(B:ℝ)+η*(p.pairIndex+1:ℕ)+2 := by
  have hb : b ≠ p.centre := by intro he;exact s.second_not_mem (he ▸ s.centre_mem)
  have hProfile := p.completed_neighbour_profile b hb
  have hSplit := LowSetEdgePreprocessing.neighboursIn_add_compl p.completed.supportGraph s.part b
  have hDis := (abs_lt.mp (s.simple_discrepancy b)).1
  have hCard : neighboursIn p.completed.supportGraph s.part b ≤
      (p.completed.neighboursInto (s.part.erase p.centre) b).card+1 := by
    rw [RobustExpansion.neighboursIn_eq_filter_card]
    have hs : s.part.filter (fun v => p.completed.supportGraph.Adj b v) ⊆
        insert p.centre (p.completed.neighboursInto (s.part.erase p.centre) b) := by
      intro v hv
      have hh := mem_filter.mp hv
      by_cases ha : v=p.centre
      · exact mem_insert.mpr (Or.inl ha)
      · exact mem_insert.mpr (Or.inr (mem_filter.mpr ⟨mem_erase.mpr ⟨ha,hh.1⟩,hh.2⟩))
    exact (card_le_card hs).trans (card_insert_le _ _)
  have hProfileR : (G.maxDegree:ℝ) ≤ (p.completed.supportGraph.degree b:ℝ)+
      (p.completed.mult s(p.centre,b):ℝ)+(B:ℝ) := by exact_mod_cast hProfile
  have hSplitR : (neighboursIn p.completed.supportGraph s.part b:ℝ)+
      (neighboursIn p.completed.supportGraph s.partᶜ b:ℝ)=p.completed.supportGraph.degree b := by
    exact_mod_cast hSplit
  have hCardR : (neighboursIn p.completed.supportGraph s.part b:ℝ) ≤
      (p.completed.neighboursInto (s.part.erase p.centre) b).card+1 := by exact_mod_cast hCard
  linarith

theorem Candidate.CaseTwoMiddleCopies.protected_run_free_eq
    (r : p.CaseTwoMiddleCopies s w) (C : r.graph.EdgeColoring r.seedPalette)
    {Q : p.completed.PartialColouring r.seedPalette} {n t : ℕ}
    (hRun : MultiGraph.PartialColouring.ProtectedRun p.centre b w (r.partialSeed C) Q n t) :
    Q.ordinaryFree s.part p.centre b=p.completed.neighboursInto (s.part.erase p.centre) b := by
  ext v
  simp only [MultiGraph.PartialColouring.ordinaryFree,MultiGraph.neighboursInto,mem_filter]
  by_cases hv : v ∈ s.part.erase p.centre
  · have hb : b ≠ p.centre := by intro he;exact s.second_not_mem (he ▸ s.centre_mem)
    have hz := r.protected_run_away_crossing_zero C hRun b v hb (mem_erase.mp hv).1
      (by simp only [s.second_not_mem,(mem_erase.mp hv).2,false_iff,not_true_eq_false,not_false_eq_true])
    change (v ∈ s.part.erase p.centre ∧ 0 < p.completed.mult s(b,v)-Q.graph.mult s(b,v)) ↔ _
    rw [hz,Nat.sub_zero]
  · simp only [hv,false_and]

theorem Candidate.CaseTwoMiddleCopies.second_anchor_reserve
    (r : p.CaseTwoMiddleCopies s w) (C : r.graph.EdgeColoring r.seedPalette)
    {Q : p.completed.PartialColouring r.seedPalette} {n t : ℕ}
    (hRun : MultiGraph.PartialColouring.ProtectedRun p.centre b w (r.partialSeed C) Q n t)
    (hMissing : ((Q.colouring.missingPalette b).card:ℝ) <
      3*(η*(p.pairIndex+1:ℕ)+4*(B:ℝ)+((p.pairIndex+1)/T:ℕ)+6*(T:ℝ)+9))
    (hGap : (p.completed.mult s(p.centre,b):ℝ)+(B:ℝ)+η*(p.pairIndex+1:ℕ)+
      6*(η*(p.pairIndex+1:ℕ)+4*(B:ℝ)+((p.pairIndex+1)/T:ℕ)+6*(T:ℝ)+9)+4 ≤ G.maxDegree) :
    (Q.colouring.missingPalette b).card+1 ≤ (Q.ordinaryFree s.part p.centre b).card := by
  rw [r.protected_run_free_eq C hRun]
  have hBound := s.second_ordinary_neighbour_bound
  have hResult : ((Q.colouring.missingPalette b).card:ℝ)+1 ≤
      (p.completed.neighboursInto (s.part.erase p.centre) b).card := by linarith
  exact_mod_cast hResult

end OverfullWork.NormalizedCanonicalCandidate

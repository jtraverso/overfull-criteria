module

public import OverfullWork.ClassTwoCleanupRound

@[expose] public section


/-! # Propagating the light-pair bound through top-pair removal

An unselected pair heavier than the new threshold would be dominated by
the selected top pair, forcing total complementary degree at least
2Delta+2. The explicit total-degree bound rules this out. This argument
does not require criticality or a degree order between the two sides.
-/
namespace OverfullWork.ClassTwoMatchingRound
open SimpleGraph Finset PaperTopDegreeMatching
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 5000000

theorem CoreRound.light_pairs_after_round {G : SimpleGraph V} [DecidableRel G.Adj]
    {X : Finset V} {x y z : V} (r : CoreRound G X x y z)
    (hTop : IsTopPair G Xᶜ y z) (hD : 0<G.maxDegree)
    (hPairs : ∀u∈Xᶜ,∀v∈Xᶜ,u≠v → G.degree u+G.degree v<G.maxDegree+2)
    (hTotal : (∑w∈Xᶜ,G.degree w)≤2*G.maxDegree+1) :
    ∀u∈Xᶜ,∀v∈Xᶜ,u≠v →
      (G\r.matching).degree u+(G\r.matching).degree v<(G\r.matching).maxDegree+2 := by
  intro u hu v hv huv
  have hU:(G\r.matching).degree u+r.matching.degree u=G.degree u:=by
    simpa only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
      MaximumMatching.degree_sdiff_add_of_le G r.matching r.le_original u
  have hV:(G\r.matching).degree v+r.matching.degree v=G.degree v:=by
    simpa only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
      MaximumMatching.degree_sdiff_add_of_le G r.matching r.le_original v
  rw [r.complementary_degrees u hu] at hU
  rw [r.complementary_degrees v hv] at hV
  rw [r.residual_maxDegree]
  have hOld:=hPairs u hu v hv huv
  by_cases huSel:u=y ∨ u=z
  · rw [if_pos huSel] at hU
    split_ifs at hV <;>omega
  · rw [if_neg huSel] at hU
    by_cases hvSel:v=y ∨ v=z
    · rw [if_pos hvSel] at hV
      omega
    · rw [if_neg hvSel] at hV
      have huRest:u∈(Xᶜ.erase y).erase z:=by
        simp only [mem_erase]
        exact ⟨fun he=>huSel (Or.inr he),fun he=>huSel (Or.inl he),hu⟩
      have hvRest:v∈(Xᶜ.erase y).erase z:=by
        simp only [mem_erase]
        exact ⟨fun he=>hvSel (Or.inr he),fun he=>hvSel (Or.inl he),hv⟩
      have hPair:=CriticalAlmostPairNormalization.pair_degree_sum_le G ((Xᶜ.erase y).erase z) u v huRest hvRest huv
      have hSumY:=sum_erase_add Xᶜ (fun w=>G.degree w) hTop.left_mem
      have hSumZ:=sum_erase_add (Xᶜ.erase y) (fun w=>G.degree w)
        (mem_erase.mpr ⟨hTop.ne.symm,hTop.right_mem⟩)
      have hRankU:=hTop.maximum u hu
      have hRankV:=hTop.second v hv (fun he=>hvSel (Or.inl he))
      omega

end OverfullWork.ClassTwoMatchingRound

namespace OverfullWork.ClassTwoCleanupRound
open SimpleGraph Finset ClassTwoMatchingRound
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 5000000

theorem CleanRound.light_pairs {G : SimpleGraph V} [DecidableRel G.Adj]
    {X : Finset V} (s : CleanRound G X)
    (hPairs : ∀u∈Xᶜ,∀v∈Xᶜ,u≠v → G.degree u+G.degree v<G.maxDegree+2)
    (hTotal : (∑w∈Xᶜ,G.degree w)≤2*G.maxDegree+1) :
    ∀u∈Xᶜ,∀v∈Xᶜ,u≠v → s.graph.degree u+s.graph.degree v<s.graph.maxDegree+2 := by
  intro u hu v hv huv
  have hPair:=s.round.light_pairs_after_round s.top (by have hh:=s.anchor_nonmaximum;omega) hPairs hTotal u hu v hv huv
  have hULe:=s.graph.degree_le_of_le s.le_residue (v:=u)
  have hVLe:=s.graph.degree_le_of_le s.le_residue (v:=v)
  have hMax:=s.maximum
  have hRMax:=s.round.residual_maxDegree
  simp only [SimpleGraph.maxDegree,←SimpleGraph.card_neighborSet_eq_degree,
    ←Nat.card_eq_fintype_card] at hPair hULe hVLe hMax hRMax ⊢
  omega

end OverfullWork.ClassTwoCleanupRound

module

public import OverfullWork.MaximumMatchingComponentGeometry
public import OverfullWork.MaximumOddCutPacking

@[expose] public section


/-! # No overfull subgraph supplies a matching covering every maximum vertex

Odd components consisting of maximum vertices pay at least Delta edges to
the deleted set. The low vertices form a single clique in the even
augmentation; exact parity removes its possible additional odd component.
No preservation of no-overfullness after deleting the matching is claimed.
-/
namespace OverfullWork.MaximumMatching
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 3000000

theorem highOddComponents_card_le_deleted (G : SimpleGraph V) [DecidableRel G.Adj]
    (hD : 0<G.maxDegree) (hno : ¬G.HasOverfullSubgraph) (U : Set (AugType V)) :
    (highOddComponents (augmentation G) {z | Low G z} U).card≤U.ncard := by
  classical
  let I:=↥(highOddComponents (augmentation G) {z | Low G z} U)
  let S : I → Finset V:=fun C => oldComponentSet G U C.val
  have hbound:=MaximumOddCutPacking.card_le_boundary G hD hno S (deletedOld G U)
    (fun C => oldComponentSet_odd G U C.val C.property)
    (fun C => oldComponentSet_all_maximum G U C.val C.property)
    (fun C D hne => oldComponentSet_disjoint G U C.val D.val
      (fun he => hne (Subtype.ext he)))
    (fun C => oldComponentSet_disjoint_deletedOld G U C.val)
    (fun C => oldComponentSet_boundary G U C.val)
  have hI : Fintype.card I=(highOddComponents (augmentation G) {z | Low G z} U).card :=
    Fintype.card_coe _
  rw [hI] at hbound
  exact hbound.trans (card_deletedOld_le G U)

/-- Tutte is discharged from graph edge counts, including the parity correction. -/
theorem augmentation_has_perfectMatching (G : SimpleGraph V) [DecidableRel G.Adj]
    (hD : 0<G.maxDegree) (hno : ¬G.HasOverfullSubgraph) :
    ∃P : (augmentation G).Subgraph,P.IsPerfectMatching := by
  apply exists_perfectMatching_of_high_components_bound (augmentation G) {z | Low G z}
    even_card_augType
  · intro x hx y hy hne
    exact low_clique G hne hx hy
  · exact highOddComponents_card_le_deleted G hD hno

/-- A genuine graph matching saturates every vertex of actual maximum degree. -/
theorem exists_matching_covering_maximum_of_no_overfull (G : SimpleGraph V)
    [DecidableRel G.Adj] (hD : 0<G.maxDegree) (hno : ¬G.HasOverfullSubgraph) :
    ∃M : SimpleGraph V,M≤G ∧ OneFactor.IsMatchingGraph M ∧
      ∀v,G.degree v=G.maxDegree → ∃!w,M.Adj v w :=
  exists_matching_covering_maximum_of_augmented_perfect G
    (augmentation_has_perfectMatching G hD hno)

/-- Deleting the constructed matching lowers the maximum degree. This
statement deliberately supplies no no-overfull invariant for the residual. -/
theorem exists_degree_lowering_matching_of_no_overfull (G : SimpleGraph V)
    [DecidableRel G.Adj] (hD : 0<G.maxDegree) (hno : ¬G.HasOverfullSubgraph) :
    ∃M : SimpleGraph V,M≤G ∧ OneFactor.IsMatchingGraph M ∧
      (G \ M).maxDegree≤G.maxDegree-1 := by
  obtain ⟨M,hMG,hmatching,hcover⟩:=exists_matching_covering_maximum_of_no_overfull G hD hno
  refine ⟨M,hMG,hmatching,?_⟩
  apply (G \ M).maxDegree_le_of_forall_degree_le
  intro v
  have hs : (G \ M).degree v+M.degree v=G.degree v := by
    convert Plantholt.degree_sdiff_add G hMG v using 1 <;> congr 5 <;> exact Subsingleton.elim _ _
  have hu:=G.degree_le_maxDegree v
  by_cases hv : G.degree v=G.maxDegree
  · have hm : M.degree v=1 := degree_eq_one_iff_existsUnique_adj.mpr (hcover v hv)
    omega
  · omega

end OverfullWork.MaximumMatching

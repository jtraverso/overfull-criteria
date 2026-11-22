module

public import OverfullWork.DirectedEndpointContraction

@[expose] public section


/-! Remove the possible loops created by endpoint contraction. This is
realized by deleting a matching of ordered host arcs; every semidegree
loses at most one more edge. No Hamiltonian existence is postulated. -/
namespace OverfullWork.DirectedEndpointContraction
open Finset DirectedRobustExpansion DirectedClusterQuotient
open scoped Classical
variable {V W : Type*} [Fintype V] [Fintype W]
set_option maxHeartbeats 18000000

def withoutMatchedArcs (D : Digraph V) (a b : W ↪ V) : Digraph V where
  Adj u v := D.Adj u v ∧ ¬∃ w,u=a w ∧ v=b w

def looplessContracted (D : Digraph V) (a b : W ↪ V) : Digraph W where
  Adj i j := i ≠ j ∧ D.Adj (a i) (b j)

theorem withoutMatchedArcs_le (D : Digraph V) (a b : W ↪ V) : withoutMatchedArcs D a b ≤ D :=
  fun _ _ h => h.1

theorem matched_indegree_loss (D : Digraph V) (a b : W ↪ V) (v : V) :
    inDegree (D\withoutMatchedArcs D a b) v ≤ 1 := by
  letI : DecidableRel (D\withoutMatchedArcs D a b).Adj := fun _ _ => Classical.propDecidable _
  unfold inDegree inNeighbours
  apply card_le_one.mpr
  intro u hu u' hu'
  obtain ⟨_,hD,hNot⟩ := mem_filter.mp hu
  obtain ⟨_,hD',hNot'⟩ := mem_filter.mp hu'
  have hMatch : ∃ w,u=a w ∧ v=b w := by by_contra hh;exact hNot ⟨hD,hh⟩
  have hMatch' : ∃ w,u'=a w ∧ v=b w := by by_contra hh;exact hNot' ⟨hD',hh⟩
  obtain ⟨w,rfl,hw⟩ := hMatch
  obtain ⟨w',rfl,hw'⟩ := hMatch'
  exact congrArg a (b.injective (hw.symm.trans hw'))

theorem matched_outdegree_loss (D : Digraph V) (a b : W ↪ V) (v : V) :
    outDegree (D\withoutMatchedArcs D a b) v ≤ 1 := by
  letI : DecidableRel (D\withoutMatchedArcs D a b).Adj := fun _ _ => Classical.propDecidable _
  unfold outDegree
  apply card_le_one.mpr
  intro u hu u' hu'
  obtain ⟨_,hD,hNot⟩ := mem_filter.mp hu
  obtain ⟨_,hD',hNot'⟩ := mem_filter.mp hu'
  have hMatch : ∃ w,v=a w ∧ u=b w := by by_contra hh;exact hNot ⟨hD,hh⟩
  have hMatch' : ∃ w,v=a w ∧ u'=b w := by by_contra hh;exact hNot' ⟨hD',hh⟩
  obtain ⟨w,hw,rfl⟩ := hMatch
  obtain ⟨w',hw',rfl⟩ := hMatch'
  exact congrArg b (a.injective (hw.symm.trans hw'))

theorem quotient_eq_loopless (D : Digraph V) (a b : W ↪ V) :
    TwoSidedClusterQuotient.quotient (withoutMatchedArcs D a b) (partialIndex a) (partialIndex b)=
      looplessContracted D a b := by
  ext i j
  constructor
  · rintro ⟨u,v,hu,hv,hD,hNot⟩
    rw [partialIndex_eq] at hu hv
    subst u;subst v
    exact ⟨fun hh => hNot ⟨i,rfl,congrArg b hh.symm⟩,hD⟩
  · rintro ⟨hij,hD⟩
    refine ⟨a i,b j,(partialIndex_eq a _ _).mpr rfl,(partialIndex_eq b _ _).mpr rfl,hD,?_⟩
    rintro ⟨w,ha,hb⟩
    exact hij ((a.injective ha).trans (b.injective hb).symm)

theorem looplessContracted_irrefl (D : Digraph V) (a b : W ↪ V) :
    ∀ w,¬(looplessContracted D a b).Adj w w := fun _ hh => hh.1 rfl

theorem robust_loopless_contracted (D : Digraph V) (a b : W ↪ V) (ν τ : ℝ)
    (hν : 0 < ν) (hτ : 0 < τ) (hRobust : IsRealRobust D ν τ)
    (hClusters : 4 ≤ ν*(Fintype.card W:ℝ)) (hOrder : 2 ≤ τ*(Fintype.card V:ℝ))
    (hDeficit : ((Fintype.card V-Fintype.card W:ℕ):ℝ) ≤ (Fintype.card V:ℝ)/4)
    (hLoss : ((Fintype.card V-Fintype.card W:ℕ):ℝ)+1 ≤ ν*(Fintype.card V:ℝ)/4) :
    IsRealRobust (looplessContracted D a b) (ν/2) (2*τ) := by
  let f := partialIndex a
  let g := partialIndex b
  let H := withoutMatchedArcs D a b
  have hG := partialIndex_size b
  have hException : ((exceptional g).card:ℝ) ≤ (Fintype.card V:ℝ)/4 := by
    simpa only [g,partialIndex_exceptional] using hDeficit
  have hSmall : ((exceptional g).card:ℝ)+(1:ℕ) ≤ ν*(Fintype.card V:ℝ)/4 := by
    simpa only [g,partialIndex_exceptional,Nat.cast_one] using hLoss
  obtain ⟨hPaid,hInterval⟩ := RobustClusterQuotient.paper_scale_budgets g 1 1 hG ν τ hν hτ
    hClusters hOrder hException hSmall
  have hR := TwoSidedClusterQuotient.real_robust_from_host D H (withoutMatchedArcs_le D a b) f g 1 1 (by omega)
    (partialIndex_size a) hG ν τ hν hτ hRobust (fun v _ => matched_indegree_loss D a b v) hPaid hInterval
  rw [quotient_eq_loopless] at hR
  exact hR

theorem loopless_indegree_loss (D : Digraph V) (a b : W ↪ V) (w : W) :
    inDegree D (b w) ≤ inDegree (looplessContracted D a b) w+(Fintype.card V-Fintype.card W)+1 := by
  let H := withoutMatchedArcs D a b
  have hLoss := RobustClusterQuotient.neighbour_loss_of_deleted_indegree D H
    (withoutMatchedArcs_le D a b) 1 (matched_indegree_loss D a b) univ (b w)
  change inDegree D (b w) ≤ inDegree H (b w)+1 at hLoss
  have hCount := indegree_loss H a b w
  have hEq := quotient_eq_loopless D a b
  rw [quotient_eq_contracted] at hEq
  change contracted H a b=looplessContracted D a b at hEq
  rw [hEq] at hCount
  omega

theorem loopless_outdegree_loss (D : Digraph V) (a b : W ↪ V) (w : W) :
    outDegree D (a w) ≤ outDegree (looplessContracted D a b) w+(Fintype.card V-Fintype.card W)+1 := by
  let H := withoutMatchedArcs D a b
  have hLoss := RobustClusterQuotient.outdegree_loss_of_deleted_outdegree D H
    (withoutMatchedArcs_le D a b) 1 (matched_outdegree_loss D a b) (a w)
  have hCount := outdegree_loss H a b w
  have hEq := quotient_eq_loopless D a b
  rw [quotient_eq_contracted] at hEq
  change contracted H a b=looplessContracted D a b at hEq
  rw [hEq] at hCount
  omega

theorem semidegrees_loopless_contracted (D : Digraph V) (a b : W ↪ V) (α : ℝ)
    (hα : 0 ≤ α) (hIn : ∀ v,α*(Fintype.card V:ℝ) ≤ (inDegree D v:ℝ))
    (hOut : ∀ v,α*(Fintype.card V:ℝ) ≤ (outDegree D v:ℝ))
    (hSmall : ((Fintype.card V-Fintype.card W:ℕ):ℝ)+1 ≤ α*(Fintype.card V:ℝ)/2) :
    (∀ w,(α/2)*(Fintype.card W:ℝ) ≤ (inDegree (looplessContracted D a b) w:ℝ)) ∧
    (∀ w,(α/2)*(Fintype.card W:ℝ) ≤ (outDegree (looplessContracted D a b) w:ℝ)) := by
  have hCard : (Fintype.card W:ℝ) ≤ (Fintype.card V:ℝ) := by
    exact_mod_cast Fintype.card_le_of_injective a a.injective
  have hScale := mul_le_mul_of_nonneg_left hCard hα
  constructor
  · intro w
    have hh : (inDegree D (b w):ℝ) ≤ (inDegree (looplessContracted D a b) w:ℝ)+((Fintype.card V-Fintype.card W:ℕ):ℝ)+1 := by
      exact_mod_cast loopless_indegree_loss D a b w
    have hMin := hIn (b w)
    linarith only [hh,hMin,hSmall,hScale]
  · intro w
    have hh : (outDegree D (a w):ℝ) ≤ (outDegree (looplessContracted D a b) w:ℝ)+((Fintype.card V-Fintype.card W:ℕ):ℝ)+1 := by
      exact_mod_cast loopless_outdegree_loss D a b w
    have hMin := hOut (a w)
    linarith only [hh,hMin,hSmall,hScale]

end OverfullWork.DirectedEndpointContraction

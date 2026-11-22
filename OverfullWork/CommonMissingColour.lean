module

public import Overfull.Degree

@[expose] public section


/-! # Choosing a common missing colour outside a prescribed finite set

The present-colour budget retains the saving at an endpoint of an
uncoloured edge. It is used in the Kempe constructions of Cao--Chen
Proposition A, including the boundary case of its numerical threshold.
-/
namespace OverfullWork.CommonMissingColour
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The number of present colours equals the number of coloured incident edges. -/
theorem present_colour_card (k : ℕ) (c : PEC G (Fin k)) (v : V) :
    (univ\missing c v).card=(colNbrs c v).card := by
  have hh:=card_missing_add_colNbrs c v
  rw [card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin]
  omega

theorem exists_common_free_outside_of_present_budget {k : ℕ}
    (c : PEC G (Fin k)) (T : Finset V) (F : Finset (Fin k))
    (hbudget : (∑ v∈T,(colNbrs c v).card)+F.card<k) :
    ∃ δ : Fin k,δ∉F ∧ ∀ v∈T,c.IsFree v δ := by
  let B:=T.biUnion (fun v => univ\missing c v)
  have hB : B.card≤∑ v∈T,(colNbrs c v).card := by
    calc
      _ ≤ ∑ v∈T,(univ\missing c v).card := card_biUnion_le
      _ = _ := sum_congr rfl (fun v _ => present_colour_card k c v)
  have hcard : (F∪B).card<(univ : Finset (Fin k)).card := by
    have hh:=card_union_le F B
    rw [card_univ,Fintype.card_fin]
    omega
  obtain ⟨δ,_hδ,hnot⟩:=exists_mem_notMem_of_card_lt_card hcard
  have hδF : δ∉F := fun h => hnot (mem_union.mpr (Or.inl h))
  refine ⟨δ,hδF,?_⟩
  intro v hv
  apply mem_missing.mp
  by_contra hn
  have hδB : δ∈B := mem_biUnion.mpr ⟨v,hv,mem_sdiff.mpr ⟨mem_univ δ,hn⟩⟩
  exact hnot (mem_union.mpr (Or.inr hδB))

theorem exists_common_free_outside_of_degree_budget {k : ℕ}
    (c : PEC G (Fin k)) (T : Finset V) (F : Finset (Fin k))
    (hbudget : (∑ v∈T,G.degree v)+F.card<k) :
    ∃ δ : Fin k,δ∉F ∧ ∀ v∈T,c.IsFree v δ := by
  apply exists_common_free_outside_of_present_budget c T F
  have hsum : (∑ v∈T,(colNbrs c v).card)≤∑ v∈T,G.degree v := by
    apply sum_le_sum
    intro v _
    exact (card_le_card (filter_subset (fun u => c.col v u≠none) (G.neighborFinset v))).trans_eq
      (card_neighborFinset_eq_degree G v)
  omega

/-- An uncoloured-edge endpoint in T pays one additional colour, so a
weak degree budget suffices. This includes the equality case in Claim 5.3. -/
theorem exists_common_free_outside_of_colMinus_budget
    {c : PEC G (Fin G.maxDegree)} {a b : V} (hcm : IsColMinus c a b)
    (T : Finset V) (F : Finset (Fin G.maxDegree)) (ha : a∈T)
    (hbudget : (∑ v∈T,G.degree v)+F.card≤G.maxDegree) :
    ∃ δ : Fin G.maxDegree,δ∉F ∧ ∀ v∈T,c.IsFree v δ := by
  have hpoint : ∀ v∈T,(colNbrs c v).card+(if v=a then 1 else 0)≤G.degree v := by
    intro v _
    have hh:=hcm.card_colNbrs v
    split_ifs with hv
    · subst v
      simp only [true_or,if_true] at hh
      omega
    · omega
  have hsum:=sum_le_sum hpoint
  rw [sum_add_distrib,show (∑ v∈T,if v=a then 1 else 0)=1 by simp [ha]] at hsum
  apply exists_common_free_outside_of_present_budget c T F
  omega

end OverfullWork.CommonMissingColour

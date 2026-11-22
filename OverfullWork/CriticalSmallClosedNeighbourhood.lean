module

public import OverfullWork.MaximumCoreDegree

@[expose] public section


/-! # The small-vertex count used in Cao--Chen Proposition A

This is the elementary observation (*) in the proof of Proposition A,
Cao--Chen, JCTB 145 (2020), page 478. Its weaker numerical hypothesis
already follows from VAL; the fork construction and the global
average-degree theorem are not asserted here.
-/
namespace OverfullWork.CaoChenSmallNeighbourhood
open SimpleGraph Finset Gate8J2C
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every closed neighbourhood contains at most d−1 vertices of degree
at most d, provided two such degrees cannot satisfy critical edge VAL. -/
theorem closed_neighbourhood_small_degree_card_le (G : SimpleGraph V)
    [DecidableRel G.Adj] (hcrit : Overfull.IsDeltaCritical G) (d : ℕ)
    (hd : 2≤d) (hthreshold : 2*d<G.maxDegree+2) (v : V) :
    ((insert v (G.neighborFinset v)).filter fun x => G.degree x≤d).card≤d-1 := by
  have hD : d<G.maxDegree := by omega
  by_cases hv : G.degree v≤d
  · have hnone : ((G.neighborFinset v).filter fun x => G.degree x≤d)=∅ := by
      apply eq_empty_of_forall_notMem
      intro x hx
      obtain ⟨hxN,hxd⟩ := mem_filter.mp hx
      have hval := Overfull.deg_add hcrit ((mem_neighborFinset G v x).mp hxN)
      omega
    simp only [filter_insert,if_pos hv,hnone,insert_empty_eq,card_singleton]
    omega
  · simp only [filter_insert,if_neg hv]
    let L:=(G.neighborFinset v).filter fun x => G.degree x≤d
    by_cases hL : L.Nonempty
    · obtain ⟨x,hx⟩ := hL
      obtain ⟨hxN,hxd⟩ := mem_filter.mp hx
      have hval := deficit_le_maximumNeighbours G hcrit ((mem_neighborFinset G v x).mp hxN)
      let K:=(G.neighborFinset v).filter fun x => G.degree x=G.maxDegree
      have hdis : Disjoint L K := by
        apply Finset.disjoint_left.mpr
        intro y hyL hyK
        have hylo := (mem_filter.mp hyL).2
        have hyhi := (mem_filter.mp hyK).2
        omega
      have hsub : L∪K⊆G.neighborFinset v :=
        union_subset (filter_subset _ _) (filter_subset _ _)
      have hcard := card_le_card hsub
      rw [card_union_of_disjoint hdis,card_neighborFinset_eq_degree] at hcard
      have hmax := G.degree_le_maxDegree v
      change G.maxDegree-G.degree x+1≤K.card at hval
      change L.card≤d-1
      omega
    · have he : L=∅ := not_nonempty_iff_eq_empty.mp hL
      change L.card≤d-1
      simp only [he,card_empty,Nat.zero_le]

end OverfullWork.CaoChenSmallNeighbourhood

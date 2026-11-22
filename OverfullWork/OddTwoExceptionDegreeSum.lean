module

public import OverfullWork.NearTightOddSetGeometry

@[expose] public section


/-! # Exact degree balance for two nonadjacent exceptions at odd order

The odd-set budgets on the whole graph and on the complement of the two
exceptional vertices force their degree sum to equal the maximum degree.
This supplies the regularity equation for an actual identification.
-/
namespace OverfullWork.OddTwoExceptionDegreeSum
open SimpleGraph Finset OddCutDeficit
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem internalEdges_pair_eq_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) (hnon : ¬G.Adj u v) : internalEdges G {u,v}=0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  induction e using Sym2.inductionOn with
  | hf a b =>
    have hab : G.Adj a b := (mem_edgeSet G).mp (mem_edgeFinset.mp (mem_filter.mp he).1)
    have hends : (a=u ∨ a=v) ∧ (b=u ∨ b=v) := by
      simpa only [Sym2.toFinset_mk_eq,insert_subset_iff,singleton_subset_iff,
        mem_insert,mem_singleton] using (mem_filter.mp he).2
    rcases hends with ⟨rfl|rfl,rfl|rfl⟩
    · exact G.ne_of_adj hab rfl
    · exact hnon hab
    · exact hnon hab.symm
    · exact G.ne_of_adj hab rfl

theorem cutEdges_pair_eq_degree_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) (huv : u≠v) (hnon : ¬G.Adj u v) :
    cutEdges G {u,v}=G.degree u+G.degree v := by
  have h:=internal_cut_identity G {u,v}
  rw [internalEdges_pair_eq_zero G u v hnon] at h
  simpa only [mul_zero,zero_add,sum_pair huv] using h

/-- No-overfullness at odd order balances precisely two nonadjacent
degree exceptions. No lower-degree or criticality hypothesis is needed. -/
theorem degree_sum_eq_maxDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    (hodd : Odd (Fintype.card V)) (hno : ¬G.HasOverfullSubgraph)
    (u v : V) (huv : u≠v) (hnon : ¬G.Adj u v)
    (hother : ∀w,w≠u → w≠v → G.degree w=G.maxDegree) :
    G.degree u+G.degree v=G.maxDegree := by
  let T : Finset V:={u,v}
  have hTcard : T.card=2 := by simp [T,huv]
  have hTcomp : Odd Tᶜ.card := by
    have hcard : T.card+Tᶜ.card=Fintype.card V := by simp
    obtain ⟨m,hm⟩:=hodd
    refine ⟨m-1,?_⟩
    omega
  have hdef : deficitMass G G.maxDegree Tᶜ=0 := by
    apply sum_eq_zero
    intro w hw
    have hw' : w≠u ∧ w≠v := by simpa [T] using hw
    rw [hother w hw'.1 hw'.2,Nat.sub_self]
  have hlow:=(no_overfull_iff_odd_cut_deficit G).mp hno Tᶜ hTcomp
  rw [NearTightOddSetGeometry.cutEdges_compl,hdef,add_zero] at hlow
  have hcutT:=cutEdges_pair_eq_degree_sum G u v huv hnon
  change cutEdges G T=G.degree u+G.degree v at hcutT
  rw [hcutT] at hlow
  have hcut : cutEdges G univ=0 := by simp [cutEdges,crossingEdges]
  have hmass : deficitMass G G.maxDegree univ=
      (G.maxDegree-G.degree u)+(G.maxDegree-G.degree v) := by
    have he : (∑w∈T,(G.maxDegree-G.degree w))=∑w∈(univ:Finset V),(G.maxDegree-G.degree w) := by
      apply sum_subset (subset_univ _)
      intro w _ hw
      have hw' : w≠u ∧ w≠v := by simpa [T] using hw
      rw [hother w hw'.1 hw'.2,Nat.sub_self]
    change (∑w∈(univ:Finset V),(G.maxDegree-G.degree w))=_
    rw [←he]
    simp only [T,sum_pair huv]
  have hhigh:=(no_overfull_iff_odd_cut_deficit G).mp hno univ (by simpa using hodd)
  rw [hcut,hmass] at hhigh
  have hu:=G.degree_le_maxDegree u
  have hv:=G.degree_le_maxDegree v
  omega

/-- At odd order, two possible degree exceptions must be nonadjacent
whenever no odd set is overfull. This removes an auxiliary construction
hypothesis from the final two-exception criterion. -/
theorem nonadjacent_of_two_exceptions (G : SimpleGraph V) [DecidableRel G.Adj]
    (hodd : Odd (Fintype.card V)) (hno : ¬G.HasOverfullSubgraph)
    (u v : V) (huv : u≠v)
    (hother : ∀w,w≠u → w≠v → G.degree w=G.maxDegree) : ¬G.Adj u v := by
  let T : Finset V:={u,v}
  have hTcard : T.card=2 := by simp [T,huv]
  have hTcomp : Odd Tᶜ.card := by
    have hcard : T.card+Tᶜ.card=Fintype.card V := by simp
    obtain ⟨m,hm⟩:=hodd
    exact ⟨m-1,by omega⟩
  have hdef : deficitMass G G.maxDegree Tᶜ=0 := by
    apply sum_eq_zero
    intro w hw
    have hw' : w≠u ∧ w≠v := by simpa [T] using hw
    rw [hother w hw'.1 hw'.2,Nat.sub_self]
  have hlow:=(no_overfull_iff_odd_cut_deficit G).mp hno Tᶜ hTcomp
  rw [NearTightOddSetGeometry.cutEdges_compl,hdef,add_zero] at hlow
  have hcut : cutEdges G univ=0 := by simp [cutEdges,crossingEdges]
  have hmass : deficitMass G G.maxDegree univ=
      (G.maxDegree-G.degree u)+(G.maxDegree-G.degree v) := by
    have he : (∑w∈T,(G.maxDegree-G.degree w))=∑w∈(univ:Finset V),(G.maxDegree-G.degree w) := by
      apply sum_subset (subset_univ _)
      intro w _ hw
      have hw' : w≠u ∧ w≠v := by simpa [T] using hw
      rw [hother w hw'.1 hw'.2,Nat.sub_self]
    change (∑w∈(univ:Finset V),(G.maxDegree-G.degree w))=_
    rw [←he]
    simp only [T,sum_pair huv]
  have hhigh:=(no_overfull_iff_odd_cut_deficit G).mp hno univ (by simpa using hodd)
  rw [hcut,hmass] at hhigh
  have hi:=internal_cut_identity G T
  have hdeg : (∑w∈T,G.degree w)=G.degree u+G.degree v := by simp [T,huv]
  rw [hdeg] at hi
  have hu:=G.degree_le_maxDegree u
  have hv:=G.degree_le_maxDegree v
  have hz : internalEdges G T=0 := by omega
  intro hadj
  have hpos : 0 < internalEdges G T := by
    apply card_pos.mpr
    refine ⟨s(u,v),mem_filter.mpr ⟨mem_edgeFinset.mpr ((mem_edgeSet G).mpr hadj),?_⟩⟩
    simp [T,Sym2.toFinset_mk_eq]
  omega

end OverfullWork.OddTwoExceptionDegreeSum

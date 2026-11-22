module

public import OverfullWork.DirectedSpanningConfiguration

@[expose] public section


/-! Semidegree bookkeeping for the flexible portions of spanning
configurations. Fixed copies never enter the host deletion. -/
namespace OverfullWork.DirectedSpanningConfiguration

open Finset DirectedRobustExpansion
open scoped Classical
variable {V I : Type*} [Fintype V] [Fintype I]

private theorem card_filter_exists_eq (P : I → V → Prop) (h : ∀ i j, i ≠ j →
    ∀ v, P i v → P j v → False) :
    ((univ : Finset V).filter (fun v => ∃ i, P i v)).card =
      ∑ i, ((univ : Finset V).filter (P i)).card := by
  let N := fun i => (univ : Finset V).filter (P i)
  have he : ((univ : Finset V).filter (fun v => ∃ i, P i v)) = univ.biUnion N := by
    ext v
    simp [N]
  rw [he]
  apply card_biUnion
  intro i _ j _ hij
  exact disjoint_left.mpr fun v hi hj => h i j hij v (mem_filter.mp hi).2 (mem_filter.mp hj).2

theorem outDegree_iSup_of_disjoint (D : I → Digraph V) (h : Pairwise (fun i j => Disjoint (D i) (D j)))
    (v : V) : outDegree (⨆ i, D i) v = ∑ i, outDegree (D i) v := by
  simp only [outDegree,Digraph.iSup_adj]
  exact card_filter_exists_eq _ (fun i j hij w hi hj => disjoint_iff_inf_le.mp (h hij) (show
    ((D i) ⊓ (D j)).Adj v w from ⟨hi,hj⟩))

theorem inDegree_iSup_of_disjoint (D : I → Digraph V) (h : Pairwise (fun i j => Disjoint (D i) (D j)))
    (v : V) : inDegree (⨆ i, D i) v = ∑ i, inDegree (D i) v := by
  simp only [inDegree,inNeighbours,Digraph.iSup_adj]
  exact card_filter_exists_eq _ (fun i j hij w hi hj => disjoint_iff_inf_le.mp (h hij) (show
    ((D i) ⊓ (D j)).Adj w v from ⟨hi,hj⟩))

private theorem card_filter_sub_partition (P Q : V → Prop) (h : ∀ v, Q v → P v) :
    ((univ : Finset V).filter (fun v => P v ∧ ¬Q v)).card +
      ((univ : Finset V).filter Q).card = ((univ : Finset V).filter P).card := by
  have hEq : ((univ : Finset V).filter (fun v => P v ∧ ¬Q v)) =
      univ.filter P \ univ.filter Q := by
    ext v
    simp
  rw [hEq]
  exact card_sdiff_add_card_eq_card ((by
    intro v hv
    exact mem_filter.mpr ⟨mem_univ _,h v (mem_filter.mp hv).2⟩))

omit [Fintype I] in
theorem outDegree_sdiff_add_of_le (D U : Digraph V) (h : U ≤ D) (v : V) :
    outDegree (D \ U) v + outDegree U v = outDegree D v :=
  by simpa only [outDegree,Digraph.sdiff_adj] using
    card_filter_sub_partition (D.Adj v) (U.Adj v) (fun _ hw => h hw)

omit [Fintype I] in
theorem inDegree_sdiff_add_of_le (D U : Digraph V) (h : U ≤ D) (v : V) :
    inDegree (D \ U) v + inDegree U v = inDegree D v :=
  by simpa only [inDegree,inNeighbours,Digraph.sdiff_adj] using
    card_filter_sub_partition (fun w => D.Adj w v) (fun w => U.Adj w v) (fun _ hw => h hw)

theorem Realization.outDegree_used {D : Digraph V} {L : Layout V I} (R : Realization D L)
    (v : V) :
    outDegree R.used v = ∑ i : {i // i ∉ L.fixed},
      if v = L.source i.val ∨ v ∈ R.interior i.val then 1 else 0 := by
  unfold Realization.used
  rw [outDegree_iSup_of_disjoint _ (fun i j hij =>
    R.disjoint_flexible i.prop (fun h => hij (Subtype.ext h)))]
  apply sum_congr rfl
  intro i _
  have h := word_outDegree (L.source i.val :: R.interior i.val) (L.target i.val) v (R.simple i.val)
  simpa only [Realization.word,List.mem_cons] using h

theorem Realization.inDegree_used {D : Digraph V} {L : Layout V I} (R : Realization D L)
    (v : V) :
    inDegree R.used v = ∑ i : {i // i ∉ L.fixed},
      if v = L.target i.val ∨ v ∈ R.interior i.val then 1 else 0 := by
  unfold Realization.used
  rw [inDegree_iSup_of_disjoint _ (fun i j hij =>
    R.disjoint_flexible i.prop (fun h => hij (Subtype.ext h)))]
  apply sum_congr rfl
  intro i _
  have h := word_inDegree (R.interior i.val ++ [L.target i.val]) (L.source i.val) v (R.simple i.val)
  simpa only [Realization.word,List.cons_append,List.mem_append,List.mem_singleton,or_comm] using h

omit [Fintype V] in
private theorem Realization.oneInterior {D : Digraph V} {L : Layout V I} (R : Realization D L)
    (v : V) (hv : v ∉ L.boundary) :
    (∑ i : {i // i ∉ L.fixed}, if v ∈ R.interior i.val then 1 else 0) = 1 := by
  obtain ⟨i,hi⟩ := R.spans v hv
  have hFlex : i ∉ L.fixed := by
    intro hf
    simp [R.fixed_empty i hf] at hi
  let j : {i // i ∉ L.fixed} := ⟨i,hFlex⟩
  rw [sum_eq_single j]
  · simp [j,hi]
  · intro k _ hek
    exact if_neg fun hk => R.unique i k.val (fun he => hek (Subtype.ext he.symm)) hi hk
  · simp

/-- Every vertex off the layout has exactly one incoming and one outgoing
host arc. On the layout boundary, only the flexible endpoint occurrences
are counted. In particular, isolated layout vertices have degree zero. -/
theorem Realization.semidegrees_used {D : Digraph V} {L : Layout V I} (R : Realization D L)
    (v : V) :
    inDegree R.used v = (if v ∈ L.boundary then
      ∑ i : {i // i ∉ L.fixed}, if v = L.target i.val then 1 else 0 else 1) ∧
    outDegree R.used v = (if v ∈ L.boundary then
      ∑ i : {i // i ∉ L.fixed}, if v = L.source i.val then 1 else 0 else 1) := by
  rw [R.inDegree_used,R.outDegree_used]
  by_cases hv : v ∈ L.boundary
  · have hNot (i : I) : v ∉ R.interior i := fun h => R.outside i v h hv
    simp [hv,hNot]
  · have hNot (i : I) : v ≠ L.target i ∧ v ≠ L.source i :=
      ⟨fun he => hv (he ▸ (L.ends i).2.1),fun he => hv (he ▸ (L.ends i).1)⟩
    simp only [if_neg hv,(hNot _).1,(hNot _).2,false_or]
    exact ⟨R.oneInterior v hv,R.oneInterior v hv⟩

end OverfullWork.DirectedSpanningConfiguration

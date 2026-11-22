module

public import OverfullWork.DirectedReserveStitching
public import OverfullWork.RobustHamiltonDecomposition

@[expose] public section


/-! Expand a Hamilton cycle of the auxiliary digraph into a cycle using
every path in the cut-open factor as an unchanged segment. -/
namespace OverfullWork.DirectedRobustExpansion
open DirectedAbsorbingLadder
variable {V I : Type*}

theorem expand_auxiliary_merge_cycle (D : Digraph V) (P : I → PathRequest D)
    (hDis : ∀ i j, i ≠ j → List.Disjoint (P i).vertices (P j).vertices)
    (hAux : HasSpanningCycle (fun i j => D.Adj (P i).target (P j).source)) :
    ∃ T : List V, ∃ a : V, T.Nodup ∧ T.head? = some a ∧
      (T ++ [a]).IsChain D.Adj ∧ (∀ v, v ∈ T ↔ ∃ i, v ∈ (P i).vertices) ∧
      ∀ i, List.IsInfix (P i).vertices T := by
  obtain ⟨order,z,hND,hAll,hHead,hOrder⟩ := hAux
  let A := fun i => (P i).vertices
  let T := order.flatMap A
  have hHead' : T.head? = some (P z).source := by
    cases he : order with
    | nil => simp [he] at hHead
    | cons x xs =>
      have hx : x = z := by simpa [he] using hHead
      subst x
      simp [T,he,A,PathRequest.vertices]
  have hChain : (T ++ [(P z).source]).IsChain D.Adj :=
    DirectedReserveStitching.chain_of_blocks D A (fun i => (P i).source)
      (fun i => (P i).target) (fun _ => rfl) (fun i => (P i).route.2)
      (fun i => (P i).route.1) z order hOrder
  refine ⟨T,(P z).source,List.nodup_flatMap.mpr ⟨fun i _ => (P i).simple,?_⟩,
    hHead',hChain,?_,?_⟩
  · exact hND.imp (fun h => hDis _ _ h)
  · intro v
    constructor
    · intro hv
      obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp hv
      exact ⟨i,hi⟩
    · rintro ⟨i,hi⟩
      exact List.mem_flatMap.mpr ⟨i,hAll i,hi⟩
  · intro i
    obtain ⟨l,r,ho⟩ := List.append_of_mem (hAll i)
    refine ⟨l.flatMap A,r.flatMap A,?_⟩
    simp [T,A,ho,List.append_assoc]

theorem expand_auxiliary_merge_cycle_spanning (D : Digraph V) (P : I → PathRequest D)
    (hDis : ∀ i j, i ≠ j → List.Disjoint (P i).vertices (P j).vertices)
    (hCover : ∀ v, ∃ i, v ∈ (P i).vertices)
    (hAux : HasSpanningCycle (fun i j => D.Adj (P i).target (P j).source)) :
    HasSpanningCycle D.Adj := by
  obtain ⟨T,a,hN,hH,hCh,hMem,_⟩ := expand_auxiliary_merge_cycle D P hDis hAux
  exact ⟨T,a,hN,fun v => (hMem v).mpr (hCover v),hH,hCh⟩

end OverfullWork.DirectedRobustExpansion

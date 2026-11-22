module

public import OverfullWork.OrderedPathContraction
public import OverfullWork.DirectedRouteJoining

@[expose] public section


/-! Expand an actual Hamilton cycle of the single-path contraction.
The resulting actual host cycle contains the prescribed path in order.
Hamilton cycle existence in the contracted graph remains a separate
unproved dependency of R2. -/
namespace OverfullWork.DirectedPrescribedVertexPath
open Finset DirectedRobustExpansion DirectedEndpointContraction DirectedListRoutes
open scoped Classical
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 12000000

theorem list_outside_of_missing_marker {X : Type*} (init : List (X ⊕ Fin 1))
    (h : Sum.inr (0 : Fin 1)∉init) : ∃ S : List X,init=S.map Sum.inl := by
  induction init with
  | nil => exact ⟨[],rfl⟩
  | cons v vs ih =>
    have hTail : Sum.inr (0 : Fin 1)∉vs := fun hh => h (List.mem_cons_of_mem _ hh)
    cases v with
    | inr j =>
      have he : j=0 := Subsingleton.elim _ _
      subst j
      exact False.elim (h (by simp))
    | inl v =>
      obtain ⟨S,hS⟩ := ih hTail
      exact ⟨v::S,by simp only [List.map_cons,←hS]⟩

theorem return_terminal_chain (D : Digraph V) (x : V) (l : List V)
    (S : List (Outside (pathVertices x l)))
    (h : (S.map Sum.inl ++ [Sum.inr (0 : Fin 1)]).IsChain (contractedPath D x l).Adj) :
    (S.map Subtype.val ++ [x]).IsChain D.Adj := by
  induction S with
  | nil => exact .singleton _
  | cons v vs ih =>
    have ht := ih h.tail
    cases vs with
    | nil => exact List.IsChain.cons_cons h.rel.2 ht
    | cons w ws => exact List.IsChain.cons_cons h.rel.2 ht

theorem return_chain (D : Digraph V) (x : V) (l : List V)
    (S : List (Outside (pathVertices x l)))
    (h : (Sum.inr (0 : Fin 1) :: (S.map Sum.inl ++ [Sum.inr 0])).IsChain
      (contractedPath D x l).Adj) :
    (pathEnd x l :: (S.map Subtype.val ++ [x])).IsChain D.Adj := by
  have ht := return_terminal_chain D x l S h.tail
  cases S with
  | nil => exact List.IsChain.cons_cons h.rel.2 ht
  | cons v vs => exact List.IsChain.cons_cons h.rel.2 ht

/-- A conventional actual Hamilton cycle in the contracted graph
expands to a conventional ordered Hamilton cycle in the host graph. -/
theorem expand_contracted_cycle (D : Digraph V) (x : V) (l marks : List V)
    (hPath : (x :: l).IsChain D.Adj) (hSimple : (x :: l).Nodup)
    (hMarks : marks.Sublist l)
    (init : List (Outside (pathVertices x l) ⊕ Fin 1))
    (hCycleSimple : (init ++ [Sum.inr (0 : Fin 1)]).Nodup)
    (hCycleCover : ∀ w,w∈init ++ [Sum.inr (0 : Fin 1)])
    (hCycle : (Sum.inr (0 : Fin 1) :: (init ++ [Sum.inr 0])).IsChain
      (contractedPath D x l).Adj) :
    ∃ T : List V,T.Nodup ∧ (∀ v,v∈T) ∧ T.head?=some x ∧
      (T++[x]).IsChain D.Adj ∧ (x :: marks).Sublist T := by
  have hNoMarker : Sum.inr (0 : Fin 1)∉init := by
    intro hh
    exact (List.nodup_append.mp hCycleSimple).2.2 _ hh _ (by simp) rfl
  obtain ⟨S,hInit⟩ := list_outside_of_missing_marker init hNoMarker
  have hS : S.Nodup := by
    have hh := (List.nodup_append.mp hCycleSimple).1
    rw [hInit] at hh
    exact hh.of_map Sum.inl
  have hMapped := hS.map Subtype.val_injective
  have hApart : ∀ v∈x :: l,∀ w∈S.map Subtype.val,v≠w := by
    intro v hv w hw he
    obtain ⟨z,_,hz⟩ := List.mem_map.mp hw
    apply z.property
    apply List.mem_toFinset.mpr
    change z.val∈x :: l
    rw [hz,←he]
    exact hv
  let T := (x :: l)++S.map Subtype.val
  have hReturn : (pathEnd x l :: (S.map Subtype.val ++ [x])).IsChain D.Adj := by
    apply return_chain D x l S
    simpa only [←hInit] using hCycle
  have hEnd : (x :: l).getLast?=some (pathEnd x l) :=
    List.getLast?_eq_some_getLast (by simp)
  refine ⟨T,List.nodup_append.mpr ⟨hSimple,hMapped,hApart⟩,?_,by simp [T],?_,?_⟩
  · intro v
    by_cases hv : v∈pathVertices x l
    · exact List.mem_append_left _ (List.mem_toFinset.mp hv)
    · let z : Outside (pathVertices x l) := ⟨v,hv⟩
      have hz := hCycleCover (Sum.inl z)
      rw [hInit] at hz
      have hzS : z∈S := by simpa using hz
      exact List.mem_append_right _ (List.mem_map.mpr ⟨z,hzS,rfl⟩)
  · have hh := join_chain D (show Route D x (pathEnd x l) l from ⟨hPath,hEnd⟩) hReturn
    simpa only [T,List.cons_append,List.append_assoc] using hh
  · exact (hMarks.cons_cons x).trans (List.sublist_append_left (x :: l) (S.map Subtype.val))

end OverfullWork.DirectedPrescribedVertexPath

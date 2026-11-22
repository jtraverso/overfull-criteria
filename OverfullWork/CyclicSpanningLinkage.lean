module

public import OverfullWork.RobustBatchPathPacking
public import Mathlib.Data.List.ChainOfFn

@[expose] public section


/-! Close the spanning linear forest by the matching edges in
CMS §5.2, Case 1. The linkage is prescribed in cyclic order. -/
namespace OverfullWork.EvenHamiltonFactorization
open SimpleGraph DirectedRobustExpansion
open scoped Classical
variable {V : Type*}

/-- Linking the head of each matching edge to the tail of the next
one gives a spanning cycle when the paths are disjoint and spanning. -/
theorem spanning_cycle_of_cyclic_linkage {G : SimpleGraph V} {adj : V → V → Prop}
    (k : ℕ) (a b : Fin (k+1) → V)
    (P : ∀ i, G.Walk (b i) (a (finRotate (k+1) i)))
    (hPath : ∀ i, (P i).IsPath)
    (hDisj : ∀ i j, i ≠ j → ∀ v, v ∈ (P i).support → v ∉ (P j).support)
    (hSpan : ∀ v, ∃ i, v ∈ (P i).support)
    (hEdge : ∀ x y, G.Adj x y → adj x y)
    (hJoin : ∀ i, adj (a i) (b i)) :
    HasSpanningCycle adj := by
  let L := List.ofFn (fun i => (P i).support)
  let T := L.flatten
  have hHead (i : Fin (k+1)) : (P i).support.head? = some (b i) := by
    rw [List.head?_eq_some_head (P i).support_ne_nil,Walk.head_support]
  have hLast (i : Fin (k+1)) : (P i).support.getLast? = some (a (finRotate (k+1) i)) := by
    rw [List.getLast?_eq_some_getLast (P i).support_ne_nil,Walk.getLast_support]
  have hNone : [] ∉ L := by
    intro h
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp h
    exact (P i).support_ne_nil hi
  have hTHead : T.head? = some (b 0) := by
    rw [List.head?_flatten]
    change (List.ofFn (fun i => (P i).support)).findSome? List.head? = _
    rw [List.ofFn_succ]
    simp only [List.findSome?_cons,hHead]
  have hTLast : T.getLast? = some (a 0) := by
    rw [List.getLast?_flatten]
    change (List.ofFn (fun i => (P i).support)).reverse.findSome? List.getLast? = _
    rw [List.ofFn_succ_last,List.reverse_append]
    simp only [List.reverse_cons,List.reverse_nil,List.nil_append,List.singleton_append,
      List.findSome?_cons,hLast,finRotate_last]
  refine ⟨T,b 0,?_,?_,hTHead,?_⟩
  · apply List.nodup_flatten.mpr
    constructor
    · intro l hl
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hl
      exact (Walk.isPath_def _).mp (hPath i)
    · apply List.pairwise_ofFn.mpr
      intro i j hij
      exact List.disjoint_left.mpr (fun v hv => hDisj i j (ne_of_lt hij) v hv)
  · intro v
    obtain ⟨i,hi⟩ := hSpan v
    exact List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,hi⟩
  · apply List.isChain_append.mpr
    refine ⟨(List.isChain_flatten hNone).mpr ⟨?_,?_⟩,List.IsChain.singleton _,?_⟩
    · intro l hl
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hl
      exact (P i).isChain_adj_support.imp hEdge
    · apply List.isChain_ofFn.mpr
      intro i hi x hx y hy
      have hRot : finRotate (k+1) ⟨i,Nat.lt_of_succ_lt hi⟩ = ⟨i+1,hi⟩ :=
        finRotate_of_lt (by omega : i < k)
      rw [hLast,hRot] at hx
      rw [hHead] at hy
      simp only [Option.mem_def,Option.some.injEq] at hx hy
      exact hx ▸ hy ▸ hJoin ⟨i+1,hi⟩
    · intro x hx y hy
      rw [hTLast] at hx
      simp only [List.head?_cons,Option.mem_def,Option.some.injEq] at hx hy
      exact hx ▸ hy ▸ hJoin 0

section Factor
open MultiGraph PathGraphRealization
variable [Fintype V] [DecidableEq V]

/-- The ordinary forest and the prescribed matching together give a
two-regular layer with its two-colouring. Multiplicities are added:
an original support edge and an extra copy have separate roles. -/
theorem colourable_layer_of_cyclic_linkage {G : SimpleGraph V}
    (k : ℕ) (a b : Fin (k+1) → V)
    (P : ∀ i, G.Walk (b i) (a (finRotate (k+1) i)))
    (hPath : ∀ i, (P i).IsPath)
    (hDisj : ∀ i j, i ≠ j → ∀ v, v ∈ (P i).support → v ∉ (P j).support)
    (hSpan : ∀ v, ∃ i, v ∈ (P i).support)
    (hEnds : ∀ i, b i ≠ a (finRotate (k+1) i))
    (J : MultiGraph V) (hJoin : ∀ i, 0 < J.mult s(a i,b i))
    (hCover : ∀ i v, v ∈ (P i).support →
      J.degree v = if v = b i ∨ v = a (finRotate (k+1) i) then 1 else 0)
    (hEven : Even (Fintype.card V)) :
    let L := (ofSimpleGraph (pathUnion P)).addCopies J
    L.IsRegularOfDegree 2 ∧ Nonempty (L.EdgeColoring 2) := by
  let L := (ofSimpleGraph (pathUnion P)).addCopies J
  have hReg : L.IsRegularOfDegree 2 := by
    intro v
    obtain ⟨i,hi⟩ := hSpan v
    change L.degree v = 2
    rw [show L = _ from rfl,degree_addCopies,degree_ofSimpleGraph,
      degree_eq_of_mem_support P hDisj i hi,hCover i v hi]
    by_cases hB : v = b i
    · subst v
      rw [if_pos (Or.inl rfl),degree_start _ (hPath i) (hEnds i)]
    by_cases hA : v = a (finRotate (k+1) i)
    · subst v
      rw [if_pos (Or.inr rfl),degree_end _ (hPath i) (hEnds i)]
    · rw [if_neg (not_or.mpr ⟨hB,hA⟩),degree_internal _ (hPath i) hi hB hA]
  have hSupport (x y : V) (hxy : (pathUnion P).Adj x y) : L.supportGraph.Adj x y := by
    change 0 < (if (pathUnion P).Adj x y then 1 else 0)+J.mult s(x,y)
    simp [hxy]
  let Q : ∀ i, (pathUnion P).Walk (b i) (a (finRotate (k+1) i)) := fun i =>
    (P i).transfer (pathUnion P) (fun edge he => by
      apply SimpleGraph.edgeSet_mono (le_iSup (fun j => PathGraphRealization.pathGraph (P j)) i)
      rw [PathGraphRealization.pathGraph,Subgraph.edgeSet_spanningCoe,Walk.mem_edges_toSubgraph]
      exact he)
  have hQ (i : Fin (k+1)) : (Q i).support = (P i).support := by
    dsimp only [Q]
    exact Walk.support_transfer (p := P i) _
  have hCycle : HasSpanningCycle L.supportGraph.Adj :=
    spanning_cycle_of_cyclic_linkage k a b Q
      (fun i => by rw [Walk.isPath_def,hQ]; exact (Walk.isPath_def _).mp (hPath i))
      (by simpa only [hQ] using hDisj) (by simpa only [hQ] using hSpan) hSupport
      (fun i => by
        change 0 < (ofSimpleGraph (pathUnion P)).mult s(a i,b i)+J.mult s(a i,b i)
        exact Nat.lt_of_lt_of_le (hJoin i) (Nat.le_add_left _ _))
  exact ⟨hReg,two_colourings_of_even_hamilton_multigraph L hCycle hReg hEven⟩

end Factor

end OverfullWork.EvenHamiltonFactorization

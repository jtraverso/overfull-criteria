module

public import OverfullWork.OsthusStadenBalancedArcSupport

@[expose] public section


/-! Add the H2 selections without changing the ordinary successor
pairs used for the regular extraction of §5.10. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical

/-- Data for the regular extraction in §5.10. The ordinary graph
is kept apart from the red arc set, with exact degrees on the latter. -/
structure OsthusStadenBalancedLayerProperties {L U V : Type*} [Fintype V]
    (G : Digraph V) (H ordinaryArcs : L → Digraph V) (redArcs : L → Finset (V × V))
    (ordinary : L → Finset V) (cell : L → U → Finset V) (label : L → V → Option U)
    (factor : L → Equiv.Perm U) (κ : ℕ) (cap δ d : ℝ) : Prop where
  le : ∀ j, H j ≤ G
  disjoint_layers : ∀ j k, j ≠ k → Disjoint (H j) (H k)
  decomposition : ∀ j, H j = ordinaryArcs j ⊔ digraphOfArcs (redArcs j)
  disjoint_parts : ∀ j, Disjoint (ordinaryArcs j) (digraphOfArcs (redArcs j))
  superregular : ∀ j u, IsSuperregularPair (ordinaryArcs j) δ d (cell j u) (cell j (factor j u))
  balance : ∀ j u, clusterArcMass (label j) (redArcs j) true u =
    clusterArcMass (label j) (redArcs j) false (factor j u)
  exceptional_degrees : ∀ j x, x ∉ ordinary j →
    inDegree (digraphOfArcs (redArcs j)) x = κ ∧ outDegree (digraphOfArcs (redArcs j)) x = κ
  ordinary_load : ∀ j (q : Bool) x, x ∈ ordinary j →
    (pairSemidegree q (digraphOfArcs (redArcs j)) x:ℝ) ≤ cap

set_option maxHeartbeats 1400000 in
/-- The full layers after balancing have a disjoint decomposition into
their original ordinary successor arcs and a balanced red arc set.
The red set has exact exceptional degrees and bounded ordinary degrees. -/
theorem balanced_physical_graphs_from_red_layers
    {L U I V : Type*} [Fintype V] {G reserve : Digraph V} {initial F : L → Digraph V}
    {factor : L → Equiv.Perm U} {ordinary : L → Finset V} {cell : L → U → Finset V}
    {red : Bool → L → Finset V} {center : L → I → V} {incoming outgoing : L → I → Finset V}
    {κ : ℕ} {cap δ d : ℝ}
    (R : OsthusStadenRedLayerProperties G reserve initial F factor ordinary cell red center incoming outgoing κ cap δ d)
    (label : L → V → Option U) (B : L → Finset (V × V)) (capBalance : ℕ)
    (hLabel : ∀ j u x, label j x = some u ↔ x ∈ cell j u)
    (hCell : ∀ j u, cell j u ⊆ ordinary j) (hReserve : reserve ≤ G)
    (hSub : ∀ j, digraphOfArcs (B j) ≤ reserve)
    (hDis : ∀ j k, j ≠ k → Disjoint (B j) (B k))
    (hEnd : ∀ j e, e ∈ B j → e.1 ∈ ordinary j ∧ e.2 ∈ ordinary j)
    (hCap : ∀ j x, inDegree (digraphOfArcs (B j)) x ≤ capBalance ∧ outDegree (digraphOfArcs (B j)) x ≤ capBalance)
    (hBalance : ∀ j u, cellExceptionalArcCount (F j) (ordinary j) (cell j u) true+
      clusterArcMass (label j) (B j) true u =
      cellExceptionalArcCount (F j) (ordinary j) (cell j (factor j u)) false+
      clusterArcMass (label j) (B j) false (factor j u)) :
    let H := fun j => F j ⊔ digraphOfArcs (B j)
    let ordinaryArcs := fun j => trimLayerArcs (F j) (ordinary j)
    let redArcs := fun j => physicalExceptionalArcs (F j) (ordinary j) ∪ B j
    OsthusStadenBalancedLayerProperties G H ordinaryArcs redArcs ordinary cell label factor κ (cap+capBalance) δ d := by
  intro H ordinaryArcs redArcs
  have hRed (j : L) := red_arc_union_after_balancing (F j) (ordinary j) (label j) (cell j) (factor j) (B j)
    (hLabel j) (hCell j) (hEnd j) (hBalance j)
  have hCross (j k : L) : Disjoint (F j) (digraphOfArcs (B k)) :=
    (R.disjoint_reserve j).mono le_rfl (hSub k)
  refine ⟨fun j => sup_le (R.le j) ((hSub j).trans hReserve),?_,?_,?_,?_,fun j => (hRed j).1,?_,?_⟩
  · intro j k hne
    rw [disjoint_iff_inf_le]
    rintro x y ⟨hj | hj,hk | hk⟩
    · exact disjoint_iff_inf_le.mp (R.disjoint_layers j k hne) ⟨hj,hk⟩
    · exact disjoint_iff_inf_le.mp (hCross j k) ⟨hj,hk⟩
    · exact disjoint_iff_inf_le.mp (hCross k j).symm ⟨hj,hk⟩
    · exact disjoint_left.mp (hDis j k hne) hj hk
  · intro j
    ext x y
    change ((F j).Adj x y ∨ (x,y) ∈ B j) ↔
      ((F j).Adj x y ∧ x ∈ ordinary j ∧ y ∈ ordinary j) ∨
        (x,y) ∈ physicalExceptionalArcs (F j) (ordinary j) ∪ B j
    simp only [mem_union,physicalExceptionalArcs,mem_filter,mem_univ,true_and]
    tauto
  · intro j
    rw [disjoint_iff_inf_le]
    rintro x y ⟨⟨he,hx,hy⟩,h⟩
    rcases mem_union.mp h with harc | hB
    · exact ((mem_filter.mp harc).2.2).elim (fun hn => hn hx) (fun hn => hn hy)
    · exact disjoint_iff_inf_le.mp (hCross j j) ⟨he,hB⟩
  · intro j u
    apply (R.superregular j u).congr_on
    intro x hx y hy
    exact ⟨fun h => ⟨h,hCell j _ hx,hCell j _ hy⟩,And.left⟩
  · intro j x hx
    have hAdj := (hRed j).2.1 x hx
    have hI : inProfile (digraphOfArcs (redArcs j)) x = inProfile (F j) x := by
      ext y
      simpa only [inProfile,mem_filter,mem_univ,true_and] using (hAdj y).2
    have hO : outProfile (digraphOfArcs (redArcs j)) x = outProfile (F j) x := by
      ext y
      simpa only [outProfile,mem_filter,mem_univ,true_and] using (hAdj y).1
    have h := R.exceptional_degrees j x hx
    exact ⟨(congrArg Finset.card hI).trans h.1,(congrArg Finset.card hO).trans h.2⟩
  · intro j q x hx
    have he := (hRed j).2.2 q x hx
    rw [he,Nat.cast_add]
    have h : (pairSemidegree q (digraphOfArcs (B j)) x:ℝ) ≤ capBalance := by
      have h' := hCap j x
      cases q
      · exact_mod_cast h'.1
      · exact_mod_cast h'.2
    exact add_le_add (R.exceptional_neighbours j x hx q) h

end OverfullWork.DirectedRobustExpansion

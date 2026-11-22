module

public import OverfullWork.OsthusStadenBlackCuts
public import OverfullWork.OsthusStadenPhysicalRedDemands
public import OverfullWork.OsthusStadenPhysicalBalance

@[expose] public section


/-! Retain the orientation and count the exceptional arcs after balancing. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical

/-- A spacing of at least three prevents a shadow source from also
being a shadow target. -/
theorem shadow_ranges_disjoint
    {U : Type*} (σ : Equiv.Perm U) (incoming outgoing : Finset U) (p : ℕ)
    (hp : 3 ≤ p)
    (hSpacing : ∀ (a b : ↥(incoming ∪ outgoing)) k, 0 < k → (σ^k) (a:U) = (b:U) → p ≤ k) :
    Disjoint (Set.range (shadowSend σ incoming outgoing)) (Set.range (shadowReceive σ incoming outgoing)) := by
  rw [Set.disjoint_left]
  rintro u ⟨a,ha⟩ ⟨b,hb⟩
  have hStep : (σ^1) (shadowSend σ incoming outgoing b) = shadowSend σ incoming outgoing a := by
    rw [pow_one]
    exact hb.trans ha.symm
  have h := shadow_starts_spaced σ incoming outgoing p hSpacing b a 1 (by decide) hStep
  omega

theorem incoming_subset_shadow_range
    {U : Type*} (σ : Equiv.Perm U) (incoming outgoing : Finset U) :
    ∀ u ∈ incoming, u ∈ Set.range (shadowReceive σ incoming outgoing) := by
  intro u hu
  refine ⟨⟨u,mem_union_left _ hu⟩,?_⟩
  simp only [shadowReceive,shadowSend,show (⟨u,mem_union_left outgoing hu⟩ :
    ↥(incoming ∪ outgoing)).val ∈ incoming from hu,if_true,Equiv.apply_symm_apply]

theorem outgoing_subset_shadow_range
    {U : Type*} (σ : Equiv.Perm U) (incoming outgoing : Finset U)
    (hDis : Disjoint incoming outgoing) :
    ∀ u ∈ outgoing, u ∈ Set.range (shadowSend σ incoming outgoing) := by
  intro u hu
  refine ⟨⟨u,mem_union_right _ hu⟩,?_⟩
  simp only [shadowSend,show (⟨u,mem_union_right incoming hu⟩ :
    ↥(incoming ∪ outgoing)).val ∉ incoming from fun h => disjoint_left.mp hDis h hu,if_false]

/-- The part of a red layer incident to its exceptional set. -/
noncomputable def physicalExceptionalArcs {V : Type*} [Fintype V]
    (F : Digraph V) (ordinary : Finset V) : Finset (V × V) :=
  univ.filter (fun e => F.Adj e.1 e.2 ∧ (e.1 ∉ ordinary ∨ e.2 ∉ ordinary))

/-- The ordinary row and column totals of the exceptional arc set
coincide with the demands used in the shadow equations. -/
theorem exceptional_arc_mass_eq_cell_demand
    {U V : Type*} [Fintype V] (F : Digraph V) (ordinary : Finset V)
    (label : V → Option U) (cell : U → Finset V)
    (hLabel : ∀ u x, label x = some u ↔ x ∈ cell u)
    (hCell : ∀ u, cell u ⊆ ordinary) (u : U) (q : Bool) :
    clusterArcMass label (physicalExceptionalArcs F ordinary) q u =
      cellExceptionalArcCount F ordinary (cell u) q := by
  cases q
  · have he :
        (physicalExceptionalArcs F ordinary).filter (fun e => label e.2 = some u) =
          (ordinaryᶜ ×ˢ cell u).filter (fun e => F.Adj e.1 e.2) := by
      ext e
      simp only [physicalExceptionalArcs,mem_filter,mem_univ,true_and,hLabel,mem_product,mem_compl]
      constructor
      · rintro ⟨⟨h,he⟩,hv⟩
        exact ⟨⟨he.resolve_right (not_not.mpr (hCell u hv)),hv⟩,h⟩
      · rintro ⟨⟨hx,hy⟩,h⟩
        exact ⟨⟨h,Or.inl hx⟩,hy⟩
    unfold clusterArcMass cellExceptionalArcCount
    simp only [Bool.false_eq_true,if_false]
    rw [he,card_filter,sum_product,sum_comm]
    apply sum_congr rfl
    intro y _
    rw [←card_filter]
    congr 1
    ext x
    simp [inProfile]
  · have he :
        (physicalExceptionalArcs F ordinary).filter (fun e => label e.1 = some u) =
          (cell u ×ˢ ordinaryᶜ).filter (fun e => F.Adj e.1 e.2) := by
      ext e
      simp only [physicalExceptionalArcs,mem_filter,mem_univ,true_and,hLabel,mem_product,mem_compl]
      constructor
      · rintro ⟨⟨h,he⟩,hu⟩
        exact ⟨⟨hu,he.resolve_left (not_not.mpr (hCell u hu))⟩,h⟩
      · rintro ⟨⟨hx,hy⟩,h⟩
        exact ⟨⟨h,Or.inr hy⟩,hx⟩
    unfold clusterArcMass cellExceptionalArcCount
    simp only [if_true]
    rw [he,card_filter,sum_product]
    apply sum_congr rfl
    intro x _
    rw [←card_filter]
    congr 1
    ext y
    simp [outProfile]

/-- Adjoin balancing arcs supported between ordinary vertices. They
preserve the exceptional incidences, and the two ordinary loads add. -/
theorem red_arc_union_after_balancing
    {U V : Type*} [Fintype V] (F : Digraph V) (ordinary : Finset V)
    (label : V → Option U) (cell : U → Finset V) (σ : Equiv.Perm U)
    (B : Finset (V × V))
    (hLabel : ∀ u x, label x = some u ↔ x ∈ cell u) (hCell : ∀ u, cell u ⊆ ordinary)
    (hEnds : ∀ e ∈ B, e.1 ∈ ordinary ∧ e.2 ∈ ordinary)
    (hBalance : ∀ u,
      cellExceptionalArcCount F ordinary (cell u) true+clusterArcMass label B true u =
      cellExceptionalArcCount F ordinary (cell (σ u)) false+clusterArcMass label B false (σ u)) :
    let A := physicalExceptionalArcs F ordinary ∪ B
    (∀ u, clusterArcMass label A true u = clusterArcMass label A false (σ u)) ∧
      (∀ x, x ∉ ordinary → ∀ y,
        ((digraphOfArcs A).Adj x y ↔ F.Adj x y) ∧ ((digraphOfArcs A).Adj y x ↔ F.Adj y x)) ∧
      ∀ (q : Bool) (x : V), x ∈ ordinary →
        pairSemidegree q (digraphOfArcs A) x =
          (ordinaryᶜ ∩ (if q then outProfile F x else inProfile F x)).card+
          pairSemidegree q (digraphOfArcs B) x := by
  intro A
  have hDis : Disjoint (physicalExceptionalArcs F ordinary) B := by
    apply disjoint_left.mpr
    intro e h h'
    exact ((mem_filter.mp h).2.2).elim (fun h => h (hEnds e h').1) (fun h => h (hEnds e h').2)
  refine ⟨?_,?_,?_⟩
  · intro u
    unfold clusterArcMass at *
    dsimp only [A]
    rw [filter_union,filter_union,card_union_of_disjoint (hDis.mono (filter_subset _ _) (filter_subset _ _)),
      card_union_of_disjoint (hDis.mono (filter_subset _ _) (filter_subset _ _))]
    change clusterArcMass label (physicalExceptionalArcs F ordinary) true u+clusterArcMass label B true u =
      clusterArcMass label (physicalExceptionalArcs F ordinary) false (σ u)+clusterArcMass label B false (σ u)
    rw [exceptional_arc_mass_eq_cell_demand F ordinary label cell hLabel hCell,
      exceptional_arc_mass_eq_cell_demand F ordinary label cell hLabel hCell]
    exact hBalance u
  · intro x hx y
    constructor
    · refine ⟨?_,fun h => mem_union_left _ (mem_filter.mpr ⟨mem_univ _,h,Or.inl hx⟩)⟩
      intro h
      rcases mem_union.mp h with h | h
      · exact (mem_filter.mp h).2.1
      · exact (hx (hEnds _ h).1).elim
    · refine ⟨?_,fun h => mem_union_left _ (mem_filter.mpr ⟨mem_univ _,h,Or.inr hx⟩)⟩
      intro h
      rcases mem_union.mp h with h | h
      · exact (mem_filter.mp h).2.1
      · exact (hx (hEnds _ h).2).elim
  · intro q x hx
    have hProfile : (if q then outProfile (digraphOfArcs A) x else inProfile (digraphOfArcs A) x) =
        (ordinaryᶜ ∩ (if q then outProfile F x else inProfile F x)) ∪
        (if q then outProfile (digraphOfArcs B) x else inProfile (digraphOfArcs B) x) := by
      ext y
      let e : V × V := if q then (x,y) else (y,x)
      have hMem (J : Digraph V) : y ∈ (if q then outProfile J x else inProfile J x) ↔ J.Adj e.1 e.2 := by
        cases q
        · exact ⟨fun h => (mem_filter.mp h).2,fun h => mem_filter.mpr ⟨mem_univ _,h⟩⟩
        · exact ⟨fun h => (mem_filter.mp h).2,fun h => mem_filter.mpr ⟨mem_univ _,h⟩⟩
      simp only [mem_union,mem_inter,mem_compl,hMem,digraphOfArcs,A,physicalExceptionalArcs,
        mem_filter,mem_univ,true_and]
      cases q <;> simp [e,hx,and_comm]
    have hLocal : Disjoint (ordinaryᶜ ∩ (if q then outProfile F x else inProfile F x))
        (if q then outProfile (digraphOfArcs B) x else inProfile (digraphOfArcs B) x) := by
      apply disjoint_left.mpr
      intro y hy hy'
      have hyNot := mem_compl.mp (mem_inter.mp hy).1
      cases q
      · exact hyNot (hEnds (y,x) (mem_filter.mp hy').2).1
      · exact hyNot (hEnds (x,y) (mem_filter.mp hy').2).2
    have h := congrArg Finset.card hProfile
    rw [card_union_of_disjoint hLocal] at h
    cases q <;> exact h

end OverfullWork.DirectedRobustExpansion

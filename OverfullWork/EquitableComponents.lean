module

public import OverfullWork.ColourBalance

@[expose] public section


/-! # Two-colour components, counting parallel copies exactly -/

namespace SimpleGraph.MultiGraph.EdgeColoring

open Finset SimpleGraph
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}

def twoColourGraph (C : M.EdgeColoring k) (a b : Fin k) : SimpleGraph V where
  Adj u v := u≠v ∧ 0<C.col s(u,v) a+C.col s(u,v) b
  symm := ⟨by intro u v h; simpa only [Sym2.eq_swap] using And.intro h.1.symm h.2⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

noncomputable instance (C : M.EdgeColoring k) (a b : Fin k) :
    DecidableRel (C.twoColourGraph a b).Adj := Classical.decRel _

noncomputable instance (C : M.EdgeColoring k) (a b : Fin k) :
    Fintype (C.twoColourGraph a b).ConnectedComponent := Fintype.ofFinite _

def colourMass (C : M.EdgeColoring k) (i : Fin k) : ℕ := (C.colourGraph i).edgeCount

noncomputable def componentSet (C : M.EdgeColoring k) (a b : Fin k)
    (z : (C.twoColourGraph a b).ConnectedComponent) : Finset V := z.supp.toFinset

theorem twoColourGraph_edgeFinset (C : M.EdgeColoring k) (a b : Fin k) :
    (C.twoColourGraph a b).edgeFinset = univ.filter (fun e => 0<C.col e a+C.col e b) := by
  ext e
  induction e using Sym2.inductionOn with
  | hf u v =>
    rw [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet]
    simp only [mem_filter,mem_univ,true_and]
    change (u≠v ∧ 0<C.col s(u,v) a+C.col s(u,v) b) ↔ _
    constructor
    · exact And.right
    · intro h
      refine ⟨?_,h⟩
      intro he
      subst v
      have h₁ := col_eq_zero_of_isDiag M C (by simp : (s(u,u)).IsDiag) a
      have h₂ := col_eq_zero_of_isDiag M C (by simp : (s(u,u)).IsDiag) b
      omega

theorem colourGraph_degree_le_one (C : M.EdgeColoring k) (i : Fin k) (v : V) :
    (C.colourGraph i).degree v≤1 := C.proper v i

theorem twice_colour_edgesWithin_le (C : M.EdgeColoring k) (i : Fin k) (S : Finset V) :
    2*(C.colourGraph i).edgesWithin S≤S.card := by
  have h := (C.colourGraph i).twiceInternal_le_degree_sum S
  rw [twiceInternal_eq] at h
  calc
    _ ≤ ∑ v ∈ S, (C.colourGraph i).degree v := h
    _ ≤ ∑ _v ∈ S, 1 := sum_le_sum (fun v _ => C.colourGraph_degree_le_one i v)
    _ = _ := by simp

theorem twoColour_edgesWithin_le (C : M.EdgeColoring k) (a b : Fin k) (S : Finset V) :
    ((C.twoColourGraph a b).edgeFinset.filter (fun e => e.toFinset⊆S)).card ≤
      (C.colourGraph a).edgesWithin S+(C.colourGraph b).edgesWithin S := by
  rw [twoColourGraph_edgeFinset]
  simp only [edgesWithin,edgeCount,restrict,colourGraph]
  rw [←sum_add_distrib,card_eq_sum_ones,sum_filter,sum_filter]
  apply sum_le_sum
  intro e _
  by_cases he : e.toFinset⊆S <;> by_cases hp : 0<C.col e a+C.col e b <;> simp [he,hp] <;> omega

theorem component_size_bound (C : M.EdgeColoring k) (a b : Fin k)
    (z : (C.twoColourGraph a b).ConnectedComponent) :
    (C.componentSet a b z).card ≤
      (C.colourGraph a).edgesWithin (C.componentSet a b z)+
      (C.colourGraph b).edgesWithin (C.componentSet a b z)+1 := by
  have hs : (↑(C.componentSet a b z) : Set V)=z.supp := by ext; simp [componentSet]
  have hconnS : ((C.twoColourGraph a b).induce (↑(C.componentSet a b z) : Set V)).Connected := by
    rw [hs]
    exact z.connected_toSimpleGraph
  have hconn := hconnS.card_vert_le_card_edgeSet_add_one
  have hcard : (C.componentSet a b z).card ≤
      ((C.twoColourGraph a b).induce (↑(C.componentSet a b z) : Set V)).edgeFinset.card+1 := by
    simpa only [Nat.card_eq_fintype_card,←edgeFinset_card,Finset.coe_sort_coe,Fintype.card_coe] using hconn
  have he := C.twoColour_edgesWithin_le a b (C.componentSet a b z)
  rw [(C.twoColourGraph a b).card_filter_edgeFinset_toFinset_subset] at he
  omega

theorem component_colour_balance (C : M.EdgeColoring k) (a b : Fin k)
    (z : (C.twoColourGraph a b).ConnectedComponent) :
    (C.colourGraph a).edgesWithin (C.componentSet a b z) ≤
      (C.colourGraph b).edgesWithin (C.componentSet a b z)+1 := by
  have h := C.component_size_bound a b z
  have hA := C.twice_colour_edgesWithin_le a (C.componentSet a b z)
  omega

theorem component_closed (C : M.EdgeColoring k) (a b : Fin k)
    (z : (C.twoColourGraph a b).ConnectedComponent) (u v : V)
    (hpos : 0<C.col s(u,v) a+C.col s(u,v) b) :
    (u ∈ C.componentSet a b z ↔ v ∈ C.componentSet a b z) := by
  have hadj : (C.twoColourGraph a b).Adj u v := by
    have hmem : s(u,v) ∈ (C.twoColourGraph a b).edgeFinset := by
      rw [twoColourGraph_edgeFinset]
      exact mem_filter.mpr ⟨mem_univ _,hpos⟩
    exact mem_edgeFinset.mp hmem
  have heq := ConnectedComponent.eq.mpr hadj.reachable
  change (u ∈ z.supp.toFinset ↔ v ∈ z.supp.toFinset)
  simp only [Set.mem_toFinset,ConnectedComponent.mem_supp_iff]
  rw [heq]

theorem sum_component_mass (C : M.EdgeColoring k) (a b i : Fin k) (hi : i=a ∨ i=b) :
    (∑ z : (C.twoColourGraph a b).ConnectedComponent,
      (C.colourGraph i).edgesWithin (C.componentSet a b z))=C.colourMass i := by
  simp only [edgesWithin,edgeCount,restrict,colourGraph,colourMass]
  rw [sum_comm]
  apply sum_congr rfl
  intro e _
  by_cases hz : C.col e i=0
  · simp [hz]
  induction e using Sym2.inductionOn with
  | hf u v =>
    have hp : 0<C.col s(u,v) a+C.col s(u,v) b := by rcases hi with rfl|rfl <;> omega
    let z₀ := (C.twoColourGraph a b).connectedComponentMk u
    have hu : u ∈ C.componentSet a b z₀ := by simp [componentSet,z₀]
    have hv := (C.component_closed a b z₀ u v hp).mp hu
    have hsub : s(u,v).toFinset⊆C.componentSet a b z₀ := by
      simpa only [Sym2.toFinset_mk_eq,insert_subset_iff,singleton_subset_iff] using And.intro hu hv
    rw [sum_eq_single z₀]
    · simp only [if_pos hsub]
    · intro z _ hne
      have hn : ¬s(u,v).toFinset⊆C.componentSet a b z := by
        intro h
        have hu' : u ∈ C.componentSet a b z := h (by simp)
        have he : (C.twoColourGraph a b).connectedComponentMk u=z := by
          simpa only [componentSet,Set.mem_toFinset,ConnectedComponent.mem_supp_iff] using hu'
        exact hne he.symm
      simp [hn]
    · simp

theorem exists_unit_imbalance_component (C : M.EdgeColoring k) (a b : Fin k)
    (hgap : C.colourMass b<C.colourMass a) :
    ∃ z : (C.twoColourGraph a b).ConnectedComponent,
      (C.colourGraph a).edgesWithin (C.componentSet a b z)=
        (C.colourGraph b).edgesWithin (C.componentSet a b z)+1 := by
  have hsA := C.sum_component_mass a b a (Or.inl rfl)
  have hsB := C.sum_component_mass a b b (Or.inr rfl)
  have hex : ∃ z, (C.colourGraph b).edgesWithin (C.componentSet a b z)<
      (C.colourGraph a).edgesWithin (C.componentSet a b z) := by
    by_contra hn
    push_neg at hn
    have hsum := sum_le_sum (s:=univ) (fun z _ => hn z)
    rw [hsA,hsB] at hsum
    omega
  obtain ⟨z,hz⟩ := hex
  exact ⟨z,by have hb := C.component_colour_balance a b z; omega⟩

end SimpleGraph.MultiGraph.EdgeColoring

module

public import OverfullWork.WeightedComponents

@[expose] public section


/-! # Swapping any selected family of bichromatic components -/
namespace SimpleGraph.MultiGraph.EdgeColoring
open Finset
open scoped Classical
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}

noncomputable def selectedComponentSet (C : M.EdgeColoring k) (a b : Fin k)
    (T : Finset (C.twoColourGraph a b).ConnectedComponent) : Finset V :=
  univ.filter fun v => (C.twoColourGraph a b).connectedComponentMk v∈T

theorem selected_component_closed (C : M.EdgeColoring k) (a b : Fin k)
    (T : Finset (C.twoColourGraph a b).ConnectedComponent) (u v : V)
    (hp : 0<C.col s(u,v) a+C.col s(u,v) b) :
    (u∈C.selectedComponentSet a b T ↔ v∈C.selectedComponentSet a b T) := by
  have hu : u∈C.componentSet a b ((C.twoColourGraph a b).connectedComponentMk u):=by simp [componentSet]
  have hv:=(C.component_closed a b _ u v hp).mp hu
  have he : (C.twoColourGraph a b).connectedComponentMk v=
      (C.twoColourGraph a b).connectedComponentMk u := by
    simpa only [componentSet,Set.mem_toFinset,ConnectedComponent.mem_supp_iff] using hv
  simp only [selectedComponentSet,mem_filter,mem_univ,true_and,he]

theorem sum_selected_components (C : M.EdgeColoring k) (a b : Fin k)
    (T : Finset (C.twoColourGraph a b).ConnectedComponent) (f : V → ℕ) :
    (∑ v∈C.selectedComponentSet a b T,f v)=∑ z∈T,∑ v∈C.componentSet a b z,f v := by
  have he : ∀ z,C.componentSet a b z=univ.filter
      (fun v => (C.twoColourGraph a b).connectedComponentMk v=z) := by
    intro z
    ext v
    simp only [componentSet,Set.mem_toFinset,ConnectedComponent.mem_supp_iff,
      mem_filter,mem_univ,true_and]
  simp_rw [he]
  simp only [selectedComponentSet,sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  by_cases hv : (C.twoColourGraph a b).connectedComponentMk v∈T
  · rw [if_pos hv,sum_eq_single ((C.twoColourGraph a b).connectedComponentMk v)]
    · simp only [ite_true]
    · intro z hz hne
      simp only [if_neg (Ne.symm hne)]
    · exact fun hn => False.elim (hn hv)
  · rw [if_neg hv]
    symm
    apply sum_eq_zero
    intro z hz
    have hn : (C.twoColourGraph a b).connectedComponentMk v≠z:=by
      intro heq
      exact hv (heq ▸ hz)
    simp only [if_neg hn]

noncomputable def swapSelected (C : M.EdgeColoring k) (a b : Fin k)
    (T : Finset (C.twoColourGraph a b).ConnectedComponent) : M.EdgeColoring k :=
  C.swapClosed a b (C.selectedComponentSet a b T) (C.selected_component_closed a b T)

theorem swapClosed_degree (C : M.EdgeColoring k) (a b : Fin k) (S : Finset V)
    (hclosed : ∀ u v,0<C.col s(u,v) a+C.col s(u,v) b → (u∈S ↔ v∈S))
    (v : V) (i : Fin k) :
    ((C.swapClosed a b S hclosed).colourGraph i).degree v=
      if v∈S then (C.colourGraph (Equiv.swap a b i)).degree v else (C.colourGraph i).degree v := by
  change (∑ e∈univ.filter (fun e : Sym2 V => v∈e),C.swappedCol a b S e i)=_
  by_cases hv : v∈S
  · rw [if_pos hv]
    apply sum_congr rfl
    intro e he
    rw [C.swappedCol_incident a b S hclosed e v (mem_filter.mp he).2 i,if_pos hv]
    rfl
  · rw [if_neg hv]
    apply sum_congr rfl
    intro e he
    rw [C.swappedCol_incident a b S hclosed e v (mem_filter.mp he).2 i,if_neg hv]
    rfl

theorem sum_selected_component_mass (C : M.EdgeColoring k) (a b i : Fin k)
    (T : Finset (C.twoColourGraph a b).ConnectedComponent) (hi : i=a ∨ i=b) :
    (∑ z∈T,(C.colourGraph i).edgesWithin (C.componentSet a b z))=
      (C.colourGraph i).edgesWithin (C.selectedComponentSet a b T) := by
  simp only [edgesWithin,edgeCount,restrict,colourGraph]
  rw [sum_comm]
  apply sum_congr rfl
  intro e _
  by_cases hz : C.col e i=0
  · simp [hz]
  induction e using Sym2.inductionOn with
  | hf u v =>
    have hp : 0<C.col s(u,v) a+C.col s(u,v) b:=by rcases hi with rfl|rfl <;> omega
    let z₀:=(C.twoColourGraph a b).connectedComponentMk u
    have hu : u∈C.componentSet a b z₀:=by simp [componentSet,z₀]
    have hv:=(C.component_closed a b z₀ u v hp).mp hu
    have hsub : s(u,v).toFinset⊆C.componentSet a b z₀:=by
      simpa only [Sym2.toFinset_mk_eq,insert_subset_iff,singleton_subset_iff] using And.intro hu hv
    have hncomp : ∀ z,z≠z₀ → ¬s(u,v).toFinset⊆C.componentSet a b z := by
      intro z hne hs
      have hu' : u∈C.componentSet a b z:=hs (by simp)
      have he : (C.twoColourGraph a b).connectedComponentMk u=z:=by
        simpa only [componentSet,Set.mem_toFinset,ConnectedComponent.mem_supp_iff] using hu'
      exact hne he.symm
    by_cases hT : z₀∈T
    · have huS : u∈C.selectedComponentSet a b T:=by simp only [selectedComponentSet,mem_filter,mem_univ,true_and];exact hT
      have hvS:=(C.selected_component_closed a b T u v hp).mp huS
      have hs : s(u,v).toFinset⊆C.selectedComponentSet a b T:=by
        simpa only [Sym2.toFinset_mk_eq,insert_subset_iff,singleton_subset_iff] using And.intro huS hvS
      rw [if_pos hs,sum_eq_single z₀]
      · simp only [if_pos hsub]
      · intro z _ hne
        simp only [if_neg (hncomp z hne)]
      · exact fun hn => False.elim (hn hT)
    · have hnS : ¬s(u,v).toFinset⊆C.selectedComponentSet a b T := by
        intro hs
        have huS:=hs (show u∈s(u,v).toFinset by simp)
        have huT : z₀∈T:=by simpa only [selectedComponentSet,mem_filter,mem_univ,true_and] using huS
        exact hT huT
      rw [if_neg hnS]
      apply sum_eq_zero
      intro z hzT
      have hne : z≠z₀:=fun he => hT (he ▸ hzT)
      simp only [if_neg (hncomp z hne)]

theorem swapSelected_mass_left (C : M.EdgeColoring k) (a b : Fin k)
    (T : Finset (C.twoColourGraph a b).ConnectedComponent) :
    (C.swapSelected a b T).colourMass a+
        (∑ z∈T,(C.colourGraph a).edgesWithin (C.componentSet a b z))=
      C.colourMass a+(∑ z∈T,(C.colourGraph b).edgesWithin (C.componentSet a b z)) := by
  rw [C.sum_selected_component_mass a b a T (Or.inl rfl),
    C.sum_selected_component_mass a b b T (Or.inr rfl)]
  simp only [colourMass,edgeCount,colourGraph,edgesWithin,restrict,swapSelected,swapClosed]
  rw [←sum_add_distrib,←sum_add_distrib]
  apply sum_congr rfl
  intro e _
  by_cases he : e.toFinset⊆C.selectedComponentSet a b T <;> simp [swappedCol,he] <;> omega

theorem swapSelected_mass_right (C : M.EdgeColoring k) (a b : Fin k)
    (T : Finset (C.twoColourGraph a b).ConnectedComponent) :
    (C.swapSelected a b T).colourMass b+
        (∑ z∈T,(C.colourGraph b).edgesWithin (C.componentSet a b z))=
      C.colourMass b+(∑ z∈T,(C.colourGraph a).edgesWithin (C.componentSet a b z)) := by
  rw [C.sum_selected_component_mass a b a T (Or.inl rfl),
    C.sum_selected_component_mass a b b T (Or.inr rfl)]
  simp only [colourMass,edgeCount,colourGraph,edgesWithin,restrict,swapSelected,swapClosed]
  rw [←sum_add_distrib,←sum_add_distrib]
  apply sum_congr rfl
  intro e _
  by_cases he : e.toFinset⊆C.selectedComponentSet a b T <;> simp [swappedCol,he] <;> omega

theorem swapSelected_mass_other (C : M.EdgeColoring k) (a b : Fin k)
    (T : Finset (C.twoColourGraph a b).ConnectedComponent) (i : Fin k)
    (ha : i≠a) (hb : i≠b) :
    (C.swapSelected a b T).colourMass i=C.colourMass i := by
  simp only [colourMass,edgeCount,colourGraph,swapSelected,swapClosed,swappedCol,
    Equiv.swap_apply_of_ne_of_ne ha hb,ite_self]

theorem swapSelected_mass_preserved (C : M.EdgeColoring k) (a b : Fin k)
    (T : Finset (C.twoColourGraph a b).ConnectedComponent)
    (hbal : (∑ z∈T,(C.colourGraph a).edgesWithin (C.componentSet a b z))=
      ∑ z∈T,(C.colourGraph b).edgesWithin (C.componentSet a b z)) :
    ∀ i,(C.swapSelected a b T).colourMass i=C.colourMass i := by
  intro i
  by_cases hi : i=a
  · subst i
    have hh:=C.swapSelected_mass_left a b T
    omega
  · by_cases hj : i=b
    · subst i
      have hh:=C.swapSelected_mass_right a b T
      omega
    · exact C.swapSelected_mass_other a b T i hi hj

/-- Vertex-weight accounting for an arbitrary closed swap set. -/
theorem swapClosed_weighted_sum (C : M.EdgeColoring k) (w : V → ℕ) (a b : Fin k)
    (S : Finset V)
    (hclosed : ∀ u v,0<C.col s(u,v) a+C.col s(u,v) b → (u∈S ↔ v∈S)) (i : Fin k) :
    (∑ v : V,w v*((C.swapClosed a b S hclosed).colourGraph i).degree v)+
        (∑ v∈S,w v*(C.colourGraph i).degree v)=
      (∑ v : V,w v*(C.colourGraph i).degree v)+
        (∑ v∈S,w v*(C.colourGraph (Equiv.swap a b i)).degree v) := by
  have hpoint : ∀ v : V,
      w v*((C.swapClosed a b S hclosed).colourGraph i).degree v+
          (if v∈S then w v*(C.colourGraph i).degree v else 0)=
        w v*(C.colourGraph i).degree v+
          (if v∈S then w v*(C.colourGraph (Equiv.swap a b i)).degree v else 0) := by
    intro v
    rw [C.swapClosed_degree a b S hclosed v i]
    by_cases hv : v∈S <;> simp only [hv,if_true,if_false] <;> omega
  have hh : (∑ v : V,(w v*((C.swapClosed a b S hclosed).colourGraph i).degree v+
      (if v∈S then w v*(C.colourGraph i).degree v else 0)))=
      ∑ v : V,(w v*(C.colourGraph i).degree v+
        (if v∈S then w v*(C.colourGraph (Equiv.swap a b i)).degree v else 0)) :=
    sum_congr rfl (fun v _ => hpoint v)
  simpa only [sum_add_distrib,←sum_filter,filter_mem_eq_inter,univ_inter] using hh

/-- Generic selected-component load identity. Unfolding weightedLoad and
componentLoad turns this into the corresponding named load identity. -/
theorem swapSelected_weighted_sum (C : M.EdgeColoring k) (w : V → ℕ) (a b : Fin k)
    (T : Finset (C.twoColourGraph a b).ConnectedComponent) (i : Fin k) :
    (∑ v : V,w v*((C.swapSelected a b T).colourGraph i).degree v)+
        (∑ z∈T,∑ v∈C.componentSet a b z,w v*(C.colourGraph i).degree v)=
      (∑ v : V,w v*(C.colourGraph i).degree v)+
        (∑ z∈T,∑ v∈C.componentSet a b z,w v*(C.colourGraph (Equiv.swap a b i)).degree v) := by
  rw [←C.sum_selected_components a b T (fun v => w v*(C.colourGraph i).degree v),
    ←C.sum_selected_components a b T (fun v => w v*(C.colourGraph (Equiv.swap a b i)).degree v)]
  exact C.swapClosed_weighted_sum w a b _ _ i

theorem swapSelected_load_left (C : M.EdgeColoring k) (w : V → ℕ) (a b : Fin k)
    (T : Finset (C.twoColourGraph a b).ConnectedComponent) :
    (C.swapSelected a b T).weightedLoad w a+(∑ z∈T,C.componentLoad w a b z a)=
      C.weightedLoad w a+(∑ z∈T,C.componentLoad w a b z b) := by
  simpa only [weightedLoad,componentLoad,Equiv.swap_apply_left] using
    C.swapSelected_weighted_sum w a b T a

theorem swapSelected_load_right (C : M.EdgeColoring k) (w : V → ℕ) (a b : Fin k)
    (T : Finset (C.twoColourGraph a b).ConnectedComponent) :
    (C.swapSelected a b T).weightedLoad w b+(∑ z∈T,C.componentLoad w a b z b)=
      C.weightedLoad w b+(∑ z∈T,C.componentLoad w a b z a) := by
  simpa only [weightedLoad,componentLoad,Equiv.swap_apply_right] using
    C.swapSelected_weighted_sum w a b T b

theorem swapSelected_load_other (C : M.EdgeColoring k) (w : V → ℕ) (a b : Fin k)
    (T : Finset (C.twoColourGraph a b).ConnectedComponent) (i : Fin k)
    (ha : i≠a) (hb : i≠b) :
    (C.swapSelected a b T).weightedLoad w i=C.weightedLoad w i := by
  have hh:=C.swapSelected_weighted_sum w a b T i
  rw [Equiv.swap_apply_of_ne_of_ne ha hb] at hh
  change (C.swapSelected a b T).weightedLoad w i+_ = C.weightedLoad w i+_ at hh
  omega

end SimpleGraph.MultiGraph.EdgeColoring

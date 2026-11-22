module

public import OverfullWork.EquitableComponents

@[expose] public section


/-!
# Kempe recolouring and equitable colourings in the multiplicity model

All copies stay coloured. Finite descent of the sum of squared class
sizes preserves the original palette and handles parallel edges.
-/

namespace SimpleGraph.MultiGraph.EdgeColoring

open Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}

def swappedCol (C : M.EdgeColoring k) (a b : Fin k) (S : Finset V)
    (e : Sym2 V) (i : Fin k) : ℕ :=
  if e.toFinset⊆S then C.col e (Equiv.swap a b i) else C.col e i

theorem zero_on_boundary (C : M.EdgeColoring k) (a b : Fin k) (S : Finset V)
    (hclosed : ∀ u v, 0<C.col s(u,v) a+C.col s(u,v) b → (u∈S ↔ v∈S))
    (e : Sym2 V) (v : V) (hv : v∈e) (hS : v∈S) (hn : ¬e.toFinset⊆S) :
    C.col e a=0 ∧ C.col e b=0 := by
  have hz : C.col e a+C.col e b=0 := by
    by_contra hp
    have hpos : 0<C.col e a+C.col e b := by omega
    apply hn
    induction e using Sym2.inductionOn with
    | hf u w =>
      have hc := hclosed u w hpos
      have hm : u∈S ∧ w∈S := by
        rcases Sym2.mem_iff.mp hv with rfl|rfl
        · exact ⟨hS,hc.mp hS⟩
        · exact ⟨hc.mpr hS,hS⟩
      simpa only [Sym2.toFinset_mk_eq,insert_subset_iff,singleton_subset_iff] using hm
  omega

theorem swappedCol_incident (C : M.EdgeColoring k) (a b : Fin k) (S : Finset V)
    (hclosed : ∀ u v, 0<C.col s(u,v) a+C.col s(u,v) b → (u∈S ↔ v∈S))
    (e : Sym2 V) (v : V) (hv : v∈e) (i : Fin k) :
    C.swappedCol a b S e i = if v∈S then C.col e (Equiv.swap a b i) else C.col e i := by
  by_cases hS : v∈S
  · rw [if_pos hS]
    unfold swappedCol
    by_cases he : e.toFinset⊆S
    · rw [if_pos he]
    · rw [if_neg he]
      obtain ⟨ha,hb⟩ := C.zero_on_boundary a b S hclosed e v hv hS he
      by_cases hi : i=a
      · subst i; simp [ha,hb]
      · by_cases hj : i=b
        · subst i; simp [ha,hb]
        · rw [Equiv.swap_apply_of_ne_of_ne hi hj]
  · have he : ¬e.toFinset⊆S := fun h => hS (h (by simpa using hv))
    simp only [swappedCol,if_neg he,if_neg hS]

def swapClosed (C : M.EdgeColoring k) (a b : Fin k) (S : Finset V)
    (hclosed : ∀ u v, 0<C.col s(u,v) a+C.col s(u,v) b → (u∈S ↔ v∈S)) :
    M.EdgeColoring k where
  col := C.swappedCol a b S
  sum_col e := by
    by_cases he : e.toFinset⊆S
    · simp only [swappedCol,if_pos he]
      exact (Fintype.sum_equiv (Equiv.swap a b) _ _ (fun _ => rfl)).trans (C.sum_col e)
    · simpa only [swappedCol,if_neg he] using C.sum_col e
  proper v i := by
    have heq : (∑ e ∈ univ.filter (fun e : Sym2 V => v∈e), C.swappedCol a b S e i) =
        if v∈S then ∑ e ∈ univ.filter (fun e : Sym2 V => v∈e), C.col e (Equiv.swap a b i)
        else ∑ e ∈ univ.filter (fun e : Sym2 V => v∈e), C.col e i := by
      by_cases hv : v∈S
      · rw [if_pos hv]
        exact sum_congr rfl (fun e he => by
          rw [C.swappedCol_incident a b S hclosed e v (mem_filter.mp he).2 i,if_pos hv])
      · rw [if_neg hv]
        exact sum_congr rfl (fun e he => by
          rw [C.swappedCol_incident a b S hclosed e v (mem_filter.mp he).2 i,if_neg hv])
    rw [heq]
    split_ifs
    · exact C.proper v (Equiv.swap a b i)
    · exact C.proper v i

noncomputable def swapComponent (C : M.EdgeColoring k) (a b : Fin k)
    (z : (C.twoColourGraph a b).ConnectedComponent) : M.EdgeColoring k :=
  C.swapClosed a b (C.componentSet a b z) (C.component_closed a b z)

theorem swapComponent_mass_left (C : M.EdgeColoring k) (a b : Fin k)
    (z : (C.twoColourGraph a b).ConnectedComponent) :
    (C.swapComponent a b z).colourMass a+(C.colourGraph a).edgesWithin (C.componentSet a b z)=
      C.colourMass a+(C.colourGraph b).edgesWithin (C.componentSet a b z) := by
  simp only [colourMass,edgeCount,colourGraph,edgesWithin,restrict,swapComponent,swapClosed]
  rw [←sum_add_distrib,←sum_add_distrib]
  apply sum_congr rfl
  intro e _
  by_cases he : e.toFinset⊆C.componentSet a b z <;> simp [swappedCol,he] <;> omega

theorem swapComponent_mass_right (C : M.EdgeColoring k) (a b : Fin k)
    (z : (C.twoColourGraph a b).ConnectedComponent) :
    (C.swapComponent a b z).colourMass b+(C.colourGraph b).edgesWithin (C.componentSet a b z)=
      C.colourMass b+(C.colourGraph a).edgesWithin (C.componentSet a b z) := by
  simp only [colourMass,edgeCount,colourGraph,edgesWithin,restrict,swapComponent,swapClosed]
  rw [←sum_add_distrib,←sum_add_distrib]
  apply sum_congr rfl
  intro e _
  by_cases he : e.toFinset⊆C.componentSet a b z <;> simp [swappedCol,he] <;> omega

theorem swapComponent_mass_other (C : M.EdgeColoring k) (a b : Fin k)
    (z : (C.twoColourGraph a b).ConnectedComponent) (i : Fin k) (ha : i≠a) (hb : i≠b) :
    (C.swapComponent a b z).colourMass i=C.colourMass i := by
  simp only [colourMass,edgeCount,colourGraph,swapComponent,swapClosed,swappedCol,
    Equiv.swap_apply_of_ne_of_ne ha hb,ite_self]

def energy (C : M.EdgeColoring k) : ℕ := ∑ i, (C.colourMass i)^2

def IsEquitable (C : M.EdgeColoring k) : Prop := ∀ a b, C.colourMass a≤C.colourMass b+1

theorem sum_two_erase (f : Fin k → ℕ) (a b : Fin k) (hab : a≠b) :
    (∑ i, f i)=f a+f b+∑ i ∈ (univ.erase a).erase b, f i := by
  have hA := sum_erase_add univ f (mem_univ a)
  have hB := sum_erase_add (univ.erase a) f (mem_erase.mpr ⟨hab.symm,mem_univ b⟩)
  omega

theorem exists_energy_drop (C : M.EdgeColoring k) (hbad : ¬C.IsEquitable) :
    ∃ B : M.EdgeColoring k, B.energy<C.energy := by
  obtain ⟨a,b,hgap⟩ : ∃ a b, C.colourMass b+1<C.colourMass a := by
    simpa only [IsEquitable,not_forall,not_le] using hbad
  have hab : a≠b := by intro h; subst b; omega
  obtain ⟨z,hz⟩ := C.exists_unit_imbalance_component a b (by omega)
  let B := C.swapComponent a b z
  have hA := C.swapComponent_mass_left a b z
  have hB := C.swapComponent_mass_right a b z
  have hdA : B.colourMass a+1=C.colourMass a := by dsimp [B]; omega
  have hdB : B.colourMass b=C.colourMass b+1 := by dsimp [B]; omega
  have hdrop : (B.colourMass a)^2+(B.colourMass b)^2<
      (C.colourMass a)^2+(C.colourMass b)^2 := by nlinarith
  have hrest : (∑ i ∈ (univ.erase a).erase b, (B.colourMass i)^2)=
      ∑ i ∈ (univ.erase a).erase b, (C.colourMass i)^2 := by
    apply sum_congr rfl
    intro i hi
    have hi' := mem_erase.mp hi
    have hi'' := mem_erase.mp hi'.2
    rw [C.swapComponent_mass_other a b z i hi''.1 hi'.1]
  refine ⟨B,?_⟩
  unfold energy
  rw [sum_two_erase _ a b hab,sum_two_erase _ a b hab,hrest]
  omega

/-- Every proper multigraph colouring can be balanced on the same palette.
No equitability or recolouring hypothesis is assumed. -/
theorem exists_equitable (C : M.EdgeColoring k) :
    ∃ B : M.EdgeColoring k, B.IsEquitable := by
  induction hn : C.energy using Nat.strong_induction_on generalizing C with
  | h n ih =>
    by_cases hC : C.IsEquitable
    · exact ⟨C,hC⟩
    · obtain ⟨B,hB⟩ := C.exists_energy_drop hC
      exact ih B.energy (hn ▸ hB) B rfl

end SimpleGraph.MultiGraph.EdgeColoring

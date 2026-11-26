module

public import OverfullWork.ChenShanPathImbalance

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

variable {V : Type*}

noncomputable def pathInternalVertices {l : ℕ} (f : Fin (l+1) ↪ V) : Finset V :=
  ((univ.erase 0).erase (Fin.last l)).map f

theorem mem_pathInternalVertices {l : ℕ} (f : Fin (l+1) ↪ V) (v : V) :
    v ∈ pathInternalVertices f ↔ ∃ i, i ≠ 0 ∧ i ≠ Fin.last l ∧ f i = v := by
  simp only [pathInternalVertices,mem_map,mem_erase,mem_univ,and_true,and_assoc]
  constructor
  · rintro ⟨i,hL,h0,hf⟩; exact ⟨i,h0,hL,hf⟩
  · rintro ⟨i,h0,hL,hf⟩; exact ⟨i,hL,h0,hf⟩

theorem card_pathInternalVertices_le_three {l : ℕ} (f : Fin (l+1) ↪ V)
    (hLength : l ≤ 4) (hNe : f 0 ≠ f (Fin.last l)) :
    (pathInternalVertices f).card ≤ 3 := by
  have hLast : (Fin.last l : Fin (l+1)) ≠ 0 := fun h => hNe (congrArg f h.symm)
  have hMem : Fin.last l ∈ (univ : Finset (Fin (l+1))).erase 0 :=
    mem_erase.mpr ⟨hLast,mem_univ _⟩
  rw [pathInternalVertices,card_map,card_erase_of_mem hMem,card_erase_of_mem (mem_univ _),
    card_univ,Fintype.card_fin]
  omega

theorem incidentDegree_path_eq {l : ℕ} (f : Fin (l+1) ↪ V)
    (hNe : f 0 ≠ f (Fin.last l)) (v : V) :
    incidentDegree (directedPathArcs l f) v =
      2*(if v ∈ pathInternalVertices f then 1 else 0) +
      (if v = f 0 ∨ v = f (Fin.last l) then 1 else 0) := by
  have hDegree := incidentDegree_directedPathArcs l f v
  by_cases hStart : v = f 0
  · subst v
    have hi : f 0 ∉ pathInternalVertices f := by
      intro h
      obtain ⟨i,hi,_,hEq⟩ := (mem_pathInternalVertices f _).mp h
      exact hi (f.injective hEq)
    simp only [hi,ite_false,true_or,ite_true,Nat.mul_zero,zero_add]
    simp only [show f (Fin.last l) ≠ f 0 from Ne.symm hNe,ite_false,ite_true,add_zero] at hDegree
    have hExists : ∃ i, f i = f 0 := ⟨0,rfl⟩
    simp only [hExists,ite_true] at hDegree
    omega
  by_cases hEnd : v = f (Fin.last l)
  · subst v
    have hi : f (Fin.last l) ∉ pathInternalVertices f := by
      intro h
      obtain ⟨i,_,hi,hEq⟩ := (mem_pathInternalVertices f _).mp h
      exact hi (f.injective hEq)
    simp only [hi,ite_false,or_true,ite_true,Nat.mul_zero,zero_add]
    have hExists : ∃ i, f i = f (Fin.last l) := ⟨Fin.last l,rfl⟩
    simp only [hNe,hExists,ite_false,ite_true,zero_add] at hDegree
    omega
  have hi : v ∈ pathInternalVertices f ↔ ∃ i, f i = v := by
    rw [mem_pathInternalVertices]
    constructor
    · rintro ⟨i,_,_,hi⟩
      exact ⟨i,hi⟩
    · rintro ⟨i,hi⟩
      refine ⟨i,?_,?_,hi⟩
      · rintro rfl; exact hStart hi.symm
      · rintro rfl; exact hEnd hi.symm
  simpa only [Ne.symm hStart,Ne.symm hEnd,hStart,hEnd,false_or,ite_false,zero_add,add_zero,hi]
    using hDegree

theorem natAbs_arcDivergence_delete_path {G : Finset (V × V)} {l : ℕ}
    (f : Fin (l+1) ↪ V) (hf : directedPathArcs l f ⊆ G)
    (hStart : 0 < arcDivergence G (f 0)) (hEnd : arcDivergence G (f (Fin.last l)) < 0)
    (v : V) :
    (arcDivergence (G \ directedPathArcs l f) v).natAbs +
      (if v = f 0 ∨ v = f (Fin.last l) then 1 else 0) =
      (arcDivergence G v).natAbs := by
  have hNe : f 0 ≠ f (Fin.last l) := by
    intro h
    rw [h] at hStart
    omega
  rw [arcDivergence_sdiff hf,arcDivergence_directedPathArcs]
  by_cases hu : v = f 0
  · subst v
    simp only [Ne.symm hNe,ite_false,ite_true,true_or,sub_zero]
    omega
  by_cases hv : v = f (Fin.last l)
  · subst v
    simp only [hNe,ite_false,ite_true,or_true,zero_sub]
    omega
  · simp [hu,hv,Ne.symm hu,Ne.symm hv]

theorem incidentDegree_union_disjoint {P Q : Finset (V × V)} (h : Disjoint P Q) (v : V) :
    incidentDegree (P ∪ Q) v = incidentDegree P v + incidentDegree Q v := by
  unfold incidentDegree
  rw [filter_union,card_union_of_disjoint]
  exact h.mono (filter_subset _ _) (filter_subset _ _)

end OverfullWork.ChenShan

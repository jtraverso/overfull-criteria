module

public import OverfullWork.CMSOperation41ProjectedLayers

@[expose] public section


/-! The retained cyclic positions give the physical round graph.
Missing positions break the cycle and its degree records count exactly
the two incidences adjacent to each cyclic vertex. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def markedCycle {n : ℕ} (A : Finset (Fin (n+3))) : SimpleGraph (Fin (n+3)) where
  Adj i j := (i ∈ A ∧ finRotate (n+3) i = j) ∨ (j ∈ A ∧ finRotate (n+3) j = i)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun i h => by
    have hi : i ∈ (finRotate (n+3)).support := by rw [support_finRotate_of_le (by omega)]; simp
    exact (Equiv.Perm.mem_support.mp hi) (h.elim And.right And.right)⟩

theorem markedCycle_le_cycleGraph {n : ℕ} (A : Finset (Fin (n+3))) :
    markedCycle A ≤ cycleGraph (n+3) := by
  intro i j h
  change (i ∈ A ∧ (finRotate (n+3)) i = j) ∨ (j ∈ A ∧ (finRotate (n+3)) j = i) at h
  rcases h with ⟨_,he⟩|⟨_,he⟩
  · exact cycleGraph_adj.mpr (Or.inr (by simpa only [sub_eq_iff_eq_add',←finRotate_apply] using he.symm))
  · exact cycleGraph_adj.mpr (Or.inl (by simpa only [sub_eq_iff_eq_add',←finRotate_apply] using he.symm))

theorem markedCycle_le_pathGraph_of_no_closing {n : ℕ} (A : Finset (Fin (n+3)))
    (hLast : Fin.last (n+2) ∉ A) : markedCycle A ≤ pathGraph (n+3) := by
  have hStep (i : Fin (n+3)) (hi : i ∈ A) :
      (finRotate (n+3) i).val = i.val+1 := by
    have hne : i ≠ Fin.last (n+2) := fun h => hLast (h ▸ hi)
    exact coe_finRotate_of_ne_last hne
  intro i j h
  change (i ∈ A ∧ (finRotate (n+3)) i = j) ∨ (j ∈ A ∧ (finRotate (n+3)) j = i) at h
  rcases h with ⟨hi,rfl⟩|⟨hj,hj'⟩
  · exact pathGraph_adj.mpr (Or.inl (hStep i hi).symm)
  · exact pathGraph_adj.mpr (Or.inr (by rw [←hj',hStep j hj]))

theorem markedCycle_degree {n : ℕ} (A : Finset (Fin (n+3))) (i : Fin (n+3)) :
    (markedCycle A).degree i = (if i ∈ A then 1 else 0)+
      (if (finRotate (n+3)).symm i ∈ A then 1 else 0) := by
  let σ := finRotate (n+3)
  have hNe : σ i ≠ σ.symm i := by
    have hCard : ({i-1,i+1} : Finset (Fin (n+3))).card = 2 := by
      rw [←cycleGraph_neighborFinset,card_neighborFinset_eq_degree,cycleGraph_degree_three_le]
    have hPred : σ.symm i = i-1 := finRotate_symm_apply i
    have hSucc : σ i = i+1 := finRotate_apply i
    intro he
    rw [hPred,hSucc] at he
    rw [he,insert_eq_of_mem (mem_singleton_self _),card_singleton] at hCard
    omega
  let N₁ : Finset (Fin (n+3)) := if i ∈ A then {σ i} else ∅
  let N₂ : Finset (Fin (n+3)) := if σ.symm i ∈ A then {σ.symm i} else ∅
  have hN : (markedCycle A).neighborFinset i = N₁ ∪ N₂ := by
    ext j
    rw [mem_neighborFinset,mem_union]
    change (i ∈ A ∧ σ i = j) ∨ (j ∈ A ∧ σ j = i) ↔ j ∈ N₁ ∨ j ∈ N₂
    have hOne : j ∈ N₁ ↔ i ∈ A ∧ σ i = j := by
      by_cases h : i ∈ A <;> simp [N₁,h,eq_comm]
    have hTwo : j ∈ N₂ ↔ j ∈ A ∧ σ j = i := by
      by_cases h : σ.symm i ∈ A
      · rw [show N₂ = {σ.symm i} by simp [N₂,h],mem_singleton]
        exact ⟨fun he => ⟨he.symm ▸ h,by rw [he,Equiv.apply_symm_apply]⟩,
          fun hh => σ.injective (hh.2.trans (σ.apply_symm_apply i).symm)⟩
      · rw [show N₂ = ∅ by simp [N₂,h]]
        simp only [notMem_empty,false_iff,not_and]
        intro hj he
        have he' : j = σ.symm i := σ.injective (he.trans (σ.apply_symm_apply i).symm)
        exact h (he' ▸ hj)
    rw [hOne,hTwo]
  have hDisjoint : Disjoint N₁ N₂ := by
    by_cases h₁ : i ∈ A <;> by_cases h₂ : σ.symm i ∈ A <;>
      simp [N₁,N₂,h₁,h₂,hNe]
  rw [←card_neighborFinset_eq_degree,hN,card_union_of_disjoint hDisjoint]
  have hCard₁ : N₁.card = if i ∈ A then 1 else 0 := by
    by_cases h : i ∈ A <;> simp [N₁,h]
  have hCard₂ : N₂.card = if σ.symm i ∈ A then 1 else 0 := by
    by_cases h : σ.symm i ∈ A <;> simp only [N₂,h,if_true,if_false,card_singleton,card_empty]
  rw [hCard₁,hCard₂]

/-- Project all physically retained edges to their original endpoints,
obtain the two-colour layer and compute all removal degrees. -/
theorem physical_layer_of_marked_cycle (G : SimpleGraph V) {n : ℕ}
    (w : Fin (n+3) ↪ V) (A : Finset (Fin (n+3)))
    (hEdges : ∀ i ∈ A,G.Adj (w i) (w (finRotate (n+3) i)))
    (hParity : Even (n+3) ∨ Fin.last (n+2) ∉ A) :
    ∃ Q : SimpleGraph V, Q = (markedCycle A).map w ∧ Q ≤ G ∧ Q.EdgeColorable 2 ∧
      (∀ i,Q.degree (w i) = (if i ∈ A then 1 else 0)+
        (if (finRotate (n+3)).symm i ∈ A then 1 else 0)) ∧
      (∀ v,v ∉ Set.range w → Q.degree v = 0) := by
  obtain ⟨Q,rfl,hLe,hC,hD,hOff⟩ :=
    projected_cycle_or_broken_cycle_layer G (markedCycle A) w (by
      intro i j h
      change (i ∈ A ∧ (finRotate (n+3)) i = j) ∨ (j ∈ A ∧ (finRotate (n+3)) j = i) at h
      rcases h with ⟨hi,rfl⟩|⟨hj,hj'⟩
      · exact hEdges i hi
      · rw [←hj']
        exact (hEdges j hj).symm)
      (markedCycle_le_cycleGraph A)
      (hParity.imp_right (markedCycle_le_pathGraph_of_no_closing A))
  refine ⟨(markedCycle A).map w,rfl,hLe,hC,?_,hOff⟩
  intro i
  exact (hD i).trans (markedCycle_degree A i)

end OverfullWork.CMSTrimmingRound

module

public import OverfullWork.CMSOperation41MarkedCycle

@[expose] public section


/-! A gap anywhere in the cyclic expansion suffices to colour its
physical edges. Rotation changes the counting coordinates only. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem marked_cycle_bicoloring_of_gap {n : ℕ} (A : Finset (Fin (n+3)))
    (j : Fin (n+3)) (hj : j ∉ A) : Nonempty ((markedCycle A).Coloring Bool) := by
  let k := j - Fin.last (n+2)
  let ρ : Fin (n+3) ≃ Fin (n+3) :=
    ⟨fun i => i+k,fun i => i-k,fun i => add_sub_cancel_right i k,fun i => sub_add_cancel i k⟩
  have hLast : ρ (Fin.last (n+2)) = j := by
    change Fin.last (n+2)+(j-Fin.last (n+2)) = j
    exact (add_comm (Fin.last (n+2)) (j-Fin.last (n+2))).trans (sub_add_cancel _ _)
  let σ := finRotate (n+3)
  have hCom (i : Fin (n+3)) : ρ (σ i) = σ (ρ i) := by
    change σ i+k = σ (i+k)
    simp only [σ,finRotate_apply]
    ac_rfl
  let B : Finset (Fin (n+3)) := univ.filter (fun i => ρ i ∈ A)
  have hNot : Fin.last (n+2) ∉ B := by
    intro h
    obtain ⟨_,hh⟩ := mem_filter.mp h
    rw [hLast] at hh
    exact hj hh
  have hRot (u v : Fin (n+3)) : (markedCycle B).Adj u v ↔ (markedCycle A).Adj (ρ u) (ρ v) := by
    change ((u ∈ B ∧ σ u = v) ∨ (v ∈ B ∧ σ v = u)) ↔
      ((ρ u ∈ A ∧ σ (ρ u) = ρ v) ∨ (ρ v ∈ A ∧ σ (ρ v) = ρ u))
    rw [←hCom u,←hCom v]
    simp only [B,mem_filter,mem_univ,true_and,Equiv.apply_eq_iff_eq]
  let C := pathGraph.bicoloring (n+3)
  refine ⟨Coloring.mk (fun v => C (ρ.symm v)) ?_⟩
  intro u v h
  apply C.valid
  apply markedCycle_le_pathGraph_of_no_closing B hNot
  apply (hRot (ρ.symm u) (ρ.symm v)).mpr
  simpa only [Equiv.apply_symm_apply] using h

theorem physical_layer_of_marked_cycle_any_gap (G : SimpleGraph V) {n : ℕ}
    (w : Fin (n+3) ↪ V) (A : Finset (Fin (n+3)))
    (hEdges : ∀ i ∈ A,G.Adj (w i) (w (finRotate (n+3) i)))
    (hParity : Even (n+3) ∨ ∃ i,i ∉ A) :
    ∃ Q : SimpleGraph V,Q = (markedCycle A).map w ∧ Q ≤ G ∧ Q.EdgeColorable 2 ∧
      (∀ i,Q.degree (w i) = (if i ∈ A then 1 else 0)+
        (if (finRotate (n+3)).symm i ∈ A then 1 else 0)) ∧
      ∀ v,v ∉ Set.range w → Q.degree v = 0 := by
  rcases hParity with hEven | ⟨j,hj⟩
  · exact physical_layer_of_marked_cycle G w A hEdges (Or.inl hEven)
  · let H := markedCycle A
    let Q := H.map w
    obtain ⟨c⟩ := marked_cycle_bicoloring_of_gap A j hj
    have hLe : Q ≤ G := by
      intro a b h
      obtain ⟨u,v,hUV,rfl,rfl⟩ := (map_adj w H a b).mp h
      change (u ∈ A ∧ finRotate (n+3) u = v) ∨ (v ∈ A ∧ finRotate (n+3) v = u) at hUV
      rcases hUV with ⟨hu,rfl⟩ | ⟨hv,he⟩
      · exact hEdges u hu
      · rw [←he]
        exact (hEdges v hv).symm
    have hD (i : Fin (n+3)) : H.degree i ≤ 2 :=
      (degree_le_of_le (markedCycle_le_cycleGraph A) (v := i)).trans
        (cycleGraph_degree_three_le (v := i)).le
    refine ⟨Q,rfl,hLe,map_edge_colourable_two_of_bicolouring H w c hD,?_,?_⟩
    · intro i
      exact (map_degree_at_embedding H w (dMap := Classical.decRel _) i).trans (markedCycle_degree A i)
    · exact map_degree_outside_embedding H w (dMap := Classical.decRel _)

end OverfullWork.CMSTrimmingRound

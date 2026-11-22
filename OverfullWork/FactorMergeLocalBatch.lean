module

public import OverfullWork.FactorMergeCoarsening

@[expose] public section


/-! Several factors can use the same selected pair. Each factor has its
own identification of the fixed target labels with the original successors. -/
namespace OverfullWork.DirectedRobustExpansion
open Finset DirectedAbsorbingLadder
open scoped Classical
universe u
variable {V : Type u} [Fintype V]

/-- The reserve of one pair supplies disjoint replacements for all
factors in the batch, while allowing different path orders. -/
theorem exists_batch_coarsening_on_pair (d ε ν τ γ : ℝ) (hν : 0 < ν)
    (hWidth : ε+ν ≤ τ) (hε : 0 ≤ ε) (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1)
    (hd : 0 < d) :
    ∃ N : ℕ, ∀ {W : Type u} [Fintype W] (S : Finset W) (D : Digraph (↑S)) (k : ℕ)
      (σ : Fin k → Equiv.Perm W) (p : Fin k → Equiv.Perm (↑S)), N ≤ S.card →
      (k:ℝ)+ν*(S.card:ℝ) ≤ d*τ*(S.card:ℝ) →
      γ*(S.card:ℝ)+(k:ℝ) ≤ d*(S.card:ℝ) →
      (∀ A B : Finset (↑S), ε*(S.card:ℝ) ≤ (A.card:ℝ) →
        ε*(S.card:ℝ) ≤ (B.card:ℝ) →
        d*(A.card:ℝ)*(B.card:ℝ) ≤ (incidences D A B:ℝ)) →
      (∀ v, d*(S.card:ℝ) ≤ (inDegree D v:ℝ)) →
      (∀ v, d*(S.card:ℝ) ≤ (outDegree D v:ℝ)) →
      ∃ M : Fin k → Equiv.Perm (↑S),
        (∀ j x, D.Adj x (M j x)) ∧
        (∀ i j, i ≠ j → ∀ x, M i x ≠ M j x) ∧
        ∀ j, let ρ := replacedSuccessor (σ j) S ((M j).trans (p j).symm)
          (∀ x y, (σ j).SameCycle x y → ρ.SameCycle x y) ∧
          ∀ x ∈ S, ∀ y ∈ S, ρ.SameCycle x y := by
  obtain ⟨N,hN⟩ := exists_disjoint_merge_matchings.{u} d ε ν τ γ hν hWidth hε hτγ hγ hd
  refine ⟨N,?_⟩
  intro W _ S D k σ p hn hCost hDegree hRect hIn hOut
  choose P e hEnds hDis hCover using fun j => exists_cut_paths_on_touched_cycles (σ j) S
  let f : Fin k → Equiv.Perm (↑S) := fun j => ((e j).trans (p j)).symm
  obtain ⟨M,hM,hCycle,hApart⟩ := hN D k f (by simpa using hn) (by simpa using hCost)
    (by simpa using hDegree) (by simpa using hRect) (by simpa using hIn) (by simpa using hOut)
  refine ⟨M,hM,hApart,?_⟩
  intro j
  let F := (M j).trans (p j).symm
  -- The labels in the packed cycle are the fixed labels of the reserve.
  have hOrder : HasSpanningCycle (fun i l => F ((e j).symm i) = l) := by
    obtain ⟨L,z,hND,hAll,hHead,hChain⟩ := hCycle j
    let g : ↑S → ↑S := (p j).symm
    refine ⟨L.map g,g z,hND.map (p j).symm.injective,?_,?_,?_⟩
    · intro x
      exact List.mem_map.mpr ⟨p j x,hAll _,(p j).symm_apply_apply x⟩
    · rw [List.head?_map,hHead]
      rfl
    · rw [←List.map_singleton,←List.map_append]
      apply List.isChain_map_of_isChain g _ hChain
      intro i l h
      exact congrArg g h
  obtain ⟨T,z,_,_,hChain,hSupport⟩ := replacement_cycle_of_path_order (σ j) S (P j) (e j) F
    (hEnds j) (hDis j) (hCover j) hOrder
  obtain ⟨hOld,hTouch⟩ := coarsening_of_touched_cycle (σ j) S F T z hChain hSupport
  exact ⟨hOld,fun x hx y hy => hTouch x y (touchesCut_of_mem (σ j) hx) (touchesCut_of_mem (σ j) hy)⟩

end OverfullWork.DirectedRobustExpansion

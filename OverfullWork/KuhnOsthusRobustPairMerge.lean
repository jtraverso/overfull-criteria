module

public import OverfullWork.KuhnOsthusPreparedPathExtender
public import OverfullWork.MergeReservePacking

@[expose] public section


/-! The local replacement in Kühn–Osthus Lemma 6.4 may start from
the robust expansion supplied by Lemma 4.11 directly. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
universe u

theorem reindexSources_real_robust {V : Type*} [Fintype V]
    (D : Digraph V) (e : Equiv.Perm V) (ν τ : ℝ)
    (hRob : IsRealRobust D ν τ) : IsRealRobust (reindexSources D e) ν τ := by
  intro S hLow hHigh
  have hCard := card_image_of_injective S e.injective
  have hN : realNeighbourhood (reindexSources D e) ν S = realNeighbourhood D ν (S.image e) := by
    ext v
    have he := reindexSources_incidences D e S {v}
    simp only [incidences,sum_singleton] at he
    simp only [realNeighbourhood,mem_filter,mem_univ,true_and,he]
  rw [hN,←hCard]
  exact hRob _ (by rwa [hCard]) (by rwa [hCard])

/-- A single free pair with a robust contracted reserve can merge all
the old cycles that touch it. This does not compare the rectangle
threshold with the density of the sparse reserve. -/
theorem exists_cut_merge_of_robust_reserve
    (ν τ γ : ℝ) (hν : 0 < ν) (hντ : ν ≤ τ) (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] (σ : Equiv.Perm V) (S : Finset V) (D : Digraph S),
      N ≤ S.card → IsRealRobust D ν τ →
      (∀ v, γ*(S.card:ℝ) ≤ (inDegree D v:ℝ)) →
      (∀ v, γ*(S.card:ℝ) ≤ (outDegree D v:ℝ)) →
      ∃ M : Equiv.Perm (↑S), (∀ x, D.Adj x (M x)) ∧
        (∀ x y, σ.SameCycle x y → (replacedSuccessor σ S M).SameCycle x y) ∧
        ∀ x y, touchesCut σ S x → touchesCut σ S y →
          (replacedSuccessor σ S M).SameCycle x y := by
  obtain ⟨N,hN⟩ := DirectedAbsorbingLadder.exists_hamilton_threshold.{u} ν τ γ hν hντ hτγ hγ
  refine ⟨N,?_⟩
  intro V _ σ S D hSize hRob hIn hOut
  obtain ⟨P,e,hEnds,hDis,hCover⟩ := exists_cut_paths_on_touched_cycles σ S
  have hAux := hN (reindexSources D e.symm)
    (by simpa only [Fintype.card_coe] using hSize)
    (reindexSources_real_robust D e.symm ν τ hRob)
    (fun v => by simpa only [Fintype.card_coe,(reindexSources_semidegrees D e.symm v).1] using hIn v)
    (fun v => by simpa only [Fintype.card_coe,(reindexSources_semidegrees D e.symm v).2] using hOut (e.symm v))
  obtain ⟨ρ,hEdge,hCycle⟩ := exists_spanning_successor hAux
  let M := e.trans ρ
  have hM (x : S) : D.Adj x (M x) := by
    simpa [M,reindexSources] using hEdge (e x)
  have hOrder : HasSpanningCycle (fun x y => M (e.symm x) = y) := by
    simpa [M] using hCycle
  obtain ⟨T,z,_,_,hChain,hSupport⟩ :=
    replacement_cycle_of_path_order σ S P e M hEnds hDis hCover hOrder
  exact ⟨M,hM,coarsening_of_touched_cycle σ S M T z hChain hSupport⟩

end OverfullWork.DirectedRobustExpansion

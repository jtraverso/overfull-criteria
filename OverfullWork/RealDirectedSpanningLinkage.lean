module

public import OverfullWork.RealRobustSpanningLinkage

@[expose] public section


/-! Directed spanning linkage, retaining the arc directions of the
contraction and decoding used in R2. -/
namespace OverfullWork.RobustSpanningLinkage

open DirectedRobustExpansion DirectedListRoutes PairedHamiltonDecode
universe u

/-- A directed robust expander can join linearly many prescribed pairs
by mutually disjoint directed paths that exhaust the host. -/
theorem exists_directed_spanning_linkage_threshold (ν τ α : ℝ) (hν : 0 < ν)
    (hντ : ν ≤ τ) (hτα : 256*τ ≤ α) (hα : α ≤ 1) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] (D : Digraph V),
      N ≤ Fintype.card V → IsRealRobust D ν τ →
      (∀ v, α*(Fintype.card V:ℝ) ≤ (inDegree D v:ℝ)) →
      (∀ v, α*(Fintype.card V:ℝ) ≤ (outDegree D v:ℝ)) →
      ∀ (k : ℕ), ((k+1:ℕ):ℝ) ≤ (ν/4)^3*(Fintype.card V:ℝ) →
      ∀ (a b : Fin (k+1) → V), Function.Injective a → Function.Injective b →
        (∀ i j, a i ≠ b j) →
        ∃ tail : Fin (k+1) → List V,
          (∀ i, Route D (a i) (b i) (tail i) ∧ (a i :: tail i).Nodup) ∧
          (∀ i j, i ≠ j → List.Disjoint (a i :: tail i) (a j :: tail j)) ∧
          ∀ v, ∃ i, v ∈ a i :: tail i := by
  obtain ⟨N,hN⟩ := exists_paired_ordered_cycle_threshold.{u} ν τ α hν
    (by linarith only [hντ,hτα,hα]) hντ hτα hα
  refine ⟨N,?_⟩
  intro V _ D hn hRobust hIn hOut k hp a b ha hb hab
  obtain ⟨init,hSimple,hCover,hOrder,hCycle⟩ :=
    hN D hn hRobust hIn hOut k hp a b ha hb hab
  obtain ⟨body,hChain,hND,hDisjoint,hAll⟩ := lists_of_hamilton_cycle a b ha hb
    (finRotate (k+1)) D D.Adj (fun h => h) hab init 0 hSimple hCover hOrder hCycle
  let tail := fun i => (body i).map Subtype.val ++ [b i]
  refine ⟨tail,fun i => ⟨⟨hChain i, ?_⟩, hND i⟩,hDisjoint,hAll⟩
  change ((a i :: (body i).map Subtype.val) ++ [b i]).getLast? = some (b i)
  exact (List.getLast?_append_of_ne_nil _ (by simp)).trans rfl

end OverfullWork.RobustSpanningLinkage

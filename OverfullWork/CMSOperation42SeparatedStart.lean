module

public import OverfullWork.CriticalAlmostPairNormalization

@[expose] public section


/-! The pair transfer from (4.2), with the loss in the odd-cut
budget recorded explicitly. The source degree-sum bound is the
one supplied by CMS Claim 4.2(3). -/
namespace OverfullWork.CMSMatchingRemoval

open SimpleGraph Finset OddCutDeficit CriticalAlmostPairNormalization
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem separate_initial_odd_cut (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (hOdd : Odd X.card) (b L : ℕ)
    (hBudget : deficitMass G G.maxDegree X+(∑ y ∈ Xᶜ,G.degree y) ≤ G.maxDegree+b)
    (hRoom : b+2*L+1 ≤ G.maxDegree)
    (hVal : ∀ u v,G.Adj u v → G.maxDegree ≤ G.degree u+G.degree v+L) :
    ∃ X' : Finset V,X ⊆ X' ∧ Odd X'.card ∧ X'ᶜ.card ≤ Xᶜ.card ∧
      G.IsIndepSet (↑(X'ᶜ) : Set V) ∧
      deficitMass G G.maxDegree X'+(∑ y ∈ X'ᶜ,G.degree y) ≤ G.maxDegree+(b+2*L) ∧
      (∀ y ∈ X'ᶜ,∀ z ∈ X'ᶜ,y ≠ z → G.degree y+G.degree z+L < G.maxDegree) := by
  have hInd (Y : Finset V)
      (hPairs : ∀ y ∈ Y,∀ z ∈ Y,y ≠ z → G.degree y+G.degree z+L < G.maxDegree) :
      G.IsIndepSet (Y : Set V) := by
    rw [isIndepSet_iff]
    intro y hy z hz hne hAdj
    have h := hPairs y hy z hz hne
    have h' := hVal y z hAdj
    omega
  by_cases hHeavy : ∃ y ∈ Xᶜ,∃ z ∈ Xᶜ,y ≠ z ∧ G.maxDegree ≤ G.degree y+G.degree z+L
  · obtain ⟨y,hy,z,hz,hyz,hLarge⟩ := hHeavy
    let X' := insert y (insert z X)
    obtain ⟨hCard,hSmall⟩ := insert_pair_cardinalities X y z hy hz hyz
    have hEq := budget_insert_pair_identity G X y z hy hz hyz
    have hExt := complement_sum_insert_pair G X y z hy hz hyz
    have hOld : (∑ w ∈ Xᶜ,G.degree w) ≤ G.maxDegree+b := by omega
    have hCost : (∑ w ∈ X'ᶜ,G.degree w) ≤ b+L := by dsimp only [X']; omega
    have hPairs (u : V) (hu : u ∈ X'ᶜ) (v : V) (hv : v ∈ X'ᶜ) (hne : u ≠ v) :
        G.degree u+G.degree v+L < G.maxDegree := by
      have h := pair_degree_sum_le G X'ᶜ u v hu hv hne
      omega
    refine ⟨X',?_,?_,?_,hInd _ hPairs,?_,hPairs⟩
    · exact fun _ hw => mem_insert_of_mem (mem_insert_of_mem hw)
    · obtain ⟨k,hk⟩ := hOdd
      exact ⟨k+1,by change (insert y (insert z X)).card = _; omega⟩
    · change (insert y (insert z X))ᶜ.card ≤ Xᶜ.card
      omega
    · dsimp only [X']
      omega
  · have hPairs (u : V) (hu : u ∈ Xᶜ) (v : V) (hv : v ∈ Xᶜ) (hne : u ≠ v) :
        G.degree u+G.degree v+L < G.maxDegree := by
      exact Nat.lt_of_not_ge (fun h => hHeavy ⟨u,hu,v,hv,hne,h⟩)
    exact ⟨X,Subset.rfl,hOdd,le_rfl,hInd _ hPairs,by omega,hPairs⟩

end OverfullWork.CMSMatchingRemoval

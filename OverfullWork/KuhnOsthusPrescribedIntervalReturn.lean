module

public import OverfullWork.KuhnOsthusCycleAbsorberHalfPaths

@[expose] public section


/-! Fill the return interval of an absorber factor with a prescribed
permutation of the labels. The physical factor keeps the entire
forward cover and the newly chosen return paths. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset Function
open scoped Classical
variable {V J : Type*} [Fintype V]

/-- Close a forward cover with a prescribed return in a separate host. -/
theorem IntervalPathCover.exists_factor_with_prescribed_return_in {G H : Digraph V} {U : Finset V}
    (A : ℕ → Finset V) (n m r : ℕ) (hn : 3 ≤ n)
    (P : IntervalPathCover H U (A n) (A 0)) (e : J ≃ A n) (ρ : Equiv.Perm J)
    (hAll : U ∪ clusterIntervalVertices A 0 n = univ)
    (hMeet : U ∩ clusterIntervalVertices A 0 n = A n ∪ A 0)
    (hBoundary : Disjoint (A n) (A 0))
    (hSize : ∀ i ≤ n, (A i).card = m)
    (hDis : ∀ i j, i ≤ n → j ≤ n → i ≠ j → Disjoint (A i) (A j))
    (ε d : ℝ) (hε : 0 ≤ ε) (hGap : 2*ε < d) (hd : d ≤ 1)
    (hPairs : ∀ i < n, IsLowerSuperregularPair G ε d (A i) (A (i+1)))
    (hr : 0 < r) (hCut : (m:ℝ)*ε ≤ (r:ℝ))
    (hBudget : 28*((r:ℝ)+1) < (d-2*ε)^14*((d-ε)*(m:ℝ))) :
    ∃ (R : OrderedClusterPaths G A J 0 n) (σ : Equiv.Perm V),
      (∀ x y, (P.digraph ⊔ R.unionPaths).Adj x y ↔ σ x = y) ∧
      (∀ j, R.vertex 0 j = (P.starts.symm (e j)).val ∧ R.vertex n j = (e (ρ j)).val) ∧
      Nonempty (MarkedCycleSegments σ (Embedding.subtype (· ∈ A n)) (e.symm.trans (ρ.trans e))) := by
  let e₀ := e.trans P.starts.symm
  let e₁ := ρ.trans e
  obtain ⟨R,h₀,h₁⟩ := exists_ordered_cluster_paths G A 0 n m r hn e₀ e₁ ε d hε hGap hd hr hCut hBudget
    (fun i _ hi => hSize i hi) (fun i j _ hi _ hj h => hDis i j hi hj h)
    (fun i _ hi => hPairs i hi)
  obtain ⟨Q,hQ,hStart⟩ := R.exists_interval_path_cover (Nat.zero_le n)
    (fun i j _ hi _ hj h => hDis i j hi hj h)
  have hOrder (j : J) : R.orderAt n (Nat.zero_le n) le_rfl j = e₁ j := Subtype.ext (h₁ j)
  have hQstart : Q.starts = e₁.symm.trans e₀ := by
    ext x
    obtain ⟨j,rfl⟩ := e₁.surjective x
    have h := hStart j
    rw [hOrder,h₀] at h
    have he' : ((e₁.symm.trans e₀) (e₁ j)).val = (e₀ j).val :=
      congrArg (fun z => (e₀ z).val) (e₁.symm_apply_apply j)
    exact h.trans he'.symm
  let P' := P.rehost (le_sup_left : H ≤ H ⊔ G)
  let Q' := Q.rehost (le_sup_right : G ≤ H ⊔ G)
  obtain ⟨σ,hArc,hReturn⟩ := P'.exists_winding_factor_with_return Q' hAll hMeet hBoundary
  change (∀ x y, (P.digraph ⊔ Q.digraph).Adj x y ↔ σ x = y) at hArc
  change Nonempty (MarkedCycleSegments σ (Embedding.subtype (· ∈ A n))
    (Q.starts.trans P.starts).symm) at hReturn
  have he : (Q.starts.trans P.starts).symm = e.symm.trans (ρ.trans e) := by
    rw [hQstart]
    apply Equiv.ext
    intro x
    simp [e₀,e₁]
  rw [hQ] at hArc
  rw [he] at hReturn
  exact ⟨R,σ,hArc,fun j => ⟨h₀ j,h₁ j⟩,hReturn⟩

/-- A prescribed return map at the initial cluster of a forward
cover. This is the choice used to close the two ordered rows of the
cycle and parity absorbers. -/
theorem IntervalPathCover.exists_factor_with_prescribed_return {G : Digraph V} {U : Finset V}
    (A : ℕ → Finset V) (n m r : ℕ) (hn : 3 ≤ n)
    (P : IntervalPathCover G U (A n) (A 0)) (e : J ≃ A n) (ρ : Equiv.Perm J)
    (hAll : U ∪ clusterIntervalVertices A 0 n = univ)
    (hMeet : U ∩ clusterIntervalVertices A 0 n = A n ∪ A 0)
    (hBoundary : Disjoint (A n) (A 0))
    (hSize : ∀ i ≤ n, (A i).card = m)
    (hDis : ∀ i j, i ≤ n → j ≤ n → i ≠ j → Disjoint (A i) (A j))
    (ε d : ℝ) (hε : 0 ≤ ε) (hGap : 2*ε < d) (hd : d ≤ 1)
    (hPairs : ∀ i < n, IsLowerSuperregularPair G ε d (A i) (A (i+1)))
    (hr : 0 < r) (hCut : (m:ℝ)*ε ≤ (r:ℝ))
    (hBudget : 28*((r:ℝ)+1) < (d-2*ε)^14*((d-ε)*(m:ℝ))) :
    ∃ (R : OrderedClusterPaths G A J 0 n) (σ : Equiv.Perm V),
      (∀ x y, (P.digraph ⊔ R.unionPaths).Adj x y ↔ σ x = y) ∧
      (∀ j, R.vertex 0 j = (P.starts.symm (e j)).val ∧ R.vertex n j = (e (ρ j)).val) ∧
      Nonempty (MarkedCycleSegments σ (Embedding.subtype (· ∈ A n)) (e.symm.trans (ρ.trans e))) :=
  P.exists_factor_with_prescribed_return_in A n m r hn e ρ hAll hMeet hBoundary
    hSize hDis ε d hε hGap hd hPairs hr hCut hBudget

end OverfullWork.DirectedRobustExpansion

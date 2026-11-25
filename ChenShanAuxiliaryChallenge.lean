module

public import OverfullWork.KLOSRobustComponents
public import OverfullWork.MultigraphCuts

@[expose] public section

namespace OverfullWork.ChenShan
open SimpleGraph Finset KLOS PrunedCore RobustExpansion

def auxiliaryOrder (n k : ℕ) : ℕ :=
  max n (k + 1) + if (max n (k + 1)) % 2 = n % 2 then 0 else 1

theorem exists_robust_graph_with_prescribed_degrees
    (δ τ : ℝ) (hδ : 0 < δ) (hτ : 0 < τ) :
    ∃ ν : ℝ, 0 < ν ∧ ∃ N : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V],
      N ≤ Fintype.card V → ∀ degrees : V → ℕ,
      (∀ v, δ * (Fintype.card V : ℝ) ≤ (degrees v : ℝ)) →
      (∀ v, degrees v < Fintype.card V) →
      (∀ v w, degrees v ≤ degrees w + 1) →
      (∑ v, degrees v) % 2 = 0 →
      ∃ G : SimpleGraph V, ∃ _ : DecidableRel G.Adj,
        (∀ v, G.degree v = degrees v) ∧ ExpandsInside G ν τ univ := by
  sorry

open scoped Classical in
theorem exists_regular_auxiliary_completion
    (α τ : ℝ) (hα : 0 < α) (hαOne : α < 1) (hτ : 0 < τ) (hRange : τ < α / 24) :
    ∃ ν ε : ℝ, 0 < ν ∧ 0 < ε ∧ ∃ N : ℕ,
      ∀ {U : Type*} [Fintype U] [DecidableEq U] (L : MultiGraph U) (k : ℕ),
      let n := Fintype.card U
      N ≤ n → α * (n : ℝ) ≤ (k : ℝ) → k ≤ 2 * n →
      (∀ u, L.degree u ≤ k) → ¬ L.HasOverfullSubset k →
      let s := ∑ u, (k - L.degree u)
      (s : ℝ) ≤ ε * (n : ℝ) ^ 2 →
      let m := auxiliaryOrder n k
      let b := ⌈(s : ℝ) / (m : ℝ)⌉₊
      ∃ P : MultiGraph (U ⊕ Fin m), ∃ G : SimpleGraph (Fin m), ∃ _ : DecidableRel G.Adj,
        P.IsRegularOfDegree k ∧ Even (Fintype.card (U ⊕ Fin m)) ∧
        (∀ u v : U, P.mult s(.inl u, .inl v) = L.mult s(u, v)) ∧
        (∀ u : U, ∀ w : Fin m, P.mult s(.inl u, .inr w) ≤ 1) ∧
        (∀ w z : Fin m, P.mult s(.inr w, .inr z) = if G.Adj w z then 1 else 0) ∧
        ¬ P.HasOverfullSubset k ∧ (∀ w, k - b ≤ G.degree w) ∧ ExpandsInside G ν τ univ := by
  sorry

open scoped Classical in
theorem exists_simple_auxiliary_completion
    (α τ : ℝ) (hα : 0 < α) (hαOne : α < 1) (hτ : 0 < τ) (hRange : τ < α / 24) :
    ∃ ν ε : ℝ, 0 < ν ∧ 0 < ε ∧ ∃ N : ℕ,
      ∀ {U : Type*} [Fintype U] [DecidableEq U] (L : SimpleGraph U) [DecidableRel L.Adj] (k : ℕ),
      let n := Fintype.card U
      N ≤ n → α * (n : ℝ) ≤ (k : ℝ) → k < n →
      (∀ u, L.degree u ≤ k) → ¬ (MultiGraph.ofSimpleGraph L).HasOverfullSubset k →
      let s := ∑ u, (k - L.degree u)
      (s : ℝ) ≤ ε * (n : ℝ) ^ 2 →
      let b := ⌈(s : ℝ) / (n : ℝ)⌉₊
      ∃ R : SimpleGraph (U ⊕ Fin n), ∃ G : SimpleGraph (Fin n), ∃ _ : DecidableRel G.Adj,
        (∀ x, R.degree x = k) ∧
        (∀ u v : U, R.Adj (.inl u) (.inl v) ↔ L.Adj u v) ∧
        (∀ w z : Fin n, R.Adj (.inr w) (.inr z) ↔ G.Adj w z) ∧
        ¬ (MultiGraph.ofSimpleGraph R).HasOverfullSubset k ∧
        (∀ w, k - b ≤ G.degree w) ∧ ExpandsInside G ν τ univ := by
  sorry

end OverfullWork.ChenShan

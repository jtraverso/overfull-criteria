module

public import OverfullWork.UniformPartitionSampling
public import OverfullWork.ChenShanUniformInclusion

@[expose] public section

namespace OverfullWork.UniformSubsetSampling

open Finset
open scoped Classical

variable {V W : Type*} [Fintype V] [Fintype W]

/-- Every vertex has inclusion probability equal to the fraction sampled. -/
theorem probability_contains_vertex (v : V) {k : ℕ} (hk : k ≤ Fintype.card V) :
    probability k (fun X => v ∈ X) = (k:ℝ)/Fintype.card V := by
  by_cases hk₀ : k = 0
  · subst k
    simp [probability]
  have hk₁ : 1 ≤ k := Nat.pos_of_ne_zero hk₀
  let n := Fintype.card V
  have hn : 0 < n := Fintype.card_pos_iff.mpr ⟨v⟩
  have hc : (0:ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hk
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hSingleton := probability_contains_eq ({v} : Finset V)
    (show ({v} : Finset V).card ≤ k by simpa only [card_singleton] using hk₁)
  rw [show probability k (fun X => v ∈ X) =
    probability k (fun X => ({v} : Finset V) ⊆ X) by simp only [singleton_subset_iff]]
  rw [hSingleton,card_singleton]
  change ((n-1).choose (k-1):ℝ)/(n.choose k) = _
  apply (div_eq_div_iff hc.ne' hnR.ne').mpr
  have h := Nat.choose_mul (n := n) (k := k) (s := 1) hk₁
  simp only [Nat.choose_one_right] at h
  exact_mod_cast (show (n-1).choose (k-1)*n = k*(n.choose k) by
    simpa only [mul_comm] using h.symm)

/-- For independent orderings of two disjoint classes, a vertex's
appearance in its own prefix contributes its exact sampling fraction
to the bad-event count for a different class. -/
theorem permutation_pair_bad_event_card (S : Finset V) (T : Finset W)
    (v : V) (bad : Finset W → Prop) :
    (((univ : Finset (Equiv.Perm V × Equiv.Perm W)).filter (fun pair =>
      v ∈ permutationImage S pair.1 ∧ bad (permutationImage T pair.2))).card : ℝ) =
        ((S.card : ℝ)/Fintype.card V) * probability T.card bad *
          ((Fintype.card (Equiv.Perm V) : ℝ) * Fintype.card (Equiv.Perm W)) := by
  let F := (univ : Finset (Equiv.Perm V × Equiv.Perm W)).filter (fun pair =>
    v ∈ permutationImage S pair.1 ∧ bad (permutationImage T pair.2))
  change (F.card : ℝ) = _
  have hF (x : Equiv.Perm V × Equiv.Perm W) : x ∈ F ↔
      v ∈ permutationImage S x.1 ∧ bad (permutationImage T x.2) :=
    ⟨fun h => (mem_filter.mp h).2,fun h => mem_filter.mpr ⟨mem_univ _,h⟩⟩
  let _ : DecidablePred (fun π : Equiv.Perm V => v ∈ permutationImage S π) :=
    fun _ => Classical.propDecidable _
  let P := (univ : Finset (Equiv.Perm V)).filter (fun π => v ∈ permutationImage S π)
  let Q := (univ : Finset (Equiv.Perm W)).filter (fun π => bad (permutationImage T π))
  have hProd : F = P ×ˢ Q := by
    ext x
    rw [hF,mem_product]
    simp only [P,Q,mem_filter,mem_univ,true_and]
  have hP : (P.card:ℝ) = ((S.card:ℝ)/Fintype.card V)*Fintype.card (Equiv.Perm V) := by
    have h := permutation_probability S (fun X => v ∈ X)
    rw [probability_contains_vertex v (card_le_univ S)] at h
    exact h
  have hQ : (Q.card:ℝ) = probability T.card bad*Fintype.card (Equiv.Perm W) :=
    permutation_probability T bad
  rw [hProd,card_product,Nat.cast_mul,hP,hQ]
  ring

end OverfullWork.UniformSubsetSampling

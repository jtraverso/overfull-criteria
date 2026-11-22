module

public import OverfullWork.DirectedGlobalEnergyGain

@[expose] public section


/-! Bounded termination for the weighted common-partition version of
directed regularity, before any equitabilization or degree cleaning. -/
namespace OverfullWork.DirectedPairEnergy
open Finset Finpartition
open scoped Classical
universe u
set_option maxHeartbeats 12000000

def refinementBound (k : ℕ) : ℕ → ℕ
  | 0 => k
  | i+1 => refinementBound k i * 2^(2*refinementBound k i)

theorem exists_weighted_regular_partition (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    ∃ M : ℕ, ∀ {V : Type u} [Fintype V] (D : Digraph V)
      (P : Finpartition (univ : Finset V)), P.parts.card ≤ k →
      ∃ Q : Finpartition (univ : Finset V), Q.parts.card ≤ M ∧ irregularMass D Q ε < ε := by
  obtain ⟨t, ht⟩ := exists_nat_gt (1/ε^5)
  refine ⟨refinementBound k t, ?_⟩
  intro V _ D P hP
  have hIter : ∀ i : ℕ, ∃ Q : Finpartition (univ : Finset V),
      Q.parts.card ≤ refinementBound k i ∧
      (irregularMass D Q ε < ε ∨ (i:ℝ)*ε^5 ≤ partitionEnergy D Q) := by
    intro i
    induction i with
    | zero => exact ⟨P,hP,Or.inr (by simpa using partitionEnergy_nonneg D P)⟩
    | succ i ih =>
      obtain ⟨Q,hCard,hQ⟩ := ih
      by_cases hReg : irregularMass D Q ε < ε
      · refine ⟨Q, ?_, Or.inl hReg⟩
        refine hCard.trans ?_
        simp only [refinementBound]
        exact Nat.le_mul_of_pos_right _ (by positivity)
      · refine ⟨witnessRefinement D Q ε hε, ?_, Or.inr ?_⟩
        · refine (witnessRefinement_card D Q ε hε).trans ?_
          exact Nat.mul_le_mul hCard (Nat.pow_le_pow_right (by omega)
            (Nat.mul_le_mul_left 2 hCard))
        · have hOld := hQ.resolve_left hReg
          have hGain := witnessRefinement_uniform_gain D Q ε hε (le_of_not_gt hReg)
          rw [Nat.cast_succ]
          linarith only [hOld,hGain]
  obtain ⟨Q,hCard,hQ⟩ := hIter t
  refine ⟨Q,hCard,hQ.resolve_right ?_⟩
  intro he
  have hLarge := (div_lt_iff₀ (pow_pos hε 5)).mp ht
  exact (not_lt_of_ge (partitionEnergy_le_one D Q)) (hLarge.trans_le he)

end OverfullWork.DirectedPairEnergy

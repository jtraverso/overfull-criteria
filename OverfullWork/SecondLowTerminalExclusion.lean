module

public import OverfullWork.SecondLowUniformReserves

@[expose] public section


/-! Uniform closure of the noncritical second-low terminal. -/
namespace OverfullWork.NormalizedClassTwoStep
open SimpleGraph Finset
open scoped Classical
universe u
set_option maxHeartbeats 12000000

theorem above_half_second_low_terminal_exclusion (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : ℕ, 8 ≤ Q ∧ ∃ N : ℕ,
      ∀ {V : Type u} [Fintype V] [DecidableEq V] {B K : ℕ}
        (s : State V B K), N ≤ Fintype.card V → Margins s →
        ((1:ℝ)/2+ε)*(Fintype.card V:ℝ) ≤ (s.graph.maxDegree:ℝ) →
        B ≤ 6*(Fintype.card V/(4096*Q^2))+6 →
        K ≤ Fintype.card V/(4096*Q^2)+1 → ¬Nonempty (SecondLowData s) := by
  obtain ⟨C,hC,Q,hQ,N,hReserves⟩ := SecondLowUniformReserves.uniform_reserves ε hε
  refine ⟨Q,hQ,N,?_⟩
  intro V _ _ B K s hn hM hDense hB hK hLow
  obtain ⟨p⟩ := hLow
  obtain ⟨hSize,hSlack,hResidual⟩ := hReserves (Fintype.card V) s.graph.maxDegree B K hn hDense hB hK
  exact second_low_excluded_of_reserves p hM C hC hSize hSlack hResidual

theorem above_half_reduced_terminal_has_small_centre (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : ℕ, 8 ≤ Q ∧ ∃ N : ℕ,
      ∀ {V : Type u} [Fintype V] [DecidableEq V] {B K : ℕ}
        (s : State V B K), N ≤ Fintype.card V → Margins s → ReducedTerminal s →
        ((1:ℝ)/2+ε)*(Fintype.card V:ℝ) ≤ (s.graph.maxDegree:ℝ) →
        B ≤ 6*(Fintype.card V/(4096*Q^2))+6 →
        K ≤ Fintype.card V/(4096*Q^2)+1 →
        (∀ x ∈ s.cut.set, (∑ y ∈ s.cut.setᶜ, s.graph.degree y) ≤ s.graph.degree x) ∧
        ∃ p : NormalizedCanonicalCandidate.Candidate s.cut, p.centre=(0,false) := by
  obtain ⟨Q,hQ,N,hExclude⟩ := above_half_second_low_terminal_exclusion.{u} ε hε
  refine ⟨Q,hQ,N,?_⟩
  intro V _ _ B K s hn hM hT hDense hB hK
  have hSmall : ∀ x ∈ s.cut.set, (∑ y ∈ s.cut.setᶜ, s.graph.degree y) ≤ s.graph.degree x := by
    rcases hT with hSmall|hLow
    · exact hSmall
    · obtain ⟨x,hx,_,hLarge,v,hv,hvx,hLow,hInd⟩ := hLow
      exact (hExclude s hn hM hDense hB hK ⟨⟨x,hx,hLarge,v,hv,hvx,hLow,hInd⟩⟩).elim
  refine ⟨hSmall,?_⟩
  apply NormalizedCanonicalCandidate.exists_centred_candidate s.graph s.cut s.no_overfull _ hSmall
  have hY := s.cut.complement_small
  have hParts := card_add_card_compl s.cut.set
  have hMatch := hM.1
  omega

end OverfullWork.NormalizedClassTwoStep

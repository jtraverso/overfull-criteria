module

public import OverfullWork.CMSOperation41AlmostStop
public import OverfullWork.CMSOperation42NearTightExclusion

@[expose] public section


/-! A stopping witness found in the degree records of Operation 4.1
is the actual odd cut needed to run Operation 4.2. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph RobustExpansion
open scoped Classical
universe u

set_option maxHeartbeats 2600000 in
theorem cms_no_almost_overfull_record_after_trimming (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ τ : ℝ,0 < τ ∧ ∀ ν : ℝ,0 < ν → ν ≤ τ →
      ∃ ηMax : ℝ,0 < ηMax ∧ ∀ η : ℝ,0 < η → η ≤ ηMax → ∃ N : ℕ,
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj] (active U : Finset V)
          (degree : V → ℕ) (a b A : ℕ),
          let n := Fintype.card V
          let K := U.card+1
          let B := b+2*(A+K)
          let d := G.maxDegree
          N+3+K ≤ n → α*(n:ℝ) ≤ (d:ℝ) →
          ¬G.EdgeColorable d → ¬G.HasOverfullSubgraph →
          IsRealRobust G (8*ν) (τ/4) →
          (∀ u v,G.Adj u v → d ≤ G.degree u+G.degree v+A) →
          ((B+4:ℕ):ℝ) ≤ η*((n-K-1:ℕ):ℝ) →
          ((K+1:ℕ):ℝ) ≤ 2*η^2*((n-K-1:ℕ):ℝ) →
          (∀ v,0 < G.degree v → v ∈ active) →
          (∀ v ∈ active,degree v = G.degree v) →
          (∀ v,v ∉ U → d ≤ G.degree v+a) → 2*a+b+1 ≤ d →
          ¬HasAlmostOverfullRecord active d b degree := by
  obtain ⟨τ,hτ,hUse⟩ := CMSMatchingRemoval.cms_no_near_tight_odd_cut_of_small_budgets.{u} α hα hα₁
  refine ⟨τ,hτ,?_⟩
  intro ν hν hντ
  obtain ⟨ηMax,hηMax,hUse⟩ := hUse ν hν hντ
  refine ⟨ηMax,hηMax,?_⟩
  intro η hη hηMax
  obtain ⟨N,hUse⟩ := hUse η hη hηMax
  refine ⟨N,?_⟩
  intro V _ _ G _ active U degree a b A n K B d hn hDens hNC hNo hRob hVAL hB hK
    hPos hExact hHigh hRoom hStop
  obtain ⟨X,_,hOdd,hSmall,hBudget⟩ :=
    localized_actual_almost_stop_of_degree_record G active U degree a b hPos hExact hStop hHigh hRoom
  exact hUse G X b A K hOdd hSmall hn hDens hNC hNo hVAL hBudget hRob hB hK

end OverfullWork.CMSTrimmingRound

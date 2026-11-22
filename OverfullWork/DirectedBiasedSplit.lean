module

public import OverfullWork.DirectedArcSelection

@[expose] public section


/-! An actual directed edge partition at any fixed fraction, controlling
both semidegrees and all ordered cuts simultaneously. -/
namespace OverfullWork.DirectedBiasedSplit
open Finset DirectedRobustExpansion DirectedArcSelection
open scoped Classical
universe u
set_option maxHeartbeats 16000000

theorem exists_selection_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ,∀ p : ℝ, 0 ≤ p → p ≤ 1 → ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (D : Digraph V),N ≤ Fintype.card V →
      ∃ H : Digraph V,H ≤ D ∧
        (∀ v,|(inDegree H v:ℝ)-p*(inDegree D v:ℝ)| < ε*(Fintype.card V:ℝ)) ∧
        (∀ v,|(outDegree H v:ℝ)-p*(outDegree D v:ℝ)| < ε*(Fintype.card V:ℝ)) ∧
        ∀ S T : Finset V,|(incidences H S T:ℝ)-p*(incidences D S T:ℝ)| <
          ε*(Fintype.card V:ℝ)^2 := by
  obtain ⟨N,hN⟩ := BiasedDegreeCutSelection.exists_degree_cut_selection_uniform.{u,u} ε hε
  refine ⟨N,?_⟩
  intro p hp hp1 V _ _ D hn
  let rows : V × Bool → V × V → ℝ := fun vb =>
    if vb.2 then weight D {vb.1} univ else weight D univ {vb.1}
  have hVar : ∀ vb,(∑ e,rows vb e^2) ≤ (Fintype.card V:ℝ) := by
    rintro ⟨v,b⟩
    cases b
    · exact in_variance_bound D v
    · exact out_variance_bound D v
  obtain ⟨s,hDegree,hCuts⟩ := hN p hp hp1 rows (fun ST => weight D ST.1 ST.2) hn hVar
    (fun ST => cut_variance_bound D ST.1 ST.2)
  refine ⟨selected D s,selected_le D s,?_,?_,?_⟩
  · intro v
    have hh := hDegree (v,false)
    change |BiasedDegreeCutSelection.value p (weight D univ {v}) s| < ε*(Fintype.card V:ℝ) at hh
    rw [biased_cut_identity,incidences_degree,incidences_degree] at hh
    exact hh
  · intro v
    have hh := hDegree (v,true)
    change |BiasedDegreeCutSelection.value p (weight D {v} univ) s| < ε*(Fintype.card V:ℝ) at hh
    rw [biased_cut_identity,incidences_outDegree,incidences_outDegree] at hh
    exact hh
  · intro S T
    have hh := hCuts S T
    rw [biased_cut_identity] at hh
    exact hh

theorem exists_selection (p ε : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 < ε) :
    ∃ N : ℕ,∀ {V : Type u} [Fintype V] [DecidableEq V]
      (D : Digraph V),N ≤ Fintype.card V →
      ∃ H : Digraph V,H ≤ D ∧
        (∀ v,|(inDegree H v:ℝ)-p*(inDegree D v:ℝ)| < ε*(Fintype.card V:ℝ)) ∧
        (∀ v,|(outDegree H v:ℝ)-p*(outDegree D v:ℝ)| < ε*(Fintype.card V:ℝ)) ∧
        ∀ S T : Finset V,|(incidences H S T:ℝ)-p*(incidences D S T:ℝ)| <
          ε*(Fintype.card V:ℝ)^2 := by
  obtain ⟨N,hN⟩ := exists_selection_uniform.{u} ε hε
  exact ⟨N,hN p hp hp1⟩

end OverfullWork.DirectedBiasedSplit

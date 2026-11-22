module

public import OverfullWork.MaximumCoreThreeCrossRound

@[expose] public section


/-! Exact budget transport for the constructed three-cross-edge round. -/
namespace OverfullWork.MaximumCoreThreeCrossRound
open SimpleGraph Finset OddCutDeficit NormalizedAlmostStoppingRun
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 24000000

theorem Round.core_deficit_fixed {G : SimpleGraph V} [DecidableRel G.Adj] {X U : Finset V}
    (r : Round G X U) :
    deficitMass (G\r.matching) (G\r.matching).maxDegree X=deficitMass G G.maxDegree X := by
  apply sum_congr rfl
  intro v hv
  have hSum : (G\r.matching).degree v+r.matching.degree v=G.degree v := by
    simpa only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
      MaximumMatching.degree_sdiff_add_of_le G r.matching r.le_original v
  rw [r.core_degrees v hv] at hSum
  rw [r.residual_maxDegree]
  have hMax := G.degree_le_maxDegree v
  omega

theorem Round.merged_degree_add_three {G : SimpleGraph V} [DecidableRel G.Adj] {X U : Finset V}
    (r : Round G X U) (hU : U ⊆ Xᶜ) (hThree : U.card=3) :
    (∑ v ∈ Xᶜ, (G\r.matching).degree v)+3=∑ v ∈ Xᶜ, G.degree v := by
  have hPoint : ∀ v, (G\r.matching).degree v+r.matching.degree v=G.degree v := by
    intro v
    simpa only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
      MaximumMatching.degree_sdiff_add_of_le G r.matching r.le_original v
  have hSum := sum_congr (s₁ := Xᶜ) (s₂ := Xᶜ) rfl (fun v _ => hPoint v)
  rw [sum_add_distrib] at hSum
  have hSelected : (∑ v ∈ Xᶜ, r.matching.degree v)=3 := by
    rw [sum_congr rfl (fun v hv => r.complementary_degrees v hv)]
    have hFilter : Xᶜ.filter (fun v => v ∈ U)=U := by
      ext v
      simp only [mem_filter]
      exact ⟨fun hh => hh.2,fun hh => ⟨hU hh,hh⟩⟩
    have hCount : (∑ v ∈ Xᶜ, if v ∈ U then 1 else 0)=(Xᶜ.filter (fun v => v ∈ U)).card := by simp [filter_mem_eq_inter]
    rw [hCount,hFilter,hThree]
  rw [hSelected] at hSum
  exact hSum

theorem Round.budget_drop_three {G : SimpleGraph V} [DecidableRel G.Adj] {X U : Finset V}
    (r : Round G X U) (hU : U ⊆ Xᶜ) (hThree : U.card=3) :
    (deficitMass (G\r.matching) (G\r.matching).maxDegree X+
      (∑ v ∈ Xᶜ, (G\r.matching).degree v))+3=
      deficitMass G G.maxDegree X+(∑ v ∈ Xᶜ, G.degree v) := by
  rw [r.core_deficit_fixed]
  have hh := r.merged_degree_add_three hU hThree
  omega

theorem Round.budget_bound_improves_two {G : SimpleGraph V} [DecidableRel G.Adj] {X U : Finset V}
    (r : Round G X U) (hU : U ⊆ Xᶜ) (hThree : U.card=3) (hX : X.Nonempty) (B : ℕ)
    (hBudget : deficitMass G G.maxDegree X+(∑ v ∈ Xᶜ, G.degree v) ≤ G.maxDegree+B) :
    (deficitMass (G\r.matching) (G\r.matching).maxDegree X+
      (∑ v ∈ Xᶜ, (G\r.matching).degree v))+2 ≤ (G\r.matching).maxDegree+B := by
  have hDrop := r.budget_drop_three hU hThree
  have hPos : 0 < G.maxDegree := by
    obtain ⟨v,hv⟩ := hX
    have hOne := r.core_degrees v hv
    have hLe := r.matching.degree_le_of_le r.le_original (v := v)
    have hMax := G.degree_le_maxDegree v
    omega
  have hMax := r.residual_maxDegree
  omega

end OverfullWork.MaximumCoreThreeCrossRound

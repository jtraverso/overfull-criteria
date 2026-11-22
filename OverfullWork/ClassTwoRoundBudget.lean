module

public import OverfullWork.FixedCoreBudgetTransport

@[expose] public section


/-! # Exact budget change in a class-two matching round

This is the fixed-core counting identity underlying CMS Claim 4.5(3).
It needs actual matching degrees and the maximum drop, not criticality.
-/
namespace OverfullWork.ClassTwoMatchingRound
open SimpleGraph Finset OddCutDeficit ClassTwoMatchingRound
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 5000000

theorem CoreRound.anchor_degree_eq {G : SimpleGraph V} [DecidableRel G.Adj]
    {X : Finset V} {x y z : V}
    (r : CoreRound G X x y z) (hx : x∈X) :
    (G\r.matching).degree x=G.degree x := by
  have hs:(G\r.matching).degree x+r.matching.degree x=G.degree x:=by
    simpa only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
      MaximumMatching.degree_sdiff_add_of_le G r.matching r.le_original x
  rw [r.core_degrees x hx,if_pos rfl] at hs
  omega


theorem CoreRound.merged_degree_add_two {G : SimpleGraph V} [DecidableRel G.Adj]
    {X : Finset V} {x y z : V}
    (r : CoreRound G X x y z) (hy : y∈Xᶜ) (hz : z∈Xᶜ) (hyz : y≠z) :
    (∑v∈Xᶜ,(G\r.matching).degree v)+2=∑v∈Xᶜ,G.degree v := by
  have hS:∀v,(G\r.matching).degree v+r.matching.degree v=G.degree v:=by
    intro v
    simpa only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
      MaximumMatching.degree_sdiff_add_of_le G r.matching r.le_original v
  have hSum:=sum_congr (s₁:=Xᶜ) (s₂:=Xᶜ) rfl (fun v _=>hS v)
  rw [sum_add_distrib] at hSum
  have hSelected:(∑v∈Xᶜ,r.matching.degree v)=2:=by
    rw [sum_congr rfl (fun v hv=>r.complementary_degrees v hv)]
    have hSplit:∀v:V,(if v=y ∨ v=z then 1 else 0)=
        (if v=y then 1 else 0)+(if v=z then 1 else 0):=by
      intro v
      by_cases hvy:v=y <;> by_cases hvz:v=z <;> simp_all
    simp_rw [hSplit]
    rw [sum_add_distrib]
    simp [hy,hz]
  rw [hSelected] at hSum
  exact hSum


theorem CoreRound.deficit_mass_add_one {G : SimpleGraph V} [DecidableRel G.Adj]
    {X : Finset V} {x y z : V}
    (r : CoreRound G X x y z) (hx : x∈X) (hxD : G.degree x<G.maxDegree) :
    deficitMass (G\r.matching) (G\r.matching).maxDegree X+1=
      deficitMass G G.maxDegree X := by
  rw [r.residual_maxDegree]
  have hPoint:∀v∈X,((G.maxDegree-1)-(G\r.matching).degree v)+
      (if v=x then 1 else 0)=G.maxDegree-G.degree v:=by
    intro v hv
    have hS:(G\r.matching).degree v+r.matching.degree v=G.degree v:=by
      simpa only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
        MaximumMatching.degree_sdiff_add_of_le G r.matching r.le_original v
    have hD:=G.degree_le_maxDegree v
    rw [r.core_degrees v hv] at hS
    by_cases hvx:v=x
    · subst v
      rw [if_pos rfl] at hS ⊢
      omega
    · rw [if_neg hvx] at hS ⊢
      omega
  have hSum:=sum_congr rfl hPoint
  rw [sum_add_distrib] at hSum
  have hOne:(∑v∈X,if v=x then 1 else 0)=1:=by simp [hx]
  rw [hOne] at hSum
  exact hSum


theorem CoreRound.budget_drop_three {G : SimpleGraph V} [DecidableRel G.Adj]
    {X : Finset V} {x y z : V} (r : CoreRound G X x y z)
    (hx : x∈X) (hxD : G.degree x<G.maxDegree)
    (hy : y∈Xᶜ) (hz : z∈Xᶜ) (hyz : y≠z) :
    (deficitMass (G\r.matching) (G\r.matching).maxDegree X+
      (∑v∈Xᶜ,(G\r.matching).degree v))+3=
      deficitMass G G.maxDegree X+(∑v∈Xᶜ,G.degree v) := by
  have hDef:=r.deficit_mass_add_one hx hxD
  have hSum:=r.merged_degree_add_two hy hz hyz
  omega

/-- Cleanup does not consume any extra fixed-core budget. The matching
accounts for exactly three units, even when cleanup deletes many edges. -/
theorem CoreRound.cleaned_budget_drop_three {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    {X : Finset V} {x y z : V} (r : CoreRound G X x y z)
    (hx : x∈X) (hxD : G.degree x<G.maxDegree)
    (hy : y∈Xᶜ) (hz : z∈Xᶜ) (hyz : y≠z)
    (hInd : G.IsIndepSet (↑(Xᶜ):Set V))
    (hLe : H≤G\r.matching)
    (hCore : H.induce (X:Set V)=(G\r.matching).induce (X:Set V))
    (hMax : H.maxDegree=(G\r.matching).maxDegree) :
    (deficitMass H H.maxDegree X+(∑v∈Xᶜ,H.degree v))+3=
      deficitMass G G.maxDegree X+(∑v∈Xᶜ,G.degree v) := by
  have hRInd:=FixedCoreBudgetTransport.independent_of_le G (G\r.matching) Xᶜ hInd sdiff_le
  have hHInd:=FixedCoreBudgetTransport.independent_of_le (G\r.matching) H Xᶜ hRInd hLe
  have hBudget:=FixedCoreBudgetTransport.budget_eq_of_fixed_core (G\r.matching) H X hCore hMax hRInd hHInd
  have hDrop:=r.budget_drop_three hx hxD hy hz hyz
  omega

end OverfullWork.ClassTwoMatchingRound

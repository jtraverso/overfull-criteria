module

public import OverfullWork.CMSOperation41ExactRecords
public import OverfullWork.CriticalAlmostPairNormalization
public import OverfullWork.ClassTwoMatchingRun

@[expose] public section


/-! The Stage I stopping record supplies an actual near-tight odd cut
for Stage II. Two omitted high-degree vertices would already spend
more than the entire outside degree budget. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph OddCutDeficit
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem actual_almost_stop_of_degree_record (G : SimpleGraph V) [DecidableRel G.Adj]
    (active : Finset V) (degree : V → ℕ) (b : ℕ)
    (hPositive : ∀ v,0 < G.degree v → v ∈ active)
    (hExact : ∀ v ∈ active,degree v = G.degree v)
    (hStop : HasAlmostOverfullRecord active G.maxDegree b degree) :
    ∃ X ⊆ active,Odd X.card ∧ ClassTwoMatchingRun.budget G X ≤ G.maxDegree+b := by
  obtain ⟨X,hX,hOdd,hMass⟩ := hStop
  have hOutside : (∑ v ∈ active \ X,G.degree v) = ∑ v ∈ Xᶜ,G.degree v := by
    have hSub : active \ X ⊆ Xᶜ := fun v hv => mem_compl.mpr (mem_sdiff.mp hv).2
    apply sum_subset hSub
    intro v hv hn
    by_contra hm
    exact hn (mem_sdiff.mpr ⟨hPositive v (Nat.pos_of_ne_zero hm),mem_compl.mp hv⟩)
  rw [sum_congr rfl (fun v hv => by rw [hExact v (hX hv)]),
    sum_congr rfl (fun v hv => hExact v (mem_sdiff.mp hv).1),hOutside] at hMass
  exact ⟨X,hX,hOdd,hMass⟩

theorem complement_of_almost_stop_le_exceptional_add_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (X U : Finset V) (a b : ℕ)
    (hBudget : ClassTwoMatchingRun.budget G X ≤ G.maxDegree+b)
    (hHigh : ∀ v,v ∉ U → G.maxDegree ≤ G.degree v+a)
    (hRoom : 2*a+b+1 ≤ G.maxDegree) :
    Xᶜ.card ≤ U.card+1 := by
  have hOutside : (∑ v ∈ Xᶜ,G.degree v) ≤ G.maxDegree+b := by
    unfold ClassTwoMatchingRun.budget at hBudget
    omega
  have hFew : (Xᶜ \ U).card ≤ 1 := by
    apply card_le_one.mpr
    intro y hy z hz
    by_contra hne
    have hy' := mem_sdiff.mp hy
    have hz' := mem_sdiff.mp hz
    have hD₁ := hHigh y hy'.2
    have hD₂ := hHigh z hz'.2
    have hBoth := CriticalAlmostPairNormalization.pair_degree_sum_le G Xᶜ y z hy'.1 hz'.1 hne
    omega
  have hSum := card_sdiff_add_card_inter Xᶜ U
  have hInter : (Xᶜ∩U).card ≤ U.card := card_le_card inter_subset_right
  omega

theorem localized_actual_almost_stop_of_degree_record (G : SimpleGraph V) [DecidableRel G.Adj]
    (active U : Finset V) (degree : V → ℕ) (a b : ℕ)
    (hPositive : ∀ v,0 < G.degree v → v ∈ active)
    (hExact : ∀ v ∈ active,degree v = G.degree v)
    (hStop : HasAlmostOverfullRecord active G.maxDegree b degree)
    (hHigh : ∀ v,v ∉ U → G.maxDegree ≤ G.degree v+a)
    (hRoom : 2*a+b+1 ≤ G.maxDegree) :
    ∃ X ⊆ active,Odd X.card ∧ Xᶜ.card ≤ U.card+1 ∧ ClassTwoMatchingRun.budget G X ≤ G.maxDegree+b := by
  obtain ⟨X,hX,hOdd,hBudget⟩ := actual_almost_stop_of_degree_record G active degree b hPositive hExact hStop
  exact ⟨X,hX,hOdd,complement_of_almost_stop_le_exceptional_add_one G X U a b hBudget hHigh hRoom,hBudget⟩

end OverfullWork.CMSTrimmingRound

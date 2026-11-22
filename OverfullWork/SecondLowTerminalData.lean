module

public import OverfullWork.BoundedWeightBipartition

@[expose] public section


/-! The full second-low witness is retained, including the vertex that pays
the degree imbalance after the two identifications. -/
namespace OverfullWork.NormalizedClassTwoStep
open SimpleGraph Finset OddCutDeficit
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {B K : ℕ}
set_option maxHeartbeats 5000000

structure SecondLowData (s : State V B K) where
  anchor : V
  anchor_mem : anchor ∈ s.cut.set
  large : s.graph.degree anchor < ∑ y ∈ s.cut.setᶜ, s.graph.degree y
  other : V
  other_mem : other ∈ s.cut.set
  other_ne : other ≠ anchor
  other_low : s.graph.degree other ≤ s.graph.maxDegree-s.graph.degree anchor
  independent : s.graph.IsIndepSet (↑(insert anchor s.cut.setᶜ):Set V)

abbrev SecondLowData.exceptional {s : State V B K} (p : SecondLowData s) : Finset V :=
  insert p.anchor s.cut.setᶜ

theorem SecondLowData.complement {s : State V B K} (p : SecondLowData s) :
    p.exceptionalᶜ=s.cut.set.erase p.anchor := by
  ext u
  simp only [SecondLowData.exceptional,mem_compl,mem_insert,not_or,not_not,mem_erase]

theorem SecondLowData.card_bound {s : State V B K} (p : SecondLowData s) :
    p.exceptional.card ≤ K+1 := by
  change (insert p.anchor s.cut.setᶜ).card ≤ K+1
  have h := card_insert_le p.anchor s.cut.setᶜ
  have hb := s.cut.complement_small
  omega

theorem SecondLowData.even_complement {s : State V B K} (p : SecondLowData s) :
    Even p.exceptionalᶜ.card := by
  rw [p.complement,card_erase_of_mem p.anchor_mem]
  obtain ⟨k,hk⟩ := s.cut.odd
  exact ⟨k,by omega⟩

theorem SecondLowData.degree_bounds {s : State V B K} (p : SecondLowData s) :
    s.graph.degree p.anchor < B ∧
    (∀ z ∈ p.exceptional, s.graph.degree z ≤ s.graph.degree p.anchor) ∧
    2*s.graph.degree p.anchor < (∑ z ∈ p.exceptional, s.graph.degree z) ∧
    (∑ z ∈ p.exceptional, s.graph.degree z) ≤ 2*B := by
  have hb := NormalizedTerminalLiteratureBridge.second_low_degree_bounds s.graph s.cut
    p.anchor_mem p.large p.other_mem p.other_ne p.other_low
  have ha : p.anchor ∉ s.cut.setᶜ := by simpa using p.anchor_mem
  have hSum : (∑ z ∈ p.exceptional, s.graph.degree z)=s.graph.degree p.anchor+
      (∑ y ∈ s.cut.setᶜ, s.graph.degree y) := sum_insert ha
  refine ⟨hb.2.1,?_,by have hh:=p.large;omega,by omega⟩
  intro z hz
  rcases mem_insert.mp hz with rfl|hz
  · exact le_rfl
  · exact s.cut.ordered z hz p.anchor p.anchor_mem

theorem SecondLowData.ordinary_deficit_bounds {s : State V B K} (p : SecondLowData s) :
    s.graph.degree p.anchor ≤ deficitMass s.graph s.graph.maxDegree p.exceptionalᶜ ∧
    deficitMass s.graph s.graph.maxDegree p.exceptionalᶜ ≤ B := by
  rw [p.complement]
  have hBudget := LargeCentreCriticalGeometry.deficit_and_excess_le s.graph s.cut p.anchor_mem p.large
  have hOther : s.graph.maxDegree-s.graph.degree p.other ≤
      deficitMass s.graph s.graph.maxDegree (s.cut.set.erase p.anchor) :=
    single_le_sum (f:=fun v => s.graph.maxDegree-s.graph.degree v)
      (fun _ _ => Nat.zero_le _) (mem_erase.mpr ⟨p.other_ne,p.other_mem⟩)
  have hD := s.graph.degree_le_maxDegree p.anchor
  have hLow := p.other_low
  omega

theorem reduced_terminal_second_low_or_candidate (s : State V B K) (hM : Margins s)
    (hT : ReducedTerminal s) :
    (∃ p : NormalizedCanonicalCandidate.Candidate s.cut, p.centre=(0,false)) ∨
      Nonempty (SecondLowData s) := by
  rcases hT with hSmall|hLow
  · left
    apply NormalizedCanonicalCandidate.exists_centred_candidate s.graph s.cut s.no_overfull _ hSmall
    have hY := s.cut.complement_small
    have hParts := card_add_card_compl s.cut.set
    have hMatch := hM.1
    omega
  · obtain ⟨x,hx,_,hLarge,v,hv,hvx,hLow,hInd⟩ := hLow
    exact Or.inr ⟨⟨x,hx,hLarge,v,hv,hvx,hLow,hInd⟩⟩

structure SecondLowData.Partition {s : State V B K} (p : SecondLowData s) where
  left : Finset V
  subset : left ⊆ p.exceptional
  left_nonempty : left.Nonempty
  right_nonempty : (p.exceptional\left).Nonempty
  positive : 0 < ∑ z ∈ left, s.graph.degree z
  ordered : (∑ z ∈ left, s.graph.degree z) ≤ ∑ z ∈ p.exceptional\left, s.graph.degree z
  imbalance : (∑ z ∈ p.exceptional\left, s.graph.degree z) ≤
    (∑ z ∈ left, s.graph.degree z)+s.graph.degree p.anchor

theorem SecondLowData.exists_partition {s : State V B K} (p : SecondLowData s) :
    Nonempty p.Partition := by
  obtain ⟨A,hA,hNonA,hNonB,hPos,hOrder,hGap⟩ :=
    BoundedWeightBipartition.exists_nonempty_balanced p.exceptional
      (fun z => s.graph.degree z) (s.graph.degree p.anchor) p.degree_bounds.2.1 p.degree_bounds.2.2.1
  exact ⟨⟨A,hA,hNonA,hNonB,hPos,hOrder,hGap⟩⟩

end OverfullWork.NormalizedClassTwoStep

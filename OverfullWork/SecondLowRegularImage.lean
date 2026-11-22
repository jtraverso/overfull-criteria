module

public import OverfullWork.SecondLowTerminalData
public import OverfullWork.TwoIdentificationMultiplicities
public import OverfullWork.TwoCentreRegularCompletion
public import OverfullWork.CanonicalColouringPullback

@[expose] public section


/-! Actual even multigraph and regular completion of the second-low terminal.
Colourings pull back, and the Class 2 obstruction is retained. Regularity
is not used as a substitute for a factorization theorem. -/
namespace OverfullWork.NormalizedClassTwoStep
open SimpleGraph Finset OddCutDeficit TwoIndependentIdentifications
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {B K : ℕ} {s : State V B K}
set_option maxHeartbeats 8000000

noncomputable def SecondLowData.Partition.image {p : SecondLowData s} (q : p.Partition) :
    MultiGraph (Vertices p.exceptional) :=
  graph s.graph p.exceptional q.left q.subset p.independent

theorem SecondLowData.Partition.centre_sum {p : SecondLowData s} (q : p.Partition) :
    q.image.degree (Sum.inl false)+q.image.degree (Sum.inl true)=
      ∑ z ∈ p.exceptional, s.graph.degree z := by
  rw [Partition.image,degree_inl,degree_inl]
  simpa only [part,Bool.false_eq_true,if_false,if_true,Nat.add_comm] using
    sum_sdiff q.subset (f:=fun z => s.graph.degree z)

theorem SecondLowData.Partition.ordinary_deficit {p : SecondLowData s} (q : p.Partition) :
    TwoCentreRegularCompletion.ordinaryDeficit q.image s.graph.maxDegree=
      deficitMass s.graph s.graph.maxDegree p.exceptionalᶜ := by
  unfold TwoCentreRegularCompletion.ordinaryDeficit
  simp_rw [Partition.image,degree_inr]
  exact (sum_subtype p.exceptionalᶜ (fun v => mem_compl)
    (fun v => s.graph.maxDegree-s.graph.degree v)).symm

theorem SecondLowData.Partition.profile {p : SecondLowData s} (q : p.Partition) :
    q.image.degree (Sum.inl false) ≤ q.image.degree (Sum.inl true) ∧
    q.image.degree (Sum.inl true) ≤ q.image.degree (Sum.inl false)+
      TwoCentreRegularCompletion.ordinaryDeficit q.image s.graph.maxDegree ∧
    q.image.degree (Sum.inl false)+q.image.degree (Sum.inl true) ≤ 2*B ∧
    TwoCentreRegularCompletion.ordinaryDeficit q.image s.graph.maxDegree ≤ B := by
  have hA : q.image.degree (Sum.inl false)=∑ z ∈ q.left, s.graph.degree z := by
    rw [Partition.image,degree_inl];rfl
  have hB : q.image.degree (Sum.inl true)=∑ z ∈ p.exceptional\q.left, s.graph.degree z := by
    rw [Partition.image,degree_inl];rfl
  have hD := p.ordinary_deficit_bounds
  have hSum := q.centre_sum
  have hBound := p.degree_bounds.2.2.2
  rw [←q.ordinary_deficit] at hD
  exact ⟨by rw [hA,hB];exact q.ordered,
    by have hh:=q.imbalance;omega,by omega,hD.2⟩

theorem SecondLowData.Partition.degree_le {p : SecondLowData s} (q : p.Partition)
    (hM : Margins s) : ∀ v, q.image.degree v ≤ s.graph.maxDegree := by
  intro v
  have hSum := q.profile.2.2.1
  have hDense := hM.2.2
  cases v with
  | inl i => cases i <;> omega
  | inr x => rw [Partition.image,degree_inr];exact s.graph.degree_le_maxDegree x.val

theorem SecondLowData.Partition.uncolourable {p : SecondLowData s} (q : p.Partition) :
    ¬Nonempty (q.image.EdgeColoring s.graph.maxDegree) := by
  rintro ⟨C⟩
  exact s.uncolourable (colourable_of_identifications s.graph p.exceptional q.left q.subset p.independent C)

theorem SecondLowData.Partition.source_colourable_of_completed {p : SecondLowData s}
    (q : p.Partition) (J : MultiGraph (Vertices p.exceptional)) {d : ℕ}
    (C : (q.image.addCopies J).EdgeColoring d) : s.graph.EdgeColorable d := by
  obtain ⟨F⟩ := CanonicalColouringPullback.restrict_copies q.image (q.image.addCopies J) C
    (fun _ => Nat.le_add_right _ _)
  exact colourable_of_identifications s.graph p.exceptional q.left q.subset p.independent F

theorem SecondLowData.Partition.exists_regular_completion {p : SecondLowData s}
    (q : p.Partition) (hM : Margins s) :
    ∃ J : MultiGraph (Vertices p.exceptional),
      (∀ v, J.degree v=s.graph.maxDegree-q.image.degree v) ∧
      (q.image.addCopies J).IsRegularOfDegree s.graph.maxDegree ∧
      J.twiceInternal (univ.erase (Sum.inl false)) ≤ B ∧
      s.graph.maxDegree ≤ (q.image.addCopies J).mult s(Sum.inl false,Sum.inl true)+3*B ∧
      ¬Nonempty ((q.image.addCopies J).EdgeColoring s.graph.maxDegree) := by
  have hP := q.profile
  have hSmall : TwoCentreRegularCompletion.ordinaryDeficit q.image s.graph.maxDegree+
      q.image.degree (Sum.inl false)+q.image.degree (Sum.inl true) ≤ 2*s.graph.maxDegree := by
    have hDense := hM.2.2
    omega
  obtain ⟨J,hJ,hReg⟩ := TwoCentreRegularCompletion.exists_completion q.image s.graph.maxDegree
    (q.degree_le hM) (even_card_vertices p.exceptional p.even_complement) hP.1 hP.2.1 hSmall
  have hOff := TwoCentreRegularCompletion.added_off_first_centre q.image J s.graph.maxDegree hReg hP.1
  have hPair := TwoCentreRegularCompletion.pair_reserve q.image J s.graph.maxDegree hJ
  refine ⟨J,hJ,hReg,by omega,by omega,?_⟩
  rintro ⟨C⟩
  exact s.uncolourable (q.source_colourable_of_completed J C)

theorem reduced_terminal_candidate_or_regular_two_centre_image (s : State V B K)
    (hM : Margins s) (hT : ReducedTerminal s) :
    (∃ p : NormalizedCanonicalCandidate.Candidate s.cut, p.centre=(0,false)) ∨
    ∃ p : SecondLowData s, ∃ q : p.Partition, ∃ J : MultiGraph (Vertices p.exceptional),
      (q.image.addCopies J).IsRegularOfDegree s.graph.maxDegree ∧
      J.twiceInternal (univ.erase (Sum.inl false)) ≤ B ∧
      s.graph.maxDegree ≤ (q.image.addCopies J).mult s(Sum.inl false,Sum.inl true)+3*B ∧
      ¬Nonempty ((q.image.addCopies J).EdgeColoring s.graph.maxDegree) := by
  rcases reduced_terminal_second_low_or_candidate s hM hT with hSmall|hLow
  · exact Or.inl hSmall
  · obtain ⟨p⟩ := hLow
    obtain ⟨q⟩ := p.exists_partition
    obtain ⟨J,_,hReg,hOff,hPair,hNC⟩ := q.exists_regular_completion hM
    exact Or.inr ⟨p,q,J,hReg,hOff,hPair,hNC⟩

end OverfullWork.NormalizedClassTwoStep

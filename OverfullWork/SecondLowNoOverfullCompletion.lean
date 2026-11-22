module

public import OverfullWork.SecondLowRegularImage
public import OverfullWork.TwoIdentificationInternalCounts

@[expose] public section


/-! No-overfullness of an actual two-centre regular completion.
All added edges meet a centre, so all-ordinary odd sets inherit the
original no-overfull bound. Every other nontrivial cut is paid by the
high-degree simple ordinary core. No criticality of the terminal is used. -/
namespace OverfullWork.NormalizedClassTwoStep
open SimpleGraph Finset OddCutDeficit TwoIndependentIdentifications TwoCentreOrdinaryCore
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {B K : ℕ} {s : State V B K}
set_option maxHeartbeats 10000000

theorem SecondLowData.Partition.exists_star_completion_no_overfull {p : SecondLowData s}
    (q : p.Partition) (hM : Margins s) :
    ∃ J : MultiGraph (Vertices p.exceptional),
      (∀ v, J.degree v=s.graph.maxDegree-q.image.degree v) ∧
      (q.image.addCopies J).IsRegularOfDegree s.graph.maxDegree ∧
      (∀ u v : Outside p.exceptional, J.mult s(Sum.inr u,Sum.inr v)=0) ∧
      ¬(q.image.addCopies J).HasOverfullSubset s.graph.maxDegree ∧
      J.twiceInternal (univ.erase (Sum.inl false)) ≤ B ∧
      s.graph.maxDegree ≤ (q.image.addCopies J).mult s(Sum.inl false,Sum.inl true)+3*B ∧
      ¬Nonempty ((q.image.addCopies J).EdgeColoring s.graph.maxDegree) := by
  have hP := q.profile
  have hSmall : TwoCentreRegularCompletion.ordinaryDeficit q.image s.graph.maxDegree+
      q.image.degree (Sum.inl false)+q.image.degree (Sum.inl true) ≤ 2*s.graph.maxDegree := by
    have hDense := hM.2.2
    omega
  obtain ⟨J,hJ,hReg,hJ0⟩ := TwoCentreStarCompletion.exists_completion q.image s.graph.maxDegree
    (q.degree_le hM) (even_card_vertices p.exceptional p.even_complement) hP.1 hP.2.1 hSmall
  have hOrd : ordinary (q.image.addCopies J)=ordinary q.image := by
    apply MultiGraph.ext_mult
    intro e
    induction e using Sym2.inductionOn with
    | hf u v =>
      change q.image.mult s(Sum.inr u,Sum.inr v)+J.mult s(Sum.inr u,Sum.inr v)=_
      rw [hJ0,Nat.add_zero]
      rfl
  have hCardOutside : Fintype.card (Outside p.exceptional)=p.exceptionalᶜ.card := by
    have hh := card_vertices p.exceptional
    rw [Fintype.card_sum,Fintype.card_bool] at hh
    omega
  obtain ⟨m,hm⟩ := p.even_complement
  have hCard : Fintype.card (Outside p.exceptional)=2*m := by omega
  have hParts := card_add_card_compl p.exceptional
  have hK := p.card_bound
  have hMax : s.graph.maxDegree < Fintype.card V := by
    have : Nonempty V := ⟨p.anchor⟩
    exact s.graph.maxDegree_lt_card_verts
  have hDense := hM.2.2
  have hMatch := hM.1
  let δ := s.graph.maxDegree-B-p.exceptional.card+1
  have hm3 : 3 ≤ m := by omega
  have hδ : m+2 ≤ δ := by dsimp only [δ];omega
  have hDδ : s.graph.maxDegree+2 ≤ 2*δ := by dsimp only [δ];omega
  have hDm : s.graph.maxDegree ≤ 3*m := by omega
  have hMin : ∀ v : Outside p.exceptional, δ ≤ (ordinary q.image).degree v := by
    intro v
    have hv : v.val ≠ p.anchor ∧ v.val ∈ s.cut.set := by
      simpa only [SecondLowData.exceptional,mem_insert,not_or,mem_compl,not_not] using v.property
    have hHigh := LargeCentreCriticalGeometry.other_degree_lower s.graph s.cut
      p.anchor_mem p.large hv.2 hv.1
    have hLoss := ordinary_degree_loss s.graph p.exceptional q.left q.subset p.independent v
    have hExcess : 1 ≤ (∑ y ∈ s.cut.setᶜ, s.graph.degree y)-s.graph.degree p.anchor := by
      have hh := p.large
      omega
    change δ ≤ (ordinary (graph s.graph p.exceptional q.left q.subset p.independent)).degree v
    dsimp only [δ]
    omega
  have hNo : ¬(q.image.addCopies J).HasOverfullSubset s.graph.maxDegree := by
    apply no_overfull_of_ordinary (q.image.addCopies J) m δ s.graph.maxDegree hReg hCard hm3
    · rw [hOrd]
      exact mult_inr_le s.graph p.exceptional q.left q.subset p.independent
    · rw [hOrd];exact hMin
    · exact hδ
    · exact hDδ
    · exact hDm
    · rw [hOrd]
      exact no_overfull_ordinary s.graph p.exceptional q.left q.subset p.independent s.no_overfull
  have hOff := TwoCentreRegularCompletion.added_off_first_centre q.image J s.graph.maxDegree hReg hP.1
  have hPair := TwoCentreRegularCompletion.pair_reserve q.image J s.graph.maxDegree hJ
  refine ⟨J,hJ,hReg,hJ0,hNo,by omega,by omega,?_⟩
  rintro ⟨C⟩
  exact s.uncolourable (q.source_colourable_of_completed J C)

end OverfullWork.NormalizedClassTwoStep

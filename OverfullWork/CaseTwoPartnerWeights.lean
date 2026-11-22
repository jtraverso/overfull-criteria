module

public import OverfullWork.CanonicalCaseTwoPartition
public import OverfullWork.CMSCaseTwoPartnerWeights

@[expose] public section


/-! # Translate the actual partner bijection and CMS (5.5) into copy budgets

The numeric allocation's hypotheses are proved from the constructed
partition. The second vertex has partner weight zero, corresponding to
the loopless centre. All other heavy partner weights use the actual
finite equivalence supplied by the partition.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun RegularHeavyCutRepair
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T : ℕ} {η : ℝ} {b : Fin (p.pairIndex+1) × Bool}
set_option maxHeartbeats 8000000

/-- Use the same cut in the general copy-allocation lemmas. -/
def Candidate.CaseTwoPartition.asCMS (s : p.CaseTwoPartition P T η b) :
    CMSBalancedCut.CaseTwoPartition p.completed p.centre b G.maxDegree (p.pairIndex+1)
      ((p.pairIndex+1)/T) ((p.pairIndex+1)/(2^30*P^3)-4*(3*T+1))
      ((p.pairIndex+1)/(1024*P)+2*(3*T+1)) η where
  part := s.part
  partners := s.partners
  card_part := s.card_part
  card_compl := s.card_compl
  centre_mem := s.centre_mem
  second_not_mem := s.second_not_mem
  partnerEquiv := s.partnerEquiv
  partners_subset := s.partners_subset
  centre_not_partner := s.centre_not_partner
  second_not_partner := s.second_not_partner
  partners_light := s.partners_light
  heavy_across := s.heavy_across
  free_weight_le := s.free_weight_le
  centre_internal_le_half := s.centre_internal_le_half
  robust := s.robust
  simple_discrepancy := s.simple_discrepancy

noncomputable def Candidate.CaseTwoPartition.heavyVertices (s : p.CaseTwoPartition P T η b) :
    Finset (Fin (p.pairIndex+1) × Bool) := insert b (heavySet p.completed p.centre b ((p.pairIndex+1)/T))

noncomputable def Candidate.CaseTwoPartition.partnerWeight (s : p.CaseTwoPartition P T η b)
    (v : Fin (p.pairIndex+1) × Bool) : ℕ :=
  if hv : v ∈ heavySet p.completed p.centre b ((p.pairIndex+1)/T) then
    p.completed.mult s(p.centre,(s.partnerEquiv ⟨v,hv⟩).val) else 0

noncomputable def Candidate.CaseTwoPartition.crossWeight (s : p.CaseTwoPartition P T η b)
    (v : Fin (p.pairIndex+1) × Bool) : ℕ :=
  if v ∈ s.partᶜ then p.completed.mult s(p.centre,v) else 0

theorem Candidate.CaseTwoPartition.heavy_subset_compl (s : p.CaseTwoPartition P T η b) :
    s.heavyVertices ⊆ s.partᶜ :=
  s.asCMS.heavy_subset_compl

theorem Candidate.CaseTwoPartition.partnerWeight_outside (s : p.CaseTwoPartition P T η b)
    (v : Fin (p.pairIndex+1) × Bool) (hv : v ∉ s.heavyVertices) : s.partnerWeight v = 0 :=
  s.asCMS.partnerWeight_outside v hv

theorem Candidate.CaseTwoPartition.partnerWeight_le (s : p.CaseTwoPartition P T η b)
    (v : Fin (p.pairIndex+1) × Bool) : s.partnerWeight v ≤ s.crossWeight v :=
  s.asCMS.partnerWeight_le v

theorem Candidate.CaseTwoPartition.sum_partnerWeight (s : p.CaseTwoPartition P T η b) :
    (∑ v, s.partnerWeight v) = p.completed.degreeInto s.partners p.centre :=
  s.asCMS.sum_partnerWeight

theorem Candidate.CaseTwoPartition.partner_budget (s : p.CaseTwoPartition P T η b) :
    (∑ v, s.partnerWeight v) ≤ p.completed.degreeInto s.part p.centre :=
  s.asCMS.partner_budget

theorem Candidate.CaseTwoPartition.cross_total (s : p.CaseTwoPartition P T η b) :
    (∑ v, s.crossWeight v) = p.completed.degreeInto s.partᶜ p.centre :=
  s.asCMS.cross_total

theorem Candidate.CaseTwoPartition.cross_ge_internal (s : p.CaseTwoPartition P T η b) :
    p.completed.degreeInto s.part p.centre ≤ p.completed.degreeInto s.partᶜ p.centre :=
  s.asCMS.cross_ge_internal p.completion.regular

theorem Candidate.CaseTwoPartition.paired_difference_budget (s : p.CaseTwoPartition P T η b) :
    (∑ v ∈ s.heavyVertices, (s.crossWeight v-s.partnerWeight v)) ≤
      p.completed.degreeInto s.partᶜ p.centre-p.completed.degreeInto s.part p.centre :=
  s.asCMS.paired_difference_budget

end OverfullWork.NormalizedCanonicalCandidate

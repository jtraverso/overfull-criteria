module

public import OverfullWork.CaseTwoMiddleCopies
public import OverfullWork.CMSCaseTwoMiddleDegreeProfile

@[expose] public section


/-! # Near-half degrees of the actual internal-plus-middle graph

This is a quantitative analogue of CMS Claim 5.1, with the integer
heavy cutoff and the explicit accumulated deficit of our allocation.
It does not assert the paper's printed constants.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun RegularHeavyCutRepair
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T : ℕ} {η : ℝ} {b w : Fin (p.pairIndex+1) × Bool}
variable {s : p.CaseTwoPartition P T η b}
set_option maxHeartbeats 10000000

theorem Candidate.off_centre_excess_le (p : Candidate c)
    (v : Fin (p.pairIndex+1) × Bool) (hv : v ≠ p.centre) :
    (∑ u ∈ univ.erase p.centre, (p.completed.mult s(v,u)-1)) ≤ B := by
  have hp : ∀ u ∈ univ.erase p.centre, (p.completed.mult s(v,u)-1) ≤
      (p.completion.L.addCopies p.completion.N).mult s(v,u) := by
    intro u hu
    have hh := p.ordered_star v u hv (mem_erase.mp hu).1
    change p.orderedBase.mult s(v,u)+p.completion.L.mult s(v,u)+p.completion.N.mult s(v,u)-1 ≤
      p.completion.L.mult s(v,u)+p.completion.N.mult s(v,u)
    omega
  exact (sum_le_sum hp).trans (CompletionOffCentreBudget.outside_row_le _ B p.centre v hv
    p.added_off_centre_internal_le)

theorem Candidate.CaseTwoPartition.partner_weight_light (s : p.CaseTwoPartition P T η b)
    (v : Fin (p.pairIndex+1) × Bool) : s.partnerWeight v ≤ (p.pairIndex+1)/T :=
  s.asCMS.partner_weight_light v

theorem Candidate.CaseTwoPartition.centred_discrepancy (s : p.CaseTwoPartition P T η b)
    (v : Fin (p.pairIndex+1) × Bool) (hv : v ≠ p.centre) :
    |2*(p.completed.degreeInto s.part v:ℝ)-(G.maxDegree:ℝ)-
      ((p.completed.mult s(p.centre,v)-1:ℕ):ℝ)| ≤ η*(p.pairIndex+1:ℕ)+(B:ℝ) :=
  s.asCMS.centred_discrepancy p.completion.regular p.off_centre_excess_le v hv

theorem Candidate.CaseTwoMiddleCopies.degree_profile (r : p.CaseTwoMiddleCopies s w)
    (v : Fin (p.pairIndex+1) × Bool) :
    |2*(r.graph.degree v:ℝ)-(G.maxDegree:ℝ)| ≤
      η*(p.pairIndex+1:ℕ)+(B:ℝ)+((p.pairIndex+1)/T:ℕ)+
      2*((p.completed.mult s(b,w)-p.completed.degreeInto s.part p.centre:ℕ):ℝ)+
      2*(s.heavyVertices.card:ℝ)+3 :=
  r.asCMS.degree_profile p.completion.regular p.off_centre_excess_le v

theorem Candidate.CaseTwoMiddleCopies.off_centre_multiplicity_le (r : p.CaseTwoMiddleCopies s w)
    (u v : Fin (p.pairIndex+1) × Bool) (hu : u ≠ p.centre) (hv : v ≠ p.centre) :
    r.graph.mult s(u,v) ≤ B+1 :=
  (r.graph_le _).trans (p.off_centre_bundle_le u v hu hv)

theorem Candidate.CaseTwoMiddleCopies.degree_profile_at_cutoff (r : p.CaseTwoMiddleCopies s w)
    (hw : w ∉ s.part) (hD : G.maxDegree ≤ 3*(p.pairIndex+1)) (hT : 1 ≤ T)
    (v : Fin (p.pairIndex+1) × Bool) :
    |2*(r.graph.degree v:ℝ)-(G.maxDegree:ℝ)| ≤
      η*(p.pairIndex+1:ℕ)+3*(B:ℝ)+((p.pairIndex+1)/T:ℕ)+6*(T:ℝ)+7 := by
  have hb : b ≠ p.centre := fun he => s.second_not_mem (he ▸ s.centre_mem)
  have hwc : w ≠ p.centre := fun he => hw (he ▸ s.centre_mem)
  have hq := p.off_centre_bundle_le b w hb hwc
  have hF : p.completed.mult s(b,w)-p.completed.degreeInto s.part p.centre ≤ B+1 :=
    (Nat.sub_le _ _).trans hq
  have hZ := heavySet_card_at_scale p.completed p.centre b G.maxDegree (p.pairIndex+1) T
    p.completion.regular hD hT
  have hH : s.heavyVertices.card ≤ 3*T+1 :=
    (card_insert_le _ _).trans (Nat.add_le_add_right hZ 1)
  have hFR : ((p.completed.mult s(b,w)-p.completed.degreeInto s.part p.centre:ℕ):ℝ) ≤ (B:ℝ)+1 := by
    exact_mod_cast hF
  have hHR : (s.heavyVertices.card:ℝ) ≤ 3*(T:ℝ)+1 := by exact_mod_cast hH
  have hh := r.degree_profile v
  linarith

end OverfullWork.NormalizedCanonicalCandidate

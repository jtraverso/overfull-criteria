module

public import OverfullWork.CaseTwoPartnerWeights
public import OverfullWork.CMSCaseTwoMiddleCopies
public import OverfullWork.CompletionOffCentreBudget

@[expose] public section


/-! # Actual CMS Case 2 middle-copy selections

The finite numerical side condition only pays for the off-centre
bundle budget. No colouring or factorization is assumed here.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun RegularHeavyCutRepair
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T : ℕ} {η : ℝ} {b w : Fin (p.pairIndex+1) × Bool}
set_option maxHeartbeats 8000000

theorem Candidate.off_centre_bundle_le (p : Candidate c)
    (u v : Fin (p.pairIndex+1) × Bool) (hu : u ≠ p.centre) (hv : v ≠ p.centre) :
    p.completed.mult s(u,v) ≤ B+1 := by
  have hbase := p.ordered_star u v hu hv
  have hrow := CompletionOffCentreBudget.outside_row_le _ B p.centre u hu
    p.added_off_centre_internal_le
  have hone := single_le_sum (f := fun x =>
    (p.completion.L.addCopies p.completion.N).mult s(u,x))
    (fun _ _ => Nat.zero_le _) (mem_erase.mpr ⟨hv,mem_univ v⟩)
  change p.completion.L.mult s(u,v)+p.completion.N.mult s(u,v) ≤
    (p.completion.L.addCopies p.completion.N).degreeInto (univ.erase p.centre) u at hone
  change p.orderedBase.mult s(u,v)+p.completion.L.mult s(u,v)+p.completion.N.mult s(u,v) ≤ B+1
  omega

noncomputable def Candidate.CaseTwoPartition.initialPriority (s : p.CaseTwoPartition P T η b)
    (w : Fin (p.pairIndex+1) × Bool) : Finset (Fin (p.pairIndex+1) × Bool) :=
  (heavySet p.completed p.centre b ((p.pairIndex+1)/T)).erase w

theorem Candidate.CaseTwoPartition.initialPriority_allowed (s : p.CaseTwoPartition P T η b)
    (w : Fin (p.pairIndex+1) × Bool) :
    s.initialPriority w ⊆ InitialMiddleCopies.allowed s.part b w := by
  intro v hv
  have hh := mem_erase.mp hv
  have hz := (heavySet_mem p.completed p.centre b v ((p.pairIndex+1)/T)).mp hh.2
  simp only [InitialMiddleCopies.allowed,mem_sdiff,mem_compl,mem_insert,mem_singleton]
  exact ⟨s.heavy_across v hz.1 hz.2,by tauto⟩

structure Candidate.CaseTwoMiddleCopies (s : p.CaseTwoPartition P T η b)
    (w : Fin (p.pairIndex+1) × Bool) where
  initial : InitialMiddleCopies.Selection p.completed s.part (s.initialPriority w) p.centre b w
  balancing : BalancedMiddleAllocation.Selection s.crossWeight initial.count s.partnerWeight s.heavyVertices
    (p.completed.degreeInto s.part p.centre) (p.completed.degreeInto s.partᶜ p.centre)
    (p.completed.mult s(b,w)-p.completed.degreeInto s.part p.centre)

theorem Candidate.CaseTwoPartition.exists_middle_copies (s : p.CaseTwoPartition P T η b)
    (hw : w ∉ s.part) (hbw : b ≠ w) (hNo : ¬p.completed.HasOverfullSubset G.maxDegree)
    (hSmall : 2*(B+1) ≤ G.maxDegree) : Nonempty (p.CaseTwoMiddleCopies s w) := by
  obtain ⟨s0⟩ := InitialMiddleCopies.exists_selection p.completed s.part (s.initialPriority w)
    p.centre b w G.maxDegree p.completion.regular hNo s.centre_mem s.second_not_mem hw hbw
    (s.initialPriority_allowed w)
  have hb : b ≠ p.centre := fun he => s.second_not_mem (he ▸ s.centre_mem)
  have hwc : w ≠ p.centre := fun he => hw (he ▸ s.centre_mem)
  have hq := p.off_centre_bundle_le b w hb hwc
  obtain ⟨copies⟩ := s.asCMS.middle_copies_of_initial w s0 p.completion.regular
    ((Nat.mul_le_mul_left 2 hq).trans hSmall)
  exact ⟨⟨copies.initial,copies.balancing⟩⟩

variable {s : p.CaseTwoPartition P T η b}

/-- Forget the ambient candidate when applying the common middle-copy estimates. -/
def Candidate.CaseTwoMiddleCopies.asCMS (r : p.CaseTwoMiddleCopies s w) :
    CMSBalancedCut.CaseTwoMiddleCopies s.asCMS w :=
  ⟨r.initial,r.balancing⟩

def Candidate.CaseTwoMiddleCopies.count (r : p.CaseTwoMiddleCopies s w)
    (v : Fin (p.pairIndex+1) × Bool) : ℕ := r.initial.count v+r.balancing.extra v

theorem Candidate.CaseTwoMiddleCopies.count_le (r : p.CaseTwoMiddleCopies s w)
    (v : Fin (p.pairIndex+1) × Bool) : r.count v ≤ s.crossWeight v := r.balancing.copies_le v

theorem Candidate.CaseTwoMiddleCopies.inside_zero (r : p.CaseTwoMiddleCopies s w)
    (v : Fin (p.pairIndex+1) × Bool) (hv : v ∈ s.part) : r.count v = 0 :=
  r.asCMS.inside_zero v hv

noncomputable def Candidate.CaseTwoMiddleCopies.graph (r : p.CaseTwoMiddleCopies s w) :
    MultiGraph (Fin (p.pairIndex+1) × Bool) :=
  MiddleCopyGraph.graph p.completed s.part p.centre r.count (r.inside_zero _ s.centre_mem)

theorem Candidate.CaseTwoMiddleCopies.graph_le (r : p.CaseTwoMiddleCopies s w) :
    ∀ e, r.graph.mult e ≤ p.completed.mult e :=
  r.asCMS.graph_le

theorem Candidate.CaseTwoMiddleCopies.centre_degree (r : p.CaseTwoMiddleCopies s w) :
    r.graph.degree p.centre = p.completed.degreeInto s.part p.centre+
      (p.completed.mult s(b,w)-p.completed.degreeInto s.part p.centre)+
      (p.completed.degreeInto s.partᶜ p.centre-p.completed.degreeInto s.part p.centre-
        (p.completed.mult s(b,w)-p.completed.degreeInto s.part p.centre))/2 :=
  r.asCMS.centre_degree

theorem Candidate.CaseTwoMiddleCopies.centre_bounds (r : p.CaseTwoMiddleCopies s w) :
    G.maxDegree-1 ≤ 2*r.graph.degree p.centre ∧
      2*r.graph.degree p.centre ≤ G.maxDegree+
        (p.completed.mult s(b,w)-p.completed.degreeInto s.part p.centre) :=
  r.asCMS.centre_bounds p.completion.regular

theorem Candidate.CaseTwoMiddleCopies.bundle_upper (r : p.CaseTwoMiddleCopies s w)
    (v : Fin (p.pairIndex+1) × Bool) :
    2*r.count v ≤ s.crossWeight v+
      (p.completed.mult s(b,w)-p.completed.degreeInto s.part p.centre)+1 := r.balancing.bundle_upper v

theorem Candidate.CaseTwoMiddleCopies.paired_lower (r : p.CaseTwoMiddleCopies s w)
    (v : Fin (p.pairIndex+1) × Bool) (hv : v ∈ s.heavyVertices) :
    s.crossWeight v ≤ 2*r.count v+s.partnerWeight v+2*r.balancing.deficit v :=
  r.balancing.paired_lower v hv

theorem Candidate.CaseTwoMiddleCopies.deficit_budget (r : p.CaseTwoMiddleCopies s w) :
    (∑ v, r.balancing.deficit v) ≤
      (p.completed.mult s(b,w)-p.completed.degreeInto s.part p.centre)+s.heavyVertices.card+1 :=
  r.balancing.deficit_sum

theorem Candidate.CaseTwoMiddleCopies.protected_triangle (r : p.CaseTwoMiddleCopies s w)
    (hw : w ∉ s.part) (hbw : b ≠ w) :
    r.graph.edgesWithin {p.centre,b,w} ≤ r.graph.degree p.centre :=
  r.asCMS.protected_triangle hw hbw

end OverfullWork.NormalizedCanonicalCandidate

module

public import OverfullWork.CMSCaseTwoInitialCopies
public import OverfullWork.CMSCaseTwoPartnerWeights
public import OverfullWork.MiddleCopyGraph

@[expose] public section


/-! Construct the actual internal-plus-middle graph of CMS Theorem
4.2, Case 2, Step 2. -/
namespace OverfullWork.CMSBalancedCut

open Finset SimpleGraph RegularHeavyCutRepair
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {M : MultiGraph V} {a b w : V} {d m L r t : ℕ} {η : ℝ}

structure CaseTwoMiddleCopies (s : CaseTwoPartition M a b d m L r t η)
    (w : V) where
  initial : InitialMiddleCopies.Selection M s.part ((heavySet M a b L).erase w) a b w
  balancing : BalancedMiddleAllocation.Selection s.crossWeight initial.count s.partnerWeight s.heavyVertices
    (M.degreeInto s.part a) (M.degreeInto s.partᶜ a)
    (M.mult s(b,w)-M.degreeInto s.part a)

theorem CaseTwoPartition.middle_copies_of_initial (s : CaseTwoPartition M a b d m L r t η)
    (w : V) (s0 : InitialMiddleCopies.Selection M s.part ((heavySet M a b L).erase w) a b w)
    (hReg : M.IsRegularOfDegree d) (hSmall : 2*M.mult s(b,w) ≤ d) :
    Nonempty (CaseTwoMiddleCopies s w) := by
  have hf : ∀ v, s0.count v ≤ s.crossWeight v := by
    intro v
    by_cases hv : v ∈ s.partᶜ
    · simpa only [CaseTwoPartition.crossWeight,if_pos hv] using s0.capacity v
    · have hz := s0.supported v (by simp [InitialMiddleCopies.allowed,hv])
      simp only [CaseTwoPartition.crossWeight,if_neg hv,hz,le_refl]
  have hsplit := M.degreeInto_add_compl s.part a
  have hreg : M.degree a = d := hReg a
  rw [hreg] at hsplit
  have hhalf := s.centre_internal_le_half
  have hFI : M.mult s(b,w)-M.degreeInto s.part a ≤
      M.degreeInto s.partᶜ a-M.degreeInto s.part a := by omega
  obtain ⟨s1⟩ := BalancedMiddleAllocation.exists_selection s.crossWeight s0.count s.partnerWeight
    s.heavyVertices _ _ _ hf s.cross_total s0.total s.partner_budget (s.cross_ge_internal hReg) hFI
    (fun v _ => s.partnerWeight_le v) s.paired_difference_budget
  exact ⟨⟨s0,s1⟩⟩

/-- Select the actual initial and balancing middle copies of the paper,
using the no-overfull condition for the exceptional triangle. -/
theorem CaseTwoPartition.exists_middle_copies (s : CaseTwoPartition M a b d m L r t η)
    (Λ E : ℕ) (hCut : L ≤ Λ) (hReg : M.IsRegularOfDegree d) (hNo : ¬ M.HasOverfullSubset d)
    (hProfile : d ≤ M.supportGraph.degree b+M.mult s(a,b)+E) (hSmall : 2*(E+2) ≤ d) :
    ∃ w : V, w ∉ s.part ∧
      (if (exceptionCandidates M a b Λ).card = 1 then
        w ∈ exceptionCandidates M a b Λ else w = b) ∧
      M.mult s(b,w) ≤ E+2 ∧ Nonempty (CaseTwoMiddleCopies s w) := by
  obtain ⟨w,hw,hEx,hq,⟨s0⟩⟩ := s.exists_initial_middle_copies Λ E hCut hReg hNo hProfile
  exact ⟨w,hw,hEx,hq,s.middle_copies_of_initial w s0 hReg
    ((Nat.mul_le_mul_left 2 hq).trans hSmall)⟩

variable {s : CaseTwoPartition M a b d m L r t η}

def CaseTwoMiddleCopies.count (r : CaseTwoMiddleCopies s w)
    (v : V) : ℕ := r.initial.count v+r.balancing.extra v

theorem CaseTwoMiddleCopies.count_le (r : CaseTwoMiddleCopies s w)
    (v : V) : r.count v ≤ s.crossWeight v := r.balancing.copies_le v

theorem CaseTwoMiddleCopies.inside_zero (r : CaseTwoMiddleCopies s w)
    (v : V) (hv : v ∈ s.part) : r.count v = 0 := by
  have hh := r.count_le v
  simp only [CaseTwoPartition.crossWeight,mem_compl,if_neg (not_not.mpr hv)] at hh
  omega

noncomputable def CaseTwoMiddleCopies.graph (r : CaseTwoMiddleCopies s w) :
    MultiGraph (V) :=
  MiddleCopyGraph.graph M s.part a r.count (r.inside_zero _ s.centre_mem)

theorem CaseTwoMiddleCopies.graph_le (r : CaseTwoMiddleCopies s w) :
    ∀ e, r.graph.mult e ≤ M.mult e := by
  apply MiddleCopyGraph.le_original _ _ _ s.centre_mem
  · intro v
    have hh := r.count_le v
    dsimp only [CaseTwoPartition.crossWeight] at hh
    split_ifs at hh <;> omega
  · exact r.inside_zero

theorem CaseTwoMiddleCopies.centre_degree (r : CaseTwoMiddleCopies s w) :
    r.graph.degree a = M.degreeInto s.part a+
      (M.mult s(b,w)-M.degreeInto s.part a)+
      (M.degreeInto s.partᶜ a-M.degreeInto s.part a-
        (M.mult s(b,w)-M.degreeInto s.part a))/2 := by
  rw [CaseTwoMiddleCopies.graph,MiddleCopyGraph.centre_degree _ _ _ _ _ s.centre_mem]
  simp only [CaseTwoMiddleCopies.count,sum_add_distrib,r.initial.total,r.balancing.total]
  omega

theorem CaseTwoMiddleCopies.centre_bounds (r : CaseTwoMiddleCopies s w)
    (hReg : M.IsRegularOfDegree d) :
    d-1 ≤ 2*r.graph.degree a ∧
      2*r.graph.degree a ≤ d+
        (M.mult s(b,w)-M.degreeInto s.part a) := by
  have hl := r.balancing.centre_lower
  have hu := r.balancing.centre_upper
  have hsplit := M.degreeInto_add_compl s.part a
  have hreg : M.degree a = d := hReg a
  rw [hreg] at hsplit
  rw [r.centre_degree]
  omega

theorem CaseTwoMiddleCopies.bundle_upper (r : CaseTwoMiddleCopies s w)
    (v : V) :
    2*r.count v ≤ s.crossWeight v+
      (M.mult s(b,w)-M.degreeInto s.part a)+1 := r.balancing.bundle_upper v

theorem CaseTwoMiddleCopies.paired_lower (r : CaseTwoMiddleCopies s w)
    (v : V) (hv : v ∈ s.heavyVertices) :
    s.crossWeight v ≤ 2*r.count v+s.partnerWeight v+2*r.balancing.deficit v :=
  r.balancing.paired_lower v hv

theorem CaseTwoMiddleCopies.deficit_budget (r : CaseTwoMiddleCopies s w) :
    (∑ v, r.balancing.deficit v) ≤
      (M.mult s(b,w)-M.degreeInto s.part a)+s.heavyVertices.card+1 :=
  r.balancing.deficit_sum

theorem CaseTwoMiddleCopies.protected_triangle (r : CaseTwoMiddleCopies s w)
    (hw : w ∉ s.part) (hbw : b ≠ w) :
    r.graph.edgesWithin {a,b,w} ≤ r.graph.degree a := by
  have hzero : r.balancing.extra a = 0 := by
    have hh := r.inside_zero a s.centre_mem
    change r.initial.count a+r.balancing.extra a = 0 at hh
    omega
  exact MiddleCopyGraph.protected_triangle M s.part ((heavySet M a b L).erase w)
    a b w r.initial s.centre_mem s.second_not_mem hw hbw r.balancing.extra hzero

end OverfullWork.CMSBalancedCut

module

public import OverfullWork.CMSGeneralCaseTwoPartition
public import OverfullWork.InitialMiddleCopies
public import OverfullWork.CentredDegreeDiscrepancy

@[expose] public section


/-! Select the exceptional triangle, if any, and the initial middle
copies from CMS Theorem 4.2, Case 2, Step 2. -/
namespace OverfullWork.CMSBalancedCut

open Finset SimpleGraph RegularHeavyCutRepair
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {M : MultiGraph V} {a b : V} {d m L r t : ℕ} {η : ℝ}

/-- The vertices eligible for the unique-exception test of Step 2. -/
noncomputable def exceptionCandidates (M : MultiGraph V) (a b : V) (Λ : ℕ) : Finset V :=
  univ.filter fun w => w ≠ a ∧ w ≠ b ∧ Λ < M.mult s(a,w) ∧ 0 < M.mult s(b,w)

/-- Off-centre row excess follows from the support degree profile,
with one unit for the centre edge in the support. -/
theorem off_centre_excess_le_of_support_degree (M : MultiGraph V) (a v : V) (d E : ℕ)
    (hreg : M.IsRegularOfDegree d) (hProfile : d ≤ M.supportGraph.degree v+M.mult s(a,v)+E) :
    (∑ w ∈ univ.erase a, (M.mult s(v,w)-1)) ≤ E+1 := by
  have hSum := M.degreeInto_eq_support_add_excess univ v
  rw [M.sum_supportRow_eq_neighboursIn] at hSum
  have hSupport : OverfullWork.PrunedCore.neighboursIn M.supportGraph univ v =
      M.supportGraph.degree v := by
    simp [OverfullWork.PrunedCore.neighboursIn,card_neighborFinset_eq_degree]
  rw [hSupport] at hSum
  rw [show M.degreeInto univ v = d by
    rw [MultiGraph.degreeInto,←M.degree_eq_sum_mult v,hreg v]] at hSum
  have hSumNat : d = M.supportGraph.degree v + ∑ w, (M.mult s(v,w)-1) := by
    push_cast at hSum ⊢
    exact_mod_cast hSum
  have hErase := sum_erase_add univ (fun w => M.mult s(v,w)-1) (mem_univ a)
  rw [show M.mult s(v,a) = M.mult s(a,v) from congrArg M.mult Sym2.eq_swap] at hErase
  omega

/-- The exceptional vertex is the unique eligible vertex when one
exists. Otherwise the second anchor serves as a repeated index and
the selected initial family is empty. -/
theorem CaseTwoPartition.exists_initial_middle_copies (s : CaseTwoPartition M a b d m L r t η)
    (Λ E : ℕ) (hCut : L ≤ Λ) (hReg : M.IsRegularOfDegree d) (hNo : ¬M.HasOverfullSubset d)
    (hProfile : d ≤ M.supportGraph.degree b+M.mult s(a,b)+E) :
    ∃ w : V, w ∉ s.part ∧
      (if (exceptionCandidates M a b Λ).card = 1 then
          w ∈ exceptionCandidates M a b Λ else w = b) ∧ M.mult s(b,w) ≤ E+2 ∧
      Nonempty (InitialMiddleCopies.Selection M s.part ((heavySet M a b L).erase w) a b w) := by
  classical
  by_cases hUnique : (exceptionCandidates M a b Λ).card = 1
  · obtain ⟨w,hwSet⟩ := card_eq_one.mp hUnique
    have hw : w ∈ exceptionCandidates M a b Λ := by rw [hwSet]; exact mem_singleton_self _
    obtain ⟨hwa,hwb,hwaHeavy,_hwbAdj⟩ := (mem_filter.mp hw).2
    have hwA := s.heavy_across w hwb (hCut.trans_lt hwaHeavy)
    have hExcess := off_centre_excess_le_of_support_degree M a b d E hReg hProfile
    have hOne : M.mult s(b,w)-1 ≤ ∑ z ∈ univ.erase a, (M.mult s(b,z)-1) :=
      single_le_sum (f := fun z => M.mult s(b,z)-1) (fun _ _ => Nat.zero_le _)
        (mem_erase.mpr ⟨hwa,mem_univ w⟩)
    have hPriority : (heavySet M a b L).erase w ⊆ InitialMiddleCopies.allowed s.part b w := by
      intro v hv
      obtain ⟨hvw,hvZ⟩ := mem_erase.mp hv
      obtain ⟨hvb,hvHeavy⟩ := (heavySet_mem M a b v L).mp hvZ
      simp [InitialMiddleCopies.allowed,hvw,hvb,s.heavy_across v hvb hvHeavy]
    exact ⟨w,hwA,by simp [hUnique,hw],by omega,
      InitialMiddleCopies.exists_selection M s.part _ a b w d hReg hNo
        s.centre_mem s.second_not_mem hwA hwb.symm hPriority⟩
  · have hLoop := M.loopless s(b,b) (by simp)
    refine ⟨b,s.second_not_mem,by simp [hUnique],by omega,⟨{
      count := fun _ => 0
      capacity := fun _ => Nat.zero_le _
      supported := fun _ _ => rfl
      total := by simp [hLoop]
      priority := by simp [hLoop]
    }⟩⟩

end OverfullWork.CMSBalancedCut

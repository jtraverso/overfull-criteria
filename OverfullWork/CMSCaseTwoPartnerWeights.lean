module

public import OverfullWork.CMSGeneralCaseTwoPartition
public import OverfullWork.BalancedMiddleAllocation

@[expose] public section


/-! The copy budgets for the partner bijection in CMS (5.5), on an
arbitrary regular multigraph with an adjusted Case 2 cut. -/
namespace OverfullWork.CMSBalancedCut

open Finset SimpleGraph RegularHeavyCutRepair
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {M : MultiGraph V} {a b : V} {d m L r t : ℕ} {η : ℝ}

noncomputable def CaseTwoPartition.heavyVertices (s : CaseTwoPartition M a b d m L r t η) :
    Finset (V) := insert b (heavySet M a b L)

noncomputable def CaseTwoPartition.partnerWeight (s : CaseTwoPartition M a b d m L r t η)
    (v : V) : ℕ :=
  if hv : v ∈ heavySet M a b L then
    M.mult s(a,(s.partnerEquiv ⟨v,hv⟩).val) else 0

noncomputable def CaseTwoPartition.crossWeight (s : CaseTwoPartition M a b d m L r t η)
    (v : V) : ℕ :=
  if v ∈ s.partᶜ then M.mult s(a,v) else 0

theorem CaseTwoPartition.heavy_subset_compl (s : CaseTwoPartition M a b d m L r t η) :
    s.heavyVertices ⊆ s.partᶜ := by
  intro v hv
  rcases mem_insert.mp hv with rfl | hz
  · exact mem_compl.mpr s.second_not_mem
  · have hh := (heavySet_mem M a b v L).mp hz
    exact mem_compl.mpr (s.heavy_across v hh.1 hh.2)

theorem CaseTwoPartition.partnerWeight_outside (s : CaseTwoPartition M a b d m L r t η)
    (v : V) (hv : v ∉ s.heavyVertices) : s.partnerWeight v = 0 := by
  apply dif_neg
  exact fun hz => hv (mem_insert_of_mem hz)

theorem CaseTwoPartition.partnerWeight_le (s : CaseTwoPartition M a b d m L r t η)
    (v : V) : s.partnerWeight v ≤ s.crossWeight v := by
  by_cases hv : v ∈ heavySet M a b L
  · have hh := (heavySet_mem M a b v L).mp hv
    have hLight := s.partners_light _ (s.partnerEquiv ⟨v,hv⟩).property
    have hSide := s.heavy_across v hh.1 hh.2
    simp only [CaseTwoPartition.partnerWeight,dif_pos hv,
      CaseTwoPartition.crossWeight,mem_compl,if_pos hSide]
    omega
  · simp only [CaseTwoPartition.partnerWeight,dif_neg hv,Nat.zero_le]

theorem CaseTwoPartition.sum_partnerWeight (s : CaseTwoPartition M a b d m L r t η) :
    (∑ v, s.partnerWeight v) = M.degreeInto s.partners a := by
  let Z := heavySet M a b L
  have hs : (∑ v, s.partnerWeight v) =
      ∑ v : Z, M.mult s(a,(s.partnerEquiv v).val) := by
    have hh := sum_attach_eq_sum_dite Z (fun v => M.mult s(a,(s.partnerEquiv v).val))
    rw [←univ_eq_attach] at hh
    exact hh.symm
  calc
    _ = ∑ v : Z, M.mult s(a,(s.partnerEquiv v).val) := hs
    _ = ∑ v : s.partners, M.mult s(a,v.val) :=
      s.partnerEquiv.sum_comp (fun v => M.mult s(a,v.val))
    _ = _ := sum_coe_sort s.partners (fun v => M.mult s(a,v))

theorem CaseTwoPartition.partner_budget (s : CaseTwoPartition M a b d m L r t η) :
    (∑ v, s.partnerWeight v) ≤ M.degreeInto s.part a := by
  rw [s.sum_partnerWeight]
  exact sum_le_sum_of_subset_of_nonneg s.partners_subset (fun _ _ _ => Nat.zero_le _)

theorem CaseTwoPartition.cross_total (s : CaseTwoPartition M a b d m L r t η) :
    (∑ v, s.crossWeight v) = M.degreeInto s.partᶜ a := by
  have hh := sum_filter (s := (univ : Finset (V)))
    (p := fun v => v ∈ s.partᶜ) (f := fun v => M.mult s(a,v))
  simpa only [filter_mem_eq_inter,univ_inter,CaseTwoPartition.crossWeight,
    MultiGraph.degreeInto] using hh.symm

theorem CaseTwoPartition.cross_ge_internal (s : CaseTwoPartition M a b d m L r t η)
    (hReg : M.IsRegularOfDegree d) :
    M.degreeInto s.part a ≤ M.degreeInto s.partᶜ a := by
  have hs := M.degreeInto_add_compl s.part a
  have hreg : M.degree a = d := hReg a
  rw [hreg] at hs
  have hh := s.centre_internal_le_half
  omega

theorem CaseTwoPartition.paired_difference_budget (s : CaseTwoPartition M a b d m L r t η) :
    (∑ v ∈ s.heavyVertices, (s.crossWeight v-s.partnerWeight v)) ≤
      M.degreeInto s.partᶜ a-M.degreeInto s.part a := by
  have hpH : (∑ v ∈ s.heavyVertices, s.partnerWeight v) = ∑ v, s.partnerWeight v := by
    apply sum_subset (subset_univ _)
    intro v _ hv
    exact s.partnerWeight_outside v hv
  have hDiff : (∑ v ∈ s.heavyVertices, (s.crossWeight v-s.partnerWeight v))+
      (∑ v, s.partnerWeight v) = M.degreeInto s.heavyVertices a := by
    rw [←hpH,←sum_add_distrib]
    apply sum_congr rfl
    intro v hv
    rw [Nat.sub_add_cancel (s.partnerWeight_le v)]
    exact if_pos (s.heavy_subset_compl hv)
  have hX : insert a s.partners ⊆ s.part := insert_subset s.centre_mem s.partners_subset
  have hInside := sum_sdiff (f := fun v => M.mult s(a,v)) hX
  rw [sum_insert s.centre_not_partner,M.loopless s(a,a) (by simp),
    zero_add] at hInside
  have hOutside := sum_sdiff (f := fun v => M.mult s(a,v)) s.heavy_subset_compl
  have hFree := s.free_weight_le
  have hPair := s.sum_partnerWeight
  change M.degreeInto (s.part\insert a s.partners) a+
    M.degreeInto s.partners a = M.degreeInto s.part a at hInside
  change M.degreeInto (s.partᶜ\s.heavyVertices) a+
    M.degreeInto s.heavyVertices a = M.degreeInto s.partᶜ a at hOutside
  change M.degreeInto (s.part\insert a s.partners) a ≤
    M.degreeInto (s.partᶜ\s.heavyVertices) a at hFree
  omega

end OverfullWork.CMSBalancedCut

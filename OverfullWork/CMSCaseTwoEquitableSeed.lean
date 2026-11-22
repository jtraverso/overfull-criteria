module

public import OverfullWork.CMSCaseTwoMiddleDegreeProfile
public import OverfullWork.OffCentreVizing
public import OverfullWork.EquitableMissingCounts

@[expose] public section


/-! The equalized colouring and missing-colour bounds of Step 2 of
CMS Theorem 4.2, Case 2, at explicit integer scales. -/
namespace OverfullWork.CMSBalancedCut

open Finset SimpleGraph RegularHeavyCutRepair
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {M : MultiGraph V} {a b : V} {d m r t : ℕ} {η : ℝ}

set_option maxHeartbeats 1400000 in
theorem CaseTwoPartition.exists_equitable_seed
    (T : ℕ) (s : CaseTwoPartition M a b d m (m/T) r t η)
    (Λ E : ℕ) (α : ℝ) (hα : 0 < α) (hDense : α*(Fintype.card V:ℝ) ≤ (d:ℝ))
    (hReg : M.IsRegularOfDegree d) (hNo : ¬ M.HasOverfullSubset d) (hD : d ≤ 3*m)
    (hT : 1 ≤ T) (hCut : m/T ≤ Λ) (hSmall : 2*(E+2) ≤ d)
    (hProfile : ∀ v, v ≠ a → d ≤ M.supportGraph.degree v+M.mult s(a,v)+E) :
    let U := η*(m:ℝ)+3*(E:ℝ)+(m/T:ℕ)+6*(T:ℝ)+10
    let k := ⌈((d:ℝ)+U)/2⌉₊+(E+2)
    let ξ := U+(E:ℝ)+3
    ∃ w : V, w ∉ s.part ∧
      (if (exceptionCandidates M a b Λ).card = 1 then
        w ∈ exceptionCandidates M a b Λ else w = b) ∧ M.mult s(b,w) ≤ E+2 ∧
      ∃ copies : CaseTwoMiddleCopies s w, ∃ C : copies.graph.EdgeColoring k,
        C.IsEquitable ∧ d ≤ 2*k ∧
        (∀ v, ((C.missingPalette v).card:ℝ) < ξ) ∧
        (∑ v, ((C.missingPalette v).card:ℝ)) ≤ (Fintype.card V:ℝ)*ξ ∧
        ∀ i : Fin k, ((C.missingSet univ i).card:ℝ) ≤ (2/α)*ξ+2 := by
  let U := η*(m:ℝ)+3*(E:ℝ)+(m/T:ℕ)+6*(T:ℝ)+10
  let D := ⌈((d:ℝ)+U)/2⌉₊
  let k := D+(E+2)
  let ξ := U+(E:ℝ)+3
  have hba : b ≠ a := fun he => s.second_not_mem (he.symm ▸ s.centre_mem)
  have hOff (v : V) (hv : v ≠ a) :
      (∑ z ∈ univ.erase a, (M.mult s(v,z)-1)) ≤ E+1 :=
    off_centre_excess_le_of_support_degree M a v d E hReg (hProfile v hv)
  obtain ⟨w,hw,hEx,hq,⟨copies⟩⟩ :=
    s.exists_middle_copies Λ E hCut hReg hNo (hProfile b hba) hSmall
  have hη : 0 ≤ η*(m:ℝ) :=
    (abs_nonneg _).trans (s.simple_discrepancy a).le
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hξ : 0 ≤ ξ := by dsimp only [ξ]; positivity
  have hBound (v : V) : |2*(copies.graph.degree v:ℝ)-(d:ℝ)| ≤ U := by
    have hh := copies.degree_profile hReg hOff v
    have hF : ((M.mult s(b,w)-M.degreeInto s.part a:ℕ):ℝ) ≤ ((E+2:ℕ):ℝ) := by
      exact_mod_cast (Nat.sub_le _ _).trans hq
    have hCount := heavySet_card_at_scale M a b d m T hReg hD hT
    have hHeavy : s.heavyVertices.card ≤ 3*T+1 :=
      (card_insert_le _ _).trans (Nat.add_le_add_right hCount 1)
    have hHeavyR : (s.heavyVertices.card:ℝ) ≤ 3*(T:ℝ)+1 := by exact_mod_cast hHeavy
    push_cast at hh hF
    dsimp only [U]
    linarith only [hh,hF,hHeavyR]
  have hCeil : ((d:ℝ)+U)/2 ≤ (D:ℝ) := Nat.le_ceil _
  have hDcap (v : V) : copies.graph.degree v ≤ D := by
    apply (Nat.cast_le (α := ℝ)).mp
    linarith only [(abs_le.mp (hBound v)).2,hCeil]
  have hOffMult (u v : V) (hu : u ≠ a) (hv : v ≠ a) : copies.graph.mult s(u,v) ≤ E+2 := by
    have hOne : M.mult s(u,v)-1 ≤ ∑ z ∈ univ.erase a, (M.mult s(u,z)-1) :=
      single_le_sum (f := fun z => M.mult s(u,z)-1) (fun _ _ => Nat.zero_le _)
        (mem_erase.mpr ⟨hv,mem_univ v⟩)
    have hLe := hOne.trans (hOff u hu)
    exact (copies.graph_le _).trans (by omega)
  obtain ⟨C₀⟩ := copies.graph.exists_edgeColoring_off_centre_bound a D (E+2) hDcap hOffMult
  obtain ⟨C,hEquitable⟩ := C₀.exists_equitable
  have hk : (k:ℝ) = (D:ℝ)+(E:ℝ)+2 := by dsimp only [k]; push_cast; ring
  have hHalf : d ≤ 2*k := by
    apply (Nat.cast_le (α := ℝ)).mp
    push_cast
    linarith only [hk,hU,hCeil,Nat.cast_nonneg (α := ℝ) E]
  have hMissing (v : V) : ((C.missingPalette v).card:ℝ) < ξ := by
    have hm : ((C.missingPalette v).card:ℝ)+(copies.graph.degree v:ℝ) = (k:ℝ) := by
      exact_mod_cast C.missingPalette_card_add_degree v
    have hUpper : (D:ℝ) < ((d:ℝ)+U)/2+1 :=
      Nat.ceil_lt_add_one (show 0 ≤ ((d:ℝ)+U)/2 by positivity)
    dsimp only [ξ]
    linarith only [hm,hk,hUpper,(abs_le.mp (hBound v)).1]
  have hTotal : (∑ v, ((C.missingPalette v).card:ℝ)) ≤ (Fintype.card V:ℝ)*ξ := by
    simpa only [sum_const,card_univ,nsmul_eq_mul] using
      sum_le_sum (s := (univ : Finset V)) (fun v _ => (hMissing v).le)
  have hRatio : (Fintype.card V:ℝ) ≤ (2/α)*(k:ℝ) := by
    have hh : (d:ℝ) ≤ 2*(k:ℝ) := by exact_mod_cast hHalf
    calc
      _ ≤ 2*(k:ℝ)/α := (le_div_iff₀ hα).mpr (by linarith only [hDense,hh])
      _ = _ := by ring
  exact ⟨w,hw,hEx,hq,copies,C,hEquitable,hHalf,hMissing,hTotal,
    fun i => C.equitable_missing_real_bound hEquitable (2/α) ξ
      (Nat.zero_lt_of_lt i.isLt) (by positivity) hRatio hTotal i⟩

end OverfullWork.CMSBalancedCut

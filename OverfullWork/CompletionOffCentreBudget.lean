module

public import OverfullWork.CanonicalCandidateNoOverfull

@[expose] public section


/-! # The actual completion has a sparse addition away from its centre

The certificate budget pays for twice the total number of added edges
away from the centre. This is obtained by degree accounting, not assumed
as a parallel-edge bound.
-/
namespace OverfullWork.CompletionOffCentreBudget
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 6000000

theorem outside_internal_le (D A : MultiGraph V) (Δ B : ℕ) (z : V)
    (hreg : (D.addCopies A).IsRegularOfDegree Δ)
    (hBudget : (∑v∈univ.erase z,(Δ-D.degree v))+D.degree z≤Δ+B) :
    A.twiceInternal (univ.erase z)≤B := by
  have hAdded:∀v,A.degree v=Δ-D.degree v:=by
    intro v
    have hh:=hreg v
    rw [MultiGraph.degree_addCopies] at hh
    omega
  have hSet:(univ.erase z:Finset V)=({z}:Finset V)ᶜ:=by ext v;simp
  have hCut:A.cutSize (univ.erase z)=A.degree z:=by
    rw [hSet,MultiGraph.cutSize_compl,CanonicalAdmissibility.cut_singleton]
  have hId:=A.sum_degree_eq_internal_add_cut (univ.erase z)
  rw [hCut] at hId
  simp_rw [hAdded] at hId
  have hz:=hreg z
  rw [MultiGraph.degree_addCopies] at hz
  have hAz:=hAdded z
  omega

theorem outside_row_le (A : MultiGraph V) (B : ℕ) (z v : V) (hv : v≠z)
    (hBudget : A.twiceInternal (univ.erase z)≤B) :
    A.degreeInto (univ.erase z) v≤B := by
  have hRow:A.degreeInto (univ.erase z) v≤A.twiceInternal (univ.erase z):=
    single_le_sum (f:=fun w=>∑u∈univ.erase z,A.mult s(w,u))
      (fun _ _=>Nat.zero_le _) (mem_erase.mpr ⟨hv,mem_univ v⟩)
  exact hRow.trans hBudget

/-- All multiplicity loss outside the centre is paid by the actual
added row. This gives the neighbour bound required by CMS (1c). -/
theorem degree_le_support_bundle_add (D A : MultiGraph V) (z v : V) (hv : v≠z)
    (hStar : D.IsStarAt z) (B : ℕ)
    (hRow : A.degreeInto (univ.erase z) v≤B) :
    (D.addCopies A).degree v≤(D.addCopies A).supportGraph.degree v+
      (D.addCopies A).mult s(z,v)+B := by
  let M:=D.addCopies A
  let T:=univ.erase z
  change M.degree v≤M.supportGraph.degree v+M.mult s(z,v)+B
  have hPoint:∀w∈T,D.mult s(v,w) ≤ (if M.supportGraph.Adj v w then 1 else 0):=by
    intro w hw
    have hSimple:=hStar v w hv (mem_erase.mp hw).1
    by_cases hEdge:M.supportGraph.Adj v w
    · simp only [if_pos hEdge];exact hSimple
    · rw [if_neg hEdge]
      change ¬0<D.mult s(v,w)+A.mult s(v,w) at hEdge
      omega
  have hBaseRow:(∑w∈T,D.mult s(v,w))≤M.supportGraph.degree v:=by
    calc
      _ ≤ ∑w∈T,(if M.supportGraph.Adj v w then 1 else 0) :=sum_le_sum hPoint
      _ ≤ ∑w:V,(if M.supportGraph.Adj v w then 1 else 0) :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _=>Nat.zero_le _)
      _ = M.supportGraph.degree v :=by
        rw [←MultiGraph.degree_ofSimpleGraph,MultiGraph.degree_eq_sum_mult]
        rfl
  have hSplit:=sum_erase_add univ (fun w=>M.mult s(v,w)) (mem_univ z)
  rw [←M.degree_eq_sum_mult] at hSplit
  have hRows:(∑w∈T,M.mult s(v,w))=(∑w∈T,D.mult s(v,w))+A.degreeInto T v:=by
    change (∑w∈T,(D.mult s(v,w)+A.mult s(v,w)))=_
    rw [sum_add_distrib]
    rfl
  change A.degreeInto T v≤B at hRow
  change (∑w∈T,M.mult s(v,w))+M.mult s(v,z)=M.degree v at hSplit
  have hSwap:M.mult s(v,z)=M.mult s(z,v):=congrArg M.mult Sym2.eq_swap
  omega

end OverfullWork.CompletionOffCentreBudget

namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}

theorem Candidate.added_off_centre_internal_le (p : Candidate c) :
    (p.completion.L.addCopies p.completion.N).twiceInternal (univ.erase p.centre)≤B := by
  apply CompletionOffCentreBudget.outside_internal_le p.orderedBase _ G.maxDegree B p.centre
  · intro v
    have hh:=p.completion.regular v
    rw [MultiGraph.degree_addCopies,MultiGraph.degree_addCopies] at hh
    change p.orderedBase.degree v+p.completion.L.degree v+p.completion.N.degree v=G.maxDegree at hh
    simp only [MultiGraph.degree_addCopies]
    omega
  · exact p.ordinary_deficit_budget

theorem Candidate.completed_neighbour_profile (p : Candidate c)
    (v : Fin (p.pairIndex+1)×Bool) (hv : v≠p.centre) :
    G.maxDegree≤p.completed.supportGraph.degree v+p.completed.mult s(p.centre,v)+B := by
  have hRow:=CompletionOffCentreBudget.outside_row_le _ B p.centre v hv p.added_off_centre_internal_le
  have hh:=CompletionOffCentreBudget.degree_le_support_bundle_add p.orderedBase
    (p.completion.L.addCopies p.completion.N) p.centre v hv p.ordered_star B hRow
  have hGraph:p.orderedBase.addCopies (p.completion.L.addCopies p.completion.N)=p.completed:=by
    apply MultiGraph.ext_mult
    intro e
    exact (Nat.add_assoc _ _ _).symm
  have hreg:p.completed.degree v=G.maxDegree:=p.completion.regular v
  rw [hGraph,hreg] at hh
  exact hh

end OverfullWork.NormalizedCanonicalCandidate

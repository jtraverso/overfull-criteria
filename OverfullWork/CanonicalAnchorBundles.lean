module

public import OverfullWork.OrdinaryEndpointSupport
public import OverfullWork.CompletionOffCentreBudget

@[expose] public section


/-! # Compare the first ordinary anchor bundle with every other bundle

This is the degree-accounting comparison used in CMS Step 4, Lemma 4.1.
The error is the original added ordinary-row budget plus B+Y losses;
no new maximum-bundle choice of the second anchor is assumed.
-/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem centre_bundle_add_ordinary_row (M : MultiGraph V) (a v : V) :
    M.mult s(a,v)+M.degreeInto (univ.erase a) v=M.degree v := by
  have hh := sum_erase_add univ (fun u => M.mult s(v,u)) (mem_univ a)
  rw [←M.degree_eq_sum_mult] at hh
  change M.degreeInto (univ.erase a) v+M.mult s(v,a)=M.degree v at hh
  rw [Sym2.eq_swap] at hh
  omega

theorem centre_bundle_comparison (M D : MultiGraph V) (a b v : V) (Δ B Y : ℕ)
    (hM : M.IsRegularOfDegree Δ) (hBase : ∀ e, D.mult e ≤ M.mult e)
    (hOrder : D.degree b ≤ D.degree v) (hSmall : D.mult s(a,v) ≤ Y)
    (hRow : M.degreeInto (univ.erase a) b ≤ D.degree b+B) :
    M.mult s(a,v) ≤ M.mult s(a,b)+B+Y := by
  have hDb := D.centre_bundle_add_ordinary_row a v
  have hMb := M.centre_bundle_add_ordinary_row a b
  have hMv := M.centre_bundle_add_ordinary_row a v
  have hMono : D.degreeInto (univ.erase a) v ≤ M.degreeInto (univ.erase a) v :=
    sum_le_sum (fun u _ => hBase s(v,u))
  rw [hM b] at hMb
  rw [hM v] at hMv
  omega

end SimpleGraph.MultiGraph

namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
set_option maxHeartbeats 24000000

theorem Candidate.first_ordinary_bundle_dominates (p : Candidate c) (hCentre : p.centre=(0,false))
    (v : Fin (p.pairIndex+1) × Bool) (hv : v ≠ p.centre) :
    p.completed.mult s(p.centre,v) ≤ p.completed.mult s(p.centre,(0,true))+B+c.setᶜ.card := by
  let b : Fin (p.pairIndex+1) × Bool := (0,true)
  have hb : b ≠ p.centre := by simp [b,hCentre]
  have hOrder : p.orderedBase.degree b ≤ p.orderedBase.degree v := by
    by_cases hvb : v=b
    · rw [hvb]
    apply p.ordered_rank_mono
    have hRank := p.rank_ge_two_of_not_anchors v (by simpa only [hCentre] using hv) hvb
    have hbRank : p.rank b=1 := by
      simp [b,Candidate.rank,OrderedCanonicalTransport.pairedIndex,Nat.mod_eq_of_lt (show 1 < 2*(p.pairIndex+1) by omega)]
    omega
  have hBase : ∀ e, p.orderedBase.mult e ≤ p.completed.mult e := by
    intro e
    change p.orderedBase.mult e ≤ p.orderedBase.mult e+p.completion.L.mult e+p.completion.N.mult e
    omega
  have hAdded := CompletionOffCentreBudget.outside_row_le _ B p.centre b hb p.added_off_centre_internal_le
  have hRow : p.completed.degreeInto (univ.erase p.centre) b ≤ p.orderedBase.degree b+B := by
    have hSplit : p.completed.degreeInto (univ.erase p.centre) b=
        p.orderedBase.degreeInto (univ.erase p.centre) b+
        (p.completion.L.addCopies p.completion.N).degreeInto (univ.erase p.centre) b := by
      unfold MultiGraph.degreeInto
      change (∑ u ∈ univ.erase p.centre, (p.orderedBase.mult s(b,u)+p.completion.L.mult s(b,u)+p.completion.N.mult s(b,u)))=_
      rw [sum_add_distrib,sum_add_distrib]
      change _=(∑ u ∈ univ.erase p.centre, p.orderedBase.mult s(b,u))+
        (∑ u ∈ univ.erase p.centre, (p.completion.L.mult s(b,u)+p.completion.N.mult s(b,u)))
      rw [sum_add_distrib]
      omega
    have hOrd := p.orderedBase.centre_bundle_add_ordinary_row p.centre b
    omega
  exact MultiGraph.centre_bundle_comparison p.completed p.orderedBase p.centre b v G.maxDegree B
    c.setᶜ.card p.completion.regular hBase hOrder (p.centre_multiplicity v) hRow

end OverfullWork.NormalizedCanonicalCandidate

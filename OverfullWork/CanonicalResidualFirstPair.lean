module

public import OverfullWork.TriangleBundleCuts

@[expose] public section


/-! # An actual unsafe centre must belong to the first ordered pair

The minimum-centre condition and the certificate's ordinary deficit
budget rule out two preceding ordinary vertices. No tie-breaking of the
original sorting permutation is assumed.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ}
variable {c : Certificate G B K}
set_option maxHeartbeats 6000000

theorem Candidate.ordered_pair_mono (p : Candidate c)
    (v w : Fin (p.pairIndex+1)×Bool) (hvw : v.1.val<w.1.val) :
    p.orderedBase.degree v≤p.orderedBase.degree w := by
  simp only [Candidate.orderedBase,OrderedCanonicalTransport.degree_reindex]
  obtain ⟨i,b⟩:=v
  obtain ⟨j,d⟩:=w
  have hh:=p.ordered_next i j hvw
  have hi:=p.ordered_pair i
  have hj:=p.ordered_pair j
  cases b <;> cases d <;> dsimp only at * <;> omega

theorem Candidate.centre_first_pair_of_unsafe_independent_triple (p : Candidate c)
    (hMin : ∀x∈c.set,(∑y∈c.setᶜ,G.degree y)≤G.degree x)
    (hScale : 3*B≤2*G.maxDegree)
    (S : Finset (Fin (p.pairIndex+1)×Bool)) (hS : S.card=3)
    (hBase : p.orderedBase.twiceInternal S=0)
    (hCut : p.completed.cutSize S<G.maxDegree) : p.centre.1.val=0 := by
  let d:=p.orderedBase.degree p.centre
  have hMinimum:=p.centre_min_of_source_min hMin
  have hLow:3*d<G.maxDegree:=by
    have hSum:3*d≤∑v∈S,p.orderedBase.degree v:=by
      calc
        _ = ∑_v∈S,d :=by simp [hS]
        _ ≤ _ :=sum_le_sum (fun v _=>hMinimum v)
    have hId:=p.orderedBase.sum_degree_eq_internal_add_cut S
    rw [hBase,Nat.zero_add] at hId
    have hMono:=StarBudgetOddCuts.cut_mono p.orderedBase p.completed (by
      intro e
      change p.orderedBase.mult e≤p.orderedBase.mult e+p.completion.L.mult e+p.completion.N.mult e
      omega) S
    omega
  by_contra hn
  let a : Fin (p.pairIndex+1)×Bool:=(0,false)
  let b : Fin (p.pairIndex+1)×Bool:=(0,true)
  have hab:a≠b:=by intro hh;have he:=congrArg Prod.snd hh;cases he
  have ha:a≠p.centre:=by intro hh;have he:=congrArg (fun v : Fin (p.pairIndex+1)×Bool=>v.1.val) hh;exact hn he.symm
  have hb:b≠p.centre:=by intro hh;have he:=congrArg (fun v : Fin (p.pairIndex+1)×Bool=>v.1.val) hh;exact hn he.symm
  have hDa:p.orderedBase.degree a≤d:=p.ordered_pair_mono a p.centre (by dsimp [a];omega)
  have hDb:p.orderedBase.degree b≤d:=p.ordered_pair_mono b p.centre (by dsimp [b];omega)
  have hSub:({a,b}:Finset _)⊆univ.erase p.centre:=by
    intro v hv
    simp only [mem_insert,mem_singleton] at hv
    rcases hv with rfl|rfl
    · exact mem_erase.mpr ⟨ha,mem_univ _⟩
    · exact mem_erase.mpr ⟨hb,mem_univ _⟩
  have hSum:(G.maxDegree-p.orderedBase.degree a)+(G.maxDegree-p.orderedBase.degree b)≤
      ∑v∈univ.erase p.centre,(G.maxDegree-p.orderedBase.degree v):=by
    have hh:=sum_le_sum_of_subset_of_nonneg (f:=fun v=>G.maxDegree-p.orderedBase.degree v)
      hSub (fun _ _ _=>Nat.zero_le _)
    simpa only [sum_insert,mem_singleton,hab,not_false_eq_true,sum_singleton] using hh
  have hBudget:=p.ordinary_deficit_budget
  change (∑v∈univ.erase p.centre,(G.maxDegree-p.orderedBase.degree v))+d≤G.maxDegree+B at hBudget
  have hA:=p.ordered_degree_le a
  have hB:=p.ordered_degree_le b
  omega

end OverfullWork.NormalizedCanonicalCandidate

namespace OverfullWork.CanonicalResidualFirstPair

theorem budget_scale (Q n Δ B : ℕ) (hQ : 2≤Q) (hn : 32≤n) (hΔ : n≤2*Δ)
    (hB : B≤6*(n/(4096*Q^2))+6) : 3*B≤2*Δ := by
  have hCoeff:64≤4096*Q^2:=by nlinarith only [hQ]
  have hh:64*(n/(4096*Q^2))≤n:=
    (Nat.mul_le_mul_right (n/(4096*Q^2)) hCoeff).trans (Nat.mul_div_le n (4096*Q^2))
  omega

end OverfullWork.CanonicalResidualFirstPair

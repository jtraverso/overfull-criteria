module

public import OverfullWork.StarBudgetOddCuts

@[expose] public section


/-! # No-overfull obligations of the actual canonical completion

The ordinary deficit budget and centre degree are transported from the
same original certificate. This is a specialization of the large/small
odd-cut split in CMS Claim 4.3, not a factorization assertion.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset OddCutDeficit NormalizedAlmostStoppingRun IndependentSetIdentification
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ}
variable {c : Certificate G B K}
set_option maxHeartbeats 6000000

theorem Candidate.ordered_degree_le (p : Candidate c) (v : Fin (p.pairIndex+1)×Bool) :
    p.orderedBase.degree v≤G.maxDegree := by
  simp only [Candidate.orderedBase,OrderedCanonicalTransport.degree_reindex]
  exact p.degree_le _

theorem Candidate.centre_degree (p : Candidate c) :
    p.orderedBase.degree p.centre=∑y∈c.setᶜ,G.degree y := by
  simp only [Candidate.orderedBase,OrderedCanonicalTransport.degree_reindex,
    Candidate.centre,p.coordinates.apply_symm_apply]
  exact degree_none G c.setᶜ _

theorem Candidate.ordinary_deficit_budget (p : Candidate c) :
    (∑v∈univ.erase p.centre,(G.maxDegree-p.orderedBase.degree v))+
      p.orderedBase.degree p.centre≤G.maxDegree+B := by
  have hOrd:(∑w : Outside c.setᶜ,(G.maxDegree-c.image.degree (some w)))=
      deficitMass G G.maxDegree c.set:=by
    simp_rw [Certificate.image,degree_some]
    have hh:(∑w : Outside c.setᶜ,(G.maxDegree-G.degree w.val))=
        ∑v∈c.setᶜᶜ,(G.maxDegree-G.degree v):=
      (sum_subtype c.setᶜᶜ (fun v=>mem_compl) (fun v=>G.maxDegree-G.degree v)).symm
    simpa only [compl_compl,deficitMass] using hh
  have hTotal:(∑v : Fin (p.pairIndex+1)×Bool,(G.maxDegree-p.orderedBase.degree v))=
      deficitMass G G.maxDegree c.set+(G.maxDegree-c.image.degree none):=by
    calc
      _ = ∑v : Fin (p.pairIndex+1)×Bool,(G.maxDegree-c.image.degree (p.coordinates v)):=by
        simp only [Candidate.orderedBase,OrderedCanonicalTransport.degree_reindex]
      _ = ∑w : Vertices c.setᶜ,(G.maxDegree-c.image.degree w):=
        p.coordinates.sum_comp (fun w : Vertices c.setᶜ=>G.maxDegree-c.image.degree w)
      _ = _ :=by rw [Fintype.sum_option,hOrd];omega
  have hSplit:=sum_erase_add univ (fun v=>G.maxDegree-p.orderedBase.degree v)
    (mem_univ p.centre)
  have hCentre:p.orderedBase.degree p.centre=c.image.degree none:=by
    simp only [Candidate.orderedBase,OrderedCanonicalTransport.degree_reindex,
      Candidate.centre,p.coordinates.apply_symm_apply]
  have hDef:(∑v∈univ.erase p.centre,(G.maxDegree-p.orderedBase.degree v))=
      deficitMass G G.maxDegree c.set:=by rw [hCentre] at hSplit;omega
  rw [hDef,p.centre_degree]
  exact c.budget

theorem Candidate.completion_no_overfull_iff_triples (p : Candidate c)
    (A : Finset (Fin (p.pairIndex+1)×Bool)) (r t : ℕ)
    (hA : A.card=p.pairIndex+1) (hAc : Aᶜ.card=p.pairIndex+1)
    (hExpand : BipartiteRobustMargin.IsBipartiteRobustAt p.completed.supportGraph A r t)
    (hThreshold : 2*t≤p.pairIndex+1) (hLarge : G.maxDegree≤r*r)
    (hSmall : B+3*(2*t+c.setᶜ.card)≤G.maxDegree) :
    (¬p.completed.HasOverfullSubset G.maxDegree) ↔
      ∀S : Finset (Fin (p.pairIndex+1)×Bool),S.card=3 → p.centre∈S →
        G.maxDegree≤p.completed.cutSize S := by
  apply StarBudgetOddCuts.no_overfull_iff_centre_triples p.orderedBase p.completed
    G.maxDegree B c.setᶜ.card (p.pairIndex+1) r t p.centre A
    p.completion.regular
  · intro e
    change p.orderedBase.mult e≤p.orderedBase.mult e+p.completion.L.mult e+p.completion.N.mult e
    omega
  · exact p.ordered_degree_le
  · exact p.ordered_star
  · exact p.centre_multiplicity
  · have hh:=p.ordinary_deficit_budget;omega
  all_goals assumption

/-- An actual no-overfull subcase. The extra centre-mass inequality is
explicit and is not asserted for every canonical terminal candidate. -/
theorem Candidate.completion_no_overfull_of_centre_mass (p : Candidate c)
    (A : Finset (Fin (p.pairIndex+1)×Bool)) (r t : ℕ)
    (hA : A.card=p.pairIndex+1) (hAc : Aᶜ.card=p.pairIndex+1)
    (hExpand : BipartiteRobustMargin.IsBipartiteRobustAt p.completed.supportGraph A r t)
    (hThreshold : 2*t≤p.pairIndex+1) (hLarge : G.maxDegree≤r*r)
    (hSmall : B+3*(2*t+c.setᶜ.card)≤G.maxDegree)
    (hCentre : B+4*c.setᶜ.card+6≤2*(∑y∈c.setᶜ,G.degree y)) :
    ¬p.completed.HasOverfullSubset G.maxDegree := by
  apply (p.completion_no_overfull_iff_triples A r t hA hAc hExpand hThreshold hLarge hSmall).mpr
  intro S hS hz
  have hBase:=StarBudgetOddCuts.centre_triple_cut_bound p.orderedBase G.maxDegree B
    c.setᶜ.card p.centre
    p.ordered_degree_le p.ordered_star p.centre_multiplicity
    p.ordinary_deficit_budget (by simpa only [p.centre_degree] using hCentre) S hS hz
  apply hBase.trans
  apply StarBudgetOddCuts.cut_mono
  intro e
  change p.orderedBase.mult e≤p.orderedBase.mult e+p.completion.L.mult e+p.completion.N.mult e
  omega

end OverfullWork.NormalizedCanonicalCandidate

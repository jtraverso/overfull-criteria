module

public import OverfullWork.RegularCompletionPartition
public import OverfullWork.RobustExpansionDeletion
public import OverfullWork.NormalizedCanonicalCandidate

@[expose] public section


/-! # Partition and expansion bridges for the actual canonical candidate

All graph additions and coordinates are those already constructed in
the candidate. Global robust expansion is preserved by adding edges.
The constructed partition controls weighted degrees at every ordinary
vertex; bipartite robust expansion and factorization remain separate.
-/
namespace OverfullWork.CanonicalRegularization
open SimpleGraph
open scoped Classical
variable {m : ℕ} {D : MultiGraph (Fin m×Bool)} {Δ : ℕ}

theorem Completion.support_le (c : Completion D Δ) :
    D.supportGraph≤((D.addCopies c.L).addCopies c.N).supportGraph := by
  intro u v huv
  change 0<D.mult s(u,v) at huv
  change 0<D.mult s(u,v)+c.L.mult s(u,v)+c.N.mult s(u,v)
  omega

theorem Completion.robust_of_base (c : Completion D Δ) (r t : ℕ)
    (hrobust : RobustExpansion.IsRobustAt D.supportGraph r t) :
    RobustExpansion.IsRobustAt ((D.addCopies c.L).addCopies c.N).supportGraph r t :=
  RobustExpansion.isRobustAt_mono_graph _ _ c.support_le r t hrobust

end OverfullWork.CanonicalRegularization

namespace OverfullWork.OrderedCanonicalTransport
open SimpleGraph
open scoped Classical
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
theorem isStarAt_reindex (M : MultiGraph V) (e : W ≃ V) (x : V)
    (hstar : M.IsStarAt x) : (reindex M e).IsStarAt (e.symm x) := by
  intro u v hu hv
  change M.mult s(e u,e v)≤1
  apply hstar
  · intro he
    exact hu (e.injective (he.trans (e.apply_symm_apply x).symm))
  · intro he
    exact hv (e.injective (he.trans (e.apply_symm_apply x).symm))

end OverfullWork.OrderedCanonicalTransport

namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset
open scoped Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ}
variable {c : NormalizedAlmostStoppingRun.Certificate G B K}

noncomputable def Candidate.orderedBase (p : Candidate c) :
    MultiGraph (Fin (p.pairIndex+1)×Bool) := OrderedCanonicalTransport.reindex c.image p.coordinates

noncomputable def Candidate.completed (p : Candidate c) : MultiGraph (Fin (p.pairIndex+1)×Bool) :=
  (p.orderedBase.addCopies p.completion.L).addCopies p.completion.N

def Candidate.centre (p : Candidate c) : Fin (p.pairIndex+1)×Bool := p.coordinates.symm none

theorem Candidate.ordered_star (p : Candidate c) : p.orderedBase.IsStarAt p.centre := by
  apply OrderedCanonicalTransport.isStarAt_reindex
  exact IndependentSetIdentification.isStarAt G c.setᶜ _

theorem Candidate.centre_multiplicity (p : Candidate c) (v : Fin (p.pairIndex+1)×Bool) :
    p.orderedBase.mult s(p.centre,v)≤c.setᶜ.card := by
  change c.image.mult s(p.coordinates (p.coordinates.symm none),p.coordinates v)≤_
  rw [p.coordinates.apply_symm_apply]
  cases hv:p.coordinates v with
  | none => rw [c.image.loopless _ (by simp)];exact Nat.zero_le _
  | some w => exact IndependentSetIdentification.centre_mult_le G c.setᶜ _ w

end OverfullWork.NormalizedCanonicalCandidate

namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset
open scoped Classical
universe u

/-- The existing candidate now has an actual balanced partition of its
actual regular completion, separating each ordered pair. For ordinary
vertices the error is the simple partition tolerance plus the original
degree deficit and the size of the identified independent set. -/
theorem exists_uniform_completed_candidate_partition (ε : ℝ) (hε : 0<ε) :
    ∃m₀ : ℕ,∀{V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] {B K : ℕ}
      (c : NormalizedAlmostStoppingRun.Certificate G B K) (p : Candidate c),
      m₀≤p.pairIndex+1 →
      ∃A : Finset (Fin (p.pairIndex+1)×Bool),
        A.card=p.pairIndex+1 ∧ Aᶜ.card=p.pairIndex+1 ∧
        (∀i : Fin (p.pairIndex+1),((i,true)∈A ↔ (i,false)∉A)) ∧
        ∀v,v≠p.centre →
          |(p.completed.degreeInto A v:ℝ)-(p.completed.degreeInto Aᶜ v:ℝ)|<
            ε*((p.pairIndex+1:ℕ):ℝ)+((G.maxDegree-p.orderedBase.degree v:ℕ):ℝ)+c.setᶜ.card := by
  obtain ⟨m₀,hm₀⟩:=CanonicalRegularization.exists_uniform_canonical_partition ε hε
  refine ⟨m₀,?_⟩
  intro V _ _ G _ B K c p hm
  obtain ⟨A,hA,hAc,hsep,hdis⟩:=hm₀ p.pairIndex p.orderedBase G.maxDegree p.completion hm
    (le_refl _) (Function.Embedding.refl _)
  refine ⟨A,hA,hAc,hsep,?_⟩
  intro v hv
  have hb:=p.completion.support_deficit_le p.centre v p.ordered_star hv c.setᶜ.card
    (p.centre_multiplicity v)
  have hb':((G.maxDegree-p.orderedBase.supportGraph.degree v:ℕ):ℝ)≤
      ((G.maxDegree-p.orderedBase.degree v:ℕ):ℝ)+(c.setᶜ.card:ℝ):=by exact_mod_cast hb
  have hd:=hdis v
  change |(p.completed.degreeInto A v:ℝ)-(p.completed.degreeInto Aᶜ v:ℝ)|<
    ε*((p.pairIndex+1:ℕ):ℝ)+((G.maxDegree-p.orderedBase.supportGraph.degree v:ℕ):ℝ) at hd
  linarith

end OverfullWork.NormalizedCanonicalCandidate

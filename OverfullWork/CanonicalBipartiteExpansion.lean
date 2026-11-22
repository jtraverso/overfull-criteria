module

public import OverfullWork.CanonicalDeficitExceptions
public import OverfullWork.CompletionBipartiteRobust

@[expose] public section


/-! # A constructed bipartite robust cut of the actual candidate

The exceptional set is constructed from the certificate. No expansion
or initial colouring is an oracle. Density and scale assumptions are
explicit arithmetic inequalities; factorization is still separate.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun BipartiteRobustMargin
open scoped Classical
universe u

theorem exists_uniform_candidate_robust_cut (ε : ℝ) (hε : 0<ε) :
    ∃m₀ : ℕ,∀{V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] {B K : ℕ}
      (c : Certificate G B K) (p : Candidate c),m₀≤p.pairIndex+1 →
      ∀s δ q r t : ℕ,
      let m:=p.pairIndex+1
      let a:=1+(2*G.maxDegree+B)/(s+1)
      2*(δ:ℝ)+ε*(m:ℝ)+3*((s+c.setᶜ.card:ℕ):ℝ)≤G.maxDegree →
      δ≤m → m+2*q≤2*δ → 0<r → r≤q → r+a≤t →
      4*r*m+2*m*a≤q*t →
      ∃A : Finset (Fin (p.pairIndex+1)×Bool),A.card=m ∧ Aᶜ.card=m ∧
        (∀i : Fin m,((i,true)∈A ↔ (i,false)∉A)) ∧
        IsBipartiteRobustAt p.orderedBase.supportGraph A r t ∧
        ∀v,|(p.completed.degreeInto A v:ℝ)-(p.completed.degreeInto Aᶜ v:ℝ)|<
          ε*(m:ℝ)+((G.maxDegree-p.orderedBase.supportGraph.degree v:ℕ):ℝ) := by
  obtain ⟨m₀,hm₀⟩:=CanonicalRegularization.exists_uniform_canonical_partition ε hε
  refine ⟨m₀,?_⟩
  intro V _ _ G _ B K c p hm s δ q r t
  dsimp only
  intro hRoom hδ hMargin hr hrq hrt hScale
  obtain ⟨A,hA,hAc,hSep,hDis⟩:=hm₀ p.pairIndex p.orderedBase G.maxDegree p.completion hm
    (le_refl _) (Function.Embedding.refl _)
  refine ⟨A,hA,hAc,hSep,?_,hDis⟩
  apply CompletionBipartiteRobust.robust_of_completed_cut p.orderedBase.supportGraph
    p.completed G.maxDegree p.completion.regular p.completion.simple_base_contained
    A (p.deficitExceptions s) (p.pairIndex+1) δ q r t
      (1+(2*G.maxDegree+B)/(s+1)) (s+c.setᶜ.card) (ε*((p.pairIndex+1:ℕ):ℝ))
    hA hAc (p.deficitExceptions_card s)
  · exact hDis
  · exact p.small_support_deficit s
  all_goals assumption

end OverfullWork.NormalizedCanonicalCandidate

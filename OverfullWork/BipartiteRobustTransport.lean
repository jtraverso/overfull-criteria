module

public import OverfullWork.CanonicalCandidateAboveHalfExpansion

@[expose] public section


/-! # Preserve the actual cut's expansion under canonical edge addition -/
namespace OverfullWork.BipartiteRobustMargin
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem neighbours_mono_graph (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hGH : G≤H) (B S : Finset V) (r : ℕ) : neighbours G B r S⊆neighbours H B r S := by
  intro v hv
  obtain ⟨hvB,hvD⟩:=mem_filter.mp hv
  have hSub:G.neighborFinset v∩S⊆H.neighborFinset v∩S:=by
    intro x hx
    refine mem_inter.mpr ⟨?_,(mem_inter.mp hx).2⟩
    exact (mem_neighborFinset H v x).mpr (hGH ((mem_neighborFinset G v x).mp (mem_inter.mp hx).1))
  exact mem_filter.mpr ⟨hvB,hvD.trans (card_le_card hSub)⟩

theorem expandsTo_mono_graph (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hGH : G≤H) (A B : Finset V) (r t : ℕ) (h : ExpandsTo G A B r t) :
    ExpandsTo H A B r t := by
  intro S hSA hlo hhi
  exact (h S hSA hlo hhi).trans (card_le_card (neighbours_mono_graph G H hGH B S r))

theorem bipartite_robust_mono_graph (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hGH : G≤H) (A : Finset V) (r t : ℕ) (h : IsBipartiteRobustAt G A r t) :
    IsBipartiteRobustAt H A r t :=
  ⟨expandsTo_mono_graph G H hGH A Aᶜ r t h.1,expandsTo_mono_graph G H hGH Aᶜ A r t h.2⟩

end OverfullWork.BipartiteRobustMargin

namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun BipartiteRobustMargin
open scoped Classical
universe u

/-- The actual completed candidate has the SAME balanced cut with both
weighted degree control and bipartite robust expansion of its support.
Only the existing sparse budgets and fixed above-half density are inputs.
This closes this expansion bridge, not edge-colouring or G2. -/
theorem exists_above_half_completed_robust_cut (ε : ℝ) (hε : 0<ε) :
    ∃Q : ℕ,2≤Q ∧ ∃N : ℕ,∀{V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] {B K : ℕ}
      (c : Certificate G B K) (p : Candidate c),N≤Fintype.card V →
      ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
      B≤6*(Fintype.card V/(4096*Q^2))+6 → K≤Fintype.card V/(4096*Q^2)+1 →
      ∃A : Finset (Fin (p.pairIndex+1)×Bool),A.card=p.pairIndex+1 ∧ Aᶜ.card=p.pairIndex+1 ∧
        (∀i : Fin (p.pairIndex+1),((i,true)∈A ↔ (i,false)∉A)) ∧
        IsBipartiteRobustAt p.completed.supportGraph A
          ((p.pairIndex+1)/(2^30*Q^3)) ((p.pairIndex+1)/(1024*Q)) ∧
        (0<(p.pairIndex+1)/(2^30*Q^3) ∧ 2*((p.pairIndex+1)/(1024*Q))≤p.pairIndex+1) ∧
        ∀v,|(p.completed.degreeInto A v:ℝ)-(p.completed.degreeInto Aᶜ v:ℝ)|<
          (1/(1024*(Q:ℝ)))*((p.pairIndex+1:ℕ):ℝ)+
            ((G.maxDegree-p.orderedBase.supportGraph.degree v:ℕ):ℝ) := by
  obtain ⟨Q,hQ,N,hN⟩:=exists_above_half_candidate_robust_cut.{u} ε hε
  refine ⟨Q,hQ,N,?_⟩
  intro V _ _ G _ B K c p hn hdense hB hK
  obtain ⟨A,hA,hAc,hSep,hRobust,hNonvacuous,hDis⟩:=hN G c p hn hdense hB hK
  exact ⟨A,hA,hAc,hSep,bipartite_robust_mono_graph _ _ p.completion.support_le _ _ _ hRobust,hNonvacuous,hDis⟩

end OverfullWork.NormalizedCanonicalCandidate

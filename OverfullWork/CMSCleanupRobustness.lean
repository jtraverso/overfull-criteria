module

public import OverfullWork.RobustRegularFactorization

@[expose] public section


/-! Stability of the robust expansion condition under an explicitly
bounded degree loss in an actual subgraph. -/
namespace OverfullWork.RobustExpansion

open SimpleGraph
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem real_robust_of_subgraph_degree_loss (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (hLe : H ≤ G) (b : ℕ) (ν ν' τ τ' : ℝ)
    (hν : ν' ≤ ν) (hτ : τ ≤ τ') (hBound : (b:ℝ) ≤ (ν-ν')*(Fintype.card V:ℝ))
    (hLoss : ∀ v,G.degree v ≤ H.degree v+b) (hRob : IsRealRobust G ν τ) :
    IsRealRobust H ν' τ' := by
  let E := sdiff G H
  have hRemoved (v : V) : E.degree v ≤ b := by
    have he : E.degree v+H.degree v=G.degree v := by
      simpa only [E,←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
        MaximumMatching.degree_sdiff_add_of_le G H hLe v
    have h := hLoss v
    omega
  have hRob' := isRealRobust_sdiff_with_loss G E ν ν' τ τ' b hν hτ hBound hRemoved hRob
  have he : sdiff G E = H := by
    ext u v
    change G.Adj u v ∧ ¬(G.Adj u v ∧ ¬H.Adj u v) ↔ H.Adj u v
    have h := @hLe u v
    tauto
  have transport (I J : SimpleGraph V) [dI : DecidableRel I.Adj] [dJ : DecidableRel J.Adj] (h : I = J)
      (hR : IsRealRobust I ν' τ') : IsRealRobust J ν' τ' := by
    subst J
    cases Subsingleton.elim dI dJ
    exact hR
  exact transport _ _ (dI := SimpleGraph.Sdiff.adjDecidable V G E) he hRob'

end OverfullWork.RobustExpansion

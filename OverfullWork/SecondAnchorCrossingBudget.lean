module

public import OverfullWork.CrossingSupport
public import OverfullWork.ProtectedCentreRowBounds

@[expose] public section


/-! # The actual simple crossing degree at the second anchor

Before its own saturation, every colored crossing edge meets the first
anchor. Each second-anchor step can add only one new simple neighbor.
The later protected saturated run leaves this entire row fixed.
-/
namespace SimpleGraph.MultiGraph.PartialColouring
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}
set_option maxHeartbeats 24000000

theorem AnchoredStep.crossing_support_degree {P Q : M.PartialColouring k} {A : Finset V} {a b : V}
    (step : AnchoredStep P Q A a b) :
    (Q.graph.crossingSupport A).degree b ≤ (P.graph.crossingSupport A).degree b+1 := by
  have hSub : (Q.graph.crossingSupport A).neighborFinset b ⊆
      (P.graph.crossingSupport A).neighborFinset b ∪ {step.step.neighbour} := by
    intro v hv
    have hAdj := (mem_neighborFinset _ b v).mp hv
    by_cases hEq : v=step.step.neighbour
    · exact mem_union_right _ (mem_singleton.mpr hEq)
    · have hUnit : (unitEdge b step.step.neighbour step.step.distinct).mult s(b,v)=0 := by
        apply if_neg
        intro he
        rcases Sym2.eq_iff.mp he with ⟨_,hv⟩|⟨hb,_⟩
        · exact hEq hv
        · exact step.step.distinct hb
      have hBalance := step.bundle_balance s(b,v)
      rw [hUnit] at hBalance
      exact mem_union_left _ ((mem_neighborFinset _ b v).mpr ⟨by have hh := hAdj.1;omega,hAdj.2⟩)
  have hCount := (card_le_card hSub).trans (card_union_le _ _)
  simpa only [card_neighborFinset_eq_degree,card_singleton] using hCount

theorem AnchoredRun.crossing_support_degree {P Q : M.PartialColouring k} {A : Finset V} {a b : V} {n t : ℕ}
    (run : AnchoredRun A a b P Q n t) :
    (Q.graph.crossingSupport A).degree b ≤ (P.graph.crossingSupport A).degree b+n := by
  induction run with
  | refl P => omega
  | step step tail ih => have hh := step.crossing_support_degree;omega

theorem GoodRouteRun.protected_saturated_crossing_degree {A E : Finset V} {h ell : ℕ}
    {P Q : M.PartialColouring k} {n t : ℕ} (run : GoodRouteRun A E h ell P Q n t)
    (a : V) (ha : a ∈ E) (hSat : P.graph.degree a=k) :
    (Q.graph.crossingSupport A).degree a=(P.graph.crossingSupport A).degree a := by
  rw [←card_neighborFinset_eq_degree,←card_neighborFinset_eq_degree]
  congr 1
  ext v
  simp only [mem_neighborFinset]
  change (0 < Q.graph.mult s(a,v) ∧ _) ↔ (0 < P.graph.mult s(a,v) ∧ _)
  rw [run.protected_saturated_bundle a ha hSat v]

end SimpleGraph.MultiGraph.PartialColouring

namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T : ℕ} {η : ℝ} {b w : Fin (p.pairIndex+1) × Bool}
variable {s : p.CaseTwoPartition P T η b}

theorem Candidate.CaseTwoMiddleCopies.first_run_second_crossing_degree
    (r : p.CaseTwoMiddleCopies s w) (C : r.graph.EdgeColoring r.seedPalette)
    {Q : p.completed.PartialColouring r.seedPalette} {n t : ℕ}
    (run : MultiGraph.PartialColouring.ProtectedRun p.centre b w (r.partialSeed C) Q n t) :
    (Q.graph.crossingSupport s.part).degree b ≤ 1 := by
  have hCover : ∀ x y, (Q.graph.crossingSupport s.part).Adj x y →
      x ∈ ({p.centre}:Finset _) ∨ y ∈ ({p.centre}:Finset _) := by
    intro x y hxy
    by_contra! hn
    have hxa : x ≠ p.centre := by simpa only [mem_singleton] using hn.1
    have hya : y ≠ p.centre := by simpa only [mem_singleton] using hn.2
    have hz := r.protected_run_away_crossing_zero C run x y hxa hya hxy.2
    have hp := hxy.1
    omega
  have hb : b ∉ ({p.centre}:Finset _) := by
    simp only [mem_singleton]
    intro he
    exact s.second_not_mem (he ▸ s.centre_mem)
  simpa only [card_singleton] using Q.graph.crossingSupport_degree_le_cover s.part {p.centre} hCover b hb

end OverfullWork.NormalizedCanonicalCandidate

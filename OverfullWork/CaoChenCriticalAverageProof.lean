module

public import OverfullWork.CaoChenEventualR1
public import OverfullWork.CaoChenAverageReduction

@[expose] public section


/-! # The critical average-degree and deficit estimates are proved

The previously explicit R1 input is now discharged by the actual eventual
R1 theorem. The proved distance-four adjacency result supplies the R2
donors in the existing reduction. No average-degree or deficit statement
is assumed as an input.
-/
namespace OverfullWork.CaoChenCriticalAverage
open SimpleGraph Finset
open scoped Classical
universe u

/-- Cao--Chen's asymptotic critical average-degree bound, with no
unproved discharging input. The threshold precedes the graph. -/
theorem average_bound : CriticalAverageDegree.AverageBound.{u} := by
  apply CaoChenDischarging.averageBound_of_eventual_R1
  intro ε hε hεone
  exact CaoChenDischarging.eventual_R1 ε hε hεone

/-- The equivalent relative-deficit estimate, now unconditional on all
finite simple Delta-critical graphs of sufficiently large maximum degree. -/
theorem deficit_bound : CriticalAverageDegree.DeficitBound.{u} :=
  CriticalAverageDegree.averageBound_iff_deficitBound.mp average_bound

/-- Above-half critical graphs are robust at the established nonvacuous
integer scales, without assuming the formerly missing deficit estimate. -/
theorem robust_critical (ε : ℝ) (hε : 0<ε) :
    ∃q : ℕ,2≤q ∧ ∃N : ℕ,
      ∀{W : Type u} [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) [DecidableRel G.Adj],
        N≤Fintype.card W → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card W:ℝ)≤(G.maxDegree:ℝ) →
        let a:=Fintype.card W/(8*q)
        let k:=Fintype.card W/(4096*q^2)
        0<k+1 ∧ 2*(a+k)≤Fintype.card W ∧
          RobustExpansion.IsRobustAt G (k+1) (a+k) :=
  CriticalAverageDegree.robust_critical_of_deficitBound deficit_bound ε hε

/-- An arbitrary sufficiently large above-half counterexample has an
actual robust critical witness. This is a reduction, not its exclusion. -/
theorem robust_critical_witness (ε : ℝ) (hε : 0<ε) :
    ∃q : ℕ,2≤q ∧ ∃N : ℕ,
      ∀{W : Type u} [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) [DecidableRel G.Adj],
        N≤Fintype.card W →
        ((1:ℝ)/2+ε)*(Fintype.card W:ℝ)≤(G.maxDegree:ℝ) →
        ¬G.HasOverfullSubgraph → ¬G.EdgeColorable G.maxDegree →
        ∃w : Critical.CriticalWitness G,
          let a:=Fintype.card w.vertices/(8*q)
          let k:=Fintype.card w.vertices/(4096*q^2)
          0<k+1 ∧ 2*(a+k)≤Fintype.card w.vertices ∧
            RobustExpansion.IsRobustAt w.graph (k+1) (a+k) :=
  CriticalAverageDegree.robust_witness_of_averageBound average_bound ε hε

end OverfullWork.CaoChenCriticalAverage

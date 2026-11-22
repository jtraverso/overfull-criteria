module

public import OverfullWork.AsymptoticDeficitExpansion
public import OverfullWork.Critical

@[expose] public section


/-! # The remaining critical average-degree input and its exact use

The two propositions below are unresolved inputs, not axioms or theorems.
Their equivalence is an elementary identity. The subsequent implications
take the input as an explicit hypothesis and construct robust critical
obstructions uniformly, including the loss of order on extraction.
No edge-colouring or factorization conclusion is asserted.
-/
namespace OverfullWork.CriticalAverageDegree
open SimpleGraph Finset SparseDeficitCore
open scoped Classical
universe u

/-- The critical average-degree estimate still to be formalized. -/
def AverageBound : Prop :=
  ∀ η : ℝ, 0 < η → ∃ D₀ : ℕ,
    ∀ {W : Type u} [Fintype W] [DecidableEq W]
      (G : SimpleGraph W) [DecidableRel G.Adj],
      Overfull.IsDeltaCritical G → D₀ ≤ G.maxDegree →
      (1-η)*(G.maxDegree:ℝ)*(Fintype.card W:ℝ) ≤
        ((∑ v : W, G.degree v : ℕ):ℝ)

/-- The same missing estimate, expressed as a relative deficit bound. -/
def DeficitBound : Prop :=
  ∀ η : ℝ, 0 < η → ∃ D₀ : ℕ,
    ∀ {W : Type u} [Fintype W] [DecidableEq W]
      (G : SimpleGraph W) [DecidableRel G.Adj],
      Overfull.IsDeltaCritical G → D₀ ≤ G.maxDegree →
      (totalDeficit G G.maxDegree:ℝ) ≤
        η*(G.maxDegree:ℝ)*(Fintype.card W:ℝ)

theorem average_iff_deficit (G : SimpleGraph W) [Fintype W] [DecidableEq W]
    [DecidableRel G.Adj] (η : ℝ) :
    ((1-η)*(G.maxDegree:ℝ)*(Fintype.card W:ℝ) ≤
      ((∑ v : W, G.degree v : ℕ):ℝ)) ↔
    (totalDeficit G G.maxDegree:ℝ) ≤
      η*(G.maxDegree:ℝ)*(Fintype.card W:ℝ) := by
  have hi := degree_sum_add_deficit G G.maxDegree G.degree_le_maxDegree
  have hr : ((∑ v : W, G.degree v : ℕ):ℝ) +
      (totalDeficit G G.maxDegree:ℝ) =
      (G.maxDegree:ℝ)*(Fintype.card W:ℝ) := by exact_mod_cast hi
  constructor <;> intro h <;> nlinarith only [hr,h]

theorem averageBound_iff_deficitBound : AverageBound.{u} ↔ DeficitBound.{u} := by
  constructor
  · intro h η hη
    obtain ⟨D₀,hD⟩ := h η hη
    refine ⟨D₀,?_⟩
    intro W _ _ G _ hc hd
    exact (average_iff_deficit G η).mp (hD G hc hd)
  · intro h η hη
    obtain ⟨D₀,hD⟩ := h η hη
    refine ⟨D₀,?_⟩
    intro W _ _ G _ hc hd
    exact (average_iff_deficit G η).mpr (hD G hc hd)

/-- Conditional use of the missing input. All scales and thresholds
precede the graph, and the robust interval and neighbour threshold are
nonvacuous. This theorem does not prove `DeficitBound`. -/
theorem robust_critical_of_deficitBound (hdef : DeficitBound.{u})
    (ε : ℝ) (hε : 0<ε) :
    ∃ q : ℕ, 2≤q ∧ ∃ N : ℕ,
      ∀ {W : Type u} [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) [DecidableRel G.Adj],
        N≤Fintype.card W → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card W:ℝ)≤(G.maxDegree:ℝ) →
        let a := Fintype.card W/(8*q)
        let k := Fintype.card W/(4096*q^2)
        0<k+1 ∧ 2*(a+k)≤Fintype.card W ∧
          RobustExpansion.IsRobustAt G (k+1) (a+k) := by
  obtain ⟨q,hq,η,hη,N,hrobust⟩ :=
    RobustExpansion.above_half_quadratic_deficit_robust_expansion ε hε
  obtain ⟨D₀,hD⟩ := hdef η hη
  refine ⟨q,hq,max N (2*D₀),?_⟩
  intro W _ _ G _ hn hc hdense
  have hnN : N≤Fintype.card W := (le_max_left _ _).trans hn
  have hnD : 2*D₀≤Fintype.card W := (le_max_right _ _).trans hn
  have hnDelta : Fintype.card W≤2*G.maxDegree := by
    have he : 0≤ε*(Fintype.card W:ℝ) := by positivity
    exact_mod_cast (show (Fintype.card W:ℝ)≤2*(G.maxDegree:ℝ) by nlinarith)
  have hD₀ : D₀≤G.maxDegree := by omega
  have hmass := hD G hc hD₀
  have hDelta : (G.maxDegree:ℝ)≤(Fintype.card W:ℝ) := by
    exact_mod_cast G.maxDegree_le_of_forall_degree_le
      (Fintype.card W) (fun v => (G.degree_lt_card_verts v).le)
  have hmass' : (totalDeficit G G.maxDegree:ℝ)≤η*(Fintype.card W:ℝ)^2 := by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hDelta hη.le)
      (Nat.cast_nonneg (Fintype.card W) : (0:ℝ)≤(Fintype.card W:ℝ))
    nlinarith only [hmass,hh]
  exact hrobust G hnN hdense hmass'

/-- Any sufficiently large counterexample has a robust critical witness,
conditional on the explicitly unproved critical deficit input. The
ambient threshold pays for vertex loss during critical extraction. -/
theorem robust_witness_of_averageBound (havg : AverageBound.{u})
    (ε : ℝ) (hε : 0<ε) :
    ∃ q : ℕ, 2≤q ∧ ∃ N : ℕ,
      ∀ {W : Type u} [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) [DecidableRel G.Adj],
        N≤Fintype.card W →
        ((1:ℝ)/2+ε)*(Fintype.card W:ℝ)≤(G.maxDegree:ℝ) →
        ¬G.HasOverfullSubgraph → ¬G.EdgeColorable G.maxDegree →
        ∃ w : Critical.CriticalWitness G,
          let a := Fintype.card w.vertices/(8*q)
          let k := Fintype.card w.vertices/(4096*q^2)
          0<k+1 ∧ 2*(a+k)≤Fintype.card w.vertices ∧
            RobustExpansion.IsRobustAt w.graph (k+1) (a+k) := by
  obtain ⟨q,hq,N,hrobust⟩ :=
    robust_critical_of_deficitBound (averageBound_iff_deficitBound.mp havg) ε hε
  refine ⟨q,hq,2*N,?_⟩
  intro W _ _ G _ hn hdense hno hnc
  obtain ⟨w⟩ := Critical.exists_criticalWitness G hnc hno
  have hnDelta : Fintype.card W≤2*G.maxDegree := by
    have he : 0≤ε*(Fintype.card W:ℝ) := by positivity
    exact_mod_cast (show (Fintype.card W:ℝ)≤2*(G.maxDegree:ℝ) by nlinarith)
  have hnw : G.maxDegree<Fintype.card w.vertices := by
    haveI : Nonempty w.vertices := w.critical.1.nonempty
    simpa only [w.maxDegree_eq] using w.graph.maxDegree_lt_card_verts
  have hsize : N≤Fintype.card w.vertices := by omega
  have hwdense : ((1:ℝ)/2+ε)*(Fintype.card w.vertices:ℝ)≤(w.graph.maxDegree:ℝ) := by
    have ho : (Fintype.card w.vertices:ℝ)≤(Fintype.card W:ℝ) := by exact_mod_cast w.order_le
    rw [w.maxDegree_eq]
    exact (mul_le_mul_of_nonneg_left ho (by positivity)).trans hdense
  exact ⟨w,hrobust w.graph hsize w.critical hwdense⟩

end OverfullWork.CriticalAverageDegree
